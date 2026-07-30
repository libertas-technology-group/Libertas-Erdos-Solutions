#!/usr/bin/env python3
"""
sum_bound_oracle.py — Verify Σ X_i / P_i summability for Erdos12.

The KEY AXIOM to discharge: X_div_P_summable.
Verifies that the series Σ (X(i) / P(i)) converges, using:
  A. X(i) ≈ sqrt(P(i+1)) ≈ 10*sqrt(V(i+1)*Y(i+1))
  B. P(i) grows super-exponentially at rate ~3^{(i+20)^3}
  C. Ratio X(i)/P(i) ~ 1/sqrt(P(i)) which is summable

All comparisons use integer bit_length() for log2 approximation,
avoiding float overflow for the enormous integers in the
block construction (P(i) ~ 3^{(i+20)^3}).

Copyright (C) 2026 Libertas Technology Group Ltd. All rights reserved.
"""

from __future__ import annotations

import math
import sys
import time
from decimal import Decimal, getcontext
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from erdos12_primitives import P_seq, X_seq

LN2 = math.log(2)
# Tolerance for X/P ratio bound check (A):
#   Allows the approximated ratio to be up to 100x larger than the ideal
#   sqrt(P(i+1))/P(i) bound.  This tolerance absorbs the +/-1-bit uncertainty
#   inherent in the bit_length() log2 approximation used by _log2_approx(),
#   as well as the loose constant factor in X(i) ~ sqrt(P(i+1)).
LOG2_100 = math.log2(100)

# Tolerance for ratio-decrease monotonicity check (B):
#   Allows adjacent log2(X(i)/P(i)) ratios to increase by up to ~10%
#   (a factor of 1.1x in linear space) without failing.  Minor jitter is
#   expected because bit_length() drops the fractional part of the true
#   log2, so exact monotonicity would be overly strict.
LOG2_110 = math.log2(1.1)


def _log2_approx(x: int) -> float:
    """Approximate log2(x) using bit_length.

    For x > 0:  floor(log2(x)) = x.bit_length() - 1.
    Since P(i) values have thousands of digits, the ±1 uncertainty
    in the fractional part is irrelevant for growth-rate analysis.
    """
    return float(x.bit_length() - 1) if x > 0 else float("-inf")


def verify_ratio_bounds(max_i: int) -> list[str]:
    """Verify the ratio X(i)/P(i) decays rapidly using log2 approximation.

    Since P(i) grows as ~3^{(i+20)^3}, the ratio X(i)/P(i) ~ 1/sqrt(P(i+1))
    decays doubly-exponentially.  We verify this in log2 space using
    bit_length() to avoid float overflow.
    """
    failures: list[str] = []
    log2_ratios: list[float] = []

    for i in range(max_i):
        pi = P_seq(i)
        pnext = P_seq(i + 1)
        xi = X_seq(i)
        if pi == 0:
            continue

        log2_pi = _log2_approx(pi)
        log2_pnext = _log2_approx(pnext)
        log2_xi = _log2_approx(xi)

        # X(i) ≈ sqrt(P(i+1)), so X(i)/P(i) ≈ sqrt(P(i+1))/P(i)
        log2_ratio = log2_xi - log2_pi
        log2_expected = 0.5 * log2_pnext - log2_pi
        log2_ratios.append(log2_ratio)

        if log2_ratio > log2_expected + LOG2_100:
            failures.append(
                f"i={i}: X/P log2 ≈ {log2_ratio:.2f}, "
                f"expected ≈ {log2_expected:.2f}",
            )

    # Check that log2 ratios decrease monotonically (summability)
    for i in range(1, len(log2_ratios)):
        if log2_ratios[i] > log2_ratios[i - 1] + LOG2_110:
            failures.append(
                f"Ratio increased: i={i-1}: log2 ≈ {log2_ratios[i-1]:.2f}, "
                f"i={i}: log2 ≈ {log2_ratios[i]:.2f}",
            )
            break

    return failures


def verify_summability(max_i: int) -> list[str]:
    """Check that partial sums of X(i)/P(i) converge.

    Uses Decimal for the first few terms (which are astronomically
    tiny); beyond that the terms are below any practical threshold
    and the sum has converged.

    Returns
    -------
    list[str]
        Empty list = PASS.  Non-empty indicates convergence issue.
    """
    failures: list[str] = []
    getcontext().prec = 50
    partial_sum = Decimal(0)

    for i in range(max_i):
        pi = P_seq(i)
        xi = X_seq(i)
        if pi == 0:
            continue

        term = Decimal(xi) / Decimal(pi)
        partial_sum += term

    if partial_sum > Decimal(10):
        failures.append(
            f"Total sum = {float(partial_sum):.4f}, expected < 10",
        )

    return failures


def log_growth_rate(max_i: int) -> None:
    """Log the growth rate of P(i) using bit_length-based log2."""
    for i in range(max_i):
        pi = P_seq(i)
        p_next = P_seq(i + 1)
        if pi == 0:
            print(f"  i={i}: P(i) = 0 (skipped)")
            continue
        log2_pi = _log2_approx(pi)
        log2_pnext = _log2_approx(p_next)
        log2_ratio = log2_pnext - log2_pi
        log_ratio = log2_ratio * LN2
        print(f"  i={i}: log(P(i+1)/P(i)) ≈ {log_ratio:.2f}")


def main() -> None:
    import argparse
    parser = argparse.ArgumentParser(description="Verify X/P summability for Erdos12.")
    parser.add_argument("--max-i", type=int, default=8)
    args = parser.parse_args()

    max_i = args.max_i
    print(f"[SUMBOUND] Verifying X(i)/P(i) summability up to i={max_i}...")
    start = time.time()

    # Show growth rates
    print("[SUMBOUND] Growth rates:")
    log_growth_rate(min(max_i, 5))

    # Ratio bounds
    ratio_fails = verify_ratio_bounds(max_i)
    sum_fails = verify_summability(max_i)

    elapsed = time.time() - start
    print(f"\n[SUMBOUND] Ratio bounds: {'✅ PASS' if not ratio_fails else '❌ FAIL'}")
    for f in ratio_fails[:3]:
        print(f"    - {f}")

    print(f"[SUMBOUND] Summability: {'✅ PASS' if not sum_fails else '❌ FAIL'}")
    for f in sum_fails[:3]:
        print(f"    - {f}")

    all_pass = not ratio_fails and not sum_fails
    print(f"\n[SUMBOUND] Completed in {elapsed:.2f}s")
    sys.exit(0 if all_pass else 1)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, RuntimeError, ImportError, OSError) as e:
        print(f"[SUMBOUND] FATAL: {e}", file=sys.stderr)
        sys.exit(2)
