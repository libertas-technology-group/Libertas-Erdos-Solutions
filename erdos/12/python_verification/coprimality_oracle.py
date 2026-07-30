#!/usr/bin/env python3
"""
coprimality_oracle.py — Verify Erdos12 coprime sequence properties.

Verifies the following:
  A. F(i) >= 3 for all i
  B. F(i) and F(j) are coprime for i != j
  C. F(i) <= 2^(i+2) (via Bertrand's postulate)
  D. F(i) is pairwise coprime with M(i)

Copyright (C) 2026 Libertas Technology Group Ltd. All rights reserved.
"""

from __future__ import annotations

import math
import sys
import time
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from erdos12_primitives import M_seq, coprime_sequence, is_pairwise_coprime


def verify_ge_3(max_i: int) -> tuple[bool, list[str]]:
    """Check F(i) >= 3 for all i."""
    failures: list[str] = []
    for i in range(max_i):
        val = coprime_sequence(i)
        if val < 3:
            failures.append(f"i={i}: F({i}) = {val} < 3")
    return len(failures) == 0, failures


def verify_pairwise_coprime(max_i: int) -> tuple[bool, list[str]]:
    """Check F(i) and F(j) are coprime for i != j."""
    failures: list[str] = []
    values = [coprime_sequence(i) for i in range(max_i)]
    if not is_pairwise_coprime(values):
        for i in range(len(values)):
            for j in range(i + 1, len(values)):
                g = math.gcd(values[i], values[j])
                if g != 1:
                    failures.append(f"F({i})={values[i]}, F({j})={values[j]}: gcd={g}")
    return len(failures) == 0, failures


def verify_F_bound(max_i: int) -> tuple[bool, list[str]]:
    """Check F(i) <= 2^(i+2) (Bertrand's postulate bound)."""
    failures: list[str] = []
    for i in range(max_i):
        val = coprime_sequence(i)
        bound = 2 ** (i + 2)
        if val > bound:
            failures.append(f"i={i}: F({i}) = {val} > 2^{i+2} = {bound}")
    return len(failures) == 0, failures


def verify_FM_coprime(max_i: int) -> tuple[bool, list[str]]:
    """Check F(i) and M(i) are coprime."""
    failures: list[str] = []
    for i in range(max_i):
        fi = coprime_sequence(i)
        mi = M_seq(i)
        if math.gcd(fi, mi) != 1:
            failures.append(f"i={i}: gcd(F({i}), M({i})) = {math.gcd(fi, mi)} != 1")
    return len(failures) == 0, failures


def main() -> None:
    import argparse
    parser = argparse.ArgumentParser(description="Verify Erdos12 coprime sequence.")
    parser.add_argument("--max-i", type=int, default=10)
    args = parser.parse_args()

    max_i = args.max_i
    print(f"[COPRIME] Verifying coprime sequence up to i={max_i}...")
    start = time.time()

    checks = [
        ("A: F(i) >= 3", verify_ge_3(max_i)),
        ("B: Pairwise coprime", verify_pairwise_coprime(max_i)),
        ("C: F(i) <= 2^(i+2)", verify_F_bound(max_i)),
        ("D: gcd(F(i), M(i)) = 1", verify_FM_coprime(max_i)),
    ]

    all_pass = True
    for name, (passed, failures) in checks:
        if passed:
            print(f"  ✅ {name}: PASS")
        else:
            all_pass = False
            print(f"  ❌ {name}: FAIL")
            for f in failures[:5]:
                print(f"      - {f}")

    elapsed = time.time() - start
    print(f"\n[COPRIME] Completed in {elapsed:.2f}s")
    sys.exit(0 if all_pass else 1)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, RuntimeError, ImportError, OSError) as e:
        print(f"[COPRIME] FATAL: {e}", file=sys.stderr)
        sys.exit(2)
