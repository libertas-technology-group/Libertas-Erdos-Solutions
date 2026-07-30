"""
erdos12_primitives.py — Shared primitives for Erdos #12 block density proof.

Erdos #12 (Erdos--Selfridge--Eggleton): Does there exist an infinite set A
of positive integers such that for every triple a < b < c in A,
b + c is not divisible by a?

This module provides the block construction primitives:
  - f(n): recursively defined injection (f(0)=0; f(n+1)=3*f((n+1)/2)+(n+1)%2)
  - F(i): pairwise coprime sequence (F(i) >= 3, pairwise coprime)
  - M(i) := product_{j < i} F(j)
  - V(i) := F(i) * M(i)
  - Y(i) := 3^{(i+20)^3}
  - P(i) := 10 * (V(i) * Y(i)) + C(i)   (C(i) from CRT)
  - X(i) := floor(sqrt(P(i+1)))
  - MyBlock(i) := { P(i) + V(i) * f(y) | y < X(i) }

This module contains ONLY pure functions — no I/O, no hardcoded paths.

Copyright (C) 2026 Libertas Technology Group Ltd. All rights reserved.
"""

from __future__ import annotations

import functools
import math
from collections.abc import Iterator

# ═══════════════════════════════════════════════════════════════════════════════
# 1. Sequence Primitives
# ═══════════════════════════════════════════════════════════════════════════════


def f(n: int) -> int:
    """Recursively defined injection used in block construction.

    f(0) = 0
    f(n+1) = 3 * f((n+1)//2) + (n+1) % 2

    Parameters
    ----------
    n : int
        Non-negative integer index.

    Returns
    -------
    int
        The f-value at *n*.
    """
    if n < 0:
        raise ValueError(f"n must be non-negative, got {n}")
    if n == 0:
        return 0
    return 3 * f(n // 2) + (n % 2)


def is_prime(n: int) -> bool:
    """Check if *n* is prime.

    Parameters
    ----------
    n : int
        Integer to test (n >= 2).

    Returns
    -------
    bool
        True if *n* is prime.
    """
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    for i in range(3, int(math.isqrt(n)) + 1, 2):
        if n % i == 0:
            return False
    return True


def primes_upto(limit: int) -> list[int]:
    """Sieve of Eratosthenes returning all primes <= *limit*.

    Parameters
    ----------
    limit : int
        Upper bound (inclusive).

    Returns
    -------
    list[int]
        Sorted list of primes <= *limit*.
    """
    if limit < 2:
        return []
    sieve = [True] * (limit + 1)
    sieve[0:2] = [False, False]
    for p in range(2, int(limit ** 0.5) + 1):
        if sieve[p]:
            step = p
            start = p * p
            sieve[start:limit + 1:step] = [False] * ((limit - start) // step + 1)
    return [i for i, is_p in enumerate(sieve) if is_p]


def bertrand_prime(n: int) -> int:
    """Return a prime p with n < p < 2n (Bertrand's postulate).

    Parameters
    ----------
    n : int
        Lower bound (n >= 1).

    Returns
    -------
    int
        A prime strictly between *n* and *2n*.

    Raises
    ------
    ValueError
        If *n* < 1.
    """
    if n < 1:
        raise ValueError(f"n must be >= 1, got {n}")
    candidate = n + 1
    while candidate < 2 * n:
        if is_prime(candidate):
            return candidate
        candidate += 1
    # Should never reach here (Bertrand's postulate guarantees existence)
    raise RuntimeError(f"No prime found between {n} and {2 * n}")


@functools.cache
def coprime_sequence(i: int) -> int:
    """Generate the i-th term of a pairwise coprime sequence.

    Uses primes starting from 3: F(i) = p_{i+2} where p_k is the k-th prime.

    Parameters
    ----------
    i : int
        Index (i >= 0).

    Returns
    -------
    int
        The i-th term, guaranteed >= 3 and pairwise coprime.
    """
    # F(0) = 3, F(1) = 5, F(2) = 7, ...
    count = 0
    n = 2
    while True:
        if is_prime(n):
            if count == i + 1:  # skip 2, start from 3
                return n
            count += 1
        n += 1


# ═══════════════════════════════════════════════════════════════════════════════
# 2. Block Construction Primitives
# ═══════════════════════════════════════════════════════════════════════════════


def F_seq(i: int) -> int:
    """Alias for coprime_sequence(i).

    Parameters
    ----------
    i : int
        Index.

    Returns
    -------
    int
        F(i) = coprime_sequence(i).
    """
    return coprime_sequence(i)


@functools.cache
def M_seq(i: int) -> int:
    """M(i) = product_{j < i} F(j).

    Parameters
    ----------
    i : int
        Index.

    Returns
    -------
    int
        M(0) = 1, M(i) = F(0) * F(1) * ... * F(i-1) for i > 0.
    """
    if i <= 0:
        return 1
    prod = 1
    for j in range(i):
        prod *= coprime_sequence(j)
    return prod


def V_seq(i: int) -> int:
    """V(i) = F(i) * M(i).

    Parameters
    ----------
    i : int
        Index.

    Returns
    -------
    int
        V(i).
    """
    return coprime_sequence(i) * M_seq(i)


def Y_seq(i: int) -> int:
    """Y(i) = 3^{(i+20)^3}.

    Parameters
    ----------
    i : int
        Index.

    Returns
    -------
    int
        Y(i) — the exponential growth factor.
    """
    return 3 ** ((i + 20) ** 3)


@functools.cache
def C_crt(i: int) -> int:
    """CRT constant C(i) satisfying C(i) mod F(i) = 0 and C(i) mod M(i) = 1.

    Uses brute-force Chinese Remainder Theorem search.

    Parameters
    ----------
    i : int
        Index.

    Returns
    -------
    int
        C(i), the smallest non-negative solution.
    """
    fi = coprime_sequence(i)
    mi = M_seq(i)
    # Edge case: M(i) = 1 (empty product for i=0)
    if mi == 1:
        return 0  # 0 % F(0) = 0, and any int ≡ 0 ≡ 1 (mod 1)
    # Naive CRT: find c such that c % fi == 0 and c % mi == 1
    # Since gcd(fi, mi) = 1, modular inverse exists
    return fi * pow(fi, -1, mi)


def P_seq(i: int) -> int:
    """P(i) = 10 * (V(i) * Y(i)) + C(i).

    The start point of the i-th block.

    Parameters
    ----------
    i : int
        Index.

    Returns
    -------
    int
        P(i).
    """
    return 10 * (V_seq(i) * Y_seq(i)) + C_crt(i)


def X_seq(i: int) -> int:
    """X(i) = floor(sqrt(P(i+1))).

    The cardinality of the i-th block.

    Parameters
    ----------
    i : int
        Index.

    Returns
    -------
    int
        X(i).
    """
    return int(math.isqrt(P_seq(i + 1)))


def block_elements(i: int) -> Iterator[int]:
    """Yield the elements of MyBlock(i).

    MyBlock(i) = { P(i) + V(i) * f(y) | y < X(i) }.

    Parameters
    ----------
    i : int
        Block index.

    Yields
    ------
    int
        Elements of the block in increasing order.
    """
    p_i = P_seq(i)
    v_i = V_seq(i)
    x_i = X_seq(i)
    for y in range(x_i):
        yield p_i + v_i * f(y)


# ═══════════════════════════════════════════════════════════════════════════════
# 3. Verification Helpers
# ═══════════════════════════════════════════════════════════════════════════════


def is_pairwise_coprime(values: list[int]) -> bool:
    """Check that all pairs in *values* are coprime.

    Parameters
    ----------
    values : list[int]
        List of integers to check.

    Returns
    -------
    bool
        True if every pair has gcd = 1.
    """
    for i in range(len(values)):
        for j in range(i + 1, len(values)):
            if math.gcd(values[i], values[j]) != 1:
                return False
    return True
