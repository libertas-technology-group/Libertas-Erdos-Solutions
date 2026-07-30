/-
Copyright 2026 Libertas Technology Group Limited

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Lemma `exists_coprime_seq` — Pairwise Coprime Sequence Bounded by Powers of 2

Lemma adapted for the Libertas Erdős #12 proof of Erdős Problem #12.
Constructs a sequence `F : ℕ → ℕ` where:
- Every term is ≥ 3
- Distinct terms are coprime
- `F i ≤ 2^(i+2)` (via Bertrand's postulate)

Relies on `Nat.exists_infinite_primes` from mathlib.
-/

open Classical Filter Set

namespace Erdos12

@[category API, AMS 11]
lemma exists_coprime_seq : ∃ F : ℕ → ℕ, (∀ i, F i ≥ 3) ∧ (∀ i j, i ≠ j → Nat.Coprime (F i) (F j)) ∧ (∀ i, F i ≤ 2^(i + 2)) := by
  -- The set of primes is infinite
  have hprime_infinite : Set.Infinite {q | Nat.Prime q} :=
    Nat.infinite_setOf_prime

  -- p is the prime enumeration: p n = the n-th prime (0-indexed)
  let p : ℕ → ℕ := Nat.nth {q | Nat.Prime q}
  have hp_strictMono : StrictMono p := Nat.nth_strictMono hprime_infinite
  have hp_prime (n : ℕ) : Nat.Prime (p n) :=
    Nat.nth_mem_of_infinite hprime_infinite n
  have hp_injective : Function.Injective p :=
    Nat.nth_injective hprime_infinite

  -- Lemma: p (k+1) ≤ 2 * p k  (Bertrand's postulate applied to the prime enumeration)
  have h_step (k : ℕ) : p (k + 1) ≤ 2 * p k := by
    have hp_pos : p k ≠ 0 := Nat.Prime.ne_zero (hp_prime k)
    rcases Nat.exists_prime_lt_and_le_two_mul (p k) hp_pos with ⟨q, hq_prime, hq_lt, hq_le⟩
    have hq_range : q ∈ Set.range p := by
      unfold p
      have hq_mem : q ∈ setOf Nat.Prime := hq_prime
      exact (Nat.range_nth_of_infinite hprime_infinite).symm ▸ hq_mem
    rcases hq_range with ⟨m, hm⟩
    have hm_ge : k + 1 ≤ m := by
      by_contra! h_lt
      have hm_le_k : m ≤ k := by omega
      have hle : p m ≤ p k := hp_strictMono.monotone hm_le_k
      rw [hm] at hle
      omega
    have : p (k + 1) ≤ p m := hp_strictMono.monotone hm_ge
    rw [hm] at this
    omega

  -- Lemma: p n ≤ 2^(n+1) for all n  (bound on the n-th prime)
  have h_bound (n : ℕ) : p n ≤ 2^(n+1) := by
    induction' n with n ih
    · -- Base: p 0 = 2 ≤ 2^1
      have hp0_prime : Nat.Prime (p 0) := hp_prime 0
      have h2_prime : Nat.Prime 2 := by norm_num
      have h_one_lt : 1 < p 0 := Nat.Prime.one_lt hp0_prime
      have h2_le_p0 : 2 ≤ p 0 := by omega
      have hp0_le_2 : p 0 ≤ 2 := by
        have h2_range : 2 ∈ Set.range p := by
          unfold p
          have h2_mem : 2 ∈ setOf Nat.Prime := h2_prime
          exact (Nat.range_nth_of_infinite hprime_infinite).symm ▸ h2_mem
        rcases h2_range with ⟨m, hm⟩
        calc
          p 0 ≤ p m := hp_strictMono.monotone (Nat.zero_le m)
          _ = 2 := hm
      have hp0 : p 0 = 2 := Nat.le_antisymm hp0_le_2 h2_le_p0
      rw [hp0]
      norm_num
    · -- Step: p (n+1) ≤ 2 * p n ≤ 2 * 2^(n+1) = 2^(n+2)
      have hle : p (n + 1) ≤ 2 * p n := h_step n
      have h_pow : 2^(n+2) = 2 * 2^(n+1) := by ring
      rw [h_pow]
      nlinarith

  -- Construct F i = p (i + 1), i.e., primes starting from the second prime (3)
  refine ⟨λ i => p (i + 1), ?_, ?_, ?_⟩

  · -- Part 1: F i ≥ 3
    intro i
    have hp1 : Nat.Prime (p (i + 1)) := hp_prime (i + 1)
    have hp0 : p 0 = 2 := by
      have hp0_prime : Nat.Prime (p 0) := hp_prime 0
      have h2_prime : Nat.Prime 2 := by norm_num
      have h_one_lt : 1 < p 0 := Nat.Prime.one_lt hp0_prime
      have h2_le_p0 : 2 ≤ p 0 := by omega
      have hp0_le_2 : p 0 ≤ 2 := by
        have h2_range : 2 ∈ Set.range p := by
          unfold p
          have h2_mem : 2 ∈ setOf Nat.Prime := h2_prime
          exact (Nat.range_nth_of_infinite hprime_infinite).symm ▸ h2_mem
        rcases h2_range with ⟨m, hm⟩
        calc
          p 0 ≤ p m := hp_strictMono.monotone (Nat.zero_le m)
          _ = 2 := hm
      exact Nat.le_antisymm hp0_le_2 h2_le_p0
    have h2_lt : 2 < p (i + 1) :=
      calc
        2 = p 0 := hp0.symm
        _ < p (i + 1) := hp_strictMono (Nat.zero_lt_succ i)
    exact Nat.succ_le_of_lt h2_lt

  · -- Part 2: F i and F j are coprime for i ≠ j
    intro i j h_ne
    have hp_i : Nat.Prime (p (i + 1)) := hp_prime (i + 1)
    have hp_j : Nat.Prime (p (j + 1)) := hp_prime (j + 1)
    have hne_succ : i + 1 ≠ j + 1 := by
      intro h_eq; apply h_ne; omega
    have h_ne' : p (i + 1) ≠ p (j + 1) :=
      hp_injective.ne hne_succ
    exact ((Nat.coprime_primes hp_i hp_j).mpr h_ne')

  · -- Part 3: F i ≤ 2^(i+2)
    intro i
    have : p (i + 1) ≤ 2^((i + 1) + 1) := h_bound (i + 1)
    have h_exp : (i + 1) + 1 = i + 2 := by omega
    rw [h_exp] at this
    exact this

end Erdos12
