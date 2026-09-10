/- 
Copyright 2026 Libertas Technology Group Limited.

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

import Mathlib
import FormalConjectures.Erdos124.Basic





-- Make the carry-family vocabulary visible to the lemma body.


-- We prove the result by well-founded induction on j - e, using the "flip" hypothesis
-- to step from j to j+1, and the base hypothesis for j in [e, J0].
-- Define the difference n = j - e, and prove j = e + n
-- Prove n ≥ 0 (trivial) and use strong induction on n
-- We use induction on n with the well-founded relation < on ℕ
-- The induction hypothesis: for all m < n, carryValue D d (e + m)
-- We need to show carryValue D d (e + n)
-- We proceed by strong induction on n
-- Rewrite j to e + n in the goal
-- Now prove by strong induction on n
-- We use the standard well-founded induction on ℕ
-- Define the induction predicate
-- We show P n for all n
-- Apply well-founded induction on n
-- We use the fact that < on ℕ is well-founded
-- The induction principle: for all n, (∀ m < n, P m) → P n
-- We prove this by cases on n
-- Case n = 0: j = e, need to show carryValue D d e
-- Since e ≤ J0 (from heJ0) and e ≥ e, we have e ∈ Set.Icc e J0
-- So hbase gives carryValue D d e
-- Case n = n+1: assume for all m ≤ n, carryValue D d (e + m)
-- Then in particular carryValue D d (e + n), and by hflip with j = e+n, we get carryValue D d (e+n+1)
-- This completes the induction
-- We formalize this below
-- First, note that e ∈ Set.Icc e J0
-- Now do the strong induction
-- We use the well-founded induction principle on ℕ with the usual < relation
-- The predicate is P
-- We prove ∀ n, P n by strong induction
-- The induction step: assume ih : ∀ m < n, P m, show P n
-- We do cases on n
-- Case n = 0: show P 0, i.e., carryValue D d (e + 0) = carryValue D d e
-- This follows from hbase he_Icc
-- Case n = n+1: show P (n+1), i.e., carryValue D d (e + (n+1))
-- Since e + (n+1) = (e + n) + 1, and we have P n from ih (since n < n+1), 
-- we apply hflip with j = e + n
-- Note: e + n ≥ e, so hflip applies
-- This gives carryValue D d (e + n + 1) = carryValue D d (e + (n+1))
-- Done
-- We now write this formally using the well-founded induction tactic
-- We use the induction principle on ℕ with the well-founded relation <
-- The tactic `well_founded_induction` or `induction` with `using` can be used
-- We'll use `induction n using Nat.strong_induction_on` or similar
-- Actually, in Lean 4, we can use `induction n with | zero => ... | succ n ih => ...`
-- But we need the strong induction hypothesis, so we use `Nat.strong_induction_on`
-- Let's proceed:
-- We need to show P n
-- Cases on n
-- n = 0, show P 0 = carryValue D d (e + 0) = carryValue D d e
-- This is exactly hbase applied to e ∈ [e, J0]
-- n = n'+1, show P (n'+1) = carryValue D d (e + (n'+1))
-- We have ih : ∀ m < n'+1, P m
-- In particular, for m = n', since n' < n'+1, we have P n' = carryValue D d (e + n')
-- We need carryValue D d (e + (n'+1))
-- Note: e + (n'+1) = (e + n') + 1
-- We apply hflip with j = e + n'
-- First, we need j ≥ e: e + n' ≥ e (trivial)
-- Second, we need carryValue D d (e + n') which is P n'
-- From ih: since n' < n'+1, we have ih n' (by omega : n' < n'+1)
-- So we have hPn' : P n' = carryValue D d (e + n')
-- Then hflip (e + n') (by omega : e + n' ≥ e) hPn' gives carryValue D d (e + n' + 1)
-- But e + n' + 1 = e + (n'+1), so we are done
-- Let's write this formally
-- Now e + n' ≥ e
-- Apply hflip
-- But e + n' + 1 = e + (n'+1), so rewrite
-- Note: e + n' + 1 = e + (n' + 1) by omega
-- So hstep has type carryValue D d (e + (n' + 1))
-- But the goal is P (n'+1) = carryValue D d (e + (n'+1))
-- So we need to rewrite or show equality
-- We can use simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep
-- Or simply: since e + n' + 1 = e + (n' + 1), we can convert
-- Let's use convert or simpa
set_option maxHeartbeats 200000
open Finset
namespace Erdos124.W3G4
/-- The carry family at level j: the doubling of the j-th window-base
    power is representable in the full tuple (closed theory §1). -/
def carryValue (D : Finset ℕ) (d j : ℕ) : Prop :=
  2 * d ^ j ∈ representableSet D 1
/-- The window anchor for tuple (3, 4, 21, 22, 29, 31) (closed theory §0). -/
def anchor (D : Finset ℕ) : ℕ := 501
end Erdos124.W3G4
open Erdos124.W3G4
lemma carryValue_unbounded_T3_4_21_22_29_31 (D : Finset ℕ) (d e J0 : ℕ)
    (hdD : d ∈ D) (hD₃ : ∀ d ∈ D, 3 ≤ d) (he : 1 ≤ e) (heJ0 : e ≤ J0)
    (hanch : d ^ e ≥ anchor D)
    (hbase : ∀ j ∈ Set.Icc e J0, carryValue D d j)
    (hflip : ∀ j ≥ e, carryValue D d j → carryValue D d (j + 1)) :
    ∀ j ≥ e, carryValue D d j := by
  intro j hj
  let n := j - e
  have hjn : j = e + n := by
    omega
  have hn_nonneg : 0 ≤ n := by omega
  rw [hjn]
  let P : ℕ → Prop := fun n => carryValue D d (e + n)
  change P n
  have he_Icc : e ∈ Set.Icc e J0 := by
    simp [Set.mem_Icc, he, heJ0]
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          exact hbase e he_Icc
      | succ n' =>
          have hPn' : P n' := ih n' (by omega)
          have hge : e + n' ≥ e := by omega
          have hstep : carryValue D d (e + n' + 1) := hflip (e + n') hge hPn'
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep