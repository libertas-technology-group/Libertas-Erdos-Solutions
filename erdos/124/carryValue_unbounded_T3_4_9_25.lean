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


-- We prove by strong induction on j, starting from the base interval [e, J0].
-- The key is that hbase covers j ≤ J0, and hflip extends beyond J0.
-- First, handle the case j ≤ J0 using hbase.
-- Induct on the difference j - J0.
-- We'll prove by induction on k = j - J0 that carryValue D d (J0 + k) holds.
-- Strong induction on k.
-- Induction on k with the base case k = 1 handled via hflip from J0.
-- We use Nat.le_induction for a clean induction.
-- Apply hflip with j = J0, since J0 ≥ e.
-- Need carryValue D d (J0 + (k+1)) = carryValue D d ((J0 + k) + 1)
-- Rewrite to match the form J0 + (k+1)
-- Now instantiate with k = j - J0
-- Rewrite J0 + (j - J0) = j
set_option maxHeartbeats 200000
open Finset
namespace Erdos124.W3G4
/-- The carry family at level j: the doubling of the j-th window-base
    power is representable in the full tuple (closed theory §1). -/
def carryValue (D : Finset ℕ) (d j : ℕ) : Prop :=
  2 * d ^ j ∈ representableSet D 1
/-- The window anchor for tuple (3, 4, 9, 25) (closed theory §0). -/
def anchor (D : Finset ℕ) : ℕ := 659
end Erdos124.W3G4
open Erdos124.W3G4
lemma carryValue_unbounded_T3_4_9_25 (D : Finset ℕ) (d e J0 : ℕ)
    (hdD : d ∈ D) (hD₃ : ∀ d ∈ D, 3 ≤ d) (he : 1 ≤ e) (heJ0 : e ≤ J0)
    (hanch : d ^ e ≥ anchor D)
    (hbase : ∀ j ∈ Set.Icc e J0, carryValue D d j)
    (hflip : ∀ j ≥ e, carryValue D d j → carryValue D d (j + 1)) :
    ∀ j ≥ e, carryValue D d j := by
  intro j hj
  have hJ0_ge : J0 ≥ e := heJ0
  by_cases hj_le_J0 : j ≤ J0
  · -- j ∈ [e, J0]
    exact hbase j (by
      simp only [Set.mem_Icc]
      exact ⟨hj, hj_le_J0⟩
    )
  · -- j > J0, so we need to use hflip repeatedly.
    have hj_gt_J0 : J0 < j := Nat.lt_of_not_ge hj_le_J0
    have hdiff : j - J0 ≥ 1 := by
      exact Nat.succ_le_of_lt (Nat.sub_pos_of_lt hj_gt_J0)
    let k := j - J0
    have hk_ge_1 : 1 ≤ k := hdiff
    have hJ0_plus_k : J0 + k = j := by
      omega
    have hmain : ∀ k : ℕ, 1 ≤ k → carryValue D d (J0 + k) := by
      intro k hk
      refine Nat.le_induction ?base ?step k hk
      · -- Base case: k = 1, need carryValue D d (J0 + 1)
        have hJ0_in_Icc : J0 ∈ Set.Icc e J0 := by
          simp only [Set.mem_Icc]
          exact ⟨heJ0, le_rfl⟩
        have hJ0_carry : carryValue D d J0 := hbase J0 hJ0_in_Icc
        have hJ0_ge_e : J0 ≥ e := heJ0
        exact hflip J0 hJ0_ge_e hJ0_carry
      · -- Step: assume carryValue D d (J0 + k) for k ≥ 1, prove for k+1.
        intro k hk_ge_1 ih
        have hJ0_plus_k_ge_e : J0 + k ≥ e := by
          omega
        have hstep : carryValue D d ((J0 + k) + 1) := hflip (J0 + k) hJ0_plus_k_ge_e ih
        have hrewrite : J0 + (k + 1) = (J0 + k) + 1 := by omega
        simpa [hrewrite] using hstep
    have hk_def : k = j - J0 := rfl
    have htarget : carryValue D d (J0 + (j - J0)) := hmain (j - J0) hdiff
    have hJ0_sub : J0 + (j - J0) = j := by omega
    simpa [hJ0_sub] using htarget