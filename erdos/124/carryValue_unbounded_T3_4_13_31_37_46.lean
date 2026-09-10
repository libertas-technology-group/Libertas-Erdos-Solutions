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


-- We prove by strong induction on j, with the base case handled by hbase and
-- the induction step using hflip.
-- Use strong induction on n
-- Since n > J0 ≥ e, we have n - 1 ≥ e and n - 1 < n
-- Apply induction hypothesis to n - 1
-- Apply flip to get carryValue at n
-- Simplify n - 1 + 1 = n
set_option maxHeartbeats 200000
open Finset
namespace Erdos124.W3G4
/-- The carry family at level j: the doubling of the j-th window-base
    power is representable in the full tuple (closed theory §1). -/
def carryValue (D : Finset ℕ) (d j : ℕ) : Prop :=
  2 * d ^ j ∈ representableSet D 1
/-- The window anchor for tuple (3, 4, 13, 31, 37, 46) (closed theory §0). -/
def anchor (D : Finset ℕ) : ℕ := 501
end Erdos124.W3G4
open Erdos124.W3G4
lemma carryValue_unbounded_T3_4_13_31_37_46 (D : Finset ℕ) (d e J0 : ℕ)
    (hdD : d ∈ D) (hD₃ : ∀ d ∈ D, 3 ≤ d) (he : 1 ≤ e) (heJ0 : e ≤ J0)
    (hanch : d ^ e ≥ anchor D)
    (hbase : ∀ j ∈ Set.Icc e J0, carryValue D d j)
    (hflip : ∀ j ≥ e, carryValue D d j → carryValue D d (j + 1)) :
    ∀ j ≥ e, carryValue D d j := by
  intro j hj
  have h_ind : ∀ n ≥ e, carryValue D d n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih
    intro hn
    by_cases hn_le_J0 : n ≤ J0
    · -- Case n ≤ J0: use the base hypothesis
      have hn_in_Icc : n ∈ Set.Icc e J0 := by
        exact Set.mem_Icc.mpr ⟨hn, hn_le_J0⟩
      exact hbase n hn_in_Icc
    · -- Case n > J0: use the flip hypothesis repeatedly
      have hn_gt_J0 : J0 < n := Nat.lt_of_not_ge hn_le_J0
      have hn_minus1_ge_e : e ≤ n - 1 := by
        omega
      have hn_minus1_lt_n : n - 1 < n := Nat.sub_lt (by omega) (by omega)
      have hprev : carryValue D d (n - 1) := ih (n - 1) hn_minus1_lt_n hn_minus1_ge_e
      have hflip_n : carryValue D d (n - 1 + 1) := hflip (n - 1) hn_minus1_ge_e hprev
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hflip_n
  exact h_ind j hj