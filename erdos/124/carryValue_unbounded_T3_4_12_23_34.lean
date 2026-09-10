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


set_option maxHeartbeats 200000
open Finset
namespace Erdos124.W3G4
/-- The carry family at level j: the doubling of the j-th window-base
    power is representable in the full tuple (closed theory §1). -/
def carryValue (D : Finset ℕ) (d j : ℕ) : Prop :=
  2 * d ^ j ∈ representableSet D 1
/-- The window anchor for tuple (3, 4, 12, 23, 34) (closed theory §0). -/
def anchor (D : Finset ℕ) : ℕ := 501
end Erdos124.W3G4
open Erdos124.W3G4
lemma carryValue_unbounded_T3_4_12_23_34 (D : Finset ℕ) (d e J0 : ℕ)
    (hdD : d ∈ D) (hD₃ : ∀ d ∈ D, 3 ≤ d) (he : 1 ≤ e) (heJ0 : e ≤ J0)
    (hanch : d ^ e ≥ anchor D)
    (hbase : ∀ j ∈ Set.Icc e J0, carryValue D d j)
    (hflip : ∀ j ≥ e, carryValue D d j → carryValue D d (j + 1)) :
    ∀ j ≥ e, carryValue D d j := by
  intro j hj
  by_cases hJ : j ≤ J0
  · exact hbase j (by exact ⟨hj, hJ⟩)
  · have hgt : J0 < j := Nat.lt_of_not_ge hJ
    have hgeJ0 : J0 ≥ e := heJ0
    have hbaseJ0 : carryValue D d J0 := hbase J0 (by exact ⟨heJ0, le_rfl⟩)
    have hstep : ∀ k, carryValue D d (J0 + k) := by
      intro k
      induction k with
      | zero => simpa using hbaseJ0
      | succ k ih =>
          have hk : J0 + k ≥ e := by
            calc
              J0 + k ≥ J0 := Nat.le_add_right _ _
              _ ≥ e := heJ0
          have hstep' : carryValue D d (J0 + k + 1) := hflip (J0 + k) hk ih
          simpa [Nat.add_assoc] using hstep'
    have hk : j = J0 + (j - J0) := by
      exact (Nat.add_sub_of_le (le_of_lt hgt)).symm
    rw [hk]
    exact hstep (j - J0)