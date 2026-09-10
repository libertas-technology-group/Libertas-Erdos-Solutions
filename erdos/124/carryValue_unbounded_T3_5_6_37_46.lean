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


-- Since j ≥ e and J0 ≥ e, we can use strong induction on j
-- Prove by induction on j - J0
-- Use induction on the difference
-- Induction on k
-- Apply hflip with j = J0
-- Apply hflip with j = J0 + k
-- Substitute j = J0 + k
set_option maxHeartbeats 200000
open Finset
namespace Erdos124.W3G4
/-- The carry family at level j: the doubling of the j-th window-base
    power is representable in the full tuple (closed theory §1). -/
def carryValue (D : Finset ℕ) (d j : ℕ) : Prop :=
  2 * d ^ j ∈ representableSet D 1
/-- The window anchor for tuple (3, 5, 6, 37, 46) (closed theory §0). -/
def anchor (D : Finset ℕ) : ℕ := 501
end Erdos124.W3G4
open Erdos124.W3G4
lemma carryValue_unbounded_T3_5_6_37_46 (D : Finset ℕ) (d e J0 : ℕ)
    (hdD : d ∈ D) (hD₃ : ∀ d ∈ D, 3 ≤ d) (he : 1 ≤ e) (heJ0 : e ≤ J0)
    (hanch : d ^ e ≥ anchor D)
    (hbase : ∀ j ∈ Set.Icc e J0, carryValue D d j)
    (hflip : ∀ j ≥ e, carryValue D d j → carryValue D d (j + 1)) :
    ∀ j ≥ e, carryValue D d j := by
  intro j hj
  by_cases hJ : j ≤ J0
  · -- j is in the base interval [e, J0]
    have hjIcc : j ∈ Set.Icc e J0 := ⟨hj, hJ⟩
    exact hbase j hjIcc
  · -- j > J0, need to induct from the base case
    have hgt : J0 < j := Nat.lt_of_not_ge hJ
    have hJge : e ≤ J0 := heJ0
    have hjgeJ : J0 ≤ j := Nat.le_of_lt hgt
    let k := j - J0
    have hkpos : 0 < k := Nat.sub_pos_of_lt hgt
    have hkdef : j = J0 + k := by
      omega
    have hmain : ∀ k : ℕ, 0 < k → carryValue D d (J0 + k) := by
      intro k hk
      induction k with
      | zero =>
        exfalso
        exact Nat.not_lt_zero 0 hk
      | succ k ih =>
        by_cases hk0 : k = 0
        · -- k = 0, so J0 + 1
          subst k
          have hbaseJ0 : carryValue D d J0 := by
            have hJ0in : J0 ∈ Set.Icc e J0 := ⟨heJ0, le_rfl⟩
            exact hbase J0 hJ0in
          have hflipJ0 : carryValue D d (J0 + 1) := hflip J0 heJ0 hbaseJ0
          exact hflipJ0
        · -- k > 0, so J0 + (k+1) = (J0 + k) + 1
          have hkge : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
          have hih : carryValue D d (J0 + k) := ih (Nat.lt_of_lt_of_le (Nat.zero_lt_one) hkge)
          have hjkge : e ≤ J0 + k := by omega
          have hflipk : carryValue D d ((J0 + k) + 1) := hflip (J0 + k) hjkge hih
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hflipk
    have hk : k > 0 := hkpos
    have hresult : carryValue D d (J0 + k) := hmain k hk
    simpa [hkdef] using hresult