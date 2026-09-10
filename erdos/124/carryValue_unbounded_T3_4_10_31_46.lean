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


-- Induction on the difference j - J0
-- Strong induction on j - J0
set_option maxHeartbeats 200000
open Finset
namespace Erdos124.W3G4
/-- The carry family at level j: the doubling of the j-th window-base
    power is representable in the full tuple (closed theory §1). -/
def carryValue (D : Finset ℕ) (d j : ℕ) : Prop :=
  2 * d ^ j ∈ representableSet D 1
/-- The window anchor for tuple (3, 4, 10, 31, 46) (closed theory §0). -/
def anchor (D : Finset ℕ) : ℕ := 501
end Erdos124.W3G4
open Erdos124.W3G4
lemma carryValue_unbounded_T3_4_10_31_46 (D : Finset ℕ) (d e J0 : ℕ)
    (hdD : d ∈ D) (hD₃ : ∀ d ∈ D, 3 ≤ d) (he : 1 ≤ e) (heJ0 : e ≤ J0)
    (hanch : d ^ e ≥ anchor D)
    (hbase : ∀ j ∈ Set.Icc e J0, carryValue D d j)
    (hflip : ∀ j ≥ e, carryValue D d j → carryValue D d (j + 1)) :
    ∀ j ≥ e, carryValue D d j := by
  intro j hj
  by_cases hjJ0 : j ≤ J0
  · have hjIcc : j ∈ Set.Icc e J0 := by
      exact ⟨hj, hjJ0⟩
    exact hbase j hjIcc
  · have hJ0lt : J0 < j := by omega
    have hdiff : 0 < j - J0 := by omega
    have hdiff_bound : j - J0 ≤ j := by omega
    have hmain : ∀ k : ℕ, k ≤ j - J0 → carryValue D d (J0 + k) := by
      intro k hk
      induction k with
      | zero =>
          have hJ0e : J0 ≥ e := heJ0
          have hJ0Icc : J0 ∈ Set.Icc e J0 := by
            exact ⟨hJ0e, le_rfl⟩
          exact hbase J0 hJ0Icc
      | succ k ih =>
          have hk_le : k ≤ j - J0 := by omega
          have hprev : carryValue D d (J0 + k) := ih hk_le
          have hge : J0 + k ≥ e := by omega
          have hstep : carryValue D d (J0 + k + 1) := hflip (J0 + k) hge hprev
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep
    have hJ0plus : J0 + (j - J0) = j := by omega
    have hcarry : carryValue D d (J0 + (j - J0)) := hmain (j - J0) (le_rfl)
    simpa [hJ0plus] using hcarry