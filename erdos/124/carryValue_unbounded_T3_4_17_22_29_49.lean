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


-- Induct on j, starting from J0
-- Use a well-founded induction on (j - J0)
-- Prove by induction on k
-- carryValue D d (J0 + k) → carryValue D d (J0 + k + 1)
-- Now rewrite J0 + k + 1 as J0 + (k+1)
-- Apply to k = j - J0
-- Rewrite J0 + (j - J0) = j
set_option maxHeartbeats 200000
open Finset
namespace Erdos124.W3G4
/-- The carry family at level j: the doubling of the j-th window-base
    power is representable in the full tuple (closed theory §1). -/
def carryValue (D : Finset ℕ) (d j : ℕ) : Prop :=
  2 * d ^ j ∈ representableSet D 1
/-- The window anchor for tuple (3, 4, 17, 22, 29, 49) (closed theory §0). -/
def anchor (D : Finset ℕ) : ℕ := 501
end Erdos124.W3G4
open Erdos124.W3G4
lemma carryValue_unbounded_T3_4_17_22_29_49 (D : Finset ℕ) (d e J0 : ℕ)
    (hdD : d ∈ D) (hD₃ : ∀ d ∈ D, 3 ≤ d) (he : 1 ≤ e) (heJ0 : e ≤ J0)
    (hanch : d ^ e ≥ anchor D)
    (hbase : ∀ j ∈ Set.Icc e J0, carryValue D d j)
    (hflip : ∀ j ≥ e, carryValue D d j → carryValue D d (j + 1)) :
    ∀ j ≥ e, carryValue D d j := by
  intro j hj
  by_cases hjJ0 : j ≤ J0
  · -- j is within the base interval [e, J0]
    have hjIcc : j ∈ Set.Icc e J0 := by
      exact Set.mem_Icc.mpr ⟨hj, hjJ0⟩
    exact hbase j hjIcc
  · -- j > J0, use induction from J0
    have hJ0ge : e ≤ J0 := heJ0
    have hJ0carry : carryValue D d J0 := by
      exact hbase J0 (Set.mem_Icc.mpr ⟨heJ0, le_rfl⟩)
    have hJ0le : J0 ≤ j := by
      exact le_of_not_ge hjJ0
    let k := j - J0
    have hkpos : 0 ≤ k := Nat.zero_le k
    have hjk : J0 + k = j := by
      omega
    have hmain : ∀ k : ℕ, carryValue D d (J0 + k) := by
      intro k
      induction k with
      | zero =>
          simpa using hJ0carry
      | succ k ih =>
          have hstep : carryValue D d (J0 + k + 1) := by
            apply hflip (J0 + k)
            · -- need J0 + k ≥ e
              have : e ≤ J0 + k := by
                omega
              exact this
            · exact ih
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep
    have hresult : carryValue D d (J0 + (j - J0)) := hmain (j - J0)
    have hrewrite : J0 + (j - J0) = j := by
      omega
    simpa [hrewrite] using hresult