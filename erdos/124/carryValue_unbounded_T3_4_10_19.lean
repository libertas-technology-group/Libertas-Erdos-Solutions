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


-- If j ≤ J0, use hbase
-- Induct from J0 up to j using hflip
-- Use Nat.le_induction for the forward direction
set_option maxHeartbeats 200000
open Finset
namespace Erdos124.W3G4
/-- The carry family at level j: the doubling of the j-th window-base
    power is representable in the full tuple (closed theory §1). -/
def carryValue (D : Finset ℕ) (d j : ℕ) : Prop :=
  2 * d ^ j ∈ representableSet D 1
/-- The window anchor for tuple (3, 4, 10, 19) (closed theory §0). -/
def anchor (D : Finset ℕ) : ℕ := 501
end Erdos124.W3G4
open Erdos124.W3G4
lemma carryValue_unbounded_T3_4_10_19 (D : Finset ℕ) (d e J0 : ℕ)
    (hdD : d ∈ D) (hD₃ : ∀ d ∈ D, 3 ≤ d) (he : 1 ≤ e) (heJ0 : e ≤ J0)
    (hanch : d ^ e ≥ anchor D)
    (hbase : ∀ j ∈ Set.Icc e J0, carryValue D d j)
    (hflip : ∀ j ≥ e, carryValue D d j → carryValue D d (j + 1)) :
    ∀ j ≥ e, carryValue D d j := by
  intro j hj
  by_cases hjJ0 : j ≤ J0
  · have hjIcc : j ∈ Set.Icc e J0 := by
      exact Set.mem_Icc.mpr ⟨hj, hjJ0⟩
    exact hbase j hjIcc
  · -- j > J0, so j ≥ J0 + 1
    have hjJ0' : J0 < j := by omega
    have hinit : carryValue D d J0 := by
      have hJ0Icc : J0 ∈ Set.Icc e J0 := by
        exact Set.mem_Icc.mpr ⟨heJ0, le_rfl⟩
      exact hbase J0 hJ0Icc
    have hstep : ∀ k, J0 ≤ k → carryValue D d k → carryValue D d (k + 1) := by
      intro k hk hck
      have hkge : k ≥ e := by omega
      exact hflip k hkge hck
    have hfinal : carryValue D d j := by
      exact Nat.le_induction hinit hstep j (by omega)
    exact hfinal