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


-- If j ≤ J0, use hbase directly.
-- We prove by strong induction on the distance from J0 to j.
-- Since j > J0, let k = j - (J0 + 1), so j = J0 + 1 + k.
-- We prove carryValue D d (J0 + 1 + k) by induction on k.
-- Base case: j = J0 + 1. We get carryValue D d J0 from hbase, then flip.
-- Inductive step: from carryValue D d (J0 + 1 + k) get carryValue D d (J0 + 1 + (k+1)).
-- Show (J0 + 1 + k) + 1 = J0 + 1 + (k+1)
-- Now use hmain with k = j - (J0 + 1).
-- Since j = J0 + 1 + k, we are done.
set_option maxHeartbeats 200000
open Finset
namespace Erdos124.W3G4
/-- The carry family at level j: the doubling of the j-th window-base
    power is representable in the full tuple (closed theory §1). -/
def carryValue (D : Finset ℕ) (d j : ℕ) : Prop :=
  2 * d ^ j ∈ representableSet D 1
/-- The window anchor for tuple (3, 4, 7) (closed theory §0). -/
def anchor (D : Finset ℕ) : ℕ := 582
end Erdos124.W3G4
open Erdos124.W3G4
lemma carryValue_unbounded_T3_4_7 (D : Finset ℕ) (d e J0 : ℕ)
    (hdD : d ∈ D) (hD₃ : ∀ d ∈ D, 3 ≤ d) (he : 1 ≤ e) (heJ0 : e ≤ J0)
    (hanch : d ^ e ≥ anchor D)
    (hbase : ∀ j ∈ Set.Icc e J0, carryValue D d j)
    (hflip : ∀ j ≥ e, carryValue D d j → carryValue D d (j + 1)) :
    ∀ j ≥ e, carryValue D d j := by
  intro j hj
  by_cases hjJ0 : j ≤ J0
  · exact hbase j (by simp [Set.Icc, hj, hjJ0])
  · -- Otherwise j > J0, so j ≥ J0 + 1.
    have hj_gt : J0 < j := Nat.lt_of_not_ge hjJ0
    let k := j - (J0 + 1)
    have hk_nonneg : 0 ≤ k := Nat.zero_le k
    have hjk : j = J0 + 1 + k := by
      omega
    have hmain : ∀ k : ℕ, carryValue D d (J0 + 1 + k) := by
      intro k
      induction k with
      | zero =>
          have hJ0 : carryValue D d J0 := hbase J0 (by simp [Set.Icc, heJ0])
          have hJ0_ge : J0 ≥ e := by omega
          exact hflip J0 hJ0_ge hJ0
      | succ k ih =>
          have hcur : carryValue D d (J0 + 1 + k) := ih
          have hcur_ge : J0 + 1 + k ≥ e := by omega
          have hnext : carryValue D d ((J0 + 1 + k) + 1) := hflip (J0 + 1 + k) hcur_ge hcur
          have hsimp : (J0 + 1 + k) + 1 = J0 + 1 + (k + 1) := by omega
          simpa [hsimp] using hnext
    have hresult : carryValue D d (J0 + 1 + k) := hmain k
    simpa [hjk] using hresult