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


-- We prove by strong induction on j, with the base case handled by hbase and the
-- step using hflip.  The key is that for j > J0, we can step down to j-1 which
-- is ≥ e, apply the induction hypothesis, and then use hflip.
-- Use well-founded induction on ℕ with the usual < relation.
-- Since j > J0 ≥ e, we have j ≥ 1 and j - 1 ≥ e
-- Apply induction hypothesis to j-1
-- Use hflip with j-1 (which is ≥ e)
-- Simplify (j - 1) + 1 = j
set_option maxHeartbeats 200000
open Finset
namespace Erdos124.W3G4
/-- The carry family at level j: the doubling of the j-th window-base
    power is representable in the full tuple (closed theory §1). -/
def carryValue (D : Finset ℕ) (d j : ℕ) : Prop :=
  2 * d ^ j ∈ representableSet D 1
/-- The window anchor for tuple (3, 5, 7, 31, 37, 46) (closed theory §0). -/
def anchor (D : Finset ℕ) : ℕ := 501
end Erdos124.W3G4
open Erdos124.W3G4
lemma carryValue_unbounded_T3_5_7_31_37_46 (D : Finset ℕ) (d e J0 : ℕ)
    (hdD : d ∈ D) (hD₃ : ∀ d ∈ D, 3 ≤ d) (he : 1 ≤ e) (heJ0 : e ≤ J0)
    (hanch : d ^ e ≥ anchor D)
    (hbase : ∀ j ∈ Set.Icc e J0, carryValue D d j)
    (hflip : ∀ j ≥ e, carryValue D d j → carryValue D d (j + 1)) :
    ∀ j ≥ e, carryValue D d j := by
  intro j hj
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases hJ : j ≤ J0
    · -- j is in the base range [e, J0]
      have hjIcc : j ∈ Set.Icc e J0 := by
        exact Set.mem_Icc.mpr ⟨hj, hJ⟩
      exact hbase j hjIcc
    · -- j > J0
      have hJlt : J0 < j := Nat.lt_of_not_ge hJ
      have hj_ge_one : 1 ≤ j := by
        omega
      have hj_minus_ge_e : e ≤ j - 1 := by
        omega
      have hprev : carryValue D d (j - 1) := by
        apply ih (j - 1)
        · omega  -- j - 1 < j
        · exact hj_minus_ge_e
      have hflip_jm1 : carryValue D d (j - 1) → carryValue D d ((j - 1) + 1) := by
        exact hflip (j - 1) hj_minus_ge_e
      have hstep := hflip_jm1 hprev
      simpa [Nat.sub_add_cancel hj_ge_one] using hstep