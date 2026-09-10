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


-- Prove by strong induction from J0+1 upward
set_option maxHeartbeats 200000
open Finset
namespace Erdos124.W3G4
/-- The carry family at level j: the doubling of the j-th window-base
    power is representable in the full tuple (closed theory §1). -/
def carryValue (D : Finset ℕ) (d j : ℕ) : Prop :=
  2 * d ^ j ∈ representableSet D 1
/-- The window anchor for tuple (3, 4, 13, 17, 49) (closed theory §0). -/
def anchor (D : Finset ℕ) : ℕ := 501
end Erdos124.W3G4
open Erdos124.W3G4
lemma carryValue_unbounded_T3_4_13_17_49 (D : Finset ℕ) (d e J0 : ℕ)
    (hdD : d ∈ D) (hD₃ : ∀ d ∈ D, 3 ≤ d) (he : 1 ≤ e) (heJ0 : e ≤ J0)
    (hanch : d ^ e ≥ anchor D)
    (hbase : ∀ j ∈ Set.Icc e J0, carryValue D d j)
    (hflip : ∀ j ≥ e, carryValue D d j → carryValue D d (j + 1)) :
    ∀ j ≥ e, carryValue D d j := by
  intro j hj
  by_cases hjJ0 : j ≤ J0
  · -- Case j ≤ J0: use hbase
    exact hbase j (by simp [Set.Icc, hj, hjJ0])
  · -- Case j > J0: use induction on j starting from J0+1
    have hJ0ge : J0 ≥ e := heJ0
    have hJ0carry : carryValue D d J0 := by
      exact hbase J0 (by simp [Set.Icc, heJ0])
    have hJ0p1carry : carryValue D d (J0 + 1) := by
      exact hflip J0 hJ0ge hJ0carry
    have hgt : J0 + 1 ≤ j := by
      omega
    have hmain : ∀ n ≥ J0 + 1, carryValue D d n := by
      intro n
      induction' n with n ih
      · intro hn
        omega -- n = 0 impossible since J0 + 1 ≥ 1
      · intro hn
        by_cases hn0 : n = J0
        · subst hn0
          exact hJ0p1carry
        · have hn_ge : n ≥ J0 + 1 := by
            have : n + 1 ≥ J0 + 1 := hn
            omega
          have hncarry : carryValue D d n := by
            exact ih (by omega)
          have hn_ge_e : n ≥ e := by
            have : J0 + 1 ≥ e + 1 := by omega
            omega
          exact hflip n hn_ge_e hncarry
    exact hmain j hgt