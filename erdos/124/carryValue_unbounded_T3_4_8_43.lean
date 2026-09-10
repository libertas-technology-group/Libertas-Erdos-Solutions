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


-- We prove by strong induction on j, but since we need to go upward from e,
-- we use well-founded induction on the distance from e, or equivalently
-- induction on j with a base at e and a step using hflip.
-- However, hbase only covers j ≤ J0.  For j > J0, we need to climb using hflip.
-- The key insight: the statement is trivial if j ≤ J0 by hbase.
-- For j > J0, we climb from J0 (or from e) using hflip repeatedly.
-- But hflip requires the previous value, so we need to ensure the chain stays valid.
-- We do this by induction on j, starting at e.
-- Since hflip gives the successor, we can use induction.
-- Use well-founded induction on the measure j - e
set_option maxHeartbeats 200000
open Finset
namespace Erdos124.W3G4
/-- The carry family at level j: the doubling of the j-th window-base
    power is representable in the full tuple (closed theory §1). -/
def carryValue (D : Finset ℕ) (d j : ℕ) : Prop :=
  2 * d ^ j ∈ representableSet D 1
/-- The window anchor for tuple (3, 4, 8, 43) (closed theory §0). -/
def anchor (D : Finset ℕ) : ℕ := 501
end Erdos124.W3G4
open Erdos124.W3G4
lemma carryValue_unbounded_T3_4_8_43 (D : Finset ℕ) (d e J0 : ℕ)
    (hdD : d ∈ D) (hD₃ : ∀ d ∈ D, 3 ≤ d) (he : 1 ≤ e) (heJ0 : e ≤ J0)
    (hanch : d ^ e ≥ anchor D)
    (hbase : ∀ j ∈ Set.Icc e J0, carryValue D d j)
    (hflip : ∀ j ≥ e, carryValue D d j → carryValue D d (j + 1)) :
    ∀ j ≥ e, carryValue D d j := by
  intro j hj
  have h_induct : ∀ j, e ≤ j → carryValue D d j := by
    intro j
    refine Nat.le_induction ?base ?step j
    · -- Base case: j = e
      have heIcc : e ∈ Set.Icc e J0 := by
        simp [Set.mem_Icc, he, heJ0]
      exact hbase e heIcc
    · -- Step: from j to j+1, given e ≤ j
      intro j hje hcarry
      exact hflip j hje hcarry
  exact h_induct j hj