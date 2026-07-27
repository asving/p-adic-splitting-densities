/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.Moves.L0_FactB_unique

/-!
# HC1.T9_blockDisjoint — (ii.3), TWO legs (audit G-5)

moves_ref: MOVES 2175–2188 ("distinct development slots have disjoint leaf subtrees
(the development is a coordinate partition) … the two forced slot classes t_k·γ*,
t_k·γ′* differ (t_k invertible mod e_k) … induction bottoms at distinct p-adic
heights — disjoint addresses"). deps: DefsCar, T12; Moves `L0_FactB_unique` (clean —
development uniqueness = the partition). Leg (a) is the ledger-facing locus
disjointness; leg (b) is THE CONTENT (audit G-5): the mixed-radix leaf-address
injectivity — "no two equations of one system pin the same digit coordinate", the
injectivity S17's `L6_ledgerCount` consumption rests on. difficulty: medium.
hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit T9: (a) distinct (block, height) pins constrain disjoint loci;
(b) the mixed-radix address map `c ↦ (Σ_r slot_r·deg Φ_r, l)` is injective on
coordinates (the slot vector is the mixed-radix representation of the base index
in the degree-ratio radices — slot_lt = exactly the digit bounds). -/
theorem T9_blockDisjoint {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) :
    (∀ (b b' : ℕ) (γ γ' : ℚ), (b, γ) ≠ (b', γ') →
      Disjoint (T.levelSet b γ) (T.levelSet b' γ')) ∧
    Function.Injective (fun c : T.Coord => (T.baseIdx c, c.l)) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.T9_blockDisjoint
