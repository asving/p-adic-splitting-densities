/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.MovesC.C2_DOM_floorForm

/-!
# HC1.T10_floorStaircase — on factor-interior blocks the coordinate floor is the
block staircase

moves_ref: MOVES 3743–3745 (LST(ii)) + 3650–3651 (DOM: "the floor is the current
staircase: F_i(b) = old_i(slot(b))"). deps: T3, C4 (DOM_real), MovesC
`C2_DOM_floorForm` (proved). The first conjunct (`floorB b = (lines K).at
(blockEdge b)`) is DEFINITIONAL (rfl-level; the F3-3 repair by construction).
difficulty: medium. hyp: `TowerRealizable` (the realizability chain (SAE)/(NA)/(HV)
of the tower's moves — §5's open kernel, carried as `rl`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit T10: the staircase equation (rfl-level) + THE CONTENT: on factor-interior
blocks the pointwise history-floor max at every block coordinate equals the block
staircase value. -/
theorem T10_floorStaircase {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (rl : TowerRealizable T) (b : ℕ) (hb : rl.interiorB b) :
    rl.floorB b = (rl.line T.K).at (T.blockEdge b) ∧
    (∀ c : T.Coord, T.blk c = b → rl.floorC c = rl.floorB b) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.T10_floorStaircase
