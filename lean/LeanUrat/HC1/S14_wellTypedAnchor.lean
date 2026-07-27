/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsSpine
import LeanUrat.Moves.L2_strideRule

/-!
# HC1.S14_wellTypedAnchor — the rev-D¹¹ F7 lemma: a ≥ 0 at e_read = 1 stages

moves_ref: MOVES 2636–2643 (WELL-TYPEDNESS LEMMA (a ≥ 0 here)). deps: S11; Moves
`L2_strideRule` (clean), Stage.he1t. sketch: he1t gives t = 0; hS5 positions 0; K1
slot positions = j ≥ 0. difficulty: medium. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit S14: at an e_read = 1 tower stage, every nonzero f has an anchored
residual with nonnegative anchor — `R(f)` is a z-POLYNOMIAL and `a = ord_z R(f)
≥ 0`. -/
theorem S14_wellTypedAnchor {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (k : Fin (T.K + 1)) (he1 : (T.stg k).e = 1)
    (f : Polynomial ℤ_[p]) (hf : f ≠ 0) :
    ∃ (a : ℤ) (Ranch : Polynomial ↥(T.stg k).K),
      HasAnchorK ((T.stg k).R f) a Ranch ∧ 0 ≤ a := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S14_wellTypedAnchor
