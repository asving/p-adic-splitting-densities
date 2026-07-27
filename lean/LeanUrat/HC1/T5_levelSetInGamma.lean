/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar

/-!
# HC1.T5_levelSetInγ — LST(i-c): in_γ is a function of exactly the level set

moves_ref: MOVES 3739–3742 "the weight-γ initial form in_γ(B) is a function of
exactly the LEVEL SET L_γ(B)". deps: T4, T6. difficulty: medium. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit T5: two assignments agreeing on the level set, with all block-b digits of
height below γ zero, have equal weight-γ initial forms. -/
theorem T5_levelSetInGamma {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (γ : ℚ) (x y : T.Coord → ↥(T.stg 0).FQ)
    (hxfin : (Function.support x).Finite) (hyfin : (Function.support y).Finite)
    (hagree : ∀ c ∈ T.levelSet b γ, x c = y c)
    (hxlow : ∀ c, T.blk c = b → T.ht c < γ → x c = 0)
    (hylow : ∀ c, T.blk c = b → T.ht c < γ → y c = 0) :
    T.inGr γ (T.slotCoeff b x) = T.inGr γ (T.slotCoeff b y) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.T5_levelSetInGamma
