/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.MovesC.C1_TYP_toClause

/-!
# HC1.C5_typToClause — the bridge to MovesC's counting

moves_ref: MOVES 3813–3815 (USE 1: "C.1.5's counting consumes exactly this
object"). deps: C3, T12; MovesC `LevelClause` (fence: consumed, not restated),
`C1_TYP_toClause` (proved). The base-coordinate chart `enc` (the block-convention
digit chart of the level set) is §C-side data, riding as an additive hypothesis.
difficulty: medium. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit C5: a TYP(b) fresh value clause yields a `MovesC.LevelClause` with support
the level set's chart, codim = aDim, and the count law from C3's equal-fiber
theorem. -/
theorem C5_typToClause {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (γ' : ℚ) (m : ℕ) (S : Finset (Fin m))
    (enc : (Fin m → ZMod p) →+ (↥(T.levelSet b γ') → ↥(T.stg 0).FQ))
    (hdep : ∀ x y : Fin m → ZMod p, (∀ c ∈ S, x c = y c) → enc x = enc y)
    (hsurj : Function.Surjective enc)
    (X : T.grQ γ') (hX : X ∈ T.alphabet b γ') :
    ∃ cl : MovesC.LevelClause p m,
      cl.support = S ∧ cl.codim = T.aDim b γ' ∧
      ∀ x : Fin m → ZMod p, cl.sat x ↔ T.typComposite b γ' (enc x) = X := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.C5_typToClause
