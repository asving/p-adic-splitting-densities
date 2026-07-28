/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsChild
import LeanUrat.HC1.K1_vertexPin

/-!
# HC1.S9a_stageLiteral — the child Stage literal with its arithmetic/valuation legs

S9 DECOMPOSITION unit (blueprint §9.5): "the Stage literal + arithmetic/valuation
legs (data + he..he1t, hmonic/hdeg, hwΦ, hStretch, hK1, hreps, hTvec, hWS)" — the
`Stage` type itself carries those fields, so the unit statement is the ∃ of a
child Stage whose construction is RECORDED: `TransitionData` (the K/e/h/reps/
threshold/slot-min records), the K1 `VertexPin` (σ'.R agrees with the
D.7(vi)-normalized `childR` on C_Φ̂ — the F-frame recording of the residual tie;
the ↥K/↥K′ cast wall stays inside this unit's proof, per the blueprint's own
escalation surface), and the childW valuation tie. Consumes S9r's data (the
literal sets `w := childW`, `R := (cast of) childR`, `K := σ.nextField z̄`,
`reps := σ.reps ++ [σ.Φ]`, Tvec := the transported vector). SUPPLIED legs per the
§9.5 re-census: w-laws from S5/S4/S2/S3, hStretch definitional at j = 0 slots,
arithmetic from th + the (vii) Bézout split, hmonic/hdeg from `L3_liftMonic`.
difficulty: HARD (assembly; the known type wall). hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit S9a: the child Stage literal exists with its construction recorded —
transition data, the D.7(vi) vertex pin, and the childW valuation tie. -/
theorem S9a_stageLiteral {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) :
    ∃ σ' : Stage p F,
      TransitionData σ σ' Φhat e' h' zbar ∧
      VertexPin σ σ' Φhat zbar ∧
      (∀ f, f ≠ 0 → σ'.w f = childW σ Φhat e' h' f) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S9a_stageLiteral
