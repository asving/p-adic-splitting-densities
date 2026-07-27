/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsSpine
import LeanUrat.Moves.L4_TRANSvii_R4
import LeanUrat.Moves.L5_recVV_R4
import LeanUrat.Moves.L2_keyResidualPow

/-!
# HC1.S7_childPin — D.7(vi)–(vii): the transported vector, z′-pin, and S5′

moves_ref: MOVES 2392–2418 (D.7(vi)–(vii)). deps: S5, S6; Moves `L4_TRANSvii_R4`,
`L5_recVV_R4`, `L2_keyResidualPow` (clean). sketch: the vector transport is
`TransitionCoreL.child_Tvec`'s shape; D.3(b) re-runs verbatim (L2_keyResidualPow at
the child); the e′ = 1 / e′ ≥ 2 split is the canonical-Bézout window. difficulty:
medium. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit S7: for a transitioned child — the read's Bézout pair rides the child
stage per the e′ = 1 / e′ ≥ 2 split (P2 at e′ = 1), child digits of the lift space
are monomial units at the forced positions `−t′·(parent weight)` (S5′), and the
child's degree-0 z′-pin (CoeffLocLaw) holds. -/
theorem S7_childPin {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ σ' : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar)
    (tc : TransitionCoreL σ σ' Φhat e' h' zbar) :
    ((e' : ℤ) * σ'.s + (h' : ℤ) * σ'.t = 1 ∧ (e' = 1 → σ'.t = 0)) ∧
    (∀ B : Polynomial ℤ_[p], B ≠ 0 → inC Φhat B →
      ∃ c' : (↥σ'.K)ˣ, σ'.R B = LaurentPolynomial.C ((c' : ↥σ'.K)) *
        LaurentPolynomial.T (- σ'.t * σ.w B)) ∧
    CoeffLocLaw σ' := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S7_childPin
