/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.K1_vertexPin
import LeanUrat.HC1.S7_childPin

/-!
# HC1.S9d_pinVerify — the pin-verification unit: the twist-class legs from the
K1 vertex pin (closes the §9.3/§9.4 seam)

S9 DECOMPOSITION unit (blueprint §9.5): "S9d: TvecUnitLaw σ′ + CoeffLocLaw σ′
(transplant scratch (a)/(b); (c) + the product law by construction) → closes
StageCoreL σ′ and DISCHARGES the §9.3/§9.4 seam."

CONSUMES K1 (`K1_vertexPin`, the kernel round 38d2903): with the D.7(vi)
normalization RECORDED as `VertexPin` (realized by construction on S9c's child —
`child_dig_frame` with `mfun ≡ 0`), the two twist-class bridges close the exact
legs the S8 twist symmetry and the S7 scratch's (⋆) proved underivable from the
un-pinned records:
* `TvecUnitLaw σ'` — `K1_tvecUnitLaw_of_pin` (S8's homed conjunct, F-4);
* `CoeffLocLaw σ'` leg (c) — `K1_coeffLocC_of_pin` (S7's homed leg, F-3), with
  legs (a)/(b) from the restated `S7_childPin` (the transplanted scratch legs).
Both theorems here are PROVED (zero sorry; Lean-core footprints expected):
`S9d_pinVerify` = the pair, `S9d_stageCoreL` = the StageCoreL close given S9c's
`StageCore`. The pin's non-vacuity obligation sits with S9c's construction (K1's
faithfulness flag). difficulty: closed. hyp: `hΦin : inC Φhat σ.Φ` (K1's own
drafted interface — the outgoing key is a child coefficient; strict at every
degree-growing read).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit S9d (the seam discharge): with the D.7(vi) pin recorded, the constructed
child's twist-class legs close — the T-vector product law and the full
coefficient-localization law. -/
theorem S9d_pinVerify {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ σ' : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar)
    (tc : TransitionCoreL σ σ' Φhat e' h' zbar)
    (pin : VertexPin σ σ' Φhat zbar) (hΦin : inC Φhat σ.Φ) :
    TvecUnitLaw σ' ∧ CoeffLocLaw σ' :=
  ⟨K1_tvecUnitLaw_of_pin σ σ' hσ tc pin hΦin,
   (S7_childPin σ σ' hσ th tc).2.2.1,
   (S7_childPin σ σ' hσ th tc).2.2.2,
   K1_coeffLocC_of_pin σ σ' hσ tc pin hΦin⟩

/-- The StageCoreL close: S9c's `StageCore` + the pin-verified twist-class legs
assemble the round-5 core of the constructed child — `S9 = ⟨literal, S9c,
S9a–S9d⟩` (blueprint §9.5). -/
theorem S9d_stageCoreL {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ σ' : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar)
    (tc : TransitionCoreL σ σ' Φhat e' h' zbar)
    (pin : VertexPin σ σ' Φhat zbar) (hΦin : inC Φhat σ.Φ)
    (hcore : StageCore σ') : StageCoreL σ' :=
  ⟨hcore, (S9d_pinVerify σ σ' hσ th tc pin hΦin).1,
   (S9d_pinVerify σ σ' hσ th tc pin hΦin).2⟩

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S9d_pinVerify
#print axioms LeanUrat.HC1.S9d_stageCoreL
