/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsChild
import LeanUrat.HC1.K1_vertexPin
import LeanUrat.HC1.S11a_coreTransport
import LeanUrat.Moves.L4_TRANSvii_R4

/-!
# HC1.S9c_coreAssembly — StageCore of the constructed child + the TransitionCoreL
records

S9 DECOMPOSITION unit (blueprint §9.5): "S9c: StageCore assembly + TransitionCoreL
records (TransitionData rfl fields, child_Tvec, pinned child_dig_frame) +
SlotDecomp/CoeffFieldLawCore." Cumulative over S9a/S9b: the literal carries the
FULL round-5 transition record (`TransitionCoreL` — its `child_dig_frame` is the
pin's own clause via `VertexPin.to_child_dig_frame`, with `mfun := 0`, no
∃-slack) and `StageCore` (the seven non-twist legs are `S11a_coreTransport`'s
transport — consumed here to shrink the per-field work; the residual construction
facts are w_jump (`ChildResData.hWjump`), TvecLaw (the transported-vector product
law of the literal), SlotDecomp and CoeffFieldLawCore (transports via
`L4_TRANSvii_R4` + S6, per §9.5)). difficulty: HARD (assembly). hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit S9c: the constructed child carries the full transition record, the pin,
the childW tie, and `StageCore`. -/
theorem S9c_coreAssembly {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) :
    ∃ σ' : Stage p F,
      TransitionCoreL σ σ' Φhat e' h' zbar ∧
      VertexPin σ σ' Φhat zbar ∧
      (∀ f, f ≠ 0 → σ'.w f = childW σ Φhat e' h' f) ∧
      StageCore σ' := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S9c_coreAssembly
