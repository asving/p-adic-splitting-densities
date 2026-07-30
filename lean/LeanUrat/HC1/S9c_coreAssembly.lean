/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsChild
import LeanUrat.HC1.K1_vertexPin
import LeanUrat.HC1.S2_childW
import LeanUrat.HC1.S3_childK1
import LeanUrat.HC1.S5_childValuation
import LeanUrat.HC1.S9_builder
import LeanUrat.HC1.S9a_stageLiteral
import LeanUrat.HC1.S9w_residualLaws
import LeanUrat.HC1.S11a_coreTransport
import LeanUrat.HC1.V7_stripDischarge
import LeanUrat.Moves.L2_slotDecomp_R4
import LeanUrat.Moves.L3_liftMonic
import LeanUrat.Moves.L4_TRANSii
import LeanUrat.Moves.L4_TRANSviii_b_R4

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
facts are w_jump (the `ChildResLaws` w_jump conjunct, via S9w's lawful carrier —
re-threaded at the 2026-07-28 unbundle; formerly a `ChildResData` field), TvecLaw
(the transported-vector product law of the literal), SlotDecomp and
CoeffFieldLawCore (transports via `L4_TRANSvii_R4` + S6, per §9.5)).

**RESTATED (2026-07-28, mechanical-closer round — the S9a adjudication + the S9b
precedent applied verbatim): the increment guard `e·g > 1`.** The unguarded
statement is refuted at the `σ.e * g = 1` corner by EXACTLY S9a's kernel
argument: S9c's ∃ CONTAINS the refuted S9a shape (its `TransitionCoreL.base` is
the `TransitionData` whose `child_reps` puts the outgoing key `σ.Φ` on the child
list, `hreps` forces it into `C_Φ̂`, and at `e·g = 1` the degrees collide) —
`S9c_ungated_corner_refuted` below, the in-file machine-checked kernel,
delegating to `S9a_ungated_corner_refuted`. ADJUDICATION (S9a's, verbatim): the
note's LST tower-induction step carries the guard EXPLICITLY — MOVES 3755–3757:
"STEP at an INCREMENT ν_{i+1} (stage data (e_{i+1}, h_{i+1}), **e·g > 1**)" — and
the `e·g = 1` corner is the note's OTHER species, MOVES 3766–3767 (RECENTERING,
`Φ̂ ↦ Φ̂ + t`), handled by the PROVED S10_recStage, not by S9. The statement gains
the hypothesis `hEG : 1 < σ.e * g`; the refutation corner fails the guard by
`S9a_corner_fails_guard` (proved in S9a's file, statement-independent
arithmetic).

**PROVED (same round): the guarded assembly.** The S9a/S9b literal re-runs
verbatim (Bézout split, the S9w lawful carrier, the S2/S3/S5 childW plumbing,
the in-file hwult, hS6b′ + the coset hS6a′ via `L4_TRANSviii_b` + the V7 strip
discharge), then the S9c-specific conjuncts close from the census suppliers:
* `TransitionCoreL`: `TransitionData` = the construction records (all rfl on the
  literal); `child_Tvec` = rfl (the literal's Tvec IS the transported vector);
  `child_dig_frame` = the carrier's S5′ pin through
  `VertexPin.to_child_dig_frame` (`mfun := 0`, no ∃-slack).
* `VertexPin` + the childW tie: the carrier's own hS5′ pin / rfl (as S9a).
* `StageCore`: the seven non-twist legs from `S11a_coreTransport` (consumed as
  planned); w_jump = the `ChildResLaws` conjunct of S9w's lawful carrier;
  TvecLaw via the NEW in-file bridge `tvecLaw_of_tvecUnitLaw` from
  `K1_tvecUnitLaw_of_pin` (the pin kills the twist class; the two-evaluation
  shadow follows from the unit law by the bare Stage laws — this supplier
  SUPERSEDES the §9.5 "by construction" route, no new law needed); SlotDecomp
  via the clean Moves `L2_slotDecomp` (w_strict/w_jump/R_neg are exactly its
  inputs); CoeffFieldLawCore via the NEW in-file `coeffCore_of_stage` — all
  three (S4)-core clauses are derivable for EVERY stage from the bare fields +
  wPrev_mul (clause 1 from hS6b at one weight above the threshold; clause 2
  from hS5-monomiality + the hStretch product law; clause 3's exponent group
  hits −1 = −(e·s + h·t) on the pair (B₁, B₂·Φ^e) of hS6b realizers at parent
  weights ν₀ + h and ν₀ — the §9.5 "L4_TRANSvii_R4 + S6" plan is superseded by
  this leaner generic route, no new law needed).
difficulty: HARD (assembly). hyp: hEG (the adjudicated note guard).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ## The corner kernel (the shape the restated guard excludes) -/

/-- **The refutation kernel, machine-checked** (the S9a kernel transported): at
`σ.e * g = 1` — the recentering species, `deg Φ̂ = deg σ.Φ` — NO child stage can
carry the S9c record, since `TransitionCoreL.base` contains the (refuted) S9a
record. -/
theorem S9c_ungated_corner_refuted (σ : Stage p F) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) (hcorner : σ.e * g = 1) :
    ¬ ∃ σ' : Stage p F,
        TransitionCoreL σ σ' Φhat e' h' zbar ∧
        VertexPin σ σ' Φhat zbar ∧
        (∀ f, f ≠ 0 → σ'.w f = childW σ Φhat e' h' f) ∧
        StageCore σ' := by
  rintro ⟨σ', tc, pin, hw, -⟩
  exact S9a_ungated_corner_refuted σ th hcorner ⟨σ', tc.base, pin, hw⟩

/-! ## The unit -/

/-- Unit S9c (RESTATED 2026-07-28 with the adjudicated note guard `e·g > 1`,
MOVES 3755–3757, per the S9a/S9b precedent — see the header): at every INCREMENT
read (`1 < σ.e * g`), the constructed child carries the full transition record,
the pin, the childW tie, and `StageCore`. -/
theorem S9c_coreAssembly (σ : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) (hEG : 1 < σ.e * g) :
    ∃ σ' : Stage p F,
      TransitionCoreL σ σ' Φhat e' h' zbar ∧
      VertexPin σ σ' Φhat zbar ∧
      (∀ f, f ≠ 0 → σ'.w f = childW σ Φhat e' h' f) ∧
      StageCore σ' := by
  -- C4 HOIST (2026-07-30, SYNTHESIS_PASS1 C4b; golf HC1#96): the former in-file
  -- construction AND the private bare-Stage/grRes/coeff-core helper block now live
  -- ONCE in `LeanUrat.HC1.S9_builder` (verbatim hoist of THIS file's body — the
  -- single delta is the builder's inserted `rfl` for its weightSet conjunct; see
  -- that file's per-conjunct record); this main is its projection (conjuncts
  -- 1-3 + 5). Statement byte-identical to the pre-hoist form.
  obtain ⟨σ', tc, pin, htie, -, hcore⟩ := S9_builder σ hσ th hEG
  exact ⟨σ', tc, pin, htie, hcore⟩
end LeanUrat.HC1

#print axioms LeanUrat.HC1.S9c_coreAssembly
#print axioms LeanUrat.HC1.S9c_ungated_corner_refuted
