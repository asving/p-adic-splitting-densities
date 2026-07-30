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
import LeanUrat.HC1.V7_stripDischarge
import LeanUrat.Moves.L3_liftMonic
import LeanUrat.Moves.L4_TRANSii
import LeanUrat.Moves.L4_TRANSviii_b_R4

/-!
# HC1.S9b_childWeightSet — the (S6′) legs: weightSet := 𝒜′, cumulative over S9a

S9 DECOMPOSITION unit (blueprint §9.5): "S9b: weightSet := 𝒜′ + hS6a/hS6b via the
TRANSviii finals." The `hS6a`/`hS6b` realizer laws are `Stage` fields of the
literal; this unit's statement content is that the literal can be built with its
`weightSet` PINNED to 𝒜′ (`childWeightSet` — the parent-scale coefficient weight
set, read against `σ'.wPrev = σ.w`), cumulatively over S9a's conjuncts.

**RESTATED (2026-07-28, mechanical-closer round — the S9a precedent + adjudication
applied verbatim): the increment guard `e·g > 1`.** The unguarded statement is
refuted at the `σ.e * g = 1` corner by EXACTLY S9a's kernel argument: S9b's ∃ is
S9a's ∃ strengthened by the `weightSet` conjunct, so any witness for it witnesses
the refuted S9a shape — `TransitionData.child_reps` puts the outgoing key `σ.Φ`
on the child list, `hreps` forces it into `C_Φ̂`, and at `e·g = 1` the degrees
collide (`S9b_ungated_corner_refuted` below, the in-file machine-checked kernel,
delegating to `S9a_ungated_corner_refuted`). ADJUDICATION (S9a's, verbatim): the
note's LST tower-induction step carries the guard EXPLICITLY — MOVES 3755–3757:
"STEP at an INCREMENT ν_{i+1} (stage data (e_{i+1}, h_{i+1}), **e·g > 1**)" — and
the `e·g = 1` corner is the note's OTHER species, MOVES 3766–3767 (RECENTERING,
`Φ̂ ↦ Φ̂ + t`), handled by the PROVED S10_recStage, not by S9. The statement gains
the hypothesis `hEG : 1 < σ.e * g`; the refutation corner fails the guard by
`S9a_corner_fails_guard` (proved in S9a's file; the arithmetic is
statement-independent, so it is cited as-is rather than duplicated).

**PROVED (same round): the guarded literal.** The S9a_final construction re-runs
verbatim — Bézout split, the S9w lawful carrier, the S2/S3/S5 childW plumbing,
the in-file hwult (slotwise development addition), hS6b′ + the above-threshold
half of hS6a′ via `L4_TRANSviii_b` + the carrier pin, and the BELOW-THRESHOLD
strip via `V7_stripDischarge` (σ′-free; the blueprint's original "TRANSviii_a
conjunct 2 verbatim" route was found CIRCULAR at S9a_final — TRANSviii_a consumes
a full child Stage — so this file's (S6a′)/(S6b′) come through the S9a route,
superseding the E-phase header's "via the TRANSviii finals" plan). The assembled
literal already pins `weightSet := childWeightSet σ Φ̂` (S9a's own `hWS` field
reads against it), so the new fourth conjunct closes by `rfl`.
difficulty: HARD (assembly). hyp: hEG (the adjudicated note guard).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- **The refutation kernel, machine-checked** (the corner the restated guard
excludes; the S9a kernel transported): at `σ.e * g = 1` — the recentering
species, `deg Φ̂ = deg σ.Φ` — NO child stage can carry the S9b record, since the
S9b record contains the (refuted) S9a record: `TransitionData.child_reps` puts
the outgoing key on the child list, `hreps` forces it into `C_Φ̂`, and the
degrees collide. -/
theorem S9b_ungated_corner_refuted {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) (hcorner : σ.e * g = 1) :
    ¬ ∃ σ' : Stage p F,
        TransitionData σ σ' Φhat e' h' zbar ∧
        VertexPin σ σ' Φhat zbar ∧
        (∀ f, f ≠ 0 → σ'.w f = childW σ Φhat e' h' f) ∧
        σ'.weightSet = childWeightSet σ Φhat := by
  rintro ⟨σ', td, pin, hw, -⟩
  exact S9a_ungated_corner_refuted σ th hcorner ⟨σ', td, pin, hw⟩

/-- Unit S9b (RESTATED 2026-07-28 with the adjudicated note guard `e·g > 1`,
MOVES 3755–3757, per the S9a precedent — see the header): at every INCREMENT
read (`1 < σ.e * g`), the S9a literal can be assembled with its `weightSet`
pinned to the child parent-scale coefficient weight set 𝒜′. -/
theorem S9b_childWeightSet {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) (hEG : 1 < σ.e * g) :
    ∃ σ' : Stage p F,
      TransitionData σ σ' Φhat e' h' zbar ∧
      VertexPin σ σ' Φhat zbar ∧
      (∀ f, f ≠ 0 → σ'.w f = childW σ Φhat e' h' f) ∧
      σ'.weightSet = childWeightSet σ Φhat := by
  -- C4 HOIST (2026-07-30, SYNTHESIS_PASS1 C4b; golf HC1#96): the former in-file
  -- re-run of the S9a construction now lives ONCE in `LeanUrat.HC1.S9_builder`
  -- (verbatim body hoist — see that file's per-conjunct record); this main is its
  -- projection (conjuncts 1-4). Statement byte-identical to the pre-hoist form.
  obtain ⟨σ', tc, pin, htie, hws, -⟩ := S9_builder σ hσ th hEG
  exact ⟨σ', tc.base, pin, htie, hws⟩
end LeanUrat.HC1

#print axioms LeanUrat.HC1.S9b_childWeightSet
#print axioms LeanUrat.HC1.S9b_ungated_corner_refuted
