/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC2.U31_gateReadsOf
import LeanUrat.Moves.L1_gaussVal

/-!
# HC2.HK13_bStageCoreP1a — HK-13: `StageCoreL` at the gate base stage, part 1a

Bridge campaign BP2 (`lean/notes/BRIDGE_BP2_HC2K1_2026-07-30.md`, Block G, unit HK-13).
E-PHASE SKELETON: carrier definition + statements with `sorry` bodies; P-phase proves
(hard-fable, est. ~90 lines; "the U31 600-line build is the precedent and supplies the
carrier lemmas").

**Unit HK-13** — blueprint statement: "`StageCoreL bStage` part 1a — wPrev valuation laws
(v_p facts), genuine reps ([p]), tie laws, prevIaug at the diagonal (1,1) Gauss stage
over F4."  (SlotDecomp + CoeffFieldLawCore split to HK-56; TvecUnitLaw + CoeffLocLaw to
HK-14.)

## ⚠ TRANSCRIPTION FINDING + RESOLUTION (E-phase, 2026-07-30 — SURFACED TO THE
## ORCHESTRATOR; read before consuming)

`StageCoreL` at the LITERAL `U31.bStage` is REFUTABLE — the blueprint's target statement
cannot be hosted there:
* `U31.bStage.reps = []` (U31_gateReadsOf.lean l.662) refutes `StageCore.reps_nonempty`
  and `StageCore.p_is_rep` outright;
* `U31.bStage.wPrev = bw` with `bw X = 1` (the stage's own `hwΦ` scale) refutes
  `StageCore.prevIaug`: `1·bw X = 1 < 1` is false.
The blueprint's own clause "genuine reps ([p])" and the D.2 base pin (`HC1.IsBaseStage`,
DefsTower: "parent valuation = the Gauss valuation, reps = [C p]") prescribe the repair.
Since `U31_gateReadsOf.lean` is an existing file (frozen for this campaign — no edits),
the unit is stated at the BASE-PIN RE-DRESS `bStageP` defined below: byte-identical to
`U31.bStage` in every field EXCEPT `wPrev := gaussVal` (the Gauss valuation, DEF-4's
base-case prescription), `reps := [C 2]`, `Tvec := [(C 2, 1)]` (exponent 1: `grRes (C 2)
= T 1 = locT`, matching `TvecLaw`/`TvecUnitLaw` at `t = 0`).  Every recorded U31 gate
fact survives: `w`/`R` ARE `bw`/`bR` unchanged, `gaussVal` agrees with `bw` on the
coefficient carrier `C_X` (constants), and `wPrev` enters the recorded U31 data only
through (S5) positions scaled by `σ.t = 0`.  CROSS-CLUSTER CONSEQUENCE (surfaced, not
decided here): every Block-G unit keyed to "bStage" (HK-15/16/17/18/21/47, the gate node
ν₀ whose `σ` field is the literal `U31.bStage`, …) must re-key to `bStageP` — ν₀ by the
mechanical re-dress `{ν₀ with σ := bStageP}` — pending the orchestrator's ratification.
NOTE: the refutation of `StageCoreL U31.bStage` is deliberately NOT compiled here (the
cross-area rule: no compiled negation witness while sibling clusters may hold sorried
universals at the old carrier); this docstring + the campaign report are the record.

## Contents (statement shapes = `StageCore`'s field types at `σ := bStageP`, so HK-16's
## assembly is a constructor application)

`bStageP` (the carrier), then part 1a: `bStageP_wPrev_mul`, `bStageP_wPrev_ult` (the
parent valuation IS a valuation — v_2 facts of `gaussVal`), `bStageP_reps_nonempty`,
`bStageP_p_is_rep` (genuine reps), `bStageP_w_strict`, `bStageP_w_jump`, `bStageP_R_neg`
(the three D.1(b) tie laws at `bw`/`bR`), `bStageP_prevIaug` ((I-aug) at the base read:
`1·gaussVal X = 0 < 1`).

deps: — (Block-G root unit).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

namespace LeanUrat.MovesJ

open Polynomial LeanUrat.Moves

/-- **HK-13 carrier: `bStageP`** — the BASE-PIN RE-DRESS of `U31.bStage` (the (1,1)-diagonal
Gauss stage at `Φ = X` over `K₂ ≅ 𝔽₂` inside F4): `wPrev := gaussVal` (the Gauss
valuation — the D.2/`IsBaseStage` base pin; `U31.bStage`'s `wPrev := bw` junk-choice off
the coefficient carrier refutes `prevIaug`), `reps := [C 2]`, `Tvec := [(C 2, 1)]`
(genuine representatives — `U31.bStage.reps = []` refutes `reps_nonempty`/`p_is_rep`);
every other field byte-identical to `U31.bStage` (`w = bw`, `R = bR`, `Φ = X`,
`(e,h,s,t) = (1,1,1,0)`, `K = FQ = K₂`, `weightSet = Set.Ici 0`).  The seven
`wPrev`/`reps`/`Tvec`-typed Stage law fields are re-supplied (`sorry` = this unit's
P-phase duty; `hTvec` is definitional).  See the module header for the full finding
record and the cross-cluster re-key consequence.
[Blueprint BP2 HK-13; deps: —.] -/
noncomputable def bStageP : Stage 2 F4 :=
  { U31.bStage with
    wPrev := gaussVal
    reps := [Polynomial.C ((2 : ℕ) : ℤ_[2])]
    Tvec := [(Polynomial.C ((2 : ℕ) : ℤ_[2]), (1 : ℤ))]
    hreps := by sorry
    hTvec := rfl
    hStretch := by sorry
    hS5 := by sorry
    hS6a := by sorry
    hS6b := by sorry
    hWS := by sorry }

/-- HK-13 (part 1a, `StageCore.wPrev_mul` shape): the parent valuation `gaussVal` is
multiplicative on nonzero polynomials — the v_2 content-exponent product law (Gauss's
lemma over the DVR `ℤ_[2]`).  [Blueprint BP2 HK-13; deps: —; supply: `L1_gaussVal`'s
Gauss-valuation toolkit.] -/
theorem bStageP_wPrev_mul :
    ∀ f g : Polynomial ℤ_[2], f ≠ 0 → g ≠ 0 →
      bStageP.wPrev (f * g) = bStageP.wPrev f + bStageP.wPrev g := by
  sorry

/-- HK-13 (part 1a, `StageCore.wPrev_ult` shape): the parent valuation `gaussVal` is
ultrametric — `min (v f) (v g) ≤ v (f + g)` on nonzero sums (coefficientwise v_2
minimum).  [Blueprint BP2 HK-13; deps: —.] -/
theorem bStageP_wPrev_ult :
    ∀ f g : Polynomial ℤ_[2], f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      min (bStageP.wPrev f) (bStageP.wPrev g) ≤ bStageP.wPrev (f + g) := by
  sorry

/-- HK-13 (part 1a, `StageCore.reps_nonempty` shape): the representative list is genuine —
nonempty.  Definitional at the re-dress (`bStageP.reps = [C 2]`).  [Blueprint BP2 HK-13.] -/
theorem bStageP_reps_nonempty : bStageP.reps ≠ [] := by
  sorry

/-- HK-13 (part 1a, `StageCore.p_is_rep` shape): `[p]` — the representative list contains
`C p` at `p = 2` (cast-shape matched to `StageCore`'s field type `Polynomial.C (↑p)`).
Definitional at the re-dress.  [Blueprint BP2 HK-13.] -/
theorem bStageP_p_is_rep : (Polynomial.C ((2 : ℕ) : ℤ_[2])) ∈ bStageP.reps := by
  sorry

/-- HK-13 (part 1a, `StageCore.w_strict` shape — D.1(b) tie law 1): strict-triangle
equality for the stage weight `bw`.  [Blueprint BP2 HK-13; supply: U31's `bw_ult`/NF
normal-form machinery (the 600-line-build precedent).] -/
theorem bStageP_w_strict :
    ∀ f g : Polynomial ℤ_[2], f ≠ 0 → g ≠ 0 →
      bStageP.w f < bStageP.w g → bStageP.w (f + g) = bStageP.w f := by
  sorry

/-- HK-13 (part 1a, `StageCore.w_jump` shape — D.1(b) tie law 2): residual cancellation at
a weight jump — equal weights, strictly larger sum weight ⇒ `R f + R g = 0` at `bR`.
[Blueprint BP2 HK-13; supply: U31's `bR_add`/NF machinery.] -/
theorem bStageP_w_jump :
    ∀ f g : Polynomial ℤ_[2], f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      bStageP.w f = bStageP.w g → bStageP.w f < bStageP.w (f + g) →
      bStageP.R f + bStageP.R g = 0 := by
  sorry

/-- HK-13 (part 1a, `StageCore.R_neg` shape — D.1(b) tie law 3): `R (−f) = −R f` at `bR`
(mod-2 reduction of the θ-cofactor; note at characteristic 2 the two sides coincide with
`R f` — still the law's shape).  [Blueprint BP2 HK-13.] -/
theorem bStageP_R_neg :
    ∀ f : Polynomial ℤ_[2], bStageP.R (-f) = - bStageP.R f := by
  sorry

/-- HK-13 (part 1a, `StageCore.prevIaug` shape): (I-aug) at the read that created the base
stage — `e·wPrev Φ < h`, i.e. `1·gaussVal X = 0 < 1`.  (At the OLD `wPrev := bw` this was
REFUTED — `bw X = 1`; the re-dress restores the base case of the StageCore docstring:
"base: `wPrev(φ) = v(φ) = 0 < h`".)  [Blueprint BP2 HK-13.] -/
theorem bStageP_prevIaug :
    (bStageP.e : ℤ) * bStageP.wPrev bStageP.Φ < (bStageP.h : ℤ) := by
  sorry

end LeanUrat.MovesJ
