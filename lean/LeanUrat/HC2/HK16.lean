/-
Unit HK-16  (BRIDGE campaign, area BP2, cluster BP2-c2 — E-phase statement skeleton)
blueprint: lean/notes/BRIDGE_BP2_HC2K1_2026-07-30.md §4 Block G, unit HK-16.

INFORMAL STATEMENT (blueprint): "σ₁'s Stage laws via the guarded S9a/S9b/S9c chain at
the gate instance (e·g = 2 > 1 — the guards pass); consume HK-13/HK-56/HK-14 for the
StageCoreL inputs."  deps: HK-13, HK-56, HK-14 (jointly: `StageCoreL bStageP` —
enters as the hypothesis `hσ`), HK-15 (σ₁'s pinned construction — NOT
YET ON DISK, see the deviation below).

RATIFIED RE-KEY (2026-07-30): every occurrence of the blueprint's "bStage" is keyed at
`bStageP` (HK-13's base-pin re-dress), NOT the literal `U31.bStage` — `StageCoreL
U31.bStage` is REFUTABLE (`U31.bStage.reps = []` refutes `StageCore.reps_nonempty`/
`p_is_rep`; `wPrev = bw` with `bw X = 1` refutes `StageCore.prevIaug`: `1·1 < 1` is
false), so the hypothesis `hσ` would be undischargeable and the unit vacuous at the
literal. bStageP differs only in (wPrev := gaussVal, reps := [C 2], Tvec := [(C 2,1)]);
w/R/Φ/(e,h,s,t)/K are byte-identical, so the S9 chain's gate instantiation is unchanged.
Full finding record: `HK13_bStageCoreP1a.lean`'s module header (orchestrator-ratified).

E-PHASE RESOLUTION (recorded): HK-15's concrete σ₁ (pinned through `ChildResData` /
the S9c witness) is not on disk, so the unit is stated as the GATE INSTANTIATION OF
THE GUARDED S9 CHAIN — existentially, with EXACTLY the S9c conclusion conjunction
(`TransitionCoreL` + `VertexPin` + the childW tie + the stage core), the core upgraded
from `StageCore` to `StageCoreL` via S9d as in the proved `S9_transStage` (HC1). The
`TransHyp` input is HK-47's `transHyp_gate` (here the hypothesis `th`). When HK-15
lands, the P-phase re-binds the ∃-witness to HK-15's pinned σ₁ (definitional mismatch
⇒ HK-47 reports, per the blueprint's K-4 seam rule). The conjuncts of this ∃ are the
exact hypothesis pack HK-20's read-1 SideReads statements consume (σ₁.Φ = fq is
`.1.base.child_key`).

PROOF SKETCH (P-phase): `S9c_coreAssembly bStageP hσ th hEG` at hEG : 1 < 1·2 =
bStageP.e * g (the guard passes at the gate), then `S9d_stageCoreL` for the L-core
upgrade exactly as in `S9_transStage`'s proof (the hΦin degree argument via
`L3_liftMonic` at th.hlift). Difficulty hard-fable ~100, mostly instantiation
(blueprint).
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.HC2.U31_gateReadsOf
import LeanUrat.HC2.HK13_bStageCoreP1a
import LeanUrat.HC1.DefsTower
import LeanUrat.HC1.DefsSpine
import LeanUrat.HC1.K1_vertexPin
import LeanUrat.HC1.S9c_coreAssembly
import LeanUrat.HC1.S9d_pinVerify
import LeanUrat.Moves.L3_liftMonic

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.MovesJ

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD LeanUrat.HC1

namespace HK16

/-- HK-16: THE GATE CHILD STAGE'S LAWS — at the gate read (bStageP, ψ₂, g = 2,
Φ̂ = fq, next pair (1, 3), zbar₀ = the recorded root), the guarded S9 chain produces
a child stage carrying the full transition record, the D.8 vertex pin, the childW
tie, and the round-5 stage core (`StageCoreL`, via S9d). Hypotheses = the dep units:
`hσ` is HK-13/HK-56/HK-14's `StageCoreL bStageP`; `th` is HK-47's `transHyp_gate`.
The ∃-witness is HK-15's σ₁ (E-phase resolution: see the file header).
RATIFIED RE-KEY 2026-07-30: keyed at `bStageP`, not the refutable-core literal
`U31.bStage` (reps = [] / prevIaug refutations — HK-13's finding record). -/
theorem childStage_gate (hσ : StageCoreL bStageP)
    (th : TransHyp bStageP U31.ψ₂ 2 U31.fq 1 3 U31.ν₀.zbar) :
    ∃ σ₁ : Stage 2 F4,
      TransitionCoreL bStageP σ₁ U31.fq 1 3 U31.ν₀.zbar ∧
      VertexPin bStageP σ₁ U31.fq U31.ν₀.zbar ∧
      (∀ f, f ≠ 0 → σ₁.w f = childW bStageP U31.fq 1 3 f) ∧
      StageCoreL σ₁ := by
  have hEG : 1 < bStageP.e * 2 := by
    rw [bStageP_e_def]
    norm_num
  obtain ⟨σ₁, tc, pin, htie, hcore⟩ := S9c_coreAssembly bStageP hσ th hEG
  obtain ⟨hmonΦ, hdegΦ⟩ := L3_liftMonic bStageP U31.ψ₂ 2 th.hg U31.fq th.hlift
  have hΦnatlt : bStageP.Φ.natDegree < U31.fq.natDegree := by
    rw [hdegΦ]
    exact lt_mul_of_one_lt_left bStageP.hdeg hEG
  have hΦin : inC U31.fq bStageP.Φ := by
    change bStageP.Φ.degree < U31.fq.degree
    rw [Polynomial.degree_eq_natDegree bStageP.hmonic.ne_zero,
      Polynomial.degree_eq_natDegree hmonΦ.ne_zero]
    exact_mod_cast hΦnatlt
  exact ⟨σ₁, tc, pin, htie, S9d_stageCoreL bStageP σ₁ hσ th tc pin hΦin hcore⟩

/-- The gate guard check, standalone (the blueprint's "e·g = 2 > 1 — the guards
pass"): the S9a/S9b/S9c/S9 increment guard is satisfied at the gate read
(`bStageP.e = U31.bStage.e = 1` — the e field is untouched by the re-dress). -/
theorem gate_guard : 1 < bStageP.e * 2 := by
  rw [bStageP_e_def]
  norm_num

end HK16

end LeanUrat.MovesJ
