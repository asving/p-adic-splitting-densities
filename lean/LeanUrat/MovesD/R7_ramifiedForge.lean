/-
Unit FORGE-A  (R7 completion round, 2026-07-31)
[The R7 countermodel COMPLETED UNCONDITIONALLY: one compiled RAMIFIED `Stage` instance
(e = 2) empties `OffsetPPin pol` for EVERY policy — the conditional leg of
`MovesD/R7_pinProbe.lean` (`offsetPPin_isEmpty_of_ramified`) discharged.  The R7 record
(`lean/notes/R7_PINPROBE_RECORD_2026-07-31.md`) priced the missing instance as "a
bStage-scale construction (~600 lines)"; the finding of this unit is that NO hand-build
is needed — the corpus's OWN proved D.7 child-stage constructor (`HC1.S9_transStage`)
forges it when fed a RAMIFIED side.]

## What is built (0 sorry; axiom footprints printed at EOF — Lean core only)

1. `bStageP_stageCore` / `bStageP_stageCoreL` — the FIRST ASSEMBLY of
   `StageCoreL bStageP` from the proved HK-13/HK-56/HK-14 pieces (blueprint BP2 Block G
   split the core into exactly these units; HK-16's `childStage_gate` carries it as the
   hypothesis `hσ` — now dischargeable).  Reusable wave-D groundwork.
2. `transHyp_ramified : TransHyp bStageP ψ₂ 2 fq 2 5 ν₀.zbar` — the RAMIFIED read
   interface at the SAME gate read as HK-47's `transHyp_gate` (same ψ₂ = z² + z + 1,
   g = 2, Φ̂ = fq = X² + 2X + 4, same recorded residue root z̄ = ν₀.zbar), with the side
   re-keyed (e′,h′) = (1,3) → (2,5).  PARAMETER CHOICES: e′ = 2 is the ramification
   target; h′ = 5 is the least h′ with gcd(2, h′) = 1 and (I-aug) h′ > e′·w(Φ̂) = 2·2 = 4
   (w(Φ̂) = bw fq = 2 — the recorded normal form `HK13R.NF_θ_fq`, the same concrete
   steepness fact HK-47 uses).  Only the four side-keyed fields (he′/hh′/hcop/hiaug) are
   new; the read-shaped fields (hmonic/hirr/hne_z/hdeg/hg/hlift/hroot) are HK-47's,
   reused verbatim — they do not mention (e′, h′).
3. `ramifiedStage : Stage 2 F4` with `ramifiedStage_e : ramifiedStage.e = 2` — the
   forged RAMIFIED stage: the S9 child of `bStageP` under the (2,5) read
   (`S9_transStage bStageP bStageP_stageCoreL transHyp_ramified hEG`, hEG : 1 < e·g = 2).
   This realizes the R7 record's intended semantics — "every `e ≥ 2` increment read
   creates a ramified child stage (the `X² − p` Eisenstein side is the standard example;
   `TransitionCoreL` ties the child stage's index to the read's)" — as a compiled term:
   the (2,5) side through the lift fq is the slope-5/2 (totally ramified, index-2) read
   over the p = 2 base pin.  The child carries `StageCoreL` + the full `TransitionCoreL`
   record (`ramifiedStage_spec`), so it is directly reusable for the wave-D instance
   construction (deeper reads at a genuinely ramified frame).
4. `offsetPPin_isEmpty_unconditional : ∀ pol : CanonPolicy 2 F4, IsEmpty (OffsetPPinBare pol)`
   — **THE R7 COUNTERMODEL, UNCONDITIONAL** at (p, F) = (2, F4):
   `offsetPPin_isEmpty_of_ramified ramifiedStage (e = 2 ≠ 1)`.  Per R7's
   `offsetPPin_forces_stage_unramified`, any inhabitant of the bare pin would prove
   EVERY `Stage 2 F4` unramified — `ramifiedStage_e` refutes that consequence, so the pin
   type is empty for every policy; this is what certified `canPolicy_pin` (the (†15)
   designer sorry) unfillable AT ANY POLICY over (2, F4) in the pre-item-13 vocabulary.
   [M1 NOTE, queue item 13 EXECUTED 2026-07-31: `OffsetPPin.total` is now
   `HistoryCoherent`-keyed (PolPin.lean); this module's emptiness theorems are
   RE-POINTED at the frozen historical form `OffsetPPinBare` (R7_pinProbe.lean) and
   refute ONLY that form — proofs byte-unchanged.  The repaired `OffsetPPin` is out of
   this argument's reach: the forcing needed `total` at a bare probe node, which no
   coherent history contains (see the probe's M1 note; ramified frames are additionally
   unreachable pre-HK-06 per `HC2/HK22_twoNodeGate`).]

## Coexistence audit (M1 rule)

The refuted sorried universal (`canPolicy_pin`, MovesD/TreeCan.lean:492) is NOT in this
module's import closure: at HEAD `TreeCan` is imported only by
`MovesU/BridgeD1_treeModelWire`; this leaf imports `R7_pinProbe` (→ PolPin), `HK47`
(→ HK18/HK13/DefsTower), `HK56`/`HK14`, `S9_transStage` (→ the S9c/S9d spine) — closure
verified TreeCan-free (grep audit, this round; re-verified by the transitive scan in the
unit record).  No local vocabulary copies were needed: every consumed name is
import-safe (none lives in TreeCan).

moves_ref: MOVES 2464–2465 (S9, "the stage axioms all hold — the induction closes") +
D.4/D.7 (the (I-aug) side freedom: ANY coprime steep side is a legal increment read) +
the R7 record §finding (the ramified-frame semantics).
deps: R7_pinProbe · HK13/HK56/HK14 (proved bStageP core pieces) · HK47 (gate TransHyp) ·
S9_transStage (the D.7 capstone constructor).
sketch: assemble core → re-key side to (2,5) → fire S9 → choose → empty the pin.
difficulty: easy GIVEN the corpus (the content is the routing, not a new construction).
hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.R7_pinProbe
import LeanUrat.HC2.HK47
import LeanUrat.HC2.HK56_bStageCoreP1b
import LeanUrat.HC2.HK14_bStageCoreP2
import LeanUrat.HC1.S9_transStage

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD

namespace R7Forge

open Polynomial LeanUrat.Moves LeanUrat.MovesJ LeanUrat.HC1

/-- **The round-4 stage core of the base pin, assembled** — the eleven `StageCore` fields
are exactly the proved HK-13 (wPrev laws, reps, tie laws, prevIaug) / HK-56 (SlotDecomp,
CoeffFieldLawCore) / HK-14 (TvecLaw) theorems, slotted. -/
theorem bStageP_stageCore : StageCore bStageP where
  wPrev_mul := bStageP_wPrev_mul
  wPrev_ult := bStageP_wPrev_ult
  reps_nonempty := bStageP_reps_nonempty
  p_is_rep := bStageP_p_is_rep
  w_strict := bStageP_w_strict
  w_jump := bStageP_w_jump
  R_neg := bStageP_R_neg
  tvec := bStageP_tvecLaw
  prevIaug := bStageP_prevIaug
  slot := bStageP_slotDecomp
  coeff := bStageP_coeffFieldLawCore

/-- **`StageCoreL bStageP`, assembled** (the first discharge of HK-16's `hσ` hypothesis):
round-4 core + HK-14's `TvecUnitLaw` + HK-14's `CoeffLocLaw`. -/
theorem bStageP_stageCoreL : StageCoreL bStageP where
  core := bStageP_stageCore
  tvec_unit := bStageP_tvecUnitLaw
  coeff_loc := bStageP_coeffLocLaw

/-- **The RAMIFIED transition hypothesis** at the gate read: same (ψ₂, g, Φ̂, z̄) as
HK-47's `transHyp_gate`, side re-keyed to (e′, h′) = (2, 5).  The four side fields are
new (1 ≤ 2, 1 ≤ 5, gcd(2,5) = 1, and (I-aug) 5 > 2·w(fq) = 4 via the recorded
`bw fq = 2`); everything read-shaped is HK-47's field, verbatim. -/
theorem transHyp_ramified :
    TransHyp bStageP U31.ψ₂ 2 U31.fq 2 5 U31.ν₀.zbar :=
  { hmonic := HK47.transHyp_gate.hmonic
    hirr := HK47.transHyp_gate.hirr
    hne_z := HK47.transHyp_gate.hne_z
    hdeg := HK47.transHyp_gate.hdeg
    hg := HK47.transHyp_gate.hg
    hlift := HK47.transHyp_gate.hlift
    he' := by norm_num
    hh' := by norm_num
    hcop := by norm_num
    hiaug := by
      show (5 : ℤ) > (2 : ℤ) * bStageP.w U31.fq
      have hbf : bStageP.w U31.fq = 2 := U31.bw_eq HK13R.NF_θ_fq
      rw [hbf]
      norm_num
    hroot := HK47.transHyp_gate.hroot }

/-- **The forge**: the guarded S9 chain fired at the ramified side — a child stage of
`bStageP` with `e = 2`, `h = 5`, carrying the full transition record and the round-5
stage core.  (hEG : 1 < bStageP.e · g = 1·2 — the same gate guard as HK-16.) -/
theorem ramifiedStage_exists :
    ∃ σ' : Stage 2 F4,
      TransitionCoreL bStageP σ' U31.fq 2 5 U31.ν₀.zbar ∧ StageCoreL σ' ∧
      σ'.K = bStageP.nextField U31.ν₀.zbar ∧ σ'.e = 2 ∧ σ'.h = 5 :=
  S9_transStage bStageP bStageP_stageCoreL transHyp_ramified
    (by rw [bStageP_e_def]; norm_num)

/-- **THE COMPILED RAMIFIED STAGE** (the first in the corpus): the chosen S9 child of the
base pin under the (2,5) read — the `X² − p` Eisenstein-side semantics at p = 2 (a
slope-5/2, index-2 totally ramified read through the lift fq = X² + 2X + 4). -/
noncomputable def ramifiedStage : Stage 2 F4 := ramifiedStage_exists.choose

/-- The forge record: transition core + stage core + the K/e/h pins. -/
theorem ramifiedStage_spec :
    TransitionCoreL bStageP ramifiedStage U31.fq 2 5 U31.ν₀.zbar ∧
      StageCoreL ramifiedStage ∧
      ramifiedStage.K = bStageP.nextField U31.ν₀.zbar ∧
      ramifiedStage.e = 2 ∧ ramifiedStage.h = 5 :=
  ramifiedStage_exists.choose_spec

/-- The ramification index pin: `e = 2`. -/
theorem ramifiedStage_e : ramifiedStage.e = 2 := ramifiedStage_spec.2.2.2.1

/-- The slope-numerator pin: `h = 5`. -/
theorem ramifiedStage_h : ramifiedStage.h = 5 := ramifiedStage_spec.2.2.2.2

/-- The residue-field pin: no residue growth is claimed here beyond the S9 record. -/
theorem ramifiedStage_K : ramifiedStage.K = bStageP.nextField U31.ν₀.zbar :=
  ramifiedStage_spec.2.2.1

/-- The child's round-5 stage core (wave-D reuse: the forged frame is itself cored). -/
theorem ramifiedStage_coreL : StageCoreL ramifiedStage := ramifiedStage_spec.2.1

/-- The full transition record from the base pin (wave-D reuse). -/
theorem ramifiedStage_trans :
    TransitionCoreL bStageP ramifiedStage U31.fq 2 5 U31.ν₀.zbar :=
  ramifiedStage_spec.1

/-- **The stage is genuinely ramified**: `e ≠ 1`. -/
theorem ramifiedStage_ramified : ramifiedStage.e ≠ 1 := by
  rw [ramifiedStage_e]
  norm_num

/-- **THE R7 COUNTERMODEL, UNCONDITIONAL** (the discharge of `R7_pinProbe`'s conditional
leg): at (p, F) = (2, F4), the FROZEN pre-item-13 pin `OffsetPPinBare pol` is EMPTY for
EVERY policy — any bare pin would prove every `Stage 2 F4` unramified
(`offsetPPin_forces_stage_unramified`), and `ramifiedStage` is not.  [Item 13, 2026-07-31:
refutes ONLY the historical bare-Node form; see header §4 M1 note.] -/
theorem offsetPPin_isEmpty_unconditional (pol : CanonPolicy 2 F4) :
    IsEmpty (OffsetPPinBare pol) :=
  offsetPPin_isEmpty_of_ramified ramifiedStage ramifiedStage_ramified pol

/-- Consumption form: a BARE-form pin at any policy over (2, F4) is absurd. -/
theorem no_offsetPPin (pol : CanonPolicy 2 F4) (pin : OffsetPPinBare pol) : False :=
  (offsetPPin_isEmpty_unconditional pol).false pin

end R7Forge

end LeanUrat.MovesD

#print axioms LeanUrat.MovesD.R7Forge.bStageP_stageCoreL
#print axioms LeanUrat.MovesD.R7Forge.transHyp_ramified
#print axioms LeanUrat.MovesD.R7Forge.ramifiedStage_e
#print axioms LeanUrat.MovesD.R7Forge.offsetPPin_isEmpty_unconditional
