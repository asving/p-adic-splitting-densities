/-
HDISCHARGE_H1 — `H1/RecSLWire.lean`: THE KP-STEP [RC] WIRING (the RECSL-supplier
consumption step; unit note `lean/notes/openmath/RECSL_WIRE_2026-08-08.md`).

CHARGE: wire the new RECSL suppliers (`B2D/RECSL_suppliers.lean`, commit 1adac62)
into the ONE compiled consumer slot for (K0)-at-a-recentering content — `kp_step`'s
argument 4 `hPhi : IsNodeLift ν σ'.Φ` (`H1/TowerStep.lean:725`), threaded as
`key1_along_history`'s `hlink` 4th conjunct and `key1SiteBlock_step`'s verbatim
binder (`H1/SiteBlock.lean`).  `HistoryCoherent` supplies `IsNodeLift` only on
NON-recentering legs (`MovesC/Defs.lean:736`); the recentering leg was the open
slot — B-M2's REC-SL residue.

PROVENANCE TRACE (charge item 1, executed read-only before this build):
* THE ABSTRACT CONSUMPTION SITE (`hlink`, `key1SiteBlock_step`'s `hΦ`): frames
  arrive WITHOUT `StageCore` — `HistoryCoherent`'s records are `IsRecenteringCore`
  (recentering leg, `MovesC/Defs.lean:729`) and `TransitionCoreL` (non-recentering
  leg, `:737`), and NEITHER bundles `StageCore` (`Moves/DefsCore.lean:242`,
  `Moves/DefsL.lean:198`).  On the abstract carrier the provenance is therefore a
  HYPOTHESIS ROW (the `hsc` binder below), same status class as the pre-route-(a)
  GR-3/GR-4 frame pins.
* EVERY COMPILED CONSUMPTION SITE HAS IT: the only on-file interior-recentering
  history is `RCW.H₃rc` (`H1/RCWitness.lean`), whose recentering frame σ₁rec
  carries the full engine chain — base `bStageP_stageCoreL' : StageCoreL bStageP`
  (`HC2/HK15_gateChildCarrier.lean:139`), increment transport `HC1.S9_transStage`
  via `gateChildStage_exists` (`HK15:168-174`; public handle `score_σ₁rec`,
  `H1/TruncatedRun.lean:713`), recentering transport `HC1.S10_recStage`
  (`HC1/S10_recStage.lean:376`; `RCW.score₂`).  [The `L1.baseStage_exists` /
  `L4.TRANSstage` / `L5.recTRANSRS` names in the `StageCore` docstring are the
  RETIRED MovesGr held units (`MovesGr/HeldUnits_certs.lean` — FAITHLESS); the
  LIVE engine chain is HC1's `T1_baseStage` / `S9_transStage` / `S10_recStage`,
  all carrying `StageCoreL`.]

WHAT IS COMPILED HERE (sorry-free; no existing statement touched; Lean-core):
* `hlink_nodeLift_of_history` — THE DISPATCHER: `hlink`'s 4th conjunct
  (`IsNodeLift` at EVERY leg) from `HistoryCoherent` alone at [NR] legs and from
  the RECSL suppliers + `StageCore` provenance at [RC] legs.  Hypothesis rows,
  both scoped to what the RECSL route needs and both DISCHARGED at the compiled
  witness family: `hfence` (interior recentering legs have a non-recentering
  predecessor — the GR0b recentering-CHAIN fence, standing) and `hsc` (`StageCore`
  at successor-having recentering frames — the provenance row).  The i = 0 leg
  needs no fence: node 0 is root by `History.root_iff`, never recentering.
* `kp_step_of_recentering` / `key1SiteBlock_step_of_recentering` — the drop-in
  consumers: `kp_step` (resp. the U10 site-block assembly) FIRED at an interior
  recentering leg of a coherent history, `hΦ` supplied by
  `recsl_isNodeLift_of_history_stageCore` (= `recsl_isNodeLift_of_history` +
  `signLaw_of_stageCore`); the remaining binders (`he`/`hh`/`hprev`, `DevBound`,
  laws) stay the displayed rows per the finding-11/12 discipline.
* `key1_along_history_recsl` — the re-keyed history fold: `key1_along_history`
  with the `IsNodeLift` conjunct DELETED from `hlink` (consumers owe only the
  three parity ties) at the price of `hfence` + `hsc`.  The [RC] IsNodeLift debt
  is no longer a consumer obligation anywhere in the fold.
* THE GATES (non-vacuity, positive; at the compiled interior-recentering family):
  `rc_recSL_hPhi_gate : IsNodeLift RCW.ν₁rc RCW.σ₂rc.Φ` — the history-level RECSL
  supplier FIRES on `H₃rc` with `score_σ₁rec.core`; and `rc_hlink_gate` — the
  dispatcher delivers `hlink`'s 4th conjunct at EVERY leg of `H₃rc` (both rows
  discharged concretely).

WHAT IS NOT CLAIMED (honesty ledger):
* The hlink PARITY TIES (`σ'.e = ν.e`, `σ'.h = ν.h`, `σ'.wPrev = ν.σ.w`) remain
  hypothesis rows at every leg — NOT REC-SL content, never supplied here.  Note
  at [RC] legs `IsRecentering` gives `σ'.wPrev = σ.wPrev`, so the third tie there
  amounts to `σ.wPrev = σ.w` at the frame — a model-dependent row, displayed.
* The GR0b scope fences are INHERITED, not lifted: the RECSL route needs a
  non-recentering landing one step back (`hfence`), and terminal recenterings
  have no recorded fired key (legs live at `i+1+1 < len`).
* Nothing here advances (H1) itself: `DevBound` is STAGING ONLY (finding 11),
  the laws binder is the U9 row (finding 12), and model-chain non-vacuity at the
  fold is the open A-M2 leaf.  Never cite these theorems alone as evidence for
  (H1).
-/
import LeanUrat.B2D.RECSL_suppliers
import LeanUrat.Scaffold.HDischarge.H1.SiteBlock
import LeanUrat.Scaffold.HDischarge.H1.TruncatedRun

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.Scaffold.HDischarge.H1

open Polynomial LeanUrat.Moves LeanUrat.MovesGr LeanUrat.MovesC LeanUrat.MovesJ
open LeanUrat.B2D

universe u
variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-! ## §1 — the dispatcher: `hlink`'s `IsNodeLift` conjunct at EVERY leg -/

/-- **THE [RC] WIRING DISPATCHER** — `key1_along_history`'s `hlink` 4th conjunct,
supplied at EVERY leg of a coherent history: at non-recentering legs verbatim from
`HistoryCoherent`'s non-recentering record; at recentering legs from the RECSL
suppliers (`recsl_isNodeLift_of_history_stageCore` =
`recsl_isNodeLift_of_history` + `signLaw_of_stageCore`), given
* `hfence` — every successor-having recentering leg has a NON-recentering
  predecessor (the GR0b recentering-chain fence, inherited; the leg at i = 0 needs
  none: node 0 is root by `History.root_iff`);
* `hsc` — `StageCore` at every successor-having recentering frame (the PROVENANCE
  ROW: `HistoryCoherent`'s records bundle no `StageCore`, so on the abstract
  carrier this is a genuine hypothesis; the engine chain
  `T1_baseStage`/`S9_transStage`/`S10_recStage` discharges it on every
  engine-built tower, and `score_σ₁rec.core` discharges it at the compiled
  witness family — `rc_hlink_gate` below). -/
theorem hlink_nodeLift_of_history {H : History p F} (hcoh : HistoryCoherent H)
    (hfence : ∀ (k : ℕ) (hk : k + 1 + 1 < H.nodes.length),
      (H.nodes[k+1]'(by omega)).species = ReadSpecies.recentering →
      (H.nodes[k]'(by omega)).species ≠ ReadSpecies.recentering)
    (hsc : ∀ (k : ℕ) (hk : k + 1 < H.nodes.length),
      (H.nodes[k]'(by omega)).species = ReadSpecies.recentering →
      StageCore (H.nodes[k]'(by omega)).σ) :
    ∀ (i : ℕ) (hi : i + 1 < H.nodes.length),
      IsNodeLift (H.nodes[i]'(by omega)) ((H.nodes[i+1]'hi).σ.Φ) := by
  intro i hi
  by_cases hspec : (H.nodes[i]'(by omega)).species = ReadSpecies.recentering
  · -- [RC] leg: the RECSL route
    match i, hi, hspec with
    | 0, hi, hspec =>
        -- node 0 is root (`root_iff`), never recentering
        have hroot : (H.nodes[0]'(by omega)).species = ReadSpecies.root :=
          (H.root_iff 0 (by omega)).mpr rfl
        exact absurd (hroot.symm.trans hspec) (fun h => ReadSpecies.noConfusion h)
    | k + 1, hi, hspec =>
        have hprev : (H.nodes[k]'(by omega)).species ≠ ReadSpecies.recentering :=
          hfence k hi hspec
        exact recsl_isNodeLift_of_history_stageCore hcoh hi hprev hspec
          (hsc (k+1) (by omega) hspec)
  · -- [NR] leg: `HistoryCoherent`'s non-recentering record carries the clause
    obtain ⟨-, -, -, htrans⟩ := hcoh
    obtain ⟨-, hnonrec, -⟩ := htrans i hi
    obtain ⟨-, σV, -, hlift, -⟩ := hnonrec hspec
    exact hlift

/-! ## §2 — the drop-in consumers: `kp_step` / the U10 site block at an [RC] leg -/

/-- **`kp_step` FIRED at an interior recentering leg** — the KP-STEP [RC]
consumption: `hΦ` is supplied by the RECSL route (history record + `ReadHyps` via
GR0b + the sign law from the frame's `StageCore`); the parity ties `he`/`hh`/`hwp`
and the `DevBound` row (STAGING ONLY, finding 11) remain the displayed per-step
rows, verbatim `kp_step`'s binder block. -/
theorem kp_step_of_recentering {H : History p F} (hcoh : HistoryCoherent H)
    {i : ℕ} (hi2 : i + 1 + 1 < H.nodes.length)
    (hprev : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
    (hspec : (H.nodes[i+1]'(by omega)).species = ReadSpecies.recentering)
    (hcore : StageCore (H.nodes[i+1]'(by omega)).σ)
    (M : GenuineStageModel ((H.nodes[i+1+1]'hi2).σ))
    (he : (H.nodes[i+1+1]'hi2).σ.e = (H.nodes[i+1]'(by omega)).e)
    (hh : (H.nodes[i+1+1]'hi2).σ.h = (H.nodes[i+1]'(by omega)).h)
    (hwp : (H.nodes[i+1+1]'hi2).σ.wPrev = (H.nodes[i+1]'(by omega)).σ.w)
    (D : DevBound (H.nodes[i+1]'(by omega)) ((H.nodes[i+1+1]'hi2).σ) M) :
    Nonempty (KPBlock ((H.nodes[i+1+1]'hi2).σ) M) :=
  kp_step _ _ M (recsl_isNodeLift_of_history_stageCore hcoh hi2 hprev hspec hcore)
    he hh hwp D

/-- **The U10 site-block assembly FIRED at an interior recentering leg** —
`key1SiteBlock_step` with `hΦ` RECSL-supplied; the laws binder is U9's explicit
row (finding 12), untouched. -/
theorem key1SiteBlock_step_of_recentering {H : History p F} (hcoh : HistoryCoherent H)
    {i : ℕ} (hi2 : i + 1 + 1 < H.nodes.length)
    (hprev : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
    (hspec : (H.nodes[i+1]'(by omega)).species = ReadSpecies.recentering)
    (hcore : StageCore (H.nodes[i+1]'(by omega)).σ)
    (M : GenuineStageModel ((H.nodes[i+1+1]'hi2).σ))
    (he : (H.nodes[i+1+1]'hi2).σ.e = (H.nodes[i+1]'(by omega)).e)
    (hh : (H.nodes[i+1+1]'hi2).σ.h = (H.nodes[i+1]'(by omega)).h)
    (hwp : (H.nodes[i+1+1]'hi2).σ.wPrev = (H.nodes[i+1]'(by omega)).σ.w)
    (D : DevBound (H.nodes[i+1]'(by omega)) ((H.nodes[i+1+1]'hi2).σ) M)
    (laws : ∀ KB : KPBlock ((H.nodes[i+1+1]'hi2).σ) M,
      GrBKeyLaws (H.nodes[i+1]'(by omega)) ((H.nodes[i+1+1]'hi2).σ) M KB) :
    Key1SiteBlock (H.nodes[i+1]'(by omega)) ((H.nodes[i+1+1]'hi2).σ) M :=
  key1SiteBlock_step _ _ M
    (recsl_isNodeLift_of_history_stageCore hcoh hi2 hprev hspec hcore)
    he hh hwp D laws

/-! ## §3 — the re-keyed history fold: `hlink` loses its `IsNodeLift` conjunct -/

/-- **H1-U11 RE-KEYED (`key1_along_history_recsl`)** — the history fold with the
`IsNodeLift` conjunct DELETED from the per-step `hlink` row: consumers now owe only
the three parity ties (`hties`), plus the two RECSL rows `hfence` (recentering-chain
fence) and `hsc` (`StageCore` provenance at recentering frames).  The `IsNodeLift`
conjunct is rebuilt at every leg by the dispatcher — `HistoryCoherent` at [NR],
RECSL + provenance at [RC] — so the [RC] IsNodeLift debt is no longer a consumer
obligation anywhere in the fold.  Everything else is `key1_along_history` verbatim
(same `hdev`/`hlaws` rows, same conclusion; never cite as evidence for (H1)). -/
theorem key1_along_history_recsl (H : History p F) (hH : HistoryCoherent H)
    (M : ∀ (j : ℕ) (hj : j < H.nodes.length), GenuineStageModel ((H.nodes[j]'hj).σ))
    (hfence : ∀ (k : ℕ) (hk : k + 1 + 1 < H.nodes.length),
      (H.nodes[k+1]'(by omega)).species = ReadSpecies.recentering →
      (H.nodes[k]'(by omega)).species ≠ ReadSpecies.recentering)
    (hsc : ∀ (k : ℕ) (hk : k + 1 < H.nodes.length),
      (H.nodes[k]'(by omega)).species = ReadSpecies.recentering →
      StageCore (H.nodes[k]'(by omega)).σ)
    (hties : ∀ (i : ℕ) (hi : i + 1 < H.nodes.length),
      (H.nodes[i+1]'hi).σ.e = (H.nodes[i]'(by omega)).e ∧
      (H.nodes[i+1]'hi).σ.h = (H.nodes[i]'(by omega)).h ∧
      (H.nodes[i+1]'hi).σ.wPrev = (H.nodes[i]'(by omega)).σ.w)
    (hdev : ∀ (i : ℕ) (hi : i + 1 < H.nodes.length),
      DevBound (H.nodes[i]'(by omega)) ((H.nodes[i+1]'hi).σ) (M (i+1) hi))
    (hlaws : ∀ (i : ℕ) (hi : i + 1 < H.nodes.length)
      (KB : KPBlock ((H.nodes[i+1]'hi).σ) (M (i+1) hi)),
      GrBKeyLaws (H.nodes[i]'(by omega)) ((H.nodes[i+1]'hi).σ) (M (i+1) hi) KB) :
    ∀ (i : ℕ) (hi : i + 2 < H.nodes.length),
      Key1SiteBlock (H.nodes[i+1]'(by omega)) ((H.nodes[i+2]'hi).σ) (M (i+2) hi) :=
  key1_along_history H hH M
    (fun i hi => ⟨(hties i hi).1, (hties i hi).2.1, (hties i hi).2.2,
      hlink_nodeLift_of_history hH hfence hsc i hi⟩)
    hdev hlaws

/-! ## §4 — the gates (non-vacuity, positive; at the compiled interior-recentering
family `RCW.H₃rc`) -/

/-- **GATE 1 — the history-level RECSL supplier FIRES on the compiled witness**:
`IsNodeLift RCW.ν₁rc RCW.σ₂rc.Φ` via `recsl_isNodeLift_of_history_stageCore` at
`H₃rc`'s interior recentering leg (i = 0: ν₀ram → ν₁rc → ν₂rc), provenance
discharged by the engine chain's `score_σ₁rec.core` (`T1`-base → `S9_transStage`
child; `H1/TruncatedRun.lean:713`).  This is `kp_step`'s `hΦ` argument at the
[RC] site, concretely inhabited. -/
theorem rc_recSL_hPhi_gate : IsNodeLift RCW.ν₁rc RCW.σ₂rc.Φ := by
  have hlen : (0 : ℕ) + 1 + 1 < RCW.H₃rc.nodes.length := by
    rw [RCW.H₃rc_len]; omega
  have h := recsl_isNodeLift_of_history_stageCore RCW.coherent_H₃rc hlen
    (show (RCW.H₃rc.nodes[0]'(by omega)).species ≠ ReadSpecies.recentering from
      fun hc => ReadSpecies.noConfusion hc)
    (show (RCW.H₃rc.nodes[0+1]'(by omega)).species = ReadSpecies.recentering from rfl)
    (show StageCore (RCW.H₃rc.nodes[0+1]'(by omega)).σ from score_σ₁rec.core)
  exact h

/-- **GATE 2 — the dispatcher delivers `hlink`'s `IsNodeLift` conjunct at EVERY leg
of `H₃rc`**, both hypothesis rows discharged concretely: the fence by ν₀ram's root
species, the provenance row by `score_σ₁rec.core` (the terminal recentering ν₂rc
has no successor, so no row is owed there).  `hlink`'s 4th conjunct is FULLY
SUPPLIED on the compiled interior-recentering family. -/
theorem rc_hlink_gate :
    ∀ (i : ℕ) (hi : i + 1 < RCW.H₃rc.nodes.length),
      IsNodeLift (RCW.H₃rc.nodes[i]'(by omega)) ((RCW.H₃rc.nodes[i+1]'hi).σ.Φ) := by
  refine hlink_nodeLift_of_history RCW.coherent_H₃rc ?_ ?_
  · -- the fence row: the only interior recentering leg (k = 0) has root predecessor
    intro k hk hrec
    have hk0 : k = 0 := by rw [RCW.H₃rc_len] at hk; omega
    subst hk0
    exact fun hc => ReadSpecies.noConfusion hc
  · -- the provenance row: k = 0 is root (vacuous); k = 1 is σ₁rec, engine-cored
    intro k hk hrec
    have hk2 : k < 2 := by rw [RCW.H₃rc_len] at hk; omega
    interval_cases k
    · exact absurd hrec (fun hc => ReadSpecies.noConfusion hc)
    · exact score_σ₁rec.core

end LeanUrat.Scaffold.HDischarge.H1

#print axioms LeanUrat.Scaffold.HDischarge.H1.hlink_nodeLift_of_history
#print axioms LeanUrat.Scaffold.HDischarge.H1.kp_step_of_recentering
#print axioms LeanUrat.Scaffold.HDischarge.H1.key1SiteBlock_step_of_recentering
#print axioms LeanUrat.Scaffold.HDischarge.H1.key1_along_history_recsl
#print axioms LeanUrat.Scaffold.HDischarge.H1.rc_recSL_hPhi_gate
#print axioms LeanUrat.Scaffold.HDischarge.H1.rc_hlink_gate
