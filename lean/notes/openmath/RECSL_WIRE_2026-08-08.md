# RECSL_WIRE — the KP-STEP [RC] wiring on the RECSL suppliers

Wiring unit, 2026-08-08. Charter: consume `B2D/RECSL_suppliers.lean` (commit
1adac62, note `RECSL_F2_2026-08-08.md`) at the ONE compiled consumer slot for
(K0)-at-a-recentering content — `kp_step`'s argument 4 `hΦ : IsNodeLift ν σ'.Φ`
(`H1/TowerStep.lean:725`), threaded as `key1_along_history`'s `hlink` 4th
conjunct (`H1/SiteBlock.lean:78`) and `key1SiteBlock_step`'s verbatim binder
(`:158-159`). `HistoryCoherent` supplies `IsNodeLift` only on non-recentering
legs (`MovesC/Defs.lean:736`); the recentering leg was B-M2's REC-SL residue.

Compiled artifact: `lean/LeanUrat/Scaffold/HDischarge/H1/RecSLWire.lean` —
6 theorems, `lake env lean` green, zero `sorry`, `#print axioms` = Lean-core
(`propext, Classical.choice, Quot.sound`) on all six, no existing file touched.

## §1 THE PROVENANCE TRACE (charge item 1, read-only, executed first)

Question: at the `kp_step` recentering consumption sites, do frames arrive with
`StageCore` provenance (base-constructed + transition-transported)?

**The abstract site — NO (structurally):** the consumer's frame is a node of an
abstract `HistoryCoherent` run. The coherence records are `IsRecenteringCore`
(recentering leg, `MovesC/Defs.lean:729`) and `TransitionCoreL` (non-recentering
leg, `:737`); NEITHER bundles `StageCore` (`Moves/DefsCore.lean:242-246`,
`Moves/DefsL.lean:198-206`). On the abstract carrier the provenance is genuine
hypothesis content — exactly the RECSL note's prediction ("the history layer
cannot hand it over").

**Every compiled consumption site — YES:** the only on-file interior-recentering
history is `RCW.H₃rc` (`H1/RCWitness.lean:401`; the `rc_historyCoherent_gate`
family). Its recentering frame σ₁rec carries the full LIVE engine chain:

* base: `bStageP_stageCoreL' : StageCoreL bStageP`
  (`HC2/HK15_gateChildCarrier.lean:139`);
* increment transport: `HC1.S9_transStage` fired as `gateChildStage_exists`
  (`HK15:168-174`) → `StageCoreL HK25.σ₁rec`; PUBLIC handle `score_σ₁rec`
  (`H1/TruncatedRun.lean:713`; RCWitness's own `score₁` at `:145` is private);
* recentering transport: `HC1.S10_recStage` (`HC1/S10_recStage.lean:376-382`)
  → `StageCoreL σ₂rc` (`RCW.score₂`, `RCWitness.lean:170`).

CAUTION (docstring vs corpus): the `StageCore` docstring's named suppliers
`L1.baseStage_exists`/`L4.TRANSstage`/`L5.recTRANSRS` are the RETIRED MovesGr
held units (FAITHLESS — `MovesGr/HeldUnits_certs.lean`, `HeldUnits_L5_cert.lean`);
the live chain is HC1's `T1_baseStage` (`T1_baseStage.lean:1667`, constructs
`StageCoreL`) / `S9_transStage` (`S9_transStage.lean:82-85`) / `S10_recStage` —
all carrying `StageCoreL ⊇ StageCore` (`Moves/DefsL.lean:186-189`).

**VERDICT: PROVENANCE-AVAILABLE at every compiled recentering consumption site
(exactly one on-file family, H₃rc), and structurally ABSENT on the abstract
carrier — there it rides as the displayed provenance row `hsc`, discharged
wherever the tower is engine-built.**

## §2 THE WIRING (charge item 2; file map, Lean order)

* `hlink_nodeLift_of_history` — THE DISPATCHER: `hlink`'s 4th conjunct
  (`IsNodeLift (nodes[i]) (nodes[i+1].σ.Φ)`) at EVERY leg. [NR] legs: verbatim
  from `HistoryCoherent`'s non-recentering record. [RC] legs:
  `recsl_isNodeLift_of_history_stageCore` (= `recsl_isNodeLift_of_history` +
  `signLaw_of_stageCore`, per the charge). Two displayed rows: `hfence` (every
  successor-having recentering leg has a non-recentering predecessor — the GR0b
  recentering-CHAIN fence, inherited) and `hsc` (`StageCore` at successor-having
  recentering frames — the provenance row). The i = 0 leg needs no fence: node 0
  is root by `History.root_iff`, never recentering (proved in-line).
* `kp_step_of_recentering` — `kp_step` FIRED at an interior [RC] leg, `hΦ`
  RECSL-supplied; `he`/`hh`/`hwp` + `DevBound` stay displayed rows (finding 11).
* `key1SiteBlock_step_of_recentering` — the U10 assembly at an [RC] leg (laws
  binder = U9's row, finding 12).
* `key1_along_history_recsl` — the re-keyed H1-U11 fold: `hlink` loses its
  `IsNodeLift` conjunct entirely (consumers owe only the three parity ties),
  at the price of `hfence` + `hsc`. The [RC] IsNodeLift debt is no longer a
  consumer obligation anywhere in the fold.
* GATES (positive, at the compiled family): `rc_recSL_hPhi_gate :
  IsNodeLift RCW.ν₁rc RCW.σ₂rc.Φ` — the history-level supplier fires on H₃rc
  with `score_σ₁rec.core`; `rc_hlink_gate` — the dispatcher delivers the
  conjunct at EVERY H₃rc leg, both rows discharged concretely (fence: ν₀ram is
  root; provenance: `score_σ₁rec.core`; the terminal recentering ν₂rc owes no
  row — no successor).

Cross-check: `GlueRun.lean:986` (`landingKey_ν₁rcRoot`) already proved the SAME
instance fact `IsNodeLift ν₁rc σ₂rc.Φ` hand-rolled (digit `−rcLift`,
`StageCore.R_neg` off `score_σ₁rec`) — the F3 walk's observation. `rc_recSL_hPhi_gate`
re-derives it THROUGH the general history-level supplier chain, confirming the
wiring reproduces the hand-built instance from the abstract route.

## §3 VERDICT ON B-M2's REC-SL OPEN (charge item 4)

**NARROWED-TO (not fully closed-by-wiring), with CLOSED-AT-EVERY-COMPILED-SITE.**
Precisely: at the KP-STEP route ((i-c) leg (1)) the `IsReadLift`-at-(1,1) +
(SL-top)/(SL-dev) obligations at [RC] legs are now SUPPLIED by compiled wiring,
leaving exactly TWO displayed rows on the abstract carrier:

1. **The provenance row `hsc`** — `StageCore` at each successor-having
   recentering frame (the RECSL-SIGN pin's carrier; `σ.R(−1) = −1` via
   `signLaw_of_stageCore`). Discharged on every engine-built tower
   (T1/S9/S10 all transport `StageCoreL`) and at every compiled site
   (`score_σ₁rec.core`). Open ONLY for abstract recorded histories with no
   engine provenance — the status class of the pre-route-(a) GR-3/GR-4 pins.
2. **The recentering-chain fence `hfence`** — [RC] legs whose predecessor is
   ALSO recentering are not covered (inherited: `readHyps_of_history` needs a
   non-recentering landing one step back; GR0b's standing future-work fence,
   NOT sign-related).

Scope fences (inherited, not residue): terminal recenterings have no recorded
fired key (legs live at `i+1+1 < len`); engine-firing shape vs recorded shape
stays S-1/SITE-EXH side (REV-12 scope note). NOT REC-SL and untouched: the
hlink parity ties (`σ'.e/h/wPrev` vs the parent pair) remain rows at every leg —
at [RC] legs the third tie reads `σ.wPrev = σ.w` at the frame (`IsRecentering`
keeps `wPrev` unchanged), a model-dependent row, displayed in the file header.
(K1)+(K2) still ride GRADED-READ, exactly as the RECSL note priced.

For the B-M2 note's consolidated opens list (rides the next revision, NOT this
unit): item 2 "REC-SL proper" can be re-priced from "the `IsReadLift`-at-(1,1)
form + the (SL-top)/(SL-dev) digit obligations" to "the `hsc` provenance row on
abstract carriers + the recentering-chain fence" — with the KP-STEP consumer slot
compiled-fed at [RC] (this unit) and at [NR] (coherence verbatim).

## §4 FOOTPRINTS

All six new theorems: `[propext, Classical.choice, Quot.sound]` (printed by the
file's `#print axioms` block; `lake env lean` clean, zero warnings). Imports FROM
the new file only: `B2D.RECSL_suppliers`, `H1.SiteBlock`, `H1.TruncatedRun`.
No existing statement or proof modified.

— KP-STEP [RC] wiring unit, 2026-08-08.
