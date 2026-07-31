# REMAINING-WORK CENSUS (2026-08-01, post-everything sweep — the evening after the 21-item queue + open-math fleet + HK-06 wave)

**Goal of record** (unchanged; BRIDGE_ADJUDICATIONS_2026-07-30.md AUTHORITY UPDATE):
`theoremU` conditional ONLY on literature statements — GMN + Denef–Igusa admissible
as cited axioms (now also AX-SERRE-DVR, declared + audited); arXiv:2212.00294
EXCLUDED as a source; htameFE out of the goal's critical path.  This census is the
ground truth of everything between HEAD (324a85f, post-HK-06-wave) and that goal.
Method: comment-aware sorry sweep (block/line comments + strings stripped) over
`lean/LeanUrat`; the capstone hypothesis-row sweep at `MovesU/U10_theoremU.lean` +
`DefsLedger.lean` + `DefsCarriers.lean` + `BridgeKernels.lean` + `BridgeMk.lean`
as built at HEAD; cross-checked against QUEUE_EXECUTION_2026-07-31.md (21/21) and
the BRIDGE_ADJUDICATIONS 2026-07-31 fold-ins (open-math fleet 18/18, numerics 8/8,
verification round 1, Group E, IFK, HK-06).

## 0. SUMMARY TABLE (one page)

**Sorry census: 43 real `sorry` tokens in 26 files** (predecessor: 114 in 40).
1 banked off-path (OM/Classifier.lean:1255) · 4 honest HK-11 reopenings (V9) ·
5 dead-vocabulary blocked records awaiting quarantine disposition (SlotsG2/G3) ·
~33 open duties (Phase-B rows, hoisted twins, probes, residuals).

| class | count | contents |
|---|---|---|
| SIGN-OFF-GATED (fence events 22–27 + G13′) | 0 sorries held; 7 statement-level events | the six refuted-as-typed rows from the open-math fleet (jcInvHist, track_restarts, count_tie/NsFree, child_local, vp_sound, SibJcRows) + `theoremU_bridged′` drafting (gated on 22) — see §4.1 |
| PHASE-B-BLOCKED (named open rows) | 9 sorries | F-chain TV_F2–F6 + V7_rbC behind `RealizationComplete` (= M18 MarkGraft); V7_livC behind the `hfin` ratification; V7_scsData + TV_G3-(e) behind the wave-D witness |
| AUTONOMOUS (provable/executable now) | ~24 sorries | TV_A2/A3/A4 hoisted-twin retirement (4, provable from landed item-5 rows); TV_G3 residuals (a)–(d) (7); G1_toyGate post-wave re-adjudication (4, HK23 carriers supply); V9 HK-52/HK-11 legs (4, post-wave BP2 queue); U17a/U26 (2); BridgeD19 n2 probe (1); SlotsG11c falsifier (1); C6 CL-05 leg (1) |
| BANKED / RECORD | 6 sorries | OM/Classifier (1, off-path); CL04 probe slot (1, pends CL-05); TreeCan canPolicy pair (2, residual = ONE compiled Prop `RunRealizerExists`); SlotsG2/G3 dead records (5 → quarantine disposition) — G2/G3 counted here |
| OPEN-MATH (hypothesis rows, no sorry token) | ~14 rows | see §4.3 — SHRUNK: cl11_ksub PROVED all n, cl17 PROVED all chains, cl6 n=2 POSITIVE, ZpBridge laws DISCHARGED (Serre axiom), REG-p finiteness FORMALIZED; five rows moved to REFUTED-AS-TYPED (the fence events); the semantic residue converges on THE IFK (instance-faithfulness kernel, blueprint in revision) |

**The capstone chain at HEAD (all compiled, Lean-core):**
`theoremU` (U10, proved) ← `theoremU_fired` (BridgeMk IB-F5, proved) ←
`mkUInstance` (IB-F4, proved) ← `BridgeInputs` — and the `BridgeInputs` field
table is **CONSTRUCTION-COMPLETE** (every field has a landed constructed supplier,
incl. `bridge : ZpBridge` = IB-E9 `bridgeZpBridge` over the audited Serre axiom),
modulo the R7 designer conditionality, which item 13 REDUCED to ONE compiled named
Prop: `RunRealizerExists p (ZMod p)` (`MovesD/R7_polFillReduction.lean`;
`canPolicyC_pin` proves the whole repaired pin from it).  What stands between HEAD
and the goal is exactly: (a) the six fence-event statement repairs (§4.1) — five
capstone-ledger rows are now REFUTED AS TYPED with compiled/dual evidence and
adjudicated repair shapes; (b) THE IFK — the one instance-faithfulness kernel that
M02/M05/M06/M12/M18 all reduce to (blueprint REJECTed at plan review, revision 1
in flight; BNS 3.13 = the 5th literature-axiom candidate, stripped to its faithful
clause); (c) `RunRealizerExists` + the HK-52/HK-11 transport legs (the BP2
post-wave queue); (d) the wave-D carrier instance at n = 2 (HK23's ramified 2-node
history + the forge stages are the groundwork); (e) G13′ after item 22; (f) the
non-literature open math that remains (K7 lemmas, X.1b/X.2, EQ-2 discharge,
RealizationComplete).

## DELTA FROM YESTERDAY (2026-07-31 census → this one)

**Net sorry count: 114 → 43 (−75 retired, +4 added).**

Retired, by landing (tree-verified):
* Item 4 (W17ii): TV_H1b 6 deleted-unfillable-false + V7_w17ii 1 PROVED = −7.
  `w17ii_wave4` now PROVED at EVERY repaired RS4Chain (counting squeeze; 5 census
  fields added to the structure); **BK.cl17 is DERIVED at every chain**.
* Item 5 (E5 hoist): E5_rootSplit −1; the TREE-EXP spine (fiber_root_split/
  treeExp/perShape_law/treeN) is sorry-free Lean-core with named hU/hR rows.
* Item 6 + CL01 landing: CL01a/b/c −11 (Tshallow + certificates PROVED).
* Item 9: BridgeRosterPins −1 (refuted universal DELETED; the §23 two-part
  re-scope PROVED; IB-B16 covered display closes under `BridgeDiteOK`).
* Items 11 + BP3-E: TV_E6 −1, TV_E7 −1, TV_E8 −2 (E-cluster sorry-free).
* Item 15 + G-cluster: TV_G1 −2, TV_G2 −8.
* Items 12/16/17/21: U4 −1 (PROVED AS STATED, (o-i)), HK15 −6, U10_zcStep −5
  ((ZC) chain CLOSED, statements byte-unchanged), U21 −1 (hoist) = −13.
* Item 19: R6_carrierInstance −1 (PROVED non-vacuously, Lean-core).
* Item 20: KA4c −1 (2 ≤ n guard; row closed).
* D-SC H-phase: SlotsG16 −4, G17 −1, G18 −6 (the 11 slot bodies FILLED).
* Forge + A5 round: TV_A5a −6, TV_A5b −2 (compiled realizable root nodes).
* Autonomous fills: KE9 −1, KE10 −1, CL16 −1, CL17 −1, CL20 −1, C6 net 0
  (relocated to the repaired statement's ⟸ leg).
* Hygiene quarantines (2026-07-31): Moves/L6_R3 −1, HC1/CL10 −1 (both in
  `quarantine/*_2026-07-31.lean.txt` with records).

Added (+4): `HC1/V9_K1nonrec.lean:2606,2617,2661,2672` — the HK-06 wave's HONEST
REOPENING (the old steep-leg closures were a masked V10 exfalso, deleted with
archival; the corners consumed the OLD-keyed record).  These are the HK-52/HK-11a/b
obligations, priced in advance by BP2 REVISION-2 finding 1.

Hypothesis-row deltas (§2 rows that moved):
* `BK.cl11_ksub` OPEN-MATH → **PROVED AT ALL n** (M09, `MovesU/KsubGeneral.lean`).
* `BK.cl17` OPEN-MATH → **PROVED at every chain** (item 4, `w17ii_pin`).
* `BK.cl6` n=2 leg → POSITIVE (`n2_polyGeomLaws_nonempty`); general n open (M08).
* `bridge : ZpBridge` missing → **PROVED construction** (Group E, IB-E5/E6/E7/E9
  on the audited `AX_integralClosure_dvr`); §2.2 CONSTRUCTION-COMPLETE.
* per-p `RegP` → failing-prime set **FINITE, FORMALIZED** (M17,
  `MovesU/RegPFinite.lean`, 14 thms Lean-core; `regP_cofinite` via `detHyp`).
* `seam.count_tie` OPEN-MATH → **REFUTED AS TYPED** (M02; fence event 24: NsFree).
* `BK.vp_sound` OPEN-MATH → **REFUTED AS BUILT** (M06; fence event 26; same root).
* `BK.sibjc` OPEN-MATH → PLAUSIBLY FALSE AS TYPED (M07; fence event 27).
* `K7.track_restarts` OPEN-MATH → **REFUTED at intended instance** (M01 + N7
  numerics; fence event 23: runCount re-type).
* `Ctor.transfer`/ReadLocality → item 7 EXECUTED, then the kernel **REFUTED at
  the canonical instance even in corrected form** (M03; fence event 25).
* `cl19_rep` → REFUTED AS STATED (M11, dual; queue item 22; G13′ gated).
* `BK.env_tendsto` → M05 PARTIAL-VERIFIED: semantic-classifier exhaustion WITH
  RATE proved at every prime incl. wild; residual = the project-classifier tie
  (OL2, BNS 3.13 pinned) — an IFK face.
* `KT.cl15_align` → GMN citation PINNED (TAMS 364 Thm 4.18(1)); `GMNIndex.lean`
  statement DRAFT with the axiom keyword WITHHELD (zero-witness on record).
* R7 designer conditionality → REDUCED to `RunRealizerExists` (item 13).

## 1. THE COMMENT-AWARE SORRY SWEEP (43 real tokens, 26 files)

### MovesD + MovesT (12)

| file:lines | holds | needs |
|---|---|---|
| MovesD/TreeCan.lean:499,506 | `canPolicy`/`canPolicy_pin` — the R7 designer data | item 13 REDUCED the residue to ONE compiled Prop `RunRealizerExists p (ZMod p)` (R7_polFillReduction; interior half PROVED from coherence). Open content: (a) the (S6b′) monomial-shape clause at deg Φ > 1 (HC-1 residue); (b) the LAST-NODE FLANK (JetSetup.landing seam; countermodel search now LIVE post-HK23) |
| MovesT/E11_treeN.lean:121 | `treeN_stable` | the ReadLocality kernel — now REFUTED at the canonical instance (fence event 25) — + the cluster-B guard collapse (not signed); honest-open |
| MovesT/TV_B7.lean:107 | `treeN_stable_hoisted` | same row's hoisted face (single admission with E11) |
| MovesT/TV_A2.lean:81 · TV_A3.lean:81,117 · TV_A4.lean:79 | the item-5 `*_hoisted` twins (4) | AUTONOMOUS retirement: provable from the landed in-place hU/hR rows (item-5 record: "now provable … and due retirement") |
| MovesT/G1_toyGate.lean:560,780 | toy `mem_realizable` ×2 (BLOCKED-FALSE at the PRE-wave tables) | post-HK-06 re-adjudication (MovesT G1b, the post-wave queue's Q7): the (S-a) re-key changed HistoryCoherent under them |
| MovesT/G1_toyGate.lean:2245,2248 | `twoNodeKcardH`, `toy_v8_wchain` | UNBLOCKED: the missing 2-node artifact now exists (HK23 carriers); autonomous build |

### OM (1)

| file:lines | holds | needs |
|---|---|---|
| OM/Classifier.lean:1255 | `npVertices_stable_of_hull_preserved` — THE banked sorry | off the capstone path; out of goal scope |

### MovesV (15)

| file:lines | holds | needs |
|---|---|---|
| TV_F2.lean:205 | `seam_coherence_exists` — remaining legs tg_val/j_val/jcell_val/jcell_sum + SeamKeys witness (ι-legs PROVED at TV_F2b) | the tg_val leg is BLOCKED on the named Phase-B row `RealizationComplete` (V2_valB:272) = M18's MarkGraft equivalence — an IFK face |
| TV_F3.lean:87 · TV_F4.lean:84 · TV_F5.lean:108 · TV_F6.lean:64 | the ratBurdens seam chain (hdom rows landed by item 11) | behind TV_F2/RealizationComplete |
| TV_G3.lean ×7 | scsSelIdx/memberOf/sel_continuing/cluster_child/… | residuals (a)–(d) recorded in-file (selPos row extension or hp-choice plumbing + member ties); (e) `scs_data_supply_pack` additionally Phase-B |
| V7_livC.lean:83 | `ledgerIV_inst` | waits on EXACTLY ONE adjudication: the `hfin : Finite (Skeleton n)` row (TV_E7-header escalation, NOT in any signed queue) |
| V7_rbC.lean:60 | `ratBurdens_exists` | behind TV_F5 |
| V7_scsData.lean:46 | `scs_data_supply` | behind TV_G3 + the wave-D witness |

### MovesU (7)

| file:lines | holds | needs |
|---|---|---|
| BridgeD19_omAgree.lean:90 | `decCovers_typeOf5_n2` | optional Architecture-B enrichment; also the n=2 `env_tendsto` seam (IB-F7); autonomous probe |
| SlotsG11c_seamAudit.lean:76 | `slot_m4bConst_falsifiable` | needs one realized-prefix Presented instance — forge groundwork landed; autonomous |
| SlotsG2_relFamily.lean:232–255 (4) · SlotsG3_rel3.lean:98 | the round-1 BLOCKED formulations | dead vocabulary wearing live names now that D-SC G16/G17/G18 are filled — quarantine-with-record disposition (the old Q14), needs naming |

### HC2 (2)

| file:lines | holds | needs |
|---|---|---|
| U17a_liftSwap.lean:57 | `lift_swap` | autonomous-HARD; rides the RE-KEYED `StageTransHyp` (Q9 rode the HK-06 wave — binder text unchanged, Prop repaired) |
| U26_fiberWelldef.lean:39 | `class_fiber_welldef` | autonomous-hard; DEFERRABLE (D15 carries `hwd`) |

### HC1 (6)

| file:lines | holds | needs |
|---|---|---|
| C6_alphabetCard.lean:129 | conjunct-2 ⟸ leg (cleanThreshold → fullness) of the REPAIRED statement | the CL-05 counting obligation (CI-1..CI-4, named in-file); believed TRUE; autonomous-hard |
| CL04_addrDichotomy.lean:190 | `CL04_dichotomy_probe` (banked; targets display (4)'s believed-FALSE ⟸ leg) | disposition pends CL-05 |
| V9_K1nonrec.lean:2606,2617,2661,2672 | the HK-06 honest reopening: e·g ≥ 2 steep legs ×2 + i=0 corners ×2 (`V9_K1nonrec`/`V9_E1box_nonrec`, statements byte-unchanged) | HK-52/HK-11a/b transport under the NEW keying (BP2 post-wave queue: HK-12 → HK-52 → HK-11a/b/c; corner truth flagged RE-ADJUDICATION-SUSPECT — the ν₁.e-stretch). Downstream K1/U20/U22 consumers honestly carry sorryAx (outside the root census) |

## 2. THE HYPOTHESIS-ROW SWEEP (theoremU + theoremU_fired at HEAD)

Statuses: PROVED · DERIVED · DISCHARGED-AT-n2 · CARRIER-DESIGNED ·
REFUTED-AS-TYPED (fence event, repair adjudicated, awaiting naming) · OPEN-MATH ·
LIT-AXIOM (declared/audited) · LIT-AXIOM-ELIGIBLE.

### 2.1 `theoremU` (U10_theoremU.lean:104) — the signature surface

| premise | status at HEAD |
|---|---|
| `hn : 2 ≤ n` | statement-fenced (unused; recorded) |
| `C : UCarriers n` | CARRIER-DESIGNED; wave-D instance duty. n-generic suppliers advanced: ctsTable/measuredOf + TablePins + the FULL LedgerIV assembly (TV_E7) PROVED; ratBurdens still behind the F-chain/RealizationComplete |
| `KC : KernelCarriers n C` | CARRIER-DESIGNED; wave-D duty |
| `K7 : Cl7Kernel n KC` | `track_restarts` **REFUTED at the intended instance** (M01 caterpillar family + N7 numerics) — fence event 23 (runCount re-type, Lemma R Lean-provable today; rest of K7 REDUCED to lemmas A–E with L(n) ≤ (n−1)+2⌊log₂n⌋) |
| `S : SolveData n` | PROVED (`bridgeSolve C hdet`, IB-C1) |
| `KT : UpstreamTyped n KC` | see §2.4 |
| 13 bare `Prop` slots | the WAVE-4 BOUNDARY — D-SC carrier layer COMPLETE (G16/G17/G18 filled, G19a-e falsifier-certified); consumed only by the unwritten G13′; jcInvHist's carrier form REFUTED (item 22) |
| `inst : ∀ p hp, UInstance …` | supplied by `mkUInstance` (PROVED) over `BridgeInputs` — CONSTRUCTION-COMPLETE (§2.2) |
| per-p `RegP (inst p hp).D` | (r1)∧(r2) covered: `bridgeRegPCovered_of_diteOK` (item 9 — (r1) via B15b, (r2) via the two-part re-scope, gated by the named `BridgeDiteOK`); failing-prime set PROVED FINITE with exact characterization (M17, `RegPFinite.lean`; `regP_cofinite` hypothesis-free via `detHyp`) |

### 2.2 `UInstance` fields via `mkUInstance` + `BridgeInputs` — CONSTRUCTION-COMPLETE

Every field now has a landed PROVED construction: `bridgeClassifierSpec` (D11),
`bridgeFibers` (D14), `bridgeTreeOf` (D17), `bridgeTreePin` (D18), `bridgeRegData`
(B8), `bridgeRegPin` (B10), **`bridgeZpBridge` (E9, landed 2026-07-31** over
IB-E5 `bridge_zf_pos` + IB-E6 `ramIdx_mul_resDeg_of_irreducible` + IB-E7
`bridge_zf_factor` in `BridgeE567_zfLaws.lean`; footprint = `AX_integralClosure_dvr`
+ core**)**, `bridgeCapstoneLedger` (F3) + `rs4_checksum_bridge` (C4) +
`bridgeSolveSeam` (C5), `bridge_cl7_slice` (F6).  Conditionality riders: (i) the R7
designer sorryAx through the D7/D8 canonical binders — REDUCED to
`RunRealizerExists` (item 13); (ii) `seam.count_tie` — see §2.3 (REFUTED AS TYPED,
fence event 24); (iii) the BK rows below are the ledger CONTENT.

### 2.3 `BridgePre` + `BridgeKernelsCtor` + `BridgeKernels` — the kernel ledger

| row | status at HEAD (tree-verified) |
|---|---|
| `BridgePre.hdet` | named ratified premise; `RegPin.detHyp` derives it from any (REG-p) prime |
| `BridgePre.hStateNe` | named ratified premise (derivation attempt still owed — if it closes, row drops) |
| Ctor.`transfer` | row repaired by item 7 (chart_pin = the N3b digit-slot pin, rfl at the dressed chart; child_local + N₀ ≤ N guard); the KERNEL then **REFUTED at the canonical instance even in corrected form** (M03: Eisenstein family f_N = X²+pᴺ forces B₀ = 0) — fence event 25 (per-site guard repair proposed) |
| BK.`slice_bound` | consumes K7.Tbound — rides fence event 23's K7 re-type; TRACK-COUNT fence otherwise stands |
| BK.`series_tie` | OPEN-MATH, REDUCED (M04) — [3t] solve-side seam; an IFK face |
| BK.`env_tendsto` | M05 PARTIAL-VERIFIED: SEMANTIC exhaustion with explicit rate PROVED at every prime incl. wild (verifier-confirmed core; N1 numerics 20/20); residual = the project-classifier tie (OL2; BNS 3.13 = lit candidate) — THE IFK's K-READ face |
| BK.`vp_sound` | **REFUTED AS BUILT** (M06: (x+p)² class realizes three types, PARI-verified; ns-verdict unsound at finite level) — fence event 26; repair rides event 24's NsFree clause |
| BK.`sibjc` | all three fields PLAUSIBLY FALSE AS TYPED (M07: CellData lacks an adaptedness law) — fence event 27; countermodel gates should compile the (a)-route first |
| BK.`cl6` | n=2 **POSITIVE** (`n2_polyGeomLaws_nonempty` at the item-10 repaired pack; N3 numerics confirm the note's real packs n=2,3,4); general n = OPEN-MATH (M08 intended-pack frame) |
| BK.`cl11_ksub` | **PROVED AT ALL n** (M09 `KsubGeneral.lean`: `ksubM1C1T_of_degCons` from `DegCons.size_sum` alone; keep-and-supply, rows byte-identical) |
| BK.`cl17` | **PROVED at every chain** (item 4: `w17ii_wave4`/`w17ii_pin`, Lean-core; the banked burden retired; N5 numerics 12k configs) |
| BK.`cl19_rep` | **REFUTED AS STATED** (M11 dual: 4 ≠ 0 cross-multiplication at n=2) — queue item 22 (carrier-parameterize `Slot_jcInvHist′`; O1–O3 semantic ladder); theoremU itself SAFE (bare-Prop slot); G13′ GATED |
| seam.`count_tie` | **REFUTED AS TYPED** (M02: bridgeTree lacks the note's ns-free clause; exact-square family scales ×p, PARI-verified) — fence event 24 (add `MovesT.NsFree` to bridgeTree; also rescues canonical_stable + VPSound); then REDUCES to one cylinder law CYL over L1–L3 (IFK faces) |
| `cl13_wf` | DISCHARGED (`menuWFT_holds`) — unchanged |

New sibling laws (item 9, additive, consumer-adoption as named rows): `VerdictDeg`
(vdeg = size·δ; VP-1's E·F = d derived) + `DegConsDelta` (δ-weighted size sum) —
compiled falsifier/witness pairs at cmT/n2T (`BridgeVerdictDeg{,Gate}.lean`).

### 2.4 `UpstreamTyped` (KT) — the nine p-uniform typed rows

| row | status |
|---|---|
| `cl2_route` | OPEN-MATH (X.1b WEIGHT-CHARGE; owner [5]) |
| `cl3_aff/cap/tails/bridge` + `cl3_progress` | OPEN-MATH; M12 verdict: Codex proof UNSOUND (inStratum realization + tree-correspondence gaps = IFK's K-RUN face) BUT the s=2 cap SURVIVES the caterpillar (resultant pays) — supported conjecture (N7); √N form still PROVED (XD4); KE9 linear-form attempt now landed in-tree |
| `cl8_eq2` | M14 CONDITIONAL PROOF + N8 numerics exhaustive (199,723 alphabets, 0 violations) — discharge of the condition = open |
| `cl13_syntax` | expected provable at the V instance; BP3-E ledger now complete (TV_E7) |
| `cl15_align` | LIT-AXIOM-ELIGIBLE, citation PINNED (M15/M16: GMN TAMS 364 Thm 4.18(1) + Defs 4.11/4.12/4.15; ind2 = 2·ind(S) 1548-case verified); `GMNIndex.lean` DRAFT with axiom keyword WITHHELD (zero-witness rule) + AXIOM_FAITHFULNESS entry DRAFT pending guardian audit; residual OL-1..OL-4 recorded |

## 3. THE WAVE-4 BOUNDARY POST-D-SC (the thirteen slots) — CARRIER LAYER COMPLETE

All 13 slots have full sited carrier vocabulary: G16 (4 sited REL laws) + G17
(rel3) + G18 (6 pack rows) FILLED statement-complete (H-phase, Codex-ACCEPTed
targets); G19a/b/c/d/e falsifier certification COMPLETE (value-level falsifiers
incl. rel2b/rel2d/rel2e + rel3).  G13′ (`theoremU_bridged′`, all thirteen at a
`RelCarrierPack` binder) remains UNWRITTEN, gated on **item 22** (jcInvHist is
outright FALSE in carrier form — the unique slot that internalizes its carrier
quantifier).  The slot Props are definitions; their DISCHARGE at a real
RelCarrierPack is wave-D work (HK23 + FORGE-A/B = groundwork).  SlotsG2/G3's 5
blocked-record sorries = dead vocabulary, quarantine disposition pending (§1).

## 4. CLASSIFICATION — THE THREE LISTS

### 4.1 SIGN-OFF-GATED (the complete list; each with dual/compiled evidence on file in lean/notes/openmath/M##_fable.md)

1. **Item 22** — carrier-parameterize `Slot_jcInvHist′ n T CA` (M11 dual
   refutation; Codex concurs on shape + O1–O3 ladder).  GATES G13′.
2. **Item 23** — `K7.track_restarts` re-type to `runCount` (M01: Lean row counts
   population where the note counts track-openings; caterpillar witness + N7).
   Lemma R (runCount ≤ #incT12+#t3+1) Lean-provable today.
3. **Item 24** — add `MovesT.NsFree` to `bridgeTree` (M02: the note's TREE-N
   always carried the ns-free clause).  Rescues count_tie + canonical_stable +
   VPSound; count_tie then reduces to CYL over L1–L3.
4. **Item 25** — `ReadLocality.child_local` per-site guard (M03: refuted at the
   canonical instance even post-item-7; chart_pin leg definitionally TRUE).
5. **Item 26** — `BK.vp_sound` repair (M06) — rides item 24's NsFree (same root
   cause: finite-level ns-verdict unsoundness).
6. **Item 27** — `SibJcRows` adaptedness law on CellData or
   carrier-parameterization (M07; compile the (a)-route countermodel first).
7. **G13′** (`theoremU_bridged′`) — drafts once item 22 lands (all other gate
   conditions DONE: G19a/b, Q5 audit, E-1 via item 4).
8. Standing un-queued adjudications (recorded, not new): the `hfin : Finite
   (Skeleton n)` row on `ledgerIV_inst` (TV_E7-header escalation); the SlotsG2/G3
   quarantine disposition (old Q14); the HK15 e′ ≥ 2 s/t-pin un-guarding (S9
   builder Bézout exposure, synthesis duty); the item-21 Wall A↔B seam supply.

### 4.2 AUTONOMOUS (the next prover round, priority-ordered)

1. **IFK revision 1 + the U6 falsifier probe** (dispatched w9j9p1ci4): fold the 26
   plan-review findings; the M18 Tests A–C falsifier runs FIRST; BNS 3.13 axiom
   draft stripped to the faithful δ+1 clause.  Re-review gate before provers.
2. **`RunRealizerExists` discharge attempt** (post-item-13 shape): interior half
   proved; the (S6b′) monomial clause + the last-node flank countermodel (LIVE
   post-HK23: 3-node extension of H₂ram by a recentering read).
3. **BP2 post-wave queue**: HK-12 → HK-52 → HK-11a/b/c (the 4 reopened V9 legs),
   HK-08 steepness restatement, HK-48(b), HK-25 U1 perimeter (unblocked),
   MovesT G1b re-adjudication (the 2 mem_realizable + the 2 unblocked 2-node
   toys), Blocks L/H/Z.
4. **TV_A2/A3/A4 hoisted-twin retirement** (4 sorries, provable from landed rows).
5. **TV_G3 residuals (a)–(d)** (7 sorries; selPos extension or plumbing).
6. **HC2 remainder**: U17a (HARD, re-keyed StageTransHyp), U26 (deferrable).
7. **C6 CL-05 leg** (CI-1..CI-4 counting identity; then CL04 disposition).
8. **Probes**: BridgeD19 n2 decoder-covering; SlotsG11c m4bConst falsifier (forge
   instance now available).
9. **Lemma R** (fence-23 companion, provable today, no statement change needed
   for the lemma itself).
10. **Wave-D n=2 instance groundwork** (UCarriers/KernelCarriers/RelCarrierPack
    at the HK23/forge carriers) — the census critical path's standing duty.

### 4.3 OPEN-MATH (the honest distance at HEAD)

THE CONVERGENCE (verification round 1, synthesis): M02 (L1–L3), M05 (OL2), M06
(ns-soundness), M12 (inStratum realization), M18 (MarkGraft/RealizationComplete)
ALL reduce to **ONE INSTANCE-FAITHFULNESS KERNEL** — "the built classifier
realizes the semantic OM object" — 4 faces K-DICT/K-READ/K-RUN/K-HALT
(IFK_BLUEPRINT_2026-07-31.md, in revision after Codex REJECT).  BNS 3.13
(LMS JCM 16 (2013), precision δ+1 preserves OM factorizations) anchors K-READ's
precision half as the 5th literature-axiom candidate (faithful clause only).

Residual list (each = IFK face, fence-event successor, or standalone):
1. THE IFK itself (subsumes count_tie's CYL/L1–L3, env_tendsto's OL2, vp_sound's
   semantic half, series_tie, RealizationComplete → unblocks the F-chain).
2. `K7` lemmas A–E at the repaired runCount form (post-item-23).
3. `KT.cl2_route` — X.1b WEIGHT-CHARGE.
4. `KT.cl3_*` — X.2 linear rates general n (s=2 cap = supported conjecture).
5. `KT.cl8_eq2` — the M14 condition's discharge.
6. `KT.cl15_align` — the GMN dictionary tie (OL-1..OL-4) beyond the pinned
   citation (axiom declaration awaits guardian audit + a witness).
7. `BK.cl6` at general n (M08 frame).
8. `BK.sibjc` at the repaired (post-27) form — HC-2 ladder.
9. `BK.cl19_rep` at the repaired (post-22) carrier form — O1–O3.
10. Wave-D carrier POPULATION at n=2 ([4] display drafting, [3] exports, Q15).
11. `BridgePre.hStateNe` derivation attempt.
12. The HK-52/HK-11 transport mathematics (the V9 legs' honest content).
13. `RunRealizerExists` (the R7 residue: S6b′ + landing flank).
14. `hfin`/Skeleton finiteness at general n (currently proved n = 1, 3).

Out of goal scope (recorded, not counted): htameFE (directive), OM/Classifier
banked sorry, proving the declared axioms (GMN index, Denef–Igusa cells,
AX-SERRE-DVR — all admissible literature; AX-SERRE-DVR audit PASSED 2026-07-31).

## 5. THE NEW CRITICAL PATH (shortest route to /goal, literature-only conditionality)

1. **Sign-off on fence events 22–27** (one naming pass; every repair shape is
   adjudicated with compiled/dual evidence).  Items 24+26 land together (NsFree);
   23 unlocks K7; 22 unlocks G13′; 25 unlocks the transfer kernel's honest form;
   27 unlocks the sibjc ladder.
2. **IFK revision → re-review → prover dispatch** (the one kernel five open rows
   reduce to; BNS 3.13 declared as the audited literature axiom for K-READ).
   This is where the remaining SEMANTIC distance lives.
3. **Wave-D n=2 instance** (carriers now exist: HK23 ramified history, FORGE-A/B
   stages, the D-SC layer) + **G13′** (post-22) — converts the 13-slot boundary
   and the carrier packs into pinned rows at a real instance.
4. **The BP2 post-wave ladder** (HK-52/HK-11) + **RunRealizerExists** — kills the
   last designer sorryAx and the V9 reopening.
5. **The KT rows** (X.1b, X.2, EQ-2, ALIGN dictionary) — the non-IFK open
   mathematics; each has a live attempt record (M12/M14/M15 fleet notes).
Then theoremU_fired's conditionality = the declared literature axioms + nothing.

## 6. VERIFICATION STATE (for the record)

Full 1053-module sweep GREEN at HEAD (HK-06 wave, exit 0); AxChk_baseline:
zero sorryAx in the census, `montes_unconditional` + `montes_unconditional_w`
Lean-core; the SerreLocalFields block = the one recorded additive change
(item 2), consumers exactly `AX_integralClosure_dvr` + core.  Numerics matrix
(N1–N8) closed with ZERO Fable/Codex/numerics conflicts; the density tie itself
CONFIRMED at deep-wild (5,5).

## DELTA (round 4, 2026-07-31 late)
-11 sorries (TV-A x4, TV-G3 x5, G1 x2); BridgeD19 row closed by countermodel;
CORRECTION: SlotsG2/G3 are NOT file-level dead (live importers: SlotsG16 ->
G2.Slot_rel1, G12b -> G3); the 5 sorried decls remain dead vocabulary IN
PLACE. New queue item 29 (sel_stage row). Real sorry count now ~32.
