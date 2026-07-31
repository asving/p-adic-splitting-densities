# REMAINING-WORK CENSUS (2026-07-31, synthesis pass 3)

**Goal of record** (AUTHORITY UPDATE, BRIDGE_ADJUDICATIONS_2026-07-30.md): `theoremU`
conditional ONLY on literature statements — GMN + Denef–Igusa admissible as cited
axioms; arXiv:2212.00294 EXCLUDED as a source (independence already verified);
htameFE out of the goal's critical path.  This census is the ground truth of
everything between HEAD (bc1dd21, post-D-SC) and that goal.  Method: comment-aware
sorry sweep (block/line comments + strings stripped) over `lean/LeanUrat`; the
capstone hypothesis-row sweep at `MovesU/U10_theoremU.lean` + `DefsLedger.lean` +
`DefsCarriers.lean` + `BridgeKernels.lean` + `BridgeMk.lean` as built; the kernel
ledger verified against the tree (not prose); the D-SC thirteen-slot boundary.

## 0. SUMMARY TABLE (one page)

**Sorry census: 114 real `sorry` tokens in 40 files.**
51 queue-gated · 62 autonomous · 1 banked off-path (OM/Classifier.lean:1255).

| class | count | contents |
|---|---|---|
| QUEUE-GATED sign-off items | 13 items (51 sorries) | the 10 named queue items (BRIDGE_ADJUDICATIONS "CONSOLIDATED SIGN-OFF QUEUE") + D-SC Q12/Q13/Q14 |
| AUTONOMOUS units (provable/executable now) | ~32 units (62 sorries) | TreeCan designer round (R7), BP3-E/F/G remainders, TV_A5 micro-carriers, HC2 P-phase (HK15/U10/U17a/U21/U26), HC1 fills (C6/CL16/CL17/CL20/R6), KA4c/KE9/KE10, D19 n2 probe, G11c falsifier, G19b-half-2 + Q5/Q12 Codex audits, L6_R3 hygiene quarantine |
| OPEN-MATH obligations (no sorry token — hypothesis rows) | 20 | the 9 BridgeKernels rows + count_tie + transfer/ReadLocality + K7 laws + the 9 UpstreamTyped rows (grouped) + ZpBridge laws + wave-D carrier population + per-p (REG-p); 3 are literature-axiom-eligible |

**The capstone chain at HEAD (all compiled, Lean-core):**
`theoremU` (U10, proved) ← `theoremU_fired` (BridgeMk IB-F5, proved) ←
`mkUInstance` (IB-F4, proved) ← `BridgeInputs` (the per-prime constructed-object
bundle — a TRANSCRIPTION DEVICE that must not survive; the post-prover wiring pass
replaces it with the landed constructions).  What stands between HEAD and the goal
is therefore exactly: (a) supply every `BridgeInputs` field from landed
constructions (one field, `bridge : ZpBridge`, has NO construction at HEAD —
group E unwritten, item-2-gated); (b) discharge or literature-cite every row of
`BridgePre` + `BridgeKernelsCtor` + `BridgeKernels` + the seam-carried `count_tie`;
(c) fill + consume the thirteen slot parameters (D-SC carriers designed; G13′ =
Q13); (d) inhabit the p-uniform packs (C, KC, K7, KT) — the wave-D instance; (e)
per-p (REG-p) at every prime claimed.

**Critical path (what closes first, what unlocks what):**
1. **TreeCan designer round (autonomous, highest leverage):** MovesD/TreeCan.lean
   `canPolicy`/`canPolicy_pin` are the R7 designer data-sorries whose `sorryAx`
   rides `bridgePol`/`bridgeTm` into EVERY D-group carrier (`bridgeTree`,
   `bridgeThr`, `bridge_slice_finite`'s statement, …).  Filling them makes the
   whole landed D-group Lean-core-clean.
2. **Item 2 sign-off (ramIdx/resDeg re-point)** unlocks group E (bridgeZpBridge =
   IB-E9 + E5–E7 provers + the IP-1 instance) — the only `BridgeInputs` field with
   no construction — and carries the ratified literature axiom (Serre, Local
   Fields: structure theorem for complete DVRs).
3. **Q12/Q13 + the G16/G17/G18 fills** close the thirteen-slot wave-4 boundary
   (theoremU_bridged′ consumes all thirteen at a `RelCarrierPack` binder).
4. **Items 4/5/7/9/10 + hdom escalation** unblock the in-flight wave provers
   (BP3-E, the E5-hoist ripples, ReadLocality, (r2), the n=2 cl6 wiring).
5. **The wave-D instance** (n = 2 first): inhabit UCarriers/KernelCarriers/
   Cl7Kernel/RelCarrierPack; n=2 instance discharges landed so far: cl11_ksub
   (SynK1), cl13 WF (menuWFT_holds), slice_finite (deleted — proved).
6. **The residual open mathematics** (§4 list): TREE-N count_tie, VP-SOUND,
   SIB/JC-multi, hExhaust general-n, TRACK-COUNT, W17ii(ii), X.1b/X.2 rows,
   EQ-2, ALIGN/GMN dictionary — each either gets a proof from the note or a
   faithfulness-audited literature citation; nothing else remains.

## 1. THE COMMENT-AWARE SORRY SWEEP (114 real tokens, 40 files)

Method: Lean tokenizer-grade strip of `/- -/` (nested), `--`, and string literals;
`\bsorry\b` on the residue.  (Raw grep shows 624 lines; 510 are prose mentions.)
Grouped by file; each row = the statement(s) held + what it needs.

### MovesU — the bridge/slot area (19)

| file:lines | holds | needs |
|---|---|---|
| BridgeD19_omAgree.lean:90 | `decCovers_typeOf5_n2` — the supplied-decoder covering proof at (n=2, p) | OPTIONAL enrichment off the default path (Architecture B, Q1); autonomous n=2 OM-agreement attempt; also the n=2 `env_tendsto` discharge candidate seam (IB-F7) |
| BridgeRosterPins.lean:319 | `bridge_r2_on_activeLocus` — (r2) transport at every active-locus pool | QUEUE ITEM 9 (evidence complete: BridgeB15a_r2Neg compiled; two-part re-scope + VerdictDeg sibling adjudicated, awaiting named sign-off) |
| SlotsG11c_seamAudit.lean:76 | `slot_m4bConst_falsifiable` — the m4bConst compiled falsifier | autonomous H-phase falsifier fill (partial E-phase record in header) |
| SlotsG16_sitedLaws.lean:93,104,114,126 | `SitedSlot_rel2a/b/d/e : Prop := sorry` — the four sited REL law bodies | Q12 (D-SC design ratification) + G19b half 2 + Q5 Codex audit, then R-difficulty fills (targets pre-elaborated at SlotsG19b) |
| SlotsG17_rel3Display.lean:108 | `SitedSlot_rel3 : Prop := sorry` | same gates; empty-`ConsumedDisplayPack` caveat until [4] drafts (Q15) |
| SlotsG18_relPack.lean:80–95 | `RelRow_rel1/2a/2b/2d/2e/3 : Prop := sorry` — the six pack-level rows IB-G13′ feeds theoremU | same gates; consumed only by theoremU_bridged′ (Q13) |
| SlotsG2_relFamily.lean:232–255 | `Slot_rel2a/b/d/e` — the BLOCKED round-1 formulations | Q14: dead vocabulary wearing live names once Q12 lands — quarantine-with-record vs keep (fence event, queued) |
| SlotsG3_rel3.lean:98 | `Slot_rel3` — same blocked record | Q14 |

### MovesD + MovesT (21)

| file:lines | holds | needs |
|---|---|---|
| MovesD/TreeCan.lean:485,492 | `canPolicy` / `canPolicy_pin` — THE canonical-policy designer data (R7) | the scheduled designer round; the `sorryAx` source of every D-group bridge carrier — highest-leverage autonomous item |
| MovesT/E11_treeN.lean:113 | `treeN_stable` — TREE-N decision/realization stability | QUEUE ITEM 7: one ReadLocality kernel (SYN-C2); the as-stated form hides a vacuity (TV-B1 record) — repair queued, then the kernel is open math (§4) |
| MovesT/TV_B7.lean:103 | `treeN_stable_hoisted` — the same row's hoisted face | item 7 (single admission with E11; no second count) |
| MovesT/E5_rootSplit.lean:352 | `fiber_root_split` internal (U)+(R) leg | QUEUE ITEM 5 (E5 hoist to named hU/hR hypotheses, ratified BP3 Q1) |
| MovesT/TV_A2.lean:81 | `fiber_root_split_hoisted` | item 5 execution + prover |
| MovesT/TV_A3.lean:81,117 | `treeExp_hoisted`, `perShape_law_hoisted` (ripple 1) | item 5 ripples |
| MovesT/TV_A4.lean:79 | `treeN_hoisted` (ripple 2) | item 5 ripples |
| MovesT/TV_A5a.lean:62,71,72,73,89,100 | the n=1 childless micro-`CellAssign` instance (6) | autonomous prover round (REV 2 finding 12 split) |
| MovesT/TV_A5b.lean:59,81 | stray-factor probes (2) | autonomous probes |
| MovesT/G1_toyGate.lean:563,783,2248,2251 | toy `mem_realizable` ×2, `twoNodeKcardH`, `toy_v8_wchain` | QUEUE ITEM 3 (task #44 HK-06 HistoryCoherent wave; two recorded BLOCKED-FALSE at the pinned tables; HK-05 GREEN, HK-21/22 staged next) |

### Moves + OM + MovesX + Kernels (5)

| file:lines | holds | needs |
|---|---|---|
| Moves/L6_moveReduceCommute_R3.lean:82 | the fenced manifest statement, FALSE at M=0 (machine-checked); superseded by R4 (sorry-free) | hygiene quarantine (BP5 Q-8 pre-authorized class); do-not-import header already in place |
| OM/Classifier.lean:1255 | `npVertices_stable_of_hull_preserved` — THE one banked sorry | off the capstone path; out of goal scope (do not count against theoremU) |
| MovesX/KE9.lean:69 | `x2Progress_of_pricing` — X2ProgressP linear form | autonomous ATTEMPT, lowest priority (√N form PROVED at XD4; but KT.cl3_progress consumes the linear Prop — see §4) |
| MovesX/KE10.lean:61 | `sharpeningAudit` — the BP4 area exit table | record unit; fills at area exit |
| Kernels/KA4c.lean:114 | `ka4c_nsFiberUnion_null` — the ROUTE-E0 drain seam | autonomous ATTEMPT; `DrainIdent` typed up front, named-hypothesis fallback pre-declared (R10) |

### MovesV — BP3 wave (36)

| file:lines | holds | needs |
|---|---|---|
| TV_E6.lean:175 | `measuredOf_comp_once` (LedgerIV group 9) | ESCALATION (new): BLOCKED on the `hdom : EntDomOrder0 V` named-hypothesis row addition — statement change, orchestrator/Asvin ratification (V7_rbB/V3_initrat precedent); prover record 2026-07-30 in file |
| TV_E7.lean:71 | `ledgerIV_inst_assembly` — the (T,M) LedgerIV assembly | blocks on TV_E6's hdom; ALL other LedgerIV fields PROVED at (ctsTable, measuredOf) per the in-file record |
| TV_E8.lean:42,55 | `mcCP`, `measuredOf_nonvacuity_gate` | autonomous (BP3-E in-flight, task #81) |
| TV_F2.lean:192 · TV_F3.lean:87 · TV_F4.lean:84 · TV_F5.lean:96 · TV_F6.lean:53 | the ratBurdens seam chain: `seam_coherence_exists`/`seam_degree_exists`/`seam_cell_exists`/`ratBurdens_exists_pack`/`measured_seam` | autonomous prover remainder (NOTE: task #80 is marked completed but these stand at HEAD — status drift, see escalations) |
| TV_G1.lean:77,92 · TV_G2.lean:30–92 (8) · TV_G3.lean:40–106 (7) | the SCSData supply cluster (gate TV-G1 first) | autonomous (gate-first protocol) |
| TV_H1b.lean:86–125 (6) | the W17ii clause-(ii) countermodel assembly (`negChain`, `w17ii_false`, …) | QUEUE ITEM 4 (W17ii field repair: census fields + shevt_disj; sealed prediction = countermodel compiles) |
| V7_livC.lean:66 | `ledgerIV_inst` (V7-6c assembly) | same hdom escalation as TV_E6/E7 |
| V7_rbC.lean:52 | `ratBurdens_exists` | consumes TV_F5 — autonomous after F-chain |
| V7_scsData.lean:46 | `scs_data_supply` | consumes TV_G3 — autonomous after G-chain |
| V7_w17ii.lean:48 | `w17ii_wave4` — THE banked W17ii clause (ii), [3t]-owned | item 4 repair first; then open math (§4 row cl17) |

### HC2 — the CL-10/ℤ_p kernel area (15)

| file:lines | holds | needs |
|---|---|---|
| HK15_gateChildCarrier.lean:85–136 (6) | the gate child carrier σ₁ (Φ̂ = U31's landing key; S9 constructor data) | autonomous P-phase (routine, ~60 lines est.; S9 shared builder landed at C4b) |
| U10_zcStep.lean:50,71,126,142,161 (5) | `zc_step` + its four pre-split legs (C.1.5 per-step conditional exactness) | autonomous-HARD ×4 (the pre-declared escalation-risk center; stuck legs become zcSeed laws via D5's fence, never silent axioms) |
| U17a_liftSwap.lean:38 | `lift_swap` (D.10 lift independence at stage reconstruction) | autonomous-HARD; rides the named `StageTransHyp` |
| U21_HV.lean:252 | `readsOf_HV` (C.0 identity-pattern lead) | autonomous (medium-hard bookkeeping post-N-4) |
| U26_fiberWelldef.lean:26 | `class_fiber_welldef` | autonomous-hard; DEFERRABLE (D15 carries it as `hwd`) |
| U4_freshCover.lean:81 | `levelSet_no_straddle` value-case leftover | ESCALATION (new): NOT PROVABLE AS STATED (value case false on a legal countermodel, dual-confirmed by Codex 2026-07-27) — needs a statement-repair adjudication, not in the 10-item queue |

### HC1 — the BP5 cleanup area (18)

| file:lines | holds | needs |
|---|---|---|
| CL01a:68,73,81 · CL01b:65,71,76,88 · CL01c:78,79,95,106 (11) | the Tshallow shallow-instance construction (base/move/tower + alphabet-deficiency certificate) | QUEUE ITEM 6 evidence chain (CL-06 LSTStmt (i-b) repair, VARIANT A ratified; CL-01/CL-04 reports adjudicated — execution queued) |
| CL04_addrDichotomy.lean:177 | `CL04_dichotomy_probe` | item 6 chain (probe report informs the CL-02 repair) |
| CL10_nclProbe.lean:84 | `CL10_ncl_countermodel_attempt` — believed UNFILLABLE (statement believed false; sealed prediction upheld; CL-12 proves the complement) | standing blocked-false record; eventual quarantine-with-record (BP5 Q-5 class) |
| CL16:66 · CL17:71 | `packE_typ1`/`packE_typ2` (TYP conjuncts at packE) | autonomous fills (CL-14 spine landed) |
| CL20_rel1Vacuity.lean:67 | `rel1_forall_refuted` — the R5 antecedent-vacuity certificate | autonomous (compile the junk-pack refutation; Q-4 adjudicated typed-only-with-record) |
| C6_alphabetCard.lean:63 | `C6_alphabetCard` fullness dichotomy | autonomous (medium) |
| R6_carrierInstance.lean:145 | `R6_carrierInstance` — the δ=1 instantiation deliverable (LST/TYP/DOM legs) | autonomous assembly; rides `TowerRealizable`; jets/counting legs = HC-2's seam (recorded, not claimed) |

## 2. THE HYPOTHESIS-ROW SWEEP (theoremU + theoremU_fired at HEAD)

Every premise/slot of the capstone chain, with per-item status.  Statuses:
PROVED · DERIVED · DISCHARGED-AT-n2 · CARRIER-DESIGNED (awaiting fill/instance) ·
QUEUE-GATED (named item) · OPEN-MATH · LIT-AXIOM-ELIGIBLE.

### 2.1 `theoremU` (U10_theoremU.lean:104) — the signature surface

| premise | type home | status |
|---|---|---|
| `hn : 2 ≤ n` | fidelity binder | statement-fenced (unused by proof body; recorded) |
| `C : UCarriers n` | DefsCarriers (TableShape/MeasuredSide/RatBurdens/DegCons/KmatHyp/ShapeFam/RS4Chain over §S-RESUM) | CARRIER-DESIGNED; instance = wave-D duty; BP3's `ctsTable`/`measuredOf` + `TablePins` + `ratBurdens_exists_pack` (TV_F5, sorried) are the n-generic suppliers in flight |
| `KC : KernelCarriers n C` | DefsLedger:124 (XFamily/XConsts/CtsFamily/SpeciesSyntax/AlphabetData) | CARRIER-DESIGNED; instance = wave-D duty |
| `K7 : Cl7Kernel n KC` | DefsLedger:199 — p-uniform L(n)/D(n)/w*(N)/T(n,N) + `track_restarts`/`zero_gain`/`genuine_bound` | OPEN-MATH (TRACK-COUNT owner [4]; "permanently fenced this campaign" per BridgeKernels slice_bound docstring) |
| `S : SolveData n` | supplied | PROVED — `bridgeSolve C hdet` (IB-C1 landed, BridgeSolve.lean) |
| `KT : UpstreamTyped n KC` | DefsLedger:166, nine rows | see §2.4 |
| 13 bare `Prop` slots | U10:107–109 | the WAVE-4 BOUNDARY — see §3 (post-D-SC status) |
| `inst : ∀ p hp, UInstance …` | DefsLedger:832 | supplied by `mkUInstance` (PROVED) over `BridgeInputs` — see §2.2/§2.3 |
| per-p `RegP (inst p hp).D` | (r1)∧(r2) exact schema | the ONE explicit per-p hypothesis (D5/D8: no claim at failing p); transports landed: `RegPin.detHyp` (r1→DetHyp, PROVED), B15b (r1)-coverage; (r2) transport = QUEUE ITEM 9 |

### 2.2 `UInstance` fields via `mkUInstance` + `BridgeInputs` (BridgeMk.lean)

| field | intended supplier (file-header wiring display) | status |
|---|---|---|
| `X : ClassifierSpec` | `bridgeClassifierSpec` (IB-D11, landed) | PROVED construction; carries `sorryAx` from TreeCan designer data (R7) via `bridgeCanonical` chain |
| `hXbase` (o3_teichmuller) | rfl at D11 (`bridgeClassifierSpec_teichmuller`) | PROVED |
| `F : FiberSeries` | `bridgeFibers` (IB-D14, landed; slice_finite argument = the PROVED `bridge_slice_finite`) | PROVED construction (same R7 conditionality) |
| `seam.treeOf`, `seam.thr_le` | IB-D17 `bridgeTreeOf` (landed) | PROVED construction |
| `seam.count_tie` | the [3t]/TREE-N row — the seam's visible third field | OPEN-MATH (named row per Q7; discharge chain IB-D20/D21 off the default path; candidate = MovesT.treeN at Tpin, blocked behind item 7 + the sibjc kernels) |
| `Tpin : TreePin` | `bridgeTreePin` (IB-D18 at D1/D2/A11/D4/D15/D16/D7/D17, landed) | PROVED construction (R7 conditionality) |
| `D : RegData` | `bridgeRegData` (IB-B8, landed) | PROVED construction (consumes BridgePre.hStateNe) |
| `Dpin : RegPin` | `bridgeRegPin` (IB-B10, BridgeRosterPins.lean, landed) | PROVED construction |
| `bridge : ZpBridge` | IB-E9 `bridgeZpBridge` — **DOES NOT EXIST AT HEAD** | QUEUE ITEM 2 (Q2-gated: E5–E7 zf_pos/zf_factor provers run only after the ramIdx/resDeg re-point; IP-1 instance = BridgeE12 gate, landed as gate only; `bridgeZfType` exists in BridgeZp.lean) |
| `L : CapstoneLedger` | `bridgeCapstoneLedger` (IB-F3, PROVED) from BK rows + seam + `rs4_checksum_bridge` (IB-C4, PROVED) + `bridgeSolveSeam` (IB-C5, PROVED) | assembly PROVED; content = the BK rows below |
| `sibjc`, `cl7_slice` | BK.sibjc, `bridge_cl7_slice` (IB-F6, PROVED projection) | ride the BK rows |

### 2.3 `BridgePre` + `BridgeKernelsCtor` + `BridgeKernels` — the kernel ledger (verified against the tree)

| row | status at HEAD (tree-verified) |
|---|---|
| `BridgePre.hdet` | named ratified premise (Q3); warranted ((r1)'s symbolic face; `RegPin.detHyp` derives it from any (REG-p) prime) |
| `BridgePre.hStateNe` | named ratified premise (Q3); derivation attempt runs FIRST — if it closes, row drops (fence event) |
| Ctor.`transfer` | the pack's SOLE remaining construction-side row.  SYN-C2: `TransferRow` DEMOTED to derived surface — THE kernel is `MovesT.ReadLocality` at the dressed tower (`transferRow_of_readLocality` PROVED, BridgeD5).  Repair of the row's statement = QUEUE ITEM 7; the kernel math = OPEN-MATH |
| ~~Ctor.`slice_finite`~~ | **ROW DELETED 2026-07-30 — VERIFIED**: `BridgeKernelsCtor` carries only `transfer` (BridgeKernels.lean:163); `bridge_slice_finite` is a PROVED theorem (:182, from BridgeD13 `realizedSelf_slice_finite`, Lean-core proof; statement carries R7 sorryAx only) |
| BK.`slice_bound` | OPEN-MATH — CL-7 conclusion at p-uniform `K7.Tbound`; TRACK-COUNT permanently fenced; carried, never discharged this campaign |
| BK.`series_tie` | OPEN-MATH — [3t] solve-side seam (tree-fiber series = chain's measured Rval) |
| BK.`env_tendsto` | OPEN-MATH — hExhaust AT GENERAL n (fenced math, UNIFORMITY_COMPLETION_BLUEPRINT); n=2 candidate = OM `hExhaustP` through the D19 agreement seam (IB-F7, optional; D19's n2 probe sorried, autonomous) |
| BK.`vp_sound` | OPEN-MATH — CL-10/[1] VP + VP-SOUND, the identification kernel of Architecture B |
| BK.`sibjc` | OPEN-MATH — (SIB)/(JC-multi) at the pinned instance; owner HC-2 (the HC2 sorried units U10/U17a/U21/U26 + HK15 are this area's ladder) |
| BK.`cl6` | row KEPT — **VERIFIED**: `SynK2_cl6N2.lean` `n2_polyGeomLaws_isEmpty` COMPILED (as-built n=2 pack REFUTES PolyGeomLaws at the e≠2 padding `pgZero.countS = 1`); `n2_countLaws_block2` proves both count laws at block 2; repair = QUEUE ITEM 10 (`countS := 0`, val-preserving); general-n = OPEN-MATH |
| BK.`cl11_ksub` | row KEPT, **DISCHARGED-AT-n2 — VERIFIED**: `SynK1_ksubN2.lean:49` `ksubM1C1T_n2 : KsubM1C1T n2T` PROVED (Lean-core roster walk); general-n row open |
| BK.`cl17` | OPEN-MATH — W17ii at the chain's carriers; clause (ii) = THE banked burden (V7_w17ii.lean sorry); repair/countermodel = QUEUE ITEM 4 (TV_H1b assembly) |
| BK.`cl19_rep` | OPEN-MATH — [2b] representative invariance (history face = the `jcInvHist` slot) |
| seam.`count_tie` | (listed in §2.2) OPEN-MATH, named row (Q7) |
| `cl13_wf` | DISCHARGED — `menuWFT_holds` PROVED at the real roster (DefsCarriers.lean:129), not carried |

**Verified kernel-wave claims (tree, not prose):** KA6b PROVED — KA6b1.lean
(`ka6b1_card_squarefree_monic` + 6 siblings) and KA6b2.lean (4 exit theorems), 0
sorry.  KB PROVED — KB12.lean (`kb12_trackUniqOn_canonical`), KB13.lean
(`kb13_trackRepOn_canonical`), D4R0K/L1.lean + Tower.lean (KB1–KB8b), all 0 sorry.
KB11 = adjudication seam unit, ratified architecture, NOT yet built (must consume
the HC1 CarryAlg dictionary per P2-C4).  The only sorried Kernels file: KA4c
(ATTEMPT, named-hypothesis fallback pre-declared).

### 2.4 `UpstreamTyped` (KT) — the nine p-uniform typed rows

All nine are HYPOTHESIS rows of theoremU (no sorry tokens); for the goal each
must be proved at the wave-D instance or literature-cited:

| row | content | status |
|---|---|---|
| `cl2_route` | X.1b WEIGHT-CHARGE in X.3(a) route form | OPEN-MATH (owner [5]; XC3/XC4 discharge carriers built) |
| `cl3_aff`/`cl3_cap`/`cl3_tails`/`cl3_bridge` | X.2 progress family | OPEN-MATH (XD2–XD4 carriers built; √N form PROVED at XD4 `x2hypAssembled`) |
| `cl3_progress` | X2ProgressP (linear rates) | OPEN-MATH; KE9 = the sorried autonomous attempt |
| `cl8_eq2` | (EQ-2) alphabet law per prime at AlphabetData | OPEN-MATH (owner [2r]) |
| `cl13_syntax` | CtsmSyntaxRow = Part_Stmt verbatim at CtsFamily | expected provable at the V instance (`ctsmSyntaxRow_iff_part` is the tie); rides the BP3-E ledger work |
| `cl15_align` | X1aAlignP at the certified-increment state | OPEN-MATH; GMN/AX-INDEX cite statement-side (LIT-AXIOM-ELIGIBLE) |

## 3. THE WAVE-4 BOUNDARY POST-D-SC (the thirteen slots)

D-SC (BP1 blueprint §D-SC, 2026-07-31) is the dispatched carrier-layer design; all
seven D-SC modules lake-build green (8567/8571 jobs); nothing imports them yet
("the new Props gate nothing and nothing consumes them" until Q12).

| slot | status post-D-SC |
|---|---|
| rel1 | FILLED (SlotsG2 `Slot_rel1` over the G1 `CInterface`); G11a falsifier audit pending |
| rel2a/rel2b/rel2d/rel2e | CARRIER-DESIGNED (G14 sites + G15 seven data packs, 0 sorry) + sited law bodies E-phase-sorried (G16, 4) — fills behind Q12 + G19b half 2 + Q5 audit; est. R ~10–25 each |
| rel3 | CARRIER-DESIGNED (G17 `RelAssignment`/`ConsumedDisplayPack`, P3 derived-not-free); body sorried (1); empty-pack caveat until [4] populates (Q15) |
| rs0Lump / trackRule / dnLattice / m1m5Echo / x1aDict / m4bConst / jcInvHist | FILLED (G4–G10); falsifier audits G11b/G11c (G11c partial — the m4bConst falsifier sorried, autonomous) |
| pack rows | `RelRow_rel1..rel3` (G18, 6 sorries) — what IB-G13′ (`theoremU_bridged′`, NOT YET WRITTEN) feeds theoremU's six REL parameters; G13′ = Q13, named sign-off (capstone-role warrant) |
| (e4) seam | G15b landed (0 sorry): both first-index candidate readings NAMED under the CF13 fence; future (e)-pass proves one reading from [3]'s tables (item 9(iv) fold-in) |

E-phase sorry count of the boundary: 11 (G16:4, G17:1, G18:6) + the G2/G3
blocked-record 5 (Q14 disposition) — all already counted in §1.

## 4. CLASSIFICATION — THE THREE LISTS

### 4.1 QUEUE-GATED (executes on Asvin's named sign-off; item numbers = BRIDGE_ADJUDICATIONS_2026-07-30.md queue)

1. **Item 1** — chi-at chart guard (KBTotTower/TreeExpNs N=0 repair). No sorries held; unblocks the T-side chart consumers.
2. **Item 2** — ramIdx/resDeg re-point → UNLOCKS ALL OF GROUP E (bridgeZpBridge IB-E9 + E5–E7 + IP-1 wiring; the one missing BridgeInputs field) + declares the Serre complete-DVR literature axiom (Wave-2b, ratified goal-compatible; needs the AXIOM_FAITHFULNESS entry on declaration).
3. **Item 3** — HK-06 HistoryCoherent wave: G1_toyGate 4 sorries (2 BLOCKED-FALSE at pinned tables); HK-21/22 staged.
4. **Item 4** — W17ii field repair: TV_H1b 6 + V7_w17ii 1; discharges/reshapes BK.cl17's instance face.
5. **Item 5** — E5 hoist: E5_rootSplit 1 + TV_A2/A3/A4 4 = 5 sorries retired-or-filled.
6. **Item 6** — CL-06 LSTStmt (i-b) repair VARIANT A: the HC1 CL01a/b/c + CL04 chain (12 sorries).
7. **Item 7** — ReadLocality row fixes (chart_pin → N3b compiled-corrected form + child_local N0≤N guard): E11_treeN 1 + TV_B7 1; then ONE kernel row remains (open math).
8. **Item 8** — P2 de-privatize sweep (six families; mechanical; no sorries).
9. **Item 9** — (r2)-on-activeLocus re-scope: BridgeRosterPins 1 + the VerdictDeg additive sibling + delta-weighted DegCons strengthening ((iii)) — evidence complete, form adjudicated.
10. **Item 10** — cl6 `pgZero.countS := 0` (private def, val-preserving): makes the n=2 wiring's BK.cl6 row instantiable.
11. **Q12/Q13 (D-SC)** — carrier-design ratification + `theoremU_bridged′` (all thirteen at a RelCarrierPack binder): gates the 11 REL fills.
12. **Q14 (D-SC)** — G2/G3 blocked-record quarantine (5 sorries retired as dead vocabulary).
13. **Q15 (D-SC)** — cross-area export duties ledger ([3] tableConv/consumed; [4] display population; wave-D inhabits SiteData/RelAssignment/RelCarrierPack) — sign-off is the ledger entry; the work itself is wave-D/open.

### 4.2 AUTONOMOUS (new-file/fenced-as-is provable NOW — the next prover round, priority-ordered)

1. **MovesD/TreeCan designer round (R7)** — canPolicy/canPolicy_pin (2): kills the sorryAx conditionality of the ENTIRE landed D-group. First.
2. **G19b half 2 + the Q5/Q12 Codex audit** over the D-SC addendum + six files (enables the Q12 adjudication).
3. **BP3-E remainder** — TV_E8 (2) (in-flight, task #81).
4. **BP3-F remainder** — TV_F2–F6 (5) + V7_rbC (1): the ratBurdens seam → `Nonempty (RatBurdens T M)` at the shared witness.
5. **SCS cluster** — TV_G1 gate → TV_G2/G3 (17) + V7_scsData (1).
6. **TV_A5a/A5b** — the n=1 micro-CellAssign instance + stray probes (8).
7. **HC2 P-phase ladder** — HK15 (6, routine); U21 (1); U26 (1, deferrable); U10_zcStep (5, HARD — stuck legs become zcSeed laws per D5 fence); U17a (1, HARD).
8. **HC1 fills** — CL16/CL17 (2), CL20 (1), C6 (1), R6 (1).
9. **Kernels/X attempts** — KA4c (1, DrainIdent construction), KE9 (1, lowest priority), KE10 (1, exit record).
10. **Bridge probes** — BridgeD19 n2 decoder-covering (1, also the n2 env_tendsto seam), SlotsG11c m4bConst falsifier (1).
11. **Hygiene** — Moves/L6_R3 quarantine (1, pre-authorized class); CL10 blocked-false record disposition (1, quarantine-with-record).

### 4.3 OPEN-MATH (the honest distance — no proof route at HEAD; each needs new mathematics at the note level OR a faithfulness-audited literature citation)

1. `seam.count_tie` — TREE-N per-tree fiber count at the real classifier ([3t]; D20/D21 chain designed, off default path).
2. `BK.env_tendsto` — hExhaust at general n (fenced); n=2 candidate via OM hExhaustP/D19.
3. `BK.vp_sound` — VP + VP-SOUND (CL-10/[1]).
4. `BK.sibjc` — (SIB)/(JC-multi) kernels (HC-2 ladder in progress).
5. `BK.slice_bound` — TRACK-COUNT p-uniform T(n,N) (permanently fenced this campaign).
6. `Ctor.transfer` / ReadLocality — the ONE locality kernel (post-item-7 statement).
7. `BK.series_tie` — [3t] solve-side seam.
8. `BK.cl17` — W17ii clause (ii) (banked; post-item-4 shape).
9. `BK.cl19_rep` — [2b] representative invariance.
10. `BK.cl6` at general n (n=2 unblocked by item 10).
11. `BK.cl11_ksub` at general n (n=2 DISCHARGED).
12. `K7 : Cl7Kernel` — explicit L(n)/D(n)/w*(N)/T(n,N) + the three laws (TRACK-COUNT/SQ.0).
13. `KT.cl2_route` — X.1b WEIGHT-CHARGE.
14. `KT.cl3_*` — X.2 at linear rates, general n (√N form proved).
15. `KT.cl8_eq2` — (EQ-2) per prime.
16. `KT.cl15_align` — ALIGN + the GMN index dictionary (LIT-AXIOM-ELIGIBLE: GMN already a declared axiom; the dictionary tie is the open part).
17. `ZpBridge` laws — zf_pos, zf_factor's local-field content, the per-factor e·f=deg pointwise law, IP-1 instance (LIT-AXIOM-ELIGIBLE: classical local field theory; Serre DVR axiom rides item 2).
18. Wave-D carrier POPULATION — inhabit UCarriers/KernelCarriers/RelCarrierPack/SiteData at n=2 first; [4]'s SQ.0–SQ.2 display drafting; [3]'s tableConv/consumed exports (Q15).
19. per-p (REG-p) verification at the primes claimed ((r1) transport landed; (r2) = item 9; the residual pool = IB-B16/B17 record).
20. `BridgePre.hStateNe` — derivation attempt (if it closes, row drops; else stays a warranted named premise).

Out of goal scope (recorded, not counted): htameFE (directive), OM/Classifier
banked sorry (off capstone path), the eventual proving of the GMN + Denef–Igusa
axioms themselves (admissible literature).

## 5. ESCALATIONS (surfaced by this census — not yet in the queue)

1. **hdom row addition** (`hdom : EntDomOrder0 V` on `ledgerIV_inst`/`measuredOf_comp_once`):
   the BP3-E prover is BLOCKED on this statement-change ratification (TV_E6 record,
   2026-07-30); blocks TV_E6/TV_E7/V7_livC (3 sorries). Established genre
   (V7_rbB/V3_initrat carry hdom for the same reason). Propose: add to the queue.
2. **HC2/U4 statement repair** (`levelSet_no_straddle`): not provable as stated —
   value case false on a legal countermodel (dual-confirmed 2026-07-27); needs an
   adjudicated repair; currently in no queue item.
3. **Task-ledger drift**: task #80 (BP3-F TV_F1–F6) is marked completed but TV_F2–F6
   sorries stand at HEAD; the tree is ground truth — re-open or re-scope the task.
4. **Group E does not exist**: `bridgeZpBridge` (IB-E9) + E5–E7 have no files at
   HEAD; `theoremU_fired`'s final wiring cannot close without them — entirely
   behind item 2. Flag the size of this dependency when naming item 2.
5. **`theoremU_bridged′` (IB-G13′) not yet written** — awaits Q12/Q13; it is the
   declaration that converts the 13 True-instantiable slots into carrier-pinned
   rows; until then the conditionality claim of record must keep the U10 wording.

## DELTA (round 3, 2026-07-31)
+16 proved (round 3). canPolicy_pin refuted-compiled (queue item 13); hdom leak
confirmed at TV_F5/F6/rbC/E7 (item 11); iota seam re-point needed (item 14); SCS
row needed (item 15). The §4.2 critical-path head (TreeCan kills D-group sorryAx)
is BLOCKED on item 13 — the critical path now STARTS at the sign-off queue.
Autonomous remainder: the D-SC carrier prover round (11 E-phase sorries, pending
the re-review) + scattered independents; everything else queue-gated or open-math.

## DELTA (D-SC H-phase, 2026-07-31, commit 42285ae)
The 11 carrier slot bodies (G16:4, G17:1, G18:6) are FILLED — statement-complete,
transcribed token-exact from the Codex-ACCEPTed (dsc_review2) displayed targets;
IB-G19b hygiene gate PASS; canonical degenerate falsifiers compiled against the
CANONICAL definitions (SlotsG19d, 7 lemmas, 0 sorry, Lean-core). The 13 reserved
theoremU slots now have their full sited carrier vocabulary. G13'
(theoremU_bridged', ALL THIRTEEN typed) remains gated on: E-1 ratification
(sign-off queue) + IB-G19a value-level falsifiers. The slot Props are DEFINITIONS
(no proof obligations of their own); their DISCHARGE at a real RelCarrierPack is
the wave-D instance work (census critical path), for which the forge round's
ramified Stage is groundwork.

## DELTA (M09 formalized, 2026-07-31, commit 7ffb1da)
BK.cl11_ksub: OPEN-MATH -> PROVED AT ALL n (KsubGeneral.lean:
ksubM1C1T_of_degCons from DegCons.size_sum alone; UCarriers.cl11_ksub_general
supplies both row sites; SynK1 n=2 subsumed, record untouched). First
open-math obligation closed by the dual-agent pipeline (independent identical
proofs). The open-math count drops by one; cl19_rep moved from OPEN-MATH to
REFUTED-AS-STATED (queue item 22 — carrier-parameterization repair awaits
sign-off; G13' gated).
