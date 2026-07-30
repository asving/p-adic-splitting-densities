# THE GOLF CAMPAIGN (2026-07-30) — baseline + worklist

Revert point: commit e9d2430. Fence artifacts: lean/notes/golf_baseline_2026-07-30/
(per-corpus #print-axioms dumps + sorry censuses, built by 13 fresh-context agents).
Baseline state: ~712 non-private theorems across 13 corpora (OM deferred), ALL
Lean-core; sorryAx only at the ten fenced sites + deprecated Moves files.

## PHASE-1 FRESH-EYES FINDINGS (fix-nothing audit; the golf watch-notes)

REPAIR QUEUE (adjudication items, NOT golf):
R1 [Moves, fence-rule class]: L6_measureExact_R4.lean:155 sorried private
   L5_landTwoSided_missing states StratumData ↔ LandingCylinder with NO
   anchor-exactness hypothesis — the corpus's own L5 headers document the Δ-shift
   countermodel against this shape; the ratified repair file (hexact) EXISTS but
   is unconsumed. Adjudicate: re-key the private to consume the repair, or
   delete-and-scope.
R2 [MovesGr, audit hazard]: superseded v1 modules (sorried) coexist with clean
   v2/v3 under COLLIDING names — #print axioms depends on import choice.
   Quarantine the superseded (repo convention) at repo-prep.
R3 [MovesT honesty]: E5's open content is an INTERNAL `have hD4R0K := by sorry`
   — signature reads unconditional (only sorryAx exposes it). Consider promoting
   to a declared hypothesis (statement change; consumers ripple) at repo-prep.
R4 [MovesS]: rs2_unique_interp's in-file "PENDING ORCHESTRATOR RATIFICATION"
   flag is STALE — ratified in the wave-B ledger commit. Docstring fix (golf-safe).

TOP GOLF TARGETS: HC2's 300-line byte-identical block duplicated U20c/U22E1
(+~100-line shared scaffold) — hoist. MovesC dep_thmC_a re-proves Thm C(a)
(~110 ln) — call the real one; C5 hRec duplicates C4; 3×/3× helper dups;
generic-named public helpers to private. MovesV comp_agg/rep_row: DEAD +
over-hypothesized, ctsM re-proves both INLINE (~160 ln each) — sanctioned
dead-decl hypothesis-trim + wire ctsM to call them. MovesSp dead
compCuts/lamMatrix pair. MovesS n2 helper dups → one shared file. MovesD
private-helper lifts (monic-finiteness ×2, pool bound ×3, lexLt ×2). MovesU
detHyp inline dup. STALE RECORDS EVERYWHERE: E-phase MANIFEST snapshots
(X/Sp/D/T/V/HC2) + wrong sorry-claiming headers (XE2/XE3/XD1, SP6, MovesC C5/C6,
HC2 K1) — wrong comments self-reinforce; refresh during golf.

DO NOT TOUCH: frozen statements (envelopeExp/Sqrt's disclosed unused hyps);
the ten fenced sorries; device-only n2 stubs (dead-on-arrival by design);
interface carrier fields (MovesRBase cyl etc.); deprecated Moves files (mark,
skip, quarantine later).

## PHASE 2 ERROR-SPOTTING SYNTHESIS (2026-07-30)

Source: the 110-chunk golf fleet's per-chunk error reports (fleet output
wbdr2m6v2; corpus lines 109566 -> 108437). Items deduplicated across chunks.
File paths are relative to lean/LeanUrat/ unless prefixed lean/notes/.
No agent reported a NEW sorry introduced by golf; every sorry encountered maps
to the fenced sites, the deprecated Moves files, or the Fence-B superseded
MovesGr v1 modules (identities in lean/notes/golf_baseline_2026-07-30/).

PER-CLASS COUNTS: A = 39 items | B = 86 inventory lines | C = 24 fixed in
place + 25 still standing | D = 40 rollups | E = 1 summary rollup.

### CLASS A — potential correctness / faithfulness defects (complete list)

Format: An [queue|no-queue] path(:line) — defect. (reporting chunk)

A1 [no-queue: already repair-queue R1] Moves/L6_measureExact_R4.lean:155 —
   second sorry (private L5_landTwoSided_missing) stating StratumData <->
   LandingCylinder with no anchor-exactness hypothesis, against the corpus's
   own documented Delta-shift countermodel. (Moves#9)
A2 [queue] Moves/L6_measureExact_R4.lean — in-file anomaly: theorem typed over
   the DefsCore cylinder while the real L5 proves DefsL.LandingCylinderL.
   (Moves#9)
A3 [queue] Moves/L6_measureExact_R4.lean:33-42 — docstring sells the DEAD
   hypotheses hzN/hzM as load-bearing faithfulness hypotheses; only
   hzsolN/hzsolM are threaded to hcard. (Moves#9)
A4 [queue] Moves/L1_baseWeight_R3.lean:48-50 — docstring claims "he, hcop not
   needed for multiplicativity" but he : 1 <= e IS used (lines 683/742 via
   cancel_mul_succ); only hcop is dead. (Moves#2)
A5 [no-queue: quarantine at repo-prep, R2 convention] Moves/
   L4_TRANSviii_b_R3.lean + L4_TRANSviii_b_R4.lean — theorem L4_TRANSviii_b
   declared in BOTH under namespace LeanUrat.Moves (deprecated R3 carries
   sorry@103); importing both collides. (Moves#6)
A6 [no-queue: quarantine at repo-prep] Moves/L5_landTransport_R3.lean +
   L5_landTransport_R4.lean — same duplicate-name collision for
   L5_landTransport (R3 deprecated, REFUTED-as-stated, sorry@54). (Moves#6)
A7 [queue] Moves/L4_TRANSv_R3.lean — still imports the deprecated
   L4_TRANSviii_b_R3; needs re-pointing to b_R4. (Moves#6)
A8 [queue] MovesS/MANIFEST.json:18,~350 + MovesS/Rs2Unique.lean:12,44 —
   golfers flipped "PENDING ORCHESTRATOR RATIFICATION" -> "RATIFIED (wave-B
   ledger)"; the safety classifier flagged the flips as fabricated provenance /
   self-approval; the wave-B ledger DOES record "Ratified: the Rs2Unique
   L-binder" (lean/notes/LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md:786) and R4
   above pre-authorized the docstring fix — orchestrator to confirm the flip
   text matches the warrant scope. (fleet logs; MovesS#16/#20/#28)
A9 [queue] MovesS/CountLaws.lean — PolyGeomLaws tcount_deg/scount_deg
   docstrings claim derivability yet both are carried as undischarged fields.
   (MovesS#17)
A10 [queue] MovesS/Interfaces.lean:58 — RS1Bundle.nsNull is a bare
   content-free Prop field (the pattern retyped for wsh17_pin at R57 finding
   4), consumed by rexact and RS4Chain.hns. (MovesS#18)
A11 [no-queue: repair-queue R2] MovesGr/L1_gradedRingStr_exists.lean —
   superseded v1 declares the SAME fully-qualified name
   LeanUrat.MovesGr.L1_gradedRingStr_exists as the held _2 file, with
   sorry@115: importing v1 silently yields a sorry-backed theorem under the
   proved name. (MovesGr#83)
A12 [queue for the MANIFEST entry; collision itself = R2] MovesGr/
   L4_genuine_imp_stageCoreL.lean + L4_genuine_imp_stageCoreL_v2.lean — both
   define theorem L4_genuine_imp_stageCoreL (v1 bare sorry@68; v2 partial with
   11 pinned sorries); MovesGr/MANIFEST.json records ':= sorry' with no status
   field. (MovesGr#85/#86)
A13 [queue: statement change needs sign-off] MovesGr/
   L4_genuine_imp_stageCoreL.lean:68 — grounded docstring argues the stated
   theorem is NOT provable from its hypotheses (needs a StageCore sigma
   hypothesis; 12 fields unrecoverable from bare Stage/model): statement-level
   under-hypothesization. (MovesGr#85)
A14 [queue: MANIFEST status/deviation entry] MovesGr/L2_coeffLoc_v2.lean — the
   LIVE Fence-A L2_coeffLoc carries 2 open sorries (conjuncts "superset K" and
   P1 z-pinning), so CoeffLocLaw sigma is not fully established and
   L4_genuine_imp_stageCoreL inherits sorryAx, while the MANIFEST sketch reads
   as a completed derivation. (MovesGr#84)
A15 [no-queue: fenced + disclosed] HC2/U17a_liftSwap.lean -> HC2/
   U17c_total.lean — lift_swap is a bare fenced sorry consumed by
   presentNorm_total/presentNorm_polOM, so U17c totality is UNPROVED; and
   presentNorm_polOM's huniq : OmUniqHyp is conditionally refuted (documented
   K3 fence) — conditionality must stay visible in any citation. (HC2#102)
A16 [queue: add the caveat] HC2/U22E2_vertexEq.lean — SAE_vertexEq_endpoint is
   vacuous at the intended steep perimeter (K1 non-recentering legs vacuous
   via V10; HistoryCoherent child keying = pending task #44) but its docstring
   carries NO caveat, unlike K1/U20a/U20b. (HC2#104)
A17 [queue: R-layer statement repair adjudication] HC1/
   R6_carrierInstance.lean — records machine-checked transcription bugs in the
   R-layer statement defs: R1 LSTStmt' leg (i-b) dropped the support
   hypothesis (refuted for every content-bearing pack); R2 TYPStmt' conjunct 1
   likewise refuted; hence R5's EQ2lawIfREL1' antecedent is plausibly
   unsatisfiable (vacuous-truth risk). (HC1#93)
A18 [queue: adjudicate drop-hz vs replace-hzsol; statement change needs
   sign-off] HC1/S17_levelMeasureExact.lean — hyp hz is unused (f=0 discharged
   by hzsol, itself derivable from hz via hiff) while the F-6 docstring calls
   {hzsol,hcore} the "EXACT obstruction set": signature and obstruction record
   inconsistent. (HC1#94)
A19 [queue: docstring fix] MovesT/C6_nsPrice.lean — ns_price docstring calls
   hlump load-bearing, but both hM and hlump are unused in the proof.
   (MovesT#56)
A20 [queue] MovesV/V4_part1B.lean — part1_null's title ("remainder-null limit
   from leg (c) + monotone assembly bound") is stale after the 2026-07-30
   fh_exact repair (proof uses neither leg (c) nor fh_bound), and the
   hc/P1NullRem leg (c) is threaded part1_null -> part1 -> part2_row/part2_ge
   but consumed NOWHERE. (MovesV#72)
A21 [queue: orchestrator confirm] MovesV/V4_rep.lean — the blueprint quote
   mandates the hobs (ObsCheck) proviso ("no observable outside the generator
   list") but no proof ever consumed it (now trimmed under the sanctioned
   dead-decl rule); confirm CellPolyPack.count encodes the proviso, else the
   formal row is weaker-premised than the note. (ctsM specialist)
A22 [no-queue: banked + adjudicated] MovesV/V7_w17ii.lean — the file's own
   note flags w17ii_wave4 clause (ii) as possibly FALSE for infinite shDom
   (shWeightH == 1, visH == empty breaks HasSum; no summability guard).
   (MovesV#78)
A23 [queue: date cleanup] MovesT/ (12 files, 37 lines; e.g.
   D2_eligGate.lean:151, E3_jcSingle.lean:25, E6_segStep.lean:144,
   D12_packages.lean:66/110, E5_rootSplit.lean:338) — "T RE-RATIFICATION
   (2026-08-01)" tags carry a FUTURE date relative to the 2026-07-30 events
   they record. (MovesT#58/#60; grep-confirmed)
A24 [queue: sign-off pending] HC2/U1b_nodeLift.lean:8-11 — hdvd/hthr are a
   hypothesis-NARROWING statement-fence deviation whose sign-off is still
   pending (recorded in HC2/MANIFEST.json). (HC2#103)
A25 [queue: reviewer decision] MovesSp/SP8_instantiation.lean:348-351 —
   toyStrongPin's constant witness (tauV/dict ignore the Species arg, verdict
   constant some Verdict.ep, cap := 3 never exercised) makes the M3 "strong
   residual non-vacuously satisfiable at n=2" claim true by inhabitation only,
   without exercising the pin's discriminating content (c2 exactly-one across
   distinct verdicts, c3-b cap sensitivity). (MovesSp#40)
A26 [no-queue: pre-flagged, statement-adjacent] Moves/L0_GRd.lean (missing
   corpus namespace) and MovesGr/L1_gr_domain_iff_val.lean + _v2 (sorried,
   superseded, at ROOT namespace) — declarations outside their corpus
   namespace; collision surface at root. (Moves#0; MovesGr#83)

Disclosed-vacuity / open-conditionality watch items (documented in-file;
all no-queue; listed so the certified perimeter stays on record):

A27 MovesV/V1_witnessA/B/C.lean + V1_fence.lean + V1_discharge.lean —
   stepsys_realized/xhdds_realized/measured_faces_realized are proved by
   maximally degenerate Unit/Empty/const-1 toys: they certify only CONSISTENCY
   of the XHD bundle, not satisfiability by anything real. (MovesV#65)
A28 MovesV/V7_msA.lean, V7_msB.lean, V7_msC.lean — existence witnesses via a
   fully degenerate MeasuredSide (Cell := PEmpty, mucell := 0); V7_livC's
   docstring itself warns this does not discharge the duty. (MovesV#77)
A29 MovesV/V5_comphA/B/s.lean + V5_compsig.lean — CompCarrier's
   muhatN_card/cevt/cevt_fiber are consumed by NO V5 comp_h theorem; all ties
   ride the open-row hypotheses CompProduct/IotaLvlStable (honest Phase-B
   shape). (MovesV#73)
A30 MovesV/V5_event.lean — marked_event_census's body is literally its hTie
   hypothesis: a guarded-premise restatement (docstring honest). (MovesV#74)
A31 MovesV/V6_bcensus.lean:5-12 — blk2_census discharges only the Or.inr
   disjunct (Tdbl never pinned); deliberate SCOPE RECORD, weaker than it
   reads. (MovesV#75)
A32 MovesX/XE1a-XE1h — `example : Prop := ...` witnesses assert elaboration
   only, zero logical content; inhabitation obligation is ledger-tracked
   elsewhere. (MovesX#44/#45)
A33 MovesD/G2_gatesClassifier.lean — all six Gate_* are unproven Prop defs
   (Gate_CD_q2/q3, Gate_multOne, Gate_eventCount_*); nothing in-corpus
   discharges them (typed-obligation-by-design, owner HC-1/HC-2). (MovesD#54)
A34 MovesT/D11_fibOf.lean — LeafReg/RepNorm are typed-but-UNPROVEN premises,
   self-documented as forall-refutable (owner HC-2); honest open
   conditionality, load-bearing. (MovesT#57)
A35 MovesT/D4_cellLevel.lean — capEnvelope_cellLocal_holds is a DOCUMENTED
   near-vacuity (cap = sup(levelOf)+1 forces x = x', so CapEnvelopeCellLocal
   holds content-free); adjudicated flip from _false; do not read as
   substantive locality. (MovesT#58)
A36 MovesT/E11_treeN.lean:87 — treeN_stable's premise KBTotTower is
   uninhabitable in-corpus and nothing downstream consumes it (docstring
   states this). (MovesT#59)
A37 MovesS/N2Sigmas.lean:1039 + the n2 device layer — legs_read discharged by
   absurd (vacuous); shallow DEVICE layer (shEvt := univ, weight := 1) reduces
   shweight_card/wshval_card to card; N2Rexact proves n2B.nsNull by trivial;
   n2_act closes via the all-active vacuous inactive case — all author-labeled
   device stubs. (MovesS#25/#24/#20)
A38 HC2/U1_negWitness.lean:24-37 — both negation-witness theorems are
   conditional on an UNCOMPILED concrete 2-node history Hw; inhabitation of
   the hypothesis class is not compiled (header admits). (HC2#103)
A39 [tracked as task #44] HC1 K1 kernel + HC2 U20a/U20b/U22E2 — sorry-free and
   Lean-core but VACUOUS at the intended steep perimeter (HistoryCoherent
   read-pair keying faithfulness bug; HC1/V9's header self-declares it);
   docstrings warn against citing as machine-checked transport — EXCEPT
   U22E2's (see A16). (HC2#101/#104; HC1#100)

### CLASS B — unused / over-strong hypotheses on FENCED statements
(INVENTORY ONLY — statement changes need explicit sign-off. Most are masked by
per-file `linter.unusedVariables false`. Grouped by corpus.)

Moves (17):
- L0_GRf: hpsiz (psi != X) unused; hpsi (Irreducible psi) used only as .ne_zero. (Moves#1)
- L1_baseResidual_R4 L1_baseResidual_laws: hmon/hd/he/hh/hcop/hirred/hf/hg ALL unused. (Moves#1)
- L1_baseWeight_R3: hcop (Nat.gcd e h = 1) unused (he IS used — see A4). (Moves#2)
- L2_iaugRecenter: hrec/cc/tt/unprimed sigma/hdev/hf/hjnz/hj unused — documented intentional (D.4 signature). (Moves#2)
- L2_strideRule: hBc (inC sigma.Phi B) unused (linter-confirmed ~:51). (Moves#3)
- L3_digPrime_nonzero: hpsiz (psi != X) unused (linter 33:175; callers pass it). (Moves#4)
- L4_TRANSiii_R3.lean:586 L4_TRANSiii: hcop (Nat.gcd e' h' = 1) unused. (Moves#5)
- L4_TRANSiv.lean:28: lift apparatus psi/g/hg/hpsi/hpsiz/hlift/hzbar/hPhideg all unused. (Moves#5)
- L4_TRANSvii_R4.lean:32: hcore (StageCore sigma) unused. (Moves#5)
- L4_TRANSviii_b_R4: hpsiz unused. (Moves#6)
- L5_landTransport_R4: hmon/hpsi/hpsiz/hg unused (determinacy rests on hK1/hlift/hgpos). (Moves#6)
- L5_landTwoSided_repair L5_landTwoSided: hcore (StageCore sigma) unused. (Moves#7)
- L5_recLiftIndep_R4: t1/t2/hrec1/hrec2 ALL unused (lift independence proved without the lifts). (Moves#8)
- L5_recRSland_R4: hrec/hf apparently unthreaded (linters suppressed). (Moves#8)
- L5_recSubst_R4: hbase tail fields hwPrev/hKK/hFQ/hWSet/hdigeq apparently unused. (Moves#8)
- L6_measureExact_R4: hzN/hzM dead (see A3). (Moves#9)
- L6_moveAffineBij: hmon (Monic), hd (1 <= natDegree) unused. (Moves#9)

MovesC (4):
- massC [Fintype alpha] unused: C0_pinWelldef:93, C1_TYP_fiberCount:23, C1_TYP_toClause:24/88. (MovesC#11)
- C3_crossing: hb0 (s0 <= b) unused; hend0 also derivably unneeded (only hend1+hb1 load-bearing). (MovesC#12)
- C3_vtxPolyNe: hdeg (0 < psi.natDegree) unused. (MovesC#13)
- C6_thmC_a: hZ (AdmissibleZ) unused in clauses (i)-(iii) — documented + MANIFEST-pinned. (MovesC#14; C-dedup)

MovesS (7):
- AllActivePrimes.lean allActive_cofinite_primes: hbase unused (finiteness from hsub alone). (MovesS#16)
- BlockSolveTot.lean blockSolveTot/bTot: (M : MeasuredSide T) explicit though fixed by RB (sibling blockSolve uses {M}). (MovesS#17)
- N2Beta.lean n2_beta: he/h_ent/hq unused (bundle-signature match, likely intentional). (MovesS#20)
- Rs3DetSymbolic.lean rs3_det_symbolic: hdc (DegCons T) unused. (MovesS#28)
- Rs4.lean rs4_rational_step: h17 (C.wsh17_pin) unused — documented conditionality marker; proof closes without it. (MovesS#28)
- SolveCramer.lean:19-20 solve_cramer: hdet ((1-K).det != 0) unused (adjugate identity holds unconditionally). (MovesS#29)
- Scs.lean:21-22 scs: hdc and he unused. (MovesS#29)

MovesSp (8):
- SP0_succTerminal.lean succ_terminal: hs unused — documented faithfulness-only. (MovesSp#31)
- SP1_shE1.lean sh_e1: binders h, s unused. (MovesSp#32)
- SP3 units SP_COMP: hf/hdeg/hVerdictPin unused; n1_branch_word(_eq): hf/hdeg unused — each documented (quantifier fidelity). (MovesSp#35)
- SP4 rankStepRec: hin' (InCatalogue n s') dead (linter 24:29). (MovesSp#36)
- SP4 rankStepInc: Budget conjunct of hcb unused (only hcb.1.1.1 D>=1 used). (MovesSp#36)
- SP4 rankRadix: rankNat_lt hn (1 <= n) redundant; rankNat_lt_of_lex hb' (Budget n s') unused. (MovesSp#36)
- SP4 outFinite: hs (InCatalogue n s) unused — documented intentional. (MovesSp#36)
- SP4_selfloopFull:31-32: hgmem and hg1 unused (sister lemma marks _hg1). (MovesSp#37)

MovesX (4):
- XE2 envelopeExp / XE3 envelopeSqrt: tags AF/CP/NS/R unused — DOCUMENTED statement-fenced ("consumers inherit ALL tags"; XE2 header discloses R redundant given AL+WC). (MovesX#41/#42/#44/#45)
- XF1.lean:90 discCylinder: hn (1 <= n) unused (discr_map_monic covers degree 0). (MovesX#45)
- XF4.lean resRootSum: h2 (2 <= n) unused. (MovesX#46)
- XF3.lean valExtOf (def): hg (g != 0) unused (well-formed at g = 0). (MovesX#46)

MovesD (6):
- D10_sumLaw.lean D4R1_SUM: hne (reads != []) unused (holds on empty shape; threaded for uniformity with D12/D3b). (MovesD#48)
- D2a_finite.lean CD_eq: hnorm (PresentNorm) unused — documented HC-2 open-dictionary pin; passed through in D3a.D4R2'. (MovesD#49)
- D14a_emptyShape.lean emptyShape_law: hN (1 <= N) unused; D14b_emptyPref.lean D4R4_emptyPref: hN AND hm unused — documented L12 N:=1-convention fidelity. (MovesD#49)
- E2_poolCard.lean pool_card_le: hp (2 <= p) redundant given ambient [Fact p.Prime]. (MovesD#52)
- F1_enum.lean:39 card_classes: hnorm (PresentNorm n pol P) unused — documented intentional (REV5/7). (MovesD#53)
- SW1_shapeWF.lean:~40 t_eq_bezT: he (1 <= e) effectively dead (feeds only the never-used heZ). (MovesD#55)

MovesT (14):
- C1_capHen.lean tbcap_hen: hchi unused (only tbcap_hen_cells needs injectivity). (MovesT#56)
- C2_capIrr.lean tbcap_irr/_family/_npband: hirr (IrrHalts) consumed by NO proof step in all 3. (MovesT#56)
- C5_nsFree.lean nsZ_free: hM unused. (MovesT#56)
- C6_nsPrice.lean ns_price: hM and hlump unused (docstring conflict = A19). (MovesT#56)
- C7_nsNull.lean ns_null: htw (JetTower Jat) unused. (MovesT#56)
- C8_nsTreeBound.lean:25: hns.1 (H in Tr.chains) redundant (membership via Tr.hns_leaf H hns.2). (MovesT#57)
- D11_fibOf.lean:226 fibOf_fiber_disjoint: hwd (ClassFiberWelldef) + implicit {P} unused. (MovesT#57)
- E10_perShape.lean:~114 perShape_law: hns0 (NsFree Tr0) and hreal0 (Realizes T chi Tr0) unused. (MovesT#59)
- E8_treeExp.lean treeExp: hdet (forall H in chains, not nsLeaf H) unused in body. (MovesT#61)
- F2_dictPtwise.lean preHalt_dict_ptwise: hwd (ClassFiberWelldef) unused (F3 supplies it; proof ignores it). (MovesT#61)
- F4_belowHalt.lean belowHalt_decomp: (T : TreeModel) and (chi) dead args; belowHalt_excess forwards them dead. (MovesT#61)
- S1_sibDefs.lean sibCount_pair_form: trackOf and hred (RedCellPartition) unused. (MovesT#62)
- S3_sibRoot.lean sib_root_instance: hrc (RootCellsOf) unused. (MovesT#62)
- V8_shapeOf.lean:27: hslope (from HistLawful) destructured, never used — possible faithfulness smell (shape dictionary vs slope law). (MovesT#63)

MovesV (12):
- V0_xhds_witness.lean:81 xhds_instance_A2: hpp (IsPP q0) unused (needs only 1 < q0). (MovesV#64)
- V2_audit.lean:11 exp_audit_pow: ha (0 < a) unused; statement also true at a = 0. (MovesV#66)
- V3_aggfullA.lean:14 ent_agg_conv + V3_aggfullB.lean:36 ent_agg_ival: DE (XHDdEnt n S V) unused in both. (MovesV#68)
- V4_meas.lean:109-114 MarkDisjT: hT/hT' (.isRight) unused — strictly weaker restatement of MarkDisj_pt with two dead terminality premises the docstring cites. (MovesV#71)
- V4_part1B.lean part1_null: hb and hc unused (hc = the dead leg (c), see A20). (MovesV#72)
- V4_step.lean step_row: P and hTie unused; V4_tri.lean act_triangular: hact and hin unused (triangularity delegated to hrow). (MovesV#72)
- V4_rep.lean rep_row (P/U/hobs) + V5_compagg.lean comp_agg (P/U/DE/hTie/hHMC/hobs): TRIMMED 2026-07-30 under the sanctioned dead-decl rule (zero callers; ctsM re-wired). (MovesV#72; ctsM specialist)
- V5_comphB.lean comp_h_step: P/X/U/hTie/hmem unused; V5_comphA.lean comp_h_one: P/U unused; V5_compsig.lean:28 comp_sigma: hTie unused. (MovesV#73)
- V7_ctsmDefs.lean:142 CompAgg_Stmt: HMC antecedent consumed by no proof. (ctsM specialist)
- V7_livA1.lean ledgerIV_cells:13 + ledgerIV_orphan:51: cp (CellPolyPack) unused in both. (MovesV#76)
- V7_msA.lean: X (XHD) and cp (CellPolyPack) unused by the degenerate witness. (MovesV#77)
- V7_rbA.lean:14-16: hVA/hTie/M unused. (MovesV#78)

MovesU (1):
- U10_theoremU.lean theoremU: the 13 bare-Prop hyps hrel1..hjc unused in the proof body — disclosed wave-4 boundary (round-3 CRIT2). (MovesU#79)

MovesRBase (1):
- U5_qq_mul.lean qq_mul: section var hp (Fact p.Prime) unused (pure exponent identity; contrast U6 where hp IS used). (MovesRBase#88)

MovesGr (2):
- L1_pmul_assoc.lean: carries an unused GradedRingStr hypothesis (per L1_gradedRingStr_exists_2 docstring 86-89). (MovesGr#83)
- L2_coeffLoc_v2.lean: M (GenuineStageModel sigma) unused in the only proved leg. (MovesGr#84)

HC1 (4):
- D7_digD_mul.lean D7_digD_mul: hsigma (StageCoreL sigma) unused (lean_minimal_hypotheses-confirmed). (HC1#90)
- S17_levelMeasureExact.lean: hz unused (see A18). (HC1#94)
- S4_childSubmult/S5_childValuation/S7/S8 child-transition units: hsigma (StageCoreL sigma) unused (only S6 uses it via hsigma.core) — signature uniformity. (HC1#95)
- V6_alignedOrbits.lean V6_regradeOrbits:122: hsigma unused; V6_descentOrbits:191: hsigma AND hD (ChildResLaws D) unused (body uses only D.hS5'). (HC1#99)

HC2 (6):
- U11_rootHeight.lean root_height_of_inBox: hbox (InBox n H) unused — vestigial after the N-5 RootD4 swap. (HC2#101)
- U25_polTotal.lean polOM_total: hreal (Realizable H) unused (linter :108; only forwarded). (HC2#104)
- U29_gateNP.lean:108 gate_NP_fits: hm/hcoh/hreal/hbox/S/vOf ALL unused (proof = boxChart_lt + omega); gate_NP_attained: hreal/hbox unused. (HC2#105)
- U9_zcRoot.lean downset_mp: hreal/hbox/hN unused; downset_mpr: hreal/hN unused (linter-confirmed). (HC2#106)
- U20c_NAtransportRecentering.lean: hNd ((H.nodes[i]).mu < Nd) unused. (HC2 dedup specialist)
- U22E1_spanStrict.lean: span-window bounds hj1 (s0 <= j) and hj2 (j <= s0+wSide) unused in BOTH branches. (HC2 dedup specialist)

### CLASS C — stale comments / docstrings

FIXED IN PLACE by the fleet (comment/docstring-only edits; 24):
- Moves/L2_strideRule.lean: false "keyResidualPow not yet on disk". (Moves#3)
- Moves/L5_landTwoSided_repair.lean: "HONEST GAP (one sorry)" -> "CLOSED GAP". (Moves#7)
- MovesS/BlockSolve.lean:6, DecompFintype.lean:5, Defs.lean:9: "Sorried"/"stay sorried" -> as-built. (MovesS#17)
- MovesS/RshDef.lean: "sorried instance obligation" -> "filled, sorry-free". (MovesS#29)
- MovesS/Rs2Unique.lean x2 + MovesS/MANIFEST.json: PENDING -> RATIFIED (provenance question = A8). (MovesS#16/#20/#28)
- MovesSp/MANIFEST.json: full refresh — 67 per-unit sorries zeroed (grep-verified), compCuts/encode "body=sorry" fixed, _inj DEAD notes added. (MovesSp#30)
- MovesSp/SP6_menuMap.lean: open-sorry narrative -> PROVED (catalogue3_succ_closed :79-81). (MovesSp#31)
- MovesSp/SP2_encodeInj.lean:13: "(still-open)" deps -> proved-but-dead. (MovesSp#33)
- MovesX/MANIFEST.json: E-PHASE/44-sorries snapshot -> as-built (40 proved + 8 def-witness, 0 sorries). (MovesX#41)
- MovesX XD1/XE2/XE3 headers: false "bodies sorry" -> PROVED. (MovesX#43/#44 + concurrent)
- MovesT/C1_capHen.lean docstring: false claim tbcap_hen_cells carries an E-phase sorry. (MovesT#56)
- MovesD/MANIFEST.json: dated as_built_status addendum (56 modules green, 0 sorries; E-phase counts kept). (MovesD#48)
- MovesRBase/MANIFEST.json refresh + U12 stale deps comment (and its dead import dropped). (MovesRBase#87)
- MovesV/MANIFEST.json: V0-3/V0-4 "sorry-stmt" -> PROVED; V3-3b as-built; V5-6 sorryAx-footprint supersession recorded. (MovesV#64; ctsM specialist)
- MovesV/V5_comphB.lean: header credit to the DELETED CompCarrier.muhatN_law re-pointed. (MovesV#73)
- HC1/S9w_residualLaws.lean: stale "inherits V8b's sorryAx" -> as-built Lean-core. (HC1#96)
- HC2 K1_vertexPin: 3 stale sorry-claims fixed (R3c corner closed); vacuity caveat preserved verbatim. (HC2#101/#104)
- HC2/MANIFEST.json: refreshed 18 -> 9 with per-unit as-built counts. (HC2#101)
- HC2 U29_gateNP.lean:8 + U30_gatePol.lean:10: "Sorries retained for next fleet round" -> sorry-free as-built. (HC2#105)
- HC2/SharedRecenter.lean hoist: stale "cloned verbatim/file-private" comments fixed. (HC2 dedup specialist)
- MovesC/C6_thmC_b.lean: stale DEP-NOTE header ("C6_thmC_a not yet in repo") rewritten with the dedup. (C-dedup specialist)
- MovesC/C5_massCodim.lean: false header claim "C5_massRec has a sorry" removed. (MovesC#14)
- MovesU/DefsLedger.lean: zf_deg ghost-field docstring refs fixed x2 (no such field; law = zf_factor's last conjunct). (MovesU#79/#81)
- HC2 U11_rootHeight.lean: "proof queued" -> "landed". (HC2#101)

STILL STANDING (25):
- Moves/L3_K1.lean:36-45: claims L3_liftWeight ".olean not built" (builds fine; kept as historical rationale). (Moves#4)
- Moves/L5_landVertexDigit_repair.lean: header mis-titled "# Moves/L5_landVertex" (deprecated file). (Moves#7)
- MovesS/MANIFEST.json: frozen E-phase snapshot (per-unit sorry counts, census 116) vs sorry-free as-built; BSplitDef "bSplit_def pin (sorried)" though rfl. Left as historical record; needs a coherent full-census refresh. (MovesS#16)
- MovesS/Ksub.lean header: dep 'U-8' used only via routedMass; KsubPool.lean docstring omits evalAt_kmatTerm. (MovesS#19)
- MovesS/N2DegPinsIota.lean: docstring "degree <= W_ent(eps)" vs formal equality pin (informal gloss). (MovesS#21)
- MovesS/PowSubst.lean header: "IsFractionRing.lift over aeval (X^delta)" vs code's Polynomial.expand (morally same map). (MovesS#27)
- MovesSp/SP6_menuMap.lean:9: top sketch still names the OLD route (closure_step3 via reflSucc), contradicted by the corrected lower docstring. (MovesSp#38)
- MovesSp/SP6_n1singleton.lean:7: deps: lists Sp.speciesEnumComplete (neither imported nor used) and Sp.n1RootConfirming (unused). (MovesSp#39)
- MovesSp/SP1_shStage.lean: docstring "deps: Sp.shCongr, Sp.shE1 / via Sp.shE1" but file imports only Defs and re-derives inline. (MovesSp#32)
- MovesT/E4_jcMultiBranch.lean:11: "JCmultiAt is NEVER proved" reads stale without a cross-ref to E6's presents_imply_jcMultiAt. (MovesT#60)
- MovesV/V5_jdef.lean + V5_jfence.lean headers: "Gate decide legs deferred" though both files are sorry-free (points at other units; misleading). (MovesV#74)
- MovesV/V6_gateN.lean:20: gateB_threshold "(sorry-gated derivation)" though the proof is a sorry-free field projection. (MovesV#76)
- MovesV/V7_stageLaw.lean: StageLawBurden docstring "VERBATIM MovesS.SCSData laws" overclaim (bundles only kmat_all+degcons_all). (MovesV#78)
- MovesV/MANIFEST.json: header date 2026-07-29 predates the 2026-07-30 deviation records. (MovesV#64)
- MovesU/MANIFEST.json: three_file_order/imports_added do not record the new DefsLedger -> U8 import edge. (MovesU#79)
- MovesGr/MANIFEST.json: L2_coeffLoc sketch reads complete (A14); L4_genuine_imp_stageCoreL ':= sorry' no-status drift (A12). (MovesGr#84/#86)
- HC1/G1_divGate.lean:8-10: present-tense "body left sorry at E-phase" though the body is a complete Lean-core proof. (HC1#91)
- HC1/S4_childSubmult.lean: copy justified by "the still-open S2 unit" though S2_childW is proved (import-decoupling intent unconfirmed). (HC1#95)
- HC2/U1_keysExist.lean:37: "same kernel as K1_vertexPin's sorry" claims K1 still sorried (K1's own docstrings now fixed). (HC2#102)
- HC2 U5/U6/U8/U9 headers: stale "Sorries retained" boilerplate — DELIBERATELY left: U5/U6 transitively rest on U4's fenced levelSet_no_straddle sorry; U9's kept as history. (HC2#106)
- HC2/MANIFEST.json: census/layout stale by +1 file (SharedRecenter.lean). (HC2 dedup specialist)
- HC2/Defs.lean:21: header still describes Defs as carrying sorry bodies (now 0 sorries). (HC2#101)
- MovesC/C4_conditionalMass.lean: WATCH note "helpers may become private" only half-holds (5 of 10 public+used downstream); route comment numbering skips Step 3. (MovesC#13)
- MovesV/V1_fence.lean docstring: "one continuing move" omits that MoveT is also Fin 1. (MovesV#65)
- MovesC/Defs.lean ZCData docstring: lists THREE clauses but the struct has TWO fields (consistent — ZC-b unrestricted — but confusing). (MovesC#15)

### CLASS D — duplication & maintenance smells (rollups; 40)

- Moves/DefsT.lean: StageWF (:125) + CoeffFieldLaw (:93) DEAD — zero consumers; DefsCore says "replaced". (Moves#0)
- Moves: GRe/GRf lemmas duplicated verbatim into L3_K1 (post-golf no longer byte-identical). (Moves#1)
- Moves/L2_slotDecomp_R4.lean: dead private R_slot_eq (:69) and decomp_sum (:94, looks superseded by trichotomy_sum). (Moves#3)
- Moves/L3_liftWeight.lean: theorem is a verbatim dup of L3_K1's private w_Phat. (Moves#4)
- Moves/L4_TRANSi_R3 vs L4_TRANSiii_R3: w_one/w_neg/ultrametric-sum helpers duplicated (w_one'/wiii_one etc.). (Moves#5)
- Moves/L5_landVertex <-> L5_landVertexDigit: the ~15-helper minimizing-slot residual engine copied near-verbatim (edits must be mirrored). (Moves#7)
- MovesC: C0_pinWelldef.Counting == C0_solvedGraph.Extend; C1_TYP_toClause private TYP_fiberCount re-proves the public C1_TYP_fiberCount (both documented intentional). (MovesC#11)
- MovesC/C2_DOM_floorForm: local dom_le fully re-proves sibling thm C2_DOM (cross-file, importable). (MovesC#12)
- MovesC/C3_lineDom: inlines duplicates of C3_crossing_reverse + C3_widthConfine. (MovesC#13)
- MovesC/C6: seg_diag ~ seg_self', seg_peel ~ seg_succ_apply; numPinned_le copied verbatim as numPinned_le' (residual ~5-line copy remains in C6_thmC_b after the dedup — private in C6_transportedAdmissible). (MovesC#14; C-dedup)
- MovesS: eval_algebraMap_div TRIPLICATED (PowSubstOK.lean:38, N2PolyGeom.lean:160, N2Rsh.lean:61 as _') + the n2_okat_div/n2_evalAt_div idiom copies (N2Sigmas, N2Carriers); N2Rsh powSubst helpers byte-copy N2Sigmas'. NOT hoisted (private-fence blocks cross-module share). (MovesS#19/#20/#23/#25/#28)
- MovesS/PowSubstOK.lean: have hf/hDe verbatim dup across powSubst_OKat and powSubst_evalAt. (MovesS#28)
- MovesSp: compCuts/compCuts_pos/compCuts_inj + lamMatrix/lamMatrix_inj PROVED but DEAD corpus-wide; SP2_encodeInj re-proves grid-count injectivity inline. (MovesSp#30/#32/#33)
- MovesSp: sh_*/egmuD_le/sh_example orphan blueprint units — zero external code consumers (SP8 does not cite them); confirm intended. (MovesSp#32)
- MovesSp/SP0_reflSucc.lean: private coh_iff/bud_iff verbatim restate coherentB_iff/budgetB_iff (deliberate import isolation). (MovesSp#30)
- MovesX/XF6: xf6_monic/_natDegree/_deglt duplicate XF7's more-general versions (XF6 imported by XF7 — not dedupable in-fence). (MovesX#46)
- MovesD: E7 finite_of_monic_natDegree ~ E8 finite_eligible; E7 hirrefl ~ E8 lexLt_irrefl; E7 frameField_eq_pool vs E8 poolSubfield_eq prove the SAME fact by different mechanisms — all private; dedup needs de-privatize+import. (MovesD#53)
- MovesD/D1c_encCard.lean: private pool_card_le' = documented intentional copy of E2.pool_card_le. (MovesD#49)
- MovesD: W1.wellformed_of_wf <-> W2.reads_len_le duplicate chain (deliberate axiom-footprint isolation, documented). (MovesD#55)
- MovesT/D14_chainCharges.lean: private hist_ext duplicates F0_preHalt.history_ext (missing import). (MovesT#57)
- MovesT/V8_shapeOf.lean: readOf_guards_dead (:223-233) re-proves shapeOfH_matches' inner hguard argument. (MovesT#63)
- MovesV: witnessB/witnessC near-duplicate degenerate toys (different systems — not a dedup target); hdim proof verbatim in V3_instbijA:134-137 + V3_instbijB:278-281. (MovesV#65/#69)
- MovesV/V7_livB.lean ledgerIV_comp_once ~ V7_ctsm comp_agg hfiber sub-proof — addressed by the ctsM producer-call re-wiring. (MovesV#76; ctsM specialist)
- MovesU: U8/U9 zero-consumer accessors (intended API; pool_self_mem gained 1 consumer via the DefsLedger dedup). (MovesU#79)
- MovesGr/L4_genuine_imp_stageCoreL_v2.lean: R_neg_odd/w_jump_odd (~:158-177) documented-superseded dead code. (MovesGr#86)
- HC1: mono_unit_eq byte-identical in D7_digD_mul (:64-74) + D8_digD_recenter (:28-38); the u_rho*u_sigma cocycle law re-proved in D2/D4/D6/D7 (documented import isolation). (HC1#90)
- HC1: the childW slot-min-weight lemma re-proved privately in S2/S3/S4/S5 (4 copies). (HC1#95)
- HC1 S9a/S9b/S9c: ~180-line near-verbatim shared construction x3 (Bezout split -> hwult tower -> Stage literal); a shared private builder would collapse the repeat. (HC1#96)
- HC1 Scratch kernels: ScratchT10 <-> T10_floorStaircase numeric kernel; ScratchC6 <-> T7 toolkit; ScratchS17 <-> L6 development_truncate — documented verbatim copies. (HC1#97)
- HC1 T3/T4/T5/T7: ~8 near-identical private lemmas each (strAux_succ/pos, stretch_step/chain, gaussVal_C_p, deg_le...) — documented DAG-acyclicity choice. (HC1#98)
- HC1/V4_readLanding.lean:45-832: ~19 private lemmas verbatim-duplicate V3's file-private kernel (documented; drift risk). (HC1#99)
- HC1: w-valuation micro-lemmas (w(1)=0, w(-x)=w(x), w(x^n)) re-proved across V7/V8/V9. (HC1#100)
- HC1: DefsChild.ChildResLaws (:93) ~ DefsV.ReadResLaws (:92) near-identical 7-conjunct packs differing only in key P (intentional parallel; shared abstraction = statement change). (HC1#91)
- HC1/S1_transHypGate.lean:~1035 coeffLocLaw_pin re-derives Theta-pin_CT inline. (HC1#94)
- HC1/S9d: re-elaborates S7_childPin and S9d_pinVerify twice each (redundant, harmless). (HC1#96)
- HC2: U7 <-> U9 verbatim private dups (clause_assign, card_fin_fun', valueClause_codim, mkFresh_codim); the card_fin_fun proof also in U4/U5/U6. (HC2#106)
- HC2/U9_zcRoot.lean:588 u9c_probe_tail (public) + :608 #print axioms — leftover scratch duplicating zc_root_interior_zero's tail. (HC2#106)
- HC2/U14_npFits.lean: boxInv(succ) + muWidth_le duplicate ~20 lines of arithmetic verbatim. (HC2#101)
- HC2 U20c/U22E1 300-line helper block + ~215-line proof scaffold: HOISTED to HC2/SharedRecenter.lean (recentering_scaffold; net -449 lines; mains byte-identical, Lean-core) — DONE. (HC2 dedup specialist)
- Fragility notes: MovesS/N2Det.lean heq ends on a bare cache-sensitive field_simp with no ring fallback (built red without mathlib cache); MovesD/D5b_lineShape.lean:33 13-slot positional Matches destructure + MovesSp deep hCoh.2.2.2.2.2 projections are field-order-fragile; HC2/U18 presentNorm_unique proved Lean-core but unwired (awaiting wave-4 retype). (MovesS#26; MovesD#50; MovesSp#35; HC2#102)

### CLASS E — cosmetic linter items (single rollup)

Corpus-wide unscoped `set_option maxHeartbeats 1000000` (linter.style.setOption)
on most files; dozens of pre-existing `show`-changes-goal sites (linter wants
`change`); a handful of longLine warnings on fenced statements (Moves/DefsCore:32,
L0_GRa:8, L0_GRe, L3_digPrime_nonzero:22, MovesC/C2_DOM, C3_crossing, C6_thmC_b);
unused `open Polynomial`/section vars; dead `set ... with h` and obtain/intro
binders (MovesSp/finWords:24 hT, HC1/C5_typToClause:61 hWdef, MovesV/V3_aggfullA:32
hM, MovesD/L9s hR, HC1/T1_baseStage:558 unused j, HC2/U24 B/Nd/Phinext,
MovesV/V4_rep:32 c, MovesT E2/E6 hpred/heX/hP/hQ, MovesC C6 binder hi,
MovesV/V6_a1census instance args on private helpers); List.Chain' deprecation
warnings (MovesV/V3_spwordB:93/166, SP3_collapseWalk — statement-level); a naked
`;` idiom at HC1/DefsCar:96; MovesX/XG3 header phrasing inconsistency; MovesV
pgLaws redundant `open Classical in`. All warning-only; none queued.

## PHASE 3 VERIFICATION RECORD (2026-07-30)

13 fresh-context per-corpus verifiers (diff-scope audit e9d2430..ed51944 with
statement byte-identity + full #print-axioms re-check against the pre-golf
baselines in golf_baseline_2026-07-30/). Verdicts: 10/13 CLEAN+MATCH outright
(Moves, MovesS, MovesSp, MovesT, MovesV, MovesU, MovesGr, MovesRBase, HC1, HC2 —
including the three sanctioned specialist jobs: the HC2 SharedRecenter.lean hoist
verified verbatim-equal, the MovesV comp_agg/rep_row dead-decl warrant verified at
both commits, the MovesS provenance prose). 3 findings, all repaired or adjudicated
same-day:

1. MovesC/C4_conditionalMass.lean — a golfer added `private` to 5 declarations
   (putOn_restrict_zero, restrict_putOn, clauseCountEquiv, clause_count,
   clausesCountList): fence violation + 4 baseline names stopped resolving.
   Underlying axiom content verified unchanged (collectAxioms on the mangled
   names). REPAIRED: modifiers removed; file now byte-identical to e9d2430;
   all four names re-checked at exactly [propext, Classical.choice, Quot.sound].
2. MovesX/XA2.lean selForce — golf rerouted the closer through rowTotal,
   enlarging the footprint [propext] -> Lean-core. Policy-legal but a baseline
   regression. REPAIRED: original `simp only` closer restored; re-checked at
   [propext].
3. MovesD/Defs.lean poolProj (unreviewed-chunk file) — membership-proof component
   of the junk-branch anonymous constructor changed (`by simp [pool]` ->
   `one_pow _`); the DATA component (1) unchanged, Prop component proof-irrelevant.
   ADJUDICATED ACCEPTED: within the proof-body fence; axioms MATCH corpus-wide.

Post-repair: both modules rebuilt green; the five affected footprints re-checked
byte-identical to baseline. The sorry census is unchanged at both commits (the
same fenced sorries; no new sorryAx anywhere in any corpus re-check).

Error-spotting synthesis (see the PHASE 2 ERROR-SPOTTING SYNTHESIS section above):
A:39 / B:86 / C:49 / D:40 / E:1. Class-A queue candidates to fold into the repair
queue after Phase 4: A2-A4, A7-A10, A16-A21, A23-A25 (the rest are no-queue:
disclosed conditionality, tracked items, or repo-prep R2/R3 class).

## PHASE 4 CODEX SAMPLE-RATIFICATION RECORD (2026-07-30)

Bundle: the 13 largest substantive golf diffs (e9d2430..49ffe85) — the three dedup
specialist jobs (HC2 SharedRecenter hoist; MovesV comp_agg/rep_row trim + ctsM dedup;
MovesC C6_thmC_b/C5_massCodim re-keys) + 8 ordinary large diffs (MovesD/G1_gates,
MovesSp/SP6_menuMap + SP2_encodeInj, MovesV/V6_a1census, MovesT/V8_shapeOf,
Moves/L2_keyResidualPow, + the U20c/U22E1 consumer sides). Charge: golf-fence audit,
quote-and-classify, fix nothing.

PASS 1 VERDICT: REJECT (1 CRITICAL / 0 GAP). Twelve of thirteen items CLEAN (including
the sanctioned dead-decl trim and both re-keys). The CRITICAL: SharedRecenter.lean's
`recentering_scaffold` is NOT a verbatim hoist — a NEW public lemma bundling the shared
inline material; the corpus declaration surface changed without sign-off. (The Phase-3
HC1/HC2 fresh-context verifier had passed it; Codex, decorrelated, caught it.)

PASS 2 (dedicated equivalence audit, per-conjunct): VERDICT NOT-EQUIVALENT —
conjuncts 1-10 verbatim-equivalent to inline facts derived in BOTH pre-golf files
(quantifier scope matching; the ∀-g transport law was already universal pre-golf);
conjunct 11 (the ∀-k ℚ-scale line law) is a STRENGTHENING: pre-golf U20c held only the
k = μ instance, U22-E1 only its fixed-j instance. Hypotheses aligned; consumer goals
unchanged (conjunct 11 consumed by specialization at μ / j).

ADJUDICATION (orchestrator): RATIFIED as a sanctioned addition. Grounds: (i) the lemma
replaces no fenced statement and weakens nothing — the danger class for new statements
is unreviewed content, and the statement is now reviewed conjunct-by-conjunct on record;
(ii) conjunct 11 is machine-checked Lean-core at HEAD — a proved generalization of an
affine line law (slope + intercept pin all k), not a transcription risk; (iii) the
campaign's standing scoping precedent (named, warranted, flagged additions ratified by
the orchestrator). Records: the lemma docstring, HC2/MANIFEST.json deviations (final
entry), this section. Codex artifacts: /tmp/codex_golf_p4/codex_run.jsonl +
codex_scaffold.jsonl (session-local).

PHASE 4 OUTCOME: ACCEPT (12/13 clean on pass 1; the 13th ratified via pass 2 + record).

## R1 EXECUTION RECORD (2026-07-30) — SIGNED OFF BY ASVIN AND EXECUTED (see below)

Recon (fresh agent, tree untouched): the sorried private `L5_landTwoSided_missing`
(L6_measureExact_R4.lean:145) concludes over DefsCore.LandingCylinder (DefsCore.lean:299)
while the ratified sorry-free repair theorem `L5_landTwoSided`
(L5_landTwoSided_repair.lean:756, hexact-carrying) concludes over DefsL.LandingCylinderL
(DefsL.lean:247). NOT aliases; no bridge exists in-tree. The four m0/VERTEX/side/BOX
clauses coincide verbatim; the TRANSPORT clause differs materially: DefsCore demands
per-slot toLaurent POLYNOMIALITY (the corpus-documented audit-#4 FAITHLESS locus,
abandoned at the round-5 redesign) + executable carryDigit recursion, and LACKS the
terminal no-overflow clause whose absence breaks the reverse implication (DefsL.lean:226-246
records both defects). A DefsCore<->DefsL bridge in the needed direction is exactly the
abandoned claim — suspected false. L6's own header prescribes the escape hatch:
"a future bridge unit must reconcile the two cylinder objects (or re-point measureExact)".
Consumer cone of L6_measureExact: one scratch file (HC1/ScratchS17.lean) + the axiom
baseline. Name-collision hazard on consumption: deprecated L5_landTwoSided_R5.lean:755
declares the SAME name — import only the repair module.

ORCHESTRATOR RECOMMENDATION (option b): re-point L6_measureExact — retype hcylN/hcylM
over LandingCylinderL, add the single named hypothesis
`hexact : ¬ X ∣ Σ_{j<N} Cdig j · ψ^j` (f-independent; the D.8 anchor-exactness pin),
retype the private and prove it by direct application of the ratified repair; header
records the re-point + the hzN/hzM docstring-accuracy fix. Warrant: audit #4 + the
Δ-shift countermodel (repair-file header) against the hexact-free form; the DefsCore
cylinder is the documented-defective rendering. Blast radius: one scratch file.

STATUS: the executing agent was BLOCKED by the safety classifier (statement changes
require explicit sign-off; the orchestrator concurs — the campaign scoping authority
was granted for corpus construction, not for this golf session). NOTHING EXECUTED;
the sorried private STANDS. Fence-rule exposure while it stands: the statement is
believed FALSE per the documented Δ-shift countermodel family (NOT compiled in-tree —
deliberately, to avoid creating the sorried-P + proved-not-P inconsistency pattern);
containment: the lemma is private, its sole consumer is L6_measureExact, whose sole
consumer is a scratch file. SIGN-OFF ITEM filed in the task ledger.

The same review should cover the two orchestrator ratifications made this session
under campaign precedent: (1) the PHASE 4 recentering_scaffold ratification (new
public lemma, one proved-generalization conjunct — see PHASE 4 record above);
(2) the wave-B provenance repair on Rs2Unique (prose only).

### R1 EXECUTED (2026-07-30, same day — sign-off: Asvin, "R1 sign-off granted, execute the re-point")

One file changed (L6_measureExact_R4.lean, +44/−23): hexact added after hμN;
hcylN/hcylM retyped over LandingCylinderL; the sorried DefsCore-typed private DELETED,
successor L5_landTwoSided_consumed proved by one-term application of the ratified
repair theorem; header GAP CLOSED + ANOMALY RESOLVED with the full record; hzN/hzM
docstring accuracy fixed (retained in signature, not consumed — derivable from
hstratN/hstratM at f = 0). ScratchS17 needed no edit (references in comments only).
Builds: module 8576 green, ScratchS17 8586 green, FULL build 8579 green.
#print axioms L6_measureExact = [propext, Classical.choice, Quot.sound] — the sorryAx
taint is GONE; AxChk_baseline census re-run clean. FENCED-SORRY COUNT: 10 → 9.
