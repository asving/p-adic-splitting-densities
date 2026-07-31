# WHOLE-PROOF SYNTHESIS — PASS 2 (2026-07-31)

CHARGE: re-scan after the pass-1 consolidations (all landed; SYN_C1_EXECUTION /
SYN_E0_CONCORDANCE / commit 7749b9e) and the 161-unit prover wave, for the NEXT
compressions. Inputs read this pass: SYNTHESIS_PASS1 (C7/C8 speculatives + the §6
micro-copy residue + N8), SYN_C1/SYN_E0 execution records, BridgeKernels.lean at HEAD
(the row census), MovesT/ReadLocality.lean + MovesU/BridgeN3b_readLocality.lean (the
stalled probe) + MovesU/BridgeD1_treeModelWire.lean (the executed IB-D27 wire),
MovesD/TreeCan.lean (the landed designer round), Kernels/D4R0K/{Tower,L1}.lean (the
proved KB induction), Kernels/KA6b1/KA6b2/KA4c, HC1 D-units, plus greps: BLOCKED
census, real-sorry census (HC1/HC2/Kernels), private-helper duplication stems across
the wave's new files, and the 2026-08 date-skew census.

Verified sorry census at HEAD (real proof sorries, comments excluded), for
calibration: HC1 {C6_alphabetCard, CL01a×3/CL01b×4/CL01c×4 (fenced side-branch
skeletons), CL04, CL10, CL16, CL17, CL20, R6_carrierInstance(stop-record)};
HC2 {HK15×6, U10×5, U17a, U21, U26, U4 — the in-flight HK-06/Block-Z prover
territory}; Kernels {KA4c:114 — the compiled blocked corner}. HC1's carry D-units
D1–D8: ZERO sorries (all proved). KA6b1/KA6b2: ZERO sorries.

════════════════════════════════════════════════════════════════════════════════
## PART 1 — RANKED CANDIDATES

### P2-C1 (TOP, mechanical). THE ONE SWEEP: six dedup families, all private-fence,
### one prover unit

Charge item (a) verified at HEAD and folded into a single plan. Everything below is
`private` (or a new public in a Defs file that shadows nothing) — ZERO statement-fence
events. Estimated net: −700..−950 lines and ~15 files off the drift surface.

**SWEEP-1: the ResVal Stage-engine micro-copies** (the SYN-E0 §6 residue, verified
present this pass; `Moves/ResVal.lean`'s Stage wrappers carry the exact classic
signatures, so each is import + delete + α-re-point):
- `Moves/L5_landTransport_R4.lean` (w_one, w_pow, R_one, R_pow @57–82)
- `Moves/L5_realDomination_R3.lean` (w_one_eq_zero, w_pow_Phi, w_sum_ge @36–52)
- `Moves/L5_recSubst_R4.lean` (R_one', R_pow', w_one', w_neg', w_pow', w_sum_ge @47–114)
- `Moves/L2_slotDecomp_R4.lean` (R_one @55, w_one @148, w_neg @153)
- `Moves/L4_TRANSviii_b_R4.lean` (grep-first: the standard-name pattern found no hits
  this pass — the copies may be differently named or already gone; verify then skip/act)
- `HC1/T3_htChainWeight.lean` (stage_w_one, stage_w_pow @36–40)
- `HC1/T4_slotMinHt.lean` (t4_w_one, t4_w_pow, t4_w_neg @51–63)
- `HC1/T7_alphabetSpan.lean` (stage_w_one @42, stage0_w_neg @423)
- `HC1/S5_childValuation.lean` (w_one @96)
- `HC1/S11a_coreTransport.lean` (w_one', w_neg_one', w_neg', R_one' @46–61)
- `HC1/V2_readResidual.lean` (v2w_one, v2w_neg, v2sum_w_ge @75–91)
- `HC1/K1_vertexPin.lean` (w_one', w_pow', R_one', R_pow' @230–250)
- `HC2/HK05_countermodelGate.lean` (hk05_w_one @121, hk05_w_pow @126) — the SYN-E0
  "concurrent agent, do not touch" hold is LIFTED (HK-05 gate landed, 127f1f9).
Out of scope, verified clean at HEAD: S9c (0 privates post-C4b), S10/V8/V9/V10 (M8
done), HC2/K1_vertexPin (no engine hits).

**SWEEP-2: `eval_algebraMap_div` — now FOUR copies plus an idiom pair** (pass-1 N8
said three; the wave added one): source `MovesS/PowSubstOK.lean:38`; copies
`MovesS/N2PolyGeom.lean:160`, `MovesS/N2Rsh.lean:65` (primed name),
`MovesV/V0_xhds_witness.lean:24`. Plan: hoist ONE public copy into
`MovesS/EvalAtCoe.lean` (the natural home; new name, shadows nothing), delete the
four privates. `MovesS/N2Sigmas.lean:921/929` (n2_okat_div / n2_evalAt_div) is the
adjacent okat/evalAt idiom — same sweep, re-point if statement-identical, else record.

**SWEEP-3: the MovesV denom-closure trio** (the TV_F1 prover's own in-file record —
"third local copy … recorded for a hoist"): `MovesV/Defs.lean:1496/1503`
(denom_dvd_of_add / denom_sum_dvd, private, directly under the public
`gcell_denom_sum`), `MovesV/V5_jrat.lean:37/44` (jrat_*), `MovesV/TV_F1.lean:55/61`
(f1_*). Plan: de-privatize the Defs pair (new public names), delete the four copies.

**SWEEP-4: History extensionality ×4 → 1**: public source
`MovesT/F0_preHalt.lean:28` (`history_ext`); private copies
`MovesT/E5_rootSplit.lean:171` (history_eq_of_nodes_eq), `MovesT/G1_toyGate.lean:414`
(hist_ext), `MovesT/TV_B8.lean:50` (history_ext — the wave's fourth copy; its own
header records the twin). The D14 copy was already deleted (N8 partial execution,
D14_chainCharges:29). Plan: import F0_preHalt, delete three privates.

**SWEEP-5: MovesD E7/E8 pairs** (pass-1 N8, verified): `E7_rankLt.lean:31`
finite_of_monic_natDegree ≈ `E8_rankInj.lean:91` finite_eligible (hoist one into
MovesD/Defs or E7, re-point E8); `E8_rankInj.lean:107` poolSubfield_eq re-proves E3's
subfield identity (E8's as-built header records it — add the E3 import, cite).

**SWEEP-6: duplication the 161-unit wave itself minted** (charge item (d), new):
- `append_one_zero_ne_zero` ×3: Kernels/KC1.lean, KC6.lean, HmcReduction.lean —
  hoist into HmcReduction (the cluster's shared import).
- `hpt_take_append`/`hpt_drop_append` ×3 each: Kernels/KC2b.lean, KC6.lean,
  MovesV/V4_naming.lean — hoist (KC2b/KC6 share HmcReduction; the V4_naming copy
  is cross-corpus — either import or leave with record).
- `length_le_dTotal_succ` ×2: MovesX/XG2d.lean, XD2.lean — hoist into MovesX/Defs.

**Explicit NON-item: HK13R** (`HC2/HK13_bStageCoreP1a.lean:77–540`, ~460 lines
re-deriving U31_gateReadsOf's frozen privates, statements byte-matched). The freeze
rationale stands (U31 is a ratified frozen file); do NOT sweep. RECORD: when the
campaign freeze lifts, de-privatize U31's toolkit and turn HK13R into re-exports —
the byte-match makes it mechanical then.

**Discipline** (the C1/C4 protocol verbatim): verbatim-hoist-then-delete; all public
statements byte-identical (scripted HEAD-vs-worktree signature check); Codex
per-conjunct equivalence pass over the α-renamed deletions (w_one' → ResVal names
etc. — the SharedRecenter Phase-4 lesson); AxChk_baseline census after; full
`lake build` green. One prover unit (SYN2-S1), routine, sequencing-free (no
dependency on any in-flight cluster except: do not touch HC2/HK15/U10 files — the
HK-06/Block-Z provers are concurrently writing there, and none of their files are in
the sweep list).

### P2-C2 (the charge-(c) finding). The ReadLocality kernel NARROWS at the landed
### canTreeModel: three of its four ingredients are now mechanical

The BridgeN3b probe (2026-07-30) STALLED on LEG 1: "bridgeTm is a sorried designer
obligation with no defining equations — the probe premise is counterfactual at
HEAD." That leg is GONE: IB-D27 executed — `bridgeTm p n N := MovesD.canTreeModelN
p n N (bridgePol p)` (BridgeD1_treeModelWire.lean:80–82), and TreeCan's IB-D22/23/24/
25/30 are PROVED (BP1-P8). LEG 3 (the layout mismatch) was already discharged by the
block-interleave dressing (SYN-C2). LEG 2 (interface-generic refutation) is moot at a
concrete model.

At the canonical model the child/mem predicates are `memCan H x = ReadsOf p F n
(dec x) H ∧ Realizable H ∧ pol.IsCanonPres H` (TreeCan.lean:175–177) — and ONLY the
first conjunct mentions the box x. So `BridgeReadLocality.child_local` decomposes:
  (i)  **ReadsOfLocal** — ReadsOf f H depends only on f's coefficient digits below
       the level-N window once the history's threshold is ≤ N. THE one genuine
       kernel; it is the note's Thm 2.1 / D4R.4 AT ITS NATURAL CARRIER (owner
       HC-2/D4R0K, unchanged).
  (ii) canDec truncation-compat: canCoeff/canDec at level M restricted to the first
       n·N digits equals the level-N decode's digits — a mechanical digit-sum lemma
       (canCoeff is literally Σ digit·p^k, TreeCan.lean:83–94).
  (iii) box-freeness of Realizable/IsCanonPres — rfl-genre projections.
And `chart_pin` at the dressed chart is already a compiled gate (BridgeD5).

Units: **SYN2-R1** (routine, ~80 ln): prove (ii) + (iii) as gates at TreeCan.
**SYN2-R2** (routine-plus): derive `BridgeReadLocality` from a stated `ReadsOfLocal`
row + R1 — after which the bridge tower, treeN_stable, StableInputs, and TransferRow
ALL ride one f-side predicate-locality statement. **ADJ-R3** (adjudication, the
actual decision): whether the honesty ledger re-keys the named kernel from the
tower-dressed `ReadLocality` row to `ReadsOfLocal`. Payoff: the eventual HC-2/D4R0K
discharge is done once, at the note-aligned carrier, and is now a WELL-POSED Lean
question (defining equations exist) instead of a hypothesis about an opaque model.
No BridgeKernels row deletes today; the open surface shrinks by strict inclusion.
TIME-SENSITIVE the same way C2 was: D-group consumers are multiplying against the
current row shape.

### P2-C3. Instance-tier discharge probes for two BridgeKernels ledger rows
### (the slice_finite precedent, one tier down)

Charge item (c), remaining rows. Census at HEAD (BridgeKernels.lean): Ctor carries
ONLY `transfer` (slice_finite DELETED — proved 2026-07-30); ledger rows slice_bound
(TRACK-COUNT, permanently fenced), series_tie ([3t]), env_tendsto (hExhaust, fenced),
vp_sound (CL-10/[1]), sibjc (HC-2 measure rows — genuinely heavy, no shortcut found),
cl17 (open by design), cl19_rep ([2b]), and TWO Q6 rows whose own docstrings
anticipate discharge:

**(a) cl11_ksub** — `KsubM1C1T C.T` (DefsCarriers.lean:113) is a FINITE ROSTER CHECK
("a finite roster check at the n = 2 real pack may discharge it there" — Q6's own
record). The n = 2 real table n2T is concrete and MovesS is zero-sorry. Precedent in
the same file: `menuWFT_holds` proved MenuWFT structurally and the cl13_wf row was
DISCHARGED, not carried. Unit **SYN2-K1** (routine, ~40 ln): `ksubM1C1T_n2 :
KsubM1C1T n2T` by fin_cases/decide-genre roster walk. Payoff: at the final n = 2
wiring the row's supply is a theorem; the generic pack keeps the row (p-uniform
shape unchanged — no fence).

**(b) cl6** — `Nonempty (MovesS.PolyGeomLaws C.T C.MS C.RB)`; Q6: "if the S-area
proves it at the real pack, the row moves out." At n2: tcount_deg/scount_deg are
"derivable from degT_le/tg_degT so instantiation is free" (the structure's own
docstring, Defs.lean:411 block); the countT polynomials are concrete (n2_polygeom_data
pins the three (iv)-POLY values); scount_val's cell-count carrier (cellP_count)
landed with N2Carriers. Unit **SYN2-K2** (probe, routine-plus): construct
`Nonempty (PolyGeomLaws n2T n2M n2RB)` with tCount := the evaluated counts.
PERMITTED OUTCOME: BLOCKED with the exact non-integer-valued pool evaluation or
missing cell-count identity — that obstruction record is precisely what Q6 needs.

### P2-C4 (the charge-(b) verdicts). KB L1-induction vs HC1 carry units and the
### KA6b escape-digit head

**(a) HC1 carry units: NOTHING TO SUBSUME — all proved.** D1–D8 (CarryAlg,
digit multiplicativity, D4_carryAdjoinRoot ≅ F[u]/(u^e − z̄)) carry zero sorries at
HEAD. No deletion, no unit. The live risk runs the OTHER way: L1's ExtCarrier block
(Kernels/D4R0K/L1.lean:514–770 — pow/toPoly/ofPoly/zbar_isUnit/anchored_ne_zero) is
already the corpus's SECOND implementation of the residue-tower unit arithmetic
(justified: different carrier, both proved, KB6 deliberately did not consume
carrierField). The unlanded ⚑ seam unit **KB11** (BP4 §4, "the convention seam /
twist lemma", ADJUDICATION) is where the two meet. PROMPT AMENDMENT (SYN2-F3, no
unit): KB11's charge must (i) consume HC1's D4_carryAdjoinRoot / CarryAlg dictionary
rather than mint implementation #3, and (ii) state the ExtCarrier ↔ CarryAlg
dictionary explicitly — this is also C8's landing spot (below).

**(b) KA6b escape-digit head: ALREADY PROVED; L1 supplies the missing seam
mechanism.** `ka6b2_squarefree_exit_of_anchor_le_one` + `ka6b2_cofactor_exit` are
Lean-core at the WindowModel (KA6a gate PASSED, c805b78). The open residue is the
(state,pool) → WindowModel seam — `free_surj` ("the window digits reach every monic
cofactor") is the contested premise. L1's PROVED `slotAssemble_designated` /
`slotAssemble_support` / `slotAssemble_total` + `offP_designated` are EXACTLY the
free-digit surjectivity mechanism at the enum carrier (designated digit tuples are
assembled and read back — independent-reader recovery), and KB6's toPoly/ofPoly_toPoly
convert digit tuples to the degree-<g cofactor coefficients. Unit **SYN2-W1** (probe,
routine-plus, ~100 ln): `WindowModel.ofEnum` at anchored enum-model states — Digit :=
the designated residue tuples, cofactor through toPoly, free_surj from
slotAssemble_total/ofPoly. HONESTY CAVEAT (state in the unit header): WindowModel is
trivially instantiable by subtype choice; ofEnum's value is that its Digit IS the
model's real digit read, so after it lands the ONLY remaining KA6b2 seam content is
the enum ↔ real-table tie — which is KB11's dictionary. One seam instead of two.

### P2-C5. The date-skew records pass (fold-in list, comment-only edits)

The "T RE-RATIFICATION 2026-08-01" stamp is clock skew — true date 2026-07-29, per
the correction precedent already in-file at MovesT/E5_rootSplit.lean:339 ("the record
originally read 2026-08-01 from clock skew") and DefsCarriers.lean:103. Fold into ONE
records pass (comment-only; zero fence risk; annotate "date corrected 2026-07-31,
true date 2026-07-29" rather than silently rewriting):
- lean/LeanUrat/MovesT/Defs.lean (16 hits) · G1_toyGate.lean (6) · E8_treeExp.lean
  (4) · E11_treeN.lean (3) · D12_packages.lean (2) · S2_sibFalse.lean, E6_segStep.lean,
  E3_jcSingle.lean, E10_perShape.lean, D2_eligGate.lean (1 each)
- lean/LeanUrat/MovesU/DefsLedger.lean (1)
- notes: RATIFY_ROUND4_2026-08-01.md + RATIFY_ROUND5_V_2026-08-01.md — the skew is in
  the FILENAMES; recommend an in-file header correction line, NOT a rename (link rot:
  both are cited from MOVESU_RATIFICATION_ROUNDS/GOLF_CAMPAIGN/BP4). In-text skewed
  cites to fix alongside: GOLF_CAMPAIGN_2026-07-30.md,
  LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md, BRIDGE_BP4_KERNELS_2026-07-30.md (the
  pass-1 N6 item), MOVESU_RATIFICATION_ROUNDS_2026-07-30.md.
- E5_rootSplit.lean and DefsCarriers.lean are ALREADY corrected — the template.

### P2-C6. Small findings (no ranking, orchestrator FYI)

- **KA4c blocked corner** (Kernels/KA4c.lean:99–114, the one Kernels sorry): the
  nsIdx-empty leg needs `frac ∅ = 0`, underivable at the XCtx interface (compiled
  countermodel frac ≡ 1 recorded in-file). Three repair options recorded; (iii)
  `Nonempty C.nsIdx` on the statement or (ii) `2 ≤ n` + discZero anchor are both
  cheap adjudications; consumers are unaffected either way. Adjudicate, don't prove.
- **C7 (finite-state transfer triple)**: stays SPECULATIVE — the BP3 E/F/G seam that
  landed is the SAME seam pass 1 anticipated, not a second one; the revisit trigger
  has not fired.
- **C8 (carry algebra D = F[u]/(u^e − z̄))**: still blocked on the B2-FINAL rewrite
  (pass-8 rejection stands). The Lean landing surface GREW this wave (D-units + L1
  ExtCarrier both proved); fold the KB11 dictionary (P2-C4a) into the standing
  "write B2-FINAL TO the carry-algebra vocabulary" charge.
- **BLOCKED census at HEAD** (grep, MovesU/Bridge* + Kernels): BridgeB2_stateNe
  (derivation attempt BLOCKED as designed — HStateNe stays a BridgePre row),
  BridgeE12 (adjudication row, by design), BridgeRosterPins IB-B15a (in-flight task
  #91), KA4c (above), KD7 (interface blockage, recorded). None is a synthesis target.
- **HK15/U10 files are hot** (HK-06 wave + Block Z provers in flight) — the sweep
  unit must not touch HC2/HK15_gateChildCarrier.lean or HC2/U10_zcStep.lean.

════════════════════════════════════════════════════════════════════════════════
## PART 2 — RECOMMENDED EXECUTION ORDER

1. **SYN2-S1** (the six-family sweep) — one routine prover unit, no dependencies;
   run now. Codex per-conjunct pass + AxChk + scripted signature fence, per protocol.
2. **SYN2-R1/R2 + ADJ-R3** (ReadLocality narrowing) — R1 immediately (pure gates);
   ADJ-R3 at the next adjudication batch; R2 behind it. Time-sensitive.
3. **SYN2-K1** (cl11_ksub n=2 roster check) — cheap, immediate. **SYN2-K2** (cl6
   PolyGeomLaws witness probe) — behind the in-flight BP3-E cluster (measuredOf
   territory is adjacent; avoid file contention on MovesS consumers).
4. **SYN2-W1** (WindowModel.ofEnum) + **SYN2-F3** (KB11 charge amendment) — W1 any
   time; F3 is a one-paragraph blueprint edit, do at the KB11 adjudication.
5. **P2-C5 records pass** — batch with the next MANIFEST/records commit.

END OF PASS 2.

════════════════════════════════════════════════════════════════════════════════
## ADDENDUM — EXECUTION STATUS AT HEAD (2026-07-31, post-report re-scan)

Recorded so this file stays accurate; outcomes live in the P2-C3 probe record
(commit 62f4f7d) and the sign-off-queue commits (4671648/f74ef9c).

- **SYN2-K1 EXECUTED — DISCHARGED**: `ksubM1C1T_n2 : KsubM1C1T n2T` PROVED
  (MovesU/SynK1_ksubN2.lean, Lean-core roster walk). Generic row KEPT per the
  §P2-C3(a) payoff line; final n=2 wiring supplies it by theorem.
- **SYN2-K2 EXECUTED — the PERMITTED OUTCOME fired**: `n2_polyGeomLaws_isEmpty :
  IsEmpty (PolyGeomLaws n2T n2M n2RB)` COMPILED (MovesU/SynK2_cl6N2.lean).
  scount_val fails at the e≠2 roster-PADDING outcomes (pgZero countS=1 vs empty
  cell fiber) — the "missing cell-count identity" arm, value-law-invisible and
  confined to padding. Row does NOT move out; the val-preserving
  `pgZero.countS := 0` repair is a Q6 sign-off item (definition-change event,
  not executed — boundary decision f74ef9c).
- **SYN2-S1 (six-family sweep): NOT executed** — all listed privates verified
  still present at HEAD. Remains the top routine unit; new-file/delete-private
  work sits on the autonomous frontier.
- **SYN2-R1/R2 + ADJ-R3 (ReadLocality narrowing): NOT executed** — no
  ReadsOfLocal at HEAD; ReadLocality.lean byte-unchanged since SYN-C2. Note the
  ratification-1b ReadLocality fixes are sign-off queue item 7 — R1's mechanical
  gates are frontier-safe, but ADJ-R3 and any row re-key must wait behind that
  queue item.
- **SYN2-W1 (WindowModel.ofEnum): NOT executed** (no ofEnum in Kernels/).
- **SYN2-F3 (KB11 charge amendment): NOT executed** — do at the KB11
  adjudication as planned.
- **P2-C5 date-skew records pass: NOT executed** — MovesT/Defs.lean still
  carries the 2026-08-01 stamps; batch with the next records commit.
