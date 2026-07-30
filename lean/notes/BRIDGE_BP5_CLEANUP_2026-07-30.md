# BRIDGE BP5 — PERIMETER CLEANUP (blueprint, 2026-07-30)

Area: HC1's two standing sorries (`C6_alphabetCard`, `R6_carrierInstance` post-A17),
the MovesGr disposition (20-sorry census: prove the live units or quarantine the
superseded), and the deprecated-Moves quarantine sweep (the golf ledger's R2/R3
class). Written for the bridge campaign (task #69): every claim below was verified
by reading the named file at HEAD on 2026-07-30; line numbers are HEAD line numbers.

Binding disciplines (verbatim from the campaign charge): statement fence
(statements may gain NAMED warranted hypotheses, flagged for orchestrator
ratification, never silently weakened); countermodel-first (a universal statement
that could be false gets a countermodel-attempt unit that runs BEFORE its prover);
honest sorries (unprovable-as-stated ⇒ repair adjudication, never a forced proof);
Lean 4.31.0 + Mathlib pinned; green records come from `lake build` ONLY (never
`lake env lean` — methodology rule #2, the maxSynthPendingDepth=3 discrepancy).

---

## 1. GOAL

This area contributes NO new clause to `LeanUrat.MovesU.U10_theoremU` (theoremU).
It delivers three things theoremU's trust story needs:

(G-1) **HC1 sorry-closure or honest fencing.** HC1 is the owner corpus for several
of theoremU's named boundary rows (the HC-1/HC-2 bridges in the OPEN SURFACE list,
PROJECT_STATE.md 2026-07-29 update). Its as-built census is exactly TWO proof
sorries (HC1/MANIFEST.json `as_built_2026-07-30`; golf_baseline HC1_axioms.txt
"TOTAL: 2 real sorries"):
  - `lean/LeanUrat/HC1/C6_alphabetCard.lean:63` — statement machine-argued
    FALSE-as-fenced (the ScratchC6 certificates); disposition = statement-repair
    adjudication (Asvin queue Q3), then prove the repaired form.
  - `lean/LeanUrat/HC1/R6_carrierInstance.lean:145` — the sorry the MANIFEST
    records as ":130" (comment drift; the token sits at :145 at HEAD). Blocked
    on the A17 statement-repair adjudication (golf ledger class-A item A17); the
    2026-07-30 verify-2 fold-in inside the file records that the documented
    post-repair assembly now carries ZERO dep-sorries (`C2_TYPa` and
    `T4_slotMinHt` both PROVED Lean-core at HEAD — re-confirmed by this
    blueprint's read: no sorry token in either file; both end in `#print axioms`).
    Deliverable: execute A17, then CLOSE R6 outright via the graded-expansion
    pack (§3.2). This is the area's main mathematical content.

(G-2) **A collision-free declaration surface.** Six superseded MovesGr modules and
four (arguably five) deprecated Moves modules declare the SAME fully-qualified
names as their proved successors, some sorry-backed — so `#print axioms` on a
proved-sounding name depends on which module got imported (golf ledger R2, A5, A6,
A11, A12, A26). Quarantine them to `lean/quarantine/*_2026-07-30.lean.txt` (repo
convention). This is an audit-soundness deliverable for EVERY future census.

(G-3) **MovesGr honest disposition.** After the quarantine, the remaining MovesGr
sorries (13 of the 20-token census) sit in two LIVE partial files that are
FAITHLESS-classified by the standing semantic audit; adjudicate
prove-vs-quarantine per file with the analysis in §3.3.

DONE criterion for the area: HC1 sorry census 2 → 0 (or → explicitly re-fenced by
orchestrator decision at C6), MovesGr sorry census 20 → 0-live (quarantined tokens
do not count; quarantine files are .txt, invisible to lake), Moves deprecated
collisions 0, full `lake build` green, `lake env lean LeanUrat/AxChk_baseline.lean`
footprints byte-identical for every capstone, PROJECT_STATE.md + MANIFESTs updated.

---

## 2. OBJECT INVENTORY (verified by reading at HEAD, 2026-07-30)

### 2.1 HC1 — the C6 cluster

| object | owner file | status at HEAD |
|---|---|---|
| `C6_alphabetCard` (thm) | HC1/C6_alphabetCard.lean:54 | SORRY at :63 (the whole 3-conjunct body) |
| `C6_cardK_bridge` (thm) | HC1/C6_alphabetCard.lean:40 | PROVED Lean-core (`Nat.card K = p^d`, d ≥ 1, via `Tower.hcharF` + `FiniteField.card`) |
| `C6_attain_automatic` | HC1/ScratchC6.lean:321 | PROVED Lean-core: every level-set slot is attainable at every nonzero digit |
| `C6_conjunct2_rhs_always` | HC1/ScratchC6.lean:358 | PROVED: conjunct 2's RHS is a theorem (witness y = 1) |
| `C6_conjunct3_hyp_false` | HC1/ScratchC6.lean:365 | PROVED: conjunct 3's hypothesis refutable outright |
| `C6_forces_unconditional_fullness` | HC1/ScratchC6.lean:374 | PROVED: fenced C6 ⟹ the unconditional fullness claim refuted at shallow heights (CODEX_CONFIRM_D11B; MOVES 2160–2165) |
| `C6_conjunct1_closable` | HC1/ScratchC6.lean:386 | PROVED: conjunct 1 = `(T7_alphabetSpan T b γ).2.2.symm` |
| `T7_alphabetSpan` | HC1/T7_alphabetSpan.lean:670 | PROVED: alphabet = span set ∧ `Finite 𝔸` ∧ `p ^ aDim = Nat.card 𝔸`; also owns `levelSet_finite'` (level sets are finite) |
| `T8_alphabetStep` | HC1/T8_alphabetStep.lean:126 | PROVED: ∃ subgroup A of level-set digit tuples with `BijOn (typComposite) A 𝔸`, additivity on A, `p^aDim = card A`. NOTE: A is a SUBGROUP, not the full tuple space — T8 does NOT give kernel-triviality of typComposite (load-bearing for §3.2's NCL risk) |
| `T9_blockDisjoint` | HC1/T9_blockDisjoint.lean:128 | PROVED: level sets pairwise disjoint ∧ `c ↦ (baseIdx c, c.l)` injective |
| `T12_coordFin` | HC1/T12_coordFin.lean:27 | PROVED: coordinate boxes finite; `levelSet` defeq to its set-builder |

### 2.2 HC1 — the R6 cluster

| object | owner file | status at HEAD |
|---|---|---|
| `R6_carrierInstance` (thm) | HC1/R6_carrierInstance.lean:68 | SORRY at :145. Statement: `∀ T rl, ∃ K : CarrierPackR p, (∀ γ, K.G.Gr γ = T.grQ γ) ∧ LSTStmt' p K ∧ TYPStmt' p K ∧ DOMStmt' p K` |
| `realSlot_offBlock_blind` (private) | R6_carrierInstance.lean:34 | PROVED kernel 2a: the real `slotCoeff b` ignores off-block digits |
| `LSTib_offBlock_pincer` (private) | R6_carrierInstance.lean:51 | PROVED kernel 2b: any off-block-blind pack satisfying current `LSTStmt'` is refuted (DEFECT 1's machine half) |
| `CarrierPackR` (structure, 17 fields) | HC1/R1_LSTStmt.lean:32 | built; fields: `G : GradedCarrierR p`, `Hist Coord Digit` (+`digitAdd`), `kIdx ht blk lvl slotCoeff aDim lines blockEdge interiorEnd window mono floorB` |
| `LSTStmt'` (def) | HC1/R1_LSTStmt.lean:58 | built; leg (i-b) at :61-63 LACKS the support hypothesis — THE A17 defect (display (2) in §3.2) |
| `TYPStmt'` (def) | HC1/R2_TYPStmt.lean:31 | built; conjunct 1 = unconditional additivity of `inγ γ' ∘ slotCoeff H b` in the digit tuple; conjunct 2 = span pricing `card closure = p ^ aDim` |
| `DOMStmt'` (def) | HC1/R3_DOMStmt.lean:26 | built; `∀ H i m b, m < i → b < interiorEnd H i → lines H m .at b ≤ lines H i .at b` — i ranges over ALL ℕ (instance must guard i > K, §3.2 step R6-e) |
| `SecB1Stmt'` (def) | HC1/R4_SecB1Stmt.lean:28 | built; literally TYPStmt' conjunct 1 quantified over (H, b, γ) — same content, no guards |
| `REL1Pack`, `EQ2lawIfREL1'` | HC1/R5_EQ2Pass.lean:29,35 | built; `EQ2lawIfREL1' EQ2law := (∀ K : CarrierPackR p, REL1Pack p K) → EQ2law` — antecedent refutable ⇒ vacuous-truth risk (A17's second half; §3.2 step R6-h) |
| `C1_LST` | HC1/C1_LST.lean:37 | PROVED: legs (i-a)=T3, (i-b)=T4 (WITH `hfin` + `hsupp`), (i-c)=T5, (ii)=T10 step-floor, (iii) arithmetic |
| `C2_TYPa` | HC1/C2_TYPa.lean:606 | PROVED Lean-core (incl. the former conjunct-(b) carry wall): (a) `inGr γ' (slotCoeff b y) = typComposite b γ' (y↾lvl)` under {hfin, block-support, low-height-zero}; (b) `typComposite b γ'` ADDITIVE in the level-set digit tuple |
| `C4_DOM` | HC1/C4_DOM.lean:37 | PROVED: line domination + floor form on the per-i interior, from `rl.steeper`/`rl.vertex_entry` via `MovesC.C2_DOM` |
| `T3_htChainWeight` | HC1/T3_htChainWeight.lean | PROVED: `w_top(mono c) = strTop · ht c` (given `c.MonoNZ`) |
| `T4_slotMinHt` | HC1/T4_slotMinHt.lean:790 | PROVED Lean-core: given `hfin`, `hsupp : ∀ c, y c ≠ 0 → blk c = b`, `hne : slotCoeff b y ≠ 0`: ∃ c₀, `y c₀ ≠ 0 ∧ wQ (slotCoeff b y) = ht c₀ ∧ ∀ c, y c ≠ 0 → ht c₀ ≤ ht c` |
| `T5_levelSetInGamma` | HC1/T5_levelSetInGamma.lean | PROVED: `inGr γ'` depends only on the level-set restriction (under the same guards) |
| `T6_carrierLaws` | HC1/T6_carrierLaws.lean:285 | PROVED: `T.HasSide ∧ T.CarrierLaws` (the four GradedCarrier laws for `(CoeffTop, wQ, inGr, grQ)`) |
| Tower vocabulary | HC1/DefsTower.lean, DefsCar.lean | built, no sorries: `Coord` (l : ℕ, bounded inner slots, unbounded top slot), `ht c = l + Σ slot_r·κ_r`, `κ_k = h_k/(e_k·STR_k)`, `strTop = STR_K·e_K`, `mono`, `blk`, `levelSet`, `digLift`, `slotCoeff` (finsum, junk-0 at infinite support), `typComposite`, `alphabet` (closure of single-slot images), `aDim = Nat.log p card`, `grQ γ = side.grPiece ⌊strTop·γ⌋`, `inGr` (0 off-lattice/below-weight), `wQ`, `onLattice`, `CoeffTop`, `carrier`, `TowerRealizable` (lines/windows + slope_law/vertex_tie/steeper/vertex_entry/window), `rl.floorB b := (rl.line T.K).at (T.blockEdge b)` — DEFINITIONAL for LST leg (ii) |

Consumer census (verified by repo-wide grep): NOTHING outside their own files
consumes `C6_alphabetCard` or `R6_carrierInstance` (ScratchC6 mentions C6 in
comments only). Blast radius of both repairs: their own files + MANIFEST records.

### 2.3 MovesGr — the 30-file corpus and the 20-token sorry census

Census cross-checked against golf_baseline_2026-07-30/MovesGr_axioms.txt
(correction addendum: 20 sorry tokens on 19 lines in 7 files; re-verified
identical at HEAD by this blueprint's grep, with the v2 sorries at 395-422).

PROVED, KEEP (20 files, all Lean-core): `Defs.lean` (vocabulary: `SideVal`,
`GradedRingStr` (+ the 2026-07-28 signed-off `add_def` field), `GenuineStageModel`
— NOTE A40: the `L₀ ≅ K[z^{±1}]` fiat is hard-coded in Θ's codomain type, standing
blueprint gap G-L0, docstrings now honest); the six `L0_*` units;
`L1_pmul_assoc`; `L1_initialForm_add_lt`; `L1_initialForm_mul`;
`L1_gradedRingStr_exists_2` (the PROVED capstone of D.1(a)-(c));
`L1_gr_domain_iff_val_v3` (PROVED, in-namespace); `L2_degZero_subring_v2`
(PROVED); `L2_loc_exists`; `L2_homMon_homogeneous`; `L3_Tunit_deg1`;
`L3_iso_exists`; `L3_rank1_residual`; `L3_residual_mul`; `L4_grRes_eq_genuine`
(the fiat discharge); `HeldUnits_certs.lean` + `HeldUnits_L5_cert.lean` (the
machine-checked vacuity/unprovability certificates `baseStage_hbase_empty`,
`transitionCoreL_e0_false`, `recTRANSRS_only_vacuous`, `tvec_units_fragment`,
`stripReps_*` — consumed by HC1/S8_childS6).

QUARANTINE-BOUND (6 files, the R2 list = "the five v1s + L1_gr_domain_iff_val_v2",
A26): `L1_gradedRingStr_exists.lean` (v1, sorry@115 `mul_assoc`, IN-namespace —
collides with _2's proved name, A11); `L1_gr_domain_iff_val.lean` (v1, sorry@59,
ROOT namespace); `L1_gr_domain_iff_val_v2.lean` (sorry@124, ROOT — v2 diagnosed
the OLD statement false pre-rekey; superseded by v3); `L2_coeffLoc.lean` (v1,
3 sorries @22/27/35, ROOT); `L2_degZero_subring.lean` (v1, ZERO sorries but
IN-namespace same-name with the proved _v2 — see the §5 R-6 check);
`L4_genuine_imp_stageCoreL.lean` (v1, bare `:= sorry`@70, ROOT; its own header
argues the statement NOT provable from its hypotheses = A13).

LIVE-SORRIED, ADJUDICATE (2 files, 13 tokens): `L2_coeffLoc_v2.lean` (2 sorries
@161/169: the "(L^coeff)₀ ⊇ K" and "(P1) z-pinning" conjuncts — in-file grounded
arguments that both need StageWF-type data ABSENT from `Stage`+`GenuineStageModel`;
FAITHLESS per MOVES_LEAN_SEMAUDIT_GR_2026-07-26.md §B #15);
`L4_genuine_imp_stageCoreL_v2.lean` (11 sorries @395-422; header classifies:
7 UNDERIVABLE from the interface — `wPrev_mul`, `wPrev_ult`, `prevIaug`, `tvec`,
`tvec_unit`, `reps_nonempty`, `p_is_rep` (free-field independence arguments) —
and 4 derivable-in-principle — `coeff` clauses 2-3, `slot`.2, `coeff_loc` clause 1;
inherits sorryAx from L2_coeffLoc_v2 regardless; FAITHLESS per semaudit §B #21).

HELD (5 MANIFEST-only units, NO .lean files): `L4_baseStage_exists`,
`L4_base_nonvacuity_gate`, `L4_TRANSvi`, `L4_TRANSstage`, `L5_recTRANSRS` — each
carries a `held_status_asbuilt_2026-07-30` MANIFEST field citing its semaudit
classification (#22-#26) and its Lean-core unprovability certificate. NO ACTION
in this area (nothing to quarantine; the honest record already exists).

Import topology (verified): every MovesGr unit file imports only Mathlib +
Moves Defs layers + MovesGr.Defs — quarantining any unit file breaks no import.
External consumers of MovesGr: HC1/DefsCar.lean (Defs), HC1/T6_carrierLaws.lean
(four L0 units), HC1/S8_childS6.lean (HeldUnits_certs) — none touch the
quarantine-bound or live-sorried files.

### 2.4 Moves — the deprecated collision files

| deprecated file (quarantine-bound) | colliding name | canonical (KEEP) | notes |
|---|---|---|---|
| Moves/L4_TRANSviii_b_R3.lean | `LeanUrat.Moves.L4_TRANSviii_b` | L4_TRANSviii_b_R4.lean | R3 sorry@103 (A5) |
| Moves/L5_landTransport_R3.lean | `LeanUrat.Moves.L5_landTransport` | L5_landTransport_R4.lean | R3 sorry@54, REFUTED-as-stated (A6) |
| Moves/L5_landTwoSided_R5.lean | `LeanUrat.Moves.L5_landTwoSided` | L5_landTwoSided_repair.lean:756 (hexact form, post-R1) | R5 sorry@964 (R1 execution record) |
| Moves/L5_landVertexDigit_repair.lean | `LeanUrat.Moves.L5_landVertexDigit` | **L5_landVertexDigit.lean** | ⚠ BASELINE A/B LABELS REVERSED for this pair (golf ledger "VERIFY-2 FOLD-IN CORRECTION"): the NON-repair file is canonical — HC1/K1_vertexPin.lean:8 and HC1/S16_levelLanding.lean:11 import it. Quarantine the `_repair` file ONLY. Both sorry-free, theorem byte-identical |
| (candidate 5th) Moves/L4_TRANSviii_a_R5.lean | `LeanUrat.Moves.L4_TRANSviii_a` | L4_TRANSviii_a_R5_final.lean | BOTH sorry-free, statements byte-identical; R5 header self-declares DEPRECATED ("Do not import — downstream uses the _final file"); zero importers. Scope call → §6 Q-7 |

Importer census (verified by grep at HEAD): ZERO in-tree modules import any of
the five files above. None is in the root import graph (LeanUrat.lean) or in
AxChk_baseline.lean. The enumerated corpus sweep discovers files on disk, so
moving them out of `LeanUrat/` removes them from all sweeps with no list edits.

### 2.5 Quarantine convention (repo standard, from lean/quarantine/README.md)

`git mv lean/LeanUrat/<dir>/<file>.lean lean/quarantine/<dir>_<file>_2026-07-30.lean.txt`
+ a dated README.md section stating WHY (collision partner, sorry census,
supersession pointer, importer census at removal) + full `lake build` + AxChk
re-run. Quarantined = preserved verbatim, invisible to lake and to greps scoped
`--include=*.lean`.
