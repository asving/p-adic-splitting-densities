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

---

## 3. THE MATHEMATICS

### 3.1 C6 — the dichotomy is mistyped; the certified collapse; the repair

The fenced statement (C6_alphabetCard.lean:54-62), for a tower T, block b, height
γ, on nonempty level sets:

    (0)  card 𝔸(b,γ) = p ^ aDim(b,γ)                                 [conjunct 1]
         ∧ (card 𝔸(b,γ) = card F_{K+1}  ↔
              ∀ c ∈ levelSet b γ, ∃ y ≠ 0-ish, typComposite(single c y) ≠ 0)
                                                                      [conjunct 2]
         ∧ ((∃ c ∈ levelSet b γ, ∀ y, typComposite(single c y) = 0) →
              aDim(b,γ) < log_p card F_{K+1})                         [conjunct 3]

Here 𝔸(b,γ) = `T.alphabet b γ` (the additive closure of the single-coordinate
slot images in the graded piece `grQ γ`), and F_{K+1} = the top stage's residue
field `(T.stg (Fin.last T.K)).K`.

The ScratchC6 walk (2026-07-28, all five certificates PROVED Lean-core) shows the
attainability condition was typed over the WRONG index set (blueprint Deviation
D-10): with T3 + T7's digit toolkit, membership in the level set already forces
attainability —

    (1)  C6_attain_automatic : ∀ c ∈ levelSet b γ, ∀ y ≠ 0,
           typComposite b γ (Pi.single c y) ≠ 0
         (proof: w_top(digLift y · mono c) = 0 + strTop·γ, exactly the piece
          index, so the class is weight-detected nonzero)

so conjunct 2's RHS is a THEOREM (take y = 1), conjunct 3's hypothesis is
REFUTABLE (both certified), and hence

    (2)  C6_forces_unconditional_fullness : (fenced C6 at (b,γ)) →
           card 𝔸(b,γ) = card F_{K+1}

— the pre-D¹¹c uniform display that CODEX_CONFIRM_D11B refuted at shallow heights
(the note's own correction, MOVES 2160-2165: "STRICTLY SMALLER at shallow
heights"). Math-level shallow instance (ScratchC6 header, not compiled): base
(e₀,h₀) = (1,1), K₀ = F₂ ⊂ F = F₄, one g = 2 increment (ψ = z²+z+1); at
(b,γ) = (0,0) the level set is the single coordinate l = 0, slots ≡ 0, so 𝔸 is
one base-digit line, card ≤ |F₂| = 2 < 4 = |F₄|. The addresses the note's
condition is really about would need l < 0 — they are NOT coordinates, so the
per-coordinate ∀ cannot see them.

**Consequence.** C6 as fenced is not provable and is believed FALSE for any tower
with residual growth. Honest disposition = statement-fence adjudication (Asvin
queue Q3), with two repair candidates:

**(R-a) minimal honest restatement.** Replace the three conjuncts by conjunct 1
plus the two certified facts, i.e.

    theorem C6_alphabetCard' … :
      Nat.card ↥(T.alphabet b γ) = p ^ T.aDim b γ ∧
      (∀ c : ↥(T.levelSet b γ), ∃ y, T.typComposite b γ (Pi.single c y) ≠ 0)

(conjunct 1 = `C6_conjunct1_closable` = T7; second conjunct =
`C6_conjunct2_rhs_always`). The note's DICHOTOMY content is then carried by the
record (the Scratch certificates + the header), not by a false iff. Cheap,
provable today, loses the MOVES 2160-2165 dichotomy as a formal statement.

**(R-b) faithful address-typed dichotomy.** Re-type the attainability condition
over ADDRESSES (bounded slot vectors), per ScratchC6's diagnosis ("the correct
typing quantifies over ALL bounded slot vectors in γ's alignment class; existence
of the coordinate, i.e. 0 ≤ γ − Σ_r s_r·κ_r, is then the attainability
condition"). Vocabulary to add (new defs, statement-fence review):

    (3)  Addr T b := { s : Fin (T.K+1) → ℕ //
                        (∀ r : Fin T.K, s r.castSucc < T.slotBound r) ∧
                        s (Fin.last T.K) = b }
         aligned T γ s := ∃ n : ℤ, (γ − Σ_r s_r·κ_r) = n     -- ℤ-alignment
         attainable T γ s := 0 ≤ γ − Σ_r s_r·κ_r             -- l exists in ℕ

and the repaired conjuncts 2'/3':

    (4)  card 𝔸(b,γ) = card F_{K+1}  ↔  ∀ s : Addr T b, aligned T γ s →
                                            attainable T γ s
         (¬ RHS → aDim(b,γ) < log_p card F_{K+1})

MATH RISK: (4) is note-content (the D-10-corrected reading of MOVES 2160-2165);
its ⟸ leg needs the counting identity "number of aligned attainable addresses at
(b,γ) × log_p|F_Q| = log_p card F_{K+1} when all aligned addresses attainable" —
NOT in the corpus, real new mathematics (relates aDim to the address count via
T8's subgroup A and the F_Q-line dimensions). Countermodel-first applies to (4)
BEFORE any prover (unit CL-04). If (4) survives probing, its proof is the
hardest C6 work (unit CL-05); if it fails, fall back to (R-a) with the probe on
record. Orchestrator picks R-a vs R-b (§6 Q-1) — this blueprint recommends
attempting R-b's countermodel probe FIRST and letting its outcome inform Q-1.

Also queued at C6: a COMPILED countermodel to the ORIGINAL fenced C6 needs a
concrete `Tower p F` term (stages + moves + base data for the shallow instance).
That construction cost is unknown (Tower has heavy per-move certificate fields);
unit CL-01 is an attempt with explicit permission to return BLOCKED with the
exact missing-constructor list. The adjudication may proceed on the math-level
record + certificates (1)-(2) alone (§6 Q-2).

### 3.2 R6 — execute A17, then close via the graded-expansion pack

**The A17 defects (both re-verified accurate at the 2026-07-30 fold-in).**

DEFECT 1 (statement-level, machine-checked): `LSTStmt'` leg (i-b)
(R1_LSTStmt.lean:61-63) reads

    (5)  ∀ b, window H b → ∀ y : K.Coord → K.Digit, slotCoeff H b y ≠ 0 →
           ∃ c₀, y c₀ ≠ 0 ∧ K.G.w (slotCoeff H b y) = ht H c₀ ∧
                 ∀ c, y c ≠ 0 → ht H c₀ ≤ ht H c

— the minimality clause quantifies over ALL coordinates: R1 dropped T4/C1's
support hypothesis. Kernels 2a+2b (R6 file, PROVED) refute (5) for every
content-bearing pack whose slotCoeff is blind to off-block digits (the real one
is, definitionally). REPAIR (fence-gated, the A17 sign-off): reinstate exactly
T4/C1's hypothesis row in (i-b):

    (6)  VARIANT A (T4-parity):  insert
           `(Function.support y).Finite → (∀ c, y c ≠ 0 → K.blk H c = b) →`
         VARIANT B (support-only): insert
           `(∀ c, y c ≠ 0 → K.blk H c = b) →`

Variant analysis: the graded-expansion pack below satisfies (i-b) under EITHER
variant — its per-level restrictions are finitely supported automatically
(`levelSet_finite'`), so `hfin` is not needed for THIS instance. But `hfin` IS
load-bearing for the direct polynomial pack (T4 requires it; finsum junk-0s at
infinite support), and C1_LST carries it. Recommendation: VARIANT A, for C-layer
parity (the R-layer was meant to abstract C1's statement verbatim). Orchestrator
ratifies (§6 Q-3).

DEFECT 2 (instance-level; NO statement change): `TYPStmt'` conjunct 1 is
unconditional additivity of `inγ γ' ∘ slotCoeff H b` in the digit tuple. For the
POLYNOMIAL-Coeff pack (`K.G := T.carrier _`, `slotCoeff := T.slotCoeff`) it is
REFUTED by cross-strata tuples (weights γ₁ < γ': LHS = 0 ≠ RHS — the R6 header's
countermodel). The repair is choosing the right INSTANCE (the note's own MOVES
3795-3807 display), not weakening TYPStmt'. A17 should RECORD this scoping:
TYPStmt', DOMStmt', SecB1Stmt' texts unchanged.

**The graded-expansion pack (the POSITIVE FINDING, elaborated).** Fix T and
rl : TowerRealizable T. Define (new defs, HC1-side, review-flagged):

    (7)  LatticeExp T := { B : ∀ γ : ℚ, T.grQ γ //
                            ∀ γ, B γ ≠ 0 → ∃ n : ℕ, γ = (n : ℚ) / T.strTop }
         -- AddCommGroup: componentwise (support condition closed under +, −, 0)
         wE (B) := least γ = n/strTop with B γ ≠ 0 (Nat.find), ⊤ if B = 0
                                                   : WithTop ℚ
         evalE γ B := B γ                          -- the class map

    (8)  packE : CarrierPackR p :=
         { G := { Coeff := LatticeExp T, Gr := T.grQ, w := wE, inγ := evalE,
                  w_add, inγ_add, inγ_kills, inγ_detects := §CL-08 },
           Hist := Unit, Coord := T.Coord, Digit := ↥(T.stg 0).FQ,
           kIdx _ := T.K, ht _ := T.ht, blk _ := T.blk,
           lvl _ b γ := T.levelSet b γ,
           slotCoeff _ b y := ⟨fun γ => T.inGr γ (T.slotCoeff b
                                 (fun c => if c ∈ T.levelSet b γ then y c else 0)),
                               lattice-support proof (LAT + levelSet-emptiness)⟩,
           aDim _ := T.aDim, lines _ := rl.line, blockEdge _ := T.blockEdge,
           interiorEnd _ i := if i ≤ T.K then rl.interiorEnd i else 0,
           window _ _ := True, mono _ c := monoE c, floorB _ := rl.floorB }

where `monoE c := ⟨fun γ => T.inGr γ (T.mono c), _⟩` (nonzero only at γ = ht c).
The Gr-pin `∀ γ, packE.G.Gr γ = T.grQ γ` holds by `rfl` — the non-vacuity clause.

Supporting arithmetic (LAT, unit CL-07): every height lies on the nonneg lattice:
`ht c ≥ 0` directly from the formula (l, slots, κ ≥ 0 as ℕ-casts), and
`strTop·ht c ∈ ℤ` since `e_r·STR_r = STR_{r+1} ∣ STR_K·e_K = strTop` for every
r ≤ K (divisibility chain on `strAux`; each κ_r = h_r/(e_r·STR_r)).

**The carrier laws for (7)** (unit CL-08): `w_add` — the least populated level of
B+B' is ≥ min of the two leasts (componentwise addition); `inγ_add` — evaluation
is additive UNCONDITIONALLY (stronger than the law); `inγ_kills` — below the
least populated level every component is 0 (minimality of Nat.find + lattice
support off-lattice); `inγ_detects` — at wE B the component is nonzero (Nat.find
spec). All elementary.

**Leg-by-leg discharge of R6's three statement defs at packE:**

(i-a) `wE (monoE c) = ht c`: monoE c has exactly one nonzero component, at
γ = ht c — detects there via T3 (`w_top(mono c) = strTop·ht c`, MonoNZ discharged
by `mono_ne`: mono = C(p^l)·∏Φ^s ≠ 0 from `hmonic`), kills elsewhere (γ < ht c:
mono ∈ gt(⌊strTop γ⌋); γ > ht c: the inGr dif-condition fails). [CL-15]

(i-b) REPAIRED, the transport from T4 — THE RISK STEP. Given y with block-b
support and E := packE.slotCoeff b y ≠ 0: let γ̂ := wE E (the least populated
level). At γ̂ the component is `T.inGr γ̂ (T.slotCoeff b (y↾lvl b γ̂))` ≠ 0, so the
restricted polynomial is ≠ 0; T4 on the restriction (finitely supported —
levelSet_finite'; all support at height γ̂) yields c₀ with y c₀ ≠ 0 and
ht c₀ = γ̂. Minimality: for y c ≠ 0 with γ := ht c < γ̂, the component at γ is 0
(below the least populated level); but by **LVL-DET** below it would be nonzero —
contradiction; hence no support below γ̂. [CL-14]

    (9)  LVL-DET: for y ≠ 0 supported inside T.levelSet b γ (a finite set),
           T.inGr γ (T.slotCoeff b ŷ) ≠ 0        (ŷ = the extension by 0)

LVL-DET = NCL + T4 + T6-detects: if the polynomial `slotCoeff b ŷ` is nonzero,
T4 pins wQ = min-height-of-support = γ EXACTLY (no weight jump possible), and
`inγ_detects` (T6) gives a nonzero class. So (9) reduces to

    (10) NCL (no-cancellation at a level): y ≠ 0 supported in levelSet b γ ⟹
           T.slotCoeff b ŷ = Σ_{c ∈ supp} digLift(y c) · mono c ≠ 0

**NCL is the one genuinely new lemma** — the corpus NEVER proves it (T4, C1 take
`slotCoeff ≠ 0` as hypothesis; T8's BijOn is from a SUBGROUP A, deliberately
dodging kernel-triviality). Mathematically NCL = uniqueness of the mixed-radix
p/Φ-adic development with unit digits. Proof plan (units CL-11/12/13):
reduce mod p^{l_min+1} then mod p, where l_min = the least p-exponent in supp y:
terms with l > l_min die; the survivors have DISTINCT slot vectors (T9(b):
(baseIdx, l) injective, and baseIdx ↔ s injective under the slot_lt bounds), so
over F_p[x] the sum is Σ_c d̄_c · ∏_r Φ̄_r^{s_c(r)} with every d̄_c ≠ 0 (digLift has
gaussVal 0 ⇒ a unit coefficient survives mod p... see the §5 R-2 caveat),
deg d̄_c < deg Φ̄₀, Φ̄_r monic of full degree. Positional uniqueness in F_p[x]:
strong induction peeling the highest slot by Euclidean div/mod against
Φ̄_r^{max} (quotient-remainder uniqueness with the degree bounds slot_lt). The
countermodel-first rule BINDS here: NCL is a universal that could conceivably
fail (unit CL-11 runs first). If NCL is FALSE, (i-b) FAILS at packE (a two-level
y with a cancelling lower level is a countermodel) and R6 needs a different
instance or a windowed (i-b) — automatic escalation to adjudication (§5 R-1).

(i-c): definitional at packE — each component of packE.slotCoeff reads y ONLY
through `y↾lvl b γ`, and the hypothesis row gives x, y equal there. [CL-15]

(ii): `rl.floorB b = (rl.line T.K).at (T.blockEdge b)` is DEFINITIONAL
(DefsCar.lean:266) with kIdx = T.K. [CL-15]

(iii): pure logic — c ∈ lvl b γ' has ht c = γ' > floorB b, contradicting
ht c ≤ floorB b (C1's leg-(iii) argument verbatim). [CL-15]

TYP conjunct 1: componentwise at each γ; restriction commutes with +; then
`inGr γ (slotCoeff b ((x+y)↾lvl)) = … x↾ … + … y↾ …` is EXACTLY C2_TYPa
conjunct (b) (typComposite additivity) after rewriting the restricted extension
through `typComposite`. SecB1Stmt' is the SAME lemma (its statement is TYP
conjunct 1 re-quantified). [CL-16]

TYP conjunct 2: the closure in R2's display, instantiated at packE, is literally
`T.alphabet b γ'` (same union of single-slot image ranges — an
extension-vs-subtype-Pi.single rewriting lemma), and `packE.aDim = T.aDim`, so
the equation is T7's third conjunct `p ^ aDim = card 𝔸` (symm). Empty level set:
both sides degenerate to card ⊥ = 1 = p^0. Off-lattice γ': singles are 0, closure
⊥, and T.alphabet is the same object — consistent. [CL-17]

DOM: for i ≤ T.K this is C4_DOM's first conjunct (rl.steeper + rl.vertex_entry
via MovesC.C2_DOM); for i > T.K the guard `interiorEnd _ i := 0` makes
`b < 0` impossible — vacuous. [CL-18]

**Assembly** (CL-19): `R6_carrierInstance := ⟨packE, fun γ => rfl, LST-legs,
TYP-legs, DOM⟩`, killing sorry@145. Zero dep-sorries: T3/T4/T5/T6/T7/C2/C4 all
PROVED Lean-core at HEAD. The 70-line obstruction record in the proof body is
HISTORY — move it verbatim into the file header (do not delete; the fold-in
notes already correct it), keep kernels 2a/2b (they document why A17 was needed).

**R5 vacuity (A17's second half)** (CL-20): `EQ2lawIfREL1' EQ2law :=
(∀ K : CarrierPackR p, REL1Pack p K) → EQ2law`. The antecedent quantifies over
ALL packs, so ONE junk pack refutes it and the def is True for every EQ2law.
Compile the refutation certificate (a pack with two constant lines violating
DOMStmt' at i=1, m=0, interiorEnd=1 — a ~30-line witness) and record: the def is
typed-only, currently consumed by NOTHING (grep-verified for `EQ2lawIfREL1'`
consumers before writing the record); whether to re-scope the antecedent (e.g.
to Gr-pinned packs or an ∃-form) is a MovesR-unparking design question, NOT
decided here (§6 Q-4). Grep at HEAD confirms: no consumer of `EQ2lawIfREL1'` or
`REL1Pack` outside R5_EQ2Pass.lean.

### 3.3 MovesGr — prove-vs-quarantine, per file

The corpus's mathematical mission (the graded-ring boundary: discharge the
"definitional facade" audit) is ALREADY delivered by the proved layer:
`L1_gradedRingStr_exists_2` (the genuine graded ring), `L1_gr_domain_iff_val_v3`
(domain ⟺ valuation), `L2_degZero_subring_v2`, `L3_iso_exists`/`L3_rank1_residual`
/`L3_residual_mul` (D.1(e)), `L4_grRes_eq_genuine` (the fiat discharge) — all
Lean-core. What remains is hygiene + two FAITHLESS partials:

**Quarantine set (6 files — golf repair-queue R2, pre-adjudicated "quarantine at
repo-prep, R2 convention"; this area IS that repo-prep pass).** Rationale per
file is in §2.3. The census effect: removes 7 of the 20 sorry tokens
(1+1+1+3+1 = 7) and ALL cross-module name collisions in MovesGr (the root-level
pairs `L1_gr_domain_iff_val` v1/v2, `L2_coeffLoc` v1, `L4_genuine_imp_stageCoreL`
v1; the in-namespace pairs `L1_gradedRingStr_exists` v1, `L2_degZero_subring`
v1). Post-quarantine name resolution: `LeanUrat.MovesGr.L1_gradedRingStr_exists`
binds uniquely to the PROVED _2 module; root `L1_gr_domain_iff_val` disappears
(the proved v3 is in-namespace); root `L2_coeffLoc` and root
`L4_genuine_imp_stageCoreL` bind uniquely to the LIVE v2 partials (still
sorry-backed — disclosed, next paragraph). Expected baseline delta vs
golf_baseline/MovesGr_axioms.txt: Group B disappears entirely; Group A loses the
root `L1_gr_domain_iff_val` line. Record this delta in the quarantine README
entry so future fence checks do not read it as a regression.

**The two live partials (13 tokens) — adjudication, NOT forced proof.**

`L2_coeffLoc_v2.lean` (2 sorries): both open conjuncts carry grounded in-file
arguments that they are UNPROVABLE from `(σ : Stage) (M : GenuineStageModel σ)` —
the "(L^coeff)₀ ⊇ K" conjunct needs rep weights that reach parent value −ν
(StageWF/DEF-3 content, not a `Stage` field; Θ-surjectivity gives arbitrary-f
preimages, not rep-monomials), and the (P1) z-pinning conjunct needs a
parent-weight-(−h)-reaching exponent vector with trivial scalar product (same
gap). Honest-sorries discipline ⇒ the options are:
  (a) statement repair: add the named hypothesis (a `RepLattice σ` Prop: the
      rep-weight lattice reaches every parent weight, + `reps_pinned`-style
      scalar normalization) to `CoeffLocLaw`'s derivation theorem — statement
      change, sign-off, and it RIPPLES into L4_v2's `coeff_loc` leg;
  (b) quarantine the partial (preserving the 2 proved conjuncts' work as .txt)
      and leave `CoeffLocLaw σ` an open obligation with the MANIFEST's
      status_asbuilt record as the pointer;
  (c) keep as-is (status quo: disclosed, censused, FAITHLESS-classified).
This blueprint recommends (b): the file's PROVED content (the Ein/Eout
weight-detecting evaluation, S4 ⊆) is preserved verbatim in quarantine, the
live census drops to L4_v2 only, and no false completeness is suggested by a
live half-file. Orchestrator decides (§6 Q-5).

`L4_genuine_imp_stageCoreL_v2.lean` (11 sorries): 7 are certified-underivable
(free-field independence: σ.wPrev, σ.Tvec exponents, σ.reps membership are
invisible to M — the header's perturbation arguments; same class as the HELD
units' certificates), 4 are derivable-in-principle (`coeff` clauses 2-3 by
hS5-monomial product induction, `slot`.2 by distinct-position termwise vanishing,
`coeff_loc` clause 1 by graded-invariant closure induction). Filling the 4 does
NOT change the unit's FAITHLESS classification (semaudit §B #21: StageCoreL
content absent from M) nor kill its sorryAx (7 + the L2 inheritance remain).
Options mirror (a)/(b)/(c) above; recommendation: (b) quarantine together with
L2_coeffLoc_v2 (they are one derivation), UNLESS the orchestrator wants the
4 derivable legs banked first (conditional unit CL-23). Either way the MovesGr
LIVE census lands at 0 sorries.

**The five HELD units:** no action (no files exist; MANIFEST held_status fields
+ Lean-core certificates already constitute the honest record). Any future
revival goes through the faithful §B2-DEF D.2 restatements, out of scope here.

### 3.4 Moves — the deprecated-file quarantine sweep

The four files of §2.4 (plus the candidate fifth) are quarantined under the
§2.5 convention. Execution constraints, each verified against the ledger:

1. **The VertexDigit reversal (CRITICAL).** The golf baseline's Group A/B labels
   are BACKWARDS for the `L5_landVertexDigit` pair: quarantine
   `L5_landVertexDigit_repair.lean`, NEVER `L5_landVertexDigit.lean` — the
   latter is imported by HC1/K1_vertexPin.lean:8 and HC1/S16_levelLanding.lean:11
   (the K1 kernel's import). Following the baseline as written would delete a
   load-bearing module. (Golf ledger, VERIFY-2 FOLD-IN CORRECTION section.)
2. Zero-importer precondition: re-run the importer grep per file AT EXECUTION
   TIME (the A7 lesson: the ledger once mis-reported an import that had already
   been re-pointed; state drifts). A file with a live importer is NOT
   quarantined — it escalates to adjudication.
3. The sorried private `shared_read_forces`-style history: L5_landTwoSided_R5's
   sorry@964 and L4_TRANSviii_b_R3's sorry@103 are believed-false or superseded
   forms; the quarantine README entry must state the supersession pointer
   (repair/R4 file + the R1 execution record for landTwoSided).
4. Census effect: the "sorryAx only at the ten fenced sites + deprecated Moves
   files" caveat (golf baseline header) simplifies to the fenced sites alone;
   AxChk_baseline output is expected byte-identical (none of the five is in any
   capstone cone — verify by the post-move re-run).

---

## 4. UNIT SPLIT

Conventions: ids CL-01…CL-25. difficulty ∈ {routine-opus, hard-fable,
adjudication}. "size" = estimated NEW proof lines (statements/defs excluded).
Every prover unit gets the standing prompt rows: staged-write discipline, lake
build (not lake env lean) for the green record, `#print axioms` tail, MANIFEST
entry, BLOCKED-with-artifact permitted (never a forced proof).

### C6 cluster

**CL-01** — compiled countermodel attempt vs fenced C6.
  Statement: construct `Tshallow : Tower 2 (GaloisField 2 2)` realizing
  ScratchC6's shallow instance (base (e₀,h₀)=(1,1), one g=2 increment,
  ψ = z²+z+1), + `card (Tshallow.alphabet 0 0) ≠ card F₄`, hence
  `¬ C6-statement(Tshallow)` via `C6_forces_unconditional_fullness`.
  Deps: none (runs first). Difficulty: hard-fable. Size: unknown, cap the
  attempt at ~400 lines; PERMITTED OUTCOME: BLOCKED + the exact list of Tower/
  Stage/move certificate fields that could not be discharged (feeds Q-2).
**CL-02** — the C6 statement-repair adjudication (Asvin queue Q3).
  Inputs: ScratchC6 certificates (1)-(2), CL-01's outcome, CL-04's probe if run.
  Output: ratified statement text, R-a or R-b (or fence-hold). Difficulty:
  adjudication. BLOCKS CL-03/CL-05.
**CL-03** — (conditional: R-a) restate + prove C6-min.
  Statement: §3.1 (R-a) display. Proof: conjunct 1 := `C6_conjunct1_closable`
  (or T7 directly); conjunct 2 := `C6_conjunct2_rhs_always`; both already
  proved — the unit re-homes them into C6_alphabetCard.lean (Scratch stays, its
  copies documented). Deps: CL-02. Difficulty: routine-opus. Size: ~15.
**CL-04** — (pre-adjudication probe; countermodel-first for R-b) address
  vocabulary + dichotomy probe.
  Part 1: defs (3) (`Addr`, `aligned`, `attainable`) — defs only, review-flagged.
  Part 2: PROBE (4): search for a tower/instance where all aligned addresses at
  (b,γ) are attainable yet card 𝔸 < card F_{K+1} (candidate mechanism: F_Q ⊊ K_top
  digit-line deficiency even at full address occupancy — exactly ScratchC6's
  card ≤ |F₂| < |F₄| mechanism, WHICH MAY SURVIVE the retype; check whether (4)'s
  RHS must instead read "attainable ∧ digit lines full", i.e. whether the note
  ties fullness to [F_Q : F_p]·#addresses = [F_{K+1} : F_p]). Output: a concrete
  candidate countermodel sketch or a "no obstruction found + the counting
  identity to prove" report. Deps: none (informs CL-02). Difficulty: hard-fable.
  Size: defs ~30 + probe report.
**CL-05** — (conditional: R-b ratified) the address-typed dichotomy proof.
  Statement: (4) as ratified. Sketch: ⟸ via the counting identity
  aDim = Σ_{attainable aligned addresses} dim_{F_p}(digit line) and the
  fullness bookkeeping vs `C6_cardK_bridge`; ⟹ contrapositive via the missing
  address ⇒ a missing p-power factor (T8's subgroup A). EXPECT re-splitting into
  3-4 subunits at execution (counting lemma / ⟸ / ⟹ / assembly) — the E-phase
  writer for this unit must propose the split. Deps: CL-02, CL-04, CL-01's
  record. Difficulty: hard-fable. Size: ~150-250 across subunits.

### R6 cluster

**CL-06** — the A17 adjudication (fence sign-off).
  Output: ratified LSTStmt' (i-b) repair text — VARIANT A vs B of (6) (§3.2
  analysis attached); the DEFECT-2 scoping record (TYPStmt'/DOMStmt'/SecB1Stmt'
  unchanged); the R6 proof-body history relocation approved. Difficulty:
  adjudication. BLOCKS CL-14, CL-19 (statement edit lands here; the R1 file edit
  itself is part of this unit: rewrite leg (i-b), rebuild HC1 cone — R1 is
  imported by R2/R3/R5/R6, expect a small ripple, no proof breaks since nothing
  proves LSTStmt' yet). Size: statement edit + ripple check.
**CL-07** — LAT: the height lattice lemma.
  Statement: `∀ c : T.Coord, 0 ≤ T.ht c ∧ ∃ n : ℕ, T.ht c = (n : ℚ) / T.strTop`
  + the divisibility `∀ r, (T.stg r).e * T.str r ∣ T.strTop`.
  Sketch: κ_r = h_r/(e_r·STR_r); clear denominators via the divisibility chain
  STR_{r+1} ∣ STR_K ∣ strTop (induction on strAux); nonneg from ℕ-casts.
  Deps: none. Difficulty: routine-opus. Size: ~40.
**CL-08** — LatticeExp + wE + the four carrier laws.
  Defs (7) + `gradedExpCarrier T : GradedCarrierR p` with `Gr := T.grQ`.
  Sketch: AddCommGroup on the subtype (support condition additive); wE via the
  well-ordering of the ℕ-indexed populated levels (Nat.find on
  `∃ n ≤ N₀, B (n/strTop) ≠ 0` — note wE needs B ≠ 0 to terminate: define via
  `if h : B = 0 then ⊤ else …`); laws per §3.2. Deps: CL-07. Difficulty:
  routine-opus (fiddly WithTop bookkeeping, no ideas). Size: ~120; SPLIT RULE:
  if the AddCommGroup instance alone exceeds ~40 lines, spin it off.
**CL-09** — packE + the Gr-pin.
  Def (8) incl. `monoE`, the lattice-support proofs of `packE.slotCoeff` and
  `monoE` (via LAT + `levelSet`-emptiness ⇒ zero component + T3 for monoE), and
  `theorem packE_gr_pin : ∀ γ, (packE T rl).G.Gr γ = T.grQ γ := fun _ => rfl`.
  Deps: CL-07, CL-08. Difficulty: routine-opus. Size: ~80.
**CL-10** — NCL countermodel attempt (COUNTERMODEL-FIRST; runs before CL-11/12).
  Charge: try to falsify (10) — find distinct same-height bounded addresses
  c ≠ c' (equal ht forces different l when s differs, since κ > 0 … verify) and
  digits a, b with `digLift a · mono c + digLift b · mono c' = 0`, or prove a
  small decidable instance rules it out. Attack the mod-p reduction's weak point:
  digLift has gaussVal 0 (SOME coefficient is a unit) but its mod-p reduction
  could in principle interact across DIFFERENT x-degree blocks. Output: a
  countermodel, or a "mechanism survey: none found" report naming the exact
  algebraic fact that blocks each attempt. Deps: none. Difficulty: hard-fable
  (analysis unit, no required theorem). Size: report + optional ≤60-line cert.
**CL-11** — F_p[x] positional uniqueness.
  Statement (over any field K₀, applied at K₀ = 𝔽_p): for a finite set of
  DISTINCT slot vectors s : Fin (K+1) → ℕ bounded by `slotBound` at inner
  levels and constant (= b) at the top, monic Φ̄_r with
  deg Φ̄_{r+1} = slotBound r · deg Φ̄_r (the key-degree ratio law), and nonzero
  digits d̄_s with deg d̄_s < deg Φ̄₀:  Σ_s d̄_s · ∏_r Φ̄_r^{s r} ≠ 0.
  Sketch: strong induction on the highest inner level where the s differ;
  Euclidean uniqueness of div/mod by Φ̄_r^{(min slot at level r)} with the degree
  bound Σ_{r'<r} slotBound·deg < deg Φ̄_r (the mixed-radix carry bound — T9(b)'s
  numeric kernel re-used); base case: distinct powers of nothing left, one term,
  d̄ ≠ 0. NOTE: the top slot is CONSTANT b, so it factors out (`Φ̄_K^b ≠ 0`) —
  the induction runs on inner levels only. Deps: CL-10 (must complete first).
  Difficulty: hard-fable. Size: ~150; SPLIT RULE: the div/mod degree lemma is
  its own ~40-line sublemma — E-phase writer may emit CL-11a/CL-11b.
**CL-12** — NCL: the ℤ_[p] lift.
  Statement: display (10). Sketch: l_min := min p-exponent over supp y (finite);
  in `slotCoeff b ŷ = Σ digLift(y c)·C(p^{l c})·∏Φ^{s c}`, reduce the coefficient
  ring mod p^{l_min+1}: terms with l > l_min vanish; divide by p^{l_min}; reduce
  mod p: survivors have distinct s (equal ht + equal l ⇒ equal s via the ht
  formula's ℚ-independence over the bounded slots — the same-baseIdx step of
  T9(b) — hence equal c); digits reduce to d̄_c ≠ 0 (gaussVal(digLift) = 0);
  apply CL-11; conclude the polynomial ≠ 0 in ℤ_[p][x] (a nonzero mod-p^{l_min+1}
  image). Deps: CL-10, CL-11, T9. Difficulty: hard-fable. Size: ~120.
**CL-13** — LVL-DET.
  Statement: display (9). Sketch: NCL gives the polynomial ≠ 0; T4 on ŷ (hfin
  from `levelSet_finite'`, hsupp from level-set support, all heights = γ) pins
  `wQ (slotCoeff b ŷ) = γ` exactly; `(T6_carrierLaws T).2`'s inγ_detects leg
  gives `T.inGr γ … ≠ 0`. Deps: CL-12. Difficulty: routine-opus. Size: ~35.
**CL-14** — repaired (i-b) at packE (the transport).
  Statement: leg (i-b) of the CL-06-ratified LSTStmt' for `packE T rl`.
  Sketch: §3.2's two-level argument — γ̂ := wE(E) via detects; T4 on the
  γ̂-restriction for the witness c₀; minimality by contradiction through LVL-DET
  at any lower populated height. Careful bookkeeping: y's support need not be
  finite (VARIANT B) — every step above uses only PER-LEVEL restrictions, which
  are finite; if VARIANT A was ratified, hfin is available and unused.
  Deps: CL-06, CL-08, CL-09, CL-13. Difficulty: hard-fable. Size: ~100.
**CL-15** — the easy LST legs at packE: (i-a), (i-c), (ii), (iii).
  Sketch: (i-a) monoE single-level detect/kill via T3 + `mono_ne` (lift the
  ScratchC6 private into this unit's file or re-prove — 10 lines); (i-c)
  componentwise `rfl`-after-congr (the level restriction reads only lvl-values);
  (ii) `rfl`-adjacent (floorB definitional); (iii) the C1 leg-(iii) two-liner.
  Deps: CL-09 (+CL-07 for (i-a)'s lattice cases). Difficulty: routine-opus.
  Size: ~90 total.
**CL-16** — TYP conjunct 1 at packE + SecB1Stmt'.
  Sketch: componentwise; restriction additive; rewrite both sides through
  `T.typComposite` (the extension-of-restriction lemma: for z supported in
  lvl b γ, `T.slotCoeff b z = T.slotCoeff b (extension of the subtype tuple)`);
  close with `C2_TYPa T b γ |>.2`. Emit both `packE_typ1` and
  `packE_secB1 : SecB1Stmt' p (packE T rl)` (same proof, second binder order).
  SecB1 is NOT consumed by R6's statement — providing it is a flagged ADDITION
  (§6 Q-6). Deps: CL-09. Difficulty: routine-opus. Size: ~70.
**CL-17** — TYP conjunct 2 at packE.
  Sketch: prove the closure-set equality `(R2's union at packE) = ↑(T.alphabet
  b γ')` — both are closures of the same single-slot image family (the
  subtype-Pi.single vs full-Pi.single rewriting: `Pi.single (c : Coord) y`
  restricted to lvl equals the subtype `Pi.single ⟨c,h⟩ y` extension; for
  c ∉ lvl both sides contribute {0} ⊆ closure — check R2's `⋃ c ∈ K.lvl` form
  only ranges over members, so only the member case arises); then
  `(T7_alphabetSpan T b γ').2.2.symm` with `packE.aDim = T.aDim` by rfl.
  Deps: CL-09. Difficulty: routine-opus (fiddly). Size: ~60.
**CL-18** — DOMStmt' at packE.
  Sketch: cases on `i ≤ T.K`: guard branch `interiorEnd = 0` kills b < 0;
  main branch: `(C4_DOM T rl ⟨i, _⟩ m hm b hb).1` after the if-rewrite.
  Deps: CL-09. Difficulty: routine-opus. Size: ~25.
**CL-19** — R6 assembly (kills HC1 sorry #2).
  `R6_carrierInstance T rl := ⟨packE T rl, packE_gr_pin, ⟨…legs…⟩, ⟨typ1, typ2⟩,
  dom⟩`; relocate the :73-144 obstruction record verbatim to the file header
  under a "HISTORY (pre-A17)" banner; keep kernels 2a/2b; refresh the docstring
  ("hyp: TowerRealizable" stays); `#print axioms` = Lean-core; full `lake build`;
  MANIFEST as-built note (sorry :145 → 0). Deps: CL-06, CL-14…CL-18.
  Difficulty: routine-opus (assembly). Size: ~30 + edits.
**CL-20** — R5 antecedent-vacuity certificate.
  Statement: `theorem rel1_forall_refuted : ¬ ∀ K : CarrierPackR p, REL1Pack p K`
  via a junk pack breaking DOMStmt' (two constant lines, interiorEnd 1).
  + a header record on `EQ2lawIfREL1'`: typed-only, zero consumers at HEAD,
  re-scope deferred to MovesR unparking (Q-4). NEW public theorem — flagged
  addition per campaign precedent. Deps: none (R1-R5 as-is; independent of
  CL-06's edit — re-verify after it lands). Difficulty: routine-opus. Size: ~40.

### MovesGr cluster

**CL-21** — MovesGr quarantine execution (the R2 six).
  Move the 6 files of §2.3 per the §2.5 convention (names:
  `MovesGr_<file>_2026-07-30.lean.txt`); README entries incl. the expected
  baseline delta (§3.3); MovesGr/MANIFEST.json as-built addendum; full
  `lake build` + AxChk_baseline re-run byte-compare; repo grep proving no
  import references remain. PRE-STEP (the §5 R-6 check): byte-diff
  `L2_degZero_subring.lean` (v1, 0 sorries) vs `_v2` statements — v1 proves the
  same-named theorem against the pre-rekey structure; record the statement diff
  in the README entry before moving. Deps: none. Difficulty: routine-opus
  (execution + evidence discipline; no proofs). Size: 0 proof lines.
**CL-22** — live-partials disposition adjudication (L2_coeffLoc_v2 +
  L4_genuine_imp_stageCoreL_v2).
  Present §3.3's options (a)/(b)/(c) with the semaudit classifications;
  recommended (b) quarantine-both-with-record. If (a) is chosen the repair
  statement (the `RepLattice`-style named hypothesis) comes back through the
  fence with its own blueprint addendum. Deps: CL-21 (so the census context is
  clean). Difficulty: adjudication.
**CL-23** — (conditional: CL-22 chooses keep-and-improve) bank the 4 derivable
  v2 obligations: `coeff` clauses 2-3 (hS5-monomial product induction: positions
  and degrees couple as (−t·ν, e·ν); `e·k_j = j − t·γ` gives the stride),
  `slot`.2 (distinct positions ⇒ termwise vanishing), `coeff_loc` clause 1
  (graded-invariant closure induction). Deps: CL-22. Difficulty: hard-fable.
  Size: ~150 in-file.

### Moves cluster

**CL-24** — deprecated-Moves quarantine execution.
  Move `L4_TRANSviii_b_R3.lean`, `L5_landTransport_R3.lean`,
  `L5_landTwoSided_R5.lean`, `L5_landVertexDigit_repair.lean` (+
  `L4_TRANSviii_a_R5.lean` iff Q-7 says yes) per §2.5 + §3.4's four constraints
  (the VertexDigit reversal guard is EXECUTION-BLOCKING: re-verify the two HC1
  imports of `L5_landVertexDigit` still resolve BEFORE and AFTER). README
  entries with supersession pointers; full build + AxChk byte-compare; update
  the golf-ledger R2 line and the baseline-header caveat via a dated addendum
  (never rewrite the frozen baseline files). Deps: none. Difficulty:
  routine-opus. Size: 0 proof lines.
**CL-25** — post-sweep audit + records.
  (i) Repo-wide duplicate-declaration audit: re-run the A26-style census —
  assert NO fully-qualified name is declared in two live modules (script:
  extract `theorem|def|structure` names per file, group, diff); expected
  residue: the 19 live root-namespace MovesGr files (a NAMING smell, NOT a
  collision — namespacing them is repo-prep batched with sign-off, OUT OF SCOPE
  here; record only). (ii) Update PROJECT_STATE.md (HC1 census 2 → 0/refenced;
  MovesGr live census; the "TEN corpus-wide" wording caveat gets the corrected
  corpus-wide count), HC1/MANIFEST.json (`as_built` refresh: C6/R6 lines),
  MovesGr/MANIFEST.json, golf ledger R2/R3 closure notes (R3 = MovesT E5, NOT
  ours — record "R2 executed, R3 untouched, owner MovesT"). Deps: CL-19 or its
  fence outcome, CL-21, CL-24. Difficulty: routine-opus.

Dependency spine: CL-06 → CL-14 → CL-19; CL-10 → CL-11 → CL-12 → CL-13 → CL-14;
CL-07 → CL-08 → CL-09 → {CL-14…CL-18} → CL-19; CL-02 → {CL-03 | CL-05};
CL-21 → CL-22 → CL-23; CL-01, CL-04, CL-10, CL-20, CL-21, CL-24 have no
prerequisites and can launch in parallel on day one.

Count: 25 units (5 C6, 15 R6, 3 MovesGr, 2 Moves), of which 4 are adjudications
(CL-02, CL-06, CL-22, + Q-7 inside CL-24) and 2 conditional (CL-03/CL-05
mutually exclusive; CL-23).

---

## 5. RISKS (each with its countermodel/probe unit)

**R-1. NCL (10) could be FALSE.** The whole R6 closure rides on it; T8's
subgroup-A construction is circumstantial evidence the original provers DODGED
kernel-triviality rather than proved it. If CL-10 finds a cancellation:
(i-b) fails at packE (two-level countermodel per §3.2), the POSITIVE FINDING in
R6's file is WRONG at its "(i-b) transports from T4" step, and R6 escalates back
to adjudication with three fallbacks — window-guard (i-b) to NCL-verified blocks
(vacuity risk: must stay non-trivial), add NCL as a named pack law (statement
change on CarrierPackR consumers), or re-fence R6. Probe: CL-10, BEFORE CL-11/12.

**R-2. The mod-p reduction step of CL-12 has a real gap candidate.** gaussVal
(digLift) = 0 gives SOME unit coefficient, but the mod-p reduction d̄_c is
nonzero only as a POLYNOMIAL — its degree may drop, and the CL-11 induction must
tolerate deg d̄_c < deg Φ̄₀ with NO lower bound. CL-11's statement is written with
exactly that tolerance; the E-phase writer must NOT strengthen d̄ to full degree.
Probe: covered by CL-10's mechanism survey.

**R-3. The repaired dichotomy (4) could STILL be false** — ScratchC6's shallow
mechanism (digit lines over F_Q ⊊ K_top) may survive the address re-typing, in
which case fullness needs the digit-field factor too. Probe: CL-04 runs BEFORE
CL-02 commits to R-b, and CL-05 never launches without CL-04's report.

**R-4. The compiled Tower countermodel (CL-01) may be unbuildable at sane cost**
(Tower's per-move certificate fields are heavy). Mitigation: capped attempt,
BLOCKED-with-artifact outcome feeds Q-2; the adjudication can rest on the
Lean-core certificates (1)-(2) + the math-level record.

**R-5. Quarantine breakage via a stale importer census.** The A7 precedent:
chunk reports mis-stated import facts that had drifted. Mitigation: §3.4
constraint 2 (grep at execution time, per file), the VertexDigit
reversal guard (execution-blocking check in CL-24), and full-build + AxChk
byte-compare as the acceptance gate for CL-21/CL-24.

**R-6. `L2_degZero_subring` v1 is sorry-FREE** — quarantining a proved file
under an "R2 sorried-superseded" banner would misstate the record. Mitigation:
CL-21's pre-step byte-diffs the two statements and writes the true reason
(same-name supersession after the add_def re-key) into the README entry.

**R-7. The A17 edit ripples.** LSTStmt' is imported by R2/R3/R5/R6 and mentioned
by kernels 2a/2b's hypotheses (`hlst : LSTStmt' p K` in `LSTib_offBlock_pincer`).
Adding the (i-b) hypothesis row CHANGES what the pincer kernel refutes — after
CL-06, kernel 2b documents the PRE-repair defect and its hypothesis no longer
matches the live def. Mitigation: CL-06 re-types the kernel against a local
frozen copy of the old (i-b) (e.g. `LSTStmt_pre_A17'` private def) so the
refutation record stays compilable and honest; this is part of the ratified
edit, not an afterthought.

**R-8. wE's Nat.find needs decidability + a ℕ-bound.** `B γ ≠ 0` over `grQ γ`
is not decidable; use Classical.dec + `Nat.find` on the ∃-form, and note the
populated-level set needs NO upper bound for find (only nonemptiness). If the
WithTop ℚ plumbing turns ugly, fall back to `sInf` on `{q : ℚ | …}` with the
lattice discreteness from LAT giving attainment. CL-08's writer picks one and
records why.

---

## 6. ORCHESTRATOR QUESTIONS (decisions this blueprint cannot make)

**Q-1 (C6, statement fence — Asvin queue Q3).** R-a (minimal honest restate) vs
R-b (address-typed dichotomy) vs fence-hold? Recommendation: run CL-01 + CL-04
first, decide on their reports. R-b is the only option that keeps MOVES
2160-2165's dichotomy as a formal statement.

**Q-2 (C6).** May the C6 adjudication rest on the math-level shallow instance +
the Lean-core collapse certificates, or is a COMPILED tower countermodel
required before the fence moves? (Campaign precedent allows machine-verified
analysis in lieu of a compiled negation when inhabitation is expensive — cf. the
E-phase fence records — but the "no sorried universal without a
countermodel-construction attempt" rule requires at least CL-01's attempt.)

**Q-3 (R6/A17, statement fence).** Ratify the (i-b) repair: VARIANT A
(hfin + hsupp, T4/C1 parity — recommended) or VARIANT B (hsupp only)? Plus the
DEFECT-2 no-change scoping record, and the R-7 kernel-freezing edit.

**Q-4 (R5).** Disposition of `EQ2lawIfREL1'` after CL-20's vacuity certificate:
keep typed-only-with-record (recommended; zero consumers at HEAD) or re-scope
the antecedent now? Re-scoping touches the MovesR unparking design — deferring
keeps this area self-contained.

**Q-5 (MovesGr).** The two live FAITHLESS partials: quarantine-with-record
(recommended), keep-as-is, or repair-with-new-hypotheses (triggers a fence
round + CL-23)? Note the HELD-unit precedent: certified-unprovable content in
this corpus is kept as MANIFEST records + certificates, not as live sorries.

**Q-6 (R6, scope).** CL-16 can deliver `SecB1Stmt' (packE)` for free. Emit it
as a flagged addition (recommended — it strengthens the eventual REL1 story), or
strictly match R6's three-conjunct statement and bank nothing extra?

**Q-7 (Moves, scope).** Quarantine the FIFTH deprecated file
(`L4_TRANSviii_a_R5.lean`, sorry-free, byte-identical statement to _final, zero
importers, self-declared deprecated)? Recommendation: yes, same sweep — a
sorry-free duplicate is still a census ambiguity; but it is outside the task's
"four files" charge, hence flagged.

**Q-8 (sequencing).** The MovesGr/Moves quarantines (CL-21, CL-24) are pure
hygiene with no math dependencies — execute immediately, or hold for a single
repo-prep batch with the (out-of-scope) A26 root-namespacing sign-off? This
blueprint recommends immediate execution: every day they stand, censuses stay
caveated.

---

*Blueprint ends. 25 units; hardest: CL-11/CL-12 (NCL — the one new theorem),
CL-14 (the (i-b) transport), CL-05 (conditional dichotomy), CL-01 (tower
inhabitation). Every load-bearing status claim above was re-verified by reading
the file at HEAD on 2026-07-30; where a ledger and the tree disagreed (R6 sorry
line, VertexDigit A/B labels, L2_degZero_subring v1 sorry count), the TREE was
taken as ground truth and the discrepancy is recorded in place.*
