# THE LEAN FORMALIZATION CAMPAIGN (2026-07-28) — master plan

DIRECTIVE (Asvin, /goal): convert the dual-accepted math write-up into a careful
blueprint, break it into many short parallel sections, ~100 agents — opus-4.8
formalizers, Codex semantic verification, Fable-5 escalation for stuck units; a unit
stuck too long feeds back into blueprint refinement or a math-error flag. The
orchestrator holds the whole proof and how each piece fits.

## 0. The target and the ground truth

TARGET: **Theorem U machine-checked in its dual-accepted CONDITIONAL form** — for each
splitting type σ, one fixed R_σ ∈ ℚ(q) with the density identity at every
(REG-p)-satisfying prime, Σ_σ R_σ = 1 — with the open kernels as NAMED HYPOTHESES
(they are ours, not published, so they cannot be axioms), and published statements
axiomatizable per the standing policy (citation + faithfulness entry + guardian
audit; the process has caught two false axioms).

GROUND TRUTH for every statement: the frozen dual-accepted text in
`lean/notes/MOVES_2026-07-24.md` (each note's final rev, per its DUAL-ACCEPTED
record). A Lean statement is faithful iff it says what the note's display says —
the Codex semantic audit is the gate, exactly as in the MovesC six-round discipline.

## 1. The corpus DAG (how each piece fits the proof)

EXISTING (built): `OM/` the classifier engine + the V2/W capstones ·
`Moves/` §B2-DEF's move ledger (54/61) · `MovesC/` §C's Theorem C over the JetSetup
interface (36/36 PROVED) · `MovesGr/` the graded model (option-(a) add_def landing).

NEW CORPORA, one per assembly note, in DAG order (consumer ← producer):

  MovesD  (§D4-R):   T_can trees, branch-indexed fibers, D4R.1-SUM/EV, D4R.2′, D4R.4.
                     Consumes: MovesC's thmC interface (Theorem C at Z = ⊤).
  MovesSp (§M-SPECIES): the (G1)–(G6) catalogue, SP-DAG, the 53-letter n=3 instance,
                     the shift map Sh. Consumes: Moves' species vocabulary.
                     MOSTLY DECIDABLE — the n=3 layer should be `decide`/`Decidable`.
  MovesV  (§V-TABLES): the CTS cell space, tables T, the measured clauses GIVEN the
                     XHD package as a structure of hypotheses. Consumes: MovesSp
                     (cells/menus), MovesD (marked masses).
  MovesT  (§T-ASSEMBLY): VP, TB-CAP per clause, (SIB) as hypothesis, TREE-EXP's
                     read-site recursion, ONE-F, (ns-null)'s proof. Consumes: MovesD,
                     MovesV.
  MovesR  (§R-LEDGER): the base-change obligation STATEMENTS ((a1)–(a6), (b), (d),
                     (e1)–(e5), the (EQ) trio) — a statements-only corpus by design.
  MovesX  (§X-EXHAUST): the T0–T5 index table, (CD), the X.1a chain, the elementary
                     discriminant tail, X.3's assembly with tags. Consumes: MovesSp.
  MovesS  (§S-RESUM): K_e/b_e/ι_e over ℚ(q), (K-TRI)/(K-SUB), the adjugate solve,
                     the (m,c) dispatch, RS.4's checksum. Consumes: MovesV, MovesT.
  MovesU  (§U-SQUEEZE): (BOX-N), (U-n), the squeeze, THEOREM U with (REG-p) and the
                     full hypothesis ledger as a structure. Consumes: MovesS, MovesX,
                     MovesD.

HARD CORES (phase 3, blueprint-first, after phase-1/2 experience):
  HC-1: §B2-DEF's tower induction (the transport bijections at every level) over
        Moves/MovesGr.  HC-2: the JetSetup-existence bridge (MovesC's interface
        instantiated from the OM engine; Montes existence/uniqueness axiomatizable).

## 2. The unit-spec format (every blueprint emits these)

Per unit: `id` (Corpus.name) · `file` · `statement` (full Lean, against the corpus
Defs) · `moves_ref` (the note display it encodes, quoted ≤ 3 lines) · `deps` ·
`sketch` (the informal proof in ≤ 8 lines, from the note) · `difficulty`
(easy/medium/hard) · `hypothesis_fields` (which open kernels/packages ride as
hypotheses — NEVER silently strengthened or dropped). Units SHORT: one display,
one lemma, ≤ ~40 lines of expected proof; split anything bigger.

## 3. The process gates (per corpus, the MovesC discipline)

  B (blueprint, Fable) → A (Codex semantic audit of blueprint+Defs; REJECT loops
  until ACCEPT — statements must be faithful, non-vacuous, quantifier-exact) →
  E (statement elaboration, scratch sorry-bodies compile) → P (prover fleet:
  opus-4.8 workflows, ≤ ~16 concurrent; fable escalation on failure) →
  V (independent recompile + sorry census + #print axioms per proved unit;
  Lean-core-only expected unless a declared published axiom) → record + commit.

STUCK RULE (the directive's feedback loop): a unit that fails opus AND fable
escalation twice is STUCK → the orchestrator (me) reads the stuck goal and
adjudicates: (i) blueprint defect → refine the unit spec (split/re-state) and
re-audit; (ii) Defs defect → designer round (statement-fence discipline: changes
need sign-off unless additive); (iii) SUSPECTED MATH ERROR → a math-side
verification pass on the source display (the write-up is dual-accepted, but the
machine has refuted 'accepted' displays before — moveReduceCommute, L1_gr_domain);
any confirmed math error goes back to the note + both verifiers.

## 4. Published-axiom policy (unchanged, restated)

Allowed as axioms: Lean core + already-declared (GMN index, Denef cells — measure
route) + NEW published statements ONLY with: the citation, a faithfulness entry in
docs/AXIOM_FAITHFULNESS.md, and a guardian audit. Candidates this campaign will
likely need: Montes existence/uniqueness (HC-2), Krasner continuity bounds (ORC/
X-tail), Hensel (Mathlib has it — prefer the library). The campaign kernels
(WEIGHT-CHARGE, (SIB), E0/(REG-p), HMC, ALIGN, X2-*, the H.6 fences, (JC-INV),
(J-RAT), TRACK-COUNT) are HYPOTHESES, never axioms.

## 5. Wave plan (~100 agents)

  WAVE 1 (now): blueprints for the 5 most tractable corpora — MovesSp, MovesX,
    MovesS, MovesU, MovesD (5 Fable writers, parallel) + the add_def propagation
    (running). MovesR is statements-only (folded into wave 1 as a 6th small job).
  WAVE 2: Codex audits (≤ 6) → Defs designers (≤ 6 Fable) → audit loops.
  WAVE 3: prover fleets per accepted corpus (opus workflows, ~30–60 provers total,
    fable escalations inside the workflow).
  WAVE 4: MovesT + MovesV (they consume wave-3 corpora) — same pipeline.
  WAVE 5 (phase 3): HC-1/HC-2 blueprints + the Moves tail backlog fleet.
  Throughout: stuck-rule adjudications; the ledger below updated per event.

## 6. The campaign ledger (updated per event)

  MovesGr option-(a): IN FLIGHT (the add_def propagation agent).
  Wave 1 blueprints: ALL SIX WRITTEN + COMMITTED (2026-07-28).
    MovesU 11 units (6e/5m) · MovesD 16 (2 hard pre-split) · MovesS 28 (10e/15m/3h)
    · MovesSp 56 (30e/22m/4mh; decide-native n=3 layer) · MovesX 35 (16e/13m/6h)
    · MovesR 21 (15 statements-only + 6 provable; concrete Witt route, no axioms).
    TOTAL: 167 units. Escalation-risk set pre-declared: X's 6 hard (P1 lattice
    counts, ValExt/Krasner archaeology, a0-translation covering), S's 3 hard
    (blockSolve WF-recursion, e0 determinant/inverse), D's 2 (chart uniqueness,
    D13 double count), Sp's 4 medium-hard (each with pre-approved splits).
  Wave 2 audits, ROUND 1 COMPLETE (2026-07-28): 6/6 REJECT — 72 criticals,
    36 gaps total (U 10/3 · S 19/3 · X 14/11 · R 15/6 · D 8/2 · Sp 6/11).
    THE SYSTEMATIC DEFECT (all six): hypothesis structures satisfiable by
    degenerate instances (True-typed tags, Empty index types, False-valued
    predicates) — the audits' non-vacuity charge did exactly its job. Plus:
    two arithmetic transcription errors in X (counterexampled by the auditor),
    circular interfaces in S/Sp (structures assuming their own conclusions),
    R inventing a satisfiable pseudo-statement for REL.3 where the note says
    none is possible. All six writers resumed on batched rev-2 repairs; ONE
    re-audit each per the budget rule. (D and S runners needed the
    foreground-wait resume — the known parking failure mode; Sp too.)
    DOCTRINE FOR ALL FUTURE UNITS (wave 3+ prompts must carry it): a faithful
    interface must be FALSE for instances the note would reject; obligations
    may be open, but their TYPES must pin their content.
  Round 2 (re-audits): U REJECT 4/3 (rev 3 charged with the orchestrator ruling:
    concrete Box N = monic coefficient tuples over ZMod p^N; conclusion split
    classifier-keyed (i) + VP-SOUND-conditional identification (ii), mirroring
    the note's own structure; RegP entry families pinned by cardinality
    equations; pole-freeness explicit in (REG-p)).
  AUDIT-BUDGET POLICY from round 3 on (Codex window ≥72%): intermediate audit
    rounds go to FRESH FABLE instances (decorrelated-enough for statement-level
    checks, zero Codex cost); Codex runs ONLY each corpus's final confirmation
    pass. The per-corpus acceptance bar stays dual: last round must be
    Codex-clean AND a Fable pass on identical text.
  *** MovesX DUAL-ACCEPTED (2026-07-28): rev 4, Codex ACCEPT 0/0 + Fable ACCEPT
  0/0 on identical text (surgical scope verified via git diff; arithmetic
  re-derived by both). FIRST corpus through the full gate. 48 units
  (19e/17m/12h). E-phase (statement elaboration) LAUNCHED. ***
  *** MovesU DUAL-ACCEPTED (2026-07-28, rev 7): Codex FINAL#3 ACCEPT 0/0 on
  rev 6; Fable#4 delta-confirm 0 crit with the sole gap = a stale rev-5 prose
  gloss contradicting the field BOTH verifiers independently requested
  (cl10_vpsound — decorrelated convergence); rev 7 = that one-phrase gloss
  fix, applied by the orchestrator (no statement touched). 13 units. The
  acceptance record: both verifiers clean on the mathematical content of
  identical rev-6 text. E-phase next. ***
  MovesR PARKED (2026-07-28, per adjudication #1's condition): the rev-4
  re-architecture's Codex final = REJECT 15/2 — the CInterface SHAPE is right
  but faithfully TYPING the eleven §C statements needs the full §C carrier
  vocabulary (basis monomials, kappa_r/STR_r, stage indices, piece maps, unit
  lifts) = a real fraction of HC-1's own design. Iterating MovesR now would
  duplicate HC-1's work badly. DISPOSITION: (a) the Witt BASE LAYER (the ~7
  provable, multiply-audited-clean units: conventions, composition law,
  Fsub_card) splits off as a mini-corpus for E-phase + provers; (b) the
  CStatements/GradedCarrier draft is RAW MATERIAL for the HC-1 blueprint
  (wave 5), where MovesR gets re-keyed to the real carriers and re-audited.
  FABLE LEG LANDED (folds in): REJECT 3/4 — but confirms the re-architecture
  SOUND (carrier fields note-supported; CF-triage genuine; criticals LOCAL to
  U26-U28's LST/TYP typings). Deep catch: the jet-additivity clause as typed
  is group-theoretically IMPOSSIBLE (p^N-torsion) — the intended instance
  would FALSIFY REL.1 (the inverse defect of vacuity). RESUMPTION CHARGE
  (wave 5, with HC-1's carriers): re-type TYP's additive object as the
  level-set-digits -> graded-piece composite (MOVES 9401-04/3801-07); price
  the slot-image SPAN not the digit-value set (TYP(b) 3815-21; the F9
  instance a = 2 is the check); link floorB to K.lines with a block-edge
  field + staircase equation; then the 4 gaps. Both verifiers agree the
  missing pieces are CARRIER structure = HC-1's surface.
  ***** THEOREM U MACHINE-CHECKED (2026-07-28). The MovesU fleet: 13/13 on
  the first opus pass (0 escalations, 0 stuck, 0 verify-failures).
  LeanUrat.MovesU.theoremU + .identification PROVED; corpus sorry-free;
  axiom footprint Lean-core only (verified post-rebuild by the orchestrator).
  The statement is the dual-accepted conditional Theorem U: ∃ one fixed
  R_σ family, ∀ p prime satisfying (REG-p), classifier-keyed density → R_σ(p)
  with Σ_σ R_σ = 1, and the VP-SOUND-conditional identification clause —
  over the CL-1..19 CapstoneLedger and the typed interface structures whose
  instantiation is the remaining campaign (the other corpora + HC-1/HC-2).
  This is the capstone TARGET of the master plan, standing as a checked
  conditional theorem exactly as the math delivers it. *****
  *** MovesSp DUAL-ACCEPTED (2026-07-28, rev 5): Codex 0/0 + Fable 0/0 on
  identical text; the Fable leg re-implemented the defs in Python and verified
  every decide target TRUE (closure 53, loops, exclusions, rosters). 67 units.
  Journey: 6/11 -> 2/4 -> split (5/8 vs 0/0) -> adjudicated 1/1 + 0/1 -> 0/0
  dual. THE NOTE ERRATUM (R6 row) now confirmed by four independent auditor
  passes. E-phase launched. ***
  THE CONSOLIDATED FRONTIER (2026-07-28, end of the autonomous horizon):
  three kernels carry every remaining hard-core sorry — (K1) the read-indexed
  D.8 vertex pin (HC-2 U20a/U20b/U22E2 + HC-1 S7(c)/S8/S11a twist class: ONE
  design, both cores); (K2) the mkSigma recursion clause (U7 refuted on real
  seeds — a Defs-design item; U10/U9b/U9c gated); (K3) U18's adjacency
  hypothesis (conditional refutation witness on record). PLUS the sign-off
  queues F-1..F-6 / N-1..N-6 (drafted, machine-justified, awaiting Asvin) and
  the recorded waves: 4 (MovesT/MovesV -> 22 seam entries), the Aug-02 Codex
  ratification batch, MovesR unparking. Every sorry in the repo is one of:
  a queue item above, a seam-contract entry, or a named obstruction kernel.
  N-1/HMC ADJUDICATION (2026-07-28, orchestrator direct read): the note's HMC
  (v) display (MOVES 8198-8221) asserts the PROCESS-DEFINED exact domain
  H(gamma) factors stepwise — the blueprint's definitional chainCount built
  the domain BY the recursion, making HMC true by construction (the 4-line
  proof = the sanity check that the interface over-committed; the mirror
  image of the vacuity doctrine). BLUEPRINT OVER-COMMITMENT (traceable to the
  rev-2 charge wording); the note intact; HMC stays OPEN. Fix: table side
  (T_gamma, G) recursive by definition; process side H(gamma) defined from
  the realized marked events; HMC = the typed link.
  S13 ADJUDICATION (2026-07-28, orchestrator direct read): the note's D.9(d)
  (MOVES 2573-2581) scopes any-scalar realizability to e_read = 1 READS
  ("At any e_read = 1 read... any digit scalar is realizable"), persisting
  along histories; HC-1's S13 conjunct 3 dropped the scope — BLUEPRINT
  OVER-STRENGTH (type i), the note intact. S13 restated with the e_read = 1
  scope; the XE-precedent applies (statement repair post-refutation).
  PHASE-2 CLOSURE DISPOSITIONS (2026-07-28, orchestrator):
  - MovesS: rev 13 = closure by ADJUDICATION — Fable 0-crit three consecutive
    computation-verified rounds; Codex's residual scope criticals OVERRULED by
    direct note reads (per-pool junk-block discipline 12198-12209; consumed
    legs 12205; the J-RAT per-cell presentation = owner [1v] per the note's
    own PLAN-SYNC flag). The deferred Codex leg = a RATIFICATION pass on the
    E-phase Lean statements after the Aug-02 reset. Core -> E-phase.
  - MovesD: rev 9 = the SEAM SPLIT (the TreeModel semantic layer + VerdictModel
    + D4R_CYL consumer + the NPband pin -> a §W4-SYNC contract; they are
    §T-ASSEMBLY vocabulary — Codex's own rev-8 findings demand ties in BOTH
    directions that only MovesT's apparatus can state). Core (certificate +
    E1-E9 + mass laws + gate, repeatedly number-confirmed by both verifiers)
    -> E-phase; Codex ratification post-reset.
  - Verifier-disagreement lesson (for the record): NINE MovesS rounds and
    EIGHT MovesD rounds; every mathematical-content finding converged; the
    non-converging residue was always interface-pinning strength at seams
    whose owner vocabulary doesn't exist yet. The seam-split + adjudicated
    closure is the honest boundary, matching the notes' own owner ledgers.
  CODEX BUDGET AT 90% (post-XE-refutation): remaining Codex = the queued
  closing finals ONLY (MovesS rev 11, MovesD rev 7, the XE mini-audit).
  After those: Codex PAUSED until the window resets (Sun Aug 02); interim
  audits Fable-only; deferred Codex finals batched post-reset. Also:
  runners now get SCRUBBED workdirs (the stale-verdict anchoring flag).
  CODEX BUDGET RE-CHECK (mid-wave-2): 77% — past the conservation threshold.
  Remaining Codex use = FINAL CONFIRMATIONS ONLY (S/U/D running; R re-arch and
  Sp final queued; X's Codex leg DONE at ACCEPT 0/0). No other Codex calls.
  MovesGr option (a): EXECUTED (2026-07-28) — with a STATEMENT-FENCE EVENT: the
    signed-off literal add_def was a Lean TAUTOLOGY (instance elaboration
    re-read the RHS + as the ring's own; repro in MOVESGR blueprint §8.4);
    landed componentwise with identical signed-off CONTENT. Ledger: 19 proved
    + 2 sorried + 5 held; L1_gr_domain_iff_val + L2_degZero_subring PROVED;
    footprints Lean-core only. FLAG FOR ASVIN in the next summary.
  MovesT/MovesV blueprints: deferred to wave 4 by design (consume wave-3 corpora).
  Everything else: PENDING.

  STUCK-RULE ADJUDICATION #1 — MovesR (2026-07-28, after rounds 15/6 → 2/5 →
  15/5 with mostly-fresh findings each round): STRUCTURAL blueprint defect,
  not writer error. §R-LEDGER's clauses are POINTERS into §C machinery
  (LST's chain-weight/initial-form content, DOM, C.0.5, C.1) that has no Lean
  form yet — every attempt to inline a clause's content into a self-contained
  MovesR Prop is necessarily partial, and each audit finds the next missing
  piece. RE-ARCHITECTURE: MovesR becomes a corpus PARAMETERIZED by a
  CInterface (the §C statement bundle over abstract graded carriers — the
  D.3(e)/K1-weight/initial-form vocabulary as a minimal typed interface,
  instantiation = HC-1's deliverable); REL.1 clause slots = the bundle's
  statements at base δ (typed pointers, faithful to the note's own 'mutatis
  mutandis' structure). MovesR's OWN content shrinks to: the Witt base
  conventions (clean since rev 2), the composition law, the (EQ) trio, the
  ledger structure. ONE re-architecture rev + ONE parallel dual confirmation;
  if it fails again → PARK until wave 4 (MovesR is downstream-light: no
  wave-3/4 corpus consumes it). I read Lemma LST directly for this ruling —
  Codex's chain-weight finding CONFIRMED against the display.

  CODEX BUDGET NOTE (checked at launch): 72% of the 7-day window used, resets
  Sun Aug 02. Per the conservation rule (>75% → cut mechanical delegation), the
  wave-2 audits run as SINGLE CONSOLIDATED passes per blueprint (audit prompt
  covers faithfulness + vacuity + quantifiers + hypothesis-fields in ONE charge;
  repair loops batched), with fresh-Fable reads carrying the second leg of the
  dual bar at zero Codex cost. Codex is reserved for semantic verification ONLY —
  no mechanical Codex delegation this campaign.

  WAVE-4 RUNNING RECORD (MovesT 55 units / MovesV 95 units; dual audits per
  round, Codex + fresh Fable on identical text; Codex crit trajectory for
  MovesT: 35 -> 21 -> 18 -> 9 -> 6):
  Round 5 (2026-07-28):
  - MovesT: Codex REJECT 6/6 + Fable REJECT 1/2. The Fable pass VERIFIED the
    entire round-4 union repaired and confirmed the derived rigidity genuine;
    its one fresh critical is the deepest finding of the wave — JOINT
    UNSATISFIABILITY of the rev-5 toy tables against the built
    TreeModel.mem_single: {child_cell at o=none + RootCellsOf + mem_single}
    force one-node-chain state events to be UNIONS of reduction cells while
    {state_cell + presents...} force a proper sub-stratum. Fix named by the
    auditor: scope child_cell to some-states, root children via
    RedCellPartition, pin the toy child(none) window digits.
  - MovesV: Codex REJECT 5/7 (verdict RECOVERED from the orphaned detached
    run — the external ~10-min killer claimed the monitor, not the process;
    parsed from codex_run.jsonl item.completed/agent_message). Per-item
    re-derivation shows most round-4 repairs LANDED (M-1/M-5 repaired, M-3
    partial); residue: the selected-member tie (tgtSk must be represented by
    a continuing roster member), the evt_disj_cell dependent key still
    outcome-splitting, SelRankTie mis-targeted, a TReal-vs-counts recap
    contradiction, + the off-pool WORDING overclaim (xhd_no_orphan permits,
    does not force, off-pool emptiness). CoprimeLiftPack fence CONFIRMED;
    the 95 = 32e/59m/4h census verified. Fable REJECT 0 crit / 3 gap —
    STATEMENT CONTENT CLEAN; G-A is a record-line falsity, not a type
    defect: the auditor PROVED HMCAug derivable from HMC (~30 lines) and
    underivability unattainable for any faithful encoding (the note's
    hypothesis is a conditional, vacuous under HMC) — so the Section-2.G
    "not a consequence" line gets SCOPED, the type stays.
  Rev 6 CHARGED (2026-07-28, two Fable writers, wf_8158eef8-c13): MovesT =
  the joint-unsatisfiability fix + the Codex-5 counter-computed items
  (childless-tower vs ScaleFaithful, trackOf:=0 vacuity, T-E10 hdict
  two-verdict row, T-G1 Realizes contradiction, W4-1 BDY third adjudication,
  SibCount finiteness, 3 gaps). MovesV = the G-A record scoping + G-B/G-C +
  the recovered Codex residue; expected CLOSING rev (statement content
  already Fable-clean).
  CODEX BUDGET RESET (2026-07-28, checked at wave-4 round-5 close): the
  rolling 7-day window now reads 15% used (resets Tue Aug 04) — the
  conservation regime is LIFTED. Consequences executed immediately: (1) the
  deferred ratification batch LAUNCHED (MovesD core vs §D4-R + seam-contract
  types; MovesS vs §S-RESUM with the three adjudicated items re-judged by
  the fresh Codex context — the adjudications were orchestrator rulings, so
  this is their independent check); (2) wave-4 round-6 audits return to FULL
  DUAL (Codex + Fable) rather than Fable-interim-only. MovesSp confirmed
  already dual-accepted (rev 5, 0/0 + 0/0) — nothing owed there.
  RATIFICATION BATCH RESULTS + ADJUDICATION (2026-07-28): MovesD REJECT 5/1,
  MovesS REJECT 5/0 — on ALREADY-PROVED corpora, so statement-level findings,
  each adjudicated by orchestrator direct note reads:
  - MovesD D1 (gamTie's STR factor vs L3's "γ_r = e_r·u*_r + j*_r·h_r"):
    OVERRULED. §C C.0 marks γ "(augmented scale)" (3461); C.1.0(c) + the
    Scale declaration (3598-3645) define stage = STR × absolute; the frozen
    MovesC Node records ustar ABSOLUTE + gam STAGE (the Codex#7 c.1 pushback
    record anticipated exactly this re-flag); lineS/kappaS carry the STR in
    the compensating spots — the shape universes correspond bijectively.
    The ratifier had ONLY §D4-R in context. Repair anyway: a machine-checked
    scale-coherence lemma (SW2) so the convention is checkable.
  - MovesD D3 (PrefIdx image + zbar normalization): core OVERRULED — the
    REV-4 η-granularity design is faithful (the note's η carries digits+ψ;
    zbar is a PRESENTATION choice the note's η never records, so the literal
    history set would OVERCOUNT conjugates; PresentNorm (ii) IS the typed
    anti-collapse law, (i) the totality, both = the open HC-2 dictionary
    pin). Residue ACCEPTED: an abstract-count theorem (image count = the
    policy-free Galois-quotient count under hnorm) to replace the rfl-only
    card_classes as the visible content.
  - MovesD D2 (POL-PIN comment-only), D4 (∅-shape event/mult unwired — the
    note's S(∅,⊤) = FULL BOX vs Lean's ∅; option-level objects exist but
    Presented.event/mult lack the dispatch), D5 (NP-ID = W4-4 "ledger pin,
    no Lean object" while D4R4_all quantifies over the NPband range), D6
    (classifier-side sealed-gate numbers untyped): ALL ACCEPTED — each is
    the campaign's own typed-fields doctrine applied back at us.
  - MovesS: ALL FIVE ACCEPTED. S1: the corpus HAS the (ii-c) gate (AVAgree,
    verbatim-faithful) and the all-active bundle carries it totally, but
    legs_reg types only E0/ACT at consumed pools — the note requires the
    agreement to pass BEFORE read-off at every non-all-active pool (12204-
    12218); typed field legs_read added. S2: deltaFactors collects halted
    members' δ (the note evaluates β only at block-state members; halted =
    factor 1) — SILENT STRENGTHENING; filter to Member.continuing. S3: the
    J-RAT per-cell TYPE must exist even though tables stay owner [1v] (the
    ratifier UPHELD the un-builtness adjudication, demanded the granularity).
    S4: wsh17_pin : Prop is the vacuous-tag defect verbatim — retype to
    W17ii's statable core. S5: PolyGeom's countT/countS have no value laws
    (absorbable into geom) — typed PolyGeomLaws added as premise-variants.
  - THE THREE PRIOR ADJUDICATIONS under independent re-judgment: (a) junk-
    block discipline UPHELD ("not itself a defect", the ratifier's words);
    (c) J-RAT upheld-with-sharpening; (b) consumed-legs re-raised in a
    SHARPER, correct form (the halted-member scope) — accepted. The
    adjudication process survives its first decorrelated audit with one
    genuine sharpening.
  REPAIR EXECUTION: two Fable repair agents (wf_acc27000-fcc), charges at
  MOVESD/MOVESS_RATIFY_REPAIR_CHARGE_2026-07-28.md; acceptance = proofs
  re-run green + ONE consolidated Codex confirm on the applied diffs (the
  definition-change authority's gate); then the W4-SYNC interface-delta note
  feeds the wave-4 round-6 audit charge.
  REPAIRS APPLIED + ROUND 6 LAUNCHED (2026-07-29): both ratification-repair
  agents landed green (full build 8579 jobs; zero sorry in the 7 new files;
  Lean-core footprints; statement fence git-diff-verified; the N2 sealed
  gate stays proved). Two agent-caught improvements over the charge: the D5
  range corrected to L12's piecewise threshold verbatim (the charge's form
  was weaker on the EMPTY branch — Pref = ∅ still demands N ≥ N(∅) = 1);
  S4's impossible literal retype resolved as field-deletion + projection-def
  RS4Chain.wsh17_pin := W17ii (h17 binder byte-identical; no instance can
  weaken it). Interface deltas recorded in W4_SYNC_DELTAS_2026-07-29.md
  (9 items) and folded into every round-6 charge. IN FLIGHT: the ONE
  consolidated Codex confirm on the applied diff (the definition-change
  authority's gate; /tmp/leanconfirm_rr) + the wave-4 round-6 FULL DUAL
  audits (Codex detached t6/v6 + two fresh Fable legs, wf_2c438758-07c),
  round-6 duties: per-row disposition verification, recomputation of the
  writer's 2^9/5^18 arithmetic, held-item judgment, seam-sync staleness.
