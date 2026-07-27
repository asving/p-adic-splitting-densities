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
