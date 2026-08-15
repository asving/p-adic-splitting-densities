# GLOBAL CONVENTIONS AND AUTHOR BRIEFS — 2026-08-15

**Role:** the CONVENTIONS CZAR document (owner directive, Asvin 2026-08-15: one agent makes
the uniform choices of conventions and strategies BEFORE the remaining chapter blueprints
are authored in parallel, so the parallel authors cannot diverge).
**Governs:** all chapter blueprints not yet authored (B §10-finisher, C, E, D, F, I) and the
repair queue against committed ones (as PROPOSED-AMENDMENTs only — this document edits
nothing committed).
**Authority:** subordinate to `docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md` REVISION 2 (the
node schema and fleet protocol) and to the landed `leanfinal` API; where this document and a
committed blueprint disagree, the disagreement is recorded here as a PROPOSED-AMENDMENT and
the committed text stands until repaired at the leanspec-stub stage.
**Authored:** 2026-08-15, Opus arm (conventions czar). CODEX CROSS-READ OWED, like every
planning artifact of this week.

---

## PART I — GLOBAL CONVENTIONS (GC-1 …)

Format per convention: DECISION (imperative, one sentence) · RATIONALE · SUPERSEDES/REPAIRS ·
BINDS.

### GC-1 — THE H₀/BASE-HEIGHT PIN: SIDE-LEFT-ENDPOINT (`sideMin`) EVERYWHERE

**DECISION.** Wherever a residual polynomial's height argument `H₀` is pinned, pin it at the
side's **left endpoint**: `npHgt φ f (sideMin φ f u ℓ h) = (H₀ : ℕ∞)` — never at abscissa `0` —
and state transport/congruence lemmas convention-free (`H₀ < N` only, the B.77 pattern) so they
serve any consumer.

**RATIONALE.** This adopts CHAP-B's own defect notice A-§9.1/D-§9.1 as the global rule. B.28/B.29/
B.30 define `resPoly` and prove its correctness clauses under the `sideMin` pin; the abscissa-`0`
pin agrees with it exactly when the side contains abscissa `0` (always on a pure one-sided
polygon, never on interior/right sides of a multi-slope polygon), and on interior sides the
abscissa-`0` pin feeds read heights `H₀ − u·k` strictly ABOVE the side's line, making every
`resCoeff` junk-`0`, `resPoly = 0` (never `Separable`) — so `hsep`-style hypotheses become
unsatisfiable and `NeedsDescent`-style predicates spuriously true. The `sideMin` pin is the one
under which the correctness layer is actually proved, and it is the corpus's own convention
(`EFF.HE3.14`'s residual coefficient reads at the λ-line through the side's endpoints).

**SUPERSEDES/REPAIRS.** Repairs committed CHAP-B nodes B.63 (`hsep`), B.65, B.73 (the
`NeedsDescent` definition body), B.74 (statement gloss) — see PROPOSED-AMENDMENT PA-1 (Part II).
No CHAP-B §9 signature changes (B.77's `resPoly_congr` is convention-free; B.79/B.80/B.82 consume
`NeedsDescent` by name). Nothing in G or H reads a polygon, so neither committed chapter is
touched.

**BINDS.** B §10-finisher (its gates must fire B.82 through the REPAIRED pin), C (every tower
level's residual read), E (any node consuming HE6's slot-seam evaluations), and any future node
that mentions `resPoly`/`H₀`. Where a chapter genuinely needs the abscissa-`0` quantity (window
visibility — B.75's `Visible` is correctly pinned at abscissa 0 because it bounds EVERY consulted
height), it must use the visibility API, not the residual-read API; the two are different objects
and GC-1 keeps them apart by name.

---

### GC-2 — POLYGON REPRESENTATION: THE CLEARED SUPPORT FUNCTION, VERBATIM AT EVERY LEVEL

**DECISION.** The Newton polygon is represented ONLY by CHAP-B DECISION D-1's three objects —
heights `npHgt : ℕ → ℕ∞`, the cleared support value `suppVal φ f u ℓ : ℕ∞` (an `inf` of
`ℕ`-linear forms over `Finset.range`), and sides/slopes/lengths/vertices as **derived predicates
on the argmin set** `onSide` — and chapter C's level-`r` polygons REUSE these declarations
literally (applied to the level-`r` development in the level-`r` normalization), declaring no new
polygon type.

**RATIONALE.** D-1's criterion C7 is the licence: the cleared form is invariant under
`(u,ℓ,c) ↦ (cu,cℓ,c·)`, so one predicate serves every order once the level-`r` heights are
`ℤ`-valued via the `e₁⋯e_{r−1}` normalization (`EFF.HE3.10`, `.20`; `EFF.HE6R1.18`'s level-2
dictionary), and the level-2 translation identity `EFF.HE6R1.13`(b) is a statement about exactly
this object. A second polygon representation in chapter C would force a bridge layer that D-1's
criterion C5 shows is where real defects live (the quarry's 1744-line `HullStability` repair
exists because `Finset`-of-points is not canonical). No `ℚ` in any statement; no hull object; no
convexity import — every consumer is an argmin statement.

**THE ONE OPEN CARRIER QUESTION, ruled narrowly.** B's `npHgt` is `ℕ∞`-valued. At level `r ≥ 2`
the normalizer `ϖ = x^{i₀}π^{a₀}` can have `a₀ < 0` (`EFF.HE6.11`: `ϖ ∈ K₀[x]`, not `O[x]`), so a
naive level-`r` height could be negative. **RULING:** chapter C must arrange its level-`r` height
function to be `ℕ∞`-valued by construction (fold the normalizer's offset into the cleared pair,
the same move that clears denominators — the translation identity `EFF.HE6R1.13`(b) with `c_g` is
the mechanism), and must state a reconciliation lemma identifying its level-1 instance with B's
`npHgt`/`suppVal` definitionally. If C's author finds a node where `ℕ∞` provably cannot carry a
needed height, the fallback is `WithTop ℤ` **with a simp-bridge to the `ℕ∞` instances** — that is
a DECISION block in C plus a flag to this document, not a silent generalization.
**CONFIDENCE: medium-high** on the `ℕ∞`-by-construction leg (the corpus keeps its `dv_r`
ℤ-valued and the offsets telescope, but no one has written the Lean carrier yet); the
alternative is recorded above rather than silently absorbed.

**SUPERSEDES/REPAIRS.** Nothing committed; codifies D-1 as global. The D-1 FALSIFIER protocol
(a node that provably needs the hull as a `List`/object ⇒ extend at B.19/B.20 with a bridging
lemma, nothing else changes) is carried as the global escape hatch.

**BINDS.** B §10-finisher, C (hard), E (T2's ladder reads slot-seam evaluations — support-
function statements per D-1 criterion C2), D and F (any polygon mention routes through these
names; expected rare).

---

### GC-3 — THE (e,f) IDEAL-THEORETIC API: PRIMED GENERATION, RANK FORM, WITH NAMED RECONCILERS

**DECISION.** Every ideal-theoretic ramification/inertia statement uses the **primed** mathlib
generation in **rank form** — `(IsLocalRing.maximalIdeal S).ramificationIdx' R`,
`(… ).inertiaDeg' R`, target `Module.finrank R S` — as already landed in
`leanfinal/Uniformity/Quarry/RamificationInertiaLocal.lean`
(`Ideal.ramificationIdx_mul_inertiaDeg_eq_finrank_of_isLocalRing`); any touchpoint with the old
`(p, q)`-keyed generation reconciles through the two mathlib lemmas
`Ideal.ramificationIdx_eq_ramificationIdx'` and `Ideal.inertiaDeg_eq_inertiaDeg'`, cited by
exactly those names.

**RATIONALE.** Verified at the landed file: our pin (`v4.31.0`, mathlib mid-migration) carries
both generations; the rank-form fundamental identity is stated in the primed generation, upstream
renamed primed→unprimed in Aug 2026, so the primed names are the future-proof spelling at our rev
AND definitionally FLT's post-rename unprimed ones (the quarry header records this). Rank form
(`finrank R S`) rather than fraction-field form is what the tower chapters consume. Mixing
generations across parallel chapters would make `e·f`-identities fail to unify at weld time.

**KEPT APART, on pain of HYP.01.** `leanfinal`'s polynomial-level `ramIndexOf` / `inertiaDegOf` /
`efPair` (the gcd-of-norm-valuations engine under `typeOf`, over the ORDER `AdjoinRoot g`) is a
DIFFERENT API from the ideal-theoretic primed pair (over the maximal order/DVR). The bridge
between them is exactly `HYP.01` (`typeOf` faithfulness, **[CORE-SET]**, open) plus `HYP.12` (the
`(e,f)` ordering convention, [CORE-SET]); **no chapter may silently identify the two**. A node
needing the identification states it as an explicit hypothesis or returns `BLOCKED: HYP.01`.

**SUPERSEDES/REPAIRS.** Codifies the Quarry files' committed choice; nothing to repair.

**BINDS.** All chapters; C and E most (tower `e·f = finrank` chains); I (the faithfulness node
speaks both languages and owns the bridge statement).

---

### GC-4 — THE σ/TYPE DICTIONARY: `FactorizationType` NORMAL FORM + DEGREE CONSERVATION

**DECISION.** Every σ-valued output in every chapter is a `Uniformity.Density.FactorizationType`
(the landed multiset-of-`(e,f)` type), produced by a NAMED dictionary function per chapter (the
CHAP-H §11 `stageSigma : GenreDatum → StageLeaf → FactorizationType` / `composedSigma` pattern;
CHAP-B's order-1 read `typeOf g = ⟨{(ℓ, m·d)}⟩` pattern), and every dictionary function ships a
**degree-conservation lemma** (`(dict …).degree = <block degree>`, the `stageSigma_degree` /
`typeOf_degree` pattern) as its mandatory invariant.

**RATIONALE.** Three chapters already speak σ in three registers (H's stage leaves, B's typeOf
values, E's ladder outputs); the only landed common coin is `FactorizationType`, and degree
conservation is the one invariant every register can check locally, catching mis-assembled
multisets at the node rather than at the weld. Inductive leaf-label types (`StageLeaf`,
`CapBranch`) are allowed as dictionary DOMAINS — they make case analysis decidable — but never as
the σ output carrier; strings/lists/parallel encodings are forbidden outright.

**ORDERING IS NOT LOCAL.** Multiset normalization and the `(e,f)` component order are `HYP.12`
[CORE-SET]; a chapter that needs an ordering property states it against the landed
`FactorizationType` API (`FactorizationType.ext`, `degree_mk_add`) and never re-decides the
convention. σ read through `monicFactors` (total on monic polynomials, no `disc ≠ 0` needed) is
the default read — see GC-9 for the quantifier consequence.

**SUPERSEDES/REPAIRS.** Nothing committed; unifies H §11 / B §7 / E's future ladder outputs.

**BINDS.** All chapters; E's ladder terminal nodes and C's composed-stage σ laws MUST expose
their outputs through a dictionary of this shape (F's weld faces consume them by name).

### GC-5 — GENRE/STAGE CARRIERS: GenreDatum/StageInterface ARE THE INTERFACE
STATUS: stub.

### GC-6 — NAMESPACE / FILE LAYOUT / ENVIRONMENT TAGS
STATUS: stub.

### GC-7 — TOWER QUANTIFIER AND CARRIER DISCIPLINE (chapter C)
STATUS: stub.

### GC-8 — TEETH DISPOSITION VOCABULARY AND REGRESSION HOMES
STATUS: stub.

### GC-9 — STATEMENT-STRENGTH DEFAULT: EVERY-LIFT DECIDEDNESS
STATUS: stub.

### GC-10 — TRANSCRIPTION-GRADE FOR T-UNIT CHAPTERS (D/F/I)
STATUS: stub.

### GC-11 — (reserved: cross-read findings)
STATUS: stub.

---

## PART II — PROPOSED-AMENDMENT LIST
STATUS: stub.

---

## PART III — PER-CHAPTER AUTHOR BRIEFS

### BRIEF B-FIN — chapter B §10 finisher
STATUS: stub.

### BRIEF C — TOWER GRAMMAR
STATUS: stub.

### BRIEF E — σ-LADDER MASTER
STATUS: stub.

### BRIEF D — GAUGE + CERTIFICATE T-CHAIN
STATUS: stub.

### BRIEF F — GRT WELD LAYER
STATUS: stub.

### BRIEF I — CAPSTONE AND CONDITIONALITY
STATUS: stub.

---

## PART IV — ITEMS FLAGGED FOR ASVIN (0d checkpoint)
STATUS: stub.

<!-- RESUME: next item = GC-5 (carriers) .. GC-11; orientation reads DONE (B/G/H front matter, D-1..D-4, A-§9.1, H §15/16, Statement.lean, Quarry primed, HYP.01/12/36/137, Display A, append #54 theta-trap, EFF headers) -->
