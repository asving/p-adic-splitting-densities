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

### GC-5 — GENRE/STAGE CARRIERS: `GenreDatum` / `StageInterface` ARE THE ONLY CARRIERS

**DECISION.** CHAP-H's committed `GenreDatum` (H.01: `(Q; e₁, f₁, μ; h, entry)` with the
`GENHN.CLASS`(i) side conditions as fields) and `StageInterface` (H.09: `stageWindow`,
`stageLoss`, `entryCodim`, `slack`, `bracket`, `drainFrac`, `stageSigma` + the hypothesis fields
`hS`/`hwin`/`hprice`/`hbracket`/`hdrain_nonneg`/`hdrain_le_one`/`hsigma`) are the binding
interface for composite-stage data; no chapter may declare a parallel carrier, and new fields
enter only by RE-PLAN to the orchestrator plus a dated amendment here (H.09's own `exactDrain`
precedent: *"a node that needs the exactness identity must return RE-PLAN for an `exactDrain`
field, not assume it"*).

**WHO DISCHARGES WHAT (the field-by-field assignment).** "DISCHARGE" = prove the field's content
for a class of instances, so downstream consumers instantiate rather than hypothesize.

| field(s) | ledger | status | owner |
|---|---|---|---|
| `hwin`/`hprice` (`(CS-1Q.a/b)`) | HYP.36, CARRY | NO universal discharge anywhere (obstructed for embedded/mixed genres, `EFF.GENIND.197/.199`) | per-genre instances only: H owns the two standalone quartic genres (`stageLoss = 0`); **C may add composed-genre instances**; a node needing `(CS-1Q.b)` for an embedded/mixed genre returns `BLOCKED: HYP.36` |
| `hbracket` (`(CS-2)`, MASS normalization) | — | numeric certificate at order 1 (H.21) | **C** discharges at composed stages where its tower grammar proves the bracket; MASS normalization is mandatory (the ghost fibre `\|K\|^{c(μ)κ}` — `EFF.GENIND.64`) |
| `hdrain_nonneg`/`hdrain_le_one` | — | trivially instantiable | any chapter's instances; the EXACT drain (`CS-EXACT`) is deliberately NOT a field — RE-PLAN if needed |
| `hsigma` (`(CS-3)` degree half, `μ = 2`) | — | proved at μ = 2 by H §11 | **E** extends the σ-decision content along the ladder (T2's business); the σ-decision at `μ ≥ 3` is `BLOCKED: HYP.81` for everyone |
| `stageSigma` (the σ value) | — | data | filled through GC-4 dictionaries only |

**THE ENTRY POINT FOR B AND E IS H §8 (H.51–H.58), NOTHING ELSE.** H-14 executes the cut's
`H → B` split at unit granularity: the slot/lift layer (H.51–H.58, incl. `stageLift'` — note
H.54's `normIdx` is WITHDRAWN and must not be consumed) is placed first among H's algebraic
sections and depends on nothing later; chapters B and E may consume H.51–H.58 by name without
consuming anything else in chapter H. Consuming any H node outside H.51–H.58 from B or E is a
blueprint defect (it re-creates the backward arc the split removed).

**RATIONALE.** H's schema-first architecture is the committed, signed transcription of the
corpus's own conditionality (the fields with no teeth are exactly the capstone's conditionality,
H.09 TEETH); parallel carriers would fork the conditionality bookkeeping and make Display A's
conjuncts untraceable. **SUPERSEDES/REPAIRS:** nothing; codifies H §3 + H-14 as binding on B/C/E.
**BINDS:** B §10-finisher, C, E (hard); D/F consume `stageSigma` outputs only, via GC-4.

---

### GC-6 — NAMESPACE, FILE LAYOUT, ENVIRONMENT TAGS, AND THE LEANSPEC NAMESPACE

**DECISION.** Six sub-rules, all mandatory:

1. **Files:** one Lean file per node, `leanfinal/Uniformity/Chap<X>/<X><nn>.lean`, module
   `Uniformity.Chap<X>.<X><nn>` — the LANDED convention (`ChapG/G05.lean`; micro-nodes suffix a
   letter: `G30a.lean`). Chapter roll-up `Uniformity/Chap<X>.lean` imports node modules in
   topological order; `Uniformity.lean` gains one line. (CHAP-G's blueprint text §0.2 says
   `Uniformity/G/G<nn>_<slug>.lean`; what LANDED is `ChapG/G<nn>.lean` and B/H codified it —
   the landed form governs, no slug.)
2. **Namespaces:** new *definitions* live in a per-chapter sub-namespace of
   `Uniformity.Density` — assigned here, collision-free: G = `.Menu` (landed), B = `.Leaf`,
   H = `.Induction` (committed), **C = `.Tower`, E = `.Ladder`, D = `.Gauge`, F = `.Weld`,
   I = none** (I states theorems about landed capstone objects only, directly in
   `Uniformity.Density`). New *theorems about landed objects* live in the namespace that owns
   the object (`Uniformity.Density` or `Uniformity.Hensel`). Another chapter's sub-namespace is
   READ, never extended.
3. **Environment tags are chapter-prefixed from now on.** The bare tags `ENV-A`/`ENV-B`/`ENV-C`
   are RETIRED for new chapters: they already mean DIFFERENT bindings in two committed chapters
   (G's ENV-A binds `[Finite (ResidueField O)]`; B's ENV-A deliberately does not — B §0.1 is the
   repair of G's stage-0e defect D4). New chapters declare `ENV-<X>1 … ENV-<X>k` (the CHAP-H
   pattern) with the full `variable` block quoted in their §0.1, and may alias committed blocks
   by exact reference ("ENV-C1 = CHAP-B's ENV-A′, verbatim").
4. **Minimal binding is the law** (the chapter-G D4 lesson): `[Finite (ResidueField O)]` only
   where a node counts or names `Res`/`Coeff`/`proj`/`residueCard`/`DecidedAt`-family objects;
   `[IsAdicComplete …]` only where a node lifts through Hensel; `π` always as data with
   `(hπ : Irreducible π)` as an explicit hypothesis where needed (landed precedent
   `Drainage.lean:85`, `StrongHensel.lean:244`, `DensityAPI.lean:124`). Environments are
   declared per NODE, not per section (B's A-§9.4 lesson).
5. **One PUBLIC declaration per node**; private helpers below it in the same file; a reusable
   helper triggers RE-PLAN, never a silent second public name.
6. **Leanspec stubs wrap in `namespace Leanspec<X>`** (CHAP-B H-13's repair), one file
   `leanspec/Leanspec/Chap<X>.lean`, never re-declaring contract names inside `Uniformity.*`
   (chapter G's stub file did, and accumulated 32 has-already-been-declared collisions, growing
   per landing). Definition/structure bodies land real, theorems land as `axiom` stubs, and the
   gate order is CHAP-H §15's: (a) elaborate the declared fragile signatures first, (b) land the
   `def` bodies, (c) run the chapter's `#eval` numeric block at `q = 2` AND `q = 3` against the
   blueprint's expected values, (d) only then sign the `axiom` stubs. The 0e type-diff runs per
   declaration against the fully-qualified `leanfinal` twin.

**RATIONALE.** Every sub-rule is a committed chapter's post-hoc repair promoted to a pre-hoc
rule; the two divergences it settles (ENV-A collision, G's stub-collision structure) are exactly
the class of thing parallel authors would each re-decide. **SUPERSEDES/REPAIRS:** retires the
bare ENV-A/B/C vocabulary for NEW chapters (committed texts unchanged); see PA-2 (leanspec ChapG
collisions) in Part II. **BINDS:** all chapters + the stub-landing agents.

---

### GC-7 — TOWER QUANTIFIER AND CARRIER DISCIPLINE (chapter C, binding E where it touches levels)

**DECISION.** The complete-DVR bundle `O` is fixed ONCE, at the standing-environment level, for
an entire tower — a tower level is DATA over `O` (a structure carrying the level's key, its
residual field, and its normalization), never a re-quantified new DVR, never a new `[Field K]`
variable smuggled in mid-proof; and residue-field enlargement is represented by the CHAP-B
`resField` pattern — `resField φ = AdjoinRoot (φ.map (residue O))` as an explicit
`ResidueField O`-algebra, iterated at level `r` over the previous level's residual key — never by
`IntermediateField` of an algebraic closure (no algebraic closure exists anywhere in `leanfinal`
and D-3/H-2 keep it that way).

**THE ABSTRACT/CONCRETE SPLIT, so C and H compose.** Pure residue-side algebra/counting nodes
MAY be stated in the abstract two-field arena (CHAP-H's ENV-H4: `{F K} [Field F] [Finite F]
[Field K] [Finite K] [Algebra F K]`) — state abstract, instantiate concrete: such lemmas are
applied at `K := resField φ` (and its iterates) through the algebra instance. Any node that must
speak about `O`-polynomials and their level-`r` reductions uses the concrete iterate, so
transport back to `typeOf` stays definitional. The card/finrank bookkeeping enters through B.23's
`finrank_resField` / `Nat.card (resField φ) = residueCard O ^ m` shapes, generalized level-wise
with the same statement shapes.

**RATIONALE.** Re-quantifying `O` per level would detach the tower from `leanfinal`'s capstone
quantifier (one `∀ O` outside, per `Statement.lean`) and make the level-`r` results unusable at
the assembly; the `resField` iterate is the only representation under which the level-1 instance
is literally B's committed API. The base-change hazard is real and named: `HE3-BOX-6`'s substitute
ramified base change `O ↝ O[Π]/(Π^ℓ − π)` is "stated too cheaply" in the corpus (`EFF.HE3.44`) —
**any C node that performs a base change of the bundle must carry it as an explicit constructed
`O₂` with its own instances, flag it in FAITHFULNESS, and never silently identify `O₂`-typeOf
with `O`-typeOf.** **CONFIDENCE: high** on fixed-`O`; **medium** on the iterated-`AdjoinRoot`
carrier at depth ≥ 3 (nobody has elaborated a depth-3 iterate; the fallback — a level structure
carrying an abstract `[Field K_r]` with a specified `Algebra` chain and a proof it is the
iterate — is recorded as the alternative and needs a DECISION block in C if taken).

**SUPERSEDES/REPAIRS.** Nothing committed. **BINDS:** C (hard), E (levels of the ladder), B §10
(gates must not introduce per-level DVRs either).

### GC-8 — TEETH DISPOSITIONS: THREE-VALUED VOCABULARY, PER-CHAPTER SUMMARY, REGRESSIONS IN `verification/`

**DECISION.** Every source battery row guarding a chapter's content receives exactly one
disposition from the closed vocabulary
**{Lean theorem · executable regression retained · signed non-applicability}** (with "signed
vacuity disclosure" as the sub-case of the third for hypothesis fields with no teeth anywhere,
per H.09), recorded per node in the TEETH field AND aggregated in a mandatory per-chapter
disposition summary table (the CHAP-G §13 / CHAP-H §16.1 format, with counts); retained
executable regressions live under `verification/` (the landed home — CHAP-G's G.30 precedent
"retained at `verification/`") and are named per node.

**Three riders.** (i) A re-scoped battery (the `HE-BND`-per-R8-1 pattern) carries its re-scoping
in the disposition text — instance evidence is never silently promoted to a law. (ii) A battery
that was FITTED to data carries the fit disclosure (the `HEX3-LAW` "fitted on 14 of 29 pairs"
pattern) so its independent force is stated. (iii) "The fields with no teeth are exactly the
capstone's conditionality" (H.09) is the sanity check every chapter's table must be able to pass:
signed-vacuity rows must reconcile against Display A's conjunct list.

**Battery inheritance per chapter:** B §10 finisher: HE3/HE6/W12 batteries (already assigned in
committed §§3–9); C: the GENTOW1–6 + HETOW sealed preregistration batteries and GENTOW2's
recovered battery; E: T2's battery including the 48 HE6-pin cites (see the E brief's adjudication
trap); D: the T1/T3/T4/T5 batteries incl. T1's battery check 10 (GENTOW2's S2 tower witness);
F: GRTJA/GRTJB/GRTJC/GRTW2/WELDMASTER/LIFTCORNER/SIGMALAW batteries; I: no batteries — its teeth
are the gate nodes (GC-11 rule on numeric gates applies).

**RATIONALE.** G and H converged on this vocabulary independently; codifying it keeps the
capstone's honesty audit greppable across nine chapters. **SUPERSEDES/REPAIRS:** nothing.
**BINDS:** all chapters.

---

### GC-9 — STATEMENT-STRENGTH DEFAULT: EVERY-LIFT `DecidedAt`, REPRESENTATIVE-BASED HYPOTHESES, NO UNIFORM-`N` LAWS

**DECISION.** Three clauses, all binding:

1. **The decided predicate is `leanfinal`'s landed `DecidedAt`, unweakened** (every lift
   `a : Fin n → O` with `proj O n N a = c`; no `disc ≠ 0` restriction) — CHAP-B DECISION D-4(a)
   made global. Where a corpus source's σ is root-read and genuinely needs `disc ≠ 0`
   (`EFF.W12.27`'s struck clause with its equal-characteristic counter-instance,
   `EFF.W12.51`/BOX-7), the Lean statement reads σ through `monicFactors`/`typeOf` instead
   (total on monic polynomials), states the strictly stronger every-lift conclusion, and flags
   the divergence in FAITHFULNESS.
2. **Hypotheses are stated on ONE representative's data and transported** (D-4(b)): a node takes
   a concrete `a` (or block `g`), states window/polygon/residual hypotheses on it, concludes
   `DecidedAt … (proj O n N a)` via the transport layer entered at landed `decidedAt_of_congr`.
   Window-level "shape datum" types on `Coeff O n N` belong to the count layer (C/H), never to
   certificate statements.
3. **No node anywhere asserts a uniform-`N` law** of the form "decided as soon as
   `N > (fixed function of the shape)` uniformly over a family" — that is the bullet `R8-1`
   REFUTED by explicit counterexample (`f = (Φ′ − C)³ + 5^M`, unbounded `M`; `EFF.HE3.67`).
   Certificates are per-member at an explicitly hypothesized `N`, plus separate
   EXISTENCE-of-a-certifying-`N` nodes read off the member's own polygon (the B.81 pattern).

**EXCEPTION PROTOCOL.** Any statement weaker than every-lift, or any family-uniform `N`-claim,
requires an explicit DECISION block in its chapter naming the counter-instance or obstruction
that forces it, plus a cross-read flag — never a silent weakening (parent statement-fence
applies).

**RATIONALE.** D-4 chose the unweakened predicate and H-11 cashed the stronger quantifier as a
theorem; a parallel author who instead imports the corpus's `disc ≠ 0` convention would produce
statements that cannot compose with B's committed §9 or with `leanfinal`'s `DecidedAt`.
**SUPERSEDES/REPAIRS:** nothing; globalizes D-4 + H-11. **BINDS:** all chapters; C's `HT`
transcription and E's ladder certificates most.

---

### GC-10 — TRANSCRIPTION GRADE FOR THE T-UNIT/LEDGER CHAPTERS (D, F, I)

**DECISION.** For chapters whose sources are T-units or ledger rows (D: T1/T3/T4/T5; F: the weld
notes; I: HYP rows + `CAP:`/`COND:` nodes), the EFF canonical statements ARE the spec: every
node's SOURCE cites its `EFF.<NOTE>.<nn>` ID(s) and the STATEMENT transcribes the canonical
effective statement at its recorded scope — **no fresh mathematics without an explicit AMENDMENT
block** (dated, in the chapter file, the CHAP-G §A- precedent), and any strengthening/weakening/
re-derivation is a DECISION block with the source's own text quoted.

**What "transcription grade" does NOT mean.** It does not mean transcribing a verifier's
phrasing (the `GENH4-CAP` `[r2]` lesson: *"re-derive, never transcribe a verifier's phrasing"* —
re-derive trichotomies/case splits from the note's own displays); it does not mean carrying a
source's false-reason-true-conclusion parentheticals (the `WZ-BOX-7` lesson: side with the
conclusion, never state the type-preservation reason); and it does not mean skipping the numeric
leg — see GC-11.

**RATIONALE.** The T-units were accepted under their own effective-text rules; the blueprint
stage's licence there is packaging, not proof invention. D/F/I are also where the capstone's
honest conditionality is assembled, so an untracked "improvement" is a trust-boundary event.
**SUPERSEDES/REPAIRS:** nothing. **BINDS:** D, F, I (hard); C/E inherit the AMENDMENT-block rule
for any unit they transcribe rather than prove.

---

### GC-11 — NUMERIC GATES: TWO PRIMES MINIMUM, `e > 1` AND `f > 1` WITNESSES, EXECUTED PRE-FLEET

**DECISION.** Every chapter ends with gate nodes whose numeric checks run at **`q = 2` AND
`q = 3` at minimum** (never `q = 2` alone), include where meaningful a witness with `e > 1` AND
`f > 1` simultaneously (the CHAP-B §10 shape), and are EXECUTED at the leanspec stub stage
(gate order GC-6.6(c)) before the fleet fires on any node consuming the audited arithmetic.

**RATIONALE.** The G.23 refutation is the project's sharpest recent lesson: a count formula
whose every numeric check ran at `q = 2` was refuted pre-fleet by a brute force at `ℤ_[3]` — the
coincidence-regime trap (same class as HE6's F-1 and H.08's `f₁ = 1` coincidence). The stub gate
cannot catch a wrong-but-well-typed inequality (CHAP-H §15's warning); executed `#eval` gates
are the only mechanical instrument that can. **SUPERSEDES/REPAIRS:** nothing; promotes CHAP-H
§15's recommended gate order and CHAP-B §10's two-prime/`e,f > 1` shape to law. **BINDS:** all
chapters; I's gates additionally re-run the capstone-slice values (chapter G's landed `n = 2`
numbers) as regression anchors.

---

### GC-12 — CROSS-CHAPTER SOURCE-ID HYGIENE: MERGED EFF IDs IN SOURCE FIELDS, DAG ROWS AGAINST HEAD's `DAG_NODES.tsv`

**DECISION.** Chapter SOURCE fields cite the **merged, contiguous** EFF IDs (`EFF.W12.NN`,
`EFF.GENTOW5.NN` — the merges exist as of append #54: 29 specs, 13 merged + 16 fulls); chapter
DAG-addition tables emit rows against whatever IDs exist in `spec/DAG_NODES.tsv` at HEAD
(shard-local where the harvest is stale), carrying the contiguous ID in the `evidence` column so
the remap is mechanical — CHAP-B's H-9 mitigation made global. Re-running `dag_build.py` against
the merges is an ORCHESTRATOR item, not any chapter's.

**RATIONALE.** `spec/DAG_README.md`'s "GENTOW5 and W12 exist only as shard pairs" is stale
(both merged 2026-08-15, append #54); until the harvest is re-run, blueprint rows citing
contiguous IDs read as dangling. Two committed chapters already handled this two different ways
(H refused to transcribe W12; B cited contiguous with shard-local DAG rows) — new chapters get
one way. **SUPERSEDES/REPAIRS:** the stale README sentence (recorded, not edited — 0c artifact).
**BINDS:** all chapters; C most (GENTOW5), plus whoever transcribes W12 (see the C brief).

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

<!-- RESUME: next item = PART II amendments (PA-1 D-§9.1 repair list, PA-2 leanspec ChapG, PA-3 GENTOW2 cut addendum), then briefs B-FIN/C/E/D/F/I, then PART IV -->
