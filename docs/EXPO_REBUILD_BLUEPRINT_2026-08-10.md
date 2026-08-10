# EXPOSITION REBUILD BLUEPRINT — the public uniformity writeup — 2026-08-10

**Unit:** EXPO-BLUEPRINT. **Status:** DESIGN ONLY — the site is not touched; the
rewrite executes after the simplification campaign (SIMPLIFICATION_BLUEPRINT
_2026-08-10) reports. **The spec (Asvin, verbatim intent):** context first, then
THE PROOF OUTLINE as the first thing after context, then the Montes algorithm
taught deep enough that the reader can guess the strategy, then the difficulties
with concrete examples, then successive refinement of the outline. Examples and
computations carry the story throughout. **Targets:** `uniformity/paper.html`
(the prose paper) + `uniformity/story.json` (headline/story/panels feeding
`index.html`). **Sources studied:** WRITING.md Protocol H;
`valuated-matroid-invariants/papers/{paper-one,paper-etale}.tex`; the current
site text at HEAD; the accepted-corpus DAG per SIMPLIFICATION_BLUEPRINT §1.

---

## A. DIAGNOSIS (order and narrative, not content — most material is reusable)

**Verdict in one breath.** The page has excellent atoms — eight worked examples,
an honest ledger, a correct squeeze section — assembled in certification-log
order rather than story order: the reader meets machinery and grade bookkeeping
before any outline, the outline they eventually get is the *old pipeline*, and
the proof that now actually exists appears only as a name list in a milestone
appendix.

1. **The outline arrives late.** In `paper.html` the first outline is the
   opening paragraph of "The proof in four movements" — the 12th body paragraph,
   ≈2,000 words of mandatory prose in (≈3,500 if the reader opened the two
   preceding worked examples). Before it: two full sections (context; statement
   + squeeze + status paragraph + 12-row ledger). The prescription wants the
   outline immediately after context.
2. **It is the wrong outline.** The "four movements" (enumerate / tree /
   recursion / visible uniformity) describe the transfer-matrix *architecture* —
   what the Lean development computes. The proof chain that now proves the
   theorem (W-12.D reduction → GENIND.B induction → GENHN stage laws → HE3–HE7
   σ-ladder → GENTOW towers) appears nowhere as mathematics: only in the
   2026-08-08/09/10 milestone entries (≈5,200 words in) as parenthesized names
   with zero content per name. A reader cannot fill in an outline they were
   never given.
3. **The story panel is a chronicle.** `story.json`'s story field is 13
   paragraphs; ¶6–13 are appended session milestones in discovery order — the
   documented anti-pattern (Tao: stream-of-consciousness order). The chain first
   surfaces in ¶10, ≈2,900 words in, again as names. The headline is one
   ≈300-word sentence-pile mixing theorem, grades, dates, and audit counts:
   minimal first-sentence signal.
4. **Examples are stapled on, not generative.** All eight worked examples sit in
   collapsed `<details>`; the mandatory reading path meets zero computations.
   They illustrate after the fact instead of creating the need for the next
   definition (WRITING.md H8: definitions are earned). The one difficulty
   example ((‡), squares mod 8) is mid-machinery in Movement 2; the actual
   difficulties of the real proof (fractional heights at μ ≥ 4; the gauge/wrap
   seam) never appear.
5. **Grade vocabulary is interleaved everywhere.** "Accepted / attempt grade /
   composition grade / not a Lean event" is re-litigated in 20+ paragraphs and
   ~half the total words. Honesty is the house style — but the exemplars show it
   pinned once (a status Convention + one ledger) and then *used*, not repeated.
6. **Reusable as-is (the rewrite is a reordering plus one new section):** the
   question section; the squeeze section; all eight worked examples; the ledger
   (as the boundary section); the polygon figure and residual-polynomial prose
   (as the Montes section core); the H²-dies passage buried in the 2026-08-07
   milestone entry — the best conceptual paragraph on the page — promoted to the
   difficulties section's capstone.

## B. EXEMPLAR LESSONS (the matroid papers; quoted, transplantable)

1. **Results in words first, numbers attached.** paper-one §1.3 "The main
   results, plainly": three families of results stated in prose with theorem
   numbers riding along — the whole outline lands by page 3.
2. **An outline section that carries each leg's WHY.** paper-one §1.4 "The two
   methods, previewed": one paragraph per method, ending in its reason-for-power
   — "The method never looks at Q as a polynomial again after the first step; it
   sees only the lattice… which is why it generalizes… and why it can prove
   dualities." Every node of our outline gets such a why-clause.
3. **Italic per-section overviews with dependencies.** "Overview. This section
   answers the basic question, the measure of a congruence event, once and for
   all… Everything downstream is resummation of these." Purpose + what-may-be-
   forgotten, two lines, every section.
4. **Compress the standard, loudly.** "Everything p-adic this paper uses fits in
   five sentences; the reader who knows them can proceed to §3." License to skip
   = density modulation the reader can feel.
5. **Status as a one-time Convention.** "A statement is called a Theorem… if and
   only if it is proven… A statement whose only support is exact machine
   verification… is displayed as a Computation." Stated once; the body then
   never hedges inline. Our analogue adds one rung: Proved-in-Lean > accepted
   prose (2-clean hostile bar) > computation > conjecture — defined once, used
   silently.
6. **"How to read this paper."** Explicit layered paths per reader type
   (formulas / probability / dualities). Ours: theorem-hunter / algorithm-
   learner / verification-auditor.
7. **Honesty as organized content, not tone.** paper-etale §1.1: "the precise
   honesty structure of that frontier — which statement is proven, which is
   machine-verified, which is refuted — is the main content of this paper." The
   boundary is a *section with a shape*, not scattered disclaimers.
8. **One conceptual dictionary section.** paper-etale §1.2 "The curve-
   singularity reading" gives the reading that makes every later object
   meaningful. Our analogue: "why wildness is cochain-level" — H²(ℤ/E, k×) has
   order gcd(E, |k|−1), prime to p, so the wild class *dies* and all wild
   information lives at cochain level; explicit ledgers, not class machinery.

---

## C. THE NEW ARC (paper.html section by section; story.json follows §C6)

### C1. Context and statement (tightened; mostly existing text, reordered)

Keep: the question (¶1–2 of the current page), tame-in-two-inputs, BCFG
conjecture, G–Wei–Yin tame theorem + open wild case, the target-theorem box, and
the squeeze in compressed form (the bracket (0) and "the measure theory is
spent" — the ledger and status paragraph MOVE to §C5's boundary section). The
quadratic p=2 worked example stays here, *expanded by default* (not collapsed):
it is the generator — "wild = decisions at digit depths the tame theory never
inspects" — and everything later deforms it. Budget: ≤ 900 words of mandatory
prose + the one example. Ends with one sentence of strategy ("run the
factorization algorithm on all polynomials at once and count"), which §C2
unpacks. The five-sentence-preliminaries device (B4) replaces the current
scattered p-adic recalls.

### C2. THE PROOF OUTLINE — the new section; skeleton drafted here

Placement: immediately after C1. Form: five anchored nodes, one paragraph each,
each closing with what the reader should hold; no machinery, no grades. The
section opens: "The proof is a reduction, an induction, and three theorems that
feed the induction; here is the whole shape." Anchor names are the notes' own
(L1: verbatim-echoed, greppable back to the corpus).

**Node R — the reduction (THEOREM W-12.D).** Fix the degree n. Suppose given,
at every prime at once: (A1) *menus* — at each truncation level, an exact
disjoint family of decided digit-cylinder classes per splitting type whose
counts are values at q = p of fixed rational expressions, uniform in the prime;
and (A2) *drainage* — an explicit envelope ε_N → 0 over the undecided mass.
Then one linear solve returns one R_τ ∈ ℚ(q) per type, at every prime power,
both characteristics, wild included, with Σ_τ R_τ = 1. Proved unconditionally
*as a reduction*; its machine-checked shadow is the Lean capstone squeeze,
which consumes the same data as typed hypotheses. Hold: **densities ⟸ menus +
drainage; the rest of the proof constructs those two at every degree.**

**Node I — the two-species induction (THEOREM GENIND.B).** A classifier history
is a chain of refine events of exactly two species: α-events (self-similar —
the active window survives whole, one digit deeper; runs of them telescope into
a geometric bracket) and β-events (partition-fracture — the window breaks into
strictly smaller windows, each a fresh instance of the same problem at smaller
degree). Menus and drainage at degree n therefore follow by induction: the
degree-< n packages feed every β-event, α-runs telescope, and the only
genuinely new content at each n is the classification of what one *stage* (one
read at one node) can do. Hold: **two species; induction on degree; all new
work is per-stage.**

**Node S — the stage laws (GENHN.A/B).** The per-stage classification is finite
and uniform: composite stages fall into finitely many *genres*, uniformly in n,
and each genre's count law is the order-1 law re-based to the stage's own ring
(residue field size q^f, ramification e) — wildness never enters the counting
layer. What a stage does not decide is the type-label σ of its pieces; the
stage laws reduce everything remaining to one question, [GENHN-HE(μ)]: decide σ
at a composite stage of multiplicity μ. And μ ≥ 4 occurs iff n ≥ 8 — the small
degrees close here. Hold: **finitely many genres; counts are re-based order-1;
one question left: σ at multiplicity μ.**

**Node L — the σ-ladder (HE3.A/B, HE6.A, HE7.A) and the μ ≤ 3 / μ ≥ 4 split.**
σ at a μ-stage is the label read of a degree-μ resolvent over the stage ring,
composed multiplicatively (HE3.A); a strict-descent induction (μ′ ≤ μ/2, base
μ ≤ 3 composite-stage-free) closes every μ from its base (HE3.B). The base case
is unconditional, so every degree n ≤ 7 closes outright. At μ ≥ 4 one branch
needs label class sizes at *fractional heights*: the enlarged test family pins
them base-change-free (HE6.A), and the slot-and-lift theorem (HE7.A) runs the
whole level ladder by one induction, terminating in depth ≤ log₂ n − 2. Hold:
**σ = a resolvent's label read; strict descent; μ ≥ 4 = the ladder.**

**Node T — the towers (n ≥ 8; HETOW, GENTOW1–6).** Multiplicity-≥ 4 stages open
genuine higher-order towers, and the tower leg's content is that no new
mechanism appears at depth: every tower-stage σ-read is a *literal instance* of
the ladder theorem at a composed carrier — composed budgets and windows
(GENTOW1), the canonical letter recursion with the one literature input (FGMN;
GENTOW2), faithfulness thresholds (GENTOW3), partial inner sides (GENTOW4), the
general-multiplicity graded frame (GENTOW5), the mixed-side tie (GENTOW6).
Hold: **the same ladder, at composed carriers, all the way down.**

Closing paragraph of the section (no sixth node): where the carry/letter layer
sits — counts are provably blind to it (JD0), σ-reads consume it only through
canonical frame choices, and the carry cocycle is a coboundary up to one honest
top carry (WELDMASTER). One sentence each; the difficulties section (§C4) pays
this forward. Precision note for the writer: *drainage* (A2) rides Node I's
induction from the HEX3 base — it is not Node L; Node L is the σ-decision. Do
not let the prompt-level word "exhaustiveness" blur the two.

### C3. The Montes algorithm, to guess-the-strategy depth

Load-bearing concepts (teach): (i) Newton polygon; slope denominator forces e —
existing figure + x³+2x²+4 example, kept; (ii) residual polynomial + Ore's
trichotomy decide/split/survive — existing (†) prose compressed, x⁴+18 vs x⁴+9
kept (one polygon, two residuals); (iii) recentering and key polynomials — a
repeated residual factor names a key; the accumulated data is the *type*;
(iv) the stage ring and re-basing — a composite stage is the same problem over
a bigger residue field with its own uniformizer (this is what Node S consumes);
(v) node = finite union of digit cylinders, measure readable off pinned digits
(the counting bridge); (vi) value-group growth / fractional heights, one
display (needed by §C4). NOT load-bearing (cut or defer): φ-adic development
internals, full type-invariant bookkeeping (h_i, e_i, f_i chains), MacLane
valuations, the carry-algebra D internals (defer to §C4), the letter/pattern
encoding (one sentence, pointing at the map page). New material: ONE full
worked quartic at p = 2 run to an order-2 stage — the running example that
matures through §C4 and §C5. Source: GENH4's committed genre keys (e.g. the
genre-F (1,2,2) instances) + `verification/` PARI oracle data; selection
criteria: reaches a level-2 read, exhibits one composite stage, decides in ≤ 3
levels, every number checkable by `quartic_oracle.py`. Section ends with the
guess-the-strategy paragraph: "you now know enough to guess the proof: classify
all polynomials by this tree, show the transition data is finite and rational
in q, and count" — then points back at the outline: the nodes are exactly the
obstructions to that guess, in order.

### C4. The difficulties — two concrete examples plus the dictionary

(a) **Where Hensel dies: the carry.** The existing (‡) computation (squares are
1 mod 8 ⟺ t + t² ≡ 0: the carry cancels the tame Newton step) moves here from
Movement 2, expanded by default. It closes with the D-ring in two displays —
the bookkeeping, not the theory. (b) **The μ ≥ 4 obstruction, numerically.**
The first-bite instance from HE6 §S2 (n = 8, μ = 4, D′ = 2): a label read at an
ℓ ≥ 2 side where the naive test family does not pin the class sizes — shown as
a table of the failing counts on the worked quartic's big sibling, then the one
sentence of what HE6/HE7 supply. (c) **The gauge/wrap caution** (candidate —
see §D): letters are frame-dependent; the wrap correction W(t) =
⌊(f₂−t)·i(u₂)/e₁⌋ drifted seven times in seven local frames before T1; the
cross-frame unit w, assumed trivial, measured ≠ 1 at six primes. Moral: counts
are gauge-blind (JD0), reads must fix a frame once. Capstone of the section:
the promoted H²-dies dictionary (B8) — *why* wild uniformity cannot be a
class-level computation and the proof is a ledger of explicit cochains. Final
text keeps (a) + (b) as the two mandatory examples; (c) compresses to a remark
if T1 lands (one lemma to cite) and stays a cautionary computation if not.

### C5. Successive refinement + the boundary

Pass structure (the spiral, B3/H1 — each pass re-reads the SAME five nodes):
after §C3, one short subsection re-states Nodes R/I/S in algorithm vocabulary
(menu = decided cylinder families; stage = the re-based read; the worked
quartic's events labeled α, β, composite); after §C4, a second subsection
refines Nodes L/T (why the ladder terminates; why μ ≥ 4 ⟺ towers; where the
carry layer sits — now meaningful). Then the two degree-5 walks (existing,
kept) as the full-pipeline payoff. Last section: **the boundary** — the status
Convention (B5, four rungs defined once), the single ledger table (existing,
updated), the four open sub-boxes, the Lean-vs-accepted line, and the four
open pieces (existing prose, updated to the chain). The milestone chronicle
LEAVES the paper: it becomes a dated changelog page linked from the boundary
section; `paper.html` carries mathematics + one ledger only.

### C6. story.json / index.html panels

Headline: two sentences — the theorem and its exact certification status; every
grade word defined in the amber panel, not the headline. Story field: rebuilt
as the spiral (context → outline's five nodes → one example → boundary), ≤ 6
paragraphs; the chronicle paragraphs move to the changelog. Panels: re-keyed to
the outline's nodes (R/I/S/L/T + the letter layer) rather than to Lean corpora
alone, each panel naming its certification rung once.

## D. WHAT WAITS FOR SIMPLIFICATION (T1–T5, SG probes) vs WRITE-NOW

- **Write now (stable under every T outcome):** §C1; §C2 Nodes R, I, S
  (accepted, byte-frozen texts); §C3 entire (the algorithm doesn't move; the
  quartic selection probe can run today); §C4(a); §C5 pass-1 subsection; the
  boundary Convention. This is ~70% of the page.
- **Waits on S-6/T2 (σ-ladder master instance):** §C2 Nodes L and T *wording*.
  If T2 lands, L+T compress toward "ONE carrier theorem; the base ring and the
  composed tower are two instances" — the five-node outline becomes four, and
  §C5's second refinement pass shrinks. The μ ≤ 3 / μ ≥ 4 split itself SURVIVES
  every T1–T5 outcome (HE3.B's strict-descent base is untouched); only its
  *presentation* (case split vs. ladder-level count) is T2-sensitive. Draft L/T
  now, flag for rewrite on S-6's verdict.
- **Waits on S-1/T1 (gauge cocycle):** §C4(c) — one citable lemma (remark form)
  vs. cautionary tale (computation form). Either way (a)+(b) carry the section.
- **Waits on S-7/SG-2 probe (weld one-face consumption):** the closing
  paragraph of §C2 and the boundary's weld row — if the load-bearing weld
  surface shrinks to WELDMASTER + JD0, the weld gets two sentences, not a
  stage; the index panels drop a stage.
- **Waits on SG-3 (pure speculation — do not hold the arc for it):** Node I's
  α/β case analysis dissolving into one transport would reword one paragraph.
- **Waits on arc/campaign terminal state:** §C5 boundary ledger + §C6 headline
  (whatever the grades are at execution time; the *slots* for them are fixed
  now).

## E. EXECUTION PLAN (post-simplification; units, gates, review points)

| Unit | Content | Size | Gate |
|---|---|---|---|
| E-0 | Source map: pin which existing blocks are reused verbatim / moved / retired (per §A6); quartic selection probe (GENH4 keys × PARI oracle) | 1 session | orchestrator check of the quartic pick |
| E-1 | §C2 THE OUTLINE (hardest first — it is the spine) | 1 composer | Codex fresh-reader + guess-test |
| E-2 | §C1 context/statement rewrite | 1 composer | Codex fresh-reader |
| E-3 | §C3 Montes + worked quartic | 1–2 composers | Codex fresh-reader + guess-test rerun |
| E-4 | §C4 difficulties | 1 composer | Codex fresh-reader |
| E-5 | §C5 refinement passes + boundary; §C6 story.json + changelog split | 1 composer | Codex fresh-reader on the whole page |

**The Codex gate, per section (standing protocol, minimal context):** "a
technically sophisticated reader sees this fresh; diagnose every unclear,
undefined, or context-presupposing point as a numbered list; do not rewrite."
**The guess-test (E-1, rerun at E-3):** hand Codex ONLY §C1+§C2 (then
§C1–§C3) and ask it to predict what the algorithm section must supply (then to
state the proof strategy); a wrong guess is a section failure, not a reader
failure. **Orchestrator review points:** after E-1 (the arc stands or falls
here — re-read this blueprint §C2 against the drafted text); after E-5
(whole-page pass; then Asvin sign-off before any push, per the standing
public-exposition rule: orchestrator reviews + pushes). Sequential units, one
at a time; composers get the 64k staged-write rules; every unit commits
per-section with prefix "EXPO rebuild". Total: ~6–7 composer sessions once
S-1/S-6 verdicts are in.
