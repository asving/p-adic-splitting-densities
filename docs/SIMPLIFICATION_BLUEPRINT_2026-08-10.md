# SIMPLIFICATION CAMPAIGN BLUEPRINT — 2026-08-10

**Unit:** SIMPLIFICATION-BLUEPRINT (pipeline stage 1.5 kickoff; Asvin's standing
directive: when the hostile arcs pass → compress the proof, hunt the
second-generation short proof — THEN stage two = Lean modulo literature except
arXiv:2212.00294). **Status:** DESIGN ONLY. No compression is performed here; no
accepted text is touched; every accepted text stays byte-frozen. **Sources:**
PROJECT_STATE dated appends #14–#20 · HEURISTICS_AND_INTUITIONS_2026-08-08 §C1 ·
the corpus notes' STATUS headers at HEAD · SITE_REFRESH2_DRAFT_2026-08-10 §0.

**The verdict up front.** The corpus is 26 texts, ~38,200 lines. Five compression
targets are real and rank cleanly by Asvin's criterion (revision-scope-reduction
— how many notes a future erratum would ripple through):

1. **T1 the gauge/ϑ cocycle lemma** — one letter-layer lemma absorbs the wrap/
   gauge annexes of the seven tower notes; the gauge seam produced findings on
   the seven tower first passes (appends #17–#20), i.e. this exact fact is
   currently proved seven times in seven local coordinate systems.
2. **T2 the σ-ladder master instance** — HETOW and GENTOW4 already prove their σ
   reads are LITERAL INSTANCES of THEOREM HE7.A; inverting that (state HE7.A once
   at a general carrier) turns five notes' bridge layers into instances.
3. **T3 the cocycle-telescope lemma** — GENTOW2-B″, HETOW-4, and GENTOW-6.4 (the
   𝒯-free cap) are three proofs of one telescoping-cocycle-monomial shape.
4. **T4 the certificate witness lemma** — GENTOW3's Θ_j threshold and GENTOW6's
   CERT-TOP share the touched-coordinate witness; one definition + one lemma.
5. **T5 the w-frame note** — define the cross-frame unit w and ψ^{(w)} once, in
   the w-inclusive canonical frame; the per-note riders become instances.

Two second-generation routes could bypass whole notes (§3): the literal-instance
cascade (T2 pushed to the whole σ-chain) and the weld one-face consumption
(retiring three junction notes from the load-bearing path). Both are graded
speculation with named cheap probes. **Proposed first wave: S-0 (the statement
ledger — the byte-tracking instrument) + S-1 (T1 through the full 2-clean bar).**

---

## 1. THE CORPUS MAP (26 texts, dependency DAG)

All files in `lean/notes/openmath/`, suffix `_2026-08-08.md` unless dated
otherwise. Grade: 25 texts ACCEPTED 2/2 at the hostile bar; JD0 is PROVED grade
(machine 68,523/0; sub-bar — the one exception, flagged where consumed).
"←" = consumes. Sizes in lines.

### 1.1 The carry/weld layer (8 texts, 11,942 lines) — letters, gauge, transport

| Text | Lines | Role (one line) |
|---|---|---|
| LIFTCORNER | 1,481 | NR-1 lift-orbit corner ((ITER-LAW-LIFT) at g₀=1∧δ₁=1); supplier to W-2's cap. |
| GRTW2 | 1,440 | W-2 the lift junction: admissible representative + (ξ,w) unit covariance + ψ-transport. ← LIFTCORNER. |
| GRTJA | 943 | J-A the dictionary junction: type→tower data, four operator equalities, covariance-corrected residual tie. ← GRTW2. |
| GRTJB | 3,161 | J-B the tree junction: expansion + polygon identities, division-step correspondence, (C-READ) transport, ε-carry collapse. ← GRTW2, GRTJA. |
| GRTJC | 2,807 | J-C the carry-algebra junction: graded target exists, TC-3 load-bearing iff δ ≥ g_m, anchor-transport Ψ, cocycle semantics. |
| WELDMASTER | 1,092 | The consolidation: four junctions = faces of ONE anchored graded transport (M0–M4); canonical gauge c = z̄^δ·∂Ẽ; one-perimeter fence. ← all four junctions. |
| JD0 | 385 | Count gauge-blindness: stratum counts see the SHAPE, never the letters. [PROVED grade, sub-bar.] |
| SIGMALAW | 633 | The Σ-LAW: per-coordinate ledger identity at every level; sign = the ξ-composite. ← GRTW2. |

### 1.2 The menu/reduction chain, n ≤ 7 (7 texts, 12,900 lines) — counts

| Text | Lines | Role |
|---|---|---|
| W11 | 719 | n=2 complete decided menu (7 families) + exact drainage q^{−N}; hExhaust as a theorem at n=2. ← JD0. |
| W12 | 1,995 | W-12.A order-1 shape-generic count law at all degrees; **THEOREM W-12.D (the reduction): menus + drainage ⟹ one R_τ ∈ ℚ(q) per splitting type, wild included**. ← W11 pattern, JD0. |
| HMENU3 | 952 | (hMenu-3): the 33-family cubic menu; W-12.D fires at n=3. ← W12. |
| HEX3 | 969 | (hExhaust-3): the exact U₃ law by per-center transport; n=3 drainage. ← W12. |
| GENIND | 3,054 | The two-species induction (α self-similar / β partition-fracture); (hMenu-n)+(hExhaust-n) scaffold; composite criterion = ≥4 keys (n ≥ 4). ← W12.A, HMENU3/HEX3 as base. |
| GENH4 | 2,173 | [GENIND-H(4)] discharged at both quartic genres (Q22-L1/L2/L3); the four-step method; 11 quartic densities. ← GENIND, weld faces. |
| GENHN | 2,038 | The general composite-stage law: genre classification FINITE+UNIFORM; every stage = W-12.A (e₁,f₁)-re-based; towers ⟺ μ ≥ 4 ⟺ n ≥ 8. ← GENH4's method, W-9 graded weld face via GENHN-4. |

### 1.3 The σ-ladder, n ≤ 7 (4 texts, 6,177 lines) — the wild read

| Text | Lines | Role |
|---|---|---|
| HE3 | 1,618 | The stage-σ recursion: σ at a μ-stage = label read of the degree-μ stage resolvent over the stage ring; [GENHN-HE(μ≥3)] closed at μ ≤ 3. ← GENHN interfaces; deliberately weld-face-minimal (§S0). |
| HE6 | 1,047 | The enlarged test family at fractional heights pins label class sizes at ℓ ≥ 2 sides, base-change-free. ← HE3. |
| HE7 | 2,652 | (SLOT₂)/(LIFT₂); the whole level ladder by ONE induction; TERMINATION depth ≤ log₂n − 2. ← HE6. |
| HE6R1 | 860 | The reconciliation: HE7 covers the widened HE6 box as a LITERAL INSTANCE; composition lemmas HE6R1-1/2/3; two errata on HE7. ← HE6, HE7. |

### 1.4 The tower leg, n ≥ 8 (7 texts, 8,160 lines) — composed carriers

| Text | Lines | Role |
|---|---|---|
| HETOW (…-09) | 834 | Tower-stage σ read = LITERAL INSTANCE of HE7.A at the composed carrier; bridges HETOW-1/2/3 + HETOW-4 (normalizer, the Codex-demanded cocycle bridge). ← GENHN, HE7 frozen, HE6R1. |
| GENTOW1 (…-09) | 975 | Items (1)(2)(5): composed budgets E₂ = e₂f₂u₂, inner refine transfer, window ledger, depth-3 floor. ← GENHN. |
| GENTOW2 (…-09) | 1,498 | Item (6α) via the PDF-verified FGMN cite; LEMMA B″ u(β_t) = ϑ(t)·w^{f₃−t}; the canonical letter formula z₂ = η₂·z₁^{−⌊ℓ₁u₂/e₁⌋}. ← GENTOW1, FGMN. |
| GENTOW3 (…-09) | 878 | Item (3) the faithfulness geography: threshold Θ_j = (μ₂−j)E₂ + δ; touched-coordinate certificate. ← GENTOW1. |
| GENTOW4 (…-09) | 1,037 | Item (4) partial inner sides = level-1 block split + HE6R1-2 projection + per-block literal HE7.A instances. ← HE6R1, HE7, GENTOW1. |
| GENTOW5 (…-09) | 1,741 | The composed graded frame at general μ₂ + the level-r grammar (depth ≥ 4); ψ^{(w)} re-scope; depth-4/5/6 witnesses. ← GENTOW1/2. |
| GENTOW6 (…-09) | 1,197 | The mixed-side tie + CERT-TOP + LEMMA GENTOW-6.4 (the 𝒯-free window cap); residues = count-grade BOX-1/2/3 (+BOX-4 battery ask). ← GENTOW1/3/4. |

**DAG summary.** Three load-bearing spines meet at W-12.D: (i) the COUNT spine
W11 → W12 → {HMENU3, HEX3} → GENIND → GENH4 → GENHN → GENTOW1/2/3/5/6, fed by
the weld layer through TWO faces (JD0 count-blindness; the W-9 graded face via
GENHN-4); (ii) the σ spine HE3 → HE6 → HE7 → HE6R1 → HETOW → GENTOW4, which
consumes strictly fewer weld faces (HE3 §S0: GENHN-4/W-9 deliberately NOT
inherited); (iii) the LETTER layer (GRTW2/WELDMASTER gauge + SIGMALAW + the
tower notes' ϑ/wrap formulas), which never enters counts (JD0) and enters σ only
through canonical-frame choices — the layer T1 unifies.

---

## 2. COMPRESSION TARGETS, ranked by revision-scope-reduction

Ranking criterion (Asvin's): how much future-revision surface one unified lemma
removes — measured as (notes whose local arguments become instances) × (the
demonstrated frequency of errata in that layer). Each target lists WHAT the
unified lemma is, what it ABSORBS, what gets SHORTER, and the RE-VERIFY scope.

### T1 — LEMMA GAUGE-COCYCLE (the ϑ/wrap recursion, stated once) — RANK 1

- **WHAT.** One lemma on the composed tower's letter layer: the canonical letter
  recursion z_{i+1} = η_{i+1}·z_i^{−⌊ℓ_i u_{i+1}/e_i⌋} (GENTOW2's formula), its
  wrap correction W(t) = ⌊(f₂−t)·i(u₂)/e₁⌋ (HETOW [r1]), and gauge-invariance of
  reads under it — proved once in the w-inclusive canonical frame, as a cocycle
  statement over the composed carrier (the WELDMASTER gauge c = z̄^δ·∂Ẽ
  specialized to towers).
- **ABSORBS (enumerated, 7 sites).** HETOW's [r1] ϖ-wrap seam repair; GENTOW1's
  gauge annex; GENTOW2's canonical-letter derivation; GENTOW3's gauge annex;
  GENTOW4's four-site gauge annex; GENTOW5's frame normalization; GENTOW6's
  gauge annex ([r] repair of the 6.3 scalar reading at f₁ ≥ 2).
- **WHY RANK 1.** The gauge seam produced findings on the seven tower first
  passes (appends #17–#20: the notes predated the wrap erratum) — the same fact,
  re-proved in seven local coordinate systems, drifted seven times. A future
  letter-layer erratum currently ripples through 7 notes; after T1, through 1.
- **SHORTER / RE-VERIFY.** Each gauge annex → one displayed substitution
  (~600–900 lines net removal across the seven). New lemma: full 2-clean arc +
  sealed battery (frames must include the recorded first-instances: q=4 letters,
  η≠1, f₁=2 letter-live, μ₂=3, w≠1) + seven consumption checks (§5.3).

### T2 — THE σ-LADDER MASTER INSTANCE (HE7.A at a general carrier) — RANK 2

- **WHAT.** Restate THEOREM HE7.A once over an abstract carrier (a complete DVR
  stage ring with the ladder data: sides, residuals, test family, termination
  measure), so that the existing instantiations become instances of ONE theorem.
- **ABSORBS (enumerated, 5 sites).** HE6R1's reconciliation (HE7 covers the
  widened box branch "as a LITERAL INSTANCE"); HETOW.A (tower σ read = literal
  HE7.A instance, bridges HETOW-1/2/3/4 becoming the carrier-checking clauses);
  GENTOW4's per-block literal HE7.A instances; HE3.A's recursion step (the
  degree-μ stage resolvent read = the base instance); HE6's ℓ ≥ 2 branch (via
  HE6R1's own reduction).
- **WHY RANK 2.** Two accepted notes (HE6R1, HETOW) already PROVE the
  instance-hood — the mathematics is done; what's missing is the inversion:
  state once, instantiate five times. This is the "the ladder is ONE induction"
  observation (HE7 §S6 + heuristics §C1) promoted to the corpus level. Risk: the
  general-carrier statement must carry HE6's test-family hypotheses abstractly —
  a real statement-design task, not a transcription.
- **SHORTER / RE-VERIFY.** HE6R1's and HETOW's instantiation maps become worked
  examples of one definition; the σ-chain's Lean surface shrinks from 4 bridge
  layers to 1 theorem + instance records. The master statement is NEW (highest
  statement-design risk of the five): Codex plan-level adversarial pass BEFORE
  composing, then the full 2-clean arc + five consumption checks.

### T3 — LEMMA COCYCLE-TELESCOPE (one shape for B″ / HETOW-4 / the cap) — RANK 3

- **WHAT.** One lemma: a cocycle-weighted product along a tower height ladder
  telescopes to (boundary value) × (monomial in the gauge letter) — the common
  shape of GENTOW2-B″ (u(β_t) = ϑ(t)·w^{f₃−t}), HETOW-4 (ρ_t = ρ̂_t·τ(H₀)·δ^{−t},
  i.e. R = τ(H₀)·R̂(Z/δ) — "exactly the J-D0-covered species"), and
  GENTOW-6.4 (the 𝒯-free window cap).
- **ABSORBS.** Three separately-proved telescopes; both Codex-challenge repair
  lemmas (HETOW-4, the 𝒯-free cap) land as instances rather than one-off
  patches.
- **SHORTER.** Three proofs → one proof + three two-line instantiations.
- **RE-VERIFY.** 2-clean arc; three consumption checks; battery re-uses the
  committed HETOW-4 frames (203 checks / 37 dual-route gp jobs) as regression.

### T4 — THE CERTIFICATE WITNESS (Θ_j threshold + CERT-TOP unified) — RANK 4

- **WHAT.** One definition (touched coordinate, certificate sense — GENTOW3's
  GT3-r2 pin) + one attainment lemma covering GENTOW3's faithfulness threshold
  Θ_j = (μ₂−j)E₂ + δ and GENTOW6's CERT-TOP.
- **ABSORBS.** Two certificate machineries; also gives the four count-grade
  sub-boxes (GENTOW6-BOX-1/2/3, BOX-4) ONE home — they are refinements of this
  lemma's count side, so their eventual closure revises one text.
- **SHORTER.** GENTOW6's CERT-TOP section becomes an instance; the sub-box
  ledger consolidates.
- **RE-VERIFY.** 2-clean arc; two consumption checks; the GENTOW3 acceptance
  battery frames (incl. FR-M3 measured slack) re-run as regression.

### T5 — THE w-FRAME NOTE (ψ^{(w)} and the cross-frame unit w, once) — RANK 5

- **WHAT.** One short note defining the cross-frame unit w and the w-twisted
  realized residual ψ^{(w)} in the w-inclusive canonical frame, with the
  measured record attached (GENTOW2-PE6: w ≠ 1 at 6 primes / 4 frames, avatars
  z₁, z₁², z₂², z₂; GENTOW5-PE3: ψ₃^{(w)}(Y) = 0 on the nose at a 7th prime).
- **ABSORBS.** GENTOW5's ψ^{(w)} re-scope machinery + the w-facts currently
  scattered across GENTOW2/GENTOW5 pass records; the owed "w ≠ 1 as-of note"
  (append #16) lands here instead of as another rider.
- **SHORTER.** Rider scatter → one citable definition. The w = 1 question stays
  honestly open and gets its one named home.
- **RE-VERIFY.** Light: mostly definitional + record consolidation; 2-clean arc
  at reduced size; no absorbed statement changes.

**Not targets (deliberate).** (a) The four count-grade sub-boxes: open refinement
work, not compression — they ride T4's home but are a separate track. (b) The
distribution suite (BCFGTIE/MOMENTS/TAMEK/TAMEKQX): outside the 26-text corpus,
arcs not yet run. (c) The weld notes themselves: accepted and byte-frozen;
compression of their CONSUMPTION is SG-2 below, not a rewrite of the notes.

---

## 3. SECOND-GENERATION PROOF CANDIDATES (sketch level; graded honestly)

### SG-1 — The literal-instance cascade (T2 pushed to its limit). GRADE:
**supported speculation** (two instance proofs exist in accepted texts). If T2's
carrier-general HE7.A lands, the second-generation σ-story is ONE theorem + one
recursion (HE3.A) + instance records — the notes HE6, HE7, HE6R1, HETOW, and
GENTOW4's read layer become history/instances. Probe: draft the carrier
signature and check it against HE6's fractional-height test family FIRST (the
one hypothesis family that resists abstraction; HE6's base-change-free property
is the thing to preserve). Failure mode: the carrier signature bloats to
re-encode each note's frame, and nothing is shorter.

### SG-2 — Weld one-face consumption. GRADE: **speculation with a recorded
scent.** HE3 §S0 records that the σ-chain does NOT inherit the W-9 graded weld
face (GENHN-4 is count-side only), i.e. the weld enters the theorem through TWO
faces: JD0 (count blindness) and GENHN-4/W-9 (digit-space bijection). Question:
can GENHN-4 be re-derived from WELDMASTER's M0–M4 transport + JD0 alone? If
yes, the load-bearing weld surface = WELDMASTER + JD0 (~1,500 lines), and
GRTJA/GRTJB/GRTJC (~6,900 lines) retire to suppliers-of-WELDMASTER — a huge
stage-two scope cut, since Lean would formalize the consumed faces only. Probe:
one session tracing GENHN-4's proof inputs against WELDMASTER's M2/M3 faces.

### SG-3 — The ϑ-cocycle view of the two-species induction. GRADE: **pure
speculation.** GENIND's α-bracket ((Q−1)Q^{(m(m−1)/2+1)μ−1}) and β-partition
product might both fall out of one cocycle-weighted per-center transport (the
T1 lemma applied at every event type), collapsing the five-event case analysis
(DRAIN / order-1 / α / β / composite-opening) to one transport with parameter
regimes. Probe (examples-first, per the standing directive): re-derive HMENU3's
33-family menu from the candidate unified form on the committed exact tables —
read the case split off the table before believing it dissolves.

### SG-4 — Letters-vs-depth splits made uniform by the w-inclusive frame. GRADE:
**speculation with one data point.** GENTOW2-PE6 closed B″(6) in the w-inclusive
canonical frame after the letters×depth refutation killed the old B-2. If T1+T5
land, re-examine the letters-vs-depth case splits in GENTOW2/GENTOW5 for
frame-artifacts: a split that exists only because the frame wasn't w-inclusive
dissolves. Probe rides SG-3's battery.

**Honesty line.** None of SG-1–4 is owed by the accepted corpus; each is a bet
that could shorten stage two. The blueprint schedules probes, not commitments.

---

## 4. LEAN-READINESS NOTES (per target; stage-two shapes)

Standing frame: stage two = Lean modulo literature (declared axioms with
faithfulness entries per docs/AXIOM_FAITHFULNESS.md), arXiv:2212.00294 EXCLUDED
everywhere. Three kernel-checked seed files are banked
(verification/openmath/{ja_pe6,w2_pe5,wm_pe9}_lean_leg.lean). The capstone
pattern to imitate: MontesV2's abstract spine + real instance (abstract data
structure, gates, instance-keyed non-vacuity witnesses).

- **T1 GAUGE-COCYCLE.** Best Lean shape in the batch: an algebraic identity over
  an abstract graded unit structure (commutative ring + distinguished unit +
  ⌊·⌋ exponent arithmetic over ℤ/ℚ — omega/ring territory), stated as a cocycle
  law, no literature cite. Formalize the LEMMA, not the seven annexes; each
  annex's Lean form is `GaugeCocycle.instance_at (params)`.
- **T2 σ-LADDER MASTER.** The carrier abstraction IS the Lean design: a
  structure `LadderCarrier` (stage ring, sides, residuals, test family,
  termination measure) + one theorem, instances for base/composed carriers.
  Highest design risk → write the Lean signature AT COMPOSE TIME (the informal
  statement and the structure should be born together; that is the readiness
  test). No new cite: HE3 §S0 records the Montes/GMN order-≥2 cite deliberately
  NOT consumed (resultant identity + ultrametric read suffice).
- **T3 COCYCLE-TELESCOPE.** Finset.prod telescope over a height ladder —
  mechanical Lean once stated; no cite.
- **T4 CERTIFICATE WITNESS.** Digit/threshold combinatorics over ℕ (Θ_j
  arithmetic, touched-coordinate predicate is decidable) — decide/omega
  friendly; no cite. Formalizing this early also fences the four count-grade
  sub-boxes as explicit hypotheses rather than prose residues.
- **T5 w-FRAME.** Definitional; one structure + the measured record as
  instance-keyed facts. The w = 1 open question becomes a named hypothesis, the
  honest-`sorry` analogue at statement level.
- **Load-bearing literature (enumerated).** FGMN Thm 6.3 + Cor 6.4 (GENTOW2's
  item 6α; PDF-verified cite — the ONE new axiom candidate stage two must
  declare, with a faithfulness entry and semantic-guardian pass per the axiom
  policy). Standing allowed axioms: GMN index theorem, Denef–Igusa cell
  recursion (measure route). NOT allowed: 2212.00294 (excluded by directive);
  the retired DCD tame-FE axiom stays a hypothesis (htameFE).
- **Ordering consequence.** T1/T3/T4 are Lean-cheap and revision-hot — compress
  first, formalize early. T2 is Lean-expensive but is the difference between
  formalizing 4 bridge layers and 1 theorem: its compose-time Lean signature is
  the cheapest insurance in the plan. SG-2, if the probe lands, cuts ~6,900
  lines of junction notes from stage-two scope — highest leverage, most
  uncertain.

---

## 5. THE CAMPAIGN PLAN (units, order, verification protocol)

### 5.1 Unit list (sizes = composer sessions; arcs per the standing bar)

| Unit | Content | Size | Depends on |
|---|---|---|---|
| S-0 | STATEMENT LEDGER: extract every named theorem/lemma statement of the 26 texts, md5 + commit pin per statement — the byte-tracking instrument | 1 session, machine | — |
| S-1 | T1 GAUGE-COCYCLE: compose + sealed battery + 2-clean arc + 7 consumption checks | 1 composer + ~3 arc sessions | S-0 |
| S-2 | T3 COCYCLE-TELESCOPE: compose + arc + 3 consumption checks | 1 + 2 | S-0 (S-1 helpful, not gating) |
| S-3 | T4 CERTIFICATE WITNESS: compose + arc + 2 consumption checks | 1 + 2 | S-0 |
| S-4 | T5 w-FRAME note (folds the owed w≠1 as-of note) | 1 + 1 | S-1 (the frame) |
| S-5 | T2 design probe: carrier signature draft + Codex plan-level adversarial pass + Lean signature sketch | 1 session | S-0 |
| S-6 | T2 σ-LADDER MASTER: compose + arc + 5 consumption checks | 2 + 3 | S-5 verdict |
| S-7 | SG-2 probe: trace GENHN-4 against WELDMASTER M0–M4 + JD0 | 1 session | — |
| S-8 | SG-3/SG-4 probe battery (examples-first, sealed two-commit) | 1 + run | S-1 |

### 5.2 Order

S-0 first (everything keys off it). Then S-1 (rank 1, and its frame feeds
S-4/S-8). S-2/S-3 next, sequential per the fleet throttle. S-5 early and cheap —
its verdict gates the biggest unit (S-6). S-7 anytime (independent, one
session). S-8 after S-1. Second-generation composition (beyond probes) is NOT
scheduled: it enters only on a probe verdict, re-ranked by this section's
criterion.

### 5.3 Verification protocol (the non-negotiables)

1. **Compressed proofs re-enter the 2-clean bar.** Every S-unit note takes the
   full hostile arc: two consecutive clean fresh-context passes, model-diverse
   verifiers, fresh route per pass, findings → minimal repair → counter resets.
2. **Sealed instruments, two-commit.** Each battery: runner + preregistered
   predictions/teeth committed BEFORE the run; verdict from the artifacts.
   Regression legs re-run the absorbed notes' committed frames unmodified.
3. **A simplification NEVER weakens a statement.** For each absorbed argument, a
   CONSUMPTION CHECK: display "new lemma ⟹ absorbed statement," where the
   absorbed statement is byte-identical to the accepted text per the S-0 ledger
   (md5 match required). A consumption check failing = the unit is wrong, not
   the corpus.
4. **Accepted texts stay byte-frozen.** Compression lands as NEW notes; the
   accepted notes get dated appends only ("absorbed by S-k as instance …"),
   after the S-unit is itself accepted 2/2.
5. **Record rule.** Enumerative/pattern-scoped record sentences only; counts
   with unit and commit; evidence-class labels on cross-note quotes.
6. **Grade vocabulary.** An S-unit before its arc closes is attempt grade; the
   corpus milestone ("accepted-text-complete") is NOT restated as covering the
   new notes until each is accepted.

### 5.4 What stage two consumes from this campaign

The Lean blueprint (stage two's first unit) keys off the POST-compression
corpus: the S-0 ledger + accepted S-units replace per-note formalization
targets wherever a consumption check landed. If only S-1/S-2/S-3 land, stage
two already drops ~12 per-note argument sites; if S-6 lands, the σ-chain
formalizes as one theorem + instances; if S-7's probe lands, the junction notes
leave the load-bearing set.

---

## Plan revision 1 (2026-08-10, post plan-pass)

**Provenance.** Run F (the Codex adversarial plan review, log
`verification/openmath/towerrat2_runF_planpass_output.txt`, commit 3fb99af6)
returned 40 numbered findings and OUTCOME: PLAN-DEFECTIVE; no charged item
was checked clean. This section adjudicates the 40 findings (REAL = the plan
defect exists / ARTIFACT = the critique dissolves against the repo's actual
artifacts) and lands the revision. Adjudication context the reviewer lacked:
**S-0 is BUILT**, not planned — `docs/STATEMENT_LEDGER_2026-08-10.md` +
`verification/openmath/statement_ledger.py`, sealed f8bd49dd, baseline-green
7e2b38df: 166 statements over the 26 texts, md5 + line range + note commit
per row, declared normalization, validated teeth (token-change fires exit 1),
(note,label) matching robust to dated appends, and an enumerated residue
class of un-rowed `**(`-display lines per note (ledger §S3 item 3). S-0
findings are adjudicated against that instrument.

### R.0 Adjudication (40 findings; disposition keys R.1–R.4 below)

| F# | Verdict | One-line adjudication → disposition |
|---|---|---|
| 1 | REAL | T1's three conclusions (recursion / wrap / read-invariance) could slide into carrier fields → R.2 skeleton gate S-1a |
| 2 | REAL | checks were priced per note, not per absorbed site (GENTOW4 = 4 sites) → R.2: per-site absorption map |
| 3 | REAL (wording) | "ripples through 1" overstates; instance maps stay revision sites → R.4 pricing fix |
| 4 | REAL | listed first-instances could be witnessed in separate frames; joint defects escape → R.3 joint-frame rule |
| 5 | REAL | carrier fields can internalize HE7.A conclusions → R.2 S-5 gate (fields-vs-conclusions ledger) |
| 6 | REAL | instances not required to be constructible prior to the absorbed theorem → R.1 provenance leg |
| 7 | REAL | bespoke per-instance carrier types would fake the unification → R.2 S-5 gate (one signature first) |
| 8 | REAL | base-change-free-ness of HE6's test family not pinned in the carrier → R.2 S-5 gate (own-ring witnesses) |
| 9 | REAL | termination measure as data could assume what HE7 proves (depth ≤ log₂n − 2) → R.2 S-5 gate (bound = conclusion) |
| 10 | REAL | component coherence laws (projection/split/composition) unstated → R.2 S-5 gate |
| 11 | REAL | quantifier order/uniformity can silently weaken at the carrier → R.2 S-5 gate (prefix display) + R.1(a) |
| 12 | REAL | consumption checks blind to circular citation of the absorbed theorem → R.1 provenance leg (the central fix) |
| 13 | REAL (pricing) | T2's downstream interface migration unpriced → R.4 |
| 14 | REAL | T3's common shape asserted verbally, no side-by-side signature → R.2 S-2 gate (withdraw tooth) |
| 15 | REAL | T3 regression battery HETOW-4-only → R.3 |
| 16 | REAL | T4 witness attainment ≠ threshold formula + CERT-TOP; conclusions must be displayed separately → R.2 |
| 17 | REAL (pricing) | BOX closures re-open T4's arc; declare the trigger → R.2/R.4 |
| 18 | REAL | T5 transfers propositions across frames; "light" underprices frame-equivalence legs → R.2 S-4 re-scope |
| 19 | REAL | a named w-hypothesis could conditionalize statements the measured w≠1 records support → R.2 S-4 rule |
| 20 | REAL | SG-1 "history" status needs non-circular instance construction → R.1(b) applied to the probe |
| 21 | REAL | SG-1 success criterion syntactic-only → folded into F20's fix (implication ledger) |
| 22 | REAL | SG-2 retirement conflicts with proving WELDMASTER; two branches must be declared → R.4 |
| 23 | REAL | one-theorem trace cannot ground whole-path retirement → R.4 probe re-scope |
| 24 | REAL | SG-3 must declare which side of the JD0 letters/counts boundary moves → R.4 |
| 25 | ARTIFACT | the plan grades SG-3 pure speculation and probes are scents, not validators (§3 honesty line; §5.3-1 re-bars any composition) |
| 26 | REAL | SG-4 riding SG-3's menu battery never exercises the letters×depth splits → R.3 |
| 27 | REAL (partially defused) | un-rowed displays exist, but the BUILT ledger enumerates the residue class per note → R.1(a) span-pin rule |
| 28 | REAL | md5 of a span does not pin the ambient definitions the span reads in → R.1(c) |
| 29 | REAL | binders/hypotheses prefixed OUTSIDE the hashed span restrict a universal statement → R.1(a) closed-display rule |
| 30 | REAL | hypothesis migration into new definitions defeats the byte check → R.1(c) definition audit |
| 31 | REAL | scope-fixing prose (base-change-free, wild-inclusive) sits outside rowed spans → R.1(a) prose pins |
| 32 | ARTIFACT | the built instrument matches by (note,label), tolerates appends, and documents the re-pin rule (ledger §S3-5, §S5) |
| 33 | ARTIFACT | md5 here is a drift tripwire inside a git-frozen corpus, not a security boundary; a collision needs repo control, which defeats any hash; the semantic kernel of the worry is F28–31 (adjudicated REAL) |
| 34 | REAL | T1 carries the same statement-design hazard as T2 but had no design gate → R.2 S-1a (the S-1 gate) |
| 35 | REAL | S-4/S-8 gated on S-1 "landing", not on semantic legs green → R.1 downstream-gating rule |
| 36 | REAL (wording) | S-7 runs anytime but its VERDICT carries ledger + axiom-policy conditionality → R.4 |
| 37 | REAL | "fresh route" constrains reviewers, not the proof artifact's dependency graph → R.1(b) |
| 38 | REAL | absorption appends could overstate; template pinned to checked ledger rows → R.1 append rule |
| 39 | REAL | stage-two replacement magnifies a false-positive check → R.1 §5.4 amendment |
| 40 | REAL (pricing) | consumption-site counts stated as formalization-scope cuts → R.4 |

**Tally: 37 REAL (of which 5 wording/pricing grade), 3 ARTIFACT (25, 32, 33).**
The 37 REAL defects group into four revision blocks; none withdraws a target,
none reorders the unit list. The blocks strengthen gates and re-scope claims.

### R.1 The conservativity protocol upgrade (§5.3 item 3 REPLACED)
[F6, F12, F20, F21, F27–F31, F35, F37, F38, F39]

The md5 leg alone proves byte identity of a span, not conservativity. §5.3
item 3 now reads: a CONSUMPTION CHECK has **three legs**, and the check
passes only with the three green.

- **(a) STATEMENT leg** (the old leg, tightened). Display "S-unit lemmas ⟹
  absorbed statement" with the absorbed statement md5-identical per the S-0
  ledger AND **closed as displayed**: no binder, hypothesis, or fixed-witness
  clause may prefix the quoted statement beyond what the frozen note's own
  span carries (kills the "for a fixed admissible carrier C, [statement]"
  weakening — the quoted bytes match while the theorem shrinks). Absorbed
  material with NO ledger row (the T1 gauge annexes and T5 pass-record facts
  live partly in the ledger §S3-3 residue class of `**(`-display lines) is
  pinned by (frozen-note commit, line range, verbatim quote) — the notes are
  byte-frozen at pinned commits, so a span pin is exactly as strong as a row.
  Scope-fixing prose (base-change-free, wild-inclusive, frame declarations)
  that the absorbed statement reads under gets the same (commit, line) pin in
  the absorption map.
- **(b) PROVENANCE leg.** The check displays the enumerated proof inputs of
  the new lemma AND of the instance construction; the absorbed statement, and
  the other statements the same S-unit absorbs, must not appear among them
  (grep-auditable citation list against the ledger labels). This is what the
  2-clean arc cannot see: hostile passes verify the implication as displayed;
  only an input audit sees that the implication cites its own conclusion
  (e.g. an HETOW carrier field discharged by HETOW.A itself rather than by
  the HETOW-1/2/3/4 bridge suppliers).
- **(c) DEFINITION-AUDIT leg.** A NEW definition appearing in a consumption
  check (carrier, frame, touched coordinate, test family) displays its
  extension against the frozen note's corresponding notion AT the absorbed
  statement's quantifier generality — a definition that builds in a formerly
  proved property narrows the subtype and defeats leg (a) silently.
  "Hypothesis migrated into a definition" and "statement re-bound in a new
  ambient frame" become NAMED verifier-charge items in each S-unit arc.

Downstream gating (F35): S-4 and S-8 fire on S-1 **ACCEPTED** — arc 2-clean
AND the seven checks green on the three legs — not on S-1 merely landing.
Absorption appends (F38): the dated append names exactly the ledger rows (or
span pins) whose checks passed, with leg record — no umbrella "absorbed"
wording. Stage-two replacement (F39, §5.4 amended): a per-note formalization
target drops only at statement granularity, and only where legs (a)+(b)+(c)
passed; the note's definitions and its upstream suppliers stay in stage-two
scope unless a separate audit clears them.

### R.2 Statement-skeleton gates on every compression unit (T2's S-5
treatment generalized) [F1, F2, F5, F7–F11, F14, F16, F17, F18, F19, F34]

- **S-1 gains a gated first commit, S-1a** (inside the same composer session;
  committed before the body per the survival discipline): the T1 statement
  skeleton — carrier data enumerated against **three displayed CONCLUSIONS**
  (the letter recursion z_{i+1} = η_{i+1}·z_i^{−⌊ℓ_i u_{i+1}/e_i⌋}; the wrap
  identity W(t) = ⌊(f₂−t)·i(u₂)/e₁⌋; gauge-invariance of reads), with the
  rule that a conclusion may not re-enter as a carrier field — plus the
  **absorption map at site granularity**: 7 notes → enumerated absorbed
  sites (GENTOW4 contributes four), one consumption-check target per SITE
  (so "seven checks" becomes "the absorption map's site count, fixed at
  S-1a"). The skeleton takes a Codex statement-level adversarial pass before
  the body composes. This is T2's compose-time-signature insurance applied
  to T1, which carries the same abstraction hazard at smaller size.
- **S-2 (T3) pre-compose gate**: display the three absorbed statements
  side-by-side from the ledger (GENTOW2-B″, HETOW-4's ρ_t telescope,
  GENTOW-6.4) with the candidate common signature and the three
  instantiation maps. Withdrawal tooth: if the signature can only cover the
  three by taking an endpoint equation as an INPUT, T3 is withdrawn as
  vacuous unification.
- **S-3 (T4) re-scope**: the unified lemma displays TWO conclusions — the
  threshold formula Θ_j = (μ₂−j)E₂ + δ at its ledger quantifier generality,
  and CERT-TOP — or splits into one definition + two lemmas; witness
  attainment alone discharges neither. Declared re-open trigger (F17): a
  closure of BOX-1/2/3/4 re-opens T4's arc (that is the price of giving the
  boxes one home, and it is the intended trade).
- **S-4 (T5) re-scope**: "light" is withdrawn. S-4 carries a
  frame-equivalence leg — for each transferred fact (the six-prime w ≠ 1
  record, GENTOW5's ψ₃^{(w)}(Y) = 0), display the old-frame ⟺ w-inclusive-
  frame reading — and the rule (F19): the measured w ≠ 1 instances stay
  unconditional records; a named w-hypothesis may condition only statements
  whose accepted forms already depend on the dichotomy, and no consumption
  check may show an absorbed statement GAINING a w-hypothesis.
- **S-5 (T2 probe) gate spec, sharpened to five named hazards**: (i) a
  fields-vs-conclusions ledger — each clause of HE7.A's conclusion appears as
  a conclusion of the master, none as carrier data; (ii) ONE carrier
  signature fixed before any instance is drafted, instances differing in
  data only; (iii) test-family witnesses defined over the carrier's own
  stage ring — no extension ring or preselected root as carrier data (HE6's
  base-change-free strength is the preservation target, promoted here from
  SG-1's probe into S-5's gate); (iv) the termination bound depth ≤ log₂n − 2
  is a conclusion, with a strictly-decreasing measure PROVED, not supplied;
  (v) coherence laws (residuals/sides/labels commuting with projection,
  block split, composition — the laws GENTOW4's per-block and HE6R1's
  widened-box instances actually use) stated as carrier laws, plus a
  quantifier-prefix display of the master against each of the five absorbed
  statements. S-6 launches only on an S-5 verdict green on the five.

### R.3 Battery coverage upgrades [F4, F15, F26]

- **S-1 battery**: the recorded first-instances (q=4 letters, η≠1, f₁=2
  letter-live, μ₂=3, w≠1) are necessary but not sufficient as separate
  witnesses; the battery must include JOINT frames — at least one frame with
  f₁ = 2 ∧ w ≠ 1 ∧ live wrap simultaneously — and a preregistered
  annex→frame coverage map (each absorbed site names the frame(s) exercising
  its hypothesis geography).
- **S-2 battery**: the committed HETOW-4 frames (203 checks / 37 dual-route
  gp jobs) regression-cover one consumer only; add GENTOW2-B″ frames (the
  PE6 instruments) and GENTOW-6.4 window-cap frames as preregistered legs.
- **S-8**: SG-4 gets its OWN preregistered leg — the GENTOW2-PE6
  letters×depth frames (the geography that killed the old B-2) — rather than
  riding SG-3's menu-reconstruction battery, which never exercises those
  splits.

### R.4 Claim re-scopes and honest pricing [F3, F13, F17, F22, F23, F24,
F36, F40]

- **SG-2 payoff split into two declared branches** (F22): (i) WELDMASTER
  stays kernel-proved from its suppliers → GRTJA/GRTJB/GRTJC remain in
  stage-two scope as upstream proofs; the cut is downstream INTERFACE only
  (formalize the consumed faces as the API). (ii) WELDMASTER's M0–M4 faces
  enter as declared axioms → the ~6,900-line scope cut is real but buys the
  full axiom-policy process (published-source citation, faithfulness entry,
  semantic-guardian pass — the process that has caught two false axioms).
  The blueprint does not pre-select a branch; S-7's probe informs the
  choice, Asvin makes it.
- **S-7's verdict re-scoped** (F23, F36): the probe concludes at most
  "GENHN-4 is / is not re-derivable from WELDMASTER M0–M4 + JD0". A
  whole-path retirement claim additionally requires a corpus-wide
  face-citation audit (grep over the 26 texts against the ledger labels) and
  the R.4 branch decision. S-7 stays schedulable anytime; its conclusion
  carries this declared conditionality.
- **SG-3 boundary declaration** (F24): the probe states up front which side
  of the JD0 boundary the candidate unified form lives on (count-side
  transport with cocycle-shaped weights, or an enriched letter layer). An
  outcome that needs JD0's blindness weakened is an automatic SG-3 failure —
  JD0 is machine-proved (68,523/0).
- **Pricing corrections** (F3, F13, F40): §2 T1's "ripples through 7 → 1"
  becomes "the letter-layer PROOF surface goes 7 → 1; the instance maps
  remain revision sites of mechanical grade, and T5/SG-4 consume T1's frame."
  §4 T2 prices the interface migration (instance records, projection/
  coercion lemmas, non-vacuity witnesses move when HE7.A's type generalizes).
  §5.4's savings are consumption-SITE counts, not formalization-scope
  counts; upstream proof obligations are priced under the R.4 SG-2 branches.

### R.5 THE S-1 VERDICT

**S-1 (T1 GAUGE-COCYCLE) is CLEARED TO LAUNCH under this revision.** Its
stated dependency is satisfied: S-0 is BUILT and baseline-green (166
statements, tripwire armed, commits f8bd49dd + 7e2b38df). Nothing else must
land first. The clearance is conditional on S-1 running in the revised form:
(i) S-1a skeleton gate as the first commit (statement skeleton + site-level
absorption map + Codex statement pass BEFORE the body); (ii) consumption
checks on the R.1 three-leg protocol, non-row annex material span-pinned per
R.1(a); (iii) the R.3 joint-frame battery requirement with the preregistered
annex→frame coverage map. S-4 and S-8 remain gated on S-1 ACCEPTED in the
R.1 sense (arc 2-clean + legs green), not on S-1 landing.
