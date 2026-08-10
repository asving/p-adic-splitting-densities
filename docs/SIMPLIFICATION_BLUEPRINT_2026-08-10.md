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
- **SHORTER.** Each tower note's gauge annex becomes "instance of GAUGE-COCYCLE
  at (e₁,f₁,u₂,…)" — one displayed substitution per note. Est. net removal
  ~600–900 lines of per-note derivation across the seven.
- **RE-VERIFY.** The new lemma: full 2-clean arc + sealed battery (frames must
  include the recorded first-instances: q=4 letters, η≠1, f₁=2 letter-live,
  μ₂=3, w≠1). Plus seven consumption checks (§5 protocol): GAUGE-COCYCLE ⟹ each
  absorbed annex's statement, byte-identical per the S-0 ledger.

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
- **SHORTER.** HE6R1's §on-instance and HETOW's §S3 instantiation map become the
  worked examples of one definition; GENTOW4's per-block argument drops its
  re-derivation. The σ-chain's Lean surface shrinks from 4 bridge layers to
  1 abstract theorem + instance records.
- **RE-VERIFY.** The master statement is NEW (highest statement-design risk of
  the five): plan-level adversarial pass (Codex) BEFORE composing; then the full
  2-clean arc; five consumption checks.

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
