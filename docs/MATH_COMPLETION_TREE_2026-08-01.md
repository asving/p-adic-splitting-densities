# THE MATHEMATICAL COMPLETION TREE — the uniformity theorem's full claim DAG
**Phase A of THE MATHEMATICAL COMPLETION campaign (Asvin authority, 2026-07-31, verbatim:
"we finish the math first, get a verified complete proof of the theorem of uniformity across
all primes including the wild primes, and use that scaffolding to figure out what to do").**

Date: 2026-08-01 (built 2026-07-31 evening, post-open-math-fleet, post-HK-06, at census
`lean/notes/REMAINING_CENSUS_2026-08-01.md`). This document is MATHEMATICS: its nodes are
mathematical statements, not Lean declarations. The Lean tree is cited only as *evidence*
about which claims are settled. Sources consumed in full: `docs/HUMAN_PROOF.md`; the census
§4.3 + row tables; the 18 open-math attempts `lean/notes/openmath/M01–M18*` with verifier
verdicts `V1_m12_verify.jsonl` / `V2_m05_verify.jsonl` / `V3_serre_audit.jsonl` /
`V4_ifk_review.jsonl` and the verification-round-1 + fleet sections of
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`; `lean/notes/IFK_BLUEPRINT_2026-07-31.md`
**including its REVISION 1 (landed 2026-07-31, commit 9fcdc2d: all 26 V4-REJECT findings
dispositioned, row-20 circularity resolved by re-attribution, BNS axiom stripped, honest
recount; Codex re-review launched, NOT yet accepted — the IFK nodes below carry the
revision's corrections)**; the U6 K-RUN falsifier probe, which HAS run and **SURVIVES
exhaustively** (174/174 length-2 strata T = T̂, zero phantoms, equal-fiber law exact, all
four (n, p) ∈ {2,3}² incl. both wild corners; `verification/openmath/results/
U6_krun_results.json`), folded in; the numerics matrix N1–N8 (§NUMERICS FLEET of the
adjudications ledger + `verification/openmath/`).

---

## 0. Status vocabulary (used on every node)

* **VERIFIED** — a proof exists AND survived adversarial verification in a fresh context;
  the pass is named. Two sub-grades, both acceptable: **VERIFIED-DUAL** (the campaign's dual
  standard: ≥2 consecutive clean Codex passes + an independent fresh-Fable clean pass on
  identical text) and **VERIFIED-LEAN** (machine-checked in Lean with Lean-core-only
  footprint AND a semantic/faithfulness audit of the statement on record — Lean checks
  proofs, not statements, so the audit is part of the grade).
* **PROVED-UNVERIFIED** — a proof is on file but has NOT had a fresh-context adversarial
  pass at the current (dual) standard. These are Phase-B verification duties, listed in §4.
* **OPEN** — no proof; the node states exactly what is missing and cites the best partial.
* **LITERATURE** — an external citation carries the node; faithfulness status stated
  (exact-statement transcription + guardian audit = the project's axiom discipline).
* **NUMERICALLY-SUPPORTED** — flag only; NEVER a substitute for a proof. A numerically
  confirmed conjecture is OPEN.
* **REFUTED-AS-STATED** — an earlier formulation was killed by an explicit countermodel;
  the repaired mathematical statement is what appears in this tree.
* **SUPERSEDED** — an earlier write-up whose load-bearing content was replaced by a
  stronger verified artifact; kept for provenance only.

A **reduction is not a proof**: a node "REDUCED to L1–L3" is OPEN until L1–L3 close.

---

## 1. THE ROOT

Fix n ≥ 2. A **splitting type** σ of degree n is a multiset of pairs (e_i, f_i) with
Σ e_i f_i = n (ramification index / residue degree of the irreducible ℚ_p-factors).
For a prime p let α(n, σ; p) be the Haar density, on the space of monic degree-n
polynomials over ℤ_p (Haar measure on ℤ_p^n, total mass 1), of
{ f : f separable with splitting type σ over ℚ_p }.

> **(U-DENS) THE UNIFORMITY THEOREM, density form.** For each n and each splitting type σ
> of degree n there is a SINGLE rational function R_σ ∈ ℚ(t) such that
>
>     α(n, σ; p) = R_σ(p)   for EVERY prime p — including every wild prime p ≤ n —
>
> and Σ_σ R_σ = 1 identically. The same R_σ works at every unramified base: over the
> degree-δ unramified extension of ℚ_p the density is R_σ read at q = p^δ.

> **(U-GEN) THE UNIFORMITY THEOREM, generating-function / counting form.** For each level
> N let decided_σ(N) count the residue classes in (ℤ/p^N)^n all of whose monic lifts have
> splitting type σ. Then for every prime p (wild included):
> (i) **two-sided bracket at every finite level**: decided_σ(N)/p^{nN} ≤ R_σ(p) ≤
> decided_σ(N)/p^{nN} + undec(N), where undec(N) is the undecided mass;
> (ii) **drainage**: undec(N) → 0 (so decided_σ(N)/p^{nN} → α(n,σ;p) = R_σ(p));
> (iii) **the rational function is produced by a p-independent finite solve**: R_σ is the
> σ-entry of the unique solution of a finite linear system (I − K(q))·C = b(q) over ℚ(q) —
> the generating identity of the cluster/OM-tree recursion (branch = convolution over
> coprime children, descend = strictly smaller child, self-loop = geometric resummation) —
> whose state menu, coefficients, and non-vanishing pivots carry NO dependence on p.

(U-DENS) ⇔ (U-GEN) given the bracket + drainage clauses; both forms are carried by the
dual-accepted Theorem U write-up (§2.3 node T-U) — (U-GEN) is Theorem U's literal shape.

**Wild-prime scope, explicit.** The content of the theorem is at p ≤ n (p | n!): there the
factorization is governed by higher-order Okutsu–Montes (OM) Newton-polygon towers whose
combinatorics a priori depend on p; the tame case p > n is residue-field combinatorics.
The paper's original tame route (S_n-equivariant resolution) FAILS at p ≤ n (Prop 5.3
counterexample: S_n not linearly reductive in residue characteristic p | n!); every route
in this tree computes the wild densities directly and never invokes it.

**Prime coverage.** The dual-accepted Theorem U is stated at every prime satisfying the
regularity condition (REG-p) (non-vanishing of the pinned determinants/denominators at the
pool q₀ = p^δ). (REG-p) failures are PROVED finite with exact characterization (node K-13);
"every prime" in the root therefore additionally requires leaf **O-12** (the failing set is
EMPTY at the intended OM instance — proved at n = 2, open at general n). This is the only
gap between "cofinitely many primes, effectively bounded" (already proved) and "all primes".

**Verified instances of the root** (anchors, not proofs of the general theorem):
* n = 2: **VERIFIED-LEAN** at every prime including wild p = 2 —
  `OM/UniformCapstone.montes_uniform_n2` (Lean-core-only): fixed numerators/denominators
  per type, value + bracket + drainage (`hExhaustP`) all machine-checked; external census
  exact at p = 2, 3 (`verification/census_n2_uniform.py`).
* n = 3: the five R_σ hand-derived through the full solve match the independent records +
  the Kac–Rice moment, wild values included (gate RESUM-n3, 65/65 decided integers exact
  at two primes, PARI 0 mismatches) — NUMERICALLY-SUPPORTED at the gate standard; the
  June write-up (`docs/HUMAN_PROOF.md` §13) claims n ≤ 3 unconditional, PROVED-UNVERIFIED.
* n ≤ 5 incl. deep-wild (p, n) = (5, 5): the density tie itself CONFIRMED numerically
  (N2 fleet: exact n = 2 sandwich widths ~1e-5; MC 150k/config) — NUMERICALLY-SUPPORTED.

**Out-of-scope annex (by standing directive, htameFE out of the critical path):** the
projective normalization ρ(n,σ;q) (monic → projective bridge, June lemma M1) and the
palindromic functional equation R_σ(1/t) = R_σ(t) (June lemma L7, interpolation from tame
primes + Del Corso–Dvornicich). Both are p-independent bookkeeping on top of (U-DENS);
they re-enter only if the root is re-targeted to the projective form. Annex nodes A-1, A-2.

---

## 2. THE DAG

Layers: §2.0 literature imports → §2.1 base lemmas (the June skeleton) → §2.2 the verified
conditional core (the MOVES write-up) → §2.3 the open kernel ledger (the leaves). Node ids:
LIT-* (literature), B-* (base), T-* (tower/core), K-* (kernel rows with verdicts), O-*
(open leaves; these are the attack-list heads of §3).

### 2.0 Literature imports (complete roster; each p-independent)

* **LIT-1 (GMN machinery).** Guàrdia–Montes–Nart, *Newton polygons of higher order in
  algebraic number theory*, Trans. AMS 364 (2012) 361–416 (arXiv:0807.2620v2). Used via:
  Thm 1.15/1.19/Cor 1.20 (order-1 polygon, residual polynomial, leaf dichotomy);
  Thm 2.11/Defs 2.19–2.21 (representatives, order-r residual coefficients); Thm 3.1/3.7/
  Cor 3.3/3.8 (order-r) + Def 3.9/3.10, eq. (37) (f-complete types, factorization product);
  Lemma 3.11(3) (descent trigger); **Thm 4.18 (theorem of the index) + Cor 4.19
  (termination)**; Defs 4.11/4.12/4.15 (index vocabulary). Pinned in
  `docs/GMN_citations.md`; the index theorem is a declared, guardian-audited Lean axiom
  (read-set-restricted, arising-key form). Status: LITERATURE, faithful-with-standing-
  caveat (printed-TAMS pagination confirmation carried). M15 verified the Thm 4.18(1)
  scope for the ALIGN row (1548-case dictionary check, 0 violations).
* **LIT-2 (Serre, local fields).** *Corps Locaux* / *Local Fields* (GTM 67): Ch. II §2
  Prop. 3 (integral closure of ℤ_p in a finite extension is a DVR — declared axiom
  `AX_integralClosure_dvr`, guardian audit PASSED 2026-07-31, V3: FAITHFUL, axiom EXACT);
  Ch. II §3 (defectless: Σ e_i f_i = [L:K]); Ch. III §6 Prop 13 (wild different bound,
  used by the June L5fix depth bound). Status: LITERATURE, audited (the DVR clause);
  the rest standard, transcription owed at use sites.
* **LIT-3 (Hensel, coprime-factor form) = (HEN-LIFT).** f̄ = ψ·h̄ coprime, ψ irreducible ⇒
  unique monic lift factorization f = g·h, g irreducible with (e, f) = (1, deg ψ), generating
  the unramified extension. Neukirch ANT II §4 Prop 4.6 + Serre LF I §6 (numbers to confirm
  at declaration). Status: LITERATURE, valid at all p (hypothesis is coprimality, not
  tameness); M06 §4.1 flags it as plausibly Mathlib-provable (`HenselianLocalRing`) —
  probe before declaring.
* **LIT-4 (OM saturation) = (OM-SAT).** A realized OM branch with residual multiplicity 1
  at its last read certifies an irreducible factor with e = e₁⋯e_r, f = f₀f₁⋯f_r
  (GMN Cor 3.8 + Def 3.9; order-1 instance Cor 1.20). Status: LITERATURE (inside LIT-1),
  faithful at K = ℚ_p exactly (no scope over-claim needed); consumed only through the
  dictionary node O-2 (an axiom typed at corpus carriers would smuggle the dictionary —
  the V4/M15 trap).
* **LIT-5 (BNS precision — CANDIDATE, NOT declared; REV-1 stripped form).**
  Bauch–Nart–Stainsby, *Complexity of OM factorizations of polynomials over local fields*,
  LMS J. Comput. Math. 16 (2013) 139–171, **Theorem 3.13, pp. 154–155**: for f, g ∈ ℤ_p[x]
  monic separable of common degree with f ≡ g mod p^{δ+1} (δ = v_p(disc f)), every OM
  factorization of f is an OM factorization of g — AND NOTHING MORE. The rev-0 draft's
  extra clauses ("OM representations remain valid", "trees correspond", "σ(f) = σ(g)")
  were V4-refuted as strengthenings the published theorem does not state; they are now
  PROOF OBLIGATIONS inside O-2 (K-DICT-OB1 tree correspondence, K-DICT-OB2 σ-invariance).
  Remaining duties before declaration: verbatim published-text transcription (this exact
  paper has documented arXiv-vs-journal numbering shifts — V1 items 1/5), GMN-side typing
  consumed only through O-2, guardian audit, sign-off. Status: LITERATURE-CANDIDATE.
* **LIT-6 (Denef–Igusa cell recursion).** `PadicMeasure.AX_cellRecursion` — measure route
  ONLY; the count-native route (the one this tree completes) does not consume it. Status:
  LITERATURE, audited; out of the critical path.
* **LIT-7 (Del Corso–Dvornicich / tame FE).** Annex only (A-2). The old global axiom was
  RETIRED 2026-07-21 as unfaithfully targeted; any future use must be re-stated after
  exhaustiveness + the projective bridge. Status: LITERATURE-CANDIDATE, annex.
* **LIT-8 (classical toolkit).** Krasner's lemma + Newton–Hensel root polish (used inside
  the VERIFIED M05 Lemma D with explicit constant 2v+1); Vandermonde/resultant identities
  (Bourbaki Alg. IV §6; Sylvester determinant = ∏ Res); Igusa §7.4 change of variables /
  inverse function theorem; Gauss/Möbius irreducible counts. Status: LITERATURE, standard;
  exact numbering to confirm at each declaration site.

### 2.1 Base lemmas — the June skeleton (`docs/HUMAN_PROOF.md` §§3–12)

These are the load-bearing elementary layers. They predate the July dual bar; grades are
per-node. The deep inductive core of the June write-up (L2core/BB3-∞) is SUPERSEDED by the
MOVES tower (§2.2) — the rest remains exactly the mathematics the assembled proof uses.

* **B-1 (L1, Hensel residue-splitting is measure-exact).** Distinct-irreducible residue
  factorization lifts uniquely; the Hensel map is a measure-preserving analytic isomorphism
  with unit-resultant Jacobian; conditional laws of coprime factors are INDEPENDENT;
  type(f) = ⊔ type(F_j); degree-δ clusters base-change with q ↦ q^δ.
  Status: PROVED-UNVERIFIED (`lean/notes/L1_proof.md`-era document referenced by
  HUMAN_PROOF; 2000/2000 unit-resultant checks at the non-reduced witnesses). Consumed by
  everything; the MOVES architecture re-proves the split it needs inside §T/§D4-R.
* **B-2 (L3, residue shape counts are universal polynomials).** Finite fields are perfect ⇒
  no inseparable irreducibles in ANY characteristic; #{type-λ monics over F_Q} = S_λ(Q) for
  one polynomial S_λ ∈ ℚ[t], p-independent. Status: PROVED-UNVERIFIED at document level
  (`lean/notes/L3_proof.md`), with the counting core VERIFIED-LEAN (`L3.lean`,
  `L3Gauss.lean`, `L3Squarefree.lean`, Lean-core); exhaustive checks over
  F_2…F_27 incl. wild.
* **B-3 (L4 = BB1, Newton-cell volume is a char-independent q-power).**
  μ{g : NP(g) = Π} = (1−Q^{−1})^{V(Π)}·Q^{−A(Π)} with V, A pure lattice data; closed
  exponent formula (`lean/notes/BB1_exponent.md`). Status: core VERIFIED-LEAN
  (`L4.lean` `cellVolume_eq`, proved not axiomatized) + PROVED-UNVERIFIED document
  (`lean/notes/L4_proof.md`); 7226-polygon numeric identity check.
* **B-4 (M6, order-r residual equidistribution).** On a fixed order-(r−1) type's cell, the
  order-r residual polynomial is Haar-equidistributed over monic degree-d_r polynomials
  over the (finite) order-r residue field — the lemma converting counts into volumes at
  every OM order. Status: order 1 = B-3 (VERIFIED-LEAN); order r: PROVED-UNVERIFIED
  (`lean/notes/M6_lemma.md`, derived from GMN Def 2.20/2.21 coordinates), empirically
  validated through OM order 4. Its modern descendants: the M08 OL-B "twisted residue"
  audit (leaf O-9) carries the same content at the built tables.
* **B-5 (R1, Vandermonde pushforward).** |det dΦ| = |V(α)|; completely-split regions push
  forward with weight q^{−d(T)}; self-similar root integral closes geometrically with
  exponents w(m) = m(m+1)/2 − 1. Status: PROVED-UNVERIFIED (`lean/notes/R1_complete.md`;
  verified numerically at wild p = 2, 3).
* **B-6 (L5fix, termination + finite p-independent shape menu).** The cluster recursion
  terminates on the separable locus; the shape menu at degree n is finite and
  p-independent (leaf-different bound (d−1) + d·v_p(d) via LIT-2); ℚ_p defectless; size-e
  self-loop sums to 1/(1 − Q^{−(e(e+1)/2−1)}). Status: PROVED-UNVERIFIED
  (`lean/notes/L5fix_complete.md`); the general-n *skeleton finiteness* at the modern
  (MOVES/species) vocabulary is leaf **O-13** — proved there only at n = 1, 3, with the
  53-letter n = 3 catalogue dual-verified inside §M-SPECIES.
* **B-7 (L6M4, the finite linear solve over ℚ(q)).** Densities assemble into A(q)C = b(q),
  block-triangular in largest-cluster size, p-independent coefficients, cyclotomic
  non-vanishing pivots; Cramer ⇒ R_σ ∈ ℚ(t). Status: PROVED-UNVERIFIED
  (`lean/notes/L6M4_complete.md`; exact at n ≤ 3). Modern verified counterpart: the §S-RESUM
  solve + spectral-escape package (T-8) and the (REG-p) analysis (K-13).
* **B-8 (L2core / BB3-∞ as written in June).** Per-shape cluster volume p-uniform at all
  OM orders, "modulo G-A′". Status: **SUPERSEDED** — the strong form is now carried by the
  dual-accepted tower §B2-DEF + composition §C + mass law §D4-R (T-1..T-3) with the open
  kernels made EXPLICIT (the June "(modulo G-A′)" hid exactly what §2.3 now names). Do not
  cite B-8 for anything; cite T-1..T-3 + leaves.

### 2.2 The verified conditional core — the MOVES write-up (ledger `lean/notes/MOVES_2026-07-24.md`)

Every node in this layer is **VERIFIED-DUAL**: accepted at the campaign's dual bar —
consecutive clean Codex passes AND an independent fresh-context Fable pass on identical
frozen text (passes named in `docs/PROJECT_STATE.md` §5 updates, 2026-07-26/27/28; the dual
bar caught six decorrelated criticals across the campaign, so the grade is earned, not
formal). Each node's conditionality is EXPLICIT: the named open kernels it consumes are the
§2.3 leaves. Twenty-two sealed numeric gates ride this layer (gate names per node).

* **T-1 (§A + §B1 + §B2-DEF — the move ledger and tower induction).** The carry-algebra
  stage tower (graded pieces, digit alphabets, weight lattices, the D.0–D.11 move laws) and
  the tower induction over stages: each OM read is one of finitely many MOVES with explicit
  transition data, uniformly in p. Dual-accepted 2026-07-26/27 (13-pass arc for §B2-DEF;
  Case-K sealed gates v2 all-pass). This is the rigorous replacement of B-8's induction.
* **T-2 (§C — composition along read histories).** The per-move digit/threshold ledgers
  compose along a read history; realizability = (NA)+(HV)+(SAE) with the span-entry
  condition (added after a Fable-found critical: an empty stratum predicted 62,500 members);
  counting engine validated on a fresh species mix. Dual-accepted 2026-07-27 (Codex 16+17 +
  Fable confirm; Case-L gate, β-strip 760σ). Its ONE deferred proof obligation C.1.5 (the
  graded-presentation "downsets are literal digit systems" layer) is consumed by leaf O-1.
* **T-3 (§D4-R — the per-shape-prefix mass law).** On the branch-tree architecture T_can(f):
  SUM + EVENT mass laws with multiplicity (rebuilt after a Fable-found critical — factor/
  side selection is not a function of f). Dual-accepted 2026-07-27 (Codex pass 11 + Fable;
  gates D4-n3 exact over 404,128,692 boxes, D4-m2 33/33). Kernel D4R.0-K (offset-P totality)
  dual-verified separately; residual (c) verdict-pin cap owned by T-6/leaf O-6.
* **T-4 (§M-SPECIES — the finite letter catalogue).** The species/letter alphabet of tree
  node data is finite and p-free; n = 3 catalogue = 53 letters, rebuilt independently by the
  Fable verifier from the definition alone; entrance-finiteness proof genuine. Dual-accepted
  2026-07-27 (gate M-n3-V2 exhaustive N = 1..7, 45 thresholds sharp both sides). General-n
  skeleton finiteness in the working vocabulary = leaf O-13.
* **T-5 (§H-DOMAINS — the height-domain package).** The H-LIST construction (slack/cone
  injectivity) delivering the height-resummation domains; survived six break campaigns
  (last: 409/409 attack suite). Dual-accepted 2026-07-27 (gate H-n3 151/151 vs factorpadic).
  Its six H.6 fences gate the [1v]-FULL event (table value-correctness, leaf O-11).
* **T-6 (§T-ASSEMBLY — tree assembly, ns-null, TB-CAP).** First-split recursion tying the
  tree series to per-branch data; the (ns-null) theorem (non-separable leaf loci are
  Haar-null) PROVED and verified four times; TB-CAP: (τ-hen) leaves cap at N_V = 1
  unconditionally, (τ-irr) leaf verdict classes are exact finite unions of shape-computable
  level-N(η) cylinders (perimeter-conditional). Dual-accepted 2026-07-27 (gates SIB 32/32,
  T-n3 21/21). Consumes leaves O-1/O-3/O-10 for its open kernels ((SIB-STEP), CUT-WD).
* **T-7 (§V-TABLES + §R-LEDGER — the symbolic value tables and the obligations ledger).**
  The per-species symbolic tables and the explicit obligations ledger (EQ-2 refutation-
  stability defect found by the Fable spiral and fixed with a per-position-class pin).
  Dual-accepted 2026-07-27 (V-n3 178/178 exact; tables exact at off-census q = 16/25).
  Open content routed to leaves O-8 (EQ-2), O-9 (cl6/order-r census), O-11 (value
  correctness).
* **T-8 (§S-RESUM — the depth resummation / block solve).** The finite block-triangular
  solve with spectral escape: sub-stochastic transition blocks, det(I−K) ≠ 0 via escape
  mass, geometric resummation of self-loops — the modern, verified form of B-7.
  Dual-accepted 2026-07-27/28 (gates RESUM-n3 — the assembled pipeline computes the correct
  n = 3 densities, 65/65 exact, PARI 0 mismatches — and STATE-probe-2). The per-prime
  regularity residue is K-13/O-12.
* **T-9 (§X-EXHAUST — the exhaustion index table).** The explicit index/weight-charge
  table pricing undecided mass against v_p(disc); two censuses totaling 6,181 polynomials,
  0 violations. Dual-accepted 2026-07-27. Its honestly-open kernels are leaves O-4
  (EXHAUST/drainage general n), O-6 (TRACK-COUNT), O-7 (WEIGHT-CHARGE X.1b, X.2 rates).
* **T-U (§U-SQUEEZE — THEOREM U, the closer).** The root in full honest form: one fixed
  R_σ ∈ ℚ(q) per type at every (REG-p)-satisfying prime including wild, Σ_σ R_σ = 1, by
  the two-sided level-N squeeze over the assembled pipeline — **conditional on the complete
  displayed kernel ledger (§U.SQ.6)**. Dual-accepted 2026-07-28 (the (REG-p) separateness
  spiral closed with both verifiers concurring; the Fable side's own wrong R(2) falsified
  live by the bracket discipline — the discipline works). SQ.6's displayed list IS §2.3.
* **T-11 (JOINT-D1 + the D1 development bijection).** The unitriangular φ-adic development
  bijection and its depth-1 joint uniformity; D1-marginal proved AND machine-checked
  (`OM/DevBijection.lean`, Lean-core); JOINT-D1 accepted as part of the T-1 perimeter.

**How §2.2 proves the root, given the leaves (the one-paragraph assembly).** T-1/T-2 turn
one OM read into finitely many p-free MOVES and compose them along histories (thresholds
by T-2's ledger); T-4 makes the state alphabet finite and p-free; T-3/T-6 convert per-shape
strata into mass laws on the branch tree T_can(f); T-7's tables evaluate each letter's
transition weight as a fixed element of ℚ(q) (B-2/B-3/B-4 are the elementary inputs); T-5
resums heights; T-8 solves the finite linear system with nonzero pivots — producing R_σ —
and T-9/T-U squeeze the level-N counting brackets so that the solved value IS the density
at every (REG-p) prime, wild included. Every place this chain touches the actual p-adic
factorization semantics of a specific polynomial (rather than the symbolic engine) is a
named leaf below; that is the honest residue of the whole project.

### 2.3 The kernel ledger — hypothesis-row verdicts (K-*) and the OPEN leaves (O-*)

First the row verdicts established by the 2026-07-31 open-math fleet (18/18 Fable + Codex
twins + numerics; adjudications in `BRIDGE_ADJUDICATIONS_2026-07-30.md` §§OPEN-MATH),
because they prune the tree; then the open leaves in §2.4-style detail.

| row (census name) | mathematical content | verdict + evidence |
|---|---|---|
| K-1 `BK.cl11_ksub` | at a branch whose sub-block degrees sum ≤ e with m·e ≤ e: m = 1, c = 1 (pigeonhole) | **PROVED (all n), VERIFIED-DUAL + Lean** — M09: Fable + Codex independent identical proofs; `MovesU/KsubGeneral.lean` Lean-core; N4: 0/240,525 violations |
| K-2 `BK.cl17` (W17ii) | the RS4-chain counting squeeze at every repaired chain | **PROVED, VERIFIED-LEAN** — `w17ii_wave4`, Lean-core, every chain; N5: 12k adversarial configs |
| K-3 `K7.track_restarts` (as typed) | population-count cap on recentering nodes | **REFUTED-AS-STATED** — M01 caterpillar family f_m = (x−a)(x−b), v_p(a−b) = m+1 forces ~v_p(disc)/2 consecutive recenterings, every p, every n ≥ 2; N7 confirms growth (49 > 36 at n = 6). Repaired math = leaf O-6 |
| K-4 `seam.count_tie` (as typed) | per-tree fiber counts scale by p^n per level | **REFUTED-AS-STATED on ns-carrying trees** — M02 exact-square family scales ×p not ×p², PARI-verified; ns-free repair reduces the row to CYL = leaf O-1/O-3 |
| K-5 `ReadLocality` (all-sites) | one tree-keyed read-locality threshold for all sites | **REFUTED-AS-STATED** — M03 Eisenstein family f_N = X² + p^N defeats every tree-keyed cutoff; the TRUE statement is per-site (leaf O-1) |
| K-6 `BK.vp_sound` (as built) | finite-level verdict soundness incl. ns leaves | **REFUTED-AS-STATED** — M06: the class (x+p)² mod p^N realizes THREE splitting types (PARI-verified) while an ns-tree fibers; ns-free repair reduces to LIT-3 + LIT-4 + leaves O-1/O-2/O-5 |
| K-7 `cl19_rep` (as typed) | joint-cell invariant-history representation | **REFUTED-AS-STATED** — M11 dual (4 ≠ 0 cross-multiplication at n = 2; unique slot that internalizes its carrier quantifier). Repaired carrier form = part of leaf O-14 |
| K-8 `SibJcRows` (as typed, ∀-cell-assignment) | sibling independence / joint-cell product law over ARBITRARY cell data | **PLAUSIBLY-FALSE-AS-STATED** — M07 three adversarial routes (correlation cells break the m = 2 product law by exactly p; Lean-core gate `SibJcRouteA`, 5¹³ ≠ 5¹²). Adapted-cell math = leaf O-10 |
| K-9 `BK.cl6` | polygon-geometry count laws | n = 2 **PROVED** (repaired pack, Lean witness); level-1 strata at EVERY n PROVED-UNVERIFIED (M08 Thm 2, 46-strata machine check); order ≥ 2 = leaf O-9 |
| K-10 `cl15_align` | engine index ≤ GMN index (finite-sum face) | **LITERATURE (LIT-1 Thm 4.18(1)), scoped by M15/M16**; engine-side residue = leaf O-2 (OL-1..OL-4); axiom keyword correctly WITHHELD until GMN-side carriers exist |
| K-11 `bridge : ZpBridge` (e·f = deg laws) | e, f invariants at the integral closure; pointwise e·f = deg; factor assembly | **PROVED over LIT-2** — M16 + Group E (Lean, footprint = `AX_integralClosure_dvr` + core); V3 guardian audit PASSED |
| K-12 `BK.env_tendsto` (n = 2) | drainage at n = 2 | **VERIFIED-LEAN** (`hExhaustP` envelope (⌊N/2⌋+1)·p^{−(N−1)}); general n = leaf O-4 |
| K-13 (REG-p) finiteness | the set of primes where the pinned rational data degenerate is finite, exactly characterized, effectively bounded; theoremU fires at a cofinite set | **PROVED + Lean-formalized** — M17 Theorems A/B/C + Corollary U; `MovesU/RegPFinite.lean` 14 thms Lean-core; N6 25/25. Emptiness at the intended instance = leaf O-12 (schema-level emptiness is REFUTED by a compiled countermodel, so O-12 is genuinely about the OM instance) |
| K-14 `RealizationComplete` (bare) | every realized mark-census extends/grafts unconditionally | **REFUTED-AS-STATED** (M18 Theorem 0, compiled toy negation); **equivalent to the one-step law MarkGraft** (Theorems A/B/C, compiled, lossless); instance truth = duties (I0)–(I3) = leaf O-3 |
| K-15 `cl13_wf`, `cl13_syntax`, `S : SolveData`, VerdictDeg/DegConsDelta laws | well-foundedness, syntax, solve seams | PROVED / DISCHARGED in Lean (census §2); no open mathematics |

**Consistency note (the countermodel closure, from the IFK blueprint §2, re-checked):**
every countermodel above is EXPLAINED by the repaired statements — the M02/M06 families
violate ns-freeness; M03's family violates only the all-sites quantifier; M18's toy
violates census-coupling (I1); the X1B 155,648-violation countermodel killed per-node
summing, which no repaired statement performs. No countermodel touches the root.

### 2.4 THE OPEN LEAVES (every one a mathematical statement; O-1..O-5 = the IFK)

**The convergence finding (verification round 1, synthesis; IFK blueprint §0):** the five
independent reductions M02/M05/M06/M12/M18 all terminate at ONE theorem family — "the
canonical digit-reading classifier faithfully realizes the semantic Okutsu–Montes object" —
whose four faces are O-1 (read), O-2 (dictionary), O-3 (run), O-5-part (halt/assembly).
IFK status: blueprint rev-0 **REJECTED at Codex plan review** (V4, 26 findings);
**REVISION 1 LANDED same day** (commit 9fcdc2d, appended to the blueprint): all 26
findings ACCEPTED and dispositioned — the K-RUN/designer-data circularity resolved by
re-attribution (RunRealizerExists is an UPSTREAM HC-1/JetSetup supply, its derivation row
DELETED); the BNS axiom stripped to the published δ+1 clause; eleven derivation arrows
re-priced with NINE new named obligations (K-OB-A finite-site assembly, K-OB-B
inStratum→realized bridge, K-OB-C Okutsu proximity, K-OB-D certificate-firing
completeness, K-OB-E continuing⇒repeated-residual, K-DICT-OB1 tree correspondence [the
hardest face], K-DICT-OB2 σ-invariance, K-RUN clause 4 acceptance, (I3-rc)); honest
recount = 8 named rows + 10 F-chain sorries retired outright, 4 more each costing one new
lemma. Codex re-review of the full revised document is launched, NOT yet accepted.
The FIRST falsifier has run and **SURVIVES exhaustively**: U6/IFK-U6-FIRST (M18 Tests
A–C at all four (n, p) ∈ {2,3}² incl. both wild corners: ZERO phantoms, counting tie
T = T̂ on all 174 length-2 strata / 369 realized chains, equal-fiber law EXACT with zero
tolerance; PARI (e,f)-multiset validation 1600 samples 0 mismatches) — falsification-
grade evidence that the heaviest face's depth-2 content is TRUE at the intended
semantics; it DISCHARGES nothing (the bare row is false without instance structure).
The faces are stated below as mathematics, with the revision's corrections folded,
independent of the blueprint's review fate.

Standing preconditions for O-1/O-3/O-5: f monic degree n, separable (off disc = 0); trees
range over ns-free carriers (the fence-24/26 repair — load-bearing: K-4/K-6 are FALSE
without it).

* **O-1 (K-READ — per-site bounded read; census: count_tie's CYL/L1, M03's K1/K2,
  M06's OL-1 mechanics, M05's OL1-ii finite-read half).** OPEN. Statement (M02 §5 L1 +
  M03 §5, the per-site form): for every lawful OM history-site (H, ν) there is a modulus
  L(H, ν), computable from the node data alone (the read ceiling: 1 + the largest
  side-line intercept / constrained band level over H's reads), such that whether the
  canonical run on f reads (H, ν) depends only on f's coefficient digits below level
  L(H, ν) — stated (per REV-1 finding 2) as an explicit two-lift comparison over sites
  REALIZED on the run: for x, x′ agreeing below slot n·L(H, ν), the run reads (H, ν) at x
  iff it does at x′, uniformly over working levels ≥ L(H, ν); and (K2, window closure) at
  a decided ns-free tree state, deep candidate children are excluded at ALL boxes agreeing
  below the tree threshold. Two tiers: **thr-tier** (tree-intrinsic modulus — project
  mathematics, no citation exists; what count_tie as typed needs) and **δ-tier** (modulus
  δ+1, δ = v_p(disc f)) — per REV-1 finding 3 the δ-tier is NOT read off LIT-5 directly:
  it is a DERIVED face conditional on O-2 (incl. OB1/OB2) + O-3. The all-sites version
  is REFUTED (K-5); any attack must be per-site. Mechanism already verified in parts: each
  box-dependent clause is exact-valuation pins / one-sided valuation bounds / residual
  digit reads at pinned heights below the ceiling, each a finite Boolean combination of
  digit conditions through the graded-presentation dictionary (T-2's C.1.5 layer; the Lean
  carry-algebra spine CL12/CL13 supplies no-cancellation + level-detection mechanics).
  Best partials: M03 §5–6 (K1)+(K2)+chart ⇒ TreeNStable derivation sketch; M02 Lemmas A/B
  (count_tie ⇔ per-tree scaling, rigorous). Consumed by: K-4, K-6, O-3, O-4, O-5, O-10,
  T-6.
* **O-2 (K-DICT — the engine ↔ GMN dictionary; census: cl15_align's OL-1..OL-4, M06's
  OL-3, V1's critical (ii)).** OPEN. Statement: a correspondence Θ between canonical-
  engine branch histories (node data: e, h, g, μ, recentering digits, …) and GMN types of
  order r with representatives, such that (i) accumulated invariants match:
  (accE, accF) = (e₁⋯e_r, f₀⋯f_r), saturation accE·accF = d ⇔ ω = 1; (ii) [order
  placement, M15 OL-1] every certified increment node maps injectively to a GMN order with
  a type realizing it; (iii) [normalization crossing, M15 OL-2] the engine's raw-frame side
  read transports to the v_r-normalized frame with the same (e, h) and per-certified-node
  ind ≥ 1; (iv) [admissibility, M15 OL-3] the engine's canonical key lifts form one
  universally-fixed GMN-admissible representative family; (v) [= **K-DICT-OB1**, REV-1's
  named form of the population clause / V1 item 8 — THE HARDEST FACE, deep-wild-tower
  hard] the tree correspondence: equality of admissible OM factorizations ⇒
  correspondence of the refinement traces/trees the classifier produces, with
  recentering-population nodes matched one-to-one to same-degree refinement iterations of
  the published Montes flow (needed to consume any BNS iteration/precision bound);
  (vi) [= **K-DICT-OB2**] σ-invariance under the paper's OM-factorization/Okutsu-
  equivalence relation (without it LIT-5 yields factorization data, never σ(f) = σ(g)).
  Θ is typed (REV-1 finding 1) as a FUNCTION per fixed separable f, from the realized
  runs on f to the GMN types of f, injectivity/surjectivity as separate clauses. ONE
  shared carrier — M06/M15/M12/V1 each independently demand it; never re-derive per row. Given Θ + LIT-1 Thm 4.18(1), the ALIGN row follows by the
  machine-checked reduction KE8. Falsified-adjacent guardrail: the engine's ⟨true,false⟩
  certified-set exclusion of T1-recenterings is load-bearing (M15 §7's worked ℤ_2 family).
  Consumed by: K-10, O-5, O-6 (Lemma A's e·g form), O-7, LIT-4/LIT-5 consumption.
* **O-3 (K-RUN — realization faithfulness; census: inStratum realization (V1 critical
  (i)), M18 duties (I0)–(I2), M02 L2/L3, RunRealizerExists, M12 (X1)/(X4)).** OPEN.
  Statement: at every level N and residue class x, the realized run set of the canonical
  classifier on x is EXACTLY the level-N truncation of the semantic OM tree T_can(f) of
  any lift f: (no-phantom) every realized pruned history is a prefix of a genuine OM
  branch; (no-missing) every OM branch prefix with resolution level ≤ N is realized;
  (nonempty locus) every fresh-frame-lawful assignment chain (per-step reads menu-lawful
  at the frame state — the REV-1 finding-4 indexing the U6 probe validated; the free-
  formal-chain wording was tautological) has a witnessing polynomial in its digit
  cylinder; (acceptance — **K-RUN clause 4**, REV-1 finding 10, = M05's OL1-ii made
  face-content) the built certification predicate accepts exactly the realized = semantic
  runs. REV-1 auxiliary obligations priced here: **K-OB-B** (stratum-relation membership ⇒
  realization — the V1-critical bridge is itself a lemma, not a reading of no-phantom),
  **K-OB-C** (Okutsu proximity: semantic-prefix membership ⇒ root-tracking disk at radius
  w − C_φ; GMN-side, candidate cite to pull), **K-OB-E** (a continuing OM node
  presupposes a repeated residual factor — GMN-side semantic theorem), **K-OB-A**
  (finite-site assembly: the finitely many sites of a row share fiber agreement below the
  max modulus). NOTE (REV-1 finding 20 / §R2): `RunRealizerExists` is NOT a corollary of
  this face — it is an UPSTREAM supply from the stage-tower cone (interior half PROVED
  from coherence: `interior_center_realizer_exists`; residue = the (S6b′) monomial-shape
  clause + the last-node landing flank, countermodel search LIVE, so far positive gates,
  not negations); listed under O-14.
  Status detail: length ≤ 1 instances COMPILED (forge: two realizable root nodes,
  child_cover exact at n = 2); the ramified 2-node history is HistoryCoherent ∧ Realizable
  ∧ InBox under the repaired keying (HK23 positive gate, Lean-core); U6 falsifier SURVIVES
  exhaustively at length 2 (see above); depth ≥ 2 / general n OPEN. Consumed by: K-4,
  K-6, K-14 (MarkGraft duties I0/I1 + the named (I3-rc) premise), O-4 (clause 4), O-7
  (via K-OB-B), F-chain.
* **O-4 (EXHAUST/drainage at general n; census: BK.env_tendsto residual; June hExhaust).**
  Statement: the canonical OM classifier decides almost every class: undec(N) → 0 at every
  prime including wild, with (optional, for rates) an explicit envelope. VERIFIED core
  (M05 + V2, the exact upheld scope): Lemma A (drainage ⇔ a.e.-decidedness — cylinder
  mass identity), Lemma B (disc is degree n−1 in a₀ with leading coefficient ±n^n — no
  cancellation), Lemma C (discriminant tail bound, exponent ⌈(m − n·v_p(n))/(n−1)⌉),
  Lemma D (Krasner local constancy of splitting type at modulus 2v+1, explicit constant,
  wild-valid), Theorem E (the SEMANTIC classifier drains with rate ~p^{−N/(2(n−1))} at
  every prime; wild term = finite additive shift n·v_p(n)) — V2 items 5–8 upheld exactly
  these; V2 corrections folded: OL1 is SUFFICIENT for drainage, not equivalent; the T5
  optimality/"real gap" claim is WITHDRAWN (superset lower bound — invalid). OPEN residue:
  **OL1-ii** — the canonical run on each fixed separable f terminates with all reads below
  a finite N(f) AND the project classifier's certification predicate accepts there (the
  agreement seam; = O-1 + O-3 at the run's sites; the "finite run ⇒ finite stable
  certificate" step is a V2-flagged justification gap, not a free observation); and
  **OL2** (rates for the OM classifier): N(f) ≤ A(n)·v_p(disc f) + B(n) — LIT-5 territory
  through O-2. GMN Cor 4.19 (termination at finite order) is the LITERATURE half of OL1-i;
  V2 item 4 flags that "≤ ind(f) nontrivial steps" needs the O-6-style charging argument,
  not just the corollary. n = 2 is closed (K-12).
* **O-5 (K-HALT + ASSEMBLY; census: vp_sound residue, M06 OL-2).** Statement: at an
  ns-free leaf of a realized run, the halting verdict is the true factorization datum
  ((τ-hen) leaf: LIT-3; (τ-irr) saturated leaf: LIT-4 through O-2), AND [ASSEMBLY = M06
  OL-2] the leaf map {leaves of the halted tree} → {monic irreducible factors of g} is a
  bijection onto factors-with-multiplicity with g = ∏(leaf factors) — for EVERY lift g of
  the decided class — so type(g) = typemult(T). Backbone known (GMN Def 3.10/eq. (37) +
  Cor 4.19 + defectlessness, LIT-1/LIT-2); OPEN content: the bookkeeping that the
  completeness clause (all realized histories are chains) + degree checksums rule out
  orphan factors at finite level — project mathematics on top of O-1/O-3. Consumed by:
  K-6, O-4 (verdict at acceptance), T-U's value ties.
* **O-6 (TRACK-COUNT/K7 at the repaired runCount form; census item 2; M01).** Statement
  family over branch histories H of T_can(f): (runCount) the number of maximal recentering
  runs ≤ ⌊log₂ n⌋ + 1 [reduces to Lemma A below + the proved list lemma (R)]; plus the
  budget clauses (zero_gain, genuine_bound, slice_bound: an explicit p-free bound T(n,N)
  on threshold-≤N trees). REDUCED (M01 §3) to: **Lemma A** (key-degree budget: every
  continuing increment multiplies key degree by e·g ≥ 2; ≤ ⌊log₂ n⌋ increments — LIT-1
  known, needs the e·g strengthening through O-2), **Lemma B** (branch-degree consumption —
  carried), **Lemma C (OPEN, the real seam)**: run-break locality — within one maximal
  recentering run the key weight climbs strictly in one common lattice, and a ladder is
  abandoned only at an intervening increment/branch node (the cross-frame comparability
  bookkeeping; census: zero (t3)-breaks over 3.9M members), **Lemma D (OPEN)**: affine
  height/weight budgets h*(N), w*(N) with all key weights in (1/D(n))·ℤ, D(n) | lcm(1..n)
  (the dnLattice duty = M12's (X2)), **Lemma E** (minor corner). With A–E: L(n) =
  (n−1) + 2⌊log₂ n⌋ ≤ n², all clauses p-uniform. N7 numerics support the repaired form.
* **O-7 (WEIGHT-CHARGE / X.1b; census item 3; M12 + V1).** Statement: along any branch of
  T_can(f), #(recentering-population nodes) ≤ s(n)·(1 + v_p(disc f)) with s(n) = 2·D(n)+1
  (count form; the numerical s = 2 cap at the intended instance SURVIVED V1's caterpillar
  stress test — the resultant term pays — and is NUMERICALLY-SUPPORTED, N7). REDUCED
  (M12, assembly machine-checked KD5/KD6/KD10; face-pricing per REV-1 rows 12–15): to the
  engine-interface lemmas **(X1)** cell ⇒ root-tracking disk = O-3 + O-2 + **K-OB-C**
  (the proximity bound is a separate GMN-side lemma — membership alone gives no radius),
  **(X2)** lattice + strict climb (= O-6 Lemma D), **(X3′)** singleton certificate
  threshold r ≤ 2v(f′(θ)) + 1 = O-5's soundness + **K-OB-D** (that the certificate FIRES
  within slack κ₀ = 1 is a COMPLETENESS lemma, not K-HALT soundness; from T-6's TB-CAP
  (τ-hen) N_V = 1 + the (D3) window read), **(X4)** first-read wildness = O-3 + **K-OB-E**
  — plus O-2 for the alignment leg. V1's two criticals (inStratum quantifier over-reach;
  tree/iteration correspondence) are exactly K-OB-B and K-DICT-OB1: no separate
  obligation. The pricing core (Lemmas A/B + Theorem WC, valuation-theoretic)
  is PROVED-UNVERIFIED in M12 §2.2–2.3 given the interface.
* **O-8 (X.2 linear rates + EQ-2; census items 4–5; M13 + M14).** Two statements:
  (a) [X.2, cl3_aff/cap/progress] linear progress pricing: threshold(b) + cap(b) ≤
  2 + 4n·maxH(b) on fourth-piece branches (2 + 2n·maxH for n ≤ 3) — REDUCED (M13, glue +
  KE9 Lean-proved) to **OL-A** (the D.11 per-move cylinder-ledger endpoint in MAX currency
  composed along a history — the faithful form of the threshold law; T-2's deferred
  composition duty), **OL-B** (TB-CAP cap identification — recorded proved,
  perimeter-conditional, T-6), **OL-C (new, OPEN)**: the flank-cofactor floor at n ≥ 4
  non-divisible key degrees (vacuous for n ≤ 3); the √N form is proved and the √N barrier
  is an artifact of the lossy Σh currency. `cl3_tails` (X2-TAILS measure/cone tail
  estimate) is a SEPARATE open estimate (owner §H-DOMAINS family).
  (b) [EQ-2, cl8] the carry-algebra alphabet law: at δ-stable position classes the
  re-based slot map is F_{p^δ}-linear and a_δ = δ·a₁ — PROVED-UNVERIFIED conditional on
  the explicitly displayed (R1)–(R4) (the REL.1 re-base slice: the stage axioms, digit/
  alphabet displays, and weight-set recursion hold verbatim over O_δ = W(F_{p^δ}));
  NUMERICALLY-SUPPORTED exhaustively (N8: 199,723 alphabets, 17 fields, 0 violations).
  Open content = (R1)–(R4), i.e. re-proving the T-1 tower laws over the unramified base —
  expected mechanical, nobody has written it.
* **O-9 (CL-6 at OM order ≥ 2 — the order-r stratum census; census item 7; M08).**
  Statement: for a type t of order r with residual field F_{q^{f̄_r}}, the order-(r+1)
  stratum census over O/π^N is q^{E′}·∏_S M_{λ_S}(q^{f̄_r}) — ONE ℕ-valued polynomial per
  stratum, independent of p, O, δ. PROVED at level 1 (order-1 strata, every n, every
  prime power, every complete DVR — M08 Theorem 2, machine-checked on 46 strata;
  PROVED-UNVERIFIED). REDUCED at order ≥ 2 to: **OL-A** (order-r slot/level ledger:
  stratum conditions are finitely many φ-adic digit slots with graded pieces
  F_{q^{f̄_r}}-lines — GMN §2 objects, project ledger), **OL-B** (residual coefficients are
  twisted residues: per-slot a bijection of F_{q^{f̄_r}}, no un-cancelled z ↦ z^a, a ≥ 2 —
  the exponent-map audit; B-4's modern form), **OL-C** (the census formula given OL-A/B —
  proof shape verbatim level-1), **OL-D** (per-row window counts at the built tables).
  No off-the-shelf theorem exists (Chatzidakis–van den Dries–Macintyre gives only
  #X(F_q) = μq^d + O(q^{d−1/2}); Pas gives large-p only). N3 confirms the real packs
  n = 2, 3, 4.
* **O-10 (SIB/JC — sibling independence at adapted cells; census item 8; M07).**
  Statement: on a realized site stratum Σ_c with branch factors f₁, …, f_m, prescribed-
  subtree events of distinct siblings are independent under the level-N counting measure,
  in exact count form. REDUCED (M07 §3.3) to: **K-FACT** (stage factorization — LIT-1,
  citable), **K-LOC (OPEN)**: continuation reads of branch j on Σ_c = OM reads of the
  factor f_j up to cell-constant normalization (residual multiplicativity, GMN Thm 2.26;
  the recentering/lift bookkeeping is the open part), **K-JAC (OPEN, routine)**:
  ρ(c) = Σ v_p(Res(f_i, f_j)) is constant on the cell (root-pair heights pinned by the
  separating side), **K-COUNT (OPEN, the genuinely new lemma)**: the multiplication map
  on factor tuples mod p^N is, for N ≥ thr(c) + ~2ρ(c), a constant-fiber surjection
  (Sylvester determinant + Smith normal form + Newton absorption); small-N boundary
  behavior (OL-4) unresolved — expect an N-guard. Depth-0 slice (Lemma A, factorization
  counting) PROVED. Consumed by: T-6's (SIB-STEP), O-11's product laws, M04's K1.
* **O-11 (SERIES-TIE — the solve-side seam; census: BK.series_tie; M04).** Statement: the
  σ-graded tree series of T_can equals the block-solve value (the [3t] ↔ [3] seam), per σ.
  PROVED-UNVERIFIED at the interface: equivalent to the limiting-density identity
  (Theorem 1); the σ-SUMMED form derivable from count_tie + drainage (Theorem 2) — the
  genuine content is the per-σ refinement. REDUCED (Theorem 4; resummation core — least
  fixed point, Bekić triangularization, Neumann under spectral escape — proved
  self-contained) to: **K1** (per-tree product formula: TREE-EXP/(SIB)/(JC-multi)/CUT-WD —
  = O-10 + T-6), **K2** (spectral escape E0 — partially Lean-formalized, `E0Matrix`;
  the per-pool evidence is K-13's escape package), **K3** (value-correctness of the
  symbolic tables = T-7's [1v]-FULL event, gated on T-5's six H.6 fences), **K4** (mass
  semantics, shared with K-4/O-1). Finding F1: the as-built n = 2 device chain CANNOT
  discharge the row (wrong value triple) — the discharge needs the real n = 2 pack.
* **O-12 ((REG-p) emptiness at the intended instance; census via K-13; M17 OL-1).**
  Statement: at the intended OM instance, for every n, the failing set is EMPTY — i.e.
  N_{Φ_e}(p^m) ≠ 0 at every prime power including wild pools and descent depths.
  Expected mechanism: entries of K_e(p^m) are volumes of continuation events, so K_e is
  substochastic with termination mass > 0 at EVERY prime power ⇒ spectral radius < 1.
  This is a property of the intended instance (schema-level emptiness is REFUTED — the
  compiled admissible countermodel fails exactly at p = 2). Proved at the real n = 2
  instance. Without O-12 the root holds at all but an explicit finite, effectively
  bounded set of primes (K-13) — O-12 is what upgrades "cofinite" to "every prime".
  NUMERICALLY-SUPPORTED (N6 25/25; RESUM-n3 det(I−K_e) exact at pools 2, 3, 4).
* **O-13 (skeleton/menu finiteness at general n in the working vocabulary; census item
  14 `hfin`; June B-6's modern face).** Statement: the set of species-skeletons (tree
  shapes with letter data) at degree n is finite, p-independent. Proved at n = 1, 3
  (the n = 3 catalogue = 53, dual-verified in T-4); the June depth bound (B-6 via LIT-2
  different bounds) gives the mathematical mechanism; OPEN as a general-n statement in
  the T-4 vocabulary (expected: T-4's entrance-finiteness + the B-6 depth bound compose).
* **O-14 (residual transport / instance mathematics; census items 9, 12, 13 + row
  `BridgePre.hStateNe`).** The remaining engine-internal lemmas, all with live partial
  results: (a) **HK-52/HK-11 anchor transport** — the D.8 grading-bridge vertex law under
  the repaired regrade keying: TRUE on the ν_{i+1}.e = 1 sub-perimeter (HK-11a kernel
  landed at e′ = 1), FALSE-SUSPECT at ν_{i+1}.e ≥ 2 (compiled stretch obstruction
  HK52_stretchGate — the factor-2 stretch at the coherent 2-node carrier); the ≥ 2
  disposition is sign-off item 28 — mathematically: determine whether the vertex-transport
  law needs the e′ = 1 guard (expected yes; then the guarded law is the true statement);
  (a′) **RunRealizerExists** (re-attributed here by IFK REV-1 §R2 — an upstream
  stage-tower supply, NOT a K-RUN corollary): every coherent history's designated
  realizer exists — interior half PROVED from the re-keyed coherence
  (`interior_center_realizer_exists`, Lean-core); open residue = the (S6b′)
  monomial-shape support clause at deg Φ > 1 + the last-node landing flank (a final node
  carries no recentering record; needs the landing threshold law or a quantifier
  re-adjudication — countermodel search LIVE);
  (b) **cl19 repaired carrier form** (post-K-7): the O1–O3 semantic ladder for the
  jc-invariant-history representation at a REAL carrier pack; (c) **hStateNe** (state
  nonemptiness — expected derivable; derivation attempt owed); (d) the wave-D n = 2
  carrier POPULATION (building the real instance the discharges run at — engineering on
  the math side of the boundary, listed for completeness).

**Annex nodes (out of critical path by directive):**
* **A-1 (M1, monic → projective bridge).** ρ(n,σ;q) = |P^n(F_q)|^{−1} Σ_D W_D[σ] over
  residue divisors on Sym^n P¹ = P^n; cluster law read at the reciprocal argument.
  PROVED-UNVERIFIED (statement + skeleton + char-independence; exact at n ≤ 3; two steps
  reduced-to-citation). Re-enters if the root is re-targeted projective.
* **A-2 (L7, functional equation).** Given (U-DENS) + the tame palindromic form at
  p > n (LIT-7), the identity theorem for ℚ(t) forces R_σ palindromic at ALL primes.
  PROVED-UNVERIFIED (`lean/notes/L7_proof.md` — the proof is three lines given its inputs;
  the honest weight is in LIT-7's faithful restatement, which needs A-1 + exhaustiveness).

---

## 3. THE ATTACK LIST (open leaves in dependency order, with charges and falsifiers)

Dependency spine: O-1 and O-2 unlock everything; O-3 rides O-1; O-5 rides O-2/O-3;
O-4 rides O-1/O-3 (+LIT-5 via O-2 for rates); O-6/O-7 ride O-2/O-3; O-9/O-10 ride O-1/O-2;
O-11 rides O-10 + T-7; O-8, O-12, O-13 are near-independent; O-14 is engine-local.
Per leaf: sharpest reduction on file → recommended prover charge → fastest falsifier.

1. **O-1 (per-site read locality).** *Reduction:* M03 §5 (K1)+(K2) with the read-ceiling
   modulus; M02 §3 (CYL ⇒ count_tie, Lemmas A/B rigorous). *Charge:* prove (K1) at the
   intended semantics by the graded-presentation dictionary — each SideReads clause is a
   finite Boolean combination of digit conditions below ceil(H); then (K2) window closure
   from decided-hull pinning; state per-site ONLY (the all-sites form is dead, K-5); write
   the thr-tier and δ-tier as separate theorems. *Falsifier:* M02 T3–T5 (threshold
   necessity + n = 3 smoke) — any realized read above the claimed ceiling on the
   exhaustive cubic boxes kills the modulus formula; the M03 Eisenstein family must sit
   OUTSIDE every claimed per-site guard (it does — check first).
2. **O-2 (engine ↔ GMN dictionary).** *Reduction:* M15 §5 OL-1..OL-4 (the only residue
   beyond LIT-1 Thm 4.18(1)); M06 §4.2; V1 item 8 (the population clause is what a
   citation cannot give). *Charge:* construct Θ explicitly by induction on order r —
   engine node data → (φ_r, λ_r, ψ_r) with the canonical representative family; prove the
   invariant matching and the injective order placement; prove the population clause
   against the PUBLISHED BNS Lemma 5.11 flow (pull the journal text — the numbering shifts
   are documented, V1 items 1/5). *Falsifier:* the M15 §7 worked ℤ_2 family (GMN §4.3) —
   any Θ must reproduce its order-2 bookkeeping including the T1-recentering exclusion;
   extend the 1548-case ind2 = 2·ind(S) dictionary check to order ≥ 2 samples.
3. **O-3 (realization faithfulness).** *Reduction:* IFK blueprint §1 K-RUN as REVISED
   (four clauses, fresh-frame indexing) + the priced auxiliaries K-OB-A/B/C/E; M18 §6
   duties (I0)–(I2) + (I3-rc). *Charge:* prove no-phantom via K-OB-C (every realized read
   constrains the tracked cluster to a genuine root disk — pull the Okutsu-bound citation
   first) and no-missing by induction on resolution level over T-6's TB-CAP cylinders;
   nonempty-locus at the fresh-frame indexing via explicit witness construction in the
   digit cylinder (the forge method that produced the compiled length-1 instances);
   clause 4 (acceptance) LAST — it consumes O-1. *Falsifier:* U6 Tests A–C at deeper
   strata/lengths and more (n, p) — ANY stratum with T < T̂ is a one-shot refutation (the
   exhaustive length-2 run SURVIVED at all four (n, p) incl. wild; push to length 3); the
   landing-flank countermodel search (3-node extension of H₂ram by a recentering read)
   refutes the O-14a′ supply if anything does.
4. **O-5 (halt + assembly).** *Reduction:* M06 §4 (VPS, ns-free) = (LOC)+(LEAF)+(ASSEMBLY)
   with (LEAF) = LIT-3 + LIT-4 through O-2. *Charge:* prove ASSEMBLY: completeness clause +
   degree checksums ⇒ the leaf-to-factor bijection, via GMN eq. (37) + defectlessness;
   Mathlib-probe LIT-3 before declaring it. *Falsifier:* M06 TD (post-repair box
   regression: verdicts vs PARI factorpadic on decided ns-free boxes, all p ≤ 5, n ≤ 4);
   Krasner-cap surrogate (40/40 so far).
5. **O-4 (drainage, general n).** *Reduction:* M05 §5 (Prop 5.1: OL1 ⇒ drainage; OL1-i =
   LIT-1 Cor 4.19; OL1-ii = O-1+O-3 at the run's sites); OL2 = LIT-5 through O-2.
   *Charge:* assemble OL1-ii from O-1/O-3 (the finite-stable-certificate step must be
   PROVED, not observed — V2 item 3); optionally OL2 for rates after LIT-5 lands.
   *Falsifier:* M05 T3–T4 (Lemma D modulus sharpness; envelope shape N̂ vs δ scatter) —
   already 39/39 + 25/25; extend to n = 4, 5 wild.
6. **O-6 (track count).** *Reduction:* M01 §3, Lemmas A–E with the proved list lemma (R);
   L(n) = (n−1) + 2⌊log₂ n⌋. *Charge:* prove Lemma C (run-break locality) from T-2's D.10
   strict climb + within-frame convexity — the cross-frame comparability bookkeeping is
   the entire content; then Lemma D's lattice from O-2's invariant matching (weights have
   denominator dividing e₁⋯e_r ≤ n). *Falsifier:* the KD9-style census (zero zero-gain
   recenterings over 3.9M members) extended to n = 5, 6 exhaustive shallow boxes; any
   ladder break NOT at an increment/branch node kills Lemma C.
7. **O-7 (weight charge).** *Reduction:* M12 (X1)–(X4) + Lemmas A/B + Theorem WC (proved
   given interface); V1's caterpillar analysis (the resultant term pays). *Charge:* prove
   (X1) cell ⇒ disk (pointwise transport, weaker than O-2's full index accounting) and
   (X3′) from TB-CAP; inherit (X2) from O-6-D, (X4) from O-3. *Falsifier:* M12 T1–T7
   (radius ledger vs v_p(disc)+1 on exhaustive cubic boxes; the T7 ind-form check) — a T1
   violation refutes the radius reading outright.
8. **O-8a (X.2 linear rates).** *Reduction:* M13 (★) via OL-A/OL-B/OL-C + KE9.
   *Charge:* prove OL-A — the D.11 max-currency endpoint composed along a history (T-2's
   deferred composition duty, the ThresholdStep sharpening); OL-C only at n ≥ 4
   (MacLane domination + flank separation sketch on file). *Falsifier:* M13 test 3
   (n = 4 flank-cofactor configurations — OL-C is live and untested at n ≥ 4); the
   worked n = 2 chain (thr = 1 + 2m vs Σh ~ m²/2) is the sanity anchor.
9. **O-8b (EQ-2).** *Reduction:* M14, conditional proof on (R1)–(R4). *Charge:* re-prove
   the T-1 stage laws over O_δ = W(F_{p^δ}) verbatim (the REL.1 re-base pass — expected
   mechanical); then the M14 proof closes the row. *Falsifier:* N8 already exhaustive
   (199,723 alphabets, 0 violations); extend to a ramified-tower stress family if (R1)
   drafting wobbles.
10. **O-9 (order-r census).** *Reduction:* M08 §3 OL-A..OL-D over the PROVED level-1
    Theorem 2. *Charge:* prove OL-A/OL-B from GMN Defs 2.19–2.21 (slot ledger + twisted-
    residue bijection); OL-C is then verbatim level-1; OL-D at table build time.
    *Falsifier:* M08's machine check extended to order-2 strata at p = 2, n = 4 (the
    Artin–Schreier atom) — any non-polynomial count or p-dependence kills OL-B first
    (the 2.5 warning examples show exactly how it would fail).
11. **O-10 (sibling independence).** *Reduction:* M07 §3.3 K-FACT/K-LOC/K-JAC/K-COUNT +
    OL-1..OL-4. *Charge:* prove K-COUNT (Sylvester/Smith + Newton absorption, constant
    fibers for N ≥ thr + 2ρ) — the one genuinely new quantitative lemma; K-JAC's
    multi-side min-slope bookkeeping; adopt an N-guard if OL-4 resolves against all-N.
    *Falsifier:* compile the route-(a) correlation-cell countermodel at a REAL adapted
    cell (needs O-14d's instance) — if the ADAPTED rows also break, the whole [3t]
    architecture needs re-adjudication; count-level PARI checks at depth-1 sites.
12. **O-11 (series tie).** *Reduction:* M04 Theorem 4 over K1–K4. *Charge:* after O-10 +
    T-7's [1v]-FULL event, instantiate the proved resummation core at the real pack;
    verify the value triple against the true densities (Finding F1's test). *Falsifier:*
    the n = 2 value triple (p/(2(p+1)), p/(2(p+1)), 1/(p+1)) — any pack whose solve
    disagrees is dead on arrival; RESUM-n3 65/65 is the n = 3 anchor.
13. **O-12 ((REG-p) emptiness).** *Reduction:* M17 §8: substochasticity + positive
    termination mass at every prime power ⇒ spectral radius < 1 ⇒ no determinant zero.
    *Charge:* prove the entries of K_e(p^m) at the intended instance are continuation-
    event volumes summing < 1 per state (uses T-3/T-6 mass laws — likely a corollary of
    the assembled pipeline rather than new work). *Falsifier:* N6-style symbolic closure
    at more pools; ANY vanishing det(I−K_e)(p^m) in exhaustive small-pool scans.
14. **O-13 (menu finiteness, general n).** *Reduction:* T-4 entrance-finiteness + B-6's
    different-bound depth cap. *Charge:* compose them: a species letter's data is bounded
    by the depth cap (d−1) + d·v_p(d) ≤ (n−1) + n·log₂ n uniformly in p; finitude of
    letters (T-4) + bounded depth ⇒ finite skeleton set. *Falsifier:* enumerate n = 4
    skeletons exhaustively and check the bound's headroom.
15. **O-14 (residual transport).** *Reduction:* (a) HK-11a landed at e′ = 1 + the compiled
    ≥ 2 stretch obstruction; (b) O1–O3 ladder (Codex-supplied); (c) expected-derivable.
    *Charge:* (a) prove the guarded (ν_{i+1}.e = 1) vertex-transport law suffices for
    every consumer (the ≥ 2 case is expected genuinely false — settle it with the
    gate-scale ReadsOf ramified-terminal countermodel, item 28 option (iii));
    (b)/(c) run after O-3. *Falsifier:* the HK52 stretch gate already refutes the
    unguarded ≥ 2 law at the coherent carrier; the question is only the guard's shape.

**Priority note.** O-1 + O-2 + O-3 are the critical path: between them they discharge or
unlock K-4, K-6, K-14, O-4, O-5, O-7, and the F-chain — this is the "one kernel five rows
reduce to" convergence. O-12 and O-13 are small and independent — good early wins.
O-10's K-COUNT and O-9's OL-A/OL-B are the two hardest genuinely-new quantitative lemmas
outside the IFK. Nothing in this list is a statement-repair item: the six parked fence
events (22–27, +28/29) are Lean statement changes whose repair shapes the finished
mathematics will dictate, per the authority.

---

## 4. THE ACCEPTANCE CRITERION (what "verified complete proof" means, operationally)

**Per leaf (Phase B, dual-agent rounds):**
1. A prover produces a SELF-CONTAINED proof note for the leaf's mathematical statement
   (standard language, all hypotheses explicit, every consumed node cited by id from this
   tree; conditional steps displayed as named open lemmas — never papered over).
2. A fresh-context adversarial verifier (Codex preferred — decorrelated blind spots)
   receives the note with MINIMAL context and the standing charge: quote each offending
   passage, classify *critical error* vs *justification gap*, fix nothing.
3. Iterate prover → verifier. **Accept only after ≥ 2 CONSECUTIVE clean passes**, at
   least one from a verifier model different from the prover (the campaign's dual bar:
   Codex clean ×2, then an independent fresh-Fable pass on the identical frozen text).
   A pass with only display/wording gaps is NOT clean.
4. Every leaf with a runnable falsifier RUNS it before acceptance (countermodel-first:
   the falsifier column of §3); a numerics pass is corroboration, never acceptance.
5. LITERATURE nodes: transcribe the PUBLISHED statement verbatim (journal text, not
   arXiv memory — the BNS numbering incident is the standing warning), write the
   faithfulness entry (says-no-more-and-no-less map, both directions), guardian audit,
   Asvin sign-off. An axiom typed at project carriers instead of the source's objects is
   an automatic REJECT (the V4/M15 trap).
6. Status transitions recorded here: OPEN → PROVED-UNVERIFIED (note on file) →
   VERIFIED (passes named). PROVED-UNVERIFIED is never consumed by an acceptance claim.

**Per node already graded PROVED-UNVERIFIED (the §4-list below): same protocol, run as
verification-only rounds (no new mathematics expected).** Roster: B-1, B-2 (doc level),
B-5, B-6, B-7, A-1, A-2; M08 Theorem 2 (level-1 census); M12 pricing core (Lemmas A/B +
WC); M13 Lemmas 1–2 + (★) glue; M14 conditional proof; M04 Theorems 1/2/4 core; M07
Lemma A/B; M05 Lemma D-dependent assembly IF any verifier disputes the V2 scope reading.

**Root (Phase C):**
1. Assemble THE COMPLETE PROOF document: root → §2.2 chain → all leaves, every node
   VERIFIED or LITERATURE-audited; zero OPEN, zero PROVED-UNVERIFIED, zero
   NUMERICALLY-SUPPORTED load-bearing steps.
2. An END-TO-END adversarial pass over the assembled document by a fresh-context
   verifier that has seen NONE of the per-leaf rounds (checks the seams: each node's
   hypotheses are actually supplied by its cited parents; no circularity; quantifier
   moves survive composition). ≥ 2 consecutive clean end-to-end passes, ≥ 2 models.
3. The numerics regression matrix re-runs green (N1–N8 + gates RESUM-n3, U6, the
   verified-instance anchors n = 2 Lean / n = 3 census).
4. Completeness audit against THIS tree: every node id appears in the document or in its
   explicitly-argued pruning list. (This tree itself goes to a Codex completeness review
   as the Phase-A exit gate, per the campaign shape.)

**Standing honesty rules carried from the repo discipline:** a reduction is not a proof;
same-context self-grading is worthless; several consecutive clean passes, fresh contexts,
before "verified" is ever written; the M05 precedent is binding — a verifier endorsement
covers EXACTLY the clauses it names, nothing more.

---

## 5. Numerics index (standing corroboration — flags, never substitutes)

| suite | what it tests | result |
|---|---|---|
| N1 exhaust | two-sided bracket + geometric drainage, 20/20 (n,p) incl. all wild | CONFIRMED (max per-level ratio 0.858 < 1) |
| N2 density-tie | THE root numerically: exact n = 2 sandwich (~1e-5); MC 150k/config n ≤ 5, p ≤ 5 incl. (5,5) | CONFIRMED |
| N3 cl6 | the real block packs n = 2, 3, 4 vs sealed anchors | CONFIRMED (supports O-9's frame) |
| N4 ksub | K-1 | CONFIRMED 0/240,525 (row since PROVED) |
| N5 w17ii | K-2 repaired form, 12k adversarial configs | CONFIRMED |
| N6 regp | (REG-p) gates + symbolic closures | CONFIRMED 25/25 (supports K-13/O-12) |
| N7 track-count | M01's refutation + the runCount repaired form | MIXED = confirms refutation; repaired form supported |
| N8 eq2 | O-8b's alphabet law, 199,723 alphabets / 17 fields | CONFIRMED exhaustively |
| U6 (IFK-U6-FIRST) | K-RUN no-phantom / counting tie / equal-fiber law at length-2 strata, all (n, p) ∈ {2,3}² incl. both wild corners | **SURVIVES exhaustively** (174/174 strata T = T̂, 369 chains, 0 phantoms, equal fibers EXACT, 0 unresolved mass; PARI (e,f) tie 1600/1600) |
| RESUM-n3, D4-n3, SIB, T-n3, M-n3-V2, H-n3, V-n3, STATE-probe-2 (+14 more sealed gates) | the §2.2 layer's per-note censuses | ALL PASSING (gate names on the T-nodes) |

Matrix summary (adjudications ledger, 2026-07-31): no Fable-vs-Codex-vs-numerics conflict
anywhere; every refutation triangulated; every surviving conjecture numerically supported.

---

## 6. Change discipline

This file is the Phase-A ground truth for the math campaign. Update rules: a leaf moves
status ONLY with the evidence named (pass records for VERIFIED; file paths for
PROVED-UNVERIFIED); new leaves discovered mid-campaign are APPENDED with a dated note,
never silently merged; the §3 dependency order is re-derived when O-1/O-2/O-3 land.
Companion live records: `lean/notes/REMAINING_CENSUS_2026-08-01.md` (Lean-side),
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` (adjudications),
`lean/notes/IFK_BLUEPRINT_2026-07-31.md` (+ its revision, in flight).

— Phase A unit, 2026-07-31/2026-08-01. Next: Codex completeness review of THIS document,
then Phase B dispatch per §3.

---

## DELTA 1 (V6 fold-in) — append-only, dated 2026-07-31 late

*(The Codex completeness review V6 (`lean/notes/openmath/V6_tree_review.jsonl`, verdict
**GAPS-FOUND**, 26 numbered findings: 24 BLOCKER + 2 ADVISORY) is folded in here per the
§6 change discipline. Everything above this line is byte-untouched; where a finding
corrects text above, the correction is recorded HERE and the corrected reading governs.
Sources: the full V6 text; the two wave-1 attempts `lean/notes/openmath/
O12_phaseB_attempt.md` + `O13_phaseB_attempt.md`, whose honest-scope declarations answer
several findings BY SCOPING (exact scopes cited); the V5 IFK re-review disposition
(`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` §"IFK RE-REVIEW: REJECT-2 (V5)"), whose
three architectural defects become tree nodes here. New node ids are **D-1..D-16**
("delta nodes"; the N-* prefix is already taken by the numerics suites in §5).
The §4 acceptance criterion is UNCHANGED — see §D1.7.)*

### D1.1 Per-finding disposition table (all 26 V6 findings; no silent drops)

Vocabulary: **ACC** = ACCEPTED-with-fix (fix named); **SCOPE** = ANSWERED-BY-SCOPING (an
attempt's honest-scope section already carries the answer; citation given); **REB** =
REBUTTED-with-argument. No finding is rebutted outright; two are answered by scoping
plus a residue node — the residue is what survives of the objection.

| # | V6 finding (compressed) | disposition |
|---|---|---|
| 1 | Haar/counting limit bridge is not a node | **ACC** → new node **D-1** (MEAS-BRIDGE) |
| 2 | semantic partition + Σ_σ R_σ = 1 in ℚ(t) never assembled | **ACC** → new node **D-2** (SUM-ONE) |
| 3 | unramified-base claim lacks a semantic transfer package | **ACC** → new node **D-3** (UNRAM-TRANSFER); O-8b re-typed as its alphabet SLICE, not its carrier |
| 4 | recursion base cases (degree 1/0) absent | **ACC** → new node **D-4** (BASE-CASES) |
| 5 | canonical-object well-posedness is not a node | **ACC** → new node **D-5** (WELLPOSED), absorbing V5 defect (1) (K-DICT carrier/equality design) |
| 6 | pole-free specialization underspecified (denominators beyond det(I−K)) | **ACC + SCOPE** → new node **D-6** (DENOM-ALL); the O-12 attempt §§5–8 (Theorem 4 + Lemma RR + numerics items B–D) PROVES the all-denominator clause at 𝔅_n; residue = the instance pin, node D-11 |
| 7 | (U-DENS) ⇔ (U-GEN) is false as written | **ACC** → root amendment §D1.5(a): downgraded to U-GEN ⇒ U-DENS; U-GEN is the operative root claim |
| 8 | LIT-1's LITERATURE grade premature (pagination caveat + O-2 conditionality) | **ACC** → §D1.5(b): LIT-1 = LITERATURE-CONDITIONAL until printed-TAMS confirmation; engine-side applicability conditional on O-2, stated on-node |
| 9 | LIT-3 claims more readiness than evidence | **ACC** → §D1.5(c): demoted to LITERATURE-CANDIDATE (numbers to confirm; the irreducibility/unramified-conclusion scope pairing owed at transcription) |
| 10 | LIT-8 is an unaudited bundle | **ACC** → §D1.5(d): split into LIT-8a..LIT-8e, each LITERATURE-CANDIDATE with per-use-site transcription |
| 11 | T-1's verified scope exceeds evidence ("each OM read" is semantic) | **ACC** → §D1.5(e): T-1 re-scoped to the SYMBOLIC engine; the semantic clause routes through O-2/O-3 |
| 12 | T-8's nonzero-pivot wording conflicts with O-12/K-13 | **ACC** → §D1.5(f): T-8 re-scoped to formal-ℚ(q) solve + (REG-p)-conditional specialization; the unrestricted claim = K-13 + O-12 |
| 13 | K-12 lacks the VERIFIED-LEAN faithfulness audit record (ADVISORY) | **ACC** → §D1.5(g): audit duty added (undec/hExhaustP vs the mathematical classifier + Haar mass); grade held pending the record |
| 14 | O-1/O-3 circular quantifier seam (realized-site restriction) | **ACC** → new node **D-14** (LAWFUL-SITE READ), the noncircular quantifier form; δ-tier one-directionality (O-1δ ← O-2+O-3, never →) recorded |
| 15 | O-2 and O-3 mutually dependent in substance | **ACC** → the §D1.3 decomposition (O-2a upstream / O-2b joined to O-3) |
| 16 | O-5's inputs don't yield the leaf/factor bijection | **ACC** → the bijection triple **D-7a/D-7b/D-7c** (disjointness / semantic coverage / multiplicity compatibility) |
| 17 | O-10 stronger than its reduction (no N-restriction) | **ACC** → node **D-8**: O-10 restated with the N ≥ thr(c)+2ρ(c) guard; small-N residue D-8r; consumer audit added |
| 18 | O-11 lacks dependencies; T-7 self-dependency; K2 ≠ K-13 | **ACC** → node **D-9**: corrected dependency set; T-7 SPLIT (T-7s symbolic vs [1v]-FULL re-owned by O-11); K2-SEM input node D-9k |
| 19 | O-12 not near-independent (semantic-mass circularity risk) | **ACC + SCOPE** → node **D-11** (MASS-ID) gates the INSTANCE-PIN half; per the O-12 attempt's §8 honesty ledger its theorems consume table STRUCTURE only, never value correctness — the circularity is scoped OUT, not incurred |
| 20 | O-13's stated reduction invalid (unbounded recentering; K-3 caterpillar) | **ACC + SCOPE** → node **D-12** (SKEL-COMPRESS): the O-13 attempt itself SUPPLIES the demanded compressed-skeleton definition + compression theorem (Lemma T run-collapse + Theorem 3 Sk(n)); the tree's §3 item-14 charge was indeed the wrong mechanism (the attempt's §4 "role display" says so explicitly) |
| 21 | O-14 is not a single settled proposition | **ACC** → node **D-10**: split into O-14a / O-14a′ / O-14b / O-14c (+ O-14d as engineering duty) |
| 22 | O-14a′ (RunRealizerExists residue) must precede O-3 | **ACC** → attack order re-cut, §D1.6 slot 1 |
| 23 | O-2-before-O-3 doesn't decompose their cycle | **ACC** → §D1.3 (K-DICT's invariant/order-placement half split from its trace-correspondence half; the latter into O-3's cluster) |
| 24 | O-11 scheduled too early | **ACC** → §D1.6: O-11 re-slotted after O-5, O-8b/O-9, O-10(guarded), D-11 |
| 25 | O-12/O-13 not justified early wins | **ACC + SCOPE** → wave 1 ran them at honestly REDUCED scopes that answer the gating objections (rows 19/20); statuses = PROVED-UNVERIFIED at those scopes (§D1.5(h,i)) with the residues as separate nodes (D-11; D-12r) |
| 26 | drainage routes conflated: O-4 vs O-6/O-7/O-8a (ADVISORY) | **ACC** → §D1.4 fork adjudication: O-4 qualitative is MANDATORY for the root; O-6/O-7/O-8a + T-9's charging table = the ALTERNATIVE quantitative route |

### D1.2 New nodes (D-1..D-16; statuses per the §0 vocabulary)

* **D-1 (MEAS-BRIDGE — the Haar/counting limit bridge; V6 finding 1).** Statement, with
  quantifiers: for every n, σ, p: (i) the locus L_σ = {f monic separable of type σ} is
  Borel in ℤ_p^n; (ii) every level-N residue class is a measurable cylinder of Haar mass
  p^{−nN}; (iii) the decided-σ cylinder unions are nested increasing in N; (iv)
  ∪_N decided_σ(N) = L_σ up to a Haar-null set; (v) continuity from below then gives
  lim_N decided_σ(N)/p^{nN} = α(n, σ; p). Fragments on file: T-6's (ns-null), O-4
  Lemma A (the cylinder mass identity), K-12 at n = 2. Status: OPEN (assembly-grade;
  no new mechanism expected, but the complete bridge with quantifiers is owed as ONE
  proposition). Consumed by: T-U's squeeze, the root.
* **D-2 (SUM-ONE — semantic partition + the rational identity; V6 finding 2).**
  Statement: (i) every monic separable degree-n f over ℚ_p has EXACTLY ONE degree-n
  splitting type (unique factorization + defectlessness, LIT-2); (ii) the nonseparable
  locus is Haar-null (= T-6 (ns-null), already VERIFIED-DUAL); (iii) hence
  Σ_σ α(n,σ;p) = 1 at every p, so Σ_σ R_σ(p) = 1 at the (REG-p) primes — infinitely
  many; (iv) a rational function with infinitely many roots is zero, so Σ_σ R_σ = 1 in
  ℚ(t). Status: OPEN (assembly of proved parts; (i) is the only new text). Consumed by:
  the root's Σ_σ R_σ = 1 clause.
* **D-3 (UNRAM-TRANSFER — the unramified-base semantic package; V6 finding 3).**
  Statement: over K_δ = W(F_{p^δ})[1/p] (every δ ≥ 1), the unramified restatements AND
  proofs of: K-DICT (O-2), K-RUN (O-3), K-HALT/ASSEMBLY (O-5), drainage (O-4), Haar
  normalization (level-N mass q^{−nN}, q = p^δ), and sibling independence (O-10) — so
  that the root's "same R_σ read at q = p^δ" clause has a proof, not a census formula.
  Partials: O-8b's (R1)–(R4) is exactly the carry-algebra/alphabet SLICE of this node
  (M14's conditional proof + N8 exhaustive numerics); O-9 is already stated over any
  complete DVR; LIT-4's audited scope is "K = ℚ_p exactly", so its consumption at K_δ
  must be re-derived or re-scoped here. Status: OPEN. Route note: the cheapest discharge
  is to prove O-1..O-5 over an arbitrary absolutely-unramified complete DVR from the
  start (the O-9/M08 discipline); adjudicate at O-1 dispatch — if adopted, D-3 collapses
  into per-leaf scope hygiene plus the O-8b slice.
* **D-4 (BASE-CASES — recursion floor; V6 finding 4).** Statement: the degree-1 density
  (a monic linear polynomial has type {(1,1)}, density 1, decided at N = 0); terminal
  classifier behavior at degree-1/saturated leaves; the empty-product/degree-0
  conventions of the branch convolution (empty child set ⇒ convolution unit). Status:
  OPEN (expected one page; nothing on file states it). Consumed by: B-7/T-8's solve,
  T-6's recursion, D-1.
* **D-5 (WELLPOSED — canonical-object well-posedness; V6 finding 5 + V5 defect (1)).**
  Statement: the quantified engine objects — T_can(f), realized sites, ns-free carriers,
  resolution levels, fresh frames, letters, skeletons, certification predicates — are
  well-defined, canonical (invariant under lift and recentering-representative
  presentation choices), and compatible across truncation levels N → N+1. Incorporates
  the V5 architectural defect: a coherent CARRIER + EQUALITY design for the dictionary
  Θ's domain (what V5 called "K-DICT lacks a coherent carrier/equality design").
  Partials: the dual-accepted §B2-DEF/§M-SPECIES definitions give symbolic
  well-typedness; the SEMANTIC invariance half is new. Status: OPEN. Consumed by: O-2a,
  O-3, every leaf that quantifies over T_can(f).
* **D-6 (DENOM-ALL — every denominator of the solve is pole-free; V6 finding 6).**
  Statement: EVERY denominator introduced anywhere in the assembled solve — block det
  numerators/denominators, table-coefficient denominators, height resummations,
  normalizations, the final R_σ — is of cyclotomic type (a unit in
  ℛ = ℚ[q, 1/q, 1/(q^c−1)]), hence nonvanishing at every prime power ≥ 2. Status:
  **PROVED-UNVERIFIED at the 𝔅_n scope** — the O-12 attempt's Theorems 1 + 4 and
  Lemma RR prove exactly this (its numerics items B–D check the FULL pipeline n = 2..5
  including all R_σ reduced denominators); the extension to the eventual general-n pack
  is gated by D-11, per the attempt's own scope declaration (§1 + §8). V7 hostile
  verification in flight.
* **D-7a/b/c (the O-5 bijection triple; V6 finding 16).** The ASSEMBLY clause of O-5,
  split into the three propositions its listed inputs do NOT supply:
  **D-7a (LEAF-DISJOINT)** distinct leaves of the halted realized run determine
  DISTINCT (pairwise coprime) irreducible factors; **D-7b (LEAF-COVER)** every monic
  irreducible factor of every lift g of the decided class is hit by some leaf — the
  degree-checksum "no orphan factors" argument made an actual proof; **D-7c
  (LEAF-MULT)** multiplicity compatibility: the leaf multiset's (e, f) data equals the
  factors-with-multiplicity of g, uniformly over ALL lifts g. All three OPEN; they ride
  O-2/O-3 + GMN eq. (37)/defectlessness but are separate obligations (V6: the product
  formula + checksums + "histories are chains" do not alone yield a bijection).
* **D-8 (O-10 restated with the N-threshold; V6 finding 17).** O-10's statement is
  RESTATED with the guard its reduction actually reaches: sibling independence in exact
  count form for N ≥ thr(c) + 2ρ(c) (K-COUNT's constant-fiber range). **D-8r (small-N
  residue)**: behavior below the threshold — expected resolution is an N-guard adopted
  by every consumer; **the consumer audit** (T-6's (SIB-STEP), O-11's K1 need only the
  guarded form) is part of D-8. Status: OPEN (statement fix + audit; K-COUNT unchanged).
* **D-9 (O-11's true dependency set + the T-7 self-dependency resolution; V6 findings
  18/24).** O-11's input set is CORRECTED to: O-10 (guarded, D-8) + O-5 (+D-7 triple,
  for correct semantic leaf labels) + O-8b/O-9 (correct transition weights) + the
  semantic mass bridge (D-1/D-11, the K4 face) + **T-7s**. The T-7 SPLIT resolving the
  self-dependency: **T-7s** = the symbolic tables + obligations ledger (VERIFIED-DUAL,
  stands as is); the **[1v]-FULL value-correctness event is RE-OWNED by O-11 as goal
  content** — K3 is struck from O-11's input list (T-7 routed its open value content to
  O-11, so T-7 was never a lawful unconditional predecessor). **D-9k (K2-SEM)**: the
  semantic escape property (positive termination/escape mass from every state at the
  intended instance) is a SEPARATE input — K-13's finiteness theorem does NOT supply it;
  at 𝔅_n it is the O-12 attempt's Theorem 1 + Corollary D (PROVED-UNVERIFIED, margins
  ≥ 3/4, 7/8, 6/7); at the eventual pack it rides D-11. Status: dependency corrections
  recorded; O-11 remains OPEN.
* **D-10 (the O-14 split; V6 finding 21).** O-14 is dissolved into its ≥ 4 distinct
  propositions, each with its own status: **O-14a** the GUARDED vertex-transport law at
  ν_{i+1}.e = 1 (HK-11a landed; the ≥ 2 disposition = sign-off item 28; suspected-false
  unguarded form REFUTED-AS-STATED by HK52_stretchGate); **O-14a′** RunRealizerExists —
  the upstream stage-tower supply: interior half PROVED
  (`interior_center_realizer_exists`, Lean-core), OPEN residue = the (S6b′)
  monomial-shape clause at deg Φ > 1 + the last-node landing flank (countermodel search
  LIVE); **O-14b** the cl19 repaired carrier ladder (OPEN); **O-14c** hStateNe
  derivability (OPEN, expected derivable); **O-14d** instance population — an
  ENGINEERING duty, tracked outside the math tree. "All leaves proved" now means:
  O-14a/a′/b/c each closed; O-14d excluded from the criterion.
* **D-11 (MASS-ID — semantic mass identification / the instance pin; V6 finding 19).**
  Statement: the eventual general-n pack's kernel entries are the Haar volumes of the
  T-3/T-6 continuation events at the intended instance, the events per row pairwise
  disjoint with positive per-state termination margin, and the pack's block system IS
  𝔅_n — or an organization covered by the O-12 attempt's robustness criterion
  (Theorem 3 + the contingent OL-O12-1). This node gates the INSTANCE-PIN half of O-12
  (the attempt's §1 scope declaration assigns it to O-2/T-7/O-14d territory — exactly
  this node) and D-9k at the pack. Status: OPEN. Inputs: O-2, T-7s, O-14d, T-3/T-6.
* **D-12 (SKEL-COMPRESS — the compressed-skeleton definition + compression theorem;
  V6 finding 20).** Statement (as supplied by the O-13 attempt §3): run-collapse is
  well-defined (within a run every node has exactly one child, so collapsing a maximal
  run has no attachment ambiguity); every realized T_can(f) — infinite branches
  included — loop-collapses to a FINITE tree (Lemma T: ≤ 6n² letter blocks per branch);
  and the collapsed shapes form the finite p-free set Sk(n) (Theorem 3,
  |Sk(n)| ≤ (n+2)^{7n³(n²+3n+16)}). This is exactly the object V6 said was missing —
  the attempt survives the K-3 caterpillar because arbitrarily long recentering runs
  collapse to one node with depth PARAMETER in ℕ∪{∞}, never new shapes. Status:
  **PROVED-UNVERIFIED** (V8 hostile verification in flight). **D-12r (completeness
  residue)**: Theorem 4 (realized trees spell inside Sk(n)) is conditional on T-4
  SP-COMP's D4R.0-K(c) verdict-pin residual (owner [3t] VP) — a SEPARATE node, not
  discharged by D-12.
* **D-13 (the O-2 split; V6 findings 15/23).** **O-2a** = clauses (i)–(iv) of O-2
  (invariant matching, injective order placement, normalization crossing,
  admissibility) + the D-5 carrier/equality design — UPSTREAM: provable against the GMN
  text without realization semantics. **O-2b** = clauses (v)–(vi) (K-DICT-OB1 trace/
  tree correspondence + K-DICT-OB2 σ-invariance) — moved INTO the O-3 cluster (§D1.3);
  these are the halves that quantify over "the trees the classifier produces", i.e.
  over O-3's subject matter. Status: split recorded; both halves OPEN.
* **D-14 (LAWFUL-SITE READ — the noncircular locality quantifier; V6 finding 14).**
  Statement: for every menu-LAWFUL site (H, ν) (lawful at the frame state — NOT
  presupposed realized on the run), whether the canonical run on f reads (H, ν) is
  determined by f's digits below L(H, ν). This strengthening of O-1's realized-site
  two-lift form is what O-3's (no-missing) direction actually needs (an
  instance-restricted locality theorem cannot establish no-missing realization). O-1's
  stated form stands as the realized-site tier; D-14 is the obligation that breaks the
  O-1/O-3 seam. Status: OPEN.
* **D-15 (CYL — the cylinder law as its own node; V5 defect (2)).** Statement: decided
  verdict classes are EXACT finite unions of level-N cylinders with the per-tree fiber
  scaling law (count_tie's L1/CYL). V5's finding: CYL is NOT implied by the faces O-1
  listed — it additionally needs D-14 + (K2) window closure + T-6's (τ-irr)
  perimeter-conditional discharged. Previously implicit inside O-1/K-4; now a node.
  Status: OPEN. Consumed by: K-4's repair, D-1(ii), T-U's bracket.
* **D-16 (READ-δ TRANSPORT — execution transport for the δ-tier; V5 defect (3)).**
  Statement: f ≡ g mod p^{δ+1} (δ = v_p(disc f)) ⇒ the canonical RUNS on f and g
  correspond site-for-site — not merely their OM factorizations (which is all LIT-5's
  published Theorem 3.13 gives). This is the "execution transport" V5 found missing
  from K-READ-δ; it consumes O-2b + O-3 and is the true carrier of O-1's δ-tier and
  O-4's OL2 rates. Status: OPEN (optional for the root — rates only; see §D1.4).

### D1.3 The O-2/O-3 cycle, decomposed (V6 findings 15/23)

The cycle V6 found: O-3's no-phantom needs engine-reads → OM-types (= O-2); O-2's
tree-correspondence clause quantifies over the classifier's produced trees (= O-3's
subject). Resolution — three pieces, acyclic:
1. **O-2a** (invariant/order-placement half + D-5 carrier design): upstream, no
   realization semantics consumed. Dispatches FIRST.
2. **O-3 ⊕ O-2b** (realization faithfulness + trace/tree correspondence + σ-invariance):
   ONE joint cluster, proved together by mutual induction on resolution level (the
   induction hypothesis at level N supplies each half what it needs of the other at
   level < N — the standard resolution of a mutual dependency, made explicit instead of
   ordered away). The U6 falsifier extension (length 3) rides this cluster.
3. **D-16** (δ-tier execution transport): AFTER the cluster; consumes both halves.
Ordering O-2 wholesale before O-3 (the pre-delta §3 order) is hereby retired.

### D1.4 The drainage-route fork, adjudicated (V6 finding 26)

From the §2.2 assembly paragraph: T-U's squeeze needs, at each prime, the two-sided
bracket at every finite N (counting/cylinder structure: T-6 + D-15 + D-1) and
undec(N) → 0 — a QUALITATIVE input. Adjudication:
* **MANDATORY for the root: O-4** (qualitative drainage). Its M05/V2-verified core
  already proves SEMANTIC drainage at every prime (Lemma D Krasner constant 2v+1 +
  Lemma C tail bound); the open residue is OL1-ii (the O-1+O-3 agreement seam), NOT any
  rate. Neither O-6 nor O-7 nor O-8a appears in this route.
* **ALTERNATIVE (quantitative) route: T-9's index/charging table + O-6 + O-7 + O-8a.**
  Needed only if (a) Phase C elects to route drainage through T-9's envelope instead of
  the M05 route, or (b) effective verification levels / explicit rates are wanted
  (OL2, via D-16). These leaves are struck from the root-mandatory set.
* Consequence recorded: the pre-delta §3 "every leaf is needed" reading is corrected —
  the mandatory set is the §D1.6 critical path + its named dependencies; O-6/O-7/O-8a
  are route-R-QNT assets (and remain live obligations for T-9's own honest kernels).

### D1.5 Status updates (append-only corrections to §§1–2.4)

* (a) **Root**: the "(U-DENS) ⇔ (U-GEN)" sentence is downgraded (V6 finding 7): U-GEN ⇒
  U-DENS holds (given D-1); the converse is NOT claimed and not needed — the operative
  root claim is U-GEN, whose clause (iii) carries the finite-solve provenance.
* (b) **LIT-1**: LITERATURE-CONDITIONAL (printed-TAMS pagination confirmation owed;
  engine-side applicability conditional on O-2).
* (c) **LIT-3**: LITERATURE-CANDIDATE (citation numbers + exact-scope pairing owed).
* (d) **LIT-8**: split into LIT-8a (Krasner + the 2v+1 polish constant), LIT-8b
  (Newton–Hensel), LIT-8c (Vandermonde/resultant identities), LIT-8d (Igusa §7.4 change
  of variables), LIT-8e (Gauss/Möbius counts) — each LITERATURE-CANDIDATE, transcribed
  at its declaration site per §4 rule 5.
* (e) **T-1**: VERIFIED-DUAL **as a theorem about the symbolic carry-algebra engine**;
  the semantic "each OM read" scope is conditional on O-2/O-3 (V6 finding 11).
* (f) **T-8**: VERIFIED-DUAL for the formal ℚ(q) solve + (REG-p)-conditional
  specialization; unrestricted per-prime wording routes through K-13 + O-12.
* (g) **K-12**: faithfulness-audit duty recorded (Lean `undec`/`hExhaustP` vs the
  mathematical classifier + Haar mass); VERIFIED-LEAN grade held pending the record.
* (h) **O-12** = **PROVED-UNVERIFIED at the O-12 attempt's honest scope**: at 𝔅_n (the
  §1-defined intended instance), all three on-record kernel organizations, every block
  determinant and assembled denominator cyclotomic-type, failing set EMPTY at every
  prime power ≥ 2 (falsifier: 18,120 prime powers, 0 findings). Hostile Codex
  verification **V7 in flight**. Residues as SEPARATE nodes: D-11 (instance pin) +
  contingent OL-O12-1 (fires only if a future pack departs from 𝔅_n's organizations).
* (i) **O-13** = **PROVED-UNVERIFIED at the O-13 attempt's honest scope**: Sk(n) finite
  and p-free by typing at every n (Theorems 1–3 + Lemmas B/L/T, unconditional over the
  dual-accepted vocabulary-as-definitions; falsifier reproduces the sealed |𝒮₃| = 53).
  Hostile Codex verification **V8 in flight**. Residue as a SEPARATE node: D-12r (the
  completeness clause rides the D4R.0-K(c) verdict pin). Note on file: the Serre bound
  is VALUE-side only (the attempt's §4 role display) — the tree's expected reduction is
  corrected accordingly.

### D1.6 THE NEW CRITICAL PATH + re-cut attack order (honoring V6 findings 22–25)

**Critical path (mandatory for the root):**
O-14a′ (upstream realizer residue) → O-1(thr-tier) + D-14 + D-15 → O-2a (+D-5) →
[O-3 ⊕ O-2b joint cluster] → O-5 + D-7a/b/c → O-4 (qualitative drainage, OL1-ii from
O-1/O-3) → D-1 + D-2 + D-4 (assembly floor) → O-9 + O-10(D-8-guarded) → D-3
(unramified package, O-8b as its slice) → D-11 (mass-id) → O-11 (D-9 dependency set) →
root — with O-12 (via D-6/D-11) and O-13 (via D-12) verifying in parallel (V7/V8).

**Attack order:**
1. **O-14a′** — BEFORE O-3 (V6 finding 22): close or remove the (S6b′) + landing-flank
   residue; the LIVE countermodel search is its falsifier.
2. **O-1 thr-tier + D-14 + D-15** — the per-site read with the lawful-site quantifier
   and the CYL law; δ-tier DEFERRED behind the O-3 cluster + D-16.
3. **O-2a + D-5** — carrier/equality design first (V5 defect 1), then invariants/order
   placement/admissibility against the GMN text.
4. **The O-3 ⊕ O-2b joint cluster** — mutual induction on resolution level; K-OB-A/B/C/E
   + K-DICT-OB1/OB2 + K-RUN clause 4 priced inside; U6 falsifier extended to length 3.
5. **O-5 + D-7a/b/c** — halt soundness, then the bijection triple.
6. **O-4** (mandatory route, §D1.4) **+ D-4** alongside.
7. **D-1 + D-2** — the measure bridge and the partition/identity assembly.
8. **O-9; O-10 at the D-8 guarded statement** (+ the consumer audit).
9. **D-3** (unramified transfer; adjudicate the arbitrary-DVR route first).
10. **D-11, then O-11** at the D-9 corrected dependency set (V6 finding 24 honored).
11. Residues + options: D-12r; O-14a/b/c; D-16 + O-6/O-7/O-8a (route R-QNT) only if
    quantitative rates are elected.

### D1.7 Acceptance criterion

**UNCHANGED.** §4 applies verbatim to every D-* node and to the re-scoped statuses
above; V7/V8 count toward (not past) the ≥ 2 consecutive clean model-diverse passes;
PROVED-UNVERIFIED is still never consumed by an acceptance claim.

— DELTA 1 complete, 2026-07-31 late. Original tree above byte-untouched.

---

## DELTA 2 (SYNTH4 + O3-REPLACE fold) — append-only, dated 2026-08-01

*(Folds in the two cross-validating adjudicated units: **SYNTH4**
(`lean/notes/SYNTHESIS_PASS4_2026-08-01.md`, commit 29dd2fa — the GD merge, the recut
mandatory path, the Lean units) and **O3adj** (`lean/notes/openmath/O3adj_adjudication.md`,
commit 57b4da4 — the two-REJECT adjudication of the O-3 ⊕ O-2b joint-induction design,
verdict REPLACE, the K-RUN-C composition). Both ACCEPTED by the orchestrator: ledger
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` §"SYNTHESIS 4 + O3 REPLACE ADJUDICATED
(2026-08-01)", commit dbccbc1. Everything above this line — DELTA 1 included — is
byte-untouched; where this delta corrects text above, the correction is recorded HERE and
the corrected reading governs. The §4 acceptance criterion is UNCHANGED and applies
verbatim to every GD-*/CU-* node (§D1.7 discipline). No Lean file is touched by this
delta.)*

### D2.1 The five SYNTH4 lines (proposed at SYNTH4 §5; adjudicated, now governing)

1. **O-3 clause 3 (nonempty locus) re-keyed:** "every fresh-frame-lawful assignment
   chain" → "every coherent chain (HistoryCoherent)"; **LC-COH** is displayed as a named
   open note CONSUMED BY NOTHING. [Executes V21 finding 3's recorded-but-unexecuted tree
   delta; the design's §R2 disposition was judged internally coherent by V21 itself.]
2. **O-2b evicted from the critical path:** the OB1 half (K-DICT-OB1 trace/tree
   correspondence, TT-DET′, MF-MATCH, the V21-4 congruence/well-definedness obligations)
   moves to route R-QNT as D-16's package, per O3design's own §4 consumer table +
   §D1.4's striking of D-16/rates. **OB2 (σ-invariance) stays root-side for now**
   (composition unit CU-6), CONDITIONAL on the owed D-11 audit (§D2.7). **LIT-5 (BNS):
   re-marked LITERATURE-CANDIDATE, route-R-QNT-ONLY** (see D2.4).
3. **D-15 (CYL): merged into the recut cluster's deliverables** — its content is the
   lift-uniformity corollary of the composition (CU-1/CU-2 per-f faithfulness + O-1thr
   Theorem 3's cylinder exactness + D-14 + TB-CAP); K-4's repair pointer follows.
   Adjudicated routing (O3adj §3.2): D-15 KEEPS its node identity and owns ALL box-level
   lift quantification — the composition states NO box-keyed universal theorem, which is
   what dissolves the V21-1/2 quantifier class permanently.
4. **K-OB-C (Okutsu proximity) struck from the mandatory set** (O-7/route-R-QNT only);
   the no-phantom warrant on the mandatory path is the GD dictionary (F5 + OL-2a-2(c,d)/3
   per O3design's intra-step order), and O5triple §7 remark 6 bypasses the Krasner route
   for D-7a. The citation is pulled only if the rates route is elected.
5. **New named nodes GD-1..GD-8** (§D2.2 below) with the statement-level consumption
   mappings as the cross-index; the O-1thr/O-2a/O-3-cluster/O-5/O-9 residues are
   RE-POINTED at them — a GD family proved retires its instances in every carrier
   package at once (after the family's own transcription-audit clause).

### D2.2 The GD-1..GD-8 merged open-lemma families (new named nodes; SYNTH4 §1)

**The merge finding:** the ~22 named open items across the seven active Phase-B packages
are EIGHT lemma families; the GMN-dictionary/engine-read seam (GD-2/GD-3) is ONE subject
stated in FIVE vocabularies. "↔ labels" below quote each package's exact item names.
A partial proved in one vocabulary transports to the family's other carriers ONLY after
the (S-1)-style machine transcription audit (O-1thr §8) — the audit is part of closure.
All GD families are **OPEN** (they merge open items); proved partials are named per row.

| id | merged subject | carriers (exact labels) | proved partials on file |
|---|---|---|---|
| **GD-1** | representative shape / pinned-lift admissibility: Φ_{i+1} = Lift_i(c) monic of degree m_i·e_i·f_i, a GMN Def-2.12 representative (one-sided N_j, R_j ∼ ψ_j, top mult 1), V-recursion V_{i+1} = e_i f_i(e_i V_i + h_i); graded corollary on in(Φ_{i+1}) | O-2a **OL-1 (a)(b)(c)** = the statement; O5triple **(R-1)** = clause (b) at the constructed representative (V23: substantive, not a lookup); O-1thr **(V2)(a)** = the graded corollary; O3design **JC-1** | GMN Thm 2.11 (SOME representative); O-1thr **Lemma KEY1** proves the graded corollary outright at degree-1 first transitions |
| **GD-2** | frame/valuation tie + development identity (the seam's spine): u_{i+1} = v_{i+1} on low-degree nonzero B, w multiplicative (MacLane); w_{i+1}(B) = min_k (w_{i+1}(C_k) + k·γ̂_i); window polygon = N_{i+1}(f) vertex-for-vertex; emitted record (e,h,ℓ,s,u) verbatim (c1) | O-2a **OL-2 (a)+(b)** ⇒ **OL-2-min [(c′)+(d′)]**; O-1thr **(V1)** + **(V2)(b)** verbatim + **Corollary VTX**'s general-order residue; O3design **JC-2** (+ the (M6b) locality corollary); O5triple **(I-1)(a)** side-data leg | **Lemmas VAL1 + DIV1** outright at degree-1 first transitions; **WGEO(a)–(d)** at every order from (V1)/(V2); T-F machine check 41,720 instances 0 violations (7,472 violations of the UNsheared reading — the convention pin is load-bearing); HK52 stretch countermodel = the standing clause-(c) trap |
| **GD-3** | residual dictionary / twisted residues. MIN CORE: ord_{ψ̂_hom}(in(f)) = ord_ψ(R_λ(f)). FULL FORM: R^nrm = c·R_λ(f), c ∈ F^×, slot-wise residue-field bijections (no un-cancelled z ↦ z^a, a ≥ 2). Consumption split: the cluster needs the MIN CORE only (V25's minimality gap, executed at O-2a rev 5's OL-3-min trim); the value side (O-9 census → O-11 tables) needs the FULL form | O-2a **OL-3** (full) / **OL-3-min** (core); O-1thr **(V2)(c)** = the min core VERBATIM; O-9 **OL-B** = the slot-wise clause ("one proof should serve both" — O-2a's own text); O3design **JC-3**; O5triple **(I-1)(a)** residual leg | KEY1's ord computation (degree-1 first transitions); M08 Theorem 2 = level-1 census PROVED (46-strata machine check); B-4/M6 empirical through OM order 4 |
| **GD-4** | emission/record discipline (engine bookkeeping, not GMN mathematics): W1–W5 well-formed dressed histories, domains, level-0 (c0), AUX-at-harvest + lower (N4) band | O-2a **OL-4**; O-1thr **(M6b)(iii)** + **(M6b)(ii−)**; O3design **JC-4** (OL-2a-4 + K-OB-E) | proof-by-construction routes on record in both briefs; K-OB-E (GMN Def 3.9 arithmetic) is the one semantic clause |
| **GD-5** | base-read conformance at order 1 — **NEARLY CLOSED BY COMPOSITION**: O-2a OL-5 (b′)+(c′) = the composition of O-1thr's PROVED (V1)/(V2)-at-order-1 layer (VAL1/KEY1/DIV1 + ROOT-M + WGEO) with O-2a's PROVED (D3). Residue: ONE transcription audit (S-1 seam, O-1thr machine ↔ O-2a stage interface F.0–F.2 at order 1) + the degree-g > 1 root-key KEY1 generalization (small, same method) | O-2a **OL-5 (b′)+(c′)**; O-1thr rev 3 §§ VAL1/KEY1/DIV1/ROOT-M/WGEO; O-2a **(D3)** (proved) | the entire content except the S-1 audit; SYNTH4's proposal: a one-page composition note closes it, no new mathematics expected |
| **GD-6** | run decomposition / execution ≡ realization: (a) run = successive stage reads with chain parameter Θ(𝐇_{≤i}) (= O-2a **OL-6**, V25 no-critical); (b) machine execution ≡ REALIZED (= O-1thr **Lemma REAL≡**); (c) O3design's F1′ level-accounting clause | O-2a **OL-6**; O-1thr **REAL≡**; O3design **F1′** conformance warrant | (b)'s V24 circularity (the non-halted guard) REPAIRED at O-1thr rev 4 (commit 5613274: (M6c) requantified, non-ns-halt now a CONCLUSION); repair verification pending — pin STANDS per ledger |
| **GD-7** | flow coherence / process matching / adequacy: (a) sprouted-type dissection factor G_{S,ψ} = f_{t′} with ω_{r+1} = a(S,ψ); (b) flow-sprouted types lie in t_r(f) so Thm 4.18/Cor 4.19 apply; (c) order-0 anchor f_{t₀} = g_j (product-closure half substantive, per V23 gap 2 — in the lemma, not the lookup); (d) ADEQ read-back surjectivity, conditional on GD-1 | O5triple **(GMN-COH)** [M], **(R-3)** [M], **(R-0)** [S/M split at rev 3]; O3design **(ADEQ)** leg (ii); **MF-MATCH** = the D-16-only sibling, NOT mandatory (kept for provenance); O-4 V2-item-4 caveat consumed at OL1-i | one GMN reading session covers (a)–(c) + the (R-1) lookup + L5b pin + printed-TAMS pagination — the whole literature-facing surface of GD-1/GD-7/GD-8 |
| **GD-8** | exact-key polygon seam: at ord_{φ_r}(g) = j₀ ≥ 1 the φ_r-development has the slope-−∞ side of length j₀ contributing the EXACT factor φ_r^{j₀}, finite sides carrying ω − j₀, with degree bookkeeping | O5triple **(R-2)** [M] (NODE(ii), Thm A(3)); O-2a order-1 **(L3+)** | the order-1 proof (falsifier-covered: 871 forced exact-divisibility samples, 0 findings); expected to generalize verbatim over GD-2's frame tie |

**The non-merging remainder (7 genuinely separate item groups, unchanged owners):**
O-10's K-COUNT + K-JAC (the hardest genuinely-new quantitative lemmas; D-8 guard +
consumer audit ride along) · O-9's OL-A/OL-C/OL-D (OL-B is GD-3) · the instance pin
(D-11 + OL-O12-2 + contingent OL-O12-1) · D-3/O-8b's (R1)–(R4) (arbitrary-DVR statement
discipline adjudicated at GD dispatch — if adopted, D-3 collapses to scope hygiene) ·
(E-N) (open, scoped, NOT consumed by the mandatory path) · the O-14 residue
(Conjecture 5.4.C, consumed by nothing mandatory) · Dfloor's (C2) conventions at
degree > 1 (owned by O5triple Theorem C). K-OB-C: struck (D2.1 line 4).

**Count: 22 named open items → 8 families + 7 independent groups**; the mandatory path
needs the 8 families minus MF-MATCH, plus O-9/O-10/instance-pin/D-3 from the remainder.

### D2.3 The K-RUN-C composition (CU-1..CU-7) — replaces the O-3 ⊕ O-2b joint cluster

**§D1.3 item 2 is RETIRED.** The "ONE joint cluster, proved together by mutual induction
on resolution level" is replaced by the K-RUN-C composition (O3adj §3, accepted at
dbccbc1). Grounds (O3adj §§1–2): V21's three heavy blockers (findings 1/2/5) are V16's
two central blockers surviving their own repairs — (P1) any box-keyed global "∀ f"
statement carries the every-lift/cylinder law intrinsically; (P2) the Cons^τ-defined
global T_can forces an un-schedulable global adequacy theorem. Both are structural to
the design's defining moves, hence REPLACE, not a third revision. The replacement's
pieces each carry their own hostile-verification record; its statements are PER-f
(selected-f); box quantification appears only where D-15 owns it (D2.1 line 3).
N\*(𝐇) = the D4R.4/L12 per-branch level with the TB-CAP verdict-window join; CEIL-UB
retained one-directional. Standing preconditions unchanged (§2.4).

* **CU-1 (NM — no-missing + interior adequacy + state binding; THE ONE NEW PROOF).**
  One ordinary induction on chain length k, two clauses: for every Cons_f chain 𝐇 with
  N\*(𝐇) ≤ N — (i) the canonical run on f at working level N realizes 𝐇; (ii) the
  engine's frame state after the realized prefix equals the stage data of Θ(𝐇) (the
  OL-6 binding — the old F5 content as a carried clause, not a face). Step = IH + OL-6 +
  OL-2a-2-min/3 + SPAN/(M6a)/(M6c)/VTX + D-14 + REAL≡ — i.e. GD-2/GD-3(min)/GD-6
  instances plus O-1thr's per-site kernel, already proved at the rev-3 perimeter (root
  states + degree-1 first transitions outright). Base = O-2a Theorem 1 + OL-5 order-1,
  statuses displayed VERBATIM (no "proved base" phrase — V21-6 accepted). Interior
  adequacy = per-site SPAN totality inside the same step; **ADEQ as a global unit is
  DELETED** (leaf surjectivity is CU-7/counting — Arg-2). Status: OPEN; primary gate =
  the promoted DEPTH-3 falsifier (order-2 states, where (V1)/(V2) are genuinely
  consumed), which must run BEFORE the CU-1 spec dispatches.
* **CU-2 (NP — no-phantom).** = O-2a Theorem 2(D) ∘ ι: every emitted record of the
  canonical run on f is the GMN datum of its chain. Consumed from O-2a rev 4/5; residue
  exactly OL-2a-1..6 = GD-1..GD-6; nothing re-derived. **CU-2t (terminal seam):** the
  old Cons^τ (t-i)/(t-ii) obligations as ONE lemma from O-2a Theorem 2(B) saturation +
  TB-CAP (τ-hen)/(τ-irr) windows; no global T_can definition rides on it. Status: OPEN
  (one lemma) over the GD residue.
* **CU-3 (NE — nonempty locus, coherent form).** = O-14a′ RunRealizerExists (ZMod p
  collapse + last-node closure) + D-14 cylinder pinning + the (O6) canonicalizations.
  Requires the O-3 clause-3 re-key — EXECUTED at D2.1 line 1.
* **CU-4 (ACC — acceptance, selected-f).** F4-S (soundness, every N) + F4-C
  (completeness at N ≥ N\*) exactly as rev 1 split them (V21 confirmed the level
  quantifiers), stated for the box's own f only; from O-1thr Theorem 3 (F1)/(F4) +
  O-2a Theorem 2(B) + TB-CAP (τ-irr) window [perimeter-conditional, displayed].
* **CU-5 (satellites).** K-OB-A = O-1thr Thm 1 per site + O-13/D-12 roster finiteness
  (corollary-grade). K-OB-B = DES-6 re-key + CU-1 (definitional + one N\* computation).
  K-OB-E = GMN Def 3.9 (near-definitional). K-OB-C = struck from mandatory (D2.1
  line 4); standalone GMN-side unit only if R-QNT elects it.
* **CU-6 (OB2 — σ-invariance, level-free).** O-2a clause (i) + the BNS §2 definitional
  transcription (Defs 1.7/3.1–3.2 pinned). Root-side PENDING the D2.7 audit: if D-11
  does not consume OB2, CU-6 and its BNS pin leave the mandatory path too.
* **CU-7 (O5triple interface discharge + re-attribution).** (I-1)(a) = CU-2 + O-1thr
  Thm 1/D-14 lift transfer below thr(T); (I-1)(b) = CU-2t + CU-4 + Lemma STEEP;
  (I-1)(c) = O-2a Theorem 2(B)/(D); (I-2) = OL-2a-2/3 faithfulness + the (N4) corner
  band. **ACTION OWED: correct the O5triple brief's (I-1) attribution line** — its
  displayed content is single-polynomial and consumes NO K-DICT-OB1; the "∘ O-2b trace
  correspondence" phrase priced a node the content never uses.
* **DEFERRED TIER (route R-QNT; not root-mandatory).** OB1 = F6′ + TT-DET′ + MF-MATCH +
  the V21-4 congruence obligations + D-16 + gates G-F6′/G-MF; rev-1's right-sized
  statements are the tier's starting spec (two review rounds banked, not discarded).
  Opens only if Phase C elects explicit rates (OL2) or the T-9 quantitative route.

**Consumer-table walk (every O-3/O-2b consumer served or explicitly deferred; O3adj
§3.2):** K-14 (I0) ← CU-1 + CU-3 · K-14 (I1) ← CU-1 + CU-2 (per f) + D-15 (box level) ·
K-14 (I3-rc) ← CU-1(ii) · O-4 OL1-ii ← CU-2 + CU-4 + GMN Cor 4.19 · O-5 + D-7a/b/c ←
CU-7 (no OB1) · O-7 (X1)/(X4) ← CU-2 + CU-5 [O-7 itself R-QNT] · D-15 ← D-14 + O-1thr
Thm 3 + CU-1/CU-2 + TB-CAP · D-16 ← DEFERRED (root-optional, §D1.4) · D-11 σ-invariance
← CU-6 · K-4/K-6 repairs ← via D-15. No box-keyed universal theorem, no global ADEQ,
no OB1 anywhere on the mandatory side; the unserved consumers are exactly route R-QNT.

**Gates (re-attributed per V21-6):** U6 length-3 (G-F1/G-F2/G-F5, selected-f);
**G-LIFT split** — per-site read comparison tests O-1thr Thm 1/D-14, full-run-set lift
comparison moves to D-15; G-F3′ (coherent-chain kill only); G-F4′; G-CEIL′ (both
directions); G-EMIT (now also OL-6's falsifier); G-OB2; G-OBC; G-F6′/G-MF → deferred
tier. **F2′-as-assembly note (SYNTH4 §2.3, verified for D-7b):** O5triple Theorem B
derives D-7b coverage from injectivity + checksums alone (NO no-missing consumed);
the drainage-side no-missing residue is exactly CU-1's induction over the PROVED
(M6a)/(M6c) layer + the GD dictionary — assembly, not fresh mathematics.

**Risk display (O3adj §4, carried):** R1 CU-1's step at deep states rides (V1)/(V2) +
REAL≡'s perimeter (depth-3 falsifier = cheap pre-test; a kill reopens the per-site
kernel, not the composition's shape) · R2 the (E-N) caveat touches CU-4 through O-1thr
Thm 3(c) (displayed OPEN) · R3 a future genuine cross-polynomial OB1 consumer would
re-open the deferred tier (re-scoping event, not silent assumption) · R4 K-14 census
granularity below leaf level is D-15 content by routing.

### D2.4 Evictions from the root-mandatory set (recorded corrections; readings govern)

* **O-2b (K-DICT-OB1 / TT-DET′ / MF-MATCH):** OFF the mandatory path → route R-QNT
  (D-16's package). Evidence: O3design §4's own consumer table gives F6′/OB1 exactly one
  consumer, D-16, which §D1.4 struck (rates only); the O3adj §3.2 walk confirms no other
  root-mandatory consumer (the O5triple (I-1) attribution was a mis-pricing — CU-7).
  §D1.3's reason for the join ("needed to consume any BNS iteration/precision bound",
  O-2 clause (v)) was a rates-only reason.
* **LIT-5 (BNS) re-marked: LITERATURE-CANDIDATE, route-R-QNT-ONLY.** Theorem 3.13 was
  already unconsumed on the mandatory path; with OB1 evicted, the BNS §2/§4
  transcription duties (with their documented arXiv-vs-journal numbering hazards) are
  R-QNT items. The ledger records the consequence: the 5th literature axiom is no
  longer needed for the root. ONE residual BNS touch-point remains root-side pending
  the D2.7 audit: CU-6/OB2's §2 definitional pin (Defs 1.7/3.1–3.2) — definitions, not
  the precision theorem.
* **K-OB-C (Okutsu proximity):** struck from the mandatory set (D2.1 line 4); only
  consumer left is O-7 (route R-QNT). O-3's §2.4/§3 charge texts naming K-OB-C for
  no-phantom are superseded by the GD-dictionary warrant.
* Already struck at §D1.4 and unchanged: D-16, O-6/O-7/O-8a (route R-QNT).

### D2.5 Status updates (evidence-cited; §D1.5 pattern)

* **Dfloor (D-1 MEAS-BRIDGE + D-2 SUM-ONE + D-4 BASE-CASES) = VERIFIED — the THIRD
  Phase-B leaf through the bar.** Pass 1 (Codex V22): CLEAN SOUND, 0 criticals (commit
  604621f). Pass 2 (fresh Fable, model-diverse, commit bdc996a): SOUND, 0 criticals,
  3 minor gaps (ID reduced-rep, ADD induction coprimality, TRANSFER sum-regularity),
  all six charged rev-2 repairs confirmed, T-F numerator independently recomputed.
  Adjudicated VERIFIED at ledger dbccbc1; the 3 minor-gap fixes ride the next doc
  touch. Residue (displayed, not discharged): the BASE-1(f) fence = classifier-side
  content, the composition cluster's business. Lean unit U-C (the Dfloor capstone
  shape) stays PARKED — sign-off class, per the ledger.
* **O-12 = VERIFIED at its honest scope — the SECOND leaf (recap).** Pass 1 (V19, no
  criticals) + pass 2 (fresh Fable, ZERO criticals; 2 gaps = one wording conjunct +
  one inert proviso, math holds) ⇒ VERIFIED: the pole-free/(REG-p)-emptiness theorem
  at the abstract solve family 𝔅_n (ledger §"WAVE 4 + PASS 2s", commit 95a46d2).
  Wording conjunct rides the next touch. Residues as separate nodes, unchanged:
  OL-O12-2 (complete degree-3 table = an (O3) member of 𝔅₃) + D-11 (instance pin) +
  contingent OL-O12-1. Lean unit U-B (𝔅_n solve-table family + pole-free theorem)
  DISPATCHED per the ledger, parked consumers noted.
* **O-13 = VERIFIED at its honest scope — the FIRST leaf (recap).** Pass 1 (Codex V8):
  SOUND-WITH-GAPS → gaps repaired in rev 2. Pass 2 (fresh Fable, model-diverse,
  package-only context): all six gaps non-consumed cosmetics; the verifier
  re-implemented the enumerator from the package text alone and reproduced
  |S_n| = 1, 15, 53, 197, 509, 1460 exactly (ledger §"O-13 REACHES VERIFIED,
  2026-07-31 night"). Scope: skeleton/menu finiteness, p-free by typing; (COMP) the
  named condition (D-12r rides the D4R.0-K(c) verdict pin, a SEPARATE node); VAL-DIV a
  labeled conjecture. Lean: `skeleton_finite n` at every n (SkeletonFinite.lean,
  catalogue encoding); the hfin consumer unwiring is parked as unit U-F behind the
  recorded import-order block.
* Repair-wave landings already on record (path step 1 below, partially done):
  **O-1thr rev 4** landed (commit 5613274 — V24's criticals repaired, (M6c)
  requantified, the REAL≡ circle killed; the sloped pin STANDS per ledger; fresh pass
  owed) · **O5triple rev 3 + O-2a rev 5** landed (commit 6fe1b2d — both 0-critical;
  OL-3 trimmed to OL-3-min; the L5b′ = (L2) single-point cross-package seam flagged).

### D2.6 The recut mandatory path, in dispatch order (REPLACES §D1.6's slots 1–11)

1. **Repair wave** (verification-only, cheap): O-1thr rev 4 [LANDED, pass owed]; O-2a
   OL-3-min trim + O5triple rev 3 [LANDED, passes owed]; Dfloor pass 2 [DONE — D2.5].
2. **GD-5 composition note** (one page, closes the base seam) + the **S-1 machine
   transcription audit** O-1thr ↔ O-2a stage interface (the audit IS the content).
3. **THE GD CAMPAIGN** (the critical mass): one prover-unit family for GD-1, GD-2,
   GD-3 (min core first, full form for the value side), GD-8 — stated over an arbitrary
   absolutely-unramified complete DVR from the start (kills most of D-3); GD-4/GD-6 as
   engine-bookkeeping units alongside. Falsifiers: T-E/T-F harnesses extended to
   order ≥ 2 states; the HK52 stretch gate as the standing GD-2(c) trap; the 871-sample
   (L3+) harness for GD-8. [Campaign head DISPATCHED per ledger: GD-2/GD-3 as ONE
   MacLane/GMN unit.]
4. **The literature unit** (one session): GMN §2.1/§3/§4.1 pulls for GD-1(R-1)/GD-7
   (a)–(c) + L5b normalization + printed-TAMS pagination; MacLane 1936 pin for (V1);
   LIT-3 numbers + Mathlib probe. (LIT-5/BNS: struck, pending the D2.7 OB2 audit.)
5. **The K-RUN-C composition** (CU-1..CU-7 per D2.3): depth-3 falsifier FIRST (CU-1's
   gate), then the CU-1 spec, then the rest as the consumption arrows dictate; the
   D2.1/D2.4 tree edits are executed by THIS delta. [CU-1 prover DISPATCHED, gated.]
6. **O-5/D-7 close** (O5triple Theorems + cluster interface via CU-7), then **O-4
   OL1-ii** assembly (CU-2 + CU-4 + GMN Cor 4.19).
7. **O-9** (OL-A/C/D over GD-3-full) ∥ **O-10** (K-COUNT/K-JAC; D-8 guard + consumer
   audit).
8. **D-11 + OL-O12-2** (instance pin; run the D2.7 OB2 audit here at the latest) →
   **O-11** (D-9 corrected dependency set) → **root assembly** (Phase C; D-1/D-2/D-4
   in hand per D2.5; Asvin's scaffold shape as the document spine).

Formalization-side (non-blocking, from SYNTH4 §4): U-D (O5triple Theorem B abstract
counting lemma) + U-A (`GDInterface` design — ONE Lean structure carrying GD-1..GD-6,
the enforceable mirror of the D2.2 merge) are hours-scale; U-B/U-E prover-unit-sized
[U-B, U-D, U-E DISPATCHED per ledger]; U-C/U-G wait on their pass-2s; U-C additionally
PARKED (capstone-statement sign-off class).

### D2.7 Owed check: the OB2-alleged-D-11-consumption audit

**The one audit gating a further eviction (SYNTH4 §2.1, flagged to the D-11 owner).**
O3design's §4 consumer table carries the row "D-11: σ invariance | OB2". If D-11's
eventual statement really consumes OB2 (σ-invariance under the BNS ∼_OM equivalence),
then the cheap level-free OB2 stays root-mandatory WITH its BNS §2 definitional pin
(CU-6 as written). If — as this tree's own D-11 statement suggests (kernel entries as
Haar volumes of continuation events; no ∼_OM quantifier anywhere in D-11's text) — it
does not, then OB2 leaves the mandatory path too, CU-6 moves to the deferred tier, and
the LAST root-side BNS touch-point disappears. Deadline: adjudicate no later than D-11
dispatch (path step 8); record the outcome as a DELTA-3 line. Until adjudicated, CU-6
stays root-side (the conservative reading).

— DELTA 2 complete, 2026-08-01. Original tree + DELTA 1 above byte-untouched; the §4
acceptance criterion unchanged (§D1.7). Next tree edit: DELTA 3 after the GD campaign's
first wave + the D2.7 audit.

---

## DELTA 3 (wave-8 fold) — append-only, dated 2026-08-02

*(Executes the ledger's wave-8 adjudications: `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`
§"WAVE 8 COMPLETE (2026-08-02, commits a9f294c/6caf586/3e9f199)", folded at 6e170e6.
Everything above — DELTA 1/2 included — is byte-untouched; corrected readings recorded HERE
govern. The §4 acceptance criterion is unchanged and applies verbatim (§D1.7 discipline).
No Lean file is touched by this delta. Unit: D3CU2t (which also EXECUTED CU-2t — §D3.5).)*

### D3.1 CU-6 EVICTED from the root-mandatory path (the D2.7 audit, adjudicated)

The owed §D2.7 audit was ANSWERED at the CU cluster unit —
`lean/notes/openmath/CU_cluster_phaseB.md` §6.1 (commit a9f294c): **NO on every text on
file** — the D-11 node text (§D1.2) carries no ∼_OM quantifier; O-12's OL-O12-2 is a pure
table-data identification with no BNS object; the O3design §R2 row has no warrant sentence
and its visible ancestry is a rates-only (LIT-5-consuming) rationale that is D-16's move.
What D-11's mass identification DOES need is σ-CONSTANCY ACROSS ONE CONTINUATION EVENT'S
CYLINDER — per-box lift uniformity, owned by O5triple Theorem E + D-15 (via CU-7's
interface) — NOT σ-invariance across ∼_OM-equivalent polynomials. Orchestrator adjudication
(math-first delegation, ledger wave-8 entry): **the CUC §6.1 recommended line is signed
off.** Governing consequences:
* **CU-6/OB2 leaves the root-mandatory path** → deferred tier (route R-QNT, D-16's package,
  alongside OB1). §D2.3's CU-6 bullet and §D2.6's conservative root-side placement are
  SUPERSEDED.
* The BNS §2 definitional pin (Defs 1.7/3.1–3.2) leaves with it: **ZERO root-side BNS
  touch-points remain.** §D2.4's "ONE residual BNS touch-point … pending the D2.7 audit"
  resolves to none; LIT-5 is now route-R-QNT-only OUTRIGHT (§D2.6 step 4's parenthesis
  resolves the same way).
* The D2.3 consumer-walk arrow "D-11 σ-invariance ← CU-6" is DELETED, replaced by
  "row-label σ-constancy ← CU-7 (O5triple Thm E) + D-15" (CUC §8 arrow delta (3)).
* Gate G-OB2 is retained as a free-rider; CU-6's §6 proof-by-citation text stays on record
  in the deferred tier (nothing is discarded).
* Standing caveat (O3adj §4 R3 discipline, carried): D-11 is OPEN — if its eventual PROOF
  (as opposed to every present statement text) pools OM-equivalent instances, this eviction
  re-opens as a re-scoping event, not a silent assumption.

### D3.2 The O-9 index fix (recorded display correction; corrected reading governs)

The §2.4 O-9 node text (and M08 §3, which it quotes) writes the order-(r+1) census field as
F_{q^{f̄_r}} with f̄_r = f₀⋯f_{r−1}. **Off by one:** in GMN indexing the order-(r+1)
residual polynomials of a type of order r live over F_{r+1}, of degree **d = f₀⋯f_r** (one
more factor, the type's own f_r = deg ψ_r included). Everywhere the O-9 node writes
q^{f̄_r}, read q^d; the census statement's polynomial-in-q content is insensitive, the field
degree display was wrong. Evidence: `lean/notes/openmath/O9_phaseB_verifybrief.md` §"INDEX
FLAG" + attempt §1 (commit 6caf586); the harness instance (order-1 parent with root key X:
f₀ = 1, f₁ = g, reads over F_{q^g}) pins it concretely.

### D3.3 O-9 status update: REDUCED to (GR-B) + (FRESH) — zero new open inputs

Per §0 vocabulary (a reduction is not a proof): **O-9 at order ≥ 2 remains OPEN, now
REDUCED to exactly two pre-existing named opens** — **(GR-B)** (GD23 rev 2/3 §7.2's
anchored-march residue-structure package = the GD-2/GD-3 head, order-1 instance PROVED,
orders ≥ 2 under the GD23 verification arc) and **(FRESH)** (the joint-with-parent
separation clause, priced at the GD-2/CL-13 vertex-law layer = CU-1's step content).
**O-9 adds ZERO new open inputs to the mandatory path.** On file (commit 6caf586;
`O9_phaseB_attempt.md` + `O9_phaseB_verifybrief.md`, hostile pass owed —
PROVED-UNVERIFIED artifacts): OL-A(i)/(ii) proved outright (Lemmas A1/TRI/LED over the
pinned GMN Prop 2.7(1)(3)(4) + Lemma 2.2(2)); OL-A(iii) CONSUMED from GD-3 (executing
D2.2's "OL-B is GD-3" re-pointing — the tree's OL-B row is thereby discharged as a
separate obligation); OL-A(iv) = the displayed (DET) sufficiency + (FRESH); OL-C = the
two-theorem census **CEN-W** (window form, conditional on (GR-B) alone; free-end factor
(q^d − 1)^ε) / **CEN-J** (joint form = THE O-9 census, conditional on (GR-B) + (FRESH);
ε killed by JUNCTION-PIN). **TYPE-MARCH** (+ the F₃ type-breaking countermodel (1,1,2):
{(1,2)} ↦ {(2,1)}) shows the march is what makes the census polynomial — GD-3-FULL is a
THEOREM-LEVEL dependency of the value side, sharpening SYNTH4's pricing note. Falsifier
executed (M08's proposed T6): `verification/openmath/o9_order2_census_check.py` — 10
configs, 8,220,994 boxes, 1,128,288 order-2 instances, checks K1–K4 + T2 all 0 violations,
18 cross-p census cells (one over F_{p²}), fitted spectrum ε = 0 throughout.

### D3.4 O-10 status update: PROVED-UNVERIFIED IN FULL, SHARPER than charged

**O-10 (SIB/JC) moves OPEN → PROVED-UNVERIFIED** (proof on file, commit 3e9f199,
`lean/notes/openmath/O10_phaseB_attempt.md`; hostile pass owed; ledger grade "PROVED IN
FULL SHARPER"). Content: **K-COUNT proved in full**, self-contained in factor coordinates
over ℤ_p, sharper than the D-8 charge — the fibers of the level-N multiplication map over
a ρ-separated polydisc are constant and nonempty at EVERY N ≥ τ, of size
p^{Σᵢ min(eᵢ, N−τ)} for the Smith profile (eᵢ) of the Sylvester block map, which equals
p^ρ exactly in the D-8 guard range N ≥ τ + e_max (e_max ≤ ρ) — Sylvester block
determinant + in-polydisc Smith-profile constancy + Newton T-bijection. Theorem 2 = the
adapted-cell O-10 statement carrying the D-8 guard, UNCONDITIONAL in factor coordinates
with the (SIB) product law; its application to the engine's realized site strata is
conditional on the two displayed open interfaces (K-LOC = M07 OL-3, and (I-τ)) — exactly
as the tree prices them. K-JAC (polydisc form) = its Lemma 3; K-FACT consumed as the
recorded GMN citations. **OL-4/D-8r RESOLVED within the adapted regime** (no small-N
anomaly; the product law needs only the read-depth guard; the 2ρ buffer buys the explicit
p^ρ). M07's fences mapped one-per-clause; the item-27 Lean statement repair stays PARKED.
Falsifier: `verification/o10_kcount_harness.py`, 68 PASS / 0 FAIL (predictions sealed
pre-run; one post-hoc refinement honestly recorded). D-8's guard is confirmed in the
sharper exact-fiber form; consumers (T-6 (SIB-STEP), O-11's K1) are now served at the
statement layer through the displayed K-LOC interface.

### D3.5 CU-2t EXECUTED (the one open lemma of the CU cluster)

The CUC's honest flag (its §2: "OPEN (one lemma)") is discharged: **Lemma CU-2t is
written and proved** — `lean/notes/openmath/CU_cluster_phaseB.md` §9 (unit D3CU2t, this
delta's commit): the (t-i)/(t-ii) terminal seam as one lemma, per the recorded route
O-2a Thm 2(B) + Cor 1.20/3.8 + TB-CAP windows. Grade: **PROVED-UNVERIFIED, conditional on
P(O-2a r5) + TB-CAP's D-12r perimeter + the GD residue** (zero new open inputs; the two
engine-bookkeeping terminal rows (T-DEC)/(T-VERD) are displayed GD-4-family instances —
scope note owed to the GD-4 owner). Displayed extras: the W3 carrier note (the τ-irr seam
object is a PAIR, not an 𝔈-concatenation) and the quarantined Corollary CU-2t-deep (the
GD-8 exact-key corner, conditional on the unpinned (REP-IRR) literature pull — flagged to
the literature unit). §D2.3's CU-2t bullet reads accordingly; hostile pass owed.

### D3.6 The pending-verdict registry + the remaining mandatory path

**Registry pointer (governing):** every CONDITIONAL-ON-PASS in the CU/GD/O-* Phase-B
grades resolves through the CUC §0 pending-verdict registry
(`lean/notes/openmath/CU_cluster_phaseB.md` §0) — the live key for P(O-2a r5),
P(O-1thr r4), P(O5t r3), P(CU-1 r2), P(GD23 r2). Tree readers consult it before citing
any D2.3/D2.5 grade.

**Remaining mandatory path (supersedes §D2.6's tail; ledger wave-8 wording):**
1. **The running pass-2 verdicts + wave-8/9 verifications.** GD23 r3 pass 2 LANDED while
   this delta was drafted (commit 4d109b9: SOUND-WITH-GAPS, 0 critical, 9 justification
   gaps — adjudication + light repairs owed); CU-1 r3 pass 2 LANDED (commit 252f34c:
   SOUND-WITH-GAPS, 0 critical, 7 consumption-accounting/display gaps — same); O4T r2
   pass 2 RUNNING. Fresh hostile passes owed on the wave-8 artifacts: O-9 (§D3.3), O-10
   (§D3.4), the CUC record + CU-2t (§D3.5), and the §0-registry passes (O-2a r5,
   O-1thr r4, O5triple r3).
2. **CU-2t** — EXECUTED (§D3.5); verification rides item 1.
3. **D-11 + OL-O12-2** (instance pin) — now precisely priced post-audit: kernel entries as
   Haar volumes of T-3/T-6 continuation events with per-row disjointness + termination
   margin + block system 𝔅_n (or the O-12 robustness criterion); the σ input is row-label
   σ-constancy ← CU-7 (O5triple Thm E) + D-15; **no OB2, no BNS** (§D3.1).
4. **O-11** (D-9 corrected dependency set: O-10 [now §D3.4, guarded] + O-5/D-7 semantic
   labels + O-8b/O-9 transition weights + K2/D-9k + K4; [1v]-FULL value content its own).
5. **ROOT ASSEMBLY** (Phase C; D-1/D-2/D-4 in hand per D2.5; Asvin's scaffold shape as
   the document spine).
Throughout: the GD-1..GD-8 families remain the conditionality mass behind items 1–4; their
heads are the GD23/CU-1 arcs (item 1) + the GD campaign (D2.6 step 3, in flight).

### D3.7 In-flight events landed while this delta was drafted (recorded, NOT adjudicated)

Two sibling wave-10 units committed between this delta's drafting and its landing;
recorded for honesty against §§D3.3/D3.6, adjudication rides the next fold:
* **O-9 verify pass 1: NOT ACCEPTED** (commit c17777f; 2 criticals / 3 gaps) — the census
  exponent E′'s left-tail ceiling is REFUTED by a machine countermodel (256 vs 64:
  overcount q^d per integral left-tail slot), and JUNCTION-PIN's PROVED label is
  unsupported against the unit's own §5.4; the verifier's SOUND sublayer: TYPE-MARCH + the
  F₃ countermodel, A1/TRI/LED, (DET), and CEN-W's (GR-B)-only conditionality. Consequence
  for §D3.3: the reduction's SHAPE (zero new open inputs; (GR-B) + (FRESH)) survives per
  the verifier's own sound-list, but the exponent ledger needs a repair round — §D3.3's
  "hostile pass owed" reads "repair + re-pass owed". The §D3.2 index fix is untouched.
* **D-11 (MASS-ID) Phase-B attempt LANDED** (commit 0cae7d8) — M1/M1′/M2/M3, with M3
  (O5triple Thm E + D-15 σ-constancy) explicitly re-confirming "OB2 unconsumed" — the
  §D3.1 eviction's factual basis re-confirmed by the D-11 prover itself; OL-O12-2's math
  half closed there, residue a finite data pass. §D3.6 item 3 is in execution, verdict
  owed.

— DELTA 3 complete, 2026-08-02 (unit D3CU2t). Original tree + DELTA 1/2 above
byte-untouched; §4 acceptance criterion unchanged. Next tree edit: DELTA 4 at the wave-10
fold (the §D3.7 verdicts + the pass-2 adjudications of §D3.6 item 1).

---

## DELTA 4 (2026-08-02, unit TREE-GAPS) — the announced fold-back + the tree-completeness-audit resolutions

*(Original tree + DELTAs 1–3 byte-untouched; corrected readings govern. This delta
executes DELTA 3's closing announcement — the wave-10/14 + VC1–VC3 fold — and resolves
the completeness audit's five gaps G-1..G-5 and five advisories A-1..A-5
(`lean/notes/openmath/TREE_COMPLETENESS_AUDIT_2026-08-02.md`, commit fba7f16). The §4
acceptance criterion is UNCHANGED. Every ROOT touch this delta owes is EXECUTED in
`docs/ROOT_ASSEMBLY_2026-08-02.md` at this unit — the [TREE-GAPS] tags there.)*

### D4.1 The fold-back (supersedes §D3.6's tail; adjudicates §D3.7)

**The ROOT ASSEMBLY (`docs/ROOT_ASSEMBLY_2026-08-02.md`, REVISION 3, unit of record
ea0336f) is the OPERATIVE status ledger for every node this tree tracks.** Where a
tree/delta grade and the ROOT ledger diverge, the ROOT governs; the completeness audit
walked every node and found each divergence traces to a named later harvest (c43b13b,
7b28562). §D3.7's two recorded-not-adjudicated events are adjudicated as the ROOT
records them: (i) the O-9 arc — pass 1 NOT ACCEPTED → r2 (01c21e6) → pass 2 UNSOUND →
r3 (460ea59) → pass 3 NOT ACCEPTED → **r4** (031784c: (ADM) at FULL attainment), fresh
pass owed; (ii) the D-11 attempt (0cae7d8) entered the ROOT as Steps 17/18b (the
D-11/O-11 cycle stratified 17 ≺ 18 ≺ 18b), now at r3 (8a0786c), pass 3 owed. §D3.6
item 1's pass-2 adjudications landed as: GD23 → VERIFIED (leaf #4, c43b13b); CU-1 →
VERIFIED (leaf #5); O-10 → VERIFIED at scope (leaf #6; both 7b28562); O4T → VERIFIED
(leaf #7, 8602e97, post-audit) — **VERIFIED = 7** with Dfloor/O-12/O-13 (leaves
#3/#2/#1). Also recorded post-audit: CU-2t R3 light (81589e9; the GD-4 residue history
0 → 2 → 3 rows said plainly there; fresh pass owed). End-to-end: VC1–VC3 ran, each
COMPOSITION-GAPS → repaired in place (ROOT §§7–9); the ≥ 2-consecutive-clean counter is
at ZERO. [In flight at this unit's close: **ROOT REVISION 4** (unit ROOT r5, sibling
session) — VC4 (Codex) ran COMPOSITION-GAPS (4 blockers + 1 advisory, again all
attribution/ledger integrity); headline repairs landing concurrently: a NEW (ROOT-C)
hypothesis **(H5) = (PACK)** (D-11's open clause 4, the actual-pack row
correspondence, promoted to a §3.1 [M] row — finding VC4-3), clause (SQ)'s
attribution corrected DOWNWARD to unconditional (VC4-4), the (K3-δ) fragment of
(H4b) attributed to clause (R) (VC4-1), (ADM) synced to O-9 r4's FULL-attainment
form (VC4-2). Where this delta's §D4.2/§D4.3 sentences say "(H1)–(H4b)", read the
hypothesis list AS OF REVISION 3; the (ROOT-C)-impact adjudications below are
restated against (H5) in place at their sites. The r5 commit is that revision's unit
of record.]

### D4.2 G-4 ADJUDICATED — the six H.6 fences gating [1v]-FULL: SUPERSEDED AS ROUTED into D-11 item (vii); one live condition; no (ROOT-C) hypothesis affected

**The question (the audit's one potentially-real conditionality).** Tree T-5: "Its six
H.6 fences gate the [1v]-FULL event"; tree O-11's K3 repeats the gate. ROOT Step 18
assembles K3 from T-7s + O-9 + O-8b with no fence mention (grep-zero at the audited
text). Either the O-11/D-11 residue restructure superseded the gate on record, or a K3
conditionality was undisplayed.

**The displayed evidence.** O-11 r2/r3's K3-a — the pass-1 G-5 repair, quoted from
`O11_phaseB_verifybrief_rev3.md` §3.4: "the six H.6 fences GATE this event at every n
(tree T-5 row); that the BUILT per-n tables sit INSIDE the fences is proved nowhere at
general n — V-n3/H-n3 (151/151) are the SEALED n = 3 EVIDENCE, not a proof. At general
n, in-fence conformance of the constructed pack is a construction obligation of the
instance pin — D-11's restated charge, item (vii)"; and its §0 restated D-11 entry:
"(vii) general-n H.6 fence conformance of the built tables (K3-a; n = 3 evidence
V-n3/H-n3)", with "(v)–(vii) WIDEN the dispatch's WAVE-8 charge: acceptance owed by
the D-11 rev-2 owner ... until accepted they are displayed here as D-11-charge-pending,
not silently ridden."

**Adjudication: SUPERSEDED AS ROUTED — honestly, not silently, and NOT discharged.**
The restructure split the tree's gate line into (i) the six fences as the PERIMETER of
T-5's dual acceptance — open general kernels with owners and refuters UNCHANGED
([2b]/§H-DOMAINS roster, `ASSEMBLY_PLAN_2026-07-26.md` REV 15/16), which NO root step
consumes as general lemmas; and (ii) the single live condition the root DOES consume
at Step 18's K3-a: in-fence conformance of the built per-n tables, open at general n,
= D-11 restated-charge item (vii). The M2 seams and declared rows do NOT carry fence
content — (S1)/(S2) are D-11 M2's hand-off seams (← Steps 14/18), D-a/D-b/D-c are the
K4-CYL/(I-τ)/(R1)–(R4) interfaces — item (vii) is the SOLE carrier. Fence-by-fence
(the mapping is uniform: the restructure treats the six as one perimeter):

| H.6 fence (REV 15/16 roster) | general kernel — owner unchanged | consumed by ROOT Step 18? |
|---|---|---|
| (1) XHD-d-EX(∂) boundary-component exactness (H.2.3) | fenced at [2b]; H-n3 low-height corner = evidence, not discharge | NO — only via item (vii) |
| (2) M4b-T-AUD normal-form-audit ALL-quantifier + π_v = id (H.5.1) | fenced at [2b]; H-n3 constancy layers run, STATE-probe-2 unrun | NO — only via item (vii) |
| (3) U-R-COUNT per-species representative count (H.4.2/H.5.3) | fenced at [2b]; JOINT-probe unrun, H-n3 rep layer run | NO — only via item (vii) |
| (4) XHD-u-X cross-component count equality (H.4.3) | fenced at [2b]; heterogeneous ≥ 2-component re-seal duty stands | NO — only via item (vii) |
| (5) H-LIST-GEN listed partitions beyond class (TRI) | fenced at [2b]; needs a non-adjacent gate family | NO — only via item (vii); sharpest escalation risk |
| (6) E-POS per-period template-total positivity ⟨w_E, v⟩ ≥ 1 | fenced at [2b]; per-family displays only (coordinatewise form FALSE) | NO — only via item (vii) |

**Status effect + the owed displays (executed at this unit).** The tree T-5/O-11 gate
lines now READ: "gated on T-5's six H.6 fences" = conditional on D-11 item (vii) (the
fences' conformance face); the fence kernels themselves are [2b]-owned perimeter, off
the mandatory path. The ROOT gains (1) the Step-18 fence display and (2) an OPERATIVE
§3.3 row for the widened-charge items (v)–(vii) — REVISION 1 executed the owed touch
only as the §7 audit-trail note "(5) ... noted pending acceptance" with no operative
row; that was the actual residue of gap G-4. **(ROOT-C) impact, said plainly: NO
hypothesis is affected** — (H1)–(H4b) are unchanged; item (vii) conditions the PROOF
of the composed implication through D-11's PENDING tier-1 grade at Steps 17/18
(alongside D-11's other open instance-pin clauses, e.g. M1(a)'s displayed exclusions
and the clause-4 actual-pack correspondence), not the statement's hypothesis list.
Escalation is displayed, not hidden: if the D-11 owner rejects items (v)–(vii), or a
built pack NEEDS fenced territory (sharpest: H-LIST-GEN's beyond-(TRI) partitions),
the fence kernel so touched enters ROOT §3.1 as [M] on clause (R)'s chain.
[REVISION-4 sync (see §D4.1's in-flight note): the concurrently landing (H5) =
(PACK) is D-11's clause 4 (pack↔𝔅_n row correspondence) — a DIFFERENT D-11 clause
from item (vii) (H-fence conformance); G-4's adjudication stands: the fence residue
neither created nor modified any (ROOT-C) hypothesis, and whether item (vii) should
be promoted to hypothesis grade like clause 4 is flagged to the next VC pass at the
ROOT §3.3 row.]

### D4.3 G-1/G-2 — O-14b (cl19 carrier ladder) + O-14c (hStateNe) HOMED; D-10's criterion clause re-scoped

**O-14b (the cl19 repaired carrier ladder, post-K-7).** OPEN. Root-side consumption:
NONE — no ROOT §2 step consumes it (audit grep-zero: `cl19` absent from the ROOT), and
K-7's dangling "repaired carrier form = part of leaf O-14" pointer lands HERE. Its
actual consumer is the Lean-bridge slot wiring: carrier-parameterize `Slot_jcInvHist′`
+ the O1–O3 semantic ladder at a real carrier pack = **queue item 22**
(`REMAINING_CENSUS_2026-08-01.md`: "REFUTED AS STATED (M11, dual; queue item 22; G13′
gated)"; theoremU itself SAFE — bare-Prop slot), PARKED by the 2026-07-31 math-first
directive (fe3cda5: items 22–29 parked until the mathematical completion lands).
HOMED: ROOT §3.3 "O-14a/b/c engine-residue dispositions" row, owner Lean side
post-math.

**O-14c (hStateNe derivability).** OPEN, expected derivable. = `BridgePre.hStateNe`,
a NAMED RATIFIED PREMISE of the Lean bridge (`BRIDGE_ADJUDICATIONS_2026-07-30.md`:
"ratified as named premises (hStateNe derivation attempt first)"); standing
disposition = the IB-B2 derivation attempt (`BRIDGE_BP1_INSTANCE_2026-07-30.md`; if it
closes, the row DROPS — a fence event). Root-side consumption: NONE. Same ROOT row,
same owner.

**Verified and said plainly (the dispatch's charge):** both are post-item-22 /
derivation-attempt Lean-bridge territory, OFF the (ROOT-C) hypothesis list — display
sweep at this unit: neither `cl19` nor `hStateNe` nor any O-14b/c content appears in
(H1)–(H4b) or any ROOT §3.1 [M] row. **D-10's completion-criterion clause is
RE-SCOPED (corrected reading, governs):** "all leaves proved means O-14a/a′/b/c each
closed" now reads at the MATH criterion as O-14a (e′ = 1 CLOSED, §D4.4; ≥ 2
disposition = sign-off item 28) + O-14a′ (consumed at ROOT Step 9; residue displayed
there); O-14b/c join O-14d and items 27/28 in the PARKED engineering register —
engine-internal instance lemmas whose closure gates the LEAN BRIDGE, not the root
composition.

### D4.4 G-3 — O-14a's guarded e′ = 1 vertex-transport law: CLOSED at its sub-perimeter

The guarded law at ν_{i+1}.e = 1 is PROVED with a machine-checked Lean twin:
**`lean/LeanUrat/HC2/HK11a_vertexTransport.lean`** (the σV-vertex transport law at
e′ = 1, Lean-core; unit record `QUEUE_EXECUTION_2026-07-31.md` POST-WAVE 1 + the
HK-11a kernel unit; in-repo at the fe3cda5 sweep). The unguarded form stays
REFUTED-AS-STATED (HK52_stretchGate — the compiled ν_{i+1}.e-stretch obstruction). The
consumer line the audit found missing, now recorded: on the ROOT mandatory path NO §2
step consumes the vertex-transport law in either form — its consumers are
engine-internal (the Lean bridge's V9/HK cone); the nearest ROOT content, GD-2's
clause-(c) HK52 trap, is the ≥ 2 COUNTERMODEL, not a consumption. The ≥ 2 disposition
remains sign-off item 28 (ROOT §3.3 PARKED row). Homed at the ROOT §3.3 O-14 row.

### D4.5 G-5 — `cl3_tails` (X2-TAILS): its own eviction row, route R-QNT

The tree O-8 row marks `cl3_tails` "a SEPARATE open estimate (owner §H-DOMAINS
family)" — by its own terms NOT carried by the O-6/O-7/O-8a eviction (D1.4).
Adjudication: it is a measure/cone TAIL estimate — quantitative-rate content of the
X.2 pricing family; the count-native mandatory path controls undecided mass by
DRAINAGE (ROOT Step 13 / O-4), never by tail rates; nothing on the root path consumes
it (audit grep-zero). **EVICTED to route R-QNT on its own row** — warrant: the D1.4
rates-only adjudication extended to it by content class, recorded here rather than
ridden on O-8a's terms; owner if rates are ever elected: §H-DOMAINS family/[2b]. ROOT
§3.3's NOT-on-ledger paragraph now names it.

### D4.6 Advisories A-1..A-5 — executed

* **A-1 (T-11/JOINT-D1 id).** ROOT §3.3 gains the closed-row id table: T-11 → Step 2
  inside T-1's perimeter (D1-marginal machine-checked, `OM/DevBijection.lean`).
* **A-2 (LIT-4/OM-SAT roster id + scope caveat).** ROOT §4 item 1 gains the LIT-4
  line: the id, its content (Cor 3.8 + Def 3.9; order-1 Cor 1.20), the audited
  **"K = ℚ_p exactly"** scope, consumption only through dictionary node O-2, and the
  K_δ re-scope duty NAMED as (UB-X)(a) content (previously covered only generically).
* **A-3 (K-OB-D).** Named in the ROOT NOT-on-ledger paragraph: certificate-firing at
  O-5's threshold; evicted by containment — sole consumer O-7, route R-QNT (D1.4 +
  D2.4); the containment is now a recorded line (the last IFK REV-1 obligation
  without an explicit disposition).
* **A-4 (K-14 duty (I2)).** Adjudicated: (I2) = level coherence TRANSCRIBES T-3
  §D4-R's own stabilization-level definition (D4R.4/L12: N(P̂) := max of per-prefix
  resolution levels, finite by L8) — definitional at the statement layer, per M18
  fable §6.2's displayed warrant; its instance-build face rides the O-14d/D-11
  population with the other build-conformance duties. Not a missing consumer-walk
  edge; recorded in the ROOT closed-row table.
* **A-5 (refuted/closed row ids).** The ROOT closed-row id table displays content
  homes for K-1/K-2/K-15 (CLOSED Lean-interface), K-3, K-5, K-7 (→ O-14b), K-8, K-9,
  K-10 — the tree-§4 criterion-4 reading ("every node id appears in the document or
  in its explicitly-argued pruning list") is now checkable against the ROOT text.

### D4.7 Disposition table (this delta)

| audit finding | resolution | recorded at |
|---|---|---|
| G-1 O-14b | HOMED: PARKED-class engine row (queue item 22; directive fe3cda5); K-7's pointer lands here; off (ROOT-C) | §D4.3; ROOT §3.3 O-14 row |
| G-2 O-14c | HOMED: `BridgePre.hStateNe` named ratified premise; IB-B2 derivation attempt; off (ROOT-C) | §D4.3; ROOT §3.3 O-14 row |
| G-3 O-14a guarded law | CLOSED at e′ = 1 (Lean twin `HC2/HK11a_vertexTransport.lean`); ≥ 2 = item 28 PARKED; no §2 consumer | §D4.4; ROOT §3.3 O-14 row |
| G-4 H.6 fences @ K3 | SUPERSEDED AS ROUTED → D-11 item (vii); uniform six-fence mapping displayed; operative [T] row + Step-18 note added; (H1)–(H4b) UNAFFECTED | §D4.2; ROOT Step 18 + §3.3 widened-charge row |
| G-5 cl3_tails | EVICTED route R-QNT on its own row (content-class warrant) | §D4.5; ROOT §3.3 NOT-on-ledger |
| A-1 T-11 id | closed-row id table | ROOT §3.3 |
| A-2 LIT-4 | roster line + "K = ℚ_p exactly" caveat named at (UB-X)(a) | ROOT §4 item 1 |
| A-3 K-OB-D | containment eviction recorded by name | ROOT §3.3 NOT-on-ledger |
| A-4 K-14 (I2) | definitional vs T-3 D4R.4/L12; instance face → O-14d/D-11 | §D4.6; ROOT §3.3 |
| A-5 closed-row ids | id table added | ROOT §3.3 |

With these homes recorded, the audit's criterion-4 blocker list is EMPTY: all five
gaps homed or adjudicated with displayed evidence, all five advisories executed. No
leaf grade changed at this delta; no new mathematics claimed.

— DELTA 4 complete, 2026-08-02 (unit TREE-GAPS). Original + DELTAs 1–3 byte-untouched;
§4 acceptance criterion unchanged and applies verbatim. Next tree edit: DELTA 5 at the
VC4 disposition (or the next harvest).
