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
