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
(status: **plan-review REJECTED (V4, 26 findings), revision 1 in flight** — the IFK nodes
below are marked blueprint-in-revision; the U6 K-RUN falsifier probe HAS run and **SURVIVES**,
`verification/openmath/results/U6_krun_results.json`, folded in); the numerics matrix N1–N8
(§NUMERICS FLEET of the adjudications ledger + `verification/openmath/`).

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
* **LIT-5 (BNS precision — CANDIDATE, NOT declared).** Bauch–Nart–Stainsby, *Complexity of
  OM factorizations of polynomials over local fields*, LMS J. Comput. Math. 16 (2013)
  139–171, **Theorem 3.13**: precision δ+1 (δ = v_p(disc f)) preserves OM factorizations of
  congruent separable polynomials. Pinned by the M05 verifier (V2 item 8, published-PDF
  link). Faithfulness duties before declaration (V4 findings 23–25 + M05/M12 flags): pull
  the PUBLISHED text verbatim (this exact paper has demonstrated arXiv-vs-journal numbering
  shifts — V1 items 1/5); state it on GMN-side objects only (no smuggled tree-correspondence
  or σ-invariance beyond the congruence clause); consume only through O-2. Status:
  LITERATURE-CANDIDATE, transcription + guardian audit + sign-off outstanding.
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
