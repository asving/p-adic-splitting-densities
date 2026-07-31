# M05-exhaust — attempt (Fable, 2026-07-31)

Target: `BridgeKernels.env_tendsto` — for the project's classifier `X : ClassifierSpec n p`,
`Tendsto X.env atTop (𝓝 0)`, i.e. the undecided density `env(N) = undec(N)/p^{nN}` vanishes as
`N → ∞`, at every prime (wild included), every degree. See the companion brief
(`M05-exhaust_brief.md`) for the full unfolding; notation from there. Every result below is
labeled (a) known / (b) new proof of known / (c) claimed new, per the rigor rules.

**Summary of what is achieved here.**
* §1–§4: a fully rigorous proof (informal-rigorous, no gaps known to me) that the **semantic
  classifier** (Def. 4.1 — decide a level-`N` class iff all its separable lifts share one
  splitting type) satisfies `env(N) → 0` at every prime `p` and degree `n`, **with an explicit
  exponential envelope** whose only `p`-dependence is through `v_p(n)`.
* §5: the obligation for the **OM classifier** (the corpus's intended instance) is reduced to
  ONE clean open lemma (OL1: pointwise finite certification on the separable locus), which
  splits into GMN termination [known, already inside this project's trusted-citation perimeter]
  plus a finite-read property of the canonical run [checkable, corpus-policy-dependent]; a
  quantitative strengthening OL2 is stated with a literature candidate (flagged, unverified).
* §6: how the pieces map onto the corpus's existing conditional Lean derivation; a wiring
  observation (the row is unconditionally true for the semantic instance).

Throughout: `p` prime, `n ≥ 2` unless stated (`n ≤ 1`: every monic degree-`n` polynomial has
the forced type — `{}` or `{(1,1)}` — so any classifier that decides constants at level 0
gives `env ≡ 0`; the corners are dispatched in each statement). `μ` = Haar probability on
`Z_p^n` (coefficient vectors `a ↔ f_a = x^n + a_{n-1}x^{n-1} + … + a_0`). `v = v_p` is the
valuation, normalized `v(p) = 1`, extended (uniquely) to each finite extension of `Q_p` and to
`Q̄_p`, `Q`-valued there. `σ(f)` = splitting type of separable monic `f` (multiset of
`(e_i, f_i)` over the distinct irreducible factors; `Σ e_i f_i = n`).

---

## 1. Lemma A — measure form; the exact content of the row [(b): elementary, load-bearing]

Let `c = (c_N)` be ANY classifier in the brief's sense (functions on the level-`N` boxes with
values in types-or-⊥, satisfying stability). Put

    U_N := { a ∈ Z_p^n : c_N(a mod p^N) = ⊥ }   (a finite union of level-N cylinders, clopen).

**Lemma A.** (i) `env(N) = μ(U_N)` for every `N`. (ii) Stability implies `U_{N'} ⊆ U_N` for
`N ≤ N'`. (iii) Consequently `env(N)` converges, with limit `μ(⋂_N U_N)`; in particular

    env(N) → 0   ⇔   μ(⋂_N U_N) = 0   ⇔   for μ-a.e. a, some level decides a.

*Proof.* (i) `U_N` is the disjoint union of the `undec(N)` undecided cylinders, each of mass
`p^{-nN}`. (ii) If `a ∉ U_N`, say `c_N(a mod p^N) = σ`, stability gives
`c_{N'}(a mod p^{N'}) = σ ≠ ⊥`, so `a ∉ U_{N'}`; contrapositive. (iii) Continuity from above
for the finite measure `μ` on the decreasing sequence `(U_N)`. ∎

So the Lean row is *exactly*: the set of coefficient vectors never decided by the classifier
is Haar-null. No rate is required. (This equivalence is what the prompt calls "why does the
classifier terminate on a full-measure set".)

## 2. Lemma B — the `a_0`-structure of the discriminant [(b): classical]

**Lemma B.** For `n ≥ 2`, in `Z[a_0, …, a_{n-1}]`, the discriminant `disc(f_a)` has degree
exactly `n − 1` as a polynomial in `a_0`, with `a_0`-leading coefficient `± n^n` (a nonzero
integer constant, independent of `a_1, …, a_{n-1}`).

*Proof.* For monic `f` of degree `n`: `disc f = (−1)^{n(n−1)/2} Res(f, f′)`, and
`Res(f, f′) = (−1)^{n(n−1)} Res(f′, f) = Res(f′, f)` since `n(n−1)` is even. Work over
`K := Q̄(a_1, …, a_{n-1})` (note: `a_0`-free). In char 0, `f′ = n x^{n−1} + …` has degree
exactly `n − 1`; let `θ_1, …, θ_{n−1}` be its roots in `K̄` (with multiplicity) — these do not
involve `a_0` since `f′` does not. The resultant product formula gives

    Res(f′, f) = lc(f′)^{deg f} · ∏_{j=1}^{n−1} f(θ_j) = n^n · ∏_{j=1}^{n−1} (a_0 + c_j),
    c_j := θ_j^n + Σ_{i≥1} a_i θ_j^i ∈ K̄.

As a polynomial in `a_0` over `K̄` this is `n^n a_0^{n−1} + (lower order)`. Since `disc` lies
in `Z[a_0, …, a_{n−1}]` (Sylvester determinant of integer-coefficient entries), the identity
pins its `a_0`-degree and leading coefficient. ∎

## 3. Lemma C — the discriminant tail bound [(b): new proof of the in-corpus bound; the
statement is classical folklore, and its finite-level count form is already Lean-proved
(`MovesX.XF7.tailCountBound`, same exponent)]

**Sublemma C1 (one variable).** Let `P ∈ Z_p[x]` have degree exactly `d ≥ 1` and
`w := v(lc P) < ∞`. For every `m ∈ Z`:

    μ{ x ∈ Z_p : v(P(x)) ≥ m }  ≤  d · p^{−max(0, ⌈(m−w)/d⌉)} .

*Proof.* Factor `P = lc(P)·∏_{j=1}^d (x − β_j)` over `Q̄_p`. For `x ∈ Z_p` with
`v(P(x)) ≥ m`: `Σ_j v(x − β_j) ≥ m − w`. Set `t := (m−w)/d`; if `t ≤ 0` the claim is trivial
(`μ ≤ 1 ≤ d`). Otherwise some `j` has `v(x − β_j) ≥ t` (if all `< t`, the sum is `< dt`;
individual terms may be negative — the averaging is still valid). So the event is covered by
the sets `E_j := {x ∈ Z_p : v(x − β_j) ≥ t}`. If `E_j` contains a point `x_0`, then every
`x ∈ E_j` has `v(x − x_0) ≥ min(t, t) = t`, and `v(x − x_0) ∈ Z_{≥0} ∪ {∞}`, hence
`≥ ⌈t⌉`: `E_j ⊆ x_0 + p^{⌈t⌉} Z_p`, of measure `≤ p^{−⌈t⌉}`. Sum over `j`. ∎

**Lemma C.** For `n ≥ 2`, every prime `p`, every `m ≥ 0`, with `w := n·v_p(n)`:

    μ{ a ∈ Z_p^n : v(disc f_a) ≥ m }  ≤  (n−1) · p^{−max(0, ⌈(m−w)/(n−1)⌉)}
    (the event includes disc = 0, read v(0) = ∞).   In particular μ{disc f_a = 0} = 0.

*Proof.* The event is closed (‖disc‖ ≤ p^{−m}), hence measurable. Fix the tail
`(a_1, …, a_{n−1}) ∈ Z_p^{n−1}`; by Lemma B the slice polynomial `a_0 ↦ disc(f_a)` has degree
exactly `n − 1` with leading-coefficient valuation exactly `w = v(n^n)`, for EVERY tail. Apply
C1 to each slice and integrate (Tonelli) over the tail. The final claim: intersect over
`m → ∞`. ∎

Remark: the only `p`-dependence is the additive constant `w = n·v_p(n)` — wild primes cost a
bounded shift, nothing more. Numerics (§NUMERIC-TESTS, T1) confirm the bound exactly at 39
`(n, p, m)` triples, with equality at `n = 2` for tame `p` (the bound is tight there).

## 4. Theorem E — drainage for the semantic classifier, with envelope

### 4.0 Lemma D — local constancy of the splitting type, modulus `2v+1` [(b): known
in substance (Krasner-continuity of factorization); assembled proof with the explicit
constant given in full since the exact constant is load-bearing]

**Lemma D.** Let `f ∈ Z_p[x]` be monic of degree `n ≥ 1`, separable, `v := v(disc f) ∈ Z_{≥0}`.
Let `g ∈ Z_p[x]` be monic of degree `n` with `g ≡ f (mod p^{2v+1})` (coefficient-wise). Then
`g` is separable, `v(disc g) = v`, and `σ(g) = σ(f)`. Moreover there is a Galois-equivariant
bijection `α ↦ β_α` from the roots of `f` to the roots of `g` with `Q_p(β_α) = Q_p(α)`.

*Proof.* Let `α_1, …, α_n ∈ Q̄_p` be the (distinct) roots of `f`; they are integral
(`f` monic over `Z_p`), so `v(α_i) ≥ 0`. For monic `f`, `disc f = ±∏_i f′(α_i)` and
`f′(α_i) = ∏_{j≠i}(α_i − α_j)`; put `v_i := v(f′(α_i)) = Σ_{j≠i} v(α_i − α_j)`. Each summand
is `≥ 0` (integral roots) and `Σ_i v_i = v`, so

    (1)  0 ≤ v(α_i − α_j) ≤ v_i ≤ v   for all j ≠ i.

Write `h := g − f`: all coefficients in `p^{2v+1} Z_p`, `deg h ≤ n − 1`, and likewise `h′`.
For any integral `x`: `v(h(x)) ≥ 2v+1` and `v(h′(x)) ≥ 2v+1`. Hence for each `i`:

    (2)  v(g(α_i)) = v(h(α_i)) ≥ 2v+1 ;
    (3)  v(g′(α_i)) = v_i ,   since v(h′(α_i)) ≥ 2v+1 > v ≥ v_i = v(f′(α_i)).

*Hensel step.* `L_i := Q_p(α_i)` is a complete discretely valued field, `g ∈ O_{L_i}[x]`,
`α_i ∈ O_{L_i}`, and by (2), (3): `v(g(α_i)) ≥ 2v+1 > 2v_i = 2·v(g′(α_i))`. Newton–Hensel
(complete nonarchimedean field, standard; e.g. Lang, *Algebraic Number Theory*, II §2 —
attribution to be confirmed against the edition; the statement used is: `|g(α)| < |g′(α)|²`
gives a root `β ∈ L` with `|β − α| ≤ |g(α)|/|g′(α)|`) yields `β_i ∈ L_i` with `g(β_i) = 0` and

    (4)  v(β_i − α_i) ≥ v(g(α_i)) − v(g′(α_i)) ≥ 2v+1 − v_i ≥ v_i + 1 > v_i .

*Krasner step.* By (1) and (4), `v(β_i − α_i) > v_i ≥ v(α_i − α_j)` for every root `α_j ≠ α_i`;
in particular for every conjugate of `α_i` (conjugates of `α_i` are among the `α_j`). Krasner's
lemma (α_i separable; standard, same references — flagged for exact numbering) gives
`Q_p(α_i) ⊆ Q_p(β_i)`; and `β_i ∈ L_i` gives the reverse. So `Q_p(β_i) = Q_p(α_i)`.

*Distinctness and completeness.* For `i ≠ j`, by (4) and (1):
`v(β_i − α_i) > v(α_i − α_j)` and `v(β_j − α_j) > v(α_j − α_i)`, so the ultrametric strict-
minimum rule gives `v(β_i − β_j) = v(α_i − α_j) < ∞`, whence `β_i ≠ β_j`. Thus `g` (degree
`n`) has `n` distinct roots `β_1, …, β_n`: it is separable, all its roots are listed, and
`v(disc g) = Σ_{i<j} 2·v(β_i − β_j) = Σ_{i<j} 2·v(α_i − α_j) = v`.

*Equivariance.* First, uniqueness of the nearby root: for fixed `i`, if a root `β` of `g`
satisfies `v(β − α_i) > v_i`, then `β = β_i` — indeed `β = β_k` for some `k`, and for `k ≠ i`,
`v(β_k − α_i) = v(α_k − α_i) ≤ v_i` (strict minimum again, using (4) for `k`). Now for
`τ ∈ Gal(Q̄_p/Q_p)`: `τα_i = α_{i′}` for some `i′`, with `v_{i′} = v_i` (Galois invariance of
`v` and of the root multiset), and `τβ_i` is a root of `g` with
`v(τβ_i − α_{i′}) = v(β_i − α_i) > v_i = v_{i′}`; by uniqueness `τβ_i = β_{i′}`. So
`α_i ↦ β_i` is Galois-equivariant: it matches Galois orbits, i.e. the irreducible factors of
`f` and `g`, with equal degrees; and the per-root field equality `Q_p(β_i) = Q_p(α_i)` matches
each factor's `(e, f)`. Hence `σ(g) = σ(f)`. ∎

Wild primes: nothing above used `p ∤ n`; Hensel and Krasner hold in any complete
nonarchimedean field. The modulus `2v+1` cannot be replaced by anything not growing like `2v`
in general (not needed here; testable — see T3).

### 4.1 The semantic classifier and its drainage [(c) as an assembled, explicitly
quantified statement; (b)/(a) in substance — this kind of local-constancy density argument is
standard, e.g. in the density literature descending from Bhargava et al.]

**Definition 4.1 (semantic classifier).** For a class `x ∈ (Z/p^N)^n`:
`c^sem_N(x) := σ` if every separable monic lift of `x` has splitting type `σ` (separable
lifts always exist: by Lemma B the disc vanishes at only finitely many `a_0` per slice);
otherwise `⊥`. Stability is immediate (the lifts of a refinement form a subset). For `n ≤ 1`
it decides everything at `N = 0`.

**Theorem E.** For every prime `p` and `n ≥ 2`, with `w := n·v_p(n)`:

    env^sem(N)  ≤  (n−1) · p^{−max(0, ⌈(⌈N/2⌉ − w)/(n−1)⌉)}   for all N ≥ 0,

hence `env^sem(N) → 0` (rate `p^{−N/(2(n−1))}` up to a constant). In particular the
`env_tendsto` statement holds for the semantic classifier at every prime and degree.

*Proof.* Suppose the class `x` at level `N` contains a separable lift `f` with
`2·v(disc f) + 1 ≤ N`. Every monic lift `g` of `x` satisfies `g ≡ f (mod p^N)`, and
`N ≥ 2v+1`, so Lemma D gives: `g` separable with `σ(g) = σ(f)`. Thus ALL lifts of `x` are
separable of one type, and `c^sem_N(x) = σ(f) ≠ ⊥`. Contrapositive: if `x` is undecided, every
lift `a` has `disc f_a = 0` or `2·v(disc f_a) + 1 > N`, i.e. (integer `v`)
`v(disc f_a) ≥ ⌈N/2⌉`. So `U^sem_N ⊆ { a : v(disc f_a) ≥ ⌈N/2⌉ }`, and Lemma A(i) + Lemma C
give the bound. ∎

*Checks.* Monotone-decreasing, exponentially decaying undecided fractions confirmed
exhaustively (T2, 25 `(n, p, N)` cells, all within the bound; several with equality). Note the
`n = 2` proved corpus envelope `(⌊N/2⌋+1)·p^{−(N−1)}` is SMALLER for large `N` than Theorem
E's `≈ p^{−N/2}` at `n = 2`: the OM classifier decides faster than the Krasner radius
guarantees; that is consistent — E is an upper bound for a different (the optimal sound)
classifier.

## 5. The OM classifier: reduction, and the open lemmas

Theorem E does not by itself discharge the Lean row: the wiring's classifier is not the
semantic one but the OM verdict-tree classifier `c^OM` (brief §3), which decides by its own
certification rule. By Lemma A, for `c^OM` the row is EQUIVALENT to:

**OPEN LEMMA OL1 (pointwise certification, a.e.).** For every prime `p`, `n ≥ 2`, and every
monic separable `f ∈ Z_p[x]` of degree `n`, there is `N(f) < ∞` with
`c^OM_{N(f)}(f mod p^{N(f)}) ≠ ⊥` — the canonical OM run on `f` certifies completely, with
every inspected digit window below `N(f)`.

**Proposition 5.1.** OL1 ⇒ `env(N) → 0` for `c^OM`. *Proof.* The never-decided set is
contained in `{disc = 0}`, which is `μ`-null (Lemma C); apply Lemma A(iii). ∎

**Status of OL1 — a two-piece decomposition, both pieces (a)-known in substance:**

* **(OL1-i) Termination at finite order** [(a), and already inside this project's trusted
  perimeter]: Guàrdia–Montes–Nart, *Newton polygons of higher order in algebraic number
  theory*, Trans. AMS 364 (2012) 361–416: Theorem 4.18 (theorem of the index:
  `ind(f) ≥ ind_1(f) + … + ind_r(f)`) and Corollary 4.19: for monic separable `f` the OM
  descent terminates at finite order — at most `ind(f) ≤ v_p(disc f)/2` nontrivial steps.
  These exact statements are pinned in `docs/GMN_citations.md` (arXiv:0807.2620v2 numbering),
  and the GMN index theorem is already an allowed citation-axiom family in this project.
  `p`-independent; wild case generic.
* **(OL1-ii) Finite read** [(a/b) in substance; corpus-policy-dependent, so stated as the
  residual obligation]: every quantity the terminated run inspected — the finitely many
  vertices/slopes of the Newton polygons of the `φ`-adic expansions, and the residual
  coefficients over the finite residue towers — is a valuation statement (`v(Q(a)) = k` or
  `≥ k`) or a residue read at a known level, about a `Z`-polynomial `Q` in the coefficients
  `a` of `f` (the key polynomials `φ` being, under the canonical policy, themselves built from
  finitely many earlier such reads). Digits of `Q(a)` below level `k` are a function of digits
  of `a` below level `k`. A terminated run makes finitely many inspections, so all its
  witnesses fit below some finite `N(f)`, and the run — hence the verdict — is constant on the
  level-`N(f)` class. What remains corpus-specific: that the project's certification predicate
  ("thr ≤ N", realizability at the pinned level-`N` model) *accepts* at this `N(f)` — the
  agreement seam between the built classifier and the canonical run (at `n = 2` this is the
  corpus's optional built enrichment; at general `n` it is engineering, not new mathematics,
  but it is NOT discharged here).

**OPEN LEMMA OL2 (quantitative threshold — optional, gives rates).** There exist `A(n), B(n)`
(`p`-free) with `N(f) ≤ A(n)·v_p(disc f) + B(n)` for all separable monic `f`. Consequence, by
the Theorem-E argument run with `⌈(N−B)/A⌉` in place of `⌈N/2⌉`: an explicit exponential
envelope for `c^OM`, of the same shape as the proved `n = 2` `hExhaustP` envelope
`(⌊N/2⌋+1)·p^{−(N−1)}`. **Literature candidate (flagged, NOT verified):** Bauch–Nart–Stainsby,
*Complexity of OM factorizations of polynomials over local fields*, LMS J. Comput. Math. 16
(2013) 139–171, analyze the Montes algorithm's cost as a polynomial in `n` and
`δ = v_p(disc f)`, which requires an input-precision bound of this kind; also
Guàrdia–Montes–Nart, *Single-factor lifting and factorization of polynomials over local
fields*, J. Symbolic Comput. 47 (2012) 1318–1346, for the lifting-side precision. I can state
their results only qualitatively from memory; the exact theorem numbers, hypotheses, and the
constant `A(n)` MUST be looked up before OL2 is cited or declared. Under this project's axiom
policy OL2 is at present *literature-candidate*, not LITERATURE-AXIOM-ELIGIBLE.

## 6. Relation to the corpus; wiring observations

* Lemma C is exactly the content of the Lean-proved `tailCountBound` (`MovesX/XF7.lean`), same
  exponent `⌈(m − n·v_p(n))/(n−1)⌉`; §3 is a measure-form restatement with proof.
* Lemma A is the measure-theoretic skeleton that the corpus's `x3Density` runs through its
  interface fields (`undec_antitone` + `frac_inter_tendsto`); here it is three lines because
  `μ` is an honest measure.
* The corpus's conditional route (alignment tag: certified descents ≤ `ind(f)` ≤ `v/2`;
  weight-charge tag; per-branch detection field) is precisely a quantified refinement of
  OL1-i/OL1-ii — the same GMN skeleton, sharpened to yield rates (OL2-strength). For the LEAN
  ROW AS STATED (no rate), the OL1 route suffices; **no Markov/spectral content (the corpus's
  E0/escape kernel) is needed for M05** — E0 concerns the block-solve resummation (a different
  ledger row), not drainage.
* Wiring observation (adjudication-grade, not actioned here): Theorem E shows `env_tendsto` is
  UNCONDITIONALLY TRUE for the semantic classifier, whose ingredients (Lemmas B, C, D) are
  individually formalizable (B: resultant product formula; C: finitely many finite extensions
  of `Q_p`, no `Q̄_p` needed if one works in a splitting field of the slice polynomial;
  D: Hensel's lemma + Krasner — Mathlib coverage of Krasner to be checked). If the wiring's
  classifier were re-based to the semantic verdict (with the OM engine kept for the
  counting/series rows), the fenced row would become a theorem. That is a definition-change
  event under the statement fence — flagged for the orchestrator, with the caveat that the
  OTHER kernel rows (`count_tie`, `series_tie`, `vp_sound`) are keyed to the tree-fibering
  classifier and would need re-examination against a semantic `canonical`.

## VERDICT

**PARTIAL.** (1) PROVED here (informal-rigorous, full proofs): `env(N) → 0` with an explicit
`p`-uniform-up-to-`v_p(n)` exponential envelope, for the semantic classifier, at every prime
including wild, every degree — Lemmas A–D + Theorem E. (2) REDUCED: the obligation for the
corpus's OM classifier is equivalent (Lemma A + Prop 5.1) to OL1 = [GMN termination, (a),
pinned citation] + [finite-read certification of the canonical run at the corpus's own
classifier, corpus-specific, open]. (3) OL2 (rates for `c^OM`) stated, literature candidate
Bauch–Nart–Stainsby 2013 flagged UNVERIFIED. Nothing here is a complete proof of the Lean row
at the constructed instance; the honest distance is OL1-ii's agreement seam.

## NUMERIC-TESTS

Script: `verification/m05_exhaust_probe.py` (pure Python + sympy for the symbolic
discriminant; run under any Python with sympy ≥ 1.13). **T1, T2 were RUN (2026-07-31): all
PASS.**

* **T1 (Lemma C, exact, exhaustive).** For `(n, p)` in a 10-case grid (`n ∈ {2,3,4}`,
  `p ∈ {2,3,5,7}`), `m` up to the enumeration budget `p^{nm} ≤ ~10^6`: count
  `#{a ∈ (Z/p^m)^n : disc ≡ 0 mod p^m}` exactly and check
  `μ ≤ (n−1)·p^{−⌈(m−n·v_p(n))/(n−1)⌉}`. RESULT: 39/39 PASS; equality at every tame `n = 2`
  cell (bound tight); wild cells (`n=p=2`: μ = 2^{-m+3}·…, `n=3, p=3`, `n=4, p=2`) all inside.
  A FAIL here would refute Lemma C (and the Lean `tailCountBound` constants).
* **T2 (Theorem E envelope, exact, exhaustive).** For `(n,p) ∈ {(3,2),(2,3),(2,2),(2,5)}`,
  `N` up to budget: exact fraction `u(N)` of level-`N` classes with `disc ≡ 0 mod p^N` or
  `v(disc) ≥ ⌈N/2⌉` (= the Krasner-undecided superset of the semantic undecided set; the event
  is class-measurable since `⌈N/2⌉ ≤ N`); check `u(N)` nonincreasing and
  `≤ (n−1)p^{−⌈(⌈N/2⌉−w)/(n−1)⌉}`. RESULT: 25/25 PASS, monotone throughout, equality in the
  tight tame cells. An INCREASE would refute stability of the criterion; a bound FAIL would
  refute Theorem E's arithmetic.
* **T3 (Lemma D, sampling; PROPOSED — needs cypari2).** For `n ∈ {3,4,5}`, `p ∈ {2,3,5}`,
  ~10^3 random monic `f` with coefficients sampled to precision `2v+30` (recompute
  `v = v_p(disc f)` exactly via integer disc of a truncation; discard `v > 20`): for `K = 20`
  random monic perturbations `g = f + p^{2v+1}h` (`deg h < n`), compare
  `pari.factorpadic(f, p, prec)` and `(g, p, prec)` splitting types (`(e_i, f_i)` multisets)
  at working precision `≥ 2v + 30`. CONFIRMS Lemma D if 100% agree; ANY disagreement REFUTES
  Lemma D/Theorem E (stop-the-line). Sharpness side-probe: perturb at modulus `2v` and
  `v+1`; occasional disagreement expected (not load-bearing).
* **T4 (OL2 shape, sampling; PROPOSED).** Implement the order-≤2 canonical OM run for
  `n ≤ 4` (Newton polygon of `f`, residuals, one refinement level — sympy suffices) and
  record the max digit index `N̂(f)` it inspects before all leaves certify, vs
  `δ = v_p(disc f)`, on ~10^4 samples per `(n, p) ∈ {(3,2),(3,3),(4,2)}`. PLOT/max-ratio:
  supports OL2 if `N̂ ≤ A·δ + B` with stable small `A` (expect `A ≤ 3`); a superlinear trend
  is a FINDING against OL2's shape (qualitative OL1 unaffected).
* **T5 (rate comparison; cheap extension of T1).** Extend T1 to `m ≤ 12` at `(2, p)` via the
  `a_0`-slice structure (per tail, count `a_0` roots mod `p^m` by Hensel lifting instead of
  enumeration) and confirm the exact geometric rate `μ{v ≥ m} = p^{−m+c}` for `n = 2` — the
  regime where Theorem E's bound is achieved; documents that no better-than-`p^{−N/2}`
  envelope for the SEMANTIC classifier is possible at `n = 2` (contrast: the OM classifier's
  proved `n = 2` envelope decays like `p^{−N}` — the gap is real, not slack in E).
