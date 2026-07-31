# M05-exhaust — problem brief (neutral, self-contained)

**Obligation ID:** M05-exhaust. **Lean site:** `LeanUrat.MovesU.BridgeKernels.env_tendsto`
(`lean/LeanUrat/MovesU/BridgeKernels.lean:230`), with a second instance-level appearance as the
hypothesis `hExhaust` of `LeanUrat.OM.RealInstanceV2.montes_unconditional_exhaustive`
(`lean/LeanUrat/OM/RealInstanceV2.lean:441`). Status in the project: **fenced open mathematics**
(the one analytic obligation of the formalization that is not an algebraic identity or a seam).

This brief is written for a reader who knows p-adic fields, Newton polygons,
MacLane/Okutsu–Montes (OM) theory, and Igusa-style p-adic integration, but knows none of this
project's internal names. Every internal name that appears is re-expanded here.

---

## 1. The setting

Fix a prime `p` and an integer `n ≥ 1`. Identify the space of monic degree-`n` polynomials over
the p-adic integers with the coefficient space

    Z_p^n  ∋  a = (a_0, …, a_{n-1})  ↔  f_a(x) = x^n + a_{n-1} x^{n-1} + … + a_1 x + a_0 ,

carrying the Haar probability measure `μ` (product of the normalized Haar measures on `Z_p`).

**Splitting type.** For a monic `f ∈ Z_p[x]` of degree `n` that is *separable* (i.e.
`disc f ≠ 0`; over `Q_p`, char 0, this means squarefree over `Q_p`), write its factorization
into distinct monic irreducibles over `Q_p` as `f = g_1 ⋯ g_r` (all `g_i ∈ Z_p[x]` by Gauss),
and let `e_i`, `f_i` be the ramification index and residue degree of the local field
`Q_p[x]/(g_i)`. The **splitting type** of `f` is the multiset

    σ(f) = {(e_1, f_1), …, (e_r, f_r)},   with  Σ_i e_i f_i = n.

(The Lean type `SplittingType n` is exactly: a multiset of pairs `(e, f)` of positive integers
with `Σ e·f = n`.)

**Level-N boxes and classifiers.** The *level-N box* is `(Z/p^N)^n` — the reductions of the
coefficient vectors mod `p^N`; each class ("box point") has `μ`-mass `p^{-nN}`. A **classifier**
is a family of maps

    c_N : (Z/p^N)^n → SplittingType(n) ∪ {⊥}     (N = 0, 1, 2, …)

(`⊥` = "undecided") satisfying **stability**: if `c_N(a mod p^N) = σ ≠ ⊥` and `N ≤ N'`, then
`c_{N'}(a mod p^{N'}) = σ`. In Lean this is the structure

```lean
structure ClassifierSpec (n p : ℕ) where
  canonical : ∀ N : ℕ, Box p n N → Option (SplittingType n)   -- Box p n N := Fin n → ZMod (p^N)
  trueType  : ∀ N : ℕ, Box p n N → Option (SplittingType n)
  canonical_stable : ∀ {N N'} (h : N ≤ N') (f : Box p n N') (σ : SplittingType n),
    canonical N (boxProj p n h f) = some σ → canonical N' f = some σ
  baseSection : BaseSection
```

with the derived quantities (Lean `ClassifierSpec.undec`, `ClassifierSpec.env`)

    undec(N) := #{ x ∈ (Z/p^N)^n : c_N(x) = ⊥ },      env(N) := undec(N) / p^{nN}.

`env(N)` is exactly the `μ`-measure of the union of the undecided level-`N` cylinders.

## 2. The obligation

**Statement (M05-exhaust).** *For the classifier described in §3 (the canonical
Okutsu–Montes classifier), at every prime `p` — including the wild primes `p ≤ n`, in
particular `p | n` — and every degree `n`:*

    env(N) → 0   as   N → ∞.

The Lean form is the field (quoted verbatim; `X : ClassifierSpec n p` is the classifier the
final wiring instantiates, and `𝓝 0` is the neighborhood filter of `0` in `ℝ`):

```lean
  /-- CL-4's OPERATIVE TRACE (`CapstoneLedger.cl4_env_tendsto`'s supply): the
      undecided envelope vanishes.  This is hExhaust AT GENERAL n — FENCED MATH … -/
  env_tendsto : Tendsto X.env atTop (𝓝 0)
```

Note the conclusion is a bare limit — **no rate is demanded**. (The proved `n = 2` case, §4,
happens to give an explicit envelope; matching that shape at general `n` is valuable but not
required by the Lean row.)

## 3. The classifier being quantified over (the intended instance)

The Lean row binds an abstract `ClassifierSpec`; it is a named hypothesis ("open kernel") of a
hypothesis pack, to be supplied at the final wiring where `X` is the project's constructed
classifier. That constructed classifier is, mathematically, the **canonical OM classifier**:

Fix a deterministic choice policy for the MacLane–Okutsu–Montes factorization procedure (a
canonical rule for choosing lifts/representatives, so the run is a *function* of `f`, with the
residue-digit convention fixed — the project pins Teichmüller-style base sections). For monic
`f ∈ Z_p[x]` of degree `n` the procedure builds the usual OM tree:

* order 0: factor `f mod p` over `F_p` into irreducibles; one branch per irreducible factor;
* at a node (a "type": a tower of augmented valuations with key polynomials `φ_1, …, φ_r` and
  residual data over a finite residue tower): compute the Newton polygon of the `φ_r`-adic
  expansion of `f` with respect to the node's valuation; for each side, compute the residual
  polynomial over the node's finite residue field and factor it; a residual factor of
  multiplicity one **certifies a leaf** — an irreducible factor of `f` over `Q_p` whose
  ramification index `e` and residue degree `f` are read off the accumulated type data;
  otherwise the procedure branches/refines and recurses.

When every branch ends in a certified leaf, the multiset of leaf data is `σ(f)`.

**Level-N decidedness (the definition that makes `c_N` a function on the box).** `c_N(x) = σ`
iff for one — equivalently every — lift `f` of the class `x`, the run certifies completely
and *every p-adic digit it inspects lies among the first `N` digits of the coefficients*
(each "inspection" is a valuation comparison or a residue read of a `Z`-polynomial in the
coefficients, so each is witnessed by a finite digit window; the requirement is that all
windows fit below level `N`). Then the run — hence the verdict — is identical for every lift
of `x`, so `c_N` is well defined on classes, and stability holds by construction. If the run
does not certify within the window, `c_N(x) = ⊥`.

A proof should target this classifier (or state precisely which properties of the classifier
it uses); it will be consumed through an agreement seam against the Lean construction, so a
clean interface — "any classifier satisfying properties (…) has env → 0" plus "the OM
classifier satisfies (…)" — is the most useful deliverable shape.

## 4. What is already proved in the corpus

* **`n = 2`, every prime `p` (wild `p = 2` included), machine-checked, Lean-core:**
  `LeanUrat.OM.UniformCapstone.hExhaustP` — for the concrete `n = 2` OM digit-stratum model,
  `undecided(N)/p^{2N} ≤ (⌊N/2⌋ + 1) · p^{-(N-1)}` for all `N ≥ 1`
  (`undecided_envelopeP`), hence `→ 0`. The proof is pure counting over the model's stratum
  tree (folded per-step weights; no axiom).
* **General `n`, conditional, machine-checked (the `MovesX` corpus, sorry-free):** over an
  interface carrying, per prime, a rooted stratum-tree presentation of the classifier's run
  (finite children menus, per-branch histories with node data (e, h, ℓ, …)), a
  "detection" vocabulary (each leaf branch is detected at level `threshold + cap` — a
  per-branch finite-level detection field), a finitely-additive normalized box content with
  monotone convergence along the decreasing undecided sets, and a level-`D` discriminant-tail
  field, the following are **theorems**:
  - `x3Density`: given (i) an *alignment* hypothesis — along any stratum history of `f`, the
    number of certified descent steps is at most a GMN-index-type invariant `ind(f)` with
    `2·ind(f) ≤ v_p(disc f)` — and (ii) a *weight-charge* hypothesis — the recentering-type
    steps along a history number at most `s(n)·v_p(disc f)` — and (iii) a *null-track*
    hypothesis — a countable family of exceptional fibers, each of content zero, covers the
    branches carrying "non-standard" nodes — the undecided content tends to `0` at every prime.
  - `envelopeExp`: with further progress/cap/tail hypotheses, the decay is exponential:
    `∃ N₀ c₃ c₄ (functions of n and the constants only), ∀ p, ∀ N ≥ N₀: content(Undec N) ≤
    c₃ · p^{-c₄ N}`.
  These reduce M05 to the named hypotheses; the hypotheses themselves are open at general `n`.
* **Unconditional discriminant tail, machine-checked:** `MovesX.XF7.tailCountBound` — with
  `tailCount p n D := #{a ∈ (Z/p^D)^n : disc(f_a) ≡ 0 mod p^D}` and
  `tailExp := ⌈(D − n·v_p(n))/(n−1)⌉`,
  `tailCount · p^{tailExp} ≤ (n−1) · p^{nD}`, i.e. `μ{ p^D | disc } ≤ (n−1)·p^{−tailExp}`.
* **Bracket consumption:** `montes_unconditional_exhaustive` (the `n = 2`-instance capstone)
  shows how `hExhaust` is consumed: with the undecided mass vanishing, the decided-limit
  density is the unique value in the bracket `[decided, decided + undecided]`, i.e. the
  decided-stratum density equals the full density. The general-`n` Theorem-U wiring consumes
  `env_tendsto` the same way (ledger row CL-4).

The `n = 2` discharge of the general row through an agreement seam is scoped in the corpus as
an *optional* unit; the general-`n` row is the open item.

## 5. What a proof must deliver

1. **Primary:** a rigorous proof, for the classifier of §3, that `env(N) → 0` for every prime
   `p` and every `n` — the qualitative limit suffices. Every hypothesis used about the
   classifier must be stated explicitly (they become interface obligations at the wiring).
2. **Acceptable alternative shapes:** a reduction to precisely stated open lemmas about the OM
   algorithm (each self-contained, with the reduction proved); or an exact literature
   identification (source, theorem number, hypotheses, and a faithfulness analysis against §2's
   statement — in particular: does the cited statement cover wild `p`, and does it bound the
   *classifier's certification level*, not merely assert that the true type is determined by
   finitely many digits? Those are different statements: §3's classifier must *certify from the
   window*, and the obligation is about its undecided mass, not about abstract determinacy).
3. **Valuable extras (not required):** an explicit envelope `env(N) ≤ C(n) · N^{k} · p^{-c(n)N}`
   matching the proved `n = 2` shape; uniformity of constants in `p`.

Degenerate corners a proof may dispose of trivially but must not ignore: `n ≤ 1` (the type is
forced); non-separable `f` (`disc f = 0`; the classifier never needs to decide these); `N = 0`
(the level-0 box is a point; the classifier is undecided there for `n ≥ 1`).
