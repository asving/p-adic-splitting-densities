# GMN citations — the single load-bearing external import, pinned verbatim

**Date:** 2026-06-15. **Role:** deliverable (2) of the human-proof bookkeeping. Pin the exact
theorem/definition labels of the one external reference the uniform-rationality proof depends on,
the higher-order Okutsu–Montes (OM) machinery of **Guàrdia–Montes–Nart**, and record a one-line
statement of each as we use it.

**Source verified.** The labels below were read directly from the arXiv text of the paper
(arXiv:0807.2620v2, 31 Oct 2008), extracted with `mutool draw -F txt` and grepped for the exact
section/theorem/definition numbers. Section and theorem numbers are quoted from **that arXiv
version**. The published version is:

> **J. Guàrdia, J. Montes, E. Nart**, *Newton polygons of higher order in algebraic number
> theory*, **Trans. Amer. Math. Soc. 364 (2012), no. 1, 361–416**. (arXiv:0807.2620.)
> Companion / context: J. Montes, E. Nart and collaborators, *Okutsu invariants and Newton
> polygons* and the higher-order OM algorithm papers; the tame/foundational version is the
> Montes thesis and Ore's three classical dissections.

> **HONEST CAVEAT on pagination.** The theorem/definition **numbers** below (Thm 1.15, 1.19, 2.11,
> 3.1, 3.7, 4.18; Def 1.21–1.22, 2.1, 2.3, 2.5, 2.21, 3.9, 3.10; Cor 1.20, 3.3, 3.8, 4.19; Lemma
> 3.11) are taken from **arXiv:0807.2620v2**. The TAMS published numbering is, in the experience of
> this literature, identical or near-identical, but **the printed-pagination numbers should be
> confirmed against the TAMS 364 (2012) PDF before final submission.** All statements below are
> quoted/paraphrased from the verified arXiv text, so the *mathematical content* is pinned even
> where a printed number might shift by one.

This note **corrects** the earlier guesses in `notes/BB3_infinity.md §1` and
`notes/COMPLETE_PROOF.md §12` (which cited "Def. 2.5, Thm. 2.11, Def. 2.20–2.23, Thm. 2.26"). The
order-1 theorems are **1.15 / 1.19**; the order-`r` theorems are **3.1 / 3.7**; the residual
polynomial of order `r` is **Definition 2.21** (not 2.20–2.23, though 2.20 defines the residual
*coefficient* and 2.19 the truncation). [AUDIT-FIX 2026-07-03] An earlier version of this paragraph
claimed "there is **no Theorem 2.26** in this paper" — that claim is **FALSE**. **Theorem 2.26
exists** (arXiv text, `gmn_v2.txt` line 2709): it is the **Theorem of the product in order `r`**,
stating `N_r^-(fg) = N_r^-(f) + N_r^-(g)` and `R_{λ_r}(fg)(y) = R_{λ_r}(f)(y)·R_{λ_r}(g)(y)` —
multiplicativity of the order-`r` principal polygon and residual polynomial under products. What
remains true is that Thm 2.26 is **not** the Theorem of the residual polynomial (that is Thm 3.7),
so the old pin "Def. 2.20–2.23, Thm. 2.26" for the residual-polynomial theorem was still a mis-pin;
but Thm 2.26 is a real and load-bearing-adjacent statement: it supplies the combinatorial half of
the GAP-1 descend-restart (restart-lemma) closure route (see `WILD_UNIFORMITY_VERDICT.md` and
`notes/RESTART_LEMMA.md`, being written). The propagation fix is listed in §4 below.

---

## 0. What we import, distilled to three `p`-independent structural facts

The whole uniform-rationality argument (BB3-∞ / L2core regime-1) imports from GMN **only** the
existence and behaviour of the higher-order key polynomials, used via three facts.
[AUDIT-FIX 2026-07-03: scope corrected — the earlier parenthetical "(GMN works over an arbitrary complete
discretely valued field; the wild/inseparable case is the *generic* case, not an exception)" is
FALSE as a citation. GMN fixes its scope at `gmn_v2.txt` line 482: "We fix a finite extension K of
Qp as a base field" — mixed characteristic 0, finite residue field, theorems proved **per fixed
`p`**. Our `K/ℚ_p` is finite unramified, exactly GMN's scope, so the three facts below apply per
`p`, in identical combinatorial form at every prime; the wildness we need is wild ramification
`p | e_i` in mixed char 0 — *inside* GMN's per-`p` scope — not inseparable residue fields, which
GMN never treats. The `p`-independence of the assembled volumes is **DERIVED** from the `p`-free
*shape* of the per-`p` combinatorial imports (lattice polygons, finite-field residual counts), not
imported as a DVF-uniformity theorem.]:

- **(I) Finite-field residuals at every order.** The order-`r` residual polynomial lives in
  `F_r[y]`, where `F_r` is a *finite* field with `[F_r : F_q] = f_0 f_1 ... f_{r-1} | n`. *(This is
  the linchpin: it lets the finite-field building block L3/BB3 apply verbatim at every order — finite
  fields are perfect at every `r`, so "needs descent = non-squarefree = discriminant locus" with no
  inseparable-irreducible exceptions in any characteristic.)*
- **(II) Lattice polygons at every order.** The order-`r` Newton polygon `N_r` is a principal
  polygon — a lattice object — with `p`-independent combinatorics. *(This is what L4/BB1 consumes:
  the cell volume is a characteristic-independent `q`-power.)*
- **(III) Repeated-factor descent, finite and `p`-independent.** A multiplicity-1 residual factor is
  a **leaf** (an irreducible `p`-adic factor with explicit `(e,f)`); a multiplicity-`≥2` factor
  **descends** to the next order; and the descent terminates at finite, `p`-independently-bounded
  order. *(This is what drives the recursion and its termination.)*

No uniformity, rationality, or volume statement is imported. Those are *derived* (see
`BB3_infinity.md`, `L2core_complete.md`).

---

## 1. The order-1 theorems (= classical Ore dissections; used at the base of the induction)

> **Definition 1.21 / 1.22 (types of order 0 and 1).** A *type of order zero* is a monic
> irreducible `t = ψ_0(y) ∈ F[y]` (`F = F_q` the residue field). A *type of order one* is a triple
> `t = (φ(x); λ, ψ(y))` with `φ` monic, `φ ≡` (lift of `ψ_0`), `λ ∈ Q_{<0}` a slope, and `ψ(y) ∈
> F_φ[y]` irreducible over the order-1 residue field `F_φ := F[y]/(ψ_0(y))`.
> *(One-line: the order-1 type is the slope + residual data of a Newton-polygon side.)*

> **Theorem 1.15 (Theorem of the polygon).** If `f ∈ O[x]` is `≡ φ^a (mod m)` and the `φ`-Newton
> polygon `N_φ^-(f) = S_1 + ... + S_g` has `g` sides of pairwise different slopes `λ_1,...,λ_g`,
> then `f_φ = F_1 ... F_g` factors in `O[x]` with `N_φ(F_i)` one-sided of slope `λ_i` and
> `R_{λ_i}(F_i) ∼ R_{λ_i}(f)`.
> *(One-line: distinct slopes of the Newton polygon split off coprime factors — the second
> dissection.)*

> **Theorem 1.19 (Theorem of the residual polynomial).** For a side `S` of `N_φ^-(f)` of finite
> slope `λ` with residual factorization `R_λ(f) ∼ ψ_1^{a_1} ... ψ_t^{a_t}` into pairwise-distinct
> monic irreducibles in `F_φ[y]`, the factor `f_{φ,λ}` splits as `G_1 ... G_t` with `R_λ(G_i) ∼
> ψ_i^{a_i}`.
> *(One-line: distinct residual factors split off coprime factors — the third dissection.)*

> **Corollary 1.20 (leaf dichotomy, order 1).** For a root `θ` of `G_i` and `L = K(θ)`: `f(L/K)` is
> divisible by `m·deg ψ_i`; the number of irreducible factors of `G_i` is at most `a_i`; **in
> particular, if `a_i = 1` then `G_i` is irreducible**, `f(L/K) = m·deg ψ_i`, `e(L/K) = e`.
> *(One-line: a multiplicity-1 residual factor is already an irreducible `p`-adic leaf with explicit
> `(e,f)`; multiplicity `≥ 2` is unresolved and needs refinement — this is fact (III) at order 1.)*

---

## 2. The order-`r` machinery (the genuine import — §2 constructs it, §3 proves the theorems)

### 2.1 Types, key polynomials, and the finite residue tower

> **Types of order `r-1` (§2.1, displayed before Definition 2.1).** A type
> `t = (φ_1; λ_1, φ_2; ...; λ_{r-1}, ψ_{r-1}(y))` with: `φ_1` irreducible mod `m`, `ψ_0 :=
> φ_1 mod m`, `F_1 := F[y]/(ψ_0)`; for `1 ≤ i < r-1`, `N_i(φ_{i+1})` one-sided of slope `λ_i` and
> `R_i(φ_{i+1})` irreducible `∼ ψ_i ∈ F_i[y]`, `F_{i+1} := F_i[y]/(ψ_i)`; finally `ψ_{r-1} ∈
> F_{r-1}[y]` monic irreducible `≠ y`, `F_r := F_{r-1}[y]/(ψ_{r-1})`.
> **"The type determines a tower `F = F_0 ⊆ F_1 ⊆ ... ⊆ F_r` of finite fields."** With
> `f_i := deg ψ_i`, `[F_r : F] = f_0 f_1 ... f_{r-1}`.
> *(One-line: this is FACT (I) — `F_r` is a finite field at every order, of `p`-independent degree
> `f_0...f_{r-1} | n` over `F_q`. GMN's own sentence "The field `F_i` should not be confused with the
> finite field with `i` elements" makes the finiteness explicit.)*

> **Definition 2.5 (`p`-adic valuation of order `r`).** `v_r(P) := e_{r-1} H_{r-1}(S_{r-1}(P))` — a
> discrete valuation on `K(x)^*` extending `v` with index `e_1 ... e_{r-1}`.
> *(One-line: the order-`r` valuation under which `N_r` is taken; integer-valued, `p`-independent
> denominators `e_i = b_i ≤ e`.)*

> **Theorem 2.11 (existence of a representative / key polynomial).** One can effectively construct a
> monic `φ_r(x) ∈ O[x]` of type `t` of degree `m_r = m_{r-1} e_{r-1} f_{r-1}`, with `v_r(φ_r) = V`
> and order-`r` residual `R_{r-1}(φ_r) ∼ ψ_{r-1}`. **Definition 2.12** names such a `φ_r` a
> *representative* of the type `t` — "which plays the analogous role in order `r` to that played by
> an irreducible polynomial modulo `m` in order one."
> *(One-line: the higher key polynomial `φ_r` exists and lifts the repeated residual factor — the
> object the whole tower is built on.)*

> **Definition 2.3 / Lemma 2.4 (order-`r` Newton polygon `N_r`, and `f_t`).** For `P` of type `t`
> with `ω_r(P) > 0`, `N_r(P)` is the order-`r` (`φ_r`-adic, `v_r`-) Newton polygon; the *principal
> part* `N_r^-` carries the finite slopes. `f_t` is the largest-degree factor of type `t`,
> `deg f_t = m_r ω_r(P)`. The polygon is a **principal polygon** (`PP`, Definition 1.1) — a lattice
> object over `Z × (1/(e_1...e_{r-1}))Z`.
> *(One-line: this is FACT (II) — `N_r` is a lattice polygon at every order, with `p`-independent
> combinatorics.)*

> **Definition 2.21 (residual polynomial of order `r`).** For a side `S = S_{λ_r}(N)` of slope
> `λ_r = -h_r/e_r` (lowest terms), degree `d = d(S)`, initial point `(s,u)`,
> `R_{λ_r}(f)(y) := c_s + c_{s+e_r} y + ... + c_{s+d e_r} y^d ∈ F_r[y]`, a monic (after
> normalization) degree-`d` polynomial over the **finite** order-`r` residue field `F_r`; "`c_s` and
> `c_{s+d e}` are always nonzero, so `R_{λ_r}(f)` has degree `d` and is never divisible by `y`."
> (Definition 2.20 gives the residual *coefficient* `R_i(f)` at an abscissa; Definition 2.19 the
> truncation `t_i`.)
> *(One-line: the order-`r` residual is a genuine monic degree-`d` polynomial over the finite field
> `F_r` — the object L3/BB3 counts, and the object whose Haar-equidistribution is M6.)*

### 2.2 The order-`r` theorems (§3 — "analogous in order `r` to Ore's Theorems")

GMN's own §-introduction (arXiv line 84): *"In section 3 we prove analogous in order `r` to Ore's
Theorems of the polygon and of the residual polynomial (**Theorems 3.1 and 3.7**), that provide two
more dissections for each order."*

> **Theorem 3.1 (Theorem of the polygon in order `r`).** If `ω_r(f) > 0` and `N_r^-(f) =
> S_1 + ... + S_g` has `g` sides of pairwise different slopes, then `f_t = F_1 ... F_g` with
> `N_r(F_i)` equal to `S_i` up to translation, `R_{λ_{r,i}}(F_i) ∼ R_{λ_{r,i}}(f)`, and `v(φ_r(θ))`
> explicit for any root `θ` of `F_i`.
> *(One-line: order-`r` analogue of Thm 1.15 — distinct order-`r` slopes split off coprime factors.)*

> **Corollary 3.3.** For a side of slope `λ_r = -h_r/e_r`: `f(L/K)` is divisible by
> `f_0 ... f_{r-1}`, `e(L/K)` divisible by `e_1 ... e_r`; the number of irreducible factors of
> `f_{t,λ_r}` is at most `d(S)`; **if `d(S) = 1` the factor is irreducible** with `f(L/K) =
> f_0...f_{r-1}`, `e(L/K) = e_1...e_r`.
> *(One-line: a length-1 side is a totally-ramified leaf — explicit `(e,f)`.)*

> **Theorem 3.7 (Theorem of the residual polynomial in order `r`).** For a side `S` of `N_r^-(f)` of
> finite slope `λ_r`, with `R_{λ_r}(f) ∼ ψ_{r,1}^{a_1} ... ψ_{r,t}^{a_t}` into pairwise-distinct
> monic irreducibles in `F_r[y]`, the factor `f_{t,λ_r} = G_1 ... G_t` with `N_r(G_i)` one-sided of
> slope `λ_r` and `R_{λ_r}(G_i) ∼ ψ_{r,i}^{a_i}`.
> *(One-line: order-`r` analogue of Thm 1.19 — distinct order-`r` residual factors split off coprime
> factors over the finite field `F_r`.)*

> **Corollary 3.8 (leaf dichotomy, order `r` — THE descent rule, fact (III)).** For a root `θ` of
> `G_i`, `L = K(θ)`, `f_r := deg ψ_{r,i}`: `f(L/K)` divisible by `f_0 f_1 ... f_r`; the number of
> irreducible factors of `G_i` is at most `a_i`; **in particular, if `a_i = 1` then `G_i` is
> irreducible** with `f(L/K) = f_0 f_1 ... f_r`, `e(L/K) = e_1 ... e_{r-1} e_r`.
> *(One-line: multiplicity-1 = OM leaf with explicit `(e,f) = (e_1...e_r, f_0...f_r)`; multiplicity
> `≥ 2` = unresolved, descend to order `r+1`. This is the exact "leaf vs descend" dichotomy the
> recursion uses.)*

### 2.3 Completeness, the descent trigger, and termination at finite order

> **Definition 3.9 (`f`-complete type).** A type `t` of order `r-1` is `f`-complete if `ω_r(f) = 1`;
> then `f_t` is irreducible with `(e,f)` computable from `t` by Corollary 3.8.

> **Definition 3.10 / eq. (37) (the full OM factorization).** `t_r(f)` is the set of order-`r` types
> sprouted from the non-`f`-complete `t ∈ t_{r-1}(f)` by choosing a finite slope `λ_r` of `N_r^-(f)`
> and a monic irreducible factor `ψ_r | R_{λ_r}(f)` in `F_r[y]`. Hensel + Theorems of the polygon and
> residual polynomial in orders `1,...,r` give the factorization `f = f_{r,∞} · ∏_{t ∈ T_r(f)} f_t`.

> **Lemma 3.11 (the descent trigger, verbatim equivalence).** The following are equivalent: (1)
> `t_{r+1}(f) = ∅`; (2) `t_r(f)_compl = t_r(f)`; **(3) for all `t ∈ t_{r-1}(f)` and all `λ_r`, the
> order-`r` residual polynomial `R_{λ_r}(f)(y)` is separable.**
> *(One-line: descent stops at order `r` **iff every order-`r` residual is separable** — i.e. the
> trigger for descending past order `r` is **exactly** a non-separable = repeated = non-squarefree
> residual. This is FACT (III) stated verbatim, and is precisely the locus L3/BB3 counts as
> `Q_r^{d_r-1}`.)*

> **Theorem 4.18 (Theorem of the index) + Corollary 4.19 (termination).** `ind(f) ≥
> ind_1(f) + ... + ind_r(f)`, with equality iff `ind_{r+1}(f) = 0`; consequently (Cor 4.19) **for a
> monic separable `f` there exists `r ≥ 0` with every type in `t_r(f)` `f`-complete**, i.e. the OM
> descent terminates at finite order. GMN's §-intro: "This result guarantees that the factorization
> process finishes at most in `ind(f)` steps."
> *(One-line: the descent terminates at finite, `p`-independently-bounded order — fact (III)'s
> finiteness half. Combined with defectlessness of `K/Q_p` (char 0, complete discrete) the leaf data
> are `Σ e_i f_i = [L:K]`, all defects 1 — see `L5fix_complete.md`.)*

---

## §4 index machinery — pins required for the depth⟹disc axiom (P1–P3; added 2026-07-22)

**Consumer:** `MATH_FULLTYPE_DECOMPOSITION_2026-07-22.md` Lemma 3.2 / boundary #6 — the planned
pointwise axiom **"still descending at depth `d` ⟹ `v_p(disc f) ≥ 2d`"** (the W5/W6 exhaustion
envelope). That axiom rests on exactly the three pins below, each with its verification status.

**Source status.** The old `gmn_v2.txt` extraction is no longer on this machine. For this section
the paper was **re-downloaded from arXiv (0807.2620v2) and re-extracted 2026-07-22** with
`pdftotext` (4350 lines; line numbers below refer to THIS extraction and differ from the old
mutool line numbers cited elsewhere in this file — sanity anchor: "We fix a finite extension K of
Qp" is line 381 here vs. 482 there). Every quote below was read from that text on 2026-07-22.

### (P1) `ind(f)` / `ind(N)` definitions + the lattice-point convention — **VERIFIED verbatim; the on-or-below question is RESOLVED (on-or-below)**

From §4.2 "Index of a polynomial and index of a polygon" (line 3221 ff.):

- **v-index of an irreducible `F`** (lines 3225–3227): "(OL : O[θ]) = q^{ind(F)}, for some natural
  number ind(F) that will be called the v-index of F(x). Note that ind(F) = v(OL : O[θ])/[K : Qp]."
- **Definition 4.11** (monic separable `f = F₁⋯F_k`):
  `ind(f) := Σᵢ ind(Fᵢ) + Σ_{1≤i<j≤k} v(Res(Fᵢ, Fⱼ))`.
- **Definition 4.12** (side `S` of negative slope; `E = ℓ(S)`, `H = H(S)`, `d = d(S)`):
  `ind(S) := ½(EH − E − H + d)` for finite slope, `0` for slope `−∞`. For a principal polygon
  `N = S₁ + ⋯ + S_g` (increasing slopes): `ind(N) := Σᵢ ind(Sᵢ) + Σ_{i<j} EᵢHⱼ`, an infinite side
  contributing `E_∞ · H_fin(N)`.
- **Remark 4.14 — THE CONVENTION, verbatim:** "The contribution of the sides of finite slope to
  ind(N) is the number of points of integer coordinates that lie **below or on** the finite part
  of N, **strictly above** the horizontal line L that passes through the last point of N, and
  **strictly beyond** the vertical line L′ that passes through the initial point of the finite
  part of N." Column form, eq. (40): `ind(N_fin) = ⌊y_{i₁+1}⌋ + ⋯ + ⌊y_{i₂−1}⌋` (`yᵢ` = height of
  `N` above `L` at integer abscissa `i`).

**The previously load-bearing unknown — on-or-below vs strictly-below — is hereby resolved: GMN
counts ON-OR-BELOW** (with the two strictness clauses of Remark 4.14). Cross-checks performed:

- Pick-style identity: for one side, (strictly-interior points) + (non-vertex on-side points)
  `= [(EH − E − H − d)/2 + 1] + (d − 1) = ½(EH − E − H + d)` = Def 4.12's formula — so the
  formula itself certifies that on-side points are included. ✓
- **Discriminating witness (pass-1 verifier's; recomputed here):** `f = x² + 6x + 36` over `ℤ₃`.
  First polygon `(0,2)–(2,0)` (`E = H = d = 2`, slope `−1`), residual `(y+1)²` ⟹ **one depth-1
  descend**; recentered `x² + 27` ⟹ leaf `(e,f) = (2,1)`, `L = ℚ₃(√−3)`. True index:
  `θ = −3 + 3√−3`, `O_L = ℤ₃[√−3]`, so `(O_L : ℤ₃[θ]) = 3`, `ind(f) = 1`. On-or-below count of the
  first polygon = 1 (the point `(1,1)`, which lies ON the side); strictly-below count = 0 ≠ 1.
  Def 4.12 gives `½(4−2−2+2) = 1` ✓, and the identity check `v₃(disc f) = v₃(−108) = 3 =
  2·1 + v₃(disc L/ℚ₃) = 2 + 1` ✓ (tame ramified quadratic, `v(disc) = e−1 = 1`).

### (P2) the index–discriminant identity — **GMN sentence VERIFIED verbatim; independent textbook pin TO-VERIFY**

- **Verbatim** (§4.2, line 3233): "Recall the **well-known relationship**,
  `v(disc(F)) = 2 ind(F) + v(disc(L/K))`, linking ind(F) with the discriminant of F(x) and the
  discriminant of L/K." (Irreducible case. GMN cite it as classical — a citable carrier, not the
  origin.)
- **Reducible case** (the form Lemma 3.2 of the decomposition note uses): combine the above with
  Def 4.11 and the elementary multiplicativity `disc(PQ) = disc(P)·disc(Q)·Res(P,Q)²` to get
  `v_p(disc f) = 2·ind(f) + Σᵢ v_p(disc(Lᵢ/K)) ≥ 2·ind(f)`. The multiplicativity step is
  elementary resultant algebra (provable, not an import).
- **Independent literature pin: TO-VERIFY against a printed source.** The order-index formula
  `disc(O′) = (O : O′)² · disc(O)` is standard (candidate pins: Neukirch, *Algebraic Number
  Theory*, Ch. I §2; Serre, *Local Fields*, Ch. III; Ore 1928), but **no exact
  proposition/theorem number has been verified in this session** — pin before axiom declaration.
  Meanwhile the GMN verbatim sentence above is the primary citation and suffices.

### (P3) per-descend-event increment `ind_r ≥ 1` — **mechanism VERIFIED against Defs 4.12/4.15 + Thm 4.18; declaration caveats listed**

- **Definition 4.15 (verbatim content):** `ind_t(P) := f₀⋯f_{r−1} · ind(N_r^−(P))`;
  `ind_r(P) := Σ_{t ∈ t_{r−1}(P)} ind_t(P)`. GMN note explicitly that "the value of ind_t(P)
  depends on this choice [of the representative φ_r], although this is not reflected in the
  notation."
- **The increment.** A descend event at order `r` — a side `S` of `N_r^−(f)` of finite slope
  `−h/e` carrying a residual factor `ψ^μ` with `μ ≥ 2` — forces `d = d(S) ≥ μ·deg ψ ≥ 2`. Then
  the **on-side lattice point `(s+e, u+(d−1)h)`** (`s` = initial abscissa of `S`, `u` = ordinate
  of `S`'s last point; the point one `e`-step in from the initial point) lies below-or-on `N`
  (it is ON `S`), strictly above `L` (its height above `N`'s last point is `≥ h ≥ 1` since
  `d ≥ 2`), and strictly beyond `L′` (`s + e > s ≥` initial abscissa of the finite part) — so it
  counts in `ind(N_r^−)` under (P1)'s on-or-below convention. **It would NOT count under a
  strictly-below convention — this is exactly where (P1) is load-bearing** and is the intended
  proof mechanism for the axiom. Closed-form corroboration from Def 4.12 directly:
  `EH − E − H + d = d(deh − e − h + 1) ≥ d·e(d−1) ≥ 2` for `d ≥ 2`, so `ind(S) ≥ 1`. ✓
- **Assembly into depth⟹disc.** In THIS paper's accounting every `μ ≥ 2` residual factor sprouts
  an order-`(r+1)` type (Def 3.10) — including the `deg ψ = 1, e = 1` "refinement-like" sprouts
  (later Montes-algorithm papers optimize these away; here they increment the order). A branch
  with `d` descend events therefore has events at orders `1, …, d`, each giving
  `ind_r(f) ≥ ind_t(f) ≥ f₀⋯f_{r−1}·1 ≥ 1` (all terms of `ind_r` are `≥ 0`), whence Thm 4.18(1):
  `ind(f) ≥ Σ_{r ≤ d} ind_r(f) ≥ d`; with (P2): **`v_p(disc f) ≥ 2d`**. Consistency check on the
  (P1) witness: `ind(f) = 1 = ind₁` forces `ind₂(f) = 0` (Thm 4.18) — the terminal leaf read
  contributes nothing, exactly as Lemma 4.16(1) requires. ✓
- **Declaration-time caveats** (carry into the axiom's faithfulness entry): (i) heights/abscissas
  in `ind_r` live in GMN's `v_r`-normalized coordinates (Def 2.5), NOT raw coefficient
  valuations; (ii) `ind_t` is representative-dependent (GMN's own remark) — Thm 4.18(1) holds per
  admissible choice, and the decomposition note's canonical lifts are one admissible choice
  within the "universally fixed family" that §4.2's opening sentence assumes (verbatim: "All
  types that we consider are still assumed to be made up with polynomials φi (x) belonging to a
  universally fixed family"); (iii) a ROOT cluster opening (choosing the order-0 type `ψ₀`) is
  NOT a descend event and carries no polygon side — consistent with the decomposition note's
  Def 1.3 exclusion (its `n = 2`, `p`-odd counterexample `x² − p` is recorded there).

---

## Lift/representative invariance — pin (P4) for boundary #5 (added 2026-07-22, the W5c declaration gate)

**Consumer:** `MATH_FULLTYPE_DECOMPOSITION_2026-07-22.md` Def 1.2 "Canonical lifts" paragraph /
boundary table #5 ("Lift admissibility/invariance (canonical lifts read the same tree)") and the
Wave-5c re-scope #4 of `om_leaf_faithful` (chain branch of `fiberOf5`): the recentered read
`g(y) = f(ĉp^m + p^m y)/p^{2m}` at a `deg ψ = 1`, integer-slope descend is a genuine Montes run,
for the canonical lift `ĉ` and independently of the choice of lift. This section completes the pin
that boundary #5 carried as "exact pin TBD at declaration".

**Source status.** Same extraction as (P1)–(P3): arXiv:0807.2620v2 re-extracted 2026-07-22 with
`pdftotext` (4350 lines; line numbers refer to that extraction, `/tmp/gmn_v2.txt`). Every quote
below was read from that text on 2026-07-22.

### (P4a) the order-1 theory is stated for an ARBITRARY monic lift — **VERIFIED verbatim**

§1.2 opening (line 389): the standing hypothesis under which ALL of §1 (Thm 1.15, Thm 1.19,
Cor 1.20) is developed is

> "Let φ(x) ∈ O[x] be a monic polynomial of degree m whose reduction modulo m is irreducible."

— nothing more. The recentering lift `φ = x − ĉp^m` (`m ≥ 1`) is monic of degree 1 with reduction
`x̄`, irreducible — **inside this stated scope, for EVERY choice of the lift `ĉ` of `c̃`**, and its
`φ`-adic development of `f` is the Taylor expansion at `ĉp^m`, i.e. exactly the recentered
coefficients (the note's staircase identity (2.3a) is the [COUNT] shear between the `φ`-polygon of
`f` and the plain polygon of the recentered `g`). So "the recentered read is a genuine Montes run"
is, at order 1, an INSTANCE of the paper's stated generality, not an extra import.

### (P4b) lift-dependence acknowledged, dissections valid PER CHOICE — **VERIFIED verbatim**

§1.5, the construction of `t1(f)` (lines 977–983):

> "…for any non-f-complete ψ0 (y) ∈ t0 (f ), we take a monic lift φ(x) to O[x]; then we consider
> all finite slopes λ of the sides of positive length of Nφ− (f ), and finally, for each of them we
> take the different monic irreducible factors ψ(y) of the residual polynomial Rλ (f )(y) ∈ Fφ [y].
> **These types are not intrinsical objects of f (x). There is a non-canonical choice of the lifts
> φ(x) ∈ O[x], and the data λ, ψ(y) depend on this choice.**"

followed immediately (lines 984–1003) by the factorization valid for the chosen lifts:

> "By the previous results we have a factorization in O[x] f (x) = f∞ (x) ∏_{t∈T1 (f )} ft (x) …
> Also, if a = 1, the Theorem of the residual polynomial shows that ft (x) is irreducible too."

I.e. the paper's own form of lift invariance: the intermediate DATA `(λ, ψ)` are
choice-dependent (our menu treats them as indexing, never as invariants of `f`), while EVERY
admissible choice's run yields a genuine factorization whose multiplicity-1 leaves are genuine
irreducible factors with the Cor 1.20 `(e, f)`.

### (P4c) order-`r` analogue: arbitrary representative — **VERIFIED verbatim**

Definition 2.12 (lines 1624–1626) and its sequel (lines 1632–1633):

> "Definition 2.12. A representative of the type t is a monic polynomial φr (x) ∈ O[x] of type t
> such that Rr−1 (φr )(y) ∼ ψr−1 (y). This object plays the analogous role in order r − 1 to that
> of an irreducible polynomial modulo m in order one."
>
> "From now on, we fix a representative φr (x) of t, **without necessarily assuming that it has
> been constructed by the method of Propositon 2.10** [sic]."

— all of §§2.5–3 (Thm 3.1, Thm 3.7, Cor 3.8) holds for an arbitrary representative. And the
Definition 3.10 remark (lines 2881–2883) with the Lemma 3.11 sequel (lines 2913–2915):

> "This set is not an intrinsic invariant of f (x) because it depends on the choices of the
> representatives φ1 (x), . . . , φr (x) of the truncations of t." …
> "If these conditions are satisfied, then (37) is a factorization of f (x) into the product of
> monic irreducible polynomials in O[x], and we get arithmetic information about each factor by
> Corollary 3.8."

— the same per-choice pattern at every order: type sets non-intrinsic, factorization + leaf
`(e,f)` data valid for each admissible choice of representatives. (Cross-check: (P3) already
recorded §4.2's "universally fixed family" convention and GMN's own remark that `ind_t(P)` is
representative-dependent.)

### (P4d) what the paper does NOT state — **the honest gap, and where it is closed**

The paper **nowhere states a translation-form invariance** ("the factorization type of
`f(ĉp^m + p^m y)/p^{2m}` equals that of `f`", or any statement about types of substitution
transforms `x ↦ ux + c`): a full-text search of the extraction for "translat"/"transform" finds
only POLYGON translations (lines 188, 283, 763, 2266 — `N_r(F_i)` equal to a side "up to a
translation") and Prop 3.6 (base change to an unramified extension, a different axis). Verdict on
the blueprint's clause (b): **the paper does not state it in translation form.**

Accordingly the W5c chain branch imports from GMN ONLY already-pinned §1 content applied to the
genuine recentered polynomial `g` — which is itself a genuine monic polynomial of `O[x]`, so
Cor 1.20 (ram leaf), Hensel/order-0 (inert/split leaves) apply to it VERBATIM in the final frame,
inside (P4a)'s arbitrary-lift scope — while the two remaining steps are **PROVED in Lean, not
imported** (Wave W5c, `OM/QpTypeChain.lean`):

- **the transport back**: `qpType_translate_rescale` — a `QpFactorization` of `g` induces one of
  `f` with the SAME type along `f(x) = p^{(deg g)·m}·g((x − c)/p^m)` (roots correspond by the
  affine bijection, the generated fields are literally identical, so each factor's
  `LocalFactorData` bundle transports with `eOf`/`fOf` unchanged);
- **lift-choice independence**: two lifts `ĉ, ĉ' = ĉ + pδ` of the same digit `c̃` give
  `g'(y) = g(y + δp)`, the pure-translation (`m = 0`) instance of the SAME proved lemma.

The residual imported content of the chain branch is therefore exactly: (P4a)+(P4b) scope (the
shifted-lift read is a genuine Ore/GMN order-1 read of `f`, per choice of lift) + the §1 pins of
§1 above (Thm 1.15/1.19/Cor 1.20 leaf data) + the box-level decode of truncated digit conditions
into genuine valuations (same [COUNT]-style content as prior scopes, cf.
`QpType.valuation_eq_of_zmodValuation_lt`). The axiom's docstring (scope #4) carries this gap
note verbatim-in-substance.

**Gate verdict (2026-07-22): PASS — declaration unblocked.** Status labels: (P4a)–(P4c) VERIFIED
verbatim; (P4d) records the absence of a translation-form statement and closes it with the PROVED
Lean lemma, so no unstated GMN content is imported.

---

## 3. Exactly how each GMN item is consumed (the derived/imported boundary)

| GMN item | imported fact | where consumed | what is DERIVED (not imported) |
|---|---|---|---|
| §2.1 tower, Def 2.21 | (I) `R_r ∈ F_r[y]`, `F_r` finite, `[F_r:F]=f_0..f_{r-1}|n` | BB3-∞ §3 / L3 | the count `Q_r^{d_r-1}` and fine counts `N_λ(Q_r)`, char-independent (L3 Thms A–C) |
| Def 2.3, Def 1.1 (`PP`) | (II) `N_r` a lattice/principal polygon | BB3-∞ §2 / L4 | cell volume `(1-Q^{-1})^V Q^{-A}`, `A,V` lattice data, `p`-indep (L4 / `BB1_exponent.md`) |
| Cor 1.20 / 3.8, Lemma 3.11 | (III) mult-1 = leaf `(e,f)`; mult-≥2 = descend iff non-separable | BB3-∞ §4 induction | the recursion's transition coefficients, all in `Q(q)` (BB3-∞ Prop 1) |
| Thm 2.11 / Def 2.12 | existence of key polynomial `φ_r` | BB3-∞ §4 / L2core §2 | (nothing — pure existence import) |
| Thm 4.18 / Cor 4.19 | termination at finite order | L5fix §6 | finite `p`-independent shape menu `T_n` (L5fix b) |

**The uniformity consequence is derived, not imported.** [AUDIT-FIX 2026-07-03: scope corrected —
previously "GMN gives the *combinatorial structure* of the OM tower over an arbitrary complete DVF
(so it is `p`-independent and the inseparable case is its generic case)", false as a citation.]
GMN gives the *combinatorial structure* of the OM tower over a fixed finite extension `K/ℚ_p`
(`gmn_v2.txt:482`) — **per fixed `p`**, with wild ramification `p | e_i` inside that scope. Our
contribution is to read its three structural facts through the volume-only building blocks L3
(finite-field counts) and L4 (lattice `q`-powers), observe that the resulting combinatorial data
have the same `p`-free form at every prime, and conclude — DERIVED, not imported — that every
per-shape cluster volume is a uniform rational function of `q` — see `BB3_infinity.md`.

---

## 4. Propagation fix (numbers to correct in the agent files)

The following files currently print the **guessed** GMN labels "Def. 2.5, Thm. 2.11, Def. 2.20–2.23,
Thm. 2.26" or "GMN §2–3, Theorem of the Polygon / Residual Polynomial". They should be updated to the
**verified** labels:

- `notes/BB3_infinity.md §1` and §8 ledger: replace "(GMN-Polygon) [Def. 2.5, Thm. 2.11]" and
  "(GMN-Residual) [Def. 2.20–2.23, Thm. 2.26]" by **order 1: Thm 1.15 / 1.19; order `r`: Thm 3.1 /
  3.7; residual poly Def 2.21; key polynomial Thm 2.11 / Def 2.12; leaf dichotomy Cor 1.20 / 3.8;
  descent trigger Lemma 3.11(3); termination Thm 4.18 / Cor 4.19.**
- `notes/L2core_complete.md §2a`: same replacement.
- `notes/COMPLETE_PROOF.md §12` and §5/§7: same replacement.

The mathematical content was correctly described in all of these; only the printed theorem numbers
were guessed. With this note the numbers are pinned to arXiv:0807.2620v2 (printed-pagination caveat
in the header).

---

## 5. One-line summary of the import

> **We import from Guàrdia–Montes–Nart (TAMS 364 (2012); arXiv:0807.2620v2) exactly: that the OM
> descent of a separable `f` over a finite extension `K/ℚ_p` (GMN's actual scope, `gmn_v2.txt:482`)
> is a finite tower of order-`r` types, each carrying
> a lattice Newton polygon `N_r` (Def 2.3) and a residual polynomial `R_{λ_r}(f) ∈ F_r[y]` over a
> finite field `F_r` (Def 2.21; §2.1 tower), governed by the Theorems of the polygon and residual
> polynomial in order `r` (Thm 3.1, 3.7), with the multiplicity-1 = leaf / multiplicity-≥2 = descend
> dichotomy (Cor 3.8) triggered exactly by a non-separable residual (Lemma 3.11(3)) and terminating
> at finite order (Thm 4.18, Cor 4.19). [AUDIT-FIX 2026-07-03: scope corrected — previously "All of
> this is `p`-independent and treats the wild inseparable case as generic", false as a citation.]
> All of this holds **per fixed `p`**, with wild ramification `p | e_i` an ordinary case inside
> GMN's scope; the `p`-independence of the assembled volumes — and that the resulting per-shape
> volumes are uniform rational functions of `q` — is derived, not imported.**
