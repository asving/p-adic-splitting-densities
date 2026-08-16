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

> **~~HONEST CAVEAT on pagination~~ — DISCHARGED [verified: A-3, 2026-08-16]**
> (`docs/CITE_NUMBERING_AUDIT_2026-08-16.md` §5). The numbers below (Thm 1.15, 1.19, 2.11, 3.1,
> 3.7, 4.18; Def 1.21–1.22, 2.1, 2.3, 2.5, 2.21, 3.9, 3.10; Cor 1.20, 3.3, 3.8, 4.19; Lemma 3.11)
> were read from **arXiv:0807.2620v2**; **every one of them has now been confirmed against the
> printed TAMS pages**, read this session from the free AMS PDF
> (`ams.org/journals/tran/2012-364-01/S0002-9947-2011-05442-5/`, header *"Volume 364, Number 1,
> January 2012, Pages 361–416, S 0002-9947(2011)05442-5, Article electronically published on May
> 18, 2011"*), with the claimed kind (Theorem/Definition/Corollary/Lemma) and content in each case.
> Spot-checks of arXiv v2 against print (1.15, 2.20, 2.21, 2.26, 4.8, 4.18) found **no drift at
> all**: GMN is the one source in the audit whose arXiv and printed numbering agree. Printed Def
> 2.21 is confirmed as the block defining both the virtual factor and the order-`r` residual
> polynomial `R_{λ_r}(f)(y)`. No number below needs to change.

This note **corrects** the earlier guesses in `notes/BB3_infinity.md §1` and
`notes/COMPLETE_PROOF.md §12` (which cited "Def. 2.5, Thm. 2.11, Def. 2.20–2.23, Thm. 2.26"). The
order-1 theorems are **1.15 / 1.19**; the order-`r` theorems are **3.1 / 3.7**; the residual
polynomial of order `r` is **Definition 2.21** (not 2.20–2.23, though 2.20 defines the residual
*coefficient*, and 2.19 defines the initial abscissas `s_j(P)` and the integer `t_{r−1}(i)` —
**A-3 2026-08-16:** the earlier gloss "2.19 the truncation" is not what printed 2.19 states);
~~there is **no Theorem 2.26** in this paper~~ — **CORRECTED [A-3, 2026-08-16]: Theorem 2.26 DOES
exist**, in both printed TAMS and arXiv v2, as the **Theorem of the product in order `r`**
(*"`N⁻_r(fg) = N⁻_r(f) + N⁻_r(g)`, `R_{λ_r}(fg)(y) = R_{λ_r}(f)(y)R_{λ_r}(g)(y)`"*). The
substantive correction stands unchanged — the order-`r` **theorems of the polygon and of the
residual polynomial** are **3.1** and **3.7**, so the old `BB3_infinity.md` / `COMPLETE_PROOF.md`
cite of "Thm 2.26" was aimed at the wrong statement — but it was aimed at a real one, and any
future reader chasing 2.26 will find the order-`r` product theorem. The propagation fix is listed
in §4 below.

---

## 0. What we import, distilled to three `p`-independent structural facts

The whole uniform-rationality argument (BB3-∞ / L2core regime-1) imports from GMN **only** the
existence and behaviour of the higher-order key polynomials, used via three facts, each
characteristic-independent (GMN works over an arbitrary complete discretely valued field; the
wild/inseparable case is the *generic* case, not an exception):

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

## 3. Exactly how each GMN item is consumed (the derived/imported boundary)

| GMN item | imported fact | where consumed | what is DERIVED (not imported) |
|---|---|---|---|
| §2.1 tower, Def 2.21 | (I) `R_r ∈ F_r[y]`, `F_r` finite, `[F_r:F]=f_0..f_{r-1}|n` | BB3-∞ §3 / L3 | the count `Q_r^{d_r-1}` and fine counts `N_λ(Q_r)`, char-independent (L3 Thms A–C) |
| Def 2.3, Def 1.1 (`PP`) | (II) `N_r` a lattice/principal polygon | BB3-∞ §2 / L4 | cell volume `(1-Q^{-1})^V Q^{-A}`, `A,V` lattice data, `p`-indep (L4 / `BB1_exponent.md`) |
| Cor 1.20 / 3.8, Lemma 3.11 | (III) mult-1 = leaf `(e,f)`; mult-≥2 = descend iff non-separable | BB3-∞ §4 induction | the recursion's transition coefficients, all in `Q(q)` (BB3-∞ Prop 1) |
| Thm 2.11 / Def 2.12 | existence of key polynomial `φ_r` | BB3-∞ §4 / L2core §2 | (nothing — pure existence import) |
| Thm 4.18 / Cor 4.19 | termination at finite order | L5fix §6 | finite `p`-independent shape menu `T_n` (L5fix b) |

**The uniformity consequence is derived, not imported.** GMN gives the *combinatorial structure* of
the OM tower over an arbitrary complete DVF (so it is `p`-independent and the inseparable case is its
generic case). Our contribution is to read its three structural facts through the volume-only
building blocks L3 (finite-field counts) and L4 (lattice `q`-powers) and conclude that every
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
> descent of a separable `f` over a complete DVF is a finite tower of order-`r` types, each carrying
> a lattice Newton polygon `N_r` (Def 2.3) and a residual polynomial `R_{λ_r}(f) ∈ F_r[y]` over a
> finite field `F_r` (Def 2.21; §2.1 tower), governed by the Theorems of the polygon and residual
> polynomial in order `r` (Thm 3.1, 3.7), with the multiplicity-1 = leaf / multiplicity-≥2 = descend
> dichotomy (Cor 3.8) triggered exactly by a non-separable residual (Lemma 3.11(3)) and terminating
> at finite order (Thm 4.18, Cor 4.19). All of this is `p`-independent and treats the wild
> inseparable case as generic. Everything else — that the resulting per-shape volumes are uniform
> rational functions of `q` — is derived.**

---

## 6. LITUNIT 2026-08-01 appendix — the GD23 flag pins + two superseding corrections

*(Appended by the literature unit for the GD23 brief; full quotes and verdicts in
`lean/notes/openmath/LITUNIT_2026-08-01.md`. Line numbers cite the 2026-07-22-compatible
pdftotext extraction of arXiv:0807.2620v2 — 4350 lines, anchor "We fix a finite extension K of
Qp" at line 381.)*

### 6.0 Two superseding corrections to THIS file (this copy had missed the 2026-07-03 audit-fix)

1. **Theorem 2.26 EXISTS** — the header paragraph above ("there is **no Theorem 2.26** in this
   paper") is FALSE and was corrected on 2026-07-03 in `lean/notes/GMN_citations.md`; this
   `docs/` copy had diverged. Re-verified 2026-08-01 (gmn.txt:2122), verbatim: **Theorem 2.26
   (Theorem of the product in order r).** "For any nonzero f(x), g(x) ∈ O[x] and any negative
   rational number λ_r we have N_r^−(fg) = N_r^−(f) + N_r^−(g),
   R_{λ_r}(fg)(y) = R_{λ_r}(f)(y)R_{λ_r}(g)(y)." (What stays true: Thm 2.26 is not the Theorem
   of the residual polynomial — that is Thm 3.7.)
2. **GMN's scope is a fixed finite extension K/ℚ_p** (gmn.txt:381), NOT "an arbitrary complete
   DVF" as §0/§3/§5 above say — same 2026-07-03 audit-fix, same divergence. The p-independence
   of the assembled volumes is DERIVED from the p-free shape of the per-p imports, not imported.

### 6.1 New verbatim pins (the GD23 T-1/T-2 flags, now discharged)

> **Proposition 2.7** (gmn.txt:1204). For nonzero P(x) ∈ O[x]:
> (1) v_r(P) ≥ e_{r−1}v_{r−1}(P), equality iff ω_{r−1}(P) = 0;
> (3) if P = Σ_i a_i φ_{r−1}^i is the φ_{r−1}-adic development, then
> v_r(P) = min_i{v_r(a_i φ_{r−1}^i)} = e_{r−1} min_i{v_{r−1}(a_i) + i(v_{r−1}(φ_{r−1}) + |λ_{r−1}|)};
> (4) v_r(φ_{r−1}) = e_{r−1}v_{r−1}(φ_{r−1}) + h_{r−1}.
> *(= the GD23 flag **T-1**, with Lemma 2.2(2) "deg P < m_r ⟹ ω_r(P) = 0" supplying the
> deg b < deg φ_{r−1} form. Also the sharp home of the (P-key)/(L4) pin: it is displayed as
> Prop 2.7(4), not merely inside Prop 2.15's proof.)*

> **Lemma 2.17** (gmn.txt:1795). (1) min_{0≤i≤n}{u_i} = v_r(f), n := ℓ(N_r(f)) = ⌊deg f/m_r⌋;
> (2) the length of N_r^−(f) is ω_r(f); (3) the side of slope −∞ of N_r^−(f) has length
> ord_{φ_r}(f). With: **ω_{i+1}(P) := ord_{ψ_i}(R_i(P))** (§2.1 displayed definition,
> gmn.txt:1093) and **Definition 1.8** ("principal φ-polygon … including the side of slope −∞",
> gmn.txt:427). *(= the GD23 flag **T-2**; the proof identifies ω_r(f) as the LEAST abscissa
> attaining the min — the first-attainment form WGEO(b) consumes.)*

### 6.2 Companion-source pins recorded by the same unit (full quotes in the LITUNIT note)

* **MacLane 1936** (Trans. AMS 40, 363–395; Ford re-typeset PDF): Part I §§2–6 standing scope =
  "any field K", any real non-archimedean value; discreteness assumed ONLY in §§7/8/16. Def 4.1
  (key polynomials: equivalence-irreducibility, minimal degree, monic) + Thm 4.2 (augmented
  values are values) quoted verbatim — the (V1)/ML-scope flags CLEARED, Vaquié fallback
  unnecessary. Residue-ring structure (the (GR-B) MacLane half): Thm 10.2, Lemma 10.1, Lemmas
  11.1–11.2, **Thm 12.1** (Δ_t ≅ F_t[y] for commensurable inductive values), Cor 12.2.
* **FGMN = Fernández–Guàrdia–Montes–Nart, J. Algebra 427 (2015) 30–75 = arXiv:1305.0775**,
  scope "Let K be a field equipped with a discrete valuation v" (arbitrary; no completeness for
  the pinned statements): Thm 4.2 (H_µ(g) = ϕ_r(g)·R_r(g)(y_r) — initial form = unit monomial ×
  residual), Cor 4.4, **Thm 4.8** (∆(µ) = F_r[y_r]), Cor 4.9, Cor 5.6 (R_i(φ_{i+1}) = ψ_i),
  **Prop 5.14/Cor 5.15** (ord_ψ(R_r(g)) = ord_{µ,φ}(g) for proper keys — (GR-B) clause (4)
  faithfulness EXISTS in print), Thm 5.8 (KP(µ)/∼ ↔ Max ∆). GD23 §10 attack items (5)/(6):
  RESOLVED.
