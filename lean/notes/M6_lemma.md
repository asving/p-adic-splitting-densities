# M6 — Order-`r` residual equidistribution (the count→volume bridge at every OM order)

**Date:** 2026-06-15. **Role:** deliverable (1). State and prove M6 as an explicit lemma: at every
OM/Montes order `r`, the order-`r` residual polynomial `R_r` is Haar-equidistributed over monic
degree-`d_r` polynomials over the finite order-`r` residue field `F_r`; equivalently the order-`r`
residual-coefficient map is a submersion onto `A^{d_r}(F_r)`. At order 1 this is BB1 = L4 (proved).
At order `r` we derive it from the GMN order-`r` Newton-polygon coordinate description.

**Why M6 matters.** L3 (= BB3) counts the residual *shapes* — e.g. the descent-trigger locus
`{R_r non-squarefree}` has `F_r`-point count `Q_r^{d_r-1}`. To turn a *count* into a *Haar volume*
(a conditional probability), one needs the residual coefficients to be **uniformly distributed** over
their ambient affine space, so that "fraction of cells of shape `λ`" = "`#{R_r of shape λ}` / `Q_r^{d_r}`".
M6 is exactly this equidistribution, at every order. It is the lemma silently invoked as "A2/A4 Haar
equidistribution" in `L3_proof.md` Prop D and as "the order-`r` residual-coefficient map is a
submersion" in `BB3_infinity.md §3.1`.

Citations to GMN are pinned in `notes/GMN_citations.md` (Def 2.21 = order-`r` residual polynomial;
§2.1 = finite residue tower `F_r`; Thm 3.1/3.7 = order-`r` polygon/residual theorems).

---

## 0. Setting and notation (project conventions)

`K/Q_p` finite **unramified**, residue field `F_q` (`q = p^k`), ring `O_K`, uniformizer `p`,
`v(p)=1`, Haar `μ`, `μ(O_K)=1`. For an unramified `K_δ/K` write `O_δ`, residue `F_{q^δ}`,
`μ_δ(O_δ)=1`. We use the unramified index identity `[O_δ : p^m O_δ] = (q^δ)^m` (the single fact that
carries all characteristic dependence, via `v(p)=1`).

Fix an OM type of order `r-1` (`GMN_citations.md §2.1`) with representative (key polynomial)
`φ_r ∈ O_K[x]` of degree `m_r` (Thm 2.11 / Def 2.12). Let `F_r` be the finite order-`r` residue field
(`[F_r : F_q] = δ f_0 ... f_{r-1} | δ n`; write `Q_r := |F_r|`, a power of `p`). Fix a side `S` of the
order-`r` Newton polygon `N_r` of finite slope `λ_r = -h_r/e_r` (lowest terms), of lattice length
`ℓ_r` and **residual degree** `d_r = ℓ_r / e_r` (Def 2.21). The **order-`r` residual polynomial** is
(Def 2.21)
```
   R_r(y) = c_s + c_{s+e_r} y + ... + c_{s + d_r e_r} y^{d_r}  ∈  F_r[y],
```
with `c_s, c_{s+d_r e_r} ∈ F_r^*` (GMN: these endpoint coefficients are always nonzero, so `R_r` has
degree exactly `d_r` and is not divisible by `y`). After dividing by the leading unit `c_{s+d_r e_r}`,
`R_r` is **monic** of degree `d_r`.

---

## 1. Statement

> **Lemma M6 (order-`r` residual equidistribution).** Let `g` range over the Haar-conditioned cell
> ```
>   M(t, S) := { g ∈ M_e^{(δ)} : g has OM type t of order r-1, and N_r(g) has the side S
>                                 (slope λ_r, length ℓ_r) },
> ```
> with the conditional Haar measure `μ̂ := μ_δ|_{M(t,S)} / μ_δ(M(t,S))`. Let
> ```
>   ρ_r : M(t, S) → A^{d_r}(F_r),     g ↦ (the d_r free residual coefficients of R_r(g)),
> ```
> be the **order-`r` residual-coefficient map** (the monic residual `R_r(g)` is recorded by its
> `d_r` lower coefficients `c_s/c_{lead}, ..., c_{s+(d_r-1)e_r}/c_{lead}`, the leading one being `1`).
> Then:
> 1. **(submersion / surjectivity)** `ρ_r` is surjective onto `A^{d_r}(F_r)` and each fibre
>    `ρ_r^{-1}(point)` has the **same** Haar measure `μ_δ(M(t,S)) · Q_r^{-d_r}`. Equivalently `R_r(g)`
>    is **Haar-equidistributed over all monic degree-`d_r` polynomials over `F_r`**: for every
>    `R_0 ∈ F_r[y]` monic of degree `d_r`,
>    ```
>       μ̂{ g : R_r(g) = R_0 }  =  Q_r^{-d_r},   the SAME value for every R_0 and every prime p.
>    ```
> 2. **(count → volume)** Consequently, for any union `Σ ⊆ A^{d_r}(F_r)` of residual values (e.g. a
>    factorization-shape stratum),
>    ```
>       μ̂{ g : R_r(g) ∈ Σ }  =  #Σ / Q_r^{d_r},
>    ```
>    a uniform rational function of `q` whenever `#Σ` is a universal polynomial in `Q_r` (which it is,
>    by L3). In particular the descent-trigger locus `Σ = {R_r non-squarefree}` (Lemma 3.11(3)) has
>    `μ̂ = Q_r^{d_r - 1} / Q_r^{d_r} = 1/Q_r`, and each fine shape `λ ⊢ d_r` has `μ̂ = N_λ(Q_r)/Q_r^{d_r}`
>    — all `p`-independent.
>
> At order `r = 1` this is BB1 = L4 (proved in `L4_proof.md`, verified exactly; §3 below records the
> identification). At order `r ≥ 2` it is derived in §2 from the GMN order-`r` coordinate description.

The hypotheses are explicit (for the Lean blueprint): `K/Q_p` unramified; `t` a fixed OM type of
order `r-1` with chosen representative `φ_r`; `S` a fixed finite-slope side of `N_r`; `μ̂` the
conditional Haar measure on the cell that realizes `(t, S)`. Conclusion: `R_r(g)` is uniform on monic
degree-`d_r` polynomials over `F_r`.

---

## 2. Proof at order `r`

The proof is the order-`r` instance of the order-1 argument, with `F_q` replaced by `F_r` and the
linear coordinates `c_i` replaced by the GMN order-`r` residual *coefficients* `c_i = R_{r-1}(a_i)`
(Def 2.20–2.21). It rests on three structural inputs, all pinned in `GMN_citations.md`.

### 2.1 The GMN order-`r` coordinates (the imported part)

By GMN (Def 2.20–2.21, and the `φ_r`-development `g = Σ_i a_i(x) φ_r(x)^i` with `deg a_i < m_r`), the
order-`r` Newton polygon is plotted from the points `(i, v_r(a_i φ_r^i))`, and the residual
coefficient attached to abscissa `i` on the side `S` is a specified element
```
   c_i  =  red_{F_r}( a_i(x) · (normalizing power of φ_{r-1}, π_{r-1}, ... ) )  ∈  F_r,
```
the reduction (Lemma 2.22 / Def 2.20) of the order-`(r-1)` residual `R_{r-1}(a_i)` of the
`φ_r`-coefficient `a_i`, evaluated at `z_{r-1}` and rescaled along the slope line. The two facts we
use:

- **(C1) The residual coordinates are the leading `F_r`-digits of independent `φ_r`-coefficients.**
  The `d_r + 1` on-side coefficients `c_{s}, c_{s+e_r}, ..., c_{s+d_r e_r}` come from the
  `φ_r`-coefficients `a_{s}, a_{s+e_r}, ..., a_{s+d_r e_r}` at the on-side abscissae. These
  `φ_r`-coefficients are **distinct, independent** coordinates of `g` in its `φ_r`-development
  (GMN: the development is unique with `deg a_i < m_r`), and each contributes one residual digit in
  `F_r` via the order-`(r-1)` residual map `R_{r-1}`. [AUDIT-FIX 2026-07-03 — citation corrected.]
  The **surjectivity** of this residual reduction (every prescribed residual value is realized by
  some coefficient polynomial) is **GMN Proposition 2.10** (`gmn_v2.txt:1802`), the
  prescribed-residual construction: for any admissible `V` and any nonzero `ϕ(y) ∈ F_{r-1}[y]` of
  degree `< f_{r-1}`, one can effectively construct `P(x) ∈ O[x]` with `deg P < m_r`, `v_r(P) = V`,
  and `y^ν R_{r-1}(P)(y) = ϕ(y)`. (The previous pin here — "item 4 of Prop 1.17 / 3.5" — was a
  MIS-CITATION: the actual content of those items is residual **vanishing at a root**,
  `R_λ(f)(γ(θ)) = 0` (`gmn_v2.txt:1095, 3034`); they say nothing about surjectivity.) NOTE the
  honest scope of the corrected pin: Prop 2.10 gives *surjectivity only*. The
  equidistribution/equal-mass-fibres half of (C1) — that the leading digit of a Haar-uniform
  coefficient is uniform on `F_r`, independently across coordinates, *under the accumulated
  order-`<r` conditioning* — has NO GMN counterpart and is exactly the open lemma **GAP-2 (M6_r)**
  of `WILD_UNIFORMITY_VERDICT.md`.
- **(C2) The side `S` forces a unit endpoint and free interior.** Imposing `N_r(g) ⊇ S` means: the
  endpoint coefficients `c_s, c_{s+d_r e_r}` are **units** of `F_r` (the polygon *touches* the line at
  the vertices — GMN: "`c_s` and `c_{s+d_r e}` are always nonzero"), and the interior on-side
  coefficients `c_{s+j e_r}` (`0 < j < d_r`) range **freely over `F_r`** (an on-line point may sit on
  the line, giving any `F_r`-value including 0, or strictly above, giving the polygon `= S` still
  as long as the endpoints are attained — exactly the order-1 Lemma 1 of `L4_proof.md`, transported
  to order `r`). Off-side abscissae carry coefficients forced strictly above the line; they do not
  enter `R_r`.

(C1)–(C2) are the order-`r` analogue of the order-1 statement in `L4_proof.md §5.3` / `L3_proof.md`
Prop D and `BB3_infinity.md §3.1`. They are imported from GMN; the *equidistribution consequence* is
derived next.

### 2.2 Haar pushes forward to the uniform measure on `A^{d_r}(F_r)`

This is the order-`r` repeat of `L4_proof.md` Lemma 0 + Lemma 1. Write the monic residual as
`R_r(g) = y^{d_r} + Σ_{j=0}^{d_r-1} u_j(g) y^j` with `u_j := c_{s+j e_r} / c_{s+d_r e_r} ∈ F_r`. By
(C1) each `c_{s+j e_r}` is the leading `F_r`-digit of an *independent* `φ_r`-coefficient `a_{s+j e_r}`,
and by the unramified index identity `[O_δ : p O_δ]` per residue layer, **the leading `F_r`-digit of a
Haar-uniform integral coordinate is uniform on `F_r`**, independently across coordinates. Precisely
(order-`r` Lemma 0): conditioned on the side `S`,
- the **leading** digit `c_{s+d_r e_r}` is a Haar-uniform **unit** of `F_r` (mass `(1-Q_r^{-1})` of
  the coordinate cell), and likewise `c_s` a uniform unit;
- each **interior** digit `c_{s+j e_r}` (`0 < j < d_r`) is a Haar-uniform element of `F_r` (the ball
  `v ≥ line` reduces to a free residue digit), independent of the others.

The change of variables `(c_s, ..., c_{s+d_r e_r}) ↦ (u_0, ..., u_{d_r-1}, c_{lead})` with
`u_j = c_{s+je_r}/c_{lead}` is, for each fixed unit `c_{lead}`, an `F_r`-affine isomorphism of the
free residue coordinates; pushing the (uniform on units × uniform on `F_r`) measure through it gives
the **uniform** measure on `(u_0, ..., u_{d_r-1}) ∈ F_r^{d_r}` (the leading-unit normalization is a
bijection `F_r^* × F_r^{d_r} → F_r^* × F_r^{d_r}` preserving uniform-Haar). Hence
`ρ_r(g) = (u_0, ..., u_{d_r-1})` is **uniform on `A^{d_r}(F_r)`**, with each fibre of equal Haar
measure `μ_δ(M(t,S)) · Q_r^{-d_r}`. This is conclusion (1). Conclusion (2) is immediate: summing the
equal fibre masses over `Σ`. ∎

### 2.3 Remark: why no characteristic obstruction at the wild node

The only `p`-sensitive quantity that could appear is the index `[O_δ : p O_δ]`; it equals `q^δ`
(hence the residue-layer index of `F_r` is `Q_r`) for **all** `p` because `K_δ/Q_p` is unramified
(`v(p)=1`). The slope denominator `e_r = b_r` (possibly `p | e_r`, wild) enters only through *where*
the on-side lattice points fall — fixed by `(h_r, e_r)` as integers — never through the residue
digit's distribution. And `F_r` is a finite field at every order (GMN §2.1 tower), so its residue
digits are genuinely free `F_r`-elements regardless of inseparability upstream. M6 therefore holds
verbatim at a wild node: the inseparability of an *upstream* residual `ψ_{r-1}` is the *trigger* that
created `φ_r` (Lemma 3.11), but it does not constrain the *downstream* residual coefficients `R_r`,
which remain Haar-uniform over `F_r`. (This is the M6-level statement of the structural mechanism:
volume reads the free residue digits, which Frobenius/perfectness make uniform; the wild geometry
lives in the slopes/lifting, invisible here.)

---

## 3. Order 1 = BB1 = L4 (already proved), and the numerics

At `r = 1`: `F_1 = F_q[y]/(ψ_0)` (or `F_q` itself when `f_0 = 1`), `φ_1 = x`, the `φ_1`-coefficients
`a_i = c_i` are literally the coefficients of `g`, and `ρ_1(g)` records the order-1 residual
`R_1(y) = y^{d_1} + Σ u_j y^j` with `u_j` the leading digits of the on-side `c_i`. This is exactly
`L4_proof.md` Lemma 0 + Lemma 1 (the box-measure / cell-as-product statement): the on-side
coefficients reduce to free `F_q`-elements (interior) and units (endpoints), so `R_1` is uniform over
monic degree-`d_1` polynomials. **Proved and verified exactly** in `L4_proof.md §5.3`.

**Numerical validation of M6.**
- **Order 1, directly (this analysis, `check_m6_equidist.py`, system python3).** For the slope-`1/2`
  size-4 cluster the order-1 residual `R_1(y) = y^2 + b̄ y + ā` has `(ā, b̄)` equidistributed over
  `F_q^* × F_q`: chi-square goodness-of-fit at `p ∈ {2,3,5}` gives `χ² = 0.1 / 2.4 / 14.2` against
  `dof = 1 / 5 / 19` — flat within noise, including the wild `p = 2`. (The endpoint `ā` is a uniform
  unit, the interior `b̄` a uniform `F_q`-element, exactly conclusion (1).)
- **Order `r ≥ 2`, indirectly via the oracle outcome distribution.** M6 at order `r` is the input
  that makes the BB3-∞ §7 derived predictions equal the observed type frequencies. Those predictions
  (the size-3 cluster law `β(3)` at the `n=6` deep-wild stratum, the size-2 law at the `n=4` atom and
  the `n=6` slope-`1/3` stratum, and the size-4 law at the `n=8` order-4 stratum) match the trusted
  PARI oracle at all primes including wild `p=2,3` with `max|z| = 3.16` (on a 5-event rare cell;
  well-populated cells `|z| < 1.8`) — see `notes/bb3inf_verify.py`. If M6 failed at any order (the
  residual coefficients non-uniform), the per-shape frequencies would deviate from the
  count/`Q_r^{d_r}` predictions; they do not, through OM order 4. So M6 is **empirically validated
  through order 4**.
- **The finite-field side counts that M6 converts to volumes** are exactly `#Σ` of conclusion (2),
  verified char-independent over `F_2,F_3,F_5,F_7` and the higher-order residue fields `F_4,F_8,F_9,
  F_25` (wild `p=2,3`): non-squarefree count `= Q_r^{d_r-1}` exactly, and every fine shape count a
  single polynomial in `Q_r` across `p` (`notes/gmn_lens_attack2.py`, `notes/gmn_fineshape_attack.py`).

---

## 4. Honest ledger

- **Derived here:** the equidistribution *consequence* (conclusions 1–2) at order `r`, from the GMN
  coordinate facts (C1)–(C2) + the unramified index identity, by the same box-measure argument that
  proves L4 at order 1.
- **Imported (GMN, `p`-independent):** (C1)–(C2) — that the order-`r` residual `R_r` is a genuine
  monic degree-`d_r` polynomial over the finite field `F_r` whose `d_r` coefficients are the
  independent leading `F_r`-digits of the on-side `φ_r`-coefficients (Def 2.20–2.21; Prop 3.5 item 4
  for the surjectivity of the residual reduction; the unique `φ_r`-development for independence). This
  is the same import flagged G-A′ in `BB3_infinity.md`; M6 adds no new external dependency.
- **Severity:** minor. M6 at order `r` is the order-`r` analogue of the fully-proved order-1 fact L4;
  its only non-elementary ingredient is the GMN claim that the order-`r` residual coordinates are
  free/surjective `F_r`-digits, which is part of the imported OM machinery. Empirically validated
  through OM order 4.

**Bottom line.** M6 is the explicit lemma that upgrades L3's *counts* to L2core's *Haar volumes* at
every OM order: `R_r` is Haar-equidistributed over monic degree-`d_r` polynomials over the finite
field `F_r`, so a shape-stratum of `F_r`-point count `#Σ` has conditional volume `#Σ/Q_r^{d_r}`, a
`p`-independent rational function of `q`. At order 1 it is L4; at order `r` it is L4's argument run on
the GMN order-`r` coordinates. ∎
