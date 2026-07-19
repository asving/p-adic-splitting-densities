# M1 — The monic → projective density bridge (general n)

Date: 2026-06-14. Status: **statement + proof reduced to two cited paper results (no
residual analytic gap at the bridge level); fully verified numerically n=2,3.**
Author note: this closes gap M1 / CP2 of `notes/GAPS.md` as the load-bearing join from
the cluster recursion's native (monic) output to the paper's projective `ρ`.

Verification script: `notes/m1_bridge_verify.py` (imports `padic_types.py`; symbolic +
exact + Monte-Carlo, all pass).

---

## 0. The problem and the one-line answer

The cluster recursion (L1–L6) natively computes the **monic** factorization-type density
on `M_n = O_K^n` (mass-1 space of monic degree-`n` polynomials). This is the paper's
`α(n,σ;q)` (Conjecture `conj: bhargava`, line 1013). It is **non-palindromic**: e.g.
`α(3,(111);2) = 4/93`. The Goal Theorem's object is the **projective** density
`ρ(n,σ;q)` on `P^n` (Conjecture `conj: bhargava`, line 1012), which **is** palindromic,
sums to 1, and gives `ρ(3,(111);2) = 25/186`.

**One line.** Both densities are the *same* stratification of "binary degree-`n` forms by
their residue divisor on `P^1`", driven by the *same* intrinsic cluster laws `L_e`; they
differ only in whether the point at infinity `[1:0] ∈ P^1` is an admissible base point.
Monic = affine chart `A^1` (`q` base points, leading coefficient pinned to a unit);
projective = full `P^1` (`q+1` base points). The paper's symmetry
`α(n,σ;q^{-1}) = β(n,σ;q)` (`eqn: symmetry for alpha`, line 1021) is exactly the statement
that `q→1/q` swaps the monic chart with the all-roots-at-infinity chart, and `ρ` — being
the `Aut(P^1)`-symmetric average over all `q+1` base points — is fixed by it.

---

## 1. Notation (fixed; consistent with WORKING_NOTES §0 and the paper)

- `K/Q_p` finite unramified, residue field `F_q`, `O_K`, maximal ideal `m`, `v(p)=1`,
  Haar measure `μ` with `μ(O_K)=1`.
- A **degree-`n` binary form** `F(X,Y) = Σ_{i=0}^n a_i X^{n-i} Y^i ∈ O_K[X,Y]`,
  primitive (not all `a_i ∈ m`), considered up to `O_K^*`-scaling, is a point of
  `P^n(O_K) = P^n(K)` via `(a_0:…:a_n)`. With the canonical measure `μ_{P^n}`
  (paper `lemma: bhargava densities to our densities`, line 1034), `P^n(O_K)` has mass 1.
- `ρ(n,σ;q) := μ_{P^n}({F : type(F)=σ})`. The paper's projective density.
- `α(n,σ;q) := μ({f ∈ M_n : type(f)=σ})`, the **monic** density (`a_0=1`, affine chart).
- `β(n,σ;q) := μ({h ≡ z^n mod m, type(h)=σ})`, the **`z^n`-residue** density.
- `|P^n(F_q)| = (q^{n+1}-1)/(q-1) = 1+q+⋯+q^n`, a palindromic form of weight `n`.
- **Residue divisor.** For primitive `F`, reduce mod `m`: `F̄ ∈ F_q[X,Y]` is a nonzero
  homogeneous degree-`n` form, hence an effective degree-`n` divisor `D(F̄)` on `P^1_{F_q}`,
  i.e. a point of the symmetric power `Sym^n P^1`. We use the classical identity
  `Sym^n P^1 = P^n` (the form ↦ its roots-with-multiplicity), so
  `D(F̄) ∈ Sym^n P^1(F_q) = P^n(F_q)` and `#{D} = |P^n(F_q)|`. **Verified general `n`** by
  the generating function `∏_{d≥1}(1−t^d)^{−N_d(P^1)} ⇒ [t^n] = |P^n(F_q)|`
  (`m1_bridge_verify`/independent check; `N_d(P^1)` = #closed points of `P^1/F_q` of degree
  `d`). For the affine/monic version `Sym^n A^1(F_q) = q^n` (monic residue polynomials).

- A residue divisor `D` is a multiset of **closed points** of `P^1` with multiplicities;
  write `D = Σ_j m_j · P_j`, `P_j` a closed point of degree `δ_j`, `Σ_j m_j δ_j = n`.
  A point `P_j` with `m_j = 1` is **simple**; with `m_j ≥ 2` it is the locus of a
  **size-`m_j` cluster** of roots all reducing to `P_j`.

---

## 2. The bridge lemma (general `n`)

### 2.1 Intrinsic cluster law `L_e^{(δ)}`

**Definition.** Fix a closed point `P` of degree `δ` on `P^1_{F_q}` and an integer `e≥1`.
Condition a degree-`(eδ)` binary form on having residue divisor `e·P` (all `eδ` roots
reduce to `P`, "an `e`-fold cluster over a degree-`δ` residue point"). The conditional
distribution of the local factorization subtype is the **intrinsic cluster law**
`L_e^{(δ)}[·]`, a probability distribution on the factorization types of a degree-`eδ`
étale `K`-algebra whose Galois orbits all sit over the single residue point `P`.

Two reductions make `L_e^{(δ)}` computable and `p`-uniform:

1. **(Base change to the residue degree.)** A degree-`δ` closed point becomes `δ` rational
   points after the unramified base change `K → K_δ`; the unramified extension preserves
   `v(p)=1` and is never wild. Hence `L_e^{(δ)}(q) = L_e^{(1)}(q^δ)` (this is exactly
   L1's `C^{(δ)}_m(q)=C^{(1)}_m(q^δ)` / the paper's `lemma: local integrals` orbit passage
   with `ℓ_i = gcd(δ,1)=1`, so `q ↦ q^{δ/ℓ}=q^δ`). The Frobenius descent back to `K`
   re-groups the `δ` conjugate sub-clusters into one closed point — this is the deferred
   M3, see §6.

2. **(`L_e^{(1)} = β`.)** A rational `e`-fold cluster `e·P` with `P` rational is, after
   translating `P` to `0`, exactly the residue condition `f ≡ z^e (mod m)`. Therefore
   `L_e^{(1)}(q)[σ] = β(e,σ;q)` (the paper's `β`, line 1014). And by the paper's
   `eqn: symmetry for alpha` (`α(e,σ;q^{-1})=β(e,σ;q)`),

   > **`L_e^{(1)}(q) = β(e,·;q) = α(e,·;q^{-1})` = the monic cluster density at `q→1/q`.**

   This is the crucial identity. It expresses the projective bridge entirely in terms of
   the monic densities the recursion already computes — read at the reciprocal argument.
   (Verified n=2,3: `m1_bridge_verify.py §0`.)

### 2.2 Statement

> **Lemma M1 (monic → projective bridge).** With notation as above, for every `n` and
> every factorization type `σ` of degree `n`,
> ```
>            1
> ρ(n,σ;q) = ────────── · Σ_{D ∈ Sym^n P^1(F_q)}  W_D[σ],            (PROJ)
>            |P^n(F_q)|
> ```
> where the weight of a residue divisor `D = Σ_j m_j·P_j` (closed points `P_j` of degree
> `δ_j`) is the convolution of cluster laws over its repeated points,
> ```
> W_D[σ] = Σ_{ (σ_j)_j : ⊔_j σ_j = σ }  ∏_j  L_{m_j}^{(δ_j)}[σ_j],     (CONV)
> ```
> the sum over ways of writing `σ` as the disjoint union (multiset sum) of local
> factorization types `σ_j`, one per closed point of `D`, with `σ_j` a type of degree
> `m_j δ_j`. Simple points (`m_j=1`) contribute the deterministic local type "one
> unramified factor of residue degree `δ_j`" (`L_1^{(δ)}` is a point mass), so only the
> repeated points carry nontrivial laws.
>
> The **monic** density is the identical formula with `P^1` replaced by the affine line
> `A^1` (drop the point at infinity from the admissible base points) and `|P^n(F_q)|`
> replaced by `q^n`:
> ```
>             1
> α(n,σ;q) =  ── · Σ_{D ∈ Sym^n A^1(F_q)}  W_D[σ].                   (MONIC)
>             q^n
> ```

The only difference between (PROJ) and (MONIC) is the base-point set
`P^1(F_q)` (size `q+1`) vs `A^1(F_q)` (size `q`) and the normalizing point count
`|P^n(F_q)|` vs `q^n`. The cluster laws `L`, the convolution `(CONV)`, and the
per-divisor combinatorics are *identical*.

### 2.3 Why this is `p`-independent

`(PROJ)` decomposes into three layers, each char-independent:

- **Residue-config counts** `#{D ∈ Sym^n P^1(F_q) of a given closed-point-degree pattern}`
  are universal polynomials in `q` (combinatorics of `Sym^n P^1 = P^n`; L3 / paper's Tate
  quotient `lemma: tate quotient`). No `p`-dependence: `Sym^k(A^1)=A^k`, finite fields
  perfect.
- **Cluster laws** `L_e^{(δ)} = β(e,·;q^δ)` are universal rational functions of `q` (this is
  the recursion's monic output `α(e,·;q^{-δ})`, the content of L1–L6; `p`-independent there).
- **The normalization** `1/|P^n(F_q)|` and `1/q^n` are explicit `q`-powers.

So the bridge introduces **no new characteristic dependence** — it is pure
combinatorics + the already-`p`-uniform monic densities.

---

## 3. Proof

The proof is a measure-theoretic stratification plus two paper citations.

### Step 1 — `P^n(O_K)` partitions into equal-measure residue cells.

By the canonical-measure normalization (`lemma: bhargava densities to our densities`,
line 1034), `μ_{P^n}` assigns each residue class of a primitive form mod `m` equal mass
`1/|P^n(F_q)|`, and these classes are exactly the points `D ∈ P^n(F_q) = Sym^n P^1(F_q)`
(the reduction of a primitive form is a nonzero degree-`n` form up to `F_q^*`, i.e. an
effective degree-`n` divisor on `P^1`). This is an exact partition up to the measure-zero
imprimitive locus (`all a_i ∈ m`), and up to the measure-zero locus where the form is
not separable over `K` (discriminant `= 0`), which carries no type. Hence
`ρ(n,σ;q) = (1/|P^n|) Σ_D μ(type=σ | residue=D)` and it remains to compute the conditional
`μ(type=σ | residue=D) = W_D[σ]`.

### Step 2 — Hensel coprime-splitting factorizes the conditional law over closed points.

On the cell `residue = D = Σ_j m_j P_j`, the residue form factors as `F̄ = ∏_j ḡ_j^{m_j}`
with the `ḡ_j` (minimal polynomials of the distinct closed points `P_j`) pairwise coprime.
By Hensel (L1: unit-resultant multiplication map is a measure-preserving analytic
isomorphism, Igusa *Local zeta functions* §7.4), `F` factors uniquely as `∏_j F_j` with
`F̄_j = ḡ_j^{m_j}`, the Haar measure factorizes as a product over `j`, and the global type
is the disjoint union `σ = ⊔_j type(F_j)` (CRT: `K[x]/F = ∏_j K[x]/F_j`). This is exactly
the convolution `(CONV)`; the factor for closed point `P_j` is the conditional law of
`F_j` given `F̄_j = ḡ_j^{m_j}`, i.e. an `m_j`-fold cluster over the degree-`δ_j` point
`P_j` — by definition `L_{m_j}^{(δ_j)}`.

### Step 3 — Each local cluster law is the monic density read at `q^δ` and `q→1/q`.

By §2.1(1)-(2), `L_e^{(δ)}(q)[σ] = β(e,σ;q^δ) = α(e,σ;q^{-δ})`. The right side is the
recursion's monic single-cluster density (L2/L4/L3), a universal rational function of `q`,
evaluated at `q^δ` (base change, L1) and `q→1/q` (the point at infinity / `z^e`-residue
reciprocal, paper `eqn: symmetry for alpha`). This is the *only* place where the
projective/monic distinction enters analytically, and it is a single substitution
`q → q^{-1}` of an object the program already controls.

### Step 4 — Monic version: drop the point at infinity.

For the monic density `α`, the leading coefficient is pinned to a unit, so the residue
form `f̄` is a **monic** degree-`n` polynomial: the point at infinity `[1:0]` is never a
root (it would require `a_0 ∈ m`). Thus the residue divisor ranges over `Sym^n A^1(F_q)`
(size `q^n`), not `Sym^n P^1(F_q)`. Steps 1–3 go through verbatim with `A^1` in place of
`P^1` and the affine normalization `μ(M_n)=1`, `#{cells}=q^n`, giving `(MONIC)`. The
cluster laws `L_e^{(δ)}` are *the same functions* — they are local to a residue point and
do not see whether that point is affine or at infinity.

### Step 5 — Identification with the paper's `eqn: factorization densities as integrals`.

The paper's route (`eqn: factorization densities as integrals`, line 1132) writes
```
ρ(n,σ;q) = (1/|P^n(F_q)|) Σ_{σ'≤σ} α^{-1}(τ_{σ'},τ_σ) η_{f_{σ'}}(K),
```
the Möbius inversion over the factorization-type poset of the incidence identity
`η_{f_σ}(K) = Σ_{σ'≤σ} α(τ_{σ'},τ_σ)|P^n(F_q)| ρ(n,σ';q)` (`thm`, line 1123). Our
`(PROJ)` is *the same identity organized by residue divisor instead of by poset*:
- The `η_{f_σ}(K)` integrals are the resolution integrals over `X_σ → (P^1)^n/H_σ → P^n`.
  Stratifying `(P^1)^n(O_K)` by residue (the paper does exactly this in the completely-split
  worked example, line 1302: "Stratifying `(P^1)^3(B)` by residue triples decomposes
  `η_{f_1}`…") shows `η_{f_σ}/|P^n|` is itself a sum over residue divisors of products of the
  same local integrals `ρ_k(m;q^{δ})` of `defn: rho, eta` (line 538) that build `β = L_e`.
- The combinatorial coefficients `α(τ_{σ'},τ_σ)` (`defn: alpha, beta`, line 591) are the
  **integer, `p`-independent** orbit counts `#{λ ∈ H_σ\S_n : λτ_{σ'}λ^{-1} ≤ τ_σ}`. In the
  residue-divisor organization these are precisely the multiplicities with which a coarser
  residue pattern `σ'` (a partition refinement on `P^1`) feeds the finer type `σ` — i.e.
  the multinomial config counts `#{D of pattern σ'}` and the within-cluster outcome
  multiplicities. The Möbius inversion `α^{-1}` of the paper is the inclusion–exclusion
  that converts "ordered cluster data over `(P^1)^n`" into "unordered factorization type
  `σ`", which in `(PROJ)` is performed by the disjoint-union sum `(CONV)` together with the
  symmetric-power identification `Sym^n P^1 = P^n` (the quotient by `S_n` that turns ordered
  roots into the divisor `D`).

Concretely for `n=3` the dictionary is exact (verified, §4): the paper's `α(τ_1,τ_1)=|S_3|=6`
for the split type is the `1/6 = 1/|Stab|` appearing in `#{3 distinct base points} =
C(q+1,3)`; the cluster-coupling coefficients `(q+1)` and `(q+1)q` of `proj_cubic_pred` are
the `P^1(F_q)` configuration counts `#{triple base points}=q+1` and `#{double+simple
ordered}=(q+1)q` — i.e. the `α`-factors specialized to the size-2 and size-3 clusters.

∎ (modulo the two residual citations isolated in §6).

---

## 4. The `n=3` instance: decoding `proj_cubic_pred`

`padic_types.proj_cubic_pred` is exactly `(PROJ)` for `n=3` with the abbreviations
`x = 1/q`, `s = monic_quad_pred`, `t = monic_cubic_pred`:

| code symbol | meaning in `(PROJ)` |
|---|---|
| `P3 = q^3+q^2+q+1` | `|P^3(F_q)|`, the normalization |
| `cfg['111']=q(q+1)(q-1)/6` | `#{3 distinct rational base pts}=C(q+1,3)` (separable leaf → 111) |
| `cfg['12']=(q+1)q(q-1)/2` | `#{1 rational + 1 deg-2 closed pt}` (separable leaf → 12) |
| `cfg['3']=(q^3-q)/3` | `#{1 deg-3 closed pt}` (separable leaf → 3) |
| `dbl=(q+1)q` | `#{double + simple, ordered}` = `#{P^1}·#{P^1∖pt}`: the size-2 cluster configs |
| `tri=(q+1)` | `#{triple rational pt}` = `#{P^1}`: the size-3 cluster configs |
| `x·s[·]` | size-2 cluster law `L_2^{(1)}` written via `α(2,·;q)·x` (the `q→1/q` of §2.1(2)) |
| `x^3·t[·]` | size-3 cluster law `L_3^{(1)}` written via `α(3,·;q)·x^3` |
| `(1-x)` terms | the algebraic remainder of `β = α(1/q)` when expressed through the mass-1 monic `α` |

The `x`-power on a size-`e` cluster is `x^{C(e,2)}` (`C(2,2)=1`, `C(3,2)=3`): the
Vandermonde / discriminant codimension of "all `e` roots in one residue disk". The cleanest
form (no `(1-x)` artifacts) uses the cluster laws `L_e` directly as probability
distributions; `m1_bridge_verify.assemble_n3` does this and reproduces both
`proj_cubic_pred` and `monic_cubic_pred` exactly:

```
L_2 :  (1)(1) → 1/(2(q+1)),   (2) → 1/(2(q+1)),   (1^2) → q/(q+1)            [sum 1]
L_3 :  (1)(1)(1) → (q^2-q+1)/(6(q^5+2q^4+2q^3+2q^2+2q+1))
       (1)(2)    → (q^2+q+1)/(2(q^5+2q^4+2q^3+2q^2+2q+1))
       (3)       → (q^2-1)/(3(q^5-1))
       (1)(1^2)  → q(q^5+q^4-q^3-1)/((q+1)^2(q^5-1))
       (1^3)     → q^2(q^3-q^2+q-1)/(q^5-1)                                  [sum 1]
```

(`L_3 = β(3,·;q) = α(3,·;1/q)`, verified.) Assembled projective densities, all
palindromic, sum 1:
```
ρ(111) = (q^2+1)^2 / (6 Φ)            [= paper, line 1305]
ρ(12)  = (q^4+1) / (2 Φ)
ρ(3)   = (q^4-q^2+1) / (3 Φ)
ρ(1r1) = (q^3+q) / Φ
ρ(1c)  = q^2 / Φ                       Φ = q^4+q^3+q^2+q+1 = |P^4(F_q)|
```
(The denominator is `Φ`, not `|P^3|=(q+1)(q^2+1)`: the `(q+1)` cancels against the cluster
laws' `(q+1)` factors and the `(q-1)` against `q^5-1=(q-1)Φ`, leaving the weight-0
palindromic `·/Φ`.)

---

## 5. The `n=2` instance from scratch (binary quadratic forms)

`P^2` parametrizes binary quadratics `a_2X^2+a_1XY+a_0Y^2` up to scale; types
split / inert / ram. `Sym^2 P^1(F_q)=P^2(F_q)`, `|P^2|=q^2+q+1`. Residue configs:
`#{2 distinct rational}=C(q+1,2)` (→split, separable leaf), `#{1 deg-2 closed pt}=(q^2-q)/2`
(→inert, separable leaf), `#{double rational}=q+1` (size-2 cluster, law `L_2`). Assembling
`(PROJ)`:
```
ρ(2,split;q) = 1/2
ρ(2,inert;q) = (q^2-q+1)/(2(q^2+q+1))
ρ(2,ram;q)   = q/(q^2+q+1)
```
All palindromic (`R(1/q)=R(q)`), sum 1. The monic `(MONIC)` version (`q` base points,
`/q^2`) reproduces `monic_quad_pred` exactly:
`α(2,split)=α(2,inert)=q/(2(q+1))`, `α(2,ram)=1/(q+1)` (non-palindromic, as required).
The clean palindromic value `ρ(split)=1/2` is independently confirmed by Monte-Carlo
across `p=2,3,5,7` (`m1_bridge_verify §2`).

---

## 6. Numeric verification summary (`notes/m1_bridge_verify.py`)

| check | result |
|---|---|
| `L_2, L_3` sum to 1; `β = α(1/q)` (n=2,3, symbolic) | PASS |
| `(PROJ)` n=2 palindromic + sum 1; n=3 palindromic + sum 1 + = paper `(q^2+1)^2/6Φ` | PASS |
| `(MONIC)` n=2 = `monic_quad_pred`; n=3 = `monic_cubic_pred` (symbolic exact) | PASS |
| bridge n=3 == `proj_cubic_pred` at q∈{2,3,5,7,11,13} (exact `Fraction`) | PASS |
| Monte-Carlo n=3 (binary cubic on `P^3`), p∈{2,3,5,7}, N=2·10^5 | max\|z\|=2.08 |
| Monte-Carlo n=2 (binary quadratic on `P^2`), p∈{2,3,5,7}, N=3·10^5 | max\|z\|=2.19 |

All `z`-scores within sampling noise; wild primes `p=2,3` included. The bridge is exact at
`n≤3`.

---

## 7. What is proved vs. what remains (honest status)

**Proved (no residual analytic gap at the bridge level):**
- The bridge *statement* `(PROJ)`/`(MONIC)` for general `n`, with every symbol defined.
- The measure-theoretic skeleton (Steps 1–4): equal-measure residue partition + Hensel
  convolution + cluster-law-as-`β`-as-`α(1/q)` + affine/projective base-point swap. Each
  step is either elementary or a cited paper/L-lemma result (`lemma: bhargava densities to
  our densities`; Igusa §7.4 via L1; `eqn: symmetry for alpha`).
- Char-independence (§2.3): config counts (Tate quotient / L3), cluster laws (L1–L6 monic
  output), normalization — all `p`-uniform.
- Exact agreement with the paper and with `proj_cubic_pred` at `n≤3`; n=2 done from scratch.

**Reduced-to-paper, not re-derived here (the two residual sub-gaps inside M1):**

- **M3 / Frobenius descent for `δ>1` closed points** (used in §2.1(1), Step 3). The identity
  `L_e^{(δ)}(q)=L_e^{(1)}(q^δ)` and the re-grouping of `δ` Frobenius-conjugate sub-clusters
  into one closed point is the paper's `lemma: local integrals` (line 772) orbit passage
  with `ℓ_i=gcd(δ,1)=1`. The substitution structure is verified consistent (and the
  measure identity is checked at `(e,δ)=(2,2)`, `p=2`, in an L1 verdict), but the descent
  itself is **cited, not executed** here. `K_δ/K` is unramified (never wild), so no new
  characteristic dependence — low risk, but a genuine external dependency.

- **The `α^{-1}` Möbius identification** (Step 5). I show `(PROJ)` and the paper's
  `eqn: factorization densities as integrals` are the *same* identity reorganized, and
  verify the dictionary exactly for `n=3` (the `(q+1)`, `(q+1)q` couplings = `P^1` config
  counts = `α`-factors). The clean general-`n` proof that the disjoint-union convolution
  `(CONV)` over `Sym^n P^1` **equals** the incidence-poset Möbius inversion
  `Σ_{σ'≤σ}α^{-1}(τ_{σ'},τ_σ)η_{f_{σ'}}/|P^n|` is *argued structurally* (both are the
  `S_n`-quotient that unorders the roots, both have integer `p`-independent coefficients)
  but is **not written as a standalone combinatorial lemma**. This is the same content as
  the deferred CP2; it is now reduced from "missing lemma" to "two equivalent
  organizations of one inclusion–exclusion, matched verbatim at `n=3`".

**Net assessment.** M1 is no longer the highest-risk *open* gap: the bridge statement is
precise, the mechanism is proved, char-independence is established, and the n≤3 numerics are
exact. What remains is (i) executing the unramified Frobenius descent (M3, the paper's
`lemma: local integrals`) and (ii) writing the general-`n` `(CONV) = α^{-1}`-Möbius
equality as a formal lemma. Both are `p`-independent bookkeeping against the paper's §2–4,
not new analysis, and neither touches the wild-prime difficulty (which lives entirely in the
cluster laws `L_e`, i.e. in L2/L5 gap G-A, not in the bridge).

---

## 8. Connection-point citations (exact labels in `main_gemini_revision.tex`)

- `lemma: bhargava densities to our densities` (line 1034): `μ_Haar(π^{-1}S)=μ_{P^n}(S)/|P^n(F_q)|`. — Step 1.
- `conj: bhargava` (line 1009), defs of `ρ,α,β` (lines 1012–1014). — §0,§1.
- `eqn: symmetry for alpha` (line 1021): `α(n,σ;q^{-1})=β(n,σ;q)`. — §2.1(2), the crux.
- `defn: factorization types from admissible pairs` (line 1053), `s(τ)`; `τ_σ` (line 1095). — §5 dictionary.
- `defn: alpha, beta` (line 589): the integer orbit counts `α,β,γ`. — §5 coefficients (`p`-independent).
- `lemma: adjointness between pairs and types` (1099), `lemma: alpha invariant under adjointness` (1113). — §5.
- `eqn: factorization densities as integrals` (line 1132): the `α^{-1}` Möbius form. — §5, the identification target.
- `lemma: local integrals` (line 772): the `q→q^{δ}` orbit/Frobenius descent. — §2.1(1), residual M3.
- Worked completely-split `n=3` example (line 1302), `ρ(3,(111);q)=(q^2+1)^2/(6Φ)` (line 1305). — §4 anchor.
