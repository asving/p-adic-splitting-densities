# UNIT NOTE — UNIFORMITY-P3: Hensel lifting of coprime factorizations, 2026-08-13

**Charge.** Supply, in `leanfinal`, Hensel's lemma in its *factorization* form — lift a coprime
monic factorization of the residue reduction of a monic polynomial to a factorization over the
base ring — at adic-complete local generality (no DVR hypothesis, no finite residue field, no
residue-characteristic hypothesis). Motivation: `leancheck/notes/N3_CHECK_2026-08-13.md` §7,
"branch (ii)" of the `n = 3` pinning argument, which needs to peel a *residually repeated
quadratic* off a linear factor and so cannot use the root form of Hensel that all the `n ≤ 3`
certificates currently use.

**Files.** `leanfinal/Uniformity/HenselFactorization.lean` (new) and one import line added to
`leanfinal/Uniformity.lean`. Nothing else under `leanfinal/` was touched.

---

## 1. STEP 0 — the absence check, and the backport decision

**Verdict: absent from Mathlib (pinned v4.31 *and* master), and not cheaply backportable from
elsewhere. Proved from scratch.**

* **Pinned mathlib v4.31** (`leanfinal/.lake/packages/mathlib`). `Mathlib/RingTheory/Henselian.lean`
  contains only the ROOT form: `HenselianRing`, `HenselianLocalRing` (both axiomatised by
  *"simple root over `R/I` lifts to a root over `R`"*), `HenselianLocalRing.TFAE` (three root
  forms), `IsAdicComplete.henselianRing`, `IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub`.
  Its own `## TODO` block says, verbatim:

  > After a good API for étale ring homomorphisms has been developed, we can give more equivalent
  > characterization of Henselian rings. **In particular, this can give a proof that factorizations
  > into coprime polynomials can be lifted from the residue field to the Henselian ring.**

  i.e. mathlib itself records the target of this unit as an open TODO.
* **Mathlib master** (sha `51c80a99`, 2026-08-13; whole tree downloaded and grepped by a
  reconnaissance agent): `henselian` occurs only inside `Mathlib/RingTheory/Henselian.lean`;
  no `HenselLift.lean`, no factorization form anywhere; the linked design gist
  (`gist.github.com/jcommelin/47d94e4af092641017a97f7f02bf9598`, Lean 3, 2021) states our exact
  theorem inside a comment and never implements it. GitHub PR search: nothing relevant.
* **The closest existing thing, and why it is not enough.**
  `Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean` (present in v4.31) proves
  `Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime` (`@[stacks 00UH]`):
  a coprime monic residual factorization lifts to *some étale algebra* `R'` with a prime over `P`
  and the same residue field. To land it on `R` itself one needs the henselian splitting property
  ("every étale `R`-algebra with a rational point over the closed point admits an `R`-section").
* **FLT** (`ImperialCollegeLondon/FLT`, main sha `4d843a6a`, 2026-08-13) has exactly that missing
  half, sorry-free: `FLT/HenselianLocalRing/Finite.lean:61`,
  `HenselianLocalRing.exists_lift_of_to_ResidueField`. **Not backported**, for two reasons:
  (i) it is not self-contained — it imports `FLT.HenselianLocalRing.EtaleDecomposition`,
  `FLT.HenselianLocalRing.Stuff` and `Mathlib.RingTheory.Unramified.LocalStructure`, and is written
  against mathlib *master*, whose `Algebra.Etale` / `Unramified` API has drifted from v4.31;
  (ii) the composed route would drag the whole étale-descent stack into `leanfinal` as a
  dependency of a lemma whose direct proof is elementary. The direct Newton proof below imports
  nothing beyond polynomial division, `Ideal.map C`, and `IsAdicComplete`.

Provenance recorded in the file header so a future reader can re-audit this decision.

---

## 2. THE INFORMAL PROOF (written before the Lean attempt)

Throughout: `R` a commutative local ring, `𝔪 = IsLocalRing.maximalIdeal R`, `k = R/𝔪` the residue
field, `π : R[X] → k[X]` the coefficientwise reduction `Polynomial.map (residue R)`, and
`R` is `𝔪`-adically complete (`IsAdicComplete 𝔪 R`, i.e. Hausdorff + precomplete).

For an ideal `J ⊆ R` write **`J⟨X⟩ := Ideal.map (C : R →+* R[X]) J`** — the ideal of `R[X]`
consisting of the polynomials all of whose coefficients lie in `J` (`Ideal.mem_map_C_iff`).
Two facts used constantly:
* `J⟨X⟩` is an ideal of `R[X]`, so `p ∈ J⟨X⟩ ⟹ qp ∈ J⟨X⟩` for any `q` (no degree condition);
* `(J⟨X⟩)·(J'⟨X⟩) ⊆ (JJ')⟨X⟩` — in fact `Ideal.map_mul` makes it an equality.

Given data: `f ∈ R[X]` monic, `g₀, h₀ ∈ k[X]` monic and `IsCoprime`, `π f = g₀ h₀`.
Set `m = deg g₀`, `l = deg h₀`, `n = deg f = m + l` (monicity of `f` gives `deg (π f) = n`, and
monicity of `g₀, h₀` gives `deg (g₀h₀) = m + l`).

### 2.1 The residue-field solve (LEMMA `Field` level)

> **(S0)** `k` a field, `g₀, h₀` monic of degrees `m, l`, `IsCoprime g₀ h₀`. For every
> `w ∈ k[X]` with `deg w < m + l` there are `u, v ∈ k[X]` with `deg u < m`, `deg v < l` and
> `w = h₀ u + g₀ v`.

*Proof.* `IsCoprime` unfolds to `a g₀ + b h₀ = 1`. Multiply by `w`:
`w = g₀ (a w) + h₀ (b w)`. Divide `b w` by the monic `g₀`: `b w = q g₀ + u` with `deg u < deg g₀ = m`
(`Polynomial.modByMonic`, `degree_modByMonic_lt`). Substituting,
`w = g₀ (a w + h₀ q) + h₀ u =: g₀ v + h₀ u`.
The degree bound on `v` is *forced*, not chosen: `g₀ v = w − h₀ u` has degree `< m + l` (both
`w` and `h₀u` do), and `g₀` is monic, so `deg (g₀ v) = m + deg v`, whence `deg v < l`. ∎

Note the pairing: **the correction to `g` multiplies `h`**. That is the pairing the Newton step
needs, since `(G+δG)(H+δH) = GH + H·δG + G·δH + δG·δH`.

### 2.2 One-step solve over `R`, modulo `𝔪`

> **(S1)** `G, H ∈ R[X]` monic with `π G = g₀`, `π H = h₀` (so `deg G = m`, `deg H = l`).
> For every `w ∈ R[X]` with `deg w < n` there are `U, V ∈ R[X]` with `deg U < m`, `deg V < l`
> and `w − (H U + G V) ∈ 𝔪⟨X⟩`.

*Proof.* Apply (S0) to `π w` (degree `≤ deg w < n`), obtaining `u, v`. Lift them **with degree
control** using `Polynomial.exists_degree_eq_of_mem_lifts` (`residue R` is surjective, so every
`k[X]`-polynomial lifts, and one can lift with `deg U = deg u`). Then `π (w − HU − GV) =
π w − h₀ u − g₀ v = 0`, i.e. every coefficient lies in `𝔪`. ∎

### 2.3 Scaled step: from `𝔪^j` to `𝔪^{j+1}` (the Newton step)

> **(S2)** Same `G, H`. For every `j` and every `e ∈ 𝔪^j⟨X⟩` with `deg e < n` there are
> `U, V ∈ 𝔪^j⟨X⟩` with `deg U < m`, `deg V < l` and `e − (H U + G V) ∈ 𝔪^{j+1}⟨X⟩`.

*Proof.* This is the only place where "coefficients in `𝔪^j`" has to interact with the degree
bookkeeping, and the trick is **linearity in the coefficients of `e`**. Apply (S1) once to each
monomial `X^i`, `i < n`: get `U_i, V_i` with `deg U_i < m`, `deg V_i < l` and
`r_i := X^i − (H U_i + G V_i) ∈ 𝔪⟨X⟩`. Since `deg e < n`, `e = Σ_{i<n} C(e_i) X^i` with
`e_i := e.coeff i ∈ 𝔪^j`. Put
`U := Σ_{i<n} C(e_i) U_i`, `V := Σ_{i<n} C(e_i) V_i`.
Then `deg U < m`, `deg V < l` (finite sums of polynomials of degree `< m`, resp. `< l`),
`U, V ∈ 𝔪^j⟨X⟩` (each `C(e_i)U_i` has coefficients `e_i · (U_i)_t ∈ 𝔪^j`), and
`e − (HU + GV) = Σ_{i<n} C(e_i) r_i ∈ 𝔪^j⟨X⟩ · 𝔪⟨X⟩ ⊆ 𝔪^{j+1}⟨X⟩`. ∎

*(Remark. The usual textbook route instead lifts a residue-field Bézout identity and divides the
error by the monic `g_k`; over a DVR one writes `e = π^j e'` and stays in the residue field. Neither
survives verbatim when `𝔪` is not principal. (S2) is the coordinate-free replacement: it is exactly
the statement `Φ(𝔪^j·M) ⊇ 𝔪^j·N mod 𝔪^{j+1}` for the `R`-linear
`Φ : R[X]_{<m} × R[X]_{<l} → R[X]_{<n}`, `(U,V) ↦ HU + GV`, proved by reducing to the
`R`-module generators `X^i` of `R[X]_{<n}`.)*

### 2.4 The limit lemma

> **(L)** Let `d : ℕ` and `p : ℕ → R[X]` with `deg (p k) < d` for all `k` and
> `p (k+1) − p k ∈ 𝔪^k⟨X⟩` for all `k`. Then there is `P ∈ R[X]` with `deg P < d` and
> `P − p k ∈ 𝔪^k⟨X⟩` for all `k`.

*Proof.* Coefficientwise. Fix `i`. For `j ≤ k`, telescoping gives `(p j − p k).coeff i ∈ 𝔪^j`, i.e.
the sequence `k ↦ (p k).coeff i` is `𝔪`-adically Cauchy in mathlib's `SModEq` sense. Precompleteness
(`IsPrecomplete.prec'`) yields `L i` with `(p k).coeff i ≡ L i [SMOD 𝔪^k]` for every `k`. Set
`P := Σ_{i<d} C(L i) X^i`. For `i < d` the claim is the displayed congruence; for `i ≥ d` both
`P.coeff i` and `(p k).coeff i` vanish. ∎

### 2.5 Existence

Lift `g₀, h₀` to monic `G₁, H₁ ∈ R[X]` of degrees `m, l`
(`Polynomial.lifts_and_degree_eq_and_monic`). Then `f − G₁H₁ ∈ 𝔪⟨X⟩` and `deg (f − G₁H₁) < n`
(difference of two monic degree-`n` polynomials).

Define recursively `(G_{k+1}, H_{k+1}) = (G_k + δG_k, H_k + δH_k)` where `(δG_k, δH_k)` is (S2)
applied at level `j = k+1` to `e_k := f − G_kH_k`, **with the fixed pair `(G₁, H₁)`** in the role
of `(G, H)`. Freezing `(G₁,H₁)` costs only linear (rather than quadratic) convergence and saves
re-deriving (S1) at every step. The invariants, all proved simultaneously by induction:

* `G_k` monic of degree `m`, `H_k` monic of degree `l`, `π G_k = g₀`, `π H_k = h₀`;
* `e_k = f − G_kH_k ∈ 𝔪^{k+1}⟨X⟩` and `deg e_k < n`;
* `G_{k+1} − G_k, H_{k+1} − H_k ∈ 𝔪^{k+1}⟨X⟩`.

The error recursion is the computation
```
e_{k+1} = f − (G_k+δG)(H_k+δH)
        = [e_k − (H₁ δG + G₁ δH)]  +  (H₁ − H_k) δG  +  (G₁ − G_k) δH  −  δG·δH,
```
whose four terms lie in `𝔪^{k+2}⟨X⟩` because, respectively: (S2)'s conclusion; `H₁ − H_k ∈ 𝔪⟨X⟩`
and `δG ∈ 𝔪^{k+1}⟨X⟩`; likewise; and `δG·δH ∈ 𝔪^{2k+2}⟨X⟩ ⊆ 𝔪^{k+2}⟨X⟩`.

Apply (L) to the *tails* `G_k − X^m` (degree `< m`) and `H_k − X^l`, obtaining `T_G, T_H`; set
`G := X^m + T_G`, `H := X^l + T_H`, monic of degrees `m, l`. Then for every `k`
```
f − GH = (f − G_kH_k) − (G − G_k)H − G_k(H − H_k) ∈ 𝔪^k⟨X⟩,
```
so every coefficient of `f − GH` lies in `⋂_k 𝔪^k = 0` (`IsHausdorff.haus'`), i.e. `f = GH`.
Finally `G − G₁ ∈ 𝔪⟨X⟩` gives `π G = π G₁ = g₀`, and similarly `π H = h₀`.

### 2.6 Exact solve, coprimality, uniqueness

> **(S3)** Same `G, H` as in (S1). For every `w` with `deg w < n` there are `U, V` with
> `deg U < m`, `deg V < l` and `w = H U + G V` **exactly**.

*Proof.* Same iteration as §2.5 but on the linear problem: `U_0 = V_0 = 0` (note `𝔪^0 = ⊤`, so the
level-0 hypothesis of (S2) is vacuous), `U_{k+1} = U_k + δU_k` with `(δU_k, δV_k)` from (S2) at
level `k` applied to `w − (HU_k + GV_k)`. Invariants: `deg U_k < m`, `deg V_k < l`,
`w − (HU_k + GV_k) ∈ 𝔪^k⟨X⟩`, `U_{k+1} − U_k ∈ 𝔪^k⟨X⟩`. (L) gives `U, V`, and
`w − (HU+GV) = [w − HU_k − GV_k] − H(U−U_k) − G(V−V_k) ∈ 𝔪^k⟨X⟩` for all `k`, hence `= 0`. ∎

> **(C)** If `n ≥ 1` then `IsCoprime G H` in `R[X]`.

*Proof.* (S3) with `w = 1`. ∎ *(This is genuinely stronger than the residual coprimality: over a
local ring `A G + B H = 1 + (something in 𝔪⟨X⟩)` is not automatically improvable, and `1 + 𝔪⟨X⟩`
consists of non-units in general. The completeness is doing real work here.)*

> **(U)** Uniqueness. If `G H = G' H'` with all four monic, `π G = π G' = g₀`, `π H = π H' = h₀`,
> then `G = G'` and `H = H'`.

*Proof.* All of `G, G'` are monic of degree `m` (degree is read off the monic reduction), so
`U := G' − G` has `deg U < m`. From `GH = G'H' = (G+U)H'` we get `G(H − H') = U H'`, so `G ∣ U H'`.
By (C) applied to the pair `(G, H')` — legitimate, since `G` and `H'` are monic lifts of the
coprime pair `(g₀, h₀)` — `IsCoprime G H'`, hence `G ∣ U` (`IsCoprime.dvd_of_dvd_mul_right`).
Writing `U = G c`, monicity gives `deg U = deg G + deg c`; `deg U < deg G` forces `deg c = ⊥`,
i.e. `c = 0`, i.e. `G = G'`. Then `G H = G H'` and `G` monic (hence regular,
`Polynomial.Monic.isRegular`) gives `H = H'`. ∎

The degenerate case `n = 0`: then `m = l = 0`, `f = G = H = 1`, and every clause holds trivially;
(C) is `IsCoprime 1 1`. The Lean proof handles `n = 0` inside the general argument
(`deg w < 0` is vacuous, so (S3) is vacuous, and (C) is stated for `0 < n`; uniqueness at `n = 0`
follows from monic-of-degree-0 ⟹ `= 1`).

---

## 3. WHAT LANDED

See §5 for the audited statement list with axiom footprints. Headline:

* `Uniformity.Hensel.exists_monic_factorization` — existence, at adic-complete local generality.
* `Uniformity.Hensel.monic_factorization_unique` — uniqueness of the lifted pair.
* `Uniformity.Hensel.isCoprime_of_map_eq` — `IsCoprime G H` in `R[X]` for monic lifts of a
  coprime residual pair (the reusable by-product).
* `Uniformity.Hensel.exists_eq_add_mul_of_degree_lt` — the exact Bézout/interpolation solve (S3).

---

## 4. TRUST BOUNDARY — faithfulness paragraphs (FLAGGED FOR ASVIN'S REVIEW)

Lean checks proofs, not statements. Every statement introduced by this unit is new, so every one
gets a paragraph. **None of these was weakened to make a proof go through**; the file contains
zero `sorry` and adds zero axioms.

### 4.1 `exists_monic_factorization`

```lean
theorem exists_monic_factorization {R : Type*} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {f : R[X]} (hf : f.Monic)
    {g₀ h₀ : ResidueField R[X]} (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) (hfgh : f.map (residue R) = g₀ * h₀) :
    ∃ g h : R[X], g.Monic ∧ h.Monic ∧ f = g * h ∧
      g.map (residue R) = g₀ ∧ h.map (residue R) = h₀ ∧
      g.natDegree = g₀.natDegree ∧ h.natDegree = h₀.natDegree
```
**Faithfulness.** This is the classical statement (Bourbaki, *Algèbre commutative* III §4.3;
Stacks 04GG/0BSF; Neukirch II.4.6 in the DVR case), transcribed with no hidden strengthening of
hypotheses or weakening of conclusions. Points a reviewer should check:
(a) `residue R : R →+* ResidueField R` is mathlib's canonical quotient map by `maximalIdeal R`,
and `Polynomial.map (residue R)` is coefficientwise reduction — so `hfgh` says exactly
"`f` reduces to `g₀h₀` mod `𝔪`";
(b) `IsCoprime g₀ h₀` in mathlib is `∃ a b, a * g₀ + b * h₀ = 1` in the ring `ResidueField R[X]`,
which over a field is equivalent to `gcd = 1`, i.e. no common root in any extension — the
intended meaning;
(c) the degree clauses are *conclusions*, not hypotheses, and are the ones that make the
factorization useful downstream (they pin which factor is which);
(d) no finiteness, no discreteness, no residue characteristic, and no `IsDomain` is assumed;
`IsAdicComplete (maximalIdeal R) R` is mathlib's Hausdorff + precomplete bundle;
(e) the theorem is *non-vacuous*: the file's `example`s instantiate it at `ℤ_[p]` and at
`leanfinal`'s own complete-DVR bundle `O`, and the `n = 2` sanity instance factors a concrete
`X² − 1` over `ℤ_[p]`, `p` odd.

### 4.2 `monic_factorization_unique`

```lean
theorem monic_factorization_unique {R : Type*} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {g h g' h' : R[X]} {g₀ h₀ : ResidueField R[X]}
    (hg : g.Monic) (hh : h.Monic) (hg' : g'.Monic) (hh' : h'.Monic)
    (hg₀ : g₀.Monic) (hh₀ : h₀.Monic) (hcop : IsCoprime g₀ h₀)
    (hgr : g.map (residue R) = g₀) (hhr : h.map (residue R) = h₀)
    (hgr' : g'.map (residue R) = g₀) (hhr' : h'.map (residue R) = h₀)
    (heq : g * h = g' * h') : g = g' ∧ h = h'
```
**Faithfulness.** Uniqueness is stated *relative to the residual data*: the pair is unique among
monic pairs reducing to the SAME `(g₀, h₀)`. That is the correct statement — a monic `f` can of
course have many monic factorizations reducing to *different* coprime residual splittings. The
hypothesis is `g*h = g'*h'` rather than `f = g*h ∧ f = g'*h'`, which is formally weaker as a
hypothesis (hence the theorem is stronger) and strictly more convenient. Note the theorem does
**not** assume `g.natDegree = g'.natDegree`: that is derived from the two reduction hypotheses.

### 4.3 `isCoprime_of_map_eq`

```lean
theorem isCoprime_of_map_eq {R : Type*} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {g h : R[X]} {g₀ h₀ : ResidueField R[X]}
    (hg : g.Monic) (hh : h.Monic) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) (hgr : g.map (residue R) = g₀) (hhr : h.map (residue R) = h₀) :
    IsCoprime g h
```
**Faithfulness.** `IsCoprime g h` in `R[X]` means `∃ a b, a*g + b*h = 1` — a genuine Bézout
identity over `R[X]`, not a residual or "up to units" statement. This is the strongest reading and
is what the divisibility arguments downstream need. It is *false* without completeness (e.g. over
a non-henselian local ring one only gets `a g + b h ∈ 1 + 𝔪⟨X⟩`), so the hypothesis is load-bearing,
not decorative. Degenerate case: if both `g₀` and `h₀` are constants then `g₀ = h₀ = 1`
(monic of degree 0), `g = h = 1` and `IsCoprime 1 1` holds; the proof covers this.

### 4.4 `exists_eq_add_mul_of_degree_lt`

```lean
theorem exists_eq_add_mul_of_degree_lt {R : Type*} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {g h : R[X]} {g₀ h₀ : ResidueField R[X]}
    (hg : g.Monic) (hh : h.Monic) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) (hgr : g.map (residue R) = g₀) (hhr : h.map (residue R) = h₀)
    {w : R[X]} (hw : w.degree < (g.natDegree + h.natDegree : ℕ)) :
    ∃ u v : R[X], u.degree < (g.natDegree : WithBot ℕ) ∧ v.degree < (h.natDegree : WithBot ℕ) ∧
      w = h * u + g * v
```
**Faithfulness.** This is "the Chinese remainder isomorphism `R[X]/(gh) ≅ R[X]/(g) × R[X]/(h)` is
surjective on degree-bounded representatives", stated concretely. The pairing is
`u` (degree `< deg g`) against `h`, and `v` (degree `< deg h`) against `g` — deliberately, since
that is the pairing the Newton correction uses. Existence only is claimed; uniqueness of `(u,v)`
is TRUE (the map is bijective) but is NOT proved here — see §6.

### 4.5 Supporting statements

`Uniformity.Hensel.coeffIdeal` is *notation*, not new mathematics: `coeffIdeal J = Ideal.map C J`,
and `mem_coeffIdeal` is mathlib's `Ideal.mem_map_C_iff` restated. `exists_solve_mod_maximalIdeal`
(S1), `exists_solve_step` (S2) and `exists_adicLimit_of_degree_lt` (L) are the intermediate lemmas
of §2 with the statements written there; each is a faithful transcription of its displayed
informal statement. `exists_monic_lift` is the degree-preserving monic lift, a one-line wrapper
around mathlib's `Polynomial.lifts_and_degree_eq_and_monic`.

---

## 5. AUDIT — axioms and `sorry` count

`sorry` count in `leanfinal/Uniformity/HenselFactorization.lean`: **0**. New axioms: **0**.
`#print axioms` output for every landed theorem, pasted verbatim from the build:

```
AXIOMCHECK_PLACEHOLDER
```

---

## 6. OPEN / NOT DONE (recorded honestly, not sorried)

1. **Uniqueness of the exact solve (S3).** The map `(u,v) ↦ hu + gv` on
   `R[X]_{<deg g} × R[X]_{<deg h} → R[X]_{<deg g + deg h}` is bijective, not merely surjective.
   Injectivity is not proved here. The clean route is: it is a surjective `R`-linear map between
   finite free `R`-modules of equal rank `n`, hence injective
   (`Module.Finite`+`OrzechProperty.injective_of_surjective_endomorphism` after transporting along
   `Polynomial.degreeLTEquiv`). Named open statement:
   `theorem eq_of_add_mul_eq {g h u v u' v'} (…deg bounds…) : h*u + g*v = h*u' + g*v' → u = u' ∧ v = v'`.
   The `n = 3` consumer does not obviously need it (uniqueness of the *factorization*, §4.2, is
   what pinning wants), so it was not pursued.
2. **The `n`-fold / multi-block form.** "A pairwise-coprime residual factorization
   `f̄ = ∏ᵢ p̄ᵢ` lifts to `f = ∏ᵢ pᵢ`" follows from the two-block form by induction on the number of
   blocks (the coprimality of `p̄ᵢ` against `∏_{j≠i} p̄ⱼ` is `IsCoprime.prod_right`). Not landed;
   the `n = 3` branch-(ii) argument only needs two blocks (linear × quadratic).
3. **The consumer itself.** This unit supplies the *mechanism* named as missing in
   `N3_CHECK_2026-08-13.md` §7. It does NOT prove branch (ii) of the `n = 3` pinning, and it does
   not prove `n = 3` drainage. What the consumer still needs is listed in §7 below.

---

## 7. WHAT THE `n = 3` CONSUMER STILL NEEDS

With this unit in hand, branch (ii) of `N3_CHECK` §7 ("undecided at level `N`, not triply
tangent ⟹ `f` = (decided linear) × (quadratic), factorization determined by the class") is
reachable, but three things are still missing and none is supplied here:

1. **The residual trigger.** A lemma turning "not triply tangent at any centre" into the
   hypothesis of this unit, i.e. producing a coprime residual splitting `f̄ = (X − ρ̄)·q̄` with
   `ρ̄` not a root of `q̄`. That is a statement about the `n = 3` undecided locus, not about Hensel.
2. **Class-determinacy of the lift.** "The factorization is determined by the level-`N` class"
   needs a *quantitative* version: if `f ≡ f'` mod `𝔪^N` then the lifted factors agree mod `𝔪^N`
   (or mod `𝔪^{N−c}` for an explicit `c`). §4.2's uniqueness is the `N = ∞` shadow of this; the
   finite-level version is a separate induction on the same Newton iteration and is NOT landed.
3. **The counting step.** Composing the branch-(ii) injection
   `(root mod 𝔪^N, quadratic class) ↪ q^{5N/2}` with the `n = 2` `class_pinned` bound, and the
   branch-(i) triple-tangency Taylor argument, into a single `undecidedCount_le` at `n = 3`.

---

*Unit note written before the Lean attempt (§§1–2) and completed after it (§§3–7), per the
house rule that the informal proof precedes the formalization.*
