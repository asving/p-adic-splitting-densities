/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.L3

/-!
# LeanUrat.L3Squarefree — the squarefree monic count `Q^m - Q^{m-1}` (Theorem A)

This file proves `notes/L3_proof.md` Theorem A:

> Over `F_Q` (finite field, `Q = #F`), for `m ≥ 2` the number of squarefree monic polynomials of
> degree `m` is `Q^m - Q^{m-1}`.

This is the `sorry` `L3.card_squarefreeMonicDegree`; we re-prove its *statement* here as the theorem
`card_squarefreeMonicDegree` (the integration phase wires it into `L3`). We do **not** edit
`L3.lean`.

## Proof outline (the "`A · B²`" bijection, `notes/L3_proof.md §1.2`, Proof 1)

Every monic `R` of degree `n` factors **uniquely** as `R = A · B²` with `A` squarefree monic and `B`
monic (collect each irreducible `g` of multiplicity `e`: put `⌊e/2⌋` copies into `B` and the parity
`e % 2` copy into `A`). Counting by `deg B = j`, `deg A = n - 2j`:
`Q^n = #monic n = ∑_{2j ≤ n} S(n - 2j) · Q^j`   (`∗`)
using `L3.card_monicDegree`. Solving (`∗`) by strong induction gives `S(0) = 1`, `S(1) = Q`, and
`S(m) = Q^m - Q^{m-1}` for `m ≥ 2` (the inner sum telescopes via (`∗`) at degree `m - 2`).

mathlib has no squarefree-polynomial count; this is a from-scratch development. The decomposition
existence is by strong induction (a repeated irreducible factor `g²` peeled off), uniqueness by
`normalizedFactors` `count` arithmetic (`count = (parity in A) + 2·(mult in B)`, `parity < 2`).

The `NormalizationMonoid F` (hence `normalizedFactors`) needs `[DecidableEq F]`; over a finite field
this is supplied by `classical` inside each proof, and the statements are `Nat.card` equalities,
independent of that decidability choice.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.L3Squarefree

open Polynomial UniqueFactorizationMonoid

variable {F : Type*} [Field F] [Finite F]

/-! ## 1. Monic polynomials over a field: normalized factors are exactly the monic factorization -/

/-- For a monic polynomial over a field, the product of its `normalizedFactors` is the polynomial
itself (not merely up to associates): both are monic and associated, hence equal. -/
theorem prod_normalizedFactors_of_monic [DecidableEq F] {p : F[X]} (hp : p.Monic) (hp0 : p ≠ 0) :
    (normalizedFactors p).prod = p := by
  have hassoc : Associated (normalizedFactors p).prod p :=
    UniqueFactorizationMonoid.prod_normalizedFactors hp0
  have hmonprod : ((normalizedFactors p).prod).Monic := by
    have heq : ((normalizedFactors p).prod) = normalize p :=
      UniqueFactorizationMonoid.prod_normalizedFactors_eq hp0
    rw [heq, hp.normalize_eq_self]; exact hp
  exact eq_of_monic_of_associated hmonprod hp hassoc

/-! ## 2. Existence: every monic `R` factors as `A · B²` with `A` squarefree monic, `B` monic -/

/-- A monic irreducible polynomial has positive `natDegree`. -/
theorem natDegree_pos_of_irreducible {g : F[X]} (hg : Irreducible g) : 0 < g.natDegree := by
  refine Nat.pos_of_ne_zero fun h0 => hg.not_isUnit ?_
  -- natDegree 0 ⇒ g = C c, a unit or zero; irreducible rules both out
  exact Polynomial.isUnit_iff_degree_eq_zero.mpr
    (by rw [Polynomial.degree_eq_natDegree hg.ne_zero, h0]; rfl)

/-- **Decomposition existence.** Every monic `R` of degree `n` over `F` can be written as
`R = A * B^2` with `A` squarefree, `A` monic, `B` monic. By strong induction on `natDegree R`:
if `R` is squarefree take `(A,B) = (R,1)`; otherwise peel off a repeated monic irreducible factor
`g²`, recurse on `R / g²`, and absorb `g` into `B`. -/
theorem exists_sqfree_sq_decomp (R : F[X]) (hR : R.Monic) :
    ∃ A B : F[X], A.Monic ∧ Squarefree A ∧ B.Monic ∧ R = A * B ^ 2 := by
  classical
  -- strong induction on natDegree
  induction hn : R.natDegree using Nat.strong_induction_on generalizing R with
  | _ n ih =>
  subst hn
  by_cases hsf : Squarefree R
  · exact ⟨R, 1, hR, hsf, monic_one, by ring⟩
  · -- not squarefree: get an irreducible g with g*g ∣ R; normalize to monic
    have hR0 : R ≠ 0 := hR.ne_zero
    rw [squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hR0] at hsf
    push_neg at hsf
    obtain ⟨x, hx_irr, hx_dvd⟩ := hsf
    -- normalize x to a monic irreducible g, still g*g ∣ R
    set g : F[X] := normalize x with hg_def
    have hg_monic : g.Monic := monic_normalize hx_irr.ne_zero
    have hassoc : Associated x g := associated_normalize x
    have hg_irr : Irreducible g := hassoc.irreducible hx_irr
    -- write R = g^2 * C with C monic
    obtain ⟨C, hC⟩ := (hassoc.mul_mul hassoc).symm.dvd.trans hx_dvd
    have hRC : R = g ^ 2 * C := by rw [sq]; exact hC
    have hg2_monic : (g ^ 2).Monic := hg_monic.pow 2
    have hC_monic : C.Monic := hg2_monic.of_mul_monic_left (hRC ▸ hR)
    -- degree bookkeeping: natDegree C < natDegree R, then recurse on C
    have hgpos : 0 < g.natDegree := natDegree_pos_of_irreducible hg_irr
    have hClt : C.natDegree < R.natDegree := by
      rw [hRC, hg2_monic.natDegree_mul hC_monic, hg_monic.natDegree_pow 2]; omega
    obtain ⟨A, B, hA_monic, hA_sf, hB_monic, hCeq⟩ := ih C.natDegree hClt C hC_monic rfl
    exact ⟨A, g * B, hA_monic, hA_sf, hg_monic.mul hB_monic, by rw [hRC, hCeq]; ring⟩

/-! ## 3. Uniqueness of the `A · B²` decomposition -/

/-- For a monic poly `A` and monic poly `B`, the normalized-factor count of `A * B^2` at `g`
splits as `count g (nf A) + 2 * count g (nf B)`. -/
theorem count_normalizedFactors_mul_sq [DecidableEq F] {A B : F[X]} (hA0 : A ≠ 0) (hB0 : B ≠ 0)
    (g : F[X]) :
    (normalizedFactors (A * B ^ 2)).count g
      = (normalizedFactors A).count g + 2 * (normalizedFactors B).count g := by
  have hB2 : (B ^ 2) ≠ 0 := pow_ne_zero 2 hB0
  rw [normalizedFactors_mul hA0 hB2, normalizedFactors_pow, Multiset.count_add,
    Multiset.count_nsmul]

/-- **Decomposition uniqueness.** If `A * B^2 = A' * B'^2` with `A, A'` squarefree and `A, A', B, B'`
all monic, then `A = A'` and `B = B'`. Proof: comparing `normalizedFactors` counts at each monic
irreducible `g`, `count A + 2·count B = count A' + 2·count B'` with `count A, count A' ≤ 1` (square-
free ⇒ `Nodup`), so reduction mod 2 forces `count A = count A'`, hence `count B = count B'`. Then
the normalized-factor multisets agree (`Multiset.ext`) and the monic polys are their products. -/
theorem sqfree_sq_decomp_unique {A B A' B' : F[X]}
    (hA_monic : A.Monic) (hA_sf : Squarefree A) (hB_monic : B.Monic)
    (hA'_monic : A'.Monic) (hA'_sf : Squarefree A') (hB'_monic : B'.Monic)
    (heq : A * B ^ 2 = A' * B' ^ 2) :
    A = A' ∧ B = B' := by
  classical
  have hA0 : A ≠ 0 := hA_monic.ne_zero
  have hB0 : B ≠ 0 := hB_monic.ne_zero
  have hA'0 : A' ≠ 0 := hA'_monic.ne_zero
  have hB'0 : B' ≠ 0 := hB'_monic.ne_zero
  -- squarefree ⇒ count ≤ 1
  have hA_le1 : ∀ g, (normalizedFactors A).count g ≤ 1 := Multiset.nodup_iff_count_le_one.mp
    ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hA0).mp hA_sf)
  have hA'_le1 : ∀ g, (normalizedFactors A').count g ≤ 1 := Multiset.nodup_iff_count_le_one.mp
    ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hA'0).mp hA'_sf)
  -- count identity at each g: count A + 2·count B = count A' + 2·count B'
  have hcount : ∀ g, (normalizedFactors A).count g + 2 * (normalizedFactors B).count g
      = (normalizedFactors A').count g + 2 * (normalizedFactors B').count g := by
    intro g
    have h1 := count_normalizedFactors_mul_sq hA0 hB0 g
    rw [heq, count_normalizedFactors_mul_sq hA'0 hB'0 g] at h1
    omega
  -- from the count identity + bounds: count A = count A', count B = count B' (mod 2 argument)
  have hAcount : ∀ g, (normalizedFactors A).count g = (normalizedFactors A').count g :=
    fun g => by have := hcount g; have := hA_le1 g; have := hA'_le1 g; omega
  have hBcount : ∀ g, (normalizedFactors B).count g = (normalizedFactors B').count g :=
    fun g => by have := hcount g; have := hAcount g; omega
  refine ⟨?_, ?_⟩
  · rw [← prod_normalizedFactors_of_monic hA_monic hA0,
        ← prod_normalizedFactors_of_monic hA'_monic hA'0, Multiset.ext.mpr hAcount]
  · rw [← prod_normalizedFactors_of_monic hB_monic hB0,
        ← prod_normalizedFactors_of_monic hB'_monic hB'0, Multiset.ext.mpr hBcount]

/-! ## 4. Finiteness of the count sets

`monicDegree F m` and `squarefreeMonicDegree F m` are finite (so `Nat.card` is a genuine count):
`degreeLT F m` is a finite-dimensional space over the finite field `F`, hence a finite type
(`Module.finite_of_finite`); `monicDegree F m` injects into `degreeLT F (m+1)` (a monic of degree
`m` has degree `< m+1`), and `squarefreeMonicDegree F m ⊆ monicDegree F m`. -/

open LeanUrat.L3

instance instFiniteDegreeLT (m : ℕ) : Finite (Polynomial.degreeLT F m) := by
  have : Module.Finite F (Polynomial.degreeLT F m) :=
    Module.Finite.of_basis (degreeLT.basis F m)
  exact Module.finite_of_finite F

instance instFiniteMonicDegree (m : ℕ) : Finite (monicDegree F m) := by
  apply Finite.of_injective (β := Polynomial.degreeLT F (m+1))
    (f := fun p : monicDegree F m =>
      (⟨(p : F[X]), by
        have hp : (p : F[X]).Monic ∧ (p : F[X]).natDegree = m := p.2
        rw [mem_degreeLT]
        have hp0 : (p : F[X]) ≠ 0 := hp.1.ne_zero
        rw [degree_eq_natDegree hp0, hp.2]
        exact_mod_cast Nat.lt_succ_self m⟩ : Polynomial.degreeLT F (m+1)))
  intro a b hab
  simp only [Subtype.mk.injEq] at hab
  exact Subtype.ext hab

instance instFiniteSquarefreeMonicDegree (m : ℕ) : Finite (squarefreeMonicDegree F m) := by
  apply Finite.of_injective (β := monicDegree F m)
    (f := fun p : squarefreeMonicDegree F m =>
      (⟨(p : F[X]), by
        have hp : (p : F[X]).Monic ∧ (p : F[X]).natDegree = m ∧ Squarefree (p : F[X]) := p.2
        exact ⟨hp.1, hp.2.1⟩⟩ : monicDegree F m))
  intro a b hab
  simp only [Subtype.mk.injEq] at hab
  exact Subtype.ext hab

/-! ## 5. The `A · B²` counting bijection and the recursion `(∗)`

`assemble` maps `(A, B)` (with `deg A = n - 2j`, `deg B = j`, `j ≤ n/2`) to `A · B²`, a monic of
degree `n`. By `exists_sqfree_sq_decomp` (surjective) and `sqfree_sq_decomp_unique` (injective) it
is a bijection of `Σ_{2j ≤ n} {sqfree monic deg (n-2j)} × {monic deg j}` onto `{monic deg n}`.
Transporting `Nat.card` through `Nat.card_sigma`/`card_prod`/`card_monicDegree` gives the recursion
`(∗) : Q^n = ∑_{2j ≤ n} S(n-2j) · Q^j`, solved to `S(m) = Q^m - Q^{m-1}` for `m ≥ 2`. -/

/-- The index type for the `A·B²` bijection: pairs `(A,B)` with `deg A = n - 2j`, `deg B = j`,
`j ≤ n/2`. -/
abbrev PairIdx (F : Type*) [Field F] (n : ℕ) :=
  Σ j : Fin (n/2 + 1), squarefreeMonicDegree F (n - 2 * (j : ℕ)) × monicDegree F (j : ℕ)

/-- The backward map `(A, B) ↦ A · B²` of the `A·B²` bijection (monic of degree `n`). -/
noncomputable def assemble (n : ℕ) : PairIdx F n → monicDegree F n :=
  fun x =>
    ⟨(x.2.1 : F[X]) * (x.2.2 : F[X]) ^ 2, by
      obtain ⟨j, ⟨A, hA⟩, ⟨B, hB⟩⟩ := x
      have hA' : A.Monic ∧ A.natDegree = n - 2 * (j : ℕ) ∧ Squarefree A := hA
      have hB' : B.Monic ∧ B.natDegree = (j : ℕ) := hB
      obtain ⟨hAm, hAd, hAsf⟩ := hA'
      obtain ⟨hBm, hBd⟩ := hB'
      have hjle : (j : ℕ) ≤ n / 2 := Nat.lt_succ_iff.mp j.2
      have h2j : 2 * (j : ℕ) ≤ n := by omega
      have hB2m : (B ^ 2).Monic := hBm.pow 2
      have hABm : (A * B ^ 2).Monic := hAm.mul hB2m
      refine ⟨hABm, ?_⟩
      have hdeg : (A * B ^ 2).natDegree = A.natDegree + (B ^ 2).natDegree := hAm.natDegree_mul hB2m
      have hB2deg : (B ^ 2).natDegree = 2 * B.natDegree := hBm.natDegree_pow 2
      rw [hdeg, hB2deg, hAd, hBd]
      omega⟩

/-- `assemble` is a bijection: injective by `sqfree_sq_decomp_unique`, surjective by
`exists_sqfree_sq_decomp`. -/
theorem assemble_bijective (n : ℕ) : Function.Bijective (assemble (F := F) n) := by
  constructor
  · rintro ⟨j₁, ⟨A₁, hA₁⟩, ⟨B₁, hB₁⟩⟩ ⟨j₂, ⟨A₂, hA₂⟩, ⟨B₂, hB₂⟩⟩ heq
    have hA₁' : A₁.Monic ∧ A₁.natDegree = n - 2 * (j₁ : ℕ) ∧ Squarefree A₁ := hA₁
    have hA₂' : A₂.Monic ∧ A₂.natDegree = n - 2 * (j₂ : ℕ) ∧ Squarefree A₂ := hA₂
    have hB₁' : B₁.Monic ∧ B₁.natDegree = (j₁ : ℕ) := hB₁
    have hB₂' : B₂.Monic ∧ B₂.natDegree = (j₂ : ℕ) := hB₂
    obtain ⟨hA₁m, hA₁d, hA₁sf⟩ := hA₁'
    obtain ⟨hA₂m, hA₂d, hA₂sf⟩ := hA₂'
    obtain ⟨hB₁m, hB₁d⟩ := hB₁'
    obtain ⟨hB₂m, hB₂d⟩ := hB₂'
    have hval : A₁ * B₁ ^ 2 = A₂ * B₂ ^ 2 := congrArg Subtype.val heq
    obtain ⟨hAeq, hBeq⟩ := sqfree_sq_decomp_unique hA₁m hA₁sf hB₁m hA₂m hA₂sf hB₂m hval
    have hjeq : (j₁ : ℕ) = (j₂ : ℕ) := by rw [← hB₁d, ← hB₂d, hBeq]
    have hj : j₁ = j₂ := Fin.ext hjeq
    subst hj
    subst hAeq
    subst hBeq
    rfl
  · rintro ⟨R, hR⟩
    have hR' : R.Monic ∧ R.natDegree = n := hR
    obtain ⟨hRm, hRd⟩ := hR'
    obtain ⟨A, B, hAm, hAsf, hBm, hRfac⟩ := exists_sqfree_sq_decomp R hRm
    have hB2m : (B ^ 2).Monic := hBm.pow 2
    have hdeg : R.natDegree = A.natDegree + (B ^ 2).natDegree := hRfac ▸ hAm.natDegree_mul hB2m
    have hB2deg : (B ^ 2).natDegree = 2 * B.natDegree := hBm.natDegree_pow 2
    have hsum : A.natDegree + 2 * B.natDegree = n := by rw [← hRd, hdeg, hB2deg]
    have hjle : B.natDegree ≤ n / 2 := by omega
    refine ⟨⟨⟨B.natDegree, Nat.lt_succ_iff.mpr hjle⟩,
      ⟨A, show A.Monic ∧ A.natDegree = n - 2 * B.natDegree ∧ Squarefree A from
        ⟨hAm, by omega, hAsf⟩⟩,
      ⟨B, show B.Monic ∧ B.natDegree = B.natDegree from ⟨hBm, rfl⟩⟩⟩, ?_⟩
    apply Subtype.ext
    change A * B ^ 2 = R
    rw [hRfac]

/-- The sigma-cardinality splits as the sum (`Nat.card_sigma` + `Nat.card_prod` +
`L3.card_monicDegree`). -/
theorem card_pairIdx (n : ℕ) :
    Nat.card (PairIdx F n)
      = ∑ j : Fin (n/2+1),
          Nat.card (squarefreeMonicDegree F (n - 2*(j:ℕ))) * Nat.card F ^ (j:ℕ) := by
  rw [Nat.card_sigma]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Nat.card_prod, card_monicDegree]

/-- **The count recursion `(∗)`**: `Q^n = ∑_{j ≤ n/2} S(n-2j) · Q^j`, where
`S(k) = #{squarefree monic deg k}` and `Q = #F`. -/
theorem sum_identity (n : ℕ) :
    ∑ j ∈ Finset.range (n/2+1),
        Nat.card (squarefreeMonicDegree F (n - 2*j)) * Nat.card F ^ j = Nat.card F ^ n := by
  have h1 : Nat.card (PairIdx F n) = Nat.card F ^ n := by
    rw [Nat.card_eq_of_bijective (assemble (F := F) n) (assemble_bijective n), card_monicDegree]
  rw [← h1, card_pairIdx,
    Fin.sum_univ_eq_sum_range
      (fun j => Nat.card (squarefreeMonicDegree F (n - 2*j)) * Nat.card F ^ j) (n/2+1)]

/-- The recursion `(∗)` solved at degree `m ≥ 2`: `S(m) + Q^{m-1} = Q^m`. The `j = 0` term of
`(∗) at m` is `S(m)`; the tail equals `Q · (∗ at m-2) = Q · Q^{m-2} = Q^{m-1}` (the inner sum
re-indexes to `(∗)` at degree `m-2` since `m/2 = (m-2)/2 + 1`). -/
theorem S_recursion (m : ℕ) (hm : 2 ≤ m) :
    Nat.card (squarefreeMonicDegree F m) + Nat.card F ^ (m-1) = Nat.card F ^ m := by
  have key := sum_identity (F := F) m
  have key2 := sum_identity (F := F) (m-2)
  rw [Finset.sum_range_succ'
      (fun j => Nat.card (squarefreeMonicDegree F (m - 2*j)) * Nat.card F ^ j) (m/2)] at key
  have hrange : m / 2 = (m-2)/2 + 1 := by omega
  have htail : (∑ k ∈ Finset.range (m/2),
        Nat.card (squarefreeMonicDegree F (m - 2*(k+1))) * Nat.card F ^ (k+1))
      = Nat.card F * (∑ k ∈ Finset.range ((m-2)/2+1),
          Nat.card (squarefreeMonicDegree F ((m-2) - 2*k)) * Nat.card F ^ k) := by
    rw [Finset.mul_sum, hrange]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [Finset.mem_range] at hk
    have hidx : m - 2*(k+1) = (m-2) - 2*k := by omega
    rw [hidx, pow_succ]
    ring
  rw [htail, key2] at key
  have hpow : Nat.card F * Nat.card F ^ (m-2) = Nat.card F ^ (m-1) := by
    rw [← pow_succ']
    congr 1
    omega
  simp only [Nat.mul_zero, Nat.sub_zero, pow_zero, Nat.mul_one] at key
  rw [hpow] at key
  omega

/-- **Theorem A (squarefree monic count, `notes/L3_proof.md §1.2`).** Over a finite field `F` with
`Q = #F` elements, for `m ≥ 2` the number of squarefree monic polynomials of degree `m` is
`Q^m - Q^{m-1}`. This is exactly the statement of the open `L3.card_squarefreeMonicDegree`,
re-proved here (`L3Squarefree` imports `L3`, so wiring it back into `L3` would create an import
cycle; the proved theorem lives here and `L3.card_squarefreeMonicDegree` should be updated to
`exact L3Squarefree.card_squarefreeMonicDegree m hm` in a later integration pass that moves the
statement out of `L3`). -/
theorem card_squarefreeMonicDegree (m : ℕ) (hm : 2 ≤ m) :
    Nat.card (squarefreeMonicDegree F m) = Nat.card F ^ m - Nat.card F ^ (m - 1) := by
  have h := S_recursion (F := F) m hm
  omega

end LeanUrat.L3Squarefree
