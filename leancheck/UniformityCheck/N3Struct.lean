/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import UniformityCheck.N3Gates

/-!
# UniformityCheck.N3Struct — the `n = 3` STRUCTURE THEOREM and the branch-(b) peel

Two things, both prerequisites for drainage at `n = 3` (`N3Drain`).

## 1. The residue trichotomy (`cubic_trichotomy`, `cubic_structure`)

Over a field `K`, a monic cubic `F = X³ + c₂X² + c₁X + c₀` satisfies exactly one of the
following (the covering is `cubic_trichotomy`, the pairwise exclusivity is
`cubic_trichotomy_disjoint`; only the covering is used downstream):

* **(T1)** `F` has a SIMPLE root: `F(ρ) = 0` and `F′(ρ) ≠ 0` for some `ρ ∈ K`;
* **(T2)** `F` has NO root in `K` (`NoRootCubic`, equivalent to irreducibility in degree 3);
* **(T3)** `F = (X − γ)³` for a unique `γ` (`cubeCoeff γ` is its coefficient vector).

The proof is elementary and characteristic-free: if `ρ` is a root with `F′(ρ) = 0` then
`F = (X − ρ)²(X − s)` with `s = −c₂ − 2ρ`, and `F′(s) = (s − ρ)²`, so either `s` is a simple
root or `s = ρ` and `F = (X − ρ)³`.

This is the enumeration that `N3_CHECK` §7 asked for and the Hensel unit's §4.5/§7 retraction
predicted. It CONFIRMS the retraction: the only residual shape without a simple root that is not
already decided (irreducible cubics are decided at level 1) is the perfect cube. There is no
third genre.

## 2. Branch (b): the peel is LOSSLESS (`exists_root_congr`, `decidedAt_of_peel`)

If `F_a(r) = 0` with `F_a′(r)` a UNIT, then for every `a′ ≡ a (mod π^N)` the perturbed cubic has
a root `r′ ≡ r (mod π^N)` — the same `N`, no digits lost — because the exact expansion
`0 = F_{a′}(r + δ) = F_{a′}(r) + δ·(unit)` forces `v(δ) = v(F_{a′}(r)) ≥ N`. Consequently the
quadratic cofactors agree mod `π^N`, and `n = 3` decidedness at level `N` follows from `n = 2`
decidedness at level `N`:

    ¬ ∃ γ, Tang π (peel a r) N γ   ⟹   the level-`N` class of `a` is decided

(`decidedAt_of_peel`), with type `{(1,1)} ∪ typeOf (monicPoly (peel a r))`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace UniformityCheck

open Uniformity Uniformity.Density IsLocalRing Polynomial

/-! ## 1. The residue trichotomy -/

section Trich

variable {K : Type*} [Field K]

/-- The coefficient vector of `(X − γ)³`, in the `monicPoly` convention
`X³ + c₂X² + c₁X + c₀`. -/
def cubeCoeff (γ : K) : Fin 3 → K := ![-(γ ^ 3), 3 * γ ^ 2, -(3 * γ)]

@[simp] theorem cubeCoeff_zero (γ : K) : cubeCoeff γ 0 = -(γ ^ 3) := rfl
@[simp] theorem cubeCoeff_one (γ : K) : cubeCoeff γ 1 = 3 * γ ^ 2 := rfl
@[simp] theorem cubeCoeff_two (γ : K) : cubeCoeff γ 2 = -(3 * γ) := rfl

/-- The value at `x` of the monic cubic with coefficient vector `c`. -/
def cVal (c : Fin 3 → K) (x : K) : K := x ^ 3 + c 2 * x ^ 2 + c 1 * x + c 0

/-- The derivative at `x` of the monic cubic with coefficient vector `c`. -/
def cDer (c : Fin 3 → K) (x : K) : K := 3 * x ^ 2 + 2 * c 2 * x + c 1

theorem noRootCubic_iff (c : Fin 3 → K) : NoRootCubic c ↔ ∀ y : K, cVal c y ≠ 0 := Iff.rfl

@[simp] theorem cVal_cubeCoeff (γ x : K) : cVal (cubeCoeff γ) x = (x - γ) ^ 3 := by
  simp only [cVal, cubeCoeff_zero, cubeCoeff_one, cubeCoeff_two]; ring

@[simp] theorem cDer_cubeCoeff (γ x : K) : cDer (cubeCoeff γ) x = 3 * (x - γ) ^ 2 := by
  simp only [cDer, cubeCoeff_one, cubeCoeff_two]; ring

/-- `(X − γ)³ = (X − γ′)³` forces `γ = γ′`, in every characteristic (in characteristic `3` the
first two coefficients carry no information and the cube root is used instead). -/
theorem cubeCoeff_injective : Function.Injective (cubeCoeff (K := K)) := by
  intro γ γ' h
  have h0 : -(γ ^ 3) = -(γ' ^ 3) := congrFun h 0
  have h1 : 3 * γ ^ 2 = 3 * γ' ^ 2 := congrFun h 1
  have h2 : -(3 * γ) = -(3 * γ') := congrFun h 2
  have hcube : (γ - γ') ^ 3 = 0 := by
    linear_combination (-1 : K) * h0 - γ' * h1 - γ' ^ 2 * h2
  have hz := pow_eq_zero_iff (n := 3) (by norm_num) |>.1 hcube
  exact sub_eq_zero.1 hz

/-- **THE RESIDUE TRICHOTOMY.** Every monic cubic over a field has a simple root, or no root at
all, or is a perfect cube. Characteristic-free. -/
theorem cubic_trichotomy (c : Fin 3 → K) :
    (∃ ρ : K, cVal c ρ = 0 ∧ cDer c ρ ≠ 0) ∨ NoRootCubic c ∨ (∃ γ : K, c = cubeCoeff γ) := by
  by_cases hroot : ∃ ρ : K, cVal c ρ = 0
  swap
  · exact Or.inr (Or.inl (fun y hy => hroot ⟨y, hy⟩))
  obtain ⟨ρ, hρ⟩ := hroot
  by_cases hd : cDer c ρ = 0
  · -- `ρ` is a multiple root: `F = (X − ρ)²(X − s)` with `s = −c₂ − 2ρ`
    simp only [cVal] at hρ
    simp only [cDer] at hd
    by_cases hsρ : -(c 2) - 2 * ρ = ρ
    · -- the third root coincides: `F = (X − ρ)³`
      refine Or.inr (Or.inr ⟨ρ, ?_⟩)
      have h2 : c 2 = -(3 * ρ) := by linear_combination -hsρ
      have h1 : c 1 = 3 * ρ ^ 2 := by linear_combination hd - 2 * ρ * h2
      have h0 : c 0 = -(ρ ^ 3) := by linear_combination hρ - ρ * h1 - ρ ^ 2 * h2
      funext i
      fin_cases i
      · simpa using h0
      · simpa using h1
      · simpa using h2
    · -- the third root is different, hence simple
      refine Or.inl ⟨-(c 2) - 2 * ρ, ?_, ?_⟩
      · simp only [cVal]
        linear_combination hρ + (-(c 2) - 3 * ρ) * hd
      · have hval : cDer c (-(c 2) - 2 * ρ) = (-(c 2) - 2 * ρ - ρ) ^ 2 := by
          simp only [cDer]; linear_combination hd
        rw [hval]
        exact pow_ne_zero 2 (sub_ne_zero.2 hsρ)
  · exact Or.inl ⟨ρ, hρ, hd⟩

/-- **The three branches are pairwise EXCLUSIVE**, so `cubic_trichotomy` really is a
trichotomy and not merely a covering. (A perfect cube `(X − γ)³` has value `(x − γ)³` and
derivative `3(x − γ)²`, so its only root is `γ` and there the derivative vanishes.) -/
theorem cubic_trichotomy_disjoint (c : Fin 3 → K) :
    ¬ ((∃ ρ : K, cVal c ρ = 0 ∧ cDer c ρ ≠ 0) ∧ NoRootCubic c)
    ∧ ¬ ((∃ ρ : K, cVal c ρ = 0 ∧ cDer c ρ ≠ 0) ∧ (∃ γ : K, c = cubeCoeff γ))
    ∧ ¬ (NoRootCubic c ∧ (∃ γ : K, c = cubeCoeff γ)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨⟨ρ, hv, -⟩, hno⟩
    exact hno ρ hv
  · rintro ⟨⟨ρ, hv, hd⟩, γ, rfl⟩
    rw [cVal_cubeCoeff] at hv
    have hz : ρ - γ = 0 := pow_eq_zero_iff (n := 3) (by norm_num) |>.1 hv
    rw [cDer_cubeCoeff, hz] at hd
    simp at hd
  · rintro ⟨hno, γ, rfl⟩
    have h : cVal (cubeCoeff γ) γ = 0 := by rw [cVal_cubeCoeff]; ring
    exact hno γ h

end Trich

/-! ## 2. The trichotomy over `O`, with the simple residue root already Hensel-lifted -/

section OTrich

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]

/-- **THE `n = 3` STRUCTURE THEOREM.** Every monic cubic over a complete DVR either has a root
in `O` at which the derivative is a UNIT (so it peels, losslessly — see `decidedAt_of_peel`), or
is residually rootless (so it is `{(1,3)}`-decided at level 1), or is residually a perfect
cube (the triple-root stratum). -/
theorem cubic_structure (a : Fin 3 → O) :
    (∃ r : O, (monicPoly a).eval r = 0 ∧ IsUnit ((monicPoly a).derivative.eval r))
      ∨ NoRootCubic (resVec a)
      ∨ (∃ γ : O, resVec a = cubeCoeff (residue O γ)) := by
  rcases cubic_trichotomy (resVec a) with ⟨ρbar, hval, hder⟩ | hno | ⟨γbar, hγ⟩
  · obtain ⟨ρ, hρ⟩ := IsLocalRing.residue_surjective (R := O) ρbar
    have hv : ρ ^ 3 + a 2 * ρ ^ 2 + a 1 * ρ + a 0 ∈ maximalIdeal O := by
      rw [← IsLocalRing.residue_eq_zero_iff]
      simp only [map_add, map_mul, map_pow, hρ]
      simpa [cVal, resVec] using hval
    have hu : IsUnit (3 * ρ ^ 2 + 2 * a 2 * ρ + a 1) := by
      refine notMem_maximalIdeal.1 (fun hmem => hder ?_)
      have h := (IsLocalRing.residue_eq_zero_iff _).2 hmem
      simp only [map_add, map_mul, map_pow, map_ofNat, hρ] at h
      simpa [cDer, resVec] using h
    obtain ⟨r, hr, hrρ⟩ := exists_cubic_root a ρ hv hu
    refine Or.inl ⟨r, hr, ?_⟩
    rw [cubic_deriv_eval]
    refine notMem_maximalIdeal.1 (fun hmem => ?_)
    have hbad : 3 * ρ ^ 2 + 2 * a 2 * ρ + a 1 ∈ maximalIdeal O := by
      have hid : 3 * ρ ^ 2 + 2 * a 2 * ρ + a 1
          = (3 * r ^ 2 + 2 * a 2 * r + a 1) - (r - ρ) * (3 * (r + ρ) + 2 * a 2) := by ring
      rw [hid]
      exact Ideal.sub_mem _ hmem (Ideal.mul_mem_right _ _ hrρ)
    exact absurd hbad (notMem_maximalIdeal.2 hu)
  · exact Or.inr (Or.inl hno)
  · obtain ⟨γ, hγ'⟩ := IsLocalRing.residue_surjective (R := O) γbar
    exact Or.inr (Or.inr ⟨γ, by rw [hγ, hγ']⟩)

end OTrich

/-! ## 3. Branch (b): the peel is lossless -/

section Peel

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- Coefficientwise congruence mod `π ^ N` is exactly equality of level-`N` classes. -/
theorem proj_of_dvd {π : O} (hπ : Irreducible π) {n N : ℕ} {a b : Fin n → O}
    (h : ∀ i, π ^ N ∣ (b i - a i)) : proj O n N a = proj O n N b := by
  funext i
  exact Ideal.Quotient.eq.2 ((mem_maximalIdeal_pow_iff_dvd hπ N _).2 (dvd_sub_comm.1 (h i)))

/-- **The Hensel root moves no further than the coefficients do.** If `r` is a root of `F_a` at
which the derivative is a unit and `a′ ≡ a (mod π^N)` (`N ≥ 1`), then `F_{a′}` has a root
`r′ ≡ r (mod π^N)`: the SAME `N`. The mechanism is the exact cubic expansion
`0 = F_{a′}(r) + δ·(unit)`, so `v(δ) = v(F_{a′}(r)) ≥ N`. -/
theorem exists_root_congr {π : O} (hπ : Irreducible π) {a a' : Fin 3 → O} {N : ℕ} (hN : 1 ≤ N)
    {r : O} (hr : (monicPoly a).eval r = 0) (hu : IsUnit ((monicPoly a).derivative.eval r))
    (hcong : ∀ i, π ^ N ∣ (a' i - a i)) :
    ∃ r' : O, (monicPoly a').eval r' = 0 ∧ π ^ N ∣ (r' - r) := by
  rw [cubic_deriv_eval] at hu
  rw [cubic_eval] at hr
  -- the perturbed value at the old root is deep
  have hE : π ^ N ∣ (r ^ 3 + a' 2 * r ^ 2 + a' 1 * r + a' 0) := by
    have hid : r ^ 3 + a' 2 * r ^ 2 + a' 1 * r + a' 0
        = (a' 2 - a 2) * r ^ 2 + (a' 1 - a 1) * r + (a' 0 - a 0)
          + (r ^ 3 + a 2 * r ^ 2 + a 1 * r + a 0) := by ring
    rw [hid, hr, add_zero]
    exact dvd_add (dvd_add ((hcong 2).mul_right _) ((hcong 1).mul_right _)) (hcong 0)
  -- the perturbed derivative at the old root is still a unit
  have hu' : IsUnit (3 * r ^ 2 + 2 * a' 2 * r + a' 1) := by
    refine notMem_maximalIdeal.1 (fun hmem => ?_)
    have hshift : (2 : O) * (a' 2 - a 2) * r + (a' 1 - a 1) ∈ maximalIdeal O := by
      refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ ?_) ?_
      · have h2 : π ∣ (a' 2 - a 2) := dvd_trans (dvd_pow_self π (by omega : N ≠ 0)) (hcong 2)
        exact Ideal.mul_mem_left _ _ ((mem_maximalIdeal_iff_dvd hπ _).2 h2)
      · exact (mem_maximalIdeal_iff_dvd hπ _).2
          (dvd_trans (dvd_pow_self π (by omega : N ≠ 0)) (hcong 1))
    have hbad : 3 * r ^ 2 + 2 * a 2 * r + a 1 ∈ maximalIdeal O := by
      have hid : 3 * r ^ 2 + 2 * a 2 * r + a 1
          = (3 * r ^ 2 + 2 * a' 2 * r + a' 1) - (2 * (a' 2 - a 2) * r + (a' 1 - a 1)) := by ring
      rw [hid]
      exact Ideal.sub_mem _ hmem hshift
    exact absurd hbad (notMem_maximalIdeal.2 hu)
  -- ordinary Hensel: a root `r′ ≡ r (mod 𝔪)`
  obtain ⟨r', hr', hδ⟩ := exists_cubic_root a' r
    ((mem_maximalIdeal_iff_dvd hπ _).2 (dvd_trans (dvd_pow_self π (by omega)) hE)) hu'
  refine ⟨r', hr', ?_⟩
  rw [cubic_eval] at hr'
  -- the exact expansion: `0 = E + δ·U` with `U` a unit
  set δ := r' - r with hδdef
  have hU : IsUnit ((3 * r ^ 2 + 2 * a' 2 * r + a' 1) + (3 * r + a' 2) * δ + δ ^ 2) := by
    refine notMem_maximalIdeal.1 (fun hmem => ?_)
    have hsmall : (3 * r + a' 2) * δ + δ ^ 2 ∈ maximalIdeal O := by
      refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hδ) ?_
      rw [pow_two]
      exact Ideal.mul_mem_left _ _ hδ
    have hbad : 3 * r ^ 2 + 2 * a' 2 * r + a' 1 ∈ maximalIdeal O := by
      have hid : 3 * r ^ 2 + 2 * a' 2 * r + a' 1
          = ((3 * r ^ 2 + 2 * a' 2 * r + a' 1) + (3 * r + a' 2) * δ + δ ^ 2)
            - ((3 * r + a' 2) * δ + δ ^ 2) := by ring
      rw [hid]
      exact Ideal.sub_mem _ hmem hsmall
    exact absurd hbad (notMem_maximalIdeal.2 hu')
  have hexp : δ * ((3 * r ^ 2 + 2 * a' 2 * r + a' 1) + (3 * r + a' 2) * δ + δ ^ 2)
      = -(r ^ 3 + a' 2 * r ^ 2 + a' 1 * r + a' 0) := by
    rw [hδdef]
    linear_combination hr'
  have hdvd : π ^ N ∣ δ * ((3 * r ^ 2 + 2 * a' 2 * r + a' 1) + (3 * r + a' 2) * δ + δ ^ 2) := by
    rw [hexp]
    exact hE.neg_right
  exact dvd_of_isUnit_mul hU (by rwa [mul_comm] at hdvd)

/-- The quadratic cofactors of two congruent cubics, at their respective roots, are congruent —
with the same modulus. -/
theorem peel_congr {π : O} {a a' : Fin 3 → O} {N : ℕ} {r r' : O}
    (hcong : ∀ i, π ^ N ∣ (a' i - a i)) (hrr : π ^ N ∣ (r' - r)) :
    ∀ i, π ^ N ∣ (peel a' r' i - peel a r i) := by
  intro i
  fin_cases i
  · show π ^ N ∣ (peel a' r' 0 - peel a r 0)
    simp only [peel_zero]
    have hid : (a' 1 + a' 2 * r' + r' ^ 2) - (a 1 + a 2 * r + r ^ 2)
        = (a' 1 - a 1) + (a' 2 - a 2) * r' + a 2 * (r' - r) + (r' - r) * (r' + r) := by ring
    rw [hid]
    exact dvd_add (dvd_add (dvd_add (hcong 1) ((hcong 2).mul_right _)) (hrr.mul_left _))
      (hrr.mul_right _)
  · show π ^ N ∣ (peel a' r' 1 - peel a r 1)
    simp only [peel_one]
    have hid : (a' 2 + r') - (a 2 + r) = (a' 2 - a 2) + (r' - r) := by ring
    rw [hid]
    exact dvd_add (hcong 2) hrr

/-- **LEMMA B — BRANCH (b) DECIDEDNESS.** If the cubic has a root `r` with unit derivative and
the quadratic cofactor `peel a r` has NO centre of tangency depth `N`, the level-`N` class of
`a` is decided. `n = 3` decidedness is reduced to `n = 2` decidedness at the SAME level. -/
theorem decidedAt_of_peel {π : O} (hπ : Irreducible π) {a : Fin 3 → O} {N : ℕ} (hN : 1 ≤ N)
    {r : O} (hr : (monicPoly a).eval r = 0) (hu : IsUnit ((monicPoly a).derivative.eval r))
    (hT : ¬ ∃ γ : O, Tang π (peel a r) N γ) :
    DecidedAt O 3 (typeOf (monicPoly a)) N (proj O 3 N a) := by
  intro a' ha'
  have hcong : ∀ i, π ^ N ∣ (a' i - a i) := fun i => dvd_sub_comm.1 (proj3_dvd hπ ha' i)
  obtain ⟨r', hr', hrr⟩ := exists_root_congr hπ hN hr hu hcong
  have hpeel := peel_congr (π := π) (N := N) hcong hrr
  have hproj : proj O 2 N (peel a r) = proj O 2 N (peel a' r') := proj_of_dvd hπ hpeel
  have hdec := decidedAt_of_not_tang (O := O) (a := peel a r) (N := N) hπ hT
  have htype : typeOf (monicPoly (peel a' r')) = typeOf (monicPoly (peel a r)) :=
    hdec (peel a' r') hproj.symm
  apply FactorizationType.ext
  rw [cubic_peel a' r' hr', typeOf_linear_mul (monicPoly_monic (peel a' r')) r', htype,
    cubic_peel a r hr, typeOf_linear_mul (monicPoly_monic (peel a r)) r]

end Peel

#print axioms UniformityCheck.cubic_trichotomy
#print axioms UniformityCheck.cubic_trichotomy_disjoint
#print axioms UniformityCheck.cubeCoeff_injective
#print axioms UniformityCheck.cubic_structure
#print axioms UniformityCheck.exists_root_congr
#print axioms UniformityCheck.decidedAt_of_peel

end UniformityCheck
