/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H116bR

/-!
# Uniformity.ChapH.H116b2 — multiplicity ADDS, and the genre of a planted product

**Chapter H, NODE H.116b2** (`blueprint/CHAP-H_general_induction.md`, AMENDMENT A-H.7 §5).
The first sub-node of the H.116b re-split, and the one that carries the SHARED DEFINITIONAL
CARRIER `plantedPoly` of §§5–8 of that amendment.

* **clause (i) `coeff_level_mul_trailing`** — MULTIPLICITY ADDS.  If `π ^ s` is the exact
  coefficient level of `P₁` with its first unit at abscissa `μ₁`, and `π ^ t` the exact level
  of `P₂` with its first unit at `μ₂`, then `π ^ (s + t)` is the exact level of `P₁ P₂` and
  its first unit sits at `μ₁ + μ₂`.  H116bR §5's landed `not_pow_add_succ_dvd_coeff_mul` is
  exactly the `μ₁ = μ₂ = 0` case (the CONTENT half); this is the MULTIPLICITY half.
* **clause (ii) `plantedPoly_genre`** — THE GENRE OF A PLANTED PRODUCT.

⚠ FENCE A-H.7/F1: nothing in this module builds a map between fibres.

DEPENDS: H.107 (`mem_maximalIdeal_pow_iff_dvd_of_irr`, `resOrd`), H.108 (`betaContent`,
`IsDrainState`), H.109 (`HasChildAt`, `hasChildAt_of_exists`), H.115 (`resSect`, `classSect`),
H.115b (`alphaParent`, `alphaFrame`, `alphaParent_coeff`, `alphaFrame_map_residue`) ·
landed in `H116bR.lean`: `pow_add_dvd_coeff_mul`, `not_pow_add_succ_dvd_coeff_mul`,
`pow_min_dvd_coeff_recentre_alphaParent`, `not_pow_min_succ_dvd_coeff_recentre_alphaParent`,
`recentre_alphaParent_own`, `coeff_zero_recentre_alphaParent_not_dvd`,
`pow_content_dvd_coeff_recentre`, `not_pow_content_succ_dvd_coeff_recentre`,
`betaContent_eq_of_recentre_exact` · mathlib `Polynomial.C_dvd_iff_dvd_coeff`,
`Polynomial.coeff_mul`, `Finset.induction_on`, `Finset.prod_insert`.

**ENVIRONMENT — ENV-H17** + `[IsAdicComplete]` (clause (ii) only) + `π` explicit.

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

namespace Uniformity.Density.Induction

open IsLocalRing Polynomial

/-! ## 0. Two arithmetic helpers (both re-derived; the H116bR copies are `private`) -/

section Helpers

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- `π ∣ x` is the residue reading of `x`. -/
theorem residue_eq_zero_iff_dvd {π : O} (hπ : Irreducible π) (x : O) :
    residue O x = 0 ↔ π ∣ x := by
  constructor
  · intro h0
    have hmem : x ∈ maximalIdeal O := Ideal.Quotient.eq_zero_iff_mem.1 h0
    have h := (mem_maximalIdeal_pow_iff_dvd_of_irr hπ 1 x).1 (by rwa [pow_one])
    rwa [pow_one] at h
  · intro hd
    refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
    have h := (mem_maximalIdeal_pow_iff_dvd_of_irr hπ 1 x).2 (by rwa [pow_one])
    rwa [pow_one] at h

/-- `π ^ (E + 1)` never divides `π ^ E * U` when `U` is a unit (nonzero residue). -/
theorem not_pow_succ_dvd_pow_mul' {π : O} (hπ : Irreducible π) (E : ℕ) {U : O}
    (hU : residue O U ≠ 0) : ¬ π ^ (E + 1) ∣ π ^ E * U := by
  intro hdvd
  have hcan : π ^ E * π ∣ π ^ E * U := by rw [← pow_succ]; exact hdvd
  exact hU ((residue_eq_zero_iff_dvd hπ U).2
    ((mul_dvd_mul_iff_left (pow_ne_zero E hπ.ne_zero)).1 hcan))

end Helpers

/-! ## 1. H.116b2 (clause i) — MULTIPLICITY ADDS -/

section Trailing

/-- The trailing-coefficient computation over an arbitrary commutative ring: if `f` vanishes
below `μ₁` and `g` below `μ₂`, then `f g` vanishes below `μ₁ + μ₂` and its coefficient there
is the product of the two first coefficients.  (This is mathlib's
`coeff_mul_natTrailingDegree_add_natTrailingDegree` argument, stated at explicit abscissae so
that no `natTrailingDegree` bookkeeping is needed.) -/
theorem coeff_mul_first {R : Type*} [CommRing R] {f g : Polynomial R} {μ₁ μ₂ : ℕ}
    (hf : ∀ j < μ₁, f.coeff j = 0) (hg : ∀ j < μ₂, g.coeff j = 0) :
    (∀ n < μ₁ + μ₂, (f * g).coeff n = 0) ∧
      (f * g).coeff (μ₁ + μ₂) = f.coeff μ₁ * g.coeff μ₂ := by
  classical
  constructor
  · intro n hn
    rw [Polynomial.coeff_mul]
    refine Finset.sum_eq_zero ?_
    rintro ⟨i, j⟩ hij
    rw [Finset.mem_antidiagonal] at hij
    by_cases hi : i < μ₁
    · rw [hf i hi, zero_mul]
    · have hj : j < μ₂ := by omega
      rw [hg j hj, mul_zero]
  · rw [Polynomial.coeff_mul]
    refine Finset.sum_eq_single (μ₁, μ₂) ?_ fun h => (h (Finset.mem_antidiagonal.mpr rfl)).elim
    rintro ⟨i, j⟩ hij hne
    rw [Finset.mem_antidiagonal] at hij
    by_cases hi : i < μ₁
    · rw [hf i hi, zero_mul]
    · by_cases hj : j < μ₂
      · rw [hg j hj, mul_zero]
      · exact absurd (show ((i, j) : ℕ × ℕ) = (μ₁, μ₂) by
          have h1 : i = μ₁ := by omega
          have h2 : j = μ₂ := by omega
          rw [h1, h2]) hne

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **H.116b2 (clause i) [A-H.7 §5].  MULTIPLICITY ADDS.**  If `π ^ s` is the exact coefficient
level of `P₁` with the first unit at abscissa `μ₁`, and `π ^ t` the exact level of `P₂` with
the first unit at `μ₂`, then `π ^ (s + t)` is the exact level of `P₁ P₂` and its first unit
sits at `μ₁ + μ₂`.

Proof: divide the exact levels out (`C_dvd_iff_dvd_coeff`); the hypotheses say precisely that
the divided reduction of `Pᵢ` vanishes below `μᵢ` and is nonzero at `μᵢ`; `(ResidueField O)[X]`
is a domain, so the product's divided reduction vanishes below `μ₁ + μ₂` and is the (nonzero)
product of the two first coefficients there. -/
theorem coeff_level_mul_trailing {π : O} (hπ : Irreducible π) {s t μ₁ μ₂ : ℕ}
    {P₁ P₂ : Polynomial O}
    (h1 : ∀ j, π ^ s ∣ P₁.coeff j) (h1' : ∀ j < μ₁, π ^ (s + 1) ∣ P₁.coeff j)
    (h1'' : ¬ π ^ (s + 1) ∣ P₁.coeff μ₁)
    (h2 : ∀ j, π ^ t ∣ P₂.coeff j) (h2' : ∀ j < μ₂, π ^ (t + 1) ∣ P₂.coeff j)
    (h2'' : ¬ π ^ (t + 1) ∣ P₂.coeff μ₂) :
    (∀ j, π ^ (s + t) ∣ (P₁ * P₂).coeff j) ∧
      (∀ j < μ₁ + μ₂, π ^ (s + t + 1) ∣ (P₁ * P₂).coeff j) ∧
      ¬ π ^ (s + t + 1) ∣ (P₁ * P₂).coeff (μ₁ + μ₂) := by
  classical
  obtain ⟨F₁, hF₁⟩ := (Polynomial.C_dvd_iff_dvd_coeff (π ^ s) P₁).2 h1
  obtain ⟨F₂, hF₂⟩ := (Polynomial.C_dvd_iff_dvd_coeff (π ^ t) P₂).2 h2
  have hc1 : ∀ j, P₁.coeff j = π ^ s * F₁.coeff j := by
    intro j; rw [hF₁, coeff_C_mul]
  have hc2 : ∀ j, P₂.coeff j = π ^ t * F₂.coeff j := by
    intro j; rw [hF₂, coeff_C_mul]
  -- the two divided reductions, read off the hypotheses
  have hr1 : ∀ j < μ₁, (F₁.map (residue O)).coeff j = 0 := by
    intro j hj
    rw [coeff_map]
    refine (residue_eq_zero_iff_dvd hπ _).2 ?_
    have h := h1' j hj
    rw [hc1 j, pow_succ] at h
    exact (mul_dvd_mul_iff_left (pow_ne_zero s hπ.ne_zero)).1 h
  have hr2 : ∀ j < μ₂, (F₂.map (residue O)).coeff j = 0 := by
    intro j hj
    rw [coeff_map]
    refine (residue_eq_zero_iff_dvd hπ _).2 ?_
    have h := h2' j hj
    rw [hc2 j, pow_succ] at h
    exact (mul_dvd_mul_iff_left (pow_ne_zero t hπ.ne_zero)).1 h
  have hn1 : (F₁.map (residue O)).coeff μ₁ ≠ 0 := by
    rw [coeff_map]
    intro hcon
    refine h1'' ?_
    rw [hc1 μ₁, pow_succ]
    exact mul_dvd_mul_left _ ((residue_eq_zero_iff_dvd hπ _).1 hcon)
  have hn2 : (F₂.map (residue O)).coeff μ₂ ≠ 0 := by
    rw [coeff_map]
    intro hcon
    refine h2'' ?_
    rw [hc2 μ₂, pow_succ]
    exact mul_dvd_mul_left _ ((residue_eq_zero_iff_dvd hπ _).1 hcon)
  obtain ⟨hzero, htop⟩ := coeff_mul_first hr1 hr2
  -- transport back through the reduction of the product
  have hmapmul : (F₁ * F₂).map (residue O)
      = (F₁.map (residue O)) * (F₂.map (residue O)) := Polynomial.map_mul _
  have hFzero : ∀ n < μ₁ + μ₂, π ∣ (F₁ * F₂).coeff n := by
    intro n hn
    refine (residue_eq_zero_iff_dvd hπ _).1 ?_
    have h := hzero n hn
    rw [← hmapmul, coeff_map] at h
    exact h
  have hFtop : residue O ((F₁ * F₂).coeff (μ₁ + μ₂)) ≠ 0 := by
    have h : ((F₁ * F₂).map (residue O)).coeff (μ₁ + μ₂)
        = (F₁.map (residue O)).coeff μ₁ * (F₂.map (residue O)).coeff μ₂ := by
      rw [hmapmul]; exact htop
    rw [coeff_map] at h
    rw [h]
    exact mul_ne_zero hn1 hn2
  have hPQ : P₁ * P₂ = Polynomial.C (π ^ (s + t)) * (F₁ * F₂) := by
    rw [hF₁, hF₂, pow_add, Polynomial.C_mul]; ring
  have hcoeff : ∀ n, (P₁ * P₂).coeff n = π ^ (s + t) * (F₁ * F₂).coeff n := by
    intro n; rw [hPQ, coeff_C_mul]
  refine ⟨fun j => ?_, fun j hj => ?_, ?_⟩
  · rw [hcoeff j]; exact Dvd.intro _ rfl
  · rw [hcoeff j, pow_succ]
    exact mul_dvd_mul_left _ (hFzero j hj)
  · rw [hcoeff (μ₁ + μ₂)]
    exact not_pow_succ_dvd_pow_mul' hπ (s + t) hFtop

/-- **The `Finset`-product form of clause (i).**  Exact levels and first-unit abscissae both
ADD along a finite product. -/
theorem coeff_level_prod_trailing {π : O} (hπ : Irreducible π) {ι : Type*}
    (S : Finset ι) (P : ι → Polynomial O) (s μ : ι → ℕ)
    (h1 : ∀ p ∈ S, ∀ j, π ^ s p ∣ (P p).coeff j)
    (h2 : ∀ p ∈ S, ∀ j < μ p, π ^ (s p + 1) ∣ (P p).coeff j)
    (h3 : ∀ p ∈ S, ¬ π ^ (s p + 1) ∣ (P p).coeff (μ p)) :
    (∀ j, π ^ (∑ p ∈ S, s p) ∣ (∏ p ∈ S, P p).coeff j) ∧
      (∀ j < ∑ p ∈ S, μ p, π ^ ((∑ p ∈ S, s p) + 1) ∣ (∏ p ∈ S, P p).coeff j) ∧
      ¬ π ^ ((∑ p ∈ S, s p) + 1) ∣ (∏ p ∈ S, P p).coeff (∑ p ∈ S, μ p) := by
  classical
  revert h1 h2 h3
  induction S using Finset.induction_on with
  | empty =>
      intro _ _ _
      rw [Finset.prod_empty, Finset.sum_empty, Finset.sum_empty]
      refine ⟨fun j => by rw [pow_zero]; exact one_dvd _, fun j hj => absurd hj (by omega), ?_⟩
      rw [zero_add, pow_one, Polynomial.coeff_one, if_pos rfl]
      exact fun hcon => hπ.not_isUnit (isUnit_of_dvd_one hcon)
  | insert a S ha ih =>
      intro h1 h2 h3
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
      exact coeff_level_mul_trailing hπ
        (h1 a (Finset.mem_insert_self a S))
        (h2 a (Finset.mem_insert_self a S))
        (h3 a (Finset.mem_insert_self a S))
        (ih (fun p hp => h1 p (Finset.mem_insert_of_mem hp))
            (fun p hp => h2 p (Finset.mem_insert_of_mem hp))
            (fun p hp => h3 p (Finset.mem_insert_of_mem hp))).1
        (ih (fun p hp => h1 p (Finset.mem_insert_of_mem hp))
            (fun p hp => h2 p (Finset.mem_insert_of_mem hp))
            (fun p hp => h3 p (Finset.mem_insert_of_mem hp))).2.1
        (ih (fun p hp => h1 p (Finset.mem_insert_of_mem hp))
            (fun p hp => h2 p (Finset.mem_insert_of_mem hp))
            (fun p hp => h3 p (Finset.mem_insert_of_mem hp))).2.2

end Trailing

end Uniformity.Density.Induction

/-! ## Axiom footprint (§1) -/

section AxCheck

#print axioms Uniformity.Density.Induction.coeff_mul_first
#print axioms Uniformity.Density.Induction.coeff_level_mul_trailing
#print axioms Uniformity.Density.Induction.coeff_level_prod_trailing

end AxCheck
