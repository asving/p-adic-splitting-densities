/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity
import UniformityCheck.N3Base

/-!
# UniformityCheck.N3Certs — the three COMPOSITE cubic certificates

The three cubic types that have a linear factor are certified here by *peeling*: Hensel produces
a root `r` of the cubic at a simple residue root, `cubic_peel` divides it out with no division,
and the quadratic cofactor `peel a r` is handed to one of `leanfinal`'s own degree-2 certificates.
`typeOf_mul` (N3Base) then assembles the type.

| theorem | certificate | type |
|---|---|---|
| `typeOf_linInert_of_residue` | `f̄ = (X − ρ̄)(X² + β̄₁X + β̄₀)`, the quadratic residually rootless | `{(1,1),(1,2)}` |
| `typeOf_linRam_of_residue` | `a₂` a unit, `a₁ ∈ 𝔪`, `a₀ ∈ 𝔪 \ 𝔪²` | `{(1,1),(2,1)}` |
| `typeOf_split3_of_deep` | `a ≡ (0, π, −(1+π))` mod `𝔪³` (the class of `X(X−1)(X−π)`) | `{(1,1)}³` |

The first two are level-1 / level-2 conditions. The third is genuinely DEEP: at `q = 2` there is
no monic cubic with three distinct residue roots at all, so the split type has no level-1
certificate over a general base and the window-3 class of `X(X−1)(X−π)` is used instead. Its
proof bootstraps the Hensel root from `r ≡ 1 (mod 𝔪)` up to `r ≡ 1 (mod 𝔪³)` — the two other
roots being `≡ 0` keeps `r` a unit and `r − π` a unit, so the exact odd factor of
`r(r−1)(r−π) = −π³w` is forced onto `r − 1`.

No residue-characteristic hypothesis appears anywhere: the simple-root derivative values used are
`ρ² + β₁ρ + β₀` and `a₂²`, which are units in every characteristic.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace UniformityCheck

open Uniformity Uniformity.Density IsLocalRing Polynomial

section Certs

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]

/-- Cancel a unit factor out of a divisibility. -/
theorem dvd_of_isUnit_mul {c d e : O} (hu : IsUnit c) (h : d ∣ c * e) : d ∣ e := by
  obtain ⟨u, rfl⟩ := hu
  have he : e = ((↑u⁻¹ : O)) * ((u : O) * e) := by
    rw [← mul_assoc]
    simp
  rw [he]
  exact h.mul_left _

/-! ## 1. Linear × inert quadratic -/

/-- **`{(1,1),(1,2)}`.** If the reduction of the monic cubic is `(X − ρ̄)(X² + β̄₁X + β̄₀)` with the
quadratic part residually rootless (`Anisotropic ![β₀, β₁]`), the cubic is a linear factor times
an inert quadratic. -/
theorem typeOf_linInert_of_residue {a : Fin 3 → O} (ρ β₀ β₁ : O)
    (hani : Anisotropic ![β₀, β₁])
    (h2 : a 2 - (β₁ - ρ) ∈ maximalIdeal O)
    (h1 : a 1 - (β₀ - ρ * β₁) ∈ maximalIdeal O)
    (h0 : a 0 + ρ * β₀ ∈ maximalIdeal O) :
    typeOf (monicPoly a) = c3linInert := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  -- the reduced cubic vanishes at ρ
  have hvalρ : ρ ^ 3 + a 2 * ρ ^ 2 + a 1 * ρ + a 0 ∈ maximalIdeal O := by
    have hid : ρ ^ 3 + a 2 * ρ ^ 2 + a 1 * ρ + a 0
        = (a 2 - (β₁ - ρ)) * ρ ^ 2 + (a 1 - (β₀ - ρ * β₁)) * ρ + (a 0 + ρ * β₀) := by ring
    rw [hid]
    exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _ h2)
      (Ideal.mul_mem_right _ _ h1)) h0
  -- ... simply, because the quadratic factor does not
  have hderρ : IsUnit (3 * ρ ^ 2 + 2 * a 2 * ρ + a 1) := by
    refine notMem_maximalIdeal.1 (fun hmem => ?_)
    have hid : quadForm ![β₀, β₁] (-ρ) 1
        = (3 * ρ ^ 2 + 2 * a 2 * ρ + a 1) - 2 * (a 2 - (β₁ - ρ)) * ρ
            - (a 1 - (β₀ - ρ * β₁)) := by
      simp only [quadForm, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    have hq : quadForm ![β₀, β₁] (-ρ) 1 ∈ maximalIdeal O := by
      rw [hid]
      exact Ideal.sub_mem _ (Ideal.sub_mem _ hmem (Ideal.mul_mem_right _ _
        (Ideal.mul_mem_left _ _ h2))) h1
    exact absurd (hani (-ρ) 1 hq).2 ((notMem_maximalIdeal (R := O)).2 isUnit_one)
  obtain ⟨r, hr, hrρ⟩ := exists_cubic_root a ρ hvalρ hderρ
  -- the cofactor is residually `X² + β₁X + β₀`
  have hg1 : peel a r 1 - β₁ ∈ maximalIdeal O := by
    have hid : peel a r 1 - β₁ = (a 2 - (β₁ - ρ)) + (r - ρ) := by
      simp only [peel_one]; ring
    rw [hid]; exact Ideal.add_mem _ h2 hrρ
  have hg0 : peel a r 0 - β₀ ∈ maximalIdeal O := by
    have hid : peel a r 0 - β₀ = (a 1 - (β₀ - ρ * β₁)) + (a 2 - (β₁ - ρ)) * ρ
        + (r - ρ) * (β₁ + ρ + (a 2 - (β₁ - ρ)) + (r - ρ)) := by
      simp only [peel_zero]; ring
    rw [hid]
    exact Ideal.add_mem _ (Ideal.add_mem _ h1 (Ideal.mul_mem_right _ _ h2))
      (Ideal.mul_mem_right _ _ hrρ)
  have hani' : Anisotropic (peel a r) := by
    refine Anisotropic_congr hπ hani ?_ ?_
    · simpa using (mem_maximalIdeal_iff_dvd hπ _).1 hg0
    · simpa using (mem_maximalIdeal_iff_dvd hπ _).1 hg1
  apply FactorizationType.ext
  rw [cubic_peel a r hr, typeOf_linear_mul (monicPoly_monic (peel a r)) r,
    typeOf_inert_of_anisotropic hani']
  rfl

/-! ## 2. Linear × ramified quadratic -/

/-- **`{(1,1),(2,1)}`.** If `a₂` is a unit, `a₁ ∈ 𝔪` and `a₀` has valuation exactly `1`, the cubic
is a linear factor times an Eisenstein quadratic. (Residually `f̄ = X²(X + ā₂)`, so `−a₂` is a
simple residue root with derivative `a₂²`.) -/
theorem typeOf_linRam_of_residue {a : Fin 3 → O}
    (h2 : IsUnit (a 2))
    (h1 : a 1 ∈ maximalIdeal O)
    (h0 : a 0 ∈ maximalIdeal O) (h0' : a 0 ∉ (maximalIdeal O) ^ 2) :
    typeOf (monicPoly a) = c3linRam := by
  have hvalρ : (-a 2) ^ 3 + a 2 * (-a 2) ^ 2 + a 1 * (-a 2) + a 0 ∈ maximalIdeal O := by
    have hid : (-a 2) ^ 3 + a 2 * (-a 2) ^ 2 + a 1 * (-a 2) + a 0 = a 1 * (-a 2) + a 0 := by ring
    rw [hid]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ h1) h0
  have hderρ : IsUnit (3 * (-a 2) ^ 2 + 2 * a 2 * (-a 2) + a 1) := by
    refine notMem_maximalIdeal.1 (fun hmem => ?_)
    have hsq : a 2 * a 2 ∈ maximalIdeal O := by
      have hid : a 2 * a 2 = (3 * (-a 2) ^ 2 + 2 * a 2 * (-a 2) + a 1) - a 1 := by ring
      rw [hid]; exact Ideal.sub_mem _ hmem h1
    exact absurd hsq (notMem_maximalIdeal.2 (h2.mul h2))
  obtain ⟨r, hr, hrρ⟩ := exists_cubic_root a (-a 2) hvalρ hderρ
  have hru : IsUnit r := by
    refine notMem_maximalIdeal.1 (fun hmem => ?_)
    have hmem2 : a 2 ∈ maximalIdeal O := by
      have hid : a 2 = (r - -a 2) - r := by ring
      rw [hid]
      exact Ideal.sub_mem _ hrρ hmem
    exact absurd hmem2 (notMem_maximalIdeal.2 h2)
  -- the cofactor is Eisenstein
  have hg1 : peel a r 1 ∈ maximalIdeal O := by
    have hid : peel a r 1 = r - -a 2 := by simp only [peel_one]; ring
    rw [hid]; exact hrρ
  have hg0 : peel a r 0 ∈ maximalIdeal O := by
    have hid : peel a r 0 = a 1 + r * (r - -a 2) := by simp only [peel_zero]; ring
    rw [hid]
    exact Ideal.add_mem _ h1 (Ideal.mul_mem_left _ _ hrρ)
  have hg0' : peel a r 0 ∉ (maximalIdeal O) ^ 2 := by
    intro hmem
    refine h0' ?_
    rw [peel_const a r hr]
    exact neg_mem (Ideal.mul_mem_left _ _ hmem)
  apply FactorizationType.ext
  rw [cubic_peel a r hr, typeOf_linear_mul (monicPoly_monic (peel a r)) r,
    typeOf_ram_of_eisenstein hg0 hg0' hg1]
  rfl

/-! ## 3. Three linear factors — the deep certificate -/

/-- **`{(1,1)}³`.** Every monic cubic congruent to `X(X − 1)(X − π)` modulo `𝔪³` splits into three
linear factors.

This is the split type's general-`O` certificate: it must be deep, because at `q = 2` no residue
cubic has three distinct roots. -/
theorem typeOf_split3_of_deep {π : O} (hπ : Irreducible π) {a : Fin 3 → O}
    (h0 : π ^ 3 ∣ a 0) (h1 : π ^ 3 ∣ (a 1 - π)) (h2 : π ^ 3 ∣ (a 2 + (1 + π))) :
    typeOf (monicPoly a) = c3split := by
  have hπm : π ∈ maximalIdeal O := (mem_maximalIdeal_iff_dvd hπ π).2 dvd_rfl
  have hcube : ∀ x : O, π ^ 3 ∣ x → x ∈ maximalIdeal O := fun x hx =>
    (mem_maximalIdeal_iff_dvd hπ x).2 (dvd_trans (dvd_pow_self π (by norm_num)) hx)
  -- Hensel at the simple residue root `1`
  have hval1 : (1 : O) ^ 3 + a 2 * 1 ^ 2 + a 1 * 1 + a 0 ∈ maximalIdeal O := by
    have hid2 : (1 : O) ^ 3 + a 2 * 1 ^ 2 + a 1 * 1 + a 0
        = (a 2 + (1 + π)) + (a 1 - π) + a 0 := by ring
    rw [hid2]
    exact Ideal.add_mem _ (Ideal.add_mem _ (hcube _ h2) (hcube _ h1)) (hcube _ h0)
  have hder1 : IsUnit (3 * (1 : O) ^ 2 + 2 * a 2 * 1 + a 1) := by
    refine notMem_maximalIdeal.1 (fun hmem => ?_)
    have hid : (1 : O) = (3 * (1 : O) ^ 2 + 2 * a 2 * 1 + a 1)
        - 2 * (a 2 + (1 + π)) - (a 1 - π) + π := by ring
    have : (1 : O) ∈ maximalIdeal O := by
      rw [hid]
      exact Ideal.add_mem _ (Ideal.sub_mem _ (Ideal.sub_mem _ hmem
        (Ideal.mul_mem_left _ _ (hcube _ h2))) (hcube _ h1)) hπm
    exact absurd this (notMem_maximalIdeal.2 isUnit_one)
  obtain ⟨r, hr, hr1⟩ := exists_cubic_root a 1 hval1 hder1
  -- bootstrap: `r ≡ 1` improves from `mod 𝔪` to `mod 𝔪³`
  obtain ⟨u0, hu0⟩ := h0
  obtain ⟨u1, hu1⟩ := h1
  obtain ⟨u2, hu2⟩ := h2
  have hru : IsUnit r := by
    refine notMem_maximalIdeal.1 (fun hmem => ?_)
    have : (1 : O) ∈ maximalIdeal O := by
      have hid : (1 : O) = r - (r - 1) := by ring
      rw [hid]; exact Ideal.sub_mem _ hmem hr1
    exact absurd this (notMem_maximalIdeal.2 isUnit_one)
  have hrπu : IsUnit (r - π) := by
    refine notMem_maximalIdeal.1 (fun hmem => ?_)
    have : (1 : O) ∈ maximalIdeal O := by
      have hid : (1 : O) = (r - π) - (r - 1) + π := by ring
      rw [hid]
      exact Ideal.add_mem _ (Ideal.sub_mem _ hmem hr1) hπm
    exact absurd this (notMem_maximalIdeal.2 isUnit_one)
  have hfactor : r * (r - π) * (r - 1) = π ^ 3 * (-(u2 * r ^ 2 + u1 * r + u0)) := by
    have hre : (monicPoly a).eval r = 0 := hr
    rw [cubic_eval] at hre
    have ha0 : a 0 = π ^ 3 * u0 := hu0
    have ha1 : a 1 = π + π ^ 3 * u1 := by linear_combination hu1
    have ha2 : a 2 = -(1 + π) + π ^ 3 * u2 := by linear_combination hu2
    rw [ha0, ha1, ha2] at hre
    linear_combination hre
  have hr1cube : π ^ 3 ∣ (r - 1) :=
    dvd_of_isUnit_mul (hru.mul hrπu) ⟨-(u2 * r ^ 2 + u1 * r + u0), by
      rw [← hfactor]⟩
  -- the cofactor carries a SPLIT certificate at the centre `0`, with `w = 1`
  have hqder : qder (peel a r) 0 = a 2 + r := by simp only [qder, peel_one]; ring
  have hqval : qval (peel a r) 0 = a 1 + a 2 * r + r ^ 2 := by simp only [qval, peel_zero]; ring
  have hd1 : π ∣ qder (peel a r) 0 := by
    rw [hqder]
    obtain ⟨v, hv⟩ := hr1cube
    refine ⟨π ^ 2 * u2 + π ^ 2 * v - 1, ?_⟩
    have ha2 : a 2 = -(1 + π) + π ^ 3 * u2 := by linear_combination hu2
    have hrv : r = 1 + π ^ 3 * v := by linear_combination hv
    rw [ha2, hrv]; ring
  have hd2 : ¬ π ^ 2 ∣ qder (peel a r) 0 := by
    rw [hqder]
    intro ⟨v', hv'⟩
    obtain ⟨v, hv⟩ := hr1cube
    have ha2 : a 2 = -(1 + π) + π ^ 3 * u2 := by linear_combination hu2
    have hrv : r = 1 + π ^ 3 * v := by linear_combination hv
    rw [ha2, hrv] at hv'
    have hcancel : π * (-1 + π ^ 2 * u2 + π ^ 2 * v - π * v') = 0 := by linear_combination hv'
    have hz := (mul_eq_zero.1 hcancel).resolve_left hπ.ne_zero
    have hdvd : π ∣ (1 : O) := ⟨π * u2 + π * v - v', by linear_combination -hz⟩
    exact hπ.not_isUnit (isUnit_of_dvd_one hdvd)
  have hv3 : π ^ 3 ∣ qval (peel a r) 0 := by
    rw [hqval]
    have hpc : peel a r 0 = a 1 + a 2 * r + r ^ 2 := rfl
    refine dvd_of_isUnit_mul hru ?_
    have hid : r * (a 1 + a 2 * r + r ^ 2) = -a 0 := by
      have hpk := peel_const a r hr
      rw [hpc] at hpk
      linear_combination hpk
    rw [hid]
    exact dvd_neg.2 ⟨u0, hu0⟩
  have hsplit : typeOf (monicPoly (peel a r)) = splitType :=
    typeOf_of_certSplit hπ (N := 3) ⟨0, 1, by omega, by simpa using hd1, by simpa using hd2, by
      simpa using hv3⟩
  apply FactorizationType.ext
  rw [cubic_peel a r hr, typeOf_linear_mul (monicPoly_monic (peel a r)) r, hsplit]
  rfl

end Certs

end UniformityCheck
