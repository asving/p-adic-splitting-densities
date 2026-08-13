/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import UniformityCheck.RamCensus

/-!
# UniformityCheck.InertShift — the centre of an INERT certificate

The INERT certificate of `Drainage.lean` says: at some centre `γ` the value is
`F(γ) = π^(2k) b₀`, the derivative is `F'(γ) = π^k b₁`, and the residual binary form
`![b₀, b₁]` is anisotropic. This file pins the centre:

* `InertAt_exact` — anisotropy makes `b₀` a unit, so `v(F(γ)) = 2k` exactly;
* **`InertAt_shift`** — the certificate survives every move of the centre inside `γ + 𝔪 ^ k`.
  The recentring `γ ↦ γ + π^k z` sends the residual form to
  `quadForm ![b₀', b₁'] u v = quadForm ![b₀, b₁] (u - z v) v`, a unimodular substitution, so
  anisotropy is preserved. (Note `k`, not `k+1`: unlike the ramified case, the inert certificate
  is stable already at the scale of its own residual reading.)
* **`InertAt_uniq`** — and nothing else: moving the centre by `δ` of valuation `m < k` makes the
  value have exact valuation `2m` with residual form `u² - 2(δ/π^m)uv + (δ/π^m)²v²`, which has
  the zero `(δ/π^m, 1)` — isotropic. So `k` and the centre mod `𝔪 ^ k` are determined by the
  class.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace UniformityCheck

open Uniformity Uniformity.Density IsLocalRing

section InertAt

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **The INERT certificate at the centre `γ` with parameter `k`** (upstairs). -/
def InertAt (π : O) (k : ℕ) (a : Fin 2 → O) (γ : O) : Prop :=
  ∃ b₀ b₁ : O, qval a γ = π ^ (2 * k) * b₀ ∧ qder a γ = π ^ k * b₁ ∧ Anisotropic ![b₀, b₁]

/-- Anisotropy forces the value to have EXACT valuation `2k`. -/
theorem InertAt_exact (hπ : Irreducible π) {k : ℕ} {a : Fin 2 → O} {γ : O}
    (h : InertAt π k a γ) :
    π ^ (2 * k) ∣ qval a γ ∧ ¬ π ^ (2 * k + 1) ∣ qval a γ := by
  obtain ⟨b₀, b₁, hv, -, han⟩ := h
  refine ⟨⟨b₀, hv⟩, ?_⟩
  rintro ⟨w, hw⟩
  refine not_dvd_of_anisotropic hπ han ⟨w, ?_⟩
  refine mul_left_cancel₀ (pow_ne_zero (2 * k) hπ.ne_zero) ?_
  rw [← hv, hw]
  ring

/-- **Shift.** The certificate survives any move of the centre inside `γ + 𝔪 ^ k`. -/
theorem InertAt_shift {k : ℕ} {a : Fin 2 → O} {γ γ' : O} (h : InertAt π k a γ)
    (hδ : π ^ k ∣ (γ' - γ)) : InertAt π k a γ' := by
  obtain ⟨b₀, b₁, hv, hd, han⟩ := h
  obtain ⟨z, hz⟩ := hδ
  have hγ' : γ' = γ + π ^ k * z := by linear_combination hz
  refine ⟨b₀ + b₁ * z + z ^ 2, b₁ + 2 * z, ?_, ?_, ?_⟩
  · rw [hγ', qval_shift a γ _, hv, hd]; ring
  · rw [hγ', qder_shift a γ _, hd]; ring
  · intro u v huv
    have hid : quadForm ![b₀ + b₁ * z + z ^ 2, b₁ + 2 * z] u v
        = quadForm ![b₀, b₁] (u - z * v) v := by
      simp only [quadForm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      ring
    rw [hid] at huv
    obtain ⟨h1, h2⟩ := han _ _ huv
    refine ⟨?_, h2⟩
    have hu : u = (u - z * v) + z * v := by ring
    rw [hu]
    exact Ideal.add_mem _ h1 (Ideal.mul_mem_left _ _ h2)

/-- **Uniqueness.** Two INERT certificates on the same coefficient vector have the same parameter
and centres in the same coset of `𝔪 ^ k`. -/
theorem InertAt_uniq (hπ : Irreducible π) {k k' : ℕ} {a : Fin 2 → O} {γ γ' : O}
    (h : InertAt π k a γ) (h' : InertAt π k' a γ') : k = k' ∧ π ^ k ∣ (γ' - γ) := by
  have hclose : π ^ k ∣ (γ' - γ) := by
    by_contra hcon
    obtain ⟨m, hmlt, hm1, hm2⟩ := exists_exact_val hπ hcon
    obtain ⟨d, rfl⟩ : ∃ d, k = m + d + 1 := ⟨k - m - 1, by omega⟩
    obtain ⟨b₀, b₁, hv, hd, han⟩ := h
    obtain ⟨ε, hε⟩ := hm1
    have hεu : ¬ π ∣ ε := by
      rintro ⟨w, hw⟩
      exact hm2 ⟨w, by rw [hε, hw]; ring⟩
    have hγ' : γ' = γ + π ^ m * ε := by linear_combination hε
    -- the value and derivative at the new centre
    set B : O := π ^ (2 * d + 2) * b₀ + π ^ (d + 1) * b₁ * ε + ε ^ 2 with hB
    have hv' : qval a γ' = π ^ (2 * m) * B := by
      rw [hγ', qval_shift a γ _, hv, hd, hB]
      ring
    have hd' : qder a γ' = π ^ m * (π ^ (d + 1) * b₁ + 2 * ε) := by
      rw [hγ', qder_shift a γ _, hd]
      ring
    have hBu : ¬ π ∣ B := by
      intro hdvd
      refine hεu (hπ.prime.dvd_of_dvd_pow (n := 2) ?_)
      have hsq : ε ^ 2 = B - (π ^ (2 * d + 2) * b₀ + π ^ (d + 1) * b₁ * ε) := by rw [hB]; ring
      rw [hsq]
      exact dvd_sub hdvd (dvd_add ⟨π ^ (2 * d + 1) * b₀, by ring⟩ ⟨π ^ d * b₁ * ε, by ring⟩)
    -- the exact valuation at the new centre is `2m`, so the second certificate has `k' = m`
    have hex' := InertAt_exact hπ h'
    have hexm : π ^ (2 * m) ∣ qval a γ' ∧ ¬ π ^ (2 * m + 1) ∣ qval a γ' := by
      refine ⟨⟨B, hv'⟩, ?_⟩
      rintro ⟨w, hw⟩
      refine hBu ⟨w, ?_⟩
      refine mul_left_cancel₀ (pow_ne_zero (2 * m) hπ.ne_zero) ?_
      rw [← hv', hw]
      ring
    have hkm : k' = m := by
      have := exact_val_unique hπ hex'.1 hex'.2 hexm.1 hexm.2
      omega
    subst hkm
    -- read off the residual data of the second certificate and find a zero of its form
    obtain ⟨b₀', b₁', hv2, hd2, han2⟩ := h'
    have hb₀' : b₀' = B := by
      refine mul_left_cancel₀ (pow_ne_zero (2 * k') hπ.ne_zero) ?_
      rw [← hv2, hv']
    have hb₁' : b₁' = π ^ (d + 1) * b₁ + 2 * ε := by
      refine mul_left_cancel₀ (pow_ne_zero k' hπ.ne_zero) ?_
      rw [← hd2, hd']
    have hzero : quadForm ![b₀', b₁'] ε 1 = π ^ (2 * d + 2) * b₀ := by
      simp only [quadForm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        hb₀', hb₁', hB]
      ring
    have hmem : quadForm ![b₀', b₁'] ε 1 ∈ maximalIdeal O := by
      rw [hzero]
      exact (mem_maximalIdeal_iff_dvd hπ _).2 ⟨π ^ (2 * d + 1) * b₀, by ring⟩
    exact (maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 (han2 ε 1 hmem).2)
  refine ⟨?_, hclose⟩
  have hshift := InertAt_shift h hclose
  have e1 := InertAt_exact hπ hshift
  have e2 := InertAt_exact hπ h'
  have := exact_val_unique hπ e1.1 e1.2 e2.1 e2.2
  omega

end InertAt

end UniformityCheck
