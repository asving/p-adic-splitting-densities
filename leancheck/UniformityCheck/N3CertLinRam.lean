/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import UniformityCheck.N3Shift

/-!
# UniformityCheck.N3CertLinRam — CASE L: `v(B₁) = 1` with `v(B₀) ≥ 2` is linear × ramified

Unit `UNIFORMITY-CHECK-N3C`, layer 2 (`notes/N3_CHECK_2026-08-13.md` §13.2, CERT L). THE strong
Hensel consumer: a cubic with

    π ∣ B₂ ,  π ∣ B₁ ,  π² ∤ B₁ ,  π² ∣ B₀

has `typeOf = c3linRam = {(1,1),(2,1)}`. This is `N3_CHECK` §9.4's "two or three sides" row, and
it is the row the coprime-factorization Hensel cannot reach.

**Strong Hensel does NOT fire at `x₀ = 0`**: there `v(F(0)) = v(B₀)` can be exactly `2 = 2·v(F′(0))`,
failing `k > 2w` by one. It fires at the SHIFTED centre `x₀ = π t` with `t := −C·u⁻¹`, where
`B₁ = π u` (`u` a unit, from `π ∣ B₁ ∧ π² ∤ B₁`) and `B₀ = π² C`:

* `F(x₀) = π²(u t + C) + π³(t³ + B₂′t²) = π³(t³ + B₂′t²)` since `u t + C = 0` exactly — so `k = 3`;
* `F′(x₀) = π·(u + π(3t² + 2B₂′t))`, a unit times `π` — so `w = 1` EXACTLY, and `2w = 2 < 3 = k`;
* strong Hensel returns a root `r` with `π² ∣ r − x₀`, hence `π ∣ r`;
* the cofactor `peel B r = ![B₁ + B₂r + r², B₂ + r]` is an EISENSTEIN quadratic: `π ∣ g₀` and
  `π² ∤ g₀` because `π² ∣ B₂r`, `π² ∣ r²` and `π² ∤ π u`;
* so `typeOf (monicPoly g) = ramType` (`typeOf_ram_of_eisenstein`) and, by `cubic_peel` and the
  additivity of `typeOf` on monic products (`typeOf_linear_mul`),
  `typeOf (monicPoly B) = (1,1) ::ₘ {(2,1)} = c3linRam`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace UniformityCheck

open Uniformity Uniformity.Density IsLocalRing Polynomial

section CertLinRam

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]

/-- **The shifted strong-Hensel centre fires.** With `B₁ = π u` (`u` a unit), `B₀ = π² C`,
`B₂ = π B₂′`, the point `x₀ = π·(−C·u⁻¹)` has `π³ ∣ F(x₀)` and `F′(x₀) = π · unit`; strong Hensel
therefore returns a root `r` of `F` with `π² ∣ r − x₀`, in particular `π ∣ r`. -/
theorem exists_root_of_val_one {π : O} (hπ : Irreducible π) {b : Fin 3 → O}
    (h2 : π ∣ b 2) (h1 : π ∣ b 1) (h1' : ¬ π ^ 2 ∣ b 1) (h0 : π ^ 2 ∣ b 0) :
    ∃ r : O, (monicPoly b).eval r = 0 ∧ π ∣ r ∧ π ^ 2 ∣ (b 1 + b 2 * r + r ^ 2) - b 1 := by
  have hm : maximalIdeal O = Ideal.span {π} := hπ.maximalIdeal_eq
  obtain ⟨u, hu_eq⟩ := h1
  obtain ⟨c, hc⟩ := h0
  obtain ⟨B2, hB2⟩ := h2
  -- `u` is a unit: otherwise `π ∣ u`, hence `π² ∣ b 1`, contradicting `h1'`
  have hu : IsUnit u := by
    by_contra hun
    refine h1' ?_
    have hπu : π ∣ u := by
      rw [← Ideal.mem_span_singleton, ← hm]
      exact (mem_maximalIdeal _).2 (mem_nonunits_iff.2 hun)
    obtain ⟨d, rfl⟩ := hπu
    exact ⟨d, by rw [hu_eq]; ring⟩
  -- the shifted centre `x₀ = π t`, where `t = -c·u⁻¹` solves `u t + c = 0` exactly
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  obtain ⟨t, hut⟩ : ∃ t : O, u * t + c = 0 := ⟨-(c * w), by linear_combination (-c) * hw⟩
  -- `F(x₀) = π³(t³ + B₂′t²)`, so `k = 3`
  have hval : π ^ 3 ∣ (monicPoly b).eval (π * t) := by
    refine ⟨t ^ 3 + B2 * t ^ 2, ?_⟩
    rw [cubic_eval, hB2, hu_eq, hc]
    linear_combination (π ^ 2) * hut
  -- `F′(x₀) = π·(u + π(3t² + 2B₂′t))`, a unit times `π`, so `w = 1` exactly
  have hmem : π * (3 * t ^ 2 + 2 * B2 * t) ∈ maximalIdeal O :=
    (mem_maximalIdeal_iff_dvd hπ _).2 ⟨_, rfl⟩
  have hbu : IsUnit (u + π * (3 * t ^ 2 + 2 * B2 * t)) :=
    Hensel.isUnit_add_of_mem_maximalIdeal hu hmem
  have hd : ∃ v : Oˣ, (monicPoly b).derivative.eval (π * t) = π ^ 1 * v := by
    refine ⟨hbu.unit, ?_⟩
    rw [hbu.unit_spec, cubic_deriv_eval, hB2, hu_eq]
    ring
  obtain ⟨r, hr0, hrd, -⟩ := exists_cubic_root_strong hπ hd hval (by norm_num)
  have hrd2 : π ^ 2 ∣ r - π * t := by simpa using hrd
  have hπr : π ∣ r := by
    have hsum := dvd_add ((dvd_pow_self π (by norm_num : (2 : ℕ) ≠ 0)).trans hrd2)
      (dvd_mul_right π t)
    simpa using hsum
  refine ⟨r, hr0, hπr, ?_⟩
  obtain ⟨s, hs⟩ := hπr
  refine ⟨B2 * s + s ^ 2, ?_⟩
  rw [hB2, hs]
  ring

/-- **CERT L (CASE L of §13.1).** `v(B₁) = 1` with `v(B₀) ≥ 2`, `v(B₂) ≥ 1` forces the type
`{(1,1),(2,1)}`: a root of positive valuation, peeled off, leaves an Eisenstein quadratic. -/
theorem typeOf_linRam_of_val_one {π : O} (hπ : Irreducible π) {b : Fin 3 → O}
    (h2 : π ∣ b 2) (h1 : π ∣ b 1) (h1' : ¬ π ^ 2 ∣ b 1) (h0 : π ^ 2 ∣ b 0) :
    typeOf (monicPoly b) = c3linRam := by
  obtain ⟨r, hr, hπr, hsq⟩ := exists_root_of_val_one hπ h2 h1 h1' h0
  have hsq' : π ^ 2 ∣ b 2 * r + r ^ 2 := by
    have hid : (b 1 + b 2 * r + r ^ 2) - b 1 = b 2 * r + r ^ 2 := by ring
    rwa [hid] at hsq
  -- the cofactor `peel b r = ![b 1 + b 2 r + r², b 2 + r]` is Eisenstein
  have hg0 : peel b r 0 ∈ maximalIdeal O := by
    rw [peel_zero]
    refine (mem_maximalIdeal_iff_dvd hπ _).2 ?_
    have hid : b 1 + b 2 * r + r ^ 2 = b 1 + (b 2 * r + r ^ 2) := by ring
    rw [hid]
    exact dvd_add h1 ((dvd_pow_self π (by norm_num : (2 : ℕ) ≠ 0)).trans hsq')
  have hg0' : peel b r 0 ∉ (maximalIdeal O) ^ 2 := by
    intro hmem
    rw [peel_zero] at hmem
    refine h1' ?_
    have hdvd : π ^ 2 ∣ b 1 + b 2 * r + r ^ 2 := by
      rwa [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
    have hid : b 1 = (b 1 + b 2 * r + r ^ 2) - (b 2 * r + r ^ 2) := by ring
    rw [hid]
    exact dvd_sub hdvd hsq'
  have hg1 : peel b r 1 ∈ maximalIdeal O := by
    rw [peel_one]
    exact (mem_maximalIdeal_iff_dvd hπ _).2 (dvd_add h2 hπr)
  apply FactorizationType.ext
  rw [cubic_peel b r hr, typeOf_linear_mul (monicPoly_monic (peel b r)) r,
    typeOf_ram_of_eisenstein hg0 hg0' hg1]
  rfl

end CertLinRam

/-! ## Axiom census -/

section AxCheck

#print axioms UniformityCheck.exists_root_of_val_one
#print axioms UniformityCheck.typeOf_linRam_of_val_one

end AxCheck

end UniformityCheck
