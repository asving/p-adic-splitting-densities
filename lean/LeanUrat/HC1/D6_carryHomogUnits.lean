/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsD

/-!
# HC1.D6_carryHomogUnits — nonzero homogeneous elements are units of 𝒟

moves_ref: MOVES 1513–1514 (digits live in homogeneous components; the R-calculus
needs their invertibility). deps: D2. difficulty: easy. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

/-- The `u_ρ · u_σ` law (D2's first clause, reproved inline so D6 stays sorry-free and
axiom-clean): the twisted product of two homogeneous generators is the homogeneous
generator at the sum coset, scaled by the carry factor `z̄^{carryExp ρ σ}`. -/
private lemma D6_dOf_mul_dOf {F : Type*} [Field F] {e : ℕ} [NeZero e] {zbar : Fˣ}
    (P : CarryRingPack F e zbar) (ρ σ : ZMod e) (c c' : F) :
    (letI := P.ring; dOf ρ c * dOf σ c')
      = dOf (ρ + σ) (c * c' * (zbar : F) ^ carryExp ρ σ) := by
  rw [P.mul_def]
  funext τ
  simp only [cmul, dOf]
  rw [Finset.sum_eq_single ρ]
  · rw [Pi.single_eq_same]
    by_cases hτ : τ = ρ + σ
    · subst hτ
      have hsub : ρ + σ - ρ = σ := by ring
      rw [hsub, Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hτ, Pi.single_eq_of_ne, mul_zero, zero_mul]
      intro hcontra
      exact hτ (by rw [← hcontra]; ring)
  · intro α _ hα
    rw [Pi.single_eq_of_ne hα, zero_mul, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ ρ) h

/-- Unit D6: the inverse of `dOf ρ c` is `dOf (−ρ) (c⁻¹·z̄^{−carryExp ρ (−ρ)})`, and
every nonzero homogeneous element is a unit. -/
theorem D6_carryHomogUnits {F : Type*} [Field F] {e : ℕ} [NeZero e] {zbar : Fˣ}
    (P : CarryRingPack F e zbar) :
    (∀ (ρ : ZMod e) (c : F), c ≠ 0 →
      (letI := P.ring;
        dOf ρ c * dOf (-ρ) (c⁻¹ * ((zbar : F) ^ carryExp ρ (-ρ))⁻¹) = 1)) ∧
    (∀ (x : CarryAlg F e) (ρ : ZMod e), IsHomog x ρ → x ≠ 0 →
      (letI := P.ring; IsUnit x)) := by
  letI := P.ring
  have h1 : ∀ (ρ : ZMod e) (c : F), c ≠ 0 →
      dOf ρ c * dOf (-ρ) (c⁻¹ * ((zbar : F) ^ carryExp ρ (-ρ))⁻¹) = 1 := by
    intro ρ c hc
    rw [D6_dOf_mul_dOf P, add_neg_cancel]
    have hz : (zbar : F) ^ carryExp ρ (-ρ) ≠ 0 := pow_ne_zero _ zbar.ne_zero
    rw [show c * (c⁻¹ * ((zbar : F) ^ carryExp ρ (-ρ))⁻¹) * (zbar : F) ^ carryExp ρ (-ρ)
          = (c * c⁻¹) * (((zbar : F) ^ carryExp ρ (-ρ))⁻¹ * (zbar : F) ^ carryExp ρ (-ρ))
        by ring,
      mul_inv_cancel₀ hc, inv_mul_cancel₀ hz, one_mul, ← P.one_def]
  refine ⟨h1, ?_⟩
  intro x ρ hhom hne
  have hxρ : x ρ ≠ 0 := by
    intro h0
    apply hne
    funext σ
    by_cases hσ : σ = ρ
    · rw [hσ]; exact h0
    · exact hhom σ hσ
  have hx : x = dOf ρ (x ρ) := by
    funext σ
    by_cases hσ : σ = ρ
    · rw [hσ, dOf, Pi.single_eq_same]
    · rw [hhom σ hσ, dOf, Pi.single_eq_of_ne hσ]
  rw [hx]
  exact IsUnit.of_mul_eq_one _ (h1 ρ (x ρ) hxρ)

end LeanUrat.HC1

#print axioms LeanUrat.HC1.D6_carryHomogUnits
