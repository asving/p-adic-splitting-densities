/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsD

/-!
# HC1.D2_carryGrading — the u_ρ·u_σ law and homogeneity of products

moves_ref: MOVES 1508–1509 (the u_ρ·u_σ law). deps: D1 (via `CarryRingPack`).
difficulty: easy. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

/-- Unit D2: `dOf ρ c * dOf σ c' = dOf (ρ+σ) (c·c'·z̄^{carryExp ρ σ})`, and products
of homogeneous elements are homogeneous at the sum coset. -/
theorem D2_carryGrading {F : Type*} [Field F] {e : ℕ} [NeZero e] {zbar : Fˣ}
    (P : CarryRingPack F e zbar) :
    (∀ (ρ σ : ZMod e) (c c' : F),
      (letI := P.ring; dOf ρ c * dOf σ c')
        = dOf (ρ + σ) (c * c' * (zbar : F) ^ carryExp ρ σ)) ∧
    (∀ (x y : CarryAlg F e) (ρ σ : ZMod e), IsHomog x ρ → IsHomog y σ →
      IsHomog (letI := P.ring; x * y) (ρ + σ)) := by
  refine ⟨?_, ?_⟩
  · -- the u_ρ·u_σ law: a single surviving summand
    intro ρ σ c c'
    rw [P.mul_def]
    funext τ
    simp only [cmul, dOf]
    rw [Finset.sum_eq_single ρ]
    · rw [Pi.single_eq_same]
      by_cases hτ : τ = ρ + σ
      · subst hτ
        rw [add_sub_cancel_left, Pi.single_eq_same, Pi.single_eq_same]
      · have hne : τ - ρ ≠ σ := by
          intro h
          rw [sub_eq_iff_eq_add] at h
          exact hτ (by rw [h]; exact add_comm σ ρ)
        rw [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hτ, mul_zero, zero_mul]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, zero_mul, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ ρ) h
  · -- homogeneity of products: every summand vanishes off the (ρ+σ) coset
    intro x y ρ σ hx hy τ hτ
    rw [P.mul_def]
    simp only [cmul]
    apply Finset.sum_eq_zero
    intro ρ' _
    by_cases hρ' : ρ' = ρ
    · have hne : τ - ρ' ≠ σ := by
        intro h
        rw [sub_eq_iff_eq_add] at h
        apply hτ
        rw [h, hρ']
        exact add_comm σ ρ
      rw [hy _ hne, mul_zero, zero_mul]
    · rw [hx _ hρ', zero_mul, zero_mul]

end LeanUrat.HC1

#print axioms LeanUrat.HC1.D2_carryGrading
