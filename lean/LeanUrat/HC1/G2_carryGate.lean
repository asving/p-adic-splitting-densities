/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsD

/-!
# HC1.G2_carryGate — the carry-algebra table at e = 2 over F₄ (decide gate)

moves_ref: MOVES 1508–1509. deps: D1, D2. legs: `dOf 1 1 * dOf 1 1 = dOf 0 z̄`,
`dOf 1 c * dOf 0 c' = dOf 1 (c·c')`, and the cocycle identity for all
ρ,σ,τ ∈ ZMod 2. difficulty: easy. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial

/-- The `u_ρ · u_σ` law (D2's first clause / D6's `D6_dOf_mul_dOf`, reproved inline so
G2 stays self-contained and axiom-clean): the twisted product of two homogeneous
generators is the homogeneous generator at the sum coset, scaled by the carry factor
`z̄^{carryExp ρ σ}`. -/
private lemma G2_dOf_mul_dOf {F : Type*} [Field F] {e : ℕ} [NeZero e] {zbar : Fˣ}
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

/-- Unit G2: the e = 2 carry table over F₄ (z̄ a primitive cube root: z̄² = z̄ + 1),
against any D1 ring pack. -/
theorem G2_carryGate :
    ∃ zbar : (GaloisField 2 2)ˣ,
      ((zbar : GaloisField 2 2) ^ 2 = (zbar : GaloisField 2 2) + 1) ∧
      ∀ P : CarryRingPack (GaloisField 2 2) 2 zbar,
        (letI := P.ring;
          dOf (1 : ZMod 2) (1 : GaloisField 2 2) * dOf 1 1
            = dOf 0 ((zbar : GaloisField 2 2))) ∧
        (∀ c c' : GaloisField 2 2, letI := P.ring;
          dOf (1 : ZMod 2) c * dOf 0 c' = dOf 1 (c * c')) ∧
        (∀ ρ σ τ : ZMod 2,
          carryExp ρ σ + carryExp (ρ + σ) τ = carryExp σ τ + carryExp ρ (σ + τ)) := by
  classical
  -- Step 1: exhibit a primitive cube root z̄ (any non-identity unit of the 3-element
  -- unit group of F₄): z̄³ = 1 and z̄ ≠ 1 force z̄² + z̄ + 1 = 0, i.e. z̄² = z̄ + 1.
  haveI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hc4 : Fintype.card (GaloisField 2 2) = 4 := by
    have h := GaloisField.card 2 2 (by norm_num)
    rw [Nat.card_eq_fintype_card] at h
    rw [h]; norm_num
  have hcu : Fintype.card (GaloisField 2 2)ˣ = 3 := by
    rw [Fintype.card_units, hc4]
  have hone : (1 : ℕ) < Fintype.card (GaloisField 2 2)ˣ := by rw [hcu]; norm_num
  obtain ⟨g, hg⟩ := Fintype.exists_ne_of_one_lt_card hone 1
  refine ⟨g, ?_, ?_⟩
  · -- z̄² = z̄ + 1
    set y : GaloisField 2 2 := (g : GaloisField 2 2) with hy
    have hg3 : g ^ 3 = 1 := by
      have := pow_card_eq_one (x := g)
      rwa [hcu] at this
    have hy3 : y ^ 3 = 1 := by
      have : ((g ^ 3 : (GaloisField 2 2)ˣ) : GaloisField 2 2)
          = ((1 : (GaloisField 2 2)ˣ) : GaloisField 2 2) := by rw [hg3]
      simpa [hy] using this
    have hy1 : y ≠ 1 := by
      intro h; apply hg; apply Units.ext; simpa [hy] using h
    have hfac : (y - 1) * (y ^ 2 + y + 1) = 0 := by linear_combination hy3
    have hquad : y ^ 2 + y + 1 = 0 := by
      rcases mul_eq_zero.mp hfac with h | h
      · exact absurd (sub_eq_zero.mp h) hy1
      · exact h
    have h2 : (2 : GaloisField 2 2) = 0 := by
      have := CharP.cast_eq_zero (GaloisField 2 2) 2
      simpa using this
    linear_combination hquad - (y + 1) * h2
  · -- the carry table, for any ring pack P (holds for any z̄)
    intro P
    refine ⟨?_, ?_, ?_⟩
    · -- dOf 1 1 * dOf 1 1 = dOf 0 z̄
      rw [G2_dOf_mul_dOf P]
      have hidx : (1 : ZMod 2) + 1 = 0 := by decide
      have hexp : carryExp (1 : ZMod 2) 1 = 1 := by decide
      rw [hidx, hexp]
      congr 1
      ring
    · -- dOf 1 c * dOf 0 c' = dOf 1 (c * c')
      intro c c'
      rw [G2_dOf_mul_dOf P]
      have hexp : carryExp (1 : ZMod 2) 0 = 0 := by decide
      simp [hexp]
    · -- the cocycle identity over ZMod 2
      decide

end LeanUrat.HC1

#print axioms LeanUrat.HC1.G2_carryGate
