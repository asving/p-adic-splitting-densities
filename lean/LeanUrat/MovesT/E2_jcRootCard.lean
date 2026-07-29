/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesC.C4_conditionalMass

/-! # T-E2 `jcRoot_card` (MOVES 7464–7468, incl. the degree-1 base case): the
coordinate-splitting equivalence (MovesC C4's `putOn` idiom). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem jcRoot_card (χ : Fin n → Fin m) (hχ : Function.Injective χ)
    (g : Fin n → ZMod p) :
    Nat.card ↥(rootCell χ g) * p ^ n = p ^ m := by
  classical
  set pred : Fin m → Prop := fun c => ∃ b, χ b = c with hpred
  -- `χ` identifies `Fin n` with the pinned coordinates `{c // pred c}`.
  have hf : Function.Bijective (fun b : Fin n => (⟨χ b, ⟨b, rfl⟩⟩ : {c // pred c})) := by
    refine ⟨fun b₁ b₂ h => hχ (congrArg Subtype.val h), ?_⟩
    rintro ⟨c, b, rfl⟩; exact ⟨b, rfl⟩
  set eχ : Fin n ≃ {c // pred c} := Equiv.ofBijective _ hf with heχ
  -- the coordinate-splitting equivalence: a root cell member is free off the range of χ.
  have er : ↥(rootCell χ g) ≃ ({c // ¬ pred c} → ZMod p) := by
    refine
      { toFun := fun x c => x.1 c.1
        invFun := fun b => ⟨putOn pred (fun c => g (eχ.symm c)) b, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro i
      show putOn pred (fun c => g (eχ.symm c)) b (χ i) = g i
      rw [putOn_apply, dif_pos (⟨i, rfl⟩ : pred (χ i))]
      have h1 : (⟨χ i, ⟨i, rfl⟩⟩ : {c // pred c}) = eχ i := rfl
      simp only [h1, Equiv.symm_apply_apply]
    · intro x
      apply Subtype.ext
      funext c
      show putOn pred (fun c => g (eχ.symm c)) (fun c : {c // ¬ pred c} => x.1 c.1) c = x.1 c
      rw [putOn_apply]
      by_cases hc : pred c
      · rw [dif_pos hc]
        have hcc : χ (eχ.symm ⟨c, hc⟩) = c :=
          congrArg Subtype.val (eχ.apply_symm_apply ⟨c, hc⟩)
        have hx := x.2 (eχ.symm ⟨c, hc⟩)
        rw [hcc] at hx
        exact hx.symm
      · rw [dif_neg hc]
    · intro b
      funext c
      show putOn pred (fun c => g (eχ.symm c)) b c.1 = b c
      rw [putOn_apply, dif_neg c.2]
  -- count via the split, then reconcile the exponents.
  have hcard : Nat.card ↥(rootCell χ g) = p ^ Nat.card {c // ¬ pred c} := by
    rw [Nat.card_congr er, Nat.card_fun, Nat.card_zmod]
  have hsum : Nat.card {c // ¬ pred c} + n = m := by
    have h1 : Nat.card {c // pred c} = n := by
      rw [← Nat.card_congr eχ, Nat.card_fin]
    have h2 : Nat.card (Fin m) = Nat.card {c // pred c} + Nat.card {c // ¬ pred c} := by
      rw [← Nat.card_sum, Nat.card_congr (Equiv.sumCompl pred)]
    rw [Nat.card_fin, h1] at h2
    omega
  rw [hcard, ← pow_add, hsum]

end LeanUrat.MovesT
