/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs

/-!
# Moves/L4_TRANSii — D.7(ii) coefficient-weight scaling (slot decomposition S3')

MOVES ~2191-2195: K1(Φ̂/w') is definitional — `w'` is defined as the slot minimum.
A coefficient `B ∈ Ĉ` (i.e. `inC Φhat B`) develops as the single slot `j = 0`, so
`w'(B) = min_{j} (e'·w(B_j) + j·h') = e'·w(B_0) + 0 = e'·w(B)`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.Moves

open Polynomial

theorem L4_TRANSii {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ) (w' : Polynomial ℤ_[p] → ℤ) (hw' : IsSlotMinWeight w' Φhat e' h' σ.w) (B : Polynomial ℤ_[p]) (hB : B ≠ 0) (hBc : inC Φhat B) : w' B = (e' : ℤ) * σ.w B := by
  classical
  -- `B` develops as the single slot `j = 0`.
  have hBc' : B.degree < Φhat.degree := hBc
  have hΦne : Φhat.degree ≠ ⊥ := fun h => not_lt_bot (h ▸ hBc')
  set Bdev : ℕ → Polynomial ℤ_[p] := fun j => if j = 0 then B else 0 with hBdefn
  have hB0 : Bdev 0 = B := by simp [hBdefn]
  have hdev : IsDevelopment Φhat B Bdev 1 := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      by_cases hj : j = 0
      · subst hj; rw [hB0]; exact hBc'
      · have hz : Bdev j = 0 := by simp [hBdefn, hj]
        rw [hz, degree_zero]; exact bot_lt_iff_ne_bot.mpr hΦne
    · intro j hj
      have : j ≠ 0 := by omega
      simp [hBdefn, this]
    · rw [Finset.sum_range_one, hB0, pow_zero, mul_one]
  obtain ⟨j, hj1, _, hjeq⟩ := (hw' B Bdev 1 hB hdev).2
  have hj0 : j = 0 := Nat.lt_one_iff.mp hj1
  subst hj0
  simpa [hB0] using hjeq

end LeanUrat.Moves
