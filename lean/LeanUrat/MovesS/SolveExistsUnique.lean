/-
Unit U-14 `solve_exists_unique` (medium) — GENERIC CARRIER (R22); witness
`(1-K)⁻¹ *ᵥ b`.  Mathlib: `isUnit_iff_ne_zero` + `Matrix.isUnit_iff_isUnit_det` +
`mul_nonsing_inv`/`nonsing_inv_mul` + `mulVec_mulVec`.  F := Qq at the solve;
F := ℝ at U-24a1 (det transported by `Aℝ_det_iff`).
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.SolveIff

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix

theorem solve_exists_unique {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*}
    [Field F] (K : Matrix ι ι F) (b : ι → F) (hdet : (1 - K).det ≠ 0) :
    ∃! β : ι → F, β = K *ᵥ β + b := by
  have hdetU : IsUnit (1 - K).det := isUnit_iff_ne_zero.mpr hdet
  have hmul_right : (1 - K) * (1 - K)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdetU
  have hmul_left : (1 - K)⁻¹ * (1 - K) = 1 := Matrix.nonsing_inv_mul _ hdetU
  have key : ∀ β : ι → F, (β = K *ᵥ β + b) ↔ ((1 - K) *ᵥ β = b) := by
    intro β
    rw [sub_mulVec, one_mulVec, sub_eq_iff_eq_add, add_comm]
  refine ⟨(1 - K)⁻¹ *ᵥ b, ?_, ?_⟩
  · change (1 - K)⁻¹ *ᵥ b = K *ᵥ ((1 - K)⁻¹ *ᵥ b) + b
    rw [key, mulVec_mulVec, hmul_right, one_mulVec]
  · intro y hy
    have hy' : (1 - K) *ᵥ y = b := (key y).mp hy
    calc y = (1 - K)⁻¹ *ᵥ ((1 - K) *ᵥ y) := by rw [mulVec_mulVec, hmul_left, one_mulVec]
      _ = (1 - K)⁻¹ *ᵥ b := by rw [hy']

end LeanUrat.MovesS
