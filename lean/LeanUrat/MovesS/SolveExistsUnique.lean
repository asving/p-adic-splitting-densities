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
    ∃! β : ι → F, β = K *ᵥ β + b :=
  sorry

end LeanUrat.MovesS
