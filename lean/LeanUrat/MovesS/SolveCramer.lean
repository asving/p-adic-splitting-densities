/-
Unit U-15 `solve_cramer` (medium) — the adjugate/Cramer form; [DecidableEq ι]
(Fable#5-F4).  moves_ref: "β_e = adj(I − K_e) b_e / det(I − K_e) entrywise"
(RS.2's conditionality = RatBurdens by construction, in (iv)-POLY form).
Mathlib: `Matrix.inv_def`/`cramer_eq_adjugate_mulVec`/
`det_smul_inv_mulVec_eq_cramer`.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.SolveExistsUnique

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix

theorem solve_cramer {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [Field F]
    (K : Matrix ι ι F) (b : ι → F) (hdet : (1 - K).det ≠ 0) :
    (1 - K)⁻¹ *ᵥ b = fun τ => ((1 - K).det)⁻¹ * ((1 - K).adjugate *ᵥ b) τ := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_mulVec]
  rfl

end LeanUrat.MovesS
