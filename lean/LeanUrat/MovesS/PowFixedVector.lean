/-
Unit U-21a `pow_fixed_vector` (easy) — fixed vectors persist under powers.
-/
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix

theorem pow_fixed_vector {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℚ} {v : ι → ℚ} (h : A *ᵥ v = v) :
    ∀ k : ℕ, (A ^ k) *ᵥ v = v := by
  intro k
  induction k with
  | zero => rw [pow_zero, Matrix.one_mulVec]
  | succ n ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, h]

end LeanUrat.MovesS
