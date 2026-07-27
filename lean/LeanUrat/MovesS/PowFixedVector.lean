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
    ∀ k : ℕ, (A ^ k) *ᵥ v = v :=
  sorry

end LeanUrat.MovesS
