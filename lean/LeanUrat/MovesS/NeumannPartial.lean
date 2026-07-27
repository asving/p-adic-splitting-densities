/-
Unit U-23a `neumann_partial` (easy) — the telescope identity.
-/
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix

theorem neumann_partial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (k : ℕ) :
    (1 - A) * (∑ m ∈ Finset.range k, A ^ m) = 1 - A ^ k :=
  mul_neg_geom_sum A k

end LeanUrat.MovesS
