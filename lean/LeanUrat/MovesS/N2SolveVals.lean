/-
Unit `n2_solve_vals` (easy; NOTE-W6 check) — the reduced solve entries
β_{(1,2)} = (q+1)/(q²+q+1), β_{(1,1)²} = q²/(q²+q+1) — the note-displayed
denominator EXACTLY (`field_simp` over `RatFunc ℚ`).
-/
import LeanUrat.MovesS.N2Det
import LeanUrat.MovesS.BlockSolve

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Polynomial

theorem n2_solve_vals (he : 2 ∈ Finset.Icc 1 2) :
    blockSolve n2T n2RB n2hdc n2hK n2hdet 2 he n2τ {n2v12}
      = algebraMap (Polynomial ℚ) Qq (X + 1)
        / algebraMap (Polynomial ℚ) Qq (X ^ 2 + X + 1) ∧
    blockSolve n2T n2RB n2hdc n2hK n2hdet 2 he n2τ {n2v11, n2v11}
      = algebraMap (Polynomial ℚ) Qq (X ^ 2)
        / algebraMap (Polynomial ℚ) Qq (X ^ 2 + X + 1) :=
  sorry

end LeanUrat.MovesS
