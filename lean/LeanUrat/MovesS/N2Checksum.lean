/-
Unit `n2_checksum` (easy; NOTE-W6 check) — β_{(1,2)} + β_{(1,1)²} = 1 (the
checksum shadow).
-/
import LeanUrat.MovesS.N2SolveVals

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Polynomial

theorem n2_checksum (he : 2 ∈ Finset.Icc 1 2) :
    blockSolve n2T n2RB n2hdc n2hK n2hdet 2 he n2τ {n2v12}
      + blockSolve n2T n2RB n2hdc n2hK n2hdet 2 he n2τ {n2v11, n2v11} = 1 := by
  obtain ⟨h12, h11⟩ := n2_solve_vals he
  have hden : algebraMap (Polynomial ℚ) Qq (X ^ 2 + X + 1) ≠ 0 := by
    apply RatFunc.algebraMap_ne_zero
    intro h
    have := congrArg (Polynomial.eval 0) h
    simp at this
  rw [h12, h11, ← add_div, ← map_add, div_eq_one_iff_eq hden]
  congr 1
  ring

end LeanUrat.MovesS
