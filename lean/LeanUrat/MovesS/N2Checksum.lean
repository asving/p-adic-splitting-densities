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

theorem n2_checksum (he : 2 ∈ Finset.Icc 1 2) :
    blockSolve n2T n2RB n2hdc n2hK n2hdet 2 he n2τ {n2v12}
      + blockSolve n2T n2RB n2hdc n2hK n2hdet 2 he n2τ {n2v11, n2v11} = 1 :=
  sorry

end LeanUrat.MovesS
