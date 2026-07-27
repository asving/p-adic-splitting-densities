/-
Unit `n2_rs1eq` (easy; S5 chain batch, split) — rs1_equates by construction.
-/
import LeanUrat.MovesS.N2Sigmas

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_rs1eq : ∀ p ∈ n2Chain.PrimePools,
    (∑ σ ∈ n2Chain.Sigmas, n2Chain.Rval σ p) = n2Chain.decidedTotal p :=
  n2Chain.rs1_equates

end LeanUrat.MovesS
