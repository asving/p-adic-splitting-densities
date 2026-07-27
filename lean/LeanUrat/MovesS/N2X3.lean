/-
Unit `n2_x3` (easy; S5 chain batch, Codex#6-13 split) — decidedTotal := Σ Rval;
x3_total by construction.
-/
import LeanUrat.MovesS.N2Sigmas

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_x3 :
    (∀ q₀ : ℚ, n2Chain.decidedTotal q₀ = ∑ σ ∈ n2Chain.Sigmas, n2Chain.Rval σ q₀) ∧
    (∀ p ∈ n2Chain.PrimePools, n2Chain.decidedTotal p = 1) :=
  sorry

end LeanUrat.MovesS
