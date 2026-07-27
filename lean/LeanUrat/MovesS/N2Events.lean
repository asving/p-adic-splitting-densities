/-
Unit `n2_events` (medium; S5 construction batch) — the cell events realizing the
row masses as card ratios (split): the measured rows take the R26 values
  rowVal o_K = q₀⁻³ · rowVal o_spl = 1 − q₀⁻¹ · rowVal o_in = q₀⁻¹ − q₀⁻³
(part1's display: their sum is 1).
-/
import LeanUrat.MovesS.N2Carriers

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_events : ∀ q₀ ∈ n2M.Pools,
    n2M.rowVal 2 n2τ n2oK q₀ = ((q₀ : ℝ))⁻¹ ^ 3 ∧
    n2M.rowVal 2 n2τ n2oSpl q₀ = 1 - ((q₀ : ℝ))⁻¹ ∧
    n2M.rowVal 2 n2τ n2oIn q₀ = ((q₀ : ℝ))⁻¹ - ((q₀ : ℝ))⁻¹ ^ 3 :=
  sorry

end LeanUrat.MovesS
