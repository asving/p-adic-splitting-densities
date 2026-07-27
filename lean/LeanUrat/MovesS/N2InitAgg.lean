/-
Unit `n2_init_agg` (easy; S5 ledger batch, LedgerIV item (8)) — ENT-AGG.
-/
import LeanUrat.MovesS.N2Sigmas

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_init_agg : ∀ e (τ : n2T.State e) (q₀ : ℚ), q₀ ∈ n2M.Pools →
    n2M.activeState q₀ e τ →
    n2M.ιval e τ q₀ = ∑ ε : n2M.EntShape e τ, n2M.ιsh e τ ε q₀ :=
  n2Chain.L.init_agg

end LeanUrat.MovesS
