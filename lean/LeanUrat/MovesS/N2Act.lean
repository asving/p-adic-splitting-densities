/-
Unit `n2_act` (easy; S5 ledger batch, LedgerIV item (7)) — act_target; the
instance is all-active, so the inactive case is vacuous.
-/
import LeanUrat.MovesS.N2Carriers

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_act : ∀ e (τ β : n2T.State e) (q₀ : ℚ), q₀ ∈ n2M.Pools →
    ¬ n2M.activeState q₀ e β → n2M.kstep 1 e τ β q₀ = 0 :=
  sorry

end LeanUrat.MovesS
