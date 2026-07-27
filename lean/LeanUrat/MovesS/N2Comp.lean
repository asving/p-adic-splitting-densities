/-
Unit `n2_comp` (easy; S5 ledger batch, LedgerIV item (9)) — comp_once, a one-term
height sum at this instance.
-/
import LeanUrat.MovesS.N2Carriers

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_comp : ∀ e (τ : n2T.State e) (ε : n2M.EntShape e τ) (q₀ : ℚ),
    q₀ ∈ n2M.Pools → n2M.activeState q₀ e τ →
    HasSum (fun h : n2M.ιDom e τ ε => n2M.ιshH e τ ε h q₀) (n2M.ιsh e τ ε q₀) :=
  sorry

end LeanUrat.MovesS
