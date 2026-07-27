/-
Unit `n2_xhd_sum` (easy; S5 ledger batch, LedgerIV item (1)) — XHD resummation at
the instance (one field, R28 split).
-/
import LeanUrat.MovesS.N2Carriers

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_xhd_sum : ∀ e (τ : n2T.State e) (x : n2M.Rep e τ) (c : n2M.Cell e τ)
    (q₀ : ℚ), q₀ ∈ n2M.Pools → n2M.activeState q₀ e τ →
    HasSum (fun h : n2M.HDom e τ c => n2M.gwt e τ c h q₀) (n2M.μcell e τ x c q₀) :=
  sorry

end LeanUrat.MovesS
