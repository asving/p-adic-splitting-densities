/-
Unit `n2_rep_indep` (easy; S5 ledger batch, LedgerIV item (4)) — RS.0(α)'s
weighted grouping at the instance.
-/
import LeanUrat.MovesS.N2Carriers

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_rep_indep : ∀ e (τ : n2T.State e) (o : n2T.Out e τ)
    (x : n2M.Rep e τ) (q₀ : ℚ), q₀ ∈ n2M.Pools → n2M.activeState q₀ e τ →
    n2M.rowVal e τ o q₀ = ∑ c ∈ n2M.cells e τ o, n2M.μcell e τ x c q₀ :=
  sorry

end LeanUrat.MovesS
