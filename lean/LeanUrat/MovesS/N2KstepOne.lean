/-
Unit `n2_kstep_one` (easy; S5 ledger batch, LedgerIV item (6)) — the 1×1 base
tie: kstep 1 = the kcol row mass (q₀⁻³), in the pinned hK-free existential-cast
form (G1).
-/
import LeanUrat.MovesS.N2Carriers

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_kstep_one : ∀ e (τ β : n2T.State e) (q₀ : ℚ), q₀ ∈ n2M.Pools →
    n2M.activeState q₀ e τ →
    n2M.kstep 1 e τ β q₀ =
    ∑ o ∈ {o : n2T.Out e τ | routeOf (n2T.odata e τ o) = .kcol ∧
        ∃ μ ∈ (n2T.odata e τ o).mem, ∃ h : μ.size = e, h ▸ μ.status = Sum.inr β
      }.toFinset, n2M.rowVal e τ o q₀ :=
  sorry

end LeanUrat.MovesS
