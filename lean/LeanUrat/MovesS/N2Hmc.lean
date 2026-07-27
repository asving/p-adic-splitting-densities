/-
Unit `n2_hmc` (easy; S5 ledger batch) — scalar powers: kstep (k+1) = kstep k · q₀⁻³
(the 1×1 HMC).
-/
import LeanUrat.MovesS.N2Sigmas

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_hmc : ∀ (k : ℕ) e (τ β : n2T.State e) (q₀ : ℚ), q₀ ∈ n2M.Pools →
    n2M.activeState q₀ e τ →
    n2M.kstep (k + 1) e τ β q₀
      = ∑ γ : n2T.State e, n2M.kstep k e τ γ q₀ * n2M.kstep 1 e γ β q₀ :=
  n2Chain.L.hmc

end LeanUrat.MovesS
