/-
Unit U-29d-ii `n2_recursion` (medium) — the 1×1 measured fixpoint:
β̂ = q₀⁻³·β̂ + (exit masses); field arithmetic.  Stated as the recursion_meas
obligation at the instance.
-/
import LeanUrat.MovesS.N2Beta

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_recursion : ∀ e (he : e ∈ Finset.Icc 1 2) (τ : n2T.State e)
    (σ' : Multiset n2T.VType) (q₀ : ℚ), q₀ ∈ n2M.Pools →
    n2M.activeState q₀ e τ → ∀ h_ent : ℕ,
    n2B.βmeas e he h_ent τ σ' q₀
      = evalRe n2T n2M n2RB n2hdc e he τ σ' q₀ (fun e' he' => n2B.βmeas e' he' h_ent) :=
  n2B.recursion_meas

end LeanUrat.MovesS
