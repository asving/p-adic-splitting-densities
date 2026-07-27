/-
Unit `n2_part1` (easy; S5 ledger batch, LedgerIV item (3)) — the partition of
unity; the display: q₀⁻³ + (1 − q₀⁻¹) + (q₀⁻¹ − q₀⁻³) = 1 (`field_simp`).
-/
import LeanUrat.MovesS.N2Carriers

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_part1 : ∀ e ∈ Finset.Icc 1 2, ∀ (τ : n2T.State e) (x : n2M.Rep e τ)
    (q₀ : ℚ), q₀ ∈ n2M.Pools → n2M.activeState q₀ e τ →
    ∑ c : n2M.Cell e τ, n2M.μcell e τ x c q₀ = 1 :=
  sorry

end LeanUrat.MovesS
