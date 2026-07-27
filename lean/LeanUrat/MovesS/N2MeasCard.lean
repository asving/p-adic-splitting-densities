/-
Unit `n2_meas_card` (medium; S5 ledger batch, LedgerIV item (5)) — the card-ratio
identities at level N (the R7 counting-native masses).
-/
import LeanUrat.MovesS.N2Carriers

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_meas_card : ∀ e (τ : n2T.State e) (x : n2M.Rep e τ)
    (c : n2M.Cell e τ) (h : n2M.Hgt), h ∈ n2M.HDom e τ c →
    ∀ q₀ ∈ n2M.Pools, n2M.activeState q₀ e τ → ∃ N₀, ∀ N ≥ N₀,
    n2M.gwt e τ c h q₀ * (Fintype.card (n2M.Box q₀ N) : ℝ)
      = ((n2M.cellEvt e τ x c h q₀ N).card : ℝ) :=
  sorry

end LeanUrat.MovesS
