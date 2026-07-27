/-
Unit `n2_init_count` (medium; S5 ledger batch) — the card-ratio tie on the one
entrance shape.
-/
import LeanUrat.MovesS.N2Carriers

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_init_count : ∀ e (τ : n2T.State e) (ε : n2M.EntShape e τ)
    (h : n2M.Hgt), h ∈ n2M.ιDom e τ ε → ∀ q₀ ∈ n2M.Pools,
    n2M.activeState q₀ e τ → ∃ N₀, ∀ N ≥ N₀,
    n2M.ιshH e τ ε h q₀ * (Fintype.card (n2M.Box q₀ N) : ℝ)
      = ((n2M.entEvtH e τ ε h q₀ N).card : ℝ) :=
  sorry

end LeanUrat.MovesS
