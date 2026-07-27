/-
Unit `n2_init_count` (medium; S5 ledger batch) — the card-ratio tie on the one
entrance shape.
-/
-- Discharges via the `init_count` field of the instance `LedgerIV` (the D-5 pin
-- idiom): the only `LedgerIV n2T n2M` is `n2Chain.L`, so this pin reads that
-- structure field, exactly as `n2_comp` reads `n2Chain.L.comp_once`.  N2Sigmas
-- supplies `n2Chain`; it transitively re-exports N2Carriers.
import LeanUrat.MovesS.N2Sigmas

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
  n2Chain.L.init_count

end LeanUrat.MovesS
