/-
Unit `n2_meas_card` (medium; S5 ledger batch, LedgerIV item (5)) — the card-ratio
identities at level N (the R7 counting-native masses).
-/
-- Discharges via the `meas_card` field of the instance `LedgerIV` (the D-5 pin
-- idiom): the only `LedgerIV n2T n2M` is `n2Chain.L`, so this pin reads that
-- structure field, exactly as `n2_init_count` reads `n2Chain.L.init_count` and
-- `n2_comp` reads `n2Chain.L.comp_once`.  N2Sigmas supplies `n2Chain`; it
-- transitively re-exports N2Carriers.
import LeanUrat.MovesS.N2Sigmas

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
  n2Chain.L.meas_card

end LeanUrat.MovesS
