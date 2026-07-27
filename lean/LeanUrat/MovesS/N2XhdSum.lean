/-
Unit `n2_xhd_sum` (easy; S5 ledger batch, LedgerIV item (1)) — XHD resummation at
the instance (one field, R28 split).
-/
-- Discharges via the `xhd_sum` field of the instance `LedgerIV` (the D-5 pin
-- idiom): the only `LedgerIV n2T n2M` is `n2Chain.L`, so this pin reads that
-- structure field, exactly as `n2_part1` reads `n2Chain.L.part1`.  N2Sigmas
-- supplies `n2Chain`; it transitively re-exports N2Carriers.
import LeanUrat.MovesS.N2Sigmas

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_xhd_sum : ∀ e (τ : n2T.State e) (x : n2M.Rep e τ) (c : n2M.Cell e τ)
    (q₀ : ℚ), q₀ ∈ n2M.Pools → n2M.activeState q₀ e τ →
    HasSum (fun h : n2M.HDom e τ c => n2M.gwt e τ c h q₀) (n2M.μcell e τ x c q₀) :=
  n2Chain.L.xhd_sum

end LeanUrat.MovesS
