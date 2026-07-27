/-
Unit `n2_comp` (easy; S5 ledger batch, LedgerIV item (9)) — comp_once, a one-term
height sum at this instance.
-/
-- Discharges via the `comp_once` field of the instance `LedgerIV` (the D-5 pin
-- idiom): the only `LedgerIV n2T n2M` is `n2Chain.L`, so this pin reads that
-- structure field, exactly as `n2_part1` reads `n2Chain.L.part1`.  N2Sigmas
-- supplies `n2Chain`; it transitively re-exports N2Carriers.
import LeanUrat.MovesS.N2Sigmas

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_comp : ∀ e (τ : n2T.State e) (ε : n2M.EntShape e τ) (q₀ : ℚ),
    q₀ ∈ n2M.Pools → n2M.activeState q₀ e τ →
    HasSum (fun h : n2M.ιDom e τ ε => n2M.ιshH e τ ε h q₀) (n2M.ιsh e τ ε q₀) :=
  n2Chain.L.comp_once

end LeanUrat.MovesS
