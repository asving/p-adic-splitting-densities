/-
Unit `n2_d4r0` (easy; S5 ledger batch, LedgerIV item (2)) — event disjointness.
-/
-- Discharges via the `d4r0` field of the instance `LedgerIV` (the D-5 pin
-- idiom): the only `LedgerIV n2T n2M` is `n2Chain.L`, so this pin reads that
-- structure field, exactly as `n2_xhd_sum` reads `n2Chain.L.xhd_sum`.  N2Sigmas
-- supplies `n2Chain`; it transitively re-exports N2Carriers.
import LeanUrat.MovesS.N2Sigmas

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_d4r0 : ∀ e (τ : n2T.State e) (x : n2M.Rep e τ) (q₀ : ℚ) (N : ℕ)
    (c c' : n2M.Cell e τ) (h h' : n2M.Hgt), (c, h) ≠ (c', h') →
    Disjoint (n2M.cellEvt e τ x c h q₀ N) (n2M.cellEvt e τ x c' h' q₀ N) :=
  n2Chain.L.d4r0

end LeanUrat.MovesS
