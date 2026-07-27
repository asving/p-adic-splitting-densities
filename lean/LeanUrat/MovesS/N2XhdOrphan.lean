/-
Unit `n2_xhd_orphan` (easy; S5 ledger batch) — no orphan heights (one field).
-/
-- Discharges via the `xhd_no_orphan` field of the instance `LedgerIV` (the D-5
-- pin idiom): the only `LedgerIV n2T n2M` is `n2Chain.L`, so this pin reads that
-- structure field, exactly as `n2_part1` reads `n2Chain.L.part1`.  N2Sigmas
-- supplies `n2Chain`; it transitively re-exports N2Carriers.
import LeanUrat.MovesS.N2Sigmas

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_xhd_orphan : ∀ e (τ : n2T.State e) (x : n2M.Rep e τ)
    (c : n2M.Cell e τ) (h : n2M.Hgt), h ∉ n2M.HDom e τ c →
    ∀ (q₀ : ℚ) (N : ℕ), n2M.cellEvt e τ x c h q₀ N = ∅ :=
  n2Chain.L.xhd_no_orphan

end LeanUrat.MovesS
