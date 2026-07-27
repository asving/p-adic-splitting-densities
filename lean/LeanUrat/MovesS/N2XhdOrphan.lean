/-
Unit `n2_xhd_orphan` (easy; S5 ledger batch) — no orphan heights (one field).
-/
import LeanUrat.MovesS.N2Carriers

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_xhd_orphan : ∀ e (τ : n2T.State e) (x : n2M.Rep e τ)
    (c : n2M.Cell e τ) (h : n2M.Hgt), h ∉ n2M.HDom e τ c →
    ∀ (q₀ : ℚ) (N : ℕ), n2M.cellEvt e τ x c h q₀ N = ∅ :=
  sorry

end LeanUrat.MovesS
