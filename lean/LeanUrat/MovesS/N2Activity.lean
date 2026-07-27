/-
Unit `n2_activity` (easy; S5 construction batch) — cellP ≡ 1 per cell +
cellP_deg/cellP_nonzero + cellP_count (singleton cellInst at each cell's level)
+ act_iff (all states active at all pools — R45's per-cell form; countS_cells is
GONE, R50).
-/
import LeanUrat.MovesS.N2PolyGeom

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_activity :
    (∀ e (τ : n2T.State e) (c : n2M.Cell e τ), n2RB.cellP e τ c = 1) ∧
    (∀ e (τ : n2T.State e) (c : n2M.Cell e τ) (q₀ : ℚ),
      q₀ ∈ n2M.Pools →
      (n2M.cellInst e τ c q₀ (n2M.cellLvl e τ c)).card = 1) ∧
    (∀ (q₀ : ℚ) e (τ : n2T.State e), n2M.activeState q₀ e τ) :=
  sorry

end LeanUrat.MovesS
