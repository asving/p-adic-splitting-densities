/-
Unit `n2_carriers` (medium; S5 construction batch) — the MeasuredSide instance:
Box/Cell/Rep carriers + boxpos/rep_ne (Codex#6-13 split).  The remaining
MeasuredSide data groups are pinned by their own units (n2_events, n2_pools,
n2_heights, n2_ent_flow).
-/
import LeanUrat.MovesS.N2Shape

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

noncomputable def n2M : MeasuredSide n2T := sorry

theorem n2_carriers :
    (∀ e (τ : n2T.State e), Nonempty (n2M.Cell e τ)) ∧
    (∀ e (τ : n2T.State e), Nonempty (n2M.Rep e τ)) ∧
    (∀ e (τ : n2T.State e) (c c' : n2M.Cell 2 n2τ),
      n2M.cellOut 2 n2τ c = n2M.cellOut 2 n2τ c' → c = c') :=
  sorry

end LeanUrat.MovesS
