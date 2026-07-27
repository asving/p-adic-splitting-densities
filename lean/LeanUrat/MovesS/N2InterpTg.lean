/-
Unit `n2_interp_tg` (medium; S5 construction batch) — the tg/j interpolation laws
at every pool (split): the evaluated presentations equal the measured rows of
n2_events.
-/
import LeanUrat.MovesS.N2PolyGeom
import LeanUrat.MovesS.N2Events

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_interp_tg :
    ∀ e (τ : n2T.State e) (o : n2T.Out e τ) (q₀ : ℚ) (h : q₀ ∈ n2M.Pools),
    (routeOf (n2T.odata e τ o) ≠ .split →
      ((evalAt q₀ ⟨(n2RB.tgP e τ o).val, n2RB.tg_ok e τ o q₀ h⟩ : ℚ) : ℝ)
        = n2M.rowVal e τ o q₀) ∧
    (routeOf (n2T.odata e τ o) = .split →
      ((evalAt q₀ ⟨(n2RB.jP e τ o).val, n2RB.j_ok e τ o q₀ h⟩ : ℚ) : ℝ)
        = n2M.rowVal e τ o q₀) :=
  fun e τ o q₀ h => ⟨n2RB.tg_interp e τ o q₀ h, n2RB.j_interp e τ o q₀ h⟩

end LeanUrat.MovesS
