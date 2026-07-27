/-
Unit `n2_degpins_tg` (easy; S5 construction batch) — the tg/j per-piece degree
pins (R31: two separate bounds, never a merged sum bound).
-/
import LeanUrat.MovesS.N2PolyGeom

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_degpins_tg : ∀ e (τ : n2T.State e) (o : n2T.Out e τ),
    (n2RB.tgP e τ o).degBoundT = n2T.Wloc e τ o ∧
    (n2RB.tgP e τ o).degBoundS = n2T.Wstate e τ ∧
    (n2RB.jP e τ o).degBoundT = n2T.Wloc e τ o ∧
    (n2RB.jP e τ o).degBoundS = n2T.Wstate e τ :=
  fun e τ o =>
    ⟨n2RB.tg_degT e τ o, n2RB.tg_degS e τ o, n2RB.j_degT e τ o, n2RB.j_degS e τ o⟩

end LeanUrat.MovesS
