/-
Unit XF.2 discResBridge  [E-phase: stated, body sorry]
moves_ref: "Res(f, f′)" ↔ disc for monic f.
sketch: Mathlib `resultant_deriv`, lc = 1, ‖±x‖. deps: Defs. difficulty: MEDIUM band.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem discResBridge (p : ℕ) [Fact p.Prime] (f : Polynomial ℤ_[p]) (hm : f.Monic)
    (h1 : 0 < f.natDegree) : ‖f.discr‖ = ‖f.resultant f.derivative‖ := by
  sorry

end LeanUrat.MovesX
