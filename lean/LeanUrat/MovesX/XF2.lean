/-
Unit XF.2 discResBridge  [PROVED]
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
  have hdeg : f.derivative.natDegree = f.natDegree - 1 := Polynomial.natDegree_derivative f
  rw [hdeg, Polynomial.resultant_deriv (Polynomial.natDegree_pos_iff_degree_pos.mp h1),
    hm.leadingCoeff, mul_one, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]

end LeanUrat.MovesX
