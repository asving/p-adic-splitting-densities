/-
Unit XF.4 resRootSum  [E-phase: stated, body sorry]
moves_ref: "Res(f, f′) over the n−1 roots of f′" + the n·v_p(n) offset.
sketch: resultant map-commutation helper; root-product over V.L
(`resultant_eq_prod_roots_sub` + eval-product lemmas); lc(f′) = n.
deps: XF.3-independent (V explicit — INTERNAL unit). difficulty: HARD.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem resRootSum (p n : ℕ) [Fact p.Prime] (h2 : 2 ≤ n) (f : Polynomial ℤ_[p])
    (hm : f.Monic) (hd : f.natDegree = n)
    (V : ValExt p ((f.map PadicInt.Coe.ringHom).derivative)) :
    ‖f.resultant f.derivative‖ =
      ‖(n : ℚ_[p])‖ ^ n *
        ((((f.map PadicInt.Coe.ringHom).derivative.map (algebraMap ℚ_[p] V.L)).roots).map
          (fun θ => V.w (Polynomial.aeval θ (f.map PadicInt.Coe.ringHom)))).prod := by
  sorry

end LeanUrat.MovesX
