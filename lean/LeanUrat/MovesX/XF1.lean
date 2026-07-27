/-
Unit XF.1 discCylinder  [E-phase: stated, body sorry]
moves_ref: the (3b) event is level-D cylinder data.
sketch: `polyOfCoeffs … = f.map (toZModPow D)` for monic deg-n; monic-case `discr_map`
helper (Mathlib gap flagged); `PadicInt.ker_toZModPow`. deps: Defs. difficulty: MEDIUM.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem discCylinder (p n D : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (f : Polynomial ℤ_[p])
    (hm : f.Monic) (hd : f.natDegree = n) :
    ((p : ℤ_[p]) ^ D ∣ f.discr ↔
      (polyOfCoeffs (ZMod (p ^ D)) n (fun i => PadicInt.toZModPow D (f.coeff i))).discr = 0) := by
  sorry

end LeanUrat.MovesX
