/-
Unit Sp.shE1 — moves_ref: "At e = 1: t = 0 ((P2)), σ = 0 — THE SYSTEMS COINCIDE
(a = a^geo = s₀′ = ord_z R; FC4's e = 1 clause)".
sketch: `simp [shSigma, Sh, geoPos, Int.fdiv_one, ht]`. difficulty: easy.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem sh_e1 (h s t γ s0 : ℤ) (ht : t = 0) :
    shSigma t γ 1 = 0 ∧ Sh t γ 1 (geoPos 1 t γ s0) = s0 := by
  simp [shSigma, Sh, geoPos, Int.fdiv_one, ht]

end LeanUrat.MovesSp
