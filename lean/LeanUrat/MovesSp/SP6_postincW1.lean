/-
Unit Sp.n3postincW1 — moves_ref: "POST-INC W = 1 always at n = 3 (every genuine
increment here has μ = 1: g·μ ≤ ℓ and e·ℓ ≤ 3 force μ ≥ 2 into e = g = 1, the
recentering class)."
sketch: decide. difficulty: easy.
-/
import LeanUrat.MovesSp.DefsN3

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem postInc3_W1 : (catalogue3.all fun s => !(s.tag == .postInc)
    || (s.W == 1)) = true := by decide

end LeanUrat.MovesSp
