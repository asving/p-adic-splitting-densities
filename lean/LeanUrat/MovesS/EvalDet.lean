/-
Unit U-20 `eval_det` (easy) — INFRA; moves_ref the S.4(ii) "K_e(p) = A" reading.
via `RingHom.map_det`.
-/
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix

theorem eval_det {ι : Type*} [Fintype ι] [DecidableEq ι] {q₀ : ℚ}
    (A : Matrix ι ι (OKat q₀)) :
    evalAt q₀ A.det = (A.map (evalAt q₀)).det :=
  sorry

end LeanUrat.MovesS
