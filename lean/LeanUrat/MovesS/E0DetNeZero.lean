/-
Unit U-21c `e0_det_ne_zero` (medium) — `EscapeE0 A → (1 - A).det ≠ 0`; the EMPTY
case is `Matrix.det_isEmpty` (det = 1 ≠ 0 — an empty active block is vacuously
nonsingular, matching "realized states only"); the nonempty case uses U-21a/b.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.PowFixedVector
import LeanUrat.MovesS.MulVecAbsBound

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix

theorem e0_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℚ} (h : EscapeE0 A) : (1 - A).det ≠ 0 :=
  sorry

end LeanUrat.MovesS
