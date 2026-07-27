/-
Unit `n2_det` (easy; the NOTE-W6 geometric-series check — retagged, Fable#8-O-4:
the note's W6 display, unrelated to the pin W-6 = AVAgree) —
`(1 - Kmat).det = (q³−1)/q³ ≠ 0`.  Also carries `n2hdet`, the DetHyp term the
downstream checks consume (block 1: Kmat = 0, det = 1).
-/
import LeanUrat.MovesS.N2PolyGeom
import LeanUrat.MovesS.N2ScsData

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Polynomial

theorem n2_det (he : 2 ∈ Finset.Icc 1 2) :
    (1 - Kmat n2T n2RB 2 (n2hK 2 he)).det
      = algebraMap (Polynomial ℚ) Qq (X ^ 3 - 1) / algebraMap (Polynomial ℚ) Qq (X ^ 3) ∧
    (1 - Kmat n2T n2RB 2 (n2hK 2 he)).det ≠ 0 :=
  sorry

theorem n2hdet : DetHyp n2T n2RB n2hK := sorry

end LeanUrat.MovesS
