/-  MovesV unit V3-5b `inst_bij_surj` — SURJECTIVITY onto the realizable
    concrete ε with template ε̊, GIVEN the entrance exactness face (XHDdEnt). -/
import LeanUrat.MovesV.V3_instbijA
import LeanUrat.MovesV.V3_tfin

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem inst_bij_surj {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (DE : XHDdEnt n S V)
    (εT : EntTemplate n) (β₀ : S.Cell) (ε : EntShapeV n)
    (hT : ε.template? = some εT) (hR : Realizable V ε β₀) :
    ∃ h : Hpt εT.entDim, (V.entDom εT).Mem h ∧ writeHeights εT h = ε := by
  sorry

end LeanUrat.MovesV
