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
  -- The inverse construction: extract the height/depth slots from ε and show
  -- that writing them back into the template's slots recovers ε (template-
  -- matching through readOfLetter, uniqueness by V3-3d's readFits_unique).
  obtain ⟨h, hwh⟩ : ∃ h : Hpt εT.entDim, writeHeights εT h = ε := by
    sorry
  refine ⟨h, ?_, hwh⟩
  -- Membership: ε realizes the template at h (Realizable = hR), so the XHD-d
  -- entrance face's no_orphanE places h in the semilinear domain.
  apply DE.no_orphanE εT h β₀
  -- instRealizable εT h β₀ := ∃ ε' ∈ writeHeights? εT h, Realizable V ε' β₀.
  have hsome : writeHeights? εT h = some ε := by
    rw [← hwh]
    exact (Option.some_get (writeHeights_total εT h)).symm
  exact ⟨ε, hsome, hR⟩

end LeanUrat.MovesV
