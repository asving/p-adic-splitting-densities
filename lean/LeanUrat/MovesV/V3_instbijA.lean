/-  MovesV unit V3-5a `inst_bij_inj` · HARD — INJECTIVITY of the instantiation
    map (V3-3d's spWord_faithful: heights + u*-codes determine the reads). -/
import LeanUrat.MovesV.V3_spwordD

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem inst_bij_inj {n : ℕ} (εT : EntTemplate n) :
    Function.Injective (writeHeights εT) := by
  sorry

end LeanUrat.MovesV
