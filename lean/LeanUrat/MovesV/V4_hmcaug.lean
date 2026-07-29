/-  MovesV unit V4-13 `hmcaug_of_hmc` (NEW at REV 7, G1) — the vacuous-repair
    implication: HMC ⟹ HMCAug via the identity refinement (unavoidable for
    any faithful encoding; proves nothing about HMC; consumed by no unit). -/
import LeanUrat.MovesV.V4_hmc

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem hmcaug_of_hmc {n : ℕ} {S : StepSys n} (TE : TmplEvents n S)
    (D : XHDd n S TE) (hHMC : HMC TE D) : HMCAug S TE := by
  sorry

end LeanUrat.MovesV
