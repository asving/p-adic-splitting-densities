/-  MovesV unit V1-8b `xhdds_realized` (SPLIT Codex-19; REV 4 process side) —
    a TmplEvents toy with all SEVEN ties + XHDd + XHDs; at THIS toy HMC is
    TRUE (with V4-11's false-HMC toy they bracket the kernel). -/
import LeanUrat.MovesV.V1_witnessA

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem xhdds_realized :
    ∃ (S : StepSys 1) (TE : TmplEvents 1 S) (D : XHDd 1 S TE)
      (X : XHDw 1 S), Nonempty (XHDs 1 S X D) ∧ HMC TE D := by
  sorry

end LeanUrat.MovesV
