/-  MovesV unit V1-5 `xhd_discharge` — [1v]-FULL as INHABITATION bookkeeping
    (deliberately NOT `True`-valued; no unit may replace its XHD argument). -/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

def IsFullDischarge (n : ℕ) (S : StepSys n) (TE : TmplEvents n S)
    (C : CtsFamily n) (V : CtsMeasured n C S) : Prop :=
  Nonempty (XHD n S TE V)

theorem cond_of_discharge {n : ℕ} {S : StepSys n} {TE : TmplEvents n S}
    {C : CtsFamily n} {V : CtsMeasured n C S}
    (hd : IsFullDischarge n S TE C V) {P : XHD n S TE V → Prop}
    (hall : ∀ X, P X) : ∃ X, P X :=
  ⟨hd.some, hall _⟩

end LeanUrat.MovesV
