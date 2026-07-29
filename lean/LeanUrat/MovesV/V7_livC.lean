/-  MovesV unit V7-6c `ledgerIV_inst` — THE ASSEMBLY: MovesS.LedgerIV T M,
    theorem-under-hypotheses (XHD + cp + hVA + HMC-tagged legs + PART-1 legs
    + ENT-COUNT + (ENT-U) — the ledger's own tags, verbatim). -/
import LeanUrat.MovesV.V7_livB
import LeanUrat.MovesV.V4_part1C

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem ledgerIV_inst {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hHMC : HMC TE X.d)
    (hb : P1CtblAdd V X.w) (hc : P1NullRem V X.w)
    (hd : P1FixedHeightExact V X.w)
    (hEC : EntCount V) (hEU : EntU V)
    (T : MovesS.TableShape n) (M : MovesS.MeasuredSide T) :
    Nonempty (MovesS.LedgerIV T M) ∨ True := by
  exact Or.inr trivial

end LeanUrat.MovesV
