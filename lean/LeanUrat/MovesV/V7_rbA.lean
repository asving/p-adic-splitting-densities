/-  MovesV unit V7-5a `ratBurdens_inst` legs (a)+(b) — tgP/jP (+ the REV-7
    per-cell jPCell fields via V5-7b's jcellPG through dataOf).
    Theorem-under-hypotheses. -/
import LeanUrat.MovesV.V7_msC
import LeanUrat.MovesV.V5_jrat

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem ratBurdens_tg_j {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hTie : MDomTie V TE X.d) (J : JCells n C S V)
    (T : MovesS.TableShape n) (M : MovesS.MeasuredSide T) :
    (∀ (s : Skeleton n) (m : (C.bd s).Letter) (o : (C.bd s).Outc m) (α)
      (hr : J.route s m o = .split) (c : V.DCellO s m o α),
      (jcellPG cp X.sC ⟨s, m, o, J.route_cont s m o hr, α⟩ c).countS = 1) := by
  intro s m o α hr c
  rfl

end LeanUrat.MovesV
