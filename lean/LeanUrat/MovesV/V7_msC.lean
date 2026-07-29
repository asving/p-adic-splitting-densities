/-  MovesV unit V7-4c `measured_values_inst` — the measured ℝ-values (gwt =
    count POLYNOMIAL × weight; μcell x-free; rowVal the cell-fiber sum; kstep
    with THE k = 0 KRONECKER δ (REV 4, N-3) and the ∏T count factor (F-4);
    the anti-smuggle pin stands). -/
import LeanUrat.MovesV.V7_msB
import LeanUrat.MovesV.V5_compsig

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem measured_values_inst {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    (T : MovesS.TableShape n) :
    ∃ M : MovesS.MeasuredSide T,
      (∀ e (τ β : T.State e) (q₀ : ℚ),
        M.kstep 0 e τ β q₀ = if τ = β then 1 else 0) := by
  sorry

end LeanUrat.MovesV
