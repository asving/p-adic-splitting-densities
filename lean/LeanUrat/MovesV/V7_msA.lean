/-  MovesV unit V7-4a `measured_cells_inst` — the `MovesS.MeasuredSide`
    cells/boxes/state half, GIVEN V + X + cp (theorem-under-data; the
    per-pool Rep family (REV 5, M-3), the DOUBLE dite cellEvt (REV 6, G-B),
    the F-5 state-census wiring).  [E-PHASE FORM: existence-with-clauses
    statement; the field-by-field construction is the prover's.] -/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesV.V2_valB

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem measured_cells_inst {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    (T : MovesS.TableShape n) :
    ∃ M : MovesS.MeasuredSide T,
      M.Pools = V.Pools ∧
      (∀ e (he : e ∈ Finset.Icc 1 n) (τ : T.State e), Nonempty (M.Rep e τ)) := by
  sorry

end LeanUrat.MovesV
