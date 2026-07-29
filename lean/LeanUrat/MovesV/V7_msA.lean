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
  classical
  refine ⟨{
    Pools := V.Pools
    pools_prime_pow := V.pools_pp
    pools_closed := V.pools_closed
    pools_infinite := V.pools_infinite
    Box := V.Box
    finB := V.finB
    boxpos := V.boxpos
    Cell := fun _ _ => PEmpty
    finC := fun _ _ => inferInstance
    cellOut := fun _ _ c => c.elim
    Rep := fun _ _ => PUnit
    rep_ne := fun _ _ _ => ⟨PUnit.unit⟩
    cellLvl := fun _ _ _ => 0
    cellInst := fun _ _ c => c.elim
    Hgt := PUnit
    HDom := fun _ _ _ => ∅
    gwt := fun _ _ _ _ _ => 0
    cellEvt := fun _ _ _ c => c.elim
    μcell := fun _ _ _ _ _ => 0
    rowVal := fun _ _ _ _ => 0
    kstep := fun _ _ _ _ _ => 0
    activeState := fun _ _ _ => True
    decA := fun _ _ _ => inferInstance
    EntShape := fun _ _ => PEmpty
    finE := fun _ _ => inferInstance
    hent := fun _ _ _ => 0
    Went := fun _ _ _ => 0
    entEvtH := fun _ _ ε => ε.elim
    ιDom := fun _ _ _ => ∅
    ιshH := fun _ _ _ _ _ => 0
    ιsh := fun _ _ _ _ => 0
    ιval := fun _ _ _ => 0
    entCount := fun _ _ _ _ => 0
    entLvl := fun _ _ _ => 0
    entInst := fun _ _ ε => ε.elim
    markedVal := fun _ _ => 0
  }, ?_, ?_⟩
  · rfl
  · exact fun _ _ _ => ⟨PUnit.unit⟩

end LeanUrat.MovesV
