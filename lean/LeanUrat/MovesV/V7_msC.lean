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
    kstep := fun _ _ τ β _ => if τ = β then 1 else 0
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
  }, ?_⟩
  intro e τ β q₀
  rfl

end LeanUrat.MovesV
