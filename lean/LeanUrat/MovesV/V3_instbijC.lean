/-  MovesV unit V3-5c `inst_bij_eq` — THE ASSEMBLED EQUIV + computation law
    (incl. the zig/gamTie roundtrip check). -/
import LeanUrat.MovesV.V3_instbijB

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem inst_bij_eq {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (DE : XHDdEnt n S V)
    (εT : EntTemplate n) (β₀ : S.Cell) (hl : V.entLands εT β₀) :
    ∃ e : {h : Hpt εT.entDim // (V.entDom εT).Mem h} ≃
        {ε : EntShapeV n // ε.template? = some εT ∧ Realizable V ε β₀},
      ∀ h, (e h).1 = writeHeights εT h.1 := by
  sorry

end LeanUrat.MovesV
