/-  MovesV unit V7-6a1 `ledgerIV_cells` (RE-SPLIT REV 4, G-2; MarkDisj
    premises REMOVED REV 7, C8) — THE CELL SUITE: meas_card / xhd_no_stray /
    xhd_no_orphan (three legs) at the instance, GIVEN V + X(dC) + cp. -/
import LeanUrat.MovesV.V7_msC

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem ledgerIV_cells {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    (d : MoveData n C) {q₀ : ℚ}
    (x : S.Hist q₀ (V.toStepCells.symm d.src)) (hzc : S.zc x)
    (hq : q₀ ∈ V.Pools) (c : V.DCellO d.s d.m d.o d.α)
    (h : Hpt (S.dim (V.moveOf d))) (hmem : (V.cdom d c).Mem h) :
    ∃ N₀, ∀ N ≥ N₀, (V.cellEvt d x c h N).Nonempty := by
  sorry

theorem ledgerIV_orphan {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    (d : MoveData n C) {q₀ : ℚ}
    (x : S.Hist q₀ (V.toStepCells.symm d.src)) (hzc : S.zc x)
    (hq : q₀ ∈ V.Pools) (c : V.DCellO d.s d.m d.o d.α)
    (h : Hpt (S.dim (V.moveOf d))) (hout : ¬ (V.cdom d c).Mem h) (N : ℕ) :
    V.cellEvt d x c h N = ∅ := by
  sorry

end LeanUrat.MovesV
