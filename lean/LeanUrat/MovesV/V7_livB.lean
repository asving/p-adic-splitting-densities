/-  MovesV unit V7-6b `ledgerIV_sums` — THE SUM/VALUE SUITE: xhd_sum via
    Gcell_hasSum ×-scaled; kstep_one via V5-8's cell_refine (omem_sel +
    omem_size + tcellM_sel cited); comp_once via Gent_hasSum × (ENT-U);
    init_agg rfl-level at the ιval def. -/
import LeanUrat.MovesV.V7_livA2
import LeanUrat.MovesV.V5_cellrefine
import LeanUrat.MovesV.V3_aggfullB

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem ledgerIV_xhd_sum {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    (d : MoveData n C) (c : V.DCellO d.s d.m d.o d.α)
    (j : Fin (V.cdom d c).comps.length) {q₀ : ℚ} (hq : q₀ ∈ S.Pools) :
    HasSum (fun h : {h // ((V.cdom d c).comps.get j).Mem h} =>
        (((cp.P d.s d.m d.o d.α c).eval q₀ : ℚ) : ℝ)
          * X.w.g (V.moveOf d) h.1 q₀)
      ((((cp.P d.s d.m d.o d.α c).eval q₀ : ℚ) : ℝ)
        * ((LeanUrat.MovesS.evalAt q₀
            ⟨X.sC.Gcell d c j, X.sC.Gcell_ok d c j q₀ hq⟩ : ℚ) : ℝ)) :=
  (X.sC.Gcell_hasSum d c j q₀ hq).mul_left _

theorem ledgerIV_comp_once {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (hEU : EntU V) (β₀ : S.Cell) (i : V.EntIx β₀)
    {q₀ : ℚ} (hq : q₀ ∈ V.Pools) :
    HasSum (fun h : {h // ((V.entDom i.1.1).comps.get i.1.2).Mem h} =>
        ιshH V i.1.1 h.1 β₀ q₀) (iotaShV V X.sEnt i q₀) := by
  sorry

end LeanUrat.MovesV
