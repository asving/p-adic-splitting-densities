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
  classical
  -- instCensus at any point IS the total-writeHeights census.
  have hIC : ∀ (εT : EntTemplate n) (h : Hpt εT.entDim),
      V.instCensus εT h β₀ q₀ = V.entCensus (writeHeights εT h) β₀ q₀ := by
    intro εT h
    unfold CtsMeasured.instCensus
    have hsome : writeHeights? εT h = some (writeHeights εT h) :=
      (Option.some_get (writeHeights_total εT h)).symm
    rw [hsome]; simp
  -- (ENT-U): the census is constant on the component, so the fibre mass is
  -- entCount · (weight-only Gent sum).
  obtain ⟨P, _, hP⟩ := hEU β₀ i
  have hconst : ∀ x : {h // ((V.entDom i.1.1).comps.get i.1.2).Mem h},
      (V.instCensus i.1.1 x.1 β₀ q₀ : ℝ) = (V.entCount i q₀ : ℝ) := by
    intro x
    have e1 := hP x.1 x.2 q₀ hq
    have e2 := hP _ (linset_base_mem ((V.entDom i.1.1).comps.get i.1.2)) q₀ hq
    have hqq : (V.entCensus (writeHeights i.1.1 x.1) β₀ q₀ : ℚ)
        = (V.entCensus (writeHeights i.1.1
            ((V.entDom i.1.1).comps.get i.1.2).base) β₀ q₀ : ℚ) :=
      e1.symm.trans e2
    rw [hIC i.1.1 x.1,
      show V.entCount i q₀
          = V.instCensus i.1.1 ((V.entDom i.1.1).comps.get i.1.2).base β₀ q₀ from rfl,
      hIC i.1.1 ((V.entDom i.1.1).comps.get i.1.2).base]
    exact_mod_cast hqq
  have hfun : (fun x : {h // ((V.entDom i.1.1).comps.get i.1.2).Mem h} =>
        ιshH V i.1.1 x.1 β₀ q₀)
      = (fun x => (V.entCount i q₀ : ℝ)
          * (q₀ : ℝ) ^ (-((instA i.1.1 x.1 : ℕ) : ℤ))) := by
    funext x; unfold ιshH; rw [hconst x]
  have hval : iotaShV V X.sEnt i q₀
      = (V.entCount i q₀ : ℝ)
        * ((LeanUrat.MovesS.evalAt q₀
            ⟨X.sEnt.Gent β₀ i, X.sEnt.Gent_ok β₀ i q₀ hq⟩ : ℚ) : ℝ) := by
    unfold iotaShV; rw [dif_pos hq]
  rw [hfun, hval]
  exact (X.sEnt.Gent_hasSum β₀ i q₀ hq).mul_left (V.entCount i q₀ : ℝ)

end LeanUrat.MovesV
