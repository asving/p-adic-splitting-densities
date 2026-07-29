/-  MovesV unit V4-5 `step_row_eq` (SIGNATURE FIXED C16) — the (iv) STEP
    display GIVEN XHD-w + (U-A) + (XHD-u) + XHD-d/s + MDomTie. -/
import LeanUrat.MovesV.V1_UA
import LeanUrat.MovesV.V1_xhdu
import LeanUrat.MovesV.V1_xhdw
import LeanUrat.MovesV.V1_xhdd

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open LeanUrat.MovesS (OKat evalAt)

theorem step_row {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {TE : TmplEvents n S} {D : XHDd n S TE}
    (P : C15Pack n S) (X : XHDw n S) (U : XHDu n S) (hTie : MDomTie V TE D)
    (Xs : XHDs n S X D) {αc βc : S.Cell} (mv : S.Move αc βc) {q₀ : ℚ}
    (x : S.Hist q₀ αc) (hzc : S.zc x) (hq : q₀ ∈ V.Pools)
    (j : Fin (D.dom (.last mv)).comps.length) :
    HasSum (fun h : {h // ((D.dom (.last mv)).comps.get j).Mem h} =>
        (S.cntraw mv x h.1 : ℝ) * X.g mv h.1 q₀)
      ((S.cntraw mv x ((D.dom (.last mv)).comps.get j).base : ℝ)
        * ((evalAt q₀ ⟨Xs.Gc (.last mv) j,
            Xs.Gc_ok (.last mv) j q₀ (V.pools_sub hq)⟩ : ℚ) : ℝ)) := by
  have hqS : q₀ ∈ S.Pools := V.pools_sub hq
  -- The XHD-s HasSum over the component, scaled by the base count.
  have hG := Xs.Gc_hasSum (.last mv) j q₀ hqS
  have hM := hG.mul_left
    (S.cntraw mv x ((D.dom (.last mv)).comps.get j).base : ℝ)
  -- the base point lies in its own component:
  have hmem_base : (D.dom (.last mv)).Mem ((D.dom (.last mv)).comps.get j).base :=
    ⟨(D.dom (.last mv)).comps.get j, List.get_mem _ _,
      ⟨fun _ => 0, by funext i; simp⟩⟩
  have pos_base : 0 < S.cntraw mv x ((D.dom (.last mv)).comps.get j).base :=
    mem_chainCount_pos D (.last mv) _ hmem_base hqS x hzc
  -- convert the summand: count is constant across the component by (u-T).
  have hfun : (fun h : {h // ((D.dom (.last mv)).comps.get j).Mem h} =>
        (S.cntraw mv x h.1 : ℝ) * X.g mv h.1 q₀)
      = (fun h : {h // ((D.dom (.last mv)).comps.get j).Mem h} =>
        (S.cntraw mv x ((D.dom (.last mv)).comps.get j).base : ℝ)
          * gProd X (.last mv) h.1 q₀) := by
    funext h
    have hmem_h : (D.dom (.last mv)).Mem h.1 :=
      ⟨(D.dom (.last mv)).comps.get j, List.get_mem _ _, h.2⟩
    have pos_h : 0 < S.cntraw mv x h.1 :=
      mem_chainCount_pos D (.last mv) _ hmem_h hqS x hzc
    have hcnt : S.cntraw mv x h.1
        = S.cntraw mv x ((D.dom (.last mv)).comps.get j).base :=
      U.u_T mv x h.1 _ hqS hzc pos_h pos_base
    rw [hcnt]
    rfl
  rw [hfun]
  exact hM

end LeanUrat.MovesV
