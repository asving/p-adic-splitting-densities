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
  sorry

end LeanUrat.MovesV
