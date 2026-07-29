/-  MovesV unit V3-9c `init_rat` (RESTATED C23/A-1(3); double-count killed
    REV 3) — INIT-RAT as a THEOREM under its displayed burdens: per
    (template, component) the PolyGeom with countT = the (ENT-U) census
    polynomial, countS = 1, geom = the WEIGHT-ONLY Gent. -/
import LeanUrat.MovesV.V3_aggfullB
import LeanUrat.MovesV.V3_entcount

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open LeanUrat.MovesS (Qq OKat evalAt PolyGeom)

theorem initRat_comp {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (XsEnt : XHDsEnt n S V) (hEU : EntU V)
    (hEC : EntCount V) (hA : AffEnt n) (β₀ : S.Cell) (i : V.EntIx β₀) :
    ∃ P : MovesS.PolyGeom,
      P.countS = 1 ∧ P.geom = XsEnt.Gent β₀ i ∧
      (∀ h : Hpt i.1.1.entDim, ((V.entDom i.1.1).comps.get i.1.2).Mem h →
        ∀ q₀ ∈ V.Pools, (P.countT.eval q₀ : ℚ)
          = V.entCensus (writeHeights i.1.1 h) β₀ q₀) ∧
      ∀ q₀ (hq : q₀ ∈ V.Pools), ∃ hok : P.val ∈ OKat q₀,
        ((evalAt q₀ ⟨P.val, hok⟩ : ℚ) : ℝ) = iotaShV V XsEnt i q₀ := by
  sorry

theorem initRat_agg {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (XsEnt : XHDsEnt n S V) (hEU : EntU V)
    (hEC : EntCount V) (hA : AffEnt n) (β₀ : S.Cell) :
    ∃ G : Qq, ∀ q₀ (hq : q₀ ∈ V.Pools), ∃ hok : G ∈ OKat q₀,
      ((evalAt q₀ ⟨G, hok⟩ : ℚ) : ℝ) = iotaValV V XsEnt β₀ q₀ := by
  sorry

end LeanUrat.MovesV
