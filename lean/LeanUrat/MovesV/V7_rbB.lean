/-  MovesV unit V7-5b `ratBurdens_inst` leg (c) — ιP from V3-9c(a)'s
    per-component PolyGeoms under V7-4b's EntIx keying. -/
import LeanUrat.MovesV.V7_rbA
import LeanUrat.MovesV.V3_initrat

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem ratBurdens_iota {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (hEU : EntU V) (hEC : EntCount V) (hA : AffEnt n)
    (β₀ : S.Cell) (i : V.EntIx β₀) :
    ∃ P : MovesS.PolyGeom, P.countS = 1 ∧ P.geom = X.sEnt.Gent β₀ i := by
  obtain ⟨P, h1, h2, _, _⟩ := initRat_comp V X.sEnt hEU hEC hA β₀ i
  exact ⟨P, h1, h2⟩

end LeanUrat.MovesV
