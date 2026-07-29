/-  MovesV unit V5-7b `j_rat` (PER-(τ,o) C8; OUTCOME-LEVEL quantifier REV 5;
    PER-CELL clause REV 7, C15) — (J-RAT) = CL-18: the deliverable, with the
    per-cell `jcellPG` clauses and the symbolic fiber sum. -/
import LeanUrat.MovesV.V5_jdef
import LeanUrat.MovesV.V0_partition
import LeanUrat.MovesV.V1_xhds

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open LeanUrat.MovesS (OKat evalAt)

theorem jRat {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {W : XHDw n S} {TE : TmplEvents n S}
    {D : XHDd n S TE} {Xs : XHDs n S W D}
    (J : JCells n C S V) (XsC : XHDsC n S W D V Xs)
    (hcell : CellPolyPack n C S V) (s : Skeleton n) (m : (C.bd s).Letter)
    (o : (C.bd s).Outc m) (α : (C.bd s).CellIdx)
    (hr : J.route s m o = .split) :
    ∃ P : MovesS.PolyGeom, P.degBoundT = C.Wloc s m ∧
      P.degBoundS = (C.bd s).Wstate ∧
      (∑ c ∈ J.bcells s m o α,
        (jcellPG hcell XsC ⟨s, m, o, J.route_cont s m o hr, α⟩ c).val
          = P.val) ∧
      ∀ q₀ ∈ S.Pools, ∃ hok : P.val ∈ OKat q₀,
        ((evalAt q₀ ⟨P.val, hok⟩ : ℚ) : ℝ)
          = Jval J hcell XsC ⟨s, m, o, J.route_cont s m o hr, α⟩ q₀ := by
  sorry

/-- THE PER-CELL CLAUSE (`jcell_interp`'s exact shape at the instance). -/
theorem jRat_cell {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {W : XHDw n S} {TE : TmplEvents n S}
    {D : XHDd n S TE} {Xs : XHDs n S W D}
    (J : JCells n C S V) (XsC : XHDsC n S W D V Xs)
    (hcell : CellPolyPack n C S V) (s : Skeleton n) (m : (C.bd s).Letter)
    (o : (C.bd s).Outc m) (α : (C.bd s).CellIdx)
    (hr : J.route s m o = .split)
    (c : V.DCellO s m o α) :
    ∀ q₀ ∈ S.Pools,
      ∃ hok : (jcellPG hcell XsC ⟨s, m, o, J.route_cont s m o hr, α⟩ c).val
          ∈ OKat q₀,
      ((evalAt q₀ ⟨_, hok⟩ : ℚ) : ℝ)
        = μcellVal hcell XsC ⟨s, m, o, J.route_cont s m o hr, α⟩ c q₀ := by
  sorry

end LeanUrat.MovesV
