/-  MovesV unit V5-7a `jcells_once` (ROUTE-KEYED F-6) — J's defining laws:
    each cell ONCE (definitional); the roster tie is a FIELD; `jval_out`
    (REV 5, Codex-10).  [Gate decide/nonzero legs deferred — roster deviation.] -/
import LeanUrat.MovesV.DefsGate

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- Jval sums EACH CELL ONCE — definitional (factors through the cell SET). -/
theorem jval_once {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {W : XHDw n S} {TE : TmplEvents n S}
    {D : XHDd n S TE} {Xs : XHDs n S W D}
    (J : JCells n C S V) (cp : CellPolyPack n C S V)
    (XsC : XHDsC n S W D V Xs) (d : MoveData n C) (q₀ : ℚ) :
    Jval J cp XsC d q₀
      = ∑ c ∈ J.bcells d.s d.m d.o d.α, μcellVal cp XsC d c q₀ :=
  rfl

/-- Jval factors through the OUTCOME quadruple (s, m, o, α): no J object
reads tgt/tcell/hc. -/
theorem jval_out {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {W : XHDw n S} {TE : TmplEvents n S}
    {D : XHDd n S TE} {Xs : XHDs n S W D}
    (J : JCells n C S V) (cp : CellPolyPack n C S V)
    (XsC : XHDsC n S W D V Xs) (d d' : MoveData n C)
    (hs : d.s = d'.s) (hm : HEq d.m d'.m) (ho : HEq d.o d'.o)
    (hα : HEq d.α d'.α) (q₀ : ℚ) :
    Jval J cp XsC d q₀ = Jval J cp XsC d' q₀ := by
  obtain ⟨s, m, o, hc, α⟩ := d
  obtain ⟨s', m', o', hc', α'⟩ := d'
  cases hs
  cases hm
  cases ho
  cases hα
  rfl

end LeanUrat.MovesV
