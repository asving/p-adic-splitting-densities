/-  MovesV unit V5-7c `j_not_marked_tg` (ALGEBRA RE-KEYED F-6) — THE J-FENCE:
    marked row = J + surplus on rosters with ≥ 1 continuing mark per cell;
    strict excess at a multi-eligible cell.  [Gate coincidence decide leg
    deferred — roster deviation.] -/
import LeanUrat.MovesV.V5_jdef

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- marked row = J + surplus (the displayed roster premise carried). -/
theorem j_marked_split {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {W : XHDw n S} {TE : TmplEvents n S}
    {D : XHDd n S TE} {Xs : XHDs n S W D}
    (J : JCells n C S V) (cp : CellPolyPack n C S V)
    (XsC : XHDsC n S W D V Xs) (d : MoveData n C) (q₀ : ℚ)
    (hroster : ∀ c ∈ J.bcells d.s d.m d.o d.α, 1 ≤ V.emult c) :
    ∑ c ∈ J.bcells d.s d.m d.o d.α, (V.emult c : ℝ) * μcellVal cp XsC d c q₀
      = Jval J cp XsC d q₀
        + ∑ c ∈ J.bcells d.s d.m d.o d.α,
            ((V.emult c - 1 : ℕ) : ℝ) * μcellVal cp XsC d c q₀ := by
  rw [jval_once, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Nat.cast_sub (hroster c hc)]
  ring

/-- with a multi-eligible cell (emult = 2) of positive mass the marked row
STRICTLY EXCEEDS the once-per-cell J-sum. -/
theorem j_marked_strict {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {W : XHDw n S} {TE : TmplEvents n S}
    {D : XHDd n S TE} {Xs : XHDs n S W D}
    (J : JCells n C S V) (cp : CellPolyPack n C S V)
    (XsC : XHDsC n S W D V Xs) (d : MoveData n C) (q₀ : ℚ)
    (hroster : ∀ c ∈ J.bcells d.s d.m d.o d.α, 1 ≤ V.emult c)
    (hnn : ∀ c ∈ J.bcells d.s d.m d.o d.α, 0 ≤ μcellVal cp XsC d c q₀)
    (c₀ : V.DCellO d.s d.m d.o d.α) (hc₀ : c₀ ∈ J.bcells d.s d.m d.o d.α)
    (h2 : 2 ≤ V.emult c₀) (hpos : 0 < μcellVal cp XsC d c₀ q₀) :
    Jval J cp XsC d q₀
      < ∑ c ∈ J.bcells d.s d.m d.o d.α,
          (V.emult c : ℝ) * μcellVal cp XsC d c q₀ := by
  sorry

end LeanUrat.MovesV
