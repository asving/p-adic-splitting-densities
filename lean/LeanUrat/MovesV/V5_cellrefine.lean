/-  MovesV unit V5-8 `cell_refine` (NEW REV 3, F-4 + Codex-9) — the DERIVED
    count-bearing refinement identity: Σ_c P_c·ΣGcell = T·ΣGc — the COUNT
    FACTOR ON BOTH SIDES, displayed; nothing collapsed, nothing decided. -/
import LeanUrat.MovesV.V2_valB
import LeanUrat.MovesV.V5_comphs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open LeanUrat.MovesS (OKat evalAt)
open Classical

/-- the cell-face weight-sum value (dite-eval). -/
noncomputable def gcellVal {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {W : XHDw n S} {TE : TmplEvents n S}
    {D : XHDd n S TE} {Xs : XHDs n S W D} (XsC : XHDsC n S W D V Xs)
    (d : MoveData n C) (c : V.DCellO d.s d.m d.o d.α) (q₀ : ℚ) : ℝ :=
  ∑ j, if hok : XsC.Gcell d c j ∈ OKat q₀
    then ((evalAt q₀ ⟨XsC.Gcell d c j, hok⟩ : ℚ) : ℝ) else 0

theorem cell_refine {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {W : XHDw n S} {TE : TmplEvents n S}
    {D : XHDd n S TE} {Xs : XHDs n S W D}
    (hVA : ValA n C S V) (U : XHDu n S) (DC : XHDdC n S V)
    (hTie : MDomTie V TE D) (XsC : XHDsC n S W D V Xs)
    (hcell : CellPolyPack n C S V) (d : MoveData n C) {q₀ : ℚ}
    (x : S.Hist q₀ (V.toStepCells.symm d.src)) (hzc : S.zc x)
    (hq : q₀ ∈ V.Pools) :
    (letI := V.finDO d.s d.m d.o d.α
     ∑ c : V.DCellO d.s d.m d.o d.α,
       (((hcell.P d.s d.m d.o d.α c).eval q₀ : ℚ) : ℝ) * gcellVal XsC d c q₀)
      = (((C.T d.s d.m d.o d.α d.tix).eval q₀ : ℚ) : ℝ)
          * gcVal Xs (.last (V.moveOf d)) q₀ := by
  sorry

end LeanUrat.MovesV
