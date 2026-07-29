/-  MovesV unit V4-9 `rep_indep` — (iv)-REP GIVEN (U-A) + (u-R) + ObsCheck:
    the WEIGHTED measured row is representative-constant.
    `measuredRow` (NAME→HOME) DISPLAYED. -/
import LeanUrat.MovesV.V4_part1A
import LeanUrat.MovesV.V1_UA

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

noncomputable def measuredRow {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (X : XHDw n S) {τ : S.Cell} {q₀ : ℚ}
    (x : S.Hist q₀ τ) : ℝ :=
  ∑' ch : Σ c : DCellAll V τ, Σ D : ℕ, Hpt D, μcellH V X x ch.1 ch.2

theorem rep_row {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} (X : XHDw n S) (P : C15Pack n S) (U : XHDu n S)
    (hobs : ∀ s : Skeleton n, ObsCheck (C.bd s)) {τ : S.Cell} {q₀ : ℚ}
    (hq : q₀ ∈ V.Pools) (x x' : S.Hist q₀ τ) (hzc : S.zc x) (hzc' : S.zc x') :
    measuredRow V X x = measuredRow V X x' := by
  sorry

end LeanUrat.MovesV
