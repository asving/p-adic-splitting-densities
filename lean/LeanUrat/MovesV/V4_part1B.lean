/-  MovesV unit V4-6b `part1_null` · HARD — the remainder-null limit from leg
    (c) + the monotone assembly bound. -/
import LeanUrat.MovesV.V4_part1A

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem part1_null {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} (X : XHDw n S)
    (hb : P1CtblAdd V X) (hc : P1NullRem V X) (hd : P1FixedHeightExact V X)
    {τ : S.Cell} {q₀ : ℚ} (x : S.Hist q₀ τ) (hzc : S.zc x)
    (hq : q₀ ∈ V.Pools) (hact : V.activeState q₀ τ)
    (v : ℝ) (hv : HasSum (fun ch : Σ c : DCellAll V τ, Σ D : ℕ, Hpt D =>
      μcellH V X x ch.1 ch.2) v) :
    1 ≤ v := by
  sorry

end LeanUrat.MovesV
