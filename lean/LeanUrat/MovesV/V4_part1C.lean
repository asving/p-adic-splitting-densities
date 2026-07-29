/-  MovesV unit V4-6c `part1` — PART-1 ASSEMBLED: the per-cell ratios over the
    whole countable partition sum to 1 (never a finite-pool identity). -/
import LeanUrat.MovesV.V4_part1B

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem part1 {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} (X : XHDw n S)
    (hb : P1CtblAdd V X) (hc : P1NullRem V X) (hd : P1FixedHeightExact V X)
    {τ : S.Cell} {q₀ : ℚ} (x : S.Hist q₀ τ) (hzc : S.zc x)
    (hq : q₀ ∈ V.Pools) (hact : V.activeState q₀ τ) :
    HasSum (fun ch : Σ c : DCellAll V τ, Σ D : ℕ, Hpt D =>
      μcellH V X x ch.1 ch.2) 1 := by
  sorry

end LeanUrat.MovesV
