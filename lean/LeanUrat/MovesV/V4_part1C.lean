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
  obtain ⟨v, hv_le, hv_sum⟩ := part1_ctbl X hb hd x hzc hq hact
  have hv_ge : 1 ≤ v := part1_null X hb hc hd x hzc hq hact v hv_sum
  have hv1 : v = 1 := le_antisymm hv_le hv_ge
  exact hv1 ▸ hv_sum

end LeanUrat.MovesV
