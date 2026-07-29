/-  MovesV unit V4-7 `part2_row` — PART-2, the marked offspring row:
    Σ T·G + terminal = 1 + surplus; NO substochasticity claimed.
    `markedRow`/`terminalRow`/`surplusRow` (NAME→HOME) DISPLAYED. -/
import LeanUrat.MovesV.V4_part1C

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- the cell's eligible-mark weight (continuing cells: emult; terminal: 0). -/
noncomputable def markWeight {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {τ : S.Cell} : DCellAll V τ → ℕ
  | .inl ⟨_, c⟩ => V.emult c
  | .inr _ => 0

noncomputable def markedRow {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (X : XHDw n S) {τ : S.Cell} {q₀ : ℚ}
    (x : S.Hist q₀ τ) : ℝ :=
  ∑' ch : Σ c : DCellAll V τ, Σ D : ℕ, Hpt D,
    (markWeight V ch.1 : ℝ) * μcellH V X x ch.1 ch.2

noncomputable def terminalRow {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (X : XHDw n S) {τ : S.Cell} {q₀ : ℚ}
    (x : S.Hist q₀ τ) : ℝ :=
  ∑' ch : Σ c : DCellAll V τ, Σ D : ℕ, Hpt D,
    (if ch.1.isRight then 1 else 0) * μcellH V X x ch.1 ch.2

noncomputable def surplusRow {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (X : XHDw n S) {τ : S.Cell} {q₀ : ℚ}
    (x : S.Hist q₀ τ) : ℝ :=
  ∑' ch : Σ c : DCellAll V τ, Σ D : ℕ, Hpt D,
    ((markWeight V ch.1 - 1 : ℕ) : ℝ) * μcellH V X x ch.1 ch.2

theorem part2_row {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} (X : XHDw n S)
    (hb : P1CtblAdd V X) (hc : P1NullRem V X) (hd : P1FixedHeightExact V X)
    {τ : S.Cell} {q₀ : ℚ} (x : S.Hist q₀ τ) (hzc : S.zc x)
    (hq : q₀ ∈ V.Pools) (hact : V.activeState q₀ τ)
    (hmark : ∀ c : DCellAll V τ, c.isLeft → 1 ≤ markWeight V c) :
    markedRow V X x + terminalRow V X x = 1 + surplusRow V X x := by
  sorry

/-- the separate lower bound: row sum ≥ 1 − terminal. -/
theorem part2_ge {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} (X : XHDw n S)
    (hb : P1CtblAdd V X) (hc : P1NullRem V X) (hd : P1FixedHeightExact V X)
    {τ : S.Cell} {q₀ : ℚ} (x : S.Hist q₀ τ) (hzc : S.zc x)
    (hq : q₀ ∈ V.Pools) (hact : V.activeState q₀ τ)
    (hmark : ∀ c : DCellAll V τ, c.isLeft → 1 ≤ markWeight V c) :
    1 - terminalRow V X x ≤ markedRow V X x := by
  sorry

end LeanUrat.MovesV
