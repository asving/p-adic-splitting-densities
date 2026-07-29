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

/-- `μcellH` is nonnegative: counts are naturals and the pool base `q₀ > 1`. -/
theorem μcellH_nonneg {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} (X : XHDw n S) {τ : S.Cell} {q₀ : ℚ}
    (x : S.Hist q₀ τ) (hq : q₀ ∈ V.Pools)
    (c : DCellAll V τ) (ch2 : Σ D : ℕ, Hpt D) :
    0 ≤ μcellH V X x c ch2 := by
  have hq0 : (0 : ℝ) ≤ (q₀ : ℝ) := by
    have h1 : (1 : ℚ) < q₀ := S.pools_gt_one q₀ (V.pools_sub hq)
    exact_mod_cast le_of_lt (lt_trans one_pos h1)
  obtain ⟨D, h⟩ := ch2
  rcases c with ⟨d, cc⟩ | ⟨v, d, cc⟩ <;>
    simp only [μcellH] <;>
    split <;>
    first
      | exact mul_nonneg (Nat.cast_nonneg _) (zpow_nonneg hq0 _)
      | exact le_refl 0

theorem part2_row {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} (X : XHDw n S)
    (hb : P1CtblAdd V X) (hc : P1NullRem V X) (hd : P1FixedHeightExact V X)
    {τ : S.Cell} {q₀ : ℚ} (x : S.Hist q₀ τ) (hzc : S.zc x)
    (hq : q₀ ∈ V.Pools) (hact : V.activeState q₀ τ)
    (hmark : ∀ c : DCellAll V τ, c.isLeft → 1 ≤ markWeight V c) :
    markedRow V X x + terminalRow V X x = 1 + surplusRow V X x := by
  -- PART-1: the raw per-cell masses sum to 1.
  have h1 : HasSum (fun ch : Σ c : DCellAll V τ, Σ D : ℕ, Hpt D =>
      μcellH V X x ch.1 ch.2) 1 := part1 X hb hc hd x hzc hq hact
  have hμsum : Summable (fun ch : Σ c : DCellAll V τ, Σ D : ℕ, Hpt D =>
      μcellH V X x ch.1 ch.2) := h1.summable
  have hμnn : ∀ ch : Σ c : DCellAll V τ, Σ D : ℕ, Hpt D,
      0 ≤ μcellH V X x ch.1 ch.2 := fun ch => μcellH_nonneg X x hq ch.1 ch.2
  -- the terminal row is dominated by the raw row (coefficient ∈ {0,1}).
  have hterm_sum : Summable (fun ch : Σ c : DCellAll V τ, Σ D : ℕ, Hpt D =>
      (if ch.1.isRight then (1:ℝ) else 0) * μcellH V X x ch.1 ch.2) := by
    refine Summable.of_nonneg_of_le (fun ch => ?_) (fun ch => ?_) hμsum
    · split_ifs
      · simpa using hμnn ch
      · simp
    · split_ifs
      · simp
      · simpa using hμnn ch
  -- GAP: summability of the marked/surplus row. Holds in the real instance
  -- because `emult ≤ branching degree ≤ n` (bounded); NOT derivable from the
  -- abstract hypotheses here (emult is an arbitrary ℕ-valued field). See notes.
  have hsurp_sum : Summable (fun ch : Σ c : DCellAll V τ, Σ D : ℕ, Hpt D =>
      ((markWeight V ch.1 - 1 : ℕ) : ℝ) * μcellH V X x ch.1 ch.2) := by
    sorry
  -- per-summand identity: marked + terminal = raw + surplus.
  have hpt : ∀ ch : Σ c : DCellAll V τ, Σ D : ℕ, Hpt D,
      (markWeight V ch.1 : ℝ) * μcellH V X x ch.1 ch.2
        + (if ch.1.isRight then (1:ℝ) else 0) * μcellH V X x ch.1 ch.2
      = μcellH V X x ch.1 ch.2
        + ((markWeight V ch.1 - 1 : ℕ) : ℝ) * μcellH V X x ch.1 ch.2 := by
    rintro ⟨cd, ch2⟩
    rcases cd with ⟨d, cc⟩ | ⟨v, d, cc⟩
    · have hml : 1 ≤ markWeight V (Sum.inl ⟨d, cc⟩ : DCellAll V τ) := hmark _ rfl
      simp only [markWeight, Sum.isRight_inl, Bool.false_eq_true, if_false,
        zero_mul, add_zero]
      rw [Nat.cast_sub (by simpa [markWeight] using hml)]
      push_cast
      ring
    · simp only [markWeight, Sum.isRight_inr, if_true, one_mul, Nat.zero_sub,
        Nat.cast_zero, zero_mul, add_zero, zero_add]
  -- marked = raw + surplus − terminal pointwise; assemble via HasSum.
  have hEq : (fun ch : Σ c : DCellAll V τ, Σ D : ℕ, Hpt D =>
        μcellH V X x ch.1 ch.2
          + ((markWeight V ch.1 - 1 : ℕ) : ℝ) * μcellH V X x ch.1 ch.2
          - (if ch.1.isRight then (1:ℝ) else 0) * μcellH V X x ch.1 ch.2)
      = fun ch => (markWeight V ch.1 : ℝ) * μcellH V X x ch.1 ch.2 := by
    funext ch; have := hpt ch; linarith
  have hM : HasSum (fun ch : Σ c : DCellAll V τ, Σ D : ℕ, Hpt D =>
      (markWeight V ch.1 : ℝ) * μcellH V X x ch.1 ch.2)
      (1 + surplusRow V X x - terminalRow V X x) := by
    have hbase := (h1.add hsurp_sum.hasSum).sub hterm_sum.hasSum
    rw [hEq] at hbase
    exact hbase
  have hMrow : markedRow V X x = 1 + surplusRow V X x - terminalRow V X x :=
    hM.tsum_eq
  linarith

/-- the separate lower bound: row sum ≥ 1 − terminal. -/
theorem part2_ge {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} (X : XHDw n S)
    (hb : P1CtblAdd V X) (hc : P1NullRem V X) (hd : P1FixedHeightExact V X)
    {τ : S.Cell} {q₀ : ℚ} (x : S.Hist q₀ τ) (hzc : S.zc x)
    (hq : q₀ ∈ V.Pools) (hact : V.activeState q₀ τ)
    (hmark : ∀ c : DCellAll V τ, c.isLeft → 1 ≤ markWeight V c) :
    1 - terminalRow V X x ≤ markedRow V X x := by
  have hrow := part2_row X hb hc hd x hzc hq hact hmark
  have hsurp_nn : 0 ≤ surplusRow V X x := by
    refine tsum_nonneg (fun ch => ?_)
    exact mul_nonneg (Nat.cast_nonneg _) (μcellH_nonneg X x hq ch.1 ch.2)
  linarith

end LeanUrat.MovesV
