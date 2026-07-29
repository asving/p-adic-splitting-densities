/-  MovesV unit V6-2b `a2_weight_table` (RE-KEYED C3) — the A2 weight,
    natural-coefficient form + the note's display re-derived THROUGH the
    chart, division-free. -/
import LeanUrat.MovesV.DefsGate

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open Polynomial

/-- (a) the chart-native weight value + the sealed census point. -/
theorem EA2_eval (t u : ℕ) : EA2.eval ![t, u] = 6 * t + 3 * u + 1 := by
  simp [AffineE.eval, EA2, Fin.sum_univ_two]
  ring

theorem A2_sealed_point : A2chart ![1, 0] = ![4, 1] ∧ EA2.eval ![1, 0] = 7 := by
  constructor
  · funext i
    fin_cases i <;> rfl
  · decide

/-- (b) THE DISPLAY IDENTITY, division-free: 2E = 3(h₀+h₂) − 1 through the
chart (the note's E = (3(h₀+h₂)−1)/2, re-derived as an ℕ-identity). -/
theorem A2_display_identity (h : Hpt 2) :
    2 * EA2.eval h = 3 * (A2chart h 0 + A2chart h 1) - 1 := by
  simp [AffineE.eval, EA2, A2chart, Fin.sum_univ_two]
  omega

/-- (c) TA2 = (X−1)² evaluations + the one-letter PART-1 row. -/
theorem TA2_evals : TA2.eval 2 = 1 ∧ TA2.eval 3 = 4 ∧ TA2.eval 13 = 144 := by
  refine ⟨?_, ?_, ?_⟩ <;> (simp [TA2]; try norm_num)

end LeanUrat.MovesV
