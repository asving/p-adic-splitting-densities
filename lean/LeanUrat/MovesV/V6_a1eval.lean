/-  MovesV unit V6-1b `rootTable_evals` — the PREDICTED EVALUATIONS at the
    nine census q + the Σ = q³ row + the m_H3 = 0 falsifier. -/
import LeanUrat.MovesV.V6_a1poly

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open Polynomial

/-- the m_H3 zero at q = 2 (a genuine falsifier). -/
theorem mH3_zero_at_two : TH3.eval 2 = 0 := by
  simp [TH3]

theorem mH3_row : TH3.eval 2 = 0 ∧ TH3.eval 3 = 1 ∧ TH3.eval 4 = 4 ∧
    TH3.eval 5 = 10 ∧ TH3.eval 7 = 35 ∧ TH3.eval 8 = 56 ∧ TH3.eval 9 = 84 ∧
    TH3.eval 11 = 165 ∧ TH3.eval 13 = 286 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [TH3]

theorem mH12_row : TH12.eval 2 = 2 ∧ TH12.eval 3 = 9 ∧ TH12.eval 13 = 1014 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [TH12]

theorem mH3c_row : TH3c.eval 2 = 2 ∧ TH3c.eval 3 = 8 ∧ TH3c.eval 13 = 728 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [TH3c]

theorem m21_m3_rows : T21.eval 2 = 2 ∧ T21.eval 13 = 156 ∧ T3.eval 2 = 2 ∧
    T3.eval 13 = 13 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [T21, T3]

/-- the Σ = q³ row, at EVERY q (via the polynomial identity). -/
theorem sum_row (q : ℚ) : (TH3 + TH12 + TH3c + T21 + T3).eval q = q ^ 3 := by
  rw [rootTable_identities]
  simp

end LeanUrat.MovesV
