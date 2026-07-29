/-  MovesV unit V6-1a `rootTable_identities` — the five root closed forms +
    PART-1 count face AS POLYNOMIALS. -/
import LeanUrat.MovesV.DefsGate

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open Polynomial

theorem rootTable_identities : TH3 + TH12 + TH3c + T21 + T3 = X ^ 3 := by
  apply Polynomial.funext
  intro x
  simp [TH3, TH12, TH3c, T21, T3]
  ring

theorem rootTable_degrees : TH3.natDegree ≤ 3 ∧ TH12.natDegree ≤ 3 ∧
    TH3c.natDegree ≤ 3 ∧ T21.natDegree ≤ 3 ∧ T3.natDegree ≤ 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [TH3, TH12, TH3c, T21, T3] <;>
    compute_degree <;> norm_num

end LeanUrat.MovesV
