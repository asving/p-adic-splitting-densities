/-
Unit XB.1 dCertZero  [E-phase: stated, body sorry]
moves_ref: "At today's discharge state … d_cert ≡ 0".
deps: Defs. difficulty: EASY.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem dCertZero {n : ℕ} (H : XHistory n) :
    dCert ⟨false, false⟩ H = 0 ∧ ∀ st, dCert st H ≤ dTotal H := by
  sorry

end LeanUrat.MovesX
