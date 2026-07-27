/-
Unit XB.2 dCertMono  [E-phase: stated, body sorry]
moves_ref: "given (ALIGN-inc): d_cert = #T1-increments + #T2; given both: also the T1
recenterings". deps: Defs. difficulty: MEDIUM.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem dCertMono {n : ℕ} (H : XHistory n) :
    dCert ⟨true, false⟩ H = countPop H .incT12 ∧
    dCert ⟨true, true⟩ H = countPop H .incT12 + countPop H .recT1 := by
  sorry

end LeanUrat.MovesX
