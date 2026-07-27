/-
Unit XD.4 x2hypAssembled  [E-phase: stated, body sorry]
moves_ref: "(X2-HYP) … DERIVED given (X2-AFF) ∧ (X2-CAP) … both prices in the ONE
currency Σ h_r, combined constant c₀⁺ := c₀ + c_cap".
deps: XD.1–XD.3. difficulty: MEDIUM. hyp_fields: X2AffP, X2CapP by name.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XD1
import LeanUrat.MovesX.XD2
import LeanUrat.MovesX.XD3

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem x2hypAssembled {n : ℕ} (X : XFamily n) (K : XConsts n)
    (AF : X2AffP n X K) (CP : X2CapP n X K)
    (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (b : (X.ctx p).Branch f)
    (hb : FourthPieceB (X.ctx p) b) (N : ℕ)
    (hN : N < (X.ctx p).threshold b + capHB (X.ctx p) b) :
    (N : ℚ) - 1 - K.ccap < (K.c0 + K.ccap) * ((dTotal ((X.ctx p).hist b) : ℚ) + 1) ^ 2 ∨
    (N : ℚ) - 1 - K.ccap < (K.c0 + K.ccap) * (maxH ((X.ctx p).hist b) : ℚ) ^ 2 := by
  sorry

end LeanUrat.MovesX
