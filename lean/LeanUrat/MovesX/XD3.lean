/-
Unit XD.3 x2hypDichotomy  [E-phase: stated, body sorry]
moves_ref: the √ dichotomy, squared form.
deps: none (Defs only, for the namespace). difficulty: EASY.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem x2hypDichotomy (M : ℚ) (d m : ℕ) (h : M < (d + 1) * m) :
    M < ((d : ℚ) + 1) ^ 2 ∨ M < (m : ℚ) ^ 2 := by
  have hd : (0 : ℚ) ≤ (d : ℚ) + 1 := by positivity
  have hm : (0 : ℚ) ≤ (m : ℚ) := Nat.cast_nonneg m
  rcases le_total ((d : ℚ) + 1) (m : ℚ) with hle | hle
  · right
    nlinarith [h, hle, hd, hm]
  · left
    nlinarith [h, hle, hd, hm]

end LeanUrat.MovesX
