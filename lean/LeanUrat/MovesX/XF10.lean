/-
Unit XF.10 discZeroNull — UNCONDITIONAL over the context (Ruling 2)
[E-phase: stated, body sorry]
moves_ref: "corollary μ{disc f = 0} = 0".
sketch: discZero ⊆ {D ≤ vdisc ∨ discZero} for every D, so `C.vdisc_le_tail` + XF.8 +
`frac_nonneg` squeeze. deps: XF.8. difficulty: MEDIUM (EASY-MEDIUM band).
hyp_fields: XCtx's `vdisc_le_tail` (definitional cylinder fact, blueprint §4).
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XF8

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem discZeroNull (n p : ℕ) [Fact p.Prime] (h2 : 2 ≤ n) (C : XCtx n p) :
    C.frac (discZero n p) = 0 := by
  sorry

end LeanUrat.MovesX
