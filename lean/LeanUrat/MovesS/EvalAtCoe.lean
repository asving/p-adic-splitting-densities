/-
Unit U-19 `evalAt` (medium) — the OKat/evalAt pair lives in Defs.lean (the E-phase
fill of the §2.C skeleton); this unit carries the coe law `evalAt_coe`.
-/
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem evalAt_coe (q₀ : ℚ) (f : OKat q₀) :
    evalAt q₀ f = RatFunc.eval (RingHom.id ℚ) q₀ (f : Qq) :=
  sorry

end LeanUrat.MovesS
