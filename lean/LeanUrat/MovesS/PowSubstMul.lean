/-
Unit U-12c `powSubst_mul` (easy) — nested substitution composes multiplicatively
(DELTA-ABS's symbolic face, R17/R48).  sketch: ring homs agree on X and constants.
-/
import LeanUrat.MovesS.PowSubst

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem powSubst_mul (δ₁ δ₂ : ℕ+) :
    (powSubst δ₁).comp (powSubst δ₂) = powSubst (δ₁ * δ₂) :=
  sorry

end LeanUrat.MovesS
