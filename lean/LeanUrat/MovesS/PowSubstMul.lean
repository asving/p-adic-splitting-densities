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
    (powSubst δ₁).comp (powSubst δ₂) = powSubst (δ₁ * δ₂) := by
  -- Two ring homs out of the fraction field ℚ(q) agree iff they agree after
  -- precomposition with `algebraMap (Polynomial ℚ) Qq`; then reduce to X and C.
  apply IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial ℚ))
  apply Polynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, RatFunc.algebraMap_C, powSubst_C]
  · simp only [RingHom.comp_apply, powSubst_X, map_pow, ← pow_mul]
    congr 1

end LeanUrat.MovesS
