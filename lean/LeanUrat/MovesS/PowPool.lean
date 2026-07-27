/-
Unit U-12d `pow_pool` (easy) — the pool face of DELTA-ABS (R48 split).
sketch: `pow_mul`.
-/
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem pow_pool (q₀ : ℚ) (δ₁ δ₂ : ℕ+) :
    (q₀ ^ (δ₁ : ℕ)) ^ (δ₂ : ℕ) = q₀ ^ ((δ₁ * δ₂ : ℕ+) : ℕ) := by
  rw [PNat.mul_coe, pow_mul]

end LeanUrat.MovesS
