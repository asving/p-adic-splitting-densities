/-
Unit `n2_pools` (easy; S5 construction batch) — Pools := all prime powers;
pools_prime_pow/closed/infinite are n2M's structure fields; the pin is the
equality with the full prime-power locus.
-/
import LeanUrat.MovesS.N2Carriers

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_pools :
    n2M.Pools = {q : ℚ | ∃ (p : ℕ) (_ : p.Prime) (δ : ℕ+), q = (p : ℚ) ^ (δ : ℕ)} :=
  sorry

end LeanUrat.MovesS
