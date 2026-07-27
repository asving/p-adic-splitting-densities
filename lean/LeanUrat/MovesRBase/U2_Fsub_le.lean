/-
Unit U2  (MovesR base layer)
moves_ref: "nested base changes then compose LITERALLY as subrings" (subfield half).
deps: Defs (U1). difficulty: medium.
sketch: x ^ p^d = x ∧ d ∣ m ⇒ x ^ p^m = x (iterate the d-th Frobenius m/d times;
`iterateFrobenius_add`/`pow_pow` bookkeeping).
-/
import Mathlib
import LeanUrat.MovesRBase.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace MovesRBase

variable (p : ℕ) [hp : Fact p.Prime]

/-- U2: `F_d ≤ F_m` for `d ∣ m` — the subfield-lattice nesting. -/
theorem Fsub_le {d m : ℕ+} (h : d ∣ m) : Fsub p d ≤ Fsub p m := sorry

end MovesRBase
