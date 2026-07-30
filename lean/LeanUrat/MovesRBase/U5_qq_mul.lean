/-
Unit U5  (MovesR base layer)  [qq_mul HALF ONLY]
moves_ref: "q_{δ_j} = p^{δ_j} = q_δ^{δ_j^rel}".
deps: Defs (U1). difficulty: easy.
sketch: `p ^ ((m * δ' : ℕ+) : ℕ) = p ^ ((m : ℕ) * δ') = (p ^ (m : ℕ)) ^ (δ' : ℕ)`
(`PNat.mul_coe` + `pow_mul`).
DEVIATION (recorded in MANIFEST): the unit's second half `βarg_eq` (the (e2)
identity `S.βarg p = qq p S.δ ^ (S.δrel : ℕ)`) is EXCLUDED from this split-off —
it is parameterized over `Setting`, which the base-layer charge excludes; it stays
with the parked MovesR corpus.
-/
import Mathlib
import LeanUrat.MovesRBase.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace MovesRBase

variable (p : ℕ) [hp : Fact p.Prime]

/-- U5: `q_{mδ′} = q_m^{δ′}` — the β-argument bookkeeping under composition. -/
theorem qq_mul (m δ' : ℕ+) : qq p (m * δ') = qq p m ^ (δ' : ℕ) := by
  rw [qq, qq, PNat.mul_coe, pow_mul]

end MovesRBase
