/-
Unit U6  (MovesR base layer)  [Fsub_card; blueprint R6, FINDING-1 REPAIR]
moves_ref: "F_m is THE subfield of order p^m" — the CARD FACT half of the display.
deps: Defs (U1). difficulty: hard (wave-3 fleet).
sketch: `Fsub p m` is the root set of the separable polynomial `X^{p^m} − X` in the
algebraically closed `Kbar p`: `galois_poly_separable` + root counting (splits with
`p^m` distinct roots); membership `x ^ p ^ m = x` is definitional in `Fsub`.
-/
import Mathlib
import LeanUrat.MovesRBase.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace MovesRBase

variable (p : ℕ) [hp : Fact p.Prime]

/-- U6: `|F_m| = p^m` — the order fact making `Fsub p m` THE subfield of order
`p^m` (blueprint D1, finding-1 repair: the card fact is part of the display). -/
theorem Fsub_card (m : ℕ+) : Nat.card ↥(Fsub p m) = p ^ (m : ℕ) := sorry

end MovesRBase
