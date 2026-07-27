/-
Unit L9s.A_stable  (MovesD campaign, E-phase)  [AUX]
informal: A(P̂, n, N) is N-stable above the shape height bound (the note's "a priori shape
bound … available but not needed" — HERE it IS needed, to make A′ N-free).
deps: Defs.
sketch: band coordinates satisfy ℓ ≤ htS ≤ line value ≤ intercept < Nshape, so levels in
[Nshape, N) contribute nothing; filter congruence on the grid split.
difficulty: medium.  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {n N : ℕ}

/-- A-stability above the shape height bound: A(n, N) = A′(n) whenever Nshape ≤ N. -/
theorem A_stable {P : Shape n} (hN : (P : ShapePrefix).Nshape ≤ N) :
    (P : ShapePrefix).A n N = (P : ShapePrefix).A' n := by
  sorry

end LeanUrat.MovesD
