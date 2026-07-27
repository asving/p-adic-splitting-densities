/-
Unit D9.L9_A  (MovesD campaign, E-phase)
moves_ref: "∏ vol(E_fresh(νᵢ)) = p^{−A(P̂)} … the product depends on P̂ alone; A(P̂) := the
resulting shape exponent" (L9).
deps: D0b, D8, D4b, F1 (reprOf ∈ PrefSet gives Matches/coherence); MovesC `mstar_eq`.
sketch: mstar_eq per read → band count → grid filter → A's summand.
difficulty: medium.  hypothesis_fields: `S.jet` only.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n N m : ℕ}
  {pol : CanonPolicy p F} {P : Shape n}

/-- L9: the presented total pin count at Z = ⊤ is the shape exponent A(P̂, n, N). -/
theorem L9_A (S : Presented p F n N m pol P) (i : PrefIdx n pol P) :
    totalPins (S.jet i) (topLocus p m) = (P : ShapePrefix).A n N := by
  sorry

end LeanUrat.MovesD
