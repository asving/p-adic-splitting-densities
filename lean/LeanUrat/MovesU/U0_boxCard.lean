/-
Unit U0.boxCard  (MovesU campaign)  [support, tag-free]
moves_ref: "the monic degree-n coefficient box mod p^N (p^{nN} residue classes)"
deps: Defs.
sketch: `Nat.card (Fin n → ZMod (p^N)) = (p^N)^n = p^(n*N)`; `Nat.card_fun`/
        `Nat.card_eq_fintype_card`, `ZMod.card` (needs `NeZero (p^N)` from
        `NeZero p`), `pow_mul` (commuted).
hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesU.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-- (BOX-N)'s denominator: the level-N box has exactly p^{nN} classes. -/
theorem boxCard (p n N : ℕ) [NeZero p] : Nat.card (Box p n N) = p ^ (n * N) :=
  sorry

end LeanUrat.MovesU
