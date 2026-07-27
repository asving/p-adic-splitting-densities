/-
Unit Sp.encodeCard — moves_ref: "Hence the displayed bound."
[|𝒮_n^raw| ≤ (n+2)^{n² + 3n + 12}]
sketch: `Nat.card_fun`/`Fintype.card_fun`, card of Fin. difficulty: easy.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem code_card (n : ℕ) : Nat.card (Code n) = (n+2)^(n^2 + 3*n + 12) := by
  change Nat.card (Fin (n ^ 2 + 3 * n + 12) → Fin (n + 2)) = _
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

end LeanUrat.MovesSp
