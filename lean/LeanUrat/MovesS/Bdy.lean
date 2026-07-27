/-
Unit U-7a `bdy_edge` (easy) — the (BDY) edge rule.
moves_ref: "the ENTERING READ of a block entrance belongs to the ENTRANCE SIDE".
-/
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem bdy_edge : ∀ fe r : ℕ,
    (bdyEdgeOwner fe r = .entrance ↔ r ≤ fe) ∧
    (bdyEdgeOwner fe r = .block ↔ fe < r) :=
  sorry

end LeanUrat.MovesS
