/-
Unit U-7b `bdy_node_shadow` (easy) — the (BDY) node rule.
moves_ref: "the first entrance node ν is BLOCK-side as a STATE INDEX …, while the
edge INTO ν is entrance-side MASS".
-/
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem bdy_node_shadow : ∀ fe : ℕ,
    bdyNodeOwner fe fe = .block ∧
    bdyEdgeOwner fe fe = .entrance ∧
    ∀ r ≠ fe, bdyNodeOwner fe r = bdyEdgeOwner fe r :=
  sorry

end LeanUrat.MovesS
