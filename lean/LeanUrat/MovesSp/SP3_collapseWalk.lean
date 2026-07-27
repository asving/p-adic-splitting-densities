/-
Unit Sp.collapseWalk — moves_ref: "a loop-collapsed entrance word is a collapsed
walk in the menu graph".
deps: Sp.collapseSublist. sketch: membership via Sublist; the boundary-edge
preservation induction: consecutive-dedup keeps exactly the SuccStep edges with
s ≠ s′ (a run boundary is a non-loop edge); two-head case split.
difficulty: medium.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem collapseRuns_collapsedWalk {n : ℕ} {l : List Species}
    (hmem : ∀ s ∈ l, InCatalogue n s) (hch : l.Chain' (SuccStep n)) :
    CollapsedWalk n (collapseRuns l) := sorry

end LeanUrat.MovesSp
