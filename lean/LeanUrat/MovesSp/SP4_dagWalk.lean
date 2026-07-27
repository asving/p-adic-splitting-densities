/-
Unit Sp.dagWalk — moves_ref: "(iii) Hence the menu graph with self-loops
collapsed is a DAG; every collapsed walk visits pairwise-distinct ranks, so it
has at most … 6n² letters".
deps: Sp.rankStrict, Sp.rankRadix. sketch: map rankNat: Chain' (· < ·) list of
ℕ < 6n²; strictly-increasing-below-B has length ≤ B. difficulty: medium.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem SP_DAG_walk {n} (hn : 1 ≤ n) {l : List Species}
    (h : CollapsedWalk n l) : l.length ≤ 6 * n^2 := sorry

end LeanUrat.MovesSp
