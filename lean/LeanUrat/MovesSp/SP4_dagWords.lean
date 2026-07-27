/-
Unit Sp.dagWords — moves_ref: "with SP-FIN, the set of collapsed words over
𝒮_n^raw is FINITE, of size ≤ (|𝒮_n^raw| + 1)^{6n²}."
deps: Sp.dagWalk, Sp.finThm. sketch: inject length-≤L lists into
`Fin L → Option (SnRaw-subtype)` (pad with none); card arithmetic.
difficulty: medium.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem SP_DAG_words (n : ℕ) (hn : 1 ≤ n) : {l | CollapsedWalk n l}.Finite
    ∧ Nat.card {l | CollapsedWalk n l} ≤ (Nat.card (SnRaw n) + 1)^(6 * n^2) := sorry

end LeanUrat.MovesSp
