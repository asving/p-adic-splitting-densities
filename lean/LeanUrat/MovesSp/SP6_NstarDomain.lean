/-
Unit Sp.n3NstarDomain — moves_ref: "N*_p(letter) := the least such N … — DEFINED
exactly on the eventually-realized letters" [here: the table's domain is exactly
the six displayed exceptions; the other 45 carry only the censused N*₃ ≤ 5
remark, deliberately not a def].
sketch: decide over 53. difficulty: easy. (Threshold-unit docstring duty: see
SP6_exclusionLists.lean.)
-/
import LeanUrat.MovesSp.DefsN3

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem nstar_domain : (catalogue3.all fun s =>
    (Nstar3six s).isSome == multiSide6.contains s) = true := sorry

end LeanUrat.MovesSp
