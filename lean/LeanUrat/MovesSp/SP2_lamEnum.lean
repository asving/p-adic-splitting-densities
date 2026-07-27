/-
Unit Sp.lamEnumComplete — moves_ref: "(residual shape) the degree–multiplicity
partition λ … with Σᵢ g⁽ⁱ⁾·μ⁽ⁱ⁾ = ℓ" + (B5)'s part caps.
sketch: enumeration by strong recursion on weight over a canonical (sorted)
representative; completeness by induction on the multiset. THE fiddly enum unit —
recommend List-of-sorted-lists internally, Multiset at the boundary.
difficulty: medium-hard.
-/
import LeanUrat.MovesSp.DefsEnum

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem lamEnum_complete {bound weight : ℕ} {lam : Multiset (ℕ × ℕ)}
    (hpos : ∀ gm ∈ lam, 1 ≤ gm.1 ∧ 1 ≤ gm.2)
    (hbd : ∀ gm ∈ lam, gm.1 ≤ bound ∧ gm.2 ≤ bound) :
    ((lam.map fun gm => gm.1 * gm.2).sum = weight ↔ lam ∈ lamEnum bound weight) := sorry

end LeanUrat.MovesSp
