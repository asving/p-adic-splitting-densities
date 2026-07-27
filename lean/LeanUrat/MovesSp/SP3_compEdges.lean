/-
Unit Sp.compEdges — moves_ref: "each consecutive read pair is linked by an edge
of the syntactic menu Out (SP.4)" + step (5): "which is precisely SP.4's edge
relation; so each realized transition is an Out edge."
deps: Sp.compMember. sketch: Succ-membership = InCatalogue (compMember at r + 1)
∧ SuccStep (assembled as in compMember); then `Or.inl` into Out. GENUINE step:
the conclusion's Out is defined through InCatalogue, which no field supplies.
difficulty: easy. hypothesis_fields: the standing group-F list (see
SP3_compMember.lean).
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem SP_COMP_edges (n p : ℕ) [Fact p.Prime] (f : Polynomial ℤ_[p])
    (hf : f.Monic) (hdeg : f.natDegree = n) (M : CanTreeModel n p f)
    (η : M.Branch) (r : ℕ) (hr : (r + 1 : ℕ∞) < M.len η) :
    Sum.inl (M.datum η (r + 1)) ∈ Out n (M.datum η r) := sorry

end LeanUrat.MovesSp
