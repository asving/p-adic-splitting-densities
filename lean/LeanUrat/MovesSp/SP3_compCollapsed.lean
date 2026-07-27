/-
Unit Sp.compCollapsed [REV 4, Codex-1 — Branch/len tied to SP-DAG as a
CONCLUSION: real, non-vacuous content over the interface] — moves_ref: "the
collapsed LETTER length of a walk (the number of letters after collapsing
self-loop runs) IS bounded — Lemma SP-DAG (SP.4): … every collapsed walk has
≤ 6n² letters. SCOPE OF THAT BOUND …: it bounds letter ALTERNATIONS only. The
number of READS stays unbounded".
deps: Sp.compMember, Sp.collapseWalk, Sp.dagWalk. sketch: the length-m read
prefix is a member-wise catalogued SuccStep chain; collapseRuns gives a
CollapsedWalk; dagWalk bounds it. NOTE the fence, kept: m (the READ count) is
NOT bounded — only the collapsed image is. difficulty: medium (easy-medium).
hypothesis_fields: the standing group-F list (see SP3_compMember.lean).
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem SP_COMP_collapsed (n p : ℕ) (hn : 1 ≤ n) [Fact p.Prime]
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (M : CanTreeModel n p f) (η : M.Branch) (m : ℕ) (hm : (m : ℕ∞) ≤ M.len η) :
    (collapseRuns ((List.range m).map (M.datum η))).length ≤ 6 * n ^ 2 := sorry

end LeanUrat.MovesSp
