/-
Unit XG.2d treeFinite — X.3(a) pointwise, DERIVED (replaces the deleted
`stratumLink`/`infBranch` fields)  [E-phase: stated, body sorry]
moves_ref: "Off {disc f = 0} …, EITHER route gives every branch finite pointwise, by
the four-population decomposition … Hence a.e. f has a FINITE tree".
sketch: an infinite path g (¬Finite via XG.2's contrapositive) gives hist (g k) of
length k (parent_hist induction), each a stratum of f (`X.gmnLink`) with HistWF (`wf`);
dTotal ≥ k − 1 (termLast) contradicts XG.1's bound at large k.
deps: XG.1, XG.2. difficulty: HARD (MEDIUM-HARD band).
hyp_fields: X3aRouteP; gmnLink/wf (context inputs).
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XG1
import LeanUrat.MovesX.XG2

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem treeFinite {n : ℕ} (X : XFamily n) (K : XConsts n) (R : X3aRouteP n X K)
    (p : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (f : MonicBox n p) (hd : f ∉ discZero n p) :
    Finite ((X.ctx p).Branch f) := by
  sorry

end LeanUrat.MovesX
