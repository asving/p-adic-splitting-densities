/-
Unit XG.1 branchLenBound  [E-phase: stated, body sorry]
moves_ref: X.3(a)'s four-population bound, both routes (auditor-confirmed arithmetic);
cleared display over the family. deps: XC.3, XC.4. difficulty: EASY (glue).
hyp_fields: X3aRouteP + HistWF.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XC3
import LeanUrat.MovesX.XC4

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem branchLenBound {n : ℕ} (X : XFamily n) (K : XConsts n) (R : X3aRouteP n X K)
    (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n)
    (hf : (X.gmn p).inStratum f H) (hd : f ∉ discZero n p) (W : HistWF n H) (hn : 1 ≤ n) :
    2 * dTotal H ≤ (2 * K.s + 1) * vdisc f + 2 * Nat.log 2 n := by
  sorry

end LeanUrat.MovesX
