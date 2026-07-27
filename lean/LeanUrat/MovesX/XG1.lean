/-
Unit XG.1 branchLenBound  [PROVED: glue over the two X.3(a) routes via XC.3/XC.4]
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
  -- X3aRouteP is the two-route disjunction: EITHER ⟨true,true⟩ + WeightChargeT4P
  -- (route via XC.4), OR ⟨true,false⟩ + WeightChargeFullP (route via XC.3).
  -- Each route delivers exactly this bound, so branchLenBound is pure glue.
  rcases R with ⟨AL, WC⟩ | ⟨AL, WC⟩
  · exact (x1bReductionT4 X K AL WC p f H hf hd W hn).2
  · exact x1bReduction X K AL WC p f H hf hd W hn

end LeanUrat.MovesX
