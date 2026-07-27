/-
Unit XC.4 x1bReductionT4  [E-phase: stated, body sorry]
moves_ref: X.3(a1)'s three bounds — same signature as XC.3 at st = ⟨true, true⟩ with
`WeightChargeT4P`. deps: XB.2–4, XC.1. difficulty: MEDIUM.
hyp_fields: X1aAlignP(both) ∧ WeightChargeT4P + HistWF.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XB2
import LeanUrat.MovesX.XB3
import LeanUrat.MovesX.XB4
import LeanUrat.MovesX.XC1

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem x1bReductionT4 {n : ℕ} (X : XFamily n) (K : XConsts n)
    (AL : X1aAlignP n X ⟨true, true⟩) (WC : WeightChargeT4P n X K)
    (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n)
    (hf : (X.gmn p).inStratum f H) (hd : f ∉ discZero n p) (W : HistWF n H) (hn : 1 ≤ n) :
    countPop H .t4 ≤ K.s * vdisc f ∧
    2 * dTotal H ≤ (2 * K.s + 1) * vdisc f + 2 * Nat.log 2 n := by
  sorry

end LeanUrat.MovesX
