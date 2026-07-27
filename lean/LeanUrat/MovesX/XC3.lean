/-
Unit XC.3 x1bReduction  [E-phase: stated, body sorry]
moves_ref: the two-step reduction display, cleared form (auditor-confirmed:
"2I ≤ v, R ≤ sv, T3 ≤ ⌊log₂n⌋ give 2d_total ≤ (2s+1)v + 2⌊log₂n⌋").
deps: XB.2–4, XC.1. difficulty: MEDIUM.
hyp_fields: X1aAlignP(inc) ∧ WeightChargeFullP + HistWF.
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

theorem x1bReduction {n : ℕ} (X : XFamily n) (K : XConsts n)
    (AL : X1aAlignP n X ⟨true, false⟩) (WC : WeightChargeFullP n X K)
    (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n)
    (hf : (X.gmn p).inStratum f H) (hd : f ∉ discZero n p) (W : HistWF n H) (hn : 1 ≤ n) :
    2 * dTotal H ≤ (2 * K.s + 1) * vdisc f + 2 * Nat.log 2 n := by
  sorry

end LeanUrat.MovesX
