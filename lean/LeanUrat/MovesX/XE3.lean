/-
Unit XE.3 envelopeSqrt — the √N fallback  [E-phase: stated, body sorry]
moves_ref: "Given (X2-HYP) + (X2-AFF) + (X2-CAP) + (X2-BRIDGE) PLUS the same two leg
tags …: env(N) ≤ c₃′(n)·p^{−c₄′(n)·√N} — subexponential, enough for X.3's qualitative
form, NOT for SQUEEZE's constants". Same signature as XE.2 MINUS `PR` (X2ProgressP);
XD.4 in place of PR. The rev-4 leg-tag line: BR's witness b carries IsLeafB ∧ NsFreeB,
hence FourthPieceB by the first disjunct — exactly XD.4's hypothesis.
deps: XD.4; otherwise as XE.2. difficulty: HARD.
hyp_fields: (X2-HYP)'s inputs + both leg tags.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XC3
import LeanUrat.MovesX.XD4
import LeanUrat.MovesX.XE1a
import LeanUrat.MovesX.XE1b
import LeanUrat.MovesX.XE1c
import LeanUrat.MovesX.XE1d
import LeanUrat.MovesX.XE1e
import LeanUrat.MovesX.XE1f
import LeanUrat.MovesX.XE1g
import LeanUrat.MovesX.XE1h
import LeanUrat.MovesX.XF7
import LeanUrat.MovesX.XG2b
import LeanUrat.MovesX.XG2c
import LeanUrat.MovesX.XG2d

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem envelopeSqrt (n : ℕ) (hn : 2 ≤ n) (X : XFamily n) (K : XConsts n)
    (BR : X2BridgeP n X) (AF : X2AffP n X K) (CP : X2CapP n X K)
    (AL : X1aAlignP n X ⟨true, false⟩) (WC : WeightChargeFullP n X K)
    (TL : X2TailsP n X K) (NS : NsNullP n X) (R : X3aRouteP n X K) :
    ∃ c3' c4' : ℝ, 0 < c3' ∧ 0 < c4' ∧ ∀ (p : ℕ) [Fact p.Prime] (N : ℕ),
      ((X.ctx p).frac ((X.ctx p).Undec N) : ℝ) ≤ c3' * (p : ℝ) ^ (-(c4' * Real.sqrt N)) := by
  sorry

end LeanUrat.MovesX
