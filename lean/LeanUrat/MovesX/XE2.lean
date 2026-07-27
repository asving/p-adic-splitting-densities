/-
Unit XE.2 envelopeExp — the note's exponential envelope, as the DERIVED ∃-theorem
(finding 7)  [E-phase: stated, body sorry]
moves_ref: "Given (X2-BRIDGE) + (X2-CAP) + (X2-AFF) … Given (X.2) with linear d*, h*
AND both legs …: env(N) ≤ c₃(n)·p^{−c₄(n)·N}, with c₃, c₄ traced to s(n), c₀, C_T, c_T,
c_cap".
sketch: BR splits Undec(N) into the three null-tagged pieces (discZero via
XF.7/vdisc_le_tail; ns via NS; InfTree via XG.2d ⊆ discZero) + the witness-branch
piece. WITNESS FEED (rev 4, traced): BR's witness b carries `IsLeafB b ∧ NsFreeB b`,
hence `FourthPieceB b` by the FIRST disjunct of FourthPieceB — exactly PR's (and
XD.4's, in XE.3) hypothesis; PR on b gives deep-or-tall at d* = cd·N − cd',
h* = ch·N − ch'; DEEP LEG: DeepEvent d* ⊆ {vdisc ≥ (2(d*−log)/(2s+1))} pointwise
(XC.3 + gmnLink) → vdisc_le_tail + XF.7 give the (3b) bound with the note's displayed
exponent; TALL LEG: TL. Constants assembled n-only (c₄ from cd, s, n − 1; the
p^{n·v_p(n)/(n−1)} ≤ n^{n/(n−1)} absorption into c₃ — p-free).
deps: XC.3, XE.1*, XF.7, XG.2b–d. difficulty: HARD.
hyp_fields: the FULL tag set, verbatim the note's "CONSUMERS … inherit ALL tags above".
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XC3
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

theorem envelopeExp (n : ℕ) (hn : 2 ≤ n) (X : XFamily n) (K : XConsts n)
    (PR : X2ProgressP n X K) (BR : X2BridgeP n X) (AF : X2AffP n X K) (CP : X2CapP n X K)
    (AL : X1aAlignP n X ⟨true, false⟩) (WC : WeightChargeFullP n X K)
    (TL : X2TailsP n X K) (NS : NsNullP n X) (R : X3aRouteP n X K) :
    ∃ c3 c4 : ℝ, 0 < c3 ∧ 0 < c4 ∧ ∀ (p : ℕ) [Fact p.Prime] (N : ℕ),
      ((X.ctx p).frac ((X.ctx p).Undec N) : ℝ) ≤ c3 * (p : ℝ) ^ (-(c4 * N)) := by
  sorry

end LeanUrat.MovesX
