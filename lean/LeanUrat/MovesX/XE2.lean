/-
Unit XE.2 envelopeExp — the note's exponential envelope, as the DERIVED ∃-theorem
(finding 7)  [RESTATED-POST-REFUTATION 2026-07-27: the previous ∀N conclusion was
kernel-certified FALSE (notes/XE2_refutation_witness.lean + _transcription_check.lean;
adjudication in blueprint §7). The conclusion now binds ∃ N₀ (an (n,K)-function, bound
BEFORE p) with the claim over N ≥ N₀ only — the note's honest domain of content (the
(N−1−c_cap) numerator; X.5(iii) no-teeth regime). The refutation countermodel (point
mass at X²+X, root-only tree, Undec N = ∅ for N ≥ 2) now SATISFIES the statement via
N₀ ≥ 2. Body sorry; fleet re-proves. D9 REBIND (audit, accepted findings 2/4): N₀, c3, c4 are
now bound BEFORE ∀ X — quantified over exactly (n, K); the tags move inside as
implications, so the constants cannot depend on any XFamily data. Disclosed: R is
redundant given AL ∧ WC (route a2) — kept, per the tag list.]
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

theorem envelopeExp (n : ℕ) (hn : 2 ≤ n) (K : XConsts n) :
    ∃ N₀ : ℕ, ∃ c3 c4 : ℝ, 0 < c3 ∧ 0 < c4 ∧
      ∀ (X : XFamily n), X2ProgressP n X K → X2BridgeP n X → X2AffP n X K → X2CapP n X K →
        X1aAlignP n X ⟨true, false⟩ → WeightChargeFullP n X K →
        X2TailsP n X K → NsNullP n X → X3aRouteP n X K →
        ∀ (p : ℕ) [Fact p.Prime], ∀ N, N₀ ≤ N →
          ((X.ctx p).frac ((X.ctx p).Undec N) : ℝ) ≤ c3 * (p : ℝ) ^ (-(c4 * N)) := by
  sorry

end LeanUrat.MovesX
