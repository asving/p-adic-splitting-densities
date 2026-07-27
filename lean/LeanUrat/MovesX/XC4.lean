/-
Unit XC.4 x1bReductionT4  [E-phase: PROVED]
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
  -- First conjunct: directly the T4 weight-charge kernel.
  refine ⟨WC p f H hd hf, ?_⟩
  -- Second conjunct: reduce via the (X.1a) chain at st = ⟨true, true⟩ + the population split.
  -- (X.1a): 2·d_cert(H) ≤ v_p(disc f), with d_cert at the both-certified state.
  have hchain := x1aChain X ⟨true, true⟩ AL p
  have hmem : f ∈ DescX X p ⟨true, true⟩ (dCert ⟨true, true⟩ H) := hchain.1 f H hf
  have hv : 2 * dCert ⟨true, true⟩ H ≤ vdisc f :=
    hchain.2 f (dCert ⟨true, true⟩ H) hmem hd
  -- (CD): d_cert at ⟨true,true⟩ = #{T1/T2 increments} + #{T1 recenterings}.
  rw [(dCertMono H).2] at hv
  -- Four-population split of d_total, and the two side charges.
  have hfour := fourPop H
  have ht3 := t3Charge H W hn
  have hWC : countPop H .t4 ≤ K.s * vdisc f := WC p f H hd hf
  -- Expand the target RHS so the only nonlinear term `K.s * vdisc f` is a shared atom.
  have hexpand : (2 * K.s + 1) * vdisc f = 2 * (K.s * vdisc f) + vdisc f := by ring
  rw [hexpand]
  omega

end LeanUrat.MovesX
