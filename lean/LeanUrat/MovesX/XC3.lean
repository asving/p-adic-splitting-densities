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
  -- Populations: I = incT12, R = recT1, T3 = t3, T4 = t4.
  -- fourPop (XB.3): dTotal = I + R + T3 + T4.
  have hpop := fourPop H
  -- XB.4: #T3 ≤ ⌊log₂ n⌋.
  have ht3 := t3Charge H W hn
  -- WeightChargeFullP: R + T4 ≤ s·v.
  have hwc := WC p f H hd hf
  -- XB.2: d_cert⟨inc⟩ = I.
  have hmono := (dCertMono H).1
  -- XC.1 (X.1a chain) at st = ⟨inc⟩: stratum(H) ⊆ Desc_{d_cert} ⊆ {2·d_cert ≤ v}.
  have hchain := x1aChain X ⟨true, false⟩ AL p
  have hdesc := hchain.1 f H hf
  have hsec := hchain.2 f (dCert ⟨true, false⟩ H) hdesc hd
  -- hence 2·I ≤ v.
  have h1 : 2 * countPop H .incT12 ≤ vdisc f := by rw [hmono] at hsec; exact hsec
  -- clear the nonlinear coefficient: (2s+1)·v = 2·(s·v) + v.
  have hexp : (2 * K.s + 1) * vdisc f = 2 * (K.s * vdisc f) + vdisc f := by ring
  -- 2·d_total = 2·I + 2·(R+T4) + 2·T3 ≤ v + 2·(s·v) + 2·log = (2s+1)·v + 2·log.
  omega

end LeanUrat.MovesX
