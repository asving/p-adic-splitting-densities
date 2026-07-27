/-
Unit XC.1 x1aChain  [E-phase: stated, body sorry]
moves_ref: "(X.1a) stratum(H) ⊆ Desc_{d_cert(H)} ⊆ { v_p(disc f) ≥ 2·d_cert(H) }";
first inclusion definitional, second via transport + (P2).
deps: Defs. difficulty: MEDIUM (EASY-MEDIUM band).
hyp_fields: X1aAlignP (kernel), GMNIndex.p2 (published).
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem x1aChain {n : ℕ} (X : XFamily n) (st : AlignState) (AL : X1aAlignP n X st)
    (p : ℕ) [Fact p.Prime] :
    (∀ (f : MonicBox n p) H, (X.gmn p).inStratum f H → f ∈ DescX X p st (dCert st H)) ∧
    (∀ (f : MonicBox n p) d, f ∈ DescX X p st d → f ∉ discZero n p → 2 * d ≤ vdisc f) := by
  refine ⟨?_, ?_⟩
  · -- First inclusion: stratum(H) ⊆ Desc_{d_cert(H)}, definitional (witness H itself).
    intro f H hf
    exact ⟨H, hf, le_refl _⟩
  · -- Second inclusion: Desc_d ⊆ { 2·d ≤ v_p(disc f) }, via (X1a-ALIGN) transport + (P2).
    intro f d hf hdisc
    obtain ⟨H, hStrat, hd⟩ := hf
    have h1 : dCert st H ≤ (X.gmn p).ind f := AL p f H hdisc hStrat
    have h2 : 2 * (X.gmn p).ind f ≤ vdisc f := (X.gmn p).p2 f hdisc
    omega

end LeanUrat.MovesX
