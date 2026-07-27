/-
Unit XC.2 x1aTrivial  [E-phase: stated, body sorry]
moves_ref: "at zero discharge d_cert ≡ 0 and (X.1a) is trivially true" — the same
two-inclusion statement as XC.1 at st = ⟨false, false⟩ WITHOUT the `AL` hypothesis
(the honest unconditional instance). deps: XB.1. difficulty: EASY. hyp: none.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XB1

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem x1aTrivial {n : ℕ} (X : XFamily n) (p : ℕ) [Fact p.Prime] :
    (∀ (f : MonicBox n p) H, (X.gmn p).inStratum f H →
      f ∈ DescX X p ⟨false, false⟩ (dCert ⟨false, false⟩ H)) ∧
    (∀ (f : MonicBox n p) d, f ∈ DescX X p ⟨false, false⟩ d → f ∉ discZero n p →
      2 * d ≤ vdisc f) := by
  refine ⟨?_, ?_⟩
  · -- First inclusion: stratum(H) ⊆ Desc_{d_cert(H)}, definitional (witness H, le_refl).
    intro f H hf
    exact ⟨H, hf, le_refl _⟩
  · -- Second inclusion: at ⟨false, false⟩ the certified depth is 0 (XB.1 dCertZero),
    -- so any d with d ≤ d_cert(H) = 0 forces d = 0 and 2·d = 0 ≤ v_p(disc f).
    intro f d hf _
    obtain ⟨H, _, hd⟩ := hf
    rw [(dCertZero H).1] at hd
    omega

end LeanUrat.MovesX
