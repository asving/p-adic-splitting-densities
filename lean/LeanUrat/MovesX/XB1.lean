/-
Unit XB.1 dCertZero  [PROVED, fleet 2026-07-28]
moves_ref: "At today's discharge state … d_cert ≡ 0".
deps: Defs. difficulty: EASY.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem dCertZero {n : ℕ} (H : XHistory n) :
    dCert ⟨false, false⟩ H = 0 ∧ ∀ st, dCert st H ≤ dTotal H := by
  refine ⟨?_, ?_⟩
  · -- At the zero-discharge state (inc = recn = false) no continuing node is certified:
    -- every branch of `certified`'s match collapses to `false`, so the filter is empty.
    have hcert : ∀ ν : XNode n, certified (⟨false, false⟩ : AlignState) ν = false := by
      intro ν
      simp only [certified]
      cases rowOf ν <;> simp
    simp only [dCert, List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro ν _
    simp [hcert ν]
  · -- `certified st ν = ν.continuing && (…)`, so it entails `ν.continuing`; hence the
    -- certified-filtered list is a sublist of the continuing-filtered list.
    intro st
    simp only [dCert, dTotal]
    exact (List.monotone_filter_right H
      (fun ν h => (Bool.and_eq_true_iff.mp (by simpa only [certified] using h)).1)).length_le

end LeanUrat.MovesX
