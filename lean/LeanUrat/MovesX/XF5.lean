/-
Unit XF.5 pigeonMax  [E-phase: stated, body sorry]
moves_ref: "some θᵢ has v_p(f(θᵢ)) ≥ (D − n·v_p(n))/(n−1)".
FLAG (blueprint): no sign hypothesis (terms may be negative).
deps: none (Defs only, for the namespace). difficulty: EASY.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem pigeonMax (m : Multiset ℚ) (hm : m ≠ 0) (K : ℚ) (h : K ≤ m.sum) :
    ∃ v ∈ m, K ≤ (m.card : ℚ) * v := by
  obtain ⟨w, hw_mem, hw_max⟩ := Multiset.exists_max_image (fun x : ℚ => x) hm
  refine ⟨w, hw_mem, ?_⟩
  have hsum : m.sum ≤ m.card • w := Multiset.sum_le_card_nsmul m w hw_max
  rw [nsmul_eq_mul] at hsum
  linarith

end LeanUrat.MovesX
