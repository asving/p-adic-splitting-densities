/-
Unit XF.5 pigeonMax  [PROVED, fleet 2026-07-28]
moves_ref: "some θᵢ has v_p(f(θᵢ)) ≥ (D − n·v_p(n))/(n−1)".
FLAG (blueprint): no sign hypothesis (terms may be negative).
deps: none (Defs only, for the namespace). difficulty: EASY.
AS-BUILT (2026-07-30 verify-2 fold-in): DEAD BLUEPRINT UNIT — pigeonMax has ZERO
consumers corpus-wide (grep over all of LeanUrat/). XF.6 imports this file but
discharges its pigeonhole with its own private `xf6_argmin` (multiplicative, over ℝ);
pigeonMax is additive over ℚ and is never called, so this unit's moves_ref duty is
actually rendered in-file by XF.6, and the MANIFEST's XF.6 deps entry "XF.5" is
import-only. Kept as a record (like the disclosed MovesSp orphans); deletion or
re-pointing is a repo-prep candidate.
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
