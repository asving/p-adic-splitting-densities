/-  MovesV unit V1-2 `xhdu_rect_sum` — ROSTER (2): (a) the (u-T) rectangle sum;
    (b) the "else false in general" witness. -/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem xhdu_rect_sum {ι : Type*} (Hfin : Finset ι) (cnt : ι → ℕ) (g : ι → ℝ)
    (T : ℕ) (hT : ∀ h ∈ Hfin, cnt h = T) :
    ∑ h ∈ Hfin, (cnt h : ℝ) * g h = (T : ℝ) * ∑ h ∈ Hfin, g h := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun h hh => by rw [hT h hh])

theorem xhdu_rect_false : ∃ (cnt : Fin 2 → ℕ) (g : Fin 2 → ℝ),
    (∑ h, (cnt h : ℝ) * g h) ≠ (cnt 0 : ℝ) * ∑ h, g h := by
  refine ⟨![1, 2], ![1, 1], ?_⟩
  simp [Fin.sum_univ_two]

end LeanUrat.MovesV
