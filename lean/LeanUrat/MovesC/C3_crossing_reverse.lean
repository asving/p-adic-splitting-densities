/-
Unit C3.crossing_reverse — moves_ref: §C.1(i)(γ) right of the crossing slot j×.
new−old strictly decreases in b (new is steeper); ≤ 0 at jstar ⟹ ≤ 0 beyond. Pure ℚ/nlinarith.
-/
import LeanUrat.MovesC.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesC

theorem C3_crossing_reverse {old new : Line} (hsteep : old.slope < new.slope) (jstar : ℕ) (hend : new.at jstar ≤ old.at jstar) (b : ℕ) (hb : jstar ≤ b) : new.at b ≤ old.at b := by
  simp only [Line.at] at hend ⊢
  have hbcast : (jstar : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb
  nlinarith [mul_nonneg (le_of_lt (sub_pos.mpr hsteep)) (sub_nonneg.mpr hbcast)]

end LeanUrat.MovesC
