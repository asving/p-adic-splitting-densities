/-
Unit C3.crossing — moves_ref: §C.1(i)(α) THE ENDPOINT/AFFINE-LINE COMPARISON (rev 10).
new−old is affine in b, ≥ 0 at both endpoints ⟹ ≥ 0 on [s0, jstar].
Concretely: [new − old](b) − [new − old](jstar) = (new.slope − old.slope)·(jstar − b) ≥ 0,
so new.at b − old.at b ≥ new.at jstar − old.at jstar ≥ 0.  Pure ℚ / nlinarith.
-/
import LeanUrat.MovesC.Defs

namespace LeanUrat.MovesC

theorem C3_crossing {old new : Line} (hsteep : old.slope < new.slope) (s0 jstar : ℕ) (hend0 : old.at s0 ≤ new.at s0) (hend1 : old.at jstar ≤ new.at jstar) (b : ℕ) (hb0 : s0 ≤ b) (hb1 : b ≤ jstar) : old.at b ≤ new.at b := by
  have hbj : (b : ℚ) ≤ (jstar : ℚ) := by exact_mod_cast hb1
  simp only [Line.at] at hend1 ⊢
  nlinarith [mul_nonneg (le_of_lt (sub_pos.mpr hsteep)) (sub_nonneg.mpr hbj)]

end LeanUrat.MovesC
