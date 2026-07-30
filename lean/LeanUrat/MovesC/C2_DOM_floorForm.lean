/-
Unit C2.DOM_floorForm  (moves_ref: §C.1 DOM floor form: on the factor interior the floor F_i IS the current line)
floorOf = sup' over m ≤ i; by C2.DOM every line_m(b) ≤ line_i(b), attained at m = i.
-/
import LeanUrat.MovesC.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

open Polynomial LeanUrat.Moves

namespace LeanUrat.MovesC

theorem C2_DOM_floorForm {lines : ℕ → Line} {i interiorEnd : ℕ} (dom : DomData lines i interiorEnd) (b : ℕ) (hb : b ≤ interiorEnd) : floorOf lines i b = (lines i).at b := by
  -- interior domination: on `[0, interiorEnd]`, every earlier line lies below `lines i`.
  have dom_le : ∀ m, m ≤ i → (lines m).at b ≤ (lines i).at b := by
    intro m hm
    rcases eq_or_lt_of_le hm with rfl | hlt
    · exact le_rfl
    · have hsteep : (lines m).slope < (lines i).slope := dom.steeper m hlt
      have hvert : (lines m).at interiorEnd ≤ (lines i).at interiorEnd :=
        dom.vertex_entry m (le_of_lt hlt)
      simp only [Line.at] at hvert ⊢
      have hbq : (b : ℚ) ≤ (interiorEnd : ℚ) := Nat.cast_le.mpr hb
      nlinarith [mul_nonneg (le_of_lt (sub_pos.mpr hsteep)) (sub_nonneg.mpr hbq)]
  unfold floorOf
  apply le_antisymm
  · -- sup' ≤ (lines i).at b : every term of the family is dominated.
    exact Finset.sup'_le _ _ fun m hm =>
      dom_le m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))
  · -- (lines i).at b ≤ sup' : the value is attained at m = i.
    exact Finset.le_sup' (fun m => (lines m).at b) (Finset.self_mem_range_succ i)

end LeanUrat.MovesC
