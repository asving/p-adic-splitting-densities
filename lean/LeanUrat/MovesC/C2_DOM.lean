/-
Unit C2.DOM — moves_ref: §C.1 Lemma DOM (interior floor domination),
the displayed affine induction (1)+(2).
Affine: line_i(b) − line_m(b) = [line_i − line_m](interiorEnd)
        + (slope_i − slope_m)·(interiorEnd − b) ≥ 0.  Pure ℚ / nlinarith.
-/
import LeanUrat.MovesC.Defs

namespace LeanUrat.MovesC

theorem C2_DOM {lines : ℕ → Line} {i interiorEnd : ℕ} (dom : DomData lines i interiorEnd) (b : ℕ) (hb : b ≤ interiorEnd) (m : ℕ) (hm : m ≤ i) : (lines m).at b ≤ (lines i).at b := by
  rcases lt_or_eq_of_le hm with hlt | heq
  · -- m < i : the steepness chain plus the vertex-entry endpoint feed the affine induction.
    have hs := dom.steeper m hlt
    have hv := dom.vertex_entry m hm
    have hbq : (b : ℚ) ≤ (interiorEnd : ℚ) := by exact_mod_cast hb
    simp only [Line.at] at hv ⊢
    nlinarith [mul_nonneg (le_of_lt (sub_pos.mpr hs)) (sub_nonneg.mpr hbq)]
  · -- m = i : the goal is reflexive.
    subst heq
    exact le_refl _

end LeanUrat.MovesC
