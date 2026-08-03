import Mathlib
import LeanUrat.Scaffold.O12.Semantic
import LeanUrat.OM.HullStability

set_option linter.style.longLine false

namespace LeanUrat.Scaffold

open LeanUrat.OM.NewtonPolygon

variable {e : ℕ}

namespace L6eHull

/-- The (positive-oriented) drop fraction of a chord pair `(A, B)`:
`(A.2 − B.2)/(B.1 − A.1)` — the magnitude of the descending slope. -/
def dropQ (pr : (ℕ × ℕ) × (ℕ × ℕ)) : ℚ :=
  ((pr.1.2 : ℚ) - (pr.2.2 : ℚ)) / ((pr.2.1 : ℚ) - (pr.1.1 : ℚ))

lemma dropQ_eq_neg_pairSlope (pr : (ℕ × ℕ) × (ℕ × ℕ)) :
    dropQ pr = -(pairSlope pr.1 pr.2) := by
  rw [dropQ, pairSlope, ← neg_div, neg_sub]

/-- Face datum of a chord pair: (width, reduced slope denominator). -/
def faceOf (pr : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ+ × ℕ+ :=
  (⟨max 1 (pr.2.1 - pr.1.1), lt_of_lt_of_le one_pos (le_max_left _ _)⟩,
   ⟨(dropQ pr).den, (dropQ pr).pos⟩)

/-- Slope-numerator datum of a chord pair. -/
def numOf (pr : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ+ :=
  ⟨max 1 (dropQ pr).num.toNat, lt_of_lt_of_le one_pos (le_max_left _ _)⟩

lemma numOf_val {pr : (ℕ × ℕ) × (ℕ × ℕ)} (h : 0 < dropQ pr) :
    ((numOf pr : ℕ) : ℤ) = (dropQ pr).num := by
  have hnum : 0 < (dropQ pr).num := Rat.num_pos.mpr h
  show ((max 1 (dropQ pr).num.toNat : ℕ) : ℤ) = (dropQ pr).num
  omega

lemma numOf_div_den {pr : (ℕ × ℕ) × (ℕ × ℕ)} (h : 0 < dropQ pr) :
    ((numOf pr : ℕ) : ℚ) / (((faceOf pr).2 : ℕ) : ℚ) = dropQ pr := by
  have h1 : ((numOf pr : ℕ) : ℚ) = ((dropQ pr).num : ℚ) := by
    exact_mod_cast numOf_val h
  have h2 : (((faceOf pr).2 : ℕ) : ℚ) = ((dropQ pr).den : ℚ) := rfl
  rw [h1, h2, Rat.num_div_den]

/-- A rational strictly between `0` and `1` has denominator `≥ 2`. -/
lemma two_le_den {q : ℚ} (h0 : 0 < q) (h1 : q < 1) : 2 ≤ q.den := by
  by_contra h
  push_neg at h
  have hd1 : q.den = 1 := by have := q.pos; omega
  have hq : q = ((q.num : ℤ) : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den q]
    rw [hd1]
    simp
  rw [hq] at h0 h1
  have h0' : 0 < q.num := by exact_mod_cast h0
  have h1' : q.num < 1 := by exact_mod_cast h1
  omega

/-- Telescoping widths: over the consecutive pairs of a strictly-abscissa-sorted
list, the widths sum to `last − head`. -/
lemma zip_width_sum : ∀ (V : List (ℕ × ℕ)),
    (V.map Prod.fst).Pairwise (· < ·) →
    ∀ A, V.head? = some A → ∀ L, V.getLast? = some L →
    ((V.zip V.tail).map (fun pr => pr.2.1 - pr.1.1)).sum + A.1 = L.1
  | [], _, A, hA, L, hL => by simp at hA
  | [P], _, A, hA, L, hL => by
      simp only [List.head?_cons, Option.some.injEq] at hA
      simp only [List.getLast?_singleton, Option.some.injEq] at hL
      subst hA; subst hL
      simp
  | P :: Q :: T, hs, A, hA, L, hL => by
      simp only [List.head?_cons, Option.some.injEq] at hA
      subst hA
      rw [List.getLast?_cons_cons] at hL
      have hs' : ((Q :: T).map Prod.fst).Pairwise (· < ·) := by
        rw [List.map_cons, List.pairwise_cons] at hs
        exact hs.2
      have hPQ : P.1 < Q.1 := by
        rw [List.map_cons, List.pairwise_cons] at hs
        exact hs.1 Q.1 (by simp)
      have ih := zip_width_sum (Q :: T) hs' Q (by simp) L hL
      rw [show (P :: Q :: T).tail = Q :: T from rfl, List.zip_cons_cons,
        List.map_cons, List.sum_cons]
      simp only [List.tail_cons] at ih ⊢
      omega

end L6eHull

end LeanUrat.Scaffold
