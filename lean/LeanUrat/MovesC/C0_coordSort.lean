/-
Unit C0.coordSort — moves_ref: §C.0 'solve in ≺-order': the ≺-SORTED enumeration of the n×N box.
Explicit level-major, index-descending chart f j := (j / n, n − 1 − j % n); the Fin-order ⟺ ≺
(CoordPrec) equivalence is the divmod lexicographic comparison. Witnesses JetSetup.coordOf.
-/
import LeanUrat.MovesC.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

open Polynomial LeanUrat.Moves

namespace LeanUrat.MovesC

theorem C0_coordSort (n N : ℕ) (hn : 0 < n) : ∃ f : Fin (n * N) → Coord, (∀ j, (f j).1 < N ∧ (f j).2 < n) ∧ ∀ j j' : Fin (n * N), j < j' ↔ CoordPrec (f j) (f j') := by
  -- The divmod lexicographic key: for the chart a ↦ (a/n, n−1−a%n), the ≺ comparison
  -- (level ascending, index descending within a level) is exactly the nat order on a.
  have key : ∀ a b : ℕ, a < b ↔
      (a / n < b / n ∨ (a / n = b / n ∧ n - 1 - b % n < n - 1 - a % n)) := by
    intro a b
    have hma := Nat.div_add_mod a n
    have hmb := Nat.div_add_mod b n
    have hra := Nat.mod_lt a hn
    have hrb := Nat.mod_lt b hn
    constructor
    · intro hab
      have hdle : a / n ≤ b / n := Nat.div_le_div_right (le_of_lt hab)
      rcases lt_or_eq_of_le hdle with hlt | heq
      · exact Or.inl hlt
      · rw [heq] at hma
        exact Or.inr ⟨heq, by omega⟩
    · intro h
      rcases h with hlt | ⟨heq, hsub⟩
      · by_contra hcon
        have hd : b / n ≤ a / n := Nat.div_le_div_right (not_lt.mp hcon)
        omega
      · rw [heq] at hma
        omega
  refine ⟨fun j => (j.val / n, n - 1 - j.val % n), ?_, ?_⟩
  · intro j
    constructor
    · show j.val / n < N
      exact (Nat.div_lt_iff_lt_mul hn).mpr (by rw [Nat.mul_comm N n]; exact j.isLt)
    · show n - 1 - j.val % n < n
      omega
  · intro j j'
    rw [Fin.lt_def]
    exact key j.val j'.val

end LeanUrat.MovesC
