/-  MovesV unit V0-1 `affine_pos` — §3 layer V0.
    moves_ref: "E affine in h with positive weights" (XHD-w). -/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem affine_strictMono {D : ℕ} (E : AffineE D) (h : Hpt D) (i : Fin D) :
    StrictMono (fun t => E.eval (Function.update h i t)) := by
  intro a b hab
  unfold AffineE.eval
  apply Nat.add_lt_add_left
  apply Finset.sum_lt_sum
  · intro x _
    by_cases hx : x = i
    · subst hx
      simp only [Function.update_self]
      exact Nat.mul_le_mul_left _ hab.le
    · simp [Function.update_of_ne hx]
  · exact ⟨i, Finset.mem_univ i, by
      simp only [Function.update_self]
      exact Nat.mul_lt_mul_of_le_of_lt le_rfl hab (E.pos i)⟩

theorem affine_ge_const {D : ℕ} (E : AffineE D) (h : Hpt D) :
    E.const ≤ E.eval h :=
  Nat.le_add_right _ _

end LeanUrat.MovesV
