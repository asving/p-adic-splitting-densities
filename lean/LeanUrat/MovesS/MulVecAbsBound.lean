/-
Unit U-21b `mulVec_abs_bound` (medium) — [Nonempty ι] (R2-16).  deps: U-23b.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.PowEntryNonneg

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix

theorem mulVec_abs_bound {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A : Matrix ι ι ℚ} (hA : ∀ i j, 0 ≤ A i j) (v : ι → ℚ) (k : ℕ) (i : ι) :
    |((A ^ k) *ᵥ v) i| ≤
      (Finset.univ.sup' Finset.univ_nonempty fun j => |v j|) *
        ((A ^ k) *ᵥ (fun _ => (1 : ℚ))) i := by
  have hB : ∀ p q, 0 ≤ (A ^ k) p q := fun p q => pow_entry_nonneg hA k p q
  have hsup : ∀ j, |v j| ≤ Finset.univ.sup' Finset.univ_nonempty (fun j => |v j|) :=
    fun j => Finset.le_sup' (fun j => |v j|) (Finset.mem_univ j)
  have hvsum : ((A ^ k) *ᵥ v) i = ∑ j, (A ^ k) i j * v j := rfl
  have h1sum : ((A ^ k) *ᵥ (fun _ => (1 : ℚ))) i = ∑ j, (A ^ k) i j := by
    show ∑ j, (A ^ k) i j * (1 : ℚ) = ∑ j, (A ^ k) i j
    simp
  rw [hvsum, h1sum]
  calc |∑ j, (A ^ k) i j * v j|
      ≤ ∑ j, |(A ^ k) i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, (A ^ k) i j * |v j| := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [abs_mul, abs_of_nonneg (hB i j)]
    _ ≤ ∑ j, (A ^ k) i j *
          (Finset.univ.sup' Finset.univ_nonempty (fun j => |v j|)) :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hsup j) (hB i j))
    _ = (Finset.univ.sup' Finset.univ_nonempty fun j => |v j|) *
          ∑ j, (A ^ k) i j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

end LeanUrat.MovesS
