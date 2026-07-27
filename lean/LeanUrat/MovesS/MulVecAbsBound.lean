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
        ((A ^ k) *ᵥ (fun _ => (1 : ℚ))) i :=
  sorry

end LeanUrat.MovesS
