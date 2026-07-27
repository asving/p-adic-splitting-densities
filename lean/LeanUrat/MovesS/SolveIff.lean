/-
Unit U-13 `solve_iff` (easy) — GENERIC CARRIER (R22) + [DecidableEq ι] (Fable#4-F1):
the fixpoint form ⟺ the linear-system form.  Instances at Qq (U-14/16b) AND at ℝ
via `Aℝ` (U-24a1).  sketch: sub_mulVec/one_mulVec; sub_eq_iff.
-/
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix

theorem solve_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]
    (K : Matrix ι ι R) (b β : ι → R) :
    β = K *ᵥ β + b ↔ (1 - K) *ᵥ β = b := by
  rw [sub_mulVec, one_mulVec, sub_eq_iff_eq_add']

end LeanUrat.MovesS
