/-
Unit U-23c `pow_entry_tendsto` (easy) — squeeze between 0 and `((A^k) *ᵥ 1) i`.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.PowEntryNonneg

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix

theorem pow_entry_tendsto {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℚ} (h : EscapeE0 A) (i j : ι) :
    Filter.Tendsto (fun k => (A ^ k) i j) Filter.atTop (nhds 0) :=
  sorry

end LeanUrat.MovesS
