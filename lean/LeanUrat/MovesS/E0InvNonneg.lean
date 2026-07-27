/-
Unit U-23d `e0_inv_nonneg` (medium) — consumer [4]/SQ.2 only.
moves_ref: "the Neumann series converges, and (I − A(q₀))^{−1} ≥ 0".
sketch: `(1-A)⁻¹ = Σ_{m<k} A^m + (1-A)⁻¹ A^k` (U-23a); nonneg partial sums
(U-23b); remainder → 0 (U-23c); closed limit.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.NeumannPartial
import LeanUrat.MovesS.PowEntryNonneg
import LeanUrat.MovesS.PowEntryTendsto

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix

theorem e0_inv_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℚ} (h : EscapeE0 A) :
    ∀ i j : ι, 0 ≤ (1 - A)⁻¹ i j :=
  sorry

end LeanUrat.MovesS
