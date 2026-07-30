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
    Filter.Tendsto (fun k => (A ^ k) i j) Filter.atTop (nhds 0) := by
  -- Upper bound: the i-th coordinate of `(A^k) *ᵥ 1`, which escapes to 0.
  have hesc : Filter.Tendsto (fun k => ((A ^ k) *ᵥ (fun _ => (1 : ℚ))) i)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_pi_nhds.mp h.escape) i
  -- Squeeze `(A^k) i j` between the constant `0` and that escaping coordinate.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hesc ?_ ?_
  · intro k
    exact pow_entry_nonneg h.nonneg k i j
  · intro k
    show (A ^ k) i j ≤ ((A ^ k) *ᵥ (fun _ => (1 : ℚ))) i
    have hsum : ((A ^ k) *ᵥ (fun _ => (1 : ℚ))) i = ∑ j', (A ^ k) i j' := by
      simp [Matrix.mulVec, dotProduct]
    rw [hsum]
    exact Finset.single_le_sum (fun j' _ => pow_entry_nonneg h.nonneg k i j')
      (Finset.mem_univ j)

end LeanUrat.MovesS
