/-
Unit U-29d-i `n2_beta` (medium) — the RS1Bundle instance: βmeas := the evaluated
solve values (β_bdd from the explicit [0,1] bounds).  The pinned values are the
note-displayed reduced solve: β_{(1,2)} = (q+1)/(q²+q+1), β_{(1,1)²} =
q²/(q²+q+1).
-/
import LeanUrat.MovesS.Interfaces
import LeanUrat.MovesS.N2PolyGeom
import LeanUrat.MovesS.N2ScsData

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

noncomputable def n2B : RS1Bundle n2T n2M n2RB n2hdc n2hK := sorry

theorem n2_beta : ∀ (he : 2 ∈ Finset.Icc 1 2) (h_ent : ℕ) (q₀ : ℚ),
    q₀ ∈ n2M.Pools →
    n2B.βmeas 2 he h_ent n2τ {n2v12} q₀ = (((q₀ + 1) / (q₀ ^ 2 + q₀ + 1) : ℚ) : ℝ) ∧
    n2B.βmeas 2 he h_ent n2τ {n2v11, n2v11} q₀ = ((q₀ ^ 2 / (q₀ ^ 2 + q₀ + 1) : ℚ) : ℝ) :=
  sorry

end LeanUrat.MovesS
