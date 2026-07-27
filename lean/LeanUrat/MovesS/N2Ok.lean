/-
Unit `n2_ok` (easy; S5 construction batch) — tg_ok/j_ok/ι_ok at every pool
(split): the explicit denominators (powers of X) vanish at no prime power.
-/
import LeanUrat.MovesS.N2PolyGeom

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_ok : ∀ e (τ : n2T.State e) (q₀ : ℚ), q₀ ∈ n2M.Pools →
    (∀ o : n2T.Out e τ,
      (n2RB.tgP e τ o).val ∈ OKat q₀ ∧ (n2RB.jP e τ o).val ∈ OKat q₀) ∧
    (∀ ε : n2M.EntShape e τ, (n2RB.ιP e τ ε).val ∈ OKat q₀) :=
  sorry

end LeanUrat.MovesS
