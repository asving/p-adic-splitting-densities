/-
Unit `n2_interp_iota` (easy; S5 construction batch) — ι interpolation +
ι_count/ι_countS_one (split).
-/
import LeanUrat.MovesS.N2PolyGeom

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_interp_iota :
    ∀ e (τ : n2T.State e) (ε : n2M.EntShape e τ) (q₀ : ℚ) (h : q₀ ∈ n2M.Pools),
    ((evalAt q₀ ⟨(n2RB.ιP e τ ε).val, n2RB.ι_ok e τ ε q₀ h⟩ : ℚ) : ℝ)
        = n2M.ιsh e τ ε q₀ ∧
    (n2RB.ιP e τ ε).countS = 1 ∧
    ((n2RB.ιP e τ ε).countT.eval q₀ : ℚ) = (n2M.entCount e τ ε q₀ : ℚ) :=
  fun e τ ε q₀ h =>
    ⟨n2RB.ι_interp e τ ε q₀ h, n2RB.ι_countS_one e τ ε, n2RB.ι_count e τ ε q₀ h⟩

end LeanUrat.MovesS
