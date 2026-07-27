/-
Unit `n2_ent_flow` (easy; S5 construction batch) — entrance carriers (one ε per
block, entLvl/entInst/hent/Went) + kstep/activeState/markedVal data (split).
The kstep pin is the 1×1 kernel entry q₀⁻³; activity is total (all states active
at all pools — the R45 per-cell form is n2_activity's).
-/
import LeanUrat.MovesS.N2Carriers

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_ent_flow :
    (∀ e (τ : n2T.State e) (ε ε' : n2M.EntShape e τ), ε = ε') ∧
    (∀ q₀ ∈ n2M.Pools, n2M.kstep 1 2 n2τ n2τ q₀ = ((q₀ : ℝ))⁻¹ ^ 3) ∧
    (∀ (q₀ : ℚ) e (τ : n2T.State e), n2M.activeState q₀ e τ) := by
  refine ⟨fun _ _ ε ε' => rfl, fun q₀ _ => ?_, fun _ _ _ => trivial⟩
  change ((if (2 : ℕ) = 2 then ((q₀ : ℝ))⁻¹ ^ 3 else 0) ^ 1) = ((q₀ : ℝ))⁻¹ ^ 3
  rw [if_pos rfl, pow_one]

end LeanUrat.MovesS
