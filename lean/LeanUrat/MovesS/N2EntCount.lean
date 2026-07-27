/-
Unit `n2_entcount` (easy; S5 ledger batch) — ENT-COUNT: the entLvl-level card
(G4's tie at ε's own defining level).
-/
import LeanUrat.MovesS.N2Carriers

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_entcount : ∀ e (τ : n2T.State e) (ε : n2M.EntShape e τ) (q₀ : ℚ),
    q₀ ∈ n2M.Pools → n2M.activeState q₀ e τ →
    (n2M.entInst e τ ε q₀ (n2M.entLvl e τ ε)).card = n2M.entCount e τ ε q₀ :=
  sorry

end LeanUrat.MovesS
