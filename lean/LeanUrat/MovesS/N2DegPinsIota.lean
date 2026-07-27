/-
Unit `n2_degpins_iota` (easy; S5 construction batch) — the ι degree pins
(ENT-COUNT polynomials of degree ≤ W_ent(ε), both pieces).
-/
import LeanUrat.MovesS.N2PolyGeom

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_degpins_iota : ∀ e (τ : n2T.State e) (ε : n2M.EntShape e τ),
    (n2RB.ιP e τ ε).degBoundT = n2M.Went e τ ε ∧
    (n2RB.ιP e τ ε).degBoundS = n2M.Went e τ ε :=
  fun e τ ε => ⟨n2RB.ι_degT e τ ε, n2RB.ι_degS e τ ε⟩

end LeanUrat.MovesS
