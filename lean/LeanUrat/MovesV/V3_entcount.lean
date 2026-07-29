/-  MovesV unit V3-9a `ent_count_stmt` (RE-KEYED REV 3, F-2 + Codex-7) —
    ENT-COUNT as the NAMED BURDEN, per CONCRETE ε against the CENSUS. -/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- ENT-COUNT (owner [1v], OPEN — V.5(3)): each I^ent_{ε,β₀} is ONE
polynomial of degree ≤ W_ent(ε). -/
def EntCount {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) : Prop :=
  ∀ (ε : EntShapeV n) (β₀ : S.Cell), Realizable V ε β₀ →
    ∃ P : Polynomial ℚ, P.natDegree ≤ ε.Went ∧
      ∀ q₀ ∈ V.Pools, (P.eval q₀ : ℚ) = V.entCensus ε β₀ q₀

end LeanUrat.MovesV
