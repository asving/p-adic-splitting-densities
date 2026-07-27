/-
Unit D4a.chart_bij  (MovesD campaign, E-phase)  [AUX]
informal: a JetSetup's ≺-sorted chart is a bijection onto the N×n grid.
deps: MovesC.Defs.
sketch: injectivity from `coordOf_sorted` + `CoordPrec` irreflexivity; surjectivity from
injective-into-a-grid-of-card-m (`J.hm`, pigeonhole).  difficulty: medium.
hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n N m : ℕ}

/-- The ≺-sorted chart is a bijection onto the N×n grid. -/
theorem chart_bij {H : History p F} (J : JetSetup H n N m) :
    Function.Injective J.coordOf ∧
      ∀ c ∈ Finset.range N ×ˢ Finset.range n, ∃ j : Fin m, J.coordOf j = c := by
  sorry

end LeanUrat.MovesD
