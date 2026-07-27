/-
Unit D4b.chart_count  (MovesD campaign, E-phase)  [AUX]
informal: pulled-back predicate counts over `Fin m` = grid filter counts.
deps: D4a.
sketch: `Nat.card_congr` along D4a's bijection; `Finset.card_filter` bridging.
difficulty: medium.  hypothesis_fields: none.
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

/-- Chart-pulled predicate counts equal grid filter counts. -/
theorem chart_count {H : History p F} (J : JetSetup H n N m) (φ : Coord → Prop)
    [DecidablePred φ] :
    Nat.card {c : Fin m // φ (J.coordOf c)}
      = ((Finset.range N ×ˢ Finset.range n).filter (fun c => φ c)).card := by
  sorry

end LeanUrat.MovesD
