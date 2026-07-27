/-
Unit D6d.htH_shape  (MovesD campaign, E-phase)
moves_ref: "each alphabet cardinality a power of p determined by the history's SHAPE data
(§C C.3, verbatim)" (L9).
deps: D6b, D6c.
sketch: Finset.sum congruence of the two K1-chain formulas.  difficulty: easy.
hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs
import LeanUrat.MovesD.D6b_kappaShape
import LeanUrat.MovesD.D6c_innerslotShape

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n : ℕ}
  {P : Shape n}

/-- The K1-chain heights are shape data. -/
theorem htH_shape {H : History p F} (hP : (P : ShapePrefix).MatchesHist H) :
    ∀ i c, H.htH i c = (P : ShapePrefix).htS i c := by
  intro i c
  simp only [History.htH, ShapePrefix.htS]
  refine congrArg (fun s => (c.1 : ℚ) + s) (Finset.sum_congr rfl ?_)
  intro r _
  rw [innerslot_shape hP r c.2, kappaH_shape hP r]

end LeanUrat.MovesD
