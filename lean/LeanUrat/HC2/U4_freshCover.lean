/-
Unit U4.mkFresh_cover  (HC-2 campaign, E-phase — blueprint §5 Layer A)
moves_ref: MovesC `fresh_cover` docstring ("every band coordinate lies in SOME clause's
support — EXACTLY one, by disj").
deps: D6, U2.  difficulty: easy-medium.  hypothesis_fields: none.
sketch: dichotomy on `IsValueCoord c`: value → c is in its slot's level set = that value
clause's support; non-value → its strip clause exists by D6's strip roster.
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- Every band coordinate is covered by some constructed clause's support (verbatim
`JetSetup.fresh_cover`'s field type at `mkFresh`). -/
theorem mkFresh_cover {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ) {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (i : ℕ) (hi : i < H.nodes.length) :
    ∀ c : Fin (n * N), inFreshBand H n (boxChart n N) i (H.nodes[i]'hi) c →
      ∃ cl ∈ (mkFresh H n N S vOf i hi).clauses, c ∈ cl.support := by
  sorry

end LeanUrat.MovesJ
