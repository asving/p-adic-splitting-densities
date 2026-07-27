/-
Unit U2.mkFresh_disj  (HC-2 campaign, E-phase — blueprint §5 Layer A)
moves_ref: §C C.1.5′ "pairwise disjoint: the factors multiply".
deps: D6.  difficulty: easy-medium.  hypothesis_fields: none.
sketch: strips are singletons at non-value coords; value supports are level sets of
distinct span slots (distinct fine blocks → disjoint) and exclude non-value coords by
definition. NOTE: the P-phase prover fills BOTH this consumer form and the Defs forward
lemma `mkFreshClauses_disj` (the same argument).
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- The constructed fresh clauses have pairwise-disjoint supports. -/
theorem mkFresh_disj {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ) {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (i : ℕ) (hi : i < H.nodes.length) :
    (mkFresh H n N S vOf i hi).clauses.Pairwise
      (fun c₁ c₂ => Disjoint c₁.support c₂.support) := by
  sorry

end LeanUrat.MovesJ
