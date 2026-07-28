/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsChild
import LeanUrat.HC1.K1_vertexPin
import LeanUrat.Moves.L4_TRANSviii_a_R5_final
import LeanUrat.Moves.L4_TRANSviii_b_R4

/-!
# HC1.S9b_childWeightSet — the (S6′) legs: weightSet := 𝒜′, realizers via the
TRANSviii finals

S9 DECOMPOSITION unit (blueprint §9.5): "S9b: weightSet := 𝒜′ + hS6a/hS6b via the
TRANSviii finals." The `hS6a`/`hS6b` realizer laws are `Stage` fields of the
literal; this unit's statement content is that the literal can be built with its
`weightSet` PINNED to 𝒜′ (`childWeightSet` — the parent-scale coefficient weight
set, read against `σ'.wPrev = σ.w`), cumulatively over S9a's conjuncts. The
(S6a′) constant-orbit realizers and the (S6b′) offset P-lift with clean threshold
are `L4_TRANSviii_a_R5_final`/`L4_TRANSviii_b_R4`'s content (clean Moves finals),
discharged inside the construction. difficulty: HARD (assembly). hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit S9b: the S9a literal can be assembled with its `weightSet` pinned to the
child parent-scale coefficient weight set 𝒜′. -/
theorem S9b_childWeightSet {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) :
    ∃ σ' : Stage p F,
      TransitionData σ σ' Φhat e' h' zbar ∧
      VertexPin σ σ' Φhat zbar ∧
      (∀ f, f ≠ 0 → σ'.w f = childW σ Φhat e' h' f) ∧
      σ'.weightSet = childWeightSet σ Φhat := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S9b_childWeightSet
