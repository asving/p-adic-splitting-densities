/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.Moves.L2_slotDecomp_R4
import LeanUrat.Moves.L2_strideRule

/-!
# HC1.T8_alphabetStep — the (ii.2) step bijection onto the alphabet

moves_ref: MOVES 2139–2160 ((ii.2), 𝔸(γ) = u(γ)·{Σ c_i z̄^i}, "an F_p-SUBSPACE … of
size Π |𝔸_k(γ_i)|; distinct attainable tuples give distinct values"). deps: T4, T5,
T7; Moves `L2_slotDecomp_R4`, `L2_strideRule` (clean). difficulty: HARD (pre-split:
T8a fixed-level bijection; T8b the tower induction on block size). hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves
open scoped Classical

/-- Unit T8: an attainable-tuple subgroup on which the typComposite is an additive
BIJECTION onto the alphabet, with the per-height block-size law
`p ^ aDim = #(attainable tuples)`. -/
theorem T8_alphabetStep {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (γ : ℚ) :
    ∃ A : AddSubgroup (↥(T.levelSet b γ) → ↥(T.stg 0).FQ),
      Set.BijOn (T.typComposite b γ) ↑A ↑(T.alphabet b γ) ∧
      (∀ x ∈ A, ∀ y ∈ A,
        T.typComposite b γ (x + y) = T.typComposite b γ x + T.typComposite b γ y) ∧
      p ^ T.aDim b γ = Nat.card ↥A := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.T8_alphabetStep
