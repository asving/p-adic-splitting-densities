/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar

/-!
# HC1.T7_alphabetSpan — the alphabet is the finite additive span of the slot images

moves_ref: MOVES 3815–3821 "image = the additive span of the slot images … = the
digit's ALPHABET". deps: DefsCar, T6. sketch: closure of finitely many F_p-lines in
an elementary abelian p-group; card a p-power. difficulty: easy. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves
open scoped Classical

/-- Unit T7: the alphabet is the set of finite sums of single-coordinate slot
images, is finite, and its cardinality is exactly `p ^ aDim` (the exactness
equation is the theorem; `aDim` is the p-logarithm by definition). -/
theorem T7_alphabetSpan {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (γ : ℚ) :
    ((T.alphabet b γ : Set (T.grQ γ)) =
      { x | ∃ (s : Finset ↥(T.levelSet b γ)) (dig : ↥(T.levelSet b γ) → ↥(T.stg 0).FQ),
          x = ∑ c ∈ s, T.typComposite b γ (Pi.single c (dig c)) }) ∧
    Finite ↥(T.alphabet b γ) ∧
    p ^ T.aDim b γ = Nat.card ↥(T.alphabet b γ) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.T7_alphabetSpan
