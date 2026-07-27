/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar

/-!
# HC1.T11_attainDichotomy — pinning the composite is solvable iff on-alphabet

moves_ref: MOVES 2165–2168 "Pinning d_γ(B) = X is solvable iff X ∈ 𝔸(γ) — an
off-alphabet pin EMPTIES the locus". deps: T7, T8. difficulty: easy. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit T11: the attainability dichotomy (image characterization from T8's
bijection); a zero pin is always solvable (0 ∈ 𝔸). -/
theorem T11_attainDichotomy {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (γ : ℚ) (X : T.grQ γ) :
    ((∃ y : ↥(T.levelSet b γ) → ↥(T.stg 0).FQ, T.typComposite b γ y = X) ↔
      X ∈ T.alphabet b γ) ∧
    (X ∉ T.alphabet b γ →
      {y : ↥(T.levelSet b γ) → ↥(T.stg 0).FQ | T.typComposite b γ y = X} = ∅) ∧
    (0 : T.grQ γ) ∈ T.alphabet b γ := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.T11_attainDichotomy
