/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar

/-!
# HC1.C3_TYPb — TYP(b): image = alphabet, equipotent fibers, exact |𝔸|⁻¹ cut

moves_ref: MOVES 3813–3824 "additive with image = the additive span of the slot
images … An additive surjection onto its image has equal-size fibers (kernel
cosets), so the clause cuts exactly (alphabet)^{−1}". deps: C2, T7, T8.
difficulty: medium. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit C3: the composite's image is the alphabet; fibers over the image are
equipotent; a fresh value clause at exact valuation γ' cuts exactly |𝔸|⁻¹ among
level-set assignments (division-free). -/
theorem C3_TYPb {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (γ' : ℚ) :
    (Set.range (T.typComposite b γ') = ↑(T.alphabet b γ')) ∧
    (∀ X X' : T.grQ γ', X ∈ T.alphabet b γ' → X' ∈ T.alphabet b γ' →
      Nat.card {y : ↥(T.levelSet b γ') → ↥(T.stg 0).FQ // T.typComposite b γ' y = X}
        = Nat.card {y : ↥(T.levelSet b γ') → ↥(T.stg 0).FQ // T.typComposite b γ' y = X'}) ∧
    (∀ X : T.grQ γ', X ∈ T.alphabet b γ' →
      Nat.card {y : ↥(T.levelSet b γ') → ↥(T.stg 0).FQ // T.typComposite b γ' y = X}
          * Nat.card ↥(T.alphabet b γ')
        = Nat.card (↥(T.levelSet b γ') → ↥(T.stg 0).FQ)) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.C3_TYPb
