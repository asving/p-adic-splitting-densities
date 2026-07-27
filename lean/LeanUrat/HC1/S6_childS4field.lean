/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsSpine
import LeanUrat.Moves.L4_TRANSv_R3
import LeanUrat.Moves.L4_TRANSviii_b_R4
import LeanUrat.Moves.L2_widthBound

/-!
# HC1.S6_childS4field — D.7(v): the child degree-0 coefficient field is F′ = K⟮z̄⟯

moves_ref: MOVES 2364–2391 (D.7(v), ingredients (1)–(3) displayed). deps: S5;
Moves `L4_TRANSv_R3` (CLEAN — repaired at 4b29f6e, +StageCore fence-change
APPROVED per its header; §4.3 CLOSED — S6 supplies `hcore` from the spine),
`L4_TRANSviii_b_R4` (clean, the (S6b) recursion), `L2_widthBound` (clean). sketch:
unit-monomial weights from powers of in(p); g consecutive stride positions; (S6b)
scalars above the clean threshold; span = F′. difficulty: HARD. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit S6: the D-map (dig′ per piece) on the lift coefficient space `C_Φ̂` is
additive-injective per piece (equal digits at equal weight force a deeper
difference) with image ALL of F′ = K⟮z̄⟯ by the LARGE-WEIGHT (S6b) argument. -/
theorem S6_childS4field {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) :
    (∀ x : F, x ∈ σ.nextField zbar → x ≠ 0 →
      ∃ B : Polynomial ℤ_[p], B ≠ 0 ∧ inC Φhat B ∧ σ.digPrime zbar B = x) ∧
    (∀ B : Polynomial ℤ_[p], B ≠ 0 → inC Φhat B →
      σ.digPrime zbar B ∈ σ.nextField zbar) ∧
    (∀ B B' : Polynomial ℤ_[p], B ≠ 0 → B' ≠ 0 → B - B' ≠ 0 →
      inC Φhat B → inC Φhat B' → σ.w B = σ.w B' →
      σ.digPrime zbar B = σ.digPrime zbar B' → σ.w B < σ.w (B - B')) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S6_childS4field
