/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsSpine
import LeanUrat.Moves.L4_TRANSviii_a_R5_final
import LeanUrat.Moves.L4_TRANSviii_b_R4
import LeanUrat.MovesGr.HeldUnits_certs

/-!
# HC1.S8_childS6 — D.7(viii): the split axiom transports; child TvecUnitLaw DERIVED

moves_ref: MOVES 2419–2463 (D.7(viii), both halves + consumers). deps: S7; Moves
`L4_TRANSviii_a_R5_final`, `L4_TRANSviii_b_R4` (clean); MovesGr
`tvec_units_fragment` (proved fragment). The child `TvecUnitLaw` is DERIVED from
the parent `StageCoreL.tvec_unit` + `child_Tvec` — the `L4_TRANSvi` held fence
(child T-law not from (ht,M′) alone). The (S6a′)/(S6b′) fields ride the assembled
child Stage; the non-projection content here is the T-law + the previous-read
(I-aug) threshold recursion bottoming at the base. difficulty: medium. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit S8: the child T-vector product law at the actual normalizing unit, and the
child's previous-read (I-aug) law (the two-line mutual recursion's bottoming data),
derived from the parent core + the transition record. -/
theorem S8_childS6 {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ σ' : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar)
    (tc : TransitionCoreL σ σ' Φhat e' h' zbar) :
    TvecUnitLaw σ' ∧ ((σ'.e : ℤ) * σ'.wPrev σ'.Φ < (σ'.h : ℤ)) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S8_childS6
