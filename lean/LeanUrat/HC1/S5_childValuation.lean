/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsSpine
import LeanUrat.Moves.L4_TRANSiii_R3
import LeanUrat.Moves.L2_psiNotDvd_R3
import LeanUrat.Moves.L3_digPrime_nonzero

/-!
# HC1.S5_childValuation — D.7(iii): childW multiplicative, child value group ℤ

moves_ref: MOVES 2343–2352 (D.7(iii), incl. the F5 "nothing is renormalized"
clause: the un-rescaled form — coefficient weights e′·w(Ĉ) + h′ with
gcd(e′,h′) = 1). deps: S3, S4; Moves `L4_TRANSiii_R3`, `L2_psiNotDvd_R3`,
`L3_digPrime_nonzero` (clean). difficulty: medium. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit S5: `childW` is multiplicative on nonzeros and its value group is ℤ (the
generated-subgroup form, Stage's own `hvalgrp` shape). -/
theorem S5_childValuation {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) :
    (∀ f f' : Polynomial ℤ_[p], f ≠ 0 → f' ≠ 0 →
      childW σ Φhat e' h' (f * f')
        = childW σ Φhat e' h' f + childW σ Φhat e' h' f') ∧
    AddSubgroup.closure {n : ℤ | ∃ f f' : Polynomial ℤ_[p], f ≠ 0 ∧ f' ≠ 0 ∧
      childW σ Φhat e' h' f - childW σ Φhat e' h' f' = n} = ⊤ := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S5_childValuation
