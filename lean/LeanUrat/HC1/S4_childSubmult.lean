/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsSpine
import LeanUrat.Moves.L3_DIV
import LeanUrat.Moves.L4_TRANSi_R3

/-!
# HC1.S4_childSubmult — D.7(i): childW is submultiplicative

moves_ref: MOVES 2331–2337 (D.7(i), the slot-(j+k+1) Q-part strictly deeper by
(I-aug)). deps: S2; Moves `L3_DIV`, `L4_TRANSi_R3` (clean). sketch: re-develop
products; the ultrametric assembly is L4_TRANSi's content instantiated at childW.
difficulty: medium. hyp: none (the read's legality bundled as `TransHyp`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit S4: `childW (f·g) ≥ childW f + childW g` (via DIV(i) on coefficient
products + the (I-aug) strict depth of Q-terms). -/
theorem S4_childSubmult {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar)
    (f f' : Polynomial ℤ_[p]) (hf : f ≠ 0) (hf' : f' ≠ 0) :
    childW σ Φhat e' h' f + childW σ Φhat e' h' f'
      ≤ childW σ Φhat e' h' (f * f') := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S4_childSubmult
