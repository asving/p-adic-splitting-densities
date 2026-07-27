/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsSpine
import LeanUrat.Moves.L0_FactA_exists
import LeanUrat.Moves.L0_FactB_unique

/-!
# HC1.S2_childW — the child valuation function is well-defined

moves_ref: MOVES 2329 "w′(Σ_j B_j Φ̂^j) := min_j (e′·w(B_j) + j·h′)". deps:
DefsSpine; Moves `L0_FactA_exists`, `L0_FactB_unique` (clean). difficulty: HARD
(the function-level development + attained min is real plumbing; pre-split: S2a
development function; S2b the IsSlotMinWeight law). hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit S2: for f ≠ 0 the Φ̂-development exists and is unique, the min is attained
at `childW`'s value, and `IsSlotMinWeight (childW σ Φhat e' h') Φhat e' h' σ.w`
holds. -/
theorem S2_childW {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (Φhat : Polynomial ℤ_[p]) (hmon : Φhat.Monic)
    (hdeg : 1 ≤ Φhat.natDegree) (e' h' : ℕ) :
    (∀ f : Polynomial ℤ_[p], f ≠ 0 →
      ∃ (B : ℕ → Polynomial ℤ_[p]) (N : ℕ), IsDevelopment Φhat f B N ∧
        SlotMinAttained (childW σ Φhat e' h' f) N
          (fun j => (e' : ℤ) * σ.w (B j) + (j : ℤ) * (h' : ℤ)) (fun j => B j ≠ 0)) ∧
    IsSlotMinWeight (childW σ Φhat e' h') Φhat e' h' σ.w := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S2_childW
