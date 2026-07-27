/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsD

/-!
# HC1.D5_carryE1 — at e = 1 the carry algebra is a plain field

moves_ref: MOVES 1483–1486 (e″ = 1 reads vs e_birth cosets — the distinction the
D6 threading rides on). deps: D1. sketch: ZMod 1 a point; ρ = σ = 0 has
val 0 + 0 < 1, so carryExp = 0; the iso is evaluation at the point.
difficulty: easy. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

/-- Unit D5: `CarryAlg F 1 ≃+* F` (the trivial twist; every e_read = 1 read sees a
plain field). -/
theorem D5_carryE1 {F : Type*} [Field F] {zbar : Fˣ} (P : CarryRingPack F 1 zbar) :
    ∃ Θ : (letI := P.ring; CarryAlg F 1 ≃+* F),
      ∀ x : CarryAlg F 1, Θ x = x 0 := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.D5_carryE1
