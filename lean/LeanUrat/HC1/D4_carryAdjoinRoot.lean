/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsD

/-!
# HC1.D4_carryAdjoinRoot — 𝒟 ≃+* F[u]/(u^e − z̄)

moves_ref: MOVES 1509 "𝒟 ≅ F_{r+1}[u]/(u^e − z̄)". deps: D1, D2.
difficulty: medium. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

/-- Unit D4: the ring iso `CarryAlg F e ≃+* AdjoinRoot (X^e − C z̄)` sending
`dOf ρ c ↦ c·u^{ρ.val}` (e ≥ 1). -/
theorem D4_carryAdjoinRoot {F : Type*} [Field F] {e : ℕ} [NeZero e] {zbar : Fˣ}
    (P : CarryRingPack F e zbar) :
    ∃ Θ : (letI := P.ring;
        CarryAlg F e ≃+* AdjoinRoot (Polynomial.X ^ e - Polynomial.C ((zbar : F)))),
      ∀ (ρ : ZMod e) (c : F),
        Θ (dOf ρ c) = algebraMap F _ c *
          AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C ((zbar : F))) ^ ρ.val := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.D4_carryAdjoinRoot
