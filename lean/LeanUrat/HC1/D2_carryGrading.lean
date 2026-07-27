/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsD

/-!
# HC1.D2_carryGrading — the u_ρ·u_σ law and homogeneity of products

moves_ref: MOVES 1508–1509 (the u_ρ·u_σ law). deps: D1 (via `CarryRingPack`).
difficulty: easy. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

/-- Unit D2: `dOf ρ c * dOf σ c' = dOf (ρ+σ) (c·c'·z̄^{carryExp ρ σ})`, and products
of homogeneous elements are homogeneous at the sum coset. -/
theorem D2_carryGrading {F : Type*} [Field F] {e : ℕ} [NeZero e] {zbar : Fˣ}
    (P : CarryRingPack F e zbar) :
    (∀ (ρ σ : ZMod e) (c c' : F),
      (letI := P.ring; dOf ρ c * dOf σ c')
        = dOf (ρ + σ) (c * c' * (zbar : F) ^ carryExp ρ σ)) ∧
    (∀ (x y : CarryAlg F e) (ρ σ : ZMod e), IsHomog x ρ → IsHomog y σ →
      IsHomog (letI := P.ring; x * y) (ρ + σ)) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.D2_carryGrading
