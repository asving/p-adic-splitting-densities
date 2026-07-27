/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsD

/-!
# HC1.D6_carryHomogUnits — nonzero homogeneous elements are units of 𝒟

moves_ref: MOVES 1513–1514 (digits live in homogeneous components; the R-calculus
needs their invertibility). deps: D2. difficulty: easy. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

/-- Unit D6: the inverse of `dOf ρ c` is `dOf (−ρ) (c⁻¹·z̄^{−carryExp ρ (−ρ)})`, and
every nonzero homogeneous element is a unit. -/
theorem D6_carryHomogUnits {F : Type*} [Field F] {e : ℕ} [NeZero e] {zbar : Fˣ}
    (P : CarryRingPack F e zbar) :
    (∀ (ρ : ZMod e) (c : F), c ≠ 0 →
      (letI := P.ring;
        dOf ρ c * dOf (-ρ) (c⁻¹ * ((zbar : F) ^ carryExp ρ (-ρ))⁻¹) = 1)) ∧
    (∀ (x : CarryAlg F e) (ρ : ZMod e), IsHomog x ρ → x ≠ 0 →
      (letI := P.ring; IsUnit x)) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.D6_carryHomogUnits
