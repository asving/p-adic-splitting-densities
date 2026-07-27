/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsD

/-!
# HC1.D3_carryDomain — products of nonzero homogeneous elements are nonzero

moves_ref: MOVES 1510–1511 "products of nonzero homogeneous elements nonzero
(c·c′·z̄^κ ≠ 0 in the field — the graded-domain property, irreducibility not
needed)". deps: D2. difficulty: easy. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

/-- Unit D3: the graded-domain property of 𝒟. -/
theorem D3_carryDomain {F : Type*} [Field F] {e : ℕ} [NeZero e] {zbar : Fˣ}
    (P : CarryRingPack F e zbar) (x y : CarryAlg F e) (ρ σ : ZMod e)
    (hx : IsHomog x ρ) (hy : IsHomog y σ) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    (letI := P.ring; x * y) ≠ 0 := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.D3_carryDomain
