/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsTower

/-!
# HC1.D8_digD_recenter — a recentering preserves the 𝒟-typing

moves_ref: MOVES 2668 "S5: coefficient digits LITERALLY unchanged (same C, same v,
same T; position 0)" + 1523–1526 (e_birth vs e_read). deps: DefsD, Moves DefsCore
(`IsRecenteringCore`). difficulty: easy. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit D8: coefficients' birth cosets ride through e_read = 1 moves untouched. -/
theorem D8_digD_recenter {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ σ' : Stage p F) (cc : ↥σ.K) (tt : Polynomial ℤ_[p])
    (hrec : IsRecenteringCore σ σ' cc tt) (zbar : Fˣ) (e_b : ℕ) [NeZero e_b]
    (B : Polynomial ℤ_[p]) (hB : B ≠ 0) (hBc : inC σ.Φ B) :
    σ'.digD zbar e_b B = σ.digD zbar e_b B := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.D8_digD_recenter
