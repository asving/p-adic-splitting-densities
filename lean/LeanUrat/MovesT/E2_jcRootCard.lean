/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-E2 `jcRoot_card` (MOVES 7464–7468, incl. the degree-1 base case): the
coordinate-splitting equivalence (MovesC C4's `putOn` idiom). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem jcRoot_card (χ : Fin n → Fin m) (hχ : Function.Injective χ)
    (g : Fin n → ZMod p) :
    Nat.card ↥(rootCell χ g) * p ^ n = p ^ m := by
  sorry

end LeanUrat.MovesT
