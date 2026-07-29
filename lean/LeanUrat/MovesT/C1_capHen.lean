/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-C1 `tbcap_hen` — CAP N_V = 1, uniform per class (MOVES 7155–7159): the class
IS a finite union of level-0 cells. PROVED-IN-NOTE status: unconditional. The locality
face is PROVED here; the finite-union face carries the E-phase sorry. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

/-- `redPoly χ x` is a function of x ∘ χ. -/
theorem redPoly_congr (χ : Fin n → Fin m) (x x' : Box p m)
    (hxx : ∀ b : Fin n, x (χ b) = x' (χ b)) :
    redPoly χ x = redPoly (p := p) χ x' := by
  unfold redPoly
  congr 1
  exact Finset.sum_congr rfl fun b _ => by rw [hxx b]

theorem tbcap_hen (χ : Fin n → Fin m) (hχ : Function.Injective χ)
    (x x' : Box p m) (hxx : ∀ b : Fin n, x (χ b) = x' (χ b)) :
    henPayload χ x = henPayload χ x' := by
  unfold henPayload henDegrees
  rw [redPoly_congr χ x x' hxx]

theorem tbcap_hen_cells (χ : Fin n → Fin m) (hχ : Function.Injective χ)
    (v₀ : Multiset Vd) :
    ∃ G : Finset (Fin n → ZMod p),
      {x : Box p m | henPayload χ x = v₀} = ⋃ g ∈ G, rootCell χ g := by
  sorry

end LeanUrat.MovesT
