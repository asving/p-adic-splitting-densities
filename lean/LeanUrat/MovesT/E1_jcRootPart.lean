/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-E1 `jcRoot_partition` — "(JC-root) PROVED, unconditional" (MOVES 7464–7466):
cells are fibers of x ↦ x ∘ χ. PROVED. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem jcRoot_partition (χ : Fin n → Fin m) :
    ((Set.univ : Set (Box p m)) = ⋃ g : Fin n → ZMod p, rootCell χ g) ∧
    Pairwise (Function.onFun Disjoint (rootCell (p := p) χ)) := by
  constructor
  · ext x
    simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
    exact ⟨fun b => x (χ b), fun b => rfl⟩
  · intro g g' hgg'
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    exact hgg' (funext fun b => (hx b).symm.trans (hx' b))

end LeanUrat.MovesT
