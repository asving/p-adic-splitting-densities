/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-E9 `tree_fiber_disjoint` — "one f, ONE tree … a genuine PARTITION of the
decided set" (MOVES 7025–7029). TRUE under the repaired `fiberAt` (REV 2, Codex 14).
The conclusion IS `VTree.ext Tr Tr'` definitionally — the quotient bridge T-F1/T-E13
consume. The CHOICE-FREENESS payoff, unconditional. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem tree_fiber_disjoint (Tr Tr' : VTree p F) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (x : Box p m)
    (h : Tr.fiberAt T χ x) (h' : Tr'.fiberAt T χ x) :
    Tr.chains = Tr'.chains ∧ Tr.henV = Tr'.henV ∧
    ∀ H ∈ Tr.chains, Tr.leafV H = Tr'.leafV H ∧ (Tr.nsLeaf H ↔ Tr'.nsLeaf H) := by
  sorry

end LeanUrat.MovesT
