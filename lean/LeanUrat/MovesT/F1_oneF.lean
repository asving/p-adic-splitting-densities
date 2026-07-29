/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.E9_fiberDisjoint

/-! # T-F1 `oneF` — "(ONE-F) … f HAS exactly one tree" (MOVES 7579–7589), INDEPENDENT
of TREE-EXP: totality + choice-freeness alone (NO hsib, NO hjcm). Uniqueness IS
uniqueness-up-to-ext, which T-E9's tuple delivers verbatim. This is `OneFStmt`
(Defs §2.10) pointwise. PROVED (modulo T-E9's own E-phase discharge). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem oneF (T : TreeModel p F n N m pol) (χ : Fin n → Fin m) (x : Box p m)
    (hx : Decided T χ x) :
    ∃ Tr : VTree p F, Tr.fiberAt T χ x ∧
      ∀ Tr' : VTree p F, Tr'.fiberAt T χ x → VTree.ext Tr Tr' := by
  obtain ⟨Tr, hTr⟩ := hx
  exact ⟨Tr, hTr, fun Tr' hTr' => tree_fiber_disjoint Tr Tr' T χ x hTr hTr'⟩

end LeanUrat.MovesT
