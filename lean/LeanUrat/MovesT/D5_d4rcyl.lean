/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-D5 `d4rcyl_canonical` — MovesD's pinned `D4R_CYL` from the NAMED `RunKey`
(W4-3(c); REV 2, Fable CRIT-4 + Codex 22: the ∀-jet quantifier OUTSIDE the iff, so
both legs come per jet — no jet-independence needed). PROVED. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem d4rcyl_canonical {P : Shape n} (S : Presented p F n N m pol P)
    (T : TreeModel p F n N m pol) (hkey : RunKey T P) :
    D4R_CYL S T :=
  fun i x => hkey (reprOf i) i.2.choose_spec.1 x (S.jet i)

end LeanUrat.MovesT
