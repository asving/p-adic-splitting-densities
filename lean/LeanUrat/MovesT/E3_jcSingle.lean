/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-E3 `jc_single` — "(JC-single) PROVED (= C.1.5(1) verbatim)" (MOVES 7469–7472):
rewrite both events by `hpres`; the conclusion is MovesC `C4_conditionalMass`'s
identity verbatim. REV 3: over the entrance carrier. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem jc_single (T : TreeModel p F n N m pol) (CA : CellData p F n N m pol T)
    (χ : Fin n → Fin m) (es : EntSt p F n) (c : CA.Cell)
    (Sigma : Locus p m) (fd : FreshData p m)
    (hpres : SitePresents T CA χ es c Sigma fd)
    (hfree : ∀ cl ∈ fd.clauses, ∀ cIdx ∈ cl.support, Sigma.pinned cIdx = false) :
    Nat.card ↥(cellEventE T CA χ es c) * p ^ fd.mstar = Nat.card ↥(entEvent T χ es) := by
  sorry

end LeanUrat.MovesT
