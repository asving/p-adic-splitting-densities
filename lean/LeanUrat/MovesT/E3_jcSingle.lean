/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesC.C4_conditionalMass

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

/-- RE-KEYED at the T RATIFICATION (2026-07-31; verdict §1): (JC-single) prices the
site's EXACT cell event (`siteCellEvent es c` — the note's Ψ^{−1}(c_s) over Σ,
MOVES 7448–7449 & 7469–7472), matching the re-keyed `SitePresents`; the 2026-07-30
branch-stratum keying (by the site node ν) is superseded. Proof unchanged: rewrite
both events by `hpres`, C4 verbatim. -/
theorem jc_single (T : TreeModel p F n N m pol) (CA : CellData p F n N m pol T)
    (χ : Fin n → Fin m) (es : EntSt p F n) (c : CA.Cell)
    (Sigma : Locus p m) (fd : FreshData p m)
    (hpres : SitePresents T CA χ es c Sigma fd)
    (hfree : ∀ cl ∈ fd.clauses, ∀ cIdx ∈ cl.support, Sigma.pinned cIdx = false) :
    Nat.card ↥(siteCellEvent T CA χ es c) * p ^ fd.mstar
      = Nat.card ↥(entEvent T χ es) := by
  rw [hpres.1, hpres.2]
  exact C4_conditionalMass Sigma fd hfree

end LeanUrat.MovesT
