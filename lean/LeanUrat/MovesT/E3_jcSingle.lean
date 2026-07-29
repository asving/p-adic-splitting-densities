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

/-- RE-KEYED at the E8 ADJUDICATION (2026-07-30, per-site cell keying): (JC-single)
prices the SITE's OWN event (`siteCellEvent es ν` — the site node's branch stratum),
matching the re-keyed `SitePresents`; the retired form priced the entrance-keyed
full joint cell (`cellEventE es c`), the shared-cell seam. Proof unchanged: rewrite
both events by `hpres`, C4 verbatim. -/
theorem jc_single (T : TreeModel p F n N m pol) (CA : CellData p F n N m pol T)
    (χ : Fin n → Fin m) (es : EntSt p F n) (ν : Node p F)
    (Sigma : Locus p m) (fd : FreshData p m)
    (hpres : SitePresents T CA χ es ν Sigma fd)
    (hfree : ∀ cl ∈ fd.clauses, ∀ cIdx ∈ cl.support, Sigma.pinned cIdx = false) :
    Nat.card ↥(siteCellEvent T CA χ es ν) * p ^ fd.mstar
      = Nat.card ↥(entEvent T χ es) := by
  rw [hpres.1, hpres.2]
  exact C4_conditionalMass Sigma fd hfree

end LeanUrat.MovesT
