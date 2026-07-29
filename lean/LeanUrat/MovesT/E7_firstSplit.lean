/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-E7 `fiber_first_split` [hard] — FIRST SPLIT (MOVES 7503–7515): the SIB
product at the SITE's conditioning event through `hdecomp`. The frame prices its OWN
`scope` (REV 5, Codex-4 #3); `belowEnt`/`SubtreeFiber`/`SplitSiteData` are Defs
carriers (REV 6, Codex-5 gap #9).

RE-KEYED at the E8 ADJUDICATION (2026-07-30, per-site cell keying): the frame now
sits AT the split site (`d.es` = the site's own state), its conditioning event is
`entEvent d.es` = the note's Σ_c, and the (SIB) input is the SITE-LEVEL count row
(`SibCountAt`-shaped, TREE-EXP's `hsibT` — the global entrance-cell `SibCount`
cannot reach the site conditioning under per-site keying: its `.st`-instances
condition on the strictly finer CHILDREN-JOINT cell). The former (B) leg (the
charge-composed display, `hcharge` from T-E3/`hjcm`) is retired here — under
per-site keying each site's own charge is T-E6's, composed in the T-E8 assembly. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem fiber_first_split (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m)
    (d : SplitSiteData Tr T CA χ)
    (hsibAt : Nat.card ↥(entEvent T χ d.es ∩ ⋂ ν ∈ CA.branchSetOf d.c, d.S ν)
        * (Nat.card ↥(entEvent T χ d.es)) ^ ((CA.branchSetOf d.c).card - 1)
      = ∏ ν ∈ CA.branchSetOf d.c, Nat.card ↥(entEvent T χ d.es ∩ d.S ν)) :
    Nat.card ↥(d.scope ∩ entEvent T χ d.es)
        * (Nat.card ↥(entEvent T χ d.es)) ^ ((CA.branchSetOf d.c).card - 1)
      = ∏ ν ∈ CA.branchSetOf d.c,
          Nat.card ↥(entEvent T χ d.es ∩ d.S ν) := by
  rw [d.hdecomp]
  exact hsibAt

end LeanUrat.MovesT
