/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-D4 `cellLevel_local` — W4-2(b)(ii): the withdrawn cap-envelope `cell_local`
replaced at the per-state level (`siteLevel`, Defs §2.5). Soundness PROVED; the
falsifier is a 2-coordinate toy witness (surrogate + bridge — Gates layer). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem cellLevel_local_sound (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T)
    (o : Option (History p F)) (hlev : CA.cellLevel (embE o) = siteLevel n o)
    (x x' : Box p m)
    (hagree : ∀ c : Fin m, CA.levelOf c < siteLevel n o → x c = x' c) :
    CA.cellOf (embE o) x = CA.cellOf (embE o) x' := by
  apply CA.cell_local
  intro c hc
  exact hagree c (hlev ▸ hc)

/-- the (b)/(c) conflation exhibited (falsifier-only vocabulary,
`CapEnvelopeCellLocal` — Defs §2.9); witnesses at the Gates layer. -/
theorem capEnvelope_cellLocal_false :
    ∃ (T : TreeModel 2 (ZMod 2) 2 3 9 polTriv)
      (CA : CellData 2 (ZMod 2) 2 3 9 polTriv T),
      ¬ CapEnvelopeCellLocal T CA := by
  sorry

end LeanUrat.MovesT
