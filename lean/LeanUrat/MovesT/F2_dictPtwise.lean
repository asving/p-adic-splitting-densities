/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-F2 `preHalt_dict_ptwise` [hard] — THE DICTIONARY, RESTRICTED TO PRE-HALT MARKS
(MOVES 7590–7603): the class↔chain bijection with EVERY leg warranted (REV 3, Codex-2
#15: `hph`/`hsep` explicit premises, §0-rowed, owner HC-2). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem preHalt_dict_ptwise {P : Shape n} (S : Presented p F n N m pol P)
    (T : TreeModel p F n N m pol) (χ : Fin n → Fin m)
    (hcyl : D4R_CYL S T) (hwd : ClassFiberWelldef p F n N m pol P)
    (heta : EtaLoc T P) (hib : InBoxOfMem T n)
    (hph : PreHaltClassData (P := P) pol)
    (Tr : VTree p F) (x : Box p m) (hfib : Tr.fiberAt T χ x)
    (hsep : ∀ H H', H ∈ Tr.chains → H' ∈ Tr.chains →
      H ∈ PrefSet n pol P → H' ∈ PrefSet n pol P →
      (∃ i : PrefIdx n pol P, SameClass i H ∧ SameClass i H') → H = H') :
    Nat.card {i : PrefIdx n pol P //
        x ∈ S.fiber i ∧ PreHalt (reprOf i)}
      = Tr.chainCount n P := by
  sorry

end LeanUrat.MovesT
