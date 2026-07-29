/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-F3 `preHalt_dict_sum` (MOVES 7601–7606): double count {(i, x)} both ways;
per-x the inner count is T-F2 at x's unique-up-to-ext tree (T-F1). `hsep` binds AFTER
𝒯 (REV 4, Fable-3 GAP-4). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem preHalt_dict_sum {P : Shape n} (S : Presented p F n N m pol P)
    (T : TreeModel p F n N m pol) (χ : Fin n → Fin m)
    (hcyl : D4R_CYL S T) (hwd : ClassFiberWelldef p F n N m pol P)
    (heta : EtaLoc T P) (hib : InBoxOfMem T n)
    (hph : PreHaltClassData (P := P) pol)
    (𝒯 : Finset (VTree p F))
    (hsep : ∀ Tr ∈ 𝒯, ∀ H H', H ∈ VTree.chains Tr → H' ∈ VTree.chains Tr →
      H ∈ PrefSet n pol P → H' ∈ PrefSet n pol P →
      (∃ i : PrefIdx n pol P, SameClass i H ∧ SameClass i H') → H = H')
    (hpart : PartitionsDecided 𝒯 T χ) :
    ∑ᶠ i : PrefIdx n pol P,
        Nat.card ↥{x | x ∈ S.fiber i ∧ PreHalt (reprOf i)}
      = ∑ Tr ∈ 𝒯, Tr.chainCount n P * Nat.card ↥{x | Tr.fiberAt T χ x} := by
  sorry

end LeanUrat.MovesT
