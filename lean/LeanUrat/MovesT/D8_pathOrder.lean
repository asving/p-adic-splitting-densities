/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.F0_preHalt

/-! # T-D8 `vtree_pathOrder` — MovesS §W4-SYNC TreeIface's ROOT-PATH ORDER LAWS
(path_refl/trans/antisymm/total): `VTree` is a lawful TreeIface CARRIER;
entrance/deep-split/blockOf semantics stay MovesV/[1v] (§5 S-5). PROVED (E-phase
prove-now set). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem vtree_pathOrder (Tr : VTree p F) :
    (∀ H : History p F, H.IsPrefixOf H) ∧
    (∀ H₁ H₂ H₃ : History p F,
      H₁.IsPrefixOf H₂ → H₂.IsPrefixOf H₃ → H₁.IsPrefixOf H₃) ∧
    (∀ H₁ H₂ : History p F,
      H₁.IsPrefixOf H₂ → H₂.IsPrefixOf H₁ → H₁ = H₂) ∧
    (∀ H₁ H₂ H : History p F, H₁ ∈ Tr.chains → H₂ ∈ Tr.chains → H ∈ Tr.chains →
      H₁.IsPrefixOf H → H₂.IsPrefixOf H →
      (H₁.IsPrefixOf H₂ ∨ H₂.IsPrefixOf H₁)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro H
    exact List.prefix_refl H.nodes
  · intro H₁ H₂ H₃ h12 h23
    exact List.IsPrefix.trans h12 h23
  · intro H₁ H₂ h12 h21
    exact history_ext (h12.eq_of_length (h12.length_le.antisymm h21.length_le))
  · intro H₁ H₂ H _ _ _ h1 h2
    exact List.prefix_or_prefix_of_prefix h1 h2

end LeanUrat.MovesT
