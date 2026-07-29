/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-C8 `ns_tree_bound` (MOVES 7240–7247): fiberAt's leaf clause at an ns leaf H
gives NsHalts at every fiber member. NEVER a raw-count claim (§0 refutation record) —
the normalized corollary is T-C7's domination, consumed at T-E12. PROVED (E-phase
prove-now set). -/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem ns_tree_bound (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (H : History p F) (hns : H ∈ Tr.chains ∧ Tr.nsLeaf H) :
    {x | Tr.fiberAt T χ x} ⊆ nsClass T H := by
  intro x hx
  obtain ⟨hchain, hmax⟩ := Tr.hns_leaf H hns.2
  rcases hx.2.1 H hchain hmax with ⟨_, hnotns, _⟩ | ⟨hnsh, _, _, _⟩
  · exact absurd hns.2 hnotns
  · exact hnsh

end LeanUrat.MovesT
