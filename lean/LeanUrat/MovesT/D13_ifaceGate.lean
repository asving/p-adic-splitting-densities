/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.D8_pathOrder

/-! # T-D13 `treeIface_carrier` [PARTIAL — §5 S-11] — pack carrier + order laws
(T-D8). HONEST SCOPE: `isEntrance`/`isDeepSplit`/`blockOf`/`entδ` are CTS/[1v]
vocabulary — MovesV's; the CARRIER CORE only. [E-DEV, MANIFEST: TNode := the ROOT
(`none`) + the family's chain carrier — "Node := chains+root" per the blueprint's own
sketch; a bare chain carrier cannot satisfy `path_refl` ∧ `finN` ∧ `node_ne`
simultaneously (empty-chain trees).] -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- the packed TreeIface CARRIER CORE: Tree := ↥𝒯, TNode := root + the family's
chain carrier, onPath := the prefix order (root below everything). -/
noncomputable def treeIfaceCore (𝒯 : Finset (VTree p F)) (h𝒯 : 𝒯.Nonempty) :
    TreeIfaceCore where
  Tree := {Tr // Tr ∈ 𝒯}
  TNode := Option {H : History p F // H ∈ ⋃ Tr ∈ 𝒯, VTree.chains Tr}
  onPath := fun _ o₁ o₂ =>
    match o₁, o₂ with
    | none, _ => True
    | some _, none => False
    | some H₁, some H₂ => H₁.1.IsPrefixOf H₂.1
  path_refl := by
    intro t ν
    cases ν with
    | none => trivial
    | some H => exact List.prefix_refl H.1.nodes
  path_trans := by
    intro t ν₁ ν₂ ν₃ h12 h23
    cases ν₁ with
    | none => trivial
    | some H₁ =>
      cases ν₂ with
      | none => exact absurd h12 (by simp)
      | some H₂ =>
        cases ν₃ with
        | none => exact absurd h23 (by simp)
        | some H₃ => exact List.IsPrefix.trans h12 h23
  path_antisymm := by
    intro t ν₁ ν₂ h12 h21
    cases ν₁ with
    | none =>
      cases ν₂ with
      | none => rfl
      | some H₂ => exact absurd h21 (by simp)
    | some H₁ =>
      cases ν₂ with
      | none => exact absurd h12 (by simp)
      | some H₂ =>
        congr 1
        exact Subtype.ext
          (history_ext (h12.eq_of_length (h12.length_le.antisymm h21.length_le)))
  finN := by
    intro t
    have hfin : (⋃ Tr ∈ 𝒯, VTree.chains Tr).Finite :=
      Set.Finite.biUnion 𝒯.finite_toSet (fun Tr _ => Tr.hfin)
    have h1 : Finite {H : History p F // H ∈ ⋃ Tr ∈ 𝒯, VTree.chains Tr} := hfin
    exact Subtype.finite
  node_ne := fun _ => ⟨none, trivial⟩

end LeanUrat.MovesT
