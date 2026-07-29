/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-E5 `fiber_root_split` [hard] — the ROOT CLAUSE (MOVES 7485–7495), exponent
t = numTracks (rev-2 arithmetic, census-verified). `RootSplitData`/`trackEvent` are
Defs carriers. `rootSplit_exists` (REV 4, Codex-3 #10) CONSTRUCTS the decomposition
from the tree's own structure — PROVED (E-phase prove-now set); only the shared
root-cell datum `hg` stays a hypothesis, owner-tagged. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

/-- the head partition, roster, injectivity, nonemptiness, and coverage all come from
the tree's OWN structure — group `Tr.chains` by head. -/
theorem rootSplit_exists (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (hreal : Realizes T χ Tr) (g : Fin n → ZMod p)
    (hg : ∀ x, Tr.fiberAt T χ x → x ∈ rootCell χ g) :
    Nonempty (RootSplitData Tr g) := by
  classical
  -- the set of head NODES of Tr's chains
  set Heads : Set (Node p F) := {ν | ∃ H ∈ Tr.chains, H.nodes.head? = some ν} with hHeads
  have hSomeIm : (Option.some '' Heads)
      ⊆ (fun H : History p F => H.nodes.head?) '' Tr.chains := by
    rintro y ⟨ν, ⟨H, hH, hhead⟩, rfl⟩
    exact ⟨H, hH, hhead⟩
  have hfinH : Heads.Finite := by
    have h1 : ((fun H : History p F => H.nodes.head?) '' Tr.chains).Finite :=
      Tr.hfin.image _
    have h2 : (Option.some '' Heads).Finite := h1.subset hSomeIm
    exact Set.Finite.of_finite_image h2 (fun a _ b _ h => Option.some.inj h)
  -- enumerate the heads
  let HFin := hfinH.toFinset
  let e := HFin.equivFin
  refine ⟨⟨HFin.card,
    fun i => {H | H ∈ Tr.chains ∧ H.nodes.head? = some ((e.symm i : { x // x ∈ HFin }) : Node p F)},
    ?_, fun i => ((e.symm i : { x // x ∈ HFin }) : Node p F), ?_, ?_, ?_, ?_⟩⟩
  · constructor
    · ext H
      constructor
      · intro hU
        obtain ⟨i, hHi⟩ := Set.mem_iUnion.mp hU
        exact hHi.1
      · intro hH
        have hne : H.nodes ≠ [] := H.nonempty
        have hhd : H.nodes.head? = some (H.nodes.head hne) := List.head?_eq_head hne
        have hmem : H.nodes.head hne ∈ Heads := ⟨H, hH, hhd⟩
        have hmemF : H.nodes.head hne ∈ HFin := hfinH.mem_toFinset.mpr hmem
        refine Set.mem_iUnion.mpr ⟨e ⟨_, hmemF⟩, hH, ?_⟩
        rw [Equiv.symm_apply_apply]
        exact hhd
    · intro i j hij
      rw [Function.onFun, Set.disjoint_left]
      rintro H ⟨_, hHi⟩ ⟨_, hHj⟩
      apply hij
      have hv : ((e.symm i : { x // x ∈ HFin }) : Node p F)
          = ((e.symm j : { x // x ∈ HFin }) : Node p F) := by
        have := hHi.symm.trans hHj
        exact Option.some.inj this
      have : e.symm i = e.symm j := Subtype.ext hv
      exact e.symm.injective this
  · intro i H hH
    exact hH.2
  · intro i j hij
    have : e.symm i = e.symm j := Subtype.ext hij
    exact e.symm.injective this
  · intro i
    have hmem : ((e.symm i : { x // x ∈ HFin }) : Node p F) ∈ Heads :=
      hfinH.mem_toFinset.mp (e.symm i).2
    obtain ⟨H, hH, hhd⟩ := hmem
    exact ⟨H, hH, hhd⟩
  · intro i
    have hmem : ((e.symm i : { x // x ∈ HFin }) : Node p F) ∈ Heads :=
      hfinH.mem_toFinset.mp (e.symm i).2
    obtain ⟨H, hH, hhd⟩ := hmem
    set ν := ((e.symm i : { x // x ∈ HFin }) : Node p F) with hν
    -- the head node has root species (History.root_iff at index 0)
    have hne : H.nodes ≠ [] := H.nonempty
    have hlen : 0 < H.nodes.length := List.length_pos_iff.mpr hne
    have hhead : H.nodes[0]'hlen = ν := by
      have := List.head?_eq_head hne
      rw [this] at hhd
      have hv : H.nodes.head hne = ν := Option.some.inj hhd
      rw [← hv]
      exact (List.getElem_zero_eq_head hlen)
    have hroot : ν.species = ReadSpecies.root := by
      have := (H.root_iff 0 hlen).mpr rfl
      rwa [hhead] at this
    refine ⟨hroot, ?_⟩
    -- oneNode ν hroot is a nonempty prefix of H, hence a chain by hclosed
    apply Tr.hclosed H hH
    · show (oneNode ν hroot).nodes <+: H.nodes
      have h1 : (oneNode ν hroot).nodes = [ν] := rfl
      rw [h1]
      cases hn : H.nodes with
      | nil => exact absurd hn hne
      | cons a l =>
        have : a = ν := by
          have := hhead
          simp only [hn] at this
          simpa using this
        rw [this]
        exact ⟨l, rfl⟩
    · simp [oneNode, childHist]

theorem fiber_root_split (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (trackOf : Node p F → Polynomial (ZMod p))
    (CA : CellAssign p F n N m pol T χ trackOf)
    (hχ : Function.Injective χ) (hrc : RootCellsOf T CA.toCellData χ)
    (hred : RedCellPartition T CA.toCellData χ trackOf)
    (hsib : SibCount T CA.toCellData χ) (hreal : Realizes T χ Tr)
    (g : Fin n → ZMod p) (htracks : RootSplitData Tr g)
    (hcr : ∀ i, ChildRoot none (htracks.headOf i))
    (hfib : ∀ x, Tr.fiberAt T χ x → x ∈ rootCell χ g) :
    Nat.card ↥{x | Tr.fiberAt T χ x}
        * (Nat.card ↥(rootCell χ g)) ^ htracks.t * p ^ n
      = p ^ m * ∏ i : Fin htracks.t,
          Nat.card ↥(rootCell χ g ∩ trackEvent Tr T htracks i (hcr i)) := by
  sorry

end LeanUrat.MovesT
