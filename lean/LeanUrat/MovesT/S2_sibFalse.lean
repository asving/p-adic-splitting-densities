/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.G1_toyGate

/-! # T-S2 `sib_falsifier` — the doctrine gate: (SIB) is a CONTENTFUL law (MOVES
7397–7400); a toy model with two children whose continuation events are IDENTICAL
fails the product AT THE CELL EVENT. Gate architecture (REV 2, Fable GAP-6): finite
surrogate + hand bridge. [E-DEV, recorded: the blueprint's display reuses the name
`toyχ` at box size 2; the T-G1 chart `toyχ : Fin 2 → Fin 9` has box size 9, so THIS
unit's chart is the size-2 identity chart `toyχ2` below — same values on `Fin 2`.] -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.openClassical false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD
open Classical

/-- the size-2 toy chart of this unit's falsifier (identity embedding). -/
def toyχ2 : Fin 2 → Fin 2 := id

/-! ### the two IDENTICAL-continuation root children of the falsifier -/

/-- the second root child — `toyHead` with a distinct `center`; ALL law-relevant fields
(σ/e/h/line/Dwidth/gam/ustar/s0/wSide/lift/zbar/ψ) shared, so its one-node history obeys
the same coherence/canonicity laws, but `center := 0 ≠ 1` makes it a distinct node. -/
noncomputable def sibNode2 : Node 2 (ZMod 2) :=
  { toyHead with
    center := (0 : ↥toyHead.σ.K)
    hspecRecCenter := by
      intro h
      rw [show toyHead.species = ReadSpecies.root from rfl] at h
      exact absurd h (by decide) }

lemma sibNode2_species : sibNode2.species = ReadSpecies.root := rfl
lemma sibNode2_root : ChildRoot none sibNode2 := sibNode2_species

lemma toyHead_ne_sibNode2 : toyHead ≠ sibNode2 := by
  intro h
  have hc := congrArg (fun n : Node 2 (ZMod 2) => n.σ.K.subtype n.center) h
  simp only [show sibNode2.center = (0 : ↥sibNode2.σ.K) from rfl,
    show toyHead.center = (1 : ↥toyHead.σ.K) from rfl, map_zero, map_one] at hc
  exact one_ne_zero hc

/-- the two length-1 root histories. `t1 = tA1` (G1's). -/
noncomputable def t1 : History 2 (ZMod 2) := oneNode toyHead toyHead_root
noncomputable def t2 : History 2 (ZMod 2) := oneNode sibNode2 sibNode2_root

private lemma histext {H H' : History 2 (ZMod 2)} (h : H.nodes = H'.nodes) : H = H' := by
  obtain ⟨n1, _, _⟩ := H; obtain ⟨n2, _, _⟩ := H'; cases h; rfl

lemma t1_nodes : t1.nodes = [toyHead] := rfl
lemma t2_nodes : t2.nodes = [sibNode2] := rfl

lemma t1_ne_t2 : t1 ≠ t2 := by
  intro h
  have : ([toyHead] : List (Node 2 (ZMod 2))) = [sibNode2] := by
    rw [← t1_nodes, ← t2_nodes, h]
  exact toyHead_ne_sibNode2 (by simpa using this)

/-! ### length-1 lawfulness (the `mem_realizable` obligation) -/

/-- `canonRoot` of the root children is their recorded `zbar = 1`: `ψ = X - C 1` has the
single residue root `1`, so the classical enumeration cancels on the singleton. -/
lemma canonRoot_toyHead : canonRoot toyHead = ((toyHead.zbar : (ZMod 2)ˣ) : ZMod 2) := by
  have hψ : ψImage toyHead = (X - C 1 : Polynomial (ZMod 2)) := by
    show (toyHead.ψ).map toyHead.σ.K.subtype = _
    rw [show toyHead.ψ = (X - C (1 : ↥toyHead.σ.K)) from rfl,
        Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_one]
  have hz : ((toyHead.zbar : (ZMod 2)ˣ) : ZMod 2) = 1 := rfl
  rw [hz]
  unfold canonRoot
  rw [hψ, Polynomial.roots_X_sub_C]
  simp only [Multiset.toFinset_singleton, Finset.image_singleton, Finset.min_singleton]
  exact Equiv.symm_apply_apply _ _

lemma canonRoot_sibNode2 : canonRoot sibNode2 = ((sibNode2.zbar : (ZMod 2)ˣ) : ZMod 2) := by
  have e1 : canonRoot sibNode2 = canonRoot toyHead := by unfold canonRoot ψImage; rfl
  rw [e1]; exact canonRoot_toyHead

lemma laws_t1 : HistoryCoherent t1 ∧ Realizable t1 ∧ polTriv.IsCanonPres t1 := by
  have hn : t1.nodes = [toyHead] := t1_nodes
  have hsf : t1.strFrame 0 = 1 := by simp [History.strFrame]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro hj
    simp only [hn, List.getElem_cons_zero]
    rw [show toyHead.σ.Φ = (X : Polynomial ℤ_[2]) from rfl, Polynomial.natDegree_X]
  · intro i hi
    obtain rfl : i = 0 := by have h := hi; rw [hn] at h; simpa using h
    simp only [hn, List.getElem_cons_zero]
    show toyHead.line.slope * ((toyHead.e : ℚ) * (t1.strFrame 0 : ℚ) * (toyHead.Dwidth : ℚ))
      = (toyHead.h : ℚ)
    rw [hsf]
    norm_num [show toyHead.line.slope = (1 : ℚ) from rfl, show toyHead.e = 1 from rfl,
      show toyHead.Dwidth = 1 from rfl, show toyHead.h = 1 from rfl]
  · intro i hi
    obtain rfl : i = 0 := by have h := hi; rw [hn] at h; simpa using h
    simp only [hn, List.getElem_cons_zero]
    show ((toyHead.gam : ℤ) : ℚ)
      = (toyHead.e : ℚ) * ((t1.strFrame 0 : ℚ) * toyHead.ustar)
        + (((toyHead.s0 + toyHead.wSide : ℕ)) : ℚ) * (toyHead.h : ℚ)
    rw [hsf]
    norm_num [show toyHead.gam = 3 from rfl, show toyHead.e = 1 from rfl,
      show toyHead.ustar = (1 : ℚ) from rfl, show toyHead.s0 = 0 from rfl,
      show toyHead.wSide = 2 from rfl, show toyHead.h = 1 from rfl]
  · intro i hi
    exfalso; rw [hn] at hi; simp only [List.length_cons, List.length_nil] at hi; omega
  · intro i hi
    exfalso; rw [hn] at hi; simp only [List.length_cons, List.length_nil] at hi; omega
  · intro r hr
    obtain rfl : r = 0 := by have h := hr; rw [hn] at h; simpa using h
    simp only [hn, List.getElem_cons_zero]
    rfl
  · intro r hr
    obtain rfl : r = 0 := by have h := hr; rw [hn] at h; simpa using h
    simp only [hn, List.getElem_cons_zero]
    exact canonRoot_toyHead.symm

lemma laws_t2 : HistoryCoherent t2 ∧ Realizable t2 ∧ polTriv.IsCanonPres t2 := by
  have hn : t2.nodes = [sibNode2] := t2_nodes
  have hsf : t2.strFrame 0 = 1 := by simp [History.strFrame]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro hj
    simp only [hn, List.getElem_cons_zero]
    rw [show sibNode2.σ.Φ = (X : Polynomial ℤ_[2]) from rfl, Polynomial.natDegree_X]
  · intro i hi
    obtain rfl : i = 0 := by have h := hi; rw [hn] at h; simpa using h
    simp only [hn, List.getElem_cons_zero]
    show sibNode2.line.slope * ((sibNode2.e : ℚ) * (t2.strFrame 0 : ℚ) * (sibNode2.Dwidth : ℚ))
      = (sibNode2.h : ℚ)
    rw [hsf]
    norm_num [show sibNode2.line.slope = (1 : ℚ) from rfl, show sibNode2.e = 1 from rfl,
      show sibNode2.Dwidth = 1 from rfl, show sibNode2.h = 1 from rfl]
  · intro i hi
    obtain rfl : i = 0 := by have h := hi; rw [hn] at h; simpa using h
    simp only [hn, List.getElem_cons_zero]
    show ((sibNode2.gam : ℤ) : ℚ)
      = (sibNode2.e : ℚ) * ((t2.strFrame 0 : ℚ) * sibNode2.ustar)
        + (((sibNode2.s0 + sibNode2.wSide : ℕ)) : ℚ) * (sibNode2.h : ℚ)
    rw [hsf]
    norm_num [show sibNode2.gam = 3 from rfl, show sibNode2.e = 1 from rfl,
      show sibNode2.ustar = (1 : ℚ) from rfl, show sibNode2.s0 = 0 from rfl,
      show sibNode2.wSide = 2 from rfl, show sibNode2.h = 1 from rfl]
  · intro i hi
    exfalso; rw [hn] at hi; simp only [List.length_cons, List.length_nil] at hi; omega
  · intro i hi
    exfalso; rw [hn] at hi; simp only [List.length_cons, List.length_nil] at hi; omega
  · intro r hr
    obtain rfl : r = 0 := by have h := hr; rw [hn] at h; simpa using h
    simp only [hn, List.getElem_cons_zero]
    rfl
  · intro r hr
    obtain rfl : r = 0 := by have h := hr; rw [hn] at h; simpa using h
    simp only [hn, List.getElem_cons_zero]
    exact canonRoot_sibNode2.symm

/-! ### the falsifier's tree model + cell data -/

/-- the toy membership: `none` universal; single root histories `t1`/`t2` present exactly
on the `x 0 = 0` slice; no deeper history is ever a member. -/
def sibMem : Option (History 2 (ZMod 2)) → Box 2 2 → Prop
  | none, _ => True
  | some H, x => (H = t1 ∨ H = t2) ∧ x 0 = 0

/-- the toy child relation: the two root children on the `x 0 = 0` slice; no window children. -/
def sibChild : Option (History 2 (ZMod 2)) → Node 2 (ZMod 2) → Box 2 2 → Prop
  | none, ν, x => (ν = toyHead ∨ ν = sibNode2) ∧ x 0 = 0
  | some _, _, _ => False

noncomputable def sibModel : TreeModel 2 (ZMod 2) 2 1 2 polTriv where
  mem := sibMem
  child := sibChild
  root_mem := fun _ => trivial
  mem_single := by
    intro ν h1 x
    have key1 : (⟨[ν], h1.1, h1.2⟩ : History 2 (ZMod 2)) = t1 ↔ ν = toyHead := by
      constructor
      · intro h; have := congrArg History.nodes h
        rw [t1_nodes] at this; simpa using this
      · intro h; subst h; exact histext rfl
    have key2 : (⟨[ν], h1.1, h1.2⟩ : History 2 (ZMod 2)) = t2 ↔ ν = sibNode2 := by
      constructor
      · intro h; have := congrArg History.nodes h
        rw [t2_nodes] at this; simpa using this
      · intro h; subst h; exact histext rfl
    show sibMem (some _) x ↔ sibChild none ν x
    simp only [sibMem, sibChild, key1, key2]
  mem_snoc := by
    intro H ν hν x
    show sibMem (some (H.snoc ν hν)) x ↔ (sibMem (some H) x ∧ sibChild (some H) ν x)
    have hlen : (H.snoc ν hν).nodes.length = H.nodes.length + 1 := by
      simp [History.snoc]
    have hpos : 0 < H.nodes.length := List.length_pos_of_ne_nil H.nonempty
    have hne1 : H.snoc ν hν ≠ t1 := by
      intro h; have hl := congrArg (fun K : History 2 (ZMod 2) => K.nodes.length) h
      simp only [hlen, t1_nodes, List.length_cons, List.length_nil] at hl; omega
    have hne2 : H.snoc ν hν ≠ t2 := by
      intro h; have hl := congrArg (fun K : History 2 (ZMod 2) => K.nodes.length) h
      simp only [hlen, t2_nodes, List.length_cons, List.length_nil] at hl; omega
    simp only [sibMem, sibChild, hne1, hne2, or_self, false_and, and_false, iff_self]
  mem_realizable := by
    intro H x hmem
    rcases hmem with ⟨hH | hH, -⟩
    · rw [hH]; exact laws_t1
    · rw [hH]; exact laws_t2

/-- the toy cell alphabet: `true` is the branching cell (both children); `false` is empty.
[RATIFICATION REPAIR 2026-07-31 (verdict §8.1: "`sibCA : CellData ...` ends after
`child_cell_red` and does not provide the newly mandatory `child_red_uniform` field.
On the supplied source, that structure literal cannot elaborate."): the `.red` row is
REFINED to read the `x 0` digit — the ADJ-SPINE-1 genre (G1's `.junk2` refinement):
a CONSTANT `.red` row cannot satisfy `child_red_uniform` against the `x 0 = 0`-gated
root-child relation. `true` on the child-carrying slice, `false` off it; the `.red`
branch set stays honest through `child_cell_red` (roster realized on the slice). -/
noncomputable def sibCellOf : EntSt 2 (ZMod 2) 2 → Box 2 2 → Bool
  | .amb, _ => true
  | .red _ _, x => decide (x 0 = 0)
  | .st _, _ => false

noncomputable def sibBranch : Bool → Finset (Node 2 (ZMod 2))
  | true => {toyHead, sibNode2}
  | false => ∅

noncomputable def sibCA : CellData 2 (ZMod 2) 2 1 2 polTriv sibModel where
  Cell := Bool
  hCellFin := inferInstance
  cellOf := sibCellOf
  cellLevel := fun _ => 1
  levelOf := fun _ => 0
  cell_local := by
    intro es x x' h
    have hx : x = x' := funext fun c => h c (by norm_num)
    rw [hx]
  branchSetOf := sibBranch
  child_cell := by
    intro H ν x hmem
    show sibChild (some H) ν x ↔ ν ∈ sibBranch (sibCellOf (.st H) x)
    simp only [sibChild, sibCellOf, sibBranch, Finset.notMem_empty]
  child_root_sub := by
    intro ν x hchild
    have h : (ν = toyHead ∨ ν = sibNode2) ∧ x 0 = 0 := hchild
    show ν ∈ sibBranch (sibCellOf .amb x)
    simp only [sibCellOf, sibBranch, Finset.mem_insert, Finset.mem_singleton]
    exact h.1
  child_cell_red := by
    intro χ g ψ ν x hx hν
    show (ν = toyHead ∨ ν = sibNode2) ∧ x 0 = 0
    by_cases h0 : x 0 = 0
    · refine ⟨?_, h0⟩
      rw [show sibCellOf (.red g ψ) x = true from by
        simp [sibCellOf, h0]] at hν
      simpa [sibBranch] using hν
    · rw [show sibCellOf (.red g ψ) x = false from by
        simp [sibCellOf, h0]] at hν
      exact absurd hν (by simp [sibBranch])
  child_red_uniform := by
    -- [RATIFICATION REPAIR 2026-07-31, the mandatory ADJ-SPINE-1 field: the `.red`
    --  table reads exactly the `x 0` digit, so the child-none region {x 0 = 0} is a
    --  union of `cellOf (.red g ψ)` fibers — child behavior transports.]
    intro g ψ x y hcell ν
    have hkey : (x 0 = 0) ↔ (y 0 = 0) := by
      by_cases hx0 : x 0 = 0 <;> by_cases hy0 : y 0 = 0 <;>
        simp only [sibCellOf, hx0, hy0, decide_true, decide_false] at hcell ⊢ <;>
        tauto
    show (ν = toyHead ∨ ν = sibNode2) ∧ x 0 = 0 ↔
      (ν = toyHead ∨ ν = sibNode2) ∧ y 0 = 0
    rw [hkey]
  -- [T RE-RATIFICATION 2026-08-01, the site-entrance keying: the falsifier's
  --  member-keyed site read is the degenerate diagonal (this unit's gate lives on
  --  the global `SibCount`, which is `cellOf`-keyed and untouched).]
  branchCellOf := fun es _ν => sibCellOf es
  branch_cell_joint := fun _es _ν _x _y h => h

/-! ### the identical continuation events -/

/-- the shared continuation event: `{x | x 0 = 1}` is the (SIB) count-face `S_j` of BOTH
root children — realized via `ContFiber` with the empty prescribed subtree (`Tsub = ∅`). -/
lemma contfib_set (ν : Node 2 (ZMod 2)) (hr : ChildRoot none ν)
    (hself : ∀ x : Box 2 2, x 0 = 0 → sibModel.mem (some (childHist none ν hr)) x) :
    ({x | x 0 = 1} : Set (Box 2 2))
      = {x | ContFiber sibModel none ν hr (∅ : Set (History 2 (ZMod 2)))
          (fun _ => none) (fun _ => False) x} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hx1
    refine ⟨fun H' => ?_, ?_, ?_⟩
    · simp only [Set.mem_empty_iff_false, false_iff, not_and]
      intro _ hmemH'
      exfalso
      have hx0 : x 0 = 0 := hmemH'.2
      rw [hx1] at hx0
      exact (by decide : (1 : ZMod 2) ≠ 0) hx0
    · intro H' hH'; exact absurd hH' (by simp)
    · intro H' hH'; exact absurd hH' (by simp)
  · intro hcf
    by_contra hx
    have hx0 : x 0 = 0 := by
      have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
      rcases hcases (x 0) with h | h
      · exact h
      · exact absurd h hx
    have hmemself := hself x hx0
    have hcontra := (hcf.1 (childHist none ν hr)).mpr
      ⟨List.prefix_refl _, hmemself, fun H'' hp1 hp2 h3 =>
        absurd (histext ((hp1.sublist.antisymm hp2.sublist))).symm h3⟩
    simp at hcontra

/-! ### the gate -/

theorem sib_falsifier : ∃ (T : TreeModel 2 (ZMod 2) 2 1 2 polTriv)
    (CA : CellData 2 (ZMod 2) 2 1 2 polTriv T), ¬ SibCount T CA toyχ2 := by
  refine ⟨sibModel, sibCA, ?_⟩
  intro hsib
  -- the shared continuation event S ≡ {x | x 0 = 1}
  have hbranch : sibCA.branchSetOf (true : Bool) = {toyHead, sibNode2} := rfl
  have hcard : 2 ≤ (sibCA.branchSetOf (true : Bool)).card := by
    rw [hbranch, Finset.card_pair toyHead_ne_sibNode2]
  -- the S-clause (inlined so SibCount's implicits drive elaboration)
  have key := hsib .amb (true : Bool) (fun _ => {x : Box 2 2 | x 0 = 1}) hcard (by
    intro ν hν
    rw [hbranch, Finset.mem_insert, Finset.mem_singleton] at hν
    refine Or.inl ?_
    rcases hν with h | h
    · subst h
      exact ⟨toyHead_root, ∅, (fun _ => none), (fun _ => False), Set.finite_empty,
        contfib_set toyHead toyHead_root (fun x hx0 => ⟨Or.inl rfl, hx0⟩)⟩
    · subst h
      exact ⟨sibNode2_root, ∅, (fun _ => none), (fun _ => False), Set.finite_empty,
        contfib_set sibNode2 sibNode2_root (fun x hx0 => ⟨Or.inr rfl, hx0⟩)⟩)
  -- the cell event is the full box
  have hcE : cellEventE sibModel sibCA toyχ2 .amb (true : Bool) = (Set.univ : Set (Box 2 2)) := by
    ext x
    exact ⟨fun _ => Set.mem_univ x, fun _ => ⟨Set.mem_univ x, rfl⟩⟩
  have hInterS : (⋂ ν ∈ ({toyHead, sibNode2} : Finset (Node 2 (ZMod 2))),
      (fun _ => {x : Box 2 2 | x 0 = 1}) ν) = ({x | x 0 = 1} : Set (Box 2 2)) := by
    apply Set.eq_of_subset_of_subset
    · intro x hx
      exact Set.mem_iInter₂.mp hx toyHead (Finset.mem_insert_self _ _)
    · intro x hx
      exact Set.mem_iInter₂.mpr (fun ν _ => hx)
  -- cardinalities
  have card_univ : Nat.card ↥(Set.univ : Set (Box 2 2)) = 4 := by
    rw [Nat.card_eq_fintype_card]; decide
  have card_half : Nat.card ↥({x : Box 2 2 | x 0 = 1}) = 2 := by
    rw [Nat.card_eq_fintype_card]; decide
  rw [hbranch, Finset.prod_pair toyHead_ne_sibNode2, Finset.card_pair toyHead_ne_sibNode2,
    hInterS, hcE] at key
  simp only [Set.univ_inter, card_half, card_univ] at key
  norm_num at key

end LeanUrat.MovesT
