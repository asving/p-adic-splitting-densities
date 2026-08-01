/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.D8_pathOrder
import LeanUrat.MovesT.F0_preHalt
import LeanUrat.MovesT.G1_toyGate
import LeanUrat.Scaffold.HDischarge.H8.CutDefs
import LeanUrat.Scaffold.HDischarge.H8.CutPartition

/-! # H8-G1 `ToyGate.lean` — the positive toy gate (Wave 2)

Blueprint `lean/blueprints/HDISCHARGE_H8.md` §3.6 + §4 Wave 2 + §5.  A concrete
3-chain `VTree 2 (ZMod 2)` (node stock REUSED from `MovesT/G1_toyGate.lean`:
`toyHead`/`toyLeafA`/`toyLeafB`, histories `tA1`/`tA2a`) with a one-entrance
predicate `toyE` pinned at the MIDDLE chain, and the explicit computation that

* `minEnts toyTr toyE = {toyEps}` (the marked entrance),
* `shallowReads toyTr toyE = {tA1, toyEps}` — the two shallow chains,
  INCLUDING the entrance itself: the (BDY) check that the entrance's own
  entering read is charged shallow-side,
* `blockReads toyTr toyE toyEps = {toy3}` — exactly the strictly-below chain,
* `read_cut_exhaustive` instantiates non-trivially (block side inhabited).

Guards (§3.6/§5): vacuously-true partition theorems (the tree has three
chains, `toy3.nodes.length = 3`), `E ≡ False` degeneracy (`toyE toyEps` holds
by `rfl`), and the (BDY) off-by-one (the gate FAILS if the entrance's own read
lands block-side: `toyEps ∈ shallowReads`, `toyEps ∉ blockReads _ _ toyEps`).
No sorried `G1_toyGate` declaration is consumed (node/history literals and
their species lemmas only).  Deps: H8-D0 (`CutDefs`), H8-A2 (`CutPartition`). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanUrat.Scaffold.HDischarge.H8

open LeanUrat.MovesC LeanUrat.MovesD LeanUrat.MovesT

/-! ## The toy data: a single 3-chain over the G1 node stock -/

/-- The ENTRANCE pin: the middle (length-2) chain `[toyHead, toyLeafA]`. -/
noncomputable def toyEps : History 2 (ZMod 2) := tA2a

/-- The deep (length-3) chain `[toyHead, toyLeafA, toyLeafB]` — the ≥ 3-chain
that makes the cut non-degenerate: it lies STRICTLY BELOW the entrance. -/
noncomputable def toy3 : History 2 (ZMod 2) := tA2a.snoc toyLeafB toyLeafB_nonroot

/-- The one-entrance predicate: exactly the middle chain enters. -/
def toyE : History 2 (ZMod 2) → Prop := fun H => H = toyEps

private lemma tA1_nodes' : tA1.nodes = [toyHead] := rfl
private lemma toyEps_nodes : toyEps.nodes = [toyHead, toyLeafA] := rfl
private lemma toy3_nodes : toy3.nodes = [toyHead, toyLeafA, toyLeafB] := rfl

/-! ## Distinctness / prefix bookkeeping (node-list level) -/

private lemma tA1_ne_toyEps : tA1 ≠ toyEps := fun h => by
  have h2 := congrArg History.nodes h
  rw [tA1_nodes', toyEps_nodes] at h2
  simp at h2

private lemma toyEps_ne_toy3 : toyEps ≠ toy3 := fun h => by
  have h2 := congrArg History.nodes h
  rw [toyEps_nodes, toy3_nodes] at h2
  simp at h2

private lemma toy3_ne_tA1 : toy3 ≠ tA1 := fun h => by
  have h2 := congrArg History.nodes h
  rw [toy3_nodes, tA1_nodes'] at h2
  simp at h2

private lemma toy3_ne_toyEps : toy3 ≠ toyEps := fun h => toyEps_ne_toy3 h.symm

private lemma tA1_pre_toy3 : tA1.IsPrefixOf toy3 :=
  show tA1.nodes <+: toy3.nodes from ⟨[toyLeafA, toyLeafB], rfl⟩

private lemma toyEps_pre_toy3 : toyEps.IsPrefixOf toy3 :=
  show toyEps.nodes <+: toy3.nodes from ⟨[toyLeafB], rfl⟩

private lemma not_toyEps_pre_tA1 : ¬ toyEps.IsPrefixOf tA1 := fun h => by
  have h2 := List.IsPrefix.length_le h
  rw [toyEps_nodes, tA1_nodes'] at h2
  simp at h2

private lemma not_toy3_pre_tA1 : ¬ toy3.IsPrefixOf tA1 := fun h => by
  have h2 := List.IsPrefix.length_le h
  rw [toy3_nodes, tA1_nodes'] at h2
  simp at h2

private lemma not_toy3_pre_toyEps : ¬ toy3.IsPrefixOf toyEps := fun h => by
  have h2 := List.IsPrefix.length_le h
  rw [toy3_nodes, toyEps_nodes] at h2
  simp at h2

/-- nonempty prefixes of a 1-list. -/
private lemma prefix_of_one {H' : History 2 (ZMod 2)} {a : Node 2 (ZMod 2)}
    (h : H'.nodes <+: [a]) : H'.nodes = [a] := by
  have hpos : 0 < H'.nodes.length := List.length_pos_iff.mpr H'.nonempty
  have hlen : H'.nodes.length ≤ 1 := by simpa using h.length_le
  have heq := List.prefix_iff_eq_take.mp h
  have h1 : H'.nodes.length = 1 := by omega
  rw [heq, h1]; rfl

/-- nonempty prefixes of a 2-list. -/
private lemma prefix_of_two {H' : History 2 (ZMod 2)} {a b : Node 2 (ZMod 2)}
    (h : H'.nodes <+: [a, b]) : H'.nodes = [a] ∨ H'.nodes = [a, b] := by
  have hpos : 0 < H'.nodes.length := List.length_pos_iff.mpr H'.nonempty
  have hlen : H'.nodes.length ≤ 2 := by simpa using h.length_le
  have heq := List.prefix_iff_eq_take.mp h
  have h12 : H'.nodes.length = 1 ∨ H'.nodes.length = 2 := by omega
  rcases h12 with h1 | h1
  · exact Or.inl (by rw [heq, h1]; rfl)
  · exact Or.inr (by rw [heq, h1]; rfl)

/-- nonempty prefixes of a 3-list. -/
private lemma prefix_of_three {H' : History 2 (ZMod 2)} {a b c : Node 2 (ZMod 2)}
    (h : H'.nodes <+: [a, b, c]) :
    H'.nodes = [a] ∨ H'.nodes = [a, b] ∨ H'.nodes = [a, b, c] := by
  have hpos : 0 < H'.nodes.length := List.length_pos_iff.mpr H'.nonempty
  have hlen : H'.nodes.length ≤ 3 := by simpa using h.length_le
  have heq := List.prefix_iff_eq_take.mp h
  have h123 : H'.nodes.length = 1 ∨ H'.nodes.length = 2 ∨ H'.nodes.length = 3 := by
    omega
  rcases h123 with h1 | h1 | h1
  · exact Or.inl (by rw [heq, h1]; rfl)
  · exact Or.inr (Or.inl (by rw [heq, h1]; rfl))
  · exact Or.inr (Or.inr (by rw [heq, h1]; rfl))

/-! ## The cut-vocabulary facts at the toy data -/

/-- The root chain is shallow: the only entrance is `toyEps`, never a proper
prefix of the SHORTER `tA1`. -/
private lemma shallow_tA1 : ShallowRead toyE tA1 := by
  intro H' hpp hE'
  have h : H' = toyEps := hE'
  subst h
  exact not_toyEps_pre_tA1 hpp.1

/-- (BDY) core: the entrance ITSELF is shallow — its only candidate entrance
proper-prefix would be itself, excluded by strictness. -/
private lemma shallow_toyEps : ShallowRead toyE toyEps := by
  intro H' hpp hE'
  have h : H' = toyEps := hE'
  subst h
  exact hpp.2 rfl

/-- The deep chain is NOT shallow: `toyEps` is an entrance proper prefix. -/
private lemma not_shallow_toy3 : ¬ ShallowRead toyE toy3 := fun hsh =>
  hsh toyEps ⟨toyEps_pre_toy3, toyEps_ne_toy3⟩ rfl

/-- `toyEps` is the first entrance strictly above the deep chain. -/
private lemma fea_toy3 : FirstEntAbove toyE toyEps toy3 := by
  refine ⟨rfl, ⟨toyEps_pre_toy3, toyEps_ne_toy3⟩, ?_⟩
  intro H' hE' _
  have h : H' = toyEps := hE'
  subst h
  show toyEps.nodes <+: toyEps.nodes
  exact List.prefix_refl _

/-! ## The toy tree: chains `{tA1, toyEps, toy3}`, one maximal 3-chain -/

/-- Leaf verdict for the single leaf `toy3`. -/
def vd0 : Vd :=
  ⟨{(1, 1)}, fun ef hef => by
    rw [Multiset.mem_singleton] at hef
    subst hef
    exact ⟨le_refl 1, le_refl 1⟩⟩

open Classical in
/-- The 3-chain toy tree: the single maximal chain `toy3` with its two
nonempty prefixes `tA1` (root) and `toyEps` (the entrance). -/
noncomputable def toyTr : VTree 2 (ZMod 2) where
  chains := {tA1, toyEps, toy3}
  hfin := ((Set.finite_singleton toy3).insert toyEps).insert tA1
  hne_nodes := fun H _ => H.nonempty
  hclosed := by
    intro H hH H' hpre hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hH ⊢
    rcases hH with rfl | rfl | rfl
    · exact Or.inl (history_ext
        ((prefix_of_one (show H'.nodes <+: [toyHead] from hpre)).trans tA1_nodes'.symm))
    · rcases prefix_of_two (show H'.nodes <+: [toyHead, toyLeafA] from hpre) with h | h
      · exact Or.inl (history_ext (h.trans tA1_nodes'.symm))
      · exact Or.inr (Or.inl (history_ext (h.trans toyEps_nodes.symm)))
    · rcases prefix_of_three
        (show H'.nodes <+: [toyHead, toyLeafA, toyLeafB] from hpre) with h | h | h
      · exact Or.inl (history_ext (h.trans tA1_nodes'.symm))
      · exact Or.inr (Or.inl (history_ext (h.trans toyEps_nodes.symm)))
      · exact Or.inr (Or.inr (history_ext (h.trans toy3_nodes.symm)))
  henV := ∅
  hhen := by simp
  leafV := fun H => if H = toy3 then some vd0 else none
  hleaf := by
    intro H
    constructor
    · intro hsome
      by_cases h3 : H = toy3
      · subst h3
        refine ⟨Or.inr (Or.inr rfl), ?_⟩
        intro H' hH' hpre
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hH'
        rcases hH' with rfl | rfl | rfl
        · exact absurd hpre not_toy3_pre_tA1
        · exact absurd hpre not_toy3_pre_toyEps
        · rfl
      · rw [if_neg h3] at hsome
        exact absurd hsome (by simp)
    · rintro ⟨hmem, hmax⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact absurd (hmax toy3 (Or.inr (Or.inr rfl)) tA1_pre_toy3) toy3_ne_tA1
      · exact absurd (hmax toy3 (Or.inr (Or.inr rfl)) toyEps_pre_toy3) toy3_ne_toyEps
      · rw [if_pos rfl]; rfl
  nsLeaf := fun _ => False
  hns_leaf := by simp

lemma toyTr_chains : toyTr.chains = {tA1, toyEps, toy3} := rfl

open Classical in
/-- The read-site carrier, computed: exactly the three chains. -/
theorem toy_toFinset : toyTr.hfin.toFinset = {tA1, toyEps, toy3} := by
  ext H
  rw [Set.Finite.mem_toFinset, toyTr_chains]
  simp

/-! ## The marked computations (§3.6): minEnts / shallowReads / blockReads -/

/-- `minEnts` comes out as MARKED: exactly the entrance. -/
theorem toy_minEnts : minEnts toyTr toyE = {toyEps} := by
  ext H
  rw [mem_minEnts, Finset.mem_singleton]
  constructor
  · rintro ⟨_, hE, _⟩
    exact hE
  · rintro rfl
    exact ⟨by simp [toyTr_chains], rfl, shallow_toyEps⟩

open Classical in
/-- `shallowReads` comes out as MARKED: the two shallow chains — the root AND
the entrance itself (the (BDY) shift), the deep chain excluded. -/
theorem toy_shallowReads : shallowReads toyTr toyE = {tA1, toyEps} := by
  ext H
  rw [mem_shallowReads, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hc, hsh⟩
    simp only [toyTr_chains, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hsh not_shallow_toy3
  · rintro (rfl | rfl)
    · exact ⟨by simp [toyTr_chains], shallow_tA1⟩
    · exact ⟨by simp [toyTr_chains], shallow_toyEps⟩

/-- `blockReads` at the entrance comes out as MARKED: exactly the
strictly-below chain — in particular the entrance's own read is NOT here. -/
theorem toy_blockReads : blockReads toyTr toyE toyEps = {toy3} := by
  ext H
  rw [mem_blockReads, Finset.mem_singleton]
  constructor
  · rintro ⟨hc, hfe⟩
    simp only [toyTr_chains, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl | rfl
    · exact absurd hfe.2.1.1 not_toyEps_pre_tA1
    · exact absurd rfl hfe.2.1.2
    · rfl
  · rintro rfl
    exact ⟨by simp [toyTr_chains], fea_toy3⟩

/-! ## The gate family (§3.6 falsifier channels; §4 Wave 2 required examples)

Non-vacuity displays: `E ≢ False`, a genuine ≥ 3-chain, the three computed
sets, the (BDY) check, and the non-trivial `read_cut_exhaustive` instance. -/

/-- `E ≢ False`: the entrance predicate genuinely fires. -/
example : toyE toyEps := rfl

/-- the ≥ 3-chain witness (no empty/degenerate chain set). -/
example : toy3.nodes.length = 3 := rfl

/-- the three chains are pairwise distinct (the tree is a genuine 3-chain). -/
example : tA1 ≠ toyEps ∧ toyEps ≠ toy3 ∧ tA1 ≠ toy3 :=
  ⟨tA1_ne_toyEps, toyEps_ne_toy3, fun h => toy3_ne_tA1 h.symm⟩

/-- `minEnts` as marked. -/
example : minEnts toyTr toyE = {toyEps} := toy_minEnts

open Classical in
/-- `shallowReads` as marked. -/
example : shallowReads toyTr toyE = {tA1, toyEps} := toy_shallowReads

/-- `blockReads` as marked. -/
example : blockReads toyTr toyE toyEps = {toy3} := toy_blockReads

open Classical in
/-- **(BDY)**: the entrance's OWN read lands shallow-side… -/
example : toyEps ∈ shallowReads toyTr toyE := by
  rw [toy_shallowReads]
  exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- …and NOT block-side (the G-2-adjacent off-by-one the gate would catch). -/
example : toyEps ∉ blockReads toyTr toyE toyEps := by
  rw [toy_blockReads, Finset.mem_singleton]
  exact toyEps_ne_toy3.symm ∘ Eq.symm

/-- the A2 (BDY) display theorem, instantiated at the toy entrance. -/
example :
    toyEps ∈ shallowReads toyTr toyE ∧
      ∀ H ∈ blockReads toyTr toyE toyEps, ProperPrefix toyEps H :=
  bdy_display toyTr toyE (by rw [toy_minEnts]; exact Finset.mem_singleton_self _)

open Classical in
/-- `read_cut_exhaustive` instantiates at the toy tree. -/
example :
    toyTr.hfin.toFinset
      = shallowReads toyTr toyE
          ∪ (minEnts toyTr toyE).biUnion (blockReads toyTr toyE) :=
  read_cut_exhaustive toyTr toyE

open Classical in
/-- …NON-trivially: the block side of the cut is inhabited (by the deep read),
so the partition theorem is exercised away from the empty/degenerate corner. -/
example : toy3 ∈ (minEnts toyTr toyE).biUnion (blockReads toyTr toyE) := by
  rw [Finset.mem_biUnion]
  exact ⟨toyEps, by rw [toy_minEnts]; exact Finset.mem_singleton_self _,
    by rw [toy_blockReads]; exact Finset.mem_singleton_self _⟩

open Classical in
/-- the fully computed cut display: carrier = the two shallow reads ∪ the
one-entrance block, every constituent evaluated. -/
theorem toy_cut_display :
    toyTr.hfin.toFinset
      = ({tA1, toyEps} : Finset (History 2 (ZMod 2)))
          ∪ ({toyEps} : Finset (History 2 (ZMod 2))).biUnion
              (blockReads toyTr toyE) := by
  rw [read_cut_exhaustive toyTr toyE, toy_shallowReads, toy_minEnts]

end LeanUrat.Scaffold.HDischarge.H8
