/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-! # Shared first-entrance calculus (carrier-generic)

The predicate-parametric first-entrance / ownership-partition layer of H8
((CUT-1)/(CUT-2)/(BDY)), hoisted carrier-generic.

PROVENANCE (SYNTHESIS_PASS3 F1 hoist, 2026-08-01): every definition and
theorem below is a VERBATIM MOVE of the corresponding declaration of
`Scaffold/HDischarge/H8/CutDefs.lean` / `CutFirst.lean` / `CutPartition.lean`
(same statement shape, same proof), with the carrier `MovesC.History p F`
abstracted to a `Carrier` class holding exactly what those proofs consume:

* a prefix relation (refl + trans),
* a ℕ-valued `size` that is monotone along prefixes and detects equality
  (the `history_ext` + `List.IsPrefix.eq_of_length` antisymmetry leg), and
* downward totality (`List.prefix_or_prefix_of_prefix`).

Deliberately NO node-list field: `DictIII.EHist` (the H6/H2/H9 instantiation
target at E = DecIrr ∨ DecHen) carries dressing fields on which a bare node
list is not injective, so the rank-ordered interface is the honest minimal
one.  The tree side is parametrized by an explicit finite, prefix-closed
chain set `(chains, hfin, hclosed)` in place of `VTree`'s fields; H8's
`VTree` versions re-derive by supplying `Tr.chains`/`Tr.hfin`/`Tr.hclosed`.

The three `Finset` layers (`minEnts`/`shallowReads`/`blockReads`) keep the
exact `by classical; exact _.filter _` elaboration shape of `CutDefs.lean`
so that H8's originals stay definitionally equal to these at the `History`
instance (their proofs are direct applications, no `Finset.ext` bridges). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanUrat.Scaffold.Shared.FirstEntrance

/-- The minimal carrier interface of the first-entrance calculus: a prefix
preorder with a ℕ-rank that is monotone, detects equality (antisymmetry),
and is total below any common upper bound (tree-likeness). -/
class Carrier (α : Type*) where
  /-- the prefix relation. -/
  IsPrefixOf : α → α → Prop
  /-- the ℕ-rank (`nodes.length` on history-like carriers). -/
  size : α → ℕ
  prefix_refl : ∀ a, IsPrefixOf a a
  prefix_trans : ∀ {a b c}, IsPrefixOf a b → IsPrefixOf b c → IsPrefixOf a c
  size_mono : ∀ {a b}, IsPrefixOf a b → size a ≤ size b
  /-- rank antisymmetry: a prefix of no smaller rank is the whole thing. -/
  eq_of_prefix_of_size_le : ∀ {a b}, IsPrefixOf a b → size b ≤ size a → a = b
  /-- downward totality: two prefixes of a common carrier element are comparable. -/
  prefix_total_of_prefix : ∀ {a b c}, IsPrefixOf a c → IsPrefixOf b c →
    IsPrefixOf a b ∨ IsPrefixOf b a

open Carrier

variable {α : Type*} [Carrier α]

/-! ## The cut vocabulary (CutDefs.lean, carrier-generic) -/

/-- Proper prefix (strict). -/
def ProperPrefix (H' H : α) : Prop := IsPrefixOf H' H ∧ H' ≠ H

/-- SHALLOW READ (the (BDY)-shifted ownership): no PROPER prefix of `H` is an
entrance — `H`'s own entering read is charged to the shallow layer. -/
def ShallowRead (E : α → Prop) (H : α) : Prop :=
  ∀ H', ProperPrefix H' H → ¬ E H'

/-- `ε` is THE FIRST ENTRANCE strictly above `H`. -/
def FirstEntAbove (E : α → Prop) (ε H : α) : Prop :=
  E ε ∧ ProperPrefix ε H ∧ ∀ H', E H' → ProperPrefix H' H → IsPrefixOf ε H'

/-! ## (CUT-1), the first-entrance calculus (CutFirst.lean, carrier-generic) -/

/-- Helper: a proper prefix has strictly smaller rank — `size_mono` sharpened
by rank antisymmetry. -/
lemma ProperPrefix.size_lt {H' H : α} (h : ProperPrefix H' H) :
    size H' < size H :=
  lt_of_le_of_ne (size_mono h.1)
    (fun heq => h.2 (eq_of_prefix_of_size_le h.1 heq.ge))

/-- (CUT-1) uniqueness: two first entrances above the same `H` mutually
prefix each other (each one's clause 3 applied to the other), hence agree. -/
theorem firstEntAbove_unique (E : α → Prop) {ε₁ ε₂ H : α}
    (h1 : FirstEntAbove E ε₁ H) (h2 : FirstEntAbove E ε₂ H) : ε₁ = ε₂ := by
  have h12 : IsPrefixOf ε₁ ε₂ := h1.2.2 ε₂ h2.1 h2.2.1
  have h21 : IsPrefixOf ε₂ ε₁ := h2.2.2 ε₁ h1.1 h1.2.1
  exact eq_of_prefix_of_size_le h12 (size_mono h21)

/-- (CUT-1) existence: a non-shallow read has a first entrance above it —
take the minimal-`size` entrance proper prefix (classical, via `Nat.sInf` on
the rank set; no decidability of `E`); downward totality + rank minimality
force it below every other entrance. -/
theorem firstEntAbove_exists (E : α → Prop) {H : α}
    (h : ¬ ShallowRead E H) : ∃ ε, FirstEntAbove E ε H := by
  classical
  have hex : ∃ H', ProperPrefix H' H ∧ E H' := by
    by_contra hno
    push Not at hno
    exact h hno
  obtain ⟨H₁, hpp₁, hE₁⟩ := hex
  set S : Set ℕ :=
    {n | ∃ H' : α, (E H' ∧ ProperPrefix H' H) ∧ size H' = n}
    with hSdef
  have hSne : S.Nonempty := ⟨size H₁, H₁, ⟨hE₁, hpp₁⟩, rfl⟩
  obtain ⟨H₀, ⟨hE₀, hpp₀⟩, hlen₀⟩ := Nat.sInf_mem hSne
  refine ⟨H₀, hE₀, hpp₀, ?_⟩
  intro H' hE' hpp'
  rcases prefix_total_of_prefix hpp₀.1 hpp'.1 with hc | hc
  · exact hc
  · -- `H' ≼ H₀`: minimality of `H₀`'s rank forces equality
    have hmem : size H' ∈ S := ⟨H', ⟨hE', hpp'⟩, rfl⟩
    have hge : sInf S ≤ size H' := Nat.sInf_le hmem
    have heq : H' = H₀ := eq_of_prefix_of_size_le hc (by omega)
    subst heq
    exact prefix_refl _

/-- (CUT-1) minimality (first entrances are shallow reads): an entrance
proper prefix `H''` of `ε` would be an entrance proper prefix of `H`
strictly smaller than `ε`, yet clause 3 puts `ε` below it — rank
contradiction. -/
theorem firstEntAbove_shallowRead (E : α → Prop) {ε H : α}
    (h : FirstEntAbove E ε H) : E ε ∧ ShallowRead E ε := by
  obtain ⟨hEε, hppε, hmin⟩ := h
  refine ⟨hEε, ?_⟩
  intro H'' hpp'' hE''
  have hlt1 : size H'' < size ε := hpp''.size_lt
  have hlt2 : size ε < size H := hppε.size_lt
  have hppH : ProperPrefix H'' H := by
    refine ⟨prefix_trans hpp''.1 hppε.1, ?_⟩
    intro hEq
    rw [hEq] at hlt1
    omega
  have hle : size ε ≤ size H'' := size_mono (hmin H'' hE'' hppH)
  omega

/-- (CUT-1) closure: the first entrance above a member of a prefix-closed
set is itself a member (`hclosed` at `H` with `ε ≼ H`). -/
theorem firstEntAbove_mem_chains {chains : Set α}
    (hclosed : ∀ H ∈ chains, ∀ ε, IsPrefixOf ε H → ε ∈ chains)
    (E : α → Prop) {ε H : α} (hH : H ∈ chains) (h : FirstEntAbove E ε H) :
    ε ∈ chains :=
  hclosed H hH ε h.2.1.1

/-! ## The ownership `Finset` layers (CutDefs.lean, carrier-generic) -/

variable {chains : Set α}

/-- MINIMAL (first) entrances of the chain set — the block roots of the
shallow cut. -/
noncomputable def minEnts (hfin : chains.Finite) (E : α → Prop) :
    Finset α := by
  classical
  exact hfin.toFinset.filter (fun ε => E ε ∧ ShallowRead E ε)

/-- The shallow-owned read sites. -/
noncomputable def shallowReads (hfin : chains.Finite) (E : α → Prop) :
    Finset α := by
  classical
  exact hfin.toFinset.filter (ShallowRead E)

/-- The block-`ε`-owned read sites. -/
noncomputable def blockReads (hfin : chains.Finite) (E : α → Prop)
    (ε : α) : Finset α := by
  classical
  exact hfin.toFinset.filter (FirstEntAbove E ε)

@[simp] lemma mem_minEnts {hfin : chains.Finite} {E : α → Prop}
    {ε : α} :
    ε ∈ minEnts hfin E ↔ ε ∈ chains ∧ E ε ∧ ShallowRead E ε := by
  classical
  simp [minEnts, Set.Finite.mem_toFinset]

@[simp] lemma mem_shallowReads {hfin : chains.Finite} {E : α → Prop}
    {H : α} :
    H ∈ shallowReads hfin E ↔ H ∈ chains ∧ ShallowRead E H := by
  classical
  simp [shallowReads, Set.Finite.mem_toFinset]

@[simp] lemma mem_blockReads {hfin : chains.Finite} {E : α → Prop}
    {ε H : α} :
    H ∈ blockReads hfin E ε ↔ H ∈ chains ∧ FirstEntAbove E ε H := by
  classical
  simp [blockReads, Set.Finite.mem_toFinset]

/-! ## (CUT-2) + (BDY), the ownership partition (CutPartition.lean, carrier-generic) -/

open Classical in
/-- (CUT-2) exhaustiveness: every read site of a finite prefix-closed chain
set is owned, shallow-side or by the block of some minimal entrance. -/
theorem read_cut_exhaustive (hfin : chains.Finite)
    (hclosed : ∀ H ∈ chains, ∀ ε, IsPrefixOf ε H → ε ∈ chains)
    (E : α → Prop) :
    hfin.toFinset
      = shallowReads hfin E ∪ (minEnts hfin E).biUnion (blockReads hfin E) := by
  ext H
  constructor
  · intro hH
    have hHc : H ∈ chains := hfin.mem_toFinset.mp hH
    by_cases hsh : ShallowRead E H
    · exact Finset.mem_union_left _ (mem_shallowReads.mpr ⟨hHc, hsh⟩)
    · obtain ⟨ε, hε⟩ := firstEntAbove_exists E hsh
      refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨ε, ?_, ?_⟩)
      · exact mem_minEnts.mpr
          ⟨firstEntAbove_mem_chains hclosed E hHc hε,
           (firstEntAbove_shallowRead E hε).1,
           (firstEntAbove_shallowRead E hε).2⟩
      · exact mem_blockReads.mpr ⟨hHc, hε⟩
  · intro hH
    rcases Finset.mem_union.mp hH with hs | hb
    · exact hfin.mem_toFinset.mpr (mem_shallowReads.mp hs).1
    · obtain ⟨ε, _, hHb⟩ := Finset.mem_biUnion.mp hb
      exact hfin.mem_toFinset.mpr (mem_blockReads.mp hHb).1

/-- (CUT-2) exclusivity, shallow half: a member of `blockReads ε` has the
entrance `ε` as a PROPER prefix (`FirstEntAbove` clause 2), refuting
`ShallowRead` — no read is charged both shallow-side and block-side.
(Holds without `hε`; the binder is the consumption shape.) -/
theorem shallow_block_disjoint (hfin : chains.Finite) (E : α → Prop)
    {ε : α} (hε : ε ∈ minEnts hfin E) :
    Disjoint (shallowReads hfin E) (blockReads hfin E ε) := by
  rw [Finset.disjoint_left]
  intro H hs hb
  exact (mem_shallowReads.mp hs).2 ε (mem_blockReads.mp hb).2.2.1
    (mem_blockReads.mp hb).2.1

/-- (CUT-2) exclusivity, block-block half: a read in two blocks would exhibit
two `FirstEntAbove` witnesses at the same `H`; uniqueness forces `ε₁ = ε₂` —
distinct blocks never overlap. -/
theorem block_block_disjoint (hfin : chains.Finite) (E : α → Prop)
    {ε₁ ε₂ : α} (h : ε₁ ≠ ε₂) :
    Disjoint (blockReads hfin E ε₁) (blockReads hfin E ε₂) := by
  rw [Finset.disjoint_left]
  intro H h1 h2
  exact h (firstEntAbove_unique E (mem_blockReads.mp h1).2
    (mem_blockReads.mp h2).2)

/-- (BDY) display — the node-vs-edge ownership shift as a THEOREM, not a
convention: a minimal entrance `ε` is `ShallowRead` by its `minEnts` filter
clause — its OWN entering read is charged shallow-side — while every member
of its block has `ε` STRICTLY above (`FirstEntAbove` clause 2). -/
theorem bdy_display (hfin : chains.Finite) (E : α → Prop)
    {ε : α} (hε : ε ∈ minEnts hfin E) :
    ε ∈ shallowReads hfin E ∧ ∀ H ∈ blockReads hfin E ε, ProperPrefix ε H := by
  obtain ⟨hc, _, hsh⟩ := mem_minEnts.mp hε
  exact ⟨mem_shallowReads.mpr ⟨hc, hsh⟩,
    fun H hH => (mem_blockReads.mp hH).2.2.1⟩

open Classical in
/-- The full ownership partition in one display — the union is exhaustive
(`read_cut_exhaustive`), the shallow layer misses every block
(`shallow_block_disjoint` lifted through `Finset.disjoint_biUnion_right`),
and the block family is pairwise disjoint (`block_block_disjoint`). -/
theorem read_cut_partition (hfin : chains.Finite)
    (hclosed : ∀ H ∈ chains, ∀ ε, IsPrefixOf ε H → ε ∈ chains)
    (E : α → Prop) :
    hfin.toFinset
        = shallowReads hfin E ∪ (minEnts hfin E).biUnion (blockReads hfin E)
      ∧ Disjoint (shallowReads hfin E) ((minEnts hfin E).biUnion (blockReads hfin E))
      ∧ ((minEnts hfin E) : Set α).PairwiseDisjoint (blockReads hfin E) := by
  refine ⟨read_cut_exhaustive hfin hclosed E, ?_, ?_⟩
  · exact Finset.disjoint_biUnion_right _ _ _ |>.mpr
      (fun ε hε => shallow_block_disjoint hfin E hε)
  · intro ε₁ h₁ ε₂ h₂ hne
    exact block_block_disjoint hfin E hne

end LeanUrat.Scaffold.Shared.FirstEntrance
