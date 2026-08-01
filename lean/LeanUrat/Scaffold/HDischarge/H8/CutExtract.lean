/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.Scaffold.HDischarge.H8.CutDefs
import LeanUrat.Scaffold.HDischarge.H8.CutFirst
import LeanUrat.Scaffold.HDischarge.H8.CutPartition

/-! # H8-B3 `CutExtract.lean` — the EXTRACTION layer = (K-CUT-1) level (1b)
[NEW at review findings C-1/C-2/C-5]

Constructs, as FUNCTIONS of `(Tr, E)`: the full-data shallow-layer object
`Ŝ(Tr)` (`shallowDataOf`), the per-block derivation objects `D_ε(Tr)`
(`blockDerivOf`), the cut map (`cutOf`), its injectivity up to the corpus tree
equality (`cut_injective` — `VTree.ext`, the (chains, henV, leafV, nsLeaf)
tuple), the interface/verdict conformance clauses (`cut_keying`,
`blockDerivOf_below`, `blockReads_eq_cone`/`blockDerivOf_cone`,
`haltsOf_leafLaw`/`nsOf_leafLaw`, `typemult_cut`), and the countability
transport for the family (`cutFamily_countable`).  NO verbatim statement was
pinned in the blueprint (`lean/blueprints/HDISCHARGE_H8.md` §4 Wave 2, H8-B3);
this file IS the unit's own E-phase, per the compile-probe rule.

## THE (a)/(b) DESIGN-GATE RECORD (reported upward, not silently picked)

* **(a) subtree-as-subset — CHOSEN.**  Block derivations are ambient-coordinate
  chain sets with inherited halt data (`BlockDeriv`: the head `ε` + the
  `blockReads`-filtered layer); the shallow layer is the `shallowReads` chain
  set with halt data + the entrance list + the retained hen payload
  (`ShallowData`).  The cut map is filter packaging — choice-free by
  construction — and injectivity is proved from `read_cut_exhaustive` + halt
  data recovery (`cut_injective`).  The blueprint's literal cone object
  `{H ∈ Tr.chains // ε.IsPrefixOf H}` is landed as a THEOREM
  (`blockDerivOf_cone`: head-insert of the block layer = the ε-cone filter),
  not as the raw carrier — the strict/non-strict split is exactly the (BDY)
  ownership shift, kept exact by carrying halt data on `blockReads` (strict)
  while `ε` heads the block as its state index.
* **(b) re-rooted VTree — BLOCKED.**  Dropping `ε`'s prefix from a cone chain
  `H` (`nodes := H.nodes.drop ε.nodes.length`) can NEVER satisfy `History`'s
  `root_iff` invariant: the dropped list's head is `H.nodes[ε.nodes.length]`,
  whose species is NOT `root` (by `H.root_iff`, since `ε.nodes.length ≠ 0` —
  `ε` is nonempty), while `root_iff` DEMANDS species `root` at index 0.  The
  obstruction is COMPILED below as `reroot_blocked` — it is definitive (holds
  for EVERY proper extension of EVERY entrance), not merely "may be false";
  repairing it would require fabricating a root node absent from `Tr` (species
  surgery), i.e. data not a function of `(Tr, E)`.  REL.2's transport reading
  therefore moves wholly into the (K-CUT-m)/(K-CUT-g) typed re-keys, as the
  blueprint's design-(a) cost note anticipated.

## Countability honesty note (deviation from the blueprint parenthetical)

The blueprint sketched countability "from `hfin` + the countable History
carrier".  The premise is FALSE at the raw-type level: `Node` carries
`lift : Polynomial ℤ_[p]` (uncountable coefficients) and `pat : ℕ → ↥σ.K`
(an unconstrained function field), so `History p F` and hence the carrier
types here are NOT countable as bare types, and no `Countable` instance is
derivable.  What IS true and landed: (i) each tree's block family is FINITE
(`blockFam` is a `Finset`, from `hfin`); (ii) countability TRANSPORTS along
the cut — the cut image of any countable tree family is countable
(`cutFamily_countable`).  The M04 consumer's "countable shape family" is the
image of the REALIZED tree family, so its countability rides the countability
of realizable trees — (K-CUT-g)/(K-CUT-s) seam territory, priced there, never
a type-level fact here.  Deps: H8-D0, H8-A1, H8-A2. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanUrat.Scaffold.HDischarge.H8

open LeanUrat.MovesC LeanUrat.MovesD LeanUrat.MovesT

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ## The design-(b) obstruction (compiled gate record) -/

/-- **DESIGN (b) IS BLOCKED**: for any proper extension `H` of any history `ε`,
the re-rooted node list `H.nodes.drop ε.nodes.length` has a head of NON-root
species — so it can never be repackaged as a `History` (whose `root_iff`
demands species `root` exactly at index 0).  The head is
`H.nodes[ε.nodes.length]`; by `H.root_iff` its species is `root` iff
`ε.nodes.length = 0`, refuted by `ε.nonempty`. -/
theorem reroot_blocked {ε H : History p F} (hpp : ProperPrefix ε H) :
    ∃ hj : ε.nodes.length < H.nodes.length,
      (H.nodes[ε.nodes.length]'hj).species ≠ ReadSpecies.root := by
  refine ⟨hpp.length_lt, fun hroot => ?_⟩
  have h0 : ε.nodes.length = 0 := (H.root_iff _ hpp.length_lt).mp hroot
  have hne : ε.nodes.length ≠ 0 := by simpa using ε.nonempty
  exact hne h0

/-! ## The carriers (design (a): ambient-coordinate chain sets + inherited data) -/

/-- A CUT LAYER: an ambient-coordinate read-site set with its inherited halt
data — the common carrier of the shallow layer and of each block.  `halts` is
the GRAPH of the tree's `leafV` restricted to the layer (full data: values
retained); `nsHalts` the ns-flagged leaves of the layer. -/
structure CutLayer (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] where
  reads : Finset (History p F)
  halts : Finset (History p F × Vd)
  nsHalts : Finset (History p F)

/-- `Ŝ(Tr, E)` — the FULL-DATA SHALLOW LAYER (§1.1 granularity: values and
heights retained; the height-forgotten resummation is CL-17(ii)/`W17ii`, NOT
here): the shallow-owned read sites with their halt data, the entrance list
(the block roots, in ambient coordinates — each entrance's full interface node
is read off it, `cut_keying`), and the retained hen payload. -/
structure ShallowData (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] where
  layer : CutLayer p F
  ents : Finset (History p F)
  henV : Multiset Vd

/-- `D_ε(Tr, E)` — a PER-BLOCK DERIVATION carrier: the entrance `ε` as the
block's head/state index (the (BDY) shift: its OWN read is shallow-side), and
the block-owned read sites with their inherited halt data, in ambient
coordinates (design (a); re-rooting is BLOCKED, `reroot_blocked`). -/
structure BlockDeriv (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] where
  head : History p F
  layer : CutLayer p F

/-- The block's INTERFACE NODE, read off the entrance's own node data (the
W7_cutWD boundary-data clause): every entrance datum — species, `(e, h)`,
`(ψ, g, μ)`, `Dwidth`, … — is a field of this node.  The typed `(e, τ, δ)`
read-offs against the grammar side are the (K-CUT-m)/(K-CUT-g) seam re-keys. -/
def BlockDeriv.iface (D : BlockDeriv p F) : Node p F := D.head.lastNode

/-- The interface's ramification datum `e` (the `e_i` of the entrance list). -/
def BlockDeriv.entE (D : BlockDeriv p F) : ℕ := D.iface.e

/-! ## The extraction maps — FUNCTIONS of `(Tr, E)`, choice-free by construction -/

open Classical in
/-- The inherited halt data of a read-site set: the graph of `Tr.leafV` on `R`. -/
noncomputable def haltsOf (Tr : VTree p F) (R : Finset (History p F)) :
    Finset (History p F × Vd) :=
  R.biUnion (fun H => (Tr.leafV H).elim (∅ : Finset (History p F × Vd)) (fun v => {(H, v)}))

open Classical in
/-- The inherited ns-halt flags of a read-site set. -/
noncomputable def nsOf (Tr : VTree p F) (R : Finset (History p F)) :
    Finset (History p F) :=
  R.filter Tr.nsLeaf

/-- Layer packaging: a read-site set with its inherited data. -/
noncomputable def layerOf (Tr : VTree p F) (R : Finset (History p F)) :
    CutLayer p F :=
  ⟨R, haltsOf Tr R, nsOf Tr R⟩

/-- **THE SHALLOW-LAYER EXTRACTION** `Tr ↦ Ŝ(Tr)`. -/
noncomputable def shallowDataOf (Tr : VTree p F) (E : History p F → Prop) :
    ShallowData p F :=
  ⟨layerOf Tr (shallowReads Tr E), minEnts Tr E, Tr.henV⟩

/-- **THE PER-BLOCK EXTRACTION** `Tr ↦ D_ε(Tr)`. -/
noncomputable def blockDerivOf (Tr : VTree p F) (E : History p F → Prop)
    (ε : History p F) : BlockDeriv p F :=
  ⟨ε, layerOf Tr (blockReads Tr E ε)⟩

/-- **THE CUT MAP** `Tr ↦ (Ŝ(Tr), (D_ε(Tr))_ε)` — the level-(1b) decomposition
data, a function of `(Tr, E)` (no choice anywhere: every component is a
`Finset.filter`/graph of tree data). -/
noncomputable def cutOf (Tr : VTree p F) (E : History p F → Prop) :
    ShallowData p F × (History p F → BlockDeriv p F) :=
  (shallowDataOf Tr E, fun ε => blockDerivOf Tr E ε)

open Classical in
/-- The tree's block FAMILY — a `Finset` (finiteness from `hfin` through
`minEnts`; the per-tree half of the countability clause). -/
noncomputable def blockFam (Tr : VTree p F) (E : History p F → Prop) :
    Finset (BlockDeriv p F) :=
  (minEnts Tr E).image (fun ε => blockDerivOf Tr E ε)

/-! ### Definitional read-offs (the extraction is literal filter packaging) -/

@[simp] lemma shallowDataOf_reads (Tr : VTree p F) (E : History p F → Prop) :
    (shallowDataOf Tr E).layer.reads = shallowReads Tr E := rfl

@[simp] lemma shallowDataOf_ents (Tr : VTree p F) (E : History p F → Prop) :
    (shallowDataOf Tr E).ents = minEnts Tr E := rfl

@[simp] lemma shallowDataOf_henV (Tr : VTree p F) (E : History p F → Prop) :
    (shallowDataOf Tr E).henV = Tr.henV := rfl

@[simp] lemma blockDerivOf_head (Tr : VTree p F) (E : History p F → Prop)
    (ε : History p F) : (blockDerivOf Tr E ε).head = ε := rfl

@[simp] lemma blockDerivOf_reads (Tr : VTree p F) (E : History p F → Prop)
    (ε : History p F) : (blockDerivOf Tr E ε).layer.reads = blockReads Tr E ε := rfl

/-! ## Membership calculus for the inherited data -/

/-- Members of a one-site halt graph carry that site and its recorded value. -/
lemma mem_haltAt {Tr : VTree p F} {H : History p F} {Hv : History p F × Vd}
    (h : Hv ∈ (Tr.leafV H).elim (∅ : Finset (History p F × Vd)) (fun v => {(H, v)})) :
    Hv.1 = H ∧ Tr.leafV Hv.1 = some Hv.2 := by
  cases hv : Tr.leafV H with
  | none => rw [hv] at h; simp at h
  | some v =>
      rw [hv] at h
      have heq : Hv = (H, v) := Finset.mem_singleton.mp h
      subst heq
      exact ⟨rfl, hv⟩

/-- The halt graph records EXACTLY the layer's realized leaf verdicts. -/
lemma mem_haltsOf {Tr : VTree p F} {R : Finset (History p F)}
    {Hv : History p F × Vd} :
    Hv ∈ haltsOf Tr R ↔ Hv.1 ∈ R ∧ Tr.leafV Hv.1 = some Hv.2 := by
  classical
  simp only [haltsOf, Finset.mem_biUnion]
  constructor
  · rintro ⟨H, hH, hmem⟩
    obtain ⟨h1, h2⟩ := mem_haltAt hmem
    exact ⟨by rw [h1]; exact hH, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Hv.1, h1, by rw [h2]; exact Finset.mem_singleton.mpr rfl⟩

/-- The ns flags record EXACTLY the layer's ns leaves. -/
lemma mem_nsOf {Tr : VTree p F} {R : Finset (History p F)} {H : History p F} :
    H ∈ nsOf Tr R ↔ H ∈ R ∧ Tr.nsLeaf H := by
  classical
  simp [nsOf]

/-! ## Conformance clauses -/

/-- KEYING CONFORMANCE: the entrance list of `Ŝ(Tr)` is `minEnts`, each block
is headed by its own entrance, and the block interface is read off the
entrance's node data — all definitional (the extraction cannot mis-key). -/
theorem cut_keying (Tr : VTree p F) (E : History p F → Prop) :
    (shallowDataOf Tr E).ents = minEnts Tr E ∧
    ∀ ε ∈ (shallowDataOf Tr E).ents,
      (blockDerivOf Tr E ε).head = ε ∧
      (blockDerivOf Tr E ε).iface = ε.lastNode :=
  ⟨rfl, fun _ _ => ⟨rfl, rfl⟩⟩

/-- (BDY) CONFORMANCE, carrier side: the entrance list is PART of the shallow
read-site set — each block root's own entering read is charged shallow-side. -/
theorem shallowDataOf_ents_subset (Tr : VTree p F) (E : History p F → Prop) :
    (shallowDataOf Tr E).ents ⊆ (shallowDataOf Tr E).layer.reads := by
  intro ε hε
  rw [shallowDataOf_ents] at hε
  rw [shallowDataOf_reads]
  obtain ⟨hc, _, hsh⟩ := mem_minEnts.mp hε
  exact mem_shallowReads.mpr ⟨hc, hsh⟩

/-- (BDY) CONFORMANCE, block side: every read a block carries sits STRICTLY
below its head. -/
theorem blockDerivOf_below (Tr : VTree p F) (E : History p F → Prop)
    (ε : History p F) :
    ∀ H ∈ (blockDerivOf Tr E ε).layer.reads, ProperPrefix ε H := by
  intro H hH
  rw [blockDerivOf_reads] at hH
  exact (mem_blockReads.mp hH).2.2.1

open Classical in
/-- SUBTREE CONFORMANCE (strict form): for a genuine minimal entrance the
block's reads are EXACTLY the chains strictly below it — the block is the full
subtree in ambient coordinates, nothing skipped, nothing re-classified (the
§2.2 no-reclassification fence at the carrier). -/
theorem blockReads_eq_cone (Tr : VTree p F) (E : History p F → Prop)
    {ε : History p F} (hε : ε ∈ minEnts Tr E) :
    blockReads Tr E ε = Tr.hfin.toFinset.filter (fun H => ProperPrefix ε H) := by
  classical
  obtain ⟨hεc, hEε, hshε⟩ := mem_minEnts.mp hε
  ext H
  simp only [mem_blockReads, Finset.mem_filter, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨hHc, hfe⟩
    exact ⟨hHc, hfe.2.1⟩
  · rintro ⟨hHc, hpp⟩
    refine ⟨hHc, hEε, hpp, ?_⟩
    intro H' hE' hpp'
    rcases List.prefix_or_prefix_of_prefix hpp.1 hpp'.1 with hc | hc
    · exact hc
    · by_cases heq : H' = ε
      · subst heq; exact List.prefix_refl _
      · exact absurd hE' (hshε H' ⟨hc, heq⟩)

open Classical in
/-- SUBTREE CONFORMANCE (cone form — the blueprint's design-(a) object as a
THEOREM): head-insert of the block layer = the ambient ε-cone
`{H ∈ Tr.chains | ε.IsPrefixOf H}`. -/
theorem blockDerivOf_cone (Tr : VTree p F) (E : History p F → Prop)
    {ε : History p F} (hε : ε ∈ minEnts Tr E) :
    insert ε ((blockDerivOf Tr E ε).layer.reads)
      = Tr.hfin.toFinset.filter (fun H => ε.IsPrefixOf H) := by
  classical
  have hεc : ε ∈ Tr.chains := (mem_minEnts.mp hε).1
  rw [blockDerivOf_reads, blockReads_eq_cone Tr E hε]
  ext H
  simp only [Finset.mem_insert, Finset.mem_filter, Set.Finite.mem_toFinset]
  constructor
  · rintro (rfl | ⟨hHc, hpp⟩)
    · exact ⟨hεc, List.prefix_refl _⟩
    · exact ⟨hHc, hpp.1⟩
  · rintro ⟨hHc, hpre⟩
    by_cases heq : H = ε
    · exact Or.inl heq
    · exact Or.inr ⟨hHc, hpre, fun hh => heq hh.symm⟩

/-- HALT-LAW CONFORMANCE: every recorded halt is a genuine maximal chain of the
tree (`hleaf` inherited — the carriers cannot record a phantom leaf). -/
theorem haltsOf_leafLaw (Tr : VTree p F) {R : Finset (History p F)}
    {Hv : History p F × Vd} (h : Hv ∈ haltsOf Tr R) :
    Hv.1 ∈ Tr.chains ∧ IsMaximalIn Tr.chains Hv.1 :=
  (Tr.hleaf Hv.1).mp (by rw [(mem_haltsOf.mp h).2]; rfl)

/-- NS-LAW CONFORMANCE: every recorded ns flag is a genuine maximal chain
(`hns_leaf` inherited). -/
theorem nsOf_leafLaw (Tr : VTree p F) {R : Finset (History p F)}
    {H : History p F} (h : H ∈ nsOf Tr R) :
    H ∈ Tr.chains ∧ IsMaximalIn Tr.chains H :=
  Tr.hns_leaf H (mem_nsOf.mp h).2

/-! ## Verdict conformance: σ₀ ⊎ ⊎_ε verdict(D_ε) = typemult (the (‡)
compatibility read at the concrete carrier) -/

/-- A layer's verdict mass: the sum of its recorded halt values. -/
noncomputable def CutLayer.verdictM (L : CutLayer p F) : Multiset (ℕ × ℕ) :=
  ∑ Hv ∈ L.halts, Hv.2.1

/-- `σ₀(Ŝ)` — the shallow layer's halted verdict: the retained hen payload plus
the shallow halt-leaf verdicts (read off the shallow halt leaves, as the
W7_cutWD σ₀-feed clause specifies). -/
noncomputable def ShallowData.σ0 (S : ShallowData p F) : Multiset (ℕ × ℕ) :=
  (S.henV.map Subtype.val).sum + S.layer.verdictM

/-- `verdict(D_ε)` — a block's verdict contribution. -/
noncomputable def BlockDeriv.verdict (D : BlockDeriv p F) : Multiset (ℕ × ℕ) :=
  D.layer.verdictM

/-- The layer verdict evaluates to the tree's own leaf-verdict sum over the
layer's reads. -/
lemma verdictM_layerOf (Tr : VTree p F) (R : Finset (History p F)) :
    (layerOf Tr R).verdictM
      = ∑ H ∈ R, ((Tr.leafV H).elim 0 Subtype.val) := by
  classical
  have hdisj : Set.PairwiseDisjoint (↑R : Set (History p F))
      (fun H => (Tr.leafV H).elim (∅ : Finset (History p F × Vd)) (fun v => {(H, v)})) := by
    intro H₁ _ H₂ _ hne
    refine Finset.disjoint_left.mpr fun Hv h1 h2 => ?_
    exact hne (((mem_haltAt h1).1).symm.trans (mem_haltAt h2).1)
  show ∑ Hv ∈ haltsOf Tr R, Hv.2.1 = _
  rw [haltsOf, Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun H _ => ?_
  cases hv : Tr.leafV H with
  | none => simp
  | some v => simp

lemma shallowDataOf_σ0 (Tr : VTree p F) (E : History p F → Prop) :
    (shallowDataOf Tr E).σ0
      = (Tr.henV.map Subtype.val).sum
        + ∑ H ∈ shallowReads Tr E, ((Tr.leafV H).elim 0 Subtype.val) :=
  congrArg (fun m => (Tr.henV.map Subtype.val).sum + m)
    (verdictM_layerOf Tr (shallowReads Tr E))

lemma blockDerivOf_verdict (Tr : VTree p F) (E : History p F → Prop)
    (ε : History p F) :
    (blockDerivOf Tr E ε).verdict
      = ∑ H ∈ blockReads Tr E ε, ((Tr.leafV H).elim 0 Subtype.val) :=
  verdictM_layerOf Tr (blockReads Tr E ε)

/-- **VERDICT CONFORMANCE** — the (‡)-compatibility identity at the concrete
carrier: the tree's total verdict is the shallow σ₀ plus the block verdicts,
each leaf charged EXACTLY ONCE across the cut (regroup along the A2 ownership
partition; the (BDY) shift keeps an entrance-that-halts charged shallow-side
only, since block halt data live on the STRICT cone). -/
theorem typemult_cut (Tr : VTree p F) (E : History p F → Prop) :
    Tr.typemult
      = (shallowDataOf Tr E).σ0
        + ∑ ε ∈ minEnts Tr E, (blockDerivOf Tr E ε).verdict := by
  classical
  have hpart := read_cut_partition Tr E
  have hsum : ∑ H ∈ Tr.hfin.toFinset, ((Tr.leafV H).elim 0 Subtype.val)
      = (∑ H ∈ shallowReads Tr E, ((Tr.leafV H).elim 0 Subtype.val))
        + ∑ ε ∈ minEnts Tr E, ∑ H ∈ blockReads Tr E ε,
            ((Tr.leafV H).elim 0 Subtype.val) := by
    rw [hpart.1, Finset.sum_union hpart.2.1, Finset.sum_biUnion hpart.2.2]
  rw [shallowDataOf_σ0]
  simp only [blockDerivOf_verdict]
  simp only [VTree.typemult]
  rw [hsum, add_assoc]

/-! ## Injectivity of the cut map (level (1b): the decomposition DATA are
unique — G-2 falsifier #3, closed at the object level) -/

/-- Data recovery inside one layer: equal inherited data force equal leaf
verdicts and ns flags at every member site. -/
lemma layer_data_agree {Tr Tr' : VTree p F} {R : Finset (History p F)}
    (hhalts : haltsOf Tr R = haltsOf Tr' R) (hns : nsOf Tr R = nsOf Tr' R)
    {H : History p F} (hH : H ∈ R) :
    Tr.leafV H = Tr'.leafV H ∧ (Tr.nsLeaf H ↔ Tr'.nsLeaf H) := by
  have key : ∀ v : Vd, Tr.leafV H = some v ↔ Tr'.leafV H = some v := by
    intro v
    constructor
    · intro hv
      have hm : ((H, v) : History p F × Vd) ∈ haltsOf Tr R :=
        mem_haltsOf.mpr ⟨hH, hv⟩
      exact (mem_haltsOf.mp (hhalts ▸ hm)).2
    · intro hv
      have hm : ((H, v) : History p F × Vd) ∈ haltsOf Tr' R :=
        mem_haltsOf.mpr ⟨hH, hv⟩
      exact (mem_haltsOf.mp (hhalts.symm ▸ hm)).2
  constructor
  · cases h1 : Tr.leafV H with
    | none =>
        cases h2 : Tr'.leafV H with
        | none => rfl
        | some v =>
            have hcontra := (key v).mpr h2
            rw [h1] at hcontra
            simp at hcontra
    | some v => exact ((key v).mp h1).symm
  · constructor
    · intro hns'
      have hm : H ∈ nsOf Tr R := mem_nsOf.mpr ⟨hH, hns'⟩
      exact (mem_nsOf.mp (hns ▸ hm)).2
    · intro hns'
      have hm : H ∈ nsOf Tr' R := mem_nsOf.mpr ⟨hH, hns'⟩
      exact (mem_nsOf.mp (hns.symm ▸ hm)).2

/-- **CUT-MAP INJECTIVITY = (K-CUT-1) level (1b)** [G-2 falsifier #3 at the
object level]: two trees with the same shallow-layer data and the same block
derivations at every shared entrance are THE SAME TREE, in the corpus's own
tree equality `VTree.ext` (the (chains, henV, leafV, nsLeaf) tuple; literal
structure equality is the wrong target — `leafV`/`nsLeaf` carry junk off the
chain set).  Chains are recovered by `read_cut_exhaustive`; leaf/ns data by
the layer graphs. -/
theorem cut_injective (Tr Tr' : VTree p F) (E : History p F → Prop)
    (hS : shallowDataOf Tr E = shallowDataOf Tr' E)
    (hB : ∀ ε ∈ minEnts Tr E, blockDerivOf Tr E ε = blockDerivOf Tr' E ε) :
    VTree.ext Tr Tr' := by
  classical
  have hsh : shallowReads Tr E = shallowReads Tr' E :=
    congrArg (fun S : ShallowData p F => S.layer.reads) hS
  have hme : minEnts Tr E = minEnts Tr' E :=
    congrArg (fun S : ShallowData p F => S.ents) hS
  have hhen : Tr.henV = Tr'.henV :=
    congrArg (fun S : ShallowData p F => S.henV) hS
  -- block reads agree on the shared entrance set
  have hbr : ∀ ε ∈ minEnts Tr E, blockReads Tr E ε = blockReads Tr' E ε :=
    fun ε hε => congrArg (fun D : BlockDeriv p F => D.layer.reads) (hB ε hε)
  -- chains recovery
  have htF : Tr.hfin.toFinset = Tr'.hfin.toFinset := by
    rw [read_cut_exhaustive Tr E, read_cut_exhaustive Tr' E, ← hsh, ← hme]
    exact congrArg (fun X => shallowReads Tr E ∪ X)
      (Finset.biUnion_congr rfl hbr)
  have hchains : Tr.chains = Tr'.chains := by
    rw [← Set.Finite.coe_toFinset Tr.hfin, ← Set.Finite.coe_toFinset Tr'.hfin, htF]
  -- shallow-layer data agreement
  have hshData : ∀ H ∈ shallowReads Tr E,
      Tr.leafV H = Tr'.leafV H ∧ (Tr.nsLeaf H ↔ Tr'.nsLeaf H) := by
    intro H hH
    refine layer_data_agree ?_ ?_ hH
    · conv_rhs => rw [hsh]
      exact congrArg (fun S : ShallowData p F => S.layer.halts) hS
    · conv_rhs => rw [hsh]
      exact congrArg (fun S : ShallowData p F => S.layer.nsHalts) hS
  -- block-layer data agreement
  have hblData : ∀ ε ∈ minEnts Tr E, ∀ H ∈ blockReads Tr E ε,
      Tr.leafV H = Tr'.leafV H ∧ (Tr.nsLeaf H ↔ Tr'.nsLeaf H) := by
    intro ε hε H hH
    refine layer_data_agree ?_ ?_ hH
    · conv_rhs => rw [hbr ε hε]
      exact congrArg (fun D : BlockDeriv p F => D.layer.halts) (hB ε hε)
    · conv_rhs => rw [hbr ε hε]
      exact congrArg (fun D : BlockDeriv p F => D.layer.nsHalts) (hB ε hε)
  refine ⟨hchains, hhen, ?_⟩
  intro H hHc
  have hH : H ∈ Tr.hfin.toFinset := Tr.hfin.mem_toFinset.mpr hHc
  rw [read_cut_exhaustive Tr E] at hH
  rcases Finset.mem_union.mp hH with hs | hb
  · exact hshData H hs
  · obtain ⟨ε, hε, hHb⟩ := Finset.mem_biUnion.mp hb
    exact hblData ε hε H hHb

/-- The packaged form: the full cut map (shallow data + the total block-keyed
family) is injective up to `VTree.ext`. -/
theorem cutOf_injective (Tr Tr' : VTree p F) (E : History p F → Prop)
    (h : cutOf Tr E = cutOf Tr' E) : VTree.ext Tr Tr' :=
  cut_injective Tr Tr' E (congrArg Prod.fst h)
    (fun ε _ => congrFun (congrArg Prod.snd h) ε)

/-! ## Countability of the family (the honest, provable scope — header note) -/

/-- Per-tree finiteness: the block family of any single tree is finite
(from `hfin` through `minEnts` — it IS a `Finset`). -/
theorem blockFam_finite (Tr : VTree p F) (E : History p F → Prop) :
    (↑(blockFam Tr E) : Set (BlockDeriv p F)).Finite :=
  (blockFam Tr E).finite_toSet

@[simp] lemma mem_blockFam {Tr : VTree p F} {E : History p F → Prop}
    {D : BlockDeriv p F} :
    D ∈ blockFam Tr E ↔ ∃ ε ∈ minEnts Tr E, blockDerivOf Tr E ε = D := by
  classical
  simp [blockFam]

/-- COUNTABILITY TRANSPORT: the cut family of any countable tree family is
countable.  (The M04 consumer instantiates the tree family as the realized
type-σ trees; THAT family's countability is (K-CUT-g)/(K-CUT-s) seam
territory — the raw `History` carrier is NOT countable, see the header
honesty note, so no type-level instance can exist here.) -/
theorem cutFamily_countable (E : History p F → Prop) {𝒯 : Set (VTree p F)}
    (h𝒯 : 𝒯.Countable) :
    ((fun Tr => cutOf Tr E) '' 𝒯).Countable :=
  h𝒯.image _

end LeanUrat.Scaffold.HDischarge.H8
