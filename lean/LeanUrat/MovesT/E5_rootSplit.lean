/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.F0_preHalt
import LeanUrat.MovesT.E2_jcRootCard

/-! # T-E5 `fiber_root_split` [hard] — the ROOT CLAUSE (MOVES 7485–7495), exponent
t = numTracks (rev-2 arithmetic, census-verified). `RootSplitData`/`trackEvent` are
Defs carriers. `rootSplit_exists` (REV 4, Codex-3 #10) CONSTRUCTS the decomposition
from the tree's own structure — PROVED (E-phase prove-now set); only the shared
root-cell datum `hg` stays a hypothesis, owner-tagged.

STATUS 2026-07-30 (the assembly-spine escalation): `fiber_root_split` is PROVED
MODULO ONE fenced residual (`hnostray` inside the proof — head-roster completeness
of realized root children on the decomposed set). Everything else of the blueprint's
five-step decomposition chain is machine-checked: the fiber/track-event set
decomposition (both inclusions, all six `fiberAt` clauses reconstructed), the (SIB)
application at the `.amb` cell (= the root cell via `RootCellsOf`), the head-roster
product split, the t ≤ 1 direct legs, and the T-E2 conversion. The residual's
countermodel shape and owner tag are recorded at the `hnostray` site. -/

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

section RootSplitHelpers

/-- `[ν]` is a list prefix iff the head is `ν`. -/
private lemma singleton_prefix_iff {α : Type*} (ν : α) (l : List α) :
    [ν] <+: l ↔ l.head? = some ν := by
  constructor
  · rintro ⟨s, hs⟩
    rw [← hs]
    rfl
  · intro h
    cases l with
    | nil => exact absurd h (by simp)
    | cons a t =>
      obtain rfl : a = ν := by simpa using h
      exact ⟨t, rfl⟩

/-- nonempty prefixes share the head. -/
private lemma prefix_head_eq {α : Type*} {l' l : List α} (h : l' <+: l)
    (hne : l' ≠ []) : l'.head? = l.head? := by
  obtain ⟨s, hs⟩ := h
  cases l' with
  | nil => exact absurd rfl hne
  | cons a t => rw [← hs]; rfl

/-- realizing the one-node history IS realizing the root child (mem_single, keyed to
the closed `oneNode`). -/
private lemma mem_oneNode_iff (T : TreeModel p F n N m pol) (ν : Node p F)
    (h : ChildRoot none ν) (x : Box p m) :
    T.mem (some (oneNode ν h)) x ↔ T.child none ν x := by
  have h1 : (([ν] : List (Node p F)) ≠ [] ∧
      ∀ (j : ℕ) (hj : j < ([ν] : List (Node p F)).length),
        ((([ν] : List (Node p F))[j]'hj).species = ReadSpecies.root ↔ j = 0)) := by
    refine ⟨by simp, ?_⟩
    intro j hj
    have hj0 : j = 0 := by simpa using Nat.lt_one_iff.mp (by simpa using hj)
    subst hj0
    simpa using (show ν.species = ReadSpecies.root from h)
  exact T.mem_single ν h1 x

/-- a realized nonempty history's HEAD is a realized root child. -/
private lemma child_of_mem (T : TreeModel p F n N m pol) (H : History p F)
    (hne : H.nodes ≠ []) (x : Box p m) (hmem : T.mem (some H) x) :
    T.child none (H.nodes.head hne) x := by
  have hlen : 0 < H.nodes.length := List.length_pos_iff.mpr hne
  have hroot : (H.nodes.head hne).species = ReadSpecies.root := by
    have := (H.root_iff 0 hlen).mpr rfl
    rwa [List.getElem_zero_eq_head hlen] at this
  have hpre : (oneNode (H.nodes.head hne) hroot).IsPrefixOf H := by
    show ([H.nodes.head hne] : List (Node p F)) <+: H.nodes
    exact (singleton_prefix_iff _ _).mpr (List.head?_eq_head hne)
  have hmem1 := mem_of_prefix T x H.nodes H rfl hmem _ hpre
  exact (mem_oneNode_iff T _ hroot x).mp hmem1

end RootSplitHelpers

/-- **T-E5, the ROOT CLAUSE** — the decomposition chain of the blueprint sketch
(steps (1)–(5)), PROVED 2026-07-30 (the assembly-spine escalation) MODULO the single
fenced residual `hnostray` below. Route: `fiberAt` decomposes as
`rootCell ∩ ⋂ᵢ trackEvent i` (the ⊆ leg from `fiberAt`'s own clauses through the
head roster; the ⊇ leg reconstructs all six clauses at any decomposed point, with
the head-roster completeness `hnostray` the one non-clause step); the count then
follows from (SIB) at the `.amb` cell (= the root cell, via `RootCellsOf`) for
t ≥ 2, and directly (no SIB) for t ≤ 1, with T-E2 converting `card(Σ₀)·pⁿ = p^m`. -/
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
  classical
  obtain ⟨x₀, hx₀⟩ := hreal
  have hx₀R : x₀ ∈ rootCell χ g := hfib x₀ hx₀
  -- ==== track/chain bookkeeping ====
  have htsub : ∀ i, htracks.trackChains i ⊆ Tr.chains := by
    intro i
    rw [← htracks.hpart.1]
    exact Set.subset_iUnion _ i
  have htrack_unique : ∀ i j, ∀ H, H ∈ htracks.trackChains i →
      H ∈ htracks.trackChains j → i = j := by
    intro i j H hi hj
    by_contra hij
    exact Set.disjoint_left.mp (htracks.hpart.2 hij) hi hj
  have hmem_track : ∀ H ∈ Tr.chains, ∃ i, H ∈ htracks.trackChains i := by
    intro H hH
    rw [← htracks.hpart.1] at hH
    exact Set.mem_iUnion.mp hH
  have htrack_of_head : ∀ (i : Fin htracks.t) (H : History p F), H ∈ Tr.chains →
      H.nodes.head? = some (htracks.headOf i) → H ∈ htracks.trackChains i := by
    intro i H hH hhd
    obtain ⟨j, hj⟩ := hmem_track H hH
    have := htracks.hhead j H hj
    rw [hhd] at this
    have : htracks.headOf i = htracks.headOf j := Option.some.inj this
    rwa [htracks.hinj this]
  -- maximality transfers between a track group and the full chain set
  have hmax_up : ∀ (i : Fin htracks.t) (H : History p F), H ∈ htracks.trackChains i →
      IsMaximalIn (htracks.trackChains i) H → IsMaximalIn Tr.chains H := by
    intro i H hHi hmax H' hH' hpre
    have hne : H.nodes ≠ [] := Tr.hne_nodes H (htsub i hHi)
    have hhd : H'.nodes.head? = some (htracks.headOf i) := by
      rw [← prefix_head_eq hpre hne]
      exact htracks.hhead i H hHi
    exact hmax H' (htrack_of_head i H' hH' hhd) hpre
  have hmax_down : ∀ (i : Fin htracks.t) (H : History p F),
      IsMaximalIn Tr.chains H → IsMaximalIn (htracks.trackChains i) H := by
    intro i H hmax H' hH' hpre
    exact hmax H' (htsub i hH') hpre
  -- heads are chains (transport `hcov`'s proof-field to the given `hcr`)
  have hheadchain : ∀ i, oneNode (htracks.headOf i) (hcr i) ∈ Tr.chains := by
    intro i
    obtain ⟨h, hmem⟩ := htracks.hcov i
    exact hmem
  -- ==== (1) fiber points realize each head as a root child ====
  have hchild_head : ∀ x, Tr.fiberAt T χ x → ∀ i,
      T.child none (htracks.headOf i) x := by
    intro x hx i
    have hchain := hheadchain i
    have hpm := (hx.1 (oneNode (htracks.headOf i) (hcr i))).mp hchain
    exact (mem_oneNode_iff T _ (hcr i) x).mp hpm.2.1
  -- ==== (⊆) fiber points lie in every track event ====
  have hfib_track : ∀ x, Tr.fiberAt T χ x → ∀ i,
      x ∈ trackEvent Tr T htracks i (hcr i) := by
    intro x hx i
    refine ⟨?_, ?_, ?_⟩
    · -- clause (1): the track group is exactly the realized head-i chain set
      intro H'
      constructor
      · intro hH'
        have hH'c : H' ∈ Tr.chains := htsub i hH'
        have hpm := (hx.1 H').mp hH'c
        refine ⟨?_, hpm.2.1, ?_⟩
        · show ([htracks.headOf i] : List (Node p F)) <+: H'.nodes
          exact (singleton_prefix_iff _ _).mpr (htracks.hhead i H' hH')
        · intro H'' hpre1 hpre2 hne''
          have hne : H''.nodes ≠ [] := by
            intro h0
            have h1 : ([htracks.headOf i] : List (Node p F)) <+: H''.nodes := hpre1
            rw [h0] at h1
            simpa using List.prefix_nil.mp h1
          exact hpm.2.2 H'' hpre2 hne'' hne
      · rintro ⟨hpre, hmem, hduties⟩
        have hhd : H'.nodes.head? = some (htracks.headOf i) :=
          (singleton_prefix_iff _ _).mp hpre
        have hne' : H'.nodes ≠ [] := by
          intro h0
          rw [h0] at hhd
          simp at hhd
        have hpm : PrunedMem T H' x := by
          refine ⟨hmem, ?_⟩
          intro H'' hpre2 hne'' hnem
          have hhd'' : H''.nodes.head? = some (htracks.headOf i) := by
            rw [prefix_head_eq hpre2 hnem]
            exact hhd
          exact hduties H'' ((singleton_prefix_iff _ _).mpr hhd'') hpre2 hne''
        have hH'c : H' ∈ Tr.chains := (hx.1 H').mpr ⟨hne', hpm⟩
        exact htrack_of_head i H' hH'c hhd
    · -- clause (2): leaf dichotomy from fiberAt (ii) via maximality transfer
      intro H' hH' hmax
      exact hx.2.1 H' (htsub i hH') (hmax_up i H' hH' hmax)
    · -- clause (3): non-maximal duties from fiberAt (iv)
      intro H' hH' hnmax
      refine hx.2.2.2.1 H' (htsub i hH') ?_
      intro hmaxc
      exact hnmax (hmax_down i H' hmaxc)
  -- ==== THE FENCED RESIDUAL: head-roster completeness on the decomposed set ====
  -- [ADJUDICATION RECORD 2026-07-30. The adjudicated `child_red_uniform` law kills
  --  the SAME-CELL strays (a child realized at one point of a root reduction cell
  --  now holds at every point of that cell, so a stray's whole `.red`-cell drops
  --  out of the fiber). What no displayed law pins is a stray root child realized
  --  on a `.red`-cell DISJOINT from the fiber's own cells but inside the same
  --  root cell {f̄ = g} — at such a point y, every trackEvent condition can hold
  --  while `oneNode ν` gives y an extra pruned chain, so y ∈ R ∩ ⋂ᵢ Sᵢ ∖ fiber
  --  and the displayed count breaks. Canonically this is dead — realized root
  --  children are exactly the first window reads on the reduction's repeated
  --  tracks ((c2) covering, MOVES 7112–7119, m_i = 1 ⇒ τ-hen carries NO child —
  --  and the fiber's roster is track-complete by `fiberAt` (vi)) — so this resi-
  --  dual is PRESENTED-FACE content, same owner genre as `presents`/`state_cell`:
  --  owner HC-2/D4R0K. Discharge shape: the canonical `T.child none ν ·` event is
  --  the ν-cell stratum inside its track's window, and window structure is track
  --  data of the reduction datum g.]
  have hnostray : ∀ y ∈ rootCell χ g,
      (∀ i, y ∈ trackEvent Tr T htracks i (hcr i)) →
      ∀ ν : Node p F, T.child none ν y → ∃ i, htracks.headOf i = ν := by
    sorry
  -- ==== (⊇) decomposed points are fiber points ====
  have hconv : ∀ y ∈ rootCell χ g,
      (∀ i, y ∈ trackEvent Tr T htracks i (hcr i)) → Tr.fiberAt T χ y := by
    intro y hyR hyT
    have hredeq : redPoly χ y = redPoly χ x₀ := by
      unfold redPoly
      congr 1
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [hyR b, hx₀R b]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- clause (i)
      intro H
      constructor
      · intro hH
        obtain ⟨i, hHi⟩ := hmem_track H hH
        obtain ⟨hpre, hmem, hduties⟩ := (hyT i).1 H |>.mp hHi
        refine ⟨Tr.hne_nodes H hH, hmem, ?_⟩
        intro H'' hpre2 hne'' hnem
        have hhd'' : H''.nodes.head? = some (htracks.headOf i) := by
          rw [prefix_head_eq hpre2 hnem]
          exact (singleton_prefix_iff _ _).mp hpre
        exact hduties H'' ((singleton_prefix_iff _ _).mpr hhd'') hpre2 hne''
      · rintro ⟨hne, hpm⟩
        have hchild : T.child none (H.nodes.head hne) y :=
          child_of_mem T H hne y hpm.1
        obtain ⟨i, hi⟩ := hnostray y hyR hyT (H.nodes.head hne) hchild
        have hHi : H ∈ htracks.trackChains i := by
          refine (hyT i).1 H |>.mpr ⟨?_, hpm.1, ?_⟩
          · show ([htracks.headOf i] : List (Node p F)) <+: H.nodes
            rw [hi]
            exact (singleton_prefix_iff _ _).mpr (List.head?_eq_head hne)
          · intro H'' hpre1 hpre2 hne''
            have hnem : H''.nodes ≠ [] := by
              intro h0
              have : ([htracks.headOf i] : List (Node p F)) <+: H''.nodes := hpre1
              rw [h0] at this
              simpa using List.prefix_nil.mp this
            exact hpm.2 H'' hpre2 hne'' hnem
        exact htsub i hHi
      -- clause (ii)
    · intro H hH hmax
      obtain ⟨i, hHi⟩ := hmem_track H hH
      exact (hyT i).2.1 H hHi (hmax_down i H hmax)
    · -- clause (iii): the hen payload is root-cell data
      rw [show henPayload χ y = henPayload χ x₀ from by
        unfold henPayload henDegrees
        rw [hredeq]]
      exact hx₀.2.2.1
    · -- clause (iv)
      intro H hH hnmax
      obtain ⟨i, hHi⟩ := hmem_track H hH
      refine (hyT i).2.2 H hHi ?_
      intro hmaxt
      exact hnmax (hmax_up i H hHi hmaxt)
    · -- clause (v): tree-only data
      exact hx₀.2.2.2.2.1
    · -- clause (vi): the repeated-factor roster is root-cell data
      rw [show redPoly χ y = redPoly χ x₀ from hredeq]
      exact hx₀.2.2.2.2.2
  -- ==== the set decomposition ====
  have hfeq : {x | Tr.fiberAt T χ x}
      = rootCell χ g ∩ ⋂ i, trackEvent Tr T htracks i (hcr i) := by
    ext x
    constructor
    · intro hx
      exact ⟨hfib x hx, Set.mem_iInter.mpr (hfib_track x hx)⟩
    · rintro ⟨hxR, hxT⟩
      exact hconv x hxR (Set.mem_iInter.mp hxT)
  -- ==== counting ====
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have hE2 : Nat.card ↥(rootCell χ g) * p ^ n = p ^ m := jcRoot_card χ hχ g
  have hCpos : 0 < Nat.card ↥(rootCell χ g) := by
    haveI : Finite ↥(rootCell χ g) := (Set.toFinite _).to_subtype
    exact Nat.card_pos_iff.mpr ⟨⟨x₀, hx₀R⟩, inferInstance⟩
  rcases Nat.lt_or_ge htracks.t 2 with ht2 | ht2
  · -- ==== t ≤ 1: no (SIB) needed (blueprint step (5)'s tail) ====
    by_cases ht0 : htracks.t = 0
    · -- t = 0: the fiber IS the root cell; the product is empty
      haveI hempty : IsEmpty (Fin htracks.t) := ⟨fun i => absurd i.2 (by omega)⟩
      have hinter : (⋂ i : Fin htracks.t, trackEvent Tr T htracks i (hcr i))
          = Set.univ := Set.iInter_of_empty _
      have hprod : (∏ i : Fin htracks.t,
          Nat.card ↥(rootCell χ g ∩ trackEvent Tr T htracks i (hcr i))) = 1 := by
        rw [Finset.univ_eq_empty, Finset.prod_empty]
      have hpow : (Nat.card ↥(rootCell χ g)) ^ htracks.t = 1 := by
        rw [ht0, pow_zero]
      rw [hprod, hpow, mul_one, mul_one, hfeq, hinter, Set.inter_univ]
      exact hE2
    · -- t = 1: a single factor, direct via T-E2
      have ht1 : htracks.t = 1 := by omega
      have i₀ : Fin htracks.t := ⟨0, by omega⟩
      have hall : ∀ i : Fin htracks.t, i = i₀ := by
        intro i
        have hi := i.isLt
        exact Fin.ext (by omega)
      have hinter : (⋂ i : Fin htracks.t, trackEvent Tr T htracks i (hcr i))
          = trackEvent Tr T htracks i₀ (hcr i₀) := by
        ext x
        rw [Set.mem_iInter]
        exact ⟨fun h => h i₀, fun h i => by rw [hall i]; exact h⟩
      have hprod : (∏ i : Fin htracks.t,
            Nat.card ↥(rootCell χ g ∩ trackEvent Tr T htracks i (hcr i)))
          = Nat.card ↥(rootCell χ g ∩ trackEvent Tr T htracks i₀ (hcr i₀)) :=
        Finset.prod_eq_single i₀ (fun j _ hj => absurd (hall j) hj)
          (fun h => absurd (Finset.mem_univ i₀) h)
      have hpow : (Nat.card ↥(rootCell χ g)) ^ htracks.t
          = Nat.card ↥(rootCell χ g) := by
        rw [ht1, pow_one]
      rw [hprod, hpow, hfeq, hinter, ← hE2]
      ring
  · -- ==== t ≥ 2: the (SIB) kernel at the .amb cell (= the root cell) ====
    set c₀ := CA.toCellData.cellOf .amb x₀ with hc₀
    have hRcell : cellEventE T CA.toCellData χ .amb c₀ = rootCell χ g := by
      ext x
      simp only [cellEventE, entEvent, Set.mem_univ, true_and, Set.mem_setOf_eq]
      rw [hrc x x₀]
      constructor
      · intro h b
        rw [h b, hx₀R b]
      · intro h b
        rw [h b, hx₀R b]
    have hheadB : ∀ i, htracks.headOf i ∈ CA.toCellData.branchSetOf c₀ :=
      fun i => CA.toCellData.child_root_sub _ _ (hchild_head x₀ hx₀ i)
    set B₀ := CA.toCellData.branchSetOf c₀ with hB₀
    set headIm := (Finset.univ : Finset (Fin htracks.t)).image htracks.headOf
      with hheadIm
    have hsubB : headIm ⊆ B₀ := by
      intro ν hν
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hν
      exact hheadB i
    have hImcard : headIm.card = htracks.t := by
      rw [hheadIm, Finset.card_image_of_injective _ htracks.hinj,
        Finset.card_univ, Fintype.card_fin]
    have hk2 : 2 ≤ B₀.card :=
      le_trans ht2 (hImcard ▸ Finset.card_le_card hsubB)
    have htk : htracks.t ≤ B₀.card := hImcard ▸ Finset.card_le_card hsubB
    -- the S-family: track events at the heads, univ off the roster
    set S : Node p F → Set (Box p m) := fun ν =>
      if h : ∃ i, htracks.headOf i = ν then
        trackEvent Tr T htracks h.choose (hcr h.choose) else Set.univ with hSdef
    have hShead : ∀ i, S (htracks.headOf i) = trackEvent Tr T htracks i (hcr i) := by
      intro i
      simp only [hSdef]
      have hex : ∃ j, htracks.headOf j = htracks.headOf i := ⟨i, rfl⟩
      rw [dif_pos hex]
      have hji : hex.choose = i := htracks.hinj hex.choose_spec
      rw [hji]
    have hSlegit : ∀ ν ∈ B₀,
        (∃ (hν : ChildRoot (stOf (EntSt.amb : EntSt p F n)) ν)
            (Tsub : Set (History p F)) (leafSpec : History p F → Option Vd)
            (nsSpec : History p F → Prop), Tsub.Finite ∧
          S ν = {x | ContFiber T (stOf (EntSt.amb : EntSt p F n)) ν hν Tsub
            leafSpec nsSpec x})
        ∨ S ν = Set.univ := by
      intro ν hν
      simp only [hSdef]
      by_cases hex : ∃ i, htracks.headOf i = ν
      · left
        rw [dif_pos hex]
        set j := hex.choose with hjdef
        have hj : htracks.headOf j = ν := hex.choose_spec
        clear_value j
        clear hjdef hex
        subst hj
        exact ⟨hcr j, htracks.trackChains j, Tr.leafV, Tr.nsLeaf,
          Tr.hfin.subset (htsub j), rfl⟩
      · right
        rw [dif_neg hex]
    have hsibapp := hsib .amb c₀ S hk2 hSlegit
    -- the ⋂ over the branch set collapses to the track intersection
    have hIcap : (⋂ ν ∈ B₀, S ν)
        = ⋂ i, trackEvent Tr T htracks i (hcr i) := by
      ext x
      simp only [Set.mem_iInter]
      constructor
      · intro h i
        have hx := h (htracks.headOf i) (hheadB i)
        rwa [hShead i] at hx
      · intro h ν hν
        simp only [hSdef]
        by_cases hex : ∃ i, htracks.headOf i = ν
        · rw [dif_pos hex]
          exact h hex.choose
        · rw [dif_neg hex]
          exact Set.mem_univ x
    -- the product over the branch set splits: head factors × card(R)^(k−t)
    have hprodsplit : (∏ ν ∈ B₀,
          Nat.card ↥(rootCell χ g ∩ S ν))
        = (∏ i : Fin htracks.t,
            Nat.card ↥(rootCell χ g ∩ trackEvent Tr T htracks i (hcr i)))
          * (Nat.card ↥(rootCell χ g)) ^ (B₀.card - htracks.t) := by
      rw [← Finset.prod_sdiff hsubB]
      have hhd : (∏ ν ∈ headIm, Nat.card ↥(rootCell χ g ∩ S ν))
          = ∏ i : Fin htracks.t,
              Nat.card ↥(rootCell χ g ∩ trackEvent Tr T htracks i (hcr i)) := by
        rw [hheadIm, Finset.prod_image (fun i _ j _ h => htracks.hinj h)]
        exact Finset.prod_congr rfl (fun i _ => by rw [hShead i])
      have hrest : (∏ ν ∈ B₀ \ headIm, Nat.card ↥(rootCell χ g ∩ S ν))
          = (Nat.card ↥(rootCell χ g)) ^ (B₀.card - htracks.t) := by
        have hstep : ∀ ν ∈ B₀ \ headIm,
            Nat.card ↥(rootCell χ g ∩ S ν) = Nat.card ↥(rootCell χ g) := by
          intro ν hν
          have hnex : ¬ ∃ i, htracks.headOf i = ν := by
            rintro ⟨i, hi⟩
            exact (Finset.mem_sdiff.mp hν).2
              (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
          simp only [hSdef]
          rw [dif_neg hnex, Set.inter_univ]
        rw [Finset.prod_congr rfl hstep, Finset.prod_const, Finset.card_sdiff,
          Finset.inter_eq_left.mpr hsubB, hImcard]
      rw [hhd, hrest, mul_comm]
    -- assemble: cancel card(R)^(k−1) (root cell inhabited)
    rw [← hB₀] at hsibapp
    rw [hRcell, hIcap] at hsibapp
    rw [hprodsplit] at hsibapp
    -- hsibapp : X · C^(k−1) = P · C^(k−t)   [X := card(R ∩ ⋂ tE) = card(fiber)]
    rw [hfeq]
    refine Nat.eq_of_mul_eq_mul_right (pow_pos hCpos (B₀.card - 1)) ?_
    have hkk : B₀.card - htracks.t + htracks.t = B₀.card := by omega
    have hk1 : B₀.card - 1 + 1 = B₀.card := by omega
    calc Nat.card ↥(rootCell χ g ∩ ⋂ i, trackEvent Tr T htracks i (hcr i))
          * (Nat.card ↥(rootCell χ g)) ^ htracks.t * p ^ n
          * (Nat.card ↥(rootCell χ g)) ^ (B₀.card - 1)
        = (Nat.card ↥(rootCell χ g ∩ ⋂ i, trackEvent Tr T htracks i (hcr i))
            * (Nat.card ↥(rootCell χ g)) ^ (B₀.card - 1))
          * ((Nat.card ↥(rootCell χ g)) ^ htracks.t * p ^ n) := by ring
      _ = ((∏ i : Fin htracks.t,
              Nat.card ↥(rootCell χ g ∩ trackEvent Tr T htracks i (hcr i)))
            * (Nat.card ↥(rootCell χ g)) ^ (B₀.card - htracks.t))
          * ((Nat.card ↥(rootCell χ g)) ^ htracks.t * p ^ n) := by rw [hsibapp]
      _ = (∏ i : Fin htracks.t,
              Nat.card ↥(rootCell χ g ∩ trackEvent Tr T htracks i (hcr i)))
          * ((Nat.card ↥(rootCell χ g)) ^ (B₀.card - htracks.t)
            * (Nat.card ↥(rootCell χ g)) ^ htracks.t) * p ^ n := by ring
      _ = (∏ i : Fin htracks.t,
              Nat.card ↥(rootCell χ g ∩ trackEvent Tr T htracks i (hcr i)))
          * (Nat.card ↥(rootCell χ g)) ^ B₀.card * p ^ n := by
            rw [← pow_add, hkk]
      _ = p ^ m * (∏ i : Fin htracks.t,
              Nat.card ↥(rootCell χ g ∩ trackEvent Tr T htracks i (hcr i)))
          * (Nat.card ↥(rootCell χ g)) ^ (B₀.card - 1) := by
            have hck : (Nat.card ↥(rootCell χ g)) ^ B₀.card
                = Nat.card ↥(rootCell χ g)
                  * (Nat.card ↥(rootCell χ g)) ^ (B₀.card - 1) := by
              conv_lhs => rw [← hk1]
              rw [pow_succ']
            rw [hck, ← hE2]
            ring

end LeanUrat.MovesT
