/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.E9_fiberDisjoint
import LeanUrat.MovesT.F0_preHalt
import LeanUrat.MovesT.F1_oneF

/-! # T-D11 `fibOf_keying` — the class-tree → VTree keying (S-7), REV 3/5/6: `fibOf`'s
body displayed with the explicit premises `hrep : PrefixCoherentRepr` and
`hri : ReprInj` (Codex-5 gap #10); `fibOf_partition` consumes `hcov : ClassCover`
(REV 5, Codex-4 #9). [E-DEV, MANIFEST: `fibOf` lives HERE, not in Defs.lean — its
`hclosed`/`hleaf`/`hns_leaf` proof fields genuinely require `hrep`/`hri` content;
the zero-sorry Defs rule forces the carrier into its consuming unit. Only T-D11's
own theorems consume it.]

ADJUDICATED (finisher round, 2026-07-29; MANIFEST ADJ-REPAIR-D11): the blueprint
D11 row's `hclosed`/`hleaf` sketches ("from `hrep`: a class-prefix's representative
IS a history prefix, and ct.addrs is PrefixClosed"; "maximal address ↔ maximal
representative, via `hrep` + `hri` + `hkeys`.2") consume two clauses never displayed
in the hypothesis row: (i) the CONVERSE of `PrefixCoherentRepr` — a nonempty proper
history-prefix of a representative is ITSELF the representative of a class-prefix
(typed below: `RepPrefixClosed`); (ii) the converse leaf-registration clause —
a maximal-in-chains representative is `leafV`-registered; `ClassTree.hkeys` only
registers leafV ⇒ maximal (typed below: `LeafReg`, per-tree — its ∀-`ClassTree`
closure is refutable by an addrs-only tree with empty `leafV`). Both ride the
`fibOf` hypothesis row; owner HC-2 (PresentNorm), the family of `hrep`/`hri`.
With them `hclosed`/`hleaf` are PROVED; `fibOf_fiber_disjoint` is PROVED (the
`hri` address read-off + `hkeys.1` key-injectivity + T-E9); `fibOf_partition` is
PROVED under the ADJUDICATED third premise `hnorm : RepNorm T` (A6 finisher round,
2026-07-29) — the rep-normalization law formerly recorded at its sorry site, typed
below next to `RepPrefixClosed`/`LeafReg` (owner HC-2, the same PresentNorm family)
— via the T-F1 `oneF` witness + the `fiberAt_of_ext` ext-invariance transfer. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

/-- REP-PREFIX CLOSURE — ADJUDICATED premise (i): the converse of
`PrefixCoherentRepr`, which the blueprint D11 row's `hclosed` sketch consumed
undisplayed. A nonempty proper history-prefix of a canonical representative is
itself the representative of a class-prefix. Owner HC-2 (PresentNorm) — typed
here, never proved here. -/
def RepPrefixClosed (n : ℕ) (pol : CanonPolicy p F) : Prop :=
  ∀ {P : Shape n} (i : PrefIdx n pol P) (H' : History p F),
    H'.IsPrefixOf (reprOf i) → H'.nodes ≠ [] → H' ≠ reprOf i →
    ∃ (P' : Shape n) (i' : PrefIdx n pol P'), reprOf i' = H' ∧ ClassPrefixOf i' i

/-- LEAF REGISTRATION — ADJUDICATED premise (ii): `hleaf`'s backward direction.
A maximal-in-chains representative address is `leafV`-registered (the converse of
`ClassTree.hkeys.2`, which only sends registered entries to maximal addresses).
Stated per-tree in the T_can leaf vocabulary (`IsMaximalIn` over the representative
chains): the ∀-`ClassTree` closure is refutable (an addrs-only tree with empty
`leafV` inhabits every `ClassTree` field), so the clause rides next to its `ct` on
the `fibOf` row. Owner HC-2 (PresentNorm). -/
def LeafReg (ct : ClassTree n (F := F) pol) : Prop :=
  ∀ a ∈ ct.addrs,
    IsMaximalIn
      ((fun b : Σ P : Shape n, PrefIdx n pol P => reprOf b.2) '' ↑ct.addrs)
      (reprOf a.2) →
    ∃ v : Vd, (a, v) ∈ ct.leafV

/-- REP NORMALIZATION AT REALIZED CHAINS — ADJUDICATED premise (iii) (A6 finisher
round, 2026-07-29; warrant = the necessity analysis formerly recorded at
`fibOf_partition`'s sorry site, its displayed missing lemma VERBATIM: "the
canonical-choice normalization law at realized chains; equivalently: strengthen
`ClassCover`'s classification clause by the conjunct `reprOf i = H`" — carried
here as the typed premise, the E-DEV-9 pattern): a realized chain classified into
class `i` IS `i`'s canonical representative. Necessity (the recorded analysis):
`fiberAt`'s clause (i) is a set-level GRAPH equality and `fibOf`'s `chains` is BY
CONSTRUCTION a `reprOf`-image, so with `reprOf i ≠ H` for a single realized pruned
chain no witness `ct` exists. Owner HC-2 (PresentNorm), the family of
`hrep`/`hri` — typed here, never proved here. -/
def RepNorm (T : TreeModel p F n N m pol) : Prop :=
  ∀ (H : History p F), (∃ y, T.mem (some H) y) →
    ∀ {P : Shape n} (i : PrefIdx n pol P), H ∈ PrefSet n pol P →
      SameClass i H → reprOf i = H

/-- the two `reprOf` defining clauses (PrefSet membership + `SameClass` of the
representative), as `hns_leaf`'s local `hspec` but shared by `hclosed`/`hleaf`. -/
private theorem reprOf_spec {Q : Shape n} (i : PrefIdx n pol Q) :
    reprOf i ∈ PrefSet n pol Q ∧ etaData (Q : ShapePrefix) (reprOf i) = i.1 :=
  i.2.choose_spec

/-- the `hri` read-off on sigma addresses (structure-eta face of `ReprInj`). -/
private theorem addr_inj (hri : ReprInj n pol)
    {a b : Σ P : Shape n, PrefIdx n pol P}
    (h : reprOf a.2 = reprOf b.2) : a = b :=
  hri a.2 b.2 h

open Classical in
/-- `hkeys.1`'s key uniqueness as element-level injectivity. -/
private theorem leafV_key_inj (ct : ClassTree n (F := F) pol)
    {av bv : (Σ P : Shape n, PrefIdx n pol P) × Vd}
    (ha : av ∈ ct.leafV) (hb : bv ∈ ct.leafV) (h : av.1 = bv.1) : av = bv :=
  Finset.card_image_iff.mp ct.hkeys.1 (Finset.mem_coe.mpr ha)
    (Finset.mem_coe.mpr hb) h

/-- `ClassTree` extensionality on the four DATA components (the proof fields close
by definitional proof irrelevance). -/
private theorem classTree_ext {ct ct' : ClassTree n (F := F) pol}
    (h1 : ct.addrs = ct'.addrs) (h2 : ct.leafV = ct'.leafV)
    (h3 : ct.nsMark = ct'.nsMark) (h4 : ct.rootV = ct'.rootV) : ct = ct' := by
  obtain ⟨A, hA, L, hL, M, hM, R, hR⟩ := ct
  obtain ⟨A', hA', L', hL', M', hM', R', hR'⟩ := ct'
  obtain rfl : A = A' := h1
  obtain rfl : L = L' := h2
  obtain rfl : M = M' := h3
  obtain rfl : R = R' := h4
  rfl

/-- `ClassPrefixOf` is IRREFLEXIVE at a fixed shape: both witnesses match the SAME
shape `P` (equal `nodes` lengths through `MatchesHist`), so the strict pair
`H'.IsPrefixOf H ∧ H' ≠ H` is impossible. Closes the `a' = a` leg of the
constructed `MaximalAddr` in `fibOf_partition`. -/
private theorem classPrefixOf_irrefl {P : Shape n} (i : PrefIdx n pol P) :
    ¬ ClassPrefixOf i i := by
  rintro ⟨H', H, h1, h2, -, -, hpre, hne⟩
  have hm1 : (P : ShapePrefix).MatchesHist H' := h1.1
  have hm2 : (P : ShapePrefix).MatchesHist H := h2.1
  obtain ⟨hlen1, -⟩ := hm1
  obtain ⟨hlen2, -⟩ := hm2
  exact hne (history_ext (List.IsPrefix.eq_of_length hpre (hlen1.trans hlen2.symm)))

open Classical in
/-- the per-address representative tree of a class tree. -/
noncomputable def fibOf (hrep : PrefixCoherentRepr n pol)
    (hri : ReprInj n pol)
    (hpr : RepPrefixClosed n pol)
    (ct : ClassTree n (F := F) pol)
    (hreg : LeafReg ct) : VTree p F where
  chains := (fun a : Σ P : Shape n, PrefIdx n pol P => reprOf a.2) '' ↑ct.addrs
  hfin := ct.addrs.finite_toSet.image _
  hne_nodes := fun H _ => H.nonempty
  hclosed := by
    rintro H ⟨a, ha, rfl⟩ H' hpre hne
    by_cases hEq : H' = reprOf a.2
    · exact hEq.symm ▸ Set.mem_image_of_mem _ ha
    · obtain ⟨P', i', hrepr, hcp⟩ := hpr a.2 H' hpre hne hEq
      exact ⟨⟨P', i'⟩,
        Finset.mem_coe.mpr (ct.haddr a (Finset.mem_coe.mp ha) ⟨P', i'⟩ hcp), hrepr⟩
  henV := ct.rootV
  hhen := ct.hroot
  leafV := fun H =>
    if h : ∃ av, av ∈ ct.leafV ∧ reprOf av.1.2 = H then some h.choose.2 else none
  hleaf := by
    intro H
    constructor
    · intro hsome
      by_cases hex : ∃ av, av ∈ ct.leafV ∧ reprOf av.1.2 = H
      · obtain ⟨av, hmem, heq⟩ := hex
        obtain ⟨haddr, hmaxa⟩ := ct.hkeys.2 av hmem
        subst heq
        refine ⟨Set.mem_image_of_mem _ (Finset.mem_coe.mpr haddr), ?_⟩
        rintro H'' ⟨b, hb, rfl⟩ hpre
        by_cases hEq : reprOf av.1.2 = reprOf b.2
        · exact hEq.symm
        · exact (hmaxa b (Finset.mem_coe.mp hb)
            ⟨reprOf av.1.2, reprOf b.2, (reprOf_spec av.1.2).1, (reprOf_spec b.2).1,
              (reprOf_spec av.1.2).2, (reprOf_spec b.2).2, hpre, hEq⟩).elim
      · rw [dif_neg hex] at hsome
        simp at hsome
    · rintro ⟨⟨a, ha, rfl⟩, hmax⟩
      obtain ⟨v, hv⟩ := hreg a (Finset.mem_coe.mp ha) hmax
      have hex : ∃ av, av ∈ ct.leafV ∧ reprOf av.1.2 = reprOf a.2 := ⟨(a, v), hv, rfl⟩
      rw [dif_pos hex]
      rfl
  nsLeaf := fun H => ∃ a ∈ ct.nsMark, reprOf a.2 = H
  hns_leaf := by
    intro H hH
    obtain ⟨a, ha, rfl⟩ := hH
    obtain ⟨v, hv⟩ := ct.hns a ha
    obtain ⟨ha_addr, hmax⟩ := ct.hkeys.2 (a, v) hv
    refine ⟨Set.mem_image_of_mem _ (Finset.mem_coe.mpr ha_addr), ?_⟩
    intro H'' hmem hpre
    obtain ⟨b, hb, hbeq⟩ := hmem
    by_cases hEq : reprOf a.2 = reprOf b.2
    · rw [← hbeq]; exact hEq.symm
    · exact (hmax b (Finset.mem_coe.mp hb)
        ⟨reprOf a.2, reprOf b.2, (reprOf_spec a.2).1, (reprOf_spec b.2).1,
          (reprOf_spec a.2).2, (reprOf_spec b.2).2,
          by rw [show reprOf b.snd = H'' from hbeq]; exact hpre, hEq⟩).elim

/-- the `fibOf` leaf lookup, characterized: `some v` at a representative iff the
entry is registered — `hri` keys the address, `hkeys.1` keys the value. -/
private theorem fibOf_leafV_some_iff (hrep : PrefixCoherentRepr n pol)
    (hri : ReprInj n pol) (hpr : RepPrefixClosed n pol)
    (ct : ClassTree n (F := F) pol) (hreg : LeafReg ct)
    (a : Σ P : Shape n, PrefIdx n pol P) (v : Vd) :
    (fibOf hrep hri hpr ct hreg).leafV (reprOf a.2) = some v ↔ (a, v) ∈ ct.leafV := by
  constructor
  · intro hsome
    by_cases hex : ∃ av, av ∈ ct.leafV ∧ reprOf av.1.2 = reprOf a.2
    · rw [show (fibOf hrep hri hpr ct hreg).leafV (reprOf a.2) = some hex.choose.2
          from dif_pos hex] at hsome
      obtain ⟨hcm, hce⟩ := hex.choose_spec
      have h2 : hex.choose.2 = v := Option.some.inj hsome
      have h3 : hex.choose = (a, v) := by
        rw [Prod.ext_iff]
        exact ⟨addr_inj hri hce, h2⟩
      exact h3 ▸ hcm
    · rw [show (fibOf hrep hri hpr ct hreg).leafV (reprOf a.2) = none
          from dif_neg hex] at hsome
      simp at hsome
  · intro hmem
    have hex : ∃ av, av ∈ ct.leafV ∧ reprOf av.1.2 = reprOf a.2 := ⟨(a, v), hmem, rfl⟩
    rw [show (fibOf hrep hri hpr ct hreg).leafV (reprOf a.2) = some hex.choose.2
        from dif_pos hex]
    obtain ⟨hcm, hce⟩ := hex.choose_spec
    have h2 : hex.choose = (a, v) := leafV_key_inj ct hcm hmem (addr_inj hri hce)
    rw [h2]

theorem fibOf_fiber_disjoint (hrep : PrefixCoherentRepr n pol)
    (hri : ReprInj n pol) (hpr : RepPrefixClosed n pol) {P : Shape n}
    (hwd : ClassFiberWelldef p F n N m pol P)
    (ct ct' : ClassTree n (F := F) pol) (h : ct ≠ ct')
    (hreg : LeafReg ct) (hreg' : LeafReg ct')
    (T : TreeModel p F n N m pol) (χ : Fin n → Fin m) :
    ¬ VTree.ext (fibOf hrep hri hpr ct hreg) (fibOf hrep hri hpr ct' hreg') ∧
    Disjoint {x | (fibOf hrep hri hpr ct hreg).fiberAt T χ x}
      {x | (fibOf hrep hri hpr ct' hreg').fiberAt T χ x} := by
  have hnext : ¬ VTree.ext (fibOf hrep hri hpr ct hreg)
      (fibOf hrep hri hpr ct' hreg') := by
    rintro ⟨hchains, hhenV, hlocal⟩
    apply h
    have hchains' :
        (fun b : Σ P : Shape n, PrefIdx n pol P => reprOf b.2) '' ↑ct.addrs
          = (fun b : Σ P : Shape n, PrefIdx n pol P => reprOf b.2) '' ↑ct'.addrs :=
      hchains
    -- (1) addrs: read off injectively via `hri`
    have haddrs : ct.addrs = ct'.addrs := by
      refine Finset.ext fun a => ⟨fun haA => ?_, fun haA => ?_⟩
      · obtain ⟨b, hb, hbe⟩ :=
          hchains' ▸ Set.mem_image_of_mem
            (fun b : Σ P : Shape n, PrefIdx n pol P => reprOf b.2)
            (Finset.mem_coe.mpr haA)
        exact addr_inj hri hbe ▸ Finset.mem_coe.mp hb
      · obtain ⟨b, hb, hbe⟩ :=
          hchains'.symm ▸ Set.mem_image_of_mem
            (fun b : Σ P : Shape n, PrefIdx n pol P => reprOf b.2)
            (Finset.mem_coe.mpr haA)
        exact addr_inj hri hbe ▸ Finset.mem_coe.mp hb
    -- (2) leaf entries: read off at the representative through the lookup
    have hleafVs : ct.leafV = ct'.leafV := by
      refine Finset.ext fun av => ⟨fun hav => ?_, fun hav => ?_⟩
      · have hmemc : reprOf av.1.2 ∈ (fibOf hrep hri hpr ct hreg).chains :=
          Set.mem_image_of_mem _ (Finset.mem_coe.mpr (ct.hkeys.2 av hav).1)
        have h1 : (fibOf hrep hri hpr ct hreg).leafV (reprOf av.1.2) = some av.2 :=
          (fibOf_leafV_some_iff hrep hri hpr ct hreg av.1 av.2).mpr hav
        have h2 : (fibOf hrep hri hpr ct' hreg').leafV (reprOf av.1.2) = some av.2 :=
          (hlocal _ hmemc).1 ▸ h1
        exact (fibOf_leafV_some_iff hrep hri hpr ct' hreg' av.1 av.2).mp h2
      · have hmemc : reprOf av.1.2
            ∈ (fun b : Σ P : Shape n, PrefIdx n pol P => reprOf b.2) '' ↑ct.addrs := by
          have hm : reprOf av.1.2
              ∈ (fun b : Σ P : Shape n, PrefIdx n pol P => reprOf b.2) '' ↑ct'.addrs :=
            Set.mem_image_of_mem _ (Finset.mem_coe.mpr (ct'.hkeys.2 av hav).1)
          exact hchains'.symm ▸ hm
        have h1 : (fibOf hrep hri hpr ct' hreg').leafV (reprOf av.1.2) = some av.2 :=
          (fibOf_leafV_some_iff hrep hri hpr ct' hreg' av.1 av.2).mpr hav
        have h2 : (fibOf hrep hri hpr ct hreg).leafV (reprOf av.1.2) = some av.2 :=
          ((hlocal _ hmemc).1).symm ▸ h1
        exact (fibOf_leafV_some_iff hrep hri hpr ct hreg av.1 av.2).mp h2
    -- (3) marks: read off through nsLeaf
    have hnsM : ct.nsMark = ct'.nsMark := by
      refine Finset.ext fun a => ⟨fun haM => ?_, fun haM => ?_⟩
      · obtain ⟨v, hv⟩ := ct.hns a haM
        have hmemc : reprOf a.2 ∈ (fibOf hrep hri hpr ct hreg).chains :=
          Set.mem_image_of_mem _ (Finset.mem_coe.mpr (ct.hkeys.2 (a, v) hv).1)
        have hns1 : (fibOf hrep hri hpr ct hreg).nsLeaf (reprOf a.2) := ⟨a, haM, rfl⟩
        obtain ⟨b, hbM, hbe⟩ := (hlocal _ hmemc).2.mp hns1
        exact addr_inj hri hbe ▸ hbM
      · obtain ⟨v, hv⟩ := ct'.hns a haM
        have hmemc : reprOf a.2
            ∈ (fun b : Σ P : Shape n, PrefIdx n pol P => reprOf b.2) '' ↑ct.addrs := by
          have hm : reprOf a.2
              ∈ (fun b : Σ P : Shape n, PrefIdx n pol P => reprOf b.2) '' ↑ct'.addrs :=
            Set.mem_image_of_mem _ (Finset.mem_coe.mpr (ct'.hkeys.2 (a, v) hv).1)
          exact hchains'.symm ▸ hm
        have hns2 : (fibOf hrep hri hpr ct' hreg').nsLeaf (reprOf a.2) := ⟨a, haM, rfl⟩
        obtain ⟨b, hbM, hbe⟩ := (hlocal _ hmemc).2.mpr hns2
        exact addr_inj hri hbe ▸ hbM
    -- (4) payload: henV IS rootV
    have hrootV : ct.rootV = ct'.rootV := hhenV
    exact classTree_ext haddrs hleafVs hnsM hrootV
  -- ¬ext trees have disjoint fibers (T-E9)
  refine ⟨hnext, Set.disjoint_left.mpr fun x hx hx' => hnext ?_⟩
  exact tree_fiber_disjoint _ _ T χ x hx hx'

/-- `fiberAt` is EXT-INVARIANT — the transfer leg of the adjudicated route: every
`fiberAt` clause reads only `chains`, `leafV`/`nsLeaf` ON chains (clauses (v)/(vi)
sum over `hfin.toFinset` = chains), and `henV`. -/
private theorem fiberAt_of_ext {Tr Tr' : VTree p F} (hext : VTree.ext Tr Tr')
    {T : TreeModel p F n N m pol} {χ : Fin n → Fin m} {x : Box p m}
    (hf : Tr'.fiberAt T χ x) : Tr.fiberAt T χ x := by
  obtain ⟨hchains, hhen, hlocal⟩ := hext
  obtain ⟨hi, hii, hiii, hiv, hv, hvi⟩ := hf
  have hmemTr : ∀ H : History p F, H ∈ Tr.chains ↔ H ∈ Tr'.chains :=
    fun H => by rw [hchains]
  have hmaxTr : ∀ H : History p F,
      IsMaximalIn Tr.chains H ↔ IsMaximalIn Tr'.chains H :=
    fun H => by rw [hchains]
  have htofin : Tr.hfin.toFinset = Tr'.hfin.toFinset := by
    ext H
    rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset, hchains]
  have hlvOn : ∀ H ∈ Tr'.hfin.toFinset, Tr.leafV H = Tr'.leafV H := fun H hH =>
    (hlocal H (by rw [hchains]; exact Tr'.hfin.mem_toFinset.mp hH)).1
  have htm : Tr.typemult = Tr'.typemult := by
    unfold VTree.typemult
    rw [hhen, htofin]
    congr 1
    exact Finset.sum_congr rfl fun H hH => by rw [hlvOn H hH]
  have hheads : Tr.heads = Tr'.heads := by
    unfold VTree.heads
    rw [htofin]
  have htd : Tr.trackDeg = Tr'.trackDeg := by
    funext H₀
    unfold VTree.trackDeg
    rw [htofin]
    exact Finset.sum_congr rfl fun H hH => by rw [hlvOn H hH]
  refine ⟨fun H => (hmemTr H).trans (hi H), ?_, hhen.trans hiii, ?_, ?_, ?_⟩
  · intro H hH hmax
    obtain ⟨hlvH, hnsH⟩ := hlocal H hH
    rw [hlvH, hnsH]
    exact hii H ((hmemTr H).mp hH) ((hmaxTr H).mp hmax)
  · intro H hH hnmax
    exact hiv H ((hmemTr H).mp hH) fun hc => hnmax ((hmaxTr H).mpr hc)
  · rw [htm]; exact hv
  · rw [hheads, htd]; exact hvi

theorem fibOf_partition (hrep : PrefixCoherentRepr n pol)
    (hri : ReprInj n pol) (hpr : RepPrefixClosed n pol)
    (T : TreeModel p F n N m pol)
    (hcov : ClassCover T) (hnorm : RepNorm T)
    (χ : Fin n → Fin m) (x : Box p m)
    (hx : Decided T χ x) :
    ∃ (ct : ClassTree n (F := F) pol) (hreg : LeafReg ct),
      (fibOf hrep hri hpr ct hreg).fiberAt T χ x := by
  -- ADJUDICATED ROUTE (A6 finisher round, 2026-07-29): `hnorm : RepNorm T` is the
  -- rep-normalization law the necessity analysis recorded here (see `RepNorm`).
  -- With it: ct := the classes of Tr.chains (Tr = the T-F1 `oneF` witness);
  -- chains (fibOf ct) = Tr.chains LITERALLY; `PrefixClosed`/`MaximalAddr`/`LeafReg`
  -- collapse to Tr's own hclosed/hleaf via `hrep`/`hri` + Tr.hfin; the fiberAt
  -- clauses transfer along `VTree.ext (fibOf ct) Tr` (`fiberAt_of_ext`).
  classical
  obtain ⟨Tr, hTr, -⟩ := oneF T χ x hx
  -- every chain is realized at x (fiberAt clause (i) + PrunedMem)
  have hmemOf : ∀ H ∈ Tr.chains, T.mem (some H) x :=
    fun H hH => ((hTr.1 H).mp hH).2.1
  -- hcov classifies each chain; hnorm NORMALIZES: the chain IS its representative
  have hAddrEx : ∀ H ∈ Tr.chains,
      ∃ a : Σ P : Shape n, PrefIdx n pol P, reprOf a.2 = H := by
    intro H hH
    obtain ⟨P, i, hPref, hSame, -⟩ := hcov H ⟨x, hmemOf H hH⟩
    exact ⟨⟨P, i⟩, hnorm H ⟨x, hmemOf H hH⟩ i hPref hSame⟩
  -- the address set: the classes whose representative is a chain (finite via `hri`)
  have hAfin : ((fun a : Σ P : Shape n, PrefIdx n pol P => reprOf a.2) ⁻¹'
      Tr.chains).Finite := by
    refine Set.Finite.preimage ?_ Tr.hfin
    intro a _ b _ hab
    exact addr_inj hri hab
  have hAmem : ∀ a : Σ P : Shape n, PrefIdx n pol P,
      (a ∈ hAfin.toFinset ↔ reprOf a.2 ∈ Tr.chains) := fun a => by
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage]
  -- the transported leaf entries, with their membership read-off
  have hLmem : ∀ (a : Σ P : Shape n, PrefIdx n pol P) (v : Vd),
      ((a, v) ∈ hAfin.toFinset.biUnion
          (fun b => (Tr.leafV (reprOf b.2)).elim ∅ (fun w => {(b, w)}))
        ↔ reprOf a.2 ∈ Tr.chains ∧ Tr.leafV (reprOf a.2) = some v) := by
    intro a v
    rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨b, hb, hmem⟩
      cases hcase : Tr.leafV (reprOf b.2) with
      | none =>
        rw [hcase, Option.elim_none] at hmem
        exact absurd hmem (Finset.notMem_empty _)
      | some w =>
        simp only [hcase, Option.elim_some, Finset.mem_singleton,
          Prod.mk.injEq] at hmem
        obtain ⟨rfl, rfl⟩ := hmem
        exact ⟨(hAmem _).mp hb, hcase⟩
    · rintro ⟨hchain, hsome⟩
      refine ⟨a, (hAmem a).mpr hchain, ?_⟩
      simp only [hsome, Option.elim_some, Finset.mem_singleton]
  -- the reprOf image of the addresses IS the chain set (hAddrEx supplies ⊇)
  have hchains_eq :
      (fun b : Σ P : Shape n, PrefIdx n pol P => reprOf b.2) '' ↑hAfin.toFinset
        = Tr.chains := by
    apply Set.Subset.antisymm
    · rintro H ⟨a, ha, rfl⟩
      exact (hAmem a).mp (Finset.mem_coe.mp ha)
    · intro H hH
      obtain ⟨a, ha⟩ := hAddrEx H hH
      exact ⟨a, Finset.mem_coe.mpr ((hAmem a).mpr (by rw [ha]; exact hH)), ha⟩
  -- LeafReg, over the data equations (record-projection-stable form)
  have hregGen : ∀ ct : ClassTree n (F := F) pol,
      ct.addrs = hAfin.toFinset →
      ct.leafV = hAfin.toFinset.biUnion
        (fun b => (Tr.leafV (reprOf b.2)).elim ∅ (fun w => {(b, w)})) →
      LeafReg ct := by
    intro ct hA hL a ha hmaxIn
    rw [hA] at ha
    rw [hA, hchains_eq] at hmaxIn
    have hchain : reprOf a.2 ∈ Tr.chains := (hAmem a).mp ha
    obtain ⟨v, hv⟩ :=
      Option.isSome_iff_exists.mp ((Tr.hleaf _).mpr ⟨hchain, hmaxIn⟩)
    exact ⟨v, by rw [hL]; exact (hLmem a v).mpr ⟨hchain, hv⟩⟩
  -- the ext tie fibOf(ct) ≈ Tr, over the data equations
  have hextGen : ∀ (ct : ClassTree n (F := F) pol) (hreg : LeafReg ct),
      ct.addrs = hAfin.toFinset →
      ct.leafV = hAfin.toFinset.biUnion
        (fun b => (Tr.leafV (reprOf b.2)).elim ∅ (fun w => {(b, w)})) →
      ct.nsMark = hAfin.toFinset.filter (fun b => Tr.nsLeaf (reprOf b.2)) →
      ct.rootV = Tr.henV →
      VTree.ext (fibOf hrep hri hpr ct hreg) Tr := by
    intro ct hreg hA hL hM hR
    have hcteq : (fibOf hrep hri hpr ct hreg).chains = Tr.chains := by
      change (fun b : Σ P : Shape n, PrefIdx n pol P => reprOf b.2) '' ↑ct.addrs
        = Tr.chains
      rw [hA]; exact hchains_eq
    refine ⟨hcteq, hR, ?_⟩
    rintro H ⟨a, ha, rfl⟩
    have haA : a ∈ hAfin.toFinset := by
      rw [← hA]; exact Finset.mem_coe.mp ha
    have hchain : reprOf a.2 ∈ Tr.chains := (hAmem a).mp haA
    constructor
    · -- leafV agreement at the representative
      cases hcase : Tr.leafV (reprOf a.2) with
      | some v =>
        exact (fibOf_leafV_some_iff hrep hri hpr ct hreg a v).mpr
          (by rw [hL]; exact (hLmem a v).mpr ⟨hchain, hcase⟩)
      | none =>
        cases hfo : (fibOf hrep hri hpr ct hreg).leafV (reprOf a.2) with
        | none => rfl
        | some w =>
          have hw := (fibOf_leafV_some_iff hrep hri hpr ct hreg a w).mp hfo
          rw [hL] at hw
          have hcontra := ((hLmem a w).mp hw).2
          rw [hcase] at hcontra
          cases hcontra
    · -- nsLeaf agreement at the representative
      constructor
      · rintro ⟨b, hb, hbe⟩
        rw [hM] at hb
        rw [← hbe]
        exact (Finset.mem_filter.mp hb).2
      · intro hns
        exact ⟨a, by rw [hM]; exact Finset.mem_filter.mpr ⟨haA, hns⟩, rfl⟩
  -- assemble the class tree; its four Prop fields close from the read-offs above
  refine ⟨⟨hAfin.toFinset, ?_,
      hAfin.toFinset.biUnion
        (fun b => (Tr.leafV (reprOf b.2)).elim ∅ (fun w => {(b, w)})),
      ⟨?_, ?_⟩,
      hAfin.toFinset.filter (fun b => Tr.nsLeaf (reprOf b.2)),
      ?_, Tr.henV, Tr.hhen⟩,
    hregGen _ rfl rfl,
    fiberAt_of_ext (hextGen _ (hregGen _ rfl rfl) rfl rfl rfl rfl) hTr⟩
  · -- haddr: PrefixClosed via hrep + Tr.hclosed
    intro a ha a' hcp
    have hchain : reprOf a.2 ∈ Tr.chains := (hAmem a).mp ha
    exact (hAmem a').mpr
      (Tr.hclosed _ hchain _ (hrep a.2 a'.2 hcp) (reprOf a'.2).nonempty)
  · -- hkeys.1: key uniqueness via the leafV read-off
    refine Finset.card_image_iff.mpr ?_
    intro av ha bv hb h
    obtain ⟨-, hsa⟩ := (hLmem av.1 av.2).mp (Finset.mem_coe.mp ha)
    obtain ⟨-, hsb⟩ := (hLmem bv.1 bv.2).mp (Finset.mem_coe.mp hb)
    rw [Prod.ext_iff]
    refine ⟨h, Option.some.inj ?_⟩
    rw [← hsa, ← hsb, h]
  · -- hkeys.2: registered ⇒ address + MaximalAddr (chain-maximality + irreflexivity)
    intro av hav
    obtain ⟨hchain, hsome⟩ := (hLmem av.1 av.2).mp hav
    refine ⟨(hAmem av.1).mpr hchain, ?_⟩
    intro a' ha' hcp
    have hmax : IsMaximalIn Tr.chains (reprOf av.1.2) :=
      ((Tr.hleaf _).mp (by rw [hsome]; rfl)).2
    have haa : a' = av.1 :=
      addr_inj hri (hmax _ ((hAmem a').mp ha') (hrep a'.2 av.1.2 hcp))
    subst haa
    exact classPrefixOf_irrefl _ hcp
  · -- hns: marked ⇒ registered (Tr.hns_leaf + Tr.hleaf)
    intro a ha
    obtain ⟨haA, hnsl⟩ := Finset.mem_filter.mp ha
    have hpair := Tr.hns_leaf _ hnsl
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((Tr.hleaf _).mpr hpair)
    exact ⟨v, (hLmem a v).mpr ⟨hpair.1, hv⟩⟩

end LeanUrat.MovesT
