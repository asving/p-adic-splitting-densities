/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.TDDefsV4
import LeanUrat.B2D.TD6_assembly

/-!
# B2D/TDV4_chain — the TD supply chain RE-PROVED on the d-leaf-read (v4) pack
  [huni-v2 repair unit; statement round 4 chain]

The huni refutation (`HuniProbe.lean` + note `HUNI_PROBE_2026-08-08.md`)
demanded the CHAIN be fixed, not just the law: `FreshReadsLaw` itself fails
at the v3 carrier's non-degenerate instances, so `fresh_of_transDeep`'s
output was undeliverable at d ≥ 2. This file re-proves the TD-1..TD-4 laws
and the TD-6 assembly on `LedgerLawfulV4` (TDDefsV4 — the d-leaf digit-code
read), leaving all H2 statements and the whole v1–v3 record byte-unchanged.

## What is a copy of what (dedup provenance, per-decl)

Every proof here is the round-3 proof with the read re-keyed — the ONLY
mathematical change is `x (slotCoord k)` → `slotRead x k` (+ the read's
block-support lemma `slotRead_congr` where `slot_coord_mem` localized the
old read). Per-decl provenance:

* `blockCount_read_partition_fn` ← TD2's `blockCount_read_partition`,
  generalized from coordinate reads `x (rd k)` to FUNCTIONAL reads `rd x k`
  (the coded d-leaf read is not a single coordinate); the original is the
  `rd := fun x k => x (coords k)` special case.
* `parent_blockCount_one_v4` ← TD3's `parent_blockCount_one`, verbatim on the
  v4 pack (it reads only the six read-FREE clauses: member_exists,
  member_split, the two supports, parent_box_disjoint, pinned_forced — all
  v3-verbatim in v4; the v3 original's signature demands the v3 pack, which a
  v4 datum deliberately does NOT satisfy, hence the twin).
* `ledger_floorsCharge_v4` / `ledger_fiberSum_v4` / `ledger_junctionPin_v4` /
  `ledger_digitsProd_v4` ← TD-1/TD-2/TD-4/TD-3, read-re-keyed as above.
* `ledger_leakFree_v4` ← TD-5's projection (the carrier reads only
  (ii.3)/(ii.4), untouched by the re-key).
* `transDeep_of_lawful_v4` / `transDeep_of_ledger_v4` / `ledger_freshRowOnV4`
  ← TD-6, family re-keyed `LedgerStrataV3` → `LedgerStrataV4`.

## Signature dispositions (the huni-v2 statement surface)

* `SlotUniformLaw`, `FreshReadsLaw`, `FreshClauses`, `TransDeep`,
  `fresh_of_transDeep`, `freshRowOn_of_transDeep`, `freshReads_of_digitsProd`
  (H2 layer): byte-UNCHANGED — the probe pinned the seam to the ledger read.
* `ledger_freshRowOn` (v3, TD6): STANDS as the round-3 record; its `huni`
  binder is unsatisfiable at d ≥ 2 non-degenerate censuses
  (`ledger_huni_face_false_at_tdD`) — the LIVE face is `ledger_freshRowOnV4`
  below, whose `huni` binder over `LedgerStrataV4` is SATISFIABLE at the
  transported countermodel instance (`HuniV4Probe.slotUniform_td2V4`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.B2D

open LeanUrat.Scaffold LeanUrat.Scaffold.HDischarge.H2 LeanUrat.MovesC
open LedgerStratumData LedgerStratumDataV4

variable {D : CensusData} {W : WindowDatum D} {P : ParentShape D W}

/-! ## The functional-read partition step (TD-2's core, generalized) -/

/-- **Read-fiber partition at a FUNCTIONAL read** (TD-2's
`blockCount_read_partition` with the coordinate read `x (rd k)` generalized
to `rd x k` — the coded d-leaf read is a sum of coordinates, not one): block
counts of "`cond` ∧ the reads equal `z`" summed over the full `Fin m` read
box recover the block count of `cond` alone. -/
theorem blockCount_read_partition_fn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q m : ℕ) (hm : 0 < m) (B : Finset Coord) (cond : (Coord → ℕ) → Prop)
    (rd : (Coord → ℕ) → ι → ℕ)
    (hrange : ∀ x, cond x → ∀ k : ι, rd x k < m) :
    ∑ z : ι → Fin m,
        blockCount q B (fun x => cond x ∧ ∀ k : ι, rd x k = (z k : ℕ))
      = blockCount q B cond := by
  classical
  have hcard : ∀ c : (Coord → ℕ) → Prop,
      blockCount q B c
        = (Finset.univ.filter (fun v : ↥B → Fin q => c (boxExt q B v))).card := by
    intro c
    unfold LedgerStratumData.blockCount
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype _
  set f : (↥B → Fin q) → (ι → Fin m) := fun v k =>
    if h : rd (boxExt q B v) k < m then ⟨rd (boxExt q B v) k, h⟩ else ⟨0, hm⟩
    with hf
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (f := f) (s := Finset.univ.filter (fun v : ↥B → Fin q => cond (boxExt q B v)))
    (t := Finset.univ) (fun v _ => Finset.mem_univ (f v))
  rw [hcard cond, hfiber]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [hcard]
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine and_congr_right fun hc => ?_
  constructor
  · intro hz
    funext k
    have hk := hrange _ hc k
    simp only [hf]
    rw [dif_pos hk]
    exact Fin.ext (hz k)
  · intro hz k
    have hk := hrange _ hc k
    have h1 := congrFun hz k
    simp only [hf] at h1
    rw [dif_pos hk] at h1
    exact congrArg Fin.val h1

/-! ## TD-1/TD-2/TD-4 at the v4 pack -/

set_option linter.unusedVariables false in
/-- **TD-1 at v4**: the (F) floors face — verbatim TD-1 (`slot_count_val` is
read-free; the v4 twin exists because the v2-pack signature is not satisfied
by a v4 datum). -/
theorem ledger_floorsCharge_v4 (L : LedgerStratumDataV4 D W P)
    (hL : L.LedgerLawfulV4) (hscope : LedgerScope W P)
    (hclean : LedgerClean D W P L.N) :
    FloorsChargeLaw W P L.toLedgerStratumData.ledgerJoint := by
  intro q ρ hρ k hk
  by_cases hq : q = L.q0
  · subst hq
    have hρ0 : ρ < L.rho0 := by
      simpa [LedgerStratumData.ledgerJoint] using hρ
    simp only [LedgerStratumData.ledgerJoint, if_true]
    exact hL.slot_count_val ρ hρ0 k hk
  · rw [ledger_rhoCount_off_support L.toLedgerStratumData q hq] at hρ
    omega

set_option linter.unusedVariables false in
/-- **TD-2 at v4**: the (F) aggregation seam — members partition over their
d-leaf READ-CODE vectors (`digit_range` keeps the codes in the `Fin (q₀^d)`
box; the partition core is the functional-read generalization above). -/
theorem ledger_fiberSum_v4 (L : LedgerStratumDataV4 D W P)
    (hL : L.LedgerLawfulV4) (hscope : LedgerScope W P)
    (hclean : LedgerClean D W P L.N) :
    FiberSumLaw W P L.toLedgerStratumData.ledgerJoint := by
  intro q ρ hρ
  by_cases hq : q = L.q0
  · subst hq
    have hρ0 : ρ < L.rho0 := by
      simpa [LedgerStratumData.ledgerJoint] using hρ
    simp only [LedgerStratumData.ledgerJoint, if_true]
    rw [(hL.semantics ρ hρ0).1]
    simp only [(hL.semantics ρ hρ0).2]
    exact blockCount_read_partition_fn L.q0 (L.q0 ^ D.d)
      (pow_pos (by have := L.hq0; omega) D.d) L.toLedgerStratumData.supportUnion
      (L.inStratum ρ) L.slotRead (hL.digit_range ρ hρ0)
  · rw [ledger_rhoCount_off_support L.toLedgerStratumData q hq] at hρ
    omega

set_option linter.unusedVariables false in
/-- **TD-4 at v4**: the (J) clause — the junction READ CODE is the
ρ-determined nonzero pin code; off-pin prescribed codes empty the cylinder
(via the re-keyed `junction` clause). Verbatim TD-4 modulo the read. -/
theorem ledger_junctionPin_v4 (L : LedgerStratumDataV4 D W P)
    (hL : L.LedgerLawfulV4) (hscope : LedgerScope W P)
    (hclean : LedgerClean D W P L.N) :
    JunctionPinLaw W P L.toLedgerStratumData.ledgerJoint := by
  intro hmt q ρ hρ
  by_cases hq : q = L.q0
  · subst hq
    have hρ0 : ρ < L.rho0 := by
      simpa [LedgerStratumData.ledgerJoint] using hρ
    refine ⟨L.pin ρ, L.hpin_ne ρ hρ0, L.hpin_lt ρ hρ0, fun hk z hz => ?_⟩
    simp only [LedgerStratumData.ledgerJoint, if_true]
    rw [(hL.semantics ρ hρ0).2 z]
    refine blockCount_of_not _ _ _ fun x hx => ?_
    exact hz ((hx.2 ⟨W.ks, hk⟩).symm.trans (hL.junction ρ hρ0 x hx.1 hk))
  · rw [ledger_rhoCount_off_support L.toLedgerStratumData q hq] at hρ
    omega

/-! ## TD-3 at the v4 pack (the D.11 product argument, read-re-keyed) -/

/-- **The parent factor is one, v4** — TD3's `parent_blockCount_one` verbatim
on the v4 pack: only the six read-FREE clauses enter (all v3-verbatim in v4),
so the proof is the round-3 proof unchanged. -/
theorem parent_blockCount_one_v4 (L : LedgerStratumDataV4 D W P)
    (hL : L.LedgerLawfulV4) {ρ : ℕ} (hρ : ρ < L.rho0) :
    blockCount L.q0 L.parentBlock (L.parentCond ρ) = 1 := by
  classical
  obtain ⟨v0, hv0⟩ := hL.member_exists ρ hρ
  have hpar_sub : L.parentBlock ⊆ L.toLedgerStratumData.supportUnion :=
    Finset.subset_union_left
  have hv0' : L.inStratum ρ (boxExt L.q0 L.toLedgerStratumData.supportUnion v0) := hv0
  have hv0split := (hL.member_split ρ _).mp hv0'
  have hglue_mem : ∀ vp : ↥L.parentBlock → Fin L.q0,
      L.parentCond ρ (boxExt L.q0 L.parentBlock vp) →
      L.inStratum ρ (boxExt L.q0 L.toLedgerStratumData.supportUnion
        (parentGlue L.q0 hpar_sub vp v0)) := by
    intro vp hvp
    refine (hL.member_split ρ _).mpr ⟨?_, ?_⟩
    · exact (hL.parent_support ρ _ _ (parentGlue_eq_on hpar_sub vp v0)).mpr hvp
    · intro k hk
      refine (hL.slot_support ρ k _ _ fun c hc => ?_).mpr (hv0split.2 k hk)
      exact parentGlue_eq_off hpar_sub vp v0 c
        (Finset.disjoint_right.mp (hL.parent_box_disjoint k hk) hc)
  have hne : Nonempty {vp : ↥L.parentBlock → Fin L.q0 //
      L.parentCond ρ (boxExt L.q0 L.parentBlock vp)} :=
    ⟨⟨boxRestrict L.q0 hpar_sub v0,
      (hL.parent_support ρ _ _ (boxExt_restrict_eq_on hpar_sub v0)).mp hv0split.1⟩⟩
  have hsub : Subsingleton {vp : ↥L.parentBlock → Fin L.q0 //
      L.parentCond ρ (boxExt L.q0 L.parentBlock vp)} := by
    constructor
    intro u w
    have hxu := hglue_mem u.1 u.2
    have hxw := hglue_mem w.1 w.2
    set x : Coord → ℕ := boxExt L.q0 L.toLedgerStratumData.supportUnion
      (parentGlue L.q0 hpar_sub u.1 v0) with hxdef
    set y : Coord → ℕ := boxExt L.q0 L.toLedgerStratumData.supportUnion
      (parentGlue L.q0 hpar_sub w.1 v0) with hydef
    have hoff : ∀ c, c ∉ L.parentBlock → x c = y c := fun c hc =>
      (parentGlue_eq_off hpar_sub u.1 v0 c hc).trans
        (parentGlue_eq_off hpar_sub w.1 v0 c hc).symm
    have hrank_lt : ∀ c ∈ L.parentBlock, ∀ c' ∈ L.parentBlock, CoordPrec c' c →
        (L.parentBlock.filter (fun c'' => CoordPrec c'' c')).card
          < (L.parentBlock.filter (fun c'' => CoordPrec c'' c)).card := by
      intro c hc c' hc' hprec
      apply Finset.card_lt_card
      have hsubset : L.parentBlock.filter (fun c'' => CoordPrec c'' c')
          ⊆ L.parentBlock.filter (fun c'' => CoordPrec c'' c) := by
        intro c'' hc''
        have h'' := Finset.mem_filter.mp hc''
        exact Finset.mem_filter.mpr ⟨h''.1, coordPrec_trans h''.2 hprec⟩
      rw [Finset.ssubset_iff_of_subset hsubset]
      exact ⟨c', Finset.mem_filter.mpr ⟨hc', hprec⟩,
        fun hmem => coordPrec_irrefl c' (Finset.mem_filter.mp hmem).2⟩
    have key : ∀ n, ∀ c ∈ L.parentBlock,
        (L.parentBlock.filter (fun c'' => CoordPrec c'' c)).card < n → x c = y c := by
      intro n
      induction n with
      | zero => exact fun c _ h => absurd h (Nat.not_lt_zero _)
      | succ n ih =>
        intro c hc hn
        refine hL.pinned_forced ρ hρ c hc x y hxu hxw fun c' hprec => ?_
        by_cases hc' : c' ∈ L.parentBlock
        · exact ih c' hc' (by have := hrank_lt c hc c' hc' hprec; omega)
        · exact hoff c' hc'
    have hpb : ∀ c ∈ L.parentBlock, x c = y c := fun c hc =>
      key ((L.parentBlock.filter (fun c'' => CoordPrec c'' c)).card + 1) c hc
        (Nat.lt_succ_self _)
    apply Subtype.ext
    funext i
    refine Fin.ext ?_
    have hui : (u.1 i : ℕ) = x i.1 := by
      rw [hxdef]
      simp only [boxExt, parentGlue]
      rw [dif_pos (hpar_sub i.2), dif_pos i.2]
    have hwi : (w.1 i : ℕ) = y i.1 := by
      rw [hydef]
      simp only [boxExt, parentGlue]
      rw [dif_pos (hpar_sub i.2), dif_pos i.2]
    rw [hui, hwi]
    exact hpb i.1 i.2
  exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, hne⟩

set_option linter.unusedVariables false in
/-- **TD-3 at v4**: the (F) product-box face at the d-leaf read — TD3's
round-3 D.11 product argument with the prescribed-read conditions keyed by
`slotRead` (block-local by `slot_coords_mem` + `slotRead_congr`); the
factorization core (`blockCount_supportUnion_prod`) and the parent-factor
step are consumed/copied read-free. -/
theorem ledger_digitsProd_v4 (L : LedgerStratumDataV4 D W P)
    (hL : L.LedgerLawfulV4) (hscope : LedgerScope W P)
    (hclean : LedgerClean D W P L.N) :
    DigitsProdLaw W P L.toLedgerStratumData.ledgerJoint := by
  classical
  intro q ρ hρ z hz
  by_cases hq : q = L.q0
  · subst hq
    have hρ0 : ρ < L.rho0 := by
      simpa [LedgerStratumData.ledgerJoint] using hρ
    simp only [LedgerStratumData.ledgerJoint, if_true]
    rw [(hL.semantics ρ hρ0).2 z]
    have hsplit : ∀ x, (L.inStratum ρ x ∧ ∀ k : ↥W.onLine, L.slotRead x k = z k)
        ↔ (L.parentCond ρ x ∧ ∀ k ∈ W.boxSlots,
            (L.slotCond ρ k x ∧
              ∀ h : k ∈ W.onLine, L.slotRead x ⟨k, h⟩ = z ⟨k, h⟩)) := by
      intro x
      constructor
      · rintro ⟨hmem, hdig⟩
        obtain ⟨hpar, hslots⟩ := (hL.member_split ρ x).mp hmem
        exact ⟨hpar, fun k hk => ⟨hslots k hk, fun h => hdig ⟨k, h⟩⟩⟩
      · rintro ⟨hpar, hK⟩
        exact ⟨(hL.member_split ρ x).mpr ⟨hpar, fun k hk => (hK k hk).1⟩,
          fun k => (hK k.1 (W.honLine_box k.2)).2 k.2⟩
    rw [blockCount_congr L.q0 L.toLedgerStratumData.supportUnion hsplit]
    have hK_supp : ∀ k ∈ W.boxSlots, ∀ x y, (∀ c ∈ L.slotBlock k, x c = y c) →
        ((L.slotCond ρ k x ∧ ∀ h : k ∈ W.onLine, L.slotRead x ⟨k, h⟩ = z ⟨k, h⟩)
          ↔ (L.slotCond ρ k y ∧ ∀ h : k ∈ W.onLine, L.slotRead y ⟨k, h⟩ = z ⟨k, h⟩)) := by
      intro k hk x y hxy
      have hread : ∀ h : k ∈ W.onLine, L.slotRead x ⟨k, h⟩ = L.slotRead y ⟨k, h⟩ :=
        fun h => slotRead_congr L (hL.slot_coords_mem ⟨k, h⟩) hxy
      constructor
      · rintro ⟨hs, hr⟩
        exact ⟨(hL.slot_support ρ k x y hxy).mp hs, fun h => (hread h).symm.trans (hr h)⟩
      · rintro ⟨hs, hr⟩
        exact ⟨(hL.slot_support ρ k x y hxy).mpr hs, fun h => (hread h).trans (hr h)⟩
    rw [blockCount_supportUnion_prod L.toLedgerStratumData (L.parentCond ρ)
      (fun k x => L.slotCond ρ k x ∧ ∀ h : k ∈ W.onLine, L.slotRead x ⟨k, h⟩ = z ⟨k, h⟩)
      (hL.parent_support ρ) hK_supp hL.parent_box_disjoint hL.slots_disjoint]
    rw [parent_blockCount_one_v4 L hL hρ0, one_mul]
    rw [← Finset.prod_sdiff W.honLine_box]
    have hoffl : ∀ k ∈ W.boxSlots \ W.onLine,
        blockCount L.q0 (L.slotBlock k)
          (fun x => L.slotCond ρ k x ∧
            ∀ h : k ∈ W.onLine, L.slotRead x ⟨k, h⟩ = z ⟨k, h⟩)
          = L.cylSlot ρ k := by
      intro k hk
      obtain ⟨hkbox, hknot⟩ := Finset.mem_sdiff.mp hk
      rw [hL.slot_sem ρ hρ0 k hkbox]
      exact blockCount_congr _ _ fun x =>
        ⟨fun h => h.1, fun h => ⟨h, fun hh => absurd hh hknot⟩⟩
    have honl : ∏ k ∈ W.onLine.attach, L.cylSlotDigits ρ k (z k)
        = ∏ k ∈ W.onLine,
            blockCount L.q0 (L.slotBlock k)
              (fun x => L.slotCond ρ k x ∧
                ∀ h : k ∈ W.onLine, L.slotRead x ⟨k, h⟩ = z ⟨k, h⟩) := by
      rw [← Finset.prod_attach W.onLine (fun k =>
        blockCount L.q0 (L.slotBlock k)
          (fun x => L.slotCond ρ k x ∧
            ∀ h : k ∈ W.onLine, L.slotRead x ⟨k, h⟩ = z ⟨k, h⟩))]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [hL.slotDigits_sem ρ hρ0 k (z k)]
      exact (blockCount_congr _ _ fun x =>
        ⟨fun h => ⟨h.1, h.2 k.2⟩, fun h => ⟨h.1, fun hh => h.2⟩⟩).symm
    rw [Finset.prod_congr rfl hoffl, honl, mul_comm]
  · rw [ledger_rhoCount_off_support L.toLedgerStratumData q hq] at hρ
    omega

/-! ## TD-5 projection + TD-6 assembly at the v4 pack -/

/-- **TD-5 at v4**: the typed (L) carrier — the (ii.3)/(ii.4) projection,
untouched by the read re-key. -/
theorem ledger_leakFree_v4 (L : LedgerStratumDataV4 D W P)
    (hL : L.LedgerLawfulV4) : LeakFreeCarrier L.toLedgerStratumData :=
  ⟨hL.parent_interior_disjoint, hL.pinned_forced⟩

/-- **The row at the presenting v4 datum** (TD-6's builder, round 4): a
v4-lawful d-leaf-read datum's q-generic carrier satisfies the (TRANS-DEEP)
row, with `leakFree := LeakFreeCarrier` of the presenting datum ([R2-G1]
plug, inspectable by `rfl` below). -/
noncomputable def transDeep_of_lawful_v4 (L : LedgerStratumDataV4 D W P)
    (hL : L.LedgerLawfulV4) (hscope : LedgerScope W P)
    (hclean : LedgerClean D W P L.N) :
    TransDeep W P L.toLedgerStratumData.ledgerJoint where
  floorsCharge := ledger_floorsCharge_v4 L hL hscope hclean
  digitsProd := ledger_digitsProd_v4 L hL hscope hclean
  fiberSum := ledger_fiberSum_v4 L hL hscope hclean
  leakFree := LeakFreeCarrier L.toLedgerStratumData
  junctionPin := ledger_junctionPin_v4 L hL hscope hclean

/-- **TD-6 at v4, the row supplier**: every member of the v4 designated
family, in the scope/clean regime, satisfies the (TRANS-DEEP) row. -/
noncomputable def transDeep_of_ledger_v4 (J : JointStratum D W P)
    (hJ : J ∈ LedgerStrataV4 D W P) (hscope : LedgerScope W P)
    (hclean : LedgerClean D W P J.N) :
    TransDeep W P J := by
  have hJ' : ∃ L : LedgerStratumDataV4 D W P,
      L.LedgerLawfulV4 ∧ J = L.toLedgerStratumData.ledgerJoint := hJ
  have hclean' : LedgerClean D W P hJ'.choose.N := by
    have h := hJ'.choose_spec.2
    rw [h] at hclean
    exact hclean
  have key : TransDeep W P hJ'.choose.toLedgerStratumData.ledgerJoint :=
    transDeep_of_lawful_v4 hJ'.choose hJ'.choose_spec.1 hscope hclean'
  rw [hJ'.choose_spec.2]
  exact key

/-- **The huni-v2 family face** (`ledger_freshRowOn` re-keyed to the v4
family): the d-leaf-read ledger strata deliver BP_IV C5′'s `FreshRowOn`
binder, `huni` displayed as before ((ADM) + (GR-B)-line content, never
supplied here) — but now over a carrier family where the binder is
SATISFIABLE at d ≥ 2 (`HuniV4Probe.slotUniform_td2V4`), where the v3 face
was compiled-unsatisfiable (`ledger_huni_face_false_at_tdD`). -/
theorem ledger_freshRowOnV4 (D : CensusData)
    (hscope : ∀ (W : WindowDatum D) (P : ParentShape D W),
      LedgerScope W P)
    (hclean : ∀ (W : WindowDatum D) (P : ParentShape D W),
      ∀ J ∈ LedgerStrataV4 D W P, LedgerClean D W P J.N)
    (huni : ∀ (W : WindowDatum D) (P : ParentShape D W),
      ∀ J ∈ LedgerStrataV4 D W P, SlotUniformLaw W P J) :
    FreshRowOn D (fun W P => LedgerStrataV4 D W P) :=
  freshRowOn_of_transDeep D (fun W P => LedgerStrataV4 D W P)
    (fun W P J hJ => transDeep_of_ledger_v4 J hJ (hscope W P) (hclean W P J hJ))
    huni

/-- **The [R2-G1] plug, v4**: at the presenting datum the row's `leakFree`
field IS TD-5's typed carrier — `rfl`, never `True`. -/
theorem transDeep_of_lawful_v4_leakFree (L : LedgerStratumDataV4 D W P)
    (hL : L.LedgerLawfulV4) (hscope : LedgerScope W P)
    (hclean : LedgerClean D W P L.N) :
    (transDeep_of_lawful_v4 L hL hscope hclean).leakFree
      = LeakFreeCarrier L.toLedgerStratumData := rfl

end LeanUrat.B2D

#print axioms LeanUrat.B2D.blockCount_read_partition_fn
#print axioms LeanUrat.B2D.ledger_floorsCharge_v4
#print axioms LeanUrat.B2D.ledger_fiberSum_v4
#print axioms LeanUrat.B2D.ledger_junctionPin_v4
#print axioms LeanUrat.B2D.parent_blockCount_one_v4
#print axioms LeanUrat.B2D.ledger_digitsProd_v4
#print axioms LeanUrat.B2D.ledger_leakFree_v4
#print axioms LeanUrat.B2D.transDeep_of_lawful_v4
#print axioms LeanUrat.B2D.transDeep_of_ledger_v4
#print axioms LeanUrat.B2D.ledger_freshRowOnV4
#print axioms LeanUrat.B2D.transDeep_of_lawful_v4_leakFree
