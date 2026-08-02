/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.TDDefsV3

/-!
# B2D/TD3_digitsProd — `DigitsProdLaw` at the ledger instance: PROVED
  [B2DEF_LEAN unit TD-3; wave 1 — THE HARDEST HOLE, front 1; round 3]

Blueprint §5 TD-3 (+ the §5 hardest-hole call, [R2-G2 fold]). moves_ref: §B2-DEF
D.3(e)(ii.3)/(ii.4), D.8 (BOX), D.11 attainable product. deps: E2 v3
(`TDDefsV3`), TD-0. difficulty: **hardest**.

Proof skeleton (blueprint verbatim, transposed to the v3 clauses): (ii.3) =
`slots_disjoint` + `parent_box_disjoint` (v3; distinct pins hit disjoint leaf
sets — T9's display at FULL box-slot range) + (ii.4) = `pinned_forced` (unit
diagonal: each pinned leaf forced given predecessors — T12's display) +
`member_exists` (v3; D.11's existence half) ⟹ the level-N box splits as a
product over slot blocks (`member_split` + the support clauses; the parent
factor is 1 = `pinned_forced`-uniqueness × `member_exists`-existence) ⟹
card = ∏ (`semantics` + `slot_sem`/`slotDigits_sem` `blockCount`s). The
shallow-height regime rides the ATTAINABLE product (T11 dichotomy, discharged
inside TD-0's `slotDigits_sem` counts) — NEVER full alphabets (D¹¹c: the
uniform field-alphabet display is FALSE at shallow heights).

**STATEMENT ROUND 2 (v2, 2026-08-02) — this file's history in two rounds.**
Round 1 (v1, commit 5371139): the N-TD1 gate FAILED at the Lean statement
level (`verification/openmath/ntd1_td3_ledger_semantics_trace.py`: intended
MOVES D.11 finite-box counts match the product 3/3, the v1 statement fails
3/3) and `TD3_countermodel.lean` compiled the refutation:
`ledger_digitsProd_refuted` is the ¬∀ of the v1 closure (preserved verbatim
there as the record), and `not_digitsProd_of_lawful` shows EVERY v1-lawful
instance with `1 ≤ rho0` violates the law — the defect was E2's v1
`LedgerSemantics` (`Nat.card` over all of `Coord → ℕ` is empty-or-infinite
⟹ ≡ 0, against the positive `slot_count_val` product).
Round 2 (the `LedgerLawfulV2` restatement): TDDefsV2's finite-box semantics
(counts over `supportUnion` with `Fin q₀` values, the MOVES D.11
`#{f mod p^N}` reading the trace matched, [LHS-V2] 3/3).

**ROUND 2 REFUTED (2026-08-02, wave-2 prover run).** The v2 statement was
ALSO false as stated: `TD3v2_countermodel.lean` compiles
`ledger_digitsProd_v2_refuted` — the ¬∀ of the exact round-2 statement — via
two v2-LAWFUL witnesses: `cmL4` (Seam A: no member-existence clause) and
`cmL3` (Seam B: `parent_interior_disjoint` fences interior on-line slots
only). The round-2 statement is preserved verbatim inside that ¬∀ as the
refutation record.

**ROUND 3 (v3, 2026-08-08 wallclock 2026-08-02): RESTATED on `LedgerLawfulV3`
and PROVED.** The v3 pack (`TDDefsV3.lean`) adds exactly the two seam
clauses: `member_exists` (D.11's existence half) and `parent_box_disjoint`
(full parent/box-slot disjointness). Gate state for round 3: the N-TD1 trace
extended with parent-pinned instances (i4-v3/i5-v3, [GATE-V2] MATCH — the v2
SEMANTICS is unchanged in round 3; only the PACK grew) and the compiled
negative controls `cmL3_not_lawfulV3`/`cmL4_not_lawfulV3` (both round-2
witnesses fail v3 at exactly the added clauses). The proof below is the
MOVES D.11 product argument in full:

1. `semantics` reads the LHS as the finite-box count over `supportUnion`;
   `member_split` + the read-leaf conditions fold into per-slot conditions
   (`slot_coord_mem` keeps each read inside its own block).
2. `blockCount_union_split` + `blockCount_biUnion_prod` (proved here, general)
   factor the count over the disjoint decomposition
   `supportUnion = parentBlock ⊔ ⨆_{k ∈ boxSlots} slotBlock k`
   (`parent_box_disjoint` + `slots_disjoint`; `parent_support`/`slot_support`
   localize the conditions).
3. `parent_blockCount_one`: the parent factor is EXACTLY 1 — existence from
   `member_exists` (restrict the compiled member), uniqueness from
   `pinned_forced` by strong induction along the ≺-rank on the finite parent
   block (`CoordPrec` is a strict order: `coordPrec_trans`/`coordPrec_irrefl`),
   the member's own slot restrictions supplying the glue.
4. `slot_sem`/`slotDigits_sem` convert the slot factors; `Finset.prod_sdiff`
   splits box slots into the on-line digit factors and off-line height factors.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.style.show false

namespace LeanUrat.B2D

open LeanUrat.Scaffold LeanUrat.Scaffold.HDischarge.H2 LeanUrat.MovesC LedgerStratumData

variable {D : CensusData} {W : WindowDatum D} {P : ParentShape D W}

/-! ## The ≺-order is strict (for the rank induction on the parent block) -/

theorem coordPrec_trans {a b c : Coord} (hab : CoordPrec a b) (hbc : CoordPrec b c) :
    CoordPrec a c := by
  unfold CoordPrec at *
  omega

theorem coordPrec_irrefl (c : Coord) : ¬ CoordPrec c c := by
  unfold CoordPrec
  omega

/-! ## Box-vector plumbing: extension by zero, restriction, gluing -/

/-- Extension-by-zero of a box vector off its box — the `blockCount` carrier's
own reading, as a named map (definitionally equal to the lambda inside
`blockCount`/`LedgerSemanticsV2`/`member_exists`). -/
def boxExt (q : ℕ) (B : Finset Coord) (v : ↥B → Fin q) : Coord → ℕ :=
  fun c => if h : c ∈ B then (v ⟨c, h⟩ : ℕ) else 0

/-- Restriction of a box vector to a sub-box. -/
def boxRestrict (q : ℕ) {B B' : Finset Coord} (hsub : B ⊆ B') (v : ↥B' → Fin q) :
    ↥B → Fin q :=
  fun i => v ⟨i.1, hsub i.2⟩

/-- On the sub-box, the extension of the restriction reads the original values. -/
theorem boxExt_restrict_eq_on {q : ℕ} {B B' : Finset Coord} (hsub : B ⊆ B')
    (v : ↥B' → Fin q) : ∀ c ∈ B, boxExt q B' v c = boxExt q B (boxRestrict q hsub v) c := by
  intro c hc
  simp only [boxExt, boxRestrict]
  rw [dif_pos hc, dif_pos (hsub hc)]

/-- Glue a parent-block vector onto an ambient box vector: parent values on the
parent block, ambient values elsewhere (the D.11 existence-half constructor). -/
def parentGlue (q : ℕ) {Bp U : Finset Coord} (_ : Bp ⊆ U)
    (vp : ↥Bp → Fin q) (v : ↥U → Fin q) : ↥U → Fin q :=
  fun i => if h : i.1 ∈ Bp then vp ⟨i.1, h⟩ else v i

/-- The glue reads the parent values on the parent block. -/
theorem parentGlue_eq_on {q : ℕ} {Bp U : Finset Coord} (hsub : Bp ⊆ U)
    (vp : ↥Bp → Fin q) (v : ↥U → Fin q) :
    ∀ c ∈ Bp, boxExt q U (parentGlue q hsub vp v) c = boxExt q Bp vp c := by
  intro c hc
  simp only [boxExt, parentGlue]
  rw [dif_pos (hsub hc), dif_pos hc, dif_pos hc]

/-- The glue reads the ambient values off the parent block. -/
theorem parentGlue_eq_off {q : ℕ} {Bp U : Finset Coord} (hsub : Bp ⊆ U)
    (vp : ↥Bp → Fin q) (v : ↥U → Fin q) :
    ∀ c, c ∉ Bp → boxExt q U (parentGlue q hsub vp v) c = boxExt q U v c := by
  intro c hc
  simp only [boxExt, parentGlue]
  by_cases hU : c ∈ U
  · rw [dif_pos hU, dif_pos hU, dif_neg hc]
  · rw [dif_neg hU, dif_neg hU]

/-! ## The product-box counting lemmas (general; D.11's factorization core) -/

/-- The disjoint-union splitting equivalence: box vectors on `B₁ ∪ B₂`
satisfying a `B₁`-supported condition AND a `B₂`-supported condition are pairs
of per-part box vectors satisfying their own conditions. -/
def unionSplitEquiv (q : ℕ) (B₁ B₂ : Finset Coord) (hd : Disjoint B₁ B₂)
    (cond₁ cond₂ : (Coord → ℕ) → Prop)
    (h₁ : ∀ x y, (∀ c ∈ B₁, x c = y c) → (cond₁ x ↔ cond₁ y))
    (h₂ : ∀ x y, (∀ c ∈ B₂, x c = y c) → (cond₂ x ↔ cond₂ y)) :
    {v : ↥(B₁ ∪ B₂) → Fin q //
        cond₁ (boxExt q (B₁ ∪ B₂) v) ∧ cond₂ (boxExt q (B₁ ∪ B₂) v)}
      ≃ {v₁ : ↥B₁ → Fin q // cond₁ (boxExt q B₁ v₁)}
        × {v₂ : ↥B₂ → Fin q // cond₂ (boxExt q B₂ v₂)} where
  toFun v :=
    (⟨boxRestrict q Finset.subset_union_left v.1,
      (h₁ _ _ (boxExt_restrict_eq_on Finset.subset_union_left v.1)).mp v.2.1⟩,
     ⟨boxRestrict q Finset.subset_union_right v.1,
      (h₂ _ _ (boxExt_restrict_eq_on Finset.subset_union_right v.1)).mp v.2.2⟩)
  invFun w :=
    ⟨fun i => if h : i.1 ∈ B₁ then w.1.1 ⟨i.1, h⟩
      else w.2.1 ⟨i.1, (Finset.mem_union.mp i.2).resolve_left h⟩,
     by
      constructor
      · refine (h₁ _ _ fun c hc => ?_).mpr w.1.2
        simp only [boxExt]
        rw [dif_pos (Finset.mem_union_left B₂ hc), dif_pos hc, dif_pos hc]
      · refine (h₂ _ _ fun c hc => ?_).mpr w.2.2
        have hc1 : c ∉ B₁ := Finset.disjoint_right.mp hd hc
        simp only [boxExt]
        rw [dif_pos (Finset.mem_union_right B₁ hc), dif_pos hc, dif_neg hc1]⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    by_cases h : i.1 ∈ B₁
    · simp only [boxRestrict, dif_pos h]
    · simp only [boxRestrict, dif_neg h]
  right_inv w := by
    refine Prod.ext (Subtype.ext (funext fun i => ?_)) (Subtype.ext (funext fun i => ?_))
    · simp only [boxRestrict, dif_pos i.2]
    · simp only [boxRestrict, dif_neg (Finset.disjoint_right.mp hd i.2)]

/-- **Binary product-box split**: the block count of a conjunction of a
`B₁`-supported and a `B₂`-supported condition over the disjoint union is the
product of the per-part block counts. -/
theorem blockCount_union_split (q : ℕ) {B₁ B₂ : Finset Coord} (hd : Disjoint B₁ B₂)
    {cond₁ cond₂ : (Coord → ℕ) → Prop}
    (h₁ : ∀ x y, (∀ c ∈ B₁, x c = y c) → (cond₁ x ↔ cond₁ y))
    (h₂ : ∀ x y, (∀ c ∈ B₂, x c = y c) → (cond₂ x ↔ cond₂ y)) :
    blockCount q (B₁ ∪ B₂) (fun x => cond₁ x ∧ cond₂ x)
      = blockCount q B₁ cond₁ * blockCount q B₂ cond₂ := by
  have h := Nat.card_congr (unionSplitEquiv q B₁ B₂ hd cond₁ cond₂ h₁ h₂)
  rw [Nat.card_prod] at h
  exact h

/-- **Iterated product-box split** over a pairwise-disjoint block family: the
block count of "all per-part conditions" over the finite union is the product
of the per-part block counts. -/
theorem blockCount_biUnion_prod {ι : Type*} (q : ℕ) (s : Finset ι)
    (B : ι → Finset Coord) (cond : ι → (Coord → ℕ) → Prop)
    (hd : ∀ k ∈ s, ∀ k' ∈ s, k ≠ k' → Disjoint (B k) (B k'))
    (hsup : ∀ k ∈ s, ∀ x y, (∀ c ∈ B k, x c = y c) → (cond k x ↔ cond k y)) :
    blockCount q (s.biUnion B) (fun x => ∀ k ∈ s, cond k x)
      = ∏ k ∈ s, blockCount q (B k) (cond k) := by
  classical
  revert hd hsup
  induction s using Finset.induction_on with
  | empty =>
    intro _ _
    rw [Finset.biUnion_empty, Finset.prod_empty,
      blockCount_of_forall q ∅ _ (fun x k hk => absurd hk (Finset.notMem_empty k)),
      Finset.card_empty, pow_zero]
  | insert a t ha ih =>
    intro hd hsup
    have hmem : ∀ k ∈ t, k ∈ insert a t := fun k hk => Finset.mem_insert_of_mem hk
    have hane : ∀ k ∈ t, a ≠ k := fun k hk h => ha (h ▸ hk)
    have hcongr : ∀ x : Coord → ℕ, (∀ k ∈ insert a t, cond k x)
        ↔ (cond a x ∧ ∀ k ∈ t, cond k x) := fun x =>
      Finset.forall_mem_insert a t (fun k => cond k x)
    have hbisup : ∀ x y, (∀ c ∈ t.biUnion B, x c = y c) →
        ((∀ k ∈ t, cond k x) ↔ (∀ k ∈ t, cond k y)) := fun x y hxy =>
      ⟨fun H k hk => (hsup k (hmem k hk) x y fun c hc =>
          hxy c (Finset.mem_biUnion.mpr ⟨k, hk, hc⟩)).mp (H k hk),
       fun H k hk => (hsup k (hmem k hk) x y fun c hc =>
          hxy c (Finset.mem_biUnion.mpr ⟨k, hk, hc⟩)).mpr (H k hk)⟩
    have hdisj : Disjoint (B a) (t.biUnion B) :=
      (Finset.disjoint_biUnion_right _ _ _).mpr fun k hk =>
        hd a (Finset.mem_insert_self a t) k (hmem k hk) (hane k hk)
    rw [Finset.biUnion_insert, blockCount_congr q _ hcongr,
      blockCount_union_split q hdisj (hsup a (Finset.mem_insert_self a t)) hbisup,
      ih (fun k hk k' hk' h => hd k (hmem k hk) k' (hmem k' hk') h)
        (fun k hk => hsup k (hmem k hk)),
      Finset.prod_insert ha]

/-- **The support-union factorization** (D.11's product box at the ledger
datum): a parent-supported condition AND per-box-slot supported conditions
over `supportUnion` count as (parent factor) × ∏ (slot factors). Consumes the
v3 disjointness geometry. -/
theorem blockCount_supportUnion_prod (L : LedgerStratumData D W P)
    (condPar : (Coord → ℕ) → Prop) (condK : Fin (W.ℓ + 1) → (Coord → ℕ) → Prop)
    (hpar : ∀ x y, (∀ c ∈ L.parentBlock, x c = y c) → (condPar x ↔ condPar y))
    (hK : ∀ k ∈ W.boxSlots, ∀ x y, (∀ c ∈ L.slotBlock k, x c = y c) →
      (condK k x ↔ condK k y))
    (hdpar : ∀ k ∈ W.boxSlots, Disjoint L.parentBlock (L.slotBlock k))
    (hdslots : ∀ k k' : Fin (W.ℓ + 1), k ≠ k' → Disjoint (L.slotBlock k) (L.slotBlock k')) :
    blockCount L.q0 L.supportUnion (fun x => condPar x ∧ ∀ k ∈ W.boxSlots, condK k x)
      = blockCount L.q0 L.parentBlock condPar
        * ∏ k ∈ W.boxSlots, blockCount L.q0 (L.slotBlock k) (condK k) := by
  have hbi : ∀ x y, (∀ c ∈ W.boxSlots.biUnion L.slotBlock, x c = y c) →
      ((∀ k ∈ W.boxSlots, condK k x) ↔ ∀ k ∈ W.boxSlots, condK k y) := fun x y hxy =>
    ⟨fun H k hk => (hK k hk x y fun c hc =>
        hxy c (Finset.mem_biUnion.mpr ⟨k, hk, hc⟩)).mp (H k hk),
     fun H k hk => (hK k hk x y fun c hc =>
        hxy c (Finset.mem_biUnion.mpr ⟨k, hk, hc⟩)).mpr (H k hk)⟩
  have hd : Disjoint L.parentBlock (W.boxSlots.biUnion L.slotBlock) :=
    (Finset.disjoint_biUnion_right _ _ _).mpr hdpar
  show blockCount L.q0 (L.parentBlock ∪ W.boxSlots.biUnion L.slotBlock) _ = _
  rw [blockCount_union_split L.q0 hd hpar hbi,
    blockCount_biUnion_prod L.q0 W.boxSlots L.slotBlock condK
      (fun k _ k' _ hkk => hdslots k k' hkk) hK]

/-! ## The parent factor is one (existence × forcedness) -/

/-- **D.11's pinned-block step**: under the v3 pack the parent-block count is
EXACTLY 1 per counted realization — existence from `member_exists` (restrict
the compiled member to the parent block), uniqueness from `pinned_forced` by
strong induction along the finite ≺-rank on the parent block (`CoordPrec` is
irreflexive and transitive, so its rank on a finite block is a strict measure),
with the member's own slot restrictions gluing any two parent realizations
into full members. -/
theorem parent_blockCount_one (L : LedgerStratumData D W P) (hL : L.LedgerLawfulV3)
    {ρ : ℕ} (hρ : ρ < L.rho0) :
    blockCount L.q0 L.parentBlock (L.parentCond ρ) = 1 := by
  classical
  obtain ⟨v0, hv0⟩ := hL.member_exists ρ hρ
  have hpar_sub : L.parentBlock ⊆ L.supportUnion := Finset.subset_union_left
  -- the compiled member, named through `boxExt` (definitionally the same map)
  have hv0' : L.inStratum ρ (boxExt L.q0 L.supportUnion v0) := hv0
  have hv0split := (hL.member_split ρ _).mp hv0'
  -- any parent-block realization glues with the member's slot data to a full member
  have hglue_mem : ∀ vp : ↥L.parentBlock → Fin L.q0,
      L.parentCond ρ (boxExt L.q0 L.parentBlock vp) →
      L.inStratum ρ (boxExt L.q0 L.supportUnion (parentGlue L.q0 hpar_sub vp v0)) := by
    intro vp hvp
    refine (hL.member_split ρ _).mpr ⟨?_, ?_⟩
    · exact (hL.parent_support ρ _ _ (parentGlue_eq_on hpar_sub vp v0)).mpr hvp
    · intro k hk
      refine (hL.slot_support ρ k _ _ fun c hc => ?_).mpr (hv0split.2 k hk)
      exact parentGlue_eq_off hpar_sub vp v0 c
        (Finset.disjoint_right.mp (hL.parent_box_disjoint k hk) hc)
  -- EXISTENCE: the member's own parent restriction realizes the parent condition
  have hne : Nonempty {vp : ↥L.parentBlock → Fin L.q0 //
      L.parentCond ρ (boxExt L.q0 L.parentBlock vp)} :=
    ⟨⟨boxRestrict L.q0 hpar_sub v0,
      (hL.parent_support ρ _ _ (boxExt_restrict_eq_on hpar_sub v0)).mp hv0split.1⟩⟩
  -- UNIQUENESS: two parent realizations agree, by rank induction on ≺
  have hsub : Subsingleton {vp : ↥L.parentBlock → Fin L.q0 //
      L.parentCond ρ (boxExt L.q0 L.parentBlock vp)} := by
    constructor
    intro u w
    have hxu := hglue_mem u.1 u.2
    have hxw := hglue_mem w.1 w.2
    set x : Coord → ℕ := boxExt L.q0 L.supportUnion (parentGlue L.q0 hpar_sub u.1 v0) with hxdef
    set y : Coord → ℕ := boxExt L.q0 L.supportUnion (parentGlue L.q0 hpar_sub w.1 v0) with hydef
    -- off the parent block the two gluings agree (both read the member)
    have hoff : ∀ c, c ∉ L.parentBlock → x c = y c := fun c hc =>
      (parentGlue_eq_off hpar_sub u.1 v0 c hc).trans
        (parentGlue_eq_off hpar_sub w.1 v0 c hc).symm
    -- the ≺-rank on the parent block strictly drops along predecessors
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
    -- strong induction on the rank: pinned leaves are forced, so x = y on the block
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
    -- read the agreement back through the gluings
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

/-! ## TD-3, round 3: the theorem -/

set_option linter.unusedVariables false in
/-- **TD-3**: the (F) product-box face at the ledger instance — fiberwise
per-slot factorization of the prescribed-digit counts (on-line digit counts ×
off-line height counts). PROVED on the v3 pack (statement round 3; the v1/v2
rounds' refutation records live in `TD3_countermodel.lean` /
`TD3v2_countermodel.lean`). `hscope`/`hclean` are the standing CEN-J/LED(i)
guards of the TD statement family (H2 FreshLaws consumption pattern) — the
D.11 product argument itself never draws on them. -/
theorem ledger_digitsProd (L : LedgerStratumData D W P) (hL : L.LedgerLawfulV3)
    (hscope : LedgerScope W P) (hclean : LedgerClean D W P L.N) :
    DigitsProdLaw W P L.ledgerJoint := by
  classical
  intro q ρ hρ z hz
  by_cases hq : q = L.q0
  · subst hq
    have hρ0 : ρ < L.rho0 := by
      simpa [LedgerStratumData.ledgerJoint] using hρ
    simp only [LedgerStratumData.ledgerJoint, if_true]
    -- Step 1: the LHS is the finite-box count over the support union
    rw [(hL.semantics ρ hρ0).2 z]
    -- Step 2: fold the member split + the on-line read conditions per slot
    have hsplit : ∀ x, (L.inStratum ρ x ∧ ∀ k : ↥W.onLine, x (L.slotCoord k) = z k)
        ↔ (L.parentCond ρ x ∧ ∀ k ∈ W.boxSlots,
            (L.slotCond ρ k x ∧
              ∀ h : k ∈ W.onLine, x (L.slotCoord ⟨k, h⟩) = z ⟨k, h⟩)) := by
      intro x
      constructor
      · rintro ⟨hmem, hdig⟩
        obtain ⟨hpar, hslots⟩ := (hL.member_split ρ x).mp hmem
        exact ⟨hpar, fun k hk => ⟨hslots k hk, fun h => hdig ⟨k, h⟩⟩⟩
      · rintro ⟨hpar, hK⟩
        exact ⟨(hL.member_split ρ x).mpr ⟨hpar, fun k hk => (hK k hk).1⟩,
          fun k => (hK k.1 (W.honLine_box k.2)).2 k.2⟩
    rw [blockCount_congr L.q0 L.supportUnion hsplit]
    -- Step 3: factor over parentBlock ⊔ ⨆ slot blocks
    have hK_supp : ∀ k ∈ W.boxSlots, ∀ x y, (∀ c ∈ L.slotBlock k, x c = y c) →
        ((L.slotCond ρ k x ∧ ∀ h : k ∈ W.onLine, x (L.slotCoord ⟨k, h⟩) = z ⟨k, h⟩)
          ↔ (L.slotCond ρ k y ∧ ∀ h : k ∈ W.onLine, y (L.slotCoord ⟨k, h⟩) = z ⟨k, h⟩)) := by
      intro k hk x y hxy
      have hcoord : ∀ h : k ∈ W.onLine, x (L.slotCoord ⟨k, h⟩) = y (L.slotCoord ⟨k, h⟩) :=
        fun h => hxy _ (hL.slot_coord_mem ⟨k, h⟩)
      constructor
      · rintro ⟨hs, hr⟩
        exact ⟨(hL.slot_support ρ k x y hxy).mp hs, fun h => (hcoord h).symm.trans (hr h)⟩
      · rintro ⟨hs, hr⟩
        exact ⟨(hL.slot_support ρ k x y hxy).mpr hs, fun h => (hcoord h).trans (hr h)⟩
    rw [blockCount_supportUnion_prod L (L.parentCond ρ)
      (fun k x => L.slotCond ρ k x ∧ ∀ h : k ∈ W.onLine, x (L.slotCoord ⟨k, h⟩) = z ⟨k, h⟩)
      (hL.parent_support ρ) hK_supp hL.parent_box_disjoint hL.slots_disjoint]
    -- Step 4: the parent factor is one
    rw [parent_blockCount_one L hL hρ0, one_mul]
    -- Step 5: split the slot factors into on-line digit counts × off-line heights
    rw [← Finset.prod_sdiff W.honLine_box]
    have hoffl : ∀ k ∈ W.boxSlots \ W.onLine,
        blockCount L.q0 (L.slotBlock k)
          (fun x => L.slotCond ρ k x ∧
            ∀ h : k ∈ W.onLine, x (L.slotCoord ⟨k, h⟩) = z ⟨k, h⟩)
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
                ∀ h : k ∈ W.onLine, x (L.slotCoord ⟨k, h⟩) = z ⟨k, h⟩) := by
      rw [← Finset.prod_attach W.onLine (fun k =>
        blockCount L.q0 (L.slotBlock k)
          (fun x => L.slotCond ρ k x ∧
            ∀ h : k ∈ W.onLine, x (L.slotCoord ⟨k, h⟩) = z ⟨k, h⟩))]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [hL.slotDigits_sem ρ hρ0 k (z k)]
      exact (blockCount_congr _ _ fun x =>
        ⟨fun h => ⟨h.1, h.2 k.2⟩, fun h => ⟨h.1, fun hh => h.2⟩⟩).symm
    rw [Finset.prod_congr rfl hoffl, honl, mul_comm]
  · rw [ledger_rhoCount_off_support L q hq] at hρ
    omega

end LeanUrat.B2D

#print axioms LeanUrat.B2D.blockCount_union_split
#print axioms LeanUrat.B2D.blockCount_biUnion_prod
#print axioms LeanUrat.B2D.parent_blockCount_one
#print axioms LeanUrat.B2D.ledger_digitsProd
