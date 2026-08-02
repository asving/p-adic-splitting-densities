/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.TDDefs

/-!
# B2D/TD3_countermodel — `ledger_digitsProd` (unit TD-3) is REFUTED as stated
  [B2DEF_LEAN units TD-0/TD-3; wave 1, hardest hole, front 1 — FAILURE OUTCOME]

Blueprint: `lean/blueprints/B2DEF_LEAN_2026-08-08.md` §5 (TD-0/TD-3 + the
hardest-hole call: "the one unit whose STATEMENT might fail at the skeletal
carrier"). It does fail — but at the E2 SEMANTICS SEAM, not at shallow heights.

## The trace that gated this (N-TD1 discipline, run BEFORE proof effort)

`verification/openmath/ntd1_td3_ledger_semantics_trace.py` (2026-08-02): at 3
shallow concrete ledger instances the intended MOVES D.11 finite-box counts
match the per-slot product EXACTLY (3/3 — the accepted §B2-DEF mathematics is
sound), while the landed Lean statement fails 3/3: the `LedgerSemantics` left
side is `Nat.card` over ALL of `Coord → ℕ` and is 0, the product side is
positive.

## The defect, precisely (TDDefs design flag 1 turned inconsistent)

`LedgerSemantics` (TDDefs.lean) defines `cylFiber`/`cylFiberDigits` as
`Nat.card {x : Coord → ℕ // …}` — `Coord = ℕ × ℕ` is INFINITE and the digit
values are UNBOUNDED. But `LedgerLawful.member_split` + `parent_support` +
`slot_support` force membership to read ONLY the finite block union, so every
nonempty stratum set is infinite (`Nat.card = 0`) and every empty one is 0:
`lawful_cylFiberDigits_eq_zero` below. Design flag 1's demanded box-supported
member predicate is therefore CONTRADICTORY with lawfulness on nonempty strata
— and emptiness does not rescue the law, because `slot_count_val` forces every
off-line factor of the product side to the positive value `q0^(mN − s(·))` and
`slot_sem`/`slotDigits_sem` then produce an in-range digit vector with all
on-line factors positive (`hpin_ne`/`hpin_lt` force `d ≥ 1`, so witness reads
are in range). Hence — `not_digitsProd_of_lawful` — EVERY lawful instance with
`1 ≤ rho0` refutes `DigitsProdLaw` at its `ledgerJoint`: no TD-0 instance
choice can rescue TD-3, and TD-0's de-vacuity duty (c) in the R0Instance sense
(positive fiber counts) is impossible (`lawful_fiber_devacuify_impossible`).
Lawful instances DO exist (`cmL_lawful` below, with `rho0 = 1`, `LedgerScope`,
`LedgerClean` — so the refutation is not by vacuous lawfulness), giving the
compiled negation `ledger_digitsProd_refuted` of TD-3's exact ∀-statement.

ADJACENT CONSEQUENCE, recorded: with `cylFiberDigits ≡ 0` forced, TD-2's
`FiberSumLaw` (0 = 0) and TD-4's `JunctionPinLaw` (all fibers vanish) become
VACUOUSLY satisfiable — the E2 semantics layer degenerates the whole counting
content, so the re-architecture (a FRESH E2 statement round: count
BOX-RESTRICTED assignments, i.e. the `blockCount` pattern `Nat.card
{x : ↥box → Fin q0 // …}` at a level-N box Finset, per MOVES D.11's
`#{f mod p^N}`) must precede ALL of TD-0..TD-6, not just TD-3. Statement
fence respected: no landed file is touched; TD-3's E-phase sorry STANDS as
refuted-open pending the E2 revision.

**RESOLUTION RECORD (2026-08-02, the E2 v2 round — this file is now the
CLOSED refutation record).** The demanded re-architecture LANDED:
`TDDefsV2.lean` restates the semantics as finite-box `blockCount`s over
`supportUnion` (parent block ∪ box-slot blocks, `Fin q0` values), and
`TD3v2_control.lean` compiles the check that THIS file's mechanism does not
apply there — `cm2_digitsProd` (the law HOLDS, proved, at the v2 control
`cmL2`, same shape as `cmL` below), `v2_mechanism_inapplicable` (the ¬∀ of
`not_digitsProd_of_lawful`'s v2 transposition), `v2_devacuify_possible`
(duty (c) restored), `cmL_not_lawfulV2` (this file's witness does not port).
TD-1..TD-6 are restated on `LedgerLawfulV2`/`LedgerStrataV2`. Every theorem
below stands byte-unchanged; nothing here may be cited as evidence about the
v2 statements beyond the control file's compiled bridges.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.B2D

open LeanUrat.Scaffold LeanUrat.Scaffold.HDischarge.H2 LeanUrat.MovesC LedgerStratumData

/-! ## Part 1 — the general refutation: every lawful ledger instance with
`1 ≤ rho0` violates `DigitsProdLaw` at its `ledgerJoint`. -/

section General

variable {D : CensusData} {W : WindowDatum D} {P : ParentShape D W}

/-- The finite coordinate perimeter a lawful instance's membership can read
(`member_split` + the two support clauses). -/
def blockUnion (L : LedgerStratumData D W P) : Finset Coord :=
  L.parentBlock ∪ Finset.univ.biUnion L.slotBlock

theorem slotCoord_mem_blockUnion (L : LedgerStratumData D W P)
    (hL : L.LedgerLawful) (k : ↥W.onLine) : L.slotCoord k ∈ blockUnion L :=
  Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨(k : Fin (W.ℓ + 1)), Finset.mem_univ _, hL.slot_coord_mem k⟩)

/-- Lawful membership depends only on the block union. -/
theorem lawful_inStratum_congr (L : LedgerStratumData D W P)
    (hL : L.LedgerLawful) (ρ : ℕ) {x y : Coord → ℕ}
    (hxy : ∀ c ∈ blockUnion L, x c = y c) :
    L.inStratum ρ x ↔ L.inStratum ρ y := by
  rw [hL.member_split ρ x, hL.member_split ρ y]
  refine and_congr
    (hL.parent_support ρ x y fun c hc => hxy c (Finset.mem_union_left _ hc)) ?_
  refine forall₂_congr fun k _ => ?_
  exact hL.slot_support ρ k x y fun c hc => hxy c
    (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hc⟩))

/-- THE SEAM, isolated: a predicate on `Coord → ℕ` that reads only a finite
coordinate set has degenerate `Nat.card` — its satisfaction set is empty or
infinite (vary any unread coordinate), so the count is 0 either way. -/
theorem card_zero_of_finite_support (U : Finset Coord)
    (Q : (Coord → ℕ) → Prop)
    (hQ : ∀ x y : Coord → ℕ, (∀ c ∈ U, x c = y c) → Q x → Q y) :
    Nat.card {x : Coord → ℕ // Q x} = 0 := by
  rw [Nat.card_eq_zero]
  rcases isEmpty_or_nonempty {x : Coord → ℕ // Q x} with h | ⟨⟨x₀, hx₀⟩⟩
  · exact Or.inl h
  · refine Or.inr ?_
    obtain ⟨c₀, hc₀⟩ := Infinite.exists_notMem_finset U
    refine Infinite.of_injective
      (fun n : ℕ => (⟨Function.update x₀ c₀ n,
        hQ x₀ _ (fun c hc =>
          (Function.update_of_ne (fun hcc => hc₀ (by rw [← hcc]; exact hc)) n x₀).symm) hx₀⟩ :
        {x : Coord → ℕ // Q x})) ?_
    intro a b hab
    have h := congrArg (fun s : {x : Coord → ℕ // Q x} => s.1 c₀) hab
    simpa [Function.update_self] using h

/-- Degeneracy of the fiber semantics: at every considered realization the
height-only fiber count of a lawful instance is FORCED to 0. (This is also
the impossibility of TD-0's de-vacuity duty in the `R0Instance` sense.) -/
theorem lawful_cylFiber_eq_zero (L : LedgerStratumData D W P)
    (hL : L.LedgerLawful) {ρ : ℕ} (hρ : ρ < L.rho0) : L.cylFiber ρ = 0 := by
  rw [(hL.semantics ρ hρ).1]
  exact card_zero_of_finite_support (blockUnion L) _
    (fun x y hxy => (lawful_inStratum_congr L hL ρ hxy).mp)

/-- Degeneracy of the digit-vector semantics: every prescribed-digit fiber
count of a lawful instance is FORCED to 0. -/
theorem lawful_cylFiberDigits_eq_zero (L : LedgerStratumData D W P)
    (hL : L.LedgerLawful) {ρ : ℕ} (hρ : ρ < L.rho0) (z : ↥W.onLine → ℕ) :
    L.cylFiberDigits ρ z = 0 := by
  rw [(hL.semantics ρ hρ).2 z]
  refine card_zero_of_finite_support (blockUnion L) _ (fun x y hxy hx => ?_)
  exact ⟨(lawful_inStratum_congr L hL ρ hxy).mp hx.1, fun k => by
    rw [← hxy (L.slotCoord k) (slotCoord_mem_blockUnion L hL k)]; exact hx.2 k⟩

theorem lawful_fiber_devacuify_impossible (L : LedgerStratumData D W P)
    (hL : L.LedgerLawful) : ¬ ∃ ρ, ρ < L.rho0 ∧ 0 < L.cylFiber ρ := by
  rintro ⟨ρ, hρ, hpos⟩
  rw [lawful_cylFiber_eq_zero L hL hρ] at hpos
  exact lt_irrefl 0 hpos

/-- The product side never vanishes: each on-line slot has an in-range digit
value with positive count (from `slot_sem` + `slot_count_val` nonemptiness
through `slotDigits_sem`; `hpin_ne`/`hpin_lt` force `D.d ≥ 1` so the witness
read is in the `Fin (q0^d)` code range). -/
theorem lawful_exists_digit_witness (L : LedgerStratumData D W P)
    (hL : L.LedgerLawful) (hrho : 0 < L.rho0) (k : ↥W.onLine) :
    ∃ zk : ℕ, zk < L.q0 ^ D.d ∧ L.cylSlotDigits 0 k zk ≠ 0 := by
  have hq0 : (1 : ℕ) ≤ L.q0 := by have := L.hq0; omega
  have hd : D.d ≠ 0 := by
    intro h0
    have h1 := L.hpin_ne 0 hrho
    have h2 := L.hpin_lt 0 hrho
    rw [h0, pow_zero] at h2
    omega
  have hkbox : (k : Fin (W.ℓ + 1)) ∈ W.boxSlots := W.honLine_box k.2
  have hbc : blockCount L.q0 (L.slotBlock (k : Fin (W.ℓ + 1)))
      (L.slotCond 0 (k : Fin (W.ℓ + 1))) ≠ 0 := by
    rw [← hL.slot_sem 0 hrho (k : Fin (W.ℓ + 1)) hkbox,
      hL.slot_count_val 0 hrho (k : Fin (W.ℓ + 1)) hkbox]
    exact pow_ne_zero _ (by omega)
  simp only [LedgerStratumData.blockCount] at hbc
  obtain ⟨v, hv⟩ := (Nat.card_ne_zero.mp hbc).1
  have hmem := hL.slot_coord_mem k
  refine ⟨(v ⟨L.slotCoord k, hmem⟩ : ℕ), ?_, ?_⟩
  · exact lt_of_lt_of_le (v ⟨L.slotCoord k, hmem⟩).isLt (le_self_pow hq0 hd)
  · rw [hL.slotDigits_sem 0 hrho k]
    simp only [LedgerStratumData.blockCount]
    rw [Nat.card_ne_zero]
    exact ⟨⟨⟨v, hv, by rw [dif_pos hmem]⟩⟩, inferInstance⟩

/-- **THE REFUTATION (general form).** Every lawful ledger instance with at
least one realization violates `DigitsProdLaw` at its q-generic carrier: the
left side is forced to 0 by the semantics seam while the right side is a
product of positive factors. No TD-0 instance can make TD-3 true. -/
theorem not_digitsProd_of_lawful (L : LedgerStratumData D W P)
    (hL : L.LedgerLawful) (hrho : 0 < L.rho0) :
    ¬ DigitsProdLaw W P L.ledgerJoint := by
  intro hDP
  choose z hzlt hzne using fun k : ↥W.onLine =>
    lawful_exists_digit_witness L hL hrho k
  have hρ0 : (0 : ℕ) < (L.ledgerJoint).rhoCount L.q0 := by
    simpa [LedgerStratumData.ledgerJoint] using hrho
  have h0 := hDP L.q0 0 hρ0 z hzlt
  have hlhs : (L.ledgerJoint).fiberDigits 0 z L.q0 = 0 := by
    simpa [LedgerStratumData.ledgerJoint] using
      lawful_cylFiberDigits_eq_zero L hL hrho z
  rw [hlhs] at h0
  refine mul_ne_zero ?_ ?_ h0.symm
  · rw [Finset.prod_ne_zero_iff]
    intro k _
    simpa [LedgerStratumData.ledgerJoint] using hzne k
  · rw [Finset.prod_ne_zero_iff]
    intro k hk
    have hkbox : k ∈ W.boxSlots := (Finset.mem_sdiff.mp hk).1
    have hcnt : (L.ledgerJoint).slotCount 0 k L.q0 = L.cylSlot 0 k := by
      simp [LedgerStratumData.ledgerJoint]
    rw [hcnt, hL.slot_count_val 0 hrho k hkbox]
    exact pow_ne_zero _ (by have := L.hq0; omega)

end General

/-! ## Part 2 — the concrete lawful witness (rho0 = 1, scope + clean satisfied)

The census datum `r = 0`, `e = h = f ≡ 1` (so `d = period = 1`, `s ≡ 1`), the
`ℓ = 1` monic-top window with empty on-line set, floors `g ≡ 0`, level `N = 2`,
`q0 = 2`, one slot block `{(k, 0)}` per slot with the trivial condition. This
shows `LedgerLawful` + `LedgerScope` + `LedgerClean` are jointly inhabited at
`rho0 = 1`, so Part 1's refutation applies to TD-3's exact statement. -/

section Witness

/-- Helper: the block count of an always-true condition is the full box. -/
theorem blockCount_of_forall (q : ℕ) (B : Finset Coord)
    (cond : (Coord → ℕ) → Prop) (h : ∀ x, cond x) :
    blockCount q B cond = q ^ B.card := by
  simp only [LedgerStratumData.blockCount]
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun v => h _)), Nat.card_fun,
    Nat.card_eq_finsetCard, Nat.card_eq_fintype_card, Fintype.card_fin]

def cmD : CensusData where
  r := 0
  e := fun _ => 1
  h := fun _ => 1
  f := fun _ => 1
  he := fun _ => le_rfl
  hf := fun _ => le_rfl
  h_coprime := fun _ => Nat.coprime_one_left 1

theorem cmD_d : cmD.d = 1 := by
  simp [CensusData.d, cmD]

theorem cmD_ledgerE (i : Fin (cmD.r + 1)) : cmD.ledgerE i = 1 := by
  unfold CensusData.ledgerE
  split <;> rfl

theorem cmD_period : cmD.period = 1 := by
  simp [CensusData.period, cmD_ledgerE]

theorem cmD_wphi (i : Fin (cmD.r + 1)) : cmD.wphi i = 0 := by
  have h2 : i.1 < 0 + 1 := i.2
  have h0 : i.1 = 0 := by omega
  unfold CensusData.wphi
  rw [if_pos h0]

theorem cmD_wt (j : cmD.J) : cmD.wt j = 0 := by
  unfold CensusData.wt
  exact Finset.sum_eq_zero fun i _ => by rw [cmD_wphi, Nat.mul_zero]

theorem cmD_card_J : Fintype.card cmD.J = 1 := by
  refine Fintype.card_eq_one_iff.mpr
    ⟨fun i => (⟨0, cmD.ledgerE_pos i⟩, ⟨0, cmD.hf i⟩), fun y => ?_⟩
  funext i
  have he := cmD_ledgerE i
  have h1 := (y i).1.2
  have h2 : ((y i).2 : ℕ) < 1 := (y i).2.2
  have hv1 : ((y i).1 : ℕ) = 0 := by omega
  have hv2 : ((y i).2 : ℕ) = 0 := by omega
  exact Prod.ext (Fin.ext hv1) (Fin.ext hv2)

theorem cmD_s (β : ℕ) : cmD.s β = 1 := by
  unfold CensusData.s
  rw [Finset.filter_true_of_mem (fun j _ => by rw [cmD_wt]; exact Nat.zero_le β),
    Finset.card_univ, cmD_card_J]

def cmW : WindowDatum cmD where
  ℓ := 1
  hℓ := le_rfl
  n := 1
  hn := by simp [cmD_period, cmD_d]
  hn2 := by simp [cmD_period, cmD_d]
  beta := fun _ => 0
  onLine := ∅
  ks := Fin.last 1
  monicTop := true
  hmono := by simp [cmD_period, cmD_d]
  boxSlots := Finset.univ.erase (Fin.last 1)
  hbox := rfl
  honLine_box := Finset.empty_subset _
  hks_line := fun h => absurd h (by decide)
  hks_top := fun _ => rfl

def cmP : ParentShape cmD cmW where
  N0 := 1
  hN0 := le_rfl
  g := fun _ => 0

def cmL : LedgerStratumData cmD cmW cmP where
  N := 2
  hN := one_le_two
  q0 := 2
  hq0 := le_rfl
  rho0 := 1
  inStratum := fun _ _ => True
  parentCond := fun _ _ => True
  slotCond := fun _ _ _ => True
  parentBlock := ∅
  slotBlock := fun k => {(k.1, 0)}
  slotCoord := fun k => ((k : Fin (cmW.ℓ + 1)).1, 0)
  cylSlot := fun _ _ => 2
  cylSlotDigits := fun _ _ _ => 0
  cylFiber := fun _ => 0
  cylFiberDigits := fun _ _ => 0
  pin := fun _ => 1
  hpin_ne := fun _ _ => one_ne_zero
  hpin_lt := fun _ _ => by rw [cmD_d]; norm_num
  hexact := True

theorem cmL_lawful : cmL.LedgerLawful where
  semantics := by
    intro ρ hρ
    constructor
    · haveI : Infinite {x : Coord → ℕ // cmL.inStratum ρ x} :=
        Infinite.of_injective (fun n : ℕ => ⟨fun _ => n, trivial⟩)
          (fun a b hab => by
            simpa using congrArg (fun s : {x : Coord → ℕ // cmL.inStratum ρ x} => s.1 (0, 0)) hab)
      exact (Nat.card_eq_zero_of_infinite).symm
    · intro z
      haveI : Infinite {x : Coord → ℕ // cmL.inStratum ρ x ∧
          ∀ k : ↥cmW.onLine, x (cmL.slotCoord k) = z k} :=
        Infinite.of_injective
          (fun n : ℕ => ⟨fun _ => n, trivial,
            fun k => absurd k.2 (Finset.notMem_empty _)⟩)
          (fun a b hab => by
            simpa using congrArg
              (fun s : {x : Coord → ℕ // cmL.inStratum ρ x ∧
                ∀ k : ↥cmW.onLine, x (cmL.slotCoord k) = z k} => s.1 (0, 0)) hab)
      exact (Nat.card_eq_zero_of_infinite).symm
  member_split := by
    intro ρ x
    show True ↔ (True ∧ ∀ k ∈ cmW.boxSlots, True)
    simp
  parent_support := fun _ _ _ _ => Iff.rfl
  slot_support := fun _ _ _ _ _ => Iff.rfl
  slots_disjoint := by
    intro k k' hkk
    refine Finset.disjoint_singleton.mpr fun h => ?_
    exact hkk (Fin.ext (congrArg Prod.fst h))
  slot_coord_mem := fun k => absurd k.2 (Finset.notMem_empty _)
  parent_interior_disjoint := fun k => absurd k.2 (Finset.notMem_empty _)
  pinned_forced := fun _ _ c hc => absurd hc (Finset.notMem_empty c)
  junction := fun _ _ _ _ hk => absurd hk (Finset.notMem_empty _)
  digit_range := fun _ _ _ _ k => absurd k.2 (Finset.notMem_empty _)
  slot_sem := by
    intro ρ hρ k hk
    rw [blockCount_of_forall cmL.q0 (cmL.slotBlock k) (cmL.slotCond ρ k)
      (fun _ => trivial)]
    show (2 : ℕ) = 2 ^ ({(k.1, 0)} : Finset Coord).card
    simp
  slotDigits_sem := fun _ _ k => absurd k.2 (Finset.notMem_empty _)
  slot_count_val := by
    intro ρ hρ k hk
    show (2 : ℕ) = 2 ^ ((cmD.period * cmD.d) * 2 - cmD.s (max 0 0))
    rw [Nat.max_self, cmD_s, cmD_period, cmD_d]
    norm_num

theorem cm_scope : LedgerScope cmW cmP :=
  fun _ hk => absurd hk (Finset.notMem_empty _)

theorem cm_clean : LedgerClean cmD cmW cmP cmL.N := by
  intro k hk
  show cmD.s (max 0 0) + cmD.d ≤ (cmD.period * cmD.d) * 2
  rw [Nat.max_self, cmD_s, cmD_period, cmD_d]

/-- The instance-level refutation: the concrete lawful witness violates the
law TD-3 must prove for it. -/
theorem cm_not_digitsProd : ¬ DigitsProdLaw cmW cmP cmL.ledgerJoint :=
  not_digitsProd_of_lawful cmL cmL_lawful Nat.one_pos

/-- **TD-3 IS FALSE AS STATED**: the ∀-closure of `ledger_digitsProd`
(TD3_digitsProd.lean, E-phase sorry) is refutable. -/
theorem ledger_digitsProd_refuted :
    ¬ ∀ (D : CensusData) (W : WindowDatum D) (P : ParentShape D W)
        (L : LedgerStratumData D W P), L.LedgerLawful → LedgerScope W P →
        LedgerClean D W P L.N → DigitsProdLaw W P L.ledgerJoint :=
  fun h => cm_not_digitsProd (h cmD cmW cmP cmL cmL_lawful cm_scope cm_clean)

end Witness

end LeanUrat.B2D

#print axioms LeanUrat.B2D.not_digitsProd_of_lawful
#print axioms LeanUrat.B2D.lawful_cylFiberDigits_eq_zero
#print axioms LeanUrat.B2D.lawful_fiber_devacuify_impossible
#print axioms LeanUrat.B2D.cmL_lawful
#print axioms LeanUrat.B2D.ledger_digitsProd_refuted
