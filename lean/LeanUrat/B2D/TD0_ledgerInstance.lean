/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.TD3v2_control

/-!
# B2D/TD0_ledgerInstance — the designated ledger instance, v2 (r ≥ 1, on-line
  digit content)  [B2DEF_LEAN unit TD-0; wave 1, round 2]

Blueprint: `lean/blueprints/B2DEF_LEAN_2026-08-08.md` §5 TD-0 (round-2 status:
"duties (a)-(c) now target `LedgerLawfulV2`"). moves_ref: §B2-DEF D.3(e)(ii),
D.8 (VERTEX), D.11. deps: E2 v2 (`TDDefsV2`), control (`TD3v2_control`).
difficulty: hard (per blueprint; the counting semantics is the work).

## What this unit delivers (the [R1-G3] duty list, round 2)

* **(a) LAWFULNESS**: `td_lawfulV2 : tdL.LedgerLawfulV2` — every clause of the
  v2 pack holds at the built instance `tdL` (the `WindowDatum`/`ParentShape`
  law fields hold by construction of `tdW`/`tdP`). The junction, digit-range,
  and per-digit-count clauses are NON-vacuous here (`onLine = {0} ∋ ks`,
  `monicTop = false`) — the control `cmL2` had them all vacuous.
* **(b) q₀-SEMANTICS**: `td_semanticsV2 : tdL.LedgerSemanticsV2` — the
  counting fields ARE the finite-box `blockCount`s over `supportUnion`
  (computed: `cylFiber = 16 = 2⁴` on the 5-coordinate support with the one
  junction-pinned leaf; `cylFiberDigits z = 16·[z₀ = 1]`).
* **(c) DE-VACUITY at r ≥ 1**: `td_devacuify` — a realization with POSITIVE
  fiber count, at the census `tdD` with `tdD.r = 1` (`tdD_r`); scope + clean
  hold (`td_scope`/`td_clean`); the designated family `LedgerStrataV2` is
  inhabited by the instance (`td_mem_ledgerStrataV2`). Precedent:
  `H2/R0Instance.lean` (r = 0); this is the demanded r ≥ 1 witness.
* **POSITIVE CONTROL for the (F) product face**: `td_digitsProd` —
  `DigitsProdLaw` HOLDS, proved, at `tdL.ledgerJoint`, with genuine on-line
  digit content (junction factor `4·[z₀ = 1]` × off-line factor `4` = the
  fiber count `16·[z₀ = 1]`). Strictly stronger than the control's
  `cm2_digitsProd` (empty on-line set there).

## The instance (N-TD1 trace instance i2, lifted to census depth r = 1)

Census `tdD`: r = 1, e = h ≡ 1, f = ![2, 1] — so d = 2, ledger period 1
(m = period·d = 2), wt ≡ 0, s ≡ 2 (both φ-monomials at weight 0). Window
`tdW`: ℓ = 1, n = 3 (2 ≤ 3 < 4, and 2 ∤ 3 forces `monicTop = false`, so
`boxSlots = univ` and the junction `ks = 0` is ON-LINE per `hks_line`);
β ≡ 0. Parent `tdP`: N₀ = 1, g ≡ 0. Datum `tdL`: N = 2, q₀ = 2, rho0 = 1;
`slotBlock 0 = {(0,0),(0,1),(0,2)}` (junction slot, its `slotCond` pins the
read leaf `(0,0)` to the pin code 1 — trace i2's "junction clause satisfied
by ALL members"), `slotBlock 1 = {(1,0),(1,1)}` (off-line, free);
`parentBlock = ∅` (as in ALL N-TD1 trace instances: the parent-realized
content of the shallow strata is exhausted by the per-slot conditions).
Counts: per-slot 4 = 2^(m·N − s) each (`slot_count_val` exact), fiber
16 = 4·4.

## Fences / honesty

* `parentBlock = ∅` means `pinned_forced` and `parent_interior_disjoint` hold
  vacuously here (their non-vacuous exercise needs a parent-pinned instance —
  NOT built in this round; the trace never probed one either, which is exactly
  where the round-2 TD-3 countermodel lives, see `TD3v2_countermodel.lean`).
  By the same token the instance satisfies the two constraints the TD-3
  round-2 refutation shows the v2 pack is MISSING (per-realization parent
  satisfiability; parent-block/box-slot disjointness) — so `tdL` survives any
  v3 statement round that adds them.
* `hexact := True` (the E2 bare-`Prop` `RootHyps` device, TDDefs flag 3).
* No claim beyond the compiled instance: this de-vacuifies the FAMILY; it does
  not prove any ∀-law over it (TD-3's ∀-form is refuted — see the
  countermodel file).

NEW helper decls (blueprint §5 TD-3 "add if needed" provision):
`pinnedRestrictEquiv` + `blockCount_pin` — the pinned-leaf block count
`blockCount q B (x c₀ = a) = q^(|B|−1)` (c₀ ∈ B, a < q), i.e. the (ii.4)
unit-diagonal counting step; consumed here and by the TD-3 countermodel.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.style.show false

namespace LeanUrat.B2D

open LeanUrat.Scaffold LeanUrat.Scaffold.HDischarge.H2 LeanUrat.MovesC LedgerStratumData

/-! ## The pinned-leaf counting helper (new; consumed by the countermodel too) -/

/-- Box functions with one pinned coordinate value correspond to functions on
the erased box (the D.3(e)(ii.4) unit-diagonal step, counted). -/
def pinnedRestrictEquiv (q : ℕ) (B : Finset Coord) (c0 : Coord) (hc0 : c0 ∈ B)
    (a0 : Fin q) :
    {v : ↥B → Fin q // v ⟨c0, hc0⟩ = a0} ≃ (↥(B.erase c0) → Fin q) where
  toFun v j := v.1 ⟨j.1, Finset.mem_of_mem_erase j.2⟩
  invFun w := ⟨fun i => if h : (i : Coord) = c0 then a0
      else w ⟨i.1, Finset.mem_erase.mpr ⟨h, i.2⟩⟩, by simp⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    by_cases h : (i : Coord) = c0
    · have hi : i = ⟨c0, hc0⟩ := Subtype.ext h
      subst hi
      simpa using v.2.symm
    · simp [h]
  right_inv w := by
    funext j
    have hj := Finset.mem_erase.mp j.2
    simp [hj.1]

/-- **Pinned-leaf block count**: pinning one in-box coordinate to one
in-alphabet value counts `q ^ (|B| − 1)` — the counting shadow of the (ii.4)
"each pinned leaf's value is forced" display at a single leaf. -/
theorem blockCount_pin (q : ℕ) (B : Finset Coord) {c0 : Coord} (hc0 : c0 ∈ B)
    {a : ℕ} (ha : a < q) :
    blockCount q B (fun x => x c0 = a) = q ^ (B.card - 1) := by
  simp only [LedgerStratumData.blockCount]
  rw [Nat.card_congr ((Equiv.subtypeEquivRight (q := fun v : ↥B → Fin q =>
        v ⟨c0, hc0⟩ = ⟨a, ha⟩) (fun v => by
        rw [dif_pos hc0]
        exact ⟨fun h => Fin.ext h, fun h => by rw [h]⟩)).trans
      (pinnedRestrictEquiv q B c0 hc0 ⟨a, ha⟩)),
    Nat.card_fun, Nat.card_eq_finsetCard, Nat.card_eq_fintype_card,
    Fintype.card_fin, Finset.card_erase_of_mem hc0]

/-! ## The census at depth r = 1 (d = 2, period 1, wt ≡ 0, s ≡ 2) -/

def tdD : CensusData where
  r := 1
  e := fun _ => 1
  h := fun _ => 1
  f := ![2, 1]
  he := fun _ => le_rfl
  hf := fun i => by fin_cases i <;> norm_num
  h_coprime := fun _ => Nat.coprime_one_left _

theorem tdD_r : tdD.r = 1 := rfl

theorem tdD_d : tdD.d = 2 := by
  show (∏ i : Fin 2, tdD.f i) = 2
  rw [Fin.prod_univ_two]
  rfl

theorem tdD_ledgerE (i : Fin (tdD.r + 1)) : tdD.ledgerE i = 1 := by
  unfold CensusData.ledgerE
  split <;> rfl

theorem tdD_period : tdD.period = 1 := by
  simp [CensusData.period, tdD_ledgerE]

theorem tdD_wphi_zero : tdD.wphi 0 = 0 := rfl

theorem tdD_wphi_one : tdD.wphi 1 = 1 := rfl

theorem tdD_wt (j : tdD.J) : tdD.wt j = 0 := by
  unfold CensusData.wt
  refine Finset.sum_eq_zero (fun i _ => ?_)
  by_cases hi : i.1 = 0
  · have hw : tdD.wphi i = 0 := by unfold CensusData.wphi; rw [if_pos hi]
    rw [hw, Nat.mul_zero]
  · have hr : tdD.r = 1 := rfl
    have hisLt := i.isLt
    have hlt1 := (j i).1.isLt
    have hE := tdD_ledgerE i
    have h1 : ((j i).1 : ℕ) = 0 := by omega
    have hv1 : ((1 : Fin (tdD.r + 1)) : ℕ) = 1 := rfl
    have hi1 : i = 1 := Fin.ext (by omega)
    have hfi : tdD.f i = 1 := by rw [hi1]; decide
    have hlt2 := (j i).2.isLt
    have h2 : ((j i).2 : ℕ) = 0 := by omega
    rw [h1, h2]
    simp

theorem tdD_card_J : Fintype.card tdD.J = 2 := by
  rw [show (Fintype.card tdD.J)
      = Fintype.card ((i : Fin 2) → Fin (tdD.ledgerE i) × Fin (tdD.f i)) from rfl,
    Fintype.card_pi, Fin.prod_univ_two]
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    Fintype.card_fin, Fintype.card_fin, tdD_ledgerE, tdD_ledgerE]
  rfl

theorem tdD_s (β : ℕ) : tdD.s β = 2 := by
  unfold CensusData.s
  rw [Finset.filter_true_of_mem (fun j _ => by rw [tdD_wt]; exact Nat.zero_le β),
    Finset.card_univ, tdD_card_J]

/-! ## Window (monicTop = false: junction on-line), parent, blocks -/

def tdW : WindowDatum tdD where
  ℓ := 1
  hℓ := le_rfl
  n := 3
  hn := by rw [tdD_period, tdD_d]; norm_num
  hn2 := by rw [tdD_period, tdD_d]; norm_num
  beta := fun _ => 0
  onLine := {0}
  ks := 0
  monicTop := false
  hmono := by
    rw [tdD_period, tdD_d]
    exact iff_of_false (by simp) (by decide)
  boxSlots := Finset.univ
  hbox := rfl
  honLine_box := Finset.subset_univ _
  hks_line := fun _ => Finset.mem_singleton_self 0
  hks_top := fun h => absurd h (by simp)

def tdP : ParentShape tdD tdW where
  N0 := 1
  hN0 := le_rfl
  g := fun _ => 0

theorem td0_mem_onLine : (0 : Fin 2) ∈ tdW.onLine := Finset.mem_singleton_self 0

/-- The unique on-line slot, as a subtype element. -/
def tdK0 : ↥tdW.onLine := ⟨0, td0_mem_onLine⟩

theorem td_onLine_eq (k : ↥tdW.onLine) : k = tdK0 :=
  Subtype.ext (Finset.mem_singleton.mp k.2)

/-- Junction slot block (3 leaves; the read leaf `(0,0)` gets pinned). -/
def tdBlock0 : Finset Coord := {((0 : ℕ), (0 : ℕ)), (0, 1), (0, 2)}

/-- Off-line slot block (2 free leaves). -/
def tdBlock1 : Finset Coord := {((1 : ℕ), (0 : ℕ)), (1, 1)}

/-! ## The datum -/

def tdL : LedgerStratumData tdD tdW tdP where
  N := 2
  hN := one_le_two
  q0 := 2
  hq0 := le_rfl
  rho0 := 1
  inStratum := fun _ x => x ((0 : ℕ), (0 : ℕ)) = 1
  parentCond := fun _ _ => True
  slotCond := fun _ k x => if k = 0 then x ((0 : ℕ), (0 : ℕ)) = 1 else True
  parentBlock := ∅
  slotBlock := fun k => if k = 0 then tdBlock0 else tdBlock1
  slotCoord := fun _ => ((0 : ℕ), (0 : ℕ))
  cylSlot := fun _ _ => 4
  cylSlotDigits := fun _ _ z => if z = 1 then 4 else 0
  cylFiber := fun _ => 16
  cylFiberDigits := fun _ z => if z tdK0 = 1 then 16 else 0
  pin := fun _ => 1
  hpin_ne := fun _ _ => one_ne_zero
  hpin_lt := fun _ _ => by rw [tdD_d]; norm_num
  hexact := True

theorem tdL_supportUnion :
    tdL.supportUnion = {((0 : ℕ), (0 : ℕ)), (0, 1), (0, 2), (1, 0), (1, 1)} := by
  decide

theorem tdL_supportUnion_card : tdL.supportUnion.card = 5 := by
  rw [tdL_supportUnion]
  rfl

/-! ## Duty (b): the q₀ finite-box semantics, computed -/

theorem td_semanticsV2 : tdL.LedgerSemanticsV2 := by
  intro ρ hρ
  have hmem : ((0 : ℕ), (0 : ℕ)) ∈ tdL.supportUnion := by
    rw [tdL_supportUnion]; decide
  have hpin : blockCount tdL.q0 tdL.supportUnion
      (fun x => x ((0 : ℕ), (0 : ℕ)) = 1) = 16 := by
    rw [blockCount_pin tdL.q0 _ hmem one_lt_two, tdL_supportUnion_card]
    rfl
  refine ⟨hpin.symm, fun z => ?_⟩
  by_cases hz : z tdK0 = 1
  · have hcongr : blockCount tdL.q0 tdL.supportUnion
        (fun x => tdL.inStratum ρ x ∧ ∀ k : ↥tdW.onLine, x (tdL.slotCoord k) = z k)
        = blockCount tdL.q0 tdL.supportUnion (fun x => x ((0 : ℕ), (0 : ℕ)) = 1) := by
      refine blockCount_congr _ _ (fun x => ⟨fun h => h.1, fun hx => ⟨hx, fun k => ?_⟩⟩)
      rw [td_onLine_eq k, hz]
      exact hx
    show (if z tdK0 = 1 then 16 else 0) = _
    rw [if_pos hz, hcongr, hpin]
  · show (if z tdK0 = 1 then 16 else 0) = _
    rw [if_neg hz]
    exact (blockCount_of_not _ _ _
      (fun x h => hz ((h.2 tdK0).symm.trans h.1))).symm

/-! ## Duty (a): the full v2 lawfulness pack -/

theorem td_lawfulV2 : tdL.LedgerLawfulV2 where
  semantics := td_semanticsV2
  member_split := by
    intro ρ x
    show (x ((0 : ℕ), (0 : ℕ)) = 1) ↔
      (True ∧ ∀ k ∈ tdW.boxSlots,
        if k = 0 then x ((0 : ℕ), (0 : ℕ)) = 1 else True)
    constructor
    · intro hx
      refine ⟨trivial, fun k _ => ?_⟩
      by_cases hk : k = 0
      · rw [if_pos hk]; exact hx
      · rw [if_neg hk]; trivial
    · rintro ⟨-, h⟩
      have h0 := h 0 (Finset.mem_univ _)
      rwa [if_pos rfl] at h0
  parent_support := fun _ _ _ _ => Iff.rfl
  slot_support := by
    intro ρ k x y hxy
    by_cases hk : k = 0
    · have hmem : ((0 : ℕ), (0 : ℕ)) ∈ tdL.slotBlock k := by
        show _ ∈ (if k = 0 then tdBlock0 else tdBlock1)
        rw [if_pos hk]
        decide
      show (if k = 0 then x ((0 : ℕ), (0 : ℕ)) = 1 else True)
        ↔ (if k = 0 then y ((0 : ℕ), (0 : ℕ)) = 1 else True)
      rw [if_pos hk, if_pos hk, hxy ((0 : ℕ), (0 : ℕ)) hmem]
    · show (if k = 0 then x ((0 : ℕ), (0 : ℕ)) = 1 else True)
        ↔ (if k = 0 then y ((0 : ℕ), (0 : ℕ)) = 1 else True)
      rw [if_neg hk, if_neg hk]
  slots_disjoint := by
    intro k k' hkk
    show Disjoint (if k = 0 then tdBlock0 else tdBlock1)
      (if k' = 0 then tdBlock0 else tdBlock1)
    have hd : Disjoint tdBlock0 tdBlock1 := by decide
    by_cases hk : k = 0 <;> by_cases hk' : k' = 0
    · exact absurd (hk.trans hk'.symm) hkk
    · rw [if_pos hk, if_neg hk']; exact hd
    · rw [if_neg hk, if_pos hk']; exact hd.symm
    · refine absurd (Fin.ext ?_ : k = k') hkk
      have h1 := k.isLt
      have h2 := k'.isLt
      have hℓ : tdW.ℓ = 1 := rfl
      have hv0 : ((0 : Fin (tdW.ℓ + 1)) : ℕ) = 0 := rfl
      have hk1 : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext (h.trans hv0.symm))
      have hk'1 : (k' : ℕ) ≠ 0 := fun h => hk' (Fin.ext (h.trans hv0.symm))
      omega
  slot_coord_mem := by
    intro k
    have hk : (k : Fin (tdW.ℓ + 1)) = 0 := Finset.mem_singleton.mp k.2
    show tdL.slotCoord k ∈ tdL.slotBlock (k : Fin (tdW.ℓ + 1))
    rw [hk]
    show ((0 : ℕ), (0 : ℕ)) ∈ (if (0 : Fin (tdW.ℓ + 1)) = 0 then tdBlock0 else tdBlock1)
    rw [if_pos rfl]
    decide
  parent_interior_disjoint := fun _ _ => Finset.disjoint_empty_left _
  pinned_forced := fun _ _ c hc => absurd hc (Finset.notMem_empty c)
  junction := fun _ _ _ hx _ => hx
  digit_range := by
    intro ρ hρ x hx k
    have hx' : x ((0 : ℕ), (0 : ℕ)) = 1 := hx
    show x ((0 : ℕ), (0 : ℕ)) < 2 ^ tdD.d
    rw [hx', tdD_d]
    norm_num
  slot_sem := by
    intro ρ hρ k hk
    by_cases hkk : k = 0
    · show (4 : ℕ) = blockCount 2 (if k = 0 then tdBlock0 else tdBlock1)
        (tdL.slotCond ρ k)
      rw [if_pos hkk]
      have hcongr : blockCount 2 tdBlock0 (tdL.slotCond ρ k)
          = blockCount 2 tdBlock0 (fun x => x ((0 : ℕ), (0 : ℕ)) = 1) :=
        blockCount_congr _ _ (fun x => by
          show (if k = 0 then x ((0 : ℕ), (0 : ℕ)) = 1 else True) ↔ _
          rw [if_pos hkk])
      rw [hcongr, blockCount_pin 2 tdBlock0 (by decide) one_lt_two]
      decide
    · show (4 : ℕ) = blockCount 2 (if k = 0 then tdBlock0 else tdBlock1)
        (tdL.slotCond ρ k)
      rw [if_neg hkk]
      rw [blockCount_of_forall 2 tdBlock1 _ (fun x => by
        show if k = 0 then x ((0 : ℕ), (0 : ℕ)) = 1 else True
        rw [if_neg hkk]
        trivial)]
      decide
  slotDigits_sem := by
    intro ρ hρ k z
    have hk : (k : Fin (tdW.ℓ + 1)) = 0 := Finset.mem_singleton.mp k.2
    by_cases hz : z = 1
    · show (if z = 1 then 4 else 0) = blockCount 2
        (if (k : Fin (tdW.ℓ + 1)) = 0 then tdBlock0 else tdBlock1)
        (fun x => tdL.slotCond ρ (k : Fin (tdW.ℓ + 1)) x ∧ x (tdL.slotCoord k) = z)
      rw [if_pos hz, if_pos hk]
      have hcongr : blockCount 2 tdBlock0
          (fun x => tdL.slotCond ρ (k : Fin (tdW.ℓ + 1)) x ∧ x (tdL.slotCoord k) = z)
          = blockCount 2 tdBlock0 (fun x => x ((0 : ℕ), (0 : ℕ)) = 1) :=
        blockCount_congr _ _ (fun x => by
          show ((if (k : Fin (tdW.ℓ + 1)) = 0 then x ((0 : ℕ), (0 : ℕ)) = 1 else True)
            ∧ x ((0 : ℕ), (0 : ℕ)) = z) ↔ _
          rw [if_pos hk, hz, and_self])
      rw [hcongr, blockCount_pin 2 tdBlock0 (by decide) one_lt_two]
      decide
    · show (if z = 1 then 4 else 0) = blockCount 2
        (if (k : Fin (tdW.ℓ + 1)) = 0 then tdBlock0 else tdBlock1)
        (fun x => tdL.slotCond ρ (k : Fin (tdW.ℓ + 1)) x ∧ x (tdL.slotCoord k) = z)
      rw [if_neg hz, if_pos hk]
      refine (blockCount_of_not _ _ _ (fun x h => hz ?_)).symm
      have h1 : x ((0 : ℕ), (0 : ℕ)) = 1 := by
        have h' : if (k : Fin (tdW.ℓ + 1)) = 0 then x ((0 : ℕ), (0 : ℕ)) = 1 else True := h.1
        rwa [if_pos hk] at h'
      have h2 : x ((0 : ℕ), (0 : ℕ)) = z := h.2
      rw [← h2, h1]
  slot_count_val := by
    intro ρ hρ k hk
    show (4 : ℕ) = 2 ^ ((tdD.period * tdD.d) * 2 - tdD.s (max 0 0))
    rw [Nat.max_self, tdD_s, tdD_period, tdD_d]
    norm_num

/-! ## Duty (c): scope, clean, de-vacuity at r = 1, family membership -/

theorem td_scope : LedgerScope tdW tdP := fun _ _ => Nat.le_refl 0

theorem td_clean : LedgerClean tdD tdW tdP tdL.N := by
  intro k hk
  show tdD.s (max 0 0) + tdD.d ≤ (tdD.period * tdD.d) * 2
  rw [Nat.max_self, tdD_s, tdD_period, tdD_d]

/-- **TD-0 duty (c), discharged at census depth r = 1** (contrast the r = 0
control `v2_devacuify_possible` and the v1 impossibility
`lawful_fiber_devacuify_impossible`): a realization with positive fiber
count at the lawful, in-scope, clean instance. -/
theorem td_devacuify : ∃ ρ, ρ < tdL.rho0 ∧ 0 < tdL.cylFiber ρ :=
  ⟨0, Nat.one_pos, by norm_num [tdL]⟩

/-- The designated family `LedgerStrataV2` is inhabited by the instance. -/
theorem td_mem_ledgerStrataV2 : tdL.ledgerJoint ∈ LedgerStrataV2 tdD tdW tdP :=
  ⟨tdL, td_lawfulV2, rfl⟩

/-! ## Positive control: the (F) product-box law at the instance -/

/-- **`DigitsProdLaw` HOLDS at the designated r = 1 instance** — with genuine
on-line digit content: junction digit factor `4·[z₀ = 1]` times off-line
height factor `4` equals the fiber count `16·[z₀ = 1]`. (The positive face of
the D.11 finite-box product; the ∀-closure over ALL v2-lawful instances is
refuted — `TD3v2_countermodel.lean`.) -/
theorem td_digitsProd : DigitsProdLaw tdW tdP tdL.ledgerJoint := by
  intro q ρ hρ z hz
  by_cases hq : q = tdL.q0
  · subst hq
    have hattach : tdW.onLine.attach = {tdK0} := rfl
    have hbox : tdW.boxSlots \ tdW.onLine = {(1 : Fin (tdW.ℓ + 1))} := by decide
    simp only [LedgerStratumData.ledgerJoint, hattach, hbox,
      Finset.prod_singleton]
    show (if z tdK0 = 1 then 16 else 0) = (if z tdK0 = 1 then 4 else 0) * 4
    by_cases hz1 : z tdK0 = 1
    · rw [if_pos hz1, if_pos hz1]
    · rw [if_neg hz1, if_neg hz1, Nat.zero_mul]
  · rw [ledger_rhoCount_off_support tdL q hq] at hρ
    omega

end LeanUrat.B2D

#print axioms LeanUrat.B2D.blockCount_pin
#print axioms LeanUrat.B2D.td_semanticsV2
#print axioms LeanUrat.B2D.td_lawfulV2
#print axioms LeanUrat.B2D.td_devacuify
#print axioms LeanUrat.B2D.td_mem_ledgerStrataV2
#print axioms LeanUrat.B2D.td_digitsProd
