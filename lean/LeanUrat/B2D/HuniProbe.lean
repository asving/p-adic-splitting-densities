/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.TD6_assembly

/-!
# B2D/HuniProbe — huni/SlotUniformLaw decided at the compiled ledger instances
  [synthesis pass 5 F1 target (i); countermodel-first probe, 2026-08-08]

The `huni : SlotUniformLaw` face is the ONE displayed open input on the
B2D/TRANS-DEEP supply chain (`transDeep_of_ledger` fills
`fresh_of_transDeep`'s `hTD`; `huni` rides `ledger_freshRowOn` as the (ADM) +
(GR-B)-line hypothesis, never supplied). This probe decides it at compiled
instances BEFORE any supplier work.

## Verdicts (both compiled below)

* **At the designated r = 1 instance `tdL`: VACUOUSLY TRUE**
  (`slotUniform_tdL_vacuous`). `tdW.onLine = {0} ∋ ks = 0`: the law's
  quantifier over NON-junction on-line slots is empty
  (`tdW_onLine_eq_junction`). The instance cannot decide the face.
* **At the cheapest non-degenerate extension `td2`: FALSE**
  (`slotUniform_td2_false`), with `td2L` fully v3-LAWFUL
  (`td2_lawfulV3`, `td2_mem_ledgerStrataV3`) and inside the supplier's own
  firing perimeter (`td2_scope`/`td2_clean`; the TransDeep row EXISTS:
  `td2_transDeep`). Hence the displayed `huni` binder of `ledger_freshRowOn`
  is UNSATISFIABLE at the census `tdD` (`ledger_huni_face_false_at_tdD`).

## The mechanism: an ALPHABET seam, not an adversarial pin

`td2` is `tdL` with the off-line slot 1 promoted on-line (`onLine = {0,1}`,
junction still 0) — slot 1's condition stays the FREE one (its read is only
alphabet-bounded). The failure is structural: the H2 digit alphabet is
`q^D.d = 4` (the F_{q^d} digit code), but the v2/v3 ledger carrier reads ONE
leaf `slotCoord k` of a `Fin q₀ = Fin 2` box vector, so
`slotDigits ρ k z q₀ = 0` is FORCED at every z ∈ [q₀, q₀^d) (here z = 2,
in-range for the law) while in-alphabet digits count positively (z = 0
counts 2). Uniformity across z < q₀^d is impossible. The same seam kills the
CONSUMER's conclusion at the instance: `FreshReadsLaw` also FAILS at `td2`
(`freshReads_td2_false`) — so no re-guarding of `huni` alone can save
`fresh_of_transDeep`'s output on this carrier.

Consequence (per F1's countermodel-first protocol): the huni face needs
RESTATEMENT before supplier work. The minimal honest repair the instance
points at is on the LEDGER side: the single-leaf `slotCoord` read must become
the full d-leaf digit CODE (the [R1-G2] "field-element-to-code bijection"
that TD-0 only ever exercised at the pin value 1 < q₀). Merely guarding
`SlotUniformLaw`'s digits to `z < q` would NOT suffice: `FreshReadsLaw`
consumes the full-alphabet range and fails here too.

NEW helper decls (blueprint §5 "add if needed" provision):
`blockCount_congr_ext` (congruence on box-supported extensions only) and
`blockCount_pin2` (the two-pin block count `q^(|B|−2)`), both consumed by
`td2_semanticsV2`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.style.show false

namespace LeanUrat.B2D

open LeanUrat.Scaffold LeanUrat.Scaffold.HDischarge.H2 LeanUrat.MovesC LedgerStratumData

/-! ## Part 1 — the designated instance: VACUOUSLY TRUE -/

/-- The degeneracy, isolated: at `tdW` EVERY on-line slot is the junction. -/
theorem tdW_onLine_eq_junction (k : ↥tdW.onLine) :
    (k : Fin (tdW.ℓ + 1)) = tdW.ks :=
  Finset.mem_singleton.mp k.2

/-- **Verdict at the compiled r = 1 instance `tdL`: VACUOUSLY TRUE.**
`SlotUniformLaw` quantifies over NON-junction on-line slots, and `tdW` has
none (`onLine = {0} ∋ ks = 0`). The instance carries no information about
the face — the probe must extend. -/
theorem slotUniform_tdL_vacuous : SlotUniformLaw tdW tdP tdL.ledgerJoint := by
  intro q ρ hρ k hk
  exact absurd (tdW_onLine_eq_junction k) hk

/-! ## The two counting helpers -/

/-- `blockCount` respects conditions agreeing on all box-supported
extensions (the weaker hypothesis `blockCount_congr` cannot supply when the
conditions differ off the extension range — e.g. a range clause that is
automatic for `Fin q` box values but false for general `x : Coord → ℕ`). -/
theorem blockCount_congr_ext (q : ℕ) (B : Finset Coord)
    {cond cond' : (Coord → ℕ) → Prop}
    (h : ∀ v : ↥B → Fin q,
      cond (fun c => if h : c ∈ B then (v ⟨c, h⟩ : ℕ) else 0)
        ↔ cond' (fun c => if h : c ∈ B then (v ⟨c, h⟩ : ℕ) else 0)) :
    blockCount q B cond = blockCount q B cond' :=
  Nat.card_congr (Equiv.subtypeEquivRight h)

/-- **Two-pin block count**: pinning two distinct in-box coordinates to
in-alphabet values counts `q ^ (|B| − 2)` (the `blockCount_pin` step,
iterated once). -/
theorem blockCount_pin2 (q : ℕ) (B : Finset Coord) {c0 c1 : Coord}
    (hc0 : c0 ∈ B) (hc1 : c1 ∈ B) (hne : c0 ≠ c1)
    {a b : ℕ} (ha : a < q) (hb : b < q) :
    blockCount q B (fun x => x c0 = a ∧ x c1 = b) = q ^ (B.card - 2) := by
  have hc1' : c1 ∈ B.erase c0 := Finset.mem_erase.mpr ⟨hne.symm, hc1⟩
  simp only [LedgerStratumData.blockCount]
  rw [Nat.card_congr ((Equiv.subtypeEquivRight (q := fun v : ↥B → Fin q =>
        v ⟨c0, hc0⟩ = ⟨a, ha⟩ ∧ v ⟨c1, hc1⟩ = ⟨b, hb⟩) (fun v => by
        rw [dif_pos hc0, dif_pos hc1]
        exact ⟨fun h => ⟨Fin.ext h.1, Fin.ext h.2⟩,
          fun h => ⟨by rw [h.1], by rw [h.2]⟩⟩)).trans
      (((Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm).trans
        ((Equiv.subtypeEquiv (pinnedRestrictEquiv q B c0 hc0 ⟨a, ha⟩)
            (fun u => Iff.rfl)).trans
          (pinnedRestrictEquiv q (B.erase c0) c1 hc1' ⟨b, hb⟩)))),
    Nat.card_fun, Nat.card_eq_finsetCard, Nat.card_eq_fintype_card,
    Fintype.card_fin, Finset.card_erase_of_mem hc1',
    Finset.card_erase_of_mem hc0]
  exact congrArg (q ^ ·) (by omega)

/-! ## Part 2 — the cheapest non-degenerate extension `td2`

Same census `tdD` (r = 1, d = 2), same blocks, same junction: only the
off-line slot 1 is promoted ON-line with the FREE (alphabet-bounded)
condition. The degeneracy of `tdW` was in the WINDOW (no non-junction
on-line slot), not the census depth, so this is the minimal extension that
makes the law's quantifier non-empty. -/

def td2W : WindowDatum tdD where
  ℓ := 1
  hℓ := le_rfl
  n := 3
  hn := by rw [tdD_period, tdD_d]; norm_num
  hn2 := by rw [tdD_period, tdD_d]; norm_num
  beta := fun _ => 0
  onLine := {0, 1}
  ks := 0
  monicTop := false
  hmono := by
    rw [tdD_period, tdD_d]
    exact iff_of_false (by simp) (by decide)
  boxSlots := Finset.univ
  hbox := rfl
  honLine_box := Finset.subset_univ _
  hks_line := fun _ => Finset.mem_insert_self 0 {1}
  hks_top := fun h => absurd h (by simp)

def td2P : ParentShape tdD td2W where
  N0 := 1
  hN0 := le_rfl
  g := fun _ => 0

theorem td2_zero_mem : (0 : Fin (td2W.ℓ + 1)) ∈ td2W.onLine := by decide

theorem td2_one_mem : (1 : Fin (td2W.ℓ + 1)) ∈ td2W.onLine := by decide

/-- The junction on-line slot. -/
def td2K0 : ↥td2W.onLine := ⟨0, td2_zero_mem⟩

/-- The NON-junction on-line slot — the law's quantifier is now inhabited. -/
def td2K1 : ↥td2W.onLine := ⟨1, td2_one_mem⟩

theorem td2K0_coe : ((td2K0 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) = 0 := rfl

theorem td2K1_coe_ne : ((td2K1 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) ≠ 0 := by decide

theorem td2_onLine_cases (k : ↥td2W.onLine) : k = td2K0 ∨ k = td2K1 := by
  rcases k with ⟨v, hv⟩
  by_cases h : v = (0 : Fin (td2W.ℓ + 1))
  · exact Or.inl (Subtype.ext h)
  · refine Or.inr (Subtype.ext ?_)
    have h1 : (v : ℕ) ≠ 0 := fun hh => h (Fin.ext hh)
    have h2 : (v : ℕ) < 2 := v.isLt
    exact Fin.ext (show (v : ℕ) = 1 by omega)

/-- The datum: `tdL` with slot 1 promoted on-line. Junction slot 0 pinned
exactly as in `tdL`; slot 1's condition is the FREE alphabet bound (needed by
`digit_range`, automatic on box vectors). Its per-digit counts are the point:
`2·[z < 2]` — positive on the leaf alphabet, FORCED zero on `[2, 4)`. -/
def td2L : LedgerStratumData tdD td2W td2P where
  N := 2
  hN := one_le_two
  q0 := 2
  hq0 := le_rfl
  rho0 := 1
  inStratum := fun _ x => x ((0 : ℕ), (0 : ℕ)) = 1 ∧ x ((1 : ℕ), (0 : ℕ)) < 2
  parentCond := fun _ _ => True
  slotCond := fun _ k x =>
    if k = 0 then x ((0 : ℕ), (0 : ℕ)) = 1 else x ((1 : ℕ), (0 : ℕ)) < 2
  parentBlock := ∅
  slotBlock := fun k => if k = 0 then tdBlock0 else tdBlock1
  slotCoord := fun k => (((k : Fin (td2W.ℓ + 1)) : ℕ), 0)
  cylSlot := fun _ _ => 4
  cylSlotDigits := fun _ k z =>
    if (k : Fin (td2W.ℓ + 1)) = 0 then (if z = 1 then 4 else 0)
    else (if z < 2 then 2 else 0)
  cylFiber := fun _ => 16
  cylFiberDigits := fun _ z => if z td2K0 = 1 ∧ z td2K1 < 2 then 8 else 0
  pin := fun _ => 1
  hpin_ne := fun _ _ => one_ne_zero
  hpin_lt := fun _ _ => by rw [tdD_d]; norm_num
  hexact := True

theorem td2L_supportUnion :
    td2L.supportUnion = {((0 : ℕ), (0 : ℕ)), (0, 1), (0, 2), (1, 0), (1, 1)} := by
  decide

theorem td2L_supportUnion_card : td2L.supportUnion.card = 5 := by
  rw [td2L_supportUnion]
  rfl

theorem td2_mem00 : ((0 : ℕ), (0 : ℕ)) ∈ td2L.supportUnion := by
  rw [td2L_supportUnion]; decide

theorem td2_mem10 : ((1 : ℕ), (0 : ℕ)) ∈ td2L.supportUnion := by
  rw [td2L_supportUnion]; decide

/-! ## td2 lawfulness (v2 pack) -/

theorem td2_semanticsV2 : td2L.LedgerSemanticsV2 := by
  intro ρ hρ
  refine ⟨?_, fun z => ?_⟩
  · -- fiber: 16 = 2^(5−1); the range clause is automatic on box vectors
    show (16 : ℕ) = blockCount td2L.q0 td2L.supportUnion (td2L.inStratum ρ)
    have hext : blockCount td2L.q0 td2L.supportUnion (td2L.inStratum ρ)
        = blockCount td2L.q0 td2L.supportUnion
            (fun x => x ((0 : ℕ), (0 : ℕ)) = 1) := by
      refine blockCount_congr_ext _ _ (fun v => ?_)
      constructor
      · exact fun hx => hx.1
      · intro hx
        refine ⟨hx, ?_⟩
        show (if h : ((1 : ℕ), (0 : ℕ)) ∈ td2L.supportUnion
          then ((v ⟨((1 : ℕ), (0 : ℕ)), h⟩ : Fin td2L.q0) : ℕ) else 0) < 2
        rw [dif_pos td2_mem10]
        exact Fin.is_lt _
    rw [hext, blockCount_pin td2L.q0 _ td2_mem00 one_lt_two,
      td2L_supportUnion_card]
    decide
  · by_cases hz : z td2K0 = 1 ∧ z td2K1 < 2
    · show (if z td2K0 = 1 ∧ z td2K1 < 2 then 8 else 0) = _
      rw [if_pos hz]
      have hcongr : blockCount td2L.q0 td2L.supportUnion
          (fun x => td2L.inStratum ρ x ∧
            ∀ k : ↥td2W.onLine, x (td2L.slotCoord k) = z k)
          = blockCount td2L.q0 td2L.supportUnion
              (fun x => x ((0 : ℕ), (0 : ℕ)) = 1 ∧ x ((1 : ℕ), (0 : ℕ)) = z td2K1) := by
        refine blockCount_congr _ _ (fun x => ?_)
        constructor
        · exact fun h => ⟨h.1.1, h.2 td2K1⟩
        · intro h
          refine ⟨⟨h.1, ?_⟩, fun k => ?_⟩
          · rw [h.2]; exact hz.2
          · rcases td2_onLine_cases k with hk | hk <;> subst hk
            · show x ((0 : ℕ), (0 : ℕ)) = z td2K0
              rw [h.1, hz.1]
            · exact h.2
      rw [hcongr,
        blockCount_pin2 td2L.q0 _ td2_mem00 td2_mem10 (by decide) one_lt_two hz.2,
        td2L_supportUnion_card]
      decide
    · show (if z td2K0 = 1 ∧ z td2K1 < 2 then 8 else 0) = _
      rw [if_neg hz]
      refine (blockCount_of_not _ _ _ (fun x h => hz ?_)).symm
      constructor
      · rw [← h.2 td2K0]
        exact h.1.1
      · rw [← h.2 td2K1]
        exact h.1.2

theorem td2_lawfulV2 : td2L.LedgerLawfulV2 where
  semantics := td2_semanticsV2
  member_split := by
    intro ρ x
    show (x ((0 : ℕ), (0 : ℕ)) = 1 ∧ x ((1 : ℕ), (0 : ℕ)) < 2) ↔
      (True ∧ ∀ k ∈ td2W.boxSlots,
        if k = 0 then x ((0 : ℕ), (0 : ℕ)) = 1 else x ((1 : ℕ), (0 : ℕ)) < 2)
    constructor
    · intro hx
      refine ⟨trivial, fun k _ => ?_⟩
      by_cases hk : k = 0
      · rw [if_pos hk]; exact hx.1
      · rw [if_neg hk]; exact hx.2
    · rintro ⟨-, h⟩
      have h0 := h 0 (Finset.mem_univ _)
      have h1 := h 1 (Finset.mem_univ _)
      rw [if_pos rfl] at h0
      rw [if_neg (by decide : (1 : Fin (td2W.ℓ + 1)) ≠ 0)] at h1
      exact ⟨h0, h1⟩
  parent_support := fun _ _ _ _ => Iff.rfl
  slot_support := by
    intro ρ k x y hxy
    by_cases hk : k = 0
    · have hmem : ((0 : ℕ), (0 : ℕ)) ∈ td2L.slotBlock k := by
        show _ ∈ (if k = 0 then tdBlock0 else tdBlock1)
        rw [if_pos hk]
        decide
      show (if k = 0 then x ((0 : ℕ), (0 : ℕ)) = 1 else x ((1 : ℕ), (0 : ℕ)) < 2)
        ↔ (if k = 0 then y ((0 : ℕ), (0 : ℕ)) = 1 else y ((1 : ℕ), (0 : ℕ)) < 2)
      rw [if_pos hk, if_pos hk, hxy _ hmem]
    · have hmem : ((1 : ℕ), (0 : ℕ)) ∈ td2L.slotBlock k := by
        show _ ∈ (if k = 0 then tdBlock0 else tdBlock1)
        rw [if_neg hk]
        decide
      show (if k = 0 then x ((0 : ℕ), (0 : ℕ)) = 1 else x ((1 : ℕ), (0 : ℕ)) < 2)
        ↔ (if k = 0 then y ((0 : ℕ), (0 : ℕ)) = 1 else y ((1 : ℕ), (0 : ℕ)) < 2)
      rw [if_neg hk, if_neg hk, hxy _ hmem]
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
      have hℓ : td2W.ℓ = 1 := rfl
      have hv0 : ((0 : Fin (td2W.ℓ + 1)) : ℕ) = 0 := rfl
      have hk1 : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext (h.trans hv0.symm))
      have hk'1 : (k' : ℕ) ≠ 0 := fun h => hk' (Fin.ext (h.trans hv0.symm))
      omega
  slot_coord_mem := by
    intro k
    rcases td2_onLine_cases k with h | h <;> subst h
    · show ((0 : ℕ), (0 : ℕ)) ∈ (if ((td2K0 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) = 0
        then tdBlock0 else tdBlock1)
      rw [if_pos td2K0_coe]
      decide
    · show ((1 : ℕ), (0 : ℕ)) ∈ (if ((td2K1 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) = 0
        then tdBlock0 else tdBlock1)
      rw [if_neg td2K1_coe_ne]
      decide
  parent_interior_disjoint := fun _ _ => Finset.disjoint_empty_left _
  pinned_forced := fun _ _ c hc => absurd hc (Finset.notMem_empty c)
  junction := by
    intro ρ hρ x hx hk
    exact hx.1
  digit_range := by
    intro ρ hρ x hx k
    rcases td2_onLine_cases k with h | h <;> subst h
    · show x ((0 : ℕ), (0 : ℕ)) < 2 ^ tdD.d
      rw [hx.1, tdD_d]
      norm_num
    · show x ((1 : ℕ), (0 : ℕ)) < 2 ^ tdD.d
      rw [tdD_d]
      exact Nat.lt_of_lt_of_le hx.2 (by norm_num)
  slot_sem := by
    intro ρ hρ k hk
    by_cases hkk : k = 0
    · show (4 : ℕ) = blockCount 2 (if k = 0 then tdBlock0 else tdBlock1)
        (td2L.slotCond ρ k)
      rw [if_pos hkk]
      have hcongr : blockCount 2 tdBlock0 (td2L.slotCond ρ k)
          = blockCount 2 tdBlock0 (fun x => x ((0 : ℕ), (0 : ℕ)) = 1) :=
        blockCount_congr _ _ (fun x => by
          show (if k = 0 then x ((0 : ℕ), (0 : ℕ)) = 1 else x ((1 : ℕ), (0 : ℕ)) < 2) ↔ _
          rw [if_pos hkk])
      rw [hcongr, blockCount_pin 2 tdBlock0 (by decide) one_lt_two]
      decide
    · show (4 : ℕ) = blockCount 2 (if k = 0 then tdBlock0 else tdBlock1)
        (td2L.slotCond ρ k)
      rw [if_neg hkk]
      have hstrip : blockCount 2 tdBlock1 (td2L.slotCond ρ k)
          = blockCount 2 tdBlock1 (fun x => x ((1 : ℕ), (0 : ℕ)) < 2) :=
        blockCount_congr _ _ (fun x => by
          show (if k = 0 then x ((0 : ℕ), (0 : ℕ)) = 1 else x ((1 : ℕ), (0 : ℕ)) < 2) ↔ _
          rw [if_neg hkk])
      have hall : blockCount 2 tdBlock1 (fun x => x ((1 : ℕ), (0 : ℕ)) < 2)
          = blockCount 2 tdBlock1 (fun _ => True) := by
        refine blockCount_congr_ext _ _ (fun v => ?_)
        constructor
        · exact fun _ => trivial
        · intro _
          show (if h : ((1 : ℕ), (0 : ℕ)) ∈ tdBlock1
            then ((v ⟨((1 : ℕ), (0 : ℕ)), h⟩ : Fin 2) : ℕ) else 0) < 2
          rw [dif_pos (by decide : ((1 : ℕ), (0 : ℕ)) ∈ tdBlock1)]
          exact Fin.is_lt _
      rw [hstrip, hall, blockCount_of_forall 2 tdBlock1 _ (fun _ => trivial)]
      decide
  slotDigits_sem := by
    intro ρ hρ k z
    rcases td2_onLine_cases k with hcase | hcase <;> subst hcase
    · -- junction slot: exactly the tdL pattern
      by_cases hz : z = 1
      · show (if z = 1 then 4 else 0) = blockCount 2
          (if ((td2K0 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) = 0 then tdBlock0 else tdBlock1)
          (fun x => td2L.slotCond ρ ((td2K0 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) x
            ∧ x (td2L.slotCoord td2K0) = z)
        rw [if_pos hz, if_pos td2K0_coe]
        have hcongr : blockCount 2 tdBlock0
            (fun x => td2L.slotCond ρ ((td2K0 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) x
              ∧ x (td2L.slotCoord td2K0) = z)
            = blockCount 2 tdBlock0 (fun x => x ((0 : ℕ), (0 : ℕ)) = 1) :=
          blockCount_congr _ _ (fun x => by
            show ((if ((td2K0 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) = 0
                then x ((0 : ℕ), (0 : ℕ)) = 1 else x ((1 : ℕ), (0 : ℕ)) < 2)
              ∧ x ((0 : ℕ), (0 : ℕ)) = z) ↔ _
            rw [if_pos td2K0_coe, hz, and_self])
        rw [hcongr, blockCount_pin 2 tdBlock0 (by decide) one_lt_two]
        decide
      · show (if z = 1 then 4 else 0) = blockCount 2
          (if ((td2K0 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) = 0 then tdBlock0 else tdBlock1)
          (fun x => td2L.slotCond ρ ((td2K0 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) x
            ∧ x (td2L.slotCoord td2K0) = z)
        rw [if_neg hz, if_pos td2K0_coe]
        refine (blockCount_of_not _ _ _ (fun x h => hz ?_)).symm
        have h1 : x ((0 : ℕ), (0 : ℕ)) = 1 := by
          have h' : if ((td2K0 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) = 0
              then x ((0 : ℕ), (0 : ℕ)) = 1 else x ((1 : ℕ), (0 : ℕ)) < 2 := h.1
          rwa [if_pos td2K0_coe] at h'
        have h2 : x ((0 : ℕ), (0 : ℕ)) = z := h.2
        rw [← h2, h1]
    · -- the NON-junction on-line slot: 2·[z < 2] — the alphabet seam on display
      by_cases hz : z < 2
      · show (if z < 2 then 2 else 0) = blockCount 2
          (if ((td2K1 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) = 0 then tdBlock0 else tdBlock1)
          (fun x => td2L.slotCond ρ ((td2K1 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) x
            ∧ x (td2L.slotCoord td2K1) = z)
        rw [if_pos hz, if_neg (by decide)]
        have hcongr : blockCount 2 tdBlock1
            (fun x => td2L.slotCond ρ ((td2K1 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) x
              ∧ x (td2L.slotCoord td2K1) = z)
            = blockCount 2 tdBlock1 (fun x => x ((1 : ℕ), (0 : ℕ)) = z) :=
          blockCount_congr _ _ (fun x => by
            show ((if ((td2K1 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) = 0
                then x ((0 : ℕ), (0 : ℕ)) = 1 else x ((1 : ℕ), (0 : ℕ)) < 2)
              ∧ x ((1 : ℕ), (0 : ℕ)) = z) ↔ _
            rw [if_neg (by decide)]
            exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hz, h⟩⟩)
        rw [hcongr, blockCount_pin 2 tdBlock1 (by decide) hz]
        decide
      · show (if z < 2 then 2 else 0) = blockCount 2
          (if ((td2K1 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) = 0 then tdBlock0 else tdBlock1)
          (fun x => td2L.slotCond ρ ((td2K1 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) x
            ∧ x (td2L.slotCoord td2K1) = z)
        rw [if_neg hz, if_neg (by decide)]
        refine (blockCount_of_not _ _ _ (fun x h => hz ?_)).symm
        have h' : if ((td2K1 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) = 0
            then x ((0 : ℕ), (0 : ℕ)) = 1 else x ((1 : ℕ), (0 : ℕ)) < 2 := h.1
        rw [if_neg (by decide)] at h'
        have h2 : x ((1 : ℕ), (0 : ℕ)) = z := h.2
        rw [← h2]
        exact h'
  slot_count_val := by
    intro ρ hρ k hk
    show (4 : ℕ) = 2 ^ ((tdD.period * tdD.d) * 2 - tdD.s (max 0 0))
    rw [Nat.max_self, tdD_s, tdD_period, tdD_d]
    norm_num

/-! ## td2 lawfulness (v3 seams) + family membership + firing perimeter -/

theorem td2_lawfulV3 : td2L.LedgerLawfulV3 where
  toLedgerLawfulV2 := td2_lawfulV2
  member_exists := fun ρ _ =>
    ⟨fun _ => ⟨1, td2L.hq0⟩, by
      constructor
      · show (if h : ((0 : ℕ), (0 : ℕ)) ∈ td2L.supportUnion
          then ((⟨1, td2L.hq0⟩ : Fin td2L.q0) : ℕ) else 0) = 1
        rw [dif_pos td2_mem00]
      · show (if h : ((1 : ℕ), (0 : ℕ)) ∈ td2L.supportUnion
          then ((⟨1, td2L.hq0⟩ : Fin td2L.q0) : ℕ) else 0) < 2
        rw [dif_pos td2_mem10]
        norm_num⟩
  parent_box_disjoint := fun _ _ => Finset.disjoint_empty_left _

/-- td2's carrier is IN the v3 designated family. -/
theorem td2_mem_ledgerStrataV3 : td2L.ledgerJoint ∈ LedgerStrataV3 tdD td2W td2P :=
  ⟨td2L, td2_lawfulV3, rfl⟩

theorem td2_scope : LedgerScope td2W td2P := fun _ _ => Nat.le_refl 0

theorem td2_clean : LedgerClean tdD td2W td2P td2L.N := by
  intro k hk
  show tdD.s (max 0 0) + tdD.d ≤ (tdD.period * tdD.d) * 2
  rw [Nat.max_self, tdD_s, tdD_period, tdD_d]

/-- **The supplier FIRES at td2**: the (TRANS-DEEP) row datum exists — td2 is
inside `transDeep_of_ledger`'s own firing perimeter, so the huni failure
below is not screened off by scope/clean side conditions. -/
noncomputable def td2_transDeep : TransDeep td2W td2P td2L.ledgerJoint :=
  transDeep_of_ledger td2L.ledgerJoint td2_mem_ledgerStrataV3 td2_scope td2_clean

/-! ## Part 3 — the refutations -/

/-- **Verdict at the non-degenerate extension: FALSE.** At the non-junction
on-line slot, digit z = 0 counts 2 but digit z = 2 (in the law's alphabet
`z < q^d = 4`, OFF the leaf alphabet `Fin 2`) counts 0 — the single-leaf
`slotCoord` read can never realize digits in `[q₀, q₀^d)`. -/
theorem slotUniform_td2_false : ¬ SlotUniformLaw td2W td2P td2L.ledgerJoint := by
  intro h
  have hρ : (0 : ℕ) < td2L.ledgerJoint.rhoCount 2 := by decide
  have hk : ((td2K1 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) ≠ td2W.ks := by decide
  have h02 := h 2 0 hρ td2K1 hk 0 2 (by rw [tdD_d]; norm_num) (by rw [tdD_d]; norm_num)
  have e1 : td2L.ledgerJoint.slotDigits 0 td2K1 0 2 = 2 := by decide
  have e2 : td2L.ledgerJoint.slotDigits 0 td2K1 2 2 = 0 := by decide
  rw [e1, e2] at h02
  exact absurd h02 (by norm_num)

/-- **The consumer's conclusion ALSO fails at td2**: `FreshReadsLaw` (what
`fresh_of_transDeep` would output) is false at the instance — prescribing the
off-leaf-alphabet digit 2 at the non-junction slot kills the fiber (0) while
digit 0 keeps it (8), with the junction reads agreeing. So the repair cannot
be a mere re-guard of `huni`: the (FRESH)(b) counting face itself is
unsatisfiable on the single-leaf-read carrier at d ≥ 2. -/
theorem freshReads_td2_false : ¬ FreshReadsLaw td2W td2P td2L.ledgerJoint := by
  intro h
  have hρ : (0 : ℕ) < td2L.ledgerJoint.rhoCount 2 := by decide
  have h02 := h 2 0 hρ
    (fun k => if (k : Fin (td2W.ℓ + 1)) = 0 then 1 else 0)
    (fun k => if (k : Fin (td2W.ℓ + 1)) = 0 then 1 else 2)
    (fun k => by
      show (if (k : Fin (td2W.ℓ + 1)) = 0 then (1 : ℕ) else 0) < 2 ^ tdD.d
      rw [tdD_d]
      split <;> norm_num)
    (fun k => by
      show (if (k : Fin (td2W.ℓ + 1)) = 0 then (1 : ℕ) else 2) < 2 ^ tdD.d
      rw [tdD_d]
      split <;> norm_num)
    (fun hk => rfl)
  have e1 : td2L.ledgerJoint.fiberDigits 0
      (fun k => if (k : Fin (td2W.ℓ + 1)) = 0 then 1 else 0) 2 = 8 := by decide
  have e2 : td2L.ledgerJoint.fiberDigits 0
      (fun k => if (k : Fin (td2W.ℓ + 1)) = 0 then 1 else 2) 2 = 0 := by decide
  rw [e1, e2] at h02
  exact absurd h02 (by norm_num)

/-- **The huni face is UNSATISFIABLE at the census `tdD`**: the displayed
`huni` binder of `ledger_freshRowOn` (∀ W P, ∀ J ∈ LedgerStrataV3,
SlotUniformLaw) can NEVER be discharged at tdD — td2 witnesses the failure
inside the family. The face needs restatement (module docstring) before any
supplier work. -/
theorem ledger_huni_face_false_at_tdD :
    ¬ ∀ (W : WindowDatum tdD) (P : ParentShape tdD W),
        ∀ J ∈ LedgerStrataV3 tdD W P, SlotUniformLaw W P J :=
  fun h => slotUniform_td2_false (h td2W td2P td2L.ledgerJoint td2_mem_ledgerStrataV3)

end LeanUrat.B2D

#print axioms LeanUrat.B2D.slotUniform_tdL_vacuous
#print axioms LeanUrat.B2D.blockCount_pin2
#print axioms LeanUrat.B2D.td2_lawfulV3
#print axioms LeanUrat.B2D.td2_mem_ledgerStrataV3
#print axioms LeanUrat.B2D.td2_transDeep
#print axioms LeanUrat.B2D.slotUniform_td2_false
#print axioms LeanUrat.B2D.freshReads_td2_false
#print axioms LeanUrat.B2D.ledger_huni_face_false_at_tdD
