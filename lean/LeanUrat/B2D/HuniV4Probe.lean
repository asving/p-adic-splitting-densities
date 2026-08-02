/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.TDV4_chain
import LeanUrat.B2D.HuniProbe

/-!
# B2D/HuniV4Probe — the huni-v2 ACCEPTANCE TESTS at the transported td2
  [huni repair unit; the countermodel decided against the re-keyed carrier]

`HuniProbe.td2` is the compiled huni countermodel: v3-lawful, d = 2, a
non-junction on-line slot, `SlotUniformLaw` FALSE (`slotUniform_td2_false`)
and even `FreshReadsLaw` FALSE (`freshReads_td2_false`). This file transports
td2 to the v4 (d-leaf digit-code read) carrier — `td2V4` — and compiles the
three acceptance verdicts:

* **(a) the countermodel FAILS against huni-v2**: at `td2V4` the SAME
  `SlotUniformLaw` (byte-unchanged H2 statement, same window `td2W`, parent
  `td2P`, census `tdD`) HOLDS — `slotUniform_td2V4` — and the exact failing
  pair of the refutation (z = 0 vs z = 2 at the non-junction slot, counts
  2 ≠ 0 on the v3 carrier) is now UNIFORM: `td2V4_oldPair_uniform` (1 = 1).
* **(c) the chain DELIVERS**: the supplier fires (`td2V4_transDeep`) and
  `fresh_of_transDeep` consumes `slotUniform_td2V4` to output the FULL
  (FRESH) counting shadow at the very census where the v3 conclusion was
  refuted — `td2V4_freshClauses`, in particular `td2V4_freshReads :
  FreshReadsLaw` (contrast `freshReads_td2_false`).
* (b) is upstream: `tdL`/`td2` REMAIN v3-lawful byte-unchanged
  (`td_lawfulV3`/`td2_lawfulV3` untouched; this unit adds no edit above them).

## The transport td2 → td2V4 (every delta named)

Same census `tdD` (d = 2, q₀ = 2), same window `td2W` (onLine = {0,1},
junction 0), same parent `td2P`, same pin code 1, same per-slot count value
4 = q₀^{mN−s} and same fiber 16. The deltas, all forced by the d-leaf code:

* junction block gains one leaf (`tdB0v4` = tdBlock0 + (0,3)): the D.8
  (VERTEX) pin now pins the FULL d-leaf code (2 leaves), so the block carries
  4 leaves to keep the D.11 count value 2^{mN−s} = 4 (v1–v3 pinned 1 of 3).
* junction condition pins the code: x(0,0) = 1 ∧ x(0,1) = 0 (the code-1
  read); slot 1 stays FREE — its condition is the alphabet bound on both
  leaves (automatic on box vectors), exactly td2's free-slot design.
* the read: `slotCoords k t = ((k : ℕ), t)`, `slotRead = x(k,0) + x(k,1)·2` —
  the [R1-G2] base-q₀ code. On the free slot it BIJECTS the 2-leaf box onto
  the full alphabet {0,1,2,3}: per-digit count ≡ 1, THE uniformity the v3
  single-leaf read (2·[z<2]) could not realize.
* the inherited `slotCoord` stays the designated leaf 0 (retired as a read).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.style.show false

namespace LeanUrat.B2D

open LeanUrat.Scaffold LeanUrat.Scaffold.HDischarge.H2 LeanUrat.MovesC
open LedgerStratumData LedgerStratumDataV4

/-! ## The transported datum -/

/-- The v4 junction block: `tdBlock0` + the leaf (0,3) — 4 leaves, so pinning
the full 2-leaf code keeps the per-slot count at 2^{mN−s} = 4. -/
def tdB0v4 : Finset Coord := {((0 : ℕ), (0 : ℕ)), (0, 1), (0, 2), (0, 3)}

def td2V4 : LedgerStratumDataV4 tdD td2W td2P where
  N := 2
  hN := one_le_two
  q0 := 2
  hq0 := le_rfl
  rho0 := 1
  inStratum := fun _ x =>
    (x ((0 : ℕ), (0 : ℕ)) = 1 ∧ x ((0 : ℕ), (1 : ℕ)) = 0) ∧
    (x ((1 : ℕ), (0 : ℕ)) < 2 ∧ x ((1 : ℕ), (1 : ℕ)) < 2)
  parentCond := fun _ _ => True
  slotCond := fun _ k x =>
    if k = 0 then x ((0 : ℕ), (0 : ℕ)) = 1 ∧ x ((0 : ℕ), (1 : ℕ)) = 0
    else x ((1 : ℕ), (0 : ℕ)) < 2 ∧ x ((1 : ℕ), (1 : ℕ)) < 2
  parentBlock := ∅
  slotBlock := fun k => if k = 0 then tdB0v4 else tdBlock1
  slotCoord := fun k => (((k : Fin (td2W.ℓ + 1)) : ℕ), 0)
  cylSlot := fun _ _ => 4
  cylSlotDigits := fun _ k z =>
    if (k : Fin (td2W.ℓ + 1)) = 0 then (if z = 1 then 4 else 0)
    else (if z < 4 then 1 else 0)
  cylFiber := fun _ => 16
  cylFiberDigits := fun _ z => if z td2K0 = 1 ∧ z td2K1 < 4 then 4 else 0
  pin := fun _ => 1
  hpin_ne := fun _ _ => one_ne_zero
  hpin_lt := fun _ _ => by rw [tdD_d]; norm_num
  hexact := True
  slotCoords := fun k t => (((k : Fin (td2W.ℓ + 1)) : ℕ), t)

/-! ## Read evaluation + support geometry -/

/-- The d-leaf read at the instance, evaluated: the base-2 code of the two
leaves of slot k. -/
theorem td2V4_slotRead_eval (x : Coord → ℕ) (k : ↥td2W.onLine) :
    td2V4.slotRead x k
      = x (((k : Fin (td2W.ℓ + 1)) : ℕ), 0) + x (((k : Fin (td2W.ℓ + 1)) : ℕ), 1) * 2 := by
  show ∑ t ∈ Finset.range tdD.d,
      x (((k : Fin (td2W.ℓ + 1)) : ℕ), t) * (2 : ℕ) ^ t
    = x (((k : Fin (td2W.ℓ + 1)) : ℕ), 0) + x (((k : Fin (td2W.ℓ + 1)) : ℕ), 1) * 2
  rw [tdD_d, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, mul_one, pow_one]

theorem td2V4_slotRead_K0 (x : Coord → ℕ) :
    td2V4.slotRead x td2K0 = x ((0 : ℕ), (0 : ℕ)) + x ((0 : ℕ), (1 : ℕ)) * 2 :=
  td2V4_slotRead_eval x td2K0

theorem td2V4_slotRead_K1 (x : Coord → ℕ) :
    td2V4.slotRead x td2K1 = x ((1 : ℕ), (0 : ℕ)) + x ((1 : ℕ), (1 : ℕ)) * 2 :=
  td2V4_slotRead_eval x td2K1

theorem td2V4_supportUnion :
    td2V4.toLedgerStratumData.supportUnion
      = {((0 : ℕ), (0 : ℕ)), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1)} := by
  decide

theorem td2V4_supportUnion_card : td2V4.toLedgerStratumData.supportUnion.card = 6 := by
  rw [td2V4_supportUnion]
  rfl

theorem td2V4_mem00 : ((0 : ℕ), (0 : ℕ)) ∈ td2V4.toLedgerStratumData.supportUnion := by
  rw [td2V4_supportUnion]; decide

theorem td2V4_mem01 : ((0 : ℕ), (1 : ℕ)) ∈ td2V4.toLedgerStratumData.supportUnion := by
  rw [td2V4_supportUnion]; decide

theorem td2V4_supportUnion_split :
    td2V4.toLedgerStratumData.supportUnion = tdB0v4 ∪ tdBlock1 := by
  decide

/-- The junction slot condition, exposed (the `if` gate resolved at the
junction coordinate). -/
theorem td2V4_slotCond_junction (ρ : ℕ) (x : Coord → ℕ) :
    td2V4.slotCond ρ ((td2K0 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) x
      ↔ (x ((0 : ℕ), (0 : ℕ)) = 1 ∧ x ((0 : ℕ), (1 : ℕ)) = 0) := by
  show (if ((td2K0 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) = 0
      then x ((0 : ℕ), (0 : ℕ)) = 1 ∧ x ((0 : ℕ), (1 : ℕ)) = 0
      else x ((1 : ℕ), (0 : ℕ)) < 2 ∧ x ((1 : ℕ), (1 : ℕ)) < 2) ↔ _
  rw [if_pos td2K0_coe]

/-- The free (non-junction) slot condition, exposed. -/
theorem td2V4_slotCond_free (ρ : ℕ) (x : Coord → ℕ) :
    td2V4.slotCond ρ ((td2K1 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) x
      ↔ (x ((1 : ℕ), (0 : ℕ)) < 2 ∧ x ((1 : ℕ), (1 : ℕ)) < 2) := by
  show (if ((td2K1 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) = 0
      then x ((0 : ℕ), (0 : ℕ)) = 1 ∧ x ((0 : ℕ), (1 : ℕ)) = 0
      else x ((1 : ℕ), (0 : ℕ)) < 2 ∧ x ((1 : ℕ), (1 : ℕ)) < 2) ↔ _
  rw [if_neg td2K1_coe_ne]

/-! ## v4 lawfulness at the instance -/

/-- The compiled member of td2V4: junction code 1 (leaf (0,0) = 1, leaf
(0,1) = 0), every other leaf 0. -/
def td2V4wit : ↥td2V4.toLedgerStratumData.supportUnion → Fin td2V4.q0 :=
  fun c => if (c : Coord) = ((0 : ℕ), (0 : ℕ))
    then ⟨1, td2V4.hq0⟩ else ⟨0, Nat.lt_of_lt_of_le two_pos td2V4.hq0⟩

theorem td2V4wit_mem (ρ : ℕ) :
    td2V4.inStratum ρ (fun c =>
      if h : c ∈ td2V4.toLedgerStratumData.supportUnion
      then (td2V4wit ⟨c, h⟩ : ℕ) else 0) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · show (if h : ((0 : ℕ), (0 : ℕ)) ∈ td2V4.toLedgerStratumData.supportUnion
        then (td2V4wit ⟨((0 : ℕ), (0 : ℕ)), h⟩ : ℕ) else 0) = 1
    rw [dif_pos td2V4_mem00]
    show (((if ((((0 : ℕ), (0 : ℕ)) : Coord) = ((0 : ℕ), (0 : ℕ)))
        then (⟨1, td2V4.hq0⟩ : Fin td2V4.q0)
        else ⟨0, Nat.lt_of_lt_of_le two_pos td2V4.hq0⟩ : Fin td2V4.q0)) : ℕ) = 1
    rw [if_pos rfl]
  · show (if h : ((0 : ℕ), (1 : ℕ)) ∈ td2V4.toLedgerStratumData.supportUnion
        then (td2V4wit ⟨((0 : ℕ), (1 : ℕ)), h⟩ : ℕ) else 0) = 0
    rw [dif_pos td2V4_mem01]
    show (((if ((((0 : ℕ), (1 : ℕ)) : Coord) = ((0 : ℕ), (0 : ℕ)))
        then (⟨1, td2V4.hq0⟩ : Fin td2V4.q0)
        else ⟨0, Nat.lt_of_lt_of_le two_pos td2V4.hq0⟩ : Fin td2V4.q0)) : ℕ) = 0
    rw [if_neg (by decide)]
  · show (if h : ((1 : ℕ), (0 : ℕ)) ∈ td2V4.toLedgerStratumData.supportUnion
        then (td2V4wit ⟨((1 : ℕ), (0 : ℕ)), h⟩ : ℕ) else 0) < 2
    split
    · exact Fin.is_lt _
    · norm_num
  · show (if h : ((1 : ℕ), (1 : ℕ)) ∈ td2V4.toLedgerStratumData.supportUnion
        then (td2V4wit ⟨((1 : ℕ), (1 : ℕ)), h⟩ : ℕ) else 0) < 2
    split
    · exact Fin.is_lt _
    · norm_num

theorem td2V4_semantics : td2V4.LedgerSemanticsV4 := by
  intro ρ hρ
  constructor
  · -- fiber: 16 = 2^(6−2); the free-slot bounds are automatic on box vectors
    show (16 : ℕ) = blockCount 2 td2V4.toLedgerStratumData.supportUnion (td2V4.inStratum ρ)
    have hext : blockCount 2 td2V4.toLedgerStratumData.supportUnion (td2V4.inStratum ρ)
        = blockCount 2 td2V4.toLedgerStratumData.supportUnion
            (fun x => x ((0 : ℕ), (0 : ℕ)) = 1 ∧ x ((0 : ℕ), (1 : ℕ)) = 0) := by
      refine blockCount_congr_ext _ _ (fun v => ?_)
      constructor
      · exact fun hx => hx.1
      · intro hx
        refine ⟨hx, ?_, ?_⟩
        · show (if h : ((1 : ℕ), (0 : ℕ)) ∈ td2V4.toLedgerStratumData.supportUnion
            then ((v ⟨((1 : ℕ), (0 : ℕ)), h⟩ : Fin td2V4.q0) : ℕ) else 0) < 2
          split
          · exact Fin.is_lt _
          · norm_num
        · show (if h : ((1 : ℕ), (1 : ℕ)) ∈ td2V4.toLedgerStratumData.supportUnion
            then ((v ⟨((1 : ℕ), (1 : ℕ)), h⟩ : Fin td2V4.q0) : ℕ) else 0) < 2
          split
          · exact Fin.is_lt _
          · norm_num
    rw [hext, blockCount_pin2 2 _ td2V4_mem00 td2V4_mem01 (by decide) one_lt_two (by norm_num),
      td2V4_supportUnion_card]
    decide
  · -- prescribed READ CODES: junction code pinned to 1, free-slot code bijects
    intro z
    by_cases hz : z td2K0 = 1 ∧ z td2K1 < 4
    · show (if z td2K0 = 1 ∧ z td2K1 < 4 then 4 else 0)
        = blockCount 2 td2V4.toLedgerStratumData.supportUnion
            (fun x => td2V4.inStratum ρ x ∧
              ∀ k : ↥td2W.onLine, td2V4.slotRead x k = z k)
      rw [if_pos hz]
      have hcongr : blockCount 2 td2V4.toLedgerStratumData.supportUnion
          (fun x => td2V4.inStratum ρ x ∧
            ∀ k : ↥td2W.onLine, td2V4.slotRead x k = z k)
          = blockCount 2 td2V4.toLedgerStratumData.supportUnion
              (fun x => (x ((0 : ℕ), (0 : ℕ)) = 1 ∧ x ((0 : ℕ), (1 : ℕ)) = 0)
                ∧ (x ((1 : ℕ), (0 : ℕ)) = z td2K1 % 2 ∧ x ((1 : ℕ), (1 : ℕ)) = z td2K1 / 2)) := by
        refine blockCount_congr _ _ (fun x => ?_)
        constructor
        · rintro ⟨⟨hj, hb⟩, hreads⟩
          have h1 := hreads td2K1
          rw [td2V4_slotRead_K1] at h1
          exact ⟨hj, by omega, by omega⟩
        · rintro ⟨⟨h00, h01⟩, h10, h11⟩
          have hz2 := hz.2
          refine ⟨⟨⟨h00, h01⟩, by omega, by omega⟩, fun k => ?_⟩
          rcases td2_onLine_cases k with hk | hk <;> subst hk
          · rw [td2V4_slotRead_K0, h00, h01, hz.1]
          · rw [td2V4_slotRead_K1, h10, h11]
            omega
      have hsup0 : ∀ x y : Coord → ℕ, (∀ c ∈ tdB0v4, x c = y c) →
          ((x ((0 : ℕ), (0 : ℕ)) = 1 ∧ x ((0 : ℕ), (1 : ℕ)) = 0)
            ↔ (y ((0 : ℕ), (0 : ℕ)) = 1 ∧ y ((0 : ℕ), (1 : ℕ)) = 0)) := by
        intro x y hxy
        rw [hxy ((0 : ℕ), (0 : ℕ)) (by decide), hxy ((0 : ℕ), (1 : ℕ)) (by decide)]
      have hsup1 : ∀ x y : Coord → ℕ, (∀ c ∈ tdBlock1, x c = y c) →
          ((x ((1 : ℕ), (0 : ℕ)) = z td2K1 % 2 ∧ x ((1 : ℕ), (1 : ℕ)) = z td2K1 / 2)
            ↔ (y ((1 : ℕ), (0 : ℕ)) = z td2K1 % 2 ∧ y ((1 : ℕ), (1 : ℕ)) = z td2K1 / 2)) := by
        intro x y hxy
        rw [hxy ((1 : ℕ), (0 : ℕ)) (by decide), hxy ((1 : ℕ), (1 : ℕ)) (by decide)]
      have hdiv : z td2K1 / 2 < 2 := by
        have := hz.2
        omega
      rw [hcongr, td2V4_supportUnion_split,
        blockCount_union_split 2 (by decide : Disjoint tdB0v4 tdBlock1) hsup0 hsup1,
        blockCount_pin2 2 tdB0v4 (by decide) (by decide) (by decide) one_lt_two (by norm_num),
        blockCount_pin2 2 tdBlock1 (by decide) (by decide) (by decide)
          (Nat.mod_lt _ two_pos) hdiv]
      decide
    · show (if z td2K0 = 1 ∧ z td2K1 < 4 then 4 else 0) = _
      rw [if_neg hz]
      refine (blockCount_of_not _ _ _ (fun x hx => hz ?_)).symm
      obtain ⟨⟨⟨h00, h01⟩, h10, h11⟩, hreads⟩ := hx
      have hr0 := hreads td2K0
      have hr1 := hreads td2K1
      rw [td2V4_slotRead_K0] at hr0
      rw [td2V4_slotRead_K1] at hr1
      constructor
      · omega
      · omega

theorem td2V4_lawfulV4 : td2V4.LedgerLawfulV4 where
  semantics := td2V4_semantics
  member_split := by
    intro ρ x
    show ((x ((0 : ℕ), (0 : ℕ)) = 1 ∧ x ((0 : ℕ), (1 : ℕ)) = 0)
        ∧ (x ((1 : ℕ), (0 : ℕ)) < 2 ∧ x ((1 : ℕ), (1 : ℕ)) < 2)) ↔
      (True ∧ ∀ k ∈ td2W.boxSlots,
        if k = 0 then x ((0 : ℕ), (0 : ℕ)) = 1 ∧ x ((0 : ℕ), (1 : ℕ)) = 0
        else x ((1 : ℕ), (0 : ℕ)) < 2 ∧ x ((1 : ℕ), (1 : ℕ)) < 2)
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
    · have hm0 : ((0 : ℕ), (0 : ℕ)) ∈ td2V4.slotBlock k := by
        show _ ∈ (if k = 0 then tdB0v4 else tdBlock1)
        rw [if_pos hk]; decide
      have hm1 : ((0 : ℕ), (1 : ℕ)) ∈ td2V4.slotBlock k := by
        show _ ∈ (if k = 0 then tdB0v4 else tdBlock1)
        rw [if_pos hk]; decide
      show (if k = 0 then x ((0 : ℕ), (0 : ℕ)) = 1 ∧ x ((0 : ℕ), (1 : ℕ)) = 0
          else x ((1 : ℕ), (0 : ℕ)) < 2 ∧ x ((1 : ℕ), (1 : ℕ)) < 2)
        ↔ (if k = 0 then y ((0 : ℕ), (0 : ℕ)) = 1 ∧ y ((0 : ℕ), (1 : ℕ)) = 0
          else y ((1 : ℕ), (0 : ℕ)) < 2 ∧ y ((1 : ℕ), (1 : ℕ)) < 2)
      rw [if_pos hk, if_pos hk, hxy _ hm0, hxy _ hm1]
    · have hm0 : ((1 : ℕ), (0 : ℕ)) ∈ td2V4.slotBlock k := by
        show _ ∈ (if k = 0 then tdB0v4 else tdBlock1)
        rw [if_neg hk]; decide
      have hm1 : ((1 : ℕ), (1 : ℕ)) ∈ td2V4.slotBlock k := by
        show _ ∈ (if k = 0 then tdB0v4 else tdBlock1)
        rw [if_neg hk]; decide
      show (if k = 0 then x ((0 : ℕ), (0 : ℕ)) = 1 ∧ x ((0 : ℕ), (1 : ℕ)) = 0
          else x ((1 : ℕ), (0 : ℕ)) < 2 ∧ x ((1 : ℕ), (1 : ℕ)) < 2)
        ↔ (if k = 0 then y ((0 : ℕ), (0 : ℕ)) = 1 ∧ y ((0 : ℕ), (1 : ℕ)) = 0
          else y ((1 : ℕ), (0 : ℕ)) < 2 ∧ y ((1 : ℕ), (1 : ℕ)) < 2)
      rw [if_neg hk, if_neg hk, hxy _ hm0, hxy _ hm1]
  slots_disjoint := by
    intro k k' hkk
    show Disjoint (if k = 0 then tdB0v4 else tdBlock1)
      (if k' = 0 then tdB0v4 else tdBlock1)
    have hd : Disjoint tdB0v4 tdBlock1 := by decide
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
  slot_coords_mem := by
    intro k t ht
    rw [tdD_d] at ht
    rcases td2_onLine_cases k with hk | hk <;> subst hk
    · show ((0 : ℕ), t) ∈ (if ((td2K0 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) = 0
        then tdB0v4 else tdBlock1)
      rw [if_pos td2K0_coe]
      interval_cases t <;> decide
    · show ((1 : ℕ), t) ∈ (if ((td2K1 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) = 0
        then tdB0v4 else tdBlock1)
      rw [if_neg td2K1_coe_ne]
      interval_cases t <;> decide
  parent_interior_disjoint := fun _ _ => Finset.disjoint_empty_left _
  pinned_forced := fun _ _ c hc => absurd hc (Finset.notMem_empty c)
  junction := by
    intro ρ hρ x hx hk
    show td2V4.slotRead x ⟨td2W.ks, hk⟩ = 1
    have he : td2V4.slotRead x ⟨td2W.ks, hk⟩
        = x ((0 : ℕ), (0 : ℕ)) + x ((0 : ℕ), (1 : ℕ)) * 2 :=
      td2V4_slotRead_eval x ⟨td2W.ks, hk⟩
    rw [he, hx.1.1, hx.1.2]
  digit_range := by
    intro ρ hρ x hx k
    rcases td2_onLine_cases k with hk | hk <;> subst hk
    · show td2V4.slotRead x td2K0 < 2 ^ tdD.d
      rw [td2V4_slotRead_K0, hx.1.1, hx.1.2, tdD_d]
      norm_num
    · show td2V4.slotRead x td2K1 < 2 ^ tdD.d
      rw [td2V4_slotRead_K1, tdD_d]
      have h1 := hx.2.1
      have h2 := hx.2.2
      have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
      rw [h4]
      omega
  slot_sem := by
    intro ρ hρ k hk
    by_cases hkk : k = 0
    · show (4 : ℕ) = blockCount 2 (if k = 0 then tdB0v4 else tdBlock1)
        (td2V4.slotCond ρ k)
      rw [if_pos hkk]
      have hcongr : blockCount 2 tdB0v4 (td2V4.slotCond ρ k)
          = blockCount 2 tdB0v4
              (fun x => x ((0 : ℕ), (0 : ℕ)) = 1 ∧ x ((0 : ℕ), (1 : ℕ)) = 0) :=
        blockCount_congr _ _ (fun x => by
          show (if k = 0 then x ((0 : ℕ), (0 : ℕ)) = 1 ∧ x ((0 : ℕ), (1 : ℕ)) = 0
            else x ((1 : ℕ), (0 : ℕ)) < 2 ∧ x ((1 : ℕ), (1 : ℕ)) < 2) ↔ _
          rw [if_pos hkk])
      rw [hcongr,
        blockCount_pin2 2 tdB0v4 (by decide) (by decide) (by decide) one_lt_two (by norm_num)]
      decide
    · show (4 : ℕ) = blockCount 2 (if k = 0 then tdB0v4 else tdBlock1)
        (td2V4.slotCond ρ k)
      rw [if_neg hkk]
      have hstrip : blockCount 2 tdBlock1 (td2V4.slotCond ρ k)
          = blockCount 2 tdBlock1
              (fun x => x ((1 : ℕ), (0 : ℕ)) < 2 ∧ x ((1 : ℕ), (1 : ℕ)) < 2) :=
        blockCount_congr _ _ (fun x => by
          show (if k = 0 then x ((0 : ℕ), (0 : ℕ)) = 1 ∧ x ((0 : ℕ), (1 : ℕ)) = 0
            else x ((1 : ℕ), (0 : ℕ)) < 2 ∧ x ((1 : ℕ), (1 : ℕ)) < 2) ↔ _
          rw [if_neg hkk])
      have hall : blockCount 2 tdBlock1
          (fun x => x ((1 : ℕ), (0 : ℕ)) < 2 ∧ x ((1 : ℕ), (1 : ℕ)) < 2)
          = blockCount 2 tdBlock1 (fun _ => True) := by
        refine blockCount_congr_ext _ _ (fun v => ?_)
        constructor
        · exact fun _ => trivial
        · intro _
          constructor
          · show (if h : ((1 : ℕ), (0 : ℕ)) ∈ tdBlock1
              then ((v ⟨((1 : ℕ), (0 : ℕ)), h⟩ : Fin 2) : ℕ) else 0) < 2
            rw [dif_pos (by decide : ((1 : ℕ), (0 : ℕ)) ∈ tdBlock1)]
            exact Fin.is_lt _
          · show (if h : ((1 : ℕ), (1 : ℕ)) ∈ tdBlock1
              then ((v ⟨((1 : ℕ), (1 : ℕ)), h⟩ : Fin 2) : ℕ) else 0) < 2
            rw [dif_pos (by decide : ((1 : ℕ), (1 : ℕ)) ∈ tdBlock1)]
            exact Fin.is_lt _
      rw [hstrip, hall, blockCount_of_forall 2 tdBlock1 _ (fun _ => trivial)]
      decide
  slotDigits_sem := by
    intro ρ hρ k z
    rcases td2_onLine_cases k with hcase | hcase <;> subst hcase
    · -- junction slot: the code is PINNED to 1 by the slot condition
      by_cases hz : z = 1
      · show (if z = 1 then 4 else 0) = blockCount 2
          (if ((td2K0 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) = 0 then tdB0v4 else tdBlock1)
          (fun x => td2V4.slotCond ρ ((td2K0 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) x
            ∧ td2V4.slotRead x td2K0 = z)
        rw [if_pos hz, if_pos td2K0_coe]
        have hcongr : blockCount 2 tdB0v4
            (fun x => td2V4.slotCond ρ ((td2K0 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) x
              ∧ td2V4.slotRead x td2K0 = z)
            = blockCount 2 tdB0v4
                (fun x => x ((0 : ℕ), (0 : ℕ)) = 1 ∧ x ((0 : ℕ), (1 : ℕ)) = 0) := by
          refine blockCount_congr _ _ (fun x => ?_)
          rw [td2V4_slotRead_K0, td2V4_slotCond_junction ρ x]
          constructor
          · exact fun h => h.1
          · intro hp
            refine ⟨hp, ?_⟩
            rw [hp.1, hp.2, hz]
        rw [hcongr,
          blockCount_pin2 2 tdB0v4 (by decide) (by decide) (by decide) one_lt_two (by norm_num)]
        decide
      · show (if z = 1 then 4 else 0) = blockCount 2
          (if ((td2K0 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) = 0 then tdB0v4 else tdBlock1)
          (fun x => td2V4.slotCond ρ ((td2K0 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) x
            ∧ td2V4.slotRead x td2K0 = z)
        rw [if_neg hz, if_pos td2K0_coe]
        refine (blockCount_of_not _ _ _ (fun x h => hz ?_)).symm
        have hc := (td2V4_slotCond_junction ρ x).mp h.1
        have hr := h.2
        rw [td2V4_slotRead_K0, hc.1, hc.2] at hr
        omega
    · -- the NON-junction on-line slot: the free 2-leaf box BIJECTS onto the
      -- full code alphabet [0,4) — per-digit count ≡ 1, huni's uniformity
      by_cases hz : z < 4
      · show (if z < 4 then 1 else 0) = blockCount 2
          (if ((td2K1 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) = 0 then tdB0v4 else tdBlock1)
          (fun x => td2V4.slotCond ρ ((td2K1 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) x
            ∧ td2V4.slotRead x td2K1 = z)
        rw [if_pos hz, if_neg td2K1_coe_ne]
        have hcongr : blockCount 2 tdBlock1
            (fun x => td2V4.slotCond ρ ((td2K1 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) x
              ∧ td2V4.slotRead x td2K1 = z)
            = blockCount 2 tdBlock1
                (fun x => x ((1 : ℕ), (0 : ℕ)) = z % 2 ∧ x ((1 : ℕ), (1 : ℕ)) = z / 2) := by
          refine blockCount_congr _ _ (fun x => ?_)
          rw [td2V4_slotRead_K1, td2V4_slotCond_free ρ x]
          constructor
          · rintro ⟨⟨hb0, hb1⟩, hr⟩
            exact ⟨by omega, by omega⟩
          · rintro ⟨h0, h1⟩
            exact ⟨⟨by omega, by omega⟩, by omega⟩
        rw [hcongr,
          blockCount_pin2 2 tdBlock1 (by decide) (by decide) (by decide)
            (Nat.mod_lt _ two_pos) (by omega)]
        decide
      · show (if z < 4 then 1 else 0) = blockCount 2
          (if ((td2K1 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) = 0 then tdB0v4 else tdBlock1)
          (fun x => td2V4.slotCond ρ ((td2K1 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) x
            ∧ td2V4.slotRead x td2K1 = z)
        rw [if_neg hz, if_neg td2K1_coe_ne]
        refine (blockCount_of_not _ _ _ (fun x h => hz ?_)).symm
        have hc := (td2V4_slotCond_free ρ x).mp h.1
        have hr := h.2
        rw [td2V4_slotRead_K1] at hr
        omega
  slot_count_val := by
    intro ρ hρ k hk
    show (4 : ℕ) = 2 ^ ((tdD.period * tdD.d) * 2 - tdD.s (max 0 0))
    rw [Nat.max_self, tdD_s, tdD_period, tdD_d]
    norm_num
  member_exists := fun ρ _ => ⟨td2V4wit, td2V4wit_mem ρ⟩
  parent_box_disjoint := fun _ _ => Finset.disjoint_empty_left _

/-! ## Family membership + firing perimeter -/

/-- td2V4's carrier is IN the v4 designated family. -/
theorem td2V4_mem_ledgerStrataV4 :
    td2V4.toLedgerStratumData.ledgerJoint ∈ LedgerStrataV4 tdD td2W td2P :=
  ⟨td2V4, td2V4_lawfulV4, rfl⟩

theorem td2V4_scope : LedgerScope td2W td2P := td2_scope

theorem td2V4_clean : LedgerClean tdD td2W td2P td2V4.N := td2_clean

/-- **The v4 supplier FIRES at td2V4**: the (TRANS-DEEP) row datum exists at
the transported countermodel instance. -/
noncomputable def td2V4_transDeep :
    TransDeep td2W td2P td2V4.toLedgerStratumData.ledgerJoint :=
  transDeep_of_ledger_v4 td2V4.toLedgerStratumData.ledgerJoint
    td2V4_mem_ledgerStrataV4 td2V4_scope td2V4_clean

/-! ## ACCEPTANCE (a): the countermodel FAILS against huni-v2 -/

/-- **huni-v2 HOLDS at the transported countermodel** — the SAME
`SlotUniformLaw` (H2 statement byte-unchanged, same `td2W`/`td2P`/`tdD`) that
`slotUniform_td2_false` refuted on the v3 single-leaf carrier is TRUE on the
d-leaf-code carrier: at the non-junction on-line slot every in-alphabet code
`z < q^d` counts exactly 1. -/
theorem slotUniform_td2V4 :
    SlotUniformLaw td2W td2P td2V4.toLedgerStratumData.ledgerJoint := by
  intro q ρ hρ k hk z z' hz hz'
  by_cases hq : q = td2V4.q0
  · subst hq
    rcases td2_onLine_cases k with hcase | hcase <;> subst hcase
    · exact absurd (by decide : ((td2K0 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) = td2W.ks) hk
    · have h4 : td2V4.q0 ^ tdD.d = 4 := by
        show (2 : ℕ) ^ tdD.d = 4
        rw [tdD_d]
        norm_num
      rw [h4] at hz hz'
      have e : ∀ w : ℕ, w < 4 →
          td2V4.toLedgerStratumData.ledgerJoint.slotDigits ρ td2K1 w td2V4.q0 = 1 := by
        intro w hw
        show (if td2V4.q0 = td2V4.q0 then td2V4.cylSlotDigits ρ td2K1 w else 0) = 1
        rw [if_pos rfl]
        show (if ((td2K1 : ↥td2W.onLine) : Fin (td2W.ℓ + 1)) = 0
          then (if w = 1 then 4 else 0) else (if w < 4 then 1 else 0)) = 1
        rw [if_neg td2K1_coe_ne, if_pos hw]
      rw [e z hz, e z' hz']
  · rw [ledger_rhoCount_off_support td2V4.toLedgerStratumData q hq] at hρ
    omega

/-- **The exact old failing pair no longer violates**: the refutation's
witness pair (z = 0 vs z = 2 at the non-junction slot, counts 2 ≠ 0 at the
v3 carrier — `HuniProbe.slotUniform_td2_false`) is UNIFORM at td2V4: both
codes count 1. -/
theorem td2V4_oldPair_uniform :
    td2V4.toLedgerStratumData.ledgerJoint.slotDigits 0 td2K1 0 2
      = td2V4.toLedgerStratumData.ledgerJoint.slotDigits 0 td2K1 2 2 := by
  decide

/-! ## ACCEPTANCE (c): the chain DELIVERS at the repaired carrier -/

/-- **The consumer chain fires end-to-end**: `fresh_of_transDeep` consumes
the v4 row + huni-v2 and outputs the FULL (FRESH) counting shadow at the
census/window where the v3 chain's output was compiled-false. -/
theorem td2V4_freshClauses :
    FreshClauses td2W td2P td2V4.toLedgerStratumData.ledgerJoint :=
  fresh_of_transDeep td2W td2P td2V4.toLedgerStratumData.ledgerJoint
    td2V4_transDeep slotUniform_td2V4

/-- **`FreshReadsLaw` DELIVERED** — the exact consumer conclusion that is
FALSE at the v3 carrier (`HuniProbe.freshReads_td2_false`) holds at the
d-leaf-read transport. The chain, not just the law, is repaired. -/
theorem td2V4_freshReads :
    FreshReadsLaw td2W td2P td2V4.toLedgerStratumData.ledgerJoint :=
  td2V4_freshClauses.freshReads

end LeanUrat.B2D

#print axioms LeanUrat.B2D.td2V4_semantics
#print axioms LeanUrat.B2D.td2V4_lawfulV4
#print axioms LeanUrat.B2D.td2V4_mem_ledgerStrataV4
#print axioms LeanUrat.B2D.td2V4_transDeep
#print axioms LeanUrat.B2D.slotUniform_td2V4
#print axioms LeanUrat.B2D.td2V4_oldPair_uniform
#print axioms LeanUrat.B2D.td2V4_freshClauses
#print axioms LeanUrat.B2D.td2V4_freshReads
