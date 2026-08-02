/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.TD0_ledgerInstance

/-!
# B2D/TD3v2_countermodel — TD-3 ROUND 2 (the v2 restatement) is ALSO refuted
  [B2DEF_LEAN unit TD-3; wave 1, round 2 — FAILURE OUTCOME, second seam class]

Blueprint §5 TD-3 (round-2 status). deps: TDDefsV2, TD3v2_control,
TD0_ledgerInstance (for `blockCount_pin`). The frozen goal
`ledger_digitsProd` (TD3_digitsProd.lean) STANDS byte-unchanged; this file is
the compiled adjudication that its round-2 statement does not admit the
intended proof.

## What broke, precisely (two seams the v2 pack does not close)

The intended MOVES D.11 finite-box product argument factors a member count
over `supportUnion = parentBlock ∪ ⋃_{k ∈ boxSlots} slotBlock k` as
(parent factor) × ∏ (slot factors), with the parent factor = 1. The v2
`LedgerLawfulV2` pack supplies the INJECTIVITY half (`pinned_forced`: two
members with equal slot restrictions agree on the parent block) but NOT the
two facts the equality needs:

* **Seam A (parent satisfiability).** No clause makes the per-realization
  member set (equivalently, the parent condition) satisfiable: `inStratum ≡
  parentCond ≡ False` is lawful (all member-quantified clauses hold
  vacuously; `blockCount` of `False` is 0, matching zero counting fields),
  yet `slot_count_val` forces every off-line product factor positive.
  Witness `cmL4`: LHS 0 ≠ 2 RHS (`cm4_not_digitsProd`).
* **Seam B (parent/slot overlap).** `parent_interior_disjoint` fences the
  parent block off INTERIOR ON-LINE slot blocks only ((ii.3) verbatim); a
  parent condition may read — and cut — inside an OFF-LINE slot's block (or
  the junction's). The joint count then loses a factor the product side
  still prices in full through `slot_sem`/`slot_count_val`. Witness `cmL3`:
  `parentBlock = {(0,0)} = slotBlock 0` (an off-line box slot), `parentCond =
  (x(0,0) = 1)`: the stratum is NONEMPTY, every clause including
  `pinned_forced` holds substantively, `LedgerScope`/`LedgerClean` hold —
  and the law fails as 1 ≠ 2 (`cm3_not_digitsProd`). So the refutation is
  NOT an emptiness pathology.

`ledger_digitsProd_v2_refuted` is the ¬∀ of TD-3 round 2's exact statement.

## Why the round-2 gates did not catch this

The N-TD1 trace instances (i1/i2/i3) all have `parentBlock = []` and carry
the junction pin inside the junction's own `slotCond` — on that subfamily
both seams are closed silently (parentCond ≡ True is satisfiable and
overlap-free), and there the law is TRUE (compiled positive controls:
`cm2_digitsProd`, onLine = ∅; `td_digitsProd`, r = 1 with genuine on-line
digit content). `TD3v2_control.v2_mechanism_inapplicable` only certified the
¬∀ of the V1 refutation MECHANISM — mechanism-inapplicability never implied
the ∀-law. The v2 statement round repaired the counting semantics (the v1
seam) and the N-TD1 [LHS-V2] 3/3 match shows the semantics now counts what
the product prices AT THE PROBED SUBFAMILY; the lawfulness PACK is what is
still too weak.

## What a v3 statement round must add (recorded, NOT executed here —
statement fence: no restatement without a fresh E-phase round)

(i) per-realization member existence (equivalently parent satisfiability
compatible with the slot conditions — the surjectivity half of D.11's
bijection), and (ii) parent-block disjointness from EVERY box slot's block
(the trace geometry: the junction pin rides the junction's own `slotCond`,
so full disjointness is faithful to the intended instances). The TD-0
designated instance `tdL` satisfies both already (`parentBlock = ∅`), so it
survives a v3 round unchanged.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.style.show false

namespace LeanUrat.B2D

open LeanUrat.Scaffold LeanUrat.Scaffold.HDischarge.H2 LeanUrat.MovesC LedgerStratumData

/-! ## Seam B witness: parent condition cutting inside an OFF-LINE slot block
(nonempty stratum; every clause substantive where it can be) -/

/-- The overlap countermodel: the control geometry (`cmD`/`cmW`/`cmP`) with
`parentBlock = {(0,0)} = slotBlock 0` (slot 0 is an off-line BOX slot) and
the parent condition pinning the shared leaf. Fiber counts are the true
finite-box counts (= 1); the slot factor stays 2. -/
def cmL3 : LedgerStratumData cmD cmW cmP :=
  { cmL2 with
    inStratum := fun _ x => x ((0 : ℕ), (0 : ℕ)) = 1
    parentCond := fun _ x => x ((0 : ℕ), (0 : ℕ)) = 1
    parentBlock := {((0 : ℕ), (0 : ℕ))}
    cylFiber := fun _ => 1
    cylFiberDigits := fun _ _ => 1 }

theorem cmL3_supportUnion : cmL3.supportUnion = {((0 : ℕ), (0 : ℕ))} := by
  decide

theorem cmL3_semanticsV2 : cmL3.LedgerSemanticsV2 := by
  intro ρ hρ
  have hmem : ((0 : ℕ), (0 : ℕ)) ∈ cmL3.supportUnion := by
    rw [cmL3_supportUnion]; decide
  have hpin : blockCount cmL3.q0 cmL3.supportUnion
      (fun x => x ((0 : ℕ), (0 : ℕ)) = 1) = 1 := by
    rw [blockCount_pin cmL3.q0 _ hmem one_lt_two, cmL3_supportUnion]
    rfl
  refine ⟨hpin.symm, fun z => ?_⟩
  rw [blockCount_congr _ _ (cond' := cmL3.inStratum ρ)
    (fun x => ⟨fun h => h.1, fun h => ⟨h, fun k => absurd k.2 (Finset.notMem_empty _)⟩⟩)]
  exact hpin.symm

/-- `cmL3` satisfies the FULL v2 lawfulness pack — including a SUBSTANTIVE
`pinned_forced` (the shared leaf is genuinely forced to 1 across members). -/
theorem cmL3_lawfulV2 : cmL3.LedgerLawfulV2 where
  semantics := cmL3_semanticsV2
  member_split := fun ρ x =>
    ⟨fun h => ⟨h, fun _ _ => trivial⟩, fun h => h.1⟩
  parent_support := by
    intro ρ x y hxy
    have h := hxy ((0 : ℕ), (0 : ℕ)) (Finset.mem_singleton_self _)
    show (x ((0 : ℕ), (0 : ℕ)) = 1) ↔ (y ((0 : ℕ), (0 : ℕ)) = 1)
    rw [h]
  slot_support := cmL_lawful.slot_support
  slots_disjoint := cmL_lawful.slots_disjoint
  slot_coord_mem := fun k => absurd k.2 (Finset.notMem_empty _)
  parent_interior_disjoint := fun k => absurd k.2 (Finset.notMem_empty _)
  pinned_forced := by
    intro ρ hρ c hc x y hx hy _
    have hc' : c = ((0 : ℕ), (0 : ℕ)) := Finset.mem_singleton.mp hc
    subst hc'
    have hx' : x ((0 : ℕ), (0 : ℕ)) = 1 := hx
    have hy' : y ((0 : ℕ), (0 : ℕ)) = 1 := hy
    rw [hx', hy']
  junction := fun _ _ _ _ hk => absurd hk (Finset.notMem_empty _)
  digit_range := fun _ _ _ _ k => absurd k.2 (Finset.notMem_empty _)
  slot_sem := cmL_lawful.slot_sem
  slotDigits_sem := fun _ _ k => absurd k.2 (Finset.notMem_empty _)
  slot_count_val := cmL_lawful.slot_count_val

/-- **Seam B fires**: the nonempty-stratum overlap witness violates
`DigitsProdLaw` — the joint count 1 (parent pin consumes the shared leaf)
against the product 2 (the slot factor priced by `slot_count_val` alone). -/
theorem cm3_not_digitsProd : ¬ DigitsProdLaw cmW cmP cmL3.ledgerJoint := by
  intro hDP
  have hρ0 : (0 : ℕ) < (cmL3.ledgerJoint).rhoCount cmL3.q0 := by
    simp [LedgerStratumData.ledgerJoint, cmL3, cmL2, cmL]
  have h0 := hDP cmL3.q0 0 hρ0 (fun _ => 0)
    (fun k => absurd k.2 (Finset.notMem_empty _))
  have hbox : cmW.boxSlots \ cmW.onLine = {(0 : Fin 2)} := by decide
  have honl : cmW.onLine.attach = ∅ := rfl
  simp only [LedgerStratumData.ledgerJoint, honl, hbox, Finset.prod_empty,
    one_mul] at h0
  simp only [cmL3, cmL2, cmL] at h0
  exact absurd h0 (by decide)

/-- The stratum of `cmL3` is genuinely nonempty (the refutation is not by
emptiness): its fiber count is positive. -/
theorem cmL3_fiber_pos : ∃ ρ, ρ < cmL3.rho0 ∧ 0 < cmL3.cylFiber ρ :=
  ⟨0, Nat.one_pos, Nat.one_pos⟩

/-! ## Seam A witness: unsatisfiable parent condition (empty stratum, lawful,
positive product) -/

/-- The satisfiability countermodel: the control's data with the member
predicate (= parent condition) FALSE and the counting fields at their true
(zero) finite-box values. Lawful: every member-quantified clause is vacuous,
and no clause asserts member existence. -/
def cmL4 : LedgerStratumData cmD cmW cmP :=
  { cmL with
    inStratum := fun _ _ => False
    parentCond := fun _ _ => False
    cylFiber := fun _ => 0
    cylFiberDigits := fun _ _ => 0 }

theorem cmL4_semanticsV2 : cmL4.LedgerSemanticsV2 := by
  intro ρ hρ
  refine ⟨(blockCount_of_not _ _ (cmL4.inStratum ρ) (fun x h => h)).symm, fun z => ?_⟩
  exact (blockCount_of_not _ _ _ (fun x (h : cmL4.inStratum ρ x ∧ _) => h.1)).symm

theorem cmL4_lawfulV2 : cmL4.LedgerLawfulV2 where
  semantics := cmL4_semanticsV2
  member_split := by
    intro ρ x
    simp only [cmL4, false_iff, not_and]
    intro h
    exact absurd h id
  parent_support := fun _ _ _ _ => Iff.rfl
  slot_support := cmL_lawful.slot_support
  slots_disjoint := cmL_lawful.slots_disjoint
  slot_coord_mem := cmL_lawful.slot_coord_mem
  parent_interior_disjoint := cmL_lawful.parent_interior_disjoint
  pinned_forced := fun _ _ c hc => absurd hc (Finset.notMem_empty c)
  junction := fun _ _ _ hx => absurd hx id
  digit_range := fun _ _ _ hx => absurd hx id
  slot_sem := cmL_lawful.slot_sem
  slotDigits_sem := cmL_lawful.slotDigits_sem
  slot_count_val := cmL_lawful.slot_count_val

/-- **Seam A fires**: the empty-stratum lawful witness violates
`DigitsProdLaw` — LHS 0 against the positive off-line product 2. -/
theorem cm4_not_digitsProd : ¬ DigitsProdLaw cmW cmP cmL4.ledgerJoint := by
  intro hDP
  have hρ0 : (0 : ℕ) < (cmL4.ledgerJoint).rhoCount cmL4.q0 := by
    simp [LedgerStratumData.ledgerJoint, cmL4, cmL]
  have h0 := hDP cmL4.q0 0 hρ0 (fun _ => 0)
    (fun k => absurd k.2 (Finset.notMem_empty _))
  have hbox : cmW.boxSlots \ cmW.onLine = {(0 : Fin 2)} := by decide
  have honl : cmW.onLine.attach = ∅ := rfl
  simp only [LedgerStratumData.ledgerJoint, honl, hbox, Finset.prod_empty,
    one_mul] at h0
  simp only [cmL4, cmL] at h0
  exact absurd h0 (by decide)

/-! ## The round-2 refutation of TD-3's exact ∀-statement -/

/-- **TD-3 ROUND 2 IS FALSE AS STATED**: the ∀-closure of `ledger_digitsProd`
(TD3_digitsProd.lean, round-2 E-phase sorry) is refutable — by the NONEMPTY
overlap witness `cmL3` (Seam B), and independently by the empty-stratum
witness `cmL4` (Seam A). Contrast the positive controls `cm2_digitsProd` /
`td_digitsProd` on the trace subfamily (`parentBlock = ∅`). -/
theorem ledger_digitsProd_v2_refuted :
    ¬ ∀ (D : CensusData) (W : WindowDatum D) (P : ParentShape D W)
        (L : LedgerStratumData D W P), L.LedgerLawfulV2 → LedgerScope W P →
        LedgerClean D W P L.N → DigitsProdLaw W P L.ledgerJoint :=
  fun h => cm3_not_digitsProd (h cmD cmW cmP cmL3 cmL3_lawfulV2 cm_scope cm_clean)

end LeanUrat.B2D

#print axioms LeanUrat.B2D.cmL3_lawfulV2
#print axioms LeanUrat.B2D.cm3_not_digitsProd
#print axioms LeanUrat.B2D.cmL3_fiber_pos
#print axioms LeanUrat.B2D.cmL4_lawfulV2
#print axioms LeanUrat.B2D.cm4_not_digitsProd
#print axioms LeanUrat.B2D.ledger_digitsProd_v2_refuted
