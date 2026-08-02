/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.TDDefsV2

/-!
# B2D/TD3v2_control — the v2 COUNTERMODEL CHECK (positive control, compiled)
  [B2DEF_LEAN unit E2 round 2 — the mandatory mechanism-inapplicability record]

Blueprint §5 E2 (v2 round). moves_ref: §B2-DEF D.11 (`#{f mod p^N}` finite-box
count). deps: TDDefsV2, TD3_countermodel.

## What this file certifies (all PROVED, no sorry)

The TD-0/TD-3 refutation (`TD3_countermodel.lean`, commit 5371139) ran on ONE
mechanism: v1's `LedgerSemantics` counted members over ALL of `Coord → ℕ`
(infinite chart, unbounded values), so box-supported membership forced
`Nat.card ≡ 0` (`card_zero_of_finite_support`) against the positive
`slot_count_val` product — EVERY v1-lawful instance with `1 ≤ rho0` violated
`DigitsProdLaw` (`not_digitsProd_of_lawful`), and de-vacuity was IMPOSSIBLE
(`lawful_fiber_devacuify_impossible`). This file compiles the check that the
mechanism does NOT apply to the v2 finite-box semantics:

* **The positive control `cmL2`** — the SAME census/window/parent/geometry as
  the countermodel's lawful witness `cmL` (= N-TD1 trace instance i1), with
  the counting fields set to the v2 finite-box values: `supportUnion = {(0,0)}`
  (ONE constrained coordinate; the erased monic-top slot contributes nothing),
  so `cylFiber = cylFiberDigits = Nat.card {v : ↥{(0,0)} → Fin 2 // True}
  = 2¹ = 2` — the `Nat.card` now COMPUTES, and it EQUALS the product side
  (trace i1's `[LHS-M] = [RHS] = 2`).
* `cmL2_lawfulV2` — `cmL2` satisfies the FULL v2 lawfulness pack (the
  non-semantics clauses are literally `cmL_lawful`'s, unchanged fields).
* `cm2_digitsProd` — **`DigitsProdLaw` HOLDS, proved, at `cmL2.ledgerJoint`**:
  the very instance shape that refuted v1 (`cm_not_digitsProd`: 0 ≠ 2)
  satisfies v2 (2 = 2).
* `v2_mechanism_inapplicable` — the ¬∀ of the v1 refutation mechanism's EXACT
  v2 transposition: it is NOT the case that every v2-lawful instance with
  `1 ≤ rho0` violates `DigitsProdLaw`. (Contrast `not_digitsProd_of_lawful`.)
* `v2_devacuify_possible` — TD-0's de-vacuity duty (c) (positive fiber count
  at a lawful instance) is POSSIBLE at v2. (Contrast
  `lawful_fiber_devacuify_impossible`.)
* `cmL_not_lawfulV2` — the countermodel's own witness data `cmL` (with its
  zero counting fields) is NOT v2-lawful: v2 semantics forces the positive
  count 2. The v1 refutation record does not port.

NOTE (scope honesty): this is a CONTROL, not TD-3. `cm2_digitsProd` is one
compiled instance of the law (onLine = ∅, so its digit factor is the empty
product); the general TD-3 v2 theorem stands as an E-phase sorry in
`TD3_digitsProd.lean`, and TD-0 still owes the designated r ≥ 1 instance.
The N-TD1 trace extension ([LHS-V2] column, 3/3 MATCH incl. the on-line
digit-content instances i2/i3) is the numeric gate for the general statement.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.B2D

open LeanUrat.Scaffold LeanUrat.Scaffold.HDischarge.H2 LeanUrat.MovesC LedgerStratumData

/-- **The v2 positive control**: the countermodel witness `cmL`'s
census/window/parent/geometry (N-TD1 trace instance i1) with the counting
fields at their v2 FINITE-BOX values (`cylFiber = cylFiberDigits = 2`,
computed below). All non-counting fields are `cmL`'s, byte-for-byte. -/
def cmL2 : LedgerStratumData cmD cmW cmP :=
  { cmL with
    cylFiber := fun _ => 2
    cylFiberDigits := fun _ _ => 2 }

/-- The v2 counting box of the control: exactly the one constrained
coordinate. (The countermodel's all-slots `blockUnion cmL` would ALSO contain
the erased monic-top slot's block coordinate `(1,0)` — `supportUnion`'s
box-slots-only union is what keeps the count free of spurious factors.) -/
theorem cmL2_supportUnion : cmL2.supportUnion = {((0 : ℕ), (0 : ℕ))} := by
  decide

/-- The v2 semantics at the control, COMPUTED: both counting fields equal
`blockCount 2 {(0,0)} (fun _ => True) = 2^1 = 2`. -/
theorem cmL2_semanticsV2 : cmL2.LedgerSemanticsV2 := by
  intro ρ hρ
  have htrue : ∀ x : Coord → ℕ, cmL2.inStratum ρ x := fun _ => trivial
  have hbc : blockCount cmL2.q0 cmL2.supportUnion (cmL2.inStratum ρ) = 2 := by
    rw [blockCount_of_forall _ _ _ htrue, cmL2_supportUnion]
    rfl
  refine ⟨hbc.symm, fun z => ?_⟩
  rw [blockCount_congr _ _ (cond' := cmL2.inStratum ρ)
    (fun x => ⟨fun h => h.1, fun h => ⟨h, fun k => absurd k.2 (Finset.notMem_empty _)⟩⟩)]
  exact hbc.symm

/-- The control satisfies the FULL v2 lawfulness pack. Every non-semantics
clause is `cmL_lawful`'s own proof (the fields it speaks about are unchanged
by the counting-field update). -/
theorem cmL2_lawfulV2 : cmL2.LedgerLawfulV2 where
  semantics := cmL2_semanticsV2
  member_split := cmL_lawful.member_split
  parent_support := cmL_lawful.parent_support
  slot_support := cmL_lawful.slot_support
  slots_disjoint := cmL_lawful.slots_disjoint
  slot_coord_mem := cmL_lawful.slot_coord_mem
  parent_interior_disjoint := cmL_lawful.parent_interior_disjoint
  pinned_forced := cmL_lawful.pinned_forced
  junction := cmL_lawful.junction
  digit_range := cmL_lawful.digit_range
  slot_sem := cmL_lawful.slot_sem
  slotDigits_sem := cmL_lawful.slotDigits_sem
  slot_count_val := cmL_lawful.slot_count_val

/-- **THE POSITIVE CONTROL**: `DigitsProdLaw` HOLDS at the v2 control's
q-generic carrier — the finite-box `Nat.card` (= 2, computed in
`cmL2_semanticsV2`) equals the per-slot product (= 2, the off-line
`slot_count_val` factor; the on-line digit product is empty here). The SAME
instance shape refuted the v1 statement (`cm_not_digitsProd`: 0 ≠ 2). -/
theorem cm2_digitsProd : DigitsProdLaw cmW cmP cmL2.ledgerJoint := by
  intro q ρ hρ z hz
  by_cases hq : q = cmL2.q0
  · subst hq
    have hbox : cmW.boxSlots \ cmW.onLine = {(0 : Fin 2)} := by decide
    have honl : cmW.onLine.attach = ∅ := rfl
    simp only [LedgerStratumData.ledgerJoint, honl, hbox,
      Finset.prod_empty, one_mul]
    rfl
  · rw [ledger_rhoCount_off_support cmL2 q hq] at hρ
    omega

/-- **THE COUNTERMODEL MECHANISM DOES NOT APPLY TO v2**: the exact v2
transposition of `not_digitsProd_of_lawful`'s ∀-closure is FALSE. The v1
refutation was total (every lawful instance with a realization violated the
law); at v2 the control witnesses a lawful instance SATISFYING it. -/
theorem v2_mechanism_inapplicable :
    ¬ ∀ (D : CensusData) (W : WindowDatum D) (P : ParentShape D W)
        (L : LedgerStratumData D W P), L.LedgerLawfulV2 → 0 < L.rho0 →
        ¬ DigitsProdLaw W P L.ledgerJoint :=
  fun h => h cmD cmW cmP cmL2 cmL2_lawfulV2 Nat.one_pos cm2_digitsProd

/-- **TD-0's de-vacuity duty (c) is POSSIBLE at v2** — a lawful instance in
scope/clean regime with a POSITIVE fiber count (contrast v1's
`lawful_fiber_devacuify_impossible`, which proved this ∃ empty). -/
theorem v2_devacuify_possible :
    ∃ (D : CensusData) (W : WindowDatum D) (P : ParentShape D W)
      (L : LedgerStratumData D W P), L.LedgerLawfulV2 ∧ LedgerScope W P ∧
      LedgerClean D W P L.N ∧ ∃ ρ, ρ < L.rho0 ∧ 0 < L.cylFiber ρ :=
  ⟨cmD, cmW, cmP, cmL2, cmL2_lawfulV2, cm_scope, cm_clean,
    0, Nat.one_pos, by norm_num [cmL2]⟩

/-- The refutation record does not port: the countermodel's own witness data
`cmL` (counting fields ≡ 0) is NOT v2-lawful — the v2 semantics forces the
positive finite-box count. The v1/v2 statements genuinely diverge at the
witness. -/
theorem cmL_not_lawfulV2 : ¬ cmL.LedgerLawfulV2 := by
  intro h
  have h0 := (h.semantics 0 Nat.one_pos).1
  have htrue : ∀ x : Coord → ℕ, cmL.inStratum 0 x := fun _ => trivial
  have hbc : blockCount cmL.q0 cmL.supportUnion (cmL.inStratum 0) = 2 := by
    have hU : cmL.supportUnion = {((0 : ℕ), (0 : ℕ))} := by decide
    rw [blockCount_of_forall _ _ _ htrue, hU]
    rfl
  rw [hbc] at h0
  exact absurd h0 (by norm_num [cmL])

end LeanUrat.B2D

#print axioms LeanUrat.B2D.cmL2_lawfulV2
#print axioms LeanUrat.B2D.cm2_digitsProd
#print axioms LeanUrat.B2D.v2_mechanism_inapplicable
#print axioms LeanUrat.B2D.v2_devacuify_possible
#print axioms LeanUrat.B2D.cmL_not_lawfulV2
