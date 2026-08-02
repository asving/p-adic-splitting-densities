/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.TD3v2_countermodel

/-!
# B2D/TDDefsV3 — the v3 lawfulness pack: v2 + the two D.11 seam clauses
  [B2DEF_LEAN unit E2, STATEMENT ROUND 3; supersedes `LedgerLawfulV2` /
   `LedgerStrataV2` as the consumable pack, per the TD-3 round-2 refutation]

Blueprint: `lean/blueprints/B2DEF_LEAN_2026-08-08.md` §3 + §5 (unit E2, v3
round). moves_ref: §B2-DEF D.3(e)(ii.3)/(ii.4), D.11 (the finite-box product
bijection — BOTH halves). Statement authority: standing statement-change rule
(an honest strengthening of a pack whose insufficiency is compiled on file).

## Provenance: why a round 3 (the round-2 countermodel record)

Round 2 (`TDDefsV2.lean`) repaired the v1 counting SEMANTICS — finite-box
`blockCount`s over `supportUnion`; that repair STANDS (N-TD1 [LHS-V2]
product-match; positive controls `cm2_digitsProd` / `td_digitsProd`). The
wave-2 prover run then REFUTED TD-3's round-2 statement at the PACK level
(`TD3v2_countermodel.ledger_digitsProd_v2_refuted`): `LedgerLawfulV2` supplies
the INJECTIVITY half of MOVES D.11's product bijection (`pinned_forced`) but
neither

* **Seam A (member existence)**: no clause makes the per-realization member
  set satisfiable — `inStratum ≡ False` is v2-lawful (witness `cmL4`:
  LHS 0 ≠ 2 = the positive `slot_count_val` product), nor
* **Seam B (parent/box-slot overlap)**: `parent_interior_disjoint` = (ii.3)
  verbatim fences the parent block off INTERIOR ON-LINE slot blocks only —
  a parent condition may cut inside an OFF-LINE (or junction) slot's block
  (witness `cmL3`: NONEMPTY stratum, substantive `pinned_forced`,
  joint 1 ≠ product 2).

## The v2 → v3 diff (everything else verbatim, by `extends`)

`LedgerLawfulV3` = the FULL v2 pack (`toLedgerLawfulV2`, all thirteen clauses
untouched) + EXACTLY the two clauses the countermodels identified:

* `member_exists` — D.11's EXISTENCE half: each counted realization's
  membership predicate is realized by at least one finite-box digit vector
  `v : ↥supportUnion → Fin q₀`, extended by zero — i.e. the N-TD1 trace's
  `members_on_window(U, q0)` elements, the same carrier `LedgerSemanticsV2`
  counts. Kills Seam A (negative control `cmL4_not_lawfulV3` below).
* `parent_box_disjoint` — FULL parent-block/box-slot disjointness: the
  parent-pinned block is disjoint from EVERY box slot's block, junction and
  off-line slots included. Trace-faithful: in every probed instance the
  junction pin rides the junction's own `slotCond` and the parent pins sit
  off the window blocks entirely (D.3(e)(ii.3)'s block reading). Strictly
  extends `parent_interior_disjoint` on the box-slot range; the erased
  monic-top slot (∉ `boxSlots`, outside `member_split`'s quantifier and
  `supportUnion`) is deliberately NOT constrained. Kills Seam B (negative
  control `cmL3_not_lawfulV3` below).

With both halves on board the D.11 product argument closes: TD-3 is PROVED
on this pack (`TD3_digitsProd.ledger_digitsProd`, round 3 — injectivity =
`pinned_forced` + rank induction along `CoordPrec`; existence = the
`member_exists` witness restricted/glued; factorization = the two support
clauses over the now genuinely disjoint `supportUnion`).

## Non-vacuity and the compiled controls (this file, all proved)

* `td_lawfulV3` — the designated r = 1 instance `tdL` satisfies the v3 pack
  (as the round-2 record predicted: `parentBlock = ∅` closes Seam B, and the
  junction-pinned member `v ≡ 1` closes Seam A). `td_mem_ledgerStrataV3`
  puts it in the v3 designated family.
* `cmL3_not_lawfulV3` / `cmL4_not_lawfulV3` — the NEGATIVE controls: both
  round-2 refutation witnesses FAIL v3, each at exactly the clause built to
  kill it. The refutation record does not port to v3.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.style.show false

namespace LeanUrat.B2D

open LeanUrat.Scaffold LeanUrat.Scaffold.HDischarge.H2 LeanUrat.MovesC LedgerStratumData

variable {D : CensusData}

namespace LedgerStratumData

variable {W : WindowDatum D} {P : ParentShape D W}

/-- **The lawfulness pack, v3** [statement round 3] — the FULL v2 pack
(every clause verbatim, via `extends`) plus EXACTLY the two MOVES D.11
clauses whose absence the round-2 countermodels compiled
(`TD3v2_countermodel.lean`, Seams A/B). What units TD-3/TD-6 consume from
round 3 on; TD-0 discharges it at the designated instance (`td_lawfulV3`). -/
structure LedgerLawfulV3 (L : LedgerStratumData D W P) : Prop
    extends L.LedgerLawfulV2 where
  /-- D.11, EXISTENCE half (Seam A): every counted realization's stratum is
      realized by at least one finite-box digit vector on the support union
      (extension-by-zero — the same carrier the v2 semantics counts; the
      N-TD1 trace's `members_on_window(U, q0)` reading). -/
  member_exists : ∀ ρ, ρ < L.rho0 →
    ∃ v : ↥L.supportUnion → Fin L.q0,
      L.inStratum ρ (fun c => if h : c ∈ L.supportUnion then (v ⟨c, h⟩ : ℕ) else 0)
  /-- D.3(e)(ii.3) at FULL box-slot range (Seam B): the parent-pinned block is
      disjoint from EVERY box slot's block — junction and off-line slots
      included, not only interior on-line ones. -/
  parent_box_disjoint : ∀ k ∈ W.boxSlots, Disjoint L.parentBlock (L.slotBlock k)

end LedgerStratumData

/-- **The designated strata family, v3** (blueprint §3 "fill the row", round
3): the v3-lawful ledger instances' q-generic carriers. Inhabited at census
depth r = 1 by the designated instance (`td_mem_ledgerStrataV3`). -/
def LedgerStrataV3 (D : CensusData) (W : WindowDatum D) (P : ParentShape D W) :
    Set (JointStratum D W P) :=
  {J | ∃ L : LedgerStratumData D W P,
    L.LedgerLawfulV3 ∧ J = L.ledgerJoint}

/-! ## TD-0 at round 3: the designated instance satisfies the v3 pack -/

/-- **The designated r = 1 instance is v3-lawful** — the round-2 record's
prediction compiled: `parentBlock = ∅` gives Seam B for free, and the
constant-1 box vector is a member (its junction read leaf `(0,0)` carries
the pin code 1). -/
theorem td_lawfulV3 : tdL.LedgerLawfulV3 where
  toLedgerLawfulV2 := td_lawfulV2
  member_exists := fun ρ _ =>
    ⟨fun _ => ⟨1, tdL.hq0⟩, by
      show (if h : ((0 : ℕ), (0 : ℕ)) ∈ tdL.supportUnion
        then ((⟨1, tdL.hq0⟩ : Fin tdL.q0) : ℕ) else 0) = 1
      rw [dif_pos (by rw [tdL_supportUnion]; decide)]⟩
  parent_box_disjoint := fun _ _ => Finset.disjoint_empty_left _

/-- The v3 designated family is inhabited by the r = 1 instance. -/
theorem td_mem_ledgerStrataV3 : tdL.ledgerJoint ∈ LedgerStrataV3 tdD tdW tdP :=
  ⟨tdL, td_lawfulV3, rfl⟩

/-! ## The negative controls: both round-2 refutation witnesses FAIL v3 -/

/-- **Negative control, Seam A**: the empty-stratum witness `cmL4`
(`inStratum ≡ False`, v2-lawful) fails the v3 pack at `member_exists` —
the clause built to kill it. -/
theorem cmL4_not_lawfulV3 : ¬ cmL4.LedgerLawfulV3 := by
  intro h
  obtain ⟨v, hv⟩ := h.member_exists 0 Nat.one_pos
  exact hv

/-- **Negative control, Seam B**: the overlap witness `cmL3`
(`parentBlock = {(0,0)} = slotBlock 0`, slot 0 a box slot; v2-lawful with a
NONEMPTY stratum) fails the v3 pack at `parent_box_disjoint` — the clause
built to kill it. -/
theorem cmL3_not_lawfulV3 : ¬ cmL3.LedgerLawfulV3 := fun h =>
  Finset.disjoint_left.mp (h.parent_box_disjoint 0 (by decide))
    (by decide : ((0 : ℕ), (0 : ℕ)) ∈ cmL3.parentBlock)
    (by decide : ((0 : ℕ), (0 : ℕ)) ∈ cmL3.slotBlock 0)

end LeanUrat.B2D

#print axioms LeanUrat.B2D.td_lawfulV3
#print axioms LeanUrat.B2D.td_mem_ledgerStrataV3
#print axioms LeanUrat.B2D.cmL4_not_lawfulV3
#print axioms LeanUrat.B2D.cmL3_not_lawfulV3
