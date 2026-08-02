/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.HuniV4Probe

/-!
# B2D/LeakFaceV4 — the leakFree GENERAL-INSTANCE FACE at the v4 (d-leaf-read)
  carrier  [synthesis pass 5 queue item 8, the F6 small-units dispatch:
  "leakFree general-instance face"; unit note
  `lean/notes/openmath/LEAKFREE_2026-08-08.md`]

## What debt this pays (the spec, located)

H2-U9's statement-gate fold of record (`TransDeep.leakFree` docstring): clause
(L) has NO faithful typed COUNTING shadow at the skeletal (W, P, J) carrier —
the round-1 cross-realization form was source-free (Codex R1-C1), the round-2
per-realization digit-sum form admits mass-preserving digit exclusions (Codex
R2-C1) — so `leakFree` landed as a bare `Prop` field, its typed carrier owed
"with the engine instantiation, keyed to §B2-DEF D.3(e)(ii.3)/(ii.4)". TD-5
paid the LEDGER-carrier half (`LeakFreeCarrier` = the (ii.3)/(ii.4) pair) and
TD-6/TDV4 plugged it ([R2-G1]: the field's VALUE is the typed carrier, never
`True`). What stayed owed (ROOT (FRESH) row residue; PROJECT_STATE frontier;
pass-5 queue item 8) is the GENERAL-INSTANCE FACE: the typed law stated at the
AS-BUILT v4 read landscape and DISCHARGED where the TransDeep chain displays
`leakFree` — the plugged Prop proved true, not merely inspectable.

## What the v4-typed law is (faithfulness lineage — no invented strengthening)

§5's verbatim (L) referent: "at every interior on-line slot k ≠ k_s, the
parent's realized conditions impose NO constraint on the height-β_k digit of
a_k beyond (F)'s floor." At the v4 carrier the height-β_k digit IS the d-leaf
READ CODE `slotRead` (TDDefsV4, the [R1-G2] field-element-to-code bijection),
and the parent's realized conditions read ONLY the parent block
(`parent_support`, a pack clause). So the typed (L) face at the v4 landscape
is GEOMETRY, exactly as at TD-5, one read deeper:

* `LeakFreeCarrierV4` = TD-5's accepted pair ((ii.3) interior disjointness +
  (ii.4) pinned forcing, via the projection) PLUS "every read leaf of every
  interior on-line slot avoids the parent block" — the (ii.3) clause
  instantiated at the d read leaves (`slot_coords_mem` puts the leaves in the
  slot block; (ii.3) makes that block parent-disjoint). No slotDigits/count
  law is stated ANYWHERE here — the R2-C1 fold's counting-shadow bar is
  respected; this is a consequence-of-clauses carrier, the TD-5 species.
* Display face `LeakFreeCarrierV4.read_parentBlind`: rewrites confined to the
  parent block cannot move any interior read code — the literal "no
  constraint on the digit" statement at the d-leaf read.

## Deliverables (all NEW declarations; every existing statement byte-untouched)

1. `LeakFreeCarrierV4` (the typed v4 law) + `read_parentBlind` (its display).
2. `ledger_leakFreeV4`: the supplier — every v4-LAWFUL datum satisfies it.
3. Chain wiring at the sites where `leakFree` is displayed/plugged:
   `transDeep_of_lawful_v4_leakFree_holds` / `transDeep_of_lawful_leakFree_holds`
   (the plugged Prop of the presenting-datum builders is TRUE — upgraded from
   the landed `rfl` inspection gates), `leakFreeCarrierV4_plug` (the typed v4
   law subsumes the plugged value), `transDeep_of_ledger_leakFree_holds` /
   `transDeep_of_ledger_v4_leakFree_holds` (the family suppliers' rows carry a
   TRUE `leakFree` — through the Exists.choose transport that TD-6's
   respelling flag recorded), `ledgerStrataV4_leakFreeV4` (family form).
4. Compiled-instance gates: `tdL_leakFree` / `td2_leakFree` (v1-carrier law at
   the v2/v3-lawful instances — `LeakFreeCarrierV4` is not applicable there:
   no `slotCoords` field), `td2V4_leakFreeV4` (the v4 law at the transported
   huni countermodel), and the fired-row discharges `td_transDeep_leakFree_holds`
   / `td2_transDeep_leakFree_holds` / `td2V4_transDeep_leakFree_holds`.
5. De-vacuity fence `td2V4bad_not_leakFreeV4`: the typed law is NOT
   True-for-all-data — a raw (unlawful) v4 datum whose read leaf sits in the
   parent block refutes it, so the instance gates are contentful.

HONESTY DISPLAY: every compiled instance to date has `parentBlock = ∅` (the
r = 1 / probe scale), so at THESE instances the carrier holds for the trivial
reason; the supplier theorem `ledger_leakFreeV4` is the general-instance
content (it consumes the real pack clauses), and gate 5 shows the law itself
has teeth. A nonempty-parent lawful instance remains future forge material
(the F5 deep-instance campaign), NOT claimed here. -/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.B2D

open LeanUrat.Scaffold LeanUrat.Scaffold.HDischarge.H2 LeanUrat.MovesC
open LedgerStratumData LedgerStratumDataV4

variable {D : CensusData} {W : WindowDatum D} {P : ParentShape D W}

/-! ## 1. The typed (L) law at the v4 carrier -/

/-- **The typed (L) carrier at the v4 (d-leaf-read) landscape** — §5's
verbatim referent one read deeper: TD-5's accepted (ii.3)/(ii.4) pair (via the
v1-datum projection) AND every read leaf of every interior on-line slot avoids
the parent block (the (ii.3) geometry instantiated at the [R1-G2] read leaves;
supplier clauses: `parent_interior_disjoint` + `slot_coords_mem`). NOT a
counting law — the R2-C1 counting-shadow bar is respected. -/
def LeakFreeCarrierV4 (L : LedgerStratumDataV4 D W P) : Prop :=
  LeakFreeCarrier L.toLedgerStratumData ∧
  (∀ k : ↥W.onLine, (k : Fin (W.ℓ + 1)) ≠ W.ks →
    ∀ t < D.d, L.slotCoords k t ∉ L.parentBlock)

/-- **The display face**: under the typed v4 law, rewrites confined to the
parent block cannot move any INTERIOR read code — "the parent's realized
conditions impose NO constraint on the height-β_k digit", literally, at the
d-leaf read (the realized conditions read only the parent block by the pack's
`parent_support`; the digit is `slotRead`). -/
theorem LeakFreeCarrierV4.read_parentBlind {L : LedgerStratumDataV4 D W P}
    (h : LeakFreeCarrierV4 L) (k : ↥W.onLine)
    (hk : (k : Fin (W.ℓ + 1)) ≠ W.ks) {x y : Coord → ℕ}
    (hxy : ∀ c ∉ L.parentBlock, x c = y c) :
    L.slotRead x k = L.slotRead y k :=
  Finset.sum_congr rfl fun t ht => by
    rw [hxy _ (h.2 k hk t (Finset.mem_range.mp ht))]

/-! ## 2. The supplier: lawful v4 data satisfy the typed law -/

/-- **The general-instance supplier**: every v4-LAWFUL ledger datum satisfies
the typed v4 (L) law. First conjunct = TD-5's projection (`ledger_leakFree_v4`);
second = `slot_coords_mem` (leaves in the slot block) pushed through
(ii.3)'s interior disjointness. -/
theorem ledger_leakFreeV4 (L : LedgerStratumDataV4 D W P)
    (hL : L.LedgerLawfulV4) : LeakFreeCarrierV4 L :=
  ⟨ledger_leakFree_v4 L hL,
   fun k hk t ht =>
     Finset.disjoint_right.mp (hL.parent_interior_disjoint k hk)
       (hL.slot_coords_mem k t ht)⟩

/-! ## 3. Chain wiring: the displayed `leakFree` is DISCHARGED, not just plugged -/

/-- **The plugged Prop is TRUE (v4 presenting datum)** — the upgrade of the
landed `rfl` gate `transDeep_of_lawful_v4_leakFree`: at every lawful v4 datum
the row's `leakFree` FIELD (= `LeakFreeCarrier` of the datum, by that gate)
HOLDS. From here on no consumer of the v4 chain needs to treat `leakFree` as
an unpinned assumption at ledger instances. -/
theorem transDeep_of_lawful_v4_leakFree_holds (L : LedgerStratumDataV4 D W P)
    (hL : L.LedgerLawfulV4) (hscope : LedgerScope W P)
    (hclean : LedgerClean D W P L.N) :
    (transDeep_of_lawful_v4 L hL hscope hclean).leakFree :=
  ledger_leakFree_v4 L hL

/-- **The typed v4 law subsumes the plugged value**: `LeakFreeCarrierV4`
implies the row's `leakFree` field at the presenting datum (its first
conjunct IS the plugged Prop, definitionally per the `rfl` gate). -/
theorem leakFreeCarrierV4_plug (L : LedgerStratumDataV4 D W P)
    (hL : L.LedgerLawfulV4) (hscope : LedgerScope W P)
    (hclean : LedgerClean D W P L.N) (h : LeakFreeCarrierV4 L) :
    (transDeep_of_lawful_v4 L hL hscope hclean).leakFree := h.1

/-- **The plugged Prop is TRUE (v3 presenting datum)** — the v3-chain twin
(the carrier reads only the (ii.3)/(ii.4) clauses, present since v2). -/
theorem transDeep_of_lawful_leakFree_holds (L : LedgerStratumData D W P)
    (hL : L.LedgerLawfulV3) (hscope : LedgerScope W P)
    (hclean : LedgerClean D W P L.N) :
    (transDeep_of_lawful L hL hscope hclean).leakFree :=
  ledger_leakFree L hL.toLedgerLawfulV2

/-- `leakFree`-truth transports along the joint-stratum index: the helper for
the family-supplier rows, which are built by `rw`-transport along
`J = L.ledgerJoint` (TD-6's flagged Exists.choose respelling). -/
theorem TransDeep.leakFree_of_heq {J J' : JointStratum D W P} (hJJ : J = J')
    {td : TransDeep W P J} {td' : TransDeep W P J'} (h : td ≍ td')
    (hld : td'.leakFree) : td.leakFree := by
  subst hJJ
  exact (eq_of_heq h) ▸ hld

/-- **The family supplier's row carries a TRUE `leakFree` (v3)**: the
`transDeep_of_ledger` row at any designated-family member has its (L) field
discharged — through the choose-transport. -/
theorem transDeep_of_ledger_leakFree_holds (J : JointStratum D W P)
    (hJ : J ∈ LedgerStrataV3 D W P) (hscope : LedgerScope W P)
    (hclean : LedgerClean D W P J.N) :
    (transDeep_of_ledger J hJ hscope hclean).leakFree := by
  have hJ' : ∃ L : LedgerStratumData D W P,
      L.LedgerLawfulV3 ∧ J = L.ledgerJoint := hJ
  have hclean' : LedgerClean D W P hJ'.choose.N := by
    have h := hJ'.choose_spec.2
    rw [h] at hclean
    exact hclean
  refine TransDeep.leakFree_of_heq hJ'.choose_spec.2 ?_
    (transDeep_of_lawful_leakFree_holds hJ'.choose hJ'.choose_spec.1 hscope hclean')
  unfold transDeep_of_ledger
  simp only [eq_mpr_eq_cast]
  exact cast_heq _ _

/-- **The family supplier's row carries a TRUE `leakFree` (v4, the LIVE
chain)**: the `transDeep_of_ledger_v4` row at any v4-family member has its
(L) field discharged. -/
theorem transDeep_of_ledger_v4_leakFree_holds (J : JointStratum D W P)
    (hJ : J ∈ LedgerStrataV4 D W P) (hscope : LedgerScope W P)
    (hclean : LedgerClean D W P J.N) :
    (transDeep_of_ledger_v4 J hJ hscope hclean).leakFree := by
  have hJ' : ∃ L : LedgerStratumDataV4 D W P,
      L.LedgerLawfulV4 ∧ J = L.toLedgerStratumData.ledgerJoint := hJ
  have hclean' : LedgerClean D W P hJ'.choose.N := by
    have h := hJ'.choose_spec.2
    rw [h] at hclean
    exact hclean
  refine TransDeep.leakFree_of_heq hJ'.choose_spec.2 ?_
    (transDeep_of_lawful_v4_leakFree_holds hJ'.choose hJ'.choose_spec.1 hscope hclean')
  unfold transDeep_of_ledger_v4
  simp only [eq_mpr_eq_cast]
  exact cast_heq _ _

/-- **The family form of the typed law**: every v4-family member presents a
lawful datum satisfying the FULL typed v4 law (not just the plugged pair). -/
theorem ledgerStrataV4_leakFreeV4 (J : JointStratum D W P)
    (hJ : J ∈ LedgerStrataV4 D W P) :
    ∃ L : LedgerStratumDataV4 D W P, L.LedgerLawfulV4 ∧
      J = L.toLedgerStratumData.ledgerJoint ∧ LeakFreeCarrierV4 L := by
  obtain ⟨L, hL, hJL⟩ := hJ
  exact ⟨L, hL, hJL, ledger_leakFreeV4 L hL⟩

/-! ## 4. Compiled-instance gates (tdL / td2 / td2V4) -/

/-- The typed (v1-carrier) law at TD-0's designated r = 1 instance. -/
theorem tdL_leakFree : LeakFreeCarrier tdL :=
  ledger_leakFree tdL td_lawfulV2

/-- The typed (v1-carrier) law at the huni-probe extension instance. -/
theorem td2_leakFree : LeakFreeCarrier td2L :=
  ledger_leakFree td2L td2_lawfulV2

/-- **The typed v4 law at the transported huni countermodel** — the
general-instance face fires at the same instance where huni-v2 was accepted
(`slotUniform_td2V4`). -/
theorem td2V4_leakFreeV4 : LeakFreeCarrierV4 td2V4 :=
  ledger_leakFreeV4 td2V4 td2V4_lawfulV4

/-- The fired v3 row at tdL carries a TRUE `leakFree`. -/
theorem td_transDeep_leakFree_holds : td_transDeep.leakFree :=
  transDeep_of_ledger_leakFree_holds tdL.ledgerJoint td_mem_ledgerStrataV3
    td_scope td_clean

/-- The fired v3 row at td2 carries a TRUE `leakFree`. -/
theorem td2_transDeep_leakFree_holds : td2_transDeep.leakFree :=
  transDeep_of_ledger_leakFree_holds td2L.ledgerJoint td2_mem_ledgerStrataV3
    td2_scope td2_clean

/-- The fired v4 row at td2V4 (the LIVE chain's instance) carries a TRUE
`leakFree`. -/
theorem td2V4_transDeep_leakFree_holds : td2V4_transDeep.leakFree :=
  transDeep_of_ledger_v4_leakFree_holds td2V4.toLedgerStratumData.ledgerJoint
    td2V4_mem_ledgerStrataV4 td2V4_scope td2V4_clean

/-! ## 5. De-vacuity fence: the typed law is refutable -/

/-- A RAW (deliberately unlawful) v4 datum: td2V4 with the parent block moved
onto slot 1's first read leaf. -/
def td2V4bad : LedgerStratumDataV4 tdD td2W td2P :=
  { td2V4 with parentBlock := {((1 : ℕ), (0 : ℕ))} }

/-- **The typed v4 law is NOT True-for-all-data**: at `td2V4bad` the interior
slot's read leaf (1,0) sits IN the parent block, refuting the second
conjunct — so the instance gates above are contentful, and lawfulness is
load-bearing in `ledger_leakFreeV4`. -/
theorem td2V4bad_not_leakFreeV4 : ¬ LeakFreeCarrierV4 td2V4bad := fun h =>
  h.2 td2K1 (by decide) 0 (by rw [tdD_d]; omega) (by decide)

end LeanUrat.B2D

#print axioms LeanUrat.B2D.ledger_leakFreeV4
#print axioms LeanUrat.B2D.LeakFreeCarrierV4.read_parentBlind
#print axioms LeanUrat.B2D.transDeep_of_lawful_v4_leakFree_holds
#print axioms LeanUrat.B2D.transDeep_of_lawful_leakFree_holds
#print axioms LeanUrat.B2D.transDeep_of_ledger_leakFree_holds
#print axioms LeanUrat.B2D.transDeep_of_ledger_v4_leakFree_holds
#print axioms LeanUrat.B2D.ledgerStrataV4_leakFreeV4
#print axioms LeanUrat.B2D.tdL_leakFree
#print axioms LeanUrat.B2D.td2_leakFree
#print axioms LeanUrat.B2D.td2V4_leakFreeV4
#print axioms LeanUrat.B2D.td_transDeep_leakFree_holds
#print axioms LeanUrat.B2D.td2_transDeep_leakFree_holds
#print axioms LeanUrat.B2D.td2V4_transDeep_leakFree_holds
#print axioms LeanUrat.B2D.td2V4bad_not_leakFreeV4
