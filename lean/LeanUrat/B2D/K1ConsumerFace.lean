/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.LeakFaceV4

/-!
# B2D/K1ConsumerFace — the Step-10/K1 classifier CONSUMER face of `leakFree`
  [synthesis pass 6 queue item 5, F3(a); the twin owed since H2-U10
  (`LEAKFREE_2026-08-08.md` honesty display: "the Step-10/K1 classifier face
  (the other U10 twin, the leakFree CONSUMER) remains owed");
  unit note `lean/notes/openmath/K1FACE_2026-08-08.md`]

## The face, stated precisely (what Step-10/K1 DEMANDS of leakFree-type data)

Consumption map of record (HDISCHARGE_H2 §1/§2.2): Step 10 (CU-1's step) is
where the classifier census produces its CU LEAF LABELS; those labels inherit
(FRESH), and clause (R) consumes them through Step 18's K1 ("CU leaf labels" —
the label-keyed regrouping of the density sum). What BOTH steps demand of the
(L)/`leakFree` clause is one thing:

  **the CU leaf label read at every interior on-line slot k ≠ k_s must be a
  WELL-DEFINED STRATUM FUNCTIONAL — a function of the off-parent window
  coordinates only, never of the parent realization.**

Without it, Step 10's label assignment is realization-relative and Step 18's
regrouping by label is ill-defined on ρ-fibers (O-9's harness test K2,
"parent-realization independence", is exactly this face's numeric shadow —
8,220,994 boxes, 0 violations, support not proof).

At the as-built v4 (d-leaf-read) ledger carrier the leaf label IS the read
code `slotRead` (the [R1-G2] field-element-to-code bijection) and the parent
realization enters ONLY through the parent block (`parent_support`), so the
demand is the ∃-label FACTORIZATION:

* `K1ConsumerFace L` := at every interior on-line slot there EXISTS a label
  function on the off-parent coordinates through which `slotRead` factors.
  The junction slot k_s is EXCLUDED by design: its read is the ρ-determined
  pin ((J)/`junction`), charged to the parent — clause (c)'s referent, not
  (L)'s.

`k1ConsumerFace_iff_parentBlind` pins the demand's exact strength: the face
is EQUIVALENT to parent-blind descent of the interior reads — Step-10/K1
demands NOTHING beyond the (L) content (no counting law is stated or implied;
the R2-C1 counting-shadow bar is respected on the CONSUMER side too).

## The supply (the F3(a) reach, executed)

`LeakFreeCarrierV4`'s display face `read_parentBlind` is exactly the descent,
so the consumer face is SUPPLIED by the typed carrier:

1. `k1ConsumerFace_of_leakFreeV4` — the typed (L) carrier supplies the face.
2. `k1ConsumerFace_of_lawful_v4` — every v4-LAWFUL datum supplies it
   (through `ledger_leakFreeV4`).
3. `ledgerStrataV4_k1ConsumerFace` — family form over `LedgerStrataV4`.
4. **FIRED**: `td2V4_k1ConsumerFace` — the consumer face holds at the
   compiled `td2V4` instance (the transported huni countermodel, the LIVE
   chain's instance).
5. De-vacuity fence (MANDATORY per the charter):
   `td2V4bad_not_k1ConsumerFace` — at the raw datum whose parent block sits
   on a read leaf the face is REFUTED (no label function can exist), so the
   fired gate is contentful and lawfulness is load-bearing.

## Honesty fences (what is NOT claimed)

* At `td2V4` the parent block is EMPTY, so the face holds there for the
  trivial reason; the general content is the supplier theorems + the fence.
  A nonempty-parent lawful instance stays future forge material (the pass-6
  DECLINED row's disposition: revisit only if THIS face demands it — it does
  NOT: the face is statable and fireable at ∅-parent instances, exactly as
  the charter priced).
* This is the STEP-10-SIDE statement at the ledger carrier. The Step-18 K1
  EXACT FORM at the K-CUT/pool carrier (`H8/KCutK1Tie.lean`: `KCutK1Tie`,
  `kcut_k1_form` over `UCarriers`/`blockSolve`) is a DIFFERENT vocabulary
  whose instantiation is owned by [2r]/CL-8 REL.2 + (K-CUT-g); no tie between
  the two carriers is claimed here.
* The DictIII (H2) row (`DictIII.FRESH`) is byte-untouched: per the H2-U10
  closure its classifier-face content is carried by the guarded
  `childDetermined` at `cu1_stepPair_ge2`, and chain-keyed (L) twins over raw
  `EHist` rejoin the refuted F-2/F-4 class — this face lives at the LEDGER
  carrier, where the typed (L) content is.
* Nothing here discharges the H2 `TransDeep.leakFree : Prop` FIELD (bare by
  the E-phase device; its VALUE at ledger instances is discharged in
  `LeakFaceV4.lean`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.B2D

open LeanUrat.Scaffold LeanUrat.Scaffold.HDischarge.H2 LeanUrat.MovesC
open LedgerStratumData LedgerStratumDataV4

variable {D : CensusData} {W : WindowDatum D} {P : ParentShape D W}

/-! ## 1. The consumer face (the Step-10/K1 demand, typed) -/

/-- **The Step-10/K1 classifier consumer face**: at every INTERIOR on-line
slot the CU leaf label (= the d-leaf read code `slotRead`) FACTORS through
the off-parent coordinates — there is a label function of the non-parent
window data alone that computes the read. This is what Step 10's leaf-label
assignment and Step 18's K1 label-keyed regrouping jointly demand of
leakFree-type data: labels must be stratum invariants, not realization
invariants. The junction slot `k_s` is excluded by design (its read is the
ρ-determined pin — clause (c)'s parent charge, not (L)'s scope). -/
def K1ConsumerFace (L : LedgerStratumDataV4 D W P) : Prop :=
  ∀ k : ↥W.onLine, (k : Fin (W.ℓ + 1)) ≠ W.ks →
    ∃ lab : ({c : Coord // c ∉ L.parentBlock} → ℕ) → ℕ,
      ∀ x : Coord → ℕ, L.slotRead x k = lab (fun c => x c.1)

/-- **Exact-strength pin**: the consumer face is EQUIVALENT to parent-blind
descent of the interior reads — Step-10/K1 demands exactly the (L) content
and nothing more (no counting law; the R2-C1 bar respected consumer-side). -/
theorem k1ConsumerFace_iff_parentBlind (L : LedgerStratumDataV4 D W P) :
    K1ConsumerFace L ↔
      (∀ k : ↥W.onLine, (k : Fin (W.ℓ + 1)) ≠ W.ks →
        ∀ x y : Coord → ℕ, (∀ c ∉ L.parentBlock, x c = y c) →
          L.slotRead x k = L.slotRead y k) := by
  constructor
  · intro h k hk x y hxy
    obtain ⟨lab, hlab⟩ := h k hk
    rw [hlab x, hlab y]
    congr 1
    funext c
    exact hxy c.1 c.2
  · intro h k hk
    refine ⟨fun v => L.slotRead
      (fun c => if hc : c ∈ L.parentBlock then 0 else v ⟨c, hc⟩) k, fun x => ?_⟩
    exact h k hk _ _ fun c hc => by rw [dif_neg hc]

/-- **The K1 regrouping display**: under the face, membership in a LABEL
FIBER (the set of boxes whose interior read is a given code z — the cells
Step 18's K1 regroups by) is invariant under parent-block rewrites: the
regrouping is well-defined across parent realizations. -/
theorem K1ConsumerFace.labelFiber_parentBlind {L : LedgerStratumDataV4 D W P}
    (h : K1ConsumerFace L) (k : ↥W.onLine)
    (hk : (k : Fin (W.ℓ + 1)) ≠ W.ks) (z : ℕ) {x y : Coord → ℕ}
    (hxy : ∀ c ∉ L.parentBlock, x c = y c) :
    L.slotRead x k = z ↔ L.slotRead y k = z := by
  rw [(k1ConsumerFace_iff_parentBlind L).mp h k hk x y hxy]

/-! ## 2. The supply from the typed (L) carrier -/

/-- **The typed carrier SUPPLIES the consumer face**: `LeakFreeCarrierV4`'s
display face (`read_parentBlind`, parent-blind descent) is exactly the
demand's equivalent form. -/
theorem k1ConsumerFace_of_leakFreeV4 {L : LedgerStratumDataV4 D W P}
    (h : LeakFreeCarrierV4 L) : K1ConsumerFace L :=
  (k1ConsumerFace_iff_parentBlind L).mpr
    (fun k hk _ _ hxy => h.read_parentBlind k hk hxy)

/-- Every v4-LAWFUL ledger datum supplies the Step-10/K1 consumer face
(through the general supplier `ledger_leakFreeV4`). -/
theorem k1ConsumerFace_of_lawful_v4 (L : LedgerStratumDataV4 D W P)
    (hL : L.LedgerLawfulV4) : K1ConsumerFace L :=
  k1ConsumerFace_of_leakFreeV4 (ledger_leakFreeV4 L hL)

/-- Family form: every v4-family member presents a lawful datum carrying the
consumer face. -/
theorem ledgerStrataV4_k1ConsumerFace (J : JointStratum D W P)
    (hJ : J ∈ LedgerStrataV4 D W P) :
    ∃ L : LedgerStratumDataV4 D W P, L.LedgerLawfulV4 ∧
      J = L.toLedgerStratumData.ledgerJoint ∧ K1ConsumerFace L := by
  obtain ⟨L, hL, hJL⟩ := hJ
  exact ⟨L, hL, hJL, k1ConsumerFace_of_lawful_v4 L hL⟩

/-! ## 3. FIRED at the compiled instance -/

/-- **THE CONSUMER FIRES AT td2V4** (the charter's mandatory gate): the
Step-10/K1 consumer face holds at the transported huni countermodel — the
same compiled instance where huni-v2 (`slotUniform_td2V4`), the (FRESH)
delivery (`td2V4_freshClauses`) and the typed (L) law (`td2V4_leakFreeV4`)
already fire. HONESTY: td2V4's parent block is ∅, so the face holds here for
the trivial reason; the content is §2's suppliers + §4's fence. -/
theorem td2V4_k1ConsumerFace : K1ConsumerFace td2V4 :=
  k1ConsumerFace_of_lawful_v4 td2V4 td2V4_lawfulV4

/-! ## 4. De-vacuity fence (mandatory) -/

/-- The bad datum's interior read agrees with td2V4's (the parent-block move
touches no read field). -/
theorem td2V4bad_slotRead_eq (x : Coord → ℕ) (k : ↥td2W.onLine) :
    td2V4bad.slotRead x k = td2V4.slotRead x k := rfl

/-- **The consumer face is REFUTABLE**: at `td2V4bad` (the raw v4 datum with
the parent block moved onto slot 1's read leaf (1,0)) NO label function can
exist — the all-zero box and the (1,0)-indicator box restrict identically
off the parent block yet read 0 ≠ 1. So `td2V4_k1ConsumerFace` is a
contentful gate and lawfulness is load-bearing in the supply chain. -/
theorem td2V4bad_not_k1ConsumerFace : ¬ K1ConsumerFace td2V4bad := by
  intro h
  obtain ⟨lab, hlab⟩ := h td2K1 (by decide)
  have hx := hlab (fun _ => 0)
  have hy := hlab (fun c => if c = ((1 : ℕ), (0 : ℕ)) then 1 else 0)
  have hres : (fun c : {c : Coord // c ∉ td2V4bad.parentBlock} =>
        (fun _ : Coord => (0 : ℕ)) c.1)
      = (fun c : {c : Coord // c ∉ td2V4bad.parentBlock} =>
        (fun c' : Coord => if c' = ((1 : ℕ), (0 : ℕ)) then (1 : ℕ) else 0) c.1) := by
    funext c
    have hc : c.1 ≠ ((1 : ℕ), (0 : ℕ)) := by
      intro hceq
      exact c.2 (by rw [hceq]; decide)
    simp only [if_neg hc]
  have hread : td2V4bad.slotRead (fun _ => 0) td2K1
      = td2V4bad.slotRead (fun c => if c = ((1 : ℕ), (0 : ℕ)) then 1 else 0) td2K1 := by
    rw [hx, hy, hres]
  rw [td2V4bad_slotRead_eq, td2V4bad_slotRead_eq,
    td2V4_slotRead_K1, td2V4_slotRead_K1] at hread
  simp at hread

end LeanUrat.B2D

#print axioms LeanUrat.B2D.k1ConsumerFace_iff_parentBlind
#print axioms LeanUrat.B2D.k1ConsumerFace_of_leakFreeV4
#print axioms LeanUrat.B2D.k1ConsumerFace_of_lawful_v4
#print axioms LeanUrat.B2D.ledgerStrataV4_k1ConsumerFace
#print axioms LeanUrat.B2D.td2V4_k1ConsumerFace
#print axioms LeanUrat.B2D.td2V4bad_not_k1ConsumerFace
