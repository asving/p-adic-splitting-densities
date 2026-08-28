/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFC0

/-!
# Uniformity.ChapI.IFC5 — the VAUD live-range ladder supply: L0's vartheta owner
amendment, enacted as SUPERSESSION TWINS (IFC0 §1 byte-untouched)

**[LVT, 2026-08-28]** — enactment of the vartheta owner amendment proposed by the VAUD
stop-line audit (`runs/wave-b/verdict_VAUD.md`; blueprint
`docs/in-progress/LADDER_SUPPLY_2026-08-27.md`, "[VAUD] Proposed vartheta owner
amendment — exact IFC0 replacement"; machine certificates `scratch/VAUD_probe.lean`).
The six declarations below promote the probe's fully elaborated shapes to production,
byte-shape, universes matched.

**⚠ TRUST BOUNDARY — every `def`/`structure` here is a NEW statement**, flagged for the
standing review (`docs/REVIEW_QUEUE_2026-08-26.md`, LVT row).  Zero `sorry`, zero new
axiom; AxChk footer expects Lean core only.

## The refutation basis (why the unbounded demand cannot stay the campaign target)

IFC0's `LadderVarthetaSupplier` demands `VarthetaRes` at EVERY `i ≥ 3`, but the guard's
only family information, `GaugeFamilyViewEq`, pins the supplied `(v, ρ, q)` only at
`GaugeLive core.r i` (`1 ≤ i < core.r`, C130vw).  VAUD's certificates
(`scratch/VAUD_probe.lean`, all Lean-core, exit 0):

* `gauge_view_offRange_kernel_replacement` — the guard view is invariant under arbitrary
  dependent `(v, ρ)` and `q` replacement at every off-range index;
* `vartheta_sitewise_negative` — a concrete FALSE sitewise `HVarthetaRes`;
* `s2_three_not_gaugeLive` — at the landed depth-2 S2 socket the FIRST demanded index
  `3` is already off range.

So no proof whose family information is the guard's can reach an off-range site: the
unbounded demand is NOT guard-derivable.  Adding an HVR-shaped guard premise is
FORBIDDEN (recorded ruling — the D.62 trap fence, C130s18 §5).  The honest repair
restricts the target's range to indices live in a realization witnessing the SAME
external socket data — never a free-floating liveness certificate.

## Adjudication: SUPERSESSION, not an in-place IFC0 edit (the GCW-6 pattern)

* (a) An in-place IFC0 edit CANNOT compile alone: IFC0's anti-drift pin
  (`example … := h.ladder`) ties `LadderField` definitionally to
  `CapstoneHypotheses.ladder`, which returns E.24's unbounded `LadderSupply`.  VAUD's
  diff would force rebinding that SIGNED capstone field (leanspec NODE I.10, A-I.3) —
  an owner gate, not this unit's licence.  The probe's own record: "An IFC0-only edit
  that pretends the old capstone field is definitionally unchanged would be false."
* (b) House precedent: IFC3 retired IFC0's `DeepGentowSupplier` as a campaign target
  with IFC0 byte-untouched as the tension record (GCW-6), and both IFC3's header and
  leanspec AMENDMENT A-I.5 record the coordination rule "`IFC0.lean` untouched;
  corrected shapes route through supersession twins".
* (c) `LadderField` has no consumers outside `IFC0.lean` (orchestrator grep,
  2026-08-28), so supersession costs nothing downstream; campaigns re-target
  `LadderFieldLive`.

Therefore IFC0 §1 is BYTE-UNTOUCHED and stays as the tension record — its
`LadderVarthetaSupplier` is RETIRED AS A CAMPAIGN TARGET; the corrected target is THIS
file's `LadderFieldLive` / `LadderVarthetaSupplierLive`.

## What lands

* §1 `CanonicalLadderLiveAt` — the live-index predicate: a realization witnessing the
  SAME external socket data (slot/block/gauge views), with `GaugeLive core.r i`.
* §2 the repaired supplier 4′ (`LadderVarthetaSupplierLive`), the repaired record
  (`LadderSupplyLive` — first three fields byte-identical to E.24; ONLY the vartheta
  field gains the live premise), and the repaired field (`LadderFieldLive`).
* §3 the exact four-way split at the repaired target (`ladderFieldLive_iff_suppliers`,
  `ladderFieldLive_of_suppliers`) — suppliers 1–3 are IFC0's OWN, byte-unchanged.
* §4 supersession-direction pins: the OLD targets imply the NEW
  (`ladderVarthetaSupplierLive_of_unbounded`, `ladderFieldLive_of_ladderField`) —
  machine-visible that the amendment only RESTRICTS the demanded range and smuggles no
  strengthening.  The CONVERSE is exactly what VAUD refuted as guard-derivable, and is
  deliberately absent.

## Honesty scope

This file proves NO vartheta mathematics: every theorem is projection/constructor
bookkeeping.  `CapstoneHypotheses.ladder` STILL returns E.24's unbounded `LadderSupply`;
rebinding it (or moving `LadderSupplyLive` into E.24) is a LATER RECORDED OWNER
AMENDMENT (leanspec: would be a numbered A-I.6) — NOT made here.  LB1's arbitrary-`I`
stop (LS-G0) and MP1's refuted cite route (LS-G1) are untouched by this file: the first
three supplier legs are consumed as IFC0 states them, open exactly as before.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.IFC5

open Uniformity.Density

universe uW uG uKt uL

/-! ## §1 The live-index predicate (VAUD probe byte-shape) -/

/-- **The live-index predicate** (the owner-amendment carrier, `scratch/VAUD_probe.lean`
byte-shape): the socket data `(C, B, N, v, ρ, q)` admit a realization witnessing the
SAME external views demanded by `CanonicalLadderConfig` — slot view, block view, gauge
family view — whose gauge range contains `i` (`GaugeLive core.r i`).  Liveness and the
family views belong to ONE witness, so a junk witness cannot buy liveness the views do
not see (the D-D12 anti-cook guard).  NEW STATEMENT (review). -/
def CanonicalLadderLiveAt.{uG', uKt', uL'}
    {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG') [CommGroup G] (Kt : Type uKt') [Field Kt]
    (L : Type uL') [Field L] [Algebra Kt L]
    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n i : ℕ) : Prop :=
  ∃ (_dom : IsDomain O) (_dvr : IsDiscreteValuationRing O)
    (E : Type) (fE : Field E) (core : Tower.ArisingCore (O := O) Kt L n)
    (A : Tower.ChainRealization (O := O) (π := core.π) (F := core.F)
      (H₀ := core.H₀) (hpin := core.hpin) (fieldE := fE) core.T Kt E L)
    (X : Tower.RealizedInput core A)
    (eK : core.T.fld core.i ≃+* K) (eG : G ≃* Tower.GaugeLattice.{uG'} core.r),
    Tower.SlotViewEq X eK C ∧
    (∃ hC : C = X.stageCarrierTransport eK, Tower.BlockViewEq X eK (hC ▸ B)) ∧
    Tower.GaugeFamilyViewEq X (N.transport eG)
      (fun j => (v j).comp eG.symm.toMonoidHom)
      (fun j => (ρ j).comp (Tower.C130s18.kerComapAlong eG (v j))) q ∧
    Tower.GaugeLive core.r i

/-! ## §2 The repaired supplier, record, and field -/

/-- **L0 supplier 4′ (live ϑ leg)** — the VAUD owner amendment: the vartheta conclusion
is demanded only when the same socket data admit a realization whose gauge range
contains `i`.  Supersedes IFC0's `LadderVarthetaSupplier` (unbounded `∀ i ≥ 3`) as the
campaign target; that form is byte-untouched in IFC0 and retained as the tension
record.  NEW STATEMENT (review). -/
def LadderVarthetaSupplierLive (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] (K : Type) [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
    (L : Type uL) [Field L] [Algebra Kt L]
    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
    CanonicalLadderConfig C B G Kt L N v ρ q n →
    ∀ i ≥ 3, CanonicalLadderLiveAt.{uG, uKt, uL} C B G Kt L N v ρ q n i →
      Ladder.VarthetaRes G Kt L N v ρ q i

/-- The repaired result record.  Its first three fields are byte-identical to E.24's
`LadderSupply`; ONLY the vartheta field receives the live-index premise.
NEW STATEMENT (review). -/
structure LadderSupplyLive {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
    (L : Type uL) [Field L] [Algebra Kt L]
    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n : ℕ) : Prop where
  package : Ladder.HE7APackage.{0, 0, uW} C B
  lb1 : Ladder.LB1Carrier.{0, 0, uW} C B
  mp1 : Ladder.MP1Carrier.{0, 0, uW} C B
  vartheta : ∀ i ≥ 3,
    CanonicalLadderLiveAt.{uG, uKt, uL} C B G Kt L N v ρ q n i →
      Ladder.VarthetaRes G Kt L N v ρ q i

/-- The repaired ladder field: `LadderField` with `LadderSupply` replaced by
`LadderSupplyLive` — the shape VAUD's diff proposes for the capstone `ladder` field.
NOT bound to `CapstoneHypotheses` here (owner gate; see the module fence).
NEW STATEMENT (review). -/
def LadderFieldLive (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] (K : Type) [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
    (L : Type uL) [Field L] [Algebra Kt L]
    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
    CanonicalLadderConfig C B G Kt L N v ρ q n →
      LadderSupplyLive.{uW, uG, uKt, uL} C B G Kt L N v ρ q n

/-! ## §3 The exact four-way split at the repaired target -/

/-- ★ **the L0 exit gate at the repaired target**: the range repair preserves the exact
four-supplier assembly — suppliers 1–3 are IFC0's OWN, byte-unchanged; only the fourth
is the live form.  Forward: record projections.  Backward: the record constructor.
No mathematics is proved; the obligation is repartitioned, byte-exactly. -/
theorem ladderFieldLive_iff_suppliers {n : ℕ} :
    LadderFieldLive.{uW, uG, uKt, uL} n ↔
      IFC0.LadderPackageSupplier.{uW, uG, uKt, uL} n ∧
      IFC0.LadderLB1Supplier.{uW, uG, uKt, uL} n ∧
      IFC0.LadderMP1Supplier.{uW, uG, uKt, uL} n ∧
      LadderVarthetaSupplierLive.{uG, uKt, uL} n := by
  constructor
  · intro h
    exact ⟨fun O _ K _ C B G _ Kt _ L _ _ N v ρ q hcfg =>
             (h O K C B G Kt L N v ρ q hcfg).package,
           fun O _ K _ C B G _ Kt _ L _ _ N v ρ q hcfg =>
             (h O K C B G Kt L N v ρ q hcfg).lb1,
           fun O _ K _ C B G _ Kt _ L _ _ N v ρ q hcfg =>
             (h O K C B G Kt L N v ρ q hcfg).mp1,
           fun O _ K _ C B G _ Kt _ L _ _ N v ρ q hcfg =>
             (h O K C B G Kt L N v ρ q hcfg).vartheta⟩
  · rintro ⟨hp, hl, hm, hv⟩
    exact fun O _ K _ C B G _ Kt _ L _ _ N v ρ q hcfg =>
      ⟨hp O K C B G Kt L N v ρ q hcfg,
       hl O K C B G Kt L N v ρ q hcfg,
       hm O K C B G Kt L N v ρ q hcfg,
       hv O K C B G Kt L N v ρ q hcfg⟩

/-- The assembly direction alone, in consumable form: four supplier proofs give the
repaired ladder field. -/
theorem ladderFieldLive_of_suppliers {n : ℕ}
    (hp : IFC0.LadderPackageSupplier.{uW, uG, uKt, uL} n)
    (hl : IFC0.LadderLB1Supplier.{uW, uG, uKt, uL} n)
    (hm : IFC0.LadderMP1Supplier.{uW, uG, uKt, uL} n)
    (hv : LadderVarthetaSupplierLive.{uG, uKt, uL} n) :
    LadderFieldLive.{uW, uG, uKt, uL} n :=
  ladderFieldLive_iff_suppliers.mpr ⟨hp, hl, hm, hv⟩

/-! ## §4 Supersession-direction pins (nothing strengthened, machine-visible) -/

/-- ★ SUPERSESSION PIN (supplier level): the OLD unbounded supplier implies the NEW
live-restricted one — the amendment only RESTRICTS the demanded range (adds the
liveness premise); it smuggles no strengthening.  The CONVERSE is exactly what VAUD
refuted as guard-derivable, and is deliberately absent. -/
theorem ladderVarthetaSupplierLive_of_unbounded {n : ℕ}
    (h : IFC0.LadderVarthetaSupplier.{uG, uKt, uL} n) :
    LadderVarthetaSupplierLive.{uG, uKt, uL} n :=
  fun O _ K _ C B G _ Kt _ L _ _ N v ρ q hcfg i hi _ =>
    h O K C B G Kt L N v ρ q hcfg i hi

/-- ★ SUPERSESSION PIN (field level): any proof of IFC0's `LadderField` (E.24's
unbounded record) yields `LadderFieldLive` — suppliers 1–3 pass through unchanged and
the vartheta leg forgets its new premise. -/
theorem ladderFieldLive_of_ladderField {n : ℕ}
    (h : IFC0.LadderField.{uW, uG, uKt, uL} n) :
    LadderFieldLive.{uW, uG, uKt, uL} n :=
  fun O _ K _ C B G _ Kt _ L _ _ N v ρ q hcfg =>
    ⟨(h O K C B G Kt L N v ρ q hcfg).package,
     (h O K C B G Kt L N v ρ q hcfg).lb1,
     (h O K C B G Kt L N v ρ q hcfg).mp1,
     fun i hi _ => (h O K C B G Kt L N v ρ q hcfg).vartheta i hi⟩

end Uniformity.Density.IFC5

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only.
Statement carriers + decomposition/supersession bookkeeping; nothing here may add to
the trusted base. -/

#print axioms Uniformity.Density.IFC5.CanonicalLadderLiveAt
#print axioms Uniformity.Density.IFC5.LadderVarthetaSupplierLive
#print axioms Uniformity.Density.IFC5.LadderSupplyLive
#print axioms Uniformity.Density.IFC5.LadderFieldLive
#print axioms Uniformity.Density.IFC5.ladderFieldLive_iff_suppliers
#print axioms Uniformity.Density.IFC5.ladderFieldLive_of_suppliers
#print axioms Uniformity.Density.IFC5.ladderVarthetaSupplierLive_of_unbounded
#print axioms Uniformity.Density.IFC5.ladderFieldLive_of_ladderField
