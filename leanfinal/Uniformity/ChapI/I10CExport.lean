/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I10LadderLegs

/-!
# Uniformity.ChapI.I10CExport — UNIT CEX: the C-to-E interface-export layer
[CEX 2026-08-31]

**Unit CEX** — the arising producer for the capstone `ladder` field's two remaining
supplier legs.  LDR (`I10LadderLegs.lean`, `runs/wave-c/verdict_LDR.md`) reduced the
field to `IFC0.LadderPackageSupplier n ∧ IFC0.LadderLB1Supplier n ∧
LadderVarthetaSupplierLive n` (machine-exact iff), with both `package` and `lb1` sitting
behind ONE missing layer: the C-to-E interface-export relation
(`RealizedRungInterfaceExport`-genre, LB1G's named gap).  This file scopes that layer,
lands its honest content, and CLOSES the package supplier.

## Scope verdict (charge 1) — the two suppliers against E.12's demand

* **`package` = `HE7APackage C B` = `Nonempty (RungInterface C B)` (E.24) —
  TAUTOLOGICALLY DISCHARGEABLE, and discharged (§1).**  E.12's `RungInterface` reads the
  pair `(C, B)` only through the numerical shadow `(C.D, B.μ, B.T)`, and the carriers
  themselves supply `C.hD : 0 < D` and `B.hμ : 1 ≤ μ`; a one-side interface (side
  `(B.T+1, 1)`, one linear residual factor of multiplicity `μ`, all counts `C.D * B.μ`,
  rank carrier `PUnit`) satisfies all five clause families at EVERY pair — see
  `rungInterfaceSynth`.  ⚠ HONESTY DISCLOSURE (standing review): the signed `package`
  field, as typed, therefore carries NO arising content — the old ledger's XL sizing
  (1,500–3,000 lines, `LADDER_SUPPLY_2026-08-27.md`) priced the MEANINGFUL arising
  exporter, not the signed `Nonempty`.  The closure below is the letter of the signed
  statement (sign-off criterion 2026-08-26: the build validates intermediate choices);
  the meaningful target is the export-restricted twin `HE7APackageLive` (§3), named here
  for the same later owner amendment as LB1G's `lb1` twin — NOT enacted into the signed
  surface.
* **`lb1` — the missing `Exported` relation now EXISTS with landed content (§2), and the
  twin's production instantiation is NAMED (§3).**  FINDING: the export relation FACTORS
  THROUGH the pair `(C, B)`.  E.12's interface reads arising data only through fields the
  socket views already pin (`BlockViewEq` pins `B.Φ/F/μ/A/T` to the realized development;
  `SlotViewEq` pins `C.hgt/dig/D`) — so "`I` is exported by the realization" is
  equivalent to "`I` agrees with `B`'s OWN development heights", stateable today against
  E.11's landed `onLadderSide` (the argmin predicate sides/slopes/lengths are derived
  from, per E.11's design note).  The realization witness is needed to DISCHARGE the
  relation at arising pairs (the F1 `BlockFrontier` construction — genuinely new
  mathematics per `BLOCKERS_PLAN_2026-08-26.md`), not to STATE it.
* **The XL-block's content (charge-1 ask): size/effort, NOT a mathematical obstruction.**
  Every ledger occurrence is a campaign-sizing label ("XL: roughly 1,500–3,000 new Lean
  lines, 3–6 focused weeks, plus unfinished F1/F2 prerequisites"); the package leg was
  never refuted — unlike the old lb1/mp1/vartheta forms, each of which carries a
  machine refutation.  Post-CEX the XL item is exactly: discharge `IfaceExportedCore`
  (and its named full-strength extensions) at arising pairs.

## What is PROVED here (charge 2)

* ★ `rungInterfaceSynth` — the generic inhabitant; `ladderPackageSupplier_all` — the
  package supplier at EVERY degree `n`; ★ `ladderFieldLive₃_iff_lb1_vartheta` — the
  capstone `ladder` field's post-CEX boundary: `lb1` supplier + the (deepTwist-subsumed)
  vartheta supplier, and nothing else.
* `SideOnBlock` / `IfaceExportedCore` — the contentful C-to-E export relation's landed
  core: every interface side is a genuine two-abscissa argmin side of `B`'s development
  ladder, and its `len` is that side's abscissa width (§2).  `RealizedRungInterfaceExport`
  — the same relation typed at the realization witness (LB1G's demanded genre), the
  factoring made definitional.
* `HE7APackageLive` + `he7aPackageLive_top_iff` (anti-cook fence, mirror of
  `lb1CarrierLive_top_iff`) + `lb1CarrierExported_of_partitionLegs` — the exported twins'
  shapes and wiring, for the later owner amendment.
* Teeth: `sideOnBlock_two_point` (exported sides satisfy the two-point support equation
  in `B`'s own heights) and `ifaceExportedCore_synth_two_point` (the synthetic inhabitant
  is NOT vacuously exported — the relation constrains it through `B.devHgt`).

## Honest remainder (charge 3) — named, minimal

1. **Discharge of `IfaceExportedCore` at arising pairs** (the F1 frontier construction:
   produce the actual side set of `B.devHgt` with its argmin windows) — the XL research
   item, now scoped to exactly this relation.  It would fire `HE7APackageExported` and
   feed the lb1 twin's `PartitionLeg` route (E.57 funnel).
2. **Full-strength export clauses** — `linFac`/`hiFac` pinned to the sides' residual
   factorizations through `C.dig`, counts pinned, rank carrier pinned to the recentering
   rank (F1/F2 + HE7.96 content).  Deliberately NOT stated here: mis-stating them would
   be worse than naming them; `IfaceExportedCore` is labeled CORE for this reason.
3. **Owner amendments (flagged, NOT enacted):** re-signing `LadderSupplyLive₃.package`
   to `HE7APackageLive`-at-`IfaceExportedCore` and `.lb1` to
   `LB1CarrierLive`-at-`IfaceExportedCore` (LB1G "BLOCKED-BECAUSE" + the §1 disclosure).

## Trust boundary

NEW STATEMENTS (standing review): `SideOnBlock`, `IfaceExportedCore`,
`RealizedRungInterfaceExport`, `HE7APackageLive`, `HE7APackageExported`,
`LadderFieldLive₃`-boundary corollary.  Nothing signed is touched; no leanspec name
changes.  Cite ledger: **empty** — Lean core over the landed corpus; `#print axioms`
footer is the audit.  Zero `sorry`, zero new axiom.  Verdict: `runs/wave-c/verdict_CEX.md`.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.IFC5

open Uniformity.Density
open Uniformity.Density.Tower

/-! ## §1 The package leg: the signed `Nonempty (RungInterface C B)` is tautologically
dischargeable — the generic inhabitant, the supplier closure, and the disclosure

The five clause families of E.12 constrain the interface's numbers against `(C.D, B.μ,
B.T)` ONLY; the carriers' own positivity fields (`C.hD`, `B.hμ`) make the one-side
solution legal at every pair.  ⚠ The inhabitant is SYNTHETIC (not arising-exported) —
that is exactly the §2 relation's reason to exist; the anti-cook tooth
`ifaceExportedCore_synth_two_point` shows §2's relation constrains it non-vacuously. -/

section Synth

universe uO uK uW

variable {O : Type uO} [CommRing O] {K : Type uK} [Field K]

/-- ★ **The generic rung interface**: one side `(B.T + 1, 1)` of length `B.μ`, one linear
residual factor (root `0`, multiplicity `B.μ`), all counts `C.D * B.μ`, rank carrier
`PUnit`.  Legal at EVERY `(C, B)` — the machine pin that E.24's `HE7APackage`, as signed,
demands no arising provenance.  NEW STATEMENT (review). -/
def rungInterfaceSynth (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C) :
    Ladder.RungInterface.{uO, uK, uW} C B where
  sides := {(B.T + 1, 1)}
  hside_cop := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact ⟨Nat.coprime_one_right _, le_rfl⟩
  hside_node := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    omega
  len := fun _ => B.μ
  hlen_pos := fun p _ => B.hμ
  hlen_sum := Finset.sum_singleton _ _
  linFac := fun _ => {((0 : K), B.μ)}
  hiFac := fun _ => 0
  hresdeg := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    simp
  rootCount := fun _ => C.D * B.μ
  haccount := fun p _ => rfl
  classCount := fun _ _ => C.D * B.μ
  classCountHi := fun _ _ => C.D * B.μ
  hnonempty := fun p _ =>
    ⟨fun q _ => Nat.mul_pos C.hD B.hμ, fun q hq => absurd hq (by simp)⟩
  hforce := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact ⟨fun q _ => Nat.mul_le_mul le_rfl B.hμ, fun q hq => absurd hq (by simp)⟩
  hexhaust := by
    intro p hp
    simp
  W := PUnit.{uW + 1}
  wf := emptyWf
  σRank := PUnit.unit

/-- The package at every pair — E.24's conjunct is unconditional.  ⚠ Read the §1
disclosure: this closes the SIGNED shape; the meaningful content lives in §2/§3. -/
theorem he7aPackage_all (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C) :
    Ladder.HE7APackage.{uO, uK, uW} C B :=
  ⟨rungInterfaceSynth C B⟩

/-- Anti-abuse pin: the synthetic interface has exactly ONE side — it can never witness
the `1 < card` half of an LB1 trigger. -/
theorem rungInterfaceSynth_sides_card (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C) :
    (rungInterfaceSynth.{uO, uK, uW} C B).sides.card = 1 :=
  Finset.card_singleton _

end Synth

section SupplierClosure

universe uW uG uKt uL

/-- ★ **The package supplier CLOSES, at every degree** (charge 2's "fire either supplier
if it closes").  The config is not consumed — that IS the §1 disclosure, machine-visible:
the signed leg never constrained the arising data. -/
theorem ladderPackageSupplier_all (n : ℕ) :
    IFC0.LadderPackageSupplier.{uW, uG, uKt, uL} n :=
  fun _ _ _ _ C B _ _ _ _ _ _ _ _ _ _ _ _hcfg => he7aPackage_all C B

/-- ★ **The capstone `ladder` field's post-CEX boundary**: with the package supplier
closed, LDR's three-supplier iff contracts to TWO — the lb1 supplier (behind §2's export
layer + the owner-gated twin) and the live vartheta supplier (subsumed by the deepTwist
campaign, LDR §2).  Machine-exact. -/
theorem ladderFieldLive₃_iff_lb1_vartheta {n : ℕ} :
    LadderFieldLive₃.{uW, uG, uKt, uL} n ↔
      IFC0.LadderLB1Supplier.{uW, uG, uKt, uL} n ∧
      LadderVarthetaSupplierLive.{uG, uKt, uL} n := by
  rw [ladderFieldLive₃_iff_suppliers]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩,
         fun h => ⟨ladderPackageSupplier_all n, h.1, h.2⟩⟩

/-- ★ The capstone `ladder` field's post-CEX assembly (LDR's `ladderFieldLive₃_of_boundary`
with the package leg discharged): the lb1 supplier + the deepTwist campaign's universal
vartheta supplier now give the SIGNED field's exact type. -/
theorem ladderFieldLive₃_of_lb1_universal {n : ℕ}
    (hl : IFC0.LadderLB1Supplier.{uW, uG, uKt, uL} n)
    (hv : DeepExport.UniversalVarthetaSupplier.{uG, uKt, uL} n) :
    LadderFieldLive₃.{uW, uG, uKt, uL} n :=
  ladderFieldLive₃_of_boundary (ladderPackageSupplier_all n) hl hv

end SupplierClosure

/-! ## §2 The C-to-E interface-export relation — LB1G's named gap, TYPED with landed
content

E.11's design note: `onLadderSide` is the argmin predicate "from which sides, slopes and
lengths are derived predicates"; no polygon type exists in chapter E by design.  The
landed CORE below pins each interface side to a genuine two-abscissa argmin side of the
block's OWN development heights, and the side's `len` to that side's extremal abscissa
window.  Necessity is the design bar (every honest arising interface satisfies it);
satisfiability at arising pairs is exactly F1's discharge — remainder R1 — so the
relation is deliberately restrictive and NOT claimed inhabited here.  The full-strength
clauses (`linFac`/`hiFac`/counts through `C.dig`, the rank carrier) are remainder R2:
deliberately named, not mis-stated. -/

section ExportRelation

universe uO uK uW

variable {O : Type uO} [CommRing O] {K : Type uK} [Field K]
variable {C : Ladder.SlotCarrier O K}

/-- `p = (u, ℓ)` is a genuine side of the block's development ladder: at least two
distinct abscissas attain the `(u, ℓ)` support value (E.11's `onLadderSide`).
NEW STATEMENT (review). -/
def SideOnBlock (B : Ladder.BlockData C) (p : ℕ × ℕ) : Prop :=
  ∃ j k : ℕ, j < k ∧ Ladder.onLadderSide B.devHgt p.1 p.2 B.μ j ∧
    Ladder.onLadderSide B.devHgt p.1 p.2 B.μ k

/-- ★ **The C-to-E export relation, landed core**: every side of `I` is a genuine side
of `B`'s development ladder, and `I.len` is that side's extremal argmin window width.
FINDING (module docstring): the relation factors through `(C, B)` because the socket
views pin every field E.12 reads; the realization witness re-enters at DISCHARGE time
(F1), not here.  NEW STATEMENT (review). -/
def IfaceExportedCore (B : Ladder.BlockData C)
    (I : Ladder.RungInterface.{uO, uK, uW} C B) : Prop :=
  ∀ p ∈ I.sides, ∃ j k : ℕ, j < k ∧
    Ladder.onLadderSide B.devHgt p.1 p.2 B.μ j ∧
    Ladder.onLadderSide B.devHgt p.1 p.2 B.μ k ∧
    I.len p = k - j ∧
    ∀ m : ℕ, Ladder.onLadderSide B.devHgt p.1 p.2 B.μ m → j ≤ m ∧ m ≤ k

/-- Core-exported interfaces have all sides on the block. -/
theorem IfaceExportedCore.sides_on {B : Ladder.BlockData C}
    {I : Ladder.RungInterface.{uO, uK, uW} C B} (h : IfaceExportedCore B I) :
    ∀ p ∈ I.sides, SideOnBlock B p := fun p hp =>
  let ⟨j, k, hjk, hj, hk, _, _⟩ := h p hp
  ⟨j, k, hjk, hj, hk⟩

/-- TOOTH: an exported side satisfies the two-point support equation in `B`'s own
development heights — the machine-visible sense in which §2's relation CONSTRAINS
(nothing `⊤`-shaped can prove this). -/
theorem sideOnBlock_two_point {B : Ladder.BlockData C} {p : ℕ × ℕ}
    (h : SideOnBlock B p) :
    ∃ j k : ℕ, j < k ∧ k ≤ B.μ ∧
      p.2 • B.devHgt j + ((j * p.1 : ℕ) : WithTop ℤ)
        = p.2 • B.devHgt k + ((k * p.1 : ℕ) : WithTop ℤ) := by
  obtain ⟨j, k, hjk, hj, hk⟩ := h
  exact ⟨j, k, hjk, hk.1, hj.2.trans hk.2.symm⟩

/-- ANTI-COOK TOOTH: the §1 synthetic inhabitant is NOT vacuously exported — if it were
core-exported, `B`'s own heights would have to realize the slope `B.T + 1` on a genuine
two-abscissa side.  So §2's relation separates the synthetic interface from arising
content exactly as designed. -/
theorem ifaceExportedCore_synth_two_point {B : Ladder.BlockData C}
    (h : IfaceExportedCore.{uO, uK, uW} B (rungInterfaceSynth C B)) :
    ∃ j k : ℕ, j < k ∧ k ≤ B.μ ∧
      B.devHgt j + ((j * (B.T + 1) : ℕ) : WithTop ℤ)
        = B.devHgt k + ((k * (B.T + 1) : ℕ) : WithTop ℤ) := by
  have hp : ((B.T + 1, 1) : ℕ × ℕ) ∈ (rungInterfaceSynth.{uO, uK, uW} C B).sides :=
    Finset.mem_singleton_self _
  obtain ⟨j, k, hjk, hkμ, heq⟩ :=
    sideOnBlock_two_point (h.sides_on _ hp)
  refine ⟨j, k, hjk, hkμ, ?_⟩
  simpa [one_smul] using heq

end ExportRelation

section Realized

universe uE uG uKt uL uW

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E] {L : Type uL} [Field L]
variable [Algebra Kt L]
variable {n : ℕ} {core : ArisingCore (O := O) Kt L n}
variable {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F)
  (H₀ := core.H₀) (hpin := core.hpin) core.T Kt E L}

/-- ★ **`RealizedRungInterfaceExport`** — the missing relation in LB1G's demanded genre,
typed at the realization witness (`RealizedInput` + the digit-field identification `eK`,
exactly the objects `CanonicalLadderConfigData` exports).  Its body is the §2 core at the
view-pinned block: the factoring finding, made definitional. -/
def RealizedRungInterfaceExport (X : RealizedInput core Aℛ)
    {K : Type} [Field K] (eK : core.T.fld core.i ≃+* K)
    (I : Ladder.RungInterface.{0, 0, uW}
      (X.stageCarrierTransport eK) (X.inputBlockTransport eK)) : Prop :=
  IfaceExportedCore (X.inputBlockTransport eK) I

/-- Anti-drift pin: the realized relation IS the E-side core at the transported block,
definitionally — consumers may work entirely E-side. -/
theorem realizedRungInterfaceExport_def (X : RealizedInput core Aℛ)
    {K : Type} [Field K] (eK : core.T.fld core.i ≃+* K)
    (I : Ladder.RungInterface.{0, 0, uW}
      (X.stageCarrierTransport eK) (X.inputBlockTransport eK)) :
    RealizedRungInterfaceExport X eK I ↔
      IfaceExportedCore (X.inputBlockTransport eK) I :=
  Iff.rfl

end Realized

/-! ## §3 The exported twins — the named targets of the later owner amendment
(mirrors of LDR §3; flagged, NOT enacted into the signed surface) -/

section Twins

universe uO uK uW

variable {O : Type uO} [CommRing O] {K : Type uK} [Field K]

/-- The export-restricted package twin (mirror of `LB1CarrierLive`): SOME exported
interface exists.  With a contentful `Exported` this is the MEANINGFUL form of E.24's
package conjunct; the fence below is its anti-cook tooth.  NEW STATEMENT (review). -/
def HE7APackageLive (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (Exported : Ladder.RungInterface.{uO, uK, uW} C B → Prop) : Prop :=
  ∃ I : Ladder.RungInterface.{uO, uK, uW} C B, Exported I

/-- Anti-cook fence (mirror of `lb1CarrierLive_top_iff`): at the trivial export relation
the twin degenerates to exactly the signed package — so the later amendment's honesty
rests entirely on a CONTENTFUL `Exported` (§2's core or stronger). -/
theorem he7aPackageLive_top_iff {C : Ladder.SlotCarrier O K} {B : Ladder.BlockData C} :
    HE7APackageLive.{uO, uK, uW} C B (fun _ => True) ↔
      Ladder.HE7APackage.{uO, uK, uW} C B :=
  ⟨fun ⟨I, _⟩ => ⟨I⟩, fun ⟨I⟩ => ⟨I, trivial⟩⟩

/-- Forgetting direction: any exported package yields the signed package (the twin only
RESTRICTS; it smuggles no strengthening of the signed surface). -/
theorem he7aPackage_of_live {C : Ladder.SlotCarrier O K} {B : Ladder.BlockData C}
    {Exported : Ladder.RungInterface.{uO, uK, uW} C B → Prop}
    (h : HE7APackageLive.{uO, uK, uW} C B Exported) :
    Ladder.HE7APackage.{uO, uK, uW} C B :=
  let ⟨I, _⟩ := h
  ⟨I⟩

/-- **The production package target** (remainder R1's endpoint): the twin at the landed
export core.  Discharging this at arising pairs is the F1 frontier construction — the
scoped XL item.  NEW STATEMENT (review). -/
def HE7APackageExported (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C) : Prop :=
  HE7APackageLive.{uO, uK, uW} C B (IfaceExportedCore B)

/-- **The production lb1 wiring**: E.57 partition legs for core-exported triggering
interfaces assemble LDR's lb1 twin at §2's landed relation — the twin's `Exported`
parameter is no longer a free slot. -/
theorem lb1CarrierExported_of_partitionLegs [IsDomain O]
    {C : Ladder.SlotCarrier O K} {B : Ladder.BlockData C}
    (hpart : ∀ I : Ladder.RungInterface.{uO, uK, uW} C B, IfaceExportedCore B I →
      (1 < I.sides.card ∨ ∃ p ∈ I.sides, ¬ I.SepSide p) →
      Nonempty (Ladder.PartitionLeg I)) :
    LB1CarrierLive.{uO, uK, uW} C B (IfaceExportedCore B) :=
  lb1CarrierLive_of_exported_partitionLegs hpart

end Twins

end Uniformity.Density.IFC5

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only. -/

#print axioms Uniformity.Density.IFC5.rungInterfaceSynth
#print axioms Uniformity.Density.IFC5.he7aPackage_all
#print axioms Uniformity.Density.IFC5.rungInterfaceSynth_sides_card
#print axioms Uniformity.Density.IFC5.ladderPackageSupplier_all
#print axioms Uniformity.Density.IFC5.ladderFieldLive₃_iff_lb1_vartheta
#print axioms Uniformity.Density.IFC5.ladderFieldLive₃_of_lb1_universal
#print axioms Uniformity.Density.IFC5.SideOnBlock
#print axioms Uniformity.Density.IFC5.IfaceExportedCore
#print axioms Uniformity.Density.IFC5.IfaceExportedCore.sides_on
#print axioms Uniformity.Density.IFC5.sideOnBlock_two_point
#print axioms Uniformity.Density.IFC5.ifaceExportedCore_synth_two_point
#print axioms Uniformity.Density.IFC5.RealizedRungInterfaceExport
#print axioms Uniformity.Density.IFC5.realizedRungInterfaceExport_def
#print axioms Uniformity.Density.IFC5.HE7APackageLive
#print axioms Uniformity.Density.IFC5.he7aPackageLive_top_iff
#print axioms Uniformity.Density.IFC5.he7aPackage_of_live
#print axioms Uniformity.Density.IFC5.HE7APackageExported
#print axioms Uniformity.Density.IFC5.lb1CarrierExported_of_partitionLegs
