/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFC5
import Uniformity.ChapI.I10TauSupply
import Uniformity.ChapE.E57p

/-!
# Uniformity.ChapI.I10LadderLegs — UNIT LDR: the capstone `ladder` field's remaining
legs, scoped and advanced post-blitz [LDR 2026-08-31]

**Unit LDR** — the `ladder` member of the capstone frontier `{ladder, deepTwist, a0}`
(ID12's `capstoneHypotheses_of_frontier`).  The field (`I10_I15_I18.lean` NODE I.10, as
amended through A-I.8) maps every canonical ladder configuration to the A-I.8 record
`IFC5.LadderSupplyLive₃`, whose four legs are `package` (HE7A) / `lb1` / `mp1` /
`vartheta`.  This file settles the field's EXACT post-A-I.8 supplier boundary and
advances the vartheta leg to the deep-witness campaign's own boundary.

## The scope verdict (charge 1) — per record leg, against today's corpus

* **`mp1` — CLOSED generically** (`mp1CarrierLiveDirect_of_steps`, A-I.8).  §1 below
  makes the closure boundary-visible: the field's exact split has THREE suppliers, not
  four — `mp1` is eliminated from the boundary.
* **`vartheta` — SUBSUMED by the deepTwist campaign's universal vartheta supplier**
  (§2, the unit's proof content).  The live guard `CanonicalLadderLiveAt` hands the
  consumer an arbitrary arising realization together with the I.10b gauge view and
  `GaugeLive core.r i`; that is exactly the input of G10U's per-witness transport
  (`varthetaRes_of_perWitness_view`), so `UniversalVarthetaSupplier n` — the deepTwist
  field's own vartheta half (G10U §5) — discharges the ladder leg too.  Through USUP +
  TWD the leg therefore rests on `UniversalKernelSpan` (row C3; closed pointwise at
  every canonical-normalizer realization) + `UniversalGeneratorDescent` (row R5,
  OPEN-LETTERS).  ⚠ It does NOT fire unconditionally from TWD's canonical-normalizer
  machinery: the guard's realization is RECEIVED (existentially quantified over the
  abstract `ChainRealization.normalizer` field), not chosen, and TWD proved
  `KernelSpanAt` falsifiable across that field (the index-2 twist) — TWD's `rfl`
  closure applies to landed witnesses, which are all canonical, not to received ones.
* **`lb1` — RESTRICT-ANYWAY named, supersession OWNER-GATED** (§3).  LB1G (2026-08-28)
  adjudicated: the unrestricted `LB1Carrier` is false on legal abstract E-data (the
  μ = 2 certificate `OM4ResignCert.lb1_resigned_not_trivial`) and vacuously true at the
  landed S2 pair (exported block has μ = 1, no legal trigger); the honest target is the
  export-restricted twin.  §3 promotes the twin's SHAPE (`LB1CarrierLive`, explicit
  `Exported` parameter) byte-identically from `scratch/LB1G_probe.lean` with its
  supersession pin and the E.57 funnel wrapper, plus the `Exported := ⊤` fence showing
  the twin degenerates to the unrestricted carrier — the anti-cook tooth.  The GAP is
  unchanged and named: NO C-to-E interface-export relation
  (`RealizedRungInterfaceExport`-genre) is landed, and retyping the signed record field
  is an owner amendment (LB1G "BLOCKED-BECAUSE") — flagged, NOT enacted.
* **`package` (HE7A) — OPEN, research-genre; same missing layer as `lb1`.**
  `HE7APackage C B = Nonempty (RungInterface C B)` (E.24), and NO landed declaration
  produces a `RungInterface` from arising data — the only inhabitants are the synthetic
  E57i/E57ih interfaces (not arising-exported).  Both `package` and `lb1` therefore sit
  behind the SAME missing C-to-E interface-export layer; no partial generic construction
  is honest without it (the LB1G consumer table).  Nothing is enacted here.

## The post-unit boundary (charge 3)

`ladder` field at degree `n` ⟸ (§1 iff, machine-exact)
`IFC0.LadderPackageSupplier n` ∧ `IFC0.LadderLB1Supplier n` ∧
`IFC5.LadderVarthetaSupplierLive n`, and the third conjunct ⟸ (§2)
`UniversalVarthetaSupplier n` ⟸ `UniversalTauWordDescentSupply n` ⟸
`UniversalKernelSpan n ∧ UniversalGeneratorDescent n`.  NO FULL CLOSURE: the field's
open content after this unit is {package supplier, lb1 supplier, C3-at-abstract-
normalizers + R5} — the vartheta leg is no longer an independent ladder-side item.

## Trust boundary

`LadderFieldLive₃` and `LB1CarrierLive` are NEW statements (standing review);
`LB1CarrierLive` + its two theorems are byte-identical promotions from
`scratch/LB1G_probe.lean` (namespace re-homed `LB1GProbe` → `IFC5`, the house
re-namespacing convention).  Nothing signed is touched; no leanspec name changes.
Cite ledger: **empty** — Lean core over the landed corpus; `#print axioms` footer is
the audit.  Zero `sorry`, zero new axiom.  Verdict: `runs/wave-c/verdict_LDR.md`.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.IFC5

open Uniformity.Density
open Uniformity.Density.Tower

section FieldBoundary

universe uW uG uKt uL

/-! ## §1 The A-I.8 field as a named target, and its exact THREE-supplier boundary -/

/-- **The A-I.8 ladder field** — the capstone `ladder` field's exact `Prop`
(`I10_I15_I18.lean` NODE I.10 post-A-I.8; ID12's `hladder` hypothesis), as a named
campaign target: every canonical ladder configuration at degree `n` admits the A-I.8
supply record.  Supersedes `LadderFieldLive` (the A-I.6 shape) as the campaign target,
exactly as `LadderSupplyLive₃` superseded `LadderSupplyLive`.  NEW STATEMENT (review). -/
def LadderFieldLive₃ (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] (K : Type) [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
    (L : Type uL) [Field L] [Algebra Kt L]
    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
    CanonicalLadderConfig C B G Kt L N v ρ q n →
      LadderSupplyLive₃.{uW, uG, uKt, uL} C B G Kt L N v ρ q n

/-- Anti-drift pin: the named target IS the signed capstone field's type (definitional;
byte-copied binder block). -/
example {n : ℕ} (h : CapstoneHypotheses.{uW, uG, uKt, uL} n) :
    LadderFieldLive₃.{uW, uG, uKt, uL} n :=
  h.ladder

/-- ★ **The exact post-A-I.8 boundary: THREE suppliers, not four.**  The A-I.8 field
splits, machine-exactly, into IFC0's package/lb1 suppliers (byte-unchanged, the tension-
record forms are still the right shapes for these two legs) and the LVT live vartheta
supplier — the `mp1` leg is ELIMINATED from the boundary by the A-I.8 generic compiler
`mp1CarrierLiveDirect_of_steps`.  Forward: record projections.  Backward: constructor
with the compiler.  No mathematics is proved; the obligation is repartitioned. -/
theorem ladderFieldLive₃_iff_suppliers {n : ℕ} :
    LadderFieldLive₃.{uW, uG, uKt, uL} n ↔
      IFC0.LadderPackageSupplier.{uW, uG, uKt, uL} n ∧
      IFC0.LadderLB1Supplier.{uW, uG, uKt, uL} n ∧
      LadderVarthetaSupplierLive.{uG, uKt, uL} n := by
  constructor
  · intro h
    exact ⟨fun O _ K _ C B G _ Kt _ L _ _ N v ρ q hcfg =>
             (h O K C B G Kt L N v ρ q hcfg).package,
           fun O _ K _ C B G _ Kt _ L _ _ N v ρ q hcfg =>
             (h O K C B G Kt L N v ρ q hcfg).lb1,
           fun O _ K _ C B G _ Kt _ L _ _ N v ρ q hcfg =>
             (h O K C B G Kt L N v ρ q hcfg).vartheta⟩
  · rintro ⟨hp, hl, hv⟩
    exact fun O _ K _ C B G _ Kt _ L _ _ N v ρ q hcfg =>
      ⟨hp O K C B G Kt L N v ρ q hcfg,
       hl O K C B G Kt L N v ρ q hcfg,
       mp1CarrierLiveDirect_of_steps C B G Kt L N v ρ q n,
       hv O K C B G Kt L N v ρ q hcfg⟩

/-- The assembly direction alone, in consumable form. -/
theorem ladderFieldLive₃_of_suppliers {n : ℕ}
    (hp : IFC0.LadderPackageSupplier.{uW, uG, uKt, uL} n)
    (hl : IFC0.LadderLB1Supplier.{uW, uG, uKt, uL} n)
    (hv : LadderVarthetaSupplierLive.{uG, uKt, uL} n) :
    LadderFieldLive₃.{uW, uG, uKt, uL} n :=
  ladderFieldLive₃_iff_suppliers.mpr ⟨hp, hl, hv⟩

/-! ## §2 The vartheta advance: the ladder leg is SUBSUMED by the deepTwist campaign's
universal vartheta supplier

The live guard hands the consumer an arising realization `X` witnessing the same socket
data (`GaugeFamilyViewEq` along `eG`) whose gauge range contains `i`; with `3 ≤ i` that
index is deep-live, so the per-witness exporter fires at it and G10U's view transport
carries the conclusion to the external socket datum.  ⚠ HONESTY: the received witness's
`normalizer` is the abstract field — TWD's canonical-normalizer `rfl` closure does NOT
apply to it, which is exactly why the hypothesis is the UNIVERSAL supplier and not the
laurent-pointwise one. -/

/-- ★ **The ladder vartheta leg from the deepTwist campaign's universal vartheta
supplier** — the two vartheta obligations share ONE boundary: any discharge of
`UniversalVarthetaSupplier n` (G10U §5, the deepTwist field's own vartheta half)
discharges the ladder record's `vartheta` leg at every canonical configuration. -/
theorem ladderVarthetaSupplierLive_of_universal {n : ℕ}
    (h : DeepExport.UniversalVarthetaSupplier.{uG, uKt, uL} n) :
    LadderVarthetaSupplierLive.{uG, uKt, uL} n := by
  intro O _ K _ C B G _ Kt _ L _ _ N v ρ q _hcfg i hi hlive
  obtain ⟨dom, dvr, E, fE, core, Aℛ, X, eK, eG, _hslot, _hblock, hgauge, hilive⟩ := hlive
  letI := dom
  letI := dvr
  letI := fE
  exact DeepExport.varthetaRes_of_perWitness_view X eG hgauge hilive
    (h O Kt E L core Aℛ X i ⟨hi, hilive.2⟩)

/-- The ladder vartheta leg from USUP's universal tau supply (rows C3 + R5 at every
arising realization) — one step further down the deep-witness campaign's chain. -/
theorem ladderVarthetaSupplierLive_of_tauSupply {n : ℕ}
    (h : DeepExport.UniversalTauWordDescentSupply.{uG, uKt, uL} n) :
    LadderVarthetaSupplierLive.{uG, uKt, uL} n :=
  ladderVarthetaSupplierLive_of_universal
    (DeepExport.universalVarthetaSupplier_of_tauSupply h)

/-- ★ The ladder vartheta leg's DEEPEST landed boundary: TWD's two universal remainders —
`UniversalKernelSpan` (row C3; closed pointwise at every canonical-normalizer
realization) + `UniversalGeneratorDescent` (row R5, OPEN-LETTERS).  After this theorem
the ladder `vartheta` leg is NOT an independent campaign item: it rests on exactly the
`Prop`s the deepTwist campaign already targets. -/
theorem ladderVarthetaSupplierLive_of_span_descent {n : ℕ}
    (hs : DeepExport.UniversalKernelSpan.{uKt, uL} n)
    (hd : DeepExport.UniversalGeneratorDescent.{uKt, uL} n) :
    LadderVarthetaSupplierLive.{uG, uKt, uL} n :=
  ladderVarthetaSupplierLive_of_tauSupply
    (DeepExport.universalTauWordDescentSupply_of_span_descent hs hd)

/-- ★ **The capstone `ladder` field's post-unit assembly**: package supplier + lb1
supplier + the deep-witness campaign's universal vartheta supplier give the SIGNED
field's exact type.  With `ladderVarthetaSupplierLive_of_span_descent`, the field's
full open content is `{package, lb1, UniversalKernelSpan-at-abstract-normalizers +
UniversalGeneratorDescent}`. -/
theorem ladderFieldLive₃_of_boundary {n : ℕ}
    (hp : IFC0.LadderPackageSupplier.{uW, uG, uKt, uL} n)
    (hl : IFC0.LadderLB1Supplier.{uW, uG, uKt, uL} n)
    (hv : DeepExport.UniversalVarthetaSupplier.{uG, uKt, uL} n) :
    LadderFieldLive₃.{uW, uG, uKt, uL} n :=
  ladderFieldLive₃_of_suppliers hp hl (ladderVarthetaSupplierLive_of_universal hv)

end FieldBoundary

section LB1Twin

universe uO uK uW

/-! ## §3 The lb1 leg: LB1G's RESTRICT-ANYWAY twin, named (promotion from
`scratch/LB1G_probe.lean`, byte-identical modulo the namespace re-home)

⚠ NOT ENACTED INTO THE SIGNED SURFACE: retyping `LadderSupplyLive₃.lb1` (and hence the
signed capstone field) to the restricted twin is an OWNER AMENDMENT (LB1G verdict,
"BLOCKED-BECAUSE"), and its production `Exported` instantiation requires the missing
C-to-E interface-export relation (`RealizedRungInterfaceExport`-genre: the same
realization witness and slot/block views as `CanonicalLadderLiveAt`, plus a contentful
interface-export clause) — NO such relation is landed, and this unit does not invent
one.  The shapes below are the named target for that later amendment. -/

/-- The honest E-layer restriction: `Exported I` is the C-to-E relation saying that `I` is the
rung interface exported by a realization witnessing the same external socket data.  That
relation is deliberately an explicit parameter here because no such exporter/relation is landed.
Instantiating it with `fun _ => True` recovers the unrestricted carrier. -/
def LB1CarrierLive {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (Exported : Ladder.RungInterface.{uO, uK, uW} C B → Prop) : Prop :=
  ∀ I : Ladder.RungInterface.{uO, uK, uW} C B, Exported I →
    (1 < I.sides.card ∨ ∃ p ∈ I.sides, ¬ I.SepSide p) →
    Nonempty (Ladder.BlockSuite I)

/-- Supersession direction: the old arbitrary-interface carrier implies every restricted twin. -/
theorem lb1CarrierLive_of_unrestricted
    {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    {C : Ladder.SlotCarrier O K} {B : Ladder.BlockData C}
    {Exported : Ladder.RungInterface.{uO, uK, uW} C B → Prop}
    (h : Ladder.LB1Carrier.{uO, uK, uW} C B) :
    LB1CarrierLive.{uO, uK, uW} C B Exported :=
  fun I _ htrigger => h I htrigger

/-- The landed E.57 funnel needs no arbitrary-interface strength: partition legs only for
exported triggering interfaces assemble the restricted carrier. -/
theorem lb1CarrierLive_of_exported_partitionLegs
    {O : Type uO} [CommRing O] [IsDomain O] {K : Type uK} [Field K]
    {C : Ladder.SlotCarrier O K} {B : Ladder.BlockData C}
    {Exported : Ladder.RungInterface.{uO, uK, uW} C B → Prop}
    (hpart : ∀ I : Ladder.RungInterface.{uO, uK, uW} C B, Exported I →
      (1 < I.sides.card ∨ ∃ p ∈ I.sides, ¬ I.SepSide p) →
      Nonempty (Ladder.PartitionLeg I)) :
    LB1CarrierLive.{uO, uK, uW} C B Exported :=
  fun I hI htrigger => (hpart I hI htrigger).map Ladder.PartitionLeg.toBlockSuite

/-- Anti-cook fence (machine pin of the probe's disclosure): at the trivial export
relation the twin degenerates to exactly the unrestricted carrier — so the later
amendment's honesty rests entirely on a CONTENTFUL `Exported`. -/
theorem lb1CarrierLive_top_iff
    {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    {C : Ladder.SlotCarrier O K} {B : Ladder.BlockData C} :
    LB1CarrierLive.{uO, uK, uW} C B (fun _ => True) ↔
      Ladder.LB1Carrier.{uO, uK, uW} C B :=
  ⟨fun h I ht => h I trivial ht, lb1CarrierLive_of_unrestricted⟩

end LB1Twin

end Uniformity.Density.IFC5

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only. -/

#print axioms Uniformity.Density.IFC5.LadderFieldLive₃
#print axioms Uniformity.Density.IFC5.ladderFieldLive₃_iff_suppliers
#print axioms Uniformity.Density.IFC5.ladderFieldLive₃_of_suppliers
#print axioms Uniformity.Density.IFC5.ladderVarthetaSupplierLive_of_universal
#print axioms Uniformity.Density.IFC5.ladderVarthetaSupplierLive_of_tauSupply
#print axioms Uniformity.Density.IFC5.ladderVarthetaSupplierLive_of_span_descent
#print axioms Uniformity.Density.IFC5.ladderFieldLive₃_of_boundary
#print axioms Uniformity.Density.IFC5.LB1CarrierLive
#print axioms Uniformity.Density.IFC5.lb1CarrierLive_of_unrestricted
#print axioms Uniformity.Density.IFC5.lb1CarrierLive_of_exported_partitionLegs
#print axioms Uniformity.Density.IFC5.lb1CarrierLive_top_iff
