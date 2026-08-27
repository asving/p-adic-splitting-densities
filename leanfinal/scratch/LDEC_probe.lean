/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFC0
import Uniformity.ChapE.E57p

/-!
# LDEC probes for the LADDER-SUPPLY blueprint

These are elaboration probes, not supplier proofs.  They pin the exact L0 split, the two
small record-assembly routes which are already landed, and the mismatch between the ladder
guard's live-range view and the unbounded vartheta conclusion.

There is no `sorry` and no new axiom.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.LDECProbe

open Uniformity.Density

universe uO uK uW uG uKt uL

/-! ## Exact L0 decomposition -/

example {n : ℕ} :
    IFC0.LadderField.{uW, uG, uKt, uL} n ↔
      IFC0.LadderPackageSupplier.{uW, uG, uKt, uL} n ∧
      IFC0.LadderLB1Supplier.{uW, uG, uKt, uL} n ∧
      IFC0.LadderMP1Supplier.{uW, uG, uKt, uL} n ∧
      IFC0.LadderVarthetaSupplier.{uG, uKt, uL} n :=
  IFC0.ladderField_iff_suppliers

example {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C) :
    Ladder.HE7APackage.{uO, uK, uW} C B ↔
      Nonempty (Ladder.RungInterface.{uO, uK, uW} C B) :=
  Iff.rfl

/-! ## What the guard actually exports -/

theorem guard_has_domain {O : Type} [CommRing O] {K : Type} [Field K]
    {C : Ladder.SlotCarrier O K} {B : Ladder.BlockData C}
    {G : Type uG} [CommGroup G] {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L]
    [Algebra Kt L] {N : Gauge.NormSection G} {v : ℕ → (G →* Multiplicative ℤ)}
    {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ} {q : ℕ → ℤ} {n : ℕ}
    (hcfg : CanonicalLadderConfig C B G Kt L N v ρ q n) :
    Nonempty (IsDomain O) := by
  rcases hcfg with ⟨dom, _dvr, _data⟩
  exact ⟨dom⟩

/-! ## Landed LB1 assembly; the missing input is `PartitionLeg` -/

theorem lb1Carrier_of_partitionLegs {O : Type uO} [CommRing O] [IsDomain O]
    {K : Type uK} [Field K] (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (hpart : ∀ I : Ladder.RungInterface.{uO, uK, uW} C B,
      (1 < I.sides.card ∨ ∃ p ∈ I.sides, ¬ I.SepSide p) →
        Nonempty (Ladder.PartitionLeg I)) :
    Ladder.LB1Carrier.{uO, uK, uW} C B := by
  intro I htrigger
  exact (hpart I htrigger).map Ladder.PartitionLeg.toBlockSuite

/-! ## Landed MP1 record assembly; all mathematical fields remain explicit inputs -/

def midPeelEmission_of_fields {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    {C : Ladder.SlotCarrier O K} (B B' quot : Ladder.BlockData C)
    (hkey : quot.Φ = B'.Φ) (hpeel : B.F = B'.Φ * quot.F)
    (hmass : quot.F.natDegree + C.D = B.F.natDegree) (hthr : quot.T = B.T)
    (iface : Ladder.RungInterface.{uO, uK, uW} C quot)
    (hirr : Irreducible (B'.Φ.map (algebraMap O (FractionRing O)))) :
    Ladder.MidPeelEmission.{uO, uK, uW} B B' where
  quot := quot
  hkey := hkey
  hpeel := hpeel
  hmass := hmass
  hthr := hthr
  iface := iface
  hirr := hirr
  hef := B'.hΦdeg.trans C.hef

/-! ## Vartheta binding and the guard's off-range freedom -/

example {G : Type uG} [CommGroup G] {Kt : Type uKt} [Field Kt]
    {L : Type uL} [Field L] [Algebra Kt L] {N : Gauge.NormSection G}
    {v : ℕ → (G →* Multiplicative ℤ)} {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ}
    {q : ℕ → ℤ} {i : ℕ} :
    Ladder.VarthetaRes G Kt L N v ρ q i ↔
      Gauge.HVarthetaRes G Kt L N (v i) (ρ i) (q i) :=
  ⟨fun h => h.supplied, fun h => ⟨h⟩⟩

example {O : Type} [CommRing O] {K : Type} [Field K]
    {C : Ladder.SlotCarrier O K} {B : Ladder.BlockData C}
    {G : Type uG} [CommGroup G] {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L]
    [Algebra Kt L] {N : Gauge.NormSection G} {v : ℕ → (G →* Multiplicative ℤ)}
    {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ} {q : ℕ → ℤ} {n : ℕ} (q₀ : ℤ) :
    CanonicalLadderConfig C B G Kt L N v ρ q n ↔
      CanonicalLadderConfig C B G Kt L N v ρ (Function.update q 0 q₀) n :=
  Tower.C130s18.canonicalLadderConfigData_update_q_zero q₀

/-! The supplier itself has no live-range premise: once a concrete guard witness is supplied,
it yields an `HVarthetaRes` at every external index `i ≥ 3`. -/
theorem varthetaSupplier_bites_at_every_ge_three
    {n : ℕ} (h : IFC0.LadderVarthetaSupplier.{uG, uKt, uL} n)
    {O : Type} [CommRing O] {K : Type} [Field K]
    {C : Ladder.SlotCarrier O K} {B : Ladder.BlockData C}
    {G : Type uG} [CommGroup G] {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L]
    [Algebra Kt L] {N : Gauge.NormSection G} {v : ℕ → (G →* Multiplicative ℤ)}
    {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ} {q : ℕ → ℤ}
    (hcfg : CanonicalLadderConfig C B G Kt L N v ρ q n) (i : ℕ) (hi : 3 ≤ i) :
    Gauge.HVarthetaRes G Kt L N (v i) (ρ i) (q i) :=
  (h O K C B G Kt L N v ρ q hcfg i hi).supplied

end Uniformity.Density.LDECProbe

/-! ## Axiom audit -/

#print axioms Uniformity.Density.LDECProbe.guard_has_domain
#print axioms Uniformity.Density.LDECProbe.lb1Carrier_of_partitionLegs
#print axioms Uniformity.Density.LDECProbe.midPeelEmission_of_fields
#print axioms Uniformity.Density.LDECProbe.varthetaSupplier_bites_at_every_ge_three

