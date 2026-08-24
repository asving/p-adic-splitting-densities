/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130in
import Uniformity.ChapC.C130cr
import Uniformity.ChapC.C130ar

/-!
# Uniformity.ChapC.C130vw — live views and transports

This file is **chain-carrier node CC-12**.  It is the assembled C.130j/k export layer and supplies
cross-universe transports for the E.10/E.11 carrier and block, transports the synchronized
normalizer and arena through the explicit `ULift` equivalence, and states the four frozen
views (`SlotViewEq`, `BlockViewEq`, `GaugeFamilyViewEq`, `ArenaFamilyViewEq`).

Every family equation is guarded by `GaugeLive`.  In particular, no declaration identifies
the ambient canonical read with the separate terminal-field arena read, and no declaration
constrains a family off the live range.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace Uniformity.Density

open Tower
open Gauge

namespace Ladder

universe uO uK uK'

variable {O : Type uO} [CommRing O] {K : Type uK} [Field K]
variable {K' : Type uK'} [Field K']

/-- Cross-universe transport of an E.10 slot carrier along a field equivalence. -/
def SlotCarrier.transport (C : SlotCarrier O K) (e : K ≃+* K') : SlotCarrier O K' where
  D := C.D
  hD := C.hD
  eC := C.eC
  fC := C.fC
  hef := C.hef
  heC := C.heC
  hfC := C.hfC
  hgt := C.hgt
  dig := fun A => e (C.dig A)
  hgt_zero := C.hgt_zero
  dig_zero := by rw [C.dig_zero, map_zero]
  hgt_ne_top := C.hgt_ne_top
  dig_ne_zero := fun A hA hdeg h => C.dig_ne_zero A hA hdeg (e.injective (h.trans (map_zero e).symm))
  hgt_add_ge := C.hgt_add_ge
  hgt_add_eq := C.hgt_add_eq
  dig_add := by
    intro A B k hA hB hne
    have hne' : C.dig A + C.dig B ≠ 0 := by
      intro h
      apply hne
      calc
        e (C.dig A) + e (C.dig B) = e (C.dig A + C.dig B) := (map_add e _ _).symm
        _ = 0 := by rw [h, map_zero]
    exact ⟨(C.dig_add A B k hA hB hne').1,
      by rw [(C.dig_add A B k hA hB hne').2, map_add]⟩
  Full := C.Full
  hlift := by
    intro k hk c hc
    obtain ⟨A, hA, hdeg, hh, hd⟩ := C.hlift k hk (e.symm c) (by
      intro h
      apply hc
      simpa using congrArg e h)
    exact ⟨A, hA, hdeg, hh, by rw [hd, e.apply_symm_apply]⟩

@[simp] theorem SlotCarrier.transport_D (C : SlotCarrier O K) (e : K ≃+* K') :
    (C.transport e).D = C.D := rfl

@[simp] theorem SlotCarrier.transport_hgt (C : SlotCarrier O K) (e : K ≃+* K') :
    (C.transport e).hgt = C.hgt := rfl

@[simp] theorem SlotCarrier.transport_dig (C : SlotCarrier O K) (e : K ≃+* K')
    (A : Polynomial O) : (C.transport e).dig A = e (C.dig A) := rfl

/-- Cross-universe transport of an E.11 block over the transported slot carrier. -/
def BlockData.transport {C : SlotCarrier O K} (B : BlockData C) (e : K ≃+* K') :
    BlockData (C.transport e) where
  Φ := B.Φ
  F := B.F
  μ := B.μ
  hμ := B.hμ
  hΦ := B.hΦ
  hΦdeg := B.hΦdeg
  A := B.A
  hdev := B.hdev
  hdegA := B.hdegA
  hkeyfree := B.hkeyfree
  hA0 := B.hA0
  T := B.T

@[simp] theorem BlockData.transport_Φ {C : SlotCarrier O K} (B : BlockData C)
    (e : K ≃+* K') : (B.transport e).Φ = B.Φ := rfl

@[simp] theorem BlockData.transport_A {C : SlotCarrier O K} (B : BlockData C)
    (e : K ≃+* K') : (B.transport e).A = B.A := rfl

end Ladder

namespace Gauge

universe uG uG' uK

variable {G : Type uG} [CommGroup G] {G' : Type uG'} [CommGroup G']
variable {K : Type uK} [Field K]

/-- Transport a normalizer section along a cross-universe multiplicative equivalence. -/
def NormSection.transport (N : NormSection G) (e : G ≃* G') : NormSection G' where
  n := fun k => e (N.n k)
  n_zero := by rw [N.n_zero, map_one]

/-- Transport a gauge arena along a multiplicative equivalence of its group carrier. -/
def GaugeArena.transport {N : NormSection G} (A : GaugeArena G K N) (e : G ≃* G') :
    GaugeArena G' K (N.transport e) where
  v := A.v.comp e.symm.toMonoidHom
  exact_height := fun k => by
    change A.v (e.symm (e (N.n k))) = Multiplicative.ofAdd k
    rw [e.symm_apply_apply, A.exact_height]
  res := A.res.comp
    { toFun := fun x => ⟨e.symm x.1, by
        change A.v (e.symm x.1) = 1
        exact x.2⟩
      map_one' := Subtype.ext (map_one e.symm)
      map_mul' := fun x y => Subtype.ext (map_mul e.symm x.1 y.1) }

@[simp] theorem GaugeArena.transport_v {N : NormSection G} (A : GaugeArena G K N)
    (e : G ≃* G') : (A.transport e).v = A.v.comp e.symm.toMonoidHom := rfl

end Gauge

namespace Tower


open Uniformity.Density.Leaf

/-- A height homomorphism together with a residue read on its dependent kernel. -/
abbrev KernelRead (G U : Type*) [CommGroup G] [CommMonoid U] :=
  Σ v : G →* Multiplicative ℤ, MonoidHom.ker v →* U

universe uG uK uKt uL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
variable {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L] [Algebra Kt L]
variable {n e' f' u' : ℕ} {core : ArisingCore (O := O) Kt L n}
variable {A : ChainRealization (O := O) (π := core.π) (F := core.F)
  (H₀ := core.H₀) (hpin := core.hpin) core.T Kt L e' f' u'}

/-- The realized stage carrier, transported to an arbitrary universe-equivalent digit field. -/
def RealizedInput.stageCarrierTransport (X : RealizedInput core A)
    {K : Type uK} [Field K] (e : core.T.fld core.i ≃+* K) : Ladder.SlotCarrier O K :=
  (A.node.stageCarrier core.i core.hi).transport e

/-- The realized input block, transported along the same digit-field equivalence. -/
noncomputable def RealizedInput.inputBlockTransport (X : RealizedInput core A)
    {K : Type uK} [Field K] (e : core.T.fld core.i ≃+* K) :
    Ladder.BlockData (X.stageCarrierTransport e) := X.inputBlock.transport e

/-- View 1 (stage): only the mathematical fields of the exported slot are pinned. -/
def SlotViewEq (X : RealizedInput core A) {K : Type uK} [Field K]
    (e : core.T.fld core.i ≃+* K) (C : Ladder.SlotCarrier O K) : Prop :=
  C.D = core.T.Dcum core.i ∧ C.eC = core.T.ehat core.i ∧
  C.fC = core.T.fhat core.i ∧ C.hgt = A.node.hgt core.i ∧
  C.dig = (fun P => e (A.node.dig core.i P)) ∧ C.Full = A.node.Full core.i

/-- View 2 (input block): coefficients are pinned only below `μ`; the named source laws are
asserted as propositions, not by equality of proof fields. -/
def BlockViewEq (X : RealizedInput core A) {K : Type uK} [Field K]
    (e : core.T.fld core.i ≃+* K) (B : Ladder.BlockData (X.stageCarrierTransport e)) : Prop :=
  B.Φ = core.stageKey ∧ B.F = core.F₀ ∧ B.μ = core.μ ∧
  (∀ j, j < core.μ → B.A j = dev core.stageKey core.F₀ j) ∧
  IsCoprime (B.F.map (algebraMap O (FractionRing O)))
    (B.Φ.map (algebraMap O (FractionRing O))) ∧
  B.A 0 ≠ 0 ∧ B.T = A.node.thresholdNat core.i ∧ X.CanonicalThresholdAt B.T

/-- The total height family used for an export.  Its off-range branch is deliberately junk. -/
def gaugeHeightFamily (X : RealizedInput core A) :
    ℕ → GaugeLattice.{uG} core.r →* Multiplicative ℤ := fun j =>
  if hj : GaugeLive core.r j then levelHeight core.T ⟨j, hj⟩ else 1

/-- The canonical L-valued read family.  Only its live branch is part of the view. -/
def canonicalResAt (X : RealizedInput core A) {j : ℕ} (hj : GaugeLive core.r j) :
    MonoidHom.ker
      (levelHeight core.T ⟨j, hj⟩ : GaugeLattice.{uG} core.r →* Multiplicative ℤ) →* Lˣ :=
  (A.node.canonicalRes0 ⟨j, hj⟩).comp (kerGaugeEquiv core.T ⟨j, hj⟩).toMonoidHom

def canonicalResFamily (X : RealizedInput core A) :
    (j : ℕ) → MonoidHom.ker (gaugeHeightFamily X j) →* Lˣ := fun j => by
  by_cases hj : GaugeLive core.r j
  · rw [gaugeHeightFamily, dif_pos hj]
    exact canonicalResAt X hj
  · rw [gaugeHeightFamily, dif_neg hj]
    exact 1

/-- The tower use-height family.  Its off-range value is junk and is never pinned. -/
def useHeightFamily (X : RealizedInput core A) : ℕ → ℤ := fun j =>
  if hj : GaugeLive core.r j then (core.T.u (j + 1) : ℤ) else 0

/-- View 3 (canonical read): normalizer, height, canonical residue, and use-height are pinned
only at gauge-live indices. -/
def GaugeFamilyViewEq (X : RealizedInput core A)
    (N : NormSection (GaugeLattice.{uG} core.r))
    (v : ℕ → GaugeLattice.{uG} core.r →* Multiplicative ℤ)
    (ρ : (j : ℕ) → MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) : Prop :=
  N.n = (A.normalizer.arenaNormSection0.transport (gaugeLatticeEquiv core.r).symm).n ∧
  ∀ j, (hj : GaugeLive core.r j) →
    (⟨v j, ρ j⟩ : KernelRead (GaugeLattice.{uG} core.r) Lˣ) =
      ⟨levelHeight core.T ⟨j, hj⟩, canonicalResAt X hj⟩ ∧
    q j = core.T.u (j + 1)

/-- The `ULift` arena family obtained from CC-11's concrete family. -/
def arenaFamily (X : RealizedInput core A) (hr : 1 < core.r) :
    ℕ → GaugeArena (GaugeLattice.{uG} core.r) Kt
      (A.normalizer.arenaNormSection0.transport (gaugeLatticeEquiv core.r).symm) := fun j =>
  (A.node.gaugeArenaFamily0 A.normalizer hr j).transport (gaugeLatticeEquiv core.r).symm

/-- The terminal-field tower read transported to the `ULift` synchronized lattice. -/
def towerReadFamily (X : RealizedInput core A) : ℕ → GaugeLattice.{uG} core.r → Kt :=
  fun j g => A.node.towerReadFamily0 j (gaugeLatticeEquiv core.r g)

/-- View 4 (arena): the separate read and the W-leg exports are pinned only on the live
range.  There is intentionally no ambient/canonical-read clause. -/
def arenaReadAt (X : RealizedInput core A) {j : ℕ} (hj : GaugeLive core.r j) :
    MonoidHom.ker
      (levelHeight core.T ⟨j, hj⟩ : GaugeLattice.{uG} core.r →* Multiplicative ℤ) →* Ktˣ :=
  (A.node.arenaRead0 ⟨j, hj⟩).comp (kerGaugeEquiv core.T ⟨j, hj⟩).toMonoidHom

def ArenaFamilyViewEq (X : RealizedInput core A)
    (N : NormSection (GaugeLattice.{uG} core.r))
    (AA : ℕ → GaugeArena (GaugeLattice.{uG} core.r) Kt N)
    (R : ℕ → GaugeLattice.{uG} core.r → Kt) (w : ℕ → Ktˣ) : Prop :=
  ∀ j, (hj : GaugeLive core.r j) →
    (⟨(AA j).v, (AA j).res⟩ : KernelRead (GaugeLattice.{uG} core.r) Ktˣ) =
      ⟨levelHeight core.T ⟨j, hj⟩, arenaReadAt X hj⟩ ∧
    (∀ g, R j g = A.node.towerRead j ((gaugeLatticeEquiv core.r g) ⟨j, hj⟩)) ∧
    w j = A.node.peelUnit j

/-- The one witness shared by the stage, block, and canonical-read exports. -/
structure CanonicalExportWitness (X : RealizedInput core A) {K : Type uK} [Field K]
    (e : core.T.fld core.i ≃+* K) where
  C : Ladder.SlotCarrier O K
  B : Ladder.BlockData C
  N : NormSection (GaugeLattice.{uG} core.r)
  v : ℕ → GaugeLattice.{uG} core.r →* Multiplicative ℤ
  ρ : (j : ℕ) → MonoidHom.ker (v j) →* Lˣ
  q : ℕ → ℤ
  slot_eq : SlotViewEq X e C
  carrier_eq : C = X.stageCarrierTransport e
  block_eq : HEq B (X.inputBlockTransport e)
  gauge_eq : GaugeFamilyViewEq X N v ρ q

/-! The four producing equalities. -/

theorem RealizedInput.slotViewEq (X : RealizedInput core A) {K : Type uK} [Field K]
    (e : core.T.fld core.i ≃+* K) : SlotViewEq X e (X.stageCarrierTransport e) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem RealizedInput.blockViewEq (X : RealizedInput core A) {K : Type uK} [Field K]
    (e : core.T.fld core.i ≃+* K) : BlockViewEq X e (X.inputBlockTransport e) := by
  refine ⟨rfl, rfl, rfl, ?_, X.inputBlock_keyfree, X.inputBlock_A0_ne_zero, rfl,
    X.inputBlock_canonicalThreshold⟩
  exact fun j hj => X.inputBlock_A_eq_dev hj

theorem RealizedInput.gaugeFamilyViewEq (X : RealizedInput core A) :
    GaugeFamilyViewEq X
      (A.normalizer.arenaNormSection0.transport (gaugeLatticeEquiv core.r).symm)
      (gaugeHeightFamily X) (canonicalResFamily X) (useHeightFamily X) := by
  refine ⟨rfl, fun j hj => ?_⟩
  constructor
  · apply Sigma.ext (dif_pos hj)
    simp [canonicalResFamily, gaugeHeightFamily, hj]
  · exact dif_pos hj

/-- The shared ladder/canonical export package built from one realized input. -/
noncomputable def RealizedInput.canonicalExportWitness (X : RealizedInput core A)
    {K : Type uK} [Field K] (e : core.T.fld core.i ≃+* K) :
    CanonicalExportWitness X e where
  C := X.stageCarrierTransport e
  B := X.inputBlockTransport e
  N := A.normalizer.arenaNormSection0.transport (gaugeLatticeEquiv core.r).symm
  v := gaugeHeightFamily X
  ρ := canonicalResFamily X
  q := useHeightFamily X
  slot_eq := X.slotViewEq e
  carrier_eq := rfl
  block_eq := HEq.rfl
  gauge_eq := X.gaugeFamilyViewEq

theorem RealizedInput.arenaFamilyViewEq (X : RealizedInput core A) (hr : 1 < core.r) :
    ArenaFamilyViewEq X
      (A.normalizer.arenaNormSection0.transport (gaugeLatticeEquiv core.r).symm)
      (arenaFamily X hr) (towerReadFamily X) A.node.peelUnitFamily := by
  intro j hj
  have hfamily := A.node.gaugeArenaFamily0_live A.normalizer hr hj
  have hA : arenaFamily X hr j =
      (A.node.gaugeArena0At A.normalizer hj).transport (gaugeLatticeEquiv core.r).symm :=
    congrArg (fun B => B.transport (gaugeLatticeEquiv core.r).symm) hfamily
  rw [hA]
  refine ⟨?_, ?_, rfl⟩
  · apply Sigma.ext rfl
    apply heq_of_eq
    rfl
  · intro g
    rw [towerReadFamily, NodePointSource.towerReadFamily0_live _ hj]

/-! Off-range lint: the four view propositions have no off-range consequence. -/

theorem gaugeFamilyViewEq_offRange_unconstrained (X : RealizedInput core A)
    (N : NormSection (GaugeLattice.{uG} core.r))
    (v : ℕ → GaugeLattice.{uG} core.r →* Multiplicative ℤ)
    (ρ : (j : ℕ) → MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
    {j : ℕ} (hj : ¬ GaugeLive core.r j) (qj : ℤ) :
    GaugeFamilyViewEq X N v ρ q ↔ GaugeFamilyViewEq X N
      v ρ (Function.update q j qj) := by
  unfold GaugeFamilyViewEq
  constructor <;> rintro ⟨hN, h⟩ <;> refine ⟨hN, fun k hk => ?_⟩
  · have hkj : k ≠ j := fun e => hj (e ▸ hk)
    simpa [Function.update_of_ne hkj] using h k hk
  · have hkj : k ≠ j := fun e => hj (e ▸ hk)
    simpa [Function.update_of_ne hkj] using h k hk

theorem arenaFamilyViewEq_offRange_unconstrained (X : RealizedInput core A)
    (N : NormSection (GaugeLattice.{uG} core.r))
    (AA : ℕ → GaugeArena (GaugeLattice.{uG} core.r) Kt N)
    (R : ℕ → GaugeLattice.{uG} core.r → Kt) (w : ℕ → Ktˣ)
    {j : ℕ} (hj : ¬ GaugeLive core.r j)
    (Rj : GaugeLattice.{uG} core.r → Kt) (wj : Ktˣ) :
    ArenaFamilyViewEq X N AA R w ↔ ArenaFamilyViewEq X N
      AA (Function.update R j Rj) (Function.update w j wj) := by
  unfold ArenaFamilyViewEq
  constructor <;> intro h
  · intro k hk
    have hkj : k ≠ j := fun e => hj (e ▸ hk)
    rw [Function.update_of_ne hkj, Function.update_of_ne hkj]
    exact h k hk
  · intro k hk
    have hkj : k ≠ j := fun e => hj (e ▸ hk)
    have hkview := h k hk
    simpa [Function.update_of_ne hkj] using hkview

end Tower

end Uniformity.Density

section AxCheck

#print axioms Uniformity.Density.Ladder.SlotCarrier.transport
#print axioms Uniformity.Density.Ladder.SlotCarrier.transport_D
#print axioms Uniformity.Density.Ladder.SlotCarrier.transport_hgt
#print axioms Uniformity.Density.Ladder.SlotCarrier.transport_dig
#print axioms Uniformity.Density.Ladder.BlockData.transport
#print axioms Uniformity.Density.Ladder.BlockData.transport_Φ
#print axioms Uniformity.Density.Ladder.BlockData.transport_A
#print axioms Uniformity.Density.Gauge.NormSection.transport
#print axioms Uniformity.Density.Gauge.GaugeArena.transport
#print axioms Uniformity.Density.Gauge.GaugeArena.transport_v
#print axioms Uniformity.Density.Tower.KernelRead
#print axioms Uniformity.Density.Tower.RealizedInput.stageCarrierTransport
#print axioms Uniformity.Density.Tower.RealizedInput.inputBlockTransport
#print axioms Uniformity.Density.Tower.SlotViewEq
#print axioms Uniformity.Density.Tower.BlockViewEq
#print axioms Uniformity.Density.Tower.gaugeHeightFamily
#print axioms Uniformity.Density.Tower.canonicalResAt
#print axioms Uniformity.Density.Tower.canonicalResFamily
#print axioms Uniformity.Density.Tower.useHeightFamily
#print axioms Uniformity.Density.Tower.GaugeFamilyViewEq
#print axioms Uniformity.Density.Tower.arenaFamily
#print axioms Uniformity.Density.Tower.towerReadFamily
#print axioms Uniformity.Density.Tower.arenaReadAt
#print axioms Uniformity.Density.Tower.ArenaFamilyViewEq
#print axioms Uniformity.Density.Tower.CanonicalExportWitness
#print axioms Uniformity.Density.Tower.RealizedInput.slotViewEq
#print axioms Uniformity.Density.Tower.RealizedInput.blockViewEq
#print axioms Uniformity.Density.Tower.RealizedInput.gaugeFamilyViewEq
#print axioms Uniformity.Density.Tower.RealizedInput.canonicalExportWitness
#print axioms Uniformity.Density.Tower.RealizedInput.arenaFamilyViewEq
#print axioms Uniformity.Density.Tower.gaugeFamilyViewEq_offRange_unconstrained
#print axioms Uniformity.Density.Tower.arenaFamilyViewEq_offRange_unconstrained

end AxCheck
