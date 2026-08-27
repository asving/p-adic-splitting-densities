/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFC0
import Uniformity.ChapC.C130sg

/-!
# VAUD stop-line probes for LADDER-SUPPLY

The declarations below audit, rather than prove, the open ladder suppliers.  They pin:

* the landed (honestly conditional) S2 degree-four ladder socket;
* the extra arbitrary-interface bite made by `LB1Carrier` after an inhabited guard;
* the exact hypotheses from which `MP1Carrier` demands recentered-key irreducibility;
* the existence of a concrete false sitewise vartheta carrier;
* an owner-amendment candidate whose vartheta field is restricted to indices live in a
  realization witnessing the same socket, together with its exact four-supplier assembly;
* the degree mismatch of the only landed S2 occurrence.

There is no `sorry` and no new axiom.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.VAUDProbe

open Polynomial IsLocalRing
open Uniformity.Density

universe uE uO uK uW uG uKt uL

/-! ## 1. The landed inhabited socket and the LB1 arbitrary-interface tooth -/

section S2Socket

open Tower

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
variable {L : Type uL} [Field L] [Algebra ((Tower.C130s17.S2DepthTwo h2 hq).fld 2) L]

/-- The only landed ladder occurrence: an honestly conditional, degree-four S2 socket. -/
theorem s2_degree_four_socket [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (w : Tower.C130sg.S2LevelOneThreshold) :
    CanonicalLadderConfig
      ((Tower.C130sg.s2Frontier h2 hq L w).s2RealizedInput.stageCarrierTransport
        (RingEquiv.refl ((Tower.C130s17.S2DepthTwo h2 hq).fld 2)))
      ((Tower.C130sg.s2Frontier h2 hq L w).s2RealizedInput.inputBlockTransport
        (RingEquiv.refl ((Tower.C130s17.S2DepthTwo h2 hq).fld 2)))
      (Tower.GaugeLattice.{uG} 2) ((Tower.C130s17.S2DepthTwo h2 hq).fld 2) L
      ((Tower.C130sg.s2Frontier h2 hq L w).toCarrier.normalizer.arenaNormSection0.transport
        (Tower.gaugeLatticeEquiv 2).symm)
      (Tower.gaugeHeightFamily (Tower.C130sg.s2Frontier h2 hq L w).s2RealizedInput)
      (Tower.canonicalResFamily (Tower.C130sg.s2Frontier h2 hq L w).s2RealizedInput)
      (Tower.useHeightFamily (Tower.C130sg.s2Frontier h2 hq L w).s2RealizedInput) 4 :=
  Tower.C130sg.s2Frontier_ladder_socket (L := L) h2 hq w

/-- The landed S2 occurrence is definitionally at input degree `4`, not degree `2`. -/
theorem landed_s2_degree_ne_two : (4 : ℕ) ≠ 2 := by decide

/-- Index `3`, demanded by the current supplier, is outside the landed S2 gauge range. -/
theorem s2_three_not_gaugeLive : ¬ Tower.GaugeLive 2 3 := by
  rintro ⟨_, h⟩
  omega

end S2Socket

/-- At any inhabited ladder socket, LB1 immediately quantifies over an independently supplied
`RungInterface`; the guard provides no linkage premise for this `I`. -/
theorem lb1_inhabited_socket_tooth
    {O : Type} [CommRing O] {K : Type} [Field K]
    {C : Ladder.SlotCarrier O K} {B : Ladder.BlockData C}
    {G : Type uG} [CommGroup G] {Kt : Type uKt} [Field Kt]
    {L : Type uL} [Field L] [Algebra Kt L]
    {N : Gauge.NormSection G} {v : ℕ → (G →* Multiplicative ℤ)}
    {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ} {q : ℕ → ℤ} {n : ℕ}
    (hs : IFC0.LadderLB1Supplier.{uW, uG, uKt, uL} n)
    (hcfg : CanonicalLadderConfig C B G Kt L N v ρ q n)
    (I : Ladder.RungInterface.{0, 0, uW} C B)
    (htrigger : 1 < I.sides.card ∨ ∃ p ∈ I.sides, ¬ I.SepSide p) :
    Nonempty (Ladder.BlockSuite I) :=
  hs O K C B G Kt L N v ρ q hcfg I htrigger

/-! ## 2. MP1's exact cite-hypothesis bite -/

/-- At an inhabited socket the MP1 conclusion certifies irreducibility from precisely the
five displayed trigger hypotheses.  In particular there is no irreducibility or
recentered-key-cite hypothesis among the inputs to this theorem. -/
theorem mp1_inhabited_socket_forces_irreducible
    {O : Type} [CommRing O] {K : Type} [Field K]
    {C : Ladder.SlotCarrier O K} {B : Ladder.BlockData C}
    {G : Type uG} [CommGroup G] {Kt : Type uKt} [Field Kt]
    {L : Type uL} [Field L] [Algebra Kt L]
    {N : Gauge.NormSection G} {v : ℕ → (G →* Multiplicative ℤ)}
    {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ} {q : ℕ → ℤ} {n : ℕ}
    (hs : IFC0.LadderMP1Supplier.{uW, uG, uKt, uL} n)
    (hcfg : CanonicalLadderConfig C B G Kt L N v ρ q n)
    (Λ : Polynomial O) (hΛ0 : Λ ≠ 0) (hΛdeg : Λ.natDegree < C.D)
    (B' : Ladder.BlockData C) (hrecenter : B'.Φ = B.Φ - Λ) (hdvd : B'.Φ ∣ B.F) :
    Irreducible (B'.Φ.map (algebraMap O (FractionRing O))) := by
  obtain ⟨E⟩ := hs O K C B G Kt L N v ρ q hcfg Λ hΛ0 hΛdeg B' hrecenter hdvd
  exact E.hirr

/-! ## 3. Vartheta: concrete negative carrier and a live-range amendment -/

abbrev BadG := Multiplicative (ℤ × ℤ)

def badV : BadG →* Multiplicative ℤ :=
  AddMonoidHom.toMultiplicative (AddMonoidHom.fst ℤ ℤ)

def badN : Gauge.NormSection BadG where
  n := fun k => Multiplicative.ofAdd (k, if k = 2 then 1 else 0)
  n_zero := by simp

noncomputable def complexIUnit : ℂˣ := Units.mk0 Complex.I Complex.I_ne_zero

noncomputable def badRho : MonoidHom.ker badV →* ℂˣ :=
  (zpowersHom ℂˣ complexIUnit).comp
    ((AddMonoidHom.toMultiplicative (AddMonoidHom.snd ℤ ℤ)).comp
      (MonoidHom.ker badV).subtype)

lemma bad_vartheta_value : badN.varthetaEl 1 2 =
    Multiplicative.ofAdd ((0 : ℤ), (-1 : ℤ)) := by
  show (badN.n 1) ^ 2 * (badN.n ((2 : ℕ) * 1))⁻¹ = _
  simp only [badN]
  norm_num
  rfl

/-- A concrete, core-axiom-only negative sitewise certificate. -/
theorem vartheta_sitewise_negative :
    ¬ Gauge.HVarthetaRes BadG ℚ ℂ badN badV badRho 1 := by
  intro h
  obtain ⟨hmem, u, hu⟩ := h 2
  have hval : ((badRho ⟨badN.varthetaEl 1 2, hmem⟩ : ℂˣ) : ℂ) = -Complex.I := by
    have hv : badRho ⟨badN.varthetaEl 1 2, hmem⟩ = complexIUnit ^ (-1 : ℤ) := by
      simp [badRho, bad_vartheta_value, complexIUnit]
    rw [hv]
    simp [complexIUnit, Complex.inv_I]
  rw [hval] at hu
  have him := congrArg Complex.im hu
  have hcast : algebraMap ℚ ℂ (u : ℚ) = ((u : ℚ) : ℂ) :=
    eq_ratCast (algebraMap ℚ ℂ) (u : ℚ)
  rw [hcast] at him
  simp [Complex.ratCast_im] at him

/- A dependent `(v, ρ)` family is most conveniently mutated through the sigma package used
by the guard itself. -/
def kernelHeight {G U : Type*} [CommGroup G] [CommMonoid U]
    (κ : ℕ → Tower.KernelRead G U) (j : ℕ) : G →* Multiplicative ℤ :=
  (κ j).1

def kernelResidue {G U : Type*} [CommGroup G] [CommMonoid U]
    (κ : ℕ → Tower.KernelRead G U) (j : ℕ) : MonoidHom.ker (kernelHeight κ j) →* U :=
  (κ j).2

/-- The guard view is invariant under an arbitrary dependent `(v,ρ)` replacement and an
arbitrary `q` replacement at every off-range index.  This is the structural negative tooth:
no theorem using only this view can inspect the replaced site. -/
theorem gauge_view_offRange_kernel_replacement
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : Tower.ArisingCore (O := O) Kt L n}
    {A : Tower.ChainRealization (O := O) (π := core.π) (F := core.F)
      (H₀ := core.H₀) (hpin := core.hpin) core.T Kt E L}
    (X : Tower.RealizedInput core A)
    (N : Gauge.NormSection (Tower.GaugeLattice.{uG} core.r))
    (κ : ℕ → Tower.KernelRead (Tower.GaugeLattice.{uG} core.r) Lˣ) (q : ℕ → ℤ)
    {j : ℕ} (hj : ¬ Tower.GaugeLive core.r j)
    (κj : Tower.KernelRead (Tower.GaugeLattice.{uG} core.r) Lˣ) (qj : ℤ) :
    Tower.GaugeFamilyViewEq X N (kernelHeight κ) (kernelResidue κ) q ↔
      Tower.GaugeFamilyViewEq X N
        (kernelHeight (Function.update κ j κj))
        (kernelResidue (Function.update κ j κj)) (Function.update q j qj) := by
  unfold Tower.GaugeFamilyViewEq
  constructor <;> rintro ⟨hN, hview⟩ <;> refine ⟨hN, fun k hk => ?_⟩
  · have hkj : k ≠ j := fun e => hj (e ▸ hk)
    simpa [kernelHeight, kernelResidue, Function.update_of_ne hkj] using hview k hk
  · have hkj : k ≠ j := fun e => hj (e ▸ hk)
    simpa [kernelHeight, kernelResidue, Function.update_of_ne hkj] using hview k hk

/- The repaired live-index predicate repeats the realization witness so `core.r` is in
scope and the liveness proof belongs to the same witness that pins the external families. -/
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

/-- Proposed owner amendment: the vartheta conclusion is demanded only when the same socket
data admit a realization whose gauge range contains `i`. -/
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

/-- IFC0-local repaired result record.  Its first three fields are byte-identical to E.24;
only the vartheta field receives the live-index premise. -/
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

def LadderFieldLive (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] (K : Type) [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
    (L : Type uL) [Field L] [Algebra Kt L]
    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
    CanonicalLadderConfig C B G Kt L N v ρ q n →
      LadderSupplyLive.{uW, uG, uKt, uL} C B G Kt L N v ρ q n

/-- The proposed range repair preserves the exact four-way supplier assembly. -/
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

theorem ladderFieldLive_of_suppliers {n : ℕ}
    (hp : IFC0.LadderPackageSupplier.{uW, uG, uKt, uL} n)
    (hl : IFC0.LadderLB1Supplier.{uW, uG, uKt, uL} n)
    (hm : IFC0.LadderMP1Supplier.{uW, uG, uKt, uL} n)
    (hv : LadderVarthetaSupplierLive.{uG, uKt, uL} n) :
    LadderFieldLive.{uW, uG, uKt, uL} n :=
  ladderFieldLive_iff_suppliers.mpr ⟨hp, hl, hm, hv⟩

end Uniformity.Density.VAUDProbe

#print axioms Uniformity.Density.VAUDProbe.s2_degree_four_socket
#print axioms Uniformity.Density.VAUDProbe.lb1_inhabited_socket_tooth
#print axioms Uniformity.Density.VAUDProbe.mp1_inhabited_socket_forces_irreducible
#print axioms Uniformity.Density.VAUDProbe.vartheta_sitewise_negative
#print axioms Uniformity.Density.VAUDProbe.gauge_view_offRange_kernel_replacement
#print axioms Uniformity.Density.VAUDProbe.ladderFieldLive_iff_suppliers
#print axioms Uniformity.Density.VAUDProbe.ladderFieldLive_of_suppliers
