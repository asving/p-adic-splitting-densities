/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFC5
import Uniformity.ChapC.C130sg

/-!
# AI6: closed refutation probe for the unbounded ladder field

This file assembles VAUD's off-range replacement engine with the landed S2 socket and a
sitewise residue obstruction over a rational-function extension.  There is no `sorry` and no
new axiom.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.AI6Probe

open Polynomial IsLocalRing
open Uniformity.Density
open Uniformity.Density.Tower

abbrev O2 := ℤ_[2]

theorem h2_padic : Irreducible (2 : O2) := by
  simpa using PadicInt.irreducible_p (p := 2)

theorem q2_padic : residueCard O2 = 2 := residueCard_padicInt 2

abbrev T2 := Tower.C130s17.S2DepthTwo h2_padic q2_padic
abbrev K2 := T2.fld 2
abbrev L2 := FractionRing (Polynomial K2)
abbrev G2 := Tower.GaugeLattice 2

def threshold0 : Tower.C130sg.S2LevelOneThreshold where
  T := 0
  Tnat := 0
  T_natCast := rfl
  T_lt_key := by norm_num

abbrev S2 := Tower.C130sg.s2Frontier h2_padic q2_padic L2 threshold0
abbrev X2 := S2.s2RealizedInput

abbrev C2 := X2.stageCarrierTransport (RingEquiv.refl K2)
abbrev B2 := X2.inputBlockTransport (RingEquiv.refl K2)
abbrev N2 : Gauge.NormSection G2 :=
  S2.toCarrier.normalizer.arenaNormSection0.transport (Tower.gaugeLatticeEquiv 2).symm
abbrev v0 : ℕ → (G2 →* Multiplicative ℤ) := Tower.gaugeHeightFamily X2
abbrev rho0 : ∀ j : ℕ, MonoidHom.ker (v0 j) →* L2ˣ := Tower.canonicalResFamily X2
abbrev q0 : ℕ → ℤ := Tower.useHeightFamily X2

def kernelHeight {G U : Type*} [CommGroup G] [CommMonoid U]
    (κ : ℕ → Tower.KernelRead G U) (j : ℕ) : G →* Multiplicative ℤ :=
  (κ j).1

def kernelResidue {G U : Type*} [CommGroup G] [CommMonoid U]
    (κ : ℕ → Tower.KernelRead G U) (j : ℕ) : MonoidHom.ker (kernelHeight κ j) →* U :=
  (κ j).2

/-- VAUD's replacement engine, repeated here so this independently compiled probe imports no
other scratch file. -/
theorem gauge_view_offRange_kernel_replacement
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type*} [Field Kt] {E : Type*} [Field E]
    {L : Type*} [Field L] [Algebra Kt L] {n : ℕ}
    {core : Tower.ArisingCore (O := O) Kt L n}
    {A : Tower.ChainRealization (O := O) (π := core.π) (F := core.F)
      (H₀ := core.H₀) (hpin := core.hpin) core.T Kt E L}
    (X : Tower.RealizedInput core A)
    (N : Gauge.NormSection (Tower.GaugeLattice core.r))
    (κ : ℕ → Tower.KernelRead (Tower.GaugeLattice core.r) Lˣ) (q : ℕ → ℤ)
    {j : ℕ} (hj : ¬ Tower.GaugeLive core.r j)
    (κj : Tower.KernelRead (Tower.GaugeLattice core.r) Lˣ) (qj : ℤ) :
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

def liveOne : Tower.LiveLevel 2 := ⟨1, by exact ⟨by decide, by decide⟩⟩

/-- The first Laurent exponent at the unique live level of the depth-two synchronized
lattice. -/
def firstExponent : G2 →* Multiplicative ℤ where
  toFun g := Multiplicative.ofAdd
    (Multiplicative.toAdd (Tower.gaugeLatticeEquiv 2 g liveOne)).1
  map_one' := rfl
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    simp

def junkV : G2 →* Multiplicative ℤ := 1

noncomputable def xUnit : L2ˣ := Units.mk0
  (algebraMap (Polynomial K2) L2 Polynomial.X)
  (by
    intro h
    apply Polynomial.X_ne_zero (R := K2)
    apply IsFractionRing.injective (Polynomial K2) L2
    simpa using h)

noncomputable def junkRho : MonoidHom.ker junkV →* L2ˣ :=
  (zpowersHom L2ˣ xUnit).comp
    (firstExponent.comp (MonoidHom.ker junkV).subtype)

/-- At the S2 normal section, `q = 1, s = 2` produces first Laurent exponent `-1`.
This is the depth-two analogue of VAUD's `bad_vartheta_value`. -/
lemma firstExponent_vartheta : firstExponent (N2.varthetaEl 1 2) =
    Multiplicative.ofAdd (-1 : ℤ) := by
  rfl

lemma xUnit_inv_not_constant (u : K2ˣ) :
    (((xUnit⁻¹ : L2ˣ) : L2)) ≠ algebraMap K2 L2 (u : K2) := by
  intro h
  have hm := congrArg (fun z : L2 => z * (xUnit : L2)) h
  have hp : (1 : Polynomial K2) = Polynomial.C (u : K2) * Polynomial.X := by
    apply IsFractionRing.injective (Polynomial K2) L2
    simpa [xUnit, IsScalarTower.algebraMap_apply K2 (Polynomial K2) L2] using hm
  have hc := congrArg (fun p : Polynomial K2 => p.coeff 0) hp
  simpa using hc

/-- A false sitewise carrier at the off-range S2 index. -/
theorem s2_junk_vartheta_negative :
    ¬ Gauge.HVarthetaRes G2 K2 L2 N2 junkV junkRho 1 := by
  intro h
  obtain ⟨hmem, u, hu⟩ := h 2
  apply xUnit_inv_not_constant u
  rw [← hu]
  congr 1
  change xUnit⁻¹ = junkRho ⟨N2.varthetaEl 1 2, hmem⟩
  symm
  simp [junkRho, firstExponent_vartheta]

def kappa0 : ℕ → Tower.KernelRead G2 L2ˣ := fun j => ⟨v0 j, rho0 j⟩
def junkRead : Tower.KernelRead G2 L2ˣ := ⟨junkV, junkRho⟩
def badKappa : ℕ → Tower.KernelRead G2 L2ˣ := Function.update kappa0 3 junkRead

abbrev badV : ℕ → (G2 →* Multiplicative ℤ) := kernelHeight badKappa
abbrev badRho : ∀ j : ℕ, MonoidHom.ker (badV j) →* L2ˣ := kernelResidue badKappa
def badQ : ℕ → ℤ := Function.update q0 3 1

theorem s2_bad_gauge_view : Tower.GaugeFamilyViewEq X2 N2 badV badRho badQ := by
  apply (gauge_view_offRange_kernel_replacement X2 N2 kappa0 q0
    (j := 3) (by
      rw [Tower.C130s18.s2ArisingCore_r h2_padic q2_padic]
      rintro ⟨_, hlt⟩
      omega) junkRead 1).mp
  exact X2.gaugeFamilyViewEq

/-- The landed degree-four S2 socket with only its off-range index `3` replaced by the false
site.  The carrier/block antecedent and hence the antecedent shared by all four IFC0 suppliers
remain inhabited. -/
theorem s2_bad_ladder_socket :
    CanonicalLadderConfig C2 B2 G2 K2 L2 N2 badV badRho badQ 4 := by
  refine ⟨inferInstance, inferInstance, FractionRing (Polynomial O2), inferInstance,
    Tower.C130s17.s2ArisingCore h2_padic q2_padic L2, S2.toCarrier, X2,
    RingEquiv.refl K2, MulEquiv.refl G2, X2.slotViewEq (RingEquiv.refl K2),
    ⟨rfl, X2.blockViewEq (RingEquiv.refl K2)⟩, ?_⟩
  obtain ⟨hN, hview⟩ := s2_bad_gauge_view
  refine ⟨hN, fun j hj => ?_⟩
  obtain ⟨hpack, hq⟩ := hview j hj
  refine ⟨?_, hq⟩
  have hv : (badV j).comp (MulEquiv.refl G2).symm.toMonoidHom = badV j := by
    ext g
    rfl
  have hr : (badRho j).comp (Tower.C130s18.kerComapAlong (MulEquiv.refl G2) (badV j)) =
      badRho j := Tower.C130s18.kerComapAlong_refl (badV j) (badRho j)
  calc
    _ = ⟨badV j, badRho j⟩ := by
      apply Sigma.ext hv
      exact heq_of_eq hr
    _ = _ := hpack

/-- The fourth supplier conclusion fails at the first demanded index. -/
theorem s2_bad_vartheta_three :
    ¬ Ladder.VarthetaRes G2 K2 L2 N2 badV badRho badQ 3 := by
  intro h
  apply s2_junk_vartheta_negative
  have hsup := h.supplied
  change Gauge.HVarthetaRes G2 K2 L2 N2 (badKappa 3).1 (badKappa 3).2 (badQ 3) at hsup
  rw [show badKappa 3 = junkRead by simp [badKappa], show badQ 3 = 1 by simp [badQ]] at hsup
  exact hsup

/-- ★ Closed countermodel: the signed unbounded ladder field is false already at the landed
degree-four S2 occurrence. -/
theorem ladderField_four_refuted : ¬ IFC0.LadderField.{0, 0, 0, 0} 4 := by
  intro h
  have hs := h O2 K2 C2 B2 G2 K2 L2 N2 badV badRho badQ s2_bad_ladder_socket
  exact s2_bad_vartheta_three (hs.vartheta 3 le_rfl)

/-- The current signed capstone block is therefore uninhabited at degree four. -/
theorem capstoneHypotheses_four_refuted :
    ¬ CapstoneHypotheses.{0, 0, 0, 0} 4 := fun h => ladderField_four_refuted h.ladder

end Uniformity.Density.AI6Probe

/-! ## AXCHECK FOOTER -- expected exactly Lean core
`{propext, Classical.choice, Quot.sound}`. -/

#print axioms Uniformity.Density.AI6Probe.firstExponent_vartheta
#print axioms Uniformity.Density.AI6Probe.s2_junk_vartheta_negative
#print axioms Uniformity.Density.AI6Probe.gauge_view_offRange_kernel_replacement
#print axioms Uniformity.Density.AI6Probe.s2_bad_gauge_view
#print axioms Uniformity.Density.AI6Probe.s2_bad_ladder_socket
#print axioms Uniformity.Density.AI6Probe.s2_bad_vartheta_three
#print axioms Uniformity.Density.AI6Probe.ladderField_four_refuted
#print axioms Uniformity.Density.AI6Probe.capstoneHypotheses_four_refuted
