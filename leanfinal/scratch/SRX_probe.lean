/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I10RecenterLiveS2
import Uniformity.ChapE.E13

/-!
# SRX — the landed S2 recenter-export audit

This probe identifies the proper depth-two key actually constructed by the C132 μ₃ bank,
then checks it against the production `GNCitePayload`/`RecenterStep` surface.

The bank's proper successor is

`g₈ = Φ₂ ^ 2 - 2 ^ 4 * Φ'`.

It is a degree-eight μ₃ key, has normalized residual `X + 1`, and is not μ₃-initial-
equivalent to the carried key `Φ₂`.  Thus it discharges the key-polynomial and tangent-class
rows in its own depth-two key role.  It is not, however, a same-degree recentering
`Φ₂ - Λ` with `deg Λ < 4`, and it cannot divide the landed degree-four input `Φ₂ + 1`.

Independently, every production `RecenterStep` contains an `MP1StepCore`.  At the landed
mass-one S2 parent that core is impossible for every successor: its quotient is a block of
degree at least `D`, while `hmass` requires `deg quotient + D = deg input = D`.  Hence the
production `RecenterStep` is empty at S2 and `MP1CarrierLive` is inhabited there only
vacuously.  Every declaration below is closed.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.SRXProbe

open Polynomial IsLocalRing
open Uniformity.Density
open Uniformity.Density.Ladder
open Uniformity.Density.Tower

universe uKt uL uR

/-! ## 0. Faithfulness tooth for the production payload surface -/

/-- The production carrier permits its `slope` to be replaced by any positive rational
without changing any other field.  Thus `slope_pos` does not encode the source clause that
`-slope` is a slope of the input's principal Newton polygon. -/
def payloadWithArbitraryPositiveSlope
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : Tower.ArisingCore (O := O) Kt L n}
    {A : Tower.ChainRealization (O := O) (π := core.π) (F := core.F)
      (H₀ := core.H₀) (hpin := core.hpin) core.T Kt E L}
    {g phi : Polynomial O} {kRes : Type uR} [Field kRes]
    (P : IFC5.GNCitePayload A g phi kRes) (slope : ℚ) (hslope : 0 < slope) :
    IFC5.GNCitePayload A g phi kRes :=
  { P with slope := slope, slope_pos := hslope }

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
abbrev v2 : ℕ → (G2 →* Multiplicative ℤ) := Tower.gaugeHeightFamily X2
abbrev rho2 : ∀ j : ℕ, MonoidHom.ker (v2 j) →* L2ˣ := Tower.canonicalResFamily X2
abbrev q2 : ℕ → ℤ := Tower.useHeightFamily X2

/-! ## 1. The genuine proper key constructed by the C132 bank -/

/-- The depth-two proper key produced by the landed μ₃ normalized-existence construction. -/
noncomputable def mu3SuccessorKey : Polynomial O2 :=
  Tower.C132rp10b.g8 h2_padic q2_padic

theorem mu3SuccessorKey_monic : mu3SuccessorKey.Monic :=
  Tower.C132rp10.s2Mu3_gEight_monic h2_padic q2_padic

theorem mu3SuccessorKey_natDegree : mu3SuccessorKey.natDegree = 8 :=
  Tower.C132rp10.s2Mu3_gEight_natDegree h2_padic q2_padic

theorem mu3SuccessorKey_normRes :
    Tower.C132rp8.s2Mu3NormRes h2_padic q2_padic mu3SuccessorKey =
      (Polynomial.X + 1 : Polynomial K2) :=
  Tower.C132rp10b.s2Mu3NormRes_g8 h2_padic q2_padic

/-- The C132 criterion turns `g₈`'s landed monicity, degree, and residual computation into
literal key-polynomialhood for the μ₃ source. -/
theorem mu3SuccessorKey_isKey :
    Tower.C132kp0.S2Mu3KeyPoly h2_padic q2_padic mu3SuccessorKey := by
  refine Tower.C132kp3.s2Mu3_key_criterion h2_padic q2_padic
    mu3SuccessorKey mu3SuccessorKey_monic ?_ ?_ ?_ ?_
  · rw [mu3SuccessorKey_natDegree]
    change 8 = 2 * 1 *
      (Tower.C130s2.s2DepthTwoKeyAt h2_padic q2_padic 2 : Polynomial O2).natDegree
    rw [Tower.C132nv1.s2Φ₂_natDegree]
  · rw [mu3SuccessorKey_normRes]
    exact Tower.C132rp10.s2Mu3_X_add_one_irreducible h2_padic q2_padic
  · rw [mu3SuccessorKey_normRes]
    simpa using Polynomial.natDegree_X_add_C (1 : K2)
  · rw [mu3SuccessorKey_normRes]
    simp

/-- The successor has a genuinely new μ₃ tangent class: its residual is `X+1`, whereas
the carried `Φ₂` has residual `1`. -/
theorem mu3SuccessorKey_tangentClass :
    ¬ Tower.C132kp0.S2Mu3InitialEquiv h2_padic q2_padic mu3SuccessorKey
      ((Tower.C130s2.s2DepthTwoKeyChain h2_padic q2_padic).keyAt 2) := by
  intro heq
  have hres := Tower.C132kp6.s2Mu3_initial_to_residual h2_padic q2_padic heq
  rw [mu3SuccessorKey_normRes] at hres
  change (Polynomial.X + 1 : Polynomial K2) =
    Tower.C132rp8.s2Mu3NormRes h2_padic q2_padic
      (Tower.C130s2.s2DepthTwoKeyAt h2_padic q2_padic 2) at hres
  rw [Tower.C132kp4.s2Mu3NormRes_Φ₂] at hres
  have hX : (Polynomial.X : Polynomial K2) = 0 := by
    linear_combination hres
  exact Polynomial.X_ne_zero hX

/-- The two source-record fields at `(2,1,21)` are fully landed. -/
theorem s2SourceLaws : Nonempty (Tower.FGMNSourceLaws T2 S2.toCarrier.keys 2 1 21
    (Tower.C132fd0.s2SourceDataTwo h2_padic q2_padic)) := by
  exact ⟨Tower.C132fd0.s2SourceLawsTwo_of h2_padic q2_padic
    (Tower.C132rp10b.s2Mu3_hex h2_padic q2_padic)
    (Tower.C132kp6b.s2Mu3_hconv h2_padic q2_padic)⟩

/-- The landed S2 input supplies the payload's bare monicity field. -/
theorem s2Input_monic : B2.F.Monic := (B2.natDegree_F).2

/-! ## 2. Why the proper key cannot be the requested live recentering -/

theorem s2CarrierDegree : C2.D = 4 := rfl

theorem s2InputDegree : B2.F.natDegree = 4 := by
  rw [(B2.natDegree_F).1, show B2.μ = 1 from rfl, one_mul, s2CarrierDegree]

theorem s2CurrentKeyDegree : B2.Φ.natDegree = 4 := by
  rw [B2.hΦdeg, s2CarrierDegree]

/-- The proper degree-eight μ₃ key cannot divide the landed degree-four input.  Thus it
cannot fill `leaf_dvd_input` for the actual S2 occurrence. -/
theorem mu3SuccessorKey_not_dvd_s2Input : ¬ mu3SuccessorKey ∣ B2.F := by
  intro hdvd
  have hle := Polynomial.natDegree_le_of_dvd hdvd s2Input_monic.ne_zero
  rw [mu3SuccessorKey_natDegree, s2InputDegree] at hle
  omega

/-- Nor is `g₈` a same-degree recentering `Φ₂ - Λ`: subtracting a polynomial of degree
strictly below four preserves the monic degree-four leading term. -/
theorem mu3SuccessorKey_not_recentered (Lambda : Polynomial O2)
    (hdeg : Lambda.natDegree < C2.D) : mu3SuccessorKey ≠ B2.Φ - Lambda := by
  have hdeg' : Lambda.natDegree < B2.Φ.natDegree := by
    rw [s2CurrentKeyDegree]
    rw [s2CarrierDegree] at hdeg
    exact hdeg
  have hrhs : (B2.Φ - Lambda).natDegree = B2.Φ.natDegree :=
    Polynomial.natDegree_sub_eq_left_of_natDegree_lt hdeg'
  intro heq
  have hnat := congrArg Polynomial.natDegree heq
  rw [mu3SuccessorKey_natDegree, hrhs, s2CurrentKeyDegree] at hnat
  omega

/-! ## 3. The production `RecenterStep` is empty at the mass-one S2 parent -/

/-- `MP1StepCore` is impossible for every proposed S2 successor.  This uses only the
mass-one parent and the fact that its quotient field is itself a positive-mass block. -/
theorem s2_mp1StepCore_empty (B' : Ladder.BlockData C2) :
    ¬ Nonempty (IFC5.MP1StepCore.{0} B2 B') := by
  rintro ⟨E⟩
  have hqdeg := (E.quot.natDegree_F).1
  have hBdeg := (B2.natDegree_F).1
  have hqLower : C2.D ≤ E.quot.F.natDegree := by
    rw [hqdeg]
    simpa using Nat.mul_le_mul_right C2.D E.quot.hμ
  rw [show B2.μ = 1 from rfl, one_mul] at hBdeg
  have hD : 0 < C2.D := C2.hD
  have hmass : E.quot.F.natDegree + C2.D = B2.F.natDegree := E.hmass
  have hCD : (X2.stageCarrierTransport (RingEquiv.refl K2)).D = C2.D := rfl
  omega

/-- Consequently no production `RecenterStep` exists at this landed socket, regardless of
the candidate `Λ`, successor block, or GN payload. -/
theorem s2_recenterStep_empty (B' : Ladder.BlockData C2) (Lambda : Polynomial O2) :
    ¬ IFC5.RecenterStep.{0, 0, 0, 0}
      C2 B2 B' G2 K2 L2 N2 v2 rho2 q2 4 Lambda := by
  rintro ⟨_dom, _dvr, E, fE, core, A, X, eK, eG, hslot, hblock, hgauge,
    hne, hdeg, hrec, hdvd, hpayload, hcore⟩
  exact s2_mp1StepCore_empty B' hcore

/-- The live MP1 proposition is therefore true at S2 only by ex falso from its
`RecenterStep` premise.  This is a vacuity certificate, not an honest step export. -/
theorem s2_mp1CarrierLive_vacuous :
    IFC5.MP1CarrierLive.{0, 0, 0, 0} C2 B2 G2 K2 L2 N2 v2 rho2 q2 4 := by
  intro Lambda _hne _hdeg B' _hrec _hdvd hstep
  exact (s2_recenterStep_empty B' Lambda hstep).elim

end Uniformity.Density.SRXProbe

end

/-! Axiom footprint: all probe declarations should remain Lean-core only. -/

#print axioms Uniformity.Density.SRXProbe.mu3SuccessorKey_isKey
#print axioms Uniformity.Density.SRXProbe.mu3SuccessorKey_tangentClass
#print axioms Uniformity.Density.SRXProbe.payloadWithArbitraryPositiveSlope
#print axioms Uniformity.Density.SRXProbe.mu3SuccessorKey_not_dvd_s2Input
#print axioms Uniformity.Density.SRXProbe.mu3SuccessorKey_not_recentered
#print axioms Uniformity.Density.SRXProbe.s2_mp1StepCore_empty
#print axioms Uniformity.Density.SRXProbe.s2_recenterStep_empty
#print axioms Uniformity.Density.SRXProbe.s2_mp1CarrierLive_vacuous
