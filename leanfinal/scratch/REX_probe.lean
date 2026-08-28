/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I10_I15_I18
import Uniformity.ChapC.C130sg
import Uniformity.ChapC.C132fd0
import Uniformity.ChapC.C132sg2
import Uniformity.ChapE.E13

/-!
# REX — producer-side recenter-step surface and live-funnel refutation probe

This file is probe-only.  It checks two independent facts:

* a cite-faithful recenter-step export and the corresponding restricted MP1 shape elaborate;
* the current `LadderSupplyLive.mp1` field still carries unrestricted MP1, and the landed
  degree-four S2 socket refutes it already from degree bookkeeping.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.REXProbe

open Polynomial IsLocalRing
open Uniformity.Density
open Uniformity.Density.Ladder
open Uniformity.Density.Tower

universe uW uG uKt uL uR

/-! ## Proposed producer surface -/

/-- Items 2--4 of `MidPeelEmission`; the cite-produced irreducibility field is absent. -/
structure MP1StepCore {O : Type} [CommRing O] {K : Type} [Field K]
    {C : Ladder.SlotCarrier O K} (B B' : Ladder.BlockData C) where
  quot : Ladder.BlockData C
  hkey : quot.Φ = B'.Φ
  hpeel : B.F = B'.Φ * quot.F
  hmass : quot.F.natDegree + C.D = B.F.natDegree
  hthr : quot.T = B.T
  iface : Ladder.RungInterface.{0, 0, uW} C quot

/-- The GN15-Theorem-2.3 payload exported by one actual recentering step.

`residual = psi * residualQuot` and `¬ psi ∣ residualQuot` is the producer-side spelling of
`ord_psi(residual) = 1`, once `psi` is irreducible.  `exactLeaf` is the indispensable
identification of the theorem-selected factor with the exact key exported to `B'`.
-/
structure GNCitePayload {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : Tower.ArisingCore (O := O) Kt L n}
    (A : Tower.ChainRealization (O := O) (π := core.π) (F := core.F)
      (H₀ := core.H₀) (hpin := core.hpin) core.T Kt E L)
    (g phi : Polynomial O) (kRes : Type uR) [Field kRes] where
  e' : ℕ
  f' : ℕ
  u' : ℕ
  source : Tower.FGMNSourceData core.T A.keys e' f' u'
  sourceLaws : Nonempty (Tower.FGMNSourceLaws core.T A.keys e' f' u' source)
  keyPolynomial : source.keyPolynomial phi
  tangentClass : ¬ source.initialEquiv phi (A.keys.keyAt core.r)
  monicInput : g.Monic
  slope : ℚ
  slope_pos : 0 < slope
  residual : Polynomial kRes
  psi : Polynomial kRes
  psi_monic : psi.Monic
  psi_irreducible : Irreducible psi
  residualQuot : Polynomial kRes
  residual_factorization : residual = psi * residualQuot
  residual_multiplicity_one : ¬ psi ∣ residualQuot
  leaf : Polynomial O
  leaf_monic : leaf.Monic
  leaf_dvd_input : leaf ∣ g
  exactLeaf : leaf = phi

/-- External same-socket recenter-step export.  All realization views and all cite data occur
under one existential witness, preventing a step from a different realization being spliced
into the socket. -/
def RecenterStep
    {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B B' : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
    (L : Type uL) [Field L] [Algebra Kt L]
    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (rho : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
    (n : ℕ) (Lambda : Polynomial O) : Prop :=
  ∃ (_dom : IsDomain O) (_dvr : IsDiscreteValuationRing O)
    (E : Type) (fE : Field E) (core : Tower.ArisingCore (O := O) Kt L n)
    (A : Tower.ChainRealization (O := O) (π := core.π) (F := core.F)
      (H₀ := core.H₀) (hpin := core.hpin) (fieldE := fE) core.T Kt E L)
    (X : Tower.RealizedInput core A)
    (eK : core.T.fld core.i ≃+* K) (eG : G ≃* Tower.GaugeLattice.{uG} core.r),
    Tower.SlotViewEq X eK C ∧
    (∃ hC : C = X.stageCarrierTransport eK,
      Tower.BlockViewEq X eK (hC ▸ B)) ∧
    Tower.GaugeFamilyViewEq X (N.transport eG)
      (fun j => (v j).comp eG.symm.toMonoidHom)
      (fun j => (rho j).comp (Tower.C130s18.kerComapAlong eG (v j))) q ∧
    Lambda ≠ 0 ∧ Lambda.natDegree < C.D ∧
    B'.Φ = B.Φ - Lambda ∧ B'.Φ ∣ B.F ∧
    (∃ (kRes : Type) (_fRes : Field kRes),
      Nonempty (GNCitePayload (Kt := Kt) (L := L) A B.F B'.Φ kRes)) ∧
    Nonempty (MP1StepCore.{uW} B B')

/-- Honest MP1: only successors actually exported by the same realization are quantified. -/
def MP1CarrierLive
    {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
    (L : Type uL) [Field L] [Algebra Kt L]
    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (rho : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n : ℕ) : Prop :=
  ∀ (Lambda : Polynomial O), Lambda ≠ 0 → Lambda.natDegree < C.D →
    ∀ (B' : Ladder.BlockData C), B'.Φ = B.Φ - Lambda → B'.Φ ∣ B.F →
      RecenterStep.{uW, uG, uKt, uL} C B B' G Kt L N v rho q n Lambda →
      Nonempty (Ladder.MidPeelEmission.{0, 0, uW} B B')

/-! ## Landed S2 prefix: the exact point where the full export stops -/

/-- The part of a cite payload that the landed S2/μ₃ bank really supplies. -/
structure S2LandedPrefix {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) where
  source : Tower.FGMNSourceData
    (Tower.C130s17.S2DepthTwo h2 hq)
    (Tower.C130s2.s2DepthTwoKeyChain h2 hq) 2 1 21
  source_eq : source = Tower.C132fd0.s2SourceDataTwo h2 hq
  sourceLaws : Nonempty (Tower.FGMNSourceLaws
    (Tower.C130s17.S2DepthTwo h2 hq)
    (Tower.C130s2.s2DepthTwoKeyChain h2 hq) 2 1 21 source)
  exactKey : Polynomial O
  exactKey_eq : exactKey = Tower.C130s2.s2DepthTwoKeyAt h2 hq 2
  keyPolynomial : source.keyPolynomial exactKey
  monic : exactKey.Monic

/-- S2 supplies the depth-two chain, μ₃ source record, and key-polynomialhood of `Φ₂`.
It does not supply a recentered external `B'`, tangent non-equivalence, a selected slope/factor
of the input residual with multiplicity one, the exact GN leaf identification, or the peel core.
-/
noncomputable def s2LandedPrefix {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) : S2LandedPrefix h2 hq where
  source := Tower.C132fd0.s2SourceDataTwo h2 hq
  source_eq := rfl
  sourceLaws := ⟨Tower.C132fd0.s2SourceLawsTwo_of h2 hq
    (Tower.C132rp10b.s2Mu3_hex h2 hq) (Tower.C132kp6b.s2Mu3_hconv h2 hq)⟩
  exactKey := Tower.C130s2.s2DepthTwoKeyAt h2 hq 2
  exactKey_eq := rfl
  keyPolynomial := Tower.C132kp4.s2Mu3KeyPoly_Φ₂ h2 hq
  monic := Tower.C132nv1.s2Φ₂_monic h2 hq

/-- The only exact key presently tied to the S2 μ₃ source is the carried tangent key itself,
so it fails GN15's required `phi`-not-equivalent-to-`phi_r` hypothesis. -/
theorem s2LandedPrefix_tangentClass_impossible {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) :
    ¬ (¬ (Tower.C132fd0.s2SourceDataTwo h2 hq).initialEquiv
      (Tower.C130s2.s2DepthTwoKeyAt h2 hq 2)
      ((Tower.C130s2.s2DepthTwoKeyChain h2 hq).keyAt 2)) := by
  intro hne
  apply hne
  exact Tower.C132kp0.S2Mu3InitialEquiv_refl h2 hq _

/-! ## Refutation passing through the live funnel -/

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

/-- For a length-one block, `F` itself is another legal key of carrier degree; use `F + 1`
as its own key-free length-one input. -/
noncomputable def recenteredAtInput {O : Type} [CommRing O] [IsDomain O]
    {K : Type} [Field K] {C : Ladder.SlotCarrier O K} (B : Ladder.BlockData C)
    (hmu : B.μ = 1) : Ladder.BlockData C where
  Φ := B.F
  F := B.F + 1
  μ := 1
  hμ := le_rfl
  hΦ := (B.natDegree_F).2
  hΦdeg := by rw [(B.natDegree_F).1, hmu, one_mul]
  A := fun j => if j = 0 then 1 else 0
  hdev := by simp
  hdegA := by
    intro j hj
    interval_cases j
    simpa using C.hD
  hkeyfree := by
    rw [Polynomial.map_add, Polynomial.map_one]
    exact IsCoprime.add_one_left_of_dvd dvd_rfl
  hA0 := by simp
  T := B.T

abbrev B2' : Ladder.BlockData C2 := recenteredAtInput B2 rfl

lemma B2_F_eq : B2.F = B2.Φ + 1 := rfl

lemma B2_D_eq : C2.D = 4 := rfl

lemma B2Prime_key : B2'.Φ = B2.Φ - (-1 : Polynomial O2) := by
  rw [show B2'.Φ = B2.F from rfl, B2_F_eq]
  ring

lemma B2Prime_dvd : B2'.Φ ∣ B2.F := by
  rw [show B2'.Φ = B2.F from rfl]

/-- The MP1 conclusion is impossible: its quotient is a block, hence has degree at least `D`,
but `hmass` at the S2 parent (`μ = 1`) forces quotient degree plus `D` to equal `D`. -/
theorem s2_midPeel_empty : ¬ Nonempty (Ladder.MidPeelEmission.{0, 0, 0} B2 B2') := by
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

theorem s2_unrestricted_mp1_false : ¬ Ladder.MP1Carrier.{0, 0, 0} C2 B2 := by
  intro h
  apply s2_midPeel_empty
  exact h (-1) (by norm_num) (by rw [B2_D_eq]; norm_num) B2' B2Prime_key B2Prime_dvd

theorem s2_ladderSupplyLive_false :
    ¬ IFC5.LadderSupplyLive.{0, 0, 0, 0} C2 B2 G2 K2 L2 N2 v2 rho2 q2 4 :=
  fun S => s2_unrestricted_mp1_false S.mp1

theorem s2_canonical_ladder_config :
    CanonicalLadderConfig C2 B2 G2 K2 L2 N2 v2 rho2 q2 4 :=
  Tower.C130sg.s2Frontier_ladder_socket h2_padic q2_padic L2 threshold0

/-- ★ The current rebound capstone remains empty at degree four through its unrestricted
`mp1` leg.  A-I.7 (`mp1` replaced by the same-realization live form) is therefore forced. -/
theorem capstoneHypotheses_four_refuted_via_mp1 :
    ¬ CapstoneHypotheses.{0, 0, 0, 0} 4 := by
  intro h
  apply s2_ladderSupplyLive_false
  exact h.ladder O2 K2 C2 B2 G2 K2 L2 N2 v2 rho2 q2 s2_canonical_ladder_config

end Uniformity.Density.REXProbe

end

/-! Axiom footprint: expected Lean core only. -/

#print axioms Uniformity.Density.REXProbe.RecenterStep
#print axioms Uniformity.Density.REXProbe.MP1CarrierLive
#print axioms Uniformity.Density.REXProbe.s2LandedPrefix
#print axioms Uniformity.Density.REXProbe.s2_unrestricted_mp1_false
#print axioms Uniformity.Density.REXProbe.s2_ladderSupplyLive_false
#print axioms Uniformity.Density.REXProbe.capstoneHypotheses_four_refuted_via_mp1
