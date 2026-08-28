/-
Shape-only probe for A-I.8.  This file is not a landed statement.

The proposed direct route removes the GN selected-factor payload from the live recenter
export.  The same realization instead owns one concrete FGMN source predicate, its laws,
and membership of the peeled key in that predicate.  At enactment the relevant
`key_irreducible` law must be supplied by the direct key proof, not by citation.
-/

import Uniformity.ChapI.I10RecenterLive
import Uniformity.ChapC.C134p1d

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.A8DProbe

open Polynomial IsLocalRing
open Uniformity.Density
open Uniformity.Density.Ladder
open Uniformity.Density.Tower

universe uW uG uKt uL

/-! The final bridge is independent of residual calculus: once the three `IsMuKey`
conjuncts exist, the standard factorization argument gives ordinary irreducibility. -/

theorem muDvd_self
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (L : LevelDatum F H₀ hpin) {g : Polynomial O} (hg : g ≠ 0) :
    Tower.C134dv2g.MuDvd L g g := by
  refine ⟨1, Or.inl ⟨?_, by simp⟩⟩
  simp only [mul_one, sub_self]
  rw [Tower.C130s6.dvSupp_zero_eq_top F L.u L.hℓ]
  exact Ne.lt_top (Tower.C130s6.dvSupp_ne_top_of_ne_zero F L.u L.ℓ hg)

theorem irreducible_of_isMuKey
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (L : LevelDatum F H₀ hpin) {g : Polynomial O}
    (hkey : Tower.C134dv2g.IsMuKey L g) : Irreducible g := by
  obtain ⟨hmon, hmin, hprime⟩ := hkey
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have hzero := Polynomial.natDegree_eq_zero_of_isUnit hu
    have hpos := hmin.1
    omega
  · by_contra hcon
    have hua : ¬ IsUnit a := fun ha => hcon (Or.inl ha)
    have hub : ¬ IsUnit b := fun hb => hcon (Or.inr hb)
    have hg0 : g ≠ 0 := hmon.ne_zero
    have ha0 : a ≠ 0 := by rintro rfl; exact hg0 (by rw [hab, zero_mul])
    have hb0 : b ≠ 0 := by rintro rfl; exact hg0 (by rw [hab, mul_zero])
    have hlc : a.leadingCoeff * b.leadingCoeff = 1 := by
      rw [← Polynomial.leadingCoeff_mul, ← hab]
      exact hmon.leadingCoeff
    have hdega : 0 < a.natDegree := by
      rcases Nat.eq_zero_or_pos a.natDegree with hzero | hpos
      · exfalso
        refine hua ?_
        have hCa : a = Polynomial.C (a.coeff 0) :=
          Polynomial.eq_C_of_natDegree_eq_zero hzero
        rw [hCa] at hlc
        rw [Polynomial.leadingCoeff_C] at hlc
        rw [hCa]
        exact Polynomial.isUnit_C.mpr (.of_mul_eq_one _ hlc)
      · exact hpos
    have hdegb : 0 < b.natDegree := by
      rcases Nat.eq_zero_or_pos b.natDegree with hzero | hpos
      · exfalso
        refine hub ?_
        have hCb : b = Polynomial.C (b.coeff 0) :=
          Polynomial.eq_C_of_natDegree_eq_zero hzero
        rw [hCb] at hlc
        rw [Polynomial.leadingCoeff_C] at hlc
        rw [hCb]
        exact Polynomial.isUnit_C.mpr (.of_mul_eq_one _ (by rw [mul_comm]; exact hlc))
      · exact hpos
    have hdeg : a.natDegree + b.natDegree = g.natDegree := by
      rw [hab, Polynomial.natDegree_mul ha0 hb0]
    have hself : Tower.C134dv2g.MuDvd L g (a * b) := by
      rw [← hab]
      exact muDvd_self L hg0
    rcases hprime a b hself with hdvd | hdvd
    · exact hmin.2 a ha0 (by omega) hdvd
    · exact hmin.2 b hb0 (by omega) hdvd

/-- The direct replacement for the GN payload.  It retains the same-chain provenance but
asks only for the key predicate and its directly proved irreducibility law. -/
structure DirectKeyPayload {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : Tower.ArisingCore (O := O) Kt L n}
    (A : Tower.ChainRealization (O := O) (π := core.π) (F := core.F)
      (H₀ := core.H₀) (hpin := core.hpin) core.T Kt E L)
    (phi : Polynomial O) where
  e' : ℕ
  f' : ℕ
  u' : ℕ
  source : Tower.FGMNSourceData core.T A.keys e' f' u'
  keyPolynomial : source.keyPolynomial phi
  key_irreducible : ∀ g : Polynomial O,
    source.keyPolynomial g → g.Monic → Irreducible g

/-- A-I.8 draft surface.  In addition to replacing the GN payload, this incorporates the
DWR provenance equalities tying the successor block to the quotient exported by the step. -/
def RecenterStepDirect
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
    B'.T = B.T ∧
    Nonempty (DirectKeyPayload (Kt := Kt) (L := L) A B'.Φ) ∧
    ∃ step : IFC5.MP1StepCore.{uW} B B',
      step.quot.F = B'.F ∧
      step.quot.T = B.T ∧
      B.F = B'.Φ * B'.F

/-- The direct payload plus the peel core compiles to the exact E.40 conclusion. -/
theorem midPeelEmission_of_recenterStepDirect
    {O : Type} [CommRing O] {K : Type} [Field K]
    {C : Ladder.SlotCarrier O K} {B B' : Ladder.BlockData C}
    {G : Type uG} [CommGroup G] {Kt : Type uKt} [Field Kt]
    {L : Type uL} [Field L] [Algebra Kt L]
    {N : Gauge.NormSection G} {v : ℕ → (G →* Multiplicative ℤ)}
    {rho : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ} {q : ℕ → ℤ}
    {n : ℕ} {Lambda : Polynomial O}
    (hstep : RecenterStepDirect.{uW, uG, uKt, uL}
      C B B' G Kt L N v rho q n Lambda) :
    Nonempty (Ladder.MidPeelEmission.{0, 0, uW} B B') := by
  rcases hstep with
    ⟨dom, dvr, E, fE, core, A, X, eK, eG, _hslot, _hblock, _hgauge,
      _hLambda0, _hLambdaDeg, _hrecenter, _hdvd, _hT, ⟨direct⟩, step,
      _hquotF, _hquotT, _hpeelBound⟩
  letI : IsDomain O := dom
  letI : IsDiscreteValuationRing O := dvr
  have hirrO : Irreducible B'.Φ :=
    direct.key_irreducible B'.Φ direct.keyPolynomial B'.hΦ
  have hirr : Irreducible (B'.Φ.map (algebraMap O (FractionRing O))) :=
    (B'.hΦ.irreducible_iff_irreducible_map_fraction_map
      (K := FractionRing O)).mp hirrO
  exact ⟨{
    quot := step.quot
    hkey := step.hkey
    hpeel := step.hpeel
    hmass := step.hmass
    hthr := step.hthr
    iface := step.iface
    hirr := hirr
    hef := B'.hΦdeg.trans C.hef }⟩

/-- The A-I.8 live carrier differs only in the producer premise. -/
def MP1CarrierLiveDirect
    {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
    (L : Type uL) [Field L] [Algebra Kt L]
    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (rho : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n : ℕ) : Prop :=
  ∀ (Lambda : Polynomial O), Lambda ≠ 0 → Lambda.natDegree < C.D →
    ∀ (B' : Ladder.BlockData C), B'.Φ = B.Φ - Lambda → B'.Φ ∣ B.F →
      RecenterStepDirect.{uW, uG, uKt, uL} C B B' G Kt L N v rho q n Lambda →
      Nonempty (Ladder.MidPeelEmission.{0, 0, uW} B B')

theorem mp1CarrierLiveDirect_of_steps
    {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
    (L : Type uL) [Field L] [Algebra Kt L]
    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (rho : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n : ℕ) :
    MP1CarrierLiveDirect.{uW, uG, uKt, uL} C B G Kt L N v rho q n := by
  intro Lambda _ _ B' _ _ hstep
  exact midPeelEmission_of_recenterStepDirect hstep

end Uniformity.Density.A8DProbe

end

#print axioms Uniformity.Density.A8DProbe.DirectKeyPayload
#print axioms Uniformity.Density.A8DProbe.irreducible_of_isMuKey
#print axioms Uniformity.Density.A8DProbe.RecenterStepDirect
#print axioms Uniformity.Density.A8DProbe.midPeelEmission_of_recenterStepDirect
#print axioms Uniformity.Density.A8DProbe.MP1CarrierLiveDirect
#print axioms Uniformity.Density.A8DProbe.mp1CarrierLiveDirect_of_steps
