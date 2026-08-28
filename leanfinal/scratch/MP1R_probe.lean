/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFC0

/-!
# MP1R — concrete countermodel to the unrestricted `MP1Carrier`

The legal abstract block below has key `X²` and developed polynomial
`X⁴ - 5X² + 4`.  The permitted recentering `Λ = 4` produces the divisor
`X² - 4`, which is reducible over `FractionRing ℤ`.  Hence the unrestricted
carrier's demanded `MidPeelEmission.hirr` cannot be supplied.

This is a standalone copy of the MP1 component of the older A-E.2
non-triviality certificate, placed at the path required by unit MP1R.  It has
no proof placeholder and declares no axiom.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.MP1RProbe

open Polynomial
open Uniformity.Density
open Uniformity.Density.Ladder

universe uO uK uW uG uKt uL

/-! ## The proposed live supersession shape -/

/-- Items 2--4 of `MidPeelEmission`; item 5 (`hirr`, `hef`) is deliberately absent. -/
structure MP1StepCore {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    {C : Ladder.SlotCarrier O K} (B B' : Ladder.BlockData C) where
  quot : Ladder.BlockData C
  hkey : quot.Φ = B'.Φ
  hpeel : B.F = B'.Φ * quot.F
  hmass : quot.F.natDegree + C.D = B.F.natDegree
  hthr : quot.T = B.T
  iface : Ladder.RungInterface.{uO, uK, uW} C quot

/-- A recenter-step export belonging to a realization witnessing the same external socket
views.  The exact recentered key is certified by FGMN data sharing that realization's tower
and key chain, and the producer supplies the non-item-5 peel core. -/
def CanonicalMP1StepExport
    {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
    (L : Type uL) [Field L] [Algebra Kt L]
    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
    (n : ℕ) (Λ : Polynomial O) (B' : Ladder.BlockData C) : Prop :=
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
      (fun j => (ρ j).comp (Tower.C130s18.kerComapAlong eG (v j))) q ∧
    B'.Φ = B.Φ - Λ ∧
    ∃ (e' f' u' : ℕ)
      (S : Tower.FGMNSourceData core.T A.keys e' f' u'),
      Nonempty (Tower.FGMNSourceLaws core.T A.keys e' f' u' S) ∧
      S.keyPolynomial B'.Φ ∧
      Nonempty (MP1StepCore.{0, 0, uW} B B')

/-- `MP1Carrier` restricted to recentered blocks exported by the same arising realization. -/
def MP1CarrierLive
    {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
    (L : Type uL) [Field L] [Algebra Kt L]
    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n : ℕ) : Prop :=
  ∀ (Λ : Polynomial O), Λ ≠ 0 → Λ.natDegree < C.D →
    ∀ (B' : Ladder.BlockData C),
      B'.Φ = B.Φ - Λ → B'.Φ ∣ B.F →
      CanonicalMP1StepExport.{uW, uG, uKt, uL}
        C B G Kt L N v ρ q n Λ B' →
      Nonempty (Ladder.MidPeelEmission.{0, 0, uW} B B')

/-- The proposed live carrier is discharged by the exported key law and peel core. -/
theorem mp1CarrierLive_proved
    {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
    (L : Type uL) [Field L] [Algebra Kt L]
    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n : ℕ) :
    MP1CarrierLive.{uW, uG, uKt, uL} C B G Kt L N v ρ q n := by
  intro Λ _hΛ0 _hΛdeg B' _hrecenter _hdvd hexport
  rcases hexport with
    ⟨dom, dvr, E, fE, core, A, X, eK, eG, _hslot, _hblock, _hgauge,
      _hrecenter', e', f', u', S, ⟨hL⟩, hkp, ⟨step⟩⟩
  letI : IsDomain O := dom
  letI : IsDiscreteValuationRing O := dvr
  have hirrO : Irreducible B'.Φ := hL.key_irreducible B'.Φ hkp B'.hΦ
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

/-- Supersession pin: the old unrestricted carrier implies the live carrier. -/
theorem mp1CarrierLive_of_unrestricted
    {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
    (L : Type uL) [Field L] [Algebra Kt L]
    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n : ℕ)
    (h : Ladder.MP1Carrier.{0, 0, uW} C B) :
    MP1CarrierLive.{uW, uG, uKt, uL} C B G Kt L N v ρ q n :=
  fun Λ hΛ0 hΛdeg B' hrecenter hdvd _ =>
    h Λ hΛ0 hΛdeg B' hrecenter hdvd

open scoped Classical in
/-- A degree-graded slot carrier over `ℤ`. -/
noncomputable def gradedCarrier (D e f : ℕ) (hD : 0 < D) (hef : D = e * f)
    (he : 1 ≤ e) (hf : 1 ≤ f) : SlotCarrier ℤ ℚ where
  D := D
  hD := hD
  eC := e
  fC := f
  hef := hef
  heC := he
  hfC := hf
  hgt := fun A => if A = 0 then ⊤ else (((-(A.natDegree : ℤ) : ℤ)) : WithTop ℤ)
  dig := fun A => (A.leadingCoeff : ℚ)
  hgt_zero := by simp
  dig_zero := by simp
  hgt_ne_top := by intro A hA _; simp [hA]
  dig_ne_zero := by
    intro A hA _
    simpa using Polynomial.leadingCoeff_ne_zero.mpr hA
  hgt_add_ge := by
    intro A B
    by_cases hA : A = 0
    · simp [hA]
    by_cases hB : B = 0
    · simp [hB]
    by_cases hAB : A + B = 0
    · simp [hA, hB, hAB]
    · simp only [if_neg hA, if_neg hB, if_neg hAB]
      have h := Polynomial.natDegree_add_le A B
      rcases le_total A.natDegree B.natDegree with hle | hle
      · refine le_trans (min_le_right _ _) ?_
        exact_mod_cast (by omega : -(B.natDegree : ℤ) ≤ -((A + B).natDegree : ℤ))
      · refine le_trans (min_le_left _ _) ?_
        exact_mod_cast (by omega : -(A.natDegree : ℤ) ≤ -((A + B).natDegree : ℤ))
  hgt_add_eq := by
    intro A B hne
    by_cases hA : A = 0
    · simp [hA]
    by_cases hB : B = 0
    · simp [hB]
    · have hd : A.natDegree ≠ B.natDegree := by
        intro h
        exact hne (by simp [if_neg hA, if_neg hB, h])
      have hAB : A + B ≠ 0 := by
        intro h
        have hBA : B = -A := eq_neg_of_add_eq_zero_right h
        exact hd (by rw [hBA, natDegree_neg])
      rcases Nat.lt_or_ge A.natDegree B.natDegree with hlt | hge
      · have h1 : (A + B).natDegree = B.natDegree :=
          Polynomial.natDegree_add_eq_right_of_natDegree_lt hlt
        simp only [if_neg hA, if_neg hB, if_neg hAB, h1, ← WithTop.coe_min]
        exact_mod_cast
          (by omega : -(B.natDegree : ℤ) = min (-(A.natDegree : ℤ)) (-(B.natDegree : ℤ)))
      · have hlt' : B.natDegree < A.natDegree := by omega
        have h1 : (A + B).natDegree = A.natDegree :=
          Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt'
        simp only [if_neg hA, if_neg hB, if_neg hAB, h1, ← WithTop.coe_min]
        exact_mod_cast
          (by omega : -(A.natDegree : ℤ) = min (-(A.natDegree : ℤ)) (-(B.natDegree : ℤ)))
  dig_add := by
    intro A B k hA hB hne
    have hA0 : A ≠ 0 := by intro h; rw [h] at hA; simp at hA
    have hB0 : B ≠ 0 := by intro h; rw [h] at hB; simp at hB
    rw [if_neg hA0] at hA
    rw [if_neg hB0] at hB
    have hdA : -(A.natDegree : ℤ) = k := by exact_mod_cast hA
    have hdB : -(B.natDegree : ℤ) = k := by exact_mod_cast hB
    have hd : B.natDegree = A.natDegree := by omega
    have hsum_ne : A.leadingCoeff + B.leadingCoeff ≠ 0 := by
      intro h
      apply hne
      show (A.leadingCoeff : ℚ) + (B.leadingCoeff : ℚ) = 0
      exact_mod_cast h
    have hcoeff : (A + B).coeff A.natDegree = A.leadingCoeff + B.leadingCoeff := by
      rw [Polynomial.coeff_add, Polynomial.leadingCoeff, Polynomial.leadingCoeff, hd]
    have hne0 : A + B ≠ 0 := by
      intro h
      apply hsum_ne
      rw [← hcoeff, h, Polynomial.coeff_zero]
    have hdeg_le : (A + B).natDegree ≤ A.natDegree := by
      have := Polynomial.natDegree_add_le A B
      omega
    have hdeg_ge : A.natDegree ≤ (A + B).natDegree :=
      Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff]; exact hsum_ne)
    have hdeg : (A + B).natDegree = A.natDegree := le_antisymm hdeg_le hdeg_ge
    refine ⟨?_, ?_⟩
    · rw [if_neg hne0, hdeg]
      exact_mod_cast hdA
    · have hlc : (A + B).leadingCoeff = A.leadingCoeff + B.leadingCoeff := by
        rw [Polynomial.leadingCoeff, hdeg, hcoeff]
      show ((A + B).leadingCoeff : ℚ) = (A.leadingCoeff : ℚ) + (B.leadingCoeff : ℚ)
      rw [hlc]
      push_cast
      ring
  Full := fun _ => False
  hlift := by intro k hk; exact hk.elim

/-- Carrier at key degree two. -/
noncomputable def C₂ : SlotCarrier ℤ ℚ :=
  gradedCarrier 2 2 1 two_pos rfl one_le_two le_rfl

/-- Parent block: `F = (X² - 4)(X² - 1)`. -/
noncomputable def B₂ : BlockData C₂ where
  Φ := X ^ 2
  F := X ^ 4 - 5 * X ^ 2 + 4
  μ := 2
  hμ := by norm_num
  hΦ := monic_X_pow 2
  hΦdeg := natDegree_X_pow 2
  A := fun j => if j = 0 then 4 else if j = 1 then -5 else 0
  hdev := by
    simp [Finset.sum_range_succ]
    ring
  hdegA := by
    intro j hj
    rcases j with _ | _ | j
    · simp [C₂, gradedCarrier, Polynomial.natDegree_ofNat]
    · simp [C₂, gradedCarrier, Polynomial.natDegree_ofNat]
    · omega
  hkeyfree := by
    have h4 : (4 : FractionRing ℤ) ≠ 0 := by
      intro h
      have h0 : algebraMap ℤ (FractionRing ℤ) 4 = algebraMap ℤ (FractionRing ℤ) 0 := by
        rw [map_ofNat, map_zero, h]
      exact absurd (IsFractionRing.injective ℤ (FractionRing ℤ) h0) (by norm_num)
    refine ⟨C ((4 : FractionRing ℤ)⁻¹), -(C ((4 : FractionRing ℤ)⁻¹) * (X ^ 2 - 5)), ?_⟩
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_mul, Polynomial.map_X, Polynomial.map_ofNat]
    have hC : (C ((4 : FractionRing ℤ)⁻¹)) * (4 : (FractionRing ℤ)[X]) = 1 := by
      rw [show (4 : (FractionRing ℤ)[X]) = C (4 : FractionRing ℤ) from
          (map_ofNat (C : (FractionRing ℤ) →+* (FractionRing ℤ)[X]) 4).symm,
        ← C_mul, inv_mul_cancel₀ h4, C_1]
    convert hC using 1
    all_goals ring
  hA0 := by norm_num
  T := 0

/-- Recentered block with reducible key `X² - 4`. -/
noncomputable def B₂' : BlockData C₂ where
  Φ := X ^ 2 - 4
  F := X ^ 2 - 3
  μ := 1
  hμ := le_rfl
  hΦ := by
    have h := monic_X_pow_sub_C (4 : ℤ) (by norm_num : (2 : ℕ) ≠ 0)
    have e : (X ^ 2 - C (4 : ℤ)) = (X ^ 2 - 4 : ℤ[X]) := by rw [map_ofNat]
    rwa [e] at h
  hΦdeg := by
    show (X ^ 2 - 4 : ℤ[X]).natDegree = C₂.D
    have e : (X ^ 2 - 4 : ℤ[X]) = X ^ 2 - C (4 : ℤ) := by rw [map_ofNat]
    rw [e, natDegree_X_pow_sub_C]
    rfl
  A := fun _ => 1
  hdev := by
    simp
    ring
  hdegA := by
    intro j hj
    simp [C₂, gradedCarrier]
  hkeyfree := by
    refine ⟨1, -1, ?_⟩
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_ofNat]
    ring
  hA0 := one_ne_zero
  T := 0

lemma not_isUnit_linear (c : FractionRing ℤ) : ¬ IsUnit (X - C c) := by
  intro h
  have hdeg := natDegree_eq_zero_of_isUnit h
  simp at hdeg

/-- The unrestricted `MP1Carrier` is false at the concrete legal pair `(C₂,B₂)`. -/
theorem unrestricted_mp1_false : ¬ MP1Carrier.{0, 0, 0} C₂ B₂ := by
  intro h
  have hΛne : (4 : ℤ[X]) ≠ 0 := by norm_num
  have hΛdeg : (4 : ℤ[X]).natDegree < C₂.D := by
    show (4 : ℤ[X]).natDegree < 2
    simp [Polynomial.natDegree_ofNat]
  have hΦeq : B₂'.Φ = B₂.Φ - 4 := rfl
  have hdvd : B₂'.Φ ∣ B₂.F := by
    refine ⟨X ^ 2 - 1, ?_⟩
    show (X ^ 4 - 5 * X ^ 2 + 4 : ℤ[X]) = (X ^ 2 - 4) * (X ^ 2 - 1)
    ring
  obtain ⟨E⟩ := h 4 hΛne hΛdeg B₂' hΦeq hdvd
  have hfactor : B₂'.Φ.map (algebraMap ℤ (FractionRing ℤ)) =
      (X - C (2 : FractionRing ℤ)) * (X + C (2 : FractionRing ℤ)) := by
    show ((X ^ 2 - 4 : ℤ[X]).map (algebraMap ℤ (FractionRing ℤ))) = _
    have hC2 : C (2 : FractionRing ℤ) = (2 : (FractionRing ℤ)[X]) :=
      map_ofNat (C : (FractionRing ℤ) →+* (FractionRing ℤ)[X]) 2
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_ofNat, hC2]
    ring
  rcases E.hirr.isUnit_or_isUnit hfactor with hu | hu
  · exact not_isUnit_linear _ hu
  · have e : X + C (2 : FractionRing ℤ) = X - C (-(2 : FractionRing ℤ)) := by
      rw [map_neg, sub_neg_eq_add]
    rw [e] at hu
    exact not_isUnit_linear _ hu

end Uniformity.Density.MP1RProbe

end

/-! AXCHECK FOOTER — Lean core only. -/

#print axioms Uniformity.Density.MP1RProbe.gradedCarrier
#print axioms Uniformity.Density.MP1RProbe.MP1StepCore
#print axioms Uniformity.Density.MP1RProbe.CanonicalMP1StepExport
#print axioms Uniformity.Density.MP1RProbe.MP1CarrierLive
#print axioms Uniformity.Density.MP1RProbe.mp1CarrierLive_proved
#print axioms Uniformity.Density.MP1RProbe.mp1CarrierLive_of_unrestricted
#print axioms Uniformity.Density.MP1RProbe.C₂
#print axioms Uniformity.Density.MP1RProbe.B₂
#print axioms Uniformity.Density.MP1RProbe.B₂'
#print axioms Uniformity.Density.MP1RProbe.unrestricted_mp1_false
