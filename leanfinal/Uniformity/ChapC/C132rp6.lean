/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C132rp5
import Uniformity.ChapC.C132rp2
import Uniformity.ChapC.C130fg

/-!
# Uniformity.ChapC.C132rp6 — the μ₃ graded product assembly

**[M3-RP6, 2026-08-27]** (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6):
assemble RP5's coefficient convolution into the arbitrary-grade carry-twisted polynomial
identity, specialize it to the source-correct preceding-grade predicate, and bundle the
exact-grade product conjunct required by `FGMNSourceLaws.graded_mul`.

This is the numeral-level port of `C130rp4.s2GradedRes_mul_of_exact` and
`C130rp6.s2_graded_mul` to the μ₃ operator.  The plain statement is deliberately fenced by
`S2Mu3PrevGrade β' := 2 ∣ β'`; only the twisted identity is asserted at arbitrary grades.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132rp6

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C132nv1 Uniformity.Density.Tower.C132rp0
open Uniformity.Density.Tower.C132rp1 Uniformity.Density.Tower.C132rp2
open Uniformity.Density.Tower.C132rp4 Uniformity.Density.Tower.C132rp5

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 1 — polynomial assembly from RP5's coefficient laws -/

/-- The product-polynomial coefficient form: the coefficient after the carry shift equals
the corresponding coefficient of the product of the two graded residuals. -/
theorem s2Mu3GradedRes_mul_coeff {β β' : ℕ} {g z : Polynomial O}
    (hg : S2Mu3ExactGrade h2 hq β g) (hz : S2Mu3ExactGrade h2 hq β' z) (T : ℕ) :
    (s2Mu3GradedRes h2 hq (β + β') (g * z)).coeff (T + s2Mu3Carry β β')
      = (s2Mu3GradedRes h2 hq β g * s2Mu3GradedRes h2 hq β' z).coeff T := by
  rw [s2Mu3GradedRes_coeff, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, s2Mu3Coeff_mul h2 hq hg hz T]
  exact Finset.sum_congr rfl fun t _ => by
    rw [s2Mu3GradedRes_coeff, s2Mu3GradedRes_coeff]

/-- In the odd×odd carry genre, the coefficient below the twist is zero. -/
theorem s2Mu3GradedRes_mul_coeff_zero_of_odd {β β' : ℕ} {g z : Polynomial O}
    (hg : S2Mu3ExactGrade h2 hq β g) (hz : S2Mu3ExactGrade h2 hq β' z)
    (hβ : β % 2 = 1) (hβ' : β' % 2 = 1) :
    (s2Mu3GradedRes h2 hq (β + β') (g * z)).coeff 0 = 0 := by
  rw [s2Mu3GradedRes_coeff]
  exact s2Mu3Coeff_mul_zero_of_odd h2 hq hg hz hβ hβ'

/-- The plain coefficient identity when the second grade is in the preceding group. -/
theorem s2Mu3GradedRes_mul_coeff_of_prevGrade {β β' : ℕ} {g z : Polynomial O}
    (hg : S2Mu3ExactGrade h2 hq β g) (hz : S2Mu3ExactGrade h2 hq β' z)
    (hβ' : β' % 2 = 0) (T : ℕ) :
    (s2Mu3GradedRes h2 hq (β + β') (g * z)).coeff T
      = (s2Mu3GradedRes h2 hq β g * s2Mu3GradedRes h2 hq β' z).coeff T := by
  rw [s2Mu3GradedRes_coeff, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    s2Mu3Coeff_mul_of_prevGrade h2 hq hg hz hβ' T]
  exact Finset.sum_congr rfl fun t _ => by
    rw [s2Mu3GradedRes_coeff, s2Mu3GradedRes_coeff]

/-- The arbitrary-grade μ₃ product identity.  The carry twist is the repository's extension
of the published plain law; no `PrevGrade` premise is used here. -/
theorem s2Mu3GradedRes_mul_of_exact {β β' : ℕ} {g z : Polynomial O}
    (hg : S2Mu3ExactGrade h2 hq β g) (hz : S2Mu3ExactGrade h2 hq β' z) :
    s2Mu3GradedRes h2 hq (β + β') (g * z)
      = Polynomial.X ^ (β % 2 * (β' % 2))
        * (s2Mu3GradedRes h2 hq β g * s2Mu3GradedRes h2 hq β' z) := by
  rcases Nat.mod_two_eq_zero_or_one β with hpb | hpb
  · refine Polynomial.ext fun T => ?_
    rw [hpb, zero_mul, pow_zero, one_mul]
    have h := s2Mu3GradedRes_mul_coeff h2 hq hg hz T
    simp [s2Mu3Carry, hpb] at h
    exact h
  · rcases Nat.mod_two_eq_zero_or_one β' with hpb' | hpb'
    · refine Polynomial.ext fun T => ?_
      rw [hpb, hpb', mul_zero, pow_zero, one_mul]
      have h := s2Mu3GradedRes_mul_coeff h2 hq hg hz T
      simp [s2Mu3Carry, hpb'] at h
      exact h
    · refine Polynomial.ext fun T => ?_
      rw [hpb, hpb', mul_one, pow_one]
      match T with
      | 0 =>
        rw [Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul]
        exact s2Mu3GradedRes_mul_coeff_zero_of_odd h2 hq hg hz hpb hpb'
      | T + 1 =>
        rw [Polynomial.coeff_X_mul]
        have h := s2Mu3GradedRes_mul_coeff h2 hq hg hz T
        simp [s2Mu3Carry, hpb, hpb'] at h
        exact h

/-- The plain μ₃ product identity at an even second grade. -/
theorem s2Mu3GradedRes_mul_of_prevGrade {β β' : ℕ} {g z : Polynomial O}
    (hg : S2Mu3ExactGrade h2 hq β g) (hz : S2Mu3ExactGrade h2 hq β' z)
    (hβ' : β' % 2 = 0) :
    s2Mu3GradedRes h2 hq (β + β') (g * z)
      = s2Mu3GradedRes h2 hq β g * s2Mu3GradedRes h2 hq β' z := by
  refine Polynomial.ext fun T => ?_
  exact s2Mu3GradedRes_mul_coeff_of_prevGrade h2 hq hg hz hβ' T

/-! ## Part 2 — source-correct `PrevGrade` and exact-grade packaging -/

/-- The μ₃ preceding-group predicate in full-current-group cleared coordinates. -/
def S2Mu3PrevGrade (β : ℕ) : Prop := 2 ∣ β

/-- The consumable parity form of `S2Mu3PrevGrade`. -/
theorem S2Mu3PrevGrade_iff_mod (β : ℕ) : S2Mu3PrevGrade β ↔ β % 2 = 0 := by
  unfold S2Mu3PrevGrade
  omega

/-- The current `FGMNSourceLaws.graded_mul` target at μ₃: exact product grade bundled with
the plain residual identity, fenced by the restored preceding-grade premise. -/
theorem s2Mu3_graded_mul :
    ∀ β β' (g h : Polynomial O),
      S2Mu3ExactGrade h2 hq β g → S2Mu3ExactGrade h2 hq β' h →
      S2Mu3PrevGrade β' →
        S2Mu3ExactGrade h2 hq (β + β') (g * h) ∧
        s2Mu3GradedRes h2 hq (β + β') (g * h)
          = s2Mu3GradedRes h2 hq β g * s2Mu3GradedRes h2 hq β' h :=
  fun _ β' _ _ hg hh hprev =>
    ⟨S2Mu3ExactGrade_mul h2 hq hg hh,
      s2Mu3GradedRes_mul_of_prevGrade h2 hq hg hh
        ((S2Mu3PrevGrade_iff_mod β').mp hprev)⟩

/-- The arbitrary-grade twisted identity with the same exact-grade conjunct packaged. -/
theorem s2Mu3_graded_mul_twisted :
    ∀ β β' (g h : Polynomial O),
      S2Mu3ExactGrade h2 hq β g → S2Mu3ExactGrade h2 hq β' h →
        S2Mu3ExactGrade h2 hq (β + β') (g * h) ∧
        s2Mu3GradedRes h2 hq (β + β') (g * h)
          = Polynomial.X ^ (β % 2 * (β' % 2))
            * (s2Mu3GradedRes h2 hq β g * s2Mu3GradedRes h2 hq β' h) :=
  fun _ _ _ _ hg hh =>
    ⟨S2Mu3ExactGrade_mul h2 hq hg hh, s2Mu3GradedRes_mul_of_exact h2 hq hg hh⟩

/-! ## Part 3 — field-shape pin for the later source-record assembly -/

/-- If a μ₃ source record exposes the landed value, residual, and preceding-grade operators,
the theorem above fills its current `FGMNSourceLaws.graded_mul` field verbatim. -/
theorem s2Mu3_graded_mul_fills (K : KeyChain (s2DepthTwo h2 hq))
    (S : FGMNSourceData (s2DepthTwo h2 hq) K 2 1 21)
    (hval : S.nextValue = s2Hgt₃ h2 hq)
    (hres : S.gradedResidual = s2Mu3GradedRes h2 hq)
    (hprev : S.PrevGrade = S2Mu3PrevGrade) :
    ∀ β β' (g h : Polynomial O),
      S.ExactGrade β g → S.ExactGrade β' h → S.PrevGrade β' →
        S.ExactGrade (β + β') (g * h) ∧
        S.gradedResidual (β + β') (g * h)
          = S.gradedResidual β g * S.gradedResidual β' h := by
  intro β β' g h hg hh hp
  have hg' : S2Mu3ExactGrade h2 hq β g := by
    have hx : S.nextValue g = (β : WithTop ℤ) := hg
    rw [hval] at hx
    exact hx
  have hh' : S2Mu3ExactGrade h2 hq β' h := by
    have hx : S.nextValue h = (β' : WithTop ℤ) := hh
    rw [hval] at hx
    exact hx
  rw [hprev] at hp
  obtain ⟨hexact, hpoly⟩ := s2Mu3_graded_mul h2 hq β β' g h hg' hh' hp
  refine ⟨?_, ?_⟩
  · show S.nextValue (g * h) = ((β + β' : ℕ) : WithTop ℤ)
    rw [hval]
    exact hexact
  · rw [hres]
    exact hpoly

end S2

end Uniformity.Density.Tower.C132rp6

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132rp6.s2Mu3GradedRes_mul_coeff
#print axioms Uniformity.Density.Tower.C132rp6.s2Mu3GradedRes_mul_coeff_zero_of_odd
#print axioms Uniformity.Density.Tower.C132rp6.s2Mu3GradedRes_mul_coeff_of_prevGrade
#print axioms Uniformity.Density.Tower.C132rp6.s2Mu3GradedRes_mul_of_exact
#print axioms Uniformity.Density.Tower.C132rp6.s2Mu3GradedRes_mul_of_prevGrade
#print axioms Uniformity.Density.Tower.C132rp6.S2Mu3PrevGrade
#print axioms Uniformity.Density.Tower.C132rp6.S2Mu3PrevGrade_iff_mod
#print axioms Uniformity.Density.Tower.C132rp6.s2Mu3_graded_mul
#print axioms Uniformity.Density.Tower.C132rp6.s2Mu3_graded_mul_twisted
#print axioms Uniformity.Density.Tower.C132rp6.s2Mu3_graded_mul_fills

end AxCheck
