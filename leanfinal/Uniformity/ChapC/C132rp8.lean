/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C132rp6
import Uniformity.ChapC.C132rp7

/-!
# Uniformity.ChapC.C132rp8 — the μ₃ normalized residual

**[M3-RP8, 2026-08-27]** (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6):
define the total μ₃ grade read, strip the initial `X`-power from the graded residual, and
prove the nonzero-constant, key-power, and universal multiplication laws.

This is the numeral-level port of `C130rp8`'s normalization and `C130rp9`'s product/order
argument.  The only product input is M3-RP6's arbitrary-grade carry-twisted identity; M3-RP7
supplies exact-grade nonvanishing.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132rp8

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130rp0
open Uniformity.Density.Tower.C130rp1
open Uniformity.Density.Tower.C130rp8
open Uniformity.Density.Tower.C132nv0 Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C132nv5 Uniformity.Density.Tower.C132rp0
open Uniformity.Density.Tower.C132rp1 Uniformity.Density.Tower.C132rp2
open Uniformity.Density.Tower.C132rp6 Uniformity.Density.Tower.C132rp7
open Uniformity.Density.Tower.C80

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## The total μ₃ grade and the initial-power strip -/

/-- The total cleared μ₃ grade; its value at zero is the harmless totalization `0`. -/
noncomputable def s2Mu3GradeOf (g : Polynomial O) : ℕ :=
  (dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2).toNat

/-- A nonzero polynomial lies at its extracted μ₃ grade. -/
theorem S2Mu3ExactGrade_s2Mu3GradeOf {g : Polynomial O} (hg : g ≠ 0) :
    S2Mu3ExactGrade h2 hq (s2Mu3GradeOf h2 hq g) g :=
  (S2Mu3ExactGrade_iff_dv2Supp h2 hq).mpr
    (ENat.coe_toNat
      (dv2Supp_ne_top_of_ne_zero ((s2Tower h2 hq).levelDatum h2) (s2Φ₂_monic h2 hq)
        (by rw [s2Φ₂_natDegree h2 hq]; norm_num) 21 2 hg)).symm

/-- The extracted grade agrees with every exact-grade witness. -/
theorem s2Mu3GradeOf_eq_of_exact {β : ℕ} {g : Polynomial O}
    (hg : S2Mu3ExactGrade h2 hq β g) : s2Mu3GradeOf h2 hq g = β := by
  unfold s2Mu3GradeOf
  rw [(S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp hg]
  exact ENat.toNat_coe β

/-- The total normalized μ₃ residual: strip the full initial `X`-power at the input's own
exact grade. -/
noncomputable def s2Mu3NormRes (g : Polynomial O) :
    Polynomial ((s2DepthTwo h2 hq).fld 2) :=
  Polynomial.divX^[(s2Mu3GradedRes h2 hq (s2Mu3GradeOf h2 hq g) g).natTrailingDegree]
    (s2Mu3GradedRes h2 hq (s2Mu3GradeOf h2 hq g) g)

/-- Caller-supplied exact-grade form of the normalized residual. -/
theorem s2Mu3NormRes_of_exact {β : ℕ} {g : Polynomial O}
    (hg : S2Mu3ExactGrade h2 hq β g) :
    s2Mu3NormRes h2 hq g =
      Polynomial.divX^[(s2Mu3GradedRes h2 hq β g).natTrailingDegree]
        (s2Mu3GradedRes h2 hq β g) := by
  unfold s2Mu3NormRes
  rw [s2Mu3GradeOf_eq_of_exact h2 hq hg]

/-- Coefficients of the strip are shifted coefficients of the graded residual. -/
theorem s2Mu3NormRes_coeff (g : Polynomial O) (t : ℕ) :
    (s2Mu3NormRes h2 hq g).coeff t =
      (s2Mu3GradedRes h2 hq (s2Mu3GradeOf h2 hq g) g).coeff
        (t + (s2Mu3GradedRes h2 hq (s2Mu3GradeOf h2 hq g) g).natTrailingDegree) := by
  unfold s2Mu3NormRes
  exact coeff_divX_iterate _ _ _

/-- The zero polynomial has zero normalized residual. -/
theorem s2Mu3NormRes_zero : s2Mu3NormRes h2 hq (0 : Polynomial O) = 0 := by
  unfold s2Mu3NormRes
  rw [s2Mu3GradedRes_zero h2 hq]
  simp

/-- Reconstruction after stripping the initial power. -/
theorem s2Mu3NormRes_mul_X_pow_of_exact {β : ℕ} {g : Polynomial O}
    (hg : S2Mu3ExactGrade h2 hq β g) :
    s2Mu3NormRes h2 hq g * Polynomial.X ^ (s2Mu3GradedRes h2 hq β g).natTrailingDegree
      = s2Mu3GradedRes h2 hq β g := by
  rw [s2Mu3NormRes_of_exact h2 hq hg]
  exact divX_iterate_mul_X_pow le_rfl

/-! ## Constant-term nonvanishing -/

private theorem old_key_natDegree_two :
    ((s2Frame h2 hq).key : Polynomial O).natDegree = 2 := by
  rw [key_eq h2 hq]
  exact s2Key_natDegree

private theorem s2GradedRes_coeff_eq_zero_of_pos {m t : ℕ} {A : Polynomial O}
    (hA : A.natDegree < 4) (ht : 0 < t) :
    (s2GradedRes h2 hq m A).coeff t = 0 := by
  rw [s2GradedRes_coeff]
  refine s2GradedCoeff_eq_zero_of_not_slotOnGrade h2 hq ?_
  intro hgate
  obtain ⟨m', hm', -⟩ := (s2SlotOnGrade_iff h2 hq).mp hgate
  have hdev : dev (s2Frame h2 hq).key A (m % 2 + 2 * t) = 0 :=
    dev_eq_zero_of_lt (s2Frame h2 hq).hmonic (s2Frame h2 hq).natDegree_key_pos A _
      (by rw [old_key_natDegree_two h2 hq]; omega)
  have htop : dvHgt (s2Frame h2 hq) A (m % 2 + 2 * t) = ⊤ := by
    rw [dvHgt, hdev]
    exact (s2Frame h2 hq).stageHeight_zero
  rw [htop] at hm'
  exact WithTop.top_ne_coe hm'

private theorem eval_one_s2GradedRes_eq_coeff_zero {m : ℕ} {A : Polynomial O}
    (hA : A.natDegree < 4) :
    Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2) (s2GradedRes h2 hq m A) =
      (s2GradedRes h2 hq m A).coeff 0 := by
  have hconst : s2GradedRes h2 hq m A =
      Polynomial.C ((s2GradedRes h2 hq m A).coeff 0) := by
    refine Polynomial.ext fun t => ?_
    match t with
    | 0 => simp
    | t + 1 =>
        rw [Polynomial.coeff_C, if_neg (Nat.succ_ne_zero t)]
        exact s2GradedRes_coeff_eq_zero_of_pos h2 hq hA (Nat.succ_pos t)
  calc
    Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2) (s2GradedRes h2 hq m A) =
        Polynomial.eval 1 (Polynomial.C ((s2GradedRes h2 hq m A).coeff 0)) :=
      congrArg _ hconst
    _ = (s2GradedRes h2 hq m A).coeff 0 := Polynomial.eval_C

/-- At every exact μ₃ grade the graded residual polynomial is nonzero. -/
theorem s2Mu3GradedRes_ne_zero_of_exact {β : ℕ} {g : Polynomial O}
    (hg : S2Mu3ExactGrade h2 hq β g) : s2Mu3GradedRes h2 hq β g ≠ 0 := by
  obtain ⟨s, hgate⟩ := exists_mu3SlotOnGrade_of_exact h2 hq hg
  let A := dev (s2DepthTwoKeyAt h2 hq 2) g s
  have hinner : S2ExactGrade h2 hq ((β - 21 * s) / 2) A :=
    s2Mu3SlotOnGrade_inner_exact h2 hq hgate
  have hdeg : A.natDegree < 4 := by
    rcases eq_or_ne A 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]
      norm_num
    · have h := Polynomial.natDegree_lt_natDegree h0
        (degree_dev_lt (s2Φ₂_monic h2 hq)
          (by rw [s2Φ₂_natDegree h2 hq]; norm_num) g s)
      rwa [s2Φ₂_natDegree h2 hq] at h
  have hcoeff := s2Mu3Coeff_slot h2 hq hgate
  rw [s2Mu3Eps_eq_one, one_mul, eval_one_s2GradedRes_eq_coeff_zero h2 hq hdeg] at hcoeff
  have hne : (s2GradedRes h2 hq ((β - 21 * s) / 2) A).coeff 0 ≠ 0 :=
    s2GradedRes_coeff_zero_ne_zero_of_exact h2 hq hinner hdeg
  intro hzero
  apply hne
  rw [← hcoeff, ← s2Mu3GradedRes_coeff, hzero, Polynomial.coeff_zero]

/-- The normalized residual of every nonzero input has nonzero constant coefficient. -/
theorem s2Mu3NormRes_coeff_zero_ne_zero {g : Polynomial O} (hg : g ≠ 0) :
    (s2Mu3NormRes h2 hq g).coeff 0 ≠ 0 := by
  have hne : s2Mu3GradedRes h2 hq (s2Mu3GradeOf h2 hq g) g ≠ 0 :=
    s2Mu3GradedRes_ne_zero_of_exact h2 hq (S2Mu3ExactGrade_s2Mu3GradeOf h2 hq hg)
  rw [s2Mu3NormRes_coeff, zero_add]
  exact fun h0 => hne (Polynomial.coeff_natTrailingDegree_eq_zero.mp h0)

/-- Polynomial-level nonvanishing of the normalized residual. -/
theorem s2Mu3NormRes_ne_zero {g : Polynomial O} (hg : g ≠ 0) :
    s2Mu3NormRes h2 hq g ≠ 0 :=
  fun h0 => s2Mu3NormRes_coeff_zero_ne_zero h2 hq hg (by rw [h0, Polynomial.coeff_zero])

/-! ## The trailing order and universal normalized multiplication -/

/-- The initial `X`-orders add, including the odd-by-odd carry. -/
theorem s2Mu3GradedRes_natTrailingDegree_mul {β β' : ℕ} {g z : Polynomial O}
    (hg : S2Mu3ExactGrade h2 hq β g) (hz : S2Mu3ExactGrade h2 hq β' z) :
    (s2Mu3GradedRes h2 hq (β + β') (g * z)).natTrailingDegree =
      (s2Mu3GradedRes h2 hq β g).natTrailingDegree +
        (s2Mu3GradedRes h2 hq β' z).natTrailingDegree + β % 2 * (β' % 2) := by
  have hgne : s2Mu3GradedRes h2 hq β g ≠ 0 :=
    s2Mu3GradedRes_ne_zero_of_exact h2 hq hg
  have hzne : s2Mu3GradedRes h2 hq β' z ≠ 0 :=
    s2Mu3GradedRes_ne_zero_of_exact h2 hq hz
  rw [s2Mu3GradedRes_mul_of_exact h2 hq hg hz,
    Polynomial.natTrailingDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero)
      (mul_ne_zero hgne hzne),
    Polynomial.natTrailingDegree_mul hgne hzne, Polynomial.natTrailingDegree_X_pow]
  omega

/-- Normalized multiplication at caller-supplied exact grades. -/
theorem s2Mu3NormRes_mul_of_exact {β β' : ℕ} {g z : Polynomial O}
    (hg : S2Mu3ExactGrade h2 hq β g) (hz : S2Mu3ExactGrade h2 hq β' z) :
    s2Mu3NormRes h2 hq (g * z) = s2Mu3NormRes h2 hq g * s2Mu3NormRes h2 hq z := by
  have hgz := S2Mu3ExactGrade_mul h2 hq hg hz
  have hntd := s2Mu3GradedRes_natTrailingDegree_mul h2 hq hg hz
  refine mul_right_cancel₀
    (pow_ne_zero ((s2Mu3GradedRes h2 hq (β + β') (g * z)).natTrailingDegree)
      Polynomial.X_ne_zero) ?_
  calc
    s2Mu3NormRes h2 hq (g * z) *
          Polynomial.X ^ (s2Mu3GradedRes h2 hq (β + β') (g * z)).natTrailingDegree
        = s2Mu3GradedRes h2 hq (β + β') (g * z) :=
          s2Mu3NormRes_mul_X_pow_of_exact h2 hq hgz
    _ = Polynomial.X ^ (β % 2 * (β' % 2)) *
          (s2Mu3GradedRes h2 hq β g * s2Mu3GradedRes h2 hq β' z) :=
          s2Mu3GradedRes_mul_of_exact h2 hq hg hz
    _ = Polynomial.X ^ (β % 2 * (β' % 2)) *
          ((s2Mu3NormRes h2 hq g *
              Polynomial.X ^ (s2Mu3GradedRes h2 hq β g).natTrailingDegree) *
            (s2Mu3NormRes h2 hq z *
              Polynomial.X ^ (s2Mu3GradedRes h2 hq β' z).natTrailingDegree)) := by
          rw [s2Mu3NormRes_mul_X_pow_of_exact h2 hq hg,
            s2Mu3NormRes_mul_X_pow_of_exact h2 hq hz]
    _ = (s2Mu3NormRes h2 hq g * s2Mu3NormRes h2 hq z) *
          Polynomial.X ^ ((s2Mu3GradedRes h2 hq β g).natTrailingDegree +
            (s2Mu3GradedRes h2 hq β' z).natTrailingDegree + β % 2 * (β' % 2)) := by
          ring
    _ = (s2Mu3NormRes h2 hq g * s2Mu3NormRes h2 hq z) *
          Polynomial.X ^ (s2Mu3GradedRes h2 hq (β + β') (g * z)).natTrailingDegree := by
          rw [hntd]

/-- The universal normalized μ₃ multiplication law, including both zero cases. -/
theorem s2Mu3NormRes_mul (g z : Polynomial O) :
    s2Mu3NormRes h2 hq (g * z) = s2Mu3NormRes h2 hq g * s2Mu3NormRes h2 hq z := by
  rcases eq_or_ne g 0 with rfl | hgne
  · rw [zero_mul, s2Mu3NormRes_zero h2 hq, zero_mul]
  rcases eq_or_ne z 0 with rfl | hzne
  · rw [mul_zero, s2Mu3NormRes_zero h2 hq, mul_zero]
  exact s2Mu3NormRes_mul_of_exact h2 hq
    (S2Mu3ExactGrade_s2Mu3GradeOf h2 hq hgne)
    (S2Mu3ExactGrade_s2Mu3GradeOf h2 hq hzne)

/-! ## One and the μ₃ key powers -/

/-- The constant polynomial `1` has exact μ₃ grade zero. -/
theorem S2Mu3ExactGrade_one : S2Mu3ExactGrade h2 hq 0 (1 : Polynomial O) := by
  unfold S2Mu3ExactGrade
  rw [s2Hgt₃_one_eq_zero]
  norm_num

/-- The full graded residual of `1` is `1`. -/
theorem s2Mu3GradedRes_one : s2Mu3GradedRes h2 hq 0 (1 : Polynomial O) = 1 := by
  refine Polynomial.ext fun t => ?_
  match t with
  | 0 =>
      rw [Polynomial.coeff_one_zero]
      exact s2Fld₂_eq_one_of_ne_zero h2 hq
        (s2Mu3GradedRes_coeff_zero_ne_zero_of_exact h2 hq
          (S2Mu3ExactGrade_one h2 hq) (by norm_num [Polynomial.natDegree_one]))
  | t + 1 =>
      rw [s2Mu3GradedRes_coeff, Polynomial.coeff_one]
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      exact s2Mu3Coeff_eq_zero_of_natDegree_lt h2 hq
        (by norm_num [Polynomial.natDegree_one])

/-- The normalized residual of `1` is `1`. -/
theorem s2Mu3NormRes_one : s2Mu3NormRes h2 hq (1 : Polynomial O) = 1 := by
  rw [s2Mu3NormRes_of_exact h2 hq (S2Mu3ExactGrade_one h2 hq),
    s2Mu3GradedRes_one h2 hq, Polynomial.natTrailingDegree_one]
  rfl

/-- The μ₃ key powers have their expected exact grades. -/
theorem S2Mu3ExactGrade_key_pow (k : ℕ) :
    S2Mu3ExactGrade h2 hq (21 * k) ((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ k) := by
  induction k with
  | zero =>
      rw [pow_zero, Nat.mul_zero]
      exact S2Mu3ExactGrade_one h2 hq
  | succ k ih =>
      rw [show 21 * (k + 1) = 21 * k + 21 by ring, pow_succ]
      exact S2Mu3ExactGrade_mul h2 hq ih (tooth_Φ₂ h2 hq)

/-- The graded residual of the μ₃ development key at grade `21` is `1`. -/
theorem s2Mu3GradedRes_key :
    s2Mu3GradedRes h2 hq 21 (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) = 1 := by
  refine Polynomial.ext fun t => ?_
  match t with
  | 0 =>
      rw [s2Mu3GradedRes_coeff, tooth_mu3Coeff_Φ₂ h2 hq, Polynomial.coeff_one_zero]
  | t + 1 =>
      rw [s2Mu3GradedRes_coeff, Polynomial.coeff_one]
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      refine s2Mu3Coeff_eq_zero_of_dv2Pin_top h2 hq ?_
      rw [dv2Pin, dev_eq_zero_of_lt (s2Φ₂_monic h2 hq)
        (by rw [s2Φ₂_natDegree h2 hq]; norm_num)]
      · exact Uniformity.Density.Tower.dv2Hgt_zero _
      · rw [s2Φ₂_natDegree h2 hq]
        norm_num

/-- The graded μ₃ residual of the `k`-th key power is the initial monomial
`X^(k/2)`; the odd-by-odd carry composes the floor. -/
theorem s2Mu3GradedRes_key_pow (k : ℕ) :
    s2Mu3GradedRes h2 hq (21 * k) ((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ k) =
      Polynomial.X ^ (k / 2) := by
  induction k with
  | zero =>
      rw [pow_zero, Nat.mul_zero, s2Mu3GradedRes_one h2 hq]
      norm_num
  | succ k ih =>
      have h := s2Mu3GradedRes_mul_of_exact h2 hq (S2Mu3ExactGrade_key_pow h2 hq k)
        (tooth_Φ₂ h2 hq)
      rw [ih, s2Mu3GradedRes_key h2 hq, mul_one, show (21 : ℕ) % 2 = 1 by norm_num,
        mul_one, show 21 * k % 2 = k % 2 by omega, ← pow_add] at h
      rw [show 21 * (k + 1) = 21 * k + 21 by ring, pow_succ, h]
      congr 1
      omega

/-- The normalized residual of the μ₃ development key is `1`. -/
theorem s2Mu3NormRes_key :
    s2Mu3NormRes h2 hq (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) = 1 := by
  rw [s2Mu3NormRes_of_exact h2 hq (tooth_Φ₂ h2 hq), s2Mu3GradedRes_key h2 hq,
    Polynomial.natTrailingDegree_one]
  rfl

/-- Every normalized μ₃ key power has residual `1`. -/
theorem s2Mu3NormRes_key_pow (k : ℕ) :
    s2Mu3NormRes h2 hq ((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ k) = 1 := by
  induction k with
  | zero => rw [pow_zero, s2Mu3NormRes_one h2 hq]
  | succ k ih =>
      rw [pow_succ, s2Mu3NormRes_mul h2 hq, ih, s2Mu3NormRes_key h2 hq, mul_one]

end S2

end Uniformity.Density.Tower.C132rp8

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132rp8.s2Mu3GradeOf
#print axioms Uniformity.Density.Tower.C132rp8.S2Mu3ExactGrade_s2Mu3GradeOf
#print axioms Uniformity.Density.Tower.C132rp8.s2Mu3NormRes
#print axioms Uniformity.Density.Tower.C132rp8.s2Mu3GradedRes_ne_zero_of_exact
#print axioms Uniformity.Density.Tower.C132rp8.s2Mu3NormRes_coeff_zero_ne_zero
#print axioms Uniformity.Density.Tower.C132rp8.s2Mu3GradedRes_natTrailingDegree_mul
#print axioms Uniformity.Density.Tower.C132rp8.s2Mu3NormRes_mul
#print axioms Uniformity.Density.Tower.C132rp8.s2Mu3GradedRes_key_pow
#print axioms Uniformity.Density.Tower.C132rp8.s2Mu3NormRes_key
#print axioms Uniformity.Density.Tower.C132rp8.s2Mu3NormRes_key_pow

end AxCheck
