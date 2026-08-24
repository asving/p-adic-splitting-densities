/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C42

/-!
# Uniformity.ChapC.C131a — the two-index weight and its product law

**Chapter C, NODES C.131a′–c′** (`wtCoeff`, `WT`, `WT_add`, and `WT_mul`).  This is the
two-index coefficient-weight layer of
`docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md` §2.1–§2.2.

The outer coefficient index and inner scalar index remain separate throughout.  Thus every
use of the discrete valuation is applied to an element of `O`, never to a polynomial over
`O`.  Empty finite infima have value `⊤`, so the zero polynomial has weight `⊤`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C131a

open Polynomial IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ}
variable {hpin : npHgt Polynomial.X F.key
  (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)}

/-- The weight of the scalar coefficient at inner index `a` and outer index `b`. -/
noncomputable def wtCoeff (T : TowerDatum F H₀ hpin) (c : O) (a b : ℕ) : ℕ∞ :=
  (F.e₁ * T.e₂) • addVal O c +
    ((a * (T.e₂ * F.h) + b * T.u₂ : ℕ) : ℕ∞)

/-- The two-index weight of a polynomial in the outer variable with coefficients in `O[X]`. -/
noncomputable def WT (T : TowerDatum F H₀ hpin)
    (P : Polynomial (Polynomial O)) : ℕ∞ :=
  P.support.inf fun b =>
    (P.coeff b).support.inf fun a => wtCoeff T ((P.coeff b).coeff a) a b

/-- The empty two-index support has infinite weight. -/
@[simp] theorem WT_zero (T : TowerDatum F H₀ hpin) : WT T 0 = ⊤ := by
  simp [WT]

/-- `WT` is below the weight of every scalar coefficient selected by the two supports. -/
theorem WT_le_wtCoeff_of_mem (T : TowerDatum F H₀ hpin)
    {P : Polynomial (Polynomial O)} {a b : ℕ}
    (hb : b ∈ P.support) (ha : a ∈ (P.coeff b).support) :
    WT T P ≤ wtCoeff T ((P.coeff b).coeff a) a b := by
  exact le_trans (Finset.inf_le hb) (Finset.inf_le ha)

/-- A zero scalar coefficient has infinite weight.  Positivity of both ramification indices
is essential here: multiplication by zero would not preserve `⊤`. -/
@[simp] theorem wtCoeff_zero (T : TowerDatum F H₀ hpin) (a b : ℕ) :
    wtCoeff T (0 : O) a b = ⊤ := by
  have hpos : 0 < F.e₁ * T.e₂ := Nat.mul_pos F.he₁ T.he₂
  have hc : ((F.e₁ * T.e₂ : ℕ) : ℕ∞) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [wtCoeff, addVal_zero, nsmul_eq_mul, ENat.mul_top hc, top_add]

/-- Support-free form of the preceding projection: absent indices have zero coefficient and
hence infinite coefficient weight. -/
theorem WT_le_wtCoeff (T : TowerDatum F H₀ hpin)
    (P : Polynomial (Polynomial O)) (a b : ℕ) :
    WT T P ≤ wtCoeff T ((P.coeff b).coeff a) a b := by
  by_cases hb : b ∈ P.support
  · by_cases ha : a ∈ (P.coeff b).support
    · exact WT_le_wtCoeff_of_mem T hb ha
    · have hz : (P.coeff b).coeff a = 0 := not_ne_iff.mp (mt mem_support_iff.mpr ha)
      rw [hz, wtCoeff_zero]
      exact le_top
  · have hz : P.coeff b = 0 := not_ne_iff.mp (mt mem_support_iff.mpr hb)
    rw [hz, Polynomial.coeff_zero, wtCoeff_zero]
    exact le_top

/-- Pointwise ultrametricity for the two-index coefficient weight. -/
theorem min_wtCoeff_le_wtCoeff_add (T : TowerDatum F H₀ hpin)
    (x y : O) (a b : ℕ) :
    min (wtCoeff T x a b) (wtCoeff T y a b) ≤ wtCoeff T (x + y) a b := by
  have hv := IsDiscreteValuationRing.addVal_add (R := O) (a := x) (b := y)
  rcases le_total (addVal O x) (addVal O y) with hxy | hyx
  · have hvx : addVal O x ≤ addVal O (x + y) := by
      simpa [min_eq_left hxy] using hv
    unfold wtCoeff
    exact le_trans (min_le_left _ _)
      (add_le_add (nsmul_le_nsmul_right hvx (F.e₁ * T.e₂)) le_rfl)
  · have hvy : addVal O y ≤ addVal O (x + y) := by
      simpa [min_eq_right hyx] using hv
    unfold wtCoeff
    exact le_trans (min_le_right _ _)
      (add_le_add (nsmul_le_nsmul_right hvy (F.e₁ * T.e₂)) le_rfl)

/-- A common lower bound on fixed-index coefficient weights passes through a finite sum. -/
theorem le_wtCoeff_sum {ι : Type*} (T : TowerDatum F H₀ hpin)
    {s : Finset ι} {f : ι → O} {c : ℕ∞} {a b : ℕ}
    (h : ∀ i ∈ s, c ≤ wtCoeff T (f i) a b) :
    c ≤ wtCoeff T (∑ i ∈ s, f i) a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact le_trans (le_min (h i (Finset.mem_insert_self i s))
          (ih fun j hj => h j (Finset.mem_insert_of_mem hj)))
        (min_wtCoeff_le_wtCoeff_add T _ _ a b)

/-- **NODE C.131b′.** The two-index weight is ultrametric. -/
theorem WT_add (T : TowerDatum F H₀ hpin) (P Q : Polynomial (Polynomial O)) :
    min (WT T P) (WT T Q) ≤ WT T (P + Q) := by
  simp only [WT, Finset.le_inf_iff]
  intro b hb a ha
  rw [Polynomial.coeff_add, Polynomial.coeff_add]
  exact le_trans (min_le_min (WT_le_wtCoeff T P a b) (WT_le_wtCoeff T Q a b))
    (min_wtCoeff_le_wtCoeff_add T _ _ a b)

/-- Scalar multiplication adds weights when both polynomial indices add. -/
theorem wtCoeff_mul (T : TowerDatum F H₀ hpin) (x y : O) (a₁ a₂ b₁ b₂ : ℕ) :
    wtCoeff T (x * y) (a₁ + a₂) (b₁ + b₂) =
      wtCoeff T x a₁ b₁ + wtCoeff T y a₂ b₂ := by
  rw [wtCoeff, wtCoeff, wtCoeff, IsDiscreteValuationRing.addVal_mul, smul_add]
  push_cast
  ring

/-- **First convolution lemma (inner variable).**  A fixed outer pair contributes an inner
polynomial product whose every scalar coefficient lies above the sum of the two input
weights. -/
theorem WT_add_le_inner_convolution (T : TowerDatum F H₀ hpin)
    (P Q : Polynomial (Polynomial O)) (b₁ b₂ a : ℕ) :
    WT T P + WT T Q ≤
      wtCoeff T (((P.coeff b₁) * (Q.coeff b₂)).coeff a) a (b₁ + b₂) := by
  rw [Polynomial.coeff_mul]
  refine le_wtCoeff_sum T fun p hp => ?_
  have hpa : p.1 + p.2 = a := Finset.mem_antidiagonal.mp hp
  calc
    WT T P + WT T Q ≤
        wtCoeff T ((P.coeff b₁).coeff p.1) p.1 b₁ +
          wtCoeff T ((Q.coeff b₂).coeff p.2) p.2 b₂ :=
      add_le_add (WT_le_wtCoeff T P p.1 b₁) (WT_le_wtCoeff T Q p.2 b₂)
    _ = wtCoeff T ((P.coeff b₁).coeff p.1 * (Q.coeff b₂).coeff p.2)
          a (b₁ + b₂) := by
      rw [← hpa, wtCoeff_mul]

/-- **Second convolution lemma (outer variable).**  After summing the outer antidiagonal,
every scalar coefficient of the product remains above the sum of the input weights. -/
theorem WT_add_le_outer_convolution (T : TowerDatum F H₀ hpin)
    (P Q : Polynomial (Polynomial O)) (a b : ℕ) :
    WT T P + WT T Q ≤ wtCoeff T (((P * Q).coeff b).coeff a) a b := by
  rw [Polynomial.coeff_mul, Polynomial.finsetSum_coeff]
  refine le_wtCoeff_sum T fun p hp => ?_
  have hpb : p.1 + p.2 = b := Finset.mem_antidiagonal.mp hp
  simpa [hpb] using WT_add_le_inner_convolution T P Q p.1 p.2 a

/-- **NODE C.131c′.** Multiplication is superadditive for the two-index weight. -/
theorem WT_mul (T : TowerDatum F H₀ hpin) (P Q : Polynomial (Polynomial O)) :
    WT T P + WT T Q ≤ WT T (P * Q) := by
  simp only [WT, Finset.le_inf_iff]
  intro b hb a ha
  exact WT_add_le_outer_convolution T P Q a b

end Uniformity.Density.Tower.C131a

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C131a.wtCoeff
#print axioms Uniformity.Density.Tower.C131a.WT
#print axioms Uniformity.Density.Tower.C131a.WT_zero
#print axioms Uniformity.Density.Tower.C131a.WT_le_wtCoeff_of_mem
#print axioms Uniformity.Density.Tower.C131a.wtCoeff_zero
#print axioms Uniformity.Density.Tower.C131a.WT_le_wtCoeff
#print axioms Uniformity.Density.Tower.C131a.min_wtCoeff_le_wtCoeff_add
#print axioms Uniformity.Density.Tower.C131a.le_wtCoeff_sum
#print axioms Uniformity.Density.Tower.C131a.WT_add
#print axioms Uniformity.Density.Tower.C131a.wtCoeff_mul
#print axioms Uniformity.Density.Tower.C131a.WT_add_le_inner_convolution
#print axioms Uniformity.Density.Tower.C131a.WT_add_le_outer_convolution
#print axioms Uniformity.Density.Tower.C131a.WT_mul

end AxCheck
