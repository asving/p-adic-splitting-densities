/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B35b
import Uniformity.ChapC.C71
import Uniformity.ChapC.C131a

/-!
# Uniformity.ChapC.C131d — the key-side floor and the x-carry

**Chapter C, NODES C.131d′–e′** (`DV_GRADED_ENGINE_V2_2026-08-24.md` §2.3 and §5).

This file supplies the bridge from the frame field
`F.hpure : IsPure X F.key F.h F.e₁` to a lower bound at every scalar coefficient of the
key.  The second theorem clears that bound by an arbitrary natural factor `e₂`, in the form
consumed by the two-index weight of C.131a′.

The x-carry half C.131e′ uses C.131a′'s shared `WT` declaration; this file deliberately does
not introduce a competing weight definition.

Both declarations are proved from B.35b's `suppVal_of_pure` and `suppVal_le_weight`, B.15's
`npHgt_X`, and the fields of `KeyFrame`.  In particular the result covers coefficients above
the degree: their valuation is `⊤`, so no support-membership hypothesis is needed.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Polynomial IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower.C131a

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## C.131d′: the `hpure` bridge -/

/-- **C.131d′ / F4.** Every coefficient of the frame key lies on or above its pure side.
This is valid at arbitrary abscissae, including those outside the polynomial's support. -/
theorem key_coeff_side_floor (F : KeyFrame O π) (a : ℕ) :
    ((((F.e₁ * F.f₁) * F.h : ℕ) : ℕ∞)) ≤
      F.e₁ • IsDiscreteValuationRing.addVal O (F.key.coeff a) +
        (((a * F.h : ℕ) : ℕ∞)) := by
  have h := suppVal_le_weight Polynomial.monic_X (by simp) F.he₁ F.h F.key a
  rw [suppVal_of_pure (n := F.e₁ * F.f₁) Polynomial.monic_X (by simp) F.hmonic
    (by simp [F.hdeg]) F.hpure, npHgt_X] at h
  simpa [Nat.mul_comm] using h

/-- **C.131d′ / F5.** Clearing F4 by `e₂` gives the coefficient contribution in the
two-index weight: `D′e₂h ≤ e₁e₂ v(keyₐ) + ae₂h`. -/
theorem key_coeff_side_floor_cleared (F : KeyFrame O π) (e₂ a : ℕ) :
    ((((F.e₁ * F.f₁) * e₂ * F.h : ℕ) : ℕ∞)) ≤
      (F.e₁ * e₂) • IsDiscreteValuationRing.addVal O (F.key.coeff a) +
        (((a * (e₂ * F.h) : ℕ) : ℕ∞)) := by
  have h := nsmul_le_nsmul_right (key_coeff_side_floor F a) e₂
  calc
    ((((F.e₁ * F.f₁) * e₂ * F.h : ℕ) : ℕ∞)) =
        e₂ • ((((F.e₁ * F.f₁) * F.h : ℕ) : ℕ∞)) := by
          push_cast [nsmul_eq_mul]
          ring
    _ ≤ e₂ • (F.e₁ • IsDiscreteValuationRing.addVal O (F.key.coeff a) +
        (((a * F.h : ℕ) : ℕ∞))) := h
    _ = (F.e₁ * e₂) • IsDiscreteValuationRing.addVal O (F.key.coeff a) +
        (((a * (e₂ * F.h) : ℕ) : ℕ∞)) := by
          push_cast [nsmul_eq_mul]
          ring

/-! ## C.131e′: the x-carry -/

/-- **C.131e′.** The tail in `X^D′ = Y + (X^D′ - F.key)`, after an inner shift by `a₀`
and an outer shift by `b`, retains the cleared key-side floor.  The leading coefficient of the
key cancels, so every coefficient that remains is strictly below `D′` and is the negation of
the corresponding key coefficient. -/
theorem xCarry_tail_floor {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (a₀ b : ℕ) :
    ((((F.e₁ * F.f₁) * T.e₂ * F.h + a₀ * (T.e₂ * F.h) + b * T.u₂ : ℕ) : ℕ∞)) ≤
      WT T (Polynomial.C ((Polynomial.X ^ (F.e₁ * F.f₁) - F.key) *
        Polynomial.X ^ a₀) * Polynomial.X ^ b) := by
  classical
  unfold WT
  refine Finset.le_inf fun b' hb' => ?_
  have hb : b' = b := by
    rw [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mem_support_iff,
      Polynomial.coeff_monomial] at hb'
    split at hb'
    · exact ‹b = b'›.symm
    · exact False.elim (hb' rfl)
  subst b'
  rw [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial, if_pos rfl]
  refine Finset.le_inf fun a' ha' => ?_
  rw [Polynomial.mem_support_iff, Polynomial.coeff_mul_X_pow'] at ha'
  have ha₀ : a₀ ≤ a' := by
    by_contra hn
    rw [if_neg (Nat.not_le.mpr (Nat.lt_of_not_ge hn))] at ha'
    exact ha' rfl
  have htail : (Polynomial.X ^ (F.e₁ * F.f₁) - F.key).coeff (a' - a₀) ≠ 0 := by
    simpa [ha₀] using ha'
  have hd : a' - a₀ < F.e₁ * F.f₁ := by
    by_contra hn
    have hle : F.e₁ * F.f₁ ≤ a' - a₀ := Nat.le_of_not_gt hn
    rcases hle.eq_or_lt with heq | hlt
    · rw [← heq, Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_pos rfl,
        ← F.hdeg, F.hmonic.coeff_natDegree, sub_self] at htail
      exact htail rfl
    · have hk : F.key.coeff (a' - a₀) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [F.hdeg] using hlt)
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg hlt.ne', hk, sub_zero] at htail
      exact htail rfl
  have hc : (Polynomial.X ^ (F.e₁ * F.f₁) - F.key).coeff (a' - a₀) =
      -F.key.coeff (a' - a₀) := by
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg hd.ne, zero_sub]
  rw [Polynomial.coeff_mul_X_pow', if_pos ha₀, hc]
  unfold wtCoeff
  rw [AddValuation.map_neg]
  have hbase := key_coeff_side_floor_cleared F T.e₂ (a' - a₀)
  have hoff := add_le_add_right hbase
    ((((a₀ * (T.e₂ * F.h) + b * T.u₂ : ℕ) : ℕ∞)))
  have hl : ((((F.e₁ * F.f₁) * T.e₂ * F.h + a₀ * (T.e₂ * F.h) +
      b * T.u₂ : ℕ) : ℕ∞)) =
      (((a₀ * (T.e₂ * F.h) + b * T.u₂ : ℕ) : ℕ∞)) +
        ((((F.e₁ * F.f₁) * T.e₂ * F.h : ℕ) : ℕ∞)) := by
    push_cast
    ring
  have hr : (F.e₁ * T.e₂) • addVal O (F.key.coeff (a' - a₀)) +
      (((a' * (T.e₂ * F.h) + b * T.u₂ : ℕ) : ℕ∞)) =
      (((a₀ * (T.e₂ * F.h) + b * T.u₂ : ℕ) : ℕ∞)) +
        ((F.e₁ * T.e₂) • addVal O (F.key.coeff (a' - a₀)) +
          ((((a' - a₀) * (T.e₂ * F.h) : ℕ) : ℕ∞))) := by
    have hacast : (a' : ℕ∞) = ((a' - a₀ : ℕ) : ℕ∞) + (a₀ : ℕ∞) := by
      rw [← Nat.cast_add, Nat.sub_add_cancel ha₀]
    push_cast only [Nat.cast_add, Nat.cast_mul]
    rw [hacast, nsmul_eq_mul, Nat.cast_mul]
    ring
  rw [hl, hr]
  exact hoff

/-- The scalar price of the `Y` branch.  C.71's margin identity rewrites one outer step as the
old side price plus exactly `δ = T.margin`. -/
theorem xCarry_branch_wtCoeff_exact {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (a₀ b : ℕ) :
    wtCoeff T (1 : O) a₀ (b + 1) =
      (((a₀ * (T.e₂ * F.h) + b * T.u₂ +
        (T.e₂ * ((F.e₁ * F.f₁) * F.h) + T.margin) : ℕ) : ℕ∞)) := by
  have hle : T.e₂ * ((F.e₁ * F.f₁) * F.h) ≤ T.u₂ :=
    Nat.le_of_lt (by simpa [Nat.mul_assoc] using T.hfloor)
  have hm : T.e₂ * ((F.e₁ * F.f₁) * F.h) + T.margin = T.u₂ := by
    simpa only [TowerDatum.margin] using Nat.add_sub_of_le hle
  simp only [wtCoeff, addVal_one, smul_zero, zero_add]
  rw [hm]
  push_cast
  ring

/-- **C.131e′, exact `+δ` branch.** The `Y` branch is a singleton two-index support, so its
`WT` is exactly its coefficient weight, namely the prior side price plus `T.margin`. -/
theorem xCarry_branch_WT_exact {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (a₀ b : ℕ) :
    WT T (Polynomial.C (Polynomial.X ^ a₀) * Polynomial.X ^ (b + 1)) =
      (((a₀ * (T.e₂ * F.h) + b * T.u₂ +
        (T.e₂ * ((F.e₁ * F.f₁) * F.h) + T.margin) : ℕ) : ℕ∞)) := by
  rw [show WT T (Polynomial.C (Polynomial.X ^ a₀) * Polynomial.X ^ (b + 1)) =
      wtCoeff T (1 : O) a₀ (b + 1) by
    unfold WT
    rw [Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.support_monomial (b + 1) (pow_ne_zero _ Polynomial.X_ne_zero)]
    simp [Polynomial.coeff_monomial, wtCoeff]]
  exact xCarry_branch_wtCoeff_exact T a₀ b

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.key_coeff_side_floor
#print axioms Uniformity.Density.Tower.key_coeff_side_floor_cleared
#print axioms Uniformity.Density.Tower.xCarry_tail_floor
#print axioms Uniformity.Density.Tower.xCarry_branch_wtCoeff_exact
#print axioms Uniformity.Density.Tower.xCarry_branch_WT_exact

end AxCheck
