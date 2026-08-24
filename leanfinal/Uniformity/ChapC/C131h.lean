/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C131f

/-!
# Uniformity.ChapC.C131h — the monic-division ledger

**Chapter C, NODES C.131h′–j′**
(`docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md` §2.5 and §5).

This file proves both sides of the one-step monic-division ledger and then iterates them
structurally.  The proof follows mathlib's actual `divModByMonicAux` recursion: at each
step the new quotient monomial loses exactly the outer-key price, while multiplication by
the homogeneous key restores that price before subtraction from the current dividend.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C131h

open Polynomial IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C131a Uniformity.Density.Tower.C131f

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

/-! ## Pins for the canonical outer divisor -/

/-- The canonical outer divisor has degree at most its displayed top index. -/
theorem natDegree_K_T_le (T : TowerDatum F H₀ hpin) :
    (K_T T).natDegree ≤ T.e₂ * T.f₂ := by
  classical
  rw [K_T]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun b hb => ?_
  exact (Polynomial.natDegree_monomial_le _).trans
    (Nat.le_of_lt_succ (Finset.mem_range.mp hb))

/-- The displayed top coefficient of the canonical outer divisor is one. -/
theorem coeff_K_T_top (T : TowerDatum F H₀ hpin) :
    (K_T T).coeff (T.e₂ * T.f₂) = 1 := by
  rw [coeff_K_T T le_rfl, composedKey_top_digit]

/-- The canonical outer divisor is monic. -/
theorem monic_K_T (T : TowerDatum F H₀ hpin) : (K_T T).Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ (natDegree_K_T_le T) (coeff_K_T_top T)

/-- Its outer degree is the advertised product `e₂ f₂`. -/
theorem natDegree_K_T (T : TowerDatum F H₀ hpin) :
    (K_T T).natDegree = T.e₂ * T.f₂ := by
  exact le_antisymm (natDegree_K_T_le T)
    (Polynomial.le_natDegree_of_ne_zero (by rw [coeff_K_T_top]; exact one_ne_zero))

/-! ## Weight bookkeeping for one division step -/

/-- Negating a scalar coefficient does not change its weight. -/
@[simp] theorem wtCoeff_neg (T : TowerDatum F H₀ hpin) (c : O) (a b : ℕ) :
    wtCoeff T (-c) a b = wtCoeff T c a b := by
  simp [wtCoeff]

/-- Negating a two-variable polynomial does not change its weight. -/
@[simp] theorem WT_neg (T : TowerDatum F H₀ hpin) (P : Polynomial (Polynomial O)) :
    WT T (-P) = WT T P := by
  classical
  simp only [WT, Polynomial.support_neg, Polynomial.coeff_neg, Polynomial.support_neg,
    Polynomial.coeff_neg, wtCoeff_neg]

/-- Shifting the outer index by the degree of `K_T` adds exactly `E₂`. -/
theorem wtCoeff_outer_key_shift (T : TowerDatum F H₀ hpin) (c : O) (a b : ℕ) :
    wtCoeff T c a (b + T.e₂ * T.f₂) = wtCoeff T c a b + (T.E₂ : ℕ∞) := by
  unfold wtCoeff TowerDatum.E₂
  push_cast
  ring

/-- The quotient monomial selected by one long-division step has the subtracted floor. -/
theorem leadingTerm_floor (T : TowerDatum F H₀ hpin) (P : Polynomial (Polynomial O))
    (w : ℕ) (hP : (w : ℕ∞) ≤ WT T P)
    (hdeg : (K_T T).degree ≤ P.degree) :
    (((w - T.E₂ : ℕ) : ℕ∞)) ≤ WT T
      (Polynomial.C P.leadingCoeff *
        Polynomial.X ^ (P.natDegree - (K_T T).natDegree)) := by
  classical
  have hnat : (K_T T).natDegree ≤ P.natDegree :=
    Polynomial.natDegree_le_natDegree hdeg
  simp only [WT, Finset.le_inf_iff]
  intro b hb a ha
  have hbne :
      (Polynomial.C P.leadingCoeff *
        Polynomial.X ^ (P.natDegree - (K_T T).natDegree)).coeff b ≠ 0 :=
    Polynomial.mem_support_iff.mp hb
  have hbeq : b = P.natDegree - (K_T T).natDegree := by
    have hx : b = P.natDegree - (K_T T).natDegree ∧ P ≠ 0 := by
      simpa [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] using hbne
    exact hx.1
  subst b
  have hcoeff :
      (Polynomial.C P.leadingCoeff *
        Polynomial.X ^ (P.natDegree - (K_T T).natDegree)).coeff
          (P.natDegree - (K_T T).natDegree) = P.leadingCoeff := by simp
  rw [hcoeff] at ha ⊢
  have hpoint := le_trans hP (WT_le_wtCoeff T P a P.natDegree)
  rw [Polynomial.coeff_natDegree] at hpoint
  rw [natDegree_K_T T]
  have hidx : P.natDegree - T.e₂ * T.f₂ + T.e₂ * T.f₂ = P.natDegree :=
    Nat.sub_add_cancel (by simpa [natDegree_K_T T] using hnat)
  have hshift := wtCoeff_outer_key_shift T (P.leadingCoeff.coeff a) a
    (P.natDegree - T.e₂ * T.f₂)
  rw [hidx] at hshift
  rw [ENat.coe_sub, tsub_le_iff_left]
  simpa [hshift, add_comm] using hpoint

/-- Both bounds, proved simultaneously along mathlib's well-founded long-division
recursion.  Keeping the pair together is what makes the remainder half available: the
recursive dividend retains the old floor while the quotient monomial retains the
subtracted floor. -/
theorem divModByMonicAux_floor (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (w : ℕ) :
    ∀ P : Polynomial (Polynomial O), (w : ℕ∞) ≤ WT T P →
      (((w - T.E₂ : ℕ) : ℕ∞) ≤
          WT T (Polynomial.divModByMonicAux P (monic_K_T T)).1) ∧
        ((w : ℕ∞) ≤ WT T (Polynomial.divModByMonicAux P (monic_K_T T)).2)
  | P, hP => by
      classical
      unfold Polynomial.divModByMonicAux
      dsimp only
      split
      next hstep =>
        let z : Polynomial (Polynomial O) :=
          Polynomial.C P.leadingCoeff *
            Polynomial.X ^ (P.natDegree - (K_T T).natDegree)
        let P' : Polynomial (Polynomial O) := P - K_T T * z
        have hw_nat : w ≤ T.E₂ + (w - T.E₂) := by omega
        have hw : (w : ℕ∞) ≤ (T.E₂ : ℕ∞) + ((w - T.E₂ : ℕ) : ℕ∞) := by
          exact_mod_cast hw_nat
        have hz : ((w - T.E₂ : ℕ) : ℕ∞) ≤ WT T z := by
          exact leadingTerm_floor T P w hP hstep.1
        have hkz : (w : ℕ∞) ≤ WT T (K_T T * z) := by
          refine le_trans hw (le_trans ?_ (WT_mul T (K_T T) z))
          rw [WT_K_T T hπ]
          exact add_le_add le_rfl hz
        have hP' : (w : ℕ∞) ≤ WT T P' := by
          have hadd := WT_add T P (-(K_T T * z))
          rw [WT_neg] at hadd
          exact le_trans (le_min hP hkz) (by simpa [P', sub_eq_add_neg] using hadd)
        have ih := divModByMonicAux_floor T hπ w P' hP'
        change ((w - T.E₂ : ℕ) : ℕ∞) ≤
            WT T (z + (Polynomial.divModByMonicAux P' (monic_K_T T)).1) ∧
          (w : ℕ∞) ≤ WT T (Polynomial.divModByMonicAux P' (monic_K_T T)).2
        refine ⟨?_, ih.2⟩
        exact le_trans (le_min hz ih.1) (WT_add T z _)
      next hstep =>
        exact ⟨by simp, hP⟩
  termination_by P => P
  decreasing_by
    exact Polynomial.div_wf_lemma (by assumption) (monic_K_T T)

/-- **NODE C.131h′ (F6).** One monic-division quotient step loses at most the
homogeneous outer-key price `E₂`. -/
theorem WT_divByMonic_ge_sub (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    (w : ℕ) (P : Polynomial (Polynomial O)) (hP : (w : ℕ∞) ≤ WT T P) :
    ((w - T.E₂ : ℕ) : ℕ∞) ≤ WT T (P /ₘ K_T T) := by
  unfold Polynomial.divByMonic
  rw [dif_pos (monic_K_T T)]
  exact (divModByMonicAux_floor T hπ w P hP).1

/-- **NODE C.131i′ (F7).** The remainder side of one monic-division step retains the
entire incoming floor. -/
theorem WT_modByMonic_ge (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    (w : ℕ) (P : Polynomial (Polynomial O)) (hP : (w : ℕ∞) ≤ WT T P) :
    (w : ℕ∞) ≤ WT T (P %ₘ K_T T) := by
  unfold Polynomial.modByMonic
  rw [dif_pos (monic_K_T T)]
  exact (divModByMonicAux_floor T hπ w P hP).2

/-! ## C.131j′ — structural iteration -/

/-- The structural quotient tower.  Recursion is on the syntactic depth, independently of
any degree argument. -/
noncomputable def quotIter (K P : Polynomial (Polynomial O)) : ℕ →
    Polynomial (Polynomial O)
  | 0 => P
  | j + 1 => (quotIter K P j) /ₘ K

/-- The digit at depth `j` is the remainder of the corresponding structural quotient. -/
noncomputable def quotDigit (K P : Polynomial (Polynomial O)) (j : ℕ) :
    Polynomial (Polynomial O) :=
  (quotIter K P j) %ₘ K

/-- The quotient half of the iterated ledger. -/
theorem quotIter_floor (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    (P : Polynomial (Polynomial O)) (μ : ℕ)
    (hP : ((μ * T.E₂ : ℕ) : ℕ∞) ≤ WT T P) :
    ∀ j, j ≤ μ →
      (((μ - j) * T.E₂ : ℕ) : ℕ∞) ≤ WT T (quotIter (K_T T) P j)
  | 0, _ => by simpa [quotIter] using hP
  | j + 1, hj => by
      have hj' : j ≤ μ := le_trans (Nat.le_succ j) hj
      have ih := quotIter_floor T hπ P μ hP j hj'
      have hstep := WT_divByMonic_ge_sub T hπ ((μ - j) * T.E₂)
        (quotIter (K_T T) P j) ih
      have hjlt : j < μ := Nat.lt_of_succ_le hj
      have hcount : μ - j = (μ - (j + 1)) + 1 := by omega
      have harith : (μ - j) * T.E₂ - T.E₂ = (μ - (j + 1)) * T.E₂ := by
        rw [hcount, Nat.add_mul, one_mul, Nat.add_sub_cancel]
      simpa [quotIter, harith] using hstep

/-- **NODE C.131j′ (F8).** Every structural quotient and its digit retain the unpaid
multiple of the outer-key price. -/
theorem division_ledger (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    (P : Polynomial (Polynomial O)) (μ j : ℕ) (hj : j ≤ μ)
    (hP : ((μ * T.E₂ : ℕ) : ℕ∞) ≤ WT T P) :
    ((((μ - j) * T.E₂ : ℕ) : ℕ∞) ≤ WT T (quotIter (K_T T) P j)) ∧
      ((((μ - j) * T.E₂ : ℕ) : ℕ∞) ≤ WT T (quotDigit (K_T T) P j)) := by
  have hq := quotIter_floor T hπ P μ hP j hj
  refine ⟨hq, ?_⟩
  unfold quotDigit
  exact WT_modByMonic_ge T hπ ((μ - j) * T.E₂) _ hq

end Uniformity.Density.Tower.C131h

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C131h.natDegree_K_T_le
#print axioms Uniformity.Density.Tower.C131h.coeff_K_T_top
#print axioms Uniformity.Density.Tower.C131h.monic_K_T
#print axioms Uniformity.Density.Tower.C131h.natDegree_K_T
#print axioms Uniformity.Density.Tower.C131h.wtCoeff_neg
#print axioms Uniformity.Density.Tower.C131h.WT_neg
#print axioms Uniformity.Density.Tower.C131h.wtCoeff_outer_key_shift
#print axioms Uniformity.Density.Tower.C131h.leadingTerm_floor
#print axioms Uniformity.Density.Tower.C131h.divModByMonicAux_floor
#print axioms Uniformity.Density.Tower.C131h.WT_divByMonic_ge_sub
#print axioms Uniformity.Density.Tower.C131h.WT_modByMonic_ge
#print axioms Uniformity.Density.Tower.C131h.quotIter
#print axioms Uniformity.Density.Tower.C131h.quotDigit
#print axioms Uniformity.Density.Tower.C131h.quotIter_floor
#print axioms Uniformity.Density.Tower.C131h.division_ledger

end AxCheck
