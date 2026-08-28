/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C136l2e3
import Uniformity.ChapC.C136d1
import Uniformity.ChapC.C132rp5

/-!
# Uniformity.ChapC.C136l2e4 — fixed-grade read audit and D3-10

This file audits L2E-09's proposed normalized fixed-grade `hconv` law and closes the
concrete S2 μ₄ coefficient convolution (D3-10) through the landed level-3 valuation
mirror.  The distinction between the absolute fixed-grade read and the own-height
normalized read is kept explicit.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C136l2e4

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130nv2
open Uniformity.Density.Tower.C132nv0 Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C132nv2
open Uniformity.Density.Tower.C132rp0 Uniformity.Density.Tower.C132rp1
open Uniformity.Density.Tower.C132rp2 Uniformity.Density.Tower.C132rp3
open Uniformity.Density.Tower.C132rp5 Uniformity.Density.Tower.C132rp8
open Uniformity.Density.Tower.C132rp10b
open Uniformity.Density.Tower.C136d0 Uniformity.Density.Tower.C136d1
open Uniformity.Density.Tower.C136d3ad
open Uniformity.Density.Tower.C136l2e0 Uniformity.Density.Tower.C136l2e1
open Uniformity.Density.Tower.C136l2e2 Uniformity.Density.Tower.C136l2e3
open Uniformity.Density.Tower.C80

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

private theorem coe_le_add_of_le {a b : ℕ} {x y : ℕ∞}
    (hx : (a : ℕ∞) ≤ x) (hy : (b : ℕ∞) ≤ y) : ((a + b : ℕ) : ℕ∞) ≤ x + y := by
  push_cast
  exact add_le_add hx hy

private theorem coe_lt_add_of_lt_of_le {a b : ℕ} {x y : ℕ∞}
    (hx : (a : ℕ∞) < x) (hy : (b : ℕ∞) ≤ y) : ((a + b : ℕ) : ℕ∞) < x + y := by
  rcases eq_or_ne x ⊤ with rfl | hx'
  · rw [top_add]
    exact lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self (a + b))) le_top
  obtain ⟨u, hu⟩ := ENat.ne_top_iff_exists.1 hx'
  rcases eq_or_ne y ⊤ with rfl | hy'
  · rw [add_top]
    exact lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self (a + b))) le_top
  obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.1 hy'
  rw [← hu] at hx ⊢
  rw [← hv] at hy ⊢
  have h1 : a < u := by exact_mod_cast hx
  have h2' : b ≤ v := by exact_mod_cast hy
  calc
    ((a + b : ℕ) : ℕ∞) < ((u + v : ℕ) : ℕ∞) := Nat.cast_lt.mpr (by omega)
    _ = (u : ℕ∞) + (v : ℕ∞) := by push_cast; rfl

private theorem s2_dv2Supp_mul_local {g z : Polynomial O} (hg : g ≠ 0) (hz : z ≠ 0) :
    dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) (g * z) 21 2
      = dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2
        + dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) z 21 2 := by
  obtain ⟨Hg, hHg⟩ := exists_dv2SideMin_height ((s2Tower h2 hq).levelDatum h2) g 21 2
    (C132nv6.s2_dv2SideSet_nonempty_at_21 h2 hq hg)
  obtain ⟨Hz, hHz⟩ := exists_dv2SideMin_height ((s2Tower h2 hq).levelDatum h2) z 21 2
    (C132nv6.s2_dv2SideSet_nonempty_at_21 h2 hq hz)
  exact C132nv4.s2_dv2Supp_mul_at_21 h2 hq
    (C132nv6.s2_dv2SideSet_nonempty_at_21 h2 hq hg)
    (C132nv6.s2_dv2SideSet_nonempty_at_21 h2 hq hz) hHg hHz

private theorem s2_dv2Supp_mul_all_local (g z : Polynomial O) :
    dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) (g * z) 21 2
      = dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2
        + dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) z 21 2 := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [zero_mul, dv2Supp_zero_eq_top ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) 21 (by norm_num), top_add]
  rcases eq_or_ne z 0 with rfl | hz
  · rw [mul_zero, dv2Supp_zero_eq_top ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) 21 (by norm_num), add_top]
  exact s2_dv2Supp_mul_local h2 hq hg hz

private theorem le_dv2Supp_finsetSum {ι : Type*} (s : Finset ι) (f : ι → Polynomial O)
    {k : ℕ∞} (hf : ∀ i ∈ s, k ≤ dv2Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) (f i) 21 2) :
    k ≤ dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2)
      (∑ i ∈ s, f i) 21 2 := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      rw [Finset.sum_empty, dv2Supp_zero_eq_top ((s2Tower h2 hq).levelDatum h2)
        (s2DepthTwoKeyAt h2 hq 2) 21 (by norm_num)]
      exact le_top
  | cons a t hat ih =>
      rw [Finset.sum_cons]
      exact le_trans (le_min (hf a (Finset.mem_cons_self a t))
          (ih fun i hi => hf i (Finset.mem_cons.2 (Or.inr hi))))
        (min_dv2Supp_le_dv2Supp_add ((s2Tower h2 hq).levelDatum h2)
          (s2Φ₂_monic h2 hq) (by rw [s2Φ₂_natDegree h2 hq]; norm_num)
          (by norm_num) _ _)

theorem s2Mu3GradedRes_finsetSum_of_le {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial O) {m : ℕ}
    (hf : ∀ i ∈ s, (m : ℕ∞) ≤ dv2Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) (f i) 21 2) :
    s2Mu3GradedRes h2 hq m (∑ i ∈ s, f i)
      = ∑ i ∈ s, s2Mu3GradedRes h2 hq m (f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact s2Mu3GradedRes_zero h2 hq m
  | cons a t hat ih =>
      rw [Finset.sum_cons, Finset.sum_cons,
        C132rp3.s2Mu3GradedRes_add_of_le h2 hq (hf a (Finset.mem_cons_self a t))
          (le_dv2Supp_finsetSum h2 hq t f
            fun i hi => hf i (Finset.mem_cons.2 (Or.inr hi))),
        ih fun i hi => hf i (Finset.mem_cons.2 (Or.inr hi))]

theorem eval_one_mu3GradedRes_g8_mul {m : ℕ} (Q : Polynomial O)
    (hm : (m : ℕ∞) ≤ dv2Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) (g8 h2 hq * Q) 21 2) :
    Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
      (s2Mu3GradedRes h2 hq m (g8 h2 hq * Q)) = 0 := by
  rcases lt_or_eq_of_le hm with hlt | heq
  · rw [s2Mu3GradedRes_zero_of_above h2 hq
      ((S2Mu3AboveGrade_iff_dv2Supp h2 hq).mpr hlt), Polynomial.eval_zero]
  · have hex : S2Mu3ExactGrade h2 hq m (g8 h2 hq * Q) :=
      (S2Mu3ExactGrade_iff_dv2Supp h2 hq).mpr heq.symm
    rw [← s2Mu3NormRes_mul_X_pow_of_exact h2 hq hex, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one,
      s2Mu3NormRes_mul h2 hq, Polynomial.eval_mul, s2Mu3NormRes_g8 h2 hq,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
      C130rp2.tooth_char_two h2 hq, zero_mul]

theorem eval_one_mu3GradedRes_modBy_g8 {A B : Polynomial O}
    (hA : A.natDegree < (g8 h2 hq).natDegree)
    (hB : B.natDegree < (g8 h2 hq).natDegree) {m : ℕ}
    (hm : (m : ℕ∞) ≤ dv2Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) A 21 2
        + dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) B 21 2) :
    Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
        (s2Mu3GradedRes h2 hq m ((A * B) %ₘ g8 h2 hq))
      = Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
          (s2Mu3GradedRes h2 hq m (A * B)) := by
  let hmul : ∀ ⦃g z : Polynomial O⦄, g ≠ 0 → z ≠ 0 →
      dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) (g * z) 21 2
        = dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2
          + dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) z 21 2 :=
    fun _ _ hg hz => s2_dv2Supp_mul_local h2 hq hg hz
  have hmodfloor : (m : ℕ∞) ≤ dv2Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) ((A * B) %ₘ g8 h2 hq) 21 2 := by
    rw [C136d3ad.dv2Supp_mul_modByKey_eq ((s2Tower h2 hq).levelDatum h2)
      (s2Φ₂_monic h2 hq) (by rw [s2Φ₂_natDegree h2 hq]; norm_num)
      (by norm_num) hmul (s2_isMu3Key_g8 h2 hq) hA hB]
    exact hm
  have hquotfloor : (m : ℕ∞) ≤ dv2Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) (g8 h2 hq * ((A * B) /ₘ g8 h2 hq)) 21 2 := by
    rw [s2_dv2Supp_mul_all_local h2 hq]
    exact hm.trans (C136d3ad.dv2Supp_add_le_key_quot_add
      ((s2Tower h2 hq).levelDatum h2) (s2Φ₂_monic h2 hq)
      (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num) hmul
      (s2_isMu3Key_g8 h2 hq) hA hB)
  conv_rhs => rw [← Polynomial.modByMonic_add_div (A * B) (g8 h2 hq)]
  rw [C132rp3.s2Mu3GradedRes_add_of_le h2 hq hmodfloor hquotfloor,
    Polynomial.eval_add, eval_one_mu3GradedRes_g8_mul h2 hq _ hquotfloor, add_zero]

theorem eval_one_mu3GradedRes_mul_of_exact {m₁ m₂ : ℕ} {A B : Polynomial O}
    (hA : S2Mu3ExactGrade h2 hq m₁ A) (hB : S2Mu3ExactGrade h2 hq m₂ B) :
    Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
        (s2Mu3GradedRes h2 hq (m₁ + m₂) (A * B))
      = Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2) (s2Mu3GradedRes h2 hq m₁ A)
        * Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
            (s2Mu3GradedRes h2 hq m₂ B) := by
  have hAB : S2Mu3ExactGrade h2 hq (m₁ + m₂) (A * B) :=
    S2Mu3ExactGrade_mul h2 hq hA hB
  rw [← s2Mu3NormRes_mul_X_pow_of_exact h2 hq hAB,
    ← s2Mu3NormRes_mul_X_pow_of_exact h2 hq hA,
    ← s2Mu3NormRes_mul_X_pow_of_exact h2 hq hB, s2Mu3NormRes_mul h2 hq]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one]

theorem eval_one_mu3GradedRes_mul_of_le {m₁ m₂ : ℕ} {A B : Polynomial O}
    (hA : (m₁ : ℕ∞) ≤ dv2Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) A 21 2)
    (hB : (m₂ : ℕ∞) ≤ dv2Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) B 21 2) :
    Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
        (s2Mu3GradedRes h2 hq (m₁ + m₂) (A * B))
      = Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2) (s2Mu3GradedRes h2 hq m₁ A)
        * Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
            (s2Mu3GradedRes h2 hq m₂ B) := by
  rcases lt_or_eq_of_le hA with hAlt | hAeq
  · have habove : ((m₁ + m₂ : ℕ) : ℕ∞) < dv2Supp ((s2Tower h2 hq).levelDatum h2)
        (s2DepthTwoKeyAt h2 hq 2) (A * B) 21 2 := by
      rw [s2_dv2Supp_mul_all_local h2 hq]
      exact coe_lt_add_of_lt_of_le hAlt hB
    rw [s2Mu3GradedRes_zero_of_above h2 hq
      ((S2Mu3AboveGrade_iff_dv2Supp h2 hq).mpr habove),
      s2Mu3GradedRes_zero_of_above h2 hq
        ((S2Mu3AboveGrade_iff_dv2Supp h2 hq).mpr hAlt), Polynomial.eval_zero, zero_mul]
  rcases lt_or_eq_of_le hB with hBlt | hBeq
  · have habove : ((m₁ + m₂ : ℕ) : ℕ∞) < dv2Supp ((s2Tower h2 hq).levelDatum h2)
        (s2DepthTwoKeyAt h2 hq 2) (A * B) 21 2 := by
      rw [s2_dv2Supp_mul_all_local h2 hq,
        add_comm (dv2Supp ((s2Tower h2 hq).levelDatum h2)
          (s2DepthTwoKeyAt h2 hq 2) A 21 2)]
      have h := coe_lt_add_of_lt_of_le hBlt hA
      rwa [Nat.add_comm m₂ m₁] at h
    rw [s2Mu3GradedRes_zero_of_above h2 hq
      ((S2Mu3AboveGrade_iff_dv2Supp h2 hq).mpr habove),
      s2Mu3GradedRes_zero_of_above h2 hq
        ((S2Mu3AboveGrade_iff_dv2Supp h2 hq).mpr hBlt), Polynomial.eval_zero, mul_zero]
  · exact eval_one_mu3GradedRes_mul_of_exact h2 hq
      ((S2Mu3ExactGrade_iff_dv2Supp h2 hq).mpr hAeq.symm)
      ((S2Mu3ExactGrade_iff_dv2Supp h2 hq).mpr hBeq.symm)

private theorem ceil_le_dv2Supp_dev_g8 {β : ℕ} {f : Polynomial O} (j : ℕ)
    (hβ : (β : ℕ∞) ≤ dv3Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) f 85 2) :
    (((β - 85 * j + 1) / 2 : ℕ) : ℕ∞)
      ≤ dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2)
          (dev (g8 h2 hq) f j) 21 2 := by
  have hterm := hβ.trans (C136d0.dv3Supp_le_term ((s2Tower h2 hq).levelDatum h2)
    (s2g8_monic h2 hq) (by rw [s2g8_natDegree h2 hq]; norm_num) 21
    (by norm_num) f 85 (by norm_num) j)
  rw [dv3Pin, dv3Hgt] at hterm
  rcases eq_or_ne (dv2Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) (dev (g8 h2 hq) f j) 21 2) ⊤ with hT | hT
  · rw [hT]
    exact le_top
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← hc] at hterm ⊢
  have hnat : β ≤ 2 * c + 85 * j := by
    rw [nsmul_eq_mul] at hterm
    exact_mod_cast hterm
  exact_mod_cast (by omega : (β - 85 * j + 1) / 2 ≤ c)

private theorem natDegree_dev_g8_lt (f : Polynomial O) (j : ℕ) :
    (dev (g8 h2 hq) f j).natDegree < (g8 h2 hq).natDegree := by
  rcases eq_or_ne (dev (g8 h2 hq) f j) 0 with h0 | h0
  · rw [h0, Polynomial.natDegree_zero, s2g8_natDegree h2 hq]
    norm_num
  · exact Polynomial.natDegree_lt_natDegree h0
      (degree_dev_lt (s2g8_monic h2 hq)
        (by rw [s2g8_natDegree h2 hq]; norm_num) f j)

private theorem natDegree_g8_quot_lt {A B : Polynomial O}
    (hA : A.natDegree < (g8 h2 hq).natDegree)
    (hB : B.natDegree < (g8 h2 hq).natDegree) :
    ((A * B) /ₘ g8 h2 hq).natDegree < (g8 h2 hq).natDegree := by
  rw [Polynomial.natDegree_divByMonic _ (s2g8_monic h2 hq)]
  have h := Polynomial.natDegree_mul_le (p := A) (q := B)
  omega

private theorem dev_g8_mul_one {A B : Polynomial O}
    (hA : A.natDegree < (g8 h2 hq).natDegree)
    (hB : B.natDegree < (g8 h2 hq).natDegree) :
    dev (g8 h2 hq) (A * B) 1 = (A * B) /ₘ g8 h2 hq := by
  have hunfold : dev (g8 h2 hq) (A * B) 1
      = dev (g8 h2 hq) ((A * B) /ₘ g8 h2 hq) 0 := rfl
  rw [hunfold, dev_zero_pin]
  rcases eq_or_ne ((A * B) /ₘ g8 h2 hq) 0 with h0 | h0
  · rw [h0, Polynomial.zero_modByMonic]
  · exact (Polynomial.modByMonic_eq_self_iff (s2g8_monic h2 hq)).mpr
      (by rw [Polynomial.degree_eq_natDegree h0,
            Polynomial.degree_eq_natDegree (s2g8_monic h2 hq).ne_zero]
          exact_mod_cast natDegree_g8_quot_lt h2 hq hA hB)

/-! ## D3-10 — the μ₄ coefficient convolution at `(85,2)` -/

private theorem s2Mu4Coeff_mul_aux {β β' c : ℕ} {g z : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) (hz : S2Mu4ExactGrade h2 hq β' z)
    (hcpar : β % 2 + β' % 2 = (β + β') % 2 + 2 * c) (T : ℕ) :
    s2Mu4Coeff h2 hq (β + β') (g * z) (T + c)
      = ∑ t ∈ Finset.range (T + 1),
          s2Mu4Coeff h2 hq β g t * s2Mu4Coeff h2 hq β' z (T - t) := by
  have hsg : dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) g 85 2 = (β : ℕ∞) := (S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp hg
  have hsz : dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) z 85 2 = (β' : ℕ∞) := (S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp hz
  have hsgz : dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) (g * z) 85 2 = ((β + β' : ℕ) : ℕ∞) :=
    (S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp (S2Mu4ExactGrade_mul h2 hq hg hz)
  rcases Nat.lt_or_ge (β + β') (85 * ((β + β') % 2 + 2 * (T + c))) with hcase | hcase
  · rw [s2Mu4Coeff_eq_zero_of_grade_lt h2 hq hcase]
    refine (Finset.sum_eq_zero fun t ht => ?_).symm
    rw [Finset.mem_range] at ht
    rcases (by omega : β < 85 * (β % 2 + 2 * t) ∨
        β' < 85 * (β' % 2 + 2 * (T - t))) with h | h
    · rw [s2Mu4Coeff_eq_zero_of_grade_lt h2 hq h, zero_mul]
    · rw [s2Mu4Coeff_eq_zero_of_grade_lt h2 hq h, mul_zero]
  · obtain ⟨m, hm⟩ : ∃ m,
        2 * m + 85 * ((β + β') % 2 + 2 * (T + c)) = β + β' :=
      ⟨(β + β' - 85 * ((β + β') % 2 + 2 * (T + c))) / 2, by omega⟩
    have hpinsum := le_dv3Pin_of_le_dv3Supp h2 hq (by norm_num)
      (le_of_eq hsgz.symm) hm
    rw [s2Mu4Coeff_eq_eval_of_le h2 hq hm hpinsum,
      dev_mul_conv_split_monic (s2g8_monic h2 hq)
        (by rw [s2g8_natDegree h2 hq]; norm_num)
        g z ((β + β') % 2 + 2 * (T + c))]
    obtain ⟨S, hSdef⟩ : ∃ S, (β + β') % 2 + 2 * (T + c) = S := ⟨_, rfl⟩
    rw [hSdef] at hm ⊢
    let hmul : ∀ ⦃a b : Polynomial O⦄, a ≠ 0 → b ≠ 0 →
        dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) (a * b) 21 2
          = dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) a 21 2
            + dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) b 21 2 :=
      fun _ _ ha hb => s2_dv2Supp_mul_local h2 hq ha hb
    have hmainfloor : ∀ j ∈ Finset.range (S + 1),
        (m : ℕ∞) ≤ dv2Supp ((s2Tower h2 hq).levelDatum h2)
          (s2DepthTwoKeyAt h2 hq 2)
          ((dev (g8 h2 hq) g j * dev (g8 h2 hq) z (S - j)) %ₘ g8 h2 hq) 21 2 := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [C136d3ad.dv2Supp_mul_modByKey_eq ((s2Tower h2 hq).levelDatum h2)
        (s2Φ₂_monic h2 hq) (by rw [s2Φ₂_natDegree h2 hq]; norm_num)
        (by norm_num) hmul (s2_isMu3Key_g8 h2 hq)
        (natDegree_dev_g8_lt h2 hq g j) (natDegree_dev_g8_lt h2 hq z (S - j))]
      refine le_trans (Nat.cast_le.mpr (show m ≤ (β - 85 * j + 1) / 2
          + (β' - 85 * (S - j) + 1) / 2 from by omega)) ?_
      exact coe_le_add_of_le
        (ceil_le_dv2Supp_dev_g8 h2 hq j (le_of_eq hsg.symm))
        (ceil_le_dv2Supp_dev_g8 h2 hq (S - j) (le_of_eq hsz.symm))
    have hcarryfloor : ∀ j ∈ Finset.range S,
        ((m + 1 : ℕ) : ℕ∞) ≤ dv2Supp ((s2Tower h2 hq).levelDatum h2)
          (s2DepthTwoKeyAt h2 hq 2)
          (dev (g8 h2 hq)
            (dev (g8 h2 hq) g j * dev (g8 h2 hq) z (S - 1 - j)) 1) 21 2 := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [dev_g8_mul_one h2 hq (natDegree_dev_g8_lt h2 hq g j)
        (natDegree_dev_g8_lt h2 hq z (S - 1 - j))]
      have hsharp := C136d3ad.dv2Supp_add_le_key_quot_add
        ((s2Tower h2 hq).levelDatum h2) (s2Φ₂_monic h2 hq)
        (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num) hmul
        (s2_isMu3Key_g8 h2 hq) (natDegree_dev_g8_lt h2 hq g j)
        (natDegree_dev_g8_lt h2 hq z (S - 1 - j))
      rw [s2_dv2Supp_g8 h2 hq] at hsharp
      have hsum := le_trans (coe_le_add_of_le
        (ceil_le_dv2Supp_dev_g8 h2 hq j (le_of_eq hsg.symm))
        (ceil_le_dv2Supp_dev_g8 h2 hq (S - 1 - j) (le_of_eq hsz.symm))) hsharp
      rcases eq_or_ne (dv2Supp ((s2Tower h2 hq).levelDatum h2)
          (s2DepthTwoKeyAt h2 hq 2)
          ((dev (g8 h2 hq) g j * dev (g8 h2 hq) z (S - 1 - j)) /ₘ g8 h2 hq)
          21 2) ⊤ with htop | hfin
      · rw [htop]
        exact le_top
      obtain ⟨q, hq'⟩ := ENat.ne_top_iff_exists.1 hfin
      rw [← hq'] at hsum ⊢
      have hnat : (β - 85 * j + 1) / 2 + (β' - 85 * (S - 1 - j) + 1) / 2
          ≤ 42 + q := by
        exact_mod_cast hsum
      exact_mod_cast (show m + 1 ≤ q from by omega)
    rw [C132rp3.s2Mu3GradedRes_add_of_le h2 hq
        (le_dv2Supp_finsetSum h2 hq _ _ hmainfloor)
        (le_dv2Supp_finsetSum h2 hq _ _ fun j hj =>
          le_trans (Nat.cast_le.mpr (Nat.le_succ m)) (hcarryfloor j hj)),
      Polynomial.eval_add,
      s2Mu3GradedRes_finsetSum_of_le h2 hq _ _ hmainfloor,
      s2Mu3GradedRes_finsetSum_of_le h2 hq _ _ (fun j hj =>
        le_trans (Nat.cast_le.mpr (Nat.le_succ m)) (hcarryfloor j hj)),
      Polynomial.eval_finsetSum, Polynomial.eval_finsetSum]
    have hcarryzero : (∑ j ∈ Finset.range S,
        Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
          (s2Mu3GradedRes h2 hq m
            (dev (g8 h2 hq)
              (dev (g8 h2 hq) g j * dev (g8 h2 hq) z (S - 1 - j)) 1))) = 0 :=
      Finset.sum_eq_zero fun j hj => by
        rw [s2Mu3GradedRes_zero_of_above h2 hq
          ((S2Mu3AboveGrade_iff_dv2Supp h2 hq).mpr
            (lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self m)) (hcarryfloor j hj))),
          Polynomial.eval_zero]
    rw [hcarryzero, add_zero]
    have hoff : ∀ j ∈ Finset.range (S + 1),
        Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
          (s2Mu3GradedRes h2 hq m
            ((dev (g8 h2 hq) g j * dev (g8 h2 hq) z (S - j)) %ₘ g8 h2 hq)) ≠ 0 →
          j % 2 = β % 2 := by
      intro j hj hne
      rw [Finset.mem_range] at hj
      by_contra hpar
      refine hne ?_
      have habove : (m : ℕ∞) < dv2Supp ((s2Tower h2 hq).levelDatum h2)
          (s2DepthTwoKeyAt h2 hq 2)
          ((dev (g8 h2 hq) g j * dev (g8 h2 hq) z (S - j)) %ₘ g8 h2 hq) 21 2 := by
        rw [C136d3ad.dv2Supp_mul_modByKey_eq ((s2Tower h2 hq).levelDatum h2)
          (s2Φ₂_monic h2 hq) (by rw [s2Φ₂_natDegree h2 hq]; norm_num)
          (by norm_num) hmul (s2_isMu3Key_g8 h2 hq)
          (natDegree_dev_g8_lt h2 hq g j) (natDegree_dev_g8_lt h2 hq z (S - j))]
        refine lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self m)) ?_
        refine le_trans (Nat.cast_le.mpr (show m + 1 ≤ (β - 85 * j + 1) / 2
            + (β' - 85 * (S - j) + 1) / 2 from by omega)) ?_
        exact coe_le_add_of_le
          (ceil_le_dv2Supp_dev_g8 h2 hq j (le_of_eq hsg.symm))
          (ceil_le_dv2Supp_dev_g8 h2 hq (S - j) (le_of_eq hsz.symm))
      rw [s2Mu3GradedRes_zero_of_above h2 hq
        ((S2Mu3AboveGrade_iff_dv2Supp h2 hq).mpr habove), Polynomial.eval_zero]
    rw [← Finset.sum_filter_of_ne hoff]
    have himg : (Finset.range (S + 1)).filter (fun j => j % 2 = β % 2)
        = (Finset.range (T + 1)).image (fun t => β % 2 + 2 * t) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hj, hpar⟩
        exact ⟨j / 2, by omega, by omega⟩
      · rintro ⟨t, ht, rfl⟩
        omega
    rw [himg, Finset.sum_image (fun a _ b _ hab => by omega)]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_range] at ht
    rw [show S - (β % 2 + 2 * t) = β' % 2 + 2 * (T - t) from by omega]
    rcases Nat.lt_or_ge β (85 * (β % 2 + 2 * t)) with hbig | hok
    · have habove : (m : ℕ∞) < dv2Supp ((s2Tower h2 hq).levelDatum h2)
          (s2DepthTwoKeyAt h2 hq 2)
          ((dev (g8 h2 hq) g (β % 2 + 2 * t)
            * dev (g8 h2 hq) z (β' % 2 + 2 * (T - t))) %ₘ g8 h2 hq) 21 2 := by
        rw [C136d3ad.dv2Supp_mul_modByKey_eq ((s2Tower h2 hq).levelDatum h2)
          (s2Φ₂_monic h2 hq) (by rw [s2Φ₂_natDegree h2 hq]; norm_num)
          (by norm_num) hmul (s2_isMu3Key_g8 h2 hq)
          (natDegree_dev_g8_lt h2 hq g (β % 2 + 2 * t))
          (natDegree_dev_g8_lt h2 hq z (β' % 2 + 2 * (T - t)))]
        refine lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self m)) ?_
        refine le_trans (Nat.cast_le.mpr (show m + 1 ≤
          (β - 85 * (β % 2 + 2 * t) + 1) / 2
            + (β' - 85 * (β' % 2 + 2 * (T - t)) + 1) / 2 from by omega)) ?_
        exact coe_le_add_of_le
          (ceil_le_dv2Supp_dev_g8 h2 hq (β % 2 + 2 * t) (le_of_eq hsg.symm))
          (ceil_le_dv2Supp_dev_g8 h2 hq (β' % 2 + 2 * (T - t)) (le_of_eq hsz.symm))
      rw [s2Mu4Coeff_eq_zero_of_grade_lt h2 hq hbig, zero_mul,
        s2Mu3GradedRes_zero_of_above h2 hq
          ((S2Mu3AboveGrade_iff_dv2Supp h2 hq).mpr habove), Polynomial.eval_zero]
    rcases Nat.lt_or_ge β' (85 * (β' % 2 + 2 * (T - t))) with hbig' | hok'
    · have habove : (m : ℕ∞) < dv2Supp ((s2Tower h2 hq).levelDatum h2)
          (s2DepthTwoKeyAt h2 hq 2)
          ((dev (g8 h2 hq) g (β % 2 + 2 * t)
            * dev (g8 h2 hq) z (β' % 2 + 2 * (T - t))) %ₘ g8 h2 hq) 21 2 := by
        rw [C136d3ad.dv2Supp_mul_modByKey_eq ((s2Tower h2 hq).levelDatum h2)
          (s2Φ₂_monic h2 hq) (by rw [s2Φ₂_natDegree h2 hq]; norm_num)
          (by norm_num) hmul (s2_isMu3Key_g8 h2 hq)
          (natDegree_dev_g8_lt h2 hq g (β % 2 + 2 * t))
          (natDegree_dev_g8_lt h2 hq z (β' % 2 + 2 * (T - t)))]
        refine lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self m)) ?_
        refine le_trans (Nat.cast_le.mpr (show m + 1 ≤
          (β - 85 * (β % 2 + 2 * t) + 1) / 2
            + (β' - 85 * (β' % 2 + 2 * (T - t)) + 1) / 2 from by omega)) ?_
        exact coe_le_add_of_le
          (ceil_le_dv2Supp_dev_g8 h2 hq (β % 2 + 2 * t) (le_of_eq hsg.symm))
          (ceil_le_dv2Supp_dev_g8 h2 hq (β' % 2 + 2 * (T - t)) (le_of_eq hsz.symm))
      rw [s2Mu4Coeff_eq_zero_of_grade_lt h2 hq hbig', mul_zero,
        s2Mu3GradedRes_zero_of_above h2 hq
          ((S2Mu3AboveGrade_iff_dv2Supp h2 hq).mpr habove), Polynomial.eval_zero]
    · have hj2 : 2 * ((β - 85 * (β % 2 + 2 * t)) / 2)
          + 85 * (β % 2 + 2 * t) = β := by omega
      have hk2 : 2 * ((β' - 85 * (β' % 2 + 2 * (T - t))) / 2)
          + 85 * (β' % 2 + 2 * (T - t)) = β' := by omega
      have hf1 : (((β - 85 * (β % 2 + 2 * t)) / 2 : ℕ) : ℕ∞)
          ≤ dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2)
            (dev (g8 h2 hq) g (β % 2 + 2 * t)) 21 2 :=
        le_trans (Nat.cast_le.mpr (by omega))
          (ceil_le_dv2Supp_dev_g8 h2 hq (β % 2 + 2 * t) (le_of_eq hsg.symm))
      have hf2 : (((β' - 85 * (β' % 2 + 2 * (T - t))) / 2 : ℕ) : ℕ∞)
          ≤ dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2)
            (dev (g8 h2 hq) z (β' % 2 + 2 * (T - t))) 21 2 :=
        le_trans (Nat.cast_le.mpr (by omega))
          (ceil_le_dv2Supp_dev_g8 h2 hq (β' % 2 + 2 * (T - t)) (le_of_eq hsz.symm))
      rw [s2Mu4Coeff_eq_eval_of_le h2 hq hj2 hf1,
        s2Mu4Coeff_eq_eval_of_le h2 hq hk2 hf2]
      rw [eval_one_mu3GradedRes_modBy_g8 h2 hq
          (natDegree_dev_g8_lt h2 hq g (β % 2 + 2 * t))
          (natDegree_dev_g8_lt h2 hq z (β' % 2 + 2 * (T - t)))
          (le_trans (Nat.cast_le.mpr (show m ≤
            (β - 85 * (β % 2 + 2 * t)) / 2
              + (β' - 85 * (β' % 2 + 2 * (T - t))) / 2 from by omega))
            (coe_le_add_of_le hf1 hf2)),
        show m = (β - 85 * (β % 2 + 2 * t)) / 2
            + (β' - 85 * (β' % 2 + 2 * (T - t))) / 2 from by omega]
      exact eval_one_mu3GradedRes_mul_of_le h2 hq hf1 hf2

/-- ★ **D3-10 — the μ₄ recursive coefficient convolution at `(u₄,ℓ₄)=(85,2)`.** -/
theorem s2Mu4Coeff_mul {β β' : ℕ} {g z : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) (hz : S2Mu4ExactGrade h2 hq β' z) (T : ℕ) :
    s2Mu4Coeff h2 hq (β + β') (g * z) (T + s2Mu4Carry β β')
      = ∑ t ∈ Finset.range (T + 1),
          s2Mu4Coeff h2 hq β g t * s2Mu4Coeff h2 hq β' z (T - t) :=
  s2Mu4Coeff_mul_aux h2 hq hg hz (s2Mu4Carry_parity β β') T

end S2

/-! ## The generic `hconv` carrier audit

The A24A off-side channel does not apply to the requested slot: the product coefficient
above is read at its fixed support grade, and strict pricing kills the carry and every
off-line main term.  A different obstruction remains for the bare generic `dv2Res`.

At a common absolute grade, a summand whose own residual window starts one lattice step
to the right contributes `η * b` to the absolute read, while its own-height normalized
`dv2Res` is `b`.  Thus replacing the absolute fixed-grade sum by the unweighted sum in
L2E-09's proposed `hconv` forces `η = 1` as soon as such a contribution is nonzero.  A
general `LevelDatum` assumes only that its residual polynomial has nonzero constant term;
it does not identify `AdjoinRoot.root L.r` with `1`.  The following elementary diagnostic
is the exact cancellation at that last step. -/

/-- If a one-step shifted fixed-grade contribution is identified with its unshifted
own-height normalization, its nonzero coefficient forces the residue letter to be `1`. -/
theorem fixedGrade_unweighted_add_forces_letter_one {K : Type*}
    [CommRing K] [IsDomain K] {η a b : K} (hb : b ≠ 0)
    (h : a + η * b = a + b) : η = 1 := by
  have hηb : η * b = b := add_left_cancel h
  have hzero : (η - 1) * b = 0 := by rw [sub_mul, hηb, one_mul, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right hb)

end Uniformity.Density.Tower.C136l2e4

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C136l2e4.fixedGrade_unweighted_add_forces_letter_one
#print axioms Uniformity.Density.Tower.C136l2e4.s2Mu3GradedRes_finsetSum_of_le
#print axioms Uniformity.Density.Tower.C136l2e4.eval_one_mu3GradedRes_g8_mul
#print axioms Uniformity.Density.Tower.C136l2e4.eval_one_mu3GradedRes_modBy_g8
#print axioms Uniformity.Density.Tower.C136l2e4.eval_one_mu3GradedRes_mul_of_exact
#print axioms Uniformity.Density.Tower.C136l2e4.eval_one_mu3GradedRes_mul_of_le
#print axioms Uniformity.Density.Tower.C136l2e4.s2Mu4Coeff_mul

end AxCheck
