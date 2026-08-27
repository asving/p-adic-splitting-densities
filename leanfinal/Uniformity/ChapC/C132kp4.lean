/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C132kp0
import Uniformity.ChapC.C132rp3
import Uniformity.ChapC.C130kp5

/-!
# Uniformity.ChapC.C132kp4 — the carried key at μ₃

**[M3-KP4, 2026-08-27]** (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6):
the carried polynomial `Φ₂ := s2DepthTwoKeyAt h2 hq 2` is a key polynomial for the
landed μ₃ value, and its normalized μ₃ residual is `1`.

The key-polynomial proof is the `C130kp0`/`C130kp1` carried-key argument with the landed
μ₃ numerals substituted: `deg Φ₂ = 4`, `μ₃(Φ₂) = 21`, and outer ramification `2`.
The residual-divisibility criterion for nonunit residuals is intentionally inapplicable:
`R₃(Φ₂)=1`.  As at μ₂, divisibility by the current development key is instead controlled
by the slot-zero gate; the odd-by-odd carry proves minimality and primality.
-/

set_option linter.style.longLine false
set_option maxHeartbeats 800000

namespace Uniformity.Density.Tower.C132kp4

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130nv2
open Uniformity.Density.Tower.C130rp0 Uniformity.Density.Tower.C130rp1
open Uniformity.Density.Tower.C130rp8 Uniformity.Density.Tower.C130kp5
open Uniformity.Density.Tower.C132nv0 Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C132rp0 Uniformity.Density.Tower.C132rp1
open Uniformity.Density.Tower.C132rp2 Uniformity.Density.Tower.C132rp3
open Uniformity.Density.Tower.C132rp6 Uniformity.Density.Tower.C132rp7
open Uniformity.Density.Tower.C132rp8 Uniformity.Density.Tower.C132kp0
open Uniformity.Density.Tower.C80

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

private theorem phi2_natDegree :
    (s2DepthTwoKeyAt h2 hq 2 : Polynomial O).natDegree = 4 :=
  s2Φ₂_natDegree h2 hq

/-! ## Initial forms through the μ₃ graded piece -/

private theorem s2Mu3GradedRes_neg_of_le {β : ℕ} {g : Polynomial O}
    (hg : (β : ℕ∞) ≤ dv2Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) g 21 2) :
    s2Mu3GradedRes h2 hq β (-g) = -s2Mu3GradedRes h2 hq β g := by
  have hneg : (β : ℕ∞) ≤ dv2Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) (-g) 21 2 := by
    rw [dv2Supp_neg _ (s2Φ₂_monic h2 hq)]
    exact hg
  have hsum := s2Mu3GradedRes_add_of_le h2 hq hg hneg
  rw [add_neg_cancel, s2Mu3GradedRes_zero] at hsum
  linear_combination hsum.symm

private theorem initialEquiv_iff_gradedRes {β : ℕ} {g h : Polynomial O}
    (hg : S2Mu3ExactGrade h2 hq β g) (hh : S2Mu3ExactGrade h2 hq β h) :
    S2Mu3InitialEquiv h2 hq g h ↔
      s2Mu3GradedRes h2 hq β g = s2Mu3GradedRes h2 hq β h := by
  have hvg : s2Hgt₃ h2 hq g = (β : WithTop ℤ) := hg
  have hvh : s2Hgt₃ h2 hq h = (β : WithTop ℤ) := hh
  constructor
  · intro hgh
    rcases hgh with ⟨hlt, -⟩ | ⟨hg0, -⟩
    · have habove : S2Mu3AboveGrade h2 hq β (g - h) := by
        show (β : WithTop ℤ) < s2Hgt₃ h2 hq (g - h)
        rw [← hvg]
        exact hlt
      have hdecomp : g = h + (g - h) := by ring
      have hadd := s2Mu3GradedRes_add_of_le h2 hq
        (le_of_eq ((S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp hh).symm)
        (le_of_lt ((S2Mu3AboveGrade_iff_dv2Supp h2 hq).mp habove))
      rw [← hdecomp, s2Mu3GradedRes_zero_of_above h2 hq habove, add_zero] at hadd
      exact hadd
    · exact absurd hg0 (S2Mu3ExactGrade_not_zero h2 hq hg)
  · intro hres
    rcases eq_or_ne (g - h) 0 with hgh0 | hgh0
    · rw [sub_eq_zero.mp hgh0]
      exact S2Mu3InitialEquiv_refl h2 hq h
    · have hnegh : S2Mu3ExactGrade h2 hq β (-h) := by
        rw [S2Mu3ExactGrade_iff_dv2Supp, dv2Supp_neg _ (s2Φ₂_monic h2 hq)]
        exact (S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp hh
      have hvneg : s2Hgt₃ h2 hq (-h) = (β : WithTop ℤ) := hnegh
      have hge : (β : WithTop ℤ) ≤ s2Hgt₃ h2 hq (g - h) := by
        have hmin := s2Hgt₃_add_ge h2 hq g (-h)
        rw [← sub_eq_add_neg, hvg, hvneg, min_self] at hmin
        exact hmin
      rcases hge.lt_or_eq with hlt | heqv
      · refine Or.inl ⟨?_, hvg.trans hvh.symm⟩
        rw [hvg]
        exact hlt
      · have hexact : S2Mu3ExactGrade h2 hq β (g - h) := heqv.symm
        have hne := s2Mu3GradedRes_ne_zero_of_exact h2 hq hexact
        have hadd := s2Mu3GradedRes_add_of_le h2 hq
          (le_of_eq ((S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp hg).symm)
          (le_of_eq ((S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp hnegh).symm)
        rw [← sub_eq_add_neg,
          s2Mu3GradedRes_neg_of_le h2 hq
            (le_of_eq ((S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp hh).symm),
          hres, add_neg_cancel] at hadd
        exact absurd hadd hne

/-! ## The odd-carry obstruction and minimality -/

private theorem not_mu3Dvd_phi2_of_even_grade {β : ℕ} {g : Polynomial O}
    (hg : S2Mu3ExactGrade h2 hq β g) (heven : 2 ∣ β)
    (hc : (s2Mu3GradedRes h2 hq β g).coeff 0 ≠ 0) :
    ¬ S2Mu3Dvd h2 hq (s2DepthTwoKeyAt h2 hq 2) g := by
  rintro ⟨q, hq'⟩
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [mul_zero] at hq'
    exact S2Mu3ExactGrade_not_zero h2 hq hg
      ((S2Mu3InitialEquiv_zero_right h2 hq).mp hq')
  · obtain ⟨β', hβ'⟩ := S2Mu3ExactGrade_exists h2 hq hq0
    have hkq : S2Mu3ExactGrade h2 hq (21 + β')
        ((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) * q) :=
      S2Mu3ExactGrade_mul h2 hq (tooth_Φ₂ h2 hq) hβ'
    have hgkq : S2Mu3ExactGrade h2 hq β
        ((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) * q) :=
      S2Mu3ExactGrade_of_initialEquiv h2 hq hg hq'
    have hβeq : β = 21 + β' := S2Mu3ExactGrade_unique h2 hq hgkq hkq
    subst hβeq
    have hres := (initialEquiv_iff_gradedRes h2 hq hg hgkq).mp hq'
    have hmul := s2Mu3GradedRes_mul_of_exact h2 hq (tooth_Φ₂ h2 hq) hβ'
    rw [s2Mu3GradedRes_key h2 hq, one_mul,
      show 21 % 2 * (β' % 2) = 1 by omega, pow_one] at hmul
    rw [hmul] at hres
    apply hc
    rw [hres, Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul]

private theorem exactGrade_even_of_natDegree_lt_four {β : ℕ} {g : Polynomial O}
    (hg : S2Mu3ExactGrade h2 hq β g) (hdeg : g.natDegree < 4) : 2 ∣ β := by
  obtain ⟨s, hgate⟩ := exists_mu3SlotOnGrade_of_exact h2 hq hg
  have hs0 : s = 0 := by
    by_contra hs
    obtain ⟨m, hm, -⟩ := (s2Mu3SlotOnGrade_iff h2 hq).mp hgate
    have hdev : dev (s2DepthTwoKeyAt h2 hq 2) g s = 0 :=
      dev_eq_zero_of_lt (s2Φ₂_monic h2 hq)
        (by rw [phi2_natDegree h2 hq]; norm_num) g s
        (by rw [phi2_natDegree h2 hq]; omega)
    have htop : dv2Pin ((s2Tower h2 hq).levelDatum h2)
        (s2DepthTwoKeyAt h2 hq 2) g s = ⊤ := by
      rw [dv2Pin, hdev]
      exact Uniformity.Density.Tower.dv2Hgt_zero _
    rw [htop] at hm
    exact WithTop.top_ne_coe hm
  subst hs0
  obtain ⟨m, -, hline⟩ := (s2Mu3SlotOnGrade_iff h2 hq).mp hgate
  exact ⟨m, by omega⟩

private theorem mu3Minimal_phi2 :
    S2Mu3Minimal h2 hq (s2DepthTwoKeyAt h2 hq 2) := by
  refine ⟨by rw [phi2_natDegree h2 hq]; omega, fun g hg0 hdeg hdvd => ?_⟩
  rw [phi2_natDegree h2 hq] at hdeg
  obtain ⟨β, hβ⟩ := S2Mu3ExactGrade_exists h2 hq hg0
  exact not_mu3Dvd_phi2_of_even_grade h2 hq hβ
    (exactGrade_even_of_natDegree_lt_four h2 hq hβ hdeg)
    (s2Mu3GradedRes_coeff_zero_ne_zero_of_exact h2 hq hβ hdeg) hdvd

private theorem not_mu3Dvd_phi2_one :
    ¬ S2Mu3Dvd h2 hq (s2DepthTwoKeyAt h2 hq 2) (1 : Polynomial O) :=
  (mu3Minimal_phi2 h2 hq).2 1 one_ne_zero
    (by rw [Polynomial.natDegree_one, phi2_natDegree h2 hq]; omega)

/-! ## The slot-zero test and primality -/

private theorem old_key_natDegree_two :
    ((s2Frame h2 hq).key : Polynomial O).natDegree = 2 := by
  rw [key_eq h2 hq]
  exact s2Key_natDegree

private theorem innerGradedRes_coeff_eq_zero_of_pos {m t : ℕ} {A : Polynomial O}
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

private theorem eval_one_innerGradedRes {m : ℕ} {A : Polynomial O} (hA : A.natDegree < 4) :
    Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2) (s2GradedRes h2 hq m A) =
      (s2GradedRes h2 hq m A).coeff 0 := by
  have hconst : s2GradedRes h2 hq m A =
      Polynomial.C ((s2GradedRes h2 hq m A).coeff 0) := by
    refine Polynomial.ext fun t => ?_
    match t with
    | 0 => simp
    | t + 1 =>
        rw [Polynomial.coeff_C, if_neg (Nat.succ_ne_zero t)]
        exact innerGradedRes_coeff_eq_zero_of_pos h2 hq hA (Nat.succ_pos t)
  calc
    Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2) (s2GradedRes h2 hq m A) =
        Polynomial.eval 1 (Polynomial.C ((s2GradedRes h2 hq m A).coeff 0)) :=
      congrArg _ hconst
    _ = (s2GradedRes h2 hq m A).coeff 0 := Polynomial.eval_C

private theorem mu3Coeff_ne_zero_of_slot {β s : ℕ} {g : Polynomial O}
    (hgate : S2Mu3SlotOnGrade h2 hq β g s) :
    s2Mu3Coeff h2 hq β g (s / 2) ≠ 0 := by
  let A := dev (s2DepthTwoKeyAt h2 hq 2) g s
  have hinner : S2ExactGrade h2 hq ((β - 21 * s) / 2) A :=
    s2Mu3SlotOnGrade_inner_exact h2 hq hgate
  have hdeg : A.natDegree < 4 := by
    rcases eq_or_ne A 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]
      norm_num
    · have h := Polynomial.natDegree_lt_natDegree h0
        (degree_dev_lt (s2Φ₂_monic h2 hq)
          (by rw [phi2_natDegree h2 hq]; norm_num) g s)
      rwa [phi2_natDegree h2 hq] at h
  have hcoeff := s2Mu3Coeff_slot h2 hq hgate
  rw [s2Mu3Eps_eq_one, one_mul, eval_one_innerGradedRes h2 hq hdeg] at hcoeff
  rw [hcoeff]
  exact s2GradedRes_coeff_zero_ne_zero_of_exact h2 hq hinner hdeg

private theorem not_mu3Dvd_phi2_of_slotZero {β : ℕ} {f : Polynomial O}
    (hf : S2Mu3ExactGrade h2 hq β f) (hgate : S2Mu3SlotOnGrade h2 hq β f 0) :
    ¬ S2Mu3Dvd h2 hq (s2DepthTwoKeyAt h2 hq 2) f := by
  obtain ⟨m, -, hline⟩ := (s2Mu3SlotOnGrade_iff h2 hq).mp hgate
  have heven : 2 ∣ β := ⟨m, by omega⟩
  have hc : (s2Mu3GradedRes h2 hq β f).coeff 0 ≠ 0 := by
    rw [s2Mu3GradedRes_coeff]
    simpa using (mu3Coeff_ne_zero_of_slot (O := O) h2 hq
      (β := β) (s := 0) (g := f) hgate)
  exact not_mu3Dvd_phi2_of_even_grade h2 hq hf heven hc

private theorem mu3Dvd_phi2_of_not_slotZero {β : ℕ} {f : Polynomial O}
    (hf : S2Mu3ExactGrade h2 hq β f) (hgate : ¬ S2Mu3SlotOnGrade h2 hq β f 0) :
    S2Mu3Dvd h2 hq (s2DepthTwoKeyAt h2 hq 2) f := by
  let phi := s2DepthTwoKeyAt h2 hq 2
  have hmon : (phi : Polynomial O).Monic := s2Φ₂_monic h2 hq
  have hmod : f %ₘ phi + phi * (f /ₘ phi) = f := Polynomial.modByMonic_add_div f phi
  rcases eq_or_ne (f %ₘ phi) 0 with hr0 | hr0
  · exact S2Mu3Dvd_of_dvd h2 hq ((Polynomial.modByMonic_eq_zero_iff_dvd hmon).mp hr0)
  have hdegr : (f %ₘ phi).natDegree < 4 := by
    have h := Polynomial.natDegree_lt_natDegree hr0 (Polynomial.degree_modByMonic_lt f hmon)
    rw [show phi.natDegree = 4 by exact phi2_natDegree h2 hq] at h
    exact h
  have hdevr : dev phi (f %ₘ phi) 0 = f %ₘ phi := by
    rw [dev_zero_pin]
    exact (Polynomial.modByMonic_eq_self_iff hmon).mpr (Polynomial.degree_modByMonic_lt f hmon)
  have hsupp_r : dv2Supp ((s2Tower h2 hq).levelDatum h2) phi (f %ₘ phi) 21 2 =
      2 • dv2Pin ((s2Tower h2 hq).levelDatum h2) phi f 0 := by
    rw [dv2Supp_eq_inf_range ((s2Tower h2 hq).levelDatum h2) hmon
      (by rw [show phi.natDegree = 4 by exact phi2_natDegree h2 hq]; norm_num)
      (by norm_num : (0 : ℕ) < 2) _ (M := 4) hdegr,
      show Finset.range 4 = {0, 1, 2, 3} by decide,
      Finset.inf_insert, Finset.inf_insert, Finset.inf_insert, Finset.inf_singleton]
    have hpin (j : ℕ) (hj : 0 < j) :
        dv2Pin ((s2Tower h2 hq).levelDatum h2) phi (f %ₘ phi) j = ⊤ := by
      rw [dv2Pin, dev_eq_zero_of_lt hmon
        (by rw [show phi.natDegree = 4 by exact phi2_natDegree h2 hq]; norm_num) _ j
        (by rw [show phi.natDegree = 4 by exact phi2_natDegree h2 hq]; omega)]
      exact Uniformity.Density.Tower.dv2Hgt_zero _
    simp only [hpin 1 (by norm_num), hpin 2 (by norm_num), hpin 3 (by norm_num),
      C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2), top_add,
      Nat.cast_zero, mul_zero, add_zero]
    simp only [min_eq_left le_top]
    rw [show dv2Pin ((s2Tower h2 hq).levelDatum h2) phi (f %ₘ phi) 0 =
        dv2Pin ((s2Tower h2 hq).levelDatum h2) phi f 0 by
      rw [dv2Pin, hdevr, dv2Pin, dev_zero_pin]]
  have hle : (β : ℕ∞) ≤ 2 • dv2Pin ((s2Tower h2 hq).levelDatum h2) phi f 0 := by
    have hterm := C132nv2.dv2Supp_le_term ((s2Tower h2 hq).levelDatum h2)
      (s2Φ₂_monic h2 hq) (by rw [phi2_natDegree h2 hq]; norm_num)
      f 21 (by norm_num : (0 : ℕ) < 2) 0
    rw [(S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp hf] at hterm
    simpa using hterm
  have hne : 2 • dv2Pin ((s2Tower h2 hq).levelDatum h2) phi f 0 ≠ (β : ℕ∞) := by
    intro heq
    have hfin : dv2Pin ((s2Tower h2 hq).levelDatum h2) phi f 0 ≠ ⊤ := by
      intro htop
      rw [htop, C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2)] at heq
      exact WithTop.top_ne_coe heq
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
    refine hgate ((s2Mu3SlotOnGrade_iff h2 hq).mpr ⟨m, hm.symm, ?_⟩)
    rw [← hm, nsmul_eq_mul] at heq
    have h2m : (2 * m : ℕ) = β := by exact_mod_cast heq
    omega
  have hltE : (β : ℕ∞) < 2 • dv2Pin ((s2Tower h2 hq).levelDatum h2) phi f 0 :=
    lt_of_le_of_ne hle (Ne.symm hne)
  have hgt : s2Hgt₃ h2 hq f < s2Hgt₃ h2 hq (f %ₘ phi) := by
    have hvf : s2Hgt₃ h2 hq f = (β : WithTop ℤ) := hf
    rw [hvf, s2Hgt₃_eq_dv2Supp, hsupp_r,
      show (β : WithTop ℤ) = C130s6.toZ (β : ℕ∞) by norm_cast]
    exact toZ_lt_toZ_iff.mpr hltE
  have hkw : phi * (f /ₘ phi) = f - f %ₘ phi := (sub_eq_of_eq_add' hmod.symm).symm
  have hval_kw : s2Hgt₃ h2 hq (phi * (f /ₘ phi)) = s2Hgt₃ h2 hq f := by
    rw [hkw, sub_eq_add_neg,
      s2Hgt₃_add_eq h2 hq _ _ (by rw [s2Hgt₃_neg h2 hq]; exact ne_of_lt hgt),
      s2Hgt₃_neg h2 hq]
    exact min_eq_left (le_of_lt hgt)
  refine ⟨f /ₘ phi, Or.inl ⟨?_, hval_kw.symm⟩⟩
  rw [show f - phi * (f /ₘ phi) = f %ₘ phi by rw [hkw]; ring]
  exact hgt

private theorem mu3Dvd_phi2_iff {β : ℕ} {f : Polynomial O}
    (hf : S2Mu3ExactGrade h2 hq β f) :
    S2Mu3Dvd h2 hq (s2DepthTwoKeyAt h2 hq 2) f ↔
      ¬ S2Mu3SlotOnGrade h2 hq β f 0 :=
  ⟨fun hdvd hgate => not_mu3Dvd_phi2_of_slotZero h2 hq hf hgate hdvd,
    mu3Dvd_phi2_of_not_slotZero h2 hq hf⟩

private theorem mu3Dvd_phi2_of_odd_grade {β : ℕ} {f : Polynomial O}
    (hf : S2Mu3ExactGrade h2 hq β f) (hodd : β % 2 = 1) :
    S2Mu3Dvd h2 hq (s2DepthTwoKeyAt h2 hq 2) f :=
  mu3Dvd_phi2_of_not_slotZero h2 hq hf fun hgate => by
    obtain ⟨m, -, hline⟩ := (s2Mu3SlotOnGrade_iff h2 hq).mp hgate
    omega

private theorem mu3Dvd_phi2_or (a b : Polynomial O)
    (hdvd : S2Mu3Dvd h2 hq (s2DepthTwoKeyAt h2 hq 2) (a * b)) :
    S2Mu3Dvd h2 hq (s2DepthTwoKeyAt h2 hq 2) a ∨
      S2Mu3Dvd h2 hq (s2DepthTwoKeyAt h2 hq 2) b := by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact Or.inl (S2Mu3Dvd_zero h2 hq _)
  rcases eq_or_ne b 0 with rfl | hb0
  · exact Or.inr (S2Mu3Dvd_zero h2 hq _)
  have hexa := S2Mu3ExactGrade_s2Mu3GradeOf h2 hq ha0
  have hexb := S2Mu3ExactGrade_s2Mu3GradeOf h2 hq hb0
  rcases Nat.mod_two_eq_zero_or_one (s2Mu3GradeOf h2 hq a) with hpa | hpa
  swap
  · exact Or.inl (mu3Dvd_phi2_of_odd_grade h2 hq hexa hpa)
  rcases Nat.mod_two_eq_zero_or_one (s2Mu3GradeOf h2 hq b) with hpb | hpb
  swap
  · exact Or.inr (mu3Dvd_phi2_of_odd_grade h2 hq hexb hpb)
  by_cases hga : S2Mu3SlotOnGrade h2 hq (s2Mu3GradeOf h2 hq a) a 0
  swap
  · exact Or.inl (mu3Dvd_phi2_of_not_slotZero h2 hq hexa hga)
  by_cases hgb : S2Mu3SlotOnGrade h2 hq (s2Mu3GradeOf h2 hq b) b 0
  swap
  · exact Or.inr (mu3Dvd_phi2_of_not_slotZero h2 hq hexb hgb)
  exfalso
  have hexab := S2Mu3ExactGrade_mul h2 hq hexa hexb
  have heven : 2 ∣ s2Mu3GradeOf h2 hq a + s2Mu3GradeOf h2 hq b := by omega
  have hca : (s2Mu3GradedRes h2 hq (s2Mu3GradeOf h2 hq a) a).coeff 0 ≠ 0 := by
    rw [s2Mu3GradedRes_coeff]
    simpa using (mu3Coeff_ne_zero_of_slot (O := O) h2 hq
      (β := s2Mu3GradeOf h2 hq a) (s := 0) (g := a) hga)
  have hcb : (s2Mu3GradedRes h2 hq (s2Mu3GradeOf h2 hq b) b).coeff 0 ≠ 0 := by
    rw [s2Mu3GradedRes_coeff]
    simpa using (mu3Coeff_ne_zero_of_slot (O := O) h2 hq
      (β := s2Mu3GradeOf h2 hq b) (s := 0) (g := b) hgb)
  have hcab :
      (s2Mu3GradedRes h2 hq (s2Mu3GradeOf h2 hq a + s2Mu3GradeOf h2 hq b)
        (a * b)).coeff 0 ≠ 0 := by
    rw [s2Mu3GradedRes_mul_of_exact h2 hq hexa hexb, hpa, hpb,
      show (0 * 0 : ℕ) = 0 from rfl, pow_zero, one_mul, Polynomial.mul_coeff_zero]
    exact mul_ne_zero hca hcb
  exact not_mu3Dvd_phi2_of_even_grade h2 hq hexab heven hcab hdvd

/-! ## M3-KP4 outputs -/

/-- `Φ₂ = keyAt 2` is a key polynomial for the landed μ₃ value. -/
theorem s2Mu3KeyPoly_Φ₂ :
    S2Mu3KeyPoly h2 hq (s2DepthTwoKeyAt h2 hq 2) := by
  refine ⟨s2Φ₂_monic h2 hq, mu3Minimal_phi2 h2 hq, ?_⟩
  exact ⟨(s2Φ₂_monic h2 hq).ne_zero, not_mu3Dvd_phi2_one h2 hq,
    fun a b hab => mu3Dvd_phi2_or h2 hq a b hab⟩

/-- The carried key's normalized μ₃ residual is the unit polynomial. -/
theorem s2Mu3NormRes_Φ₂ :
    s2Mu3NormRes h2 hq (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) = 1 :=
  s2Mu3NormRes_key h2 hq

/-- Regression tooth: the same carried polynomial reads as `1` at μ₃ but as `X+1` at μ₂. -/
theorem tooth_Φ₂_mu3_vs_mu2 :
    s2Mu3NormRes h2 hq (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) = 1 ∧
      s2NormRes h2 hq (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) = Polynomial.X + 1 := by
  constructor
  · exact s2Mu3NormRes_Φ₂ h2 hq
  · rw [s2DepthTwoKeyAt_two h2 hq]
    exact s2NormRes_composedKey h2 hq

end S2

end Uniformity.Density.Tower.C132kp4

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132kp4.s2Mu3KeyPoly_Φ₂
#print axioms Uniformity.Density.Tower.C132kp4.s2Mu3NormRes_Φ₂
#print axioms Uniformity.Density.Tower.C132kp4.tooth_Φ₂_mu3_vs_mu2

end AxCheck
