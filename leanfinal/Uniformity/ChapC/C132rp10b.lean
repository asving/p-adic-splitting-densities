/-
[M3-RP10b, 2026-08-27] — the non-recipe `normalized_exists` discharge (orchestrator
landing; the calibrated route of `runs/wave-b/launch_wave_20260827_2207.sh`'s MRP10B
brief).  STAGE A: the exact μ₃ grade of the recipe candidate.

The candidate is RP-10's own `g₈ := Φ₂² − 2⁴·Φ′` (`C132rp10.lean` — monic and degree 8
are landed there).  The correction `2⁴Φ′` has inner μ₂-height
`4·h₂(C 2) + h₂(Φ′) = 4·4 + 5 = 21`, so BOTH development slots of `g₈` sit on the μ₃
grade-42 line (`j = 0`: `2·21 + 21·0`; `j = 2`: `2·0 + 21·2`) — grade `42 = e′·u′` is the
honest corrected grade (the printed `21` is machine-impossible: RP-10's
`s2Mu3_recipe_correction_input_impossible`).
-/
import Uniformity.ChapC.C132sg

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132rp10b

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130np0 Uniformity.Density.Tower.C130nv2
open Uniformity.Density.Tower.C130nv3
open Uniformity.Density.Tower.C132nv0 Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C132nv6
open Uniformity.Density.Tower.C132rp0 Uniformity.Density.Tower.C80
open Uniformity.Density.Tower.C130rp0 Uniformity.Density.Tower.C130rp1
open Uniformity.Density.Tower.C130rp4 Uniformity.Density.Tower.C130rp8
open Uniformity.Density.Tower.C132rp1 Uniformity.Density.Tower.C132rp2
open Uniformity.Density.Tower.C132rp3 Uniformity.Density.Tower.C132rp6
open Uniformity.Density.Tower.C132rp8 Uniformity.Density.Tower.C130kp0
open Uniformity.Density.Tower.C132rp10 Uniformity.Density.Tower.C132fd0
open Uniformity.Density.Tower.C132sg Uniformity.Density.Tower.C132kp0

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- the recipe candidate, RP-10's own `g₈ = Φ₂² − 2⁴Φ′`. -/
noncomputable def g8 : Polynomial O :=
  (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ 2 -
    Polynomial.C ((2 : O) ^ 4) * (s2DepthTwoKeyChain h2 hq).keyAt 1

/-- the correction summand. -/
noncomputable def corr : Polynomial O :=
  Polynomial.C ((2 : O) ^ 4) * (s2DepthTwoKeyChain h2 hq).keyAt 1

theorem g8_eq : g8 h2 hq =
    (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ 2 - corr h2 hq := rfl

/-- `keyAt 1` of the depth-two chain is the frame key. -/
theorem corr_eq : corr h2 hq =
    Polynomial.C ((2 : O) ^ 4) * ((s2Frame h2 hq).key : Polynomial O) := rfl

/-- **the inner μ₂ height of the correction is `21`**: `4·4 + 5`. -/
theorem s2Hgt₂_corr : s2Hgt₂ h2 hq (corr h2 hq) = ((21 : ℤ) : WithTop ℤ) := by
  rw [corr_eq, show ((2 : O) ^ 4) = 2 * 2 * 2 * 2 by ring, map_mul, map_mul, map_mul]
  rw [s2Hgt₂_mul h2 hq, s2Hgt₂_mul h2 hq, s2Hgt₂_mul h2 hq, s2Hgt₂_mul h2 hq,
    s2Hgt₂_C_two h2 hq, s2Hgt₂_key h2 hq]
  norm_num

/-! ## STAGE B — the digit and the exact μ₃ grade `42` -/

/-- the `j = 0` digit of `g₈` is `−corr` (the correction survives reduction whole:
`deg corr = 3 < 4`). -/
theorem g8_dev_zero :
    dev (s2DepthTwoKeyAt h2 hq 2) (g8 h2 hq) 0 = -(corr h2 hq) := by
  have hmon : (s2DepthTwoKeyAt h2 hq 2 : Polynomial O).Monic := s2Φ₂_monic h2 hq
  have hsub : g8 h2 hq = (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ 2 + -(corr h2 hq) := by
    rw [g8_eq]; ring
  rw [hsub, dev_add_of_monic hmon, dev_pow_self hmon
    (by rw [s2Φ₂_natDegree h2 hq]; norm_num) 2 0]
  rw [if_neg (by norm_num), zero_add, dev_neg hmon]
  congr 1
  show corr h2 hq %ₘ (s2DepthTwoKeyAt h2 hq 2) = corr h2 hq
  refine (Polynomial.modByMonic_eq_self_iff hmon).mpr ?_
  refine Polynomial.degree_lt_degree ?_
  rw [s2Φ₂_natDegree h2 hq]
  calc (corr h2 hq).natDegree
      ≤ (Polynomial.C ((2:O)^4)).natDegree
          + (((s2Frame h2 hq).key : Polynomial O)).natDegree := by
        rw [corr_eq]; exact Polynomial.natDegree_mul_le
    _ < 4 := by
        rw [Polynomial.natDegree_C]
        have : ((s2Frame h2 hq).key : Polynomial O).natDegree = 2 := by
          rw [C35b.key_eq h2 hq]; exact s2Key_natDegree
        omega

/-- the correction is nonzero (its μ₂ height is finite). -/
theorem corr_ne_zero : corr h2 hq ≠ (0 : Polynomial O) := by
  intro h0
  have := s2Hgt₂_corr h2 hq
  rw [h0] at this
  rw [s2Hgt₂_zero h2 hq] at this
  exact (by simp : ((⊤ : WithTop ℤ)) ≠ ((21 : ℤ) : WithTop ℤ)) this

/-- the inner reading of the correction, in `ℕ∞`: `dvSupp = 21`. -/
theorem dvSupp_corr : dvSupp (s2Frame h2 hq) (corr h2 hq) 5 2 = ((21 : ℕ) : ℕ∞) := by
  refine toZ_inj ?_
  have h : s2Hgt₂ h2 hq (corr h2 hq) = ((21 : ℤ) : WithTop ℤ) := s2Hgt₂_corr h2 hq
  rw [s2Hgt₂] at h
  rw [h, toZ_coe]
  norm_num

/-- the `dv2Hgt`/`dvSupp` bridge at the S2 level datum (nv3b's local idiom). -/
private theorem dv2Hgt_eq (A : Polynomial O) :
    dv2Hgt ((s2Tower h2 hq).levelDatum h2) A = dvSupp (s2Frame h2 hq) A 5 2 :=
  toZ_inj ((s2Hgt₂_eq_dv2Hgt h2 hq A).symm.trans (s2Hgt₂_eq_dvSupp h2 hq A))

/-- the correction is its own `j = 0` digit (`deg corr = 3 < 4`). -/
theorem corr_dev_zero :
    dev (s2DepthTwoKeyAt h2 hq 2) (corr h2 hq) 0 = corr h2 hq := by
  have h := g8_dev_zero h2 hq
  have hmon : (s2DepthTwoKeyAt h2 hq 2 : Polynomial O).Monic := s2Φ₂_monic h2 hq
  have hsub : g8 h2 hq = (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ 2 + -(corr h2 hq) := by
    rw [g8_eq]; ring
  rw [hsub, dev_add_of_monic hmon, dev_pow_self hmon
    (by rw [s2Φ₂_natDegree h2 hq]; norm_num) 2 0, if_neg (by norm_num), zero_add,
    dev_neg hmon] at h
  have := neg_injective h
  exact this

/-- the higher digits of the correction vanish. -/
theorem corr_dev_succ (j : ℕ) (hj : 1 ≤ j) :
    dev (s2DepthTwoKeyAt h2 hq 2) (corr h2 hq) j = 0 := by
  have hmon : (s2DepthTwoKeyAt h2 hq 2 : Polynomial O).Monic := s2Φ₂_monic h2 hq
  refine dev_eq_zero_of_lt hmon ?_ (corr h2 hq) j ?_
  · rw [s2Φ₂_natDegree h2 hq]; norm_num
  · rw [s2Φ₂_natDegree h2 hq]
    have hd : (corr h2 hq).natDegree < 4 := by
      calc (corr h2 hq).natDegree
          ≤ (Polynomial.C ((2:O)^4)).natDegree
              + (((s2Frame h2 hq).key : Polynomial O)).natDegree := by
            rw [corr_eq]; exact Polynomial.natDegree_mul_le
        _ < 4 := by
            rw [Polynomial.natDegree_C]
            have : ((s2Frame h2 hq).key : Polynomial O).natDegree = 2 := by
              rw [C35b.key_eq h2 hq]; exact s2Key_natDegree
            omega
    omega

/-- **the exact μ₃ grade of the correction is `42 = 2·21`, in `ℕ∞`**. -/
theorem dv2Supp_corr :
    dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2)
      (corr h2 hq) 21 2 = ((42 : ℕ) : ℕ∞) := by
  rw [dv2Supp]
  refine le_antisymm ?_ ?_
  · refine le_trans (Finset.inf_le (Finset.mem_range.mpr (Nat.succ_pos _))) ?_
    rw [dv2Pin, corr_dev_zero h2 hq, dv2Hgt_eq h2 hq, dvSupp_corr h2 hq]
    simp [nsmul_eq_mul]
    norm_num
  · refine Finset.le_inf fun j hj => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · rw [dv2Pin, corr_dev_zero h2 hq, dv2Hgt_eq h2 hq, dvSupp_corr h2 hq]
      simp [nsmul_eq_mul]
      norm_num
    · rw [dv2Pin, corr_dev_succ h2 hq j hj1, dv2Hgt_eq h2 hq,
        dvSupp_zero_eq_top _ _ (by norm_num)]
      simp

/-- **the exact μ₃ grade of the correction, value form**. -/
theorem s2Hgt₃_corr : s2Hgt₃ h2 hq (corr h2 hq) = ((42 : ℤ) : WithTop ℤ) := by
  rw [s2Hgt₃_eq_dv2Supp h2 hq, dv2Supp_corr h2 hq, toZ_coe]
  norm_num

/-- negation invariance of the μ₃ grade. -/
theorem s2Hgt₃_neg (f : Polynomial O) : s2Hgt₃ h2 hq (-f) = s2Hgt₃ h2 hq f := by
  rw [s2Hgt₃_eq_dv2Supp h2 hq, s2Hgt₃_eq_dv2Supp h2 hq,
    dv2Supp_neg _ (s2Φ₂_monic h2 hq)]

/-- **the exact μ₃ grade of `g₈` is `42`**. -/
theorem s2Hgt₃_g8 : s2Hgt₃ h2 hq (g8 h2 hq) = ((42 : ℤ) : WithTop ℤ) := by
  have hsub : g8 h2 hq = (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ 2 + -(corr h2 hq) := by
    rw [g8_eq]; ring
  have hpow : s2Hgt₃ h2 hq ((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ 2)
      = ((42 : ℤ) : WithTop ℤ) := by
    rw [pow_two, s2Hgt₃_mul_all h2 hq, s2Hgt₃_Φ₂ h2 hq]
    norm_num
  have hge : ((42 : ℤ) : WithTop ℤ) ≤ s2Hgt₃ h2 hq (g8 h2 hq) := by
    have h := s2Hgt₃_add_ge h2 hq ((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ 2)
      (-(corr h2 hq))
    rw [← hsub, hpow, s2Hgt₃_neg h2 hq, s2Hgt₃_corr h2 hq, min_self] at h
    exact h
  have hle : s2Hgt₃ h2 hq (g8 h2 hq) ≤ ((42 : ℤ) : WithTop ℤ) := by
    rw [s2Hgt₃_eq_dv2Supp h2 hq]
    have hslot : dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2)
        (g8 h2 hq) 21 2 ≤ ((42 : ℕ) : ℕ∞) := by
      rw [dv2Supp]
      refine le_trans (Finset.inf_le (Finset.mem_range.mpr (Nat.succ_pos _))) ?_
      rw [dv2Pin, g8_dev_zero h2 hq, dv2Hgt_eq h2 hq, dvSupp_neg, dvSupp_corr h2 hq]
      simp [nsmul_eq_mul]
      norm_num
    calc toZ (dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2)
          (g8 h2 hq) 21 2)
        ≤ toZ ((42 : ℕ) : ℕ∞) := toZ_le_toZ_iff.mpr hslot
      _ = ((42 : ℤ) : WithTop ℤ) := by rw [toZ_coe]; norm_num
  exact le_antisymm hle hge

/-- the candidate is at exact μ₃ grade `42`. -/
theorem g8_exactGrade : S2Mu3ExactGrade h2 hq 42 (g8 h2 hq) := by
  show s2Hgt₃ h2 hq (g8 h2 hq) = ((42 : ℕ) : WithTop ℤ)
  rw [s2Hgt₃_g8 h2 hq]
  norm_num

/-! ## STAGE C, part 1 — the μ₂ leaf: the graded read of the correction is `1` -/

/-- the constant factor sits at exact μ₂ grade `16`. -/
theorem exactGrade_C_two_pow :
    S2ExactGrade h2 hq 16 (Polynomial.C ((2 : O) ^ 4)) := by
  unfold S2ExactGrade
  rw [show ((2 : O) ^ 4) = 2 * 2 * 2 * 2 by ring, map_mul, map_mul, map_mul,
    s2Hgt₂_mul h2 hq, s2Hgt₂_mul h2 hq, s2Hgt₂_mul h2 hq, s2Hgt₂_C_two h2 hq]
  norm_num

/-- the μ₂ graded read of the constant is a nonzero constant. -/
theorem gradedRes_C_two_pow_eq_C :
    s2GradedRes h2 hq 16 (Polynomial.C ((2 : O) ^ 4))
      = Polynomial.C ((s2GradedRes h2 hq 16 (Polynomial.C ((2 : O) ^ 4))).coeff 0) := by
  refine (Polynomial.eq_C_of_natDegree_le_zero ?_).trans rfl
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
  refine s2GradedRes_coeff_eq_zero_of_natDegree_lt h2 hq _ ?_
  rw [Polynomial.natDegree_C]
  omega

/-- the μ₂ graded read of the correction collapses to `1` (two-element field). -/
theorem s2GradedRes_corr : s2GradedRes h2 hq 21 (corr h2 hq) = 1 := by
  have hmul := s2GradedRes_mul_of_exact h2 hq (exactGrade_C_two_pow h2 hq)
    (tooth_key h2 hq)
  have h21 : (16 : ℕ) + 5 = 21 := by norm_num
  rw [h21] at hmul
  have hcorr : corr h2 hq
      = Polynomial.C ((2 : O) ^ 4) * ((s2Frame h2 hq).key : Polynomial O) := corr_eq h2 hq
  rw [hcorr, hmul, tooth_gradedRes_key h2 hq, mul_one,
    show (16 : ℕ) % 2 * (5 % 2) = 0 from by norm_num, pow_zero, one_mul]
  have hc0 : (s2GradedRes h2 hq 16 (Polynomial.C ((2 : O) ^ 4))).coeff 0 ≠ 0 := by
    refine s2GradedRes_coeff_zero_ne_zero_of_exact h2 hq (exactGrade_C_two_pow h2 hq) ?_
    rw [Polynomial.natDegree_C]
    norm_num
  rw [gradedRes_C_two_pow_eq_C h2 hq, s2Fld₂_eq_one_of_ne_zero h2 hq hc0]
  rfl

/-! ## STAGE C, part 2 — the μ₃ residual of `g₈` is `X + 1`, and the hex package -/

/-- `Φ₂` sits at exact μ₃ grade `21`. -/
theorem Φ₂_exactGrade : S2Mu3ExactGrade h2 hq 21 (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) := by
  show s2Hgt₃ h2 hq _ = _
  rw [s2Hgt₃_Φ₂ h2 hq]
  norm_num

/-- `−corr` sits at exact μ₃ grade `42`. -/
theorem neg_corr_exactGrade : S2Mu3ExactGrade h2 hq 42 (-(corr h2 hq)) := by
  show s2Hgt₃ h2 hq _ = _
  rw [s2Hgt₃_neg h2 hq, s2Hgt₃_corr h2 hq]
  norm_num

/-- the μ₃ graded residual of the carried key is `1`, polynomial form (eq (11)'s read,
assembled from RP-1's coefficient tooth). -/
theorem mu3GradedRes_Φ₂ :
    s2Mu3GradedRes h2 hq 21 (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) = 1 := by
  have hmon : (s2DepthTwoKeyAt h2 hq 2 : Polynomial O).Monic := s2Φ₂_monic h2 hq
  refine Polynomial.ext fun t => ?_
  rw [s2Mu3GradedRes_coeff h2 hq]
  match t with
  | 0 => rw [tooth_mu3Coeff_Φ₂ h2 hq, Polynomial.coeff_one]; norm_num
  | 1 =>
    rw [Polynomial.coeff_one, if_neg (by norm_num)]
    refine s2Mu3Coeff_eq_zero_of_dv2Pin_top h2 hq ?_
    rw [dv2Pin, show 21 % 2 + 2 * 1 = 3 from by norm_num]
    have hdev : dev (s2DepthTwoKeyAt h2 hq 2) (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) 3
        = 0 := by
      refine dev_eq_zero_of_lt hmon ?_ _ 3 ?_
      · rw [s2Φ₂_natDegree h2 hq]; norm_num
      · rw [s2Φ₂_natDegree h2 hq]; norm_num
    rw [hdev, dv2Hgt_eq h2 hq, dvSupp_zero_eq_top _ _ (by norm_num)]
  | (n+2) =>
    rw [Polynomial.coeff_one, if_neg (by omega)]
    refine s2Mu3Coeff_eq_zero_of_natDegree_lt h2 hq ?_
    rw [s2Φ₂_natDegree h2 hq]
    omega

/-- the μ₃ graded residual of `Φ₂²` at grade `42` is `X` (the odd×odd carry). -/
theorem mu3GradedRes_Φ₂_sq :
    s2Mu3GradedRes h2 hq 42 ((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ 2)
      = Polynomial.X := by
  have h := (s2Mu3_graded_mul_twisted h2 hq 21 21
    (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) (s2DepthTwoKeyAt h2 hq 2 : Polynomial O)
    (Φ₂_exactGrade h2 hq) (Φ₂_exactGrade h2 hq)).2
  rw [show (21 : ℕ) + 21 = 42 from by norm_num, ← pow_two] at h
  rw [h, mu3GradedRes_Φ₂ h2 hq]
  norm_num

/-- the μ₂ pin of `−corr`'s zero digit is `21`. -/
theorem neg_corr_pin :
    dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2)
      (-(corr h2 hq)) 0 = ((21 : ℕ) : ℕ∞) := by
  have hmon : (s2DepthTwoKeyAt h2 hq 2 : Polynomial O).Monic := s2Φ₂_monic h2 hq
  rw [dv2Pin, dev_neg hmon, corr_dev_zero h2 hq, dv2Hgt_eq h2 hq, dvSupp_neg,
    dvSupp_corr h2 hq]

/-- the μ₃ graded residual of `−corr` at grade `42` is `1` (the correction's read
survives with value `1`: the minus dies in the two-element field). -/
theorem mu3GradedRes_neg_corr :
    s2Mu3GradedRes h2 hq 42 (-(corr h2 hq)) = 1 := by
  have hmon : (s2DepthTwoKeyAt h2 hq 2 : Polynomial O).Monic := s2Φ₂_monic h2 hq
  refine Polynomial.ext fun t => ?_
  rw [s2Mu3GradedRes_coeff h2 hq]
  match t with
  | 0 =>
    have hgate : S2Mu3SlotOnGrade h2 hq 42 (-(corr h2 hq)) (42 % 2 + 2 * 0) := by
      refine (s2Mu3SlotOnGrade_iff h2 hq).mpr ⟨21, ?_, by norm_num⟩
      rw [show 42 % 2 + 2 * 0 = 0 from by norm_num]
      exact neg_corr_pin h2 hq
    have hpin : dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2)
        (-(corr h2 hq)) (42 % 2 + 2 * 0) = ((21 : ℕ) : ℕ∞) := by
      rw [show 42 % 2 + 2 * 0 = 0 from by norm_num]
      exact neg_corr_pin h2 hq
    rw [s2Mu3Coeff_eq_eval h2 hq hgate hpin]
    rw [show 42 % 2 + 2 * 0 = 0 from by norm_num, dev_neg hmon, corr_dev_zero h2 hq]
    have hle : ((21 : ℕ) : ℕ∞) ≤ dvSupp (s2Frame h2 hq) (corr h2 hq) 5 2 := by
      rw [dvSupp_corr h2 hq]
    rw [s2GradedRes_neg_of_le h2 hq hle, s2GradedRes_corr h2 hq]
    rw [Polynomial.coeff_one, if_pos rfl]
    simp only [Polynomial.eval_neg, Polynomial.eval_one]
    exact (s2Fld₂_eq_one_of_ne_zero h2 hq (neg_ne_zero.mpr one_ne_zero))
  | 1 =>
    rw [Polynomial.coeff_one, if_neg (by norm_num)]
    refine s2Mu3Coeff_eq_zero_of_dv2Pin_top h2 hq ?_
    rw [dv2Pin, show 42 % 2 + 2 * 1 = 2 from by norm_num, dev_neg hmon,
      corr_dev_succ h2 hq 2 (by norm_num), neg_zero, dv2Hgt_eq h2 hq,
      dvSupp_zero_eq_top _ _ (by norm_num)]
  | (n+2) =>
    rw [Polynomial.coeff_one, if_neg (by omega)]
    refine s2Mu3Coeff_eq_zero_of_natDegree_lt h2 hq ?_
    rw [Polynomial.natDegree_neg]
    have hd : (corr h2 hq).natDegree < 4 := by
      calc (corr h2 hq).natDegree
          ≤ (Polynomial.C ((2:O)^4)).natDegree
              + (((s2Frame h2 hq).key : Polynomial O)).natDegree := by
            rw [corr_eq]; exact Polynomial.natDegree_mul_le
        _ < 4 := by
            rw [Polynomial.natDegree_C]
            have : ((s2Frame h2 hq).key : Polynomial O).natDegree = 2 := by
              rw [C35b.key_eq h2 hq]; exact s2Key_natDegree
            omega
    omega

/-- ★ **the μ₃ graded residual of `g₈` at grade `42` is `X + 1`**. -/
theorem mu3GradedRes_g8 :
    s2Mu3GradedRes h2 hq 42 (g8 h2 hq) = Polynomial.X + 1 := by
  have hsub : g8 h2 hq = (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ 2 + -(corr h2 hq) := by
    rw [g8_eq]; ring
  have hpow : S2Mu3ExactGrade h2 hq 42
      ((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ 2) := by
    show s2Hgt₃ h2 hq _ = _
    rw [pow_two, s2Hgt₃_mul_all h2 hq, s2Hgt₃_Φ₂ h2 hq]
    norm_num
  have hg8 : S2Mu3ExactGrade h2 hq 42 (g8 h2 hq) := g8_exactGrade h2 hq
  rw [hsub]
  rw [s2Mu3GradedRes_add h2 hq hpow (neg_corr_exactGrade h2 hq) (by rw [← hsub]; exact hg8)]
  rw [mu3GradedRes_Φ₂_sq h2 hq, mu3GradedRes_neg_corr h2 hq]

/-- ★★ **the normalized μ₃ residual of `g₈` is `X + 1`** — the non-recipe evaluation the
whole node exists for. -/
theorem s2Mu3NormRes_g8 :
    s2Mu3NormRes h2 hq (g8 h2 hq) = Polynomial.X + 1 := by
  rw [s2Mu3NormRes_of_exact h2 hq (g8_exactGrade h2 hq), mu3GradedRes_g8 h2 hq]
  have htr : (Polynomial.X + 1 : Polynomial ((s2DepthTwo h2 hq).fld 2)).natTrailingDegree
      = 0 := by
    refine Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr ?_)
    simp
  rw [htr]
  rfl

/-! ## The hex package — `normalized_exists` discharged -/

/-- ★★★ **M3-RP10b**: the `hex` hypothesis of `C132fd0.s2SourceLawsTwo_of`, discharged —
every admissible degree-one residual is `X + 1` (RP-10's two-element collapse), and `g₈`
is its monic degree-8 witness. -/
theorem s2Mu3_hex :
    ∀ ψ : Polynomial ((s2DepthTwo h2 hq).fld 2),
      ψ.Monic → Irreducible ψ → ψ.natDegree = 1 → ψ.coeff 0 ≠ 0 →
        ∃ g : Polynomial O, g.Monic ∧
          g.natDegree = 2 * 1 * (((s2DepthTwoKeyChain h2 hq).keyAt 2).natDegree) ∧
          s2Mu3NormRes h2 hq g = ψ := by
  intro ψ hm hirr hd hc
  have hψ : ψ = Polynomial.X + 1 :=
    s2Mu3_unique_admissible_linear h2 hq ψ hm hd hc
  refine ⟨g8 h2 hq, s2Mu3_gEight_monic h2 hq, ?_, ?_⟩
  · have hK : ((s2DepthTwoKeyChain h2 hq).keyAt 2 : Polynomial O)
        = (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) := rfl
    rw [hK, s2Φ₂_natDegree h2 hq]
    have h8 := s2Mu3_gEight_natDegree h2 hq
    show (g8 h2 hq).natDegree = 2 * 1 * 4
    rw [show (2 : ℕ) * 1 * 4 = 8 from by norm_num]
    exact h8
  · rw [hψ]
    exact s2Mu3NormRes_g8 h2 hq

/-- ★★★ the μ₃ depth-2 calculus, now conditional on ONLY the converse (M3-KP6b). -/
theorem s2Mu3_calculus_nonempty_of_conv
    (hconv : ∀ g h : Polynomial O,
      S2Mu3KeyPoly h2 hq g → S2Mu3KeyPoly h2 hq h →
        s2Mu3NormRes h2 hq g = s2Mu3NormRes h2 hq h → S2Mu3InitialEquiv h2 hq g h) :
    Nonempty (FGMNCalculus (s2DepthTwo h2 hq) 2 1 21) :=
  s2Mu3_calculus_nonempty_of h2 hq (s2Mu3_hex h2 hq) hconv

end Uniformity.Density.Tower.C132rp10b

section AxCheck

#print axioms Uniformity.Density.Tower.C132rp10b.s2Hgt₂_corr
#print axioms Uniformity.Density.Tower.C132rp10b.g8_dev_zero
#print axioms Uniformity.Density.Tower.C132rp10b.s2Hgt₃_g8
#print axioms Uniformity.Density.Tower.C132rp10b.g8_exactGrade
#print axioms Uniformity.Density.Tower.C132rp10b.s2GradedRes_corr
#print axioms Uniformity.Density.Tower.C132rp10b.mu3GradedRes_g8
#print axioms Uniformity.Density.Tower.C132rp10b.s2Mu3NormRes_g8
#print axioms Uniformity.Density.Tower.C132rp10b.s2Mu3_hex
#print axioms Uniformity.Density.Tower.C132rp10b.s2Mu3_calculus_nonempty_of_conv

end AxCheck
