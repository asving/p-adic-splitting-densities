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

end Uniformity.Density.Tower.C132rp10b

section AxCheck

#print axioms Uniformity.Density.Tower.C132rp10b.s2Hgt₂_corr
#print axioms Uniformity.Density.Tower.C132rp10b.g8_dev_zero

end AxCheck
