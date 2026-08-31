/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I10RungLift3W
import Uniformity.ChapC.C136e1
import Uniformity.ChapC.C136e2

/-!
# Uniformity.ChapI.I10RungLift4 — UNIT R4K: the rung-4 key lift — the μ₅ coefficient
layer, the level-5 key, and the fire to rung 4

W3P (`I10RungLift3W`) inhabited the keystone tower to rung 3+ and named the honest
rung-4 remainder: the KEY LIFT's three data.  Since W3P's forecast, the D4 campaign
(C136e1/C136e2) LANDED the μ₅ coefficient layer it anticipated as the "D4-13..16 gap"
— `s2Mu5Coeff`/`s2Mu5GradedRes`/`s2Mu5NormRes`, the leaf `s2Mu5Leaf = g16 − Λ` (monic,
degree 16, exact μ₅ grade `171`, normalized residual `X + 1`), and the μ₅ calculus
`s2Mu5_calculus_nonempty` at `(1,1,171)`.  This file lands the three DICTIONARY data
one rung above W3P's recipe and fires:

* §1 **the μ₄ eval-1 read bridge** (the W-c analogue's engine, one level down):
  `eval 1 (nextRead s2Carrier s2Key m g) = eval 1 (s2Mu4GradedRes m g)` under a
  `dv3Supp` floor — the ℓ = 2 slot dilation of the rung-2 read (W3P's `X ↦ X²`) is
  INVISIBLE to eval-1; proved by the parity-slot reindex `j = m % 2 + 2t` against the
  floor form of WCC's coefficient dictionary.
* §2 **the μ₅ coefficient dictionary at the rung-3 pack** (the W-c analogue):
  `s2Mu5Coeff β f t = wcoeff C₃ P₃ β f t` under a `dv4Supp` floor — at `ℓ₅ = 1` the
  slot index needs NO dilation, so the rung-3 iterated read IS the landed μ₅ graded
  residual as a POLYNOMIAL (`s2_nextRead3_eq_mu5GradedRes`).  The root: the leaf's
  residual is `X + 1`, and eval-1 dies by the char-2 tooth.
* §3 **the grade dictionary** (the W-b analogue): `nextSupp C₃ P₃ f = dv4Supp … f 171 1`
  for EVERY `f` (the same two-step identification as W3P §2, one level up: the rung-3
  carrier's support is `dv3Supp` by W3P's landed dictionary, and `dv4Pin` is
  definitionally `dv3Supp ∘ dev g16`), then `nextSupp C₃ P₃ (s2Mu5Leaf) = 171` from the
  landed `s2Mu5Leaf_exactGrade`.
* §4 ★★ **the fire**: `s2RungLift4 := RungLift.ofRootF1 …` — the S2 rung-4 `RungLift`
  at key `s2Mu5Leaf` (monic, degree 16 = the fence `1·16` exactly), exact iterated
  grade `171`, root `1` of the residual `X + 1`, next ring `fld 2` ITSELF (f′ = 1
  again), next slopes `(u₆, ℓ₆) = (172, 1)`; `s2LiftAt4`; `s2Rung4PackAt`;
  `towerPacks` reaches rung 4 at index 2; the level-5→6 weighted convolution law
  fires (`s2_rung4_wcoeff_mul`); the rung-5 CARRIER exists unconditionally.

**The μ₆ slopes, honestly.**  NO landed μ₆ table exists (no `dv5` layer anywhere in the
corpus), and per the [G5F 2026-08-28] record none SHOULD: the `(1,1,171)` triple is
TERMINAL operator data over the depth-four tower — the keystone's arising depth is 4/5
and the leaf is the LAST key.  The fired slopes `(172, 1) = (kgrade₅ + 1, 1)` are the
strict-floor refinement pattern — the exact genre of [G5F]'s own `(171, 1) =
(kgrade₄ + 1, 1)` — pinned by `s2Rung4_slope_floor : u₆ = kgrade₅ + 1` (rfl).  They are
PACKAGING data for the rung-4 pack (its `strict` field and any further lift); no μ₆
anti-drift tie is claimed, because there is no landed table to tie against.

**Coverage after the fire.**  The deepTwist bank's tower side is COMPLETE at the
keystone genre: rung 2 (key `g8`, slopes `(85,2)`), rung 3 (key `g16`, slopes
`(171,1)`), rung 4 (key `s2Mu5Leaf`, slopes `(172,1)`) — every landed key of the
depth-four chain and its terminal [G5F] refinement carries a rung pack, and
`towerPacks` reaches all of them.  The remaining `s2Rung5Carrier` is unconditional;
no rung-5 KEY exists in the source to lift (the tower terminates at the leaf).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.I10rl4

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C132nv0 Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C132rp10b Uniformity.Density.Tower.C80
open Uniformity.Density.Tower.C136d0 Uniformity.Density.Tower.C136d1
open Uniformity.Density.Tower.C136d2 Uniformity.Density.Tower.C136t
open Uniformity.Density.Tower.C136e0 Uniformity.Density.Tower.C136e1
open Uniformity.Density.Tower.C136e2
open Uniformity.Density.Tower.I10wcc
open Uniformity.Density.Tower.I10rung
open Uniformity.Density.Tower.I10rl3
open Uniformity.Density.Tower.I10rl3w

/-! ## §0 — local guard twins (the standing local-twin convention)

`wcoeff_of_guard`/`wcoeff_of_not_guard` (7th corpus repetition) and W3P's private
`nextSupp_eq_inf_range` (2nd repetition) — all flagged for the standing dedup pass. -/

section GenericTwins

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {K : Type*} [CommRing K]

private theorem wcoeff_of_guard (C : WeightedCarrier O K) {u ℓ : ℕ} (P : CarrierKey C u ℓ)
    {β J : ℕ} {f : Polynomial O} (h1 : u * J ≤ β) (h2 : ℓ ∣ (β - u * J)) :
    wcoeff C P β f J = C.read ((β - u * J) / ℓ) (dev P.key f J) := if_pos ⟨h1, h2⟩

private theorem wcoeff_of_not_guard (C : WeightedCarrier O K) {u ℓ : ℕ}
    (P : CarrierKey C u ℓ) {β J : ℕ} {f : Polynomial O}
    (h : ¬ (u * J ≤ β ∧ ℓ ∣ (β - u * J))) : wcoeff C P β f J = 0 := if_neg h

/-- local twin of W3P's private `nextSupp_eq_inf_range` (verbatim): the ℕ-indexed
`nextSupp` infimum truncates to the development range — past-degree slots price `⊤`. -/
private theorem nextSupp_eq_inf_range (C : WeightedCarrier O K) {u ℓ : ℕ}
    (P : CarrierKey C u ℓ) (f : Polynomial O) :
    nextSupp C P f = (Finset.range (f.natDegree + 1)).inf
      (fun j => (ℓ : ℕ∞) * C.supp (dev P.key f j) + ((u * j : ℕ) : ℕ∞)) := by
  refine le_antisymm (Finset.le_inf fun j _ => iInf_le _ j) (le_iInf fun j => ?_)
  by_cases hj : j ≤ f.natDegree
  · exact Finset.inf_le (Finset.mem_range.mpr (by omega))
  · have hdev : dev P.key f j = 0 :=
      dev_eq_zero_of_lt P.monic P.deg_pos f j
        (lt_of_lt_of_le (not_le.mp hj) (Nat.le_mul_of_pos_right j P.deg_pos))
    have htop : (ℓ : ℕ∞) * ⊤ = ⊤ :=
      WithTop.mul_top (Nat.cast_ne_zero.mpr P.ell_pos.ne')
    rw [hdev, C.supp_zero, htop, top_add]
    exact le_top

end GenericTwins

/-! ## §1 — the μ₄ eval-1 read bridge (the W-c analogue's engine, one level down) -/

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- floor form of WCC's private `s2Mu4Coeff_eq_wcoeff` (the exact-grade hypothesis
relaxed to the cleared-support floor it actually uses): the landed μ₄ coefficient IS the
rung-2 carrier coefficient at the parity abscissa `m % 2 + 2t`. -/
private theorem s2Mu4Coeff_eq_wcoeff_of_le {β : ℕ} {g : Polynomial O}
    (hβ : (β : ℕ∞) ≤ dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2)
      21 2 (g8 h2 hq) g 85 2) (t : ℕ) :
    s2Mu4Coeff h2 hq β g t
      = wcoeff (s2Carrier h2 hq) (I10wcc.s2Key h2 hq) β g (β % 2 + 2 * t) := by
  rcases Nat.lt_or_ge β (85 * (β % 2 + 2 * t)) with hlt | hge
  · rw [s2Mu4Coeff_eq_zero_of_grade_lt h2 hq hlt,
      wcoeff_of_not_guard (s2Carrier h2 hq) (I10wcc.s2Key h2 hq) (by omega)]
  · have hdvd : 2 ∣ (β - 85 * (β % 2 + 2 * t)) := by omega
    have hm2 : 2 * ((β - 85 * (β % 2 + 2 * t)) / 2) + 85 * (β % 2 + 2 * t) = β := by
      omega
    have hpin : (((β - 85 * (β % 2 + 2 * t)) / 2 : ℕ) : ℕ∞)
        ≤ dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
          (g8 h2 hq) g (β % 2 + 2 * t) :=
      le_dv3Pin_of_le_dv3Supp h2 hq (by norm_num) hβ hm2
    rw [s2Mu4Coeff_eq_eval_of_le h2 hq hm2 hpin,
      wcoeff_of_guard (s2Carrier h2 hq) (I10wcc.s2Key h2 hq) hge hdvd]
    rfl

/-- ★ **the μ₄ eval-1 read bridge**: under the cleared-support floor, the eval-1 read of
the abstract rung-2 iterated read IS the eval-1 read of the landed μ₄ graded residual —
the ℓ = 2 slot dilation (W3P's `X ↦ X²`) is invisible to eval-1.  The parity reindex
`j = m % 2 + 2t`: off-parity and past-line slots vanish on both sides. -/
private theorem eval_one_nextRead_eq_mu4 {m : ℕ} {g : Polynomial O}
    (hβ : (m : ℕ∞) ≤ dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2)
      21 2 (g8 h2 hq) g 85 2) :
    Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
        (nextRead (s2Carrier h2 hq) (I10wcc.s2Key h2 hq) m g)
      = Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2) (s2Mu4GradedRes h2 hq m g) := by
  have hL : nextRead (s2Carrier h2 hq) (I10wcc.s2Key h2 hq) m g
      = ∑ j ∈ Finset.range (m + 1),
          Polynomial.C (wcoeff (s2Carrier h2 hq) (I10wcc.s2Key h2 hq) m g j)
            * Polynomial.X ^ j := rfl
  have hR := s2Mu4GradedRes_eq_sum_range h2 hq m g (le_refl (m + 1))
  rw [hL, hR, Polynomial.eval_finsetSum, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, one_pow, mul_one]
  -- kill the off-guard slots on the left
  have hLfilter : ∑ j ∈ Finset.range (m + 1),
        wcoeff (s2Carrier h2 hq) (I10wcc.s2Key h2 hq) m g j
      = ∑ j ∈ (Finset.range (m + 1)).filter (fun j => 85 * j ≤ m ∧ j % 2 = m % 2),
          wcoeff (s2Carrier h2 hq) (I10wcc.s2Key h2 hq) m g j := by
    refine (Finset.sum_filter_of_ne fun j _ hne => ?_).symm
    by_contra hcon
    have hng : ¬ (85 * j ≤ m ∧ 2 ∣ (m - 85 * j)) := fun hg' => hcon (by omega)
    exact hne (wcoeff_of_not_guard (s2Carrier h2 hq) (I10wcc.s2Key h2 hq) hng)
  -- kill the past-line slots on the right (after the twin dictionary)
  have hRdict : ∑ t ∈ Finset.range (m + 1), s2Mu4Coeff h2 hq m g t
      = ∑ t ∈ Finset.range (m + 1),
          wcoeff (s2Carrier h2 hq) (I10wcc.s2Key h2 hq) m g (m % 2 + 2 * t) :=
    Finset.sum_congr rfl fun t _ => s2Mu4Coeff_eq_wcoeff_of_le h2 hq hβ t
  have hRfilter : ∑ t ∈ Finset.range (m + 1),
        wcoeff (s2Carrier h2 hq) (I10wcc.s2Key h2 hq) m g (m % 2 + 2 * t)
      = ∑ t ∈ (Finset.range (m + 1)).filter (fun t => 85 * (m % 2 + 2 * t) ≤ m),
          wcoeff (s2Carrier h2 hq) (I10wcc.s2Key h2 hq) m g (m % 2 + 2 * t) := by
    refine (Finset.sum_filter_of_ne fun t _ hne => ?_).symm
    by_contra hcon
    exact hne (wcoeff_of_not_guard (s2Carrier h2 hq) (I10wcc.s2Key h2 hq)
      (fun hg' => hcon hg'.1))
  rw [hLfilter, hRdict, hRfilter]
  -- the parity reindex between the two filtered supports
  refine Finset.sum_nbij' (i := fun j => (j - m % 2) / 2) (j := fun t => m % 2 + 2 * t)
    ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    rw [show m % 2 + 2 * ((a - m % 2) / 2) = a from by omega]

/-! ## §2 — the W-c analogue: the μ₅ coefficient dictionary at the rung-3 pack -/

/-- ★ **the μ₅ coefficient dictionary** (the W-c analogue's supply, one level above
WCC's `s2Mu4Coeff_eq_wcoeff`): under the level-5 cleared floor, the landed μ₅
coefficient IS the rung-3 carrier coefficient — at `ℓ₅ = 1` the slot index needs NO
dilation. -/
theorem s2Mu5Coeff_eq_wcoeff3 {β : ℕ} {f : Polynomial O}
    (hβ : (β : ℕ∞) ≤ dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2)
      21 2 (g8 h2 hq) 85 2 (g16 h2 hq) f 171 1) (t : ℕ) :
    s2Mu5Coeff h2 hq β f t
      = wcoeff (s2Rung3Pack h2 hq).C (s2Rung3Pack h2 hq).P β f t := by
  rcases Nat.lt_or_ge β (171 * t) with hlt | hge
  · rw [s2Mu5Coeff_eq_zero_of_grade_lt h2 hq hlt,
      wcoeff_of_not_guard (s2Rung3Pack h2 hq).C (s2Rung3Pack h2 hq).P (by omega)]
  · have hm : 1 * (β - 171 * t) + 171 * t = β := by omega
    have hpin := le_dv4Pin_of_le_dv4Supp h2 hq hβ hm
    rw [s2Mu5Coeff_eq_eval_of_le h2 hq hm hpin,
      wcoeff_of_guard (s2Rung3Pack h2 hq).C (s2Rung3Pack h2 hq).P hge (one_dvd _)]
    show Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
        (s2Mu4GradedRes h2 hq (β - 171 * t) (dev (g16 h2 hq) f t))
      = Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
          (nextRead (s2Carrier h2 hq) (I10wcc.s2Key h2 hq) ((β - 171 * t) / 1)
            (dev (g16 h2 hq) f t))
    rw [Nat.div_one]
    exact (eval_one_nextRead_eq_mu4 h2 hq hpin).symm

/-- ★ **the rung-3 iterated read IS the μ₅ graded residual** — a POLYNOMIAL identity
(contrast W3P's rung-2 dictionary, where the read was the μ₄ residual dilated `X ↦ X²`;
at `ℓ₅ = 1` there is no dilation). -/
theorem s2_nextRead3_eq_mu5GradedRes {β : ℕ} {f : Polynomial O}
    (hβ : (β : ℕ∞) ≤ dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2)
      21 2 (g8 h2 hq) 85 2 (g16 h2 hq) f 171 1) :
    nextRead (s2Rung3Pack h2 hq).C (s2Rung3Pack h2 hq).P β f
      = s2Mu5GradedRes h2 hq β f := by
  refine Polynomial.ext fun t => ?_
  rw [nextRead_coeff (s2Rung3Pack h2 hq).C (s2Rung3Pack h2 hq).P β f t,
    s2Mu5GradedRes_coeff h2 hq β f t]
  exact (s2Mu5Coeff_eq_wcoeff3 h2 hq hβ t).symm

/-- the leaf's μ₅ graded residual is `X + 1` (the graded form of the landed
`s2Mu5NormRes_leaf`; same landed rewrites, without the normalizer wrapper). -/
theorem s2_mu5GradedRes_leaf :
    s2Mu5GradedRes h2 hq 171 (s2Mu5Leaf h2 hq) = Polynomial.X + 1 := by
  have hsub : s2Mu5Leaf h2 hq = (g16 h2 hq : Polynomial O) + -(s2Mu5Lambda h2 hq) := by
    show (g16 h2 hq : Polynomial O) - s2Mu5Lambda h2 hq = _
    ring
  have hpow : S2Mu5ExactGrade h2 hq 171 (g16 h2 hq : Polynomial O) := tooth_g16 h2 hq
  have hnegΛ : S2Mu5ExactGrade h2 hq 171 (-(s2Mu5Lambda h2 hq)) := by
    show s2Hgt₅ h2 hq _ = _
    rw [s2Hgt₅_neg h2 hq]
    exact s2Mu5Lambda_exactGrade h2 hq
  have hleaf : S2Mu5ExactGrade h2 hq 171 (s2Mu5Leaf h2 hq) := s2Mu5Leaf_exactGrade h2 hq
  rw [hsub, s2Mu5GradedRes_add h2 hq hpow hnegΛ (hsub ▸ hleaf), s2Mu5GradedRes_key h2 hq,
    s2Mu5_recipe_negTooth_gradedRes h2 hq (s2Mu5Lambda_exactGrade h2 hq)
      (s2Mu5Lambda_natDegree_lt h2 hq)]

/-- ★ **the W-c analogue — the root dictionary at the leaf**:
`eval 1 (nextRead C₃ P₃ 171 s2Mu5Leaf) = 0` — the residual is the landed `X + 1`, and
the char-2 tooth kills it at `1`. -/
theorem s2_eval_one_nextRead3_leaf :
    Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
      (nextRead (s2Rung3Pack h2 hq).C (s2Rung3Pack h2 hq).P 171 (s2Mu5Leaf h2 hq)) = 0 := by
  rw [s2_nextRead3_eq_mu5GradedRes h2 hq
      (le_of_eq ((S2Mu5ExactGrade_iff_dv4Supp h2 hq).mp (s2Mu5Leaf_exactGrade h2 hq)).symm),
    s2_mu5GradedRes_leaf h2 hq, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  exact C130rp2.tooth_char_two h2 hq

/-! ## §3 — the W-b analogue: the grade dictionary `nextSupp = dv4Supp`, and the leaf
at `171` -/

/-- ★ **the rung-3 support dictionary** (for EVERY `f`): the abstract iterated support
at the rung-3 pack IS the landed level-4 cleared support `dv4Supp` at the μ₅ side
`(171, 1)` — term-for-term after the range truncation, since the rung-3 carrier's
support is `dv3Supp` (W3P's landed dictionary) and `dv4Pin = dv3Supp ∘ dev g16` by
definition. -/
theorem s2_nextSupp3_eq_dv4Supp (f : Polynomial O) :
    nextSupp (s2Rung3Pack h2 hq).C (s2Rung3Pack h2 hq).P f
      = dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
          85 2 (g16 h2 hq) f 171 1 := by
  rw [nextSupp_eq_inf_range, dv4Supp]
  refine Finset.inf_congr rfl fun j _ => ?_
  show ((1 : ℕ) : ℕ∞) * nextSupp (s2Carrier h2 hq) (I10wcc.s2Key h2 hq) (dev (g16 h2 hq) f j)
      + ((171 * j : ℕ) : ℕ∞)
    = 1 • dv4Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
        85 2 (g16 h2 hq) f j + ((171 : ℕ) : ℕ∞) * (j : ℕ∞)
  rw [s2_nextSupp_eq_dv3Supp h2 hq (dev (g16 h2 hq) f j), dv4Pin, dv4Hgt, nsmul_eq_mul]
  push_cast
  ring

/-- ★ **the W-b analogue at the witness**: `nextSupp C₃ P₃ (s2Mu5Leaf) = 171`, from the
landed `s2Mu5Leaf_exactGrade` through `S2Mu5ExactGrade_iff_dv4Supp`. -/
theorem s2_nextSupp3_leaf :
    nextSupp (s2Rung3Pack h2 hq).C (s2Rung3Pack h2 hq).P (s2Mu5Leaf h2 hq)
      = ((171 : ℕ) : ℕ∞) := by
  rw [s2_nextSupp3_eq_dv4Supp h2 hq]
  exact (S2Mu5ExactGrade_iff_dv4Supp h2 hq).mp (s2Mu5Leaf_exactGrade h2 hq)

/-! ## §4 — ★★ the fire: the S2 rung-4 `RungLift` + `towerPacks` at the keystone -/

/-- ★★ **the S2 rung-4 `RungLift`** — RL3's f′ = 1 closed form fired at the keystone one
rung above W3P: key `s2Mu5Leaf` (monic, degree 16 = the fence `1·16` exactly), exact
iterated grade `171` (§3), root `1` of the residual `X + 1` (§2), next ring `fld 2`
ITSELF (f′ = 1 again: no ring growth), next slopes `(172, 1)` with the strict floor
`1·171 < 172` (the [G5F] refinement-floor genre; no landed μ₆ table exists to tie — see
the file docstring). -/
noncomputable def s2RungLift4 :
    RungLift (s2Rung3Pack h2 hq) ((s2DepthTwo h2 hq).fld 2) 172 1 :=
  RungLift.ofRootF1 (s2Rung3Pack h2 hq) (s2Mu5Leaf_monic h2 hq)
    (by rw [s2Mu5Leaf_natDegree h2 hq]; norm_num)
    (by show (s2Mu5Leaf h2 hq).natDegree ≤ 1 * (g16 h2 hq : Polynomial O).natDegree
        rw [s2Mu5Leaf_natDegree h2 hq, g16_natDegree h2 hq])
    (by norm_num)
    (s2_nextSupp3_leaf h2 hq)
    (one_ne_zero : (1 : (s2DepthTwo h2 hq).fld 2) ≠ 0)
    (s2_eval_one_nextRead3_leaf h2 hq)
    (by norm_num)
    (by norm_num)

/-- ★ **the bundled fire** through RL3's §5 wrapper. -/
noncomputable def s2LiftAt4 : LiftAt O (s2Rung3PackAt h2 hq) :=
  haveI : IsDomain ((s2Rung3PackAt h2 hq).K) :=
    inferInstanceAs (IsDomain ((s2DepthTwo h2 hq).fld 2))
  liftAtOfRootF1 (s2Rung3PackAt h2 hq) (u' := 172) (ℓ' := 1) (s2Mu5Leaf_monic h2 hq)
    (by rw [s2Mu5Leaf_natDegree h2 hq]; norm_num)
    (by show (s2Mu5Leaf h2 hq).natDegree ≤ 1 * (g16 h2 hq : Polynomial O).natDegree
        rw [s2Mu5Leaf_natDegree h2 hq, g16_natDegree h2 hq])
    (by show Nat.gcd 171 1 = 1; norm_num)
    (show nextSupp (s2Rung3PackAt h2 hq).pack.C (s2Rung3PackAt h2 hq).pack.P
        (s2Mu5Leaf h2 hq) = ((171 : ℕ) : ℕ∞) from s2_nextSupp3_leaf h2 hq)
    (one_ne_zero : (1 : (s2DepthTwo h2 hq).fld 2) ≠ 0)
    (show Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
        (nextRead (s2Rung3PackAt h2 hq).pack.C (s2Rung3PackAt h2 hq).pack.P 171
          (s2Mu5Leaf h2 hq)) = 0 from s2_eval_one_nextRead3_leaf h2 hq)
    (by norm_num)
    (by norm_num)

/-- ★★ **the S2 rung-4 pack at the keystone** — the deepTwist bank's tower side
inhabited to rung 4: the LAST landed key (the [G5F] terminal refinement leaf). -/
noncomputable def s2Rung4PackAt : PackAt O := (s2LiftAt4 h2 hq).next

/-- rfl-pins: the rung-4 pack's slopes are `(172, 1)`, its key is the μ₅ leaf at grade
`171`, and its ring is `fld 2` again (f′ = 1: no ring growth). -/
theorem s2Rung4PackAt_u : (s2Rung4PackAt h2 hq).u = 172 := rfl

theorem s2Rung4PackAt_ell : (s2Rung4PackAt h2 hq).ℓ = 1 := rfl

theorem s2Rung4PackAt_key : (s2Rung4PackAt h2 hq).pack.P.key = s2Mu5Leaf h2 hq := rfl

theorem s2Rung4PackAt_kgrade : (s2Rung4PackAt h2 hq).pack.P.kgrade = 171 := rfl

/-- anti-drift tie: the fired rung-4 key's grade IS the tower's own μ₅ table value —
the landed exact μ₅ grade of the leaf (`C136e1.s2Mu5Leaf_exactGrade`). -/
theorem s2Rung4_kgrade_is_leaf_mu5_grade :
    S2Mu5ExactGrade h2 hq ((s2Rung4PackAt h2 hq).pack.P.kgrade)
      ((s2Rung4PackAt h2 hq).pack.P.key) :=
  s2Mu5Leaf_exactGrade h2 hq

/-- honesty pin for the μ₆ slopes: the fired next slope is EXACTLY the strict floor
`kgrade₅ + 1` (the [G5F] refinement-floor genre `(171,1) = (170+1, 1)`, one level up);
no landed μ₆ table exists to tie against. -/
theorem s2Rung4_slope_floor :
    (s2Rung4PackAt h2 hq).u = (s2Rung4PackAt h2 hq).pack.P.kgrade + 1 := rfl

/-- ★ **`towerPacks` reaches rung 4 at the keystone**: any step supplier extending the
two S2 lifts reaches the rung-4 pack at index 2. -/
theorem s2_towerPacks_rung4 (step : ∀ Q : PackAt O, LiftAt O Q)
    (h3 : step (s2Rung2PackAt h2 hq) = s2LiftAt3 h2 hq)
    (h4 : step (s2Rung3PackAt h2 hq) = s2LiftAt4 h2 hq) :
    towerPacks (s2Rung2PackAt h2 hq) step 2 = s2Rung4PackAt h2 hq := by
  rw [towerPacks_succ, s2_towerPacks_rung3 h2 hq step h3, h4]
  rfl

/-- ★ the tower side of the deepTwist bank at rung 4: the S2 rung-4 `RungLift`
EXISTS. -/
theorem s2_rungLift4_nonempty :
    Nonempty (RungLift (s2Rung3Pack h2 hq) ((s2DepthTwo h2 hq).fld 2) 172 1) :=
  ⟨s2RungLift4 h2 hq⟩

/-- the unbundled rung-4 pack. -/
noncomputable def s2Rung4Pack : RungPack O ((s2DepthTwo h2 hq).fld 2) 172 1 :=
  (s2RungLift4 h2 hq).pack

/-- ★ the rung-4 pack EXISTS at the keystone slopes `(172, 1)`. -/
theorem s2_rung4_pack_nonempty :
    Nonempty (RungPack O ((s2DepthTwo h2 hq).fld 2) 172 1) :=
  ⟨s2Rung4Pack h2 hq⟩

/-- ★ **the "4+": the rung-5 CARRIER exists unconditionally** (RUNG §6's `nextCarrier`
at the landed rung-4 pack).  There is NO rung-5 key to lift: per the [G5F] record the
`(1,1,171)` refinement is terminal — the leaf is the last key of the keystone tower, so
the tower side of the deepTwist bank is COMPLETE at this witness genre. -/
noncomputable def s2Rung5Carrier :
    WeightedCarrier O (Polynomial ((s2DepthTwo h2 hq).fld 2)) :=
  nextCarrier (s2Rung4Pack h2 hq)

/-- ★★ **the weighted convolution law at rung 4 of the keystone tower** — the
level-5→6 convolution, fired through the landed rung-4 pack. -/
theorem s2_rung4_wcoeff_mul {β β' : ℕ} {g z : Polynomial O}
    (hg : LineFloor (s2Rung4Pack h2 hq).C (s2Rung4Pack h2 hq).P β g)
    (hz : LineFloor (s2Rung4Pack h2 hq).C (s2Rung4Pack h2 hq).P β' z) (J : ℕ) :
    wcoeff (s2Rung4Pack h2 hq).C (s2Rung4Pack h2 hq).P (β + β') (g * z) J
      = ∑ j ∈ Finset.range (J + 1),
          wcoeff (s2Rung4Pack h2 hq).C (s2Rung4Pack h2 hq).P β g j
            * wcoeff (s2Rung4Pack h2 hq).C (s2Rung4Pack h2 hq).P β' z (J - j) :=
  wcoeff_mul _ _ hg hz J

end S2

end Uniformity.Density.Tower.I10rl4

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.I10rl4.s2Mu5Coeff_eq_wcoeff3
#print axioms Uniformity.Density.Tower.I10rl4.s2_nextRead3_eq_mu5GradedRes
#print axioms Uniformity.Density.Tower.I10rl4.s2_mu5GradedRes_leaf
#print axioms Uniformity.Density.Tower.I10rl4.s2_eval_one_nextRead3_leaf
#print axioms Uniformity.Density.Tower.I10rl4.s2_nextSupp3_eq_dv4Supp
#print axioms Uniformity.Density.Tower.I10rl4.s2_nextSupp3_leaf
#print axioms Uniformity.Density.Tower.I10rl4.s2RungLift4
#print axioms Uniformity.Density.Tower.I10rl4.s2LiftAt4
#print axioms Uniformity.Density.Tower.I10rl4.s2Rung4PackAt
#print axioms Uniformity.Density.Tower.I10rl4.s2Rung4_kgrade_is_leaf_mu5_grade
#print axioms Uniformity.Density.Tower.I10rl4.s2Rung4_slope_floor
#print axioms Uniformity.Density.Tower.I10rl4.s2_towerPacks_rung4
#print axioms Uniformity.Density.Tower.I10rl4.s2_rungLift4_nonempty
#print axioms Uniformity.Density.Tower.I10rl4.s2_rung4_pack_nonempty
#print axioms Uniformity.Density.Tower.I10rl4.s2Rung5Carrier
#print axioms Uniformity.Density.Tower.I10rl4.s2_rung4_wcoeff_mul

end AxCheck
