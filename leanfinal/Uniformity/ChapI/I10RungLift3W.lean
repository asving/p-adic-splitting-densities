/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I10RungLift3
import Uniformity.ChapC.C136d2
import Uniformity.ChapC.C136e0
import Uniformity.ChapC.C130rp2

/-!
# Uniformity.ChapI.I10RungLift3W — UNIT W3P: the S2 rung-3 dictionary (W-a/W-b/W-c) and the fire

RL3 (`I10RungLift3`) landed the generic `RungLift` core and named (§6) EXACTLY three
unlanded S2 dictionary lemmas between the abstract pack vocabulary and the landed C136
depth-3/4 content.  This file lands them and fires the constructors:

* §1 **W-a** — `s2_exact_ne`: the S2 pack's eval-1 exact-grade nonvanishing below the
  `g8` fence (`deg g < 8`, exact `dv2Supp` grade ⇒ `eval 1 (s2Mu3GradedRes m g) ≠ 0`).
  Pure plumbing: C136d2's landed eval-1 collapse under the degree-8 fence
  (`eval_one_s2Mu3GradedRes_eq_coeff_zero`) + C132rp8's fence-free nonvanishing
  (`s2Mu3GradedRes_ne_zero_of_exact`).  `s2Rung2Pack` — WCC's `s2Carrier`/`s2Key`
  completed to a `RungPack` — follows.
* §2 **W-b** — `s2_nextSupp_g16`: the grade dictionary `nextSupp s2Carrier s2Key g16
  = 170`.  Generic half: the ℕ-indexed `nextSupp` infimum truncates to the development
  range (`nextSupp_eq_inf_range`); S2 half: term-for-term identification with `dv3Supp`
  (`s2_nextSupp_eq_dv3Supp`, for EVERY `f`), then the landed `g16_exactGrade` through
  `S2Mu4ExactGrade_iff_dv3Supp`.
* §3 **W-c** — `s2_eval_one_nextRead_g16`: the root dictionary.  Payload
  `s2_nextRead_g16 : nextRead s2Carrier s2Key 170 g16 = X² + 1` — the landed μ₄
  residual `s2Mu4GradedRes_g16 = X + 1` re-indexed by the ramification stretch `ℓ = 2`
  (the raw-abscissa slots are `{0, 2}`); eval-1 is reindex-invariant and the landed
  char-2 tooth (`C130rp2.tooth_char_two`) kills it.
* §4 ★★ **the fire**: `s2RungLift3 := RungLift.ofRootF1 …` — the S2 rung-3 `RungLift`
  at the tower's own μ₅ slopes `(u₅, ℓ₅) = (171, 1)` (anti-drift tie to the landed μ₅
  tooth `s2Hgt₅_g16 : s2Hgt₅ g16 = 171`); `s2LiftAt3 := liftAtOfRootF1 …`;
  `s2Rung3PackAt := s2LiftAt3.next` — the rung-3 pack EXISTS at the keystone: ring
  `fld 2` again (f′ = 1: no ring growth), key `g16`, grade `170`, slopes `(171, 1)`;
  `towerPacks` reaches it at index 1, and the weighted convolution law fires at rung 3
  (`s2_rung3_wcoeff_mul` — the level-4→5 convolution at the keystone).

The honest remainder AFTER this file (the deepTwist bank's tower side): rung 4+ out of
`s2Rung3PackAt` needs the rung-4 dictionary one level up — the μ₅ COEFFICIENT layer
(SlotOnGrade/Coeff/GradedRes at `(171,1)`, C136e0's declared D4-13..16 gap) and the next
key with its μ₅ grade; the generic core needs nothing new (`ofRootF1` at `gcd 171 1 = 1`
if the μ₅ residual is again linear with a nonzero root, else `ofPrime`).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.I10rl3w

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C132nv0 Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C132rp0 Uniformity.Density.Tower.C132rp1
open Uniformity.Density.Tower.C132rp2 Uniformity.Density.Tower.C132rp8
open Uniformity.Density.Tower.C132rp10b Uniformity.Density.Tower.C80
open Uniformity.Density.Tower.C136d0 Uniformity.Density.Tower.C136d1
open Uniformity.Density.Tower.C136d2 Uniformity.Density.Tower.C136e0
open Uniformity.Density.Tower.I10wcc
open Uniformity.Density.Tower.I10rung
open Uniformity.Density.Tower.I10rl3

/-! ## §0 — the generic iInf-vs-range-inf identification (W-b's generic half) -/

section GenericInf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {K : Type*} [CommRing K]

/-- local guard twins of WCC/RUNG's private unfoldings (6th corpus repetition — flagged
for the standing dedup pass). -/
private theorem wcoeff_of_guard (C : WeightedCarrier O K) {u ℓ : ℕ} (P : CarrierKey C u ℓ)
    {β J : ℕ} {f : Polynomial O} (h1 : u * J ≤ β) (h2 : ℓ ∣ (β - u * J)) :
    wcoeff C P β f J = C.read ((β - u * J) / ℓ) (dev P.key f J) := if_pos ⟨h1, h2⟩

private theorem wcoeff_of_not_guard (C : WeightedCarrier O K) {u ℓ : ℕ}
    (P : CarrierKey C u ℓ) {β J : ℕ} {f : Polynomial O}
    (h : ¬ (u * J ≤ β ∧ ℓ ∣ (β - u * J))) : wcoeff C P β f J = 0 := if_neg h

/-- **the iInf-vs-range-inf identification**: the ℕ-indexed infimum in `nextSupp`
truncates to the development range — past-degree slots price `⊤`. -/
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

end GenericInf

/-! ## §1 — W-a: the S2 eval-1 exact-grade nonvanishing, and the rung-2 pack -/

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- local twin of C136d2's private `s2Mu3GradedRes_coeff_eq_zero_of_pos` (verbatim): past
abscissa `0`, every μ₃ graded coefficient of a `< 8`-degree input vanishes. -/
private theorem s2Mu3GradedRes_coeff_eq_zero_of_pos {m t : ℕ} {A : Polynomial O}
    (hA : A.natDegree < 8) (ht : 0 < t) :
    (s2Mu3GradedRes h2 hq m A).coeff t = 0 := by
  rw [s2Mu3GradedRes_coeff]
  refine s2Mu3Coeff_eq_zero_of_dv2Pin_top h2 hq ?_
  rw [dv2Pin, dev_eq_zero_of_lt (s2Φ₂_monic h2 hq)
    (by rw [s2Φ₂_natDegree h2 hq]; norm_num) A _
    (by rw [s2Φ₂_natDegree h2 hq]; omega), dv2Hgt]
  exact dvSupp_zero_eq_top _ _ ((s2Tower h2 hq).levelDatum h2).hℓ

/-- local twin of C136d2's private `s2Mu3GradedRes_eq_C_coeff_zero` (verbatim): under the
`< 8` fence the μ₃ graded residual is its own degree-zero term. -/
private theorem s2Mu3GradedRes_eq_C_coeff_zero {m : ℕ} {A : Polynomial O}
    (hA : A.natDegree < 8) :
    s2Mu3GradedRes h2 hq m A = Polynomial.C ((s2Mu3GradedRes h2 hq m A).coeff 0) := by
  refine Polynomial.ext fun t => ?_
  match t with
  | 0 => simp
  | (t + 1) =>
    rw [Polynomial.coeff_C, if_neg (Nat.succ_ne_zero t)]
    exact s2Mu3GradedRes_coeff_eq_zero_of_pos h2 hq hA (Nat.succ_pos t)

/-- ★ **W-a — the S2 pack's eval-1 `exact_ne`**: below the `g8` fence, the eval-1 read of
the μ₃ graded residual at an exact `dv2Supp` grade is nonzero.  The RL3 §6 diagonal
singleton one level down, discharged from landed content: the eval-1 collapse under the
degree-8 fence (C136d2) + the fence-free exact-grade nonvanishing (C132rp8). -/
theorem s2_exact_ne {m : ℕ} {g : Polynomial O}
    (hdeg : g.natDegree < (g8 h2 hq : Polynomial O).natDegree)
    (hsupp : dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2
      = (m : ℕ∞)) :
    Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2) (s2Mu3GradedRes h2 hq m g) ≠ 0 := by
  rw [s2g8_natDegree h2 hq] at hdeg
  have hex : S2Mu3ExactGrade h2 hq m g := (S2Mu3ExactGrade_iff_dv2Supp h2 hq).mpr hsupp
  rw [eval_one_s2Mu3GradedRes_eq_coeff_zero h2 hq hdeg]
  intro hc0
  refine C132rp8.s2Mu3GradedRes_ne_zero_of_exact h2 hq hex ?_
  rw [s2Mu3GradedRes_eq_C_coeff_zero h2 hq hdeg, hc0, Polynomial.C_0]

/-- anti-drift pin: the S2 key pack's key is `g8`. -/
theorem s2Key_key : (I10wcc.s2Key h2 hq).key = g8 h2 hq := rfl

/-- ★ **the S2 rung-2 `RungPack`** — WCC's `s2Carrier`/`s2Key` completed by W-a: the
keystone pack at slopes `(85, 2)`, every field landed content. -/
noncomputable def s2Rung2Pack : RungPack O ((s2DepthTwo h2 hq).fld 2) 85 2 where
  C := s2Carrier h2 hq
  P := I10wcc.s2Key h2 hq
  exact_ne := fun hdeg hsupp => s2_exact_ne h2 hq hdeg hsupp

/-! ## §2 — W-b: the grade dictionary `nextSupp = dv3Supp`, and `g16` at `170` -/

/-- ★ **the S2 support dictionary** (for EVERY `f`): the abstract iterated support at the
S2 pack IS the landed level-3 cleared support `dv3Supp` — term-for-term after the range
truncation, since `dv3Pin = dv2Supp ∘ dev g8` by definition. -/
theorem s2_nextSupp_eq_dv3Supp (f : Polynomial O) :
    nextSupp (s2Carrier h2 hq) (I10wcc.s2Key h2 hq) f
      = dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
          f 85 2 := by
  rw [nextSupp_eq_inf_range, dv3Supp]
  refine Finset.inf_congr rfl fun j _ => ?_
  show (2 : ℕ∞) * dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2)
      (dev (g8 h2 hq) f j) 21 2 + ((85 * j : ℕ) : ℕ∞)
    = 2 • dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
        (g8 h2 hq) f j + ((85 : ℕ) : ℕ∞) * (j : ℕ∞)
  rw [dv3Pin, dv3Hgt, nsmul_eq_mul]
  push_cast
  ring

/-- ★ **W-b — the grade dictionary at the witness**: `nextSupp s2Carrier s2Key g16 = 170`,
from the landed `g16_exactGrade` through `S2Mu4ExactGrade_iff_dv3Supp`. -/
theorem s2_nextSupp_g16 :
    nextSupp (s2Carrier h2 hq) (I10wcc.s2Key h2 hq) (g16 h2 hq) = ((170 : ℕ) : ℕ∞) := by
  rw [s2_nextSupp_eq_dv3Supp h2 hq]
  exact (S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp (g16_exactGrade h2 hq)

/-! ## §3 — W-c: the root dictionary `eval 1 (nextRead 170 g16) = 0` -/

/-- local twin of WCC's private `s2Mu4Coeff_eq_wcoeff` (verbatim): the landed μ₄
coefficient IS the abstract carrier coefficient at the parity abscissa. -/
private theorem s2Mu4Coeff_eq_wcoeff {β : ℕ} {g : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) (t : ℕ) :
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
      le_dv3Pin_of_le_dv3Supp h2 hq (by norm_num)
        (le_of_eq ((S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp hg).symm) hm2
    rw [s2Mu4Coeff_eq_eval_of_le h2 hq hm2 hpin, wcoeff_of_guard (s2Carrier h2 hq) (I10wcc.s2Key h2 hq) hge hdvd]
    rfl

/-- ★ **the W-c payload — the raw-abscissa residual**: the iterated read of `g16` at its
exact grade `170` is `X² + 1` — the landed μ₄ residual `X + 1` (`s2Mu4GradedRes_g16`)
with its slots dilated by the ramification stretch `ℓ = 2` (raw slots `{0, 2}`; odd and
past-fence slots are off the `(85, 2)` guard). -/
theorem s2_nextRead_g16 :
    nextRead (s2Carrier h2 hq) (I10wcc.s2Key h2 hq) 170 (g16 h2 hq)
      = Polynomial.X ^ 2 + 1 := by
  refine Polynomial.ext fun J => ?_
  rw [nextRead_coeff]
  match J with
  | 0 =>
      have h := s2Mu4Coeff_eq_wcoeff h2 hq (g16_exactGrade h2 hq) 0
      rw [show (170 % 2 + 2 * 0 : ℕ) = 0 from by norm_num] at h
      rw [← h, ← s2Mu4GradedRes_coeff h2 hq, s2Mu4GradedRes_g16 h2 hq]
      simp [Polynomial.coeff_one]
  | 1 =>
      rw [wcoeff_of_not_guard (s2Carrier h2 hq) (I10wcc.s2Key h2 hq) (by omega)]
      simp [Polynomial.coeff_one]
  | 2 =>
      have h := s2Mu4Coeff_eq_wcoeff h2 hq (g16_exactGrade h2 hq) 1
      rw [show (170 % 2 + 2 * 1 : ℕ) = 2 from by norm_num] at h
      rw [← h, ← s2Mu4GradedRes_coeff h2 hq, s2Mu4GradedRes_g16 h2 hq]
      simp [Polynomial.coeff_one]
  | (J + 3) =>
      rw [wcoeff_of_not_guard (s2Carrier h2 hq) (I10wcc.s2Key h2 hq) (by omega), Polynomial.coeff_add,
        Polynomial.coeff_X_pow, Polynomial.coeff_one, if_neg (by omega),
        if_neg (by omega), add_zero]

/-- ★ **W-c — the root dictionary**: `eval 1 (nextRead s2Carrier s2Key 170 g16) = 0` —
eval-1 is reindex-invariant, and `1 + 1 = 0` is the landed char-2 tooth. -/
theorem s2_eval_one_nextRead_g16 :
    Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
      (nextRead (s2Carrier h2 hq) (I10wcc.s2Key h2 hq) 170 (g16 h2 hq)) = 0 := by
  rw [s2_nextRead_g16 h2 hq, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one, one_pow]
  exact C130rp2.tooth_char_two h2 hq

/-! ## §4 — ★★ the fire: the S2 rung-3 `RungLift` + `towerPacks` at the keystone -/

/-- the bundled S2 rung-2 pack (the recursion base at the keystone). -/
noncomputable def s2Rung2PackAt : PackAt O :=
  ⟨(s2DepthTwo h2 hq).fld 2, 85, 2, s2Rung2Pack h2 hq⟩

/-- ★★ **the S2 rung-3 `RungLift`** — RL3's f′ = 1 closed form fired at the keystone:
key `g16` (monic, degree 16 = the fence `2·8` exactly), exact iterated grade `170`
(W-b), root `1` of the raw-abscissa residual `X² + 1` (W-c), next ring `fld 2` ITSELF
(no ring growth), next slopes the μ₅ pair `(171, 1)` with the strict floor
`1·170 < 171`. -/
noncomputable def s2RungLift3 :
    RungLift (s2Rung2Pack h2 hq) ((s2DepthTwo h2 hq).fld 2) 171 1 :=
  RungLift.ofRootF1 (s2Rung2Pack h2 hq) (g16_monic h2 hq)
    (by rw [g16_natDegree h2 hq]; norm_num)
    (by show (g16 h2 hq : Polynomial O).natDegree ≤ 2 * (g8 h2 hq : Polynomial O).natDegree
        rw [g16_natDegree h2 hq, s2g8_natDegree h2 hq])
    (by norm_num)
    (s2_nextSupp_g16 h2 hq)
    (one_ne_zero : (1 : (s2DepthTwo h2 hq).fld 2) ≠ 0)
    (s2_eval_one_nextRead_g16 h2 hq)
    (by norm_num)
    (by norm_num)

/-- ★ **the bundled fire** through RL3's §5 wrapper. -/
noncomputable def s2LiftAt3 : LiftAt O (s2Rung2PackAt h2 hq) :=
  haveI : IsDomain ((s2Rung2PackAt h2 hq).K) :=
    inferInstanceAs (IsDomain ((s2DepthTwo h2 hq).fld 2))
  liftAtOfRootF1 (s2Rung2PackAt h2 hq) (u' := 171) (ℓ' := 1) (g16_monic h2 hq)
    (by rw [g16_natDegree h2 hq]; norm_num)
    (by show (g16 h2 hq : Polynomial O).natDegree ≤ 2 * (g8 h2 hq : Polynomial O).natDegree
        rw [g16_natDegree h2 hq, s2g8_natDegree h2 hq])
    (by show Nat.gcd 85 2 = 1; norm_num)
    (s2_nextSupp_g16 h2 hq)
    (one_ne_zero : (1 : (s2DepthTwo h2 hq).fld 2) ≠ 0)
    (s2_eval_one_nextRead_g16 h2 hq)
    (by norm_num)
    (by norm_num)

/-- ★★ **the S2 rung-3 pack at the keystone** — the deepTwist bank's tower side
inhabited to rung 3. -/
noncomputable def s2Rung3PackAt : PackAt O := (s2LiftAt3 h2 hq).next

/-- rfl-pins: the rung-3 pack's slopes are the μ₅ pair, its key is `g16` at grade
`170`, and its ring is `fld 2` again (f′ = 1: no ring growth). -/
theorem s2Rung3PackAt_u : (s2Rung3PackAt h2 hq).u = 171 := rfl

theorem s2Rung3PackAt_ell : (s2Rung3PackAt h2 hq).ℓ = 1 := rfl

theorem s2Rung3PackAt_key : (s2Rung3PackAt h2 hq).pack.P.key = g16 h2 hq := rfl

theorem s2Rung3PackAt_kgrade : (s2Rung3PackAt h2 hq).pack.P.kgrade = 170 := rfl

/-- anti-drift tie: the fired rung-3 key carries the landed μ₅ tooth value `171 = u₅` —
the chosen slopes ARE the tower's own μ₅ table (`C136e0.s2Hgt₅_g16`). -/
theorem s2Rung3_slope_is_mu5_tooth :
    s2Hgt₅ h2 hq ((s2Rung3PackAt h2 hq).pack.P.key) = ((171 : ℤ) : WithTop ℤ) :=
  s2Hgt₅_g16 h2 hq

/-- ★ **`towerPacks` fires at the keystone**: any step supplier extending the S2 lift
reaches the rung-3 pack at index 1. -/
theorem s2_towerPacks_rung3 (step : ∀ Q : PackAt O, LiftAt O Q)
    (hstep : step (s2Rung2PackAt h2 hq) = s2LiftAt3 h2 hq) :
    towerPacks (s2Rung2PackAt h2 hq) step 1 = s2Rung3PackAt h2 hq := by
  rw [towerPacks_succ, towerPacks_zero, hstep]
  rfl

/-- ★ the tower side of the deepTwist bank, inhabited: the S2 rung-3 `RungLift`
EXISTS. -/
theorem s2_rungLift3_nonempty :
    Nonempty (RungLift (s2Rung2Pack h2 hq) ((s2DepthTwo h2 hq).fld 2) 171 1) :=
  ⟨s2RungLift3 h2 hq⟩

/-- the unbundled rung-3 pack. -/
noncomputable def s2Rung3Pack : RungPack O ((s2DepthTwo h2 hq).fld 2) 171 1 :=
  (s2RungLift3 h2 hq).pack

/-- ★ the rung-3 pack EXISTS at the keystone slopes `(171, 1)`. -/
theorem s2_rung3_pack_nonempty :
    Nonempty (RungPack O ((s2DepthTwo h2 hq).fld 2) 171 1) :=
  ⟨s2Rung3Pack h2 hq⟩

/-- ★ **the "3+": the rung-4 CARRIER exists unconditionally** (RUNG §6's `nextCarrier`
at the landed rung-3 pack) — the tower side continues past rung 3 with no new data; the
honest rung-4 remainder is the KEY lift alone (the μ₅ coefficient layer, C136e0's
declared D4-13..16 gap, plus the level-5 key with its grade and the μ₆ slopes). -/
noncomputable def s2Rung4Carrier :
    WeightedCarrier O (Polynomial ((s2DepthTwo h2 hq).fld 2)) :=
  nextCarrier (s2Rung3Pack h2 hq)

/-- ★★ **the weighted convolution law at rung 3 of the keystone tower** — the
level-4→5 convolution, fired through the landed rung-3 pack. -/
theorem s2_rung3_wcoeff_mul {β β' : ℕ} {g z : Polynomial O}
    (hg : LineFloor (s2Rung3Pack h2 hq).C (s2Rung3Pack h2 hq).P β g)
    (hz : LineFloor (s2Rung3Pack h2 hq).C (s2Rung3Pack h2 hq).P β' z) (J : ℕ) :
    wcoeff (s2Rung3Pack h2 hq).C (s2Rung3Pack h2 hq).P (β + β') (g * z) J
      = ∑ j ∈ Finset.range (J + 1),
          wcoeff (s2Rung3Pack h2 hq).C (s2Rung3Pack h2 hq).P β g j
            * wcoeff (s2Rung3Pack h2 hq).C (s2Rung3Pack h2 hq).P β' z (J - j) :=
  wcoeff_mul _ _ hg hz J

end S2

end Uniformity.Density.Tower.I10rl3w

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.I10rl3w.s2_exact_ne
#print axioms Uniformity.Density.Tower.I10rl3w.s2Rung2Pack
#print axioms Uniformity.Density.Tower.I10rl3w.s2_nextSupp_eq_dv3Supp
#print axioms Uniformity.Density.Tower.I10rl3w.s2_nextSupp_g16
#print axioms Uniformity.Density.Tower.I10rl3w.s2_nextRead_g16
#print axioms Uniformity.Density.Tower.I10rl3w.s2_eval_one_nextRead_g16
#print axioms Uniformity.Density.Tower.I10rl3w.s2RungLift3
#print axioms Uniformity.Density.Tower.I10rl3w.s2LiftAt3
#print axioms Uniformity.Density.Tower.I10rl3w.s2Rung3PackAt
#print axioms Uniformity.Density.Tower.I10rl3w.s2Rung3_slope_is_mu5_tooth
#print axioms Uniformity.Density.Tower.I10rl3w.s2_towerPacks_rung3
#print axioms Uniformity.Density.Tower.I10rl3w.s2_rungLift3_nonempty
#print axioms Uniformity.Density.Tower.I10rl3w.s2_rung3_pack_nonempty
#print axioms Uniformity.Density.Tower.I10rl3w.s2_rung3_wcoeff_mul
#print axioms Uniformity.Density.Tower.I10rl3w.s2Rung4Carrier

end AxCheck
