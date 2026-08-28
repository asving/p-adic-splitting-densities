/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C136e0
import Uniformity.ChapC.C136t

/-!
# Uniformity.ChapC.C136e1 — the μ₅ refinement stack's middle tranche: D4-05..D4-12 [D4B 2026-08-28]

**Unit D4B** of the deep-witness campaign
(`docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md` §6.3, rows D4-05 through D4-12).
Chains onto `C136e0`'s landed D4-00..D4-04 (the `dv4` layer, `s2Hgt₅`, the UNCONDITIONAL
survival `s2_dv4ResSurv_at_171` and product `s2Hgt₅_mul_all`, `s2AddVal₅` + the grade
bank, and the `e' = 1` gate: unique slot residue `0`, `S2Mu5PrevGrade` ALL grades, the
level-4 ε-data Bézout pair `(1, −42)`).

Every declaration below is the one-level-up mirror of the landed μ₄ D3 stack's
`C136d1`/`C136d2` (D3-07/08 for the coefficient and graded operator, D3-10/11 for the
convolution and product laws, D3-11's Part 3 and D3-12 for the scalar nonvanishing and
normalized operator), with the inner key `g8` (level-3) replaced by `g16` (level-4), the
outer refinement side `(u₅, ℓ₅) = (171, 1)` replacing `(u₄, ℓ₄) = (85, 2)`, and the inner
graded/normalized read `s2Mu3GradedRes`/`s2Mu3NormRes` (landed μ₃-level) replaced by the
landed μ₄-level `s2Mu4GradedRes`/`s2Mu4NormRes` (`C136d1`/`C136d2`).  Because `e' = 1`
(the [G5F]-adjudicated refinement side), the abscissa formula collapses: coefficient
index `t` IS the development slot `s` (no `β % e'` residue, no `/e'` division), so the
ε-exponent/carry machinery collapses to `1`/`0` identically (row D4-05's signed exit) and
the coefficient convolution is UNTWISTED for every grade pair, not merely the
preceding-group ones (row D4-07's signed exit, since `S2Mu5PrevGrade` is landed as ALL
grades).

## What lands

* **D4-05 (recursive coefficient).** `s2Mu5EpsExp`/`s2Mu5EpsOf`/`s2Mu5Eps` (the ε-collapse
  at the level-4 Bézout pair `(1,−42)`, reusing the field-generic
  `C132rp1.s2Fld₂_eq_one_of_ne_zero`/`s2Mu3_eval_letter_pinned` directly, exactly as
  `C136d1` reused them one level down); `s2Mu5Coeff` reading the landed μ₄ GRADED
  operator `s2Mu4GradedRes` at the on-line inner grade `β − 171·t` (no division); the
  letter-display, true-height, and graded/normalized (`s2Mu4NormRes`) collapse pins; the
  finite-support and above-grade zero laws.
* **D4-06 (total graded operator/add).** `s2Mu5GradedRes`, its master coefficient law,
  range independence, finite support, and zero-above law; PLUS the exact-grade
  additivity engine — the level-4 floor bridge `le_dv4Pin_of_le_dv4Supp` (off the
  ALREADY-LANDED `C136e0.dv4Supp_le_term`), the coefficient floor bridge
  `s2Mu5Coeff_eq_eval_of_le`, `s2Mu5Coeff_add`, and the polynomial lift
  `s2Mu5GradedRes_add_of_le`/`s2Mu5GradedRes_add`.
* **D4-07 (convolution/product).** The gate-witness existence `exists_mu5SlotOnGrade_of_exact`;
  the coefficient convolution `s2Mu5Coeff_mul` (untwisted, no carry shift — the [G5F]
  `e' = 1` collapse); the UNTWISTED graded multiplication `s2Mu5GradedRes_mul` for every
  grade pair (no preceding-group hypothesis needed, since `S2Mu5PrevGrade` is landed as
  ALL grades).
* **D4-08 (scalar nonzero below degree 16).** `s2Mu5GradedRes_coeff_zero_ne_zero_of_exact`:
  for `g` of degree below `deg(g16) = 16`, the graded residual's constant term is
  nonzero — via the forced slot-`0` read (the ONLY live slot below degree 16) and the
  ALREADY-LANDED μ₄-level collapse-to-constant `C136d3.s2Mu4GradedRes_eq_C_of_natDegree_lt_sixteen`
  plus the ALREADY-LANDED nonvanishing `C136d2.s2Mu4GradedRes_ne_zero_of_exact` (a
  contradiction argument, no fresh eval-collapse lemma needed — the campaign's fence
  `16 = 2 · deg(g8)` is EXACTLY the fence the landed μ₄-level collapse already carries).
* **D4-09 (normalized operator).** `s2Mu5GradeOf`/`s2Mu5NormRes` (strip the initial `X`
  power); the polynomial-level nonvanishing `s2Mu5GradedRes_ne_zero_of_exact`; the
  universal multiplication `s2Mu5NormRes_mul`; the key reads `s2Mu5NormRes_key`/`_key_pow`
  at `g16` itself.

## What this unit does NOT claim (honesty scope)

No normalizer exact grade (D4-10), no recipe/leaf (D4-11/12), no μ₅ key predicates on top
of the μ₅ valuation (D4-13..16), no `FGMNSourceData`/calculus record (D4-17/18).  The
OPEN-RP1-TRANSPORT faithfulness split is inherited exactly as the D3 stack left it —
cited, never re-derived or re-opened.

**DEPENDS.** `C136e0` (D4-00..04: `dv4Hgt`/`dv4Pin`/`dv4Supp` + bank, `s2Hgt₅`,
`S2Mu5ExactGrade`/`AboveGrade`, `S2Mu5SlotOnGrade` + its iff/inner-exact/bound laws,
`S2Mu5PrevGrade_all`, `s2Mu5_bezout_level4`) · `C136d1` (D3-07: the μ₄ recursive
coefficient pattern) · `C136d2` (D3-11/12: `s2Mu4GradedRes_mul_of_exact`, `s2Mu4NormRes`
+ its mul/key laws, `g16`, `g16_monic`, `g16_natDegree`) · `C136d3` (D3-15:
`s2Mu4GradedRes_eq_C_of_natDegree_lt_sixteen`) · `C132rp1`
(`s2Fld₂_eq_one_of_ne_zero`, `s2Mu3_eval_letter_pinned`) · `C130nv2` (`weight_read`) ·
`C118a` (`smul_top_pos`).

## Status

Sorry-free target for D4-05..09; verdict `runs/wave-c/verdict_D4B.md`.
-/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace Uniformity.Density.Tower.C136e1

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130rp0
open Uniformity.Density.Tower.C130nv2 (weight_read dev_zero_pin)
open Uniformity.Density.Tower.C132rp5 (dev_mul_conv_split_monic)
open Uniformity.Density.Tower.C130np0
open Uniformity.Density.Tower.C132nv0 Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C132nv2 (dv2Hgt_zero)
open Uniformity.Density.Tower.C132rp0 Uniformity.Density.Tower.C132rp1
open Uniformity.Density.Tower.C132rp2 Uniformity.Density.Tower.C132rp3
open Uniformity.Density.Tower.C132rp8 Uniformity.Density.Tower.C132rp10b
open Uniformity.Density.Tower.C136d0 Uniformity.Density.Tower.C136d1
open Uniformity.Density.Tower.C136d2 Uniformity.Density.Tower.C136d3
open Uniformity.Density.Tower.C136d3ad Uniformity.Density.Tower.C136t
open Uniformity.Density.Tower.C136e0
open Uniformity.Density.Tower.C80

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## D4-05 — the μ₅ ε-collapse and recursive coefficient `s2Mu5Coeff`, at `e' = 1`

Mirror of `C136d1`'s D3-06 Part 2 (the ε-factor) and D3-07 (`s2Mu4Coeff`), one level up,
with the abscissa formula collapsed since `e' = 1`: coefficient index `t` IS the
development slot, no `β % e'` residue and no `/e'` division anywhere. -/

/-! ### Part 0 — the ε-factor at the level-4 Bézout pair `(1,−42)` -/

/-- Def 3.12's ε-exponent at the S2 level-4 numerals: `ℓ₄′·s₄(m) − ℓ₄·u₄(m)` with
`(ℓ₄,ℓ₄′) = (1,−42)` (`C136e0.s2Mu5_bezout_level4`). -/
def s2Mu5EpsExp (m : ℕ) : ℤ :=
  (-42) * ((m % 2 : ℕ) : ℤ) - ((m : ℤ) - 85 * ((m % 2 : ℕ) : ℤ)) / 2

/-- the ε-factor, parametric in the letter: `ε₄(m) = z ^ s2Mu5EpsExp m`. -/
noncomputable def s2Mu5EpsOf (z : (s2DepthTwo h2 hq).fld 2) (m : ℕ) :
    (s2DepthTwo h2 hq).fld 2 :=
  z ^ s2Mu5EpsExp m

/-- ★ the ε-collapse: for every nonzero letter `z`, the ε-factor is `1` — reusing
`C132rp1.s2Fld₂_eq_one_of_ne_zero`, since the collapse is a field fact, not a level
fact. -/
theorem s2Mu5EpsOf_eq_one {z : (s2DepthTwo h2 hq).fld 2} (hz : z ≠ 0) (m : ℕ) :
    s2Mu5EpsOf h2 hq z m = 1 := by
  unfold s2Mu5EpsOf
  rw [C132rp1.s2Fld₂_eq_one_of_ne_zero h2 hq hz, one_zpow]

/-- the collapsed ε-operator used by the coefficient definition. -/
noncomputable def s2Mu5Eps (_ : ℕ) : (s2DepthTwo h2 hq).fld 2 := 1

theorem s2Mu5Eps_eq_one (m : ℕ) : s2Mu5Eps h2 hq m = 1 := rfl

theorem s2Mu5Eps_eq_epsOf {z : (s2DepthTwo h2 hq).fld 2} (hz : z ≠ 0) (m : ℕ) :
    s2Mu5Eps h2 hq m = s2Mu5EpsOf h2 hq z m :=
  (s2Mu5EpsOf_eq_one h2 hq hz m).symm

theorem s2Mu5Eps_ne_zero (m : ℕ) : s2Mu5Eps h2 hq m ≠ 0 := one_ne_zero

/-! ### Part 1 — the μ₅ recursive coefficient -/

open Classical in
/-- ★ **the μ₅ recursive coefficient**: the landed μ₄ graded read of the `g16`-development
slot at abscissa `t` (no residue/spacing since `e' = 1`), at the on-line inner grade
`β − 171·t`, evaluated at the collapsed letter and multiplied by the collapsed
ε-factor, if the slot is on the line; `0` otherwise. -/
noncomputable def s2Mu5Coeff (β : ℕ) (g : Polynomial O) (t : ℕ) :
    (s2DepthTwo h2 hq).fld 2 :=
  if S2Mu5SlotOnGrade h2 hq β g t then
    s2Mu5Eps h2 hq (β - 171 * t)
      * Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
          (s2Mu4GradedRes h2 hq (β - 171 * t) (dev (g16 h2 hq) g t))
  else 0

open Classical in
/-- ★ **the letter-display pin**: for EVERY nonzero candidate letter `z`, the coefficient
equals the literal published display with `z` in place of the collapsed values. -/
theorem s2Mu5Coeff_letter_display {z : (s2DepthTwo h2 hq).fld 2} (hz : z ≠ 0)
    (β : ℕ) (g : Polynomial O) (t : ℕ) :
    s2Mu5Coeff h2 hq β g t =
      if S2Mu5SlotOnGrade h2 hq β g t then
        s2Mu5EpsOf h2 hq z (β - 171 * t)
          * Polynomial.eval z
              (s2Mu4GradedRes h2 hq (β - 171 * t) (dev (g16 h2 hq) g t))
      else 0 := by
  unfold s2Mu5Coeff
  rw [s2Mu5EpsOf_eq_one h2 hq hz, s2Mu5Eps_eq_one, C132rp1.s2Mu3_eval_letter_pinned h2 hq hz]

/-- **the true-height pin**: on the gate, the ℕ-cleared inner grade `β − 171t` IS the
slot's actual μ₄ value. -/
theorem s2Mu5Coeff_eq_eval {β t m : ℕ} {g : Polynomial O}
    (hgate : S2Mu5SlotOnGrade h2 hq β g t)
    (hm : dv4Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
      85 2 (g16 h2 hq) g t = (m : ℕ∞)) :
    s2Mu5Coeff h2 hq β g t =
      Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
        (s2Mu4GradedRes h2 hq m (dev (g16 h2 hq) g t)) := by
  obtain ⟨m', hm', hβ⟩ := (s2Mu5SlotOnGrade_iff h2 hq).mp hgate
  have hmm : m = m' := by rw [hm] at hm'; exact_mod_cast hm'
  subst hmm
  have hk : β - 171 * t = m := by omega
  unfold s2Mu5Coeff
  rw [if_pos hgate, hk, s2Mu5Eps_eq_one, one_mul]

/-- ★ **the graded/normalized two-read collapse**: on the gate, reading the inner slot
through the landed μ₄ NORMALIZED operator `s2Mu4NormRes` gives the SAME coefficient. -/
theorem s2Mu5Coeff_eq_eval_normRes {β t m : ℕ} {g : Polynomial O}
    (hgate : S2Mu5SlotOnGrade h2 hq β g t)
    (hm : dv4Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
      85 2 (g16 h2 hq) g t = (m : ℕ∞)) :
    s2Mu5Coeff h2 hq β g t =
      Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
        (s2Mu4NormRes h2 hq (dev (g16 h2 hq) g t)) := by
  rw [s2Mu5Coeff_eq_eval h2 hq hgate hm]
  have hex : S2Mu4ExactGrade h2 hq m (dev (g16 h2 hq) g t) := by
    have h := s2Mu5SlotOnGrade_inner_exact h2 hq hgate
    obtain ⟨m', hm', hβ⟩ := (s2Mu5SlotOnGrade_iff h2 hq).mp hgate
    have hmm : m = m' := by rw [hm] at hm'; exact_mod_cast hm'
    have hk : β - 171 * t = m := by omega
    rwa [hk] at h
  rw [← s2Mu4NormRes_mul_X_pow_of_exact h2 hq hex, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, one_pow, mul_one]

/-- **slot completeness**: every on-line slot `s` IS read at index `s` (no rescaling,
`e' = 1`). -/
theorem s2Mu5Coeff_slot {β s : ℕ} {g : Polynomial O} (h : S2Mu5SlotOnGrade h2 hq β g s) :
    s2Mu5Coeff h2 hq β g s =
      s2Mu5Eps h2 hq (β - 171 * s)
        * Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
            (s2Mu4GradedRes h2 hq (β - 171 * s) (dev (g16 h2 hq) g s)) := by
  unfold s2Mu5Coeff
  rw [if_pos h]

/-- vanishing off finite inner values. -/
theorem s2Mu5Coeff_eq_zero_of_dv4Pin_top {β t : ℕ} {g : Polynomial O}
    (h : dv4Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
      85 2 (g16 h2 hq) g t = ⊤) :
    s2Mu5Coeff h2 hq β g t = 0 := by
  unfold s2Mu5Coeff
  rw [if_neg]
  intro hgate
  obtain ⟨m, hm, -⟩ := (s2Mu5SlotOnGrade_iff h2 hq).mp hgate
  rw [h] at hm
  exact WithTop.top_ne_coe hm

/-- **finite support, the natDegree bound**. -/
theorem s2Mu5Coeff_eq_zero_of_natDegree_lt {β t : ℕ} {g : Polynomial O}
    (h : g.natDegree < t) :
    s2Mu5Coeff h2 hq β g t = 0 :=
  s2Mu5Coeff_eq_zero_of_dv4Pin_top h2 hq
    (dv4Pin_top_of_gt ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21
      (by norm_num) (g8 h2 hq) 85 (by norm_num) (g16_monic h2 hq)
      (by rw [g16_natDegree h2 hq]; norm_num) g h)

/-- **finite support, the grade bound**. -/
theorem s2Mu5Coeff_eq_zero_of_grade_lt {β t : ℕ} {g : Polynomial O}
    (h : β < 171 * t) :
    s2Mu5Coeff h2 hq β g t = 0 := by
  unfold s2Mu5Coeff
  rw [if_neg]
  intro hgate
  obtain ⟨m, -, hβ⟩ := (s2Mu5SlotOnGrade_iff h2 hq).mp hgate
  omega

/-- **the coefficient-level zero law at above-grade inputs**. -/
theorem s2Mu5Coeff_eq_zero_of_above {β : ℕ} {g : Polynomial O}
    (h : S2Mu5AboveGrade h2 hq β g) (t : ℕ) :
    s2Mu5Coeff h2 hq β g t = 0 := by
  have hdv := (S2Mu5AboveGrade_iff_dv4Supp h2 hq).mp h
  unfold s2Mu5Coeff
  rw [if_neg]
  intro hgate
  exact absurd (dv4Supp_le_of_mu5SlotOnGrade h2 hq hgate) (not_le.mpr hdv)

/-! ## D4-06 — the total graded operator `s2Mu5GradedRes`, and the ADD law -/

/-! ### The assembly -/

/-- ★ **the total μ₅ graded residual** `R_β(g) ∈ 𝔽₃[y]`. -/
noncomputable def s2Mu5GradedRes (β : ℕ) (g : Polynomial O) :
    Polynomial ((s2DepthTwo h2 hq).fld 2) :=
  ∑ t ∈ Finset.range (β + 1), Polynomial.C (s2Mu5Coeff h2 hq β g t) * Polynomial.X ^ t

/-- ★ **the master coefficient law**. -/
theorem s2Mu5GradedRes_coeff (β : ℕ) (g : Polynomial O) (t : ℕ) :
    (s2Mu5GradedRes h2 hq β g).coeff t = s2Mu5Coeff h2 hq β g t := by
  unfold s2Mu5GradedRes
  rw [Uniformity.Hensel.coeff_sum_range_C_mul_X_pow]
  split_ifs with ht
  · rfl
  · exact (s2Mu5Coeff_eq_zero_of_grade_lt h2 hq (by omega)).symm

/-- **range independence**. -/
theorem s2Mu5GradedRes_eq_sum_range (β : ℕ) (g : Polynomial O) {M : ℕ} (hM : β + 1 ≤ M) :
    s2Mu5GradedRes h2 hq β g
      = ∑ t ∈ Finset.range M, Polynomial.C (s2Mu5Coeff h2 hq β g t) * Polynomial.X ^ t := by
  unfold s2Mu5GradedRes
  refine Finset.sum_subset (fun x hx => ?_) fun t _ hts => ?_
  · rw [Finset.mem_range] at hx ⊢; omega
  · rw [s2Mu5Coeff_eq_zero_of_grade_lt h2 hq
      (by rw [Finset.mem_range, not_lt] at hts; omega), Polynomial.C_0, zero_mul]

/-- **finite support, packaged**. -/
theorem s2Mu5GradedRes_natDegree_le (β : ℕ) (g : Polynomial O) :
    (s2Mu5GradedRes h2 hq β g).natDegree ≤ β := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
  rw [s2Mu5GradedRes_coeff]
  exact s2Mu5Coeff_eq_zero_of_grade_lt h2 hq (by omega)

/-- **finite support, the `natDegree` form on the polynomial**. -/
theorem s2Mu5GradedRes_coeff_eq_zero_of_natDegree_lt {β t : ℕ} (g : Polynomial O)
    (h : g.natDegree < t) :
    (s2Mu5GradedRes h2 hq β g).coeff t = 0 := by
  rw [s2Mu5GradedRes_coeff]
  exact s2Mu5Coeff_eq_zero_of_natDegree_lt h2 hq h

/-- **the zero law at above-grade inputs**. -/
theorem s2Mu5GradedRes_zero_of_above {β : ℕ} {g : Polynomial O}
    (h : S2Mu5AboveGrade h2 hq β g) : s2Mu5GradedRes h2 hq β g = 0 := by
  refine Polynomial.ext fun t => ?_
  rw [s2Mu5GradedRes_coeff, Polynomial.coeff_zero]
  exact s2Mu5Coeff_eq_zero_of_above h2 hq h t

/-- the zero polynomial has zero graded residual at every grade. -/
theorem s2Mu5GradedRes_zero (β : ℕ) : s2Mu5GradedRes h2 hq β (0 : Polynomial O) = 0 :=
  s2Mu5GradedRes_zero_of_above h2 hq (S2Mu5AboveGrade_zero h2 hq β)

/-! ### The additivity engine (citing the ALREADY-LANDED `C136e0.dv4Supp_le_term` directly,
mirroring `C136d1` D3-08's engine, which cited `C136d0.dv3Supp_le_term` directly). -/

/-- ★ **the level-4 slot floor from a cleared-support floor**, at `ℓ₅ = 1` (mirror of
`C136d1.le_dv3Pin_of_le_dv3Supp`, one level up; NO division, since `ℓ₅ = 1`). -/
theorem le_dv4Pin_of_le_dv4Supp {β m s : ℕ} {f : Polynomial O}
    (hβ : (β : ℕ∞) ≤ dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) 85 2 (g16 h2 hq) f 171 1)
    (hm : 1 * m + 171 * s = β) :
    (m : ℕ∞) ≤ dv4Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) 85 2 (g16 h2 hq) f s := by
  have h := le_trans hβ (dv4Supp_le_term (Ψ₂ := s2DepthTwoKeyAt h2 hq 2) (Ψ₃ := g8 h2 hq)
    ((s2Tower h2 hq).levelDatum h2) (g16_monic h2 hq) (by rw [g16_natDegree h2 hq]; norm_num)
    21 (by norm_num) 85 (by norm_num) f 171 (by norm_num) s)
  rcases eq_or_ne (dv4Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) 85 2 (g16 h2 hq) f s) ⊤ with hT | hT
  · rw [hT]; exact le_top
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← hc, one_nsmul] at h
  rw [← hc]
  have hnat : β ≤ c + 171 * s := by exact_mod_cast h
  exact_mod_cast (by omega : m ≤ c)

/-- ★ **the μ₅ coefficient floor bridge** (mirror of `C136d1.s2Mu4Coeff_eq_eval_of_le`). -/
theorem s2Mu5Coeff_eq_eval_of_le {β t m : ℕ} {g : Polynomial O}
    (hm : 1 * m + 171 * t = β)
    (hge : (m : ℕ∞)
        ≤ dv4Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
            85 2 (g16 h2 hq) g t) :
    s2Mu5Coeff h2 hq β g t =
      Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
        (s2Mu4GradedRes h2 hq m (dev (g16 h2 hq) g t)) := by
  rcases eq_or_lt_of_le hge with heq | hlt
  · exact s2Mu5Coeff_eq_eval h2 hq
      ((s2Mu5SlotOnGrade_iff h2 hq).mpr ⟨m, heq.symm, hm⟩) heq.symm
  · have hgate : ¬ S2Mu5SlotOnGrade h2 hq β g t := by
      intro hgate
      obtain ⟨m', hm', hβ⟩ := (s2Mu5SlotOnGrade_iff h2 hq).mp hgate
      rw [hm'] at hlt
      have : m < m' := by exact_mod_cast hlt
      omega
    have habove : S2Mu4AboveGrade h2 hq m (dev (g16 h2 hq) g t) := by
      rw [dv4Pin, dv4Hgt] at hlt
      exact (S2Mu4AboveGrade_iff_dv3Supp h2 hq).mpr hlt
    unfold s2Mu5Coeff
    rw [if_neg hgate, s2Mu4GradedRes_zero_of_above h2 hq habove, Polynomial.eval_zero]

/-! ### ★ the coefficientwise and polynomial ADD laws -/

theorem s2Mu5Coeff_add {β t : ℕ} {g h : Polynomial O}
    (hg : (β : ℕ∞)
        ≤ dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
            85 2 (g16 h2 hq) g 171 1)
    (hh : (β : ℕ∞)
        ≤ dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
            85 2 (g16 h2 hq) h 171 1) :
    s2Mu5Coeff h2 hq β (g + h) t
      = s2Mu5Coeff h2 hq β g t + s2Mu5Coeff h2 hq β h t := by
  rcases Nat.lt_or_ge β (171 * t) with hlt | hge171
  · rw [s2Mu5Coeff_eq_zero_of_grade_lt h2 hq hlt,
      s2Mu5Coeff_eq_zero_of_grade_lt h2 hq hlt,
      s2Mu5Coeff_eq_zero_of_grade_lt h2 hq hlt, add_zero]
  · have hm : 1 * (β - 171 * t) + 171 * t = β := by omega
    have hgeg := le_dv4Pin_of_le_dv4Supp h2 hq hg hm
    have hgeh := le_dv4Pin_of_le_dv4Supp h2 hq hh hm
    have hmin : min
        (dv4Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
          85 2 (g16 h2 hq) g t)
        (dv4Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
          85 2 (g16 h2 hq) h t)
        ≤ dv4Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
            85 2 (g16 h2 hq) (g + h) t := by
      rw [dv4Pin, dv4Pin, dv4Pin,
        dev_add_of_monic (g16_monic h2 hq) g h t,
        dv4Hgt, dv4Hgt, dv4Hgt]
      exact min_dv3Supp_le_dv3Supp_add ((s2Tower h2 hq).levelDatum h2) (s2Φ₂_monic h2 hq)
        (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num) (s2g8_monic h2 hq)
        (by rw [s2g8_natDegree h2 hq]; norm_num) (by norm_num) (dev (g16 h2 hq) g t)
        (dev (g16 h2 hq) h t)
    have hgegh := le_trans (le_min hgeg hgeh) hmin
    rw [s2Mu5Coeff_eq_eval_of_le h2 hq hm hgeg, s2Mu5Coeff_eq_eval_of_le h2 hq hm hgeh,
      s2Mu5Coeff_eq_eval_of_le h2 hq hm hgegh, dev_add_of_monic (g16_monic h2 hq) g h t,
      ← Polynomial.eval_add]
    congr 1
    have hA : ((β - 171 * t : ℕ) : ℕ∞) ≤ dv3Supp ((s2Tower h2 hq).levelDatum h2)
        (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) (dev (g16 h2 hq) g t) 85 2 := by
      rw [dv4Pin, dv4Hgt] at hgeg; exact hgeg
    have hB : ((β - 171 * t : ℕ) : ℕ∞) ≤ dv3Supp ((s2Tower h2 hq).levelDatum h2)
        (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) (dev (g16 h2 hq) h t) 85 2 := by
      rw [dv4Pin, dv4Hgt] at hgeh; exact hgeh
    exact s2Mu4GradedRes_add_of_le h2 hq hA hB

/-- ★ **the polynomial ADD law, floor form**: if both `g` and `h` clear the same grade
`β`, the graded residuals add (mirror of `C132rp3.s2Mu3GradedRes_add_of_le`). -/
theorem s2Mu5GradedRes_add_of_le {β : ℕ} {g h : Polynomial O}
    (hg : (β : ℕ∞)
        ≤ dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
            85 2 (g16 h2 hq) g 171 1)
    (hh : (β : ℕ∞)
        ≤ dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
            85 2 (g16 h2 hq) h 171 1) :
    s2Mu5GradedRes h2 hq β (g + h) = s2Mu5GradedRes h2 hq β g + s2Mu5GradedRes h2 hq β h := by
  refine Polynomial.ext fun t => ?_
  rw [Polynomial.coeff_add, s2Mu5GradedRes_coeff, s2Mu5GradedRes_coeff, s2Mu5GradedRes_coeff]
  exact s2Mu5Coeff_add h2 hq hg hh

/-- **the polynomial ADD law, exact-grade form** (mirror of `C136d1.s2Mu4GradedRes_add`,
directly consumed by D4-11/12's residual computation). -/
theorem s2Mu5GradedRes_add {β : ℕ} {g h : Polynomial O}
    (hg : S2Mu5ExactGrade h2 hq β g) (hh' : S2Mu5ExactGrade h2 hq β h)
    (_hgh : S2Mu5ExactGrade h2 hq β (g + h)) :
    s2Mu5GradedRes h2 hq β (g + h) = s2Mu5GradedRes h2 hq β g + s2Mu5GradedRes h2 hq β h :=
  s2Mu5GradedRes_add_of_le h2 hq
    (le_of_eq ((S2Mu5ExactGrade_iff_dv4Supp h2 hq).mp hg).symm)
    (le_of_eq ((S2Mu5ExactGrade_iff_dv4Supp h2 hq).mp hh').symm)

/-! ## D4-07 — convolution/product: gate witness, coefficient convolution (untwisted,
no carry shift), and the graded multiplication for EVERY grade pair

Mirror of `C136d2`'s D3-11 Part 1 (gate witness) and `C136l2e4`'s D3-10 (the coefficient
convolution), one level up, with the `e' = 1` collapse: coefficient index `t` IS the
development slot (no residue, no `/e'`), so NO parity case-split and NO reindexing via
`Finset.sum_filter`/`Finset.sum_image` is needed — the row's signed exit ("the carry is
IDENTICALLY ZERO"). -/

/-! ### Part 1 — the μ₅ gate witness (inf attainment) -/

theorem exists_mu5SlotOnGrade_of_exact {β : ℕ} {g : Polynomial O}
    (hg : S2Mu5ExactGrade h2 hq β g) :
    ∃ s : ℕ, S2Mu5SlotOnGrade h2 hq β g s := by
  have hsupp : dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) 85 2 (g16 h2 hq) g 171 1 = (β : ℕ∞) := (S2Mu5ExactGrade_iff_dv4Supp h2 hq).mp hg
  rw [dv4Supp] at hsupp
  obtain ⟨j, -, hjeq⟩ :=
    Finset.exists_mem_eq_inf (Finset.range (g.natDegree + 1))
      Finset.nonempty_range_add_one
      (fun j => 1 • dv4Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
        (g8 h2 hq) 85 2 (g16 h2 hq) g j + ((171 : ℕ) : ℕ∞) * (j : ℕ∞))
  rw [hjeq] at hsupp
  refine ⟨j, ?_⟩
  unfold S2Mu5SlotOnGrade
  rw [← hsupp]
  congr 1

/-! ### Part 2 — the level-4 machinery: `g16`-key reduction, finite-sum additivity,
and the eval-1 product laws (mirror of `C136l2e4`, one level up: `g8 ↦ g16`,
`s2Mu3GradedRes ↦ s2Mu4GradedRes`, `dv2Supp ↦ dv3Supp`). -/

private theorem coe_le_add_of_le_e1 {a b : ℕ} {x y : ℕ∞}
    (hx : (a : ℕ∞) ≤ x) (hy : (b : ℕ∞) ≤ y) : ((a + b : ℕ) : ℕ∞) ≤ x + y := by
  push_cast; exact add_le_add hx hy

private theorem coe_lt_add_of_lt_of_le_e1 {a b : ℕ} {x y : ℕ∞}
    (hx : (a : ℕ∞) < x) (hy : (b : ℕ∞) ≤ y) : ((a + b : ℕ) : ℕ∞) < x + y := by
  rcases eq_or_ne x ⊤ with rfl | hxne
  · rw [top_add]; exact_mod_cast WithTop.coe_lt_top _
  rcases eq_or_ne y ⊤ with rfl | hyne
  · rw [add_top]; exact_mod_cast WithTop.coe_lt_top _
  obtain ⟨cx, hcx⟩ := ENat.ne_top_iff_exists.1 hxne
  obtain ⟨cy, hcy⟩ := ENat.ne_top_iff_exists.1 hyne
  subst hcx; subst hcy
  have hax : a < cx := by exact_mod_cast hx
  have hby : b ≤ cy := by exact_mod_cast hy
  exact_mod_cast (show a + b < cx + cy from by omega)

/-- the multiplicativity of `dv3Supp` at the S2 numerals, private local copy (mirror of
`C136e0.s2_dv3Supp_mul`, per the corpus's private-copy convention). -/
private theorem s2_dv3Supp_mul_local (g z : Polynomial O) :
    dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
        (g * z) 85 2
      = dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
          g 85 2
        + dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
          z 85 2 := by
  apply C130s6.toZ_inj
  rw [C130nv.toZ_add, ← s2Hgt₄_eq_dv3Supp h2 hq, ← s2Hgt₄_eq_dv3Supp h2 hq,
    ← s2Hgt₄_eq_dv3Supp h2 hq]
  exact s2Hgt₄_mul_all h2 hq g z

/-- **the exact level-4 slot floor**, at `ℓ₅ = 1` (NO ceiling/rounding, unlike the
`e' = 2` mirrors): reads off `le_dv4Pin_of_le_dv4Supp` through `dv4Pin`/`dv4Hgt`'s
definitional unfolding. -/
private theorem exact_le_dv3Supp_dev_g16 {β : ℕ} {f : Polynomial O} (j : ℕ)
    (hβ : (β : ℕ∞) ≤ dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) 85 2 (g16 h2 hq) f 171 1) :
    ((β - 171 * j : ℕ) : ℕ∞)
      ≤ dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
          (g8 h2 hq) (dev (g16 h2 hq) f j) 85 2 := by
  rcases Nat.lt_or_ge β (171 * j) with hlt | hge
  · rw [show β - 171 * j = 0 from by omega]
    exact bot_le
  · have h := le_dv4Pin_of_le_dv4Supp h2 hq hβ
      (show 1 * (β - 171 * j) + 171 * j = β from by omega)
    rwa [dv4Pin, dv4Hgt] at h

private theorem natDegree_dev_g16_lt (f : Polynomial O) (j : ℕ) :
    (dev (g16 h2 hq) f j).natDegree < (g16 h2 hq).natDegree := by
  rcases eq_or_ne (dev (g16 h2 hq) f j) 0 with h0 | h0
  · rw [h0, Polynomial.natDegree_zero, g16_natDegree h2 hq]; norm_num
  · exact Polynomial.natDegree_lt_natDegree h0
      (degree_dev_lt (g16_monic h2 hq)
        (by rw [g16_natDegree h2 hq]; norm_num) f j)

private theorem natDegree_g16_quot_lt {A B : Polynomial O}
    (hA : A.natDegree < (g16 h2 hq).natDegree) (hB : B.natDegree < (g16 h2 hq).natDegree) :
    ((A * B) /ₘ g16 h2 hq).natDegree < (g16 h2 hq).natDegree := by
  rw [Polynomial.natDegree_divByMonic _ (g16_monic h2 hq)]
  have h := Polynomial.natDegree_mul_le (p := A) (q := B)
  omega

private theorem dev_g16_mul_one {A B : Polynomial O}
    (hA : A.natDegree < (g16 h2 hq).natDegree) (hB : B.natDegree < (g16 h2 hq).natDegree) :
    dev (g16 h2 hq) (A * B) 1 = (A * B) /ₘ g16 h2 hq := by
  have hunfold : dev (g16 h2 hq) (A * B) 1 = dev (g16 h2 hq) ((A * B) /ₘ g16 h2 hq) 0 := rfl
  rw [hunfold, dev_zero_pin]
  rcases eq_or_ne ((A * B) /ₘ g16 h2 hq) 0 with h0 | h0
  · rw [h0, Polynomial.zero_modByMonic]
  · exact (Polynomial.modByMonic_eq_self_iff (g16_monic h2 hq)).mpr
      (by rw [Polynomial.degree_eq_natDegree h0,
            Polynomial.degree_eq_natDegree (g16_monic h2 hq).ne_zero]
          exact_mod_cast natDegree_g16_quot_lt h2 hq hA hB)

/-- finite-sum ultrametric floor (private mirror of `C136l2e4.le_dv2Supp_finsetSum`, one
level up). -/
private theorem le_dv3Supp_finsetSum {ι : Type*} (s : Finset ι) (f : ι → Polynomial O)
    {k : ℕ∞} (hf : ∀ i ∈ s, k ≤ dv3Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) (f i) 85 2) :
    k ≤ dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
      (∑ i ∈ s, f i) 85 2 := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      rw [Finset.sum_empty, dv3Supp_zero_eq_top ((s2Tower h2 hq).levelDatum h2)
        (s2DepthTwoKeyAt h2 hq 2) 21 (by norm_num) (g8 h2 hq) 85 (by norm_num)]
      exact le_top
  | cons a t hat ih =>
      rw [Finset.sum_cons]
      exact le_trans (le_min (hf a (Finset.mem_cons_self a t))
          (ih fun i hi => hf i (Finset.mem_cons.2 (Or.inr hi))))
        (min_dv3Supp_le_dv3Supp_add ((s2Tower h2 hq).levelDatum h2) (s2Φ₂_monic h2 hq)
          (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num) (s2g8_monic h2 hq)
          (by rw [s2g8_natDegree h2 hq]; norm_num) (by norm_num) _ _)

/-- graded-residual finite-sum additivity (private mirror of
`C136l2e4.s2Mu3GradedRes_finsetSum_of_le`, one level up). -/
private theorem s2Mu4GradedRes_finsetSum_of_le {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial O) {m : ℕ}
    (hf : ∀ i ∈ s, (m : ℕ∞) ≤ dv3Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) (f i) 85 2) :
    s2Mu4GradedRes h2 hq m (∑ i ∈ s, f i) = ∑ i ∈ s, s2Mu4GradedRes h2 hq m (f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact s2Mu4GradedRes_zero h2 hq m
  | cons a t hat ih =>
      rw [Finset.sum_cons, Finset.sum_cons,
        s2Mu4GradedRes_add_of_le h2 hq (hf a (Finset.mem_cons_self a t))
          (le_dv3Supp_finsetSum h2 hq t f fun i hi => hf i (Finset.mem_cons.2 (Or.inr hi))),
        ih fun i hi => hf i (Finset.mem_cons.2 (Or.inr hi))]

/-- reading the μ₄ graded residual of a `g16`-multiple always evaluates to `0` at `1`
(mirror of `C136l2e4.eval_one_mu3GradedRes_g8_mul`; the carried key's residual `X + 1`
kills the eval, `1 + 1 = 0` in characteristic `2`). -/
theorem eval_one_mu4GradedRes_g16_mul {m : ℕ} (Q : Polynomial O)
    (hm : (m : ℕ∞) ≤ dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) (g16 h2 hq * Q) 85 2) :
    Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
      (s2Mu4GradedRes h2 hq m (g16 h2 hq * Q)) = 0 := by
  rcases lt_or_eq_of_le hm with hlt | heq
  · rw [s2Mu4GradedRes_zero_of_above h2 hq
      ((S2Mu4AboveGrade_iff_dv3Supp h2 hq).mpr hlt), Polynomial.eval_zero]
  · have hex : S2Mu4ExactGrade h2 hq m (g16 h2 hq * Q) :=
      (S2Mu4ExactGrade_iff_dv3Supp h2 hq).mpr heq.symm
    rw [← s2Mu4NormRes_mul_X_pow_of_exact h2 hq hex, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one,
      s2Mu4NormRes_mul h2 hq, Polynomial.eval_mul, s2Mu4NormRes_g16 h2 hq,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
      C130rp2.tooth_char_two h2 hq, zero_mul]

/-- reduction modulo `g16` does not change the eval-1 reading of the μ₄ graded residual
(mirror of `C136l2e4.eval_one_mu3GradedRes_modBy_g8`). -/
theorem eval_one_mu4GradedRes_modBy_g16 {A B : Polynomial O}
    (hA : A.natDegree < (g16 h2 hq).natDegree) (hB : B.natDegree < (g16 h2 hq).natDegree)
    {m : ℕ} (hm : (m : ℕ∞) ≤ dv3Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) A 85 2
        + dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
          (g8 h2 hq) B 85 2) :
    Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
        (s2Mu4GradedRes h2 hq m ((A * B) %ₘ g16 h2 hq))
      = Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
          (s2Mu4GradedRes h2 hq m (A * B)) := by
  have hmodfloor : (m : ℕ∞) ≤ dv3Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) ((A * B) %ₘ g16 h2 hq) 85 2 := by
    rw [dv3Supp_mul_modByKey_eq ((s2Tower h2 hq).levelDatum h2) (s2Φ₂_monic h2 hq)
      (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num) (s2g8_monic h2 hq)
      (by rw [s2g8_natDegree h2 hq]; norm_num) (by norm_num)
      (fun a b _ _ => s2_dv3Supp_mul_local h2 hq a b) (s2_isMu4Key_g16 h2 hq) hA hB]
    exact hm
  have hquotfloor : (m : ℕ∞) ≤ dv3Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) (g16 h2 hq * ((A * B) /ₘ g16 h2 hq)) 85 2 := by
    rw [s2_dv3Supp_mul_local h2 hq]
    exact hm.trans (dv3Supp_add_le_key_quot_add ((s2Tower h2 hq).levelDatum h2)
      (s2Φ₂_monic h2 hq) (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num)
      (s2g8_monic h2 hq) (by rw [s2g8_natDegree h2 hq]; norm_num) (by norm_num)
      (fun a b _ _ => s2_dv3Supp_mul_local h2 hq a b) (s2_isMu4Key_g16 h2 hq) hA hB)
  conv_rhs => rw [← Polynomial.modByMonic_add_div (A * B) (g16 h2 hq)]
  rw [s2Mu4GradedRes_add_of_le h2 hq hmodfloor hquotfloor,
    Polynomial.eval_add, eval_one_mu4GradedRes_g16_mul h2 hq _ hquotfloor, add_zero]

/-- the eval-1 product law at exact grades (mirror of
`C136l2e4.eval_one_mu3GradedRes_mul_of_exact`). -/
theorem eval_one_mu4GradedRes_mul_of_exact {m₁ m₂ : ℕ} {A B : Polynomial O}
    (hA : S2Mu4ExactGrade h2 hq m₁ A) (hB : S2Mu4ExactGrade h2 hq m₂ B) :
    Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
        (s2Mu4GradedRes h2 hq (m₁ + m₂) (A * B))
      = Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2) (s2Mu4GradedRes h2 hq m₁ A)
        * Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2) (s2Mu4GradedRes h2 hq m₂ B) := by
  have hAB : S2Mu4ExactGrade h2 hq (m₁ + m₂) (A * B) := S2Mu4ExactGrade_mul h2 hq hA hB
  rw [← s2Mu4NormRes_mul_X_pow_of_exact h2 hq hAB, ← s2Mu4NormRes_mul_X_pow_of_exact h2 hq hA,
    ← s2Mu4NormRes_mul_X_pow_of_exact h2 hq hB, s2Mu4NormRes_mul h2 hq]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one]

/-- the eval-1 product law, floor form (mirror of
`C136l2e4.eval_one_mu3GradedRes_mul_of_le`). -/
theorem eval_one_mu4GradedRes_mul_of_le {m₁ m₂ : ℕ} {A B : Polynomial O}
    (hA : (m₁ : ℕ∞) ≤ dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) A 85 2)
    (hB : (m₂ : ℕ∞) ≤ dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) B 85 2) :
    Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
        (s2Mu4GradedRes h2 hq (m₁ + m₂) (A * B))
      = Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2) (s2Mu4GradedRes h2 hq m₁ A)
        * Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2) (s2Mu4GradedRes h2 hq m₂ B) := by
  rcases lt_or_eq_of_le hA with hAlt | hAeq
  · have habove : ((m₁ + m₂ : ℕ) : ℕ∞) < dv3Supp ((s2Tower h2 hq).levelDatum h2)
        (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) (A * B) 85 2 := by
      rw [s2_dv3Supp_mul_local h2 hq]
      exact coe_lt_add_of_lt_of_le_e1 hAlt hB
    rw [s2Mu4GradedRes_zero_of_above h2 hq
      ((S2Mu4AboveGrade_iff_dv3Supp h2 hq).mpr habove),
      s2Mu4GradedRes_zero_of_above h2 hq
        ((S2Mu4AboveGrade_iff_dv3Supp h2 hq).mpr hAlt), Polynomial.eval_zero, zero_mul]
  rcases lt_or_eq_of_le hB with hBlt | hBeq
  · have habove : ((m₁ + m₂ : ℕ) : ℕ∞) < dv3Supp ((s2Tower h2 hq).levelDatum h2)
        (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) (A * B) 85 2 := by
      rw [s2_dv3Supp_mul_local h2 hq, add_comm (dv3Supp ((s2Tower h2 hq).levelDatum h2)
          (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) A 85 2)]
      have h := coe_lt_add_of_lt_of_le_e1 hBlt hA
      rwa [Nat.add_comm m₂ m₁] at h
    rw [s2Mu4GradedRes_zero_of_above h2 hq
      ((S2Mu4AboveGrade_iff_dv3Supp h2 hq).mpr habove),
      s2Mu4GradedRes_zero_of_above h2 hq
        ((S2Mu4AboveGrade_iff_dv3Supp h2 hq).mpr hBlt), Polynomial.eval_zero, mul_zero]
  · exact eval_one_mu4GradedRes_mul_of_exact h2 hq
      ((S2Mu4ExactGrade_iff_dv3Supp h2 hq).mpr hAeq.symm)
      ((S2Mu4ExactGrade_iff_dv3Supp h2 hq).mpr hBeq.symm)

/-! ### Part 3 — ★ NODE D4-07: the μ₅ coefficient convolution (untwisted, `e' = 1`) -/

private theorem s2Mu5Coeff_mul_aux {β β' : ℕ} {g z : Polynomial O}
    (hg : S2Mu5ExactGrade h2 hq β g) (hz : S2Mu5ExactGrade h2 hq β' z) (T : ℕ) :
    s2Mu5Coeff h2 hq (β + β') (g * z) T
      = ∑ t ∈ Finset.range (T + 1),
          s2Mu5Coeff h2 hq β g t * s2Mu5Coeff h2 hq β' z (T - t) := by
  have hsg : dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) 85 2 (g16 h2 hq) g 171 1 = (β : ℕ∞) := (S2Mu5ExactGrade_iff_dv4Supp h2 hq).mp hg
  have hsz : dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) 85 2 (g16 h2 hq) z 171 1 = (β' : ℕ∞) :=
    (S2Mu5ExactGrade_iff_dv4Supp h2 hq).mp hz
  have hsgz : dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) 85 2 (g16 h2 hq) (g * z) 171 1 = ((β + β' : ℕ) : ℕ∞) :=
    (S2Mu5ExactGrade_iff_dv4Supp h2 hq).mp (S2Mu5ExactGrade_mul h2 hq hg hz)
  rcases Nat.lt_or_ge (β + β') (171 * T) with hcase | hcase
  · rw [s2Mu5Coeff_eq_zero_of_grade_lt h2 hq hcase]
    refine (Finset.sum_eq_zero fun t ht => ?_).symm
    rw [Finset.mem_range] at ht
    rcases (by omega : β < 171 * t ∨ β' < 171 * (T - t)) with h | h
    · rw [s2Mu5Coeff_eq_zero_of_grade_lt h2 hq h, zero_mul]
    · rw [s2Mu5Coeff_eq_zero_of_grade_lt h2 hq h, mul_zero]
  · set m := β + β' - 171 * T with hmdef
    have hm : 1 * m + 171 * T = β + β' := by omega
    have hpinsum := le_dv4Pin_of_le_dv4Supp h2 hq (le_of_eq hsgz.symm) hm
    rw [s2Mu5Coeff_eq_eval_of_le h2 hq hm hpinsum,
      dev_mul_conv_split_monic (g16_monic h2 hq) (by rw [g16_natDegree h2 hq]; norm_num) g z T]
    have hmainfloor : ∀ j ∈ Finset.range (T + 1), (m : ℕ∞) ≤ dv3Supp
        ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
        ((dev (g16 h2 hq) g j * dev (g16 h2 hq) z (T - j)) %ₘ g16 h2 hq) 85 2 := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [dv3Supp_mul_modByKey_eq ((s2Tower h2 hq).levelDatum h2) (s2Φ₂_monic h2 hq)
        (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num) (s2g8_monic h2 hq)
        (by rw [s2g8_natDegree h2 hq]; norm_num) (by norm_num)
        (fun a b _ _ => s2_dv3Supp_mul_local h2 hq a b) (s2_isMu4Key_g16 h2 hq)
        (natDegree_dev_g16_lt h2 hq g j) (natDegree_dev_g16_lt h2 hq z (T - j))]
      refine le_trans (Nat.cast_le.mpr (show m ≤ (β - 171 * j) + (β' - 171 * (T - j))
        from by omega)) ?_
      exact coe_le_add_of_le_e1
        (exact_le_dv3Supp_dev_g16 h2 hq j (le_of_eq hsg.symm))
        (exact_le_dv3Supp_dev_g16 h2 hq (T - j) (le_of_eq hsz.symm))
    have hcarryfloor : ∀ j ∈ Finset.range T, ((m + 1 : ℕ) : ℕ∞) ≤ dv3Supp
        ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
        (dev (g16 h2 hq) (dev (g16 h2 hq) g j * dev (g16 h2 hq) z (T - 1 - j)) 1) 85 2 := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [dev_g16_mul_one h2 hq (natDegree_dev_g16_lt h2 hq g j)
        (natDegree_dev_g16_lt h2 hq z (T - 1 - j))]
      have hsharp := dv3Supp_add_le_key_quot_add ((s2Tower h2 hq).levelDatum h2)
        (s2Φ₂_monic h2 hq) (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num)
        (s2g8_monic h2 hq) (by rw [s2g8_natDegree h2 hq]; norm_num) (by norm_num)
        (fun a b _ _ => s2_dv3Supp_mul_local h2 hq a b) (s2_isMu4Key_g16 h2 hq)
        (natDegree_dev_g16_lt h2 hq g j) (natDegree_dev_g16_lt h2 hq z (T - 1 - j))
      rw [s2_dv3Supp_g16 h2 hq] at hsharp
      have hsum := le_trans (coe_le_add_of_le_e1
        (exact_le_dv3Supp_dev_g16 h2 hq j (le_of_eq hsg.symm))
        (exact_le_dv3Supp_dev_g16 h2 hq (T - 1 - j) (le_of_eq hsz.symm))) hsharp
      rcases eq_or_ne (dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
          (g8 h2 hq)
          ((dev (g16 h2 hq) g j * dev (g16 h2 hq) z (T - 1 - j)) /ₘ g16 h2 hq) 85 2) ⊤
          with htop | hfin
      · rw [htop]; exact le_top
      obtain ⟨q, hq'⟩ := ENat.ne_top_iff_exists.1 hfin
      rw [← hq'] at hsum ⊢
      have hnat : (β - 171 * j) + (β' - 171 * (T - 1 - j)) ≤ 170 + q := by
        exact_mod_cast hsum
      exact_mod_cast (show m + 1 ≤ q from by omega)
    rw [s2Mu4GradedRes_add_of_le h2 hq
        (le_dv3Supp_finsetSum h2 hq _ _ hmainfloor)
        (le_dv3Supp_finsetSum h2 hq _ _ fun j hj =>
          le_trans (Nat.cast_le.mpr (Nat.le_succ m)) (hcarryfloor j hj)),
      Polynomial.eval_add,
      s2Mu4GradedRes_finsetSum_of_le h2 hq _ _ hmainfloor,
      s2Mu4GradedRes_finsetSum_of_le h2 hq _ _ (fun j hj =>
        le_trans (Nat.cast_le.mpr (Nat.le_succ m)) (hcarryfloor j hj)),
      Polynomial.eval_finsetSum, Polynomial.eval_finsetSum]
    have hcarryzero : (∑ j ∈ Finset.range T,
        Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
          (s2Mu4GradedRes h2 hq m
            (dev (g16 h2 hq)
              (dev (g16 h2 hq) g j * dev (g16 h2 hq) z (T - 1 - j)) 1))) = 0 :=
      Finset.sum_eq_zero fun j hj => by
        rw [s2Mu4GradedRes_zero_of_above h2 hq
          ((S2Mu4AboveGrade_iff_dv3Supp h2 hq).mpr
            (lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self m)) (hcarryfloor j hj))),
          Polynomial.eval_zero]
    rw [hcarryzero, add_zero]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_range] at ht
    rcases Nat.lt_or_ge β (171 * t) with hbig | hok
    · have habove : (m : ℕ∞) < dv3Supp ((s2Tower h2 hq).levelDatum h2)
          (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
          ((dev (g16 h2 hq) g t * dev (g16 h2 hq) z (T - t)) %ₘ g16 h2 hq) 85 2 := by
        rw [dv3Supp_mul_modByKey_eq ((s2Tower h2 hq).levelDatum h2) (s2Φ₂_monic h2 hq)
          (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num) (s2g8_monic h2 hq)
          (by rw [s2g8_natDegree h2 hq]; norm_num) (by norm_num)
          (fun a b _ _ => s2_dv3Supp_mul_local h2 hq a b) (s2_isMu4Key_g16 h2 hq)
          (natDegree_dev_g16_lt h2 hq g t) (natDegree_dev_g16_lt h2 hq z (T - t))]
        refine lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self m)) ?_
        refine le_trans (Nat.cast_le.mpr (show m + 1 ≤
          (β - 171 * t) + (β' - 171 * (T - t)) from by omega)) ?_
        exact coe_le_add_of_le_e1
          (exact_le_dv3Supp_dev_g16 h2 hq t (le_of_eq hsg.symm))
          (exact_le_dv3Supp_dev_g16 h2 hq (T - t) (le_of_eq hsz.symm))
      rw [s2Mu5Coeff_eq_zero_of_grade_lt h2 hq hbig, zero_mul,
        s2Mu4GradedRes_zero_of_above h2 hq
          ((S2Mu4AboveGrade_iff_dv3Supp h2 hq).mpr habove), Polynomial.eval_zero]
    rcases Nat.lt_or_ge β' (171 * (T - t)) with hbig' | hok'
    · have habove : (m : ℕ∞) < dv3Supp ((s2Tower h2 hq).levelDatum h2)
          (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
          ((dev (g16 h2 hq) g t * dev (g16 h2 hq) z (T - t)) %ₘ g16 h2 hq) 85 2 := by
        rw [dv3Supp_mul_modByKey_eq ((s2Tower h2 hq).levelDatum h2) (s2Φ₂_monic h2 hq)
          (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num) (s2g8_monic h2 hq)
          (by rw [s2g8_natDegree h2 hq]; norm_num) (by norm_num)
          (fun a b _ _ => s2_dv3Supp_mul_local h2 hq a b) (s2_isMu4Key_g16 h2 hq)
          (natDegree_dev_g16_lt h2 hq g t) (natDegree_dev_g16_lt h2 hq z (T - t))]
        refine lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self m)) ?_
        refine le_trans (Nat.cast_le.mpr (show m + 1 ≤
          (β - 171 * t) + (β' - 171 * (T - t)) from by omega)) ?_
        exact coe_le_add_of_le_e1
          (exact_le_dv3Supp_dev_g16 h2 hq t (le_of_eq hsg.symm))
          (exact_le_dv3Supp_dev_g16 h2 hq (T - t) (le_of_eq hsz.symm))
      rw [s2Mu5Coeff_eq_zero_of_grade_lt h2 hq hbig', mul_zero,
        s2Mu4GradedRes_zero_of_above h2 hq
          ((S2Mu4AboveGrade_iff_dv3Supp h2 hq).mpr habove), Polynomial.eval_zero]
    · have hj1 : 1 * (β - 171 * t) + 171 * t = β := by omega
      have hk1 : 1 * (β' - 171 * (T - t)) + 171 * (T - t) = β' := by omega
      have hf1 : ((β - 171 * t : ℕ) : ℕ∞) ≤ dv3Supp ((s2Tower h2 hq).levelDatum h2)
          (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) (dev (g16 h2 hq) g t) 85 2 :=
        exact_le_dv3Supp_dev_g16 h2 hq t (le_of_eq hsg.symm)
      have hf2 : ((β' - 171 * (T - t) : ℕ) : ℕ∞) ≤ dv3Supp ((s2Tower h2 hq).levelDatum h2)
          (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) (dev (g16 h2 hq) z (T - t)) 85 2 :=
        exact_le_dv3Supp_dev_g16 h2 hq (T - t) (le_of_eq hsz.symm)
      rw [s2Mu5Coeff_eq_eval_of_le h2 hq hj1 hf1, s2Mu5Coeff_eq_eval_of_le h2 hq hk1 hf2]
      rw [eval_one_mu4GradedRes_modBy_g16 h2 hq
          (natDegree_dev_g16_lt h2 hq g t) (natDegree_dev_g16_lt h2 hq z (T - t))
          (le_trans (Nat.cast_le.mpr (show m ≤
            (β - 171 * t) + (β' - 171 * (T - t)) from by omega))
            (coe_le_add_of_le_e1 hf1 hf2)),
        show m = (β - 171 * t) + (β' - 171 * (T - t)) from by omega]
      exact eval_one_mu4GradedRes_mul_of_le h2 hq hf1 hf2

/-- ★ **D4-07 — the μ₅ recursive coefficient convolution, at `e' = 1` (UNTWISTED, no
carry shift)**. -/
theorem s2Mu5Coeff_mul {β β' : ℕ} {g z : Polynomial O}
    (hg : S2Mu5ExactGrade h2 hq β g) (hz : S2Mu5ExactGrade h2 hq β' z) (T : ℕ) :
    s2Mu5Coeff h2 hq (β + β') (g * z) T
      = ∑ t ∈ Finset.range (T + 1),
          s2Mu5Coeff h2 hq β g t * s2Mu5Coeff h2 hq β' z (T - t) :=
  s2Mu5Coeff_mul_aux h2 hq hg hz T

theorem s2Mu5GradedRes_mul_coeff {β β' : ℕ} {g z : Polynomial O}
    (hg : S2Mu5ExactGrade h2 hq β g) (hz : S2Mu5ExactGrade h2 hq β' z) (T : ℕ) :
    (s2Mu5GradedRes h2 hq (β + β') (g * z)).coeff T
      = (s2Mu5GradedRes h2 hq β g * s2Mu5GradedRes h2 hq β' z).coeff T := by
  rw [s2Mu5GradedRes_coeff, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, s2Mu5Coeff_mul h2 hq hg hz T]
  exact Finset.sum_congr rfl fun t _ => by rw [s2Mu5GradedRes_coeff, s2Mu5GradedRes_coeff]

/-- ★★ **D4-07's second signed exit: the UNTWISTED graded multiplication, for EVERY
grade pair** (no preceding-group hypothesis needed, `S2Mu5PrevGrade` being landed as ALL
grades — the `e' = 1` collapse). -/
theorem s2Mu5GradedRes_mul {β β' : ℕ} {g z : Polynomial O}
    (hg : S2Mu5ExactGrade h2 hq β g) (hz : S2Mu5ExactGrade h2 hq β' z) :
    s2Mu5GradedRes h2 hq (β + β') (g * z)
      = s2Mu5GradedRes h2 hq β g * s2Mu5GradedRes h2 hq β' z :=
  Polynomial.ext fun T => s2Mu5GradedRes_mul_coeff h2 hq hg hz T

theorem s2Mu5_graded_mul :
    ∀ β β' (g z : Polynomial O),
      S2Mu5ExactGrade h2 hq β g → S2Mu5ExactGrade h2 hq β' z →
      S2Mu5ExactGrade h2 hq (β + β') (g * z) ∧
        s2Mu5GradedRes h2 hq (β + β') (g * z)
          = s2Mu5GradedRes h2 hq β g * s2Mu5GradedRes h2 hq β' z :=
  fun _ _ _ _ hg hz => ⟨S2Mu5ExactGrade_mul h2 hq hg hz, s2Mu5GradedRes_mul h2 hq hg hz⟩

/-! ## D4-08 — scalar nonzero below degree 16 (mirror of `C136d2`'s D3-11 Part 3, one
level up).  The forced slot-`0` read (the ONLY live slot below degree 16, since `e' = 1`
gives NO parity ambiguity) plus the ALREADY-LANDED μ₄-level collapse-to-constant
`C136d3.s2Mu4GradedRes_eq_C_of_natDegree_lt_sixteen` and nonvanishing
`C136d2.s2Mu4GradedRes_ne_zero_of_exact` — a contradiction argument, no fresh
eval-collapse lemma needed: the campaign's fence `16 = 2 · deg(g8)` is EXACTLY the fence
the landed μ₄-level collapse already carries. -/

theorem s2Mu5GradedRes_coeff_zero_ne_zero_of_exact {β : ℕ} {g : Polynomial O}
    (hg : S2Mu5ExactGrade h2 hq β g) (hdeg : g.natDegree < 16) :
    (s2Mu5GradedRes h2 hq β g).coeff 0 ≠ 0 := by
  obtain ⟨s, hgate⟩ := exists_mu5SlotOnGrade_of_exact h2 hq hg
  have hs0 : s = 0 := by
    by_contra hs
    obtain ⟨m, hm, -⟩ := (s2Mu5SlotOnGrade_iff h2 hq).mp hgate
    have hdev : dev (g16 h2 hq) g s = 0 :=
      dev_eq_zero_of_lt (g16_monic h2 hq) (by rw [g16_natDegree h2 hq]; norm_num) g s
        (by rw [g16_natDegree h2 hq]; omega)
    have htop : dv4Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
        (g8 h2 hq) 85 2 (g16 h2 hq) g s = ⊤ := by
      rw [dv4Pin, hdev]
      exact dv4Hgt_zero ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21
        (by norm_num) (g8 h2 hq) 85 (by norm_num)
    rw [htop] at hm
    exact WithTop.top_ne_coe hm
  subst hs0
  have hdevg : dev (g16 h2 hq) g 0 = g := by
    rw [dev_zero_pin]
    exact (Polynomial.modByMonic_eq_self_iff (g16_monic h2 hq)).mpr
      (Polynomial.degree_lt_degree (by rw [g16_natDegree h2 hq]; omega))
  have hinner : S2Mu4ExactGrade h2 hq β g := by
    have h := s2Mu5SlotOnGrade_inner_exact h2 hq hgate
    rwa [show β - 171 * 0 = β from by omega, hdevg] at h
  have hslot := s2Mu5Coeff_slot h2 hq hgate
  rw [show β - 171 * 0 = β from by omega, hdevg, s2Mu5Eps_eq_one, one_mul] at hslot
  rw [s2Mu5GradedRes_coeff, hslot]
  intro hc0
  have hcollapse := s2Mu4GradedRes_eq_C_of_natDegree_lt_sixteen h2 hq hdeg β
  rw [hcollapse, Polynomial.eval_C] at hc0
  exact s2Mu4GradedRes_ne_zero_of_exact h2 hq hinner (by rw [hcollapse, hc0, Polynomial.C_0])

theorem tooth_mu5_scalar_fires :
    (s2Mu5GradedRes h2 hq 0 (1 : Polynomial O)).coeff 0 ≠ 0 := by
  refine s2Mu5GradedRes_coeff_zero_ne_zero_of_exact h2 hq ?_
    (by norm_num [Polynomial.natDegree_one])
  unfold S2Mu5ExactGrade
  rw [s2Hgt₅_one_eq_zero]
  norm_num

/-! ## D4-09 — the normalized μ₅ operator `s2Mu5NormRes` (mirror of `C136d2`'s D3-12).
Since the μ₅ product `s2Mu5GradedRes_mul` (D4-07) is UNTWISTED (no `X`-power carry at
`e' = 1`), the `natTrailingDegree`/normalized-multiplication engine is genuinely simpler
than its `e' = 2` mirror. -/

noncomputable def s2Mu5GradeOf (g : Polynomial O) : ℕ :=
  (dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) 85 2
    (g16 h2 hq) g 171 1).toNat

theorem S2Mu5ExactGrade_s2Mu5GradeOf {g : Polynomial O} (hg : g ≠ 0) :
    S2Mu5ExactGrade h2 hq (s2Mu5GradeOf h2 hq g) g :=
  (S2Mu5ExactGrade_iff_dv4Supp h2 hq).mpr
    (ENat.coe_toNat
      (dv4Supp_ne_top_of_ne_zero ((s2Tower h2 hq).levelDatum h2) (s2Φ₂_monic h2 hq)
        (by rw [s2Φ₂_natDegree h2 hq]; norm_num) 21 2 (s2g8_monic h2 hq)
        (by rw [s2g8_natDegree h2 hq]; norm_num) 85 2 (g16_monic h2 hq)
        (by rw [g16_natDegree h2 hq]; norm_num) 171 1 hg)).symm

theorem s2Mu5GradeOf_eq_of_exact {β : ℕ} {g : Polynomial O}
    (hg : S2Mu5ExactGrade h2 hq β g) : s2Mu5GradeOf h2 hq g = β := by
  unfold s2Mu5GradeOf
  rw [(S2Mu5ExactGrade_iff_dv4Supp h2 hq).mp hg]
  exact ENat.toNat_coe β

noncomputable def s2Mu5NormRes (g : Polynomial O) :
    Polynomial ((s2DepthTwo h2 hq).fld 2) :=
  Polynomial.divX^[(s2Mu5GradedRes h2 hq (s2Mu5GradeOf h2 hq g) g).natTrailingDegree]
    (s2Mu5GradedRes h2 hq (s2Mu5GradeOf h2 hq g) g)

theorem s2Mu5NormRes_of_exact {β : ℕ} {g : Polynomial O}
    (hg : S2Mu5ExactGrade h2 hq β g) :
    s2Mu5NormRes h2 hq g =
      Polynomial.divX^[(s2Mu5GradedRes h2 hq β g).natTrailingDegree]
        (s2Mu5GradedRes h2 hq β g) := by
  unfold s2Mu5NormRes
  rw [s2Mu5GradeOf_eq_of_exact h2 hq hg]

theorem s2Mu5NormRes_coeff (g : Polynomial O) (t : ℕ) :
    (s2Mu5NormRes h2 hq g).coeff t =
      (s2Mu5GradedRes h2 hq (s2Mu5GradeOf h2 hq g) g).coeff
        (t + (s2Mu5GradedRes h2 hq (s2Mu5GradeOf h2 hq g) g).natTrailingDegree) := by
  unfold s2Mu5NormRes
  exact C130rp8.coeff_divX_iterate _ _ _

theorem s2Mu5NormRes_zero : s2Mu5NormRes h2 hq (0 : Polynomial O) = 0 := by
  unfold s2Mu5NormRes
  rw [s2Mu5GradedRes_zero h2 hq]
  simp

theorem s2Mu5NormRes_mul_X_pow_of_exact {β : ℕ} {g : Polynomial O}
    (hg : S2Mu5ExactGrade h2 hq β g) :
    s2Mu5NormRes h2 hq g * Polynomial.X ^ (s2Mu5GradedRes h2 hq β g).natTrailingDegree
      = s2Mu5GradedRes h2 hq β g := by
  rw [s2Mu5NormRes_of_exact h2 hq hg]
  exact C130rp8.divX_iterate_mul_X_pow le_rfl

/-- ★ **the μ₅ graded residual is ALWAYS nonzero at an exact grade** (mirror of
`C136d2.s2Mu4GradedRes_ne_zero_of_exact`; the digit `dev(g16,g,s)` automatically has
degree `< 16`, so the ALREADY-LANDED μ₄-level collapse fires unconditionally — no degree
hypothesis on `g` itself). -/
theorem s2Mu5GradedRes_ne_zero_of_exact {β : ℕ} {g : Polynomial O}
    (hg : S2Mu5ExactGrade h2 hq β g) : s2Mu5GradedRes h2 hq β g ≠ 0 := by
  obtain ⟨s, hgate⟩ := exists_mu5SlotOnGrade_of_exact h2 hq hg
  set A := dev (g16 h2 hq) g s with hAdef
  have hinner : S2Mu4ExactGrade h2 hq (β - 171 * s) A := s2Mu5SlotOnGrade_inner_exact h2 hq hgate
  have hdeg : A.natDegree < 16 := by
    rcases eq_or_ne A 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]; norm_num
    · have h := Polynomial.natDegree_lt_natDegree h0
        (degree_dev_lt (g16_monic h2 hq) (by rw [g16_natDegree h2 hq]; norm_num) g s)
      rwa [g16_natDegree h2 hq] at h
  have hcoeff := s2Mu5Coeff_slot h2 hq hgate
  rw [s2Mu5Eps_eq_one, one_mul] at hcoeff
  have heval_collapse : Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
      (s2Mu4GradedRes h2 hq (β - 171 * s) A)
      = (s2Mu4GradedRes h2 hq (β - 171 * s) A).coeff 0 := by
    conv_lhs => rw [s2Mu4GradedRes_eq_C_of_natDegree_lt_sixteen h2 hq hdeg (β - 171 * s)]
    exact Polynomial.eval_C
  rw [heval_collapse] at hcoeff
  have hne : (s2Mu4GradedRes h2 hq (β - 171 * s) A).coeff 0 ≠ 0 := by
    intro hc0
    have hzero : s2Mu4GradedRes h2 hq (β - 171 * s) A = 0 := by
      rw [s2Mu4GradedRes_eq_C_of_natDegree_lt_sixteen h2 hq hdeg (β - 171 * s), hc0,
        Polynomial.C_0]
    exact s2Mu4GradedRes_ne_zero_of_exact h2 hq hinner hzero
  intro hzero
  apply hne
  rw [← hcoeff, ← s2Mu5GradedRes_coeff, hzero, Polynomial.coeff_zero]

theorem s2Mu5NormRes_coeff_zero_ne_zero {g : Polynomial O} (hg : g ≠ 0) :
    (s2Mu5NormRes h2 hq g).coeff 0 ≠ 0 := by
  have hne : s2Mu5GradedRes h2 hq (s2Mu5GradeOf h2 hq g) g ≠ 0 :=
    s2Mu5GradedRes_ne_zero_of_exact h2 hq (S2Mu5ExactGrade_s2Mu5GradeOf h2 hq hg)
  rw [s2Mu5NormRes_coeff, zero_add]
  exact fun h0 => hne (Polynomial.coeff_natTrailingDegree_eq_zero.mp h0)

theorem s2Mu5NormRes_ne_zero {g : Polynomial O} (hg : g ≠ 0) :
    s2Mu5NormRes h2 hq g ≠ 0 :=
  fun h0 => s2Mu5NormRes_coeff_zero_ne_zero h2 hq hg (by rw [h0, Polynomial.coeff_zero])

/-- **the `natTrailingDegree` additivity**, UNTWISTED at `e' = 1` (contrast the μ₄ mirror
`C136d2.s2Mu4GradedRes_natTrailingDegree_mul`, which carries an extra `β%2*β'%2` twist
term — absent here since `s2Mu5GradedRes_mul` has no `X`-power factor at all). -/
theorem s2Mu5GradedRes_natTrailingDegree_mul {β β' : ℕ} {g z : Polynomial O}
    (hg : S2Mu5ExactGrade h2 hq β g) (hz : S2Mu5ExactGrade h2 hq β' z) :
    (s2Mu5GradedRes h2 hq (β + β') (g * z)).natTrailingDegree =
      (s2Mu5GradedRes h2 hq β g).natTrailingDegree +
        (s2Mu5GradedRes h2 hq β' z).natTrailingDegree := by
  have hgne : s2Mu5GradedRes h2 hq β g ≠ 0 := s2Mu5GradedRes_ne_zero_of_exact h2 hq hg
  have hzne : s2Mu5GradedRes h2 hq β' z ≠ 0 := s2Mu5GradedRes_ne_zero_of_exact h2 hq hz
  rw [s2Mu5GradedRes_mul h2 hq hg hz, Polynomial.natTrailingDegree_mul hgne hzne]

theorem s2Mu5NormRes_mul_of_exact {β β' : ℕ} {g z : Polynomial O}
    (hg : S2Mu5ExactGrade h2 hq β g) (hz : S2Mu5ExactGrade h2 hq β' z) :
    s2Mu5NormRes h2 hq (g * z) = s2Mu5NormRes h2 hq g * s2Mu5NormRes h2 hq z := by
  have hgz := S2Mu5ExactGrade_mul h2 hq hg hz
  have hntd := s2Mu5GradedRes_natTrailingDegree_mul h2 hq hg hz
  refine mul_right_cancel₀
    (pow_ne_zero ((s2Mu5GradedRes h2 hq (β + β') (g * z)).natTrailingDegree)
      Polynomial.X_ne_zero) ?_
  calc
    s2Mu5NormRes h2 hq (g * z) *
          Polynomial.X ^ (s2Mu5GradedRes h2 hq (β + β') (g * z)).natTrailingDegree
        = s2Mu5GradedRes h2 hq (β + β') (g * z) :=
          s2Mu5NormRes_mul_X_pow_of_exact h2 hq hgz
    _ = s2Mu5GradedRes h2 hq β g * s2Mu5GradedRes h2 hq β' z :=
          s2Mu5GradedRes_mul h2 hq hg hz
    _ = (s2Mu5NormRes h2 hq g *
            Polynomial.X ^ (s2Mu5GradedRes h2 hq β g).natTrailingDegree) *
          (s2Mu5NormRes h2 hq z *
            Polynomial.X ^ (s2Mu5GradedRes h2 hq β' z).natTrailingDegree) := by
          rw [s2Mu5NormRes_mul_X_pow_of_exact h2 hq hg,
            s2Mu5NormRes_mul_X_pow_of_exact h2 hq hz]
    _ = (s2Mu5NormRes h2 hq g * s2Mu5NormRes h2 hq z) *
          Polynomial.X ^ ((s2Mu5GradedRes h2 hq β g).natTrailingDegree +
            (s2Mu5GradedRes h2 hq β' z).natTrailingDegree) := by ring
    _ = (s2Mu5NormRes h2 hq g * s2Mu5NormRes h2 hq z) *
          Polynomial.X ^ (s2Mu5GradedRes h2 hq (β + β') (g * z)).natTrailingDegree := by
          rw [hntd]

theorem s2Mu5NormRes_mul (g z : Polynomial O) :
    s2Mu5NormRes h2 hq (g * z) = s2Mu5NormRes h2 hq g * s2Mu5NormRes h2 hq z := by
  rcases eq_or_ne g 0 with rfl | hgne
  · rw [zero_mul, s2Mu5NormRes_zero h2 hq, zero_mul]
  rcases eq_or_ne z 0 with rfl | hzne
  · rw [mul_zero, s2Mu5NormRes_zero h2 hq, mul_zero]
  exact s2Mu5NormRes_mul_of_exact h2 hq
    (S2Mu5ExactGrade_s2Mu5GradeOf h2 hq hgne) (S2Mu5ExactGrade_s2Mu5GradeOf h2 hq hzne)

theorem S2Mu5ExactGrade_one : S2Mu5ExactGrade h2 hq 0 (1 : Polynomial O) := by
  unfold S2Mu5ExactGrade
  rw [s2Hgt₅_one_eq_zero]
  norm_num

theorem s2Mu5GradedRes_one : s2Mu5GradedRes h2 hq 0 (1 : Polynomial O) = 1 := by
  refine Polynomial.ext fun t => ?_
  match t with
  | 0 =>
      rw [Polynomial.coeff_one_zero]
      exact C132rp1.s2Fld₂_eq_one_of_ne_zero h2 hq
        (s2Mu5GradedRes_coeff_zero_ne_zero_of_exact h2 hq
          (S2Mu5ExactGrade_one h2 hq) (by norm_num [Polynomial.natDegree_one]))
  | t + 1 =>
      rw [s2Mu5GradedRes_coeff, Polynomial.coeff_one]
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      exact s2Mu5Coeff_eq_zero_of_natDegree_lt h2 hq
        (by norm_num [Polynomial.natDegree_one])

theorem s2Mu5NormRes_one : s2Mu5NormRes h2 hq (1 : Polynomial O) = 1 := by
  rw [s2Mu5NormRes_of_exact h2 hq (S2Mu5ExactGrade_one h2 hq),
    s2Mu5GradedRes_one h2 hq, Polynomial.natTrailingDegree_one]
  rfl

theorem S2Mu5ExactGrade_key_pow (k : ℕ) :
    S2Mu5ExactGrade h2 hq (171 * k) ((g16 h2 hq : Polynomial O) ^ k) := by
  induction k with
  | zero => rw [pow_zero, Nat.mul_zero]; exact S2Mu5ExactGrade_one h2 hq
  | succ k ih =>
      rw [show 171 * (k + 1) = 171 * k + 171 from by ring, pow_succ]
      exact S2Mu5ExactGrade_mul h2 hq ih (tooth_g16 h2 hq)

private theorem g16_one_mod_local : (1 : Polynomial O) %ₘ g16 h2 hq = 1 :=
  (Polynomial.modByMonic_eq_self_iff (g16_monic h2 hq)).mpr
    (Polynomial.degree_lt_degree
      (by rw [Polynomial.natDegree_one, g16_natDegree h2 hq]; norm_num))

private theorem g16_dev1_local : dev (g16 h2 hq) (g16 h2 hq : Polynomial O) 1 = 1 := by
  have h := dev_mul_pow (g16_monic h2 hq) 1 (1 : Polynomial O) 0
  rw [Nat.add_zero, one_mul, pow_one] at h
  rw [h]
  exact g16_one_mod_local h2 hq

private theorem s2_dv4Hgt_one_local :
    dv4Hgt ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) 85 2
      (1 : Polynomial O) = (0 : ℕ∞) := by
  apply C130s6.toZ_inj
  rw [dv4Hgt, ← s2Hgt₄_eq_dv3Supp h2 hq, s2Hgt₄_one_eq_zero h2 hq]
  rfl

private theorem g16_dev0_local : dev (g16 h2 hq) (g16 h2 hq : Polynomial O) 0 = 0 := by
  have h := dev_mul_pow_of_lt (g16_monic h2 hq) 1 1 0 Nat.one_pos
  rwa [one_mul, pow_one] at h

/-- ★ **the carried outer key's own μ₅ graded residual is `X`** (NOT `1` — contrast the
`e' = 2` mirror `C136d1.s2Mu4GradedRes_key`, where slot `1` maps to coefficient index `0`
via the `/2` rescaling; at `e' = 1` slot `1` maps to index `1` directly, so the residual
survives as `X`, not a bare constant). -/
theorem s2Mu5GradedRes_key :
    s2Mu5GradedRes h2 hq 171 (g16 h2 hq : Polynomial O) = Polynomial.X := by
  have hgate : S2Mu5SlotOnGrade h2 hq 171 (g16 h2 hq) 1 := by
    refine (s2Mu5SlotOnGrade_iff h2 hq).mpr ⟨0, ?_, by norm_num⟩
    rw [dv4Pin, g16_dev1_local h2 hq, s2_dv4Hgt_one_local h2 hq]
    rfl
  refine Polynomial.ext fun t => ?_
  match t with
  | 0 =>
      rw [s2Mu5GradedRes_coeff, Polynomial.coeff_X_zero]
      refine s2Mu5Coeff_eq_zero_of_dv4Pin_top h2 hq ?_
      rw [dv4Pin, g16_dev0_local h2 hq]
      exact dv4Hgt_zero ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21
        (by norm_num) (g8 h2 hq) 85 (by norm_num)
  | 1 =>
      rw [s2Mu5GradedRes_coeff, Polynomial.coeff_X_one]
      have hslot := s2Mu5Coeff_slot h2 hq hgate
      rw [g16_dev1_local h2 hq, s2Mu5Eps_eq_one, one_mul,
        show (171 : ℕ) - 171 * 1 = 0 from by norm_num, s2Mu4GradedRes_one h2 hq,
        Polynomial.eval_one] at hslot
      exact hslot
  | t + 2 =>
      rw [s2Mu5GradedRes_coeff, show (Polynomial.X : Polynomial ((s2DepthTwo h2 hq).fld 2)).coeff
        (t + 2) = 0 from by rw [Polynomial.coeff_X]; simp]
      refine s2Mu5Coeff_eq_zero_of_dv4Pin_top h2 hq ?_
      rw [dv4Pin, dev_eq_zero_of_lt (g16_monic h2 hq)
        (by rw [g16_natDegree h2 hq]; norm_num) (g16 h2 hq) _
        (by rw [g16_natDegree h2 hq]; omega)]
      exact dv4Hgt_zero ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21
        (by norm_num) (g8 h2 hq) 85 (by norm_num)

theorem s2Mu5GradedRes_key_pow (k : ℕ) :
    s2Mu5GradedRes h2 hq (171 * k) ((g16 h2 hq : Polynomial O) ^ k) = Polynomial.X ^ k := by
  induction k with
  | zero => rw [pow_zero, Nat.mul_zero, s2Mu5GradedRes_one h2 hq]; norm_num
  | succ k ih =>
      have h := s2Mu5GradedRes_mul h2 hq (S2Mu5ExactGrade_key_pow h2 hq k) (tooth_g16 h2 hq)
      rw [ih, s2Mu5GradedRes_key h2 hq] at h
      rw [show 171 * (k + 1) = 171 * k + 171 from by ring, pow_succ, h, pow_succ]

theorem s2Mu5NormRes_key : s2Mu5NormRes h2 hq (g16 h2 hq : Polynomial O) = 1 := by
  have h := s2Mu5NormRes_mul_X_pow_of_exact h2 hq (tooth_g16 h2 hq)
  rw [s2Mu5GradedRes_key h2 hq, Polynomial.natTrailingDegree_X, pow_one] at h
  exact mul_right_cancel₀ Polynomial.X_ne_zero (by rw [h, one_mul])

theorem s2Mu5NormRes_key_pow (k : ℕ) :
    s2Mu5NormRes h2 hq ((g16 h2 hq : Polynomial O) ^ k) = 1 := by
  induction k with
  | zero => rw [pow_zero, s2Mu5NormRes_one h2 hq]
  | succ k ih => rw [pow_succ, s2Mu5NormRes_mul h2 hq, ih, s2Mu5NormRes_key h2 hq, mul_one]

/-! ## D4-10 — the normalizer's exact μ₅ grade, finishing T5

`chainNormBelow 4 171 = Λ = 2·x·Φ′·Φ₂·g₈` (`C136t`'s landed `s2Mu5Lambda`) has degree `15`
and is nonzero — BOTH already landed (`C136t.s2Mu5Lambda_natDegree`/`_ne_zero`).  This row
prices the missing piece: its exact μ₅ grade is `171`.  The route is a multiplicative peel
down the tower (μ₅→μ₄→μ₃→base), mirroring D3-13's "single lower-key slot" mechanism
(`C136d2.dv3Supp_eq_two_smul_of_natDegree_lt`) at each transition, applied THREE times
(once per level Λ's factorization crosses), since Λ carries all three lower keys as exact
factors: `Λ = g₈ · (2·x·Φ′·Φ₂) = g₈ · (Φ₂ · (2·x·Φ′))`. -/

/-- negation-invariance of `s2Hgt₅` (private local copy, mirroring `C136d2`'s
`s2Hgt₄_neg_local`). -/
private theorem s2Hgt₅_neg_local (A : Polynomial O) : s2Hgt₅ h2 hq (-A) = s2Hgt₅ h2 hq A := by
  rw [s2Hgt₅_eq_dv4Supp, s2Hgt₅_eq_dv4Supp,
    dv4Supp_neg _ (s2Φ₂_monic h2 hq) 21 2 (s2g8_monic h2 hq) 85 2 (g16_monic h2 hq)]

/-- the base→μ₃ "single Φ′-slot" collapse (private local copy of the mechanism `C132rp10b`
uses for `corr`, one level up: for `A` of degree `< deg Φ₂ = 4`, the μ₃ grade is exactly
twice the base grade). -/
private theorem dv2Supp_eq_two_smul_of_natDegree_lt {A : Polynomial O} (hA : A.natDegree < 4) :
    dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) A 21 2
      = 2 • dvSupp (s2Frame h2 hq) A 5 2 := by
  have hdev0 : dev (s2DepthTwoKeyAt h2 hq 2) A 0 = A :=
    (Polynomial.modByMonic_eq_self_iff (s2Φ₂_monic h2 hq)).mpr
      (Polynomial.degree_lt_degree (by rw [s2Φ₂_natDegree h2 hq]; omega))
  have hpin0 : dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) A 0
      = dvSupp (s2Frame h2 hq) A 5 2 := by
    rw [dv2Pin, hdev0]
    exact toZ_inj ((s2Hgt₂_eq_dv2Hgt h2 hq A).symm.trans (s2Hgt₂_eq_dvSupp h2 hq A))
  have hpinj : ∀ j, 1 ≤ j →
      dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) A j = ⊤ := by
    intro j hj
    have hdevj : dev (s2DepthTwoKeyAt h2 hq 2) A j = 0 :=
      dev_eq_zero_of_lt (s2Φ₂_monic h2 hq) (by rw [s2Φ₂_natDegree h2 hq]; norm_num) A j
        (by rw [s2Φ₂_natDegree h2 hq]
            have hj4 : (4 : ℕ) ≤ j * 4 := Nat.le_mul_of_pos_left 4 hj
            omega)
    rw [dv2Pin, hdevj]
    exact dv2Hgt_zero _
  rw [dv2Supp]
  refine le_antisymm ?_ ?_
  · refine le_trans (Finset.inf_le (Finset.mem_range.mpr (Nat.succ_pos _))) ?_
    rw [hpin0]; simp
  · refine Finset.le_inf fun j _ => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · rw [hpin0]; simp
    · rw [hpinj j hj1, C118a.smul_top_pos (by norm_num), top_add]
      exact le_top

/-- the μ₃→μ₄ "single g₈-slot" collapse (private local copy of `C136d2`'s
`dv3Supp_eq_two_smul_of_natDegree_lt`, per the corpus's private-copy convention). -/
private theorem dv3Supp_eq_two_smul_of_natDegree_lt {A : Polynomial O} (hA : A.natDegree < 8) :
    dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) A 85 2
      = 2 • dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) A 21 2 := by
  have hdev0 : dev (g8 h2 hq) A 0 = A :=
    (Polynomial.modByMonic_eq_self_iff (s2g8_monic h2 hq)).mpr
      (Polynomial.degree_lt_degree (by rw [s2g8_natDegree h2 hq]; omega))
  have hpin0 : dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) A 0
      = dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) A 21 2 := by
    rw [dv3Pin, hdev0, dv3Hgt]
  have hpinj : ∀ j, 1 ≤ j → dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) A j = ⊤ := by
    intro j hj
    have hdevj : dev (g8 h2 hq) A j = 0 :=
      dev_eq_zero_of_lt (s2g8_monic h2 hq) (by rw [s2g8_natDegree h2 hq]; norm_num) A j
        (by rw [s2g8_natDegree h2 hq]
            have hj8 : (8 : ℕ) ≤ j * 8 := Nat.le_mul_of_pos_left 8 hj
            omega)
    rw [dv3Pin, hdevj]
    exact dv3Hgt_zero _ _ _ (by norm_num)
  rw [dv3Supp]
  refine le_antisymm ?_ ?_
  · refine le_trans (Finset.inf_le (Finset.mem_range.mpr (Nat.succ_pos _))) ?_
    rw [hpin0]; simp
  · refine Finset.le_inf fun j _ => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · rw [hpin0]; simp
    · rw [hpinj j hj1, C118a.smul_top_pos (by norm_num), top_add]
      exact le_top

/-- the μ₄→μ₅ direct identity at `ℓ₅ = 1` (NO scaling, unlike the two collapses above):
for `A` of degree `< deg g16 = 16`, the μ₅-cleared support IS the μ₄-cleared support. -/
private theorem dv4Supp_eq_dv3Supp_of_natDegree_lt {A : Polynomial O} (hA : A.natDegree < 16) :
    dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) 85 2
      (g16 h2 hq) A 171 1
      = dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) A 85 2 := by
  have hdev0 : dev (g16 h2 hq) A 0 = A :=
    (Polynomial.modByMonic_eq_self_iff (g16_monic h2 hq)).mpr
      (Polynomial.degree_lt_degree (by rw [g16_natDegree h2 hq]; omega))
  have hpin0 : dv4Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
      85 2 (g16 h2 hq) A 0
      = dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) A 85 2 := by
    rw [dv4Pin, hdev0, dv4Hgt]
  have hpinj : ∀ j, 1 ≤ j → dv4Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) 85 2 (g16 h2 hq) A j = ⊤ := by
    intro j hj
    have hdevj : dev (g16 h2 hq) A j = 0 :=
      dev_eq_zero_of_lt (g16_monic h2 hq) (by rw [g16_natDegree h2 hq]; norm_num) A j
        (by rw [g16_natDegree h2 hq]
            have hj16 : (16 : ℕ) ≤ j * 16 := Nat.le_mul_of_pos_left 16 hj
            omega)
    rw [dv4Pin, hdevj]
    exact dv4Hgt_zero _ _ _ (by norm_num) _ _ (by norm_num)
  rw [dv4Supp]
  refine le_antisymm ?_ ?_
  · refine le_trans (Finset.inf_le (Finset.mem_range.mpr (Nat.succ_pos _))) ?_
    rw [hpin0]; simp
  · refine Finset.le_inf fun j _ => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · rw [hpin0]; simp
    · rw [hpinj j hj1, C118a.smul_top_pos (by norm_num), top_add]
      exact le_top

/-- **the μ₄-level grade of `Λ'` matches its μ₅-level grade, at degree `< 16`** (`ℓ₅ = 1`
gives a DIRECT identity, no scaling — the generic collapse bridge D4-11 reuses). -/
theorem s2Mu4ExactGrade_of_s2Mu5ExactGrade_natDegree_lt {β : ℕ} {A : Polynomial O}
    (hgrade : S2Mu5ExactGrade h2 hq β A) (hdeg : A.natDegree < 16) :
    S2Mu4ExactGrade h2 hq β A := by
  rw [S2Mu4ExactGrade_iff_dv3Supp, ← dv4Supp_eq_dv3Supp_of_natDegree_lt h2 hq hdeg]
  exact (S2Mu5ExactGrade_iff_dv4Supp h2 hq).mp hgrade

/-- ★ **the μ₄-level grade of `Λ` is `171`**: the multiplicative peel
`Λ = g₈ · (Φ₂ · (2·x·Φ′))`, with base-level tooth data (`tooth_key`, `tooth_X`,
`s2Hgt₂_C_two`) lifted through the two collapses. -/
theorem s2Mu5Lambda_mu4ExactGrade : S2Mu4ExactGrade h2 hq 171 (s2Mu5Lambda h2 hq) := by
  have hkey1 : s2DepthThreeKeyAt h2 hq 1 = (s2Frame h2 hq).key := s2DepthThreeKeyAt_one h2 hq
  have hkey2 : s2DepthThreeKeyAt h2 hq 2 = s2DepthTwoKeyAt h2 hq 2 := s2DepthThreeKeyAt_two h2 hq
  have hkey3 : s2DepthThreeKeyAt h2 hq 3 = g8 h2 hq := s2DepthThreeKeyAt_three h2 hq
  have hC2 : S2ExactGrade h2 hq 4 (Polynomial.C (2 : O)) := by
    show s2Hgt₂ h2 hq _ = _
    rw [s2Hgt₂_C_two h2 hq]; norm_num
  have hR0base : S2ExactGrade h2 hq 11
      (Polynomial.C (2 : O) * Polynomial.X * (s2Frame h2 hq).key) := by
    have h1 : S2ExactGrade h2 hq 6 (Polynomial.C (2 : O) * Polynomial.X) :=
      S2ExactGrade_mul h2 hq hC2 (C130rp0.tooth_X h2 hq)
    exact S2ExactGrade_mul h2 hq h1 (C130rp0.tooth_key h2 hq)
  have hkdeg : ((s2Frame h2 hq).key : Polynomial O).natDegree = 2 := by
    rw [C35b.key_eq h2 hq]; exact s2Key_natDegree
  have hR0deg : (Polynomial.C (2 : O) * Polynomial.X * (s2Frame h2 hq).key).natDegree < 4 := by
    calc (Polynomial.C (2 : O) * Polynomial.X * (s2Frame h2 hq).key).natDegree
        ≤ (Polynomial.C (2 : O) * Polynomial.X).natDegree
            + ((s2Frame h2 hq).key : Polynomial O).natDegree := Polynomial.natDegree_mul_le
      _ < 4 := by
          have h1 : (Polynomial.C (2 : O) * Polynomial.X).natDegree ≤ 1 := by
            calc (Polynomial.C (2 : O) * Polynomial.X).natDegree
                ≤ (Polynomial.C (2 : O)).natDegree + (Polynomial.X : Polynomial O).natDegree :=
                  Polynomial.natDegree_mul_le
              _ ≤ 1 := by rw [Polynomial.natDegree_C, Polynomial.natDegree_X]
          omega
  have hR0mu3 : S2Mu3ExactGrade h2 hq 22
      (Polynomial.C (2 : O) * Polynomial.X * (s2Frame h2 hq).key) := by
    show s2Hgt₃ h2 hq _ = _
    rw [s2Hgt₃_eq_dv2Supp, dv2Supp_eq_two_smul_of_natDegree_lt h2 hq hR0deg,
      (S2ExactGrade_iff_dvSupp h2 hq).mp hR0base, nsmul_eq_mul]
    norm_cast
  have hR1mu3 : S2Mu3ExactGrade h2 hq 43
      (s2DepthTwoKeyAt h2 hq 2 * (Polynomial.C (2 : O) * Polynomial.X * (s2Frame h2 hq).key)) :=
    S2Mu3ExactGrade_mul h2 hq (tooth_Φ₂ h2 hq) hR0mu3
  have hR1deg : (s2DepthTwoKeyAt h2 hq 2 *
      (Polynomial.C (2 : O) * Polynomial.X * (s2Frame h2 hq).key)).natDegree < 8 := by
    have h1 : (s2DepthTwoKeyAt h2 hq 2 : Polynomial O).natDegree = 4 := s2Φ₂_natDegree h2 hq
    calc (s2DepthTwoKeyAt h2 hq 2 *
        (Polynomial.C (2 : O) * Polynomial.X * (s2Frame h2 hq).key)).natDegree
        ≤ (s2DepthTwoKeyAt h2 hq 2 : Polynomial O).natDegree
            + (Polynomial.C (2 : O) * Polynomial.X * (s2Frame h2 hq).key).natDegree :=
          Polynomial.natDegree_mul_le
      _ < 8 := by omega
  have hR1mu4 : S2Mu4ExactGrade h2 hq 86
      (s2DepthTwoKeyAt h2 hq 2 * (Polynomial.C (2 : O) * Polynomial.X * (s2Frame h2 hq).key)) := by
    show s2Hgt₄ h2 hq _ = _
    rw [s2Hgt₄_eq_dv3Supp, dv3Supp_eq_two_smul_of_natDegree_lt h2 hq hR1deg,
      (S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp hR1mu3, nsmul_eq_mul]
    norm_cast
  have hR2mu4 : S2Mu4ExactGrade h2 hq 171
      ((g8 h2 hq : Polynomial O) * (s2DepthTwoKeyAt h2 hq 2 *
        (Polynomial.C (2 : O) * Polynomial.X * (s2Frame h2 hq).key))) := by
    have h := S2Mu4ExactGrade_mul h2 hq (tooth_g8 h2 hq) hR1mu4
    exact h
  have hΛeq : s2Mu5Lambda h2 hq =
      (g8 h2 hq : Polynomial O) * (s2DepthTwoKeyAt h2 hq 2 *
        (Polynomial.C (2 : O) * Polynomial.X * (s2Frame h2 hq).key)) := by
    rw [s2Mu5Lambda, hkey1, hkey2, hkey3]; ring
  rw [hΛeq]; exact hR2mu4

/-- ★★ **D4-10 — `chainNormBelow 4 171` (= `Λ`) has exact μ₅ grade `171`**, degree `15`,
nonzero (the last two ALREADY LANDED, `C136t.s2Mu5Lambda_natDegree`/`_ne_zero`); this row
supplies the exact-grade third. -/
theorem s2Mu5Lambda_exactGrade : S2Mu5ExactGrade h2 hq 171 (s2Mu5Lambda h2 hq) := by
  rw [S2Mu5ExactGrade_iff_dv4Supp,
    dv4Supp_eq_dv3Supp_of_natDegree_lt h2 hq (s2Mu5Lambda_natDegree_lt h2 hq)]
  exact (S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp (s2Mu5Lambda_mu4ExactGrade h2 hq)

/-! ## D4-11 — the literal `f' = 1, e' = 1` refinement recipe (the exact-evaluation genre)

Mirror of `C132rp9`'s `FGMNSourceLaws.normalized_recipe` field shape, but NON-vacuous:
contrast the `e' > 1` mirrors (`C132rp9`, `C136d2`'s D3-18), which are vacuous because no
low-degree polynomial can realize the printed ODD grade — at `e' = 1` EVERY grade is
realizable (`S2Mu5PrevGrade_all`), so this row is a genuine computation.  The key fact
(`s2Mu5_recipe_negTooth_gradedRes` below) needs ONLY the two abstract properties `S2Mu5ExactGrade
171 Λ'` and `Λ'.natDegree < 16` — NOT any algebraic structure of `Λ'` — which is exactly
why the theorem holds for an ARBITRARY `khat`, not merely the concrete `Λ` (D4-12 is then a
pure corollary, instantiating `Λ' := s2Mu5Lambda`). -/

/-- below twice the development key's degree, every μ₅ graded residual is constant
(private mirror of `C136d3.s2Mu4GradedRes_eq_C_of_natDegree_lt_sixteen`, one level up —
here the fence is `deg g16 = 16` itself, not `2 · deg g16`, since `e' = 1` needs no
doubling). -/
private theorem s2Mu5GradedRes_eq_C_of_natDegree_lt_sixteen {g : Polynomial O}
    (hdeg : g.natDegree < 16) (β : ℕ) :
    s2Mu5GradedRes h2 hq β g = Polynomial.C ((s2Mu5GradedRes h2 hq β g).coeff 0) := by
  refine Polynomial.ext fun t => ?_
  match t with
  | 0 => rw [Polynomial.coeff_C_zero]
  | t + 1 =>
    rw [Polynomial.coeff_C_of_ne_zero (Nat.succ_ne_zero t), s2Mu5GradedRes_coeff]
    refine s2Mu5Coeff_eq_zero_of_dv4Pin_top h2 hq ?_
    rw [dv4Pin, dev_eq_zero_of_lt (g16_monic h2 hq)
      (by rw [g16_natDegree h2 hq]; norm_num) g _
      (by rw [g16_natDegree h2 hq]; omega)]
    exact dv4Hgt_zero ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21
      (by norm_num) (g8 h2 hq) 85 (by norm_num)

/-- ★ **the generic negated-correction graded residual is `1`**, for ANY `Λ'` with exact
μ₅ grade `171` and degree below `16`. -/
theorem s2Mu5_recipe_negTooth_gradedRes {Λ' : Polynomial O}
    (hgrade : S2Mu5ExactGrade h2 hq 171 Λ') (hdeg : Λ'.natDegree < 16) :
    s2Mu5GradedRes h2 hq 171 (-Λ') = 1 := by
  have hdeg' : (-Λ').natDegree < 16 := by rw [Polynomial.natDegree_neg]; exact hdeg
  have hgrade' : S2Mu5ExactGrade h2 hq 171 (-Λ') := by
    show s2Hgt₅ h2 hq _ = _
    rw [s2Hgt₅_neg_local h2 hq]
    exact hgrade
  have hne : s2Mu5GradedRes h2 hq 171 (-Λ') ≠ 0 := s2Mu5GradedRes_ne_zero_of_exact h2 hq hgrade'
  have hcollapse := s2Mu5GradedRes_eq_C_of_natDegree_lt_sixteen h2 hq hdeg' 171
  have hc0 : (s2Mu5GradedRes h2 hq 171 (-Λ')).coeff 0 ≠ 0 :=
    fun h0 => hne (by rw [hcollapse, h0, Polynomial.C_0])
  rw [hcollapse, C132rp1.s2Fld₂_eq_one_of_ne_zero h2 hq hc0, Polynomial.C_1]

/-- ★★ **the generic recipe's exact μ₅ grade**: `keyAt4 − Λ'` has exact grade `171`, for
ANY `Λ'` with grade `171` and degree `< 16` (the two-sided bound, mirroring D3-14's
`g16_exactGrade` one level up). -/
theorem s2Mu5_recipe_exactGrade {Λ' : Polynomial O}
    (hgrade : S2Mu5ExactGrade h2 hq 171 Λ') (hdeg : Λ'.natDegree < 16) :
    S2Mu5ExactGrade h2 hq 171 ((g16 h2 hq : Polynomial O) - Λ') := by
  have hsub : (g16 h2 hq : Polynomial O) - Λ' = g16 h2 hq + -Λ' := by ring
  have hpow : S2Mu5ExactGrade h2 hq 171 (g16 h2 hq) := tooth_g16 h2 hq
  have hnegΛ' : S2Mu5ExactGrade h2 hq 171 (-Λ') := by
    show s2Hgt₅ h2 hq _ = _
    rw [s2Hgt₅_neg_local h2 hq]
    exact hgrade
  have hge : ((171 : ℤ) : WithTop ℤ) ≤ s2Hgt₅ h2 hq ((g16 h2 hq : Polynomial O) - Λ') := by
    have h := s2Hgt₅_add_ge h2 hq (g16 h2 hq) (-Λ')
    rw [← hsub] at h
    have hp : s2Hgt₅ h2 hq (g16 h2 hq) = ((171 : ℤ) : WithTop ℤ) := hpow
    have hn : s2Hgt₅ h2 hq (-Λ') = ((171 : ℤ) : WithTop ℤ) := hnegΛ'
    rw [hp, hn, min_self] at h
    exact h
  have hΛ'mu4 : S2Mu4ExactGrade h2 hq 171 Λ' :=
    s2Mu4ExactGrade_of_s2Mu5ExactGrade_natDegree_lt h2 hq hgrade hdeg
  have hdev0 : dev (g16 h2 hq) ((g16 h2 hq : Polynomial O) - Λ') 0 = -Λ' := by
    rw [hsub, dev_add_of_monic (g16_monic h2 hq), g16_dev0_local h2 hq, zero_add,
      dev_neg (g16_monic h2 hq)]
    congr 1
    exact (Polynomial.modByMonic_eq_self_iff (g16_monic h2 hq)).mpr
      (Polynomial.degree_lt_degree (by rw [g16_natDegree h2 hq]; exact hdeg))
  have hle : s2Hgt₅ h2 hq ((g16 h2 hq : Polynomial O) - Λ') ≤ ((171 : ℤ) : WithTop ℤ) := by
    rw [s2Hgt₅_eq_dv4Supp]
    have hslot : dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
        (g8 h2 hq) 85 2 (g16 h2 hq) ((g16 h2 hq : Polynomial O) - Λ') 171 1
        ≤ ((171 : ℕ) : ℕ∞) := by
      rw [dv4Supp]
      refine le_trans (Finset.inf_le (Finset.mem_range.mpr (Nat.succ_pos _))) ?_
      rw [dv4Pin, hdev0, dv4Hgt, dv3Supp_neg _ (s2Φ₂_monic h2 hq) 21 2 (s2g8_monic h2 hq),
        (S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp hΛ'mu4]
      norm_num
    calc toZ (dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
          (g8 h2 hq) 85 2 (g16 h2 hq) ((g16 h2 hq : Polynomial O) - Λ') 171 1)
        ≤ toZ ((171 : ℕ) : ℕ∞) := toZ_le_toZ_iff.mpr hslot
      _ = ((171 : ℤ) : WithTop ℤ) := by rw [toZ_coe]; norm_num
  show s2Hgt₅ h2 hq ((g16 h2 hq : Polynomial O) - Λ') = ((171 : ℕ) : WithTop ℤ)
  rw [show ((171 : ℕ) : WithTop ℤ) = ((171 : ℤ) : WithTop ℤ) by norm_num]
  exact le_antisymm hle hge

/-- ★★★ **D4-11 — the literal `f' = 1, e' = 1` refinement recipe** (the
`FGMNSourceLaws.normalized_recipe` field shape, published exact-evaluation genre): for ANY
correction `khat 0` of exact μ₅ grade `171` and degree below `deg(keyAt4) = 16`, the
recipe `keyAt4 − khat 0` has normalized μ₅ residual `X + 1`. -/
theorem s2Mu5_normalized_recipe (khat : ℕ → Polynomial O)
    (hkhat : ∀ t, t < 1 → S2Mu5ExactGrade h2 hq ((1 - t) * 171) (khat t))
    (hdeg : ∀ t, t < 1 → (khat t).natDegree <
      ((s2DepthFourKeyChain h2 hq).keyAt 4 : Polynomial O).natDegree) :
    s2Mu5NormRes h2 hq
        (((s2DepthFourKeyChain h2 hq).keyAt 4 : Polynomial O) ^ (1 * 1) -
          ∑ t ∈ Finset.range 1,
            khat t * ((s2DepthFourKeyChain h2 hq).keyAt 4 : Polynomial O) ^ (1 * t)) =
      Polynomial.X ^ 1 -
        ∑ t ∈ Finset.range 1,
          Polynomial.C ((s2Mu4GradedRes h2 hq ((1 - t) * 171) (khat t)).coeff 0) *
            Polynomial.X ^ t := by
  have hk0grade : S2Mu5ExactGrade h2 hq 171 (khat 0) := by
    have h := hkhat 0 (by omega); simpa using h
  have hk0deg : (khat 0).natDegree < 16 := by
    have h := hdeg 0 (by omega)
    rwa [s2DepthFourKeyChain_keyAt_four, g16_natDegree h2 hq] at h
  have hΛ'mu4 : S2Mu4ExactGrade h2 hq 171 (khat 0) :=
    s2Mu4ExactGrade_of_s2Mu5ExactGrade_natDegree_lt h2 hq hk0grade hk0deg
  have hcollapse := s2Mu4GradedRes_eq_C_of_natDegree_lt_sixteen h2 hq hk0deg 171
  have hne : s2Mu4GradedRes h2 hq 171 (khat 0) ≠ 0 :=
    s2Mu4GradedRes_ne_zero_of_exact h2 hq hΛ'mu4
  have hc0 : (s2Mu4GradedRes h2 hq 171 (khat 0)).coeff 0 ≠ 0 :=
    fun h0 => hne (by rw [hcollapse, h0, Polynomial.C_0])
  have hCeq1 : Polynomial.C ((s2Mu4GradedRes h2 hq 171 (khat 0)).coeff 0)
      = (1 : Polynomial ((s2DepthTwo h2 hq).fld 2)) := by
    rw [C132rp1.s2Fld₂_eq_one_of_ne_zero h2 hq hc0, Polynomial.C_1]
  simp only [Finset.sum_range_one, Nat.mul_zero, pow_zero, pow_one, mul_one]
  rw [s2DepthFourKeyChain_keyAt_four, hCeq1]
  rw [s2Mu5NormRes_of_exact h2 hq (s2Mu5_recipe_exactGrade h2 hq hk0grade hk0deg)]
  have hsub : (g16 h2 hq : Polynomial O) - khat 0 = g16 h2 hq + -(khat 0) := by ring
  have hpow : S2Mu5ExactGrade h2 hq 171 (g16 h2 hq) := tooth_g16 h2 hq
  have hnegk : S2Mu5ExactGrade h2 hq 171 (-(khat 0)) := by
    show s2Hgt₅ h2 hq _ = _
    rw [s2Hgt₅_neg_local h2 hq]
    exact hk0grade
  have hleaf' := s2Mu5_recipe_exactGrade h2 hq hk0grade hk0deg
  rw [hsub, s2Mu5GradedRes_add h2 hq hpow hnegk (hsub ▸ hleaf'), s2Mu5GradedRes_key h2 hq,
    s2Mu5_recipe_negTooth_gradedRes h2 hq hk0grade hk0deg]
  have htr : (Polynomial.X + 1 : Polynomial ((s2DepthTwo h2 hq).fld 2)).natTrailingDegree = 0 :=
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr (by simp))
  rw [htr, Function.iterate_zero_apply]
  have hneg1 : (-1 : Polynomial ((s2DepthTwo h2 hq).fld 2)) = 1 := by
    have h : (1 : Polynomial ((s2DepthTwo h2 hq).fld 2)) + 1 = 0 := by
      rw [← Polynomial.C_1, ← Polynomial.C_add, C130rp2.tooth_char_two h2 hq, Polynomial.C_0]
    linear_combination -h
  rw [sub_eq_add_neg, hneg1]

/-! ## D4-12 — the normalized existence leaf: `leaf := keyAt4 − Λ`, monic, degree 16,
residual `X + 1` (a pure corollary of D4-10's grade fact + D4-11's generic machinery,
instantiated at `Λ' := s2Mu5Lambda`). -/

/-- ★ **the leaf**: `keyAt4 − Λ`, the concrete `f' = e' = 1` normalized-existence
witness. -/
noncomputable def s2Mu5Leaf : Polynomial O := (g16 h2 hq : Polynomial O) - s2Mu5Lambda h2 hq

theorem s2Mu5Leaf_eq_keyAt_sub :
    s2Mu5Leaf h2 hq = (s2DepthFourKeyChain h2 hq).keyAt 4 - s2Mu5Lambda h2 hq := by
  rw [s2Mu5Leaf, s2DepthFourKeyChain_keyAt_four]

theorem s2Mu5Leaf_monic : (s2Mu5Leaf h2 hq).Monic := by
  unfold s2Mu5Leaf
  apply (g16_monic h2 hq).sub_of_left
  refine Polynomial.degree_lt_degree ?_
  rw [g16_natDegree h2 hq]
  exact s2Mu5Lambda_natDegree_lt h2 hq

theorem s2Mu5Leaf_natDegree : (s2Mu5Leaf h2 hq).natDegree = 16 := by
  unfold s2Mu5Leaf
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
  · exact g16_natDegree h2 hq
  · rw [g16_natDegree h2 hq]; exact s2Mu5Lambda_natDegree_lt h2 hq

theorem s2Mu5Leaf_ne_zero : s2Mu5Leaf h2 hq ≠ 0 := (s2Mu5Leaf_monic h2 hq).ne_zero

/-- ★★ **the leaf has exact μ₅ grade `171`** — D4-11's generic recipe-grade lemma,
instantiated at `Λ' := s2Mu5Lambda`. -/
theorem s2Mu5Leaf_exactGrade : S2Mu5ExactGrade h2 hq 171 (s2Mu5Leaf h2 hq) :=
  s2Mu5_recipe_exactGrade h2 hq (s2Mu5Lambda_exactGrade h2 hq) (s2Mu5Lambda_natDegree_lt h2 hq)

/-- ★★★ **the leaf's normalized μ₅ residual is `X + 1`**. -/
theorem s2Mu5NormRes_leaf : s2Mu5NormRes h2 hq (s2Mu5Leaf h2 hq) = Polynomial.X + 1 := by
  have hsub : s2Mu5Leaf h2 hq = g16 h2 hq + -(s2Mu5Lambda h2 hq) := by unfold s2Mu5Leaf; ring
  have hpow : S2Mu5ExactGrade h2 hq 171 (g16 h2 hq) := tooth_g16 h2 hq
  have hnegΛ : S2Mu5ExactGrade h2 hq 171 (-(s2Mu5Lambda h2 hq)) := by
    show s2Hgt₅ h2 hq _ = _
    rw [s2Hgt₅_neg_local h2 hq]
    exact s2Mu5Lambda_exactGrade h2 hq
  have hleaf := s2Mu5Leaf_exactGrade h2 hq
  rw [s2Mu5NormRes_of_exact h2 hq hleaf, hsub,
    s2Mu5GradedRes_add h2 hq hpow hnegΛ (hsub ▸ hleaf), s2Mu5GradedRes_key h2 hq,
    s2Mu5_recipe_negTooth_gradedRes h2 hq (s2Mu5Lambda_exactGrade h2 hq)
      (s2Mu5Lambda_natDegree_lt h2 hq)]
  have htr : (Polynomial.X + 1 : Polynomial ((s2DepthTwo h2 hq).fld 2)).natTrailingDegree = 0 :=
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr (by simp))
  rw [htr]
  rfl

end S2

end Uniformity.Density.Tower.C136e1

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C136e1.s2Mu5EpsExp
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5EpsOf
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5EpsOf_eq_one
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5Eps
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5Eps_eq_one
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5Eps_eq_epsOf
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5Eps_ne_zero
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5Coeff
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5Coeff_letter_display
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5Coeff_eq_eval
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5Coeff_eq_eval_normRes
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5Coeff_slot
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5Coeff_eq_zero_of_dv4Pin_top
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5Coeff_eq_zero_of_natDegree_lt
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5Coeff_eq_zero_of_grade_lt
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5Coeff_eq_zero_of_above
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5GradedRes
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5GradedRes_coeff
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5GradedRes_eq_sum_range
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5GradedRes_natDegree_le
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5GradedRes_coeff_eq_zero_of_natDegree_lt
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5GradedRes_zero_of_above
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5GradedRes_zero
#print axioms Uniformity.Density.Tower.C136e1.le_dv4Pin_of_le_dv4Supp
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5Coeff_eq_eval_of_le
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5Coeff_add
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5GradedRes_add_of_le
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5GradedRes_add
#print axioms Uniformity.Density.Tower.C136e1.exists_mu5SlotOnGrade_of_exact
#print axioms Uniformity.Density.Tower.C136e1.eval_one_mu4GradedRes_g16_mul
#print axioms Uniformity.Density.Tower.C136e1.eval_one_mu4GradedRes_modBy_g16
#print axioms Uniformity.Density.Tower.C136e1.eval_one_mu4GradedRes_mul_of_exact
#print axioms Uniformity.Density.Tower.C136e1.eval_one_mu4GradedRes_mul_of_le
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5Coeff_mul
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5GradedRes_mul_coeff
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5GradedRes_mul
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5_graded_mul
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5GradedRes_coeff_zero_ne_zero_of_exact
#print axioms Uniformity.Density.Tower.C136e1.tooth_mu5_scalar_fires
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5GradeOf
#print axioms Uniformity.Density.Tower.C136e1.S2Mu5ExactGrade_s2Mu5GradeOf
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5GradeOf_eq_of_exact
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5NormRes
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5NormRes_of_exact
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5NormRes_coeff
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5NormRes_zero
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5NormRes_mul_X_pow_of_exact
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5GradedRes_ne_zero_of_exact
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5NormRes_coeff_zero_ne_zero
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5NormRes_ne_zero
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5GradedRes_natTrailingDegree_mul
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5NormRes_mul_of_exact
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5NormRes_mul
#print axioms Uniformity.Density.Tower.C136e1.S2Mu5ExactGrade_one
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5GradedRes_one
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5NormRes_one
#print axioms Uniformity.Density.Tower.C136e1.S2Mu5ExactGrade_key_pow
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5GradedRes_key
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5GradedRes_key_pow
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5NormRes_key
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5NormRes_key_pow
#print axioms Uniformity.Density.Tower.C136e1.s2Mu4ExactGrade_of_s2Mu5ExactGrade_natDegree_lt
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5Lambda_mu4ExactGrade
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5Lambda_exactGrade
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5_recipe_negTooth_gradedRes
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5_recipe_exactGrade
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5_normalized_recipe
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5Leaf
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5Leaf_eq_keyAt_sub
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5Leaf_monic
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5Leaf_natDegree
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5Leaf_ne_zero
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5Leaf_exactGrade
#print axioms Uniformity.Density.Tower.C136e1.s2Mu5NormRes_leaf

end AxCheck
