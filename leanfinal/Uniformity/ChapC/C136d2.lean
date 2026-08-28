/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C136l2e4
import Uniformity.ChapC.C136t
import Uniformity.ChapC.C132rp7

/-!
# Uniformity.ChapC.C136d2 — the μ₄ operator stack's upper-middle tranche: D3-11..D3-14 [D3C 2026-08-28]

**Unit D3C** of the deep-witness campaign
(`docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md` §6.2, rows D3-11 through D3-14).
Chains onto D3-10's just-landed μ₄ coefficient convolution `s2Mu4Coeff_mul`
(`C136l2e4`), on top of `C136d1`'s D3-05..09 bank (`s2Mu4Coeff`, `s2Mu4GradedRes`, the
grade predicates, the carry arithmetic) and `C136t`'s T1/T2/T4 carriers (`g8`,
`s2DepthThreeKeyChain`, `s2Mu4_chainNormBelow_three_eighty_five`).

Every declaration below is the one-level-up mirror of the landed μ₃ campaign's
`C132rp6`/`C132rp7` (D3-11), `C132rp8` (D3-12), `C132rp9`/`C132sg3` (D3-13, the exact-grade
half T4 deferred), and `C132rp10`/`C132rp10b` (D3-14), with the inner key `g8` (level-3)
replacing `Φ₂` (level-2), the outer side `(u₄,ℓ₄) = (85,2)` replacing `(u₃,ℓ₃) = (21,2)`,
and the inner graded/normalized read `s2Mu3GradedRes`/`s2Mu3NormRes` (landed μ₃-level,
`C132rp2`/`C132rp8`) replacing `s2GradedRes`/`s2NormRes` (μ₂-level).

## What lands

* **D3-11 (graded product/scalar).** The gate witness `exists_mu4SlotOnGrade_of_exact`; the
  eval-1 collapse of the INNER μ₃-level operator `s2Mu3GradedRes` under the degree-`8` fence
  (the genuinely new content, one level up from `C132rp7`'s Part 2); the twisted/plain
  product laws `s2Mu4GradedRes_mul_of_exact`/`_of_prevGrade`; `S2Mu4PrevGrade := 2 ∣ β` and
  the packaged `s2Mu4_graded_mul`; the coefficient-zero nonvanishing
  `s2Mu4GradedRes_coeff_zero_ne_zero_of_exact`/`s2Mu4_graded_scalar_nonzero` below degree `8`,
  citing the LANDED μ₃-level nonvanishing (`C132rp7.s2Mu3GradedRes_coeff_zero_ne_zero_of_exact`)
  directly rather than re-deriving it — the "genuine transport" the campaign predicts.
* **D3-12 (normalized operator).** `s2Mu4GradeOf`/`s2Mu4NormRes` (strip the initial `X`
  power); the polynomial-level nonvanishing `s2Mu4GradedRes_ne_zero_of_exact` (via the
  development DIGIT's automatic degree bound, mirroring `C132rp8`'s own route rather than
  D3-11's g-itself-bounded route); the universal multiplication `s2Mu4NormRes_mul`; the key
  reads `s2Mu4NormRes_key`/`_key_pow` at `g8` itself.
* **D3-13 (recipe/B-1).** The exact μ₄ grade `170 = 2·85` of the T4 tooth
  `2⁸·Φ₂` — the ONE genuinely new computation T4 deferred — via the constant-doubling
  bridge `s2Hgt₃_C_two` (mu₂→mu₃ level, the same "single g8/Φ₂-slot" mechanism one level
  down) and the μ₃-level multiplicativity `S2Mu3ExactGrade_mul`; then the B-1 degree/nonzero/
  exact-grade supply bundle, generic over `I : FGMNCalculus (s2DepthThree h2 hq) 2 1 85` with
  `hkey`, mirroring `C132fd1`'s style (no concrete μ₄ calculus exists yet to mirror `C132sg3`).
* **D3-14 (normalized existence).** `g16 := g8² − 2⁸·Φ₂`, monic of degree `16`
  (`C132rp10`'s route, one level up); its exact μ₄ grade `170` (BOTH summands individually at
  grade `170`, `C132rp10b`'s STAGE B route); the graded/normalized residual `X + 1`
  (`C132rp10b`'s STAGE C route, needing the mu₃-level graded read of `−2⁸·Φ₂` collapsing to a
  nonzero constant — the mu₃ analogue of `s2GradedRes_corr`).

## What this unit does NOT claim (honesty scope)

No key predicates/divisibility (D3-15), no key criterion/irreducibility (D3-16), no
`FGMNSourceData`/`FGMNSourceLaws` record or `FGMNCalculus` instance (D3-18/19) — this unit's
"B-1 supply" and "normalized existence" theorems are stated generically (over an abstract
`I`/pointwise polynomial facts), never against a concrete μ₄ calculus, since none exists yet.
The `S2Mu4KeyPoly` predicate and its criterion are D3-15/16's job, not consumed here.

**DEPENDS.** `C136d1` (D3-05..09: `S2Mu4ExactGrade`/`AboveGrade`, `S2Mu4SlotOnGrade`,
`s2Mu4Coeff` + its eval/slot/zero laws, `s2Mu4GradedRes` + its coeff/zero laws,
`s2Mu4Carry`/`_parity`, `le_dv3Pin_of_le_dv3Supp`) · `C136l2e4` (D3-10: `s2Mu4Coeff_mul`) ·
`C136d0` (D3-00..02: `dv3Hgt`/`dv3Pin`/`dv3Supp` + bank, `s2Hgt₄` + its teeth, `s2g8_monic`/
`s2g8_natDegree`) · `C136t` (T1/T2/T4: `g8`, `s2DepthThreeKeyChain`,
`s2Mu4_chainNormBelow_three_eighty_five`, `s2Mu4_chainNormBelow_tooth_degree_lt_key`) ·
`C132rp7` (the μ₃-level nonvanishing `s2Mu3GradedRes_coeff_zero_ne_zero_of_exact`, cited
directly) · `C132rp5` (`dev_mul_conv_split_monic`, generic over any monic key) · `C132rp8`
(`s2Mu3NormRes`, `s2Mu3NormRes_mul_X_pow_of_exact`, `S2Mu3ExactGrade_one`,
`s2Mu3GradedRes_one`) · `C132rp0` (`S2Mu3ExactGrade_mul`) · `C130s6`
(`s2Hgt₂_C_two`, `s2Hgt₂_eq_dv2Hgt`) · `C132nv1` (`s2Hgt₃`, `s2Hgt₃_eq_dv2Supp`, `s2Φ₂_monic`,
`s2Φ₂_natDegree`) · `C132nv0` (the `dv2Supp` bank) · `C136d3ad` (`dv2Supp_mul_modByKey_eq`,
`dv2Supp_add_le_key_quot_add`, `s2_isMu3Key_g8`) · `C132nv4`/`C132nv6` (the μ₃-level `dv2Supp`
multiplicativity at side `(21,2)`, cited to build a private local copy per the corpus's
private-copy convention).

## Status

Sorry-free target for D3-11..13; D3-14 is the campaign's flagged hardest row (the exact
non-recipe evaluation genre) and may land partially, with any residual gap named explicitly.
Verdict: `runs/wave-c/verdict_D3C.md`.
-/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace Uniformity.Density.Tower.C136d2

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130rp0
open Uniformity.Density.Tower.C132nv0 Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C132nv5
open Uniformity.Density.Tower.C132rp0 Uniformity.Density.Tower.C132rp1
open Uniformity.Density.Tower.C132rp2 Uniformity.Density.Tower.C132rp8
open Uniformity.Density.Tower.C132rp10 Uniformity.Density.Tower.C132rp10b
open Uniformity.Density.Tower.C136d0 Uniformity.Density.Tower.C136d1
open Uniformity.Density.Tower.C136d3ad Uniformity.Density.Tower.C136l2e4
open Uniformity.Density.Tower.C136t
open Uniformity.Density.Tower.C80

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## D3-11 — graded product/scalar: gate witness, eval-1 collapse, product laws,
coefficient-zero nonvanishing below degree 8 -/

/-! ### Part 1 — the μ₄ gate witness (inf attainment) -/

theorem exists_mu4SlotOnGrade_of_exact {β : ℕ} {g : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) :
    ∃ s : ℕ, S2Mu4SlotOnGrade h2 hq β g s := by
  have hsupp : dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) g 85 2 = (β : ℕ∞) := (S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp hg
  rw [dv3Supp] at hsupp
  obtain ⟨j, -, hjeq⟩ :=
    Finset.exists_mem_eq_inf (Finset.range (g.natDegree + 1))
      Finset.nonempty_range_add_one
      (fun j => 2 • dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
        (g8 h2 hq) g j + ((85 : ℕ) : ℕ∞) * (j : ℕ∞))
  rw [hjeq] at hsupp
  refine ⟨j, ?_⟩
  unfold S2Mu4SlotOnGrade
  rw [← hsupp]
  congr 1

/-! ### Part 2 — the eval-1 collapse of the INNER μ₃-level operator under the degree-8 fence -/

private theorem s2Mu3GradedRes_coeff_eq_zero_of_pos {m t : ℕ} {A : Polynomial O}
    (hA : A.natDegree < 8) (ht : 0 < t) :
    (s2Mu3GradedRes h2 hq m A).coeff t = 0 := by
  rw [s2Mu3GradedRes_coeff]
  refine s2Mu3Coeff_eq_zero_of_dv2Pin_top h2 hq ?_
  rw [dv2Pin, dev_eq_zero_of_lt (s2Φ₂_monic h2 hq)
    (by rw [s2Φ₂_natDegree h2 hq]; norm_num) A _
    (by rw [s2Φ₂_natDegree h2 hq]; omega), dv2Hgt]
  exact dvSupp_zero_eq_top _ _ ((s2Tower h2 hq).levelDatum h2).hℓ

private theorem s2Mu3GradedRes_eq_C_coeff_zero {m : ℕ} {A : Polynomial O}
    (hA : A.natDegree < 8) :
    s2Mu3GradedRes h2 hq m A = Polynomial.C ((s2Mu3GradedRes h2 hq m A).coeff 0) := by
  refine Polynomial.ext fun t => ?_
  match t with
  | 0 => simp
  | (t + 1) =>
    rw [Polynomial.coeff_C, if_neg (Nat.succ_ne_zero t)]
    exact s2Mu3GradedRes_coeff_eq_zero_of_pos h2 hq hA (Nat.succ_pos t)

theorem eval_one_s2Mu3GradedRes_eq_coeff_zero {m : ℕ} {A : Polynomial O}
    (hA : A.natDegree < 8) :
    Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2) (s2Mu3GradedRes h2 hq m A)
      = (s2Mu3GradedRes h2 hq m A).coeff 0 := by
  conv_lhs => rw [s2Mu3GradedRes_eq_C_coeff_zero h2 hq hA]
  exact Polynomial.eval_C

/-! ### Part 3 — ★ NODE D3-11: coefficient-zero nonvanishing below degree 8 -/

theorem s2Mu4GradedRes_coeff_zero_ne_zero_of_exact {β : ℕ} {g : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) (hdeg : g.natDegree < 8) :
    (s2Mu4GradedRes h2 hq β g).coeff 0 ≠ 0 := by
  obtain ⟨s, hgate⟩ := exists_mu4SlotOnGrade_of_exact h2 hq hg
  have hs0 : s = 0 := by
    by_contra hs
    obtain ⟨m, hm, -⟩ := (s2Mu4SlotOnGrade_iff h2 hq).mp hgate
    have hdev : dev (g8 h2 hq) g s = 0 :=
      dev_eq_zero_of_lt (s2g8_monic h2 hq)
        (by rw [s2g8_natDegree h2 hq]; norm_num) g s
        (by rw [s2g8_natDegree h2 hq]; omega)
    have htop : dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
        (g8 h2 hq) g s = ⊤ := by
      rw [dv3Pin, hdev]
      exact dv3Hgt_zero _ _ _ (by norm_num)
    rw [htop] at hm
    exact WithTop.top_ne_coe hm
  subst hs0
  have hdevg : dev (g8 h2 hq) g 0 = g :=
    (Polynomial.modByMonic_eq_self_iff (s2g8_monic h2 hq)).mpr
      (Polynomial.degree_lt_degree (by rw [s2g8_natDegree h2 hq]; omega))
  have hinner : S2Mu3ExactGrade h2 hq (β / 2) g := by
    have h := s2Mu4SlotOnGrade_inner_exact h2 hq hgate
    rw [show (β - 85 * 0) / 2 = β / 2 by omega, hdevg] at h
    exact h
  have hslot := s2Mu4Coeff_slot h2 hq hgate
  rw [show (0 : ℕ) / 2 = 0 by norm_num] at hslot
  rw [show (β - 85 * 0) / 2 = β / 2 by omega, hdevg, s2Mu4Eps_eq_one, one_mul] at hslot
  rw [s2Mu4GradedRes_coeff, hslot, eval_one_s2Mu3GradedRes_eq_coeff_zero h2 hq hdeg]
  intro hc0
  have hzero : s2Mu3GradedRes h2 hq (β / 2) g = 0 := by
    rw [s2Mu3GradedRes_eq_C_coeff_zero h2 hq hdeg, hc0, Polynomial.C_0]
  exact C132rp8.s2Mu3GradedRes_ne_zero_of_exact h2 hq hinner hzero

theorem s2Mu4_graded_scalar_nonzero :
    ∀ β (g : Polynomial O),
      S2Mu4ExactGrade h2 hq β g →
      g.natDegree < ((s2DepthThreeKeyChain h2 hq).keyAt 3).natDegree →
      g ≠ 0 →
      (s2Mu4GradedRes h2 hq β g).coeff 0 ≠ 0 := by
  intro β g hg hdeg _
  have hkd : ((s2DepthThreeKeyChain h2 hq).keyAt 3).natDegree = 8 :=
    s2DepthThreeKeyAt_natDegree_three h2 hq
  rw [hkd] at hdeg
  exact s2Mu4GradedRes_coeff_zero_ne_zero_of_exact h2 hq hg hdeg

theorem tooth_mu4_scalar_fires :
    (s2Mu4GradedRes h2 hq 0 (1 : Polynomial O)).coeff 0 ≠ 0 := by
  refine s2Mu4GradedRes_coeff_zero_ne_zero_of_exact h2 hq ?_
    (by norm_num [Polynomial.natDegree_one])
  unfold S2Mu4ExactGrade
  rw [s2Hgt₄_one_eq_zero]
  norm_num

/-! ### Part 4 — the product laws (mirror of `C132rp6`) -/

private theorem natDegree_dev_g8_lt_local (f : Polynomial O) (j : ℕ) :
    (dev (g8 h2 hq) f j).natDegree < (g8 h2 hq).natDegree := by
  rcases eq_or_ne (dev (g8 h2 hq) f j) 0 with h0 | h0
  · rw [h0, Polynomial.natDegree_zero, s2g8_natDegree h2 hq]
    norm_num
  · exact Polynomial.natDegree_lt_natDegree h0
      (degree_dev_lt (s2g8_monic h2 hq)
        (by rw [s2g8_natDegree h2 hq]; norm_num) f j)

private theorem ceil_le_dv2Supp_dev_g8_local {β : ℕ} {f : Polynomial O} (j : ℕ)
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

private theorem coe_le_add_of_le_local {a b : ℕ} {x y : ℕ∞}
    (hx : (a : ℕ∞) ≤ x) (hy : (b : ℕ∞) ≤ y) : ((a + b : ℕ) : ℕ∞) ≤ x + y := by
  push_cast
  exact add_le_add hx hy

private theorem s2_dv2Supp_mul_local {g z : Polynomial O} (hg : g ≠ 0) (hz : z ≠ 0) :
    dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) (g * z) 21 2
      = dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2
        + dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) z 21 2 := by
  obtain ⟨Hg, hHg⟩ := C132nv2.exists_dv2SideMin_height ((s2Tower h2 hq).levelDatum h2) g 21 2
    (C132nv6.s2_dv2SideSet_nonempty_at_21 h2 hq hg)
  obtain ⟨Hz, hHz⟩ := C132nv2.exists_dv2SideMin_height ((s2Tower h2 hq).levelDatum h2) z 21 2
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

private theorem s2Mu4Coeff_mul_zero_of_odd {β β' : ℕ} {g z : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) (hz : S2Mu4ExactGrade h2 hq β' z)
    (hβ : β % 2 = 1) (hβ' : β' % 2 = 1) :
    s2Mu4Coeff h2 hq (β + β') (g * z) 0 = 0 := by
  have hsgz : dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) (g * z) 85 2 = ((β + β' : ℕ) : ℕ∞) :=
    (S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp (S2Mu4ExactGrade_mul h2 hq hg hz)
  have hm : 2 * ((β + β') / 2) + 85 * ((β + β') % 2 + 2 * 0) = β + β' := by omega
  have hpinsum := le_dv3Pin_of_le_dv3Supp h2 hq (by norm_num) (le_of_eq hsgz.symm) hm
  rw [s2Mu4Coeff_eq_eval_of_le h2 hq hm hpinsum,
    show (β + β') % 2 + 2 * 0 = 0 from by omega,
    C132rp5.dev_mul_conv_split_monic (s2g8_monic h2 hq)
      (by rw [s2g8_natDegree h2 hq]; norm_num) g z 0,
    Finset.range_one, Finset.sum_singleton, Finset.range_zero, Finset.sum_empty, add_zero,
    show (0 : ℕ) - 0 = 0 from rfl]
  have hsg : dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) g 85 2 = (β : ℕ∞) := (S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp hg
  have hsz : dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) z 85 2 = (β' : ℕ∞) := (S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp hz
  let hmul : ∀ ⦃a b : Polynomial O⦄, a ≠ 0 → b ≠ 0 →
      dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) (a * b) 21 2
        = dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) a 21 2
          + dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) b 21 2 :=
    fun _ _ ha hb => s2_dv2Supp_mul_local h2 hq ha hb
  have habove : (((β + β') / 2 : ℕ) : ℕ∞) < dv2Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2)
      ((dev (g8 h2 hq) g 0 * dev (g8 h2 hq) z 0) %ₘ g8 h2 hq) 21 2 := by
    rw [C136d3ad.dv2Supp_mul_modByKey_eq ((s2Tower h2 hq).levelDatum h2)
      (s2Φ₂_monic h2 hq) (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num)
      hmul (s2_isMu3Key_g8 h2 hq) (natDegree_dev_g8_lt_local h2 hq g 0)
      (natDegree_dev_g8_lt_local h2 hq z 0)]
    refine lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self ((β + β') / 2))) ?_
    refine le_trans (Nat.cast_le.mpr (show (β + β') / 2 + 1 ≤
        (β - 85 * 0 + 1) / 2 + (β' - 85 * 0 + 1) / 2 from by omega)) ?_
    exact coe_le_add_of_le_local
      (ceil_le_dv2Supp_dev_g8_local h2 hq 0 (le_of_eq hsg.symm))
      (ceil_le_dv2Supp_dev_g8_local h2 hq 0 (le_of_eq hsz.symm))
  rw [s2Mu3GradedRes_zero_of_above h2 hq ((S2Mu3AboveGrade_iff_dv2Supp h2 hq).mpr habove),
    Polynomial.eval_zero]

theorem s2Mu4GradedRes_mul_coeff {β β' : ℕ} {g z : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) (hz : S2Mu4ExactGrade h2 hq β' z) (T : ℕ) :
    (s2Mu4GradedRes h2 hq (β + β') (g * z)).coeff (T + s2Mu4Carry β β')
      = (s2Mu4GradedRes h2 hq β g * s2Mu4GradedRes h2 hq β' z).coeff T := by
  rw [s2Mu4GradedRes_coeff, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, s2Mu4Coeff_mul h2 hq hg hz T]
  exact Finset.sum_congr rfl fun t _ => by
    rw [s2Mu4GradedRes_coeff, s2Mu4GradedRes_coeff]

theorem s2Mu4GradedRes_mul_coeff_zero_of_odd {β β' : ℕ} {g z : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) (hz : S2Mu4ExactGrade h2 hq β' z)
    (hβ : β % 2 = 1) (hβ' : β' % 2 = 1) :
    (s2Mu4GradedRes h2 hq (β + β') (g * z)).coeff 0 = 0 := by
  rw [s2Mu4GradedRes_coeff]
  exact s2Mu4Coeff_mul_zero_of_odd h2 hq hg hz hβ hβ'

theorem s2Mu4GradedRes_mul_coeff_of_prevGrade {β β' : ℕ} {g z : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) (hz : S2Mu4ExactGrade h2 hq β' z)
    (hβ' : β' % 2 = 0) (T : ℕ) :
    (s2Mu4GradedRes h2 hq (β + β') (g * z)).coeff T
      = (s2Mu4GradedRes h2 hq β g * s2Mu4GradedRes h2 hq β' z).coeff T := by
  have h := s2Mu4GradedRes_mul_coeff h2 hq hg hz T
  rwa [show s2Mu4Carry β β' = 0 by unfold s2Mu4Carry; rw [hβ']; ring, Nat.add_zero] at h

theorem s2Mu4GradedRes_mul_of_exact {β β' : ℕ} {g z : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) (hz : S2Mu4ExactGrade h2 hq β' z) :
    s2Mu4GradedRes h2 hq (β + β') (g * z)
      = Polynomial.X ^ (β % 2 * (β' % 2))
        * (s2Mu4GradedRes h2 hq β g * s2Mu4GradedRes h2 hq β' z) := by
  rcases Nat.mod_two_eq_zero_or_one β with hpb | hpb
  · refine Polynomial.ext fun T => ?_
    rw [hpb, zero_mul, pow_zero, one_mul]
    have h := s2Mu4GradedRes_mul_coeff h2 hq hg hz T
    simp [s2Mu4Carry, hpb] at h
    exact h
  · rcases Nat.mod_two_eq_zero_or_one β' with hpb' | hpb'
    · refine Polynomial.ext fun T => ?_
      rw [hpb, hpb', mul_zero, pow_zero, one_mul]
      have h := s2Mu4GradedRes_mul_coeff h2 hq hg hz T
      simp [s2Mu4Carry, hpb'] at h
      exact h
    · refine Polynomial.ext fun T => ?_
      rw [hpb, hpb', mul_one, pow_one]
      match T with
      | 0 =>
        rw [Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul]
        exact s2Mu4GradedRes_mul_coeff_zero_of_odd h2 hq hg hz hpb hpb'
      | T + 1 =>
        rw [Polynomial.coeff_X_mul]
        have h := s2Mu4GradedRes_mul_coeff h2 hq hg hz T
        simp [s2Mu4Carry, hpb, hpb'] at h
        exact h

theorem s2Mu4GradedRes_mul_of_prevGrade {β β' : ℕ} {g z : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) (hz : S2Mu4ExactGrade h2 hq β' z)
    (hβ' : β' % 2 = 0) :
    s2Mu4GradedRes h2 hq (β + β') (g * z)
      = s2Mu4GradedRes h2 hq β g * s2Mu4GradedRes h2 hq β' z := by
  refine Polynomial.ext fun T => ?_
  exact s2Mu4GradedRes_mul_coeff_of_prevGrade h2 hq hg hz hβ' T

/-- The μ₄ preceding-group predicate. -/
def S2Mu4PrevGrade (β : ℕ) : Prop := 2 ∣ β

theorem S2Mu4PrevGrade_iff_mod (β : ℕ) : S2Mu4PrevGrade β ↔ β % 2 = 0 := by
  unfold S2Mu4PrevGrade
  omega

theorem s2Mu4_graded_mul :
    ∀ β β' (g z : Polynomial O),
      S2Mu4ExactGrade h2 hq β g → S2Mu4ExactGrade h2 hq β' z →
      S2Mu4PrevGrade β' →
        S2Mu4ExactGrade h2 hq (β + β') (g * z) ∧
        s2Mu4GradedRes h2 hq (β + β') (g * z)
          = s2Mu4GradedRes h2 hq β g * s2Mu4GradedRes h2 hq β' z :=
  fun _ β' _ _ hg hz hprev =>
    ⟨S2Mu4ExactGrade_mul h2 hq hg hz,
      s2Mu4GradedRes_mul_of_prevGrade h2 hq hg hz
        ((S2Mu4PrevGrade_iff_mod β').mp hprev)⟩

/-! ## D3-12 — the normalized μ₄ operator (mirror of `C132rp8`) -/

noncomputable def s2Mu4GradeOf (g : Polynomial O) : ℕ :=
  (dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) g 85 2).toNat

theorem S2Mu4ExactGrade_s2Mu4GradeOf {g : Polynomial O} (hg : g ≠ 0) :
    S2Mu4ExactGrade h2 hq (s2Mu4GradeOf h2 hq g) g :=
  (S2Mu4ExactGrade_iff_dv3Supp h2 hq).mpr
    (ENat.coe_toNat
      (dv3Supp_ne_top_of_ne_zero ((s2Tower h2 hq).levelDatum h2) (s2Φ₂_monic h2 hq)
        (by rw [s2Φ₂_natDegree h2 hq]; norm_num) 21 2 (s2g8_monic h2 hq)
        (by rw [s2g8_natDegree h2 hq]; norm_num) 85 2 hg)).symm

theorem s2Mu4GradeOf_eq_of_exact {β : ℕ} {g : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) : s2Mu4GradeOf h2 hq g = β := by
  unfold s2Mu4GradeOf
  rw [(S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp hg]
  exact ENat.toNat_coe β

noncomputable def s2Mu4NormRes (g : Polynomial O) :
    Polynomial ((s2DepthTwo h2 hq).fld 2) :=
  Polynomial.divX^[(s2Mu4GradedRes h2 hq (s2Mu4GradeOf h2 hq g) g).natTrailingDegree]
    (s2Mu4GradedRes h2 hq (s2Mu4GradeOf h2 hq g) g)

theorem s2Mu4NormRes_of_exact {β : ℕ} {g : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) :
    s2Mu4NormRes h2 hq g =
      Polynomial.divX^[(s2Mu4GradedRes h2 hq β g).natTrailingDegree]
        (s2Mu4GradedRes h2 hq β g) := by
  unfold s2Mu4NormRes
  rw [s2Mu4GradeOf_eq_of_exact h2 hq hg]

theorem s2Mu4NormRes_coeff (g : Polynomial O) (t : ℕ) :
    (s2Mu4NormRes h2 hq g).coeff t =
      (s2Mu4GradedRes h2 hq (s2Mu4GradeOf h2 hq g) g).coeff
        (t + (s2Mu4GradedRes h2 hq (s2Mu4GradeOf h2 hq g) g).natTrailingDegree) := by
  unfold s2Mu4NormRes
  exact C130rp8.coeff_divX_iterate _ _ _

theorem s2Mu4NormRes_zero : s2Mu4NormRes h2 hq (0 : Polynomial O) = 0 := by
  unfold s2Mu4NormRes
  rw [s2Mu4GradedRes_zero h2 hq]
  simp

theorem s2Mu4NormRes_mul_X_pow_of_exact {β : ℕ} {g : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) :
    s2Mu4NormRes h2 hq g * Polynomial.X ^ (s2Mu4GradedRes h2 hq β g).natTrailingDegree
      = s2Mu4GradedRes h2 hq β g := by
  rw [s2Mu4NormRes_of_exact h2 hq hg]
  exact C130rp8.divX_iterate_mul_X_pow le_rfl

theorem s2Mu4GradedRes_ne_zero_of_exact {β : ℕ} {g : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) : s2Mu4GradedRes h2 hq β g ≠ 0 := by
  obtain ⟨s, hgate⟩ := exists_mu4SlotOnGrade_of_exact h2 hq hg
  set A := dev (g8 h2 hq) g s with hAdef
  have hinner : S2Mu3ExactGrade h2 hq ((β - 85 * s) / 2) A :=
    s2Mu4SlotOnGrade_inner_exact h2 hq hgate
  have hdeg : A.natDegree < 8 := by
    rcases eq_or_ne A 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]
      norm_num
    · have h := Polynomial.natDegree_lt_natDegree h0
        (degree_dev_lt (s2g8_monic h2 hq)
          (by rw [s2g8_natDegree h2 hq]; norm_num) g s)
      rwa [s2g8_natDegree h2 hq] at h
  have hcoeff := s2Mu4Coeff_slot h2 hq hgate
  rw [s2Mu4Eps_eq_one, one_mul, eval_one_s2Mu3GradedRes_eq_coeff_zero h2 hq hdeg] at hcoeff
  have hne : (s2Mu3GradedRes h2 hq ((β - 85 * s) / 2) A).coeff 0 ≠ 0 := by
    intro hc0
    have hzero : s2Mu3GradedRes h2 hq ((β - 85 * s) / 2) A = 0 := by
      rw [s2Mu3GradedRes_eq_C_coeff_zero h2 hq hdeg, hc0, Polynomial.C_0]
    exact C132rp8.s2Mu3GradedRes_ne_zero_of_exact h2 hq hinner hzero
  intro hzero
  apply hne
  rw [← hcoeff, ← s2Mu4GradedRes_coeff, hzero, Polynomial.coeff_zero]

theorem s2Mu4NormRes_coeff_zero_ne_zero {g : Polynomial O} (hg : g ≠ 0) :
    (s2Mu4NormRes h2 hq g).coeff 0 ≠ 0 := by
  have hne : s2Mu4GradedRes h2 hq (s2Mu4GradeOf h2 hq g) g ≠ 0 :=
    s2Mu4GradedRes_ne_zero_of_exact h2 hq (S2Mu4ExactGrade_s2Mu4GradeOf h2 hq hg)
  rw [s2Mu4NormRes_coeff, zero_add]
  exact fun h0 => hne (Polynomial.coeff_natTrailingDegree_eq_zero.mp h0)

theorem s2Mu4NormRes_ne_zero {g : Polynomial O} (hg : g ≠ 0) :
    s2Mu4NormRes h2 hq g ≠ 0 :=
  fun h0 => s2Mu4NormRes_coeff_zero_ne_zero h2 hq hg (by rw [h0, Polynomial.coeff_zero])

theorem s2Mu4GradedRes_natTrailingDegree_mul {β β' : ℕ} {g z : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) (hz : S2Mu4ExactGrade h2 hq β' z) :
    (s2Mu4GradedRes h2 hq (β + β') (g * z)).natTrailingDegree =
      (s2Mu4GradedRes h2 hq β g).natTrailingDegree +
        (s2Mu4GradedRes h2 hq β' z).natTrailingDegree + β % 2 * (β' % 2) := by
  have hgne : s2Mu4GradedRes h2 hq β g ≠ 0 :=
    s2Mu4GradedRes_ne_zero_of_exact h2 hq hg
  have hzne : s2Mu4GradedRes h2 hq β' z ≠ 0 :=
    s2Mu4GradedRes_ne_zero_of_exact h2 hq hz
  rw [s2Mu4GradedRes_mul_of_exact h2 hq hg hz,
    Polynomial.natTrailingDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero)
      (mul_ne_zero hgne hzne),
    Polynomial.natTrailingDegree_mul hgne hzne, Polynomial.natTrailingDegree_X_pow]
  omega

theorem s2Mu4NormRes_mul_of_exact {β β' : ℕ} {g z : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) (hz : S2Mu4ExactGrade h2 hq β' z) :
    s2Mu4NormRes h2 hq (g * z) = s2Mu4NormRes h2 hq g * s2Mu4NormRes h2 hq z := by
  have hgz := S2Mu4ExactGrade_mul h2 hq hg hz
  have hntd := s2Mu4GradedRes_natTrailingDegree_mul h2 hq hg hz
  refine mul_right_cancel₀
    (pow_ne_zero ((s2Mu4GradedRes h2 hq (β + β') (g * z)).natTrailingDegree)
      Polynomial.X_ne_zero) ?_
  calc
    s2Mu4NormRes h2 hq (g * z) *
          Polynomial.X ^ (s2Mu4GradedRes h2 hq (β + β') (g * z)).natTrailingDegree
        = s2Mu4GradedRes h2 hq (β + β') (g * z) :=
          s2Mu4NormRes_mul_X_pow_of_exact h2 hq hgz
    _ = Polynomial.X ^ (β % 2 * (β' % 2)) *
          (s2Mu4GradedRes h2 hq β g * s2Mu4GradedRes h2 hq β' z) :=
          s2Mu4GradedRes_mul_of_exact h2 hq hg hz
    _ = Polynomial.X ^ (β % 2 * (β' % 2)) *
          ((s2Mu4NormRes h2 hq g *
              Polynomial.X ^ (s2Mu4GradedRes h2 hq β g).natTrailingDegree) *
            (s2Mu4NormRes h2 hq z *
              Polynomial.X ^ (s2Mu4GradedRes h2 hq β' z).natTrailingDegree)) := by
          rw [s2Mu4NormRes_mul_X_pow_of_exact h2 hq hg,
            s2Mu4NormRes_mul_X_pow_of_exact h2 hq hz]
    _ = (s2Mu4NormRes h2 hq g * s2Mu4NormRes h2 hq z) *
          Polynomial.X ^ ((s2Mu4GradedRes h2 hq β g).natTrailingDegree +
            (s2Mu4GradedRes h2 hq β' z).natTrailingDegree + β % 2 * (β' % 2)) := by
          ring
    _ = (s2Mu4NormRes h2 hq g * s2Mu4NormRes h2 hq z) *
          Polynomial.X ^ (s2Mu4GradedRes h2 hq (β + β') (g * z)).natTrailingDegree := by
          rw [hntd]

theorem s2Mu4NormRes_mul (g z : Polynomial O) :
    s2Mu4NormRes h2 hq (g * z) = s2Mu4NormRes h2 hq g * s2Mu4NormRes h2 hq z := by
  rcases eq_or_ne g 0 with rfl | hgne
  · rw [zero_mul, s2Mu4NormRes_zero h2 hq, zero_mul]
  rcases eq_or_ne z 0 with rfl | hzne
  · rw [mul_zero, s2Mu4NormRes_zero h2 hq, mul_zero]
  exact s2Mu4NormRes_mul_of_exact h2 hq
    (S2Mu4ExactGrade_s2Mu4GradeOf h2 hq hgne)
    (S2Mu4ExactGrade_s2Mu4GradeOf h2 hq hzne)

theorem S2Mu4ExactGrade_one : S2Mu4ExactGrade h2 hq 0 (1 : Polynomial O) := by
  unfold S2Mu4ExactGrade
  rw [s2Hgt₄_one_eq_zero]
  norm_num

theorem s2Mu4GradedRes_one : s2Mu4GradedRes h2 hq 0 (1 : Polynomial O) = 1 := by
  refine Polynomial.ext fun t => ?_
  match t with
  | 0 =>
      rw [Polynomial.coeff_one_zero]
      exact C132rp1.s2Fld₂_eq_one_of_ne_zero h2 hq
        (s2Mu4GradedRes_coeff_zero_ne_zero_of_exact h2 hq
          (S2Mu4ExactGrade_one h2 hq) (by norm_num [Polynomial.natDegree_one]))
  | t + 1 =>
      rw [s2Mu4GradedRes_coeff, Polynomial.coeff_one]
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      exact s2Mu4Coeff_eq_zero_of_natDegree_lt h2 hq
        (by norm_num [Polynomial.natDegree_one])

theorem s2Mu4NormRes_one : s2Mu4NormRes h2 hq (1 : Polynomial O) = 1 := by
  rw [s2Mu4NormRes_of_exact h2 hq (S2Mu4ExactGrade_one h2 hq),
    s2Mu4GradedRes_one h2 hq, Polynomial.natTrailingDegree_one]
  rfl

theorem S2Mu4ExactGrade_key_pow (k : ℕ) :
    S2Mu4ExactGrade h2 hq (85 * k) ((g8 h2 hq : Polynomial O) ^ k) := by
  induction k with
  | zero =>
      rw [pow_zero, Nat.mul_zero]
      exact S2Mu4ExactGrade_one h2 hq
  | succ k ih =>
      rw [show 85 * (k + 1) = 85 * k + 85 by ring, pow_succ]
      exact S2Mu4ExactGrade_mul h2 hq ih (tooth_g8 h2 hq)

theorem s2Mu4GradedRes_key :
    s2Mu4GradedRes h2 hq 85 (g8 h2 hq : Polynomial O) = 1 := by
  have hd1 : dev (g8 h2 hq) (g8 h2 hq : Polynomial O) 1 = 1 := by
    have h := dev_mul_pow (s2g8_monic h2 hq) 1 (1 : Polynomial O) 0
    rw [Nat.add_zero, one_mul, pow_one] at h
    rw [h]
    exact (Polynomial.modByMonic_eq_self_iff (s2g8_monic h2 hq)).mpr
      (Polynomial.degree_lt_degree
        (by rw [Polynomial.natDegree_one, s2g8_natDegree h2 hq]; norm_num))
  have hgate : S2Mu4SlotOnGrade h2 hq 85 (g8 h2 hq) 1 := by
    refine (s2Mu4SlotOnGrade_iff h2 hq).mpr ⟨0, ?_, by norm_num⟩
    rw [dv3Pin, hd1, dv3Hgt]
    apply C130s6.toZ_inj
    rw [← s2Hgt₃_eq_dv2Supp h2 hq, s2Hgt₃_one_eq_zero h2 hq]
    rfl
  refine Polynomial.ext fun t => ?_
  match t with
  | 0 =>
      rw [s2Mu4GradedRes_coeff, Polynomial.coeff_one_zero]
      have hslot := s2Mu4Coeff_slot h2 hq hgate
      rw [hd1, s2Mu4Eps_eq_one, one_mul, C132rp8.s2Mu3GradedRes_one h2 hq, Polynomial.eval_one]
        at hslot
      exact hslot
  | t + 1 =>
      rw [s2Mu4GradedRes_coeff, Polynomial.coeff_one, if_neg (by omega)]
      refine s2Mu4Coeff_eq_zero_of_dv3Pin_top h2 hq ?_
      rw [dv3Pin, dev_eq_zero_of_lt (s2g8_monic h2 hq)
        (by rw [s2g8_natDegree h2 hq]; norm_num) (g8 h2 hq) _
        (by rw [s2g8_natDegree h2 hq]; omega)]
      exact dv3Hgt_zero _ _ _ (by norm_num)

theorem s2Mu4GradedRes_key_pow (k : ℕ) :
    s2Mu4GradedRes h2 hq (85 * k) ((g8 h2 hq : Polynomial O) ^ k) = Polynomial.X ^ (k / 2) := by
  induction k with
  | zero =>
      rw [pow_zero, Nat.mul_zero, s2Mu4GradedRes_one h2 hq]
      norm_num
  | succ k ih =>
      have h := s2Mu4GradedRes_mul_of_exact h2 hq (S2Mu4ExactGrade_key_pow h2 hq k)
        (tooth_g8 h2 hq)
      rw [ih, s2Mu4GradedRes_key h2 hq, mul_one, show (85 : ℕ) % 2 = 1 by norm_num,
        mul_one, show 85 * k % 2 = k % 2 by omega, ← pow_add] at h
      rw [show 85 * (k + 1) = 85 * k + 85 by ring, pow_succ, h]
      congr 1
      omega

theorem s2Mu4NormRes_key :
    s2Mu4NormRes h2 hq (g8 h2 hq : Polynomial O) = 1 := by
  rw [s2Mu4NormRes_of_exact h2 hq (tooth_g8 h2 hq), s2Mu4GradedRes_key h2 hq,
    Polynomial.natTrailingDegree_one]
  rfl

theorem s2Mu4NormRes_key_pow (k : ℕ) :
    s2Mu4NormRes h2 hq ((g8 h2 hq : Polynomial O) ^ k) = 1 := by
  induction k with
  | zero => rw [pow_zero, s2Mu4NormRes_one h2 hq]
  | succ k ih =>
      rw [pow_succ, s2Mu4NormRes_mul h2 hq, ih, s2Mu4NormRes_key h2 hq, mul_one]

/-! ## D3-13 — recipe/B-1: the exact μ₄ grade 170 of the T4 tooth, and the supply bundle -/

/-! ### Part 1 — the mu₂→mu₃ constant-doubling bridge -/

private theorem C_two_dev_zero :
    dev (s2DepthTwoKeyAt h2 hq 2) (Polynomial.C (2 : O)) 0 = Polynomial.C (2 : O) :=
  (Polynomial.modByMonic_eq_self_iff (s2Φ₂_monic h2 hq)).mpr
    (Polynomial.degree_lt_degree
      (by rw [Polynomial.natDegree_C, s2Φ₂_natDegree h2 hq]; norm_num))

private theorem dv2Hgt_C_two_eq :
    dv2Hgt ((s2Tower h2 hq).levelDatum h2) (Polynomial.C (2 : O)) = ((4 : ℕ) : ℕ∞) :=
  C130s6.toZ_inj (by
    rw [← C130s6.s2Hgt₂_eq_dv2Hgt h2 hq, C130np0.s2Hgt₂_C_two h2 hq, C130s6.toZ_coe]
    norm_cast)

/-- ★ **the mu₂→mu₃ constant-doubling bridge**: `s2Hgt₃ (C 2) = 8 = 2 · s2Hgt₂ (C 2)` — the
SAME "single `Φ₂`-slot" mechanism `C132rp10b.s2Hgt₃_corr` uses for `corr`, specialized to
the bare constant `2` (a genuinely new tooth: not previously landed, since the μ₃ campaign
never needed the mu₃-height of the bare constant `2`, only of `2⁴Φ′`). -/
theorem s2Hgt₃_C_two : s2Hgt₃ h2 hq (Polynomial.C (2 : O)) = ((8 : ℤ) : WithTop ℤ) := by
  have hval : dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2)
      (Polynomial.C (2 : O)) 21 2 = ((8 : ℕ) : ℕ∞) := by
    rw [dv2Supp, Polynomial.natDegree_C, show Finset.range (0 + 1) = {0} by decide,
      Finset.inf_singleton, dv2Pin, C_two_dev_zero h2 hq, dv2Hgt_C_two_eq h2 hq]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    norm_num
  rw [s2Hgt₃, hval, toZ_coe]
  norm_num

theorem S2Mu3ExactGrade_C_two : S2Mu3ExactGrade h2 hq 8 (Polynomial.C (2 : O)) := by
  show s2Hgt₃ h2 hq (Polynomial.C (2 : O)) = ((8 : ℕ) : WithTop ℤ)
  rw [s2Hgt₃_C_two h2 hq]
  norm_num

theorem S2Mu3ExactGrade_C_two_pow_eight :
    S2Mu3ExactGrade h2 hq 64 (Polynomial.C ((2 : O) ^ 8)) := by
  have h2' := S2Mu3ExactGrade_mul h2 hq (S2Mu3ExactGrade_C_two h2 hq) (S2Mu3ExactGrade_C_two h2 hq)
  rw [← Polynomial.C_mul] at h2'
  have h4 := S2Mu3ExactGrade_mul h2 hq h2' h2'
  rw [← Polynomial.C_mul] at h4
  have h8 := S2Mu3ExactGrade_mul h2 hq h4 h4
  rw [← Polynomial.C_mul] at h8
  norm_num at h8
  convert h8 using 3
  norm_num

/-! ### Part 2 — the tooth's exact μ₄ grade 170 -/

theorem s2Mu4_chainNormBelow_tooth_ne_zero :
    Polynomial.C ((2 : O) ^ 8) * (s2DepthThreeKeyChain h2 hq).keyAt 2 ≠ 0 := by
  apply mul_ne_zero
  · exact Polynomial.C_ne_zero.mpr (pow_ne_zero 8 h2.ne_zero)
  · exact ((s2DepthThreeKeyChain h2 hq).keyAt_monic 2 ⟨by omega, by omega⟩).ne_zero

/-- ★ **the mu₃→mu₄ "single g8-slot" bridge, general form**: for any `A` with
`A.natDegree < 8`, the outer μ₄ support collapses to twice the inner μ₃ support — the SAME
mechanism `C132rp10b.dv2Supp_corr`/`s2Hgt₃_corr` uses one level down, generalized off a bare
constant to an arbitrary short input (needed again by D3-14's `g16` grade computation). -/
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
    rw [hpin0]
    simp
  · refine Finset.le_inf fun j _ => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · rw [hpin0]
      simp
    · rw [hpinj j hj1, C118a.smul_top_pos (by norm_num), top_add]
      exact le_top

theorem s2Mu4_chainNormBelow_tooth_exactGrade :
    S2Mu4ExactGrade h2 hq 170
      (Polynomial.C ((2 : O) ^ 8) * (s2DepthThreeKeyChain h2 hq).keyAt 2) := by
  have hkey2 : (s2DepthThreeKeyChain h2 hq).keyAt 2 = s2DepthTwoKeyAt h2 hq 2 :=
    s2DepthThreeKeyAt_two h2 hq
  rw [hkey2]
  have hdeg8 : (Polynomial.C ((2 : O) ^ 8) * s2DepthTwoKeyAt h2 hq 2).natDegree < 8 := by
    rw [Polynomial.natDegree_C_mul (pow_ne_zero 8 h2.ne_zero), s2Φ₂_natDegree h2 hq]
    norm_num
  have hmu3 : S2Mu3ExactGrade h2 hq 85
      (Polynomial.C ((2 : O) ^ 8) * s2DepthTwoKeyAt h2 hq 2) := by
    have h := S2Mu3ExactGrade_mul h2 hq
      (S2Mu3ExactGrade_C_two_pow_eight h2 hq) (tooth_Φ₂ h2 hq)
    rwa [show (64 : ℕ) + 21 = 85 from by norm_num] at h
  have hsmul : (2 : ℕ) • ((85 : ℕ) : ℕ∞) = ((170 : ℕ) : ℕ∞) := by
    rw [nsmul_eq_mul]; norm_num
  show s2Hgt₄ h2 hq _ = ((170 : ℤ) : WithTop ℤ)
  rw [s2Hgt₄_eq_dv3Supp, dv3Supp_eq_two_smul_of_natDegree_lt h2 hq hdeg8,
    (S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp hmu3, hsmul, toZ_coe]
  norm_num

/-! ### Part 3 — the generic B-1 supply bundle (mirror of `C132fd1`, no concrete calculus) -/

theorem s2Mu4_chainNormBelow_exactGrade
    (I : FGMNCalculus (s2DepthThree h2 hq) 2 1 85)
    (hkey : I.keyAt = (s2DepthThreeKeyChain h2 hq).keyAt) :
    S2Mu4ExactGrade h2 hq 170 (I.chainNormBelow 3 85) := by
  rw [s2Mu4_chainNormBelow_three_eighty_five h2 hq I hkey]
  exact s2Mu4_chainNormBelow_tooth_exactGrade h2 hq

theorem s2Mu4_B1_degree_supply
    (I : FGMNCalculus (s2DepthThree h2 hq) 2 1 85)
    (hkey : I.keyAt = (s2DepthThreeKeyChain h2 hq).keyAt) :
    ∀ d, 0 < d → d ≤ 1 →
      (I.chainNormBelow 3 (d * 85)).natDegree < (I.keyAt 3).natDegree := by
  intro d hd hd1
  have hd' : d = 1 := by omega
  subst hd'
  rw [one_mul, s2Mu4_chainNormBelow_three_eighty_five h2 hq I hkey, hkey]
  exact s2Mu4_chainNormBelow_tooth_degree_lt_key h2 hq

theorem s2Mu4_B1_nonzero_supply
    (I : FGMNCalculus (s2DepthThree h2 hq) 2 1 85)
    (hkey : I.keyAt = (s2DepthThreeKeyChain h2 hq).keyAt) :
    ∀ d, 0 < d → d ≤ 1 → I.chainNormBelow 3 (d * 85) ≠ 0 := by
  intro d hd hd1
  have hd' : d = 1 := by omega
  subst hd'
  rw [one_mul, s2Mu4_chainNormBelow_three_eighty_five h2 hq I hkey]
  exact s2Mu4_chainNormBelow_tooth_ne_zero h2 hq

theorem s2Mu4_B1_exact_grade_supply
    (I : FGMNCalculus (s2DepthThree h2 hq) 2 1 85)
    (hkey : I.keyAt = (s2DepthThreeKeyChain h2 hq).keyAt) :
    ∀ d, 0 < d → d ≤ 1 →
      S2Mu4ExactGrade h2 hq (2 * (d * 85)) (I.chainNormBelow 3 (d * 85)) := by
  intro d hd hd1
  have hd' : d = 1 := by omega
  subst hd'
  rw [show 2 * (1 * 85) = 170 from by norm_num, one_mul,
    s2Mu4_chainNormBelow_three_eighty_five h2 hq I hkey]
  exact s2Mu4_chainNormBelow_tooth_exactGrade h2 hq

/-! ## D3-14 — normalized existence: `g16 := g8² − 2⁸·Φ₂`, monic degree 16, residual X+1 -/

noncomputable def g16 : Polynomial O :=
  (g8 h2 hq : Polynomial O) ^ 2 - Polynomial.C ((2 : O) ^ 8) * (s2DepthThreeKeyChain h2 hq).keyAt 2

theorem g16_monic : (g16 h2 hq : Polynomial O).Monic := by
  unfold g16
  have hpow : ((g8 h2 hq : Polynomial O) ^ 2).Monic := (s2g8_monic h2 hq).pow 2
  apply hpow.sub_of_left
  refine Polynomial.degree_lt_degree ?_
  rw [pow_two, Polynomial.natDegree_mul (s2g8_monic h2 hq).ne_zero (s2g8_monic h2 hq).ne_zero,
    s2g8_natDegree h2 hq, s2Mu4_chainNormBelow_tooth_natDegree h2 hq]
  norm_num

theorem g16_natDegree : (g16 h2 hq : Polynomial O).natDegree = 16 := by
  unfold g16
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
  · rw [pow_two, Polynomial.natDegree_mul (s2g8_monic h2 hq).ne_zero (s2g8_monic h2 hq).ne_zero,
      s2g8_natDegree h2 hq]
  · rw [pow_two, Polynomial.natDegree_mul (s2g8_monic h2 hq).ne_zero (s2g8_monic h2 hq).ne_zero,
      s2g8_natDegree h2 hq, s2Mu4_chainNormBelow_tooth_natDegree h2 hq]
    norm_num

private theorem s2Hgt₄_neg_local (f : Polynomial O) : s2Hgt₄ h2 hq (-f) = s2Hgt₄ h2 hq f := by
  rw [s2Hgt₄_eq_dv3Supp, s2Hgt₄_eq_dv3Supp,
    dv3Supp_neg _ (s2Φ₂_monic h2 hq) 21 2 (s2g8_monic h2 hq) f 85 2]

theorem g16_exactGrade : S2Mu4ExactGrade h2 hq 170 (g16 h2 hq) := by
  have hkey2 : (s2DepthThreeKeyChain h2 hq).keyAt 2 = s2DepthTwoKeyAt h2 hq 2 :=
    s2DepthThreeKeyAt_two h2 hq
  have hsub : g16 h2 hq = (g8 h2 hq : Polynomial O) ^ 2 +
      -(Polynomial.C ((2 : O) ^ 8) * (s2DepthThreeKeyChain h2 hq).keyAt 2) := by
    unfold g16; ring
  have hpow : s2Hgt₄ h2 hq ((g8 h2 hq : Polynomial O) ^ 2) = ((170 : ℤ) : WithTop ℤ) := by
    rw [pow_two, s2Hgt₄_mul_all h2 hq, s2Hgt₄_g8 h2 hq]
    norm_num
  have htooth : s2Hgt₄ h2 hq
      (Polynomial.C ((2 : O) ^ 8) * (s2DepthThreeKeyChain h2 hq).keyAt 2) =
      ((170 : ℤ) : WithTop ℤ) := s2Mu4_chainNormBelow_tooth_exactGrade h2 hq
  have hge : ((170 : ℤ) : WithTop ℤ) ≤ s2Hgt₄ h2 hq (g16 h2 hq) := by
    have h := s2Hgt₄_add_ge h2 hq ((g8 h2 hq : Polynomial O) ^ 2)
      (-(Polynomial.C ((2 : O) ^ 8) * (s2DepthThreeKeyChain h2 hq).keyAt 2))
    rw [← hsub, hpow, s2Hgt₄_neg_local h2 hq, htooth, min_self] at h
    exact h
  have hmu3tooth : S2Mu3ExactGrade h2 hq 85
      (Polynomial.C ((2 : O) ^ 8) * (s2DepthThreeKeyChain h2 hq).keyAt 2) := by
    rw [hkey2]
    have h := S2Mu3ExactGrade_mul h2 hq
      (S2Mu3ExactGrade_C_two_pow_eight h2 hq) (tooth_Φ₂ h2 hq)
    rwa [show (64 : ℕ) + 21 = 85 from by norm_num] at h
  have hdevpow : dev (g8 h2 hq) ((g8 h2 hq : Polynomial O) ^ 2) 0 = 0 := by
    rw [dev_pow_self (s2g8_monic h2 hq)
      (by rw [s2g8_natDegree h2 hq]; norm_num) 2 0, if_neg (by norm_num)]
  have hdevtooth : dev (g8 h2 hq)
      (Polynomial.C ((2 : O) ^ 8) * (s2DepthThreeKeyChain h2 hq).keyAt 2) 0
      = Polynomial.C ((2 : O) ^ 8) * (s2DepthThreeKeyChain h2 hq).keyAt 2 :=
    (Polynomial.modByMonic_eq_self_iff (s2g8_monic h2 hq)).mpr
      (Polynomial.degree_lt_degree (by
        rw [s2g8_natDegree h2 hq, s2Mu4_chainNormBelow_tooth_natDegree h2 hq]; norm_num))
  have hdev16 : dev (g8 h2 hq) (g16 h2 hq) 0 =
      -(Polynomial.C ((2 : O) ^ 8) * (s2DepthThreeKeyChain h2 hq).keyAt 2) := by
    rw [hsub, dev_add_of_monic (s2g8_monic h2 hq), hdevpow, zero_add,
      dev_neg (s2g8_monic h2 hq), hdevtooth]
  have hle : s2Hgt₄ h2 hq (g16 h2 hq) ≤ ((170 : ℤ) : WithTop ℤ) := by
    rw [s2Hgt₄_eq_dv3Supp]
    have hslot : dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
        (g8 h2 hq) (g16 h2 hq) 85 2 ≤ ((170 : ℕ) : ℕ∞) := by
      rw [dv3Supp]
      refine le_trans (Finset.inf_le (Finset.mem_range.mpr (Nat.succ_pos _))) ?_
      rw [dv3Pin, hdev16, dv3Hgt, dv2Supp_neg _ (s2Φ₂_monic h2 hq),
        (S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp hmu3tooth]
      simp only [nsmul_eq_mul, Nat.cast_ofNat]
      norm_num
    calc toZ (dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
          (g8 h2 hq) (g16 h2 hq) 85 2)
        ≤ toZ ((170 : ℕ) : ℕ∞) := toZ_le_toZ_iff.mpr hslot
      _ = ((170 : ℤ) : WithTop ℤ) := by rw [toZ_coe]; norm_num
  show s2Hgt₄ h2 hq (g16 h2 hq) = ((170 : ℕ) : WithTop ℤ)
  rw [show ((170 : ℕ) : WithTop ℤ) = ((170 : ℤ) : WithTop ℤ) by norm_num]
  exact le_antisymm hle hge

/-! ### Stage C — the graded/normalized residual of `g16` is `X + 1` -/

private theorem exactGrade_C_two_pow_eight_mu2 :
    S2ExactGrade h2 hq 32 (Polynomial.C ((2 : O) ^ 8)) := by
  have h := C130rp0.S2ExactGrade_mul h2 hq
    (C132rp10b.exactGrade_C_two_pow h2 hq) (C132rp10b.exactGrade_C_two_pow h2 hq)
  rw [← Polynomial.C_mul] at h
  have h16 : (2 : O) ^ 4 * 2 ^ 4 = 2 ^ 8 := by ring
  rw [h16] at h
  have h32 : (16 : ℕ) + 16 = 32 := by norm_num
  rwa [h32] at h

private theorem gradedRes_C_two_pow_eight_eq_C_mu2 :
    C130rp1.s2GradedRes h2 hq 32 (Polynomial.C ((2 : O) ^ 8))
      = Polynomial.C ((C130rp1.s2GradedRes h2 hq 32 (Polynomial.C ((2 : O) ^ 8))).coeff 0) := by
  refine (Polynomial.eq_C_of_natDegree_le_zero ?_).trans rfl
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
  refine C130rp1.s2GradedRes_coeff_eq_zero_of_natDegree_lt h2 hq _ ?_
  rw [Polynomial.natDegree_C]
  omega

private theorem s2GradedRes_C_two_pow_eight_mu2 :
    C130rp1.s2GradedRes h2 hq 32 (Polynomial.C ((2 : O) ^ 8)) = 1 := by
  have hc0 : (C130rp1.s2GradedRes h2 hq 32 (Polynomial.C ((2 : O) ^ 8))).coeff 0 ≠ 0 :=
    C130rp8.s2GradedRes_coeff_zero_ne_zero_of_exact h2 hq
      (exactGrade_C_two_pow_eight_mu2 h2 hq) (by rw [Polynomial.natDegree_C]; norm_num)
  rw [gradedRes_C_two_pow_eight_eq_C_mu2 h2 hq, C132rp1.s2Fld₂_eq_one_of_ne_zero h2 hq hc0]
  rfl

private theorem s2GradedRes_neg_C_two_pow_eight_mu2 :
    C130rp1.s2GradedRes h2 hq 32 (-(Polynomial.C ((2 : O) ^ 8))) = 1 := by
  have hle : (32 : ℕ∞) ≤ dvSupp (s2Frame h2 hq) (Polynomial.C ((2 : O) ^ 8)) 5 2 :=
    le_of_eq ((S2ExactGrade_iff_dvSupp h2 hq).mp (exactGrade_C_two_pow_eight_mu2 h2 hq)).symm
  have hne1 : (-1 : (s2DepthTwo h2 hq).fld 2) ≠ 0 := fun h => one_ne_zero (neg_eq_zero.mp h)
  rw [C130kp0.s2GradedRes_neg_of_le h2 hq hle, s2GradedRes_C_two_pow_eight_mu2 h2 hq,
    ← Polynomial.C_1, ← map_neg, C132rp1.s2Fld₂_eq_one_of_ne_zero h2 hq hne1]

private theorem tooth_div_eq_mu3 :
    (Polynomial.C ((2 : O) ^ 8) * s2DepthTwoKeyAt h2 hq 2) /ₘ s2DepthTwoKeyAt h2 hq 2
      = Polynomial.C ((2 : O) ^ 8) := by
  have hrec := Polynomial.modByMonic_add_div
    (Polynomial.C ((2 : O) ^ 8) * s2DepthTwoKeyAt h2 hq 2) (s2DepthTwoKeyAt h2 hq 2)
  rw [show (Polynomial.C ((2 : O) ^ 8) * s2DepthTwoKeyAt h2 hq 2) %ₘ s2DepthTwoKeyAt h2 hq 2 = 0
      from (Polynomial.modByMonic_eq_zero_iff_dvd (s2Φ₂_monic h2 hq)).mpr
        ⟨Polynomial.C ((2 : O) ^ 8), by ring⟩, zero_add] at hrec
  have heq : s2DepthTwoKeyAt h2 hq 2 *
      ((Polynomial.C ((2 : O) ^ 8) * s2DepthTwoKeyAt h2 hq 2) /ₘ s2DepthTwoKeyAt h2 hq 2)
      = s2DepthTwoKeyAt h2 hq 2 * Polynomial.C ((2 : O) ^ 8) := by
    rw [hrec]; ring
  exact mul_left_cancel₀ (s2Φ₂_monic h2 hq).ne_zero heq

private theorem tooth_dev_one_mu3 :
    dev (s2DepthTwoKeyAt h2 hq 2)
      (Polynomial.C ((2 : O) ^ 8) * s2DepthTwoKeyAt h2 hq 2) 1 = Polynomial.C ((2 : O) ^ 8) := by
  show ((Polynomial.C ((2 : O) ^ 8) * s2DepthTwoKeyAt h2 hq 2) /ₘ s2DepthTwoKeyAt h2 hq 2)
      %ₘ s2DepthTwoKeyAt h2 hq 2 = Polynomial.C ((2 : O) ^ 8)
  rw [tooth_div_eq_mu3 h2 hq]
  exact (Polynomial.modByMonic_eq_self_iff (s2Φ₂_monic h2 hq)).mpr
    (Polynomial.degree_lt_degree (by rw [Polynomial.natDegree_C, s2Φ₂_natDegree h2 hq]; norm_num))

private theorem neg_tooth_pin_one :
    dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2)
      (-(Polynomial.C ((2 : O) ^ 8) * s2DepthTwoKeyAt h2 hq 2)) 1 = ((32 : ℕ) : ℕ∞) := by
  rw [dv2Pin, dev_neg (s2Φ₂_monic h2 hq), tooth_dev_one_mu3 h2 hq, dv2Hgt, dvSupp_neg]
  exact (S2ExactGrade_iff_dvSupp h2 hq).mp (exactGrade_C_two_pow_eight_mu2 h2 hq)

private theorem s2Mu3GradedRes_neg_tooth_coeff_zero :
    (s2Mu3GradedRes h2 hq 85
      (-(Polynomial.C ((2 : O) ^ 8) * s2DepthTwoKeyAt h2 hq 2))).coeff 0 = 1 := by
  have hgate : S2Mu3SlotOnGrade h2 hq 85
      (-(Polynomial.C ((2 : O) ^ 8) * s2DepthTwoKeyAt h2 hq 2)) 1 := by
    refine (s2Mu3SlotOnGrade_iff h2 hq).mpr ⟨32, ?_, by norm_num⟩
    exact neg_tooth_pin_one h2 hq
  have hslot := s2Mu3Coeff_slot h2 hq hgate
  rw [show (1 : ℕ) / 2 = 0 by norm_num, show (85 - 21 * 1) / 2 = 32 by norm_num] at hslot
  rw [s2Mu3GradedRes_coeff, hslot, s2Mu3Eps_eq_one, one_mul,
    dev_neg (s2Φ₂_monic h2 hq), tooth_dev_one_mu3 h2 hq,
    s2GradedRes_neg_C_two_pow_eight_mu2 h2 hq, Polynomial.eval_one]

private theorem s2Mu3GradedRes_neg_tooth_eq_one :
    s2Mu3GradedRes h2 hq 85
      (-(Polynomial.C ((2 : O) ^ 8) * s2DepthTwoKeyAt h2 hq 2)) = 1 := by
  refine Polynomial.ext fun t => ?_
  match t with
  | 0 =>
      rw [s2Mu3GradedRes_neg_tooth_coeff_zero h2 hq, Polynomial.coeff_one_zero]
  | t + 1 =>
      rw [s2Mu3GradedRes_coeff, Polynomial.coeff_one, if_neg (by omega)]
      refine s2Mu3Coeff_eq_zero_of_dv2Pin_top h2 hq ?_
      rw [dv2Pin, dev_neg (s2Φ₂_monic h2 hq)]
      have hdev0 : dev (s2DepthTwoKeyAt h2 hq 2)
          (Polynomial.C ((2 : O) ^ 8) * s2DepthTwoKeyAt h2 hq 2) (85 % 2 + 2 * (t + 1)) = 0 := by
        refine dev_eq_zero_of_lt (s2Φ₂_monic h2 hq)
          (by rw [s2Φ₂_natDegree h2 hq]; norm_num) _ _ ?_
        rw [Polynomial.natDegree_C_mul (pow_ne_zero 8 h2.ne_zero), s2Φ₂_natDegree h2 hq]
        omega
      rw [hdev0, neg_zero, dv2Hgt]
      exact dvSupp_zero_eq_top _ _ ((s2Tower h2 hq).levelDatum h2).hℓ

theorem s2Mu4GradedRes_g8_sq :
    s2Mu4GradedRes h2 hq 170 ((g8 h2 hq : Polynomial O) ^ 2) = Polynomial.X := by
  have h := s2Mu4GradedRes_mul_of_exact h2 hq (tooth_g8 h2 hq) (tooth_g8 h2 hq)
  rw [show (85 : ℕ) + 85 = 170 from by norm_num, ← pow_two] at h
  rw [h, s2Mu4GradedRes_key h2 hq]
  norm_num

theorem s2Mu4GradedRes_neg_tooth :
    s2Mu4GradedRes h2 hq 170
      (-(Polynomial.C ((2 : O) ^ 8) * (s2DepthThreeKeyChain h2 hq).keyAt 2)) = 1 := by
  have hkey2 : (s2DepthThreeKeyChain h2 hq).keyAt 2 = s2DepthTwoKeyAt h2 hq 2 :=
    s2DepthThreeKeyAt_two h2 hq
  rw [hkey2]
  have hd0 : dev (g8 h2 hq)
      (Polynomial.C ((2 : O) ^ 8) * s2DepthTwoKeyAt h2 hq 2) 0
      = Polynomial.C ((2 : O) ^ 8) * s2DepthTwoKeyAt h2 hq 2 :=
    (Polynomial.modByMonic_eq_self_iff (s2g8_monic h2 hq)).mpr
      (Polynomial.degree_lt_degree (by
        rw [s2g8_natDegree h2 hq, Polynomial.natDegree_C_mul (pow_ne_zero 8 h2.ne_zero),
          s2Φ₂_natDegree h2 hq]
        norm_num))
  have hmu3 : S2Mu3ExactGrade h2 hq 85
      (Polynomial.C ((2 : O) ^ 8) * s2DepthTwoKeyAt h2 hq 2) := by
    have h := S2Mu3ExactGrade_mul h2 hq
      (S2Mu3ExactGrade_C_two_pow_eight h2 hq) (tooth_Φ₂ h2 hq)
    rwa [show (64 : ℕ) + 21 = 85 from by norm_num] at h
  refine Polynomial.ext fun t => ?_
  match t with
  | 0 =>
      have hgate : S2Mu4SlotOnGrade h2 hq 170
          (-(Polynomial.C ((2 : O) ^ 8) * s2DepthTwoKeyAt h2 hq 2)) 0 := by
        refine (s2Mu4SlotOnGrade_iff h2 hq).mpr ⟨85, ?_, by norm_num⟩
        rw [dv3Pin, dev_neg (s2g8_monic h2 hq), hd0, dv3Hgt, dv2Supp_neg _ (s2Φ₂_monic h2 hq)]
        exact (S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp hmu3
      have hslot := s2Mu4Coeff_slot h2 hq hgate
      rw [show (0 : ℕ) / 2 = 0 by norm_num, show (170 - 85 * 0) / 2 = 85 by norm_num] at hslot
      rw [s2Mu4GradedRes_coeff, hslot, s2Mu4Eps_eq_one, one_mul, dev_neg (s2g8_monic h2 hq), hd0,
        s2Mu3GradedRes_neg_tooth_eq_one h2 hq, Polynomial.eval_one, Polynomial.coeff_one_zero]
  | t + 1 =>
      rw [s2Mu4GradedRes_coeff, Polynomial.coeff_one, if_neg (by omega)]
      refine s2Mu4Coeff_eq_zero_of_dv3Pin_top h2 hq ?_
      rw [dv3Pin, dev_neg (s2g8_monic h2 hq)]
      have hdev0 : dev (g8 h2 hq)
          (Polynomial.C ((2 : O) ^ 8) * s2DepthTwoKeyAt h2 hq 2) (170 % 2 + 2 * (t + 1)) = 0 := by
        refine dev_eq_zero_of_lt (s2g8_monic h2 hq)
          (by rw [s2g8_natDegree h2 hq]; norm_num) _ _ ?_
        rw [s2g8_natDegree h2 hq, Polynomial.natDegree_C_mul (pow_ne_zero 8 h2.ne_zero),
          s2Φ₂_natDegree h2 hq]
        omega
      rw [hdev0, neg_zero]
      exact dv3Hgt_zero _ _ _ (by norm_num)

theorem s2Mu4GradedRes_g16 :
    s2Mu4GradedRes h2 hq 170 (g16 h2 hq) = Polynomial.X + 1 := by
  have hsub : g16 h2 hq = (g8 h2 hq : Polynomial O) ^ 2 +
      -(Polynomial.C ((2 : O) ^ 8) * (s2DepthThreeKeyChain h2 hq).keyAt 2) := by
    unfold g16; ring
  have hpow : S2Mu4ExactGrade h2 hq 170 ((g8 h2 hq : Polynomial O) ^ 2) := by
    show s2Hgt₄ h2 hq _ = _
    rw [pow_two, s2Hgt₄_mul_all h2 hq, s2Hgt₄_g8 h2 hq]
    norm_num
  have hnegtooth : S2Mu4ExactGrade h2 hq 170
      (-(Polynomial.C ((2 : O) ^ 8) * (s2DepthThreeKeyChain h2 hq).keyAt 2)) := by
    show s2Hgt₄ h2 hq _ = _
    rw [s2Hgt₄_neg_local h2 hq]
    exact s2Mu4_chainNormBelow_tooth_exactGrade h2 hq
  have hg16 : S2Mu4ExactGrade h2 hq 170
      ((g8 h2 hq : Polynomial O) ^ 2 +
        -(Polynomial.C ((2 : O) ^ 8) * (s2DepthThreeKeyChain h2 hq).keyAt 2)) := by
    have h := g16_exactGrade h2 hq
    rwa [hsub] at h
  rw [hsub, s2Mu4GradedRes_add h2 hq hpow hnegtooth hg16,
    s2Mu4GradedRes_g8_sq h2 hq, s2Mu4GradedRes_neg_tooth h2 hq]

theorem s2Mu4NormRes_g16 : s2Mu4NormRes h2 hq (g16 h2 hq) = Polynomial.X + 1 := by
  rw [s2Mu4NormRes_of_exact h2 hq (g16_exactGrade h2 hq), s2Mu4GradedRes_g16 h2 hq]
  have htr : (Polynomial.X + 1 : Polynomial ((s2DepthTwo h2 hq).fld 2)).natTrailingDegree = 0 :=
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr (by simp))
  rw [htr]
  rfl

theorem s2Mu4_hex :
    ∀ ψ : Polynomial ((s2DepthTwo h2 hq).fld 2),
      ψ.Monic → Irreducible ψ → ψ.natDegree = 1 → ψ.coeff 0 ≠ 0 →
        ∃ g : Polynomial O, g.Monic ∧
          g.natDegree = 2 * 1 * (((s2DepthThreeKeyChain h2 hq).keyAt 3).natDegree) ∧
          s2Mu4NormRes h2 hq g = ψ := by
  intro ψ hm hirr hd hc
  have hψ : ψ = Polynomial.X + 1 :=
    C132rp10.s2Mu3_unique_admissible_linear h2 hq ψ hm hd hc
  refine ⟨g16 h2 hq, g16_monic h2 hq, ?_, ?_⟩
  · rw [show ((s2DepthThreeKeyChain h2 hq).keyAt 3).natDegree = 8 from
      s2DepthThreeKeyAt_natDegree_three h2 hq, show (2 : ℕ) * 1 * 8 = 16 from by norm_num]
    exact g16_natDegree h2 hq
  · rw [hψ]
    exact s2Mu4NormRes_g16 h2 hq

end S2

end Uniformity.Density.Tower.C136d2

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C136d2.exists_mu4SlotOnGrade_of_exact
#print axioms Uniformity.Density.Tower.C136d2.eval_one_s2Mu3GradedRes_eq_coeff_zero
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4GradedRes_coeff_zero_ne_zero_of_exact
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4_graded_scalar_nonzero
#print axioms Uniformity.Density.Tower.C136d2.tooth_mu4_scalar_fires
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4GradedRes_mul_coeff
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4GradedRes_mul_coeff_zero_of_odd
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4GradedRes_mul_coeff_of_prevGrade
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4GradedRes_mul_of_exact
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4GradedRes_mul_of_prevGrade
#print axioms Uniformity.Density.Tower.C136d2.S2Mu4PrevGrade
#print axioms Uniformity.Density.Tower.C136d2.S2Mu4PrevGrade_iff_mod
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4_graded_mul
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4GradeOf
#print axioms Uniformity.Density.Tower.C136d2.S2Mu4ExactGrade_s2Mu4GradeOf
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4GradeOf_eq_of_exact
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4NormRes
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4NormRes_of_exact
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4NormRes_coeff
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4NormRes_zero
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4NormRes_mul_X_pow_of_exact
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4GradedRes_ne_zero_of_exact
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4NormRes_coeff_zero_ne_zero
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4NormRes_ne_zero
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4GradedRes_natTrailingDegree_mul
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4NormRes_mul_of_exact
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4NormRes_mul
#print axioms Uniformity.Density.Tower.C136d2.S2Mu4ExactGrade_one
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4GradedRes_one
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4NormRes_one
#print axioms Uniformity.Density.Tower.C136d2.S2Mu4ExactGrade_key_pow
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4GradedRes_key
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4GradedRes_key_pow
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4NormRes_key
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4NormRes_key_pow
#print axioms Uniformity.Density.Tower.C136d2.s2Hgt₃_C_two
#print axioms Uniformity.Density.Tower.C136d2.S2Mu3ExactGrade_C_two
#print axioms Uniformity.Density.Tower.C136d2.S2Mu3ExactGrade_C_two_pow_eight
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4_chainNormBelow_tooth_ne_zero
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4_chainNormBelow_tooth_exactGrade
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4_chainNormBelow_exactGrade
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4_B1_degree_supply
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4_B1_nonzero_supply
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4_B1_exact_grade_supply
#print axioms Uniformity.Density.Tower.C136d2.g16
#print axioms Uniformity.Density.Tower.C136d2.g16_monic
#print axioms Uniformity.Density.Tower.C136d2.g16_natDegree
#print axioms Uniformity.Density.Tower.C136d2.g16_exactGrade
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4GradedRes_g8_sq
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4GradedRes_neg_tooth
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4GradedRes_g16
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4NormRes_g16
#print axioms Uniformity.Density.Tower.C136d2.s2Mu4_hex

end AxCheck
