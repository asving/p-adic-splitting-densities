/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C132rp3
import Uniformity.ChapC.C132rp8
import Uniformity.ChapC.C132nv5
import Uniformity.ChapC.C136d3ad

/-!
# Uniformity.ChapC.C136d1 — the μ₄ operator stack's middle tranche: D3-05..D3-09 [D3B 2026-08-28]

**Unit D3B** of the deep-witness campaign
(`docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md` §6.2, rows D3-05 through D3-09).
Chains onto D3-04's just-landed UNCONDITIONAL `s2Hgt₄_mul`/`s2Hgt₄_mul_all`
(`C136d3ad`, fired from the discharged survival `s2_dv3ResSurv_at_85`), on top of C136d0's
dv3 support layer (D3-00/01/02).  Every declaration below is the exact one-level-up mirror
of the landed μ₃ campaign's `C132rp0`/`C132rp1`/`C132rp2`/`C132rp3`/`C132rp4`, with the inner
key `Φ₂` (level-2) replaced by `g8` (level-3), the outer side `(u₃,ℓ₃) = (21,2)` replaced by
`(u₄,ℓ₄) = (85,2)`, the ε-data numerals `(e₂,h₂) = (2,5)` replaced by `(e₃,h₃) = (2,21)`
(one level up in BOTH slots: gate numerals AND ε-data numerals), and the inner graded/
normalized read `s2GradedRes`/`s2NormRes` (μ₂-level, `C130rp1`/`C130rp8`) replaced by the
landed μ₃-level `s2Mu3GradedRes`/`s2Mu3NormRes` (`C132rp2`/`C132rp8`).  The residue field
codomain stays `(s2DepthTwo h2 hq).fld 2` throughout — S2's constant residue tower means
every level's coefficient field is the SAME two-element field, so no field-index bump is
needed anywhere in this port (checked: `s2Fld₂_card`'s own proof is `C80.card_K₁ h2 hq`
regardless of the index, confirming `.fld i` is definitionally the same type at every `i`).

## What lands

* **D3-05 (valuation/grades).** `s2Hgt₄_one_eq_zero` (a fresh tooth, the `h1`-shape bridge
  mirror of `C132nv5.s2Hgt₃_one_eq_zero`), then the genuine UNCONDITIONAL `AddValuation`
  packaging `s2AddVal₄` directly from `C136d3ad.s2Hgt₄_mul_all` (no nonemptiness-gap
  machinery needed, unlike `C132nv6`, because D3-04 already landed the unconditional
  product law) — plus the full `S2Mu4ExactGrade`/`S2Mu4AboveGrade` grade-predicate bank,
  mirroring `C132rp0` wholesale.
* **D3-06 (grade-line/epsilon).** Published Def 3.12's line arithmetic at levels 4 (gate,
  `(e₄,h₄)=(2,85)`) and 3 (ε-data, `(e₃,h₃)=(2,21)`, Bézout pair `(1,-10)`); the μ₄ gate
  `S2Mu4SlotOnGrade β g s := 2·μ₃(A_s) + 85·s = β`; the ε-exponent/collapse at the SAME
  two-element field (reusing `C132rp1.s2Fld₂_eq_one_of_ne_zero`/`s2Mu3_eval_letter_pinned`
  directly rather than re-deriving the collapse, since both are field-generic, not
  level-specific).
* **D3-07 (recursive coefficient).** `s2Mu4Coeff`, reading the landed μ₃ GRADED operator
  `s2Mu3GradedRes` at the on-line inner grade; the letter-display, true-height, and
  graded/normalized (`s2Mu3NormRes`) collapse pins; the finite-support and above-grade
  zero laws.
* **D3-08 (total graded operator/add).** `s2Mu4GradedRes`, its master coefficient law,
  range independence, finite support, and zero-above law (mirror of `C132rp2`); PLUS the
  exact-grade additivity engine — the level-3 floor bridge `le_dv3Pin_of_le_dv3Supp`
  (off the ALREADY-LANDED `C136d0.dv3Supp_le_term`, unlike `C132rp3`'s private re-derivation
  one level down), the coefficient floor bridge, `s2Mu4Coeff_add`, and the polynomial lift
  `s2Mu4GradedRes_add_of_le`/`s2Mu4GradedRes_add` (mirror of `C132rp3`).
* **D3-09 (carry arithmetic).** `s2Mu4Carry`/`s2Mu4Carry_parity` (the `e=2` carry identity —
  numeral-only, IDENTICAL formula to `C132rp4.s2Mu3Carry_parity` since it never mentions
  `h`, reproved standalone per the corpus's private-copy convention), the abscissa endpoint
  sum, the gate-level endpoint sum (building on D3-06's `s2Mu4SlotOnGrade_parity`), and the
  `u`-value endpoint sum `s2Mu4_def312_add` (REUSING D3-06's `s2Mu4_def312_level4` twice,
  mirroring `C132rp4`'s reuse of `s2Mu3_def312_level3`).

## What this unit does NOT claim (honesty scope)

No multiplicativity/convolution (published Cor 4.12(2)/(3): D3-10, superseded by the [DWR]
§11.7 L2E shared engine), no normalization of the μ₄ operator itself (D3-11/D3-12), no
`FGMNSourceData`/`FGMNSourceLaws` record (D3-18/19).  The OPEN-RP1-TRANSPORT faithfulness
split (the μ₃-level read's own paper fidelity) is exactly as `C132rp1`/`C132rp2`/`C132rp8`
left it — this unit inherits it as a citation, never re-derives or re-opens it.  Part-4
"computation teeth" at concrete landed numerals (the μ₃ campaign's `C132rp1` Part 4 genre)
are NOT reproduced here: no downstream row in this unit's scope consumes them, and the
row budgets (30–60 min each) do not include them.

**DEPENDS.** `C136d0` (D3-00/01/02: `dv3Hgt`/`dv3Pin`/`dv3Supp`, `s2Hgt₄` + its zero/add-ge/
key-value teeth, `s2g8_monic`/`s2g8_natDegree`, `dv3Pin_top_of_gt`, `dv3Supp_le_term`,
`dv3Supp_ne_top_of_ne_zero`) · `C136d3ad` (D3-03/04: `s2Hgt₄_mul_all`) · `C132nv0`
(`min_dv2Supp_le_dv2Supp_add`) · `C132nv1` (`s2Hgt₃`, `s2Hgt₃_eq_dv2Supp`, `s2Φ₂_monic`,
`s2Φ₂_natDegree`) · `C132nv5` (`s2Hgt₃_one_eq_zero`) · `C130rp0` (`toZ_lt_toZ_iff`,
`S2Grade_natCast_add`) · `C132rp0` (`S2Mu3ExactGrade`, `S2Mu3AboveGrade`, their `dv2Supp`
normal forms) · `C132rp1` (`s2Fld₂_eq_one_of_ne_zero`, `s2Mu3_eval_letter_pinned`) ·
`C132rp2` (`s2Mu3GradedRes`, `s2Mu3GradedRes_zero_of_above`) · `C132rp3`
(`s2Mu3GradedRes_add_of_le`) · `C132rp8` (`s2Mu3NormRes`, `s2Mu3NormRes_mul_X_pow_of_exact`)
· `C132rp10b` (`g8`) · `C130nv2` (`weight_read`) · `C118a` (`smul_top_pos`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement invented
beyond the rows' sketches and the μ₃ porting pattern.  New statement shapes (every `def`
and every theorem introducing a new predicate) are trust-boundary declarations flagged for
human review.  Verdict: `runs/wave-c/verdict_D3B.md`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C136d1

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130rp0
open Uniformity.Density.Tower.C132nv0 Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C132nv5
open Uniformity.Density.Tower.C132rp0 Uniformity.Density.Tower.C132rp1
open Uniformity.Density.Tower.C132rp2 Uniformity.Density.Tower.C132rp3
open Uniformity.Density.Tower.C132rp8
open Uniformity.Density.Tower.C132rp10b
open Uniformity.Density.Tower.C136d0 Uniformity.Density.Tower.C136d3ad
open Uniformity.Density.Tower.C80

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## D3-05 — valuation/grades: the `AddValuation` packaging and the grade-predicate bank

Mirror of `C132nv5`'s `h1`-tooth + `C132nv6` Part 3 (the `AddValuation` packaging) +
`C132rp0` wholesale (the grade predicates), one level up.  UNLIKE `C132nv6`, no
nonemptiness-gap-closing machinery is needed: D3-04 (`C136d3ad.s2Hgt₄_mul_all`) is already
the fully unconditional `hmul` shape at birth. -/

/-! ### The `h1`-shape bridging tooth: `s2Hgt₄ 1 = 0` -/

private theorem one_mod_g8 : (1 : Polynomial O) %ₘ (g8 h2 hq) = 1 :=
  (Polynomial.modByMonic_eq_self_iff (s2g8_monic h2 hq)).mpr
    (Polynomial.degree_lt_degree
      (by rw [Polynomial.natDegree_one, s2g8_natDegree h2 hq]; norm_num))

private theorem dv3Hgt_one_eq_zero :
    dv3Hgt ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (1 : Polynomial O)
      = (0 : ℕ∞) := by
  apply C130s6.toZ_inj
  rw [dv3Hgt, ← s2Hgt₃_eq_dv2Supp h2 hq, s2Hgt₃_one_eq_zero h2 hq]
  rfl

/-- ★ **the `h1`-shape bridging tooth**: `s2Hgt₄ 1 = 0` in `AddValuation.of`'s exact `h1`
shape — the μ₄ twin of `C132nv5.s2Hgt₃_one_eq_zero`. -/
theorem s2Hgt₄_one_eq_zero : s2Hgt₄ h2 hq (1 : Polynomial O) = 0 := by
  have hdev0 : dev (g8 h2 hq) (1 : Polynomial O) 0 = 1 := one_mod_g8 h2 hq
  have hval : dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) (1 : Polynomial O) 85 2 = ((0 : ℕ) : ℕ∞) := by
    rw [dv3Supp, Polynomial.natDegree_one, show Finset.range (0 + 1) = {0} by decide,
      Finset.inf_singleton, dv3Pin, hdev0, dv3Hgt_one_eq_zero h2 hq]
    simp
  rw [s2Hgt₄, hval, C130s6.toZ_coe]
  rfl

/-! ### The genuine UNCONDITIONAL `AddValuation` instance -/

/-- ★ **the genuine (UNCONDITIONAL) `AddValuation` instance for `s2Hgt₄`**, directly from
`AddValuation.of` at D3-04's already-unconditional `s2Hgt₄_mul_all` — no conditional
wrapper, no nonemptiness gap, unlike `C132nv6`. -/
noncomputable def s2AddVal₄ : AddValuation (Polynomial O) (WithTop ℤ) :=
  AddValuation.of (s2Hgt₄ h2 hq) (s2Hgt₄_zero h2 hq) (s2Hgt₄_one_eq_zero h2 hq)
    (s2Hgt₄_add_ge h2 hq) (s2Hgt₄_mul_all h2 hq)

/-- Anti-drift restriction pin: `s2AddVal₄` evaluates to exactly `s2Hgt₄`. -/
theorem s2AddVal₄_apply (A : Polynomial O) : s2AddVal₄ h2 hq A = s2Hgt₄ h2 hq A := rfl

/-! ### The concrete S2 μ₄ instantiation of `FGMNSourceData.ExactGrade`/`AboveGrade` -/

/-- `S2Mu4ExactGrade β g ↔ μ₄(g) = β` (the μ₄ analogue of `C132rp0.S2Mu3ExactGrade`). -/
def S2Mu4ExactGrade (β : ℕ) (g : Polynomial O) : Prop :=
  s2Hgt₄ h2 hq g = (β : WithTop ℤ)

/-- `S2Mu4AboveGrade β g ↔ μ₄(g) > β` (the μ₄ analogue of `C132rp0.S2Mu3AboveGrade`). -/
def S2Mu4AboveGrade (β : ℕ) (g : Polynomial O) : Prop :=
  (β : WithTop ℤ) < s2Hgt₄ h2 hq g

theorem S2Mu4ExactGrade_iff_dv3Supp {β : ℕ} {g : Polynomial O} :
    S2Mu4ExactGrade h2 hq β g ↔
      dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) g 85 2
        = (β : ℕ∞) := by
  unfold S2Mu4ExactGrade
  rw [s2Hgt₄_eq_dv3Supp]
  constructor
  · intro h
    exact toZ_inj (by rw [h]; norm_cast)
  · intro h
    rw [h]; norm_cast

theorem S2Mu4AboveGrade_iff_dv3Supp {β : ℕ} {g : Polynomial O} :
    S2Mu4AboveGrade h2 hq β g ↔
      (β : ℕ∞) < dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
        (g8 h2 hq) g 85 2 := by
  unfold S2Mu4AboveGrade
  rw [s2Hgt₄_eq_dv3Supp]
  rw [show (β : WithTop ℤ) = toZ (β : ℕ∞) by norm_cast]
  exact toZ_lt_toZ_iff

theorem S2Mu4ExactGrade_exists {g : Polynomial O} (hg : g ≠ 0) :
    ∃ β : ℕ, S2Mu4ExactGrade h2 hq β g := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1
    (dv3Supp_ne_top_of_ne_zero ((s2Tower h2 hq).levelDatum h2) (s2Φ₂_monic h2 hq)
      (by rw [s2Φ₂_natDegree h2 hq]; norm_num) 21 2 (s2g8_monic h2 hq)
      (by rw [s2g8_natDegree h2 hq]; norm_num) 85 2 hg)
  exact ⟨n, (S2Mu4ExactGrade_iff_dv3Supp h2 hq).mpr hn.symm⟩

theorem S2Mu4ExactGrade_unique {β β' : ℕ} {g : Polynomial O}
    (h1 : S2Mu4ExactGrade h2 hq β g) (h2' : S2Mu4ExactGrade h2 hq β' g) : β = β' := by
  unfold S2Mu4ExactGrade at h1 h2'
  rw [h1] at h2'
  exact_mod_cast h2'

/-- ★ **the grade arithmetic** — `S2Mu4ExactGrade` is closed under multiplication with
grades adding, UNCONDITIONALLY (off D3-04's `s2Hgt₄_mul_all`). -/
theorem S2Mu4ExactGrade_mul {β β' : ℕ} {g h : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) (hh : S2Mu4ExactGrade h2 hq β' h) :
    S2Mu4ExactGrade h2 hq (β + β') (g * h) := by
  unfold S2Mu4ExactGrade at hg hh ⊢
  rw [s2Hgt₄_mul_all h2 hq, hg, hh, S2Grade_natCast_add]

theorem S2Mu4ExactGrade_not_above {β : ℕ} {g : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) : ¬ S2Mu4AboveGrade h2 hq β g := by
  unfold S2Mu4ExactGrade at hg
  unfold S2Mu4AboveGrade
  rw [hg]
  exact lt_irrefl _

theorem S2Mu4ExactGrade_not_zero {β : ℕ} {g : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) : g ≠ 0 := by
  intro h0
  unfold S2Mu4ExactGrade at hg
  rw [h0, s2Hgt₄_zero] at hg
  exact WithTop.top_ne_coe hg

theorem S2Mu4ExactGrade_zero_false (β : ℕ) :
    ¬ S2Mu4ExactGrade h2 hq β (0 : Polynomial O) :=
  fun hg => S2Mu4ExactGrade_not_zero h2 hq hg rfl

theorem S2Mu4AboveGrade_zero (β : ℕ) : S2Mu4AboveGrade h2 hq β (0 : Polynomial O) := by
  unfold S2Mu4AboveGrade
  rw [s2Hgt₄_zero]
  exact_mod_cast WithTop.coe_lt_top (β : ℤ)

theorem S2Mu4ExactGrade_eq_addVal (β : ℕ) (g : Polynomial O) :
    S2Mu4ExactGrade h2 hq β g ↔ s2AddVal₄ h2 hq g = (β : WithTop ℤ) := by
  unfold S2Mu4ExactGrade
  rw [s2AddVal₄_apply]

theorem S2Mu4AboveGrade_eq_addVal (β : ℕ) (g : Polynomial O) :
    S2Mu4AboveGrade h2 hq β g ↔ (β : WithTop ℤ) < s2AddVal₄ h2 hq g := by
  unfold S2Mu4AboveGrade
  rw [s2AddVal₄_apply]

/-- **tooth**: `h₄(g₈) = 85 = u₄` re-read as an exact grade, off `C136d0.s2Hgt₄_g8`. -/
theorem tooth_g8 : S2Mu4ExactGrade h2 hq 85 (g8 h2 hq : Polynomial O) := by
  unfold S2Mu4ExactGrade
  rw [s2Hgt₄_g8]
  norm_cast

/-! ## D3-06 — grade-line gate and ε-factor, at levels 4 (gate) and 3 (ε-data)

Mirror of `C132rp1` Parts 0–2, one level up: the gate's OWN numerals move `(2,21) ↦
(2,85)`; the ε-exponent's numerals — one level DOWN from the gate, i.e. the level whose
OWN outer numerals build the gate's inner variable — move `(2,5) ↦ (2,21)`. -/

/-! ### Part 0 — published Def 3.12's grade-line arithmetic at levels 4 and 3 -/

/-- **Def 3.12 at `i = 4`, uniqueness** (`(e₄,h₄) = (2,85)`): the unique solution of
`u·2 + s·85 = β`, `0 ≤ s < 2` is `s₄(β) = β % 2`, `u₄(β) = (β − 85·(β % 2))/2`. -/
theorem s2Mu4_def312_level4 (β : ℕ) (u s : ℤ) (h : u * 2 + s * 85 = (β : ℤ))
    (hs0 : 0 ≤ s) (hs2 : s < 2) :
    s = ((β % 2 : ℕ) : ℤ) ∧ u = ((β : ℤ) - 85 * ((β % 2 : ℕ) : ℤ)) / 2 := by omega

/-- **Def 3.12 at `i = 3`, uniqueness** (`(e₃,h₃) = (2,21)`): the unique solution of
`u·2 + s·21 = m`, `0 ≤ s < 2` — the ε-exponent's data, one level down from the gate. -/
theorem s2Mu4_def312_level3 (m : ℕ) (u s : ℤ) (h : u * 2 + s * 21 = (m : ℤ))
    (hs0 : 0 ≤ s) (hs2 : s < 2) :
    s = ((m % 2 : ℕ) : ℤ) ∧ u = ((m : ℤ) - 21 * ((m % 2 : ℕ) : ℤ)) / 2 := by omega

/-- **Def 3.12 at `i = 3`, existence**: the displayed pair does solve the equation with the
required range constraint. -/
theorem s2Mu4_def312_level3_exists (m : ℕ) :
    (((m : ℤ) - 21 * ((m % 2 : ℕ) : ℤ)) / 2) * 2 + ((m % 2 : ℕ) : ℤ) * 21 = (m : ℤ)
      ∧ 0 ≤ ((m % 2 : ℕ) : ℤ) ∧ ((m % 2 : ℕ) : ℤ) < 2 := by omega

/-- **§3.3's Bézout pair at `i = 3`**: `(ℓ₃, ℓ₃′) = (1, −10)` solves `ℓ₃·h₃ + ℓ₃′·e₃ = 1`
with `0 ≤ ℓ₃ < e₃` at `(e₃, h₃) = (2, 21)`. -/
theorem s2Mu4_bezout_level3 :
    (1 : ℤ) * 21 + (-10) * 2 = 1 ∧ (0 : ℤ) ≤ 1 ∧ (1 : ℤ) < 2 := by norm_num

/-! ### Part 1 — ★ the μ₄ grade-line gate `S2Mu4SlotOnGrade` -/

/-- ★ **the μ₄ grade-line gate**: `2·μ₃(A_s) + 85·s = β` — slot `s` of the `g₈`-development
of `g` sits exactly on the μ₄ grade-`β` line. -/
def S2Mu4SlotOnGrade (β : ℕ) (g : Polynomial O) (s : ℕ) : Prop :=
  2 • dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) g s
    + ((85 * s : ℕ) : ℕ∞) = (β : ℕ∞)

theorem s2Mu4SlotOnGrade_iff {β s : ℕ} {g : Polynomial O} :
    S2Mu4SlotOnGrade h2 hq β g s ↔
      ∃ m : ℕ, dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
          (g8 h2 hq) g s = (m : ℕ∞) ∧ 2 * m + 85 * s = β := by
  unfold S2Mu4SlotOnGrade
  constructor
  · intro h
    have hne : dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
        (g8 h2 hq) g s ≠ ⊤ := by
      intro htop
      rw [htop, C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2), top_add] at h
      exact WithTop.top_ne_coe h
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
    refine ⟨m, hm.symm, ?_⟩
    rw [← hm, nsmul_eq_mul] at h
    exact_mod_cast h
  · rintro ⟨m, hm, hβ⟩
    rw [hm, nsmul_eq_mul, ← hβ]
    push_cast
    ring

/-- **the campaign display form**: the gate reads the inner value through the landed
μ₃ table `s2Hgt₃` itself — `2·μ₃(A_s) + 85·s = β` verbatim. -/
theorem s2Mu4SlotOnGrade_iff_hgt₃ {β s : ℕ} {g : Polynomial O} :
    S2Mu4SlotOnGrade h2 hq β g s ↔
      ∃ m : ℕ, s2Hgt₃ h2 hq (dev (g8 h2 hq) g s) = ((m : ℤ) : WithTop ℤ)
        ∧ 2 * m + 85 * s = β := by
  rw [s2Mu4SlotOnGrade_iff h2 hq]
  constructor
  · rintro ⟨m, hm, hβ⟩
    refine ⟨m, ?_, hβ⟩
    rw [dv3Pin, dv3Hgt] at hm
    rw [s2Hgt₃_eq_dv2Supp h2 hq, hm]
    exact C130s6.toZ_coe m
  · rintro ⟨m, hm, hβ⟩
    refine ⟨m, ?_, hβ⟩
    rw [dv3Pin, dv3Hgt]
    apply C130s6.toZ_inj
    rw [← s2Hgt₃_eq_dv2Supp h2 hq, hm]
    exact (C130s6.toZ_coe m).symm

/-- **parity of on-line slots**: every slot on the μ₄ grade-`β` line has the grade's
parity. -/
theorem s2Mu4SlotOnGrade_parity {β s : ℕ} {g : Polynomial O}
    (h : S2Mu4SlotOnGrade h2 hq β g s) : s % 2 = β % 2 := by
  obtain ⟨m, -, hβ⟩ := (s2Mu4SlotOnGrade_iff h2 hq).mp h
  omega

/-- ★ **the inner exact-grade pin** (eq (10)'s second conjunct): on the gate, the
development coefficient `A_s` has EXACTLY the on-line inner μ₃ grade `(β − 85s)/2`. -/
theorem s2Mu4SlotOnGrade_inner_exact {β s : ℕ} {g : Polynomial O}
    (h : S2Mu4SlotOnGrade h2 hq β g s) :
    S2Mu3ExactGrade h2 hq ((β - 85 * s) / 2) (dev (g8 h2 hq) g s) := by
  obtain ⟨m, hm, hβ⟩ := (s2Mu4SlotOnGrade_iff h2 hq).mp h
  have hdiv : (β - 85 * s) / 2 = m := by omega
  rw [dv3Pin, dv3Hgt] at hm
  rw [hdiv]
  exact (S2Mu3ExactGrade_iff_dv2Supp h2 hq).mpr hm

/-- an on-line slot bounds the cleared μ₄ support. -/
theorem dv3Supp_le_of_mu4SlotOnGrade {β s : ℕ} {g : Polynomial O}
    (h : S2Mu4SlotOnGrade h2 hq β g s) :
    dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) g 85 2
      ≤ (β : ℕ∞) := by
  obtain ⟨m, hm, hβ⟩ := (s2Mu4SlotOnGrade_iff h2 hq).mp h
  have hs : s ≤ g.natDegree := by
    by_contra hs
    rw [dv3Pin_top_of_gt ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21
      (by norm_num) (s2g8_monic h2 hq) (by rw [s2g8_natDegree h2 hq]; norm_num) g
      (not_le.mp hs)] at hm
    exact absurd hm (by exact WithTop.top_ne_coe)
  have hle : dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) g 85 2
      ≤ 2 • dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
          (g8 h2 hq) g s + ((85 : ℕ∞) * (s : ℕ∞)) := by
    rw [dv3Supp]
    exact Finset.inf_le (Finset.mem_range.mpr (by omega))
  have heq : 2 • dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) g s + ((85 : ℕ∞) * (s : ℕ∞)) = (β : ℕ∞) := by
    rw [hm, nsmul_eq_mul, ← hβ]
    push_cast
    ring
  rw [heq] at hle
  exact hle

/-! ### Part 2 — the FGMN ε-factor at level 3, and the S2 collapse (REUSED from `C132rp1`)

The letter and the field are ALREADY generic (not level-specific) in `C132rp1`'s own
collapse: `s2Fld₂_eq_one_of_ne_zero` and `s2Mu3_eval_letter_pinned` are field-only facts,
so this Part cites them directly rather than re-deriving. Only the EXPONENT (level-3's
own Bézout data) is level-specific and genuinely new. -/

/-- **Def 3.12's ε-exponent at the S2 level-3 numerals**: `ℓ₃′·s₃(m) − ℓ₃·u₃(m)` with
`(ℓ₃, ℓ₃′) = (1, −10)`. -/
def s2Mu4EpsExp (m : ℕ) : ℤ :=
  (-10) * ((m % 2 : ℕ) : ℤ) - ((m : ℤ) - 21 * ((m % 2 : ℕ) : ℤ)) / 2

theorem s2Mu4EpsExp_eq (m : ℕ) :
    s2Mu4EpsExp m
      = (-10) * ((m % 2 : ℕ) : ℤ) - 1 * (((m : ℤ) - 21 * ((m % 2 : ℕ) : ℤ)) / 2) := by
  unfold s2Mu4EpsExp
  ring

/-- **the ε-factor, parametric in the letter**: `ε₃(m) = z^{s2Mu4EpsExp m}`. -/
noncomputable def s2Mu4EpsOf (z : (s2DepthTwo h2 hq).fld 2) (m : ℕ) :
    (s2DepthTwo h2 hq).fld 2 :=
  z ^ s2Mu4EpsExp m

/-- ★ **the ε-collapse**: for every nonzero letter `z`, the ε-factor is `1` — reusing
`C132rp1.s2Fld₂_eq_one_of_ne_zero`, since the collapse is a field fact, not a level fact. -/
theorem s2Mu4EpsOf_eq_one {z : (s2DepthTwo h2 hq).fld 2} (hz : z ≠ 0) (m : ℕ) :
    s2Mu4EpsOf h2 hq z m = 1 := by
  unfold s2Mu4EpsOf
  rw [C132rp1.s2Fld₂_eq_one_of_ne_zero h2 hq hz, one_zpow]

/-- **the collapsed ε-operator** used by the coefficient definition. -/
noncomputable def s2Mu4Eps (_ : ℕ) : (s2DepthTwo h2 hq).fld 2 := 1

theorem s2Mu4Eps_eq_one (m : ℕ) : s2Mu4Eps h2 hq m = 1 := rfl

theorem s2Mu4Eps_eq_epsOf {z : (s2DepthTwo h2 hq).fld 2} (hz : z ≠ 0) (m : ℕ) :
    s2Mu4Eps h2 hq m = s2Mu4EpsOf h2 hq z m :=
  (s2Mu4EpsOf_eq_one h2 hq hz m).symm

theorem s2Mu4Eps_ne_zero (m : ℕ) : s2Mu4Eps h2 hq m ≠ 0 := one_ne_zero

/-! ## D3-07 — the recursive coefficient `s2Mu4Coeff`

Mirror of `C132rp1` Part 3, one level up: the inner read is the landed μ₃-level GRADED
operator `s2Mu3GradedRes` (`C132rp2`), and the graded/normalized collapse reads the landed
μ₃-level NORMALIZED operator `s2Mu3NormRes` (`C132rp8`). -/

open Classical in
/-- ★ **the μ₄ recursive coefficient**: the landed μ₃ graded read of the `g₈`-development
slot at the `t`-th abscissa `β % 2 + 2t` of the grade-`β` line, at the on-line inner grade
`(β − 85s)/2`, evaluated at the collapsed letter and multiplied by the collapsed
ε-factor, if the slot is on the line; `0` otherwise. -/
noncomputable def s2Mu4Coeff (β : ℕ) (g : Polynomial O) (t : ℕ) :
    (s2DepthTwo h2 hq).fld 2 :=
  if S2Mu4SlotOnGrade h2 hq β g (β % 2 + 2 * t) then
    s2Mu4Eps h2 hq ((β - 85 * (β % 2 + 2 * t)) / 2)
      * Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
          (s2Mu3GradedRes h2 hq ((β - 85 * (β % 2 + 2 * t)) / 2)
            (dev (g8 h2 hq) g (β % 2 + 2 * t)))
  else 0

open Classical in
/-- ★ **the letter-display pin**: for EVERY nonzero candidate letter `z`, the coefficient
equals the literal published display with `z` in place of the collapsed values. -/
theorem s2Mu4Coeff_letter_display {z : (s2DepthTwo h2 hq).fld 2} (hz : z ≠ 0)
    (β : ℕ) (g : Polynomial O) (t : ℕ) :
    s2Mu4Coeff h2 hq β g t =
      if S2Mu4SlotOnGrade h2 hq β g (β % 2 + 2 * t) then
        s2Mu4EpsOf h2 hq z ((β - 85 * (β % 2 + 2 * t)) / 2)
          * Polynomial.eval z
              (s2Mu3GradedRes h2 hq ((β - 85 * (β % 2 + 2 * t)) / 2)
                (dev (g8 h2 hq) g (β % 2 + 2 * t)))
      else 0 := by
  unfold s2Mu4Coeff
  rw [s2Mu4EpsOf_eq_one h2 hq hz, s2Mu4Eps_eq_one, C132rp1.s2Mu3_eval_letter_pinned h2 hq hz]

/-- **the true-height pin**: on the gate, the `ℕ`-truncated inner grade `(β − 85s)/2` IS
the slot's actual μ₃ value. -/
theorem s2Mu4Coeff_eq_eval {β t m : ℕ} {g : Polynomial O}
    (hgate : S2Mu4SlotOnGrade h2 hq β g (β % 2 + 2 * t))
    (hm : dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) g
      (β % 2 + 2 * t) = (m : ℕ∞)) :
    s2Mu4Coeff h2 hq β g t =
      Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
        (s2Mu3GradedRes h2 hq m (dev (g8 h2 hq) g (β % 2 + 2 * t))) := by
  obtain ⟨m', hm', hβ⟩ := (s2Mu4SlotOnGrade_iff h2 hq).mp hgate
  have hmm : m = m' := by
    rw [hm] at hm'
    exact_mod_cast hm'
  subst hmm
  have hk : (β - 85 * (β % 2 + 2 * t)) / 2 = m := by omega
  unfold s2Mu4Coeff
  rw [if_pos hgate, hk, s2Mu4Eps_eq_one, one_mul]

/-- ★ **the graded/normalized two-read collapse**: on the gate, reading the inner slot
through the landed μ₃ NORMALIZED operator `s2Mu3NormRes` gives the SAME coefficient. -/
theorem s2Mu4Coeff_eq_eval_normRes {β t m : ℕ} {g : Polynomial O}
    (hgate : S2Mu4SlotOnGrade h2 hq β g (β % 2 + 2 * t))
    (hm : dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) g
      (β % 2 + 2 * t) = (m : ℕ∞)) :
    s2Mu4Coeff h2 hq β g t =
      Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
        (s2Mu3NormRes h2 hq (dev (g8 h2 hq) g (β % 2 + 2 * t))) := by
  rw [s2Mu4Coeff_eq_eval h2 hq hgate hm]
  have hex : S2Mu3ExactGrade h2 hq m (dev (g8 h2 hq) g (β % 2 + 2 * t)) := by
    have h := s2Mu4SlotOnGrade_inner_exact h2 hq hgate
    obtain ⟨m', hm', hβ⟩ := (s2Mu4SlotOnGrade_iff h2 hq).mp hgate
    have hmm : m = m' := by
      rw [hm] at hm'
      exact_mod_cast hm'
    have hk : (β - 85 * (β % 2 + 2 * t)) / 2 = m := by omega
    rwa [hk] at h
  rw [← s2Mu3NormRes_mul_X_pow_of_exact h2 hq hex, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, one_pow, mul_one]

/-- **slot completeness**: every on-line slot `s` IS read, at `y`-power `s / 2`. -/
theorem s2Mu4Coeff_slot {β s : ℕ} {g : Polynomial O}
    (h : S2Mu4SlotOnGrade h2 hq β g s) :
    s2Mu4Coeff h2 hq β g (s / 2) =
      s2Mu4Eps h2 hq ((β - 85 * s) / 2)
        * Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
            (s2Mu3GradedRes h2 hq ((β - 85 * s) / 2)
              (dev (g8 h2 hq) g s)) := by
  have hpar := s2Mu4SlotOnGrade_parity h2 hq h
  have hs : β % 2 + 2 * (s / 2) = s := by omega
  unfold s2Mu4Coeff
  rw [hs, if_pos h]

/-- vanishing off finite inner values. -/
theorem s2Mu4Coeff_eq_zero_of_dv3Pin_top {β t : ℕ} {g : Polynomial O}
    (h : dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) g
      (β % 2 + 2 * t) = ⊤) :
    s2Mu4Coeff h2 hq β g t = 0 := by
  unfold s2Mu4Coeff
  rw [if_neg]
  intro hgate
  obtain ⟨m, hm, -⟩ := (s2Mu4SlotOnGrade_iff h2 hq).mp hgate
  rw [h] at hm
  exact WithTop.top_ne_coe hm

/-- **finite support, the natDegree bound**. -/
theorem s2Mu4Coeff_eq_zero_of_natDegree_lt {β t : ℕ} {g : Polynomial O}
    (h : g.natDegree < β % 2 + 2 * t) :
    s2Mu4Coeff h2 hq β g t = 0 :=
  s2Mu4Coeff_eq_zero_of_dv3Pin_top h2 hq
    (dv3Pin_top_of_gt ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21
      (by norm_num) (s2g8_monic h2 hq) (by rw [s2g8_natDegree h2 hq]; norm_num) g h)

/-- **finite support, the grade bound**. -/
theorem s2Mu4Coeff_eq_zero_of_grade_lt {β t : ℕ} {g : Polynomial O}
    (h : β < 85 * (β % 2 + 2 * t)) :
    s2Mu4Coeff h2 hq β g t = 0 := by
  unfold s2Mu4Coeff
  rw [if_neg]
  intro hgate
  obtain ⟨m, -, hβ⟩ := (s2Mu4SlotOnGrade_iff h2 hq).mp hgate
  omega

/-- **the coefficient-level zero law at above-grade inputs** (published Lemma 3.14's
engine, μ₄ occurrence). -/
theorem s2Mu4Coeff_eq_zero_of_above {β : ℕ} {g : Polynomial O}
    (h : S2Mu4AboveGrade h2 hq β g) (t : ℕ) :
    s2Mu4Coeff h2 hq β g t = 0 := by
  have hdv := (S2Mu4AboveGrade_iff_dv3Supp h2 hq).mp h
  unfold s2Mu4Coeff
  rw [if_neg]
  intro hgate
  exact absurd (dv3Supp_le_of_mu4SlotOnGrade h2 hq hgate) (not_le.mpr hdv)

/-! ## D3-08 — the total graded operator `s2Mu4GradedRes`, and the ADD law

Mirror of `C132rp2` (assembly + finite support + zero-above) AND `C132rp3` (the
exact-grade additivity engine), one level up. -/

/-! ### The assembly -/

/-- ★ **the total μ₄ graded residual** `R_β(g) ∈ 𝔽₃[y]` (published Def 3.13 at the μ₄
numerals). -/
noncomputable def s2Mu4GradedRes (β : ℕ) (g : Polynomial O) :
    Polynomial ((s2DepthTwo h2 hq).fld 2) :=
  ∑ t ∈ Finset.range (β + 1), Polynomial.C (s2Mu4Coeff h2 hq β g t) * Polynomial.X ^ t

/-- ★ **the master coefficient law**. -/
theorem s2Mu4GradedRes_coeff (β : ℕ) (g : Polynomial O) (t : ℕ) :
    (s2Mu4GradedRes h2 hq β g).coeff t = s2Mu4Coeff h2 hq β g t := by
  unfold s2Mu4GradedRes
  rw [Uniformity.Hensel.coeff_sum_range_C_mul_X_pow]
  split_ifs with ht
  · rfl
  · exact (s2Mu4Coeff_eq_zero_of_grade_lt h2 hq (by omega)).symm

/-- **range independence**. -/
theorem s2Mu4GradedRes_eq_sum_range (β : ℕ) (g : Polynomial O) {M : ℕ} (hM : β + 1 ≤ M) :
    s2Mu4GradedRes h2 hq β g
      = ∑ t ∈ Finset.range M, Polynomial.C (s2Mu4Coeff h2 hq β g t) * Polynomial.X ^ t := by
  unfold s2Mu4GradedRes
  refine Finset.sum_subset (fun x hx => ?_) fun t _ hts => ?_
  · rw [Finset.mem_range] at hx ⊢
    omega
  · rw [s2Mu4Coeff_eq_zero_of_grade_lt h2 hq
      (by rw [Finset.mem_range, not_lt] at hts; omega), Polynomial.C_0, zero_mul]

/-- **finite support, packaged**. -/
theorem s2Mu4GradedRes_natDegree_le (β : ℕ) (g : Polynomial O) :
    (s2Mu4GradedRes h2 hq β g).natDegree ≤ β := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
  rw [s2Mu4GradedRes_coeff]
  exact s2Mu4Coeff_eq_zero_of_grade_lt h2 hq (by omega)

/-- **finite support, the `natDegree` form on the polynomial**. -/
theorem s2Mu4GradedRes_coeff_eq_zero_of_natDegree_lt {β t : ℕ} (g : Polynomial O)
    (h : g.natDegree < β % 2 + 2 * t) :
    (s2Mu4GradedRes h2 hq β g).coeff t = 0 := by
  rw [s2Mu4GradedRes_coeff]
  exact s2Mu4Coeff_eq_zero_of_natDegree_lt h2 hq h

/-- **the zero law at above-grade inputs** (published Lemma 3.14, the μ₄ occurrence). -/
theorem s2Mu4GradedRes_zero_of_above {β : ℕ} {g : Polynomial O}
    (h : S2Mu4AboveGrade h2 hq β g) : s2Mu4GradedRes h2 hq β g = 0 := by
  refine Polynomial.ext fun t => ?_
  rw [s2Mu4GradedRes_coeff, Polynomial.coeff_zero]
  exact s2Mu4Coeff_eq_zero_of_above h2 hq h t

/-- the zero polynomial has zero graded residual at every grade. -/
theorem s2Mu4GradedRes_zero (β : ℕ) : s2Mu4GradedRes h2 hq β (0 : Polynomial O) = 0 :=
  s2Mu4GradedRes_zero_of_above h2 hq (S2Mu4AboveGrade_zero h2 hq β)

/-! ### The additivity engine (mirror of `C132rp3`)

UNLIKE `C132rp3`'s private re-derivation of the level-2 term bound (one level down), this
Part cites the ALREADY-LANDED `C136d0.dv3Supp_le_term` directly. -/

private theorem dv3Supp_le_term_s2 (f : Polynomial O) (u₃ : ℕ) {ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃)
    (s : ℕ) :
    dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) f u₃ ℓ₃
      ≤ ℓ₃ • dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
          f s + (u₃ * s : ℕ∞) :=
  C136d0.dv3Supp_le_term ((s2Tower h2 hq).levelDatum h2) (s2g8_monic h2 hq)
    (by rw [s2g8_natDegree h2 hq]; norm_num) 21 (by norm_num) f u₃ hℓ₃ s

/-- ★ **the level-3 slot floor from a cleared-support floor** (mirror of
`C132rp3.le_dv2Pin_of_le_dv2Supp`, one level up). -/
theorem le_dv3Pin_of_le_dv3Supp {u₃ ℓ₃ β m s : ℕ} {f : Polynomial O} (hℓ₃ : 0 < ℓ₃)
    (hβ : (β : ℕ∞) ≤ dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) f u₃ ℓ₃)
    (hm : ℓ₃ * m + u₃ * s = β) :
    (m : ℕ∞) ≤ dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) f s := by
  have h := le_trans hβ (dv3Supp_le_term_s2 h2 hq f u₃ hℓ₃ s)
  rcases eq_or_ne (dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) f s) ⊤ with hT | hT
  · rw [hT]; exact le_top
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← hc, C130nv2.weight_read] at h
  rw [← hc]
  have hnat : β ≤ ℓ₃ * c + u₃ * s := by exact_mod_cast h
  exact_mod_cast Nat.le_of_mul_le_mul_left (by omega : ℓ₃ * m ≤ ℓ₃ * c) hℓ₃

/-- ★ **the μ₄ coefficient floor bridge** (mirror of `C132rp3.s2Mu3Coeff_eq_eval_of_le`). -/
theorem s2Mu4Coeff_eq_eval_of_le {β t m : ℕ} {g : Polynomial O}
    (hm : 2 * m + 85 * (β % 2 + 2 * t) = β)
    (hge : (m : ℕ∞)
        ≤ dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) g
            (β % 2 + 2 * t)) :
    s2Mu4Coeff h2 hq β g t =
      Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
        (s2Mu3GradedRes h2 hq m (dev (g8 h2 hq) g (β % 2 + 2 * t))) := by
  rcases eq_or_lt_of_le hge with heq | hlt
  · exact s2Mu4Coeff_eq_eval h2 hq
      ((s2Mu4SlotOnGrade_iff h2 hq).mpr ⟨m, heq.symm, hm⟩) heq.symm
  · have hgate : ¬ S2Mu4SlotOnGrade h2 hq β g (β % 2 + 2 * t) := by
      intro hgate
      obtain ⟨m', hm', hβ⟩ := (s2Mu4SlotOnGrade_iff h2 hq).mp hgate
      rw [hm'] at hlt
      have : m < m' := by exact_mod_cast hlt
      omega
    have habove : S2Mu3AboveGrade h2 hq m (dev (g8 h2 hq) g (β % 2 + 2 * t)) := by
      rw [dv3Pin, dv3Hgt] at hlt
      exact (S2Mu3AboveGrade_iff_dv2Supp h2 hq).mpr hlt
    unfold s2Mu4Coeff
    rw [if_neg hgate, s2Mu3GradedRes_zero_of_above h2 hq habove, Polynomial.eval_zero]

/-! ### ★ the coefficientwise and polynomial ADD laws -/

theorem s2Mu4Coeff_add {β t : ℕ} {g h : Polynomial O}
    (hg : (β : ℕ∞)
        ≤ dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) g
            85 2)
    (hh : (β : ℕ∞)
        ≤ dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) h
            85 2) :
    s2Mu4Coeff h2 hq β (g + h) t
      = s2Mu4Coeff h2 hq β g t + s2Mu4Coeff h2 hq β h t := by
  rcases Nat.lt_or_ge β (85 * (β % 2 + 2 * t)) with hlt | hge85
  · rw [s2Mu4Coeff_eq_zero_of_grade_lt h2 hq hlt,
      s2Mu4Coeff_eq_zero_of_grade_lt h2 hq hlt,
      s2Mu4Coeff_eq_zero_of_grade_lt h2 hq hlt, add_zero]
  · have hm : 2 * ((β - 85 * (β % 2 + 2 * t)) / 2) + 85 * (β % 2 + 2 * t) = β := by omega
    have hgeg := le_dv3Pin_of_le_dv3Supp h2 hq (by norm_num) hg hm
    have hgeh := le_dv3Pin_of_le_dv3Supp h2 hq (by norm_num) hh hm
    have hmin : min
        (dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) g
          (β % 2 + 2 * t))
        (dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) h
          (β % 2 + 2 * t))
        ≤ dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
            (g + h) (β % 2 + 2 * t) := by
      rw [dv3Pin, dv3Pin, dv3Pin,
        dev_add_of_monic (s2g8_monic h2 hq) g h (β % 2 + 2 * t),
        dv3Hgt, dv3Hgt, dv3Hgt]
      exact min_dv2Supp_le_dv2Supp_add ((s2Tower h2 hq).levelDatum h2) (s2Φ₂_monic h2 hq)
        (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num) _ _
    have hgegh := le_trans (le_min hgeg hgeh) hmin
    rw [s2Mu4Coeff_eq_eval_of_le h2 hq hm hgegh,
      s2Mu4Coeff_eq_eval_of_le h2 hq hm hgeg,
      s2Mu4Coeff_eq_eval_of_le h2 hq hm hgeh,
      dev_add_of_monic (s2g8_monic h2 hq) g h (β % 2 + 2 * t)]
    rw [dv3Pin, dv3Hgt] at hgeg
    rw [dv3Pin, dv3Hgt] at hgeh
    rw [C132rp3.s2Mu3GradedRes_add_of_le h2 hq hgeg hgeh, Polynomial.eval_add]

/-- ★ **the graded ADD law (strong form)**: `R_β(g + h) = R_β(g) + R_β(h)` whenever both
inputs have a common cleared `dv3Supp`-value `≥ β`. -/
theorem s2Mu4GradedRes_add_of_le {β : ℕ} {g h : Polynomial O}
    (hg : (β : ℕ∞)
        ≤ dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) g
            85 2)
    (hh : (β : ℕ∞)
        ≤ dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) h
            85 2) :
    s2Mu4GradedRes h2 hq β (g + h) = s2Mu4GradedRes h2 hq β g + s2Mu4GradedRes h2 hq β h := by
  refine Polynomial.ext fun t => ?_
  rw [Polynomial.coeff_add, s2Mu4GradedRes_coeff, s2Mu4GradedRes_coeff, s2Mu4GradedRes_coeff,
    s2Mu4Coeff_add h2 hq hg hh]

set_option linter.unusedVariables false in
/-- ★ **the graded ADD law** (published Cor 4.12(1), the `FGMNSourceLaws.graded_add`
binder pattern at the μ₄ occurrence, the `hgh` hypothesis carried for field-shape fidelity
only — `s2Mu4GradedRes_add_of_le` proves the law without it). -/
theorem s2Mu4GradedRes_add {β : ℕ} {g h : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) (hh : S2Mu4ExactGrade h2 hq β h)
    (hgh : S2Mu4ExactGrade h2 hq β (g + h)) :
    s2Mu4GradedRes h2 hq β (g + h) = s2Mu4GradedRes h2 hq β g + s2Mu4GradedRes h2 hq β h :=
  s2Mu4GradedRes_add_of_le h2 hq
    (le_of_eq ((S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp hg).symm)
    (le_of_eq ((S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp hh).symm)

/-! ## D3-09 — the μ₄ grade-sum arithmetic: parity, endpoint sums, carry

Mirror of `C132rp4`, one level up. The carry identity itself is `h`-independent (pure
`e = 2` arithmetic) and hence IDENTICAL to `C132rp3.s2Mu3Carry_parity`'s; it is reproved
standalone here per the corpus's private-copy convention (the same fact restated under the
μ₄ name so this row's later consumers need not reach back one campaign). -/

/-- ★ **the μ₄ carry exponent** (U14's `c`, COR412 §5): `(β%2)·(β'%2)` — `h`-independent,
hence the SAME formula as `C132rp4.s2Mu3Carry`. -/
def s2Mu4Carry (β β' : ℕ) : ℕ := β % 2 * (β' % 2)

theorem s2Mu4Carry_eq_zero_or_one (β β' : ℕ) :
    s2Mu4Carry β β' = 0 ∨ s2Mu4Carry β β' = 1 := by
  unfold s2Mu4Carry
  rcases Nat.mod_two_eq_zero_or_one β with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one β' with h' | h' <;> rw [h, h'] <;> omega

/-- ★ **U14's carry formula**, restated at the μ₄ name. -/
theorem s2Mu4Carry_parity (β β' : ℕ) :
    β % 2 + β' % 2 = (β + β') % 2 + 2 * s2Mu4Carry β β' := by
  unfold s2Mu4Carry
  rcases Nat.mod_two_eq_zero_or_one β with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one β' with h' | h' <;> rw [h, h'] <;> omega

/-- ★ **the abscissa endpoint sum**: the μ₄ analogue of `C132rp4.s2Mu3_abscissa_sum`. -/
theorem s2Mu4_abscissa_sum (β β' T t : ℕ) (ht : t ≤ T) :
    (β % 2 + 2 * t) + (β' % 2 + 2 * (T - t)) = (β + β') % 2 + 2 * (T + s2Mu4Carry β β') := by
  have hc := s2Mu4Carry_parity β β'
  omega

/-- ★ **the gate-level endpoint sum**, building on D3-06's `s2Mu4SlotOnGrade_parity`. -/
theorem s2Mu4SlotOnGrade_abscissa_sum {β s β' s' : ℕ} {g z : Polynomial O}
    (h : S2Mu4SlotOnGrade h2 hq β g s) (h' : S2Mu4SlotOnGrade h2 hq β' z s') :
    s + s' = (β + β') % 2 + 2 * (s / 2 + s' / 2 + s2Mu4Carry β β') := by
  have hpar : s % 2 = β % 2 := s2Mu4SlotOnGrade_parity h2 hq h
  have hpar' : s' % 2 = β' % 2 := s2Mu4SlotOnGrade_parity h2 hq h'
  have hc := s2Mu4Carry_parity β β'
  omega

/-- ★ **the `u`-value endpoint sum** (Definition 3.12's `u₄(α+β) = u₄(α)+u₄(β)+c·h₄` at
`h₄ = 85`), REUSING D3-06's `s2Mu4_def312_level4` twice. -/
theorem s2Mu4_def312_add (β β' : ℕ) (u s u' s' : ℤ)
    (h : u * 2 + s * 85 = (β : ℤ)) (hs0 : 0 ≤ s) (hs2 : s < 2)
    (h' : u' * 2 + s' * 85 = (β' : ℤ)) (hs0' : 0 ≤ s') (hs2' : s' < 2) :
    (u + u' + 85 * (s2Mu4Carry β β' : ℤ)) * 2 + ((((β + β') % 2 : ℕ) : ℤ)) * 85
      = ((β + β' : ℕ) : ℤ) := by
  have hβs : s = ((β % 2 : ℕ) : ℤ) := (s2Mu4_def312_level4 β u s h hs0 hs2).1
  have hβ's' : s' = ((β' % 2 : ℕ) : ℤ) := (s2Mu4_def312_level4 β' u' s' h' hs0' hs2').1
  have hc : ((β % 2 : ℕ) : ℤ) + ((β' % 2 : ℕ) : ℤ)
      = (((β + β') % 2 : ℕ) : ℤ) + 2 * ((s2Mu4Carry β β' : ℕ) : ℤ) := by
    exact_mod_cast s2Mu4Carry_parity β β'
  have hβadd : ((β + β' : ℕ) : ℤ) = (β : ℤ) + (β' : ℤ) := by push_cast; ring
  omega

end S2

end Uniformity.Density.Tower.C136d1

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C136d1.s2Hgt₄_one_eq_zero
#print axioms Uniformity.Density.Tower.C136d1.s2AddVal₄
#print axioms Uniformity.Density.Tower.C136d1.s2AddVal₄_apply
#print axioms Uniformity.Density.Tower.C136d1.S2Mu4ExactGrade
#print axioms Uniformity.Density.Tower.C136d1.S2Mu4AboveGrade
#print axioms Uniformity.Density.Tower.C136d1.S2Mu4ExactGrade_iff_dv3Supp
#print axioms Uniformity.Density.Tower.C136d1.S2Mu4AboveGrade_iff_dv3Supp
#print axioms Uniformity.Density.Tower.C136d1.S2Mu4ExactGrade_exists
#print axioms Uniformity.Density.Tower.C136d1.S2Mu4ExactGrade_unique
#print axioms Uniformity.Density.Tower.C136d1.S2Mu4ExactGrade_mul
#print axioms Uniformity.Density.Tower.C136d1.S2Mu4ExactGrade_not_above
#print axioms Uniformity.Density.Tower.C136d1.S2Mu4ExactGrade_not_zero
#print axioms Uniformity.Density.Tower.C136d1.S2Mu4ExactGrade_zero_false
#print axioms Uniformity.Density.Tower.C136d1.S2Mu4AboveGrade_zero
#print axioms Uniformity.Density.Tower.C136d1.S2Mu4ExactGrade_eq_addVal
#print axioms Uniformity.Density.Tower.C136d1.S2Mu4AboveGrade_eq_addVal
#print axioms Uniformity.Density.Tower.C136d1.tooth_g8
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4_def312_level4
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4_def312_level3
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4_def312_level3_exists
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4_bezout_level3
#print axioms Uniformity.Density.Tower.C136d1.S2Mu4SlotOnGrade
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4SlotOnGrade_iff
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4SlotOnGrade_iff_hgt₃
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4SlotOnGrade_parity
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4SlotOnGrade_inner_exact
#print axioms Uniformity.Density.Tower.C136d1.dv3Supp_le_of_mu4SlotOnGrade
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4EpsExp
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4EpsExp_eq
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4EpsOf
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4EpsOf_eq_one
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4Eps
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4Eps_eq_one
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4Eps_eq_epsOf
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4Eps_ne_zero
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4Coeff
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4Coeff_letter_display
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4Coeff_eq_eval
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4Coeff_eq_eval_normRes
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4Coeff_slot
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4Coeff_eq_zero_of_dv3Pin_top
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4Coeff_eq_zero_of_natDegree_lt
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4Coeff_eq_zero_of_grade_lt
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4Coeff_eq_zero_of_above
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4GradedRes
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4GradedRes_coeff
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4GradedRes_eq_sum_range
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4GradedRes_natDegree_le
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4GradedRes_coeff_eq_zero_of_natDegree_lt
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4GradedRes_zero_of_above
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4GradedRes_zero
#print axioms Uniformity.Density.Tower.C136d1.le_dv3Pin_of_le_dv3Supp
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4Coeff_eq_eval_of_le
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4Coeff_add
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4GradedRes_add_of_le
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4GradedRes_add
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4Carry
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4Carry_eq_zero_or_one
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4Carry_parity
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4_abscissa_sum
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4SlotOnGrade_abscissa_sum
#print axioms Uniformity.Density.Tower.C136d1.s2Mu4_def312_add

end AxCheck
