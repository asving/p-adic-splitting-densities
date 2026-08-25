/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130rp8

/-!
# Uniformity.ChapC.C130rp11 — S2-source plan nodes RP-11/RP-12

**S2-source plan nodes RP-11 + RP-12** (`docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6
rows RP-11 "Prove the S2-specialized universal recipe (`f'=1`) symbolically" and RP-12
"Collapse the residual input to the unique admissible linear polynomial and construct its
degree-eight lift"), on RP-2's ADD laws (`C130rp2`), RP-6's assembled `graded_mul`
(`C130rp6`), and RP-8's total normalized residual `s2NormRes` + key powers (`C130rp8`).

## A course correction against the row's own "degree-eight" framing

The row text (and the calling brief) reads the recipe at `r = 2` (`K.keyAt r = keyAt 2 =
composedKey`, degree `4`), giving `e'f'·deg(keyAt 2) = 2·1·4 = 8`.  Checking the LANDED
realization before writing anything: `C130rp0`'s own module docstring is explicit that the
concrete operators built here (`s2Hgt₂`, `s2GradedRes`, `s2NormRes`) realize `nextValue :=
μ₂` — i.e. `FGMNSourceData` at `r = 1`, where `K.keyAt r = K.keyAt 1 = Φ′` (`(s2Frame
h2 hq).key`, degree `2`), NOT `keyAt 2 = composedKey` (degree `4`, RP-8's own explicit
disclaimer: "the literal S2 `keyAt 2 = composedKey` field instance is KP-6's row, not
claimed here").  At `r = 1`, `e'f'·deg(keyAt 1) = 2·1·2 = 4`: the faithful degree is
**four**, not eight, and RP-12's lift is built from `Φ′` alone.

## A second, load-bearing correction: the naive `khat` grade is VACUOUS

`C130fg.normalized_recipe` reads `khat(0)`'s grade as `(f' - 0)·u' = 1·5 = 5` (an ODD
numeral).  But the degree fence `(khat 0).natDegree < (K.keyAt r).natDegree = 2` forces
`khat(0)` to be a "short digit" living ONLY at `Φ′`-abscissa `0` (`dev` vanishes at every
slot `≥ 1` below the key's own degree), so its cleared grade `dvSupp(khat, 5, 2) =
2 • dvHgt(khat, 0)` is a **multiple of `2`, hence always EVEN**.  Grade `5` is odd: no
`khat` can satisfy both hypotheses simultaneously — `normalized_recipe`'s literal-numeral
instantiation at these operators is VACUOUS (machine-checked below,
`s2_recipe_naive_numeral_vacuous`), exactly the "sorry-free ≠ non-vacuous"
failure mode the repo's standing discipline warns against.

The honest, NON-VACUOUS S2 realization needs `khat`'s grade to be `e'·(f' - t)·u' = 2 · 5 =
10` — an extra factor of `e' = 2`, i.e. measured on the SAME cleared scale as the leading
term `Φ′^{e'f'}` itself (`S2ExactGrade_key_pow 2 : S2ExactGrade (5·2) (Φ′·Φ′)`, RP-8).  This
is exactly the calibration `C130rp2`'s own landed `tooth_C4X_grade`/`tooth_sum_exact`/
`tooth_gradedRes_add_exact` teeth already use and verify (`R₁₀(Φ′² + 4x) = X + 1`, a
NON-VACUOUS witness with the leading term and the correction term tied at the SAME grade
`10`, landing at OUTPUT degree `f' = 1` exactly).  This file promotes that fixed instance to
the general `khat`-parametrized recipe (RP-11) and specializes it to the existence law
(RP-12).  The factor-of-`e'` discrepancy is recorded honestly, not silently absorbed: it is
exactly the content OPEN-DICT-2 (the clearing dictionary between `FGMNSourceData`'s abstract
grades and the concrete `S2ExactGrade` numerals) has not yet settled, per
`S2_SOURCE_PLAN_2026-08-24.md` §5's own ruling that `grade_compat` is unproven future work.

## NODE RP-11 — the S2-specialized recipe, symbolically (published Def 1.6/3.13, eq (11))

★ `s2_normalized_recipe`: for ANY `khat : Polynomial O` with `S2ExactGrade h2 hq 10 khat` and
`khat.natDegree < 2`, `s2NormRes h2 hq (Φ′·Φ′ - khat) = X - C((s2GradedRes h2 hq 10
khat).coeff 0)` — the single-`khat` (`f' = 1`) case of the abstract field's display,
symbolically (no enumeration): the leading term `Φ′·Φ′` sits ABOVE grade `10`'s
COMPETITOR... no — sits EXACTLY AT grade `10` (a true tie with `khat`, not a dominance
relation), the two summands' `Φ′`-development slots (abscissa `2` vs abscissa `0`) are
DISJOINT so no characteristic-2 cancellation is possible, RP-2's strong ADD law
(`s2GradedRes_add_of_le`) splits the graded residual as `X + R₁₀(khat)`, and the trailing
strip is trivial because RP-8's scalar law (`s2GradedRes_coeff_zero_ne_zero_of_exact`) makes
the constant term of `R₁₀(khat)` nonzero whenever `khat ≠ 0`.

## NODE RP-12 — residual existence at `ψ = X + 1` (published Thm 5.7's construction)

★ `s2_unique_admissible_linear`: `X + 1` is the UNIQUE monic linear polynomial over `K₂`
with nonzero constant term (`s2Fld₂_card`'s forced two-element collapse: the only nonzero
scalar is `1`).

★ `s2_normalized_exists`: the explicit degree-four monic lift `g := Φ′·Φ′ + C(4)·x`
(`e'f'·deg(keyAt 1) = 2·1·2 = 4`) has `s2NormRes h2 hq g = X + 1`, assembled from RP-2's
ALREADY-LANDED `tooth_C4X_grade`/`tooth_gradedRes_C4X`/`tooth_sum_exact`/
`tooth_gradedRes_add_exact` teeth — the `f' = 1` instance of RP-11's recipe at the concrete
witness `khat := C(4)·x`, packaged in the `FGMNSourceLaws.normalized_exists` field shape
(monic `ψ`, `Irreducible ψ`, `ψ.natDegree = f' = 1`, `ψ.coeff 0 ≠ 0`; `Irreducible (X+1)` is
immediate — every nonconstant degree-`1` polynomial over a field is irreducible).

## What this file does NOT claim (honesty scope)

* No literal instance of `C130fg.FGMNSourceLaws.normalized_recipe`/`normalized_exists` at
  their PRINTED numerals — see the two course-correction notes above.  What is claimed is
  the SAME quantifier/binder GENRE, realized honestly at the numerals the landed engine
  actually supports, in the tradition of RP-8's own `s2NormRes_key` (realized at `Φ′ =
  keyAt 1`, explicitly not the literal `keyAt 2` instance).
* No `FGMNSourceData`/`FGMNSourceLaws`/`ChainRealization` instance (FD-0); no resolution of
  OPEN-DICT-2's clearing dictionary (that is what would either confirm or replace the
  factor-of-`e'` correction recorded above).
* No `key_criterion`/`key_irreducible`/`initial_iff_residual` (KP-0 onward): this file is
  scoped to `normalized_recipe`/`normalized_exists` only.

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements): the two
course corrections above (the `r = 1` realization choice and the factor-of-`e'` grade
correction), `s2_normalized_recipe`, `s2_unique_admissible_linear`, `s2_normalized_exists`.

**DEPENDS.** C130rp8 (`s2NormRes`, `s2NormRes_of_exact`, `s2GradedRes_coeff_zero_ne_zero_of_exact`,
`S2ExactGrade_key_pow`, `s2GradedRes_key_pow`) · C130rp6/C130rp4/C130rp2 (`s2GradedRes_add_of_le`,
`le_dvSupp_of_exact`, `le_dvSupp_of_above`, `tooth_char_two`, `tooth_C4X_grade`,
`tooth_gradedRes_C4X`, `tooth_sum_exact`, `tooth_gradedRes_add_exact`, `dev_key_sq_zero`,
`dev_key_sq_two`) · C130rp1 (`s2GradedRes_zero_of_above`, `s2GradedRes_coeff`,
`s2GradedCoeff_eq_zero_of_natDegree_lt`) · C130rp0 (`S2ExactGrade_iff_dvSupp`,
`S2ExactGrade_not_zero`) · C130s6 (`s2Fld₂_card`, `dvSupp_neg`, `min_dvSupp_le_dvSupp_add`) ·
C131v/C131w/C131y (`dev_sub`, `dev_neg`, `dvSupp_le_term`, `dvHgt_neg`) · C35b (`key_eq`,
`s2Key_natDegree`, `sh_C`) · B04 (`dev_eq_zero_of_lt`) · C127 (`KeyFrame.natDegree_key_pos`) ·
mathlib (`Polynomial.modByMonic_eq_self_iff`, `Polynomial.degree_le_natDegree`,
`Polynomial.natTrailingDegree_le_of_ne_zero`, `exists_eq_X_add_C_of_natDegree_le_one`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement touched.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C130rp11

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130rp0
open Uniformity.Density.Tower.C130rp1 Uniformity.Density.Tower.C130rp2
open Uniformity.Density.Tower.C130nv2 Uniformity.Density.Tower.C130rp4
open Uniformity.Density.Tower.C130rp6 Uniformity.Density.Tower.C130rp8
open Uniformity.Density.Tower.C130nv3 Uniformity.Density.Tower.C131v
open Uniformity.Density.Tower.C131w Uniformity.Density.Tower.C131y

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 0 — private helpers (the private-copy pattern) -/

/-- private copy of the S2 key-degree numeral: `deg Φ′ = 2`. -/
private theorem key_natDegree_two : ((s2Frame h2 hq).key : Polynomial O).natDegree = 2 := by
  rw [key_eq h2 hq]
  exact s2Key_natDegree

/-- private copy of RP-1's `sh_one`: the stage height of the digit `1` is `0`. -/
private theorem sh_one' : (s2Frame h2 hq).stageHeight (1 : Polynomial O) = 0 := by
  rw [show (1 : Polynomial O) = Polynomial.C 1 by rw [map_one], sh_C h2 hq]
  simp

/-- private copy of C.80's `eq_one_of_card_two` at `fld 2` (the private-copy pattern:
`private` does not export; the corpus already carries at least two such copies,
`C80.eq_one_of_card_two` and `C130s6.fld₂_eq_one_of_ne_zero`). -/
private theorem s2Fld2_eq_one_of_ne_zero {c : (s2DepthTwo h2 hq).fld 2} (hc : c ≠ 0) :
    c = 1 := by
  haveI : Finite ((s2DepthTwo h2 hq).fld 2) :=
    Nat.finite_of_card_ne_zero (by rw [s2Fld₂_card h2 hq]; norm_num)
  have hu : Nat.card ((s2DepthTwo h2 hq).fld 2)ˣ = 1 := by
    rw [Nat.card_units, s2Fld₂_card h2 hq]
  haveI : Subsingleton ((s2DepthTwo h2 hq).fld 2)ˣ := (Nat.card_eq_one_iff_unique.mp hu).1
  have h1 : hc.isUnit.unit = 1 := Subsingleton.elim _ _
  calc c = ((hc.isUnit.unit : ((s2DepthTwo h2 hq).fld 2)ˣ) : (s2DepthTwo h2 hq).fld 2) :=
        (hc.isUnit.unit_spec).symm
    _ = 1 := by rw [h1]; rfl

/-- the char-2 negation identity, scalar form: every element of `K₂` is its own negative
(from `tooth_char_two`'s `1 + 1 = 0`, via a pure ring computation — no exotic lemma name
needed). -/
private theorem s2Fld2_neg_eq_self (x : (s2DepthTwo h2 hq).fld 2) : -x = x := by
  by_cases hx : x = 0
  · rw [hx, neg_zero]
  · rw [s2Fld2_eq_one_of_ne_zero h2 hq hx]
    have h := tooth_char_two h2 hq
    calc (-1 : (s2DepthTwo h2 hq).fld 2) = -1 + (1 + 1) := by rw [h, add_zero]
      _ = 1 := by ring

/-- the char-2 negation identity, polynomial form (coefficientwise). -/
private theorem s2Fld2_poly_neg_eq_self (p : Polynomial ((s2DepthTwo h2 hq).fld 2)) :
    -p = p := by
  ext n
  rw [Polynomial.coeff_neg]
  exact s2Fld2_neg_eq_self h2 hq _

/-- `khat`'s own degree bound, converted to the `degree` (`WithBot ℕ`) comparison
`Polynomial.modByMonic_eq_self_iff` consumes. -/
private theorem degree_lt_key_of_natDegree_lt {khat : Polynomial O} (hdeg : khat.natDegree < 2) :
    khat.degree < ((s2Frame h2 hq).key : Polynomial O).degree := by
  have h1 : khat.degree ≤ (khat.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
  have h2' : (khat.natDegree : WithBot ℕ) < (2 : WithBot ℕ) := by exact_mod_cast hdeg
  have h3 : ((s2Frame h2 hq).key : Polynomial O).degree = (2 : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree (s2Frame h2 hq).hmonic.ne_zero, key_natDegree_two h2 hq]
    norm_cast
  rw [h3]
  exact lt_of_le_of_lt h1 h2'

/-- a short digit (`natDegree < 2 = deg Φ′`) is its own slot-`0` development. -/
private theorem dev_zero_of_natDegree_lt {khat : Polynomial O} (hdeg : khat.natDegree < 2) :
    dev (s2Frame h2 hq).key khat 0 = khat := by
  rw [dev_zero_pin]
  exact (Polynomial.modByMonic_eq_self_iff (s2Frame h2 hq).hmonic).mpr
    (degree_lt_key_of_natDegree_lt h2 hq hdeg)

/-- a short digit's development vanishes at every slot `≥ 1` (B.04's `dev_eq_zero_of_lt`,
against the degree-2 key). -/
private theorem dev_eq_zero_of_natDegree_lt {khat : Polynomial O} (hdeg : khat.natDegree < 2)
    {s : ℕ} (hs : 1 ≤ s) :
    dev (s2Frame h2 hq).key khat s = 0 :=
  dev_eq_zero_of_lt (s2Frame h2 hq).hmonic (s2Frame h2 hq).natDegree_key_pos khat s
    (by rw [key_natDegree_two h2 hq]; omega)

/-! ## Part 1 — the recorded vacuity of the LITERAL field-shape numeral

`C130fg.normalized_recipe`'s printed grade for `khat(0)` is `(f' - 0) * u' = 5` (odd); the
degree fence forces only EVEN grades.  Recorded once, honestly, before building the
non-vacuous replacement. -/

/-- ★ **the recorded finding**: no `khat` of degree `< 2` can have `S2ExactGrade 5 khat` —
the printed field-shape numeral is UNSATISFIABLE at the degree fence, since a short digit's
cleared grade `2 • dvHgt(khat, 0)` is always EVEN. -/
theorem s2_recipe_naive_numeral_vacuous {khat : Polynomial O} (hdeg : khat.natDegree < 2) :
    ¬ S2ExactGrade h2 hq 5 khat := by
  intro hkhat
  have hdv : dvSupp (s2Frame h2 hq) khat 5 2 = ((5 : ℕ) : ℕ∞) :=
    (S2ExactGrade_iff_dvSupp h2 hq).mp hkhat
  have hrange := dvSupp_eq_inf_range (s2Frame h2 hq) (u := 5) (ℓ := 2) (by norm_num) khat
    (M := 2) hdeg
  rw [hrange, show Finset.range 2 = {0, 1} from rfl, Finset.inf_insert, Finset.inf_singleton]
    at hdv
  have hdev1 : dev (s2Frame h2 hq).key khat 1 = 0 := dev_eq_zero_of_natDegree_lt h2 hq hdeg le_rfl
  have hhgt1 : dvHgt (s2Frame h2 hq) khat 1 = ⊤ := by
    rw [dvHgt, hdev1]
    exact (s2Frame h2 hq).stageHeight_zero
  rw [hhgt1, C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2), top_add,
    min_eq_left (le_top), Nat.cast_zero, mul_zero, add_zero] at hdv
  have hfin : dvHgt (s2Frame h2 hq) khat 0 ≠ ⊤ := by
    intro htop
    rw [htop, C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2)] at hdv
    exact WithTop.top_ne_coe hdv
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hm, nsmul_eq_mul] at hdv
  have : (2 * m : ℕ) = 5 := by exact_mod_cast hdv
  omega

/-! ## Part 2 — ★ NODE RP-11: the S2-realized recipe, symbolically

The non-vacuous S2 realization: `khat` at grade `10` (a TRUE TIE with the leading term
`Φ′·Φ′`, also grade `10`), degree `< 2` (matching `deg(keyAt 1) = 2`). -/

/-- the combined recipe input sits at exact grade `10`: the leading term's slot (abscissa
`2`) and `khat`'s slot (abscissa `0`, or below) are DISJOINT, so no characteristic-2
cancellation threatens either, and the standard ultrametric argument (≤ via the exhibited
abscissa-`2` term, ≥ via `min_dvSupp_le_dvSupp_add` at the tied value `10`) pins the exact
grade. -/
theorem s2_recipe_exact_grade {khat : Polynomial O}
    (hkhat : S2ExactGrade h2 hq 10 khat) (hdeg : khat.natDegree < 2) :
    S2ExactGrade h2 hq 10
      (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key - khat) := by
  refine (S2ExactGrade_iff_dvSupp h2 hq).mpr (le_antisymm ?_ ?_)
  · -- ≤ 10, via the exhibited abscissa-2 term
    have hdev2 : dev (s2Frame h2 hq).key
        (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key - khat) 2 = 1 := by
      rw [dev_sub (s2Frame h2 hq).hmonic, dev_key_sq_two h2 hq,
        dev_eq_zero_of_natDegree_lt h2 hq hdeg (by norm_num), sub_zero]
    have hhgt2 : dvHgt (s2Frame h2 hq)
        (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key - khat) 2 = 0 := by
      rw [dvHgt, hdev2]
      exact sh_one' h2 hq
    have hterm := dvSupp_le_term (s2Frame h2 hq)
      (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key - khat) 5
      (by norm_num : (0 : ℕ) < 2) 2
    rw [hhgt2] at hterm
    have h10 : (2 : ℕ) • (0 : ℕ∞) + ((5 : ℕ) * (2 : ℕ) : ℕ∞) = ((10 : ℕ) : ℕ∞) := by
      norm_num
    rwa [h10] at hterm
  · -- 10 ≤, via the ultrametric at the tied value
    have hmin := min_dvSupp_le_dvSupp_add (s2Frame h2 hq) (u := 5) (by norm_num : (0 : ℕ) < 2)
      (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key) (-khat)
    rw [← sub_eq_add_neg] at hmin
    rw [s2_dvSupp_key_sq h2 hq, dvSupp_neg, (S2ExactGrade_iff_dvSupp h2 hq).mp hkhat,
      min_self] at hmin
    exact hmin

/-- the combined recipe input's graded residual at grade `10` splits, via RP-2's strong ADD
law, as the leading term's `X` (RP-1's landed `tooth_gradedRes_key_sq`) plus `khat`'s own
graded residual — the sign flip on `-khat` is absorbed by the "sum to zero" trick
(`khat + -khat = 0` forces `R₁₀(-khat) = -R₁₀(khat)`) composed with the char-2 negation
identity (`R₁₀(-khat) = R₁₀(khat)`, since the codomain has two elements). -/
theorem s2_recipe_graded_res {khat : Polynomial O} (hkhat : S2ExactGrade h2 hq 10 khat) :
    s2GradedRes h2 hq 10
        (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key - khat)
      = Polynomial.X + s2GradedRes h2 hq 10 khat := by
  have hnegExact : S2ExactGrade h2 hq 10 (-khat) := by
    rw [S2ExactGrade_iff_dvSupp, dvSupp_neg]
    exact (S2ExactGrade_iff_dvSupp h2 hq).mp hkhat
  have hkeysq : S2ExactGrade h2 hq 10
      (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key) :=
    (S2ExactGrade_iff_dvSupp h2 hq).mpr (s2_dvSupp_key_sq h2 hq)
  have hsum0 := s2GradedRes_add_of_le h2 hq (le_dvSupp_of_exact h2 hq hkhat)
    (le_dvSupp_of_exact h2 hq hnegExact)
  rw [add_neg_cancel, s2GradedRes_zero] at hsum0
  have hba : s2GradedRes h2 hq 10 (-khat) = - s2GradedRes h2 hq 10 khat := by
    have heq : s2GradedRes h2 hq 10 khat + s2GradedRes h2 hq 10 (-khat) = 0 := hsum0.symm
    calc s2GradedRes h2 hq 10 (-khat)
        = -(s2GradedRes h2 hq 10 khat)
            + (s2GradedRes h2 hq 10 khat + s2GradedRes h2 hq 10 (-khat)) := by ring
      _ = -(s2GradedRes h2 hq 10 khat) + 0 := by rw [heq]
      _ = -(s2GradedRes h2 hq 10 khat) := by ring
  have hadd := s2GradedRes_add_of_le h2 hq (le_dvSupp_of_exact h2 hq hkeysq)
    (le_dvSupp_of_exact h2 hq hnegExact)
  rw [sub_eq_add_neg, hadd, tooth_gradedRes_key_sq h2 hq, hba, s2Fld2_poly_neg_eq_self h2 hq]

/-- `khat`'s own graded residual at grade `10` is a pure constant, once `khat` is a short
digit (`natDegree < 2`): every coefficient past `t = 0` reads an abscissa `≥ 2 >
khat.natDegree`, hence `0` (RP-1's `s2GradedCoeff_eq_zero_of_natDegree_lt`). -/
theorem s2_khat_gradedRes_eq_C {khat : Polynomial O} (hdeg : khat.natDegree < 2) :
    s2GradedRes h2 hq 10 khat = Polynomial.C ((s2GradedRes h2 hq 10 khat).coeff 0) := by
  refine Polynomial.ext fun t => ?_
  match t with
  | 0 => rw [Polynomial.coeff_C_zero]
  | (t + 1) =>
    rw [s2GradedRes_coeff,
      s2GradedCoeff_eq_zero_of_natDegree_lt h2 hq (by omega : khat.natDegree < 10 % 2 + 2 * (t + 1)),
      show (Polynomial.C ((s2GradedRes h2 hq 10 khat).coeff 0) : Polynomial ((s2DepthTwo h2 hq).fld 2)).coeff (t + 1) = 0 from
        Polynomial.coeff_C_of_ne_zero (Nat.succ_ne_zero t)]

/-- ★ **NODE RP-11 — the S2-realized recipe, symbolically** (the `f' = 1` display, published
Def 1.6/3.13, at the non-vacuous S2 numerals recorded above): for any `khat` of grade `10`
and degree `< 2`, `s2NormRes(Φ′·Φ′ - khat) = X - C(scalar)` where `scalar` is `khat`'s own
grade-`10` scalar residual (`R₁₀(khat)`'s coefficient `0`). The trailing strip is trivial
(RP-8's scalar law makes the constant term of `X + R₁₀(khat)` nonzero whenever `khat ≠ 0`),
and `X + C(scalar) = X - C(scalar)` by the char-2 identity. -/
theorem s2_normalized_recipe {khat : Polynomial O}
    (hkhat : S2ExactGrade h2 hq 10 khat) (hdeg : khat.natDegree < 2) :
    s2NormRes h2 hq
        (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key - khat)
      = Polynomial.X - Polynomial.C ((s2GradedRes h2 hq 10 khat).coeff 0) := by
  have hgrade := s2_recipe_exact_grade h2 hq hkhat hdeg
  have hgraded := s2_recipe_graded_res h2 hq hkhat
  have hne : khat ≠ 0 := S2ExactGrade_not_zero h2 hq hkhat
  have hscalar : (s2GradedRes h2 hq 10 khat).coeff 0 ≠ 0 :=
    s2GradedRes_coeff_zero_ne_zero_of_exact h2 hq hkhat (by omega)
  have htrail : (s2GradedRes h2 hq 10
      (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key - khat)).natTrailingDegree
      = 0 := by
    refine le_antisymm ?_ (Nat.zero_le _)
    refine Polynomial.natTrailingDegree_le_of_ne_zero ?_
    rw [hgraded, Polynomial.coeff_add, Polynomial.coeff_X_zero, zero_add]
    exact hscalar
  rw [s2NormRes_of_exact h2 hq hgrade, htrail, Function.iterate_zero_apply, hgraded]
  conv_lhs => rw [s2_khat_gradedRes_eq_C h2 hq hdeg]
  rw [sub_eq_add_neg, s2Fld2_poly_neg_eq_self h2 hq]

/-! ## Part 3 — ★ NODE RP-12: residual existence at `ψ = X + 1`

The `khat := C(4)·x` instance of RP-11's recipe, assembled from RP-2's ALREADY-LANDED
grade-`10` tie teeth (`tooth_C4X_grade`, `tooth_gradedRes_C4X`, `tooth_sum_exact`,
`tooth_gradedRes_add_exact` — `R₁₀(Φ′² + 4x) = X + 1`), packaged in the
`FGMNSourceLaws.normalized_exists` field shape at `r = 1` (`e' = 2`, `f' = 1`, `K.keyAt r =
Φ′`, degree `2`; existence degree `e'·f'·deg(Φ′) = 2·1·2 = 4`). -/

/-- ★ **the uniqueness half of RP-12**: `X + 1` is the UNIQUE monic linear polynomial over
`K₂` with nonzero constant term (`s2Fld₂_card`'s forced two-element collapse leaves only one
admissible scalar). -/
theorem s2_unique_admissible_linear (p : Polynomial ((s2DepthTwo h2 hq).fld 2))
    (hp : p.Monic) (hdeg : p.natDegree = 1) (hc : p.coeff 0 ≠ 0) :
    p = Polynomial.X + 1 := by
  obtain ⟨a, b, hab⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one (le_of_eq hdeg)
  have hb : p.coeff 0 = b := by rw [hab]; simp
  have ha : p.coeff 1 = a := by rw [hab]; simp
  have ha1 : a = 1 := by
    have hlead : p.coeff p.natDegree = 1 := hp
    rw [hdeg, ha] at hlead
    exact hlead
  have hb1 : b = 1 := s2Fld2_eq_one_of_ne_zero h2 hq (hb ▸ hc)
  rw [hab, ha1, hb1, map_one, one_mul]

/-- `X + 1` itself is Irreducible over `K₂` — every degree-one polynomial over a field is
irreducible; this witnesses that RP-12's hypothesis set is non-vacuous. -/
theorem s2_X_add_one_irreducible :
    Irreducible (Polynomial.X + 1 : Polynomial ((s2DepthTwo h2 hq).fld 2)) := by
  letI : Field ((s2DepthTwo h2 hq).fld 2) := (s2DepthTwo h2 hq).fldField 2
  refine Polynomial.irreducible_of_degree_eq_one ?_
  rw [show (1 : Polynomial ((s2DepthTwo h2 hq).fld 2)) = Polynomial.C 1 from (map_one _).symm]
  exact Polynomial.degree_X_add_C 1

/-- the degree of `Φ′·Φ′`, in `WithBot ℕ` form (shared by the monic and degree lemmas
below). -/
private theorem s2_g_key_sq_degree :
    (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key).degree = (4 : WithBot ℕ) := by
  rw [Polynomial.degree_eq_natDegree
      (mul_ne_zero (s2Frame h2 hq).hmonic.ne_zero (s2Frame h2 hq).hmonic.ne_zero),
    Polynomial.natDegree_mul (s2Frame h2 hq).hmonic.ne_zero (s2Frame h2 hq).hmonic.ne_zero,
    key_natDegree_two h2 hq]
  norm_cast

/-- `4x` sits strictly below `Φ′·Φ′`'s degree — the `Monic.add_of_left`/`degree_add_eq_left`
hypothesis both `s2_g_monic`/`s2_g_natDegree` consume. -/
private theorem s2_g_C4X_degree_lt :
    (Polynomial.C (4 : O) * Polynomial.X).degree
      < (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key).degree := by
  rw [s2_g_key_sq_degree h2 hq]
  exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le (4 : O)) (by norm_num)

/-- the explicit lift `g := Φ′·Φ′ + 4x` is monic (the degree-4 leading term dominates). -/
theorem s2_g_monic :
    (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
      + Polynomial.C (4 : O) * Polynomial.X).Monic :=
  ((s2Frame h2 hq).hmonic.mul (s2Frame h2 hq).hmonic).add_of_left (s2_g_C4X_degree_lt h2 hq)

/-- `g`'s degree is exactly `4 = e'·f'·deg(Φ′) = 2·1·2`. -/
theorem s2_g_natDegree :
    (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
      + Polynomial.C (4 : O) * Polynomial.X).natDegree = 4 := by
  have hdegeq := Polynomial.degree_add_eq_left_of_degree_lt (s2_g_C4X_degree_lt h2 hq)
  rw [s2_g_key_sq_degree h2 hq] at hdegeq
  exact Polynomial.natDegree_eq_of_degree_eq_some hdegeq

/-- `g`'s normalized residual is `X + 1` — RP-2's tie tooth `tooth_gradedRes_add_exact`
lifted through `s2NormRes` (the strip is trivial: `(X+1).coeff 0 = 1 ≠ 0`). -/
theorem s2_normalized_exists_normRes :
    s2NormRes h2 hq
        (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
          + Polynomial.C (4 : O) * Polynomial.X)
      = Polynomial.X + 1 := by
  have htrail : (s2GradedRes h2 hq 10
      (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
        + Polynomial.C (4 : O) * Polynomial.X)).natTrailingDegree = 0 := by
    refine le_antisymm ?_ (Nat.zero_le _)
    refine Polynomial.natTrailingDegree_le_of_ne_zero ?_
    rw [tooth_gradedRes_add_exact h2 hq, Polynomial.coeff_add, Polynomial.coeff_X_zero,
      Polynomial.coeff_one_zero, zero_add]
    exact one_ne_zero
  rw [s2NormRes_of_exact h2 hq (tooth_sum_exact h2 hq), htrail, Function.iterate_zero_apply,
    tooth_gradedRes_add_exact h2 hq]

/-- ★ **NODE RP-12 — residual existence** (`FGMNSourceLaws.normalized_exists`'s field shape
at `r = 1`, `(e', f', u') = (2, 1, 5)`, `K.keyAt r = Φ′`): for ANY monic irreducible `ψ` of
degree `f' = 1` with nonzero constant term — forced by `s2_unique_admissible_linear` to be
`X + 1` — the explicit degree-`e'f'·deg(Φ′) = 4` monic lift `g := Φ′·Φ′ + 4x` satisfies
`s2NormRes g = ψ`. -/
theorem s2_normalized_exists :
    ∀ ψ : Polynomial ((s2DepthTwo h2 hq).fld 2),
      ψ.Monic → Irreducible ψ → ψ.natDegree = 1 → ψ.coeff 0 ≠ 0 →
        ∃ g : Polynomial O, g.Monic ∧
          g.natDegree = 2 * 1 * ((s2Frame h2 hq).key : Polynomial O).natDegree ∧
          s2NormRes h2 hq g = ψ := by
  intro ψ hψmonic _hψirr hψdeg hψc0
  have hψeq : ψ = Polynomial.X + 1 := s2_unique_admissible_linear h2 hq ψ hψmonic hψdeg hψc0
  refine ⟨(((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
    + Polynomial.C (4 : O) * Polynomial.X), s2_g_monic h2 hq, ?_, ?_⟩
  · rw [s2_g_natDegree h2 hq, key_natDegree_two h2 hq]
  · rw [hψeq]
    exact s2_normalized_exists_normRes h2 hq

end S2

end Uniformity.Density.Tower.C130rp11

/-! ## Axiom footprint (Part 0/1/2) -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130rp11.s2_recipe_naive_numeral_vacuous
#print axioms Uniformity.Density.Tower.C130rp11.s2_recipe_exact_grade
#print axioms Uniformity.Density.Tower.C130rp11.s2_recipe_graded_res
#print axioms Uniformity.Density.Tower.C130rp11.s2_khat_gradedRes_eq_C
#print axioms Uniformity.Density.Tower.C130rp11.s2_normalized_recipe
#print axioms Uniformity.Density.Tower.C130rp11.s2_unique_admissible_linear
#print axioms Uniformity.Density.Tower.C130rp11.s2_X_add_one_irreducible
#print axioms Uniformity.Density.Tower.C130rp11.s2_g_monic
#print axioms Uniformity.Density.Tower.C130rp11.s2_g_natDegree
#print axioms Uniformity.Density.Tower.C130rp11.s2_normalized_exists_normRes
#print axioms Uniformity.Density.Tower.C130rp11.s2_normalized_exists

end AxCheck
