/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130kp1

/-!
# Uniformity.ChapC.C130kp3 — S2-source plan nodes KP-3/KP-4 — key_criterion CLOSED

**S2-source plan nodes KP-3 + KP-4** (`docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6
rows KP-3 "Prove μ-minimality at the recipe degree" and KP-4 "Assemble the literal frontier
field"), CORES 3–4 of 4 of the `key_criterion` inductive core — on KP-0's predicates
(C130kp0), KP-1/KP-2's translation + primality (C130kp1), and RP-12's landed degree-four
lift (C130rp11).  This CLOSES the fourth inductive core.

## NODE KP-3 — μ-minimality at the recipe degree (the honest hypothesis set)

The row reads "every monic g of degree 4 with exact-grade/irreducible-residual data"; the
proof forces LESS.  The engine is KP-1's forward translation composed with KP-1's Part-2
degree law:

* ★ `s2MuMinimal_of_not_isUnit_normRes` — the honest set: `0 < deg g ≤ 4` and `R₃(g)` NOT a
  unit suffice (NO monicity, NO grade data).  Any nonzero `f` of degree `< deg g ≤ 4` has a
  UNIT normalized residual (`s2NormRes_isUnit_of_natDegree_lt_four`: slots `{0,1}` + parity
  make the graded residual a nonzero constant), so `g ∣µ₂ f` would push forward
  (`normRes_dvd_of_S2MuDvd`, universal) to the non-unit `R₃(g)` dividing a unit.  This is
  the recipe-degree analogue of KP-0's `s2MuMinimal_key` with the residual test replacing
  the odd-carry engine: at `Φ′` the residual is the unit `1` and the engine had to fire on
  the grade line; at the recipe degree the residual itself is the obstruction.
* ★ `s2MuMinimal_of_irreducible_normRes` — the row form at the recipe degree
  `4 = e'f'·deg Φ′`: irreducible residual (never a unit) gives μ₂-minimality.

**The honest fences, machine-witnessed (the degree-4 trichotomy).**  The `¬ IsUnit`
hypothesis is what the METHOD needs; at degree 4 it is sufficient but NOT necessary, and
naked degree-4 minimality is FALSE:

* ★ `tooth_kp3_needs_nonunit` — the refuter: `Φ′² + Φ′` is monic of degree `4` with UNIT
  residual (`R₃ = 1`, since `Φ′² + Φ′ ∼µ₂ Φ′` — the `Φ′²` perturbation sits at value
  `10 > 5`) yet is NOT μ₂-minimal: it μ₂-divides the degree-TWO `Φ′` outright (cofactor
  `1`).  So "monic + degree 4 → μ₂-minimal" is false, and KP-3's residual hypothesis is not
  decorative.
* `not_S2MuDvd_of_gradedRes_coeff_zero` — the SECOND minimality mechanism (the trailing
  `y`-power): a `φ` whose top-grade residual has ZERO scalar cannot μ₂-divide any nonzero
  `f` of degree `< 4` — RP-4's twisted product law keeps the scalar of every `R(φ·q)` at
  `0`, while the low-degree `f` has NONZERO residual scalar (RP-7's worker).  (KP-0's
  odd-carry engine is the `φ = Φ′` shadow of this mechanism.)
* `s2MuMinimal_key_sq` — by that mechanism `Φ′²` (unit residual `R₃(Φ′²) = 1`, but scalar
  `0` at grade 10: `R₁₀(Φ′²) = X`) IS μ₂-minimal: unit-residual degree-4 inputs can go
  either way, so `¬ IsUnit` is sufficient-not-necessary.
* `tooth_key_sq_not_muIrreducible` — yet `Φ′²` is NOT μ₂-irreducible (`Φ′² ∣µ₂ Φ′·Φ′` but
  `Φ′² ∤µ₂ Φ′` — the same scalar-death mechanism): μ₂-minimal does not give key-polynomial,
  so `key_criterion`'s Irreducible hypothesis is not decorative either.

## NODE KP-4 — the literal frontier field, assembled (`key_criterion` CLOSED)

* ★★ `s2_key_criterion` — the C130fg `FGMNSourceLaws.key_criterion` / A-C.11
  `FGMNCalculus.KP_criterion` hypothesis list at the landed `r = 1` anchoring
  (`(e', f') = (2, 1)`, `keyAt 1 = Φ′`, recipe degree `2·1·deg Φ′ = 4`): monic + degree +
  `Irreducible (R₃ g)` + `deg R₃(g) = 1` + `(R₃ g)(0) ≠ 0` → `S2KeyPoly g` (published
  Lemma 5.2(2) + Corollary 4.9 + the Theorem 5.7 degree display).  Monic is the frame's,
  μ₂-minimality is KP-3's, μ₂-irreducibility is KP-2's consumable
  (`s2_key_criterion_muIrreducible`).
* ★★ **the crown corollary** `s2KeyPoly_lift`: RP-12's landed degree-four lift `Φ′² + 4x`
  IS a key polynomial for μ₂ — the constructed witness the whole RP/KP chain aims at
  (published Theorem 5.7's construction, machine-closed end to end: RP-11/RP-12 produce
  the lift with residual `X + 1`, KP-2 makes its initial form prime, KP-3 makes it
  μ₂-minimal).  Spelled at the explicit polynomial `(x² − 2)² + 4x` too
  (`s2KeyPoly_lift_spelled`).
* ★ **the FD-0 pin** (`s2_key_criterion_fills`): for ANY
  `S : FGMNSourceData (s2DepthTwo h2 hq) K 2 1 5` reading
  `normalizedResidual := s2NormRes` and `keyPolynomial := S2KeyPoly`, the `key_criterion`
  field shape holds with the key read at the chain's OWN `K.keyAt 1` (= `Φ′` by the chain
  law `keyAt_one`) — zero residual assembly work at FD-0 for this field at the landed
  anchoring.

## The anchoring note (the standing RP-11 course correction, applied)

Per C130rp11's recorded course correction, the landed operators realize
`FGMNSourceData.nextValue := μ₂` at `r = 1` (`keyAt 1 = Φ′`, degree 2, recipe degree
`2·1·2 = 4`) — NOT the s2 tower's own depth `r = 2` (`keyAt 2 = composedKey`, degree 4,
which would print the recipe degree `2·1·4 = 8`).  The FD-0 pin therefore reads its degree
binder at `K.keyAt 1`, exactly like RP-8's `s2NormRes_key` realization choice; the literal
`keyAt 2` numeral is KP-6's row and is NOT claimed (KP-3's method stops at degree 4: above
it, low-degree cofactors no longer have unit residuals).

## What this node does NOT claim (honesty scope)

* No literal `keyAt 2 = composedKey` field instance (KP-6) and no `FGMNSourceData`/
  `FGMNSourceLaws`/`ChainRealization` INSTANCE (FD-0 assembles later; the `_fills` pin is
  conditional on the record's operator fields, like RP-6/RP-7/RP-10's pins).
* No `initial_iff_residual` (KP-7..KP-9), no `key_irreducible` (KP-5's row).
* No μ₂-minimality above degree 4 — `tooth_kp3_needs_nonunit` shows even AT degree 4 the
  naked statement fails, and the KP-1 backward fences (degree ≤ 4) bound the method.

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements): KP-3's
statement and its honest hypothesis set (`s2MuMinimal_of_not_isUnit_normRes`), the
trichotomy teeth (`tooth_kp3_needs_nonunit`, `s2MuMinimal_key_sq`,
`tooth_key_sq_not_muIrreducible`), the assembled criterion (`s2_key_criterion`), the crown
(`s2KeyPoly_lift`), and the FD-0 pin's `keyAt 1` anchoring (`s2_key_criterion_fills`).

**DEPENDS.** C130kp1 (`normRes_dvd_of_S2MuDvd`, `s2NormRes_isUnit_of_natDegree_lt_four`,
`s2_key_criterion_muIrreducible`) · C130kp0 (the predicates, `S2InitialEquiv_symm`,
`S2InitialEquiv_zero_right`, `S2ExactGrade_of_initialEquiv`, `S2InitialEquiv_iff_gradedRes`,
`s2NormRes_eq_of_initialEquiv`, `S2MuDvd_self`) · C130rp11 (`s2_g_monic`, `s2_g_natDegree`,
`s2_normalized_exists_normRes`, `s2_X_add_one_irreducible`) · C130rp8 (`s2GradeOf` bank,
`s2NormRes_key`, `s2GradedRes_coeff_zero_ne_zero_of_exact`, `tooth_key_sq_natDegree`,
`tooth_scalar_fence_sharp`) · C130rp4 (`s2GradedRes_mul_of_exact`) · C130rp0
(`S2ExactGrade_mul`, `tooth_key`, `tooth_key_sq`) · C130s6 (`s2Hgt₂_add_eq`) · C130fg/C130k
(`FGMNSourceData`, `KeyChain.keyAt_one`) · C35b/C97 (`key_eq`, `s2Key_natDegree`) · mathlib
(`isUnit_of_dvd_unit`, `natDegree_X_add_C`, `degree_add_eq_left_of_degree_lt`,
`natDegree_eq_of_degree_eq_some`, `mul_coeff_zero`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement touched.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C130kp3

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130nv
open Uniformity.Density.Tower.C130rp0 Uniformity.Density.Tower.C130rp1
open Uniformity.Density.Tower.C130rp2 Uniformity.Density.Tower.C130rp4
open Uniformity.Density.Tower.C130rp6 Uniformity.Density.Tower.C130rp8
open Uniformity.Density.Tower.C130rp9 Uniformity.Density.Tower.C130rp11
open Uniformity.Density.Tower.C130kp0 Uniformity.Density.Tower.C130kp1

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 0 — private copies (the private-copy pattern) -/

/-- private copy of the S2 key-degree numeral: `deg Φ′ = 2`. -/
private theorem key_natDegree_two : ((s2Frame h2 hq).key : Polynomial O).natDegree = 2 := by
  rw [key_eq h2 hq]
  exact s2Key_natDegree

/-- private copy: `Φ′`'s `degree` (`WithBot ℕ` form). -/
private theorem key_degree_withBot :
    ((s2Frame h2 hq).key : Polynomial O).degree = (2 : WithBot ℕ) := by
  rw [Polynomial.degree_eq_natDegree (s2Frame h2 hq).hmonic.ne_zero, key_natDegree_two h2 hq]
  norm_cast

/-- private copy: `Φ′·Φ′`'s `degree` (`WithBot ℕ` form; RP-11's private
`s2_g_key_sq_degree`, re-derived through RP-8's public `tooth_key_sq_natDegree`). -/
private theorem key_sq_degree_withBot :
    (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key).degree = (4 : WithBot ℕ) := by
  rw [Polynomial.degree_eq_natDegree
      (mul_ne_zero (s2Frame h2 hq).hmonic.ne_zero (s2Frame h2 hq).hmonic.ne_zero),
    tooth_key_sq_natDegree h2 hq]
  norm_cast

/-- private copy: `Φ′²`'s top-grade residual has ZERO scalar (`R₁₀(Φ′²) = X`; RP-8's sharp
fence `tooth_scalar_fence_sharp`, re-keyed at the canonical grade extraction). -/
private theorem key_sq_scalar_zero :
    (s2GradedRes h2 hq
        (s2GradeOf h2 hq (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key))
        (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key)).coeff 0 = 0 := by
  rw [s2GradeOf_eq_of_exact h2 hq (tooth_key_sq h2 hq)]
  exact tooth_scalar_fence_sharp h2 hq

/-! ## Part 1 — ★ NODE KP-3: μ-minimality at the recipe degree

The honest hypothesis set the proof forces: `0 < deg g ≤ 4` and a NON-UNIT residual — no
monicity, no grade data.  The mechanism: any candidate dividend `f` (nonzero, degree
`< deg g ≤ 4`) has a UNIT residual (KP-1's degree law), and KP-1's UNIVERSAL forward
translation would make the non-unit `R₃(g)` divide it. -/

/-- ★ **NODE KP-3, the engine (the honest hypothesis set)**: `0 < deg g ≤ 4` and `R₃(g)`
NOT a unit make `g` μ₂-minimal — every nonzero `f` of smaller degree has a UNIT normalized
residual (`s2NormRes_isUnit_of_natDegree_lt_four`), so `g ∣µ₂ f` would push forward
(`normRes_dvd_of_S2MuDvd`) to the non-unit `R₃(g)` dividing a unit.  (The recipe-degree
analogue of KP-0's `s2MuMinimal_key`, with the residual test replacing the odd-carry
engine.) -/
theorem s2MuMinimal_of_not_isUnit_normRes {g : Polynomial O}
    (hpos : 0 < g.natDegree) (hdeg : g.natDegree ≤ 4)
    (hnu : ¬ IsUnit (s2NormRes h2 hq g)) :
    S2MuMinimal h2 hq g :=
  ⟨hpos, fun f hf0 hdegf hdvd =>
    hnu (isUnit_of_dvd_unit (normRes_dvd_of_S2MuDvd h2 hq hdvd)
      (s2NormRes_isUnit_of_natDegree_lt_four h2 hq hf0 (by omega)))⟩

/-- ★ **NODE KP-3, the row form**: a polynomial of the recipe degree `4 = e'f'·deg Φ′` with
IRREDUCIBLE normalized residual is μ₂-minimal (published Definition 1.2's µ-minimality at
μ₂; irreducible elements are never units).  Monicity is NOT needed — recorded as part of
the honest hypothesis set. -/
theorem s2MuMinimal_of_irreducible_normRes {g : Polynomial O}
    (hdeg : g.natDegree = 4) (hirr : Irreducible (s2NormRes h2 hq g)) :
    S2MuMinimal h2 hq g :=
  s2MuMinimal_of_not_isUnit_normRes h2 hq (by omega) (le_of_eq hdeg) hirr.not_isUnit

/-! ## Part 2 — the honest fences: the degree-4 trichotomy, machine-witnessed

Three degree-4 inputs, three fates: irreducible residual → minimal (KP-3); unit residual
CAN still be minimal (`Φ′²`, by the second — trailing — mechanism); unit residual can FAIL
minimality (`Φ′² + Φ′`, the refuter).  So KP-3's residual hypothesis is not decorative, and
it is sufficient-not-necessary. -/

/-- **the SECOND minimality mechanism (trailing scalar death)**: a nonzero `φ` whose
top-grade residual has ZERO scalar μ₂-divides NO nonzero `f` of degree `< 4` — RP-4's
twisted product law forces the scalar of every `R(φ·q)` to `0` (the twist multiplies by
`X`-powers, the factor `R(φ)` already has scalar `0`), while `f`'s residual scalar is
NONZERO at its exact grade (RP-7's worker).  KP-0's odd-carry engine is the `φ = Φ′`
shadow of this mechanism (there parity forces the zero scalar on the cofactor side). -/
theorem not_S2MuDvd_of_gradedRes_coeff_zero {φ f : Polynomial O} (hφ0 : φ ≠ 0)
    (hφc : (s2GradedRes h2 hq (s2GradeOf h2 hq φ) φ).coeff 0 = 0)
    (hf0 : f ≠ 0) (hdegf : f.natDegree < 4) :
    ¬ S2MuDvd h2 hq φ f := by
  rintro ⟨q, hq'⟩
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [mul_zero] at hq'
    exact hf0 ((S2InitialEquiv_zero_right h2 hq).mp hq')
  have hexφ := S2ExactGrade_s2GradeOf h2 hq hφ0
  have hexq := S2ExactGrade_s2GradeOf h2 hq hq0
  have hexφq := S2ExactGrade_mul h2 hq hexφ hexq
  have hexf : S2ExactGrade h2 hq (s2GradeOf h2 hq φ + s2GradeOf h2 hq q) f :=
    S2ExactGrade_of_initialEquiv h2 hq hexφq (S2InitialEquiv_symm h2 hq hq')
  have hres := (S2InitialEquiv_iff_gradedRes h2 hq hexf hexφq).mp hq'
  have hmul := s2GradedRes_mul_of_exact h2 hq hexφ hexq
  have hc0 : (s2GradedRes h2 hq (s2GradeOf h2 hq φ + s2GradeOf h2 hq q) f).coeff 0 = 0 := by
    rw [hres, hmul, Polynomial.mul_coeff_zero, Polynomial.mul_coeff_zero, hφc, zero_mul,
      mul_zero]
  exact s2GradedRes_coeff_zero_ne_zero_of_exact h2 hq hexf hdegf hc0

/-- **`Φ′²` IS μ₂-minimal** — a UNIT-residual degree-4 input (`R₃(Φ′²) = 1`) that the
second mechanism still covers: its grade-10 residual `X` has scalar `0`, so it divides no
short polynomial.  KP-3's `¬ IsUnit` hypothesis is sufficient, NOT necessary. -/
theorem s2MuMinimal_key_sq :
    S2MuMinimal h2 hq (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key) := by
  refine ⟨by rw [tooth_key_sq_natDegree h2 hq]; omega, fun f hf0 hdeg hdvd => ?_⟩
  rw [tooth_key_sq_natDegree h2 hq] at hdeg
  exact not_S2MuDvd_of_gradedRes_coeff_zero h2 hq
    (mul_ne_zero (s2Frame h2 hq).hmonic.ne_zero (s2Frame h2 hq).hmonic.ne_zero)
    (key_sq_scalar_zero h2 hq) hf0 hdeg hdvd

/-- **tooth (minimal ≠ key)**: `Φ′²` is NOT μ₂-irreducible — it μ₂-divides the product
`Φ′·Φ′` (itself) but NEITHER factor (the second mechanism refutes `Φ′² ∣µ₂ Φ′`).  With
`s2MuMinimal_key_sq`: μ₂-minimality alone does not give key-polynomialhood, so
`key_criterion`'s Irreducible hypothesis is not decorative. -/
theorem tooth_key_sq_not_muIrreducible :
    ¬ S2MuIrreducible h2 hq (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key) := by
  rintro ⟨-, -, hprime⟩
  rcases hprime ((s2Frame h2 hq).key : Polynomial O) ((s2Frame h2 hq).key : Polynomial O)
      (S2MuDvd_self h2 hq _) with h | h <;>
    exact not_S2MuDvd_of_gradedRes_coeff_zero h2 hq
      (mul_ne_zero (s2Frame h2 hq).hmonic.ne_zero (s2Frame h2 hq).hmonic.ne_zero)
      (key_sq_scalar_zero h2 hq) (s2Frame h2 hq).hmonic.ne_zero
      (by rw [key_natDegree_two h2 hq]; omega) h

/-- ★ **the KP-3 refuter (naked degree-4 minimality is FALSE)**: `Φ′² + Φ′` is monic of
degree `4` with UNIT residual — it is initial-equivalent to `Φ′` itself (the `Φ′²`
perturbation sits at value `10 > 5`), so `R₃(Φ′² + Φ′) = R₃(Φ′) = 1` — yet NOT μ₂-minimal:
it μ₂-divides the degree-TWO `Φ′` with cofactor `1`.  So "monic + degree 4 → μ₂-minimal"
fails, and KP-3's residual hypothesis is essential. -/
theorem tooth_kp3_needs_nonunit :
    (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
        + (s2Frame h2 hq).key).Monic
      ∧ (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
          + (s2Frame h2 hq).key).natDegree = 4
      ∧ IsUnit (s2NormRes h2 hq (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
          + (s2Frame h2 hq).key))
      ∧ ¬ S2MuMinimal h2 hq (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
          + (s2Frame h2 hq).key) := by
  have hdlt : ((s2Frame h2 hq).key : Polynomial O).degree
      < (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key).degree := by
    rw [key_degree_withBot h2 hq, key_sq_degree_withBot h2 hq]
    norm_num
  have hmon : (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
      + (s2Frame h2 hq).key).Monic :=
    ((s2Frame h2 hq).hmonic.mul (s2Frame h2 hq).hmonic).add_of_left hdlt
  have hdeg4 : (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
      + (s2Frame h2 hq).key).natDegree = 4 := by
    have h := Polynomial.degree_add_eq_left_of_degree_lt hdlt
    rw [key_sq_degree_withBot h2 hq] at h
    exact Polynomial.natDegree_eq_of_degree_eq_some h
  have hv10 : s2Hgt₂ h2 hq (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key)
      = ((10 : ℕ) : WithTop ℤ) := tooth_key_sq h2 hq
  have hv5 : s2Hgt₂ h2 hq ((s2Frame h2 hq).key : Polynomial O)
      = ((5 : ℕ) : WithTop ℤ) := tooth_key h2 hq
  have hlt : ((5 : ℕ) : WithTop ℤ) < ((10 : ℕ) : WithTop ℤ) := by
    exact_mod_cast (by norm_num : (5 : ℕ) < 10)
  have hvsum : s2Hgt₂ h2 hq (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
      + (s2Frame h2 hq).key) = ((5 : ℕ) : WithTop ℤ) := by
    rw [s2Hgt₂_add_eq h2 hq _ _ (by rw [hv10, hv5]; exact hlt.ne'), hv10, hv5]
    exact min_eq_right hlt.le
  have hequiv : S2InitialEquiv h2 hq
      (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key + (s2Frame h2 hq).key)
      ((s2Frame h2 hq).key : Polynomial O) := by
    refine Or.inl ⟨?_, by rw [hvsum, hv5]⟩
    rw [show (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
          + (s2Frame h2 hq).key) - (s2Frame h2 hq).key
        = ((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key from by ring,
      hv10, hvsum]
    exact hlt
  refine ⟨hmon, hdeg4, ?_, ?_⟩
  · rw [s2NormRes_eq_of_initialEquiv h2 hq hequiv, s2NormRes_key h2 hq]
    exact isUnit_one
  · rintro ⟨-, hmin⟩
    refine hmin ((s2Frame h2 hq).key : Polynomial O) (s2Frame h2 hq).hmonic.ne_zero
      (by rw [key_natDegree_two h2 hq, hdeg4]; omega) ⟨1, ?_⟩
    rw [mul_one]
    exact S2InitialEquiv_symm h2 hq hequiv

/-! ## Part 3 — ★ NODE KP-4: the literal frontier field, assembled

`key_criterion` CLOSED: monic is given, μ₂-minimality is Part 1's, μ₂-irreducibility is
KP-2's consumable.  The A-C.11 `FGMNCalculus.KP_criterion` shape is the same hypothesis
list at `Rres := s2NormRes`, `KP := S2KeyPoly`. -/

/-- ★★ **NODE KP-4 — the S2 `key_criterion`** (published Lemma 5.2(2) + Corollary 4.9 + the
Theorem 5.7 degree display; the C130fg `FGMNSourceLaws.key_criterion` / A-C.11
`FGMNCalculus.KP_criterion` hypothesis list at the landed `r = 1` anchoring,
`(e', f') = (2, 1)`, `keyAt 1 = Φ′`): a monic `g` of the recipe degree
`4 = 2·1·deg Φ′` with irreducible residual of degree `f' = 1` and nonzero constant term is
a KEY POLYNOMIAL for μ₂.  Monic + KP-3's minimality + KP-2's primality.  The `deg R₃(g) = 1`
and `(R₃ g)(0) ≠ 0` hypotheses are carried for field-shape fidelity (the constant-term
clause is automatic at the landed operators, RP-8). -/
theorem s2_key_criterion :
    ∀ g : Polynomial O, g.Monic →
      g.natDegree = 2 * 1 * ((s2Frame h2 hq).key : Polynomial O).natDegree →
      Irreducible (s2NormRes h2 hq g) →
      (s2NormRes h2 hq g).natDegree = 1 →
      (s2NormRes h2 hq g).coeff 0 ≠ 0 →
      S2KeyPoly h2 hq g := by
  intro g hmon hdeg hirr hfdeg hc0
  refine ⟨hmon, ?_, s2_key_criterion_muIrreducible h2 hq g hmon hdeg hirr hfdeg hc0⟩
  refine s2MuMinimal_of_irreducible_normRes h2 hq ?_ hirr
  rw [hdeg, key_natDegree_two h2 hq]

/-- ★★ **the crown corollary — RP-12's lift IS a key polynomial**:
`S2KeyPoly (Φ′² + 4x)` — the constructed degree-four witness the whole RP/KP chain aims at
(published Theorem 5.7's construction, machine-closed end to end: monic and degree four by
RP-12, residual `X + 1` irreducible of degree `1` with nonzero constant term, so the
assembled criterion fires). -/
theorem s2KeyPoly_lift :
    S2KeyPoly h2 hq (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
      + Polynomial.C (4 : O) * Polynomial.X) := by
  have hres := s2_normalized_exists_normRes h2 hq
  refine s2_key_criterion h2 hq _ (s2_g_monic h2 hq)
    (by rw [s2_g_natDegree h2 hq, key_natDegree_two h2 hq]) ?_ ?_ ?_
  · rw [hres]
    exact s2_X_add_one_irreducible h2 hq
  · rw [hres,
      show (1 : Polynomial ((s2DepthTwo h2 hq).fld 2)) = Polynomial.C 1 from (map_one _).symm]
    exact Polynomial.natDegree_X_add_C 1
  · rw [hres, Polynomial.coeff_add, Polynomial.coeff_X_zero, Polynomial.coeff_one_zero,
      zero_add]
    exact one_ne_zero

/-- the crown, spelled at the explicit polynomial `(x² − 2)·(x² − 2) + 4x` (C97's `s2Key`). -/
theorem s2KeyPoly_lift_spelled :
    S2KeyPoly h2 hq ((Polynomial.X ^ 2 - Polynomial.C (2 : O))
        * (Polynomial.X ^ 2 - Polynomial.C (2 : O))
      + Polynomial.C (4 : O) * Polynomial.X) := by
  have h := s2KeyPoly_lift h2 hq
  rwa [key_eq h2 hq,
    show s2Key O = Polynomial.X ^ 2 - Polynomial.C (2 : O) from rfl] at h

/-- ★ **the FD-0 pin**: if `S : FGMNSourceData (s2DepthTwo h2 hq) K 2 1 5` reads
`normalizedResidual := s2NormRes` and `keyPolynomial := S2KeyPoly`, then the
`FGMNSourceLaws.key_criterion` field shape holds for `S` with the key read at the chain's
OWN `K.keyAt 1` (the landed `r = 1` anchoring; `keyAt_one` ties it to `Φ′`) — zero residual
assembly work at FD-0 for this field at the landed anchoring.  (The literal `keyAt 2`
numeral `2·1·4 = 8` is KP-6's row, NOT claimed — see the module docstring's anchoring
note.) -/
theorem s2_key_criterion_fills (K : KeyChain (s2DepthTwo h2 hq))
    (S : FGMNSourceData (s2DepthTwo h2 hq) K 2 1 5)
    (hnorm : S.normalizedResidual = s2NormRes h2 hq)
    (hkp : S.keyPolynomial = S2KeyPoly h2 hq) :
    ∀ g : Polynomial O, g.Monic →
      g.natDegree = 2 * 1 * (K.keyAt 1).natDegree →
      Irreducible (S.normalizedResidual g) →
      (S.normalizedResidual g).natDegree = 1 →
      (S.normalizedResidual g).coeff 0 ≠ 0 →
      S.keyPolynomial g := by
  intro g hmon hdeg hirr hfdeg hc0
  rw [hnorm] at hirr hfdeg hc0
  rw [hkp]
  refine s2_key_criterion h2 hq g hmon ?_ hirr hfdeg hc0
  rwa [K.keyAt_one] at hdeg

end S2

end Uniformity.Density.Tower.C130kp3

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130kp3.s2MuMinimal_of_not_isUnit_normRes
#print axioms Uniformity.Density.Tower.C130kp3.s2MuMinimal_of_irreducible_normRes
#print axioms Uniformity.Density.Tower.C130kp3.not_S2MuDvd_of_gradedRes_coeff_zero
#print axioms Uniformity.Density.Tower.C130kp3.s2MuMinimal_key_sq
#print axioms Uniformity.Density.Tower.C130kp3.tooth_key_sq_not_muIrreducible
#print axioms Uniformity.Density.Tower.C130kp3.tooth_kp3_needs_nonunit
#print axioms Uniformity.Density.Tower.C130kp3.s2_key_criterion
#print axioms Uniformity.Density.Tower.C130kp3.s2KeyPoly_lift
#print axioms Uniformity.Density.Tower.C130kp3.s2KeyPoly_lift_spelled
#print axioms Uniformity.Density.Tower.C130kp3.s2_key_criterion_fills

end AxCheck
