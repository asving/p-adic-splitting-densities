/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130kp5
import Uniformity.ChapC.C130kp7
import Uniformity.ChapC.C130np0
import Uniformity.ChapC.C130np6

/-!
# Uniformity.ChapC.C130fd0 — S2-source plan nodes FD-0/FD-1 — the records ASSEMBLED

**S2-source plan nodes FD-0 + FD-1** (`docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6 rows
FD-0 "Construct both records; every one of the thirteen projections has a named theorem" and
FD-1 "`grade_compat` and `letter_compat`, preferably definitional after explicit normalization
pins"), assembling the five closed cores (RP-0..RP-12, KP-0..KP-9, NP-0/NP-6) into the C130fg
records.  Everything below REUSES landed theorems; the only new mathematics is the
`key_irreducible` law (Part 1), which was re-scoped out of KP-5 and is proved here directly
from KP-0's honest predicates.

## The anchoring adjudication (the load-bearing FD-0 finding)

The plan's brief types the records at the depth-TWO tower:
`FGMNSourceData (s2DepthTwo h2 hq) K 2 1 5`, whose `FGMNSourceLaws` fields read the chain at
`K.keyAt r = K.keyAt 2` (degree `4`, pinned by the chain's own `keyAt_degree` law).  But the
landed S2 operators realize the augmentation `μ₁ → μ₂` whose key is `Φ′ = keyAt 1` — the
`r = 1` anchoring RECORDED by RP-0's module docstring, RP-11's course correction, and KP-3's
anchoring note.  At the depth-two typing the two carried-key fields are JOINTLY
UNSATISFIABLE over the landed operators, and this file lands that as a machine theorem
(★ `s2SourceLaws_depthTwo_unsatisfiable`): `carried_key_is_key` forces `keyAt 2 ∈ KP(μ₂)`,
`carried_key_residual` forces `R₃(keyAt 2) = 1`, and KP-9's landed degree dictionary
(`s2KeyPoly_normRes_natDegree`: `deg R₃(g) = deg g / 4` on keys) collides with
`deg (keyAt 2) = 4`: a degree-4 key polynomial has residual degree `1 ≠ 0`.  The briefed
`s2SourceLaws` at the depth-two typing therefore CANNOT exist — this is the same genre of
typing-level finding as U13's `no_s2_node_source`, and it is reported as a theorem, not
worked around by weakening any field.

The honest FD-0 assembly is therefore made at the recorded `r = 1` anchoring: the SAME
landed witness truncated to depth one (`s2DepthOne := (s2Witness …).trunc 1`, C.83's
`trunc`), whose `fld 1` is DEFINITIONALLY the same carrier as `(s2DepthTwo h2 hq).fld 2`
(C.97's witness uses one constant stage field at every index — pinned below by `rfl`).
There ★ `s2SourceDataOne` and ★ `s2SourceLawsOne` are BOTH constructed, with every one of
the thirteen law projections discharged by a NAMED landed theorem (table in
`runs/wave-b/verdict_FD01.md`).

## What lands at the depth-two typing (the briefed record, honestly)

* ★ `s2SourceData : FGMNSourceData (s2DepthTwo h2 hq) (s2DepthTwoKeyChain h2 hq) 2 1 5` —
  the DATA record at the briefed typing, fields = the landed S2 operators (`s2Hgt₂`,
  `s2GradedRes`, `s2NormRes`, `S2PrevGrade`, `S2KeyPoly`, `S2InitialEquiv`, NP-6's
  `s2Letter`), each read pinned by `rfl`.
* The five banked `_fills` pins all FIRE at it with `rfl` discharges
  (`s2SourceData_graded_mul`, `s2SourceData_graded_scalar_nonzero`,
  `s2SourceData_normalized_mul`, `s2SourceData_initial_iff_residual`,
  `s2SourceData_key_criterion_keyAtOne` — the last at KP-3's recorded `keyAt 1` anchoring),
  and five more fields hold by direct landed theorems (`graded_zero_of_above`, `graded_add`,
  `key_irreducible`, `carried_key_is_key` via KP-6's `s2KeyPoly_composedKey`,
  `letter_ne_zero`), plus `normalized_exists` through the NEW degree-eight adapter
  `g₈ := (Φ′² + 4x)·Φ′²` (`s2_gEight_monic`/`_natDegree`/`_normRes` — the shape adapter the
  plan row anticipated, built from RP-10's universal product law).
* The two fields that FAIL at this typing are machine-refuted, not skipped silently:
  `s2_carried_key_residual_depthTwo_refuted` (`R₃(composedKey) = X + 1 ≠ 1`, KP-6's landed
  value) and `s2_key_criterion_depthTwo_shape_refuted` (the same `g₈` witnesses that the
  degree-eight criterion shape is FALSE: its residual has degree `1`, but a key of degree 8
  must have residual degree `2`).  `normalized_recipe`'s depth-two shape is NOT landed and
  NOT claimed (STOP field; RP-11's recorded factor-of-`e'` grade correction applies —
  its khat grade numeral `(f'-t)·u' = 5` is calibrated for the `keyAt 1` recipe, not the
  `keyAt 2` one).  Consequently ★ `s2SourceLaws_impossible`: the briefed laws record is
  EMPTY at the landed operator readings.

## FD-1 (OPEN-DICT-2/4), at the corrected split frontier's field shapes

The un-split `ChainRealization` (C130fg) is uninhabitable at S2 (U13's `no_s2_node_source`);
the corrected carrier is C130s17's split `S2SourceFrontier`.  FD-1 lands both compat fields
in that structure's EXACT shapes, at NP-0's realized node pieces and NP-6's letters:

* ★ `s2_grade_compat` — `(s2SourceData …).nextValue g = s2NPPointHgt 2 x g` for every legal
  point: definitional after NP-0's normalization pin `s2NPPointHgt_two` (exactly the
  "definitional after explicit normalization pins" the plan row asks for).
* ★ `s2_letter_compat` — the transported FGMN letter is the ambient node letter:
  `algebraMap (topEquiv (letter i)) = ambientLetter i`, definitional from `map_one` at
  NP-6's forced letters (`s2Letter = 1`, `s2AmbientLetter = 1`).

## Honesty scope

* No `SplitNodePointSource`/`S2SourceFrontier`/`ChainRealization` INSTANCE (SG-0's row).
* The `r = 1`-anchored `normalized_recipe` field is discharged VACUOUSLY — its printed
  hypotheses are jointly unsatisfiable at the landed operators, MACHINE-CERTIFIED by RP-11's
  `s2_recipe_naive_numeral_vacuous` and re-exposed here as
  `tooth_recipe_printed_numerals_vacuous`.  This is a recorded defect of the abstract
  field's grade numerals (OPEN-DICT-2 content, RP-11's course correction), NOT hidden
  content: the honest non-vacuous recipe is RP-11's `s2_normalized_recipe` at the
  `e'`-corrected grade `10`.  Every other law field is filled non-vacuously.
* `s2SourceLaws_depthTwo_unsatisfiable` is CONDITIONAL on the landed operator readings
  (`normalizedResidual = s2NormRes`, `keyPolynomial = S2KeyPoly`); a future depth-two record
  built from genuinely `μ₃`-level operators (the plan §5.2 originals, nowhere landed) is not
  refuted.

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements):
`s2_key_irreducible` (the direct KP-0-predicate proof of published Lemma 1.8's conclusion at
the concrete model), the `g₈` adapter statements, the two depth-two refutation statements,
the unsatisfiability statement, the `s2DepthOne` truncation typing, and the two FD-1
statements.

**DEPENDS.** C130fg (the records, via C130rp6) · C130rp0/rp1/rp2/rp4/rp6/rp8/rp9/rp11 (the
RP chain: `S2ExactGrade` bank, `s2GradedRes` + zero/add laws, `s2_graded_mul` + fills,
`s2NormRes` + `s2NormRes_mul` + fills + key values, recipe vacuity + existence) ·
C130kp0/kp1/kp3/kp5/kp7 (the KP chain: predicates + `S2MuDvd_self`, `s2KeyPoly_key`,
`s2_key_criterion` + fills, `s2NormRes_composedKey`/`s2KeyPoly_composedKey`,
`s2_initial_iff_residual` + fills + `s2KeyPoly_normRes_natDegree`) · C130np0 (`S2NPPoint`,
`s2NPPt`, `s2NPPointHgt`, `s2NPPointHgt_two`) · C130np6 (`s2Letter`, `s2Letter_ne_zero`,
`s2AmbientLetter`, `s2AmbientLetter_coe`) · C130s17 (`s2RepositoryRealization`,
`s2TerminalReceiver`) · C130s2 (`s2DepthTwo`, `s2DepthTwoKeyChain`, `s2DepthTwo_Dcum_two`) ·
C97 (`s2Witness`) · C83 (`DeepTower.trunc`) · C80/C78adj (`s2Tower`, `composedKey`) ·
mathlib (`Polynomial.natDegree_mul`, `Polynomial.leadingCoeff_mul`,
`Polynomial.natDegree_eq_zero_of_isUnit`, `Polynomial.eq_C_of_natDegree_eq_zero`,
`Polynomial.isUnit_C`, `Polynomial.natDegree_X_add_C`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement touched in
any other file.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C130fd0

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130rp0
open Uniformity.Density.Tower.C130rp1 Uniformity.Density.Tower.C130rp2
open Uniformity.Density.Tower.C130rp6 Uniformity.Density.Tower.C130rp8
open Uniformity.Density.Tower.C130rp9 Uniformity.Density.Tower.C130rp11
open Uniformity.Density.Tower.C130kp0 Uniformity.Density.Tower.C130kp1
open Uniformity.Density.Tower.C130kp3 Uniformity.Density.Tower.C130kp5
open Uniformity.Density.Tower.C130kp7 Uniformity.Density.Tower.C130np0
open Uniformity.Density.Tower.C130np6 Uniformity.Density.Tower.C130s17
open Uniformity.Density.Tower.C80

universe uL

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 1 — the one genuinely new law: `key_irreducible` at the honest predicates

KP-5 re-scoped the universal field out ("needs published Lemma 1.8 in full"); at KP-0's
CONCRETE predicates no cite is needed — the classical MacLane argument is three landed
steps: `g ∣µ₂ g = a·b` (KP-0's `S2MuDvd_self`), μ₂-primality splits it, and μ₂-minimality
forbids either branch since both factors have strictly smaller degree.  Monicity forces the
degree-zero factors to be units (their leading coefficients multiply to `1`). -/

/-- ★ **the `key_irreducible` law** (published Lemma 1.8's conclusion, proved DIRECTLY at
KP-0's honest predicates — no fraction-field cite): every `S2KeyPoly` is irreducible in
`Polynomial O`.  Monic is carried inside `S2KeyPoly`; the field's extra `Monic` hypothesis
is absorbed. -/
theorem s2_key_irreducible {g : Polynomial O} (hkey : S2KeyPoly h2 hq g) :
    Irreducible g := by
  obtain ⟨hmon, hmin, hirr⟩ := hkey
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    have hpos := hmin.1
    omega
  · by_contra hcon
    have hua : ¬ IsUnit a := fun h => hcon (Or.inl h)
    have hub : ¬ IsUnit b := fun h => hcon (Or.inr h)
    have hg0 : g ≠ 0 := hmon.ne_zero
    have ha0 : a ≠ 0 := by rintro rfl; exact hg0 (by rw [hab, zero_mul])
    have hb0 : b ≠ 0 := by rintro rfl; exact hg0 (by rw [hab, mul_zero])
    have hlc : a.leadingCoeff * b.leadingCoeff = 1 := by
      rw [← Polynomial.leadingCoeff_mul, ← hab]
      exact hmon.leadingCoeff
    have hdega : 0 < a.natDegree := by
      rcases Nat.eq_zero_or_pos a.natDegree with h0 | h
      · exfalso
        refine hua ?_
        have hCa : a = Polynomial.C (a.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
        rw [hCa] at hlc
        rw [Polynomial.leadingCoeff_C] at hlc
        rw [hCa]
        exact Polynomial.isUnit_C.mpr (.of_mul_eq_one _ hlc)
      · exact h
    have hdegb : 0 < b.natDegree := by
      rcases Nat.eq_zero_or_pos b.natDegree with h0 | h
      · exfalso
        refine hub ?_
        have hCb : b = Polynomial.C (b.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
        rw [hCb] at hlc
        rw [Polynomial.leadingCoeff_C] at hlc
        rw [hCb]
        exact Polynomial.isUnit_C.mpr (.of_mul_eq_one _ (by rw [mul_comm]; exact hlc))
      · exact h
    have hdeg : a.natDegree + b.natDegree = g.natDegree := by
      rw [hab, Polynomial.natDegree_mul ha0 hb0]
    have hself : S2MuDvd h2 hq g (a * b) := S2MuDvd_of_dvd h2 hq (dvd_of_eq hab)
    rcases hirr.2.2 a b hself with hdvd | hdvd
    · exact hmin.2 a ha0 (by omega) hdvd
    · exact hmin.2 b hb0 (by omega) hdvd

/-! ## Part 2 — FD-0 at the briefed depth-two typing: the DATA record + what survives

The data record exists (all seven operator fields are landed); the laws record does NOT
(Part 3's unsatisfiability).  Every field-level fact that IS true at this typing gets a
named instance-level theorem here — the five pins fire with `rfl` discharges. -/

/-- ★ **FD-0, the briefed DATA record**: the landed S2 operators as a literal
`FGMNSourceData` over the depth-two tower and its concrete chain.  Every field read is
pinned `rfl` below. -/
noncomputable def s2SourceData :
    FGMNSourceData (s2DepthTwo h2 hq) (s2DepthTwoKeyChain h2 hq) 2 1 5 where
  nextValue := s2Hgt₂ h2 hq
  gradedResidual := s2GradedRes h2 hq
  normalizedResidual := s2NormRes h2 hq
  PrevGrade := S2PrevGrade
  keyPolynomial := S2KeyPoly h2 hq
  initialEquiv := S2InitialEquiv h2 hq
  letter := s2Letter h2 hq

/-- read pin: `nextValue` is the landed level-two cleared value `μ₂` (RP-0/NV chain). -/
theorem s2SourceData_nextValue : (s2SourceData h2 hq).nextValue = s2Hgt₂ h2 hq := rfl

/-- read pin: `gradedResidual` is RP-1's `s2GradedRes`. -/
theorem s2SourceData_gradedResidual :
    (s2SourceData h2 hq).gradedResidual = s2GradedRes h2 hq := rfl

/-- read pin: `normalizedResidual` is RP-8's `s2NormRes`. -/
theorem s2SourceData_normalizedResidual :
    (s2SourceData h2 hq).normalizedResidual = s2NormRes h2 hq := rfl

/-- read pin: `PrevGrade` is RP-6's `S2PrevGrade` (evenness, the A-C.13 realization). -/
theorem s2SourceData_PrevGrade : (s2SourceData h2 hq).PrevGrade = S2PrevGrade := rfl

/-- read pin: `keyPolynomial` is KP-0's `S2KeyPoly`. -/
theorem s2SourceData_keyPolynomial :
    (s2SourceData h2 hq).keyPolynomial = S2KeyPoly h2 hq := rfl

/-- read pin: `initialEquiv` is KP-0's `S2InitialEquiv`. -/
theorem s2SourceData_initialEquiv :
    (s2SourceData h2 hq).initialEquiv = S2InitialEquiv h2 hq := rfl

/-- read pin: `letter` is NP-6's `s2Letter`. -/
theorem s2SourceData_letter : (s2SourceData h2 hq).letter = s2Letter h2 hq := rfl

/-! ### 2a. The five banked pins FIRE at the record (`rfl` discharges) -/

/-- field `graded_mul` HOLDS at the briefed record — RP-6's pin, fired with `rfl`s. -/
theorem s2SourceData_graded_mul :
    ∀ β β' (g h : Polynomial O),
      (s2SourceData h2 hq).ExactGrade β g → (s2SourceData h2 hq).ExactGrade β' h →
      (s2SourceData h2 hq).PrevGrade β' →
        (s2SourceData h2 hq).ExactGrade (β + β') (g * h) ∧
        (s2SourceData h2 hq).gradedResidual (β + β') (g * h)
          = (s2SourceData h2 hq).gradedResidual β g
            * (s2SourceData h2 hq).gradedResidual β' h :=
  s2_graded_mul_fills h2 hq _ _ rfl rfl rfl

/-- field `graded_scalar_nonzero` HOLDS at the briefed record — RP-7's pin, fired with
`rfl`s (the fence is the chain's own `keyAt 2` degree, `4`). -/
theorem s2SourceData_graded_scalar_nonzero :
    ∀ β (g : Polynomial O),
      (s2SourceData h2 hq).ExactGrade β g →
      g.natDegree < ((s2DepthTwoKeyChain h2 hq).keyAt 2).natDegree → g ≠ 0 →
        ((s2SourceData h2 hq).gradedResidual β g).coeff 0 ≠ 0 :=
  s2_graded_scalar_nonzero_fills h2 hq _ _ rfl rfl

/-- field `normalized_mul` HOLDS at the briefed record — RP-10's pin, fired with `rfl`. -/
theorem s2SourceData_normalized_mul :
    ∀ g h : Polynomial O,
      (s2SourceData h2 hq).normalizedResidual (g * h)
        = (s2SourceData h2 hq).normalizedResidual g
          * (s2SourceData h2 hq).normalizedResidual h :=
  s2_normalized_mul_fills h2 hq _ _ rfl

/-- field `initial_iff_residual` HOLDS at the briefed record — KP-9's pin, fired with
`rfl`s. -/
theorem s2SourceData_initial_iff_residual :
    ∀ g h : Polynomial O,
      (s2SourceData h2 hq).keyPolynomial g → (s2SourceData h2 hq).keyPolynomial h →
        ((s2SourceData h2 hq).initialEquiv g h ↔
          (s2SourceData h2 hq).normalizedResidual g
            = (s2SourceData h2 hq).normalizedResidual h) :=
  s2_initial_iff_residual_fills h2 hq _ _ rfl rfl rfl

/-- the `key_criterion` SHAPE at KP-3's recorded `keyAt 1` anchoring HOLDS at the briefed
record — KP-4's pin, fired with `rfl`s.  (The literal `keyAt 2` field shape is REFUTED
below.) -/
theorem s2SourceData_key_criterion_keyAtOne :
    ∀ g : Polynomial O, g.Monic →
      g.natDegree = 2 * 1 * ((s2DepthTwoKeyChain h2 hq).keyAt 1).natDegree →
      Irreducible ((s2SourceData h2 hq).normalizedResidual g) →
      ((s2SourceData h2 hq).normalizedResidual g).natDegree = 1 →
      ((s2SourceData h2 hq).normalizedResidual g).coeff 0 ≠ 0 →
      (s2SourceData h2 hq).keyPolynomial g :=
  s2_key_criterion_fills h2 hq _ _ rfl rfl

/-! ### 2b. The direct-law fields at the briefed record -/

/-- field `graded_zero_of_above` HOLDS at the briefed record (RP-2's landed law). -/
theorem s2SourceData_graded_zero_of_above :
    ∀ β (g : Polynomial O), (s2SourceData h2 hq).AboveGrade β g →
      (s2SourceData h2 hq).gradedResidual β g = 0 :=
  fun _ _ h => s2GradedRes_zero_of_above h2 hq h

/-- field `graded_add` HOLDS at the briefed record (RP-2's landed law). -/
theorem s2SourceData_graded_add :
    ∀ β (g h : Polynomial O),
      (s2SourceData h2 hq).ExactGrade β g → (s2SourceData h2 hq).ExactGrade β h →
      (s2SourceData h2 hq).ExactGrade β (g + h) →
        (s2SourceData h2 hq).gradedResidual β (g + h)
          = (s2SourceData h2 hq).gradedResidual β g
            + (s2SourceData h2 hq).gradedResidual β h :=
  fun _ _ _ hg hh hgh => s2GradedRes_add h2 hq hg hh hgh

/-- field `key_irreducible` HOLDS at the briefed record (Part 1's new law). -/
theorem s2SourceData_key_irreducible :
    ∀ g : Polynomial O, (s2SourceData h2 hq).keyPolynomial g → g.Monic → Irreducible g :=
  fun _ hkp _ => s2_key_irreducible h2 hq hkp

/-- field `carried_key_is_key` HOLDS at the briefed record — KP-6's landed
`s2KeyPoly_composedKey` (`keyAt 2 = composedKey` definitionally). -/
theorem s2SourceData_carried_key_is_key :
    0 < 2 → (s2SourceData h2 hq).keyPolynomial ((s2DepthTwoKeyChain h2 hq).keyAt 2) :=
  fun _ => s2KeyPoly_composedKey h2 hq

/-- field `letter_ne_zero` HOLDS at the briefed record (NP-6's exact shape). -/
theorem s2SourceData_letter_ne_zero :
    ∀ i, 1 ≤ i → i ≤ 2 → (s2SourceData h2 hq).letter i ≠ 0 :=
  s2Letter_ne_zero h2 hq

/-! ### 2c. The degree-eight existence adapter (the plan-anticipated shape adapter)

The depth-two `normalized_exists` field asks for a monic lift of degree
`e'f'·deg(keyAt 2) = 8`.  RP-12 landed the degree-four lift `g₄ := Φ′² + 4x`; the
degree-eight witness is `g₈ := g₄·Φ′²`, whose residual is unchanged by RP-10's universal
product law (`R₃(Φ′²) = 1`). -/

/-- the degree-eight witness `g₈ = (Φ′² + 4x)·Φ′²` is monic. -/
theorem s2_gEight_monic :
    ((((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
        + Polynomial.C (4 : O) * Polynomial.X)
      * (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key)).Monic :=
  (s2_g_monic h2 hq).mul ((s2Frame h2 hq).hmonic.mul (s2Frame h2 hq).hmonic)

/-- the degree-eight witness has degree exactly `8`. -/
theorem s2_gEight_natDegree :
    ((((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
        + Polynomial.C (4 : O) * Polynomial.X)
      * (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key)).natDegree = 8 := by
  rw [Polynomial.natDegree_mul (s2_g_monic h2 hq).ne_zero
      ((s2Frame h2 hq).hmonic.mul (s2Frame h2 hq).hmonic).ne_zero,
    s2_g_natDegree h2 hq, tooth_key_sq_natDegree h2 hq]

/-- the degree-eight witness keeps the residual `X + 1` (RP-10's universal law kills the
`Φ′²` factor: `R₃(Φ′²) = R₃(Φ′)² = 1`). -/
theorem s2_gEight_normRes :
    s2NormRes h2 hq
        ((((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
            + Polynomial.C (4 : O) * Polynomial.X)
          * (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key))
      = Polynomial.X + 1 := by
  rw [s2NormRes_mul h2 hq, s2_normalized_exists_normRes h2 hq, s2NormRes_mul h2 hq,
    s2NormRes_key h2 hq, mul_one, mul_one]

/-- field `normalized_exists` HOLDS at the briefed record, through the degree-eight
adapter: any admissible residual input is forced to `X + 1` (RP-12's collapse) and `g₈`
lifts it at the printed degree `2·1·deg(keyAt 2) = 8`. -/
theorem s2SourceData_normalized_exists :
    0 < 2 → ∀ ψ : Polynomial ((s2DepthTwo h2 hq).fld 2),
      ψ.Monic → Irreducible ψ → ψ.natDegree = 1 → ψ.coeff 0 ≠ 0 →
        ∃ g : Polynomial O, g.Monic ∧
          g.natDegree = 2 * 1 * ((s2DepthTwoKeyChain h2 hq).keyAt 2).natDegree ∧
          (s2SourceData h2 hq).normalizedResidual g = ψ := by
  intro _ ψ hm _hirr hd hc
  have hψeq : ψ = Polynomial.X + 1 := s2_unique_admissible_linear h2 hq ψ hm hd hc
  refine ⟨_, s2_gEight_monic h2 hq, ?_, ?_⟩
  · rw [s2_gEight_natDegree h2 hq, s2KeyChain_keyAt_two_natDegree h2 hq]
  · rw [hψeq]
    exact s2_gEight_normRes h2 hq

/-! ## Part 3 — the depth-two laws record is IMPOSSIBLE (the FD-0 finding, as theorems)

The STOP fields of the briefed typing, machine-certified.  Nothing is weakened: the field
statements are refuted exactly as printed. -/

/-- **refutation, field `carried_key_residual` at the briefed typing**: the chain's own
`keyAt 2 = composedKey` has residual `X + 1 ≠ 1` (KP-6's landed value).  Published eq (11)
is about the key GENERATING the realized valuation — `Φ′ = keyAt 1`, where the field DOES
hold (`s2NormRes_key`, consumed at Part 4's `r = 1` record). -/
theorem s2_carried_key_residual_depthTwo_refuted :
    ¬ ((s2SourceData h2 hq).normalizedResidual ((s2DepthTwoKeyChain h2 hq).keyAt 2) = 1) := by
  intro h
  have h' : s2NormRes h2 hq (composedKey (s2Tower h2 hq)) = 1 := h
  rw [s2NormRes_composedKey h2 hq] at h'
  have hX : (Polynomial.X : Polynomial ((s2DepthTwo h2 hq).fld 2)) = 0 := by
    linear_combination h'
  exact Polynomial.X_ne_zero hX

/-- **refutation, field `key_criterion` at the briefed typing** (the literal
`e'f'·deg(keyAt 2) = 8` shape): `g₈` is monic of degree 8 with irreducible degree-1
residual of nonzero scalar, yet is NOT a key polynomial — KP-9's degree dictionary forces
degree-8 keys to have residual degree `2`.  (KP-3's anchoring note said the degree-8 shape
was "KP-6's row, NOT claimed"; this shows it was unclaimable.) -/
theorem s2_key_criterion_depthTwo_shape_refuted :
    ¬ (∀ g : Polynomial O, g.Monic →
        g.natDegree = 2 * 1 * ((s2DepthTwoKeyChain h2 hq).keyAt 2).natDegree →
        Irreducible ((s2SourceData h2 hq).normalizedResidual g) →
        ((s2SourceData h2 hq).normalizedResidual g).natDegree = 1 →
        ((s2SourceData h2 hq).normalizedResidual g).coeff 0 ≠ 0 →
        (s2SourceData h2 hq).keyPolynomial g) := by
  intro hcrit
  have hXdeg : (Polynomial.X + 1 : Polynomial ((s2DepthTwo h2 hq).fld 2)).natDegree = 1 := by
    rw [show (1 : Polynomial ((s2DepthTwo h2 hq).fld 2)) = Polynomial.C 1 from
      (map_one _).symm]
    exact Polynomial.natDegree_X_add_C 1
  have hnorm : s2NormRes h2 hq
      ((((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
          + Polynomial.C (4 : O) * Polynomial.X)
        * (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key))
      = Polynomial.X + 1 := s2_gEight_normRes h2 hq
  have hdeg8 : ((((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
        + Polynomial.C (4 : O) * Polynomial.X)
      * (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key)).natDegree
      = 2 * 1 * ((s2DepthTwoKeyChain h2 hq).keyAt 2).natDegree := by
    rw [s2_gEight_natDegree h2 hq, s2KeyChain_keyAt_two_natDegree h2 hq]
  have hkey := hcrit _ (s2_gEight_monic h2 hq) hdeg8
    (by rw [show (s2SourceData h2 hq).normalizedResidual = s2NormRes h2 hq from rfl, hnorm]
        exact s2_X_add_one_irreducible h2 hq)
    (by rw [show (s2SourceData h2 hq).normalizedResidual = s2NormRes h2 hq from rfl, hnorm]
        exact hXdeg)
    (by rw [show (s2SourceData h2 hq).normalizedResidual = s2NormRes h2 hq from rfl, hnorm,
          Polynomial.coeff_add, Polynomial.coeff_X_zero, Polynomial.coeff_one_zero, zero_add]
        exact one_ne_zero)
  have hpin := s2KeyPoly_normRes_natDegree h2 hq hkey
  rw [hnorm, hXdeg, s2_gEight_natDegree h2 hq] at hpin
  norm_num at hpin

/-- ★★ **the FD-0 finding — the briefed depth-two laws record is UNSATISFIABLE** at the
landed operator readings, for EVERY key chain over `s2DepthTwo`: `carried_key_is_key` and
`carried_key_residual` jointly collide with the chain's own degree law through KP-9's
landed degree dictionary (`deg R₃(g) = deg g / 4` on keys — a degree-4 key cannot have the
degree-0 residual `1`).  Same genre as U13's `no_s2_node_source`: a typing-level index
clash (the structure reuses the tower depth `r` as the FGMN key index, but the landed
operators realize the `keyAt 1` augmentation), reported as a theorem, with the honest
`r = 1` assembly landed in Part 4. -/
theorem s2SourceLaws_depthTwo_unsatisfiable
    (K : KeyChain (s2DepthTwo h2 hq))
    (S : FGMNSourceData (s2DepthTwo h2 hq) K 2 1 5)
    (hnorm : S.normalizedResidual = s2NormRes h2 hq)
    (hkp : S.keyPolynomial = S2KeyPoly h2 hq) :
    IsEmpty (FGMNSourceLaws (s2DepthTwo h2 hq) K 2 1 5 S) := by
  refine ⟨fun L => ?_⟩
  have hkey : S2KeyPoly h2 hq (K.keyAt 2) := by
    rw [← hkp]
    exact L.carried_key_is_key (by omega)
  have hres : s2NormRes h2 hq (K.keyAt 2) = 1 := by
    rw [← hnorm]
    exact L.carried_key_residual (by omega)
  have hdeg4 : (K.keyAt 2).natDegree = 4 :=
    (K.keyAt_degree 2 ⟨by omega, le_rfl⟩).trans (s2DepthTwo_Dcum_two h2 hq)
  have hpin := s2KeyPoly_normRes_natDegree h2 hq hkey
  rw [hres, hdeg4, Polynomial.natDegree_one] at hpin
  norm_num at hpin

/-- the instance corollary: the briefed `s2SourceLaws` does not exist. -/
theorem s2SourceLaws_impossible :
    IsEmpty (FGMNSourceLaws (s2DepthTwo h2 hq) (s2DepthTwoKeyChain h2 hq) 2 1 5
      (s2SourceData h2 hq)) :=
  s2SourceLaws_depthTwo_unsatisfiable h2 hq _ _ rfl rfl

/-! ## Part 4 — ★ FD-0 at the recorded `r = 1` anchoring: BOTH records CONSTRUCTED

The landed operators realize `nextValue := μ₂` at repo depth `r = 1` (`keyAt 1 = Φ′`) —
RP-0's docstring, RP-11's course correction, KP-3's anchoring note.  The depth-one carrier
is the SAME landed witness truncated one level lower; its stage field is definitionally the
same carrier (C.97's witness is constant-field), so every landed operator plugs in
unchanged. -/

/-- **the depth-one S2 tower**: C.97's witness truncated to depth ONE — the repo depth at
which the landed operators realize `FGMNSourceData` (RP-11's recorded course
correction). -/
noncomputable def s2DepthOne : DeepTower (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) 1 :=
  (s2Witness h2 hq 1 (s2Frame_pin h2 hq)).trunc 1 (by omega)

/-- anti-drift pin: the depth-one terminal carrier IS the depth-two terminal carrier,
definitionally (C.97's witness uses one constant stage field at every index). -/
theorem s2DepthOne_fld_eq : (s2DepthOne h2 hq).fld 1 = (s2DepthTwo h2 hq).fld 2 := rfl

/-- `D₁ = e₁f₁ = 2` at the depth-one truncation. -/
theorem s2DepthOne_Dcum_one : (s2DepthOne h2 hq).Dcum 1 = 2 := by
  rw [DeepTower.Dcum, show (Finset.Icc 1 1 : Finset ℕ) = {1} by decide,
    Finset.prod_singleton, (s2DepthOne h2 hq).he1, (s2DepthOne h2 hq).hf1]
  rfl

/-- the depth-one key assignment: the frame key `Φ′` at every index (only index `1` is
live; junk elsewhere, exactly as C130s2's chain treats its off-range indices). -/
noncomputable def s2DepthOneKeyAt (_ : ℕ) : Polynomial O := (s2Frame h2 hq).key

/-- the depth-one key chain: `keyAt 1 = Φ′`, monic, of the cumulative degree `2`. -/
noncomputable def s2DepthOneKeyChain : KeyChain (s2DepthOne h2 hq) where
  keyAt := s2DepthOneKeyAt h2 hq
  keyAt_one := rfl
  keyAt_monic := fun _ _ => (s2Frame h2 hq).hmonic
  keyAt_degree := by
    intro i hi
    obtain ⟨h1, h2i⟩ := hi
    interval_cases i
    show ((s2Frame h2 hq).key : Polynomial O).natDegree = (s2DepthOne h2 hq).Dcum 1
    rw [(s2Frame h2 hq).hdeg, s2DepthOne_Dcum_one h2 hq, e1_eq h2 hq, f1_eq h2 hq]

/-- the chain's key degree, as a numeral: `deg (keyAt 1) = deg Φ′ = 2`. -/
theorem s2DepthOneKeyChain_keyAt_natDegree :
    ((s2DepthOneKeyChain h2 hq).keyAt 1).natDegree = 2 := by
  show ((s2Frame h2 hq).key : Polynomial O).natDegree = 2
  rw [key_eq h2 hq]
  exact s2Key_natDegree

/-- ★★ **FD-0, the DATA record at the honest anchoring**: the SAME seven landed operators,
typed at repo depth `r = 1` — where the abstract dictionary's `keyAt r` is the key `Φ′`
that actually generates the realized `nextValue = μ₂`. -/
noncomputable def s2SourceDataOne :
    FGMNSourceData (s2DepthOne h2 hq) (s2DepthOneKeyChain h2 hq) 2 1 5 where
  nextValue := s2Hgt₂ h2 hq
  gradedResidual := s2GradedRes h2 hq
  normalizedResidual := s2NormRes h2 hq
  PrevGrade := S2PrevGrade
  keyPolynomial := S2KeyPoly h2 hq
  initialEquiv := S2InitialEquiv h2 hq
  letter := s2Letter h2 hq

/-- read pin: `nextValue` is `s2Hgt₂` — same operator as the depth-two record. -/
theorem s2SourceDataOne_nextValue : (s2SourceDataOne h2 hq).nextValue = s2Hgt₂ h2 hq := rfl

/-- read pin: `gradedResidual` is `s2GradedRes`. -/
theorem s2SourceDataOne_gradedResidual :
    (s2SourceDataOne h2 hq).gradedResidual = s2GradedRes h2 hq := rfl

/-- read pin: `normalizedResidual` is `s2NormRes`. -/
theorem s2SourceDataOne_normalizedResidual :
    (s2SourceDataOne h2 hq).normalizedResidual = s2NormRes h2 hq := rfl

/-- read pin: `PrevGrade` is `S2PrevGrade`. -/
theorem s2SourceDataOne_PrevGrade : (s2SourceDataOne h2 hq).PrevGrade = S2PrevGrade := rfl

/-- read pin: `keyPolynomial` is `S2KeyPoly`. -/
theorem s2SourceDataOne_keyPolynomial :
    (s2SourceDataOne h2 hq).keyPolynomial = S2KeyPoly h2 hq := rfl

/-- read pin: `initialEquiv` is `S2InitialEquiv`. -/
theorem s2SourceDataOne_initialEquiv :
    (s2SourceDataOne h2 hq).initialEquiv = S2InitialEquiv h2 hq := rfl

/-- read pin: `letter` is NP-6's `s2Letter` (typed through the definitional carrier
equality `s2DepthOne_fld_eq`). -/
theorem s2SourceDataOne_letter : (s2SourceDataOne h2 hq).letter = s2Letter h2 hq := rfl

/-- **the recorded vacuity of the printed recipe numerals** (RP-11's course correction,
re-exposed at the assembled record so the `normalized_recipe` fill below cannot be
mistaken for content): NO polynomial satisfies the field's own khat hypotheses — the
degree fence `< deg (keyAt 1) = 2` forces an even cleared grade, but the printed grade
numeral `(f'-t)·u' = 5` is odd.  The honest non-vacuous recipe is RP-11's
`s2_normalized_recipe` at the `e'`-corrected grade `10` (OPEN-DICT-2 content). -/
theorem tooth_recipe_printed_numerals_vacuous :
    ∀ khat : Polynomial O,
      khat.natDegree < ((s2DepthOneKeyChain h2 hq).keyAt 1).natDegree →
      ¬ (s2SourceDataOne h2 hq).ExactGrade 5 khat := by
  intro khat hdeg
  rw [s2DepthOneKeyChain_keyAt_natDegree h2 hq] at hdeg
  exact s2_recipe_naive_numeral_vacuous h2 hq hdeg

/-- ★★ **FD-0, the LAWS record at the honest anchoring — ALL THIRTEEN projections
discharged by named landed theorems** (the per-field table is
`runs/wave-b/verdict_FD01.md`): RP-2's zero/add laws, RP-6's assembled `graded_mul`, RP-7's
scalar worker under the `keyAt 1` fence, RP-10's universal `normalized_mul`, RP-11's
recipe-vacuity + existence, KP-4's criterion, Part 1's `key_irreducible`, KP-1's
`s2KeyPoly_key`, RP-8's `s2NormRes_key`, KP-9's Proposition-5.6 field, and NP-6's letters.
The one vacuous discharge (`normalized_recipe`) is certified vacuous by the tooth above and
is a recorded defect of the abstract field's grade numerals, not of the realization. -/
theorem s2SourceLawsOne :
    FGMNSourceLaws (s2DepthOne h2 hq) (s2DepthOneKeyChain h2 hq) 2 1 5
      (s2SourceDataOne h2 hq) where
  graded_zero_of_above := fun _ _ h => s2GradedRes_zero_of_above h2 hq h
  graded_add := fun _ _ _ hg hh hgh => s2GradedRes_add h2 hq hg hh hgh
  graded_mul := fun β β' g h hg hh hp => s2_graded_mul h2 hq β β' g h hg hh hp
  graded_scalar_nonzero := fun _ g hg hdeg _ => by
    rw [s2DepthOneKeyChain_keyAt_natDegree h2 hq] at hdeg
    exact s2GradedRes_coeff_zero_ne_zero_of_exact h2 hq hg (by omega)
  normalized_mul := fun g h => s2NormRes_mul h2 hq g h
  normalized_recipe := fun khat hgr hdeg => by
    exfalso
    exact tooth_recipe_printed_numerals_vacuous h2 hq (khat 0) (hdeg 0 (by omega))
      (hgr 0 (by omega))
  normalized_exists := fun _ ψ hm hirr hd hc => s2_normalized_exists h2 hq ψ hm hirr hd hc
  key_criterion := fun g hm hd hirr hfd hc => s2_key_criterion h2 hq g hm hd hirr hfd hc
  key_irreducible := fun _ hkp _ => s2_key_irreducible h2 hq hkp
  carried_key_is_key := fun _ => s2KeyPoly_key h2 hq
  carried_key_residual := fun _ => s2NormRes_key h2 hq
  initial_iff_residual := fun g h hg hh => s2_initial_iff_residual h2 hq g h hg hh
  letter_ne_zero := fun i h1 hr => s2Letter_ne_zero h2 hq i h1 (by omega)

/-! ## Part 5 — FD-1: OPEN-DICT-2/4, at the corrected split frontier's field shapes

The un-split `ChainRealization` is uninhabitable at S2 (U13); the corrected carrier is
C130s17's split `S2SourceFrontier`, whose `grade_compat`/`letter_compat` fields read the
depth-two record against NP-0's node pieces and NP-6's letters.  Both are landed here in
those EXACT shapes, definitionally after the recorded normalization pins. -/

/-- ★ **FD-1, OPEN-DICT-2 (`grade_compat`)** — the split `S2SourceFrontier.grade_compat`
field shape at `fgmn := s2SourceData` and NP-0's realized node pieces: the record's
`nextValue` IS the legal-point read at the terminal stage.  Definitional after NP-0's
normalization pin `s2NPPointHgt_two` (the point read restricts to the landed `s2Hgt₂` for
ALL polynomials, not only slot-fenced ones). -/
theorem s2_grade_compat :
    ∀ x : S2NPPoint, s2NPPt h2 hq 2 x → ∀ g : Polynomial O,
      (s2SourceData h2 hq).nextValue g = s2NPPointHgt h2 hq 2 x g :=
  fun x _ g => (s2NPPointHgt_two h2 hq x g).symm

/-- ★ **FD-1, OPEN-DICT-4 (`letter_compat`)** — the split `S2SourceFrontier.letter_compat`
field shape at `fgmn := s2SourceData`, the repository receiver, and NP-6's letters: the
transported FGMN letter is the ambient node letter, at every live stage.  Definitional
from `map_one` — NP-6's letters are FORCED to `1` on both sides (`s2Letter_forced`). -/
theorem s2_letter_compat (L : Type uL) [Field L]
    [Algebra ((s2DepthTwo h2 hq).fld 2) L] :
    ∀ i, StageLive 2 i →
      algebraMap ((s2DepthTwo h2 hq).fld 2) L
          ((s2RepositoryRealization h2 hq).receiver.topEquiv
            ((s2SourceData h2 hq).letter i)) =
        (s2AmbientLetter L i : L) := by
  intro i _
  show algebraMap ((s2DepthTwo h2 hq).fld 2) L
      ((s2RepositoryRealization h2 hq).receiver.topEquiv 1) = (s2AmbientLetter L i : L)
  rw [map_one, map_one, s2AmbientLetter_coe]

end S2

end Uniformity.Density.Tower.C130fd0

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130fd0.s2_key_irreducible
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceData
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceData_nextValue
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceData_gradedResidual
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceData_normalizedResidual
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceData_PrevGrade
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceData_keyPolynomial
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceData_initialEquiv
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceData_letter
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceData_graded_mul
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceData_graded_scalar_nonzero
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceData_normalized_mul
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceData_initial_iff_residual
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceData_key_criterion_keyAtOne
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceData_graded_zero_of_above
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceData_graded_add
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceData_key_irreducible
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceData_carried_key_is_key
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceData_letter_ne_zero
#print axioms Uniformity.Density.Tower.C130fd0.s2_gEight_monic
#print axioms Uniformity.Density.Tower.C130fd0.s2_gEight_natDegree
#print axioms Uniformity.Density.Tower.C130fd0.s2_gEight_normRes
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceData_normalized_exists
#print axioms Uniformity.Density.Tower.C130fd0.s2_carried_key_residual_depthTwo_refuted
#print axioms Uniformity.Density.Tower.C130fd0.s2_key_criterion_depthTwo_shape_refuted
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceLaws_depthTwo_unsatisfiable
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceLaws_impossible
#print axioms Uniformity.Density.Tower.C130fd0.s2DepthOne
#print axioms Uniformity.Density.Tower.C130fd0.s2DepthOne_fld_eq
#print axioms Uniformity.Density.Tower.C130fd0.s2DepthOne_Dcum_one
#print axioms Uniformity.Density.Tower.C130fd0.s2DepthOneKeyAt
#print axioms Uniformity.Density.Tower.C130fd0.s2DepthOneKeyChain
#print axioms Uniformity.Density.Tower.C130fd0.s2DepthOneKeyChain_keyAt_natDegree
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceDataOne
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceDataOne_nextValue
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceDataOne_gradedResidual
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceDataOne_normalizedResidual
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceDataOne_PrevGrade
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceDataOne_keyPolynomial
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceDataOne_initialEquiv
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceDataOne_letter
#print axioms Uniformity.Density.Tower.C130fd0.tooth_recipe_printed_numerals_vacuous
#print axioms Uniformity.Density.Tower.C130fd0.s2SourceLawsOne
#print axioms Uniformity.Density.Tower.C130fd0.s2_grade_compat
#print axioms Uniformity.Density.Tower.C130fd0.s2_letter_compat

end AxCheck
