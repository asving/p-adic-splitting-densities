/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130kp0
import Uniformity.ChapC.C130rp9
import Uniformity.ChapC.C130rp11

/-!
# Uniformity.ChapC.C130kp1 — S2-source plan nodes KP-1/KP-2 (CORES 1-2/4)

**S2-source plan nodes KP-1 + KP-2** (`docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6
rows KP-1 "Translate μ-divisibility into divisibility of normalized residuals in the needed
scopes" and KP-2 "Irreducible residual with nonzero constant term gives prime initial
form"), the fourth inductive core (`key_criterion`, CORES 1–2 of 4) — on KP-0's predicates
(C130kp0), RP-10's universal `s2NormRes_mul` (C130rp9), RP-8's normalized-residual bank
(C130rp8), and RP-12's landed degree-four lift (C130rp11).

## NODE KP-1 — the translation, at the scopes the proofs force

* ★ **forward, UNIVERSAL** (`normRes_dvd_of_S2MuDvd`): `φ ∣µ₂ g → R₃(φ) ∣ R₃(g)` for ALL
  `φ, g` — KP-0's normalized tie composed with RP-10's universal product law.
* ★ **backward, fenced** (`S2MuDvd_of_normRes_dvd`; packaged iff
  `S2MuDvd_iff_normRes_dvd`): for MONIC `g` with `deg g ≤ 4 = e'f'·deg Φ′` and `R₃(g)` NOT
  a unit, `R₃(g) ∣ R₃(a) → g ∣µ₂ a`.  **The mechanism is the `modByMonic` remainder, not a
  residual-realization lemma**: the μ₂-cofactor is the literal polynomial quotient
  `a /ₘ g`.  Either the remainder `a %ₘ g` sits strictly above `g·(a /ₘ g)` in value — then
  `a ∼µ₂ g·(a /ₘ g)` by the value criterion — or its value ties/undercuts, and then RP-2's
  strong add law + RP-4's product law would make the NON-UNIT `R₃(g)` divide the
  remainder's graded residual, which is a nonzero CONSTANT (`deg (a %ₘ g) < 4` develops
  only in slots `0, 1`, and parity puts at most one on any grade line —
  `s2GradedRes_eq_C_of_natDegree_lt_four` / `s2NormRes_isUnit_of_natDegree_lt_four`).
  This is published Lemma 5.2's mechanism (the Prop 1.7(2)/1.9 `µ(g) = µ′(g) ↔ φ ∤µ g`
  genre).
* ★ **the carried-key scope** (`S2MuDvd_key_iff`): for `Φ′` itself the residual test is
  VOID (`R₃(Φ′) = 1` is a unit), and the honest translation is the SLOT-0 GATE:
  `Φ′ ∣µ₂ f ↔ f`'s slot-0 development digit is off the grade line.  Forward is KP-0's
  odd-carry engine; backward is the same remainder mechanism (`f %ₘ Φ′` IS the slot-0
  digit, `dev_zero_pin`).  Odd grades are divisible outright (`S2MuDvd_key_of_odd_grade`).
* **both fences machine-witnessed**: `tooth_backward_needs_nonunit` (`(Φ′, 1)`: residual
  divisibility without μ₂-divisibility — the non-unit fence) and Part 8's degree-six
  refuter (the degree fence).

## NODE KP-2 — irreducible residual gives PRIME initial form

* ★ `s2MuIrreducible_of_irreducible_normRes`: monic `g`, `deg g ≤ 4`, `Irreducible (R₃ g)`
  → `S2MuIrreducible g` (KP-0's rendering: nonzero, `∤µ₂ 1`, prime on products) — the
  primality substance of published Lemma 5.2(2)/Theorem 5.7.  Proof: `g ∣µ₂ a·b` pushes
  forward to `R₃(g) ∣ R₃(a)·R₃(b)` (KP-1 forward + RP-10), `K₂[y]`'s UFD structure turns
  irreducibility into primality, and KP-1's backward translation pulls the winner back.
  The row's "nonzero constant term" hypothesis is AUTOMATIC at the landed operators
  (RP-8's `s2NormRes_coeff_zero_ne_zero`); it is restored in the field-shaped wrapper
  `s2_key_criterion_muIrreducible` (the C130fg `key_criterion` hypothesis list, concluding
  the irreducibility conjunct — KP-4's consumable).
* ★ **the honesty fence — naked KP-2 is FALSE** (`tooth_kp2_degree_fence_sharp`): the
  degree-SIX monic `Φ′·(Φ′² + 4x)` has irreducible residual `X + 1` yet is NOT
  μ₂-irreducible — its initial form μ₂-divides `(Φ′·Φ′)·((Φ′²+4x)·(Φ′²+4x))` but neither
  factor (against `Φ′²` by the forward residual test; against `(Φ′²+4x)²` by RP-9's
  trailing-degree law, whose odd×odd carry `+1` no cofactor can cancel).  The degree fence
  of published Lemma 5.2/Theorem 5.7 is essential, not decorative.
* ★ **KP-2 fires at the landed recipe key** (`s2MuIrreducible_lift`):
  `S2MuIrreducible (Φ′² + 4x)` — RP-12's degree-four lift has prime initial form.

## ★★ KP-0's named gap DISCHARGED: `S2KeyPoly Φ′`

The carried key's primality (`S2MuDvd_key_or`) falls out of the slot-0 characterization:
odd-grade factors are divisible outright, and at even×even grades the slot-0 scalars
multiply (RP-4, trivial twist), so two live gates force a live product gate — refuted by
the engine.  With KP-0's `s2MuMinimal_key` and the frame's monicity this closes
`s2KeyPoly_key : S2KeyPoly Φ′` through KP-0's own reduction
(`s2KeyPoly_key_of_muIrreducible`) — published Prop 1.7(4) at the carried key, spelled at
`x² − 2` too (`s2KeyPoly_X_sq_sub_two`).  Note KP-2's residual criterion says NOTHING about
`Φ′` (unit residual); the discharge rides on the carried-key scope of KP-1.

## What this node does NOT claim (honesty scope)

* No `S2MuMinimal` at the recipe degree (KP-3's row) and no assembled `key_criterion`
  field (`S2KeyPoly g` from the full hypothesis list — KP-4's row): here only the
  IRREDUCIBILITY conjunct is produced (`s2_key_criterion_muIrreducible`); in particular
  `S2KeyPoly (Φ′² + 4x)` is NOT claimed (its minimality is open at KP-3).
* No `carried_key_is_key` FIELD instance (KP-6's row is about `keyAt 2 = composedKey`,
  degree 4); `s2KeyPoly_key` is the same genre at the DEVELOPMENT key `Φ′ = keyAt 1`,
  exactly like RP-8's `s2NormRes_key` realization choice (C130rp11's recorded course
  correction).
* No `initial_iff_residual` (KP-7..KP-9) and no `FGMNSourceData`/`FGMNSourceLaws`/
  `ChainRealization` instance (FD-0).
* The backward translation is stated at its honest fences (monic, `deg ≤ 4`, non-unit
  residual); both fences are PROVED essential (Part 7/Part 8), so no wider claim is
  available at these operators without new mechanism.

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements): the
backward-translation statement and its fences (`S2MuDvd_of_normRes_dvd`), the carried-key
characterization (`S2MuDvd_key_iff`), KP-2's statement
(`s2MuIrreducible_of_irreducible_normRes`), the naked-KP-2 refutation
(`tooth_kp2_degree_fence_sharp`), and the named-gap discharge (`s2KeyPoly_key`).

**DEPENDS.** C130kp0 (the predicates + equivalence bank + `S2InitialEquiv_iff_gradedRes` +
`not_S2MuDvd_key_of_even_grade` + `s2MuMinimal_key` + `not_S2MuDvd_key_one` +
`s2KeyPoly_key_of_muIrreducible` + `s2Hgt₂_neg`) · C130rp9 (`s2NormRes_mul`,
`s2GradeOf_mul`, `s2GradedRes_natTrailingDegree_mul`) · C130rp11 (`s2_g_monic`,
`s2_g_natDegree`, `s2_normalized_exists_normRes`, `s2_X_add_one_irreducible`) · C130rp8
(`s2GradeOf` bank, `s2NormRes` bank, `s2NormRes_mul_X_pow_of_exact`,
`s2GradedCoeff_ne_zero_of_slotOnGrade`, `tooth_normRes_key_sq`) · C130rp6
(`s2GradedRes_ne_zero_of_exact`) · C130rp4 (`s2GradedRes_mul_of_exact`) · C130rp2
(`s2GradedRes_add_of_le`, `le_dvSupp_of_exact`, `tooth_sum_exact`,
`tooth_gradedRes_add_exact`) · C130rp1 (`s2SlotOnGrade_iff`, `s2GradedRes_coeff`,
`s2GradedCoeff_eq_zero_of_dvHgt_top`, `s2GradedRes_zero_of_above`, `tooth_gradedRes_key`)
· C130rp0 (`S2ExactGrade` normal forms, `S2ExactGrade_mul`/`_unique`, `tooth_key`) ·
C130s6 (`s2Hgt₂_eq_dvSupp`, `s2Hgt₂_add_ge`, `s2Hgt₂_add_eq`, `toZ` bank,
`dvSupp_eq_inf_range`) · C130nv2 (`dev_zero_pin`) · C131y (`dvSupp_le_term`) · C118a
(`smul_top_pos`) · B.04 (`dev_eq_zero_of_lt`) · C35b/C97 (`key_eq`, `s2Key_natDegree`,
`s2Key`) · C127 (`KeyFrame.stageHeight_zero`, `natDegree_key_pos`) · mathlib
(`modByMonic_add_div`, `modByMonic_eq_zero_iff_dvd`, `degree_modByMonic_lt`,
`modByMonic_eq_self_iff`, the `natTrailingDegree` bank, `isUnit_C`,
`UniqueFactorizationMonoid.irreducible_iff_prime` through the `EuclideanDomain (K₂[y])` →
PID → UFD instance chain).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement touched.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C130kp1

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130nv
open Uniformity.Density.Tower.C130nv2 Uniformity.Density.Tower.C131y
open Uniformity.Density.Tower.C130rp0 Uniformity.Density.Tower.C130rp1
open Uniformity.Density.Tower.C130rp2 Uniformity.Density.Tower.C130rp4
open Uniformity.Density.Tower.C130rp6 Uniformity.Density.Tower.C130rp8
open Uniformity.Density.Tower.C130rp9 Uniformity.Density.Tower.C130rp11
open Uniformity.Density.Tower.C130kp0

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 0 — private copies (the private-copy pattern) -/

/-- private copy of the S2 key-degree numeral: `deg Φ′ = 2`. -/
private theorem key_natDegree_two : ((s2Frame h2 hq).key : Polynomial O).natDegree = 2 := by
  rw [key_eq h2 hq]
  exact s2Key_natDegree

/-! ## Part 1 — ★ NODE KP-1, the FORWARD translation (universal)

μ₂-divisibility maps to divisibility of normalized residuals, with NO hypothesis at all:
`g ∼µ₂ φ·q` forces `R₃(g) = R₃(φ·q)` (KP-0's tie), and RP-10's universal product law
factors the right side.  This is the direction published Prop 1.7's `P` structure gives
for free once Cor 4.12(3) is universal. -/

/-- ★ **KP-1, forward (UNIVERSAL)**: `φ ∣µ₂ g → R₃(φ) ∣ R₃(g)` — no monic, degree, grade,
or nonzero premise.  KP-0's normalized tie `s2NormRes_eq_of_initialEquiv` plus RP-10's
universal `s2NormRes_mul`. -/
theorem normRes_dvd_of_S2MuDvd {φ g : Polynomial O} (h : S2MuDvd h2 hq φ g) :
    s2NormRes h2 hq φ ∣ s2NormRes h2 hq g := by
  obtain ⟨q, hq'⟩ := h
  have heq := s2NormRes_eq_of_initialEquiv h2 hq hq'
  rw [s2NormRes_mul h2 hq] at heq
  exact ⟨s2NormRes h2 hq q, heq⟩

/-! ## Part 2 — the structure of LOW-DEGREE residuals

A polynomial of degree `< 4 = 2·deg Φ′` develops only in slots `0, 1`, and at most ONE of
them sits on any grade line (parity), so its graded residual is a CONSTANT — nonzero at the
exact grade.  This is the pivot of the backward translation: `modByMonic` remainders
against a degree-`≤ 4` divisor are exactly such polynomials, and a non-unit residual can
never divide their (unit) residuals. -/

/-- **low-degree graded residuals are constants**: `deg g < 4` forces
`R_β(g) = C (R_β(g)(0))` at EVERY grade `β` — every coefficient `t ≥ 1` reads an abscissa
`≥ 2`, where the `Φ′`-development of a degree-`< 4` polynomial has already stopped
(B.04 against the degree-2 key).  (The `deg < 4` widening of C130rp11's
`s2_khat_gradedRes_eq_C`.) -/
theorem s2GradedRes_eq_C_of_natDegree_lt_four {g : Polynomial O}
    (hdeg : g.natDegree < 4) (β : ℕ) :
    s2GradedRes h2 hq β g = Polynomial.C ((s2GradedRes h2 hq β g).coeff 0) := by
  refine Polynomial.ext fun t => ?_
  match t with
  | 0 => rw [Polynomial.coeff_C_zero]
  | (t + 1) =>
    rw [Polynomial.coeff_C_of_ne_zero (Nat.succ_ne_zero t), s2GradedRes_coeff]
    refine s2GradedCoeff_eq_zero_of_dvHgt_top h2 hq ?_
    have hdev : dev (s2Frame h2 hq).key g (β % 2 + 2 * (t + 1)) = 0 :=
      dev_eq_zero_of_lt (s2Frame h2 hq).hmonic (s2Frame h2 hq).natDegree_key_pos g _
        (by rw [key_natDegree_two h2 hq]; omega)
    rw [dvHgt, hdev]
    exact (s2Frame h2 hq).stageHeight_zero

/-- **low-degree normalized residuals are units**: a NONZERO `g` of degree `< 4` has
`R₃(g)` a unit of `K₂[y]` (its graded residual is a nonzero constant, and the strip is
trivial on constants). -/
theorem s2NormRes_isUnit_of_natDegree_lt_four {g : Polynomial O} (hg : g ≠ 0)
    (hdeg : g.natDegree < 4) : IsUnit (s2NormRes h2 hq g) := by
  have hex := S2ExactGrade_s2GradeOf h2 hq hg
  have hC := s2GradedRes_eq_C_of_natDegree_lt_four h2 hq hdeg (s2GradeOf h2 hq g)
  have hne := s2GradedRes_ne_zero_of_exact h2 hq hex
  have hγ : (s2GradedRes h2 hq (s2GradeOf h2 hq g) g).coeff 0 ≠ 0 := by
    intro h0
    rw [hC, h0, map_zero] at hne
    exact hne rfl
  rw [s2NormRes_of_exact h2 hq hex, hC, Polynomial.natTrailingDegree_C,
    Function.iterate_zero_apply]
  exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hγ)

/-! ## Part 3 — ★ NODE KP-1, the BACKWARD translation (the remainder mechanism)

The honest converse scope, derived from the proof (published Lemma 5.2's mechanism, the
same one Prop 1.7(2)/1.9's `µ(g) = µ′(g) ↔ φ ∤µ g` criterion rides on): for a MONIC `g` of
degree `≤ 4` with NON-UNIT normalized residual, residual divisibility comes back.  The
witness is the literal polynomial quotient `a /ₘ g`: either the remainder `a %ₘ g` sits
strictly above `g·(a /ₘ g)` in value — and then `a ∼µ₂ g·(a /ₘ g)` on the nose — or the
remainder's value ties/undercuts, in which case its graded residual (a nonzero CONSTANT,
Part 2, because `deg (a %ₘ g) < deg g ≤ 4`) would be divisible by the non-unit `R₃(g)`:
impossible.  NO residual-realization lemma is needed — `modByMonic` supplies the cofactor.

Both fences are ESSENTIAL, machine-witnessed in Part 7: at `(Φ′, 1)` the residual
divisibility `1 ∣ 1` holds but `Φ′ ∤µ₂ 1` (the non-unit fence), and at the degree-6 input
`Φ′·(Φ′² + 4x)` residual divisibility into `(Φ′² + 4x)²` holds but μ₂-divisibility fails
(the degree fence). -/

/-- ★ **KP-1, backward (the honest scope)**: for monic `g` with `deg g ≤ 4` and `R₃(g)` NOT
a unit, `R₃(g) ∣ R₃(a) → g ∣µ₂ a`, with the polynomial quotient `a /ₘ g` as the μ₂-cofactor.
The remainder `a %ₘ g` has degree `< 4`, hence a UNIT residual (Part 2) — so its value can
neither tie nor undercut `g·(a /ₘ g)`'s, and the initial forms match. -/
theorem S2MuDvd_of_normRes_dvd {g a : Polynomial O} (hmon : g.Monic)
    (hdeg : g.natDegree ≤ 4) (hnu : ¬ IsUnit (s2NormRes h2 hq g))
    (hdvd : s2NormRes h2 hq g ∣ s2NormRes h2 hq a) :
    S2MuDvd h2 hq g a := by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact S2MuDvd_zero h2 hq g
  have hmod : a %ₘ g + g * (a /ₘ g) = a := Polynomial.modByMonic_add_div a g
  rcases eq_or_ne (a %ₘ g) 0 with hr0 | hr0
  · exact S2MuDvd_of_dvd h2 hq ((Polynomial.modByMonic_eq_zero_iff_dvd hmon).mp hr0)
  rcases eq_or_ne (a /ₘ g) 0 with hw0 | hw0
  · -- `a /ₘ g = 0`: `a` IS its own remainder, degree `< 4`, so `R₃(a)` is a unit — the
    -- non-unit `R₃(g)` cannot divide it
    exfalso
    have ha : a %ₘ g = a := by rw [hw0, mul_zero, add_zero] at hmod; exact hmod
    have hdega : a.natDegree < 4 := by
      have h1 := Polynomial.natDegree_lt_natDegree hr0
        (Polynomial.degree_modByMonic_lt a hmon)
      rw [ha] at h1
      omega
    exact hnu (isUnit_of_dvd_unit hdvd
      (s2NormRes_isUnit_of_natDegree_lt_four h2 hq ha0 hdega))
  -- both `a %ₘ g` and `a /ₘ g` nonzero
  have hgw0 : g * (a /ₘ g) ≠ 0 := mul_ne_zero hmon.ne_zero hw0
  have hexr := S2ExactGrade_s2GradeOf h2 hq hr0
  have hexgw := S2ExactGrade_s2GradeOf h2 hq hgw0
  have hvr : s2Hgt₂ h2 hq (a %ₘ g)
      = ((s2GradeOf h2 hq (a %ₘ g) : ℕ) : WithTop ℤ) := hexr
  have hvgw : s2Hgt₂ h2 hq (g * (a /ₘ g))
      = ((s2GradeOf h2 hq (g * (a /ₘ g)) : ℕ) : WithTop ℤ) := hexgw
  rcases Nat.lt_or_ge (s2GradeOf h2 hq (g * (a /ₘ g))) (s2GradeOf h2 hq (a %ₘ g))
    with hlt | hge
  · -- ★ the GOAL case: the remainder sits strictly ABOVE — `a ∼µ₂ g·(a /ₘ g)`
    have hltv : s2Hgt₂ h2 hq (g * (a /ₘ g)) < s2Hgt₂ h2 hq (a %ₘ g) := by
      rw [hvr, hvgw]
      exact_mod_cast hlt
    have hadd := s2Hgt₂_add_eq h2 hq (a %ₘ g) (g * (a /ₘ g)) (ne_of_gt hltv)
    rw [hmod] at hadd
    have hva : s2Hgt₂ h2 hq a = s2Hgt₂ h2 hq (g * (a /ₘ g)) := by
      rw [hadd]
      exact min_eq_right (le_of_lt hltv)
    refine ⟨a /ₘ g, Or.inl ⟨?_, hva⟩⟩
    rw [show a - g * (a /ₘ g) = a %ₘ g from sub_eq_of_eq_add hmod.symm, hva]
    exact hltv
  · -- the CONTRADICTION case: the remainder ties or undercuts — then the non-unit `R₃(g)`
    -- divides the remainder's nonzero CONSTANT graded residual
    exfalso
    -- `R₃(g) ∣ R_{βr}(g·(a /ₘ g))` (zero above the grade; the RP-4 product at a tie)
    have hψg : s2NormRes h2 hq g
        ∣ s2GradedRes h2 hq (s2GradeOf h2 hq (a %ₘ g)) (g * (a /ₘ g)) := by
      rcases (ge_iff_le.mp hge).lt_or_eq with hlt' | heq'
      · rw [s2GradedRes_zero_of_above h2 hq
          (show ((s2GradeOf h2 hq (a %ₘ g) : ℕ) : WithTop ℤ)
              < s2Hgt₂ h2 hq (g * (a /ₘ g)) from by rw [hvgw]; exact_mod_cast hlt')]
        exact dvd_zero _
      · have hmul := s2GradedRes_mul_of_exact h2 hq
          (S2ExactGrade_s2GradeOf h2 hq hmon.ne_zero)
          (S2ExactGrade_s2GradeOf h2 hq hw0)
        rw [heq', s2GradeOf_mul h2 hq hmon.ne_zero hw0, hmul]
        have hrec : s2NormRes h2 hq g ∣ s2GradedRes h2 hq (s2GradeOf h2 hq g) g :=
          ⟨Polynomial.X ^ (s2GradedRes h2 hq (s2GradeOf h2 hq g) g).natTrailingDegree,
            (s2NormRes_mul_X_pow_of_exact h2 hq
              (S2ExactGrade_s2GradeOf h2 hq hmon.ne_zero)).symm⟩
        exact Dvd.dvd.mul_left (hrec.mul_right _) _
    -- `R₃(g) ∣ R_{βr}(a)` (zero above; RP-8's reconstruction at a tie)
    have hβr_le_a : ((s2GradeOf h2 hq (a %ₘ g) : ℕ) : WithTop ℤ) ≤ s2Hgt₂ h2 hq a := by
      have hmin := s2Hgt₂_add_ge h2 hq (a %ₘ g) (g * (a /ₘ g))
      rw [hmod] at hmin
      refine le_trans ?_ hmin
      rw [hvr, hvgw]
      exact le_min le_rfl (by exact_mod_cast hge)
    have hψa : s2NormRes h2 hq g
        ∣ s2GradedRes h2 hq (s2GradeOf h2 hq (a %ₘ g)) a := by
      rcases hβr_le_a.lt_or_eq with hlt' | heq'
      · rw [s2GradedRes_zero_of_above h2 hq hlt']
        exact dvd_zero _
      · exact dvd_trans hdvd
          ⟨Polynomial.X ^ (s2GradedRes h2 hq (s2GradeOf h2 hq (a %ₘ g)) a).natTrailingDegree,
            (s2NormRes_mul_X_pow_of_exact h2 hq heq'.symm).symm⟩
    -- combine through RP-2's strong ADD law: `R_{βr}(a %ₘ g) = R_{βr}(a) − R_{βr}(g·(a /ₘ g))`
    have h1 : ((s2GradeOf h2 hq (a %ₘ g) : ℕ) : ℕ∞)
        ≤ dvSupp (s2Frame h2 hq) (g * (a /ₘ g)) 5 2 := by
      rw [(S2ExactGrade_iff_dvSupp h2 hq).mp hexgw]
      exact_mod_cast hge
    have haddres := s2GradedRes_add_of_le h2 hq (le_dvSupp_of_exact h2 hq hexr) h1
    rw [hmod] at haddres
    have hψr : s2NormRes h2 hq g
        ∣ s2GradedRes h2 hq (s2GradeOf h2 hq (a %ₘ g)) (a %ₘ g) := by
      have hsub : s2GradedRes h2 hq (s2GradeOf h2 hq (a %ₘ g)) (a %ₘ g)
          = s2GradedRes h2 hq (s2GradeOf h2 hq (a %ₘ g)) a
            - s2GradedRes h2 hq (s2GradeOf h2 hq (a %ₘ g)) (g * (a /ₘ g)) := by
        rw [haddres]
        ring
      rw [hsub]
      exact dvd_sub hψa hψg
    -- but that graded residual is a nonzero CONSTANT (`deg (a %ₘ g) < 4`) — `R₃(g)` a unit
    have hdegr : (a %ₘ g).natDegree < 4 := by
      have h2' := Polynomial.natDegree_lt_natDegree hr0
        (Polynomial.degree_modByMonic_lt a hmon)
      omega
    have hC := s2GradedRes_eq_C_of_natDegree_lt_four h2 hq hdegr
      (s2GradeOf h2 hq (a %ₘ g))
    have hne := s2GradedRes_ne_zero_of_exact h2 hq hexr
    have hγ : (s2GradedRes h2 hq (s2GradeOf h2 hq (a %ₘ g)) (a %ₘ g)).coeff 0 ≠ 0 := by
      intro h0
      rw [hC, h0, map_zero] at hne
      exact hne rfl
    rw [hC] at hψr
    exact hnu (isUnit_of_dvd_unit hψr
      (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hγ)))

/-! ## Part 4 — ★ NODE KP-1, the packaged translation at its honest scope -/

/-- ★ **NODE KP-1 — the μ-divisibility ↔ residual-divisibility translation** (published
Def 1.2's factor criterion against published Cor 4.9/4.12's residual calculus), at the
honest scope the proofs force: monic `g`, `deg g ≤ 4 = e'f'·deg Φ′`, non-unit residual.
Forward is universal (`normRes_dvd_of_S2MuDvd`); backward is the remainder mechanism. -/
theorem S2MuDvd_iff_normRes_dvd {g a : Polynomial O} (hmon : g.Monic)
    (hdeg : g.natDegree ≤ 4) (hnu : ¬ IsUnit (s2NormRes h2 hq g)) :
    S2MuDvd h2 hq g a ↔ s2NormRes h2 hq g ∣ s2NormRes h2 hq a :=
  ⟨normRes_dvd_of_S2MuDvd h2 hq, S2MuDvd_of_normRes_dvd h2 hq hmon hdeg hnu⟩

/-! ## Part 5 — ★ NODE KP-2: irreducible residual gives PRIME initial form

Published Lemma 5.2(2)'s primality substance: `R₃(g)` irreducible in `K₂[y]` makes `g`'s
initial form prime in the `S2MuDvd` sense (KP-0's `S2MuIrreducible` rendering).  The
`(R₃ g)(0) ≠ 0` hypothesis of the row is AUTOMATIC at the landed operators (RP-8's
`s2NormRes_coeff_zero_ne_zero`: EVERY nonzero input has nonzero residual constant term,
because the strip removes the whole trailing `y`-power), so the honest hypothesis set is
monic + degree fence + irreducibility; the redundant hypothesis is restored in the
field-shaped Part 6 wrapper. -/

/-- ★ **NODE KP-2 — residual primality**: monic `g` with `deg g ≤ 4` and `R₃(g)`
IRREDUCIBLE is `S2MuIrreducible` — nonzero, `g ∤µ₂ 1`, and prime on products.  Primality:
`g ∣µ₂ a·b` pushes forward to `R₃(g) ∣ R₃(a)·R₃(b)` (KP-1 forward + RP-10's universal
product law), `K₂[y]`'s UFD structure turns irreducibility into primality, and KP-1's
backward translation pulls the winning factor back. -/
theorem s2MuIrreducible_of_irreducible_normRes {g : Polynomial O} (hmon : g.Monic)
    (hdeg : g.natDegree ≤ 4) (hirr : Irreducible (s2NormRes h2 hq g)) :
    S2MuIrreducible h2 hq g := by
  refine ⟨hmon.ne_zero, ?_, ?_⟩
  · -- properness: `g ∣µ₂ 1` would make the irreducible residual divide `R₃(1) = 1`
    intro hone
    have hd := normRes_dvd_of_S2MuDvd h2 hq hone
    rw [s2NormRes_one h2 hq] at hd
    exact hirr.not_isUnit (isUnit_of_dvd_one hd)
  · -- primality on products
    intro x y hxy
    have hd := normRes_dvd_of_S2MuDvd h2 hq hxy
    rw [s2NormRes_mul h2 hq] at hd
    have hprime : Prime (s2NormRes h2 hq g) :=
      UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
    rcases hprime.2.2 _ _ hd with hda | hdb
    · exact Or.inl (S2MuDvd_of_normRes_dvd h2 hq hmon hdeg hirr.not_isUnit hda)
    · exact Or.inr (S2MuDvd_of_normRes_dvd h2 hq hmon hdeg hirr.not_isUnit hdb)

/-! ## Part 6 — the CARRIED KEY: `Φ′`'s divisibility test, primality, and `S2KeyPoly Φ′`

`R₃(Φ′) = 1` is a UNIT, so KP-2's residual criterion says nothing about `Φ′` itself — the
carried key's translation (the KP-1 row's "needed scopes" clause, second scope) is the
SLOT-0 GATE instead: `Φ′ ∣µ₂ f ↔ f`'s slot-0 development digit is OFF the grade line
(equivalently, the initial `y`-order of `R_β(f)` is positive once parity is accounted).
Forward is KP-0's odd-carry engine; backward is the SAME remainder mechanism as Part 3 —
`f %ₘ Φ′` IS the slot-0 digit (`dev_zero_pin`), and the failed gate says exactly that its
value `2·dvHgt(f,0)` sits strictly above `β`.  Primality then falls out because the gate
scalar is MULTIPLICATIVE at even×even grades (RP-4's product law with trivial twist), and
odd grades are divisible outright (parity keeps slot 0 off odd lines).  This discharges
KP-0's named gap: ★ `S2KeyPoly Φ′` (published Prop 1.7(4) at the carried key). -/

/-- **the carried-key test, forward**: if `f`'s slot-0 digit sits ON the grade line, then
`Φ′ ∤µ₂ f` — the gate forces `β = 2·h₀` EVEN with NONZERO residual scalar (RP-8's on-line
read), and KP-0's odd-carry engine fires. -/
theorem not_S2MuDvd_key_of_slotOnGrade {β : ℕ} {f : Polynomial O}
    (hf : S2ExactGrade h2 hq β f) (hgate : S2SlotOnGrade h2 hq β f 0) :
    ¬ S2MuDvd h2 hq ((s2Frame h2 hq).key : Polynomial O) f := by
  obtain ⟨m, -, hline⟩ := (s2SlotOnGrade_iff h2 hq).mp hgate
  have heven : 2 ∣ β := ⟨m, by omega⟩
  have hc : (s2GradedRes h2 hq β f).coeff 0 ≠ 0 := by
    have h := s2GradedCoeff_ne_zero_of_slotOnGrade h2 hq hgate
    rw [Nat.zero_div] at h
    rw [s2GradedRes_coeff]
    exact h
  exact not_S2MuDvd_key_of_even_grade h2 hq hf heven hc

/-- ★ **the carried-key test, backward (the remainder mechanism at `Φ′`)**: if `f`'s slot-0
digit is OFF the grade line, then `Φ′ ∣µ₂ f`, with the polynomial quotient `f /ₘ Φ′` as the
μ₂-cofactor — the remainder `f %ₘ Φ′` IS the slot-0 digit, and off-line means its value
`2·dvHgt(f,0)` sits strictly above `µ₂(f) = β`. -/
theorem S2MuDvd_key_of_not_slotOnGrade {β : ℕ} {f : Polynomial O}
    (hf : S2ExactGrade h2 hq β f) (hgate : ¬ S2SlotOnGrade h2 hq β f 0) :
    S2MuDvd h2 hq ((s2Frame h2 hq).key : Polynomial O) f := by
  have hkeymon : ((s2Frame h2 hq).key : Polynomial O).Monic := (s2Frame h2 hq).hmonic
  have hmod : f %ₘ (s2Frame h2 hq).key
      + (s2Frame h2 hq).key * (f /ₘ (s2Frame h2 hq).key) = f :=
    Polynomial.modByMonic_add_div f ((s2Frame h2 hq).key : Polynomial O)
  rcases eq_or_ne (f %ₘ (s2Frame h2 hq).key) 0 with hr0 | hr0
  · exact S2MuDvd_of_dvd h2 hq ((Polynomial.modByMonic_eq_zero_iff_dvd hkeymon).mp hr0)
  -- the remainder is a SHORT digit
  have hdegr : (f %ₘ (s2Frame h2 hq).key).natDegree < 2 := by
    have h1 := Polynomial.natDegree_lt_natDegree hr0
      (Polynomial.degree_modByMonic_lt f hkeymon)
    have h2' := key_natDegree_two h2 hq
    omega
  have hdevr : dev (s2Frame h2 hq).key (f %ₘ (s2Frame h2 hq).key) 0
      = f %ₘ (s2Frame h2 hq).key := by
    rw [dev_zero_pin]
    exact (Polynomial.modByMonic_eq_self_iff hkeymon).mpr
      (Polynomial.degree_modByMonic_lt f hkeymon)
  -- its cleared value IS the slot-0 term `2 • dvHgt(f, 0)` of `f`
  have hsupp_r : dvSupp (s2Frame h2 hq) (f %ₘ (s2Frame h2 hq).key) 5 2
      = 2 • dvHgt (s2Frame h2 hq) f 0 := by
    rw [dvSupp_eq_inf_range (s2Frame h2 hq) (by norm_num : (0 : ℕ) < 2) _ (M := 2) hdegr,
      show Finset.range 2 = {0, 1} from rfl, Finset.inf_insert, Finset.inf_singleton]
    have hdev1 : dev (s2Frame h2 hq).key (f %ₘ (s2Frame h2 hq).key) 1 = 0 :=
      dev_eq_zero_of_lt (s2Frame h2 hq).hmonic (s2Frame h2 hq).natDegree_key_pos _ 1
        (by rw [key_natDegree_two h2 hq]; omega)
    have hhgt1 : dvHgt (s2Frame h2 hq) (f %ₘ (s2Frame h2 hq).key) 1 = ⊤ := by
      rw [dvHgt, hdev1]
      exact (s2Frame h2 hq).stageHeight_zero
    rw [hhgt1, C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2), top_add,
      min_eq_left le_top, Nat.cast_zero, mul_zero, add_zero]
    rw [show dvHgt (s2Frame h2 hq) (f %ₘ (s2Frame h2 hq).key) 0
        = dvHgt (s2Frame h2 hq) f 0 from by rw [dvHgt, hdevr, dvHgt, dev_zero_pin]]
  -- the failed gate says: that term sits STRICTLY above the grade
  have hle : ((β : ℕ) : ℕ∞) ≤ 2 • dvHgt (s2Frame h2 hq) f 0 := by
    have hterm := dvSupp_le_term (s2Frame h2 hq) f 5 (by norm_num : (0 : ℕ) < 2) 0
    rw [(S2ExactGrade_iff_dvSupp h2 hq).mp hf] at hterm
    simpa using hterm
  have hne : 2 • dvHgt (s2Frame h2 hq) f 0 ≠ ((β : ℕ) : ℕ∞) := by
    intro heq
    have hfin : dvHgt (s2Frame h2 hq) f 0 ≠ ⊤ := by
      intro htop
      rw [htop, C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2)] at heq
      exact WithTop.top_ne_coe heq
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
    refine hgate ((s2SlotOnGrade_iff h2 hq).mpr ⟨m, hm.symm, ?_⟩)
    rw [← hm, nsmul_eq_mul] at heq
    have h2m : (2 * m : ℕ) = β := by exact_mod_cast heq
    omega
  have hltE : ((β : ℕ) : ℕ∞) < 2 • dvHgt (s2Frame h2 hq) f 0 :=
    lt_of_le_of_ne hle (Ne.symm hne)
  -- lift to the value level: `µ₂(f) = β < µ₂(f %ₘ Φ′)`
  have hgt : s2Hgt₂ h2 hq f < s2Hgt₂ h2 hq (f %ₘ (s2Frame h2 hq).key) := by
    have hvf : s2Hgt₂ h2 hq f = (β : WithTop ℤ) := hf
    rw [hvf, s2Hgt₂_eq_dvSupp, hsupp_r,
      show (β : WithTop ℤ) = toZ ((β : ℕ) : ℕ∞) from by norm_cast]
    exact toZ_lt_toZ_iff.mpr hltE
  -- assemble the initial equivalence `f ∼µ₂ Φ′·(f /ₘ Φ′)`
  have hkw : ((s2Frame h2 hq).key : Polynomial O) * (f /ₘ (s2Frame h2 hq).key)
      = f - f %ₘ (s2Frame h2 hq).key := (sub_eq_of_eq_add' hmod.symm).symm
  have hval_kw : s2Hgt₂ h2 hq
      (((s2Frame h2 hq).key : Polynomial O) * (f /ₘ (s2Frame h2 hq).key))
      = s2Hgt₂ h2 hq f := by
    rw [hkw, sub_eq_add_neg,
      s2Hgt₂_add_eq h2 hq _ _ (by rw [s2Hgt₂_neg h2 hq]; exact ne_of_lt hgt),
      s2Hgt₂_neg h2 hq]
    exact min_eq_left (le_of_lt hgt)
  refine ⟨f /ₘ (s2Frame h2 hq).key, Or.inl ⟨?_, hval_kw.symm⟩⟩
  rw [show f - ((s2Frame h2 hq).key : Polynomial O) * (f /ₘ (s2Frame h2 hq).key)
      = f %ₘ (s2Frame h2 hq).key from by rw [hkw]; ring]
  exact hgt

/-- ★ **the carried-key translation** (the KP-1 row's SECOND honest scope — `Φ′`'s own
divisibility test, where the residual test is void because `R₃(Φ′) = 1`): at the exact
grade, `Φ′ ∣µ₂ f ↔ f`'s slot-0 digit is OFF the grade line. -/
theorem S2MuDvd_key_iff {β : ℕ} {f : Polynomial O} (hf : S2ExactGrade h2 hq β f) :
    S2MuDvd h2 hq ((s2Frame h2 hq).key : Polynomial O) f
      ↔ ¬ S2SlotOnGrade h2 hq β f 0 :=
  ⟨fun hdvd hgate => not_S2MuDvd_key_of_slotOnGrade h2 hq hf hgate hdvd,
    S2MuDvd_key_of_not_slotOnGrade h2 hq hf⟩

/-- **odd grades are `Φ′`-divisible outright**: slot 0 (even abscissa) is never on an odd
grade line (RP-1's parity), so the backward test always fires. -/
theorem S2MuDvd_key_of_odd_grade {β : ℕ} {f : Polynomial O}
    (hf : S2ExactGrade h2 hq β f) (hodd : β % 2 = 1) :
    S2MuDvd h2 hq ((s2Frame h2 hq).key : Polynomial O) f :=
  S2MuDvd_key_of_not_slotOnGrade h2 hq hf fun hgate => by
    obtain ⟨m, -, hline⟩ := (s2SlotOnGrade_iff h2 hq).mp hgate
    omega

/-- ★ **the carried key's initial form is PRIME on products**: `Φ′ ∣µ₂ a·b → Φ′ ∣µ₂ a ∨
Φ′ ∣µ₂ b`.  Odd-grade factors are divisible outright; at even×even grades the slot-0
scalars MULTIPLY (RP-4's product law, trivial twist), so if both factors kept their slot-0
gates the product would keep its own — refuting the hypothesis through the engine. -/
theorem S2MuDvd_key_or (a b : Polynomial O)
    (hdvd : S2MuDvd h2 hq ((s2Frame h2 hq).key : Polynomial O) (a * b)) :
    S2MuDvd h2 hq ((s2Frame h2 hq).key : Polynomial O) a
      ∨ S2MuDvd h2 hq ((s2Frame h2 hq).key : Polynomial O) b := by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact Or.inl (S2MuDvd_zero h2 hq _)
  rcases eq_or_ne b 0 with rfl | hb0
  · exact Or.inr (S2MuDvd_zero h2 hq _)
  have hexa := S2ExactGrade_s2GradeOf h2 hq ha0
  have hexb := S2ExactGrade_s2GradeOf h2 hq hb0
  rcases Nat.mod_two_eq_zero_or_one (s2GradeOf h2 hq a) with hpa | hpa
  swap
  · exact Or.inl (S2MuDvd_key_of_odd_grade h2 hq hexa hpa)
  rcases Nat.mod_two_eq_zero_or_one (s2GradeOf h2 hq b) with hpb | hpb
  swap
  · exact Or.inr (S2MuDvd_key_of_odd_grade h2 hq hexb hpb)
  by_cases hga : S2SlotOnGrade h2 hq (s2GradeOf h2 hq a) a 0
  swap
  · exact Or.inl (S2MuDvd_key_of_not_slotOnGrade h2 hq hexa hga)
  by_cases hgb : S2SlotOnGrade h2 hq (s2GradeOf h2 hq b) b 0
  swap
  · exact Or.inr (S2MuDvd_key_of_not_slotOnGrade h2 hq hexb hgb)
  -- both slot-0 gates fire: even product grade with NONZERO scalar — the engine refutes
  exfalso
  have hexab := S2ExactGrade_mul h2 hq hexa hexb
  have heven : 2 ∣ s2GradeOf h2 hq a + s2GradeOf h2 hq b := by omega
  have hca : (s2GradedRes h2 hq (s2GradeOf h2 hq a) a).coeff 0 ≠ 0 := by
    have h := s2GradedCoeff_ne_zero_of_slotOnGrade h2 hq hga
    rw [Nat.zero_div] at h
    rw [s2GradedRes_coeff]
    exact h
  have hcb : (s2GradedRes h2 hq (s2GradeOf h2 hq b) b).coeff 0 ≠ 0 := by
    have h := s2GradedCoeff_ne_zero_of_slotOnGrade h2 hq hgb
    rw [Nat.zero_div] at h
    rw [s2GradedRes_coeff]
    exact h
  have hcab : (s2GradedRes h2 hq (s2GradeOf h2 hq a + s2GradeOf h2 hq b) (a * b)).coeff 0
      ≠ 0 := by
    rw [s2GradedRes_mul_of_exact h2 hq hexa hexb, hpa, hpb,
      show (0 * 0 : ℕ) = 0 from rfl, pow_zero, one_mul, Polynomial.mul_coeff_zero]
    exact mul_ne_zero hca hcb
  exact not_S2MuDvd_key_of_even_grade h2 hq hexab heven hcab hdvd

/-- ★ **`Φ′` IS μ₂-irreducible** — nonzero (monic), proper (KP-0's `not_S2MuDvd_key_one`),
and prime on products (`S2MuDvd_key_or`).  The μ₂-irreducibility clause of published Prop
1.7(4) for the carried key. -/
theorem s2MuIrreducible_key :
    S2MuIrreducible h2 hq ((s2Frame h2 hq).key : Polynomial O) :=
  ⟨(s2Frame h2 hq).hmonic.ne_zero, not_S2MuDvd_key_one h2 hq,
    fun a b hab => S2MuDvd_key_or h2 hq a b hab⟩

/-- ★★ **`S2KeyPoly Φ′` — KP-0's named gap, DISCHARGED** (published Prop 1.7(4): the
carried key `φ₂ = Φ′` is a key polynomial for `µ₂`): monic (the frame's), μ₂-minimal
(KP-0's `s2MuMinimal_key`), μ₂-irreducible (above). -/
theorem s2KeyPoly_key : S2KeyPoly h2 hq ((s2Frame h2 hq).key : Polynomial O) :=
  s2KeyPoly_key_of_muIrreducible h2 hq (s2MuIrreducible_key h2 hq)

/-- `S2KeyPoly Φ′`, spelled at the explicit polynomial `x² − 2` (C97's `s2Key`). -/
theorem s2KeyPoly_X_sq_sub_two :
    S2KeyPoly h2 hq (Polynomial.X ^ 2 - Polynomial.C (2 : O)) := by
  have h := s2KeyPoly_key h2 hq
  rwa [key_eq h2 hq,
    show s2Key O = Polynomial.X ^ 2 - Polynomial.C (2 : O) from rfl] at h

/-! ## Part 7 — the KP-4 consumable, the positive tooth, and the non-unit fence -/

/-- **the `key_criterion`-shaped irreducibility conjunct** (KP-4's consumable): the C130fg
`FGMNSourceLaws.key_criterion` hypothesis list at the landed `r = 1` realization
(`(e', f') = (2, 1)`, `keyAt 1 = Φ′`), concluding the μ₂-IRREDUCIBILITY conjunct of
`S2KeyPoly g`.  The `(R₃ g)(0) ≠ 0` and `deg R₃(g) = f'` hypotheses are carried for
field-shape fidelity; the proof consumes only monic + the degree numeral + irreducibility
(the constant-term clause is AUTOMATIC at the landed operators, RP-8). -/
theorem s2_key_criterion_muIrreducible :
    ∀ g : Polynomial O, g.Monic →
      g.natDegree = 2 * 1 * ((s2Frame h2 hq).key : Polynomial O).natDegree →
      Irreducible (s2NormRes h2 hq g) →
      (s2NormRes h2 hq g).natDegree = 1 →
      (s2NormRes h2 hq g).coeff 0 ≠ 0 →
      S2MuIrreducible h2 hq g := by
  intro g hmon hdeg hirr _ _
  refine s2MuIrreducible_of_irreducible_normRes h2 hq hmon ?_ hirr
  rw [hdeg, key_natDegree_two h2 hq]

/-- ★ **tooth (the degree-four NEW key is μ₂-irreducible)**: RP-12's landed lift `Φ′² + 4x`
(monic, degree `4`, residual `X + 1` irreducible) satisfies KP-2's criterion, so its
initial form is PRIME.  (Its μ₂-minimality is KP-3's row; `S2KeyPoly (Φ′² + 4x)` completes
at KP-4 — not claimed here.) -/
theorem s2MuIrreducible_lift :
    S2MuIrreducible h2 hq (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
      + Polynomial.C (4 : O) * Polynomial.X) := by
  refine s2MuIrreducible_of_irreducible_normRes h2 hq (s2_g_monic h2 hq)
    (le_of_eq (s2_g_natDegree h2 hq)) ?_
  rw [s2_normalized_exists_normRes h2 hq]
  exact s2_X_add_one_irreducible h2 hq

/-- **tooth (the NON-UNIT fence is essential)**: at `(Φ′, 1)` residual divisibility holds —
`R₃(Φ′) = 1 ∣ 1 = R₃(1)` — but `Φ′ ∤µ₂ 1` (KP-0).  The backward translation genuinely
needs `¬ IsUnit (R₃ g)`; unit-residual divisors are governed by the slot-0 gate instead
(Part 6). -/
theorem tooth_backward_needs_nonunit :
    (s2NormRes h2 hq ((s2Frame h2 hq).key : Polynomial O)
        ∣ s2NormRes h2 hq (1 : Polynomial O))
      ∧ ¬ S2MuDvd h2 hq ((s2Frame h2 hq).key : Polynomial O) (1 : Polynomial O) := by
  constructor
  · rw [s2NormRes_key h2 hq, s2NormRes_one h2 hq]
  · exact not_S2MuDvd_key_one h2 hq

/-! ## Part 8 — ★ the honesty fence: NAKED KP-2 is FALSE (machine-refuted)

The row's literal reading — "irreducible residual with nonzero constant term gives prime
initial form", with NO degree fence — is REFUTED at the landed operators: the degree-SIX
monic `Φ′·(Φ′² + 4x)` has irreducible residual `X + 1` (constant term nonzero, as always),
yet its initial form is a PRODUCT of two primes: it μ₂-divides `(Φ′·Φ′)·((Φ′²+4x)·(Φ′²+4x))`
but divides NEITHER factor.  Against `Φ′·Φ′` the residual test refutes (`X+1 ∤ 1`); against
`(Φ′²+4x)²` the residual test PASSES (`X+1 ∣ (X+1)²`) and the refutation is the initial
`y`-order: RP-9's trailing-degree law forces every `Φ′·(Φ′²+4x)·q` at grade 20 to carry the
odd×odd twist `+1`, while `R₂₀((Φ′²+4x)²) = (X+1)²` has trailing order `0`.  So KP-2's
degree fence `deg g ≤ 4 = e'f'·deg Φ′` is ESSENTIAL — the degree hypothesis printed in
published Lemma 5.2/Theorem 5.7 is not decorative.  (This same witness shows the BACKWARD
translation's degree fence is essential: residual divisibility without μ₂-divisibility at
degree 6.) -/

/-- the refuter's residual: `R₃(Φ′·(Φ′² + 4x)) = X + 1` — irreducible, via the universal
product law. -/
theorem tooth_normRes_key_mul_lift :
    s2NormRes h2 hq (((s2Frame h2 hq).key : Polynomial O)
      * (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
        + Polynomial.C (4 : O) * Polynomial.X))
      = Polynomial.X + 1 := by
  rw [s2NormRes_mul h2 hq, s2NormRes_key h2 hq, s2_normalized_exists_normRes h2 hq, one_mul]

/-- ★ **the naked-KP-2 refutation** (the honesty fence, machine-checked): the degree-six
monic `Φ′·(Φ′² + 4x)` has IRREDUCIBLE residual yet is NOT μ₂-irreducible — KP-2's degree
fence is sharp at the very next composite degree. -/
theorem tooth_kp2_degree_fence_sharp :
    (((s2Frame h2 hq).key : Polynomial O)
        * (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
          + Polynomial.C (4 : O) * Polynomial.X)).Monic
    ∧ Irreducible (s2NormRes h2 hq (((s2Frame h2 hq).key : Polynomial O)
        * (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
          + Polynomial.C (4 : O) * Polynomial.X)))
    ∧ ¬ S2MuIrreducible h2 hq (((s2Frame h2 hq).key : Polynomial O)
        * (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
          + Polynomial.C (4 : O) * Polynomial.X)) := by
  refine ⟨(s2Frame h2 hq).hmonic.mul (s2_g_monic h2 hq), ?_, ?_⟩
  · rw [tooth_normRes_key_mul_lift h2 hq]
    exact s2_X_add_one_irreducible h2 hq
  · rintro ⟨-, -, hprime⟩
    have hg₄ : S2ExactGrade h2 hq 10
        (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
          + Polynomial.C (4 : O) * Polynomial.X) := tooth_sum_exact h2 hq
    have hg₄0 : (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
        + Polynomial.C (4 : O) * Polynomial.X) ≠ 0 := (s2_g_monic h2 hq).ne_zero
    -- the split product: (Φ′·Φ′)·((Φ′²+4x)·(Φ′²+4x)) = (Φ′·(Φ′²+4x))²
    have hdvd : S2MuDvd h2 hq (((s2Frame h2 hq).key : Polynomial O)
        * (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
          + Polynomial.C (4 : O) * Polynomial.X))
        ((((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key)
          * ((((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
              + Polynomial.C (4 : O) * Polynomial.X)
            * (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
              + Polynomial.C (4 : O) * Polynomial.X))) :=
      S2MuDvd_of_dvd h2 hq ⟨((s2Frame h2 hq).key : Polynomial O)
        * (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
          + Polynomial.C (4 : O) * Polynomial.X), by ring⟩
    rcases hprime _ _ hdvd with hL | hR
    · -- against `Φ′·Φ′` the FORWARD translation refutes: `X + 1 ∣ R₃(Φ′²) = 1`
      have hd := normRes_dvd_of_S2MuDvd h2 hq hL
      rw [tooth_normRes_key_mul_lift h2 hq, tooth_normRes_key_sq h2 hq] at hd
      exact (s2_X_add_one_irreducible h2 hq).not_isUnit (isUnit_of_dvd_one hd)
    · -- against `(Φ′²+4x)²` the refutation is the initial `y`-order (RP-9's carry)
      obtain ⟨q, hq'⟩ := hR
      rcases eq_or_ne q 0 with rfl | hq0
      · rw [mul_zero] at hq'
        exact mul_ne_zero hg₄0 hg₄0 ((S2InitialEquiv_zero_right h2 hq).mp hq')
      have hexq := S2ExactGrade_s2GradeOf h2 hq hq0
      have hex15 : S2ExactGrade h2 hq 15 (((s2Frame h2 hq).key : Polynomial O)
          * (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
            + Polynomial.C (4 : O) * Polynomial.X)) := by
        have h := S2ExactGrade_mul h2 hq (tooth_key h2 hq) hg₄
        rwa [show (5 + 10 : ℕ) = 15 from rfl] at h
      have hex20 : S2ExactGrade h2 hq 20
          ((((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
              + Polynomial.C (4 : O) * Polynomial.X)
            * (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key
              + Polynomial.C (4 : O) * Polynomial.X)) := by
        have h := S2ExactGrade_mul h2 hq hg₄ hg₄
        rwa [show (10 + 10 : ℕ) = 20 from rfl] at h
      have hex20' := S2ExactGrade_of_initialEquiv h2 hq hex20 hq'
      have hexprod := S2ExactGrade_mul h2 hq hex15 hexq
      have hβq : 15 + s2GradeOf h2 hq q = 20 :=
        S2ExactGrade_unique h2 hq hexprod hex20'
      have hq5 : s2GradeOf h2 hq q = 5 := by omega
      rw [hq5] at hexq hexprod
      -- residual equality at the common exact grade 20
      have hres := (S2InitialEquiv_iff_gradedRes h2 hq hex20
        (by rwa [show (15 + 5 : ℕ) = 20 from rfl] at hexprod)).mp hq'
      -- LHS: `R₂₀((Φ′²+4x)²) = (X+1)·(X+1)`, trailing order 0
      have hLmul := s2GradedRes_mul_of_exact h2 hq hg₄ hg₄
      rw [show (10 + 10 : ℕ) = 20 from rfl, tooth_gradedRes_add_exact h2 hq,
        show (10 % 2 * (10 % 2) : ℕ) = 0 from rfl, pow_zero, one_mul] at hLmul
      have hntdL : ((Polynomial.X + 1) * (Polynomial.X + 1)
          : Polynomial ((s2DepthTwo h2 hq).fld 2)).natTrailingDegree = 0 :=
        Nat.le_zero.mp (Polynomial.natTrailingDegree_le_of_ne_zero (by
          rw [Polynomial.mul_coeff_zero, Polynomial.coeff_add, Polynomial.coeff_X_zero,
            Polynomial.coeff_one_zero, zero_add, one_mul]
          exact one_ne_zero))
      -- RHS: RP-9's trailing law carries the odd×odd `+1`
      have hntd15 := s2GradedRes_natTrailingDegree_mul h2 hq (tooth_key h2 hq) hg₄
      rw [show (5 + 10 : ℕ) = 15 from rfl, tooth_gradedRes_key h2 hq,
        tooth_gradedRes_add_exact h2 hq, Polynomial.natTrailingDegree_one] at hntd15
      have hntdX1 : (Polynomial.X + 1
          : Polynomial ((s2DepthTwo h2 hq).fld 2)).natTrailingDegree = 0 :=
        Nat.le_zero.mp (Polynomial.natTrailingDegree_le_of_ne_zero (by
          rw [Polynomial.coeff_add, Polynomial.coeff_X_zero, Polynomial.coeff_one_zero,
            zero_add]
          exact one_ne_zero))
      rw [hntdX1] at hntd15
      have hntdprod := s2GradedRes_natTrailingDegree_mul h2 hq hex15 hexq
      rw [show (15 + 5 : ℕ) = 20 from rfl, hntd15] at hntdprod
      have htr := congrArg Polynomial.natTrailingDegree hres
      rw [hLmul, hntdL, hntdprod] at htr
      -- 0 = (0 + 0 + 1%…) + ntd(R₅ q) + 1 — impossible
      omega

end S2

end Uniformity.Density.Tower.C130kp1

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130kp1.normRes_dvd_of_S2MuDvd
#print axioms Uniformity.Density.Tower.C130kp1.s2GradedRes_eq_C_of_natDegree_lt_four
#print axioms Uniformity.Density.Tower.C130kp1.s2NormRes_isUnit_of_natDegree_lt_four
#print axioms Uniformity.Density.Tower.C130kp1.S2MuDvd_of_normRes_dvd
#print axioms Uniformity.Density.Tower.C130kp1.S2MuDvd_iff_normRes_dvd
#print axioms Uniformity.Density.Tower.C130kp1.s2MuIrreducible_of_irreducible_normRes
#print axioms Uniformity.Density.Tower.C130kp1.not_S2MuDvd_key_of_slotOnGrade
#print axioms Uniformity.Density.Tower.C130kp1.S2MuDvd_key_of_not_slotOnGrade
#print axioms Uniformity.Density.Tower.C130kp1.S2MuDvd_key_iff
#print axioms Uniformity.Density.Tower.C130kp1.S2MuDvd_key_of_odd_grade
#print axioms Uniformity.Density.Tower.C130kp1.S2MuDvd_key_or
#print axioms Uniformity.Density.Tower.C130kp1.s2MuIrreducible_key
#print axioms Uniformity.Density.Tower.C130kp1.s2KeyPoly_key
#print axioms Uniformity.Density.Tower.C130kp1.s2KeyPoly_X_sq_sub_two
#print axioms Uniformity.Density.Tower.C130kp1.s2_key_criterion_muIrreducible
#print axioms Uniformity.Density.Tower.C130kp1.s2MuIrreducible_lift
#print axioms Uniformity.Density.Tower.C130kp1.tooth_backward_needs_nonunit
#print axioms Uniformity.Density.Tower.C130kp1.tooth_normRes_key_mul_lift
#print axioms Uniformity.Density.Tower.C130kp1.tooth_kp2_degree_fence_sharp

end AxCheck
