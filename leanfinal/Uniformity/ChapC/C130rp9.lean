/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130rp8

/-!
# Uniformity.ChapC.C130rp9 — S2-source plan nodes RP-9/RP-10 — normalized_mul CLOSED

**S2-source plan nodes RP-9 + RP-10** (`docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6
rows RP-9 "Initial y-orders add under products, including all zero cases" and RP-10 "Prove
the universal normalized residual product law"), the third inductive core — on RP-8's
normalized residual `s2NormRes` and its reconstruction (C130rp8), RP-4's twisted product
law (C130rp4), RP-0's grade arithmetic (C130rp0), under the U14 adjudication
(`docs/in-progress/COR412_ADJUDICATION_2026-08-25.md` §1/§7: `normalized_mul` is PLAIN and
UNRESTRICTED per published Cor 4.12(3) — "for all `g, h ∈ K[x]`" — because the `y`-order
strip absorbs exactly the carry twist).

## NODE RP-9 — the `y`-order arithmetic (initial `y`-orders ADD, with the twist bookkeeping)

The initial `y`-order of the graded residual is its trailing degree, certified equal to
Def 3.15's strip amount `j₀ = ⌊s(g)/e₂⌋ = dvSideMin g / 2` by RP-8's strip pin.  The
addition law is DERIVED from RP-4's twist rather than re-fought on the Newton side:

* ★ **`s2GradedRes_natTrailingDegree_mul`** — at exact grades,
  `j₀(g·z) = j₀(g) + j₀(z) + (β%2)·(β′%2)`: take `natTrailingDegree` of the twisted product
  identity `R_{β+β′}(g·z) = y^{(β%2)(β′%2)}·R_β(g)·R_{β′}(z)` (RP-4); trailing degrees add
  over the residue-field domain because both graded residuals are nonzero at exact grade
  (RP-5/RP-6).  The carry term IS U14 §7's floor identity `⌊(s+s′)/2⌋ = ⌊s/2⌋+⌊s′/2⌋+carry`,
  now as a theorem instead of bookkeeping.
* **`dvSideMin_div_two_mul_of_exact`** — the same law in published coordinates
  (`j₀ = dvSideMin/2`, through RP-8's strip pin on all three polynomials): the brief's
  display `j₀(g·h) = j₀(g) + j₀(h) + (β%2)(β′%2)` verbatim.
* ★ **`dvSideMin_mul_of_exact`** — the UNHALVED endpoint law: the left endpoints themselves
  add, `s(g·z) = s(g) + s(z)` (U14 §7's "the left endpoints add under multiplication").
  NV-2/NV-3 landed only the `≤` direction (`s2_dvSideMin_mul_le`, under explicit endpoint
  height hypotheses); the EQUALITY falls out here from the halved law + the slot-parity pin
  `dvSideMin ≡ β (mod 2)` — no new Newton-side work.
* **grade companion** `s2GradeOf_mul`: the total extracted grades add,
  `μ₂(g·z) = μ₂(g) + μ₂(z)` for nonzero `g, z` (RP-0's `S2ExactGrade_mul` through the
  extraction), and the total-anchoring form `s2GradedRes_natTrailingDegree_mul_total`.
* **all zero cases** (the row's clause): the zero polynomial has NO exact grade
  (RP-0's `S2ExactGrade_zero_false`), so the exact-grade laws have no zero instance to
  state; the total carriers are pinned at `0` anyway (`s2GradedRes_natTrailingDegree_zero`:
  `R_β(0) = 0` has trailing degree `0`), and the zero cases of the NORMALIZED law are
  published Def 3.15's own `R₃(0) = 0` clause, discharged inside RP-10's universal law and
  regression-toothed below.

## NODE RP-10 — ★ the universal plain normalized product law (published Cor 4.12(3))

* ★ **`s2NormRes_mul`** — `R₃(g·z) = R₃(g)·R₃(z)` for ALL `g, z : Polynomial O`, no grade
  premise, no parity premise, no nonzero premise.  Assembly (U14 §7 verbatim): divide RP-4's
  twisted identity by `y^{j₀(g·z)}` — concretely, cancel `X^{j₀(g·z)}` between RP-8's
  reconstruction `R₃(g·z)·y^{j₀(g·z)} = R_{β+β′}(g·z)` and the twist+reconstruction
  composite `y^c·(R₃(g)·y^{j₀(g)})·(R₃(z)·y^{j₀(z)})`, using RP-9's
  `j₀(g·z) = j₀(g)+j₀(z)+c` to match the powers (`mul_right_cancel₀` over the domain).
  Zero cases: `g = 0` or `z = 0` land on Def 3.15's zero clause (`s2NormRes_zero`), where
  the law reads `0 = 0·R₃(z)`.  Exact-grade worker: `s2NormRes_mul_of_exact`.
* **`s2NormRes_pow`** — `R₃(g^k) = R₃(g)^k`, unrestricted (contrast: the SCALAR `Rgr_pow`
  was adjudicated unsound at odd grades, U14 §8.3 — the normalized power law is clean).
* **`s2NormRes_coeff_zero_mul`** — the normalized-scalar multiplicativity, U14 §8.3's
  `RgrNorm` route: the coefficient-zero read of Cor 4.12(3) (NOT of Cor 4.12(2)).
* **the FD-0 pin** (`s2_normalized_mul_fills`): for ANY `FGMNSourceData` whose
  `normalizedResidual` field is the S2 operator `s2NormRes`, the C130fg
  `FGMNSourceLaws.normalized_mul` field holds — byte-identical binder shape, zero residual
  assembly work left at FD-0.
* **the A-C.11 class-shape tooth** (`s2_Rres_mul_shape`): the statement of the leanspec
  `FGMNCalculus.Rres_mul` field (C130pk: `∀ g h, Rres (g·h) = Rres g · Rres h`) at
  `Rres := s2NormRes`, byte-shaped.

## What this node does NOT claim (honesty scope)

* No `FGMNSourceData`/`FGMNSourceLaws`/`FGMNCalculus` INSTANCE (FD-0/CC-17): the `_fills`
  pin and the class-shape tooth are conditional pins/shape checks only.
* No change to any A-C.11 field and no `RgrNorm` amendment: `s2NormRes_coeff_zero_mul` is a
  theorem about the S2 operator, cited to Cor 4.12(3); the plain scalar `Rgr_mul` keeps its
  restored `PrevGrade` premise (A-C.13), untouched here.
* The graded-level plain product law stays REFUTED at odd×odd
  (`C130rp2.tooth_graded_mul_plain_shape_refuted`); nothing here re-litigates it — the
  normalized law is multiplicative precisely because the strip absorbs that twist.
* The ϖ-read ↔ `ε(α)·R(a)(z)` evaluation dictionary stays on C.22/C.25's recorded
  faithfulness boundary, inherited through RP-1/RP-8, not re-derived.

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements):
`s2GradedRes_natTrailingDegree_mul` (the RP-9 carry form), `dvSideMin_mul_of_exact` (the
endpoint equality), `s2NormRes_mul` (the Cor 4.12(3) realization), and the FD-0/A-C.11
shape pins.

**DEPENDS.** C130rp8 (`s2NormRes`, `s2GradeOf`, `S2ExactGrade_s2GradeOf`,
`s2GradeOf_eq_of_exact`, `s2NormRes_of_exact`, `s2NormRes_zero`, `s2NormRes_one`,
`s2NormRes_key`, `s2NormRes_mul_X_pow_of_exact`, `s2GradedRes_natTrailingDegree_eq`,
`tooth_normRes_X`) · C130rp6 (`s2GradedRes_ne_zero_of_exact`, `exists_slotOnGrade_of_exact`)
· C130rp4 (`s2GradedRes_mul_of_exact`) · C130rp2 (`s2SlotOnGrade_iff_dvOnSide`) · C130rp1
(`s2SlotOnGrade_parity`, `s2GradedRes_zero`, `tooth_gradedRes_key`,
`tooth_gradedRes_X_mul_key`, `tooth_gradedRes_key_sq`) · C130rp0 (`S2ExactGrade_mul`,
`S2ExactGrade_zero_false`, `tooth_key`, `tooth_X`, `tooth_X_mul_key`) · C130fg
(`FGMNSourceData`, for the pin) · C130nv2 (`dvOnSide_dvSideMin`,
`mem_dvSideSet_of_dvOnSide`) · C.07 (`dvSideSet`, `dvSideMin`) · mathlib
(`Polynomial.natTrailingDegree_mul`/`_X_pow`/`_X`/`_one`/`_zero`, `mul_right_cancel₀`,
`Polynomial.mul_coeff_zero`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement touched.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C130rp9

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130rp0
open Uniformity.Density.Tower.C130rp1 Uniformity.Density.Tower.C130rp2
open Uniformity.Density.Tower.C130nv2 Uniformity.Density.Tower.C130rp4
open Uniformity.Density.Tower.C130rp6 Uniformity.Density.Tower.C130rp8

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 0 — side-set nonemptiness at exact grade

Every exact-grade polynomial has a nonempty side set (RP-5's gate witness read through the
RP-2 dictionary) — the hypothesis every endpoint statement carries, discharged once. -/

/-- at exact grade the side set is nonempty: RP-5's gate witness is an on-side slot. -/
theorem dvSideSet_nonempty_of_exact {β : ℕ} {g : Polynomial O}
    (hg : S2ExactGrade h2 hq β g) :
    (dvSideSet (s2Frame h2 hq) g 5 2).Nonempty := by
  obtain ⟨s, hgate⟩ := exists_slotOnGrade_of_exact h2 hq hg
  exact ⟨s, mem_dvSideSet_of_dvOnSide ((s2SlotOnGrade_iff_dvOnSide h2 hq hg).mp hgate)⟩

/-- the chosen minimizer has the grade's parity (`dvSideMin ≡ β (mod 2)`): the left-endpoint
slot is on-line, and every on-line slot has abscissa `≡ β (mod 2)` (RP-1's gate parity). -/
theorem dvSideMin_mod_two_of_exact {β : ℕ} {g : Polynomial O}
    (hg : S2ExactGrade h2 hq β g)
    (hng : (dvSideSet (s2Frame h2 hq) g 5 2).Nonempty) :
    dvSideMin (s2Frame h2 hq) g 5 2 hng % 2 = β % 2 :=
  s2SlotOnGrade_parity h2 hq ((s2SlotOnGrade_iff_dvOnSide h2 hq hg).mpr
    (dvOnSide_dvSideMin (s2Frame h2 hq) g 5 2 hng))

/-! ## Part 1 — ★ NODE RP-9: the initial `y`-orders ADD (with the carry twist)

The initial `y`-order is the trailing degree of the graded residual — certified equal to
published Def 3.15's `j₀ = ⌊s(g)/e₂⌋` by RP-8's strip pin.  Taking trailing degrees of
RP-4's twisted product identity over the residue-field DOMAIN turns the twist power into
the additive carry: U14 §7's floor identity, as a theorem. -/

/-- ★ **NODE RP-9 — the `y`-order addition law** (U14 §7's `j_{gh} = j_g + j_h + c`): at
exact grades, the trailing degree (= the strip amount `j₀`) of the product's graded residual
is the SUM of the factors' plus the odd×odd carry — `natTrailingDegree` of RP-4's twisted
identity, additive over the domain because both graded residuals are nonzero at exact grade
(RP-5/RP-6). -/
theorem s2GradedRes_natTrailingDegree_mul {β β' : ℕ} {g z : Polynomial O}
    (hg : S2ExactGrade h2 hq β g) (hz : S2ExactGrade h2 hq β' z) :
    (s2GradedRes h2 hq (β + β') (g * z)).natTrailingDegree
      = (s2GradedRes h2 hq β g).natTrailingDegree
        + (s2GradedRes h2 hq β' z).natTrailingDegree
        + β % 2 * (β' % 2) := by
  have hgne := s2GradedRes_ne_zero_of_exact h2 hq hg
  have hzne := s2GradedRes_ne_zero_of_exact h2 hq hz
  rw [s2GradedRes_mul_of_exact h2 hq hg hz,
    Polynomial.natTrailingDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero)
      (mul_ne_zero hgne hzne),
    Polynomial.natTrailingDegree_mul hgne hzne, Polynomial.natTrailingDegree_X_pow]
  omega

/-- **the grade companion** — the total extracted grades ADD: `μ₂(g·z) = μ₂(g) + μ₂(z)` for
nonzero inputs (RP-0's `S2ExactGrade_mul` read through the RP-8 extraction). -/
theorem s2GradeOf_mul {g z : Polynomial O} (hg : g ≠ 0) (hz : z ≠ 0) :
    s2GradeOf h2 hq (g * z) = s2GradeOf h2 hq g + s2GradeOf h2 hq z :=
  s2GradeOf_eq_of_exact h2 hq
    (S2ExactGrade_mul h2 hq (S2ExactGrade_s2GradeOf h2 hq hg)
      (S2ExactGrade_s2GradeOf h2 hq hz))

/-- the RP-9 law in TOTAL anchoring (each residual at its own extracted grade `s2GradeOf`):
the form RP-10's universal assembly consumes conceptually. -/
theorem s2GradedRes_natTrailingDegree_mul_total {g z : Polynomial O}
    (hg : g ≠ 0) (hz : z ≠ 0) :
    (s2GradedRes h2 hq (s2GradeOf h2 hq (g * z)) (g * z)).natTrailingDegree
      = (s2GradedRes h2 hq (s2GradeOf h2 hq g) g).natTrailingDegree
        + (s2GradedRes h2 hq (s2GradeOf h2 hq z) z).natTrailingDegree
        + s2GradeOf h2 hq g % 2 * (s2GradeOf h2 hq z % 2) := by
  have h := s2GradedRes_natTrailingDegree_mul h2 hq (S2ExactGrade_s2GradeOf h2 hq hg)
    (S2ExactGrade_s2GradeOf h2 hq hz)
  rwa [← s2GradeOf_mul h2 hq hg hz] at h

/-- **the published-coordinate form** (the brief's display
`j₀(g·h) = j₀(g) + j₀(h) + (β%2)(β′%2)`, with `j₀ = ⌊s(·)/e₂⌋ = dvSideMin/2` by RP-8's
strip pin on all three polynomials): U14 §7's floor identity
`⌊(s+s′)/2⌋ = ⌊s/2⌋ + ⌊s′/2⌋ + carry` at S2. -/
theorem dvSideMin_div_two_mul_of_exact {β β' : ℕ} {g z : Polynomial O}
    (hg : S2ExactGrade h2 hq β g) (hz : S2ExactGrade h2 hq β' z)
    (hng : (dvSideSet (s2Frame h2 hq) g 5 2).Nonempty)
    (hnz : (dvSideSet (s2Frame h2 hq) z 5 2).Nonempty)
    (hngz : (dvSideSet (s2Frame h2 hq) (g * z) 5 2).Nonempty) :
    dvSideMin (s2Frame h2 hq) (g * z) 5 2 hngz / 2
      = dvSideMin (s2Frame h2 hq) g 5 2 hng / 2
        + dvSideMin (s2Frame h2 hq) z 5 2 hnz / 2
        + β % 2 * (β' % 2) := by
  have hntd := s2GradedRes_natTrailingDegree_mul h2 hq hg hz
  rwa [s2GradedRes_natTrailingDegree_eq h2 hq hg hng,
    s2GradedRes_natTrailingDegree_eq h2 hq hz hnz,
    s2GradedRes_natTrailingDegree_eq h2 hq (S2ExactGrade_mul h2 hq hg hz) hngz] at hntd

/-- ★ **NODE RP-9 — the UNHALVED endpoint law**: the left endpoints themselves add,
`s(g·z) = s(g) + s(z)` (U14 §7's "the left endpoints add under multiplication").  NV-2/NV-3
landed only `≤` (`s2_dvSideMin_mul_le`, under endpoint-height hypotheses); the EQUALITY
falls out of the halved law + the parity pins — the carry `(β%2)(β′%2)` is exactly what the
halving had absorbed, and the parities restore it. -/
theorem dvSideMin_mul_of_exact {β β' : ℕ} {g z : Polynomial O}
    (hg : S2ExactGrade h2 hq β g) (hz : S2ExactGrade h2 hq β' z)
    (hng : (dvSideSet (s2Frame h2 hq) g 5 2).Nonempty)
    (hnz : (dvSideSet (s2Frame h2 hq) z 5 2).Nonempty)
    (hngz : (dvSideSet (s2Frame h2 hq) (g * z) 5 2).Nonempty) :
    dvSideMin (s2Frame h2 hq) (g * z) 5 2 hngz
      = dvSideMin (s2Frame h2 hq) g 5 2 hng + dvSideMin (s2Frame h2 hq) z 5 2 hnz := by
  have hj := dvSideMin_div_two_mul_of_exact h2 hq hg hz hng hnz hngz
  have hpg := dvSideMin_mod_two_of_exact h2 hq hg hng
  have hpz := dvSideMin_mod_two_of_exact h2 hq hz hnz
  have hpgz := dvSideMin_mod_two_of_exact h2 hq (S2ExactGrade_mul h2 hq hg hz) hngz
  rcases Nat.mod_two_eq_zero_or_one β with hb | hb <;>
    rcases Nat.mod_two_eq_zero_or_one β' with hb' | hb' <;>
    rw [hb, hb'] at hj <;> omega

/-! ## Part 2 — the RP-9 zero cases (the row's "including all zero cases" clause)

The zero polynomial has NO exact grade (RP-0's `S2ExactGrade_zero_false`), so the
exact-grade addition laws have no zero instance to state — their zero cases are vacuously
closed by RP-0.  The total carriers are pinned at `0` explicitly, and the zero cases of the
NORMALIZED product law are Def 3.15's own zero clause, discharged in Part 3's universal law
and toothed in Part 5. -/

/-- the total trailing-degree carrier at the zero polynomial: `R_β(0) = 0` has trailing
degree `0` (every grade `β`). -/
theorem s2GradedRes_natTrailingDegree_zero (β : ℕ) :
    (s2GradedRes h2 hq β (0 : Polynomial O)).natTrailingDegree = 0 := by
  rw [s2GradedRes_zero h2 hq, Polynomial.natTrailingDegree_zero]

/-- the RP-9 exact-grade laws have NO zero instance: re-exposed from RP-0 in this file's
vocabulary (any exact-grade hypothesis on a factor already excludes `0`). -/
theorem no_exact_grade_at_zero (β : ℕ) : ¬ S2ExactGrade h2 hq β (0 : Polynomial O) :=
  S2ExactGrade_zero_false h2 hq β

/-! ## Part 3 — ★ NODE RP-10: the universal plain normalized product law

Published Cor 4.12(3) verbatim scope ("for all `g, h ∈ K[x]`"), realized: divide RP-4's
twisted identity by `y^{j₀(g·z)}` — the reconstruction supplies the divisions, RP-9 matches
the powers, and `mul_right_cancel₀` over the domain performs the division. -/

/-- **the RP-10 worker at caller-supplied exact grades**: `R₃(g·z) = R₃(g)·R₃(z)` for
nonzero inputs — the twist power `y^{(β%2)(β′%2)}` is EXACTLY absorbed by the strip
(U14 §1 clause 4: "this removal absorbs exactly the carry"). -/
theorem s2NormRes_mul_of_exact {β β' : ℕ} {g z : Polynomial O}
    (hg : S2ExactGrade h2 hq β g) (hz : S2ExactGrade h2 hq β' z) :
    s2NormRes h2 hq (g * z) = s2NormRes h2 hq g * s2NormRes h2 hq z := by
  have hgz : S2ExactGrade h2 hq (β + β') (g * z) := S2ExactGrade_mul h2 hq hg hz
  have hntd := s2GradedRes_natTrailingDegree_mul h2 hq hg hz
  refine mul_right_cancel₀
    (pow_ne_zero ((s2GradedRes h2 hq (β + β') (g * z)).natTrailingDegree)
      Polynomial.X_ne_zero) ?_
  calc s2NormRes h2 hq (g * z)
        * Polynomial.X ^ (s2GradedRes h2 hq (β + β') (g * z)).natTrailingDegree
      = s2GradedRes h2 hq (β + β') (g * z) := s2NormRes_mul_X_pow_of_exact h2 hq hgz
    _ = Polynomial.X ^ (β % 2 * (β' % 2))
        * (s2GradedRes h2 hq β g * s2GradedRes h2 hq β' z) :=
        s2GradedRes_mul_of_exact h2 hq hg hz
    _ = Polynomial.X ^ (β % 2 * (β' % 2))
        * ((s2NormRes h2 hq g
              * Polynomial.X ^ (s2GradedRes h2 hq β g).natTrailingDegree)
          * (s2NormRes h2 hq z
              * Polynomial.X ^ (s2GradedRes h2 hq β' z).natTrailingDegree)) := by
        rw [s2NormRes_mul_X_pow_of_exact h2 hq hg, s2NormRes_mul_X_pow_of_exact h2 hq hz]
    _ = (s2NormRes h2 hq g * s2NormRes h2 hq z)
        * Polynomial.X ^ ((s2GradedRes h2 hq β g).natTrailingDegree
            + (s2GradedRes h2 hq β' z).natTrailingDegree + β % 2 * (β' % 2)) := by
        ring
    _ = (s2NormRes h2 hq g * s2NormRes h2 hq z)
        * Polynomial.X ^ (s2GradedRes h2 hq (β + β') (g * z)).natTrailingDegree := by
        rw [hntd]

/-- ★ **NODE RP-10 — the UNIVERSAL normalized product law** (published Cor 4.12(3), its
verbatim "for all `g, h ∈ K[x]`" scope): `R₃(g·z) = R₃(g)·R₃(z)` for ALL `g, z` — no grade,
parity, or nonzero premise.  Zero cases via published Def 3.15's own `R₃(0) = 0` clause;
nonzero cases at the extracted grades (RP-0's existence through RP-8's `s2GradeOf`). -/
theorem s2NormRes_mul (g z : Polynomial O) :
    s2NormRes h2 hq (g * z) = s2NormRes h2 hq g * s2NormRes h2 hq z := by
  rcases eq_or_ne g 0 with rfl | hgne
  · rw [zero_mul, s2NormRes_zero h2 hq, zero_mul]
  rcases eq_or_ne z 0 with rfl | hzne
  · rw [mul_zero, s2NormRes_zero h2 hq, mul_zero]
  exact s2NormRes_mul_of_exact h2 hq (S2ExactGrade_s2GradeOf h2 hq hgne)
    (S2ExactGrade_s2GradeOf h2 hq hzne)

/-- **the unrestricted normalized power law**: `R₃(g^k) = R₃(g)^k` for all `g, k` (contrast
U14 §8.3: the SCALAR `Rgr_pow` was adjudicated unsound at odd grades — the normalized power
law is clean because each step of the induction is the universal Cor 4.12(3)). -/
theorem s2NormRes_pow (g : Polynomial O) (k : ℕ) :
    s2NormRes h2 hq (g ^ k) = s2NormRes h2 hq g ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, s2NormRes_one h2 hq]
  | succ k ih => rw [pow_succ, pow_succ, s2NormRes_mul h2 hq, ih]

/-- **the normalized-scalar multiplicativity** (U14 §8.3's `RgrNorm` route): the
coefficient-zero read of the universal law — a consequence of Cor 4.12(3), deliberately NOT
cited as Cor 4.12(2) (whose scalar projection fails odd×odd, U14 §6). -/
theorem s2NormRes_coeff_zero_mul (g z : Polynomial O) :
    (s2NormRes h2 hq (g * z)).coeff 0
      = (s2NormRes h2 hq g).coeff 0 * (s2NormRes h2 hq z).coeff 0 := by
  rw [s2NormRes_mul h2 hq, Polynomial.mul_coeff_zero]

/-! ## Part 4 — the FD-0 pin and the A-C.11 class shape -/

/-- **the FD-0 pin**: if `S : FGMNSourceData (s2DepthTwo h2 hq) K 2 1 5` reads
`normalizedResidual := s2NormRes`, then the `FGMNSourceLaws.normalized_mul` field for `S`
holds — byte-identical binder shape (C130fg: published Cor 4.12(3)); zero residual assembly
work left at FD-0 for this field. -/
theorem s2_normalized_mul_fills (K : KeyChain (s2DepthTwo h2 hq))
    (S : FGMNSourceData (s2DepthTwo h2 hq) K 2 1 5)
    (hnorm : S.normalizedResidual = s2NormRes h2 hq) :
    ∀ g h : Polynomial O,
      S.normalizedResidual (g * h) = S.normalizedResidual g * S.normalizedResidual h := by
  intro g h
  rw [hnorm]
  exact s2NormRes_mul h2 hq g h

/-- **the A-C.11 class-shape tooth**: the leanspec `FGMNCalculus.Rres_mul` field shape
(C130pk: `∀ g h, Rres (g * h) = Rres g * Rres h`) at `Rres := s2NormRes`, byte-shaped —
the S2 witness that the class field is realizable at the normalized operator. -/
theorem s2_Rres_mul_shape :
    ∀ g h : Polynomial O,
      s2NormRes h2 hq (g * h) = s2NormRes h2 hq g * s2NormRes h2 hq h :=
  s2NormRes_mul h2 hq

/-! ## Part 5 — teeth (regressions against the landed RP-1/RP-8 values)

Every genre of the case split gets a machine-checked instance: the odd×odd carry (law vs
hand), a NEW odd×odd pair beyond pure key powers, the mixed pair, the key powers re-derived
through the universal law, and both zero cases. -/

/-- **tooth (RP-9, odd×odd carry, via the LAW)**: `j₀(Φ′·Φ′) = 0 + 0 + 1 = 1` — the carry
term is LIVE. -/
theorem tooth_ntd_carry_law :
    (s2GradedRes h2 hq 10
      (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key)).natTrailingDegree
      = 1 := by
  have h := s2GradedRes_natTrailingDegree_mul h2 hq (tooth_key h2 hq) (tooth_key h2 hq)
  rw [show (5 : ℕ) + 5 = 10 from rfl, tooth_gradedRes_key h2 hq,
    Polynomial.natTrailingDegree_one] at h
  omega

/-- **tooth (RP-9, odd×odd carry, by HAND)**: the same value read off RP-1's landed
`R₁₀(Φ′²) = X` — the law's output matches the landed table. -/
theorem tooth_ntd_carry_hand :
    (s2GradedRes h2 hq 10
      (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key)).natTrailingDegree
      = 1 := by
  rw [tooth_gradedRes_key_sq h2 hq]
  exact Polynomial.natTrailingDegree_X

/-- **tooth (RP-9, a NEW odd×odd pair beyond key powers)**: at `(β, β′) = (5, 7)` — the pair
`(Φ′, x·Φ′)`, both grades odd — `j₀(Φ′·(x·Φ′)) = 0 + 0 + 1 = 1`: a fresh grade-12 value
produced by the law alone. -/
theorem tooth_ntd_odd_pair :
    (s2GradedRes h2 hq 12 (((s2Frame h2 hq).key : Polynomial O)
      * (Polynomial.X * (s2Frame h2 hq).key))).natTrailingDegree = 1 := by
  have h := s2GradedRes_natTrailingDegree_mul h2 hq (tooth_key h2 hq)
    (tooth_X_mul_key h2 hq)
  rw [show (5 : ℕ) + 7 = 12 from rfl, tooth_gradedRes_key h2 hq,
    tooth_gradedRes_X_mul_key h2 hq, Polynomial.natTrailingDegree_one] at h
  omega

/-- **tooth (RP-10, mixed parity, by HAND)**: `R₃(x·Φ′) = 1` — grade `7`, landed
`R₇(x·Φ′) = 1` (RP-1), trailing degree `0`, identity strip. -/
theorem tooth_normRes_X_mul_key :
    s2NormRes h2 hq ((Polynomial.X : Polynomial O) * (s2Frame h2 hq).key) = 1 := by
  rw [s2NormRes_of_exact h2 hq (tooth_X_mul_key h2 hq), tooth_gradedRes_X_mul_key h2 hq,
    Polynomial.natTrailingDegree_one]
  rfl

/-- **tooth (RP-10, mixed parity, via the LAW)**: the universal law reproduces the hand
value — `R₃(x·Φ′) = R₃(x)·R₃(Φ′) = 1·1 = 1`. -/
theorem tooth_normRes_mul_mixed :
    s2NormRes h2 hq ((Polynomial.X : Polynomial O) * (s2Frame h2 hq).key)
      = s2NormRes h2 hq (Polynomial.X : Polynomial O)
        * s2NormRes h2 hq ((s2Frame h2 hq).key : Polynomial O) :=
  s2NormRes_mul h2 hq _ _

/-- **tooth (RP-10, the NEW odd×odd pair)**: `R₃(Φ′·(x·Φ′)) = 1` — the grade-12 normalized
value through the universal law (`= R₃(Φ′)·R₃(x·Φ′) = 1·1`), where the PLAIN graded law
carries a live twist (`tooth_ntd_odd_pair`). -/
theorem tooth_normRes_mul_odd_odd :
    s2NormRes h2 hq (((s2Frame h2 hq).key : Polynomial O)
      * (Polynomial.X * (s2Frame h2 hq).key)) = 1 := by
  rw [s2NormRes_mul h2 hq, s2NormRes_key h2 hq, tooth_normRes_X_mul_key h2 hq, one_mul]

/-- **tooth (RP-10, key powers re-derived)**: `R₃(Φ′^k) = 1` through the UNIVERSAL law
(`s2NormRes_pow` + `s2NormRes_key`) — matches RP-8's independent induction
(`s2NormRes_key_pow`). -/
theorem tooth_normRes_key_pow_via_law (k : ℕ) :
    s2NormRes h2 hq (((s2Frame h2 hq).key : Polynomial O) ^ k) = 1 := by
  rw [s2NormRes_pow h2 hq, s2NormRes_key h2 hq, one_pow]

/-- **tooth (RP-10, zero case LEFT)**: the universal law at `(0, g)` — both sides are `0`
(Def 3.15's zero clause). -/
theorem tooth_normRes_mul_zero_left (g : Polynomial O) :
    s2NormRes h2 hq ((0 : Polynomial O) * g)
      = s2NormRes h2 hq (0 : Polynomial O) * s2NormRes h2 hq g :=
  s2NormRes_mul h2 hq 0 g

/-- **tooth (RP-10, zero case LEFT, value)**: `R₃(0·g) = 0`. -/
theorem tooth_normRes_mul_zero_left_value (g : Polynomial O) :
    s2NormRes h2 hq ((0 : Polynomial O) * g) = 0 := by
  rw [zero_mul, s2NormRes_zero h2 hq]

/-- **tooth (RP-10, zero case RIGHT, value)**: `R₃(g·0) = 0`. -/
theorem tooth_normRes_mul_zero_right_value (g : Polynomial O) :
    s2NormRes h2 hq (g * (0 : Polynomial O)) = 0 := by
  rw [mul_zero, s2NormRes_zero h2 hq]

end S2

end Uniformity.Density.Tower.C130rp9

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130rp9.dvSideSet_nonempty_of_exact
#print axioms Uniformity.Density.Tower.C130rp9.dvSideMin_mod_two_of_exact
#print axioms Uniformity.Density.Tower.C130rp9.s2GradedRes_natTrailingDegree_mul
#print axioms Uniformity.Density.Tower.C130rp9.s2GradeOf_mul
#print axioms Uniformity.Density.Tower.C130rp9.s2GradedRes_natTrailingDegree_mul_total
#print axioms Uniformity.Density.Tower.C130rp9.dvSideMin_div_two_mul_of_exact
#print axioms Uniformity.Density.Tower.C130rp9.dvSideMin_mul_of_exact
#print axioms Uniformity.Density.Tower.C130rp9.s2GradedRes_natTrailingDegree_zero
#print axioms Uniformity.Density.Tower.C130rp9.no_exact_grade_at_zero
#print axioms Uniformity.Density.Tower.C130rp9.s2NormRes_mul_of_exact
#print axioms Uniformity.Density.Tower.C130rp9.s2NormRes_mul
#print axioms Uniformity.Density.Tower.C130rp9.s2NormRes_pow
#print axioms Uniformity.Density.Tower.C130rp9.s2NormRes_coeff_zero_mul
#print axioms Uniformity.Density.Tower.C130rp9.s2_normalized_mul_fills
#print axioms Uniformity.Density.Tower.C130rp9.s2_Rres_mul_shape
#print axioms Uniformity.Density.Tower.C130rp9.tooth_ntd_carry_law
#print axioms Uniformity.Density.Tower.C130rp9.tooth_ntd_carry_hand
#print axioms Uniformity.Density.Tower.C130rp9.tooth_ntd_odd_pair
#print axioms Uniformity.Density.Tower.C130rp9.tooth_normRes_X_mul_key
#print axioms Uniformity.Density.Tower.C130rp9.tooth_normRes_mul_mixed
#print axioms Uniformity.Density.Tower.C130rp9.tooth_normRes_mul_odd_odd
#print axioms Uniformity.Density.Tower.C130rp9.tooth_normRes_key_pow_via_law
#print axioms Uniformity.Density.Tower.C130rp9.tooth_normRes_mul_zero_left
#print axioms Uniformity.Density.Tower.C130rp9.tooth_normRes_mul_zero_left_value
#print axioms Uniformity.Density.Tower.C130rp9.tooth_normRes_mul_zero_right_value

end AxCheck
