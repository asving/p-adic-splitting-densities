/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130nv5

/-!
# Uniformity.ChapC.C130rp0 — S2-source plan node RP-0

**S2-source plan node RP-0** (`docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6 row RP-0:
"grade arithmetic", dependencies `NV-5`, S2 numerals `(2,1,5)`): the CLEARED grade / value-
group lemma bank at the S2 numerals, and the exact- and above-membership normal forms, built
directly on the LANDED level-two value `s2Hgt₂` (C130s6) and its now-UNIVERSAL product law
`s2Hgt₂_mul` (C130nv3, NV-4's row) and `AddValuation` packaging `s2AddVal₂` (C130nv5, NV-5).

## The U9 dictionary this instantiates (`FGMN_ADJUDICATION_2026-08-24.md` §2, §4 Q3)

`FGMNSourceData.ExactGrade`/`AboveGrade` (`C130fg.lean`) are, for an abstract
`S : FGMNSourceData W K e' f' u'`, the DEFINITIONS

```text
ExactGrade β g := S.nextValue g = (β : WithTop ℤ)
AboveGrade β g := (β : WithTop ℤ) < S.nextValue g
```

At the S2 depth-two consumer the next-augmentation convention (U9 §2) reads `keyAt 1 = Φ′`,
`(e', f', u') = (e₂, f₂, u₂) = (2, 1, 5)` (`C130s2.s2DepthTwo_stage2`), and `nextValue`
is `μ₂`, the repo's level-two cleared value `s2Hgt₂ = toZ (dvSupp (s2Frame …) · 5 2)`
(C130s6/C130nv3's doc header). This file therefore fixes the CONCRETE S2 instantiation

```text
S2ExactGrade β g := s2Hgt₂ h2 hq g = (β : WithTop ℤ)
S2AboveGrade β g := (β : WithTop ℤ) < s2Hgt₂ h2 hq g
```

— byte-for-byte the `FGMNSourceData.ExactGrade`/`AboveGrade` shape with `nextValue` read as
`s2Hgt₂ h2 hq`, ahead of any `FGMNSourceData W K e' f' u'` instance (RP-1 onward); no field
or structure is instantiated here, only the two `Prop`s and their lemma bank.

## What lands

* **value-group arithmetic**: `toZ_lt_toZ_iff` (the missing strict-order companion of
  C130s6's `toZ_le_toZ_iff`) and `S2Grade_natCast_add` (cleared grades add as NATURALS
  before the `WithTop ℤ` cast) — the glue `S2ExactGrade_mul` below rides on.
* **the exact-membership normal form** `S2ExactGrade_iff_dvSupp`: `S2ExactGrade β g ↔
  dvSupp (s2Frame …) g 5 2 = (β : ℕ∞)` — derived (via `toZ_inj`/`toZ`'s cast-compatibility,
  not guessed) as the honest CLEARED normalization: the `ℕ∞`-valued corpus support read,
  with no sign ambiguity, matching U9 §2's "the clearing already lives inside `nextValue`".
* **the above-membership normal form** `S2AboveGrade_iff_dvSupp`, the strict companion via
  `toZ_lt_toZ_iff`.
* **grade existence** `S2ExactGrade_exists`: every nonzero polynomial has SOME natural
  cleared grade (`dvSupp_ne_top_of_ne_zero` lands in `ℕ∞`, never past it) — grades are
  honestly `ℕ`-valued at S2, not merely `ℤ`-valued.
* **grade uniqueness** `S2ExactGrade_unique`: a polynomial has at most one exact grade
  (`nextValue` is a function).
* **exact + exact → exact under multiplication** `S2ExactGrade_mul` (the grade half of
  published Cor 4.12(2)/`FGMNSourceLaws.graded_mul`'s first conjunct that RP-3/RP-6 consume,
  U9 Q3: no `PrevGrade` premise — after clearing every class grade is already in `Γ_r`),
  proved directly from `s2Hgt₂_mul`, unconditionally, no source hypothesis.
* **exact/above mutual exclusion** `S2ExactGrade_not_above`.
* **the zero/⊤ edge cases**: `S2ExactGrade_not_zero`/`S2ExactGrade_zero_false` (the zero
  polynomial has NO exact grade — `s2Hgt₂ 0 = ⊤` never equals a finite cast) and
  `S2AboveGrade_zero` (the zero polynomial is `AboveGrade` every `β` — `⊤` dominates every
  finite cast), matching FGMN's `P_β⁺`/`P_β` split at the top of the value group.
* **the NV-5 tie** `S2ExactGrade_eq_addVal`/`S2AboveGrade_eq_addVal`: both predicates read
  off the packaged `AddValuation` `s2AddVal₂` (C130nv5) verbatim, so the concrete grade
  bank is not an ad hoc reinvention but the level-sets of the landed valuation.
* **numeral teeth** at the landed table values: `h₂(x) = 2`, `h₂(Φ′) = 5` (both landed,
  C130s6), `h₂(x·Φ′) = 7 = 2 + 5`, `h₂(Φ′²) = 10 = 5 + 5` (both NEW, through
  `S2ExactGrade_mul` alone — no fresh computation, only the grade-closure law applied to
  the two landed base teeth).

## What this node does NOT claim (honesty scope)

* No `gradedResidual`/`Rgr`/`normalizedResidual`/`Rres` scalar or polynomial content: this
  file is purely about the `Prop`-valued grade predicates and the `WithTop ℤ`/`ℕ∞`
  value-group arithmetic underneath them. The residual operators are RP-1 onward.
* No `FGMNSourceData`/`FGMNSourceLaws`/`ChainRealization` instance: `S2ExactGrade`/
  `S2AboveGrade` are free-standing `Prop`s at this node, matched to the C130fg shape but
  not (yet) packaged as a structure field. That packaging is FD-0.
* `S2ExactGrade_mul` proves only the grade-EXACTNESS conjunct of published Cor 4.12(2); the
  polynomial-residual-value conjunct (`Rgr (β+β') (g*h) = Rgr β g * Rgr β' h`) needs
  `gradedResidual` and is RP-3–RP-6's CORE chain, untouched here.

**DEPENDS.** C130nv5 (`s2AddVal₂`, `s2AddVal₂_apply`; transitively C130nv3's `s2Hgt₂_mul`,
C130nv's `s2Hgt₁`-adjacent dictionary, C130s6's `s2Hgt₂` + zero/`toZ` bank, C130s2's
`s2Frame`/S2 numerals) · C130fg (the `FGMNSourceData.ExactGrade`/`AboveGrade` shape this
concretely instantiates, read-only reference, not imported).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement touched.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C130rp0

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130nv Uniformity.Density.Tower.C130nv3
open Uniformity.Density.Tower.C130nv5

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 1 — the missing `toZ` value-group companion, and cleared-grade addition -/

/-- **the strict companion of C130s6's `toZ_le_toZ_iff`**: `toZ` is a strict order embedding
`ℕ∞ ↪ WithTop ℤ`, via the generic `lt_iff_le_not_ge` unfolding on both sides. -/
theorem toZ_lt_toZ_iff {x y : ℕ∞} : toZ x < toZ y ↔ x < y := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge, toZ_le_toZ_iff, toZ_le_toZ_iff]

/-- **the value-group arithmetic**: cleared grades add AS NATURALS before the `WithTop ℤ`
cast — the glue fact that lets `s2Hgt₂_mul`'s value equation upgrade to an `ExactGrade`
closure statement. -/
theorem S2Grade_natCast_add (β β' : ℕ) :
    ((β + β' : ℕ) : WithTop ℤ) = (β : WithTop ℤ) + (β' : WithTop ℤ) := by
  norm_cast

/-! ## Part 2 — the concrete S2 instantiation of `FGMNSourceData.ExactGrade`/`AboveGrade`

Byte-for-byte the C130fg shape `S.nextValue g = (β : WithTop ℤ)` /
`(β : WithTop ℤ) < S.nextValue g`, with `nextValue` read as the landed `s2Hgt₂ h2 hq`. -/

/-- `S2ExactGrade β g ↔ μ₂(g) = β` (U9 §2's `ExactGrade`, at the S2 numerals): the cleared
level-two value hits the natural grade `β` exactly. -/
def S2ExactGrade (β : ℕ) (g : Polynomial O) : Prop :=
  s2Hgt₂ h2 hq g = (β : WithTop ℤ)

/-- `S2AboveGrade β g ↔ μ₂(g) > β` (U9 §2's `AboveGrade`, at the S2 numerals): FGMN's
`P_β⁺`, defined from the SAME `s2Hgt₂` as `S2ExactGrade`, never independently. -/
def S2AboveGrade (β : ℕ) (g : Polynomial O) : Prop :=
  (β : WithTop ℤ) < s2Hgt₂ h2 hq g

/-! ## Part 3 — the exact- and above-membership normal forms

The honest cleared normalization (derived, not guessed): both predicates read off the
`ℕ∞`-valued corpus support `dvSupp (s2Frame …) · 5 2` directly, with no sign ambiguity —
exactly U9 §2's "the clearing already lives inside `nextValue`". -/

/-- **the exact-membership normal form**: `S2ExactGrade β g` is EXACTLY the `ℕ∞`-level
equation `dvSupp (s2Frame h2 hq) g 5 2 = (β : ℕ∞)` — the cast-free cleared read. -/
theorem S2ExactGrade_iff_dvSupp {β : ℕ} {g : Polynomial O} :
    S2ExactGrade h2 hq β g ↔ dvSupp (s2Frame h2 hq) g 5 2 = (β : ℕ∞) := by
  unfold S2ExactGrade
  rw [s2Hgt₂_eq_dvSupp]
  constructor
  · intro h
    exact toZ_inj (by rw [h]; norm_cast)
  · intro h
    rw [h]; norm_cast

/-- **the above-membership normal form**: `S2AboveGrade β g` is EXACTLY the `ℕ∞`-level
strict inequality `(β : ℕ∞) < dvSupp (s2Frame h2 hq) g 5 2`. -/
theorem S2AboveGrade_iff_dvSupp {β : ℕ} {g : Polynomial O} :
    S2AboveGrade h2 hq β g ↔ (β : ℕ∞) < dvSupp (s2Frame h2 hq) g 5 2 := by
  unfold S2AboveGrade
  rw [s2Hgt₂_eq_dvSupp]
  rw [show (β : WithTop ℤ) = toZ (β : ℕ∞) by norm_cast]
  exact toZ_lt_toZ_iff

/-! ## Part 4 — existence/uniqueness of the natural cleared grade -/

/-- **grade existence**: every NONZERO polynomial has SOME natural cleared grade — cleared
grades are honestly `ℕ`-valued at S2 (`dvSupp_ne_top_of_ne_zero` lands in `ℕ∞`, and `toZ`
of a finite `ℕ∞` value is always a nonnegative cast, never a genuinely negative integer). -/
theorem S2ExactGrade_exists {g : Polynomial O} (hg : g ≠ 0) :
    ∃ β : ℕ, S2ExactGrade h2 hq β g := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (dvSupp_ne_top_of_ne_zero (s2Frame h2 hq) 5 2 hg)
  exact ⟨n, (S2ExactGrade_iff_dvSupp h2 hq).mpr hn.symm⟩

/-- **grade uniqueness**: a polynomial has AT MOST one exact grade (`nextValue` is a
function, so two exact-grade witnesses coincide). -/
theorem S2ExactGrade_unique {β β' : ℕ} {g : Polynomial O}
    (h1 : S2ExactGrade h2 hq β g) (h2' : S2ExactGrade h2 hq β' g) : β = β' := by
  unfold S2ExactGrade at h1 h2'
  rw [h1] at h2'
  exact_mod_cast h2'

/-! ## Part 5 — the grade arithmetic: exact + exact → exact under multiplication

The grade half of published Cor 4.12(2)/`FGMNSourceLaws.graded_mul`'s first conjunct
(RP-3/RP-6's consumed vocabulary), UNCONDITIONAL — no `FGMNSourceLaws` hypothesis, direct
from the now-universal `s2Hgt₂_mul` (C130nv3, NV-4's row) plus `S2Grade_natCast_add`. -/

/-- ★ **the grade arithmetic** — `S2ExactGrade` is closed under multiplication with grades
adding: `S2ExactGrade β g → S2ExactGrade β' h → S2ExactGrade (β + β') (g * h)`, for ALL
`g, h` (no fence). U9 Q3: no `PrevGrade` premise — clearing already puts every grade in
`Γ_r`. -/
theorem S2ExactGrade_mul {β β' : ℕ} {g h : Polynomial O}
    (hg : S2ExactGrade h2 hq β g) (hh : S2ExactGrade h2 hq β' h) :
    S2ExactGrade h2 hq (β + β') (g * h) := by
  unfold S2ExactGrade at hg hh ⊢
  rw [s2Hgt₂_mul h2 hq, hg, hh, S2Grade_natCast_add]

/-- **exact/above mutual exclusion**: a polynomial cannot be both exactly AND strictly
above the same grade. -/
theorem S2ExactGrade_not_above {β : ℕ} {g : Polynomial O} (hg : S2ExactGrade h2 hq β g) :
    ¬ S2AboveGrade h2 hq β g := by
  unfold S2ExactGrade at hg
  unfold S2AboveGrade
  rw [hg]
  exact lt_irrefl _

/-! ## Part 6 — the zero/⊤ edge cases

`s2Hgt₂ h2 hq 0 = ⊤` (C130s6's `s2Hgt₂_zero`): the zero polynomial has NO exact grade and
is `AboveGrade` every `β` — the S2 concrete instance of FGMN's `P_β⁺`/`P_β` split at `⊤`. -/

/-- the zero polynomial has no exact grade — an exact-grade witness would force
`g ≠ 0` (`s2Hgt₂ 0 = ⊤` never equals a finite cast). -/
theorem S2ExactGrade_not_zero {β : ℕ} {g : Polynomial O} (hg : S2ExactGrade h2 hq β g) :
    g ≠ 0 := by
  intro h0
  unfold S2ExactGrade at hg
  rw [h0, s2Hgt₂_zero] at hg
  exact WithTop.top_ne_coe hg

/-- the zero-polynomial edge case, restated with the zero polynomial displayed: no `β` is
an exact grade of `0`. -/
theorem S2ExactGrade_zero_false (β : ℕ) : ¬ S2ExactGrade h2 hq β (0 : Polynomial O) :=
  fun hg => S2ExactGrade_not_zero h2 hq hg rfl

/-- the zero polynomial is `AboveGrade` every natural `β` — `⊤` dominates every finite
cast. -/
theorem S2AboveGrade_zero (β : ℕ) : S2AboveGrade h2 hq β (0 : Polynomial O) := by
  unfold S2AboveGrade
  rw [s2Hgt₂_zero]
  exact_mod_cast WithTop.coe_lt_top (β : ℤ)

/-! ## Part 7 — the NV-5 tie: both predicates read off the packaged `AddValuation`

`S2ExactGrade`/`S2AboveGrade` are not an ad hoc reinvention: they are literally the level
sets of C130nv5's packaged `s2AddVal₂ : AddValuation (Polynomial O) (WithTop ℤ)`. -/

/-- `S2ExactGrade` IS the equality level-set of the packaged `AddValuation` `s2AddVal₂`. -/
theorem S2ExactGrade_eq_addVal (β : ℕ) (g : Polynomial O) :
    S2ExactGrade h2 hq β g ↔ s2AddVal₂ h2 hq g = (β : WithTop ℤ) := by
  unfold S2ExactGrade
  rw [s2AddVal₂_apply]

/-- `S2AboveGrade` IS the strict-inequality level-set of `s2AddVal₂`. -/
theorem S2AboveGrade_eq_addVal (β : ℕ) (g : Polynomial O) :
    S2AboveGrade h2 hq β g ↔ (β : WithTop ℤ) < s2AddVal₂ h2 hq g := by
  unfold S2AboveGrade
  rw [s2AddVal₂_apply]

/-! ## Part 8 — numeral teeth at the landed table values

`h₂(x) = 2` and `h₂(Φ′) = 5` are landed (C130s6); `h₂(x·Φ′) = 7` and `h₂(Φ′²) = 10` are NEW
here, produced by `S2ExactGrade_mul` ALONE — no fresh computation, only the grade-closure
law applied to the two landed base teeth. -/

/-- **tooth**: `h₂(x) = 2` re-read as an exact grade. -/
theorem tooth_X : S2ExactGrade h2 hq 2 (Polynomial.X : Polynomial O) := by
  unfold S2ExactGrade; rw [s2Hgt₂_X]; norm_cast

/-- **tooth**: `h₂(Φ′) = 5 = u₂` re-read as an exact grade. -/
theorem tooth_key : S2ExactGrade h2 hq 5 ((s2Frame h2 hq).key : Polynomial O) := by
  unfold S2ExactGrade; rw [s2Hgt₂_key]; norm_cast

/-- **tooth (grade arithmetic, mixed)**: `h₂(x·Φ′) = 7 = 2 + 5`, through `S2ExactGrade_mul`
alone. -/
theorem tooth_X_mul_key :
    S2ExactGrade h2 hq 7 ((Polynomial.X : Polynomial O) * (s2Frame h2 hq).key) := by
  have h := S2ExactGrade_mul h2 hq (tooth_X h2 hq) (tooth_key h2 hq)
  norm_num at h
  exact h

/-- **tooth (grade arithmetic, even × even)**: `h₂(Φ′²) = 10 = 5 + 5`, through
`S2ExactGrade_mul` alone. -/
theorem tooth_key_sq :
    S2ExactGrade h2 hq 10 (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key) := by
  have h := S2ExactGrade_mul h2 hq (tooth_key h2 hq) (tooth_key h2 hq)
  norm_num at h
  exact h

end S2

end Uniformity.Density.Tower.C130rp0

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130rp0.toZ_lt_toZ_iff
#print axioms Uniformity.Density.Tower.C130rp0.S2Grade_natCast_add
#print axioms Uniformity.Density.Tower.C130rp0.S2ExactGrade
#print axioms Uniformity.Density.Tower.C130rp0.S2AboveGrade
#print axioms Uniformity.Density.Tower.C130rp0.S2ExactGrade_iff_dvSupp
#print axioms Uniformity.Density.Tower.C130rp0.S2AboveGrade_iff_dvSupp
#print axioms Uniformity.Density.Tower.C130rp0.S2ExactGrade_exists
#print axioms Uniformity.Density.Tower.C130rp0.S2ExactGrade_unique
#print axioms Uniformity.Density.Tower.C130rp0.S2ExactGrade_mul
#print axioms Uniformity.Density.Tower.C130rp0.S2ExactGrade_not_above
#print axioms Uniformity.Density.Tower.C130rp0.S2ExactGrade_not_zero
#print axioms Uniformity.Density.Tower.C130rp0.S2ExactGrade_zero_false
#print axioms Uniformity.Density.Tower.C130rp0.S2AboveGrade_zero
#print axioms Uniformity.Density.Tower.C130rp0.S2ExactGrade_eq_addVal
#print axioms Uniformity.Density.Tower.C130rp0.S2AboveGrade_eq_addVal
#print axioms Uniformity.Density.Tower.C130rp0.tooth_X
#print axioms Uniformity.Density.Tower.C130rp0.tooth_key
#print axioms Uniformity.Density.Tower.C130rp0.tooth_X_mul_key
#print axioms Uniformity.Density.Tower.C130rp0.tooth_key_sq

end AxCheck
