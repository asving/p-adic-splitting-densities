/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130rp0
import Uniformity.ChapC.C132nv6

/-!
# Uniformity.ChapC.C132rp0 — the μ₃ grade predicates `S2Mu3ExactGrade`/`S2Mu3AboveGrade` (μ₃ campaign, node M3-RP0)

**[M3-RP0, 2026-08-27]** (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6, row M3-RP0):
a mechanical port of the μ₂ `S2ExactGrade`/`S2AboveGrade` grade bank (`C130rp0.lean:115-248`)
to the μ₃ value table `s2Hgt₃` (C132nv1) and its now-UNCONDITIONAL product law
`s2Hgt₃_mul_all` / `AddValuation` packaging `s2AddVal₃` (C132nv6, the just-landed gap-close).
The generic value-group arithmetic (`toZ_lt_toZ_iff`, `S2Grade_natCast_add`) is REUSED
verbatim from C130rp0 rather than re-derived: neither lemma mentions μ₂, `s2Hgt₂`, or any
S2 numeral, so duplicating them here would be a pure copy with no new content.

## What lands

* the concrete S2 μ₃ instantiation `S2Mu3ExactGrade β g := s2Hgt₃ h2 hq g = (β : WithTop ℤ)`
  and `S2Mu3AboveGrade β g := (β : WithTop ℤ) < s2Hgt₃ h2 hq g` — byte-for-byte the
  `FGMNSourceData.ExactGrade`/`AboveGrade` shape with `nextValue` read as `s2Hgt₃ h2 hq`.
* the exact- and above-membership normal forms against the raw `dv2Supp` table
  (`S2Mu3ExactGrade_iff_dv2Supp`/`S2Mu3AboveGrade_iff_dv2Supp`).
* existence (`S2Mu3ExactGrade_exists`) and uniqueness (`S2Mu3ExactGrade_unique`) of the
  natural cleared μ₃ grade.
* the grade arithmetic `S2Mu3ExactGrade_mul` — UNCONDITIONAL (no side-set/pin fence): μ₂'s
  `S2ExactGrade_mul` was already unconditional off `s2Hgt₂_mul`, and nv6's
  `s2Hgt₃_mul_all` is the fully unconditional `∀ x y` product law, so the port carries no
  extra hypothesis — plus mutual exclusion `S2Mu3ExactGrade_not_above`.
* the zero/⊤ edge cases `S2Mu3ExactGrade_not_zero`/`S2Mu3ExactGrade_zero_false`/
  `S2Mu3AboveGrade_zero`, off `s2Hgt₃_zero` (C132nv1).
* the `AddValuation` tie `S2Mu3ExactGrade_eq_addVal`/`S2Mu3AboveGrade_eq_addVal` against the
  genuine unconditional `s2AddVal₃` (C132nv6).
* one numeral tooth, `tooth_Φ₂ : S2Mu3ExactGrade 21 Φ₂`, re-reading nv1's landed
  `s2Hgt₃_Φ₂` as an exact grade (anti-drift check, mirroring μ₂'s `tooth_key`).

## What this node does NOT claim (honesty scope)

Same scope fence as C130rp0: no `gradedResidual`/`Rgr`/`normalizedResidual`/`Rres` scalar
or polynomial content — purely the `Prop`-valued grade predicates and their value-group
arithmetic. No `FGMNSourceData`/`FGMNSourceLaws`/`ChainRealization` instance (out of scope
here; that is FD-0-analogue territory). `S2Mu3ExactGrade_mul`'s unconditional strength is
inherited entirely from nv6's `s2Hgt₃_mul_all`, not re-derived. No law in the μ₂ bank
failed to port (BLOCKED-BECAUSE: none — every law in `C130rp0.lean:115-248` ported
directly, several (the multiplication law) even more simply than at μ₂ since the μ₃ input
`s2Hgt₃_mul_all` is already unconditional with no side-set fence to carry through).

**DEPENDS.** C130rp0 (`toZ_lt_toZ_iff`, `S2Grade_natCast_add`, reused verbatim, not
reproved) · C132nv1 (`s2Hgt₃`, `s2Hgt₃_zero`, `s2Hgt₃_eq_dv2Supp`, `s2Hgt₃_Φ₂`,
`s2Φ₂_monic`, `s2Φ₂_natDegree`) · C132nv0 (`dv2Supp`, `dv2Supp_ne_top_of_ne_zero`) ·
C132nv6 (`s2Hgt₃_mul_all`, `s2AddVal₃`, `s2AddVal₃_apply`) · C130s6 (`toZ`, `toZ_inj`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement invented
beyond the row's sketch and the μ₂ porting pattern.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132rp0

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130rp0
open Uniformity.Density.Tower.C132nv0 Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C132nv6
open Uniformity.Density.Tower.C80

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 1 — the concrete S2 μ₃ instantiation of `FGMNSourceData.ExactGrade`/`AboveGrade`
-/

/-- `S2Mu3ExactGrade β g ↔ μ₃(g) = β` (the μ₃ analogue of `C130rp0.S2ExactGrade`): the
cleared level-three value hits the natural grade `β` exactly. -/
def S2Mu3ExactGrade (β : ℕ) (g : Polynomial O) : Prop :=
  s2Hgt₃ h2 hq g = (β : WithTop ℤ)

/-- `S2Mu3AboveGrade β g ↔ μ₃(g) > β` (the μ₃ analogue of `C130rp0.S2AboveGrade`), defined
from the SAME `s2Hgt₃` as `S2Mu3ExactGrade`, never independently. -/
def S2Mu3AboveGrade (β : ℕ) (g : Polynomial O) : Prop :=
  (β : WithTop ℤ) < s2Hgt₃ h2 hq g

/-! ## Part 2 — the exact- and above-membership normal forms -/

/-- **the exact-membership normal form**: `S2Mu3ExactGrade β g` is EXACTLY the `ℕ∞`-level
equation `dv2Supp L Φ₂ g 21 2 = (β : ℕ∞)` — the cast-free cleared read. -/
theorem S2Mu3ExactGrade_iff_dv2Supp {β : ℕ} {g : Polynomial O} :
    S2Mu3ExactGrade h2 hq β g ↔
      dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2
        = (β : ℕ∞) := by
  unfold S2Mu3ExactGrade
  rw [s2Hgt₃_eq_dv2Supp]
  constructor
  · intro h
    exact toZ_inj (by rw [h]; norm_cast)
  · intro h
    rw [h]; norm_cast

/-- **the above-membership normal form**: `S2Mu3AboveGrade β g` is EXACTLY the `ℕ∞`-level
strict inequality `(β : ℕ∞) < dv2Supp L Φ₂ g 21 2`. -/
theorem S2Mu3AboveGrade_iff_dv2Supp {β : ℕ} {g : Polynomial O} :
    S2Mu3AboveGrade h2 hq β g ↔
      (β : ℕ∞) < dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2 := by
  unfold S2Mu3AboveGrade
  rw [s2Hgt₃_eq_dv2Supp]
  rw [show (β : WithTop ℤ) = toZ (β : ℕ∞) by norm_cast]
  exact toZ_lt_toZ_iff

/-! ## Part 3 — existence/uniqueness of the natural cleared grade -/

/-- **grade existence**: every NONZERO polynomial has SOME natural cleared μ₃ grade. -/
theorem S2Mu3ExactGrade_exists {g : Polynomial O} (hg : g ≠ 0) :
    ∃ β : ℕ, S2Mu3ExactGrade h2 hq β g := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1
    (dv2Supp_ne_top_of_ne_zero ((s2Tower h2 hq).levelDatum h2) (s2Φ₂_monic h2 hq)
      (by rw [s2Φ₂_natDegree h2 hq]; norm_num) 21 2 hg)
  exact ⟨n, (S2Mu3ExactGrade_iff_dv2Supp h2 hq).mpr hn.symm⟩

/-- **grade uniqueness**: a polynomial has AT MOST one exact μ₃ grade. -/
theorem S2Mu3ExactGrade_unique {β β' : ℕ} {g : Polynomial O}
    (h1 : S2Mu3ExactGrade h2 hq β g) (h2' : S2Mu3ExactGrade h2 hq β' g) : β = β' := by
  unfold S2Mu3ExactGrade at h1 h2'
  rw [h1] at h2'
  exact_mod_cast h2'

/-! ## Part 4 — the grade arithmetic: exact + exact → exact under multiplication

UNCONDITIONAL, direct from nv6's already fully unconditional `s2Hgt₃_mul_all` plus
`C130rp0.S2Grade_natCast_add` (reused, not re-derived). -/

/-- ★ **the grade arithmetic** — `S2Mu3ExactGrade` is closed under multiplication with
grades adding: `S2Mu3ExactGrade β g → S2Mu3ExactGrade β' h → S2Mu3ExactGrade (β+β') (g*h)`,
for ALL `g, h` (no fence). -/
theorem S2Mu3ExactGrade_mul {β β' : ℕ} {g h : Polynomial O}
    (hg : S2Mu3ExactGrade h2 hq β g) (hh : S2Mu3ExactGrade h2 hq β' h) :
    S2Mu3ExactGrade h2 hq (β + β') (g * h) := by
  unfold S2Mu3ExactGrade at hg hh ⊢
  rw [s2Hgt₃_mul_all h2 hq, hg, hh, S2Grade_natCast_add]

/-- **exact/above mutual exclusion**: a polynomial cannot be both exactly AND strictly
above the same μ₃ grade. -/
theorem S2Mu3ExactGrade_not_above {β : ℕ} {g : Polynomial O}
    (hg : S2Mu3ExactGrade h2 hq β g) : ¬ S2Mu3AboveGrade h2 hq β g := by
  unfold S2Mu3ExactGrade at hg
  unfold S2Mu3AboveGrade
  rw [hg]
  exact lt_irrefl _

/-! ## Part 5 — the zero/⊤ edge cases -/

/-- the zero polynomial has no exact μ₃ grade. -/
theorem S2Mu3ExactGrade_not_zero {β : ℕ} {g : Polynomial O}
    (hg : S2Mu3ExactGrade h2 hq β g) : g ≠ 0 := by
  intro h0
  unfold S2Mu3ExactGrade at hg
  rw [h0, s2Hgt₃_zero] at hg
  exact WithTop.top_ne_coe hg

/-- the zero-polynomial edge case, restated with the zero polynomial displayed. -/
theorem S2Mu3ExactGrade_zero_false (β : ℕ) :
    ¬ S2Mu3ExactGrade h2 hq β (0 : Polynomial O) :=
  fun hg => S2Mu3ExactGrade_not_zero h2 hq hg rfl

/-- the zero polynomial is `S2Mu3AboveGrade` every natural `β`. -/
theorem S2Mu3AboveGrade_zero (β : ℕ) : S2Mu3AboveGrade h2 hq β (0 : Polynomial O) := by
  unfold S2Mu3AboveGrade
  rw [s2Hgt₃_zero]
  exact_mod_cast WithTop.coe_lt_top (β : ℤ)

/-! ## Part 6 — the `AddValuation` tie -/

/-- `S2Mu3ExactGrade` IS the equality level-set of the packaged `AddValuation` `s2AddVal₃`.
-/
theorem S2Mu3ExactGrade_eq_addVal (β : ℕ) (g : Polynomial O) :
    S2Mu3ExactGrade h2 hq β g ↔ s2AddVal₃ h2 hq g = (β : WithTop ℤ) := by
  unfold S2Mu3ExactGrade
  rw [s2AddVal₃_apply]

/-- `S2Mu3AboveGrade` IS the strict-inequality level-set of `s2AddVal₃`. -/
theorem S2Mu3AboveGrade_eq_addVal (β : ℕ) (g : Polynomial O) :
    S2Mu3AboveGrade h2 hq β g ↔ (β : WithTop ℤ) < s2AddVal₃ h2 hq g := by
  unfold S2Mu3AboveGrade
  rw [s2AddVal₃_apply]

/-! ## Part 7 — one numeral tooth: `h₃(Φ₂) = 21` re-read as an exact grade -/

/-- **tooth**: `h₃(Φ₂) = 21 = u₃` re-read as an exact grade, off nv1's landed
`s2Hgt₃_Φ₂`. -/
theorem tooth_Φ₂ : S2Mu3ExactGrade h2 hq 21 (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) := by
  unfold S2Mu3ExactGrade
  rw [s2Hgt₃_Φ₂]
  norm_cast

end S2

end Uniformity.Density.Tower.C132rp0

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132rp0.S2Mu3ExactGrade
#print axioms Uniformity.Density.Tower.C132rp0.S2Mu3AboveGrade
#print axioms Uniformity.Density.Tower.C132rp0.S2Mu3ExactGrade_iff_dv2Supp
#print axioms Uniformity.Density.Tower.C132rp0.S2Mu3AboveGrade_iff_dv2Supp
#print axioms Uniformity.Density.Tower.C132rp0.S2Mu3ExactGrade_exists
#print axioms Uniformity.Density.Tower.C132rp0.S2Mu3ExactGrade_unique
#print axioms Uniformity.Density.Tower.C132rp0.S2Mu3ExactGrade_mul
#print axioms Uniformity.Density.Tower.C132rp0.S2Mu3ExactGrade_not_above
#print axioms Uniformity.Density.Tower.C132rp0.S2Mu3ExactGrade_not_zero
#print axioms Uniformity.Density.Tower.C132rp0.S2Mu3ExactGrade_zero_false
#print axioms Uniformity.Density.Tower.C132rp0.S2Mu3AboveGrade_zero
#print axioms Uniformity.Density.Tower.C132rp0.S2Mu3ExactGrade_eq_addVal
#print axioms Uniformity.Density.Tower.C132rp0.S2Mu3AboveGrade_eq_addVal
#print axioms Uniformity.Density.Tower.C132rp0.tooth_Φ₂

end AxCheck
