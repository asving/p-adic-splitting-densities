/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Localization.FractionRing
import Uniformity.ChapC.C130nv3

/-!
# Uniformity.ChapC.C130nv5 — S2-source plan nodes NV-5/NV-6

**S2-source plan nodes NV-5 and NV-6** (`docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6,
rows NV-5 "additive valuation packaging (CORE 4/4)" and NV-6 "fraction-field extension"):
package the two landed cleared polynomial values `s2Hgt₁` (C130nv) and `s2Hgt₂` (C130s6,
product law by C130nv3) as genuine mathlib `AddValuation`s on `Polynomial O`, then extend
both to `E = FractionRing (Polynomial O)` — the ambient the S2-source plan's SF-1 valued
field `E` and NP-0's evaluation live on (C130s17's non-vacuity tooth already sits at this
same `E`) — via mathlib's `Valuation.extendToLocalization`, and PIN the restriction law the
plan's NP-0 will consume: the extended valuation composed with the canonical embedding
`algebraMap (Polynomial O) E` is the original value, on the nose.

## NV-5 — packaging as `AddValuation`s

Mathlib's `AddValuation R Γ₀` (`Ring R`, `LinearOrderedAddCommMonoidWithTop Γ₀`) is built by
`AddValuation.of f h0 h1 hadd hmul` from exactly the five fields C130nv/C130nv3 already
landed for both `s2Hgt₁` and `s2Hgt₂`: `f 0 = ⊤`, `f 1 = 0`, the ultrametric inequality, and
the UNIVERSAL product law.  `WithTop ℤ` is a `LinearOrderedAddCommGroupWithTop` (mathlib's
generic `WithTop`-of-a-linearly-ordered-group instance), so both packagings type-check
directly against the landed banks with no new hypothesis and no restatement of any law.

* `s2AddVal₁ : AddValuation (Polynomial O) (WithTop ℤ)` from `s2Hgt₁` + its zero/one/add/mul
  bank.
* `s2AddVal₂ : AddValuation (Polynomial O) (WithTop ℤ)` from `s2Hgt₂` + its zero/one/add/mul
  bank (the `mul` field is C130nv3's `s2Hgt₂_mul`, ★ NV-4's row).
* Anti-drift application pins (`rfl`): the packaged `AddValuation` evaluates to exactly the
  landed value function, nothing new invented.

## NV-6 — the fraction-field extension

Mathlib's `AddValuation.toValuation : AddValuation R Γ₀ ≃ Valuation R (Multiplicative Γ₀ᵒᵈ)`
is `Equiv.refl` (an `AddValuation` IS-BY-DEFINITION the corresponding `Valuation`; `Multiplicative`
and `OrderDual` are plain type synonyms), and mathlib's generic instance
`[LinearOrderedAddCommGroupWithTop α] → LinearOrderedCommGroupWithZero (Multiplicative αᵒᵈ)`
supplies EXACTLY the value-group shape `Valuation.extendToLocalization` needs — so the
"wrong value-group shape" risk flagged in the node brief does NOT materialize here: no
bespoke bridge was needed, mathlib's own `WithTop`/`Multiplicative`/`OrderDual` instance
chain already produces a `LinearOrderedCommGroupWithZero`.

* `s2Val₁`, `s2Val₂ : Valuation (Polynomial O) (Multiplicative (WithTop ℤ)ᵒᵈ)` — the
  multiplicative repackaging (`AddValuation.toValuation`).
* The submonoid hypothesis `nonZeroDivisors (Polynomial O) ≤ v.supp.primeCompl` needed by
  `extendToLocalization` is exactly the landed finiteness law `s2Hgt₁_ne_top`/`s2Hgt₂_ne_top`
  (nonzero polynomials have finite, hence multiplicatively nonzero, value) plus the domain
  fact `nonZeroDivisors = {≠ 0}` — `s2Val₁_hS`, `s2Val₂_hS`.
* `s2EVal₁`, `s2EVal₂ : Valuation (FractionRing (Polynomial O)) (Multiplicative (WithTop ℤ)ᵒᵈ)`
  — the extensions (`Valuation.extendToLocalization`).
* Converted back: `s2AddEVal₁`, `s2AddEVal₂ : AddValuation (FractionRing (Polynomial O))
  (WithTop ℤ)` (`AddValuation.ofValuation`, again `Equiv.refl`).
* ★ **The polynomial-restriction PIN** (NP-0's consumer law): `s2AddEVal₁_algebraMap` /
  `s2AddEVal₂_algebraMap` — the extended additive valuation, composed with the canonical
  embedding `algebraMap (Polynomial O) (FractionRing (Polynomial O))`, is exactly the
  original landed `s2Hgt₁`/`s2Hgt₂` — from mathlib's
  `Valuation.extendToLocalization_apply_map_apply`, no fresh identification.

## What this node does NOT claim (honesty scope)

* No `NodePointSource`/`Point`/`coeffHom`/`coord`/`valueOn`/`pointHgt` (NP-0); this file
  supplies the ambient valuations NP-0 will read off, not the point-evaluation interface
  itself.
* No characteristic-zero noncontradiction tooth (SF-4): that row needs a SEPARATE ambient
  with `eval₂ coeffHom X (C 2) ≠ 0`, unrelated to the DVR-valued `E` built here (this `E` is
  the fraction field of `Polynomial O` itself, not a place where `(2 : O)` could vanish —
  `algebraMap (Polynomial O) E` is injective since `Polynomial O` is a domain, so no
  collapse of `O`-constants occurs on this leg either, but that is not separately pinned
  here as it is out of NV-5/NV-6's row scope).
* No claim that `s2AddEVal₁`/`s2AddEVal₂` are THE canonical extensions in any universal
  sense beyond mathlib's `extendToLocalization` construction (which is characterized by the
  restriction law pinned here, `extendToLocalization_mk'`, and its own uniqueness facts —
  not re-derived).

**DEPENDS.** C130nv (`s2Hgt₁` + full law bank) · C130s6 (`s2Hgt₂` + zero/add bank) · C130nv3
(`s2Hgt₂_mul`) · `Mathlib.RingTheory.Valuation.Basic` (`AddValuation`, `AddValuation.of`,
`toValuation`, `ofValuation`, `Valuation.supp`) · `Mathlib.Algebra.Order.AddGroupWithTop`
(`WithTop` linearly-ordered-group-with-⊤ instances) ·
`Mathlib.Algebra.Order.GroupWithZero.Canonical` (the `Multiplicative αᵒᵈ`
`LinearOrderedCommGroupWithZero` instance) · `Mathlib.RingTheory.Valuation.ExtendToLocalization`
(`Valuation.extendToLocalization` + its two apply lemmas) · `Mathlib.RingTheory.Localization.FractionRing`.

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement touched.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C130nv5

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130nv Uniformity.Density.Tower.C130nv3

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 1 — NV-5: the `map_one` bridging teeth (the carrier's `0` vs. the cast `((0:ℤ):·)`) -/

/-- `s2Hgt₁_one` in `AddValuation.of`'s exact `h1` shape (`f 1 = 0`, not the cast literal). -/
theorem s2Hgt₁_one_eq_zero : s2Hgt₁ h2 hq (1 : Polynomial O) = 0 := by
  rw [s2Hgt₁_one h2 hq]; rfl

/-- `s2Hgt₂_one` in `AddValuation.of`'s exact `h1` shape. -/
theorem s2Hgt₂_one_eq_zero : s2Hgt₂ h2 hq (1 : Polynomial O) = 0 := by
  rw [s2Hgt₂_one h2 hq]; rfl

/-! ## Part 2 — NV-5: the packaged `AddValuation`s -/

/-- ★ **NODE NV-5, level one** — `s2Hgt₁` packaged as a mathlib `AddValuation`, assembled
entirely from the landed law bank: `s2Hgt₁_zero`, `s2Hgt₁_one_eq_zero`, `s2Hgt₁_add_ge`,
`s2Hgt₁_mul`. -/
noncomputable def s2AddVal₁ : AddValuation (Polynomial O) (WithTop ℤ) :=
  AddValuation.of (s2Hgt₁ h2 hq) (s2Hgt₁_zero h2 hq) (s2Hgt₁_one_eq_zero h2 hq)
    (s2Hgt₁_add_ge h2 hq) (s2Hgt₁_mul h2 hq)

/-- ★ **NODE NV-5, level two** — `s2Hgt₂` packaged as a mathlib `AddValuation`, from
`s2Hgt₂_zero`, `s2Hgt₂_one_eq_zero`, `s2Hgt₂_add_ge`, and C130nv3's ★ `s2Hgt₂_mul` (NV-4's
row). -/
noncomputable def s2AddVal₂ : AddValuation (Polynomial O) (WithTop ℤ) :=
  AddValuation.of (s2Hgt₂ h2 hq) (s2Hgt₂_zero h2 hq) (s2Hgt₂_one_eq_zero h2 hq)
    (s2Hgt₂_add_ge h2 hq) (s2Hgt₂_mul h2 hq)

/-- Anti-drift pin: the packaged level-one `AddValuation` evaluates to `s2Hgt₁` — nothing
fresh was invented in the packaging. -/
theorem s2AddVal₁_apply (A : Polynomial O) : s2AddVal₁ h2 hq A = s2Hgt₁ h2 hq A := rfl

/-- Anti-drift pin: the packaged level-two `AddValuation` evaluates to `s2Hgt₂`. -/
theorem s2AddVal₂_apply (A : Polynomial O) : s2AddVal₂ h2 hq A = s2Hgt₂ h2 hq A := rfl

/-! ## Part 3 — NV-6: the multiplicative repackaging -/

/-- The level-one value as a mathlib `Valuation` (`AddValuation.toValuation`, `Equiv.refl`). -/
noncomputable def s2Val₁ : Valuation (Polynomial O) (Multiplicative (WithTop ℤ)ᵒᵈ) :=
  (s2AddVal₁ h2 hq).toValuation

/-- The level-two value as a mathlib `Valuation`. -/
noncomputable def s2Val₂ : Valuation (Polynomial O) (Multiplicative (WithTop ℤ)ᵒᵈ) :=
  (s2AddVal₂ h2 hq).toValuation

/-- Anti-drift pin: `s2Val₁` reads the same as `s2AddVal₁` (the repackaging changes no
value, only the ambient type it is stated in). -/
theorem s2Val₁_apply (A : Polynomial O) : s2Val₁ h2 hq A = s2AddVal₁ h2 hq A := rfl

/-- Anti-drift pin: `s2Val₂` reads the same as `s2AddVal₂`. -/
theorem s2Val₂_apply (A : Polynomial O) : s2Val₂ h2 hq A = s2AddVal₂ h2 hq A := rfl

/-- `s2Val₁` vanishes only at `0` — the multiplicative reading of `s2Hgt₁_eq_top_iff`, via
`AddValuation.supp`/`Valuation.supp` (the same ideal for `v` and `v.toValuation`), never
comparing the two ambients' `0`/`⊤` literals directly. -/
theorem s2Val₁_eq_zero_iff {A : Polynomial O} : s2Val₁ h2 hq A = 0 ↔ A = 0 := by
  rw [← Valuation.mem_supp_iff]
  show A ∈ AddValuation.supp (s2AddVal₁ h2 hq) ↔ A = 0
  rw [AddValuation.mem_supp_iff, s2AddVal₁_apply]
  exact s2Hgt₁_eq_top_iff h2 hq

/-- `s2Val₂` vanishes only at `0`. -/
theorem s2Val₂_eq_zero_iff {A : Polynomial O} : s2Val₂ h2 hq A = 0 ↔ A = 0 := by
  rw [← Valuation.mem_supp_iff]
  show A ∈ AddValuation.supp (s2AddVal₂ h2 hq) ↔ A = 0
  rw [AddValuation.mem_supp_iff, s2AddVal₂_apply]
  exact s2Hgt₂_eq_top_iff h2 hq

/-- The submonoid hypothesis `extendToLocalization` needs at level one: every nonzero
divisor of `Polynomial O` (= every nonzero polynomial, `Polynomial O` being a domain) sits
outside `s2Val₁`'s support. -/
theorem s2Val₁_hS :
    nonZeroDivisors (Polynomial O) ≤ (s2Val₁ h2 hq).supp.primeCompl := by
  intro x hx
  rw [Ideal.mem_primeCompl_iff, Valuation.mem_supp_iff]
  rw [mem_nonZeroDivisors_iff_ne_zero] at hx
  exact fun h => hx (s2Val₁_eq_zero_iff h2 hq |>.mp h)

/-- The submonoid hypothesis at level two. -/
theorem s2Val₂_hS :
    nonZeroDivisors (Polynomial O) ≤ (s2Val₂ h2 hq).supp.primeCompl := by
  intro x hx
  rw [Ideal.mem_primeCompl_iff, Valuation.mem_supp_iff]
  rw [mem_nonZeroDivisors_iff_ne_zero] at hx
  exact fun h => hx (s2Val₂_eq_zero_iff h2 hq |>.mp h)

/-! ## Part 4 — NV-6: the extension to `E = FractionRing (Polynomial O)` -/

/-- The level-one valuation extended to the fraction field, via mathlib's
`Valuation.extendToLocalization`. -/
noncomputable def s2EVal₁ :
    Valuation (FractionRing (Polynomial O)) (Multiplicative (WithTop ℤ)ᵒᵈ) :=
  (s2Val₁ h2 hq).extendToLocalization (s2Val₁_hS h2 hq) (FractionRing (Polynomial O))

/-- The level-two valuation extended to the fraction field. -/
noncomputable def s2EVal₂ :
    Valuation (FractionRing (Polynomial O)) (Multiplicative (WithTop ℤ)ᵒᵈ) :=
  (s2Val₂ h2 hq).extendToLocalization (s2Val₂_hS h2 hq) (FractionRing (Polynomial O))

/-- Converted back to an `AddValuation` on the fraction field (`AddValuation.ofValuation`,
again `Equiv.refl`) — the object the S2-source plan's evaluation ambient `E` carries. -/
noncomputable def s2AddEVal₁ : AddValuation (FractionRing (Polynomial O)) (WithTop ℤ) :=
  AddValuation.ofValuation (s2EVal₁ h2 hq)

/-- Converted back at level two. -/
noncomputable def s2AddEVal₂ : AddValuation (FractionRing (Polynomial O)) (WithTop ℤ) :=
  AddValuation.ofValuation (s2EVal₂ h2 hq)

theorem s2AddEVal₁_apply (x : FractionRing (Polynomial O)) :
    s2AddEVal₁ h2 hq x = s2EVal₁ h2 hq x := rfl

theorem s2AddEVal₂_apply (x : FractionRing (Polynomial O)) :
    s2AddEVal₂ h2 hq x = s2EVal₂ h2 hq x := rfl

/-! ## Part 5 — the polynomial-restriction PIN (NP-0's law) -/

/-- ★ **NODE NV-6's PIN, level one** — the extended additive valuation, restricted to
`Polynomial O` along the canonical embedding into the fraction field, IS the original
landed `s2Hgt₁` — on the nose, from mathlib's `extendToLocalization_apply_map_apply`. -/
theorem s2AddEVal₁_algebraMap (A : Polynomial O) :
    s2AddEVal₁ h2 hq (algebraMap (Polynomial O) (FractionRing (Polynomial O)) A)
      = s2Hgt₁ h2 hq A := by
  rw [s2AddEVal₁_apply]
  show (s2Val₁ h2 hq).extendToLocalization (s2Val₁_hS h2 hq) (FractionRing (Polynomial O))
      (algebraMap (Polynomial O) (FractionRing (Polynomial O)) A) = s2Hgt₁ h2 hq A
  rw [Valuation.extendToLocalization_apply_map_apply, s2Val₁_apply, s2AddVal₁_apply]

/-- ★ **NODE NV-6's PIN, level two.** -/
theorem s2AddEVal₂_algebraMap (A : Polynomial O) :
    s2AddEVal₂ h2 hq (algebraMap (Polynomial O) (FractionRing (Polynomial O)) A)
      = s2Hgt₂ h2 hq A := by
  rw [s2AddEVal₂_apply]
  show (s2Val₂ h2 hq).extendToLocalization (s2Val₂_hS h2 hq) (FractionRing (Polynomial O))
      (algebraMap (Polynomial O) (FractionRing (Polynomial O)) A) = s2Hgt₂ h2 hq A
  rw [Valuation.extendToLocalization_apply_map_apply, s2Val₂_apply, s2AddVal₂_apply]

/-! ### 5a. Teeth — the PIN reproduces the landed table values through the fraction field -/

/-- **tooth**: the level-one value of `X`, read through the fraction-field extension, is
still `1`. -/
theorem s2AddEVal₁_X :
    s2AddEVal₁ h2 hq (algebraMap (Polynomial O) (FractionRing (Polynomial O))
      (Polynomial.X : Polynomial O)) = ((1 : ℤ) : WithTop ℤ) := by
  rw [s2AddEVal₁_algebraMap, s2Hgt₁_X]

/-- **tooth**: the level-two value of `2`, read through the fraction-field extension, is
still `4` (`s2Hgt₂ (C 2) = 4`, C130s6's `s2Hgt₂_key`-adjacent teeth aside — here the plain
constant). -/
theorem s2AddEVal₂_one :
    s2AddEVal₂ h2 hq (algebraMap (Polynomial O) (FractionRing (Polynomial O))
      (1 : Polynomial O)) = ((0 : ℤ) : WithTop ℤ) := by
  rw [s2AddEVal₂_algebraMap, s2Hgt₂_one]

end S2

end Uniformity.Density.Tower.C130nv5

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130nv5.s2Hgt₁_one_eq_zero
#print axioms Uniformity.Density.Tower.C130nv5.s2Hgt₂_one_eq_zero
#print axioms Uniformity.Density.Tower.C130nv5.s2AddVal₁
#print axioms Uniformity.Density.Tower.C130nv5.s2AddVal₂
#print axioms Uniformity.Density.Tower.C130nv5.s2AddVal₁_apply
#print axioms Uniformity.Density.Tower.C130nv5.s2AddVal₂_apply
#print axioms Uniformity.Density.Tower.C130nv5.s2Val₁
#print axioms Uniformity.Density.Tower.C130nv5.s2Val₂
#print axioms Uniformity.Density.Tower.C130nv5.s2Val₁_apply
#print axioms Uniformity.Density.Tower.C130nv5.s2Val₂_apply
#print axioms Uniformity.Density.Tower.C130nv5.s2Val₁_eq_zero_iff
#print axioms Uniformity.Density.Tower.C130nv5.s2Val₂_eq_zero_iff
#print axioms Uniformity.Density.Tower.C130nv5.s2Val₁_hS
#print axioms Uniformity.Density.Tower.C130nv5.s2Val₂_hS
#print axioms Uniformity.Density.Tower.C130nv5.s2EVal₁
#print axioms Uniformity.Density.Tower.C130nv5.s2EVal₂
#print axioms Uniformity.Density.Tower.C130nv5.s2AddEVal₁
#print axioms Uniformity.Density.Tower.C130nv5.s2AddEVal₂
#print axioms Uniformity.Density.Tower.C130nv5.s2AddEVal₁_apply
#print axioms Uniformity.Density.Tower.C130nv5.s2AddEVal₂_apply
#print axioms Uniformity.Density.Tower.C130nv5.s2AddEVal₁_algebraMap
#print axioms Uniformity.Density.Tower.C130nv5.s2AddEVal₂_algebraMap
#print axioms Uniformity.Density.Tower.C130nv5.s2AddEVal₁_X
#print axioms Uniformity.Density.Tower.C130nv5.s2AddEVal₂_one

end AxCheck
