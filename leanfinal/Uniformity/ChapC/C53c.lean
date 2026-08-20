/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C53
import Uniformity.ChapB.B15
import Uniformity.ChapB.B18
import Uniformity.ChapB.B30

/-!
# Uniformity.ChapC.C53c — `TriangularDigitRead` machine-REFUTED

**Sub-unit of NODE C.53** (companion to `C53_LEG2_REFUTED_2026-08-20.md`): the PROSE refutation
of C.53 leg 2 (`TriangularDigitRead`, `C53.lean`), converted into a machine-checked theorem, by
the record's explicit numeric instance.  Nothing here is signed; nothing in `C53.lean` or
`C53b.lean` is edited.  Pattern: `C35b.lean` (`d13_refuted` + `hasLabel_natDegree_dvd_false`).

## The refuting instance (the record's, verbatim)

* frame `linFrame hπ : KeyFrame O π` — `Φ′ = X + π`, `(e₁, f₁, h) = (1, 1, 1)`, `D′ = 1`,
  over any DVR base; pin `H₀ = 1`;
* tower `linTower hπ : TowerDatum (linFrame hπ) 1 _` — `(e₂, f₂, u₂) = (2, 1, 3)`,
  `ψ₂ = T + 1`; fences: `hcomp : 2 ≤ 2`, `hcop : Coprime 3 2`, `hfloor : 2·1·1 = 2 < 3`;
* derived: `D₂ = 2`, `E₂ = 6`, `μ₂ = 1`, `n = μ₂D₂ = 2`, floors `(4, 2)` at slots `0, 1`;
* `f₂ = 1` and `f₁ = 1` make C.43's `composedKey` explicitly `Φ₂ = (X+π)² − C w` for a single
  constant `w : O` (`slotIdx 3 = 0`, one `stageLiftIA` summand), so `Φ₂.coeff 1 = 2π` EXACTLY —
  no appeal to C.47's `cLift` bounds and, crucially, **no appeal to C.50's transcribed
  `gridWeight` scope note** (corpus prose): the numeric route needs only landed theorems.
* At window `N = 2`, class `c = 0`, and residue characteristic ≠ 2 (`IsUnit (2 : O)`):
  RAW-BOX contains `0` (witness `a = 0`, `addVal 0 = ⊤`), DIGIT-BOX does not — any lift `a`
  of `0` has `a 1 ∈ 𝔪²`, so the slot-1 two-key digit `a 1 − 2π` has `addVal = 1 < 2 = floor`.
* Absolute realization: `O = ℤ_[3]`, `π = 3` (both `Irreducible (3 : ℤ_[3])` and
  `IsUnit (2 : ℤ_[3])` hold), so nothing is vacuous.

**Why NOT the `s2Frame` workhorse** (today's C.27/C.35b/C.61 counterexample frame): there the
residue characteristic IS 2, `2π = 4` collapses into the uniformizer tower, and the obstructing
digit of `X^{D₂}` migrates into the `stageLiftO` correction constant — exactly the computation
the record's instance is designed to avoid.  The linear frame keeps the obstructing digit
`a 1 − 2π` independent of the (opaque) lift constant `w`.

## Deliverables (the OPEN list; filled in committed increments)

1. `linKey` + coefficient facts — DONE below.
2. frame legs: `linKey_irr` (Eisenstein), heights/`suppVal`/purity/`sideSet`/pin, `resirr`.
3. `linFrame : KeyFrame O π`, `linFrame_pin : (linFrame hπ).Pin 1`.
4. stage-field `Field` instance; `linTower : TowerDatum (linFrame hπ) 1 _`.
5. `composedKey_linTower : ∃ w : O, composedKey (linTower hπ) = (X + C π)^2 − C w`.
6. the slot-1 digit: `(dev Φ′ (dev Φ₂ (monicPoly a) 0) 1).coeff 0 = a 1 − 2π`.
7. `budgetFloor (linTower hπ) 1 0 0 1 = 2` (numeral).
8. `triangularDigitRead_false_at : ¬ TriangularDigitRead (linTower hπ) 1 2` given `IsUnit 2`.
9. absolute closure over `ℤ_[3]`:
   `triangularDigitRead_false : ¬ ∀ …(guards `Irreducible π`, `0 < μ₂`, `1 ≤ F.h`)…,
   TriangularDigitRead T μ₂ N`, its unguarded corollary, the exact-binder companion at
   GOAL 3's printed shape (faithfulness machine-checked, per the C35b pattern), and the
   conjunction corollary `¬ (TowerBudgetIff T μ₂ ∧ TriangularDigitRead T μ₂ N)` (the two-leg
   discharge route of `budgetBoxRead_of_legs`, closed).

## Status

In progress; every committed state compiles green with zero `sorry` and Lean-core axioms only.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C53c

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## 1. The linear key `Φ′ = X + π` -/

/-- the refuting frame's stage key: `Φ′ = X + π`, monic of degree `1 = e₁f₁`. -/
noncomputable def linKey (π : O) : Polynomial O := Polynomial.X + Polynomial.C π

theorem linKey_monic : (linKey π).Monic := monic_X_add_C π

theorem linKey_natDegree : (linKey π).natDegree = 1 := natDegree_X_add_C π

theorem linKey_coeff0 : (linKey π).coeff 0 = π := by simp [linKey]

theorem linKey_coeff1 : (linKey π).coeff 1 = 1 := by simp [linKey, coeff_C]

end Uniformity.Density.Tower.C53c

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C53c.linKey
#print axioms Uniformity.Density.Tower.C53c.linKey_monic

end AxCheck
