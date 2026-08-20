/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C53
import Uniformity.ChapC.C47
import Uniformity.ChapB.B05
import Uniformity.ChapB.B06

/-!
# Uniformity.ChapC.C53b — the GENERAL TWO-KEY DIGIT DICTIONARY

**Sub-unit of NODE C.53** (`C53_BLOCKED_2026-08-20.md`, GOAL 3 / leg 2), and the supplier
obstruction 4 of `C52_BLOCKED_2026-08-18.md` names.  Nothing here is signed; nothing in
`C53.lean` is edited.

## What this file is

The **two-key dictionary**: a mutually inverse pair between

* raw coefficient vectors `a : Fin (μ₂D₂) → O` of monic degree-`μ₂D₂` polynomials, and
* two-key digit vectors `c : Fin (μ₂D₂) → O`, `c` at raw index `i = j·D₂ + b·D′ + a'` being the
  degree-`a'` coefficient of the `b`-th `Φ′`-digit of the `j`-th `Φ₂`-digit,

realized as `digitVec` (`a ↦ c`) and `polyVec` (`c ↦ a`), with `polyVec` computed from the
explicit two-key monomial expansion `Φ₂^{μ₂} + ∑ᵢ cᵢ·X^{a'}Φ′^{b}Φ₂^{j}`.  Both directions are
proved from the one-key development API alone (B.02 `dev`, B.03 `degree_dev_lt`,
B.05 `sum_dev_eq`, B.06 `dev_unique`) — no polygon, no purity, no residual, no completeness, no
Hensel lifting.  Style modelled on `C110.lean` clause 2's `dev_sub_C`: an exact identity in
`O[X]`, never a "the change of coordinates is unitriangular" hand-wave.

## Status

Sorry-free. Axiom footprint: Lean core (AxCheck footer).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Uniformity Uniformity.Density Uniformity.Density.Leaf IsLocalRing IsDiscreteValuationRing
open Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### The two-key monomial basis -/

/-- **The two-key monomial** `X^{a}·Φ′^{b}·Φ₂^{j}` (`Φ′ = F.key`, `Φ₂ = composedKey T`).  For
`a < D′`, `b < e₂f₂`, `j < μ₂` it is monic of degree exactly `j·D₂ + b·D′ + a`, and these
`μ₂D₂` monomials together with `Φ₂^{μ₂}` are the basis in which the two-key digits are the
coordinates. -/
noncomputable def twoKeyMon {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (j a b : ℕ) : Polynomial O :=
  X ^ a * F.key ^ b * (composedKey T) ^ j

/-- The two-key monomial at the **raw index** `i`, decoded exactly as `budgetSlot` decodes it:
`j = i / D₂`, `a = i % D₂ % D′`, `b = i % D₂ / D′`, so that `i = j·D₂ + b·D′ + a`. -/
noncomputable def slotMon {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (i : ℕ) : Polynomial O :=
  twoKeyMon T (i / T.D₂) (i % T.D₂ % (F.e₁ * F.f₁)) (i % T.D₂ / (F.e₁ * F.f₁))

/-- **The reconstruction map on polynomials**: the monic degree-`μ₂D₂` polynomial whose two-key
digit vector is `c`. -/
noncomputable def slotPoly {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (μ₂ : ℕ) (c : Fin (μ₂ * T.D₂) → O) : Polynomial O :=
  (composedKey T) ^ μ₂ + ∑ i : Fin (μ₂ * T.D₂), C (c i) * slotMon T i.1

/-- **The digit map** `a ↦ c`: the two-key digit vector of `monicPoly a`, indexed by the same
raw slot decoding `budgetSlot` uses. -/
noncomputable def digitVec {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (μ₂ : ℕ) (a : Fin (μ₂ * T.D₂) → O) : Fin (μ₂ * T.D₂) → O :=
  fun i => (dev F.key (dev (composedKey T) (monicPoly a) (i.1 / T.D₂))
    (i.1 % T.D₂ / (F.e₁ * F.f₁))).coeff (i.1 % T.D₂ % (F.e₁ * F.f₁))

/-- **The reconstruction map** `c ↦ a`: the raw coefficient vector of `slotPoly`. -/
noncomputable def polyVec {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (μ₂ : ℕ) (c : Fin (μ₂ * T.D₂) → O) : Fin (μ₂ * T.D₂) → O :=
  fun i => (slotPoly T μ₂ c).coeff i.1

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.twoKeyMon
#print axioms Uniformity.Density.Tower.slotMon
#print axioms Uniformity.Density.Tower.slotPoly
#print axioms Uniformity.Density.Tower.digitVec
#print axioms Uniformity.Density.Tower.polyVec

end AxCheck
