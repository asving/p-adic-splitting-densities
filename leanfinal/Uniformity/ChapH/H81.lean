/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Ring

/-!
# Uniformity.ChapH.H81 — the genre-F development identities

**Chapter H, NODE H.81** (`blueprint/CHAP-H_general_induction.md` §12, the `n = 4` template). In
any commutative ring, with `φ = X² + p₁X + p₀`,

`φ² + (α₁X + α₀)φ + (β₁X + β₀)`
` = X⁴ + (2p₁ + α₁)X³ + (p₁² + 2p₀ + α₁p₁ + α₀)X² + (2p₁p₀ + α₁p₀ + α₀p₁ + β₁)X`
`   + (p₀² + α₀p₀ + β₀)`,

so the four opening coordinates of a genre-F development read `b₃ = 2p₁ + α₁`,
`b₂ = p₁² + 2p₀ + α₁p₁ + α₀`, `b₁ = 2p₁p₀ + α₁p₀ + α₀p₁ + β₁`, `b₀ = p₀² + α₀p₀ + β₀`.

**Triangularity with unit pivots.** Each `b_j` is its own `A`-coordinate (`α₁`, `α₀`, `β₁`, `β₀`
respectively) plus terms in the fixed data `p₁, p₀` and only *earlier-listed* `A`-coordinates, and
every pivot is `1` — visible by inspection of the four displayed right-hand sides. This is the
genre-F companion of H.80's genre-E witness for §9's `TriangularUnitPivot`.

**Both characteristics, by construction.** `EFF.GENH4.15`'s proof closes *"both characteristics (at
`p = 2` the pins `2ĉ₁π^k` etc. degenerate, the budgets do not — the cancellations are universal
identities)"*. The statement below is a `ring` identity in a bare `CommRing` with no `p ≠ 2`
hypothesis, which is exactly that claim — so this node discharges the corpus's
characteristic-uniformity claim for the development layer outright.

DEPENDS: none (mathlib `Polynomial.C` as a ring hom: `map_add`, `map_mul`, `map_pow`, `map_ofNat`;
then `ring`).

SOURCE: `EFF.GENH4.15` (`LEMMA GENH4-1F`, the four displayed relations verbatim, and its proof
*"The relations are the expansion of `φ² + A₁φ + A₀`"*).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

open Polynomial in
/-- The genre-F development identity: expanding `φ² + (α₁X + α₀)φ + (β₁X + β₀)` at
`φ = X² + p₁X + p₀` gives the opening coordinates `b₃ = 2p₁ + α₁`,
`b₂ = p₁² + 2p₀ + α₁p₁ + α₀`, `b₁ = 2p₁p₀ + α₁p₀ + α₀p₁ + β₁`, `b₀ = p₀² + α₀p₀ + β₀`.
The pivots are all `1`, which is `TriangularUnitPivot`'s hypothesis realised in genre F. -/
theorem quartic_dev_F {R : Type*} [CommRing R] (p₁ p₀ a₁ a₀ b₁ b₀ : R) :
    ((X ^ 2 + C p₁ * X + C p₀) ^ 2 + (C a₁ * X + C a₀) * (X ^ 2 + C p₁ * X + C p₀)
        + (C b₁ * X + C b₀))
      = X ^ 4 + C (2 * p₁ + a₁) * X ^ 3 + C (p₁ ^ 2 + 2 * p₀ + a₁ * p₁ + a₀) * X ^ 2
        + C (2 * p₁ * p₀ + a₁ * p₀ + a₀ * p₁ + b₁) * X + C (p₀ ^ 2 + a₀ * p₀ + b₀) := by
  simp only [map_add, map_mul, map_pow, map_ofNat]
  ring

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.quartic_dev_F

end AxCheck
