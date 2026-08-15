/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Ring

/-!
# Uniformity.ChapH.H80 — the genre-E development identities

**Chapter H, NODE H.80** (`blueprint/CHAP-H_general_induction.md` §12, the `n = 4` template). In
any commutative ring,

`(X² − s)² + (α₁X + α₀)(X² − s) + (β₁X + β₀)`
` = X⁴ + α₁X³ + (α₀ − 2s)X² + (β₁ − sα₁)X + (β₀ − sα₀ + s²)`,

so the four opening coordinates of a genre-E development read `b₃ = α₁`, `b₂ = α₀ − 2s`,
`b₁ = β₁ − sα₁`, `b₀ = β₀ − sα₀ + s²`.

**Triangularity with unit pivots.** Each `b_j` is its own `A`-coordinate (`α₁`, `α₀`, `β₁`, `β₀`
respectively) plus terms involving only *later* coordinates, and every pivot is `1` — visible by
inspection of the four displayed right-hand sides. This is the concrete witness that §9's
`TriangularUnitPivot` condition (ANNEX R R2's global unit-pivot requirement) is satisfiable.

DEPENDS: none (mathlib `Polynomial.C` as a ring hom: `map_sub`, `map_add`, `map_mul`, `map_pow`,
`map_ofNat`; then `ring`).

SOURCE: `EFF.GENIND.68` (`LEMMA GENIND-4`: the four displayed identities and the proof *"the direct
expansion of `(x²−s)² + (α₁x+α₀)(x²−s) + (β₁x+β₀)`"*), decorrelated by the QSCOUT22 `Q22-B`
cross-derivation.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

open Polynomial in
/-- The genre-E development identity: expanding `(X² − s)² + (α₁X + α₀)(X² − s) + (β₁X + β₀)`
gives the opening coordinates `b₃ = α₁`, `b₂ = α₀ − 2s`, `b₁ = β₁ − sα₁`, `b₀ = β₀ − sα₀ + s²`.
The pivots are all `1`, which is `TriangularUnitPivot`'s hypothesis realised. -/
theorem quartic_dev_E {R : Type*} [CommRing R] (s a₁ a₀ b₁ b₀ : R) :
    ((X ^ 2 - C s) ^ 2 + (C a₁ * X + C a₀) * (X ^ 2 - C s) + (C b₁ * X + C b₀))
      = X ^ 4 + C a₁ * X ^ 3 + C (a₀ - 2 * s) * X ^ 2 + C (b₁ - s * a₁) * X
        + C (b₀ - s * a₀ + s ^ 2) := by
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
  ring

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.quartic_dev_E

end AxCheck
