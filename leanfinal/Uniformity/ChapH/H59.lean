/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Order.Fin.Basic

/-!
# Uniformity.ChapH.H59 — `TriangularUnitPivot`, triangularity with unit pivots

**Chapter H, NODE H.59** (`blueprint/CHAP-H_general_induction.md` §9, source `EFF.GENIND.156`,
`ANNEX R R2.1`). For a commutative ring `R` and `Φ : (Fin n → R) → (Fin n → R)`, the datum
witnessing that `Φ` is *triangular with unit pivots* for the order `0 < 1 < ⋯ < n−1`: pivots
`c : Fin n → R`, each a unit, and tails `g i` depending only on the coordinates `< i`, with
`Φ v i = c i * v i + g i v` for every `v` and `i`.

Definitional, no proof obligation (a `structure` declares field *types*, not proofs of them).
DEPENDS: none.

**Why a structure and not a comment.** `EFF.GENIND.156`'s supersession kind is `license`, not
`wording-rider`: although the surface instruction reads "read triangular as triangular with unit
pivots", the operative content is a new condition together with a proof of what it buys (onto,
constant fibres), which a wording substitution is not. Chapter H therefore lands the condition as
a definition with theorems attached (H.60, H.61), against the counterexample at H.62 showing that
triangularity ALONE gives neither surjectivity nor constant fibres over a truncated DVR.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **Triangular with unit pivots.**  `Φ` solves each output slot as `unit × (its input slot) +
(a function of strictly earlier input slots)`.  This is the condition ANNEX R R2 identifies as the
missing displayed step of `GENIND-6(c)`: triangularity ALONE does not give surjectivity or constant
fibres over a truncated DVR (H.62). -/
structure TriangularUnitPivot {R : Type*} [CommRing R] {n : ℕ}
    (Φ : (Fin n → R) → (Fin n → R)) where
  /-- The pivots. -/
  pivot : Fin n → R
  /-- The strictly-earlier part. -/
  tail : (i : Fin n) → (Fin n → R) → R
  /-- Each pivot is a unit. -/
  pivot_isUnit : ∀ i, IsUnit (pivot i)
  /-- The tail at `i` depends only on coordinates `< i`. -/
  tail_lower : ∀ i v w, (∀ j : Fin n, j < i → v j = w j) → tail i v = tail i w
  /-- The displayed form. -/
  apply_eq : ∀ v i, Φ v i = pivot i * v i + tail i v

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.TriangularUnitPivot

end AxCheck
