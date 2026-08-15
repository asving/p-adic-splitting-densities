/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapH.H87 — the three-term carry cancellation (the `z̄`-twist kill)

**Chapter H, NODE H.87** (`blueprint/CHAP-H_general_induction.md` §12; source `EFF.GENH4.23`,
the signature computation). *The three-term carry cancellation, both characteristics.*

`A₀′`'s `2dμ`-digit (even slot) collects three terms: `S₀` (its own), `+z·s²` from `−C·p₀′` (the
carry times the key's constant term) and `−2·z·s²` from the `α₁`-component of `−C·p₀′`; the total
is `S₀ + z·s² − 2·z·s² = S₀ − z·s² = 0` since `S₀ = z·s²`.  In characteristic `2` the same total
reads `z·s² + z·s² = 2·(z·s²) = 0`.  The companion `A₁′` kill is `S₁ + 2·s = 0` given `S₁ = −(2·s)`.

These are *identities* in a commutative ring, nothing more: per the node's ⚠ note, the `W-9`
cocycle mention in the source is a frame citation that Chapter H does not consume, and no
type-preservation (bijection) claim is made or implied here.

DEPENDS: none.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **NODE H.87 (i).** The three-term `2dμ`-slot total vanishes: `S₀ + z·s² − 2·(z·s²) = 0`
whenever `S₀ = z·s²`.  Every characteristic. -/
theorem carry_cancel {R : Type*} [CommRing R] {z s S₀ : R} (h : S₀ = z * s ^ 2) :
    S₀ + z * s ^ 2 - 2 * (z * s ^ 2) = 0 := by
  subst h; ring

/-- **NODE H.87 (ii).** In characteristic `2` the same total reads `z·s² + z·s² = 2·(z·s²) = 0`. -/
theorem carry_cancel_char_two {R : Type*} [CommRing R] (hR : (2 : R) = 0) (z s : R) :
    z * s ^ 2 + z * s ^ 2 = 0 := by
  have : z * s ^ 2 + z * s ^ 2 = 2 * (z * s ^ 2) := by ring
  rw [this, hR, zero_mul]

/-- **NODE H.87 (iii).** The `A₁′` kill: `S₁ + 2·s = 0` given `S₁ = −(2·s)`, in every
characteristic (in characteristic `2` both summands are separately zero). -/
theorem refine_kill_A₁ {R : Type*} [CommRing R] {S₁ s : R} (h : S₁ = -(2 * s)) : S₁ + 2 * s = 0 := by
  subst h; ring

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.carry_cancel
#print axioms Uniformity.Density.Induction.carry_cancel_char_two
#print axioms Uniformity.Density.Induction.refine_kill_A₁

end AxCheck
