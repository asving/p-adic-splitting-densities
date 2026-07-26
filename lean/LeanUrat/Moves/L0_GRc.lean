/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs

/-!
# Moves/L0_GRc — residue evaluation of a monomial (D.6)

MOVES §B2-DEF D.6 (residue evaluation of a monomial; MOVES ~2147-2150). Generalizes round-1
`GRc` to the SUBFIELD coercion `φ = K.subtype` used by `Stage.digPrime`.
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.Moves

theorem L0_GRc {K F : Type*} [Field K] [Field F] (φ : K →+* F) (zbar : Fˣ) (a : K) (k : ℤ) : LaurentPolynomial.eval₂ φ zbar (LaurentPolynomial.C a * LaurentPolynomial.T k) = φ a * ((zbar ^ k : Fˣ) : F) := by
  exact LaurentPolynomial.eval₂_C_mul_T φ zbar a k

end LeanUrat.Moves
