import Mathlib
import LeanUrat.Moves.Defs

namespace LeanUrat.Moves

open Polynomial

theorem L0_GRa {K : Type*} [Field K] {x y : LaurentPolynomial K} (hx : IsMonomialUnit x) (hy : IsMonomialUnit y) : IsMonomialUnit (x * y) := by
  obtain ⟨c₁, k₁, rfl⟩ := hx
  obtain ⟨c₂, k₂, rfl⟩ := hy
  refine ⟨c₁ * c₂, k₁ + k₂, ?_⟩
  rw [Units.val_mul, map_mul, LaurentPolynomial.T_add]
  ring

end LeanUrat.Moves
