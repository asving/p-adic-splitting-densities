import Mathlib
import LeanUrat.Moves.Defs

namespace LeanUrat.Moves

open Polynomial

theorem L0_GRb {K : Type*} [Field K] (c d : Kˣ) (k l : ℤ) (hkl : k ≠ l) : LaurentPolynomial.C (c : K) * LaurentPolynomial.T k + LaurentPolynomial.C (d : K) * LaurentPolynomial.T l ≠ 0 := by
  intro h
  rw [← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T] at h
  have h' : (Finsupp.single k (↑c : K) + Finsupp.single l (↑d : K) : ℤ →₀ K) = 0 := h
  have hcoeff := DFunLike.congr_fun h' k
  rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply, Finsupp.zero_apply,
    if_pos rfl, if_neg hkl.symm, add_zero] at hcoeff
  exact c.ne_zero hcoeff

end LeanUrat.Moves
