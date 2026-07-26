/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Moves/L0_GRg — D.3(d) width bound

Support-in-window `[a, a+g)` for a nonzero Laurent polynomial ⟹ it is an anchored polynomial of
degree `< g`: `x = T a · toLaurent Ranch` with `Ranch.natDegree < g`. (MOVES ~2051-2055.)
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.Moves

theorem L0_GRg {K : Type*} [Field K] {x : LaurentPolynomial K} (hx : x ≠ 0) (a : ℤ) (g : ℕ) (hsupp : ∀ k ∈ x.support, a ≤ k ∧ k < a + g) : ∃ Ranch : Polynomial K, Ranch.natDegree < g ∧ x = LaurentPolynomial.T a * Polynomial.toLaurent Ranch := by
  have hg : 1 ≤ g := by
    obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.mpr hx
    obtain ⟨hle, hlt⟩ := hsupp k hk
    omega
  refine ⟨∑ i ∈ Finset.range g, Polynomial.C (x.coeff (a + (i : ℤ))) * Polynomial.X ^ i, ?_, ?_⟩
  · -- degree bound
    have h1 : (∑ i ∈ Finset.range g, Polynomial.C (x.coeff (a + (i : ℤ))) * Polynomial.X ^ i).natDegree ≤ g - 1 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [Polynomial.finsetSum_coeff]
      apply Finset.sum_eq_zero
      intro i hi
      have hig : i < g := Finset.mem_range.mp hi
      rw [Polynomial.coeff_C_mul_X_pow, if_neg (by omega)]
    omega
  · -- the anchored identity
    have key : LaurentPolynomial.T a *
          Polynomial.toLaurent (∑ i ∈ Finset.range g, Polynomial.C (x.coeff (a + (i : ℤ))) * Polynomial.X ^ i)
        = ∑ i ∈ Finset.range g,
            LaurentPolynomial.C (x.coeff (a + (i : ℤ))) * LaurentPolynomial.T (a + (i : ℤ)) := by
      rw [map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Polynomial.toLaurent_C_mul_X_pow, LaurentPolynomial.T_add]
      ring
    rw [key]
    -- represent `x` as a sum over its support, then reindex onto `range g`
    have hx_repr : x = ∑ k ∈ x.support, LaurentPolynomial.C (x.coeff k) * LaurentPolynomial.T k := by
      conv_lhs => rw [← Finsupp.sum_single x]
      rw [Finsupp.sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← LaurentPolynomial.single_eq_C_mul_T]
      rfl
    conv_lhs => rw [hx_repr]
    let e : ℕ ↪ ℤ := ⟨fun i => a + (i : ℤ), fun i j h => by simpa using h⟩
    have hsub : x.support ⊆ (Finset.range g).map e := by
      intro k hk
      obtain ⟨hle, hlt⟩ := hsupp k hk
      rw [Finset.mem_map]
      exact ⟨(k - a).toNat, Finset.mem_range.mpr (by omega),
        by simp only [e, Function.Embedding.coeFn_mk]; omega⟩
    have hzero : ∀ k ∈ (Finset.range g).map e, k ∉ x.support →
        LaurentPolynomial.C (x.coeff k) * LaurentPolynomial.T k = 0 := by
      intro k hkS hknot
      rw [Finsupp.notMem_support_iff] at hknot
      rw [show x.coeff k = 0 from hknot, map_zero, zero_mul]
    rw [Finset.sum_subset hsub hzero, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [e, Function.Embedding.coeFn_mk]

end LeanUrat.Moves
