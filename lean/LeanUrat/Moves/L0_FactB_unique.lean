/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs

/-!
# Moves/L0_FactB_unique — uniqueness of the Φ-adic development (§0 Fact B)

The Φ-adic development `f = ∑_{j<N} B_j Φ^j` with `deg B_j < deg Φ` and monic `Φ` is unique:
subtracting two developments gives `∑_j (B_j − B'_j) Φ^j = 0` with each coefficient of degree
`< deg Φ`, and one reads off level by level (reduce mod Φ ⟹ bottom coefficient vanishes, then the
monic factor is a non-zero-divisor, so recurse).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.Moves

open Polynomial

/-- If `∑_{j<M} C_j Φ^j = 0` with `Φ` monic and every `C_j` of degree `< deg Φ`, then every
`C_j` with `j < M` is zero. Read level by level: reduce mod `Φ` kills the bottom slot, then the
monic factor `Φ` is a non-zero-divisor so the shifted sum vanishes and we recurse. -/
private lemma dev_coeffs_zero {R : Type*} [CommRing R] [Nontrivial R] {Φ : Polynomial R}
    (hΦ : Φ.Monic) :
    ∀ (M : ℕ) (C : ℕ → Polynomial R), (∀ j, (C j).degree < Φ.degree) →
      ∑ j ∈ Finset.range M, C j * Φ ^ j = 0 → ∀ j, j < M → C j = 0 := by
  intro M
  induction M with
  | zero => intro C _ _ j hj; exact absurd hj (Nat.not_lt_zero j)
  | succ M ih =>
    intro C hdeg hsum
    rw [Finset.sum_range_succ', pow_zero, mul_one] at hsum
    have hshift : (∑ j ∈ Finset.range M, C (j + 1) * Φ ^ (j + 1))
        = (∑ j ∈ Finset.range M, C (j + 1) * Φ ^ j) * Φ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [pow_succ]; ring
    rw [hshift] at hsum
    set g := ∑ j ∈ Finset.range M, C (j + 1) * Φ ^ j with hg
    -- hsum : g * Φ + C 0 = 0
    have hC0 : C 0 = 0 := by
      have hmod : (g * Φ + C 0) %ₘ Φ = 0 := by rw [hsum]; exact zero_modByMonic Φ
      rw [add_modByMonic,
          (modByMonic_eq_zero_iff_dvd hΦ).mpr (dvd_mul_left Φ g),
          (modByMonic_eq_self_iff hΦ).mpr (hdeg 0), zero_add] at hmod
      exact hmod
    rw [hC0, add_zero] at hsum
    -- hsum : g * Φ = 0
    have hg0 : g = 0 := by
      have hlc : (g * Φ).leadingCoeff = g.leadingCoeff := leadingCoeff_mul_monic hΦ
      rw [hsum, leadingCoeff_zero] at hlc
      exact leadingCoeff_eq_zero.mp hlc.symm
    have hrec : ∀ j, j < M → C (j + 1) = 0 :=
      ih (fun j => C (j + 1)) (fun j => hdeg (j + 1)) (by rw [← hg]; exact hg0)
    intro j hj
    cases j with
    | zero => exact hC0
    | succ k => exact hrec k (by omega)

/-- **§0 Fact B**: the Φ-adic development is unique. -/
theorem L0_FactB_unique {R : Type*} [CommRing R] (Φ : Polynomial R) (hΦ : Φ.Monic) (f : Polynomial R) {B B' : ℕ → Polynomial R} {N N' : ℕ} (h : IsDevelopment Φ f B N) (h' : IsDevelopment Φ f B' N') : ∀ j, B j = B' j := by
  obtain ⟨hBdeg, hBzero, hBsum⟩ := h
  obtain ⟨hB'deg, hB'zero, hB'sum⟩ := h'
  rcases subsingleton_or_nontrivial R with hs | hn
  · -- trivial ring: all polynomials are equal
    intro j; exact Polynomial.ext (fun n => Subsingleton.elim _ _)
  · -- nontrivial ring
    have hfB : ∑ j ∈ Finset.range (max N N'), B j * Φ ^ j = f := by
      rw [hBsum]; symm
      apply Finset.sum_subset (Finset.range_subset_range.mpr (le_max_left N N'))
      intro x _ hxN
      rw [Finset.mem_range] at hxN
      rw [hBzero x (not_lt.mp hxN), zero_mul]
    have hfB' : ∑ j ∈ Finset.range (max N N'), B' j * Φ ^ j = f := by
      rw [hB'sum]; symm
      apply Finset.sum_subset (Finset.range_subset_range.mpr (le_max_right N N'))
      intro x _ hxN
      rw [Finset.mem_range] at hxN
      rw [hB'zero x (not_lt.mp hxN), zero_mul]
    have hCsum : ∑ j ∈ Finset.range (max N N'), (B j - B' j) * Φ ^ j = 0 := by
      have hsplit : ∑ j ∈ Finset.range (max N N'), (B j - B' j) * Φ ^ j
          = (∑ j ∈ Finset.range (max N N'), B j * Φ ^ j)
            - (∑ j ∈ Finset.range (max N N'), B' j * Φ ^ j) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [hsplit, hfB, hfB', sub_self]
    have hCdeg : ∀ j, (B j - B' j).degree < Φ.degree :=
      fun j => lt_of_le_of_lt (degree_sub_le _ _) (max_lt (hBdeg j) (hB'deg j))
    have hkey := dev_coeffs_zero hΦ (max N N') (fun j => B j - B' j) hCdeg hCsum
    intro j
    by_cases hj : j < max N N'
    · exact sub_eq_zero.mp (hkey j hj)
    · rw [not_lt] at hj
      rw [hBzero j (by omega), hB'zero j (by omega)]

end LeanUrat.Moves
