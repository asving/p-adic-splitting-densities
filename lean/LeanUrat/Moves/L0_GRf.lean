/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs

/-!
# Moves/L0_GRf — a finite sum of nonzero terms with distinct ψ-orders is ≠ 0 (D.5, K1 core)

MOVES §B2-DEF D.5 / Lemma K1 (MOVES ~2136-2142). In the Laurent ring `K[z^{±1}]` of the CURRENT
residue field `K`, with `ψ` irreducible over `K` (hence prime after inverting `z`, using `ψ ≠ X`),
a finite sum `Σ_{j∈S} c_j·ψ^j` with each `c_j ≠ 0` and `ψ ∤ c_j` is nonzero. Proof: factor out
`ψ^{min S}`; modulo `ψ` only the minimal-order term survives (`ψ ∤ c_{min}`), so the cofactor is
not divisible by `ψ`, hence nonzero; the ring is a domain.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.Moves

open Polynomial

theorem L0_GRf {K : Type*} [Field K] (ψ : Polynomial K) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (c : ℕ → LaurentPolynomial K) (S : Finset ℕ) (hne : S.Nonempty) (hc : ∀ j ∈ S, c j ≠ 0 ∧ ¬ (Polynomial.toLaurent ψ ∣ c j)) : (∑ j ∈ S, c j * (Polynomial.toLaurent ψ) ^ j) ≠ 0 := by
  set P := Polynomial.toLaurent ψ with hP
  set m := S.min' hne with hm
  have hmmem : m ∈ S := S.min'_mem hne
  have hmle : ∀ j ∈ S, m ≤ j := fun j hj => S.min'_le j hj
  have hψ0 : ψ ≠ 0 := hψ.ne_zero
  -- `P = toLaurent ψ ≠ 0` via injectivity of `toLaurent`.
  have hP0 : P ≠ 0 := by
    rw [hP]
    intro h
    exact hψ0 (Polynomial.toLaurent_injective (by rw [map_zero]; exact h))
  -- Factor out `P^m` (every `j ∈ S` has `j ≥ m`).
  have hfact : (∑ j ∈ S, c j * P ^ j) = P ^ m * (∑ j ∈ S, c j * P ^ (j - m)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hpow : P ^ j = P ^ m * P ^ (j - m) := by
      rw [← pow_add]; congr 1; have := hmle j hj; omega
    rw [hpow]; ring
  -- `P` divides every non-minimal term of the cofactor.
  have hrest : P ∣ (∑ j ∈ S.erase m, c j * P ^ (j - m)) := by
    refine Finset.dvd_sum (fun j hj => ?_)
    rw [Finset.mem_erase] at hj
    obtain ⟨hjm, hjS⟩ := hj
    have hlt : m < j := lt_of_le_of_ne (hmle j hjS) (Ne.symm hjm)
    exact (dvd_pow_self P (by omega : j - m ≠ 0)).mul_left (c j)
  -- Split the minimal term off the cofactor.
  have hsplit : (∑ j ∈ S, c j * P ^ (j - m))
      = c m * P ^ (m - m) + (∑ j ∈ S.erase m, c j * P ^ (j - m)) :=
    (Finset.add_sum_erase S (fun j => c j * P ^ (j - m)) hmmem).symm
  -- The cofactor is not divisible by `P`: else `P ∣ c m`, contradicting the hypothesis.
  have hcofdvd : ¬ P ∣ (∑ j ∈ S, c j * P ^ (j - m)) := by
    intro hdvd
    rw [hsplit] at hdvd
    have hdvd2 : P ∣ c m * P ^ (m - m) := (dvd_add_left hrest).mp hdvd
    rw [Nat.sub_self, pow_zero, mul_one] at hdvd2
    exact (hc m hmmem).2 hdvd2
  -- Hence the cofactor is nonzero.
  have hcof0 : (∑ j ∈ S, c j * P ^ (j - m)) ≠ 0 := fun h => hcofdvd (h ▸ dvd_zero P)
  -- And the whole sum is a product of nonzero factors in a domain.
  rw [hfact]
  exact mul_ne_zero (pow_ne_zero m hP0) hcof0

end LeanUrat.Moves
