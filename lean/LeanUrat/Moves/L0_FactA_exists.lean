/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs

/-!
# Moves/L0 — Fact A: the Φ-adic development exists (MOVES §0, ~29-39)

For a monic key `Φ` of degree `≥ 1`, every `f` has a (finite) `Φ`-adic development
`f = Σ_{j<N} B_j·Φ^j` with `deg B_j < deg Φ`. Constructed by strong induction on
`f.natDegree`: peel `f = (f %ₘ Φ) + Φ·(f /ₘ Φ)`, recurse on the quotient `f /ₘ Φ`
(strictly smaller degree, or zero), and prepend the remainder as `B_0`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.Moves

open Polynomial

theorem L0_FactA_exists {R : Type*} [CommRing R] (Φ : Polynomial R) (hΦ : Φ.Monic)
    (hd : 1 ≤ Φ.natDegree) (f : Polynomial R) :
    ∃ (B : ℕ → Polynomial R) (N : ℕ), IsDevelopment Φ f B N := by
  have hRnt : Nontrivial R := by
    rcases subsingleton_or_nontrivial R with h | h
    · have hz : Φ = 0 := Subsingleton.elim _ _
      simp [hz] at hd
    · exact h
  have hΦ0 : Φ ≠ 0 := hΦ.ne_zero
  have hΦbot : (⊥ : WithBot ℕ) < Φ.degree :=
    bot_lt_iff_ne_bot.mpr (fun h => hΦ0 (Polynomial.degree_eq_bot.mp h))
  -- strong induction on natDegree, phrased as a bounded family
  suffices H : ∀ n (g : Polynomial R), g.natDegree < n → ∃ B N, IsDevelopment Φ g B N by
    exact H (f.natDegree + 1) f (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => exact fun g hg => absurd hg (Nat.not_lt_zero _)
  | succ n IH =>
    intro g hg
    have hdiv : g %ₘ Φ + Φ * (g /ₘ Φ) = g := Polynomial.modByMonic_add_div g Φ
    -- development of the quotient
    have hqdev : ∃ B N, IsDevelopment Φ (g /ₘ Φ) B N := by
      rcases eq_or_ne (g /ₘ Φ) 0 with hqz | hqz
      · refine ⟨fun _ => 0, 0, ?_, fun j _ => rfl, ?_⟩
        · intro j
          show (0 : Polynomial R).degree < Φ.degree
          rw [Polynomial.degree_zero]; exact hΦbot
        · rw [hqz]; simp
      · apply IH
        have hdvz : ¬ (g.degree < Φ.degree) :=
          fun hlt => hqz ((Polynomial.divByMonic_eq_zero_iff hΦ).mpr hlt)
        have hnd : Φ.natDegree ≤ g.natDegree :=
          Polynomial.natDegree_le_natDegree (not_lt.mp hdvz)
        have hqnd : (g /ₘ Φ).natDegree = g.natDegree - Φ.natDegree :=
          Polynomial.natDegree_divByMonic g hΦ
        omega
    obtain ⟨B', N', hB'deg, hB'zero, hB'sum⟩ := hqdev
    refine ⟨(fun j => match j with | 0 => g %ₘ Φ | k + 1 => B' k), N' + 1, ?_, ?_, ?_⟩
    · intro j
      cases j with
      | zero =>
        show (g %ₘ Φ).degree < Φ.degree
        exact Polynomial.degree_modByMonic_lt g hΦ
      | succ k =>
        show (B' k).degree < Φ.degree
        exact hB'deg k
    · intro j hj
      cases j with
      | zero => exact absurd hj (by omega)
      | succ k =>
        show B' k = 0
        exact hB'zero k (by omega)
    · symm
      rw [Finset.sum_range_succ']
      show (∑ k ∈ Finset.range N', B' k * Φ ^ (k + 1)) + (g %ₘ Φ) * Φ ^ 0 = g
      rw [pow_zero, mul_one]
      have e1 : (∑ k ∈ Finset.range N', B' k * Φ ^ (k + 1)) = (g /ₘ Φ) * Φ := by
        rw [hB'sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [e1]
      linear_combination hdiv

end LeanUrat.Moves
