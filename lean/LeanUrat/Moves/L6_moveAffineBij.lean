/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs

/-!
# Moves/L6_moveAffineBij — the development move is an affine unitriangular bijection (injectivity)

Unit `L6.moveAffineBij` (MOVES §0 Fact A/B, ~29-46). Equal Φ-adic development coefficients force
equal polynomials: the "move" (Φ-adic development) is injective, over any `CommRing` (so it descends
to the mod-`p^N` boxes `(ZMod (p^N))[X]`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

open Polynomial LeanUrat.Moves

namespace LeanUrat.Moves

theorem L6_moveAffineBij {R : Type*} [CommRing R] (Φ : Polynomial R) (hmon : Φ.Monic) (hd : 1 ≤ Φ.natDegree) (f g : Polynomial R) (Bf Bg : ℕ → Polynomial R) (Nf Ng : ℕ) (hf : IsDevelopment Φ f Bf Nf) (hg : IsDevelopment Φ g Bg Ng) (heq : ∀ j, Bf j = Bg j) : f = g := by
  obtain ⟨_, hfz, hfsum⟩ := hf
  obtain ⟨_, hgz, hgsum⟩ := hg
  rw [hfsum, hgsum]
  -- Extend both sums to the common range `max Nf Ng`; the extra terms vanish (B j = 0 past N).
  have hsubf : Finset.range Nf ⊆ Finset.range (max Nf Ng) := by
    intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
  have hsubg : Finset.range Ng ⊆ Finset.range (max Nf Ng) := by
    intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
  have hMf : ∑ j ∈ Finset.range Nf, Bf j * Φ ^ j
      = ∑ j ∈ Finset.range (max Nf Ng), Bf j * Φ ^ j := by
    apply Finset.sum_subset hsubf
    intro j _ hj
    simp only [Finset.mem_range, not_lt] at hj
    rw [hfz j hj, zero_mul]
  have hMg : ∑ j ∈ Finset.range Ng, Bg j * Φ ^ j
      = ∑ j ∈ Finset.range (max Nf Ng), Bg j * Φ ^ j := by
    apply Finset.sum_subset hsubg
    intro j _ hj
    simp only [Finset.mem_range, not_lt] at hj
    rw [hgz j hj, zero_mul]
  rw [hMf, hMg]
  exact Finset.sum_congr rfl (fun j _ => by rw [heq j])

end LeanUrat.Moves
