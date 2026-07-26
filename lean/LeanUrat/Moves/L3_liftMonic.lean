/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs

/-!
# Moves/L3_liftMonic — D.5 MONICITY + degree of the standard lift

`L3.liftMonic`: from the displayed standard lift `Φ̂ = Φ^{eg} + Σ_{k<g} t_k·Φ^{ek}`
(DEF-9), the leading slot `Φ^{eg}` is monic of degree `eg·deg Φ`, and every present
slot `t_k·Φ^{ek}` has strictly smaller degree (`deg t_k < deg Φ`, and `ek+1 ≤ eg` for
`e ≥ 1`, `k < g`). Hence `Φ̂` is monic of degree `eg·deg Φ`. No ψ-irreducibility needed.
A THEOREM of the lift, not a clause (DEF-9 repair). MOVES ~2119-2122.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanUrat.Moves

open Polynomial

theorem L3_liftMonic {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (hg1 : 1 ≤ g) (Φhat : Polynomial ℤ_[p])
    (hlift : IsStandardLift σ ψ g Φhat) :
    Φhat.Monic ∧ Φhat.natDegree = σ.e * g * σ.Φ.natDegree := by
  obtain ⟨hψmon, hψdeg, tt, htt0, httne, hΦhat⟩ := hlift
  -- the leading slot is monic and nonzero
  have hpowg_mon : (σ.Φ ^ (σ.e * g)).Monic := σ.hmonic.pow _
  have hpowg_ne : σ.Φ ^ (σ.e * g) ≠ 0 := hpowg_mon.ne_zero
  have hbpos : (⊥ : WithBot ℕ) < (σ.Φ ^ (σ.e * g)).degree :=
    bot_lt_iff_ne_bot.mpr (fun h => hpowg_ne (Polynomial.degree_eq_bot.mp h))
  -- each present slot has strictly smaller degree than the leading slot
  have hterm : ∀ k ∈ Finset.range g,
      (tt k * σ.Φ ^ (σ.e * k)).degree < (σ.Φ ^ (σ.e * g)).degree := by
    intro k hk
    rw [Finset.mem_range] at hk
    by_cases htk : tt k = 0
    · rw [htk, zero_mul, Polynomial.degree_zero]; exact hbpos
    · have hcoeff : ψ.coeff k ≠ 0 := fun h => htk (htt0 k h)
      have hlt : (tt k).degree < σ.Φ.degree := (httne k hk hcoeff).2.1
      have hpowk_ne : σ.Φ ^ (σ.e * k) ≠ 0 := (σ.hmonic.pow _).ne_zero
      have hprod_ne : tt k * σ.Φ ^ (σ.e * k) ≠ 0 := mul_ne_zero htk hpowk_ne
      have hA : (tt k).natDegree < σ.Φ.natDegree := Polynomial.natDegree_lt_natDegree htk hlt
      have hmn : σ.e * k + 1 ≤ σ.e * g := by
        have h1 : σ.e * (k + 1) ≤ σ.e * g := mul_le_mul_left' (by omega) σ.e
        have he := σ.he
        have h2 : σ.e * (k + 1) = σ.e * k + σ.e := by ring
        omega
      rw [Polynomial.degree_eq_natDegree hprod_ne, Polynomial.degree_eq_natDegree hpowg_ne,
        Polynomial.natDegree_mul htk hpowk_ne, Polynomial.natDegree_pow,
        Polynomial.natDegree_pow, Nat.cast_lt]
      have h1 : (σ.e * k + 1) * σ.Φ.natDegree ≤ σ.e * g * σ.Φ.natDegree :=
        mul_le_mul_right' hmn _
      have h2 : (σ.e * k + 1) * σ.Φ.natDegree = σ.e * k * σ.Φ.natDegree + σ.Φ.natDegree := by
        ring
      omega
  -- the sum has strictly smaller degree than the leading slot
  have hSdeg : (∑ k ∈ Finset.range g, tt k * σ.Φ ^ (σ.e * k)).degree
      < (σ.Φ ^ (σ.e * g)).degree := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff hbpos]
    exact hterm
  refine ⟨?_, ?_⟩
  · rw [hΦhat]; exact hpowg_mon.add_of_left hSdeg
  · rw [hΦhat, Polynomial.natDegree_eq_of_degree_eq
        (Polynomial.degree_add_eq_left_of_degree_lt hSdeg), Polynomial.natDegree_pow]

end LeanUrat.Moves
