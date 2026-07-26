/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs

/-!
# Moves/L3_liftWeight — EQUAL WEIGHTS: `w(Φ̂) = e·h·g` (§B2-DEF D.5, DEF-9)

`moves_ref`: D.5 EQUAL WEIGHTS; MOVES ~2121-2122.

The standard lift develops in `Φ` in its own displayed slots:
`Φ̂ = Φ^{eg} + Σ_{0≤k<g} t_k·Φ^{ek}`.  Each PRESENT slot `t_k·Φ^{ek}` has
`w(t_k) + ek·h = e·wPrev(t_k) + ek·h = eh(g−k) + ekh = ehg`
(using `hStretch` and the lift's `wPrev(t_k) = h(g−k)`), and the leading slot
`Φ^{eg}` has `w(1) + eg·h = ehg`.  All present slots are tied at `ehg`, so by
`Stage.hK1` (Lemma K1 at the current key `Φ`) the attained slot-minimum — which
is `w(Φ̂)` — equals `ehg`.

The proof provides the explicit `Φ`-adic development `B j = Σ_{k≤g} [j = e·k] c_k`
(`c_k = t_k` for `k<g`, `c_g = 1`), feeds it to `σ.hK1`, and reads the tie off the
existence witness of the slot-minimum.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanUrat.Moves

open Polynomial

theorem L3_liftWeight {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg1 : 1 ≤ g) (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (hΦne : Φhat ≠ 0) : σ.w Φhat = (σ.e : ℤ) * σ.h * g := by
  obtain ⟨hψmon, hψdeg, tt, htt0, httk, hΦhat⟩ := hlift
  -- The coefficient of the k-th displayed slot: t_k for k<g, 1 for k=g.
  set cc : ℕ → Polynomial ℤ_[p] := fun k => if k = g then 1 else tt k with hccdef
  -- The Φ-adic development of Φ̂: B j = Σ_{k≤g} [j = e·k]·c_k.
  set B : ℕ → Polynomial ℤ_[p] :=
    (fun j => ∑ k ∈ Finset.range (g + 1), if j = σ.e * k then cc k else 0) with hBdef
  -- Basic facts about cc.
  have hccg : cc g = 1 := by simp [hccdef]
  have hcck : ∀ k, k < g → cc k = tt k := by
    intro k hk; simp only [hccdef]; rw [if_neg (by omega : k ≠ g)]
  -- Degree facts about Φ.
  have hΦ0 : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hΦdegbot : (⊥ : WithBot ℕ) < σ.Φ.degree :=
    bot_lt_iff_ne_bot.mpr (fun h => hΦ0 (Polynomial.degree_eq_bot.mp h))
  have hΦdeg0 : (0 : WithBot ℕ) < σ.Φ.degree := by
    rw [Polynomial.degree_eq_natDegree hΦ0]
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one σ.hdeg
  -- Every displayed coefficient sits in the coefficient space C.
  have hccdeg : ∀ k, k ≤ g → (cc k).degree < σ.Φ.degree := by
    intro k hk
    by_cases hkg : k = g
    · rw [hkg, hccg, Polynomial.degree_one]; exact hΦdeg0
    · have hklt : k < g := lt_of_le_of_ne hk hkg
      rw [hcck k hklt]
      by_cases hcoef : ψ.coeff k = 0
      · rw [htt0 k hcoef, Polynomial.degree_zero]; exact hΦdegbot
      · obtain ⟨-, hinC, -, -⟩ := httk k hklt hcoef
        exact hinC
  -- w 1 = 0.
  have hw1 : σ.w 1 = 0 := by
    have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at h; omega
  -- The development sum equals Φ̂'s displayed form.
  have hsum : ∑ j ∈ Finset.range (σ.e * g + 1), B j * σ.Φ ^ j
      = (∑ k ∈ Finset.range g, tt k * σ.Φ ^ (σ.e * k)) + σ.Φ ^ (σ.e * g) := by
    have step1 : ∑ j ∈ Finset.range (σ.e * g + 1), B j * σ.Φ ^ j
        = ∑ k ∈ Finset.range (g + 1), cc k * σ.Φ ^ (σ.e * k) := by
      simp only [hBdef, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      have hmem : σ.e * k ∈ Finset.range (σ.e * g + 1) := by
        rw [Finset.mem_range]
        have : σ.e * k ≤ σ.e * g := Nat.mul_le_mul (le_refl σ.e) (by omega)
        omega
      simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq', if_pos hmem]
    rw [step1, Finset.sum_range_succ, hccg, one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [hcck k (Finset.mem_range.mp hk)]
  -- The development.
  have hDev : IsDevelopment σ.Φ Φhat B (σ.e * g + 1) := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      simp only [hBdef]
      refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
      rw [Finset.sup_lt_iff hΦdegbot]
      intro k hk
      rw [Finset.mem_range] at hk
      by_cases hjk : j = σ.e * k
      · rw [if_pos hjk]; exact hccdeg k (by omega)
      · rw [if_neg hjk, Polynomial.degree_zero]; exact hΦdegbot
    · intro j hj
      simp only [hBdef]
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_range] at hk
      apply if_neg
      intro hjk
      have hkg : σ.e * k ≤ σ.e * g := Nat.mul_le_mul (le_refl σ.e) (by omega)
      omega
    · rw [hΦhat, hsum]; ring
  -- Lemma K1 at the current key gives the attained slot-minimum.
  have hSMA := σ.hK1 Φhat B (σ.e * g + 1) hΦne hDev
  obtain ⟨-, j₀, hj₀N, hj₀nz, hj₀eq⟩ := hSMA
  have hj₀nz' : B j₀ ≠ 0 := hj₀nz
  have hsumnz : (∑ k ∈ Finset.range (g + 1), if j₀ = σ.e * k then cc k else 0) ≠ 0 := by
    simpa only [hBdef] using hj₀nz'
  obtain ⟨k₀, hk₀mem, hk₀ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumnz
  rw [Finset.mem_range] at hk₀mem
  have hcond : j₀ = σ.e * k₀ := by
    by_contra h
    rw [if_neg h] at hk₀ne
    exact hk₀ne rfl
  rw [if_pos hcond] at hk₀ne
  have hBval : B j₀ = cc k₀ := by
    simp only [hBdef]
    rw [Finset.sum_eq_single k₀]
    · rw [if_pos hcond]
    · intro k _ hkne
      exact if_neg (fun hh => hkne (Nat.eq_of_mul_eq_mul_left σ.he (hh.symm.trans hcond)))
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega : k₀ < g + 1)) h
  rw [hj₀eq]
  show σ.w (B j₀) + (↑j₀ : ℤ) * σ.w σ.Φ = (σ.e : ℤ) * σ.h * g
  rw [hBval, hcond, σ.hwΦ]
  by_cases hk₀g : k₀ = g
  · rw [hk₀g, hccg, hw1]
    push_cast; ring
  · have hk₀lt : k₀ < g := lt_of_le_of_ne (by omega) hk₀g
    have httne : tt k₀ ≠ 0 := by rw [hcck k₀ hk₀lt] at hk₀ne; exact hk₀ne
    have hcoefne : ψ.coeff k₀ ≠ 0 := fun hc => httne (htt0 k₀ hc)
    obtain ⟨-, hinC, hwprev, -⟩ := httk k₀ hk₀lt hcoefne
    rw [hcck k₀ hk₀lt, σ.hStretch (tt k₀) httne hinC, hwprev]
    push_cast; ring

end LeanUrat.Moves
