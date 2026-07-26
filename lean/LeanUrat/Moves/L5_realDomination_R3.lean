/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT

/-!
# Moves/L5_realDomination_R3 — per-stage domination `h_r > e_r·f_r` as the INDUCTIVE STEP (D.9(c))

Given the parent domination `hfr : h > e·fr`, the child bound
`f' := e·fr + (e−1)·h` satisfies

  `e·fr + (e−1)·h  <  e·h  ≤  e·h·g  ≤  w(Φ̂)`,

the middle step by `g ≥ 1` and the last by the standard lift's weight
lower bound (proved inline: every term of `Φ̂ = Φ^{eg} + Σ_{k<g} t_k·Φ^{ek}`
has parent-`w` weight `e·h·g`, so the ultrametric gives `w(Φ̂) ≥ e·h·g`).
By (I-aug) every child read has slope `> w(Φ̂)`, so `h' > e'·w(Φ̂) ≥ e'·f'`.
(MOVES ~2392-2397.)
-/

open Polynomial LeanUrat.Moves

namespace LeanUrat.Moves

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 400000

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- `w 1 = 0` (from multiplicativity). -/
private lemma w_one_eq_zero (σ : Stage p F) : σ.w 1 = 0 := by
  have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
  simp only [mul_one] at h
  linarith

/-- `w(Φ^m) = m · w Φ = m · h`. -/
private lemma w_pow_Phi (σ : Stage p F) (m : ℕ) : σ.w (σ.Φ ^ m) = (m : ℤ) * σ.h := by
  have hΦ0 : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  induction m with
  | zero => simpa using w_one_eq_zero σ
  | succ n ih =>
    rw [pow_succ, σ.hwmul _ _ (pow_ne_zero n hΦ0) hΦ0, ih, σ.hwΦ]
    push_cast; ring

/-- Ultrametric over a finite sum: if every nonzero summand has weight `≥ M`, then the whole
sum is either zero or has weight `≥ M`. -/
private lemma w_sum_ge (σ : Stage p F) (M : ℤ) (f : ℕ → Polynomial ℤ_[p]) (s : Finset ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0 → M ≤ σ.w (f i)) :
    (∑ i ∈ s, f i) = 0 ∨ M ≤ σ.w (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => left; simp
  | @insert a t ha ih =>
    have hft : ∀ i ∈ t, f i ≠ 0 → M ≤ σ.w (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have iht := ih hft
    rw [Finset.sum_insert ha]
    by_cases hfa : f a = 0
    · rw [hfa, zero_add]; exact iht
    · have hMfa : M ≤ σ.w (f a) := hf a (Finset.mem_insert_self a t) hfa
      rcases eq_or_ne (∑ i ∈ t, f i) 0 with hst | hst
      · rw [hst, add_zero]; right; exact hMfa
      · have hMt : M ≤ σ.w (∑ i ∈ t, f i) := iht.resolve_left hst
        by_cases htot : f a + ∑ i ∈ t, f i = 0
        · left; exact htot
        · right
          calc M ≤ min (σ.w (f a)) (σ.w (∑ i ∈ t, f i)) := le_min hMfa hMt
            _ ≤ σ.w (f a + ∑ i ∈ t, f i) := σ.hwult _ _ hfa hst htot

/-- Standard-lift weight LOWER bound `e·h·g ≤ w(Φ̂)` (the inequality half of `L3.liftWeight`,
proved inline: all terms of the displayed lift have weight `e·h·g`). -/
private lemma liftWeight_ge (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (hΦne : Φhat ≠ 0) :
    (σ.e : ℤ) * σ.h * g ≤ σ.w Φhat := by
  obtain ⟨hψmon, hψdeg, tt, htt0, ttp, hΦhat⟩ := hlift
  set M := (σ.e : ℤ) * σ.h * (g : ℤ) with hM
  have hΦ0 : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  -- each non-key term has weight `= M`
  have hterm : ∀ k ∈ Finset.range g, tt k * σ.Φ ^ (σ.e * k) ≠ 0 →
      M ≤ σ.w (tt k * σ.Φ ^ (σ.e * k)) := by
    intro k hk hne
    have hkg : k < g := Finset.mem_range.mp hk
    have httk : tt k ≠ 0 := by intro h0; apply hne; rw [h0, zero_mul]
    have hcoeff : ψ.coeff k ≠ 0 := fun hc => httk (htt0 k hc)
    obtain ⟨_, hinC, hwp, _⟩ := ttp k hkg hcoeff
    have hpow0 : σ.Φ ^ (σ.e * k) ≠ 0 := pow_ne_zero _ hΦ0
    have hval : σ.w (tt k * σ.Φ ^ (σ.e * k)) = M := by
      rw [σ.hwmul _ _ httk hpow0, σ.hStretch (tt k) httk hinC, hwp, w_pow_Phi σ (σ.e * k), hM]
      push_cast; ring
    exact hval.ge
  -- the key term has weight `= M`
  have hlead : σ.w (σ.Φ ^ (σ.e * g)) = M := by
    rw [w_pow_Phi σ (σ.e * g), hM]; push_cast; ring
  have hlead0 : σ.Φ ^ (σ.e * g) ≠ 0 := pow_ne_zero _ hΦ0
  set S := ∑ k ∈ Finset.range g, tt k * σ.Φ ^ (σ.e * k) with hSdef
  have hsum := w_sum_ge σ M (fun k => tt k * σ.Φ ^ (σ.e * k)) (Finset.range g) hterm
  rw [← hSdef] at hsum
  rw [hΦhat]
  rcases eq_or_ne S 0 with hS0 | hSne
  · rw [hS0, add_zero, hlead]
  · have hMS : M ≤ σ.w S := hsum.resolve_left hSne
    have htot_ne : σ.Φ ^ (σ.e * g) + S ≠ 0 := by rw [← hΦhat]; exact hΦne
    calc M ≤ min (σ.w (σ.Φ ^ (σ.e * g))) (σ.w S) := le_min hlead.ge hMS
      _ ≤ σ.w (σ.Φ ^ (σ.e * g) + S) := σ.hwult _ _ hlead0 hSne htot_ne

theorem L5_realDomination {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g e' h' : ℕ) (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (hg : 1 ≤ g) (he : 1 ≤ σ.e) (hΦne : Φhat ≠ 0) (hiaug : IAug σ Φhat e' h') (fr : ℤ) (hfr : (σ.h : ℤ) > (σ.e : ℤ) * fr) : (h' : ℤ) > (e' : ℤ) * ((σ.e : ℤ) * fr + ((σ.e : ℤ) - 1) * σ.h) := by
  have hlw : (σ.e : ℤ) * σ.h * g ≤ σ.w Φhat := liftWeight_ge σ ψ g Φhat hlift hΦne
  have hI : (h' : ℤ) > (e' : ℤ) * σ.w Φhat := hiaug
  have hg1 : (1 : ℤ) ≤ (g : ℤ) := by exact_mod_cast hg
  have he'nn : (0 : ℤ) ≤ (e' : ℤ) := by positivity
  have ehnn : (0 : ℤ) ≤ (σ.e : ℤ) * σ.h := by positivity
  -- `f' = e·fr + (e−1)·h  <  e·h`
  have expand : ((σ.e : ℤ) - 1) * (σ.h : ℤ) = (σ.e : ℤ) * (σ.h : ℤ) - (σ.h : ℤ) := by ring
  have h1 : (σ.e : ℤ) * fr + ((σ.e : ℤ) - 1) * σ.h < (σ.e : ℤ) * σ.h := by
    rw [expand]; linarith
  -- `e·h ≤ e·h·g`
  have h2 : (σ.e : ℤ) * σ.h ≤ (σ.e : ℤ) * σ.h * g :=
    le_mul_of_one_le_right ehnn hg1
  have hfprime : (σ.e : ℤ) * fr + ((σ.e : ℤ) - 1) * σ.h ≤ σ.w Φhat := by linarith
  have hmul : (e' : ℤ) * ((σ.e : ℤ) * fr + ((σ.e : ℤ) - 1) * σ.h) ≤ (e' : ℤ) * σ.w Φhat :=
    mul_le_mul_of_nonneg_left hfprime he'nn
  linarith

end LeanUrat.Moves
