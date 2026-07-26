/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.L3_liftMonic

/-!
# Moves/L5_recSpecies_R4 — D.10 species lemma (MANIFEST_CORE)

`L5.recSpecies`: recenterings (same-degree modifications `Φ' := Φ̂ − tt` with
`w'(tt) = w'(Φ̂)`, i.e. a slot-1 coincidence in the `w'`-value) exist exactly at
`e_read = e' = 1` sides.  MOVES §D.10 ~2410-2413.

The only two `w'`-computations used, both from the ∀-development `IsSlotMinWeight`:
* `w'(Φ̂) = h'` (the slot-1 value, via `Φ̂ = 1·Φ̂¹`);
* `w'(f) = e'·w(f)` for a coefficient `f ∈ C_Φ̂` (via `f = f·Φ̂⁰`).

Then `(∃ tt … w' tt = w' Φ̂) ↔ e' = 1`:
(→) `h' = e'·w(tt)` forces `e' ∣ h'`, so `e' = 1` by `gcd(e',h') = 1`;
(←) `e' = 1` + (I-aug) gives `w(Φ̂) < h'`, `hreal` realizes weight `h'`, done.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.Moves

open Polynomial

theorem L5_recSpecies {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (hcore : StageCore σ) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g) (hgpos : 1 ≤ g) (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (e' h' : ℕ) (he' : 1 ≤ e') (hh' : 1 ≤ h') (hcop : Nat.gcd e' h' = 1) (hiaug : IAug σ Φhat e' h') (w' : Polynomial ℤ_[p] → ℤ) (hw' : IsSlotMinWeight w' Φhat e' h' σ.w) (hreal : ∀ ν : ℤ, σ.w Φhat < ν → ∃ tt, tt ≠ 0 ∧ inC Φhat tt ∧ σ.w tt = ν) : (∃ tt : Polynomial ℤ_[p], inC Φhat tt ∧ tt ≠ 0 ∧ w' tt = w' Φhat) ↔ e' = 1 := by
  -- Φ̂ is monic of positive degree (from the standard-lift shape, L3).
  have hΦmon : Φhat.Monic := (L3_liftMonic σ ψ g hgpos Φhat hlift).1
  have hΦne : Φhat ≠ 0 := hΦmon.ne_zero
  have hnd : Φhat.natDegree = σ.e * g * σ.Φ.natDegree := (L3_liftMonic σ ψ g hgpos Φhat hlift).2
  have hndpos : 0 < Φhat.natDegree := by
    rw [hnd]; exact Nat.mul_pos (Nat.mul_pos σ.he hgpos) σ.hdeg
  have hΦdeg : (0 : WithBot ℕ) < Φhat.degree := Polynomial.natDegree_pos_iff_degree_pos.mp hndpos
  have hbot : (⊥ : WithBot ℕ) < Φhat.degree :=
    bot_lt_iff_ne_bot.mpr (by rw [Ne, Polynomial.degree_eq_bot]; exact hΦne)
  have hw1 : σ.w (1 : Polynomial ℤ_[p]) = 0 := by
    have h := σ.hwmul 1 1 one_ne_zero one_ne_zero; rw [mul_one] at h; omega
  -- Helper A: `w'` of a coefficient `f ∈ C_Φ̂` reads its slot-0 value `e'·w(f)`.
  have hwf : ∀ f, inC Φhat f → f ≠ 0 → w' f = (e' : ℤ) * σ.w f := by
    intro f hfC hfne
    have hfC' : f.degree < Φhat.degree := hfC
    have hdev : IsDevelopment Φhat f (fun j => if j = 0 then f else 0) 1 := by
      refine ⟨fun j => ?_, fun j hj => ?_, ?_⟩
      · by_cases hj : j = 0
        · subst hj; simpa using hfC'
        · simp only [if_neg hj, Polynomial.degree_zero]; exact hbot
      · simp only [if_neg (show j ≠ 0 by omega)]
      · simp
    have hmin := hw' f (fun j => if j = 0 then f else 0) 1 hfne hdev
    simp only [SlotMinAttained] at hmin
    obtain ⟨-, j, hj1, -, hjeq⟩ := hmin
    have hj0 : j = 0 := by omega
    subst hj0; simpa using hjeq
  -- Helper B: `w'(Φ̂) = h'` (the slot-1 value of `Φ̂ = 1·Φ̂¹`).
  have hwΦhat : w' Φhat = (h' : ℤ) := by
    have hdev : IsDevelopment Φhat Φhat (fun j => if j = 1 then 1 else 0) 2 := by
      refine ⟨fun j => ?_, fun j hj => ?_, ?_⟩
      · by_cases hj : j = 1
        · subst hj; simpa [Polynomial.degree_one] using hΦdeg
        · simp only [if_neg hj, Polynomial.degree_zero]; exact hbot
      · simp only [if_neg (show j ≠ 1 by omega)]
      · simp
    have hmin := hw' Φhat (fun j => if j = 1 then 1 else 0) 2 hΦne hdev
    simp only [SlotMinAttained] at hmin
    obtain ⟨-, j, hj2, hjne, hjeq⟩ := hmin
    have hj1 : j = 1 := by by_contra hj; simp [if_neg hj] at hjne
    subst hj1; simpa [hw1] using hjeq
  constructor
  · rintro ⟨tt, httC, httne, htteq⟩
    rw [hwf tt httC httne, hwΦhat] at htteq
    have hdvd : (e' : ℤ) ∣ (h' : ℤ) := ⟨σ.w tt, htteq.symm⟩
    have hdvdN : e' ∣ h' := Int.natCast_dvd_natCast.mp hdvd
    have hgcd : Nat.gcd e' h' = e' := Nat.gcd_eq_left hdvdN
    omega
  · intro he1
    have hIA : (h' : ℤ) > (e' : ℤ) * σ.w Φhat := hiaug
    rw [he1] at hIA
    have hlt : σ.w Φhat < (h' : ℤ) := by simpa using hIA
    obtain ⟨tt, httne, httC, htteq⟩ := hreal (h' : ℤ) hlt
    refine ⟨tt, httC, httne, ?_⟩
    rw [hwf tt httC httne, hwΦhat, he1]
    simp [htteq]

end LeanUrat.Moves
