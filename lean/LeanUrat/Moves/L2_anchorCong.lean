/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs

open Polynomial LeanUrat.Moves

namespace LeanUrat.Moves

/-- **D.3(a) Anchor congruence.** Two slots `j, j'` both minimizing `w(B_j) + j·w(Φ)` in a
`Φ`-development satisfy `e·(w_prev-difference) = (j'−j)·w(Φ)`; since `w Φ = h` and `gcd(e,h)=1`,
this forces `e ∣ (j'−j)`. -/
theorem L2_anchorCong {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) (hdev : IsDevelopment σ.Φ f B N) (j j' : ℕ) (hj : j < N) (hj' : j' < N) (hjnz : B j ≠ 0) (hj'nz : B j' ≠ 0) (hmin : σ.w (B j) + (j : ℤ) * σ.w σ.Φ = σ.w f) (hmin' : σ.w (B j') + (j' : ℤ) * σ.w σ.Φ = σ.w f) : (σ.e : ℤ) ∣ ((j' : ℤ) - j) := by
  -- The slot coefficients lie in `C_Φ` (deg < deg Φ), from the development.
  have hinCj : inC σ.Φ (B j) := hdev.1 j
  have hinCj' : inC σ.Φ (B j') := hdev.1 j'
  -- DEF-4 coefficient-weight stretch: `w B = e·w_prev B`.
  have hsj : σ.w (B j) = (σ.e : ℤ) * σ.wPrev (B j) := σ.hStretch (B j) hjnz hinCj
  have hsj' : σ.w (B j') = (σ.e : ℤ) * σ.wPrev (B j') := σ.hStretch (B j') hj'nz hinCj'
  -- Equate the two minimality equations and substitute `w Φ = h`, then the stretches.
  have hcomb : (σ.e : ℤ) * σ.wPrev (B j) + (j : ℤ) * (σ.h : ℤ)
      = (σ.e : ℤ) * σ.wPrev (B j') + (j' : ℤ) * (σ.h : ℤ) := by
    have : σ.w (B j) + (j : ℤ) * σ.w σ.Φ = σ.w (B j') + (j' : ℤ) * σ.w σ.Φ := by
      rw [hmin, hmin']
    rw [σ.hwΦ, hsj, hsj'] at this
    linarith [this]
  -- Hence `e·(w_prev-difference) = (j'−j)·h`.
  have hkey : (σ.e : ℤ) * (σ.wPrev (B j) - σ.wPrev (B j')) = ((j' : ℤ) - j) * (σ.h : ℤ) := by
    linear_combination hcomb
  -- So `e ∣ (j'−j)·h`, and coprimality of `e,h` yields `e ∣ (j'−j)`.
  have hdvd : (σ.e : ℤ) ∣ ((j' : ℤ) - j) * (σ.h : ℤ) := ⟨_, hkey.symm⟩
  have hcop : IsCoprime (σ.e : ℤ) (σ.h : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact σ.hcop
  exact hcop.dvd_of_dvd_mul_right hdvd

end LeanUrat.Moves
