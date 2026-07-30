/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.L3_K1
import LeanUrat.Moves.L3_digPrime_nonzero
import LeanUrat.Moves.L3_liftResidual
import LeanUrat.Moves.L3_liftMonic

/-!
# Moves/L3_DIV — Lemma DIV: dig' multiplicative + exact remainder weight (§B2-DEF D.6)

`moves_ref`: D.6 Lemma DIV; MOVES ~2152-2175.

For `B, B'' ∈ Ĉ∖0` with `B·B'' = Q·Φ̂ + R_dev` (monic division, `R_dev ∈ Ĉ`):
`R_dev ≠ 0`, `w(R_dev) = w(B) + w(B'')` exactly, and `dig'(R_dev) = dig'(B)·dig'(B'')`.

## Proof structure (the δ₂ = 1 argument, D.6(ii)/(iii))

* (★) `digPrime(B·B'') = digPrime(B)·digPrime(B'')`: `R` is multiplicative on nonzero inputs
  (`Stage.hRmul`) and `LaurentPolynomial.eval₂` is a ring hom.
* The RHS of (★) is `≠ 0` in the field `F` (`L3_digPrime_nonzero` on each factor).
* `digPrime` kills every multiple of `Φ̂`: `R(Q·Φ̂) = R(Q)·z^{m̂}·ψ(z)` (`L3_liftResidual`) and
  `ψ(z̄) = 0` (`hzbar`).  With (★) this forces `R_dev ≠ 0` (else `B·B'' = Q·Φ̂` has zero digit).
* K1 at `Φ̂` (`L3_K1`) on the 2-slot development `B·B'' = R_dev·Φ̂⁰ + Q·Φ̂¹` (slot degrees checked
  via `L3_liftMonic`: `deg Φ̂ = eg·deg Φ`) gives `w(B·B'') ≤ w(R_dev)`, killing the cancellation
  branch.  Trichotomy on `w(Q·Φ̂)` vs `w(R_dev)`:
  - `w(Q·Φ̂) < w(R_dev)`: `hRlt` gives `R(B·B'') = R(Q·Φ̂)`, so the digit of `B·B''` vanishes —
    contradiction with (★)≠0.  (This is `δ₂ = 0`, refuted.)
  - `w(Q·Φ̂) = w(R_dev)`: K1 + ultrametric pin `w(B·B'') = w(R_dev)`; `hRadd` splits the residual
    as a sum, whose `Q·Φ̂`-part evaluates to `0` at `z̄`.
  - `w(R_dev) < w(Q·Φ̂)`: `hRlt` gives `R(B·B'') = R(R_dev)` and the ultrametric + K1 pin the
    weight.
  In every surviving branch `w(R_dev) = w(B·B'') = w(B) + w(B'')` (`hwmul`) and
  `digPrime(R_dev) = digPrime(B·B'')`, which is the product by (★).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanUrat.Moves

open Polynomial

theorem L3_DIV {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (zbar : Fˣ) (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0) (B B'' : Polynomial ℤ_[p]) (hB : B ≠ 0) (hB'' : B'' ≠ 0) (hBd : B.natDegree < σ.e * g * σ.Φ.natDegree) (hB''d : B''.natDegree < σ.e * g * σ.Φ.natDegree) (Rdev Q : Polynomial ℤ_[p]) (hdiv : B * B'' = Q * Φhat + Rdev) (hRd : Rdev.natDegree < σ.e * g * σ.Φ.natDegree) : Rdev ≠ 0 ∧ σ.w Rdev = σ.w B + σ.w B'' ∧ σ.digPrime zbar Rdev = σ.digPrime zbar B * σ.digPrime zbar B'' := by
  -- basic positivity
  have hg1 : 1 ≤ g := by rw [← hg]; exact hψ.natDegree_pos
  have hD1 : 1 ≤ σ.e * g * σ.Φ.natDegree :=
    Nat.mul_pos (Nat.mul_pos σ.he hg1) σ.hdeg
  -- Φ̂ is monic of degree eg·deg Φ
  obtain ⟨hmonic, hΦhatdeg⟩ := L3_liftMonic σ ψ g hg1 Φhat hlift
  have hΦhatne : Φhat ≠ 0 := hmonic.ne_zero
  have hbot : (⊥ : WithBot ℕ) < Φhat.degree :=
    bot_lt_iff_ne_bot.mpr (fun h => hΦhatne (Polynomial.degree_eq_bot.mp h))
  have hBB : B * B'' ≠ 0 := mul_ne_zero hB hB''
  -- (★) digit multiplicativity: `digPrime(B·B'') = digPrime B · digPrime B''`.
  have hstar : σ.digPrime zbar (B * B'') = σ.digPrime zbar B * σ.digPrime zbar B'' := by
    simp only [Stage.digPrime]
    rw [σ.hRmul B B'' hB hB'', map_mul]
  -- the product digit is nonzero in the field F
  have hne : σ.digPrime zbar (B * B'') ≠ 0 := by
    rw [hstar]
    exact mul_ne_zero
      (L3_digPrime_nonzero σ ψ g hg hψ hψz zbar hzbar B hB hBd)
      (L3_digPrime_nonzero σ ψ g hg hψ hψz zbar hzbar B'' hB'' hB''d)
  -- the lift residual `R(Φ̂) = z^{−thg}·ψ(z)`
  have hRΦhat := L3_liftResidual σ ψ g Φhat hlift
  -- digPrime kills Φ̂-multiples (evaluation at z̄ kills ψ)
  have hdigQ : ∀ Q' : Polynomial ℤ_[p], Q' ≠ 0 → σ.digPrime zbar (Q' * Φhat) = 0 := by
    intro Q' hQ'
    simp only [Stage.digPrime]
    rw [σ.hRmul Q' Φhat hQ' hΦhatne, map_mul, hRΦhat, map_mul,
      LaurentPolynomial.eval₂_T, LaurentPolynomial.eval₂_toLaurent, hzbar, mul_zero, mul_zero]
  -- (i) R_dev ≠ 0
  have hRdev : Rdev ≠ 0 := by
    intro h0
    rw [h0, add_zero] at hdiv
    have hQ : Q ≠ 0 := by rintro rfl; rw [zero_mul] at hdiv; exact hBB hdiv
    exact hne (by rw [hdiv]; exact hdigQ Q hQ)
  -- degree of Q is sub-Φ̂
  have hQdeg : Q.degree < Φhat.degree := by
    by_cases hQ : Q = 0
    · rw [hQ, Polynomial.degree_zero]; exact hbot
    · have hQΦ : Q * Φhat = B * B'' - Rdev := by rw [hdiv]; ring
      have h1 : (Q * Φhat).natDegree = Q.natDegree + Φhat.natDegree :=
        Polynomial.natDegree_mul hQ hΦhatne
      have h2 : (B * B'').natDegree = B.natDegree + B''.natDegree :=
        Polynomial.natDegree_mul hB hB''
      have h4 : Q.natDegree + Φhat.natDegree ≤ max (B * B'').natDegree Rdev.natDegree := by
        rw [← h1, hQΦ]; exact Polynomial.natDegree_sub_le _ _
      have hlt : Q.natDegree < Φhat.natDegree := by
        rw [h2] at h4
        rw [hΦhatdeg] at h4 ⊢
        omega
      exact Polynomial.degree_lt_degree hlt
  -- the 2-slot Φ̂-development of B·B'': slot 0 = R_dev, slot 1 = Q
  have hdev : IsDevelopment Φhat (B * B'')
      (fun j => if j = 0 then Rdev else if j = 1 then Q else 0) 2 := by
    refine ⟨fun j => ?_, fun j hj => ?_, ?_⟩
    · rcases j with _ | _ | j
      · simpa using Polynomial.degree_lt_degree
          (show Rdev.natDegree < Φhat.natDegree by rw [hΦhatdeg]; exact hRd)
      · simpa using hQdeg
      · simpa using hbot
    · rcases j with _ | _ | j
      · omega
      · omega
      · simp
    · rw [hdiv, Finset.sum_range_succ, Finset.sum_range_one]
      simp only [pow_zero, pow_one, mul_one]
      norm_num
      ring
  -- K1 at Φ̂: the slot minimum is attained, hence w(B·B'') ≤ w(R_dev) (slot 0)
  have hK1 := L3_K1 σ ψ g hg hψ hψz hlift.1 Φhat hlift
  have hmin := hK1 (B * B'') _ 2 hBB hdev
  have hle : σ.w (B * B'') ≤ σ.w Rdev := by
    simpa using hmin.1 0 (by omega) (by simpa using hRdev)
  refine ⟨hRdev, ?_⟩
  by_cases hQ : Q = 0
  · -- trivial branch: B·B'' = R_dev
    have hEq : B * B'' = Rdev := by rw [hdiv, hQ, zero_mul, zero_add]
    constructor
    · rw [← hEq]; exact σ.hwmul B B'' hB hB''
    · rw [← hEq]; exact hstar
  · have hu : Q * Φhat ≠ 0 := mul_ne_zero hQ hΦhatne
    have hsum_ne : Q * Φhat + Rdev ≠ 0 := by rw [← hdiv]; exact hBB
    rcases lt_trichotomy (σ.w (Q * Φhat)) (σ.w Rdev) with hlt | heq | hgt
    · -- δ₂ = 0 branch, refuted: the digit of B·B'' would vanish
      exfalso
      apply hne
      have hR : σ.R (B * B'') = σ.R (Q * Φhat) := by
        rw [hdiv]; exact σ.hRlt _ _ hu hRdev hsum_ne hlt
      have : σ.digPrime zbar (B * B'') = σ.digPrime zbar (Q * Φhat) := by
        simp only [Stage.digPrime]; rw [hR]
      rw [this]; exact hdigQ Q hQ
    · -- equal weights: hRadd splits the residual; the Q·Φ̂ part dies at z̄
      have hwsum : σ.w (B * B'') = σ.w Rdev := by
        refine le_antisymm hle ?_
        have h := σ.hwult _ _ hu hRdev hsum_ne
        rw [heq, min_self] at h
        rw [hdiv]; exact h
      have hRsum : σ.R (B * B'') = σ.R (Q * Φhat) + σ.R Rdev := by
        rw [hdiv]
        refine σ.hRadd _ _ hu hRdev hsum_ne heq ?_
        rw [← hdiv, hwsum, heq]
      constructor
      · rw [← hwsum]; exact σ.hwmul B B'' hB hB''
      · rw [← hstar]
        have h0 := hdigQ Q hQ
        simp only [Stage.digPrime] at h0 ⊢
        rw [hRsum, map_add, h0, zero_add]
    · -- w(R_dev) < w(Q·Φ̂): R_dev carries the initial form
      have hwsum : σ.w (B * B'') = σ.w Rdev := by
        refine le_antisymm hle ?_
        have h := σ.hwult _ _ hu hRdev hsum_ne
        rw [min_eq_right (le_of_lt hgt)] at h
        rw [hdiv]; exact h
      have hRsum : σ.R (B * B'') = σ.R Rdev := by
        rw [hdiv, add_comm (Q * Φhat) Rdev]
        refine σ.hRlt _ _ hRdev hu ?_ hgt
        rw [add_comm Rdev (Q * Φhat)]; exact hsum_ne
      constructor
      · rw [← hwsum]; exact σ.hwmul B B'' hB hB''
      · rw [← hstar]
        simp only [Stage.digPrime]
        rw [hRsum]

end LeanUrat.Moves
