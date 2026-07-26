/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.L3_liftResidual

/-!
# Moves/L5_landVertexDigit — the VERTEX explicit digit (§B2-DEF D.8, pass-10 finding 2)

`R(f) = ψ^μ·q` with `ψ ∤ q` (the ψ-free part), and the pinned VERTEX digit carries its
EXPLICIT normalization unit `z̄^{−μm̂} = z̄^{μthg}` (m̂ = −thg):

  `dig'(B_μ) = z̄^{μthg}·(q mod ψ)`.

## Status of the three parts

* **Part 1** (`R f = ψ^μ·q`) — PROVEN: the z-anchored ψ-order read-off. From
  `HasAnchorK (R f) a Ranch` and `OrdPsiPoly ψ Ranch μ` we get `Ranch = ψ^μ·R'`, `ψ ∤ R'`,
  and `q := T a · toLaurent R'`.
* **Part 2** (`ψ ∤ q`) — PROVEN: the toLaurent-divisibility transfer of `L2_psiNotDvd`
  (cancel the unit `T a`, clear `X`-denominators via `exists_T_pow`, reflect to `↥K[X]` by
  `toLaurent_injective`; `ψ` prime and `ψ ∤ X` since `ψ ≠ X` monic irreducible).
* **Part 3** (the explicit-unit digit identity) — PROVEN **modulo the single private core**
  `vertexCongruence` below: the K1 minimizing-slot congruence
  `q ≡ z^{μm̂}·R(B_μ) (mod ψ)` in `↥K[z^{±1}]`, `m̂ = −thg`.  Given the congruence, the whole
  evaluation layer is machine-checked here: `eval₂` at the root `z̄` kills the `ψ`-multiple
  (`hzbar`), `eval₂(T μm̂) = z̄^{−μthg}` (mathlib `LaurentPolynomial.eval₂_T`), and the unit
  cancellation `z̄^{μthg}·z̄^{−μthg} = 1` produces exactly the pinned digit with its explicit
  normalization unit — pass-10 finding 2, NOT dropped.

## The honest gap (the private core)

`vertexCongruence` is the residual minimizing-slot content of the deps `L5.landVertex` +
`L3.K1` (D.8 VERTEX / D.5 K1): `R(f) = Σ_{minimizing j} T^{jm̂}·R(B_j)·ψ^j` with pairwise
distinct ψ-orders, `μ` = least minimizing slot, so dividing by `ψ^μ` leaves
`T^a·R' = T^{μm̂}·R(B_μ) + ψ·r`.  Both dep units are still open (`sorry`) and their `.olean`s
are unbuilt, so the core cannot be imported; it is stated here as a faithful PRIVATE lemma
with an honest `sorry`, pending `L3.K1`/`L5.landVertex` landing.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000

open Polynomial

namespace LeanUrat.Moves

/-- PRIVATE CORE (honest `sorry` — the K1 minimizing-slot residual content of the open deps
`L5.landVertex`/`L3.K1`, whose `.olean`s are not built): dividing the minimizing-slot
decomposition `R(f) = Σ_{minimizing j≥μ} T^{jm̂}·R(B_j)·(toLaurent ψ)^j` (`m̂ = −t·h·g`, cf.
`L3_liftResidual`) by `ψ^μ` leaves the congruence
`T^a·R' ≡ T^{μm̂}·R(B_μ) (mod toLaurent ψ)` in `↥K[z^{±1}]`. -/
private theorem vertexCongruence {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g) (hmon : ψ.Monic)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (Φhat : Polynomial ℤ_[p])
    (hlift : IsStandardLift σ ψ g Φhat) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (μ : ℕ) (a : ℤ)
    (Ranch : Polynomial ↥σ.K) (hanch : HasAnchorK (σ.R f) a Ranch) (hord : OrdPsiPoly ψ Ranch μ)
    (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) (hdev : IsDevelopment Φhat f B N)
    (R' : Polynomial ↥σ.K) (hR' : Ranch = ψ ^ μ * R') :
    ∃ r : LaurentPolynomial ↥σ.K,
      LaurentPolynomial.T a * Polynomial.toLaurent R' =
        LaurentPolynomial.T ((μ : ℤ) * (- σ.t * (σ.h : ℤ) * (g : ℤ))) * σ.R (B μ) +
          Polynomial.toLaurent ψ * r := by
  sorry

theorem L5_landVertexDigit {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g) (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (zbar : Fˣ) (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (μ : ℕ) (a : ℤ) (Ranch : Polynomial ↥σ.K) (hanch : HasAnchorK (σ.R f) a Ranch) (hord : OrdPsiPoly ψ Ranch μ) (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) (hdev : IsDevelopment Φhat f B N) : ∃ q : LaurentPolynomial ↥σ.K, σ.R f = (Polynomial.toLaurent ψ) ^ μ * q ∧ ¬ (Polynomial.toLaurent ψ ∣ q) ∧ σ.digPrime zbar (B μ) = ((zbar ^ ((μ : ℤ) * σ.t * (σ.h : ℤ) * (g : ℤ)) : Fˣ) : F) * LaurentPolynomial.eval₂ σ.K.subtype zbar q := by
  classical
  -- the z-anchored ψ-order factorization `Ranch = ψ^μ · R'`, `ψ ∤ R'`
  obtain ⟨R', hR'⟩ := hord.1
  have hR'notdvd : ¬ (ψ ∣ R') := by
    intro ⟨R'', hR''⟩
    exact hord.2 ⟨R'', by rw [hR', hR'', pow_succ]; ring⟩
  -- the witness: the ψ-free part `q = T a · toLaurent R'`
  refine ⟨LaurentPolynomial.T a * Polynomial.toLaurent R', ?_, ?_, ?_⟩
  · -- Part 1: `R f = ψ^μ · q`
    rw [hanch.2, hR', map_mul, map_pow]; ring
  · -- Part 2: `ψ ∤ q`  (toLaurent-divisibility transfer, cf. L2_psiNotDvd)
    intro hdvd
    -- divide out the unit `T a`: `toLaurent ψ ∣ toLaurent R'`
    have hdvdR : Polynomial.toLaurent ψ ∣ Polynomial.toLaurent R' := by
      have h := hdvd.mul_left (LaurentPolynomial.T (-a))
      rwa [← mul_assoc, ← LaurentPolynomial.T_add, neg_add_cancel,
        LaurentPolynomial.T_zero, one_mul] at h
    obtain ⟨qq, hq⟩ := hdvdR
    obtain ⟨n, f', hf'⟩ := LaurentPolynomial.exists_T_pow qq
    -- clear `X`-denominators, reflect divisibility back to `↥K[X]`
    have hkey : R' * Polynomial.X ^ n = ψ * f' := by
      apply Polynomial.toLaurent_injective
      rw [map_mul, map_mul, Polynomial.toLaurent_X_pow, hq, mul_assoc, ← hf']
    have hdiv : ψ ∣ R' * Polynomial.X ^ n := ⟨f', hkey⟩
    have hprime : Prime ψ := hψ.prime
    have hnotdvdX : ¬ (ψ ∣ Polynomial.X) := fun hdX =>
      hψz (Polynomial.eq_of_monic_of_associated hmon Polynomial.monic_X
        (hψ.associated_of_dvd Polynomial.irreducible_X hdX))
    rcases hprime.dvd_or_dvd hdiv with h1 | h2
    · exact hR'notdvd h1
    · exact hnotdvdX (hprime.dvd_of_dvd_pow h2)
  · -- Part 3: the explicit-unit VERTEX digit identity, from the private congruence core:
    -- evaluate `T^a·R' = T^{μm̂}·R(B_μ) + ψ·r` at the root `z̄` and cancel the unit.
    obtain ⟨r, hcong⟩ := vertexCongruence σ ψ g hg hmon hψ hψz Φhat hlift f hf μ a Ranch
      hanch hord B N hdev R' hR'
    -- the root kills the ψ-multiple
    have hψ0 : LaurentPolynomial.eval₂ σ.K.subtype zbar (Polynomial.toLaurent ψ) = 0 := by
      rw [LaurentPolynomial.eval₂_toLaurent]; exact hzbar
    -- evaluate the congruence: `eval(q) = z̄^{μm̂}·dig'(B_μ)`, `m̂ = −thg`
    have heval : LaurentPolynomial.eval₂ σ.K.subtype zbar
        (LaurentPolynomial.T a * Polynomial.toLaurent R') =
        ((zbar ^ ((μ : ℤ) * (- σ.t * (σ.h : ℤ) * (g : ℤ))) : Fˣ) : F) *
          σ.digPrime zbar (B μ) := by
      rw [hcong, map_add, map_mul, map_mul, hψ0, zero_mul, add_zero,
        LaurentPolynomial.eval₂_T, Stage.digPrime]
    -- the explicit normalization unit: `z̄^{μthg} · z̄^{−μthg} = 1`
    have hunit : zbar ^ ((μ : ℤ) * σ.t * (σ.h : ℤ) * (g : ℤ)) *
        zbar ^ ((μ : ℤ) * (- σ.t * (σ.h : ℤ) * (g : ℤ))) = 1 := by
      rw [← zpow_add,
        show (μ : ℤ) * σ.t * (σ.h : ℤ) * (g : ℤ) +
          (μ : ℤ) * (- σ.t * (σ.h : ℤ) * (g : ℤ)) = 0 by ring, zpow_zero]
    rw [heval, ← mul_assoc, ← Units.val_mul, hunit, Units.val_one, one_mul]

end LeanUrat.Moves
