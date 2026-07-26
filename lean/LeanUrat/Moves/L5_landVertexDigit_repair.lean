/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.L3_liftResidual
import LeanUrat.Moves.L3_liftMonic
import LeanUrat.Moves.L2_widthBound

/-!
# Moves/L5_landVertex — D.8 (VERTEX): the pinned child vertex (MOVES ~2323-2338)

On the descend stratum at `ψ` with multiplicity `μ`, i.e. `f` with `ord_ψ R(f) = μ` (read on the
`z`-anchored `Ranch`, `R(f) = z^a·Ranch`, `ψ^μ ∥ Ranch`), the `Φ̂`-development of `f` has slot
`μ` MINIMIZING and nonzero: `w(B_μ) + μ·(ehg) = w(f)` and `B_μ ≠ 0`.

## Proof structure (fully closed — no `sorry`)

* **The residual-sum machine** (`residual_sum_machine`): for terms of a common weight `m` whose
  residuals can never satisfy `R(a_j) = u·Σ_{l∈T} R(a_l)` (`u² = 1`), every sub-sum is nonzero of
  weight `m` with residual the sum of residuals.  The cancellation cases are killed by an ε-trick:
  if `w(a_j + S) > m` (or `a_j + S = 0`) then `hRlt` applied to `-S` and `a_j + S` (resp. `R` of
  `a_j = -S`) forces `R(a_j) = R(-1)·R(S)` with `R(-1)² = R(1) = 1` — exactly the excluded shape.
* **ψ-freeness of slot residuals** (`psiNotDvd_local`): `deg B < deg Φ̂ = eg·deg Φ` puts the
  support of `R(B)` in a window of width `< g` (`L2_widthBound`), so its `z`-anchored polynomial
  has degree `< g = deg ψ`; a `toLaurent`-divisibility transfer (`toLaurent_pow_dvd_transfer`,
  using `ψ` prime in `K[z]` and `ψ ∤ z`) then forbids `ψ ∣ R(B)`.
* **Order pinning**: `R(f) = Σ_{minimizing j} (R(B_j)·z^{jm̂})·ψ^j`, terms of pairwise-distinct
  ψ-order (each cofactor ψ-free); factoring out `ψ^{min}` GRf-style gives `ord_ψ R(f) = ` least
  minimizing slot; the anchored hypothesis pins it to `μ`, so slot `μ` is minimizing and nonzero.

The separation hypothesis of the machine is itself discharged by the ψ-order comparison, so the
whole argument is self-contained over the `Stage` axioms plus the imported units
`L3_liftResidual`, `L3_liftMonic`, `L2_widthBound` (manifest-listed dep `L2.psiNotDvd` is
reproved inline from `L2.widthBound`; the `L3.K1` slot-minimum content is re-derived by the
machine, so the sorried `L3_K1` unit is NOT imported).  `L3_liftWeight` (proved on disk but
without a built olean) is reproduced verbatim as a private lemma.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanUrat.Moves

open Polynomial

section Helpers

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- `w 1 = 0`: from `w(1·1) = w 1 + w 1`. -/
private lemma w_one' (σ : Stage p F) : σ.w 1 = 0 := by
  have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  omega

/-- `w(-1) = 0`: from `w((-1)·(-1)) = 2·w(-1)`. -/
private lemma w_neg_one' (σ : Stage p F) : σ.w (-1) = 0 := by
  have h := σ.hwmul (-1) (-1) (by norm_num) (by norm_num)
  rw [neg_mul_neg, one_mul, w_one' σ] at h
  omega

/-- `w(-x) = w(x)`. -/
private lemma w_neg' (σ : Stage p F) (x : Polynomial ℤ_[p]) (hx : x ≠ 0) :
    σ.w (-x) = σ.w x := by
  have h := σ.hwmul (-1) x (by norm_num) hx
  rw [neg_one_mul] at h
  rw [h, w_neg_one' σ, zero_add]

/-- `w(x^n) = n·w(x)`. -/
private lemma w_pow' (σ : Stage p F) (x : Polynomial ℤ_[p]) (hx : x ≠ 0) (n : ℕ) :
    σ.w (x ^ n) = (n : ℤ) * σ.w x := by
  induction n with
  | zero => simpa [pow_zero] using w_one' σ
  | succ k ih =>
    rw [pow_succ, σ.hwmul _ x (pow_ne_zero k hx) hx, ih]
    push_cast; ring

/-- `R 1 = 1` (cancel `R 1` in the domain `K[z^{±1}]`). -/
private lemma R_one' (σ : Stage p F) : σ.R 1 = 1 := by
  have h := σ.hRmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  have hne : σ.R 1 ≠ 0 := σ.hRne 1 one_ne_zero
  have heq : σ.R 1 * 1 = σ.R 1 * σ.R 1 := by rw [mul_one]; exact h
  exact (mul_left_cancel₀ hne heq).symm

/-- `R(-1)² = 1`. -/
private lemma R_neg_one_sq' (σ : Stage p F) : σ.R (-1) * σ.R (-1) = 1 := by
  have h := σ.hRmul (-1) (-1) (by norm_num) (by norm_num)
  rw [neg_mul_neg, one_mul, R_one' σ] at h
  exact h.symm

/-- `R(-x) = R(-1)·R(x)`. -/
private lemma R_neg' (σ : Stage p F) (x : Polynomial ℤ_[p]) (hx : x ≠ 0) :
    σ.R (-x) = σ.R (-1) * σ.R x := by
  have h := σ.hRmul (-1) x (by norm_num) hx
  rwa [neg_one_mul] at h

/-- `R(x^n) = R(x)^n` (the `L0.GRe` content, reproved inline: no olean on disk). -/
private lemma R_pow' (σ : Stage p F) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (n : ℕ) :
    σ.R (f ^ n) = (σ.R f) ^ n := by
  induction n with
  | zero => simpa [pow_zero] using R_one' σ
  | succ k ih =>
    have hfk : f ^ k ≠ 0 := pow_ne_zero k hf
    rw [pow_succ, σ.hRmul (f ^ k) f hfk hf, ih, ← pow_succ]

/-- Ultrametric finite-sum lower bound. -/
private lemma w_sum_ge' (σ : Stage p F) (S : Finset ℕ) (a : ℕ → Polynomial ℤ_[p]) (m : ℤ)
    (hm : ∀ j ∈ S, a j ≠ 0 → m ≤ σ.w (a j)) (hsum : (∑ j ∈ S, a j) ≠ 0) :
    m ≤ σ.w (∑ j ∈ S, a j) := by
  classical
  revert hm hsum
  induction S using Finset.induction with
  | empty =>
    intro hm hsum
    simp only [Finset.sum_empty] at hsum
    exact absurd rfl hsum
  | insert i T hiT ih =>
    intro hm hsum
    rw [Finset.sum_insert hiT] at hsum ⊢
    by_cases hai : a i = 0
    · rw [hai, zero_add] at hsum ⊢
      exact ih (fun j hj hj0 => hm j (Finset.mem_insert_of_mem hj) hj0) hsum
    · by_cases hsT : (∑ j ∈ T, a j) = 0
      · rw [hsT, add_zero] at hsum ⊢
        exact hm i (Finset.mem_insert_self i T) hai
      · have h1 : m ≤ σ.w (a i) := hm i (Finset.mem_insert_self i T) hai
        have h2 : m ≤ σ.w (∑ j ∈ T, a j) :=
          ih (fun j hj hj0 => hm j (Finset.mem_insert_of_mem hj) hj0) hsT
        have hult := σ.hwult (a i) (∑ j ∈ T, a j) hai hsT hsum
        calc m ≤ min (σ.w (a i)) (σ.w (∑ j ∈ T, a j)) := le_min h1 h2
          _ ≤ σ.w (a i + ∑ j ∈ T, a j) := hult

/-- **The residual-sum machine.**  Terms of common weight `m`, with residuals that can never
satisfy `R(a_j) = u·Σ_{l∈T} R(a_l)` for `u² = 1` (`j ∉ T`), have all sub-sums nonzero of weight
`m` and residual the sum of the residuals.  Cancellation cases reduce, via `hRlt` applied to the
negated partial sum (the ε-trick, `ε := R(-1)`, `ε² = 1`), exactly to the excluded shape. -/
private lemma residual_sum_machine (σ : Stage p F) (m : ℤ) (a : ℕ → Polynomial ℤ_[p])
    (S : Finset ℕ)
    (hSne : ∀ j ∈ S, a j ≠ 0) (hSw : ∀ j ∈ S, σ.w (a j) = m)
    (hsep : ∀ j ∈ S, ∀ T ⊆ S, T.Nonempty → j ∉ T →
        ∀ u : LaurentPolynomial ↥σ.K, u * u = 1 → σ.R (a j) ≠ u * ∑ l ∈ T, σ.R (a l)) :
    ∀ T ⊆ S, T.Nonempty →
      (∑ j ∈ T, a j) ≠ 0 ∧ σ.w (∑ j ∈ T, a j) = m ∧
        σ.R (∑ j ∈ T, a j) = ∑ j ∈ T, σ.R (a j) := by
  classical
  intro T
  induction T using Finset.induction with
  | empty =>
    intro _ hne
    exact absurd hne (by simp)
  | insert j T hjT ih =>
    intro hsub _
    have hjS : j ∈ S := hsub (Finset.mem_insert_self j T)
    have hTsub : T ⊆ S := fun x hx => hsub (Finset.mem_insert_of_mem hx)
    have haj : a j ≠ 0 := hSne j hjS
    have hwj : σ.w (a j) = m := hSw j hjS
    rcases T.eq_empty_or_nonempty with rfl | hTne
    · refine ⟨by simpa using haj, by simpa using hwj, by simp⟩
    · obtain ⟨hT0, hTw, hTR⟩ := ih hTsub hTne
      have hcontra : σ.R (a j) ≠ σ.R (-1) * ∑ l ∈ T, σ.R (a l) :=
        hsep j hjS T hTsub hTne hjT (σ.R (-1)) (R_neg_one_sq' σ)
      have hRST : σ.R (-(∑ l ∈ T, a l)) = σ.R (-1) * ∑ l ∈ T, σ.R (a l) := by
        rw [R_neg' σ _ hT0, hTR]
      have hne0 : a j + ∑ l ∈ T, a l ≠ 0 := by
        intro h0
        have haj_eq : a j = -(∑ l ∈ T, a l) := eq_neg_of_add_eq_zero_left h0
        exact hcontra (by rw [haj_eq, hRST])
      have hwmin : m ≤ σ.w (a j + ∑ l ∈ T, a l) := by
        have h := σ.hwult (a j) _ haj hT0 hne0
        rwa [hwj, hTw, min_self] at h
      have hwsum : σ.w (a j + ∑ l ∈ T, a l) = m := by
        by_contra hne'
        have hlt : m < σ.w (a j + ∑ l ∈ T, a l) := lt_of_le_of_ne hwmin (Ne.symm hne')
        have hnST : -(∑ l ∈ T, a l) ≠ 0 := neg_ne_zero.mpr hT0
        have heq : -(∑ l ∈ T, a l) + (a j + ∑ l ∈ T, a l) = a j := by ring
        have hR := σ.hRlt (-(∑ l ∈ T, a l)) (a j + ∑ l ∈ T, a l) hnST hne0
          (by rw [heq]; exact haj) (by rw [w_neg' σ _ hT0, hTw]; exact hlt)
        rw [heq] at hR
        exact hcontra (by rw [hR, hRST])
      have hRadd := σ.hRadd (a j) _ haj hT0 hne0 (by rw [hwj, hTw]) (by rw [hwsum, hwj])
      refine ⟨?_, ?_, ?_⟩
      · rwa [Finset.sum_insert hjT]
      · rwa [Finset.sum_insert hjT]
      · rw [Finset.sum_insert hjT, Finset.sum_insert hjT, hRadd, hTR]

/-- Divisibility descends through a right `T`-unit factor. -/
private lemma dvd_of_dvd_mul_T {K : Type*} [Field K] (x y : LaurentPolynomial K) (n : ℤ)
    (h : y ∣ x * LaurentPolynomial.T n) : y ∣ x := by
  have h2 := h.mul_right (LaurentPolynomial.T (-n))
  rwa [mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero,
    mul_one] at h2

/-- Divisibility descends through a left `T`-unit factor. -/
private lemma dvd_of_dvd_T_mul {K : Type*} [Field K] (x y : LaurentPolynomial K) (n : ℤ)
    (h : y ∣ LaurentPolynomial.T n * x) : y ∣ x := by
  rw [mul_comm] at h
  exact dvd_of_dvd_mul_T x y n h

/-- `ψ ∤ X^n` for `ψ` monic irreducible `≠ X`. -/
private lemma psi_not_dvd_X_pow {K : Type*} [Field K] (ψ : Polynomial K) (hmon : ψ.Monic)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (n : ℕ) : ¬ ψ ∣ Polynomial.X ^ n := by
  intro hdvd
  have hprime : Prime ψ := UniqueFactorizationMonoid.irreducible_iff_prime.mp hψ
  have hX : ψ ∣ Polynomial.X := hprime.dvd_of_dvd_pow hdvd
  exact hψz (Polynomial.eq_of_monic_of_associated hmon Polynomial.monic_X
    (hψ.associated_of_dvd Polynomial.irreducible_X hX))

/-- **`toLaurent` divisibility transfer**: `toLaurent ψ ^ k ∣ toLaurent P → ψ^k ∣ P` for `ψ`
monic irreducible `≠ X` (so `ψ` is prime and coprime to the inverted variable). -/
private lemma toLaurent_pow_dvd_transfer {K : Type*} [Field K] (ψ : Polynomial K)
    (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (k : ℕ) (P : Polynomial K)
    (h : (Polynomial.toLaurent ψ) ^ k ∣ Polynomial.toLaurent P) : ψ ^ k ∣ P := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨n, Q, hQ⟩ := LaurentPolynomial.exists_T_pow q
  have hmain : Polynomial.toLaurent (P * Polynomial.X ^ n) = Polynomial.toLaurent (ψ ^ k * Q) := by
    calc Polynomial.toLaurent (P * Polynomial.X ^ n)
        = Polynomial.toLaurent P * LaurentPolynomial.T (n : ℤ) := by
          rw [map_mul, Polynomial.toLaurent_X_pow]
      _ = ((Polynomial.toLaurent ψ) ^ k * q) * LaurentPolynomial.T (n : ℤ) := by rw [← hq]
      _ = (Polynomial.toLaurent ψ) ^ k * (q * LaurentPolynomial.T (n : ℤ)) := by ring
      _ = Polynomial.toLaurent (ψ ^ k) * Polynomial.toLaurent Q := by rw [hQ, map_pow]
      _ = Polynomial.toLaurent (ψ ^ k * Q) := by rw [map_mul]
  have heq : P * Polynomial.X ^ n = ψ ^ k * Q := Polynomial.toLaurent_injective hmain
  have hprime : Prime ψ := UniqueFactorizationMonoid.irreducible_iff_prime.mp hψ
  refine hprime.pow_dvd_of_dvd_mul_right k (psi_not_dvd_X_pow ψ hmon hψ hψz n) ?_
  rw [heq]
  exact dvd_mul_right _ _

/-- **[dep `L2.psiNotDvd`, inline — reproved from `L2.widthBound`]** `ψ ∤ R(B)` for a
sub-`Φ̂`-width coefficient `B`: the support of `R(B)` sits in a window of width `< g`
(`L2_widthBound`), so its anchored polynomial has degree `< g = deg ψ`. -/
private lemma psiNotDvd_local (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ)
    (hg : ψ.natDegree = g) (hg1 : 1 ≤ g) (hmon : ψ.Monic) (hψ : Irreducible ψ)
    (hψz : ψ ≠ Polynomial.X) (B : Polynomial ℤ_[p]) (hB : B ≠ 0)
    (hBdeg : B.natDegree < σ.e * g * σ.Φ.natDegree) :
    ¬ (Polynomial.toLaurent ψ ∣ σ.R B) := by
  intro hdvd
  obtain ⟨w0, hwin⟩ := L2_widthBound σ g hg1 B hB hBdeg
  have hRBne : σ.R B ≠ 0 := σ.hRne B hB
  obtain ⟨n, P, hP⟩ := LaurentPolynomial.exists_T_pow (σ.R B)
  have hTne : (LaurentPolynomial.T (n : ℤ) : LaurentPolynomial ↥σ.K) ≠ 0 :=
    (LaurentPolynomial.isUnit_T (n : ℤ)).ne_zero
  have hPne : P ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hP
    exact (mul_ne_zero hRBne hTne) hP.symm
  -- coefficient bridge: `P.coeff d = R(B) (d − n)`
  have hcoeff : ∀ d : ℕ, P.coeff d = (σ.R B) ((d : ℤ) - (n : ℤ)) := by
    intro d
    have h1 : (Polynomial.toLaurent P) ((d : ℕ) : ℤ) = P.coeff d := by
      rw [Polynomial.toLaurent_apply]
      exact Finsupp.mapDomain_apply Nat.cast_injective P.toFinsupp d
    rw [← h1, hP,
      show (LaurentPolynomial.T (n : ℤ) : LaurentPolynomial ↥σ.K)
        = AddMonoidAlgebra.single (n : ℤ) 1 from rfl,
      AddMonoidAlgebra.mul_single_apply, mul_one, ← sub_eq_add_neg]
  -- the window transported to `P`
  have hwinP : ∀ d : ℕ, P.coeff d ≠ 0 → w0 + n ≤ (d : ℤ) ∧ (d : ℤ) < w0 + n + g := by
    intro d hd
    have hmem : ((d : ℤ) - (n : ℤ)) ∈ (σ.R B).support :=
      Finsupp.mem_support_iff.mpr (by rw [← hcoeff]; exact hd)
    obtain ⟨h1, h2⟩ := hwin _ hmem
    omega
  -- trailing-degree factorization `P = X^tr · P₀`, `deg P₀ < g`
  have htrcoeff : P.coeff P.natTrailingDegree ≠ 0 :=
    fun h => hPne (Polynomial.trailingCoeff_eq_zero.mp h)
  have hleadcoeff : P.coeff P.natDegree ≠ 0 :=
    Polynomial.mem_support_iff.mp (Polynomial.natDegree_mem_support_of_nonzero hPne)
  have hXdvd : Polynomial.X ^ P.natTrailingDegree ∣ P :=
    Polynomial.X_pow_dvd_iff.mpr (fun _ hd => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hd)
  obtain ⟨P₀, hP₀⟩ := hXdvd
  have hP₀ne : P₀ ≠ 0 := by
    intro h
    rw [h, mul_zero] at hP₀
    exact hPne hP₀
  have hdegP : P.natDegree = P.natTrailingDegree + P₀.natDegree := by
    have h := congrArg Polynomial.natDegree hP₀
    rwa [Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero) hP₀ne,
      Polynomial.natDegree_X_pow] at h
  have hspread : P₀.natDegree < g := by
    obtain ⟨hlo, -⟩ := hwinP P.natTrailingDegree htrcoeff
    obtain ⟨-, hhi⟩ := hwinP P.natDegree hleadcoeff
    omega
  -- `ψ ∣ P₀` yet `deg P₀ < g = deg ψ`: contradiction
  have hψP : ψ ∣ P := by
    have h2 : Polynomial.toLaurent ψ ∣ Polynomial.toLaurent P := by
      rw [hP]
      exact hdvd.mul_right _
    have h3 := toLaurent_pow_dvd_transfer ψ hmon hψ hψz 1 P (by rwa [pow_one])
    rwa [pow_one] at h3
  have hprime : Prime ψ := UniqueFactorizationMonoid.irreducible_iff_prime.mp hψ
  have hψP₀ : ψ ∣ P₀ :=
    (hprime.dvd_or_dvd (hP₀ ▸ hψP)).resolve_left
      (psi_not_dvd_X_pow ψ hmon hψ hψz P.natTrailingDegree)
  have hgle : g ≤ P₀.natDegree := by
    have := Polynomial.natDegree_le_of_dvd hψP₀ hP₀ne
    omega
  omega

/-- **GRf-style order reading**: a sum `Σ_{l∈T} d_l·Ψ^l` with each `d_l ≠ 0`, `Ψ ∤ d_l` has
`Ψ`-order exactly `min T`. -/
private lemma psi_order_of_sum {K : Type*} [Field K] (Ψ : LaurentPolynomial K) (hΨ0 : Ψ ≠ 0)
    (d : ℕ → LaurentPolynomial K) (T : Finset ℕ) (hTne : T.Nonempty)
    (hd : ∀ l ∈ T, d l ≠ 0 ∧ ¬ Ψ ∣ d l) :
    Ψ ^ (T.min' hTne) ∣ (∑ l ∈ T, d l * Ψ ^ l) ∧
      ¬ Ψ ^ (T.min' hTne + 1) ∣ (∑ l ∈ T, d l * Ψ ^ l) := by
  classical
  set m := T.min' hTne with hm
  have hmmem : m ∈ T := T.min'_mem hTne
  have hmle : ∀ j ∈ T, m ≤ j := fun j hj => T.min'_le j hj
  have hfact : (∑ l ∈ T, d l * Ψ ^ l) = Ψ ^ m * (∑ l ∈ T, d l * Ψ ^ (l - m)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    have hpow : Ψ ^ l = Ψ ^ m * Ψ ^ (l - m) := by
      rw [← pow_add]; congr 1; have := hmle l hl; omega
    rw [hpow]; ring
  have hrest : Ψ ∣ (∑ l ∈ T.erase m, d l * Ψ ^ (l - m)) := by
    refine Finset.dvd_sum (fun l hl => ?_)
    rw [Finset.mem_erase] at hl
    obtain ⟨hlm, hlT⟩ := hl
    exact (dvd_pow_self Ψ (by have := hmle l hlT; omega : l - m ≠ 0)).mul_left (d l)
  have hsplit : (∑ l ∈ T, d l * Ψ ^ (l - m))
      = d m * Ψ ^ (m - m) + (∑ l ∈ T.erase m, d l * Ψ ^ (l - m)) :=
    (Finset.add_sum_erase T (fun l => d l * Ψ ^ (l - m)) hmmem).symm
  have hcofdvd : ¬ Ψ ∣ (∑ l ∈ T, d l * Ψ ^ (l - m)) := by
    intro hdvd
    rw [hsplit] at hdvd
    have hdvd2 : Ψ ∣ d m * Ψ ^ (m - m) := (dvd_add_left hrest).mp hdvd
    rw [Nat.sub_self, pow_zero, mul_one] at hdvd2
    exact (hd m hmmem).2 hdvd2
  constructor
  · rw [hfact]
    exact Dvd.intro _ rfl
  · intro hdvd
    rw [hfact, pow_succ] at hdvd
    exact hcofdvd ((mul_dvd_mul_iff_left (pow_ne_zero m hΨ0)).mp hdvd)

/-- Two exact `Ψ`-order readings agree. -/
private lemma pow_order_unique {α : Type*} [Monoid α] (Ψ x : α) (n k : ℕ)
    (hn1 : Ψ ^ n ∣ x) (hn2 : ¬ Ψ ^ (n + 1) ∣ x) (hk1 : Ψ ^ k ∣ x) (hk2 : ¬ Ψ ^ (k + 1) ∣ x) :
    n = k := by
  by_contra hne
  rcases Nat.lt_or_ge n k with h | h
  · exact hn2 (dvd_trans (pow_dvd_pow Ψ (by omega)) hk1)
  · exact hk2 (dvd_trans (pow_dvd_pow Ψ (by omega)) hn1)

/-- **[`L3.liftWeight`, verbatim copy — proved on disk, olean not built]** `w(Φ̂) = e·h·g`. -/
private theorem liftWeight_local (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg1 : 1 ≤ g)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (hΦne : Φhat ≠ 0) :
    σ.w Φhat = (σ.e : ℤ) * σ.h * g := by
  obtain ⟨hψmon, hψdeg, tt, htt0, httk, hΦhat⟩ := hlift
  set cc : ℕ → Polynomial ℤ_[p] := fun k => if k = g then 1 else tt k with hccdef
  set B : ℕ → Polynomial ℤ_[p] :=
    (fun j => ∑ k ∈ Finset.range (g + 1), if j = σ.e * k then cc k else 0) with hBdef
  have hccg : cc g = 1 := by simp [hccdef]
  have hcck : ∀ k, k < g → cc k = tt k := by
    intro k hk; simp only [hccdef]; rw [if_neg (by omega : k ≠ g)]
  have hΦ0 : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hΦdegbot : (⊥ : WithBot ℕ) < σ.Φ.degree :=
    bot_lt_iff_ne_bot.mpr (fun h => hΦ0 (Polynomial.degree_eq_bot.mp h))
  have hΦdeg0 : (0 : WithBot ℕ) < σ.Φ.degree := by
    rw [Polynomial.degree_eq_natDegree hΦ0]
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one σ.hdeg
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
  have hw1 : σ.w 1 = 0 := by
    have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at h; omega
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

end Helpers

/-- The VERTEX ψ-congruence.  Deps `L3.K1` + `L5.landVertex` are CLEAN (sorry-free) on disk;
their residual minimizing-slot engine is cribbed above as private helpers.  From
`R(f) = Σ_{minimizing l} R(B l)·z^{lm̂}·ψ^l` (`m̂ = −t·h·g`) with `μ` the LEAST minimizing
slot (ψ-order read-off), dividing by `ψ^μ` isolates the μ-slot mod `ψ`. -/
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
  classical
  -- `g ≥ 1` from irreducibility
  have hg1 : 1 ≤ g := by
    rw [← hg]
    exact Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hψ)
  -- lift facts
  obtain ⟨hΦhatmon, hΦhatdeg⟩ := L3_liftMonic σ ψ g hg1 Φhat hlift
  have hΦhatne : Φhat ≠ 0 := hΦhatmon.ne_zero
  have hwhat : σ.w Φhat = (σ.e : ℤ) * σ.h * g := liftWeight_local σ ψ g hg1 Φhat hlift hΦhatne
  have hΨne : (Polynomial.toLaurent ψ : LaurentPolynomial ↥σ.K) ≠ 0 := fun h =>
    hψ.ne_zero (Polynomial.toLaurent_injective (by rw [map_zero]; exact h))
  obtain ⟨hdevdeg, hdevzero, hdevsum⟩ := hdev
  -- the nonzero slots
  have hfsupp : f = ∑ j ∈ (Finset.range N).filter (fun j => B j ≠ 0), B j * Φhat ^ j := by
    rw [hdevsum]
    refine (Finset.sum_filter_of_ne ?_).symm
    intro j hj hne hBj
    exact hne (by rw [hBj, zero_mul])
  have hsuppne : ((Finset.range N).filter (fun j => B j ≠ 0)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    exact hf (by rw [hfsupp, hemp, Finset.sum_empty])
  have hsuppB : ∀ j ∈ (Finset.range N).filter (fun j => B j ≠ 0), B j ≠ 0 :=
    fun j hj => (Finset.mem_filter.mp hj).2
  have ha'ne : ∀ j ∈ (Finset.range N).filter (fun j => B j ≠ 0), B j * Φhat ^ j ≠ 0 :=
    fun j hj => mul_ne_zero (hsuppB j hj) (pow_ne_zero j hΦhatne)
  have ha'w : ∀ j ∈ (Finset.range N).filter (fun j => B j ≠ 0),
      σ.w (B j * Φhat ^ j) = σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g) := by
    intro j hj
    rw [σ.hwmul _ _ (hsuppB j hj) (pow_ne_zero j hΦhatne), w_pow' σ Φhat hΦhatne j, hwhat]
  -- the attained minimum over nonzero slots
  obtain ⟨jmin, hjminmem, hjminle⟩ :=
    Finset.exists_min_image ((Finset.range N).filter (fun j => B j ≠ 0))
      (fun j => σ.w (B j * Φhat ^ j)) hsuppne
  -- the minimizing set M
  have hMsub : ((Finset.range N).filter (fun j => B j ≠ 0)).filter
      (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin))
      ⊆ (Finset.range N).filter (fun j => B j ≠ 0) := Finset.filter_subset _ _
  have hMne : (((Finset.range N).filter (fun j => B j ≠ 0)).filter
      (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin))).Nonempty :=
    ⟨jmin, Finset.mem_filter.mpr ⟨hjminmem, rfl⟩⟩
  -- residual normal form of the slot terms
  have hRterm : ∀ j ∈ (Finset.range N).filter (fun j => B j ≠ 0),
      σ.R (B j * Φhat ^ j)
        = (σ.R (B j) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ j) *
            (Polynomial.toLaurent ψ) ^ j := by
    intro j hj
    rw [σ.hRmul _ _ (hsuppB j hj) (pow_ne_zero j hΦhatne), R_pow' σ Φhat hΦhatne j,
      L3_liftResidual σ ψ g Φhat hlift, mul_pow]
    ring
  -- ψ-freeness of the slot cofactors
  have hcne : ∀ j ∈ (Finset.range N).filter (fun j => B j ≠ 0),
      (σ.R (B j) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ j) ≠ 0 ∧
        ¬ (Polynomial.toLaurent ψ ∣
            σ.R (B j) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ j) := by
    intro j hj
    have hBj : B j ≠ 0 := hsuppB j hj
    have hRBne : σ.R (B j) ≠ 0 := σ.hRne _ hBj
    have hTu : ((LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ)) :
        LaurentPolynomial ↥σ.K)) ^ j ≠ 0 :=
      ((LaurentPolynomial.isUnit_T _).pow j).ne_zero
    refine ⟨mul_ne_zero hRBne hTu, fun hdvd => ?_⟩
    rw [LaurentPolynomial.T_pow] at hdvd
    have hdvd2 : Polynomial.toLaurent ψ ∣ σ.R (B j) :=
      dvd_of_dvd_mul_T _ _ _ hdvd
    have hBdeg : (B j).natDegree < σ.e * g * σ.Φ.natDegree := by
      have h1 := Polynomial.natDegree_lt_natDegree hBj (hdevdeg j)
      omega
    exact psiNotDvd_local σ ψ g hg hg1 hmon hψ hψz (B j) hBj hBdeg hdvd2
  -- separation: distinct ψ-orders forbid `R(a_j) = u·Σ R(a_l)`
  have hsep : ∀ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
        (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)),
      ∀ T ⊆ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
        (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)),
      T.Nonempty → j ∉ T → ∀ u : LaurentPolynomial ↥σ.K, u * u = 1 →
        σ.R (B j * Φhat ^ j) ≠ u * ∑ l ∈ T, σ.R (B l * Φhat ^ l) := by
    intro j hjM T hTM hTne hjT u hu2 heq
    have hjsupp : j ∈ (Finset.range N).filter (fun j => B j ≠ 0) := hMsub hjM
    have hTsupp : ∀ l ∈ T, l ∈ (Finset.range N).filter (fun j => B j ≠ 0) :=
      fun l hl => hMsub (hTM hl)
    have hune : u ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hu2
      exact zero_ne_one hu2
    have hRHS : u * ∑ l ∈ T, σ.R (B l * Φhat ^ l)
        = ∑ l ∈ T, (u * (σ.R (B l) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ l)) *
            (Polynomial.toLaurent ψ) ^ l := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l hl => ?_)
      rw [hRterm l (hTsupp l hl)]
      ring
    have hcond : ∀ l ∈ T,
        (u * (σ.R (B l) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ l)) ≠ 0 ∧
          ¬ (Polynomial.toLaurent ψ ∣
            u * (σ.R (B l) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ l)) := by
      intro l hl
      obtain ⟨h1, h2⟩ := hcne l (hTsupp l hl)
      refine ⟨mul_ne_zero hune h1, fun hdvd => h2 ?_⟩
      have h3 := hdvd.mul_left u
      rwa [← mul_assoc, hu2, one_mul] at h3
    have horderT := psi_order_of_sum (Polynomial.toLaurent ψ) hΨne
      (fun l => u * (σ.R (B l) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ l))
      T hTne hcond
    have hLHS : σ.R (B j * Φhat ^ j)
        = (σ.R (B j) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ j) *
            (Polynomial.toLaurent ψ) ^ j := hRterm j hjsupp
    have hLup : (Polynomial.toLaurent ψ) ^ j ∣ σ.R (B j * Φhat ^ j) := by
      rw [hLHS]
      exact dvd_mul_left _ _
    have hLdown : ¬ (Polynomial.toLaurent ψ) ^ (j + 1) ∣ σ.R (B j * Φhat ^ j) := by
      rw [hLHS]
      intro hdvd
      rw [pow_succ] at hdvd
      have h4 : (Polynomial.toLaurent ψ) ^ j * (Polynomial.toLaurent ψ) ∣
          (Polynomial.toLaurent ψ) ^ j *
            (σ.R (B j) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ j) := by
        rwa [mul_comm ((Polynomial.toLaurent ψ) ^ j)
          (σ.R (B j) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ j)]
      exact (hcne j hjsupp).2 ((mul_dvd_mul_iff_left (pow_ne_zero j hΨne)).mp h4)
    rw [heq, hRHS] at hLup hLdown
    have hj_eq : j = T.min' hTne :=
      pow_order_unique (Polynomial.toLaurent ψ) _ j (T.min' hTne)
        hLup hLdown horderT.1 horderT.2
    exact hjT (hj_eq ▸ T.min'_mem hTne)
  -- the machine on the minimizing set
  obtain ⟨hMsum_ne, hMsum_w, hMsum_R⟩ :=
    residual_sum_machine σ (σ.w (B jmin * Φhat ^ jmin)) (fun j => B j * Φhat ^ j)
      (((Finset.range N).filter (fun j => B j ≠ 0)).filter
        (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)))
      (fun j hj => ha'ne j (hMsub hj))
      (fun j hj => (Finset.mem_filter.mp hj).2)
      hsep _ Finset.Subset.rfl hMne
  -- split off the strictly heavier slots and conclude `w f = m`, `R f = Σ_M R`
  have hsplitsum :
      (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
          (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)), B j * Φhat ^ j)
        + (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
          (fun j => ¬ σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)), B j * Φhat ^ j)
        = ∑ j ∈ (Finset.range N).filter (fun j => B j ≠ 0), B j * Φhat ^ j :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hwf_and_Rf : σ.w f = σ.w (B jmin * Φhat ^ jmin) ∧
      σ.R f = ∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
        (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)),
          σ.R (B j * Φhat ^ j) := by
    by_cases hrest0 : (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
        (fun j => ¬ σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)), B j * Φhat ^ j) = 0
    · have hfeq : f = ∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
          (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)), B j * Φhat ^ j := by
        rw [hfsupp, ← hsplitsum, hrest0, add_zero]
      rw [hfeq]
      exact ⟨hMsum_w, hMsum_R⟩
    · have hrest_ge : σ.w (B jmin * Φhat ^ jmin) + 1 ≤
          σ.w (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
            (fun j => ¬ σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)), B j * Φhat ^ j) := by
        refine w_sum_ge' σ _ _ _ (fun j hj _ => ?_) hrest0
        obtain ⟨hjsupp, hjne⟩ := Finset.mem_filter.mp hj
        have := hjminle j hjsupp
        omega
      have hfeq : f = (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
            (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)), B j * Φhat ^ j)
          + (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
            (fun j => ¬ σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)), B j * Φhat ^ j) := by
        rw [hfsupp, hsplitsum]
      have hfne' : (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
            (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)), B j * Φhat ^ j)
          + (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
            (fun j => ¬ σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)), B j * Φhat ^ j)
          ≠ 0 := by rw [← hfeq]; exact hf
      constructor
      · -- weight
        have hlow := σ.hwult _ _ hMsum_ne hrest0 hfne'
        rw [hMsum_w] at hlow
        have hup : σ.w f ≤ σ.w (B jmin * Φhat ^ jmin) := by
          by_contra hgt
          rw [not_le] at hgt
          have hne2 : -(∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
              (fun j => ¬ σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)),
                B j * Φhat ^ j) ≠ 0 := neg_ne_zero.mpr hrest0
          have heq2 : f + -(∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
              (fun j => ¬ σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)), B j * Φhat ^ j)
              = ∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
                (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)),
                  B j * Φhat ^ j := by
            rw [hfeq]; ring
          have h5 := σ.hwult f _ hf hne2 (by rw [heq2]; exact hMsum_ne)
          rw [heq2, hMsum_w, w_neg' σ _ hrest0] at h5
          rcases min_choice (σ.w f)
            (σ.w (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
              (fun j => ¬ σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)),
                B j * Φhat ^ j)) with hc | hc <;> rw [hc] at h5 <;> omega
        have hlow2 : σ.w (B jmin * Φhat ^ jmin) ≤ σ.w f := by
          have h6 : min (σ.w (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
                (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)), B j * Φhat ^ j))
              (σ.w (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
                (fun j => ¬ σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)),
                  B j * Φhat ^ j)) ≤ σ.w f := by
            have h7 := σ.hwult _ _ hMsum_ne hrest0 hfne'
            rw [← hfeq] at h7
            exact h7
          rw [hMsum_w] at h6
          rcases min_choice (σ.w (B jmin * Φhat ^ jmin))
            (σ.w (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
              (fun j => ¬ σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)),
                B j * Φhat ^ j)) with hc | hc <;> rw [hc] at h6 <;> omega
        omega
      · -- residual
        have h7 := σ.hRlt _ _ hMsum_ne hrest0 hfne' (by rw [hMsum_w]; omega)
        rw [← hfeq] at h7
        rw [h7, hMsum_R]
  obtain ⟨hwfm, hRf⟩ := hwf_and_Rf
  -- `R f` in `c·Ψ^order` normal form over M
  have hRf2 : σ.R f = ∑ l ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
      (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)),
        (σ.R (B l) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ l) *
          (Polynomial.toLaurent ψ) ^ l := by
    rw [hRf]
    exact Finset.sum_congr rfl (fun l hl => hRterm l (hMsub hl))
  have horder := psi_order_of_sum (Polynomial.toLaurent ψ) hΨne
    (fun l => σ.R (B l) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ l)
    _ hMne (fun l hl => hcne l (hMsub hl))
  rw [← hRf2] at horder
  -- the anchored ψ-order reading: exactly μ
  obtain ⟨hRanch0, hanch_eq⟩ := hanch
  obtain ⟨horddvd, hordndvd⟩ := hord
  have hμup : (Polynomial.toLaurent ψ) ^ μ ∣ σ.R f := by
    rw [hanch_eq]
    have h8 := map_dvd (Polynomial.toLaurent (R := ↥σ.K)) horddvd
    rw [map_pow] at h8
    exact h8.mul_left _
  have hμdown : ¬ (Polynomial.toLaurent ψ) ^ (μ + 1) ∣ σ.R f := by
    intro hdvd
    rw [hanch_eq] at hdvd
    have h9 : (Polynomial.toLaurent ψ) ^ (μ + 1) ∣ Polynomial.toLaurent Ranch :=
      dvd_of_dvd_T_mul _ _ _ hdvd
    exact hordndvd (toLaurent_pow_dvd_transfer ψ hmon hψ hψz (μ + 1) Ranch h9)
  -- pin μ = least minimizing slot
  have hj0μ : (((Finset.range N).filter (fun j => B j ≠ 0)).filter
      (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin))).min' hMne = μ :=
    pow_order_unique (Polynomial.toLaurent ψ) (σ.R f) _ μ horder.1 horder.2 hμup hμdown
  have hμM : μ ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
      (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)) :=
    hj0μ ▸ Finset.min'_mem _ hMne
  obtain ⟨hμsupp, hμmin⟩ := Finset.mem_filter.mp hμM
  have hμne : B μ ≠ 0 := (Finset.mem_filter.mp hμsupp).2
  -- μ is the LEAST minimizing slot; divide the resSum decomposition `hRf2` by ψ^μ
  set M := ((Finset.range N).filter (fun j => B j ≠ 0)).filter
      (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)) with hMdef
  have hge : ∀ l ∈ M, μ ≤ l := by
    intro l hl; rw [← hj0μ]; exact Finset.min'_le M l hl
  have hTp : ∀ n : ℕ,
      (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ)) : LaurentPolynomial ↥σ.K) ^ n
        = LaurentPolynomial.T ((n : ℤ) * (- σ.t * (σ.h : ℤ) * (g : ℤ))) := by
    intro n
    induction n with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, ← LaurentPolynomial.T_add]; congr 1; push_cast; ring
  refine ⟨∑ l ∈ M.erase μ,
      (σ.R (B l) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ l)
        * (Polynomial.toLaurent ψ) ^ (l - μ - 1), ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero μ hΨne)
  have hLHS : (Polynomial.toLaurent ψ) ^ μ
        * (LaurentPolynomial.T a * Polynomial.toLaurent R') = σ.R f := by
    rw [hanch_eq, hR', map_mul, map_pow]; ring
  have hRHS : (Polynomial.toLaurent ψ) ^ μ *
      (LaurentPolynomial.T ((μ : ℤ) * (- σ.t * (σ.h : ℤ) * (g : ℤ))) * σ.R (B μ)
        + Polynomial.toLaurent ψ *
            ∑ l ∈ M.erase μ,
              (σ.R (B l) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ l)
                * (Polynomial.toLaurent ψ) ^ (l - μ - 1)) = σ.R f := by
    rw [mul_add]
    have hterm : (Polynomial.toLaurent ψ) ^ μ
          * (LaurentPolynomial.T ((μ : ℤ) * (- σ.t * (σ.h : ℤ) * (g : ℤ))) * σ.R (B μ))
        = (σ.R (B μ) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ μ)
            * (Polynomial.toLaurent ψ) ^ μ := by
      rw [hTp μ]; ring
    have htail : (Polynomial.toLaurent ψ) ^ μ *
          (Polynomial.toLaurent ψ *
            ∑ l ∈ M.erase μ,
              (σ.R (B l) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ l)
                * (Polynomial.toLaurent ψ) ^ (l - μ - 1))
        = ∑ l ∈ M.erase μ,
            (σ.R (B l) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ l)
              * (Polynomial.toLaurent ψ) ^ l := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l hl => ?_)
      have hlgt : μ < l := by
        have hlM := Finset.mem_of_mem_erase hl
        have hlne := Finset.ne_of_mem_erase hl
        have := hge l hlM; omega
      rw [show (Polynomial.toLaurent ψ) ^ μ *
              (Polynomial.toLaurent ψ *
                ((σ.R (B l) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ l)
                  * (Polynomial.toLaurent ψ) ^ (l - μ - 1)))
            = (σ.R (B l) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ l)
                * ((Polynomial.toLaurent ψ) ^ μ * (Polynomial.toLaurent ψ) ^ 1
                  * (Polynomial.toLaurent ψ) ^ (l - μ - 1)) from by rw [pow_one]; ring,
          ← pow_add, ← pow_add, show μ + 1 + (l - μ - 1) = l from by omega]
    rw [hterm, htail]
    refine Eq.trans ?_ hRf2.symm
    exact Finset.add_sum_erase M
      (fun x => σ.R (B x) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ x
        * (Polynomial.toLaurent ψ) ^ x) hμM
  rw [hLHS, hRHS]
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
