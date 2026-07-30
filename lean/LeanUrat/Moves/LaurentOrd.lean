/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Moves/LaurentOrd — the (w,R)-free Laurent ψ-order toolkit (SYN-E1, C1 cluster)

The pure-Laurent lemmas of the residual-valuation engine, hoisted ONCE from the
file-private copies (SYN-E0 concordance table:
`lean/notes/SYN_E0_CONCORDANCE_2026-07-30.md`; plan: SYNTHESIS_PASS1 PART 2,
ratified 2026-07-30). Every lemma below is a **verbatim hoist** (statement and proof
unchanged, `private` dropped, source of truth per the concordance) EXCEPT the two
divisibility-transfer wrappers, which are one-line derivations of the third variant
(equivalence records in their docstrings).

Sources of truth (all copies statement-identical per SYN-E0):
* `dvd_of_dvd_mul_T`, `dvd_of_dvd_T_mul`, `psi_not_dvd_X_pow`,
  `toLaurent_pow_dvd_transfer`, `psi_order_of_sum`, `pow_order_unique` —
  `Moves/L5_landVertex.lean` (= `L5_landVertexDigit` = `HC1/V4_readLanding` tail,
  byte-identical).
* `OrdAt`, `ordAt_unique`, `ordAt_unit_mul`, `ordAt_add` — `Moves/L5_landBox.lean`.
* `GRf_priv` — `Moves/L3_K1.lean` (= `L5_landTwoSided_repair` = `HC1/V3_readLift`'s
  `v3_GRf`, statement-identical); name kept for zero-churn migration.
* `pow_dvd_of_toLaurent_pow_dvd` (`L5_landBox`), `poly_dvd_of_laurent_dvd`
  (`L5_landTwoSided_repair`) — derived from `toLaurent_pow_dvd_transfer`.

Consumers `open LeanUrat.Moves.LaurentOrd` (namespace-fenced against the
SharedRecenter/Mathlib name surface — the R2/MovesGr shadowing lesson).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanUrat.Moves.LaurentOrd

open Polynomial

/-! ## Divisibility through `T`-units -/

/-- Divisibility descends through a right `T`-unit factor. -/
lemma dvd_of_dvd_mul_T {K : Type*} [Field K] (x y : LaurentPolynomial K) (n : ℤ)
    (h : y ∣ x * LaurentPolynomial.T n) : y ∣ x := by
  have h2 := h.mul_right (LaurentPolynomial.T (-n))
  rwa [mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero,
    mul_one] at h2

/-- Divisibility descends through a left `T`-unit factor. -/
lemma dvd_of_dvd_T_mul {K : Type*} [Field K] (x y : LaurentPolynomial K) (n : ℤ)
    (h : y ∣ LaurentPolynomial.T n * x) : y ∣ x := by
  rw [mul_comm] at h
  exact dvd_of_dvd_mul_T x y n h

/-- `ψ ∤ X^n` for `ψ` monic irreducible `≠ X`. -/
lemma psi_not_dvd_X_pow {K : Type*} [Field K] (ψ : Polynomial K) (hmon : ψ.Monic)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (n : ℕ) : ¬ ψ ∣ Polynomial.X ^ n := by
  intro hdvd
  have hprime : Prime ψ := UniqueFactorizationMonoid.irreducible_iff_prime.mp hψ
  have hX : ψ ∣ Polynomial.X := hprime.dvd_of_dvd_pow hdvd
  exact hψz (Polynomial.eq_of_monic_of_associated hmon Polynomial.monic_X
    (hψ.associated_of_dvd Polynomial.irreducible_X hX))

/-- **`toLaurent` divisibility transfer**: `toLaurent ψ ^ k ∣ toLaurent P → ψ^k ∣ P` for `ψ`
monic irreducible `≠ X` (so `ψ` is prime and coprime to the inverted variable). -/
lemma toLaurent_pow_dvd_transfer {K : Type*} [Field K] (ψ : Polynomial K)
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

/-- `L5_landBox`'s transfer variant (implicit args, hypothesis order `hmon hψ hψz`).
EQUIVALENCE RECORD (SYN-E0): statement identical to `toLaurent_pow_dvd_transfer` up to
binder implicitness/order; the landBox proof body is retired for this derivation. -/
lemma pow_dvd_of_toLaurent_pow_dvd {K : Type*} [Field K] {ψ q : Polynomial K}
    (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) {m : ℕ}
    (h : Polynomial.toLaurent ψ ^ m ∣ Polynomial.toLaurent q) : ψ ^ m ∣ q :=
  toLaurent_pow_dvd_transfer ψ hmon hψ hψz m q h

/-- `L5_landTwoSided_repair`'s transfer variant (explicit args, hypothesis order
`hψ hψz hmon`). EQUIVALENCE RECORD (SYN-E0): statement identical to
`toLaurent_pow_dvd_transfer` up to binder order; the twoSided induction proof body is
retired for this derivation. -/
lemma poly_dvd_of_laurent_dvd {K : Type*} [Field K] (ψ : Polynomial K)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (hmon : ψ.Monic) (Q : Polynomial K) (k : ℕ)
    (hdvd : Polynomial.toLaurent ψ ^ k ∣ Polynomial.toLaurent Q) : ψ ^ k ∣ Q :=
  toLaurent_pow_dvd_transfer ψ hmon hψ hψz k Q hdvd

/-! ## ψ-adic order at a fixed exponent, over the Laurent ring -/

/-- `x` has `P`-order exactly `k`. -/
def OrdAt {K : Type*} [Field K] (P x : LaurentPolynomial K) (k : ℕ) : Prop :=
  P ^ k ∣ x ∧ ¬ P ^ (k + 1) ∣ x

lemma ordAt_unique {K : Type*} [Field K] {P x : LaurentPolynomial K} {k l : ℕ}
    (hk : OrdAt P x k) (hl : OrdAt P x l) : k = l := by
  by_contra hne
  rcases Nat.lt_or_ge k l with h | h
  · exact hk.2 ((pow_dvd_pow P (by omega)).trans hl.1)
  · exact hl.2 ((pow_dvd_pow P (by omega)).trans hk.1)

lemma ordAt_unit_mul {K : Type*} [Field K] {P x c : LaurentPolynomial K}
    (hc : c * c = 1) {k : ℕ} (h : OrdAt P x k) : OrdAt P (c * x) k := by
  refine ⟨h.1.mul_left c, fun hd => h.2 ?_⟩
  have h2 := hd.mul_left c
  rwa [← mul_assoc, hc, one_mul] at h2

lemma ordAt_add {K : Type*} [Field K] {P x y : LaurentPolynomial K} {k l : ℕ}
    (hx : OrdAt P x k) (hy : OrdAt P y l) (hkl : k < l) : OrdAt P (x + y) k := by
  have hyk : P ^ (k + 1) ∣ y := (pow_dvd_pow P (by omega)).trans hy.1
  refine ⟨dvd_add hx.1 ((pow_dvd_pow P hkl.le).trans hy.1), fun hd => hx.2 ?_⟩
  have h2 := dvd_sub hd hyk
  simpa using h2

/-- Two exact `Ψ`-order readings agree. -/
lemma pow_order_unique {α : Type*} [Monoid α] (Ψ x : α) (n k : ℕ)
    (hn1 : Ψ ^ n ∣ x) (hn2 : ¬ Ψ ^ (n + 1) ∣ x) (hk1 : Ψ ^ k ∣ x) (hk2 : ¬ Ψ ^ (k + 1) ∣ x) :
    n = k := by
  by_contra hne
  rcases Nat.lt_or_ge n k with h | h
  · exact hn2 (dvd_trans (pow_dvd_pow Ψ (by omega)) hk1)
  · exact hk2 (dvd_trans (pow_dvd_pow Ψ (by omega)) hn1)

/-! ## Distinct-ψ-order sums -/

/-- **[the GRf face]** In `K[z^{±1}]` with `ψ` irreducible, `ψ ≠ X`, a finite
sum `Σ_{j∈S} c_j·ψ^j` with each `c_j ≠ 0`, `ψ ∤ c_j` is nonzero. -/
theorem GRf_priv {K : Type*} [Field K] (ψ : Polynomial K) (hψ : Irreducible ψ)
    (hψz : ψ ≠ Polynomial.X) (c : ℕ → LaurentPolynomial K) (S : Finset ℕ) (hne : S.Nonempty)
    (hc : ∀ j ∈ S, c j ≠ 0 ∧ ¬ (Polynomial.toLaurent ψ ∣ c j)) :
    (∑ j ∈ S, c j * (Polynomial.toLaurent ψ) ^ j) ≠ 0 := by
  set P := Polynomial.toLaurent ψ with hP
  set m := S.min' hne with hm
  have hmmem : m ∈ S := S.min'_mem hne
  have hmle : ∀ j ∈ S, m ≤ j := fun j hj => S.min'_le j hj
  have hψ0 : ψ ≠ 0 := hψ.ne_zero
  have hP0 : P ≠ 0 := Polynomial.toLaurent_ne_zero.mpr hψ0
  have hfact : (∑ j ∈ S, c j * P ^ j) = P ^ m * (∑ j ∈ S, c j * P ^ (j - m)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hpow : P ^ j = P ^ m * P ^ (j - m) := by
      rw [← pow_add]; congr 1; have := hmle j hj; omega
    rw [hpow]; ring
  have hrest : P ∣ (∑ j ∈ S.erase m, c j * P ^ (j - m)) := by
    refine Finset.dvd_sum (fun j hj => ?_)
    rw [Finset.mem_erase] at hj
    obtain ⟨hjm, hjS⟩ := hj
    have hlt : m < j := lt_of_le_of_ne (hmle j hjS) (Ne.symm hjm)
    exact (dvd_pow_self P (by omega : j - m ≠ 0)).mul_left (c j)
  have hsplit : (∑ j ∈ S, c j * P ^ (j - m))
      = c m * P ^ (m - m) + (∑ j ∈ S.erase m, c j * P ^ (j - m)) :=
    (Finset.add_sum_erase S (fun j => c j * P ^ (j - m)) hmmem).symm
  have hcofdvd : ¬ P ∣ (∑ j ∈ S, c j * P ^ (j - m)) := by
    intro hdvd
    rw [hsplit] at hdvd
    have hdvd2 : P ∣ c m * P ^ (m - m) := (dvd_add_left hrest).mp hdvd
    rw [Nat.sub_self, pow_zero, mul_one] at hdvd2
    exact (hc m hmmem).2 hdvd2
  have hcof0 : (∑ j ∈ S, c j * P ^ (j - m)) ≠ 0 := fun h => hcofdvd (h ▸ dvd_zero P)
  rw [hfact]
  exact mul_ne_zero (pow_ne_zero m hP0) hcof0

/-- **GRf-style order reading**: a sum `Σ_{l∈T} d_l·Ψ^l` with each `d_l ≠ 0`, `Ψ ∤ d_l` has
`Ψ`-order exactly `min T`. -/
lemma psi_order_of_sum {K : Type*} [Field K] (Ψ : LaurentPolynomial K) (hΨ0 : Ψ ≠ 0)
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

end LeanUrat.Moves.LaurentOrd
