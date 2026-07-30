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
import LeanUrat.Moves.L0_GRg

/-!
# Moves/L3_K1 — Lemma K1 at the lifted key `Φ̂` (D.5, MOVES ~2131-2142)

For every `Φ̂`-development `f = Σ_j B_j Φ̂^j` (with `B_j ∈ Ĉ`), the stage valuation `w(f)` equals
the attained slot minimum `min_j (w(B_j) + j·w(Φ̂))`, with `w(Φ̂) = e·h·g` (the `kw` of the
statement).

## Proof structure (per the MOVES §D.5 note)

* `≥` (ultrametric): `w_sum_ge` — a finite-sum ultrametric lower bound from `hwult`.
* `w(Φ̂) = ehg`: `w_Phat` (the L3.liftWeight argument, inlined — its `.olean` is not built): all
  present slots of the displayed `Φ`-development of `Φ̂` are tied at `ehg`, so `hK1` at `Φ` pins
  the weight.
* `=` (no cancellation below the minimum): `minsum_facts` — any nonempty subsum of minimizing
  slots is nonzero of weight exactly `m`, with additive residuals.  The engine is
  `key_no_cancel`: the slot residuals are `R(B_j)·z^{jm̂}·ψ(z)^j` (`L3_liftResidual` + `R_pow`),
  each of exact ψ-order `j` (`psiNotDvd`: ψ ∤ R(B_j), width < g), so no subsum relation
  `Σ_T R(a_j) = R(−1)·R(a_i)` can hold (`GRf_priv`, the distinct-ψ-order lemma).  Both the
  "subsum vanishes" and the "weight jumps" degenerations reduce to exactly that relation via
  `hRlt`/`hRmul` — note the argument needs only `R(−1)² = 1` (from `R(1) = 1`), never the sign
  of `R(−1)`.  The `f = f_min + f_rest` split then forces `w(f) = m` by the ultrametric
  strict-triangle equality (weights only).

## Inlined dependencies (their `.olean`s are not built, so importing would break `lake env lean`)

* `L0.GRe` → `R_pow` (verbatim from `L0_GRe.lean`).
* `L0.GRf` → `GRf_priv` (verbatim from `L0_GRf.lean`).
* `L2.psiNotDvd` → `psiNotDvd` (verbatim from `L2_psiNotDvd_R3.lean`, the audit-corrected R3
  statement with `hmon`; its inputs `L2.widthBound`/`L0.GRg` ARE imported — NOTE the earlier
  claim that `L2.widthBound` injects a `slotDecomp` `sorry` into this footprint was REFUTED by
  the 2026-07-26 census (§5, via `#print axioms`): `L2_widthBound` and `L2_slotDecomp_R4` are
  themselves sorry-free, so L3.K1 is proved CLEAN with no `sorry` in its import cone).
* `L3.liftWeight` → `w_Phat` (verbatim from `L3_liftWeight.lean`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.Moves

open Polynomial

section Helpers

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- `w 1 = 0`: from `w(1·1) = w 1 + w 1`. -/
private lemma w_one (σ : Stage p F) : σ.w 1 = 0 := by
  have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  omega

/-- `w(−f) = w f` (via `w(−1) = 0`). -/
private lemma w_neg (σ : Stage p F) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) : σ.w (-f) = σ.w f := by
  have hm1 : σ.w (-1 : Polynomial ℤ_[p]) = 0 := by
    have h := σ.hwmul (-1) (-1) (neg_ne_zero.mpr one_ne_zero) (neg_ne_zero.mpr one_ne_zero)
    rw [neg_mul_neg, one_mul, w_one σ] at h
    omega
  have h := σ.hwmul (-1) f (neg_ne_zero.mpr one_ne_zero) hf
  rw [neg_one_mul] at h
  rw [h, hm1, zero_add]

/-- `w(f^n) = n·w f`. -/
private lemma w_pow (σ : Stage p F) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (n : ℕ) :
    σ.w (f ^ n) = (n : ℤ) * σ.w f := by
  induction n with
  | zero => rw [pow_zero, w_one σ, Nat.cast_zero, zero_mul]
  | succ k ih =>
    rw [pow_succ, σ.hwmul _ _ (pow_ne_zero k hf) hf, ih]
    push_cast
    ring

/-- `R 1 = 1` (from `hRmul` + `hRne`, cancellation in the Laurent domain). -/
private lemma R_one (σ : Stage p F) : σ.R (1 : Polynomial ℤ_[p]) = 1 := by
  have h := σ.hRmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  exact (mul_eq_left₀ (σ.hRne 1 one_ne_zero)).mp h.symm

/-- `R(−1)² = 1`.  (Only THIS is needed downstream — never the sign of `R(−1)`.) -/
private lemma R_negone_sq (σ : Stage p F) : σ.R (-1 : Polynomial ℤ_[p]) * σ.R (-1) = 1 := by
  have h := σ.hRmul (-1) (-1) (neg_ne_zero.mpr one_ne_zero) (neg_ne_zero.mpr one_ne_zero)
  rw [neg_mul_neg, one_mul, R_one σ] at h
  exact h.symm

/-- `R(−f) = R(−1)·R(f)`. -/
private lemma R_neg (σ : Stage p F) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) :
    σ.R (-f) = σ.R (-1) * σ.R f := by
  have h := σ.hRmul (-1) f (neg_ne_zero.mpr one_ne_zero) hf
  rw [neg_one_mul] at h
  exact h

/-- **[dep `L0.GRe`, inlined verbatim]** `R(f^n) = R(f)^n`. -/
private lemma R_pow (σ : Stage p F) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (n : ℕ) :
    σ.R (f ^ n) = (σ.R f) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, R_one σ]
  | succ k ih =>
    have hfk : f ^ k ≠ 0 := pow_ne_zero k hf
    rw [pow_succ, σ.hRmul (f ^ k) f hfk hf, ih, ← pow_succ]

/-- **Ultrametric finite-sum lower bound** (the `≥` direction of K1): if `m` bounds `w` from below
on every nonzero summand, then `m ≤ w(Σ)`. -/
private lemma w_sum_ge (σ : Stage p F)
    (S : Finset ℕ) (a : ℕ → Polynomial ℤ_[p]) (m : ℤ)
    (hm : ∀ j ∈ S, a j ≠ 0 → m ≤ σ.w (a j)) (hsum : (∑ j ∈ S, a j) ≠ 0) :
    m ≤ σ.w (∑ j ∈ S, a j) := by
  revert hm hsum
  induction S using Finset.induction with
  | empty =>
    intro _ hsum
    exact absurd Finset.sum_empty hsum
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
        exact (le_min h1 h2).trans (σ.hwult (a i) (∑ j ∈ T, a j) hai hsT hsum)

end Helpers

/-- **[dep `L0.GRf`, inlined verbatim]** In `K[z^{±1}]` with `ψ` irreducible, `ψ ≠ X`, a finite
sum `Σ_{j∈S} c_j·ψ^j` with each `c_j ≠ 0`, `ψ ∤ c_j` is nonzero. -/
private theorem GRf_priv {K : Type*} [Field K] (ψ : Polynomial K) (hψ : Irreducible ψ)
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

section Core

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- **[dep `L2.psiNotDvd`, inlined verbatim from the audit-corrected R3 unit]**
ψ ∤ R(B) for a nonzero below-`Φ̂`-width coefficient `B`. -/
private theorem psiNotDvd (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g)
    (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (B : Polynomial ℤ_[p])
    (hB : B ≠ 0) (hBdeg : B.natDegree < σ.e * g * σ.Φ.natDegree) :
    ¬ (Polynomial.toLaurent ψ ∣ σ.R B) := by
  classical
  intro hdvd
  have hgpos : 0 < ψ.natDegree := hψ.natDegree_pos
  have hg1 : 1 ≤ g := by omega
  obtain ⟨a, ha⟩ := L2_widthBound σ g hg1 B hB hBdeg
  obtain ⟨Ranch, hRdeg, hRB⟩ := L0_GRg (σ.hRne B hB) a g ha
  have hRanch_ne : Ranch ≠ 0 := by
    intro h
    rw [h, map_zero, mul_zero] at hRB
    exact σ.hRne B hB hRB
  have hdvdR : Polynomial.toLaurent ψ ∣ Polynomial.toLaurent Ranch := by
    have h := hdvd.mul_left (LaurentPolynomial.T (-a))
    rwa [hRB, ← mul_assoc, ← LaurentPolynomial.T_add, neg_add_cancel,
      LaurentPolynomial.T_zero, one_mul] at h
  obtain ⟨q, hq⟩ := hdvdR
  obtain ⟨n, f', hf'⟩ := LaurentPolynomial.exists_T_pow q
  have hkey : Ranch * Polynomial.X ^ n = ψ * f' := by
    apply Polynomial.toLaurent_injective
    rw [map_mul, map_mul, Polynomial.toLaurent_X_pow, hq, mul_assoc, ← hf']
  have hdiv : ψ ∣ Ranch * Polynomial.X ^ n := ⟨f', hkey⟩
  have hprime : Prime ψ := hψ.prime
  have hnotdvdX : ¬ (ψ ∣ Polynomial.X) := by
    intro hdX
    exact hψz (Polynomial.eq_of_monic_of_associated hmon Polynomial.monic_X
      (hψ.associated_of_dvd Polynomial.irreducible_X hdX))
  rcases hprime.dvd_or_dvd hdiv with h1 | h2
  · have hle := Polynomial.natDegree_le_of_dvd h1 hRanch_ne
    omega
  · exact hnotdvdX (hprime.dvd_of_dvd_pow h2)

/-- **[dep `L3.liftWeight`, inlined verbatim]** `w(Φ̂) = e·h·g`: all present slots of the
displayed `Φ`-development of `Φ̂` are tied at `ehg`, so `hK1` at `Φ` pins the weight. -/
private lemma w_Phat (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg1 : 1 ≤ g)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (hΦne : Φhat ≠ 0) :
    σ.w Φhat = (σ.e : ℤ) * σ.h * g := by
  classical
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
  have hw1 : σ.w 1 = 0 := w_one σ
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
  have hsumnz : (∑ k ∈ Finset.range (g + 1), if j₀ = σ.e * k then cc k else 0) ≠ 0 := by
    simpa only [hBdef] using hj₀nz
  obtain ⟨k₀, hk₀mem, hk₀ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumnz
  rw [Finset.mem_range] at hk₀mem
  have hcond : j₀ = σ.e * k₀ := by
    by_contra h
    exact hk₀ne (if_neg h)
  rw [if_pos hcond] at hk₀ne
  have hBval : B j₀ = cc k₀ := by
    simp only [hBdef]
    rw [Finset.sum_eq_single k₀]
    · rw [if_pos hcond]
    · intro k _ hkne
      exact if_neg (fun hh => hkne (Nat.eq_of_mul_eq_mul_left σ.he (hh.symm.trans hcond)))
    · exact fun h => absurd (Finset.mem_range.mpr hk₀mem) h
  rw [hj₀eq]
  change σ.w (B j₀) + (↑j₀ : ℤ) * σ.w σ.Φ = (σ.e : ℤ) * σ.h * g
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

/-- The residual slot coefficient `c_j = R(B_j)·z^{j·m̂}` (`m̂ = −thg`), so that
`R(B_j·Φ̂^j) = c_j·ψ(z)^j`. -/
private noncomputable def cslot (σ : Stage p F) (g : ℕ) (B : ℕ → Polynomial ℤ_[p]) (j : ℕ) :
    LaurentPolynomial ↥σ.K :=
  σ.R (B j) * LaurentPolynomial.T ((j : ℤ) * (-σ.t * (σ.h : ℤ) * (g : ℤ)))

/-- **The no-cancellation engine.**  For development coefficients `B_j` (width < `deg Φ̂`),
no relation `Σ_{j∈T} R(B_j Φ̂^j) = R(−1)·R(B_i Φ̂^i)` with `i ∉ T` can hold: transporting to the
residual side, the two sides assemble to a distinct-ψ-order sum (each term has exact ψ-order `j`
by `psiNotDvd`), which is nonzero by `GRf_priv`. -/
private lemma key_no_cancel (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ)
    (hg : ψ.natDegree = g) (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (hΦne : Φhat ≠ 0)
    (hDeg : Φhat.natDegree = σ.e * g * σ.Φ.natDegree)
    (B : ℕ → Polynomial ℤ_[p]) (hdeg : ∀ j, (B j).degree < Φhat.degree)
    (i : ℕ) (T : Finset ℕ) (hiT : i ∉ T) (hBi : B i ≠ 0) (hBT : ∀ j ∈ T, B j ≠ 0) :
    (∑ j ∈ T, σ.R (B j * Φhat ^ j)) ≠ σ.R (-1) * σ.R (B i * Φhat ^ i) := by
  intro heq
  have hTne0 : ∀ n : ℤ, (LaurentPolynomial.T n : LaurentPolynomial ↥σ.K) ≠ 0 :=
    fun n => (LaurentPolynomial.isUnit_T n).ne_zero
  have hRhat := L3_liftResidual σ ψ g Φhat hlift
  -- the residual slot identity R(B_j Φ̂^j) = c_j ψ^j
  have hRa : ∀ j, B j ≠ 0 →
      σ.R (B j * Φhat ^ j) = cslot σ g B j * Polynomial.toLaurent ψ ^ j := by
    intro j hBj
    unfold cslot
    rw [σ.hRmul _ _ hBj (pow_ne_zero j hΦne), R_pow σ Φhat hΦne j, hRhat, mul_pow,
      LaurentPolynomial.T_pow, ← mul_assoc]
  have hBdeg' : ∀ j, B j ≠ 0 → (B j).natDegree < σ.e * g * σ.Φ.natDegree := by
    intro j hBj
    have h := Polynomial.natDegree_lt_natDegree hBj (hdeg j)
    rwa [hDeg] at h
  have hc0 : ∀ j, B j ≠ 0 → cslot σ g B j ≠ 0 := by
    intro j hBj
    unfold cslot
    exact mul_ne_zero (σ.hRne _ hBj) (hTne0 _)
  have hcnd : ∀ j, B j ≠ 0 → ¬ (Polynomial.toLaurent ψ ∣ cslot σ g B j) := by
    intro j hBj hdvd
    unfold cslot at hdvd
    have h2 := hdvd.mul_right (LaurentPolynomial.T (-((j : ℤ) * (-σ.t * (σ.h : ℤ) * (g : ℤ)))))
    rw [mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero,
      mul_one] at h2
    exact psiNotDvd σ ψ g hg hmon hψ hψz (B j) hBj (hBdeg' j hBj) h2
  have hRm1 : σ.R (-1 : Polynomial ℤ_[p]) ≠ 0 := σ.hRne _ (neg_ne_zero.mpr one_ne_zero)
  -- the twisted coefficient certificates
  have hc' : ∀ j ∈ insert i T,
      (if j = i then -(σ.R (-1) * cslot σ g B i) else cslot σ g B j) ≠ 0 ∧
      ¬ (Polynomial.toLaurent ψ ∣
        (if j = i then -(σ.R (-1) * cslot σ g B i) else cslot σ g B j)) := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hjT
    · rw [if_pos rfl]
      refine ⟨neg_ne_zero.mpr (mul_ne_zero hRm1 (hc0 j hBi)), ?_⟩
      intro hdvd
      rw [dvd_neg] at hdvd
      have h2 := hdvd.mul_left (σ.R (-1))
      rw [← mul_assoc, R_negone_sq σ, one_mul] at h2
      exact hcnd j hBi h2
    · have hne : j ≠ i := by rintro rfl; exact hiT hjT
      rw [if_neg hne]
      exact ⟨hc0 j (hBT j hjT), hcnd j (hBT j hjT)⟩
  -- the vanishing distinct-ψ-order sum forced by `heq`
  have hsum0 : (∑ j ∈ insert i T,
      (if j = i then -(σ.R (-1) * cslot σ g B i) else cslot σ g B j)
        * Polynomial.toLaurent ψ ^ j) = 0 := by
    rw [Finset.sum_insert hiT, if_pos rfl]
    have hrest : (∑ j ∈ T,
        (if j = i then -(σ.R (-1) * cslot σ g B i) else cslot σ g B j)
          * Polynomial.toLaurent ψ ^ j)
        = ∑ j ∈ T, σ.R (B j * Φhat ^ j) := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hne : j ≠ i := by rintro rfl; exact hiT hj
      rw [if_neg hne, ← hRa j (hBT j hj)]
    rw [hrest, heq, hRa i hBi]
    ring
  exact GRf_priv ψ hψ hψz
    (fun j => if j = i then -(σ.R (-1) * cslot σ g B i) else cslot σ g B j)
    (insert i T) ⟨i, Finset.mem_insert_self i T⟩ hc' hsum0

/-- **Minimizing-slot subsums are honest** (the `=` core of K1): a nonempty sum of slot terms
`B_j Φ̂^j`, all of weight exactly `m`, is nonzero of weight exactly `m`, with additive residuals.
Induction on the slot set; both degenerations (a vanishing subsum, a weight jump) reduce to a
`key_no_cancel` relation via `hRlt`/`R_neg` — using only `R(−1)² = 1`, never the sign. -/
private lemma minsum_facts (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ)
    (hg : ψ.natDegree = g) (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (hΦne : Φhat ≠ 0)
    (hDeg : Φhat.natDegree = σ.e * g * σ.Φ.natDegree)
    (B : ℕ → Polynomial ℤ_[p]) (hdeg : ∀ j, (B j).degree < Φhat.degree) (m : ℤ) :
    ∀ S' : Finset ℕ, (∀ j ∈ S', B j ≠ 0) → (∀ j ∈ S', σ.w (B j * Φhat ^ j) = m) →
      S'.Nonempty →
      (∑ j ∈ S', B j * Φhat ^ j) ≠ 0 ∧ σ.w (∑ j ∈ S', B j * Φhat ^ j) = m ∧
        σ.R (∑ j ∈ S', B j * Φhat ^ j) = ∑ j ∈ S', σ.R (B j * Φhat ^ j) := by
  intro S'
  induction S' using Finset.induction with
  | empty => exact fun _ _ h => absurd h Finset.not_nonempty_empty
  | insert i T hiT ih =>
    intro hB' hw' _
    have hBi : B i ≠ 0 := hB' i (Finset.mem_insert_self i T)
    have hwi : σ.w (B i * Φhat ^ i) = m := hw' i (Finset.mem_insert_self i T)
    have hai : B i * Φhat ^ i ≠ 0 := mul_ne_zero hBi (pow_ne_zero i hΦne)
    have hBT : ∀ j ∈ T, B j ≠ 0 := fun j hj => hB' j (Finset.mem_insert_of_mem hj)
    have hwT : ∀ j ∈ T, σ.w (B j * Φhat ^ j) = m := fun j hj => hw' j (Finset.mem_insert_of_mem hj)
    rcases T.eq_empty_or_nonempty with rfl | hTne
    · simp only [Finset.sum_insert (Finset.notMem_empty i), Finset.sum_empty, add_zero]
      exact ⟨hai, hwi, trivial⟩
    · obtain ⟨hsTne, hwsT, hRsT⟩ := ih hBT hwT hTne
      rw [Finset.sum_insert hiT, Finset.sum_insert hiT]
      -- (a) the subsum cannot vanish (else Σ_T R(a_j) = R(−1)·R(a_i), killed by key_no_cancel)
      have hsne : B i * Φhat ^ i + (∑ j ∈ T, B j * Φhat ^ j) ≠ 0 := by
        intro h0
        have hsTeq : (∑ j ∈ T, B j * Φhat ^ j) = -(B i * Φhat ^ i) :=
          eq_neg_of_add_eq_zero_right h0
        have hR1 : σ.R (∑ j ∈ T, B j * Φhat ^ j) = σ.R (-1) * σ.R (B i * Φhat ^ i) := by
          rw [hsTeq, R_neg σ _ hai]
        exact key_no_cancel σ ψ g hg hmon hψ hψz Φhat hlift hΦne hDeg B hdeg i T hiT hBi hBT
          (hRsT.symm.trans hR1)
      have hwge : m ≤ σ.w (B i * Φhat ^ i + ∑ j ∈ T, B j * Φhat ^ j) := by
        have h1 := σ.hwult _ _ hai hsTne hsne
        rwa [hwi, hwsT, min_self] at h1
      rcases eq_or_lt_of_le hwge with hweq | hwlt
      · -- weight stays at m: hRadd gives residual additivity
        refine ⟨hsne, hweq.symm, ?_⟩
        rw [σ.hRadd _ _ hai hsTne hsne (by rw [hwi, hwsT]) (by rw [hwi]; exact hweq.symm), hRsT]
      · -- (b) the weight cannot jump (else hRlt forces the same killed relation)
        exfalso
        have hnegne : -(∑ j ∈ T, B j * Φhat ^ j) ≠ 0 := neg_ne_zero.mpr hsTne
        have haux : -(∑ j ∈ T, B j * Φhat ^ j) + (B i * Φhat ^ i + ∑ j ∈ T, B j * Φhat ^ j)
            = B i * Φhat ^ i := by ring
        have hlt' : σ.w (-(∑ j ∈ T, B j * Φhat ^ j))
            < σ.w (B i * Φhat ^ i + ∑ j ∈ T, B j * Φhat ^ j) := by
          rwa [w_neg σ _ hsTne, hwsT]
        have hRlt := σ.hRlt _ _ hnegne hsne (by rw [haux]; exact hai) hlt'
        rw [haux, R_neg σ _ hsTne, hRsT] at hRlt
        have hfinal : (∑ j ∈ T, σ.R (B j * Φhat ^ j)) = σ.R (-1) * σ.R (B i * Φhat ^ i) := by
          rw [hRlt, ← mul_assoc, R_negone_sq σ, one_mul]
        exact key_no_cancel σ ψ g hg hmon hψ hψz Φhat hlift hΦne hDeg B hdeg i T hiT hBi hBT
          hfinal

theorem L3_K1 {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (hmon : ψ.Monic) (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) : K1At σ.w Φhat ((σ.e : ℤ) * σ.h * g) := by
  classical
  intro f B N hf hdev
  obtain ⟨hdeg, hzero, hsum⟩ := hdev
  have hg1 : 1 ≤ g := by have := hψ.natDegree_pos; omega
  obtain ⟨hMon, hDeg⟩ := L3_liftMonic σ ψ g hg1 Φhat hlift
  have hΦne : Φhat ≠ 0 := hMon.ne_zero
  have hwhat : σ.w Φhat = (σ.e : ℤ) * σ.h * g := w_Phat σ ψ g hg1 Φhat hlift hΦne
  -- slot weights
  have hwa : ∀ j, B j ≠ 0 →
      σ.w (B j * Φhat ^ j) = σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g) := by
    intro j hBj
    rw [σ.hwmul _ _ hBj (pow_ne_zero j hΦne), w_pow σ Φhat hΦne j, hwhat]
  -- the nonzero-slot set and the attained minimum
  set SN : Finset ℕ := (Finset.range N).filter (fun j => B j ≠ 0) with hSNdef
  have hSNmem : ∀ j : ℕ, j ∈ SN ↔ j < N ∧ B j ≠ 0 := by
    intro j
    rw [hSNdef, Finset.mem_filter, Finset.mem_range]
  have hSNne : SN.Nonempty := by
    have hfs : (∑ j ∈ Finset.range N, B j * Φhat ^ j) ≠ 0 := hsum ▸ hf
    obtain ⟨j, hjr, hjne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hfs
    refine ⟨j, (hSNmem j).mpr ⟨Finset.mem_range.mp hjr, fun hBj => hjne ?_⟩⟩
    rw [hBj, zero_mul]
  obtain ⟨m, hmle, j₀, hj₀SN, hj₀eq⟩ :
      ∃ m : ℤ, (∀ j ∈ SN, m ≤ σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g)) ∧
        ∃ j₀, j₀ ∈ SN ∧ m = σ.w (B j₀) + (j₀ : ℤ) * ((σ.e : ℤ) * σ.h * g) := by
    obtain ⟨j₁, hj₁, heq₁⟩ := Finset.exists_mem_eq_inf' hSNne
      (fun j => σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g))
    exact ⟨SN.inf' hSNne (fun j => σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g)),
      fun j hj => Finset.inf'_le _ hj, j₁, hj₁, heq₁⟩
  have hSN_B : ∀ j ∈ SN, B j ≠ 0 := fun j hj => ((hSNmem j).mp hj).2
  -- minimizing and non-minimizing slots
  set Smin : Finset ℕ :=
    SN.filter (fun j => σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g) = m) with hSminDef
  set Srest : Finset ℕ :=
    SN.filter (fun j => ¬ (σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g) = m)) with hSrestDef
  have hSminMem : ∀ j : ℕ, j ∈ Smin ↔
      j ∈ SN ∧ σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g) = m := by
    intro j
    rw [hSminDef, Finset.mem_filter]
  have hSrestMem : ∀ j : ℕ, j ∈ Srest ↔
      j ∈ SN ∧ ¬ (σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g) = m) := by
    intro j
    rw [hSrestDef, Finset.mem_filter]
  have hj₀Smin : j₀ ∈ Smin := (hSminMem j₀).mpr ⟨hj₀SN, hj₀eq.symm⟩
  have hSminB : ∀ j ∈ Smin, B j ≠ 0 := fun j hj => hSN_B j ((hSminMem j).mp hj).1
  have hSminw : ∀ j ∈ Smin, σ.w (B j * Φhat ^ j) = m := by
    intro j hj
    rw [hwa j (hSminB j hj)]
    exact ((hSminMem j).mp hj).2
  obtain ⟨hminNe, hminW, -⟩ := minsum_facts σ ψ g hg hmon hψ hψz Φhat hlift hΦne hDeg B hdeg m
    Smin hSminB hSminw ⟨j₀, hj₀Smin⟩
  -- the development sum over the nonzero slots, split at the minimum
  have hfSN : f = ∑ j ∈ SN, B j * Φhat ^ j := by
    rw [hsum, hSNdef]
    refine (Finset.sum_filter_of_ne ?_).symm
    intro x hx hax hBx
    exact hax (by rw [hBx, zero_mul])
  have hfd : f = (∑ j ∈ Smin, B j * Φhat ^ j) + (∑ j ∈ Srest, B j * Φhat ^ j) := by
    rw [hfSN, hSminDef, hSrestDef]
    exact (Finset.sum_filter_add_sum_filter_not SN _ _).symm
  -- w f = m
  have hwf : σ.w f = m := by
    rcases eq_or_ne (∑ j ∈ Srest, B j * Φhat ^ j) 0 with hr0 | hrne
    · rw [hfd, hr0, add_zero]
      exact hminW
    · have hwrest : m + 1 ≤ σ.w (∑ j ∈ Srest, B j * Φhat ^ j) := by
        refine w_sum_ge σ Srest _ (m + 1) ?_ hrne
        intro j hj haj
        have hjSN : j ∈ SN := ((hSrestMem j).mp hj).1
        have hBj : B j ≠ 0 := hSN_B j hjSN
        have h1 := hmle j hjSN
        have h2 : ¬ (σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g) = m) := ((hSrestMem j).mp hj).2
        rw [hwa j hBj]
        omega
      have hfne' : (∑ j ∈ Smin, B j * Φhat ^ j) + (∑ j ∈ Srest, B j * Φhat ^ j) ≠ 0 :=
        hfd ▸ hf
      have hge : m ≤ σ.w f := by
        rw [hfd]
        have h1 := σ.hwult _ _ hminNe hrne hfne'
        rw [hminW] at h1
        exact le_trans (le_min le_rfl (by omega)) h1
      by_contra hne
      have hgt : m < σ.w f := lt_of_le_of_ne hge (fun h => hne h.symm)
      have hnegne : -(∑ j ∈ Srest, B j * Φhat ^ j) ≠ 0 := neg_ne_zero.mpr hrne
      have hfmin_eq : (∑ j ∈ Smin, B j * Φhat ^ j) = f + -(∑ j ∈ Srest, B j * Φhat ^ j) := by
        rw [hfd]; ring
      have hminne' : f + -(∑ j ∈ Srest, B j * Φhat ^ j) ≠ 0 := hfmin_eq ▸ hminNe
      have h1 := σ.hwult f _ hf hnegne hminne'
      rw [← hfmin_eq, hminW, w_neg σ _ hrne] at h1
      have h3 : m < min (σ.w f) (σ.w (∑ j ∈ Srest, B j * Φhat ^ j)) := lt_min hgt (by omega)
      omega
  -- assemble SlotMinAttained
  refine ⟨?_, j₀, ?_, ?_, ?_⟩
  · intro j hjN hBj
    have hjSN : j ∈ SN := (hSNmem j).mpr ⟨hjN, hBj⟩
    rw [hwf]
    exact hmle j hjSN
  · exact ((hSNmem j₀).mp hj₀SN).1
  · exact hSN_B j₀ hj₀SN
  · rw [hwf]; exact hj₀eq

end Core

end LeanUrat.Moves
