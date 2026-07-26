/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.L3_digPrime_nonzero
import LeanUrat.Moves.L3_DIV
import LeanUrat.Moves.L3_liftMonic
import LeanUrat.Moves.L2_keyResidualPow
import LeanUrat.Moves.L0_FactB_unique

/-!
# Moves/L4_TRANSviii_b_R4 — (S6b') the OFFSET P-LIFT above the clean threshold

`moves_ref`: D.7(viii) S6b'; MOVES ~2285-2311, esp. ~2299-2303.

CORRECTED unit (machine-checked finding 1): `hcore : StageCore σ` supplies
`prevIaug : e·wPrev(Φ) < h`, the exact bridge the R3 fan-out identified as unprovable —
the summand parent weights `μ_k ≥ (ν − (eg−1)h)/e > h/e > wPrev(Φ)` clear the (S6b)
threshold at the PREVIOUS read.

Construction (a ≠ 0): with `j₀ := (t·ν) mod e`, `m₁ := (t·ν) div e`, the target scalar
`a` is re-anchored to `b := a·z̄^{m₁} ∈ K⟮z̄⟯` and written `b = P(z̄)` with `deg P < g`
(finite-subfield polynomial representation, reduced mod ψ).  Each present coefficient
`P_k ≠ 0` gets an (S6b) realizer `B_k` of parent weight `μ_k := s·ν + h·m₁ − h·k`; then
`B := Σ_k B_k·Φ^{j₀+e·k}` has all slots tied at total weight `ν` with residual positions
`−m₁ + k` (consecutive, distinct).  Lemma K1 + Fact B give `B ≠ 0`, `w(B) = ν`; `hRadd`
gives slotwise residual additivity; evaluation at `z̄` telescopes to
`z̄^{−m₁}·P(z̄) = a`.  The `a = 0` scalar is realized by `B = 0`.
-/

open Polynomial LeanUrat.Moves

namespace LeanUrat.Moves

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

section Helpers

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

private lemma wOne (σ : Stage p F) : σ.w 1 = 0 := by
  have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h; omega

private lemma wPow (σ : Stage p F) (j : ℕ) : σ.w (σ.Φ ^ j) = (j : ℤ) * σ.h := by
  induction j with
  | zero => simpa using wOne σ
  | succ n ih =>
    rw [pow_succ, σ.hwmul _ _ (pow_ne_zero n σ.hmonic.ne_zero) σ.hmonic.ne_zero, ih, σ.hwΦ]
    push_cast; ring

/-- Every element of the next residue field `K⟮z̄⟯` is a polynomial in `z̄` over `K`
(the image of `eval₂` is a subfield: inverses via the finite-field power trick). -/
private lemma exists_poly_of_mem_nextField (σ : Stage p F) (zbar : Fˣ) (b : F)
    (hb : b ∈ σ.nextField zbar) :
    ∃ Q : Polynomial ↥σ.K, Polynomial.eval₂ σ.K.subtype (zbar : F) Q = b := by
  refine Subfield.closure_induction ?_ ?_ ?_ ?_ ?_ ?_ hb
  · rintro x (hx | hx)
    · exact ⟨Polynomial.C ⟨x, hx⟩, by rw [Polynomial.eval₂_C]; rfl⟩
    · exact ⟨Polynomial.X, by rw [Polynomial.eval₂_X, Set.mem_singleton_iff.mp hx]⟩
  · exact ⟨1, Polynomial.eval₂_one _ _⟩
  · rintro x y hx hy ⟨Qx, hQx⟩ ⟨Qy, hQy⟩
    exact ⟨Qx + Qy, by rw [Polynomial.eval₂_add, hQx, hQy]⟩
  · rintro x hx ⟨Qx, hQx⟩
    exact ⟨-Qx, by rw [Polynomial.eval₂_neg, hQx]⟩
  · rintro x hx ⟨Qx, hQx⟩
    by_cases hx0 : x = 0
    · exact ⟨0, by rw [Polynomial.eval₂_zero, hx0, inv_zero]⟩
    · letI : Fintype F := Fintype.ofFinite F
      refine ⟨Qx ^ (Fintype.card F - 2), ?_⟩
      have hpow : Polynomial.eval₂ σ.K.subtype (zbar : F) (Qx ^ (Fintype.card F - 2))
          = x ^ (Fintype.card F - 2) := by
        have := map_pow (Polynomial.eval₂RingHom σ.K.subtype (zbar : F)) Qx (Fintype.card F - 2)
        simp only [Polynomial.coe_eval₂RingHom] at this
        rw [this, hQx]
      rw [hpow]
      have hcard : 2 ≤ Fintype.card F := Fintype.one_lt_card
      have h1 : x ^ (Fintype.card F - 1) = 1 := FiniteField.pow_card_sub_one_eq_one x hx0
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← pow_succ]
      rw [(by omega : Fintype.card F - 2 + 1 = Fintype.card F - 1)]
      exact h1
  · rintro x y hx hy ⟨Qx, hQx⟩ ⟨Qy, hQy⟩
    exact ⟨Qx * Qy, by rw [Polynomial.eval₂_mul, hQx, hQy]⟩

/-- Inlined copy of `L3_liftWeight` (dep not built on disk): `w(Φ̂) = e·h·g`. -/
private lemma liftWeight' (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg1 : 1 ≤ g)
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
  have hw1 : σ.w 1 = 0 := wOne σ
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

/-- The `Φ`-adic development of an offset arithmetic-progression slot sum
`Σ_{k∈t} C_k·Φ^{j₀+e·k}` (slots `j₀+e·k < e·g`, coefficients in `C_Φ`). -/
private lemma devOfSum (σ : Stage p F) (g j₀ : ℕ) (hj₀ : j₀ < σ.e)
    (C : ℕ → Polynomial ℤ_[p]) (t : Finset ℕ) (ht : t ⊆ Finset.range g)
    (hC : ∀ k ∈ t, inC σ.Φ (C k)) :
    ∃ Bf : ℕ → Polynomial ℤ_[p],
      IsDevelopment σ.Φ (∑ k ∈ t, C k * σ.Φ ^ (j₀ + σ.e * k)) Bf (σ.e * g) ∧
      (∀ k ∈ t, Bf (j₀ + σ.e * k) = C k) ∧
      (∀ j, Bf j ≠ 0 → ∃ k ∈ t, j = j₀ + σ.e * k) := by
  have hΦ0 : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hΦdegbot : (⊥ : WithBot ℕ) < σ.Φ.degree :=
    bot_lt_iff_ne_bot.mpr (fun h => hΦ0 (Polynomial.degree_eq_bot.mp h))
  have hlt : ∀ k, k < g → j₀ + σ.e * k < σ.e * g := by
    intro k hk
    have h2 : σ.e * (k + 1) ≤ σ.e * g := Nat.mul_le_mul (le_refl σ.e) hk
    rw [Nat.mul_succ] at h2; omega
  refine ⟨fun j => ∑ k ∈ t, if j = j₀ + σ.e * k then C k else 0, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff hΦdegbot]
    intro k hk
    by_cases hjk : j = j₀ + σ.e * k
    · rw [if_pos hjk]; exact hC k hk
    · rw [if_neg hjk, Polynomial.degree_zero]; exact hΦdegbot
  · intro j hj
    apply Finset.sum_eq_zero
    intro k hk
    apply if_neg
    intro hjk
    have := hlt k (Finset.mem_range.mp (ht hk))
    omega
  · have step1 : ∑ j ∈ Finset.range (σ.e * g),
        (∑ k ∈ t, if j = j₀ + σ.e * k then C k else 0) * σ.Φ ^ j
        = ∑ k ∈ t, C k * σ.Φ ^ (j₀ + σ.e * k) := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      have hmem : j₀ + σ.e * k ∈ Finset.range (σ.e * g) :=
        Finset.mem_range.mpr (hlt k (Finset.mem_range.mp (ht hk)))
      simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq', if_pos hmem]
    exact step1.symm
  · intro k hk
    show (∑ k' ∈ t, if j₀ + σ.e * k = j₀ + σ.e * k' then C k' else 0) = C k
    rw [Finset.sum_eq_single k]
    · rw [if_pos rfl]
    · intro k' hk' hne
      exact if_neg (fun hh => hne ((Nat.eq_of_mul_eq_mul_left σ.he (by omega)).symm))
    · intro h; exact absurd hk h
  · intro j hj
    obtain ⟨k, hk, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj
    by_cases hjk : j = j₀ + σ.e * k
    · exact ⟨k, hk, hjk⟩
    · rw [if_neg hjk] at hne; exact absurd rfl hne

/-- Equal-weight offset slot sums are nonzero (Fact B) with the tied weight (Lemma K1). -/
private lemma sumNW (σ : Stage p F) (g j₀ : ℕ) (hj₀ : j₀ < σ.e)
    (C : ℕ → Polynomial ℤ_[p]) (t : Finset ℕ) (ht : t ⊆ Finset.range g) (htne : t.Nonempty)
    (ν : ℤ)
    (hC : ∀ k ∈ t, C k ≠ 0 ∧ inC σ.Φ (C k) ∧
      σ.w (C k) + ((j₀ + σ.e * k : ℕ) : ℤ) * σ.h = ν) :
    (∑ k ∈ t, C k * σ.Φ ^ (j₀ + σ.e * k)) ≠ 0 ∧
      σ.w (∑ k ∈ t, C k * σ.Φ ^ (j₀ + σ.e * k)) = ν := by
  obtain ⟨Bf, hdev, hex, hsupp⟩ := devOfSum σ g j₀ hj₀ C t ht (fun k hk => (hC k hk).2.1)
  have hSne : (∑ k ∈ t, C k * σ.Φ ^ (j₀ + σ.e * k)) ≠ 0 := by
    intro hS0
    rw [hS0] at hdev
    have hzero : IsDevelopment σ.Φ (0 : Polynomial ℤ_[p]) (fun _ => (0 : Polynomial ℤ_[p])) 0 := by
      refine ⟨fun j => ?_, fun j _ => rfl, by simp⟩
      rw [Polynomial.degree_zero]
      exact bot_lt_iff_ne_bot.mpr (fun h => σ.hmonic.ne_zero (Polynomial.degree_eq_bot.mp h))
    have hall := L0_FactB_unique σ.Φ σ.hmonic 0 hdev hzero
    obtain ⟨k₀, hk₀⟩ := htne
    have hzk := hall (j₀ + σ.e * k₀)
    rw [hex k₀ hk₀] at hzk
    exact (hC k₀ hk₀).1 hzk
  refine ⟨hSne, ?_⟩
  obtain ⟨-, j, hjN, hjnz, hjeq⟩ := σ.hK1 _ Bf (σ.e * g) hSne hdev
  obtain ⟨k, hk, hjk⟩ := hsupp j hjnz
  subst hjk
  rw [hjeq]
  show σ.w (Bf (j₀ + σ.e * k)) + ((j₀ + σ.e * k : ℕ) : ℤ) * σ.w σ.Φ = ν
  rw [hex k hk, σ.hwΦ]
  exact (hC k hk).2.2

/-- Slotwise residual additivity across an equal-weight offset slot sum (`hRadd` chain). -/
private lemma sumRes (σ : Stage p F) (g j₀ : ℕ) (hj₀ : j₀ < σ.e)
    (C : ℕ → Polynomial ℤ_[p]) (ν : ℤ) :
    ∀ t : Finset ℕ, t ⊆ Finset.range g →
      (∀ k ∈ t, C k ≠ 0 ∧ inC σ.Φ (C k) ∧
        σ.w (C k) + ((j₀ + σ.e * k : ℕ) : ℤ) * σ.h = ν) →
      σ.R (∑ k ∈ t, C k * σ.Φ ^ (j₀ + σ.e * k))
        = ∑ k ∈ t, σ.R (C k * σ.Φ ^ (j₀ + σ.e * k)) := by
  intro t
  induction t using Finset.cons_induction with
  | empty => intro _ _; simpa using σ.hR0
  | cons a t' ha ih =>
    intro hsub hC
    have hsub' : t' ⊆ Finset.range g := fun x hx => hsub (Finset.mem_cons.mpr (Or.inr hx))
    have hCa := hC a (Finset.mem_cons_self a t')
    have hC' : ∀ k ∈ t', C k ≠ 0 ∧ inC σ.Φ (C k) ∧
        σ.w (C k) + ((j₀ + σ.e * k : ℕ) : ℤ) * σ.h = ν :=
      fun k hk => hC k (Finset.mem_cons.mpr (Or.inr hk))
    rw [Finset.sum_cons, Finset.sum_cons]
    rcases t'.eq_empty_or_nonempty with h0 | htne'
    · subst h0; simp [σ.hR0]
    · have hΦpne : σ.Φ ^ (j₀ + σ.e * a) ≠ 0 := pow_ne_zero _ σ.hmonic.ne_zero
      have hfa_ne : C a * σ.Φ ^ (j₀ + σ.e * a) ≠ 0 := mul_ne_zero hCa.1 hΦpne
      have hfa_w : σ.w (C a * σ.Φ ^ (j₀ + σ.e * a)) = ν := by
        rw [σ.hwmul _ _ hCa.1 hΦpne, wPow σ]
        exact hCa.2.2
      obtain ⟨hS'ne, hS'w⟩ := sumNW σ g j₀ hj₀ C t' hsub' htne' ν hC'
      have hcons := sumNW σ g j₀ hj₀ C (Finset.cons a t' ha) hsub
        ⟨a, Finset.mem_cons_self a t'⟩ ν hC
      rw [Finset.sum_cons] at hcons
      have hadd := σ.hRadd _ _ hfa_ne hS'ne hcons.1
        (by rw [hfa_w, hS'w]) (by rw [hcons.2, hfa_w])
      rw [hadd, ih hsub' hC']

end Helpers

/-- **D.7(viii) S6b' [CORRECTED: machine-checked finding 1].** Above the CLEAN threshold
`σ.w Φ̂ < ν`, every NEXT-field scalar `a ∈ K⟮z̄⟯` is a residue digit of some coefficient
`B ∈ C_{Φ̂}`, realized at the prescribed weight when `a ≠ 0`.  The correction adds
`hcore : StageCore σ`, whose `prevIaug : e·wPrev(Φ) < h` clears the (S6b) threshold at
every summand of the offset P-lift (the exact R3 blocker). -/
theorem L4_TRANSviii_b {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (hcore : StageCore σ) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g) (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (zbar : Fˣ) (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0) (ν : ℤ) (hthr : σ.w Φhat < ν) (a : F) (ha : a ∈ σ.nextField zbar) : ∃ B, inC Φhat B ∧ σ.digPrime zbar B = a ∧ (a ≠ 0 → B ≠ 0 ∧ σ.w B = ν) := by
  have hg1 : 1 ≤ g := by rw [← hg]; exact hψ.natDegree_pos
  obtain ⟨hΦmon, hΦdeg⟩ := L3_liftMonic σ ψ g hg1 Φhat hlift
  have hΦne : Φhat ≠ 0 := hΦmon.ne_zero
  by_cases ha0 : a = 0
  · refine ⟨0, ?_, ?_, fun h => absurd ha0 h⟩
    · simp only [inC, Polynomial.degree_zero]
      exact bot_lt_iff_ne_bot.mpr (fun h => hΦne (Polynomial.degree_eq_bot.mp h))
    · simp only [Stage.digPrime, σ.hR0, map_zero, ha0]
  · -- ===== numeric setup =====
    have hepos : (0 : ℤ) < (σ.e : ℤ) := by exact_mod_cast σ.he
    have hhpos : (0 : ℤ) < (σ.h : ℤ) := by exact_mod_cast σ.hh
    have hwhat : σ.w Φhat = (σ.e : ℤ) * σ.h * g := liftWeight' σ ψ g hg1 Φhat hlift hΦne
    have hνlt : (σ.e : ℤ) * σ.h * g < ν := hwhat ▸ hthr
    have hIaug : (σ.e : ℤ) * σ.wPrev σ.Φ < (σ.h : ℤ) := hcore.prevIaug
    set m₁ : ℤ := σ.t * ν / σ.e with hm₁
    set j₀z : ℤ := σ.t * ν % σ.e with hj₀z
    have hj₀nn : 0 ≤ j₀z := by rw [hj₀z]; exact Int.emod_nonneg _ hepos.ne'
    have hj₀lt : j₀z < (σ.e : ℤ) := by rw [hj₀z]; exact Int.emod_lt_of_pos _ hepos
    have hsplit : (σ.e : ℤ) * m₁ + j₀z = σ.t * ν := by
      rw [hm₁, hj₀z]; exact Int.mul_ediv_add_emod (σ.t * ν) σ.e
    set j₀ : ℕ := j₀z.toNat with hj₀n
    have hj₀cast : (j₀ : ℤ) = j₀z := Int.toNat_of_nonneg hj₀nn
    have hj₀e : j₀ < σ.e := by omega
    -- ===== the target scalar b = a·z̄^{m₁} and its reduced polynomial P =====
    have hzmem : (zbar : F) ∈ σ.nextField zbar := Subfield.subset_closure (Or.inr rfl)
    have hbmem : a * ((zbar ^ m₁ : Fˣ) : F) ∈ σ.nextField zbar := by
      refine mul_mem ha ?_
      rw [Units.val_zpow_eq_zpow_val]
      exact Subfield.zpow_mem _ hzmem m₁
    obtain ⟨Q, hQ⟩ := exists_poly_of_mem_nextField σ zbar _ hbmem
    set P : Polynomial ↥σ.K := Q %ₘ ψ with hPdef
    have hPeval : Polynomial.eval₂ σ.K.subtype (zbar : F) P = a * ((zbar ^ m₁ : Fˣ) : F) := by
      have hmod := Polynomial.modByMonic_add_div Q ψ
      have hcong := congrArg (Polynomial.eval₂ σ.K.subtype (zbar : F)) hmod
      rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, hzbar, zero_mul, add_zero] at hcong
      rw [← hPdef] at hcong
      rw [hcong]; exact hQ
    have hbne : a * ((zbar ^ m₁ : Fˣ) : F) ≠ 0 := mul_ne_zero ha0 (Units.ne_zero _)
    have hPne : P ≠ 0 := by
      intro h0; rw [h0, Polynomial.eval₂_zero] at hPeval; exact hbne hPeval.symm
    have hPnat : P.natDegree < g := by
      rw [← hg]
      exact Polynomial.natDegree_lt_natDegree hPne (Polynomial.degree_modByMonic_lt Q hmon)
    -- ===== slot parent-weights and (S6b) realizers =====
    set μ : ℕ → ℤ := fun k => σ.s * ν + σ.h * m₁ - σ.h * (k : ℤ) with hμ
    have hμthr : ∀ k : ℕ, k < g → σ.wPrev σ.Φ < μ k := by
      intro k hk
      have hkz : ((k : ℤ) + 1) ≤ (g : ℤ) := by exact_mod_cast hk
      have h2 : (σ.e : ℤ) * ((k : ℤ) + 1) ≤ (σ.e : ℤ) * g :=
        mul_le_mul_of_nonneg_left hkz (le_of_lt hepos)
      have h2' : (σ.e : ℤ) * ((k : ℤ) + 1) = (σ.e : ℤ) * (k : ℤ) + σ.e := by ring
      have h3 : j₀z + (σ.e : ℤ) * (k : ℤ) + 1 ≤ (σ.e : ℤ) * g := by linarith
      have h4 : (j₀z + (σ.e : ℤ) * (k : ℤ) + 1) * σ.h ≤ (σ.e : ℤ) * g * σ.h :=
        mul_le_mul_of_nonneg_right h3 (le_of_lt hhpos)
      have h5 : (σ.e : ℤ) * g * σ.h = (σ.e : ℤ) * σ.h * g := by ring
      have h6 : (j₀z + (σ.e : ℤ) * (k : ℤ) + 1) * σ.h
          = (j₀z + (σ.e : ℤ) * (k : ℤ)) * σ.h + σ.h := by ring
      have hμkey : (σ.e : ℤ) * μ k = ν - (j₀z + (σ.e : ℤ) * (k : ℤ)) * σ.h := by
        simp only [hμ]; linear_combination (σ.h : ℤ) * hsplit + ν * σ.hbez
      have h7 : (σ.h : ℤ) < (σ.e : ℤ) * μ k := by linarith
      exact lt_of_mul_lt_mul_left (lt_trans hIaug h7) (le_of_lt hepos)
    have hreal : ∀ k : ℕ, ∃ Bk : Polynomial ℤ_[p], (k < g ∧ P.coeff k ≠ 0) →
        Bk ≠ 0 ∧ inC σ.Φ Bk ∧ σ.wPrev Bk = μ k ∧
          σ.R Bk = LaurentPolynomial.C (P.coeff k) * LaurentPolynomial.T (-σ.t * μ k) := by
      intro k
      by_cases hk : k < g ∧ P.coeff k ≠ 0
      · obtain ⟨Bk, h1, h2, h3, h4⟩ := σ.hS6b (μ k) (Units.mk0 (P.coeff k) hk.2) (hμthr k hk.1)
        exact ⟨Bk, fun _ => ⟨h1, h2, h3, by simpa using h4⟩⟩
      · exact ⟨0, fun h => absurd h hk⟩
    choose CB hCB using hreal
    have hsupsub : P.support ⊆ Finset.range g := fun k hk =>
      Finset.mem_range.mpr (lt_of_le_of_lt (Polynomial.le_natDegree_of_mem_supp k hk) hPnat)
    have hsupne : P.support.Nonempty := Polynomial.nonempty_support_iff.mpr hPne
    have hmem' : ∀ k ∈ P.support, k < g ∧ P.coeff k ≠ 0 := fun k hk =>
      ⟨Finset.mem_range.mp (hsupsub hk), Polynomial.mem_support_iff.mp hk⟩
    have hCprops : ∀ k ∈ P.support, CB k ≠ 0 ∧ inC σ.Φ (CB k) ∧
        σ.w (CB k) + ((j₀ + σ.e * k : ℕ) : ℤ) * σ.h = ν := by
      intro k hk
      obtain ⟨h1, h2, h3, -⟩ := hCB k (hmem' k hk)
      refine ⟨h1, h2, ?_⟩
      rw [σ.hStretch (CB k) h1 h2, h3]
      simp only [hμ]
      push_cast [hj₀cast]
      linear_combination (σ.h : ℤ) * hsplit + ν * σ.hbez
    obtain ⟨hBne, hBw⟩ := sumNW σ g j₀ hj₀e CB P.support hsupsub hsupne ν hCprops
    refine ⟨∑ k ∈ P.support, CB k * σ.Φ ^ (j₀ + σ.e * k), ?_, ?_, fun _ => ⟨hBne, hBw⟩⟩
    · -- ===== inC Φ̂: the degree bound =====
      have hd1 : 1 ≤ σ.Φ.natDegree := σ.hdeg
      have hbound : ∀ k ∈ P.support,
          (CB k * σ.Φ ^ (j₀ + σ.e * k)).natDegree ≤ σ.e * g * σ.Φ.natDegree - 1 := by
        intro k hk
        obtain ⟨h1, h2, -⟩ := hCprops k hk
        have hCBdeg : (CB k).natDegree < σ.Φ.natDegree :=
          Polynomial.natDegree_lt_natDegree h1 h2
        have hjk : j₀ + σ.e * k + 1 ≤ σ.e * g := by
          have hkg : k + 1 ≤ g := (hmem' k hk).1
          have h2m : σ.e * (k + 1) ≤ σ.e * g := Nat.mul_le_mul (le_refl σ.e) hkg
          rw [Nat.mul_succ] at h2m; omega
        calc (CB k * σ.Φ ^ (j₀ + σ.e * k)).natDegree
            ≤ (CB k).natDegree + (σ.Φ ^ (j₀ + σ.e * k)).natDegree :=
              Polynomial.natDegree_mul_le
          _ ≤ (σ.Φ.natDegree - 1) + (j₀ + σ.e * k) * σ.Φ.natDegree := by
              rw [σ.hmonic.natDegree_pow]; omega
          _ ≤ σ.e * g * σ.Φ.natDegree - 1 := by
              have hstep := Nat.mul_le_mul hjk (le_refl σ.Φ.natDegree)
              rw [Nat.succ_mul] at hstep; omega
      have hBnat : (∑ k ∈ P.support, CB k * σ.Φ ^ (j₀ + σ.e * k)).natDegree
          ≤ σ.e * g * σ.Φ.natDegree - 1 :=
        Polynomial.natDegree_sum_le_of_forall_le P.support _ hbound
      have hpos : 0 < σ.e * g * σ.Φ.natDegree :=
        Nat.mul_pos (Nat.mul_pos σ.he hg1) hd1
      have hltnat : (∑ k ∈ P.support, CB k * σ.Φ ^ (j₀ + σ.e * k)).natDegree
          < Φhat.natDegree := by rw [hΦdeg]; omega
      show inC Φhat _
      rw [inC, Polynomial.degree_eq_natDegree hΦne]
      exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hltnat)
    · -- ===== the digit evaluates to a =====
      have hRsum := sumRes σ g j₀ hj₀e CB ν P.support hsupsub hCprops
      have hterm : ∀ k ∈ P.support, σ.R (CB k * σ.Φ ^ (j₀ + σ.e * k))
          = LaurentPolynomial.C (P.coeff k) * LaurentPolynomial.T (-m₁ + (k : ℤ)) := by
        intro k hk
        obtain ⟨h1, -, -, h4⟩ := hCB k (hmem' k hk)
        rw [σ.hRmul _ _ h1 (pow_ne_zero _ σ.hmonic.ne_zero), h4,
          L2_keyResidualPow σ (j₀ + σ.e * k), mul_assoc, ← LaurentPolynomial.T_add]
        congr 2
        simp only [hμ]
        push_cast [hj₀cast]
        linear_combination σ.s * hsplit + ((k : ℤ) - m₁) * σ.hbez
      have heval : ∀ k ∈ P.support,
          LaurentPolynomial.eval₂ σ.K.subtype zbar (σ.R (CB k * σ.Φ ^ (j₀ + σ.e * k)))
            = σ.K.subtype (P.coeff k) * ((zbar ^ (-m₁ + (k : ℤ)) : Fˣ) : F) := by
        intro k hk
        rw [hterm k hk, map_mul, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T]
      simp only [Stage.digPrime]
      rw [hRsum, map_sum, Finset.sum_congr rfl heval]
      rw [Finset.sum_subset hsupsub (fun k _ hk' => by
        rw [Polynomial.notMem_support_iff.mp hk', map_zero, zero_mul])]
      have hzsplit : ∀ k ∈ Finset.range g,
          σ.K.subtype (P.coeff k) * ((zbar ^ (-m₁ + (k : ℤ)) : Fˣ) : F)
            = ((zbar ^ (-m₁) : Fˣ) : F) * (σ.K.subtype (P.coeff k) * (zbar : F) ^ k) := by
        intro k hk
        rw [zpow_add, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val]
        ring
      rw [Finset.sum_congr rfl hzsplit, ← Finset.mul_sum]
      have hPsum : ∑ k ∈ Finset.range g, σ.K.subtype (P.coeff k) * (zbar : F) ^ k
          = a * ((zbar ^ m₁ : Fˣ) : F) := by
        rw [← Polynomial.eval₂_eq_sum_range' σ.K.subtype hPnat (zbar : F)]
        exact hPeval
      rw [hPsum]
      calc ((zbar ^ (-m₁) : Fˣ) : F) * (a * ((zbar ^ m₁ : Fˣ) : F))
          = a * (((zbar ^ (-m₁) : Fˣ) : F) * ((zbar ^ m₁ : Fˣ) : F)) := by ring
        _ = a := by
            rw [← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, mul_one]

end LeanUrat.Moves
