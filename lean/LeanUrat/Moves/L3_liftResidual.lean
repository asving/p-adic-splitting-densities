/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.L2_keyResidualPow
import LeanUrat.Moves.L2_strideRule
import LeanUrat.Moves.L0_GRb
import LeanUrat.Moves.L0_FactB_unique

/-!
# Moves/L3_liftResidual — the standard-lift residual `R(Φ̂) = z^{−thg}·ψ(z)` (§B2 D.5)

`R(Φ̂) = z^{m̂}·ψ(z)`, `m̂ = −t·h·g`, proved FROM the displayed lift formula (DEF-9).

Each slot `a_k` of `Φ̂ = Φ^{eg} + Σ_{k<g} t_k Φ^{ek}` has residual
`R(a_k) = ψ_k·z^{k−thg}` (stride rule + realizer residual + Bézout `es+ht=1`) and common
weight `w(a_k) = ehg`.  The slot residuals sit at DISTINCT `T`-exponents, so their initial
forms add without cancellation (`hRadd`); the weights of the partial sums are pinned by
Lemma K1 (`hK1`) applied to the Φ-adic development, and non-vanishing by Fact B uniqueness.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.Moves

open Polynomial

theorem L3_liftResidual {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) : σ.R Φhat = LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ)) * Polynomial.toLaurent ψ := by
  obtain ⟨hψmonic, hψdeg, tt, htt0, httk, hΦhat⟩ := hlift
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  -- the uniform slot family
  set a : ℕ → Polynomial ℤ_[p] :=
    (fun k => if k < g then tt k * σ.Φ ^ (σ.e * k) else σ.Φ ^ (σ.e * g)) with ha
  -- abbreviation for the anchor exponent
  set D : ℤ := - σ.t * (σ.h : ℤ) * (g : ℤ) with hD
  -- Φ̂ is the sum of the family over range (g+1)
  have hsum : Φhat = ∑ k ∈ Finset.range (g + 1), a k := by
    rw [Finset.sum_range_succ]
    have hag : a g = σ.Φ ^ (σ.e * g) := by rw [ha]; simp
    have hlt : ∀ k ∈ Finset.range g, a k = tt k * σ.Φ ^ (σ.e * k) := by
      intro k hk; rw [Finset.mem_range] at hk; rw [ha]; simp [hk]
    rw [hag, Finset.sum_congr rfl hlt, hΦhat, add_comm]
  -- per-slot residual: R(a k) = C(ψ.coeff k) · T (D + k)
  have hslot : ∀ k, k ≤ g →
      σ.R (a k) = LaurentPolynomial.C (ψ.coeff k) * LaurentPolynomial.T (D + (k : ℤ)) := by
    intro k hk
    rcases lt_or_eq_of_le hk with hlt | heq
    · -- k < g
      have hak : a k = tt k * σ.Φ ^ (σ.e * k) := by rw [ha]; simp [hlt]
      by_cases hc : ψ.coeff k = 0
      · -- absent slot: t_k = 0
        have htk0 : tt k = 0 := htt0 k hc
        rw [hak, htk0, zero_mul, σ.hR0, hc, map_zero, zero_mul]
      · -- present slot
        obtain ⟨htne, htc, htw, htR⟩ := httk k hlt hc
        rw [hak, L2_strideRule σ (tt k) htne htc (σ.e * k), htR, mul_assoc,
            ← LaurentPolynomial.T_add]
        congr 1
        congr 1
        rw [hD]
        push_cast
        linear_combination (k : ℤ) * σ.hbez
    · -- k = g : leading slot Φ^{eg}, coeff = 1 (monic)
      subst heq
      have hag : a k = σ.Φ ^ (σ.e * k) := by rw [ha]; simp
      have hck : ψ.coeff k = 1 := by
        have := hψmonic.coeff_natDegree; rw [hψdeg] at this; exact this
      rw [hag, L2_keyResidualPow σ (σ.e * k), hck, map_one, one_mul]
      congr 1
      rw [hD]
      push_cast
      linear_combination (k : ℤ) * σ.hbez
  -- the graded additivity core: R is additive across the slots because they share the common
  -- weight W = ehg (so hRadd applies) and the partial-sum weights are pinned by Lemma K1 (σ.hK1)
  -- applied to the Φ-adic development; non-vanishing by Fact B (L0_FactB_unique).
  have hadd : σ.R (∑ k ∈ Finset.range (g + 1), a k)
      = ∑ k ∈ Finset.range (g + 1), σ.R (a k) := by
    set W : ℤ := (σ.e : ℤ) * σ.h * g with hW
    set coeff : ℕ → Polynomial ℤ_[p] := (fun k => if k < g then tt k else 1) with hcoeff
    set M : ℕ := σ.e * g + 1 with hM
    set Bc : ℕ → ℕ → Polynomial ℤ_[p] :=
      (fun n j => ∑ k ∈ Finset.range n, if σ.e * k = j then coeff k else 0) with hBc
    -- basic degree facts
    have hbotΦ : (⊥ : WithBot ℕ) < σ.Φ.degree := by
      rw [Polynomial.degree_eq_natDegree hΦne]; exact WithBot.bot_lt_coe _
    have hΦdeg1 : (1 : Polynomial ℤ_[p]).degree < σ.Φ.degree := by
      have hnd : 0 < σ.Φ.natDegree := by have := σ.hdeg; omega
      rw [Polynomial.degree_one, Polynomial.degree_eq_natDegree hΦne]; exact_mod_cast hnd
    -- a k as coeff k · Φ^{ek}
    have hacoeff : ∀ k, k ≤ g → a k = coeff k * σ.Φ ^ (σ.e * k) := by
      intro k hk
      by_cases hlt : k < g
      · rw [ha, hcoeff]; simp [hlt]
      · have hkg : k = g := le_antisymm hk (not_lt.mp hlt)
        subst hkg; rw [ha, hcoeff]; simp
    -- coeff k ∈ C
    have hcoeffC : ∀ k, k ≤ g → (coeff k).degree < σ.Φ.degree := by
      intro k hk
      by_cases hlt : k < g
      · have hck : coeff k = tt k := by rw [hcoeff]; simp [hlt]
        rw [hck]
        by_cases hc : ψ.coeff k = 0
        · rw [htt0 k hc, Polynomial.degree_zero]; exact hbotΦ
        · exact (httk k hlt hc).2.1
      · have hkg : k = g := le_antisymm hk (not_lt.mp hlt)
        subst hkg
        have hck : coeff k = 1 := by rw [hcoeff]; simp
        rw [hck]; exact hΦdeg1
    -- w 1 = 0 and w(Φ^m) = m·h
    have hw1 : σ.w 1 = 0 := by
      have h := σ.hwmul 1 1 one_ne_zero one_ne_zero; rw [mul_one] at h; linarith
    have hwpow : ∀ m : ℕ, σ.w (σ.Φ ^ m) = (m : ℤ) * σ.h := by
      intro m; induction m with
      | zero => simpa using hw1
      | succ n ih =>
        rw [pow_succ, σ.hwmul _ _ (pow_ne_zero n hΦne) hΦne, ih, σ.hwΦ]; push_cast; ring
    -- weight of any nonzero slot is W
    have hwa : ∀ k, a k ≠ 0 → σ.w (a k) = W := by
      intro k hak
      by_cases hlt : k < g
      · have hak' : a k = tt k * σ.Φ ^ (σ.e * k) := by rw [ha]; simp [hlt]
        have htne : tt k ≠ 0 := fun h => hak (by rw [hak', h, zero_mul])
        have hcne : ψ.coeff k ≠ 0 := fun hc => htne (htt0 k hc)
        obtain ⟨_, htc, htw, _⟩ := httk k hlt hcne
        rw [hak', σ.hwmul _ _ htne (pow_ne_zero _ hΦne), hwpow, σ.hStretch _ htne htc, htw, hW]
        push_cast; ring
      · have hak' : a k = σ.Φ ^ (σ.e * g) := by rw [ha]; simp [hlt]
        rw [hak', hwpow, hW]; push_cast; ring
    -- the Φ-adic development of every partial sum
    have hDev : ∀ n, n ≤ g + 1 → IsDevelopment σ.Φ (∑ k ∈ Finset.range n, a k) (Bc n) M := by
      intro n hn
      refine ⟨?_, ?_, ?_⟩
      · intro j
        rw [hBc]
        refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
        rw [Finset.sup_lt_iff hbotΦ]
        intro k hk
        by_cases hjk : σ.e * k = j
        · rw [if_pos hjk]
          exact hcoeffC k (Nat.lt_succ_iff.mp (lt_of_lt_of_le (Finset.mem_range.mp hk) hn))
        · rw [if_neg hjk, Polynomial.degree_zero]; exact hbotΦ
      · intro j hj
        rw [hBc]
        apply Finset.sum_eq_zero
        intro k hk
        rw [if_neg]
        intro hcon
        have hkg : k ≤ g := Nat.lt_succ_iff.mp (lt_of_lt_of_le (Finset.mem_range.mp hk) hn)
        have : σ.e * k ≤ σ.e * g := Nat.mul_le_mul (le_refl σ.e) hkg
        rw [hM] at hj; omega
      · rw [Finset.sum_congr rfl (fun k hk =>
            hacoeff k (Nat.lt_succ_iff.mp (lt_of_lt_of_le (Finset.mem_range.mp hk) hn)))]
        simp_rw [hBc, Finset.sum_mul]
        rw [Finset.sum_comm]
        simp_rw [ite_mul, zero_mul, Finset.sum_ite_eq]
        apply Finset.sum_congr rfl
        intro k hk
        have hkg : k ≤ g := Nat.lt_succ_iff.mp (lt_of_lt_of_le (Finset.mem_range.mp hk) hn)
        rw [if_pos (Finset.mem_range.mpr (by
          rw [hM]; have := Nat.mul_le_mul (le_refl σ.e) hkg; omega))]
    -- lower bound W ≤ w(partial sum)
    have hlow : ∀ n, (∑ k ∈ Finset.range n, a k) = 0 ∨ W ≤ σ.w (∑ k ∈ Finset.range n, a k) := by
      intro n
      induction n with
      | zero => left; simp
      | succ n ih =>
        rw [Finset.sum_range_succ]
        by_cases han : a n = 0
        · rw [han, add_zero]; exact ih
        · have hwan : σ.w (a n) = W := hwa n han
          by_cases hSn0 : (∑ k ∈ Finset.range n, a k) = 0
          · rw [hSn0, zero_add]; right; rw [hwan]
          · have hle : W ≤ σ.w (∑ k ∈ Finset.range n, a k) := ih.resolve_left hSn0
            by_cases hsum : (∑ k ∈ Finset.range n, a k) + a n = 0
            · left; exact hsum
            · right
              have hub := σ.hwult _ _ hSn0 han hsum
              rw [hwan, min_eq_right hle] at hub; exact hub
    -- Bc n (e·k) = coeff k  (single nonzero term, e injective)
    have hBcek : ∀ n k, k ∈ Finset.range n → Bc n (σ.e * k) = coeff k := by
      intro n k hkr
      simp only [hBc]
      rw [Finset.sum_eq_single_of_mem k hkr (fun k' _ hne' => by
        rw [if_neg]; intro hc; exact hne' (Nat.eq_of_mul_eq_mul_left σ.he hc)), if_pos rfl]
    -- exact weight of a nonzero partial sum
    have hwSn : ∀ n, n ≤ g + 1 → (∑ k ∈ Finset.range n, a k) ≠ 0 →
        σ.w (∑ k ∈ Finset.range n, a k) = W := by
      intro n hn hSn
      obtain ⟨k, hkr, hak⟩ := Finset.exists_ne_zero_of_sum_ne_zero hSn
      have hkg : k ≤ g := Nat.lt_succ_iff.mp (lt_of_lt_of_le (Finset.mem_range.mp hkr) hn)
      have hck : coeff k ≠ 0 := fun h => hak (by rw [hacoeff k hkg, h, zero_mul])
      have hjlt : σ.e * k < M := by
        rw [hM]; have := Nat.mul_le_mul (le_refl σ.e) hkg; omega
      have hnz : Bc n (σ.e * k) ≠ 0 := by rw [hBcek n k hkr]; exact hck
      have hsw : σ.w (Bc n (σ.e * k)) + (↑(σ.e * k) : ℤ) * σ.w σ.Φ = W := by
        rw [hBcek n k hkr, σ.hwΦ]
        have hwak : σ.w (a k) = σ.w (coeff k) + (↑(σ.e * k) : ℤ) * ↑σ.h := by
          rw [hacoeff k hkg, σ.hwmul _ _ hck (pow_ne_zero _ hΦne), hwpow]
        rw [← hwak]; exact hwa k hak
      have hslotmin := σ.hK1 (∑ k ∈ Finset.range n, a k) (Bc n) M hSn (hDev n hn)
      refine le_antisymm ?_ ((hlow n).resolve_left hSn)
      calc σ.w (∑ k ∈ Finset.range n, a k)
          ≤ σ.w (Bc n (σ.e * k)) + (↑(σ.e * k) : ℤ) * σ.w σ.Φ := hslotmin.1 (σ.e * k) hjlt hnz
        _ = W := hsw
    -- non-vanishing of a partial sum with a present slot (Fact B)
    have hSne : ∀ n, n ≤ g + 1 → (∃ k ∈ Finset.range n, a k ≠ 0) →
        (∑ k ∈ Finset.range n, a k) ≠ 0 := by
      intro n hn hex hcon
      obtain ⟨k, hkr, hak⟩ := hex
      have hkg : k ≤ g := Nat.lt_succ_iff.mp (lt_of_lt_of_le (Finset.mem_range.mp hkr) hn)
      have hdev := hDev n hn
      rw [hcon] at hdev
      have hz : IsDevelopment σ.Φ (0 : Polynomial ℤ_[p]) (fun _ => 0) 0 :=
        ⟨fun _ => by rw [Polynomial.degree_zero]; exact hbotΦ, fun _ _ => rfl, by simp⟩
      have heq : coeff k = 0 := by
        have h := L0_FactB_unique σ.Φ σ.hmonic 0 hdev hz (σ.e * k)
        rw [hBcek n k hkr] at h; simpa using h
      exact hak (by rw [hacoeff k hkg, heq, zero_mul])
    -- main induction: R additive over the slots
    have hind : ∀ n, n ≤ g + 1 →
        σ.R (∑ k ∈ Finset.range n, a k) = ∑ k ∈ Finset.range n, σ.R (a k) := by
      intro n
      induction n with
      | zero => intro _; simp [σ.hR0]
      | succ n ih =>
        intro hn
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        by_cases han : a n = 0
        · rw [han, add_zero, σ.hR0, add_zero]; exact ih (by omega)
        · by_cases hSn0 : (∑ k ∈ Finset.range n, a k) = 0
          · rw [hSn0, zero_add]
            have hih := ih (by omega)
            rw [hSn0, σ.hR0] at hih
            rw [← hih, zero_add]
          · have hSne1 : (∑ k ∈ Finset.range (n + 1), a k) ≠ 0 :=
              hSne (n + 1) hn ⟨n, Finset.mem_range.mpr (by omega), han⟩
            have hwS1 : σ.w (∑ k ∈ Finset.range (n + 1), a k) = W := hwSn (n + 1) hn hSne1
            rw [Finset.sum_range_succ] at hwS1
            have hwSn' : σ.w (∑ k ∈ Finset.range n, a k) = W := hwSn n (by omega) hSn0
            have hwan : σ.w (a n) = W := hwa n han
            rw [σ.hRadd _ _ hSn0 han (by rw [← Finset.sum_range_succ]; exact hSne1)
                (by rw [hwSn', hwan]) (by rw [hwS1, hwSn']), ih (by omega)]
    exact hind (g + 1) le_rfl
  -- assemble
  rw [hsum, hadd, Finset.sum_congr rfl (fun k hk => hslot k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))]
  -- goal: ∑ C(ψ.coeff k) T(D+k) = T D * toLaurent ψ
  have htL : Polynomial.toLaurent ψ
      = ∑ k ∈ Finset.range (g + 1), LaurentPolynomial.C (ψ.coeff k) * LaurentPolynomial.T (k : ℤ) := by
    conv_lhs => rw [ψ.as_sum_range' (g + 1) (by rw [hψdeg]; omega)]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.toLaurent_C_mul_X_pow]
  rw [htL, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [LaurentPolynomial.T_add]
  ring

end LeanUrat.Moves
