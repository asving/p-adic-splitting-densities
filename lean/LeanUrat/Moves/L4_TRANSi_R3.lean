/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.L0_FactA_exists
import LeanUrat.Moves.L3_liftMonic
import LeanUrat.Moves.L3_DIV
import LeanUrat.Moves.ResVal

/-!
# Moves/L4_TRANSi_R3 — D.7(i): submultiplicativity of `w'` at the level of `A`

`moves_ref`: D.7(i); MOVES ~2184-2190.

For `f = Σ_j B_j Φ̂^j`, `gg = Σ_k B''_k Φ̂^k` (Fact A developments), each product
`B_j·B''_k = Q_{jk}·Φ̂ + R_{jk}` re-develops with the remainder in slot `j+k` of weight
EXACTLY `w(B_j) + w(B''_k)` (Lemma DIV, `L3_DIV`) and the quotient in slot `j+k+1` of
`w'`-weight strictly deeper by `h' − e'·w(Φ̂) > 0` (I-aug).  Collecting slots and applying
the ultrametric finite-sum bound to the resulting `Φ̂`-development of `f·gg` gives
`w'(f) + w'(gg) ≤ w'(f·gg)` via the slot-minimum reading `hw'`.

Deps: `L3.DIV` (on disk, imported).  `L0_FactA_exists` and `L3_liftMonic` are on-disk
units used for development existence and the lift's monicity/degree.
-/

/-! ## SYN-M6 record (2026-07-30, C1 cluster)
Private `w_one'`/`w_neg'`/`wsum_ge'` deleted; call sites re-pointed at
`ResVal.w_neg` and `ult_sum_ge` (`Moves/ResVal.lean`) — `wsum_ge'` was the
weakest-assumption bare-(W, hult) copy on disk and is the VERBATIM source of the shared
`ult_sum_ge` (SYN-E0 §3 VAR-G). Publics `TRANSi_ge_core`/`L4_TRANSi` byte-identical. -/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Polynomial LeanUrat.Moves.ResVal

namespace LeanUrat.Moves

/-- **Lift-free core of `L4_TRANSi`** (submultiplicativity `w' f + w' g ≤ w'(f·g)`): all
the lift structure is used only through the abstract exact-remainder DIV hypothesis
`hDIVw`.  Reused at the SAME KEY (regrade instance) by HC1.V1. -/
theorem TRANSi_ge_core {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (Φhat : Polynomial ℤ_[p]) (hmon : Φhat.Monic) (hd1 : 1 ≤ Φhat.natDegree) (e' h' : ℕ) (w' : Polynomial ℤ_[p] → ℤ) (hw' : IsSlotMinWeight w' Φhat e' h' σ.w) (hiaug : IAug σ Φhat e' h') (hDIVw : ∀ (B B'' : Polynomial ℤ_[p]), B ≠ 0 → B'' ≠ 0 → B.degree < Φhat.degree → B''.degree < Φhat.degree → (B * B'') %ₘ Φhat ≠ 0 ∧ σ.w ((B * B'') %ₘ Φhat) = σ.w B + σ.w B'') (f gg : Polynomial ℤ_[p]) (hf : f ≠ 0) (hg : gg ≠ 0) (hfg : f * gg ≠ 0) : w' f + w' gg ≤ w' (f * gg) := by
  classical
  have hΦne : Φhat ≠ 0 := hmon.ne_zero
  have hbot : (⊥ : WithBot ℕ) < Φhat.degree :=
    bot_lt_iff_ne_bot.mpr (Polynomial.degree_ne_bot.mpr hΦne)
  -- ── (1) developments of f and gg (Fact A) and their slot lower bounds
  obtain ⟨B, N, hBdev⟩ := L0_FactA_exists Φhat hmon hd1 f
  obtain ⟨B'', M, hB''dev⟩ := L0_FactA_exists Φhat hmon hd1 gg
  have hbf := (hw' f B N hf hBdev).1
  have hbg := (hw' gg B'' M hg hB''dev).1
  -- ── (2) division facts for pairwise products: exact remainder weight (L3_DIV) …
  have hDIV : ∀ x : ℕ × ℕ, B x.1 ≠ 0 → B'' x.2 ≠ 0 →
      (B x.1 * B'' x.2) %ₘ Φhat ≠ 0 ∧
        σ.w ((B x.1 * B'' x.2) %ₘ Φhat) = σ.w (B x.1) + σ.w (B'' x.2) := by
    intro x hBj hBk
    exact hDIVw (B x.1) (B'' x.2) hBj hBk (hBdev.1 x.1) (hB''dev.1 x.2)
  -- ── … and the quotient weight lower bound (ultrametric on Q·Φ̂ = B·B″ − R_dev)
  have hQw : ∀ x : ℕ × ℕ, B x.1 ≠ 0 → B'' x.2 ≠ 0 → (B x.1 * B'' x.2) /ₘ Φhat ≠ 0 →
      σ.w (B x.1) + σ.w (B'' x.2) ≤ σ.w ((B x.1 * B'' x.2) /ₘ Φhat) + σ.w Φhat := by
    intro x hBj hBk hQne
    obtain ⟨hRne, hRw⟩ := hDIV x hBj hBk
    have hprodne : B x.1 * B'' x.2 ≠ 0 := mul_ne_zero hBj hBk
    have hQΦne : ((B x.1 * B'' x.2) /ₘ Φhat) * Φhat ≠ 0 := mul_ne_zero hQne hΦne
    have heq2 : ((B x.1 * B'' x.2) /ₘ Φhat) * Φhat =
        B x.1 * B'' x.2 + -((B x.1 * B'' x.2) %ₘ Φhat) := by
      linear_combination Polynomial.modByMonic_add_div (B x.1 * B'' x.2) Φhat
    have hsumne : B x.1 * B'' x.2 + -((B x.1 * B'' x.2) %ₘ Φhat) ≠ 0 := heq2 ▸ hQΦne
    have hult := σ.hwult _ _ hprodne (neg_ne_zero.mpr hRne) hsumne
    rw [← heq2, σ.hwmul _ _ hQne hΦne, w_neg σ _ hRne, hRw,
      σ.hwmul _ _ hBj hBk, min_self] at hult
    exact hult
  -- ── (3) the collected Φ̂-development of f·gg
  set C : ℕ → Polynomial ℤ_[p] := fun m =>
      (∑ x ∈ (Finset.range N ×ˢ Finset.range M).filter (fun x => x.1 + x.2 = m),
        (B x.1 * B'' x.2) %ₘ Φhat)
      + (∑ x ∈ (Finset.range N ×ˢ Finset.range M).filter (fun x => x.1 + x.2 + 1 = m),
        (B x.1 * B'' x.2) /ₘ Φhat) with hC
  have hmaps1 : ∀ x ∈ Finset.range N ×ˢ Finset.range M, x.1 + x.2 ∈ Finset.range (N + M) := by
    intro x hx
    simp only [Finset.mem_product, Finset.mem_range] at hx ⊢
    omega
  have hmaps2 : ∀ x ∈ Finset.range N ×ˢ Finset.range M,
      x.1 + x.2 + 1 ∈ Finset.range (N + M) := by
    intro x hx
    simp only [Finset.mem_product, Finset.mem_range] at hx ⊢
    omega
  have hCdev : IsDevelopment Φhat (f * gg) C (N + M) := by
    refine ⟨?_, ?_, ?_⟩
    · -- every slot is a coefficient: degree < deg Φ̂
      intro m
      simp only [hC]
      refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
      · refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
        rw [Finset.sup_lt_iff hbot]
        intro x hx
        exact Polynomial.degree_modByMonic_lt _ hmon
      · refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
        rw [Finset.sup_lt_iff hbot]
        intro x hx
        rcases eq_or_ne ((B x.1 * B'' x.2) /ₘ Φhat) 0 with h0 | h0
        · rw [h0, Polynomial.degree_zero]; exact hbot
        · have hprodne : B x.1 * B'' x.2 ≠ 0 := by
            intro hz; apply h0; rw [hz, Polynomial.zero_divByMonic]
          have hB1 : B x.1 ≠ 0 := fun h => hprodne (by rw [h, zero_mul])
          have hB2 : B'' x.2 ≠ 0 := fun h => hprodne (by rw [h, mul_zero])
          have hd1 : (B x.1).natDegree < Φhat.natDegree :=
            Polynomial.natDegree_lt_natDegree hB1 (hBdev.1 x.1)
          have hd2 : (B'' x.2).natDegree < Φhat.natDegree :=
            Polynomial.natDegree_lt_natDegree hB2 (hB''dev.1 x.2)
          have hqd := Polynomial.natDegree_divByMonic (B x.1 * B'' x.2) hmon
          have hprodd : (B x.1 * B'' x.2).natDegree ≤ (B x.1).natDegree + (B'' x.2).natDegree :=
            Polynomial.natDegree_mul_le
          have hlt : ((B x.1 * B'' x.2) /ₘ Φhat).natDegree < Φhat.natDegree := by omega
          rw [Polynomial.degree_eq_natDegree h0, Polynomial.degree_eq_natDegree hΦne]
          exact_mod_cast hlt
    · -- slots vanish from N+M on
      intro m hm
      simp only [hC]
      have h1 : (Finset.range N ×ˢ Finset.range M).filter (fun x => x.1 + x.2 = m) = ∅ := by
        apply Finset.filter_false_of_mem
        intro x hx
        simp only [Finset.mem_product, Finset.mem_range] at hx
        omega
      have h2 : (Finset.range N ×ˢ Finset.range M).filter (fun x => x.1 + x.2 + 1 = m) = ∅ := by
        apply Finset.filter_false_of_mem
        intro x hx
        simp only [Finset.mem_product, Finset.mem_range] at hx
        omega
      rw [h1, h2, Finset.sum_empty, Finset.sum_empty, add_zero]
    · -- the development sums to f·gg (double-sum re-indexing)
      have hthird : (∑ m ∈ Finset.range (N + M), C m * Φhat ^ m) = f * gg := by
        simp only [hC]
        calc
          ∑ m ∈ Finset.range (N + M),
              ((∑ x ∈ (Finset.range N ×ˢ Finset.range M).filter (fun x => x.1 + x.2 = m),
                  (B x.1 * B'' x.2) %ₘ Φhat)
                + ∑ x ∈ (Finset.range N ×ˢ Finset.range M).filter (fun x => x.1 + x.2 + 1 = m),
                    (B x.1 * B'' x.2) /ₘ Φhat) * Φhat ^ m
            = ∑ m ∈ Finset.range (N + M),
                ((∑ x ∈ (Finset.range N ×ˢ Finset.range M).filter (fun x => x.1 + x.2 = m),
                    ((B x.1 * B'' x.2) %ₘ Φhat) * Φhat ^ m)
                  + ∑ x ∈ (Finset.range N ×ˢ Finset.range M).filter (fun x => x.1 + x.2 + 1 = m),
                      ((B x.1 * B'' x.2) /ₘ Φhat) * Φhat ^ m) := by
              refine Finset.sum_congr rfl fun m _ => ?_
              rw [add_mul, Finset.sum_mul, Finset.sum_mul]
          _ = ∑ m ∈ Finset.range (N + M),
                ((∑ x ∈ (Finset.range N ×ˢ Finset.range M).filter (fun x => x.1 + x.2 = m),
                    ((B x.1 * B'' x.2) %ₘ Φhat) * Φhat ^ (x.1 + x.2))
                  + ∑ x ∈ (Finset.range N ×ˢ Finset.range M).filter (fun x => x.1 + x.2 + 1 = m),
                      ((B x.1 * B'' x.2) /ₘ Φhat) * Φhat ^ (x.1 + x.2 + 1)) := by
              refine Finset.sum_congr rfl fun m _ => ?_
              congr 1
              · refine Finset.sum_congr rfl fun x hx => ?_
                rw [(Finset.mem_filter.mp hx).2]
              · refine Finset.sum_congr rfl fun x hx => ?_
                rw [(Finset.mem_filter.mp hx).2]
          _ = (∑ m ∈ Finset.range (N + M),
                ∑ x ∈ (Finset.range N ×ˢ Finset.range M).filter (fun x => x.1 + x.2 = m),
                  ((B x.1 * B'' x.2) %ₘ Φhat) * Φhat ^ (x.1 + x.2))
              + ∑ m ∈ Finset.range (N + M),
                ∑ x ∈ (Finset.range N ×ˢ Finset.range M).filter (fun x => x.1 + x.2 + 1 = m),
                  ((B x.1 * B'' x.2) /ₘ Φhat) * Φhat ^ (x.1 + x.2 + 1) :=
              Finset.sum_add_distrib
          _ = (∑ x ∈ Finset.range N ×ˢ Finset.range M,
                ((B x.1 * B'' x.2) %ₘ Φhat) * Φhat ^ (x.1 + x.2))
              + ∑ x ∈ Finset.range N ×ˢ Finset.range M,
                ((B x.1 * B'' x.2) /ₘ Φhat) * Φhat ^ (x.1 + x.2 + 1) := by
              congr 1
              · exact Finset.sum_fiberwise_of_maps_to hmaps1 _
              · exact Finset.sum_fiberwise_of_maps_to hmaps2 _
          _ = ∑ x ∈ Finset.range N ×ˢ Finset.range M,
                (((B x.1 * B'' x.2) %ₘ Φhat) * Φhat ^ (x.1 + x.2)
                  + ((B x.1 * B'' x.2) /ₘ Φhat) * Φhat ^ (x.1 + x.2 + 1)) :=
              Finset.sum_add_distrib.symm
          _ = ∑ x ∈ Finset.range N ×ˢ Finset.range M,
                (B x.1 * B'' x.2) * Φhat ^ (x.1 + x.2) := by
              refine Finset.sum_congr rfl fun x _ => ?_
              linear_combination
                (Φhat ^ (x.1 + x.2)) * Polynomial.modByMonic_add_div (B x.1 * B'' x.2) Φhat
          _ = ∑ x ∈ Finset.range N ×ˢ Finset.range M,
                (B x.1 * Φhat ^ x.1) * (B'' x.2 * Φhat ^ x.2) := by
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [pow_add]; ring
          _ = f * gg := by
              rw [hBdev.2.2, hB''dev.2.2, Finset.sum_mul]
              rw [Finset.sum_product]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.mul_sum]
      exact hthird.symm
  -- ── (4) the per-slot bound: every nonzero slot of C sits at w'-weight ≥ w'(f) + w'(gg)
  have hultW : ∀ f₁ g₁ : Polynomial ℤ_[p], f₁ ≠ 0 → g₁ ≠ 0 → f₁ + g₁ ≠ 0 →
      min ((e' : ℤ) * σ.w f₁) ((e' : ℤ) * σ.w g₁) ≤ (e' : ℤ) * σ.w (f₁ + g₁) := by
    intro f₁ g₁ h1 h2 h3
    rw [← mul_min_of_nonneg _ _ (Int.natCast_nonneg e')]
    exact mul_le_mul_of_nonneg_left (σ.hwult f₁ g₁ h1 h2 h3) (Int.natCast_nonneg e')
  have hslot : ∀ m : ℕ, C m ≠ 0 →
      w' f + w' gg ≤ (e' : ℤ) * σ.w (C m) + (m : ℤ) * (h' : ℤ) := by
    intro m hCm
    -- rewrite C m as a single sum over the product index set
    have hsingle : C m = ∑ x ∈ Finset.range N ×ˢ Finset.range M,
        ((if x.1 + x.2 = m then (B x.1 * B'' x.2) %ₘ Φhat else 0)
          + (if x.1 + x.2 + 1 = m then (B x.1 * B'' x.2) /ₘ Φhat else 0)) := by
      simp only [hC]
      rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    have hper : ∀ x ∈ Finset.range N ×ˢ Finset.range M,
        ((if x.1 + x.2 = m then (B x.1 * B'' x.2) %ₘ Φhat else 0)
          + (if x.1 + x.2 + 1 = m then (B x.1 * B'' x.2) /ₘ Φhat else 0)) ≠ 0 →
        w' f + w' gg - (m : ℤ) * (h' : ℤ) ≤ (e' : ℤ) * σ.w
          ((if x.1 + x.2 = m then (B x.1 * B'' x.2) %ₘ Φhat else 0)
            + (if x.1 + x.2 + 1 = m then (B x.1 * B'' x.2) /ₘ Φhat else 0)) := by
      intro x hx hax
      obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hx
      rw [Finset.mem_range] at hx1 hx2
      by_cases h1 : x.1 + x.2 = m
      · -- remainder slot j+k = m: exact weight w(B_j) + w(B″_k) (Lemma DIV)
        have h2 : ¬(x.1 + x.2 + 1 = m) := by omega
        rw [if_pos h1, if_neg h2, add_zero] at hax ⊢
        have hBj : B x.1 ≠ 0 := by
          intro h0; apply hax; rw [h0, zero_mul, Polynomial.zero_modByMonic]
        have hBk : B'' x.2 ≠ 0 := by
          intro h0; apply hax; rw [h0, mul_zero, Polynomial.zero_modByMonic]
        obtain ⟨hRne, hRw⟩ := hDIV x hBj hBk
        have b1 := hbf x.1 hx1 hBj
        have b2 := hbg x.2 hx2 hBk
        rw [hRw, mul_add, ← h1]
        push_cast
        linarith
      · by_cases h2 : x.1 + x.2 + 1 = m
        · -- quotient slot j+k+1 = m: strictly deeper by h' − e'·w(Φ̂) > 0 (I-aug)
          rw [if_neg h1, if_pos h2, zero_add] at hax ⊢
          have hBj : B x.1 ≠ 0 := by
            intro h0; apply hax; rw [h0, zero_mul, Polynomial.zero_divByMonic]
          have hBk : B'' x.2 ≠ 0 := by
            intro h0; apply hax; rw [h0, mul_zero, Polynomial.zero_divByMonic]
          have hq := hQw x hBj hBk hax
          have b1 := hbf x.1 hx1 hBj
          have b2 := hbg x.2 hx2 hBk
          have hIA : (h' : ℤ) > (e' : ℤ) * σ.w Φhat := hiaug
          have hmul := mul_le_mul_of_nonneg_left hq (Int.natCast_nonneg e')
          rw [mul_add, mul_add] at hmul
          rw [← h2]
          push_cast
          linarith
        · rw [if_neg h1, if_neg h2, add_zero] at hax
          exact absurd rfl hax
    have hkey : w' f + w' gg - (m : ℤ) * (h' : ℤ) ≤ (e' : ℤ) * σ.w (C m) := by
      rw [hsingle] at hCm ⊢
      exact ult_sum_ge (fun q => (e' : ℤ) * σ.w q) hultW _ _ _ hper hCm
    linarith
  -- ── (5) conclude via the attained minimum of the C-development of f·gg
  obtain ⟨m₀, hm₀lt, hCne, heq⟩ := (hw' (f * gg) C (N + M) hfg hCdev).2
  calc w' f + w' gg ≤ (e' : ℤ) * σ.w (C m₀) + (m₀ : ℤ) * (h' : ℤ) := hslot m₀ hCne
    _ = w' (f * gg) := heq.symm

/-- **Lemma TRANS(i)** — submultiplicativity of the child weight (statement unchanged;
now a thin wrapper over `TRANSi_ge_core`, feeding it the DIV fact from `L3_DIV`). -/
theorem L4_TRANSi {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (zbar : Fˣ) (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0) (e' h' : ℕ) (w' : Polynomial ℤ_[p] → ℤ) (hw' : IsSlotMinWeight w' Φhat e' h' σ.w) (hiaug : IAug σ Φhat e' h') (f gg : Polynomial ℤ_[p]) (hf : f ≠ 0) (hg : gg ≠ 0) (hfg : f * gg ≠ 0) : w' f + w' gg ≤ w' (f * gg) := by
  classical
  have hψmon : ψ.Monic := hlift.1
  have hψdeg : ψ.natDegree = g := hlift.2.1
  have hg1 : 1 ≤ g := by
    by_contra hcon
    have h0 : ψ.natDegree = 0 := by rw [hψdeg]; omega
    have hψ1 : ψ = 1 := (Polynomial.Monic.natDegree_eq_zero hψmon).mp h0
    exact hψ.not_isUnit (hψ1 ▸ isUnit_one)
  obtain ⟨hΦmon, hΦdeg⟩ := L3_liftMonic σ ψ g hg1 Φhat hlift
  have hdegpos : 0 < σ.e * g * σ.Φ.natDegree := Nat.mul_pos (Nat.mul_pos σ.he hg1) σ.hdeg
  have hd1 : 1 ≤ Φhat.natDegree := by rw [hΦdeg]; exact hdegpos
  have hDIVw : ∀ (B B'' : Polynomial ℤ_[p]), B ≠ 0 → B'' ≠ 0 →
      B.degree < Φhat.degree → B''.degree < Φhat.degree →
      (B * B'') %ₘ Φhat ≠ 0 ∧ σ.w ((B * B'') %ₘ Φhat) = σ.w B + σ.w B'' := by
    intro B B'' hB hB'' hBd hB''d
    have hBd' : B.natDegree < σ.e * g * σ.Φ.natDegree := by
      rw [← hΦdeg]; exact Polynomial.natDegree_lt_natDegree hB hBd
    have hB''d' : B''.natDegree < σ.e * g * σ.Φ.natDegree := by
      rw [← hΦdeg]; exact Polynomial.natDegree_lt_natDegree hB'' hB''d
    have hRd' : ((B * B'') %ₘ Φhat).natDegree < σ.e * g * σ.Φ.natDegree := by
      by_cases hz : (B * B'') %ₘ Φhat = 0
      · rw [hz]; simpa using hdegpos
      · rw [← hΦdeg]
        exact Polynomial.natDegree_lt_natDegree hz (Polynomial.degree_modByMonic_lt _ hΦmon)
    have hdiv : B * B'' = ((B * B'') /ₘ Φhat) * Φhat + (B * B'') %ₘ Φhat := by
      linear_combination -Polynomial.modByMonic_add_div (B * B'') Φhat
    have hd := L3_DIV σ ψ g hψdeg hψ hψz Φhat hlift zbar hzbar B B'' hB hB'' hBd' hB''d'
      ((B * B'') %ₘ Φhat) ((B * B'') /ₘ Φhat) hdiv hRd'
    exact ⟨hd.1, hd.2.1⟩
  exact TRANSi_ge_core σ Φhat hΦmon hd1 e' h' w' hw' hiaug hDIVw f gg hf hg hfg

end LeanUrat.Moves
