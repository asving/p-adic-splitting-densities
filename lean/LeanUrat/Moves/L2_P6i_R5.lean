/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL
import LeanUrat.Moves.L2_slotDecomp_R4
import LeanUrat.Moves.L2_strideRule
import LeanUrat.Moves.L0_GRb

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

/- DEPRECATED — superseded by `L2_P6i_R5_final.lean` (sorry-free, byte-exact fence). Retained
only for the round-5 provenance record; NOT on any capstone path. Do not import. -/

namespace LeanUrat.Moves

open Polynomial

/-- **L2.P6i** (D.3(e)(i) per-piece: R_δ additive, F_Q-linear, injective; image = additive span of slot images).

AUDIT #5 SCOPE (FLAGGED-OK, conditional/local): proved from the ABSTRACT Stage residual
laws + StageCore fields ONLY; it does NOT certify the deferred graded-localization
provenance (see lean/notes/MOVES_LEAN_SEMAUDIT5_2026-07-26.md §6). -/
theorem L2_P6i {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (hcore : StageCore σ) (γ : ℤ) : (∀ f f', f ≠ 0 → f' ≠ 0 → σ.w f = γ → σ.w f' = γ → σ.R f = σ.R f' → f - f' = 0 ∨ γ < σ.w (f - f')) ∧ (∀ f f', f ≠ 0 → f' ≠ 0 → f + f' ≠ 0 → σ.w f = γ → σ.w f' = γ → σ.w (f + f') = γ → σ.R (f + f') = σ.R f + σ.R f') ∧ (∀ (û : Polynomial ℤ_[p]) (c : ↥σ.FQ), û ≠ 0 → c ≠ 0 → inC σ.Φ û → σ.w û = 0 → σ.R û = LaurentPolynomial.C (Subfield.inclusion σ.hFQ_le c) * LaurentPolynomial.T (0 : ℤ) → ∀ f, f ≠ 0 → σ.w f = γ → σ.w (û * f) = γ ∧ σ.R (û * f) = LaurentPolynomial.C (Subfield.inclusion σ.hFQ_le c) * σ.R f) ∧ (∀ f, f ≠ 0 → σ.w f = γ → σ.R f ∈ AddSubgroup.closure (σ.slotImages γ)) ∧ (∀ x ∈ AddSubgroup.closure (σ.slotImages γ), x ≠ 0 → ∃ f, f ≠ 0 ∧ σ.w f = γ ∧ σ.R f = x) := by
  -- helper: `w` is even (`w (-g) = w g`), from `w 1 = 0` and `w (C (-1)) = 0`
  have hw1 : σ.w (1 : Polynomial ℤ_[p]) = 0 := by
    have hw := σ.hwmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at hw; omega
  have hc0 : (Polynomial.C (-1 : ℤ_[p])) ≠ 0 := by simp
  have hsq : Polynomial.C (-1 : ℤ_[p]) * Polynomial.C (-1) = 1 := by
    rw [← Polynomial.C_mul, show ((-1 : ℤ_[p]) * (-1)) = 1 from by ring, Polynomial.C_1]
  have hcneg1 : σ.w (Polynomial.C (-1 : ℤ_[p])) = 0 := by
    have hw := σ.hwmul (Polynomial.C (-1)) (Polynomial.C (-1)) hc0 hc0
    rw [hsq, hw1] at hw; omega
  have wneg : ∀ g : Polynomial ℤ_[p], g ≠ 0 → σ.w (-g) = σ.w g := by
    intro g hg
    have hnegC : Polynomial.C (-1 : ℤ_[p]) * g = -g := by
      rw [Polynomial.C_neg, Polynomial.C_1, neg_one_mul]
    have hw := σ.hwmul (Polynomial.C (-1)) g hc0 hg
    rw [hnegC, hcneg1, zero_add] at hw; exact hw
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (1) injectivity on the graded piece
    intro f f' hf hf' hwf hwf' hR
    rcases eq_or_ne (f - f') 0 with h0 | hne
    · exact Or.inl h0
    · right
      have hsum : (f - f') + f' = f := by ring
      rcases lt_trichotomy (σ.w (f - f')) γ with hlt | heq | hgt
      · exfalso
        have hs := hcore.w_strict (f - f') f' hne hf' (by rw [hwf']; exact hlt)
        rw [hsum, hwf] at hs; omega
      · exfalso
        have hadd := σ.hRadd (f - f') f' hne hf' (by rw [hsum]; exact hf)
          (by rw [hwf']; exact heq) (by rw [hsum, hwf, heq])
        rw [hsum, hR] at hadd
        have hz : σ.R (f - f') = 0 :=
          add_right_cancel (b := σ.R f') (by rw [zero_add]; exact hadd.symm)
        exact σ.hRne (f - f') hne hz
      · exact hgt
  · -- (2) per-piece additivity
    intro f f' hf hf' hs hwf hwf' hws
    exact σ.hRadd f f' hf hf' hs (by rw [hwf, hwf']) (by rw [hws, hwf])
  · -- (3) F_Q-linearity: a weight-0 unit lift preserves the piece and scales R
    intro u c hu _ _ hwu hRu f hf hwf
    refine ⟨?_, ?_⟩
    · rw [σ.hwmul u f hu hf, hwu, hwf, zero_add]
    · rw [σ.hRmul u f hu hf, hRu, LaurentPolynomial.T_zero, mul_one]
  · -- (4) image ⊆ additive span of the slot images (needs Φ-adic development + slot drop)
    sorry
  · -- (5) additive span ⊆ image: the image ∪ {0} is a subgroup containing the slot images
    intro x hx hxne
    let S : AddSubgroup (LaurentPolynomial ↥σ.K) :=
    { carrier := {y | y = 0 ∨ ∃ f : Polynomial ℤ_[p], f ≠ 0 ∧ σ.w f = γ ∧ σ.R f = y}
      zero_mem' := Or.inl rfl
      add_mem' := by
        rintro a b (rfl | ⟨f, hf, hwf, rfl⟩) hb
        · rw [zero_add]; exact hb
        · rcases hb with rfl | ⟨g, hg, hwg, rfl⟩
          · rw [add_zero]; exact Or.inr ⟨f, hf, hwf, rfl⟩
          · rcases eq_or_ne (f + g) 0 with hfg | hfg
            · left
              have hgf : g = -f := by
                rw [eq_neg_iff_add_eq_zero, add_comm]; exact hfg
              rw [hgf, hcore.R_neg]; ring
            · have hge : γ ≤ σ.w (f + g) := by
                have hh := σ.hwult f g hf hg hfg
                rw [hwf, hwg, min_self] at hh; exact hh
              rcases eq_or_lt_of_le hge with heq | hlt
              · exact Or.inr ⟨f + g, hfg, heq.symm,
                  σ.hRadd f g hf hg hfg (by rw [hwf, hwg]) (by rw [hwf, ← heq])⟩
              · exact Or.inl
                  (hcore.w_jump f g hf hg hfg (by rw [hwf, hwg]) (by rw [hwf]; exact hlt))
      neg_mem' := by
        rintro a (rfl | ⟨f, hf, hwf, rfl⟩)
        · rw [neg_zero]; exact Or.inl rfl
        · exact Or.inr ⟨-f, neg_ne_zero.mpr hf, by rw [wneg f hf]; exact hwf, hcore.R_neg f⟩ }
    have hsub : σ.slotImages γ ⊆ (S : Set (LaurentPolynomial ↥σ.K)) := by
      rintro y ⟨B, j, hB, _, hwj, rfl⟩
      exact Or.inr ⟨B * σ.Φ ^ j, mul_ne_zero hB (pow_ne_zero j σ.hmonic.ne_zero), hwj, rfl⟩
    have hmem : x = 0 ∨ ∃ f : Polynomial ℤ_[p], f ≠ 0 ∧ σ.w f = γ ∧ σ.R f = x :=
      (AddSubgroup.closure_le S).mpr hsub hx
    rcases hmem with h0 | h
    · exact absurd h0 hxne
    · exact h
