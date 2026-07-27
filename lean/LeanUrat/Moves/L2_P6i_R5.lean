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
import LeanUrat.Moves.L0_FactA_exists
import LeanUrat.Moves.L0_FactB_unique
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

/-- `w 1 = 0` (from `hwmul` at `1·1`). -/
private lemma w_one_aux {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) : σ.w (1 : Polynomial ℤ_[p]) = 0 := by
  have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h; omega

/-- `w (Φ^j) = j·w Φ`. -/
private lemma w_keyPow {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (j : ℕ) : σ.w (σ.Φ ^ j) = (j : ℤ) * σ.w σ.Φ := by
  have hΦ : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  induction j with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul]; exact w_one_aux σ
  | succ n ih =>
    rw [pow_succ, σ.hwmul (σ.Φ ^ n) σ.Φ (pow_ne_zero n hΦ) hΦ, ih]
    push_cast; ring

/-- `w (B·Φ^j) = w B + j·w Φ` for `B ≠ 0`. -/
private lemma w_slot_aux {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (B : Polynomial ℤ_[p]) (j : ℕ) (hB : B ≠ 0) :
    σ.w (B * σ.Φ ^ j) = σ.w B + (j : ℤ) * σ.w σ.Φ := by
  rw [σ.hwmul B (σ.Φ ^ j) hB (pow_ne_zero j σ.hmonic.ne_zero), w_keyPow]

/-- **Clause (4) engine — image ⊆ additive span of the slot images.** Develop `f` Φ-adically
(Fact A); split the development into the K1-minimizing slots (all at total weight `γ`) and the
strictly-higher rest. The minimizing part is nonzero (Fact B uniqueness vs. the attained
minimum witness), sits at weight `γ` (K1 again), and `R` decomposes across its slots
(StageCore's S3 DECOMPOSITION); the rest has weight `> γ` (K1 on the rest), so `hRlt` drops
it. Each slot residual is literally a `slotImages γ` element. -/
private lemma image_in_span {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hcore : StageCore σ) (γ : ℤ) (f : Polynomial ℤ_[p])
    (hf : f ≠ 0) (hwf : σ.w f = γ) :
    σ.R f ∈ AddSubgroup.closure (σ.slotImages γ) := by
  obtain ⟨B, N, hdev⟩ := L0_FactA_exists σ.Φ σ.hmonic σ.hdeg f
  obtain ⟨hBdeg, hBvan, hBsum⟩ := hdev
  obtain ⟨hmin, j₀, hj₀N, hBj₀, hγ₀⟩ := σ.hK1 f B N hf ⟨hBdeg, hBvan, hBsum⟩
  replace hmin : ∀ j, j < N → B j ≠ 0 → σ.w f ≤ σ.w (B j) + (j : ℤ) * σ.w σ.Φ := hmin
  replace hγ₀ : σ.w f = σ.w (B j₀) + (j₀ : ℤ) * σ.w σ.Φ := hγ₀
  rw [hwf] at hmin hγ₀
  have h0deg : (0 : Polynomial ℤ_[p]).degree < σ.Φ.degree := by
    rw [Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.mpr (fun hb => σ.hmonic.ne_zero (Polynomial.degree_eq_bot.mp hb))
  -- the minimizing-slot truncation
  set B' : ℕ → Polynomial ℤ_[p] :=
    fun j => if σ.w (B j) + (j : ℤ) * σ.w σ.Φ = γ then B j else 0 with hB'def
  have hB'cases : ∀ j, B' j = B j ∨ B' j = 0 := by
    intro j
    by_cases hc : σ.w (B j) + (j : ℤ) * σ.w σ.Φ = γ
    · exact Or.inl (by simp only [hB'def]; exact if_pos hc)
    · exact Or.inr (by simp only [hB'def]; exact if_neg hc)
  have hB'ne : ∀ j, B' j ≠ 0 → B' j = B j ∧ σ.w (B j) + (j : ℤ) * σ.w σ.Φ = γ := by
    intro j hj
    by_cases hc : σ.w (B j) + (j : ℤ) * σ.w σ.Φ = γ
    · exact ⟨by simp only [hB'def]; exact if_pos hc, hc⟩
    · exact absurd (by simp only [hB'def]; exact if_neg hc) hj
  have hB'deg : ∀ j, (B' j).degree < σ.Φ.degree := by
    intro j
    rcases hB'cases j with h | h
    · rw [h]; exact hBdeg j
    · rw [h]; exact h0deg
  have hB'van : ∀ j, N ≤ j → B' j = 0 := by
    intro j hj
    rcases hB'cases j with h | h
    · rw [h]; exact hBvan j hj
    · exact h
  have hdevmin : IsDevelopment σ.Φ (∑ j ∈ Finset.range N, B' j * σ.Φ ^ j) B' N :=
    ⟨hB'deg, hB'van, rfl⟩
  -- the minimizing part is nonzero (Fact B uniqueness against the zero development)
  have hfmin_ne : (∑ j ∈ Finset.range N, B' j * σ.Φ ^ j) ≠ 0 := by
    intro h0
    have hzdev : IsDevelopment σ.Φ (0 : Polynomial ℤ_[p]) (fun _ => (0 : Polynomial ℤ_[p])) 0 :=
      ⟨fun _ => h0deg, fun _ _ => rfl, by simp⟩
    have hdev0 : IsDevelopment σ.Φ (0 : Polynomial ℤ_[p]) B' N := by
      rw [← h0]; exact hdevmin
    have hu := L0_FactB_unique σ.Φ σ.hmonic 0 hdev0 hzdev j₀
    have hB'j₀ : B' j₀ = B j₀ := by simp only [hB'def]; exact if_pos hγ₀.symm
    rw [hB'j₀] at hu
    exact hBj₀ hu
  -- every active slot of the minimizing part is at total weight γ
  have hwslot' : ∀ j, j < N → B' j ≠ 0 → σ.w (B' j * σ.Φ ^ j) = γ := by
    intro j hj hne
    obtain ⟨heq, hc⟩ := hB'ne j hne
    rw [heq] at hne ⊢
    rw [w_slot_aux σ (B j) j hne]
    exact hc
  -- the minimizing part sits at weight γ (K1 on it: the attained witness slot has value γ)
  have hwfmin : σ.w (∑ j ∈ Finset.range N, B' j * σ.Φ ^ j) = γ := by
    obtain ⟨_, j₁, hj₁N, hB'j₁, hwmin⟩ := σ.hK1 _ B' N hfmin_ne hdevmin
    replace hwmin : σ.w (∑ j ∈ Finset.range N, B' j * σ.Φ ^ j)
        = σ.w (B' j₁) + (j₁ : ℤ) * σ.w σ.Φ := hwmin
    obtain ⟨heq, hc⟩ := hB'ne j₁ hB'j₁
    rw [hwmin, heq]
    exact hc
  -- S3 DECOMPOSITION across the minimizing slots
  have hRdec : σ.R (∑ j ∈ Finset.range N, B' j * σ.Φ ^ j)
      = ∑ j ∈ Finset.range N, σ.R (B' j * σ.Φ ^ j) :=
    hcore.slot.1 B' N γ hB'van hwslot' hfmin_ne hwfmin
  -- f = (minimizing part) + (rest)
  have hsplit : f = (∑ j ∈ Finset.range N, B' j * σ.Φ ^ j)
      + ∑ j ∈ Finset.range N, (B j - B' j) * σ.Φ ^ j := by
    calc f = ∑ j ∈ Finset.range N, B j * σ.Φ ^ j := hBsum
    _ = ∑ j ∈ Finset.range N, (B' j * σ.Φ ^ j + (B j - B' j) * σ.Φ ^ j) :=
        Finset.sum_congr rfl (fun j _ => by ring)
    _ = _ := Finset.sum_add_distrib
  -- R f = R (minimizing part): the rest is 0 or strictly heavier (K1 on the rest + hRlt)
  have hRf : σ.R f = σ.R (∑ j ∈ Finset.range N, B' j * σ.Φ ^ j) := by
    rcases eq_or_ne (∑ j ∈ Finset.range N, (B j - B' j) * σ.Φ ^ j) 0 with hr0 | hrne
    · rw [hsplit, hr0, add_zero]
    · have hdevrest : IsDevelopment σ.Φ (∑ j ∈ Finset.range N, (B j - B' j) * σ.Φ ^ j)
          (fun j => B j - B' j) N :=
        ⟨fun j => lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt (hBdeg j) (hB'deg j)),
         fun j hj => by show B j - B' j = 0; rw [hBvan j hj, hB'van j hj]; exact sub_zero 0,
         rfl⟩
      obtain ⟨_, j₁, hj₁N, hne₁, hwrest⟩ := σ.hK1 _ (fun j => B j - B' j) N hrne hdevrest
      replace hne₁ : B j₁ - B' j₁ ≠ 0 := hne₁
      replace hwrest : σ.w (∑ j ∈ Finset.range N, (B j - B' j) * σ.Φ ^ j)
          = σ.w (B j₁ - B' j₁) + (j₁ : ℤ) * σ.w σ.Φ := hwrest
      have hkey : γ < σ.w (∑ j ∈ Finset.range N, (B j - B' j) * σ.Φ ^ j) := by
        by_cases hc : σ.w (B j₁) + (j₁ : ℤ) * σ.w σ.Φ = γ
        · exfalso
          have hB'e : B' j₁ = B j₁ := by simp only [hB'def]; exact if_pos hc
          rw [hB'e, sub_self] at hne₁
          exact hne₁ rfl
        · have hB'0 : B' j₁ = 0 := by simp only [hB'def]; exact if_neg hc
          rw [hB'0, sub_zero] at hne₁ hwrest
          rw [hwrest]
          exact lt_of_le_of_ne (hmin j₁ hj₁N hne₁) (Ne.symm hc)
      rw [hsplit]
      exact σ.hRlt _ _ hfmin_ne hrne (by rw [← hsplit]; exact hf) (by rw [hwfmin]; exact hkey)
  -- conclude: each slot residual is a slot image
  rw [hRf, hRdec]
  refine AddSubgroup.sum_mem _ (fun j hj => ?_)
  rcases eq_or_ne (B' j) 0 with h0 | hne
  · rw [h0, zero_mul, σ.hR0]
    exact zero_mem _
  · exact AddSubgroup.subset_closure
      ⟨B' j, j, hne, hB'deg j, hwslot' j (Finset.mem_range.mp hj) hne, rfl⟩

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
  · -- (4) image ⊆ additive span of the slot images (Fact A development + K1 split + S3)
    intro f hf hwf
    exact image_in_span σ hcore γ f hf hwf
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
