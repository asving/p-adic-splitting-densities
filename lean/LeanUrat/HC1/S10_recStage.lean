/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsSpine
import LeanUrat.Moves.L0_FactA_exists
import LeanUrat.Moves.L0_FactB_unique
import LeanUrat.Moves.L2_slotDecomp_R4
import LeanUrat.Moves.L5_recSpecies_R4
import LeanUrat.Moves.L5_recSubst_R4
import LeanUrat.Moves.L5_recLiftIndep_R4
import LeanUrat.Moves.L5_recRSland_R4
import LeanUrat.Moves.L5_recVV_R4

/-!
# HC1.S10_recStage — the D.10/TRANS-RS capstone

moves_ref: MOVES 2661–2670 (TRANS-RS, S1–S6 item by item). deps: S13; Moves
`L5_recSpecies_R4`, `L5_recSubst_R4`, `L5_recLiftIndep_R4`, `L5_recRSland_R4`,
`L5_recVV_R4` (clean). The honest replacement for MovesGr's `L5_recTRANSRS`,
consuming/producing the RECORDING relation `IsRecenteringCore` per the fence
(D4(iii)). The D.9-supplied lift existence (via S13) rides as `hlift`. sketch:
Φ′ := Φ − tt; same w/wPrev/K/FQ/weightSet fields; K1(Φ′/v) = the g = 1 instance of
D.5 (L5_recVV); digits unchanged. difficulty: HARD. hyp: `hlift` (S13-supplied).

## Construction (this file)

The recentered stage is `σ` with ONLY two fields changed: the key `Φ′ := Φ − tt`
and the residual map `R′ := (z ↦ z + c̃) ∘ R` — the D.10 change of frame. The
substitution is well-defined because at an `e = 1` stage EVERY residual is a
genuine polynomial in `z` (`res_poly` below: K1 + the graded trichotomy reduce
`R f` to the minimizing-slot sum `Σ C(cⱼ)·zʲ`, positions `≥ 0` since `t = 0`),
and on polynomials `z ↦ z + c̃` is a ring automorphism, so every stage law
transports. `w(Φ′) = w(Φ)` and `K1` at `Φ′` are `L5_recVV` (the D.5 `g = 1`
instance); `R(Φ′) = z − c̃` pins `R′(Φ′) = z`; coefficient residuals are
position-0 constants, hence substitution-FIXED — digits unchanged, and the
`IsRecenteringCore` records plus `StageCoreL` transport field by field.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

section Helpers

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- `R 1 = 1`. -/
private lemma R_one (σ : Stage p F) : σ.R 1 = 1 := by
  have h := σ.hRmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  exact (mul_left_cancel₀ (σ.hRne 1 one_ne_zero) (by rw [mul_one]; exact h)).symm

/-- `R (g^j) = (R g)^j` for `g ≠ 0`. -/
private lemma R_pow (σ : Stage p F) (g : Polynomial ℤ_[p]) (hg : g ≠ 0) (j : ℕ) :
    σ.R (g ^ j) = (σ.R g) ^ j := by
  induction j with
  | zero => rw [pow_zero, pow_zero, R_one]
  | succ n ih => rw [pow_succ, σ.hRmul (g ^ n) g (pow_ne_zero n hg) hg, ih, pow_succ]

/-- Any multiplicative integer valuation sends `1` to `0`. -/
private lemma val_one (w : Polynomial ℤ_[p] → ℤ)
    (hmul : ∀ f g : Polynomial ℤ_[p], f ≠ 0 → g ≠ 0 → w (f * g) = w f + w g) : w 1 = 0 := by
  have h := hmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h; linarith

/-- Any multiplicative integer valuation is invariant under negation. -/
private lemma val_neg (w : Polynomial ℤ_[p] → ℤ)
    (hmul : ∀ f g : Polynomial ℤ_[p], f ≠ 0 → g ≠ 0 → w (f * g) = w f + w g)
    (f : Polynomial ℤ_[p]) (hf : f ≠ 0) : w (-f) = w f := by
  have hn1 : (-1 : Polynomial ℤ_[p]) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have key := hmul (-1) (-1) hn1 hn1
  rw [neg_one_mul, neg_neg, val_one w hmul] at key
  have hw1 : w (-1 : Polynomial ℤ_[p]) = 0 := by linarith
  have h2 := hmul (-1) f hn1 hf
  rw [neg_one_mul, hw1, zero_add] at h2; exact h2

/-- `w (g^j) = j·(w g)` for `g ≠ 0`. -/
private lemma w_pow (σ : Stage p F) (g : Polynomial ℤ_[p]) (hg : g ≠ 0) (j : ℕ) :
    σ.w (g ^ j) = (j : ℤ) * σ.w g := by
  induction j with
  | zero => rw [pow_zero, val_one σ.w σ.hwmul]; simp
  | succ n ih =>
    rw [pow_succ, σ.hwmul (g ^ n) g (pow_ne_zero n hg) hg, ih]
    push_cast; ring

/-- `(T s)^j = T (j·s)` in any Laurent ring. -/
private lemma T_pow_s {R : Type*} [CommRing R] (s : ℤ) (j : ℕ) :
    (LaurentPolynomial.T s : LaurentPolynomial R) ^ j = LaurentPolynomial.T ((j : ℤ) * s) := by
  induction j with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, ← LaurentPolynomial.T_add]
    congr 1; push_cast; ring

/-- A list of nonzero polynomials has nonzero product. -/
private lemma list_prod_ne_zero (l : List (Polynomial ℤ_[p])) (h : ∀ u ∈ l, u ≠ 0) :
    l.prod ≠ 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.prod_cons]
    exact mul_ne_zero (h a List.mem_cons_self) (ih fun u hu => h u (List.mem_cons_of_mem a hu))

/-- Monomial units of `K[z^{±1}]` have unique scalar and position (nonzero scalar). -/
private lemma monomial_unique {K : Type*} [Field K] {c d : K} {k j : ℤ} (hd : d ≠ 0)
    (h : LaurentPolynomial.C c * LaurentPolynomial.T k
        = LaurentPolynomial.C d * LaurentPolynomial.T j) : c = d ∧ k = j := by
  rw [← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T] at h
  rcases (Finsupp.single_eq_single_iff _ _ _ _).mp h with ⟨hk, hc⟩ | ⟨_, hd'⟩
  · exact ⟨hc, hk⟩
  · exact absurd hd' hd

/-- A nonempty subfamily of the slots of a development sums to a nonzero element (Fact B). -/
private lemma subsum_ne_zero {R : Type*} [CommRing R] [Nontrivial R] (Φ : Polynomial R)
    (hΦ : Φ.Monic) (B : ℕ → Polynomial R) (hdeg : ∀ j, (B j).degree < Φ.degree)
    (S : Finset ℕ) (j₀ : ℕ) (hj₀ : j₀ ∈ S) (hB₀ : B j₀ ≠ 0) :
    (∑ j ∈ S, B j * Φ ^ j) ≠ 0 := by
  classical
  intro hzero
  have hbot : (⊥ : WithBot ℕ) < Φ.degree :=
    bot_lt_iff_ne_bot.mpr (fun h => hΦ.ne_zero (Polynomial.degree_eq_bot.mp h))
  have hSsub : S ⊆ Finset.range (S.sup id + 1) := fun j hj =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hj))
  have hdev : IsDevelopment Φ 0 (fun j => if j ∈ S then B j else 0) (S.sup id + 1) := by
    refine ⟨fun j => ?_, fun j hj => ?_, ?_⟩
    · dsimp only; split_ifs
      · exact hdeg j
      · rw [Polynomial.degree_zero]; exact hbot
    · dsimp only; rw [if_neg]
      intro hjS
      have h := Finset.le_sup (f := id) hjS
      simp only [id] at h
      omega
    · simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hSsub]
      exact hzero.symm
  have hdev0 : IsDevelopment Φ (0 : Polynomial R) (fun _ => 0) 0 :=
    ⟨fun j => by rw [Polynomial.degree_zero]; exact hbot, fun _ _ => rfl, by simp⟩
  have h := L0_FactB_unique Φ hΦ 0 hdev hdev0 j₀
  simp only [if_pos hj₀] at h
  exact hB₀ h

/-- Generalized ultrametric bound over a finset with nonvanishing subsums. -/
private lemma w_sum_ge (σ : Stage p F) (T : ℕ → Polynomial ℤ_[p]) (γ' : ℤ) (S : Finset ℕ)
    (h0 : ∀ j ∈ S, T j ≠ 0) (hw : ∀ j ∈ S, γ' ≤ σ.w (T j))
    (hsub : ∀ S' ⊆ S, S'.Nonempty → (∑ j ∈ S', T j) ≠ 0) (hne : S.Nonempty) :
    γ' ≤ σ.w (∑ j ∈ S, T j) := by
  classical
  revert h0 hw hsub hne
  refine Finset.induction_on S ?_ ?_
  · intro _ _ _ hne; exact absurd hne (by simp)
  · intro a S' ha ih h0 hw hsub _
    rw [Finset.sum_insert ha]
    have hTa0 : T a ≠ 0 := h0 a (Finset.mem_insert_self a S')
    have hwa : γ' ≤ σ.w (T a) := hw a (Finset.mem_insert_self a S')
    rcases S'.eq_empty_or_nonempty with hE | hE
    · subst hE; rw [Finset.sum_empty, add_zero]; exact hwa
    · have hP0 : (∑ j ∈ S', T j) ≠ 0 := hsub S' (Finset.subset_insert a S') hE
      have hPw : γ' ≤ σ.w (∑ j ∈ S', T j) :=
        ih (fun j hj => h0 j (Finset.mem_insert_of_mem hj))
          (fun j hj => hw j (Finset.mem_insert_of_mem hj))
          (fun S'' h'' => hsub S'' (h''.trans (Finset.subset_insert a S'))) hE
      have htot : T a + ∑ j ∈ S', T j ≠ 0 := by
        have h := hsub (insert a S') (Finset.Subset.refl _) ⟨a, Finset.mem_insert_self a S'⟩
        rwa [Finset.sum_insert ha] at h
      exact le_trans (le_min hwa hPw) (σ.hwult (T a) (∑ j ∈ S', T j) hTa0 hP0 htot)

/-- The graded trichotomy engine (see `L5_recSubst_R4`, where it is private). -/
private lemma graded_sum (σ : Stage p F)
    (hstrict : ∀ f g, f ≠ 0 → g ≠ 0 → σ.w f < σ.w g → σ.w (f + g) = σ.w f)
    (hjump : ∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 → σ.w f = σ.w g → σ.w f < σ.w (f + g) →
      σ.R f + σ.R g = 0)
    (T : ℕ → Polynomial ℤ_[p]) (γ : ℤ) (S : Finset ℕ)
    (h0 : ∀ j ∈ S, T j ≠ 0) (hw : ∀ j ∈ S, σ.w (T j) = γ)
    (hsub : ∀ S' ⊆ S, S'.Nonempty → (∑ j ∈ S', T j) ≠ 0) (hne : S.Nonempty) :
    γ ≤ σ.w (∑ j ∈ S, T j) ∧
      (σ.w (∑ j ∈ S, T j) = γ → σ.R (∑ j ∈ S, T j) = ∑ j ∈ S, σ.R (T j)) ∧
      (γ < σ.w (∑ j ∈ S, T j) → ∑ j ∈ S, σ.R (T j) = 0) := by
  classical
  revert h0 hw hsub hne
  refine Finset.induction_on S ?_ ?_
  · intro _ _ _ hne; exact absurd hne (by simp)
  · intro a S' ha ih h0 hw hsub _
    simp only [Finset.sum_insert ha]
    have hTa0 : T a ≠ 0 := h0 a (Finset.mem_insert_self a S')
    have hwa : σ.w (T a) = γ := hw a (Finset.mem_insert_self a S')
    rcases S'.eq_empty_or_nonempty with hE | hE
    · subst hE
      rw [Finset.sum_empty, add_zero, Finset.sum_empty, add_zero]
      exact ⟨le_of_eq hwa.symm, fun _ => rfl,
        fun h => absurd h (by rw [hwa]; exact lt_irrefl γ)⟩
    · have hP0 : (∑ j ∈ S', T j) ≠ 0 := hsub S' (Finset.subset_insert a S') hE
      obtain ⟨hPge, hPeq, hPgt⟩ := ih (fun j hj => h0 j (Finset.mem_insert_of_mem hj))
        (fun j hj => hw j (Finset.mem_insert_of_mem hj))
        (fun S'' h'' => hsub S'' (h''.trans (Finset.subset_insert a S'))) hE
      have htot : T a + ∑ j ∈ S', T j ≠ 0 := by
        have h := hsub (insert a S') (Finset.Subset.refl _) ⟨a, Finset.mem_insert_self a S'⟩
        rwa [Finset.sum_insert ha] at h
      have hge : γ ≤ σ.w (T a + ∑ j ∈ S', T j) := by
        have h := σ.hwult (T a) (∑ j ∈ S', T j) hTa0 hP0 htot
        rwa [hwa, min_eq_left hPge] at h
      rcases eq_or_lt_of_le hPge with hPγ | hPγ
      · refine ⟨hge, ?_, ?_⟩
        · intro htotw
          rw [σ.hRadd (T a) (∑ j ∈ S', T j) hTa0 hP0 htot (hwa.trans hPγ)
            (htotw.trans hwa.symm), hPeq hPγ.symm]
        · intro hgt
          have hj := hjump (T a) (∑ j ∈ S', T j) hTa0 hP0 htot (hwa.trans hPγ)
            (by rw [hwa]; exact hgt)
          rw [← hPeq hPγ.symm]
          exact hj
      · have hwtot : σ.w (T a + ∑ j ∈ S', T j) = γ := by
          rw [hstrict (T a) (∑ j ∈ S', T j) hTa0 hP0 (by rw [hwa]; exact hPγ), hwa]
        refine ⟨hge, ?_, ?_⟩
        · intro _
          rw [σ.hRlt (T a) (∑ j ∈ S', T j) hTa0 hP0 htot (by rw [hwa]; exact hPγ),
            hPgt hPγ, add_zero]
        · intro hgt
          rw [hwtot] at hgt
          exact absurd hgt (lt_irrefl γ)

/-! ### The frame substitution `z ↦ z + c̃` on the polynomial part of `L₀` -/

open scoped Classical in
/-- The D.10 substitution `z ↦ z + c̃`, total on `K[z^{±1}]`: on the image of
`Polynomial.toLaurent` it is `P(z) ↦ P(z + c̃)` (the unique preimage, `toLaurent`
being injective); junk identity off it. At an `e = 1` stage every residual lies
in the image (`res_poly`), so all stage laws see only the ring-automorphism leg. -/
private noncomputable def shiftL {K : Type*} [Field K] (cc : K)
    (ℓ : LaurentPolynomial K) : LaurentPolynomial K :=
  if h : ∃ P : Polynomial K, ℓ = Polynomial.toLaurent P
  then Polynomial.toLaurent (h.choose.comp (Polynomial.X + Polynomial.C cc))
  else ℓ

private lemma shiftL_spec {K : Type*} [Field K] (cc : K) (ℓ : LaurentPolynomial K)
    (P : Polynomial K) (hP : ℓ = Polynomial.toLaurent P) :
    shiftL cc ℓ = Polynomial.toLaurent (P.comp (Polynomial.X + Polynomial.C cc)) := by
  have h : ∃ Q : Polynomial K, ℓ = Polynomial.toLaurent Q := ⟨P, hP⟩
  rw [shiftL, dif_pos h]
  have hQP : h.choose = P := Polynomial.toLaurent_injective (h.choose_spec.symm.trans hP)
  rw [hQP]

private lemma shiftL_zero {K : Type*} [Field K] (cc : K) : shiftL cc 0 = 0 := by
  rw [shiftL_spec cc 0 0 (by simp), Polynomial.zero_comp, map_zero]

private lemma shiftL_C {K : Type*} [Field K] (cc : K) (c : K) :
    shiftL cc (LaurentPolynomial.C c) = LaurentPolynomial.C c := by
  rw [shiftL_spec cc _ (Polynomial.C c) (Polynomial.toLaurent_C c).symm,
    Polynomial.C_comp, Polynomial.toLaurent_C]

/-- A finite sum of `toLaurent`-images is a `toLaurent`-image. -/
private lemma sum_toLaurent {K : Type*} [Field K] (S : Finset ℕ)
    (φ : ℕ → LaurentPolynomial K) (h : ∀ j ∈ S, ∃ P, φ j = Polynomial.toLaurent P) :
    ∃ P, (∑ j ∈ S, φ j) = Polynomial.toLaurent P := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a S' ha ih =>
    obtain ⟨Pa, hPa⟩ := h a (Finset.mem_insert_self a S')
    obtain ⟨Pr, hPr⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    exact ⟨Pa + Pr, by rw [Finset.sum_insert ha, hPa, hPr, map_add]⟩

/-! ### The image lemma: at `e = 1`, every residual is a genuine polynomial in `z` -/

/-- **The image lemma.** At an `e = 1` stage with the tie laws, `R f` has no
negative `z`-positions: develop `f` at the stage key (Fact A); K1 pins `w f` as
the attained slot minimum; the graded trichotomy reduces `R f` to the sum over
the minimizing slots, each of which is `C(cⱼ)·zʲ` (position-0 digit `hS5` at
`t = 0` times the key residual `z^{s·j}`, `s = 1`). -/
private lemma res_poly {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hcore : StageCore σ) (ht0 : σ.t = 0) (hs1 : σ.s = 1)
    (f : Polynomial ℤ_[p]) (hf : f ≠ 0) :
    ∃ P : Polynomial ↥σ.K, σ.R f = Polynomial.toLaurent P := by
  classical
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  obtain ⟨B, N, hdev⟩ := L0_FactA_exists σ.Φ σ.hmonic σ.hdeg f
  obtain ⟨hBdeg, hBz, hBsum⟩ := hdev
  obtain ⟨hmin, jat, hjN, hjnz, hjw⟩ := σ.hK1 f B N hf ⟨hBdeg, hBz, hBsum⟩
  set A : Finset ℕ := (Finset.range N).filter (fun j => B j ≠ 0) with hA
  set M : Finset ℕ := A.filter (fun j => σ.w (B j) + (j : ℤ) * σ.w σ.Φ = σ.w f) with hM
  set Rt : Finset ℕ := A.filter (fun j => ¬(σ.w (B j) + (j : ℤ) * σ.w σ.Φ = σ.w f)) with hRt
  have hMmem : ∀ j ∈ M, B j ≠ 0 ∧ σ.w (B j) + (j : ℤ) * σ.w σ.Φ = σ.w f := by
    intro j hj
    have h1 := Finset.mem_filter.mp hj
    exact ⟨(Finset.mem_filter.mp h1.1).2, h1.2⟩
  have hTw : ∀ j, B j ≠ 0 → σ.w (B j * σ.Φ ^ j) = σ.w (B j) + (j : ℤ) * σ.w σ.Φ := by
    intro j hBj
    rw [σ.hwmul (B j) (σ.Φ ^ j) hBj (pow_ne_zero _ hΦne), w_pow σ σ.Φ hΦne]
  have hT0M : ∀ j ∈ M, B j * σ.Φ ^ j ≠ 0 := fun j hj =>
    mul_ne_zero (hMmem j hj).1 (pow_ne_zero _ hΦne)
  have hTwM : ∀ j ∈ M, σ.w (B j * σ.Φ ^ j) = σ.w f := fun j hj => by
    rw [hTw j (hMmem j hj).1]; exact (hMmem j hj).2
  have hsubA : ∀ S ⊆ A, S.Nonempty → (∑ j ∈ S, B j * σ.Φ ^ j) ≠ 0 := by
    intro S hS hSne
    obtain ⟨j₀, hj₀⟩ := hSne
    exact subsum_ne_zero σ.Φ σ.hmonic B hBdeg S j₀ hj₀
      (Finset.mem_filter.mp (hS hj₀)).2
  have hsubM : ∀ S ⊆ M, S.Nonempty → (∑ j ∈ S, B j * σ.Φ ^ j) ≠ 0 :=
    fun S hS hSne => hsubA S (hS.trans (Finset.filter_subset _ _)) hSne
  have hMne : M.Nonempty :=
    ⟨jat, Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjN, hjnz⟩, hjw.symm⟩⟩
  have hfminne : (∑ j ∈ M, B j * σ.Φ ^ j) ≠ 0 := hsubM M (Finset.Subset.refl M) hMne
  have hfA : f = ∑ j ∈ A, B j * σ.Φ ^ j := by
    rw [hBsum]
    refine (Finset.sum_filter_of_ne ?_).symm
    intro j hj hne hBj
    exact hne (by rw [hBj, zero_mul])
  have hkey : f = (∑ j ∈ M, B j * σ.Φ ^ j) + ∑ j ∈ Rt, B j * σ.Φ ^ j := by
    rw [hfA]
    exact (Finset.sum_filter_add_sum_filter_not A _ _).symm
  obtain ⟨hgeM, heqM, _⟩ := graded_sum σ hcore.w_strict hcore.w_jump
    (fun j => B j * σ.Φ ^ j) (σ.w f) M hT0M hTwM hsubM hMne
  -- `R f` is the residual of the minimizing part
  have hpair : σ.w (∑ j ∈ M, B j * σ.Φ ^ j) = σ.w f ∧
      σ.R f = σ.R (∑ j ∈ M, B j * σ.Φ ^ j) := by
    rcases Rt.eq_empty_or_nonempty with hRtE | hRtne
    · have hfeq : f = ∑ j ∈ M, B j * σ.Φ ^ j := by
        rw [hkey, hRtE, Finset.sum_empty, add_zero]
      rw [← hfeq]
      exact ⟨rfl, rfl⟩
    · have hfrne : (∑ j ∈ Rt, B j * σ.Φ ^ j) ≠ 0 :=
        hsubA Rt (Finset.filter_subset _ _) hRtne
      have hfrw : σ.w f + 1 ≤ σ.w (∑ j ∈ Rt, B j * σ.Φ ^ j) := by
        refine w_sum_ge σ _ (σ.w f + 1) Rt (fun j hj => ?_) (fun j hj => ?_)
          (fun S hS hSne => hsubA S (hS.trans (Finset.filter_subset _ _)) hSne) hRtne
        · exact mul_ne_zero (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
            (pow_ne_zero _ hΦne)
        · have hjA := (Finset.mem_filter.mp hj).1
          have hjne := (Finset.mem_filter.mp hj).2
          have hBj := (Finset.mem_filter.mp hjA).2
          have hjN' := Finset.mem_range.mp (Finset.mem_filter.mp hjA).1
          rw [hTw j hBj]
          exact Int.add_one_le_iff.mpr (lt_of_le_of_ne (hmin j hjN' hBj) (Ne.symm hjne))
      have hwfmin : σ.w (∑ j ∈ M, B j * σ.Φ ^ j) = σ.w f := by
        by_contra hne2
        have hlt : σ.w f < σ.w (∑ j ∈ M, B j * σ.Φ ^ j) :=
          lt_of_le_of_ne hgeM (Ne.symm hne2)
        have h := σ.hwult (∑ j ∈ M, B j * σ.Φ ^ j) (∑ j ∈ Rt, B j * σ.Φ ^ j)
          hfminne hfrne (by rw [← hkey]; exact hf)
        rw [← hkey] at h
        exact absurd h (not_le.mpr (lt_min hlt (by omega)))
      refine ⟨hwfmin, ?_⟩
      conv_lhs => rw [hkey]
      exact σ.hRlt _ _ hfminne hfrne (by rw [← hkey]; exact hf)
        (by rw [hwfmin]; omega)
  rw [hpair.2, heqM hpair.1]
  refine sum_toLaurent M _ (fun j hj => ?_)
  have hBj : B j ≠ 0 := (hMmem j hj).1
  obtain ⟨c, hc⟩ := σ.hS5 (B j) hBj (hBdeg j)
  have hcC : σ.R (B j) = LaurentPolynomial.C (c : ↥σ.K) := by
    rw [hc, ht0, neg_zero, zero_mul, LaurentPolynomial.T_zero, mul_one]
  refine ⟨Polynomial.C (c : ↥σ.K) * Polynomial.X ^ j, ?_⟩
  rw [σ.hRmul (B j) (σ.Φ ^ j) hBj (pow_ne_zero _ hΦne), R_pow σ σ.Φ hΦne, σ.hRΦ, hs1,
    hcC, T_pow_s, mul_one, map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow]

/-- The residual of a product of nonzero coefficients is a nonzero `K`-constant (`t = 0`). -/
private lemma coeff_prod_R (σ : Stage p F) (ht0 : σ.t = 0) (l : List (Polynomial ℤ_[p]))
    (hl : ∀ u ∈ l, u ≠ 0 ∧ inC σ.Φ u) :
    ∃ d : ↥σ.K, d ≠ 0 ∧ σ.R l.prod = LaurentPolynomial.C d := by
  induction l with
  | nil => exact ⟨1, one_ne_zero, by rw [List.prod_nil, R_one, map_one]⟩
  | cons a rest ih =>
    obtain ⟨d, hd, hR⟩ := ih (fun u hu => hl u (List.mem_cons_of_mem a hu))
    obtain ⟨ha1, ha2⟩ := hl a List.mem_cons_self
    obtain ⟨c, hc⟩ := σ.hS5 a ha1 ha2
    have hcC : σ.R a = LaurentPolynomial.C (c : ↥σ.K) := by
      rw [hc, ht0, neg_zero, zero_mul, LaurentPolynomial.T_zero, mul_one]
    have htne : rest.prod ≠ 0 :=
      list_prod_ne_zero rest (fun u hu => (hl u (List.mem_cons_of_mem a hu)).1)
    exact ⟨(c : ↥σ.K) * d, mul_ne_zero c.ne_zero hd,
      by rw [List.prod_cons, σ.hRmul a rest.prod ha1 htne, hcC, hR, ← map_mul]⟩

/-- The residual of an `L`-monomial `l.prod · Φ^j` is `C d · zʲ` (`t = 0`, `s = 1`). -/
private lemma unitMonProd_R (σ : Stage p F) (ht0 : σ.t = 0) (hs1 : σ.s = 1)
    (l : List (Polynomial ℤ_[p])) (j : ℕ) (hl : ∀ u ∈ l, u ≠ 0 ∧ inC σ.Φ u) :
    ∃ d : ↥σ.K, d ≠ 0 ∧
      σ.R (l.prod * σ.Φ ^ j) = LaurentPolynomial.C d * LaurentPolynomial.T (j : ℤ) := by
  obtain ⟨d, hd, hR⟩ := coeff_prod_R σ ht0 l hl
  have hlne : l.prod ≠ 0 := list_prod_ne_zero l (fun u hu => (hl u hu).1)
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  refine ⟨d, hd, ?_⟩
  rw [σ.hRmul _ _ hlne (pow_ne_zero j hΦne), hR, R_pow σ σ.Φ hΦne j, σ.hRΦ, hs1,
    T_pow_s, mul_one]

/-- Inverting the substitution: `P(z + c̃) = 0` forces `P = 0`. -/
private lemma comp_shift_eq_zero {K : Type*} [Field K] (cc : K) (P : Polynomial K)
    (h : P.comp (Polynomial.X + Polynomial.C cc) = 0) : P = 0 := by
  have hP : P = (P.comp (Polynomial.X + Polynomial.C cc)).comp
      (Polynomial.X - Polynomial.C cc) := by
    rw [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp,
      sub_add_cancel, Polynomial.comp_X]
  rw [h, Polynomial.zero_comp] at hP
  exact hP

end Helpers

/-- Unit S10: at e_read = 1, a cored stage with a nonzero center and a D.9 lift
recenters to a cored stage, with the recording relation. -/
theorem S10_recStage {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ) (he1 : σ.e = 1)
    (cc : ↥σ.K) (hcc : cc ≠ 0)
    (hlift : ∃ tt : Polynomial ℤ_[p], tt ≠ 0 ∧ inC σ.Φ tt ∧ σ.w tt = σ.w σ.Φ ∧
      σ.R tt = LaurentPolynomial.C cc * LaurentPolynomial.T 0) :
    ∃ (σ' : Stage p F) (tt : Polynomial ℤ_[p]),
      IsRecenteringCore σ σ' cc tt ∧ StageCoreL σ' := by
  classical
  obtain ⟨tt, httne, htc, htw, htdig⟩ := hlift
  have hcore : StageCore σ := hσ.core
  -- e = 1 pins t = 0, s = 1
  have ht0 : σ.t = 0 := σ.he1t he1
  have hs1 : σ.s = 1 := by
    have h := σ.hbez; rw [he1, ht0] at h; push_cast at h; linarith
  -- basic nonvanishing
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have httne' : (-tt) ≠ 0 := neg_ne_zero.mpr httne
  have hmonic' : (σ.Φ - tt).Monic := σ.hmonic.sub_of_left htc
  have hΦ'ne : σ.Φ - tt ≠ 0 := hmonic'.ne_zero
  have hΦ'ne2 : σ.Φ + -tt ≠ 0 := by rw [← sub_eq_add_neg]; exact hΦ'ne
  have hdegΦ' : (σ.Φ - tt).degree = σ.Φ.degree :=
    Polynomial.degree_sub_eq_left_of_degree_lt htc
  have hinC : ∀ B : Polynomial ℤ_[p], (inC (σ.Φ - tt) B ↔ inC σ.Φ B) := by
    intro B
    show B.degree < (σ.Φ - tt).degree ↔ B.degree < σ.Φ.degree
    rw [hdegΦ']
  -- D.5 at g = 1: the recentered key keeps the weight and satisfies K1
  have hVV := L5_recVV σ hcore he1 cc hcc tt htc httne htw htdig
  have hwΦ' : σ.w (σ.Φ - tt) = σ.w σ.Φ := hVV.1
  have hK1' : K1At σ.w (σ.Φ - tt) (σ.w σ.Φ) := hVV.2
  -- the parent residual of the recentered key: R(Φ − tt) = z − c̃
  have hwneg : σ.w (-tt) = σ.w σ.Φ := by rw [val_neg σ.w σ.hwmul tt httne, htw]
  have hRΦsub : σ.R (σ.Φ - tt) = LaurentPolynomial.T 1 - LaurentPolynomial.C cc := by
    have h := σ.hRadd σ.Φ (-tt) hΦne httne' hΦ'ne2 hwneg.symm
      (by rw [← sub_eq_add_neg]; exact hwΦ')
    rw [← sub_eq_add_neg] at h
    rw [h, σ.hRΦ, hs1, hcore.R_neg, htdig, LaurentPolynomial.T_zero, mul_one,
      ← sub_eq_add_neg]
  -- the parent weight of the recentered key is unchanged
  have hwPrevtt : σ.wPrev tt = (σ.h : ℤ) := by
    have h1 := σ.hStretch tt httne htc
    rw [he1] at h1
    have h2 : σ.w tt = (σ.h : ℤ) := htw.trans σ.hwΦ
    push_cast at h1
    linarith
  have hpI : σ.wPrev σ.Φ < (σ.h : ℤ) := by
    have h := hcore.prevIaug
    rw [he1] at h
    push_cast at h
    linarith
  have hwPrevΦ' : σ.wPrev (σ.Φ - tt) = σ.wPrev σ.Φ := by
    have hwPn : σ.wPrev (-tt) = (σ.h : ℤ) := by
      rw [val_neg σ.wPrev hcore.wPrev_mul tt httne, hwPrevtt]
    have hge := hcore.wPrev_ult σ.Φ (-tt) hΦne httne' hΦ'ne2
    rw [← sub_eq_add_neg] at hge
    have hle := hcore.wPrev_ult (σ.Φ - tt) tt hΦ'ne httne
      (by rw [sub_add_cancel]; exact hΦne)
    rw [sub_add_cancel] at hle
    rw [hwPn] at hge
    rw [hwPrevtt] at hle
    omega
  -- coefficient residuals are position-0 constants, hence substitution-FIXED
  have hRconst : ∀ B : Polynomial ℤ_[p], B ≠ 0 → inC σ.Φ B →
      ∃ c : (↥σ.K)ˣ, σ.R B = LaurentPolynomial.C (c : ↥σ.K) := by
    intro B hB hin
    obtain ⟨c, hc⟩ := σ.hS5 B hB hin
    exact ⟨c, by rw [hc, ht0, neg_zero, zero_mul, LaurentPolynomial.T_zero, mul_one]⟩
  have hRfix : ∀ B : Polynomial ℤ_[p], inC σ.Φ B → shiftL cc (σ.R B) = σ.R B := by
    intro B hin
    rcases eq_or_ne B 0 with h0 | hB
    · rw [h0, σ.hR0, shiftL_zero]
    · obtain ⟨c, hc⟩ := hRconst B hB hin
      rw [hc, shiftL_C]
  -- the recentered stage: ONLY the key and the residual frame change
  let σ' : Stage p F :=
    { e := σ.e, h := σ.h, s := σ.s, t := σ.t
      he := σ.he, hh := σ.hh, hcop := σ.hcop, hbez := σ.hbez, he1t := σ.he1t
      Φ := σ.Φ - tt
      hmonic := hmonic'
      hdeg := by rw [Polynomial.natDegree_eq_of_degree_eq hdegΦ']; exact σ.hdeg
      w := σ.w
      wPrev := σ.wPrev
      K := σ.K
      FQ := σ.FQ
      hFQ_le := σ.hFQ_le
      R := fun f => shiftL cc (σ.R f)
      hwmul := σ.hwmul
      hwult := σ.hwult
      hvalgrp := σ.hvalgrp
      hwΦ := by rw [hwΦ']; exact σ.hwΦ
      hStretch := fun B hB hin => σ.hStretch B hB ((hinC B).mp hin)
      hR0 := by rw [σ.hR0, shiftL_zero]
      hRne := by
        intro f hf h0
        obtain ⟨P, hP⟩ := res_poly σ hcore ht0 hs1 f hf
        rw [shiftL_spec cc _ P hP] at h0
        have hPc : P.comp (Polynomial.X + Polynomial.C cc) = 0 :=
          Polynomial.toLaurent_injective (by rw [h0, map_zero])
        exact σ.hRne f hf (by rw [hP, comp_shift_eq_zero cc P hPc, map_zero])
      hRmul := by
        intro f g hf hg
        obtain ⟨P, hP⟩ := res_poly σ hcore ht0 hs1 f hf
        obtain ⟨Q, hQ⟩ := res_poly σ hcore ht0 hs1 g hg
        show shiftL cc (σ.R (f * g)) = shiftL cc (σ.R f) * shiftL cc (σ.R g)
        rw [σ.hRmul f g hf hg, hP, hQ, ← map_mul, shiftL_spec cc _ (P * Q) rfl,
          shiftL_spec cc _ P rfl, shiftL_spec cc _ Q rfl, Polynomial.mul_comp, map_mul]
      hRadd := by
        intro f g hf hg hfg hwfg hwsum
        obtain ⟨P, hP⟩ := res_poly σ hcore ht0 hs1 f hf
        obtain ⟨Q, hQ⟩ := res_poly σ hcore ht0 hs1 g hg
        show shiftL cc (σ.R (f + g)) = shiftL cc (σ.R f) + shiftL cc (σ.R g)
        rw [σ.hRadd f g hf hg hfg hwfg hwsum, hP, hQ, ← map_add,
          shiftL_spec cc _ (P + Q) rfl, shiftL_spec cc _ P rfl, shiftL_spec cc _ Q rfl,
          Polynomial.add_comp, map_add]
      hRlt := by
        intro f g hf hg hfg hlt
        show shiftL cc (σ.R (f + g)) = shiftL cc (σ.R f)
        rw [σ.hRlt f g hf hg hfg hlt]
      hRΦ := by
        show shiftL cc (σ.R (σ.Φ - tt)) = LaurentPolynomial.T σ.s
        rw [hs1, hRΦsub,
          shiftL_spec cc _ (Polynomial.X - Polynomial.C cc)
            (by rw [map_sub, Polynomial.toLaurent_X, Polynomial.toLaurent_C]),
          Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, add_sub_cancel_right,
          Polynomial.toLaurent_X]
      hK1 := by
        show K1At σ.w (σ.Φ - tt) (σ.w (σ.Φ - tt))
        rw [hwΦ']
        exact hK1'
      hS5 := by
        intro B hB hin
        have hin' : inC σ.Φ B := (hinC B).mp hin
        obtain ⟨c, hc⟩ := σ.hS5 B hB hin'
        exact ⟨c, by show shiftL cc (σ.R B) = _; rw [hRfix B hin']; exact hc⟩
      reps := σ.reps
      hreps := fun u hu => ⟨(σ.hreps u hu).1, (hinC u).mpr (σ.hreps u hu).2⟩
      Tvec := σ.Tvec
      hTvec := σ.hTvec
      weightSet := σ.weightSet
      hWS := fun B hB hin => σ.hWS B hB ((hinC B).mp hin)
      hS6a := by
        intro ν hν
        obtain ⟨b, hb⟩ := σ.hS6a ν hν
        refine ⟨b, fun c hcF => ?_⟩
        obtain ⟨B, hB, hin, hw, hR⟩ := hb c hcF
        exact ⟨B, hB, (hinC B).mpr hin, hw,
          by show shiftL cc (σ.R B) = _; rw [hRfix B hin]; exact hR⟩
      hS6b := by
        intro ν a hν
        have hν' : σ.wPrev σ.Φ < ν := by rwa [hwPrevΦ'] at hν
        obtain ⟨B, hB, hin, hw, hR⟩ := σ.hS6b ν a hν'
        exact ⟨B, hB, (hinC B).mpr hin, hw,
          by show shiftL cc (σ.R B) = _; rw [hRfix B hin]; exact hR⟩ }
  refine ⟨σ', tt, ?_, ?_⟩
  -- (1) the recording relation
  · refine ⟨⟨he1, he1, hcc, htc, httne, htw, htdig, rfl, fun _ => rfl, fun _ => rfl,
      rfl, rfl, rfl, ?_⟩, ?_, rfl, rfl⟩
    · -- digits literally unchanged (position-0 constants are substitution-fixed)
      intro B hB hin zbar
      exact congrArg (LaurentPolynomial.eval₂ σ.K.subtype zbar) (hRfix B hin)
    · -- coefficient residuals unchanged in the common localization
      intro B hin
      exact congrArg
        (LaurentPolynomial.eval₂ ((algebraMap F (RatFunc F)).comp σ.K.subtype) (ratX F))
        (hRfix B hin)
  -- (2) the stage core transports
  · -- shared transports: the tie laws for the shifted residual, and `grRes` agreement
    have hjump' : ∀ f g : Polynomial ℤ_[p], f ≠ 0 → g ≠ 0 → f + g ≠ 0 → σ.w f = σ.w g →
        σ.w f < σ.w (f + g) → σ'.R f + σ'.R g = 0 := by
      intro f g hf hg hfg hwfg hlt
      have hR := hcore.w_jump f g hf hg hfg hwfg hlt
      obtain ⟨P, hP⟩ := res_poly σ hcore ht0 hs1 f hf
      obtain ⟨Q, hQ⟩ := res_poly σ hcore ht0 hs1 g hg
      have hPQ : P + Q = 0 := by
        apply Polynomial.toLaurent_injective
        rw [map_add, ← hP, ← hQ, hR, map_zero]
      show shiftL cc (σ.R f) + shiftL cc (σ.R g) = 0
      rw [shiftL_spec cc _ P hP, shiftL_spec cc _ Q hQ, ← map_add, ← Polynomial.add_comp,
        hPQ, Polynomial.zero_comp, map_zero]
    have hRneg' : ∀ f : Polynomial ℤ_[p], σ'.R (-f) = - σ'.R f := by
      intro f
      rcases eq_or_ne f 0 with h0 | hf
      · rw [h0, neg_zero]
        show shiftL cc (σ.R 0) = - shiftL cc (σ.R 0)
        rw [σ.hR0, shiftL_zero, neg_zero]
      · obtain ⟨P, hP⟩ := res_poly σ hcore ht0 hs1 f hf
        have hnf : σ.R (-f) = Polynomial.toLaurent (-P) := by
          rw [hcore.R_neg, hP, map_neg]
        show shiftL cc (σ.R (-f)) = - shiftL cc (σ.R f)
        rw [shiftL_spec cc _ (-P) hnf, shiftL_spec cc _ P hP, Polynomial.neg_comp, map_neg]
    have hgrC : ∀ B : Polynomial ℤ_[p], inC σ.Φ B →
        Stage.grRes σ' B = Stage.grRes σ B := by
      intro B hin
      unfold Stage.grRes
      rw [show σ'.R B = σ.R B from hRfix B hin]
    have hR'Φ : σ'.R σ'.Φ = LaurentPolynomial.T 1 := by
      have h := σ'.hRΦ
      rwa [show σ'.s = 1 from hs1] at h
    have hgrPhi : Stage.grRes σ' σ'.Φ = Stage.grRes σ σ.Φ := by
      unfold Stage.grRes
      rw [hR'Φ, show σ'.w σ'.Φ = σ.w σ.Φ from hwΦ', σ.hRΦ, hs1]
    have hN : σ'.tvecNum = σ.tvecNum := by
      unfold Stage.tvecNum
      rw [show σ'.t = (0 : ℤ) from ht0]
      simp only [Int.toNat_zero, pow_zero, mul_one]
      rfl
    have hD : σ'.tvecDen = σ.tvecDen := by
      unfold Stage.tvecDen
      rw [show σ'.t = (0 : ℤ) from ht0]
      simp only [neg_zero, Int.toNat_zero, pow_zero, mul_one]
      rfl
    have htvec' : TvecLaw σ' := by
      constructor
      · rw [hN, hD]
        exact hcore.tvec.1
      · rw [hN, hD]
        show shiftL cc (σ.R σ.tvecNum) = shiftL cc (σ.R σ.tvecDen)
        rw [hcore.tvec.2]
    refine ⟨⟨hcore.wPrev_mul, hcore.wPrev_ult, hcore.reps_nonempty, hcore.p_is_rep,
      hcore.w_strict, hjump', hRneg', htvec', ?_,
      L2_slotDecomp σ' hcore.w_strict hjump' hRneg', ?_, ?_⟩, ?_, ?_⟩
    · -- prevIaug: the parent weight of the recentered key is unchanged
      show (σ.e : ℤ) * σ.wPrev (σ.Φ - tt) < (σ.h : ℤ)
      rw [hwPrevΦ']
      exact hcore.prevIaug
    · -- (S4) core, clause 1: realizers transport (digits substitution-fixed)
      intro c
      obtain ⟨B, ν, hB, hin, hw, hR⟩ := hcore.coeff.1 c
      refine ⟨B, ν, hB, (hinC B).mpr hin, hw, ?_⟩
      show shiftL cc (σ.R B) = _
      rw [hRfix B hin]
      exact hR
    · constructor
      · -- (S4) core, clause 2: K-lines transport
        intro f g hf hg hfne hgne hwfg
        obtain ⟨l, hlf, hfeq⟩ := hf
        obtain ⟨l', hlg, hgeq⟩ := hg
        have hfσ : IsCoeffProd σ f :=
          ⟨l, fun u hu => ⟨(hlf u hu).1, (hinC u).mp (hlf u hu).2⟩, hfeq⟩
        have hgσ : IsCoeffProd σ g :=
          ⟨l', fun u hu => ⟨(hlg u hu).1, (hinC u).mp (hlg u hu).2⟩, hgeq⟩
        obtain ⟨d, hd⟩ := hcore.coeff.2.1 f g hfσ hgσ hfne hgne hwfg
        obtain ⟨Q, hQ⟩ := res_poly σ hcore ht0 hs1 g hgne
        refine ⟨d, ?_⟩
        show shiftL cc (σ.R f) = LaurentPolynomial.C d * shiftL cc (σ.R g)
        have hdQ : σ.R f = Polynomial.toLaurent (Polynomial.C d * Q) := by
          rw [hd, hQ, map_mul, Polynomial.toLaurent_C]
        rw [shiftL_spec cc _ _ hdQ, shiftL_spec cc _ Q hQ, Polynomial.mul_comp,
          Polynomial.C_comp, map_mul, Polynomial.toLaurent_C]
      · -- (S4) core, clause 3: the exponent group transfers generator by generator
        apply eq_top_iff.mpr
        rw [← hcore.coeff.2.2]
        apply AddSubgroup.closure_mono
        rintro n ⟨f, g, c, c', k, k', hf, hg, hfne, hgne, hwfg, hRf, hRg, hn⟩
        obtain ⟨l, j, hl, hfeq⟩ := hf
        obtain ⟨l', j', hl', hgeq⟩ := hg
        obtain ⟨d, hd, hRd⟩ := unitMonProd_R σ ht0 hs1 l j hl
        obtain ⟨d', hd', hRd'⟩ := unitMonProd_R σ ht0 hs1 l' j' hl'
        rw [hfeq] at hRf
        rw [hgeq] at hRg
        have hkj : k = (j : ℤ) := (monomial_unique hd (hRf.symm.trans hRd)).2
        have hkj' : k' = (j' : ℤ) := (monomial_unique hd' (hRg.symm.trans hRd')).2
        have hl₂ : ∀ u ∈ l, u ≠ 0 ∧ inC σ'.Φ u :=
          fun u hu => ⟨(hl u hu).1, (hinC u).mpr (hl u hu).2⟩
        have hl₂' : ∀ u ∈ l', u ≠ 0 ∧ inC σ'.Φ u :=
          fun u hu => ⟨(hl' u hu).1, (hinC u).mpr (hl' u hu).2⟩
        obtain ⟨e₂, he₂, hRe₂⟩ := unitMonProd_R σ' ht0 hs1 l j hl₂
        obtain ⟨e₂', he₂', hRe₂'⟩ := unitMonProd_R σ' ht0 hs1 l' j' hl₂'
        have hlne : l.prod ≠ 0 := list_prod_ne_zero l (fun u hu => (hl u hu).1)
        have hlne' : l'.prod ≠ 0 := list_prod_ne_zero l' (fun u hu => (hl' u hu).1)
        refine ⟨l.prod * σ'.Φ ^ j, l'.prod * σ'.Φ ^ j', e₂, e₂', (j : ℤ), (j' : ℤ),
          ⟨l, j, hl₂, rfl⟩, ⟨l', j', hl₂', rfl⟩,
          mul_ne_zero hlne (pow_ne_zero _ hΦ'ne),
          mul_ne_zero hlne' (pow_ne_zero _ hΦ'ne), ?_, hRe₂, hRe₂', by omega⟩
        show σ.w (l.prod * (σ.Φ - tt) ^ j) = σ.w (l'.prod * (σ.Φ - tt) ^ j')
        rw [σ.hwmul _ _ hlne (pow_ne_zero _ hΦ'ne), σ.hwmul _ _ hlne' (pow_ne_zero _ hΦ'ne),
          w_pow σ _ hΦ'ne, w_pow σ _ hΦ'ne, hwΦ', ← w_pow σ _ hΦne, ← w_pow σ _ hΦne,
          ← σ.hwmul _ _ hlne (pow_ne_zero _ hΦne), ← σ.hwmul _ _ hlne' (pow_ne_zero _ hΦne),
          ← hfeq, ← hgeq]
        exact hwfg
    · -- TvecUnitLaw: the same witnesses work (grRes agrees on reps and on the key)
      obtain ⟨uY, ru, huY, hru, hprod⟩ := hσ.tvec_unit
      refine ⟨uY, ru, huY.trans hgrPhi.symm, fun i => ?_, hprod⟩
      have hmem : (σ.Tvec.get i).1 ∈ σ.reps := by
        rw [← σ.hTvec]
        exact List.mem_map.mpr ⟨σ.Tvec.get i, σ.Tvec.get_mem i, rfl⟩
      exact (hru i).trans (hgrC _ (σ.hreps _ hmem).2).symm
    · -- CoeffLocLaw: the coefficient-localization subring is LITERALLY the same
      have hS1 : {x : LTwo ↥σ'.K | ∃ B, B ≠ 0 ∧ inC σ'.Φ B ∧ x = Stage.grRes σ' B}
          = {x | ∃ B, B ≠ 0 ∧ inC σ.Φ B ∧ x = Stage.grRes σ B} := by
        ext x
        constructor
        · rintro ⟨B, hB, hin, rfl⟩
          exact ⟨B, hB, (hinC B).mp hin, hgrC B ((hinC B).mp hin)⟩
        · rintro ⟨B, hB, hin, rfl⟩
          exact ⟨B, hB, (hinC B).mpr hin, (hgrC B hin).symm⟩
      have hS2 : {x : LTwo ↥σ'.K | ∃ (i : Fin σ'.reps.length) (u : (LTwo ↥σ'.K)ˣ),
            IsGrUnit σ' (σ'.reps.get i) u ∧ x = ((u⁻¹ : (LTwo ↥σ'.K)ˣ) : LTwo ↥σ'.K)}
          = {x | ∃ (i : Fin σ.reps.length) (u : (LTwo ↥σ.K)ˣ),
            IsGrUnit σ (σ.reps.get i) u ∧ x = ((u⁻¹ : (LTwo ↥σ.K)ˣ) : LTwo ↥σ.K)} := by
        ext x
        constructor
        · rintro ⟨i, u, hu, rfl⟩
          exact ⟨i, u, hu.trans (hgrC _ (σ.hreps _ (σ.reps.get_mem i)).2), rfl⟩
        · rintro ⟨i, u, hu, rfl⟩
          exact ⟨i, u, hu.trans (hgrC _ (σ.hreps _ (σ.reps.get_mem i)).2).symm, rfl⟩
      have hSR : Stage.coeffLocSR σ' = Stage.coeffLocSR σ := by
        unfold Stage.coeffLocSR
        rw [hS1, hS2]
      refine ⟨?_, ?_, ?_⟩
      · intro ℓ hmem
        rw [hSR] at hmem
        exact hσ.coeff_loc.1 ℓ hmem
      · intro d
        rw [hSR]
        exact hσ.coeff_loc.2.1 d
      · obtain ⟨zv, u, hzw, hzval, hzu⟩ := hσ.coeff_loc.2.2
        obtain ⟨ru, uY, hru, huY, hueq⟩ := hzval
        exact ⟨zv, u, hzw, ⟨ru, uY,
          fun i => (hru i).trans (hgrC _ (σ.hreps _ (σ.reps.get_mem i)).2).symm,
          huY.trans hgrPhi.symm, hueq⟩, hzu⟩

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S10_recStage
