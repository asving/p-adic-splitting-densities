/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.L0_FactA_exists
import LeanUrat.Moves.L0_FactB_unique

/-!
# Moves/L5_recSubst — the D.10 substitution identity in the common localization (§B2-DEF)

`moves_ref`: D.10 substitution identity `R'(f) = R(f)(z' + c̃)` in the COMMON LOCALIZATION,
for every `f` — DERIVED; MOVES ~2447-2469.

The conclusion `RecenterSubstCore σ σ' cc` unfolds to: for EVERY `f`,
`σ'.ratRes f = σ.ratResShift (cc:F) f` as elements of `RatFunc F`, i.e.
`(σ'.R f)(z') = (σ.R f)(z' + c̃)` at the transcendental point `ζ` (injective on Laurent
polynomials — the audit-#3 fix, not finite-field evaluation).

Proof (the D.10 development): develop `f` at the child key `Φ' = Φ − tt` (Fact A); `hK1'`
pins `w f` as the attained slot minimum; the graded trichotomy engine (`graded_sum`, run
from the StageCore tie laws `w_strict`/`w_jump` with Fact-B nonvanishing of slot subsums)
reduces `R f` on BOTH stages to the residual sum over the minimizing slots; at `e = e' = 1`
the coefficient residuals are position-0 constants (`hS5` + `t = 0`), hence substitution-
invariant, and equal across the recentering by `coeff_R`; the key residuals are
`R(Φ') = z − c̃` (parent, via `hRadd` + the tie laws) and `R'(Φ') = z'` (child, `hRΦ`), and
`eval₂` sends both slot monomial factors to `ζ^j` — the two sides agree slotwise.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.Moves

open Polynomial

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- `R 1 = 1`. -/
private lemma R_one' (σ : Stage p F) : σ.R 1 = 1 := by
  have h := σ.hRmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  exact (mul_left_cancel₀ (σ.hRne 1 one_ne_zero) (by rw [mul_one]; exact h)).symm

/-- `R (g^j) = (R g)^j` for `g ≠ 0`. -/
private lemma R_pow' (σ : Stage p F) (g : Polynomial ℤ_[p]) (hg : g ≠ 0) (j : ℕ) :
    σ.R (g ^ j) = (σ.R g) ^ j := by
  induction j with
  | zero => rw [pow_zero, pow_zero, R_one']
  | succ n ih => rw [pow_succ, σ.hRmul (g ^ n) g (pow_ne_zero n hg) hg, ih, pow_succ]

/-- `w 1 = 0`. -/
private lemma w_one' (σ : Stage p F) : σ.w 1 = 0 := by
  have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h; linarith

/-- `w (-f) = w f` (via the unit `-1`). -/
private lemma w_neg' (σ : Stage p F) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) :
    σ.w (-f) = σ.w f := by
  have hn1 : (-1 : Polynomial ℤ_[p]) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have key := σ.hwmul (-1) (-1) hn1 hn1
  rw [neg_one_mul, neg_neg, w_one' σ] at key
  have hw1 : σ.w (-1 : Polynomial ℤ_[p]) = 0 := by linarith
  have h2 := σ.hwmul (-1) f hn1 hf
  rw [neg_one_mul, hw1, zero_add] at h2; exact h2

/-- `w (g^j) = j·(w g)` for `g ≠ 0`. -/
private lemma w_pow' (σ : Stage p F) (g : Polynomial ℤ_[p]) (hg : g ≠ 0) (j : ℕ) :
    σ.w (g ^ j) = (j : ℤ) * σ.w g := by
  induction j with
  | zero => rw [pow_zero, w_one' σ]; simp
  | succ n ih =>
    rw [pow_succ, σ.hwmul (g ^ n) g (pow_ne_zero n hg) hg, ih]
    push_cast; ring

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

/-- **The graded trichotomy engine.** Over a family of nonzero terms of common weight `γ`
with nonvanishing subsums: the total weight is `≥ γ`; if it equals `γ` the residual is
additive across the family; if it exceeds `γ` the term residuals cancel. Joint induction
from the D.1(b) tie laws (`w_strict`, `w_jump`) and the stage laws (`hwult`/`hRadd`/`hRlt`). -/
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
      · -- the tail sits AT weight γ
        refine ⟨hge, ?_, ?_⟩
        · intro htotw
          rw [σ.hRadd (T a) (∑ j ∈ S', T j) hTa0 hP0 htot (hwa.trans hPγ)
            (htotw.trans hwa.symm), hPeq hPγ.symm]
        · intro hgt
          have hj := hjump (T a) (∑ j ∈ S', T j) hTa0 hP0 htot (hwa.trans hPγ)
            (by rw [hwa]; exact hgt)
          rw [← hPeq hPγ.symm]
          exact hj
      · -- the tail sits ABOVE weight γ
        have hwtot : σ.w (T a + ∑ j ∈ S', T j) = γ := by
          rw [hstrict (T a) (∑ j ∈ S', T j) hTa0 hP0 (by rw [hwa]; exact hPγ), hwa]
        refine ⟨hge, ?_, ?_⟩
        · intro _
          rw [σ.hRlt (T a) (∑ j ∈ S', T j) hTa0 hP0 htot (by rw [hwa]; exact hPγ),
            hPgt hPγ, add_zero]
        · intro hgt
          rw [hwtot] at hgt
          exact absurd hgt (lt_irrefl γ)

end

theorem L5_recSubst {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ σ' : Stage p F) (hcore : StageCore σ) (hcore' : StageCore σ') (cc : ↥σ.K) (tt : Polynomial ℤ_[p]) (hrec : IsRecenteringCore σ σ' cc tt) (hK1' : K1At σ.w σ'.Φ (σ.w σ.Φ)) : RecenterSubstCore σ σ' cc := by
  classical
  obtain ⟨hbase, hcoeffR, _, _⟩ := hrec
  obtain ⟨he1, he1', hcc, htc, httne, htw, htR, hΦ'eq, hww, hwPrev, hKK, hFQ, hWSet, hdigeq⟩ :=
    hbase
  -- e = 1 pins t = 0, s = 1 on both stages
  have ht0 : σ.t = 0 := σ.he1t he1
  have hs1 : σ.s = 1 := by
    have h := σ.hbez; rw [he1, ht0] at h; push_cast at h; linarith
  have ht0' : σ'.t = 0 := σ'.he1t he1'
  have hs1' : σ'.s = 1 := by
    have h := σ'.hbez; rw [he1', ht0'] at h; push_cast at h; linarith
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hΦ'ne : σ'.Φ ≠ 0 := σ'.hmonic.ne_zero
  have httne' : (-tt) ≠ 0 := neg_ne_zero.mpr httne
  have hΦ'ne2 : σ.Φ + -tt ≠ 0 := by rw [← sub_eq_add_neg, ← hΦ'eq]; exact hΦ'ne
  have hwneg : σ.w (-tt) = σ.w σ.Φ := by rw [w_neg' σ tt httne, htw]
  have hdegΦ' : σ'.Φ.degree = σ.Φ.degree := by
    rw [hΦ'eq]; exact Polynomial.degree_sub_eq_left_of_degree_lt htc
  have hRtt : σ.R (-tt) = - LaurentPolynomial.C cc := by
    rw [hcore.R_neg, htR, LaurentPolynomial.T_zero, mul_one]
  -- the recentered key keeps the weight: w(Φ') = w(Φ)
  have hwmin : σ.w σ.Φ ≤ σ.w σ'.Φ := by
    have h := σ.hwult σ.Φ (-tt) hΦne httne' hΦ'ne2
    rw [hwneg, min_self] at h
    rw [hΦ'eq, sub_eq_add_neg]
    exact h
  have hwΦ' : σ.w σ'.Φ = σ.w σ.Φ := by
    rcases eq_or_lt_of_le hwmin with heq | hlt
    · exact heq.symm
    · exfalso
      have hj := hcore.w_jump σ.Φ (-tt) hΦne httne' hΦ'ne2 hwneg.symm
        (by rw [← sub_eq_add_neg, ← hΦ'eq]; exact hlt)
      rw [σ.hRΦ, hs1, hRtt] at hj
      -- hj : T 1 + -C cc = 0, i.e. z = c̃ — impossible (toLaurent is injective, X ≠ C c̃)
      have heqTC : (LaurentPolynomial.T 1 : LaurentPolynomial ↥σ.K)
          = LaurentPolynomial.C cc := add_neg_eq_zero.mp hj
      rw [← Polynomial.toLaurent_X, ← Polynomial.toLaurent_C] at heqTC
      exact Polynomial.X_ne_C cc (Polynomial.toLaurent_injective heqTC)
  -- the parent residual of the recentered key: R(Φ') = z − c̃
  have hRΦ' : σ.R σ'.Φ = LaurentPolynomial.T 1 - LaurentPolynomial.C cc := by
    have h := σ.hRadd σ.Φ (-tt) hΦne httne' hΦ'ne2 hwneg.symm
      (by rw [← sub_eq_add_neg, ← hΦ'eq]; exact hwΦ')
    rw [← sub_eq_add_neg, ← hΦ'eq, σ.hRΦ, hs1, hRtt, ← sub_eq_add_neg] at h
    exact h
  -- the substitution identity, f by f
  intro f
  rcases eq_or_ne f 0 with hf | hf
  · subst hf
    simp only [Stage.ratRes, Stage.ratResShift, σ'.hR0, σ.hR0, map_zero]
  -- develop f at the child key Φ' (Fact A) and read K1 there (hK1')
  obtain ⟨B, N, hdev⟩ := L0_FactA_exists σ'.Φ σ'.hmonic σ'.hdeg f
  obtain ⟨hBdeg, hBz, hBsum⟩ := hdev
  obtain ⟨hmin, jat, hjN, hjnz, hjw⟩ := hK1' f B N hf ⟨hBdeg, hBz, hBsum⟩
  -- slot bookkeeping
  set A : Finset ℕ := (Finset.range N).filter (fun j => B j ≠ 0) with hA
  set M : Finset ℕ := A.filter (fun j => σ.w (B j) + (j : ℤ) * σ.w σ.Φ = σ.w f) with hM
  set Rt : Finset ℕ := A.filter (fun j => ¬(σ.w (B j) + (j : ℤ) * σ.w σ.Φ = σ.w f)) with hRt
  have hMmem : ∀ j ∈ M, B j ≠ 0 ∧ σ.w (B j) + (j : ℤ) * σ.w σ.Φ = σ.w f := by
    intro j hj
    have h1 := Finset.mem_filter.mp hj
    exact ⟨(Finset.mem_filter.mp h1.1).2, h1.2⟩
  have hTw : ∀ j, B j ≠ 0 → σ.w (B j * σ'.Φ ^ j) = σ.w (B j) + (j : ℤ) * σ.w σ.Φ := by
    intro j hBj
    rw [σ.hwmul (B j) (σ'.Φ ^ j) hBj (pow_ne_zero _ hΦ'ne), w_pow' σ σ'.Φ hΦ'ne, hwΦ']
  have hT0M : ∀ j ∈ M, B j * σ'.Φ ^ j ≠ 0 := fun j hj =>
    mul_ne_zero (hMmem j hj).1 (pow_ne_zero _ hΦ'ne)
  have hTwM : ∀ j ∈ M, σ.w (B j * σ'.Φ ^ j) = σ.w f := fun j hj => by
    rw [hTw j (hMmem j hj).1]; exact (hMmem j hj).2
  have hsubA : ∀ S ⊆ A, S.Nonempty → (∑ j ∈ S, B j * σ'.Φ ^ j) ≠ 0 := by
    intro S hS hSne
    obtain ⟨j₀, hj₀⟩ := hSne
    exact subsum_ne_zero σ'.Φ σ'.hmonic B hBdeg S j₀ hj₀
      (Finset.mem_filter.mp (hS hj₀)).2
  have hsubM : ∀ S ⊆ M, S.Nonempty → (∑ j ∈ S, B j * σ'.Φ ^ j) ≠ 0 :=
    fun S hS hSne => hsubA S (hS.trans (Finset.filter_subset _ _)) hSne
  have hMne : M.Nonempty :=
    ⟨jat, Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjN, hjnz⟩, hjw.symm⟩⟩
  have hfminne : (∑ j ∈ M, B j * σ'.Φ ^ j) ≠ 0 := hsubM M (Finset.Subset.refl M) hMne
  -- f splits into the minimizing slots plus the strictly-heavier rest
  have hfA : f = ∑ j ∈ A, B j * σ'.Φ ^ j := by
    rw [hBsum]
    refine (Finset.sum_filter_of_ne ?_).symm
    intro j hj hne hBj
    exact hne (by rw [hBj, zero_mul])
  have hkey : f = (∑ j ∈ M, B j * σ'.Φ ^ j) + ∑ j ∈ Rt, B j * σ'.Φ ^ j := by
    rw [hfA]
    exact (Finset.sum_filter_add_sum_filter_not A _ _).symm
  -- the trichotomy engine on the minimizing slots, both stages
  obtain ⟨hgeM, heqM, _⟩ := graded_sum σ hcore.w_strict hcore.w_jump
    (fun j => B j * σ'.Φ ^ j) (σ.w f) M hT0M hTwM hsubM hMne
  obtain ⟨_, heqM', _⟩ := graded_sum σ' hcore'.w_strict hcore'.w_jump
    (fun j => B j * σ'.Φ ^ j) (σ.w f) M hT0M
    (fun j hj => (hww (B j * σ'.Φ ^ j)).trans (hTwM j hj)) hsubM hMne
  -- R f = R (minimizing part) on both stages, and its weight is w f
  have hthree : σ.w (∑ j ∈ M, B j * σ'.Φ ^ j) = σ.w f ∧
      σ.R f = σ.R (∑ j ∈ M, B j * σ'.Φ ^ j) ∧
      σ'.R f = σ'.R (∑ j ∈ M, B j * σ'.Φ ^ j) := by
    rcases Rt.eq_empty_or_nonempty with hRtE | hRtne
    · have hfeq : f = ∑ j ∈ M, B j * σ'.Φ ^ j := by
        rw [hkey, hRtE, Finset.sum_empty, add_zero]
      rw [← hfeq]
      exact ⟨rfl, rfl, rfl⟩
    · have hfrne : (∑ j ∈ Rt, B j * σ'.Φ ^ j) ≠ 0 :=
        hsubA Rt (Finset.filter_subset _ _) hRtne
      have hfrw : σ.w f + 1 ≤ σ.w (∑ j ∈ Rt, B j * σ'.Φ ^ j) := by
        refine w_sum_ge σ _ (σ.w f + 1) Rt (fun j hj => ?_) (fun j hj => ?_)
          (fun S hS hSne => hsubA S (hS.trans (Finset.filter_subset _ _)) hSne) hRtne
        · exact mul_ne_zero (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
            (pow_ne_zero _ hΦ'ne)
        · have hjA := (Finset.mem_filter.mp hj).1
          have hjne := (Finset.mem_filter.mp hj).2
          have hBj := (Finset.mem_filter.mp hjA).2
          have hjN' := Finset.mem_range.mp (Finset.mem_filter.mp hjA).1
          rw [hTw j hBj]
          exact Int.add_one_le_iff.mpr (lt_of_le_of_ne (hmin j hjN' hBj) (Ne.symm hjne))
      have hwfmin : σ.w (∑ j ∈ M, B j * σ'.Φ ^ j) = σ.w f := by
        by_contra hne2
        have hlt : σ.w f < σ.w (∑ j ∈ M, B j * σ'.Φ ^ j) :=
          lt_of_le_of_ne hgeM (Ne.symm hne2)
        have h := σ.hwult (∑ j ∈ M, B j * σ'.Φ ^ j) (∑ j ∈ Rt, B j * σ'.Φ ^ j)
          hfminne hfrne (by rw [← hkey]; exact hf)
        rw [← hkey] at h
        exact absurd h (not_le.mpr (lt_min hlt (by omega)))
      refine ⟨hwfmin, ?_, ?_⟩
      · conv_lhs => rw [hkey]
        exact σ.hRlt _ _ hfminne hfrne (by rw [← hkey]; exact hf)
          (by rw [hwfmin]; omega)
      · conv_lhs => rw [hkey]
        exact σ'.hRlt _ _ hfminne hfrne (by rw [← hkey]; exact hf)
          (by rw [hww, hww, hwfmin]; omega)
  have hRdecσ : σ.R (∑ j ∈ M, B j * σ'.Φ ^ j) = ∑ j ∈ M, σ.R (B j * σ'.Φ ^ j) :=
    heqM hthree.1
  have hRdecσ' : σ'.R (∑ j ∈ M, B j * σ'.Φ ^ j) = ∑ j ∈ M, σ'.R (B j * σ'.Φ ^ j) :=
    heqM' (by rw [hww]; exact hthree.1)
  -- assemble in the common localization: both sides become Σ ratRes(B_j)·ζ^j
  have hXchild : LaurentPolynomial.eval₂ ((algebraMap F (RatFunc F)).comp σ'.K.subtype)
      (ratX F) (LaurentPolynomial.T (1 : ℤ)) = RatFunc.X := by
    rw [LaurentPolynomial.eval₂_T, zpow_one]
    rfl
  have hXpar : LaurentPolynomial.eval₂ ((algebraMap F (RatFunc F)).comp σ.K.subtype)
      (ratXShift ((cc : ↥σ.K) : F))
      (LaurentPolynomial.T (1 : ℤ) - LaurentPolynomial.C cc) = RatFunc.X := by
    rw [map_sub, LaurentPolynomial.eval₂_T, zpow_one, LaurentPolynomial.eval₂_C,
      RingHom.comp_apply]
    show (RatFunc.X + RatFunc.C ((cc : ↥σ.K) : F))
        - algebraMap F (RatFunc F) (σ.K.subtype cc) = RatFunc.X
    rw [RatFunc.algebraMap_eq_C, Subfield.coe_subtype]
    exact add_sub_cancel_right _ _
  simp only [Stage.ratRes, Stage.ratResShift]
  rw [hthree.2.1, hthree.2.2, hRdecσ, hRdecσ', map_sum, map_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hBj : B j ≠ 0 := (hMmem j hj).1
  have hinCj : inC σ.Φ (B j) := by
    show (B j).degree < σ.Φ.degree
    rw [← hdegΦ']
    exact hBdeg j
  -- the coefficient residual is a position-0 constant (e = 1, t = 0)
  obtain ⟨c, hc⟩ := σ.hS5 (B j) hBj hinCj
  have hcC : σ.R (B j) = LaurentPolynomial.C (c : ↥σ.K) := by
    rw [hc, ht0, neg_zero, zero_mul, LaurentPolynomial.T_zero, mul_one]
  have hcoeffj : LaurentPolynomial.eval₂ ((algebraMap F (RatFunc F)).comp σ'.K.subtype)
      (ratX F) (σ'.R (B j))
      = LaurentPolynomial.eval₂ ((algebraMap F (RatFunc F)).comp σ.K.subtype)
        (ratXShift ((cc : ↥σ.K) : F)) (σ.R (B j)) := by
    have h1 : Stage.ratRes σ' (B j) = Stage.ratRes σ (B j) := hcoeffR (B j) hinCj
    simp only [Stage.ratRes] at h1
    rw [h1, hcC, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_C]
  -- slotwise: R'(B_j·Φ'^j) = R'(B_j)·z^j vs R(B_j·Φ'^j) = R(B_j)·(z − c̃)^j
  rw [σ.hRmul (B j) (σ'.Φ ^ j) hBj (pow_ne_zero _ hΦ'ne), R_pow' σ σ'.Φ hΦ'ne,
    σ'.hRmul (B j) (σ'.Φ ^ j) hBj (pow_ne_zero _ hΦ'ne), R_pow' σ' σ'.Φ hΦ'ne,
    hRΦ', σ'.hRΦ, hs1', map_mul, map_mul, map_pow, map_pow, hXchild, hXpar, hcoeffj]

end LeanUrat.Moves
