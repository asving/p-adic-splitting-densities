/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT

/-!
# Moves/L2_slotDecomp_R4 — (S3) slot decomposition + Y-transcendence (D.2/D.3)

AUDIT-3 REPAIR. Carries the D.1(b) tie laws (`hstrict`, `hjump`, `hneg`) as explicit
hypotheses (StageCore fields), so this unit does not consume `StageCore` (no circularity).

Core facts (both `SlotDecomp` clauses hinge on them):
* each active slot's residual is a monomial `single (p j) (c j)`, `c j ≠ 0` (from `hS5`, `hRΦ`);
* `e·(p j) = j − t·γ`, so distinct slots have DISTINCT `z`-positions;
* a distinct-position monomial sum is non-cancelling (coefficient extraction).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.Moves

open Polynomial

/-- Coefficient extraction: in a distinct-position sum of monomials, the coefficient at
`p m` is exactly `c m`. -/
private lemma coeff_extract {ι : Type*} {A : Type*} [AddCommMonoid A]
    (S : Finset ι) (p : ι → ℤ) (c : ι → A) (m : ι) (hm : m ∈ S)
    (hinj : ∀ j ∈ S, p j = p m → j = m) :
    (∑ j ∈ S, Finsupp.single (p j) (c j)) (p m) = c m := by
  rw [Finsupp.finset_sum_apply]
  rw [Finset.sum_eq_single m
    (fun j hj hjm => by rw [Finsupp.single_apply, if_neg (fun h => hjm (hinj j hj h))])
    (fun h => absurd hm h)]
  rw [Finsupp.single_apply, if_pos rfl]

/-- `(z^s)^j = z^{s·j}`. -/
private lemma T_pow_s {R : Type*} [CommRing R] (s : ℤ) (j : ℕ) :
    (LaurentPolynomial.T s : LaurentPolynomial R) ^ j = LaurentPolynomial.T (s * j) := by
  induction j with
  | zero => rw [pow_zero, Nat.cast_zero, mul_zero, LaurentPolynomial.T_zero]
  | succ n ih =>
    rw [pow_succ, ih, ← LaurentPolynomial.T_add]
    congr 1; push_cast; ring

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- `R 1 = 1`. -/
private lemma R_one (σ : Stage p F) : σ.R 1 = 1 := by
  have h := σ.hRmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  exact (mul_left_cancel₀ (σ.hRne 1 one_ne_zero) (by rw [mul_one]; exact h)).symm

/-- `R(Φ^j) = (R Φ)^j`. -/
private lemma R_Phi_pow (σ : Stage p F) (j : ℕ) : σ.R (σ.Φ ^ j) = (σ.R σ.Φ) ^ j := by
  have hΦ : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  induction j with
  | zero => rw [pow_zero, pow_zero, R_one]
  | succ n ih =>
    rw [pow_succ, σ.hRmul (σ.Φ ^ n) σ.Φ (pow_ne_zero n hΦ) hΦ, ih, pow_succ]

/-- The slot residual (Part-1 form = Part-2 form). -/
private lemma R_slot_eq (σ : Stage p F) (B : Polynomial ℤ_[p]) (j : ℕ) (hB : B ≠ 0) :
    σ.R (B * σ.Φ ^ j) = σ.R B * (σ.R σ.Φ) ^ j := by
  rw [σ.hRmul B (σ.Φ ^ j) hB (pow_ne_zero j σ.hmonic.ne_zero), R_Phi_pow]

/-- Each active slot's residual is a monomial `single (pos) (unit)`. -/
private lemma slot_data (σ : Stage p F) (B : Polynomial ℤ_[p]) (j : ℕ)
    (hB : B ≠ 0) (hC : inC σ.Φ B) :
    ∃ c : (↥σ.K)ˣ,
      σ.R B * (σ.R σ.Φ) ^ j
        = Finsupp.single (-σ.t * σ.wPrev B + σ.s * j) (c : ↥σ.K) := by
  obtain ⟨c, hc⟩ := σ.hS5 B hB hC
  refine ⟨c, ?_⟩
  rw [hc, σ.hRΦ, T_pow_s, mul_assoc, ← LaurentPolynomial.T_add,
    ← LaurentPolynomial.single_eq_C_mul_T]

/-- Position law: `e·(pos) = j − t·γ` — the source of DISTINCTNESS across slots. -/
private lemma e_pos (σ : Stage p F) (B : Polynomial ℤ_[p]) (j : ℕ) (γ : ℤ)
    (hB : B ≠ 0) (hC : inC σ.Φ B) (hg : σ.w B + (j : ℤ) * (σ.h : ℤ) = γ) :
    (σ.e : ℤ) * (-σ.t * σ.wPrev B + σ.s * j) = (j : ℤ) - σ.t * γ := by
  have hst : σ.w B = (σ.e : ℤ) * σ.wPrev B := σ.hStretch B hB hC
  have hg' : (σ.e : ℤ) * σ.wPrev B + (j : ℤ) * (σ.h : ℤ) = γ := by rw [← hst]; exact hg
  linear_combination (-σ.t) * hg' + (j : ℤ) * σ.hbez

/-- **DECOMPOSITION engine.** A finite sum of nonzero equal-weight slots whose residuals are
distinct-position monomials: `R` is additive across it, weight stays `γ`, sum is nonzero. -/
private lemma decomp_sum (σ : Stage p F)
    (hjump : ∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 → σ.w f = σ.w g → σ.w f < σ.w (f + g) → σ.R f + σ.R g = 0)
    (hneg : ∀ f, σ.R (-f) = - σ.R f)
    (γ : ℤ) (T : ℕ → Polynomial ℤ_[p]) (pos : ℕ → ℤ) (c : ℕ → ↥σ.K) (S : Finset ℕ)
    (hT0 : ∀ j ∈ S, T j ≠ 0) (hTw : ∀ j ∈ S, σ.w (T j) = γ)
    (hTR : ∀ j ∈ S, σ.R (T j) = Finsupp.single (pos j) (c j)) (hc : ∀ j ∈ S, c j ≠ 0)
    (hinj : ∀ j ∈ S, ∀ k ∈ S, pos j = pos k → j = k) (hne : S.Nonempty) :
    σ.R (∑ j ∈ S, T j) = ∑ j ∈ S, σ.R (T j) ∧ σ.w (∑ j ∈ S, T j) = γ ∧ (∑ j ∈ S, T j) ≠ 0 := by
  classical
  revert hT0 hTw hTR hc hinj hne
  refine Finset.induction_on S ?_ ?_
  · intro _ _ _ _ _ hne; exact absurd hne (by simp)
  · intro a S' ha ih hT0 hTw hTR hc hinj _
    simp only [Finset.sum_insert ha]
    have hwta : σ.w (T a) = γ := hTw a (Finset.mem_insert_self a S')
    have hTa0 : T a ≠ 0 := hT0 a (Finset.mem_insert_self a S')
    rcases S'.eq_empty_or_nonempty with hE | hE
    · subst hE; simp only [Finset.sum_empty, add_zero]; exact ⟨trivial, hwta, hTa0⟩
    obtain ⟨hRP, hwP, hP0⟩ := ih (fun j hj => hT0 j (Finset.mem_insert_of_mem hj))
      (fun j hj => hTw j (Finset.mem_insert_of_mem hj))
      (fun j hj => hTR j (Finset.mem_insert_of_mem hj))
      (fun j hj => hc j (Finset.mem_insert_of_mem hj))
      (fun j hj k hk => hinj j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)) hE
    have hMQ : σ.R (T a) + σ.R (∑ j ∈ S', T j)
        = ∑ j ∈ insert a S', Finsupp.single (pos j) (c j) := by
      rw [Finset.sum_insert ha, hTR a (Finset.mem_insert_self a S'), hRP]
      congr 1
      exact Finset.sum_congr rfl (fun j hj => hTR j (Finset.mem_insert_of_mem hj))
    have hMval : ((σ.R (T a) + σ.R (∑ j ∈ S', T j) : LaurentPolynomial ↥σ.K)
        : ℤ →₀ ↥σ.K) (pos a) = c a := by
      rw [hMQ]
      exact coeff_extract (insert a S') pos c a (Finset.mem_insert_self a S')
        (fun j hj hpj => hinj j hj a (Finset.mem_insert_self a S') hpj)
    have hMne : σ.R (T a) + σ.R (∑ j ∈ S', T j) ≠ 0 := by
      intro hz; rw [hz] at hMval
      exact hc a (Finset.mem_insert_self a S') hMval.symm
    have h3 : T a + ∑ j ∈ S', T j ≠ 0 := by
      intro hzero
      apply hMne
      have hxe : T a = -(∑ j ∈ S', T j) := eq_neg_of_add_eq_zero_left hzero
      rw [hxe, hneg]; exact neg_add_cancel _
    have hge : γ ≤ σ.w (T a + ∑ j ∈ S', T j) := by
      have h := σ.hwult (T a) (∑ j ∈ S', T j) hTa0 hP0 h3
      rw [hwta, hwP, min_self] at h; exact h
    have h2 : σ.w (T a + ∑ j ∈ S', T j) = γ := by
      refine le_antisymm ?_ hge
      by_contra hlt; push_neg at hlt
      exact hMne (hjump (T a) (∑ j ∈ S', T j) hTa0 hP0 h3 (by rw [hwta, hwP])
        (by rw [hwta]; exact hlt))
    have h1 : σ.R (T a + ∑ j ∈ S', T j) = σ.R (T a) + ∑ j ∈ S', σ.R (T j) := by
      rw [σ.hRadd (T a) (∑ j ∈ S', T j) hTa0 hP0 h3 (by rw [hwta, hwP]) (by rw [h2, hwta]), hRP]
    exact ⟨h1, h2, h3⟩

/-- `w 1 = 0`. -/
private lemma w_one (σ : Stage p F) : σ.w 1 = 0 := by
  have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h; linarith

/-- `w(-f) = w f` (via the unit `-1`). -/
private lemma w_neg (σ : Stage p F) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) :
    σ.w (-f) = σ.w f := by
  have hn1 : (-1 : Polynomial ℤ_[p]) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have key := σ.hwmul (-1) (-1) hn1 hn1
  rw [neg_one_mul, neg_neg, w_one σ] at key
  have hw1 : σ.w (-1 : Polynomial ℤ_[p]) = 0 := by linarith
  have h2 := σ.hwmul (-1) f hn1 hf
  rw [neg_one_mul, hw1, zero_add] at h2; exact h2

/-- **DECOMPOSITION engine** (graded trichotomy induction): every partial sum of equal-weight
slots is (a) zero with vanishing residual sum, (b) at weight `γ` with `R` additive so far, or
(c) jumped strictly above `γ` with vanishing residual sum. Needs no monomial structure — only
the tie laws `hstrict`/`hjump`/`hneg` and the `Stage` residual laws. -/
private lemma trichotomy_sum (σ : Stage p F)
    (hstrict : ∀ f g, f ≠ 0 → g ≠ 0 → σ.w f < σ.w g → σ.w (f + g) = σ.w f)
    (hjump : ∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 → σ.w f = σ.w g → σ.w f < σ.w (f + g) →
      σ.R f + σ.R g = 0)
    (hneg : ∀ f, σ.R (-f) = - σ.R f)
    (γ : ℤ) (T : ℕ → Polynomial ℤ_[p]) (hTw : ∀ j, T j ≠ 0 → σ.w (T j) = γ) (k : ℕ) :
    ((∑ j ∈ Finset.range k, T j) = 0 ∧ (∑ j ∈ Finset.range k, σ.R (T j)) = 0)
    ∨ ((∑ j ∈ Finset.range k, T j) ≠ 0 ∧ σ.w (∑ j ∈ Finset.range k, T j) = γ ∧
        σ.R (∑ j ∈ Finset.range k, T j) = ∑ j ∈ Finset.range k, σ.R (T j))
    ∨ ((∑ j ∈ Finset.range k, T j) ≠ 0 ∧ γ < σ.w (∑ j ∈ Finset.range k, T j) ∧
        (∑ j ∈ Finset.range k, σ.R (T j)) = 0) := by
  induction k with
  | zero => left; simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    rcases eq_or_ne (T n) 0 with hTn | hTn
    · rw [hTn, σ.hR0, add_zero, add_zero]; exact ih
    · have hwn : σ.w (T n) = γ := hTw n hTn
      rcases ih with ⟨hP0, hQ0⟩ | ⟨hPne, hPw, hPR⟩ | ⟨hPne, hPgt, hQ0⟩
      · -- (a) prefix vanished: the new term starts a fresh weight-γ state
        rw [hP0, hQ0, zero_add, zero_add]
        right; left; exact ⟨hTn, hwn, rfl⟩
      · -- (b) prefix at weight γ with R additive
        rcases eq_or_ne ((∑ j ∈ Finset.range n, T j) + T n) 0 with hz | hz
        · -- new sum vanishes: term = −prefix, so residual sum cancels (hneg)
          left
          refine ⟨hz, ?_⟩
          have hTneg : T n = -(∑ j ∈ Finset.range n, T j) :=
            eq_neg_of_add_eq_zero_right hz
          rw [← hPR, hTneg, hneg]
          exact add_neg_cancel _
        · have hge : γ ≤ σ.w ((∑ j ∈ Finset.range n, T j) + T n) := by
            have h := σ.hwult _ _ hPne hTn hz
            rw [hPw, hwn, min_self] at h; exact h
          rcases hge.eq_or_lt with heq | hlt
          · -- stays at γ: hRadd applies
            right; left
            refine ⟨hz, heq.symm, ?_⟩
            rw [σ.hRadd _ _ hPne hTn hz (hPw.trans hwn.symm) (heq.symm.trans hPw.symm), hPR]
          · -- weight jump: hjump kills the residual sum
            right; right
            refine ⟨hz, hlt, ?_⟩
            rw [← hPR]
            exact hjump _ _ hPne hTn hz (hPw.trans hwn.symm) (by rw [hPw]; exact hlt)
      · -- (c) prefix jumped above γ (residual sum already 0): new term dominates
        have hz : (∑ j ∈ Finset.range n, T j) + T n ≠ 0 := by
          intro h0
          have hTneg : T n = -(∑ j ∈ Finset.range n, T j) :=
            eq_neg_of_add_eq_zero_right h0
          rw [hTneg, w_neg σ _ hPne] at hwn
          omega
        have hwPT : σ.w ((∑ j ∈ Finset.range n, T j) + T n) = γ := by
          rw [add_comm (∑ j ∈ Finset.range n, T j) (T n),
            hstrict (T n) _ hTn hPne (by rw [hwn]; exact hPgt), hwn]
        right; left
        refine ⟨hz, hwPT, ?_⟩
        have hRPT : σ.R ((∑ j ∈ Finset.range n, T j) + T n) = σ.R (T n) := by
          rw [add_comm (∑ j ∈ Finset.range n, T j) (T n)]
          exact σ.hRlt (T n) _ hTn hPne
            (by rw [add_comm (T n) (∑ j ∈ Finset.range n, T j)]; exact hz)
            (by rw [hwn]; exact hPgt)
        rw [hRPT, hQ0, zero_add]

theorem L2_slotDecomp {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (hstrict : ∀ f g, f ≠ 0 → g ≠ 0 → σ.w f < σ.w g → σ.w (f + g) = σ.w f) (hjump : ∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 → σ.w f = σ.w g → σ.w f < σ.w (f + g) → σ.R f + σ.R g = 0) (hneg : ∀ f, σ.R (-f) = - σ.R f) : SlotDecomp σ := by
  constructor
  · -- DECOMPOSITION (graded trichotomy induction on partial sums)
    intro B N γ hvan hslot hne hw
    have hTw : ∀ j, B j * σ.Φ ^ j ≠ 0 → σ.w (B j * σ.Φ ^ j) = γ := by
      intro j hTj
      have hBj : B j ≠ 0 := fun h => hTj (by rw [h, zero_mul])
      have hjN : j < N := by
        by_contra hge; push_neg at hge
        exact hBj (hvan j hge)
      exact hslot j hjN hBj
    rcases trichotomy_sum σ hstrict hjump hneg γ (fun j => B j * σ.Φ ^ j) hTw N with
      ⟨hP0, _⟩ | ⟨_, _, hPR⟩ | ⟨_, hPgt, _⟩
    · exact absurd hP0 hne
    · exact hPR
    · exact absurd hw (ne_of_gt hPgt)
  · -- INDEPENDENCE / Y-transcendence (distinct-position coefficient extraction)
    intro B N γ hslot hsum j hjN
    by_contra hBj
    set pos : ℕ → ℤ := fun k => -σ.t * σ.wPrev (B k) + σ.s * (k : ℤ) with hposdef
    have hinCj : inC σ.Φ (B j) := (hslot j hjN hBj).1
    have hwj : σ.w (B j) + (j : ℤ) * (σ.h : ℤ) = γ := by
      rw [← σ.hwΦ]; exact (hslot j hjN hBj).2
    obtain ⟨cj, hcj⟩ := slot_data σ (B j) j hBj hinCj
    -- positions are distinct across active slots
    have hdist : ∀ k, k < N → B k ≠ 0 → pos k = pos j → k = j := by
      intro k hk hBk hpk
      have ek := e_pos σ (B k) k γ hBk (hslot k hk hBk).1 (by rw [← σ.hwΦ]; exact (hslot k hk hBk).2)
      have ej := e_pos σ (B j) j γ hBj hinCj hwj
      have : (k : ℤ) = (j : ℤ) := by
        have := congrArg (fun x => (σ.e : ℤ) * x) hpk
        simp only [hposdef] at this ek ej ⊢; omega
      exact_mod_cast this
    -- coefficient at pos j of the (vanishing) sum equals cj
    have hval : (∑ k ∈ Finset.range N, σ.R (B k) * (σ.R σ.Φ) ^ k : ℤ →₀ ↥σ.K) (pos j)
        = (cj : ↥σ.K) := by
      rw [Finsupp.finsetSum_apply]
      rw [Finset.sum_eq_single j]
      · rw [hcj, Finsupp.single_apply, if_pos rfl]
      · intro k hk hkj
        rcases eq_or_ne (B k) 0 with hBk | hBk
        · rw [hBk, σ.hR0, zero_mul]; rfl
        · obtain ⟨ck, hck⟩ := slot_data σ (B k) k hBk (hslot k (Finset.mem_range.mp hk) hBk).1
          rw [hck, Finsupp.single_apply, if_neg]
          intro hpe
          exact hkj (hdist k (Finset.mem_range.mp hk) hBk hpe)
      · intro h; exact absurd (Finset.mem_range.mpr hjN) h
    have h' : (∑ k ∈ Finset.range N, σ.R (B k) * (σ.R σ.Φ) ^ k : ℤ →₀ ↥σ.K) = 0 := hsum
    have hz := hval.symm.trans (DFunLike.congr_fun h' (pos j))
    exact Units.ne_zero cj (by simpa using hz)

end LeanUrat.Moves
