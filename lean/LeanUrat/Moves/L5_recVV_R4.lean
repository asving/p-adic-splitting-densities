/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.L3_K1

/-!
# Moves/L5_recVV_R4 — D.10 `v = v'` for the recentered key (round 4)

`Φ' = Φ − tt` is the `g = 1` standard lift of `ψ = X − C c̃` (`e = 1 ⇒ t = 0`), so `L3.K1`
gives `K1(Φ'/v)` directly, and applying that K1 to the length-2 development `Φ' = 1·Φ'^1`
recovers `w(Φ') = w(Φ)`.  No child stage `σ'` appears (round-3 was circular).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open Polynomial LeanUrat.Moves

namespace LeanUrat.Moves

theorem L5_recVV {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (hcore : StageCore σ) (he1 : σ.e = 1) (cc : ↥σ.K) (hcc : cc ≠ 0) (tt : Polynomial ℤ_[p]) (htc : inC σ.Φ tt) (httne : tt ≠ 0) (htw : σ.w tt = σ.w σ.Φ) (htdig : σ.R tt = LaurentPolynomial.C cc * LaurentPolynomial.T (0 : ℤ)) : σ.w (σ.Φ - tt) = σ.w σ.Φ ∧ K1At σ.w (σ.Φ - tt) (σ.w σ.Φ) := by
  have ht0 : σ.t = 0 := σ.he1t he1
  have htlt : tt.degree < σ.Φ.degree := htc
  -- valuation of units
  have w1 : σ.w (1 : Polynomial ℤ_[p]) = 0 := by
    have h := σ.hwmul 1 1 one_ne_zero one_ne_zero; rw [mul_one] at h; omega
  have hn1 : (-1 : Polynomial ℤ_[p]) ≠ 0 := by simp
  have wneg1 : σ.w (-1 : Polynomial ℤ_[p]) = 0 := by
    have h := σ.hwmul (-1) (-1) hn1 hn1; rw [neg_mul_neg, one_mul, w1] at h; omega
  have wnegtt : σ.w (-tt) = σ.w tt := by
    have h := σ.hwmul (-1) tt hn1 httne; rw [neg_one_mul, wneg1] at h; omega
  have hcoeff0 : (Polynomial.X - Polynomial.C cc).coeff 0 = -cc := by simp
  have hinctt : inC σ.Φ (-tt) := by
    show (-tt).degree < σ.Φ.degree; rw [Polynomial.degree_neg]; exact htlt
  -- Φ' = Φ − tt is the g = 1 standard lift of ψ = X − C cc
  have hlift : IsStandardLift σ (Polynomial.X - Polynomial.C cc) 1 (σ.Φ - tt) := by
    refine ⟨Polynomial.monic_X_sub_C cc, Polynomial.natDegree_X_sub_C cc,
      fun k => if k = 0 then -tt else 0, ?_, ?_, ?_⟩
    · intro k hk
      dsimp only
      split_ifs with hk0
      · subst hk0; rw [hcoeff0] at hk; exact absurd (neg_eq_zero.mp hk) hcc
      · rfl
    · intro k hk1 _
      have hk0 : k = 0 := Nat.lt_one_iff.mp hk1
      subst hk0
      refine ⟨?_, ?_, ?_, ?_⟩
      · show -tt ≠ 0
        exact neg_ne_zero.mpr httne
      · show inC σ.Φ (-tt)
        exact hinctt
      · show σ.wPrev (-tt) = _
        have hs := σ.hStretch (-tt) (neg_ne_zero.mpr httne) hinctt
        rw [he1] at hs; push_cast at hs ⊢
        rw [one_mul, wnegtt, htw, σ.hwΦ] at hs
        simp only [mul_one]; omega
      · show σ.R (-tt) = _
        rw [hcore.R_neg tt, htdig, hcoeff0, ht0]
        simp only [neg_zero, zero_mul, map_neg, neg_mul]
    · rw [he1]; simp [sub_eq_add_neg]
  -- part 2: K1(Φ'/v) from L3.K1
  have hK1' := L3_K1 σ (Polynomial.X - Polynomial.C cc) 1
    (Polynomial.natDegree_X_sub_C cc) (Polynomial.irreducible_X_sub_C cc)
    (by intro h; exact hcc (Polynomial.C_eq_zero.mp (sub_eq_self.mp h)))
    (Polynomial.monic_X_sub_C cc) (σ.Φ - tt) hlift
  have hwkey : (σ.e : ℤ) * (σ.h : ℤ) * ((1 : ℕ) : ℤ) = σ.w σ.Φ := by
    rw [σ.hwΦ, he1]; push_cast; ring
  rw [hwkey] at hK1'
  refine ⟨?_, hK1'⟩
  -- part 1: w(Φ') = w(Φ) via K1 on the development Φ' = 1·Φ'^1
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hΦ'deg : (σ.Φ - tt).degree = σ.Φ.degree :=
    Polynomial.degree_sub_eq_left_of_degree_lt htlt
  have hΦ'ne : σ.Φ - tt ≠ 0 := by
    intro h; apply hΦne
    have hd := hΦ'deg; rw [h, Polynomial.degree_zero] at hd
    exact Polynomial.degree_eq_bot.mp hd.symm
  have hdegpos : (0 : WithBot ℕ) < σ.Φ.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp (by have := σ.hdeg; omega)
  have hbot : (⊥ : WithBot ℕ) < (σ.Φ - tt).degree :=
    bot_lt_iff_ne_bot.mpr (fun h => hΦ'ne (Polynomial.degree_eq_bot.mp h))
  have hdev : IsDevelopment (σ.Φ - tt) (σ.Φ - tt)
      (fun j => if j = 1 then (1 : Polynomial ℤ_[p]) else 0) 2 := by
    refine ⟨fun j => ?_, fun j hj => ?_, ?_⟩
    · dsimp only; split_ifs with h
      · rw [Polynomial.degree_one, hΦ'deg]; exact hdegpos
      · rw [Polynomial.degree_zero]; exact hbot
    · dsimp only; split_ifs with h
      · exact absurd h (by omega)
      · rfl
    · simp
  obtain ⟨j, hj2, hBj, hval⟩ :=
    (hK1' (σ.Φ - tt) (fun j => if j = 1 then (1 : Polynomial ℤ_[p]) else 0) 2 hΦ'ne hdev).2
  interval_cases j
  · exact absurd rfl hBj
  · simp [w1] at hval
    omega

end LeanUrat.Moves
