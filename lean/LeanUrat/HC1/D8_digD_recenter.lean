/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsTower

/-!
# HC1.D8_digD_recenter — a recentering preserves the 𝒟-typing

moves_ref: MOVES 2668 "S5: coefficient digits LITERALLY unchanged (same C, same v,
same T; position 0)" + 1523–1526 (e_birth vs e_read). deps: DefsD, Moves DefsCore
(`IsRecenteringCore`). difficulty: easy. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- A Laurent monomial `c·zᵏ` with `c ≠ 0` determines its exponent and scalar uniquely
(single-support). Used to pin the choice-extracted data inside `digD`. -/
private lemma mono_unit_eq {K : Type*} [Field K] {c₁ c₂ : K} {k₁ k₂ : ℤ}
    (hc₁ : c₁ ≠ 0)
    (h : LaurentPolynomial.C c₁ * LaurentPolynomial.T k₁
        = LaurentPolynomial.C c₂ * LaurentPolynomial.T k₂) :
    k₁ = k₂ ∧ c₁ = c₂ := by
  rw [← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T] at h
  have h' : Finsupp.single k₁ c₁ = Finsupp.single k₂ c₂ := h
  rw [Finsupp.single_eq_single_iff] at h'
  rcases h' with ⟨hk, hc⟩ | ⟨h0, _⟩
  · exact ⟨hk, hc⟩
  · exact absurd h0 hc₁

/-- At an unramified read (`σ.e = 1`, hence `σ.t = 0`) every coefficient `B` has residual
`σ.R B = C c · z⁰`, so its `digD` collapses to the position-0 generator carrying the
`digPrime` scalar. This is the (S5) shape "same C, same v, same T; position 0". -/
private lemma digD_eq_dOf_digPrime {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (he : σ.e = 1) (zbar : Fˣ) (e_b : ℕ) [NeZero e_b]
    (B : Polynomial ℤ_[p]) (hB : B ≠ 0) (hBc : inC σ.Φ B) :
    σ.digD zbar e_b B = dOf (0 : ZMod e_b) (σ.digPrime zbar B) := by
  have ht : σ.t = 0 := σ.he1t he
  obtain ⟨c, hc⟩ := σ.hS5 B hB hBc
  rw [ht] at hc
  simp only [neg_zero, zero_mul] at hc
  -- hc : σ.R B = C ↑c * T 0
  have hmono : IsMonomialUnit (σ.R B) := ⟨c, 0, hc⟩
  -- the digit's `digPrime` scalar is exactly `↑c`
  have hdp : σ.digPrime zbar B = ((c : ↥σ.K) : F) := by
    rw [Stage.digPrime, hc, LaurentPolynomial.eval₂_C_mul_T]
    simp
  -- pin the choice-extracted exponent/scalar via uniqueness
  obtain ⟨hk, hcoe⟩ :=
    mono_unit_eq (Units.ne_zero hmono.choose)
      (hmono.choose_spec.choose_spec.symm.trans hc)
  unfold Stage.digD
  rw [dif_pos hmono, hk, hcoe, hdp]
  simp only [Int.cast_zero, ZMod.val_zero, Nat.cast_zero, sub_zero, EuclideanDomain.zero_div,
    zpow_zero, Units.val_one, mul_one]

/-- Unit D8: coefficients' birth cosets ride through e_read = 1 moves untouched. -/
theorem D8_digD_recenter {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ σ' : Stage p F) (cc : ↥σ.K) (tt : Polynomial ℤ_[p])
    (hrec : IsRecenteringCore σ σ' cc tt) (zbar : Fˣ) (e_b : ℕ) [NeZero e_b]
    (B : Polynomial ℤ_[p]) (hB : B ≠ 0) (hBc : inC σ.Φ B) :
    σ'.digD zbar e_b B = σ.digD zbar e_b B := by
  obtain ⟨he, he', _hcc, htt, _httne, _htw, _hRtt, hΦ', _hw, _hwp, _hK, _hFQ, _hwset, hdig⟩ :=
    hrec.base
  -- `B` is a coefficient of `σ'.Φ` too: the recentering keeps the key's degree
  have hdegΦ : σ'.Φ.degree = σ.Φ.degree := by
    rw [hΦ']; exact Polynomial.degree_sub_eq_left_of_degree_lt htt
  have hBc' : inC σ'.Φ B := by
    rw [inC, hdegΦ]; exact hBc
  rw [digD_eq_dOf_digPrime σ' he' zbar e_b B hB hBc',
    digD_eq_dOf_digPrime σ he zbar e_b B hB hBc,
    hdig B hB hBc zbar]

end LeanUrat.HC1

#print axioms LeanUrat.HC1.D8_digD_recenter
