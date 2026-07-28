/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsSpine
import LeanUrat.HC1.S11_towerSpine
import LeanUrat.Moves.L2_strideRule
import LeanUrat.Moves.L2_P6i_R5_final

/-!
# HC1.S14_wellTypedAnchor — the rev-D¹¹ F7 lemma: a ≥ 0 at e_read = 1 stages

moves_ref: MOVES 2636–2643 (WELL-TYPEDNESS LEMMA (a ≥ 0 here)). deps: S11; Moves
`L2_strideRule` (clean), Stage.he1t. sketch: he1t gives t = 0; hS5 positions 0; K1
slot positions = j ≥ 0. difficulty: medium. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit S14: at an e_read = 1 tower stage, every nonzero f has an anchored
residual with nonnegative anchor — `R(f)` is a z-POLYNOMIAL and `a = ord_z R(f)
≥ 0`. -/
theorem S14_wellTypedAnchor {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (k : Fin (T.K + 1)) (he1 : (T.stg k).e = 1)
    (f : Polynomial ℤ_[p]) (hf : f ≠ 0) :
    ∃ (a : ℤ) (Ranch : Polynomial ↥(T.stg k).K),
      HasAnchorK ((T.stg k).R f) a Ranch ∧ 0 ≤ a := by
  set σ := T.stg k with hσ
  -- (P2) DEF-5: at an `e = 1` read the stage is coefficient-pure — `t = 0`; the Bézout
  -- relation `e·s + h·t = 1` then forces the stride exponent `s = 1`.
  have ht0 : σ.t = 0 := σ.he1t he1
  have hs1 : σ.s = 1 := by
    have hb := σ.hbez
    rw [he1, ht0] at hb
    simpa using hb
  -- The spine (S11) equips level `k` with the round-5 stage core; its `StageCore` part is
  -- what `L2_P6i` consumes.
  have hcore : StageCore σ := ((S11_towerSpine T).1 k).core
  -- P6i clause (4): `R f` lies in the additive span of the weight-`w f` slot images.
  have hmem : σ.R f ∈ AddSubgroup.closure (σ.slotImages (σ.w f)) :=
    (L2_P6i σ hcore (σ.w f)).2.2.2.1 f hf rfl
  -- Every slot image is `z^j·(unit)` with `j ≥ 0` (stride `s = 1`, coefficient digit at
  -- position `-t·wPrev B = 0`), hence a genuine z-POLYNOMIAL; the span of z-polynomials is
  -- z-polynomial, so `R f = toLaurent Q` for some `Q ∈ ↥K[z]`.
  have key : ∀ x : LaurentPolynomial ↥σ.K,
      x ∈ AddSubgroup.closure (σ.slotImages (σ.w f)) →
      ∃ Q : Polynomial ↥σ.K, Polynomial.toLaurent Q = x := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
        obtain ⟨B, j, hB, hBc, hwj, rfl⟩ := hy
        obtain ⟨c, hc⟩ := σ.hS5 B hB hBc
        refine ⟨Polynomial.C (c : ↥σ.K) * Polynomial.X ^ j, ?_⟩
        rw [Polynomial.toLaurent_C_mul_X_pow, L2_strideRule σ B hB hBc j, hc, ht0, hs1]
        simp only [neg_zero, zero_mul, LaurentPolynomial.T_zero, mul_one, one_mul]
    | zero => exact ⟨0, by rw [map_zero]⟩
    | add x y hx hy ihx ihy =>
        obtain ⟨Qx, hQx⟩ := ihx
        obtain ⟨Qy, hQy⟩ := ihy
        exact ⟨Qx + Qy, by rw [map_add, hQx, hQy]⟩
    | neg x hx ih =>
        obtain ⟨Qx, hQx⟩ := ih
        exact ⟨-Qx, by rw [map_neg, hQx]⟩
  obtain ⟨Q, hQ⟩ := key (σ.R f) hmem
  have hRfne : σ.R f ≠ 0 := σ.hRne f hf
  have hQne : Q ≠ 0 := Polynomial.toLaurent_ne_zero.mp (by rw [hQ]; exact hRfne)
  -- Split off the maximal power of `z` (root 0): `Q = z^m·Ranch` with `Ranch(0) ≠ 0`.
  obtain ⟨Ranch, hfac, hndvd⟩ := Q.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hQne 0
  simp only [map_zero, sub_zero] at hfac hndvd
  set m := Q.rootMultiplicity 0 with hm
  refine ⟨(m : ℤ), Ranch, ⟨?_, ?_⟩, ?_⟩
  · -- `Ranch.coeff 0 ≠ 0` — otherwise `z ∣ Ranch`, contradicting the choice of `m`.
    exact fun h0 => hndvd (Polynomial.X_dvd_iff.mpr h0)
  · -- `R f = z^m · Ranch` (the anchor identity), with `m = ord_z R f ≥ 0`.
    rw [← hQ, hfac, map_mul, Polynomial.toLaurent_X_pow]
  · exact_mod_cast Nat.zero_le m

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S14_wellTypedAnchor
