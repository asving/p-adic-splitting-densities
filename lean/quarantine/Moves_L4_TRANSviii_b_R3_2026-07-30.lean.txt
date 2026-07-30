/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT

open Polynomial LeanUrat.Moves

namespace LeanUrat.Moves

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 400000

/- DEPRECATED — superseded by `L4_TRANSviii_b_R4.lean` (sorry-free, adds `hcore : StageCore σ`
per machine-checked finding 1). The :98 I-aug/prev-read sorry is closed there. NOTE:
`L4_TRANSv_R3` currently imports THIS file — re-point it to _R4 (see MANIFEST_REPAIR L4.TRANSv).
Do not import elsewhere. -/

/-- **D.7(viii) S6b': the OFFSET P-LIFT.** Above the CLEAN threshold `σ.w Φ̂ < ν` (the child's
S6b threshold `σ'.wPrev Φ̂ = σ.w Φ̂`, DEF-8), every NEXT-field scalar `a ∈ K⟮z̄⟯` is a residue
digit of some coefficient `B ∈ C_{Φ̂}`, realized at the prescribed weight when `a ≠ 0`. -/
theorem L4_TRANSviii_b {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g) (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (zbar : Fˣ) (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0) (ν : ℤ) (hthr : σ.w Φhat < ν) (a : F) (ha : a ∈ σ.nextField zbar) : ∃ B, inC Φhat B ∧ σ.digPrime zbar B = a ∧ (a ≠ 0 → B ≠ 0 ∧ σ.w B = ν) := by
  -- The standard lift `Φ̂ = Φ^{eg} + Σ_{k<g} t_k Φ^{ek}` is monic (leading term dominates),
  -- hence nonzero — needed so `0 ∈ C_{Φ̂}` (degree ⊥ < deg Φ̂).
  have hΦne : Φhat ≠ 0 := by
    obtain ⟨-, -, tt, htt0, httk, hEq⟩ := hlift
    rw [hEq]
    set d := σ.Φ.natDegree with hd
    have hd1 : 1 ≤ d := σ.hdeg
    have he1 : 1 ≤ σ.e := σ.he
    have hΦ0 : σ.Φ ≠ 0 := σ.hmonic.ne_zero
    have hP0 : (σ.Φ ^ (σ.e * g)) ≠ 0 := pow_ne_zero _ hΦ0
    have hPdeg : (σ.Φ ^ (σ.e * g)).natDegree = (σ.e * g) * d := by
      rw [Polynomial.natDegree_pow]
    -- leading part `Φ^{eg}` is monic; the correction sum has strictly smaller degree.
    refine (Polynomial.Monic.add_of_left (σ.hmonic.pow (σ.e * g)) ?_).ne_zero
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (bot_lt_iff_ne_bot.mpr (fun h => hP0 (Polynomial.degree_eq_bot.mp h)))]
    intro k hk
    simp only [Finset.mem_range] at hk
    -- Each correction term `t_k · Φ^{ek}` has natDegree `< eg·d`, so smaller degree.
    apply Polynomial.degree_lt_degree
    rw [hPdeg]
    have hg1 : 0 < g := lt_of_le_of_lt (Nat.zero_le k) hk
    by_cases htk : tt k = 0
    · rw [htk, zero_mul, Polynomial.natDegree_zero]
      exact Nat.mul_pos (Nat.mul_pos he1 hg1) hd1
    · have hck : ψ.coeff k ≠ 0 := fun h => htk (htt0 k h)
      obtain ⟨-, hinC, -, -⟩ := httk k hk hck
      have hpow0 : (σ.Φ ^ (σ.e * k)) ≠ 0 := pow_ne_zero _ hΦ0
      have hlt : (tt k).natDegree < d :=
        Polynomial.natDegree_lt_natDegree htk hinC
      rw [Polynomial.natDegree_mul htk hpow0, Polynomial.natDegree_pow, ← hd]
      -- goal: (tt k).natDegree + (e·k)·d < (e·g)·d
      have hkg : σ.e * k + σ.e ≤ σ.e * g := by
        have h0 := Nat.mul_le_mul (le_refl σ.e) hk
        rw [Nat.mul_succ] at h0
        exact h0
      have h2 : σ.e * k * d + σ.e * d ≤ σ.e * g * d := by
        have := Nat.mul_le_mul_right d hkg
        rwa [Nat.add_mul] at this
      have h3 : d ≤ σ.e * d := Nat.le_mul_of_pos_left d he1
      omega
  by_cases ha0 : a = 0
  · -- a = 0: the zero coefficient B = 0 realizes it (R 0 = 0 ⟹ dig' = 0), and the
    -- weight-realization clause is vacuous.
    refine ⟨0, ?_, ?_, ?_⟩
    · -- inC Φ̂ 0 : (0).degree = ⊥ < Φ̂.degree
      have hbot : Φhat.degree ≠ ⊥ := fun h => hΦne (Polynomial.degree_eq_bot.mp h)
      simp only [inC, Polynomial.degree_zero]
      exact bot_lt_iff_ne_bot.mpr hbot
    · -- dig'(0) = R(0) evaluated = 0 = a
      simp only [Stage.digPrime, σ.hR0, map_zero, ha0]
    · intro h; exact absurd ha0 h
  · -- a ≠ 0: the OFFSET P-LIFT.  The construction is FORCED by the statement: since lower-weight
    -- development slots dominate `R` (hRlt) and higher-weight ones vanish from it, every nonzero
    -- component of `B` must sit at total weight EXACTLY ν.  The solutions of `e·μ + h·j = ν` with
    -- slot `j ∈ [0, e·g)` are exactly `g` slots `j_k = j* + e·k` (Bézout, gcd(e,h) = 1), whose
    -- evaluated z-positions `s·j_k − t·μ_k` are CONSECUTIVE integers (step `s·e + t·h = 1`) —
    -- matching the K-basis `z̄^{pos₀}, …, z̄^{pos₀+g−1}` of `K⟮z̄⟯ = K[z̄]`.  Writing
    -- `a = Σ_k λ_k·z̄^{pos₀+k}` (λ_k ∈ K), take `B := Σ_{λ_k≠0} u_k·Φ^{j_k}` with `u_k` the (S6b)
    -- realizer of scalar `λ_k` at parent weight `μ_k = (ν − h·j_k)/e`; the distinct positions give
    -- `R`-additivity across the partial sums (derivable from hwult + hRlt + hRadd: a two-term sum
    -- of equal-weight terms whose monomial residuals have distinct positions has nonvanishing
    -- residual sum, forcing `w(f+g) = ν` and `R(f+g) = R f + R g`), so `dig'(B) = a`, `w B = ν`,
    -- and `deg B < e·g·deg Φ = deg Φ̂`.
    --
    -- THE ONE UNBRIDGEABLE STEP: applying `σ.hS6b` at `μ_k` needs `σ.wPrev σ.Φ < μ_k`.  From
    -- `hthr` and `σ.w Φhat = e·h·g` (provable via hK1 on the lift's development) one gets only
    -- `μ_k > h/e`.  MOVES ~2299-2303 closes this via "(I-aug) at the PREVIOUS read":
    -- `h/e > w_prevprev(Φ_prev)`, i.e. `(σ.e : ℤ) * σ.wPrev σ.Φ < σ.h`.  But `σ.wPrev σ.Φ` is
    -- unconstrained by EVERY `Stage` field (hStretch/hS5/hWS/hS6a see only `C_Φ`; enlarging
    -- `wPrev Φ` merely weakens hS6b, so any model can be modified to defeat the threshold without
    -- touching `w`, `R`, or `digPrime`), and no hypothesis of this fenced statement supplies the
    -- bound — it lives in `TransitionData`/(I-aug) data of the PREVIOUS transition, absent here.
    -- NOTE (correcting the round-2 attempt's gap note): S3 `SlotDecomp` / S4 `CoeffFieldLaw` are
    -- NOT the blocker — the additivity is derivable as above and hS6b itself is the scalar
    -- surjectivity once its threshold is cleared.  Honest `sorry` on exactly this bridge.
    sorry

end LeanUrat.Moves
