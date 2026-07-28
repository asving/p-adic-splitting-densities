/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsSpine

/-!
# HC1.S11a_coreTransport — the F-5 minimality certificate: the non-twist StageCore
legs transport from the records alone

NEW UNIT (F-5(b), sign-off event 2026-07-28, blueprint §9.6): from `StageCoreL σ` +
`TransitionCoreL σ σ'` + the move's `TransHyp` + σ′'s bare `Stage` laws, derive
StageCore σ′ MINUS the residual twist-class set — i.e. the seven legs
{wPrev_mul, wPrev_ult, reps_nonempty, p_is_rep, w_strict, R_neg, prevIaug}
(the S11 escalation's verified partial transport, transplanted per the §9.6
kernel's own proof sketches: wPrev laws via `child_wPrev` + parent hwmul/hwult;
reps legs via `child_reps`; w_strict via the w(−1) = 0 valuation trick; R_neg via
`child_dig_frame` at B = 1 pinning z̄^{mfun 0} = 1 then B = −1 with parent R_neg;
prevIaug via the move's hiaug + threshold, S8-leg-2's pattern).

VALUE (the certificate): together with the in-file S11 countermodel (the sign
twist, which preserves every recorded witness and breaks exactly
{w_jump, TvecLaw, TvecUnitLaw, CoeffLocLaw, SlotDecomp, CoeffFieldLawCore}), this
unit certifies the F-5 `MoveWitness` enrichment `core' : StageCoreL σ'` is
MINIMAL: everything OUTSIDE the twist class was already derivable — the field adds
exactly the twist-class legs the kernel proved independent. It also shrinks S9c's
per-field work. difficulty: medium. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ## Bare-Stage valuation facts (any stage) -/

private lemma w_one' (σ : Stage p F) : σ.w 1 = 0 := by
  have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  omega

private lemma w_neg_one' (σ : Stage p F) : σ.w (-1) = 0 := by
  have h := σ.hwmul (-1) (-1) (neg_ne_zero.mpr one_ne_zero) (neg_ne_zero.mpr one_ne_zero)
  rw [neg_mul_neg, one_mul, w_one' σ] at h
  omega

private lemma w_neg' (σ : Stage p F) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) :
    σ.w (-f) = σ.w f := by
  have h : (-f) = (-1) * f := by ring
  rw [h, σ.hwmul (-1) f (neg_ne_zero.mpr one_ne_zero) hf, w_neg_one' σ, zero_add]

private lemma R_one' (σ : Stage p F) : σ.R 1 = 1 := by
  have h := σ.hRmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  have hne : σ.R 1 ≠ 0 := σ.hRne 1 one_ne_zero
  exact (mul_left_cancel₀ hne (by rw [mul_one]; exact h)).symm

/-- The w_strict tie law holds for EVERY stage from the bare (S1) laws (the
escalation's "valuation trick"): if the sum vanished, `w g = w (−f) = w f` would
contradict strictness; otherwise squeeze via `hwult` on `f + g` and on
`f = (f + g) + (−g)`. -/
private lemma w_strict_of_bare (σ : Stage p F) (f g : Polynomial ℤ_[p])
    (hf : f ≠ 0) (hg : g ≠ 0) (hlt : σ.w f < σ.w g) : σ.w (f + g) = σ.w f := by
  have hfg : f + g ≠ 0 := by
    intro h0
    have hgf : g = -f := by linear_combination h0
    rw [hgf, w_neg' σ f hf] at hlt
    omega
  have h1 : σ.w f ≤ σ.w (f + g) := by
    have := σ.hwult f g hf hg hfg
    omega
  have h2 : σ.w (f + g) ≤ σ.w f := by
    have hng : (-g) ≠ 0 := neg_ne_zero.mpr hg
    have hsum : (f + g) + (-g) ≠ 0 := by
      intro h0
      exact hf (by linear_combination h0)
    have := σ.hwult (f + g) (-g) hfg hng hsum
    have heq : (f + g) + (-g) = f := by ring
    rw [heq, w_neg' σ g hg] at this
    omega
  omega

/-! ## The main transport -/

/-- **S11a (the F-5 minimality certificate):** the seven non-twist StageCore legs of
the recorded child, from the parent core + the transition record + the move's
interface alone. The residual complement — {w_jump, TvecLaw, TvecUnitLaw,
CoeffLocLaw, SlotDecomp, CoeffFieldLawCore} — is EXACTLY the sign-twist
countermodel's break set (S11's retained certificate), realized instead by S9's
construction (S9d, via the K1 vertex pin). -/
theorem S11a_coreTransport (σ σ' : Stage p F) (hσ : StageCoreL σ)
    {ψ : Polynomial ↥σ.K} {g : ℕ} {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar)
    (tc : TransitionCoreL σ σ' Φhat e' h' zbar) :
    (∀ f g, f ≠ 0 → g ≠ 0 → σ'.wPrev (f * g) = σ'.wPrev f + σ'.wPrev g) ∧
    (∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      min (σ'.wPrev f) (σ'.wPrev g) ≤ σ'.wPrev (f + g)) ∧
    σ'.reps ≠ [] ∧
    (Polynomial.C (p : ℤ_[p])) ∈ σ'.reps ∧
    (∀ f g, f ≠ 0 → g ≠ 0 → σ'.w f < σ'.w g → σ'.w (f + g) = σ'.w f) ∧
    (∀ f, σ'.R (-f) = - σ'.R f) ∧
    ((σ'.e : ℤ) * σ'.wPrev σ'.Φ < (σ'.h : ℤ)) := by
  have hwp := tc.base.child_wPrev
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- wPrev_mul: the child parent valuation IS the parent stage valuation
    intro f g hf hg
    rw [hwp, hwp, hwp]
    exact σ.hwmul f g hf hg
  · -- wPrev_ult
    intro f g hf hg hfg
    rw [hwp, hwp, hwp]
    exact σ.hwult f g hf hg hfg
  · -- reps_nonempty: σ'.reps = σ.reps ++ [σ.Φ]
    rw [tc.base.child_reps]
    simp
  · -- p_is_rep: p rides the parent list into the append
    rw [tc.base.child_reps]
    exact List.mem_append_left _ hσ.core.p_is_rep
  · -- w_strict: bare-Stage valuation trick on σ' itself
    exact w_strict_of_bare σ'
  · -- R_neg: child_dig_frame at B = 1 pins the frame unit at weight 0, then B = −1
    -- with the parent R_neg pins σ'.R (−1) = −1; multiplicativity finishes.
    obtain ⟨mfun, hdig⟩ := tc.child_dig_frame
    -- coefficient membership of the constants ±1
    have hΦdeg : (0 : WithBot ℕ) < Φhat.degree := by
      have h1 : 1 ≤ σ'.Φ.natDegree := σ'.hdeg
      rw [tc.base.child_key] at h1
      have hne : Φhat ≠ 0 := by
        intro h0
        rw [h0, Polynomial.natDegree_zero] at h1
        omega
      rw [Polynomial.degree_eq_natDegree hne]
      exact_mod_cast h1
    have hinC1 : inC Φhat (1 : Polynomial ℤ_[p]) := by
      show (1 : Polynomial ℤ_[p]).degree < Φhat.degree
      rw [Polynomial.degree_one]
      exact hΦdeg
    have hinCm1 : inC Φhat (-1 : Polynomial ℤ_[p]) := by
      show (-1 : Polynomial ℤ_[p]).degree < Φhat.degree
      rw [Polynomial.degree_neg, Polynomial.degree_one]
      exact hΦdeg
    -- the frame unit at parent weight 0 is 1 (read off B = 1)
    obtain ⟨c₁, hc₁R, hc₁F⟩ := hdig 1 one_ne_zero hinC1
    have hw1 : σ.w 1 = 0 := w_one' σ
    have hc₁val : LaurentPolynomial.C ((c₁ : ↥σ'.K)) = 1 := by
      rw [R_one' σ', hw1, mul_zero, LaurentPolynomial.T_zero, mul_one] at hc₁R
      exact hc₁R.symm
    have hc₁one : (c₁ : ↥σ'.K) = 1 := by
      have h2 := congrArg (LaurentPolynomial.eval₂ (RingHom.id ↥σ'.K) (1 : (↥σ'.K)ˣ)) hc₁val
      rwa [LaurentPolynomial.eval₂_C, map_one, RingHom.id_apply] at h2
    have hdig1F : σ.digPrime zbar 1 = 1 := by
      unfold Stage.digPrime
      rw [R_one' σ, map_one]
    have hzm0 : ((zbar ^ (mfun 0) : Fˣ) : F) = 1 := by
      rw [hw1, hc₁one, hdig1F, one_mul] at hc₁F
      rw [← hc₁F]
      simp
    -- the child residual of −1 is −1 (read off B = −1, parent R_neg)
    have hm1ne : (-1 : Polynomial ℤ_[p]) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    obtain ⟨c₂, hc₂R, hc₂F⟩ := hdig (-1) hm1ne hinCm1
    have hwm1 : σ.w (-1) = 0 := w_neg_one' σ
    have hdigm1F : σ.digPrime zbar (-1) = -1 := by
      unfold Stage.digPrime
      rw [hσ.core.R_neg 1, R_one' σ, map_neg, map_one]
    have hc₂F' : ((c₂ : ↥σ'.K) : F) = -1 := by
      rw [hwm1, hdigm1F, hzm0, mul_one] at hc₂F
      exact hc₂F
    have hc₂val : (c₂ : ↥σ'.K) = -1 := by
      have hcast : ((c₂ : ↥σ'.K) : F) = ((-1 : ↥σ'.K) : F) := by
        rw [hc₂F']
        simp
      exact Subtype.coe_injective hcast
    have hRm1 : σ'.R (-1) = -1 := by
      rw [hwm1, mul_zero, LaurentPolynomial.T_zero, mul_one] at hc₂R
      rw [hc₂R, hc₂val]
      simp
    -- assemble: R(−f) = R(−1)·R(f) = −R(f); the f = 0 leg is hR0
    intro f
    by_cases hf : f = 0
    · subst hf
      rw [neg_zero, σ'.hR0, neg_zero]
    · have h : (-f) = (-1) * f := by ring
      rw [h, σ'.hRmul (-1) f hm1ne hf, hRm1]
      ring
  · -- prevIaug: the move's hiaug through the records (S8-leg-2's pattern)
    have he : σ'.e = e' := tc.base.child_e
    have hh : σ'.h = h' := tc.base.child_h
    have hk : σ'.Φ = Φhat := tc.base.child_key
    have hthr : σ'.wPrev Φhat = σ.w Φhat := tc.base.threshold
    rw [he, hh, hk, hthr]
    exact th.hiaug

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S11a_coreTransport
