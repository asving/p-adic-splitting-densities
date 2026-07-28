/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.HC1.T3_htChainWeight
import LeanUrat.HC1.T5_levelSetInGamma
import LeanUrat.HC1.T6_carrierLaws
import LeanUrat.HC1.T12_coordFin
import LeanUrat.Moves.L3_liftMonic

/-!
# HC1.C2_TYPa — TYP(a): the composite computes in_γ' and is ADDITIVE in the digits

moves_ref: MOVES 3795–3807 "in_{γ'}(B) = Σ_{c ∈ L_{γ'}(B)} y′_c·in(m_c) … an
ADDITIVE function … of exactly the level-set digits". deps: T4, T5, T6. The F3-1
repair: additivity in (y_c)_c, NEVER in box points (jet additivity is
p^N-torsion-impossible). The unit-lift additive carry (base-residue carries killed
in the piece) is the one genuinely delicate step. difficulty: HARD. hyp: none.

## The carry wall (conjunct (b)) — how it is closed here

The delicate step is that `digLift` (a choice of (S6a) realizer per digit) is NOT
additive on the nose: the base-residue carry
`κ := digLift (a+b) − digLift a − digLift b` is a nonzero polynomial in general.
It IS killed in the γ'-piece, by two facts proved here from the Stage laws alone:

* **The base wall** (`carry_wall`): if `κ ≠ 0` then `(stg 0).w κ ≥ 1`.  All three
  lifts are weight-0 realizers with residues `C(a+b)`, `C a`, `C b` (existence is
  the Stage law `hS6a` — 0 lies in `weightSet` via the coefficient 1; `digLift 0
  = 0` definitionally by `hRne`).  If `κ` had weight 0 too, then `hRadd` applied
  twice along `digLift a + κ + digLift b = digLift (a+b)` (with `hRlt`/degenerate
  branches giving `R (digLift (a+b)) = R (digLift b)`, i.e. `a = 0`) forces
  `R κ = C(a+b) − C a − C b = C 0 = 0`, contradicting `hRne`.
* **The stretch chain** (`w_chain`): `κ` has degree < deg Φ₀ ≤ deg Φ_k for every
  k, so it is a COEFFICIENT at every stage and `hStretch` + `child_wPrev` (or the
  recentering's `w' = w`) chain the base weight multiplicatively to the top:
  `(stg K).w κ = m·(stg 0).w κ` with `m ≥ 1`.  Hence `w_K(κ·m_c) ≥ 1 + strTop·γ'`
  strictly above the piece (T3 pins `w_K(m_c) = strTop·γ'` on the level set), and
  the class of the total carry vanishes.  No development machinery is needed —
  this is the same induction skeleton as T6's `stage_wC_nonneg`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves
open scoped Classical

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ## Base-stage Gauss-valuation facts -/

/-- Constants are coefficients at every stage (degree ≤ 0 < deg Φ). -/
private lemma degC_lt' (σ : Stage p F) (a : ℤ_[p]) :
    (Polynomial.C a).degree < σ.Φ.degree :=
  lt_of_le_of_lt Polynomial.degree_C_le
    (Polynomial.natDegree_pos_iff_degree_pos.mp (by have := σ.hdeg; omega))

private lemma gaussVal_nonneg (f : Polynomial ℤ_[p]) : 0 ≤ gaussVal f := by
  simp only [gaussVal]
  split
  · apply Finset.le_inf'
    intro i _
    positivity
  · exact le_refl 0

private lemma gaussVal_one : gaussVal (1 : Polynomial ℤ_[p]) = 0 := by
  have h1 : (1 : Polynomial ℤ_[p]) ≠ 0 := one_ne_zero
  have hmem : (0 : ℕ) ∈ (1 : Polynomial ℤ_[p]).support := by
    rw [Polynomial.mem_support_iff, Polynomial.coeff_one_zero]
    exact one_ne_zero
  simp only [gaussVal]
  rw [dif_pos (Polynomial.support_nonempty.mpr h1)]
  apply le_antisymm
  · apply le_trans (Finset.inf'_le _ hmem)
    simp
  · apply Finset.le_inf'
    intro i _
    positivity

private lemma val_neg_one : ((-1 : ℤ_[p])).valuation = 0 := by
  have h := PadicInt.valuation_mul (x := (-1 : ℤ_[p])) (y := (-1 : ℤ_[p]))
    (by norm_num) (by norm_num)
  rw [neg_mul_neg, one_mul, PadicInt.valuation_one] at h
  omega

private lemma gaussVal_C_neg_one : gaussVal (Polynomial.C (-1 : ℤ_[p])) = 0 := by
  have hne : (-1 : ℤ_[p]) ≠ 0 := by norm_num
  have hCne : Polynomial.C (-1 : ℤ_[p]) ≠ 0 := Polynomial.C_ne_zero.mpr hne
  have hmem : (0 : ℕ) ∈ (Polynomial.C (-1 : ℤ_[p])).support := by
    rw [Polynomial.support_C hne]
    exact Finset.mem_singleton_self 0
  simp only [gaussVal]
  rw [dif_pos (Polynomial.support_nonempty.mpr hCne)]
  apply le_antisymm
  · apply le_trans (Finset.inf'_le _ hmem)
    simp [val_neg_one]
  · apply Finset.le_inf'
    intro i _
    positivity

/-- The base-stage weight of a coefficient is the stretched Gauss valuation. -/
private lemma w0_eq (T : Tower p F) (f : Polynomial ℤ_[p]) (hf : f ≠ 0)
    (hdeg : f.degree < (T.stg 0).Φ.degree) :
    (T.stg 0).w f = ((T.stg 0).e : ℤ) * gaussVal f := by
  rw [(T.stg 0).hStretch f hf hdeg, T.base.1.1 f hf]

private lemma w0_nonneg (T : Tower p F) (f : Polynomial ℤ_[p]) (hf : f ≠ 0)
    (hdeg : f.degree < (T.stg 0).Φ.degree) : 0 ≤ (T.stg 0).w f := by
  rw [w0_eq T f hf hdeg]
  exact mul_nonneg (Int.natCast_nonneg _) (gaussVal_nonneg f)

/-- Base-stage weight is negation-invariant (via `w(C(−1)) = e·gaussVal(−1) = 0`). -/
private lemma w0_neg (T : Tower p F) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) :
    (T.stg 0).w (-f) = (T.stg 0).w f := by
  have hCne : Polynomial.C (-1 : ℤ_[p]) ≠ 0 := Polynomial.C_ne_zero.mpr (by norm_num)
  have hCw : (T.stg 0).w (Polynomial.C (-1 : ℤ_[p])) = 0 := by
    rw [w0_eq T _ hCne (degC_lt' (T.stg 0) _), gaussVal_C_neg_one, mul_zero]
  have hneg : -f = Polynomial.C (-1 : ℤ_[p]) * f := by
    rw [map_neg, Polynomial.C_1, neg_one_mul]
  rw [hneg, (T.stg 0).hwmul _ f hCne hf, hCw, zero_add]

/-! ## The digit lift: definitional facts from the Stage laws -/

/-- `digLift 0 = 0`: a nonzero realizer of the zero residue would violate `hRne`. -/
private lemma digLift_zero (T : Tower p F) : T.digLift 0 = 0 := by
  rw [Tower.digLift, dif_neg]
  rintro ⟨B, hB0, -, -, hR⟩
  apply (T.stg 0).hRne B hB0
  rw [hR]
  have h0 : (⟨((0 : ↥(T.stg 0).FQ) : F), (T.stg 0).hFQ_le (0 : ↥(T.stg 0).FQ).2⟩ :
      ↥(T.stg 0).K) = 0 := Subtype.ext (by simp)
  rw [h0, map_zero, zero_mul]

/-- Nonzero digits HAVE realizers (`hS6a` at `ν = 0 ∈ weightSet`), so `digLift`
returns one: nonzero, a coefficient, parent weight 0, residue `C(digit)·T⁰`. -/
private lemma digLift_spec (T : Tower p F) (y : ↥(T.stg 0).FQ) (hy : y ≠ 0) :
    T.digLift y ≠ 0 ∧ inC (T.stg 0).Φ (T.digLift y) ∧ (T.stg 0).wPrev (T.digLift y) = 0 ∧
      (T.stg 0).R (T.digLift y)
        = LaurentPolynomial.C (⟨(y : F), (T.stg 0).hFQ_le y.2⟩ : ↥(T.stg 0).K) *
            LaurentPolynomial.T 0 := by
  have hex : ∃ B : Polynomial ℤ_[p], B ≠ 0 ∧ inC (T.stg 0).Φ B ∧ (T.stg 0).wPrev B = 0 ∧
      (T.stg 0).R B = LaurentPolynomial.C (⟨(y : F), (T.stg 0).hFQ_le y.2⟩ : ↥(T.stg 0).K) *
        LaurentPolynomial.T 0 := by
    -- 0 ∈ weightSet via the coefficient 1
    have h1ne : (1 : Polynomial ℤ_[p]) ≠ 0 := one_ne_zero
    have h1C : inC (T.stg 0).Φ (1 : Polynomial ℤ_[p]) := by
      show (1 : Polynomial ℤ_[p]).degree < _
      rw [← Polynomial.C_1]
      exact degC_lt' (T.stg 0) 1
    have h0mem : (0 : ℤ) ∈ (T.stg 0).weightSet := by
      have hmem := (T.stg 0).hWS 1 h1ne h1C
      rwa [T.base.1.1 1 h1ne, gaussVal_one] at hmem
    -- the digit as a unit of the current residue field
    have hyF : (y : F) ≠ 0 := by
      intro h
      exact hy (Subtype.ext h)
    have hkne : (⟨(y : F), (T.stg 0).hFQ_le y.2⟩ : ↥(T.stg 0).K) ≠ 0 := by
      intro h
      exact hyF (congrArg Subtype.val h)
    obtain ⟨B, hB0, hBC, hBw, hBR⟩ := (T.stg 0).hS6a 0 h0mem
      (Units.mk0 (⟨(y : F), (T.stg 0).hFQ_le y.2⟩ : ↥(T.stg 0).K) hkne) y.2
    refine ⟨B, hB0, hBC, hBw, ?_⟩
    simpa using hBR
  rw [Tower.digLift, dif_pos hex]
  exact hex.choose_spec

private lemma w0_digLift (T : Tower p F) (y : ↥(T.stg 0).FQ) (hy : y ≠ 0) :
    (T.stg 0).w (T.digLift y) = 0 := by
  obtain ⟨h0, hC, hw, -⟩ := digLift_spec T y hy
  rw [(T.stg 0).hStretch _ h0 hC, hw, mul_zero]

private lemma digLift_deg (T : Tower p F) (y : ↥(T.stg 0).FQ) :
    (T.digLift y).degree < (T.stg 0).Φ.degree := by
  by_cases hy : y = 0
  · rw [hy, digLift_zero T, Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.mpr
      (fun h => (T.stg 0).hmonic.ne_zero (Polynomial.degree_eq_bot.mp h))
  · exact (digLift_spec T y hy).2.1

private lemma carry_deg (T : Tower p F) (a b : ↥(T.stg 0).FQ) :
    (T.digLift (a + b) - T.digLift a - T.digLift b).degree < (T.stg 0).Φ.degree := by
  apply lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
  rw [max_lt_iff]
  exact ⟨lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
      (max_lt_iff.mpr ⟨digLift_deg T _, digLift_deg T _⟩),
    digLift_deg T _⟩

/-- `LaurentPolynomial.C` is injective (a constant is the `Finsupp.single` at 0). -/
private lemma laurentC_inj {R : Type*} [Ring R] {x y : R}
    (h : LaurentPolynomial.C x = LaurentPolynomial.C y) : x = y := by
  have h0 : LaurentPolynomial.C (x - y) = 0 := by rw [map_sub, h, sub_self]
  rw [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.single_eq_zero] at h0
  exact sub_eq_zero.mp h0

/-! ## The base carry wall -/

/-- **The wall at the base**: the digit-lift carry
`κ = digLift(a+b) − digLift a − digLift b` is either 0 or of base weight ≥ 1.
The residual laws (`hRne`, `hRadd`, `hRlt`) force the weight-0 part of `κ` to
carry the residue `C(a+b) − C a − C b = 0`, which `hRne` forbids. -/
private lemma carry_wall (T : Tower p F) (a b : ↥(T.stg 0).FQ) :
    T.digLift (a + b) - T.digLift a - T.digLift b = 0 ∨
      (T.digLift (a + b) - T.digLift a - T.digLift b ≠ 0 ∧
        1 ≤ (T.stg 0).w (T.digLift (a + b) - T.digLift a - T.digLift b)) := by
  by_cases hκ : T.digLift (a + b) - T.digLift a - T.digLift b = 0
  · exact Or.inl hκ
  refine Or.inr ⟨hκ, ?_⟩
  -- degenerate digit cases make κ literally 0
  by_cases ha : a = 0
  · exact absurd (by rw [ha, zero_add, digLift_zero T]; ring) hκ
  by_cases hb : b = 0
  · exact absurd (by rw [hb, add_zero, digLift_zero T]; ring) hκ
  -- κ is a base coefficient of nonnegative weight
  have hκdeg : (T.digLift (a + b) - T.digLift a - T.digLift b).degree <
      (T.stg 0).Φ.degree := carry_deg T a b
  have hκw0 : 0 ≤ (T.stg 0).w (T.digLift (a + b) - T.digLift a - T.digLift b) :=
    w0_nonneg T _ hκ hκdeg
  by_contra hcon
  have hκeq : (T.stg 0).w (T.digLift (a + b) - T.digLift a - T.digLift b) = 0 := by omega
  obtain ⟨hDa0, hDaC, -, hRa⟩ := digLift_spec T a ha
  obtain ⟨hDb0, hDbC, -, hRb⟩ := digLift_spec T b hb
  have hwa : (T.stg 0).w (T.digLift a) = 0 := w0_digLift T a ha
  have hwb : (T.stg 0).w (T.digLift b) = 0 := w0_digLift T b hb
  by_cases hab : a + b = 0
  · -- κ = −(digLift a + digLift b); its residue would be C(a) + C(b) = C(a+b) = 0
    have hκform : T.digLift (a + b) - T.digLift a - T.digLift b
        = -(T.digLift a + T.digLift b) := by
      rw [hab, digLift_zero T]; ring
    have hs : T.digLift a + T.digLift b ≠ 0 := by
      intro h0
      exact hκ (by rw [hκform, h0, neg_zero])
    have hws : (T.stg 0).w (T.digLift a + T.digLift b) = 0 := by
      have h1 : (T.stg 0).w (-(T.digLift a + T.digLift b)) = 0 := by
        rw [← hκform]; exact hκeq
      rwa [w0_neg T _ hs] at h1
    have hRadd := (T.stg 0).hRadd (T.digLift a) (T.digLift b) hDa0 hDb0 hs
      (by rw [hwa, hwb]) (by rw [hws, hwa])
    apply (T.stg 0).hRne _ hs
    rw [hRadd, hRa, hRb, ← add_mul, ← map_add]
    have hzero : ((⟨(a : F), (T.stg 0).hFQ_le a.2⟩ : ↥(T.stg 0).K)
        + ⟨(b : F), (T.stg 0).hFQ_le b.2⟩) = 0 := by
      apply Subtype.ext
      show (a : F) + (b : F) = 0
      have hab' : ((a + b : ↥(T.stg 0).FQ) : F) = 0 := by rw [hab]; simp
      push_cast at hab'
      exact hab'
    rw [hzero, map_zero, zero_mul]
  · -- all three digits nonzero: chase the residues through hRadd/hRlt
    obtain ⟨hDf0, hDfC, -, hRf⟩ := digLift_spec T (a + b) hab
    have hwf : (T.stg 0).w (T.digLift (a + b)) = 0 := w0_digLift T (a + b) hab
    -- the recurring contradiction: R(digLift(a+b)) = R(digLift b) forces a = 0
    have hcontra : (T.stg 0).R (T.digLift (a + b)) = (T.stg 0).R (T.digLift b) → False := by
      intro heq
      rw [hRf, hRb, LaurentPolynomial.T_zero, mul_one, mul_one] at heq
      have h3 := congrArg Subtype.val (laurentC_inj heq)
      -- h3 : ((a+b : ↥FQ) : F) = (b : F)
      apply ha
      have h4 : (a : F) + (b : F) = (b : F) := by
        push_cast at h3
        exact h3
      have h5 : (a : F) + (b : F) = 0 + (b : F) := by rw [zero_add]; exact h4
      have h6 : (a : F) = 0 := add_right_cancel h5
      exact Subtype.ext (by rw [h6]; simp)
    by_cases hu0 : T.digLift a + (T.digLift (a + b) - T.digLift a - T.digLift b) = 0
    · -- then digLift(a+b) = digLift b outright
      apply hcontra
      have heq : T.digLift (a + b) = T.digLift b := by
        have h := hu0
        have h2 : T.digLift (a + b) - T.digLift b = 0 := by
          calc T.digLift (a + b) - T.digLift b
              = T.digLift a + (T.digLift (a + b) - T.digLift a - T.digLift b) := by ring
            _ = 0 := h
        exact sub_eq_zero.mp h2
      rw [heq]
    · by_cases hwu : (T.stg 0).w
          (T.digLift a + (T.digLift (a + b) - T.digLift a - T.digLift b)) = 0
      · -- weight-0 intermediate sum: hRadd twice pins R κ = C(a+b) − C a − C b = 0
        have hR1 := (T.stg 0).hRadd (T.digLift a)
          (T.digLift (a + b) - T.digLift a - T.digLift b) hDa0 hκ hu0
          (by rw [hwa, hκeq]) (by rw [hwu, hwa])
        have hplus : T.digLift a + (T.digLift (a + b) - T.digLift a - T.digLift b)
            + T.digLift b = T.digLift (a + b) := by ring
        have hR2 := (T.stg 0).hRadd
          (T.digLift a + (T.digLift (a + b) - T.digLift a - T.digLift b)) (T.digLift b)
          hu0 hDb0 (by rw [hplus]; exact hDf0) (by rw [hwu, hwb]) (by rw [hplus, hwf, hwu])
        rw [hplus, hR1] at hR2
        -- hR2 : R (digLift (a+b)) = (R (digLift a) + R κ) + R (digLift b)
        apply (T.stg 0).hRne _ hκ
        have hRκ : (T.stg 0).R (T.digLift (a + b) - T.digLift a - T.digLift b)
            = (T.stg 0).R (T.digLift (a + b)) - (T.stg 0).R (T.digLift a)
              - (T.stg 0).R (T.digLift b) := by
          rw [hR2]; ring
        rw [hRκ, hRf, hRa, hRb, LaurentPolynomial.T_zero, mul_one, mul_one, mul_one,
          ← map_sub, ← map_sub]
        have hzero : ((⟨((a + b : ↥(T.stg 0).FQ) : F), (T.stg 0).hFQ_le (a + b).2⟩ :
            ↥(T.stg 0).K) - ⟨(a : F), (T.stg 0).hFQ_le a.2⟩
              - ⟨(b : F), (T.stg 0).hFQ_le b.2⟩) = 0 := by
          apply Subtype.ext
          show ((a + b : ↥(T.stg 0).FQ) : F) - (a : F) - (b : F) = 0
          push_cast
          ring
        rw [hzero, map_zero]
      · -- positive-weight intermediate sum: hRlt hides it, R(digLift(a+b)) = R(digLift b)
        have hwu_ge : 0 ≤ (T.stg 0).w
            (T.digLift a + (T.digLift (a + b) - T.digLift a - T.digLift b)) := by
          have hult := (T.stg 0).hwult (T.digLift a)
            (T.digLift (a + b) - T.digLift a - T.digLift b) hDa0 hκ hu0
          rw [hwa, hκeq] at hult
          simpa using hult
        have hwu_pos : 0 < (T.stg 0).w
            (T.digLift a + (T.digLift (a + b) - T.digLift a - T.digLift b)) :=
          lt_of_le_of_ne hwu_ge (Ne.symm hwu)
        have hplus' : T.digLift b
            + (T.digLift a + (T.digLift (a + b) - T.digLift a - T.digLift b))
            = T.digLift (a + b) := by ring
        have hRlt := (T.stg 0).hRlt (T.digLift b)
          (T.digLift a + (T.digLift (a + b) - T.digLift a - T.digLift b)) hDb0 hu0
          (by rw [hplus']; exact hDf0) (by rw [hwb]; exact hwu_pos)
        rw [hplus'] at hRlt
        exact hcontra hRlt

/-! ## The stretch chain: base positivity rides to the top stage -/

/-- Degree monotonicity along one move (T3's argument, reproved locally). -/
private lemma deg_mono_step (T : Tower p F) (m : ℕ) (hm : m < T.K) :
    (T.stg ⟨m, Nat.lt_succ_of_lt hm⟩).Φ.natDegree
      ≤ (T.stg ⟨m + 1, Nat.succ_lt_succ hm⟩).Φ.natDegree := by
  set k : Fin T.K := ⟨m, hm⟩ with hk
  show (T.stg k.castSucc).Φ.natDegree ≤ (T.stg k.succ).Φ.natDegree
  cases T.move k with
  | inc ψ g Φhat e' h' zbar hyp core =>
    have hkey := core.base.child_key
    have hdeg := (L3_liftMonic (T.stg k.castSucc) ψ g hyp.hg Φhat hyp.hlift).2
    rw [hkey, hdeg]
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (T.stg k.castSucc).he hyp.hg)
  | recenter cc tt core =>
    obtain ⟨_, _, _, htt, _, _, _, hΦ', _, _, _, _, _, _⟩ := core.base
    rw [hΦ']
    have hne1 : (T.stg k.castSucc).Φ - tt ≠ 0 := by
      rw [← hΦ']; exact (T.stg k.succ).hmonic.ne_zero
    have hne2 : (T.stg k.castSucc).Φ ≠ 0 := (T.stg k.castSucc).hmonic.ne_zero
    have hdegeq : ((T.stg k.castSucc).Φ - tt).degree = (T.stg k.castSucc).Φ.degree :=
      Polynomial.degree_sub_eq_left_of_degree_lt htt
    have hnd : ((T.stg k.castSucc).Φ - tt).natDegree = (T.stg k.castSucc).Φ.natDegree := by
      rw [Polynomial.degree_eq_natDegree hne1, Polynomial.degree_eq_natDegree hne2] at hdegeq
      exact_mod_cast hdegeq
    rw [hnd]

private lemma deg_le (T : Tower p F) (a : ℕ) :
    ∀ (b : ℕ) (hab : a ≤ b) (hbK : b < T.K + 1),
      (T.stg ⟨a, by omega⟩).Φ.natDegree ≤ (T.stg ⟨b, hbK⟩).Φ.natDegree := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ n hn ih =>
    intro hbK
    have hnK : n < T.K + 1 := by omega
    have hnlt : n < T.K := by omega
    exact le_trans (ih hnK) (deg_mono_step T n hnlt)

/-- `deg Φ₀ ≤ deg Φ_k` (degree form). -/
private lemma deg0_le (T : Tower p F) (j : ℕ) (hj : j < T.K + 1) :
    (T.stg 0).Φ.degree ≤ (T.stg ⟨j, hj⟩).Φ.degree := by
  have h0 : (⟨0, Nat.succ_pos T.K⟩ : Fin (T.K + 1)) = 0 := Fin.ext (by simp)
  have h := deg_le T 0 j (Nat.zero_le j) hj
  rw [h0] at h
  rw [Polynomial.degree_eq_natDegree (T.stg 0).hmonic.ne_zero,
    Polynomial.degree_eq_natDegree (T.stg ⟨j, hj⟩).hmonic.ne_zero]
  exact_mod_cast h

/-- One tower step multiplies coefficient weights by `e` (T3's `stretch_step`). -/
private lemma stretch_step (T : Tower p F) (m : ℕ) (hm0 : m < T.K + 1)
    (hm1 : m + 1 < T.K + 1) (B : Polynomial ℤ_[p]) (hB : B ≠ 0)
    (hcoef : B.degree < (T.stg ⟨m + 1, hm1⟩).Φ.degree) :
    (T.stg ⟨m + 1, hm1⟩).w B = ((T.stg ⟨m + 1, hm1⟩).e : ℤ) * (T.stg ⟨m, hm0⟩).w B := by
  have hm : m < T.K := by omega
  set k : Fin T.K := ⟨m, hm⟩ with hk
  show (T.stg k.succ).w B = ((T.stg k.succ).e : ℤ) * (T.stg k.castSucc).w B
  cases T.move k with
  | inc ψ g Φhat e' h' zbar hyp core =>
    rw [(T.stg k.succ).hStretch B hB hcoef, core.base.child_wPrev B]
  | recenter cc tt core =>
    obtain ⟨_, he', _, _, _, _, _, _, hw, _, _, _, _, _⟩ := core.base
    rw [hw B, he']
    simp

/-- **The stretch chain**: a base coefficient's weight at stage k is a positive
multiple of its base weight (increments stretch by `e′ ≥ 1`, recenterings keep). -/
private lemma w_chain (T : Tower p F) (f : Polynomial ℤ_[p]) (hf : f ≠ 0)
    (hdeg : f.degree < (T.stg 0).Φ.degree) (k : ℕ) :
    ∀ hk : k < T.K + 1, ∃ m : ℕ, 0 < m ∧
      (T.stg ⟨k, hk⟩).w f = (m : ℤ) * (T.stg 0).w f := by
  induction k with
  | zero =>
    intro hk
    refine ⟨1, Nat.one_pos, ?_⟩
    have h0 : (⟨0, hk⟩ : Fin (T.K + 1)) = 0 := Fin.ext (by simp)
    rw [h0, Nat.cast_one, one_mul]
  | succ n ih =>
    intro hk
    have hn : n < T.K + 1 := by omega
    obtain ⟨m, hm, hmw⟩ := ih hn
    have hstep := stretch_step T n hn hk f hf (lt_of_lt_of_le hdeg (deg0_le T (n + 1) hk))
    refine ⟨(T.stg ⟨n + 1, hk⟩).e * m, Nat.mul_pos (T.stg ⟨n + 1, hk⟩).he hm, ?_⟩
    rw [hstep, hmw]
    push_cast
    ring

private lemma fin_last_eq (T : Tower p F) :
    Fin.last T.K = (⟨T.K, Nat.lt_succ_self T.K⟩ : Fin (T.K + 1)) := Fin.ext (by simp)

/-- Base weight ≥ 1 rides to the top stage. -/
private lemma w_top_pos (T : Tower p F) (f : Polynomial ℤ_[p]) (hf : f ≠ 0)
    (hdeg : f.degree < (T.stg 0).Φ.degree) (h1 : 1 ≤ (T.stg 0).w f) :
    1 ≤ (T.stg (Fin.last T.K)).w f := by
  obtain ⟨m, hm, hmw⟩ := w_chain T f hf hdeg T.K (Nat.lt_succ_self T.K)
  rw [fin_last_eq T, hmw]
  have hm1 : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  nlinarith

/-- Digit lifts stay at weight 0 at the top stage. -/
private lemma w_top_digLift (T : Tower p F) (y : ↥(T.stg 0).FQ) (hy : y ≠ 0) :
    (T.stg (Fin.last T.K)).w (T.digLift y) = 0 := by
  obtain ⟨hD0, hDC, -, -⟩ := digLift_spec T y hy
  obtain ⟨m, -, hmw⟩ := w_chain T _ hD0 hDC T.K (Nat.lt_succ_self T.K)
  rw [fin_last_eq T, hmw, w0_digLift T y hy, mul_zero]

/-! ## Monomials, the level set, and its finiteness -/

private lemma mono_ne (T : Tower p F) (c : T.Coord) : T.mono c ≠ 0 := by
  rw [Tower.mono]
  apply mul_ne_zero
  · rw [Ne, Polynomial.C_eq_zero]
    exact pow_ne_zero _ PadicInt.prime_p.ne_zero
  · exact Finset.prod_ne_zero_iff.mpr fun r _ => pow_ne_zero _ (T.stg r).hmonic.ne_zero

/-- On the lattice, the top-stage weight of a level-set monomial is exactly the
piece index `⌊strTop·γ⌋` (T3 + `ht c = γ`). -/
private lemma w_mono_level (T : Tower p F) {b : ℕ} {γ : ℚ} (honL : T.onLattice γ)
    {c : T.Coord} (hc : c ∈ T.levelSet b γ) :
    (T.stg (Fin.last T.K)).w (T.mono c) = ⌊(T.strTop : ℚ) * γ⌋ := by
  have h3 := T3_htChainWeight T c (mono_ne T c)
  have hht : T.ht c = γ := hc.2
  rw [hht] at h3
  have honL' : ((⌊(T.strTop : ℚ) * γ⌋ : ℚ)) = (T.strTop : ℚ) * γ := honL
  rw [← honL'] at h3
  exact_mod_cast h3

private lemma kappa_nonneg (T : Tower p F) (r : Fin (T.K + 1)) : 0 ≤ T.kappa r := by
  rw [Tower.kappa]
  positivity

/-- The level set is finite: heights bound the p-adic level, `slot_lt` bounds the
inner slots, and the block pins the top slot (rides T12's box finiteness). -/
private lemma levelSet_finite (T : Tower p F) (b : ℕ) (γ : ℚ) :
    (T.levelSet b γ).Finite := by
  apply Set.Finite.subset ((T12_coordFin T (⌊γ⌋.toNat + 1) (b + 1)).1)
  rintro c ⟨hblk, hht⟩
  constructor
  · have hle : (c.l : ℚ) ≤ γ := by
      rw [← hht, Tower.ht]
      have hsum : 0 ≤ ∑ r, (c.slot r : ℚ) * T.kappa r :=
        Finset.sum_nonneg fun r _ => mul_nonneg (Nat.cast_nonneg _) (kappa_nonneg T r)
      linarith
    have h1 : (c.l : ℤ) ≤ ⌊γ⌋ := Int.le_floor.mpr (by exact_mod_cast hle)
    omega
  · have hb : c.slot (Fin.last T.K) = b := hblk
    omega

/-- On assignments supported in the level set, `slotCoeff` is the honest finite
sum over the level set. -/
private lemma slotCoeff_eq_sum (T : Tower p F) (b : ℕ) (γ : ℚ)
    (u : T.Coord → ↥(T.stg 0).FQ) (hu : ∀ c, u c ≠ 0 → c ∈ T.levelSet b γ) :
    T.slotCoeff b u
      = ∑ c ∈ (levelSet_finite T b γ).toFinset, T.digLift (u c) * T.mono c := by
  have hsub : ({c : T.Coord | T.blk c = b}
      ∩ Function.support fun c => T.digLift (u c) * T.mono c) ⊆ T.levelSet b γ := by
    rintro c ⟨-, hc⟩
    by_contra hcl
    have hu0 : u c = 0 := by
      by_contra h
      exact hcl (hu c h)
    exact Function.mem_support.mp hc
      (by show T.digLift (u c) * T.mono c = 0; rw [hu0, digLift_zero T, zero_mul])
  have hfin : ({c : T.Coord | T.blk c = b}
      ∩ Function.support fun c => T.digLift (u c) * T.mono c).Finite :=
    (levelSet_finite T b γ).subset hsub
  rw [Tower.slotCoeff, finsum_mem_eq_sum _ hfin]
  apply Finset.sum_subset
  · intro c hc
    rw [Set.Finite.mem_toFinset] at hc ⊢
    exact hsub hc
  · intro c hcL hcn
    by_contra hne
    apply hcn
    rw [Set.Finite.mem_toFinset] at hcL ⊢
    exact ⟨hcL.1, Function.mem_support.mpr hne⟩

/-- `typComposite` as an honest finite sum inside `inGr`. -/
private lemma typComposite_eq_sum (T : Tower p F) (b : ℕ) (γ : ℚ)
    (z : ↥(T.levelSet b γ) → ↥(T.stg 0).FQ) :
    T.typComposite b γ z
      = T.inGr γ (∑ c ∈ (levelSet_finite T b γ).toFinset,
          T.digLift (if h : c ∈ T.levelSet b γ then z ⟨c, h⟩ else 0) * T.mono c) := by
  rw [Tower.typComposite, slotCoeff_eq_sum T b γ _ (fun c hc => by
    by_contra h
    exact hc (dif_neg h))]

/-! ## Graded-piece plumbing (T6's private toolkit, re-derived) -/

private lemma inGr_off (T : Tower p F) {γ : ℚ} (honL : ¬ T.onLattice γ)
    (f : Polynomial ℤ_[p]) : T.inGr γ f = 0 := by
  rw [Tower.inGr, dif_neg (fun h => honL h.1)]

private lemma inGr_on (T : Tower p F) {γ : ℚ} (honL : T.onLattice γ) (f : Polynomial ℤ_[p])
    (hf : (↑(⌊(T.strTop : ℚ) * γ⌋) : WithTop ℤ) ≤ T.side.w f) :
    T.inGr γ f = Submodule.Quotient.mk (⟨f, hf⟩ : T.side.ge (⌊(T.strTop : ℚ) * γ⌋)) := by
  rw [Tower.inGr, dif_pos ⟨honL, hf⟩]

private lemma mk_eq_zero_iff (T : Tower p F) (m : ℤ) (f : Polynomial ℤ_[p])
    (hf : f ∈ T.side.ge m) :
    (Submodule.Quotient.mk (⟨f, hf⟩ : T.side.ge m) : T.side.grPiece m) = 0
      ↔ (↑m : WithTop ℤ) < T.side.w f := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

/-- The side valuation computes the top-stage weight on nonzeros (T6's `HasSide`). -/
private lemma side_w_eq (T : Tower p F) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) :
    T.side.w f = (((T.stg (Fin.last T.K)).w f : ℤ) : WithTop ℤ) :=
  T.side_w (T6_carrierLaws T).1 hf

/-- Ultrametric bound for finite sums of the side valuation. -/
private lemma side_w_sum (T : Tower p F) {ι : Type*} (s : Finset ι)
    (G : ι → Polynomial ℤ_[p]) (μ : ℤ) :
    (∀ i ∈ s, (μ : WithTop ℤ) ≤ T.side.w (G i)) →
      (μ : WithTop ℤ) ≤ T.side.w (∑ i ∈ s, G i) := by
  induction s using Finset.cons_induction with
  | empty =>
    intro _
    rw [Finset.sum_empty, T.side.w_zero]
    exact le_top
  | cons a s ha ih =>
    intro h
    rw [Finset.sum_cons]
    exact le_trans (le_min (h a (Finset.mem_cons.mpr (Or.inl rfl)))
      (ih fun i hi => h i (Finset.mem_cons.mpr (Or.inr hi)))) (T.side.w_add _ _)

/-- `inGr γ` is additive on summands of weight ≥ the piece index. -/
private lemma inGr_add_of_ge (T : Tower p F) {γ : ℚ} (honL : T.onLattice γ)
    (f g : Polynomial ℤ_[p])
    (hf : (↑(⌊(T.strTop : ℚ) * γ⌋) : WithTop ℤ) ≤ T.side.w f)
    (hg : (↑(⌊(T.strTop : ℚ) * γ⌋) : WithTop ℤ) ≤ T.side.w g) :
    T.inGr γ (f + g) = T.inGr γ f + T.inGr γ g := by
  have hfg : (↑(⌊(T.strTop : ℚ) * γ⌋) : WithTop ℤ) ≤ T.side.w (f + g) :=
    (T.side.ge _).add_mem hf hg
  rw [inGr_on T honL _ hfg, inGr_on T honL f hf, inGr_on T honL g hg]
  exact Submodule.Quotient.mk_add (T.side.gtIn (⌊(T.strTop : ℚ) * γ⌋))
    (x := ⟨f, hf⟩) (y := ⟨g, hg⟩)

/-- Perturbations of weight STRICTLY above the piece index are invisible to `inGr γ`. -/
private lemma inGr_add_high (T : Tower p F) {γ : ℚ} (f E : Polynomial ℤ_[p])
    (hE : (↑(⌊(T.strTop : ℚ) * γ⌋) : WithTop ℤ) < T.side.w E) :
    T.inGr γ (f + E) = T.inGr γ f := by
  by_cases honL : T.onLattice γ
  · by_cases hf : (↑(⌊(T.strTop : ℚ) * γ⌋) : WithTop ℤ) ≤ T.side.w f
    · have hfE : (↑(⌊(T.strTop : ℚ) * γ⌋) : WithTop ℤ) ≤ T.side.w (f + E) :=
        (T.side.ge _).add_mem hf (le_of_lt hE)
      rw [inGr_on T honL _ hfE, inGr_on T honL f hf]
      refine (Submodule.Quotient.eq (T.side.gtIn (⌊(T.strTop : ℚ) * γ⌋))).mpr ?_
      have hsub : ((⟨f + E, hfE⟩ : T.side.ge (⌊(T.strTop : ℚ) * γ⌋)) - ⟨f, hf⟩)
          = ⟨E, le_of_lt hE⟩ := Subtype.ext (add_sub_cancel_left f E)
      rw [hsub]
      exact hE
    · have hfE : ¬ (↑(⌊(T.strTop : ℚ) * γ⌋) : WithTop ℤ) ≤ T.side.w (f + E) := by
        intro hle
        apply hf
        have heq : f + E + -E = f := by ring
        calc (↑(⌊(T.strTop : ℚ) * γ⌋) : WithTop ℤ)
            ≤ min (T.side.w (f + E)) (T.side.w (-E)) :=
              le_min hle (by rw [T.side.w_neg]; exact le_of_lt hE)
          _ ≤ T.side.w (f + E + -E) := T.side.w_add _ _
          _ = T.side.w f := by rw [heq]
      rw [Tower.inGr, dif_neg (fun h => hfE h.2), Tower.inGr, dif_neg (fun h => hf h.2)]
  · rw [inGr_off T honL, inGr_off T honL]

/-! ## The unit -/

/-- Unit C2: TYP(a) — on assignments with block-b digits of height < γ' all zero,
`inγ γ' (slotCoeff b y) = typComposite b γ' (y ↾ levelSet)`, and the composite is
additive in the digit tuple. -/
theorem C2_TYPa {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (γ' : ℚ) :
    (∀ y : T.Coord → ↥(T.stg 0).FQ, (Function.support y).Finite →
      (∀ c, y c ≠ 0 → T.blk c = b) →
      (∀ c, T.blk c = b → T.ht c < γ' → y c = 0) →
      T.inGr γ' (T.slotCoeff b y)
        = T.typComposite b γ' (fun c => y c.1)) ∧
    (∀ x y : ↥(T.levelSet b γ') → ↥(T.stg 0).FQ,
      T.typComposite b γ' (x + y)
        = T.typComposite b γ' x + T.typComposite b γ' y) := by
  refine ⟨?_, ?_⟩
  · -- Conjunct (a): the composite computes inγ' on the level-set restriction.
    -- `typComposite b γ' (y ↾ levelSet)` unfolds to `inGr γ' (slotCoeff b y')` with
    -- `y' c := if c ∈ levelSet b γ' then y c else 0`; T5 then equates the two inGr's.
    intro y hyfin _hsupp hlow
    set y' : T.Coord → ↥(T.stg 0).FQ :=
      fun c => if h : c ∈ T.levelSet b γ' then y c else 0 with hy'
    show T.inGr γ' (T.slotCoeff b y) = T.inGr γ' (T.slotCoeff b y')
    apply T5_levelSetInGamma T b γ' y y' hyfin
    · -- support y' ⊆ support y, hence finite
      apply hyfin.subset
      intro c hc
      by_contra hcy
      simp only [Function.mem_support, not_not] at hcy
      apply hc
      simp only [hy']
      split <;> simp [hcy]
    · -- agree on the level set: y' c = y c there
      intro c hc
      simp only [hy', dif_pos hc]
    · -- hxlow for x := y is exactly the hypothesis
      exact hlow
    · -- y' c = 0 whenever ht c < γ' (such c are off the level set)
      intro c _hbc hlt
      simp only [hy']
      rw [dif_neg]
      rintro ⟨_, hht⟩
      exact absurd hht (ne_of_lt hlt)
  · -- Conjunct (b): additivity of the composite in the digit tuple.
    -- The base-residue carry `digLift(a+b) − digLift a − digLift b` has base weight
    -- ≥ 1 when nonzero (`carry_wall`), hence top-stage weight ≥ 1 (`w_chain` — it is
    -- a coefficient at EVERY stage), hence its monomial multiples sit STRICTLY above
    -- the γ'-piece and `inGr γ'` kills the whole carry sum (`inGr_add_high`); the
    -- remaining digit-wise sums split by `inGr_add_of_ge` at weight exactly the piece.
    intro x y
    by_cases honL : T.onLattice γ'
    · rw [typComposite_eq_sum, typComposite_eq_sum, typComposite_eq_sum]
      -- the (x+y)-digit at c is the sum of the x- and y-digits at c
      have hdigadd : ∀ c : T.Coord,
          (if h : c ∈ T.levelSet b γ' then (x + y) ⟨c, h⟩ else 0)
            = (if h : c ∈ T.levelSet b γ' then x ⟨c, h⟩ else 0)
              + (if h : c ∈ T.levelSet b γ' then y ⟨c, h⟩ else 0) := by
        intro c
        by_cases h : c ∈ T.levelSet b γ'
        · simp only [dif_pos h]
          rfl
        · simp only [dif_neg h, add_zero]
      -- split the (x+y)-sum into the two digit-wise sums plus the carry sum
      have hsplit : (∑ c ∈ (levelSet_finite T b γ').toFinset,
            T.digLift (if h : c ∈ T.levelSet b γ' then (x + y) ⟨c, h⟩ else 0) * T.mono c)
          = ((∑ c ∈ (levelSet_finite T b γ').toFinset,
              T.digLift (if h : c ∈ T.levelSet b γ' then x ⟨c, h⟩ else 0) * T.mono c)
            + (∑ c ∈ (levelSet_finite T b γ').toFinset,
              T.digLift (if h : c ∈ T.levelSet b γ' then y ⟨c, h⟩ else 0) * T.mono c))
            + (∑ c ∈ (levelSet_finite T b γ').toFinset,
              (T.digLift ((if h : c ∈ T.levelSet b γ' then x ⟨c, h⟩ else 0)
                  + (if h : c ∈ T.levelSet b γ' then y ⟨c, h⟩ else 0))
                - T.digLift (if h : c ∈ T.levelSet b γ' then x ⟨c, h⟩ else 0)
                - T.digLift (if h : c ∈ T.levelSet b γ' then y ⟨c, h⟩ else 0)) * T.mono c) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro c _
        rw [hdigadd c]
        ring
      rw [hsplit]
      -- weight bookkeeping: digit terms sit AT the piece, carry terms strictly above
      have hterm_ge : ∀ (d : ↥(T.stg 0).FQ) (c : T.Coord),
          c ∈ (levelSet_finite T b γ').toFinset →
          ((⌊(T.strTop : ℚ) * γ'⌋ : ℤ) : WithTop ℤ) ≤ T.side.w (T.digLift d * T.mono c) := by
        intro d c hc
        by_cases hd : d = 0
        · rw [hd, digLift_zero T, zero_mul, T.side.w_zero]
          exact le_top
        · have hcl : c ∈ T.levelSet b γ' := (Set.Finite.mem_toFinset _).mp hc
          have hD := digLift_spec T d hd
          have hne : T.digLift d * T.mono c ≠ 0 := mul_ne_zero hD.1 (mono_ne T c)
          rw [side_w_eq T _ hne, (T.stg (Fin.last T.K)).hwmul _ _ hD.1 (mono_ne T c),
            w_top_digLift T d hd, w_mono_level T honL hcl, zero_add]
      have hcarry_ge : ∀ (d e : ↥(T.stg 0).FQ) (c : T.Coord),
          c ∈ (levelSet_finite T b γ').toFinset →
          ((⌊(T.strTop : ℚ) * γ'⌋ + 1 : ℤ) : WithTop ℤ)
            ≤ T.side.w ((T.digLift (d + e) - T.digLift d - T.digLift e) * T.mono c) := by
        intro d e c hc
        have hcl : c ∈ T.levelSet b γ' := (Set.Finite.mem_toFinset _).mp hc
        rcases carry_wall T d e with hκ0 | ⟨hκ, hκ1⟩
        · rw [hκ0, zero_mul, T.side.w_zero]
          exact le_top
        · have hκtop : 1 ≤ (T.stg (Fin.last T.K)).w
              (T.digLift (d + e) - T.digLift d - T.digLift e) :=
            w_top_pos T _ hκ (carry_deg T d e) hκ1
          have hne : (T.digLift (d + e) - T.digLift d - T.digLift e) * T.mono c ≠ 0 :=
            mul_ne_zero hκ (mono_ne T c)
          rw [side_w_eq T _ hne, (T.stg (Fin.last T.K)).hwmul _ _ hκ (mono_ne T c),
            w_mono_level T honL hcl, WithTop.coe_le_coe]
          omega
      have hwB1 := side_w_sum T (levelSet_finite T b γ').toFinset
        (fun c => T.digLift (if h : c ∈ T.levelSet b γ' then x ⟨c, h⟩ else 0) * T.mono c)
        (⌊(T.strTop : ℚ) * γ'⌋)
        (fun c hc => hterm_ge (if h : c ∈ T.levelSet b γ' then x ⟨c, h⟩ else 0) c hc)
      have hwB2 := side_w_sum T (levelSet_finite T b γ').toFinset
        (fun c => T.digLift (if h : c ∈ T.levelSet b γ' then y ⟨c, h⟩ else 0) * T.mono c)
        (⌊(T.strTop : ℚ) * γ'⌋)
        (fun c hc => hterm_ge (if h : c ∈ T.levelSet b γ' then y ⟨c, h⟩ else 0) c hc)
      have hwE := side_w_sum T (levelSet_finite T b γ').toFinset
        (fun c => (T.digLift ((if h : c ∈ T.levelSet b γ' then x ⟨c, h⟩ else 0)
              + (if h : c ∈ T.levelSet b γ' then y ⟨c, h⟩ else 0))
            - T.digLift (if h : c ∈ T.levelSet b γ' then x ⟨c, h⟩ else 0)
            - T.digLift (if h : c ∈ T.levelSet b γ' then y ⟨c, h⟩ else 0)) * T.mono c)
        (⌊(T.strTop : ℚ) * γ'⌋ + 1)
        (fun c hc => hcarry_ge (if h : c ∈ T.levelSet b γ' then x ⟨c, h⟩ else 0)
          (if h : c ∈ T.levelSet b γ' then y ⟨c, h⟩ else 0) c hc)
      rw [inGr_add_high T _ _ (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (lt_add_one _)) hwE)]
      exact inGr_add_of_ge T honL _ _ hwB1 hwB2
    · -- off the stage lattice, every class is 0 by the D3 convention
      rw [Tower.typComposite, Tower.typComposite, Tower.typComposite,
        inGr_off T honL, inGr_off T honL, inGr_off T honL, add_zero]

end LeanUrat.HC1

#print axioms LeanUrat.HC1.C2_TYPa
