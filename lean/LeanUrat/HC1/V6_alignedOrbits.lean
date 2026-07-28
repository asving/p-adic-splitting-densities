/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsV
import LeanUrat.Moves.L4_TRANSviii_a_R5_final
import LeanUrat.Moves.L3_liftMonic

/-!
# HC1.V6_alignedOrbits — the aligned digit orbits, both levels (blueprint §10, V6)

V′-KERNEL unit (blueprint §10.1), TWO legs — post-V5 (the `Stage.hS6a` coset
restate, 2026-07-28), the S9a header's twisted-orbit display is now a POSITIVE
statement, not an obstruction:

* **(a) REGRADE orbits are UNTWISTED**: σ★-realizers = the parent's coset hS6a
  realizers RE-POSITIONED, scalars PRESERVED (no z̄ enters at the same level) —
  fills `ReadFrame.hS6a`; also the b-transport helper the V5 census cites.
* **(b) DESCENT orbit base points**: the strip window display — slots at child
  weight ν are `(γ, j) = (s·ν − λ·h, t·ν + λ·e)`, λ ∈ (a g-window), twist = λ;
  the minimizing-slot choice (`L4_TRANSviii_a` conjunct 1 forward + choice)
  fixes THE base b(ν) per weight, of the displayed SHAPE
  `(b : F) = (b̃ : F)·z̄^m` (a parent unit times a fixed z̄-monomial class —
  D.7(viii)'s realizer display, MOVES 2423–2435).

moves_ref: D.7(viii)'s 𝒜′ + realizer display (MOVES 2423–2435); the S9a
header's twisted-orbit display.  deps: V0; (b) consumes
`L4_TRANSviii_a_R5_final` post-V5.  difficulty: short.
P-phase COMPLETE (2026-07-28): both legs PROVED σ-only, Lean-core axioms only
(no `sorry`, no new axiom). V6(a) = parent coset `hS6a` transported through
`ReadResData.hS5`; V6(b) = the window (Lemma K1 on the σ.Φ-development) + the
single-slot realizer `Creal·σ.Φ^j` whose z̄-evaluation carries the twist `z̄^m`
that the base `b` absorbs (the below-threshold strip needs NO threshold: it rides
`σ.hS6a`'s coefficient-level coset, not `hS6b`), read into `D.Rc` via `hS5'`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Bounded Φ-adic development (the general polynomial fact; a private copy of the
same-named lemma in `Moves.L4_TRANSviii_a_R5_final`, which is `private` there). -/
private lemma dev_exists_bounded {R : Type*} [CommRing R] (Φ : Polynomial R) (hΦ : Φ.Monic)
    (hd : 1 ≤ Φ.natDegree) :
    ∀ (M : ℕ) (f : Polynomial R), f.natDegree < M * Φ.natDegree →
      ∃ B : ℕ → Polynomial R, IsDevelopment Φ f B M := by
  have hRnt : Nontrivial R := by
    rcases subsingleton_or_nontrivial R with h | h
    · exfalso
      have hz : Φ = 0 := Subsingleton.elim _ _
      rw [hz] at hd; simp at hd
    · exact h
  have hΦ0 : Φ ≠ 0 := hΦ.ne_zero
  have hΦbot : (⊥ : WithBot ℕ) < Φ.degree :=
    bot_lt_iff_ne_bot.mpr (fun h => hΦ0 (Polynomial.degree_eq_bot.mp h))
  intro M
  induction M with
  | zero =>
    intro f hf
    rw [zero_mul] at hf
    exact absurd hf (Nat.not_lt_zero _)
  | succ n IH =>
    intro f hf
    have hdiv : f %ₘ Φ + Φ * (f /ₘ Φ) = f := Polynomial.modByMonic_add_div f Φ
    have hqdev : ∃ B, IsDevelopment Φ (f /ₘ Φ) B n := by
      rcases eq_or_ne (f /ₘ Φ) 0 with hqz | hqz
      · refine ⟨fun _ => 0, ?_, fun j _ => rfl, ?_⟩
        · intro j
          show (0 : Polynomial R).degree < Φ.degree
          rw [Polynomial.degree_zero]; exact hΦbot
        · rw [hqz]; simp
      · apply IH
        have hdvz : ¬ (f.degree < Φ.degree) :=
          fun hlt => hqz ((Polynomial.divByMonic_eq_zero_iff hΦ).mpr hlt)
        have hnd : Φ.natDegree ≤ f.natDegree :=
          Polynomial.natDegree_le_natDegree (not_lt.mp hdvz)
        have hqnd : (f /ₘ Φ).natDegree = f.natDegree - Φ.natDegree :=
          Polynomial.natDegree_divByMonic f hΦ
        rw [Nat.succ_mul] at hf
        omega
    obtain ⟨B', hB'deg, hB'zero, hB'sum⟩ := hqdev
    refine ⟨(fun j => match j with | 0 => f %ₘ Φ | k + 1 => B' k), ?_, ?_, ?_⟩
    · intro j
      cases j with
      | zero =>
        show (f %ₘ Φ).degree < Φ.degree
        exact Polynomial.degree_modByMonic_lt f hΦ
      | succ k =>
        show (B' k).degree < Φ.degree
        exact hB'deg k
    · intro j hj
      cases j with
      | zero => exact absurd hj (by omega)
      | succ k =>
        show B' k = 0
        exact hB'zero k (by omega)
    · symm
      rw [Finset.sum_range_succ']
      show (∑ k ∈ Finset.range n, B' k * Φ ^ (k + 1)) + (f %ₘ Φ) * Φ ^ 0 = f
      rw [pow_zero, mul_one]
      have e1 : (∑ k ∈ Finset.range n, B' k * Φ ^ (k + 1)) = (f /ₘ Φ) * Φ := by
        rw [hB'sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        rw [pow_succ]; ring
      rw [e1]
      linear_combination hdiv

/-- Unit V6(a): REGRADE orbits are the parent's coset orbits re-positioned —
scalars preserved, positions re-forced at `−t★·ν`; fills `ReadFrame.hS6a`. -/
theorem V6_regradeOrbits {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ)
    (estar hstar : ℕ) (sstar tstar : ℤ)
    (hrp : ReadPair σ estar hstar sstar tstar)
    (D : ReadResData σ estar hstar sstar tstar) :
    ∀ ν : ℤ, ν ∈ childWeightSet σ σ.Φ →
      ∃ b : (↥σ.K)ˣ, ∀ c : (↥σ.K)ˣ, ((c : ↥σ.K) : F) ∈ σ.FQ →
        ∃ B, B ≠ 0 ∧ inC σ.Φ B ∧ σ.w B = ν ∧
          D.Rv B = LaurentPolynomial.C ((c * b : (↥σ.K)ˣ) : ↥σ.K) *
            LaurentPolynomial.T (- tstar * ν) := by
  intro ν hν
  obtain ⟨B₀, hB₀ne, hB₀C, hB₀w⟩ := hν
  -- the regrade weight `ν` decomposes as `e·(parent weight ν₀)` (hStretch);
  -- ν₀ := σ.wPrev B₀ lies in σ's own weight set (hWS), so σ's coset realizer fires.
  have hstretch0 : σ.w B₀ = (σ.e : ℤ) * σ.wPrev B₀ := σ.hStretch B₀ hB₀ne hB₀C
  have hν'WS : σ.wPrev B₀ ∈ σ.weightSet := σ.hWS B₀ hB₀ne hB₀C
  have hνeq : ν = (σ.e : ℤ) * σ.wPrev B₀ := by rw [← hB₀w]; exact hstretch0
  obtain ⟨b, hb⟩ := σ.hS6a (σ.wPrev B₀) hν'WS
  -- SAME base `b` transports (regrade scalars preserved via `D.hS5`)
  refine ⟨b, ?_⟩
  intro c hcFQ
  obtain ⟨B, hBne, hBC, hBwPrev, hBR⟩ := hb c hcFQ
  have hσwB : σ.w B = ν := by
    rw [σ.hStretch B hBne hBC, hBwPrev]; exact hνeq.symm
  refine ⟨B, hBne, hBC, hσwB, ?_⟩
  -- `D.hS5` gives the SAME scalar `c'` for `σ.R B` and `D.Rv B`; the parent realizer
  -- `hBR` pins that scalar's class to `c·b`, so `D.Rv B` reads off with base `b`.
  obtain ⟨c', hc'R, hc'Rv⟩ := D.hS5 B hBne hBC
  rw [hBwPrev] at hc'R
  have hCeq : LaurentPolynomial.C (c' : ↥σ.K)
            = LaurentPolynomial.C ((c * b : (↥σ.K)ˣ) : ↥σ.K) := by
    have hCT := hc'R.symm.trans hBR
    have h2 : LaurentPolynomial.C (c' : ↥σ.K)
          * LaurentPolynomial.T (- σ.t * σ.wPrev B₀)
          * LaurentPolynomial.T (σ.t * σ.wPrev B₀)
        = LaurentPolynomial.C ((c * b : (↥σ.K)ˣ) : ↥σ.K)
          * LaurentPolynomial.T (- σ.t * σ.wPrev B₀)
          * LaurentPolynomial.T (σ.t * σ.wPrev B₀) := by rw [hCT]
    rwa [mul_assoc, mul_assoc, ← LaurentPolynomial.T_add,
      show (- σ.t * σ.wPrev B₀ + σ.t * σ.wPrev B₀) = (0 : ℤ) by ring,
      LaurentPolynomial.T_zero, mul_one, mul_one] at h2
  rw [hc'Rv, hσwB, hCeq]

/-- Unit V6(b): DESCENT orbit base points — every child weight ν ∈ 𝒜′ decomposes
through a minimizing slot `(γ, j)` (the TRANSviii_a conjunct-1 window), and the
choice of slot fixes ONE coset base `b(ν)` of the displayed z̄-monomial shape
`(b : F) = (b̃ : F)·z̄^m`, whose F_Qˣ-coset is realized in the carrier `D.Rc`. -/
theorem V6_descentOrbits {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) (s' t' : ℤ)
    (hbez' : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (ht'0 : e' = 1 → t' = 0)
    (D : ChildResData σ Φhat e' h' zbar s' t') (hD : ChildResLaws D) :
    ∀ ν : ℤ, ν ∈ childWeightSet σ Φhat →
      (∃ (γ : ℤ) (j : ℕ), (∃ C, C ≠ 0 ∧ inC σ.Φ C ∧ σ.w C = γ) ∧ j < σ.e * g ∧
        ν = γ + (j : ℤ) * (σ.h : ℤ)) ∧
      ∃ b : (↥(σ.nextField zbar))ˣ,
        (∃ (btilde : (↥σ.K)ˣ) (m : ℤ),
          ((b : ↥(σ.nextField zbar)) : F)
            = ((btilde : ↥σ.K) : F) * ((zbar ^ m : Fˣ) : F)) ∧
        ∀ c : (↥(σ.nextField zbar))ˣ, ((c : ↥(σ.nextField zbar)) : F) ∈ σ.FQ →
          ∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ.w B = ν ∧
            D.Rc B = LaurentPolynomial.C
                ((c * b : (↥(σ.nextField zbar))ˣ) : ↥(σ.nextField zbar)) *
              LaurentPolynomial.T (- t' * ν) := by
  classical
  obtain ⟨hΦmon, hΦdeg⟩ := L3_liftMonic σ ψ g th.hg Φhat th.hlift
  have hΦne : Φhat ≠ 0 := hΦmon.ne_zero
  -- `σ.R 1 = 1` and `σ.w 1 = 0` (cancellation in the residual / valuation)
  have hR1 : σ.R 1 = 1 := by
    have h := σ.hRmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at h
    exact (mul_left_cancel₀ (σ.hRne 1 one_ne_zero) (by rw [mul_one]; exact h)).symm
  have hw1 : σ.w 1 = 0 := by
    have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at h; omega
  -- key-power residual and valuation
  have hRpow : ∀ k : ℕ, σ.R (σ.Φ ^ k) = (LaurentPolynomial.T σ.s) ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero]; exact hR1
    | succ n ih =>
        rw [pow_succ, σ.hRmul _ _ (pow_ne_zero n σ.hmonic.ne_zero) σ.hmonic.ne_zero, ih,
          σ.hRΦ, pow_succ]
  have hwpow : ∀ k : ℕ, σ.w (σ.Φ ^ k) = (k : ℤ) * (σ.h : ℤ) := by
    intro k
    induction k with
    | zero => rw [pow_zero, hw1]; simp
    | succ n ih =>
        rw [pow_succ, σ.hwmul _ _ (pow_ne_zero n σ.hmonic.ne_zero) σ.hmonic.ne_zero, ih, σ.hwΦ]
        push_cast; ring
  intro ν hν
  obtain ⟨B₀, hB₀ne, hB₀C, hB₀w⟩ := hν
  -- WINDOW (Part 1): develop `B₀` in base `σ.Φ`, ≤ `σ.e*g` slots, then Lemma K1.
  have hdegbound : B₀.natDegree < (σ.e * g) * σ.Φ.natDegree := by
    have h1 : B₀.degree < Φhat.degree := hB₀C
    rw [Polynomial.degree_eq_natDegree hB₀ne, Polynomial.degree_eq_natDegree hΦne] at h1
    have h2 : B₀.natDegree < Φhat.natDegree := by exact_mod_cast h1
    rw [hΦdeg] at h2
    calc B₀.natDegree < σ.e * g * σ.Φ.natDegree := h2
      _ = (σ.e * g) * σ.Φ.natDegree := by ring
  obtain ⟨Bdev, hdev⟩ := dev_exists_bounded σ.Φ σ.hmonic σ.hdeg (σ.e * g) B₀ hdegbound
  obtain ⟨-, j0, hj0lt, hj0nz, hj0eq⟩ := σ.hK1 B₀ Bdev (σ.e * g) hB₀ne hdev
  set C := Bdev j0 with hCdef
  have hCne : C ≠ 0 := hj0nz
  have hCinC : inC σ.Φ C := hdev.1 j0
  have hwin : ν = σ.w C + (j0 : ℤ) * (σ.h : ℤ) := by rw [← hB₀w, hj0eq, σ.hwΦ]
  refine ⟨⟨σ.w C, j0, ⟨C, hCne, hCinC, rfl⟩, hj0lt, hwin⟩, ?_⟩
  -- PART 2: the coset realizer for `D.Rc`, built σ-only from `σ.hS6a` (no threshold).
  have hwPrevWS : σ.wPrev C ∈ σ.weightSet := σ.hWS C hCne hCinC
  obtain ⟨bσ, hbσ⟩ := σ.hS6a (σ.wPrev C) hwPrevWS
  set m : ℤ := σ.s * (j0 : ℤ) - σ.t * σ.wPrev C with hmdef
  -- the base `b : (K')ˣ` of the displayed z̄-monomial shape `(bσ)·z̄^m`
  have hz_mem : (zbar : F) ∈ σ.nextField zbar := Subfield.subset_closure (Or.inr rfl)
  have hbσ_mem : ((bσ : ↥σ.K) : F) ∈ σ.nextField zbar :=
    Subfield.subset_closure (Or.inl (SetLike.coe_mem (bσ : ↥σ.K)))
  have hbval_mem : ((bσ : ↥σ.K) : F) * (zbar : F) ^ m ∈ σ.nextField zbar :=
    mul_mem hbσ_mem (Subfield.zpow_mem (σ.nextField zbar) hz_mem m)
  have hbσF_ne : ((bσ : ↥σ.K) : F) ≠ 0 := by
    have : (bσ : ↥σ.K) ≠ 0 := bσ.ne_zero
    simp only [ne_eq, ZeroMemClass.coe_eq_zero]; exact this
  have hbval_ne : (⟨((bσ : ↥σ.K) : F) * (zbar : F) ^ m, hbval_mem⟩ : ↥(σ.nextField zbar)) ≠ 0 := by
    simp only [ne_eq, Subtype.ext_iff]
    exact mul_ne_zero hbσF_ne (zpow_ne_zero m zbar.ne_zero)
  set b : (↥(σ.nextField zbar))ˣ :=
    Units.mk0 (⟨((bσ : ↥σ.K) : F) * (zbar : F) ^ m, hbval_mem⟩ : ↥(σ.nextField zbar)) hbval_ne with hbdef
  have hbF : ((b : ↥(σ.nextField zbar)) : F) = ((bσ : ↥σ.K) : F) * (zbar : F) ^ m := rfl
  -- exponent-combining identity
  have hzcomb : (zbar : F) ^ (- σ.t * σ.wPrev C) * ((zbar : F) ^ σ.s) ^ j0 = (zbar : F) ^ m := by
    rw [← zpow_natCast ((zbar : F) ^ σ.s) j0, ← zpow_mul, ← zpow_add₀ zbar.ne_zero]
    rw [hmdef]; ring_nf
  refine ⟨b, ⟨bσ, m, ?_⟩, ?_⟩
  · -- z̄-monomial shape of the base
    rw [hbF]; push_cast; ring
  · intro c hcFQ
    -- pull the coset scalar `c ∈ F_Q` back to a unit of `K` (F_Q ≤ K)
    have hcF_mem : ((c : ↥(σ.nextField zbar)) : F) ∈ σ.K := σ.hFQ_le hcFQ
    have hcF_ne : ((c : ↥(σ.nextField zbar)) : F) ≠ 0 := by
      have : (c : ↥(σ.nextField zbar)) ≠ 0 := c.ne_zero
      simp only [ne_eq, ZeroMemClass.coe_eq_zero]; exact this
    set cσ : (↥σ.K)ˣ :=
      Units.mk0 (⟨((c : ↥(σ.nextField zbar)) : F), hcF_mem⟩ : ↥σ.K)
        (by simp only [ne_eq, Subtype.ext_iff]; exact hcF_ne) with hcσdef
    have hcσF : ((cσ : ↥σ.K) : F) = ((c : ↥(σ.nextField zbar)) : F) := rfl
    have hcσFQ : ((cσ : ↥σ.K) : F) ∈ σ.FQ := by rw [hcσF]; exact hcFQ
    obtain ⟨Creal, hCrealNe, hCrealC, hCrealWPrev, hCrealR⟩ := hbσ cσ hcσFQ
    -- the single-slot realizer `B' := Creal · σ.Φ^{j0}`
    have hprodne : Creal * σ.Φ ^ j0 ≠ 0 := mul_ne_zero hCrealNe (pow_ne_zero j0 σ.hmonic.ne_zero)
    have hB'inC : inC Φhat (Creal * σ.Φ ^ j0) := by
      have hcnd : Creal.natDegree < σ.Φ.natDegree := by
        have h : Creal.degree < σ.Φ.degree := hCrealC
        rw [Polynomial.degree_eq_natDegree hCrealNe,
          Polynomial.degree_eq_natDegree σ.hmonic.ne_zero] at h
        exact_mod_cast h
      have hpnd : (Creal * σ.Φ ^ j0).natDegree = Creal.natDegree + j0 * σ.Φ.natDegree := by
        rw [Polynomial.natDegree_mul hCrealNe (pow_ne_zero j0 σ.hmonic.ne_zero),
          Polynomial.natDegree_pow]
      have hbound : Creal.natDegree + j0 * σ.Φ.natDegree < σ.e * g * σ.Φ.natDegree := by
        have h3 : (j0 + 1) * σ.Φ.natDegree ≤ σ.e * g * σ.Φ.natDegree := by gcongr; omega
        have h4 : (j0 + 1) * σ.Φ.natDegree = j0 * σ.Φ.natDegree + σ.Φ.natDegree := by ring
        omega
      show (Creal * σ.Φ ^ j0).degree < Φhat.degree
      rw [Polynomial.degree_eq_natDegree hprodne, Polynomial.degree_eq_natDegree hΦne, hΦdeg, hpnd]
      exact_mod_cast hbound
    have hwB' : σ.w (Creal * σ.Φ ^ j0) = ν := by
      rw [σ.hwmul Creal (σ.Φ ^ j0) hCrealNe (pow_ne_zero j0 σ.hmonic.ne_zero)]
      have hwCreal : σ.w Creal = σ.w C := by
        rw [σ.hStretch Creal hCrealNe hCrealC, hCrealWPrev, ← σ.hStretch C hCne hCinC]
      rw [hwCreal, hwpow j0, ← hwin]
    refine ⟨Creal * σ.Φ ^ j0, hprodne, hB'inC, hwB', ?_⟩
    -- digit computation: `digPrime` of the single slot = `(c)·(b)` in `F`
    have hdig : σ.digPrime zbar (Creal * σ.Φ ^ j0)
        = ((c : ↥(σ.nextField zbar)) : F) * ((b : ↥(σ.nextField zbar)) : F) := by
      have hval : σ.R (Creal * σ.Φ ^ j0)
          = LaurentPolynomial.C ((cσ * bσ : (↥σ.K)ˣ) : ↥σ.K)
              * LaurentPolynomial.T (- σ.t * σ.wPrev C) * (LaurentPolynomial.T σ.s) ^ j0 := by
        rw [σ.hRmul Creal (σ.Φ ^ j0) hCrealNe (pow_ne_zero j0 σ.hmonic.ne_zero), hCrealR, hRpow j0]
      simp only [Stage.digPrime]
      rw [hval, map_mul, map_pow, LaurentPolynomial.eval₂_C_mul_T, LaurentPolynomial.eval₂_T, hbF,
        show σ.K.subtype ((cσ * bσ : (↥σ.K)ˣ) : ↥σ.K) = (((cσ * bσ : (↥σ.K)ˣ) : ↥σ.K) : F) from rfl]
      push_cast
      rw [hcσF]
      rw [show ((c : ↥(σ.nextField zbar)) : F) * ((bσ : ↥σ.K) : F)
              * (zbar : F) ^ (- σ.t * σ.wPrev C) * ((zbar : F) ^ σ.s) ^ j0
            = ((c : ↥(σ.nextField zbar)) : F) * ((bσ : ↥σ.K) : F)
              * ((zbar : F) ^ (- σ.t * σ.wPrev C) * ((zbar : F) ^ σ.s) ^ j0) from by ring,
        hzcomb]
      ring
    -- convert to `D.Rc` via the S5′ pin and identify the digit unit with `c·b`
    obtain ⟨c'', hc''Rc, hc''dig⟩ := D.hS5' (Creal * σ.Φ ^ j0) hprodne hB'inC
    have hc''eq : (c'' : ↥(σ.nextField zbar))
        = ((c * b : (↥(σ.nextField zbar))ˣ) : ↥(σ.nextField zbar)) := by
      have hinj : Function.Injective (fun x : ↥(σ.nextField zbar) => (x : F)) :=
        fun x y hxy => Subtype.ext hxy
      apply hinj
      show ((c'' : ↥(σ.nextField zbar)) : F)
          = (((c * b : (↥(σ.nextField zbar))ˣ) : ↥(σ.nextField zbar)) : F)
      rw [hc''dig, hdig, Units.val_mul]
      push_cast; ring
    rw [hc''Rc, hwB', hc''eq]

end LeanUrat.HC1

#print axioms LeanUrat.HC1.V6_regradeOrbits
#print axioms LeanUrat.HC1.V6_descentOrbits
