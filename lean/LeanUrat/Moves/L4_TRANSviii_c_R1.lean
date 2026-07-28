/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL
import LeanUrat.Moves.L2_strideRule

/-!
# Moves/L4_TRANSviii_c — the σ′-FREE weight-pinned digPrime coset realizer (D.7(viii))

`moves_ref`: D.7(viii)'s realizer display (MOVES 2423–2435) read at the RAW-PIN
(`mfun ≡ 0`) normalization — the S9a/V7 escalation artifact (2026-07-28).

## Why this unit exists (the escalation finding)

`L4_TRANSviii_a` conjunct 2 produces the child coset realizers, but it consumes a FULL
child `Stage σ'` through `TransitionCoreL` — and σ'.hS6a IS the strip realizer being
proved, so S9a cannot consume it (circular; first-prover census, S9a_final escalation).
This unit re-derives conjunct 2's content ENTIRELY over the parent σ, at the F-valued
`digPrime` level: no child stage, no carrier, no frame function. The only child-side
inputs are the lift degree `deg Φ̂ = e·g·deg Φ` and the read root `z̄` — both plain data.
Consumers (V7 → S9a hS6a′) pin the resulting digit through `ChildResData.hS5'`
(position `−t′·σ.w B`, scalar = `digPrime` exactly), which converts this lemma's coset
of digits into the coset of `Rc`-scalars — the exact `Stage.hS6a` field shape.

## Statement

For every weight ν REALIZED in `C_Φ̂` (i.e. ν ∈ 𝒜′ = `childWeightSet`; NO threshold
hypothesis — the strip and the above-threshold region are treated uniformly), there is
ONE base `bF ∈ Fˣ` such that for every orbit scalar `c ∈ F_Qˣ` there is a realizer
`B ∈ C_Φ̂` with `σ.w B = ν` and `dig′_{z̄}(B) = c·bF`.

## Proof

Slot-decompose the given witness `B₀` (bounded Fact A with budget `e·g`, Lemma K1's
attained slot minimum): `ν = γ + j·h`, `γ = σ.w C₀`, `C₀ := (B₀)_j ∈ C_Φ` nonzero,
`j < e·g`. Fix the PARENT coset base `b` from `σ.hS6a` at `ν̃ := σ.wPrev C₀` (γ = e·ν̃ by
`hStretch`) and set `bF := b·z̄^{−t·ν̃+s·j}` — both c-INDEPENDENT. For each `c ∈ F_Q`,
the (S6a) realizer `C` at `(ν̃, c)` gives `B := C·Φ^j ∈ C_Φ̂` (degree bound `j < e·g`),
`σ.w B = γ + j·h = ν` (`w_mul_keyPow` + `hStretch` twice), and
`σ.R B = C(c·b)·T(−t·ν̃ + s·j)` (`L2_strideRule`), so
`dig′(B) = (c·b)·z̄^{−t·ν̃+s·j} = c·bF` (`eval₂_C_mul_T` — the orbit scalar enters
LINEARLY). The private lemmas `w_mul_keyPow`/`dev_exists_bounded` are reproved inline
(they are `private` in `L4_TRANSviii_a_R5_final`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanUrat.Moves

open Polynomial

/-- Stage-valuation of a single-slot element: `w(C·Φ^j) = w C + j·w Φ = w C + j·h`. -/
private lemma w_mul_keyPow' {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (C : Polynomial ℤ_[p]) (hC : C ≠ 0) (j : ℕ) :
    σ.w (C * σ.Φ ^ j) = σ.w C + (j : ℤ) * (σ.h : ℤ) := by
  have hΦ : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  induction j with
  | zero => simp
  | succ n ih =>
    have hΦn : σ.Φ ^ n ≠ 0 := pow_ne_zero n hΦ
    have hrw : C * σ.Φ ^ (n + 1) = (C * σ.Φ ^ n) * σ.Φ := by ring
    rw [hrw, σ.hwmul _ _ (mul_ne_zero hC hΦn) hΦ, ih, σ.hwΦ]
    push_cast; ring

/-- **Bounded Fact A** (reproved inline; `private` in `L4_TRANSviii_a_R5_final`): for
monic `Φ` of degree `≥ 1`, every `f` with `deg f < M·deg Φ` has a Φ-adic development
with slot budget exactly `M`. -/
private lemma dev_exists_bounded' {R : Type*} [CommRing R] (Φ : Polynomial R) (hΦ : Φ.Monic)
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

/-- **The σ′-free weight-pinned digPrime coset realizer** (D.7(viii) at the raw pin):
every weight ν realized in `C_Φ̂` carries ONE digit base `bF` (nonzero, c-independent)
whose `F_Q`-coset is realized at ν — `∃ B ∈ C_Φ̂, σ.w B = ν, dig′_{z̄}(B) = c·bF` for
every `c ∈ F_Qˣ`. NO child stage, carrier, or threshold hypothesis is consumed: the
realizers are parent (S6a) coset realizers ridden up one slot (`L2_strideRule`). -/
theorem L4_TRANSviii_c {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (g : ℕ) (Φhat : Polynomial ℤ_[p])
    (hΦdeg : Φhat.natDegree = σ.e * g * σ.Φ.natDegree) (zbar : Fˣ) (ν : ℤ)
    (hν : ∃ B₀, B₀ ≠ 0 ∧ inC Φhat B₀ ∧ σ.w B₀ = ν) :
    ∃ bF : F, bF ≠ 0 ∧ ∀ cF : F, cF ∈ σ.FQ → cF ≠ 0 →
      ∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ.w B = ν ∧ σ.digPrime zbar B = cF * bF := by
  classical
  have hΦ : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hd1 : 1 ≤ σ.Φ.natDegree := σ.hdeg
  -- degree bound for single-slot elements `C·Φ^j`, `j < e·g`: they lie in `C_Φ̂`
  have hslot : ∀ (C : Polynomial ℤ_[p]) (j : ℕ), C ≠ 0 → inC σ.Φ C → j < σ.e * g →
      inC Φhat (C * σ.Φ ^ j) := by
    intro C j hC hCc hj
    have hΦj : σ.Φ ^ j ≠ 0 := pow_ne_zero j hΦ
    have hB0 : C * σ.Φ ^ j ≠ 0 := mul_ne_zero hC hΦj
    have hCd : C.natDegree < σ.Φ.natDegree := Polynomial.natDegree_lt_natDegree hC hCc
    have hΦhat0 : Φhat ≠ 0 := by
      intro h
      rw [h, Polynomial.natDegree_zero] at hΦdeg
      have hpos : 0 < σ.e * g * σ.Φ.natDegree :=
        Nat.mul_pos (by omega) (by omega)
      omega
    have hBnd : (C * σ.Φ ^ j).natDegree < Φhat.natDegree := by
      rw [Polynomial.natDegree_mul hC hΦj, Polynomial.natDegree_pow, hΦdeg]
      have h2 : (j + 1) * σ.Φ.natDegree ≤ σ.e * g * σ.Φ.natDegree := by gcongr; omega
      calc C.natDegree + j * σ.Φ.natDegree
          < σ.Φ.natDegree + j * σ.Φ.natDegree := by omega
        _ = (j + 1) * σ.Φ.natDegree := by ring
        _ ≤ σ.e * g * σ.Φ.natDegree := h2
    show (C * σ.Φ ^ j).degree < Φhat.degree
    rw [Polynomial.degree_eq_natDegree hB0, Polynomial.degree_eq_natDegree hΦhat0]
    exact_mod_cast hBnd
  -- ## Slot-decompose the witness: ν = γ + j·h, γ = σ.w (B₀)_j, j < e·g
  obtain ⟨B₀, hB₀, hB₀c, hB₀w⟩ := hν
  have hBnd : B₀.natDegree < σ.e * g * σ.Φ.natDegree := by
    have h := Polynomial.natDegree_lt_natDegree hB₀ hB₀c
    rwa [hΦdeg] at h
  obtain ⟨Bd, hdev⟩ := dev_exists_bounded' σ.Φ σ.hmonic hd1 (σ.e * g) B₀ hBnd
  obtain ⟨-, j, hjN, hnz, hmin⟩ := σ.hK1 B₀ Bd (σ.e * g) hB₀ hdev
  have hC₀c : inC σ.Φ (Bd j) := hdev.1 j
  -- the decomposition ν = σ.w (Bd j) + j·h
  have hνdec : ν = σ.w (Bd j) + (j : ℤ) * (σ.h : ℤ) := by
    rw [← hB₀w, hmin, σ.hwΦ]
  -- ## The parent coset base at ν̃ := σ.wPrev (Bd j), and the c-independent digit base bF
  have hnutil : σ.wPrev (Bd j) ∈ σ.weightSet := σ.hWS (Bd j) hnz hC₀c
  obtain ⟨b, hb⟩ := σ.hS6a (σ.wPrev (Bd j)) hnutil
  refine ⟨((b : ↥σ.K) : F) *
    ((zbar ^ (- σ.t * σ.wPrev (Bd j) + σ.s * (j : ℤ)) : Fˣ) : F), ?_, ?_⟩
  · -- bF ≠ 0: a K-unit image times a z̄-monomial
    exact mul_ne_zero (fun h => Units.ne_zero b (ZeroMemClass.coe_eq_zero.mp h))
      (Units.ne_zero _)
  · -- ## The realizer family: parent (S6a) realizers ridden up slot j
    intro cF hcFQ hcF0
    -- transfer the orbit scalar into (↥σ.K)ˣ
    have hcK : cF ∈ σ.K := σ.hFQ_le hcFQ
    have hc₁0 : (⟨cF, hcK⟩ : ↥σ.K) ≠ 0 := by simp [Subtype.ext_iff, hcF0]
    set c₁ : (↥σ.K)ˣ := Units.mk0 ⟨cF, hcK⟩ hc₁0 with hc₁def
    have hc₁FQ : ((c₁ : ↥σ.K) : F) ∈ σ.FQ := hcFQ
    -- the (S6a) coset realizer at (ν̃, c₁)
    obtain ⟨C, hC0, hCc, hCν, hCR⟩ := hb c₁ hc₁FQ
    -- the single-slot realizer B := C·Φ^j
    have hB0 : C * σ.Φ ^ j ≠ 0 := mul_ne_zero hC0 (pow_ne_zero j hΦ)
    have hBinC : inC Φhat (C * σ.Φ ^ j) := hslot C j hC0 hCc hjN
    -- weight: σ.w C = e·wPrev C = e·ν̃ = σ.w (Bd j), so σ.w B = ν
    have hwC : σ.w C = σ.w (Bd j) := by
      rw [σ.hStretch C hC0 hCc, hCν, ← σ.hStretch (Bd j) hnz hC₀c]
    have hwB : σ.w (C * σ.Φ ^ j) = ν := by
      rw [w_mul_keyPow' σ C hC0 j, hwC]
      exact hνdec.symm
    -- residual: R(B) = C(c₁·b)·T(−t·ν̃ + s·j) (stride rule)
    have hRB : σ.R (C * σ.Φ ^ j)
        = LaurentPolynomial.C ((c₁ * b : (↥σ.K)ˣ) : ↥σ.K)
          * LaurentPolynomial.T (- σ.t * σ.wPrev (Bd j) + σ.s * (j : ℤ)) := by
      rw [L2_strideRule σ C hC0 hCc j, hCR, mul_assoc, ← LaurentPolynomial.T_add]
    -- digit: dig′(B) = (c₁·b)·z̄^{−t·ν̃+s·j} = cF·bF — the orbit scalar enters LINEARLY
    have hdig : σ.digPrime zbar (C * σ.Φ ^ j)
        = (((c₁ * b : (↥σ.K)ˣ) : ↥σ.K) : F)
          * ((zbar ^ (- σ.t * σ.wPrev (Bd j) + σ.s * (j : ℤ)) : Fˣ) : F) := by
      show LaurentPolynomial.eval₂ σ.K.subtype zbar (σ.R (C * σ.Φ ^ j)) = _
      rw [hRB, LaurentPolynomial.eval₂_C_mul_T]
      rfl
    refine ⟨C * σ.Φ ^ j, hB0, hBinC, hwB, ?_⟩
    have hc₁F : ((c₁ : ↥σ.K) : F) = cF := by rw [hc₁def]; rfl
    rw [hdig, Units.val_mul, MulMemClass.coe_mul, hc₁F, mul_assoc]

end LeanUrat.Moves

#print axioms LeanUrat.Moves.L4_TRANSviii_c
