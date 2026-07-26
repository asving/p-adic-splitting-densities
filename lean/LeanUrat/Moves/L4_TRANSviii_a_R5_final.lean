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
# Moves/L4_TRANSviii_a — S6a' index recursion + single-slot realizers (D.7(viii))

`moves_ref`: D.7(viii) (S6a'), the index recursion 𝒜' and the single-slot realizers with ONE
fixed z̄-monomial class per index; MOVES ~2272-2284.

## Scope note (semantic audit #5, 2026-07-26: FLAGGED-OK — conditional/local)

`MOVES_LEAN_SEMAUDIT5_2026-07-26.md` cleared this unit **at its conditional/local scope only**:
the statement is faithful GIVEN the established abstract `Stage`/`StageCoreL` residual laws (the
`child_dig_frame` repair supplies the uniform-orbit coherence — `mfun` is fixed BEFORE the orbit
scalar varies, depending only on the parent weight). It does NOT certify the deferred
graded-localization provenance (the round-1 D2 codomain fiat + D.1(e) identification). Fan-out
was authorised at this explicitly conditional/local scope (audit §"Fan-out may proceed").

## Proof

* **Conjunct 1, ⟹**: develop `B` Φ-adically with the slot budget `N = e·g` (a bounded Fact A,
  reproved inline as `dev_exists_bounded`, valid since `deg B < deg Φ̂ = e·g·deg Φ`), then read
  `σ.w B` as the ATTAINED slot minimum via Lemma K1 (`σ.hK1`, `σ.hwΦ`): the attaining slot `j`
  with digit `C := B_j ≠ 0` is the index `(γ := σ.w C, j)`, and `j < e·g` since the development
  budget is `e·g`.
* **Conjunct 1, ⟸**: the single-slot element `B := C·Φ^j` has
  `σ'.wPrev B = σ.w B = σ.w C + j·h = γ + j·h` (`child_wPrev`, `w_mul_keyPow`) and lies in `C_Φ̂`
  by the degree bound `deg C + j·deg Φ < e·g·deg Φ = deg Φ̂`.
* **Conjunct 2 (∃ m BEFORE ∀ c)**: fix `ν := σ.wPrev C₀` (so `γ = e·ν` by `hStretch`) and the
  frame function `mfun` from `htrans.child_dig_frame`, and set
  `m := (−t·ν + s·j) + mfun (γ + j·h)` — c-INDEPENDENT. For each orbit scalar `c` (transferred
  to `(↥σ.K)ˣ` through `σ'.FQ = σ.FQ ≤ σ.K`), the (S6a) realizer `C` at `(ν, c)` gives
  `B := C·Φ^j` with `σ.R B = C(c)·T(−t·ν + s·j)` (`L2_strideRule`), so
  `dig'(B) = c·z̄^{−t·ν+s·j}` (`eval₂_C_mul_T` — the orbit scalar enters LINEARLY), and
  `child_dig_frame` yields the child digit `d` with `(d:F) = dig'(B)·z̄^{mfun(γ+j·h)}
  = c·z̄^m` at the forced position `−t'·(γ+j·h)`; the weights are `child_wPrev`/`hStretch'`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false -- `hcore` is part of the fenced manifest statement

namespace LeanUrat.Moves

open Polynomial

/-- Stage-valuation of a single-slot element: `w(C·Φ^j) = w C + j·w Φ = w C + j·h`. -/
private lemma w_mul_keyPow {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
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

/-- **Bounded Fact A**: for monic `Φ` of degree `≥ 1`, every `f` with `deg f < M·deg Φ` has a
Φ-adic development with slot budget exactly `M` (the `N`-tracking refinement of
`L0_FactA_exists`, reproved inline since the on-disk statement does not expose the budget). -/
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
    -- development of the quotient, within budget `n`
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

theorem L4_TRANSviii_a {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ σ' : Stage p F) (hcore : StageCoreL σ) (g : ℕ) (Φhat : Polynomial ℤ_[p]) (hΦdeg : Φhat.natDegree = σ.e * g * σ.Φ.natDegree) (e' h' : ℕ) (zbar : Fˣ) (htrans : TransitionCoreL σ σ' Φhat e' h' zbar) : (∀ W' : ℤ, (∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ'.wPrev B = W') ↔ (∃ (γ : ℤ) (j : ℕ), (∃ C, C ≠ 0 ∧ inC σ.Φ C ∧ σ.w C = γ) ∧ j < σ.e * g ∧ W' = γ + (j : ℤ) * σ.h)) ∧ (∀ (γ : ℤ) (j : ℕ), (∃ C, C ≠ 0 ∧ inC σ.Φ C ∧ σ.w C = γ) → j < σ.e * g → ∃ m : ℤ, ∀ c : (↥σ'.K)ˣ, ((c : ↥σ'.K) : F) ∈ σ'.FQ → ∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ'.wPrev B = γ + (j : ℤ) * σ.h ∧ σ'.w B = (σ'.e : ℤ) * (γ + (j : ℤ) * σ.h) ∧ ∃ d : (↥σ'.K)ˣ, σ'.R B = LaurentPolynomial.C (d : ↥σ'.K) * LaurentPolynomial.T (- σ'.t * (γ + (j : ℤ) * σ.h)) ∧ ((d : ↥σ'.K) : F) = ((c : ↥σ'.K) : F) * ((zbar ^ m : Fˣ) : F)) := by
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
  refine ⟨?_, ?_⟩
  · -- Conjunct 1: the weight-set recursion σ'.wPrev over C_Φ̂ = { γ + j·h : γ ∈ w(C_Φ), j < e·g }.
    intro W'
    constructor
    · -- ⟹ FORWARD: bounded Φ-adic development + Lemma K1's attained slot minimum.
      rintro ⟨B, hB, hBc, hW⟩
      have hBnd : B.natDegree < σ.e * g * σ.Φ.natDegree := by
        have h := Polynomial.natDegree_lt_natDegree hB hBc
        rwa [hΦdeg] at h
      obtain ⟨Bd, hdev⟩ := dev_exists_bounded σ.Φ σ.hmonic hd1 (σ.e * g) B hBnd
      obtain ⟨-, j, hjN, hnz, hmin⟩ := σ.hK1 B Bd (σ.e * g) hB hdev
      have hnzj : Bd j ≠ 0 := hnz
      have hminb : σ.w B = σ.w (Bd j) + (j : ℤ) * (σ.w σ.Φ) := hmin
      refine ⟨σ.w (Bd j), j, ⟨Bd j, hnzj, hdev.1 j, rfl⟩, hjN, ?_⟩
      rw [← hW, htrans.base.child_wPrev, hminb, σ.hwΦ]
    · -- ⟸ BACKWARD: the single-slot realizer B := C·Φ^j.
      rintro ⟨γ, j, ⟨C, hC, hCc, hCw⟩, hj, hW⟩
      have hΦj : σ.Φ ^ j ≠ 0 := pow_ne_zero j hΦ
      refine ⟨C * σ.Φ ^ j, mul_ne_zero hC hΦj, hslot C j hC hCc hj, ?_⟩
      rw [htrans.base.child_wPrev, w_mul_keyPow σ C hC j, hCw]
      exact hW.symm
  · -- Conjunct 2: single-slot realizers, ONE fixed z̄-monomial class per index (∃ m BEFORE ∀ c).
    rintro γ j ⟨C₀, hC₀0, hC₀c, hC₀w⟩ hj
    -- the parent-scale weight ν of the index: γ = e·ν (hStretch), ν ∈ 𝒲 (hWS)
    have hν : σ.wPrev C₀ ∈ σ.weightSet := σ.hWS C₀ hC₀0 hC₀c
    have hγ : γ = (σ.e : ℤ) * σ.wPrev C₀ := by
      rw [← hC₀w]; exact σ.hStretch C₀ hC₀0 hC₀c
    -- the frame function, fixed BEFORE the orbit scalar varies (child_dig_frame)
    obtain ⟨mfun, hmf⟩ := htrans.child_dig_frame
    -- the c-INDEPENDENT frame exponent of the index (γ, j)
    refine ⟨(- σ.t * σ.wPrev C₀ + σ.s * (j : ℤ)) + mfun (γ + (j : ℤ) * σ.h), ?_⟩
    intro c hcFQ
    -- transfer the orbit scalar c through σ'.FQ = σ.FQ ≤ σ.K
    have hx0 : ((c : ↥σ'.K) : F) ≠ 0 :=
      fun h => (Units.ne_zero c) (ZeroMemClass.coe_eq_zero.mp h)
    have hxFQ : ((c : ↥σ'.K) : F) ∈ σ.FQ := htrans.base.child_base ▸ hcFQ
    have hxK : ((c : ↥σ'.K) : F) ∈ σ.K := σ.hFQ_le hxFQ
    have hc₁0 : (⟨((c : ↥σ'.K) : F), hxK⟩ : ↥σ.K) ≠ 0 := by
      simp [Subtype.ext_iff, hx0]
    set c₁ : (↥σ.K)ˣ := Units.mk0 ⟨((c : ↥σ'.K) : F), hxK⟩ hc₁0 with hc₁
    have hc₁FQ : ((c₁ : ↥σ.K) : F) ∈ σ.FQ := hxFQ
    -- the (S6a) basic realizer at (ν, c)
    obtain ⟨C, hC0, hCc, hCν, hCR⟩ := σ.hS6a (σ.wPrev C₀) hν c₁ hc₁FQ
    have hCw : σ.w C = γ := by
      rw [σ.hStretch C hC0 hCc, hCν]; exact hγ.symm
    -- the single-slot realizer B := C·Φ^j and its weights
    have hB0 : C * σ.Φ ^ j ≠ 0 := mul_ne_zero hC0 (pow_ne_zero j hΦ)
    have hBinC : inC Φhat (C * σ.Φ ^ j) := hslot C j hC0 hCc hj
    have hwB : σ.w (C * σ.Φ ^ j) = γ + (j : ℤ) * σ.h := by
      rw [w_mul_keyPow σ C hC0 j, hCw]
    have hwPrevB : σ'.wPrev (C * σ.Φ ^ j) = γ + (j : ℤ) * σ.h := by
      rw [htrans.base.child_wPrev]; exact hwB
    refine ⟨C * σ.Φ ^ j, hB0, hBinC, hwPrevB, ?_, ?_⟩
    · -- σ'.w B = e'·(γ + j·h), via the child's own stretch law
      have hBc' : inC σ'.Φ (C * σ.Φ ^ j) := by
        rw [htrans.base.child_key]; exact hBinC
      rw [σ'.hStretch _ hB0 hBc', hwPrevB]
    · -- the child digit: position −t'·(γ+j·h), scalar d = c·z̄^m
      obtain ⟨d, hdR, hdF⟩ := hmf (C * σ.Φ ^ j) hB0 hBinC
      rw [hwB] at hdR hdF
      refine ⟨d, hdR, ?_⟩
      -- the parent residual of the slot element: R(B) = C(c₁)·T(−t·ν + s·j) (stride rule)
      have hRB : σ.R (C * σ.Φ ^ j)
          = LaurentPolynomial.C (c₁ : ↥σ.K)
            * LaurentPolynomial.T (- σ.t * σ.wPrev C₀ + σ.s * (j : ℤ)) := by
        rw [L2_strideRule σ C hC0 hCc j, hCR, mul_assoc, ← LaurentPolynomial.T_add]
      -- the parent digit: dig'(B) = c·z̄^{−t·ν+s·j} — the orbit scalar enters LINEARLY
      have hdig : σ.digPrime zbar (C * σ.Φ ^ j)
          = ((c : ↥σ'.K) : F)
            * ((zbar ^ (- σ.t * σ.wPrev C₀ + σ.s * (j : ℤ)) : Fˣ) : F) := by
        show LaurentPolynomial.eval₂ σ.K.subtype zbar (σ.R (C * σ.Φ ^ j)) = _
        rw [hRB, LaurentPolynomial.eval₂_C_mul_T]
        rfl
      rw [hdF, hdig, mul_assoc, ← Units.val_mul, ← zpow_add]

end LeanUrat.Moves
