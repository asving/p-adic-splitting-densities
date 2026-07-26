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

/-!
# Moves/L4_TRANSviii_a — S6a' index recursion + single-slot realizers (D.7(viii))

`moves_ref`: D.7(viii) (S6a'), the index recursion 𝒜' and the single-slot realizers with ONE
fixed z̄-monomial class per index; MOVES ~2272-2284.

## Scope note (semantic audit #5, 2026-07-26: FLAGGED-OK — conditional/local)

`MOVES_LEAN_SEMAUDIT5_2026-07-26.md` cleared this unit **at its conditional/local scope only**: the
statement is faithful GIVEN the established abstract `Stage`/`StageCoreL` residual laws (the
`child_dig_frame` repair supplies the uniform-orbit coherence — `mfun` is fixed BEFORE the orbit
scalar varies, depending only on the parent weight). It does NOT certify the deferred
graded-localization provenance (the round-1 D2 codomain fiat + D.1(e) identification). Fan-out was
authorised at this explicitly conditional/local scope (audit §"Fan-out may proceed").

## Proof status (this file)

* **Conjunct 1, ⟸ (weight-set recursion, backward):** PROVED. The single-slot element `B := C·Φ^j`
  has `σ'.wPrev B = σ.w B = σ.w C + j·h = γ + j·h` (`child_wPrev`, `w_mul_keyPow`) and lies in
  `C_Φ̂` by the degree bound `deg C + j·deg Φ < e·g·deg Φ = deg Φ̂`.
* **Conjunct 1, ⟹ (forward):** `sorry` — genuinely requires the Φ-adic development of `B ∈ C_Φ̂`
  (Fact A) plus Lemma K1 (`σ.hK1`) to read `σ.w B` as the attained slot-minimum
  `min_{i<eg}(σ.w C_i + i·h)`, then extract the minimizing slot as the index `(γ, i)`. Not closed
  within this unit's budget.
* **Conjunct 2 (single-slot realizers, ∃m ∀c):** `sorry` — the construction is derived in the
  comment there; the residual arithmetic (`hS6a` realizer · `Φ^j` via `L2_strideRule`, then the
  `child_dig_frame` frame unit, then the `eval₂` digit computation showing the orbit scalar `c`
  enters LINEARLY so `m` is c-independent) is not closed within budget.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

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

theorem L4_TRANSviii_a {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ σ' : Stage p F) (hcore : StageCoreL σ) (g : ℕ) (Φhat : Polynomial ℤ_[p]) (hΦdeg : Φhat.natDegree = σ.e * g * σ.Φ.natDegree) (e' h' : ℕ) (zbar : Fˣ) (htrans : TransitionCoreL σ σ' Φhat e' h' zbar) : (∀ W' : ℤ, (∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ'.wPrev B = W') ↔ (∃ (γ : ℤ) (j : ℕ), (∃ C, C ≠ 0 ∧ inC σ.Φ C ∧ σ.w C = γ) ∧ j < σ.e * g ∧ W' = γ + (j : ℤ) * σ.h)) ∧ (∀ (γ : ℤ) (j : ℕ), (∃ C, C ≠ 0 ∧ inC σ.Φ C ∧ σ.w C = γ) → j < σ.e * g → ∃ m : ℤ, ∀ c : (↥σ'.K)ˣ, ((c : ↥σ'.K) : F) ∈ σ'.FQ → ∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ'.wPrev B = γ + (j : ℤ) * σ.h ∧ σ'.w B = (σ'.e : ℤ) * (γ + (j : ℤ) * σ.h) ∧ ∃ d : (↥σ'.K)ˣ, σ'.R B = LaurentPolynomial.C (d : ↥σ'.K) * LaurentPolynomial.T (- σ'.t * (γ + (j : ℤ) * σ.h)) ∧ ((d : ↥σ'.K) : F) = ((c : ↥σ'.K) : F) * ((zbar ^ m : Fˣ) : F)) := by
  refine ⟨?_, ?_⟩
  · -- Conjunct 1: the weight-set recursion σ'.wPrev over C_Φ̂ = { σ.w C + j·h : ... }.
    intro W'
    constructor
    · -- ⟹ FORWARD: develop B Φ-adically (Fact A), read σ.w B as the K1 slot-minimum,
      -- extract the minimizing slot (i, γ = σ.w C_i).  Needs σ.hK1 + development existence.
      rintro ⟨B, hB, hBc, hW⟩
      sorry
    · -- ⟸ BACKWARD: the single-slot realizer B := C·Φ^j.
      rintro ⟨γ, j, ⟨C, hC, hCc, hCw⟩, hj, hW⟩
      have hΦ : σ.Φ ≠ 0 := σ.hmonic.ne_zero
      have hΦj : σ.Φ ^ j ≠ 0 := pow_ne_zero j hΦ
      have hB0 : C * σ.Φ ^ j ≠ 0 := mul_ne_zero hC hΦj
      have hCd : C.natDegree < σ.Φ.natDegree := Polynomial.natDegree_lt_natDegree hC hCc
      have hd1 : 1 ≤ σ.Φ.natDegree := σ.hdeg
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
      refine ⟨C * σ.Φ ^ j, hB0, ?_, ?_⟩
      · show (C * σ.Φ ^ j).degree < Φhat.degree
        rw [Polynomial.degree_eq_natDegree hB0, Polynomial.degree_eq_natDegree hΦhat0]
        exact_mod_cast hBnd
      · rw [htrans.base.child_wPrev, w_mul_keyPow σ C hC j, hCw]
        exact hW.symm
  · -- Conjunct 2: single-slot realizers, one fixed z̄-monomial class per index.
    -- CONSTRUCTION (derived; not closed in budget):
    --   ν := σ.wPrev C₀ ∈ σ.weightSet (hWS); e·ν = σ.w C₀ = γ (hStretch).
    --   For each orbit scalar c ∈ FQ, hS6a ν c gives C with R C = C(c)·T(−t·ν);
    --   B := C·Φ^j.  Then σ'.wPrev B = σ.w B = γ + j·h; σ'.w B = σ'.e·(γ+j·h) (σ'.hStretch);
    --   R B via L2_strideRule = C(c)·T(−t·ν + s·j); child_dig_frame gives σ'.R B shape and
    --   (d:F) = digPrime zbar B · zbar^{mfun(σ.w B)}.  digPrime zbar B = (c:F)·zbar^{−tν+sj}
    --   (eval₂), so m := (−t·ν + s·j) + mfun(γ+j·h) is FIXED (c enters linearly), independent of c.
    intro γ j hCex hj
    sorry

end LeanUrat.Moves
