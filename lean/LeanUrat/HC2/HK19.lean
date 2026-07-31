/-
Unit HK-19  (BRIDGE campaign, area BP2, cluster BP2-c2 — E-phase statement skeleton)
blueprint: lean/notes/BRIDGE_BP2_HC2K1_2026-07-30.md §4 Block G, unit HK-19.

INFORMAL STATEMENT (blueprint): "SideReads at read 0 for f, clauses (i)/(ii) — the base
development of f (concrete coefficients; U31's `sideReads_ν₀` machinery de-privatized).
(Clauses (iii)–(vi) split to HK-57 at REVISION 2, finding 16.)"  deps: HK-18.

E-PHASE SHAPE: `SideReads` is one bundled Prop; per its own docstring U20–U22 "consume
its conjuncts by name", so the clause-(i)/(ii) content is stated as the LITERAL conjunct
types of `SideReads ν₀gate Bdev0 5 _` (byte-copies of HC2/Defs.SideReads at
ν := HK18.ν₀gate, B := Bdev0, Nd := 5) — HK-22 reassembles them with HK-57's (iii)–(vi)
by `refine ⟨⟨_, _⟩, _, …⟩`. The base development itself (`Bdev0_dev`) is included here:
it is the `ReadsOf` per-read witness datum at i = 0 (the blueprint's "the base
development of f").

DATA (from HK-18 resolution R-1): fgate = X⁴ + 4X³ + 14X² + 20X + 40 in base
coordinates; Bdev0 = (C 40, C 20, C 14, C 4, 1); coefficient valuations
(3, 2, 1, 2, 0); (1,1) side functional values (3, 3, 3, 5, 4) — γ₀ = 3 attained
exactly at slots 0, 1, 2 = the strides s0 + k, k ≤ wSide/e = 2, digits all 1.

PROOF SKETCH (P-phase): U31's toolkit verbatim at the new constants — `bw_eq` against
normal forms NF(θ(C 40)) = (3, C 5), NF(θ(C 20)) = (2, C 5), NF(θ(C 14)) = (1, C 7),
NF(θ(C 4)) = (2, 1), NF(θ 1) = (0, 1) (units 5, 7 have nonzero mod-2 digit);
`bR_const`-style digit lemmas give the clause-(ii) monomial-unit residuals at position
0 (σ.t = 0). interval_cases on j/k. Difficulty hard-fable ~80 (blueprint).
-/
import Mathlib
import LeanUrat.HC2.HK18

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.MovesJ

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

namespace HK19

open HK18

/-! ### Local normal-form table: the base-development coefficient weights (P-phase;
residuals are `HK13R.bR_const`, weights via `HK13R.bw_C_two_pow_mul` at the 2-adic
normal forms 40 = 2³·5, 20 = 2²·5, 14 = 2·7, 4 = 2²·1). -/

lemma bw_C40 : U31.bw (Polynomial.C (40 : ℤ_[2])) = 3 := by
  have h : (40 : ℤ_[2]) = 2 ^ 3 * 5 := by norm_num
  rw [h, HK13R.bw_C_two_pow_mul (by rw [HK13R.ρ_five]; exact one_ne_zero)]
  norm_num

lemma bw_C20 : U31.bw (Polynomial.C (20 : ℤ_[2])) = 2 := by
  have h : (20 : ℤ_[2]) = 2 ^ 2 * 5 := by norm_num
  rw [h, HK13R.bw_C_two_pow_mul (by rw [HK13R.ρ_five]; exact one_ne_zero)]
  norm_num

lemma bw_C14 : U31.bw (Polynomial.C (14 : ℤ_[2])) = 1 := by
  have h : (14 : ℤ_[2]) = 2 ^ 1 * 7 := by norm_num
  rw [h, HK13R.bw_C_two_pow_mul (by rw [HK13R.ρ_seven]; exact one_ne_zero)]
  norm_num

lemma bw_C4 : U31.bw (Polynomial.C (4 : ℤ_[2])) = 2 := by
  have h : (4 : ℤ_[2]) = 2 ^ 2 * 1 := by norm_num
  rw [h, HK13R.bw_C_two_pow_mul HK13R.ρ_one_ne]
  norm_num

/-- The base (frame-0, key X) development of fgate: slot coefficients
(C 40, C 20, C 14, C 4, 1), window length 5. -/
noncomputable def Bdev0 : ℕ → Polynomial ℤ_[2] :=
  fun j =>
    if j = 0 then Polynomial.C 40
    else if j = 1 then Polynomial.C 20
    else if j = 2 then Polynomial.C 14
    else if j = 3 then Polynomial.C 4
    else if j = 4 then 1
    else 0

/-- Bdev0 IS fgate's development at the base key X (the `ReadsOf` i = 0 witness
datum; degree bounds + tail zeros + the window sum). -/
theorem Bdev0_dev : IsDevelopment (Polynomial.X : Polynomial ℤ_[2]) fgate Bdev0 5 := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    rw [degree_X]
    unfold Bdev0
    split_ifs
    · exact lt_of_le_of_lt degree_C_le (by norm_num)
    · exact lt_of_le_of_lt degree_C_le (by norm_num)
    · exact lt_of_le_of_lt degree_C_le (by norm_num)
    · exact lt_of_le_of_lt degree_C_le (by norm_num)
    · exact lt_of_le_of_lt degree_one_le (by norm_num)
    · rw [degree_zero]
      exact bot_lt_iff_ne_bot.mpr (by norm_num)
  · intro j hj
    unfold Bdev0
    split_ifs with h1 h2 h3 h4 h5
    · exact absurd h1 (by omega)
    · exact absurd h2 (by omega)
    · exact absurd h3 (by omega)
    · exact absurd h4 (by omega)
    · exact absurd h5 (by omega)
    · rfl
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one]
    have h0 : Bdev0 0 = Polynomial.C 40 := rfl
    have h1 : Bdev0 1 = Polynomial.C 20 := rfl
    have h2 : Bdev0 2 = Polynomial.C 14 := rfl
    have h3 : Bdev0 3 = Polynomial.C 4 := rfl
    have h4 : Bdev0 4 = 1 := rfl
    rw [h0, h1, h2, h3, h4, fgate, U31.fq]
    simp only [map_ofNat]
    ring

/-- SideReads clause (i), lower bound, at (ν₀gate, Bdev0, 5): the read functional
`e·w(B_j) + j·h` is ≥ the recorded total side weight γ₀ = 3 at every nonzero slot
(the side is a genuine lower-hull support line). Byte-copy of the first (i) conjunct
of `SideReads`. -/
theorem sideReads0_side_lb :
    ∀ j : ℕ, j < 5 → Bdev0 j ≠ 0 →
      ν₀gate.gam ≤ (ν₀gate.e : ℤ) * ν₀gate.σ.w (Bdev0 j) + (j : ℤ) * (ν₀gate.h : ℤ) := by
  intro j hj hBj
  show (3 : ℤ) ≤ ((1 : ℕ) : ℤ) * U31.bw (Bdev0 j) + (j : ℤ) * ((1 : ℕ) : ℤ)
  interval_cases j
  · rw [show U31.bw (Bdev0 0) = 3 from bw_C40]
    norm_num
  · rw [show U31.bw (Bdev0 1) = 2 from bw_C20]
    norm_num
  · rw [show U31.bw (Bdev0 2) = 1 from bw_C14]
    norm_num
  · rw [show U31.bw (Bdev0 3) = 2 from bw_C4]
    norm_num
  · rw [show U31.bw (Bdev0 4) = 0 from HK13R.bw_one]
    norm_num

/-- SideReads clause (i), equality slots are stride slots, at (ν₀gate, Bdev0, 5):
equality holds ONLY at the recorded stride digits j = s0 + e·k = k, k ≤ 2, pat k ≠ 0.
Byte-copy of the second (i) conjunct of `SideReads`. -/
theorem sideReads0_side_eq :
    ∀ j : ℕ, j < 5 → Bdev0 j ≠ 0 →
      (ν₀gate.e : ℤ) * ν₀gate.σ.w (Bdev0 j) + (j : ℤ) * (ν₀gate.h : ℤ) = ν₀gate.gam →
      ∃ k : ℕ, k ≤ ν₀gate.wSide / ν₀gate.e ∧ j = ν₀gate.s0 + ν₀gate.e * k ∧
        ν₀gate.pat k ≠ 0 := by
  intro j hj hBj heq
  have heq' : ((1 : ℕ) : ℤ) * U31.bw (Bdev0 j) + (j : ℤ) * ((1 : ℕ) : ℤ) = 3 := heq
  interval_cases j
  · exact ⟨0, (by norm_num : (0 : ℕ) ≤ 2 / 1), (by norm_num : (0 : ℕ) = 0 + 1 * 0),
      (one_ne_zero : (1 : ↥U31.K2) ≠ 0)⟩
  · exact ⟨1, (by norm_num : (1 : ℕ) ≤ 2 / 1), (by norm_num : (1 : ℕ) = 0 + 1 * 1),
      (one_ne_zero : (1 : ↥U31.K2) ≠ 0)⟩
  · exact ⟨2, (by norm_num : (2 : ℕ) ≤ 2 / 1), (by norm_num : (2 : ℕ) = 0 + 1 * 2),
      (one_ne_zero : (1 : ↥U31.K2) ≠ 0)⟩
  · rw [show U31.bw (Bdev0 3) = 2 from bw_C4] at heq'
    norm_num at heq'
  · rw [show U31.bw (Bdev0 4) = 0 from HK13R.bw_one] at heq'
    norm_num at heq'

/-- SideReads clause (ii), DIGITS, at (ν₀gate, Bdev0, 5): at every recorded stride slot
the coefficient is nonzero, ON the side, and its residual is the monomial-unit with
scalar pat k = 1 at the forced (S5) position −σ.t·σ.wPrev(B) = 0. Byte-copy of the (ii)
conjunct of `SideReads`. -/
theorem sideReads0_digits :
    ∀ k : ℕ, k ≤ ν₀gate.wSide / ν₀gate.e → ν₀gate.pat k ≠ 0 →
      Bdev0 (ν₀gate.s0 + ν₀gate.e * k) ≠ 0 ∧
      (ν₀gate.e : ℤ) * ν₀gate.σ.w (Bdev0 (ν₀gate.s0 + ν₀gate.e * k))
          + ((ν₀gate.s0 + ν₀gate.e * k : ℕ) : ℤ) * (ν₀gate.h : ℤ) = ν₀gate.gam ∧
      ν₀gate.σ.R (Bdev0 (ν₀gate.s0 + ν₀gate.e * k)) =
        LaurentPolynomial.C (ν₀gate.pat k) *
          LaurentPolynomial.T (- ν₀gate.σ.t * ν₀gate.σ.wPrev (Bdev0 (ν₀gate.s0 + ν₀gate.e * k))) := by
  intro k hk hpat
  have hk2 : k ≤ 2 := hk
  interval_cases k
  · refine ⟨?_, ?_, ?_⟩
    · show Polynomial.C (40 : ℤ_[2]) ≠ 0
      exact Polynomial.C_ne_zero.mpr (by norm_num)
    · show ((1 : ℕ) : ℤ) * U31.bw (Bdev0 (0 + 1 * 0)) + ((0 + 1 * 0 : ℕ) : ℤ) * ((1 : ℕ) : ℤ) = 3
      rw [show U31.bw (Bdev0 (0 + 1 * 0)) = 3 from bw_C40]
      norm_num
    · have hgoal : U31.bR (Polynomial.C (40 : ℤ_[2])) = LaurentPolynomial.C ((1 : ↥U31.K2)) *
          LaurentPolynomial.T (- (0 : ℤ) * gaussVal (Polynomial.C (40 : ℤ_[2]))) := by
        rw [HK13R.bR_const (by norm_num : (40 : ℤ_[2]) ≠ 0), map_one, neg_zero, zero_mul,
          LaurentPolynomial.T_zero, one_mul]
      exact hgoal
  · refine ⟨?_, ?_, ?_⟩
    · show Polynomial.C (20 : ℤ_[2]) ≠ 0
      exact Polynomial.C_ne_zero.mpr (by norm_num)
    · show ((1 : ℕ) : ℤ) * U31.bw (Bdev0 (0 + 1 * 1)) + ((0 + 1 * 1 : ℕ) : ℤ) * ((1 : ℕ) : ℤ) = 3
      rw [show U31.bw (Bdev0 (0 + 1 * 1)) = 2 from bw_C20]
      norm_num
    · have hgoal : U31.bR (Polynomial.C (20 : ℤ_[2])) = LaurentPolynomial.C ((1 : ↥U31.K2)) *
          LaurentPolynomial.T (- (0 : ℤ) * gaussVal (Polynomial.C (20 : ℤ_[2]))) := by
        rw [HK13R.bR_const (by norm_num : (20 : ℤ_[2]) ≠ 0), map_one, neg_zero, zero_mul,
          LaurentPolynomial.T_zero, one_mul]
      exact hgoal
  · refine ⟨?_, ?_, ?_⟩
    · show Polynomial.C (14 : ℤ_[2]) ≠ 0
      exact Polynomial.C_ne_zero.mpr (by norm_num)
    · show ((1 : ℕ) : ℤ) * U31.bw (Bdev0 (0 + 1 * 2)) + ((0 + 1 * 2 : ℕ) : ℤ) * ((1 : ℕ) : ℤ) = 3
      rw [show U31.bw (Bdev0 (0 + 1 * 2)) = 1 from bw_C14]
      norm_num
    · have hgoal : U31.bR (Polynomial.C (14 : ℤ_[2])) = LaurentPolynomial.C ((1 : ↥U31.K2)) *
          LaurentPolynomial.T (- (0 : ℤ) * gaussVal (Polynomial.C (14 : ℤ_[2]))) := by
        rw [HK13R.bR_const (by norm_num : (14 : ℤ_[2]) ≠ 0), map_one, neg_zero, zero_mul,
          LaurentPolynomial.T_zero, one_mul]
      exact hgoal

end HK19

end LeanUrat.MovesJ
