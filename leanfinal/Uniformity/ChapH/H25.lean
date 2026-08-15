/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Uniformity.ChapH.H23
import Uniformity.ChapH.H24

/-!
# Uniformity.ChapH.H25 — the telescoped recursion for `uTwo`

**Chapter H, NODE H.25** (`blueprint/CHAP-H_general_induction.md` §5). The `m = 2` conservative
complement `uTwo` (H.23) satisfies, for `2 ≤ Q` and `N ≥ 3`, the SUBTRACTION-FREE form of the
corpus's `u(N) = Q^{N−1} − Q^{N−2} + Q²·u(N−2)`:

`uTwo Q N + Q ^ (N − 2) = Q ^ (N − 1) + Q ^ 2 * uTwo Q (N − 2)`.

DEPENDS: H.23 (`uTwo`), H.24 (`uTwo_one`, the window-1 boundary consumed at `N = 3`).

SOURCE: `EFF.GENIND.150` (the telescope, with the spec's own re-derivation: *"Re-index `S(N)` at
`j = k−1` on its `k ≥ 2` tail … the index ranges match, since `2k ≤ N−1, k ≥ 2` ⟺ `2j ≤ N−3,
j ≥ 1` ✓. Hence `S(N) = (Q−1)Q·u(N−2) + Q·S(N−2)`, and substituting `S(N−2) = u(N−2) − Q^{N−3}`
gives `u(N) = Q^{N−1} − Q^{N−2} + Q²·u(N−2)` ✓ — the displayed telescoped recurrence, exactly"*).

## The proof, as transcribed

Write `S(A)` for the α-sum of the H.23 recursion at window `A` (the private `aSum` below, whose
body is character-for-character the body of `uTwo`'s defining sum). Two private steps:

* `uTwo_succ_eq : uTwo Q (M+1) = Q ^ M + aSum Q (M+1)` — the head/α split, valid at EVERY `M`
  including `M = 0`, where `uTwo Q 1 = 1 = Q ^ 0` and the α-sum is empty (H.24's window-1
  boundary, reproved here from the defining equation so that the `N = 3` instance needs no case
  split).
* `aSum_rec : aSum Q (M+3) = (Q−1) * Q * uTwo Q (M+1) + Q * aSum Q (M+1)` — the re-index. The
  `k = 1` term is pulled off (`Finset.sum_range_succ'` twice, once to discard the vacuous `k = 0`
  term and once to expose `k = 1`), and the `k ≥ 2` tail is matched termwise against
  `Q * aSum Q (M+1)` under `j = k − 1`; the two admissibility windows agree because
  `1 ≤ j+1 ∧ 2(j+1) ≤ M+2` ⟺ `2j ≤ M`, which is `omega`.

Then, ADDITIVELY (no `ℕ`-subtraction is ever introduced): `Q · aSum Q (M+1) + Q · Q^M
= Q · uTwo Q (M+1)`, so the total is `Q^{M+2} + (Q−1)Q·u + Q·u = Q^{M+2} + Q²·u`. The single use
of `2 ≤ Q` is `(Q−1) + 1 = Q`, discharged by writing `Q = q + 1`.

**⚠ THE `Q = 3` COLUMN IS THE INFORMATIVE ONE.** At `Q = 2` the letter factor `(Q−1) = 1` is
invisible, so the numeric gate below runs both `Q = 2` and `Q = 3` (the chapter's G.23 lesson,
inherited from H.23's own gate).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- The α-sum of the H.23 first-step recursion at window `A`: `Σ_{k ≥ 1, 2k ≤ A−1} (Q−1)·Q^k·
uTwo Q (A − 2k)`, written with the same `Finset.range A` index set and the same guard as the body
of `uTwo`'s defining equation. Private: an internal name for the telescope, not part of H.25's
signature. -/
private def aSum (Q A : ℕ) : ℕ :=
  ∑ k ∈ Finset.range A,
    if 1 ≤ k ∧ 2 * k ≤ A - 1 then (Q - 1) * Q ^ k * uTwo Q (A - 2 * k) else 0

/-- The head/α split of `uTwo`, at every window `M + 1 ≥ 1`. At `M = 0` this is H.24's window-1
boundary `uTwo Q 1 = 1` together with the emptiness of the α-sum there. -/
private lemma uTwo_succ_eq (Q M : ℕ) : uTwo Q (M + 1) = Q ^ M + aSum Q (M + 1) := by
  cases M with
  | zero => simp [aSum, uTwo_one]
  | succ M =>
    rw [uTwo, aSum]
    simp only [Nat.add_sub_cancel, dite_eq_ite]

/-- The re-index: peeling the `k = 1` term off the α-sum at window `M + 3` leaves exactly `Q`
times the α-sum at window `M + 1`. This is `EFF.GENIND.150`'s `S(N) = (Q−1)Q·u(N−2) + Q·S(N−2)`. -/
private lemma aSum_rec (Q M : ℕ) :
    aSum Q (M + 3) = (Q - 1) * Q * uTwo Q (M + 1) + Q * aSum Q (M + 1) := by
  classical
  -- `T j` is the `k = j + 1` term of the window-`M+3` α-sum, with its guard already simplified.
  set T : ℕ → ℕ :=
    fun j => if 2 * j ≤ M then (Q - 1) * Q ^ (j + 1) * uTwo Q (M + 1 - 2 * j) else 0 with hTdef
  have hTzero : T 0 = (Q - 1) * Q * uTwo Q (M + 1) := by
    simp [hTdef]
  have hTtop : T (M + 1) = 0 := by
    have : ¬ (2 * (M + 1) ≤ M) := by omega
    simp [hTdef, this]
  -- Step 1: the window-`M+3` α-sum, re-indexed by `j = k − 1`.
  have h1 : aSum Q (M + 3) = ∑ j ∈ Finset.range (M + 2), T j := by
    rw [aSum, Finset.sum_range_succ' _ (M + 2)]
    have hzero : (if 1 ≤ 0 ∧ 2 * 0 ≤ M + 3 - 1 then (Q - 1) * Q ^ 0 * uTwo Q (M + 3 - 2 * 0) else 0) = 0 := by
      simp
    rw [hzero, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : 2 * j ≤ M
    · have hc : 1 ≤ j + 1 ∧ 2 * (j + 1) ≤ M + 3 - 1 := by omega
      have harg : M + 3 - 2 * (j + 1) = M + 1 - 2 * j := by omega
      rw [if_pos hc, harg]
      simp [hTdef, hj]
    · have hc : ¬ (1 ≤ j + 1 ∧ 2 * (j + 1) ≤ M + 3 - 1) := by omega
      rw [if_neg hc]
      simp [hTdef, hj]
  -- Step 2: the tail of that sum is `Q` times the window-`M+1` α-sum.
  have h2 : Q * aSum Q (M + 1) = ∑ i ∈ Finset.range (M + 1), T (i + 1) := by
    rw [aSum, Finset.mul_sum, Finset.sum_range_succ' _ M, Finset.sum_range_succ _ M, hTtop, add_zero]
    have hzero : Q * (if 1 ≤ 0 ∧ 2 * 0 ≤ M + 1 - 1 then (Q - 1) * Q ^ 0 * uTwo Q (M + 1 - 2 * 0) else 0) = 0 := by
      simp
    rw [hzero, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : 2 * (i + 1) ≤ M
    · have hc : 1 ≤ i + 1 ∧ 2 * (i + 1) ≤ M + 1 - 1 := by omega
      rw [if_pos hc]
      simp only [hTdef, if_pos hi]
      ring
    · have hc : ¬ (1 ≤ i + 1 ∧ 2 * (i + 1) ≤ M + 1 - 1) := by omega
      rw [if_neg hc]
      simp [hTdef, hi]
  rw [h1, Finset.sum_range_succ' _ (M + 1), hTzero, h2, add_comm]

/-- **NODE H.25, the telescoped recursion.** For `2 ≤ Q` and `N ≥ 3`,
`uTwo Q N + Q^(N−2) = Q^(N−1) + Q^2 · uTwo Q (N−2)` — the subtraction-free form of
`u(N) = Q^{N−1} − Q^{N−2} + Q²·u(N−2)` (`EFF.GENIND.150`). -/
theorem uTwo_rec (Q : ℕ) (hQ : 2 ≤ Q) {N : ℕ} (hN : 3 ≤ N) :
    uTwo Q N + Q ^ (N - 2) = Q ^ (N - 1) + Q ^ 2 * uTwo Q (N - 2) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 3 := ⟨N - 3, by omega⟩
  have hsub1 : M + 3 - 2 = M + 1 := by omega
  have hsub2 : M + 3 - 1 = M + 2 := by omega
  have hhead : uTwo Q (M + 3) = Q ^ (M + 2) + aSum Q (M + 3) := uTwo_succ_eq Q (M + 2)
  have hu : uTwo Q (M + 1) = Q ^ M + aSum Q (M + 1) := uTwo_succ_eq Q M
  obtain ⟨q, rfl⟩ : ∃ q, Q = q + 1 := ⟨Q - 1, by omega⟩
  rw [hsub1, hsub2, hhead, aSum_rec, hu]
  simp only [Nat.add_sub_cancel]
  ring

end Uniformity.Density.Induction

/-! ## Numeric gate — the recursion at both `Q = 2` and `Q = 3`.
`#guard` fails elaboration when the proposition evaluates to `false`, so this block is a
build-time regression on the recursion's two sides, evaluated from H.23's definition (the values
are H.29's certified column). Both characteristics are mandatory: at `Q = 2` the `(Q − 1)`
coefficient is `1` and cannot expose a missing letter factor. -/

section NumericGate

open Uniformity.Density.Induction

/-! `N = 3, …, 6` at `Q = 2`: `u(N) + 2^(N−2) = 2^(N−1) + 4·u(N−2)`. -/
#guard [3, 4, 5, 6].all fun N => uTwo 2 N + 2 ^ (N - 2) == 2 ^ (N - 1) + 2 ^ 2 * uTwo 2 (N - 2)

/-! `N = 3, …, 6` at `Q = 3` — the column where `(Q − 1) = 2` is genuinely tested. -/
#guard [3, 4, 5, 6].all fun N => uTwo 3 N + 3 ^ (N - 2) == 3 ^ (N - 1) + 3 ^ 2 * uTwo 3 (N - 2)

/-! The prime-power arguments `Q = q^d` are the intended reading; `Q = 4, 9` run too. -/
#guard [4, 9].all fun Q => [3, 4, 5, 6].all fun N =>
  uTwo Q N + Q ^ (N - 2) == Q ^ (N - 1) + Q ^ 2 * uTwo Q (N - 2)

end NumericGate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.uTwo_rec

end AxCheck
