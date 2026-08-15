/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H26

/-!
# Uniformity.ChapH.H27 — THE RATE of the `m = 2` conservative complement, in `ℕ`

**Chapter H, NODE H.27** (`blueprint/CHAP-H_general_induction.md` §5). The `m = 2` conservative
complement `uTwo` (H.23), computed in closed form at H.26, obeys the linear-coefficient bound

`uTwo Q N ≤ N * Q^(N−1)` for `2 ≤ Q` and `N ≥ 1`.

This is the `ℕ`-level half of the `(A2-RATE)` ground instance; H.28 divides it by `Q^(2(N−1))`
and reads it in `ℝ` as the species at `(μ, K, B, c) = (2, 1, 1, 1)`.

DEPENDS: H.24 (`uTwo_one`, the window-1 boundary), H.26 (`uTwo_closed`, the closed form).

SOURCE: `EFF.GENIND.150`, leg C, verbatim: *"Rate (leg C): `u(N) ≤ N·Q^{N−1}` … at `N = 2..14`,
`Q ∈ {2,3,4,5,8,9}` — coefficient POLYNOMIAL (degree 1) in the window, deficit LINEAR in the
window"*, with the spec's own audit *"at `N = 2ℓ`, `u = ℓQ^{2ℓ−1} − (ℓ−1)Q^{2ℓ−2} ≤ ℓQ^{2ℓ−1} ≤
2ℓ·Q^{2ℓ−1} = N·Q^{N−1}` ✓"*.

## The proof, as transcribed

1. `N = 1` is H.24's boundary: `uTwo Q 1 = 1 ≤ 1 * Q^0 = 1`.
2. `N ≥ 2`: substitute H.26's closed form
   `uTwo Q N = Q^(N−1) + ⌊(N−1)/2⌋ · ((Q−1) · Q^(N−2))`.
3. The letter factor is absorbed: `(Q−1)·Q^(N−2) ≤ Q·Q^(N−2) = Q^(N−1)` (this is the ONE place
   the bound is lossy, and it is lossy by the factor `Q/(Q−1)`).
4. Hence `uTwo Q N ≤ (1 + ⌊(N−1)/2⌋) · Q^(N−1)`, and `1 + ⌊(N−1)/2⌋ ≤ N` for `N ≥ 1` (`omega`,
   which handles the division by the literal `2`).

No `ℕ`-subtraction is ever introduced beyond the exponents `N−1`, `N−2` already present in H.26's
statement, and every step is a `Nat.mul_le_mul`/`Nat.add_le_add` monotonicity step.

**⚠ HYPOTHESIS AT ITS TRUE MINIMUM** (blueprint, carried forward). The corpus's leg C is checked
at `Q ∈ {2,3,4,5,8,9}` and `N ≤ 14`; this node is stated at **every** `Q ≥ 2` and **every**
`N ≥ 1`, with no `d = 1` and no characteristic hypothesis — which is what makes
`GENIND-BOX-3`'s `Q`-uniformity claim a theorem for this leg (honesty item H-3).

**ARITHMETIC AUDIT (recomputed fresh, against H.29's certified column).** `Q = 2`: `N=1`,
`1 ≤ 1·1 = 1` (tight); `N=2`, `2 ≤ 2·2 = 4`; `N=3`, `6 ≤ 3·4 = 12`; `N=4`, `12 ≤ 4·8 = 32`;
`N=5`, `32 ≤ 5·16 = 80`; `N=6`, `64 ≤ 6·32 = 192`. `Q = 3`: `N=1`, `1 ≤ 1`; `N=2`, `3 ≤ 2·3 = 6`;
`N=3`, `15 ≤ 3·9 = 27`; `N=4`, `45 ≤ 4·27 = 108`; `N=5`, `189 ≤ 5·81 = 405`; `N=6`,
`567 ≤ 6·243 = 1458`. Twelve cells, both mandatory columns; the `q = 3` column is where a lost
`(Q−1)` factor would show, since at `Q = 2` it is invisible (the chapter's G.23 lesson, H.29).

**TEETH.** `EFF.GENIND.150`'s machine leg C → **Lean theorem** (this file): the node generalizes
the corpus's 78 checked cells to all `(Q, N)` with `Q ≥ 2`, `N ≥ 1`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **NODE H.27, THE RATE in `ℕ`.** For `2 ≤ Q` and `1 ≤ N`, `uTwo Q N ≤ N · Q^(N−1)` —
`EFF.GENIND.150`'s leg C, proved at every window and every `Q ≥ 2` rather than checked on the
78-cell grid `N = 2..14`, `Q ∈ {2,3,4,5,8,9}`. -/
theorem uTwo_le (Q : ℕ) (hQ : 2 ≤ Q) {N : ℕ} (hN : 1 ≤ N) : uTwo Q N ≤ N * Q ^ (N - 1) := by
  rcases Nat.lt_or_ge N 2 with hlt | hge
  · -- `N = 1`: H.24's window-1 boundary, and the bound is tight (`1 ≤ 1`).
    obtain rfl : N = 1 := by omega
    simp [uTwo_one]
  · -- `N ≥ 2`: H.26's closed form, with the letter factor absorbed into one more `Q`.
    have hpow : Q * Q ^ (N - 2) = Q ^ (N - 1) := by
      rw [show N - 1 = (N - 2) + 1 from by omega, pow_succ]
      ring
    have hstep : (Q - 1) * Q ^ (N - 2) ≤ Q ^ (N - 1) := by
      calc (Q - 1) * Q ^ (N - 2) ≤ Q * Q ^ (N - 2) :=
            Nat.mul_le_mul_right _ (by omega)
        _ = Q ^ (N - 1) := hpow
    calc uTwo Q N = Q ^ (N - 1) + ((N - 1) / 2) * ((Q - 1) * Q ^ (N - 2)) :=
          uTwo_closed Q hQ hge
      _ ≤ Q ^ (N - 1) + ((N - 1) / 2) * Q ^ (N - 1) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left _ hstep) _
      _ = (1 + (N - 1) / 2) * Q ^ (N - 1) := by ring
      _ ≤ N * Q ^ (N - 1) := Nat.mul_le_mul_right _ (by omega)

end Uniformity.Density.Induction

/-! ## Numeric gate — the rate at four values of `Q`, out to `N = 9`.
`#guard` fails elaboration when the proposition evaluates to `false`, so this block is a
build-time regression against H.23's recursion. Both `q = 2` and `q = 3` are mandatory (H.29's
rule: at `Q = 2` the letter factor `(Q − 1) = 1` is invisible); `Q = 4, 9` are the intended
`Q = q^d` reading. -/

section NumericGate

open Uniformity.Density.Induction

#guard [2, 3, 4, 9].all fun Q => [1, 2, 3, 4, 5, 6, 7, 8, 9].all fun N =>
  uTwo Q N ≤ N * Q ^ (N - 1)

/-! The blueprint's twelve audited cells, spelled out: the two mandatory columns at `N = 1, …, 6`. -/
#guard [uTwo 2 1, uTwo 2 2, uTwo 2 3, uTwo 2 4, uTwo 2 5, uTwo 2 6] ==
  [1, 2, 6, 12, 32, 64]

#guard [1 * 2 ^ 0, 2 * 2 ^ 1, 3 * 2 ^ 2, 4 * 2 ^ 3, 5 * 2 ^ 4, 6 * 2 ^ 5] ==
  [1, 4, 12, 32, 80, 192]

#guard [uTwo 3 1, uTwo 3 2, uTwo 3 3, uTwo 3 4, uTwo 3 5, uTwo 3 6] ==
  [1, 3, 15, 45, 189, 567]

#guard [1 * 3 ^ 0, 2 * 3 ^ 1, 3 * 3 ^ 2, 4 * 3 ^ 3, 5 * 3 ^ 4, 6 * 3 ^ 5] ==
  [1, 6, 27, 108, 405, 1458]

end NumericGate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.uTwo_le

end AxCheck
