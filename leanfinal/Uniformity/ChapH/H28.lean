/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Data.Real.Basic
import Uniformity.ChapH.H27

/-!
# Uniformity.ChapH.H28 — THE `(A2-RATE)` GROUND INSTANCE

**Chapter H, NODE H.28** (`blueprint/CHAP-H_general_induction.md` §5). The `m = 2` cluster
system's normalized conservative complement obeys the `(A2-RATE)` species, in `ℝ`: for `2 ≤ Q`
and `N ≥ 1`,

`uTwo Q N / Q^(2(N−1)) ≤ N / Q^(N−1)`,

which is the species `u_{μ,d}(M) / Q^(μ(M−1)) ≤ K · M^B · Q^(−(M−c))` at
`(μ, K, B, c) = (2, 1, 1, 1)`.

DEPENDS: H.27 (`uTwo_le`, the `ℕ`-level rate) · mathlib `div_le_div_iff₀`, `pow_pos`,
`mul_le_mul_of_nonneg_right`.

SOURCE: `EFF.GENIND.150` (*"`u(N)/Q^{2(N−1)} ≤ N·Q^{−(N−1)}`"*); `EFF.GENIND.151` (the
`(A2-RATE)` species display with its instance list: *"`(μ, d) = (2, d)`: `K = 1, B = 1, c = 1`
(the closed forms above, machine legs A–C)"*, audited there as *"`K·M^B·Q^{−(M−c)}` with
`K = B = c = 1` is `M·Q^{−(M−1)}` ✓"*).

## The proof, as transcribed

1. `0 < (Q : ℝ)` from `2 ≤ Q`, hence both denominators are positive by `pow_pos`.
2. `div_le_div_iff₀` clears them: the goal becomes
   `uTwo Q N * Q^(N−1) ≤ N * Q^(2(N−1))`.
3. `Q^(2(N−1)) = Q^(N−1) · Q^(N−1)` (`two_mul`, `pow_add`), and reassociating puts the goal in
   the form `(uTwo Q N) * Q^(N−1) ≤ (N * Q^(N−1)) * Q^(N−1)`.
4. Cancel the common non-negative right factor and cast H.27 down: `uTwo Q N ≤ N · Q^(N−1)`.

Note the exponent `2 * (N − 1)` is `ℕ`-subtraction *inside* the multiplication, exactly as
signed; at `N = 1` both sides read `uTwo Q 1 / 1 = 1 ≤ 1 = 1 / 1`, so the statement is not vacuous
at the boundary.

**⚠ WHAT THIS NODE IS AND IS NOT** (blueprint, carried forward). It is the **ground instance** of
`(A2-RATE)`, unconditional. It is **not** `(A2-RATE)` itself, which is a species *pinned onto
`P(k)`'s fourth member* and whose general form is a hypothesis — `EFF.GENIND.151`'s TEETH:
*"nothing for the general species, which is why it is a hypothesis pin and not a theorem"*,
disposition `signed vacuity disclosure` at general `(μ, d)`. Chapter H's `RateSpecies` predicate
(H.65) is the general form; **this node discharges it at `μ = 2` and nowhere else in the chapter**.

**⚠ DO NOT IDENTIFY WITH H.96's `n = 2` RATE.** H.96's rate is a *full-space* statement (the
level-`N` undecided fraction of `Coeff O 2 N`, with the sharper constants `(1, 0, 0)`); this one
bounds the `(2, d)` *cluster* system's normalized complement. They are different objects and are
not to be wired together (§16 item 6).

**ARITHMETIC AUDIT (recomputed fresh at `Q = 2` and `Q = 3`).** `Q = 2, N = 5`: `u = 32`,
`32/2^8 = 0.125`; bound `5/2^4 = 0.3125` ✓. `Q = 3, N = 5`: `u = 189`, `189/3^8 = 189/6561 ≈
0.0288`; bound `5/3^4 = 5/81 ≈ 0.0617` ✓. `Q = 2, N = 2`: `2/2^2 = 0.5`; bound `2/2 = 1` ✓ (the
tightest non-boundary cell). `Q = 3, N = 2`: `3/9 = 1/3`; bound `2/3` ✓. `N = 1` is the tight
boundary, `1 ≤ 1`, at every `Q`. The bound is never tight beyond `N = 1` but stays within a factor
`< 4` at every cell checked — consistent with `EFF.GENIND.153`'s *"the `m = 2` closed forms realize
`(K, B, c) = (1, 1, 1)` — the ansatz is sharp at the ground instance."*

**TEETH.** `EFF.GENIND.150`'s leg C → **Lean theorem**; `EFF.GENIND.151`'s `signed vacuity
disclosure` at general `(μ, d)` is **carried unchanged** (H.65 is a predicate, not a theorem, and
no node in this chapter supplies it beyond `μ = 2`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **NODE H.28, THE `(A2-RATE)` GROUND INSTANCE.** For `2 ≤ Q` and `1 ≤ N`, in `ℝ`,
`uTwo Q N / Q^(2(N−1)) ≤ N / Q^(N−1)` — the species at `(μ, K, B, c) = (2, 1, 1, 1)`. This is the
only unconditional instance of the `(A2-RATE)` species in chapter H; at general degree data the
species remains a hypothesis pin (H.65). -/
theorem uTwo_ratio_le (Q : ℕ) (hQ : 2 ≤ Q) {N : ℕ} (hN : 1 ≤ N) :
    (uTwo Q N : ℝ) / (Q : ℝ) ^ (2 * (N - 1)) ≤ (N : ℝ) / (Q : ℝ) ^ (N - 1) := by
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by
    have hQ0' : (0 : ℕ) < Q := by omega
    exact_mod_cast hQ0'
  have hnat : (uTwo Q N : ℝ) ≤ (N : ℝ) * (Q : ℝ) ^ (N - 1) := by
    exact_mod_cast uTwo_le Q hQ hN
  rw [div_le_div_iff₀ (pow_pos hQ0 _) (pow_pos hQ0 _),
    show 2 * (N - 1) = (N - 1) + (N - 1) from two_mul _, pow_add, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hnat (pow_pos hQ0 _).le

end Uniformity.Density.Induction

/-! ## Numeric gate — the cross-multiplied form, at four values of `Q`, out to `N = 9`.
The signed statement lives in `ℝ`, where `#guard` cannot evaluate; the `ℕ` inequality below is
its exact cross-multiplication by the two positive denominators (step 2 of the proof), so it is a
faithful build-time regression. Both `q = 2` and `q = 3` are mandatory (H.29's rule). -/

section NumericGate

open Uniformity.Density.Induction

#guard [2, 3, 4, 9].all fun Q => [1, 2, 3, 4, 5, 6, 7, 8, 9].all fun N =>
  uTwo Q N * Q ^ (N - 1) ≤ N * Q ^ (2 * (N - 1))

/-! The blueprint's four audited cells, cross-multiplied: `(Q, N) = (2,5), (3,5), (2,2), (3,2)`,
plus the tight boundary `N = 1`. -/
#guard uTwo 2 5 * 2 ^ 4 == 512 && 5 * 2 ^ 8 == 1280

#guard uTwo 3 5 * 3 ^ 4 == 15309 && 5 * 3 ^ 8 == 32805

#guard uTwo 2 2 * 2 ^ 1 == 4 && 2 * 2 ^ 2 == 8

#guard uTwo 3 2 * 3 ^ 1 == 9 && 2 * 3 ^ 2 == 18

#guard [2, 3, 4, 9].all fun Q => uTwo Q 1 * Q ^ 0 == 1 * Q ^ 0

end NumericGate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.uTwo_ratio_le

end AxCheck
