/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H38

/-!
# Uniformity.ChapH.H42 — the quintic vertex-at-1 law `CS5-V1E2(h)` and its headroom

**Chapter H, NODE H.42** (`blueprint/CHAP-H_general_induction.md` §7). Defines
`lawV1E2 q N h = lawE q N h * (q^{N − (5h+1)/2} − 1)`, the quintic vertex-at-1 genre's per-centre
opening locus: H.38's quartic `CS4-E` law times the split root's **headroom fibre**. The exponent
identity of the first factor is H.39's (the four-coordinate exponent `4N − 5h − 3`); what is new
here is the second factor, and the two clauses landed are about *it*:

* `headroom_exp_odd` — at `h = 2t + 1` the headroom threshold is `(5h+1)/2 = 5t + 3`;
* `lawV1E2_eq_zero_iff` — for `2 ≤ q` the whole locus vanishes **exactly** when either the
  headroom is exhausted (`N ≤ 5t + 3`) or the underlying `CS4-E` law already vanishes. Both
  directions.

DEPENDS: H.38 (`lawE`), H.39 (the exponent identity, cited not consumed); mathlib
`Nat.mul_eq_zero`, `Nat.one_lt_pow`.

**SOURCE.** `EFF.GENIND.50`, verbatim: *"`(q−1)·q^{4N−5h−3}·(q^{N−(5h+1)/2} − 1)` — the CS4-E law
times the `b₀` headroom factor (the split root's fiber)"*, with the note that `v(b₀)` must be
*"NOT window-zero (else DRAIN fires first)"*.

**ARITHMETIC AUDIT** (recomputed in the blueprint, re-checked by the spec's `#eval` gate):
`lawV1E2 2 5 1 = 4096 · 3 = 12288` (= `EFF.GENIND.99`'s reported `V1E2(1)`); `lawV1E2 3 3 1 = 0`
(the corpus's *"NO CS key at all (V1E2 headroom = 0)"*); `lawV1E2 3 5 1 = 1062882 · 8 = 8503056`,
the `q = 3` cell where **both** factors are non-degenerate.

**PROOF.** (1) `headroom_exp_odd` by `omega` (`(10t+6)/2 = 5t+3`). (2) `lawV1E2_eq_zero_iff`:
`Nat.mul_eq_zero` splits the product; the headroom factor `q^{N−(5t+3)} − 1` is `0` in `ℕ` iff
`q^{N−(5t+3)} ≤ 1`, which for `2 ≤ q` happens iff the exponent `N − (5t+3)` is `0`
(`Nat.one_lt_pow`), i.e. iff `N ≤ 5t + 3` (`omega` for the `ℕ`-subtraction).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- `CS5-V1E2(h)` — the quintic vertex-at-1 genre: `CS4-E`'s law times the split root's headroom
fibre `(q^{N−(5h+1)/2} − 1)` (`GENIND` §S5.3). -/
def lawV1E2 (q N h : ℕ) : ℕ := lawE q N h * (q ^ (N - (5 * h + 1) / 2) - 1)

/-- The headroom threshold at odd `h = 2t + 1`: `(5h+1)/2 = 5t + 3`. -/
theorem headroom_exp_odd (t : ℕ) : (5 * (2 * t + 1) + 1) / 2 = 5 * t + 3 := by
  omega

/-- **H.42 — the headroom vanishing law.** For `2 ≤ q` and odd `h = 2t + 1`, the vertex-at-1 locus
is zero exactly when the headroom is exhausted (`N ≤ 5t + 3`) or the underlying `CS4-E` law is
already zero. -/
theorem lawV1E2_eq_zero_iff {q N t : ℕ} (hq : 2 ≤ q) :
    lawV1E2 q N (2 * t + 1) = 0 ↔ (N ≤ 5 * t + 3 ∨ lawE q N (2 * t + 1) = 0) := by
  have hexp : (5 * (2 * t + 1) + 1) / 2 = 5 * t + 3 := headroom_exp_odd t
  unfold lawV1E2
  rw [hexp, Nat.mul_eq_zero]
  constructor
  · rintro (hE | hH)
    · exact Or.inr hE
    · refine Or.inl ?_
      by_contra hN
      have hk : N - (5 * t + 3) ≠ 0 := by omega
      have hpow : 1 < q ^ (N - (5 * t + 3)) := Nat.one_lt_pow hk hq
      omega
  · rintro (hN | hE)
    · refine Or.inr ?_
      have hk : N - (5 * t + 3) = 0 := by omega
      rw [hk, Nat.pow_zero]
    · exact Or.inl hE

section AxCheck
#print axioms Uniformity.Density.Induction.lawV1E2
#print axioms Uniformity.Density.Induction.headroom_exp_odd
#print axioms Uniformity.Density.Induction.lawV1E2_eq_zero_iff
end AxCheck

end Uniformity.Density.Induction
