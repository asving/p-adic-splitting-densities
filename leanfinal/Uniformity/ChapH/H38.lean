/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Data.Nat.Basic

/-!
# Uniformity.ChapH.H38 — the quartic e-first law `CS4-E(h)` and its visibility floor

**Chapter H, NODE H.38** (`blueprint/CHAP-H_general_induction.md` §7). Defines
`lawE q N h = (q − 1) * q^(4N − 5h − 3)`, the quartic e-first genre's per-centre opening locus,
and states its **visibility floor** `2h + 1 ≤ N` (the genre's entry height is `v(a₀) = 2h`, and
`DRAIN` fires at `v(a₀) ≥ N`). Two clauses:

* `lawE_exp_honest` — the floor implies the exponent is honest, `5h + 3 ≤ 4N`, so the `ℕ`-
  subtraction in the definition does not truncate;
* `lawE_floor_fails_at_two_one` — the floor **fails** at `(N, h) = (2, 1)` while
  `lawE q 2 1 = q − 1 ≠ 0` for `q ≥ 2`: the unfloored display's false positive.

The definition is TOTAL by construction (a `ℕ`-valued law must be total, per §7's standing rule);
the floor is a hypothesis of the lemmas, never of the definition. Two of the corpus's confirmed
defects were missing floors, one of them producing a non-integer count — hence the discipline.

DEPENDS: none (pure `ℕ` arithmetic).

SOURCE: `EFF.GENIND.48`: *"**CS4-E(h)** [e-first: `e = 2`, `ψ` linear, `μ = 2`; = `QRT-G2(h;(1²))`]:
slope `h/2`, `h` odd, residual `(y−z)²`: `(q−1)·q^{4N−5h−3}`, VISIBILITY FLOOR `2h ≤ N−1` … at
`(N, h) = (2, 1)` the unfloored display would return `q−1` against a true locus of 0"*
(`GENIND` §S5.3 = `W-12` §S2.5's `QRT-G2(h;(1²))`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Induction

/-- `CS4-E(h)` — the quartic e-first genre's per-centre opening locus, `(q−1)q^{4N−5h−3}`
(`GENIND` §S5.3 = `W-12` §S2.5's `QRT-G2(h;(1²))`).  Total by construction; the visibility floor
`2h ≤ N−1` is a hypothesis of `lawE_floor_*`, not of the definition. -/
def lawE (q N h : ℕ) : ℕ := (q - 1) * q ^ (4 * N - 5 * h - 3)

/-- **NODE H.38(i).** Above the visibility floor `2h + 1 ≤ N`, the exponent of `lawE` is honest:
`5h + 3 ≤ 4N`, so `4 * N - 5 * h - 3` is a genuine (untruncated) `ℕ`-subtraction. -/
theorem lawE_exp_honest {N h : ℕ} (hfl : 2 * h + 1 ≤ N) : 5 * h + 3 ≤ 4 * N := by
  omega

/-- **NODE H.38(ii).** The floor is not vacuous: at `(N, h) = (2, 1)` it fails, yet the unfloored
display `lawE q 2 1` returns `q − 1 ≠ 0` for `q ≥ 2` against a true locus of `0`. -/
theorem lawE_floor_fails_at_two_one {q : ℕ} (hq : 2 ≤ q) :
    ¬ (2 * 1 + 1 ≤ 2) ∧ lawE q 2 1 ≠ 0 := by
  refine ⟨by omega, ?_⟩
  have h : lawE q 2 1 = q - 1 := by simp [lawE]
  omega

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.lawE
#print axioms Uniformity.Density.Induction.lawE_exp_honest
#print axioms Uniformity.Density.Induction.lawE_floor_fails_at_two_one

end AxCheck
