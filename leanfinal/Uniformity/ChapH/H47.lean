/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.Drainage

/-!
# Uniformity.ChapH.H47 — `GENH4.B`'s genre-E aggregate and the `h = 1` coincidence

**Chapter H, NODE H.47** (`blueprint/CHAP-H_general_induction.md` §7, source `EFF.GENH4.10`,
`THEOREM GENH4.B`). Two clauses, both pure exponent arithmetic over `ℕ`:

* `genh4B_aggregate_exp` — the aggregate over the genre-E ladder: for `2h + 1 ≤ N`,
  `(N + h − 1) + (N − 1 − 2h) = 2N − h − 2`, i.e. the ladder's per-rung exponent `N + h − 1`
  summed against the rung count `N − 1 − 2h` produces the aggregate exponent `2N − h − 2` of
  `(q−1)^{r+1}·q^{2N−h−2}`.
* `und_exp_coincide_iff_h_one` — **the coincidence is the theorem**: at odd `h = 2t + 1` the
  scout-note exponent `N + (h−1)/2` and the proved exponent `N + h − 1` agree *iff* `t = 0`
  (`h = 1`). The corpus corrected the *value* (`(2,7,3)`: `512`, not `256`); this clause records
  the *mechanism* — the two laws agree exactly on the one-parameter slice every check ran on,
  which is why the slip survived.

DEPENDS: none (Lean core + `omega`).

⚠ `ℕ`-subtraction is intended throughout: the hypotheses (`2h + 1 ≤ N`, `1 ≤ N`) keep every
truncating subtraction in range, and `omega` reasons about `ℕ`-subtraction and division by the
literal `2` natively.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **H.47 (i).** The genre-E aggregate exponent: on the ladder `2h + 1 ≤ N`, the per-rung
exponent `N + h − 1` and the rung count `N − 1 − 2h` add to the aggregate exponent `2N − h − 2`. -/
theorem genh4B_aggregate_exp {N h : ℕ} (hfl : 2 * h + 1 ≤ N) :
    (N + h - 1) + (N - 1 - 2 * h) = 2 * N - h - 2 := by
  omega

/-- **H.47 (ii).** The `h = 1` coincidence, as an iff: at `h = 2t + 1` the scout note's exponent
`N + (h−1)/2 = N + t` equals the proved exponent `N + h − 1 = N + 2t` exactly when `t = 0`. -/
theorem und_exp_coincide_iff_h_one {N t : ℕ} (hN : 1 ≤ N) :
    N + ((2 * t + 1) - 1) / 2 = N + (2 * t + 1) - 1 ↔ t = 0 := by
  omega

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.genh4B_aggregate_exp
#print axioms Uniformity.Density.Induction.und_exp_coincide_iff_h_one

end AxCheck
