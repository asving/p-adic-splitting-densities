/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Uniformity.ChapH.H13

/-!
# Uniformity.ChapH.H14 — the three faces of `clusterC`

**Chapter H, NODE H.14** (`blueprint/CHAP-H_general_induction.md` §4). Three clauses on
`clusterC m = m.choose 2` (H.13), the α-bracket's exponent coefficient offset `c(m) = m(m−1)/2`.

* `two_mul_clusterC` — the doubled closed form `2 * clusterC m = m * (m − 1)`, exact in `ℕ` with
  no floor (this is the payoff of H.13's `Nat.choose` definition: the identity is a mathlib
  rewrite, not a parity argument);
* `clusterC_eq_sum` — the triangular-number face `clusterC m = ∑_{j < m} j`, which is the form
  the ghost-fibre count `Σ_{j<m} j·k` of H.15/H.17 consumes;
* `clusterC_succ_values` — the four exponent-coefficient instances
  `c(m) + 1 = 2, 4, 7, 11` at `m = 2, 3, 4, 5`.

DEPENDS: H.13.

**Why clause (iii) is a cross-chapter tie** (blueprint): `c(2) + 1 = 2` is the coefficient chapter
G's `hex3R`/`hex3U` layer sees as W-11's `(q−1)q^{2l−1}` telescoping coefficient, and
`c(3) + 1 = 4` is HMENU3's `(q−1)q^{4μ−1}` — so the instances are checkable against two landed
chapter-G objects, not just against the source display.

SOURCE: `EFF.GENIND.09` (*"exponent coefficient `c(m)+1 = m(m−1)/2 + 1` (= 2, 4, 7, 11 at
`m = 2, 3, 4, 5`)"*); `EFF.GENIND.23` (the instance display, with its own ARITHMETIC AUDIT
*"`1+1 = 2` ✓, `3+1 = 4` ✓, `6+1 = 7` ✓, `10+1 = 11` ✓"*).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **NODE H.14(ii).** `clusterC` is the `m`-th triangular number: `c(m) = ∑_{j < m} j`. Both
sides are literally `m * (m − 1) / 2` in `ℕ`. -/
theorem clusterC_eq_sum (m : ℕ) : clusterC m = ∑ j ∈ Finset.range m, j := by
  rw [clusterC, Nat.choose_two_right, Finset.sum_range_id]

/-- **NODE H.14(i).** The doubled closed form, exact in `ℕ`: `2 * c(m) = m(m − 1)`. No
`ℕ`-division appears, so the identity cannot hide a floor. -/
theorem two_mul_clusterC (m : ℕ) : 2 * clusterC m = m * (m - 1) := by
  rw [clusterC_eq_sum, Nat.mul_comm, Finset.sum_range_id_mul_two]

/-- **NODE H.14(iii).** The four exponent-coefficient instances `c(m) + 1` at `m = 2, 3, 4, 5`:
`2, 4, 7, 11` — the values §S11 P-7 scored. -/
theorem clusterC_succ_values :
    clusterC 2 + 1 = 2 ∧ clusterC 3 + 1 = 4 ∧ clusterC 4 + 1 = 7 ∧ clusterC 5 + 1 = 11 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.clusterC_eq_sum
#print axioms Uniformity.Density.Induction.two_mul_clusterC
#print axioms Uniformity.Density.Induction.clusterC_succ_values

end AxCheck
