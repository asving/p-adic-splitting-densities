/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.Drainage

/-!
# Uniformity.ChapH.H49 — the `m = 6` mixed grammar: entry heights by Gauss additivity

**Chapter H, NODE H.49** (`blueprint/CHAP-H_general_induction.md` §7, source `EFF.GENIND.32`,
the complete `[r5]`-re-derived `m = 6` mixed grammar). Entry heights are Gauss-additive,
`v(a₀) = Σ_sides (side length) × (side slope)`, and the abscissa budget is `2 + 4 = 6 = m`.
For integer slopes `k, h ≥ 1` the three families and their heights are:

* **child + E-block** (`(e,γ,μ) = (2,1,2)`, block slope `h/2`): height `2k + 2h`
  (`2` at slope `k` plus `4` at slope `h/2`). `mixed_six_childE_lt_six` says the **unique** cell
  below `6` is `(k,h) = (1,1)` (height `4`), and `mixed_six_stage_steeper` says the
  stage-steeper arrangement `h ≥ 2k + 1` already costs `≥ 8`.
* **child + f-first block, SAME side** (`(1,2,2)`, forced `k = h`): height `6k ≥ 6`
  (`mixed_six_sameSide`).
* **child + f-first block, DISTINCT sides** (`h ≠ k`): height `2k + 4h ≥ 8`
  (`mixed_six_distinctSide`; the minimum `8` is at `(k,h) = (2,1)`, while `(1,2)` gives `10`).

Consequently every non-`M6` mixed genre enters at `v(a₀) ≥ 6`, i.e. `N ≥ 7`, and the unique cell
of height `4` is genre `M6`'s (`EFF.GENIND.33`: hull `(0,4)–(2,2)–(6,0)`, so `k = h = 1`),
first visible at `N = 5`.

⚠ WHAT IS NOT CLAIMED. "No other arrangement fits the `2 + 4 = 6` abscissa budget" is a
**grammar-completeness** claim over frame shapes — geometric, chapter C, deliberately *not* a
node here. This file proves only the four height inequalities, which is the checkable content
the `n = 6` threshold rests on.

DEPENDS: none beyond Lean core + `omega`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **H.49 (i), uniqueness.** The child + E-block height `2k + 2h` is `< 6` only at
`(k,h) = (1,1)` (where it is `4`). -/
theorem mixed_six_childE_lt_six {k h : ℕ} (hk : 1 ≤ k) (hh : 1 ≤ h)
    (hlt : 2 * k + 2 * h < 6) : k = 1 ∧ h = 1 := by
  omega

/-- **H.49 (i), the steeper arrangement.** If the block stage is steeper, `h ≥ 2k + 1`, the
child + E-block height is at least `8`. -/
theorem mixed_six_stage_steeper {k h : ℕ} (hk : 1 ≤ k) (hst : 2 * k + 1 ≤ h) :
    8 ≤ 2 * k + 2 * h := by
  omega

/-- **H.49 (ii).** The same-side f-first height `6k` is at least `6` (so `N ≥ 7`). -/
theorem mixed_six_sameSide {k : ℕ} (hk : 1 ≤ k) : 6 ≤ 6 * k := by
  omega

/-- **H.49 (iii).** The distinct-side f-first height `2k + 4h` is at least `8`: if `h ≥ 2` then
`2k + 4h ≥ 2 + 8 = 10`, and if `h = 1` then `h ≠ k` forces `k ≥ 2`, giving `2k + 4 ≥ 8`. -/
theorem mixed_six_distinctSide {k h : ℕ} (hk : 1 ≤ k) (hh : 1 ≤ h) (hne : h ≠ k) :
    8 ≤ 2 * k + 4 * h := by
  omega

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.mixed_six_childE_lt_six
#print axioms Uniformity.Density.Induction.mixed_six_stage_steeper
#print axioms Uniformity.Density.Induction.mixed_six_sameSide
#print axioms Uniformity.Density.Induction.mixed_six_distinctSide

end AxCheck
