/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapH.H86 — `carry_height_gt`, the refine carry's height bound

**Chapter H, NODE H.86** (`blueprint/CHAP-H_general_induction.md` §12; source `EFF.GENH4.23`,
§S5's proof of `LEMMA GENH4-4`). *The refine carry's height bound.* For `h ≥ 1`, `dμ ≥ 2h+1`
and `2·v(α₁) ≥ h+1`, both branches of the carry's height exceed `dμ`:

* first branch: `2·(dμ − h) > dμ ⟺ dμ > 2h`, which is `hd`;
* second branch: `2·v(α₁) + (dμ − h) ≥ (h+1) + (dμ − h) = dμ + 1 > dμ`, using `h ≤ dμ` from `hd`.

Hence `dμ < min (2·(dμ − h)) (2·v(α₁) + (dμ − h))` — the carry lands at even heights strictly
above the odd-parity pin it could have threatened.

DEPENDS: none.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **NODE H.86.** The refine carry's height bound: under `1 ≤ h`, `2h + 1 ≤ dμ` and
`h + 1 ≤ 2·va`, both branches of the carry's height strictly exceed `dμ`.  (All subtraction is
ℕ-truncated; `hd` supplies `h ≤ dμ`, so `dμ - h` is the honest difference.) -/
theorem carry_height_gt {h dμ va : ℕ} (hh : 1 ≤ h) (hd : 2 * h + 1 ≤ dμ) (hva : h + 1 ≤ 2 * va) :
    dμ < min (2 * (dμ - h)) (2 * va + (dμ - h)) := by
  refine Nat.lt_min.mpr ⟨?_, ?_⟩
  · omega
  · omega

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.carry_height_gt

end AxCheck
