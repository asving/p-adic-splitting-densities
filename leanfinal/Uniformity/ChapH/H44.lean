/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.Drainage

/-!
# Uniformity.ChapH.H44 — `pinCensus`, the comp-weighted pin census

**Chapter H, NODE H.44** (`blueprint/CHAP-H_general_induction.md`, source `EFF.GENH4.07`
`[r2]`, `EFF.GENH4.25`, `EFF.GENHN.79`). At the quartic genres a RAM or 2SIDED pin at slot
height `m` is censused `q ^ (comp m) − 1`, where `comp m` is the pinned slot's
`F_q`-dimension:

* genre E: `comp m = 1` identically, so the factor is `q − 1 = Q − 1` (`Q = q`);
* genre F below the boundary band (`m ≤ N − 1`): `comp m = 2`, factor `q² − 1 = Q − 1`
  (`Q = q²`);
* genre F **on** the boundary band (`N ≤ m ≤ N + k − 1`): `comp m = 1`, factor `q − 1`,
  which is **NOT** `Q − 1 = q² − 1` for `q ≥ 2`.

**⚠ THIS NODE IS THE REPAIRED `GENH4` CRITICAL.** The content of the third clause is the
*distinction* between the two censuses, not either value on its own: a file stating only
`pinCensus q 1 = q − 1` has not landed the repair. The inequality holds at every `q ≥ 2`,
including `q = 2` (`1 ≠ 3`) — the one place in this chapter where `q = 2` is a good witness.

DEPENDS: none (ℕ-arithmetic only).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- The pin census at a slot of `F_q`-dimension `c`: the nonzero readable vectors of an
`F_q`-subspace of dimension `c`. -/
def pinCensus (q c : ℕ) : ℕ := q ^ c - 1

/-- Genre E: every slot is one `F_q`-digit (`comp = 1`), so the pin census is `q − 1`. -/
theorem pinCensus_genreE (q : ℕ) : pinCensus q 1 = q - 1 := by
  simp [pinCensus]

/-- Genre F, interior (pin height `m ≤ N − 1`): `comp = 2`, so the census is `q² − 1`,
which is `Q − 1` for the stage field of size `Q = q²`. -/
theorem pinCensus_genreF_interior (q : ℕ) : pinCensus q 2 = q ^ 2 - 1 := rfl

/-- The repair itself: on the genre-F boundary band the census is `q − 1` (a single in-window
`F_q`-digit), and that is **not** the interior census `q² − 1 = Q − 1`, at every `q ≥ 2`. -/
theorem pinCensus_band_ne_interior {q : ℕ} (hq : 2 ≤ q) :
    pinCensus q 1 ≠ pinCensus q 2 := by
  have hlt : q < q ^ 2 := by nlinarith [sq_nonneg q]
  simp only [pinCensus, pow_one]
  omega

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.pinCensus_genreE
#print axioms Uniformity.Density.Induction.pinCensus_genreF_interior
#print axioms Uniformity.Density.Induction.pinCensus_band_ne_interior

end AxCheck
