/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G64

/-!
# Uniformity.ChapG.G66 — `hex3U`, the HEX3 conservative-residue function

**Chapter G, NODE G.66** (`blueprint/CHAP-G_base_cases_menus.md` §9). *The HEX3
conservative-residue function `u`,* in its telescoped (direct-sum) form:
`u(q,N) = q^(2N−2) + (q−1)·∑_{k=1}^{⌊(N−1)/3⌋} q^(4k−1)·(q^(N−3k) − 1)·R(N−3k)`.

DEPENDS: G.64.

`hex3U q N` is the per-centre conservative-undecided count of the cubic TRP stratum
(`EFF.HEX3.08`, THEOREM HEX3.A), in telescoped form. Pure arithmetic — this definition
mentions no ring.

⚠ ARITHMETIC CROSS-CHECK (blueprint, verbatim note carried forward, three anchors):
`u(q,1) = 1`, `u(q,2) = q²`, `u(q,3) = q⁴` (the `k`-sum is empty for `N ≤ 3`);
`u(q,4) = q⁶ + (q−1)²q³`; `u(2,7) = 4096 + 1440 + 128 = 5664`.

Definitional, no proof obligation.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

/-- HEX3's `u(q, N)` — the per-centre conservative-undecided count of the cubic TRP stratum
(`EFF.HEX3.08`, THEOREM HEX3.A), in telescoped form. Pure arithmetic. -/
def hex3U (q N : ℕ) : ℕ :=
  q ^ (2 * N - 2)
    + (q - 1) * ∑ k ∈ Finset.Icc 1 ((N - 1) / 3),
        q ^ (4 * k - 1) * ((q ^ (N - 3 * k) - 1) * hex3R q (N - 3 * k))

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.hex3U

end AxCheck
