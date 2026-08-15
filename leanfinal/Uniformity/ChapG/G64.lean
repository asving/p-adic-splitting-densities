/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.Drainage

/-!
# Uniformity.ChapG.G64 — `hex3R`, the HEX3 residual recursion

**Chapter G, NODE G.64** (`blueprint/CHAP-G_base_cases_menus.md` §9). *The HEX3 residual
recursion `R`.* `R(q, M)` counts the level-`M` block states whose `n = 2` chain reaches
`A₀ = 0`; its closed form is `R(M) = q^(M−1) + ⌊(M−1)/2⌋·(q−1)·q^(M−2)`, with `R(1) = 1`.

DEPENDS: none. Pure arithmetic — this definition mentions no ring (`ENVIRONMENT. ENV-A (no O)`
per the blueprint node).

⚠ THE IDENTIFICATION A CROSS-READER SHOULD MAKE (blueprint, verbatim note carried forward):
`R(M)` is exactly W-11's *shape-truncated* undecided count per centre; chapter G does **not**
prove `q·hex3R q N` equals any Lean-side count — that identification is `W11-BOX-5`
(`EFF.W11.33`), out of this chapter's scope.

Definitional, no proof obligation.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

/-- HEX3's `R(M)`: the `n = 2` conservative-drain count per centre at window `M`
(`EFF.HEX3.26`, LEMMA H-4). Pure arithmetic — this definition mentions no ring. -/
def hex3R (q M : ℕ) : ℕ := q ^ (M - 1) + ((M - 1) / 2) * ((q - 1) * q ^ (M - 2))

end Uniformity.Density.Menu
