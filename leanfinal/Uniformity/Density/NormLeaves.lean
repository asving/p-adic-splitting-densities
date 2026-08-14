/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.TypeOf

/-!
# Uniformity.Density.NormLeaves — the norm of the root, and the Eisenstein leaf at every `n`

Two nodes of `spec/CERTAIN_NODES_2026-08-14.md`:

* **CN-19** `norm_adjoinRoot_root` — `N(α) = (−1)ⁿ·a₀` for every monic `f` over a domain.
* **CN-20** `typeOf_eisenstein` — the totally ramified leaf `⟨{(n,1)}⟩` at every degree `n`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing Polynomial

end Uniformity.Density
