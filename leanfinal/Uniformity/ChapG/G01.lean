/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.Drainage

/-!
# Uniformity.ChapG.G01 — `ExactVal`, the exact-valuation predicate

**Chapter G, NODE G.01** (`blueprint/CHAP-G_base_cases_menus.md` §3). For `π` in a DVR `O`,
`k : ℕ` and `x : O`, `x` has *exact valuation* `k` when `π ^ k ∣ x` and `¬ π ^ (k+1) ∣ x`.

Definitional, no proof obligation. DEPENDS: none.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- `ExactVal π k x` : `x` has valuation exactly `k` with respect to the uniformizer `π`. -/
def ExactVal (π : O) (k : ℕ) (x : O) : Prop := π ^ k ∣ x ∧ ¬ π ^ (k + 1) ∣ x

end Uniformity.Density.Menu
