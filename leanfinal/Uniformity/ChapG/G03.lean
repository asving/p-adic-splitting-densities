/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.Drainage

/-!
# Uniformity.ChapG.G03 — `readEquiv`, the (value, derivative) re-coordinatisation

**Chapter G, NODE G.03** (`blueprint/CHAP-G_base_cases_menus.md` §3). At a level-`N` centre
class `γ : Res O N`, re-coordinatise the level-`N` coefficient box of monic quadratics by the
pair (value at `γ`, derivative at `γ`): the map `(a₀, a₁) ↦ (γ² + a₁γ + a₀, 2γ + a₁)` is a
bijection of `(O ⧸ 𝔪^N)²`, because each coordinate is a translation once the other is fixed.

DEPENDS: landed `Uniformity.Density.Coeff`, `Uniformity.Density.Res` (`LocalData.lean:75,131`).

⚠ RE-DERIVATION TARGET: `leancheck/UniformityCheck/Counting.lean` lands the same declaration;
this is the independent `leanfinal` re-derivation (`leancheck` imports `leanfinal`, never the
converse).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-- The `(value, derivative)` re-coordinatisation of the level-`N` box at the centre class `γ`. -/
def readEquiv {N : ℕ} (γ : Res O N) : Coeff O 2 N ≃ (Res O N × Res O N) where
  toFun c := (c 0 + c 1 * γ + γ ^ 2, 2 * γ + c 1)
  invFun p := ![p.1 - (p.2 - 2 * γ) * γ - γ ^ 2, p.2 - 2 * γ]
  left_inv := by intro c; funext i; fin_cases i <;> simp <;> ring
  right_inv := by intro p; simp <;> ring

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.readEquiv

end AxCheck
