/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B02

/-!
# Uniformity.ChapB.B03 — the development coefficients have degree below `deg φ`

**Chapter B, NODE B.03** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §3, the development /
polygon layer), ENV-A.

Each coefficient of the `φ`-adic development of `f` has degree strictly below `deg φ`: for
`φ` monic with `0 < deg φ`, `(dev φ f j).degree < φ.degree` for every `f` and `j`.

DEPENDS: B.02 (`dev`) · mathlib `Polynomial.degree_modByMonic_lt`.

**PROOF.** Induction on `j`, generalising `f`. At `j = 0` the development coefficient is
`f %ₘ φ` by definition, and `degree_modByMonic_lt` is exactly the claim. At `j + 1` the
coefficient is `dev φ (f /ₘ φ) j` by definition, so the induction hypothesis applies at
`f /ₘ φ`.

SOURCE: `EFF.W12.23` (*"`deg A_j < D′`"*); `EFF.HE3.13`; `EFF.HE6.10`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

-- The signed hypothesis `hd : 0 < φ.natDegree` is kept (frozen signature) but is not needed at
-- our pin: `Polynomial.degree_modByMonic_lt` holds for every monic `φ` over a nontrivial ring,
-- the degenerate case `φ = 1` being `⊥ < 0`. Consumers state the bound with `hd` in hand anyway.
set_option linter.unusedVariables false in
/-- Every coefficient of the `φ`-adic development of `f` has degree below `φ.degree`. -/
theorem degree_dev_lt {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree) :
    ∀ (f : Polynomial O) (j : ℕ), (dev φ f j).degree < φ.degree := by
  intro f j
  induction j generalizing f with
  | zero => exact degree_modByMonic_lt f hφ
  | succ j ih => exact ih (f /ₘ φ)

section AxCheck
#print axioms Uniformity.Density.Leaf.degree_dev_lt
end AxCheck

end Uniformity.Density.Leaf
