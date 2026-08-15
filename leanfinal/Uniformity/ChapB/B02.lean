/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapB.B02 — `dev`, the `φ`-adic development

**Chapter B, NODE B.02** [def] (`blueprint/CHAP-B_leaf_layer.md` §3, the development /
polygon layer), ENV-A.

For monic `φ` of positive degree and any `f ∈ O[X]`, the `j`-th development coefficient is
defined by iterated monic division: `dev φ f 0 = f %ₘ φ` and `dev φ f (j+1) = dev φ (f /ₘ φ) j`.

DEPENDS: none (mathlib `Polynomial.modByMonic`, `Polynomial.divByMonic`).

**PROOF.** Definitional. The recursion is structural in `j`, so no well-foundedness obligation
arises; `f` is the varying argument and `φ` is fixed, which is why `φ` is a parameter and `f`
is not.

The definition does not require `φ̄` irreducible, only `φ` monic — deliberately, since the
product law (B.32) is proved for any monic `φ`. Monicity is not bound here either: it enters
only in the lemmas about `dev` (B.03–B.06), where `%ₘ`/`/ₘ` have their intended meaning.

**Flagged for human review as a new definition** (parent CLAUDE.md trust boundary).

SOURCE: `EFF.W12.23` verbatim ("Monic division gives the UNIQUE `Φ`-adic development
`f = Φ^m + Σ_{j<m} a_j Φ^j`, `a_j ∈ (O/π^N)[x]_{<d}`"); `EFF.HE3.13`; `EFF.HE6.10`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- `dev φ f j` : the `j`-th coefficient of the `φ`-adic development of `f`. -/
noncomputable def dev (φ : Polynomial O) : Polynomial O → ℕ → Polynomial O
  | f, 0 => f %ₘ φ
  | f, (j + 1) => dev φ (f /ₘ φ) j

section AxCheck
#print axioms Uniformity.Density.Leaf.dev
end AxCheck

end Uniformity.Density.Leaf
