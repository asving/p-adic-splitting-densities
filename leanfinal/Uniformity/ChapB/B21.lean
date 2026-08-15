/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapB.B21 — the digit at a height

**Chapter B, NODE B.21** (`blueprint/CHAP-B_leaf_layer.md` §4, the order-1 residual layer).
Source: `EFF.W12.23` (*"Each `a_j` is a free module of `N` digit-slots over the residue
`F_q`-space `F_q^d ≅ F_{q^d}` … write `digit_h(a_j) ∈ F_{q^d}` for the slot at height `h`"* —
the GMN order-1 residual-coefficient convention); `EFF.HE3.14`; `EFF.HE6.13`.

For `π : O`, `k : ℕ` and `x : O`, `digAt π k x` is the residue class of the unique `y` with
`x = π ^ k * y` when `π ^ k ∣ x`, and `0` otherwise.  Uniqueness of `y` holds because `O` is a
domain and `π ^ k ≠ 0` (for `π ≠ 0`); the `otherwise` branch is junk and no lemma reads it.
B.22 is the specification that pins the value on the divisible branch.

This node is the *scalar* half of the corpus's `digit_h`: B.23 assembles the coefficientwise
digit into a polynomial and B.28 pushes it into the residual field `F_{q^d}`.  The corpus's
`digit_h` is a **slot**, read at a height that need not be the element's own valuation — which is
exactly why `digAt` takes `k` as an argument rather than computing it.  `EFF.HE3.14`'s residual
coefficient is `0` "whenever the pin at `j₁+tℓ` lies strictly above the `λ`-line", and that is
`digAt π k x = 0` with `k` the line height and `v x > k`.

DEPENDS: none beyond mathlib (`IsLocalRing.residue`, `Dvd.dvd.choose`).

**PROOF.** Definitional.  Environment ENV-A (blueprint §0.1).  The body is the gate-verified
`leanspec/Leanspec/ChapB.lean` stub body verbatim.

## Status

Sorry-free, axiom-free (Lean core only).  **Flagged for human review** (definition faithfulness).
-/

namespace Uniformity.Density.Leaf

-- ENV-A (blueprint §0.1): the polynomial arena.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **B.21 — the digit at a height.** `digAt π k x` : the residue of `x / π ^ k` when
`π ^ k ∣ x` (junk `0` otherwise) — the "digit of `x` at height `k`" of the corpus's digit
calculus. -/
noncomputable def digAt (π : O) (k : ℕ) (x : O) : IsLocalRing.ResidueField O :=
  open Classical in if h : π ^ k ∣ x then IsLocalRing.residue O h.choose else 0

section AxCheck
#print axioms Uniformity.Density.Leaf.digAt
end AxCheck

end Uniformity.Density.Leaf
