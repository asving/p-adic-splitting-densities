/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapB.B27 — separability over a finite residual field

**Chapter B, NODE B.27** (`blueprint/CHAP-B_leaf_layer.md` §4, the order-1 residual layer).
Source: `docs/GMN_citations.md` fact (I); `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` NS-6;
`EFF.W12.27` (*"If every residual is separable"*); `EFF.HE3.15` (*"every TERMINAL residual
polynomial separable"*).

Let `K` be a finite field.  Then every irreducible `p ∈ K[y]` is separable, and for any `p ≠ 0`,
`p.Separable ↔ Squarefree p`.  Consequently, for a monic `R ∈ K[y]` of positive degree,
`R.Separable` holds iff every monic irreducible factor of `R` occurs with multiplicity `1`.

**Why this is a node and not a `simp` step.**  `docs/GMN_citations.md` fact (I)'s parenthetical is
the whole reason: *"finite fields are perfect at every `r`, so 'needs descent = non-squarefree =
discriminant locus' with no inseparable-irreducible exceptions in any characteristic"*.  The
`Separable ↔ Squarefree` bridge is what makes NS-6 (B.63/B.64) a statement about **multiplicities**
rather than about derivatives, and it is the single place the chapter uses finiteness of the
residue field for anything other than counting.

DEPENDS: mathlib only — `PerfectField.ofFinite` (the instance making a finite field perfect,
found by typeclass synthesis), `PerfectField.separable_of_irreducible`,
`PerfectField.separable_iff_squarefree`.

**PROOF.**  A finite field is perfect (`PerfectField.ofFinite`, an instance: the Frobenius is
injective, hence surjective by finiteness).  `irreducible_separable` is then
`PerfectField.separable_of_irreducible`, and `separable_iff_squarefree` is the pinned equivalence
`PerfectField.separable_iff_squarefree` (which at our pin needs no `p ≠ 0`; the signed hypothesis
`hp` is retained unused, since both sides already fail at `p = 0`).

Environment ENV-D + `[Finite K]`: these two statements bind their own field inline and mention no
`O`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

/-- **B.27 (a) — irreducible ⇒ separable over a finite field.**  There are no
inseparable irreducibles over a finite field, in any characteristic. -/
theorem irreducible_separable {K : Type*} [Field K] [Finite K] {p : Polynomial K}
    (hp : Irreducible p) : p.Separable :=
  PerfectField.separable_of_irreducible hp

-- The signed hypothesis `hp : p ≠ 0` is kept (frozen signature) but is not needed at our pin:
-- `PerfectField.separable_iff_squarefree` holds unconditionally, both sides failing at `p = 0`.
set_option linter.unusedVariables false in
/-- **B.27 (b) — separable ⇔ squarefree over a finite field.**  The bridge that turns
separability of a residual polynomial into a statement about the multiplicities of its monic
irreducible factors. -/
theorem separable_iff_squarefree {K : Type*} [Field K] [Finite K] {p : Polynomial K}
    (hp : p ≠ 0) : p.Separable ↔ Squarefree p :=
  PerfectField.separable_iff_squarefree

section AxCheck
#print axioms Uniformity.Density.Leaf.irreducible_separable
#print axioms Uniformity.Density.Leaf.separable_iff_squarefree
end AxCheck

end Uniformity.Density.Leaf
