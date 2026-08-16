/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B67
import Uniformity.Density.InertLeaf

/-!
# Uniformity.ChapB.B68 — THE ORDER-0 LEAF LAW at every degree

**Chapter B, NODE B.68** [theorem] (`blueprint/CHAP-B_leaf_layer.md` §8), ENV-C. One signed
declaration.

*The statement.* Let `f` be monic of positive degree over the complete local base and let its
reduction be **separable**, presented as a product `f̄ = ∏_{i ∈ s} r̄_i` of pairwise distinct monic
irreducibles. Then

```
typeOf f = ⟨ Σ_{i ∈ s} {(1, (r̄_i).natDegree)} ⟩
```

— one unramified factor per residual factor, ramification index `1`, residue degree `deg r̄_i`.

This is `spec/CERTAIN_NODES_2026-08-14.md` REJECTED **R10**, *"the single highest-value node not
on this list"*: it was rejected only because it needs three internal edges — CN-17 (`n`-fold
Hensel), CN-03 (`typeOf_mul`) and CN-21 (the unramified leaf). All three landed on 2026-08-14,
B.67 assembled the first two into the order-0 peel, and this node is the last step.

## Proof

Three steps, exactly the blueprint's.

1. **B.67 at `a i = 1`.** The order-0 peel with all exponents `1` gives the monic family `g` with
   `f = ∏ i ∈ s, g i`, `(g i).map (residue O) = (r i) ^ 1 = r i`, and the type identity
   `(typeOf f).data = ∑ i ∈ s, (typeOf (g i)).data`.
2. **CN-21 per block.** `(g i).map (residue O) = r i` is irreducible, so landed
   `typeOf_inert_of_irreducible_map` values the block at `⟨{(1, (g i).natDegree)}⟩`; landed
   `Uniformity.Hensel.natDegree_eq_of_map_eq` rewrites `(g i).natDegree = (r i).natDegree`
   (which is positive, since an irreducible polynomial over a field is not a unit).
3. **`FactorizationType.ext`.** The type is determined by its datum, so the sum of the blocks'
   singletons is the answer.

The signed hypothesis `hd : 0 < f.natDegree` is not consumed: it is retained because the
signature is frozen against the gate-verified stub. (It is not vacuous decoration either — at
`f = 1` with `s = ∅` both sides are the empty type, so the statement is simply also true there.)

DEPENDS: B.67 (`exists_order0_peel`, at `a i = 1`) · landed
`Uniformity.Density.typeOf_inert_of_irreducible_map` (`Density/InertLeaf.lean:179`),
`Uniformity.FactorizationType.ext` (`Density/LocalData.lean:53`),
`Uniformity.Hensel.natDegree_eq_of_map_eq` · mathlib `Polynomial.Irreducible.natDegree_pos`,
`Finset.prod_congr`.

**Namespace.** `Uniformity.Density.Leaf`, the chapter's namespace, as in the frozen stub.

**SIZE.** blueprint 22 lines; landed 16.

**TEETH.** `W12-LVL0` (`EFF.W12.54`, 0/138 violations) → **Lean theorem** (this declaration).

SOURCE: `spec/CERTAIN_NODES_2026-08-14.md` REJECTED R10; `spec/HYPOTHESIS_LEDGER.md` `HYP.03`'s
residual-scope note; `EFF.W12.22`.

## Status

Sorry-free, axiom-free (Lean core only). The 2026-08-16 B.42 literature cite is **not** on this
file's import path — the order-0 leaf law never touches the slope factorization.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

section ENVC
-- ENV-C (blueprint §0.1): ENV-A + completeness + residue finiteness.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

omit [Finite (ResidueField O)] in
-- `hd : 0 < f.natDegree` is part of the frozen signature and is not used by the proof; see the
-- module docstring.
set_option linter.unusedVariables false in
/-- **B.68 — the order-0 leaf law at every degree.** A monic `f` whose reduction is a product of
pairwise distinct monic irreducibles `r̄_i` has splitting type `⟨Σ_i {(1, deg r̄_i)}⟩`.

Residue finiteness is `omit`ted (§12 rule 7): the node is B.67's peel composed with the
unramified leaf, and neither asks the residue field to be finite. -/
theorem typeOf_of_separable_reduction {f : Polynomial O} (hf : f.Monic) (hd : 0 < f.natDegree)
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {r : ι → Polynomial (ResidueField O)}
    (hmon : ∀ i ∈ s, (r i).Monic) (hirr : ∀ i ∈ s, Irreducible (r i))
    (hne : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → r i ≠ r j)
    (hres : f.map (IsLocalRing.residue O) = ∏ i ∈ s, r i) :
    typeOf f = ⟨∑ i ∈ s, {((1 : ℕ), (r i).natDegree)}⟩ := by
  classical
  -- ## step 1 — the order-0 peel at all exponents `1`
  obtain ⟨g, hgm, -, hgres, hgtype⟩ :=
    exists_order0_peel hf hd (a := fun _ => 1) hmon hirr hne (by simpa using hres)
  -- ## steps 2-3 — every block is an unramified leaf of residue degree `deg r̄_i`
  refine FactorizationType.ext ?_
  rw [hgtype]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hgri : (g i).map (IsLocalRing.residue O) = r i := by rw [hgres i hi, pow_one]
  have hdegi : (g i).natDegree = (r i).natDegree :=
    Uniformity.Hensel.natDegree_eq_of_map_eq (hgm i hi) hgri
  rw [typeOf_inert_of_irreducible_map (hgm i hi)
    (by rw [hdegi]; exact (hirr i hi).natDegree_pos) (by rw [hgri]; exact hirr i hi), hdegi]

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.typeOf_of_separable_reduction
end AxCheck
