/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.TypeOfAlgebra

/-!
# Uniformity.ChapB.B63a — `typeOf_prod`, the `Finset`-indexed peel law

**Chapter B, NODE B.63a** [RE-PLAN supplier] (`blueprint/CHAP-B_leaf_layer.md` §8, booked at
B.63's SIZE field — *"a 20-line `Finset.prod_induction`"* — and consumed by B.67's and B.80's
DEPENDS; §14 item 10), ENV-A. One signed declaration.

*The statement.* Landed `Uniformity.Density.typeOf_mul` (CN-03) is binary; B.63 step 4, B.67
step 3 and B.80 step 6 all need it iterated over a `Finset` product:

```
(typeOf (∏ i ∈ s, g i)).data = ∑ i ∈ s, (typeOf (g i)).data
```

with monicity of each factor the only hypothesis. Booked as a shared supplier precisely so that
those three nodes do not each grow a private copy (`spec/CERTAIN_NODES_2026-08-14.md` REJECTED
R10: *"Recommendation to the orchestrator: book it as the FIRST second-layer node"*).

**SIGNATURE.** Verbatim from the frozen stub (`leanspec/Leanspec/ChapB.lean`, **B.63a**): binder
names, order, implicitness and conclusion unchanged. The conclusion shape is fixed by B.67's own
conclusion, as the stub's docstring records.

**PROOF.** `Finset.induction_on`, with the monicity hypothesis reverted so the motive carries it.

1. **Empty.** `∏ i ∈ ∅, g i = 1` and `∑ i ∈ ∅, … = 0`; `monicFactors 1 = 0` because the empty
   multiset is a monic factorization of `1` (`IsMonicFactorization 1 0`, uniqueness through the
   landed `monicFactors_eq`), so `(typeOf 1).data = (0 : Multiset _).map efPair = 0`. This is the
   same two-line argument CN-14 (`typeOf_prod_X_sub_C`) uses for its base case.
2. **Insert.** `Finset.prod_insert` / `Finset.sum_insert` peel the new factor; the remaining
   product is monic (`Polynomial.monic_prod_of_monic` on the induction hypothesis's monicity),
   so landed `typeOf_mul` applies and the induction hypothesis closes the tail.

No coprimality, no separability, no completeness: the law is `monicFactors_mul` (CN-02) plus
bookkeeping, exactly as in the binary case.

DEPENDS: landed `Uniformity.Density.typeOf_mul` (`Density/TypeOfAlgebra.lean:60`),
`Uniformity.Density.typeOf_data`, `monicFactors_eq`, `IsMonicFactorization`
(`Density/TypeOf.lean:111`, `:166`) · mathlib `Finset.induction_on`, `Finset.prod_insert`,
`Finset.sum_insert`, `Polynomial.monic_prod_of_monic`.

**Namespace.** Landed in `Uniformity.Density.Leaf`, the chapter's namespace, for consistency with
all 83 sibling declarations and with the closest precedent — B.56's `factorizationType_eq_of_dvd`,
also a theorem about a landed `Uniformity.Density` object living in `.Leaf`. (GC-6 rule 2's
"theorems about landed objects live in the owning namespace" would put it in
`Uniformity.Density`, beside `typeOf_mul`; either resolves unqualified from every chapter-B
consumer, since `.Leaf` is a sub-namespace of `Uniformity.Density`. Flagged for the orchestrator
in case the roll-up prefers the other placement.)

**SIZE.** blueprint 20 lines; landed 16.

**TEETH.** The `W12-BLOCK` product identity (0/1,594,670) that B.67 carries is this lemma's
regression; here **signed non-applicability** (a bookkeeping law with no numeric content of its
own).

SOURCE: `blueprint/CHAP-B_leaf_layer.md` §8, B.63 step 4 and its ⚠ booking; `EFF.W12.27`;
`spec/CERTAIN_NODES_2026-08-14.md` REJECTED R10.

## Status

Sorry-free, axiom-free (Lean core only). The 2026-08-16 B.42 literature cite is not on this
file's import path.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Leaf

open Polynomial

-- ENV-A (blueprint §0.1): the polynomial arena. Nothing below needs completeness or residue
-- finiteness — the same environment `typeOf_mul` itself is stated in.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **B.63a — the `Finset`-indexed peel law.** Landed `typeOf_mul` iterated over a `Finset`
product: the type data of a product of monic polynomials is the sum of their type data. -/
theorem typeOf_prod {ι : Type*} {s : Finset ι} {g : ι → Polynomial O}
    (hg : ∀ i ∈ s, (g i).Monic) :
    (typeOf (∏ i ∈ s, g i)).data = ∑ i ∈ s, (typeOf (g i)).data := by
  classical
  revert hg
  induction s using Finset.induction_on with
  | empty =>
    intro _
    have hF : IsMonicFactorization (1 : Polynomial O) 0 :=
      ⟨fun p hp => absurd hp (Multiset.notMem_zero p), Multiset.prod_zero⟩
    rw [Finset.prod_empty, Finset.sum_empty, typeOf_data, monicFactors_eq hF]
    simp
  | insert a s ha ih =>
    intro hg
    have hga : (g a).Monic := hg a (Finset.mem_insert_self a s)
    have hgs : ∀ i ∈ s, (g i).Monic := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hprod : (∏ i ∈ s, g i).Monic := Polynomial.monic_prod_of_monic _ _ hgs
    rw [Finset.prod_insert ha, Finset.sum_insert ha, typeOf_mul hga hprod, ih hgs]

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.typeOf_prod
end AxCheck
