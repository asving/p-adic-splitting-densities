# UNIT FP0 — VERDICT: the counting recurrence

STATUS FIRST: **THE UNCONDITIONAL SOCKET DID NOT FIRE.  The widest honest FP0 form is
LANDED, zero `sorry`: the entire generic LOOP-cell count is proved, the target decided
set is partitioned into loop and canonical non-loop cells at exact finite cardinality,
and `ClusterRecursionAt m` is proved EQUIVALENT to one named remainder,
`RationalNonloopRemainderAt m`.  Consequently neither `UniformClusterRecursion` nor the
reserved ★★★ `decidedSliceAt_all` is declared.**

Date: 2026-08-29.  File: `leanfinal/Uniformity/ChapI/IFCG15.lean` (NEW, 320 lines).
Verification:

    cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/IFCG15.lean

Result: **exit 0, zero errors, zero warnings, zero `sorry`, zero new axioms**.  Repo
footprint: exactly this file + this verdict; no landed/leanspec file edited; no git
mutation performed.

## What landed

### The loop counting law — fully discharged

`LoopParamsN O m σ M` is the residue centre times the mixed-box preimage of the level-`M`
decided set.  The following generic statements are unconditional at every positive mass:

* `loopClassN_injective`: IFCG3's loop map is injective jointly in centre and mixed-box
  parameter.
* `loopClassN_mem_decidedSet` and `range_loopClassN_subset_decidedSet`: every loop image
  class is `σ`-decided at level `M+m`.
* `card_loopParamsN` and `card_range_loopClassN`: the exact count is
  `q * decidedCount O m σ M * q^κ_m`.
* `loopClassN_weight`: subtraction-free exact weight; multiplying by
  `q^(T_m-1) * q^(mM)` gives `decidedCount(M) * q^(m(M+m))`.
* `loopImageSeq_eq`: after normalization, the loop image is literally
  `q^{-(T_m-1)} * decidedSeq O m σ M`, the coefficient in IFCG14's `LoopStepLaw`.

This leg uses IFCG3's rescale injection/decidedness and IFCG1's mixed-box fibre count.

### The exact finite-level partition and canonical remainder

`nonloopDecidedSet π m σ M` is defined as the target decided set at level `M+m` minus
the proved loop image.  Then:

* `card_nonloop_add_loop` proves exact cardinality additivity against
  `decidedCount O m σ (M+m)`.
* `nonloopCellSeq` is its normalized cardinality.
* `nonloopBaseSeq` is IFCG14's target sequence minus the exact loop scalar.
* `nonloopBaseSeq_step` proves the affine recurrence exactly.
* `nonloopBaseSeq_eq_nonloopCellSeq` proves that this canonical base sequence is not an
  arbitrary analytic subtraction: it is precisely the normalized cardinality of the
  actual non-loop complement.

### The named remainder and exact socket equivalence

`RationalNonloopRemainderAt m` says: after the smaller laws `k < m`, each witnessed
degree-`m` label's canonical non-loop cell sequence tends uniformly over `O` to one
rational function of `q`, with both denominator obligations.

The central audit theorem is:

    clusterRecursionAt_iff_rationalNonloopRemainderAt (m) :
      ClusterRecursionAt m ↔ RationalNonloopRemainderAt m

The reverse implication chooses the canonical non-loop sequence and uses its exact step.
The forward implication proves IFCG14's existential `bs` equals that canonical sequence
pointwise.  Thus the exact affine equality in the current socket is automatic once the
loop term is identified; **the remaining mathematics is precisely the rational limit of
the non-loop finite counts**.

Uniformly:

    uniformClusterRecursion_iff_nonloopRemainder :
      UniformClusterRecursion ↔ UniformRationalNonloopRemainder

and the widest capstone declaration is:

    decidedSliceAt_all_of_nonloopRemainder :
      UniformRationalNonloopRemainder → ∀ n : ℕ, DecidedSliceAt n

This is conditional.  It is not the requested unconditional ★★★ declaration.

## Why the named remainder cannot be discharged from the landed signatures

The decisive finding is a theorem-signature gap, not an assumed difficulty with algebra:

1. **IFCG12's cover is polynomial-level existence.**  `StrongCoverExhaustive` produces
   existential skeleton/parameter/block witnesses for a recentred polynomial.
   `StrongCoverDisjoint` compares two strong realizations carried by the same block
   family.  Neither theorem constructs finite level-`M` cell sets, a partition
   equivalence, or their cardinalities.
2. **IFCG13 does not export the asserted cell-measure bridge.**  It defines
   `skeletonExp` and proves exponent/cone-sum identities in `ℕ`/`ℝ`, but there is no
   theorem whose left side is the cardinality of a strong-realization locus in `Coeff`
   or `MBoxN` and whose right side is `q^{-skeletonExp}`.  Therefore the prose phrase
   “each skeleton's cell has the exact measure” is not a consumable Lean fact.
3. **IFCG6 is a split existence theorem, not a measure-preserving parameter bijection.**
   `schema_split` produces polynomial factors from a residual factorization.  It exports
   no inverse map on finite coefficient classes and no fibre cardinality.
4. **IFCG2 propagates decidedness forward, not counts.**
   `decidedAt_combinedClass` certifies the folded class.  There is no injectivity,
   surjectivity, or product-cardinality theorem for `combinedClass` on child-class
   tuples.
5. The other three remainders from the A0GA verdict are not hidden behind a landed
   general measure theorem: IFCG13's `UnitPatternCensus`/`PatternCensus` are Prop
   interfaces without general instances; only the single-face and all-denominator-one
   general cone forms are proved; and no general stage-field/base-change counting law is
   exported.  These would be inputs to a future proof of the named non-loop remainder,
   but the first missing theorem is already the finite-level cell/split cardinality
   bridge in items 1–4.

Accordingly, asserting `UniformClusterRecursion` from the present corpus would require
inventing exactly the absent per-cell finite counting theorem (plus its general rational
summation inputs), or adding an axiom.  Neither was done.

## ★★★ status and footprint

* ★★★ `Uniformity.Density.IFCG15.decidedSliceAt_all`: **NOT DECLARED**.
* Existing reserved prize name `Uniformity.Density.IFCG14.decidedSliceAt_all`: **also not
  declared** (IFCG14 intentionally provides only `decidedSliceAt_all_of_recursion`).
* Widest exact declaration landed:
  `Uniformity.Density.IFCG15.decidedSliceAt_all_of_nonloopRemainder`.
* Its assumption footprint is the single named package
  `Uniformity.Density.IFCG15.UniformRationalNonloopRemainder`; by the proved iff, that is
  neither weaker nor stronger than IFCG14's `UniformClusterRecursion` socket.

## AxCheck

Every printed declaration in IFCG15 reports exactly Lean core
`[propext, Classical.choice, Quot.sound]`.  The C.33 cite does not occur: the landed cover
cannot be consumed for a count without the missing bridge, so no theorem in this file
depends on it.

