# Unit C131u verdict

## C.131u′ — LANDED

Proved declaration:

* `Uniformity.Density.Tower.C131u.dvAbove_of_forall_coeff_floor`

This is the one-way all-coefficient bridge of v2 §3.7.  It uses the landed flattened
`dvHgt` formula and the positive-scalar finite-infimum law from C.131p′–r′.  No converse is
asserted.

## C.131v′ — BLOCKED

No declaration landed.  The named missing object is the **tagged-census discrepancy normal
form together with its erasure theorem**, advertised at C.131m′ as the `tagged paid-branch
recursion and erasure theorem`.  C.71 supplies the semantic discrepancy and C.131k′–l′
supplies structural normal forms, but neither supplies a term denoting the normal form produced
by the tagged census.  Consequently v2 `Cnv13` has no faithful left-hand side to identify with

```lean
shadowDev T f j - dev (composedKey T) f j
```

Defining that left-hand side to be `xNF F` of the displayed difference would make the theorem
circular and would not establish the census semantics required by §3.8.

## Verification

From `leanfinal/`:

```text
lake env lean Uniformity/ChapC/C131u.lean
```

The command succeeds.  The file contains no `sorry`, new axiom, or `unsafe` declaration.
Its `#print axioms` output is:

```text
'Uniformity.Density.Tower.C131u.dvAbove_of_forall_coeff_floor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
