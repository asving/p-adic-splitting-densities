# C131m verdict

**LANDED**

Implemented `leanfinal/Uniformity/ChapC/C131m.lean` for Chapter C, node C.131m′.

Declarations proved/supplied:

- finite tagged-sum carrier and erasure operations: `TaggedTerm`, `eraseTagged`, `pay`,
  `preserve`, with erasure lemmas for append, paid-tag increment, and tail multiplication;
- the concrete two-branch x-carry: `xCarryTail`, `xCarryPaid`, `xCarryStep`, its zero/one tag
  theorem, the inherited tail floor, and the inherited exact paid-branch `WT` formula;
- structural inner recursion: `taggedXNFUpTo`, `taggedXNF`,
  `eraseTagged_taggedXNFUpTo`, and `taggedXNF_erasure`;
- tag-preserving outer transport and structural coefficientwise recursion:
  `atOuter`, `taggedCoeffwiseUpTo`, `taggedCoeffwiseXNF`, and their erasure theorems;
- outer tagged normal form and the requested erasure theorem:
  `taggedOuterNF`, `taggedOuterNF_erasure`.

The recursion is structural on natural bounds and produces finite lists.  No `sorry`, new
axiom, `unsafe` declaration, or polynomial-dependent termination measure is present.  The
footer prints the axiom footprint of every authored declaration.

Verification command (from `leanfinal/`):

```text
lake env lean Uniformity/ChapC/C131m.lean
```

Result: exit code 0.
