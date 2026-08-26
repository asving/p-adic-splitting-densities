# Verdict — unit BW1 (probe-complete F2/F3 landings)

**Verdict: LANDED.** The already-proved quotient/norm bridge and shadow-linearity API are now
production declarations in two topical files. No existing Lean source, scratch probe, roll-up,
or out-of-scope file was edited.

## LANDED — F2.1 scalar-membership transfer

File: `leanfinal/Uniformity/ChapB/B53d.lean`.

The contract is the corrected, membership-assisted one: ramified exactness supplies a nonzero
scalar-membership certificate, and `quotKeyEquiv` transfers it. No bare norm-nonzero implication
is stated.

* `Uniformity.Density.Leaf.normA_ne_zero_of_normB_ne_zero` — first orientation, line 43.
* `Uniformity.Density.Leaf.normB_ne_zero_of_normA_ne_zero` — reverse orientation, line 69.

Both retain the exact generality of `scratch/DEC4_check.lean`: only the target quotient's monicity
is assumed in each orientation, together with `c ≠ 0` and membership in the source principal
ideal.

## LANDED — F2.2 norm-valuation symmetry

File: `leanfinal/Uniformity/ChapB/B53d.lean`.

* `Uniformity.Density.Leaf.addVal_norm_symm` — line 98.

The statement remains generic in two monic positive-degree polynomials and keeps both norm
nonvanishing hypotheses explicit. Its proof rewrites both norm valuations through
`length_quot_eq_addVal_norm` and identifies the quotient lengths with `quotKeyEquiv`.

## LANDED — F3.5 shadow linearity API

File: `leanfinal/Uniformity/ChapC/C131ah.lean`.

* `Uniformity.Density.Tower.biRead_add` — line 40.
* `Uniformity.Density.Tower.biRead_composedKey_monic` — line 47.
* `Uniformity.Density.Tower.shadowDev_add` — line 58.

These are the three probe-complete declarations from `scratch/DEC4_check.lean`: coefficientwise
linearity, monicity through the mapped canonical `xNF`, and additivity through `devQ_add` plus
`reass_add`.

## Verification and AxCheck

Run from `leanfinal/`:

```text
lake env lean Uniformity/ChapB/B53d.lean
# exit 0
lake env lean Uniformity/ChapC/C131ah.lean
# exit 0
```

AxCheck footers are at `B53d.lean:131-133` and `C131ah.lean:70-72`. Every declaration prints
exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Scoped source scans found zero `sorry`, zero `sorryAx`, and zero new `axiom` declarations.

## Deviations

The plan fixed declaration names/namespaces but was silent on filenames. Following topical local
convention, F2.1–F2.2 were placed in the next B.53 file, `B53d.lean`, and F3.5 in the next
available C.131-series file, `C131ah.lean`. This deliberately avoids extending the older C150 RB
grab-bag.

No production-name collision required renaming. The only proof adaptation was to open
`Uniformity.Density.Tower.C131k` explicitly in `C131ah.lean`; the scratch probe obtained `xNF`
from a broader namespace-open set. Statements and proofs are otherwise unchanged in generality.
