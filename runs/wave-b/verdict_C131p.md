# Unit C131p verdict

## C.131p′ — LANDED

Declarations:

- `enat_nsmul_finset_inf` (Cnv1)
- `enat_add_finset_inf`, `enat_finset_inf_add` (Cnv2)
- `finset_inf_sigma` (Cnv3)
- `inf_range_eq_inf_support` (Cnv4)

## C.131q′ — LANDED

Declarations:

- `gaussVal_C_eq_addVal` (Cnv5)
- `stageHeight_eq_coeff_inf` (Cnv6)

## C.131r′ — LANDED

Declarations:

- `dvHgt_eq_coeff_inf` (Cnv7)
- `dvSupp_eq_nested_inf'`
- `dvSupp_eq_nested_inf` (Cnv8, normalized two-index coefficient weight)

## C.131s′ — LANDED

Declarations:

- `dev_reconstruct_reduced` (Cnv9 in-range recovery)
- `dev_reconstruct_reduced_tail` (Cnv9 vanishing tail)

The range-to-support conversion used by this node is the generic Cnv4 declaration
`inf_range_eq_inf_support` landed in C.131p′.

## Verification

Verified from inside `leanfinal/` with exactly:

```text
lake env lean Uniformity/ChapC/C131p.lean
```

The axiom footer reports only Lean/mathlib foundations (`propext`, `Classical.choice`,
`Quot.sound`) for every declaration: no `sorryAx`, no new axiom, and no `unsafe` declaration.

## Commit note

The requested `git add`/`git commit` was attempted twice (including the prescribed five-second
retry), but this execution environment exposes `.git` read-only and both attempts failed while
creating `.git/index.lock`. Only `leanfinal/Uniformity/ChapC/C131p.lean` and this verdict file
were authored by this unit.
