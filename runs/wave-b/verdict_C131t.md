# Unit C131t verdict

## Per-node status

- **C.131t′ — LANDED.** Proved
  `Uniformity.Density.Tower.C131t.dv2Hgt_eq_WT_phiNF` by flattening `dv2Hgt` with
  C131p's `dvSupp_eq_nested_inf`, identifying the digits with C131k's `xNF_coeff` and
  `xDigit_eq_dev`, and converting both finite ranges to supports with
  `inf_range_eq_inf_support`.
- **C.131x′ — LANDED.** Proved
  `Uniformity.Density.Tower.C131t.dv2Hgt_add_eq_left_of_lt`.  The proof establishes strict
  exactness for `WT` at a coefficient attaining the shallower weight, uses additivity of
  the canonical development, and transports the result through C.131t′.
- **SUPPLY:** none.
- **BLOCKED:** none.

Both declarations are sorry-free and have axiom footprint
`[propext, Classical.choice, Quot.sound]` (Lean core only).

## Verification

```sh
cd leanfinal && lake env lean Uniformity/ChapC/C131t.lean
```
