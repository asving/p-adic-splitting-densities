# C131h verdict — monic-division ledger (F6/F7/F8)

## Per-node verdict

- **C.131h′ — LANDED.** `WT_divByMonic_ge_sub` proves the one-step quotient bound F6 by
  well-founded induction over mathlib's actual `Polynomial.divModByMonicAux` recursion.
- **C.131i′ — LANDED.** `WT_modByMonic_ge` proves the one-step remainder bound F7 in the
  same simultaneous recursion, retaining the full incoming floor.
- **C.131j′ — LANDED.** `division_ledger` proves F8 for the structural definitions
  `quotIter` and `quotDigit`; `quotIter_floor` supplies its quotient half.

## Supply declarations

`natDegree_K_T_le`, `coeff_K_T_top`, `monic_K_T`, `natDegree_K_T`, `wtCoeff_neg`,
`WT_neg`, `wtCoeff_outer_key_shift`, `leadingTerm_floor`, and
`divModByMonicAux_floor` package the canonical divisor pins and the long-division
bookkeeping used by the three nodes.

No node is BLOCKED.  The file contains no `sorry`, new axiom, or `unsafe` declaration.

## Verification

```bash
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities/leanfinal && lake env lean Uniformity/ChapC/C131h.lean
```

The command succeeds.  Every declaration in the file has a `#print axioms` line; the
reported footprint is `[propext, Classical.choice, Quot.sound]` throughout.
