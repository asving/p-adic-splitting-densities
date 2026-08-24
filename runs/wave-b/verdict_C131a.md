# C131a verdict

- **C.131a′ — LANDED.** Proved `wtCoeff`, `WT`, `WT_zero`, `wtCoeff_zero`,
  `WT_le_wtCoeff_of_mem`, and the support-free `WT_le_wtCoeff`.
- **C.131b′ — LANDED.** Proved `min_wtCoeff_le_wtCoeff_add`, the finite-sum valuation
  helper `le_wtCoeff_sum`, and `WT_add`.
- **C.131c′ — LANDED.** Proved `wtCoeff_mul`, the two convolution lemmas
  `WT_add_le_inner_convolution` and `WT_add_le_outer_convolution`, and `WT_mul`.

No `sorry`, new axioms, or `unsafe` declarations.  The axiom audit reports only Lean/mathlib's
standard `propext`, `Classical.choice`, and `Quot.sound` dependencies.

Verified from `leanfinal/` with:

```text
lake env lean Uniformity/ChapC/C131a.lean
```
