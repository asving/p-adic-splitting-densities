# Unit C131d verdict

## C.131d′ — LANDED

File: `leanfinal/Uniformity/ChapC/C131d.lean`

Declarations proved:

- `Uniformity.Density.Tower.key_coeff_side_floor` (F4)
- `Uniformity.Density.Tower.key_coeff_side_floor_cleared` (F5)

The proof uses the landed `F.hpure`, `suppVal_of_pure`, `suppVal_le_weight`, and `npHgt_X`.
The cleared form is obtained by monotonicity of natural scalar multiplication on `ℕ∞`.

## C.131e′ — LANDED

Declarations proved:

- `Uniformity.Density.Tower.xCarry_tail_floor`
- `Uniformity.Density.Tower.xCarry_branch_wtCoeff_exact`
- `Uniformity.Density.Tower.xCarry_branch_WT_exact`

The tail proof uses C131a's shared `C131a.WT` and `C131a.wtCoeff` (no duplicate weight), proves
the leading coefficient cancellation and the strict `a < D′` bound for every surviving tail
coefficient, and applies F5 after the inner and outer shifts.  The singleton `Y` branch has
exact weight equal to the prior side price plus `T.margin`; the no-truncation equality uses
`T.hfloor` and C.71's definition of `TowerDatum.margin`.

## Verification

Verified from inside `leanfinal/` with exactly:

```text
lake env lean Uniformity/ChapC/C131d.lean
```

Result: exit code 0.  All five declarations' `#print axioms` output contains only `propext`,
`Classical.choice`, and `Quot.sound`; there is no `sorryAx`.

## Commit note

The required `git add`/commit was attempted after the d′ increment, but this execution
environment mounts `.git` read-only and rejected creation of `.git/index.lock` with
`Read-only file system`.  No unrelated file was staged or modified by this unit.
