# Lean formalization (`LeanUrat`)

Lean 4 (`v4.31.0`) / mathlib (`v4.31.0`). Formalizes the rationality + palindromy argument
for the projective $p$-adic factorization densities.

## Build

```
lake exe cache get        # prebuilt mathlib oleans (large download)
lake build LeanUrat
```

Reproduce the axiom footprints (this is the honesty deliverable):

```
lake env lean LeanUrat/AxChk_baseline.lean
```

This prints `#print axioms` for ~55 key declarations.

> **Environmental caveat.** On a heavily loaded NFS-backed node, `lake build LeanUrat` has
> been observed to hang at the *final-job commit* step (the worker `lean` exits 0 but lake
> does not return). This is an environmental I/O issue, not a code error: every module
> compiles green via `lake env lean`, and `AxChk_baseline.lean` elaborates all declarations
> with exit 0. On a normal machine `lake build` completes.

## What the capstone says

`Goal.goal_theorem_montes` — footprint `{propext, Classical.choice, Quot.sound,
tame_functionalEquation}` — states that the genuine counting density (the decided-level
limit `M.countingDensity`, with the undecided tail proved to vanish) is a uniform rational
function of $q$ **and** palindromic, conditional on a `CountingModel` / `MontesData` /
`DensityFoundation` hypothesis bundle.

**Proved Lean-core-only** (`{propext, Classical.choice, Quot.sound}`, 0 `sorryAx`): the OM
cluster-volume induction (`OMInduction.clusterVol_isRational`), the box-volume and residual
counts (`MontesAxiom.boxVolume_eq`, `residualBoxCount`/`T_BB3`), additivity
(`clusterCount_boxSum`), the geometric self-loop collapse (`NestedCollapse`), the tail bound
`undecidedVanishes` ($U_N\to0$), the decomposition theorem `countingDensity_eq_sum_coeff`
(a genuine limit-interchange), `countingDensity_isRational`, the `RatFn` closure lemmas, and
the `L7` palindromy transfer. `Witness.montes_full_instance` shows the statement is
non-vacuous over a coupled witness bundle.

## What is assumed (the honest boundary)

- **`boxHaarEquidist` + `nodeMeasure_boxSum`** (`MontesData` fields): the per-box $p$-adic
  Haar volume equals the proved closed-form value, and the node limit is box-additive. This
  is the *measure wall* — equivalently, the Montes cell-count bijection. mathlib has no
  $p$-adic Haar measure, so this is carried as a hypothesis and the only instance built is a
  trivial degree-0 witness, **not** the real density.
- **GMN count-shadow hypotheses** (`partition`, `cells_descend`, `finiteTermination`, tail
  envelopes): the combinatorial shadow of the published Montes algorithm.
- **`tame_functionalEquation`** (the single declared `axiom`): palindromy at tame primes,
  cited from the Igusa–Denef–Meuser / tame factorization-density literature.

So: *uniform rationality + palindromy of the genuine counting density, formally verified
modulo the above + Lean core.* Not an unconditional proof.

## Notes

- `Goal.goal_theorem` is the older measure-route capstone, deliberately kept as a positive
  control; its footprint still carries the four `PadicMeasure` axioms
  (`clusterMeasure`, `AX_cellRecursion`, `omCells`, `descend_size_lt`), which the
  count-native path (`goal_theorem_montes`) eliminates.
- `L3.lean` has two `sorry`s (`card_squarefreeMonicDegree`, `gauss_necklace_count`); both
  are re-proved sorry-free in `L3Squarefree.lean` / `L3Gauss.lean`. An import cycle blocks
  re-pointing them inside `L3` itself, but they are **off every capstone footprint** (the
  count path consumes the sorry-free versions), and no `sorryAx` reaches the goal.
