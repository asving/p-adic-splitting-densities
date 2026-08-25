# Unit NP8 verdict — S2-source plan node NP-8 (the S2 arena data)

## Verdict: **LANDED**

New file: `leanfinal/Uniformity/ChapC/C130np8.lean` (plan row NP-8: "Construct `arenaRead`,
`towerRead`, `peelUnit`; lint that no canonical/arena equality was introduced"). Zero `sorry`,
no new axiom, no `unsafe`, no `True` body; all 25 named declarations print Lean-core axioms
only (`propext`/`Classical.choice`/`Quot.sound`); `lake env lean` and
`lake build Uniformity.ChapC.C130np8` both green (8700 jobs, no collisions).

## What was computed

`Kt := (S2DepthTwo h2 hq).fld 2` has `|Kt| = 2` (`s2Fld₂_card`, CC-6). This forces `|Ktˣ| = 1`
unconditionally (`np8_units_subsingleton`), so:

* **`arenaRead`/`peelUnit`** (codomain `Ktˣ`) are FORCED to the trivial value `1` at every
  index whatsoever, live or junk — no nonzero/liveness hypothesis needed (`s2ArenaRead_forced`,
  `s2PeelUnit_forced`, stronger than the existing `C130np6.s2Letter_forced` pattern, which does
  need a nonzero hypothesis on the field `Kt` itself).
* **`towerRead`** (codomain `Kt`, not `Ktˣ`) is genuinely FREE: `Kt` has two elements, so no
  cardinality collapse applies (`s2Kt_zero_ne_one`); the concrete choice `s2TowerRead := 0` is
  a convenience. `s2Kt_eq_zero_or_one` records the honest small-values fact that IS forced:
  every element of `Kt` is one of the two numerals `0`/`1`.

CC-11's arena-family constructors (`gaugeArenaAt`/`arenaRead0`/`gaugeArena0At`/
`gaugeArenaFamily0`/`towerReadFamily0`/`peelUnitFamily`, `C130ar`) were then instantiated
directly against these concrete values (`s2GaugeArenaAt`, `s2ArenaRead0`, `s2GaugeArena0At`,
`s2GaugeArenaFamily0` with `_live`/`_junk` pins, `s2TowerReadFamily0` with `_live`/`_junk`
pins, `s2PeelUnitFamily`), reusing CC-11's standalone helpers (`arenaKerProj`,
`LaurentNormalizer.arenaNormSectionAt`/`.arenaNormSection0`, `gaugeLive_exists_iff`) verbatim.
This is done WITHOUT a `NodePointSource`/`SplitNodePointSource` wrapper: the un-split
`NodePointSource` is uninhabitable at the S2 repository realization's receiver/keys for ANY
choice of these three fields (U13's char-2 argument bites on `coeffHom`/`pointHgt_eval`
independently), so CC-11's methods (which live on a `NodePointSource` instance) cannot be
called through one at S2; the bodies were reconstructed byte-parallel instead. The S2 tower's
unique gauge-live index is `j = 1` (`1 < r = 2` exactly, no slack — `gaugeLive_exists_iff`
tooth included); live-index numerals are spelled out for `towerRead` at `j = 1` and `peelUnit`
at `i = 1, 2`.

## Separation lint (CC-11's audit pattern, re-run at this file)

Mechanical grep-tooth from the repo root:

```
rg -n "canonical[R]ead|[H]VarthetaRes|hvartheta[R]es|algebra[M]ap" \
  leanfinal/Uniformity/ChapC/C130np8.lean
```

returned NO output (exit 1) — no canonical/arena equality, no `Lˣ`-valued datum, no
`algebraMap`, and no residue-ambient reference occurs anywhere in the file. The file never
constructs a `NodePointSource`/`SplitNodePointSource` instance, so no socket-unpacking
argument can be smuggled in either.

## Supply notes for downstream nodes

* Feeds `FD-0`'s later `SplitNodePointSource`/`FGMNSourceData` assembly: `s2ArenaRead`,
  `s2TowerRead`, `s2PeelUnit` are ready to plug into the corresponding fields verbatim.
* NP-4 (threshold source) and NP-7 (canonical read) are untouched, own their files, and were
  not imported or duplicated here.
