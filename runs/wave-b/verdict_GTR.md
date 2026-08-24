# Unit GTR verdict — A-C.12 re-signed GENTOW2 landings (C.99, C.101, C.103)

## Verdict

**All three assigned nodes LANDED** (upgraded from the planned SUPPLY disposition to FULL
landings mid-unit, once TDW's `C84d.lean` — `TowerDatum.deepTower` — appeared). `theta_letter_valued`
correctly NOT attempted (stays BLOCKED, OPEN-LETTERS).

| node | signed name | verdict |
|---|---|---|
| C.99 | `gentow2_Bpp` | **LANDED** — promoted from `GSW_check.gentow2_Bpp_resigned_provable` |
| C.99 | `theta_letter_valued` | not attempted — BLOCKED (OPEN-LETTERS), per charge |
| C.101 | `gentow2_B` | **LANDED** — real proof via `Rres_recipe`, instantiated at `T.deepTower hπ` |
| C.103 | `gentow2_A` | **LANDED** — real proof via `KP_criterion`/`KP_irred`/`nuEquiv_iff_Rres`, instantiated at `T.deepTower hπ` |

New file: `leanfinal/Uniformity/ChapC/C99r.lean`. No other file touched (leanspec, roll-ups,
CC18's `C130s18.lean`, TDW's `C84d.lean` all untouched — `C84d` only imported).

## What's in the file

Six declarations, all sorry-free, all `#print axioms` = `[propext, Classical.choice, Quot.sound]`
(Lean core only — `FGMNCalculus` is a hypothesis carrier, so its fields are ordinary function
arguments, not axioms):

* `gentow2_Bpp` — byte-faithful twin, general `W : DeepTower F H₀ hpin r` with `hr : r = 2` a
  scope-fence hypothesis (needs no `TowerDatum.deepTower`).
* `recipe3` — the §10 shared abbreviation, local byte-mirror (needed to state C.101/C.103).
* `gentow2_A_supply` / `gentow2_B_supply` — the real content, proved over an explicit
  `W₂ : DeepTower.{0, uKt} F H₀ hpin 2` stand-in.
* `gentow2_A` / `gentow2_B` — the byte-faithful leanspec twins: `_supply` instantiated at
  `W₂ := T.deepTower hπ` (TDW's `C84d.lean`, which landed mid-unit). One line each.

Proof content: `gentow2_A`'s `KP_criterion` needs `recipe3`'s Monic/degree shape, proved by a
private one-level-up repeat of C.47/C.53b's "leading term dominates" argument for `composedKey`
(now run on `recipe3`); non-equivalence with `composedKey T` uses `nuEquiv_iff_Rres` against
`KP_keyAt`/`Rres_keyAt` and a degree-mismatch contradiction. `gentow2_B` is one application of
`Rres_recipe` (grades = `hlift`, degrees = `hliftdeg` converted via `hkey` +
`composedKey_natDegree_D₂`) plus `Finset.sum_congr` through the re-signed `hunit`. Exactly the
adjudication doc's sketches (§5/§6), now machine-checked.

## Verification

```text
cd leanfinal && lake env lean Uniformity/ChapC/C99r.lean
```

Exit 0; six `#print axioms` lines, all `[propext, Classical.choice, Quot.sound]`.
