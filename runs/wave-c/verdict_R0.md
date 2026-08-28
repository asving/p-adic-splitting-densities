# Verdict: UNIT R0 — depth-four TerminalReceiver and LaurentNormalizer

**Status: LANDED, first attempt, zero repairs.**

Source: `docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md` §6.4 row R0
("Build depth-four `TerminalReceiver` and `LaurentNormalizer`; pin level maps
and exact heights"; inputs: landed `DeepTower.terminalReceiver` (C130tr) +
`DeepTower.laurentNormalizer` (C130ln); campaign input T3; blocker: none).

New file: `leanfinal/Uniformity/ChapC/C136r0.lean`
(namespace `Uniformity.Density.Tower.C136r0`).

## What landed

* `s2TerminalReceiverFour` — `(s2DepthFour h2 hq).terminalReceiver
  (fun _ _ _ => RingHom.id _)`, the depth-two precedent's junk filler
  (`C130s17.s2TerminalReceiver`) reused verbatim one level up in `r`, since
  T3's `s2WitnessFour`/`s2DepthFour` (`C136t.lean`, already landed) still uses
  one constant stage field at every index.
* `s2LaurentNormalizerFour` — `(s2DepthFour h2 hq).laurentNormalizer`,
  unconditional post the C.130f one-token repair.
* Level-map pins: `topEquiv = RingEquiv.refl`, the terminal field
  (`levelHom 4 = topEquiv.toRingHom`), the live-range step-composite identity
  at each of the four live levels 1–4 (`terminalReceiver_levelHom_live`,
  specialized via `show`-then-apply, never bare `rfl` against the
  `dite`-branched `receiverLevelHom` — the TSTK discipline), and injectivity
  at every level.
* Exact-height pins: `norm = laurentNormAt`, `norm_zero`, the universal
  live-range exact-height law specialized to this tower, and its instances at
  the campaign's own numerals — `5` (level 2, `u_2`), `21` (level 3, `u_3`),
  `85` (level 3, the T4 operator height), and `171` (level 4, the T5
  refinement height).

## Verification

```
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C136r0.lean
```

Exit code 0. Full output is exactly the 18 `#print axioms` lines (47 lines
total incl. wraps); zero errors, zero warnings, zero `sorry`. Every
declaration's footprint is `[propext, Classical.choice, Quot.sound]`
(Lean-core only).

## Scope discipline

GCW-6 fence respected: this file is data (a `TerminalReceiver` instance, a
`LaurentNormalizer` instance, and pins) — no `SplitNodePointSource`,
`ChainRealization`, or `RealizedInput` is touched (that is R6/R7/R9). No
landed file was edited; `C136l2e2.lean` untouched; no git operations
performed.
