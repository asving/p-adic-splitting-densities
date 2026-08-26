# Verdict CW1a — `DecidedSliceAt 2` / `MenuLawAt 2` public wrappers

Unit CW1a (Sonnet transcription tier), brief `runs/wave-b/brief_CW_wrappers.md`.

## Outcome: LANDED, both wrappers.

New file: `leanfinal/Uniformity/ChapI/I02_I03w.lean` (an I.02/I.03-adjacent appendix file,
not a blueprint node — the H09w/H89w/H73w/F04w precedent).

- `Uniformity.Density.decidedSliceAt_two : DecidedSliceAt 2` — replays `I02.lean:116-125`'s
  anonymous gate (map row CHFD-N2A0), via `uniformityStatement_two` (Chapter G.51) and the
  landed `n=2` tie `genuineDensity_eq_decidedDensity_two`.
- `Uniformity.Density.menuLawAt_two : MenuLawAt 2` — replays `I03.lean:177-210`'s anonymous
  gate content (map row CHFD-N2A1), via the real three-cell family
  `[a1LabelCell splitType, a1LabelCell inertType, a1LabelCell ramType]` over the menu
  `{splitType, inertType, ramType}` and landed `coveringMenu_two`.

Both proof scripts are byte-identical replays of the CHFD probe's
`decidedSliceAt_two`/`menuLawAt_two` (`leanfinal/scratch/CHFD_probe.lean:25-31,46-63`), which
itself replays I02/I03's own gates verbatim. No statement invented; the only plumbing addition
is a local `private def a1LabelCell` (identical ten-field record, forced at `r=0`, free fields
`expConst=0, visConst=0, coeff=1`) since I.03's own `a1LabelCell` is `private` to that file and
not importable.

## Verification

`cd leanfinal && lake env lean Uniformity/ChapI/I02_I03w.lean` — exit 0, zero errors, zero
`sorry`.

`#print axioms` footer:
```
'Uniformity.Density.decidedSliceAt_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.menuLawAt_two' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Both Lean-core only, as predicted by the brief (no `agnprw_termination` inheritance — neither
wrapper touches `ns7`).

## Scope discipline

Did not touch `I02.lean`, `I03.lean`, any roll-up, `leanspec/`, any `ChapC` file, or CW1b's
file. No commits made.
