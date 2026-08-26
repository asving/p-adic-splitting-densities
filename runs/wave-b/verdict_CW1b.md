# Verdict CW1b — `DrainageAt 2` / `MenuLawAt 3` public wrappers

Unit CW1b (Sonnet transcription tier), brief `runs/wave-b/brief_CW_wrappers.md`.

## Outcome: LANDED, both wrappers.

New file: `leanfinal/Uniformity/ChapI/I03_I04w.lean` (an I.03/I.04-adjacent appendix file, not
a blueprint node — the H09w/H89w/H73w/F04w precedent, matching CW1a's `I02_I03w.lean` for the
sibling unit).

- `Uniformity.Density.drainageAt_two : DrainageAt 2` — replays `CHFD_probe.lean`'s
  `drainageAt_two` (map row `CHFD-N2A2`), directly from the landed `drainage_two`
  (`Density/Drainage.lean:838`). `DrainageAt` is unaltered (`Density/Statement.lean:118`); no
  parallel drainage `Prop` is declared, per I.04's note-node ruling
  (`I04_I12_I19_I22_NOTES_2026-08-20.md`) — this only names a witness at the existing carrier.
- `Uniformity.Density.menuLawAt_three : MenuLawAt 3` — replays `CHFD_probe.lean`'s
  `menuLawAt_three` (map row `CHFD-N3A1`), packaging the landed five-type cubic menu
  `coveringMenu_three` (`ChapG/G54.lean:35`) with the mechanical `A1Family` label cells over
  `{c3split, c3linInert, c3inert, c3linRam, c3ram}` (`ChapG/G52.lean`), degrees from
  `c3_degrees`.

Both proof scripts are byte-identical replays of the CHFD probe's
`drainageAt_two`/`menuLawAt_three` (`leanfinal/scratch/CHFD_probe.lean:91-93,67-89`), which
itself replays H97b's landed cubic-menu content packaged against I.03's own gate shape. No
statement invented; the only plumbing addition is a local `private def a1LabelCell` (identical
ten-field record, forced at `r=0`, free fields `expConst=0, visConst=0, coeff=1`) since I.03's
own `a1LabelCell` is `private` to that file and not importable — identical in every field to
I.03's and CW1a's copies.

## Verification

`cd leanfinal && lake env lean Uniformity/ChapI/I03_I04w.lean` — exit 0, zero errors, zero
`sorry`.

`#print axioms` footer:
```
'Uniformity.Density.drainageAt_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.menuLawAt_three' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Both Lean-core only, as predicted by the brief (no `agnprw_termination` inheritance — neither
wrapper touches `ns7`).

## Scope discipline

Did not touch `I02.lean`, `I03.lean`, `I04_I12_I19_I22_NOTES_2026-08-20.md`, any roll-up,
`leanspec/`, any `ChapC` file, or CW1a's file (`I02_I03w.lean`). No commits made.
