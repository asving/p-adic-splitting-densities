# DT1 verdict — definitional twins, batch 1

New file: `leanfinal/Uniformity/ChapC/C140defs.lean`.

## Per-name verdict

- **`ComposedLabel` — LANDED.** leanspec `ChapC.lean:2221–2235` (NODE C.62). Byte-identical
  transcription (verified by `diff` against the leanspec range, modulo namespace/import). All
  referenced vocabulary (`KeyFrame`, `TowerDatum`, `F.Pin`, `TowerDatum.levelDatum`, `towerLabel`,
  `composedKey`, `IsDvPure`, `IsPure`, `dv2SideSet`, `dv2ResPoly`, `AdjoinRoot`) is landed
  (`C01`, `C42`, `C14a`, `C44`, `C43`, `C29`, `ChapB/B34`, `C38a`).

- **`ClassSizeSupplyData` — LANDED.** leanspec `ChapC.lean:2343–2368` (NODE C.69, the
  class-size/block-length TERMINAL SUPPLY bundle, `Prop`-valued). Byte-identical transcription.
  All referenced vocabulary (`LevelDatum`, `KeyFrame.stageField`, `dvSideSet`, `dvHgt`,
  `dvSideMin`, `dvResPoly`, `IsDvPure`, `IsPure`, `BlockContext`, `blockFactor`, `mult₂`,
  `monicFactors`, `typeOf`, `inertiaDegOf`) is landed (`C09`, `C03`, `C06`, `C07`, `C25`, `C29`,
  `ChapB/B34`, `C35`, `Density/TypeOf`). Only the `classSize_supply` axiom that PRODUCES an
  instance of this structure (leanspec L2370–2371) is out of scope for this batch — it is
  proof-content, not a definitional twin, and is left for a proving unit.
  `set_option linter.unusedVariables false in` added ahead of the structure (matches the
  established repo pattern at `C35.lean`/`C97.lean`) since several `hπ`/adic-completeness
  binders are threaded but unused in each clause body, exactly as signed.

- **`Mu2TwoCase` — LANDED.** leanspec `ChapC.lean:3499–3504` (NODE C.79's five-case decision
  tag). Byte-identical transcription; no external dependency (`inductive ... where` with five
  nullary constructors).

- **`Phi1`, `Phi2`, `Phi3` — LANDED**, together with their two composite-defining prerequisites
  `pmul`, `padd`, `psmul`. leanspec `ChapC.lean:4292–4294` (`pmul`), `:4296–4297` (`padd`),
  `:4299` (`psmul`), `:4305–4307` (`Phi1`/`Phi2`/`Phi3`). Byte-identical transcription of each.
  `v2` (leanspec `:4301–4303`) is NOT landed — it is not referenced by `Phi1`/`Phi2`/`Phi3` and
  was outside the named batch; recorded here rather than silently included. These six defs are
  self-contained `List ℤ` arithmetic (C.97's numeric-gate audit script, no signature/D1) and
  needed no leanfinal vocabulary lookup.

- **`DescentStep` — SKIPPED.** leanspec `ChapC.lean:1731–1745`. This is the A-C.1 draft
  constructor for the §5 descent grammar. leanspec itself marks it, in the immediately following
  block (`:1761–1780`): *"MACHINE-REFUTED — STRUCK, NOT DECLARED (A-C.6)"* and *"`DescentStep`
  and `NS7TerminationStatement` above are kept for the record and MUST NOT BE CONSUMED."*
  The A-C.6 redraft `DescentStepR` already supersedes it and is landed in
  `leanfinal/Uniformity/ChapC/C94.lean`. Landing the struck name here would create a dead/trap
  twin the corpus explicitly forbids consuming — skipped per that instruction, not per the
  task's ambiguity clause (which named only item 6).

- **`NS7TerminationStatement` — SKIPPED.** leanspec `ChapC.lean:1752–1759`. Same struck-draft
  situation as `DescentStep` (same `:1761–1780` block): `NS7TerminationStatement → False` is
  proved absolutely in `leanfinal/Uniformity/ChapC/C94_REFUTATION.lean.txt`. The superseding A-C.6
  redraft `NS7TerminationStatementR` is already landed in `leanfinal/Uniformity/ChapC/C94.lean`
  (with `axiom agnprw_termination : NS7TerminationStatementR`). Per the task's own caution note,
  the landed target is the redraft, not this name — skipped, not landed.

## Verification

```bash
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities/leanfinal && lake env lean Uniformity/ChapC/C140defs.lean
```

The command succeeds with zero warnings and zero errors. Every landed declaration has a
`#print axioms` line; the reported footprint is Lean core throughout: `ComposedLabel` and
`ClassSizeSupplyData` depend on `[propext, Classical.choice, Quot.sound]` (structure formation);
`Mu2TwoCase`, `psmul`, `Phi1` depend on no axioms; `pmul`, `padd`, `Phi2`, `Phi3` depend on
`[propext]` alone. No `sorry`, no new axiom, no `unsafe` declaration anywhere in the file.
