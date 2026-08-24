# Unit AE7 (codex) — enact amendment A-E.7: the leanspec PartitionLeg twin + hpart re-sign

You are a Lean 4 transcription unit in the p-adic-splitting-densities campaign. Repo root:
/data/users/asvin/math-and-lean/p-adic-splitting-densities. Two Lean projects: leanfinal/
(landed) and leanspec/ (signed statements). Build check: `cd leanspec && lake build
Leanspec.ChapE`. THIS UNIT IS EXPLICITLY AUTHORIZED TO EDIT leanspec/Leanspec/ChapE.lean —
the amendment A-E.7 enactment (normally orchestrator work, delegated with exact scope).

## Context
The E.57 hard unit landed leanfinal/Uniformity/ChapE/E57p.lean (committed): the
`PartitionLeg` carrier typing E.57's `hpart : True` socket, with `block_split_of_partitionLeg`
proving the corrected statement, and machine-checked non-vacuity gates. The leanspec
re-sign of `BlockSplitTarget`'s `hpart` binder FAILED on first attempt because leanspec
ChapE declares its OWN `SlotCarrier`/`BlockData`/`RungInterface`/`BlockSuite` twins — the
landed `Uniformity.Density.Ladder.PartitionLeg` cannot apply to leanspec's `I`. The cure:
transcribe a leanspec `PartitionLeg` twin (the `BlockSuite` precedent in the same file).

## Read first
1. leanfinal/Uniformity/ChapE/E57p.lean — the landed `PartitionLeg` (~L144–176) + its
   helpers `ClassIx`, `classWeight` (find them: `rg -n "ClassIx|classWeight" leanfinal/Uniformity/ChapE/E57p.lean`)
   + the module docstring (the adjudication record).
2. leanspec/Leanspec/ChapE.lean — the signed twins (`RungInterface`, `BlockData`,
   `BlockSuite`, `BlockSplitTarget` ~L1279–1293), the §8 A-E.6 RE-SIGN NOTE (~L232, 1236),
   and the file's namespace/universe conventions (E-D6: RungInterface.{uO,uK,uW}).

## Your task
1. In leanspec/Leanspec/ChapE.lean, immediately before `BlockSplitTarget`: transcribe the
   `PartitionLeg` structure twin (+ `ClassIx`/`classWeight` helper twins if leanspec lacks
   them) AGAINST LEANSPEC'S OWN RungInterface/BlockData — field-for-field byte-matching the
   landed structure (docstrings included), with an [A-E.7, 2026-08-24] header comment noting
   it mirrors the landed carrier.
2. Re-sign the binder: `(hpart : True),  -- the product/disjointness leg; typed at GC-13 resolution`
   → `(hpart : Nonempty (PartitionLeg I)),` with an [A-E.7] comment (the GC-13 typing
   executed; landed twin = E57p.lean; corrected statement proved there as
   block_split_of_partitionLeg).
3. Update the `BlockSplitTarget` docstring's "**NOT ASSERTED.**" opening: prefix an
   [A-E.7 2026-08-24] paragraph saying `hpart` is now typed and the target is assertable
   via the landed assembly; keep the historical record below it intact.
4. Verify: `cd leanspec && lake build Leanspec.ChapE` green. Also confirm the field-match:
   a comment-stripped diff of the twin vs the landed structure body (modulo namespace)
   in your verdict.

## Rules
NO sorry/new axioms/unsafe. Byte-fidelity on the mirrored fields — deviations = STOP and
report. Do NOT touch any other leanspec declaration, leanfinal/, or roll-ups. Do NOT git
commit. Write runs/wave-b/verdict_AE7.md (applied diff summary, field-match audit, build
result).
