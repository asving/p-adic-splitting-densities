# Verdict: DEC1-N5 (GC-13 bridge plan, node N5, final section of `E57i.lean`)

**Plan:** `docs/in-progress/GC13_BRIDGE_PLAN_2026-08-25.md` §3, node `DEC1-N5` — the plan's
FINAL node: assembly + firing `block_split_of_partitionLeg` at the SPLIT row
(`F = X² − 1 = (X+1)(X−1)`, one side `(1,1)`, TWO unit-weight linear classes). Consumes N3's
ledger/product/disjointness field-group (`split_N3`) and N4's degree/purity/threshold
field-group (`split_N4`, both already landed in `E57i.lean`), plus the landed
`PartitionLeg`/`block_split_of_partitionLeg`/`PartitionLeg.dvd_classCount_lin`
(`Uniformity/ChapE/E57p.lean`).

**File extended:** `leanfinal/Uniformity/ChapE/E57i.lean` (N3/N4's sections left
byte-untouched — verified via `git diff`: the only changes are pure line **insertions**
after N4's closing `theorem split_N4` proof and before `end E57iCert`, plus three new
`#print axioms` lines appended after N3/N4's existing four; 58 insertions, 0 deletions,
0 lines of N3/N4 content removed or altered).

**Contents added (namespace `Uniformity.Density.Ladder.E57iCert`):**
* `splitLeg : PartitionLeg mixIface` — assembled via the anonymous constructor in exactly
  `DEC1Check.legOfSpecs`'s field order: `⟨splitCls, split_N3.1, split_N3.2.1, splitBlk,
  split_N3.2.2.1, split_N3.2.2.2, split_N4.1, split_N4.2.1, split_N4.2.2.1,
  split_N4.2.2.2.1, split_N4.2.2.2.2⟩` (projections of N3's 4-conjunct and N4's
  5-conjunct packed proofs onto `PartitionLeg`'s 11 fields — no repair needed, the
  decomposition is exactly lossless as `legOfSpecs` term-checks in `scratch/DEC1_check.lean`).
  This is the first typed leg in the campaign with a genuinely MULTI-class ledger (two
  linear classes, each assigned its OWN child block: `E57pCert.pureBlock` for `a1`,
  `E57i2`'s `pureBlock₂` for `a2`) — `E57pCert.pureLeg` and `E57ih.lean`'s `hiLeg` are both
  one-class residues where the sole block IS the row.
* `split_partitionLeg_nonempty : Nonempty (PartitionLeg mixIface) := ⟨splitLeg⟩` — the
  typed `hpart` socket discharged at the split row.
* `split_blockSuite : Nonempty (BlockSuite mixIface)` — fired via
  `block_split_of_partitionLeg mixIface splitLeg.supplies_hblocks
  splitLeg.supplies_hblocksHi ⟨splitLeg⟩`.
* Teeth:
  - `example : splitCls.card = 2 := Finset.card_pair a1_ne_a2` — the ledger is genuinely
    two classes.
  - Two `dvd_classCount_lin` examples, one per class (`a1`'s label `1`, `a2`'s label
    `−1`): `(1*1 : ℕ) ∣ mixIface.classCount (1,1) ((±1:ℚ),1)`, each discharged by
    `splitLeg.dvd_classCount_lin (1,1) (by simp [mixIface]) (±1,1) (by simp [mixIface])`.
    At `D = 1` the read is numerically trivial (`1*1 ∣ 1`, per the plan's own honest note —
    the hi row's N7 carries the saturated non-trivial case) but this is the first row
    exercising the field at more than one class of the same leg.
* Closing `example` — the DEC1-N5 target's body, byte-copied from
  `leanfinal/scratch/DEC1_check.lean`'s `DEC1Check.N5_target`, discharged by
  `⟨mixBlock, mixIface, rfl, rfl, split_partitionLeg_nonempty, split_blockSuite⟩`.

**Build:** `lake env lean Uniformity/ChapE/E57i.lean` (from `leanfinal/`) — exit 0, zero
`sorry`, zero `axiom`, zero `unsafe`. Also ran `lake build Uniformity.ChapE.E57i` (per task
instructions, in place of a bare `lake build`) — 1376/1376 jobs, "Build completed
successfully"; the only diagnostics are pre-existing `linter.style.show` warnings on N3/N4's
unmodified `show`-tactic lines (151, 155, 156, 162, 163, 165, 166 — all inside the
untouched N3/N4 proofs, not new). `#print axioms` on all seven declarations in the file
(N3/N4's four plus N5's three):

```
'Uniformity.Density.Ladder.E57iCert.splitCls' depends on axioms: [propext, Quot.sound]
'Uniformity.Density.Ladder.E57iCert.splitBlk' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Ladder.E57iCert.split_N3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Ladder.E57iCert.split_N4' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Ladder.E57iCert.splitLeg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Ladder.E57iCert.split_partitionLeg_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Ladder.E57iCert.split_blockSuite' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Lean-core only, as required.

**Statement fence / scope discipline:** no edits to `E57p.lean`, `E57i1.lean`, `E57i2.lean`,
`leanspec/`, roll-ups, or any sibling unit's files; `E57i.lean` is the only file touched,
N3/N4's sections are byte-untouched (verified by `git diff`: 58 insertions, 0 deletions).
No C.63/C.69 clause consumed — level-(a) of the plan's bridge-levels split: the leg's
fields are direct construction over the landed `mixBlock`/`mixIface`/`pureBlock`/
`pureBlock₂`, citing no C-record axiom. No `git add`/`commit` performed.

**Status:** DEC1-N5 COMPLETE — the plan's final node. The split row's `hpart` socket is now
discharged (`Nonempty (PartitionLeg mixIface)`) and the corrected E.57 statement
(`block_split_of_partitionLeg`) fires end-to-end at a genuinely multi-class row for the
first time in the campaign; the E-D15 linear divisibility (`dvd_classCount_lin`) is
exercised at both classes. Together with N1–N4 (landed) and N6/N7 (landed in `E57ih.lean`),
all seven nodes of the GC-13 bridge plan's level-(a) SHADOW-instance bridge are now complete.
The ARENA bridge (level (b): landing C.63 in `leanfinal` + the arena functor
`Tower → Ladder`) remains the honestly MISSING, unplanned object per the plan's §2(b).
