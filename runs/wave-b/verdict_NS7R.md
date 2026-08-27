# NS7R verdict — 2026-08-27

Status: **LANDED**

## Amendment

Enacted **A-I.4**, the next free Chapter-I amendment number.  The signed I.01
`LeanspecI.NS7Termination` body now has the exact landed A-C.6 redraft shape:

- every complete DVR with finite residue field;
- a uniformizer `π` with `Irreducible π`;
- a monic squarefree polynomial `f`;
- an infinite `Tower.DescentState` history whose blocks divide `f` and whose successors satisfy
  `Tower.DescentStepR`;
- conclusion `False`.

Only the I.01 body matrix changed.  Its name, complete-DVR bundle, and `Prop` kind are preserved;
no other signed declaration changed.  The superseded `True` body and gate are retained as struck
history in comments, following A-I.3's amendment convention.

The Tier 2 queue now begins with A-I.4 and explicitly flags the Tier-1-adjacent linkage to C.94:
`agnprw_termination : NS7TerminationStatementR`, consumed on the landed side by
`ns7Termination_of_cite`.

## Gate and AxChk evidence

The §4 gate item (14) now executes both reconciliation checks:

```lean
example : NS7Termination ↔ Uniformity.Density.Tower.NS7TerminationStatementR := Iff.rfl
example (n : ℕ) (h : CapstoneHypotheses.{uW, uG, uKt, uL} n) : NS7Termination := h.ns7
```

The file's enforced `#axiom_core` gates for `LeanspecI.NS7Termination` and
`LeanspecI.CapstoneHypotheses` pass.  A separate temporary print probe reported for each exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Thus the signed carrier itself remains Lean-core; cite conditionality remains visible in the
landed discharge theorem, whose designed extra dependency is
`Uniformity.Density.Tower.agnprw_termination`.

## Build evidence

- `cd leanspec && lake env lean Leanspec/ChapI.lean` — **exit 0**.
- `cd leanspec && lake build Leanspec.ChapI` — **exit 0**, 9,270 jobs completed.

## Scope audit

Tracked edits are restricted to:

- `leanspec/Leanspec/ChapI.lean` — A-I.4 body, dated/struck amendment record, and gate item (14);
- `docs/REVIEW_QUEUE_2026-08-26.md` — newest Tier 2 row;
- `runs/wave-b/verdict_NS7R.md` — this verdict.

`git diff` shows no tracked edit under `leanfinal/`; no roll-up or other leanspec file was touched.
The `ChapI.lean` executable diff contains only the `NS7Termination` body replacement and the two
required gate examples; every other declaration is byte-unchanged.

## Source-record note

At this checkout, `docs/AXIOM_FAITHFULNESS.md` contains no `agnprw_termination`, AGNPRW, or
`NS7TerminationStatementR` entry to read.  The reconciliation therefore used the available signed
A-C.6 record in `Leanspec/ChapC.lean`, the executed-print-read documentation in
`leanfinal/Uniformity/ChapC/C94.lean`, landed `I01.lean`, and Tier 1 row 1 of the review queue.
