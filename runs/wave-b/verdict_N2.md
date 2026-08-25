# Verdict: DEC1-N2 (GC-13 bridge plan, node N2)

**Plan:** `docs/in-progress/GC13_BRIDGE_PLAN_2026-08-25.md` §3, node `DEC1-N2` —
the split row's SECOND child (`pureBlock₂`/`pureIface₂`), the block/interface pair for
the linear factor `X − 1` (label `−1`) of the split row's parent
`F = X² − 1 = (X + 1)(X − 1)`. The label-`1` child is not rebuilt — `N3`–`N5` (sibling
file `E57i.lean`) reuse the landed `E57pCert.pureBlock`/`pureIface`.

**File delivered:** `leanfinal/Uniformity/ChapE/E57i2.lean` (new; wave-1 slot, no
conflict with sibling files `E57i1.lean`/`E57ih.lean`).

**Contents:**
* `Uniformity.Density.Ladder.E57iCert.pureBlock₂ : BlockData E57pCert.flatCarrier` —
  `Φ = X`, `F = X - 1`, `μ = 1`, `A := fun _ => -1`, `T = 0`. Template
  `E57pCert.pureBlock` (`E57p.lean:535–550`) with the sign flip. `hkeyfree` uses the
  integer Bézout witness `⟨-1, 1⟩` (`(−1)(X−1) + 1·X = 1`); `hA0 : (-1 : Polynomial ℤ) ≠ 0`
  by `norm_num`; `hdev` by `simp; ring`.
* `Uniformity.Density.Ladder.E57iCert.pureIface₂ : RungInterface.{0,0,0} flatCarrier
  pureBlock₂` — `sides = {(1,1)}`, `len ≡ 1`, `linFac ≡ {((-1:ℚ),1)}`, `hiFac ≡ 0`,
  `rootCount ≡ 1`, `classCount ≡ 1`, `classCountHi ≡ 1`, `W = Unit`. Template
  `E57pCert.pureIface` (`E57p.lean:553–590`) with the label flipped, otherwise verbatim
  (all numeric laws are label-independent).
* Closing `example` — the DEC1-N2 target's body, byte-copied from
  `leanfinal/scratch/DEC1_check.lean`'s `DEC1Check.N2_target` (the check file is scratch,
  not importable, so this is the anti-drift transcription), discharged by
  `⟨pureBlock₂, pureIface₂, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩` — all seven conjuncts
  (`B.Φ = X`, `B.F = X - 1`, `B.μ = 1`, `B.T = 0`, `J.sides = {(1,1)}`,
  `J.linFac (1,1) = {((-1:ℚ),1)}`, `J.hiFac (1,1) = 0`) hold definitionally.

**Build:** `lake env lean Uniformity/ChapE/E57i2.lean` (from `leanfinal/`) — exit 0, zero
`sorry`, zero `axiom`, zero `unsafe`, zero warnings (the one lint hint from an initial
`simp [Finset.sum_range_succ]` draft was cleared by dropping the unused simp arg, leaving
plain `simp; ring`). `#print axioms` on both declarations:

```
'Uniformity.Density.Ladder.E57iCert.pureBlock₂' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Ladder.E57iCert.pureIface₂' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Lean-core only, as required.

**Statement fence / scope discipline:** no edits to `E57p.lean`, `leanspec/`, roll-ups,
or any other unit's files — `E57i2.lean` is a new addition only. No C.69 clause consumed
(plan's stop-the-line finding: C.69 is poisoned; this node cites no C-record axiom at
all — the block/interface data is direct construction, per level-(a) of the plan's
bridge-levels split). No `git` operations performed (per instructions).

**Status:** DEC1-N2 COMPLETE. Ready for `N3`/`N4` (sibling `E57i.lean`) to consume
`pureBlock₂`/`pureIface₂` as named inputs alongside `E57pCert.pureBlock`/`pureIface` and
N1's `mixBlock`/`mixIface`.
