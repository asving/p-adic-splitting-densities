# Verdict: DEC1-N6 (GC-13 bridge plan, node N6, part 1 of `E57ih.lean`)

**Plan:** `docs/in-progress/GC13_BRIDGE_PLAN_2026-08-25.md` §3, node `DEC1-N6` — the HI
row's parent block/interface pair (`hiBlock`/`hiIface`): `F = X² + X + 1` over the landed
flat carrier, one side `(1,1)`, ONE higher residual class of degree `2`, multiplicity `1`
(the inert shape — no linear residual at all). Exercises the `hclsHi`/`hpureHi`/
`dvd_classCount_hi` branch that no landed gate touches (`E57pCert.pure` is lin-only;
`E57pCert.dup`'s countermodel is lin-only too).

**File delivered:** `leanfinal/Uniformity/ChapE/E57ih.lean` (new; **PART 1 only** — N6's
section). Node `DEC1-N7` (assembly + firing `block_split_of_partitionLeg` at this row) is
a wave-2 sibling that will EXTEND this same file later; it is deliberately not attempted
here. N6's content is complete and self-verifying: the file compiles standalone as
delivered.

**Contents (namespace `Uniformity.Density.Ladder.E57iCert`):**
* `hiBlock : BlockData E57pCert.flatCarrier` — `Φ = X`, `F = X ^ 2 + X + 1`, `μ = 2`,
  `A := fun j => if j = 0 then 1 else if j = 1 then 1 else 0`, `T = 0`. Template
  `E57pCert.dupBlock` (`E57p.lean:633–659`), same shape, new content in three
  `F`-touching proofs: `hdev` (`A 0 = A 1 = 1`) by `simp [Finset.sum_range_succ]; ring`;
  `hdegA` by case-splitting `j < 2` (`rcases j with _ | _ | j`, `omega` on the
  out-of-range case — `interval_cases` is unavailable, its tactic import is not on this
  file's transitive import path, so the plan's suggested tactic name was swapped for the
  `rcases`/`omega` idiom `dupBlock.hdegA` itself already uses); `hkeyfree` via the integer
  Bézout witness `⟨1, -(X + 1)⟩` (`1·F + (-(X+1))·Φ = (X²+X+1) - (X+1)·X = 1`).
* `hiIface : RungInterface.{0,0,0} flatCarrier hiBlock` — `sides = {(1,1)}`, `len ≡ 2`,
  `linFac ≡ 0`, `hiFac ≡ {(2,1)}`, `rootCount ≡ 2`, `classCount ≡ 1`, `classCountHi ≡ 2`,
  `W = Unit`. All five hi-branch laws (`hresdeg`, `haccount`, `hnonempty`, `hforce`,
  `hexhaust`) verified — `hforce`'s hi bound `D·ℓ·deg = 1·1·2 = 2` is SATURATED by
  `classCountHi ≡ 2` (no slack, the inert shape).
* Closing `example` — the DEC1-N6 target's body, byte-copied from
  `leanfinal/scratch/DEC1_check.lean`'s `DEC1Check.N6_target` (scratch, not importable —
  this is the anti-drift transcription), discharged by
  `⟨hiBlock, hiIface, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩` — all eight conjuncts
  (`B.Φ = X`, `B.F = X^2+X+1`, `B.μ = 2`, `B.T = 0`, `I.sides = {(1,1)}`,
  `I.linFac (1,1) = 0`, `I.hiFac (1,1) = {(2,1)}`, `I.classCountHi (1,1) (2,1) = 2`) hold
  definitionally.

**Build:** `lake env lean Uniformity/ChapE/E57ih.lean` (from `leanfinal/`) — exit 0, zero
`sorry`, zero `axiom`, zero `unsafe`, zero warnings. `#print axioms` on both declarations:

```
'Uniformity.Density.Ladder.E57iCert.hiBlock' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Ladder.E57iCert.hiIface' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Lean-core only, as required.

**Statement fence / scope discipline:** no edits to `E57p.lean`, `leanspec/`, roll-ups,
or any other unit's files (`E57i1.lean`, `E57i2.lean`, `E57i.lean` untouched);
`E57ih.lean` is a new addition only, and only N6's section was written (N7's section is
left for its wave-2 owner to append). No C.63/C.69 clause consumed — per level-(a) of the
plan's bridge-levels split, the block/interface data is direct construction over the
landed flat carrier, citing no C-record axiom. No `git` operations performed.

**Status:** DEC1-N6 COMPLETE. Ready for `N7` to append the HI row's `PartitionLeg`
(`ah`, `hiLeg`) and firing to this same file, consuming `hiBlock`/`hiIface` as named
inputs alongside the landed `block_split_of_partitionLeg`, `PartitionLeg.dvd_classCount_hi`.
