# Verdict: DEC1-N7 (GC-13 bridge plan, node N7, part 2 of `E57ih.lean`)

**Plan:** `docs/in-progress/GC13_BRIDGE_PLAN_2026-08-25.md` §3, node `DEC1-N7` — assembly +
firing `block_split_of_partitionLeg` at the HI row. Consumes N6's `hiBlock`/`hiIface`
(`F = X² + X + 1`, one side `(1,1)`, one higher residual class `(deg,mult) = (2,1)`, no
linear residual) and the landed `PartitionLeg`/`block_split_of_partitionLeg`/
`PartitionLeg.dvd_classCount_hi` (`Uniformity/ChapE/E57p.lean`).

**File extended:** `leanfinal/Uniformity/ChapE/E57ih.lean` (N6's section left byte-untouched
— verified via `git diff`: the only changes are pure line **insertions** after N6's closing
example and before `end E57iCert`, plus three new `#print axioms` lines appended after N6's
two existing ones; zero lines of N6's original content removed or altered).

**Contents added (namespace `Uniformity.Density.Ladder.E57iCert`):**
* `ah : ClassIx ℚ := ((1,1), Sum.inr (2,1))` — the HI row's sole class address.
* `hiLeg : PartitionLeg hiIface` — the one-class residue: `cls = {ah}`,
  `blk := fun _ => ⟨hiBlock, hiIface⟩` (the honest E39a-style residue — an inert row's
  single block IS the row, same idiom as `E57pCert.pureLeg` but on the hi branch instead
  of the lin branch). All eleven `PartitionLeg` fields discharged:
  - `hclsLin`/`hclsHi`: `simp [ah, hiIface]` (both sides of each iff reduce to the same
    equality since `hiFac`/`sides` are constant singletons and `ah`'s tag is `Sum.inr`).
  - `hprod`: `Finset.prod_singleton` via `simp`.
  - `hdisj`: vacuous (singleton `cls`), same `absurd (hc.trans hc'.symm) hne` idiom as
    `pureLeg`.
  - `hdeg`: the genuinely new content — `(hiBlock.natDegree_F).1 : hiBlock.F.natDegree =
    hiBlock.μ * flatCarrier.D` (`= 2 * 1`) closes `(X²+X+1).natDegree = 2` via
    `simpa [hiBlock, flatCarrier]`, avoiding `compute_degree` per the plan's routing note.
  - `hone`, `hthr`: `rfl` (both project through to `hiIface`/`hiBlock`'s own fields).
  - `hpureLin`: vacuous (`ah`'s tag is `Sum.inr`, so no `Sum.inl` address is ever in
    `cls`) — `simp [ah] at h`.
  - `hpureHi`: witness `k = 1`; `2 ≤ q.1` closes by `le_rfl` once `q = (2,1)` is
    extracted from membership in `{ah}`.
* `hi_partitionLeg_nonempty : Nonempty (PartitionLeg hiIface) := ⟨hiLeg⟩` — the typed
  `hpart` socket discharged at the HI row.
* `hi_blockSuite : Nonempty (BlockSuite hiIface)` — fired via
  `block_split_of_partitionLeg hiIface hiLeg.supplies_hblocks hiLeg.supplies_hblocksHi
  ⟨hiLeg⟩`.
* Teeth: `example : (1*1*2 : ℕ) ∣ hiIface.classCountHi (1,1) (2,1) :=
  hiLeg.dvd_classCount_hi (1,1) (by simp [hiIface]) (2,1) (by simp [hiIface])` — the E-D15
  hi divisibility consumed NON-TRIVIALLY at this row (`2 ∣ 2` read through the leg's own
  arithmetic — `hforce`'s hi lower bound `D·ℓ·deg = 1·1·2 = 2` is saturated here, no slack
  — not discharged by `norm_num` on a free-standing numeral).
* Closing `example` — the DEC1-N7 target's body, byte-copied from
  `leanfinal/scratch/DEC1_check.lean`'s `DEC1Check.N7_target`, discharged by
  `⟨hiBlock, hiIface, rfl, rfl, rfl, hi_partitionLeg_nonempty, hi_blockSuite⟩`.

**Build:** `lake env lean Uniformity/ChapE/E57ih.lean` (from `leanfinal/`) — exit 0, zero
`sorry`, zero `axiom`, zero `unsafe`. Also ran `lake build Uniformity.ChapE.E57ih` (per
task instructions, in place of a bare `lake build`) — 1371/1371 jobs, "Build completed
successfully"; the only diagnostic is a pre-existing-style `linter.style.show` info/warning
on the `show (X^2+X+1 : Polynomial ℤ).natDegree = 2` line inside `hdeg` (identical warning
class already present, unmodified, at `E57p.lean:640` and `:645` in the landed template
`pureBlock`/`dupBlock` — not a new problem, not sorry/axiom/unsafe). `#print axioms` on all
five declarations in the file (N6's two plus N7's three):

```
'Uniformity.Density.Ladder.E57iCert.hiBlock' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Ladder.E57iCert.hiIface' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Ladder.E57iCert.hiLeg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Ladder.E57iCert.hi_partitionLeg_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Ladder.E57iCert.hi_blockSuite' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Lean-core only, as required.

**Statement fence / scope discipline:** no edits to `E57p.lean`, `leanspec/`, roll-ups, or
any sibling unit's files (`E57i1.lean`, `E57i2.lean`, `E57i.lean` — N34's `E57i.lean`
untouched); `E57ih.lean` is the only file touched, N6's section is byte-untouched (verified
by `git diff`: 78 insertions, 0 deletions). No C.63/C.69 clause consumed — level-(a) of the
plan's bridge-levels split: the leg's fields are direct construction over the landed
`hiBlock`/`hiIface`, citing no C-record axiom. No `git` operations performed (no add/commit).

**Status:** DEC1-N7 COMPLETE. The HI row's `hpart` socket is now discharged
(`Nonempty (PartitionLeg hiIface)`) and the E.57 assembly fires end-to-end at the inert
shape; the E-D15 hi divisibility (`dvd_classCount_hi`) is exercised non-trivially for the
first time in the campaign. Together with N6, `E57ih.lean` is now complete and
self-contained (imports only `Uniformity.ChapE.E57p`). Remaining plan nodes N3/N4/N5
(the split row's assembly, in `E57i.lean`) are separate units, not touched here.
