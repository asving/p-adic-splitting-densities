# Unit E57C verdict — the two E-chapter closures attempted after the GC-13 bridge (N1–N7)

## Task 1 — `BlockSplitTarget`: LANDED, PROVED (wrap)

**File:** `leanfinal/Uniformity/ChapE/E57c.lean` (new).

Read leanspec's exact current shape first
(`leanspec/Leanspec/ChapE.lean:1338–1350`, amendment A-E.7):

```lean
def BlockSplitTarget {O : Type uO} [CommRing O] [IsDomain O] {K : Type uK} [Field K]
    {C : SlotCarrier O K} {B : BlockData C} (I : RungInterface.{uO, uK, uW} C B) : Prop :=
  ∀ (hblocks : ∀ p ∈ I.sides, ∀ q ∈ I.linFac p,
      ∃ Fpq : Polynomial O, Fpq.Monic ∧ Fpq ∣ B.F ∧ Fpq.natDegree = I.classCount p q)
    (hblocksHi : ∀ p ∈ I.sides, ∀ q ∈ I.hiFac p,
      ∃ Fpq : Polynomial O, Fpq.Monic ∧ Fpq ∣ B.F ∧ Fpq.natDegree = I.classCountHi p q)
    (hpart : Nonempty (PartitionLeg I)),
    Nonempty (BlockSuite I)
```

Compared against `Uniformity.ChapE.E57p`'s landed `block_split_of_partitionLeg` (already
PROVED there): binder names, binder types (down to inner `p`/`q`/`Fpq` names) and the
conclusion are **byte-parallel** — the two declarations differ only in surface syntax for
currying an implication (`def … : Prop := ∀ hblocks hblocksHi hpart, …` vs. the theorem's
binders moved before the `:`). The elaborated types coincide, so this is a **wrap, not a
re-derivation**.

Landed: `def BlockSplitTarget` (the leanfinal twin, in `Uniformity.Density.Ladder`, using
the LANDED `SlotCarrier`/`BlockData`/`RungInterface`/`PartitionLeg`/`BlockSuite`) and
`theorem blockSplitTarget_holds (I) : BlockSplitTarget I := block_split_of_partitionLeg I`.
This closes E.57's schema node: `BlockSplitTarget` holds at every trigger interface `I`,
unconditionally.

**Honest scope, stated in the file:** this does not assert `PartitionLeg I` is inhabited in
general (A-E.6/A-E.7 machine-checked that it is FALSE at the untyped/ill-typed socket —
`verification/om4_resign_nontriviality.lean` Part 4, mirrored by `E57p.lean`'s
`E57pCert.dup_partitionLeg_empty`); `BlockSplitTarget I` is a genuine implication, true
because it is vacuous exactly where the leg is empty. Non-vacuity elsewhere is exhibited by
the already-landed GC-13 bridge rows `Uniformity.ChapE.E57iCert.split_partitionLeg_nonempty`
(SPLIT row, multi-class) and `Uniformity.ChapE.E57iCert.hi_partitionLeg_nonempty` (HI row,
hi-residual), both firing `block_split_of_partitionLeg` end-to-end already
(`split_blockSuite`/`hi_blockSuite`) — cited in the docstring, not re-derived.

**Naming decision (recorded, not adjudicated here):** the file deliberately does NOT
declare the bare blueprint name `block_split` (E57p's own discipline: *"the declaration
keeping the blueprint name `block_split` is GC-13's; this file deliberately does not take
it"*). `rg '\bblock_split\b' leanfinal/ leanspec/` shows the name is still unclaimed in any
`.lean` file — only mentioned in comments/notes. That naming call is left to the
orchestrator.

**Verification:**
- `lake build Uniformity.ChapE.E57i Uniformity.ChapE.E57ih` — exit 0 (prerequisite gate,
  both rows fire `block_split_of_partitionLeg`, Lean-core only).
- `lake env lean Uniformity/ChapE/E57c.lean` — exit 0, zero warnings after silencing the
  (leanspec-matching) `unusedVariables` linter on the target `def`'s carrier-leg binders.
- `lake build Uniformity.ChapE.E57c` — exit 0 (1371 jobs).
- `#print axioms`: both `BlockSplitTarget` and `blockSplitTarget_holds` report exactly
  `[propext, Classical.choice, Quot.sound]`.
- `grep -n 'sorry\|^axiom\|unsafe' E57c.lean` — no hits outside the docstring's prose.

## Task 2 — `peel_row_law` (E.51): BLOCKED (unchanged; block deepened since the RESCHEDULE)

Read `leanspec/Leanspec/ChapE.lean:1121–1130` (still `hpeel : True`, still marked
`BLOCKED: GC-13 resolution`, still "A fleet agent must NOT prove E.51 while the placeholder
is `True`") and the landed `leanfinal/Uniformity/ChapE/E51.lean`, which already exists and
already does everything honestly landable:

- `peel_row_arith`, `peel_row_arith_of_shadow` — the full ℕ-arithmetic content of the node.
- `PeelRowLawFrozen`/`PeelRowLawArith` (statement carriers) +
  `peelRowLawFrozen_iff_arith` — the defect certificate: the frozen signed type is
  EQUIVALENT to bare arithmetic (`hpeel : True` and the redundant `hforce4` carry nothing).
- The file's own header: *"The GC-13 resolution pre-check was re-run at this commit and
  still fails … The signed `peel_row_law` remains OPEN."*

**Re-ran the pre-check at this unit's commit (2026-08-25).** The GC-13 bridge that landed
(N1–N7, `E57i.lean`/`E57ih.lean`) resolved E.57's socket only — the bridge plan says so
explicitly (`docs/in-progress/GC13_BRIDGE_PLAN_2026-08-25.md` §"After landing", item 4):
*"E.51's `hpeel : True` is the OTHER GC-13 socket — same treatment, separate decomposition:
it needs a typed `PeelLeg` against E.37 `peel_once` (landed) with the HE6R1-3 emission
record as the C-side carrier … Not planned here."* No `PeelLeg`-shaped object exists
anywhere in `leanspec` or `leanfinal`.

The named C-side supplier is chapter C's NODE C.40 `level2_peel` (LEMMA HE6R1-3). It is now
**more precisely blocked** than at the 2026-08-16 RESCHEDULE, not less:

- `leanfinal/Uniformity/ChapC/C40.lean` exists but deliberately does **not** declare
  `level2_peel` (its header: *"PARTIAL: BLOCKED"*). Clause (ii) needs C.61 `tier1_typeOf`
  at *general* `L.ℓ`; `leanfinal/Uniformity/ChapC/C61.lean` now exists but is itself
  **"BLOCKED at general `L.ℓ`; PROVED UNCONDITIONALLY at `L.ℓ = 1`"** only — the general
  case needs two further nodes (C.59/C.27) not landed.
- Clause (iii) needs `mult₂`/`blockFactor` (C.35, landed) to agree with `HasLabel`'s own
  multiplicity, which `leanfinal/Uniformity/ChapC/C35b.lean` machine-REFUTES as stated
  (`hasLabel_natDegree_dvd_false`, a genuine ℤ_[2] counterexample) — settled as inseparable
  from C.34's within-slope maximality refinement (`C35B_D13_REFUTED_2026-08-20.md`), which
  is not landed either.

So even the direct C-side supplier `level2_peel` cannot be asserted yet, let alone the
`PeelLeg`-style typed carrier the bridge plan names as the genuinely missing arena object
for E.51. **Verdict: BLOCKED**, on (a) the undesigned `PeelLeg` arena bridge (no blueprint
node signs it, per the GC-13 bridge plan) and (b) transitively on chapter C's own open
nodes — C.61 at general `L.ℓ` (behind C.59/C.27) and C.40 clause (iii) (behind C.34's
maximality refinement). Nothing was touched in chapter C or in `E51.lean`; no new file was
added for this task (the honest landing already exists).

## Rules compliance

No `sorry`, no new axiom, no `unsafe`. Every name checked against the actual source
(`rg`/`Read`), not memory. `leanspec/`, roll-ups, and other units' files untouched — only
`leanfinal/Uniformity/ChapE/E57c.lean` (new) and this verdict were written. No git commit
made.
