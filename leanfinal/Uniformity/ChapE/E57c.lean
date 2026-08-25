/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E57p

/-!
# Uniformity.ChapE.E57c — `BlockSplitTarget`, E.57's schema node CLOSED

**Chapter E, NODE E.57 — unit E57C.** This file lands the leanfinal theorem twin of the
leanspec named target `LeanspecE.BlockSplitTarget`
(`leanspec/Leanspec/ChapE.lean:1338–1350`, amendment **A-E.7**, 2026-08-24) and discharges
it. Leanspec signs `BlockSplitTarget I` as the schema-level `Prop`

    ∀ hblocks hblocksHi (hpart : Nonempty (PartitionLeg I)), Nonempty (BlockSuite I)

and records it **NOT ASSERTED** there — leanspec is an interface contract, never a proof
site (its own header: *"Nothing here is proved"*). This file's job is exactly that
assertion, at the LANDED objects (`SlotCarrier`/`BlockData`/`RungInterface`/`PartitionLeg`/
`BlockSuite`, E.10–E.13/A-E.2/A-E.7, all in `Uniformity.ChapE.E57p`'s import closure).

## The shape check (binder-by-binder, against `block_split_of_partitionLeg`)

`Uniformity.ChapE.E57p`'s `block_split_of_partitionLeg` is

    theorem block_split_of_partitionLeg {O K} [...] {C B} (I : RungInterface C B)
        (hblocks : ∀ p ∈ I.sides, ∀ q ∈ I.linFac p,
          ∃ Fpq : Polynomial O, Fpq.Monic ∧ Fpq ∣ B.F ∧ Fpq.natDegree = I.classCount p q)
        (hblocksHi : ∀ p ∈ I.sides, ∀ q ∈ I.hiFac p,
          ∃ Fpq : Polynomial O, Fpq.Monic ∧ Fpq ∣ B.F ∧ Fpq.natDegree = I.classCountHi p q)
        (hpart : Nonempty (PartitionLeg I)) :
        Nonempty (BlockSuite I)

— binder names, binder types (down to the `Fpq`/`p`/`q` inner names) and the conclusion are
byte-identical to leanspec's `BlockSplitTarget`'s three `∀`-bound hypotheses and its
conclusion; E57p's own docstring records the binders as *"byte-preserved from the committed
signature"*. The leanspec `def` and this file's target differ ONLY in Lean's surface syntax
for currying an implication (`def … : Prop := ∀ hblocks hblocksHi hpart, …` vs. the
`theorem`'s binders moved before the `:`) — the ELABORATED TYPES coincide. **Byte-parallel:
this is a wrap, not a re-derivation** — `block_split_of_partitionLeg I` is already a term of
type `BlockSplitTarget I`, with no further tactic needed.

## Honest scope — what "closed" means here, and what it does not claim

This closes E.57's SCHEMA node (the ∀-over-`I` implication `BlockSplitTarget`) — it does
**not** assert that `PartitionLeg I` is inhabited for every `I` (A-E.6/A-E.7 machine-checked
that this would be FALSE at an untyped or ill-typed socket:
`verification/om4_resign_nontriviality.lean` Part 4, the `F = X²` countermodel, also
mirrored in `E57p.lean`'s `E57pCert.dup_partitionLeg_empty`). `BlockSplitTarget I` is a
genuine implication (`hpart : Nonempty (PartitionLeg I)` is a HYPOTHESIS, not a claim it
always holds), so `∀ I, BlockSplitTarget I` is true precisely because it is vacuous exactly
where the leg is empty and contentful exactly where it is not — and it is not vacuous
everywhere: the GC-13 bridge's two landed instance rows exercise the hypothesis firing
non-trivially — `Uniformity.ChapE.E57iCert.split_partitionLeg_nonempty`
(`Uniformity.ChapE.E57i`, the SPLIT row, `Nonempty (PartitionLeg mixIface)`, genuinely
multi-class) and `Uniformity.ChapE.E57iCert.hi_partitionLeg_nonempty`
(`Uniformity.ChapE.E57ih`, the HI row, `Nonempty (PartitionLeg hiIface)`, the hi-residual
branch) — both already firing `block_split_of_partitionLeg` end-to-end as
`split_blockSuite`/`hi_blockSuite`. Nothing in this file re-derives those; they are cited
here only as the non-vacuity witness for the schema closed below.

**Not attempted, by design (per the GC-13 bridge plan, `docs/in-progress/
GC13_BRIDGE_PLAN_2026-08-25.md` §2(b)):** the ARENA bridge — a functor from chapter C's
tower objects (`classSize_separable`, C.63) to a `PartitionLeg` at an ARBITRARY row — is a
genuinely missing object (no blueprint node signs it) and stays out of scope here, exactly
as it stayed out of scope for `E57p.lean` and the `E57i*`/`E57ih` instance nodes.

The declaration keeping the blueprint's own name `block_split` (the SIGNED node, taking
`hblocks`/`hblocksHi`/`hpart` as direct hypotheses rather than under the named target) is
left to whichever unit the orchestrator assigns it — this file deliberately does not take
that name, matching `E57p.lean`'s own discipline; what is landed here is the schema wrap
`BlockSplitTarget` plus its discharge.

DEPENDS: `Uniformity.ChapE.E57p` (`SlotCarrier`, `BlockData`, `RungInterface`,
`PartitionLeg`, `BlockSuite`, `block_split_of_partitionLeg`), transitively E.10–E.13, E.39a,
E.59.

SOURCE: `leanspec/Leanspec/ChapE.lean:1253–1351` (amendment A-E.7, the leanspec twin +
`BlockSplitTarget`); blueprint amendment A-E.6 (the re-sign this discharges).

## Status

Sorry-free, axiom-free, `unsafe`-free: every declaration reports at most the Lean-core
triple `{propext, Classical.choice, Quot.sound}` (census at end of file).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

-- E.12's three universes (A-E.1/E-D6), matching `E57p.lean`'s convention exactly: `uW`
-- occurs only inside `RungInterface`'s body, so anything quantifying over an interface
-- must name it.
universe uO uK uW

-- The three carrier-leg binders are byte-preserved from the committed signature and are
-- named but not referenced in the conclusion (they are consumed only by the DISCHARGE
-- below, via `block_split_of_partitionLeg`) — the linter is silenced exactly as leanspec's
-- own `BlockSplitTarget` and `E57p.lean`'s `block_split_of_partitionLeg` do.
set_option linter.unusedVariables false in
/-- **The leanfinal twin of `LeanspecE.BlockSplitTarget`** (A-E.7): E.57's full schema
content at the typed socket. Given the two carrier legs (`hblocks`, `hblocksHi`,
byte-preserved from the committed signature) and the typed partition leg
(`hpart : Nonempty (PartitionLeg I)`, GC-13's resolution), the full suite `BlockSuite I` is
nonempty. -/
def BlockSplitTarget {O : Type uO} [CommRing O] [IsDomain O] {K : Type uK} [Field K]
    {C : SlotCarrier O K} {B : BlockData C} (I : RungInterface.{uO, uK, uW} C B) : Prop :=
  ∀ (hblocks : ∀ p ∈ I.sides, ∀ q ∈ I.linFac p,
      ∃ Fpq : Polynomial O, Fpq.Monic ∧ Fpq ∣ B.F ∧
        Fpq.natDegree = I.classCount p q)
    (hblocksHi : ∀ p ∈ I.sides, ∀ q ∈ I.hiFac p,
      ∃ Fpq : Polynomial O, Fpq.Monic ∧ Fpq ∣ B.F ∧
        Fpq.natDegree = I.classCountHi p q)
    (hpart : Nonempty (PartitionLeg I)),
    Nonempty (BlockSuite I)

/-- **E.57's schema node, CLOSED**: `BlockSplitTarget` holds at every trigger interface —
exactly `block_split_of_partitionLeg`, re-packaged under the named target `Prop`. The
elaborated types coincide (see the file docstring's shape check), so the wrap is the proof
term with no tactic content. -/
theorem blockSplitTarget_holds {O : Type uO} [CommRing O] [IsDomain O] {K : Type uK}
    [Field K] {C : SlotCarrier O K} {B : BlockData C} (I : RungInterface.{uO, uK, uW} C B) :
    BlockSplitTarget I :=
  block_split_of_partitionLeg I

/-- **The blueprint's designated landing name** (E.57's leanspec docstring: "the landing
declaration keeps the blueprint name `block_split` and may be asserted only after GC-13
types `hpart`" — GC-13 typed it at A-E.7; asserted here). [orchestrator, 2026-08-25] -/
theorem block_split {O : Type uO} [CommRing O] [IsDomain O] {K : Type uK}
    [Field K] {C : SlotCarrier O K} {B : BlockData C} (I : RungInterface.{uO, uK, uW} C B) :
    BlockSplitTarget I :=
  blockSplitTarget_holds I

end Uniformity.Density.Ladder

/-! ## Axiom footprint (Lean core only — no repo axiom, no stub axiom enters) -/

section AxCheck

#print axioms Uniformity.Density.Ladder.BlockSplitTarget
#print axioms Uniformity.Density.Ladder.blockSplitTarget_holds
#print axioms Uniformity.Density.Ladder.block_split

end AxCheck
