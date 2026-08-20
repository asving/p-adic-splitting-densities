/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.LocalData

/-!
# Uniformity.ChapI.I01 — `NS7(O)`, the OM-termination carrier — **STATEMENT CARRIER**

**Chapter I, NODE I.01** [def] [fresh] (`blueprint/CHAP-I_capstone_conditionality.md` §4,
`### NODE I.01`; SIGNED twin `leanspec/Leanspec/ChapI.lean`, the `### NODE I.01` block,
lines 403–426).  **ENV-I1**.

**Chapter I's statements ARE signed.**  `leanspec/Leanspec/ChapI.lean` exists (100 808 bytes,
2026-08-16, wrapper `namespace LeanspecI`) and carries a signature block for every one of the
25 blueprint nodes.  This file transcribes I.01's signature BYTE-FROZEN from that file: the
declaration name, the bundle quantifier, the binder order and the `Prop` kind are the
leanspec's, re-namespaced only (`LeanspecI` → `Uniformity.Density`, which is GC-6.2's
assignment: chapter I gets no sub-namespace).

## ⚠ DISPOSITION — READ THIS FIRST

`NS7Termination` is a **statement carrier** (A-C.8.5: *"the signing unit must use statement
carriers, never temporary axioms"*), and it is carried at its **STUB-STAGE SIGNED BODY**, which
is the literal placeholder `True`.

* **Nothing is asserted and nothing is proved here.**  No axiom is declared, no cite is
  imported, no capstone statement is asserted.
* **OWNER-GATED (gate (b), a literature cite).**  I.01's mathematical content — OM descent
  terminates over every complete DVR with finite residue field — is Display A line 1, ledger
  row `HYP.15`, and its intended discharge is chapter C's gate-(b) cite **C.94**
  ([AGNPRW] Thm 5.6, published; the repo's "Thm 5.2" is the arXiv-v1 number, A-3 audit §3).
  That cite is **NOT signed** and this unit may not sign it.  The live target is
  `LeanspecC.NS7TerminationStatementR` (landed as a carrier at
  `Uniformity/ChapC/C94.lean:109`, `NS7TerminationStatementR`), **awaiting the owner's
  gate-(b) signature**.  On signature this carrier becomes cite-conditional and visible to
  `#print axioms` (gate I.25).
* **THE PUBLISHED RESOLUTION ROUTE IS REFUTED (blueprint defect I-D6).**  The 2026-08-16 A-C.1
  addendum instruction to resolve this body against `NS7TerminationStatement` is UNSAFE: that
  statement proves `False` (`Uniformity/ChapC/C94_REFUTATION.lean.txt:124`) and was STRUCK at
  A-C.6.  **No resolution pass may type I.01's body against it.**  A-I.1 re-pointed the
  instruction at the A-C.6 REDRAFT.

## MANDATORY BINDER-VACUITY AUDIT (A-C.8.4 checklist; verdict committed before any proving)

Two distinct questions, answered separately, because conflating them is how a fiction gets into
the capstone's stated dependencies.

**(1) The guard binders — NOT vacuous, and they restrict nothing they should not.**  The five
instance binders `[CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
[IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]` are the repo's standard
complete-DVR bundle, verbatim as `Uniformity.Density.DrainageAt` (`Density/Statement.lean:118`)
and `TotalMassOne` (`Density/Statement.lean:163`) spell it.  The bundle is **inhabited**:
`ℤ_[p]` is a landed instance of it (`Density/LocalData.lean` §6, "`ℤ_[p]` is an instance of the
bundle", `instance : Finite (ResidueField ℤ_[p])`), so this is the A-C.8.4 row *"provably
satisfiable — restricts the intended class and no more"*, not the C.113 `hne`-shape defect.
Against the four A-C.7 registry shapes: no unpinned carrier field (C.111), **no self-loop and
no quantified relation or descent history at all** (C.94's own failure shape — note that this
is precisely the node whose intended cite the C.94 self-loop refutation struck, so the check
is not idle), no `Nonempty`-only hypothesis (C.113), and no implication-guarded `≠ ⊤` /
visibility window (C.118).

**(2) The CONCLUSION is the placeholder `True`, so the carrier as signed is PROVABLE and
carries NO mathematical content.**  This is the honest, load-bearing finding of this node and
it must not be read as a defect of the transcription: it is the signed stage-0e state
(blueprint defect **I-D12**, *"six SIGNED bodies are the literal placeholder `True`"* — I.01,
I.05, I.06, I.07, I.21 and one more).  `NS7Termination` is closed by `fun _ => trivial`; the
leanspec's own §4 gate executes exactly that (`example : NS7Termination := fun _ => trivial`,
`leanspec/Leanspec/ChapI.lean:943`).  Consequences, stated so no consumer can be misled:

* **A hypothesis of this `Prop` buys a consumer nothing today.**  Any node discharging an
  obligation by assuming `NS7Termination` has discharged nothing.  The name is a *label for a
  future obligation*, reserved at frozen signature so that the field list of the capstone
  hypothesis structure is fixed before the bodies land.
* **It is therefore NOT a vacuity defect in the A-C.7 sense** (a guard no instance satisfies,
  which would make a conditionality clause a fiction by being unsatisfiable).  It is the exact
  opposite failure mode — a clause satisfied by everything — and it is disclosed, not hidden:
  FROZEN here are **the name, the bundle quantifier and the `Prop` kind**, and nothing else.
* **What the real body will say** (from the signed docstring, unchanged): it quantifies over
  chapter C's descent-history type and asserts finiteness.  Typing it is the resolution pass's
  job and is blocked on the owner's C.94 signature (above).

**Verdict: NON-VACUOUS BINDERS · CONTENT-FREE CONCLUSION (signed placeholder, I-D12) ·
OWNER-GATED at gate (b) · no fifth A-C.7 instance.**

## Definitional choices made here (flagged for human review, per the trust boundary)

1. **Namespace.** `Uniformity.Density`, flat — GC-6.2 gives chapter I no sub-namespace.  The
   leanspec's `LeanspecI` wrapper is dropped, which is the documented landed-side assignment.
2. **Import.** `Uniformity.Density.LocalData` only, rather than ENV-I1's nominal
   `import Uniformity`.  Reason: the leanspec header records defect **I-D1** — importing the
   `Uniformity.ChapD` roll-up together with the chapter-E deep-twist branch is a hard Lean
   error at HEAD.  Per-node minimal imports avoid inheriting that break; `LocalData` supplies
   the bundle idioms and `Mathlib`.  This is an import choice only: **the statement is
   byte-identical to the signed one.**
3. **Nothing else.**  No gate `example`, no `#check` suite, no witness: the coordinator's
   narrow charge for this file is preamble + frozen statement + verdict.  The triviality
   witness quoted in audit item (2) is cited by leanspec line number, not re-executed here.
-/

namespace Uniformity.Density

open IsLocalRing Polynomial

/-- `NS7(O)` (Display A line 1; ledger HYP.15, CARRY-as-CITE): OM descent terminates over every
complete DVR with finite residue field. Discharged by chapter C's gate-(b) cite C.94 ([AGNPRW]
**Thm 5.6**, published — the repo's "Thm 5.2" is the arXiv-v1 number, A-3 audit §3) once signed;
carried as a named `Prop` until then.

⚠ STUB-STAGE BODY (BLOCKED-UNTIL-RESOLUTION): the real body quantifies over chapter C's
descent-history type and asserts finiteness. FROZEN HERE: the name, the bundle quantifier, the
`Prop` kind. **Do not resolve it against `NS7TerminationStatement` (refuted) — see I-D6.** -/
def NS7Termination : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
    True

end Uniformity.Density

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only -/

#print axioms Uniformity.Density.NS7Termination
