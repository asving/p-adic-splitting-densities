/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/

/-!
# Uniformity.ChapD.D64 — OPEN-CALL and orphan routing: chapter D's residual-obligation table

**Chapter D, NODE D.64** [record] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §9; amendments
A-1, A-D.1 govern — A-1 is what renumbered this record from its pre-composition ID `D.69`, and
A-D.1's Rider R-2 records that some §§0–1 prose still cites the old numbers). ENVIRONMENT: n/a.

**NO Lean declaration, by signature.** The blueprint signs this node as `SIGNATURE. none`,
`DEPENDS. n/a`, `PROOF. n/a`, `SIZE. 0 Lean lines`, and A-D.1's closing paragraph confirms it:
"the five GC-13 interface nodes and the two `record` nodes still declare nothing". The artifact
IS the table below — one row per surviving open item of the four T-specs, each routed. This
file is the landed copy so that the routing survives in the repo next to the chapter's
mathematics; it deliberately imports nothing and defines nothing, so it can never become a
silent dependency of a proof.

## The routing table (transcribed from the blueprint's §9 record)

| item | content | routing |
|---|---|---|
| T1 OPEN-CALL 1 (`(H-JA-CONJ)_i` source designation) | the JA supplier for letter monomiality | inline hypothesis at D.20's consumers; designation resolution FOR-0d — chapter I gate (b) if cited as literature |
| T1 OPEN-CALL 2 (`(H-JA-RES-CONJ)` source) | the conjugation supplier | inline at D.23; same routing |
| T1 OPEN-CALL 3 (`(H-GENHN-CLEAR)` source) | the clearance supplier | NO D node (D-H4(5)); consumers in C |
| T1 OPEN-CALL 4 = T3 OPEN-CALL 1 (**NEEDS ASVIN**) | "the surrounding tower correctness theorem" converting residual factor patterns to p-adic splitting types — unnamed in both notes; "Assigning a source or formal interface would be invention" | **chapter I / the 0d trust boundary** (owner gate (b) — a literature cite if one exists); D and E consume factor-pattern statements only, never splitting types, until it lands |
| T1 OPEN-CALL 5 (level-general residual-read supplier) | the `i ≥ 3` read bundle | D.29-instantiation obligation = `[GENTOW5-W(i)]`/HVR stack (D.44/D.62); C's spans |
| T3 deferred obligation 1 (GENTOW5 §S2 perimeter, XREF X18 `PERIMETER-UNRESOLVED`) | the five-fold certified package's fine designations | `EFF.GENTOW5 [supplied-by: chapter C]` — C's DEPENDS re-home it |
| T3 deferred obligation 2 (the outer `ψ₁` statement) | unnamed source theorem | `[supplied-by: chapter C]` if GENTOW5's spec exposes it; else I ledger |
| T3 deferred obligation 3 (ABS-G5W consumption check + dated append) | protocol action | ORCHESTRATOR item (not mathematical) |
| T5 OPEN-CALL 1 / `HYP.99` (two-clause staleness) | note-owner repair | recorded at D.61(4); NOT executed |
| WFRAME OPEN-2 (`ω₁ = w₁?`), OPEN-3/`HYP.66` (avatar) | open identifications | I ledger rows; D.59/D.61 fence them |
| `JD0-BOX-2` | zero T-unit cites (D-H8's grep) | **chapter I**, named hypothesis (`HYP.39`) |
| `HYP.01`/`HYP.12` escalations | trust-boundary naming from T3/T1 open calls | **chapter I** core-set (`HYP.98`); NO D node (Brief D trap (iii)) |
| T3 `(T3-JOINT-OPEN)` | a realized p-adic B″ frame with `Θ ≠ 1 ∧ w ≠ 1` simultaneously — "a machine-coverage gap, not a proof gap" | gate D.67 carries the record; coverage stays open |

## Three reading notes the landed copy must carry

1. **Nothing in this table is discharged by chapter D.** Every row is an obligation that leaves
   the chapter — to chapter C (as a GC-13 `[supplied-by: chapter C]` placeholder), to chapter I
   (as a named hypothesis or a 0d trust-boundary item), or to the orchestrator (as a protocol
   action). A fleet agent who finds a chapter-D node that appears to prove one of these rows has
   found a defect, not a discharge.
2. **Row 4 is the load-bearing one.** The surrounding tower correctness theorem — residual
   factor patterns ⇒ p-adic splitting types — is unnamed in both T1 and T3, and both notes
   record that assigning it a source or a formal interface "would be invention". Chapter D's
   transport package (D.34a/b/c) therefore stops at factor data: `wtwist` transports
   monicity, degree, constant term, irreducibility, separability, roots and factor
   multiplicities, and asserts nothing whatever about splitting types. The same fence is
   repeated in each of those files' docstrings, at the node's own instruction.
3. **The D.62 reference in row 5 is governed by A-D.2 / DECISION D-2**, not by the text quoted
   above: the stage-0e gate refuted the committed existential form of the
   `(H-VARTHETA-RES)_i` carrier as VACUOUS (defect D-D12, machine-checked), and the Display-A
   carrier adjudication unit re-signed D.62/D.63 as the sitewise ambient-residue clause (Lean
   side landed at commit `d420f112`; the committed form is retained, named and voided, as
   `HVarthetaResVoided`). This record cites the row's ID only; it makes no strength claim about
   the carrier, and no consumer may read one out of this file.

**SOURCE.** `EFF-T1.md` §8 (OPEN-CALLs 1–5 + FOR-0d routing); `EFF-T3.md` §8–§9 (deferred
obligations + OPEN-CALL 1); `EFF-T5.md` §8–§9 + `HYP.63/.66/.99/.100`; `EFF.T3.30`.

**TEETH.** n/a (a routing table). §13 asks the codex cross-read to verify that the table is
EXHAUSTIVE against the four specs' self-audit sections — that read is **OWED**, and this landed
copy does not discharge it.

## Status

No declarations, hence nothing to check: no `sorry`, no `axiom`, no import, and no axiom
footprint block (there is no name to print). The file elaborates as pure documentation.
-/
