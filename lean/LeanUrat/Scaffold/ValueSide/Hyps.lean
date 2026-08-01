/-
BP_IV §1.0 — the independent named [M] hypothesis rows (`Hyps.lean`).
Units landed in this file so far: H2a (`AssembledPack` + installed `Fintype`) ·
H2b (`PackReference`/`PackCorrespondence`) · H3 (`K3DeltaRow`) ·
H4 (PARTIAL — see the H4 import block below for the per-row ledger).
-/
import Mathlib
import LeanUrat.MovesU.Defs
-- H2b: `UCarriers` lives in `LeanUrat/MovesU/DefsCarriers.lean` (used AS IS).
import LeanUrat.MovesU.DefsCarriers
-- SKEL (§1.0 import graph `CensusCore → Hyps → Census`): the CensusCore edge,
-- carrying the re-export path for `ADMFull` (unit H1 lands it in CensusCore).
import LeanUrat.Scaffold.ValueSide.CensusCore
/- **Unit H4** (BP_IV §1.0 owner table + §5 seams): imports of the ACTUAL
BP_III/BP_V owner row modules — no local declarations, no Prop aliases
(BP_IV audit finding 8: owner structures are compile-time prerequisites).

LANDED owner module (compiles green, `lake build LeanUrat.Scaffold.DictIII.Hyps`):
`Scaffold/DictIII/Hyps.lean` (BP_III §1.3, the dictionary hypothesis rows) —
carries the actual datum-indexed rows
  `LeanUrat.Scaffold.DictIII.GRB`   = (GR-B) orders ≥ 2 (consumed at C5/S5/D4),
  `LeanUrat.Scaffold.DictIII.FRESH` = (FRESH)           (consumed at C5'/S5/D4). -/
import LeanUrat.Scaffold.DictIII.Hyps
-- H4 ledger, REVISION-3 disposition (mop-up adjudication, 2026-08-01; full
-- record: `blueprints/BP_IV.md` REVISION 3).  The remaining §1.0-table owner
-- rows have NO landed owner modules — AND their owner blueprints never
-- charter them at ANY signature (grep of BP_III.md/BP_V.md: zero hits for
-- R1R4Row/TerminalSeamRows/ThmERow/D15Row/K-LOC/GRBRow/FreshRow — a
-- cross-blueprint SEAM FAILURE escalated to the orchestrator).  Since no
-- owner declaration can be awaited, the REVISION-3 ruling replaces "wait"
-- with the sanctioned K3DeltaRow OPAQUE-PARAMETER pattern wherever the
-- consumer's PROOF does not need the row's content (the row is a rider of
-- the honest-conditionality display):
--  · (R1)–(R4) = (H4a) `R1R4Row` (owner BP_V) — consumed at S5b/D4 as the
--    opaque parameter `{R1R4Row : ClassifierSpec n p → Prop}` + binder.
--  · (H6) `TerminalSeamRows` (owner BP_III, CU-2t) — likewise, keyed at F.
--  · (GR-B)/(FRESH) census-keyed forms (owner BP_III) — opaque parameters
--    `{GRBRow FreshRow : CensusData → Prop}` of `CensusValueRows` (see
--    `Census.lean` REVISION-3 C5 block) and of S5b/D4.
--  · K-LOC/(I-τ) (owner BP_III) — opaque Prop parameters of K11's
--    `EngineSIBRow` (`KCount.lean`).
--  When BP_III/BP_V land the real rows they INSTANTIATE these parameters —
--  no re-key of any BP_IV statement.
--  · D-15 / O5triple Thm E rows (`ThmERow`/`D15Row`) — the ONE consumer
--    whose PROOF needs the rows' CONTENT (M7's two-row transport), so the
--    opaque pattern does NOT apply; M7 stays owner-blocked (see
--    `MassId.lean` header).  Its BP_IV-owned event carriers `CylEvent` /
--    `IsContinuationEvent` are landed at the END of this file, so M7
--    elaborates the moment BP_III lands the rows.

/-!
# Value-side named [M] rows [BP_IV division, unit H2a]

**PROVENANCE (unit H2a; BP_IV §1.0).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.0 (statement transcribed VERBATIM).
* Math source of record: ROOT §3.1 (PACK).
* Definition only: the finite assembled-pack table carrier with its `Fintype`
  instance installed and one-based block bounds.  The (PACK) correspondence
  itself is unit H2b (`PackReference`/`PackCorrespondence`), which consumes
  this carrier — no law is smuggled here.
-/

namespace LeanUrat.Scaffold.ValueSide

/-- **(PACK)** = (ROOT-C)(H5) (ROOT §3.1, REVISION 4 finding VC4-3): the CONCRETE
assembled pack equals the intended 𝔅_n instantiation ENTRY-FOR-ENTRY (D-11's
OPEN clause 4 = OL-O12-2's data half).  `AssembledPack` is the finite table
carrier (fields below); `intendedEntry` is the 𝔅_n reference read off the
`UCarriers` chain.  No proof of this row exists anywhere; Steps 18/18b consume
Step 17 AS this correspondence. -/
structure AssembledPack (n : ℕ) where
  Row : Type
  instR : Fintype Row
  entry : Row → RatFunc ℚ
  blockOf : Row → ℕ
  blockOf_pos : ∀ r, 1 ≤ blockOf r
  blockOf_le : ∀ r, blockOf r ≤ n

attribute [instance] AssembledPack.instR

/-! **PROVENANCE (unit H2b; BP_IV §1.0, unit table §2 row H2b).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.0 (statements transcribed VERBATIM).
* Math source of record: ROOT §3.1 (PACK); D11 r3 §5 clause 4.
* Dep H2a: consumes the `AssembledPack` carrier above.  `UCarriers` is imported
  from `LeanUrat/MovesU/DefsCarriers.lean` (used AS IS, per BP_IV §0).
* `PackCorrespondence` is a named [M] row (no proof of this row exists anywhere;
  Steps 18/18b consume Step 17 AS this correspondence) — never an axiom, never
  discharged by fiat.  `C` and `P` are scoped dependently (§4 note 9). -/

open LeanUrat.MovesU in
/-- The independently typed reference table read from `C`; unit H2 supplies the
actual reader without mentioning an out-of-scope pack variable. -/
structure PackReference (n : ℕ) (C : UCarriers n) (P : AssembledPack n) where
  intendedEntry : P.Row → RatFunc ℚ
  intendedBlock : P.Row → ℕ
  intendedBlock_pos : ∀ r, 1 ≤ intendedBlock r
  intendedBlock_le : ∀ r, intendedBlock r ≤ n

open LeanUrat.MovesU in
structure PackCorrespondence (n : ℕ) (C : UCarriers n) (P : AssembledPack n)
    (R : PackReference n C P) : Prop where
  entry_eq : ∀ r : P.Row, P.entry r = R.intendedEntry r
  block_eq : ∀ r : P.Row, P.blockOf r = R.intendedBlock r

/-! **PROVENANCE (unit H3; BP_IV §1.0, unit table §2 row H3).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.0 (statement transcribed VERBATIM).
* Math source of record: ROOT §3.1 (UB-X)(b)/(K3-δ) (REVISION 4 finding VC4-1).
* Corpus import: `RegData` from `LeanUrat/MovesU/Defs.lean` (used AS IS, per
  BP_IV §0 — existing corpus types are never redefined).
* `DeltaStablePos` is OWNED by Movement V (BP_V, O-8b/UB) — consumed as an
  opaque predicate parameter (`ℕ → Prop`), never aliased or defined here. -/

open LeanUrat.MovesU in
/-- **(K3-δ)** (ROOT §3.1 (UB-X)(b) restricted; REVISION 4 finding VC4-1): every
REALIZED δ > 1 pool of Step 18's K3-c is a δ-STABLE position class.
`DeltaStablePos` is OWNED by Movement V (O-8b's blueprint) — consumed here as an
opaque predicate parameter so this row compiles before Movement V lands. -/
structure K3DeltaRow (p : ℕ) (D : RegData p)
    (RealizedPool DeltaStablePos : ℕ → Prop) : Prop where
  depthSet_iff_realized : ∀ δ, δ ∈ D.depthSet ↔ RealizedPool δ
  realized_stable : ∀ δ, RealizedPool δ → 1 < δ → DeltaStablePos δ

/-! ## M7's event carriers (BP_IV §1.4; AUTHORED at REVISION 3)

**PROVENANCE (REVISION 3, mop-up adjudication).**  `CylEvent` and
`IsContinuationEvent` appear in BP_IV §1.4's M7 display with no owner module
and no spec anywhere in the corpus or blueprints; since they occur only in
BP_IV's display, BP_IV OWNS them, and the mop-up authors the minimal faithful
forms: a level-N cylinder event is a Finset of level-N boxes (the corpus
counting vocabulary — `Box p n N` used AS IS); a CONTINUATION event is one
all of whose members are still undecided at its level (the scaffold's
continuation reading of `canonical = none`).  DERIVED, flagged for
division-lead/Codex ratification (trust boundary).  Consumer: unit M7
(owner-blocked on BP_III's `ThmERow`/`D15Row` — see the H4 ledger above). -/

open LeanUrat.MovesU in
/-- M7 carrier (REVISION 3): a level-N cylinder event — a Finset of level-N
    boxes.  (`abbrev`, not `def`: the event carrier must be REDUCIBLE so the
    Finset `Membership`/card instances flow through — the `∀ f ∈ cyl` binder
    of `IsContinuationEvent` and of M7 itself does not elaborate otherwise;
    compile-gate repair of the 429-killed first mop-up pass.) -/
abbrev CylEvent (n p N : ℕ) : Type := Finset (Box p n N)

open LeanUrat.MovesU in
/-- M7 carrier (REVISION 3): the event is a CONTINUATION event of the
    classifier — every member box is undecided at level N. -/
def IsContinuationEvent {n p N : ℕ} (X : ClassifierSpec n p)
    (cyl : CylEvent n p N) : Prop :=
  ∀ f ∈ cyl, X.canonical N f = none

end LeanUrat.Scaffold.ValueSide
