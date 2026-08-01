/-
BP_IV §1.0 — the independent named [M] hypothesis rows (`Hyps.lean`).
Units landed in this file so far: H2a (`AssembledPack` + installed `Fintype`) ·
H3 (`K3DeltaRow`).
-/
import Mathlib
import LeanUrat.MovesU.Defs

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

end LeanUrat.Scaffold.ValueSide
