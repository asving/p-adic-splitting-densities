/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.HDischarge.H4.Defs

/-!
# Scaffold/HDischarge/H4/TypedFaces — unit H4-L6

Statement VERBATIM from `lean/blueprints/HDISCHARGE_H4.md` §L.3 (compile-probed
text; probe record §L.0). Def only — no proof obligation.

STANDING WARNING (Codex review finding 6, accepted): `RootHyps.h4a_r1r4`'s
refinement target is the FOUR-LAW package (H4-F6's carriers, post-H4-M1),
never this consumption face — a face-level refinement would replace the
hypothesis being discharged.

REUSED carriers (§L.0, never duplicated here): `MovesRBase.SpeciesSyntax` /
`AlphabetData` / `EQ2law` (base-index convention: δ ABSOLUTE);
`MovesU.DefsLedger.UpstreamTyped.cl8_eq2` is the consumed row whose statement
is NORMATIVE for this face's shape.
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.Scaffold.HDischarge.H4

open MovesRBase

variable (p : ℕ) [Fact p.Prime]

/-- The typed face of (H4a)'s CONSUMPTION SHAPE (what Steps 16/18 read:
the per-prime (EQ-2) law at carried `AlphabetData`, verbatim the
`UpstreamTyped.cl8_eq2` row) — NOT a refinement candidate for
`RootHyps.h4a_r1r4`: (H4a) is the four stage-tower laws, and EQ-2 is their
downstream consequence (Codex review finding 6); refining the field to this
face would silently weaken the row. -/
def H4aConsumptionFace (KCAD : ∀ (p : ℕ) [Fact p.Prime],
    (Sp : SpeciesSyntax) × AlphabetData p Sp) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], EQ2law p (KCAD p).2

end LeanUrat.Scaffold.HDischarge.H4
