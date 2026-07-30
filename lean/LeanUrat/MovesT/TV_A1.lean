/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.MovesT.Defs

/-! # TV-A1 — the E5 (U)∧(R) pair, NAMED (`TrackUniqOn` / `TrackRepOn`)

BRIDGE CAMPAIGN unit **TV-A1** (area BP3, cluster A; blueprint
`lean/notes/BRIDGE_BP3_TV_2026-07-30.md` §3.A + §4). E-PHASE STATEMENT MODULE.

The two predicates below are the internal fenced pair `hD4R0K` of
`fiber_root_split` (MovesT/E5_rootSplit.lean:343-348) VERBATIM, hoisted to named
Defs-genre predicates so the ratified R3 hoist (units TV-A2/A3/A4, orchestrator
Q1) can thread them as NAMED warranted hypotheses through the TREE-EXP spine
(E5 → E8 → E10 → E11 → D12), the wave-4 parameter genre.

PLACEMENT RESOLUTION (recorded per the E-phase rules): the blueprint prescribes
"MovesT/Defs.lean, §2.4 vicinity"; E-phase writes NEW FILES ONLY, so the defs
land in this additive module. TV-A2 (which edits E5_rootSplit.lean anyway) may
either import this module or fold the two defs into Defs.lean at execution —
byte-identical definitions either way.

deps: none. Consumed by: TV-A2 (`fiber_root_split` restated), TV-A3 (`treeExp`/
`perShape_law` threading, ∀-g shape), TV-A4 (E11/D12/Defs ∀-closures sweep),
TV-A5a/A5b (non-vacuity/necessity probes).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

/-- **(U) — per-point per-track UNIQUENESS of realized root children** (unit TV-A1;
the first conjunct of E5's `hD4R0K`, E5_rootSplit.lean:343-345, verbatim).

Over a fixed reduction datum `g`: two realized root children at one root-cell point
sharing a track are equal — "THE first window read" (per point, per track, at most
one child). Owner **HC-2/D4R0K** (presented-face genre, the same owner row as
`presents`/`state_cell`), quoting MOVES 7112–7119 (the (c2) covering case
analysis): "realized root children are EXACTLY the first window reads on the
reduction's REPEATED tracks"; (U) is the "EXACTLY … THE first window read" half.
NOT derivable from the displayed `CellData`/`CellAssign` laws: nothing bounds a
`.red`-cell branch set's cardinality — two distinct children can share a track
(blueprint §3.A). NEVER proved in this corpus; consumed as a named hypothesis. -/
def TrackUniqOn (T : TreeModel p F n N m pol) (χ : Fin n → Fin m)
    (trackOf : Node p F → Polynomial (ZMod p)) (g : Fin n → ZMod p) : Prop :=
  ∀ y ∈ rootCell χ g, ∀ ν ν' : Node p F, T.child none ν y →
    T.child none ν' y → trackOf ν = trackOf ν' → ν = ν'

/-- **(R) — REPEATED-ONLY track EXHAUSTIVENESS of realized root children** (unit
TV-A1; the second conjunct of E5's `hD4R0K`, E5_rootSplit.lean:346-348, verbatim).

Over a fixed reduction datum `g`: a realized root child's track is a repeated
(multiplicity ≥ 2) normalized factor of the point's level-0 reduction. Owner
**HC-2/D4R0K**, quoting MOVES 7112–7119: "m_i = 1 gives τ-hen and m_i ≥ 2 opens
the window — total"; a multiplicity-1 track τ-hen-halts and carries NO child, so
realized children ride repeated tracks only. NOT derivable from the displayed
laws: nothing forces multiplicity ≥ 2 at a realized child (`ChildCover` is the
∃-direction only; `KBTotTower.root_total` likewise; blueprint §3.A). NEVER proved
in this corpus; consumed as a named hypothesis. -/
def TrackRepOn (T : TreeModel p F n N m pol) (χ : Fin n → Fin m)
    (trackOf : Node p F → Polynomial (ZMod p)) (g : Fin n → ZMod p) : Prop :=
  ∀ y ∈ rootCell χ g, ∀ ν : Node p F, T.child none ν y →
    2 ≤ Multiset.count (trackOf ν)
      (UniqueFactorizationMonoid.normalizedFactors (redPoly χ y))

end LeanUrat.MovesT
