/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.Defs
import LeanUrat.Scaffold.HDischarge.H8.Lemma33

/-! # H8-B2 `CutSeam.lean` — (K-CUT)'s residual hypothesis surface at the [3t] carrier

`VTreeCutSeam` (three bare Prop fields, BP_VI `RootHyps` convention: named visible
FIELDS, True-instantiable, never axioms, no self-supply) + `VTreeCutSeam.holds`.
Statements VERBATIM from `lean/blueprints/HDISCHARGE_H8.md` §4, Wave 2 block
"H8-B2 CutSeam.lean"; design §3.5.  **NO theorem in this unit claims to
discharge a field.**

## The §1.3 owner table (field-by-field, owner of record)

| field | content | owner of record (existing display) |
|---|---|---|
| (K-CUT-s) `supply_cell` | the entrance predicate E is CELL data, per-node decidable from the realized read (CTS-M(i) computed partition CL-13 + CTS-M(iii) entrance-shape family) | MOVES §S.2's fenced SUPPLY; [1v]/[2b]; surfaces of the (H1) dictionary group + the O-9/CL-13 census rows |
| (K-CUT-g) `graft_complete` | every verdict-compatible (Ŝ_full, (D_i)) tuple is the cut of exactly one complete realizable tree (continuation memorylessness at entrances, incl. the δ > 1 base-changed legs) | the T-6 serving arc: D-14 (read locality, PROVED) + CU-3 (coherent nonempty locus) + [2r] REL.2 (CL-8, open) — the arc G-2 found UNDEMONSTRATED; adjudication unit H8-R1 |
| (K-CUT-m) `mass_tie` | the cut factors are the MEASURED weights: shallow factor = W(Ŝ_full)(p), block-ε factor = the grammar weight of D_ε at pool p^{δ_ε} | TREE-EXP ((SIB)/(JC-multi) = (H7)/sibjc rows) + REL.2's pool dictionary ([2r], CL-8) + (K4) mass semantics (M02/count_tie — O-1/O-3) |

Discharging the three fields is other rows' work (each cell names its row); the
residual CONSTRUCTION layer is unit H8-B3, not a field here.

## Anti-vacuity note

The fields are consumed as NAMED assumptions by BP_V-side units; they are bare
`Prop`s and hence True-instantiable.  A `trivialSeam` True-instantiation may
exist ONLY next to the honesty gate comment below, mirroring
`Scaffold/Hypotheses.lean`'s `trivialRootHyps` pattern: the trivial instance is
the machine-checked display that this structure is a transcription device, not
a discharge — any theorem consuming a `VTreeCutSeam` is conditional on ALL
three fields until their typed carriers land.

## BINDING DISPLAY RULE [review finding C-3, folded]

These are bare `Prop` fields with NO Lean-level semantics — deliberately, per
the corpus-wide theoremU/BP_VI precedent ("a row whose owner vocabulary is
ABSENT from the built corpus stays a bare Prop — a NAMED, VISIBLE field, never
an axiom"); every conditionality claim consuming them MUST list them as
UNPINNED named assumptions until their typed carriers land.  The typed re-key
targets, named now:

* `supply_cell` → a per-node decidable-from-`CellData` characterization of E;
* `graft_complete` → the graft function + two inverse laws at H8-B3's concrete
  carriers (= the `cut` Equiv's missing half);
* `mass_tie` → the W/weight equations against the measured masses.

Typing them TODAY would mean inventing carriers ahead of H8-B3 — the exact
ill-typed-statement failure the compile-probe rule exists to prevent; the
bare-Prop stage is the honest one. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanUrat.Scaffold.HDischarge.H8

/-- (K-CUT)'s residual hypothesis surface at the [3t] carrier (BP_VI `RootHyps`
convention: named Prop FIELDS, True-instantiable, never axioms, no self-supply).
Field-by-owner map: blueprint §1.3. -/
structure VTreeCutSeam (n p : ℕ) {X : LeanUrat.MovesU.ClassifierSpec n p}
    (Fb : LeanUrat.MovesU.FiberSeries n p X) where
  /-- (K-CUT-s): the entrance predicate is CELL data (CTS-M(i)/(iii) supply;
  MOVES §S.2's fenced SUPPLY — owner [1v]/[2b], CL-13). -/
  supply_cell : Prop
  /-- (K-CUT-g): GRAFT COMPLETENESS — every verdict-compatible (Ŝ,(Dᵢ)) tuple is
  the cut of exactly one complete realizable type-σ tree (continuation
  memorylessness; the D-14 + CU-3 + REL.2 serving face — G-2's open channel). -/
  graft_complete : Prop
  /-- (K-CUT-m): the measured shallow mass / block weights equal the cut factors
  (TREE-EXP-conditional; (SIB)/(JC-multi)/[2r] priced at their own rows). -/
  mass_tie : Prop

/-- All three residual legs (the row's honest remainder after waves 0–2). -/
def VTreeCutSeam.holds {n p : ℕ} {X : LeanUrat.MovesU.ClassifierSpec n p}
    {Fb : LeanUrat.MovesU.FiberSeries n p X} (S : VTreeCutSeam n p Fb) : Prop :=
  S.supply_cell ∧ S.graft_complete ∧ S.mass_tie

/- HONESTY GATE (the BP_VI display, mirroring `trivialRootHyps`): `VTreeCutSeam`
and `holds` are transcription devices, not mathematical discharge.  The
all-`True` instance below EXISTS — which is exactly why no theorem may treat
possession of a `VTreeCutSeam` (or of `holds` for a chosen instance) as
progress on (K-CUT): the mathematical content lives in the typed re-key
targets named in the module docstring, discharged at their owner rows.  Any
conditionality claim consuming these fields must display them as UNPINNED
named assumptions. -/

/-- The all-`True` instance (every field `True`) — the honesty gate's witness
that the seam rows are True-instantiable, NOT a discharge of any field. -/
def trivialSeam (n p : ℕ) {X : LeanUrat.MovesU.ClassifierSpec n p}
    (Fb : LeanUrat.MovesU.FiberSeries n p X) : VTreeCutSeam n p Fb where
  supply_cell := True
  graft_complete := True
  mass_tie := True

/-- The honesty gate, machine-checked: the trivial instance satisfies `holds`
vacuously — so `holds` alone certifies NOTHING about (K-CUT); consumers must
name the fields as assumptions (binding display rule, module docstring). -/
theorem trivialSeam_holds (n p : ℕ) {X : LeanUrat.MovesU.ClassifierSpec n p}
    (Fb : LeanUrat.MovesU.FiberSeries n p X) : (trivialSeam n p Fb).holds :=
  ⟨trivial, trivial, trivial⟩

end LeanUrat.Scaffold.HDischarge.H8
