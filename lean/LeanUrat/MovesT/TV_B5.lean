/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.MovesT.Defs

/-! # TV-B5 — PrunedMem / halting-duty transfer from (S-mem) + (S-ns)

BRIDGE CAMPAIGN unit **TV-B5** (area BP3, cluster B; blueprint
`lean/notes/BRIDGE_BP3_TV_2026-07-30.md` §3.B + §4). E-PHASE SKELETON —
statements pinned, bodies `sorry`.

INFORMAL STATEMENT: `fiberAt`'s clauses (i)/(ii)/(iv) read x only through
`T.mem (some H) x` and `NsHalts T (some H) x` (inside `PrunedMem` duties),
quantified over ALL histories H. Given the mem transfer (S-mem, TV-B3) and the
child transfer (S-child), all of `NsHalts`, `PrunedMem`, the clause-(i)
membership conjunction, and the clause-(iv) duty conjunction transfer between
level-<n·N-agreeing boxes.

STATEMENT RESOLUTION (recorded): stated at the SINGLE-MODEL CORE layer (one
fixed box pair, pointwise child + mem transfer hypotheses — TV-B3's core
supplies `hmem`), mirroring TV-B3's two-layer split; TV-B6 wires the tower
quantifiers. (S-ns) is DERIVED, not assumed: verified at Defs.lean:223-225,
`NsHalts T o x = T.mem o x ∧ ∀ ν, ¬ T.child o ν x` is mem/child-composed —
the TV-B2 bundle's field (iii) was dropped for exactly this reason (its module
docstring records the drop), and `tv_b5_nsHalts_transfer` IS the derivation.
The o = none leg of the mem conjunct is `root_mem` on both sides.

PROOF SKETCH: `NsHalts` — And-congruence of `hmem` (o = some) or `root_mem`
(o = none) with the ∀ν-negation congruence of `hchild`. `PrunedMem`
(Defs.lean:238-241: mem ∧ prefix duties) — And-congruence of `hmem H` with,
per proper nonempty prefix H', the duty pair's congruence (`IrrHalts` is
x-free, Defs.lean:179-182; `NsHalts` by the first lemma at `some H'`). Clause
(i)'s conjunction adds the x-free `H.nodes ≠ []`; clause (iv)'s duty pair is
the same congruence at H itself.

deps: B2 (shape provenance), B3 (supplies `hmem` at the consumer). Consumed
by: TV-B6 (clauses (i)/(ii)/(iv)). difficulty: routine-opus, ~30 lines. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

/-- **TV-B5, NsHalts transfer** — the derived (S-ns): `NsHalts` is
mem/child-composed (Defs.lean:223-225), so it transfers from the pointwise
child + mem transfers. The o = none mem leg is `root_mem` on both sides. -/
theorem tv_b5_nsHalts_transfer (T : TreeModel p F n N m pol)
    (x x' : Box p m)
    (hchild : ∀ (o : Option (History p F)) (ν : Node p F),
      T.child o ν x ↔ T.child o ν x')
    (hmem : ∀ H : History p F, T.mem (some H) x ↔ T.mem (some H) x')
    (o : Option (History p F)) :
    NsHalts T o x ↔ NsHalts T o x' := by
  unfold NsHalts
  cases o with
  | none =>
    exact and_congr (iff_of_true (T.root_mem x) (T.root_mem x'))
      (forall_congr' fun ν => not_congr (hchild none ν))
  | some H =>
    exact and_congr (hmem H)
      (forall_congr' fun ν => not_congr (hchild (some H) ν))

/-- **TV-B5, PrunedMem transfer** — τ-pruned membership (Defs.lean:238-241)
transfers: the mem conjunct by `hmem`, each proper-nonempty-prefix duty pair by
IrrHalts x-freeness + the NsHalts transfer. -/
theorem tv_b5_prunedMem_transfer (T : TreeModel p F n N m pol)
    (x x' : Box p m)
    (hchild : ∀ (o : Option (History p F)) (ν : Node p F),
      T.child o ν x ↔ T.child o ν x')
    (hmem : ∀ H : History p F, T.mem (some H) x ↔ T.mem (some H) x')
    (H : History p F) :
    PrunedMem T H x ↔ PrunedMem T H x' := by
  unfold PrunedMem
  refine and_congr (hmem H) (forall_congr' fun H' => imp_congr Iff.rfl
    (imp_congr Iff.rfl (imp_congr Iff.rfl (and_congr Iff.rfl
      (not_congr (tv_b5_nsHalts_transfer T x x' hchild hmem (some H')))))))

/-- **TV-B5, clause-(i) conjunction transfer** — the right-hand side of
`fiberAt`'s clause (i) (`H.nodes ≠ [] ∧ PrunedMem T H x`) transfers; with the
x-free left side of the ↔ this transports clause (i) whole (both directions —
the backward direction is exactly why (S-mem) quantifies over ALL H). -/
theorem tv_b5_clause_i_transfer (T : TreeModel p F n N m pol)
    (x x' : Box p m)
    (hchild : ∀ (o : Option (History p F)) (ν : Node p F),
      T.child o ν x ↔ T.child o ν x')
    (hmem : ∀ H : History p F, T.mem (some H) x ↔ T.mem (some H) x')
    (H : History p F) :
    (H.nodes ≠ [] ∧ PrunedMem T H x) ↔ (H.nodes ≠ [] ∧ PrunedMem T H x') := by
  exact and_congr Iff.rfl (tv_b5_prunedMem_transfer T x x' hchild hmem H)

/-- **TV-B5, clause-(iv) duty transfer** — the non-maximal chain duty pair
(`¬ IrrHalts H ∧ ¬ NsHalts T (some H) x`; `IrrHalts` x-free) transfers; also
the clause-(ii) NsHalts disjunct's input. -/
theorem tv_b5_duty_transfer (T : TreeModel p F n N m pol)
    (x x' : Box p m)
    (hchild : ∀ (o : Option (History p F)) (ν : Node p F),
      T.child o ν x ↔ T.child o ν x')
    (hmem : ∀ H : History p F, T.mem (some H) x ↔ T.mem (some H) x')
    (H : History p F) :
    (¬ IrrHalts H ∧ ¬ NsHalts T (some H) x)
      ↔ (¬ IrrHalts H ∧ ¬ NsHalts T (some H) x') := by
  exact and_congr Iff.rfl
    (not_congr (tv_b5_nsHalts_transfer T x x' hchild hmem (some H)))

end LeanUrat.MovesT
