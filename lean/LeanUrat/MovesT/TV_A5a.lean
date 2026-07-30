/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.MovesT.TV_A1

/-! # TV-A5a — the first in-corpus `CellAssign` instance (n = 1 childless micro-carrier)

BRIDGE CAMPAIGN unit **TV-A5a** (area BP3, cluster A; blueprint
`lean/notes/BRIDGE_BP3_TV_2026-07-30.md` §3.A(i) + §4; REV 2 finding 12, split
from the old A5). E-PHASE SKELETON — statements pinned, bodies `sorry`.

INFORMAL STATEMENT: an n = 1 childless micro-carrier inhabits the FULL
`CellAssign` premise row. For n = 1 the reduction `redPoly χ x` is the monic
LINEAR polynomial `X + C (x (χ 0))`, whose `normalizedFactors` multiset has card
1, so no factor has count ≥ 2 and `ChildCover` is VACUOUS with
`child := fun _ _ _ => False`; `mem := fun o _ => o = none` (the some-side is
False), `branchSetOf := ∅`, and every `TreeModel`/`CellData` law is decidable or
vacuous. This kills the standing "premise row uninhabitable" fence rationale
(E5_rootSplit.lean:339-342 and E11_treeN.lean:85-89 both rest on "NO `CellAssign`
instance exists in-corpus") and makes the TV-A1 pair NON-VACUOUSLY STATABLE:
at this witness both `TrackUniqOn` and `TrackRepOn` hold vacuously.

FENCE-RECORD DUTY (prover phase): on completion, BOTH fence-rule records
(E5:339-342, E11:85-89) must be updated from "premise uninhabitable" to
"inhabited; pair vacuously true at the witness" — those are edits to EXISTING
files, deferred to the prover fleet (E-phase writes new files only).

deps: TV-A1. Consumed by: TV-A5b (reuses the carrier machinery pattern).
difficulty: hard-fable, ~70 lines (blueprint estimate).

PROOF SKETCH: `mem_single` — `some ⟨[ν],…⟩ = none ↔ child none ν x` is
`False ↔ False`; `mem_snoc` — `False ↔ (mem ∧ False)`; `mem_realizable` —
vacuous (no some-state is realized). `CellAssign`: take `Cell := Unit` (finite),
`cellOf`/`branchCellOf` constant, `cellLevel`/`levelOf := 0`, `branchSetOf := ∅`;
`cell_local`/`branch_cell_joint` by constancy; `child_cell`/`child_root_sub`/
`child_cell_red`/`child_red_uniform` vacuous or by `False.elim`/`∅`-membership;
`child_cover` via `count_normalizedFactors_le_one_of_monic_natDegree_one` below
(the 2 ≤ count premise is refuted: `redPoly χ x` at n = 1 is monic of natDegree
1, its factor multiset is the singleton {itself}, all counts ≤ 1). The pair
lemma: both conjuncts have a `T.child none ν y` premise = False. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- TV-A5a helper: a monic polynomial of natDegree 1 over the field `ZMod p` has
no normalized factor of multiplicity ≥ 2 (its `normalizedFactors` multiset has
card 1). This is the exact lemma that makes `ChildCover` VACUOUS on the n = 1
micro-carrier (blueprint §3.A(i): "a monic linear poly's normalizedFactors has no
factor of count ≥ 2 — card computation"). -/
theorem count_normalizedFactors_le_one_of_monic_natDegree_one
    (f : Polynomial (ZMod p)) (hf : f.Monic) (hdeg : f.natDegree = 1)
    (ψ : Polynomial (ZMod p)) :
    Multiset.count ψ (UniqueFactorizationMonoid.normalizedFactors f) ≤ 1 := by
  sorry

/-- TV-A5a data block: the n = 1 CHILDLESS micro-tree — `mem o x := (o = none)`
(root always realized, no some-state ever realized), `child ≡ False`. The three
law fields are the unit's proof obligations (sketch in the module docstring). -/
def microTree (pol : CanonPolicy p F) (N m : ℕ) : TreeModel p F 1 N m pol where
  mem o _ := o = none
  child _ _ _ := False
  root_mem _ := rfl
  mem_single := sorry
  mem_snoc := sorry
  mem_realizable := sorry

/-- TV-A5a: the micro-tree is CHILDLESS (definitional). -/
theorem micro_childless (pol : CanonPolicy p F) (N m : ℕ) :
    ∀ (o : Option (History p F)) (ν : Node p F) (x : Box p m),
      ¬ (microTree pol N m).child o ν x :=
  fun _ _ _ h => h

/-- **TV-A5a, the instance**: the first in-corpus `CellAssign` witness, over the
childless micro-tree at n = 1. Intended data (sketch): `Cell := Unit`, constant
`cellOf`/`branchCellOf`, `branchSetOf := ∅`, levels 0; `child_cover` vacuous via
`count_normalizedFactors_le_one_of_monic_natDegree_one` (n = 1 reductions are
monic linear). -/
noncomputable def microCellAssign (pol : CanonPolicy p F) (N m : ℕ)
    (χ : Fin 1 → Fin m) (trackOf : Node p F → Polynomial (ZMod p)) :
    CellAssign p F 1 N m pol (microTree pol N m) χ trackOf := by
  sorry

/-- **TV-A5a, the fence-record upgrade**: at the micro-carrier the TV-A1 pair is
(vacuously) TRUE at every reduction datum `g` — so the (U)∧(R) hypotheses of the
A2 hoist are non-vacuously statable: the premise row of `fiber_root_split` is
inhabitable AND the pair holds at an inhabitant. -/
theorem micro_pair_vacuous (pol : CanonPolicy p F) (N m : ℕ)
    (χ : Fin 1 → Fin m) (trackOf : Node p F → Polynomial (ZMod p))
    (g : Fin 1 → ZMod p) :
    TrackUniqOn (microTree pol N m) χ trackOf g ∧
    TrackRepOn (microTree pol N m) χ trackOf g := by
  sorry

end LeanUrat.MovesT
