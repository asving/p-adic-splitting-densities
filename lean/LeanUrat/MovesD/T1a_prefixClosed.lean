/-
Unit T1a.tree_prefix_closed  (MovesD campaign, E-phase)
moves_ref: "T_can(f) is prefix-closed — a tree" (L2) — now a THEOREM from the generation
laws, not a field.  [REV 5: Option carrier — plus the base clause from `root_mem`.]
deps: Defs.
sketch: downward induction along `mem_snoc` (peel the last node; a prefix of a snoc is
the history or a prefix of it).  difficulty: medium.  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n N m : ℕ}
  {pol : CanonPolicy p F}

/-- Prefix-closure of the tree, derived from the generation laws. -/
theorem tree_prefix_closed (T : TreeModel p F n N m pol) :
    ∀ (H H' : History p F) (x : Box p m),
      H.IsPrefixOf H' → T.mem (some H') x → T.mem (some H) x := by
  sorry

/-- The base clause: every inhabited chain sits over the root (immediate from
`root_mem`). -/
theorem tree_root_of_mem (T : TreeModel p F n N m pol) :
    ∀ (H : History p F) (x : Box p m), T.mem (some H) x → T.mem none x := by
  sorry

end LeanUrat.MovesD
