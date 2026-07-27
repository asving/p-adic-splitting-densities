/-
Unit XG.2 koenigFinite — the note's König, VERBATIM premise (finding 10 — no uniform
depth bound)  [E-phase: stated, body sorry]
moves_ref: "T_can(f) is FINITELY BRANCHING — each node's child menu is finite … — so
König's lemma upgrades 'every branch finite' to 'T_can(f) finite'" (finite branching is
`children : Finset` in the interface; "every branch finite" = no infinite
root-descending path).
sketch: contrapositive is König: if Branch f infinite, the finitely-branching rooted
forest (children_iff, reach) has a node at every level with infinitely many
descendants; choose successively (Mathlib route:
`nonempty_sections_of_finite_inverse_system` on the level-k sets of
infinite-descendant nodes, or a direct classical induction).
deps: Defs. difficulty: HARD. hyp: none beyond the context.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem koenigFinite {n p : ℕ} [Fact p.Prime] (C : XCtx n p) (f : MonicBox n p)
    (hbranch : ¬ ∃ g : ℕ → C.Branch f,
      g 0 = C.root f ∧ ∀ k, C.parent (g (k + 1)) = some (g k)) :
    Finite (C.Branch f) := by
  sorry

end LeanUrat.MovesX
