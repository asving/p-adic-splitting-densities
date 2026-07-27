/-
Unit Sp.collapseWalk — moves_ref: "a loop-collapsed entrance word is a collapsed
walk in the menu graph".
deps: Sp.collapseSublist. sketch: membership via Sublist; the boundary-edge
preservation induction: consecutive-dedup keeps exactly the SuccStep edges with
s ≠ s′ (a run boundary is a non-loop edge); two-head case split.
difficulty: medium.
-/
import LeanUrat.MovesSp.Defs
import LeanUrat.MovesSp.SP3_collapseSublist

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

/-- The head of a collapsed list is the head of the input: collapsing self-loop
runs keeps the FIRST letter of the first run. -/
private theorem collapseRuns_head? (a : Species) (t : List Species) :
    (collapseRuns (a :: t)).head? = some a := by
  induction t generalizing a with
  | nil => rfl
  | cons b rest ih =>
      simp only [collapseRuns]
      by_cases hab : a = b
      · rw [if_pos hab, hab]
        exact ih b
      · rw [if_neg hab]
        rfl

/-- Boundary-edge preservation: a SuccStep chain, after collapsing self-loop
runs, is a chain of non-loop SuccStep edges (each surviving adjacency is a run
boundary, hence `s ≠ s'`, and carries the original SuccStep since run members
are equal). -/
private theorem collapseRuns_chain {n : ℕ} :
    ∀ l : List Species, l.Chain' (SuccStep n) →
      (collapseRuns l).Chain' (fun s s' => SuccStep n s s' ∧ s ≠ s') := by
  intro l
  induction l using collapseRuns.induct with
  | case1 => intro _; exact List.isChain_nil
  | case2 s => intro _; exact List.isChain_singleton _
  | case3 s' rest ih =>
      intro hch
      simp only [collapseRuns]
      exact ih hch.tail
  | case4 s s' rest hne ih =>
      intro hch
      simp only [collapseRuns, if_neg hne]
      refine List.isChain_cons.mpr ⟨?_, ih hch.tail⟩
      intro y hy
      rw [collapseRuns_head? s' rest, Option.mem_some_iff] at hy
      subst hy
      exact ⟨hch.rel_head, hne⟩

theorem collapseRuns_collapsedWalk {n : ℕ} {l : List Species}
    (hmem : ∀ s ∈ l, InCatalogue n s) (hch : l.Chain' (SuccStep n)) :
    CollapsedWalk n (collapseRuns l) := by
  refine ⟨?_, collapseRuns_chain l hch⟩
  intro s hs
  exact hmem s ((collapseRuns_sublist l).subset hs)

end LeanUrat.MovesSp
