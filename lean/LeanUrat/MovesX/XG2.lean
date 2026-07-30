/-
Unit XG.2 koenigFinite — the note's König, VERBATIM premise (finding 10 — no uniform
depth bound)  [PROVED, fleet 2026-07-28]
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
  -- König's lemma. Contrapositive: if `Branch f` is infinite then, because the tree is
  -- finitely branching (`children` is a `Finset`) and every node reaches the root
  -- (`reach`), the subtree rooted at `root f` is all of `Branch f` and hence infinite;
  -- an infinite subtree has a child whose subtree is again infinite, so we can descend
  -- forever, contradicting `hbranch`.
  by_contra hfin
  haveI : Infinite (C.Branch f) := not_finite_iff_infinite.mp hfin
  -- `r c d` : `d` is the parent of `c`; `Sub b` : the descendants of `b` (incl. `b`).
  set r : C.Branch f → C.Branch f → Prop := fun c d => C.parent c = some d
  set Sub : C.Branch f → Set (C.Branch f) := fun b => { c | Relation.ReflTransGen r c b }
    with hSub
  -- An infinite subtree has a child whose subtree is infinite.
  have hstep : ∀ b : C.Branch f, (Sub b).Infinite → ∃ c ∈ C.children b, (Sub c).Infinite := by
    intro b hb
    by_contra hcon
    push Not at hcon
    -- `hcon : ∀ c ∈ children b, (Sub c).Finite` (`push_neg` unfolds `Set.Infinite`).
    -- Decompose `Sub b` as `{b} ∪ ⋃_{c child of b} Sub c`; each piece is finite.
    have hfinU : (⋃ c ∈ (↑(C.children b) : Set (C.Branch f)), Sub c).Finite := by
      apply Set.Finite.biUnion (C.children b).finite_toSet
      intro c hc
      exact hcon c (Finset.mem_coe.mp hc)
    have hsub : Sub b ⊆ insert b (⋃ c ∈ (↑(C.children b) : Set (C.Branch f)), Sub c) := by
      intro c' hc'
      have hc'' : Relation.ReflTransGen r c' b := hc'
      rcases Relation.ReflTransGen.cases_tail hc'' with h | ⟨d, hd1, hd2⟩
      · exact Set.mem_insert_iff.mpr (Or.inl h.symm)
      · refine Set.mem_insert_iff.mpr (Or.inr ?_)
        exact Set.mem_biUnion (Finset.mem_coe.mpr ((C.children_iff b d).mpr hd2)) hd1
    exact hb ((hfinU.insert b).subset hsub)
  -- The subtree of the root is everything, hence infinite.
  have hroot : (Sub (C.root f)).Infinite := by
    have huniv : Sub (C.root f) = Set.univ := by
      ext c
      simp only [hSub, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact C.reach c
    rw [huniv]
    exact Set.infinite_univ
  -- Descend: pick, at each infinite node, a child with an infinite subtree.
  let step : {b : C.Branch f // (Sub b).Infinite} → {b : C.Branch f // (Sub b).Infinite} :=
    fun x => ⟨(hstep x.1 x.2).choose, (hstep x.1 x.2).choose_spec.2⟩
  have hstep_parent : ∀ x : {b : C.Branch f // (Sub b).Infinite},
      C.parent (step x).1 = some x.1 := by
    intro x
    exact (C.children_iff x.1 _).mp (hstep x.1 x.2).choose_spec.1
  refine hbranch ⟨fun k => (step^[k] ⟨C.root f, hroot⟩).1, rfl, ?_⟩
  intro k
  change C.parent (step^[k + 1] ⟨C.root f, hroot⟩).1 = some (step^[k] ⟨C.root f, hroot⟩).1
  rw [Function.iterate_succ_apply']
  exact hstep_parent (step^[k] ⟨C.root f, hroot⟩)

end LeanUrat.MovesX
