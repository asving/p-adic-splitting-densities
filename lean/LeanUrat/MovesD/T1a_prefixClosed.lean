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

/-- Two histories with the same node list are equal (the remaining fields are Props,
so proof-irrelevance closes the gap). -/
private theorem hist_ext {H H' : History p F} (h : H.nodes = H'.nodes) : H = H' := by
  obtain ⟨a, ha1, ha2⟩ := H
  obtain ⟨b, hb1, hb2⟩ := H'
  cases h
  rfl

/-- A strictly-shorter prefix survives dropping the last element. -/
private theorem prefix_dropLast {α : Type*} {a b : List α} (h : a <+: b)
    (hlt : a.length < b.length) : a <+: b.dropLast := by
  obtain ⟨s, hs⟩ := h
  have hsne : s ≠ [] := by
    rintro rfl
    rw [List.append_nil] at hs
    rw [hs] at hlt
    omega
  exact ⟨s.dropLast, by rw [← hs, List.dropLast_append_of_ne_nil hsne]⟩

/-- Peel the last node: a history of length `> 1` is a `snoc` of its truncation. -/
private theorem exists_snoc_of_len (H' : History p F) (h2 : 1 < H'.nodes.length) :
    ∃ (H'' : History p F) (ν : Node p F) (hν : ν.species ≠ ReadSpecies.root),
      H' = H''.snoc ν hν ∧ H''.nodes = H'.nodes.dropLast := by
  have hνspec : (H'.nodes.getLast H'.nonempty).species ≠ ReadSpecies.root := by
    rw [List.getLast_eq_getElem]
    intro hc
    have := (H'.root_iff (H'.nodes.length - 1) (by omega)).mp hc
    omega
  refine ⟨⟨H'.nodes.dropLast, ?_, ?_⟩, H'.nodes.getLast H'.nonempty, hνspec, ?_, rfl⟩
  · -- the truncation is nonempty
    intro hc
    have hz : H'.nodes.dropLast.length = 0 := by simp [hc]
    rw [List.length_dropLast] at hz
    omega
  · -- root_iff transports along the prefix inclusion
    intro j hj
    rw [List.getElem_dropLast]
    exact H'.root_iff j (by rw [List.length_dropLast] at hj; omega)
  · -- the snoc reassembles the original node list
    apply hist_ext
    change H'.nodes = H'.nodes.dropLast ++ [H'.nodes.getLast H'.nonempty]
    exact (List.dropLast_concat_getLast H'.nonempty).symm

/-- Downward induction on the node-list length: membership of a chain descends to every
prefix chain, by peeling the last node through `mem_snoc`. -/
private theorem tpc_aux (T : TreeModel p F n N m pol) (x : Box p m) :
    ∀ (k : ℕ) (H' : History p F), H'.nodes.length = k →
      ∀ (H : History p F), H.IsPrefixOf H' → T.mem (some H') x → T.mem (some H) x := by
  intro k
  induction k with
  | zero =>
    intro H' hk H _ _
    have h1 : 0 < H'.nodes.length := List.ne_nil_iff_length_pos.mp H'.nonempty
    rw [hk] at h1
    exact absurd h1 (lt_irrefl 0)
  | succ j ih =>
    intro H' hk H hpre hmem
    obtain ⟨s, hs⟩ := hpre
    rcases eq_or_ne s [] with rfl | hsne
    · -- equal chains
      rw [List.append_nil] at hs
      have hHH : H = H' := hist_ext hs
      subst hHH
      exact hmem
    · -- strictly shorter: peel H'
      have hlen_eq : H.nodes.length + s.length = H'.nodes.length := by
        have := congrArg List.length hs
        simpa using this
      have hs1 : 0 < s.length := List.ne_nil_iff_length_pos.mp hsne
      have h0 : 0 < H.nodes.length := List.ne_nil_iff_length_pos.mp H.nonempty
      have h2 : 1 < H'.nodes.length := by omega
      have hltlen : H.nodes.length < H'.nodes.length := by omega
      obtain ⟨H'', ν, hν, hsnoc, hnodes⟩ := exists_snoc_of_len H' h2
      have hmem'' : T.mem (some H'') x := by
        have hx : T.mem (some (H''.snoc ν hν)) x := by rw [← hsnoc]; exact hmem
        exact ((T.mem_snoc H'' ν hν x).mp hx).1
      have hpre'' : H.IsPrefixOf H'' := by
        change H.nodes <+: H''.nodes
        rw [hnodes]
        exact prefix_dropLast ⟨s, hs⟩ hltlen
      have hk'' : H''.nodes.length = j := by
        have hnl : H''.nodes.length = H'.nodes.length - 1 := by
          rw [hnodes, List.length_dropLast]
        omega
      exact ih H'' hk'' H hpre'' hmem''

/-- Prefix-closure of the tree, derived from the generation laws. -/
theorem tree_prefix_closed (T : TreeModel p F n N m pol) :
    ∀ (H H' : History p F) (x : Box p m),
      H.IsPrefixOf H' → T.mem (some H') x → T.mem (some H) x := by
  intro H H' x hpre hmem
  exact tpc_aux T x H'.nodes.length H' rfl H hpre hmem

/-- The base clause: every inhabited chain sits over the root (immediate from
`root_mem`). -/
theorem tree_root_of_mem (T : TreeModel p F n N m pol) :
    ∀ (H : History p F) (x : Box p m), T.mem (some H) x → T.mem none x := by
  intro H x _
  exact T.root_mem x

end LeanUrat.MovesD
