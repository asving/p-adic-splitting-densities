/-
Unit Sp.dagWalk — moves_ref: "(iii) Hence the menu graph with self-loops
collapsed is a DAG; every collapsed walk visits pairwise-distinct ranks, so it
has at most … 6n² letters".
deps: Sp.rankStrict, Sp.rankRadix. sketch: map rankNat: Chain' (· < ·) list of
ℕ < 6n²; strictly-increasing-below-B has length ≤ B.
-/
import LeanUrat.MovesSp.Defs
import LeanUrat.MovesSp.SP0_memCoherent   -- dep Sp.memCoherent: InCatalogue.coherent_budget
import LeanUrat.MovesSp.SP4_rankStrict    -- dep Sp.rankStrict: rank_strict
import LeanUrat.MovesSp.SP4_rankRadix     -- dep Sp.rankRadix: rankNat_lt

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

/-- Along a collapsed walk (consecutive non-self-loop SUCC edges, all letters in
the catalogue), the `rankNat` images form a strictly increasing chain — the
"visits pairwise-distinct ranks" of the moves_ref, via `rank_strict`. -/
private theorem chain'_rank_lt {n : ℕ} :
    ∀ {l : List Species}, (∀ s ∈ l, InCatalogue n s) →
      l.IsChain (fun s s' => SuccStep n s s' ∧ s ≠ s') →
      l.IsChain (fun a b => rankNat n a < rankNat n b)
  | [], _, _ => List.isChain_nil
  | [_], _, _ => List.isChain_singleton _
  | a :: b :: t, hmem, hchain => by
      obtain ⟨⟨hstep, hne⟩, hrest⟩ := List.isChain_cons_cons.mp hchain
      exact List.isChain_cons_cons.mpr
        ⟨rank_strict (hmem a (by simp)) (hmem b (by simp)) hstep hne,
         chain'_rank_lt (fun s hs => hmem s (List.mem_cons_of_mem a hs)) hrest⟩

/-- A strictly increasing list of naturals, all below `B`, has length ≤ `B`:
it is `Nodup`, and its `toFinset` embeds into `range B`. -/
private theorem length_le_of_chain'_lt {B : ℕ} {L : List ℕ}
    (hchain : L.IsChain (· < ·)) (hbound : ∀ x ∈ L, x < B) : L.length ≤ B := by
  have hpair : L.Pairwise (· < ·) := List.isChain_iff_pairwise.mp hchain
  have hnodup : L.Nodup := hpair.imp (fun h => Nat.ne_of_lt h)
  have hsub : L.toFinset ⊆ Finset.range B := by
    intro x hx
    rw [List.mem_toFinset] at hx
    rw [Finset.mem_range]
    exact hbound x hx
  calc L.length = L.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
    _ ≤ (Finset.range B).card := Finset.card_le_card hsub
    _ = B := Finset.card_range B

theorem SP_DAG_walk {n} (hn : 1 ≤ n) {l : List Species}
    (h : CollapsedWalk n l) : l.length ≤ 6 * n^2 := by
  obtain ⟨hmem, hchain⟩ := h
  -- The rank images: a strictly increasing chain (rank_strict) bounded by 6n²
  -- (rankNat_lt on catalogue members).
  have hLchain : (l.map (rankNat n)).IsChain (· < ·) :=
    (List.isChain_map (rankNat n)).mpr (chain'_rank_lt hmem hchain)
  have hbound : ∀ x ∈ l.map (rankNat n), x < 6 * n ^ 2 := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨hc, hb⟩ := (hmem s hs).coherent_budget
    exact rankNat_lt hn hc hb
  have := length_le_of_chain'_lt hLchain hbound
  rwa [List.length_map] at this

end LeanUrat.MovesSp
