/-
Unit Sp.compEdges — moves_ref: "each consecutive read pair is linked by an edge
of the syntactic menu Out (SP.4)" + step (5): "which is precisely SP.4's edge
relation; so each realized transition is an Out edge."
deps: Sp.compMember. sketch: Succ-membership = InCatalogue (compMember at r + 1)
∧ SuccStep (assembled as in compMember); then `Or.inl` into Out. GENUINE step:
the conclusion's Out is defined through InCatalogue, which no field supplies.
difficulty: easy. hypothesis_fields: the standing group-F list (see
SP3_compMember.lean).
AS-BUILT (2026-07-30 verify-2 fold-in): the deps line above is the blueprint
plan — the file imports only Defs and re-runs the compMember closure induction
inline (see the in-proof comment); Sp.compMember is neither imported nor cited.
Inline duplication tracked under the Class-D watch
(notes/GOLF_CAMPAIGN_2026-07-30.md).
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem SP_COMP_edges (n p : ℕ) [Fact p.Prime] (f : Polynomial ℤ_[p])
    (hf : f.Monic) (hdeg : f.natDegree = n) (M : CanTreeModel n p f)
    (η : M.Branch) (r : ℕ) (hr : (r + 1 : ℕ∞) < M.len η) :
    Sum.inl (M.datum η (r + 1)) ∈ Out n (M.datum η r) := by
  -- InCatalogue for every read below len (Sp.compMember's content, inline: the
  -- closure induction on the read index; no field mentions InCatalogue/Succ/Out).
  have hmem : ∀ k : ℕ, (k : ℕ∞) < M.len η → InCatalogue n (M.datum η k) := by
    intro k
    induction k with
    | zero =>
      intro hk
      exact InCatalogue.root (M.hRoot η (by exact_mod_cast hk))
    | succ j ih =>
      intro hk
      have hj : (j : ℕ∞) < M.len η :=
        lt_trans (by exact_mod_cast Nat.lt_succ_self j) hk
      exact InCatalogue.step (ih hj) ⟨M.hStage η j (by exact_mod_cast hk),
        M.hCoh η (j + 1) hk⟩
  have hrsucc : ((r + 1 : ℕ) : ℕ∞) < M.len η := by exact_mod_cast hr
  -- Succ-membership = InCatalogue (compMember at r+1) ∧ SuccStep (assembled).
  have hsucc : M.datum η (r + 1) ∈ Succ n (M.datum η r) :=
    ⟨hmem (r + 1) hrsucc, M.hStage η r hr, M.hCoh η (r + 1) hrsucc⟩
  -- Or.inl into Out.
  exact Set.mem_union_left _ (Set.mem_image_of_mem Sum.inl hsucc)

end LeanUrat.MovesSp
