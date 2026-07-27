/-
Unit C3.steeperChain
moves_ref: §C DOM(1) (I-aug) along the whole history (statement unchanged; HistoryCoherent
beneath is retyped — IsNodeLift, Bézout ties, intercept ties: audit R2 F3/F10/54/56/59)

The consecutive-steeper clause of `HistoryCoherent` — for every `i` with `i+1 < length`,
`slope_i < slope_{i+1}` (the last conjunct of `HistoryCoherent`'s transition component,
`hcoh.2.2.2 i hi |>.2.2.2.2.2.2`) — chains transitively.  Induction on the target index `j`:
at `i+1 = j+1` it is one application of the consecutive clause; at `i < j` it is the IH
composed with the consecutive clause by `lt_trans`.
-/
import LeanUrat.MovesC.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Polynomial LeanUrat.Moves

namespace LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

theorem C3_steeperChain (H : History p F) (hcoh : HistoryCoherent H) (i j : ℕ) (hj : j < H.nodes.length) (hij : i < j) : (H.nodes[i]'(lt_trans hij hj)).line.slope < (H.nodes[j]'hj).line.slope := by
  -- The consecutive-steeper clause of `HistoryCoherent` (its transition component's last
  -- conjunct); re-stated with the caller's own `getElem` bound proofs (proof-irrelevant).
  have steeper : ∀ (k : ℕ) (hk1 : k < H.nodes.length) (hk2 : k + 1 < H.nodes.length),
      (H.nodes[k]'hk1).line.slope < (H.nodes[k + 1]'hk2).line.slope := by
    intro k _ hk2
    exact (hcoh.2.2.2 k hk2).2.2.2.2.2.2
  -- Transitive chaining, by induction on the target index `j`.
  have key : ∀ (j : ℕ) (hj : j < H.nodes.length) (i : ℕ) (hi : i < H.nodes.length),
      i < j → (H.nodes[i]'hi).line.slope < (H.nodes[j]'hj).line.slope := by
    intro j
    induction j with
    | zero => intro _ i _ hij; omega
    | succ j ih =>
      intro hj i hi hij
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hij) with h | h
      · -- i < j : IH gives slope_i < slope_j, then one consecutive step to slope_{j+1}.
        have hjlt : j < H.nodes.length := by omega
        exact lt_trans (ih hjlt i hi h) (steeper j hjlt hj)
      · -- i = j : the goal IS the consecutive-steeper clause at k = i.
        subst h
        exact steeper _ hi hj
  exact key j hj i (lt_trans hij hj) hij

end LeanUrat.MovesC
