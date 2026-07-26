/-
Unit C2.floorH_succ  (moves_ref: §C.1.5 (ZC-a): F_i = pointwise max of the history's line
staircases, grown one node at a time)
take (i+1) = take i ++ [nodes[i]]; foldr max over an append. Linear-order WithBot ℚ.
-/
import LeanUrat.MovesC.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

open Polynomial LeanUrat.Moves

namespace LeanUrat.MovesC

/-- `foldr max` on a snoc list: the last entry can be pulled out as an outer `max`, since `⊥` is
the identity of `max` on the linear order `WithBot ℚ`. -/
private lemma foldr_max_snoc (L : List (WithBot ℚ)) (x : WithBot ℚ) :
    (L ++ [x]).foldr max ⊥ = max (L.foldr max ⊥) x := by
  induction L with
  | nil => simp
  | cons a t ih =>
      rw [List.cons_append, List.foldr_cons, ih, List.foldr_cons, ← max_assoc]

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

theorem C2_floorH_succ (H : History p F) (i : ℕ) (hi : i < H.nodes.length) (b : ℕ) : H.floorH (i+1) b = max (H.floorH i b) ((H.nodes[i]'hi).staircase b) := by
  unfold History.floorH
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.map_append,
    List.map_cons, List.map_nil, foldr_max_snoc]

end LeanUrat.MovesC
