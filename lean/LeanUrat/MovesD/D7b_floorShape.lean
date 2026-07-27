/-
Unit D7b.floorH_shape  (MovesD campaign, E-phase)
moves_ref: "the fresh inventory's strip depths run between the recorded old/new lines,
each pinned only WITH its height" (L9 rev 9).
deps: D7a.
sketch: fold congruence over the first-i staircases (List.take/map/range).
difficulty: medium.  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs
import LeanUrat.MovesD.D7a_staircaseShape

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n : ℕ}
  {P : Shape n}

/-- `foldr max ⊥` splits over concatenation (max is associative/commutative with unit ⊥). -/
private lemma foldrMaxBotAppend (l₁ l₂ : List (WithBot ℚ)) :
    (l₁ ++ l₂).foldr max ⊥ = max (l₁.foldr max ⊥) (l₂.foldr max ⊥) := by
  induction l₁ with
  | nil => rw [List.nil_append, List.foldr_nil, max_eq_right bot_le]
  | cons a l ih => simp only [List.cons_append, List.foldr_cons, ih, max_assoc]

/-- The cumulative floor is shape data. -/
theorem floorH_shape {H : History p F} (hcoh : HistoryCoherent H)
    (hP : (P : ShapePrefix).MatchesHist H) :
    ∀ i b, H.floorH i b = (P : ShapePrefix).floorS i b := by
  have hlen : H.nodes.length = (P : ShapePrefix).reads.length := hP.choose
  intro i
  induction i with
  | zero => intro b; simp [History.floorH, ShapePrefix.floorS]
  | succ k ih =>
    intro b
    -- the k-th (last) staircase contribution agrees on both sides
    have key : ((H.nodes[k]?).toList.map (fun ν => ν.staircase b)).foldr max (⊥ : WithBot ℚ)
        = ((P : ShapePrefix).reads[k]?).elim ⊥
            (fun R => R.staircaseS ((P : ShapePrefix).lineS k) b) := by
      by_cases hk : k < H.nodes.length
      · have hk' : k < (P : ShapePrefix).reads.length := hlen ▸ hk
        rw [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk']
        simp only [Option.toList_some, List.map_cons, List.map_nil, List.foldr_cons,
          List.foldr_nil, Option.elim_some]
        rw [max_eq_left bot_le]
        exact staircase_shape hcoh hP k hk hk' b
      · have hk2 : H.nodes.length ≤ k := by omega
        have hk' : (P : ShapePrefix).reads.length ≤ k := by omega
        rw [List.getElem?_eq_none hk2, List.getElem?_eq_none hk']
        simp
    -- unfold one fold step on each side
    have stepH : H.floorH (k + 1) b
        = max (H.floorH k b)
            (((H.nodes[k]?).toList.map (fun ν => ν.staircase b)).foldr max ⊥) := by
      unfold History.floorH
      rw [List.take_add_one, List.map_append, foldrMaxBotAppend]
    have stepS : (P : ShapePrefix).floorS (k + 1) b
        = max ((P : ShapePrefix).floorS k b)
            (((P : ShapePrefix).reads[k]?).elim ⊥
              (fun R => R.staircaseS ((P : ShapePrefix).lineS k) b)) := by
      unfold ShapePrefix.floorS
      rw [List.range_succ, List.map_append, foldrMaxBotAppend]
      simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
        max_eq_left bot_le]
    rw [stepH, stepS, ih b, key]

end LeanUrat.MovesD
