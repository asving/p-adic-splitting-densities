/-
Unit Sp.dagWords — moves_ref: "with SP-FIN, the set of collapsed words over
𝒮_n^raw is FINITE, of size ≤ (|𝒮_n^raw| + 1)^{6n²}."
deps: Sp.dagWalk, Sp.finThm. sketch: inject length-≤L lists into
`Fin L → Option (SnRaw-subtype)` (pad with none); card arithmetic.
difficulty: medium.
-/
import LeanUrat.MovesSp.Defs
import LeanUrat.MovesSp.SP4_dagWalk   -- dep Sp.dagWalk: SP_DAG_walk (length ≤ 6n²)
import LeanUrat.MovesSp.SP2_finThm    -- dep Sp.finThm: SP_FIN (SnRaw n finite)

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem SP_DAG_words (n : ℕ) (hn : 1 ≤ n) : {l | CollapsedWalk n l}.Finite
    ∧ Nat.card {l | CollapsedWalk n l} ≤ (Nat.card (SnRaw n) + 1)^(6 * n^2) := by
  -- 𝒮ₙ^raw is finite (SP-FIN), so its subtype is a `Finite` type.
  have hSfin : (SnRaw n).Finite := (SP_FIN n hn).1
  haveI : Finite ↥(SnRaw n) := hSfin.to_subtype
  -- Encode a collapsed walk `l` by the padded coordinate map: position `i` of
  -- `Fin (6n²)` records `some (l.get i)` when `i` is in range, `none` otherwise.
  -- Each in-range letter lies in `SnRaw n` by the walk's membership clause; the
  -- length is `≤ 6n²` by SP-DAG (`SP_DAG_walk`), so nothing is truncated.
  let g : ↥{l | CollapsedWalk n l} → (Fin (6 * n^2) → Option ↥(SnRaw n)) :=
    fun l i => if h : (i : ℕ) < l.val.length then
      some ⟨l.val.get ⟨i, h⟩, l.prop.1 _ (List.get_mem _ _)⟩ else none
  have hg : Function.Injective g := by
    intro l1 l2 hfw
    apply Subtype.ext
    have hb1 : l1.val.length ≤ 6 * n^2 := SP_DAG_walk hn l1.prop
    have hb2 : l2.val.length ≤ 6 * n^2 := SP_DAG_walk hn l2.prop
    -- Padding with `none` above the length makes the length recoverable: the first
    -- coordinate mapped to `none` is the length, so equal encodings force equal lengths.
    have hlen : l1.val.length = l2.val.length := by
      rcases lt_trichotomy l1.val.length l2.val.length with h | h | h
      · exfalso
        have hlt : l1.val.length < 6 * n^2 := lt_of_lt_of_le h hb2
        have hcf := congrFun hfw ⟨l1.val.length, hlt⟩
        simp only [g] at hcf
        rw [dif_neg (lt_irrefl _), dif_pos h] at hcf
        simp at hcf
      · exact h
      · exfalso
        have hlt : l2.val.length < 6 * n^2 := lt_of_lt_of_le h hb1
        have hcf := congrFun hfw ⟨l2.val.length, hlt⟩
        simp only [g] at hcf
        rw [dif_pos h, dif_neg (lt_irrefl _)] at hcf
        simp at hcf
    -- With equal lengths, every in-range coordinate agrees, so the lists agree entrywise.
    apply List.ext_get hlen
    intro k hk1 hk2
    have hkL : k < 6 * n^2 := lt_of_lt_of_le hk1 hb1
    have hcf := congrFun hfw ⟨k, hkL⟩
    simp only [g] at hcf
    rw [dif_pos hk1, dif_pos hk2] at hcf
    exact congrArg Subtype.val (Option.some.inj hcf)
  refine ⟨Set.finite_coe_iff.mp (Finite.of_injective g hg), ?_⟩
  -- `Fin (6n²) → Option ↥(SnRaw n)` has exactly `(|𝒮ₙ^raw| + 1)^{6n²}` elements.
  calc Nat.card ↥{l | CollapsedWalk n l}
      ≤ Nat.card (Fin (6 * n^2) → Option ↥(SnRaw n)) := Nat.card_le_card_of_injective g hg
    _ = (Nat.card (SnRaw n) + 1) ^ (6 * n^2) := by
        rw [Nat.card_fun, Finite.card_option, Nat.card_fin]

end LeanUrat.MovesSp
