/-
Unit Sp.finWords — moves_ref: "Corollary SP-FIN′ (words). For every L, the set
of length-L words over 𝒮_n^raw is finite, of size ≤ |𝒮_n^raw|^L".
deps: Sp.finThm. sketch: inject into `Fin L → SnRaw-subtype` via get; standard
`List.injective` bookkeeping (`List.ext_get`). difficulty: medium.
-/
import LeanUrat.MovesSp.Defs
import LeanUrat.MovesSp.SP2_finThm

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem SP_FIN' (n L : ℕ) (hn : 1 ≤ n) :
    {w : List Species | w.length = L ∧ ∀ s ∈ w, s ∈ SnRaw n}.Finite ∧
    Nat.card {w : List Species | w.length = L ∧ ∀ s ∈ w, s ∈ SnRaw n} ≤
      (Nat.card (SnRaw n))^L := by
  have hSfin : (SnRaw n).Finite := (SP_FIN n hn).1
  haveI : Finite ↥(SnRaw n) := hSfin.to_subtype
  -- the coordinate function: a length-L word over SnRaw ↦ its Fin L-indexed entries
  set T : Set (List Species) :=
    {w : List Species | w.length = L ∧ ∀ s ∈ w, s ∈ SnRaw n} with hT
  let g : ↥T → (Fin L → ↥(SnRaw n)) :=
    fun w i => ⟨w.val.get (Fin.cast w.prop.1.symm i), w.prop.2 _ (List.get_mem _ _)⟩
  have hg : Function.Injective g := by
    rintro ⟨w1, hw1len, hw1mem⟩ ⟨w2, hw2len, hw2mem⟩ hfw
    apply Subtype.ext
    apply List.ext_get (by rw [hw1len, hw2len])
    intro k hk1 hk2
    have hkL : k < L := hw1len ▸ hk1
    have h := congrFun hfw ⟨k, hkL⟩
    exact congrArg Subtype.val h
  refine ⟨Set.finite_coe_iff.mp (Finite.of_injective g hg), ?_⟩
  calc Nat.card ↥T ≤ Nat.card (Fin L → ↥(SnRaw n)) := Nat.card_le_card_of_injective g hg
    _ = (Nat.card ↥(SnRaw n))^L := by rw [Nat.card_fun, Nat.card_fin]

end LeanUrat.MovesSp
