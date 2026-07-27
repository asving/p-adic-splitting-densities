/-
Unit Sp.finWords — moves_ref: "Corollary SP-FIN′ (words). For every L, the set
of length-L words over 𝒮_n^raw is finite, of size ≤ |𝒮_n^raw|^L".
deps: Sp.finThm. sketch: inject into `Fin L → SnRaw-subtype` via get; standard
`List.injective` bookkeeping (`List.ext_get`). difficulty: medium.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem SP_FIN' (n L : ℕ) (hn : 1 ≤ n) :
    {w : List Species | w.length = L ∧ ∀ s ∈ w, s ∈ SnRaw n}.Finite ∧
    Nat.card {w : List Species | w.length = L ∧ ∀ s ∈ w, s ∈ SnRaw n} ≤
      (Nat.card (SnRaw n))^L := sorry

end LeanUrat.MovesSp
