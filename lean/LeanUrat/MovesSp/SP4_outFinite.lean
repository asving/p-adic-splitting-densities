/-
Unit Sp.outFinite [REV 4, Codex-3 FIXED — restricted to the note's own
quantifier: SP.4 defines Out only on catalogue letters] — moves_ref:
"**Definition (Out; retyped at rev 3).** For s ∈ 𝒮_n^raw, the OUTGOING MENU
Out(s) ⊆ 𝒮_n^raw ∪ V_term" + "FINITENESS: |Out(s)| ≤ |𝒮_n^raw| + 3 by SP-FIN."
deps: Sp.finThm. sketch: Succ n s ⊆ SnRaw n; union card ≤ sum; card Verdict = 3.
(hs is not needed by the proof — the restriction is FAITHFULNESS to the display's
quantifier, per the adjudication: never state more than the note does.)
difficulty: easy.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem out_finite (n : ℕ) (hn : 1 ≤ n) (s : Species)
    (hs : InCatalogue n s) : (Out n s).Finite ∧
    Nat.card (Out n s) ≤ Nat.card (SnRaw n) + 3 := sorry

end LeanUrat.MovesSp
