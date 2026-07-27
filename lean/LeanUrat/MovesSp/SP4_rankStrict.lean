/-
Unit Sp.rankStrict — moves_ref: "(ii) The rank ρ(s) := (D, tagord, n − W,
1 − [s is full]) … STRICTLY increases lexicographically along every non-self-loop
SUCC edge s → s′".
deps: Sp.rankStepInc, Sp.rankStepRec, Sp.rankRadix. sketch: e·g = 1 ∨ e·g ≥ 2
(WellTyped positivity); dispatch. difficulty: easy.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem rank_strict {n} {s s'} (hin : InCatalogue n s)
    (hin' : InCatalogue n s') (h : SuccStep n s s') (hne : s ≠ s') :
    rankNat n s < rankNat n s' := sorry

end LeanUrat.MovesSp
