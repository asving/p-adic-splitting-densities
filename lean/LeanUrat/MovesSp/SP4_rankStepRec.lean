/-
Unit Sp.rankStepRec — moves_ref: "· e = g = 1, μ < W(s): D′ = D; tagord′ = 2 ≥
tagord; if tagord < 2 done, else n − W′ = n − μ > n − W(s). · e = g = 1, μ = W(s):
s is full …; if tagord(s) = 2, then s is THE full POST-REC letter at its stage, so
s′ ≠ s … is non-full by (i)'s uniqueness: the last coordinate rises 0 → 1."
deps: Sp.fullForcing, Sp.fullUnique, Sp.rankRadix, Sp.memCoherent. sketch: the
displayed three-way split on (μ vs W, tagord); the μ = W ∧ tagord = 2 branch:
s full; if s' full too then full_unique forces s' = s, contra hne; so fullBit
rises. difficulty: medium-hard (the subtle case; keep the three branches as
`have`s).
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem rank_step_rec {n} {s s'} (h : SuccStep n s s') (hne : s ≠ s')
    (hin : InCatalogue n s) (hin' : InCatalogue n s')
    (he1 : ∀ g μ, s.sel = some (g,μ) → s.e * g = 1) :
    rankNat n s < rankNat n s' := sorry

end LeanUrat.MovesSp
