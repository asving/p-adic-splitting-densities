/-
Unit Sp.succTerminal — moves_ref: "For s ∈ 𝒮_n^raw, the OUTGOING MENU
Out(s) ⊆ 𝒮_n^raw ∪ V_term … and SUCC(s) := ∅ for terminal s (selection ⊥)."
[REV 5, Fable rev-4 gap — hs added per the C-3 pattern: the clause sits inside
SP.4's catalogue-scoped definition block, and hs is faithfulness-only, unused by
the proof; stageLaws_terminal stays unrestricted (corpus-internal bookkeeping).]
sketch: unfold StageLaws; the match's none-branch is False; Succ empty via its
StageLaws conjunct. difficulty: easy.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem succ_terminal (n : ℕ) (s : Species)
    (hs : InCatalogue n s) (h : s.sel = none) : Succ n s = ∅ := sorry

theorem stageLaws_terminal (s s' : Species) (h : s.sel = none) :
    ¬ StageLaws s s' := sorry

end LeanUrat.MovesSp
