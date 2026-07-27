/-
Unit Sp.tauWord [REV 2, F3 — the halt endpoint is now a STRUCTURE LAW of
CatalogueWord; the theorem is unconditional] — moves_ref: "the CATALOGUE WORD
(SP-COMP's quantifier, the census's object) closes at the confirming read; the
τ-WORD (every density consumer's object) is the catalogue word with that final
confirming letter removed".
deps: Sp.memCoherent. sketch: length via `List.length_dropLast` + hne; sel = none
at the last letter from hLast + (G6) (memCoherent through hMem); sel ≠ none on
tauWord from hFirstW1 + (G6). difficulty: easy.
hypothesis_fields: verdict pinning (WHERE the halt verdict sits — parent read /
level-0 track) is VP's, NOT stated; only the word arithmetic is.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem tauWord_spec {n : ℕ} (cw : CatalogueWord n) :
    cw.tauWord.length + 1 = cw.word.length ∧
    (∀ s, cw.word.getLast? = some s → s.W = 1 ∧ s.sel = none) ∧
    (∀ s ∈ cw.tauWord, s.W ≠ 1 ∧ s.sel ≠ none) := sorry

end LeanUrat.MovesSp
