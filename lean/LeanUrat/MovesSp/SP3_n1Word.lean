/-
Unit Sp.n1Word [REV 3, G2 — the other half; DAG: n1RootConfirming → n1singleton
→ n1Word, acyclic] — moves_ref: "the τ-WORD is EMPTY (the standing rule
'catalogue word minus the final confirming letter' applied to the one-letter word
…); the CATALOGUE WORD is the single confirming root letter".
deps: Sp.n1singleton, Sp.memCoherent. sketch: every letter of cw is InCatalogue 1
(hMem) = confirmingRoot1 (n1singleton), so every letter has W = 1; hFirstW1 then
empties dropLast; length 1; tauWord = dropLast = []. difficulty: easy-medium.
hypothesis_fields: as Sp.n1RootConfirming ((τ-hen) semantics is VP's).
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem n1_word (cw : CatalogueWord 1) :
    cw.word.length = 1 ∧ cw.tauWord = [] := sorry

end LeanUrat.MovesSp
