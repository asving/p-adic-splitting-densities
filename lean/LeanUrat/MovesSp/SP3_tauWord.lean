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
import LeanUrat.MovesSp.SP0_memCoherent

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem tauWord_spec {n : ℕ} (cw : CatalogueWord n) :
    cw.tauWord.length + 1 = cw.word.length ∧
    (∀ s, cw.word.getLast? = some s → s.W = 1 ∧ s.sel = none) ∧
    (∀ s ∈ cw.tauWord, s.W ≠ 1 ∧ s.sel ≠ none) := by
  refine ⟨?_, ?_, ?_⟩
  · -- length arithmetic: tauWord = dropLast, word ≠ [] (hne)
    have hpos : 0 < cw.word.length := List.length_pos_of_ne_nil cw.hne
    unfold CatalogueWord.tauWord
    rw [List.length_dropLast]
    omega
  · -- last letter: W = 1 by hLast; sel = none by (G6) through memCoherent
    intro s hs
    have hW : s.W = 1 := cw.hLast s hs
    have hmem : s ∈ cw.word := List.mem_of_getLast? hs
    have hco := (InCatalogue.coherent_budget (cw.hMem s hmem)).1
    exact ⟨hW, hco.2.2.2.2.2.mpr hW⟩
  · -- τ-word letters: W ≠ 1 by hFirstW1; sel ≠ none by (G6) through memCoherent
    intro s hs
    have hne1 : s.W ≠ 1 := cw.hFirstW1 s hs
    have hmem : s ∈ cw.word := (List.dropLast_sublist cw.word).subset hs
    have hco := (InCatalogue.coherent_budget (cw.hMem s hmem)).1
    exact ⟨hne1, fun hsel => hne1 (hco.2.2.2.2.2.mp hsel)⟩

end LeanUrat.MovesSp
