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
import LeanUrat.MovesSp.SP6_n1singleton

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem n1_word (cw : CatalogueWord 1) :
    cw.word.length = 1 ∧ cw.tauWord = [] := by
  -- Every letter of the catalogue word is InCatalogue 1, hence equals
  -- `confirmingRoot1` (Sp.n1singleton), whose window width is W = 1.
  have hW : ∀ s ∈ cw.word, s.W = 1 := by
    intro s hs
    have hs' : s = confirmingRoot1 := (SnRaw1_eq s).1 (cw.hMem s hs)
    rw [hs']; rfl
  -- `hFirstW1` forbids W = 1 strictly before the last letter, so the initial
  -- segment (`dropLast`) is empty.
  have hdrop : cw.word.dropLast = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro s hs
    exact cw.hFirstW1 s hs (hW s (List.dropLast_subset _ hs))
  refine ⟨?_, hdrop⟩
  -- A nonempty list whose `dropLast` is empty has length 1.
  have hlen : cw.word.dropLast.length = cw.word.length - 1 := List.length_dropLast
  have hpos : 0 < cw.word.length := List.length_pos_of_ne_nil cw.hne
  rw [hdrop, List.length_nil] at hlen
  omega

end LeanUrat.MovesSp
