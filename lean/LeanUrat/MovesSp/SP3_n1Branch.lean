/-
Unit Sp.n1Branch [REV 5, Codex rev-4 crit — the tie between an ACTUAL
CanTreeModel branch and the n = 1 CatalogueWord; with hN1, an all-len-0 model at
n = 1 is now unsatisfiable and this unit exhibits the forced word] — moves_ref:
"At n = 1 the catalogue word is the single ROOT letter (W = n = 1, selection ⊥ —
(G6)'s degenerate degree) … the τ-WORD is EMPTY …; the CATALOGUE WORD is the
single confirming root letter — census data, gate-walked".
deps: Sp.n1singleton, Sp.n1RootConfirming, Sp.compMember. sketch: hN1 gives
0 < M.len η; hRoot + n1_root_confirming give (M.datum η 0).W = 1; hHalt closes
M.len η = 1; SP_COMP + n1singleton pin datum η 0 = confirmingRoot1; package the
singleton word (hMem via SP_COMP; hChain trivial on a singleton; hLast from
n1_root_confirming's W = 1; hFirstW1 vacuous). difficulty: medium (easy-medium).
hypothesis_fields: the standing group-F list (see SP3_compMember.lean); hN1 is
the note-quoted n = 1 clause (rev 5 of the note), not an engine kernel.
[E-phase binder note: the def's (p, f) binders are implicit and hf/hdeg are NOT
taken — the packaging needs only the interface fields; the theorems carry the
blueprint's full binder list.]
-/
import LeanUrat.MovesSp.DefsN3

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem n1_branch_word (p : ℕ) [Fact p.Prime]
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = 1)
    (M : CanTreeModel 1 p f) (η : M.Branch) :
    M.len η = 1 ∧ M.datum η 0 = confirmingRoot1 := sorry

/-- the packaging: every branch of an n = 1 model carries THE one-letter
catalogue word `[M.datum η 0]`. -/
def CanTreeModel.n1CatalogueWord {p : ℕ} [Fact p.Prime] {f : Polynomial ℤ_[p]}
    (M : CanTreeModel 1 p f) (η : M.Branch) : CatalogueWord 1 where
  word := [M.datum η 0]
  hne := sorry
  hMem := sorry
  hChain := sorry
  hLast := sorry
  hFirstW1 := sorry

theorem n1_branch_word_eq (p : ℕ) [Fact p.Prime]
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = 1)
    (M : CanTreeModel 1 p f) (η : M.Branch) :
    (M.n1CatalogueWord η).word = [confirmingRoot1] := sorry

end LeanUrat.MovesSp
