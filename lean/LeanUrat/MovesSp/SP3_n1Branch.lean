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
import LeanUrat.MovesSp.SP3_n1Root
import LeanUrat.MovesSp.SP6_n1singleton

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem n1_branch_word (p : ℕ) [Fact p.Prime]
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = 1)
    (M : CanTreeModel 1 p f) (η : M.Branch) :
    M.len η = 1 ∧ M.datum η 0 = confirmingRoot1 := by
  -- hN1 (the rev-5 n = 1 model law): the branch's catalogue word is nonempty.
  have h0 : 0 < M.len η := M.hN1 rfl η
  -- read 0's datum is a member of 𝒮₁^raw (the r = 0 leg of SP_COMP: `InCatalogue.root`
  -- fed by hRoot; hf/hdeg are unused here).
  have hcat : InCatalogue 1 (M.datum η 0) := InCatalogue.root (M.hRoot η h0)
  -- n1singleton pins the sole member: datum η 0 = confirmingRoot1.
  have hdatum : M.datum η 0 = confirmingRoot1 := (SnRaw1_eq (M.datum η 0)).mp hcat
  -- confirmingRoot1 is a W = 1 letter, so read 0 is confirming (via n1_root_confirming).
  have hW : (M.datum η 0).W = 1 := (n1_root_confirming (M.hRoot η h0)).1
  -- hHalt then closes the word at read 0: len η = 0 + 1 = 1.
  have hlen := M.hHalt η 0 (by exact_mod_cast h0) hW
  exact ⟨by simpa using hlen, hdatum⟩

/-- the packaging: every branch of an n = 1 model carries THE one-letter
catalogue word `[M.datum η 0]`. -/
def CanTreeModel.n1CatalogueWord {p : ℕ} [Fact p.Prime] {f : Polynomial ℤ_[p]}
    (M : CanTreeModel 1 p f) (η : M.Branch) : CatalogueWord 1 where
  word := [M.datum η 0]
  hne := by simp
  hMem := by
    intro s hs
    simp only [List.mem_singleton] at hs
    subst hs
    exact InCatalogue.root (M.hRoot η (M.hN1 rfl η))
  hChain := by constructor
  hLast := by
    intro s hs
    simp only [List.getLast?_singleton, Option.some.injEq] at hs
    subst hs
    exact (n1_root_confirming (M.hRoot η (M.hN1 rfl η))).1
  hFirstW1 := by
    intro s hs
    simp at hs

theorem n1_branch_word_eq (p : ℕ) [Fact p.Prime]
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = 1)
    (M : CanTreeModel 1 p f) (η : M.Branch) :
    (M.n1CatalogueWord η).word = [confirmingRoot1] := by
  change [M.datum η 0] = [confirmingRoot1]
  rw [(n1_branch_word p f hf hdeg M η).2]

end LeanUrat.MovesSp
