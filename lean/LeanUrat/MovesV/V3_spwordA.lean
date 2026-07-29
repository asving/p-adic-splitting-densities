/-  MovesV unit V3-3a `spword_exists` (RE-KEYED REV 9, N-3) — the dite PASSES
    on WF prefixes.
    STATEMENT REPAIR 2026-07-30 (adjudicated; machine-verified refutation
    `V3_spwordA_negWitness.lean`): `spWord_exists`/`spWord_fits` gain THE
    WIDTH-≥-2 CONTINUATION HYPOTHESES (`hn` + `hcont`) — the negWitness showed
    the unconditional form FALSE: `SpFitsRead` pins EVERY letter's selection
    `sel = some (R.g, R.μ)` while MovesSp's Coherent (G6) terminal rule
    (`sel = none ↔ W = 1`) forbids a selection on any letter whose inherited
    window is 1; the second letter's window is `μ₀` by the stage law, and the
    root letter's window is `n`.  Of the two adjudicated forms (width-
    conditional `SpFitsRead` selection clause vs. the continuation hypothesis)
    the HYPOTHESIS form is landed: (i) it keeps `SpWordFits`/`SpFitsRead`
    (§2.D Defs layer) and every downstream consumer's statement intact, and
    (ii) the negWitness itself extends to THREE-read WF prefixes ([R0,R1,R1]:
    a read after a μ = 1 read breaks the `SuccStep` chain at the interior
    letter regardless of the selection clause's conditioning), so the
    conditional-clause form alone would stay refutable.  Blueprint row
    (MOVESV_LEAN_BLUEPRINT_2026-07-28.md V3-3a): "existence of the fitting
    species word on WF prefixes (fold of the stage laws along `P.reads`: each
    read's stage fields seed a catalogue member, `SuccStep` from the `ShapeWF`
    stage clauses via the D.5/D.7/D.8 output laws)" — the fold needs every
    seeded letter selection-bearing, i.e. every inherited window ≥ 2:
    `2 ≤ n` (the root letter's window, `RootStage`) and `2 ≤ μ_r` for every
    CONTINUED read (letter r+1's window, D.8's `W' = μ`).  The negWitness
    (which refutes the OLD unconditional ∀-sentence, restated inline there)
    stays on file untouched.  Consumption note: `template_total`
    (V3_spwordB) consumed the unconditional form; `EntShapeV` carries no
    width law, so its `hfits` leg is now an explicit open sorry — SIGN-OFF
    ITEM recorded there and in the MANIFEST. -/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem spWord_exists (n : ℕ) (P : MovesD.ShapePrefix)
    (hWF : MovesD.ShapeWF n P) (hn : 2 ≤ n)
    (hcont : ∀ (r : ℕ) (hr : r + 1 < P.reads.length),
      2 ≤ (P.reads[r]'(Nat.lt_of_succ_lt hr)).μ) :
    ∃ ws, SpWordFits n P ws := by
  -- [PROVER PASS B3 2026-07-29: REFUTED AS STATED, width hypotheses included —
  --  machine-verified witness `SpWordNeg2.spWord_exists_false'` in
  --  `V3_spword_negWitness2.lean`.  THE SPECIES/TAG OFF-BY-ONE: SpFitsRead's
  --  species clause ties read i's OWN move class (hspecInc/hspecRec +
  --  species_iff force increment iff its own e·g ≥ 2) to letter i's POSITION
  --  class (StageLaws' tag law: postInc iff the PARENT's e·g_sel ≥ 2); ShapeWF
  --  carries no cross-read species law, so the classes can disagree (witness
  --  P4 = [root move e·g = 1, μ = 2; increment read e = 2] at n = 3).
  --  SIGN-OFF ITEM: repair = cross-read species clause in ShapeWF, or re-key
  --  SpFitsRead's species clause to the parent read's move class.]
  sorry

theorem spWord_fits (n : ℕ) (P : MovesD.ShapePrefix)
    (hWF : MovesD.ShapeWF n P) (hn : 2 ≤ n)
    (hcont : ∀ (r : ℕ) (hr : r + 1 < P.reads.length),
      2 ≤ (P.reads[r]'(Nat.lt_of_succ_lt hr)).μ) :
    SpWordFits n P (spWord n P) := by
  rw [spWord, dif_pos (spWord_exists n P hWF hn hcont)]
  exact (spWord_exists n P hWF hn hcont).choose_spec

end LeanUrat.MovesV
