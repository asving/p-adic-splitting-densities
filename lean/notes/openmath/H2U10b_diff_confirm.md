# H2-U10b Codex diff-gate archive (2026-08-01)

Charge: fresh-context Codex, applied diff (5 files, vs 49ac1f0) pasted with the
adjudication's sanctioned-repair spec; 7 enumerated checks; CONFIRMED | DEVIATION.
Runner note: Codex sandbox launcher (bubblewrap) unavailable on this box — the
verdict is over the PASTED diff (the standing workaround; the on-disk state was
independently gated by lake build + AxChk, recorded in the ledger entry).

```
VERDICT: CONFIRMED

1. `childDetermined` exactly matches the sanctioned guarded form:

   > `InteriorChain H → ConsF f H D R → H.nodes[i]? = some ν →`
   > `∃! S, R.side i = some S ∧ S ∈ D.principalSides i ∧`
   > `HasRequestedSlope (Theta H) i S`

2. `InteriorChain` was removed from `CU1.lean` and moved to `Hyps.lean` with the same proposition:

   > `2 ≤ H.a0 ∧`
   > `∀ (i : ℕ) ν, H.nodes[i]? = some ν →`
   > `ν.sel ≠ none ∧ ∀ gμ ∈ ν.sel, 2 ≤ gμ.2`

   CU1 retains the required pointer note.

3. `parentSeparated` is unchanged in the displayed context:

   > `H.nodes[i]? ≠ H.nodes[j]?`

   No hunk touches `parentSeparated` or `junctionPin`, so both remain byte-identical.

4. CU1 still consumes the named hypothesis row:

   > `have hex := hFRESH.childDetermined hint hcons hν`

   The uniqueness proof is correctly adapted to the triple:

   > `⟨(R.side_spec i T).mpr ..., hT.1, hT.2.1⟩`
   > `⟨hS, hmem, hslope⟩`

   No CU1 theorem statement changes; only the moved definition, comments, and this proof body change.

5. The added witness is genuinely non-vacuous:

   > `a0 := 2`
   > `nodes := [interiorNode]`
   > `sel := some (1, 2)`
   > `(DictIII.Theta interiorEHist).slopes = [(1, 1)]`

   The gate exhibits an actual read side:

   > `∃! S, interiorReader.side 0 = some S ∧ ...`
   > `refine ⟨interiorSide, ⟨rfl, List.mem_singleton.mpr rfl, rfl⟩, ?_⟩`

   The F-4 witness is explicitly excluded:

   > `theorem duplicateEHist_not_interior : ¬ DictIII.InteriorChain duplicateEHist`

6. Every added Lean declaration is a witness, supporting law proof, gate, or field-shape instance. No `axiom` or `sorry` is added. The instance keeps `FRESH` as an argument:

   > `(hF : DictIII.FRESH 2 (ZMod 2))`
   > `hF.childDetermined ...`

   Thus the row is tested and consumed, not proved or globally instantiated.

7. The only changed files are the three sanctioned Lean files and the two sanctioned blueprint files. The docstrings honestly state ConsF/reader-law derivability, route terminal reads to `(T-READ)/(H6)`, and leave `parentSeparated` refuted and whole-row inhabitation open. No hunk falls outside the sanctioned envelope.
tokens used
VERDICT: CONFIRMED

1. `childDetermined` exactly matches the sanctioned guarded form:

   > `InteriorChain H → ConsF f H D R → H.nodes[i]? = some ν →`
   > `∃! S, R.side i = some S ∧ S ∈ D.principalSides i ∧`
   > `HasRequestedSlope (Theta H) i S`

2. `InteriorChain` was removed from `CU1.lean` and moved to `Hyps.lean` with the same proposition:

   > `2 ≤ H.a0 ∧`
   > `∀ (i : ℕ) ν, H.nodes[i]? = some ν →`
   > `ν.sel ≠ none ∧ ∀ gμ ∈ ν.sel, 2 ≤ gμ.2`

   CU1 retains the required pointer note.

3. `parentSeparated` is unchanged in the displayed context:

   > `H.nodes[i]? ≠ H.nodes[j]?`

   No hunk touches `parentSeparated` or `junctionPin`, so both remain byte-identical.

```
