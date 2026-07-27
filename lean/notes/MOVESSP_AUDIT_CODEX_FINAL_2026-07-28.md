# MOVESSP FINAL CONFIRMATION AUDIT — Codex, rev 3 (2026-07-28)
# Run 2026-07-27; verdict: REJECT (5 crit / 8 gap); erratum reasoning CONFIRMED.

Erratum check — confirmed, not a finding. The note’s R6 row explicitly contains:

> “`{(1,2),(1,1)}▸(1,2) and ▸(1,1)`”

and the sealed menu law says:

> “`▸(1,2) → Q2 letters`”

without a row restriction. Therefore the correct direct μ=2 entrance roster is the three ▸(1,2) rows from R4, R5, and R6. The erratum record’s three-row reading is correct.

1. **CRITICAL — Sp.compMember / Sp.compEdges are vacuously satisfiable and do not represent all canonical branches.**

   > `theorem SP_COMP ... (M : CanTreeModel n p f) (η : M.Branch) (r : ℕ)
   > (hr : r < M.len η) : InCatalogue n (M.datum η r)`

   > `theorem SP_COMP_edges ... (M : CanTreeModel n p f) ... 
   > (hr : r + 1 < M.len η) : ... ∈ Out ...`

   `CanTreeModel.Branch` need not be inhabited, and even when inhabited, `len` may be constantly zero. Then all read laws and both theorems hold vacuously. Moreover, a branch has one finite `Nat` length, so infinite branches are not represented; the prose claim that they are handled “prefixwise” is unsupported by a prefix-realization or prefix-extension field. This is weaker than SP-COMP’s quantification over every actual terminal or infinite chain and every catalogue-word read.

2. **GAP — the declared D4R.0-K(c) field does not carry the note’s residual.**

   > `hVerdictPin : ∀ η, 0 < len η →
   >   (datum η (len η - 1)).sel = none → (verdict η).isSome`

   The note identifies the residual as the verdict alphabet, halting rule τ, and uniform detection cap. This field merely permits an arbitrary constant `some .z`; it contains no halting-rule or detection-cap data and covers only ⊥-ended words, not the note’s V_term edges from continuing letters. The blueprint itself admits that the field is logically detachable. Thus the named field does not faithfully encode the advertised open kernel.

3. **CRITICAL — Sp.outFinite is stronger than the displayed theorem.**

   > `theorem out_finite ... (s : Species) :
   > (Out n s).Finite ∧ Nat.card (Out n s) ≤ Nat.card (SnRaw n) + 3`

   SP.4 defines and bounds `Out(s)` for `s ∈ 𝒮_n^raw`. The Lean statement quantifies over every arbitrary `Species`, including incoherent and unreachable records, without `InCatalogue n s`.

4. **CRITICAL — Sp.selfloopChar characterizes `SuccStep`, not membership in `SUCC`.**

   > `theorem selfloop_iff ... :
   > SuccStep n s s ↔ (s.tag = .postRec ∧ s.e = 1 ∧
   > s.sel = some (1, s.W))`

   The note’s claim is “`s ∈ SUCC(s)` iff …” for a catalogue letter. By definition, `s ∈ Succ n s` additionally requires `InCatalogue n s`. The proposed theorem assumes only coherence and budget, so unreachable full POST-REC records satisfy its right side and `SuccStep s s` without being menu-graph self-loops. It therefore states a stronger, different claim.

5. **GAP — EntranceShape omits part of the entrance datum and does not relate depths to runs.**

   > `theorem entrance_collapsed_finite ... :
   > {l | ∃ E : EntranceShape n gsel μsel, collapseRuns E.word = l}.Finite`

   `EntranceShape` records only `(gsel, μsel)`. The note’s object is an entrance into a specified size-`e` block and landing cell `β₀`; neither appears as data or a hypothesis field. Its `depths` function is also arbitrary and is not constrained to equal the run lengths encoded by `word`. This leaves the Defs dependency underspecified relative to the displayed entrance object.

6. **GAP — several n=3 decide targets are not well-typed as Lean 4 expressions.**

   Offending specifications include:

   > `rootAdmissibleB 3 s == (s ∈ groupR : Bool)`

   > `!(succStepB 3 s s') || (s' ∈ catalogue3 : Bool)`

   > `succStepB 3 s s' == (s' ∈ menuMap3 s : Bool)`

   > `(multiSide6.all (· ∈ groupQ3)) = true`

   > `(Nstar3six s ≠ none : Bool) == (s ∈ multiSide6 : Bool)`

   > `.all fun s => s ∈ groupR ++ groupQ2 ++ groupQ3`

   In Lean 4, `List.all` consumes `α → Bool`, while list membership and `≠` are propositions; there is no automatic `Prop → Bool` coercion. `List.filter` also consumes a Boolean predicate, so the threshold targets

   > `catalogue3.filter (fun s => 2 ≤ linCount s)`

   and the analogous `3 ≤` target are likewise ill-typed. These require explicit Boolean comparisons, `List.contains`, or `decide`.

7. **CRITICAL — Sp.n3menuMap does not itself state exactness over the catalogue.**

   > `theorem menu3_exact : catalogue3.all fun s =>
   >   catalogue3.all fun s' =>
   >     succStepB 3 s s' == (s' ∈ menuMap3 s : Bool)`

   Even after repairing the Boolean typing, this checks only targets already in `catalogue3`. It does not rule out `SuccStep` targets outside that list, so it is weaker than the sealed exact menu display. The prose relies on separate closure/completeness results, but those are neither hypotheses nor dependencies of this unit.

8. **CRITICAL — Sp.n3thresholdData still does not formally pin the six named letters’ content.**

   > `multiSide6 = [msQ3R1, msQ3R2, msQ3R3, msQ3R4a, msQ3R4b, msQ3R4c]`

   > `(multiSide6.all (· ∈ groupQ3)) = true`

   > `Nstar3six msQ3R1 = some 7 ∧ ...`

   The first equality is definitional because `multiSide6` is defined as that same list. The remaining clauses assert only group membership and values of a locally defined lookup table. No statement pins the six names to the displayed R1/R2/R3 flank variants and three distinct R4 λ-rows. Thus the unit can pass with six wrong—or repeated—Q3 letters and a matching hand-defined table.

9. **GAP — the requested pinned-list order cannot be audited from the proposed definitions.**

   > `def fieldSizeExcluded2 : List Species  -- the 11 displayed letters, named`

   > `def fieldSizeExcluded3 : List Species  -- the 2 {(1,1)³} rows, named`

   Their literal bodies are absent. The intended order discipline is mathematically correct:

   - loops: Q3 before Q2;
   - terminal letters: Q1 followed by I;
   - direct μ=2 roster: R4, R5, R6;
   - exclusions: R group, then Q3, then Q2, in row order.

   But comments do not determine actual list order, so the two exclusion targets cannot receive the requested “full pinned-list audit.”

10. **GAP — Sp.lamEncode contains an unstated theorem.**

   > `def lamMatrix ... + injectivity on part-bounded λ`

   The “injectivity on part-bounded λ” result has no complete Lean statement, binders, or precise boundedness assumptions. `Sp.encodeInj` depends on it, so this is an underspecified dependency.

11. **GAP — Sp.compEnumComplete elides a required statement.**

   > `theorem compEnum_complete ... (+ compEnum_nodup)`

   `compEnum_nodup` is not stated with its binders or result. This repeats the prohibited elided-theorem pattern and leaves later enumeration reasoning unauditable.

12. **GAP — Sp.n1singleton refers to an undeclared definition and omits a dependency used by its sketch.**

   > `theorem SnRaw1_eq : ∀ s, InCatalogue 1 s ↔ s = confirmingRoot1`

   `confirmingRoot1` does not occur in the proposed DefsN3 declarations. The sketch also invokes `g6Forcing`, but the dependency list contains only `Sp.speciesEnumComplete`, `Sp.n1RootConfirming`, and `Sp.succTerminal`.

13. **GAP — Sp.collapseWalk is a hidden multi-lemma unit.**

   > `collapseRuns_collapsedWalk` AND `collapseRuns_sublist` PLUS
   > `collapseRuns_ne_nil` and `collapseRuns_eq_self_iff`

   This packages four independently useful induction/API results—especially the nontrivial preservation of boundary `SuccStep` edges—under one unit and one sketch. It violates the blueprint’s one-display/short-unit decomposition discipline.

Counts: **5 CRITICAL / 8 GAP**

**REJECT (5 crit / 8 gap)**
tokens used
71,330
Erratum check — confirmed, not a finding. The note’s R6 row explicitly contains:

> “`{(1,2),(1,1)}▸(1,2) and ▸(1,1)`”

and the sealed menu law says:

> “`▸(1,2) → Q2 letters`”

without a row restriction. Therefore the correct direct μ=2 entrance roster is the three ▸(1,2) rows from R4, R5, and R6. The erratum record’s three-row reading is correct.

1. **CRITICAL — Sp.compMember / Sp.compEdges are vacuously satisfiable and do not represent all canonical branches.**

   > `theorem SP_COMP ... (M : CanTreeModel n p f) (η : M.Branch) (r : ℕ)
   > (hr : r < M.len η) : InCatalogue n (M.datum η r)`

   > `theorem SP_COMP_edges ... (M : CanTreeModel n p f) ... 
   > (hr : r + 1 < M.len η) : ... ∈ Out ...`

   `CanTreeModel.Branch` need not be inhabited, and even when inhabited, `len` may be constantly zero. Then all read laws and both theorems hold vacuously. Moreover, a branch has one finite `Nat` length, so infinite branches are not represented; the prose claim that they are handled “prefixwise” is unsupported by a prefix-realization or prefix-extension field. This is weaker than SP-COMP’s quantification over every actual terminal or infinite chain and every catalogue-word read.

2. **GAP — the declared D4R.0-K(c) field does not carry the note’s residual.**

   > `hVerdictPin : ∀ η, 0 < len η →
   >   (datum η (len η - 1)).sel = none → (verdict η).isSome`

   The note identifies the residual as the verdict alphabet, halting rule τ, and uniform detection cap. This field merely permits an arbitrary constant `some .z`; it contains no halting-rule or detection-cap data and covers only ⊥-ended words, not the note’s V_term edges from continuing letters. The blueprint itself admits that the field is logically detachable. Thus the named field does not faithfully encode the advertised open kernel.

3. **CRITICAL — Sp.outFinite is stronger than the displayed theorem.**

   > `theorem out_finite ... (s : Species) :
   > (Out n s).Finite ∧ Nat.card (Out n s) ≤ Nat.card (SnRaw n) + 3`

   SP.4 defines and bounds `Out(s)` for `s ∈ 𝒮_n^raw`. The Lean statement quantifies over every arbitrary `Species`, including incoherent and unreachable records, without `InCatalogue n s`.

4. **CRITICAL — Sp.selfloopChar characterizes `SuccStep`, not membership in `SUCC`.**

   > `theorem selfloop_iff ... :
   > SuccStep n s s ↔ (s.tag = .postRec ∧ s.e = 1 ∧
   > s.sel = some (1, s.W))`

   The note’s claim is “`s ∈ SUCC(s)` iff …” for a catalogue letter. By definition, `s ∈ Succ n s` additionally requires `InCatalogue n s`. The proposed theorem assumes only coherence and budget, so unreachable full POST-REC records satisfy its right side and `SuccStep s s` without being menu-graph self-loops. It therefore states a stronger, different claim.

5. **GAP — EntranceShape omits part of the entrance datum and does not relate depths to runs.**

   > `theorem entrance_collapsed_finite ... :
   > {l | ∃ E : EntranceShape n gsel μsel, collapseRuns E.word = l}.Finite`

   `EntranceShape` records only `(gsel, μsel)`. The note’s object is an entrance into a specified size-`e` block and landing cell `β₀`; neither appears as data or a hypothesis field. Its `depths` function is also arbitrary and is not constrained to equal the run lengths encoded by `word`. This leaves the Defs dependency underspecified relative to the displayed entrance object.

6. **GAP — several n=3 decide targets are not well-typed as Lean 4 expressions.**

   Offending specifications include:

   > `rootAdmissibleB 3 s == (s ∈ groupR : Bool)`

   > `!(succStepB 3 s s') || (s' ∈ catalogue3 : Bool)`

   > `succStepB 3 s s' == (s' ∈ menuMap3 s : Bool)`

   > `(multiSide6.all (· ∈ groupQ3)) = true`

   > `(Nstar3six s ≠ none : Bool) == (s ∈ multiSide6 : Bool)`

   > `.all fun s => s ∈ groupR ++ groupQ2 ++ groupQ3`

   In Lean 4, `List.all` consumes `α → Bool`, while list membership and `≠` are propositions; there is no automatic `Prop → Bool` coercion. `List.filter` also consumes a Boolean predicate, so the threshold targets

   > `catalogue3.filter (fun s => 2 ≤ linCount s)`

   and the analogous `3 ≤` target are likewise ill-typed. These require explicit Boolean comparisons, `List.contains`, or `decide`.

7. **CRITICAL — Sp.n3menuMap does not itself state exactness over the catalogue.**

   > `theorem menu3_exact : catalogue3.all fun s =>
   >   catalogue3.all fun s' =>
   >     succStepB 3 s s' == (s' ∈ menuMap3 s : Bool)`

   Even after repairing the Boolean typing, this checks only targets already in `catalogue3`. It does not rule out `SuccStep` targets outside that list, so it is weaker than the sealed exact menu display. The prose relies on separate closure/completeness results, but those are neither hypotheses nor dependencies of this unit.

8. **CRITICAL — Sp.n3thresholdData still does not formally pin the six named letters’ content.**

   > `multiSide6 = [msQ3R1, msQ3R2, msQ3R3, msQ3R4a, msQ3R4b, msQ3R4c]`

   > `(multiSide6.all (· ∈ groupQ3)) = true`

   > `Nstar3six msQ3R1 = some 7 ∧ ...`

   The first equality is definitional because `multiSide6` is defined as that same list. The remaining clauses assert only group membership and values of a locally defined lookup table. No statement pins the six names to the displayed R1/R2/R3 flank variants and three distinct R4 λ-rows. Thus the unit can pass with six wrong—or repeated—Q3 letters and a matching hand-defined table.

9. **GAP — the requested pinned-list order cannot be audited from the proposed definitions.**

   > `def fieldSizeExcluded2 : List Species  -- the 11 displayed letters, named`

   > `def fieldSizeExcluded3 : List Species  -- the 2 {(1,1)³} rows, named`

   Their literal bodies are absent. The intended order discipline is mathematically correct:

   - loops: Q3 before Q2;
   - terminal letters: Q1 followed by I;
   - direct μ=2 roster: R4, R5, R6;
   - exclusions: R group, then Q3, then Q2, in row order.

   But comments do not determine actual list order, so the two exclusion targets cannot receive the requested “full pinned-list audit.”

10. **GAP — Sp.lamEncode contains an unstated theorem.**

   > `def lamMatrix ... + injectivity on part-bounded λ`

   The “injectivity on part-bounded λ” result has no complete Lean statement, binders, or precise boundedness assumptions. `Sp.encodeInj` depends on it, so this is an underspecified dependency.

11. **GAP — Sp.compEnumComplete elides a required statement.**

   > `theorem compEnum_complete ... (+ compEnum_nodup)`

   `compEnum_nodup` is not stated with its binders or result. This repeats the prohibited elided-theorem pattern and leaves later enumeration reasoning unauditable.

12. **GAP — Sp.n1singleton refers to an undeclared definition and omits a dependency used by its sketch.**

   > `theorem SnRaw1_eq : ∀ s, InCatalogue 1 s ↔ s = confirmingRoot1`

   `confirmingRoot1` does not occur in the proposed DefsN3 declarations. The sketch also invokes `g6Forcing`, but the dependency list contains only `Sp.speciesEnumComplete`, `Sp.n1RootConfirming`, and `Sp.succTerminal`.

13. **GAP — Sp.collapseWalk is a hidden multi-lemma unit.**

   > `collapseRuns_collapsedWalk` AND `collapseRuns_sublist` PLUS
   > `collapseRuns_ne_nil` and `collapseRuns_eq_self_iff`

   This packages four independently useful induction/API results—especially the nontrivial preservation of boundary `SuccStep` edges—under one unit and one sketch. It violates the blueprint’s one-display/short-unit decomposition discipline.

Counts: **5 CRITICAL / 8 GAP**

**REJECT (5 crit / 8 gap)**
