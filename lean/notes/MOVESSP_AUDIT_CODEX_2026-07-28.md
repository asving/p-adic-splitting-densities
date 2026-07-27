Codex semantic audit of MovesSp Lean blueprint against §M-SPECIES — run 2026-07-28.
Prompt = CAMPAIGN_AUDIT_CHARGE_2026-07-28.md (charge) + MOVES_2026-07-24.md lines 5857-6757 (§M-SPECIES, tail trimmed at the interleaved §C heading) + MOVESSP_LEAN_BLUEPRINT_2026-07-28.md (full, 927 lines).

1. **CRITICAL — Sp.compMember.**  
   Offending spec:  
   > `theorem SP_COMP {n : ℕ} (ch : EngineChain n) : ∀ s ∈ ch.word, InCatalogue n s`  
   `EngineChain.hRoot` already assumes `RootAdmissible`, and `EngineChain.hStep` already assumes `SuccStep`. Thus the theorem merely restates closure induction. It drops the note’s quantifiers over `n, p, f, η ∈ T_can(f), r` and does not connect the list to an actual engine chain. It is strictly weaker and self-certifying.

2. **CRITICAL — Sp.compEdges.**  
   Offending spec:  
   > `theorem SP_COMP_edges {n} (ch : EngineChain n) : ch.word.Chain' (fun s s' => Sum.inl s' ∈ Out n s)`  
   This follows immediately because `EngineChain.hStep` assumes exactly the `SuccStep` relation used to define `Out`. It does not establish the note’s claim for consecutive reads of an actual canonical branch and has the same missing `p, f, η` quantifiers.

3. **CRITICAL — Sp.tauWord.**  
   Offending spec:  
   > `structure CatalogueWord ... hClose : ∀ s ∈ word.dropLast, s.sel ≠ none`  
   > `∀ s, cw.word.getLast? = some s → s.W = 1 → ...`  
   The note defines a completed catalogue word as ending at its first confirming `W = 1` read. The structure never requires the last letter to have `W = 1` or `sel = none`; the theorem makes that endpoint only a conditional antecedent. Hence arbitrary finite continuing prefixes satisfy the proposed “CatalogueWord”.

4. **CRITICAL — Sp.entranceDef.**  
   Offending spec:  
   > `structure EntranceShape ... hLast : ∃ s g μ, word.getLast? = some s ∧ s.sel = some (g, μ)`  
   The note requires the last letter to be the specified block-entry read and its designated branch to enter the size-`e` block. It also retains height-pair parameter slots and collapsed-run depth parameters. “Last letter has some continuing selection” is strictly weaker, contains no block size or entry datum, and the finiteness theorem is disconnected from `EntranceShape`.

5. **CRITICAL — Sp.n3thresholdData.**  
   Offending spec:  
   > `fieldSizeExcluded2.length = 11 ∧ fieldSizeExcluded3.length = 2 ...`  
   > `multiSide6.map Nstar3six = [some 6, ..., some 7]`  
   These checks do not state that the lists are exactly the displayed λ-defined exclusions or exactly the six named multi-side letters. Arbitrary catalogue members of the right cardinalities and ordering can satisfy the theorem. The semantic content of the sealed data is therefore not pinned.

6. **CRITICAL — Sp.n3R3check.**  
   Offending spec:  
   > `theorem R3_member : ... R3letter ∈ groupR ...`  
   > `(both flank variants)`  
   A single `Species` value cannot represent both distinct R3 flank compositions `(2)` and `(1,1)`. The displayed statement checks only one unspecified `R3letter`, while the note explicitly asserts membership of both variants.

7. **GAP — SP-COMP hypothesis fidelity.**  
   Offending spec:  
   > `D4R.0-K(c)/VP residual rides by omission (no verdict semantics consumed)`  
   The note says SP-COMP is conditional on exactly D4R.0-K(c). “Rides by omission” is not a hypothesis field. Either the residual must occur in the formal claim’s interface, or the proposed units must be identified as only a weaker, verdict-free subclaim. As written, the note’s sole open kernel is silently dropped.

8. **GAP — Sp.reflSucc.**  
   Offending spec:  
   > `and theorem rootAdmissibleB_iff (n s) : … ↔ RootAdmissible n s`  
   The second theorem is not stated, its binder types are omitted, and its `moves_ref` quotes only the SUCC display. This also combines two distinct reflection obligations without an exact second specification.

9. **GAP — Sp.shDvd.**  
   Offending spec:  
   > `theorem sh_dvd (…same hyps…) (k : ℤ) ...`  
   “Same hyps” does not pin the binders, their order, or whether `e ≥ 1` is assumed. Exact hypothesis fidelity cannot be audited from this statement.

10. **GAP — Sp.shSlots.**  
    Offending spec:  
    > `(hbez : …) (hγ : …)`  
    > `and theorem sh_anchor : ...`  
    Both hypotheses and the complete binder list of `sh_anchor` are elided. The second theorem’s quantification is therefore underspecified.

11. **GAP — Sp.shEquiv.**  
    Offending spec:  
    > `(hσ : … the slot identities of Sp.shSlots)`  
    This is not a proposition. It is unclear which slot identities, quantifiers, or endpoint identification are assumed. Moreover, the displayed interval-translation equality itself needs no such hypothesis.

12. **GAP — Sp.shStage.**  
    Offending spec:  
    > `+ the e = 1 corollary via σs.he1t`  
    The promised corollary has no statement. It is unclear whether it asserts only `σ = 0`, the position identity, the anchor identity, or the full coincidence display.

13. **GAP — Sp.selfloopFull.**  
    Offending spec:  
    > `theorem selfloop_isFull {n s} (hc) (hb) ...`  
    The types of `hc` and `hb` are absent. The intended `Coherent s` and `Budget n s` assumptions appear only in the sketch, not in the statement.

14. **GAP — Sp.rankRadix.**  
    Offending spec:  
    > `(hcb…: bounds)`  
    > `(s.D, ..., fullBit s) <ₗₑₓ ...`  
    `fullBit` is not defined in the Defs skeleton, the hypotheses are elided, and the claimed “four-case disjunction” is not actually stated. The rank-order equivalence is therefore unauditable.

15. **GAP — Sp.mcRoster.**  
    Offending spec:  
    > `moves_ref: §S-RESUM (K-SUB) ...`  
    The cited K-SUB classification is not a display in the frozen §M-SPECIES note. The definitions `mOf`, `cOf`, and the interpretation “μ ≥ 2 means continuing” therefore have an underspecified external dependency rather than support from the sole supplied ground truth.

16. **GAP — Sp.n3rootLetters.**  
    Offending spec:  
    > `root3_exact : ... ~ groupR (permutation, or filter-membership iff: ...)`  
    These are different statements: permutation also fixes multiplicities, whereas membership equivalence does not. This matters because the sketched selection generator can emit duplicate candidates when λ contains repeated equal factors.

17. **GAP — Sp.n3entrancePatterns.**  
    Offending spec:  
    > `... ∧ …`  
    The statement stops with an ellipsis and does not specify which increment-landing and block-entry patterns are checked. It cannot be compared with the displayed entrance roster or audited for exhaustiveness.

Counts: **6 CRITICAL / 11 GAP**

**REJECT (6 crit / 11 gap)**
