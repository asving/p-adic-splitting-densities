# MovesV REV-7 CHARGE (2026-07-29) — the round-6 union, orchestrator-adjudicated

Blueprint: lean/notes/MOVESV_LEAN_BLUEPRINT_2026-07-28.md (REV 6, 5164 lines, 95 units).
Verdicts to fold (READ ALL): lean/notes/MOVESV_AUDIT_CODEX6_2026-07-29.md (REJECT 15/2)
+ lean/notes/MOVESV_AUDIT_FABLE6_2026-07-29.md (2 crit/4 gap; §6.5 table verified real).
Note: MOVES §V-TABLES 7829–9054. Post-repair MovesS: lean/LeanUrat/MovesS/Interfaces.lean
+ Defs.lean (READ — the corpus changed under you) + lean/notes/W4_SYNC_DELTAS_2026-07-29.md.
Produce REV 7 in place; header + full round-6 disposition table. No git. Staged writes
≤4000 tokens/response.

## Adjudicated rulings (bind these; do not relitigate)
1. C4 — the ¬HMCAug-for-every-refinement claim is FALSE; the coupled toy is the
   SEPARATION WITNESS. Codex's construction (verified by the orchestrator): refine by
   whether h₁ = 0 — in the h₁ = 0 state the tail domain excludes h₂ = 0, in the h₁ ≠ 0
   state it is full; each refined domain FACTORS. So at the V4-11 toy: ¬HMC (the coupled
   domain does not factor unrefined) ∧ HMCAug TRUE (one 𝒞_n refinement round restores
   factorization). Rewrite V4-11 + every echo: the toy separates HMC from HMCAug —
   exactly the note's design (HMC-AUG display 8213–8221: "if a global cone inequality
   couples successive steps, ONE round of 𝒞_n refinement … restores the factorization;
   … a second surviving coupling is R2's wall channel"). Strike every ¬HMCAug claim.
   Also G1: allocate the HMC → HMCAug theorem as a real unit (the ~30-line identity-
   refinement proof).
2. C6 — XHD-d's object is the note's T_γ, NOT TReal. The note DEFINES T_γ directly
   (7921–7923: "T_γ(x, h) := #{fresh-assignment chains from x realizing (γ, h)} — a
   finite count at each level") and states no-orphan/no-stray with T_γ verbatim
   (7947–7949). FIX: a typed direct-count DEF T_γ over the process carrier (chain count,
   NOT the recursive product — the factorization T_γ = ∏ T_step is (u-T)/HMC content and
   must NOT be definitional); XHD-d keyed to T_γ > 0 two-sidedly verbatim; TReal demoted
   to a derived notion with its equivalence to T_γ > 0 as a lemma (or struck). HMC
   openness is PRESERVED by this design — verify nothing closes it.
3. C8 — marked-space disjointness is DERIVABLE, not hypothesized. (iv)-MEAS (8185–8197):
   every summand is a sub-event of the MARKED source space {(f, η)} with the mark
   ADJOINED, "pairwise disjoint IN THE MARKED SPACE; as f-events only the DIGIT CELLS
   are disjoint". FIX: the marked carrier gains the law that a mark determines its
   (m, o, β, height-class) reading; disjointness-in-the-marked-space becomes a DERIVED
   lemma (or a carrier law proved at instances); MarkDisj/MarkDisjT are REMOVED as open
   hypotheses on LedgerIV (they become the derived lemmas' names). f-event disjointness
   stays NOT claimed (PART-2's whole point).
4. C3 (Fable's "not over-pinning" OVERRULED on the quantifier read): tcellM_tgt's ∀ i
   forces EVERY same-skeleton roster member to the designated tcell — unsupported for
   multi-continuing outcomes. FIX: scope the landing tie to the DESIGNATED member — fold
   into omem_sel: ∃ μ ∈ omem m o, μ.status = Sum.inr (tgtSk m o h) ∧ (its tcellM at that
   position) = tcell s m o h. Drop the ∀-form. (The [tie] content survives for THAT
   member; n = 3 unaffected — single-continuing.)

## Codex round-6 criticals (accepted)
5. C1: SelMatches must be LOAD-BEARING — EntranceCut gains the law lands i → SelMatches
   ε i (or lands is defined as … ∧ SelMatches); CtsMeasured.entEvt/entInst gain the
   selection-matching law tying their ε-keyed data to SelMatches. A selection-ignoring
   instance must fail BY TYPE.
6. C2: IsBranchingRead := 2 ≤ mbar is an upper-bound key, not actual branching. Re-key
   to the REALIZED eligible menu (≥ 2 realized eligible continuations at the read —
   find the faithful carrier: the branch set/eligible-side vocabulary, or the realized
   selection roster; document which built object supplies it).
7. C5: SolveCond_Stmt gains the HMC premise. Note 8005 ("(COMP-Σ) additionally GIVEN
   (v)") + 8222–8224 ("Until HMC closes, K_e(p)^k is NOT a theorem about the process and
   only the unfactored per-template sum (COMP-hΣ) holds") — the solve's factored form is
   HMC-conditional; type it so.
8. C7: EntMassSummable is a silent strengthening. ENT-AGG (8124–8133): primitives and
   every FINITE partial sum hypothesis-free; CONVERGENCE "GIVEN XHD-s on the shallow
   layer". FIX: V3-8a's convergence premise = the XHD-s shallow-layer field (derive
   summability from it, or take XHD-s-shallow itself as the premise); EntMassSummable
   struck as an independent field.
9. C9: AVRec_Stmt's ∀ RB hK closure — scope to the chain's OWN RB/hK instance.
10. C10/C11/C12 (closure failures — the round-6 pattern): CellOf/stepKey as REAL
    displayed Lean defs (not comments under evt_disj_cell); fix the Defs-before-V3
    declaration order (readOfLetter/writeHeights_wf/writeHeights_ties must be IN the
    Defs layer or the consuming defs move; no forward references); XhdS_Stmt's literal
    prose "(the same three clauses …)" replaced by the three clauses verbatim.

## Seam re-keys (both verifiers converged; Fable CRIT-1/2 + Codex C13/C14/C15 + GAPs)
11. wsh17: the Prop field IS DELETED in built MovesS; RS4Chain.wsh17_pin is a
    projection-def = W17ii (Interfaces.lean 103–109, 187–190). SCHEDULE the proof duty:
    a unit proving W17ii for the wave-4 instance (or carrying it sorry-gated at exactly
    that type); rewrite S-8/V7-7/§4.2's wsh17 rows.
12. jPCell: built RatBurdens REQUIRES jPCell/jcell_ok/jcell_interp/jcell_sum (Defs.lean
    386–395). The planned instance FAILS BY TYPE. Re-key §2.H/V5-7b/V7-5a leg (b)/§4.1:
    CellPolyPack is WIRED INTO supplying these fields (no parallel type may remain the
    deliverable). Also: PolyGeomLaws.tCount's event-side identification (Defs.lean
    407–409) is a RECORDED MovesV duty — schedule it (ValA/tbl_count is the named
    carrier: "the COUNT SEMANTICS is ValA's field content" — your own §2.F note).
13. legs_read: add the §4.2 row (supplier/owner) for RS4Chain.legs_read (Interfaces.lean
    141–143) — LegAgree at non-all-active consumed pools; the map's "every field"
    completeness claim must be true again.
14. Fable GAP-3: refresh the stale MovesD/MovesS line cites (content verified verbatim,
    positions shifted post-repair). GAP-4: branchingRead/branchMenuCard use `getD` at
    MovesD.ShapeRead which has NO Inhabited instance — restructure with hlen-guarded
    `get`/`getElem` (or provide the junk witness the auditor displays) so the defs
    elaborate.

## Discipline
Same as ever: faithfulness both directions, typed fields, HMC open and unclosed, no
claimed repair that is not real in the text (round 6 burned six such rows on the Codex
leg). Display your own checks. Return {units, dispositions, summary} per the schema.
