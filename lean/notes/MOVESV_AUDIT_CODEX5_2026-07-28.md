# MovesV REV 5 — Codex round-5 verdict (recovered from the orphaned detached run, 2026-07-28)
# Prompt: the standing 4-part assembly (charge+addendum / note 7829-9054 / MovesS source+W4-SYNC / the full REV-5 blueprint)

1. **M-3 = prior 1 + 14 — PARTIALLY REPAIRED.**  
   The pooled signatures in V1-6/V1-7 now elaborate, and
   > `Rep e τ := ∀ q₀, q₀ ∈ V.Pools → {x : S.Hist q₀ (cellOf τ) // S.zc x}`
   
   does inhabit the frozen pool-global `MeasuredSide.Rep`. The seven pooled carriers remain consistently pool-indexed. However, the accompanying claim
   > “the resolution the frozen UNGUARDED `xhd_no_orphan` … forces”
   
   is false: `xhd_no_orphan` forces emptiness only when `h ∉ HDom`; it places no off-pool restriction when `h ∈ HDom`. The off-pool-empty branch is permitted, not forced. **GAP.**

2. **Prior 2 (`odata`) — PARTIALLY REPAIRED.**  
   `omem`, `omem_ne`, `omem_size`, `skBlk`, and `tcellM` provide genuine data, and V7-3a displays sizes, δ, verdict transport, and continuing cell construction. But a split outcome’s selected `tgtSk` need not be represented by any continuing roster member; see finding 22 below.

3. **Prior 3 (`TargetIx.term`/successor) — PARTIALLY REPAIRED.**  
   > `| term (ht : ¬ B.cont m o) (v : VLabel n)`
   
   kills junk terminal columns, and
   > `letterSp m = Sum.inl (tgtSk m o h).sp`
   
   pins the successor species. The missing selected-member tie remains critical.

4. **Prior 4 (`evt_disj_cell`) — STILL OPEN.**  
   The nominal key was shortened, but its dependent digit-cell type still contains `(s,m,o,α)`, so different continuation outcomes remain different keys and receive ordinary-box disjointness. See finding 21.

5. **Prior 5 (`MarkDisjT`) — REPAIRED.**  
   > `def MarkDisjT ...`
   
   is displayed, and V7-6a1 explicitly takes
   > `hMDT : MarkDisjT V`
   
   and names the terminal half of `meas_card`.

6. **Prior 6 (`shapeRank`) — STILL OPEN.**  
   `SelRankTie` is now typed, but it ties `MovesD.selRank` to a rank of `(g,μ)`, not to the selected `(side,ψ)` continuation required by L11. See finding 23.

7. **Prior 7 + Fable G-2 (`hentCode`) — REPAIRED.**  
   > `Nat.pair reads.length ( ... foldr Nat.pair 0)`
   
   separates different lengths and is injective on the encoded `(h,γ)` lists. The u* claim is now correctly scoped to template-fixed `gamTie` data. The pasted MovesS source confirms no law reads `MeasuredSide.hent`.

8. **Prior 8 (`mass_summable`) — REPAIRED under the adjudicated strategy.**  
   `XHDsEnt.mass_summable` is gone.  
   > `def EntMassSummable ... : Prop := ... Summable ...`
   
   is a standalone, explicitly owned premise of V3-8a and asserts no rational value.

9. **Prior 9 (V5-2a/c XHD-w) — REPAIRED.**  
   Both units explicitly list XHD-w/`w_eq`; neither treats the V4-5 dependency as discharging it.

10. **Prior 10 (J-RAT indexing) — REPAIRED.**  
    V5-7b quantifies over
    > `∀ (s) (m) (o ...) (α) (hr : J.route s m o = .split)`
    
    and constructs the datum via `route_cont`. `Jval` itself reads only the outcome quadruple. The XHD-s cell face and `CellPolyPack` are explicit hypotheses.

11. **Prior 11 (XRB adapter) — STILL OPEN.**  
    The proposed target does not exist in the pasted E-phase source, and the face definitions remain schematic. See finding 25.

12. **Prior 12 (empty `StepSys.Pools`) — REPAIRED.**  
    > `pools_ne : Pools.Nonempty`
    
    is present, and V1-8a explicitly instantiates it with a pool containing 2.

13. **Prior 13 (`kmat_all`) — REPAIRED.**  
    > `kmat_all : ∀ e, e ∈ Finset.Icc 1 n → ...`
    
    exactly matches the frozen solve quantifier.

14. **Prior 15 (closed definitions/field instances) — PARTIALLY REPAIRED.**  
    F4/F8/F9 now show full principal field-law rosters; `eligMenu`, `branchingRead`, and the three requested cast helpers are displayed. Other material definitions still contain ellipses or undefined helper promises; see finding 28.

15. **Prior 16 (`BlockData.CellIdx` duplicate) — REPAIRED.**  
    It has one declaration in §2.C; V2-2 contains only the instance and lemma.

16. **Prior 17 (24 `*_Stmt` bodies) — STILL OPEN.**  
    All names are listed, but many “bodies” are English placeholders rather than Lean expressions. See finding 27.

17. **Prior 18 (design-freedom slot 2) — PARTIALLY REPAIRED.**  
    Slot 2 itself now states TReal-only exactness, but a later current recap reasserts count-keyed exactness. See finding 32.

18. **Fable M-1 (`tbl_count`) — REPAIRED.**  
    `tbl_count` is bound to `d.tix`; `tbl_offkey` pins all other continuing columns to zero; `TargetIx.term` requires terminality. The cooked continuing-outcome terminal column no longer type-checks, and the cooked nonzero off-key family violates `tbl_offkey`.

19. **Fable M-2 (`HMCAug`) — STILL OPEN.**  
    The MOVES 8213–8220 quotation is faithful, but `RefEvents` does not establish the claimed anti-cooking result. See finding 24.

20. **Fable G-1 (V4-12 status) — PARTIALLY REPAIRED.**  
    §0 and V4-12(b) use the honest “OPEN, claimed neither way” status, but a remaining revision-record assertion contradicts it. See finding 31.

21. **CRITICAL — V7-6a2 still overclaims ordinary-event disjointness.**  
    Offending spec:
    > “`stepKey p := (⟨(s,m,o,α of dataOf p), cellOfA-image of p⟩ ... , ... height)`”
    
    and:
    > “within-cell mark differences (which assignment; which eligible continuation the mark selects) have EQUAL keys”
    
    The latter does not follow. `DCellO s m o α` is outcome-indexed, so two eligible continuation marks represented by different `o` values inhabit different dependent cell types and hence different Σ-keys. `evt_disj_cell` then asserts their unmarked box events are disjoint, contrary to the note’s explicit permission for literally equal f-projections. This also makes the advertised frozen `d4r0` supply too strong.

22. **CRITICAL — selected continuing targets are not tied to the outcome roster.**  
    Offending specs:
    > `tgtSk : ∀ m (o : Outc m), cont m o → Skeleton n`
    
    > `cont_iff : ... ↔ ∃ mu ∈ omem m o, mu.status.isRight = true`
    
    > `omem_kcol : ... (omem m o).length = 1 → ... status = Sum.inr (tgtSk ...)`
    
    For a split outcome, `cont_iff` proves only that *some* continuing member exists. No field says any member has status `Sum.inr (tgtSk m o h)` unless the entire roster has length one. `tcellM_tgt` is merely conditional on such an equality. Thus `MoveData`, V7-3a’s target state, and V5-7b’s constructed split datum can select a successor absent from the outcome’s member roster.

23. **CRITICAL — `SelRankTie` identifies the wrong selection object.**  
    Offending spec:
    > `MovesD.selRank ... ν % ...mbar = shapeRank n P r (ν.g, ν.μ)`
    
    with:
    > `eligMenu ... : List (ℕ × ℕ)`
    
    The frozen σ_sel records L11’s selected `(side, ψ)` continuation rank. Ranking only `(g,μ)` loses ψ/side distinctions; distinct eligible continuations can share the same `(g,μ)`. Consequently this tie is either unsatisfiable with `E8_rankInj` or collapses distinct selections, and V3-1/V5-1 do not establish post-split label fidelity.

24. **CRITICAL — `RefEvents` does not kill the cooked `HMCAug` witness.**  
    Offending spec:
    > `TE.tevt ... = ((refTmpls ...).map (... TE'.tevt ...)).foldr (· ∪ ·) ∅`
    
    and the claim:
    > “at the identity refinement it forces `TE' = TE` outright”
    
    A union-cover equation does not identify each refined event with the base event. `refTmpls` can contain multiple refined templates; there is no uniqueness, pairwise-disjointness, or per-template inverse law. `Refinement` also does not make histories or projected moves bijective. Hence base events may still be repartitioned among cooked refined templates whose independently chosen `D'` factors. `boxEq` only identifies box carrier types; it does not pin event subsets. The asserted reduction to `HMC TE D` is therefore invalid.

25. **CRITICAL — V7-7 cannot supply the real MovesS seam type.**  
    Offending spec:
    > `def xrbPackageOf ... : MovesS.XRBPackage := ...`
    
    The pasted real `MovesS/Interfaces.lean` explicitly says the §W4-SYNC declarations are “NOT built at E-phase” and contains no `MovesS.XRBPackage`. Thus this target type is absent from the imported Lean source. Moreover the proposed laws remain schematic:
    > `def XhdW_Stmt ... := (∀ … , ...) ∧ ...`
    
    > `def XhdU_Stmt ... := (the six XHDu law fields, verbatim ...)`
    
    so even after relocating the contract type, the unit does not yet produce the advertised Prop fields.

26. **GAP — the off-pool-empty branch is not forced.**  
    Offending claim:
    > “forced by the frozen UNGUARDED `xhd_no_orphan`”
    
    `xhd_no_orphan` constrains off-pool events only for heights outside `HDom`. The chosen empty branch is compatible and useful, but its asserted uniqueness/forcedness is unsupported.

27. **GAP — V7-2a does not display 24 Lean statement bodies.**  
    Examples:
    > `def Tri_Stmt ... := ... (the V4-2 conclusion: ...)`
    
    > `def Meas_Stmt ... := (marked-space disjointness on the Σ-carrier) ∧ ...`
    
    > `def SolveCond_Stmt ... := ... (the (vi) solve sentence: ...)`
    
    These are transcription promises, not Lean terms. Quantifiers and exact hypothesis dependencies remain unauditable; the unit also hides substantially more than one short display.

28. **GAP — material Defs placeholders remain.**  
    Examples:
    > `EntShapeV.template ... hne := …, hMem := …, ...`
    
    > `writeHeights ... Phat := shapeOfSlots ... hne := …, ...`
    
    > `shapeOfSlots := List.foldl ...`  
    > “terminal twins [+T] ... by the substitution table”
    
    > `castMoveT ... one line`
    
    These are not closed definitions. `Refinement`, `refTmpls`, entrance instantiation, and several downstream units therefore remain only plausibility sketches.

29. **GAP — the §4 RatBurdens supplier rows use stale/nonexistent unit legs.**  
    The unit split says V7-5a supplies tgP/jP, V7-5b supplies ιP, and V7-5c supplies cellP. The seam table instead states:
    > `RatBurdens.jP... | [MovesV: V7-5(b) ...]`
    
    > `RatBurdens.ιP... | [MovesV: V7-5(c) ...]`
    
    > `RatBurdens.cellP... | [MovesV: V7-5(d) ...]`
    
    There is no V7-5d, and the other two pointers identify the wrong files. The underlying prose suggests intended suppliers, but the binding SEAM-SUPPLY table is not field-accurate.

30. **GAP — the declared unit DAG is cyclic.**  
    Offending spec:
    > `V4-3 ... deps: MovesS.Interfaces, V7-4c`
    
    Yet V7 assembly depends on the V4 statement layer, and the build order places V4 before V7. The cycle must be resolved or V4-3 restated parametrically; as written, the 95-unit build order is not a DAG.

31. **GAP — contradictory V4-12 status text remains.**  
    The REV-4 revision record still says:
    > “the only-if leg is recorded process-scoped with a machine-checked inderivability witness”
    
    while the operative V4-12 text says:
    > “whether it is INTERFACE-derivable ... is OPEN and CLAIMED NEITHER WAY”
    
    Thus the requested corpus-wide single status has not been achieved.

32. **GAP — the operative TReal rule is contradicted later in the current text.**  
    The non-vacuity recap says:
    > “XHD-d/XHD-dC: two-sided exactness against the DEFINED counts (V1-3...)”
    
    This contradicts the repaired slot 2 and the actual `XHDd`, whose template exactness is against `TReal`; only the cell face remains count-keyed.

The `CoprimeLiftPack` remains correctly fenced: it is a typed premise of V6-4c, explicitly marked as a possible published-axiom candidate if Mathlib lacks the exact theorem, and is never declared as an unconditional axiom.

The unit census arithmetic is internally correct: 95 units = 32 easy / 59 medium / 4 hard.

**Counts:** 5 critical, 7 gaps.

**REJECT (5 crit / 7 gap)**