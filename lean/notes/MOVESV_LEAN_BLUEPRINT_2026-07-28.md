# MOVESV LEAN BLUEPRINT — REV 7 (wave 4)

*(2026-07-28, Fable blueprint writer. GROUND TRUTH: the frozen dual-accepted
§V-TABLES text, `lean/notes/MOVES_2026-07-24.md` lines 7829–9054 (rev 7 —
Codex passes 6+7 + Fable pass, all CLEAN on identical text; V-n3 gate PASSED
178/178). A Lean statement below is faithful iff it says what that text's
display says. Campaign doctrine per `LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md`
§2/§3 + the wave-2 ledger doctrine: "a faithful interface must be FALSE for
instances the note would reject; obligations may be open, but their TYPES must
pin their content".)*

**REVISION RECORD.** REV 1 was REJECTED by both round-1 auditors on identical
text: Codex 23 crit / 6 gap (`MOVESV_AUDIT_CODEX_2026-07-28.md`, findings C1–C29)
and Fable fresh-instance 2 crit / 5 gap (`MOVESV_AUDIT_FABLE_2026-07-28.md`,
findings A-1–A-7). REV 2 repairs the UNION; the full disposition table is §6.
The five structural repairs, named once here:
1. **The A2 arithmetic catch (C3, verified first):** `(3(h₀+h₂)−1)/2` has
   half-integral coefficients in (h₀,h₂), so it cannot inhabit the
   natural-coefficient `AffineE`. REPAIR: note-faithful reparameterization —
   `A2dom` and `EA2` are now DECLARED in the (t,u) chart where the coefficients
   ARE natural (E = 6t+3u+1 — OUR derived chart form; the note displays
   E = (3(h₀+h₂)−1)/2 plus the substitution h₂ = t ≥ 1, h₀ = 3t+2u+1, and the
   string "6t+3u+1" appears nowhere in it — attribution corrected at REV 3,
   G-1), and the coordinate change `A2chart` is a DEFINITION;
   V0-4/V6-2a/V6-2b re-keyed (§2.I, §3).
2. **The doctrine core (C1, C2):** `StepSys` gains non-vacuity laws (`cell_ne`,
   `out_ne`, `zc_ne`) where the note realizes them; `cntraw` is now a DEF
   (`Fintype.card (Assign …)` — tied to Assign cardinality BY DEFINITION);
   the chain count is the DEF `chainCount` (the note's T_γ definition encoded
   as the recursion through the new history-extension field `StepSys.ext`),
   so XHDd's exactness laws quantify over the real count, and the cell-event
   tie rides `CtsMeasured.evtOf` (§2.B, §2.F, §2.G).
3. **The wiring core (A-1, A-2, C7, C24):** the entrance-side carrier is now
   TEMPLATE×COMPONENT-keyed (`EntIx`, finite; `ιDom = the listed component`;
   `ιshH` the per-instantiation mass; per-component PolyGeoms exposed), which
   is the granularity `MovesS.MeasuredSide`/`RatBurdens.ιP` actually types;
   `StepSys.ext` is the history-extension carrier the chain recursion needs.
4. **The J/measured retyping (C8, C23, C24):** digit cells are OUTCOME-keyed
   (`DCellO`), so J tables exist per (τ, o) including split outcomes; the
   measured ℝ-fields (gwt/μcell/rowVal/kstep/ιshH/ιsh/ιval) are no longer free
   data — V7-4 DEFINES them from the typed XHD package over the counting
   carriers, which is exactly the tie set C24 demanded.
5. **Census upgraded (C20, A-4):** DefsGate gains explicit table-based finite
   fields `F4/F8/F9`, so V6-1c/V6-3b now decide the census at ALL NINE sealed
   prime-power points in-kernel; the multiplicity sketch is re-keyed to
   char-free divisibility (no f″ — the p = 2 trap is out).

**REVISION RECORD — REV 3.** REV 2 was REJECTED by both round-2 auditors:
Codex 16 crit / 4 gap (`MOVESV_AUDIT_CODEX2_2026-07-28.md`, findings 1–20) and
Fable fresh-instance 6 crit / 4 gap (`MOVESV_AUDIT_FABLE2_2026-07-28.md`,
F-1–F-6, G-1–G-4). The A2 chart, the doctrine core, the EntIx carrier itself,
the V6 gate layer, and the unit DAG outside the measured-wiring region were
VERIFIED CLEAN by both passes and are UNTOUCHED here. REV 3 repairs the union;
the round-2 disposition table is §6.2. The five structural repairs:
1. **THE MEASURED-WIRING CLUSTER (F-1..F-6; Codex 7–11, 16):** the INSTANCE
   CENSUS is now a carrier distinct from the box events — `CtsMeasured.entInst`
   (D4R.4's marked-prefix census, box-realized at the defining level) with the
   TYPED counting law `ent_card` (card(entEvt at N)·q^A = census·q^{nN});
   `ιshH` := census·q^{−A} (the F-1 slip is out — gate B: card at N = 3 is
   128 and ιshH·|Box(3)| = (1/4)·512 = 128, never 8192); `entCount` := the
   census (the ent-degree ledger is jointly satisfiable: gate degree 2 ≤
   Went = 3); `XHDsC`/`XHDsEnt` re-keyed WEIGHT-ONLY (the [2b] height-sum
   faces proper — counts enter only through the typed [1v] burdens
   CellPolyPack/ENT-COUNT, so INIT-RAT/(J-RAT) are never decided by a
   hypothesis field and nothing double-counts); `cell_refine` is a DERIVED
   UNIT (V5-8) with the count factor DISPLAYED (Σ_c P_c·ΣGcell = T·ΣGc —
   the (q−1)² adversary dies); `kstep` carries its ∏T path-product factor;
   `cellP` REVERTED to the rev-1 sizeP wiring (state-census fields
   stLvl/stInst/stInst_card added — the frozen cellP_deg bound and the m_H3
   q = 2 falsifier both pass again); J re-keyed to the ROUTE classification
   (ALL cells of a split-route outcome, EACH ONCE — the gate Jval is nonzero).
2. **THE COUNTING-TIE TYPES (F-3; Codex 10):** `evt_card` (per-assignment
   card = mass·|Box| eventually), `box_card` (|Box(N)| = q^{nN}), ONE
   heterogeneous disjointness law over the assignment-step Σ-carrier `AStep`
   (cross-move, cross-height, cross-assignment, terminal included), and the
   cell d-face `XHDdC` (cdom exact against cntc) — the
   meas_card/no_stray/no_orphan/d4r0 suite is now derivable field-by-field.
3. **THE STEPSYS/TERMINAL CORE (Codex 1, 2):** `out_ne` re-keyed to
   realized-history PRODUCTIVITY (empty syntactic menus are allowed, as the
   note demands; a globally unrealized model now violates the law at the
   zc_ne witness); TERMINAL-FINAL TWINS typed throughout (XHDu, C15Pack,
   CtsMeasured, XHDsC/XHDdC, CellPolyPack, Refinement) via the displayed
   substitution table.
4. **FORCING + CLOSED DISPLAYS (Codex 3–6, 12–18, 20; G-2, G-3):** the rel
   generator's partition FACTORS THROUGH its polynomial by type; `moveOf`'s
   target is ENFORCED by `tcell` BY TYPE; `ValA.tbl_count` base-point-keyed
   (says something at zero counts, smuggles no height-uniformity) +
   `ent_supported` (V4-1's missing premise); σ_sel pinned as the L11
   `selRank` data (E8_rankInj semantics); the V3-3(d) reconstruction bridge +
   the u*-slot zigzag/gamTie encoding (G-3); `XHDdEnt.lands_of_realizable`;
   V2-7's three cells corrected (nonzero coordinates); `Refinement` fully
   typed (`assign_cover`); V4-12 RESTORED to the note's IF AND ONLY IF at the
   ∀-weight-system quantifier (both directions now stated, the ⟸ leg proved,
   the ⟹ leg the generating-series separation — HARD); every named
   placeholder displayed closed (CoprimeLiftPack, CtsmConclusions,
   writeHeights, MoveData/TermData/dataOf, emult, F4/F8/F9 with the Conway
   claim corrected, Hpt.take/drop); `Wsh17PackageV` displayed AS A TYPE +
   seam flag SF-2; the general SCSData/KmatHyp supply typed
   (`StageLawBurden`, a CtsmLedger field).
5. **ONE-DISPLAY SPLITS + ATTRIBUTIONS (Codex 19; G-1, G-4):** V1-8, V7-2,
   V7-3, V7-4, V7-6 split into one-display units (census now 82 = 33/43/6);
   the two E = 6t+3u+1 attributions corrected (our derived chart form — the
   note never displays that string); V3-6(c) re-pointed to the EXPORTED
   `D4R1_SUM`/`D0b_thmCtop`.

**REVISION RECORD — REV 4.** REV 3 was REJECTED by both round-3 auditors:
Codex 13 crit / 4 gap (`MOVESV_AUDIT_CODEX3_2026-07-28.md`, findings 1–17) and
Fable fresh-instance 3 crit / 2 gap (`MOVESV_AUDIT_FABLE3_2026-07-28.md`,
N-1/N-2/N-3, G-1/G-2 — with ALL SIX round-2 F-refutations verified DEAD and the
rev-3 entrance/census cluster verified correct). The round-3 disposition table
is §6.3. The structural repairs, named once here:
1. **THE HMC SPLIT (Fable N-1; ORCHESTRATOR ADJUDICATION, campaign ledger
   "N-1/HMC ADJUDICATION" 2026-07-28 — binding).** Rev 3's `XHDd` keyed its
   two-sided exactness to the DEFINITIONAL `chainCount`, which built the
   domain BY the recursion — `HMC S D` became a four-line THEOREM of every
   instance, V4-11's false-HMC toy and V4-12(c)'s fence were unsatisfiable,
   and every XHD consumer could discharge the open kernel (the ledger
   {XHD-d} vs {XHD-d, HMC} collapsed). ADJUDICATED FIX, implemented here:
   the TABLE side (T_γ = `chainCount`, G = the XHD-s sums) stays
   recursive-by-definition; the PROCESS side H(γ) is DEFINED from the
   realized MARKED EVENTS (the (vi) COMP vocabulary, MOVES 8225–8245) via
   the new carrier `TmplEvents` (§2.G: free composite-template event data,
   tied to the step layer ONLY at length 1) and the realization def `TReal`
   [RE-KEYED at REV 7, C6: exactness is keyed to the note's own direct
   count `Tgam` (the mark-census card); `TReal` is the derived notion,
   equivalent via the mark facts];
   `XHDd`'s exactness is re-keyed to the process side; **HMC is the TYPED LINK** —
   the factorization hypothesis, OPEN exactly as the note displays it
   (MOVES 8198–8204, quoted at §2.G) and now underivable (the four-line
   proof needs count-keyed exactness, which no longer exists). V4-11's toy
   and V4-12(c)'s fence are re-keyed to the process side (satisfiable
   again); clause (v)'s conditionality is restored corpus-wide.
2. **THE POOL PARAMETER (Fable N-2 = Codex-1, the convergent finding).**
   Rev 3's `Hist`/`Assign`/`cntraw`/`cntc` were pool-FREE while every count
   law quantified `∀ q₀ ∈ Pools` — forcing constant count polynomials
   (refuted by the gate: T21 = X(X−1) has eval 2 = 2 ≠ 6 = eval 3). REV 4
   pool-indexes the history layer: `Hist : ℚ → Cell → Type`; every count is
   a count AT q₀ through its history's pool index (the same box-side move
   the rev-3 census carriers already made, extended one layer down). The
   T21 check 2-vs-6 is the acceptance number, displayed at V2-4.
3. **kstep's k = 0 case (Fable N-3):** `kstep 0 τ β q₀ := if τ = β then 1
   else 0` (the Kronecker δ — empty path: ∏T = 1, empty height sum = 1);
   the frozen `LedgerIV.hmc` at k = 0 now reads kstep 1 = Σ δ·kstep 1 ✓.
   The built device instance documents the requirement
   (`MovesS/N2Carriers.lean` 101–105: "kstep 0 = 1 and the HMC scalar law
   … holds"; kstep := (…)^k).
4. **THE CODEX-ROUND-3 STATEMENT REPAIRS (findings 2–13):**
   continuing/terminal status re-keyed from letters to OUTCOMES (§2.C —
   V.6.3's m₂ has terminal o_split/o_inert AND continuing o_double);
   `evt_disj` re-keyed to DIGIT-CELL disjointness only (cross-continuation
   pairs excluded — the note allows equal f-projections across marks; the
   within-cell sum meas_card needs is the NAMED burden `MarkDisj`)
   [SUPERSEDED at REV 7, C8: the within-cell card step is the CARRIER
   [tie] `evt_disj_assign` (C.1.5 semantics, discharged at instances);
   `MarkDisj`/`MarkDisjT` are V4-10's DERIVED marked-space lemmas];
   σ_sel's entries tied BY FIELD to the taken continuation's shape-level
   rank (`hrank`, §2.D) [SUPERSEDED at REV 6, Codex5-23: the shape-level
   rank was the wrong object — `hrank` struck, the tie now the value-level
   `SelMatches` def]; `mdom` tied to XHDd's length-1 domain by the
   displayed coherence structure `MDomTie` (§2.G); `hent` upgraded from the
   lossy sum to the INJECTIVE retained-tuple code `hentCode` (SF-1 stands,
   re-verified: no MovesS law reads the field); ENT-AGG split into the
   note-exact aggregation (V3-8a, GIVEN the shallow summability face — NO
   (ENT-U)) and the ιval identification (V3-8b, GIVEN (ENT-U), where the
   note itself lists it); V4-12's iff restated at the note's EXACT
   quantifier (the FIXED XHD weight system — the ∀-E-family quantifier is
   struck; the only-if leg is recorded process-scoped [CORRECTED at REV 6,
   Codex5-31: rev 4's phrase "with a machine-checked inderivability
   witness" over-read (b′), which shows only non-sum-arithmetic-
   consequence; the ONE operative status is V4-12(b)'s — OPEN, CLAIMED
   NEITHER WAY]); `tgt_supported` gains the note's active-source
   guard; the XRB re-key is now ONE SHARED PACKAGE PARAMETER with the four
   names as face projections (never four bundle-strength premises);
   `Wsh17PackageV` carries the FULL frozen field roster (owner Props as
   parameters); XHD-w/-u laws gain the `zc` realizability guards; V6-2b's
   moves_ref splice deleted.
5. **ONE-DISPLAY PROMOTION + ROSTER HYGIENE (Codex-16; Fable G-1/G-2):**
   the pre-approved splits are PROMOTED to real unit IDs with files
   (V3-3a–d, V3-5a–c, V4-6a–c, V5-2a–c, V7-5a–c); V7-6a splits into
   V7-6a1/V7-6a2 (the ≤ 4-lemma roster rule); V7-5's act_iff leg now
   DISPLAYS its `Nonempty (Cell e τ)` step (G-1). Census: 95 units =
   32 easy / 59 medium / 4 hard (§5).

**REVISION RECORD — REV 5.** REV 4 was REJECTED by both round-4 auditors:
Codex 13 crit / 5 gap (`MOVESV_AUDIT_CODEX4_2026-07-28.md`, findings 1–18)
and Fable fresh-instance 3 crit / 2 gap (`MOVESV_AUDIT_FABLE4_2026-07-28.md`,
M-1/M-2/M-3, G-1/G-2 — with all three round-3 ADJUDICATED repairs verified
LANDED: the four-line HMC proof re-run FAILS, both N-2 gate refutations DEAD,
kstep's k = 0 δ correct, V4-12 at the note's exact quantifier; and all six
round-2 F-refutations re-armed DEAD). The round-4 disposition table is §6.4.
The structural repairs, named once here:
1. **THE POOL RIPPLE COMPLETED (Fable M-3 = Codex-1/14, the convergent
   core).** Rev 4 pool-indexed the history layer but three displays kept
   rev-3 pool-free signatures: V1-6/V1-7 are re-signatured to the pooled
   `Hist`/`massOf` (mechanical), and V7-4a's `Rep e τ := {x // S.zc x}` —
   which left the pool index UNBOUND while the frozen `MeasuredSide.Rep` is
   pool-global — is re-keyed to the PER-POOL REPRESENTATIVE FAMILY
   `Rep e τ := ∀ q₀, q₀ ∈ V.Pools → {x : S.Hist q₀ _ // S.zc x}` with the
   OFF-POOL EMPTY event value (`cellEvt … q₀ N := ∅` at q₀ ∉ Pools) — a
   RECORDED design decision (inventory slot 12), conceptual typecheck
   walked at V7-4a [SCOPE CORRECTED at REV 6, Codex5-26: the frozen
   UNGUARDED `xhd_no_orphan` (∀ (q₀ : ℚ), verified against the built law)
   FORCES ∅ off-pool only at h ∉ HDom; at h ∈ HDom the off-pool value is
   unconstrained (the guarded laws read same-pool components only) and ∅
   is the CHOSEN branch — permitted, not forced].
2. **THE TABLE-INDEX BINDING (Fable M-1, inherited since rev 2) + THE
   OUTCOME-MEMBER ROSTER (Codex-2/3/10).** `ValA.tbl_count` quantified its
   index β FREE with a β-independent right side — forcing every TargetIx
   entry (junk terminals included) equal to the datum's count; `valA_gate`
   was FALSE at the note-correct gate family (0 = 2 at q₀ = 2). REV 5 binds
   β to THE DATUM'S OWN TargetIx (`MoveData.tix`/`TermData.tix`, new §2.C
   defs — exactly as V2-5/V5-8/V7-4c already wrote it) and adds the
   off-key ZERO clauses (`tbl_offkey`/`tbl_offkeyT` — VAL(a)'s "valued
   correctly at EVERY entry": off the (D4) landing the count is 0).
   `TargetIx.term` now REQUIRES the outcome terminal (`¬ cont` — junk
   terminal columns for continuing outcomes are gone BY TYPE, Codex-3), and
   `tgtSk` is PINNED to the letter's own successor species (`tgt_sp` — the
   note's (CTS-T) "species m : s → s′ … target cell β ∈ JREF^src(s′)").
   `BlockData` gains the OUTCOME-MEMBER ROSTER `omem` (per-member size/δ/
   status tuples — DEG-CONS's tuples now EXIST as data, `odata` is
   constructible at V7-3a, Codex-2), with the per-member landing maps
   `tcellM` (CtsFamily) and the kcol coherence laws. V5-7b's (J-RAT)
   supplier is re-keyed to the bare OUTCOME quantifier (s, m, o, α) — a
   split outcome needs no chosen continuing target (Jval consumes tgt
   NOWHERE — the definitional lemma `jval_out`, V5-7a; Codex-10).
3. **HMCAug DE-TRIVIALIZED (Fable M-2 — round-3 N-1's last leg).** Rev 4's
   `∃ TE'`-quantified HMCAug was DERIVABLE from any XHD d-face (the
   identity-refinement/cooked-composite-events construction, displayed in
   the audit) — the "unrelated witness stays impossible" comment was false.
   REV 5: `HMCAug` takes the ledger's `TE` as a PARAMETER and the refined
   events are PINNED to it through the new event-transport structure
   `RefEvents` (boxEq + the event/census re-partition ties): a refinement
   re-partitions the BASE marked events by finitely-valued boundary/gap
   data — it does not mint free ones. The cooked witness now dies at
   `tevt_cover` (the audit's construction re-run at §2.G); the note's
   display (MOVES 8213–8220) is quoted at the def site.
4. **THE CODEX-ROUND-4 STATEMENT RESIDUE (findings 4–5, 7–9, 11–13).**
   `evt_disj_cell`'s key MINIMIZED to the frozen d4r0's own (Σ-embedded
   digit cell, Σ-embedded height) pair — no datum coordinate, so no
   cross-mark disjointness is claimable even in principle (Codex-4);
   `MarkDisj` gains its displayed TermData/AssignT twin `MarkDisjT`
   (terminal-cell meas_card support, Codex-5); `hentCode` LENGTH-SEEDED
   (genuinely injective on the retained (h, γ)-tuple lists) with the
   injectivity gloss SCOPED to fixed-template consumption (Codex-7 +
   Fable G-2); `XHDsEnt.mass_summable` REMOVED — the aggregate-summability
   premise is the NAMED standalone burden `EntMassSummable`, a displayed
   hypothesis of V3-8a, no longer a silent strengthening of frozen XHD-s
   (Codex-8) [SUPERSEDED at REV 7, C7: `EntMassSummable` itself silently
   STRENGTHENED the note's per-clause package — STRUCK; V3-8a's premise is
   the XHD-s shallow face `XHDsEnt`, summability DERIVED from it];
   V5-2a/c regain the explicit XHD-w premise (Codex-9); the XRB
   re-key is now a DISPLAYED Prop-typed adapter (`XHDFrame` + the four
   face-law `*_Stmt` defs + `xrbPackageOf` — shared data, Prop fields,
   Codex-11); `StepSys` gains `pools_ne` (empty-pool vacuity dead,
   Codex-12); `kmat_all` scoped to `e ∈ Icc 1 n` (Codex-13).
5. **DISPLAY/RECORD CLOSURES (Codex-15/16/17/18; Fable G-1).** The
   F4/F8/F9 `Field` instances displayed in full (no `..`), with
   `eligMenu`/`branchingRead` and the `castMove`/`castHpt`/`castAssign`
   helpers as closed defs; `BlockData.CellIdx` single-homed (V2-2 keeps
   only the instance + lemma); ALL 24 `*_Stmt` bodies of V7-2a displayed;
   design-freedom slot 2 rewritten to the operative TReal keying; V4-12's
   only-if status made self-consistent corpus-wide (OPEN, CLAIMED NEITHER
   WAY — (b′)'s honest form, §0 + V4-12(b)).

**REVISION RECORD — REV 6.** REV 5 was REJECTED by both round-5 auditors:
Codex 5 crit / 7 gap (`MOVESV_AUDIT_CODEX5_2026-07-28.md`, per-item
re-derivation: priors 5/7/8/9/10/12/13/16 + Fable M-1 REPAIRED; the
partial/open priors' residues carried into the fresh findings 21–32)
and Fable fresh-instance 0 crit / 3 gap
(`MOVESV_AUDIT_FABLE5_2026-07-28.md`, G-A/G-B/G-C — STATEMENT CONTENT
CLEAN: all round-2/3/4 refutation batteries re-armed DEAD, the three
round-4 repairs verified LANDED, census exact). The round-5 disposition
table is §6.5. The structural repairs, named once here:
1. **THE SELECTED-MEMBER TIE (Codex5-22, the round's core).** A split
   outcome's designated `tgtSk` was not required to be any roster member's
   target — `MoveData.tgt`, V7-3a's continuing statuses, and V5-7b's
   constructed split datum could select a successor ABSENT from the
   DEG-CONS roster. REV 6 adds the BlockData law `omem_sel`: for every
   continuing outcome, SOME member's status is `Sum.inr (tgtSk m o h)` —
   the (D4) designated target IS a continuing roster member; `omem_kcol`
   is demoted to its displayed length-1 corollary (§2.C).
2. **THE σ_sel RE-TARGET (Codex5-23 — the recorded §2.D hatch FIRED).**
   Rev 5's `SelRankTie` equated `MovesD.selRank % m̄` with a rank of
   (g, μ) PAIRS (`shapeRank` over `eligMenu`) — but the m̄-menu is the
   ψ-menu AT the read's own (g, μ) (`ShapeRead.mbar = len/(g·μ)`;
   `selRank` ranks ν's OWN ψ among `EligibleImage`-eligibles), so the
   equation was unsatisfiable-or-collapsing against `E8_rankInj` whenever
   two ψ-selections share (g, μ). REV 6: `hrank`/`takenGm`/`shapeRank`/
   `eligMenu` are STRUCK; `selRec` is genuine SELECTION DATA (the L11 s_r
   ranks, menu-bounded by `hmenu`); the value tie is the DEF `SelMatches`
   (label ↔ realized prefix: entry r = `selRank w ν_r % m̄_r` at the r-th
   branching read's node — MovesD's own E9 encoding, Defs.lean 528–533,
   quoted) — the ε-class membership V3-1(b)/V5-1 consume, (side, ψ)-
   faithful through E7/E8, no independent enumeration left to mismatch.
3. **THE KEY NARROWING FINISHED + THE MARKS RECORD (Codex5-21/prior-4).**
   `stepKey` now lands in the SOURCE-CELL Σ-carrier `CellOf αc` — LITERALLY
   the frozen `Cell e τ = Σ o, DCellO`'s shape, so V7-6a2's d4r0 supply is
   definitional — and the standing record is displayed: continuation-mark
   multiplicity is `emult`-carried and marked-space-only (a mark is NOT an
   `AStep` element; two marks over one assignment are ONE `AStep` point),
   while distinct (m, o) at one source are distinct COLLISION-PATTERN
   f-strata (outcome = f-data), exactly the cross-cell disjointness the
   frozen `d4r0` itself demands over its Σ-outcome `Cell` type. The
   auditor disagreement (Codex5-21 vs Fable-5's F-3 re-walk) is
   adjudicated against the frozen law's own quantifier (§2.F).
4. **RECORD/DISPLAY CLOSURES (Codex5-24..32; Fable G-A/G-B/G-C).** The
   HMCAug record SCOPED (G-A: `HMC ⟹ HMCAug` IS a ~30-line theorem —
   identity refinement + transported RefEvents — and unavoidably so for
   any faithful encoding, since the note's hypothesis is a CONDITIONAL
   whose antecedent is empty under HMC; "NOT a consequence of HMC" is
   ledger-role bookkeeping, never a logical-independence claim; the TYPE
   is unchanged); the `cellEvt` DIMENSION dite displayed with its forced-∅
   branch + V7-6a1's third no_orphan leg (G-B, inventory slot 15); V5-7b's
   accessor fixed to `J.route_cont` (G-C); the off-pool branch corrected
   to PERMITTED-AND-CHOSEN at in-domain heights (forced only at h ∉ HDom
   — Codex5-26; the design stands, the wording overclaimed); `xrbPackageOf`'s
   target re-provenanced (frozen at the MovesS wave-4 BLUEPRINT, NOT in
   the built E-phase source — Codex5-25) and the four face-law `*_Stmt`
   bodies displayed closed; ALL 24 V7-2a `*_Stmt` bodies now Lean
   expressions over a displayed name→home table (Codex5-27); the
   `writeHeights` slot projections + `castMoveT` + Refinement's [+T]
   twins displayed closed (Codex5-28); the §4.1 RatBurdens rows re-pointed
   to the real V7-5a/b/c legs (no V7-5d — Codex5-29); V4-3 restated
   PARAMETRICALLY, breaking the V4→V7 build-order cycle (Codex5-30); the
   stale REV-4 record line on V4-12's only-if leg corrected in place
   (Codex5-31); the §5 non-vacuity recap re-keyed to the operative TReal
   rule (Codex5-32). Codex5-24 (RefEvents vs the cooked witness) is
   ADJUDICATED DEAD per Fable-5's §A.2 walk (singleton-roster reduction at
   the identity refinement computed through the displayed filterMap;
   ¬HMCAug PROVED at the coupled toy for EVERY refinement) — with its
   record half absorbed into G-A's scoping. Census unchanged: 95 = 32/59/4.
[The Codex5-24 adjudication is ITSELF overturned at REV 7 (round-6 C4,
orchestrator-adjudicated): the "¬HMCAug for EVERY refinement" claim was
FALSE — see the REV-7 record, item 1.]

**REVISION RECORD — REV 7.** REV 6 was REJECTED by both round-6 auditors
against the POST-RATIFICATION corpora (`W4_SYNC_DELTAS_2026-07-29.md` — the
MovesS/MovesD sources changed under the blueprint): Codex 15 crit / 2 gap
(`MOVESV_AUDIT_CODEX6_2026-07-29.md`, C1–C15/G1–G2) and Fable 2 crit / 4 gap
(`MOVESV_AUDIT_FABLE6_2026-07-29.md` — all 14 §6.5 disposition rows verified
REAL; the two criticals are seam drift). Four rulings were
ORCHESTRATOR-ADJUDICATED (binding; rev7 charge on file). The round-6
disposition table is §6.6. The structural repairs:
1. **THE HMC/HMCAug SEPARATION CORRECTED (C4, adjudicated — Codex's
   construction verified).** The rev-5/6 claim "¬HMCAug is PROVABLE at
   V4-11's coupled toy for EVERY refinement" was FALSE: refining the
   intermediate state by WHETHER h₁ = 0 gives refined tail domains (full
   at h₁ ≠ 0; excluding h₂ = 0 at h₁ = 0) that each FACTOR — one round of
   𝒞_n refinement RESTORES the factorization, exactly the note's HMC-AUG
   display. The toy is the SEPARATION WITNESS: ¬HMC ∧ HMCAug at V4-11.
   Every ¬HMCAug claim is STRUCK corpus-wide; HMCAug's falsifiability is
   OPEN (the note's predicted falsifier: a SECOND surviving coupling —
   R2's wall channel). `HMC → HMCAug` is now the REAL UNIT V4-13 (G1).
2. **XHD-d RE-KEYED TO THE NOTE'S OWN T_γ (C6, adjudicated).** The note
   DEFINES T_γ directly (MOVES 7921–7923: "#{fresh-assignment chains from
   x realizing (γ, h)} — a finite count at each level") and states
   no-orphan/no-stray with T_γ verbatim (7947–7949). REV 7: the typed
   DIRECT-COUNT def `Tgam TE γ x h := (TE.tinst γ x h (tmplLvl γ)).card`
   (the mark census IS the chain count — marks are the realized chains;
   NOT the recursive product: T_γ = ∏ T_step stays (u-T)/HMC content);
   `XHDd` keyed to `0 < Tgam` two-sidedly verbatim; `TReal` DEMOTED to a
   derived notion with the equivalence `TReal ↔ 0 < Tgam` a §2.G lemma
   (via the mark facts; the new third [tie] `marks_realize` supplies the
   ← leg). HMC stays OPEN: no census recursion exists at composites.
3. **MARKED-SPACE DISJOINTNESS DERIVED, NOT HYPOTHESIZED (C8,
   adjudicated).** Per (iv)-MEAS (MOVES 8185–8197) the mark is ADJOINED
   to the summand and DETERMINES its (m, o, β, height-class) reading —
   V4-10's marked Σ-carrier now carries that reading law, and
   `MarkDisj`/`MarkDisjT` are the DERIVED marked-space lemmas' names
   (V4-10), REMOVED as open hypotheses from V7-6a1/V7-1/§5. The
   within-cell CARD step of meas_card rides the new CtsMeasured [tie]
   `evt_disj_assign`(+T): distinct fresh assignments occupy disjoint
   residue boxes — C.1.5 counting semantics, discharged at the real
   instance, NOT PART-2's mark multiplicity (which stays f-unclaimed).
4. **THE LANDING TIE SCOPED TO THE DESIGNATED MEMBER (C3, adjudicated —
   the round-6 quantifier read overrules rev 6).** `tcellM_tgt`'s ∀-form
   forced EVERY same-skeleton roster member to the designated tcell —
   unsupported for multi-continuing outcomes. REV 7: the ∃-form
   `tcellM_sel` (CtsFamily): SOME roster position with the designated
   target skeleton lands BY the (D4) map — the [tie] survives for THAT
   member; BlockData.omem_sel is its projection; n = 3 unaffected.
5. **SELECTION MADE LOAD-BEARING + THE BRANCHING RE-KEY (C1, C2).**
   `EntranceCut` gains `lands_sel : lands i → SelMatches ε i` (cuts fail
   BY TYPE if selection-ignoring); `CtsMeasured` gains `ent_sel` (sibling
   labels differing only in selRec have DISJOINT mark-census realizations
   at the defining level — the μ̂-additivity face "distinct concrete ε
   give distinct marked pairs", typed). `IsBranchingRead` (2 ≤ m̄, an
   upper-bound key) is renamed `IsBranchSlot` — the SLOT roster — and the
   REALIZED key is the new `RealizedBranching` (≥ 2 realized eligible
   continuations: MovesD's `EligibleImage` census at the read's node,
   the object `selRank` ranks; E6/E7 give Realized → Slot); `SelMatches`
   pins EVERY slot read (surplus slots carry the canonical rank — zero
   information; realized-branching reads carry the note's σ_sel).
6. **THE SOLVE'S HMC PREMISE + PREMISE HYGIENE (C5, C7, C9).**
   `SolveCond_Stmt` gains the HMC antecedent (MOVES 8005 + 8222–8224:
   the factored solve is HMC-conditional); `EntMassSummable` is STRUCK —
   V3-8a's convergence premise is the XHD-s shallow face itself
   (`XHDsEnt`; summability DERIVED via the census's uniform box bound);
   `AVRec_Stmt`/`SolveCond_Stmt` scope to the ledger's OWN `L.RB`/`L.hK`
   (new CtsmLedger data fields) — the ∀-(RB, hK) closures struck.
7. **CLOSURE FOR REAL (C10, C11, C12).** `AStep`/`CellOf`/`stepKey`/
   `evtOfStep` are DISPLAYED closed defs over the new sub-carrier
   `CtsCells` (CtsMeasured extends it — no comment-defs under
   evt_disj_cell); the §2.D forward references are GONE — `readOfLetter`/
   `shapeOfSlots` are closed RAW Defs-layer defs and `writeHeights?`/
   `EntTemplate.of?` are Option-valued classical-dite defs whose
   TOTALITY is V3-3d/V3-3b's named theorem (consumers read displayed
   `Option.elim` defaults; no proof term is forward-referenced);
   `XhdS_Stmt`'s "(the same three clauses …)" parenthesis replaced by
   the GcellT triple VERBATIM.
8. **THE W4-SYNC SEAM RE-KEYS (C13/C14/C15 = Fable CRIT-1/2, GAP-1/2).**
   `wsh17_pin` is a projection-DEF in built MovesS (nothing to
   instantiate): the NEW UNIT V7-8 carries `W17ii` at the chain's own
   carriers as the scheduled proof duty (sorry-gated at EXACTLY that type
   until the wave-4 assembly discharges it); built `RatBurdens` REQUIRES
   `jPCell/jcell_ok/jcell_interp/jcell_sum` — §2.H/V5-7b/V7-5a leg (b)
   re-keyed so `CellPolyPack` × the weight-only Gcell sums SUPPLY the
   per-cell J tables over `M.Cell` (no parallel type is the deliverable);
   the NEW UNIT V7-9 supplies `MovesS.PolyGeomLaws` (tCount's event-side
   identification — the recorded MovesV duty, `ValA.tbl_count` the named
   carrier); §4.2 gains the `legs_read` row (the map's completeness claim
   true again). Stale MovesD/MovesS line cites refreshed (Fable GAP-3);
   `branchMenuCard`/`branchingRead?`/`bIdx` restructured Option-indexed
   (no `Inhabited MovesD.ShapeRead` exists — Fable GAP-4).
   Census: 98 = 32 easy / 62 medium / 4 hard (+V4-13, +V7-8, +V7-9).

## §0 Charge, status, and the conditionality banner

**WHAT THIS CORPUS IS.** §V-TABLES = assembly note [1v]-COND: ONE fixed
p-independent state space of syntactic branch-cells (V.2), one polynomial table
family T counting per-cell fresh-assignment transitions (V.2), and ONE measured
theorem — CTS-M (V.1) — typing how counts (T), fixed-height weights (g),
resummed weights (G), entrance masses (ι), and marked masses (μ̂) compose,
EACH CLAUSE GIVEN EXACTLY its V.1-ledger hypothesis set. Every left-hand side
is a MARKED-BRANCH mass μ̂ (μ̂(E) := Σ_η μ({f : (f,η) ∈ E}) — a sum over marks
BY DEFINITION), never an f-event mass and never a density.

**THE CONDITIONALITY BANNER (binding on every unit and on the corpus record).**
- XHD (XHD-w/-d/-s) + (XHD-u) + (ENT-U): OPEN, owner [2b] §H-DOMAINS (its six
  H.6 fences block [1v]-FULL). In Lean they are the §2.B/§2.G typed hypothesis
  structures; NO unit proves them; the discharge is the separate recorded
  event [1v]-FULL (V1-5's `IsFullDischarge` — bookkeeping, no mathematics).
- (v) HMC: OPEN KERNEL (probe specced-and-pinned at V.4, RUN status per the
  note: NOT run at freeze). Typed at §2.G as the LINK between the
  process-side domain (defined from the realized marked events — the N-1
  adjudication) and the table side; NO unit proves it, and REV 4 restores
  its underivability: the rev-3 interface PROVED it (XHDd's exactness was
  keyed to the definitional chain count — the four-line collapse Fable N-1
  displayed), which the process-side re-key repairs. (HMC-AUG) a SEPARATE
  named Prop (body DISPLAYED, §2.G; REV 5, M-2: it takes the ledger's
  `TmplEvents` as a PARAMETER and pins the refined events to it through
  `RefEvents` — the rev-4 ∃-form was derivable from the XHD d-face).
  SCOPE (REV 6, Fable G-A; RE-SCOPED at REV 7, C4): "SEPARATE" is
  LEDGER-ROLE bookkeeping (its own named line item, cited separately,
  assumed nowhere) — NOT logical independence: `HMC ⟹ HMCAug` is now the
  PROVED-BY-DESIGN unit V4-13 (identity refinement — the vacuous-repair
  case, inherent to the note's conditional), while V4-11's coupled toy is
  the SEPARATION WITNESS the other way: ¬HMC ∧ HMCAug hold there (the
  h₁ = 0 refinement restores the factorization — one 𝒞_n round, exactly
  the note's HMC-AUG display), so HMCAug is STRICTLY WEAKER than HMC.
  No ¬HMCAug instance is claimed anywhere (the rev-5/6 "¬HMCAug at the
  toy" was FALSE — C4); HMCAug's falsifiability is OPEN, its predicted
  falsifier the note's own "second surviving coupling — R2's wall
  channel". Consumed by nothing; assumed nowhere.
- ENT-COUNT, (ENT-U), INIT-RAT: named burdens of clause (iii) — statements
  typed, INIT-RAT a theorem-under-hypotheses unit (V3-9c).
- (J-RAT)/CL-18: owner [1v] (with [2b] on the height-sum face) — THE PLAN-SYNC
  deliverable this corpus records on the owner side: the per-cell tables
  J_{τ,o} ∈ ℚ(q) ENTRYWISE, beyond PART-1's total (layer V5, units V5-7*).
- (ii-c) ACTIVE-VALUE: a finite per-(n, q₀) check (MovesS's AVAgree shape),
  recorded, never a blanket det ≠ 0 claim.
- Inherited: §C (via MovesC/HC-2 — the C.1.5(1)/TYP(b) faces ride as the typed
  `C15Pack`, owner tag §C/HC-2), §D4-R (MovesD — PROVED core consumed),
  [2a] §M-SPECIES (MovesSp — PROVED, so the note's "[2a] pending" inheritance
  is DISCHARGED against the Lean corpus at n = 3; recorded as an upgrade,
  not a deviation: the note's conditionality only shrinks).
- ESCAPE(E0): [3]'s duty (MovesS.EscapeE0); cited only inside (vi)'s
  conditional solve sentence, never claimed here.
- [3t] fence: VP, TB-CAP, TREE-EXP/ONE-F, tree pruning are NOT in this corpus;
  terminal outcome labels are consumed as ABSORBING COLUMN LABELS only
  (`VLabel`, §2.A). Equating any μ̂ object of this corpus with an f-event mass
  is a TYPE ERROR except through [3t]'s displayed conversion (MovesT, wave 4).

**WHAT IS PROVED OUTRIGHT HERE (no hypothesis fields)** — SCOPED PER UNIT
(A-6 repair; the banner sentence carries the same scope its units do): (U-A)
as the note proves it (V1-6, GIVEN only the typed §C-supply pack — the note's
own GIVEN); the clause-(i) meet lemma (V2-3); the entrance-template
finiteness (V3-4, now intrinsic — see C12); ENT-AGG's finite half (V3-7);
(ii-a)/(ii-b) given ValA's count semantics (V4-1/2); PART-2's n = 3 surplus
≡ 0 over the gate rosters + the general lemma GIVEN the displayed
continuing-size-≥-2 premise (V4-8); the (v)-naming sentence's IF leg at the
note's OWN quantifier — HMC ⟹ the factorization identity AT THE FIXED XHD
weight system, every template (V4-12(a); the ONLY-IF leg is process-scoped,
consumed by nothing, and its interface-derivability is OPEN, CLAIMED
NEITHER WAY — (b′) shows only that it is not a SUM-ARITHMETIC consequence;
the coincidence witness and the false-HMC failure fence are
machine-checked, V4-12(b′)/(c)) [REV 5, Fable G-1: this sentence and
V4-12(b) now carry (b′)'s one honest status]; and the V.6
gate layer
**EXCEPT V6-4c** (V6-1a..V6-4b:
closed forms, PART-1 count faces, DEG-CONS rosters, domain normal form, the
gate-B dyadic arithmetic and two-history discipline; the census units V6-1c/
V6-3b at all nine sealed prime-power points via `F4/F8/F9`) — decide/ring/
norm_num-native. V6-4c is NOT in this list: its threshold derivation carries
the typed `hensel : CoprimeLiftPack` premise (fields displayed at §2.I).

## §1 Consumption map (all PROVED corpora; owner tags for open vocabulary)

| consumed | what | where used |
|---|---|---|
| `MovesSp` (PROVED, dual-accepted rev 5) | `Species` (SP.1 datum, heights forgotten BY TYPE), `InCatalogue`/`SnRaw`, `Succ`/`Out`/`SuccStep` (SP-OUT syntactic menus, NO field evaluated), `Verdict` (bare labels), `EntranceShape` (the species-word entrance carrier with height SLOTS — now the V3-3 bridge TARGET), `CollapsedWalk`/`collapseRuns` + the `rankNat` DAG idiom (SP4_dagWords), SP2 finiteness (`SP2_finThm`), the 53-catalogue + SP6 menu roster (kernel-decided) | §2.C skeletons + (D1) menus; V2-1; the (iii) template layer §2.D/V3-3/V3-4 (EntTemplate's WF fields mirror `EntranceShape.hMem/hChain/hEntry` — the A-3 tie); V4-8's roster; clause (i)'s [2a] discharge |
| `MovesD` (PROVED core, rev 9 seam split) | `Shape n`/`ShapePrefix`/`ShapeRead` (L3 rev 9: retains per-read (h, u*) — fields `h`, `ustar`; per-read `(g, μ)` — fields `g`, `μ`), `Presented`/`PrefIdx`/`Presented.fiber`/`mult`, `Box`, `D4R1_SUM` (D10), `D0b_thmCtop`, `mult_sum` (D11a), `D4R4_all`, `ShapePrefix.A`/`A'`/`W`, `ShapeRead.len`/`.mbar`, the L5/L11 eligibility apparatus BY NAME: `EligibleImage`, `RanchImage` (REV 7: `RealizedBranching`'s census carrier — C2), `selRank` (L11's s_r), `eligible_card_le` (E6), `E5_gmuLe`, `E8_rankInj`/`E9_encInj`, `ShapePrefix.gamTie` (the u*-determinacy law) | §2.D entrance shapes ε (P̂ concrete WITH heights; entry-read/eligibility WF ties); ι's counting-native def; A(ε) = A(P̂), W_ent(ε) = W(P̂); the marked-event census V5-1 |
| `MovesS` core (E-phase built, POST-RATIFICATION — `W4_SYNC_DELTAS_2026-07-29.md` binding at REV 7) | `Qq`, `PolyGeom`, `OKat`/`evalAt`, `MuHat`, `TableShape`, `MeasuredSide`, `RatBurdens` (incl. the NEW per-cell `jPCell/jcell_*` — C15), `LedgerIV`, `DegCons`, `KmatHyp`, `SCSData`, `EscapeE0`, `AVAgree`, and the ratification names `W17ii` (V7-8's target type), `LegAgree`/`consumedDeltas` (§4.2's legs_read row — owner [3]'s, cited not stated), `PolyGeomLaws` (V7-9's target) | §4 SEAM-SUPPLY: layer V7 instantiates; §2 reuses the ℚ(q) plumbing verbatim (NO re-derivation) |
| `MovesC` (PROVED) — owner tag §C/HC-2 | Theorem C(b) engine; C.1.5(1)/TYP(b) have NO standalone Lean form yet | the `C15Pack` typed supply for (U-A) (§2.B); each field cites its §C display; discharge = HC-2 territory |
| owner [2b] §H-DOMAINS | XHD-w/-u/-d/-s (incl. the cell and shallow/entrance faces), (ENT-U), (JC-INV) | typed hypothesis structures §2.B/§2.G; NEVER proved here |
| owner [3t] → MovesT | VP/TB-CAP/TREE-EXP/ONE-F/(SIB) | absent; absorbing labels only (`VLabel`) |
| owner [3] MovesS | ESCAPE(E0), the solve | cited in (vi)'s solve sentence via `MovesS.EscapeE0`/`DetHyp` |

Ownership fence, restated binding: this corpus does NOT own and nowhere
re-derives VP, TB-CAP, TREE-EXP/ONE-F (the SOLE marked→per-f conversion), the
nine-input ledger's probabilistic reading (CL-5, [3] RS.PRE), or exhaustion
([5]). K_e's construction as a MATRIX is MovesS's (`Kmat`); this corpus
supplies its ENTRY tables and their laws.

DAG position: MovesV consumes MovesSp + MovesD + MovesS-core (+ MovesC via the
typed pack); it is consumed by MovesS's wave-4 seam (§W4-SYNC) and MovesT.
Import direction `MovesV → MovesS.Defs/Interfaces` is ACYCLIC: MovesS's core
never imports MovesV (its intended-instance comments become real here).

## §2 The Defs layer — `MovesV/Defs.lean` (+ `DefsGate.lean` for V.6 data)

Declaration order below is normative AND Lean-plausible (C4 repair: `VLabel`
precedes `StepSys`; the `XHD` bundle follows XHDd/XHDs in §2.G; no invalid sum
types remain). Defs are sorry-free; every law with content is a UNIT, not a
Defs field, EXCEPT hypothesis-package fields (obligations by design, per the
doctrine) and the displayed data-tie fields marked [tie]. `open LeanUrat.MovesS
(Qq PolyGeom OKat evalAt MuHat)` — the ℚ(q) plumbing is reused, never rebuilt.
NO placeholder survives this revision: §2.J is the checklist (C29 repair).

### 2.A The height apparatus (V.0's ambient objects, "defined here so the package is CLOSED and refutable")

```lean
namespace LeanUrat.MovesV
open LeanUrat.MovesS (Qq PolyGeom OKat evalAt MuHat)

/-- A height point in D ℕ-slots (V.0: "the tuple of its reads' ℕ-height
parameters (the parameters [2a] SP.1 forgets; d_i height slots at step i)"). -/
abbrev Hpt (D : ℕ) := Fin D → ℕ

/-- concatenation of height points (used by templates and HMC). -/
def Hpt.append {D₁ D₂ : ℕ} (h₁ : Hpt D₁) (h₂ : Hpt D₂) : Hpt (D₁ + D₂) :=
  Fin.append h₁ h₂

/-- the Fin-append splitters (Codex-18: displayed, closed — no longer a
"defs in the E-phase file" pointer). -/
def Hpt.take {D₁ D₂ : ℕ} (h : Hpt (D₁ + D₂)) : Hpt D₁ :=
  fun i => h (Fin.castAdd D₂ i)
def Hpt.drop {D₁ D₂ : ℕ} (h : Hpt (D₁ + D₂)) : Hpt D₂ :=
  fun j => h (Fin.natAdd D₁ j)

/-- prime-power evaluation points (was dangling in rev 1 — A-7 repair). -/
def IsPP (q₀ : ℚ) : Prop := ∃ (p k : ℕ), p.Prime ∧ 0 < k ∧ q₀ = (p : ℚ) ^ k

/-- (XHD-w)'s exponent: "E affine in h with positive weights". The weights are
DATA with a typed positivity law — a weight-0 (h-degenerate) instance is
UNSATISFIABLE, per the wave-2 doctrine. CHART CONVENTION (C3 repair, binding):
every `AffineE` of this corpus is declared IN COORDINATES WHERE ITS
COEFFICIENTS ARE NATURAL; where the note displays an exponent in other
coordinates (the A2 (h₀,h₂) display), the coordinate change is a DEFINITION
(`A2chart`, §2.I) and the display is re-derived THROUGH it (V6-2b) —
division-free, note-faithful. -/
structure AffineE (D : ℕ) where
  const : ℕ
  coeff : Fin D → ℕ
  pos   : ∀ i, 1 ≤ coeff i

def AffineE.eval {D : ℕ} (E : AffineE D) (h : Hpt D) : ℕ :=
  E.const + ∑ i, E.coeff i * h i

/-- V.0: "a LINEAR SET in ℕ^D is L(h₀; P) := {h₀ + Σ_{v∈P} n_v·v : n_v ∈ ℕ}
with base h₀ ∈ ℕ^D and a FINITE period list P" — bases and periods EXPLICITLY
LISTED (the "congruence-class translates" gloss is struck). -/
structure LinSet (D : ℕ) where
  base    : Hpt D
  periods : List (Hpt D)

def LinSet.Mem {D : ℕ} (L : LinSet D) (h : Hpt D) : Prop :=
  ∃ c : Fin L.periods.length → ℕ,
    h = fun i => L.base i + ∑ j, c j * (L.periods.get j) i

/-- THE DISJOINT-COMPONENT CONVENTION (rev 3, pass-2 finding 1), AS A TYPE:
every semilinear domain this corpus consumes is a LISTED PARTITION — the
listed linear sets pairwise disjoint. Overlapping lists are UNSATISFIABLE. -/
structure SemilinPart (D : ℕ) where
  comps : List (LinSet D)
  disj  : comps.Pairwise (fun L L' => ∀ h, ¬(L.Mem h ∧ L'.Mem h))

def SemilinPart.Mem {D : ℕ} (S : SemilinPart D) (h : Hpt D) : Prop :=
  ∃ L ∈ S.comps, L.Mem h

/-- Absorbing column labels: (e, f) with e·f ≤ n — verdict SEMANTICS is [3t]
VP's, "consumed here only as absorbing column labels"; this carrier is also
MovesS's R20 pin verbatim (TableShape.vEquiv will be `Equiv.refl`-keyed).
Declared HERE so `StepSys.MoveT` can reference it (C4 declaration-order fix). -/
abbrev VLabel (n : ℕ) := {ef : ℕ+ × ℕ+ // (ef.1 : ℕ) * (ef.2 : ℕ) ≤ n}
```

### 2.B The step system, the (U-A) supply pack, and the first two XHD faces (V.0; owner tags per package)

XHD is stated over the STEP SYSTEM `StepSys` (§2.C defines its intended
instance; the structures are parameterized so [2b]'s eventual discharge
re-keys once). The RAW primitives are HISTORY-INDEXED — without that, (u-R)
and (U-A) would be contentless (the pass-1/2 lumpability findings).
**REV-4 CHANGE (N-2 = Codex-1, THE POOL PARAMETER):** the history layer is
POOL-INDEXED — `Hist : ℚ → Cell → Type`, histories of the process AT the
pool q₀ (over F_{q₀}) — and every count/mass primitive reads its pool
through its history argument. The rev-3 defect: `Assign`/`cntraw` had no q₀
anywhere, so `∀ q₀ ∈ Pools`-quantified count laws forced ONE natural to
equal T.eval at every pool — every table polynomial CONSTANT, refuted by
T21 = X(X−1) (eval 2 = 2 ≠ 6 = eval 3, the V2-4 acceptance numbers). The
census carriers (§2.F) already carried q₀ box-side; this extends the same
index one layer down. TWO-HORN CLOSURE (N-2's): `u_R_cnt` now compares
histories AT THE SAME POOL only — no cross-prime count equality is forced.
REV-2 CHANGES (C1/C2/A-2/A-5 repairs), REV-3 AMENDMENTS (Codex-1/2: `out_ne`
re-keyed to productivity; terminal twins throughout): non-vacuity laws
`cell_ne`/`out_ne`/`zc_ne` typed in; the history-extension operation `ext`
added (the carrier the chain
recursion requires — the normative-Defs amendment A-2 named); `cntraw` is now
a DEF, tied to `Assign` cardinality by definition; the rev-1 `inv` stub is
DELETED (design-freedom slot (1) resolved: `C15Pack` already carries the
pinned inventory carrier — nothing in the note demands a slot on `StepSys`).

```lean
/-- The index vocabulary + measured primitives XHD quantifies over (V.0:
"for every step datum (m, o) with source cell α and target cell β, and every
height point h"). `Hist α` = admissible histories/representatives reaching a
concrete state of α (x AND its history — (u-R)'s quantifier); `Assign` = the
fresh-assignment fiber realizing (m, o, β) at h from x; `massOf` = the
per-assignment C.1.5 conditional mass carrier; `ext` = history extension by
one realized assignment (V.0's chain vocabulary: "fresh-assignment CHAINS
from x" — a chain IS iterated extension). NON-VACUITY (C1, re-keyed at REV 3
per Codex-1): the note's 𝒞_n is nonempty (the root skeleton); every cell has
a (ZC)-realizable history (post-deletion cells are realized states — V.2's
deletion convention); and every (ZC) history is PRODUCTIVE (PART-1's mass 1
forces a realized continuing or terminal fresh assignment — `out_ne` below,
AFTER the Assign fields it constrains). The empty model violates `cell_ne`;
the all-empty-fibers model violates `out_ne`.
TERMINAL TWIN CONVENTION (REV 3, Codex-2): every per-move law of §2.B–§2.H
has a terminal-final twin under the SUBSTITUTION TABLE
  Move ↦ MoveT · dim ↦ dimT · Assign ↦ AssignT · finA ↦ finAT ·
  cntraw ↦ cntrawT · massOf ↦ massOfT · moveOf ↦ moveOfT · dataOf ↦ dataOfT ·
  evtOf ↦ evtOfT · stabLvl ↦ stabLvlT · cellOfA ↦ cellOfAT · cdom ↦ cdomT ·
  cntc ↦ cntcT · Gcell ↦ GcellT (targets: the absorbing label v, no ext, no
  target cell) —
twins are DISPLAYED fields (suffix T), written out in full where short and
marked [+T] where the substitution is verbatim. -/
structure StepSys (n : ℕ) where
  Cell  : Type                        -- 𝒞_n, symbolic, p-independent BY TYPE
  finC  : Fintype Cell
  cell_ne : Nonempty Cell                              -- [C1 non-vacuity]
  Move  : Cell → Cell → Type          -- continuing step data (m, o) : α → β
  MoveT : Cell → VLabel n → Type      -- terminal-final step data (rev-4 exit
  finM  : ∀ α β, Fintype (Move α β)   --   objects; β_k := absorbing label)
  finMT : ∀ α v, Fintype (MoveT α v)
  dim   : ∀ {α β}, Move α β → ℕ       -- the step's height-slot count d_i
  dimT  : ∀ {α v}, MoveT α v → ℕ
  Pools : Set ℚ
  pools_ne : Pools.Nonempty              -- [REV 5, Codex-12: Pools = ∅
                                         --  satisfied every pool-guarded law
                                         --  vacuously (hist_ne/zc_ne/out_ne,
                                         --  XHD-w/-u, the TE ties); the
                                         --  degenerate instance now violates
                                         --  a field. V1-8a instantiates it.]
  pools_pp : ∀ q₀ ∈ Pools, IsPP q₀
  pools_gt_one : ∀ q₀ ∈ Pools, (1 : ℚ) < q₀
  Hist  : ℚ → Cell → Type             -- [REV 4, N-2: histories AT the pool q₀]
  hist_ne : ∀ q₀ ∈ Pools, ∀ α, Nonempty (Hist q₀ α)
  zc    : ∀ {q₀ α}, Hist q₀ α → Prop  -- (ZC)-satisfying realizable prefixes
  zc_ne : ∀ q₀ ∈ Pools, ∀ α, ∃ x : Hist q₀ α, zc x    -- [C1 non-vacuity]
  Assign : ∀ {α β} (m : Move α β) {q₀}, Hist q₀ α → Hpt (dim m) → Type
    -- [N-2: the fresh-assignment fiber AT q₀ — the count layer is per-pool
    --  THROUGH the history index; no law compares fibers across pools]
  finA   : ∀ {α β} (m : Move α β) {q₀} (x : Hist q₀ α) h, Fintype (Assign m x h)
  AssignT : ∀ {α v} (m : MoveT α v) {q₀}, Hist q₀ α → Hpt (dimT m) → Type
  finAT  : ∀ {α v} (m : MoveT α v) {q₀} (x : Hist q₀ α) h, Fintype (AssignT m x h)
  ext : ∀ {α β} (m : Move α β) {q₀} (x : Hist q₀ α) (h : Hpt (dim m)),
    Assign m x h → Hist q₀ β          -- [A-2; extension stays AT the pool]
  ext_zc : ∀ {α β} (m : Move α β) {q₀} (x : Hist q₀ α) (h) (a : Assign m x h),
    zc x → zc (ext m x h a)           -- extension preserves realizability
  massOf : ∀ {α β} (m : Move α β) {q₀} (x : Hist q₀ α) (h : Hpt (dim m)),
    Assign m x h → ℝ                  -- the C.1.5 fresh-volume ratio AT q₀
                                      -- (the pool rides the history index —
                                      --  the rev-3 free ℚ argument is out)
  massOfT : ∀ {α v} (m : MoveT α v) {q₀} (x : Hist q₀ α) (h : Hpt (dimT m)),
    AssignT m x h → ℝ
  out_ne : ∀ q₀ ∈ Pools, ∀ α (x : Hist q₀ α), zc x →
    (∃ β (m : Move α β) (h : Hpt (dim m)), Nonempty (Assign m x h)) ∨
    (∃ v (m : MoveT α v) (h : Hpt (dimT m)), Nonempty (AssignT m x h))
    -- [RE-KEYED at REV 3 (Codex-1's both horns): PRODUCTIVITY at realized
    -- histories, not menu-nonemptiness. The note does NOT assert every
    -- syntactic menu nonempty (empty menus matter at the seam; "a species
    -- inadmissible at a particular p keeps its label and contributes empty
    -- landing sets") — so no ∀-menu claim survives. What the note DOES
    -- realize: PART-1's mass 1 at every (ZC) history forces at least one
    -- realized fresh assignment (continuing or terminal) from it. The
    -- all-empty-Assign adversary now violates out_ne at the zc_ne witness.]

/-- T(h) from x — a DEF, not data (C2 repair: the count IS the Assign
cardinality; nothing to tie). REV 4 (N-2): a count AT x's pool — the value
at q₀ = 2 and the value at q₀ = 3 are counts of DIFFERENT fibers (histories
over F₂ vs F₃); `tbl_count`'s per-pool valuation is now satisfiable at
non-constant tables (the T21 gate check, V2-4). -/
def StepSys.cntraw {n} (S : StepSys n) {α β} (m : S.Move α β) {q₀}
    (x : S.Hist q₀ α) (h : Hpt (S.dim m)) : ℕ :=
  @Fintype.card (S.Assign m x h) (S.finA m x h)
def StepSys.cntrawT {n} (S : StepSys n) {α v} (m : S.MoveT α v) {q₀}
    (x : S.Hist q₀ α) (h : Hpt (S.dimT m)) : ℕ :=
  @Fintype.card (S.AssignT m x h) (S.finAT m x h)

/-- (U-A)'s §C supply, TYPED (V.0 "WHAT §C ACTUALLY SUPPLIES, displayed"):
C.1.5(1) gives per fresh assignment vol_nom(E_fresh) = q^{−#(strip pins)} ·
∏_slots (alphabet size)^{−1}, and BOTH factors are functions of the read's
NOMINAL DIGIT INVENTORY (C.1(ii)) — never of which values the cell pins.
Owner §C/HC-2; each field cites its display. -/
structure C15Pack (n : ℕ) (S : StepSys n) where
  Inv   : Type
  invOf : ∀ {α β} (m : S.Move α β) {q₀}, S.Hist q₀ α → Hpt (S.dim m) → Inv
  invOfT : ∀ {α v} (m : S.MoveT α v) {q₀}, S.Hist q₀ α → Hpt (S.dimT m) → Inv
  F     : Inv → ℚ → ℝ                 -- the common conditional-mass functional
  mass_factors : ∀ {α β} (m : S.Move α β) {q₀} (x : S.Hist q₀ α)
    (h : Hpt (S.dim m)) (a : S.Assign m x h), q₀ ∈ S.Pools → S.zc x →
    S.massOf m x h a = F (invOf m x h) q₀
  mass_factorsT : ∀ {α v} (m : S.MoveT α v) {q₀} (x : S.Hist q₀ α)
    (h : Hpt (S.dimT m)) (a : S.AssignT m x h), q₀ ∈ S.Pools → S.zc x →
    S.massOfT m x h a = F (invOfT m x h) q₀
    -- [+T, Codex-2: the note's (U-A)/C.1.5(1) covers the final terminal read
    -- exactly as it covers continuing reads — same inventory functional F]
  -- [C.1.5(1) + TYP(b): the mass is q^{−pins(inv)}·∏ alph(inv)⁻¹; the
  -- factored NUMERIC form is a second field the E-designer adds if a unit
  -- needs it; `mass_factors` alone carries (U-A)'s derivation.]

/-- (XHD-w) WEIGHTS, typed: per step datum a monomial g = q^{−E(h)}, E affine
positive, EQUAL to the per-assignment C.1.5 ratio at h — "the conditional
mass, given the source cylinder at ANY representative of α under ANY
admissible history reaching it, of one fresh assignment realizing (m, o, β)
at h". Indexed by SOURCE AND TARGET cells (pass-6 concern 1). REV 4
(Codex-12): the laws carry the `zc` REALIZABILITY GUARD — the note
quantifies over "ANY admissible history reaching it", never junk `Hist`
elements (the `C15Pack.mass_factors` pattern, now uniform). Owner [2b]. -/
structure XHDw (n : ℕ) (S : StepSys n) where
  E : ∀ {α β} (m : S.Move α β), AffineE (S.dim m)
  ET : ∀ {α v} (m : S.MoveT α v), AffineE (S.dimT m)
  w_eq : ∀ {α β} (m : S.Move α β) {q₀} (x : S.Hist q₀ α) (h : Hpt (S.dim m))
    (a : S.Assign m x h), q₀ ∈ S.Pools → S.zc x →
    S.massOf m x h a = (q₀ : ℝ) ^ (-((E m).eval h : ℤ))
  wT_eq : ∀ {α v} (m : S.MoveT α v) {q₀} (x : S.Hist q₀ α) (h : Hpt (S.dimT m))
    (a : S.AssignT m x h), q₀ ∈ S.Pools → S.zc x →
    S.massOfT m x h a = (q₀ : ℝ) ^ (-((ET m).eval h : ℤ))

/-- the derived one-step weight (a def, not a field): g^{α,β}_{m,o}(h)(q₀).
Pool-explicit BY DESIGN — the weight formula is symbolic; only masses ride
histories. -/
noncomputable def XHDw.g {n} {S : StepSys n} (X : XHDw n S) {α β}
    (m : S.Move α β) (h : Hpt (S.dim m)) (q₀ : ℚ) : ℝ :=
  (q₀ : ℝ) ^ (-((X.E m).eval h : ℤ))

/-- (XHD-u) UNIFORMITY (rev 2, findings 2–3), typed. (u-R): ratio and count
depend on x and its history ONLY through (α, β, m, o, h). (u-T): the count is
one h-independent value per step ON the one-step domain; the RAW field below
demands it where both heights are realized, and the domain-conditional form
is DERIVED (V1-3's exactness + XHDd.no_stray) — no named `u_T_dom` object
exists or is pointed to (A-7 repair). Owner [2b]; NOT §C-derivable (V.0's
honest split — the fence unit V1-7 exhibits a C15Pack model violating u_R). -/
structure XHDu (n : ℕ) (S : StepSys n) where
  -- REV 4: SAME-POOL comparisons only (N-2's two-horn closure: no
  -- cross-prime count equality is forced) + zc guards (Codex-12: the note
  -- compares "representatives … under admissible histories", never junk):
  u_R_mass : ∀ {α β} (m : S.Move α β) {q₀} (x x' : S.Hist q₀ α)
    (h : Hpt (S.dim m)) (a : S.Assign m x h) (a' : S.Assign m x' h),
    q₀ ∈ S.Pools → S.zc x → S.zc x' →
    S.massOf m x h a = S.massOf m x' h a'
  u_R_cnt : ∀ {α β} (m : S.Move α β) {q₀} (x x' : S.Hist q₀ α)
    (h : Hpt (S.dim m)), q₀ ∈ S.Pools → S.zc x → S.zc x' →
    S.cntraw m x h = S.cntraw m x' h
  u_T : ∀ {α β} (m : S.Move α β) {q₀} (x : S.Hist q₀ α)
    (h h' : Hpt (S.dim m)), q₀ ∈ S.Pools → S.zc x →
    0 < S.cntraw m x h → 0 < S.cntraw m x h' →
    S.cntraw m x h = S.cntraw m x h'
  -- terminal twins (Codex-2: XHD-u covers the final terminal read):
  u_R_massT : ∀ {α v} (m : S.MoveT α v) {q₀} (x x' : S.Hist q₀ α)
    (h : Hpt (S.dimT m)) (a : S.AssignT m x h) (a' : S.AssignT m x' h),
    q₀ ∈ S.Pools → S.zc x → S.zc x' →
    S.massOfT m x h a = S.massOfT m x' h a'
  u_R_cntT : ∀ {α v} (m : S.MoveT α v) {q₀} (x x' : S.Hist q₀ α)
    (h : Hpt (S.dimT m)), q₀ ∈ S.Pools → S.zc x → S.zc x' →
    S.cntrawT m x h = S.cntrawT m x' h
  u_TT : ∀ {α v} (m : S.MoveT α v) {q₀} (x : S.Hist q₀ α)
    (h h' : Hpt (S.dimT m)), q₀ ∈ S.Pools → S.zc x →
    0 < S.cntrawT m x h → 0 < S.cntrawT m x h' →
    S.cntrawT m x h = S.cntrawT m x h'
```

`Template`/`XHDd`/`XHDs` (and their cell/entrance faces) need the path and
state-space vocabulary; they follow in §2.G, and THE `XHD` BUNDLE IS DECLARED
THERE, after its components (C4 declaration-order fix) — keeping V.0's own
order (the package is stated at V.0 but quantifies over templates constructed
at V.2).

### 2.C The state space 𝒞_n (CTS-S) and the computed-partition deliverable (D1)–(D4)

```lean
/-- A SKELETON s (V.2 CTS-S): "the [2a] SP.1 stage/side/residual-shape fields
of the CURRENT node, values and heights forgotten" — EXACTLY MovesSp.Species
(which forgets heights BY TYPE), catalogue-membered. p-INDEPENDENCE BY TYPING:
no field mentions a prime. -/
structure Skeleton (n : ℕ) where
  sp  : MovesSp.Species
  mem : MovesSp.InCatalogue n sp

/-- (D2) generator KIND — a proper inductive (C4/C5 repair; the rev-1
`(twist : ℤ) ⊕ (relName : String)` is struck): (a) an anchor-twisted VAL.1
generator with its twist exponent DISPLAYED; (b) a relational stratum WITH ITS
POLYNOMIAL (the note: "each relation named WITH its polynomial and its
exceptional-characteristic convention") — `relPoly` is a FIELD, not a comment;
the exceptional-characteristic convention IS the per-q₀ assignment map itself
(`part` below), as the note displays it. -/
inductive GenKind where
  | anchor (a_eff : ℤ)
  | rel (relPoly : Polynomial ℤ)

def GenKind.twistExp : GenKind → ℤ
  | .anchor a => a
  | .rel _ => 0

/-- ONE (D2) GENERATOR over the per-prime concrete-state carrier: a UNIFORM
finite partition — one fixed label set, a total per-q₀ cell assignment.
ANCHOR ALIGNMENT AS A TYPE (C10 repair): the generator carries the fixed-frame
map `base`, the anchor action `twistOf`, and the LAW `part_eq`: the partition
map IS base∘twist at the generator's twist exponent — at a_eff ≠ 0 cells apply
to the TWISTED target BY CONSTRUCTION and never directly to the fixed frame;
at a_eff = 0 `twist0` collapses part = base (V2-8 states both as lemmas). -/
structure GenSpec (Carrier : ℚ → Type) where
  idx    : Type
  finI   : Fintype idx
  kind   : GenKind
  base   : ∀ q₀, Carrier q₀ → idx        -- the fixed-frame cell map
  twistOf : ∀ q₀, ℤ → Carrier q₀ → Carrier q₀   -- the anchor action α^{−a}·(−)
  twist0 : ∀ q₀, twistOf q₀ 0 = id
  twist_add : ∀ q₀ a b, twistOf q₀ (a + b) = twistOf q₀ a ∘ twistOf q₀ b
    -- [REV 3, Codex-3/C10 residue: `twistOf` is a ℤ-ACTION by type — junk
    -- non-action data is out. WHICH action (α^{−a}·(−)) is the (D2) display
    -- duty at each computed skeleton, exactly where the note places it; the
    -- gate blocks display it concretely (V6 layer).]
  part   : ∀ q₀, Carrier q₀ → idx        -- total ⟹ a partition, typed
  part_eq : ∀ q₀ x, part q₀ x = base q₀ (twistOf q₀ kind.twistExp x)
  -- (D2) REL FORCING (REV 3, Codex-3: rev 2's `relPoly` was decorative —
  -- nothing relates `part` to it). The relational generator carries the
  -- observable it evaluates, a value carrier with a ring structure to
  -- evaluate the ℤ-polynomial in, and the LAW that its fixed-frame partition
  -- FACTORS THROUGH the polynomial's value at that observable — cells can
  -- depend on x only through relPoly(obs x). For anchor generators these
  -- fields are inert (rel_eq's premise is false).
  Val    : ℚ → Type
  ringV  : ∀ q₀, CommRing (Val q₀)
  relObs : ∀ q₀, Carrier q₀ → Val q₀
  stratOf : ∀ q₀, Val q₀ → idx
  rel_eq : ∀ (P : Polynomial ℤ), kind = .rel P → ∀ q₀ x,
    base q₀ x = stratOf q₀
      (letI := ringV q₀
       ((P.map (Int.castRingHom (Val q₀))).eval (relObs q₀ x)))
    -- [REV 4, Codex-15: the stored CommRing installed via letI before the
    --  polynomial evaluation — the field now elaborates as written]

/-- the skeleton's BLOCK SIZE e (the SP.1 cluster size — V7-3a's "block-size
datum", now a NAMED Defs object: `State e` partitions CTS cells by it;
NEW at REV 5, needed by `omem_size` below). E-phase points this at the
MovesSp stage projection (the cluster-size identity W·D = e at the species
layer — V7-3c's stage-field wiring); if MovesSp names the size field
directly, the def re-points THERE — one token, zero design content,
recorded as inventory slot 13. -/
def skBlk {n : ℕ} (s : Skeleton n) : ℕ := s.sp.W * s.sp.D

/-- ONE OUTCOME MEMBER (NEW at REV 5, Codex-2: "member data from DEG-CONS's
tuples" had NO carrier — neither BlockData nor CtsFamily supplied the
member lists/sizes/statuses, so V7-3a could not construct
`MovesS.TableShape.odata`, whose `Outcome` demands a NONEMPTY `Member`
list). The DEG-CONS tuple datum: cluster size e_j, base-change factor δ,
and status — an absorbing verdict label, or a continuing target SKELETON
(the cross-block CELL landing per member is CtsFamily-level data, `tcellM`
below, since its codomain needs the target skeleton's own BlockData).
Mirrors the frozen `MovesS.Member` (size/δ/status) field-for-field, with
`Skeleton` in place of the seam's `State size`; V7-3a's odata map casts
along `omem_size`. -/
structure OMember (n : ℕ) where
  size   : ℕ
  δ      : ℕ+
  status : VLabel n ⊕ Skeleton n

/-- (D1)–(D4) for ONE skeleton — CL-13's COMPUTED-PARTITION DELIVERABLE, one
typed record (V.2: "the meet symbol is a construction RECIPE; the clause-(i)
deliverable is the DISPLAYED LIST"). The MEET CELLS are the fibers of the
product of generator maps — "explicit cell predicates as boolean combinations
of (D2)'s generators" is DEFINITIONAL here. REV 2 adds `evalObs`: the letters'
evaluation-map carrier, so (iv)-REP's per-species proviso `ObsCheck` (§2.G)
has a typed referent (C29 repair). REV 5 adds the OUTCOME-MEMBER ROSTER
`omem` (Codex-2) and pins the (D4) target skeleton to the letter's own
successor species (`tgt_sp` — Codex-3). -/
structure BlockData (n : ℕ) (s : Skeleton n) where
  Carrier : ℚ → Type                       -- concrete states over F_{q₀}
  finCar : ∀ q₀, Fintype (Carrier q₀)
  -- (D1) the menu: [2a] SP-OUT letters from s, membership TYPED:
  Letter : Type
  finL   : Fintype Letter
  letterSp : Letter → MovesSp.Species ⊕ MovesSp.Verdict
  letter_menu : ∀ m, letterSp m ∈ MovesSp.Out n s.sp
  -- the letters' evaluation-map carrier ((D1)-level data; ObsCheck's referent):
  Obs     : Letter → ℚ → Type
  evalObs : ∀ (m : Letter) (q₀ : ℚ), Carrier q₀ → Obs m q₀
  -- (D2) the generator list:
  Gen  : Type
  finG : Fintype Gen
  gen  : Gen → GenSpec Carrier
  -- (D3) the meet list: labels = the product of generator labels; size
  -- polynomials with the SPLIT degree bound (W_state(s), never any W_loc):
  Wstate : ℕ
  sizeP  : (∀ g : Gen, (gen g).idx) → Polynomial ℚ
  size_deg : ∀ a, (sizeP a).natDegree ≤ Wstate
  size_count : ∀ (a) (q₀ : ℚ), IsPP q₀ →
    ((sizeP a).eval q₀ : ℚ)
      = (Finset.univ.filter (fun x : Carrier q₀ => ∀ g, (gen g).part q₀ x = a g)).card
  -- the letter's FULL OUTCOME roster (REV 4, Codex-2: outcomes moved HERE
  -- from CtsFamily — continuing/terminal status is an OUTCOME datum, never
  -- a letter datum: V.6.3's ONE letter m₂ has terminal outcomes o_split,
  -- o_inert AND the continuing outcome o_double; no `cont : Letter → Prop`
  -- can represent that roster, so the rev-1..3 letter keying is STRUCK):
  Outc : Letter → Type
  finO : ∀ m, Fintype (Outc m)
  -- THE OUTCOME-MEMBER ROSTER (NEW at REV 5, Codex-2): per (letter,
  -- outcome), the DEG-CONS member tuples as DATA — the note's "m ≥ 2
  -- children, each child cluster size e_j ≥ 1, Σ_j e_j ≤ e — per member"
  -- finally has a carrier; `MovesS.Outcome`'s nonempty Member list is
  -- constructible (V7-3a), DEG-CONS's size laws get a typed referent
  -- (V2-9), and the (m, c) route classification reads the roster:
  omem : ∀ m (o : Outc m), List (OMember n)
  omem_ne : ∀ m o, omem m o ≠ []          -- `Outcome.hm`'s supplier
  omem_size : ∀ m o, ∀ mu ∈ omem m o, ∀ sk : Skeleton n,
    mu.status = Sum.inr sk → skBlk sk = mu.size
    -- a continuing member's target skeleton sits in the member's own
    -- size-e_j block (the seam's `Member.status : V ⊕ State size` typing
    -- rides this cast)
  -- (D4) the target data per CONTINUING OUTCOME, landing in the TARGET
  -- block's cells "under the SAME global definition" (typed by codomain):
  cont : ∀ m, Outc m → Prop
  decCont : ∀ m, DecidablePred (cont m)
  cont_iff : ∀ m o, cont m o ↔ ∃ mu ∈ omem m o, mu.status.isRight = true
    -- [REV 5: continuing = HAS a continuing member — (K-SUB)'s c ≥ 1,
    --  tied to the roster, never a free Prop]
  tgtSk : ∀ m (o : Outc m), cont m o → Skeleton n
  tgt_sp : ∀ m (o : Outc m) (h : cont m o),
    letterSp m = Sum.inl (tgtSk m o h).sp
    -- [REV 5, Codex-3's second horn: the note's (CTS-T) reads "species
    --  m : s → s′ ∈ Out(s) … target cell β ∈ JREF^src(s′)" — the (D4)
    --  target block IS the letter's own successor species s′, never an
    --  unrelated skeleton. Rev 4's `(letterSp m).isLeft` is the corollary;
    --  a continuing outcome still forces the species side, and (D4)'s
    --  duty still covers continuing outcomes only.]
  omem_sel : ∀ m (o : Outc m) (h : cont m o),
    ∃ mu ∈ omem m o, mu.status = Sum.inr (tgtSk m o h)
    -- THE SELECTED-MEMBER TIE (NEW at REV 6, Codex5-22 — the round-5
    -- core): the (D4) designated target skeleton IS some continuing
    -- roster member's target. Without it, `MoveData.tgt`, V7-3a's
    -- continuing statuses, and V5-7b's constructed split datum could
    -- select a successor ABSENT from the DEG-CONS roster (`cont_iff`
    -- gives only "SOME continuing member exists", not "the designated
    -- one is a member"). With it, the frozen `kstep_one` member
    -- condition ("∃ μ ∈ mem, ∃ h : μ.size = e, h ▸ μ.status = Sum.inr β"
    -- — built Defs.lean 238–242) is supplied at the designated β through
    -- `omem_size` (the size cast) + `tcellM_sel` (the DESIGNATED-member
    -- landing tie, CtsFamily — REV 7, C3: the ∀-form `tcellM_tgt` is
    -- STRUCK); V7-3a/V7-6b cite THIS law.
```

`omem_kcol` — rev 5's field — is now the DERIVED length-1 corollary
(displayed; one line, no longer a proof obligation on instance-builders):
```lean
theorem BlockData.omem_kcol {n s} (B : BlockData n s) (m) (o : B.Outc m)
    (h : B.cont m o) (h1 : (B.omem m o).length = 1) :
    ((B.omem m o).head (B.omem_ne m o)).status = Sum.inr (B.tgtSk m o h) := by
  obtain ⟨mu, hmem, hst⟩ := B.omem_sel m o h
  obtain ⟨a, ha⟩ := List.length_eq_one.mp h1   -- omem m o = [a]
  rw [ha] at hmem ⊢
  simpa [List.eq_of_mem_singleton hmem] using hst
```

`BlockData.CellIdx` (the def now DISPLAYED above, in declaration order —
Codex-15) encodes zero-size deletion (V.2: "cells with IDENTICALLY-zero size
polynomial are deleted once, symbolically"); V2-2 keeps its Fintype instance
and the `deleted_empty` lemma. THE TARGET-CELL MAP's cell-level component is
a field of the
GLOBAL family record `CtsFamily`, since its codomain needs the target
skeleton's own BlockData — matrix indices type-check BY CONSTRUCTION, "no
species-relative cell ever appears as an index".

```lean
/-- `BlockData.CellIdx` — DECLARED IN DEFS (REV 4, Codex-15's order gap:
rev 3 assigned the def to unit V2-2 while `TargetIx` consumed it here). -/
def BlockData.CellIdx {n s} (B : BlockData n s) : Type :=
  {a : ∀ g : B.Gen, (B.gen g).idx // B.sizeP a ≠ 0}

/-- The target index of an OUTCOME (REV 4, Codex-2: per (letter, outcome)):
continuing outcome ⟹ a target-block cell; terminal outcome ⟹ the absorbing
column label. REV 5 (Codex-3 + Fable M-1's junk-terminal horn): `term` now
REQUIRES the outcome terminal — a continuing outcome has NO absorbing
column (the note's terminal-final extension attaches β_k := [o_k] only
"whose FINAL step carries a TERMINAL outcome o_k"), so the round-4
refutation instance (a `.term ⟨(1,1),_⟩ column on the T21 letter's
continuing outcome) no longer TYPES. -/
inductive TargetIx (n : ℕ) {s : Skeleton n} (B : BlockData n s)
    (B' : ∀ s', BlockData n s') (m : B.Letter) (o : B.Outc m) where
  | cell (h : B.cont m o) (β : (B' (B.tgtSk m o h)).CellIdx)
  | term (ht : ¬ B.cont m o) (v : VLabel n)

/-- THE TABLE FAMILY over one n: per-skeleton BlockData + the globally-typed
(D4) cell maps + the per-entry count tables (CTS-T). THIS is the record the
SEAM instantiates into MovesS.TableShape (unit V7-3a). REV 4 (Codex-2):
`tcell`/`T`/`vlabOf` keyed per (letter, OUTCOME). -/
structure CtsFamily (n : ℕ) where
  bd : ∀ s : Skeleton n, BlockData n s
  tcell : ∀ (s : Skeleton n) (m : (bd s).Letter) (o : (bd s).Outc m)
    (h : (bd s).cont m o),
    (bd s).CellIdx → (bd ((bd s).tgtSk m o h)).CellIdx
  -- THE PER-MEMBER LANDING MAPS (NEW at REV 5, Codex-2): `odata`'s
  -- continuing members carry target STATES (skeleton, cell) at the seam;
  -- the cross-block cell component per ROSTER POSITION lives here (same
  -- reason tcell does: the codomain needs the target skeleton's own
  -- BlockData). At n = 3 every continuing outcome is single-continuing
  -- (V4-8's census), so tcellM's extra content beyond tcell is empty
  -- there — the field is what makes odata TOTAL at every n:
  tcellM : ∀ (s : Skeleton n) (m : (bd s).Letter) (o : (bd s).Outc m)
    (i : Fin ((bd s).omem m o).length) (sk : Skeleton n),
    (((bd s).omem m o).get i).status = Sum.inr sk →
    (bd s).CellIdx → (bd sk).CellIdx
  tcellM_sel : ∀ (s) (m) (o) (h : (bd s).cont m o),
    ∃ (i : Fin ((bd s).omem m o).length)
      (hs : (((bd s).omem m o).get i).status = Sum.inr ((bd s).tgtSk m o h)),
      tcellM s m o i _ hs = tcell s m o h
    -- [tie] THE DESIGNATED MEMBER'S landing coherence — RE-SCOPED at
    -- REV 7 (C3, adjudicated: the rev-6 ∀-form `tcellM_tgt` forced EVERY
    -- roster member whose status carries the designated skeleton to the
    -- designated tcell — unsupported for multi-continuing outcomes where
    -- two same-skeleton siblings land in different target cells; no
    -- uniqueness-of-target-skeleton invariant exists in BlockData).
    -- THIS is the ruling's fold of `omem_sel` with the landing tie: SOME
    -- roster position carries the designated target skeleton AND lands
    -- BY the (D4) map — the [tie] content survives for THAT member;
    -- `BlockData.omem_sel` is the ∃-projection (get-membership); at
    -- n = 3 every continuing outcome is single-continuing (V4-8), so
    -- the ∃ is the whole roster there. kstep_one's seam supply (V7-6b)
    -- coheres through this; other members' tcellM values are FREE (their
    -- landings are their own odata content, V7-3a).
  -- (CTS-T) the tables, with Theorem VAL(a)'s per-entry content as TYPE:
  -- one polynomial, degree ≤ W_loc(m); the COUNT SEMANTICS is ValA's field
  -- content (§2.F note + V2-4 — the rev-1 `tbl_count` field moved there,
  -- resolving design-freedom slot (3)):
  Wloc : ∀ (s : Skeleton n), (bd s).Letter → ℕ
  T : ∀ (s : Skeleton n) (m : (bd s).Letter) (o : (bd s).Outc m)
    (α : (bd s).CellIdx) (β : TargetIx n (bd s) bd m o), Polynomial ℚ
  T_deg : ∀ s m o α β, (T s m o α β).natDegree ≤ Wloc s m
  -- terminal outcome labels (the outcome's absorbing column label):
  vlabOf : ∀ (s) (m) (o : (bd s).Outc m), ¬ (bd s).cont m o → VLabel n
```

**The (D4)-typed step data (REV 3, Codex-3/Codex-18: displayed closed; the
target of a continuing datum is ENFORCED by `tcell` BY TYPE — the global D4
map can no longer be decorative, since `S.Move αc βc` will be empty unless βc
is a tcell-image, per `moveOf_bij` in §2.F):**
```lean
structure MoveData (n : ℕ) (C : CtsFamily n) where
  s  : Skeleton n
  m  : (C.bd s).Letter
  o  : (C.bd s).Outc m
  hc : (C.bd s).cont m o              -- [REV 4, Codex-2: OUTCOME-continuing]
  α  : (C.bd s).CellIdx

/-- the datum's source and its tcell-ENFORCED target. -/
def MoveData.src {n C} (d : MoveData n C) : Σ s, (C.bd s).CellIdx := ⟨d.s, d.α⟩
def MoveData.tgt {n C} (d : MoveData n C) : Σ s, (C.bd s).CellIdx :=
  ⟨(C.bd d.s).tgtSk d.m d.o d.hc, C.tcell d.s d.m d.o d.hc d.α⟩

structure TermData (n : ℕ) (C : CtsFamily n) (v : VLabel n) where
  s  : Skeleton n
  m  : (C.bd s).Letter
  o  : (C.bd s).Outc m
  ht : ¬ (C.bd s).cont m o            -- [REV 4, Codex-2: OUTCOME-terminal —
                                      --  m₂'s o_split/o_inert land here while
                                      --  its o_double is a MoveData; ONE
                                      --  letter, both kinds, representable]
  hv : C.vlabOf s m o ht = v          -- the absorbing label, enforced
  α  : (C.bd s).CellIdx

/-- THE DATUM'S OWN TABLE INDEX (NEW at REV 5 — Fable M-1's binding
object): the ONE TargetIx column the datum's counts inhabit — the (D4)
landing cell for a continuing datum, the outcome's absorbing label for a
terminal-final one. `ValA.tbl_count`/`tbl_countT` (V2-4), `pathProdPoly`
(V2-5), V5-8's identity and V7-4c's kstep all bind THIS index. (Rev 2–4's
tbl_count quantified its β FREE with a β-independent right side — every
junk entry was forced equal to the datum's count and `valA_gate` was FALSE
at the note-correct family, 0 = 2 at q₀ = 2. The M-1 repair.) -/
def MoveData.tix {n C} (d : MoveData n C) :
    TargetIx n (C.bd d.s) C.bd d.m d.o :=
  .cell d.hc (C.tcell d.s d.m d.o d.hc d.α)
def TermData.tix {n C v} (d : TermData n C v) :
    TargetIx n (C.bd d.s) C.bd d.m d.o :=
  .term d.ht v
```

[The OUTCOME label o carries "next-node data + all hinge-value cells +
collision pattern, or a terminal label — the [2a] L5-case letters"; its Lean
carrier is the abstract `Outc` with the V.6 gate instances pinning concrete
rosters (V6 layer), and the FULL per-skeleton roster is the TABLE-BUILD
deliverable — [1v]-COND's CL-13 burden, which this corpus types but does not
globally compute (exactly the note's own perimeter: "executed in this note
ONLY for the three V.6 gate blocks").]

### 2.D Entrance shapes ε (V.1(iii), rev-4 unified typing) — REV 2: the WF ties (C6/C12/A-3)

```lean
/-- V.1(iii)'s ENTRANCE SHAPE — "the TRIPLE ε := (P̂, b, σ_sel) of a shallow
CONCRETE §D4-R shape-prefix P̂ — which RETAINS its per-node heights h_r and
its per-read side heights u*_r (§D4-R L3, rev 9) — a designated continuing
branch b entering the size-e block landing in cell β₀, and the
branch-selection record σ_sel (L11's encoding data, lifted into the label)".
P̂ IS MovesD.Shape n (its ShapeRead fields `h`, `ustar` are the retained
heights — the rev-4 F1 unification is BY TYPE: no independent height
parameter exists). REV 2 (C6 repair): the triple's components are now TIED —
(gsel, musel) is the ENTRY READ's designated continuing selection (`hentry`,
mirroring MovesSp.EntranceShape.hEntry), L5-ELIGIBLE at that read (`helig`,
keyed to MovesD's eligible-(g,μ) menu — the E6 carrier), and σ_sel carries
ONE record entry per shallow branching cell passed (`hlen`) with each entry
in that cell's finite branch menu (`hmenu`). Degenerate/fictitious entrances
now violate a field. The LANDING (block e, cell β₀) is NOT a field of ε: it
is the measured side's landing data (`CtsMeasured.entLands`, §2.F) — the
note's β₀ always appears as the pairing index (ε, β₀). Entrances are
POST-SPLIT objects: siblings differ in s_r, hence carry DISTINCT ε. -/
structure EntShapeV (n : ℕ) where
  Phat   : MovesD.Shape n
  hne    : (Phat : MovesD.ShapePrefix).reads ≠ []
  gsel   : ℕ                       -- the designated branch's selection (g, μ)
  musel  : ℕ                       --   at the entry read (b's datum)
  hsel_g : 1 ≤ gsel
  hsel_μ : 1 ≤ musel
  hentry : ∀ R, (Phat : MovesD.ShapePrefix).reads.getLast? = some R →
    R.g = gsel ∧ R.μ = musel       -- b IS the entry read's designated branch
  helig  : ∀ R, (Phat : MovesD.ShapePrefix).reads.getLast? = some R →
    EligPair R gsel musel          -- L5 eligibility (MovesD E6 menu; def below)
  selRec : List ℕ                  -- σ_sel: s_r at every shallow branching
                                   --   cell passed — THE L11 RANKS (below)
  hlen   : selRec.length =
    ((Phat : MovesD.ShapePrefix).reads.filter
      (fun R => decide (IsBranchSlot R))).length
  hmenu  : ∀ i (hi : i < selRec.length),
    selRec.get ⟨i, hi⟩ < branchMenuCard n Phat i
    -- [REV 7, C2: the label's roster is the SLOT roster (`IsBranchSlot`,
    --  2 ≤ m̄ — the E6-licensed SUPERSET: every read that CAN branch has a
    --  slot, since a realized menu of ≥ 2 forces m̄ ≥ 2). ACTUAL branching
    --  is the REALIZED key `RealizedBranching` (value-level, below) —
    --  membership (`SelMatches`) pins every slot to E9's own per-read
    --  component, so surplus slots carry the CANONICAL rank (a singleton
    --  realized menu has selRank = 0 — zero information) and the
    --  realized-branching reads' entries are exactly the note's σ_sel.]
    -- [REV 6, Codex5-23: `selRec` is genuine SELECTION DATA — the L11
    --  s_r ranks of the ψ-selections taken, menu-bounded here (< m̄, the
    --  E7 range). The rev-4/5 field `hrank` (entry = a rank of (g, μ)
    --  PAIRS via shapeRank/eligMenu/takenGm) is STRUCK: the m̄-menu is
    --  the ψ-menu AT the read's own (g, μ) — `ShapeRead.mbar =
    --  len/(g·μ)`, and `MovesD.selRank w ν` ranks ν's OWN ψ among the
    --  `EligibleImage`-eligibles at (ν.g, ν.μ) — so no shape-level
    --  function of (g, μ) can compute the entry, and equating the two
    --  enumerations was unsatisfiable against E8_rankInj whenever two
    --  eligible ψ-selections share (g, μ). The value tie is the DEF
    --  `SelMatches` below (the recorded hatch FIRED, as designed:
    --  re-key at MovesD's own enumeration, fresh audit).]
```

**σ_sel's SEMANTIC PIN — RE-TARGETED at REV 6 (Codex5-23; supersedes the
REV-4 `hrank` and the REV-5 `SelRankTie`, both of which tied the entries
to a rank of (g, μ) PAIRS).** What the frozen text records is L11's s_r —
the rank of the SELECTED (side, ψ) CONTINUATION — and MovesD's own E9
encoding says exactly where that rank lives (built MovesD/Defs.lean:
`EncTargetP` 529–531, the per-read component displayed in `encIdx`
556–564 — cites REFRESHED at REV 7, Fable GAP-3, content verbatim): the
branch datum at read r is `(side digits, Fin mbar_r)` with the Fin
component `selRank (reads.get r).w ν % (reads.get r).mbar` AT THE READ'S
OWN NODE ν, "the collapse is the identity on members, where E7 gives
selRank < m̄" (Defs.lean 552–555). So: `selRec` is genuine SELECTION DATA
(bounded by `hmenu`; NO label-internal equation exists — none can, since
the ψ-choice is value-level); and the label↔value tie is the DEF
`SelMatches` below — the σ_sel-component of ε-CLASS MEMBERSHIP, which the
instance layer (the 2.E entrance cuts, V3-1(b), V5-1) consumes
DEFINITIONALLY, not as a coherence hypothesis. (side, ψ)-FAITHFULNESS is
then MovesD's proved apparatus, cited never re-derived: two cuts taking
DISTINCT eligible ψ-selections at read r have distinct `selRank` values
(`E8_rankInj`), both < m̄_r (E7, so the mod-collapse is the identity on
members), hence labels with DIFFERENT selRec r-entries. No independently
invented enumeration survives (`shapeRank`/`eligMenu`/`takenGm` STRUCK —
the rev-5 equation was unsatisfiable-or-collapsing against E8_rankInj
whenever two eligible ψ-selections share (g, μ), which is Codex5-23's
finding; the §2.D hatch fired exactly as recorded). The entrance events
and the instance census (§2.F) take the FULL label ε (selRec included)
as their key, so distinct selections cut distinct events by construction.
The displayed defs (closed, keyed to NAMED MovesD declarations — Codex-18):
```lean
/-- shape-level eligibility of a (g, μ) pair at a read: the L5 budget
(E5_gmuLe is MovesD's law that every realized node's own pair satisfies it). -/
def EligPair (R : MovesD.ShapeRead) (g μ : ℕ) : Prop :=
  1 ≤ g ∧ 1 ≤ μ ∧ g * μ ≤ R.len

/-- a branch SLOT — RENAMED at REV 7 (C2: `IsBranchingRead := 2 ≤ mbar`
is an UPPER-BOUND key, not actual branching — `mbar = ⌊len/(g·μ)⌋` is a
bound/rank codomain, `eligible_card_le` (MovesD E6) only BOUNDS the
realized census by it). This shape-level predicate is the σ_sel SLOT
LAYOUT: every read that CAN branch gets a slot. -/
def IsBranchSlot (R : MovesD.ShapeRead) : Prop := 2 ≤ R.mbar

/-- ACTUAL branching — THE REALIZED KEY (NEW at REV 7, C2): the read's
realized node has ≥ 2 realized eligible continuations. THE FAITHFUL
CARRIER, documented: MovesD's own value-level eligible census
`EligibleImage p w ν.g ν.μ (RanchImage ν)` (built Defs.lean 297–303) —
the SAME census `selRank` ranks (308–310) and E7/E8 govern; E6's
`eligible_card_le` + E7's F-image bound give
`RealizedBranching → IsBranchSlot` at the read (realized menu ≤ m̄), so
every realized-branching read HAS a slot. -/
def RealizedBranching {p : ℕ} [Fact p.Prime] {F : Type*} [Field F]
    [Finite F] (w : ℕ) (ν : MovesC.Node p F) : Prop :=
  2 ≤ Nat.card {q : Polynomial F //
        MovesD.EligibleImage p w ν.g ν.μ (MovesD.RanchImage ν) q}

/-- the i-th slot read's menu card — RESTRUCTURED at REV 7 (Fable GAP-4:
`MovesD.ShapeRead` is proof-carrying with NO `Inhabited` instance, so the
rev-5/6 `getD i default` did not elaborate; Option-indexing needs no junk
witness). Out-of-range gives 0 (never consumed: `hmenu` quantifies
i < selRec.length = the filter length, where `[i]?` is `some`). -/
def branchMenuCard (n : ℕ) (P : MovesD.Shape n) (i : ℕ) : ℕ :=
  ((((P : MovesD.ShapePrefix).reads.filter
    (fun R => decide (IsBranchSlot R)))[i]?).map MovesD.ShapeRead.mbar).getD 0

/-- the i-th slot read of P̂, Option-valued (REV 7, GAP-4 — replaces the
`getD … default` form; `some R` implies R is a filter member, hence
`IsBranchSlot R`). -/
def branchingRead? (n : ℕ) (P : MovesD.Shape n) (i : ℕ) :
    Option MovesD.ShapeRead :=
  ((P : MovesD.ShapePrefix).reads.filter
    (fun R => decide (IsBranchSlot R)))[i]?

-- [REV 6, Codex5-23: `takenGm`, `eligMenu`, and `shapeRank` are STRUCK.
--  They enumerated (g, μ) PAIRS, but the m̄-menu they were meant to index
--  is the ψ-menu at the read's OWN (g, μ) (`ShapeRead.mbar = len/(g·μ)`,
--  built Defs.lean 104; `selRank w ν` = the rank of ν's own ψImage among
--  the `EligibleImage p w ν.g ν.μ`-eligibles, built Defs.lean 308–310 —
--  cites refreshed at REV 7, GAP-3) —
--  a different, value-level menu. No shape-level (g, μ) enumeration
--  exists in this corpus any more; inventory slot 10 is OVERTAKEN.]

/-- the position of the r-th slot read in P̂'s read list (REV 7, GAP-4:
Option-indexed — no `Inhabited MovesD.ShapeRead` exists; the outer getD
is on ℕ, fine). -/
def bIdx {n : ℕ} (P : MovesD.Shape n) (r : ℕ) : ℕ :=
  ((List.range (P : MovesD.ShapePrefix).reads.length).filter
    (fun j => (((P : MovesD.ShapePrefix).reads[j]?).map
      (fun R => decide (IsBranchSlot R))).getD false)).getD r 0

/-- the realized node at the r-th branching read of a presented prefix. -/
noncomputable def nodeAt {n : ℕ} {p F} [Fact p.Prime] [Field F] [Finite F]
    {pol : MovesD.CanonPolicy p F} {P : MovesD.Shape n}
    (i : MovesD.PrefIdx n pol P) (r : ℕ) : Option (MovesC.Node p F) :=
  (MovesD.reprOf i).nodes[bIdx P r]?
    -- Option-valued, so no junk default; PrefIdx realizes every read, so
    -- the none branch is never taken there (E9's own quoted convention)

/-- THE σ_sel/L11 VALUE TIE — A DEF at REV 6 (Codex5-23, replacing rev 5's
`SelRankTie` coherence structure); RE-KEYED at REV 7 (C2 + GAP-4): the
label's selRec RECORDS the realized prefix's own ψ-selections.
`SelMatches ε i` is the σ_sel-COMPONENT OF ε-CLASS MEMBERSHIP: at EVERY
SLOT read r of P̂, the label's r-th entry equals MovesD's OWN selection
index of the read's realized node — `selRank w ν % m̄`, verbatim the E9
encoding component (built MovesD/Defs.lean: `EncTargetP` 529–531, the
component in `encIdx` 556–564; E7 gives selRank < m̄, so the collapse is
the identity on members, 552–555 — cites refreshed, GAP-3). REV-7
faithfulness note (C2): the note's σ_sel has one entry per ACTUAL
branching cell; here every SLOT (2 ≤ m̄) is pinned, and at a slot whose
REALIZED menu is a singleton (`¬ RealizedBranching` — the read's node has
one eligible) the pinned value is the canonical `selRank = 0`, so surplus
slots carry ZERO information and the realized-branching reads' entries
(`RealizedBranching` — the value-level key, above) are EXACTLY the note's
σ_sel; E9's own encoding likewise records a `Fin m̄` component at every
read. The 2.E entrance cuts carry this predicate BY FIELD (`lands_sel` —
REV 7, C1); V3-1(b)/V5-1 consume it DEFINITIONALLY: distinct eligible
ψ-selections at read r have distinct selRank (`E8_rankInj`), both < m̄_r
(E7), hence no one selRec matches both — post-split (side, ψ) label
fidelity, from MovesD's proved units, never re-derived. -/
def SelMatches {n : ℕ} {p : ℕ} [Fact p.Prime] {F : Type*} [Field F]
    [Finite F] {pol : MovesD.CanonPolicy p F} (ε : EntShapeV n)
    (i : MovesD.PrefIdx n pol ε.Phat) : Prop :=
  ∀ (r : ℕ) (hr : r < ε.selRec.length) (R : MovesD.ShapeRead)
    (ν : MovesC.Node p F),
    branchingRead? n ε.Phat r = some R → nodeAt i r = some ν →
    ε.selRec.get ⟨r, hr⟩ = MovesD.selRank R.w ν % R.mbar
```

```lean
/-- HEIGHT PROJECTION (rev 4): h_ent(ε) := the tuple of ε's RETAINED height
data — the (h_r, u*_r) pair vector over P̂'s reads. A FUNCTION of ε,
displayed; "one concrete ε FIXES its entrance heights". -/
def EntShapeV.hent {n : ℕ} (ε : EntShapeV n) : List (ℕ × ℚ) :=
  (ε.Phat : MovesD.ShapePrefix).reads.map (fun R => (R.h, R.ustar))

/-- the ℕ-code of the retained height data (REV 4, Codex-6: the seam's
`MeasuredSide.hent : … → ℕ` slot is supplied by THIS code, never by a
lossy sum). REV 5 (Codex-7 + Fable G-2 — the round-4 injectivity gloss was
FALSE as stated): the fold is now LENGTH-SEEDED — the rev-4 zero-seeded
fold collided across read counts (Nat.pair 0 0 = 0 and zig 0 = 0, so [x]
and [x, R₀] with R₀.h = 0, R₀.gam = 0 coded equal). WHAT IS CLAIMED, and
only this: the code is injective ON THE RETAINED (h_r, γ_r)-TUPLE LISTS
(equal length: Nat.pair-injectivity + list induction; unequal length: the
outer seed differs). Recovering u*_r from γ_r additionally uses the
prefix's (e, s0, wSide, STR) via `gamTie` — data NOT in the code but FIXED
by the template at the seam's consumption granularity (`hent` is supplied
per (template, component) INDEX, V7-4b, where those per-read data are the
template's own) — so at the consumption site the code separates exactly
the retained (h_r, u*_r) data; no ∀-ε injectivity into u* is claimed, and
NO MovesS law reads the value at all (SF-1's standing grep: declaration +
device `:= 0` + one comment). -/
def EntShapeV.hentCode {n : ℕ} (ε : EntShapeV n) : ℕ :=
  Nat.pair (ε.Phat : MovesD.ShapePrefix).reads.length
    (((ε.Phat : MovesD.ShapePrefix).reads.map
      (fun R => Nat.pair R.h (zig R.gam))).foldr Nat.pair 0)

/-- ledger exponent A(ε) := §D4-R's A(P̂) — "a function of ε since u*_r ∈ P̂";
pool dimension W_ent(ε) := §D4-R's W(P̂) — "height-free, L3 rev 9". -/
noncomputable def EntShapeV.A (ε : EntShapeV n) : ℕ :=
  (ε.Phat : MovesD.ShapePrefix).A' n
def EntShapeV.Went (ε : EntShapeV n) : ℕ := (ε.Phat : MovesD.ShapePrefix).W

/-- The height-forgetting TEMPLATE ε̊ — "SP.1 applied to P̂, selection data
kept". REV 2 (C12/A-3 repair): the boundedness is INTRINSIC, not an external
[3t] premise — the word is a CATALOGUE-membered, SuccStep-linked,
RUN-COLLAPSED species word (MovesSp's `CollapsedWalk`: self-loop runs are
struck into the depth direction, exactly [2a]'s collapse convention), the
entry law mirrors `MovesSp.EntranceShape.hEntry`, and σ_sel is menu-bounded
per branching letter. V3-4 proves the family FINITE OUTRIGHT from these
fields ([2a]/M1: `rankNat` strictly increases along collapsed SuccStep edges
— the SP4_dagWords idiom — over the finite SP2 catalogue; L5's finite menus
bound selRec). No `WordBounded` premise exists any more. -/
structure EntTemplate (n : ℕ) where
  word   : List MovesSp.Species
  hne    : word ≠ []
  hMem   : ∀ s ∈ word, MovesSp.InCatalogue n s
  hWalk  : word.Chain' (fun s s' => MovesSp.SuccStep n s s' ∧ s ≠ s')
  gsel musel : ℕ
  hsel_g : 1 ≤ gsel
  hsel_μ : 1 ≤ musel
  hEntry : ∀ s, word.getLast? = some s → s.sel = some (gsel, musel)
  selRec : List ℕ
  hlen   : selRec.length = (word.filter (IsBranchingLetter n)).length
  hmenu  : ∀ i (hi : i < selRec.length),
    selRec.get ⟨i, hi⟩ < letterMenuCard n word i
    -- (REV 7, C2: `IsBranchingLetter` is the TEMPLATE-side SLOT layout,
    --  mirroring `IsBranchSlot` — same upper-bound reading, same
    --  surplus-slot-canonical convention through SelMatches; realized
    --  branching stays value-level, `RealizedBranching`.)

/-- ε's template, Option-valued — RESTRUCTURED at REV 7 (C11: the rev-6
form filled its six proof fields by projections of the V3-3b lemma
`spWord_collapseWF`, a FORWARD REFERENCE — Defs builds before V3, so no
later unit's theorem may appear in a Defs-layer term). The WF conjunction
is CHECKED here (classical dite — every clause is a proposition about
concrete lists; no proof term is imported), and V3-3b's deliverable is
now the TOTALITY + tie theorem `template_total : ∀ ε, (ε.template?).isSome`
(with the six clauses' transport from ε's own WF fields as its content —
same mathematics, no forward reference; the none branch is DEAD at every
consumption site by this lemma). -/
open Classical in
noncomputable def EntShapeV.template? {n : ℕ} (ε : EntShapeV n) :
    Option (EntTemplate n) :=
  let w := MovesSp.collapseRuns (spWord n (ε.Phat : MovesD.ShapePrefix))
  if hw : w ≠ [] ∧ (∀ s ∈ w, MovesSp.InCatalogue n s) ∧
      w.Chain' (fun s s' => MovesSp.SuccStep n s s' ∧ s ≠ s') ∧
      (∀ s, w.getLast? = some s → s.sel = some (ε.gsel, ε.musel)) ∧
      ε.selRec.length = (w.filter (IsBranchingLetter n)).length ∧
      (∀ i (hi : i < ε.selRec.length),
        ε.selRec.get ⟨i, hi⟩ < letterMenuCard n w i)
  then some { word := w, gsel := ε.gsel, musel := ε.musel,
              selRec := ε.selRec,
              hsel_g := ε.hsel_g, hsel_μ := ε.hsel_μ,
              hne := hw.1, hMem := hw.2.1, hWalk := hw.2.2.1,
              hEntry := hw.2.2.2.1, hlen := hw.2.2.2.2.1,
              hmenu := hw.2.2.2.2.2 }
  else none

/-- the instantiation dimension of a template: two ℕ-slots (h_r, the u*-code
u°_r — encoding below) per letter + one depth slot per (collapsed) self-loop
letter — the h-vector H(ε̊) ranges over (V3-5's chart;
MovesSp.EntranceShape's slot layout). -/
def EntTemplate.entDim {n : ℕ} (ε̊ : EntTemplate n) : ℕ :=
  2 * ε̊.word.length + (ε̊.word.filter (SelfLoopLetter n)).length
```

**THE u\*-SLOT ENCODING, PINNED (REV 3, G-3: `MovesD.ShapeRead.ustar : ℚ`
vs the ℕ-slot).** The second slot per letter carries NOT u\*_r but the ℕ-code
of the read's ℤ-datum γ_r (`ShapeRead.gam`); u\*_r is then the DISPLAYED
inversion of MovesD's own WF law `ShapePrefix.gamTie`
(γ = e·(STR·u\*) + (s0 + wSide)·h, an exact ℚ-identity), which DETERMINES
u\* from (γ, h, e, s0, wSide, STR):
```lean
abbrev zig : ℤ ≃ ℕ := (Denumerable.eqv ℤ)   -- the standard zigzag code
-- [REV 4, Codex-15: orientation pinned at E-phase — Mathlib's
--  `Denumerable.eqv α : α ≃ ℕ`; if the library form is ℕ-first, the fix is
--  `.symm` (one token, zero design content; recorded so nothing is silent)]

-- inside readOfLetter (V3-3(d)): given the letter's reconstructed
-- (e, s0, wSide) data, the prefix-so-far's STR value, the h-slot value h,
-- and the u*-slot value k:
--   ustar := ((zig.symm k : ℚ) − ((s0 + wSide) : ℚ) * h) / (e * STR)
-- gamTie makes the roundtrip EXACT (V3-5(c)'s computation law); if MovesD's
-- WF is later found to constrain gam's range, the code tightens THERE —
-- recorded, never silent.
```
So the note's "H(ε̊) ⊆ ∏ ℕ^{d_i}" typing is honored with a displayed,
invertible encoding; V3-5's bijection horns lean on `gamTie`, a PROVED law.

**THE INSTANTIATION MAP, DISPLAYED (Codex-18: `writeHeights` was prose).**
```lean
/-- the three slot projections + the word expansion, CLOSED (REV 6,
Codex5-28 — no longer "closed defs in this file" promises). Slot layout
(per `entDim`): pairs (h-slot, u*-code slot) at positions 2i/2i+1 for the
i-th letter, then one depth slot per collapsed self-loop letter. -/
def EntTemplate.pairSlots {n : ℕ} (ε̊ : EntTemplate n) (h : Hpt ε̊.entDim) :
    List (ℕ × ℕ) :=
  List.ofFn (fun i : Fin ε̊.word.length =>
    (h ⟨2 * i, by unfold EntTemplate.entDim; omega⟩,
     h ⟨2 * i + 1, by unfold EntTemplate.entDim; omega⟩))
def EntTemplate.depthSlots {n : ℕ} (ε̊ : EntTemplate n) (h : Hpt ε̊.entDim) :
    List ℕ :=
  List.ofFn (fun j : Fin (ε̊.word.filter (SelfLoopLetter n)).length =>
    h ⟨2 * ε̊.word.length + j, by
        unfold EntTemplate.entDim
        have := (List.length_filter_le _ ε̊.word); omega⟩)
/-- re-expand each collapsed self-loop letter into a run of (depth + 1)
copies, consuming one depth slot per self-loop letter ([2a]'s collapse
convention, inverted). -/
def expandRuns (n : ℕ) : List MovesSp.Species → List ℕ → List MovesSp.Species
  | [], _ => []
  | s :: ws, ds =>
    if SelfLoopLetter n s
    then List.replicate (ds.headD 0 + 1) s ++ expandRuns n ws ds.tail
    else s :: expandRuns n ws ds
/-- the per-letter read reconstruction, Option-valued — CLOSED IN DEFS at
REV 7 (C11: rev 6 declared the body "V3-3d's deliverable", a forward
reference from Defs into V3). The DATA half is mechanical (e/g/μ/s0/
wSide/Dwidth/w from the letter's stage fields and the prefix-so-far's
chains; a/gam via anchorTie/gamTie; ustar := the zig/gamTie inversion
displayed above); `ShapeRead` is PROOF-CARRYING, so the constructed
candidate is CHECKED (classical dite over its decidable WF clauses) and
returned as `some` iff it passes — no junk witness, no imported proof.
V3-3d's deliverable is now the FAITHFULNESS theorem `spWord_faithful`
PLUS totality (below); the reconstruction ITSELF lives here. -/
open Classical in
noncomputable def readOfLetter? (n : ℕ) (P : MovesD.ShapePrefix)
    (s : MovesSp.Species) (hslot uslot : ℕ) : Option MovesD.ShapePrefix :=
  if hc : ∃ R : MovesD.ShapeRead, ReadFits n P s hslot uslot R
  then some (P.snoc hc.choose) else none
  -- `ReadFits n P s hslot uslot R` is the Defs-local Prop pinning R's
  -- every field to (s, P, hslot, uslot): the stage-field equations
  -- (R.e/g/μ/s0/wSide/Dwidth/w = the letter's stage reads at P's chains),
  -- R.h = hslot, R.gam = zig.symm uslot, R.ustar = the displayed gamTie
  -- inversion, R.a via anchorTie — each clause one equation, displayed at
  -- the ReadFits decl (Defs). Uniqueness of the fitting R is V3-3d's
  -- `spWord_faithful` content; EXISTENCE on template-realizable slots is
  -- V3-3d's totality — neither is consumed here (the dite needs no proof
  -- term, and `P.snoc` is MovesD's own extension). No forward reference:
  -- ReadFits and this def are Defs-layer declarations.

/-- fold the reconstruction along the expanded word (Option-monadic:
one failing letter kills the fold). `emptyPrefix` = the reads-[] prefix. -/
noncomputable def shapeOfSlots? (n : ℕ) (ws : List MovesSp.Species)
    (ps : List (ℕ × ℕ)) : Option MovesD.ShapePrefix :=
  (ws.zip ps).foldlM (fun P sp => readOfLetter? n P sp.1 sp.2.1 sp.2.2)
    emptyPrefix

/-- write the height/depth point into the template's slots — Option-valued
at REV 7 (C11: the rev-6 total form filled `Phat`'s WF proof and the five
tie fields by the V3-3d lemmas `writeHeights_wf`/`writeHeights_ties`,
both FORWARD REFERENCES). The folded prefix's Shape-WF and the five
EntShapeV ties are CHECKED here (classical dite); V3-3d's deliverable is
the TOTALITY theorem `writeHeights_total : ∀ ε̊ h, (writeHeights? ε̊ h).isSome`
(= exactly the old wf + ties content) plus `spWord_faithful`. Every
§2.F/2.G consumer reads through the DISPLAYED wrappers below; the none
branch is DEAD at consumption by `writeHeights_total`. -/
open Classical in
noncomputable def writeHeights? {n : ℕ} (ε̊ : EntTemplate n)
    (h : Hpt ε̊.entDim) : Option (EntShapeV n) :=
  (shapeOfSlots? n (expandRuns n ε̊.word (ε̊.depthSlots h))
    (ε̊.pairSlots h)).bind fun P =>
  if hw : ∃ hWF : ShapeWFOf P, EntTiesAt ⟨P, hWF⟩ ε̊
    -- ShapeWFOf / EntTiesAt: Defs-local abbreviations for MovesD's
    -- Shape-WF predicate at P and the five EntShapeV tie clauses
    -- (hne/hentry/helig/hlen/hmenu) at (⟨P, ·⟩, ε̊.gsel, ε̊.musel,
    -- ε̊.selRec) — plain Props about concrete data, dite'd classically
  then some { Phat := ⟨P, hw.choose⟩,
              gsel := ε̊.gsel, musel := ε̊.musel, selRec := ε̊.selRec,
              hsel_g := ε̊.hsel_g, hsel_μ := ε̊.hsel_μ,
              hne := hw.choose_spec.1, hentry := hw.choose_spec.2.1,
              helig := hw.choose_spec.2.2.1,
              hlen := hw.choose_spec.2.2.2.1,
              hmenu := hw.choose_spec.2.2.2.2 }
  else none

/-- the TOTAL consumption wrappers (REV 7, C11) — displayed defaults,
never realized (V3-3d's `writeHeights_total`): -/
noncomputable def instA {n : ℕ} (ε̊ : EntTemplate n) (h : Hpt ε̊.entDim) : ℕ :=
  ((writeHeights? ε̊ h).map EntShapeV.A).getD 0
noncomputable def instHentCode {n : ℕ} (ε̊ : EntTemplate n)
    (h : Hpt ε̊.entDim) : ℕ :=
  ((writeHeights? ε̊ h).map EntShapeV.hentCode).getD 0
```

REV-7 CONSUMPTION RULE (C11, binding): the Defs layer (§2.F/2.G) reads
the instantiation ONLY through `writeHeights?` and the displayed total
wrappers (`instA`/`instHentCode` here; `instCensus`/`instRealizable`/
`instLvl` at §2.F, after their carriers) — every default branch recorded,
none realized. UNIT layers (V3 up) may use the totalized
`def writeHeights (ε̊) (h) : EntShapeV n := (writeHeights? ε̊ h).get
(writeHeights_total ε̊ h)` — DECLARED AT V3-3d, downstream of its totality
theorem; the token `writeHeights` in V3–V7 statements means THAT def (no
forward reference anywhere: Defs is Option-typed, units are total).
The template family's FINITENESS is unit V3-4 (hypothesis-free). The
bijection of `writeHeights` onto {concrete realizable ε with template ε̊} is
unit V3-5 (theorem-under-hypotheses: GIVEN the entrance-layer exactness
`XHDdEnt` supplying H(ε̊) — §2.G — and V3-3(d)'s reconstruction laws).
V3-3's bridge additionally constructs the `MovesSp.EntranceShape n gsel musel`
behind (ε̊, h) — the consumption-map tie A-3 demanded (word + hMem + hChain +
hEntry transported; heights into the slot functions). ESCALATION HATCH
(recorded, Codex-6): IF V3-3(d) finds a ShapeRead datum genuinely NOT
determined by (species letter, slots, WF ties), the template gains that
datum as a field THEN, with a fresh audit pass — never silently.

### 2.E The marked space and μ̂ (keying to MovesD; the [3t] fence)

```lean
/-- ι_{e,ε,β₀}'s counting-native carrier: the ε-REFINED ENTRANCE INDEX — the
sub-family of Pref(P̂) (MovesD.PrefIdx, D4R.1-SUM's index) cut by the
landing-cell condition on the designated continuing branch (cell data, §D4-R
L5). `lands` is a PARAMETER field with its (D4)-tie: the cut is a CELL
condition, never a height condition (heights ride IN ε). -/
structure EntranceCut (n : ℕ) (ε : EntShapeV n) (p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] (pol : MovesD.CanonPolicy p F) where
  lands : MovesD.PrefIdx n pol ε.Phat → Prop
  decL  : DecidablePred lands
  lands_sel : ∀ i, lands i → SelMatches ε i
    -- THE SELECTION LAW, A FIELD at REV 7 (Codex6-C1: rev 6's "consumers
    -- conjoin SelMatches" was PROSE — the displayed carrier let a
    -- selection-ignoring cut pass, merging note-distinct sibling
    -- selections. Now every cut of every ε-refined index is
    -- SelMatches-bounded BY TYPE: `iotaCount` sums only over
    -- selection-matching prefixes, and V3-6's census cut / V5-1's marks
    -- inherit the law from the carrier, not from discipline.)

/-- The MARKED entrance mass at level N, division-free (the MovesC/MovesD
counting idiom): ι·p^{nN} = Σ over the refined index of fiber cards. Each
member is one realized branch prefix η with its Theorem C(b) mass — "ι is
their SUM — a D4R.1-SUM sub-sum, hence a μ̂-object; an f entering twice
carries two marks". The ℝ-valued ι of the seam is DEFINED at V7-4b from this
count and the entrance census/events (§2.F) — tied, not parallel. -/
noncomputable def iotaCount {n : ℕ} (ε : EntShapeV n) {p F pol}
    (cut : EntranceCut n ε p F pol) {N m : ℕ}
    (S : MovesD.Presented p F n N m pol ε.Phat) : ℕ :=
  ∑ᶠ i ∈ {i | cut.lands i}, Nat.card ↥(S.fiber i)
```

μ̂ FENCE (binding, from MovesS): every aggregate of `iotaCount`-type objects
that leaves this corpus is wrapped in `MovesS.MuHat` (no Add, no coercion) —
"the pairing ι_e^T β_e is the μ̂-typed MARKED-entrance total … NEVER a clause
of the density R_σ". No unit of this corpus states a per-f density.

### 2.F The counting carrier `CtsMeasured` (the `MeasuredSide` producer's data half)

REV 2 REDESIGN (C7/C24/A-1 repair) + REV 3 RE-WIRING (F-1/F-2/F-3/F-5,
Codex-7/10/15/16) + REV 4 (N-2's pool-through-history indexing; Codex-3's
digit-cell-keyed disjointness; the process-side marked events live in §2.G's
standalone `TmplEvents`, NOT here — see HMCAug's quantification note). `CtsMeasured` carries ONLY counting data: boxes,
per-assignment events, digit-cell classifiers, listed height domains,
entrance events and landing data — and, NEW at REV 3, the two INSTANCE-CENSUS
carriers the round-2 audit showed are NOT box events (their cards scale
differently in N — the F-1/F-2 conflation): the ε-instance census `entInst`
(D4R.4's marked-prefix census, box-realized at the defining level) and the
state-instance census `stInst` (the G4 pattern; cellP's rev-1 sizeP wiring).
Each census is tied to its box events by a TYPED division-free counting law
(`ent_card`, `evt_card` + `box_card`) — the fields Fable's adjudication hints
named, making the LedgerIV suite derivable (V7-6a). Digit cells are
OUTCOME-KEYED (`DCellO` — C8). The entrance side is TEMPLATE×COMPONENT-keyed
(A-1). Terminal twins per the §2.B substitution table.

```lean
/-- REV 7 (C10): the carrier is SPLIT — `CtsCells` holds the classifier
half (boxes, embeddings, digit cells, per-assignment events), so that
`AStep`/`CellOf`/`stepKey`/`evtOfStep` are REAL DISPLAYED DEFS over it
(rev 6 carried them as comments under `evt_disj_cell`, which nevertheless
consumed them — Codex6-C10); `CtsMeasured extends CtsCells` and states the
disjointness law through the parent's `stepKey`. -/
structure CtsCells (n : ℕ) (C : CtsFamily n) (S : StepSys n) where
  toStepCells : S.Cell ≃ Σ s : Skeleton n, (C.bd s).CellIdx
    -- 𝒞_n := {(s, α)} — the StepSys index IS the state space, typed once
  Pools : Set ℚ
  pools_sub : Pools ⊆ S.Pools
  pools_pp : ∀ q₀ ∈ Pools, ∃ (p : ℕ) (_ : p.Prime) (δ : ℕ+), q₀ = (p : ℚ) ^ (δ : ℕ)
  pools_closed : ∀ q₀ ∈ Pools, ∀ δ : ℕ+, q₀ ^ (δ : ℕ) ∈ Pools
  pools_infinite : Pools.Infinite      -- [C7: the MeasuredSide pool laws]
  Box  : ℚ → ℕ → Type                  -- level-N residue boxes (MovesD.Box keyed)
  finB : ∀ q₀ N, Fintype (Box q₀ N)
  boxpos : ∀ q₀ N, Nonempty (Box q₀ N)
  box_card : ∀ q₀ ∈ Pools, ∀ N, ((Fintype.card (Box q₀ N) : ℚ)) = q₀ ^ (n * N)
    -- [tie: MovesD.Box's card law at the real instance — the F-1/F-3 counting
    --  laws read |Box(N)| = q^{nN}; gate B: |Box(3)| = 2⁹ = 512]
  -- THE MOVE EMBEDDING, target tcell-ENFORCED BY TYPE (Codex-3; §2.C data):
  moveOf : ∀ d : MoveData n C,
    S.Move (toStepCells.symm d.src) (toStepCells.symm d.tgt)
  moveOf_bij : ∀ αc : S.Cell, Function.Bijective
    (fun d : {d : MoveData n C // toStepCells.symm d.src = αc} =>
      (⟨toStepCells.symm d.1.tgt, d.2 ▸ moveOf d.1⟩ : Σ βc, S.Move αc βc))
    -- S.Move αc βc is EMPTY unless βc is a tcell-image: the displayed (D4)
    -- target-cell map is load-bearing BY TYPE (Codex-3's second horn)
  moveOfT : ∀ {v : VLabel n} (d : TermData n C v),
    S.MoveT (toStepCells.symm ⟨d.s, d.α⟩) v
  moveOfT_bij : ∀ (αc : S.Cell) (v : VLabel n), Function.Bijective
    (fun d : {d : TermData n C v // toStepCells.symm ⟨d.1.s, d.1.α⟩ = αc} =>
      d.2 ▸ moveOfT d.1)                                            -- [+T]
  -- OUTCOME-KEYED digit cells (C8) + the classifiers (C2's tie):
  DCellO : ∀ (s : Skeleton n) (m : (C.bd s).Letter) (o : (C.bd s).Outc m),
    (C.bd s).CellIdx → Type
  finDO : ∀ s m o α, Fintype (DCellO s m o α)
  cellOfA : ∀ (d : MoveData n C) {q₀} (x : S.Hist q₀ (toStepCells.symm d.src))
    (h : Hpt (S.dim (moveOf d))),
    S.Assign (moveOf d) x h → DCellO d.s d.m d.o d.α
    -- every fresh assignment lies in EXACTLY ONE digit cell — D4R.0 totality
    -- at the assignment level, BY TYPE (a function, not a relation)
  cellOfAT : ∀ {v} (d : TermData n C v) {q₀} (x : S.Hist q₀ _)
    (h : Hpt (S.dimT (moveOfT d))),
    S.AssignT (moveOfT d) x h → DCellO d.s d.m d.o d.α              -- [+T]
  emult : ∀ {s m o α}, DCellO s m o α → ℕ
    -- the cell's eligible continuing-mark count (Codex-18: was prose) — L5
    -- data at the real instance (MovesD EligibleImage census); V4-7's surplus
    -- and §2.H consume it
  -- per-assignment box events; cell/entrance events are DEFINED from them
  -- (pools ride the history index — N-2):
  evtOf : ∀ {αc βc} (mv : S.Move αc βc) {q₀} (x : S.Hist q₀ αc)
    (h : Hpt (S.dim mv)), S.Assign mv x h → ∀ N : ℕ, Finset (Box q₀ N)
  evtOfT : ∀ {αc v} (mv : S.MoveT αc v) {q₀} (x : S.Hist q₀ αc)
    (h : Hpt (S.dimT mv)), S.AssignT mv x h → ∀ N : ℕ, Finset (Box q₀ N)

/-- one assignment step from (αc, x): continuing or terminal, with its
move, height, and fresh assignment (the heterogeneous Σ-carrier of the
REV-3 disjointness law) — a CLOSED DEF at REV 7 (C10). -/
def AStep {n} (S : StepSys n) (αc : S.Cell) {q₀} (x : S.Hist q₀ αc) : Type :=
  (Σ (β : S.Cell) (mv : S.Move αc β) (h : Hpt (S.dim mv)), S.Assign mv x h)
  ⊕ (Σ (v : VLabel n) (mv : S.MoveT αc v) (h : Hpt (S.dimT mv)),
      S.AssignT mv x h)

/-- the SOURCE-CELL digit-cell carrier at αc — LITERALLY the frozen
`MeasuredSide.Cell e τ = Σ o, DCellO` shape at the instance (REV 6 content,
now a REAL def — C10): -/
def CtsCells.CellOf {n C S} (W : CtsCells n C S) (αc : S.Cell) : Type :=
  (Σ d : {d : MoveData n C // W.toStepCells.symm d.src = αc},
     W.DCellO d.1.s d.1.m d.1.o d.1.α)
  ⊕ (Σ v, Σ d : {d : TermData n C v // W.toStepCells.symm ⟨d.1.s, d.1.α⟩ = αc},
     W.DCellO d.1.s d.1.m d.1.o d.1.α)

/-- the step's digit-cell key: (classified cell, Σ-embedded height).
The datum is recovered through the bijections' inverses
(`Function.invFun` of `moveOf_bij`/`moveOfT_bij` — noncomputable, licit;
`h2`/`hd` are the recovered datum's src/move identities, mechanical
▸-transports as in `castAssign`): -/
noncomputable def CtsCells.stepKey {n C S} (W : CtsCells n C S)
    {αc : S.Cell} {q₀} {x : S.Hist q₀ αc} (p : AStep S αc x) :
    W.CellOf αc × Σ D : ℕ, Hpt D :=
  match p with
  | .inl ⟨β, mv, h, a⟩ =>
      let d := Function.invFun
        (fun d : {d : MoveData n C // W.toStepCells.symm d.src = αc} =>
          (⟨W.toStepCells.symm d.1.tgt, d.2 ▸ W.moveOf d.1⟩ :
            Σ βc, S.Move αc βc)) ⟨β, mv⟩
      (Sum.inl ⟨d, W.cellOfA d.1 (d.2 ▸ x) _ (by
          -- transport a along the invFun identity (moveOf_bij surjective)
          exact castAssignKey W d mv h a)⟩,
       ⟨S.dim mv, h⟩)
  | .inr ⟨v, mv, h, a⟩ =>
      let d := Function.invFun
        (fun d : {d : TermData n C v // W.toStepCells.symm ⟨d.1.s, d.1.α⟩ = αc}
          => d.2 ▸ W.moveOfT d.1) mv
      (Sum.inr ⟨v, d, W.cellOfAT d.1 (d.2 ▸ x) _ (castAssignKeyT W d mv h a)⟩,
       ⟨S.dimT mv, h⟩)
  -- (`castAssignKey`/`castAssignKeyT`: the two ▸-transport wrappers along
  --  the invFun surjectivity identities — same zero-content pattern as
  --  §2.G's castAssign, declared beside this def; on the bijections'
  --  ranges — ALL of AStep, by moveOf_bij/moveOfT_bij — the key computes
  --  the assignment's own classified cell.)

/-- the step's event (unpacks to evtOf/evtOfT) — closed (C10): -/
def CtsCells.evtOfStep {n C S} (W : CtsCells n C S) {αc} {q₀}
    {x : S.Hist q₀ αc} (p : AStep S αc x) (N : ℕ) : Finset (W.Box q₀ N) :=
  match p with
  | .inl ⟨_, mv, h, a⟩ => W.evtOf mv x h a N
  | .inr ⟨_, mv, h, a⟩ => W.evtOfT mv x h a N

structure CtsMeasured (n : ℕ) (C : CtsFamily n) (S : StepSys n)
    extends CtsCells n C S where
  -- THE DISJOINTNESS LAW — RE-KEYED at REV 4 (Codex-3: rev 3's blanket
  -- AStep law `p ≠ p' → Disjoint` claimed ORDINARY-BOX disjointness across
  -- CONTINUATION MARKS too, but the note's (iv)-MEAS display says "the
  -- summands are pairwise disjoint IN THE MARKED SPACE; as f-events only
  -- the DIGIT CELLS are disjoint" — two marked summands may have literally
  -- EQUAL f-projections (one digit cell, two eligible continuations), and
  -- marked offspring mass may exceed 1. The claim is now keyed to the
  -- DIGIT-CELL KEY (letter, outcome, cell, height — terminal included):
  -- distinct KEYS ⟹ disjoint f-events (the D4R.0/PART-1 partition face);
  -- equal keys (mark-only differences): NOTHING claimed):
  evt_disj_cell : ∀ {αc q₀} (x : S.Hist q₀ αc) (p p' : AStep S αc x) (N : ℕ),
    toCtsCells.stepKey p ≠ toCtsCells.stepKey p' →
    Disjoint (toCtsCells.evtOfStep p N) (toCtsCells.evtOfStep p' N)
    -- THE KEY — REAL DEFS at REV 7 (Codex6-C10: rev 6's `CellOf`/`stepKey`
    -- existed only as comments here while this field consumed them; they
    -- are now the DISPLAYED closed defs over `CtsCells` above, and this
    -- law reads them through the parent projection). Narrowing as at
    -- REV 6 (Codex5-21/prior-4): the key lands in the SOURCE-CELL
    -- Σ-carrier `CellOf αc` — LITERALLY the shape of the frozen
    -- `MeasuredSide.Cell` (`Cell e τ = Σ o : Out e τ, DCellO (dataOf τ o)`,
    -- V7-4a) —
    -- so V7-6a2's d4r0 supply is DEFINITIONAL: `CellOf αc` IS the frozen
    -- Cell type at the instance (the moveOf_bij transport of Σ (m,o),
    -- DCellO at the one source), and the frozen `d4r0`'s (c, h) ≠ (c′, h′)
    -- quantifier is stepKey-inequality verbatim.
    -- THE MARKS RECORD (the Codex5-21 vs Fable-5 adjudication, displayed):
    -- the note's "two marked summands may have literally EQUAL
    -- f-projections (one digit cell, two eligible continuations)" is about
    -- MARKS — the ψ/member-selection multiplicity, which in this corpus is
    -- carried by `emult` (the per-cell eligible-mark COUNT) and by the
    -- marked Σ-carrier of V4-10, and is INVISIBLE at the AStep layer BY
    -- TYPE: a mark is not an AStep element (AStep has no member/ψ index;
    -- two marks over one fresh assignment are ONE AStep point), so no
    -- cross-mark pair is expressible as a key difference at all — nothing
    -- is claimed about marks (REV 7, C8: the marked-space disjointness is
    -- V4-10's DERIVED lemma; the within-cell per-ASSIGNMENT card step is
    -- the carrier [tie] `evt_disj_assign` below — no open MarkDisj
    -- hypothesis survives).
    -- Distinct KEYS mean distinct (outcome, digit cell) or distinct
    -- height AT ONE SOURCE — distinct collision-pattern/hinge f-strata
    -- (the outcome label is f-data; D4R.0/PART-1's partition face), and
    -- their f-disjointness is EXACTLY what the frozen `d4r0` itself
    -- asserts over its Σ-outcome `Cell` type (built Defs.lean 221–223:
    -- `(c, h) ≠ (c', h')` with c, c' : M.Cell e τ carrying their outcome
    -- index). The law is precisely as strong as its frozen consumer —
    -- no stronger, no weaker. [tie]
  -- THE PER-ASSIGNMENT COUNTING LAW (REV 3, F-3/Codex-10; REV-4 pools ride
  -- histories; C.1.5's counting semantics, discharged by MovesC/MovesD at
  -- the real instance):
  stabLvl : ∀ {αc βc}, S.Move αc βc → ℕ
  stabLvlT : ∀ {αc v}, S.MoveT αc v → ℕ                              -- [+T]
  evt_card : ∀ {αc βc} (mv : S.Move αc βc) {q₀} (x : S.Hist q₀ αc) (h)
    (a : S.Assign mv x h), q₀ ∈ Pools → S.zc x → ∀ N ≥ stabLvl mv,
    ((evtOf mv x h a N).card : ℝ)
      = S.massOf mv x h a * (Fintype.card (Box q₀ N) : ℝ)  -- [tie]
  evt_cardT : ∀ {αc v} (mv : S.MoveT αc v) {q₀} (x : S.Hist q₀ αc) (h) (a),
    q₀ ∈ Pools → S.zc x → ∀ N ≥ stabLvlT mv,
    ((evtOfT mv x h a N).card : ℝ)
      = S.massOfT mv x h a * (Fintype.card (Box q₀ N) : ℝ)  -- [tie, +T]
  -- WITHIN-CELL PER-ASSIGNMENT DISJOINTNESS — a CARRIER [tie] at REV 7
  -- (C8, adjudicated: this is C.1.5 COUNTING SEMANTICS — two distinct
  -- fresh assignments assign distinct fresh digits, occupying disjoint
  -- residue boxes — discharged at the real instance exactly like
  -- evt_card, NOT an open burden. The rev-4/5/6 `MarkDisj`/`MarkDisjT`
  -- named-hypothesis reading conflated ASSIGNMENTS with MARKS: PART-2's
  -- mark multiplicity is invisible at this layer — see the marks record
  -- above — and nothing about marks is claimed here):
  evt_disj_assign : ∀ {αc βc} (mv : S.Move αc βc) {q₀} (x : S.Hist q₀ αc)
    (h) (a a' : S.Assign mv x h), a ≠ a' →
    ∀ N, Disjoint (evtOf mv x h a N) (evtOf mv x h a' N)   -- [tie]
  evt_disj_assignT : ∀ {αc v} (mv : S.MoveT αc v) {q₀} (x : S.Hist q₀ αc)
    (h) (a a' : S.AssignT mv x h), a ≠ a' →
    ∀ N, Disjoint (evtOfT mv x h a N) (evtOfT mv x h a' N) -- [tie, +T]
  -- listed height domains, AS DATA (the [2b] packages assert their EXACTNESS
  -- — XHDd at template level, XHDdC at cell level (§2.G, NEW at REV 3);
  -- the lists themselves are this corpus's constructed data):
  cdom : ∀ (d : MoveData n C), DCellO d.s d.m d.o d.α → SemilinPart (S.dim (moveOf d))
  cdomT : ∀ {v} (d : TermData n C v), DCellO d.s d.m d.o d.α
    → SemilinPart (S.dimT (moveOfT d))                               -- [+T]
  mdom : ∀ (d : MoveData n C), SemilinPart (S.dim (moveOf d))
  mdomT : ∀ {v} (d : TermData n C v), SemilinPart (S.dimT (moveOfT d))
    -- the MOVE-level listed one-step domains (ValA.tbl_count's base-point
    -- keys). REV 4 (Codex-5): the identification with XHDd's length-1
    -- domain is now the TYPED coherence structure `MDomTie` (§2.G) — a
    -- displayed hypothesis of every unit that transports tbl_count across
    -- a component (V2-5, V4-5, V5-8, V7-5a); [1v] states its lists
    -- XHD-free (VAL(a)'s duty), [2b]'s exactness binds them through the tie
  -- activity:
  activeState : ℚ → S.Cell → Prop     -- |α|(q₀) > 0 (Act_{q₀}'s predicate)
  act_size : ∀ q₀ ∈ Pools, ∀ c : S.Cell, activeState q₀ c ↔
    ((C.bd (toStepCells c).1).sizeP (toStepCells c).2.1).eval q₀ ≠ 0
  -- THE STATE-INSTANCE CENSUS (REV 3, F-5's revert + Codex-16: cellP's
  -- rev-1 sizeP wiring needs the state-census carriers; the G4 pattern
  -- "instance events whose card IS the cell size"):
  stLvl : S.Cell → ℕ
  stInst : S.Cell → ∀ (q₀ : ℚ) (N : ℕ), Finset (Box q₀ N)
  stInst_card : ∀ (c : S.Cell) (q₀ : ℚ), q₀ ∈ Pools →
    ((stInst c q₀ (stLvl c)).card : ℚ)
      = ((C.bd (toStepCells c).1).sizeP (toStepCells c).2.1).eval q₀  -- [tie]
  -- ENTRANCE SIDE, template×component-keyed (A-1):
  entDom : ∀ ε̊ : EntTemplate n, SemilinPart ε̊.entDim   -- H(ε̊), LISTED (data)
  entLands : EntTemplate n → S.Cell → Prop   -- "entering the size-e block
  decLands : ∀ ε̊, DecidablePred (entLands ε̊) -- landing in cell β₀" (the
                                             -- ε-triple's landing datum)
  entEvt : ∀ (ε : EntShapeV n) (β₀ : S.Cell), ∀ (q₀ : ℚ) (N : ℕ),
    Finset (Box q₀ N)                  -- concrete-ε entrance BOX events
  entLvl : EntTemplate n → ℕ           -- the stabilization level per template
  -- THE ε-INSTANCE CENSUS (REV 3, F-1/F-2/Codex-7: the carrier the round-2
  -- audit demanded — D4R.4's finite marked-prefix census, box-realized at
  -- the defining level; NOT the box event entEvt, whose card scales as
  -- q^{nN−A}):
  entInst : ∀ (ε : EntShapeV n) (β₀ : S.Cell), ∀ (q₀ : ℚ) (N : ℕ),
    Finset (Box q₀ N)
  -- THE ENTRANCE COUNTING LAW, division-free (F-1's typed repair; discharged
  -- by the EXPORTED MovesD.D4R1_SUM/D0b_thmCtop at the real instance — G-4):
  ent_card : ∀ (ε : EntShapeV n) (β₀ : S.Cell) (q₀ : ℚ), q₀ ∈ Pools →
    ∀ N ≥ (ε.template?).elim 0 entLvl,
    ((entEvt ε β₀ q₀ N).card : ℚ) * q₀ ^ (ε.A : ℕ)
      = ((entInst ε β₀ q₀ ((ε.template?).elim 0 entLvl)).card : ℚ)
          * q₀ ^ (n * N)
    -- [tie] (REV 7, C11: the level reads through `template?` — default 0,
    -- dead at consumption by V3-3b's totality.) gate B (q₀ = 2, n = 3,
    -- A = 3, N = 3): 128·2³ = 2·2⁹ ✓ — the
    -- event card is I^ent·q^{nN−A} = 128, and the census is I^ent(2) = 2:
    -- F-1's 128-not-8192 acceptance number
  -- THE SELECTION-SEPARATION LAW (NEW at REV 7, Codex6-C1: rev 6 keyed
  -- entEvt/entInst by the FULL label but no law READ the selection
  -- component — a selection-ignoring instance could merge note-distinct
  -- sibling selections). Typed at the census: sibling labels (same P̂ —
  -- hence same heights — same designated (g, μ)) differing in selRec have
  -- DISJOINT mark-census realizations at the defining level. FAITHFUL:
  -- this is ENT-AGG's own μ̂-additivity face ("distinct concrete ε give
  -- distinct marked pairs" — a realized branch η takes DEFINITE
  -- selections, so the sibling mark families partition) typed on the
  -- count-realizing carrier (entInst is the D4R.4 census box-REALIZED —
  -- an encoding Finset, F-2's distinction, so a joint injective
  -- realization at the defining level exists; the instance picks it).
  -- NO f-event analogue is stated for entEvt: sibling marks over one f
  -- share f-residues (PART-2's permission) — entEvt's selection tie is
  -- ent_card + THIS census law + the V3-6(c)/V7-4b cut identification
  -- (whose cuts are `lands_sel`-bounded BY TYPE, §2.E):
  ent_sel : ∀ (ε ε' : EntShapeV n) (β₀ : S.Cell) (q₀ : ℚ), q₀ ∈ Pools →
    ε.Phat = ε'.Phat → ε.gsel = ε'.gsel → ε.musel = ε'.musel →
    ε.selRec ≠ ε'.selRec →
    Disjoint (entInst ε β₀ q₀ ((ε.template?).elim 0 entLvl))
      (entInst ε' β₀ q₀ ((ε'.template?).elim 0 entLvl))
```

Derived defs (displayed here; no free data behind them; the [+T] twins
DISPLAYED — Codex-14):
```lean
/-- fixed-height CELL events := the union of the cell's assignments' events
(C2's demanded tie: cellEvt ↔ Assign ↔ cntraw, definitional). N-2: the pool
rides x. -/
noncomputable def CtsMeasured.cellEvt (V : CtsMeasured n C S)
    (d : MoveData n C) {q₀} (x : S.Hist q₀ _) (c : V.DCellO d.s d.m d.o d.α)
    (h : Hpt (S.dim (V.moveOf d))) (N : ℕ) : Finset (V.Box q₀ N) :=
  (Finset.univ.filter (fun a : S.Assign (V.moveOf d) x h =>
    V.cellOfA d x h a = c)).biUnion (fun a => V.evtOf (V.moveOf d) x h a N)
noncomputable def CtsMeasured.cellEvtT (V : CtsMeasured n C S) {v}
    (d : TermData n C v) {q₀} (x : S.Hist q₀ _) (c : V.DCellO d.s d.m d.o d.α)
    (h : Hpt (S.dimT (V.moveOfT d))) (N : ℕ) : Finset (V.Box q₀ N) :=
  (Finset.univ.filter (fun a : S.AssignT (V.moveOfT d) x h =>
    V.cellOfAT d x h a = c)).biUnion (fun a => V.evtOfT (V.moveOfT d) x h a N)

/-- the cell-refined MARKED count T_c(h) from x at x's pool — again a def. -/
def CtsMeasured.cntc (V : CtsMeasured n C S) (d : MoveData n C)
    {q₀} (x : S.Hist q₀ _) (c : V.DCellO d.s d.m d.o d.α)
    (h : Hpt (S.dim (V.moveOf d))) : ℕ :=
  (Finset.univ.filter (fun a : S.Assign (V.moveOf d) x h =>
    V.cellOfA d x h a = c)).card
def CtsMeasured.cntcT (V : CtsMeasured n C S) {v} (d : TermData n C v)
    {q₀} (x : S.Hist q₀ _) (c : V.DCellO d.s d.m d.o d.α)
    (h : Hpt (S.dimT (V.moveOfT d))) : ℕ :=
  (Finset.univ.filter (fun a : S.AssignT (V.moveOfT d) x h =>
    V.cellOfAT d x h a = c)).card

-- [THE REV-4/5 `MarkDisj`/`MarkDisjT` HYPOTHESIS DEFS ARE STRUCK at
--  REV 7 (C8, adjudicated). What they QUANTIFIED was per-ASSIGNMENT
--  within-cell disjointness — C.1.5 counting semantics (distinct fresh
--  digits, disjoint boxes), now the CtsMeasured carrier [tie]s
--  `evt_disj_assign`/`evt_disj_assignT` above, discharged at the real
--  instance like evt_card; what their PROSE claimed ("distinct MARKS
--  realize disjoint f-events … open where PART-2's surplus lives") was a
--  conflation — the note's (iv)-MEAS disjointness is IN THE MARKED SPACE
--  and DERIVABLE there (the mark is ADJOINED and determines its
--  (m, o, β, height-class) reading, MOVES 8185–8197). The NAMES survive
--  as V4-10's derived marked-space lemmas `MarkDisj`/`MarkDisjT` (the
--  Σ-carrier's mark coordinate separates summands); LedgerIV (V7-6a1)
--  and V7-1 carry NO MarkDisj hypothesis fields any more.]

/-- THE ε-INSTANCE COUNT — a DEF (card of the census at the defining level):
I^ent_{ε,β₀}(q₀), the note's marked-prefix count. NOT an event card at a
box level (F-2's repair): its q₀-dependence is the polynomial ENT-COUNT
burden (deg ≤ W_ent), never a q^{nN−A} scaling. -/
noncomputable def CtsMeasured.entCensus (V : CtsMeasured n C S)
    (ε : EntShapeV n) (β₀ : S.Cell) (q₀ : ℚ) : ℕ :=
  (V.entInst ε β₀ q₀ ((ε.template?).elim 0 V.entLvl)).card
  -- (REV 7, C11: through `template?` — default level 0, dead by totality)

/-- the REV-7 (C11) total consumption wrappers over `writeHeights?` that
need the carrier V (companions of §2.D's `instA`/`instHentCode`);
defaults recorded, never realized (V3-3d's totality): -/
noncomputable def CtsMeasured.instCensus (V : CtsMeasured n C S)
    (ε̊ : EntTemplate n) (h : Hpt ε̊.entDim) (β₀ : S.Cell) (q₀ : ℚ) : ℕ :=
  ((writeHeights? ε̊ h).map (fun ε => V.entCensus ε β₀ q₀)).getD 0
def CtsMeasured.instRealizable (V : CtsMeasured n C S) (ε̊ : EntTemplate n)
    (h : Hpt ε̊.entDim) (β₀ : S.Cell) : Prop :=
  ∃ ε ∈ writeHeights? ε̊ h, Realizable V ε β₀
  -- (`Realizable` is declared in §2.G BELOW; in the E-file this wrapper
  --  sits after it — reading-order note only, no forward reference in
  --  the build: both live in the one Defs file, Realizable first.)

/-- THE ENTRANCE INDEX (A-1's carrier, DECLARED): template × listed component,
landing at β₀ — FINITE (V3-4 × list length), the type `MovesS.MeasuredSide.
EntShape e τ` instantiates. -/
def CtsMeasured.EntIx (V : CtsMeasured n C S) (β₀ : S.Cell) : Type :=
  {p : Σ ε̊ : EntTemplate n, Fin (V.entDom ε̊).comps.length // V.entLands p.1 β₀}

/-- entrance count per EntIx member := the CENSUS at the component's base
instantiation (F-2/Codex-7 repair: the census, never the box-event card; the
polynomial across the WHOLE component being this same value is exactly
(ENT-U) — V3-9b — cited where consumed, never baked in). Gate B: entCount =
I^ent(q₀) = q₀(q₀−1), degree 2 ≤ Went = 3 — the ent-degree ledger
(ι_degT/degT_le vs Went) is jointly satisfiable again. -/
noncomputable def CtsMeasured.entCount (V : CtsMeasured n C S) {β₀}
    (i : V.EntIx β₀) (q₀ : ℚ) : ℕ :=
  V.instCensus i.1.1 ((V.entDom i.1.1).comps.get i.1.2).base β₀ q₀
  -- (REV 7, C11: the instCensus wrapper — the rev-6 body verbatim once
  --  totality lands)
```

The rev-1 fields `tbl_count`, `μcell`, `ιval`, `entCount`(free), `DCell`
(move-keyed), and the loose "from 2.E" pointers are GONE: the table-count
semantics is `ValA`'s field content (V2-4 — VAL(a)'s burden, where the note
itself places it: "alternative discharge: the table build proves
representative-uniform count rows per species"); the measured ℝ-objects are
V7-4a/b/c definitions; A-7's pointer hygiene is moot (each object has one
home).

### 2.G Templates, the two-sided count architecture (table side + process side — the REV-4 N-1 split), XHD-d/-s (all faces), the bundle, HMC, and the COMP typing (V.1(iv)–(vi), V.4)

```lean
/-- A finite path template γ in block e (V.1(vi)): β₀ →^{m₁,o₁} β₁ → … → β_k,
length ≥ 1, with the rev-4 TERMINAL-FINAL EXTENSION: the final step may carry
a terminal outcome — "there β_k := the absorbing column label [o_k] — an EXIT
OBJECT … the label consumed only as a column index", heights/weight/count
typed as for any read, NO target-cell map consumed. -/
inductive Template (n : ℕ) (S : StepSys n) : S.Cell → Type
  | last  {α β} (m : S.Move α β)  : Template n S α
  | lastT {α v} (m : S.MoveT α v) : Template n S α
  | cons  {α β} (m : S.Move α β) (γ : Template n S β) : Template n S α

def Template.D {n S} : ∀ {α}, Template n S α → ℕ    -- total height dimension
  | _, .last m => S.dim m | _, .lastT m => S.dimT m
  | _, .cons m γ => S.dim m + γ.D

/-- THE TABLE-SIDE CHAIN COUNT T_γ(x, h) — A DEF, recursive by definition
(C2/C9/A-2; **REV-4 SCOPE PER THE N-1 ADJUDICATION**: this recursion is the
TABLE side — the combinatorial count of iterated fresh-assignment
extensions, the object VAL(b)/(u-T)/the count shadow consume. It is NOT the
definition of the process domain H(γ): rev 3 keyed XHDd's exactness to this
count, and the recursion + the ∀-representative no-stray PROVED HMC in four
lines — the interface over-commitment Fable N-1 displayed. H(γ) is
process-side, below.) N-2: counts at x's pool throughout. -/
def chainCount {n} (S : StepSys n) :
    ∀ {α} (γ : Template n S α) {q₀}, S.Hist q₀ α → Hpt γ.D → ℕ
  | _, .last m,  x, h => S.cntraw m x h
  | _, .lastT m, x, h => S.cntrawT m x h
  | _, .cons m γ, x, h =>
      ∑ a : S.Assign m x (Hpt.take h), chainCount S γ (S.ext m x _ a) (Hpt.drop h)
-- (Hpt.take/drop: the Fin-append splitters, §2.A closed defs.)

/-- THE PROCESS-SIDE MARKED-EVENT CARRIER (NEW at REV 4 — the N-1
adjudication's fix: "process side H(γ) defined from the realized marked
events"). The vocabulary is the note's (vi) COMP display (MOVES 8225–8232):
"the MARKED EVENT of (ε, γ, h) is the family of marked pairs (f, η) — its
MARK-INDEX family (the realized histories η) is FINITE per level and its
level-N residue census is finite (D4R.4); the f-fibers are p-adic boxes,
generally INFINITE". Fields: per (template, source history, height point),
the level-N BOX REALIZATION `tevt` of the marked event and its MARK CENSUS
`tinst` — FREE DATA at composite templates (their tie to the step layer is
EXACTLY the (v)/(vi) content), tied to the step layer ONLY at length 1 and
through the two note-definitional mark facts. `Box` is its own carrier
(MovesD.Box at the real instance — V7-4a identifies it with
CtsMeasured.Box), so `HMCAug`'s refined systems quantify cleanly. -/
structure TmplEvents (n : ℕ) (S : StepSys n) where
  Box  : ℚ → ℕ → Type
  finB : ∀ q₀ N, Fintype (Box q₀ N)
  tevt : ∀ {α} (γ : Template n S α) {q₀} (x : S.Hist q₀ α),
    Hpt γ.D → ∀ N : ℕ, Finset (Box q₀ N)
  tinst : ∀ {α} (γ : Template n S α) {q₀} (x : S.Hist q₀ α),
    Hpt γ.D → ∀ N : ℕ, Finset (Box q₀ N)   -- the mark census, box-realized
  tmplLvl : ∀ {α}, Template n S α → ℕ       -- census-defining level
  -- THE LENGTH-1 TIE [tie]: a one-step marked event is realized iff a fresh
  -- assignment exists (its marks ARE the fresh assignments; the f-fiber of
  -- a fresh assignment is a nonempty digit cell — C.1.5 mass-positivity):
  tevt_last_iff : ∀ {α β} (m : S.Move α β) {q₀} (x : S.Hist q₀ α) (h),
    q₀ ∈ S.Pools → S.zc x →
    ((∃ N₀, ∀ N ≥ N₀, (tevt (.last m) x h N).Nonempty) ↔ 0 < S.cntraw m x h)
  tevt_lastT_iff : ∀ {α v} (m : S.MoveT α v) {q₀} (x : S.Hist q₀ α) (h),
    q₀ ∈ S.Pools → S.zc x →
    ((∃ N₀, ∀ N ≥ N₀, (tevt (.lastT m) x h N).Nonempty) ↔ 0 < S.cntrawT m x h)
  -- THE TWO MARK FACTS [tie], definitional in the note, typed here because
  -- tevt/tinst are free data: (i) a realized event HAS a mark; (ii) the
  -- marks are fresh-assignment CHAINS ("the realized histories η"):
  real_marks : ∀ {α} (γ : Template n S α) {q₀} (x : S.Hist q₀ α) (h),
    q₀ ∈ S.Pools → S.zc x → (∃ N₀, ∀ N ≥ N₀, (tevt γ x h N).Nonempty) →
    0 < (tinst γ x h (tmplLvl γ)).card
  marks_chains : ∀ {α} (γ : Template n S α) {q₀} (x : S.Hist q₀ α) (h),
    q₀ ∈ S.Pools → S.zc x →
    (tinst γ x h (tmplLvl γ)).card ≤ chainCount S γ x h
  marks_realize : ∀ {α} (γ : Template n S α) {q₀} (x : S.Hist q₀ α) (h),
    q₀ ∈ S.Pools → S.zc x → 0 < (tinst γ x h (tmplLvl γ)).card →
    ∃ N₀, ∀ N ≥ N₀, (tevt γ x h N).Nonempty
    -- THE THIRD MARK FACT (NEW at REV 7, C6): a mark IS a realized
    -- history whose f-fiber is a nonempty p-adic box (the (vi) display),
    -- so a positive mark census realizes the event — note-definitional,
    -- typed because tevt/tinst are free data. With real_marks this gives
    -- the equivalence `TReal ↔ 0 < Tgam` (the §2.G lemma below); it adds
    -- NO composite recursion (census cards at (.cons m γ) stay untied to
    -- the step layer), so HMC's openness is untouched.
  -- NO composite-template law relates tevt/tinst at (.cons m γ) to the step
  -- layer. In particular NO census recursion exists: marks may fail to be
  -- f-realized at composites (empty deep fibers — (HMC-AUG)'s cone
  -- coupling), which is exactly what keeps (v) OPEN below. The (COMP-h)
  -- mass identity at REALIZED points is the THEOREM V5-2, GIVEN (U-A) +
  -- (XHD-u), never a carrier law.

/-- THE NOTE'S OWN T_γ — A TYPED DIRECT COUNT (NEW at REV 7, C6,
adjudicated): "T_γ(x, h) := #{fresh-assignment chains from x realizing
(γ, h)} — a finite count at each level" (MOVES 7921–7923). The realized
chains ARE the marks ("the realized histories η" — the marks_chains
fact), so the direct count is the MARK CENSUS CARD at the defining
level — over the PROCESS carrier, NOT the recursive product (the
factorization T_γ = ∏ᵢ T_step is (u-T)/HMC CONTENT and must never be
definitional; `chainCount` stays the TABLE side): -/
def Tgam {n S} (TE : TmplEvents n S) {α} (γ : Template n S α)
    {q₀} (x : S.Hist q₀ α) (h : Hpt γ.D) : ℕ :=
  (TE.tinst γ x h (TE.tmplLvl γ)).card

/-- PROCESS REALIZATION — DEMOTED to a DERIVED notion at REV 7 (C6):
eventual event nonemptiness at x's pool. Its tie to the note's T_γ is
the LEMMA `treal_iff_tgam (hq : q₀ ∈ S.Pools) (hzc : S.zc x) :
TReal TE γ x h ↔ 0 < Tgam TE γ x h` — the → leg is `real_marks`, the ←
leg the REV-7 `marks_realize`; proved at V1-3, cited wherever the event
reading is needed (V5-1's guard, the entrance symmetry note). -/
def TReal {n S} (TE : TmplEvents n S) {α} (γ : Template n S α)
    {q₀} (x : S.Hist q₀ α) (h : Hpt γ.D) : Prop :=
  ∃ N₀, ∀ N ≥ N₀, (TE.tevt γ x h N).Nonempty

/-- (XHD-d) DOMAINS, typed — RE-KEYED at REV 7 (C6, adjudicated;
supersedes the REV-4 `TReal` keying, which SUBSTITUTED event
realization for the note's count): per template an EXPLICITLY LISTED
pairwise-disjoint semilinear PARTITION of the EXACT realizable height
domain, exact two-sidedly. The note's display (MOVES 7947–7949),
VERBATIM at the note's own object: "(no orphan) T_γ(x, h) > 0 for some
representative x ⟹ h ∈ H(γ); (no stray) h ∈ H(γ) ⟹ T_γ(x, h) > 0 for
EVERY representative x of α" — T_γ = the §2.G DIRECT COUNT `Tgam` (the
note DEFINES T_γ at MOVES 7921–7923; the mark census IS that count).
The rev-3 keying to the recursive `chainCount` stays STRUCK (it proved
HMC); Tgam is process-side (free at composites), so the openness
argument is unchanged. no_orphan's pointwise form implies the note's
"for some representative" form. Owner [2b]. -/
structure XHDd (n : ℕ) (S : StepSys n) (TE : TmplEvents n S) where
  dom : ∀ {α} (γ : Template n S α), SemilinPart γ.D
  no_orphan : ∀ {α} (γ : Template n S α) {q₀} (x : S.Hist q₀ α) (h : Hpt γ.D),
    q₀ ∈ S.Pools → S.zc x → 0 < Tgam TE γ x h → (dom γ).Mem h
  no_stray : ∀ {α} (γ : Template n S α) (h : Hpt γ.D),
    (dom γ).Mem h → ∀ {q₀}, q₀ ∈ S.Pools → ∀ x : S.Hist q₀ α, S.zc x →
    0 < Tgam TE γ x h
  -- COUNT SUPPLY (derived, not a field): membership ⟹ positive TABLE-side
  -- count at every zc representative, via Mem → (no_stray) 0 < Tgam →
  -- (marks_chains: Tgam ≤ chainCount) 0 < chainCount. Stated as unit
  -- V1-3's lemma `mem_chainCount_pos`;
  -- V2-5/V4-5/V5-8 consume it. The CONVERSE (chainCount > 0 → Tgam > 0)
  -- is NOT derivable at composite templates — combinatorial chains need
  -- not be f-realized ((HMC-AUG)'s coupling) — and that one-way gap is
  -- precisely what keeps HMC below out of theorem-hood. The EVENT
  -- reading is recovered where needed by `treal_iff_tgam` (V1-3, from
  -- real_marks + marks_realize) — HMC-safe: no composite recursion, no
  -- count→realization link beyond the census's own card.

/-- THE mdom COHERENCE TIE (NEW at REV 4, Codex-5: rev 3 had "no law
identifying `mdom d` with `XHDd.dom (.last (moveOf d))`"). [1v] lists its
one-step domains XHD-free (VAL(a)); when the [2b] package is in scope, the
lists coincide — a displayed hypothesis of every base-point transport
(V2-5(b), V4-5, V5-8, V7-5a). Base realizability follows: base ∈ mdom d
= dom(.last …) → no_stray → 0 < Tgam → count > 0 (V1-3's lemma, via
marks_chains — REV 7, C6) — u_T's
transport from tbl_count's base points is licit. -/
structure MDomTie {n} {S : StepSys n} {C : CtsFamily n}
    (V : CtsMeasured n C S) (TE : TmplEvents n S) (D : XHDd n S TE) : Prop where
  mdom_eq : ∀ (d : MoveData n C), D.dom (.last (V.moveOf d)) = V.mdom d
  mdomT_eq : ∀ {v} (d : TermData n C v), D.dom (.lastT (V.moveOfT d)) = V.mdomT d

/-- ∏ᵢ g_i(h_i): the fixed-height template weight — the TABLE side's weight
product, a def over XHDw by recursion on γ (DISPLAYED at REV 4 — Codex-14's
`…`). -/
noncomputable def gProd {n S} (W : XHDw n S) :
    ∀ {α} (γ : Template n S α), Hpt γ.D → ℚ → ℝ
  | _, .last m,  h, q₀ => (q₀ : ℝ) ^ (-((W.E m).eval h : ℤ))
  | _, .lastT m, h, q₀ => (q₀ : ℝ) ^ (-((W.ET m).eval h : ℤ))
  | _, .cons m γ, h, q₀ =>
      (q₀ : ℝ) ^ (-((W.E m).eval (Hpt.take h) : ℤ)) * gProd W γ (Hpt.drop h) q₀

/-- (XHD-s) SUMS, template face, typed: per LISTED linear set, the height sum
of the weight product is ONE ℚ(q) element in the note's geometric-denominator
class (denominators ∣ X^b·∏(1 − X^a)), convergent at every pool evaluation.
"By XHD-d's disjointness the finitely many component sums ADD EXACTLY to the
H(γ)-sum" is unit V0-3 + V5-4's consumption, not a field. Owner [2b].
(REV 4: D rides over the process side — the sums are still TABLE-side
weight sums over the LISTED components; G stays recursive-by-definition
exactly as the adjudication fixes.) -/
structure XHDs (n : ℕ) (S : StepSys n) (W : XHDw n S) {TE : TmplEvents n S}
    (D : XHDd n S TE) where
  Gc : ∀ {α} (γ : Template n S α), Fin (D.dom γ).comps.length → Qq
  Gc_denom : ∀ {α} (γ : Template n S α) (j), ∃ b (as : Finset ℕ+),
    (Gc γ j).denom ∣ Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a : ℕ))
  Gc_ok : ∀ {α} (γ : Template n S α) (j) (q₀ : ℚ), q₀ ∈ S.Pools →
    Gc γ j ∈ OKat q₀
  Gc_hasSum : ∀ {α} (γ : Template n S α) (j) (q₀ : ℚ) (hq : q₀ ∈ S.Pools),
    HasSum (fun h : {h // ((D.dom γ).comps.get j).Mem h} =>
        gProd W γ h.1 q₀)
      ((evalAt q₀ ⟨Gc γ j, Gc_ok γ j q₀ hq⟩ : ℚ) : ℝ)

/-- THE CELL D-FACE (NEW at REV 3 — F-3's missing face: the XHD bundle had a
d-face for templates and entrances and NONE for digit cells): per digit cell,
the listed `cdom` is exact two-sidedly against the cell-refined count —
h ∈ cdom(c) ⟺ cntc(c, h) > 0. Supplies LedgerIV.xhd_no_stray/no_orphan
through the evt_card nonemptiness tie (V7-6a). Owner [2b]. -/
structure XHDdC (n : ℕ) (S : StepSys n) {C : CtsFamily n}
    (V : CtsMeasured n C S) where
  -- (REV 4: pool-per-history + zc guards, N-2/Codex-12; the LISTS stay
  -- pool-uniform, exactness holds per pool. Length-1 count- and process-
  -- keying agree through tevt_last_iff, so no second HMC leak opens here.)
  no_orphanC : ∀ (d : MoveData n C) {q₀} (x : S.Hist q₀ _)
    (c : V.DCellO d.s d.m d.o d.α) (h : Hpt (S.dim (V.moveOf d))),
    q₀ ∈ V.Pools → S.zc x → 0 < V.cntc d x c h → (V.cdom d c).Mem h
  no_strayC : ∀ (d : MoveData n C) (c) (h), (V.cdom d c).Mem h →
    ∀ {q₀}, q₀ ∈ V.Pools → ∀ x : S.Hist q₀ _, S.zc x → 0 < V.cntc d x c h
  no_orphanCT : ∀ {v} (d : TermData n C v) {q₀} (x : S.Hist q₀ _) (c) (h),
    q₀ ∈ V.Pools → S.zc x → 0 < V.cntcT d x c h → (V.cdomT d c).Mem h
  no_strayCT : ∀ {v} (d : TermData n C v) (c) (h), (V.cdomT d c).Mem h →
    ∀ {q₀}, q₀ ∈ V.Pools → ∀ x : S.Hist q₀ _, S.zc x → 0 < V.cntcT d x c h

/-- (XHD-s) CELL FACE — RE-KEYED WEIGHT-ONLY at REV 3 (F-4/Codex-9: the rev-2
count-bearing `Gcell` with `cell_refine : Σ Gcell = Σ Gc` forced T ≡ 1 — the
(q−1)² adversary — AND, count-bearing, it decided (J-RAT)'s ℚ(q)-membership
by hypothesis). The [2b] height-sum face proper carries the WEIGHT g alone
per (cell, listed component); the COUNT factor enters only through the typed
[1v] burden `CellPolyPack` at the definition sites (V7-4c's gwt/μcell), and
the count-bearing refinement identity Σ_c P_c·ΣGcell = T·ΣGc is the DERIVED
unit V5-8 — count factor displayed, nothing collapsed, nothing decided.
Owner [2b]. -/
structure XHDsC (n : ℕ) (S : StepSys n) (W : XHDw n S) {TE : TmplEvents n S}
    (D : XHDd n S TE) {C : CtsFamily n} (V : CtsMeasured n C S)
    (Xs : XHDs n S W D) where
  Gcell : ∀ (d : MoveData n C) (c : V.DCellO d.s d.m d.o d.α)
    (j : Fin (V.cdom d c).comps.length), Qq
  Gcell_denom : ∀ d c j, ∃ b (as : Finset ℕ+),
    (Gcell d c j).denom ∣ Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a:ℕ))
  Gcell_ok : ∀ d c j (q₀ : ℚ), q₀ ∈ S.Pools → Gcell d c j ∈ OKat q₀
  Gcell_hasSum : ∀ (d) (c) (j) (q₀) (hq : q₀ ∈ S.Pools),
    HasSum (fun h : {h // ((V.cdom d c).comps.get j).Mem h} =>
        W.g (V.moveOf d) h.1 q₀)
      ((evalAt q₀ ⟨Gcell d c j, Gcell_ok d c j q₀ hq⟩ : ℚ) : ℝ)
    -- WEIGHT-ONLY: no cntc factor, no x quantifier — the count polynomial
    -- multiplies OUTSIDE (V7-4c), where CellPolyPack types it
  GcellT : ∀ {v} (d : TermData n C v) (c : V.DCellO d.s d.m d.o d.α)
    (j : Fin (V.cdomT d c).comps.length), Qq                        -- [+T]
  GcellT_denom : ∀ {v} (d : TermData n C v) c j, ∃ b (as : Finset ℕ+),
    (GcellT d c j).denom ∣ Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a:ℕ))
  GcellT_ok : ∀ {v} (d : TermData n C v) c j (q₀ : ℚ),
    q₀ ∈ S.Pools → GcellT d c j ∈ OKat q₀
  GcellT_hasSum : ∀ {v} (d : TermData n C v) (c) (j) (q₀) (hq : q₀ ∈ S.Pools),
    HasSum (fun h : {h // ((V.cdomT d c).comps.get j).Mem h} =>
        (q₀ : ℝ) ^ (-((W.ET (V.moveOfT d)).eval h.1 : ℤ)))
      ((evalAt q₀ ⟨GcellT d c j, GcellT_ok d c j q₀ hq⟩ : ℚ) : ℝ)   -- [+T]

/-- (XHD-s) ENTRANCE FACE — RE-KEYED WEIGHT-ONLY at REV 3 (Codex-8: the rev-2
face summed the full count·weight mass ιshH, which (i) double-counted against
V3-9c's countT×geom PolyGeom and (ii) silently DECIDED the INIT-RAT burden.
The note's own split: "the note's XHD-s shallow face supplies the geometric
sum of WEIGHTS; (ENT-U) and ENT-COUNT are then needed to extract a constant
count polynomial"). Per entrance-index member (template ε̊, listed component
j of H(ε̊)): the height sum of the C(b) WEIGHT q^{−A(ε̊[h])} alone is one
ℚ(q) element of the class, convergent at pools. Owner [2b]. -/
structure XHDsEnt (n : ℕ) (S : StepSys n) {C : CtsFamily n}
    (V : CtsMeasured n C S) where
  Gent : ∀ (β₀ : S.Cell) (i : V.EntIx β₀), Qq
  Gent_denom : ∀ β₀ i, ∃ b (as : Finset ℕ+),
    (Gent β₀ i).denom ∣ Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a:ℕ))
  Gent_ok : ∀ β₀ i (q₀ : ℚ), q₀ ∈ V.Pools → Gent β₀ i ∈ OKat q₀
  Gent_hasSum : ∀ β₀ (i : V.EntIx β₀) (q₀) (hq : q₀ ∈ V.Pools),
    HasSum (fun h : {h // ((V.entDom i.1.1).comps.get i.1.2).Mem h} =>
        (q₀ : ℝ) ^ (-((instA i.1.1 h.1 : ℕ) : ℤ)))
      ((evalAt q₀ ⟨Gent β₀ i, Gent_ok β₀ i q₀ hq⟩ : ℚ) : ℝ)
    -- WEIGHT-ONLY: the count I^ent multiplies OUTSIDE, through ENT-COUNT +
    -- (ENT-U) at V3-9c/V7-4b — the burdens stay burdens. (REV 7, C11:
    -- the exponent reads §2.D's `instA` wrapper.)
  -- (REV 5, Codex-8: the rev-4 `mass_summable` FIELD is REMOVED from this
  --  structure — packing the count-weighted aggregate's summability into
  --  XHDsEnt silently STRENGTHENED the frozen XHD-s, whose shallow face
  --  asserts geometric summability of WEIGHT sums only. REV 7, C7: the
  --  rev-5 replacement `EntMassSummable` was ITSELF a silent
  --  strengthening — the note's ENT-AGG ledger line gives convergence
  --  "GIVEN XHD-s on the shallow layer" ALONE, so a separate named
  --  summability burden ADDED a hypothesis the note does not levy. It is
  --  STRUCK: V3-8a's premise is THIS structure, and the count-weighted
  --  summability is DERIVED there — the census is a Finset of
  --  Box(q₀, entLvl) at the FIXED defining level, so it is uniformly
  --  bounded by |Box(q₀, entLvl)| = q₀^{n·entLvl} per template (box_card),
  --  and comparison against q₀^{n·entLvl}·(weight sum) closes it from
  --  Gent_hasSum. No EntMassSummable def exists any more.)

-- [`EntMassSummable` IS STRUCK at REV 7 (Codex6-C7): the note's ENT-AGG
--  ledger line grants convergence "GIVEN XHD-s on the shallow layer"
--  ALONE (MOVES 8124–8133) — a separate named summability burden was a
--  silent strengthening of the per-clause hypothesis package. V3-8a now
--  takes `XHDsEnt` itself and DERIVES the count-weighted summability
--  (census ≤ |Box(q₀, entLvl)| uniformly per template — see the XHDsEnt
--  note above). No consumer of the name remains.]

/-- (XHD-d) ENTRANCE FACE: exactness of the LISTED H(ε̊) against concrete-ε
realizability (V3-5's hypothesis; `Realizable` DISPLAYED — C29), PLUS the
REV-3 landing law (Codex-6's second horn: rev 2's no_orphanE concluded only
domain membership, so a realizable entrance could be excluded from EntIx and
V3-8 could omit genuine entrances). Owner [2b]. -/
def Realizable {n C S} (V : CtsMeasured n C S) (ε : EntShapeV n)
    (β₀ : S.Cell) : Prop :=
  ∀ q₀ ∈ V.Pools, ∃ N₀, ∀ N ≥ N₀, (V.entEvt ε β₀ q₀ N).Nonempty
  -- [REV 4, Codex-15: declared BEFORE its consumer XHDdEnt. NOTE the
  --  symmetry with the new template-side `TReal` — the entrance face was
  --  ALREADY process-keyed (event realization, not a count recursion);
  --  the N-1 re-key makes the template face match it.]

structure XHDdEnt (n : ℕ) (S : StepSys n) {C : CtsFamily n}
    (V : CtsMeasured n C S) where
  -- (REV 7, C11: the laws read `instRealizable` — the ∃-over-Option
  --  wrapper; at a `none` instantiation no_orphanE/lands_of_realizable
  --  are vacuous and no_strayE demands nothing, all DEAD branches by
  --  V3-3d's totality at consumption)
  no_orphanE : ∀ (ε̊ : EntTemplate n) (h : Hpt ε̊.entDim) (β₀ : S.Cell),
    V.instRealizable ε̊ h β₀ → (V.entDom ε̊).Mem h
  no_strayE : ∀ (ε̊ : EntTemplate n) (h : Hpt ε̊.entDim) (β₀ : S.Cell),
    V.entLands ε̊ β₀ → (V.entDom ε̊).Mem h → V.instRealizable ε̊ h β₀
  lands_of_realizable : ∀ (ε̊ : EntTemplate n) (h : Hpt ε̊.entDim) (β₀ : S.Cell),
    V.instRealizable ε̊ h β₀ → V.entLands ε̊ β₀
    -- [REV 3: no realizable entrance falls outside the EntIx carrier]

/-- the per-instantiation ℝ-valued entrance mass — A DEF, RE-KEYED at REV 3
(F-1, THE q-POWER SLIP: rev 2's body read the BOX-EVENT card, which is
I^ent·q^{n·entLvl−A}, so the def computed ι·q^{n·entLvl−A}, not ι — refuted
by the blueprint's own gate numbers). The census carrier is the fix:
ιshH(ε̊, h, β₀) := I^ent(ε̊[h])(q₀) · q₀^{−A(ε̊[h])}, I^ent := the ε-INSTANCE
CENSUS (V.entCensus — the D4R.4 marked-prefix count, NOT an event card).
GATE CHECK (F-1's acceptance): q₀ = 2, A = 3, entLvl = 3 —
ιshH = 2·2⁻³ = 1/4; ιshH·|Box(3)| = (1/4)·512 = 128 = card(entEvt at 3)
per `ent_card` (128, never 8192): `LedgerIV.init_count` is TRUE at the
intended instance. -/
noncomputable def ιshH {n C S} (V : CtsMeasured n C S) (ε̊ : EntTemplate n)
    (h : Hpt ε̊.entDim) (β₀ : S.Cell) (q₀ : ℚ) : ℝ :=
  (V.instCensus ε̊ h β₀ q₀ : ℝ)
    * (q₀ : ℝ) ^ (-((instA ε̊ h : ℕ) : ℤ))
  -- (REV 7, C11: the census/exponent wrappers — same values on the
  --  totality range, i.e. everywhere at consumption)

/-- THE XHD PACKAGE (V.0), one record — DECLARED AFTER ITS COMPONENTS (C4):
w + u + d (template, CELL — new at REV 3 — and entrance faces) + s (template,
cell, entrance faces) + the entrance exactness. [1v]-FULL is V1-5's
`IsFullDischarge`; until it is instantiated every measured unit takes the
package (or the exact sub-package its V.1 ledger line names) as an explicit
argument — the tag displayed at its site. -/
structure XHD (n : ℕ) (S : StepSys n) (TE : TmplEvents n S)
    {C : CtsFamily n} (V : CtsMeasured n C S) where
  w : XHDw n S
  u : XHDu n S
  d : XHDd n S TE            -- [REV 4: exactness process-keyed — N-1]
  dC : XHDdC n S V           -- [REV 3: the cell d-face — F-3]
  s : XHDs n S w d
  sC : XHDsC n S w d V s
  sEnt : XHDsEnt n S V
  dEnt : XHDdEnt n S V

/-- (v) HMC — THE OPEN KERNEL, the TYPED LINK between the process side and
the table side (the N-1 adjudication). The note's display (MOVES 8198–8204),
quoted: "**(v) HMC — height-domain Markov compatibility. OPEN KERNEL,
displayed hypothesis.** For every template γ, the whole-template exact
domain FACTORS stepwise: H(γ) = ∏_i H(γ¹_i), γ¹_i := (β_{i−1} →^{m_i,o_i}
β_i), each factor depending ONLY on the retained state β_{i−1} and the step
data — never on earlier height choices — so Σ_{h ∈ H(γ)} ∏ g_i(h_i) =
∏_i G^{β_{i−1},β_i}_{m_i,o_i}." Stated as membership-factorization of the
LISTED presentation of the process-side domain; templates INCLUDE
terminal-final ones (`Template` constructors — the rev-4 note signature is
BY TYPE). UNDERIVABILITY RESTORED (the rev-3 defect): with XHDd exact
against the mark census `Tgam` (REV 7, C6) and the composite
`tevt`/`tinst` free, the four-line proof
is blocked in BOTH directions at composite tails — no census recursion, no
chainCount→census link. (The ⊆-flavored fragment at length-2 composites
whose TAIL is a single step is derivable GIVEN the mark facts +
tevt_last_iff — recorded at V4-11; the note's open content, the ⊇ direction
and state-only dependence, is untouched. The false-HMC toy V4-11 couples
exactly ⊇.) NEVER proved in this corpus; consumed by (COMP-Σ)/V5-5 and
V4-12(a). -/
def HMC {n : ℕ} {S : StepSys n} (TE : TmplEvents n S) (D : XHDd n S TE) : Prop :=
  ∀ {α β} (m : S.Move α β) (γ : Template n S β) (h₁ : Hpt (S.dim m))
    (h₂ : Hpt γ.D),
    (D.dom (.cons m γ)).Mem (Hpt.append h₁ h₂) ↔
      (D.dom (.last m)).Mem h₁ ∧ (D.dom γ).Mem h₂

/-- the three ▸-transport helpers (REV 5, Codex-15: DISPLAYED closed defs,
no longer "one line each at E-phase" — mechanical Eq-recursion wrappers,
zero design content). -/
def castMove {n} {S : StepSys n} {α α' β β' : S.Cell}
    (hα : α = α') (hβ : β = β') (m : S.Move α β) : S.Move α' β' :=
  hα ▸ hβ ▸ m
def castHpt {D D' : ℕ} (h : D = D') (x : Hpt D) : Hpt D' := h ▸ x
def castAssign {n} {S : StepSys n} {α α' β β' : S.Cell}
    (hα : α = α') (hβ : β = β') {m : S.Move α β} {q₀}
    {x : S.Hist q₀ α} {h : Hpt (S.dim m)} (a : S.Assign m x h) :
    S.Assign (castMove hα hβ m) (hα ▸ x) (by cases hα; cases hβ; exact h) := by
  cases hα; cases hβ; exact a
def castMoveT {n} {S : StepSys n} {α α' : S.Cell} {v : VLabel n}
    (hα : α = α') (m : S.MoveT α v) : S.MoveT α' v := hα ▸ m
  -- [REV 6, Codex5-28: displayed — no longer §2.J's residual one-line
  --  token; the absorbing label v does not transport (VLabel is
  --  refinement-invariant)]

/-- (HMC-AUG)'s refinement carrier — FULLY TYPED at REV 3 (Codex-13: the
rev-2 count_proj was an inequality with a loose ∃m and count_cover was
schematic, so an UNRELATED HMC-satisfying system could witness the
existential). Now: moves PROJECT (moveProj, dimension-preserving), heights
identify along dim_eq, assignments EMBED (assignOf, mass-preserving), and
the refined assignments over each coarse move PARTITION its fiber
(assign_cover, a displayed Σ-bijection) — so S' is keyed to S move-by-move,
height-by-height, count-by-count; count_proj/count_cover are now LEMMAS
(cards of a partitioned Σ-type), not fields. "One round of 𝒞_n refinement
by finitely-valued boundary/gap data"; never assumed in this corpus
(ledgered V.5(2)). -/
structure Refinement (n : ℕ) (S : StepSys n) where
  B : S.Cell → Type                       -- the finitely-valued refinement data
  finB : ∀ α, Fintype (B α)
  S' : StepSys n
  cellEq : S'.Cell ≃ Σ α : S.Cell, B α    -- refined cells fiber over 𝒞_n
  histOf : ∀ (α' : S'.Cell) {q₀}, S'.Hist q₀ α' → S.Hist q₀ (cellEq α').1
    -- [REV 4: pools ride histories on both sides — same-pool projection]
  moveProj : ∀ {α' β'}, S'.Move α' β' → S.Move (cellEq α').1 (cellEq β').1
  dim_eq : ∀ {α' β'} (m' : S'.Move α' β'), S'.dim m' = S.dim (moveProj m')
  assignOf : ∀ {α' β'} (m' : S'.Move α' β') {q₀} (x' : S'.Hist q₀ α')
    (h : Hpt (S'.dim m')),
    S'.Assign m' x' h → S.Assign (moveProj m') (histOf α' x') (dim_eq m' ▸ h)
  mass_eq : ∀ {α' β'} (m' : S'.Move α' β') {q₀} (x' : S'.Hist q₀ α') (h) (a'),
    S'.massOf m' x' h a'
      = S.massOf (moveProj m') (histOf α' x') (dim_eq m' ▸ h) (assignOf m' x' h a')
  assign_cover : ∀ {α β} (m : S.Move α β) (α' : S'.Cell)
    (hα : (cellEq α').1 = α) {q₀} (x' : S'.Hist q₀ α') (h : Hpt (S.dim m)),
    Function.Bijective
      (fun p : Σ (β' : {β' : S'.Cell // (cellEq β').1 = β})
          (m' : {m' : S'.Move α' β'.1 // castMove hα β'.2 (moveProj m') = m}),
          S'.Assign m'.1 x' (castHpt m'.2 (dim_eq m'.1) h) =>
        castAssign hα β'.2 (assignOf p.2.1.1 x' _ p.2.2))
    -- the refined assignments over (α', x') PARTITION the coarse fiber
    -- S.Assign m (histOf α' x') h. `castMove`/`castHpt`/`castAssign` are
    -- the three ▸-transport helpers along hα/β'.2/dim_eq — DISPLAYED
    -- closed defs above (REV 5, Codex-15); the Σ-domain and the target
    -- fiber are otherwise verbatim as shown.
  -- terminal twins [+T], WRITTEN OUT at REV 6 (Codex5-28; targets: the
  -- SAME absorbing label v on both sides — VLabel does not refine):
  moveProjT : ∀ {α'} {v : VLabel n}, S'.MoveT α' v → S.MoveT (cellEq α').1 v
  dimT_eq : ∀ {α' v} (m' : S'.MoveT α' v), S'.dimT m' = S.dimT (moveProjT m')
  assignOfT : ∀ {α' v} (m' : S'.MoveT α' v) {q₀} (x' : S'.Hist q₀ α')
    (h : Hpt (S'.dimT m')),
    S'.AssignT m' x' h
      → S.AssignT (moveProjT m') (histOf α' x') (dimT_eq m' ▸ h)
  massT_eq : ∀ {α' v} (m' : S'.MoveT α' v) {q₀} (x' : S'.Hist q₀ α') (h) (a'),
    S'.massOfT m' x' h a'
      = S.massOfT (moveProjT m') (histOf α' x') (dimT_eq m' ▸ h)
          (assignOfT m' x' h a')
  assign_coverT : ∀ {α v} (m : S.MoveT α v) (α' : S'.Cell)
    (hα : (cellEq α').1 = α) {q₀} (x' : S'.Hist q₀ α') (h : Hpt (S.dimT m)),
    Function.Bijective
      (fun p : Σ (m' : {m' : S'.MoveT α' v // castMoveT hα (moveProjT m') = m}),
          S'.AssignT m'.1 x' (castHpt (m'.2 ▸ dimT_eq m'.1) h) =>
        (hα ▸ (assignOfT p.1.1 x' _ p.2) : S.AssignT m (histOf α' x') h))
    -- (the ▸-transports along hα/m'.2/dimT_eq mirror assign_cover's
    --  castMove/castHpt/castAssign wrappers; no target-cell Σ layer —
    --  the absorbing label is fixed)

/-- the refined-template roster over a coarse template: every template of
the refined system from the refined source cell α' whose stepwise
`moveProj`/`moveProjT` image is γ, LISTED (finitely many refined cells and
moves per step — `finC`/`finM`/`finMT`), each with its height-dimension
identity (dims agree stepwise by `dim_eq`/`dimT_eq`). Closed def, REV 5
(M-2's carrier); `open Classical in` supplies the match decidabilities
(noncomputable is licit — the consumers are Props). -/
open Classical in
noncomputable def refTmpls {n} {S : StepSys n} (R : Refinement n S) :
    ∀ (α' : R.S'.Cell) {α}, (R.cellEq α').1 = α →
    ∀ γ : Template n S α, List (Σ' γ' : Template n R.S' α', γ'.D = γ.D)
  | α', _, hα, .last m =>
      (Finset.univ (α := Σ β', R.S'.Move α' β')).toList.filterMap fun p =>
        if h : ∃ hβ : (R.cellEq p.1).1 = _,
            castMove hα hβ (R.moveProj p.2) = m
        then some ⟨.last p.2, by rw [R.dim_eq]; cases h.choose; rfl⟩
        else none
  | α', _, hα, .lastT m =>
      (Finset.univ (α := R.S'.MoveT α' _)).toList.filterMap fun m' =>
        if h : castMoveT hα (R.moveProjT m') = m    -- VLabel does not refine:
        then some ⟨.lastT m', by rw [R.dimT_eq]; cases hα; rfl⟩  -- same v
        else none
  | α', _, hα, .cons m γ =>
      ((Finset.univ (α := Σ β', R.S'.Move α' β')).toList.filterMap fun p =>
        if h : ∃ hβ : (R.cellEq p.1).1 = _,
            castMove hα hβ (R.moveProj p.2) = m
        then some (p, h.choose) else none).flatMap fun ph =>
          (refTmpls R ph.1.1 ph.2 γ).map fun q =>
            ⟨.cons ph.1.2 q.1, by
              simp [Template.D, q.2, R.dim_eq]; cases ph.2; rfl⟩
  -- (castMoveT: the displayed ▸-wrapper above — REV 6, Codex5-28; the
  --  proof terms are the stepwise dim_eq/dimT_eq rewrites — E-phase may
  --  restate them as `by omega`-free Eq.trans chains; zero design content.)

/-- THE REFINED-EVENT TRANSPORT (NEW at REV 5 — Fable M-2's repair, the
round-3 N-1 residue): the refined process's marked events, PINNED to the
ledger's own event carrier. The note's display (MOVES 8213–8220), quoted:
"(HMC-AUG) — a SEPARATE named redesign hypothesis, NOT a consequence of
HMC (rev 2, finding 12; ledgered V.5): if a global cone inequality couples
successive steps, ONE round of 𝒞_n refinement by finitely-valued
boundary/gap data restores the factorization; finite-memory repair need
not be possible at all — a second surviving coupling is R2's wall
channel." A refinement RE-PARTITIONS the base process's marked events by
the boundary/gap reading — it does not mint free composite events. Rev 4's
∃-bound `TE'` was FREE data, and the identity-refinement/cooked-events
construction (Fable M-2, quoted in the audit: B α := PUnit, tevt' :=
if-membership-then-univ-else-∅ over PUnit boxes, product-partition
domains) derived HMCAug from any XHD d-face — the "unrelated witness stays
impossible" comment was FALSE. The two tie fields below kill it: `boxEq`
kills the PUnit box (the refined process lives over the SAME p-adic
residue boxes), and `tevt_cover` forces the refined events to re-partition
the base event — at the identity refinement it forces TE' = TE outright,
so the cooked witness would have to prove HMC TE D itself. -/
structure RefEvents {n : ℕ} {S : StepSys n} (R : Refinement n S)
    (TE : TmplEvents n S) where
  TE' : TmplEvents n R.S'              -- carries its OWN four [tie] fields
  boxEq : ∀ q₀ N, TE'.Box q₀ N ≃ TE.Box q₀ N
  tevt_cover : ∀ (α' : R.S'.Cell) {q₀} (x' : R.S'.Hist q₀ α')
    (γ : Template n S (R.cellEq α').1) (h : Hpt γ.D) (N : ℕ),
    q₀ ∈ S.Pools →
    TE.tevt γ (R.histOf α' x') h N
      = ((refTmpls R α' rfl γ).map (fun p =>
          (TE'.tevt p.1 x' (castHpt p.2.symm h) N).image (boxEq q₀ N))
        ).foldr (· ∪ ·) ∅
    -- the base marked event IS the union of its refined re-partition
    -- (heights transported along the roster's own dim identity, castHpt)
  tinst_cover : ∀ (α' : R.S'.Cell) {q₀} (x' : R.S'.Hist q₀ α')
    (γ : Template n S (R.cellEq α').1) (h : Hpt γ.D),
    q₀ ∈ S.Pools →
    (TE.tinst γ (R.histOf α' x') h (TE.tmplLvl γ)).card
      = ((refTmpls R α' rfl γ).map (fun p =>
          (TE'.tinst p.1 x' (castHpt p.2.symm h) (TE'.tmplLvl p.1)).card)
        ).sum
    -- the mark census re-partitions too (marks refine along the
    -- assign_cover chains — no mark is created or lost; a LIST sum, so
    -- distinct refined templates are counted per roster entry)

def HMCAug {n : ℕ} (S : StepSys n) (TE : TmplEvents n S) : Prop :=
  ∃ (R : Refinement n S) (RE : RefEvents R TE)
    (D' : XHDd n R.S' RE.TE'), HMC RE.TE' D'
  -- [REV 5, M-2: TE is a PARAMETER (the ledger's own event carrier), and
  --  the ∃-bound refined events are PINNED to it through RefEvents. The
  --  round-4 derivability audit is RE-RUN with the ties: the cooked
  --  identity-refinement witness dies at boxEq (PUnit boxes) and — with
  --  real boxes — at tevt_cover, which forces TE' = TE at the identity
  --  refinement (refTmpls reduces to the singleton roster there — one
  --  surviving (β', m') per step through the displayed filterMap; walked
  --  by the round-5 fresh audit, §A.2), reducing the witness to a proof
  --  of HMC TE D, i.e. of the open kernel itself; non-identity
  --  refinements must supply GENUINE boundary/gap data whose refined
  --  domains factor, exactly the note's hypothesis.]
  -- [THE SEPARATION RECORD — CORRECTED at REV 7 (C4, adjudicated;
  --  Codex's construction verified, overturning the rev-5/6 "¬HMCAug at
  --  the coupled toy for every refinement" and the Codex5-24 walk's
  --  ¬HMCAug half): at V4-11's coupled toy HMCAug is TRUE — refine the
  --  intermediate cell by WHETHER h₁ = 0 (B := Fin 2, finitely-valued
  --  boundary data); in the h₁ = 0 refined state the tail domain
  --  excludes h₂ = 0, in the h₁ ≠ 0 state it is full; `assign_cover`
  --  routes the first assignment by its reading and `tevt_cover`/
  --  `tinst_cover` reassemble the coarse events, and EACH refined
  --  composite domain FACTORS. (The old argument's error: tevt_cover
  --  forces refined events empty AT THE COUPLED POINT, but the refined
  --  DOMAINS may exclude that point per refined cell — no_stray does not
  --  fail.) So the toy is the SEPARATION WITNESS: ¬HMC ∧ HMCAug — one
  --  round of 𝒞_n refinement RESTORES the factorization, EXACTLY the
  --  note's HMC-AUG display (MOVES 8213–8221), and HMCAug is STRICTLY
  --  WEAKER than HMC. Its non-vacuity as an OPEN Prop: satisfiable
  --  (V4-11(iii)); its falsifiability UNWITNESSED and OPEN — the note's
  --  predicted falsifier is a SECOND surviving coupling ("R2's wall
  --  channel"), not constructed here; and NO ¬HMCAug claim survives
  --  anywhere in this corpus. Derivability-from-XHD-alone is likewise
  --  now UNCLAIMED either way (the former underivability witness was
  --  the false ¬HMCAug).]
  -- [THE HMC → HMCAug THEOREM — A REAL UNIT at REV 7 (G1): `V4-13
  --  hmcaug_of_hmc` (R := the identity refinement, RE := the transported
  --  TE with Equiv.refl boxes and the singleton-roster covers, D' := D —
  --  ~30 mechanical lines), UNAVOIDABLE for any faithful encoding: the
  --  note's hypothesis is a CONDITIONAL whose antecedent is EMPTY when
  --  HMC holds. The note's "NOT a consequence of HMC" lives at the
  --  LEDGER level (separate named line item, cited separately, assumed
  --  nowhere — V7-1), never as logical independence. Harmless while (v)
  --  is open: HMC is proved nowhere and HMCAug is consumed by nothing.
  --  Do NOT re-key the type: conditioning the ∃ on ¬HMC buys nothing
  --  and would entangle the Prop with the kernel's negation.]

/-- (ENT-U)'s affine-A face (M4a), DISPLAYED (C29): A(ε̊[h]) is affine in h
across instantiations of one template (dependent codomain — the rev-2 `_`
made explicit). -/
structure AffEnt (n : ℕ) where
  AE : ∀ ε̊ : EntTemplate n, AffineE ε̊.entDim
  A_eq : ∀ (ε̊ : EntTemplate n) (h : Hpt ε̊.entDim),
    instA ε̊ h = (AE ε̊).eval h    -- (REV 7, C11: the instA wrapper)

/-- (iv)-REP's per-species proviso, DISPLAYED (C29): "the species' evaluation
maps mention no observable outside the (a)/(b) generator list" — the letters'
evaluation maps factor through the generator meet. A PER-SPECIES CHECK
(table-build burden; executed at the gate blocks — V6-3b's (D2)-EMPTY). -/
def ObsCheck {n : ℕ} {s : Skeleton n} (B : BlockData n s) : Prop :=
  ∀ (m : B.Letter) (q₀ : ℚ) (x x' : B.Carrier q₀),
    (∀ g, (B.gen g).part q₀ x = (B.gen g).part q₀ x') →
    B.evalObs m q₀ x = B.evalObs m q₀ x'

/-- cofinite activity (V7-5 leg (c)'s premise carrier, DISPLAYED — C29):
at every state, only finitely many pools are inactive. -/
def CofinAct {n C S} (V : CtsMeasured n C S) : Prop :=
  ∀ c : S.Cell, {q₀ ∈ V.Pools | ¬ V.activeState q₀ c}.Finite
```

### 2.H The J tables ((J-RAT)/CL-18's carrier — the PLAN-SYNC deliverable) — REV 3: ROUTE-keyed (F-6)

```lean
/-- the (K-SUB) route classification of an outcome — the (m, c) row datum. -/
inductive RouteTag | kcol | split | term
  deriving DecidableEq

/-- THE J-CELL ROSTER — RE-KEYED at REV 3 (F-6, THE ROSTER BUG: rev 2 kept
only cells with ≥ 2 CONTINUING marks, but the note's bracket "[o branching :=
the (c ≥ 1, m ≥ 2) row of (K-SUB)'s (m, c) CLASSIFICATION]" classifies the
OUTCOME, not a sub-roster of its cells — and (K-SUB)'s arithmetic
Σ_β K + Σ b^term + Σ_o J_{τ,o} = 1 = PART-1's total over ALL cells forces
J_{τ,o} = the FULL cell mass of every split-route outcome. At n = 3 the rev-2
roster was EMPTY everywhere (V4-8's emult ≤ 1 census) while the note's J at
the root's m_2+1 outcome (m = 2, c = 1, T = q(q−1)) is nonzero.) J sums ALL
cells of a split-route outcome, EACH CELL ONCE — PART-1's partition index,
NEVER the marked per-continuing-branch T·G. -/
-- (Declaration order in the E-file: RouteTag → JCells → CellPolyPack → Jval
--  — Jval consumes the pack; displayed here in reading order.)
structure JCells (n : ℕ) (C : CtsFamily n) (S : StepSys n)
    (V : CtsMeasured n C S) where
  route : ∀ (s : Skeleton n) (m : (C.bd s).Letter), (C.bd s).Outc m → RouteTag
    -- the (K-SUB) classification datum; V7-3a carries the compatibility law
    -- `route_eq` tying it to MovesS's routeOf ∘ odata at the seam instance
  route_cont : ∀ (s) (m) (o : (C.bd s).Outc m),
    route s m o = .split → (C.bd s).cont m o
    -- [REV 5, Codex-10: split route = the (c ≥ 1, m ≥ 2) row, so a
    --  continuing member exists (`cont_iff`); V5-7b's OUTCOME-level
    --  supplier builds its datum from this law — no continuing-target
    --  choice enters the J stack]
  bcells : ∀ (s : Skeleton n) (m : (C.bd s).Letter) (o : C.Outc s m)
    (α : (C.bd s).CellIdx), Finset (V.DCellO s m o α)
  roster_tie : ∀ s m o α (c : V.DCellO s m o α),
    c ∈ bcells s m o α ↔ route s m o = .split
    -- ALL cells iff the outcome is split-route; ∅ otherwise. The rev-2
    -- emult ≥ 2 tie is STRUCK; emult stays V4-7's surplus datum only.

/-- J_{τ,o}(q₀) as a MEASURED value: Σ over ALL cells of the split-route
(τ, o), EACH ONCE, of the XHD-resummed conditional cell mass — REV 3: the
cell mass is count-polynomial × weight-sum (the [1v]×[2b] split; XHDsC is
weight-only, so no factor is dropped and none is squared):
μcellVal cp XsC c q₀ := (cp.P … c).eval q₀ · Σ_j evalAt (XsC.Gcell … c j).
The ℚ(q) membership — (J-RAT) — is unit V5-7b; its PolyGeom presentation
supplies `MovesS.RatBurdens.jP` AND — RE-KEYED at REV 7 (C15 = Fable
CRIT-2; W4-SYNC delta 3) — the PER-CELL fields the BUILT RatBurdens now
REQUIRES (`jPCell/jcell_ok/jcell_interp/jcell_sum`, built MovesS/Defs.lean
386–395): V5-7b's per-cell clause exhibits, per digit cell c of a
split-route outcome, the PolyGeom `jcellPG c` with countT := cp.P c,
countS := 1, geom := the Σ_j Gcell c j value — eval = μcellVal (which IS
`M.μcell` at the V7-4c instance, rep-quantified and split-guarded exactly
as `jcell_interp` demands) — and the SYMBOLIC cell-fiber sum
Σ_{c ∈ cells o} (jcellPG c).val = jP.val (`jcell_sum`). NO parallel type
is the deliverable: the tables target the EXISTING carrier `M.Cell`
(= Σ o, DCellO at V7-4a) through `dataOf`; V7-5a leg (b) maps them.
GATE (F-6's acceptance): at the root's
m_2+1 split outcome, Jval = T·G-mass of its one cell = q(q−1)-count mass
≠ 0 — the n = 3 roster is NONEMPTY and Jval is nonzero. -/
noncomputable def Jval {n C S} {V : CtsMeasured n C S} (J : JCells n C S V)
    (cp : CellPolyPack n C S V) (XsC : XHDsC n S _ _ V _)
    (d : MoveData n C) (q₀ : ℚ) : ℝ :=
  ∑ c ∈ J.bcells d.s d.m d.o d.α, μcellVal cp XsC d c q₀
-- μcellVal cp XsC d c q₀ :=
--   ((cp.P d.s d.m d.o d.α c).eval q₀ : ℝ)
--     * ∑ j, ((evalAt q₀ ⟨XsC.Gcell d c j, _⟩ : ℚ) : ℝ)
-- (+T twin JvalT over TermData/GcellT for terminal split bookkeeping rows.)

/-- the per-cell count-polynomial pack ((J-RAT)'s [1v] face) — CLOSED at
REV 3 (Codex-16/18: no `V.moveOf …` ellipses; CtsMeasured now HAS the domain
carriers). One polynomial per digit cell, degree ≤ W_loc, valued at the
cell-refined count ON THE LISTED CELL DOMAIN (domain-keyed, unguarded — it
says something wherever the domain does; cdom exactness is XHDdC's face).
ADJUDICATION (recorded): keying the valuation across the whole listed domain
bakes CELL-LEVEL height-constancy into this [1v] burden — that is the note's
OWN (J-RAT) split ("cell-level counts polynomial per the (iv)-POLY pattern"
= one polynomial per cell), unlike VAL(a), where the note explicitly assigns
height-uniformity to (XHD-u) and V2-4 therefore keys tbl_count to base
points. A burden may be strong when the note's burden is. -/
structure CellPolyPack (n : ℕ) (C : CtsFamily n) (S : StepSys n)
    (V : CtsMeasured n C S) where
  P : ∀ (s) (m) (o : (C.bd s).Outc m) (α), V.DCellO s m o α → Polynomial ℚ
  deg : ∀ s m o α c, (P s m o α c).natDegree ≤ C.Wloc s m
  count : ∀ (d : MoveData n C) (c : V.DCellO d.s d.m d.o d.α)
    {q₀} (x : S.Hist q₀ _) (hzc : S.zc x), q₀ ∈ V.Pools →
    ∀ h, (V.cdom d c).Mem h →
    ((P d.s d.m d.o d.α c).eval q₀ : ℚ) = V.cntc d x c h
  countT : ∀ {v} (d : TermData n C v) (c) {q₀} (x : S.Hist q₀ _)
    (hzc : S.zc x), q₀ ∈ V.Pools → ∀ h, (V.cdomT d c).Mem h →
    ((P d.s d.m d.o d.α c).eval q₀ : ℚ) = V.cntcT d x c h           -- [+T]
```
N-2 ACCEPTANCE at this layer (the round-3 refuter, now satisfiable): the A2
digit cell's polynomial (X−1)² evaluates 1 at q₀ = 2 and 4 at q₀ = 3, and
`cntc` at q₀ = 2 counts F₂-histories' fibers (1) while `cntc` at q₀ = 3
counts F₃-histories' (4) — two different fibers, no shared ℕ, the law holds
per pool. Same for `ValA.tbl_count`'s T21 = X(X−1): 2-vs-6 (V2-4's displayed
gate check).

### 2.I `DefsGate.lean` — the V.6 sealed data (concrete, decide-native) — REV 2: the A2 chart + the nine-point fields (C3, C20, C21)

Concrete data only (no laws): the root roster (five letters with their five
closed-form polynomials `TH3 = C(1/6)·X·(X−1)·(X−2)`, `TH12 = C(1/2)·X²·(X−1)`,
`TH3c = C(1/3)·(X³−X)`, `T21 = X·(X−1)`, `T3 = X`); the s_blk2 roster
(`Tsplit = C(1/2)·(X−1)·(X−2)`, `Tinert = C(1/2)·X·(X−1)`, `Tdbl = X−1`,
`Tw2 = X−1`, `Tvv = (X−1)²`); the gate-B constants (A(ε) = 3, W_ent = 3,
`Ient = X·(X−1)`, ι = 1/4, T = 1, g = 1/8, μ̂ = 1/32, shadow = 2, N₀ = 3);
the census q-list `censusQ := [2,3,4,5,7,8,9,11,13]` (ALL NINE, in-kernel —
C20 repair; `censusP` deleted); REV 5 (Codex-2): the gate letters'
OUTCOME-MEMBER ROSTERS as list literals — the `omem` data of the two gate
BlockDatas (root: e.g. the m_2+1 letter's {(2, δ, .inr s_blk2), (1, δ,
.inl (1,1))} — Σ sizes 3 ≤ e = 3; s_blk2: o_split {(1, δ, .inl (1,1)) ×2},
o_inert {(2, δ, .inl (1,2))}, o_double {(2, δ, .inr s_dbl)} — Σ ≤ e = 2
per outcome; the V.6.1/V.6.3 rosters, transcribed at E-phase from the
note's displayed outcome tables, checked by V2-9's decide).

**The A2 entry, note-faithfully reparameterized (C3 — THE ARITHMETIC CATCH):**
```lean
/-- the (t,u) chart: t = h₂ ≥ 1, u ≥ 0; chart (t,u) = (h₀, h₂) =
(3t + 2u + 1, t). A DEFINITION — the coordinate change itself. -/
def A2chart (h : Hpt 2) : Hpt 2 := ![3 * h 0 + 2 * h 1 + 1, h 0]

/-- the A2 height domain IN (t,u) COORDINATES: L((1,0); {(1,0),(0,1)})
(t ≥ 1, u ≥ 0 — one linear set; the (h₀,h₂)-image is V6-2a's lemma). -/
def A2dom : LinSet 2 := ⟨![1, 0], [![1, 0], ![0, 1]]⟩

/-- the A2 weight IN (t,u) COORDINATES — coefficients NATURAL: const 1,
coeff (6, 3), i.e. E = 6t + 3u + 1. ATTRIBUTION (REV 3, G-1): this (t,u)
form is OURS, derived; the note displays E = (3(h₀+h₂)−1)/2 and the domain
substitution "h₂ = t ≥ 1, h₀ = 3t + 2u + 1" (MOVES 8844) — the string
"6t+3u+1" appears nowhere in the frozen note. Both round-2 auditors
re-derived it independently (3(4t+2u+1)−1 = 2(6t+3u+1) ✓). The (h₀,h₂)
display is RE-DERIVED through A2chart as the division-free identity
2·E = 3(h₀+h₂) − 1 (V6-2b). -/
def EA2 : AffineE 2 := ⟨1, ![6, 3], by decide⟩

def TA2 : Polynomial ℚ := (Polynomial.X - 1) ^ 2
```
Sealed census height point: (h₀,h₂) = (4,1) = A2chart ![1,0], E = EA2.eval
![1,0] = 7 ✓ (the seal's value).

**The three prime-power fields (C20 repair; tables DISPLAYED at REV 3 —
Codex-18; provenance corrected — G-2):** explicit table-based instances over
`Fin` carriers, laws discharged by `decide`:
```lean
def F4 : Type := Fin 4          -- 0,1,x,x+1 over F₂[x]/(x²+x+1)
def f4mul : Fin 4 → Fin 4 → Fin 4 :=
  fun a b => (([[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]].get a).get b)
def f4add : Fin 4 → Fin 4 → Fin 4 :=
  fun a b => (([[0,1,2,3],[1,0,3,2],[2,3,0,1],[3,2,1,0]].get a).get b)
def f4inv : Fin 4 → Fin 4 := fun a => [0,1,3,2].get a
noncomputable instance : Field F4 where
  -- [REV 5, Codex-15: the FULL instance skeleton, no `..` — every data
  --  field explicit, every law field one `by decide` over the tables]
  add := f4add;  zero := (0 : Fin 4);  neg := id;  sub := f4add
  mul := f4mul;  one := (1 : Fin 4);   inv := f4inv
  div := fun a b => f4mul a (f4inv b)
  nsmul := nsmulRec;  zsmul := zsmulRec;  npow := npowRec;  zpow := zpowRec
  add_assoc := by decide;      zero_add := by decide
  add_zero := by decide;       add_comm := by decide
  neg_add_cancel := by decide; sub_eq_add_neg := by decide
  mul_assoc := by decide;      one_mul := by decide
  mul_one := by decide;        zero_mul := by decide
  mul_zero := by decide;       mul_comm := by decide
  left_distrib := by decide;   right_distrib := by decide
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_inv_cancel := by decide; inv_zero := by decide
  -- (ratCast/qsmul/nnratCast/nnqsmul: Mathlib DivisionRing fields WITH
  --  default values — omitted-by-default, not elided content; if the
  --  pinned Mathlib demands them explicitly each is its documented
  --  recursor default, one line, recorded)

-- F8 := Fin 8 over F₂[x]/(x³+x+1) (code b₂b₁b₀ ↦ 4b₂+2b₁+b₀) and
-- F9 := Fin 9 over F₃[x]/(x²+1) (code a+bx ↦ a+3b) — the tables PASTED
-- (REV 4, Codex-14; generated by carryless-mod-C₂,₃ / componentwise-mod-3
-- arithmetic, re-derivable in one line each):
def F8 : Type := Fin 8
def f8add : Fin 8 → Fin 8 → Fin 8 := fun a b => (([
  [0,1,2,3,4,5,6,7],[1,0,3,2,5,4,7,6],[2,3,0,1,6,7,4,5],[3,2,1,0,7,6,5,4],
  [4,5,6,7,0,1,2,3],[5,4,7,6,1,0,3,2],[6,7,4,5,2,3,0,1],[7,6,5,4,3,2,1,0]
  ].get a).get b)
def f8mul : Fin 8 → Fin 8 → Fin 8 := fun a b => (([
  [0,0,0,0,0,0,0,0],[0,1,2,3,4,5,6,7],[0,2,4,6,3,1,7,5],[0,3,6,5,7,4,1,2],
  [0,4,3,7,6,2,5,1],[0,5,1,4,2,7,3,6],[0,6,7,1,5,3,2,4],[0,7,5,2,1,6,4,3]
  ].get a).get b)
def F9 : Type := Fin 9
def f9add : Fin 9 → Fin 9 → Fin 9 := fun a b => (([
  [0,1,2,3,4,5,6,7,8],[1,2,0,4,5,3,7,8,6],[2,0,1,5,3,4,8,6,7],
  [3,4,5,6,7,8,0,1,2],[4,5,3,7,8,6,1,2,0],[5,3,4,8,6,7,2,0,1],
  [6,7,8,0,1,2,3,4,5],[7,8,6,1,2,0,4,5,3],[8,6,7,2,0,1,5,3,4]
  ].get a).get b)
def f9mul : Fin 9 → Fin 9 → Fin 9 := fun a b => (([
  [0,0,0,0,0,0,0,0,0],[0,1,2,3,4,5,6,7,8],[0,2,1,6,8,7,3,5,4],
  [0,3,6,2,5,8,1,4,7],[0,4,8,5,6,1,7,2,3],[0,5,7,8,1,3,4,6,2],
  [0,6,3,1,7,4,2,8,5],[0,7,5,4,2,6,8,3,1],[0,8,4,7,3,2,5,1,6]
  ].get a).get b)
-- THE F8/F9 INSTANCES, DISPLAYED (REV 5, Codex-15: "the F4 pattern
-- verbatim" was a comment, not a definition; the inverse/negation tables
-- are now literals — f8inv read off f8mul's rows, f9inv/f9neg the mod-3
-- componentwise tables):
def f8inv : Fin 8 → Fin 8 := fun a => [0,1,5,6,7,2,3,4].get a
noncomputable instance : Field F8 where
  add := f8add;  zero := (0 : Fin 8);  neg := id;  sub := f8add  -- char 2
  mul := f8mul;  one := (1 : Fin 8);   inv := f8inv
  div := fun a b => f8mul a (f8inv b)
  nsmul := nsmulRec;  zsmul := zsmulRec;  npow := npowRec;  zpow := zpowRec
  add_assoc := by decide;      zero_add := by decide
  add_zero := by decide;       add_comm := by decide
  neg_add_cancel := by decide; sub_eq_add_neg := by decide
  mul_assoc := by decide;      one_mul := by decide
  mul_one := by decide;        zero_mul := by decide
  mul_zero := by decide;       mul_comm := by decide
  left_distrib := by decide;   right_distrib := by decide
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_inv_cancel := by decide; inv_zero := by decide

def f9neg : Fin 9 → Fin 9 := fun a => [0,2,1,6,8,7,3,5,4].get a
def f9inv : Fin 9 → Fin 9 := fun a => [0,1,2,6,5,4,3,8,7].get a
noncomputable instance : Field F9 where
  add := f9add;  zero := (0 : Fin 9);  neg := f9neg
  sub := fun a b => f9add a (f9neg b)
  mul := f9mul;  one := (1 : Fin 9);   inv := f9inv
  div := fun a b => f9mul a (f9inv b)
  nsmul := nsmulRec;  zsmul := zsmulRec;  npow := npowRec;  zpow := zpowRec
  add_assoc := by decide;      zero_add := by decide
  add_zero := by decide;       add_comm := by decide
  neg_add_cancel := by decide; sub_eq_add_neg := by decide
  mul_assoc := by decide;      one_mul := by decide
  mul_one := by decide;        zero_mul := by decide
  mul_zero := by decide;       mul_comm := by decide
  left_distrib := by decide;   right_distrib := by decide
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_inv_cancel := by decide; inv_zero := by decide
-- (the ratCast-family default-field remark under F4 applies to all three)
```
PROVENANCE (G-2, corrected): x²+x+1 and x³+x+1 ARE the Conway polynomials
C_{2,2}/C_{2,3}; x²+1 over F₃ is NOT the Conway polynomial (C_{3,2} =
x²+2x+2) — it is simply AN irreducible (−1 a non-square mod 3), which is all
the census needs; the rev-2 "standard Conway-polynomial tables" claim is
struck. These make V6-1c/V6-3b decide-native at q = 4, 8, 9 — the census is
the note's NINE points in-kernel, and the char-2/char-3 finite-field behavior
(not polynomial interpolation) is what is checked, as the seal demands.

**`CoprimeLiftPack` — CLOSED at REV 3 (Codex-18: rev 2's `…`/`monic …`/
`reduce`/`hOf` were unspecified). It states EXACTLY unique coprime lifting +
coefficient determinacy, nothing stronger; determinacy of `hOf` is now BY
TYPE (it consumes only f mod 2^k):**
```lean
/-- reduction mod 2 of a mod-2^k polynomial (the one cast this pack uses). -/
def reduce2 (k : ℕ) (hk : 1 ≤ k) :
    Polynomial (ZMod (2 ^ k)) →+* Polynomial (ZMod 2) :=
  Polynomial.mapRingHom (ZMod.castHom (dvd_pow_self 2 (Nat.one_le_iff_ne_zero.mp hk)) (ZMod 2))

structure CoprimeLiftPack where
  hOf : ∀ (k : ℕ), Polynomial (ZMod (2 ^ k)) → Polynomial (ZMod (2 ^ k))
    -- the designated lifted factor; a FUNCTION of f mod 2^k BY TYPE —
    -- rev 2's separate `determined` field is subsumed (recorded)
  lift_unique : ∀ (k : ℕ) (hk : 1 ≤ k) (f : Polynomial (ZMod (2 ^ k)))
    (hf : f.Monic) (ū h̄ : Polynomial (ZMod 2)) (hcop : IsCoprime ū h̄)
    (hmh : h̄.Monic) (hfac : reduce2 k hk f = ū * h̄),
    ∃! uh : Polynomial (ZMod (2 ^ k)) × Polynomial (ZMod (2 ^ k)),
      uh.1 * uh.2 = f ∧ uh.2.Monic ∧
      reduce2 k hk uh.1 = ū ∧ reduce2 k hk uh.2 = h̄
  hOf_spec : ∀ (k : ℕ) (hk : 1 ≤ k) (f : Polynomial (ZMod (2 ^ k)))
    (hf : f.Monic) (ū h̄ : Polynomial (ZMod 2)) (hcop : IsCoprime ū h̄)
    (hmh : h̄.Monic) (hfac : reduce2 k hk f = ū * h̄),
    (∃ u, u * hOf k f = f) ∧ (hOf k f).Monic ∧ reduce2 k hk (hOf k f) = h̄
    -- hOf picks THE unique monic factor over h̄ whenever one exists
```
Mathlib-first (`Polynomial.hensel`-adjacent archaeology at E-phase); if the
exact form is missing it becomes a DECLARED published-axiom candidate per
campaign §4 — flag at E-phase, do NOT silently strengthen; it remains a typed
premise of V6-4c either way (never an unconditional Lean axiom).

### 2.J The no-placeholder checklist (C29/Codex-18 closure, REV 3)

Every carrier either round named as a placeholder now has a displayed CLOSED
home: `inv` DELETED (§2.B note) · `TargetIx` §2.C (inductive) ·
`MoveData`/`TermData` §2.C (structures; `src`/`tgt` defs — tcell-enforced) ·
`dataOf`/`dataOfT` (the inverses of `moveOf_bij`/`moveOfT_bij`, derived
noncomputable defs — one line each at V7-4a) · `HMCAug` §2.G (body +
`Refinement` fully typed: moveProj/dim_eq/assignOf/mass_eq/assign_cover;
`count_proj`/`count_cover` are now LEMMAS) · `XHDdSh` → `XHDdEnt` §2.G (+
`lands_of_realizable`) · `XHDdC` §2.G (new) · `AffEnt` §2.G (dependent
codomain explicit) · `CellPolyPack` §2.H (closed, domain-keyed, no
ellipses) · `ObsCheck` §2.G (over `BlockData.evalObs`) · `CofinAct` §2.G ·
`moveOf`/`moveOfT` §2.F (fields + bijection laws, targets enforced) ·
`Realizable` §2.G · `CtsmConclusions` V7-2a (a CLOSED structure declaration,
one `*_Stmt`-typed field per deliverable) · `EligPair`/`IsBranchingRead`/
`branchMenuCard` §2.D (closed defs keyed to NAMED MovesD declarations:
`ShapeRead.len`/`.mbar`, `E5_gmuLe`, `eligible_card_le`, `selRank`,
`E8_rankInj`) · `writeHeights` §2.D (displayed fold via `readOfLetter`;
slots/zig/gamTie encoding pinned) · `Hpt.take/drop/append` §2.A (closed
defs) · `IsPP` §2.A · `CoprimeLiftPack` §2.I (closed; `reduce2` displayed;
determinacy BY TYPE) · `F4/F8/F9` §2.I (tables displayed; Conway claim
corrected) · `emult` §2.F (a CtsMeasured FIELD — rev 2 called it a def over
data the carrier did not have) · `AStep`/`evtOfStep` §2.F (closed Σ-carrier
defs) · `zig` §2.D (Mathlib's `Denumerable.eqv ℤ`) · `StageLawBurden` V7-3d ·
`Wsh17PackageV` V7-7 (a displayed TYPE — REV 4: full frozen roster,
parameterized owner legs). REV-4 ADDITIONS, each displayed closed:
`TmplEvents`/`TReal` §2.G (the process side; four [tie] fields, no
composite law BY DESIGN — inventory slot 9) · `MDomTie` §2.G ·
`MarkDisj` §2.F · `gProd` §2.G (recursion displayed — the last `…` body
is out) · `cellEvtT`/`cntcT` §2.F (twins displayed, no longer comments) ·
`hentCode` §2.D (REV 5: length-seeded) ·
`BlockData.CellIdx` §2.C (moved into Defs — order fixed; V2-2's duplicate
declaration DELETED at REV 5, Codex-16) · the F8/F9 add/mul tables §2.I
(pasted literals) · `stepKey` §2.F (REV 5: minimized; REV 6, Codex5-21:
re-landed in the `CellOf` carrier — the REV-6 block below governs). REV-5 ADDITIONS, each displayed closed: `skBlk`/`OMember` §2.C (the
member roster's carrier) · `MoveData.tix`/`TermData.tix` §2.C (the M-1
binding objects) · `tcellM` §2.C (per-member landing maps) ·
`branchingRead` §2.D (Codex-15 — closed def, decide-filtered) ·
`MarkDisjT` §2.F (the Codex-5 twin) · `EntMassSummable` §2.G (the named
burden replacing the struck XHDsEnt field) ·
`castMove`/`castHpt`/
`castAssign` §2.G (displayed ▸-wrappers) · `refTmpls`/`RefEvents` §2.G
(the M-2 event transport) · `f4inv`/`f8inv`/`f9neg`/`f9inv` + the three
FULL `Field` instances §2.I (no `..`) · the 24 `*_Stmt` bodies (V7-2a) ·
`XHDFrame`/`XhdW_Stmt`-family/`xrbPackageOf`/`frameOf` (V7-7, the
Codex-11 adapter).
REV-6 ADDITIONS AND STRIKES, each displayed closed: `omem_sel` §2.C (the
Codex5-22 selected-member field; `omem_kcol` now its DERIVED length-1
corollary, displayed) · `SelMatches` + its `bIdx`/`nodeAt` helpers §2.D
(the Codex5-23 re-target; rev 5's `SelRankTie` STRUCK together with
`takenGm`/`eligMenu`/`shapeRank` — no shape-level (g, μ) enumeration
survives) · `CellOf`/`stepKey` §2.F (the key lands in the frozen-Cell-
shaped Σ-carrier — Codex5-21) · `pairSlots`/`depthSlots`/`expandRuns`/
`shapeOfSlots` §2.D (the writeHeights slot projections, closed —
Codex5-28) · `castMoveT` §2.G (displayed; no longer a residual token) ·
Refinement's five [+T] twin fields §2.G (written out — Codex5-28) ·
`gProdF` V7-7 (the frame-keyed weight product for `XhdS_Stmt`) · the
V7-4a `cellEvt` DIMENSION dite (Fable G-B; slot 15).
REV-7 ADDITIONS AND STRIKES, each displayed closed: `Tgam` §2.G (C6 —
the note's T_γ as the mark-census direct count; `TReal` demoted derived)
· `marks_realize` §2.G (the third mark [tie]) · `CtsCells` + the REAL
defs `AStep`/`CellOf`/`stepKey`/`evtOfStep` §2.F (C10 — the rev-6
comment-defs are OUT; `CtsMeasured extends CtsCells`) ·
`evt_disj_assign`(+T) §2.F (C8 carrier [tie]s; the `MarkDisj`/`MarkDisjT`
HYPOTHESIS defs STRUCK — the names survive as V4-10's derived lemmas) ·
`EntranceCut.lands_sel` §2.E + `CtsMeasured.ent_sel` §2.F (C1) ·
`IsBranchSlot`/`RealizedBranching` §2.D (C2; `IsBranchingRead` renamed —
the upper-bound key no longer claims branching) · `branchingRead?`/
`branchMenuCard`/`bIdx` §2.D (GAP-4 — Option-indexed, no Inhabited junk)
· `readOfLetter?`/`ReadFits`/`shapeOfSlots?`/`writeHeights?`/
`EntShapeV.template?` §2.D + the total wrappers `instA`/`instHentCode`
(§2.D)/`instCensus`/`instRealizable` (§2.F) (C11 — no forward reference;
totality = V3-3b/V3-3d theorems) · `EntMassSummable` STRUCK §2.G (C7) ·
`tcellM_sel` §2.C (C3 — the ∀-form `tcellM_tgt` struck) · `jcellPG` +
the per-cell (J-RAT) clause §2.H/V5-7b (C15) · `Tgam`-keyed `XHDd` §2.G.
Residual E-phase freedom: zig's orientation token, `skBlk`'s MovesSp
projection pointer (slot 13), the Mathlib ratCast-family default fields,
and `ReadFits`'s clause tuple (the Defs-layer deliverable inheriting
V3-3d's old body duty — its clause LIST is displayed at §2.D; REV 7,
C11) — mechanical or Defs-assigned, zero unrecorded design content,
each in §5's inventory.

## §3 The unit DAG — 98 units (32 easy / 62 medium / 4 hard)

Format per campaign §2: id `MovesV.<name>` · file · statement (against §2
Defs) · moves_ref (V-TABLES display, ≤ 3 lines) · deps · sketch · difficulty ·
hypothesis_fields (which open kernels ride — NEVER silently strengthened or
dropped). FORMAT AMENDMENT (C28 repair): a unit is ONE FILE with an
ENUMERATED LEMMA ROSTER (≤ 4 lemmas; each lemma one display); units whose
rev-1 spec concealed several declarations now display their rosters (V0-2,
V2-1, V2-2, V6-4a). Pre-approved splits are marked ⌿.

### Layer V0 — height apparatus [4]

**V0-1 `affine_pos` · `V0_affine.lean` · easy.**
`theorem affine_strictMono {D} (E : AffineE D) (h : Hpt D) (i : Fin D) :
StrictMono (fun t => E.eval (Function.update h i t))` + `theorem
affine_ge_const (E : AffineE D) (h : Hpt D) : E.const ≤ E.eval h` (h now
BOUND — A-7 repair). moves_ref: "E affine in h with positive weights" (XHD-w).
deps: Defs. sketch: sum manipulation; `Finset.sum_le_sum`. hyp_fields: none.

**V0-2 `linset_mem_iff` · `V0_linset.lean` · easy.**
ROSTER (3 — C28): (a) `linset_mem_iff` normal-form membership; (b)
`linset_base_mem : L.Mem L.base` (c := 0); (c) `linset_add_period` closure
under adding one period. moves_ref: "L(h₀; P) := {h₀ + Σ n_v·v}".
deps: Defs. sketch: definitional; `Fin.sum` lemmas. hyp_fields: none.

**V0-3 `semilin_sum_exact` · `V0_partition.lean` · medium.**
For `S : SemilinPart D`, `f : Hpt D → ℝ` with `0 ≤ f`, and per-component
`HasSum (f ∘ incl_j) (v j)`: `HasSum (f ∘ incl_{S.Mem}) (Σ_j v j)`.
moves_ref: "the finitely many component sums ADD EXACTLY to the H(γ)-sum —
no overlap terms exist (rev 3)". deps: V0-2.
sketch: induction on comps; `HasSum` over a disjoint union of subtypes
(`hasSum_subtype_iff` + disjointness field); nonneg gives summability
transfer. hyp_fields: none (the disjointness is a TYPE field of SemilinPart).

**V0-4 `xhds_instance_A2` · `V0_xhds_witness.lean` · medium ⌿ — RE-KEYED (C3).**
THE NON-DEGENERACY WITNESS for the XHD-s format (doctrine: packages must be
non-degenerately instantiable), now stated IN THE (t,u) CHART where `EA2`
lives: `HasSum (fun h : {h // A2dom.Mem h} => (q₀:ℝ)^(-(EA2.eval h.1 : ℤ)))
((evalAt q₀ ⟨GA2, _⟩ : ℚ) : ℝ)` for every prime power q₀ > 1, where
`GA2 : Qq` = the cleared form `X²/((X⁶−1)(X³−1))` — denominators in the
PolyGeom class. Base value: EA2.eval ![1,0] = 7 (the seal's E at (4,1)).
moves_ref: "HEIGHT DOMAIN … the ONE linear set L((4,1); {(3,1), (2,0)}) …
E = (3(h₀+h₂)−1)/2 — affine, positive weights" + "h₂ = t ≥ 1, h₀ = 3t+2u+1"
(V.6.2; the (t,u) form E = 6t+3u+1 is OUR derivation — G-1: never spliced
into the quotation again).
deps: V0-2, DefsGate (EA2/A2dom are (t,u)-native, so no V6 dependency — the
V0 layer stays before V6 in the build order; the (h₀,h₂) display is
V6-2a/b's downstream theorem). sketch: E = 6t+3u+1 over
t = 1+a, u = b: q^{−7}·Σ q^{−6a}·Σ q^{−3b}; product of two geometric series
(`tsum_geometric_of_lt_one`, `HasSum.mul`); match the cleared rational form
at eval. ⌿ split: (a) the double geometric sum; (b) the Qq clearing identity.
hyp_fields: none — a PROVED instance. [No half-integral arithmetic exists
anywhere in this unit: the (h₀,h₂) display is V6-2a/b's chart theorem.]

### Layer V1 — the XHD packages + (U-A) [10]

**V1-1 `xhdw_range` · `V1_xhdw.lean` · easy.**
`theorem xhdw_pos (X : XHDw n S) … : 0 < X.g m h q₀` and `X.g m h q₀ ≤ 1`
at pools (q₀ > 1, E ≥ const… state `0 <` and `≤ q₀^(−E.const)`).
moves_ref: "a FIXED-HEIGHT weight monomial g = q^{−E(h)}".
deps: Defs, V0-1. sketch: `zpow` monotonicity. hyp_fields: consumes XHDw as
an ARGUMENT (owner [2b]); proves only its numeric range.

**V1-2 `xhdu_rect_sum` · `V1_xhdu.lean` · easy.**
ROSTER (2): (a) GIVEN (u-T)'s constant count:
`∑ h ∈ Hfin, (cnt h : ℝ) * g h = (T:ℝ) * ∑ h ∈ Hfin, g h` when
`∀ h ∈ Hfin, cnt h = T`; (b) `xhdu_rect_false`, the "else false in general"
witness: a concrete `cnt` non-constant on a two-point H with
`Σ cnt·g ≠ cnt(h₀)·Σ g` (norm_num instance).
moves_ref: "Σ_h T(h)·g(h) = T·Σ_h g(h) is EXACTLY (u-T), else false in
general" ((iv) STEP). deps: Defs. sketch: `Finset.sum_congr` + `mul_sum`;
norm_num. hyp_fields: none (the premise is the (u-T) instance, explicit).

**V1-3 `xhdd_exact_supp` · `V1_xhdd.lean` · easy — RE-KEYED at REV 7 (C6:
XHDd is now keyed to the note's own T_γ = `Tgam`; the REV-4 TReal keying
had substituted event realization for the note's count).**
ROSTER (3): (a) `xhdd_exact : (D.dom γ).Mem h ↔ ∀ q₀ ∈ Pools,
∀ x : Hist q₀ α, zc x → 0 < Tgam TE γ x h` at pool-inhabited zc histories
(both directions from no_orphan/no_stray + zc_ne) — the exactness iff at
the note's own object; (b) `mem_chainCount_pos : (D.dom γ).Mem h →
∀ q₀ ∈ Pools, ∀ x, zc x → 0 < chainCount S γ x h` — THE ONE-WAY COUNT
SUPPLY (no_stray → 0 < Tgam → marks_chains), the lemma V2-5/V4-5/V5-8
consume; its converse is NOT stated (underivable at composites — exactly
HMC's openness, §2.G); (c) `treal_iff_tgam : q₀ ∈ Pools → zc x →
(TReal TE γ x h ↔ 0 < Tgam TE γ x h)` — the REV-7 demotion lemma
(→ real_marks; ← marks_realize), cited wherever the EVENT reading is
needed (V5-1's guard, the entrance symmetry).
moves_ref: "T_γ(x, h) := #{fresh-assignment chains from x realizing
(γ, h)}" + "(no orphan) T_γ(x, h) > 0 for some representative x ⟹
h ∈ H(γ); (no stray) h ∈ H(γ) ⟹ T_γ(x, h) > 0 for EVERY representative"
(V.0, MOVES 7921–7923 + 7947–7949 — VERBATIM at Tgam). deps: Defs 2.G.
sketch: unfold; chain the TE mark facts. hyp_fields: XHDd + TmplEvents
ties (owner [2b] / carrier).

**V1-4 `xhds_eval_nonneg` · `V1_xhds.lean` · easy.**
GIVEN XHDw/XHDd/XHDs: each `Gc γ j` evaluates ≥ 0 at pools (limit of a
nonneg-term sum via `Gc_hasSum` + V1-1). moves_ref: "convergent at every
prime power evaluation (positive weights)". deps: V1-1.
sketch: `HasSum.nonneg`. hyp_fields: XHDw/XHDd/XHDs arguments.

**V1-5 `xhd_discharge` · `V1_discharge.lean` · easy.**
`def IsFullDischarge (n S TE C V) : Prop := Nonempty (XHD n S TE V)` + the RECORD
lemma `theorem cond_of_discharge : IsFullDischarge … → ∀ {P : XHD … → Prop},
(∀ X, P X) → ∃ X, P X` — the [1v]-FULL bookkeeping shape: discharge =
INHABITATION of the package, "no new mathematics"; every measured unit keeps
its explicit `XHD` argument. moves_ref: "[1v]-FULL := the RECORDED DISCHARGE
of the XHD hypotheses upon [2b]'s acceptance — a bookkeeping event" (V.0).
deps: Defs. sketch: trivial. hyp_fields: none (typing unit). [Deliberately
NOT `True`-valued; no unit may replace its XHD argument by this Prop.]

**V1-6 `UA_fixed_history` · `V1_UA.lean` · medium — RE-SIGNATURED at
REV 5 (Fable M-3 = Codex-14: the display still carried the rev-3 pool-free
`Hist α` and a trailing `massOf … q₀` argument that no longer exists —
it did not elaborate against the REV-4 carriers).**
(U-A) AS THE NOTE PROVES IT — this corpus's ONE §C-derivable clause:
`theorem UA (P : C15Pack n S) {α β} (m : S.Move α β) {q₀}
(hq : q₀ ∈ S.Pools) (x : S.Hist q₀ α) (hzc : S.zc x) (h : Hpt (S.dim m))
(a a' : S.Assign m x h) : S.massOf m x h a = S.massOf m x h a'`
(the pool rides the history index — §2.B).
moves_ref: "Fix ONE realizable prefix satisfying (ZC) … BOTH factors are
functions of the read's NOMINAL DIGIT INVENTORY … Hence all fresh assignments
realizing (m, o, β) at h FROM THAT PREFIX carry one common conditional
mass. ∎" (V.0 (U-A)). deps: Defs (C15Pack).
sketch: two `mass_factors` rewrites; both sides = `F (invOf m x h) q₀`.
hyp_fields: `C15Pack` (owner §C/HC-2 — the typed C.1.5(1)+TYP(b) supply; the
PROOF is unconditional given the pack, exactly the note's GIVEN).

**V1-7 `ua_split_fence` · `V1_fence.lean` · medium — RE-SIGNATURED at
REV 5 (M-3's second mechanical leg: same rev-3 pool-free signature).**
THE HONEST-SPLIT WITNESS, display Prop-corrected (A-7): `theorem ua_fence :
∃ S : StepSys n, ∃ _P : C15Pack n S, ¬ (∀ {α β} (m : S.Move α β) {q₀}
(_ : q₀ ∈ S.Pools) (x x' : S.Hist q₀ α) h (a : S.Assign m x h)
(a' : S.Assign m x' h), S.massOf m x h a = S.massOf m x' h a')` — nested
existentials, no Type-as-conjunct; same-pool histories (the cross-history
lumpability (u-R) denies §C, at ONE pool). moves_ref: "NOT §C-derivable, HYPOTHESIZED in (XHD-u)
(they are lumpability assertions about histories §C never compares)" (V.0).
deps: Defs. sketch: two-history toy model, F distinguishing inventories;
norm_num. hyp_fields: none — a machine-checked record that (XHD-u) is not a
consequence of the pack (the inverse-defect discipline).

**V1-8a `stepsys_realized` · `V1_witnessA.lean` · medium — SPLIT (Codex-19);
POOL-INDEXED at REV 4.**
THE STEP-SYSTEM WITNESS: ONE concrete finite `StepSys` instance (two cells,
one continuing move with dim 1 + one terminal move, listed one-component
domain, `Hist q₀ α := PUnit` at every pool, `Assign x h := Fin 1` on the
domain and `Empty` off it, `ext` the evident map) which INHABITS,
non-degenerately, `StepSys` (all non-vacuity fields incl. the REV-3
productivity `out_ne`, now pool-guarded, AND the REV-5 `pools_ne` —
Codex-12: the toy's Pools = the prime powers, nonempty by ⟨2, …⟩), a
`C15Pack` (incl. the T-twin fields), an `XHDw` (E = h + 1; zc guards
trivial), an `XHDu` (incl. T-twins). moves_ref: the V.0 package displays (each quantifier realized at
a true instance). deps: Defs. sketch: decide/norm_num.
hyp_fields: none — a PROVED instance.

**V1-8b `xhdds_realized` · `V1_witnessB.lean` · medium — SPLIT (Codex-19);
REV 4: the PROCESS SIDE realized.**
Over V1-8a's instance: a `TmplEvents` toy (Box q₀ N := Fin 1; tevt/tinst :=
the full box on the product-of-listed-domains points, ∅ off them — all FIVE
ties by decide: length-1 iff ×2, real_marks, marks_chains, and the REV-7
`marks_realize`), an `XHDd` over it
(exactness against the toy `Tgam` holds by decide — REV 7, C6), and an `XHDs` (one
geometric sum — the V0-4 pattern at dim 1); `MDomTie` holds by rfl on the
toy's lists. moves_ref: (XHD-d)/(XHD-s) displays + the §2.G process carrier.
deps: V1-8a, V0-4's pattern. sketch: one geometric series + decide.
hyp_fields: none — a PROVED instance. [At THIS toy HMC happens to be true —
the false-HMC instance is V4-11's, with a COUPLED composite tevt; together
they bracket the kernel: satisfiable both ways, provable neither.]

**V1-8c `measured_faces_realized` · `V1_witnessC.lean` · medium — SPLIT
(Codex-19).** Over a one-cell/one-template `CtsMeasured` toy on the same
system (incl. the REV-3 census/tie fields entInst/ent_card/box_card/
evt_card/stInst_card AND the REV-4/5/6/7 laws — evt_disj_cell at the
`CellOf` key (now the REAL §2.F def — C10), the omem/tcellM roster data
WITH `omem_sel` + `tcellM_sel` (Codex5-22/C3: the toy's designated
targets are roster members landing by tcell, by construction), the REV-7
carrier [tie]s `evt_disj_assign`(+T) (Fin-1 assignments — decide) and
`ent_sel` (the toy censuses chosen disjoint per label) — realized by
explicit finite data; the struck `EntMassSummable`/`MarkDisj`/`MarkDisjT`
appear NOWHERE (C7/C8)): the faces
`XHDdC`/`XHDsC`/`XHDsEnt`/`XHDdEnt`, hence the FULL bundle `XHD` (over
V1-8b's TmplEvents toy).
moves_ref: the V.0 package + V.1(iii)/(iv) faces. deps: V1-8b, Defs 2.F/2.G.
sketch: decide + one geometric series; the census data is a literal.
hyp_fields: none — a PROVED instance; together with V1-7's failure witness
V1-8a/b/c bracket the packages (satisfiable, not vacuous; not §C-implied).

### Layer V2 — state space + tables [10]

**V2-1 `skeleton_menu` · `V2_skeleton.lean` · easy.**
ROSTER (2 — C28): (a) `letter_menu_out (B : BlockData n s) (m) :
B.letterSp m ∈ MovesSp.Out n s.sp` (projection); (b) `skeleton3_finite :
Set.Finite {s : Skeleton 3 | True}` via `SnRaw` finiteness (SP2/SP6, the
53-catalogue). moves_ref: "Out(s) := the finite p-INDEPENDENT SYNTACTIC menu
… ([2a] SP-OUT + M1 bookkeeping ALONE, evaluated over NO residue field)"
(CTS-S). deps: MovesSp.SP2_finThm, Defs. sketch: image of a finite set.
hyp_fields: none — the note's "[2a] pending" inheritance is DISCHARGED
against the PROVED MovesSp (recorded upgrade, §0).

**V2-2 `cellidx_delete` · `V2_cells.lean` · easy — DEDUPLICATED at REV 5
(Codex-16: rev 4 declared `BlockData.CellIdx` BOTH in §2.C Defs and in
this roster — a duplicate-name error; the def's ONE home is §2.C).**
ROSTER (2 — C28): (a) `instance : Fintype B.CellIdx` (for the §2.C def);
(b) `deleted_empty`: deleted cells have empty fibers at every prime power
(`size_count` + eval 0 ⟹ card 0). moves_ref: "cells with IDENTICALLY-zero size polynomial are
deleted from 𝒞_n once, symbolically" (CTS-S). deps: Defs.
sketch: subtype Fintype; card = 0 from ℚ-cast. hyp_fields: none.

**V2-3 `meet_finite_uniform` · `V2_meet.lean` · medium.**
Clause (i)'s proved core: the product-of-generators cell map
`x ↦ (fun g => (B.gen g).part q₀ x)` induces a finite partition of
`Carrier q₀` with p-independent label set `∀ g, idx g`; fibers are pairwise
disjoint and exhaustive; refines EVERY generator.
moves_ref: "the meet of finitely many finite uniform partitions is finite and
uniform, and labels are fixed by (D2)/(D3)'s conventions" (V.3(i)).
deps: V2-2. sketch: fibers of a total map partition the domain; `Fintype.pi`.
hyp_fields: none. [The note's conditionality of clause (i) on the UNCOMPUTED
skeletons is the `BlockData`-per-skeleton ARGUMENT — clause (i) at full depth
is `∀ s, BlockData n s → …`, never "proved by construction" bare.]

**V2-4 `val_a_burden` · `V2_valA.lean` · easy (statement-shape unit) —
RE-KEYED (Codex-4: rev 2's `tbl_count` was BOTH too weak — guarded by
`0 < cntraw`, silent at zero-count entries — AND too strong — realized-height
equality smuggled (u-T), which the note assigns to (XHD-u), into VAL(a)).**
`structure ValA (n) (C : CtsFamily n) (S) (V : CtsMeasured n C S) : Prop`
with fields: (a) **REWRITTEN at REV 5 (Fable M-1 — the inherited rev-2
display quantified β FREE with a β-independent right side, forcing EVERY
TargetIx entry of the row — junk terminals included — equal to the datum's
count; the note-correct gate family FALSIFIED `valA_gate` at the T21
letter's junk `.term ⟨(1,1),_⟩` column: 0 = 2 at q₀ = 2. The index is now
THE DATUM'S OWN, exactly as V2-5/V5-8/V7-4c already bind it):**
`tbl_count : ∀ (d : MoveData n C) {q₀} (x : S.Hist q₀ _)
(hzc : S.zc x) (hq : q₀ ∈ V.Pools) (j : Fin (V.mdom d).comps.length),
((C.T d.s d.m d.o d.α d.tix).eval q₀ : ℚ) = S.cntraw (V.moveOf d) x
(((V.mdom d).comps.get j).base)` — the polynomial AT THE DATUM'S TargetIx
(`MoveData.tix`, §2.C) valued at the count AT THE LISTED BASE POINTS of
the one-step domain, ∀ representatives AT THE POOL
(REV 4, N-2: the count is a count of q₀-histories' fibers — the law is
satisfiable at non-constant tables. THE ACCEPTANCE NUMBERS, displayed:
T21 = X·(X−1) has eval 2 = 2 and eval 3 = 6; at q₀ = 2 the law pins the
F₂-fiber count 2, at q₀ = 3 the F₃-fiber count 6 — different fibers,
different naturals, one polynomial, exactly VAL(a)); UNGUARDED at zero:
· at an entry inadmissible at q₀ the base counts are 0, so the law FORCES
  T.eval q₀ = 0 (horn (i) closed — it says something at zero counts);
· NO height-uniformity is entailed: the polynomial is pinned only at base
  points; its validity across each component is EXACTLY (u-T)'s content,
  cited where consumed (V4-5, V2-5) — horn (ii) closed. Representative-
  uniformity stays (the note's own alternative discharge: "the table build
  proves representative-uniform count rows per species").
(a′) **THE OFF-KEY ZERO CLAUSES (REV 5 — VAL(a)'s "valued correctly at
every prime power q" covers EVERY displayed entry; off the (D4) landing
the correct count is 0, since `moveOf`'s target is tcell-enforced BY TYPE
— §2.C/§2.F):** `tbl_offkey : ∀ (d : MoveData n C)
(β : TargetIx n (C.bd d.s) C.bd d.m d.o) {q₀}, q₀ ∈ V.Pools → β ≠ d.tix →
((C.T d.s d.m d.o d.α β).eval q₀ : ℚ) = 0` — with `TargetIx.term` gated by
¬cont (Codex-3), the off-key entries of a continuing outcome are exactly
the non-landing target cells; the round-4 cooked-junk family (junk entries
:= the row count) now VIOLATES a field, restoring the doctrine ("a
faithful interface must be FALSE for instances the note would reject"),
and the note-correct family (junk ≡ 0) satisfies it — `valA_gate` is
satisfiable again.
(+ `tbl_countT`, the [+T] twin over mdomT/cntrawT AT `d.tix = .term d.ht v`
— the datum's absorbing label, bound through `TermData.hv`; +
`tbl_offkeyT`: entries at wrong absorbing labels v' ≠ C.vlabOf … evaluate
0 at pools);
(b) the size ties (`size_deg`/`size_count`-keyed, already TYPE);
(c) `tgt_supported : ∀ (d : MoveData n C) {q₀} (x : S.Hist q₀ _)
(hzc : S.zc x) (h), q₀ ∈ V.Pools →
V.activeState q₀ (toStepCells.symm d.src) →
¬ V.activeState q₀ (toStepCells.symm d.tgt) → S.cntraw (V.moveOf d) x h = 0`
— "a landing forces a concrete target state", the count-level landing tie,
NOW GUARDED BY THE ACTIVE SOURCE + zc (REV 4, Codex-9: the note's (ii-a)
reads "for every source active at q₀ …" and "deliberately leaves
inactive-source rows as formal junk" — rev 3 smuggled the unguarded form
into the hypothesis; V4-1's conclusion guard alone was not enough);
(d) NEW at REV 3 (Codex-15): `ent_supported : ∀ (ε : EntShapeV n) (β₀)
(q₀ ∈ V.Pools), ¬ V.activeState q₀ β₀ → V.entCensus ε β₀ q₀ = 0` — the SAME
landing sentence at the entrance layer ("… and ι of (iii) is supported on
Act_{q₀}", V.1(ii-a); the entrance leg has no source state to guard) —
V4-1's iota_supp is derivable, not free.
+ `theorem valA_gate : ValA 3 gateFam gateMeas` DEFERRED to V6.
moves_ref: "(a) LOCAL: every entry T_{m,o}^{α,β} is ONE polynomial in ℚ[q] of
degree ≤ W_loc(m), and every cell size |α| ONE polynomial of degree ≤
W_state(s), each valued correctly at every prime power q" (Thm VAL) +
"(ii-a) NO-ENTRY … and ι of (iii) is supported on Act_{q₀}" (V.1(ii)).
deps: Defs. sketch: structure decl + gate pointer. hyp_fields: the count ties
are per-skeleton TABLE-BUILD burdens (CL-13/V.5(4)) — open beyond the V.6
blocks, stated as the structure.

**V2-5 `val_b_chain` · `V2_valB.lean` · medium — RESTATED (C2/C9).**
Theorem VAL(b) GIVEN (XHD-u)'s count face, over the DEFINED `chainCount`
(no free chain data, no missing tie field — the recursion is definitional):
ROSTER (3): (a) `chain_resolved (U : XHDu n S) {α} (γ) (x) (h) :
chainCount S γ x h = hProd γ h` where `hProd γ h := ∏ᵢ cnt_i(hᵢ)` with each
factor state-only (well-defined by u_R_cnt) — pure induction on γ through
`ext` (base = cntraw def; cons = `Fintype.sum_const` after IH + u_R_cnt at
the extended histories); (b) `valB (hVA : ValA n C S V) (U : XHDu) (D : XHDd n S TE)
(hTie : MDomTie V TE D) (hzc : S.zc x) (q₀ ∈ V.Pools)
(hmem : (D.dom γ).Mem h) :
(chainCount S γ x h : ℚ) = (pathProdPoly C γ).eval q₀` — REV 3 (Codex-4's
V2-5 leg): the path product is THE TABLE POLYNOMIALS' product,
`pathProdPoly C γ := ∏ᵢ C.T (step-i data of γ) ((step-i datum).tix)` (a
displayed def of this file over `dataOf`; `.tix` = §2.C's datum index —
REV 5: the SAME object `ValA.tbl_count` now binds, M-1), CONNECTED to ValA
and evaluated at q₀.
REV-4 ROUTE (N-1 ripple): realized-ness now comes from V1-3(b)'s
`mem_chainCount_pos` (Mem → 0 < Tgam → marks_chains → 0 < chainCount — the ONE-WAY
supply), whose positivity decomposes stepwise through the recursion; then
u_T carries each realized cnt_i(hᵢ) to its base point and `tbl_count`
values it — base realizability through `MDomTie.mdom_eq` (Codex-5's tie,
now a displayed premise); terminal factor via the [+T] twins;
(c) `pathProd_deg : (pathProdPoly C γ).natDegree ≤ W γ` —
the degree bound RE-SCOPED (C9): it is a POLYNOMIAL-degree statement about
C_γ(q) = ∏ T given ValA's `T_deg` (Σ W_loc arithmetic), NOT a counting
inequality with no hypotheses. moves_ref: "(b) CHAIN — GIVEN (XHD-u)'s COUNT
FACE …: the PER-REPRESENTATIVE linked count from one fixed source
representative EQUALS the PATH PRODUCT C_γ(q) = ∏ T" (Thm VAL).
deps: Defs, V1-2, V1-3, V2-4 (for (c)). sketch: as per roster.
hyp_fields: XHDu + XHDd (owner [2b]) + MDomTie (the [1v]/[2b] coherence tie,
displayed); "never proved here" — the unit derives the equality FROM them,
matching "hypothesized in (XHD-u), never proved here (alternative discharge:
the table build proves representative-uniform count rows per species)".

**V2-6 `exp_audit_pow` · `V2_audit.lean` · medium.**
The EXPONENT-MAP AUDIT's worked law: for a finite field F with `|Fˣ| = m`,
the image of `t ↦ t^a` on `Fˣ` has cardinality `m / gcd a m`.
moves_ref: "e.g. the image size of t ↦ t^a on F_{q^g}ˣ is
(q^g − 1)/gcd(a, q^g − 1)" (EXPONENT-MAP AUDIT).
deps: none (Mathlib: `IsCyclic`, `powMonoidHom`, index/range card).
sketch: cyclic Fˣ; image of power map = unique subgroup of order m/gcd.
hyp_fields: none. [The AUDIT as a duty — "each such factor either cancels
against a displayed cell-size factor or splits the cell" — is a FIELD of the
table-build structure `AuditedEntry` in this file: per entry, a proof term
`cancels ⊕ splits`, consumed by V2-4's gate instances.]

**V2-7 `val1_worked` · `V2_val1.lean` · medium — CELLS CORRECTED (Codex-12:
rev 2's FL = {y = 0} and FS = {x = 0} both contained (0,0) and overlapped —
not the displayed disjoint strata).** The VAL.1 worked instance, stated
generically: F a field, `V : Fˣ × Fˣ → F × F`, `V (A, B) = (A, B)` in the
basis coordinates (the note's V(A,B) = Aα + B read in the basis {α, 1}).
ROSTER (2): (a) the THREE cells AS THE NOTE DISPLAYS THEM —
FG = {x ≠ 0 ∧ y ≠ 0}, FL = {x ≠ 0 ∧ y = 0} (= F_qˣ·α: the nonzero
coordinate REQUIRED), FS = {x = 0 ∧ y ≠ 0} (= F_qˣ) — are pairwise disjoint
and partition the NONZERO target (F×F) \ {(0,0)} (the target t = xα + y of
a value map into F_{q²}; the origin is no cell's member and carries fiber
count 0 — stated as its own lemma, outside the three-cell partition);
(b) the fiber count is 1 on FG, 0 on FL, 0 on FS — c_V constant per cell.
moves_ref: "Worked instance (V(A,B) = Aα + B …): THREE cells — FG =
{x ≠ 0, y ≠ 0}, c_V = 1; FL = F_qˣ·α (y = 0), c_V = 0 (B = 0 prohibited);
FS = F_qˣ (x = 0), c_V = 0 (A = 0 prohibited)" (VAL.1).
deps: none. sketch: coordinates are literal; fiber = {(x,y)} iff both
nonzero, else empty (A = 0/B = 0 prohibited by Fˣ). hyp_fields: none.

**V2-8 `anchor_twist_fence` · `V2_anchor.lean` · easy — RESTATED (C10).**
ANCHOR ALIGNMENT, now STRUCTURAL (the type does the fencing): ROSTER (2):
(a) `anchor_twisted (G : GenSpec Carrier) (ha : G.kind = .anchor a_eff) :
∀ q₀ x, G.part q₀ x = G.base q₀ (G.twistOf q₀ a_eff x)` — at a_eff ≠ 0 the
cells apply to the TWISTED target and NEVER directly to the fixed frame
(the partition map factors through the twist BY the `part_eq` field; there
is no un-twisted access to `part`); (b) `anchor_zero : G.kind = .anchor 0 →
G.part = G.base` (via `twist0`) — the a_eff = 0 collapse, now a corollary
not the content. moves_ref: "at anchor exponent a_eff ≠ 0 the cells apply to
the TWISTED target α^{−a_eff}·t, never to t in the fixed frame — fixed-frame
cell counts are PROVABLY char-dependent (the value probe …)" (VAL.1).
deps: Defs 2.C. sketch: field projections. hyp_fields: none. [The
char-dependence refutation itself is the Python probe's, cited as evidence —
no Lean claim.]

**V2-9 `deg_cons_gate` · `V2_degcons.lean` · easy.**
DEG-CONS at the computed rosters: for the V.6 gate family's outcome rosters,
every m ≥ 2 outcome has per-member sizes e_j ≥ 1 with Σ e_j ≤ e — by
`decide` over the DefsGate lists, which at REV 5 ARE the gate BlockDatas'
`omem` member rosters (Codex-2: the per-member tuples finally have a
carrier; the statement quantifies `∀ mu ∈ omem m o`); PLUS the shape lemma
producing `MovesS.DegCons gateTS` for V7-3b (`Member.size` = `OMember.size`
under V7-3a's odata map — definitional). moves_ref: "DEG-CONS … m ≥ 2 children,
each child cluster size e_j ≥ 1, Σ_j e_j ≤ e — per member … The check runs
over the FULL roster of each computed table block" (V.2).
deps: DefsGate. sketch: decide. hyp_fields: none at the gate blocks; the
full-roster check at other skeletons is CL-11's burden (typed as the ValA-
style structure field, open).

**V2-10 `wloc_wstate_split` · `V2_bounds.lean` · easy — RESTATED (C11).**
The SPLIT-bound fence, examples now matching the claims: ROSTER (2):
(a) `gate_bounds`: the gate data's actual values RECORDED with their true
directions — root: Wstate = 0 < Wloc = 3; s_blk2: Wstate = 1 < Wloc = 2
(norm_num; these illustrate sizes and table degrees living on DIFFERENT
keys); (b) `wstate_gt_wloc_consistent`: an explicit SYNTHETIC `CtsFamily`
instance (one skeleton, sizeP = X so Wstate = 1; one letter with constant
entry T = 1 so Wloc = 0) witnessing `Wstate s > Wloc s m` — the note's "may
exceed some W_loc(m)" possibility, now witnessed in the CORRECT direction
(rev 1 cited two gate examples that both satisfy the opposite inequality).
moves_ref: "(SPLIT bounds — a source-cell size belongs to (s, α), not to any
outgoing m, and may exceed some W_loc(m))" ((iv)-POLY). deps: DefsGate.
sketch: norm_num + a two-line instance. hyp_fields: none.

### Layer V3 — entrance shapes + clause (iii) [17]

**V3-1 `entshape_postsplit` · `V3_eps.lean` · easy — RE-SCOPED (Codex-5:
rev 2's (b) claimed a derivation the fields cannot give).**
POST-SPLIT TYPING: ROSTER (2): (a) injectivity of the label in the σ_sel
coordinate (two `EntShapeV` differing in `selRec` are ≠ — trivial, but it is
what the LABEL layer owns); (b) the SEMANTIC LEG, RE-TARGETED at REV 6
(Codex5-23): σ_sel's entries record the SELECTED (side, ψ) continuations
through the membership DEF `SelMatches` (§2.D — entry r = `selRank w ν_r %
m̄_r` at the r-th branching read's realized node, MovesD's own E9 encoding
component), and the lemma is: two entrance CUTS (2.E) whose realized
prefixes take DISTINCT eligible ψ-selections at read r admit NO COMMON
`SelMatches` label — distinct ψ ⟹ distinct `selRank` (MovesD's PROVED
`E8_rankInj`), both < m̄_r (E7: the mod-collapse is the identity on
members), so no one selRec r-entry equals both. Cited, never re-derived.
The note's "siblings … differ in s_r" is the CONJUNCTION (a) + (b).
moves_ref: "siblings at a shallow split differ in s_r, hence carry DISTINCT
ε — ι never aggregates a pre-split f-event or a joint-sibling locus"
(V.3(iii)) + "σ_sel = (s_r … — L11's encoding data, lifted into the label)".
deps: Defs 2.D/2.E, MovesD.E8_rankInj. sketch: structure injectivity +
rank-distinctness through the `SelMatches` def. hyp_fields: NONE beyond
MovesD's proved apparatus (REV 6: the rev-5 `SelRankTie` hypothesis is
GONE — the tie is definitional class membership, not a coherence premise).

**V3-2 `hent_proj` · `V3_hent.lean` · easy.**
h_ent is a PROJECTION: `hent` is a function of ε (definitional), determined
by `Phat` alone; + the non-degeneracy law: two ε with same template but
different read-heights have different `hent` (heights are RETAINED, not
quotiented). moves_ref: "h_ent(ε) := the tuple of ε's RETAINED height data —
… a FUNCTION of ε, displayed, no free height variable anywhere" (V.1(iii)).
deps: Defs. sketch: `List.map` congruence + a two-read discriminating
instance. hyp_fields: none.

**V3-3a `spword_def` · `V3_spwordA.lean` · medium — REAL UNIT ID at REV 4
(Codex-16: the pre-approved split is PROMOTED; the parent V3-3 dissolves
into a/b/c/d, each one display).**
`def spWord (n) (P : MovesD.ShapePrefix) : List MovesSp.Species` (fold of
the stage laws along `P.reads`) + its law: consecutive outputs satisfy
`MovesSp.SuccStep` when the reads satisfy MovesD's `ShapeWF` stage clauses.
moves_ref: "ε̊ := ε's height-forgetting TEMPLATE (SP.1 applied to P̂,
selection data kept)" (V.1(iii)). deps: MovesD.Defs, MovesSp.Defs.
sketch: structural recursion over reads; match `ShapeRead` fields to
`Species` stage fields via the D.5/D.7/D.8 output laws. hyp_fields: the
ShapeWF certificate (MovesD's, PROVED apparatus) — no open kernel.

**V3-3b `spword_collapse` · `V3_spwordB.lean` · medium — RE-KEYED at
REV 7 (C11: rev 6's `spWord_collapseWF` was a V3 lemma consumed by the
DEFS-layer `EntShapeV.template` — a forward reference; §2.D's `template?`
now CHECKS the six clauses by classical dite, and this unit proves the
check PASSES).**
THE TOTALITY + TIE THEOREM `template_total : ∀ ε : EntShapeV n,
(ε.template?).isSome` — the collapsed word is nonempty,
catalogue-membered, and a `CollapsedWalk`; the entry/len/menu ties
transport from ε's §2.D WF fields (same six-clause content as the old
`spWord_collapseWF`, now the dite-pass proof; the `hrank` clause stays
GONE, Codex5-23). Downstream units read `ε.template := (ε.template?).get
(template_total ε)` — DECLARED HERE, total, no forward reference.
moves_ref: as V3-3a + [2a]'s collapse convention.
deps: V3-3a. sketch: CollapsedWalk transport → the dite's hypothesis.
hyp_fields: as V3-3a.

**V3-3c `entshape_bridge` · `V3_spwordC.lean` · medium.**
The ENTRANCE-SHAPE BRIDGE: from (ε̊, h) construct the
`MovesSp.EntranceShape n gsel musel` behind it (word + hMem + hChain +
hEntry from ε̊'s fields; heights h into the slot functions) — the §1
consumption tie A-3 demanded. moves_ref: as V3-3a. deps: V3-3a/b.
sketch: field transport. hyp_fields: as V3-3a.

**V3-3d `spword_faithful` · `V3_spwordD.lean` · HARD — the Codex-6
reconstruction bridge (the corpus's real E-phase risk); RE-KEYED at
REV 7 (C11: the reconstruction DEF `readOfLetter?`/`ReadFits` moved into
the Defs layer — no forward reference; THIS unit owns the THEOREMS).**
ROSTER (3): (a) `readFits_unique` — the `ReadFits`-satisfying ShapeRead
is UNIQUE (e/g/μ/s0/wSide/Dwidth/w pinned by the letter's stage fields
and the WF chains (width chain, wchain), ustar via zig + `gamTie`'s
inversion, a/gam via `anchorTie`/`gamTie` — the §2.D clause list);
(b) `writeHeights_total : ∀ ε̊ (h : Hpt ε̊.entDim),
(writeHeights? ε̊ h).isSome` — existence along template slots: every
`readOfLetter?` dite passes on the expanded word and the folded prefix
is WF with the five EntShapeV ties (= exactly the old
`writeHeights_wf`/`writeHeights_ties` content, now the dite-pass proof);
declares the TOTAL `writeHeights ε̊ h := (writeHeights? ε̊ h).get
(writeHeights_total ε̊ h)` — the token every V3–V7 statement uses;
(c) `spWord_faithful`: two shallow WF prefixes with
equal collapsed spWord, equal height/depth/u*-code slots are EQUAL — SP.1
genuinely forgets ONLY heights, realized as a THEOREM from the two corpora's
WF laws. THE load-bearing leg of V3-5a's injectivity; ESCALATION HATCH
recorded at §2.D (if a datum is genuinely lost, the template gains it as a
field, with a fresh audit — never silently).
moves_ref: as V3-3a + L3 rev 9 (retained (h, u*)).
deps: V3-3a, MovesD.Defs (gamTie/anchorTie/wchain).
sketch: invert the stage-output laws read by read. hyp_fields: as V3-3a.

*(Legacy ID note: "V3-3" in earlier dispositions = the a/b/c/d suite;
"V3-3(d)" = V3-3d.)*

**V3-4 `template_finite` · `V3_tfin.lean` · medium — RESTATED (C12/A-3).**
The template family is FINITE, OUTRIGHT AND UNCONDITIONALLY (no `WordBounded`
premise exists — the boundedness is §2.D's intrinsic WF fields):
`theorem template_finite (n) : Finite (EntTemplate n)` (n = 3 build target;
stated for the n the corpus fixes). moves_ref: "the family {ε̊} is FINITE
([2a]/M1 for the P̂-templates; L5's finite eligible-continuation menus for
the σ_sel's)" (V.1(iii)). deps: V3-3, MovesSp.SP2_finThm.
sketch: `hWalk` words are collapsed SuccStep walks over the finite SP2
catalogue; `rankNat` strictly increases along collapsed edges (the
SP4_dagWords idiom — at n = 3 decidable over the 53-catalogue), bounding
word length; words of bounded length over a finite alphabet are finite;
`hlen`/`hmenu` bound selRec (length by the word, entries by the L5 menus);
(gsel, musel) bounded via `hEntry` + the catalogue's finite sel field.
hyp_fields: NONE (this was C12's silent-weakening finding: the note asserts
finiteness from [2a]/M1 + L5, and the Lean statement now proves exactly
that, quantifier unmoved).

**V3-5a `inst_bij_inj` · `V3_instbijA.lean` · HARD — REAL UNIT ID at REV 4
(Codex-16; the parent V3-5 dissolves into a/b/c).**
INJECTIVITY of the instantiation map on H(ε̊): distinct h give distinct
`writeHeights ε̊ h` — V3-3d's `spWord_faithful` (heights + u*-codes
determine the reads given the template). moves_ref: "the INSTANTIATION MAP
h ↦ ε̊[h] … is a BIJECTION from H(ε̊) onto {concrete ε with template ε̊} —
D4R.1-SUM is cited ONLY at concrete ε" (V.1(iii), pass-3 F1's two horns).
deps: V3-3d, Defs 2.D. hyp_fields: none beyond V3-3d's apparatus.

**V3-5b `inst_bij_surj` · `V3_instbijB.lean` · medium.**
SURJECTIVITY onto {concrete realizable ε with template ε̊}, GIVEN the
entrance exactness face: no_strayE realizability + template-matching
through readOfLetter; membership in EntIx via `lands_of_realizable`
(Codex-6's landing horn). `Realizable` is the DISPLAYED §2.G def.
deps: V3-3d, V3-4, Defs 2.G. hyp_fields: XHDdEnt (owner [2b] — the
shallow-layer XHD-d face, with the landing law).

**V3-5c `inst_bij_eq` · `V3_instbijC.lean` · medium.**
THE ASSEMBLED EQUIV + computation law: `∃ e : {h // (V.entDom ε̊).Mem h} ≃
{ε : EntShapeV n // ε.template = ε̊ ∧ Realizable V ε β₀}, ∀ h, (e h).1 =
writeHeights ε̊ h.1` (incl. the zig/gamTie roundtrip check).
deps: V3-5a/b. hyp_fields: XHDdEnt.

*(Legacy ID note: "V3-5" = the a/b/c suite.)*

**V3-6 `iota_muhat` · `V3_iota.lean` · medium — RESTATED (C13).**
ι's typing laws, the FALSE IFF STRUCK: ROSTER (3): (a) `iota_le_total`:
`iotaCount ε cut S ≤ Σᶠ i, Nat.card (S.fiber i)` (a SUB-SUM of D4R.1-SUM's
index); (b) `iota_eq_of_total`: IF `lands` is total THEN equality — ONE
direction only (rev 1's converse is FALSE: excluded indices may have empty
fibers; C13); (c) `iota_d10_tie`: the D4R.1-SUM tie at stabilized levels —
each summand's fiber card × p^{A'} = p^{nN}, via the EXPORTED
`MovesD.D4R1_SUM` + `MovesD.D0b_thmCtop` (G-4 repair: rev 2 cited "D10's
`key`", a proof-internal `have` in `D10_sumLaw.lean`, not a consumable).
This tie is also what discharges `CtsMeasured.ent_card` at the real
instance. moves_ref: "ι_{e,ε,β₀}(p) := the D4R.1-SUM MARKED mass μ̂ of the
entrance family refined by ε (each summand Theorem C(b); an f entering twice
carries two marks — a μ̂-object, never an f-event mass)" (V.1(iii)).
deps: MovesD.D10_sumLaw, Defs 2.E. sketch: `finsum` over a subset ≤ total;
per-summand D10.key. hyp_fields: `S.jet` (MovesD's presented-jet field, as in
D10); the `lands` cut (§D4-R L5 cell data — a parameter with its (D4)-tie).

**V3-7 `ent_agg_finite` · `V3_aggfin.lean` · medium.**
ENT-AGG's hypothesis-free half: for FINITELY many pairwise-distinct concrete
ε (distinct marked pairs), the refined counts ADD:
`iotaCount` over a disjoint union of cuts = Σ of `iotaCount`s
(μ̂-additivity over disjoint mark families).
moves_ref: "The primitives and every FINITE partial sum are hypothesis-free
(μ̂-additivity over disjoint mark families — distinct concrete ε give
distinct marked pairs)" (V.1(iii)). deps: V3-6, V3-1.
sketch: `finsum_mem_union` on disjoint index sets. hyp_fields: none.

**V3-8a `ent_agg_conv` · `V3_aggfullA.lean` · medium — SPLIT at REV 4
(Codex-7: rev 3's single unit required (ENT-U) for the AGGREGATE, but the
note's ledger line gives ENT-AGG's convergence "GIVEN XHD-s on the shallow
layer" ALONE — "(ENT-U) is required for INIT-RAT, not for defining or
aggregating the marked masses". The aggregation and the ιval identification
are now SEPARATE units with SEPARATE premise sets).**
THE NOTE-EXACT AGGREGATION — PREMISE RE-KEYED at REV 7 (Codex6-C7: rev
5/6's `EntMassSummable` was ITSELF a silent strengthening — the note's
ledger line grants convergence "GIVEN XHD-s on the shallow layer" ALONE,
MOVES 8124–8133, so no separate summability hypothesis may be levied):
`theorem ent_agg_conv (XsEnt : XHDsEnt n S V)
(DE : XHDdEnt …) (β₀) (q₀ ∈ Pools) : ∃ v : ℝ, HasSum (fun p : Σ i :
V.EntIx β₀, {h // comp-Mem i h} => ιshH V p.1.1.1 p.2.1 β₀ q₀) v` —
the count-weighted summability is DERIVED from the shallow face: per
(template, component), the census is a Finset of Box(q₀, entLvl ε̊) at
the FIXED defining level, so instCensus ≤ |Box(q₀, entLvl)| =
q₀^{n·entLvl} UNIFORMLY in h (`box_card` + Finset.card_le_univ); the
summand is ≤ q₀^{n·entLvl}·q₀^{−A}, and `Summable.of_nonneg_of_le`
against the q₀^{n·entLvl}-scaled `Gent_hasSum` weight sum closes each
component; finitely many (template, component) pairs (V3-4 × list
length). Entrance heights summed HERE and
nowhere else; each concrete realizable ε hit EXACTLY ONCE (V3-5's bijection
composed with the disjoint component listing + lands_of_realizable — no
realizable entrance omitted). NO (ENT-U). moves_ref: "ι_{e,β₀} := Σ_{ε̊}
Σ_{h ∈ H(ε̊)} ι_{e,ε̊[h],β₀} … The primitives and every FINITE partial sum
are hypothesis-free …; CONVERGENCE of the full aggregate … is GIVEN
XHD-s on the shallow layer" (ENT-AGG). deps: V3-5a/b/c, V3-7, V3-4, V0-3.
sketch: comparison against the box-bounded weight sum, per component;
the exactly-once structure is the content. hyp_fields: `XHDsEnt` (THE
XHD-s shallow-layer face itself, owner [2b] — VERBATIM the ledger line;
REV 7: nothing else) + XHD-d
shallow (owner [2b]); (iv)-REP invoked NOWHERE (the note: "never for the
sum's definition").

**V3-8b `ent_agg_ival` · `V3_aggfullB.lean` · medium.**
THE ιval IDENTIFICATION (the seam's object): GIVEN additionally (ENT-U),
V3-8a's aggregate value IS `ιval β₀ q₀ = Σ_i entCount i q₀ · evalAt
(XsEnt.Gent β₀ i)` (V7-4b's DEF): per component the census is CONSTANT by
(ENT-U), factor it out (HasSum.mul_left) of the weight-only Gent_hasSum;
finite outer sum (V3-4 × list length). THIS is where (ENT-U) enters — the
note's own INIT-RAT line lists it; the aggregate's existence never needed
it (V3-8a). moves_ref: ENT-AGG + "INIT-RAT (BURDEN, GIVEN XHD on the
shallow layer + (ENT-U))" (V.3(iii)). deps: V3-8a, V3-9b.
sketch: per-component factoring; sum comparison. hyp_fields: V3-8a's set +
(ENT-U) (owner [2b] M4b — displayed).

*(Legacy ID note: "V3-8" = a + b.)*

**V3-9a `ent_count_stmt` · `V3_entcount.lean` · easy (statement unit) —
RE-KEYED at REV 3 (F-2 + Codex-7: PER CONCRETE ε, against the CENSUS —
never the base-point collapse, never a box-event card).**
ENT-COUNT as the NAMED BURDEN, at the note's own granularity:
`def EntCount (V : CtsMeasured …) : Prop := ∀ (ε : EntShapeV n) (β₀ : S.Cell),
Realizable V ε β₀ → ∃ P : Polynomial ℚ, P.natDegree ≤ ε.Went ∧
∀ q₀ ∈ V.Pools, (P.eval q₀ : ℚ) = V.entCensus ε β₀ q₀` — "each I^ent_{ε,β₀}
is one polynomial", ε concrete; the collapse of the family {ε̊[h] : h ∈ c}
to ONE polynomial is (ENT-U)'s separate content (V3-9b), NEVER assumed here
(Codex-7's carrier-collapse horn closed). Degree ledger at gate B: census
polynomial q(q−1), degree 2 ≤ Went = 3 ✓ (F-2's joint-satisfiability
acceptance). + the displayed FENCE lemma: `I^ent = |β₀|` is NOT assumed (no
field ties them; the gate exhibits I^ent = q·|β₀| ≠ |β₀| — V6-4a).
moves_ref: "ENT-COUNT (named burden): each I^ent_{ε,β₀} is one polynomial
in q of degree ≤ W_ent(ε) … I^ent = |β₀| is NOT general — a per-family
theorem, displayed wherever used" (V.1(iii)).
deps: Defs 2.F. sketch: def + gate pointer. hyp_fields: ENT-COUNT itself
(owner [1v], open — THIS corpus's burden, V.5(3)).

**V3-9b `ent_u_stmt` · `V3_entu.lean` · easy (statement unit) — RE-KEYED
(over the census).**
(ENT-U), typed: over each listed component c of H(ε̊), the per-concrete-ε
census polynomial is ONE polynomial CONSTANT across the instantiations:
`def EntU (V) : Prop := ∀ β₀ (i : V.EntIx β₀), ∃ P : Polynomial ℚ,
P.natDegree ≤ Went i ∧ ∀ h, comp-Mem i h → ∀ q₀ ∈ V.Pools,
(P.eval q₀ : ℚ) = V.entCensus (writeHeights i.1.1 h) β₀ q₀`.
(EntU ⟹ the common P also witnesses EntCount at every ε̊[h] on c — a
one-line corollary in this file.)
moves_ref: "(ENT-U) …: over each listed linear set c of H(ε̊) …, I^ent,
viewed across the instantiations ε̊[h] with h ∈ c, is ONE polynomial CONSTANT
in h on c — [2b] M4b's h_ent-constancy clause, never assumed here" (V.3(iii)).
deps: Defs, V3-5. sketch: def. hyp_fields: (ENT-U) (owner [2b] M4b).

**V3-9c `init_rat` · `V3_initrat.lean` · medium — RESTATED (C23/A-1(3));
DOUBLE-COUNT KILLED at REV 3 (Codex-8/F-2: countT interpolates the CENSUS
polynomial and geom is the WEIGHT-ONLY Gent — the count enters exactly
once, and INIT-RAT is a THEOREM under its displayed burdens, no longer
pre-decided by a count-bearing package field).** ROSTER (2):
(a) `initRat_comp (XsEnt : XHDsEnt …) (hEU : EntU …) (hEC : EntCount …)
(hA : AffEnt n) : ∀ β₀ (i : V.EntIx β₀), ∃ P : PolyGeom,
P.countT = the (ENT-U) common census polynomial of i (degree ≤ Went i) ∧
P.countS = 1 ∧ P.geom = XsEnt.Gent β₀ i (the WEIGHT-ONLY component height
sum, denominators in class) ∧ ∀ q₀ ∈ Pools,
((evalAt q₀ ⟨P.val, _⟩ : ℚ) : ℝ) = ιsh i q₀` — per (template, component):
I^ent_c(q) × Σ_{h∈c} q^{−A(ε̊[h])}, the inner sum geometric (AffEnt's
affine A + XHDsEnt's weight face), the count constant by (ENT-U) — EXACTLY
the fields `RatBurdens.ιP/ι_interp/ι_count/ι_countS_one/ι_degT/ι_degS`
demand, jointly satisfiable (ι_count: countT.eval = entCount = the census
at base ✓ since base ∈ c; ι_degT = Went with natDegree ≤ Went ✓ — gate B:
degree 2 ≤ 3); (b) `initRat_agg`: the displayed aggregate
ι_{e,(s,α)} = Σ_{ε̊} Σ_{c} I^ent_c(q)·Σ_{h∈c} q^{−A(ε̊[h])} ∈ ℚ(q) — finite
sum of (a)'s values (PolyGeom closure mini-lemmas, local to this corpus —
design-freedom slot (5) resolved: the closure route, no MovesS edit).
moves_ref: "INIT-RAT (BURDEN, GIVEN XHD on the shallow layer + (ENT-U)):
ι_{e,(s,α)} = Σ_{ε̊} Σ_{c ⊆ H(ε̊)} I^ent_c(q)·Σ_{h∈c} p^{−A(ε̊[h])} … hence
∈ ℚ(q); CITED by RS.2" (V.3(iii)).
deps: V3-8a/b, V3-9a, V3-9b, V0-3, V0-4 (the witness pattern).
sketch: per component: constant I^ent_c times the XHDsEnt geometric value;
finitely many components and templates. hyp_fields: XHD-s shallow + (ENT-U)
+ ENT-COUNT + M4a's affine-A face (`AffEnt`) — EXACTLY the V.1 ledger line
"INIT-RAT GIVEN XHD (shallow) + (ENT-U)"; supplies `RatBurdens.ιP/ι_interp`.

### Layer V4 — clauses (ii), (iv), (v) [15]

**V4-1 `act_no_entry` · `V4_act.lean` · medium — GUARD RESTORED (C15);
REV 4 (Codex-9): the guard now ALSO sits on ValA's `tgt_supported` FIELD
(V2-4(c)) — the theorem's premise and the hypothesis's premise match, and
inactive-source rows are formal junk at BOTH layers.**
(ii-a) NO-ENTRY, GIVEN ValA (whose `tbl_count`/`tgt_supported` fields carry
(iv)-POLY's correct valuation + the GUARDED landing tie), WITH the note's
active-source guard — REV 5 (the M-1 ripple: the entry's β/βc tie is now
EXPLICIT — the entry INTO the inactive target is the DATUM'S column):
`theorem no_entry (hVA : ValA …) (d : MoveData n C) {q₀} (hq : q₀ ∈ Pools)
(hact : V.activeState q₀ (toStepCells.symm d.src))
(hin : ¬ V.activeState q₀ (toStepCells.symm d.tgt)) :
(C.T d.s d.m d.o d.α d.tix).eval q₀ = 0` (tbl_count at d.tix + the guarded
tgt_supported kill the count; off-key columns are 0 outright by
`tbl_offkey`) — zero is claimed ONLY for active sources
(rev 1 demanded zero from inactive rows too — strictly stronger than the
note, which treats those rows as formal junk; struck);
+ `theorem iota_supp (hVA : ValA …) : ¬ V.activeState q₀ β₀ → ιval β₀ q₀ = 0`
(the entrance side has no source guard: ι is supported on Act by its
target) — DERIVABLE at REV 3 (Codex-15's under-hypothesization closed):
ιval = Σ_i entCount·evalAt Gent, and `ValA.ent_supported` (the V2-4(d)
field, the note's own "landing forces a concrete target state" at the
entrance layer) kills every census at the inactive β₀.
moves_ref: "(ii-a) NO-ENTRY — for every source active at q₀, every
table/kernel entry INTO a target inactive at q₀ evaluates to 0 there (a
landing forces a concrete target state), and ι of (iii) is supported on
Act_{q₀}" (V.1(ii)). deps: V2-4 (ValA), Defs 2.F.
sketch: at active source pick a realized (x, h) (zc_ne + act_size);
tgt_supported kills the count; tbl_count casts the zero to the polynomial
value. hyp_fields: ValA ((iv)-POLY's table-build burden beyond the gate
blocks) — the unit is GIVEN it per the V.1 ledger "(ii-a/b) GIVEN (iv)-POLY's
correct valuation".

**V4-2 `act_triangular` · `V4_tri.lean` · medium.**
(ii-b): ordering states active-first, the evaluated kernel matrix at q₀ is
block-triangular `[[A, 0], [C, D]]` — every active-source → inactive-target
entry vanishes (V4-1): stated on `MovesS.Kmat` at evaluation, matching
`MovesS.PoolHyp.inactive_vanish`'s shape. NO stochastic-chain reading: rows
are marked offspring rows ("chain" struck at rev 2) — the lemma is about
matrix zeros only. moves_ref: "(ii-b) DELETION COMPATIBILITY — ordering
states active-first, K_e(q₀) is block-triangular [[A, 0],[C, D]]: the
realized system at q₀ IS the A-block" (V.1(ii)). deps: V4-1, MovesS.Defs.
sketch: entry-wise from V4-1 through Kmat's dite sum. hyp_fields: same as
V4-1.

**V4-3 `act_agreement_stmt` · `V4_agree.lean` · easy (statement unit) —
PARAMETRIC at REV 6 (Codex5-30: rev 5's `deps: MovesS.Interfaces, V7-4c`
made the declared 95-unit build order CYCLIC — V4 builds before V7, while
V7's assembly consumes the V4 statement layer. The def never needed
V7-4c's OBJECTS, only their TYPES).**
(ii-c) ACTIVE-VALUE as the typed per-(n, q₀) check — the Prop this corpus
RECORDS, never proves — stated over PARAMETERS, not over the V7 instance:
`def ActiveValueAgree (T : MovesS.TableShape n) (M : MovesS.MeasuredSide T)
(RB : MovesS.RatBurdens T M) (hK : ∀ e, e ∈ Finset.Icc 1 n →
MovesS.KmatHyp T e) : Prop := ∀ q₀ ∈ finitely many empty-cell pools,
AVAgree-shaped agreement after cancellation` — via `MovesS.AVAgree` at
the PoolHyp built from the arguments; removability of det(I − D)(q₀) = 0
carried as the OKat membership hypothesis (MovesS's "(ii-c) PASS" gate
shape, verbatim consumption). The BINDING to the V7 instance is the
CONSUMER'S: V7-2a's `AVRec_Stmt L := ActiveValueAgree L.T L.M …`
instantiates the parameters at the ledger's own objects (V7 layer, after
V7-4). moves_ref: "(ii-c)
ACTIVE-VALUE — … the burden is AGREEMENT: at the finitely many q₀ with empty
cells, the symbolic ℚ(q)-solution's value component, after cancellation,
EVALUATES to the active-subsystem value" (V.1(ii)).
deps: MovesS.Interfaces ONLY (the cycle is broken; the build order is a
DAG again). sketch: def only. hyp_fields: (ii-c) itself —
"a finite per-(n, q₀) verification duty … exercised by RESUM-n3's wild-p
layer ([3]'s gate), recorded here as the clause's standing check, never a
blanket det ≠ 0 claim" (V.3(ii), finding 8: NO general theorem claimed).
SEAM SCOPE (REV 7, C13 — the built corpus SPLIT (ii-c) at ratification):
this unit's `ActiveValueAgree`/AVAgree shape is the ALL-ACTIVE-pool face
(`ReadOffBundle.read`, U-24b); the NON-all-active consumed pools now
carry the SEPARATE built burden `RS4Chain.legs_read` (LegAgree at
`B.βmeas` per consumed δ, GIVEN `hdet : DetHyp` — built Interfaces.lean
141–143, quantifier structure the field's own), which is OWNER [3]'s
wave-4 assembly duty with MovesT; MovesV supplies only the RatBurdens
entries/OKat memberships it reads (§4.2's legs_read row). V4-3 states
the [1v] citation form for ITS face only — nothing here quantifies
LegAgree/βmeas/consumedDeltas.

**V4-4 `kernel_row_hfree` · `V4_krow.lean` · easy.**
K_e's entrance-height-freeness BY TYPE + the no-division fence: the entry def
`Σ_{m,o} T·G` consumes no `hent` argument (a definitional lemma: the entry
function factors through (α, β) only) and no source-mass denominator (its Qq
numerator is a product, never a quotient by |α| — checked on the def's
shape). moves_ref: "K_e(q)_{(s,α),(s′,β)} := Σ_{m: s→s′} Σ_o T·G — NO
source-mass division … K_e is entrance-height-FREE: entrance heights ride in
ε (retained data, rev 4), hence in ι alone" (V.1(iv)).
deps: Defs, MovesS.Kmat. sketch: definitional. hyp_fields: none.

**V4-5 `step_row_eq` · `V4_step.lean` · medium — SIGNATURE FIXED (C16).**
The (iv) STEP display, GIVEN XHD-w + (U-A) + (XHD-u) + XHD-d/s — the XHDw
argument now EXPLICIT (rev 1 used `X.g` with no `X`; and (U-A) alone does
NOT identify the common mass with q^{−E(h)} — that identification is
XHDw.w_eq's): `theorem step_row (P : C15Pack) (X : XHDw) (U : XHDu)
(D : XHDd n S TE) (hTie : MDomTie V TE D) (Xs : XHDs) {αc βc} (mv) {q₀}
(x : S.Hist q₀ αc) (hzc : S.zc x) (hq : q₀ ∈ Pools) (j) :
HasSum (fun h : {h // comp-Mem j h} => (S.cntraw mv x h.1 : ℝ) *
X.g mv h.1 q₀) ((T : ℝ) * G_j)` — the height-resolved row Σ T(h)·g(h)
equals T·G: w_eq + (U-A) make g the common per-assignment mass at the fixed
history, (u-R) makes mass and count state-only, (u-T) makes T(h) = T; each
g-summand ALREADY conditional (no re-division — no |α| factor exists).
moves_ref: "UNIFORMITY CONSUMPTION, displayed at the product (rev 2 —
findings 2–3: T·G is NOT licit from XHD-w/d alone): the height-resolved row
is Σ_{h} T(h)·g(h) … = T·Σ_h g(h) is EXACTLY (u-T)" (V.1(iv)).
deps: V1-6, V1-2, V1-1, V1-3, Defs. sketch: pointwise congr to constant
count (realizedness across the component from V1-3(b)'s
`mem_chainCount_pos` at length 1 — the REV-4 one-way supply; base-point
valuation through `MDomTie.mdom_eq`); `HasSum.mul_left`; G := the length-1
XHD-s component value.
hyp_fields: XHD-w + (U-A)'s pack + XHD-u + XHD-d/s + MDomTie — VERBATIM the
ledger "(iv) measured faces GIVEN XHD-w + (U-A) + (XHD-u); resummed forms
also GIVEN XHD-d/s" (the tie is [1v]/[2b] coherence, displayed).

**V4-6a/b/c `part1_route` · `V4_part1A/B/C.lean` · m/HARD/m — SUITE
(REV 4, Codex-16: real unit IDs, assigned below); FULL SIGNATURE DISPLAYED
(C17).**
PART-1 by the rev-3 countable route; ALL premises now in the displayed
signature (rev 1 left (U-A)/XHD-d/s to the prose):
`theorem part1 (P : C15Pack) (X : XHDw) (D : XHDd) (Xs : XHDs)
(leg_a : Totality …) (leg_b : CtblAdd …) (leg_c : NullRem …)
(leg_d : FixedHeightExact …) : ∀ τ x q₀ ∈ Pools, V.activeState q₀ τ →
HasSum (fun ch : Σ c : DCellAll τ, {h // (cdom c)-Mem h} => μcellH …) 1`
— legs: (a) TOTALITY: outside the no-finite-height locus every source point
lies in exactly ONE digit cell (D4R.0 — keyed to MovesD's d4r0 apparatus;
`cellOfA` gives the assignment-level function, the leg lifts it to the
box level); (b) COUNTABLE ADDITIVITY of the conditional measure over this
countable partition; (c) NULL REMAINDER: the no-finite-height locus lies in
the decreasing intersection of height-≥-H strip cylinders with conditional
masses → 0 (typed: `Tendsto (stripMass H) atTop (nhds 0)`); (d) each
fixed-height block sums by C.1.5(1)'s conditional exactness. The four legs
are DISPLAYED structures in this file (Totality/CtblAdd/NullRem/
FixedHeightExact — typed field-by-field over §2.F's carriers).
moves_ref: "PART-1's route, displayed: (a) TOTALITY … (b) COUNTABLE
ADDITIVITY … (c) NULL REMAINDER … (d) each fixed-height block sums by
C.1.5(1)'s conditional exactness — together, the per-cell ratios over the
whole partition sum to 1" (V.3(iv), pass-2 finding 4: "mass 1 is NOT a
finite-pool identity"). deps: Defs, V0-3.
sketch: (d) gives per-(c,h) masses; (a)+(b) give the countable HasSum to the
total minus remainder; (c) kills the remainder; assemble by monotone limits
on nonneg terms. REV 4 (Codex-16): the split is PROMOTED to real units —
**V4-6a `part1_ctbl`** (the countable-partition HasSum from legs a/b/d,
medium, `V4_part1A.lean`), **V4-6b `part1_null`** (the remainder-null limit
from leg c + the monotone assembly bound, HARD, `V4_part1B.lean`),
**V4-6c `part1`** (the assembled theorem, medium, `V4_part1C.lean`) —
"V4-6" = the suite.
hyp_fields: the four legs VERBATIM (the ledger: "PART-1 additionally GIVEN
D4R.0 totality + countable additivity + the null no-finite-height remainder"
+ XHD-w's (U-A) face at fixed history + XHD-d/s) — every one in the
signature; leg (a)'s D4R.0 cite keys to MovesD (PROVED core) at the shape
layer but stays a premise HERE because the CTS digit-cell carrier is
abstract until V7-4a.

**V4-7 `part2_row` · `V4_part2.lean` · medium.**
PART-2, the marked offspring row: GIVEN PART-1's conclusion + the mark-count
data (each cell's eligible continuing marks, `emult` — the §2.H def over the
L5 eligibility data): `Σ_{m,o,β} T·G + terminal = 1 + surplus` with
`surplus := Σ_cells (emult c − 1)⁺·mass c ≥ 0` — the marked row counts each
branching cell once PER eligible continuing mark; NO substochasticity of THIS
row is stated anywhere (the lemma's conclusion is the equality, and a
separate lemma `part2_ge`: row sum ≥ 1 − terminal).
moves_ref: "(PART-2, the marked offspring row) the kernel row Σ T·G counts
each branching cell once PER eligible continuing mark, so Σ T·G + (terminal)
= 1 + (branch surplus) … possibly > 1: NO substochasticity is claimed"
(V.1(iv)). deps: V4-6, Defs 2.H. sketch: regroup the marked sum by cells;
emult-weighted count vs once-per-cell count. hyp_fields: PART-1's set +
the emult roster tie (§D4-R L5's multi-eligible cells — MovesD-keyed field).

**V4-8 `part2_n3_zero` · `V4_n3surplus.lean` · easy — PREMISE DISPLAYED (C18).**
At n = 3 the surplus vanishes IDENTICALLY: ROSTER (2): (a) the gate census:
`∀ cells in the V.6 rosters, emult ≤ 1` by `decide`; (b) the GENERAL lemma
WITH ITS TRUE PREMISE DISPLAYED: `theorem surplus_zero (hDC : DegCons T)
(h2 : ContTwo T) : ∀ …, emult c ≤ 1` where `ContTwo T : Prop := ∀ e τ o,
∀ μ ∈ (T.odata e τ o).mem, μ.continuing → 2 ≤ μ.size` — the note's own
argument premise ("two continuing clusters need sizes ≥ 2 + 2 > 3": a
CONTINUING cluster has size ≥ 2; DegCons's size_pos alone gives only ≥ 1 —
C18's finding); then omega (2 + 2 > 3). ContTwo at the gate rosters: decide.
moves_ref: "(At n = 3 the surplus vanishes identically — two continuing
clusters need sizes ≥ 2 + 2 > 3 … first possible surplus at n = 4. Verified
over the V.6 rosters.)" (V.1(iv)). deps: V2-9, DefsGate.
sketch: decide + omega. hyp_fields: ContTwo (a table-build roster law,
decide at gates; displayed premise generally — nothing silently claimed).

**V4-9 `rep_indep` · `V4_rep.lean` · medium.**
(iv)-REP GIVEN (U-A) + (u-R), as the checkable row-level clause:
`theorem rep_row (P : C15Pack) (U : XHDu) (hobs : ObsCheck (C.bd s)) :
∀ (x x' : reps of α) …, measuredRow x = measuredRow x'` — the WEIGHTED
(T·G)-row, not the cardinality row; `ObsCheck` is now the DISPLAYED §2.G def
over `BlockData.evalObs` (the per-species proviso "the species' evaluation
maps mention no observable outside the (a)/(b) generator list"), executed at
the gate blocks (V6-3b's (D2)-EMPTY check) and OPEN elsewhere.
moves_ref: "(iv)-REP … the measured row from x ∈ α is a function of (a) x's
twisted VAL.1 cell data and (b) x's relational strata … the row is
cell-constant PROVIDED the species' evaluation maps mention no observable
outside the (a)/(b) generator list. That proviso is a PER-SPECIES CHECK"
(V.3(iv)). deps: V4-5, V1-6. sketch: row entries via u_R_mass/u_R_cnt +
ObsCheck's factoring. hyp_fields: (U-A) pack + (XHD-u)(u-R) + ObsCheck (the
table-build per-species check; refuter JOINT-probe is Python evidence,
cited not claimed).

**V4-10 `meas_marked` · `V4_meas.lean` · medium — THE MARKED CARRIER
GAINS ITS READING LAW at REV 7 (C8, adjudicated: marked-space
disjointness is DERIVABLE, never hypothesized).**
(iv)-MEAS in the RETYPED (rev 3) marked-space form: each (m, o, β,
height-class) summand is a finite-level digit-cell union WITH the
continuation mark ADJOINED — a fiber of a finite-level map ON the marked
space. ROSTER (4): (a) `markReading` — THE READING LAW (C8's demanded
carrier law): the marked Σ-carrier `MStep` (cell × mark) carries the DEF
`reading : MStep → (m, o, β, height-class)` and a marked point's mark
DETERMINES its summand — reading is a FUNCTION of the point (the mark is
adjoined to the finite-level map; note verbatim: "a finite-level
digit-cell union … with the continuation mark ADJOINED", MOVES
8185–8197) — definitional on the Σ-carrier, displayed; (b) `MarkDisj` —
the DERIVED marked-space disjointness (the rev-4/5 HYPOTHESIS name, now
THIS lemma per the ruling): summands with distinct (m, o, β,
height-class) readings are pairwise disjoint IN THE MARKED SPACE — a
shared marked point would carry both readings, contradicting (a); one
proof, no premise beyond the carrier; (c) `MarkDisjT` — the terminal
twin, same derivation over the TermData reading; (d) the f-FENCE: as
f-events only the DIGIT CELLS are disjoint — the explicit
two-continuation instance where f-projections coincide (D4-R L5), so NO
ordinary-source disjointness is claimed (PART-2's whole point — the
derivation in (b) NEVER projects to f).
moves_ref: "every (m, o, β, height-class) summand is a measurable
sub-event of the MARKED source space {(f, η)} … with the continuation
mark ADJOINED to the finite-level map — and the summands are pairwise
disjoint IN THE MARKED SPACE; as f-events only the DIGIT CELLS are
disjoint. No ordinary-source disjointness is claimed anywhere"
(V.1(iv), MOVES 8185–8197).
deps: Defs 2.E/2.F, MovesD (L12/D4R.4 finite-level realization).
sketch: the Σ-carrier's projection IS the reading; disjointness from
the mark coordinate + `evt_disj_cell` at distinct
digit-cell keys; the equal-projection witness from L5's two eligible
(side, ψ) continuations. hyp_fields: XHD-d (height classes
listed); the L5 eligibility roster (MovesD-keyed field). NO MarkDisj
hypothesis exists any more (C8); the within-cell CARD step V7-6a1 needs
is the carrier [tie] `evt_disj_assign` (§2.F).

**V4-11 `hmc_typing` · `V4_hmc.lean` · medium — RE-KEYED TO THE PROCESS
SIDE at REV 4 (N-1: the rev-3 spec was UNSATISFIABLE — with count-keyed
exactness no false-HMC XHDd existed; Fable N-1's four-line proof. With
`Tgam`-keyed exactness (REV 7, C6 — the census is free at composites) and
FREE composite events the toy exists again).**
The HMC/HMCAug Prop shapes compile against NON-degenerate instances, BOTH
WAYS: (i) THE FALSE-HMC TOY — over V1-8a's StepSys, a `TmplEvents` with a
COUPLED composite: the 2-step template's `tevt`/`tinst` empty at the
product point (h₁, h₂) = (0, 0) while both one-step events are realized
there (the ⊇ direction of the factorization FAILS; all four TE ties hold
by decide — the coupling lives entirely in the free composite data, exactly
(HMC-AUG)'s "global cone inequality couples successive steps"), with the
`XHDd` listing dom(cons) = the coupled set: `HMC TE D` is FALSE, by decide;
(ii) V1-8b's toy, where HMC is TRUE — the kernel is a REAL hypothesis,
satisfiable both ways, provable neither;
(iii) THE SEPARATION WITNESS (NEW at REV 7, C4 — adjudicated; replaces
the FALSE rev-5/6 claim "¬HMCAug provable at this toy for every
refinement"): at the SAME coupled toy, `HMCAug S TE` is PROVED — the
refinement R with `B (intermediate cell) := Fin 2` reading WHETHER
h₁ = 0 (finitely-valued boundary data; `B := PUnit` elsewhere), refined
tail domains {h₂ ≠ 0} at the h₁ = 0 state and full at the h₁ ≠ 0 state,
`assign_cover` routing the first assignment by its reading, `RefEvents`
re-partitioning the toy's marked events accordingly, and EACH refined
composite domain FACTORS (decide-scale) — so the toy exhibits
¬HMC ∧ HMCAug: ONE round of 𝒞_n refinement restores the factorization,
exactly the note's HMC-AUG display (MOVES 8213–8221), and HMCAug is
STRICTLY WEAKER than HMC (V4-13 gives the converse direction);
+ the terminal-final signature
check: `Template.lastT` instances type against `HMC`'s quantifier (the
probe's step 2 is a literal instance BY TYPE); + the HONESTY REMARK,
recorded (from §2.G's underivability audit): the ⊆-flavored fragment at
single-step tails is derivable GIVEN the mark facts + tevt_last_iff — the
toy therefore couples ⊇, which is the note's open direction.
moves_ref: "(v) HMC — … OPEN KERNEL, displayed hypothesis … TERMINAL-
FINAL EXTENSION (rev 4 …): templates INCLUDE those whose FINAL step carries a
terminal outcome" (V.1(v), MOVES 8198–8213) + the HMC-AUG display
(8213–8221). deps: Defs 2.G, V1-8a/b.
sketch: two decide-scale toy models + the Fin-2 refinement construction.
hyp_fields: none proved ABOUT the CTS
instance; HMC itself OPEN (V.5(2)) — "until HMC closes, K_e(p)^k is NOT a
theorem about the process"; NO ¬HMCAug claim (its falsifiability is OPEN
— the note's predicted falsifier: R2's wall channel).

**V4-13 `hmcaug_of_hmc` · `V4_hmcaug.lean` · medium — NEW UNIT at REV 7
(round-6 G1: the ~30-line theorem was cited as recorded but had no
unit).**
`theorem hmcaug_of_hmc (TE : TmplEvents n S) (D : XHDd n S TE)
(hHMC : HMC TE D) : HMCAug S TE` — R := the identity refinement
(B α := PUnit; cellEq the evident equiv), RE := the transported TE
(boxEq := Equiv.refl; tevt_cover/tinst_cover via the singleton-roster
reduction of `refTmpls` at the identity — the displayed filterMap
computation), D' := D; HMC RE.TE' D' = hHMC up to the transport. The
vacuous-repair case, UNAVOIDABLE for any faithful encoding (§2.G note);
proves nothing about HMC and closes nothing — HMCAug is consumed by no
unit. moves_ref: the HMC-AUG display (MOVES 8213–8221; the conditional's
antecedent is empty under HMC). deps: Defs 2.G, V4-11.
sketch: ~30 mechanical transport lines. hyp_fields: HMC in the premise
slot (open kernel — the theorem is the implication, never its
antecedent).

**V4-12 `comp_naming` · `V4_naming.lean` · medium — RESTATED at REV 4 AT
THE NOTE'S EXACT QUANTIFIER (Codex-8: rev 3 quantified over EVERY
positive-affine E-family, but the note's sentence "refers to the actual XHD
weight system attached to the process. It does not quantify over every
possible positive-affine exponent family" — the ∀-E quantifier is STRUCK.
Fable round-3 §B independently found rev 3's version OVERTAKEN by N-1; both
verdicts land here).** The note's sentence, quoted exactly (V.4, MOVES
8596–8602): "Summing (COMP-h) over h ∈ H(γ) GIVEN XHD-d/s yields the
unfactored per-template series (COMP-hΣ) — always well-defined, no HMC. The
right side factors into ∏(T·G), i.e. (COMP-hΣ) upgrades to (COMP-Σ), IF AND
ONLY IF the whole-template domain factors stepwise with state-only
dependence — exactly (v) HMC, a displayed open hypothesis." ROSTER (4):
(a) `comp_upgrade (hHMC : HMC TE D) (X : XHDw) (Xs : XHDs) … :
Factorizes X D` — THE IF LEG, PROVED, at the FIXED system: `Factorizes X D
:= ∀ {α β} (m : S.Move α β) (γ : Template n S β) (q₀ ∈ S.Pools),
(Σ_{h∈dom(cons m γ)} gProd X (cons m γ) h q₀) = (Σ_{h₁∈dom(.last m)}
X.g m h₁ q₀)·(Σ_{h₂∈dom γ} gProd X γ h₂ q₀)` (HasSum-typed via V0-3) —
Fubini over the membership factorization HMC provides. Supplies V5-5.
(b) `def UpgradeOnlyIf (X : XHDw) (TE) (D) : Prop := Factorizes X D →
HMC TE D` — THE ONLY-IF LEG at the note's exact quantifier, a NAMED
STATEMENT with its status RECORDED: it is the note's claim ABOUT THE
PROCESS (where H(γ) is the realized domain of the actual splitting flow);
whether it is INTERFACE-derivable from the full tie set is OPEN and
CLAIMED NEITHER WAY — (b′) shows only that it is not a SUM-ARITHMETIC
consequence [REV 5, Fable G-1: this is the ONE status statement; the
rev-4 "NOT an interface-general theorem, by (b′)" over-read (b′) and
contradicted (b′)'s own record — struck here and in §0] — and NO unit
consumes it
(downstream needs only (a) + the hHMC tag: "until HMC closes, only
(COMP-hΣ) holds" is enforced by V5-5's explicit hypothesis, not by the
converse). It rides inside clause (v)'s kernel scope — never proved, never
assumed.
(b′) `sum_not_membership` — the MACHINE-CHECKED SUM-LEVEL COINCIDENCE
(why (b) is not a SUM-ARITHMETIC consequence and therefore cannot be
proved by V5-4/V5-5-style reasoning): two DIFFERENT listed sets with
IDENTICAL fixed-system weight sums — {(0,0),(1,0),(0,1),(2,0)} vs
{0,1} × {0,1} under E = h₁ + h₂: both sum to 1 + 2q₀⁻¹ + q₀⁻² =
(1 + q₀⁻¹)² at every q₀ (the E-value multisets {0,1,1,2} coincide;
membership does not) — norm_num/ring. Round-1 C19's coincidence content,
correctly placed. DERIVABILITY STATUS OF (b), recorded honestly (computed
at THIS revision): the naive lift of this coincidence to a full
interface instance DIES against `marks_chains` (the point (2,0) carries
no chain, so no_stray at a dom(cons) containing it is unsatisfiable), and
the inner-template clauses of `Factorizes` block the 2-step and the
tested 3-step arrangements — so whether (b) is interface-derivable from
the FULL tie set is OPEN and CLAIMED NEITHER WAY; nothing rests on it
((b) is consumed by no unit, and (v)'s conditionality is carried by
V5-5's explicit hHMC, not by the converse).
(c) `comp_upgrade_fails` — THE FENCE, RE-KEYED TO THE PROCESS SIDE (the
N-1 directive): at V4-11's false-HMC toy, the FIXED gate weight system's
identity FAILS (norm_num) — an instance where ¬HMC ∧ ¬Factorizes: no
unconditional upgrade theorem can exist, the hHMC tag is not vacuous.
SATISFIABLE AGAIN (rev 3's version had no false-HMC instance to stand on).
moves_ref: the V.4 sentence quoted above — the IF leg proved as (a), the
ONLY-IF leg carried as the recorded process-scoped statement (b) with its
interface status machine-checked at (b′)/(c); nothing weakened silently,
nothing over-quantified.
deps: V0-3, V1-1, V4-11, Defs 2.G. sketch: (a) HasSum.mul over the
factored domain; (b′)/(c) norm_num toys. hyp_fields: XHD-w/-d/-s data +
HMC in (a)'s premise slot (owner [2b] / open kernel) — hypotheses of the
lemma, displayed; (b) NEVER consumed.

### Layer V5 — COMP + the J tables [12]

**V5-1 `marked_event_census` · `V5_event.lean` · medium — RE-KEYED at
REV 4 (N-1 ripple: the (vi) marked event's carrier is now the PROCESS-side
`TmplEvents` (tevt/tinst, §2.G) paired with the entrance events — no
independent event object exists).**
The (vi) marked event, typed: the (ε, γ, h) event's carrier is the pair
(entrance mark family, per-mark tevt from the entrance-extended histories);
its MARK-INDEX family is FINITE per level and its level-N residue census is
finite (keyed to MovesD.D4R4_all at the entrance layer + `tinst`'s Finset
typing); the f-fibers are boxes, GENERALLY INFINITE — the event is a Finset
of (box-point, mark) pairs at each level, NEVER a Finset of f's; + the
census lemma AT REALIZED POINTS: card = Σ over marks of fiber cards —
GIVEN the named, displayed mark-fiber tie
`MarkFiberTie TE : Prop := ∀ γ {q₀} (x) (h), q₀ ∈ Pools → zc x →
TReal TE γ x h → ∀ N ≥ tmplLvl γ, (TE.tevt γ x h N).card = Σ over the
mark census of the per-mark fiber cards` — the note-DEFINITIONAL mark-fiber
structure of the (vi) display, typed as a GUARDED premise because tevt is
free data. HMC-SAFETY (the §2.G audit's pattern, re-run for this tie): the
guard is TReal of the COMPOSITE itself, so the four-line proof's (←) leg
cannot manufacture TReal(cons) to enter it, and the (→) leg gains nothing
beyond the already-recorded single-step-tail fragment — the kernel stays
open (any UNGUARDED version would re-prove HMC through no_stray; the guard
is load-bearing and mirrors the note's own scope "(COMP-h) at every
concrete ε and fixed h ∈ H(γ)").
moves_ref: "its MARK-INDEX family (the realized histories η) is FINITE per
level and its level-N residue census is finite (D4R.4); the f-fibers are
p-adic boxes, generally INFINITE (rev 2, finding 13 — never 'finitely many
f')" (V.1(vi), MOVES 8225–8232). deps: Defs 2.E/2.F/2.G,
MovesD.D4R4all_wrapper, V3-6. sketch: Fintype instances + double counting
(MovesD.mult_sum's idiom) under the tie.
hyp_fields: MovesD's proved apparatus + the TE mark facts (carrier ties) +
`MarkFiberTie` (the guarded (vi) structure tie — [1v]/[2b] seam-grade,
displayed; consumed by V5-2a/b/c and V5-4). REV 6 (Codex5-23): where the
entrance-mark census reads σ_sel against ψ-selections, membership is the
`SelMatches` DEF (§2.D) — definitional, no `SelRankTie` hypothesis
survives; E7/E8_rankInj cited for mark-distinctness.

**V5-2a `comp_h_one` · `V5_comphA.lean` · medium — REAL UNIT ID at REV 4
(Codex-16; the parent V5-2 dissolves into a/b/c).**
(COMP-h)'s ONE-STEP case at a fixed entrance mark: the counting-native
`(one-step event).card × normalization = cnt · q₀^{−E} × |Box|-power` at
stabilized levels — evt_card + (U-A) at the fixed history + w_eq.
moves_ref: "(COMP-h) at every concrete ε and fixed h ∈ H(γ): μ̂(marked
event of (ε, γ, h) at p) = ι_{e,ε,β₀}(p) · ∏_{i=1}^k [T·g](p)" (V.1(vi)).
deps: V5-1, V1-6, V4-5. hyp_fields: XHD-w (`w_eq` — the q^{−E}
identification this unit's display consumes; REV 5, Codex-9: the frozen
COMP-h ledger reads "XHD-w's (U-A) face + (XHD-u)", and V4-5's dependence
does not discharge ITS open XHD-w argument) + (U-A) pack (§C/HC-2) +
(XHD-u) (owner [2b]).

**V5-2b `comp_h_step` · `V5_comphB.lean` · HARD.**
THE INDUCTION STEP along γ through `ext`: each step contributes cnt·g by
(U-A) at the fixed history + (u-R) across the histories reaching βᵢ —
REV 4: the per-mark fiber decomposition at REALIZED points rides V5-1's
census lemma (the (COMP-h) scope guard: h ∈ H(γ), supplied by no_stray →
0 < Tgam → `treal_iff_tgam` → TReal — REV 7, C6); the count positivity
along the chain from V1-3(b). NO unguarded
composite recursion is consumed (none exists — §2.G).
deps: V5-2a, V5-1, V1-3, V2-5. hyp_fields: as V5-2a + XHD-d (the scope
guard's face).

**V5-2c `comp_h` · `V5_comphC.lean` · medium.**
(COMP-h) ASSEMBLED, GIVEN XHD-w's (U-A) face + (XHD-u), ε concrete and h
FIXED in H(γ): `μ̂N (markedEvent ε γ h) q₀ N = ιN ε β₀ q₀ N * ∏ i, (T_i *
g_i(h_i))` in counting-native form (exact at stabilized levels, the MovesC
idiom) — group by entrance mark (V5-1), multiply out (V5-2a/b).
moves_ref: as V5-2a + the V.4 route "Group the marked event by its entrance
prefix … Per entrance mark, the continuation mass along γ at h is the
C.1.5 conditional chain". deps: V5-2a/b, V3-6.
hyp_fields: XHD-w (`w_eq` — REV 5, Codex-9: the frozen COMP-h ledger reads
"XHD-w's (U-A) face + (XHD-u)"; rev 4 listed only the pack and left the
open XHD-w argument to V4-5's dependency, which does not discharge it) +
(U-A) pack (§C/HC-2) + (XHD-u) (owner [2b]) + `MarkFiberTie`
(V5-1's guarded structure tie) — VERBATIM V.4's GIVEN plus the typed
carrier tie the free process data makes explicit; "at a FIXED path height
point AND one fixed entrance history, the identity consumes only (U-A)'s
§C-derivable content" is the V6-4 gate's per-history face.
*(Legacy ID note: "V5-2" = the a/b/c suite.)*

**V5-3 `comp_h_count` · `V5_shadow.lean` · medium.**
The COUNT SHADOW: `Ĉ_{ε,γ}(q) = I^ent_{ε,β₀}(q)·C_γ(q)` at the same concrete
ε — the same grouping at the count layer, GIVEN VAL(b)'s (XHD-u) count face +
ENT-COUNT; degree ≤ W̄(ε,γ) = W_ent(ε) + W(γ); + the FENCES as typed
non-lemmas: never |β₀| without the displayed per-family theorem, never summed
raw across ε with different A(ε) (the aggregation lemma V5-6 takes masses
ONLY). moves_ref: "the FULL realization count is PER (concrete) ENTRANCE
SHAPE: Ĉ_{ε,γ}(q) = I^ent_{ε,β₀}(q)·C_γ(q) (same (XHD-u) tag, plus
ENT-COUNT), degree ≤ W̄(ε,γ) = W_ent(ε) + W(γ) — the entrance factor never
omitted" (Thm VAL(b)). deps: V2-5, V3-9a, V5-2c's grouping.
sketch: count-layer replay of V5-2. hyp_fields: (XHD-u) + ENT-COUNT.

**V5-4 `comp_hsum` · `V5_comphs.lean` · medium.**
(COMP-hΣ), GIVEN XHD-d/s, NO HMC: `HasSum (fun h : {h // (dom γ).Mem h} =>
μ̂(ε, γ, h) q₀) (ι_{e,ε,β₀} q₀ * Σ_{h∈H(γ)} ∏ (T·g(h_i)))` — the unfactored
per-template series, well-defined via V0-3 over the listed disjoint
components. moves_ref: "(COMP-hΣ) GIVEN XHD-d/s, NO HMC (rev 2, finding 11
— the unfactored height sum carries its OWN name)" (V.1(vi)).
deps: V5-2c, V0-3, V1-4. sketch: sum V5-2c over h; `HasSum.mul_left`.
hyp_fields: XHD-d/s + V5-2's set.

**V5-5 `comp_sigma` · `V5_compsig.lean` · easy.**
(COMP-Σ), GIVEN additionally HMC: the V5-4 value factors to
`ι · ∏ (T·G)_i` — by V4-12(a)'s upgrade direction. moves_ref: "(COMP-Σ)
GIVEN additionally (v) HMC — the factored form" (V.1(vi)).
deps: V5-4, V4-12. sketch: rewrite. hyp_fields: + HMC (OPEN kernel; the tag
rides — every consumer of this unit carries `hHMC`).

**V5-6 `comp_agg` · `V5_compagg.lean` · medium.**
(COMP-AGG), GIVEN (COMP-Σ) + (iii) + (iv)-REP: summing over instantiations
ε̊[h] (the V3-5 bijection) then templates (V3-4 finite):
`Σ_{ε̊} Σ_{h∈H(ε̊)} (COMP-Σ at ε̊[h]) = ι_{e,β₀} · ∏ (T·G)` — entrance
heights EXACTLY ONCE; the common continuation factor pulled out by (iv)-REP
(the ONLY site invoking it, per ENT-AGG's fence); counts do NOT aggregate
(no count analogue stated — distinct A(ε)).
moves_ref: "(COMP-AGG) summing (COMP-Σ) over entrance heights (via the
instantiation bijection) then over templates ε̊ via ENT-AGG (licit by
(iv)-REP): … = ι_{e,β₀} · ∏ (T·G) — masses aggregate, counts do NOT"
(V.1(vi)). deps: V5-5, V3-8, V4-9, V3-5.
sketch: factor the constant continuation out of the double sum; ENT-AGG.
hyp_fields: HMC + XHD set + (iv)-REP's set (union of the deps' ledgers —
displayed in the theorem's signature, nothing implicit).

**V5-7a `jcells_once` · `V5_jdef.lean` · easy — ROUTE-KEYED (F-6; C8's
outcome keying kept).**
J's defining laws over the §2.H REV-3 carrier: `Jval` sums EACH CELL ONCE
(a `Finset.sum` over `bcells s m o α`, no mark index — definitional lemma:
`Jval` factors through the cell SET); the roster tie `bcells = ALL cells iff
route = split, ∅ otherwise` is a FIELD (roster_tie — the (K-SUB) OUTCOME
classification, F-6's repair); at the n = 3 gate rosters the route instance
is `decide` AND the gate NONZERO check is a named lemma: the root's m_2+1
outcome is split-route with a nonempty roster and Jval ≠ 0 there (norm_num
over the gate data — F-6's acceptance test); + REV 5 (Codex-10) the
definitional lemma `jval_out : ∀ d d' : MoveData n C, d.s = d'.s → d.m ≍
d'.m → d.o ≍ d'.o → d.α ≍ d'.α → Jval J cp XsC d q₀ = Jval J cp XsC d' q₀`
— Jval factors through the OUTCOME quadruple (s, m, o, α): no J object
reads `tgt`/`tcell`/`hc` (rfl-level after unfolding; the ≍ are the
dependent-eq transports along d.s = d'.s). moves_ref: "J_{τ,o}(q) := the
CELL-LEVEL resummed branching mass — the sum, over the branching digit
CELLS of outcome class o at state τ, of the XHD-resummed conditional cell
mass …, EACH CELL ONCE. [o branching := the (c ≥ 1, m ≥ 2) row of (K-SUB)'s
(m, c) CLASSIFICATION]" (§S-RESUM S.0, the CL-18 display; owner-side record
per the PLAN-SYNC flag). deps: Defs 2.H, DefsGate. sketch: definitional +
decide + norm_num. hyp_fields: none (def-layer).

**V5-7b `j_rat` · `V5_jrat.lean` · medium — PER-(τ,o) (C8); OUTCOME-LEVEL
QUANTIFIER at REV 5 (Codex-10: the frozen `RatBurdens.jP/j_interp` are
indexed by EVERY (e, τ, o) split outcome WITHOUT a chosen continuing
target, while rev 4 quantified `∀ (d : MoveData … with route = split)` —
a datum carrying tgt baggage and, for multi-continuing splits, a target
CHOICE the frozen field never makes).**
(J-RAT) = CL-18, the deliverable, quantified over the BARE OUTCOME INDEX:
`theorem jRat (J : JCells …) (XsC : XHDsC …) (hcell : CellPolyPack …) :
∀ (s) (m) (o : (C.bd s).Outc m) (α) (hr : J.route s m o = .split),
∃ P : MovesS.PolyGeom, P.degBoundT = Wloc ∧
P.degBoundS = Wstate ∧ ∀ q₀ ∈ Pools, ((evalAt q₀ ⟨P.val, _⟩ : ℚ) : ℝ)
= Jval J hcell XsC ⟨s, m, o, J.route_cont s m o hr, α⟩ q₀` — the datum
is BUILT from the quadruple through `J.route_cont` (§2.H's OWN field:
split ⟹ c ≥ 1 ⟹ cont — REV 6, Fable G-C: rev 5's display attributed a
phantom corollary `cont_of_route` to `(C.bd s)`, which has no `route`
field and cannot see J; the field's type IS the needed implication, so
the phantom name is struck and the field consumed directly), and the value
factors through the quadruple by V5-7a's `jval_out` (tgt enters nowhere) —
so the supplier produces the frozen per-(e, τ, o) field EXACTLY, split
outcomes with ANY number of continuing members included. J_{τ,o} ∈ ℚ(q)
ENTRYWISE, "a deliverable BEYOND
PART-1's TOTAL cell-partition mass"; supplies `RatBurdens.jP/j_ok/j_interp/
j_degT/j_degS` at MovesS's ∀ (e, τ, o) quantifier through V7-3a's roster
equivalence. THE PER-CELL CLAUSE (NEW at REV 7, C15 = Fable CRIT-2 —
the BUILT RatBurdens additionally REQUIRES `jPCell/jcell_ok/jcell_interp/
jcell_sum`, Defs.lean 386–395, and the rev-6 aggregate-only plan FAILED
BY TYPE): `jRat_cell : ∀ (s m o α) (hr : route = .split)
(c : V.DCellO s m o α), ∃ Pc : MovesS.PolyGeom, Pc = jcellPG c (§2.H:
countT := hcell.P … c, countS := 1, geom := the Σ_j Gcell value) ∧
∀ q₀ ∈ Pools, evalAt Pc.val = μcellVal hcell XsC … c q₀` — the per-cell
eval IS `M.μcell` at the V7-4c instance (rep-quantified, split-guarded:
jcell_interp's exact shape) — PLUS the SYMBOLIC fiber sum `jRat_sum :
∑ c ∈ bcells s m o α, (jcellPG c).val = (the jRat aggregate P).val`
(jcell_sum's shape; `Finset.sum` over the same roster Jval sums, so the
identity is PolyGeom-closure algebra over V5-7a's cell set). CellPolyPack
is thereby WIRED INTO the per-cell J supply — no parallel type is the
deliverable; V7-5a leg (b) transports both clauses to `M.Cell` through
`dataOf`. NO DOUBLE COUNT (Codex-9's second horn closed): Jval's cell
mass is ALREADY count-polynomial × weight-only-Gcell (§2.H's μcellVal), so
jRat multiplies nothing again — P.countT collects the cells' count
polynomials, P.geom the weight sums; and (J-RAT) is a genuine theorem-under-
burdens, not decided by a count-bearing package field (Codex-8's pattern,
avoided at the cell layer too). moves_ref: "its ℚ(q)-membership is the NEW
NAMED burden (J-RAT) (owner [1v]/[2b]: cell-level counts polynomial per the
(iv)-POLY pattern, XHD-s height sums)" (S.0/CL-18).
deps: V5-7a, V0-3, V1-4. sketch: per cell: count polynomial (CellPolyPack) ×
the weight-only XHDsC value; finite cell sum; PolyGeom closure (V3-9c's
mini-lemmas). hyp_fields: XHD-s cell face ([2b]'s height-sum face) +
`CellPolyPack` (the per-cell count polynomials — [1v]'s own OPEN face beyond
the gate blocks; at the gate blocks discharged by V6 data).

**V5-7c `j_not_marked_tg` · `V5_jfence.lean` · easy — ALGEBRA RE-KEYED
(F-6's tail: the "(J + surplus = marked row)" identity holds only for the
ALL-CELLS-ONCE J, which the REV-3 carrier now is).**
THE J-FENCE, machine-checked: on any split-route roster whose cells each
carry ≥ 1 continuing mark (the (c ≥ 1) classification's cell-level face — a
DISPLAYED roster premise), marked row Σ T·G = J + surplus with surplus =
Σ (emult − 1)⁺·mass; with a multi-eligible cell (emult c = 2) the marked row
STRICTLY EXCEEDS the once-per-cell J-sum; at the n = 3 gate rosters they
coincide (surplus ≡ 0, V4-8, and the roster premise holds by decide) — BOTH
directions stated, so no consumer can conflate the objects. moves_ref: "This
is NOT the marked per-continuing-branch T·G (rev 2, pass-1 finding 1: … a
T·G-sum would multiply-count the cell)" (S.0). deps: V5-7a, V4-7, V4-8.
sketch: toy 2-mark cell instance + the n = 3 decide. hyp_fields: the
displayed roster premise (gate: decide; general: the (K-SUB) cell-level
face, a table-build item).

**V5-8 `cell_refine` · `V5_cellrefine.lean` · medium — NEW at REV 3 (F-4 +
Codex-9: rev 2 carried this as an XHDsC FIELD equating count-bearing cell
sums with the count-free template sum — forcing T ≡ 1, the (q−1)²
adversary. It is neither a field nor false: with the counts displayed it is
a DERIVED identity).** `theorem cell_refine (hVA : ValA …) (U : XHDu)
(DC : XHDdC …) (D : XHDd n S TE) (hTie : MDomTie V TE D) (Xs : XHDs)
(XsC : XHDsC …) (hcell : CellPolyPack …) (d : MoveData n C) {q₀}
(x : S.Hist q₀ _) (hzc : S.zc x) (hq : q₀ ∈ Pools) :
∑ c, ((hcell.P d.s d.m d.o d.α c).eval q₀ : ℝ) *
  ∑ j, evalAt (XsC.Gcell d c j)
= ((C.T d.s d.m d.o d.α d.tix).eval q₀ : ℝ) *
  ∑ j', evalAt (Xs.Gc (.last (V.moveOf d)) j')` — the COUNT FACTOR ON BOTH
SIDES, displayed: cell count polynomials on the left, the table entry on the
right. ADVERSARY CHECK (F-4's acceptance): A2's one digit cell with count
(q−1)²: LHS = (q−1)²·G = TA2·G = RHS ✓ — no collapse; pool-consistently at
REV 4 (eval 2 = 1 vs eval 3 = 4 — the N-2 layer, §2.H). [+T twin over
GcellT/mdomT.] moves_ref: "by XHD-d's disjointness the finitely many
component sums ADD EXACTLY to the H(γ)-sum" (XHD-s) + the (iv)-STEP row
"Σ_h T(h)·g(h) … = T·Σ_h g(h) is EXACTLY (u-T)" (V.1(iv)).
deps: V2-4, V0-3, V1-2, V1-3, Defs 2.F/2.G/2.H. sketch: Fubini the double
(c, h)-sum over nonneg terms (HasSum rearrangement); pointwise
Σ_{c ∋ h} P_c.eval = Σ_c cntc = cntraw (CellPolyPack.count on the domain +
XHDdC exactness + the cntc/cntraw partition identity, definitional); then
cntraw(h) = T.eval across the domain — REV 4 route: u_T + V1-3(b)'s
`mem_chainCount_pos` (Mem → count > 0, the one-way supply) + tbl_count at
base through `MDomTie.mdom_eq` (Codex-5's tie, displayed premise).
hyp_fields: ValA + (XHD-u) + XHDd + XHDdC + MDomTie + XHD-s (template +
cell faces) + CellPolyPack — all displayed; supplies LedgerIV.kstep_one
through V7-6b.

### Layer V6 — gate V-n3, decide-native (the seal's displays re-derived) [10]

**V6-1a `rootTable_identities` · `V6_a1poly.lean` · easy.**
The five root closed forms + PART-1 count face AS POLYNOMIALS:
`TH3 + TH12 + TH3c + T21 + T3 = X^3` in ℚ[X] (`ring`), + each degree ≤ 3.
moves_ref: "PART-1 count face, displayed: (q³−3q²+2q)/6 + (3q³−3q²)/6 +
(2q³−2q)/6 + (6q²−6q)/6 + 6q/6 = q³ = pool. ✓" (V.6.1).
deps: DefsGate. sketch: ring/decide on coefficients. hyp_fields: none.

**V6-1b `rootTable_evals` · `V6_a1eval.lean` · easy.**
The PREDICTED EVALUATIONS table at the nine census q — all 45 entries + the
Σ = q³ row, `norm_num`/`decide` (values from V.6.1's table: m_H3 row
0,1,4,10,35,56,84,165,286; …; m_3 row = q). Includes the m_H3 = 0 at q = 2
falsifier as its own named lemma. moves_ref: the V.6.1 evaluation table +
"the m_H3 zero at q = 2 (a genuine falsifier)" (V.6.5).
deps: V6-1a. sketch: norm_num. hyp_fields: none.

**V6-1c `rootTable_census` · `V6_a1census.lean` · medium — NINE POINTS,
CHAR-FREE SKETCH (C20, A-4).**
THE COUNT SEMANTICS at ALL NINE census points: over each F ∈ {ZMod 2, ZMod 3,
F4, ZMod 5, ZMod 7, F8, F9, ZMod 11, ZMod 13} (the §2.I table fields for the
prime powers), classifying monic cubics z³+az²+bz+c by (root count, max
multiplicity): the five class counts equal the closed forms' values —
`decide` per point. MULTIPLICITY PREDICATE, char-free (A-4 repair — the
rev-1 `f″` test is FALSE at p = 2, where f″ ≡ 6x + 2a ≡ 0 marks every double
root as triple, at the m_H3 falsifier's own point): multiplicity of a root
r := the largest k ≤ 3 with `(z − r)^k ∣ f`, decided by direct coefficient
arithmetic (three explicit divisibility tests) — no derivative, no
discriminant, exactly the note's char-free root block.
moves_ref: "(A-side …) exhaustive enumeration over F_q at the nine census q
of all fresh assignments … CHECKED EXACTLY, zero tolerance" (V.6.5).
deps: DefsGate (incl. F4/F8/F9). sketch: decide over F³ per point with the
divisibility multiplicity. hyp_fields: none. [The rev-1 honest-scope split
(six primes in Lean, prime powers Python-sealed) is RETIRED: all nine points
are now in-kernel; the Python seal remains the historical record.]

**V6-2a `a2_domain_chart` · `V6_a2dom.lean` · medium — RE-KEYED (C3).**
The A2 height-domain normal form THROUGH THE CHART: ROSTER (3):
(a) `A2chart_image : A2chart '' {h | A2dom.Mem h} = {(h₀,h₂) : 1 ≤ h₂ ∧
3·h₂ < h₀ ∧ Odd (h₀ − h₂)}` — the note's realizability set IS the chart
image of the (t,u) linear set (omega both directions; parity via 2u+1);
(b) `A2chart_inj : Set.InjOn A2chart {h | A2dom.Mem h}`;
(c) one-component ⟹ the disjointness convention holds VACUOUSLY (a
`Pairwise` on a singleton list — stated). moves_ref: "realizability =
{h₂ ≥ 1 (vertex), h₀ > 3h₂ (hull strictness), h₀ − h₂ odd}; with h₂ = t ≥ 1,
h₀ = 3t + 2u + 1 (u ≥ 0) this is the ONE linear set L((4,1); {(3,1), (2,0)})"
(V.6.2). deps: Defs 2.A, DefsGate. sketch: omega. hyp_fields: none — the
gate "FIXES its heights and consumes no domain hypothesis" (an ILLUSTRATION
of XHD-d's format, exactly as displayed).

**V6-2b `a2_weight_table` · `V6_a2wt.lean` · easy — RE-KEYED (C3).**
The A2 weight, natural-coefficient form + the note's display re-derived:
ROSTER (3): (a) `EA2.eval ![t, u] = 6*t + 3*u + 1` (rfl-level; the
declaration IS in the chart) and the sealed point: `A2chart ![1,0] = ![4,1]`
∧ `EA2.eval ![1,0] = 7`; (b) THE DISPLAY IDENTITY, division-free:
`∀ h, 2 * EA2.eval h = 3 * ((A2chart h 0) + (A2chart h 1)) − 1` — the note's
"E = (3(h₀+h₂)−1)/2" re-derived THROUGH the chart as an ℕ-identity (omega);
no half-integral coefficient exists anywhere; (c) `TA2 = (X−1)²` with the
nine evaluations 1,4,9,16,36,49,64,100,144 and PART-1 `(q−1)² = pool` (one
letter). moves_ref: "g(h₀,h₂) = q^{−E}, E = (3(h₀+h₂)−1)/2 — affine,
positive weights. Sealed census height point: (4, 1): E = 7" + the
T = (q−1)² table (V.6.2). [REV 4, Codex-13: the "= 6t+3u+1" splice is
DELETED from this quotation — that string is OUR derived chart form (§2.I's
attribution record) and appears nowhere in the frozen note; it lives only
in the statement body, marked ours.] deps: DefsGate, V6-2a. sketch: omega/
norm_num. hyp_fields: none.

**V6-3a `blk2_table` · `V6_bpoly.lean` · easy.**
s_blk2 closed forms + PART-1: `Tsplit + Tinert + Tdbl = X·(X−1)` (ring);
char-2 recount equalities as polynomial identities ((q−1)(q/2 − 1) form =
Tsplit, (q−1)·q/2 = Tinert — the displayed convention: "the closed forms
below are the SAME polynomials under both"); degrees ≤ 2; Tw2 = X−1,
Tvv = (X−1)². moves_ref: "PART-1 count face: (q−1)(q−2)/2 + q(q−1)/2 +
(q−1) = q(q−1) ✓" + "(D2) … DISPLAYED exceptional-char convention; the
closed forms below are the SAME polynomials under both" (V.6.3).
deps: DefsGate. sketch: ring. hyp_fields: none.

**V6-3b `blk2_census` · `V6_bcensus.lean` · medium — NINE POINTS (C20).**
The m₂ outcome census at ALL NINE census points (ZMod primes + F4/F8/F9):
quadratics y² + wy + u with (u, w) ∈ Fˣ × F classified split/inert/double by
root count + multiplicity (the V6-1c divisibility predicate): counts =
(q−1)(q−2)/2, q(q−1)/2, q−1 — decide per point (char-2 points 2, 4, 8
exercise the exceptional-char convention IN THE FIELD, not by
interpolation); + the (iv)-REP count face: the classification is independent
of the source state t ∈ F_qˣ BY CONSTRUCTION in the Lean carrier (the count
sets don't mention t — the (D2)-EMPTY executed check, stated as a
definitional lemma), with the two-representative census duty recorded as
discharged-by-typing. moves_ref: "the s_blk2 rows identical at both
representatives ((iv)-REP)" (gate record) + "(D2) source generators: EMPTY —
none of the three letters' displayed evaluation maps reads t" (V.6.3).
deps: DefsGate. sketch: decide + rfl-lemma. hyp_fields: none.

**V6-4a `gateB_numbers` · `V6_gateB.lean` · easy — ROSTER ENUMERATED (C28).**
Gate B's dyadic arithmetic, every number displayed; ROSTER (4, each one
display): (a) `gateB_mass`: ι = 2·2⁻³ = 1/4, T_{o_double}(2) = 1, g = 2⁻³,
μ̂ = ι·T·g = 2⁻⁵ = 1/32; (b) `gateB_shadow`: count shadow I^ent(2)·T(2) =
2·1 = 2 + marked pairs 2^{3N−5}: N = 3 ↦ 16, N = 4 ↦ 128; (c)
`gateB_ledger`: A(ε) = 3, W_ent(ε) = 3, degree facts; (d) `gateB_ient_ne`:
I^ent = q(q−1) = q·|β₀| ≠ |β₀| (the displayed NOT-general instance, q ≥ 2 —
V3-9a's fence witness). moves_ref: "SEALED EXACT PREDICTIONS: μ̂(marked
event) = ι·T·g = (1/4)·1·(1/8) = 2⁻⁵ = 1/32 …; count shadow = 2·1 = 2" +
"note I^ent = q·|β₀| ≠ |β₀|" (V.6.4). deps: DefsGate. sketch: norm_num.
hyp_fields: none.

**V6-4b `gateB_two_histories` · `V6_gate2h.lean` · medium.**
The TWO-HISTORY DISCIPLINE, concrete at p = 2: the two marked entrance
histories (f̄ = z²(z+1) and f̄ = (z+1)²z over ZMod 2) BOTH land at the
same β₀ state (t = β̄ − ᾱ: 1 and −1 = 1 in ZMod 2), and their step reads
carry the SAME nominal inventory (E = 3λ as a function of the window shape
alone — stated as: the inventory function of DefsGate does not read the
recentering shift; evaluated equal for both histories) — hence T = 1 and
g = 2⁻³ per history BY DISPLAY, aggregate 2·2⁻³·(step factor); NO (XHD-u)
content consumed (the theorem's hypotheses list contains only the C15-shape
inventory data — auditable from the signature).
moves_ref: "(U-A) is applied PER HISTORY, separately … Both land at the SAME
β₀ state (t = 1 for z²(z+1); t = −1 = 1 at p = 2 …) and in EACH history's
branch frame the step read carries the SAME nominal digit inventory …
the commonality is DERIVED, not assumed" (V.6.4). deps: DefsGate, V1-6.
sketch: ZMod 2 arithmetic + inventory-function evaluation; decide/norm_num.
hyp_fields: the concrete inventory data (DefsGate) — no open kernel.

**V6-4c `gateB_threshold` · `V6_gateN.lean` · medium — PREMISE NOW AUDITABLE (C21).**
THRESHOLD N = 3, the derivation typed: GIVEN the coprime-factorization lift
(the typed premise `hensel : CoprimeLiftPack` — fields DISPLAYED at §2.I:
unique coprime lifting + coefficient determinacy, NOTHING stronger), level-3
data determine every event datum: h₀ ≡ 4 mod 8 (v(h₀) = 2 + unit digit at
level 3) and h₁ ≡ 0 mod 4 (v(h₁) ≥ 2) are level-3 predicates; box-precision
2^{3N−5} follows for all N ≥ 3 with ZERO event-word changes (the multiplier
lemma: each level adds exactly 2³ free digits). moves_ref: "THRESHOLD
N := 3, with the derivation displayed: … the coprime (Hensel) factorization
f = u·h lifts uniquely with h mod 2^k determined by f mod 2^k for EVERY k …
So level 3 determines every event datum" (V.6.4). deps: DefsGate, V6-4a.
sketch: mod-arithmetic on box coordinates; the lift pack supplies
determinacy; counting the free digits. hyp_fields: `CoprimeLiftPack`
(Mathlib-backed; if the exact form is missing, it becomes a DECLARED
published-axiom candidate per campaign §4 — flag at E-phase, do NOT silently
strengthen; NEVER an unconditional Lean axiom).

### Layer V7 — CTS-M assembly + the seam instances [20] (Codex-19/REV-4 splits: every former multi-lemma unit is now one display per unit; REV 7 adds V7-8/V7-9 — the W4-SYNC seam duties)

**V7-1 `ctsm_ledger` · `V7_ledger.lean` · easy (typing unit).**
THE PER-CLAUSE HYPOTHESIS LEDGER as ONE record (V.1's rev-2 finding-7 list,
verbatim — "each clause is asserted GIVEN exactly its listed set, nothing
less"): `structure CtsmLedger …` with one field per clause line: (i) the
BlockData family + computed lists at consumed skeletons; (ii) (ii-a/b) ←
ValA's (iv)-POLY ties, (ii-c) ← ActiveValueAgree at the ledger's OWN
(RB, hK) — REV 7, C9: `CtsmLedger` gains the DATA fields
`RB : MovesS.RatBurdens L.T L.M` and `hK : ∀ e ∈ Icc 1 n, KmatHyp L.T e`
(supplied at assembly by V7-5's instance and V7-3b/d), so AVRec/SolveCond
scope to the chain's own instance, never ∀-(RB, hK); (iii) primitives
free; ENT-AGG ← the XHD-s SHALLOW FACE `XHDsEnt` (its own X.sEnt
projection) + XHD-d shallow (REV 7, C7: `EntMassSummable` STRUCK — the
ledger line's "GIVEN XHD-s on the shallow layer" consumed VERBATIM, the
summability derived at V3-8a); ENT-COUNT
named; INIT-RAT ← XHD shallow +
(ENT-U) + AffEnt; (iv) ← computed tables / + (XHD-u) / + PART-1's four legs /
measured ← XHD-w + (U-A) + (XHD-u) / resummed ← XHD-d/s (+ cell face); (v)
OPEN + (HMC-AUG) separate [REV 6, Fable G-A scope; RE-SCOPED REV 7, C4:
"separate" = ledger-ROLE (its own named line item, never assumed, never
conflated) — NOT logical independence: HMC ⟹ HMCAug is the REAL UNIT
V4-13, and V4-11's coupled toy is the SEPARATION witness the other way
(¬HMC ∧ HMCAug — no ¬HMCAug claim survives anywhere); the ledger carries
NO HMC-typed conclusion field — every
displayed consumer (V7-2a's CompSigma/CompAgg/SolveCond Stmt's, V7-6c's
hmc leg)
takes HMC as an explicit ANTECEDENT]; (vi) ← per-identity sets + the
solve sentence's ESCAPE(E0)/(ii-c)/HMC/ENT-COUNT/INIT-RAT (REV 7, C5:
the solve's HMC antecedent displayed — MOVES 8005 + 8222–8224). REV-3
additions: the (J-RAT) cell
pack (`CellPolyPack`) and (ENT-U) ride as their own ledger fields (they are
consumed by the REV-3 defs, V7-4b/c), and the general table-build law supply
is the TYPED field `stage_laws : StageLawBurden n C` (V7-3d — Codex-20's
missing closed structure). REV-4 additions: the process-side carrier
`TE : TmplEvents n S` rides as ledger DATA (the (v)/(vi) clauses quantify
over it), and `MDomTie` rides as its own ledger field (the coherence
tie — Codex-5). [REV 7, C8: the rev-4/5 `MarkDisj`/`MarkDisjT` ledger
fields are REMOVED — the marked-space disjointness is V4-10's DERIVED
lemma and the within-cell card step is the carrier [tie]
`evt_disj_assign`; REV 7, C7: the rev-5 `EntMassSummable` field is
REMOVED — struck corpus-wide.] Every field TYPED to the §3 unit statements (no
Prop-placeholder fields for in-corpus content; owner-tagged packages for
[2b]/[3t]). moves_ref: "PER-CLAUSE HYPOTHESIS LEDGER (rev 2 — finding 7 …)"
(V.1). deps: all statement layers. sketch: record decl.
hyp_fields: the ledger IS the hypothesis inventory — nothing new.

**V7-2a `ctsm_conclusions_decl` · `V7_ctsmDefs.lean` · easy (Defs-layer
unit) — SPLIT (Codex-19) + CLOSED (Codex-18/C22).**
`structure CtsmConclusions (L : CtsmLedger …) : Prop` DECLARED CLOSED: one
field per ledgered deliverable, each field's type a named `*_Stmt` def of
this file, and each `*_Stmt` def is the VERBATIM ∀-closure of the named
unit's displayed conclusion (zero new content; the transcription rule is
normative). Fields (24): `syntax_partition : Part_Stmt L` (V2-3 at every
listed skeleton) · `val_a : ValA_Stmt L` · `val_b_chain : ValB_Stmt L`
(V2-5(b)) · `no_entry : NoEntry_Stmt L` + `triangular : Tri_Stmt L`
(V4-1/2) · `iota_supp : IotaSupp_Stmt L` · `active_value_recorded :
AVRec_Stmt L` (the (ii-c) Prop CARRIED, never concluded) · `ent_typing` +
`ent_agg_fin` + `ent_agg_full` (V3-1/2, V3-7, V3-8) · `ent_count_named`
(the Prop carried) · `init_rat` (V3-9c under its ledger set) · `step_row`
(V4-5) · `part1` (V4-6) · `part2` + `surplus_n3` (V4-7/8) · `rep` (V4-9) ·
`meas` (V4-10) · `comp_h` + `count_shadow` + `comp_hsum` + `comp_sigma` +
`comp_agg` (V5-2/3/4/5/6) · `solve_conditional` (the (vi) solve sentence as
the displayed implication with ESCAPE(E0)/(ii-c)/ENT-COUNT/INIT-RAT
premises, MovesS-typed) — (v) has NO conclusion field (it remains a LEDGER
field — open kernel). ALL 24 `*_Stmt` BODIES DISPLAYED (REV 5, Codex-17:
"the rest follow the same rule" concealed 21 transcriptions; the
quantifiers and hypothesis references are now auditable — L's fields are
the §2/V7-1 data, and each body is the named unit's displayed conclusion,
∀-closed over that unit's own binders):
```lean
-- NOTATION (binding): L : CtsmLedger carries the data (C, S, V, TE), the
-- XHD faces bundled as L.X (so L.D := L.X.d), cp : CellPolyPack, and the
-- burden Props; L.T := tableShapeOf L.C (V7-3a's def), L.M := the
-- V7-4a/b/c MeasuredSide defs at (L.V, L.X, L.cp); L.RB/L.hK := the
-- ledger's OWN RatBurdens/KmatHyp DATA (REV 7, C9 — V7-1); L.skels :=
-- the listed computed skeletons. `@…` marks the exact §3 display being closed over —
-- zero new content per the rule. EVERY free name below is either a §2 def
-- or an entry of the NAME→HOME table after the block (each declared as a
-- def in its home unit's file — all upstream of V7-2a in the build order).
def Part_Stmt (L) : Prop := ∀ s ∈ L.skels, ∀ (q₀ : ℚ), IsPP q₀ →
  (∀ x : (L.C.bd s).Carrier q₀,
     ∃! a : ∀ g : (L.C.bd s).Gen, ((L.C.bd s).gen g).idx,
     ∀ g, ((L.C.bd s).gen g).part q₀ x = a g) ∧
  Finite (∀ g : (L.C.bd s).Gen, ((L.C.bd s).gen g).idx)          -- @V2-3
def ValA_Stmt (L) : Prop := ValA n L.C L.S L.V           -- V2-4's structure
def ValB_Stmt (L) : Prop := ∀ {α} (γ) {q₀} (x : L.S.Hist q₀ α)
  (hzc : L.S.zc x) (hq : q₀ ∈ L.V.Pools)
  (h) (hmem : (L.D.dom γ).Mem h),
  (chainCount L.S γ x h : ℚ) = (pathProdPoly L.C γ).eval q₀      -- @V2-5(b)
def NoEntry_Stmt (L) : Prop := ∀ (d : MoveData n L.C) {q₀}
  (hq : q₀ ∈ L.V.Pools)
  (hact : L.V.activeState q₀ (L.V.toStepCells.symm d.src))
  (hin : ¬ L.V.activeState q₀ (L.V.toStepCells.symm d.tgt)),
  ((L.C.T d.s d.m d.o d.α d.tix).eval q₀ : ℚ) = 0                -- @V4-1
def Tri_Stmt (L) : Prop := ∀ e {q₀} (hq : q₀ ∈ L.V.Pools)
  (τ β : L.T.State e), L.M.activeState q₀ e τ →
  ¬ L.M.activeState q₀ e β → evalKmatEntry L e τ β q₀ = 0        -- @V4-2
def IotaSupp_Stmt (L) : Prop := ∀ β₀ {q₀} (hq : q₀ ∈ L.V.Pools),
  ¬ L.V.activeState q₀ β₀ → iotaVal L β₀ q₀ = 0                  -- @V4-1
def AVRec_Stmt (L) : Prop :=
  ActiveValueAgree L.T L.M L.RB L.hK                             -- @V4-3,
  -- CARRIED never concluded — SCOPED at REV 7 (Codex6-C9: the rev-6
  -- ∀-(RB, hK) closure demanded the finite agreement check at EVERY
  -- possible RatBurdens/KmatHyp package over the carriers — a silent
  -- strengthening; the note's (ii-c) is the check for THE actual
  -- table/solve instance). L.RB/L.hK are the ledger's own data (V7-1);
  -- V4-3 is PARAMETRIC (Codex5-30), so this reference stays downward.
def EntTyping_Stmt (L) : Prop := (∀ ε ε' : EntShapeV n, ε.selRec ≠ ε'.selRec
  → ε ≠ ε') ∧ (∀ ε ε', ε.template = ε'.template → ε.hent ≠ ε'.hent →
  ε ≠ ε')                                                        -- @V3-1/V3-2
def EntAggFin_Stmt (L) : Prop := ∀ (ε : EntShapeV n) {p F pol}
  [Fact p.Prime] [Field F] [Finite F]
  (cs : List (EntranceCut n ε p F pol)), CutsDisj cs →
  ∀ {N m} (Pr : MovesD.Presented p F n N m pol ε.Phat),
  iotaCount ε (unionCut cs) Pr = (cs.map (fun c => iotaCount ε c Pr)).sum
                                                                 -- @V3-7
def EntAggFull_Stmt (L) : Prop := ∀ β₀ {q₀} (hq : q₀ ∈ L.V.Pools),
  (∃ v : ℝ, HasSum
    (fun p : Σ i : L.V.EntIx β₀,
        {h // ((L.V.entDom p.1.1.1).comps.get p.1.1.2).Mem h} =>
      ιshH L.V p.1.1.1 p.2.1 β₀ q₀) v) ∧
  (EntU L.V → HasSum
    (fun p : Σ i : L.V.EntIx β₀,
        {h // ((L.V.entDom p.1.1.1).comps.get p.1.1.2).Mem h} =>
      ιshH L.V p.1.1.1 p.2.1 β₀ q₀) (iotaVal L β₀ q₀))           -- @V3-8a/b
def EntCountNamed_Stmt (L) : Prop := EntCount L.V                -- carried
def InitRat_Stmt (L) : Prop := ∀ β₀ (i : L.V.EntIx β₀),
  ∃ P : MovesS.PolyGeom,
  P.countT = entCountPoly L i ∧ P.countS = 1 ∧
  P.geom = L.X.sEnt.Gent β₀ i ∧
  ∀ q₀ ∈ L.V.Pools, ∃ hok : P.val ∈ OKat q₀,
    ((evalAt q₀ ⟨P.val, hok⟩ : ℚ) : ℝ) = iotaSh L β₀ i q₀        -- @V3-9c(a)
def StepRow_Stmt (L) : Prop := ∀ {αc βc} (mv : L.S.Move αc βc) {q₀}
  (x : L.S.Hist q₀ αc) (hzc : L.S.zc x) (hq : q₀ ∈ L.V.Pools)
  (j : Fin (L.D.dom (.last mv)).comps.length)
  (hok : L.X.s.Gc (.last mv) j ∈ OKat q₀),
  HasSum (fun h : {h // ((L.D.dom (.last mv)).comps.get j).Mem h} =>
    (L.S.cntraw mv x h.1 : ℝ) * L.X.w.g mv h.1 q₀)
  (((tblOf L mv).eval q₀ : ℝ)
    * ((evalAt q₀ ⟨L.X.s.Gc (.last mv) j, hok⟩ : ℚ) : ℝ))        -- @V4-5
def Part1_Stmt (L) : Prop := ∀ τ {q₀} (x : L.S.Hist q₀ τ)
  (hzc : L.S.zc x) (hq : q₀ ∈ L.V.Pools)
  (hact : L.V.activeState q₀ τ),
  HasSum (fun ch : Σ c : DCellAll L τ, {h // (cdomAll L c).Mem h} =>
    μcellH L x ch.1 ch.2.1 q₀) 1                                 -- @V4-6c
def Part2_Stmt (L) : Prop := ∀ τ {q₀} (x : L.S.Hist q₀ τ)
  (hzc : L.S.zc x) (hq : q₀ ∈ L.V.Pools)
  (hact : L.V.activeState q₀ τ),
  markedRow L τ x q₀ + terminalRow L τ x q₀ = 1 + surplusRow L τ x q₀
                                                                 -- @V4-7
def SurplusN3_Stmt (L) : Prop :=
  (∀ c ∈ gateCellRoster, gateMeas.emult c ≤ 1) ∧
  (ContTwo L.T → ∀ {s m o α} (c : L.V.DCellO s m o α), L.V.emult c ≤ 1)
                                                                 -- @V4-8
def Rep_Stmt (L) : Prop := ∀ αc {q₀} (hq : q₀ ∈ L.V.Pools)
  (x x' : {x : L.S.Hist q₀ αc // L.S.zc x}),
  measuredRow L x.1 q₀ = measuredRow L x'.1 q₀                   -- @V4-9
def Meas_Stmt (L) : Prop :=
  (∀ {αc q₀} (x : L.S.Hist q₀ αc) (N : ℕ) (p p' : MStep L.S αc x),
     p ≠ p' → Disjoint (mEvt L p N) (mEvt L p' N)) ∧
  EqualProjInstance L                                            -- @V4-10
  -- (mEvt = the MARKED event, a Finset of (box-point, mark) pairs —
  --  disjointness claimed IN THE MARKED SPACE only, by the mark
  --  coordinate; the second conjunct is the displayed two-continuation
  --  instance where the F-PROJECTIONS coincide — verbatim V4-10's two
  --  lemmas, jointly satisfiable)
def CompH_Stmt (L) : Prop := ∀ (ε : EntShapeV n) (β₀) {α}
  (γ : Template n L.S α) (h : Hpt γ.D) (hmem : (L.D.dom γ).Mem h)
  {q₀} (hq : q₀ ∈ L.V.Pools), ∀ N ≥ compLvl L ε γ,
  μhatN L ε β₀ γ h q₀ N
    = ιN L ε β₀ q₀ N * ((pathProdPoly L.C γ).eval q₀ : ℝ)
        * gProd L.X.w γ h q₀                                     -- @V5-2c
def CountShadow_Stmt (L) : Prop := ∀ (ε : EntShapeV n) (β₀) {α}
  (γ : Template n L.S α),
  cshadowPoly L ε β₀ γ = entCountPolyC L ε β₀ * pathProdPoly L.C γ ∧
  (cshadowPoly L ε β₀ γ).natDegree ≤ ε.Went + Wtmpl L γ          -- @V5-3
def CompHSum_Stmt (L) : Prop := ∀ (ε : EntShapeV n) (β₀) {α}
  (γ : Template n L.S α) {q₀} (hq : q₀ ∈ L.V.Pools)
  (hok : ∀ j, L.X.s.Gc γ j ∈ OKat q₀),
  HasSum (fun h : {h // (L.D.dom γ).Mem h} => μhatVal L ε β₀ γ h.1 q₀)
  (iotaEps L ε β₀ q₀ * ((pathProdPoly L.C γ).eval q₀ : ℝ)
    * ∑ j, ((evalAt q₀ ⟨L.X.s.Gc γ j, hok j⟩ : ℚ) : ℝ))          -- @V5-4
def CompSigma_Stmt (L) : Prop := HMC L.TE L.D →
  ∀ (ε : EntShapeV n) (β₀) {α} (γ : Template n L.S α) {q₀}
  (hq : q₀ ∈ L.V.Pools) (hok : ∀ j, L.X.s.Gc γ j ∈ OKat q₀),
  iotaEps L ε β₀ q₀ * ((pathProdPoly L.C γ).eval q₀ : ℝ)
    * ∑ j, ((evalAt q₀ ⟨L.X.s.Gc γ j, hok j⟩ : ℚ) : ℝ)
  = iotaEps L ε β₀ q₀ * stepProdVal L γ q₀                       -- @V5-5
def CompAgg_Stmt (L) : Prop := HMC L.TE L.D → ∀ (β₀) {α}
  (γ : Template n L.S α) {q₀} (hq : q₀ ∈ L.V.Pools),
  aggMass L β₀ γ q₀ = iotaVal L β₀ q₀ * stepProdVal L γ q₀       -- @V5-6
def SolveCond_Stmt (L) : Prop :=
  EscapeE0Rec L → ActiveValueAgree L.T L.M L.RB L.hK →
  HMC L.TE L.D →
  EntCount L.V → InitRat_Stmt L →
  MovesS.DetHyp L.T L.RB L.hK ∧ NeumannRec L L.RB L.hK           -- @V7-1's
  -- (vi) solve sentence, MovesS-typed — TWO REV-7 repairs: (C5) the HMC
  -- ANTECEDENT is displayed — the note's solve is "(COMP-Σ) additionally
  -- GIVEN (v)" (MOVES 8005) and "Until HMC closes, K_e(p)^k is NOT a
  -- theorem about the process and only the unfactored per-template sum
  -- (COMP-hΣ) holds" (8222–8224): the factored solve is HMC-conditional,
  -- typed so; (C9) the (RB, hK) quantifiers are the ledger's OWN L.RB/
  -- L.hK, never a ∀-closure. DetHyp is the frozen
  -- `(1 − Kmat …).det ≠ 0` ∀-e-in-Icc abbrev (built MovesS/Defs.lean
  -- 550–552 — cite refreshed, GAP-3)
```
NAME→HOME TABLE (binding — each name is a DEF declared in its home unit's
file, upstream of V7-2a; the transcription rule binds each body
token-for-token to its home display at E-phase): `evalKmatEntry` (V4-2:
the evaluated MovesS.Kmat entry at the instance) · `iotaVal`/`iotaSh`
(V7-4b's ιval/ιsh — restated as ledger-level defs in V3-9c's file for the
V3/V4 layer, one definition, two homes recorded) · `entCountPoly` (V3-9a:
the (ENT-U) census polynomial per EntIx member) · `CutsDisj`/`unionCut`
(V3-7: pairwise-disjoint cut families and their union cut) · `tblOf`
(V2-5: the datum's table polynomial `C.T … .tix` at a bare move through
`dataOf`) · `DCellAll`/`cdomAll`/`μcellH` (V4-6a: the all-outcomes digit
cell Σ-carrier, its Σ-embedded domain, the per-(cell, height) conditional
mass) · `markedRow`/`terminalRow`/`surplusRow` (V4-7) · `gateCellRoster`/
`gateMeas` (V4-8/DefsGate) · `measuredRow` (V4-9) · `MStep`/`mEvt`/`EqualProjInstance` (V4-10: the
marked Σ-carrier — cell × mark — its level-N MARKED event, and the
displayed two-continuation equal-f-projection instance) ·
`compLvl`/`μhatN`/`ιN`
(V5-2c: the stabilization level and the level-N counting-native masses) ·
`μhatVal`/`iotaEps` (V5-2c: the stabilized values) · `cshadowPoly`/
`entCountPolyC`/`Wtmpl` (V5-3: the count shadow, its entrance factor, the
template weight bound W(γ)) · `stepProdVal` (V5-5: ∏ᵢ Tᵢ.eval·ΣGᵢ over
the template's step decomposition) · `aggMass` (V5-6: the ε̊-and-height
double aggregate) · `EscapeE0Rec`/`NeumannRec` (V7-2a's own two
MovesS-typed record defs: the [3]-owned ESCAPE(E0) premise and the
ρ(A) < 1-at-pools/Neumann-convergence conclusion, each a def whose body
cites the named MovesS object — the two [3]-vocabulary items, present in
the type, inhabited by [3]). Every quantifier and premise above is
displayed and exhaustive for its field. moves_ref: the V.1 clause list.
deps: statement layers.
sketch: structure decl + Stmt defs. hyp_fields: none (typing unit).

**V7-2b `ctsm_given` · `V7_ctsm.lean` · medium — SPLIT (Codex-19).**
THEOREM CTS-M assembled: `theorem ctsM (L : CtsmLedger …) :
CtsmConclusions L` — apply each cited unit; assemble. The [1v]-COND capstone
of this corpus. moves_ref: "This note proves CTS-M's clauses EACH GIVEN
EXACTLY the hypothesis set displayed in V.1's per-clause ledger" (header).
deps: V7-1, V7-2a + cited units. sketch: apply; assemble.
hyp_fields: = V7-1's ledger, displayed in the signature.

**V7-3a `tableShape_inst` · `V7_ts.lean` · medium — SPLIT (Codex-19);
`odata` CONSTRUCTIBLE at REV 5 (Codex-2: rev 4's "member data from
DEG-CONS's tuples" named data that existed nowhere — DEG-CONS is a LAW
about an already-built odata; the §2.C member roster `omem` is the
carrier).**
The `MovesS.TableShape n` instance from `CtsFamily`: State e := block-e CTS
cells {(s, α) // skBlk s = e} (via `toStepCells` and §2.C's `skBlk`);
VType := `VLabel n` with `vEquiv := Equiv.refl`-keyed and `vdeg_spec` by
rfl; Out e ⟨s,α⟩ := Σ m : (C.bd s).Letter, (C.bd s).Outc m; THE odata MAP,
displayed:
`odata e ⟨s,α⟩ ⟨m,o⟩ := ⟨((C.bd s).omem m o).mapIdx (fun i mu =>
  ⟨mu.size, mu.δ, match hs : mu.status with
    | .inl v => Sum.inl (vEquiv.symm v)
    | .inr sk => Sum.inr (⟨sk, C.tcellM s m o ⟨i,_⟩ sk hs α⟩
        cast along (C.bd s).omem_size … hs : skBlk sk = mu.size)⟩),
  by simpa using (C.bd s).omem_ne m o⟩`
— sizes/δ verbatim from the roster, terminal statuses through the R20
vEquiv pin, continuing statuses = the member's target STATE (its roster
skeleton + its `tcellM` landing cell at the source α), total BY the
roster's own fields (`Outcome.hm` ← `omem_ne`); the (D4) designated
target is IN the roster BY `omem_sel` (REV 6, Codex5-22 — so the odata
image genuinely contains the selected member, at every continuing
outcome, multi-continuing splits included), and the kcol coherence with
V7-4c's kernel wiring is `tcellM_sel` (REV 7, C3 — the DESIGNATED
member's ∃-scoped landing tie; other members' tcellM values are their
own odata content, unpinned) (+ the derived
`omem_kcol` at single-member outcomes — §2.C, cited at
V7-6b); Wloc/Wstate transported; PLUS `route_eq` (the §2.H compatibility
law): JCells.route s m o = MovesS.routeOf (odata …) under this map —
F-6's classification is the seam's own (and `route_cont` matches
`routeOf`'s c ≥ 1 arm through `cont_iff`). moves_ref: "Downstream discipline
(plan REV 6): M2's τ, RS.0, RS.PRE, SQ.2 condition on CTS cells and on
NOTHING finer or coarser" (V.0) — the seam's one carrier.
deps: V2-*, V7-1, MovesSp. sketch: structure wiring; Fintype instances.
hyp_fields: the roster-coverage burden (CL-13) rides as the
BlockData-family argument.

**V7-3b `degcons_kmat_gate` · `V7_tsGate.lean` · easy — SPLIT (Codex-19).**
(a) `MovesS.DegCons` for the instance (V2-9 at the gate family; the general
instance GIVEN the CL-11 burden field); (b) `KmatHyp` AT THE GATE INSTANCE
by `decide` (a PROP about the roster — C25's correction stands).
moves_ref: DEG-CONS/CL-11 + the kcol column convention. deps: V7-3a, V2-9,
DefsGate. sketch: decide. hyp_fields: CL-11 beyond gates (in V7-3d's
StageLawBurden).

**V7-3c `scs_data_supply` · `V7_scsData.lean` · medium — SPLIT (Codex-19).**
The `SCSData` DATA supply: W/D/ℓ/g/μsel/W'/D'/flankCount/flankWidth/
resFactors/selIdx/memberOf from the MovesSp species stage fields (s.D, s.w,
s.W, s.sel, s.lam) through the roster wiring; the twelve LAWS decided AT THE
GATE ROSTERS (decide). moves_ref: the SP.2 stage laws (consumed).
deps: V7-3a, MovesSp, DefsGate. sketch: wiring + decide.
hyp_fields: none at gates; general = V7-3d.

**V7-3d `stage_law_burden` · `V7_stageLaw.lean` · medium — NEW TYPE
(Codex-20: the general SCSData/KmatHyp supply was an untyped prose burden).**
```lean
-- (the *Of functions below are V7-3c's DATA suppliers — W/D/ℓ/g/μsel/W'/D'/
--  flankCount/flankWidth/resFactors/selIdx/memberOf from the MovesSp
--  species stage fields; TS := tableShapeOf C. The law statements are the
--  VERBATIM MovesS.SCSData laws (the built MovesS/Defs.lean 97–139 —
--  line cite corrected at REV 5; rev 4 cited a stale pasted-source range)
--  with those data substituted — displayed in full at REV 4, Codex-14.)
structure StageLawBurden (n : ℕ) (C : CtsFamily n) : Prop where
  kmat_all : ∀ e, e ∈ Finset.Icc 1 n → MovesS.KmatHyp (tableShapeOf C) e
    -- [REV 5, Codex-13: SCOPED to the frozen solve interface's own
    --  quantifier `hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e` — rev 4's
    --  ∀-e form demanded KmatHyp at indices outside 1…n, strictly
    --  stronger than anything the note's roster laws supply]
  degcons_all : MovesS.DegCons (tableShapeOf C)          -- CL-11, full roster
  ℓpos : ∀ e (τ : (tableShapeOf C).State e) (o), 1 ≤ ℓOf C e τ o
  window_comp : ∀ e τ o, WOf C e τ o = e * ℓOf C e τ o + flankWidthOf C e τ o
  flank_zero : ∀ e τ o, flankCountOf C e τ o = 0 → flankWidthOf C e τ o = 0
  sel_mem : ∀ e τ o, (gOf C e τ o, μselOf C e τ o) ∈ resFactorsOf C e τ o
  res_sum : ∀ e τ o,
    ((resFactorsOf C e τ o).map (fun x => x.1 * x.2)).sum = ℓOf C e τ o
  memberOf_inj : ∀ e τ o, Function.Injective (memberOfOf C e τ o)
  memberOf_ne_sel : ∀ e τ o i, memberOfOf C e τ o i ≠ selIdxOf C e τ o
  sel_continuing : ∀ e τ o,
    MovesS.routeOf ((tableShapeOf C).odata e τ o) = .kcol →
    (((tableShapeOf C).odata e τ o).mem.get (selIdxOf C e τ o)).continuing
  stage_D : ∀ e τ o, D'Of C e τ o = e * gOf C e τ o * DOf C e τ o
  stage_W : ∀ e τ o, W'Of C e τ o = μselOf C e τ o
  cluster_parent : ∀ e τ o, WOf C e τ o * DOf C e τ o = e
  cluster_child : ∀ e τ o (i : Fin ((tableShapeOf C).odata e τ o).mem.length),
    (((tableShapeOf C).odata e τ o).mem.get i).continuing →
    i = selIdxOf C e τ o →
    (((tableShapeOf C).odata e τ o).mem.get i).size
      = W'Of C e τ o * D'Of C e τ o
```
+ `theorem stage_law_gate : StageLawBurden-restricted-to-gates` by decide.
A FIELD of `CtsmLedger` (V7-1); at gates discharged by V7-3b/c; beyond them
the [2a]-SP.2 stage-law burden, now a TYPE, not prose. moves_ref: the (i)
ledger line + CL-13. deps: V7-3a/b/c. sketch: structure decl + gate decide.
hyp_fields: itself (the typed open burden).

**V7-4a `measured_cells_inst` · `V7_msA.lean` · medium — SPLIT (Codex-19);
the `MovesS.MeasuredSide` instance is a theorem-under-data across
V7-4a/b/c: GIVEN V : CtsMeasured, X : XHD, cp : CellPolyPack (the [2b]
package + the [1v] cell-count face as EXPLICIT data — conditional exactly
as [1v]-COND is).** Cells/boxes/state half:
- pools: `Pools`/`pools_prime_pow`/`pools_closed`/`pools_infinite` ← V (C7);
- `Box/finB/boxpos` ← V; `State e` := block-e CTS cells;
- `Cell e τ := Σ o : Out e τ, DCellO (dataOf τ o)` (outcome-cell fibers;
  `cellOut` := the Σ-projection);
- **THE REPRESENTATIVE CARRIER — RE-KEYED at REV 5 (Fable M-3 = Codex-1,
  the convergent core: rev 4's `Rep e τ := {x // S.zc x}` left the pool
  index of the now pool-indexed `Hist` UNBOUND and could not produce the
  frozen POOL-GLOBAL `MeasuredSide.Rep : ∀ e, State e → Type`, whose
  consumers quantify (x : Rep) and q₀ INDEPENDENTLY). The PER-POOL
  REPRESENTATIVE FAMILY:**
  `Rep e τ := ∀ q₀, q₀ ∈ V.Pools → {x : S.Hist q₀ (cellOf τ) // S.zc x}`
  — one representative per pool, bundled; `rep_ne` ← Classical choice over
  pools from `zc_ne` (noncomputable witness, licit);
  **`cellEvt`, the DOUBLE dite (REV 6, Fable G-B: the frozen signature
  takes h : `Hgt = Σ D, Hpt D` — ONE global type — while the §2.F biUnion
  takes `Hpt (S.dim (moveOf d))`, so the pool dite alone left the on-pool
  branch ILL-TYPED at wrong-dimension heights; the DIMENSION dite is now
  displayed):**
  `cellEvt x c h q₀ N := if hq : q₀ ∈ V.Pools then
    (if hD : h.1 = S.dim (V.moveOf (dOf c)) then
      (§2.F biUnion at (x q₀ hq).1, at the height castHpt hD h.2)
     else ∅)
   else ∅`
  (`dOf c` = the cell's datum through `dataOf`; Classical.dec on the pool
  membership; the terminal twin `cellEvtT` carries the same double dite at
  `dimT`). BRANCH VALUES, each with its exact status:
  · wrong-dimension (either pool status): ∅ — FORCED: a mismatched-Σ-
    component h is ∉ HDom c (HDom is the Σ-EMBEDDED cdom, every member
    carrying the cell's own dimension), and the frozen `xhd_no_orphan` is
    UNGUARDED over ALL (q₀, N) (built Defs.lean 218–219), so any nonempty
    value (expressible via `boxpos`) would FALSIFY the law — the same
    junk-vs-forced dichotomy that rejected the Σ-typed Rep (slot 12);
    zero design freedom (inventory slot 15);
  · off-pool, h ∉ HDom: ∅ — FORCED (the same unguarded law);
  · off-pool, h ∈ HDom: ∅ — PERMITTED-AND-CHOSEN (REV 6, Codex5-26: rev
    5's "forced" overclaimed — the guarded laws read same-pool components
    only and say nothing here; `d4r0`'s off-pool instances hold trivially
    at ∅; the uniform ∅ is the recorded CHOICE, slot 12);
  · on-pool, matching dimension: the §2.F biUnion (the real content).
  CONCEPTUAL TYPECHECK WALK (the
  frozen instantiation, field by field): `Rep : ∀ e, State e → Type` ✓
  (pool-global by the Π); `rep_ne : ∀ e ∈ Icc 1 n, ∀ τ, Nonempty (Rep e τ)`
  ✓ (per-pool zc_ne witnesses + choice); `cellEvt : Rep e τ → Cell e τ →
  Hgt → ∀ (q₀ : ℚ) (N : ℕ), Finset (Box q₀ N)` ✓ (the double dite lands
  in the right Box fiber on ALL branches — G-B's ill-typed leg is gone);
  `LedgerIV.xhd_sum/meas_card/part1/
  rep_indep` (pool-GUARDED: q₀ ∈ Pools premises) read `(x q₀ hq)` — the
  SAME-pool history, so the V7-6 derivations proceed as displayed ✓ (their
  height quantifiers ride HDom membership, hence the matching-dimension
  branch);
  `xhd_no_orphan` (UNguarded) ✓ — THREE legs, all displayed (V7-6a1):
  on-pool matching-dimension: cntc = 0 → empty filter → empty biUnion;
  wrong-dimension: ∅ by the dimension dite at EVERY (q₀, N); off-pool: ∅
  by the pool dite; `d4r0` (unguarded) ✓ — off-key/off-pool/mismatched
  instances have at least one side ∅, disjoint;
- `dataOf/dataOfT` := the inverses of moveOf_bij/moveOfT_bij (one-line
  noncomputable defs, displayed here — Codex-18);
- `Hgt := Σ D : ℕ, Hpt D`; `HDom c` := the Σ-embedded listed `cdom`/`cdomT`;
- `cellLvl e τ c := V.stLvl (state of τ)`; `cellInst e τ c := V.stInst …` —
  THE F-5 REVERT: the STATE-instance census (the G4 pattern; rev 2's
  "stabilized level + cellEvt" line named fields that did not exist —
  Codex-16 — and the cell-instance keying broke cellP_deg/act_iff at both
  gates — F-5);
- `activeState` ← V.activeState (act laws ← act_size);
- `cellEvt x c h` := the §2.F biUnion def.
moves_ref: MovesS.Defs §2.B's intended-instance note: "the CTS cell space
over the level-N residue boxes of the O_δ theory (the MovesC counting
idiom), wave 4". deps: V7-3a, Defs 2.F, MovesD. sketch: field defs +
Fintype/Nonempty instances. hyp_fields: as in the header (data args).

**V7-4b `measured_entrance_inst` · `V7_msB.lean` · medium — SPLIT
(Codex-19); ENTRANCE SIDE at A-1's granularity, REV-3 census wiring.**
- `EntShape e τ := V.EntIx (cellOf τ)` — FINITE (`finE` ← V3-4 × list
  length); `Went i` := W(P̂) via the template (height-free, L3 rev 9);
- `entEvtH i h := V.entEvt (writeHeights i.1.1 h) β₀ …`; `ιDom i` := the
  Σ-embedded component; `ιshH i h` := the §2.G DEF (CENSUS·q^{−A} — F-1's
  corrected body); `ιsh i q₀ := (V.entCount i q₀ : ℝ) · evalAt
  (X.sEnt.Gent β₀ i)` (count × WEIGHT-ONLY sum — Codex-8's split);
  `ιval τ q₀ := Σ_{i : EntIx} ιsh i q₀`;
- `entCount i` := the §2.F CENSUS def (F-2); `entLvl i := V.entLvl i.1.1`;
  `entInst i q₀ N := V.entInst (writeHeights base) β₀ q₀ N` — so
  `LedgerIV.ent_count_card` is rfl-level AGAINST THE CENSUS (the ledger
  comment "the counting tie ι_count's polynomial now means the full count"
  is honored: ι_count's polynomial = the census polynomial, degree ≤ Went);
- `hent i := (writeHeights i.1.1 ((V.entDom i.1.1).comps.get i.1.2).base
  ).hentCode` — REV 4 (Codex-6, THIRD-round adjudication with the
  two-verdict record): the supplied value is UPGRADED from the rev-3 lossy
  base-coordinate SUM to the retained-tuple code (§2.D `hentCode`; REV 5,
  Codex-7 + Fable G-2: LENGTH-SEEDED — the zero-seeded fold collided
  across read counts — and the injectivity claim SCOPED: injective on the
  retained (h_r, γ_r)-tuple lists, which at this fixed-template
  consumption site separates the retained (h_r, u*_r) data via gamTie;
  "identifies distinct entrance heights" stays dead, and no blanket
  ∀-ε-injectivity is claimed). WHAT REMAINS STRUCTURAL AND STAYS SF-1: the frozen
  seam's `hent : EntShape e τ → ℕ` is ONE value per (template, component)
  INDEX while the note's h_ent(ε) is per CONCRETE ε — no per-index ℕ can
  carry the full family; the supplied code is the BASE instantiation's.
  TWO-VERDICT RECORD: Codex round-3 #6 called the scalar supply CRITICAL
  ("RS1Meas.βmeas and the W4 seam expressly use the h_ent : ℕ index");
  Fable round-3 §B re-verified SF-1 HONEST with computed evidence. THIS
  revision's own re-grep (2026-07-28): `hent` in the BUILT MovesS =
  the field declaration (Defs.lean 179), one device-instance assignment
  (N2Carriers.lean 118, `:= fun _ _ _ => 0`), one comment — NO law reads
  it; and `RS1Meas.βmeas`'s h_ent is its OWN independent ℕ ARGUMENT
  (Interfaces: the W2_xrb conclusion asserts βmeas's h_ent-INDEPENDENCE),
  not a read of `MeasuredSide.hent`. DISPOSITION: value upgraded (the
  faithful half of Codex-6 adopted); the binding rule stands — MovesT's
  wave-4 re-keying of βmeas's h_ent argument must bind to the Hgt-indexed
  carriers (ιDom/ιshH/entEvtH), never to `hent`; any future MovesS law
  reading `hent` re-opens this line item (SEAM FLAG SF-1);
- `markedVal` := the μ̂ totals (MuHat-wrapped at exit).
moves_ref: V.1(iii) + the A-1 granularity record. deps: V7-4a, Defs 2.D/2.F,
V3-4. sketch: field defs. hyp_fields: as in the V7-4a header.

**V7-4c `measured_values_inst` · `V7_msC.lean` · medium — SPLIT (Codex-19);
the measured ℝ-values, REV-3 count-polynomial wiring (F-4/F-5).**
- `gwt c h q₀ := ((cp.P … c).eval q₀ : ℝ) * X.w.g (moveOf …) h q₀` — count
  POLYNOMIAL × weight (x-FREE by construction, as MovesS's gwt signature
  demands; the count factor is the [1v] pack, the weight the [2b] monomial);
- `μcell x c q₀ := ((cp.P … c).eval q₀ : ℝ) * Σ_j evalAt (X.sC.Gcell … c j)`
  (x-free; count × weight-only component sums);
- `rowVal o q₀ := Σ_{c ∈ cells o} μcell c q₀` (for split routes this IS the
  J cell-sum — MovesS's own comment — via §2.H's roster_tie);
- `kstep 0 τ β q₀ := if τ = β then 1 else 0` — THE k = 0 CASE (NEW at
  REV 4, Fable N-3: `Template` has no length-0 constructor, so the rev-3
  template-sum def gave kstep 0 ≡ 0, falsifying the frozen `LedgerIV.hmc`
  at k = 0: kstep 1 = Σ_γ kstep 0 · kstep 1 forced kstep 1 ≡ 0, false at
  s_blk2's o_double row T_dbl(2) = 1. The Kronecker δ is the empty path's
  value — ∏T over no steps = 1, the empty height sum = 1 — and the frozen
  law at k = 0 collapses correctly: Σ_γ δ_{τγ}·kstep 1 γ β = kstep 1 τ β ✓.
  The built device instance documents the requirement:
  `MovesS/N2Carriers.lean` 101–105, "kstep 0 = 1 and the HMC scalar law
  kstep (k+1) = kstep k · kstep 1 holds"; kstep := (…)^k);
- `kstep (k+1) τ β q₀ := Σ_{γ : length-(k+1) kcol templates τ→β}
  ((pathProdPoly C γ).eval q₀ : ℝ) · Σ_j evalAt (X.s.Gc γ j)` — THE COUNT
  FACTOR RESTORED (F-4/Codex-11: rev 2 dropped ∏T; kstep_one then demanded
  T ≡ 1). THE ANTI-SMUGGLE PIN STANDS: kstep at k ≥ 1 is the measured
  k-step TEMPLATE mass (∏T × the unfactored template height sum), NOT the
  matrix-power recursion — LedgerIV.hmc stays V5-5's conditional content
  (the k ≥ 1 recursion given hHMC: regroup length-(k+1) templates as
  prefix∘last and factor by V4-12(a); the k = 0 instance is the δ-collapse
  above, hypothesis-free).
moves_ref: "K_e(q)_{(s,α),(s′,β)} := Σ Σ T·G" (V.1(iv)) + S.0's kstep row.
deps: V7-4a/b, V2-5 (pathProdPoly), Defs 2.G/2.H. sketch: field defs.
hyp_fields: as in the V7-4a header (X, cp explicit).

**V7-5a/b/c `ratBurdens_inst` · `V7_rbA/B/C.lean` · 3 × medium — REAL UNIT
IDs at REV 4 (Codex-16: the ⌿ split promoted — V7-5a = legs (a)+(b)
tgP/jP, `V7_rbA.lean`; V7-5b = leg (c) ιP, `V7_rbB.lean`; V7-5c = leg (d)
cellP + act_iff + the assembly, `V7_rbC.lean`); LEGS RE-KEYED (C23); leg
(d) REVERTED at REV 3 (F-5).**
`MovesS.RatBurdens T M`, theorem-under-hypotheses — GIVEN the open faces,
the burdens structure is inhabited: `theorem ratBurdens_exists
(hVA : ValA …) (X : XHD …) (hTie : MDomTie …) (hcell : CellPolyPack …)
(hEU : EntU …) (hEC : EntCount …) (hA : AffEnt n) :
Nonempty (MovesS.RatBurdens T M)` with the legs:
(a) `tgP` := ValA's count polynomials × the XHDs/XHDsC geometric values —
the G-BEARING FACE IS A PREMISE (C23), and via V5-8's cell_refine the
count-polynomial form matches V7-4c's rowVal;
(b) `jP` ← V5-7b (weight-only XsC × CellPolyPack — no re-multiplication,
Codex-9's second horn; per-(τ,o) incl. split routes via V7-3a's route_eq)
— AND, RE-KEYED at REV 7 (C15 = Fable CRIT-2: the BUILT RatBurdens
REQUIRES the per-cell J interface, Defs.lean 386–395; the rev-6
aggregate-only leg FAILED BY TYPE), the PER-CELL fields:
`jPCell e τ c` := V5-7b's `jcellPG` at the cell's datum (through V7-4a's
`Cell e τ = Σ o, DCellO` and `dataOf` — the tables target the EXISTING
carrier `M.Cell`, no parallel type); `jcell_ok` ← the PolyGeom OKat
clauses; `jcell_interp` ← V5-7b's `jRat_cell` (per-cell eval = μcellVal
= V7-4c's `M.μcell`, rep-quantified via the per-pool Rep family,
split-guarded via route_eq — the frozen field's exact shape);
`jcell_sum` ← V5-7b's `jRat_sum` (the symbolic cell-fiber sum = jP.val);
(c) `ιP` ← V3-9c(a)'s PER-COMPONENT PolyGeoms — same type as
`RatBurdens.ιP : ∀ e τ, EntShape e τ → PolyGeom` under V7-4b's EntIx keying
(the C23 aggregate-vs-per-shape mismatch is gone); ι_count = the CENSUS tie
(countT.eval = entCount, TRUE at degree ≤ Went under the F-2 re-key — gate:
deg 2 ≤ 3), ι_countS_one, ι_degT/ι_degS from V3-9c(a)'s clauses;
(d) `cellP` — REVERTED TO THE REV-1 sizeP WIRING (F-5: rev 2's
"CellPolyPack granularity fix" was a REGRESSION — digit-cell COUNT
polynomials violate the frozen `cellP_deg ≤ Wstate` at BOTH gate blocks
(Wloc 3 > Wstate 0 at the root; 2 > 1 at s_blk2) and make `act_iff` FALSE
at q₀ = 2 through the m_H3 empty cell, the blueprint's own falsifier;
round-1 C23 never named cellP): `cellP e τ c := sizeP (state of τ)` —
constant across the state's digit cells — satisfying all four frozen laws:
`cellP_deg` ≤ Wstate ✓ (sizeP's bound); `cellP_nonzero` ✓ (post-deletion
CellIdx); `cellP_count` ✓ ← `V.stInst_card` (the state-census card at stLvl
IS sizeP.eval — the G4 pattern; cellInst/cellLvl wired at V7-4a);
`act_iff` ✓ ← `act_size` (activity IS state-size nonvanishing; with cellP
constant in c the ∀-c iff collapses to act_size — and at q₀ = 2 the root
stays active while the m_H3 DIGIT cell is empty, contradicting NOTHING).
THE COLLAPSE'S NONEMPTINESS STEP, DISPLAYED (REV 4, Fable G-1: the ⟸
direction "∀ c, cellP.eval ≠ 0 → active" is vacuous at an empty cell type
unless `Cell e τ` is inhabited — rev 3 used the step silently): the roster
lemma `cell_ne_inst : ∀ e τ, Nonempty (M.Cell e τ)` — pick a zc history
(zc_ne), apply the REV-3 productivity `out_ne` (a realized continuing or
terminal fresh assignment exists), and classify it (`cellOfA`/`cellOfAT`
through `moveOf_bij`/`moveOfT_bij`): the assignment's digit cell inhabits
`Σ o, DCellO (dataOf τ o)` — one display, part of V7-5c's roster.
The rev-2 `ActIff` premise is DELETED (subsumed by act_size); CofinAct
rides where MovesS's R45/R50 keying needs it.
*(Legacy ID note: "V7-5" = the a/b/c suite.)* moves_ref: the
V.0 downstream line "[3] RESUM consumes K_e and ι_e from this note's clauses
only" + CL-6/CL-18/INIT-RAT ownership rows + MovesS R45/R50 ("EACH CELL SIZE
one polynomial of degree ≤ W_state(s)"; cellInst = "instance events whose
card IS the cell size"). deps: V2-4, V5-7b, V5-8, V3-9c, V7-4a/b/c.
sketch: assemble PolyGeoms; interp fields from the units' eval conclusions.
hyp_fields: (iv)-POLY beyond gate blocks (CL-13/CL-6) + (J-RAT)'s cell pack +
INIT-RAT's set — the STATED premises; nothing discharged silently.

**V7-6a1 `ledgerIV_cells` · `V7_livA1.lean` · medium — RE-SPLIT at REV 4
(Fable G-2: rev 3's V7-6a derived SIX fields against the ≤ 4-lemma roster
rule; now TWO units of three, each an enumerated roster). THE CELL SUITE:**
GIVEN V + X (with the dC face) + cp — REV 7 (C8, adjudicated): the
rev-4/5/6 premises `hMD : MarkDisj V`/`hMDT : MarkDisjT V` are REMOVED;
the within-cell biUnion-card step is the CARRIER [tie]
`V.evt_disj_assign`(+T) — C.1.5 counting semantics (distinct fresh
assignments, disjoint residue boxes), discharged at the real instance
like evt_card, NOT an open mark burden (the old "open exactly where
PART-2's surplus lives" reading conflated assignments with marks; marks
are invisible at this layer, §2.F record, and the note's marked-space
disjointness is V4-10's DERIVED lemma):
- `meas_card` (gwt·|Box| = |cellEvt| eventually): gwt = P_c·g by V7-4c's
  DEF; |cellEvt| = Σ_a |evtOf a| (V.evt_disj_assign within a continuing
  cell, V.evt_disj_assignT
  within a terminal one — the carrier [tie]s — since cross-cell/height
  needs nothing here); each |evtOf a| =
  massOf·|Box| eventually (V.evt_card); massOf = g (X.w.w_eq, zc-guarded);
  P_c.eval = cntc on the domain (cp.count + X.dC.no_strayC realizedness);
  the representative's history at the quantified pool is `(x q₀ hq)` —
  the REV-5 per-pool Rep family (V7-4a) — assemble;
- `xhd_no_stray`: h ∈ HDom → cntc > 0 (X.dC.no_strayC) → cellEvt nonempty
  for N ≥ stabLvl (evt_card with massOf = g > 0; the law is pool-guarded,
  so the dite's on-pool branch is in force);
- `xhd_no_orphan` (the UNGUARDED frozen ∀-q₀ law) — THREE legs (REV 6,
  Fable G-B: rev 5 displayed two and silently assumed the dimension leg):
  (i) at q₀ ∈ Pools, matching dimension — h ∉ HDom → cntc = 0
  (X.dC.no_orphanC contrapositive; the cntc = 0 step is stateable ONLY
  here) → the filter is empty → cellEvt = ∅ at EVERY N (definitional);
  (ii) at a MISMATCHED Σ-dimension (any q₀) — cellEvt = ∅ BY the V7-4a
  DIMENSION dite (a wrong-dimension h is ∉ HDom, so the law demands
  exactly this; inventory slot 15); (iii) at q₀ ∉ Pools (matching
  dimension) — cellEvt = ∅ BY the pool dite (inventory slot 12; the leg
  rev 4 assumed silently, displayed since REV 5). `d4r0`'s off-key
  instances ride the same three-leg case split (mismatched or off-pool:
  one side ∅).
moves_ref: the CL-5 nine-input ledger's counting faces (S.0). deps: Defs
2.F/2.G, V7-4a/b/c. sketch: as listed, field by field. hyp_fields: XHD
(w + dC faces) + CellPolyPack — displayed (REV 7, C8: MarkDisj/MarkDisjT
are GONE from this list; the card step rides the carrier [tie]s).

**V7-6a2 `ledgerIV_counts` · `V7_livA2.lean` · medium — the other half of
the G-2 re-split. THE DISJOINTNESS/CENSUS SUITE:** GIVEN V + X + cp:
- `d4r0` (cross-(c,h) disjointness incl. h ≠ h′, one x): `evt_disj_cell`
  at DISTINCT DIGIT-CELL KEYS — cross-cell (same h: the cellOfA key
  differs), cross-HEIGHT, cross-outcome, terminal included, are ALL
  distinct-key instances (REV 6, Codex5-21: the key lands in `CellOf αc ×
  Σ D, Hpt D` — `CellOf` IS the frozen `Cell e τ = Σ o, DCellO` shape at
  the instance through moveOf_bij/moveOfT_bij, so the frozen d4r0's own
  (c, h) ≠ (c′, h′) quantifier is stepKey-inequality DEFINITIONALLY —
  never a within-cell or cross-MARK pair (marks are not AStep elements,
  §2.F's marks record), so the law supplies it exactly; no cross-mark
  claim is consumed; the mismatched-dimension and off-pool instances ride
  the V7-4a double dite (one side ∅ — slot 15/12);
  the representative reads through the per-pool family at the law's q₀);
- `init_count` (ιshH·|Box| = |entEvtH| eventually): V.ent_card + V.box_card
  + the §2.G ιshH DEF — gate B: (1/4)·512 = 128 ✓ (F-1's number);
- `ent_count_card` ← rfl (entCount IS the census card BY DEF, §2.F).
moves_ref: as V7-6a1. deps: Defs 2.F/2.G, V7-4a/b/c. sketch: field by
field. hyp_fields: XHD (w + dC faces) + CellPolyPack — displayed.
*(Legacy ID note: "V7-6a" = a1 + a2.)*

**V7-6b `ledgerIV_sums` · `V7_livB.lean` · medium — SPLIT (Codex-19); THE
SUM/VALUE SUITE:** GIVEN V + X + cp + (ENT-U):
- `xhd_sum` ← X.sC.Gcell_hasSum (weight-only) ×-scaled by P_c.eval
  (HasSum.mul_left) through V0-3 — μcell IS the count×component-sum value
  by V7-4c's DEF (the C24(1) tie, now with the count factor VISIBLE);
- `kstep_one` ← V5-8's cell_refine (the count-bearing refinement — the
  C24(3) supplier, no longer a false package field) summed over the kcol
  outcomes landing at β (V7-4c's kstep carries ∏T, so the length-1 case is
  T·ΣGc = Σ_c P_c·ΣGcell = rowVal — the F-4 acceptance identity; the
  frozen field's member condition "∃ μ ∈ mem, ∃ h : μ.size = e, h ▸
  μ.status = Sum.inr β" matches V7-3a's odata through `omem_sel` (the
  designated β IS a member's target — REV 6, Codex5-22) + `omem_size`
  (the size cast) + `tcellM_sel` (the DESIGNATED member's landing
  coherence — REV 7, C3: the ∃-form; `omem_kcol` the
  derived single-member case) — cited here);
- `comp_once` ← X.sEnt.Gent_hasSum ×-scaled by the constant census
  ((ENT-U) at q₀ — the entrance-height sum, once; ιsh/ιDom/ιshH are the
  §2.F/2.G objects);
- `init_agg` ← V7-4b's ιval DEF (a finite sum over EntIx — rfl-level).
moves_ref: ledger faces (1)/(6)/(8)/(9). deps: V5-8, V0-3, V3-9b, V7-4b/c.
sketch: HasSum algebra. hyp_fields: XHD (s faces) + CellPolyPack + (ENT-U)
— displayed.

**V7-6c `ledgerIV_inst` · `V7_livC.lean` · medium — SPLIT (Codex-19); THE
ASSEMBLY:** `MovesS.LedgerIV T M`, theorem-under-hypotheses: GIVEN the XHD
bundle (the SAME X as V7-4's instance) + cp + hVA + HMC + the PART-1 legs +
ENT-COUNT + (ENT-U), every LedgerIV field is supplied: the V7-6a/b suites +
- `part1` ← V4-6; `rep_indep` ← V4-9 (rowVal is x-free BY DEF; the law is
  exactly (iv)-REP's content);
- `hmc` ← V5-5's (COMP-Σ) factorization GIVEN the open kernel (hHMC
  explicit — no unconditional instance until (v) closes; REV 4 RESTORES
  THE TAG'S CONTENT: with XHDd process-keyed, `hmc_theorem`-style
  discharges no longer exist — Fable N-1's collapse is repaired at the
  source — and the k = 0 leg is V7-4c's δ-collapse, hypothesis-free);
- `act_target` ← V4-1 (through hVA's tbl_count/tgt_supported at base
  points + u_T across the domain).
moves_ref: the CL-5 nine-input ledger's [1v] faces (S.0, cited; each face's
home display quoted at its field). deps: V7-6a1/a2/b, V4-*, V3-*, V7-4a/b/c.
sketch: assemble. hyp_fields: XHD + CellPolyPack + ValA + HMC + PART-1
legs + ENT-COUNT + (ENT-U) — the ledger's own tags, verbatim, nothing
silent.

**V7-7 `seam_rekey_stmts` · `V7_seam.lean` · easy (statement units) —
ONE SHARED PACKAGE PARAMETER (REV 4, Codex-10: rev 3 re-keyed all four
`XRBPackage.xhd_w/xhd_u/xhd_d/xhd_s` fields to the ONE full-bundle Prop —
"the field named xhd_w now assumes xhd_u, all domain faces, all sum faces,
and entrance exactness": each separately-owned premise was silently
STRENGTHENED to the bundle. The audit's own remedy is adopted: "coherence
should be obtained by projections from one shared package parameter").**
THE XRB RE-KEY, shared-parameter form — **Prop-TYPED at REV 5 (Codex-11:
the frozen `XRBPackage.xhd_w/xhd_u/xhd_d/xhd_s` fields have type `Prop`,
while rev 4's "aliases" `xhd_w ↦ X.w` assigned STRUCTURE VALUES — a type
mismatch, not a Lean mapping. The DISPLAYED adapter):** the shared
parameter is the DATA-ONLY frame; the four Props are the four FACE-LAW
∀-closures AT that frame:
```lean
/-- the [2b] DATA halves, bundled once (weights, listed domains, listed
sums — every datum the four face-law sets read; laws NOT included): -/
structure XHDFrame (n : ℕ) (S : StepSys n) {C : CtsFamily n}
    (V : CtsMeasured n C S) where
  E     : ∀ {α β} (m : S.Move α β), AffineE (S.dim m)
  ET    : ∀ {α v} (m : S.MoveT α v), AffineE (S.dimT m)
  dom   : ∀ {α} (γ : Template n S α), SemilinPart γ.D
  Gc    : ∀ {α} (γ : Template n S α), Fin (dom γ).comps.length → Qq
  Gcell : ∀ (d : MoveData n C) (c : V.DCellO d.s d.m d.o d.α)
    (j : Fin (V.cdom d c).comps.length), Qq
  GcellT : ∀ {v} (d : TermData n C v) (c)
    (j : Fin (V.cdomT d c).comps.length), Qq
  Gent  : ∀ (β₀ : S.Cell) (i : V.EntIx β₀), Qq

-- the four face-law Props at a frame F — CLOSED at REV 6 (Codex5-25's
-- second horn: rev 5's bodies were transcription promises). Rule kept:
-- each body = the VERBATIM law set of its §2.B/§2.G structure with the
-- data references re-pointed at F; where a face is LAW-ONLY (no data
-- fields — XHDu, XHDdC, XHDdEnt), `Nonempty` of the structure IS its law
-- set exactly (Prop-valued ✓, nothing added, nothing dropped):

/-- the frame-keyed weight product (gProd with F.E/F.ET in place of an
XHDw's — same three-case recursion; `gProdF (frameOf X) = gProd X.w`
definitionally): -/
noncomputable def gProdF (F : XHDFrame n S V) :
    ∀ {α} (γ : Template n S α), Hpt γ.D → ℚ → ℝ
  | _, .last m,  h, q₀ => (q₀ : ℝ) ^ (-((F.E m).eval h : ℤ))
  | _, .lastT m, h, q₀ => (q₀ : ℝ) ^ (-((F.ET m).eval h : ℤ))
  | _, .cons m γ, h, q₀ =>
      (q₀ : ℝ) ^ (-((F.E m).eval (Hpt.take h) : ℤ)) * gProdF F γ (Hpt.drop h) q₀

def XhdW_Stmt (F : XHDFrame n S V) : Prop :=
  (∀ {α β} (m : S.Move α β) {q₀} (x : S.Hist q₀ α) (h : Hpt (S.dim m))
     (a : S.Assign m x h), q₀ ∈ S.Pools → S.zc x →
     S.massOf m x h a = (q₀ : ℝ) ^ (-((F.E m).eval h : ℤ))) ∧
  (∀ {α v} (m : S.MoveT α v) {q₀} (x : S.Hist q₀ α) (h : Hpt (S.dimT m))
     (a : S.AssignT m x h), q₀ ∈ S.Pools → S.zc x →
     S.massOfT m x h a = (q₀ : ℝ) ^ (-((F.ET m).eval h : ℤ)))
def XhdU_Stmt (S : StepSys n) : Prop := Nonempty (XHDu n S)
  -- XHDu is LAW-ONLY (six Prop fields, no data) — Nonempty = exactly the
  -- six-law conjunction, no frame data read
def XhdD_Stmt (F : XHDFrame n S V) (TE : TmplEvents n S) : Prop :=
  (∀ {α} (γ : Template n S α) {q₀} (x : S.Hist q₀ α) (h : Hpt γ.D),
     q₀ ∈ S.Pools → S.zc x → 0 < Tgam TE γ x h → (F.dom γ).Mem h) ∧
  (∀ {α} (γ : Template n S α) (h : Hpt γ.D), (F.dom γ).Mem h →
     ∀ {q₀}, q₀ ∈ S.Pools → ∀ x : S.Hist q₀ α, S.zc x →
     0 < Tgam TE γ x h) ∧
  Nonempty (XHDdC n S V) ∧ Nonempty (XHDdEnt n S V)
  -- (REV 7, C6 echo: the template clauses at the note's own T_γ = Tgam,
  --  verbatim XHDd's two re-keyed laws)
  -- template face at F.dom, verbatim XHDd's two laws; the cell/entrance
  -- d-faces are LAW-ONLY over V's own listed data (cdom/entDom) —
  -- Nonempty is exact for both
def XhdS_Stmt (F : XHDFrame n S V) : Prop :=
  ((∀ {α} (γ : Template n S α) (j : Fin (F.dom γ).comps.length),
      ∃ b (as : Finset ℕ+), (F.Gc γ j).denom ∣
        Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a : ℕ))) ∧
   (∀ {α} (γ : Template n S α) (j) (q₀ : ℚ), q₀ ∈ S.Pools →
      F.Gc γ j ∈ OKat q₀) ∧
   (∀ {α} (γ : Template n S α) (j) (q₀) (hok : F.Gc γ j ∈ OKat q₀),
      q₀ ∈ S.Pools →
      HasSum (fun h : {h // ((F.dom γ).comps.get j).Mem h} =>
          gProdF F γ h.1 q₀)
        ((evalAt q₀ ⟨F.Gc γ j, hok⟩ : ℚ) : ℝ))) ∧
  ((∀ (d : MoveData n C) (c) (j : Fin (V.cdom d c).comps.length),
      ∃ b (as : Finset ℕ+), (F.Gcell d c j).denom ∣
        Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a : ℕ))) ∧
   (∀ d c j (q₀ : ℚ), q₀ ∈ S.Pools → F.Gcell d c j ∈ OKat q₀) ∧
   (∀ d c j q₀ (hok : F.Gcell d c j ∈ OKat q₀), q₀ ∈ S.Pools →
      HasSum (fun h : {h // ((V.cdom d c).comps.get j).Mem h} =>
          (q₀ : ℝ) ^ (-((F.E (V.moveOf d)).eval h.1 : ℤ)))
        ((evalAt q₀ ⟨F.Gcell d c j, hok⟩ : ℚ) : ℝ)) ∧
   -- the [+T] triple, WRITTEN OUT at REV 7 (Codex6-C12: the rev-6
   -- parenthesis "(the same three clauses …)" was literal prose inside a
   -- claimed-closed Lean body):
   (∀ {v} (d : TermData n C v) (c) (j : Fin (V.cdomT d c).comps.length),
      ∃ b (as : Finset ℕ+), (F.GcellT d c j).denom ∣
        Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a : ℕ))) ∧
   (∀ {v} (d : TermData n C v) (c) (j) (q₀ : ℚ), q₀ ∈ S.Pools →
      F.GcellT d c j ∈ OKat q₀) ∧
   (∀ {v} (d : TermData n C v) (c) (j) (q₀)
      (hok : F.GcellT d c j ∈ OKat q₀), q₀ ∈ S.Pools →
      HasSum (fun h : {h // ((V.cdomT d c).comps.get j).Mem h} =>
          (q₀ : ℝ) ^ (-((F.ET (V.moveOfT d)).eval h.1 : ℤ)))
        ((evalAt q₀ ⟨F.GcellT d c j, hok⟩ : ℚ) : ℝ))) ∧
  ((∀ (β₀ : S.Cell) (i : V.EntIx β₀), ∃ b (as : Finset ℕ+),
      (F.Gent β₀ i).denom ∣
        Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a : ℕ))) ∧
   (∀ β₀ i (q₀ : ℚ), q₀ ∈ V.Pools → F.Gent β₀ i ∈ OKat q₀) ∧
   (∀ β₀ (i : V.EntIx β₀) q₀ (hok : F.Gent β₀ i ∈ OKat q₀), q₀ ∈ V.Pools →
      HasSum (fun h : {h // ((V.entDom i.1.1).comps.get i.1.2).Mem h} =>
          (q₀ : ℝ) ^ (-((instA i.1.1 h.1 : ℕ) : ℤ)))
        ((evalAt q₀ ⟨F.Gent β₀ i, hok⟩ : ℚ) : ℝ)))
  -- template/cell/entrance s-faces at F's sums — weight-only throughout,
  -- exactly XHDs/XHDsC/XHDsEnt's law fields at the frame; NO substitution
  -- parenthesis survives (REV 7, C12: the [+T] triple is written out
  -- above; the exponent reads §2.D's instA wrapper — C11)

/-- the wave-4 XRBPackage instantiation — a DISPLAYED def into the frozen
CONTRACT type. PROVENANCE (REV 6, Codex5-25): `MovesS.XRBPackage` is
frozen at the MOVESS WAVE-4 BLUEPRINT level (13 Prop fields,
`MOVESS_LEAN_BLUEPRINT_2026-07-28.md` — the roster this adapter's nine
owner parameters + four xhd fields match EXACTLY, verified by the round-5
fresh audit), NOT in the built E-phase source — the built
`MovesS/Interfaces.lean` says the §W4-SYNC declarations are "NOT built at
E-phase". This unit therefore BUILDS AFTER the MovesS-side wave-4
declaration lands (dep recorded below); until then the def is
blueprint-typed against the frozen roster. The nine non-xhd fields stay
their owners' Prop parameters: -/
def xrbPackageOf (F : XHDFrame n S V) (TE : TmplEvents n S)
    (jc_inv sib jc_multi tb_cap vp rel2_a rel2_b rel2_d ns_null : Prop) :
    MovesS.XRBPackage :=
  { xhd_w := XhdW_Stmt F, xhd_u := XhdU_Stmt S,
    xhd_d := XhdD_Stmt F TE, xhd_s := XhdS_Stmt F,
    jc_inv := jc_inv, sib := sib, jc_multi := jc_multi,
    tb_cap := tb_cap, vp := vp,
    rel2_a := rel2_a, rel2_b := rel2_b, rel2_d := rel2_d,
    ns_null := ns_null }

-- the discharge direction (one line): a full package witnesses its own
-- frame's Props — `frameOf (X : XHD n S TE V) : XHDFrame n S V` := the
-- data projections (X.w.E, X.d.dom, X.s.Gc, …), and
-- `xhd_faces_of (X) : XhdW_Stmt (frameOf X) ∧ XhdU_Stmt S ∧
--  XhdD_Stmt (frameOf X) TE ∧ XhdS_Stmt (frameOf X)` — by X's law fields.
```
So (i) coherence is BY SHARING (one frame F: same
weights, same domains, same sums — C27's demand still met: four unrelated
incompatible witnesses are impossible), (ii) NO premise is
strengthened: each Prop is EXACTLY its face's law set at F, and the S.1
proof may consume exactly the faces its ledger line
names, per-face accounting preserved (Codex-10's demand), and (iii) the
frozen field TYPES are supplied (Props, Codex-11). `xhdStmt :=
Nonempty (XHD n S_cts TE_cts V_cts)` SURVIVES ONLY as V1-5's [1v]-FULL
discharge-event Prop — it is NO LONGER any field's re-key target.
`def cts_counts_stmt : Prop := ValA … ∧ EntCount …` (re-keying
`Wsh17Package.cts_counts` — S-8's [1v] leg); PLUS the S-8 demands honored
AS A TYPE, at REV 4 with the FULL FROZEN FIELD ROSTER (Codex-11: rev 3's
two-field structure "is not a re-keyed Wsh17Package and cannot supply
W17ii's premise type" — the frozen package has `c15_volumes`/`cts_counts`/
`sib_count`, and comments do not put fields in a type; Fable SF-2's
ownership record was HONEST and is kept — the owner-side fields now ride
as PARAMETERS, present in the type, inhabited by their owners):
```lean
/-- the re-keyed Wsh17 package, DISPLAYED — REV 4: the frozen three-field
roster complete; the [§C/HC-2]- and [3t]-owned legs are Prop PARAMETERS
(the owners bind them at wave 4; MovesV pins its own two legs' content),
plus S-8's demanded xhd_s face as the shared-parameter projection: -/
structure Wsh17PackageV (c15V sibC : Prop)
    (X : XHD n S_cts TE_cts V_cts) : Prop where
  c15_volumes : c15V                    -- owner §C/HC-2 (frozen field 1)
  cts_counts  : cts_counts_stmt         -- S-8's [1v] leg (frozen field 2)
  sib_count   : sibC                    -- owner [3t]/CL-10 (frozen field 3)
  -- S-8's DEMANDED xhd_s face is DELIVERED BY THE PARAMETER X (its
  -- s/sC/sEnt projections — the shared-instance form, per Codex-10's
  -- remedy; a separate Nonempty field would be either free-floating or
  -- trivially witnessed by X.s, both defects).
  -- (the empty-menu fence stays OWNER-SIDE OPEN — SF-2 below; the field
  --  NAMES are verbatim from MovesS's frozen Wsh17Package — tree/shape
  --  vocabulary MovesV does not restate; §4.3's re-keying instruction
  --  binds the owner parameters at wave 4.)
```
THE EMPTY-MENU LEG, HONESTLY SCOPED (Codex-17's second horn: rev 2 routed
`F.Sh.Nonempty` "through S-5" while listing S-5 as NOT re-keyed — a
contradiction, and the owner-side `W7_cutWD` still carries the obsolete
`isDeepSplit → ¬ isEntrance` clause): REV 3 does NOT claim the vacuity
fence closed. SEAM FLAG SF-2 (new, recorded in §4.3): W17ii's
nonemptiness leg awaits [3t]'s `tree_ne` + the W7_cutWD
first-entrance-ancestor retype — OWNER-SIDE OPEN; MovesV delivers exactly
its two legs (the `cts_counts` field + the shared-parameter s-face) in the
DISPLAYED full-roster `Wsh17PackageV` and flags the rest. [REV 7, C14:
the CONTENTFUL W17ii proof duty at the built projection-def type is now
scheduled — unit V7-8; this package remains the [1v]-legs record only.]
moves_ref: MovesS §W4-SYNC S-2/S-8/S-9 +
this note's V.0 package. deps: V7-4a/b/c, V2-4, V3-9a, **+ the MovesS
wave-4 §W4-SYNC declaration of `XRBPackage` (Codex5-25: the target type
is BLUEPRINT-frozen — MOVESS blueprint, 13 Prop fields — and absent from
the built E-phase `MovesS/Interfaces.lean` by that file's own "NOT built
at E-phase" note; `xrbPackageOf` and the S-2 re-key are SEAM-PHASE
deliverables gated on that co-build; the four face-law `*_Stmt` defs and
`XHDFrame`/`gProdF` build NOW, MovesS-free)**.
sketch: defs + one structure. hyp_fields: none (names for open obligations —
their TYPES pin their content, per doctrine; inhabitation stays with the
owners).

**V7-8 `w17ii_wave4` · `V7_w17ii.lean` · medium — NEW UNIT at REV 7
(C14 = Fable CRIT-1; W4-SYNC delta 2): the SCHEDULED W17ii proof duty.**
The built MovesS DELETED the `wsh17_pin` Prop FIELD — `RS4Chain.wsh17_pin`
is now a projection-NAMED DEF equal to `W17ii T M F C.WshP C.WshVal
C.shDom C.shWeightH` at the chain's own carriers (built Interfaces.lean
103–109 + 187–190), so rev 6's duty "instantiate the pin with W17ii's
statement" names NOTHING; the wave-4 duty is to PROVE W17ii for the
instance. THIS unit carries it at EXACTLY that type:
`theorem w17ii_wave4 (C : RS4Chain T M RB hdc hK F) [the wave-4 instance
data] : MovesS.W17ii T M F C.WshP C.WshVal C.shDom C.shWeightH` — clause
(i) (WshP evaluates to WshVal) from the chain's own `wsh_ok`/`wsh_interp`
fields (rfl-level at the instance); clause (ii) (WshVal IS the shDom
height-sum of shWeightH — the XHD-s shallow-height-sum face) from the
per-ε̊ ingredients V7-4b supplies (entDom/ιshH/Gent) ASSEMBLED over the
per-shape Ŝ layer — the [3t]-owned half (shapes are tree vocabulary), so
the theorem is SORRY-GATED at exactly the displayed type until the
wave-4 assembly (MovesT + [3]) discharges it: one named sorry, banked
per campaign policy, its type the whole content. The `h17 : C.wsh17_pin`
binder in U-28 is byte-identical and now CONTENTFUL — no unconditional
marking while this sorry lives. moves_ref: CL-17(ii) production core
(MOVES 12095–12099). deps: V7-4b, V7-7, MovesS.Interfaces (built).
sketch: clause (i) rfl-level; clause (ii) sorry-gated assembly.
hyp_fields: the sorry IS the recorded obligation (SF-2's vacuity fence
stays owner-side open beneath it).

**V7-9 `polygeom_count_laws` · `V7_pgLaws.lean` · medium — NEW UNIT at
REV 7 (Fable GAP-2; W4-SYNC delta 5): the recorded MovesV seam residue.**
Supplies `MovesS.PolyGeomLaws T M RB` (built Defs.lean 396–410 region):
`countS` pinned against the cell-count carrier (`cellInst`/`cellLvl` —
V7-5c's `cellP_count` wiring, aggregated over the outcome's cell fiber
exactly as rep_indep aggregates masses) and `countT` pinned against the
carried `tCount` data, whose EVENT-SIDE IDENTIFICATION is THIS unit's
content — the built comment names the duty: "tCount's event-side
identification with the CTS/[1] count tables and V.2's exponent-map
audit needs §V-TABLES vocabulary — the MovesV seam (wave 4)". The named
carrier is `ValA.tbl_count` (the §2.F note: "the COUNT SEMANTICS is
ValA's field content"): tCount e τ o := the table count
`(C.T … d.tix).eval` at the datum's own index, identified with the
realized event counts through tbl_count (base points) + u_T across
domains (MDomTie) + evt_card; V.2's exponent-map audit rides the same
Wloc degree ledger V2-4 displays. moves_ref: CL-6 "(iv)-POLY (CL-6, with
V.2's EXPONENT-MAP AUDIT)" (MOVES 12129–12132) + the built PolyGeomLaws
header. deps: V2-4, V7-4a/c, V7-5a/c. sketch: field defs + the
tbl_count/evt_card chain. hyp_fields: ValA + (XHD-u) + MDomTie —
displayed (the count laws are theorem-under-burdens, "consumed by the
`_counted` variants (CountLaws.lean); never self-supplied").

## §4 SEAM-SUPPLY — every MovesS interface field, mapped to its supplying unit

This section is the wave-4 answer to MovesS's §W4-SYNC contract and to the
intended-instance notes in `MovesS/Defs.lean`. Legend: **[MovesV: unit]** =
supplied by this corpus; **[owner]** = NOT this corpus's (named owner; MovesV
neither states nor strengthens it). REV-2 pointer hygiene (A-7): entrance
carriers live in §2.F (EntIx/entDom/entEvt) and §2.D (hent/Went projections);
no "from 2.E" pointers remain.

### 4.1 `MovesS/Defs.lean` instantiation targets (the W-11 process gate)

| MovesS object | supplier |
|---|---|
| `TableShape n` (State/VType/vEquiv/Out/odata/Wloc/Wstate) | [MovesV: V7-3a from `CtsFamily` (§2.C); vEquiv via `VLabel` = the R20 pin verbatim; `odata` from the REV-5 member roster `omem`/`tcellM` (Codex-2 — the map DISPLAYED at V7-3a, `Outcome.hm` ← `omem_ne`); + route_eq (F-6's classification tie)] |
| `DegCons T` | [MovesV: V2-9 (gate rosters, decide) + the CL-11 full-roster burden field for uncomputed skeletons — carried, not discharged] |
| `KmatHyp T e` (a PROP: kcol members size e) | [MovesV: V7-3b PROVES it at the gate instance by decide; general = the TYPED `StageLawBurden.kmat_all` (V7-3d — Codex-20; no prose burden). (C25 repair stands: it is a proposition, and no MovesS theorem derives it.)] |
| `SCSData T` (W/D/ℓ/g/μsel/W'/D'/flankCount/flankWidth/resFactors/selIdx/memberOf + 12 laws) | [SPLIT (C25 repair): DATA fields ← V7-3c from MovesSp species stage fields (s.D, s.w, s.W, s.sel, s.lam) through the roster wiring; LAWS decided at the gate rosters (V7-3c) AND, beyond them, carried as the TYPED `StageLawBurden` (V7-3d — Codex-20: a closed hypothesis structure with all twelve law fields + kmat_all + degcons_all, a `CtsmLedger` field; no prose burden survives)] |
| `MeasuredSide T` (all fields) | [MovesV: V7-4a/b/c from `CtsMeasured` (§2.F) + the XHD package + `CellPolyPack` as data + MovesD boxes; `Hgt` carrier = Σ D, Hpt D ("MovesV instantiates the carrier at wave 4" — DONE here); entrance side = EntIx with the CENSUS wiring (entCount/entInst = the ε-instance census, ιshH = census·q^{−A} — F-1/F-2); cellLvl/cellInst = the STATE census stLvl/stInst (F-5); gwt/μcell/rowVal/kstep = count-polynomial × weight-only sums, kstep with ∏T (F-4) AND the REV-4 k = 0 Kronecker-δ case (N-3); `Rep` = the REV-5 PER-POOL representative family with the off-pool-∅ `cellEvt` branch (M-3 = Codex-1 — the frozen pool-global type instantiated, walk at V7-4a) + the REV-6 DIMENSION dite on `Hgt = Σ D, Hpt D` (Fable G-B, slot 15 — the mismatch branch forced ∅ by the unguarded no_orphan); `hent` = the length-seeded `hentCode` of the base instantiation (REV 4, Codex-6; REV 5, Codex-7/G-2 scope) + seam flag SF-1 (V7-4b — the round-2/3 disagreement and its computed-evidence resolution on file)] |
| `MeasuredSide`/`TableShape` MECHANICAL INSTANCE FIELDS, named per Codex-17 (`fin`, `deq`, `deqV`, `finV`, `finO`, `finC`, `finB`, `finE`, `decA`, `boxpos`, `rep_ne`) | [MovesV: V7-3a (TableShape side: Fintype/DecidableEq from the §2.C Fintype fields + `Skeleton`'s SP2-finite catalogue; `finO` ← `BlockData.finO`) and V7-4a/b (measured side: `finB/boxpos` ← V's box fields; `finC` ← `finDO` + finite outcomes; `finE` ← V3-4 × list length; `decA` ← `act_size` + polynomial-eval decidability at ℚ points; `rep_ne` ← `zc_ne`) — each an EXPLICIT instance line in the unit's roster, none silently assumed] |
| `RatBurdens T M`: `tgP/tg_ok/tg_interp/tg_degT/tg_degS` | [MovesV: **V7-5a leg (a)** (`V7_rbA.lean`) from ValA (V2-4) × the XHDs/XHDsC geometric faces — CL-6 (iv)-POLY, GIVEN the table-build coverage AND the [2b] height-sum face (C23: rowVal is resummed; counts alone cannot interpolate it)] |
| `RatBurdens.jP/j_ok/j_interp/j_degT/j_degS` | [MovesV: **V7-5a leg (b)** (`V7_rbA.lean`) from V5-7b — **(J-RAT)/CL-18, THE PLAN-SYNC DELIVERABLE recorded owner-side**; per-(τ,o) incl. split routes (C8); height-sum face tagged [2b]] |
| `RatBurdens.jPCell/jcell_ok/jcell_interp/jcell_sum` (NEW at ratification — the per-cell J-RAT interface, built Defs.lean 386–395) | [MovesV: **V7-5a leg (b)**, RE-KEYED at REV 7 (C15 = Fable CRIT-2): V5-7b's `jRat_cell`/`jRat_sum` per-cell clauses (CellPolyPack × weight-only Gcell sums = `jcellPG`, eval = M.μcell rep-quantified split-guarded; symbolic cell-fiber Σ = jP.val), transported to the EXISTING carrier `M.Cell` through V7-4a's `dataOf` — NO parallel type is the deliverable] |
| `RatBurdens.ιP/ι_ok/ι_interp/ι_countS_one/ι_count/ι_degT/ι_degS` | [MovesV: **V7-5b** (`V7_rbB.lean`, leg (c)) from V3-9c(a)'s PER-COMPONENT PolyGeoms (the C23 type fix) + V3-9a (ENT-COUNT); GIVEN XHD-shallow + (ENT-U) + AffEnt] |
| `RatBurdens.cellP/cellP_deg/cellP_nonzero/cellP_count/act_iff` | [MovesV: **V7-5c** (`V7_rbC.lean`, leg (d) + act_iff + the assembly), the REV-3 REVERT to the rev-1 sizeP wiring (F-5): cellP = the state-size polynomial; cellP_count ← `stInst_card` (the state census, G4 pattern); act_iff ← `act_size`; the rev-2 CellPolyPack keying and its ActIff premise are STRUCK (they violated cellP_deg at both gates and act_iff at q₀ = 2)] — [REV 6, Codex5-29: these four rows now name the REAL unit IDs/files of the Codex-16 split (V7-5a = legs a+b, V7-5b = leg c, V7-5c = leg d); rev 5's `V7-5(a)/(b)/(c)/(d)` pointers pre-dated the split and `V7-5(d)` named a unit that does not exist] |
| `LedgerIV T M` (all nine inputs) | [MovesV: V7-6a/b/c, CONDITIONALLY — the field-by-field map with the REV-3 TYPED TIES (meas_card ← evt_card + w_eq + cp.count + XHDdC; no_stray/no_orphan ← XHDdC + evt_card; d4r0 ← the AStep disjointness law; xhd_sum ← weight-only Gcell sums × P_c; kstep_one ← V5-8's DERIVED cell_refine; init_count ← ent_card + box_card + the census ιshH (gate: 128 ✓); ent_count_card ← rfl against the census; comp_once ← Gent_hasSum × (ENT-U); hmc ← hHMC explicit — no unconditional instance until (v) closes)] |
| `EscapeE0`, `PoolHyp`, `DetHyp`, `RegP` | [owner [3] MovesS — CL-1; MovesV only supplies the entries' OKat memberships through RatBurdens] |

### 4.2 `MovesS/Interfaces.lean` fields

| field | supplier |
|---|---|
| `RS1Meas.βmeas/β_bdd/βfull` | [owner [3t] → MovesT: measured subtree values; MovesV supplies NO per-f or subtree object — the [3t] fence; h_ent binding per seam flag SF-1] |
| `RS1Bundle.xrb` (W-2) | [owner [3]: the S.1 theorem; its `XRBPackage.xhd_w/xhd_u/xhd_d/xhd_s` premise fields (Prop-typed) RE-KEYED to the FOUR FACE-LAW Props at ONE SHARED data frame — V7-7's DISPLAYED adapter `XHDFrame`/`XhdW_Stmt`…/`xrbPackageOf` (REV 5, Codex-11: rev 4's structure-valued "aliases" did not type; coherence by sharing the frame, per-face accounting preserved, Codex-10; the rev-3 all-fields-=-full-bundle form stays STRUCK)] |
| `RS1Bundle.recursion_meas` (W-3) | [owner [3t]/[3]: the RS1GivenPackage route; MovesV contributes the PCI leg's (iv)-REP statement (V4-9) as the re-key target for `pci`'s REP conjunct] |
| `RS1Bundle.nsNull/rexact` | [owner [3t] §T.2 — CLOSED there; tag displayed] |
| `RS4Chain.L` | [MovesV: V7-6c (conditional instance)] |
| `RS4Chain.B/hns/PrimePools/prime_*/Sigmas/sig_exact` | [owner: wave-4 assembly (MovesT + MovesS gate)] |
| `RS4Chain.pools_e0/legs_reg` | [owner [3] — CL-1 E0; consumes MovesV's RatBurdens entries. REV 7 note (W4-SYNC delta 4): `deltaFactors` is NARROWED to `Member.continuing` (halted = factor 1), so these quantify over FEWER pools than rev 6's text assumed — no MovesV statement quoted the old collection (Codex round-6 confirmed), recorded here so the map reads against the built source] |
| `RS4Chain.legs_read` (NEW at ratification — built Interfaces.lean 141–143) | [owner [3] with MovesT at the wave-4 assembly — the note's PER-POOL weakened (ii-c) read-off gate at every NON-all-active consumed pool (MOVES 12204–12218): `LegAgree` at `B.βmeas` per consumed δ ∈ `consumedDeltas`, GIVEN `hdet : DetHyp`; MovesV supplies the RatBurdens entries/OKat memberships it reads and the (ii-c) statement form for the ALL-ACTIVE face only (V4-3, C13-scoped) — the LegAgree check itself is not MovesV's to state. ROW ADDED at REV 7 (C13 = Fable GAP-1: the map's "every field" completeness claim is true again)] |
| `RS4Chain.WshP/wsh_ok/WshVal/wsh_interp/wshval_bdd` | [owner [3t]/[3] — CL-17(ii) production; MovesV supplies the `cts_counts` leg: V7-7's `cts_counts_stmt` (ValA ∧ EntCount) + the demanded `xhd_s` face `wsh_xhd_s_stmt` (seam S-8, C26)] |
| `RS4Chain.wsh17_pin` | [RE-KEYED at REV 7 (C14 = Fable CRIT-1; W4-SYNC delta 2): the Prop FIELD IS DELETED in built MovesS — `wsh17_pin` is a projection-DEF = `W17ii` at the chain's own carriers (built Interfaces.lean 103–109, 187–190); NOTHING remains to instantiate. The duty is now PROVE `W17ii T M F C.WshP C.WshVal C.shDom C.shWeightH`: **MovesV V7-8** carries it at exactly that type (clause (i) rfl-level from wsh_ok/wsh_interp; clause (ii) sorry-gated pending the [3t]/[3] shape-layer assembly); the [1v] ingredients = V7-7 + V7-4b; the empty-menu exclusion stays [3t] tree_ne (SF-2)] |
| `RS4Chain.shDom/shEvtH/visH/shEvt/shWeightH/shevt_grouping/shDom_ne/sh_realized/shweight_card/wshval_card` | [SPLIT: the per-ε̊ shallow ingredients (entrance domains entDom/H(ε̊), entrance events entEvt/entEvtH, ιshH weights — §2.F/§2.G) are MovesV's, at V7-4b's entrance side; the per-SHAPE Ŝ assembly over trees is MovesT's (shapes are [3t] vocabulary). The re-keying REPLACES MovesS's device fields by production objects only when BOTH halves exist — per S-8/S-10's re-keying charge] |
| `RS4Chain.Rval/r_bdd/decidedTotal/x3_total/rs1_equates/rsh_interp` | [owners [3t]/[5]/[3] — W-1/W-4 pins; μ̂/density fence: nothing here is MovesV's to state] |
| `ReadOffBundle.pkg` | [owner [3] — E0 packages] |
| `ReadOffBundle.read` (AVAgree) | [MovesV: V4-3 states the (ii-c) duty in MovesS's own AVAgree shape; the CHECK is RESUM-n3's ([3]'s gate) — recorded, never a blanket claim] |

### 4.3 The seam entries RE-KEYED by this blueprint (count: 6)

1. **S-2 (`W2_xrb` package fields)** — REV 5 (Codex-11, refining REV 4's
   Codex-10 repair): the four `xhd_*` Prop placeholders in `XRBPackage`
   re-keyed to the FOUR FACE-LAW Props AT ONE SHARED DATA FRAME —
   `xrbPackageOf F TE …` with `xhd_w := XhdW_Stmt F`, `xhd_u := XhdU_Stmt`,
   `xhd_d := XhdD_Stmt F TE` (incl. the dC/dEnt exactness clauses),
   `xhd_s := XhdS_Stmt F` (incl. the sC/sEnt clauses) — Prop-typed as the
   frozen fields demand (rev 4's structure-valued aliases did not type);
   coherence BY SHARING the frame F (C27's demand kept: no four unrelated
   existentials), no premise strengthened (each Prop is exactly its face's
   law set at F; the S.1 proof's per-face ledger accounting survives);
   `frameOf`/`xhd_faces_of` give the discharge direction from a full X.
   The rev-3 every-field-=-`xhdStmt` re-key stays STRUCK; `xhdStmt`
   remains only as V1-5's [1v]-FULL discharge-event Prop. `jc_inv`/`sib`/`tb_cap`/`vp`/`rel2_*` stay with
   their owners ([2b]/[3t]/[2r]). PROVENANCE (REV 6, Codex5-25): the
   `XRBPackage` contract type is frozen at the MOVESS WAVE-4 BLUEPRINT
   (13 Prop fields), not in the built E-phase source (its Interfaces.lean
   marks §W4-SYNC "NOT built at E-phase") — this re-key executes at the
   wave-4 co-build (V7-7's recorded dep).
2. **S-8 (`W17ii` + `Wsh17Package`)** — REV 7 (C14 = Fable CRIT-1): the
   built corpus RETYPED the pin — `wsh17_pin` is a projection-def =
   `W17ii` at the chain's carriers, so S-8's rev-6 "package re-key"
   framing is no longer the whole duty: the CONTENTFUL obligation is
   W17ii's PROOF at the wave-4 instance, SCHEDULED as unit V7-8
   (sorry-gated at exactly the built type until the [3t]/[3] shape-layer
   assembly lands; U-28's `h17` binder byte-identical, now contentful;
   no unconditional marking while it is open). The package legs stand:
   the `cts_counts` field re-keyed to
   `cts_counts_stmt := ValA ∧ EntCount` (V7-7); REV 4 (Codex-11): the
   re-keyed package `Wsh17PackageV` now carries the frozen package's FULL
   three-field roster (`c15_volumes`/`cts_counts`/`sib_count`) — the two
   owner legs as Prop PARAMETERS (present in the type; [§C/HC-2] and
   [3t]/CL-10 inhabit them at wave 4) — and S-8's demanded `xhd_s` face
   rides as the SHARED package parameter's projection (never a free
   Nonempty). THE EMPTY-MENU LEG IS **OWNER-SIDE OPEN**
   (SEAM FLAG SF-2, replacing rev 2's contradictory S-5 routing claim):
   W17ii's vacuity fence stays open until [3t] types `TreeIface.tree_ne` AND
   retypes `W7_cutWD`'s obsolete `isDeepSplit → ¬ isEntrance` clause to the
   first-entrance-ancestor form; MovesV claims only its delivered legs.
3. **S-9 (packages as registries)** — the [1v]/[2b]-XHD names in the
   registries now point at ONE typed bundle with content-pinning fields
   (doctrine satisfied: degenerate instances violate typed laws — chainCount
   definitional, non-vacuity fields, exactness over the process-side
   realization with the one-way count supply — REV 4).
4. **W-6 (wild-pool read-off, AVAgree)** — cited per consumption site: V4-3
   is the [1v]-side citation form — SCOPED at REV 7 (C13): V4-3's shape
   covers the ALL-ACTIVE face (`ReadOffBundle.read`); the non-all-active
   consumed pools now ride the built `RS4Chain.legs_read` (LegAgree,
   owner [3]/MovesT — §4.2's new row); V4-3 quantifies none of
   LegAgree/βmeas/consumedDeltas.
5. **W-11 (instantiation of every §2 structure by the REAL CTS objects)** —
   the process gate is now the concrete unit list V7-3a/b/c/d, V7-4a/b/c,
   V7-5, V7-6a/b/c (+ V2-9), PLUS the REV-7 seam duties V7-8 (W17ii at
   the built type) and V7-9 (`PolyGeomLaws` — tCount's event-side
   identification, the recorded MovesV residue); DONE when those build
   (V7-8's sorry is the one recorded open leg). The SCSData/KmatHyp rows
   are part of this gate (C25/Codex-20).
6. **CL-18 (J-RAT) owner-side record** — the PLAN-SYNC flag's demand ("the
   owner notes' NEXT revision rounds must record these deliverables on their
   side") is discharged FOR THE LEAN CORPUS by §2.H + V5-7a/b/c: the
   per-cell tables are typed PER (τ, o) INCLUDING split routes (C8), their
   ℚ(q)-membership stated in the (iv)-POLY pattern, the not-the-marked-T·G
   fence machine-checked — AND, at REV 7 (C15), PER CELL: V5-7b's
   `jRat_cell`/`jRat_sum` supply the built `jPCell/jcell_ok/jcell_interp/
   jcell_sum` through V7-5a leg (b), on the existing `M.Cell` carrier.
   (The NOTE text itself is accepted and unedited —
   this is the Lean-side record, exactly as the flag prescribes cross-note
   binding through the ledger.)

NOT re-keyed here (recorded): MovesS seam entries S-1/S-1e/S-1m, S-3, S-4,
S-5, S-6, S-7, S-10, S-11 (MovesT's vocabulary — trees, fibers, read
ledgers, RS.1); MovesD's §2.5 entries W4-1..W4-4 (TreeModel semantics,
VerdictModel, D4R_CYL consumer, NP-ID — MovesT/HC-2's; the W4-SYNC
delta-10 W4-1 covering-clause change (`ChildCover`, MovesT REV-7 ruling
1) is MovesT/MovesD's contract traffic — no MovesV statement reads
W4-1). (JC-INV)/CL-19 is
[2b]'s and appears in NO MovesV statement. SEAM FLAG SF-1 (V7-4b): MovesT's
h_ent binding must use the Hgt-indexed entrance carriers, not
`MeasuredSide.hent` (retained at REV 3 over Codex-7's objection, on Fable's
round-2 source verification that no MovesS law reads the field — the
disagreement and its resolution are on the record at V7-4b). SEAM FLAG SF-2
(V7-7/S-8; RESTATED at REV 7 with C14): W17ii's empty-menu vacuity fence is
OWNER-SIDE OPEN — [3t]
owes `tree_ne` + the W7_cutWD first-entrance-ancestor retype; MovesV's S-8
delivery is the two `Wsh17PackageV` fields PLUS the scheduled W17ii proof
duty V7-8 (sorry-gated at the built projection-def type — the pin field
no longer exists to instantiate).

## §5 Build order, process, and the census

**Build order (E-phase):** Defs → DefsGate → V0 → V1 → {V2, V6} (parallel;
V6 depends only on DefsGate + 2.A) → V3 → V4 → V5 → V7. The gate layer V6
is deliberately early-buildable: it is the corpus's non-vacuity anchor (the
sealed numbers re-derived in-kernel before any measured clause elaborates).

**Difficulty census: 98 units = 32 easy / 62 medium / 4 hard (REV 7:
+V4-13 `hmcaug_of_hmc` (G1), +V7-8 `w17ii_wave4` (C14), +V7-9
`polygeom_count_laws` (GAP-2) — all medium).**
Per layer: V0[4: 2e/2m] V1[10: 5e/5m] V2[10: 6e/4m] V3[17: 4e/11m/2h]
V4[15: 3e/11m/1h] V5[12: 3e/8m/1h] V6[10: 5e/5m] V7[20: 4e/16m].
Delta vs rev 3 (82 = 33/43/6), all REV-4 driven: the pre-approved splits
PROMOTED to real unit IDs (Codex-16) — V3-3 → V3-3a/b/c/d (m/m/m/h),
V3-5 → V3-5a/b/c (h/m/m), V4-6 → V4-6a/b/c (m/h/m), V5-2 → V5-2a/b/c
(m/h/m), V7-5 → V7-5a/b/c (3 medium — the split de-escalates the
assembly); V3-8 → V3-8a/b (Codex-7's premise split, 2 medium); V7-6a →
V7-6a1/a2 (Fable G-2's roster rule, 2 medium); V4-11 re-graded easy →
medium (it now BUILDS the coupled process-side toy); V4-12 re-graded
HARD → medium (the ∀-E generating-series separation is GONE with the
quantifier fix — the remaining legs are a HasSum Fubini + two norm_num
toys). HARD (escalation-risk set, pre-declared): V3-3d (the
reconstruction bridge — the corpus's real E-phase risk, hatch recorded),
V3-5a (injectivity through it), V4-6b (the null-remainder limit),
V5-2b (the COMP-h grouping induction step). WATCH (medium with known
teeth): V0-4 (double geometric sum in Qq), V2-6 (cyclic power-image
cardinality), V5-8 (the Fubini rearrangement over the (c,h) double sum),
V6-1c/V6-3b (the F4/F8/F9 table fields — decide feasibility over 9³·9
tuples is fine, but the Field-instance decides need `Decidable` instances
written with care), V6-4c (the CoprimeLiftPack — Mathlib Hensel
archaeology; published-axiom fallback per campaign §4, flag before
declaring), V4-11 (the coupled-toy decide budget). REV 5 ADDS NO UNITS
(census unchanged at 95 = 32/59/4): every round-4 repair is a
statement/Defs-level rewrite inside existing units — the omem/tix/
TargetIx retype (§2.C), the Rep re-key (V7-4a), the RefEvents pin (§2.G),
the named-burden move (EntMassSummable), and the display closures.

**THE DESIGN-FREEDOM INVENTORY — COMPLETE, ALL FIVE SLOTS, ALL RESOLVED
(A-5 repair; per campaign §3(ii) each resolution is recorded WITH the audit
round, and no slot remains open into E-phase):**
1. `StepSys.inv` (rev-1 stub) → RESOLVED: DELETED. `C15Pack` already carries
   the pinned inventory carrier (`Inv`/`invOf`/`F`/`mass_factors` — the
   note's C.1(ii) role); nothing in the note demands a slot on `StepSys`
   (adjudicated at A-5, adopted here).
2. `XHDd.chain`'s recursion tie (rev-1 "field the E-designer adds") →
   RESOLVED, RESTATED at REV 7 (C6, adjudicated — refining the REV-5
   restatement). The OPERATIVE
   RULE: NO FREEDOM EXISTS, split two-sidedly — the note DEFINES T_γ
   DIRECTLY ("#{fresh-assignment chains from x realizing (γ, h)}") and
   Lean encodes it as the PROCESS-side mark-census count `Tgam` (§2.G);
   the TABLE-side recursion is the separate def `chainCount` (through
   `StepSys.ext`); XHDd's EXACTNESS laws quantify over `Tgam` (the
   note's T_γ verbatim — NEVER over `chainCount`, whose tie enters
   one-way only via marks_chains/V1-3(b)'s `mem_chainCount_pos`); the
   factorization T_γ = ∏ T_step is (u-T)/HMC CONTENT, never
   definitional; any E-phase re-key of exactness to `chainCount` (or any
   composite census recursion) re-proves HMC and is FORBIDDEN (the
   slot-9 fence).
3. `moveOf` + the fixed-h form of `tbl_count` → RESOLVED: `moveOf` is a
   DISPLAYED CtsMeasured field with its bijection law (§2.F); the count
   semantics is `ValA.tbl_count`, stated representative- and height-uniformly
   at realized heights (V2-4 — VAL(a)'s burden, the note's own
   "alternative discharge" framing).
4. V4-1's `lands_in` → RESOLVED: the count-level landing tie is the ValA
   field `tgt_supported` (V2-4; "a landing forces a concrete target state"),
   consumed by V4-1 under the restored active-source guard (C15).
5. V3-9c's PolyGeom-closure vs OKat-landing route → RESOLVED: the CLOSURE
   route — PolyGeom add/scalar mini-lemmas local to MovesV (no MovesS edit);
   V3-9c(b)/V5-7b consume them.
6. (NEW at REV 3) the u*-slot ℕ-encoding (G-3) → RESOLVED: the slot carries
   zig(gam_r) (`Denumerable.eqv ℤ`); u* is the DISPLAYED gamTie inversion
   (§2.D); recorded with its tighten-at-MovesD hatch.
7. (NEW at REV 3) the instance-census box realization → RESOLVED: `entInst`/
   `stInst` are carrier DATA (box-embedded censuses at the defining levels)
   with the typed counting ties `ent_card`/`stInst_card`/`evt_card`/
   `box_card` pinning their semantics ([tie] fields; discharged by
   MovesD/MovesC at the real instance — D4R1_SUM/D0b_thmCtop, G4).
8. (NEW at REV 3) the `castMove/castHpt/castAssign` transport helpers
   (Refinement's assign_cover) → RESOLVED: mechanical ▸-wrappers, zero
   design content, one line each at E-phase (recorded so the inventory
   stays COMPLETE).
9. (NEW at REV 4) the process-side carriers (N-1) → RESOLVED: `TmplEvents`
   is FREE DATA at composite templates BY DESIGN — the freedom is the
   kernel's openness, not a slot to fill; its four [tie] fields
   (tevt_last_iff ×2, real_marks, marks_chains) pin everything the note
   makes definitional, and NOTHING more may be added without re-proving
   the §2.G underivability audit (any composite-recursion tie re-proves
   HMC — the rev-3 lesson, now a standing fence).
10. (NEW at REV 4) `shapeRank`'s enumeration order (Codex-4) → OVERTAKEN
   at REV 6 (Codex5-23 — the recorded hatch FIRED): `shapeRank`/`eligMenu`/
   `takenGm` are STRUCK; no shape-level enumeration order exists to
   choose. The selection index is MovesD's OWN `selRank % m̄` (the E9
   encoding component), consumed by name through the `SelMatches` def
   (§2.D) — zero residual freedom.
11. (NEW at REV 4) `zig`'s orientation (Codex-15) → RESOLVED: pinned at
   E-phase (`Denumerable.eqv ℤ` vs its `.symm` — one token, recorded).
12. (NEW at REV 5) the `MeasuredSide.Rep` instantiation (M-3 = Codex-1) →
   RESOLVED, RECORDED DESIGN DECISION: the PER-POOL representative family
   `Rep e τ := ∀ q₀, q₀ ∈ V.Pools → {x : S.Hist q₀ _ // S.zc x}` with the
   OFF-POOL EMPTY event branch (`cellEvt … q₀ N := ∅` at q₀ ∉ Pools) —
   SCOPE CORRECTED at REV 6 (Codex5-26): FORCED by the frozen UNGUARDED
   `xhd_no_orphan` (∀ (q₀ : ℚ)) only at h ∉ HDom; at h ∈ HDom the
   off-pool value is unconstrained and ∅ is the CHOICE (uniform;
   trivializes d4r0's off-pool instances). The
   Σ-typed one-pool alternative stays REJECTED (junk-valued guarded laws,
   underivable). Walk at V7-4a; rep_ne's choice step displayed.
13. (NEW at REV 5) `skBlk`'s species projection (the block-size datum) →
   RESOLVED: `s.sp.W * s.sp.D` (the cluster-size identity at the species
   layer); if MovesSp names the size field directly the def re-points
   there — one token, recorded (§2.C).
14. (NEW at REV 5) `castMoveT` and the Mathlib ratCast-family default
   fields of the F4/F8/F9 instances → RESOLVED: `castMoveT` DISPLAYED at
   REV 6 (§2.G, Codex5-28 — no longer a residual token); the ratCast
   default fields stay the one recorded Mathlib-mechanical remainder,
   zero design content.
15. (NEW at REV 6) the `cellEvt` DIMENSION branch (Fable G-B — the
   zero-freedom twin of slot 12) → RESOLVED, FORCED VALUE: `Hgt = Σ D,
   Hpt D` is pool-global and dimension-global, so `cellEvt` carries a
   SECOND dite on `h.1 = S.dim (moveOf …)`; the mismatch branch is ∅,
   FORCED by the frozen unguarded `xhd_no_orphan` (a wrong-dimension h
   is ∉ HDom — the Σ-embedded cdom carries the cell's own dimension;
   `univ` via `boxpos` would falsify the law). Displayed at V7-4a
   (+ the `cellEvtT` twin); V7-6a1's no_orphan roster carries the leg.

**Statement-fence inventory (changes needing sign-off):** none — every
structure above is new (additive); MovesS/MovesSp/MovesD are imported, never
edited. (The §4.3 re-keyings amend the SEAM CONTRACT's pins, which is that
contract's stated purpose — "NOT LEAN UNITS; re-keyed when the vocabulary
exists"; no frozen statement changes.)

**Non-vacuity anchors (the wave-2 doctrine, per package):** StepSys:
`cell_ne`/`zc_ne` + the REV-3 PRODUCTIVITY `out_ne` (the all-empty-fibers
adversary dies at the zc_ne witness — Codex-1) + the V1-8a realized
instance; XHD-w: positive weights are typed data (V0-1) + range lemma V1-1 +
V1-8a's witness; XHD-u (incl. T-twins): the rectangularity FALSITY witness
(V1-2(b)) + the (U-A)-does-not-imply-(u-R) fence V1-7 + V1-8a; XHD-d:
two-sided exactness against the note's OWN T_γ — the process-side mark
census `Tgam` (V1-3 — the REV-7/C6 slot-2 rule; the recursive
`chainCount` enters ONE-WAY only, via
`mem_chainCount_pos`; degenerate domains violate no_stray outright)
[REV 6, Codex5-32's "against the DEFINED counts" strike stands — Tgam is
NOT the recursive count; REV 7 keys to the note's direct count];
XHD-dC: two-sided exactness against the
defined CELL counts `cntc` (the cell face IS count-keyed; no HMC leak —
`tevt_last_iff` aligns the length-1 keyings, §2.G) + listed partition BY
TYPE (2.A) + V1-8b/c;
XHD-s (all three faces, WEIGHT-ONLY): the PROVED A2-format witness V0-4 +
V1-8b/c — and the count factors live in the [1v] burdens, so no package
field can silently decide INIT-RAT/(J-RAT) (Codex-8/9); the counting ties:
realized by V1-8c's literal census data (ent_card/evt_card/box_card/
stInst_card all checked on the toy); HMC: the false-instance/true-instance
pair V4-11 + V1-8b (REV 4: BOTH exist again — the false one couples the
free composite tevt, the ⊇ direction) + V4-12(c)'s fixed-system
factorization-failure fence + V4-12(b′)'s sum-level coincidence record;
HMCAug (REV 7, C4): satisfiable non-trivially BOTH relative directions —
TRUE at the ¬HMC coupled toy (V4-11(iii), the SEPARATION witness) and
implied by HMC (V4-13); falsifiability OPEN, no ¬HMCAug instance claimed
(the note's predicted falsifier: R2's wall channel);
templates: terminal-final BY CONSTRUCTOR (+ the T-twin fields throughout —
Codex-2); J: route-keyed roster with the GATE-NONZERO lemma (V5-7a — the
F-6 emptiness adversary dies) + the not-marked-T·G fence V5-7c; ε:
post-split distinctness V3-1 (selRank semantics, E8_rankInj) + WF
entry/eligibility/menu ties (C6), heights-retained discrimination V3-2;
ε̊: intrinsic finiteness V3-4; cell_refine: DERIVED with the count displayed
(V5-8 — the (q−1)² collapse adversary dies); gate: 100+ sealed numbers
re-derived (V6-1a..V6-4a) including the m_H3 = 0 falsifier, at all nine
census points, + the F-1 counting check 128 = (1/4)·512 (ent_card at gate
B).

**Honest-perimeter recap (what a corpus record may claim when all 98 build):**
CTS-M's clauses machine-checked EACH GIVEN EXACTLY its V.1-ledger set
(V7-2b, conclusions displayed at V7-2a); (U-A) proved given the typed §C
pack; the V-n3 displays re-derived in-kernel at all nine census points
(V6-4c's threshold conditional on the typed CoprimeLiftPack premise); the
MovesS seam supplied per §4 — with XHD (all faces incl. dC)/(XHD-u)/
(ENT-U)/HMC/ENT-COUNT/INIT-RAT-premises/(J-RAT)-cell-pack/
(ii-c)/CL-13-coverage/ContTwo/StageLawBurden/MDomTie/
MarkFiberTie all
OPEN, riding as typed arguments (REV 6: `SelRankTie` is OFF this list —
the σ_sel tie is now the definitional `SelMatches` membership, Codex5-23;
REV 7: `EntMassSummable` is OFF — struck, C7; `MarkDisj`/`MarkDisjT` are
OFF — V4-10's DERIVED lemmas, C8, with the within-cell card step the
carrier [tie] `evt_disj_assign`) —
the W17ii vacuity fence OWNER-SIDE OPEN (SF-2), and V7-8's W17ii sorry
the ONE banked open leg (C14 — no unconditional marking while it lives).
CLAUSE (v)'s record in particular: HMC typed, linked, probed by units both
ways (V4-11/V1-8b), and PROVED BY NOTHING — the REV-4 restoration,
completed at REV 5 for (HMC-AUG) at the TYPE level (the TE-pinned
RefEvents form — the rev-4 ∃-form was derivable, M-2) and CORRECTED at
REV 7 at the RECORD level (C4: V4-11's coupled toy is the SEPARATION
witness — ¬HMC ∧ HMCAug, one refinement round restoring factorization
per the note's own display; `HMC ⟹ HMCAug` is the REAL unit V4-13,
unavoidable for any faithful encoding of the note's conditional; NO
¬HMCAug claim survives; HMCAug's falsifiability OPEN — R2's wall channel
the note's predicted falsifier; all harmless while (v) is open). NOTHING
here is "the density R_σ": every mass is μ̂-typed or counting-native; the
marked→per-f conversion stays [3t]'s.

## §6 DISPOSITION TABLES

### §6.1 Round 1 → REV 2 (historical; the round-2 audits re-adjudicated
several of these rows — where a rev-2 "REPAIRED" was refuted, the governing
row is now in §6.2: C24 → F-1/F-3/F-4, C23's cellP leg → F-5, C8's roster →
F-6, C1/C2/C5/C6/C7/C9/C14/C15/C19/C21/C22/C25/C26/C28/C29 → Codex-round-2
1–20)

Codex findings C1–C29 (`MOVESV_AUDIT_CODEX_2026-07-28.md`), Fable findings
A-1–A-7 (`MOVESV_AUDIT_FABLE_2026-07-28.md`). "Fixed at" names the governing
section/unit of REV 2.

| # | finding (compressed) | disposition | fixed at |
|---|---|---|---|
| C1 | XHD packages vacuously inhabitable | REPAIRED: cell_ne/out_ne/zc_ne fields + per-structure witness unit | §2.B, V1-8, §5 anchors |
| C2 | cntraw/chain/cellEvt untied | REPAIRED: cntraw + chainCount are DEFS; cellEvt = assignment biUnion | §2.B, §2.G, §2.F |
| C3 | A2 exponent ∉ natural AffineE | REPAIRED: (t,u) declaration + chart-as-definition; display identity 2E = 3(h₀+h₂)−1 | §2.A convention, §2.I, V0-4, V6-2a/b |
| C4 | declaration order / invalid types | REPAIRED: VLabel→2.A; XHD bundle→2.G; GenKind inductive | §2.A/2.C/2.G |
| C5 | (D2) weakened to a String | REPAIRED: GenKind.rel carries relPoly; part_eq forces the twist | §2.C |
| C6 | EntShapeV triple untyped | REPAIRED: hentry/helig/hlen/hmenu WF fields; sibling law V3-1(b) | §2.D, V3-1 |
| C7 | V7-4 cannot produce MeasuredSide | REPAIRED: pool laws added; all fields defined from V + XHD; Cell granularity = outcome fibers; finE from V3-4 | §2.F, V7-4 |
| C8 | J tables not per-(τ,o) | REPAIRED: DCellO outcome-keyed; JCells/Jval/V5-7b per (s,m,o,α) incl. split | §2.F/2.H, V5-7a/b |
| C9 | V2-5 false as stated | REPAIRED: chainCount definitional; valB via u_R/u_T route; degree bound re-scoped to the path-product polynomial | V2-5 |
| C10 | V2-8 proves only zero-twist | REPAIRED: part_eq structural (twisted BY TYPE at a_eff ≠ 0); zero case a corollary | §2.C, V2-8 |
| C11 | V2-10 witness contradicts examples | REPAIRED: gate values recorded with true directions; synthetic Wstate > Wloc witness | V2-10 |
| C12 | V3-4 weakens finiteness | REPAIRED: intrinsic WF fields; finiteness proved OUTRIGHT, no premise | §2.D, V3-4 |
| C13 | V3-6 false iff | REPAIRED: iff struck; ≤ + one-directional equality + D10 tie | V3-6 |
| C14 | V3-8 underivable from XHDs | REPAIRED: XHDsEnt entrance face (sums of the DEFINED ιshH) + XHDdEnt | §2.G, V3-8 |
| C15 | V4-1 drops active-source guard | REPAIRED: guard restored; zero claimed only from active sources | V4-1 |
| C16 | V4-5 omits XHDw | REPAIRED: X : XHDw explicit; w_eq supplies the q^{−E} identification | V4-5 |
| C17 | V4-6 hypotheses undisplayed | REPAIRED: full signature displayed (pack + XHDw/d/s + four typed legs) | V4-6 |
| C18 | V4-8 gate fragment only | REPAIRED: ContTwo premise displayed (continuing size ≥ 2); gate decide + general lemma | V4-8 |
| C19 | V4-12 iff invalid | REPAIRED: extensional ⟹ STRUCK; ⟸ + machine-checked failure fence; adjudication recorded | V4-12 |
| C20 | census weakened to six primes | REPAIRED: F4/F8/F9 table fields; all nine points in-kernel | §2.I, V6-1c, V6-3b |
| C21 | CoprimeLiftPack unauditable | REPAIRED: fields displayed (unique coprime lift + determinacy, nothing stronger) | §2.I |
| C22 | CtsmConclusions opaque | REPAIRED: field list displayed incl. VAL(b), INIT-RAT, ACTIVE-VALUE record, count shadow, solve sentence | V7-2 |
| C23 | V7-5 legs type-wrong | REPAIRED: tgP gains the G-bearing face; ιP per-component (V3-9c(a)); cellP re-keyed to CellPolyPack | V7-5, V3-9c |
| C24 | V7-6 fields unsupplied | REPAIRED: μcell/gwt/rowVal/kstep DEFINED from XHD; cell_refine; init_count/comp_once re-keyed | §2.F/2.G, V7-4, V7-6 |
| C25 | SCSData dropped; KmatHyp misattributed | REPAIRED: SCSData row field-by-field (data ← species fields; laws ← gate decide + [2a] burden); KmatHyp = Prop, proved at gates | §4.1, V7-3 |
| C26 | S-8 vacuous; xhd_s missing | REPAIRED: wsh_xhd_s_stmt delivered; Sh-nonemptiness routed to [3t] tree_ne via S-5 | V7-7, §4.3 |
| C27 | XHD re-keyed as unrelated fragments | REPAIRED: ONE xhdStmt = Nonempty (full bundle); all four fields re-keyed to it | V7-7, §4.3 |
| C28 | units conceal multiple declarations | REPAIRED: lemma-roster format amendment; rosters displayed at V0-2/V2-1/V2-2/V6-4a (+ others) | §3 preamble |
| C29 | placeholders unauditable | REPAIRED: every named carrier displayed; checklist | §2.J |
| A-1 | entrance carrier granularity broken | REPAIRED: EntIx (template × component); ιDom/ιshH/ιsh/ιval defined; hent ADJUDICATED + seam flag SF-1; per-component PolyGeoms exposed; init_count re-keyed | §2.F/2.G, V3-8/9c, V7-4/6 |
| A-2 | chain recursion has no carrier | REPAIRED: StepSys.ext (normative Defs amendment); chainCount definitional | §2.B/2.G |
| A-3 | WordBounded under-pinned; EntranceShape unused | REPAIRED: intrinsic WF fields incl. menu bounds; V3-3(c) constructs the MovesSp.EntranceShape | §2.D, V3-3, V3-4 |
| A-4 | V6-1c f″ sketch false at p = 2 | REPAIRED: char-free divisibility multiplicity | V6-1c |
| A-5 | design-freedom inventory incomplete | REPAIRED: all five slots listed AND resolved | §5 inventory |
| A-6 | §0 banner overstates V6 | REPAIRED: V6-4c scoped out by name; census scope stated | §0 |
| A-7 | dangling-display cluster | REPAIRED: u_T_dom pointer removed; HMCAug displayed; V1-7 ∃-nested; V0-1 binds h; IsPP defined; eligibility ties added; §4.2 pointers fixed | §2.A/2.B/2.G, V0-1, V1-7, §4 |

### §6.2 DISPOSITION TABLE (round 2 → REV 3)

(HISTORICAL at REV 4 — where round 3 re-adjudicated a rev-3 "REPAIRED" row,
the governing row is now in §6.3: X-14's ∀-weight iff → Y-8; the F-3/X-10
AStep disjointness → Y-3; X-5's selRank pin → Y-4; X-4's count layer →
N-2/Y-1; the C2/A-2 chainCount-exactness keying → N-1; X-17's Wsh17 type →
Y-11; X-7's hent half → Y-6; C27's one-Prop re-key → Y-10.)

Codex round-2 findings 1–20 (`MOVESV_AUDIT_CODEX2_2026-07-28.md`; cited as
X-1..X-20), Fable round-2 findings F-1–F-6 / G-1–G-4
(`MOVESV_AUDIT_FABLE2_2026-07-28.md`). "Fixed at" names the governing
section/unit of REV 3. The gate numbers the audits supplied are the
acceptance tests and are checked at the named sites.

| # | finding (compressed) | disposition | fixed at |
|---|---|---|---|
| F-1 | ιshH body = ι·q^{n·entLvl−A} (event card, not census; gate 8192 ≠ 128) | REPAIRED: entInst census carrier + ent_card counting law; ιshH := census·q^{−A}; gate check 128 = (1/4)·512 displayed | §2.F (entInst/ent_card/box_card), §2.G ιshH, V7-6a |
| F-2 | entCount = box-event card; ι_count+ι_degT+degT_le jointly unsatisfiable | REPAIRED: entCount := the census (deg 2 ≤ Went 3 at gate); EntCount per CONCRETE ε against entCensus; EntU over the census | §2.F entCount, V3-9a/b, V7-4b |
| F-3 | meas_card/no_stray/no_orphan/d4r0 have no derivation AS TYPES | REPAIRED: evt_card + box_card [tie fields]; XHDdC cell d-face; ONE AStep disjointness law (cross-move/height/assignment/terminal) — suite derivable field-by-field | §2.F, §2.G XHDdC, V7-6a |
| F-4 | cell_refine forces T ≡ 1 ((q−1)² adversary); kstep drops ∏T | REPAIRED: XHDsC weight-only; cell_refine a DERIVED unit with the count displayed (Σ P_c·ΣGcell = T·ΣGc); kstep := Σ (pathProdPoly).eval·ΣGc | §2.G XHDsC, V5-8, V7-4c |
| F-5 | cellP ← CellPolyPack regression (cellP_deg broken at both gates; act_iff false at q₀ = 2) | REPAIRED: REVERTED to the rev-1 sizeP wiring; stLvl/stInst/stInst_card state-census fields added; ActIff premise deleted (act_size suffices) | §2.F, V7-4a, V7-5(d) |
| F-6 | roster_tie (emult ≥ 2) empties every n = 3 roster; Jval ≡ 0 | REPAIRED: route-keyed bcells (ALL cells of a split-route outcome, once); gate-nonzero lemma; V5-7c's algebra re-keyed with its roster premise displayed | §2.H, V5-7a/c, V7-3a (route_eq) |
| X-1 | out_ne forbids empty menus yet admits all-empty Assign models | REPAIRED: out_ne re-keyed to realized-history PRODUCTIVITY (menus may be empty; unrealized models violate it at zc_ne's witness) | §2.B |
| X-2 | terminal-final steps missing from XHDu/C15Pack/events/cells | REPAIRED: T-twins typed throughout via the displayed substitution table (XHDu ×3, C15Pack ×2, CtsMeasured events/domains/classifiers, XHDsC GcellT, XHDdC, CellPolyPack.countT, ValA.tbl_countT, Refinement twins) | §2.B convention + per-structure fields |
| X-3 | relPoly decorative; tcell not forced on moveOf | REPAIRED: GenSpec.rel_eq (partition factors through the polynomial) + twist_add (ℤ-action); moveOf target = d.tgt BY TYPE with moveOf_bij over MoveData | §2.C, §2.F |
| X-4 | tbl_count weak at zeros + smuggles (u-T); V2-5 unconnected to C.T | REPAIRED: base-point-keyed unguarded tbl_count; valB restated against (pathProdPoly C γ).eval q₀ with ValA+u_T route | V2-4, V2-5 |
| X-5 | selRec entries unrelated to actual selections | REPAIRED: σ_sel pinned as the L11 selRank data (definitional at the label; E8_rankInj at instances); V3-1(b) re-scoped; EligPair/IsBranchingRead/branchMenuCard closed over named MovesD decls | §2.D, V3-1 |
| X-6 | template lossy (bijection false); no_orphanE lacks landing | REPAIRED: V3-3(d) readOfLetter + spWord_faithful (reconstruction as a THEOREM, hatch recorded); writeHeights displayed; XHDdEnt.lands_of_realizable | §2.D, §2.G, V3-3/V3-5 |
| X-7 | EntIx collapses ENT-COUNT to base point; hent scalar | REPAIRED at the count: EntCount per concrete ε (census); base-collapse only in entCount's DEF with (ENT-U) cited at consumption. hent: ADJUDICATED-RETAINED (round-2 auditor disagreement resolved on Fable's source verification; SF-1 stands, re-opened iff a MovesS law ever reads hent) | V3-9a, §2.F, V7-4b |
| X-8 | XHDsEnt assumes INIT-RAT + double count in V3-9c | REPAIRED: Gent weight-only; counts enter via EntCount/(ENT-U); V3-9c countT×geom now counts once; V3-8 displays the (ENT-U) premise (adjudication recorded) | §2.G, V3-8, V3-9c |
| X-9 | cell_refine arithmetic wrong; V5-7b count-squared | REPAIRED: = F-4 + jRat over weight-only Gcell × CellPolyPack (no re-multiplication) | §2.G, V5-8, V5-7b |
| X-10 | events untied to LedgerIV (no card law; evt_disj same-h only; cdom unexact) | REPAIRED: = F-3 (evt_card/AStep disjointness/XHDdC) | §2.F/2.G, V7-6a |
| X-11 | kstep omits transition counts | REPAIRED: kstep carries (pathProdPoly).eval — kstep_one = V5-8's identity | V7-4c, V7-6b |
| X-12 | V2-7 cells overlap at (0,0) | REPAIRED: FL/FS with nonzero coordinate; partition of the nonzero target; origin lemma separate | V2-7 |
| X-13 | HMCAug satisfiable by an unrelated refinement | REPAIRED: Refinement fully typed (moveProj/dim_eq/assignOf/mass_eq/assign_cover Σ-bijection + T-twins); count laws now lemmas | §2.G |
| X-14 | V4-12 weakens the frozen IF AND ONLY IF | REPAIRED: the iff RESTORED at the ∀-weight-system quantifier — ⟸ proved, ⟹ = the generating-series separation (HARD, split); single-system fence retained as (c) | V4-12, §0 banner |
| X-15 | iota_supp under-hypothesized | REPAIRED: ValA.ent_supported (the note's own landing sentence); iota_supp derivable | V2-4(d), V4-1 |
| X-16 | cellP unsuppliable from CellPolyPack; no cellLvl/cellInst | REPAIRED: = F-5 (sizeP revert + stLvl/stInst/stInst_card); CellPolyPack retained ONLY for (J-RAT)/V5-8, closed and domain-keyed | §2.F/2.H, V7-5(d) |
| X-17 | Wsh17 xhd_s not expressed as a type; S-5 routing contradictory | REPAIRED: Wsh17PackageV displayed AS A STRUCTURE (wsh_xhd_s a field); the empty-menu leg re-scoped to SEAM FLAG SF-2 (owner-side OPEN — no closure claimed) | V7-7, §4.3 |
| X-18 | placeholder checklist not closed (7 named clusters) | REPAIRED: every named item displayed closed — Refinement (no `…`), CellPolyPack, CtsmConclusions (V7-2a structure), CoprimeLiftPack (reduce2; determinacy by type), MoveData/TermData/dataOf, writeHeights, Hpt.take/drop, emult (a field), moveOfT_bij, F4/F8/F9 tables, EligPair-cluster named-keyed | §2.J (the audit trail) |
| X-19 | V1-8/V7-2/V7-3(d)/V7-4/V7-6 conceal multi-lemma constructions | REPAIRED: split into V1-8a/b/c, V7-2a/b, V7-3a/b/c/d, V7-4a/b/c, V7-6a/b/c — census 82 = 33/43/6 | §3, §5 |
| X-20 | general SCSData/KmatHyp supply untyped | REPAIRED: StageLawBurden (closed structure, all twelve laws + kmat_all + degcons_all), a CtsmLedger field; gate restriction by decide | V7-3d, V7-1, §4.1 |
| G-1 | E = 6t+3u+1 misattributed to the note (×2 + moves_ref splice) | REPAIRED: both sites + V0-4's moves_ref corrected — ours, derived; note displays (3(h₀+h₂)−1)/2 + the substitution | §0, §2.I, V0-4 |
| G-2 | x²+1 over F₃ called a Conway polynomial | REPAIRED: provenance corrected (C_{3,2} = x²+2x+2; ours is merely irreducible) | §2.I |
| G-3 | u*-slot ℚ/ℕ encoding unpinned | REPAIRED: zig(gam) slot code + gamTie inversion, displayed; hatch recorded; V3-5(c) checks the roundtrip | §2.D, V3-3(d)/V3-5 |
| G-4 | V3-6(c) cites a proof-internal `key` | REPAIRED: re-pointed to exported D4R1_SUM/D0b_thmCtop (also ent_card's discharge cite) | V3-6, §1, §2.F |

VERIFIED-CLEAN CORES (both round-2 audits) LEFT UNTOUCHED, as charged: the
A2 chart complex (§2.I/V0-4/V6-2a/V6-2b — re-derived independently by both
auditors), the doctrine core (cell_ne/zc_ne/cntraw/chainCount/ext), the
EntIx carrier TYPE itself, the V6 gate layer (V6-1a..V6-4c incl. censusQ,
the m_H3 falsifier, the two-history discipline, the A-4 char-free
multiplicity), and the §4 field lists verified verbatim against the built
MovesS sources.

### §6.3 DISPOSITION TABLE (round 3 → REV 4)

(HISTORICAL at REV 5 — where round 4 re-adjudicated a rev-4 "REPAIRED"
row, the governing row is now in §6.4: N-2/Y-1's seam leg → M-3 =
Codex-1/14; Y-2's odata/TargetIx legs → Codex-2/3; Y-3 → Codex-4/5;
Y-4 → Codex-6; Y-6's injectivity gloss → Codex-7/G-2; Y-7's XHD-s
strengthening → Codex-8; Y-10 → Codex-11; Y-14/Y-15 → Codex-15/16;
Y-16's V7-2a leg → Codex-17; N-1's HMCAug leg → M-2; the M-1 tbl_count
row is a FRESH round-4 finding on a display this table never touched.)

Codex round-3 findings 1–17 (`MOVESV_AUDIT_CODEX3_2026-07-28.md`; cited as
Y-1..Y-17: 13 critical + 4 gap), Fable round-3 findings N-1/N-2/N-3 +
G-1/G-2 (`MOVESV_AUDIT_FABLE3_2026-07-28.md`; that audit also re-ran all
six round-2 F-refutations — ALL DEAD — and verified the byte-stability of
the round-2 clean cores, which is what certified Y-1/N-2 and N-1 as
INHERITED defects). "Fixed at" names the governing section/unit of THIS
revision. Where a Codex finding met a Fable verified-clean row, the row
carries the TWO-VERDICT COMPARISON with the computed evidence.

| # | finding (compressed) | disposition | fixed at |
|---|---|---|---|
| N-1 = the HMC collapse | XHDd's chainCount-keyed exactness PROVED the open kernel (4-line proof); V4-11/V4-12(c) unsatisfiable; (v)-conditionality defeated | REPAIRED PER THE ORCHESTRATOR ADJUDICATION (campaign ledger, N-1/HMC entry — the note-side flag was adjudicated NOTE-INTACT, blueprint over-commitment): table side (chainCount, G) stays recursive-by-definition; process side H(γ) DEFINED from realized marked events (`TmplEvents`/`TReal`, the COMP vocabulary MOVES 8225–8232 quoted); XHDd exactness re-keyed to TReal; HMC = the typed link, quoted verbatim (MOVES 8198–8204), underivability audited in §2.G (one-way count supply only; no composite ties); V4-11 re-keyed process-side (coupled toy, satisfiable); V4-12(c) satisfiable; every (v)-tag restored (V5-5's hHMC undischargeable; V7-6c note) | §2.G (TmplEvents/TReal/XHDd/HMC/HMCAug), V1-3, V4-11, V4-12, V7-6c, §0 |
| N-2 = Y-1 (CONVERGENT: both auditors, same defect) | pool-free Hist/Assign/cntraw/cntc force constant count polynomials (T21: eval 2 = 2 ≠ 6 = eval 3); valA_gate FALSE; CellPolyPack/ValA/valB/tgt_supported/cellEvt-cluster unsatisfiable; XHDu's cross-prime horn | REPAIRED: the history layer is POOL-INDEXED (`Hist : ℚ → Cell → Type`; Assign/cntraw/cntc/massOf/chainCount/evtOf/cellEvt ride the history's pool — the census carriers' box-side move extended one layer down, as the round-3 hint prescribed); XHDu compares SAME-POOL histories only (the two-horn closure); the T21 2-vs-6 acceptance check DISPLAYED at V2-4, the (X−1)² 1-vs-4 check at §2.H | §2.B, §2.F, §2.G, §2.H, V2-4, V2-5 |
| N-3 | kstep has no k = 0 case: template-sum gives kstep 0 ≡ 0, falsifying the frozen LedgerIV.hmc at k = 0 | REPAIRED: `kstep 0 τ β q₀ := if τ = β then 1 else 0` (Kronecker δ — empty path: ∏T = 1, empty height sum = 1); the frozen ∀-k law's k = 0 instance is the δ-collapse, hypothesis-free; the built-instance cite (N2Carriers 101–105) displayed | V7-4c |
| Y-2 | continuing/terminal keyed to Letter; V.6.3's m₂ has terminal o_split/o_inert AND continuing o_double — unrepresentable | REPAIRED: outcomes moved into `BlockData` (`Outc : Letter → Type`); `cont`/`tgtSk`/`tgt_menu`/`tcell`/`T`/`vlabOf`/`TargetIx`/`MoveData.hc`/`TermData.ht` all re-keyed per (letter, OUTCOME) — m₂'s three outcomes type as one letter, two TermData + one MoveData | §2.C |
| Y-3 | evt_disj claims ordinary-box disjointness across continuation marks; the note allows equal f-projections and offspring mass > 1 | REPAIRED: `evt_disj_cell` — disjointness EXACTLY at distinct DIGIT-CELL KEYS (letter, outcome, cellOfA-class, height; terminal included); cross-mark pairs excluded (nothing claimed); the within-cell sum meas_card needs is the NAMED displayed burden `MarkDisj` (decide at the n = 3 gates via emult ≤ 1; open beyond — exactly PART-2's surplus territory); d4r0's supply re-derived (the frozen field is (c,h)-keyed — never cross-mark); V4-10's equal-projection witness now jointly satisfiable with the carrier | §2.F, V7-6a1/a2, V4-10 |
| Y-4 | selRec entries are bare bounded naturals — no tie to the selected continuation or MovesD.selRank | REPAIRED: `hrank` FIELD (entry = `shapeRank` of `takenGm`, the continuation the prefix actually takes — successor read's (g,μ) / entry selection at the last); value-level identification stays the E7/E8 cite (MovesD Defs 522-523's Fin m̄ collapse, quoted); enumeration-order hatch recorded | §2.D |
| Y-5 | mdom untied to XHDd's length-1 domain; u_T transport broken (V2-5/V4-5/V5-8/tg_interp) | REPAIRED: `MDomTie` (mdom_eq/mdomT_eq) — a displayed coherence structure, EXPLICIT premise of every base-point transport; base realizability derived (mdom_eq + no_stray + mark facts) | §2.G, V2-5, V5-8, V7-5a |
| Y-6 | hent supplied by a lossy scalar (Σ of base coordinates) | PARTIALLY ADOPTED + TWO-VERDICT RECORD: the VALUE is upgraded to the INJECTIVE `hentCode` (Nat.pair-fold over retained (h_r, zig(γ_r)) — no identification of distinct heights); the STRUCTURAL half is owner-side and stays SEAM FLAG SF-1 — Fable round-3 §B held SF-1 HONEST on computed evidence, re-verified at REV 4 by fresh grep: `hent` in built MovesS = Defs.lean 179 (declaration) + N2Carriers.lean 118 (device `:= 0`) + one comment, NO law reads it; RS1Meas.βmeas's h_ent is its OWN ℕ argument (its h_ent-INDEPENDENCE is W2_xrb's CONCLUSION), not a `MeasuredSide.hent` read. Codex's faithful-supply demand adopted; its "expressly use" premise corrected by the grep | V7-4b, §4.3 |
| Y-7 | ENT-AGG strengthened by an (ENT-U) premise; the note gives convergence from XHD-s (shallow) alone | REPAIRED: V3-8 SPLIT — V3-8a (the note-exact aggregation: convergence from the NEW shallow mass-summability face `XHDsEnt.mass_summable`, summability only so INIT-RAT is decided by nothing; exactly-once structure proved; NO (ENT-U)) + V3-8b (the ιval identification, where (ENT-U) enters — the note's own INIT-RAT line lists it) | §2.G (mass_summable), V3-8a/b |
| Y-8 | V4-12's iff quantifies over EVERY positive-affine E-family; the note fixes the actual XHD weight system | REPAIRED AT THE NOTE'S EXACT QUANTIFIER (the round-3 directive: match exactly): (a) the IF leg proved at the FIXED system (`Factorizes X D`, ∀-template — supplies V5-5); (b) the ONLY-IF leg carried as the NAMED process-scoped statement `UpgradeOnlyIf`, CONSUMED BY NOTHING, its interface-derivability recorded OPEN-UNCLAIMED, with (b′) the machine-checked SUM-LEVEL coincidence (the E-multiset toy {(0,0),(1,0),(0,1),(2,0)} vs {0,1}², sums (1+q₀⁻¹)² both — displayed arithmetic; the naive full-instance lift dies against marks_chains, computed and recorded); (c) the failure fence at the false-HMC toy (¬HMC ∧ ¬Factorizes). The ∀-E quantifier and the generating-series ⟹ leg are GONE; V4-12 de-escalates HARD → medium. TWO-VERDICT NOTE: Fable round-3 §B independently found rev 3's iff OVERTAKEN by N-1 and its adjudication line wrong — both verdicts land in this restatement | V4-12, §0 |
| Y-9 | tgt_supported lacks the active-source premise (stronger than (ii-a)) | REPAIRED: the ValA FIELD now carries `activeState q₀ (src)` + zc guards (the note: "for every source active at q₀ …"; inactive-source rows stay formal junk at both layers); V4-1's derivation re-checked under the guard; `ent_supported` keeps no source guard (the entrance leg has no source state — note text quoted) | V2-4(c), V4-1 |
| Y-10 | XRB re-key strengthens each premise to the full bundle | REPAIRED BY THE AUDIT'S OWN REMEDY: ONE SHARED package parameter `X : XHD …`; the four field names = FACE PROJECTIONS (xhd_w ↦ X.w, …) — coherence by sharing (C27 kept), per-face accounting preserved, no premise strengthened; `xhdStmt` survives only as V1-5's discharge Prop | V7-7, §4.3-1, §4.2 |
| Y-11 | Wsh17PackageV drops c15_volumes/sib_count (comments ≠ fields) | REPAIRED: full frozen three-field roster IN THE TYPE — owner legs as Prop PARAMETERS (c15V : §C/HC-2, sibC : [3t]/CL-10; inhabitation owner-side), cts_counts MovesV's, the xhd_s face as the shared parameter's projection; SF-2 (Fable-verified HONEST) unchanged | V7-7, §4.3-2 |
| Y-12 | XHD-w/u quantify over non-realizable histories (no zc premises) | REPAIRED: `S.zc` guards on w_eq/wT_eq and all six XHDu fields (the C15Pack.mass_factors pattern, uniform); XHDd/XHDdC exactness zc-guarded in the same sweep | §2.B, §2.G |
| Y-13 | V6-2b's moves_ref still splices "= 6t+3u+1" | REPAIRED: the splice DELETED from the quotation; the derived form lives only in the statement body, marked ours | V6-2b |
| Y-14 (gap) | placeholder checklist materially open (gProd `…`, twin comments, F4 `…laws`, F8/F9 undisplayed, StageLawBurden ellipses, …) | LARGELY REPAIRED: gProd's recursion displayed; cellEvtT/cntcT displayed; the F4 instance skeleton displayed with per-law decide (no `…laws`); F8/F9 add/mul tables PASTED (computed this revision); StageLawBurden's TWELVE LAW FIELDS TRANSCRIBED IN FULL against the verbatim MovesS.SCSData statements (V7-3d); CellIdx moved into Defs; §2.J re-inventoried. REMAINING (recorded, not hidden): the `*_Stmt` defs of V7-2a stay transcription-rule-bound, and the cast/menu helpers stay recorded one-liners — each in §5's inventory with zero design content | §2.D/2.F/2.G/2.I/2.J, V7-3d |
| Y-15 (gap) | declaration order / Lean-plausibility (CellIdx, Realizable, zig orientation, ringV instance) | REPAIRED: `BlockData.CellIdx` a Defs def before TargetIx; `Realizable` moved before XHDdEnt; `rel_eq` displays the `letI := ringV q₀` install; zig's orientation pinned as a recorded E-phase token (inventory slot 11) | §2.C, §2.D, §2.G |
| Y-16 (gap) | "pre-approved split" without unit IDs/files conceals multi-lemma units | REPAIRED for the five named suites: V3-3a/b/c/d, V3-5a/b/c, V4-6a/b/c, V5-2a/b/c, V7-5a/b/c — real IDs, own files, own grades (census 95 = 32/59/4); V7-1/V7-2a REMAIN single structure-declaration units BY DESIGN (one structure = one display; V7-2a's `*_Stmt` fields are rule-bound transcriptions, not lemmas) — recorded as the residual disagreement, with the rationale displayed | §3, §5 |
| Y-17 (gap) | seam table not field-complete (fin/deq/finV/finO/finC/decA/nonemptiness carriers unmapped) | REPAIRED: an explicit MECHANICAL-INSTANCE-FIELDS row added to §4.1 naming every such field with its supplier unit and derivation source; StageLawBurden's role unchanged (its law fields are V7-3d's, not instance fields) | §4.1 |
| G-1 (Fable) | V7-5(d)'s act_iff collapse silently needs Nonempty (Cell e τ) | REPAIRED: the `cell_ne_inst` roster lemma DISPLAYED (zc_ne → out_ne productivity → cellOfA/cellOfAT through the bijections) — part of V7-5c | V7-5c |
| G-2 (Fable) | V7-6a bundles six supply legs against the ≤ 4-lemma roster rule | REPAIRED: split into V7-6a1 (cell suite: meas_card + two exactness legs) and V7-6a2 (d4r0 + init_count + ent_count_card), each an enumerated ≤ 3-lemma roster | V7-6a1/a2 |

ROUND-3 CROSS-CHECKS HONORED: Fable's §A re-ran all six round-2
F-refutations against rev 3 and found them DEAD (F-1's 128 = (1/4)·512,
F-2's degree ledger, F-3's typed suite, F-4's (q−1)² identity, F-5's
revert, F-6's route roster) — REV 4 leaves those wirings intact except
where the N-1/N-2/Y re-keys pass through them (each such touch is a row
above); Codex's round-2 disposition census (17 REPAIRED) is superseded row
by row by this table where it disagreed, with the convergent finding (Y-1
= N-2) repaired once. The A2 numerical core and gate-B arithmetic were
re-confirmed by BOTH round-3 auditors and are UNTOUCHED at REV 4.

### §6.4 DISPOSITION TABLE (round 4 → REV 5)

(HISTORICAL at REV 6 — where round 5 re-adjudicated a rev-5 "REPAIRED"
row, the governing row is now in §6.5: Codex-2's selected-target residue
→ Codex5-22; Codex-4's key → Codex5-21; Codex-6's SelRankTie →
Codex5-23; Codex-11's adapter target → Codex5-25; Codex-17's bodies →
Codex5-27; M-2's record half → G-A; M-3's "forced" wording → Codex5-26;
G-1's status → Codex5-31.)

Codex round-4 findings 1–18 (`MOVESV_AUDIT_CODEX4_2026-07-28.md`: 13
critical + 5 gap), Fable round-4 findings M-1/M-2/M-3 + G-1/G-2
(`MOVESV_AUDIT_FABLE4_2026-07-28.md`; that audit also VERIFIED all three
round-3 adjudicated repairs LANDED — the four-line HMC proof re-run FAILS
against the TReal-keyed XHDd, both N-2 gate refutations dead, kstep's
k = 0 δ correct against the frozen law and the built device instance,
V4-12 at the note's exact quantifier — and re-armed all six round-2
F-refutations, ALL DEAD). Convergent finding: Fable M-3 = Codex-1 +
Codex-14 (the incomplete pool ripple), repaired once. "Fixed at" names
the governing section/unit of THIS revision.

| # | finding (compressed) | disposition | fixed at |
|---|---|---|---|
| M-3 = Codex-1 + Codex-14 (CONVERGENT) | the pool ripple missed three displays: V1-6/V1-7 still pool-free (don't elaborate); V7-4a's `Rep e τ := {x // S.zc x}` leaves the pool unbound — the frozen POOL-GLOBAL `MeasuredSide.Rep`/`cellEvt` cannot be instantiated | REPAIRED: V1-6/V1-7 re-signatured to the pooled Hist/massOf (mechanical); V7-4a re-keyed to the PER-POOL REPRESENTATIVE FAMILY `∀ q₀, q₀ ∈ Pools → {x : Hist q₀ _ // zc x}` with the OFF-POOL ∅ `cellEvt` branch — the resolution the frozen UNGUARDED `xhd_no_orphan` forces, a RECORDED design decision (inventory slot 12); rep_ne's per-pool choice displayed; the frozen-instantiation typecheck WALKED field-by-field at V7-4a (Rep/rep_ne/cellEvt/guarded suite/unguarded no_orphan/d4r0); V7-6a1's off-pool leg now explicit | V1-6, V1-7, V7-4a, V7-6a1, §5 slot 12 |
| M-1 (Fable, crit — inherited since rev 2) | `ValA.tbl_count` binds β FREE with a β-independent RHS: every TargetIx entry (junk terminals included) forced equal to the datum's count; `valA_gate` FALSE at the note-correct family (0 = 2 at q₀ = 2) | REPAIRED: β BOUND to the datum's own index `MoveData.tix`/`TermData.tix` (new §2.C defs — exactly V2-5/V5-8/V7-4c's object); junk terminal columns killed BY TYPE (`TargetIx.term` requires ¬cont — the round-4 refutation instance no longer types); the off-key entries pinned to their note-correct value 0 (`tbl_offkey`/`tbl_offkeyT` — VAL(a)'s "every entry valued correctly"; the cooked-junk family now violates a field, doctrine restored); V4-1's β/βc tie made explicit (the datum's column) | §2.C (tix/TargetIx), V2-4(a)/(a′), V4-1, V2-5, V5-8 |
| M-2 (Fable, crit — round-3 N-1's residue) | `HMCAug` DERIVABLE from the XHD d-face: the identity-refinement + cooked-composite-events witness satisfies the ∃ at every instance — the §2.G "unrelated witness stays impossible" comment FALSE | REPAIRED: HMCAug takes the ledger's `TE` as a PARAMETER; the refined events PINNED through the new `RefEvents` (boxEq + tevt_cover/tinst_cover — a refinement RE-PARTITIONS the base marked events by boundary/gap data, per the note display MOVES 8213–8220, quoted at the def site); the cooked witness RE-RUN and DEAD (boxEq kills PUnit boxes; tevt_cover forces TE' = TE at the identity refinement, reducing the witness to HMC TE D itself); `refTmpls` displayed closed; the false comment struck, the honest audit displayed | §2.G (refTmpls/RefEvents/HMCAug), §0 banner |
| Codex-2 | `TableShape.odata` unconstructible: no member-data carrier exists (DegCons is a law, not data) | REPAIRED: the OUTCOME-MEMBER ROSTER `omem : List (OMember n)` (+ omem_ne/omem_size/omem_kcol, `skBlk`) is BlockData DATA; per-member landing maps `tcellM` (+ tcellM_tgt) at CtsFamily; V7-3a's odata map DISPLAYED (sizes/δ verbatim, terminal statuses through vEquiv, continuing statuses = roster skeleton + tcellM cell, `Outcome.hm` ← omem_ne); V2-9's DEG-CONS gets its typed referent | §2.C, V7-3a, V2-9 |
| Codex-3 | `TargetIx.term` admits terminal columns for CONTINUING outcomes; `tgt_menu` (isLeft) does not pin the successor skeleton | REPAIRED: `term` gains `(ht : ¬ cont)` — junk terminal columns gone BY TYPE; `tgt_sp : letterSp m = Sum.inl (tgtSk m o h).sp` pins the (D4) target block to the letter's OWN successor species (the note's (CTS-T): "species m : s → s′ … β ∈ JREF^src(s′)"); the member-roster laws (omem_size/omem_kcol) tie the skeleton data down | §2.C |
| Codex-4 | `evt_disj_cell`'s key includes the whole datum — distinct move/outcome-represented continuations get disjointness the note denies | REPAIRED: the key MINIMIZED to the frozen d4r0's own pair — (Σ-embedded digit cell, Σ-embedded height), NO datum coordinate beyond the cell's type index; within-cell mark differences (which assignment, which continuation) have EQUAL keys — nothing claimed; distinct keys = the D4R.0/PART-1 partition face exactly | §2.F (stepKey) |
| Codex-5 | `MarkDisj` has no TermData twin — terminal cells lack meas_card support | REPAIRED: `MarkDisjT` DISPLAYED (§2.F, the substitution-table twin); V7-6a1 takes `hMDT` as a displayed premise and its meas_card derivation names the terminal half; a CtsmLedger field | §2.F, V7-6a1, V7-1 |
| Codex-6 | `shapeRank` an independently-invented enumeration with no typed tie to `MovesD.selRank` (the identification only prose + a hatch) | REPAIRED: the TYPED coherence structure `SelRankTie` (§2.D, the MDomTie pattern) — `selRank … % mbar = shapeRank … (nodeAt i r).g,μ` at every presented prefix and branching read — a DISPLAYED premise of V3-1(b) and V5-1 (never a background assumption); E8_rankInj cited for distinctness through the tie; `eligMenu` now a displayed closed def, so the lex enumeration is auditable; the hatch is TYPE-ARMED (order mismatch ⟹ the tie is unsatisfiable ⟹ shapeRank re-keys at MovesD, fresh audit) | §2.D (SelRankTie), V3-1, V5-1, §5 slot 10 |
| Codex-7 (+ Fable G-2) | `hentCode` not injective as glossed (zero-seeded fold collides across read counts; gam-not-ustar; e/STR/s0/wSide unencoded) | REPAIRED: LENGTH-SEEDED fold (injective on the retained (h, γ)-tuple lists — displayed argument); the gloss SCOPED honestly (u* recovery via gamTie needs template-fixed data, which the seam's per-(template, component) consumption fixes; no ∀-ε claim); the standing fact re-recorded: NO MovesS law reads hent (SF-1) | §2.D, V7-4b |
| Codex-8 | `XHDsEnt.mass_summable` silently STRENGTHENS frozen XHD-s and assumes V3-8a's conclusion by hypothesis-field | REPAIRED: the field REMOVED; the premise is the NAMED standalone burden `EntMassSummable` (EntCount/EntU pattern — statement-only def), a DISPLAYED theorem premise of V3-8a, owner-[2b] shallow per the ledger line; XHDsEnt is weight-only again; realized on V1-8c's toy | §2.G, V3-8a, V1-8c |
| Codex-9 | V5-2a/c drop the frozen ledger's explicit XHD-w premise (w_eq consumed but unlisted) | REPAIRED: XHD-w (`w_eq`) named in V5-2a's and V5-2c's hyp_fields — "XHD-w's (U-A) face + (XHD-u)" verbatim; V4-5's dependency noted as NOT discharging it | V5-2a, V5-2c |
| Codex-10 | V5-7b quantifies `d : MoveData` — cannot supply the frozen per-(e,τ,o) `jP` at general split outcomes (no chosen continuing target exists there) | REPAIRED: jRat re-keyed to the BARE OUTCOME quantifier (s, m, o, α) + route = split; the datum built through the new `JCells.route_cont` (split ⟹ c ≥ 1 ⟹ cont); Jval factors through the quadruple by the definitional `jval_out` (V5-7a — tgt/tcell/hc read nowhere) | §2.H (route_cont), V5-7a, V5-7b |
| Codex-11 | the XRB re-key maps Prop-typed frozen fields to STRUCTURE values — not a Lean mapping | REPAIRED: the DISPLAYED Prop-typed adapter — `XHDFrame` (the shared data halves) + the four face-law `*_Stmt` ∀-closures + `xrbPackageOf : … → MovesS.XRBPackage` (a def INTO the frozen type; the nine non-xhd fields stay owner Prop parameters) + `frameOf`/`xhd_faces_of` (the discharge direction); coherence by the one frame, per-face accounting kept | V7-7, §4.2, §4.3-1 |
| Codex-12 | `StepSys.Pools = ∅` satisfies every pool-guarded law vacuously | REPAIRED: `pools_ne : Pools.Nonempty` field; V1-8a instantiates it | §2.B, V1-8a |
| Codex-13 | `StageLawBurden.kmat_all` demands KmatHyp at EVERY ℕ index — strictly stronger than the frozen `∀ e ∈ Icc 1 n` interface | REPAIRED: scoped to `∀ e, e ∈ Finset.Icc 1 n →` — the frozen solve quantifier verbatim | V7-3d |
| Codex-15 (gap) | Y-14/Y-15 residue: F4 `..`, F8/F9 instances as comments, eligMenu/branchingRead/cast helpers undisplayed | REPAIRED: the three FULL Field instances displayed (every law field `by decide`; f4inv/f8inv/f9neg/f9inv table literals; the ratCast-family default-field remark recorded); `eligMenu`/`branchingRead` closed defs (decide-filtered, incl. the branchMenuCard/hlen/takenGm filter fixes); `castMove`/`castHpt`/`castAssign` displayed ▸-defs; residue shrunk to the recorded slot-11/13/14 tokens | §2.I, §2.D, §2.G, §2.J |
| Codex-16 (gap) | `BlockData.CellIdx` declared twice (§2.C + V2-2) — duplicate-name error | REPAIRED: single home §2.C; V2-2's roster reduced to the Fintype instance + `deleted_empty` | §2.C, V2-2 |
| Codex-17 (gap) | V7-2a displays 3 of 24 `*_Stmt` bodies — a concealed transcription suite | REPAIRED: ALL 24 bodies displayed with their quantifiers and premise references (the prose-parenthesized cores bound token-for-token to the cited units' displayed conclusions by the normative rule) | V7-2a |
| Codex-18 (gap) | design-freedom slot 2 still says "the exactness laws quantify over the defined count" — the pre-N-1 keying, contradicting the operative Defs | REPAIRED: slot 2 rewritten to the operative two-sided rule (table side definitional; exactness over TReal ONLY; count one-way via V1-3(b); re-keying back = re-proving HMC, forbidden by the slot-9 fence) | §5 slot 2 |
| G-1 (Fable, gap) | V4-12's only-if status asserted two contradictory ways (§0/V4-12(b) "NOT interface-derivable" vs (b′) "OPEN, CLAIMED NEITHER WAY") | REPAIRED: ONE status corpus-wide — (b′)'s honest form (OPEN, claimed neither way; (b′) proves only non-sum-arithmetic-consequence); §0 and V4-12(b) restated | §0, V4-12(b) |
| G-2 (Fable, gap) | the hentCode injectivity gloss false as stated (cross-read-count collision) | REPAIRED with Codex-7 (one row above): length-seeded code + scoped gloss | §2.D, V7-4b |

ROUND-4 CROSS-CHECKS HONORED: Fable's §A verified the three ADJUDICATED
round-3 repairs LANDED (the four-line proof re-run FAILS both directions
at composite tails; the T21 2-vs-6 and (X−1)² 1-vs-4 refutations DEAD;
the k = 0 δ against the frozen law and N2Carriers 101–105; V4-12 at MOVES
8596–8602 verbatim) and re-armed the round-1/2/3 refutation batteries —
ALL DEAD; Codex confirmed the seven-carrier pool threading, the
XHDu same-pool re-key, both gate arithmetics, the A2 chart, gate-B's
128 = (1/4)·512, and CoprimeLiftPack's fenced status. REV 5 touches NONE
of those verified cores except where the M-1/M-3 re-keys pass through
them (each touch is a row above); the census stays 95 = 32/59/4 (no new
units — statement/Defs-level repairs only).

### §6.5 DISPOSITION TABLE (round 5 → REV 6)

Codex round-5 findings (`MOVESV_AUDIT_CODEX5_2026-07-28.md`, the recovered
per-item re-derivation: 5 critical + 7 gap, cited as Codex5-21..32; its
items 1–20 are the prior-round re-derivations — priors 5 (MarkDisjT),
7 (hentCode), 8 (EntMassSummable), 9 (V5-2a/c), 10 (J-RAT quantifier),
12 (pools_ne), 13 (kmat_all), 16 (CellIdx) and Fable M-1 (tbl_count)
REPAIRED as recorded there; the partial/open rows' residues — priors
1+14, 2, 3, 4, 6, 11, 15, 17, 18(slot 2), 19, 20 — carried into 21–32),
Fable round-5 findings G-A/G-B/G-C
(`MOVESV_AUDIT_FABLE5_2026-07-28.md`; that audit also verified all three
round-4 repairs LANDED — the tix refutation dead BY TYPE, the cooked
HMCAug witness dead at boxEq/tevt_cover with ¬HMCAug proved at the
coupled toy [the ¬HMCAug half OVERTURNED at REV 7, C4], the pool ripple
complete — re-armed every earlier refutation
battery DEAD, spot-verified eleven disposition rows, and recounted the
census exact). "Fixed at" names the governing section/unit of THIS
revision.

| # | finding (compressed) | disposition | fixed at |
|---|---|---|---|
| Codex5-22 (crit) | a split outcome's designated `tgtSk` need not be any roster member's target (`cont_iff` gives only ∃-continuing-member) — `MoveData.tgt`, V7-3a's continuing statuses, and V5-7b's constructed datum can select a successor absent from the DEG-CONS roster | REPAIRED: the BlockData law `omem_sel` (∃ mu ∈ omem, mu.status = Sum.inr (tgtSk m o h) — the designated (D4) target IS a continuing member); `omem_kcol` demoted to the DISPLAYED derived length-1 corollary; V7-3a's odata and V7-6b's kstep_one supply re-cited through `omem_sel` + `omem_size` + `tcellM_tgt` | §2.C, V7-3a, V7-6b |
| Codex5-23 (crit) | `SelRankTie` ties `MovesD.selRank % m̄` to a rank of (g, μ) PAIRS — but the m̄-menu is the ψ-menu at the read's own (g, μ), so the tie is unsatisfiable with `E8_rankInj` or collapses distinct (side, ψ) selections; V3-1/V5-1 fail post-split label fidelity | REPAIRED — THE RECORDED §2.D HATCH FIRED: `hrank`/`takenGm`/`eligMenu`/`shapeRank` STRUCK (no shape-level (g, μ) enumeration survives); `selRec` = genuine SELECTION DATA (menu-bounded, `hmenu`); the value tie is the DEF `SelMatches` (entry r = `selRank w ν_r % m̄_r` at the r-th branching read's realized node — MovesD's own E9 encoding component, built Defs.lean 528–533, quoted); V3-1(b)/V5-1 consume it DEFINITIONALLY, (side, ψ)-faithful via E7 (< m̄: the collapse is the identity on members) + E8_rankInj; slot 10 OVERTAKEN | §2.D (SelMatches), V3-1, V3-3b, V5-1, §5 slot 10 |
| Codex5-21 (crit) + prior-4 | `evt_disj_cell`'s dependent key still carries (s, m, o, α), so different continuation outcomes get ordinary-box disjointness — claimed contrary to the note's equal-f-projection permission, making the d4r0 supply "too strong" | NARROWING FINISHED + ADJUDICATED: `stepKey` re-landed in the SOURCE-CELL Σ-carrier `CellOf αc` — literally the frozen `Cell e τ = Σ o, DCellO` shape, so V7-6a2's d4r0 supply is DEFINITIONAL; the MARKS RECORD displayed: continuation-mark multiplicity is `emult`-carried and marked-space-only (a mark is NOT an AStep element — two marks over one assignment are ONE AStep point, so no cross-mark pair is even expressible), while distinct (m, o) at one source are distinct COLLISION-PATTERN f-strata (outcome = f-data), exactly the cross-cell disjointness the FROZEN `d4r0` itself demands over its Σ-outcome Cell type (built Defs.lean 221–223). The auditor disagreement (Codex5-21 vs the Fable-5 F-3 re-walk "suite derivable field-by-field") is adjudicated against the frozen law's own quantifier: any weaker carrier law could not supply it, and no stronger claim than the frozen consumer's is made | §2.F (CellOf/stepKey), V7-6a2 |
| Codex5-24 (crit) | `RefEvents` does not kill the cooked HMCAug witness: a union-cover equation gives no per-template identification; `refTmpls` may contain multiple refined templates; the TE′ = TE reduction claimed invalid | ADJUDICATED DEAD against the round-5 Fable fresh-instance walk (§A.2, identical text, computed): at the IDENTITY refinement `refTmpls` reduces to the SINGLETON roster (exactly one surviving (β′, m′) per step, through the displayed filterMap — moveProj = id there), so the fold over one term forces TE′ = TE up to boxEq; and non-identity cooking dies at V4-11's coupled toy, where ¬HMCAug is PROVABLE for EVERY refinement (assign_cover partitions each nonempty coarse fiber; tevt_cover forces every refined composite event empty at the coupled point; no_stray fails) [the ¬HMCAug leg of this adjudication OVERTURNED at REV 7, C4 — the refined DOMAINS may exclude the coupled point per refined cell, so no_stray need not fail; the toy is in fact the ¬HMC ∧ HMCAug SEPARATION witness; the singleton-roster/boxEq reduction half STANDS]. The reduction note is now displayed at the def site. The finding's SOUND half — the "NOT a consequence of HMC" record line — is repaired under G-A (the type unchanged) | §2.G (the displayed singleton-roster note), + the G-A row |
| Codex5-25 (crit) | `xrbPackageOf`'s target `MovesS.XRBPackage` is absent from the built E-phase source (Interfaces.lean: §W4-SYNC "NOT built at E-phase"); the four face-law `*_Stmt` bodies schematic | REPAIRED: PROVENANCE corrected — the contract type is frozen at the MOVESS WAVE-4 BLUEPRINT (13 Prop fields; the adapter's roster matches it EXACTLY, per the Fable-5 Codex-11 row check); V7-7 gains the explicit co-build dep (the S-2 re-key is a SEAM-PHASE deliverable; `XHDFrame`/`gProdF`/the four Stmt defs build now, MovesS-free); the four bodies CLOSED — XhdW/XhdD's template legs written out verbatim at F, the law-only faces via EXACT `Nonempty` (XHDu/XHDdC/XHDdEnt carry no data), XhdS's three sum-face triples displayed over `gProdF` | V7-7, §4.2, §4.3-1 |
| Codex5-26 (gap) | the off-pool-∅ branch asserted FORCED by the unguarded `xhd_no_orphan`; the law constrains off-pool only at h ∉ HDom | REPAIRED at all three sites (the REV-5 record, V7-4a's branch roster, slot 12): FORCED at h ∉ HDom; PERMITTED-AND-CHOSEN at h ∈ HDom (the guarded laws read same-pool components only; d4r0's off-pool instances hold trivially at ∅) — the design stands, the wording overclaimed | REV-5 record, V7-4a, §5 slot 12 |
| Codex5-27 (gap) | V7-2a's `*_Stmt` bodies are English transcription promises, not Lean terms — quantifiers/hypotheses unauditable | REPAIRED: ALL 24 bodies are now Lean expressions with displayed quantifiers, guards, and premise references; every free name bound by the displayed NAME→HOME table (each a def declared in its home unit's file, upstream of V7-2a in the build order); the two [3]-vocabulary items (EscapeE0Rec/NeumannRec) are V7-2a's own MovesS-citing record defs | V7-2a |
| Codex5-28 (gap) | material Defs placeholders: `EntShapeV.template`'s `…` WF fields, `writeHeights`/`shapeOfSlots` promises, Refinement's [+T]-comment twins, `castMoveT` | REPAIRED: template's six proof fields = projections of the ONE named V3-3b lemma `spWord_collapseWF` (no anonymous holes); `pairSlots`/`depthSlots`/`expandRuns`/`shapeOfSlots` displayed CLOSED; `writeHeights`' proof fields = the two named V3-3d lemmas (`writeHeights_wf`/`writeHeights_ties`); `castMoveT` displayed; Refinement's five [+T] twin fields WRITTEN OUT (moveProjT/dimT_eq/assignOfT/massT_eq/assign_coverT); `readOfLetter` recorded as V3-3d's NAMED deliverable — a unit obligation, not a placeholder | §2.D, §2.G, §2.J |
| Codex5-29 (gap) | the §4.1 RatBurdens rows name stale/nonexistent unit legs (V7-5(b)/(c)/(d); no V7-5d exists) | REPAIRED: the four rows re-pointed to the REAL Codex-16 split — tgP/jP = V7-5a legs (a)/(b) (`V7_rbA.lean`); ιP = V7-5b (`V7_rbB.lean`); cellP = V7-5c (`V7_rbC.lean`) | §4.1 |
| Codex5-30 (gap) | V4-3 deps on V7-4c while V7 depends on the V4 statement layer — the declared 95-unit build order is cyclic | REPAIRED: `ActiveValueAgree` restated PARAMETRICALLY over (T, M, RB, hK); V4-3's deps = MovesS.Interfaces ONLY; the binding to the V7 instance is the CONSUMER's (V7-2a's AVRec_Stmt/SolveCond_Stmt at the ledger's objects) — the build order is a DAG again (checked: no V0–V6 unit deps on V7) | V4-3, V7-2a, §5 build order |
| Codex5-31 (gap) | the REV-4 revision record still asserts "a machine-checked inderivability witness" for V4-12's only-if leg, contradicting the operative OPEN-CLAIMED-NEITHER-WAY status | REPAIRED: the record line corrected IN PLACE (bracketed REV-6 correction naming the over-read) — ONE status corpus-wide | the REV-4 record, item 4 |
| Codex5-32 (gap) | the §5 non-vacuity recap reasserts "two-sided exactness against the DEFINED counts" for XHD-d, contradicting slot 2 and the operative TReal-keyed XHDd | REPAIRED: the recap re-keyed — XHD-d against `TReal` (the count enters one-way via `mem_chainCount_pos`; the stale clause struck and marked); XHD-dC separately recorded count-keyed BY DESIGN with the tevt_last_iff no-leak note | §5 anchors |
| G-A (Fable, gap) | the §2.G record line "NOT a consequence of HMC" is FALSE as a derivability claim: `HMC ⟹ HMCAug` is a ~30-line theorem (identity refinement + transported RefEvents + D′ := D), and underivability-from-HMC is UNATTAINABLE for any faithful encoding (the note's hypothesis is a conditional whose antecedent is empty under HMC) | REPAIRED BY SCOPING, the TYPE untouched (the audit's own disposition hint adopted; re-keying the ∃ on ¬HMC rejected — it buys nothing and entangles the Prop with the kernel's negation): the §2.G comment rewritten — the theorem recorded with its witness recipe; the unavoidability argument displayed; "NOT a consequence of HMC" carried as LEDGER-ROLE bookkeeping only (separate named line item, cited separately, assumed nowhere); harmless while (v) is open (HMC proved nowhere, HMCAug consumed nowhere). Echo sites scoped: §0's banner, V7-1's (v) ledger line (+ the A.6 sub-finding note: consumers take HMC as an explicit antecedent), §5's recap | §2.G, §0, V7-1, §5 |
| G-B (Fable, gap) | V7-4a's `cellEvt` handles the pool dite but not the `Hgt = Σ D, Hpt D` DIMENSION mismatch — the on-pool branch ill-typed at wrong-dimension heights; V7-6a1's no_orphan leg silently assumes the forced resolution | REPAIRED: the DOUBLE dite displayed (pool × dimension) with per-branch status — the mismatch branch ∅ is FORCED by the frozen unguarded `xhd_no_orphan` (a wrong-dimension h is ∉ HDom; the boxpos-expressible `univ` alternative would falsify the law — slot 12's dichotomy); V7-6a1's no_orphan roster gains the THIRD leg; `cellEvtT` twin noted; inventory slot 15 records the forced value beside slot 12 | V7-4a, V7-6a1, §5 slot 15 |
| G-C (Fable, gap) | V5-7b's display attributes `cont_of_route` to `(C.bd s)`, which has no `route` field — the corollary lives on JCells | REPAIRED: the display consumes `J.route_cont s m o hr` DIRECTLY (the field's type IS the needed implication `route = .split → cont`); the phantom corollary name struck | V5-7b |

ROUND-5 CROSS-CHECKS HONORED: the Fable fresh instance verified the three
round-4 repairs LANDED (the junk-terminal refutation dead BY TYPE; the
cooked HMCAug witness dead at boxEq/tevt_cover, with ¬HMCAug PROVED at
the coupled toy for every refinement [the ¬HMCAug half OVERTURNED at
REV 7, C4 — the boxEq/tevt_cover half stands]; the pool ripple complete with the
per-pool Rep walk sound), re-armed ALL prior refutation batteries (round
1/2/3/4 — DEAD), re-verified eleven disposition rows and every MovesD/
MovesSp/MovesS name key at source, and recounted the census EXACT; Codex
confirmed the CoprimeLiftPack fence and the census arithmetic. REV 6
touches NONE of the verified numeric/gate cores; the census stays 95 =
32/59/4 (no new units — the REV-6 repairs are Defs/statement/record-level
rewrites inside existing units: omem_sel + the derived omem_kcol (§2.C),
the SelMatches re-key (§2.D), the CellOf key re-landing (§2.F), the
V7-2a/V7-7 body closures, the V7-4a double dite, and the record
corrections).

### §6.6 DISPOSITION TABLE (round 6 → REV 7)

Codex round-6 findings (`MOVESV_AUDIT_CODEX6_2026-07-29.md`, REJECT 15/2:
C1–C15, G1–G2 — audited against the POST-RATIFICATION corpora per
`W4_SYNC_DELTAS_2026-07-29.md`), Fable round-6 findings
(`MOVESV_AUDIT_FABLE6_2026-07-29.md`, REJECT 2/4: CRIT-1/2, GAP-1..4 —
all 14 §6.5 disposition rows verified REAL, no fake repairs; the
criticals are seam drift). CONVERGENCES: C14 ≡ F-CRIT-1 (wsh17),
C15 ≡ F-CRIT-2 (jPCell), C13 ≡ F-GAP-1 (legs_read). FOUR rulings
ORCHESTRATOR-ADJUDICATED (bind; rev7 charge on file): C4, C6, C8, C3.
"Fixed at" names the governing section/unit of THIS revision.

| # | finding (compressed) | disposition | fixed at |
|---|---|---|---|
| C4 (crit, ADJUDICATED) + G1 | the rev-5/6 claim "¬HMCAug provable at V4-11's coupled toy for EVERY refinement" is FALSE — refine by whether h₁ = 0: each refined domain FACTORS (Codex's construction, orchestrator-verified); and the cited ~30-line HMC → HMCAug theorem had no unit | REPAIRED: the toy is the SEPARATION WITNESS (¬HMC ∧ HMCAug — one 𝒞_n refinement round restores the factorization, the note's own HMC-AUG display); V4-11 gains leg (iii) (the Fin-2 h₁-reading refinement, displayed); EVERY ¬HMCAug claim STRUCK (header, §0, §2.G, §5; the §6.5 rows and the REV-6 record line bracket-corrected in place); HMCAug's falsifiability recorded OPEN (predicted falsifier: R2's wall channel); derivability-from-XHD-alone now UNCLAIMED either way; `HMC → HMCAug` allocated as the REAL unit V4-13 (identity refinement + singleton-roster covers) | §2.G, V4-11(iii), V4-13, §0, §5 |
| C6 (crit, ADJUDICATED) | XHD-d's object was changed: the note DEFINES T_γ directly (MOVES 7921–7923) and states no-orphan/no-stray with T_γ verbatim (7947–7949); rev 6 keyed exactness to `TReal` (event nonemptiness) | REPAIRED: the typed DIRECT-COUNT def `Tgam TE γ x h := (tinst … tmplLvl).card` (the mark census IS the chain count; NOT the recursive product — chainCount stays table-side, the factorization stays (u-T)/HMC content); `XHDd` keyed to `0 < Tgam` two-sidedly VERBATIM; `TReal` DEMOTED derived with `treal_iff_tgam` (V1-3(c), via the new third mark [tie] `marks_realize`); XhdD_Stmt re-keyed; HMC openness VERIFIED preserved (no census recursion at composites; the §2.G audit re-run at the def site) | §2.G (Tgam/XHDd/marks_realize), V1-3, V7-7, §5 slot 2 |
| C8 (crit, ADJUDICATED) | `MarkDisj`/`MarkDisjT` were OPEN hypotheses on LedgerIV for content the note makes typed/definitional marked-event structure ((iv)-MEAS: the mark is ADJOINED and the summands disjoint IN THE MARKED SPACE) | REPAIRED: V4-10's marked Σ-carrier gains the READING LAW (a mark determines its (m, o, β, height-class) summand — definitional on the carrier); `MarkDisj`/`MarkDisjT` are now V4-10's DERIVED marked-space lemmas (the ruling's naming); the within-cell CARD step V7-6a1 needs is the new CtsMeasured [tie] `evt_disj_assign`(+T) (C.1.5 assignment semantics — the old defs conflated assignments with marks); the hypothesis defs, the LedgerIV premises, and the V7-1/§5 fields all REMOVED; f-event disjointness stays NOT claimed | §2.F, V4-10, V7-6a1, V7-1, §5 |
| C3 (crit, ADJUDICATED — overruling rev 6) | `tcellM_tgt`'s ∀ i forced EVERY same-skeleton roster member to the designated tcell — unsupported for multi-continuing outcomes | REPAIRED: the ∀-form STRUCK; `tcellM_sel` (CtsFamily): ∃ roster position with the designated target skeleton whose tcellM = tcell — the [tie] survives for THAT member; omem_sel its projection; V7-3a/V7-6b re-cited; n = 3 unaffected (single-continuing) | §2.C, V7-3a, V7-6b |
| C1 (crit) | `SelMatches` not load-bearing: EntranceCut.lands/iotaCount/entEvt/entInst nowhere required to read the selection — a selection-ignoring instance passes, merging note-distinct sibling selections | REPAIRED BY TYPE: `EntranceCut.lands_sel : lands i → SelMatches ε i` (every cut selection-bounded; iotaCount inherits); `CtsMeasured.ent_sel` (sibling labels differing only in selRec have DISJOINT mark-census realizations at the defining level — ENT-AGG's "distinct concrete ε give distinct marked pairs", typed on the count-realizing carrier; entEvt deliberately gets NO f-disjointness — PART-2's permission — its tie is ent_card + ent_sel + the lands_sel-bounded cut identification) | §2.E, §2.F, V3-1/V3-6/V5-1 |
| C2 (crit) | `IsBranchingRead := 2 ≤ mbar` is an upper-bound key (eligible_card_le BOUNDS the realized menu), not actual branching — "every actual shallow branching cell" silently became "every read with bound ≥ 2" | REPAIRED: renamed `IsBranchSlot` (the SLOT layout — the E6-licensed superset); ACTUAL branching = the new value-level `RealizedBranching` (≥ 2 realized eligible continuations — the documented faithful carrier: MovesD's `EligibleImage` census at the read's node, built Defs.lean 297–303, the same census selRank ranks; E6/E7 give Realized → Slot); SelMatches pins EVERY slot (surplus slots carry canonical rank 0 — zero information; realized-branching entries are exactly the note's σ_sel) | §2.D |
| C5 (crit) | `SolveCond_Stmt` omitted the HMC premise — the factored solve is HMC-conditional (MOVES 8005: "(COMP-Σ) additionally GIVEN (v)"; 8222–8224) | REPAIRED: the HMC L.TE L.D antecedent DISPLAYED in SolveCond_Stmt; V7-1's (vi) ledger line carries it | V7-2a, V7-1 |
| C7 (crit) | `EntMassSummable` silently strengthened the note's package — ENT-AGG grants convergence "GIVEN XHD-s on the shallow layer" ALONE | REPAIRED: `EntMassSummable` STRUCK corpus-wide; V3-8a's premise = `XHDsEnt` itself, the summability DERIVED (census ≤ q₀^{n·entLvl} uniformly per template — box_card — then comparison against the scaled Gent weight sum); V7-1/V1-8c/§5 lists purged | §2.G, V3-8a, V7-1, §5 |
| C9 (crit) | `AVRec_Stmt`/`SolveCond_Stmt` ∀-closed over EVERY (RB, hK) — the note's (ii-c) is the check for the ACTUAL instance | REPAIRED: `CtsmLedger` gains the DATA fields `RB`/`hK` (supplied by V7-5/V7-3b-d at assembly); both Stmts scope to L.RB/L.hK; no ∀-closure survives | V7-1, V7-2a |
| C10 (crit) | `CellOf`/`stepKey` existed only as COMMENTS under evt_disj_cell, which consumed them | REPAIRED: the carrier SPLIT — `CtsCells` (classifier half) + `CtsMeasured extends CtsCells`; `AStep`/`CellOf`/`stepKey`/`evtOfStep` are REAL DISPLAYED closed defs over CtsCells (stepKey via the bijections' invFun + the named castAssignKey transports); evt_disj_cell reads them through the parent projection | §2.F |
| C11 (crit) | Defs-before-V3 order impossible: §2.D's `shapeOfSlots`/`writeHeights`/`template` consumed `readOfLetter`/`writeHeights_wf`/`writeHeights_ties`/`spWord_collapseWF` — V3-3b/d theorems (forward references) | REPAIRED: `readOfLetter?`/`ReadFits` are DEFS-LAYER declarations (candidate + classical dite — no proof term imported); `shapeOfSlots?` foldlM; `writeHeights?`/`EntShapeV.template?` Option-valued classical-dite defs; the TOTALITY theorems are V3-3d's `writeHeights_total` (+ the total `writeHeights` decl for unit layers) and V3-3b's `template_total`; every §2.F/2.G consumer reads the displayed wrappers (`instA`/`instHentCode`/`instCensus`/`instRealizable`, `template?.elim`) with recorded dead defaults — NO forward reference anywhere | §2.D, §2.F, §2.G, V3-3b, V3-3d |
| C12 (crit) | `XhdS_Stmt` contained literal prose "(the same three clauses …)" inside a claimed-closed body | REPAIRED: the [+T] GcellT triple WRITTEN OUT verbatim (denom/OKat/HasSum over cdomT with F.ET); no substitution parenthesis survives | V7-7 |
| C13 (crit) ≡ F-GAP-1 | `RS4Chain.legs_read` (NEW built field) missing from §4.2 — the map's "every field" claim false; V4-3's shape lacks the LegAgree/βmeas/consumed-δ/hdet structure | REPAIRED: §4.2 row ADDED (owner [3]/MovesT; MovesV supplies entries/OKat + the all-active (ii-c) form only); V4-3 SEAM-SCOPED (the built split displayed: AVAgree = all-active face, legs_read = the non-all-active burden); §4.3 W-6 re-scoped; the deltaFactors narrowing (delta 4) recorded at the pools_e0/legs_reg row | §4.2, §4.3-4, V4-3 |
| C14 (crit) ≡ F-CRIT-1 | `wsh17_pin` Prop field DELETED in built MovesS (projection-def = W17ii); "instantiate the pin" names nothing; the proof duty unscheduled | REPAIRED: NEW UNIT V7-8 `w17ii_wave4` — W17ii at EXACTLY the built type (clause (i) rfl-level from wsh_ok/wsh_interp; clause (ii) sorry-gated pending the [3t]/[3] shape-layer assembly — the one banked open leg, no unconditional marking); §4.2 wsh17_pin row, §4.3 S-8, and the SF-2 record rewritten to the proof duty | V7-8, §4.2, §4.3-2 |
| C15 (crit) ≡ F-CRIT-2 | built `RatBurdens` REQUIRES `jPCell/jcell_ok/jcell_interp/jcell_sum` (Defs.lean 386–395) — the planned instance FAILS BY TYPE; rev 6 built a parallel CellPolyPack aggregate only | REPAIRED: §2.H's `jcellPG` + V5-7b's per-cell clauses `jRat_cell`/`jRat_sum` (CellPolyPack WIRED INTO the per-cell supply; eval = M.μcell rep-quantified split-guarded; symbolic fiber Σ = jP.val); V7-5a leg (b) transports to the EXISTING `M.Cell` carrier via dataOf; §4.1 row added; §4.3 CL-18 updated — NO parallel type is the deliverable | §2.H, V5-7b, V7-5a, §4.1, §4.3-6 |
| G1 (gap) | no unit allocated for the HMC → HMCAug theorem | REPAIRED: unit V4-13 (see C4's row) | V4-13 |
| G2 (gap) | `MovesS.XRBPackage` still absent from the built source — the co-build dep | STANDS AS RECORDED (rev 6's provenance correction unchanged): blueprint-frozen contract, V7-7's xrbPackageOf gated on the MovesS wave-4 co-build; no new duty | V7-7 (unchanged) |
| F-GAP-2 | `PolyGeomLaws.tCount`'s event-side identification is a RECORDED MovesV duty (built Defs.lean 407–409) with no blueprint unit | REPAIRED: NEW UNIT V7-9 `polygeom_count_laws` — countS via cellInst/cellLvl, countT via ValA.tbl_count (the named carrier) + u_T/MDomTie + evt_card; V.2's exponent-map audit on V2-4's degree ledger | V7-9, §4.3-5 |
| F-GAP-3 | stale MovesD/MovesS line cites (content verbatim, positions shifted post-repair) | REPAIRED: SelMatches/σ_sel-pin blocks re-cited (EncTargetP 529–531, encIdx 556–564, E7 comment 552–555, mbar 104, selRank 308–310); V7-2a's DetHyp cite → MovesS/Defs.lean 550–552; the current cites (d4r0 221–223, kstep_one 238–242) verified and kept | §2.D, V7-2a |
| F-GAP-4 | `branchingRead`/`branchMenuCard` (and bIdx) used `getD … default` at `MovesD.ShapeRead`, which has NO Inhabited instance — the defs did not elaborate | REPAIRED: Option-indexed restructure (`[i]?` + `.map`/`.getD` on the projected value; `branchingRead?` Option-valued; SelMatches keyed to `= some R`) — no junk witness minted | §2.D |

ROUND-6 CROSS-CHECKS HONORED: Fable verified all 14 §6.5 rows REAL (no
fake repairs — the round-6 pattern was statement-level, not
transcription); Codex's per-row table (6 rows re-opened) is absorbed
above — the re-opened rows are exactly C1/C3/C4/C10/C11/C12's subjects,
each now repaired at statement level. Census 95 → 98 (V4-13, V7-8,
V7-9); the numeric/gate cores are untouched.

*(End of MOVESV blueprint REV 7. Next per campaign §3 + the audit-budget
policy: dual round-7 audit of this revision (Fable fresh instance + Codex
per-item, BOTH against the post-ratification corpora per
`W4_SYNC_DELTAS_2026-07-29.md`), REJECT loops until ACCEPT; then E-phase —
build order Defs → DefsGate → V0 → V1 → {V2, V6} → V3 → V4 → V5 → V7,
with V7-7's xrbPackageOf leg gated on the MovesS wave-4 co-build and
V7-8's W17ii sorry the one banked open leg.)*
