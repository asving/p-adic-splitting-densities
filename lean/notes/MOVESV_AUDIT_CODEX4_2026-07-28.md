# Codex re-audit of MovesV Lean blueprint, REV 4 (§V-TABLES) — 2026-07-28

Verdict: REJECT (13 crit / 5 gap). This is the FOURTH Codex pass on this corpus, after
round 1 (`MOVESV_AUDIT_CODEX_2026-07-28.md`, REV 1) returned REJECT (23 crit / 6 gap),
round 2 (`MOVESV_AUDIT_CODEX2_2026-07-28.md`, REV 2) returned REJECT (16 crit / 4 gap)
against a disjoint Fable round-2 pass (6 crit / 4 gap: F-1..F-6/G-1..G-4), and round 3
(`MOVESV_AUDIT_CODEX3_2026-07-28.md`, REV 3) returned REJECT (13 crit / 4 gap: Y-1..Y-17)
against a disjoint Fable round-3 pass (`MOVESV_AUDIT_FABLE3_2026-07-28.md`, 3 crit / 2 gap:
N-1/N-2/N-3, G-1/G-2). REV 4, pasted in full below (~3817 lines), claims in its own §6.3
disposition table that all 21 distinct round-3 findings (Y-1..Y-17 with N-2 = Y-1 the
convergent defect, plus N-1, N-3, G-1, G-2) are now repaired — centered on two
orchestrator-adjudicated centerpieces: (1) the HMC split (a new process-side
`TmplEvents`/`TReal` carrier, with `HMC` demoted to a typed OPEN link quoted verbatim
from the note, per the N-1/HMC adjudication — this pass correctly declined to re-litigate
whether HMC *should* be derivable, auditing only whether the Lean text implements the
adjudicated split); and (2) pool-layer threading (`Hist : ℚ → Cell → Type`, with
`Assign`/`cntraw`/`cntc`/`massOf`/`chainCount`/`evtOf`/`cellEvt` all riding the pool, and
the T21/(X−1)² gate arithmetic re-verified correct: T21(2)=2, T21(3)=6, (X−1)²(2)=1,
(X−1)²(3)=4).

This pass re-derived the disposition of all 21 round-3 findings from the pasted text
rather than trusting the table's self-report, confirmed the two centerpiece claims are
real (the HMC split genuinely leaves composite realization free; the seven named
carriers are genuinely pool-threaded and XHDu is genuinely same-pool-only), and
confirmed the arithmetic and the VERIFIED-CLEAN cores (A2 chart, gate-B 128 = (1/4)·512,
`CoprimeLiftPack` still a fenced published-axiom candidate) are intact. It nonetheless
found 13 NEW/persisting critical faults and 5 gaps, dominated by ONE structural defect:
the pool-index repair does not reach the actual MovesS seam — `V7-4a`'s `Rep e τ :=
{x // S.zc x}` cannot recover the pool index that pool-indexed `Hist` now carries, so the
frozen `MeasuredSide.Rep`/`cellEvt` cannot actually be instantiated from the repaired
carrier (finding 1; degrades N-2/Y-1 from REPAIRED to PARTIALLY REPAIRED). The other
critical findings: `V7-3a` cannot construct `TableShape.odata` (no member-data list
exists to supply it, finding 2); `TargetIx` still admits terminal targets for continuing
outcomes and doesn't pin the actual successor skeleton (finding 3); `evt_disj_cell`'s key
still includes the whole `MoveData` datum, so Y-3's cross-mark-equality demand is still
violated in the displayed type (finding 4); the new `MarkDisj` burden has no
`TermData`/`AssignT` twin, so terminal cells still lack `meas_card` support (finding 5);
Y-4's `shapeRank` is an independently-invented enumeration with no typed tie to
`MovesD.selRank` (finding 6); the upgraded `hentCode` is not actually injective — a
fold with a zero terminal seed can collide, and it never encodes `e`/`STR`/`s0`/`wSide`
(finding 7); Y-7's repair silently strengthens XHD-s with a new `mass_summable` field
that assumes the conclusion instead of deriving it (finding 8); V5-2 drops the frozen
XHD-w `(U-A)` premise (finding 9); V5-7b's J-RAT supplier can't represent a general split
outcome at the frozen per-(τ,o) type since `MoveData` fixes one continuing target
(finding 10); Y-10's XRB re-key maps `Prop`-typed frozen fields to structure-valued
projections — a type mismatch, not a Lean mapping (finding 11); `StepSys`/XHD `Pools`
still admits `Pools = ∅`, vacuously satisfying every non-vacuity law (finding 12); and
`StageLawBurden.kmat_all` strengthens `KmatHyp` to every natural index instead of just
`1..n` (finding 13). The five gaps: `V1-6` wasn't retyped after pool-indexing and doesn't
elaborate (14); the Y-14/Y-15 placeholder checklist is still materially incomplete
(F4/F8/F9 `Field` instances, `eligMenu`/`branchingRead`, cast helpers — comments, not
definitions; 15); `BlockData.CellIdx` is declared twice, a duplicate-name error (16);
`V7-2a`'s 24-field structure only displays 3 of its 24 `*_Stmt` bodies, still a hidden
transcription suite (17); and the design-freedom inventory's slot 2 still describes the
pre-N-1 exactness keying, contradicting the operative (and correct) `TReal` re-key (18).

Full round-3 disposition audit (this pass's own, not REV 4's table): N-1 REPAIRED, N-2 =
Y-1 PARTIALLY REPAIRED (degraded by finding 1), N-3 REPAIRED, Y-2 PARTIALLY REPAIRED,
Y-3 STILL OPEN, Y-4 STILL OPEN, Y-5 REPAIRED, Y-6 STILL OPEN, Y-7 PARTIALLY REPAIRED,
Y-8 REPAIRED (under the binding adjudication), Y-9 REPAIRED, Y-10 STILL OPEN, Y-11
REPAIRED locally, Y-12 REPAIRED, Y-13 REPAIRED, Y-14 STILL OPEN, Y-15 PARTIALLY
REPAIRED, Y-16 PARTIALLY REPAIRED, Y-17 PARTIALLY REPAIRED, G-1 REPAIRED, G-2 REPAIRED.

Note on the charge's round-history recap: the charge sent to Codex states the verified
figures 23/6 (round 1), 16/4 (round 2, Codex's own re-audit), 13/4 (round 3, Codex's own
Y-1..Y-17) — these were re-checked against the actual saved round-2/round-3 audit files
before assembly (the task instruction's shorthand "17/3" for round 2 does not match any
recorded figure in this repo: Codex round 2 was 16 crit/4 gap over 20 findings X-1..X-20,
and Fable round 2 was separately 6 crit/4 gap; "17" only appears elsewhere as REV 4's own
count of "17 REPAIRED" round-2 dispositions per Codex's round-3 re-derivation table, a
different quantity). The corrected, source-verified figures were used in the charge to
avoid feeding Codex an inconsistent history.

This is the RAW Codex transcript (prompt echo, exactly as sent via stdin, + full
response, including the CLI's own duplicate-print-then-token-usage-then-duplicate-print
artifact seen in every prior round's saved transcript) — nothing edited, nothing
summarized.

OpenAI Codex v0.145.0
--------
workdir: /tmp/leanaudit_v44
model: gpt-5.6-sol
provider: openai
approval: never
sandbox: read-only
reasoning effort: none
reasoning summaries: none
session id: 019faaab-5316-72a2-9795-1f89bbd6706a
--------
user
You are the semantic auditor for a Lean formalization blueprint. You verify
FAITHFULNESS of proposed Lean statements to a frozen mathematical note; you fix
nothing. Quote each offending unit spec and classify: CRITICAL (the Lean
statement says something different from, weaker than, stronger than, or vacuously
satisfiable relative to the note's display) vs GAP (ambiguity, missing
hypothesis-field, underspecified Defs dependency). Then give counts and a verdict
line 'ACCEPT' or 'REJECT (n crit / m gap)'.

Check EVERY unit spec for, in one pass:
1. FAITHFULNESS: the `statement` field says exactly what the quoted `moves_ref`
   display says — same quantifier order, same side conditions, same edge cases
   (empty menus, m = 1, N = 0, the (BDY) conventions).
2. NON-VACUITY: no statement satisfiable by an empty/degenerate instance of its
   own hypothesis structures (the trap that killed the pre-rebase chain — check
   each structure has an inhabitation story or an explicit instance unit).
3. HYPOTHESIS FIDELITY: every open kernel the note attaches to a claim appears in
   `hypothesis_fields` — never silently dropped, never silently strengthened into
   a definition, never smuggled into an axiom (the axiom policy allows PUBLISHED
   statements only).
4. DEFS SOUNDNESS: the proposed Defs skeleton — no definition that secretly
   decides an open question (a def that computes what the note only hypothesizes
   exists); typing plausible in Lean 4 + Mathlib.
5. DECOMPOSITION: units genuinely short (one display each); flag any unit whose
   sketch cannot fit its statement (a hidden multi-lemma unit).

The note text is the sole ground truth. Do not trust the blueprint's prose
summaries of the note; check against the quoted displays and the pasted note.
Write NOTHING to disk. Output: the numbered findings, counts, verdict.

CORPUS: MovesV
NOTE: §V-TABLES

This corpus SUPPLIES the MovesS interface — audit the SEAM-SUPPLY table
HARDEST of all: check every field of MovesS's `Defs.lean`/`Interfaces.lean`
(both pasted below, verbatim, as the ground-truth signatures — this is the
REAL, E-PHASE-BUILT Lean source, not a blueprint restatement) is mapped to an
explicit supplier unit or an explicit owner in MovesV's §4 SEAM-SUPPLY table,
with no field silently dropped, silently self-supplied where the field's true
owner is a different corpus (per the included MovesS §W4-SYNC seam-contract
section, also pasted below), or supplied by a unit whose statement does not
actually produce that field's type.

The (J-RAT)/CL-18 per-cell deliverable is the note's PLAN-SYNC obligation
(owner [1v]): check that the V5-7 units (V5-7a/b/c) carry it EXACTLY — the
per-cell rational coefficients J_{τ,o} ∈ ℚ(q), not the marked T·G aggregate,
with the XHD-s + cell-count hypotheses displayed as explicit hypothesis
fields, not folded into a definition or silently discharged.

The ONE flagged axiom candidate in this corpus — the Hensel/coprime-lift
hypothesis at V6-4c (`CoprimeLiftPack`) — must remain a FENCED PROPOSAL per
the campaign axiom policy (a typed hypothesis field, explicitly flagged as a
published-axiom candidate if Mathlib's exact form is missing, NEVER silently
declared as an unconditional axiom or silently discharged as a plain
definition). Flag any deviation from fenced-proposal form as CRITICAL.

This doctrine (SEAM-SUPPLY-hardest, J-RAT exactness, axiom-candidate fencing)
is BINDING on this audit pass — apply it in addition to, not instead of, the
five-point check above.

---

## FOURTH-ROUND ADDENDUM (read before auditing; this is REV 4, the fourth pass on this corpus)

FOURTH round after 23/6 (your own round-1 pass, `MOVESV_AUDIT_CODEX_2026-07-28.md`,
REJECT 23 crit / 6 gap), 16/4 (your own round-2 re-audit, `MOVESV_AUDIT_CODEX2_2026-07-28.md`,
REJECT 16 crit / 4 gap, against a disjoint Fable round-2 pass at 6 crit / 4 gap —
F-1..F-6/G-1..G-4), and 13/4 (your own round-3 re-audit, `MOVESV_AUDIT_CODEX3_2026-07-28.md`,
REJECT 13 crit / 4 gap — your findings Y-1..Y-17 — against a disjoint Fable round-3 pass at
3 crit / 2 gap: N-1/N-2/N-3, G-1/G-2, `MOVESV_AUDIT_FABLE3_2026-07-28.md`). REV 4 (pasted
below in full, ~3817 lines) claims in its own §6.3 DISPOSITION TABLE that all 21 distinct
round-3 findings (your Y-1..Y-17, Fable's N-1/N-2/N-3 with N-2 = Y-1 the convergent defect
both auditors found, and Fable's G-1/G-2) are now repaired. Do not trust that table's
self-report — re-derive each disposition from the pasted text itself.

The claimed repair has TWO centerpieces, both stated as BINDING ADJUDICATIONS from the
campaign orchestrator (not something this pass should re-litigate at the adjudication
level — but the pass MUST check the Lean text actually implements what the adjudication
says):

1. **THE HMC SPLIT (Fable's N-1).** Round 3 found that keying `XHDd`'s two-sided
   exactness to the DEFINITIONAL `chainCount` made `HMC S D` a four-line THEOREM
   (provable from the recursion), defeating the note's own (v)-conditionality on
   HMC as an open hypothesis. REV 4's claimed fix: the orchestrator adjudicated the
   note-side flag NOTE-INTACT (blueprint over-commitment, not a note error) — table
   side (`chainCount`, `G`) stays recursive-by-definition; a NEW process-side carrier
   `TmplEvents`/`TReal` is introduced (the COMP vocabulary quoted from MOVES 8225-8232);
   `XHDd` exactness is RE-KEYED to `TReal` (not `chainCount`); `HMC` is now the TYPED
   OPEN LINK between the two sides, quoted VERBATIM from the note display at MOVES
   8198-8204 (check the quotation is exact, not a paraphrase); its underivability must
   be AUDITED (one-way count supply only, no composite tie forcing it) — this is what
   you must verify, not whether `HMC` *should* be derivable. Do NOT re-open "should HMC
   be derivable/definitional" as a finding — that question is CLOSED by the
   adjudication; a finding here is legitimate only if the pasted Lean text fails to
   actually carry out the split as described (e.g. if `TReal`/`TmplEvents` secretly
   collapse back to `chainCount`, if the MOVES 8198-8204 quotation is inexact or
   incomplete, if `XHDd`'s exactness still cites `chainCount` anywhere, or if any
   consumer re-derives `HMC` from the typed carriers despite the underivability claim).
   Check also that every (v)-tagged conditional claim the note attaches to HMC (V5-5's
   `hHMC`, the V7-6c note, V4-11, V4-12(c)) is restored to genuinely CONDITIONAL form —
   satisfiable-but-not-forced, per the note's own (v) marking.

2. **THE POOL-LAYER THREADING (N-2 = Y-1, the convergent defect both round-3 auditors
   found independently).** Round 3 found the history layer (`Hist`/`Assign`/`cntraw`/
   `cntc`) pool-FREE, forcing constant count polynomials — the displayed acceptance
   check was `T21 = X(X−1)` with eval at q₀ = 2 giving 2 and eval at q₀ = 3 giving 6
   (2 ≠ 6, so a constant polynomial cannot match both, and `valA_gate` was FALSE).
   REV 4's claimed fix: `Hist` becomes POOL-INDEXED (`Hist : ℚ → Cell → Type`), with
   `Assign`/`cntraw`/`cntc`/`massOf`/`chainCount`/`evtOf`/`cellEvt` all riding the
   history's pool argument; `XHDu` is re-keyed to compare SAME-POOL histories only
   (closing the cross-prime horn). Two gate checks are claimed DISPLAYED: the T21
   2-vs-6 acceptance check at unit V2-4, and a companion `(X−1)²` check at §2.H
   claimed to read 1 at q₀ = 2 and 4 at q₀ = 3 (the "1-vs-4" check). RE-COMPUTE both
   checks YOURSELF from the actual pasted polynomial definitions and evaluation sites
   — do not accept a displayed numeral without redoing the arithmetic in context, and
   confirm the pool index is actually threaded through every one of the seven named
   carriers (not added to `Hist`'s signature and then ignored downstream).

Beyond the two centerpieces, give an EXPLICIT quote-per-row disposition for each of
your OWN 13 critical + 4 gap round-3 findings (Y-2 through Y-17 — Y-1 is centerpiece 2
above), checking the actual current text at each named site, not the table's self-report:
  - Y-2 (continuing/terminal keyed to bare Letter, unrepresentable for V.6.3's m₂):
    check outcomes now live in `BlockData.Outc : Letter → Type` with `cont`/`tgtSk`/
    `tgt_menu`/`tcell`/`T`/`vlabOf`/`TargetIx`/`MoveData.hc`/`TermData.ht` re-keyed to
    (letter, outcome).
  - Y-3 (evt_disj too strong: claims ordinary-box disjointness across continuation
    marks): check the replacement `evt_disj_cell` is disjointness EXACTLY at distinct
    (letter, outcome, cellOfA-class, height), that cross-mark pairs are NOT claimed
    disjoint, and that the within-cell sum burden `MarkDisj` is a NAMED, DISPLAYED,
    explicitly open-beyond-gates hypothesis (not silently assumed).
  - Y-4 (selRec entries untied to MovesD.selRank or the actual continuation taken):
    check the new `hrank` field is keyed to `shapeRank` of the continuation the prefix
    ACTUALLY takes, and that the value-level identification cites MovesD Defs 522-523
    verbatim (not a paraphrase).
  - Y-5 (mdom untied to XHDd's length-1 domain; u_T transport broken): check `MDomTie`
    (`mdom_eq`/`mdomT_eq`) is an EXPLICIT premise of every base-point transport site
    (V2-5/V4-5/V5-8/tg_interp), not a background assumption.
  - Y-6 (hent a lossy scalar): check the VALUE is now the injective `hentCode`
    (Nat.pair-fold over (h_r, zig(γ_r)), no height identification), and that seam flag
    SF-1 is HONESTLY still open on the structural half — verify by grep against the
    built MovesS sources that `hent` truly has no consuming law (the claimed evidence:
    Defs.lean declaration + N2Carriers.lean device `:= 0` + one comment, nothing else).
  - Y-7 (ENT-AGG over-strengthened by an (ENT-U) premise the note doesn't attach to
    convergence): check V3-8 is SPLIT into V3-8a (convergence from `XHDsEnt.mass_summable`
    alone, NO (ENT-U)) and V3-8b (the ιval identification, where (ENT-U) is cited because
    the note's own INIT-RAT line lists it there — confirm the note text actually places
    it there and not at convergence).
  - Y-8 (V4-12's iff quantifies over every positive-affine E-family; the note fixes the
    actual XHD weight system): check the note's EXACT quantifier is now matched — the IF
    leg at the FIXED system, the ONLY-IF leg as the named `UpgradeOnlyIf` explicitly
    marked OPEN-UNCLAIMED and consumed by nothing, plus the machine-checked sum-level
    toy computation and the false-HMC failure fence. Also check the TWO-VERDICT note
    (Fable round-3 found rev-3's iff overtaken by N-1/the HMC adjudication) is honestly
    reconciled, not just asserted resolved.
  - Y-9 (tgt_supported lacks the note's active-source premise): check the `ValA` field
    now carries `activeState q₀ (src)` + zc guards, and that `ent_supported` correctly
    keeps NO source guard (verify against the note's own text — the entrance leg has no
    source state).
  - Y-10 (XRB re-key strengthens each premise to the full bundle): check the fix is ONE
    shared package parameter `X : XHD …` with the four field names as FACE PROJECTIONS
    (not four independently-strengthened premises), and that `xhdStmt` survives only as
    V1-5's discharge Prop.
  - Y-11 (Wsh17PackageV drops c15_volumes/sib_count as mere comments): check the FULL
    frozen three-field roster is IN THE TYPE (not commentary), with owner legs as Prop
    parameters and seam flag SF-2 unchanged.
  - Y-12 (XHD-w/u quantify over non-realizable histories): check `S.zc` guards are on
    `w_eq`/`wT_eq` and ALL SIX XHDu fields, and that XHDd/XHDdC exactness got the same
    zc-guard sweep.
  - Y-13 (V6-2b's moves_ref splices "= 6t+3u+1" into the quotation): check the splice is
    DELETED from the quoted note text (the derived form may still appear in the
    statement body, marked as ours, but not inside the quotation marks).
  - Y-14/Y-15/Y-16/Y-17 (the four gaps: placeholder checklist, declaration order,
    unlabeled multi-lemma splits, seam-table field completeness): check each claimed
    closure by name against the actual text — gProd's recursion, cellEvtT/cntcT,
    the F4 instance skeleton with per-law decide, the F8/F9 tables, StageLawBurden's
    twelve law fields, CellIdx/Realizable declaration order, the zig-orientation token,
    the V3-3/V3-5/V4-6/V5-2/V7-5 named-suite splits with real unit IDs, and the §4.1
    mechanical-instance-fields row.
  - G-1/G-2 (Fable): check `cell_ne_inst` is displayed as part of V7-5c, and that
    V7-6a is genuinely split into V7-6a1 (≤3-lemma cell-suite roster) and V7-6a2
    (≤3-lemma d4r0/init_count/ent_count_card roster).

The VERIFIED-CLEAN CORES this revision claims LEFT UNTOUCHED — the A2 two-chart
arithmetic, the doctrine core, the EntIx carrier type, the V6 gate layer, PLUS (new at
REV 4, per Fable round 3) the round-3 entrance/census cluster and all six round-2
F-refutations (F-1's 128 = (1/4)·512, F-2's degree ledger, F-3's typed suite, F-4's
(q−1)² identity, F-5's revert, F-6's route roster) — should be CONFIRMED BYTE-STABLE
where the N-1/N-2/Y re-keys do not touch them, not re-derived from scratch; flag a
finding only if REV 4 silently changed one of these despite claiming not to, or if a
claimed byte-stable site actually sits downstream of a touched carrier (e.g. anything
consuming the now pool-indexed `Hist`).

Sweep fresh beyond this list too: a repair to one finding can introduce a new fault
elsewhere, and a four-round-deep patch history is exactly where regressions hide. Give
each of the 21 round-3 findings (Y-1..Y-17 with N-2 = Y-1 noted once, N-1, N-3, G-1, G-2)
an explicit disposition (REPAIRED / STILL OPEN / PARTIALLY REPAIRED with what remains,
quoting the offending text each time) plus any NEW findings, then the counts and verdict
line.

---

# PART 2 — THE FROZEN NOTE: §V-TABLES (ground truth; MOVES_2026-07-24.md lines 7829-9054)

## §V-TABLES — the measured value tables, XHD-conditional (assembly note 4, = plan [1v]-COND)

*(2026-07-27. Assembly note [1v] per ASSEMBLY_PLAN_2026-07-26.md §2v, drafted
in its strictly marked-μ̂, XHD-CONDITIONAL form — the [1v]-COND acceptance
event of the plan's REV 7 split, under the REV 9/10 sharpenings (h_ent an
explicit argument everywhere — RETYPED at REV 4: a displayed projection
of ε, V.1(iii); POST-SPLIT ι typing; RS.1-DEEP/SH/MARKED
downstream routing; the branch-cell decision; marked-μ̂ typing binding).
REV 2 (2026-07-27, same day): the pass-1 findings (VTAB_PASS1_2026-07-27.md,
7 critical / 7 gaps) repaired IN PLACE; plan citations follow REV 12 —
the shape-level multinomial is STRUCK, member-indexed convolution
everywhere, (NS-ROUTE) scoping at every (ns) site.
REV 3 (2026-07-27, same day): the pass-2 findings (VTAB_PASS2_2026-07-27.md,
3 critical / 3 gaps) repaired IN PLACE — the DISJOINT-COMPONENT convention
on every semilinear domain (F1), (iv)-MEAS retyped to the marked source
space (F2), Theorem VAL(b) relabeled (XHD-u)-conditional (F3), PART-1's
countable-partition/null-remainder route displayed (F4), the HMC-probe
step 2 pinned (F5), gate B's two-history attribution corrected (F6).
REV 4 (2026-07-27, same day): the pass-3 findings (VTAB_PASS3_2026-07-27.md,
2 critical / 1 gap) repaired IN PLACE — the entrance-height DOUBLE
PARAMETRIZATION UNIFIED (F1: a §D4-R shape-prefix P̂ already RETAINS its
per-node heights h_r and per-read side heights u*_r — §D4-R L3, rev 9 —
so ε is CONCRETE and h_ent(ε) is a displayed PROJECTION of ε's retained
data, never an independent parameter; heights are ranged via the finite
height-forgetting TEMPLATES ε̊ and the instantiation bijection —
ENT-AGG/INIT-RAT/(ENT-U)/COMP-h/COMP-AGG/VAL(b) re-indexed, every h_ent
occurrence swept); the HMC-probe's terminal step 2 given its EXIT-OBJECT
typing (F3: terminal-final templates displayed in the (v)/(vi)
signature). F2 (V-n3 not yet run) is GOVERNANCE, not text: no V.6 sealed
value changed — the census runs against the unchanged seal.
Consumes: the DUAL-ACCEPTED §C (rev 14 — C.0's coordinates/(SAE)/(NA)/(HV)
and the vtx display, C.0.5 transport, C.1/C.1.5 with (ZC), Theorem C(b),
C.3), the DUAL-ACCEPTED §D4-R (rev 9 — T_can(f), L2/L5/L11/L12, D4R.1-SUM/
-EV, D4R.4-SUM/-EV, W(P̂), mult_P̂), §M-SPECIES (rev 4,
acceptance pending — under its pass spiral; the catalogue 𝒮_n^raw, SP-FIN,
SP-OUT's syntactic successor menus), and the plan's §1s/§2v notation. This note proves CTS-M's clauses EACH
GIVEN EXACTLY the hypothesis set displayed in V.1's per-clause ledger
(rev 2, pass-1 finding 7: "CTS-M GIVEN XHD" alone was not clean — some
clauses also need ENT-COUNT, computed tables, or per-instance checks,
and clause (v) is an open kernel, not a proved clause): XHD is [2b]'s
theorem (M4a-X + M4a's affine weights + M4b-T's compatibility), NEVER this
note's duty; the recorded discharge of the hypotheses upon [2b]'s acceptance
is the separate event [1v]-FULL (no new mathematics). CTS-M(v) HMC is an
OPEN KERNEL with its own probe, consumed as a displayed hypothesis by
COMP-Σ. This note does NOT own and nowhere re-derives what [3t]
§T-ASSEMBLY owns: the verdict pin VP, TB-CAP, TREE-EXP/ONE-F — the SOLE
marked→per-f conversion (plan §1s REV 9). Everything below is conditional
on the standing perimeter (§C + §B2-DEF + §D4-R acceptance conditions,
[2a]'s pending acceptance) and, where flagged, on XHD and HMC.)*

**What this note is.** The retired torus lemma was the only bridge from
Theorem C's per-branch masses to p-independent COEFFICIENTS; the pass-1
review demolished it, and the honest rebuild is a TRANSITION SYSTEM: one
fixed p-independent state space of syntactic cells (V.2), one polynomial
table family T counting per-cell fresh-assignment transitions (V.2), and
ONE measured theorem — CTS-M (V.1) — that types how counts (T), fixed-height
weights (g), resummed weights (G), entrance masses (ι), and marked masses
(μ̂) compose. Every left-hand side in this note is a MARKED-BRANCH mass μ̂
(§1s REV 9: μ̂(E) := Σ_η μ({f : (f,η) ∈ E}) — a sum over marks BY
DEFINITION, no disjointness claimed; one f may carry several marks), never
an f-event mass and never a density. What this note hands downstream: to
[3] RESUM, the kernel entries K_e = Σ T·G, the entrance vectors ι_e with
INIT-RAT, and the COMP identities; to [3t]/[4], marked branch masses per
(ε, γ, h) (ε concrete, carrying its entrance heights h_ent(ε) — rev 4)
and the count tables. What it does NOT claim: per-f
densities (RS.1-SH's object, assembled in [3] via [3t]'s TREE-EXP), tree
pruning or verdict semantics (VP — [3t]), finite-cap detectability
(TB-CAP — [3t]), exhaustion ([5]), or any unconditional probabilistic
reading of K_e (the nine-input ledger, CL-5, lives at [3] RS.PRE).

### V.0 The XHD hypothesis package, and the acceptance split

**(XHD) THE EXACT-HEIGHT-DOMAIN PACKAGE (named hypotheses of CTS-M's
measured clauses; owner [2b] — plan §2v REV 7; stated here in the exact
form this note consumes).** Throughout, a HEIGHT POINT h of a step or
template is the tuple of its reads' ℕ-height parameters (the parameters
[2a] SP.1 forgets; d_i height slots at step i).

Ambient objects, defined here so the package is CLOSED and refutable
(pass-1 finding 1): a LINEAR SET in ℕ^D is L(h₀; P) := {h₀ + Σ_{v∈P}
n_v·v : n_v ∈ ℕ} with base h₀ ∈ ℕ^D and a FINITE period list P ⊂ ℕ^D;
SEMILINEAR := a finite union of linear sets, consumed only with the
bases and period lists EXPLICITLY LISTED per template (the "congruence-
class translates of cone lattices" gloss is struck for this definition).
THE DISJOINT-COMPONENT CONVENTION (rev 3 — pass-2 finding 1: overlapping
listed sets double-count every shared point, and inclusion-exclusion is
NOT available since intersections need not be listed): every semilinear
domain this package consumes is a PARTITION — the listed linear sets are
required PAIRWISE DISJOINT, and [2b] proves XHD-d in exactly that form
(an explicitly listed disjoint decomposition). EVERY sum over components
in this note reads this convention: Σ over listed components = Σ over
the union, term by term, no overlap correction anywhere.
REALIZABILITY is per representative: for a source representative x of α
and h ∈ ∏_i ℕ^{d_i}, T_γ(x, h) := #{fresh-assignment chains from x
realizing (γ, h)} — a finite count at each level.

> **(XHD-w) WEIGHTS.** For every step datum (m, o) with source cell α and
> target cell β, and every height point h of that step's parameter space,
> a FIXED-HEIGHT weight monomial
>     g^{α,β}_{m,o}(h) = q^{−E(h)},   E affine in h with positive weights,
> EQUAL to the per-assignment C.1.5 fresh-volume ratio at height h — the
> conditional mass, given the source cylinder at ANY representative of α
> under ANY admissible history reaching it, of one fresh assignment
> realizing (m, o, β) at h. Indexed by SOURCE AND TARGET cells (pass-6
> concern 1: (m, o) alone is under-indexed).
> **(XHD-u) UNIFORMITY (NEW at rev 2 — pass-1 findings 2–3; the count/
> domain rectangularity neither XHD-w nor XHD-d stated).** For every
> template γ with source cell α: (u-R) REPRESENTATIVE UNIFORMITY — the
> per-assignment ratio of XHD-w and the count T_γ(x, h) depend on x and
> its history ONLY through (α, β⃗, m⃗, o⃗, h); (u-T) HEIGHT RECTANGULARITY —
> T_γ(x, h) = ∏_i T_{m_i,o_i}^{β_{i−1},β_i}(q) for EVERY h ∈ H(γ):
> the count is one h-independent value per step, and every assignment
> chain counted at one h has a counterpart at every other h ∈ H(γ).
> Consumed by every T·g and T·G display below ((iv) STEP, (vi) COMP).
> **(XHD-d) DOMAINS.** For every finite template γ (length 1 included),
> the EXACT realizable height domain H(γ) ⊆ ∏_i ℕ^{d_i} is SEMILINEAR
> with its bases/periods explicitly listed and its listed components
> PAIRWISE DISJOINT (a listed PARTITION of H(γ) — the rev-3 convention),
> and EXACT two-sidedly:
> (no orphan) T_γ(x, h) > 0 for some representative x ⟹ h ∈ H(γ);
> (no stray) h ∈ H(γ) ⟹ T_γ(x, h) > 0 for EVERY representative x of α.
> **(XHD-s) SUMS.** Per listed linear set, Σ_{h} ∏_i g_i(h_i) ∈ ℚ(q)
> with geometric denominators (1 − q^{−a}), convergent at every prime
> power evaluation (positive weights). By XHD-d's disjointness the
> finitely many component sums ADD EXACTLY to the H(γ)-sum — no overlap
> terms exist (rev 3); every union-sum below reads this convention.

WHAT §C ACTUALLY SUPPLIES, displayed (the honest split of XHD-w —
pass-1 finding 2). PROVED from the accepted §C, C.1.5(1) + Lemma
TYP(b), and displayed here as this note's one §C-derivable clause:

  (U-A) ASSIGNMENT UNIFORMITY AT A FIXED HISTORY. Fix ONE realizable
  prefix satisfying (ZC) and one transition-admissible read shape
  (species m, height point h). C.1.5(1) gives, for EACH fresh
  assignment (digit cell) of that read, conditional mass
  vol_nom(E_fresh) = q^{−#(strip pins)} · ∏_slots (alphabet size)^{−1},
  and BOTH factors are functions of the read's NOMINAL DIGIT INVENTORY
  (C.1(ii)) — the strip-pin count from the shape's staircase gap, the
  alphabet sizes from TYP(b)'s piece-map images — NEVER of which values
  the cell pins. Hence all fresh assignments realizing (m, o, β) at h
  FROM THAT PREFIX carry one common conditional mass. ∎

  NOT §C-derivable, HYPOTHESIZED in (XHD-u) (they are lumpability
  assertions about histories §C never compares): (u-R) — that the
  inventory depends on the history only through the retained cell pair —
  and (u-T)'s rectangularity. Both are [2b] territory (M4a's affine
  uniformity is exactly the inventory-through-state claim); both sit in
  this note's ledger (V.5) until [2b] discharges them.

At any SINGLE FIXED height point AND fixed history, XHD-w's
identification is therefore §C content via (U-A); XHD's genuine open
content is (XHD-u), the domain exactness (XHD-d), and the closed-form
sums (XHD-s) plus E's affine form — [2b] M4a/M4a-X/M4b-T territory
(the package as displayed EXTENDS [2b]'s deliverable by (XHD-u); plan
sync flagged for the next plan rev). This note's gate V-n3 (V.6) fixes
its height points and TWO entrance histories, EACH checked separately
with the common branch-frame inventory displayed (rev 3 — pass-2
finding 6), consuming only the (U-A) face per history.

**THE ACCEPTANCE SPLIT (plan REV 7, displayed — the status discipline
binding on every consumer of this note):**

  [1v]-COND  :=  acceptance of THIS NOTE — Theorem CTS-M proved GIVEN
                 XHD. Proof-duty split by clause:
                 XHD-FREE duties of this note: (i) SYNTAX, (ii) ACT,
                 (iii)'s mass vector (ι well-typed, ENT-AGG, INIT-RAT's
                 assembly shape), and the T-half of (iv)-POLY (Theorem
                 VAL(a) ONLY: tables + cell sizes polynomial at split
                 degree bounds — VAL(b)'s chain identification is NOT
                 XHD-free, rev 3);
                 XHD-CONDITIONAL duties, proved here GIVEN XHD
                 (INCLUDING (XHD-u) — rev 2): the G-bearing clauses —
                 (iv) STEP/PART/REP/MEAS, Theorem VAL(b)'s chain-count
                 identification (rev 3 — pass-2 finding 3: the count
                 layer beyond VAL(a) is (XHD-u)-conditional), and (vi)
                 COMP ((COMP-hΣ)
                 GIVEN XHD-d/s; (COMP-Σ) additionally GIVEN (v));
                 (v) HMC: an OPEN KERNEL — stated, probed, never proved
                 here; COMP-Σ and every kernel-power identity carry its
                 tag;
                 ENT-COUNT ((iii)): a NAMED COMPANION BURDEN, per
                 entrance shape.
  [2b]       :=  proves XHD (M4a, M4a-X, M4b/M4b-T).
  [1v]-FULL  :=  the RECORDED DISCHARGE of the XHD hypotheses upon
                 [2b]'s acceptance — a bookkeeping event, no new
                 mathematics; until it is recorded, every measured
                 clause below carries the XHD tag displayed at its site.

Downstream discipline (plan REV 6): M2's τ, RS.0, RS.PRE, SQ.2 condition
on CTS cells and on NOTHING finer or coarser; [3] RESUM consumes K_e and
ι_e from this note's clauses only (no source-mass division anywhere).

### V.1 Theorem CTS-M — the measured transition system (five conditional clauses + one open kernel)

Fix n. Let 𝒞_n be the branch-cell state space and T the table family, both
constructed at V.2. PER-CLAUSE HYPOTHESIS LEDGER (rev 2 — finding 7;
each clause is asserted GIVEN exactly its listed set, nothing less):
    (i)   GIVEN [2a] SP-FIN/SP-OUT (pending) + the computed lists (D1)–(D4)
          at each consumed skeleton;
    (ii)  (ii-a/b) GIVEN (iv)-POLY's correct valuation; (ii-c) a finite
          per-(n, q₀) AGREEMENT check, per instance;
    (iii) mass primitives hypothesis-free; ENT-AGG's aggregate GIVEN
          XHD-s (shallow); ENT-COUNT a named burden; INIT-RAT GIVEN
          XHD (shallow) + (ENT-U);
    (iv)  T-half GIVEN the computed tables (Theorem VAL(a); VAL(b)'s
          chain count additionally GIVEN (XHD-u) — rev 3); PART-1
          additionally GIVEN D4R.0 totality + countable additivity +
          the null no-finite-height remainder (rev 3, V.3(iv)); measured
          faces GIVEN XHD-w + (U-A) + (XHD-u); resummed forms also
          GIVEN XHD-d/s;
    (v)   OPEN KERNEL — never proved here; (HMC-AUG) a separate named
          redesign hypothesis;
    (vi)  (COMP-h) GIVEN XHD-w's (U-A) face + (XHD-u); (COMP-hΣ) also
          GIVEN XHD-d/s; (COMP-Σ) also GIVEN (v); the solve sentence
          also GIVEN ENT-COUNT, INIT-RAT, ESCAPE(E0), (ii-c).
Then:

> **(i) SYNTAX — fixed state set, partition displayed.** 𝒞_n is ONE finite
> p-INDEPENDENT SYMBOLIC index set: Out(s) is the SYNTACTIC successor menu
> ([2a] SP-OUT — never field-evaluated; a species inadmissible at a
> particular p keeps its label and contributes empty landing sets, handled
> by (ii)); every JREF_m^source is a uniformly labelled finite partition
> with its cell predicates DISPLAYED per V.2's computed-partition duty (a
> list of relation NAMES is not a partition with polynomial
> cardinalities); and for each m : s → s′ the TARGET-CELL MAP is displayed
> and lands in JREF^src(s′) under the SAME global definition — matrix
> indices type-check, and no species-relative cell ever appears as an
> index. [Ledgered: CL-13.]
>
> **(ii) ACT — active/empty-cell semantics at every prime.** For each
> prime power q₀, Act_{q₀} := {(s, α) ∈ 𝒞_n : |α|(q₀) > 0} (|α| = the
> cell-size polynomial). Then: (ii-a) NO-ENTRY — for every source active
> at q₀, every table/kernel entry INTO a target inactive at q₀ evaluates
> to 0 there (a landing forces a concrete target state), and ι of (iii)
> is supported on Act_{q₀}; (ii-b) DELETION COMPATIBILITY — ordering
> states active-first, K_e(q₀) is block-triangular [[A, 0],[C, D]]: the
> realized system at q₀ IS the A-block ("chain" struck at rev 2 — rows
> are MARKED OFFSPRING rows per (iv)-PART-2, a branching-kernel reading,
> not a stochastic chain), every measured statement
> of (iii)–(vi) reads ONLY the A-block, so deleting empty rows/columns at
> each prime is COMPATIBLE with the one fixed symbolic matrix; (ii-c)
> ACTIVE-VALUE — the realized value at each q₀ is DEFINED through the
> active subsystem alone (β_A = A·β_A + b_A, the ι-pairing reading only
> A-block coordinates); the burden is AGREEMENT: at the finitely many q₀
> with empty cells, the symbolic ℚ(q)-solution's value component, after
> cancellation, EVALUATES to the active-subsystem value — any
> det(I − D)(q₀) = 0 checked REMOVABLE on that component. A formal row
> out of an empty cell is NEVER cited as a probability; no division by a
> zero cell mass occurs anywhere.
>
> **(iii) INIT — entrance mass AND entrance count, both refined by
> ENTRANCE SHAPE; entrance heights RETAINED IN ε (rev 4 — pass-3
> finding 1: h_ent is a displayed PROJECTION of ε, never an independent
> parameter).** An ENTRANCE SHAPE ε
> into (e, β₀) is a NEW object of this note (rev 2 — finding 9: it is
> NOT a §D4-R shape-prefix, which forgets selection data): the TRIPLE
> ε := (P̂, b, σ_sel) of a shallow CONCRETE §D4-R shape-prefix P̂ —
> which RETAINS its per-node heights h_r (the (e, h, g, μ, a) tuples)
> and its per-read side heights u*_r (§D4-R L3, rev 9) — a designated
> continuing branch b entering the size-e block landing in cell β₀, and
> the branch-selection record σ_sel = (s_r at every shallow branching
> cell b passed — L11's encoding data, lifted into the label), so
> entrances are POST-SPLIT objects: at a shallow split each sibling
> carries its OWN ε and its OWN mark.
> HEIGHT PROJECTION (the rev-4 unification): h_ent(ε) := the tuple of
> ε's RETAINED height data — the (h_r, u*_r) pair vector over P̂'s reads
> (exactly the ℕ-height parameters [2a] SP.1 forgets) — a FUNCTION of ε,
> displayed, no free height variable anywhere: one concrete ε FIXES its
> entrance heights. TEMPLATE/INSTANTIATION (how heights are ranged):
> ε̊ := ε's height-forgetting TEMPLATE (SP.1 applied to P̂, selection
> data kept); the family {ε̊} is FINITE ([2a]/M1 for the P̂-templates;
> L5's finite eligible-continuation menus for the σ_sel's); H(ε̊) := the
> exact realizable entrance-height domain of the template (XHD-d on the
> shallow layer); and the INSTANTIATION MAP h ↦ ε̊[h] (write the heights
> h into the template's retained slots) is a BIJECTION from H(ε̊) onto
> {concrete ε with template ε̊} — D4R.1-SUM is cited ONLY at concrete ε,
> where P̂ is a genuine §D4-R shape-prefix (pass-3 F1's two horns
> closed: no duplication, and the instantiation map displayed).
> Primitives, per CONCRETE ε (h_ent(ε) determined by ε):
>     ι_{e,ε,β₀}(p) := the D4R.1-SUM MARKED mass μ̂ of the
>       entrance family refined by ε (each summand Theorem
>       C(b); an f entering twice carries two marks — a μ̂-object,
>       never an f-event mass);
>     I^ent_{ε,β₀}(q) := #{realized shallow entrance prefixes of
>       shape ε whose continuation lands in β₀} — a MARKED
>       count, with ledger exponent A(ε) := §D4-R's A(P̂) (a function
>       of ε since u*_r ∈ P̂ — L3; affine in h_ent(ε) across each
>       template's instantiations, [2b] M4a) and pool dimension
>       W_ent(ε) := Σ_{r ∈ reads(ε)} w_r·d_r (= §D4-R's W(P̂) —
>       height-free, L3 rev 9: W consumes no u*_r, so ONE degree bound
>       per template).
> ENT-COUNT (named burden): each I^ent_{ε,β₀} is one polynomial
> in q of degree ≤ W_ent(ε), computed as a CTS path count through the
> shallow layer. I^ent_{ε,β₀} = |β₀| is NOT general — a per-family
> theorem, displayed wherever used. Counts at different ε are NEVER
> added raw (distinct A(ε)). ENT-AGG (the derived aggregate — masses DO
> aggregate; rev 2, finding 10 — its conditionality split; RE-INDEXED
> at rev 4 on the template/instantiation pair): ι_{e,β₀} :=
> Σ_{ε̊} Σ_{h ∈ H(ε̊)} ι_{e,ε̊[h],β₀} — entrance heights are summed HERE
> and nowhere else, each concrete ε hit EXACTLY ONCE (the instantiation
> bijection). The primitives and every FINITE partial sum are
> hypothesis-free (μ̂-additivity over disjoint mark families — distinct
> concrete ε give distinct marked pairs); CONVERGENCE of the full
> aggregate (infinitely many instantiations per template) is GIVEN
> XHD-s on the shallow layer,
> and (iv)-REP is invoked ONLY where a common continuation factor is
> pulled out ((COMP-AGG)), never for the sum's definition.
> INIT-RAT (named burden): each ι_{e,(s,α)} ∈ ℚ(q), hence
> ι_e ∈ ℚ(q)^{𝒞_n} — GIVEN XHD on the shallow layer; CITED by RS.2.
> The pairing ι_e^T β_e is the μ̂-typed MARKED-entrance total over
> post-split marks — consumed by (COMP-AGG) and the gates, NEVER a
> clause of the density R_σ (RS.1-SH assembles R_σ — [3]).
>
> **(iv) STEP — correctly normalized measured rows.** One-step kernel
> entry, from ONE representative x ∈ α:
>     K_e(q)_{(s,α),(s′,β)} := Σ_{m: s→s′} Σ_{o continuing}
>       T_{m,o}^{α,β}(q) · G^{α,β}_{m,o}(q)    — NO source-mass division,
> G^{α,β}_{m,o} := Σ_{h ∈ H(γ¹)} g^{α,β}_{m,o}(h) the resummed one-step
> height mass over XHD-d's exact length-1 domain (well-typed from XHD
> alone; no HMC at k = 1; rationality = XHD-s per component over the
> PAIRWISE DISJOINT listed components, finitely many — rev 3). UNIFORMITY CONSUMPTION, displayed at the
> product (rev 2 — findings 2–3: T·G is NOT licit from XHD-w/d alone):
> the height-resolved row is Σ_{h ∈ H(γ¹)} T_{m,o}^{α,β}(h)·g(h) with
> T(h) := #{fresh assignments producing (m, o, β) at h}; it equals
> T·G because (U-A) makes g one constant per (m, o, β, h) at the fixed
> history, (XHD-u)(u-R) makes that constant and the count depend only on
> (α, β, m, o, h), and (XHD-u)(u-T) makes T(h) = T one h-independent
> count — Σ_h T(h)·g(h) = T·Σ_h g(h) is EXACTLY (u-T), else false in
> general. Each g-summand is ALREADY conditional on the
> source cylinder (XHD-w = the C.1.5 ratio); dividing again inflates the
> conditional. K_e is entrance-height-FREE: entrance heights ride in ε
> (retained data, rev 4), hence in ι alone.
> Sub-clauses: (iv)-POLY — every entry T is one polynomial of degree
> ≤ W_loc(m) and every cell size one polynomial of degree ≤ W_state(s)
> (SPLIT bounds — a source-cell size belongs to (s, α), not to any
> outgoing m), valued correctly at every prime power, with V.2's
> EXPONENT-MAP AUDIT; (iv)-PART — RETYPED at rev 2 (finding 5: one digit
> cell may carry SEVERAL eligible (side, ψ) continuations — D4-R L5 —
> so the (m, o, β)-indexed sets do NOT partition the pool). Two faces:
> (PART-1, the partition identity, per representative) the DIGIT CELLS
> of the read partition the fresh pool (D4R.0/L5), each cell counted
> ONCE; summing the per-cell conditional masses over the whole partition
> (all shapes, heights, values, terminal cells included) gives 1 —
> a COUNTABLE partition across heights, mass 1 by the rev-3 route at
> V.3(iv) (fixed-height pools finite via C.1.5(1), countable additivity,
> null no-finite-height remainder — NOT a finite-pool identity). (PART-2, the marked offspring row)
> the kernel row Σ_{m,o,β} T·G counts each branching cell once PER
> eligible continuing mark, so Σ_{m,o,β} T·G + (terminal conditional
> mass) = 1 + (branch surplus), surplus := the mass of continuing marks
> beyond each cell's first — a MARKED OFFSPRING mass, possibly > 1: NO
> substochasticity is claimed for K_e's rows; any substochastic reading
> routes through PART-1 alone. (At n = 3 the surplus vanishes
> identically — two continuing clusters need sizes ≥ 2 + 2 > 3, so no
> digit cell carries two continuing marks; first possible surplus at
> n = 4. Verified over the V.6 rosters.)
> (iv)-REP — WEIGHTED representative independence: the MEASURED
> row (T·G)_{m,o,β} is identical from every representative of α
> (cardinality-row equality alone is insufficient) — the lumpability
> clause M2(ii) consumes; (iv)-MEAS — RETYPED at rev 3 (pass-2 finding
> 2: ordinary-source disjointness contradicts D4-R L5 — one digit cell
> may carry two eligible (side, ψ) continuations whose next-node strata
> are literally EQUAL as f-sets; PART-2 exists because these sets do
> NOT partition): every (m, o, β, height-class) summand is a measurable
> sub-event of the MARKED source space {(f, η)} — a finite-level digit-
> cell union (D4R.0/L12) with the continuation mark ADJOINED to the
> finite-level map — and the summands are pairwise disjoint IN THE
> MARKED SPACE; as f-events only the DIGIT CELLS are disjoint. No
> ordinary-source disjointness is claimed anywhere.
>
> **(v) HMC — height-domain Markov compatibility. OPEN KERNEL, displayed
> hypothesis.** For every template γ, the whole-template exact domain
> FACTORS stepwise:
>     H(γ) = ∏_i H(γ¹_i),   γ¹_i := (β_{i−1} →^{m_i,o_i} β_i),
> each factor depending ONLY on the retained state β_{i−1} and the step
> data — never on earlier height choices — so Σ_{h ∈ H(γ)} ∏ g_i(h_i) =
> ∏_i G^{β_{i−1},β_i}_{m_i,o_i}. TERMINAL-FINAL EXTENSION (rev 4 —
> pass-3 finding 3, the displayed signature): templates INCLUDE those
> whose FINAL step carries a terminal outcome o_k; there β_k := the
> absorbing column label [o_k] — an EXIT OBJECT ((iv)-PART's absorbing
> columns; verdict semantics [3t]'s, the label consumed only as a
> column index) — the step's height coordinates, weight g, and count T
> typed as for any read, H(γ¹_k) and G_k reading verbatim, and NO
> target-cell map consumed ((D4)'s duty covers continuing outcomes
> only). The pinned HMC probe's step 2 (V.4) is a literal instance of
> THIS signature. (HMC-AUG) — a SEPARATE named redesign
> hypothesis, NOT a consequence of HMC (rev 2, finding 12; ledgered
> V.5): if a global cone inequality couples successive steps, ONE round
> of 𝒞_n refinement by finitely-valued boundary/gap data restores the
> factorization; finite-memory repair need not be possible at all — a
> second surviving coupling is R2's wall channel. Until HMC closes,
> K_e(p)^k is NOT a theorem about the process and only the unfactored
> per-template sum (COMP-hΣ) holds.
>
> **(vi) COMP — the composition identities, μ̂-typed.** For every
> finite path template γ = (β₀ →^{m₁,o₁} β₁ → … → β_k) in block e and
> every CONCRETE entrance shape ε into (e, β₀) (ε carrying its retained
> entrance heights h_ent(ε) — rev 4): the MARKED EVENT of
> (ε, γ, h) is the family of marked pairs (f, η) — its MARK-INDEX
> family (the realized histories η) is FINITE per level and its level-N
> residue census is finite (D4R.4); the f-fibers are p-adic boxes,
> generally INFINITE (rev 2, finding 13 — never "finitely many f") —
> whose branch η has entrance shape ε (entrance heights h_ent(ε)),
> template γ, height point
> h; its mass is μ̂ := Σ_η μ(S(η, ⊤)) (V.4 — a sum over marks; equal-
> strata branches each contribute their own summand). Then:
>     (COMP-h)  at every concrete ε and fixed h ∈ H(γ):
>       μ̂(marked event of (ε, γ, h) at p) = ι_{e,ε,β₀}(p)
>         · ∏_{i=1}^k [T_{m_i,o_i}^{β_{i−1},β_i} ·
>                       g^{β_{i−1},β_i}_{m_i,o_i}(h_i)](p);
>     count shadow: I^ent_{ε,β₀}·∏_i T (same concrete ε).
>     (COMP-hΣ)  GIVEN XHD-d/s, NO HMC (rev 2, finding 11 — the
>       unfactored height sum carries its OWN name; "COMP-Σ" is ONLY
>       the factored form): Σ_{h ∈ H(γ)} μ̂(…) = ι_{e,ε,β₀} ·
>       Σ_{h ∈ H(γ)} ∏_i [T·g(h_i)] — a well-defined XHD-s series,
>       per template;
>     (COMP-Σ)  GIVEN additionally (v) HMC — the factored form:
>       Σ_{h ∈ H(γ)} μ̂(…) = ι_{e,ε,β₀} · ∏_{i=1}^k [T·G]_i;
>     (COMP-AGG)  summing (COMP-Σ) over entrance heights (via the
>       instantiation bijection) then over templates ε̊ via ENT-AGG
>       (licit by (iv)-REP): Σ_{ε̊} Σ_{h ∈ H(ε̊)} (COMP-Σ at ε̊[h]) =
>       ι_{e,β₀} · ∏ (T·G) — the
>       FAM-side μ̂-identity RS.PRE/RS.1 consume; masses aggregate,
>       counts do NOT.
> COMPOSITION-TYPING DUTY: every consumer sums entrance heights EXACTLY
> ONCE (ENT-AGG's instantiation sum) and path heights EXACTLY ONCE,
> via (COMP-h)→(COMP-hΣ)→(COMP-Σ) — G never at a height point, g never
> in a kernel entry. GIVEN XHD, (i)–(v), ENT-COUNT, INIT-RAT, (ii-c),
> and ESCAPE(E0) on the
> ACTIVE submatrix: ρ(A) < 1 at each prime evaluation, the Neumann
> series converges, and det(I − K_e) ≢ 0 in ℚ(q) — hence the rational
> solve exists; every downstream fixpoint assertion carries this
> conditionality until E0 and (v) close.

### V.2 The state space 𝒞_n, the branch-cell decision, and the tables T

**(CTS-S) THE STATE SPACE.** A SKELETON s is a bounded current-state datum:
residual degrees/multiplicities, anchor a, tower phase — the [2a] SP.1
stage/side/residual-shape fields of the CURRENT node, values and heights
forgotten. Out(s) := the finite p-INDEPENDENT SYNTACTIC menu of outgoing
move-species labels emittable from s ([2a] SP-OUT + M1 bookkeeping ALONE,
evaluated over NO residue field). The SOURCE partition of s's concrete
states is the MEET over the WHOLE menu:
    JREF^src(s) := ⋀_{m ∈ Out(s)} JREF_m^source,
JREF_m^source := the common refinement of
 (a) the per-coordinate ANCHOR-TWISTED VAL.1 cell partitions of the
     residual-factor value tuple (below), and
 (b) the RELATIONAL strata of exactly the finitely many polynomial
     relations m's displayed evaluation/admissibility maps mention:
     factor collision/distinctness (φ_i = φ_j), hinge-ratio cells (the
     twisted cell of t_i/t_j), and the norm/trace strata tested by
     (NA)/(HV) (§C C.0) and the nonzero-endpoint convention
— EVERY source observable used by EVERY syntactically-listed outgoing
species, admissibility judged over no field (an m inadmissible at some p
keeps its label; its landing sets are empty there — (ii)'s zero-extension
is built into the definition). The CTS states are 𝒞_n := {(s, α) :
α ∈ JREF^src(s)}; finiteness follows from finiteness of Out(s) (a finite
meet of finite partitions); cells with IDENTICALLY-zero size polynomial
are deleted from 𝒞_n once, symbolically.

**BRANCH-CELL DECISION (plan REV 8, binding).** A CTS cell is a
BRANCH-CELL: its concrete states are states of ONE continuing branch of
T_can(f) in that branch's own frame, and the CTS walks SINGLE branches —
every transition consumes the branch's next read, T counts per-branch
fresh assignments from one representative, every measured step factor is
a per-branch Theorem C(b)/C.1.5 object. The alternative (f-cells with
set-valued transitions) is REJECTED: §C has no mass theorem for
joint-over-branch loci and the tables would not be §C-citable.
CONSEQUENCE (binding on FAM): BRANCHING EXITS TO THE FAM LAYER — a read
whose digit cell carries several eligible (side, ψ) continuations
contributes each continuation as a SEPARATE branch entry, composed
multiplicatively by [3t]'s (SIB)/TREE-EXP at the REV-10 routing sites
(b_e^split at DEEP splits; RS.1-SH's convolution at ROOT/SHALLOW splits),
never a raw sum of separately-inserted child entrances; MULTIPLICITY
WEIGHTS (mult, D4R.1) are carried by the FAM aggregation — never inside
T, never inside a single-branch path product.

**THE COMPUTED-PARTITION DUTY (CTS-M(i)'s deliverable — CL-13; what must
be COMPUTED, displayed).** The meet symbol above is a construction
RECIPE; the clause-(i) deliverable, per skeleton s consumed by any
downstream instance claim, is the DISPLAYED LIST:
 (D1) the menu Out(s) — the [2a] SP-OUT letters from s;
 (D2) the GENERATOR LIST — every (a)-generator (one twisted VAL.1
      partition per residual coordinate, the twist exponent displayed)
      and every (b)-generator (each relation named WITH its polynomial
      and its exceptional-characteristic convention, e.g. the char-2
      collapse of a distinctness stratum);
 (D3) the MEET LIST — the resulting finite uniform partition: explicit
      cell predicates as boolean combinations of (D2)'s generators,
      fixed labels, per-cell size polynomials |α|(q) (degree ≤
      W_state(s));
 (D4) the TARGET-CELL MAP per m : s → s′, displayed, landing in
      JREF^src(s′) under the same global definition.
This note displays the recipe and computes (D1)–(D4) IN FULL at V.6.1–
V.6.3 for the three gate blocks (rev 2 — finding 14: displayed in the
note, not referred to a seal); the FULL per-skeleton lists at each
consumed n are the TABLE-BUILD deliverable — [1v]-COND acceptance
requires them for every skeleton any downstream instance claim
consumes (V.5).

**VAL.1 (the stratified fiber calculus — the (a)-generators).** For each
node species the EVALUATION MAP V sends the node's side-pattern value
tuple to its transported vertex value (C.0's display: vtx =
z̄^{−μm̂}·z̄^{a}·((R_anch/ψ^μ) mod ψ)); the fiber-count function
c_V : Fˣ → ℕ, c_V(t) := #{pattern values : V = t}, is NOT constant (the
pass-1 counterexample: values 0 and 1 at fixed shape). VAL.1's content:
c_V is CONSTANT on the cells of an explicit p-independent stratification
of the target. Worked instance (V(A,B) = Aα + B, A, B ∈ F_qˣ; target
coordinates t = xα + y in the basis {α, 1} of F_{q²}/F_q): THREE cells —
FG = {x ≠ 0, y ≠ 0}, c_V = 1; FL = F_qˣ·α (y = 0), c_V = 0 (B = 0
prohibited); FS = F_qˣ (x = 0), c_V = 0 (A = 0 prohibited). ANCHOR
ALIGNMENT (probe-forced, binding): at anchor exponent a_eff ≠ 0 the cells
apply to the TWISTED target α^{−a_eff}·t, never to t in the fixed frame —
fixed-frame cell counts are PROVABLY char-dependent (the value probe,
verification/value_probe.py + results: 32 non-universal series, a q mod 3
split at a_eff = 2), while TWISTED cells are fiber-constant EXACTLY at
all 24 census q. Cell sizes and counts are universal polynomials; the L3
necklace/Gauss counts are the depth-0 instance.

**(CTS-T) THE TABLES.** For every source cell α ∈ JREF^src(s), species
m : s → s′ ∈ Out(s), full outcome label o (next-node data + all
hinge-value cells + collision pattern, or a terminal label — the [2a]
L5-case letters; verdict SEMANTICS is [3t] VP's, consumed here only as
absorbing column labels), and target cell β ∈ JREF^src(s′):
    T_{m,o}^{α,β}(q) := #{fresh assignments producing (m, o, β) │ one
                          representative source state in α}.
**Theorem VAL (the count layer — split degree bounds).** (a) LOCAL: every
entry T_{m,o}^{α,β} is ONE polynomial in ℚ[q] of degree ≤ W_loc(m), and
every cell size |α| ONE polynomial of degree ≤ W_state(s), each valued
correctly at every prime power q. (b) CHAIN — GIVEN (XHD-u)'s COUNT
FACE (RELABELED at rev 3, pass-2 finding 3: NOT XHD-free): for each
finite path template γ, the PER-REPRESENTATIVE linked count from one
fixed source representative EQUALS the PATH PRODUCT C_γ(q) =
∏_i T_{m_i,o_i}^{β_{i−1},β_i}(q). Clause (i)'s one global partition
makes the product a DEFINED matrix operation (typing only); the
IDENTIFICATION with the actual linked count needs every concrete
target representative inside each intermediate cell to emit the SAME
next-step count — exactly (u-R)'s count clause + (u-T), hypothesized
in (XHD-u), never proved here (alternative discharge: the table build
proves representative-uniform count rows per species and the ledger
cites that proof). The degree bound ≤ W(γ) = Σ_i W_loc(m_i) holds for
the ACTUAL linked count unconditionally (per-step pools bound it); the
FULL realization count is PER (concrete) ENTRANCE SHAPE: Ĉ_{ε,γ}(q) =
I^ent_{ε,β₀}(q)·C_γ(q) (same (XHD-u) tag, plus ENT-COUNT), degree
≤ W̄(ε,γ) = W_ent(ε) + W(γ) — the entrance factor never omitted, never
smuggled into T, never replaced by |β₀| without the displayed
one-unrestricted-copy theorem, never summed raw across entrance shapes
with different A(ε). NO path product is a mass or a full count without
its initial factor: ∏ T counts extensions from ONE representative.

**EXPONENT-MAP AUDIT (a (iv)-POLY burden, displayed).** Every norm/trace/
ratio/collision exponent map in every table's evaluation chain is audited
for congruence factors (e.g. the image size of t ↦ t^a on F_{q^g}ˣ is
(q^g − 1)/gcd(a, q^g − 1)); "triangular/monomial shape" alone is NOT
accepted as a polynomiality argument — each such factor either cancels
against a displayed cell-size factor or splits the cell into displayed
congruence sub-cells with their own labels ((D2)'s conventions).

**DEG-CONS (per-outcome degree conservation — the [3t]/[3] display duty
executed at THIS note's table build; CL-11).** For EVERY branching
outcome o in the CTS outcome roster: m ≥ 2 children, each child cluster
size e_j ≥ 1, Σ_j e_j ≤ e — per member, from M1's degree identity applied
to the cell's residual-factor degrees. The check runs over the FULL
roster of each computed table block ((D1)–(D4)); an analogy to "the same
degree identity" is not the check. Executed and DISPLAYED for the V-n3
blocks (V.6.1–V.6.3); a full-roster obligation of the table build at
each consumed n.

**(†) epistemics at the count layer (recalled, binding).** Per table
entry/row (degree bound W_loc(m)), per cell size (W_state(s)), per finite
template (W(γ)), per full count (W̄(ε,γ)): 0 ≤ C(q) ≤ q^W at every prime
power, so agreement with any R ∈ ℚ(q) at all prime powers forces R
polynomial of degree ≤ W — the unique interpolant through any W+1 census
points; one exact census mismatch surviving adjudication CONCLUSIVELY
refutes ℚ(q)-universality (refute-or-support; support at surplus
m − W − 1 is evidence, never proof). Aggregates only via (†-AGG): the
marked level-N count marked(N) := Σ_{(ε,γ): thr ≤ N} Ĉ_{ε,γ}(q)·
q^{nN−A(ε)−A(γ)} — each summand at its OWN displayed normalization, a
μ̂-object NEVER identified with decided_σ(N) (instance (2), which is
[3t]/[4] territory via input (vii)'s tree-shape sum). Rev 3: the
per-template and full-count rows read the ACTUAL linked counts — the
bounds are unconditional, while the identification with ∏T and
I^ent·∏T carries VAL(b)'s (XHD-u) tag; a census mismatch there indicts
the conjunction, per V.6.5's attribution discipline.

### V.3 The measured clauses — proof routes and per-clause status

**(i) SYNTAX — XHD-free; status RESTATED at rev 2 (finding 6: full-depth
SYNTAX was overstated).** What is proved HERE: the meet of finitely many
finite uniform partitions is finite and uniform, and labels are fixed by
(D2)/(D3)'s conventions — GIVEN finiteness and p-independence of Out(s),
which is [2a] SP-FIN/SP-OUT (syntactic menus over the budget
inequalities (B1)–(B5), no field evaluated) and INHERITS [2a]'s PENDING
acceptance. What is NOT proved here: the uniform partitions themselves,
polynomial cell sizes, target maps, and exponent audits at any skeleton
whose lists are uncomputed — each is a PER-SKELETON burden, executed in
this note ONLY for the three V.6 gate blocks (displayed there in full).
Clause (i) at full depth is therefore CONDITIONAL on [2a] + the
table-build deliverable (CL-13), never "proved by construction" bare.

**(ii) ACT — XHD-free; status: (ii-a)/(ii-b) proved GIVEN (iv)-POLY's
correct valuation; (ii-c) a displayed per-instance burden.** (ii-a): a
table entry counts fresh assignments landing ON a concrete target state;
at q₀ with |β|(q₀) = 0 there is no state to land on, the definitional
count is 0, and (iv)-POLY's "valued correctly at every prime power"
forces the polynomial's value there to be 0; ι's support claim is the
same argument at the entrance layer. (ii-b): order states active-first;
by (ii-a) every active-source → inactive-target entry vanishes at q₀, so
K_e(q₀) = [[A, 0],[C, D]] and every measured statement reads the A-block
(the realized process has no mass on inactive cells — their defining
predicates are unsatisfiable over F_{q₀}). (ii-c) AGREEMENT is a
FINITE per-(n, q₀) verification duty (finitely many q₀ have empty
cells): symbolic-solution value = active-subsystem value after
cancellation, det(I − D)(q₀) = 0 checked removable on that component —
exercised by RESUM-n3's wild-p ACTIVE-VALUE layer ([3]'s gate), recorded
here as the clause's standing check, never a blanket det ≠ 0 claim. NO
general deletion-compatibility theorem for the rational solution is
claimed anywhere (finding 8): agreement is per-instance, finite,
ledgered at V.5(5).

**(iii) INIT — per-concrete-ε primitives hypothesis-free; the
aggregate GIVEN XHD-s (shallow); ENT-COUNT, (ENT-U), INIT-RAT displayed
burdens.** WELL-TYPEDNESS of ι_{e,ε,β₀} (proved): ε = (P̂, b,
σ_sel) is V.1(iii)'s refined entrance label — a CONCRETE §D4-R
shape-prefix P̂ (retaining its heights h_r, u*_r — L3 rev 9) with a
designated continuing branch and recorded
selection data s_r (L11), the triple a NEW object of this note (finding
9) — so the entrance family is a sub-family of
Pref(P̂) cut by the landing-cell condition on the continuing branch
(cell data, L5); the entrance heights h_ent(ε) are NOT a separate cut
but ε's OWN retained data (rev 4 — pass-3 finding 1: h_ent lives IN P̂
via (h_r, u*_r), no independent height parameter);
each member is a single realized branch prefix η with its Theorem C(b)
mass μ(S(η,⊤)), and ι is their SUM — a D4R.1-SUM sub-sum, hence a
μ̂-object; an f entering twice carries two marks, matching the
per-branch solve. POST-SPLIT TYPING (proved by construction): siblings
at a shallow split differ in s_r, hence carry DISTINCT ε — ι never
aggregates a pre-split f-event or a joint-sibling locus. ENT-AGG
(finite partial sums proved hypothesis-free; the full aggregate GIVEN
XHD-s on the shallow layer — finding 10): μ̂ is additive over disjoint
mark families (distinct concrete ε give distinct marked pairs;
the instantiation bijection hits each ε once);
convergence over the infinitely many instantiations is XHD-s's, and
(iv)-REP enters ONLY when the aggregate is paired with a common
continuation factor ((COMP-AGG)), never for the sum itself. ENT-COUNT
(BURDEN, per template): each I^ent_{ε,β₀} is one polynomial of degree ≤
W_ent(ε) (= W(P̂), height-free — L3)
— Theorem VAL's machinery applied to the shallow cascade (root cells =
the L3 depth-0 instance; each shallow read a table step; the
landing-cell refinement a target-cell condition). (ENT-U) (BURDEN,
NAMED at rev 2 — finding 4: without it INIT-RAT is NOT derivable, since
XHD-s covers products of the g_i, not an arbitrarily entrance-height-
varying polynomial multiplier): over each listed linear set c of
H(ε̊) (the template's entrance-height domain), the
polynomial I^ent, viewed across the instantiations ε̊[h] with h ∈ c,
=: I^ent_c is ONE polynomial CONSTANT in
h on c — [2b] M4b's h_ent-constancy clause, never assumed here.
INIT-RAT (BURDEN, GIVEN XHD on the shallow layer + (ENT-U)):
ι_{e,(s,α)} = Σ_{ε̊} Σ_{c ⊆ H(ε̊)} I^ent_c(q) · Σ_{h ∈ c}
p^{−A(ε̊[h])}, c ranging over XHD-d's PAIRWISE DISJOINT listed
components of H(ε̊) (the rev-3 partition convention — each
instantiation counted exactly once, no overlap correction), with
A(ε̊[h]) affine in h
(M4a) — the inner sum XHD-s geometric, the outer sums finite — hence
∈ ℚ(q); CITED by RS.2.

**(iv) STEP — T-half XHD-free (Theorem VAL(a) ONLY; VAL(b)'s chain
identification is (XHD-u)-conditional — rev 3); measured sub-clauses
GIVEN XHD-w's (U-A) face + (XHD-u), resummed forms also XHD-d/s (the
V.1 ledger).**
 (iv)-POLY: the T-half is Theorem VAL(a) — VAL.1 twisted-cell constancy
   makes each (m, o, β) count a product of cell sizes and fiber counts
   over the displayed strata, polynomial after the EXPONENT-MAP AUDIT
   (V.2); the split bound W_state(s) covers source-cell sizes (a source
   cell belongs to (s, α), not to any outgoing m, and may exceed some
   W_loc(m)). Status: mechanism displayed; per-entry closed forms are
   the table-build deliverable, gate-sealed at V.6.
 (iv)-PART (PART-1 GIVEN XHD-w's (U-A) face at fixed history + D4R.0
   totality + countable additivity + the null remainder + XHD-d/s —
   rev 3; the resummed faces GIVEN XHD-d/s + (XHD-u)) — retyped per
   finding 5, route COMPLETED per pass-2 finding 4 (mass 1 is NOT a
   finite-pool consequence of C.1.5(1)): AT EACH FIXED height point
   the fresh pool is finite and its DIGIT-CELL datum is a total
   single-valued function of the fresh assignment (digit cells
   partition — D4R.0/L5; the menu is total per [2a] SP-COMP,
   conditional on its stated perimeter); ACROSS heights the digit-cell
   decomposition of the source cylinder is COUNTABLE. PART-1's route,
   displayed: (a) TOTALITY — outside the no-finite-height locus every
   source point lies in exactly ONE digit cell (D4R.0); (b) COUNTABLE
   ADDITIVITY of the conditional measure over this countable
   partition; (c) NULL REMAINDER — the no-finite-height locus
   (all-window degeneracy) lies in the decreasing intersection of the
   height-≥-H strip cylinders, whose conditional masses → 0 (C.1.5
   strip volumes; XHD-s positive weights), hence μ-null; (d) each
   fixed-height block sums by C.1.5(1)'s conditional exactness —
   together, the per-cell ratios over the whole partition sum to 1.
   The CONTINUATION datum is NOT
   single-valued (L5's multi-eligible cells), so the (m, o, β)-indexed
   row is PART-2's marked offspring row: = 1 − (terminal mass) +
   (branch surplus), surplus ≡ 0 at n = 3 (V.1(iv)); no substochastic
   claim survives except through PART-1.
 (iv)-REP (GIVEN XHD-w's (U-A) face + (XHD-u)(u-R) — REP is (u-R)'s
   row-level consequence, restated as the checkable clause M2(ii)
   consumes): the measured row from x ∈ α is a function of
   (a) x's twisted VAL.1 cell data and (b) x's relational strata — by
   construction JREF^src(s) refines EVERY observable every listed
   species consumes, so the row is cell-constant PROVIDED the species'
   evaluation maps mention no observable outside the (a)/(b) generator
   list. That proviso is a PER-SPECIES CHECK of the table build
   (executed with (D2); refuter: JOINT-probe below); weighted (T·G)-row
   equality, not cardinality-row equality, is what is checked.
 (iv)-MEAS (stated lemma, GIVEN XHD-d; RETYPED rev 3 — pass-2 finding
   2): each (m, o, β, height-class) summand's f-PROJECTION is a
   finite-level digit-cell union (D4R.0 strata realized at the finite
   level L12/D4R.4 provides); the summand ITSELF is that union with
   the continuation mark ADJOINED — the fiber of a finite-level map ON
   THE MARKED SPACE {(f, η)}, the branch label a coordinate of the
   map. Disjointness holds in the marked space ONLY; two summands'
   f-projections can be literally EQUAL (D4-R L5). Multi-step events
   are the (vi) marked-event displays: finite mark-disjoint unions of
   finite-level marked cylinders, never single cylinders.

**ENTRANCE-HEIGHT THREADING (the REV 9 rule, RETYPED at rev 4 —
pass-3 finding 1: entrance heights are ε's retained data, not a free
argument).** K_e and every T/G/g factor are entrance-height-FREE; ι
is indexed by the CONCRETE ε (whose retained h_ent(ε) is displayed,
not a separate argument); (COMP-h) fixes ε and the path height h and
displays both; (COMP-Σ) sums h ONLY; ENT-AGG/(COMP-AGG) sums over the
instantiations ε̊[h] (i.e. entrance heights) EXACTLY ONCE.
Height elimination from the block unknowns (β carries no height index)
is RS.0(β)'s bisimulation — [3]'s theorem (CL-9), nowhere assumed here.

### V.4 COMP — the composition identities, HMC, and the [3t] interface

**The marked event, fully typed (the (vi) left side; plan §1s REV 9).**
The MARKED-BRANCH SPACE is M := {(f, η) : η ∈ T_can(f)}. The marked
event of (ε, γ, h) at p is the family of pairs (f, η) whose
branch η has entrance shape ε (entrance heights h_ent(ε), ε's retained
data — rev 4), template γ
(the CTS path of its in-block reads — single-branch, V.2's decision),
and height point h; its MARK-INDEX family is FINITE at each level and
its level-N residue census is finite (D4R.4) — the f-fibers themselves
are p-adic boxes, generally infinite (finding 13) — and its
mass is the MARKED MASS μ̂ := Σ_η μ(S(η,⊤)) — a sum over the mark index
BY DEFINITION: same-shape branches with literally EQUAL strata each
contribute their own summand (F1's instance is not an obstruction but
the typing's reason). NO ordinary event mass μ appears anywhere in
clause (vi); no disjointness across marks is claimed or needed.

**(COMP-h) — proof route (GIVEN XHD-w's (U-A) face + (XHD-u); ε concrete
and path height h FIXED).** Group the marked event by its entrance
prefix: each member extends exactly one ε-shaped entrance (heights
h_ent(ε)) landing in β₀. Per
entrance mark, the continuation mass along γ at h is the C.1.5
conditional chain — per step, (U-A) makes each fresh assignment's ratio
one common value at the fixed history, (XHD-u)(u-R) makes that value and
the count the SAME across representatives and histories reaching β₀
(the hypothesized lumpability face — findings 2–3, displayed, not
derived), giving T_{m_i,o_i}^{β_{i−1},β_i}·g(h_i) per step. Summing
over the entrance marks gives ι_{e,ε,β₀}·∏ T·g — the displayed
identity; the count shadow I^ent·∏ T is the same grouping at the count
layer (Theorem VAL(b) — carrying its (XHD-u) count-face tag, rev 3 —
+ ENT-COUNT, the same concrete ε on both sides — a marked-history
count). At a FIXED path height point AND one fixed entrance history, the
identity consumes only (U-A)'s §C-derivable content; V-n3 gates that
per-history face at each of its TWO entrance histories SEPARATELY,
with the common inventory displayed (V.6.4 — rev 3).

**(COMP-hΣ)/(COMP-Σ) — the naming discipline (finding 11).** Summing
(COMP-h) over h ∈ H(γ) GIVEN XHD-d/s yields the unfactored per-template
series (COMP-hΣ) — always well-defined, no HMC. The right side factors
into ∏(T·G), i.e. (COMP-hΣ) upgrades to (COMP-Σ), IF AND ONLY IF the
whole-template domain factors stepwise with state-only dependence —
exactly (v) HMC, a displayed open hypothesis. Until HMC closes, only
(COMP-hΣ) holds, and K_e^k is not a theorem about the process.

**HMC-probe (exploration-class, specced-and-pinned with this draft — NOT
yet run, no result claimed; the rev-8 spec,
typing-safe; tested family PINNED at rev 2, finding 12).** THE FAMILY:
p = 2, the V.6 objects — entrance ε := the A1 root entrance (designated
branch = the μ = 2 track; retained h_ent(ε) = (), V.6.4), source cell β₀, two
consecutive s_blk2 steps: step 1 := (m₂, o_double, β₁) at heights
h₁ = (k₀ = 2λ₁), λ₁ ranging over the censused domain {1, 2, 3}; step 2
— PINNED at rev 3 (pass-2 finding 5): SOURCE = β₁ (V.6.3 (D4): the
⊤-cell of the refined-cluster skeleton s_blk2⁽²⁾, recentered at y*,
|β₁| = 1); the depth-2 window is again NP over (0, v(h₀⁽²⁾)),
(1, v(h₁⁽²⁾)), (2, 0) in the RECENTERED branch frame (the s_blk2 form
one level down at the AUGMENTED anchor — tower phase depth 2; the
anchor exponent recorded from C.0.5 transport at the instance, a
monitored probe datum, exactly where HMC may fail); SPECIES m₂⁽²⁾ :=
the one-side stride-1 residual-degree-2 letter (V.6.3 (D1)'s m₂ read
at s_blk2⁽²⁾); sealed OUTCOME o₂ := o_inert (absorbing label
[e=1, f=2] — a TERMINAL-FINAL step in the (v)/(vi) signature (rev 4 —
pass-3 finding 3): its EXIT OBJECT is the absorbing column β₂ := [o₂]
(the [e=1,f=2] label as a target index — verdict semantics [3t]'s),
so the template γ = (β₀ →^{m₂,o_double} β₁ →^{m₂⁽²⁾,o_inert} [o₂]) IS a
literal instance of the displayed HMC/COMP template (β₂ typed, height
coordinate h₂ and weight g⁽²⁾ read verbatim; NO continuing target-cell
map is consumed because (D4) covers continuing outcomes only — the
terminal step needs none, not one that is "not needed");
HEIGHT COORDINATE h₂ := (k₀⁽²⁾ = 2λ₂), the depth-2 side height in the
recentered frame; source generators at s_blk2⁽²⁾ expected EMPTY by
V.6.3's executed check (the letter reads only h⁽²⁾'s own digits) —
the census READS the actual dependence rather than assuming it.
SEALED HMC-EXPECTED conditional domain and law, per fixed h₁: domain
{k₀⁽²⁾ = 2λ₂ : λ₂ ≥ 1} INDEPENDENT of λ₁; per-h₂ conditional mass
T_{o_inert}·g⁽²⁾ = [q(q−1)/2]·q^{−3λ₂}│_{q=2} = 2^{−3λ₂} (E⁽²⁾ = 3λ₂,
the V.6.3 affine form one level down). Censused pairs (λ₁, λ₂):
λ₁ ∈ {1, 2, 3}, all λ₂ whose event data are determined at box level
≤ N = 7 (the gate-B feasibility bound); the seal records the per-pair
determination levels BEFORE the census runs, and pairs undetermined at
N = 7 are recorded OUT OF SCOPE, never partially censused. Two layers: (a) COMP-h layer (typing check, no
HMC content) — sealed height pairs (h₁, h₂), exact census of
fixed-height marked masses vs ι·T·g(h₁)·T·g(h₂), only fixed-height
monomials g appearing; (b) HMC layer — for each FIXED h₁ across its
exact one-step domain, census the CONDITIONAL step-2 height domain and
per-h₂ mass law given (m₁, o₁, β₁ at h₁): HMC predicts both INDEPENDENT
of h₁ given β₁; after summing over h₂ ONLY, the fixed-h₁ two-step
marked mass equals ι·T·g(h₁)·(T·G)₂ — G only after the h₂-sum, h₁ never
summed. SCOPE (finding 12): the probe is a ONE-INSTANCE REFUTER testing
the CONJUNCTION {HMC at this template + XHD-w/(U-A)/(XHD-u) + (iv)-REP};
it cannot support (v)'s universal "every template" quantifier, and a
pass is evidence only. Any surviving h₁-dependence beyond the retained
state refutes the conjunction and — if adjudication (V.6's order)
localizes it to (v) — triggers (HMC-AUG)'s one refinement round, itself
a hypothesis (V.1(v)); a second coupling is R2's wall channel.

**(COMP-AGG) — GIVEN (COMP-Σ) + (iii).** Sum over the instantiations
ε̊[h] (h ∈ H(ε̊), i.e. entrance heights) then over templates ε̊ via
ENT-AGG: Σ_{ε̊} Σ_{h ∈ H(ε̊)} (COMP-Σ at ε̊[h]) = ι_{e,β₀}·∏(T·G) —
entrance heights summed exactly once, the FAM-side μ̂-identity. Counts
do NOT aggregate this way (distinct A(ε) across templates — V.1(iii)).

**THE [3t] INTERFACE (what this note HANDS OVER, and what it does NOT
claim — the plan's ownership fence, restated as binding).**
 HANDED to [3]/[3t]/[4]: (1) marked branch masses per (ε, γ, h) (ε
   concrete, carrying h_ent(ε) — rev 4)
   and their resummed forms — the (COMP-h)/(COMP-Σ)/(COMP-AGG)
   identities, every left side μ̂-typed; (2) the count tables T, C_γ,
   Ĉ_{ε,γ}, I^ent with their degree bounds; (3) K_e and ι_e as [3]
   RS.PRE consumes them (no source-mass division; ι paired once on the
   left; b_e is [3]'s object — this note supplies its T·G entries via
   (iv)-PART's absorbing columns, not its multilinear split formula);
   (4) DEG-CONS's per-outcome roster check at the computed blocks.
 NOT CLAIMED here: per-f densities or f-counts — every output of this
   note is a μ̂-object or a marked count; the marked→per-f conversion
   is [3t]'s TREE-EXP ALONE (its (ONE-F) dictionary, its tree fibers),
   and the pairing ι_e^T(I − K_e)^{−1}b_e is the μ̂-typed MARKED-
   entrance total (RS.1-MARKED) — consumed by (COMP-AGG) and gates,
   NEVER summed into R_σ (the density is RS.1-SH's shallow convolution,
   [3]). Equating any μ̂ quantity of this note with an f-event mass or
   an f-count is a TYPE ERROR except through [3t]'s displayed
   conversion. VP, TB-CAP, tree pruning: [3t]'s, consumed only as
   terminal outcome LABELS in o. STATUS NOTE (2026-07-27): §T-ASSEMBLY
   is DUAL-ACCEPTED (Codex pass 8 + Fable confirm, both CLEAN on the
   rev-7 text — the EOF record); nothing in THIS note consumes a [3t]
   THEOREM — only the plan-level typing rule (§1s REV 9) and the
   ownership fence, so [3t]'s repair rounds do not propagate here.

### V.5 Honest perimeter (what is conditional, on what, and what is only evidence)

CONDITIONAL ON, named per the acceptance-record rule (plan §7):
 (1) XHD — OPEN, owner [2b] (M4a/M4a-X/M4b-T), INCLUDING the rev-2
   clause (XHD-u) (findings 2–3: representative uniformity (u-R) +
   height rectangularity (u-T) — hypothesized, NOT §C-derivable; the
   package extension is flagged for the next plan rev) AND the rev-3
   DISJOINT-COMPONENT form of XHD-d (pass-2 finding 1: [2b] proves the
   listed decomposition PAIRWISE DISJOINT — the partition convention
   every component sum reads). (XHD-u) also carries Theorem VAL(b)'s
   chain-count identification and the full-count formula Ĉ (rev 3 —
   pass-2 finding 3: the count layer beyond VAL(a) is never XHD-free).
   Every G-bearing
   clause ((iv) measured faces, (vi) COMP) is proved here GIVEN its
   V.1-ledger set; the discharge is the separate recorded event
   [1v]-FULL. Only (U-A) — assignment uniformity at a fixed history —
   is §C-derivable now (V.0, displayed derivation); domains and sums
   are not anticipated anywhere in this note.
 (2) HMC (CTS-M(v)) — OPEN KERNEL, its probe (family pinned) at V.4.
   Until it closes: (COMP-hΣ) per template only, K_e^k not a process
   theorem, and every downstream fixpoint claim carries the tag ([3]'s
   nine-input ledger, CL-5, item 6). (HMC-AUG) — the finite-memory
   augmentation REPAIR — is a SEPARATE named hypothesis (finding 12),
   not a consequence of HMC and not assumed anywhere.
 (3) ENT-COUNT, (ENT-U), and INIT-RAT — named burdens of clause (iii):
   shallow-layer polynomiality per entrance shape (degree ≤ W_ent(ε));
   per-linear-set h_ent-constancy ((ENT-U), owner [2b] M4b — finding 4:
   INIT-RAT is underivable without it); ℚ(q) assembly GIVEN XHD +
   (ENT-U). RS.2 cites INIT-RAT; it is not yet proved.
 (4) The VAL.1/JREF deliverables — the computed-partition lists
   (D1)–(D4) per consumed skeleton, the per-entry closed forms with the
   EXPONENT-MAP AUDIT, the per-species (iv)-REP observable check, and
   DEG-CONS's full-roster check: DISPLAYED duties of the table build,
   executed in this note only for the three V.6 gate blocks (displayed
   IN FULL there — rev 2, finding 14; nothing is "pinned in the seal"
   that is not also derivable from the note text).
   [1v]-COND acceptance requires the lists for every skeleton any
   downstream instance claim consumes at its n.
 (5) (ii-c) ACTIVE-VALUE agreement — a finite per-(n, q₀) check,
   exercised by RESUM-n3's wild-p layer ([3]); recorded, not proved.
 (6) Inherited: §C (rev 14 conditions incl. (SAE)'s dual-pass status as
   recorded at its acceptance), §B2-DEF, §D4-R (D4R.0-K's residual is
   [3t]/VP territory), and [2a] §M-SPECIES — acceptance PENDING; this
   note's (iv)-PART cites SP-COMP's per-read totality and so carries
   SP-COMP's conditionality (D4R.0-K, (SAE)) until [2a] is accepted.
 (7) ESCAPE(E0) — [3]'s duty; cited only inside (vi)'s conditional
   solve sentence, never claimed.
EVIDENCE, NOT PROOF (the probe roster; exploration-class, no seals):
 - the VALUE probe (verification/value_probe.py + results): all 15
   probed linked totals interpolated UNIVERSAL with surplus ≥ 15;
   twisted-cell fiber constancy EXACT at all 24 census q while
   fixed-frame cells are provably char-dependent — the anchor-alignment
   clause is probe-forced and now part of VAL.1's statement;
 - JOINT-probe (runs with this draft): one species with k = 2 linked
   children sharing a parent + one sibling-collision condition, exact
   F_q joint census over the 24-q list — row constancy on JREF^src
   cells vs on products of marginal cells; a marginal-constant/
   joint-varying finding refutes any state type lacking relational
   strata;
 - COMPOSE-probe (same run): one two-step family, step-1 target cell
   consumed as step-2 source — exact census of two-step linked counts
   vs the matrix product of sealed one-step tables, the count layer
   carrying its sealed entrance factor at ONE sealed ε (any
   I^ent = |β₀| identification displayed as sealed per-family, never a
   rule); an exact mismatch refutes the conjunction {(i)'s typing +
   VAL CHAIN's (XHD-u) count face} at k = 2 (rev 3 — CHAIN is
   (XHD-u)-conditional, so the probe tests that face too);
 - HMC-probe (V.4).
THE REDESIGN BRANCH (VAL.3 — unexercised): if some table entry or
template count is PROVEN non-polynomial (a census refutation per (†))
AND aggregate cancellation is PROVEN, the aggregate-block architecture
[3′] replaces [3] (plan §2v VAL.3 — 3+ units, own verification); a
proved NON-cancellation at some σ and wild p is the R1 wall. Probe
status keeps the trigger unexercised; the branch stays specified and
unbudgeted. The plan's VALUE-Fq (24-q sealed table layer) and VALUE-p
(n = 5 p-adic shadow) gates REMAIN STANDING obligations of the full
table build, distinct from and additional to V-n3 below.

### V.6 Sealed gate V-n3 (the obligation — table block both ways + one COMP-h instance)

**GATE STATUS: PASSED (2026-07-27) — 178 exact checks, 0 failures.** The
seal (`verification/CASE_VN3_SEALED_PREDICTIONS.md`, transcribed from
V.6.1–V.6.4 before any census code) and the census
(`case_vn3_gate.py`, results json committed): A1 — all 45 root-table
entries exact at the nine q, Σ = q³ per q, m_H3 = 0 at q = 2 exactly;
A2 — T = (q−1)² at all nine q, the p = 2 digit census 32 = 2¹²·2⁻⁷
exact; the s_blk2 rows identical at both representatives ((iv)-REP);
gate B — 16 marked pairs at N = 3 and 128 at N = 4, μ̂ = 2⁻⁵ exact,
count shadow 2, box-precision exact (zero event-word changes). Cited as
support, not closure: XHD/(XHD-u)/(ENT-U)/HMC remain open hypotheses
with their owners; VALUE-Fq/VALUE-p remain standing obligations.

Spec discipline: seal-before-census (Case-K), FREE CHOICES pinned
BELOW IN THE NOTE (rev 2, finding 14: nothing lives only in an external
seal — every predicted number is derivable from THIS section's
displays), predictions EXACT integers/dyadic rationals, attribution a
CONJUNCTION (TASM pass-1 finding 14: no scheme may claim to isolate a
clause its layers only jointly exercise). The seal file
verification/CASE_VN3_SEALED_PREDICTIONS.md TRANSCRIBES V.6.1–V.6.4 and
is written before the census script case_vn3_gate.py runs. Census
q-list: q ∈ {2, 3, 4, 5, 7, 8, 9, 11, 13} (prime powers deliberately
included); every entry below has degree ≤ 3, so the nine-point census
carries per-entry surplus ≥ 5 per (†).

**V.6.1 Block A1 — the root skeleton s₀ (n = 3), computed.** The root
node: no history, fresh read = the reduction f̄ = z³ + āz² + b̄z + c̄
over F_q (three fresh digits; pool q³; W_loc(root) = 3; W_state(s₀)=0).
 (D1) Out(s₀) — five letters, the monic-cubic reduction geometries:
   m_H3 [three distinct linear factors] TERMINAL (3 Hensel tracks);
   m_H12 [linear × irreducible quadratic] TERMINAL ([1,1]+[1,2]);
   m_H⟨3⟩ [irreducible cubic] TERMINAL ([e=1,f=3]);
   m_2+1 [ψ²χ, ψ ≠ χ linear] CONTINUING — μ = 2 cluster into the
     size-2 block (+ sibling Hensel track, FAM's);
   m_3 [ψ³, deg ψ = 1] CONTINUING — μ = 3 cluster into the size-3 block.
 (D2) source generator lists (a)/(b): EMPTY — the root source is the
   empty history, so the meet is trivial; the letters' own strata are
   factorization-type predicates (char-free; no discriminant formula is
   used, so NO exceptional-char convention is needed at this block).
 (D3) meet list: JREF^src(s₀) = {α₀}, predicate ⊤, |α₀|(q) = 1
   (degree 0 ≤ W_state(s₀) = 0). One representative — the "two
   representatives" census clause is VACUOUS here (recorded).
 (D4) target maps: m_2+1 ↦ β₀ ∈ JREF^src(s_blk2) (V.6.3): the
   assignment f̄ = (z−α)²(z−β) lands at hinge value t := β̄ − ᾱ ∈ F_qˣ,
   always in β₀ = the ⊤-cell (t ≠ 0 by distinctness); m_3 ↦ β_3 :=
   the single ⊤-cell of the size-3 entry skeleton, |β_3| = 1 (recentering
   at the triple root retains no residual value).
 TABLE (one row; closed forms; each degree ≤ W_loc = 3):
   T_{m_H3}   = q(q−1)(q−2)/6      T_{m_H12}     = q²(q−1)/2
   T_{m_H⟨3⟩} = (q³−q)/3           T_{m_2+1}^{α₀,β₀} = q(q−1)
   T_{m_3}^{α₀,β_3} = q
 PART-1 count face, displayed: (q³−3q²+2q)/6 + (3q³−3q²)/6 + (2q³−2q)/6
   + (6q²−6q)/6 + 6q/6 = q³ = pool. ✓
 DEG-CONS (full roster): m_H3: 3 children (1,1,1), Σ = 3 ≤ 3 ✓;
   m_H12: (1,2) ✓; m_2+1: (2,1) ✓; m_H⟨3⟩, m_3: single-child (m = 1,
   no branching check applies). ✓
 PREDICTED EVALUATIONS at the nine census q (rows in the (D1) order;
 final row = the PART-1 sum q³):
   q:        2    3    4    5     7     8     9    11    13
   m_H3:     0    1    4   10    35    56    84   165   286
   m_H12:    2    9   24   50   147   224   324   605  1014
   m_H⟨3⟩:   2    8   20   40   112   168   240   440   728
   m_2+1:    2    6   12   20    42    56    72   110   156
   m_3:      2    3    4    5     7     8     9    11    13
   Σ = q³:   8   27   64  125   343   512   729  1331  2197
**V.6.2 Block A2 — the wild-heavy side skeleton s₁, computed (the SP.1
data formerly "pinned in the seal", now DISPLAYED).** After the root
letter m_3 (f̄ = z³, recentered: f = z³ + az² + bz + c with v(a), v(b),
v(c) ≥ 1), the size-3 window is the NP over (0, v(c)), (1, v(b)),
(2, v(a)), (3, 0). s₁ := the branch state riding the SIDE from (0, h₀)
to (2, h₂) of STRIDE e = 2: slope (h₀−h₂)/2 with h₀ − h₂ ODD
(fractional; WILD at p = 2 since p │ e); the third root rides the
sibling side (2, h₂)–(3, 0) (a separate branch, FAM's). Anchor exponent
a_eff = 0 (untwisted vertex values at this node); tower phase: depth 1,
first window.
 HEIGHT DOMAIN (displayed ILLUSTRATION of XHD-d's format — the gate
 FIXES its heights and consumes no domain hypothesis): realizability =
 {h₂ ≥ 1 (vertex), h₀ > 3h₂ (hull strictness), h₀ − h₂ odd}; with
 h₂ = t ≥ 1, h₀ = 3t + 2u + 1 (u ≥ 0) this is the ONE linear set
 L((4,1); {(3,1), (2,0)}) in coordinates (h₀, h₂) — base and periods
 explicitly listed; a ONE-component decomposition, so the rev-3
 disjointness convention holds vacuously.
 FRESH VALUES at fixed (h₀, h₂): u₀ := the level-h₀ digit of c ∈ F_qˣ,
 u₂ := the level-h₂ digit of a ∈ F_qˣ (side support = endpoints only:
 the interior point (1, (h₀+h₂)/2) is half-integral — no lattice digit);
 v(b) ≥ (h₀+h₂+1)/2 is pure STRIP. Pool (F_qˣ)²; W_loc(m_w) = 2.
 (D1) Out(s₁) = {m_w} — ONE letter: residual R(y) = u₂y + u₀ (degree
   length/e = 1), root y₀ = −u₀/u₂ ∈ F_qˣ, ALWAYS multiplicity 1 —
   the branch's factor is certified irreducible, absorbing verdict
   label [e = 2, f = 1] (label only; VP semantics [3t]'s; μ = 1
   certification is wildness-independent — A2's wild-heavy content is
   the parity class, the p = 2 census point, and the (D2) convention).
 (D2) source generators: EMPTY (see D3). Outcome hinge-value cell: the
   untwisted (a_eff = 0) VAL.1 cell of y₀ — one cell F_qˣ with fiber
   count c_V ≡ q − 1 (for fixed y₀, #{(u₀,u₂) : −u₀/u₂ = y₀} = q−1; a
   worked two-variable VAL.1 instance, char-free). Exceptional-char
   convention: at char 2 the sign in y₀ = −u₀/u₂ collapses (−1 = 1);
   no cell and no count changes — displayed as the convention.
 (D3) meet list: JREF^src(s₁) = {α₁}, predicate ⊤, |α₁|(q) = 1
   (recentering retains no residual value), W_state(s₁) = 0.
 (D4) no continuing letter — vacuous. DEG-CONS: vacuous over Out(s₁)
   (no m ≥ 2 outcome); the window-level sibling split upstream has
   children 2 + 1, Σ = 3 ≤ 3 ✓ (M1's degree identity), recorded at the
   entrance layer.
 TABLE: T_{m_w, [y₀-cell]}^{α₁, [e=2,f=1]} = (q−1)², degree 2 ≤ 2 ✓;
   PART-1: (q−1)² = pool ✓ (one letter).
 WEIGHT (the (U-A) face, displayed derivation — used at the census
 heights): new digit pins beyond the entry cylinder {v(a),v(b),v(c)≥1}:
 c: (h₀−1) strip zeros + 1 value pin; a: (h₂−1) + 1; b: (h₀+h₂−1)/2
 strip zeros; so g(h₀,h₂) = q^{−E}, E = (3(h₀+h₂)−1)/2 — affine,
 positive weights. Sealed census height point: the base (h₀,h₂) =
 (4, 1): E = 7, per-assignment conditional mass q^{−7}.
 PREDICTED EVALUATIONS, T = (q−1)²:
   q:      2    3    4    5     7     8     9    11    13
   T:      1    4    9   16    36    49    64   100   144

**V.6.3 Block B-step — the size-2 block skeleton s_blk2, computed
(displayed IN the note because gate B consumes its table).** s_blk2 :=
the m_2+1 target: in the branch frame f = u·h with h = z² + h₁z + h₀
the distinguished quadratic (v(h₀), v(h₁) ≥ 1) and u the unit cotrack;
concrete states = the hinge value t ∈ F_qˣ; window = NP over
(0, v(h₀)), (1, v(h₁)), (2, 0).
 (D1) Out(s_blk2) — three letters:
   m₂ [one side (0, 2λ)→(2, 0), λ ∈ ℤ≥1, stride 1, residual degree 2]:
     fresh (u, w) ∈ F_qˣ × F_q (u := level-2λ digit of h₀; w := level-λ
     digit of h₁ — w = 0 encodes v(h₁) > λ); R(y) = y² + wy + u;
     outcomes: o_split (two distinct roots in F_qˣ — 2 terminal
     tracks), o_inert (irreducible — terminal [e=1,f=2]), o_double
     (double root y* ∈ F_qˣ — CONTINUING, μ = 2 refined cluster → β₁);
   m_w2 [one side, slope k₀/2, k₀ odd, stride 2]: fresh u ∈ F_qˣ,
     residual degree 1 — terminal certified [e=2,f=1] (the V.6.2
     pattern one level down);
   m_vv [two sides, vertex (1, k₁), 2k₁ < k₀]: fresh (u₀,u₁) ∈ (F_qˣ)²
     — two degree-1 sides, 2 terminal tracks at distinct heights.
 (D2) source generators: EMPTY — none of the three letters' displayed
   evaluation maps reads t (residual coefficients are h's OWN digits;
   the lead at (2,0) is monic — no hinge/anchor twist, a_eff = 0);
   this is the executed per-species (iv)-REP observable check for this
   block. Outcome strata (they live in o, not in the source): for m₂,
   odd q: the square class of disc := w² − 4u (split ⟺ nonzero
   square, inert ⟺ nonsquare, double ⟺ 0); char 2: the
   Artin–Schreier convention — double ⟺ w = 0; for w ≠ 0, split ⟺
   Tr_{F_q/F_2}(u/w²) = 0, inert ⟺ Tr = 1. DISPLAYED
   exceptional-char convention; the closed forms below are the SAME
   polynomials under both.
 (D3) meet list: JREF^src(s_blk2) = {β₀}, predicate ⊤ on the state
   space F_qˣ (t ≠ 0), |β₀|(q) = q − 1, degree 1 ≤ W_state = 1.
   Representatives censused: t = 1, and t = 2 at q ≥ 3 ((iv)-REP's
   count face; at q = 2 the cell has one state — recorded).
 (D4) m₂/o_double ↦ β₁ := the ⊤-cell of the refined-cluster skeleton
   (recentered at y*; no retained residual value; |β₁| = 1); all other
   letters absorbing.
 TABLE for m₂ (pool q(q−1) per representative; degrees ≤ W_loc(m₂)=2):
   T_{o_split} = (q−1)(q−2)/2   [pairs {r,s} ⊆ F_qˣ, r ≠ s; char-2
     recount (q−1)(q/2 − 1) — equal];
   T_{o_inert} = q(q−1)/2   [all monic irreducible quadratics — the
     constant is automatically nonzero; char-2 recount (q−1)·q/2];
   T_{o_double}^{β₀,β₁} = q − 1   [(y−r)², r ∈ F_qˣ; char 2: w = 0,
     u ∈ F_qˣ — equal].
   PART-1 count face: (q−1)(q−2)/2 + q(q−1)/2 + (q−1) = q(q−1) ✓.
   Other letters: T_{m_w2} = q − 1; T_{m_vv} = (q−1)².
 DEG-CONS (full roster): m₂/o_split children (1,1), Σ = 2 ≤ 2 ✓;
   m_vv (1,1) ✓; o_double single child size 2, m_w2 single child —
   no branching check. ✓
 PREDICTED EVALUATIONS:
   q:          2    3    4    5     7     8     9    11    13
   o_split:    0    1    3    6    15    21    28    45    66
   o_inert:    1    3    6   10    21    28    36    55    78
   o_double:   1    2    3    4     6     7     8    10    12
   Σ = q(q−1): 2    6   12   20    42    56    72   110   156
   m_w2:       1    2    3    4     6     7     8    10    12
   m_vv:       1    4    9   16    36    49    64   100   144
**V.6.4 Gate B — ONE COMP-h instance vs a §D4-R fiber mass, p = 2, all
heights fixed, every number displayed (consumes only (U-A)'s
§C-derivable face at TWO fixed entrance histories, EACH checked
separately, the common inventory displayed below — rev 3, pass-2
finding 6: the gate is an aggregate over two histories, never a
one-history exercise — V.0/V.4).**
 ENTRANCE: ε := (P̂ = the root m_2+1 prefix, b = the μ = 2 branch,
   σ_sel = its (side, ψ)-selection at the root cell) — V.1(iii)'s
   refined label; landing cell β₀ (V.6.3). The root read carries d = 0
   height slots, so ε RETAINS no height data: h_ent(ε) = () and the
   template ε̊ = ε with H(ε̊) = {()} (rev 4's unified typing — the root
   read is HEIGHT-FREE, so the projection h_ent(ε) is the empty tuple
   and the instantiation is trivial; supersedes rev 1's "minimal
   realizable root-side height"); ledger exponent A(ε) = 3 (three
   reduction digit pins), W_ent(ε) = 3.
 ENTRANCE COUNT/MASS: I^ent_{ε,β₀}(q) = T_{m_2+1} = q(q−1)
   (every ψ²χ entrance lands in β₀ — V.6.1 (D4)), degree 2 ≤ 3 ✓;
   note I^ent = q·|β₀| ≠ |β₀| — the displayed instance of
   "I^ent = |β₀| is NOT general". ι_{2,ε,β₀}(q) = q(q−1)·q^{−3}
   (each entrance mark carries the D4R.1-SUM summand q^{−3});
   AT p = 2: I^ent(2) = 2 (the two marked histories: f̄ = z²(z+1) and
   f̄ = (z+1)²z), ι = 2·2^{−3} = 1/4.
 TWO-HISTORY DISCIPLINE (rev 3 — the finding-6 repair): (U-A) is
   applied PER HISTORY, separately to each of the two marked entrance
   histories. Both land at the SAME β₀ state (t = β̄ − ᾱ = 1 for
   z²(z+1); t = −1 = 1 at p = 2 for (z+1)²z), and in EACH history's
   branch frame (recentered at that history's double root) the step
   read carries the SAME nominal digit inventory: the window NP over
   (0, v(h₀)), (1, v(h₁)), (2, 0), fresh (u, w), pins E = 3λ — a
   function of the window shape ALONE (C.1(ii)), which the recentering
   shift never enters. Hence T = 1 and g = 2^{−3} for each history BY
   DISPLAY, and the aggregate 2·2^{−3}·(step factor) exercises no
   (XHD-u) content — the commonality is DERIVED, not assumed.
 STEP: γ¹ = (β₀ →^{m₂, o_double} β₁) at sealed λ = 1, i.e. height
   point h₁ = (k₀ = 2). From V.6.3: T_{o_double}(2) = q−1│_{q=2} = 1 —
   the unique cell (u, w) = (1, 0): R = y² + 1 = (y+1)², y* = 1.
   WEIGHT: new pins beyond {v(h₀) ≥ 1, v(h₁) ≥ 1}: h₀ — one strip zero
   (level 1) + the level-2 value pin; h₁ — the level-1 digit w = 0:
   E(h₁) = 3λ = 3, g = 2^{−3} = 1/8 (general E = 3λ — affine ✓).
 SEALED EXACT PREDICTIONS:
   μ̂(marked event) = ι·T·g = (1/4)·1·(1/8) = 2^{−5} = 1/32 (the
     dyadic mass); count shadow = I^ent(2)·T(2) = 2·1 = 2.
 THRESHOLD N := 3, with the derivation displayed: the entrance datum is
   f mod 2; f̄ has the double and simple roots reduction-separated, so
   the coprime (Hensel) factorization f = u·h lifts uniquely with
   h mod 2^k determined by f mod 2^k for EVERY k; the step data are
   v(h₀) = 2 with unit digit (h₀ ≡ 4 mod 8 — level 3) and v(h₁) ≥ 2
   (h₁ ≡ 0 mod 4 — level 2). So level 3 determines every event datum.
 PREDICTED CENSUS COUNTS: marked pairs among the 2^{3N} residues =
   μ̂·2^{3N} = 2^{3N−5}: N = 3: 16; N = 4: 128 (= 16·2³ EXACTLY, zero
   event-word changes — BOX-PRECISION, the SIB-gate B22 pattern);
   marked-history count = 2 at both levels.

**V.6.5 Census duties (definitional side; scripts written AFTER the
seal transcribes V.6.1–V.6.4).**
 (A-side, blocks V.6.1–V.6.3) exhaustive enumeration over F_q at the
   nine census q of all fresh assignments, from ≥ 2 representatives per
   active cell WHERE the cell has ≥ 2 states (β₀ at q ≥ 3; vacuities
   recorded above). CHECKED EXACTLY, zero tolerance: every entry value
   against its closed form (per-entry surplus ≥ 5 per (†)); the
   PART-1 count identity per representative; identical rows from
   distinct representatives ((iv)-REP's count face); every landing
   inside the displayed (D4) target cell ((i)); the m_H3 zero at q = 2
   (a genuine falsifier: the census must find EXACTLY 0). NO displayed
   cell size vanishes at any census q (sizes 1, q−1, 1) — (ii-a)'s
   empty-cell check is VACUOUS at these blocks, recorded honestly (the
   wild-p ACTIVE-VALUE layer remains RESUM-n3's, V.5(5)).
 (B-side, V.6.4) exhaustive enumeration of f mod 2^N (box 2^{3N},
   N = 3 then N = 4; feasible through N = 7), counting MARKED pairs —
   per mark, an f realizing the event on two branches counted twice,
   exactly as μ̂ demands. PASS = marked count 16 (N = 3) and 128
   (N = 4), and marked-history count 2, ALL EXACT.

 ATTRIBUTION (sealed with the predictions — finding-14 discipline).
   Layers A and B JOINTLY test the conjunction {the computed partition
   (D1)–(D4) + the closed-form tables ((iv)-POLY, T-half) + target
   typing ((i)) + the partition/representative count faces ((iv)-PART/
   REP count faces) + the COMP-h typing at fixed heights and TWO fixed
   entrance histories checked separately ((vi), (U-A)'s §C-derivable
   face PER HISTORY, the common inventory displayed at V.6.4 — no
   (XHD-u) content is exercised; per-h counts censused directly)
   + the upstream §C/§D4-R laws they consume}. A surviving
   mismatch INDICTS THE CONJUNCTION — no layer isolates one clause.
   Adjudication order (sealed): (1) prediction-derivation error
   (Case-K); (2) re-run the upstream face on the same box (D4R.4-SUM
   count for B; raw pool totals for A) — if upstream reconfirms, the
   failure localizes to THIS note's layer but NOT to a single clause;
   (3) a theory error triggers plan §8 R1's isolation experiment BEFORE
   any further RESUM work, and the (†) protocol decides any
   non-polynomiality claim (one exact mismatch, surviving (1)–(2),
   refutes universality of that entry conclusively).
 GOVERNANCE. [1v]-COND may NOT be accepted before V-n3 passes; V-n3
   joins the plan §7 roster beside the standing VALUE-Fq/VALUE-p
   obligations (V.5). This note's acceptance record must name: the XHD
   tag ([1v]-FULL pending [2b]), HMC's open status + probe result,
   ENT-COUNT/INIT-RAT status, computed-list coverage (which skeletons),
   both gate results, the [2a] pending-acceptance inheritance, and the
   probe roster as evidence-only — per the acceptance-record rule.

CONSOLIDATED ACCEPTANCE-RECORD PERIMETER (rev 7, per V.6.5's rule —
what any acceptance record of this note must name): the XHD package
(XHD-w/-d/-s, owner [2b]) + (XHD-u) (representative-uniformity +
height-rectangularity, owner [2b]) + (ENT-U) (owner [2b], M4b) as OPEN
hypotheses — the XHD tag ([1v]-FULL pending [2b]); (U-A) PROVED here; HMC an OPEN kernel (its probe is
specced-and-pinned at V.4 but has NOT run — no result is claimed;
evidence-only when it does); ENT-COUNT + INIT-RAT as this note's named
burdens (INIT-RAT rederived GIVEN XHD + (ENT-U)); the computed-list
coverage duty (CTS-M(i)/CL-13: the V.6 skeletons cover THREE cells'
lists (s₀/α₀, s₁/α₁, s_blk2/β₀), not the full n = 3 partition — the full
(D1)–(D4) table build for every consumed skeleton is THIS note's
[1v]-COND/CL-13 burden (PENDING), resting on [2a]'s SP-FIN/SP-OUT (the
PENDING syntactic-menu inheritance underlying clause (i))); the V-n3 gate PASSED with BOTH
components (the definitional table census A-side and the COMP-h gate B)
— support, never closure; VALUE-Fq/VALUE-p standing; the probe roster
evidence-only. Nothing in this note claims per-f content ([3t]'s fence).

*(End of §V-TABLES, rev 7 — 2026-07-27: the pass-2 repairs (disjoint

---

# PART 3 — THE MovesS SOURCE (real, E-phase-built Lean; ground truth for what the seam actually
# owes/demands) + §W4-SYNC (the seam contract, from MOVESS_LEAN_BLUEPRINT_2026-07-28.md REV 13,
# lines 1116-1346) — do not trust MovesV's own restatement of either.

--- lean/LeanUrat/MovesS/Defs.lean (full) ---

/-
MovesS/Defs — shared vocabulary for MOVES §S-RESUM (the depth resummation core).

E-phase transcription of `lean/notes/MOVESS_LEAN_BLUEPRINT_2026-07-28.md` (REV 13,
core accepted by adjudicated closure) §2.A–§2.C + the §2.D Defs-part (MuHat/ReadOwner/
Shape/ShapeFam/consumedDeltas/RegP).  Declaration order = spec.  The skeleton defs the
blueprint displays with `sorry` bodies (OKat/evalAt, kTarget, Kmat, bTerm,
consumedDeltas) are FILLED here per the E-phase discipline (Defs sorry-free); their
LAW units (U-19, U-16a3, …) stay sorried in their own files.  Nothing in this file
asserts mathematics — it fixes the vocabulary §S-RESUM's statements are typed in.
-/
import Mathlib

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix Polynomial

/-- D1: the symbolic carrier ℚ(q). -/
abbrev Qq := RatFunc ℚ

variable {n : ℕ}

/-! ## §2.A Combinatorial layer (owner MovesV/MovesSp rosters) -/

/-- A branch member.  `δ` is the base-change FACTOR contributed at this nesting step;
the SEMANTIC index rel. the base prime is the product along the chain (CONVENTION
DELTA-ABS, R17; [2r] (e2)); no δ = 0. -/
structure Member (V : Type*) (State : ℕ → Type*) where
  size   : ℕ
  δ      : ℕ+
  status : V ⊕ State size

def Member.continuing {V : Type*} {State : ℕ → Type*} (μ : Member V State) : Prop :=
  μ.status.isRight = true

structure Outcome (V : Type*) (State : ℕ → Type*) where
  mem : List (Member V State)
  hm  : mem ≠ []

section OutcomeDefs
variable {V : Type*} {State : ℕ → Type*}

def Outcome.m (o : Outcome V State) : ℕ := o.mem.length
def Outcome.c (o : Outcome V State) : ℕ :=
  (o.mem.filter (fun μ => μ.status.isRight)).length
def Outcome.verdicts (o : Outcome V State) : Multiset V :=
  ((o.mem.filterMap fun μ => μ.status.getLeft?) : List V)

inductive Route | kcol | termFin | split
  deriving DecidableEq

/-- The (m, c) dispatch: exhaustive and exclusive by construction. -/
def routeOf (o : Outcome V State) : Route :=
  if o.c = 0 then .termFin else if o.m = 1 then .kcol else .split

end OutcomeDefs

/-- Block states + rosters.  NO SigSet (R9): σ′ ranges over all of `Multiset VType`;
finite σ′-sums use `verdictImage` below.  `vEquiv` is the R20 STRUCTURAL PIN: verdict
types ARE the (e, f) pairs of degree e·f ≤ n; `vdeg_spec` reads degree through it.
`Wloc`/`Wstate` are the note's degree-bound data, FIXED here before any burden (R27). -/
structure TableShape (n : ℕ) where
  State  : ℕ → Type
  fin    : ∀ e, Fintype (State e)
  deq    : ∀ e, DecidableEq (State e)
  VType  : Type
  deqV   : DecidableEq VType
  finV   : Fintype VType
  vdeg   : VType → ℕ+
  vEquiv : VType ≃ {ef : ℕ+ × ℕ+ // ((ef.1 : ℕ) * (ef.2 : ℕ)) ≤ n}
  vdeg_spec : ∀ v, (vdeg v : ℕ) = ((vEquiv v).1.1 : ℕ) * ((vEquiv v).1.2 : ℕ)
  Out    : ∀ e, State e → Type
  finO   : ∀ e (τ : State e), Fintype (Out e τ)
  odata  : ∀ e (τ : State e), Out e τ → Outcome VType State
  Wloc   : ∀ e (τ : State e), Out e τ → ℕ
  Wstate : ∀ e, State e → ℕ

attribute [instance] TableShape.fin TableShape.deq TableShape.deqV TableShape.finV
  TableShape.finO

open scoped Classical

/-- The finitely many verdict multisets the (e, τ) roster's terminal outcomes emit —
the index Finset of (K-SUB)'s Σ_{σ′} b^{term,fin} (replaces REV 2's SigSet). -/
noncomputable def verdictImage (T : TableShape n) (e : ℕ) (τ : T.State e) :
    Finset (Multiset T.VType) :=
  Finset.image (fun o => (T.odata e τ o).verdicts)
    {o : T.Out e τ | routeOf (T.odata e τ o) = .termFin}.toFinset

/-- (SCS) supply — owner [2a] SP.1 + §B2-DEF D.5/D.8/D.10 via SP.2.  Data first
(R2-3); `∨ True` artifact deleted (R2-1); `flank_zero` added (R2-2); `resFactors`
a Multiset with position-indexed `memberOf` (REV 10, Codex#6-10). -/
structure SCSData (T : TableShape n) where
  W  : ∀ e (τ : T.State e), T.Out e τ → ℕ
  D  : ∀ e (τ : T.State e), T.Out e τ → ℕ
  ℓ  : ∀ e (τ : T.State e), T.Out e τ → ℕ
  g  : ∀ e (τ : T.State e), T.Out e τ → ℕ
  μsel : ∀ e (τ : T.State e), T.Out e τ → ℕ
  W' : ∀ e (τ : T.State e), T.Out e τ → ℕ
  D' : ∀ e (τ : T.State e), T.Out e τ → ℕ
  flankCount : ∀ e (τ : T.State e), T.Out e τ → ℕ
  flankWidth : ∀ e (τ : T.State e), T.Out e τ → ℕ
  resFactors : ∀ e (τ : T.State e), T.Out e τ → Multiset (ℕ × ℕ)
  selIdx : ∀ e (τ : T.State e) (o : T.Out e τ), Fin (T.odata e τ o).mem.length
  memberOf : ∀ e (τ : T.State e) (o : T.Out e τ),
    (Fin (flankCount e τ o) ⊕
      Fin ((resFactors e τ o).erase (g e τ o, μsel e τ o)).card) →
    Fin (T.odata e τ o).mem.length
  -- laws
  ℓpos : ∀ e (τ : T.State e) (o : T.Out e τ), 1 ≤ ℓ e τ o
  window_comp : ∀ e (τ : T.State e) (o : T.Out e τ),
    W e τ o = e * ℓ e τ o + flankWidth e τ o
  flank_zero : ∀ e (τ : T.State e) (o : T.Out e τ),
    flankCount e τ o = 0 → flankWidth e τ o = 0
  sel_mem : ∀ e (τ : T.State e) (o : T.Out e τ),
    (g e τ o, μsel e τ o) ∈ resFactors e τ o
  res_sum : ∀ e (τ : T.State e) (o : T.Out e τ),
    ((resFactors e τ o).map (fun x => x.1 * x.2)).sum = ℓ e τ o
  memberOf_inj : ∀ e (τ : T.State e) (o : T.Out e τ),
    Function.Injective (memberOf e τ o)
  memberOf_ne_sel : ∀ e (τ : T.State e) (o : T.Out e τ) i,
    memberOf e τ o i ≠ selIdx e τ o
  sel_continuing : ∀ e (τ : T.State e) (o : T.Out e τ),
    routeOf (T.odata e τ o) = .kcol →
    ((T.odata e τ o).mem.get (selIdx e τ o)).continuing
  stage_D : ∀ e (τ : T.State e) (o : T.Out e τ), D' e τ o = e * g e τ o * D e τ o
  stage_W : ∀ e (τ : T.State e) (o : T.Out e τ), W' e τ o = μsel e τ o
  cluster_parent : ∀ e (τ : T.State e) (o : T.Out e τ), W e τ o * D e τ o = e
  cluster_child : ∀ e (τ : T.State e) (o : T.Out e τ)
    (i : Fin (T.odata e τ o).mem.length),
    ((T.odata e τ o).mem.get i).continuing → i = selIdx e τ o →
    ((T.odata e τ o).mem.get i).size = W' e τ o * D' e τ o

/-- DEG-CONS (CL-11, [1v]): full-roster per-member degree law. -/
structure DegCons (T : TableShape n) : Prop where
  size_pos : ∀ e (τ : T.State e) (o : T.Out e τ),
    ∀ μ ∈ (T.odata e τ o).mem, 1 ≤ μ.size
  size_sum : ∀ e ∈ Finset.Icc 1 n, ∀ (τ : T.State e) (o : T.Out e τ),
    ((T.odata e τ o).mem.map Member.size).sum ≤ e

/-! ## §2.B The measured side (R7 event carrier).  Owner [1v] CTS-M / [2b] XHD / [5].
Intended instance: the CTS cell space over the level-N residue boxes of the O_δ
theory (the MovesC counting idiom), wave 4. -/

structure MeasuredSide (T : TableShape n) where
  -- pools: prime powers, closed under the base-change legs (R2-7, R2-14)
  Pools : Set ℚ
  pools_prime_pow : ∀ q₀ ∈ Pools, ∃ (p : ℕ) (_ : p.Prime) (δ : ℕ+), q₀ = (p : ℚ) ^ (δ : ℕ)
  pools_closed : ∀ q₀ ∈ Pools, ∀ δ : ℕ+, q₀ ^ (δ : ℕ) ∈ Pools
  pools_infinite : Pools.Infinite
  -- the counting carrier (R7): level-N boxes, events as Finsets
  Box  : ℚ → ℕ → Type
  finB : ∀ q₀ N, Fintype (Box q₀ N)
  boxpos : ∀ q₀ N, Nonempty (Box q₀ N)
  -- cells, representatives, heights
  Cell : ∀ e, T.State e → Type
  finC : ∀ e (τ : T.State e), Fintype (Cell e τ)
  cellOut : ∀ e (τ : T.State e), Cell e τ → T.Out e τ
  Rep : ∀ e, T.State e → Type
  rep_ne : ∀ e ∈ Finset.Icc 1 n, ∀ τ : T.State e, Nonempty (Rep e τ)
  cellLvl : ∀ e (τ : T.State e), Cell e τ → ℕ
  cellInst : ∀ e (τ : T.State e), Cell e τ → ∀ (q₀ : ℚ) (N : ℕ), Finset (Box q₀ N)
  Hgt : Type
  HDom : ∀ e (τ : T.State e), Cell e τ → Set Hgt
  gwt : ∀ e (τ : T.State e) (c : Cell e τ), Hgt → ℚ → ℝ
  cellEvt : ∀ e (τ : T.State e), Rep e τ → Cell e τ → Hgt → ∀ (q₀ : ℚ) (N : ℕ), Finset (Box q₀ N)
  μcell : ∀ e (τ : T.State e), Rep e τ → Cell e τ → ℚ → ℝ
  rowVal : ∀ e (τ : T.State e), T.Out e τ → ℚ → ℝ
  kstep : ℕ → ∀ e, T.State e → T.State e → ℚ → ℝ
  activeState : ℚ → ∀ e, T.State e → Prop
  decA : ∀ q₀ e, DecidablePred (activeState q₀ e)
  -- entrance side
  EntShape : ∀ e, T.State e → Type
  finE : ∀ e (τ : T.State e), Fintype (EntShape e τ)
  hent : ∀ e (τ : T.State e), EntShape e τ → ℕ
  Went : ∀ e (τ : T.State e), EntShape e τ → ℕ
  entEvtH : ∀ e (τ : T.State e), EntShape e τ → Hgt → ∀ (q₀ : ℚ) (N : ℕ), Finset (Box q₀ N)
  ιDom : ∀ e (τ : T.State e), EntShape e τ → Set Hgt
  ιshH : ∀ e (τ : T.State e), EntShape e τ → Hgt → ℚ → ℝ
  ιsh : ∀ e (τ : T.State e), EntShape e τ → ℚ → ℝ
  ιval : ∀ e, T.State e → ℚ → ℝ
  entCount : ∀ e (τ : T.State e), EntShape e τ → ℚ → ℕ
  entLvl : ∀ e (τ : T.State e), EntShape e τ → ℕ
  entInst : ∀ e (τ : T.State e), EntShape e τ → ∀ (q₀ : ℚ) (N : ℕ), Finset (Box q₀ N)
  markedVal : ∀ _e : ℕ, ℚ → ℝ

attribute [instance] MeasuredSide.finB MeasuredSide.finC MeasuredSide.finE
  MeasuredSide.decA

variable {T : TableShape n}

/-- The DEFINED all-active locus (R2-7/R9): only its infinitude is a burden (U-22b). -/
def allActivePools (M : MeasuredSide T) : Set ℚ :=
  {q₀ ∈ M.Pools | ∀ e ∈ Finset.Icc 1 n, ∀ τ : T.State e, M.activeState q₀ e τ}

/-- `cells o` — the outcome's cell fiber (the blueprint's LedgerIV notation). -/
noncomputable def MeasuredSide.cells (M : MeasuredSide T) (e : ℕ) (τ : T.State e)
    (o : T.Out e τ) : Finset (M.Cell e τ) :=
  {c | M.cellOut e τ c = o}.toFinset

/-- CL-5, all nine inputs as contentful Props (R2-4/5/6).  ACTIVITY GUARDS THROUGHOUT
(R13): every per-(e,τ,q₀) mass claim carries `M.activeState q₀ e τ` — the note's
"realized states only" scope; NO zero-row law for inactive sources exists (act_row
DELETED — undisplayed).  The ONLY height summations in the corpus are `xhd_sum` and
`comp_once` — (COMP-Σ)'s "no further height sum" is structural. -/
structure LedgerIV (T : TableShape n) (M : MeasuredSide T) : Prop where
  -- (1) XHD [2b], guarded; two-sided exactness representative-quantified (R2-4):
  xhd_sum : ∀ e (τ : T.State e) (x : M.Rep e τ) (c : M.Cell e τ) (q₀ : ℚ),
    q₀ ∈ M.Pools → M.activeState q₀ e τ →
    HasSum (fun h : M.HDom e τ c => M.gwt e τ c h q₀) (M.μcell e τ x c q₀)
  xhd_no_stray : ∀ e (τ : T.State e) (x : M.Rep e τ) (c : M.Cell e τ) (h : M.Hgt),
    h ∈ M.HDom e τ c → ∀ q₀ ∈ M.Pools, M.activeState q₀ e τ →
    ∃ N₀, ∀ N ≥ N₀, (M.cellEvt e τ x c h q₀ N).Nonempty
  xhd_no_orphan : ∀ e (τ : T.State e) (x : M.Rep e τ) (c : M.Cell e τ) (h : M.Hgt),
    h ∉ M.HDom e τ c → ∀ (q₀ : ℚ) (N : ℕ), M.cellEvt e τ x c h q₀ N = ∅
  -- (2) D4R.0 (event disjointness needs no realization; unguarded is harmless):
  d4r0 : ∀ e (τ : T.State e) (x : M.Rep e τ) (q₀ : ℚ) (N : ℕ)
    (c c' : M.Cell e τ) (h h' : M.Hgt), (c, h) ≠ (c', h') →
    Disjoint (M.cellEvt e τ x c h q₀ N) (M.cellEvt e τ x c' h' q₀ N)
  -- (3) (iv)-PART-1 [1v], GUARDED:
  part1 : ∀ e ∈ Finset.Icc 1 n, ∀ (τ : T.State e) (x : M.Rep e τ) (q₀ : ℚ),
    q₀ ∈ M.Pools → M.activeState q₀ e τ →
    ∑ c : M.Cell e τ, M.μcell e τ x c q₀ = 1
  -- (4) (iv)-REP = RS.0(α) verbatim (weighted grouping), GUARDED:
  rep_indep : ∀ e (τ : T.State e) (o : T.Out e τ) (x : M.Rep e τ) (q₀ : ℚ),
    q₀ ∈ M.Pools → M.activeState q₀ e τ →
    M.rowVal e τ o q₀ = ∑ c ∈ M.cells e τ o, M.μcell e τ x c q₀
  -- (5) (iv)-MEAS counting-native (R7), GUARDED:
  meas_card : ∀ e (τ : T.State e) (x : M.Rep e τ) (c : M.Cell e τ) (h : M.Hgt),
    h ∈ M.HDom e τ c → ∀ q₀ ∈ M.Pools, M.activeState q₀ e τ → ∃ N₀, ∀ N ≥ N₀,
    M.gwt e τ c h q₀ * (Fintype.card (M.Box q₀ N) : ℝ)
      = ((M.cellEvt e τ x c h q₀ N).card : ℝ)
  -- (6) CTS-M(v) HMC (OPEN) + the base tie, target predicate PINNED hK-FREE (G1):
  kstep_one : ∀ e (τ β : T.State e) (q₀ : ℚ), q₀ ∈ M.Pools → M.activeState q₀ e τ →
    M.kstep 1 e τ β q₀ =
    ∑ o ∈ {o : T.Out e τ | routeOf (T.odata e τ o) = .kcol ∧
        ∃ μ ∈ (T.odata e τ o).mem, ∃ h : μ.size = e, h ▸ μ.status = Sum.inr β
      }.toFinset, M.rowVal e τ o q₀
  hmc : ∀ (k : ℕ) e (τ β : T.State e) (q₀ : ℚ), q₀ ∈ M.Pools → M.activeState q₀ e τ →
    M.kstep (k + 1) e τ β q₀ = ∑ γ : T.State e, M.kstep k e τ γ q₀ * M.kstep 1 e γ β q₀
  -- (7) CTS-M(ii) ACT — ONLY the displayed law (S.7(iv)):
  act_target : ∀ e (τ β : T.State e) (q₀ : ℚ), q₀ ∈ M.Pools →
    ¬ M.activeState q₀ e β → M.kstep 1 e τ β q₀ = 0
  -- (8) CTS-M(iii) INIT + ENT-COUNT, guarded; the I^ent tie at ε's OWN level (G4):
  init_agg : ∀ e (τ : T.State e) (q₀ : ℚ), q₀ ∈ M.Pools → M.activeState q₀ e τ →
    M.ιval e τ q₀ = ∑ ε : M.EntShape e τ, M.ιsh e τ ε q₀
  init_count : ∀ e (τ : T.State e) (ε : M.EntShape e τ) (h : M.Hgt),
    h ∈ M.ιDom e τ ε → ∀ q₀ ∈ M.Pools, M.activeState q₀ e τ → ∃ N₀, ∀ N ≥ N₀,
    M.ιshH e τ ε h q₀ * (Fintype.card (M.Box q₀ N) : ℝ)
      = ((M.entEvtH e τ ε h q₀ N).card : ℝ)
  ent_count_card : ∀ e (τ : T.State e) (ε : M.EntShape e τ) (q₀ : ℚ),
    q₀ ∈ M.Pools → M.activeState q₀ e τ →
    (M.entInst e τ ε q₀ (M.entLvl e τ ε)).card = M.entCount e τ ε q₀
  -- (9) COMP-TYPING, heights once: (COMP-h) = init_count's fixed-height objects;
  -- (COMP-hΣ) = THE one height sum; (COMP-Σ)'s factorization is hmc's duty:
  comp_once : ∀ e (τ : T.State e) (ε : M.EntShape e τ) (q₀ : ℚ),
    q₀ ∈ M.Pools → M.activeState q₀ e τ →
    HasSum (fun h : M.ιDom e τ ε => M.ιshH e τ ε h q₀) (M.ιsh e τ ε q₀)

/-! ## §2.C Evaluation, rationality burdens, kernel, pools -/

private theorem eval_ne_zero_of_dvd {p q : Polynomial ℚ} {x : ℚ} (hdvd : p ∣ q)
    (hq : q.eval x ≠ 0) : p.eval x ≠ 0 := by
  intro h0
  obtain ⟨c, rfl⟩ := hdvd
  rw [Polynomial.eval_mul, h0, zero_mul] at hq
  exact hq rfl

/-- The evaluation-regular subring at q₀: {f | f.denom.eval q₀ ≠ 0} (U-19's object;
OKat membership is post-cancellation — RatFunc num/denom are reduced). -/
def OKat (q₀ : ℚ) : Subring Qq where
  carrier := {f : Qq | f.denom.eval q₀ ≠ 0}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := @fun a b ha hb => by
    simp only [Set.mem_setOf_eq] at *
    exact eval_ne_zero_of_dvd (RatFunc.denom_add_dvd a b)
      (by rw [Polynomial.eval_mul]; exact mul_ne_zero ha hb)
  mul_mem' := @fun a b ha hb => by
    simp only [Set.mem_setOf_eq] at *
    exact eval_ne_zero_of_dvd (RatFunc.denom_mul_dvd a b)
      (by rw [Polynomial.eval_mul]; exact mul_ne_zero ha hb)
  neg_mem' := @fun a ha => by
    simp only [Set.mem_setOf_eq] at *
    have hdvd : (-a).denom ∣ (-1 : Qq).denom * a.denom := by
      simpa [neg_one_mul] using RatFunc.denom_mul_dvd (-1 : Qq) a
    have h1 : (-1 : Qq).denom = 1 := by
      rw [show (-1 : Qq) = algebraMap (Polynomial ℚ) Qq (-1) by simp]
      exact RatFunc.denom_algebraMap _
    exact eval_ne_zero_of_dvd hdvd (by rw [h1, one_mul]; exact ha)

theorem mem_OKat_iff {q₀ : ℚ} {f : Qq} : f ∈ OKat q₀ ↔ f.denom.eval q₀ ≠ 0 :=
  Iff.rfl

private theorem eval₂_denom_ne_zero_of_mem {q₀ : ℚ} {f : Qq} (hf : f ∈ OKat q₀) :
    Polynomial.eval₂ (RingHom.id ℚ) q₀ f.denom ≠ 0 := by
  rw [Polynomial.eval₂_id]; exact hf

/-- D4: partial evaluation on the regular subring (RatFunc.eval_add/eval_mul are
hypothesis-carrying; the memberships supply the hypotheses). -/
noncomputable def evalAt (q₀ : ℚ) : OKat q₀ →+* ℚ where
  toFun f := RatFunc.eval (RingHom.id ℚ) q₀ (f : Qq)
  map_one' := by simp
  map_mul' a b := by
    push_cast
    exact RatFunc.eval_mul (RingHom.id ℚ) q₀
      (eval₂_denom_ne_zero_of_mem a.2) (eval₂_denom_ne_zero_of_mem b.2)
  map_zero' := by simp
  map_add' a b := by
    push_cast
    exact RatFunc.eval_add (RingHom.id ℚ) q₀
      (eval₂_denom_ne_zero_of_mem a.2) (eval₂_denom_ne_zero_of_mem b.2)

/-- The (iv)-POLY/XHD-s presentation pattern — R30/R31: TWO independently bounded
count polynomials × a height part in the note's OWN denominator class (q-powers
allowed — the §2.C.1 diagnosis: the note's class in q⁻¹, cleared to X = q, is
denom ∣ X^b · ∏ (1 − X^a)). -/
structure PolyGeom where
  countT : Polynomial ℚ
  degBoundT : ℕ
  degT_le : countT.natDegree ≤ degBoundT
  countS : Polynomial ℚ
  degBoundS : ℕ
  degS_le : countS.natDegree ≤ degBoundS
  geom : Qq
  qpow : ℕ
  geomDenoms : Finset ℕ+
  geom_denom_dvd : geom.denom ∣
    Polynomial.X ^ qpow * ∏ a ∈ geomDenoms, (1 - Polynomial.X ^ (a : ℕ))

noncomputable def PolyGeom.val (P : PolyGeom) : Qq :=
  algebraMap (Polynomial ℚ) Qq (P.countT * P.countS) * P.geom

/-- The rationality burdens: ℚ(q) data in (iv)-POLY form + interpolation to the
measured rows.  Owners: CL-6 (iv)-POLY [1v] (tgP + tg_interp); (J-RAT) [1v]/[2b]
(jP + j_interp); INIT-RAT [1v] (ιP + ι_interp); + the cofinite-activity face
(cellP family, R45/R50 — per-cell, `act_iff` keyed to it). -/
structure RatBurdens (T : TableShape n) (M : MeasuredSide T) where
  tgP : ∀ e (τ : T.State e), T.Out e τ → PolyGeom
  jP  : ∀ e (τ : T.State e), T.Out e τ → PolyGeom
  ιP  : ∀ e (τ : T.State e), M.EntShape e τ → PolyGeom
  tg_ok : ∀ e (τ : T.State e) (o : T.Out e τ) (q₀ : ℚ), q₀ ∈ M.Pools →
    (tgP e τ o).val ∈ OKat q₀
  j_ok  : ∀ e (τ : T.State e) (o : T.Out e τ) (q₀ : ℚ), q₀ ∈ M.Pools →
    (jP e τ o).val ∈ OKat q₀
  ι_ok  : ∀ e (τ : T.State e) (ε : M.EntShape e τ) (q₀ : ℚ), q₀ ∈ M.Pools →
    (ιP e τ ε).val ∈ OKat q₀
  tg_interp : ∀ e (τ : T.State e) (o : T.Out e τ) (q₀ : ℚ) (h : q₀ ∈ M.Pools),
    routeOf (T.odata e τ o) ≠ .split →
    ((evalAt q₀ ⟨(tgP e τ o).val, tg_ok e τ o q₀ h⟩ : ℚ) : ℝ) = M.rowVal e τ o q₀
  j_interp : ∀ e (τ : T.State e) (o : T.Out e τ) (q₀ : ℚ) (h : q₀ ∈ M.Pools),
    routeOf (T.odata e τ o) = .split →
    ((evalAt q₀ ⟨(jP e τ o).val, j_ok e τ o q₀ h⟩ : ℚ) : ℝ) = M.rowVal e τ o q₀
  ι_interp : ∀ e (τ : T.State e) (ε : M.EntShape e τ) (q₀ : ℚ) (h : q₀ ∈ M.Pools),
    ((evalAt q₀ ⟨(ιP e τ ε).val, ι_ok e τ ε q₀ h⟩ : ℚ) : ℝ) = M.ιsh e τ ε q₀
  ι_countS_one : ∀ e (τ : T.State e) (ε : M.EntShape e τ), (ιP e τ ε).countS = 1
  ι_count : ∀ e (τ : T.State e) (ε : M.EntShape e τ) (q₀ : ℚ), q₀ ∈ M.Pools →
    ((ιP e τ ε).countT.eval q₀ : ℚ) = (M.entCount e τ ε q₀ : ℚ)
  tg_degT : ∀ e (τ : T.State e) (o : T.Out e τ), (tgP e τ o).degBoundT = T.Wloc e τ o
  tg_degS : ∀ e (τ : T.State e) (o : T.Out e τ), (tgP e τ o).degBoundS = T.Wstate e τ
  j_degT  : ∀ e (τ : T.State e) (o : T.Out e τ), (jP e τ o).degBoundT = T.Wloc e τ o
  j_degS  : ∀ e (τ : T.State e) (o : T.Out e τ), (jP e τ o).degBoundS = T.Wstate e τ
  ι_degT  : ∀ e (τ : T.State e) (ε : M.EntShape e τ), (ιP e τ ε).degBoundT = M.Went e τ ε
  ι_degS  : ∀ e (τ : T.State e) (ε : M.EntShape e τ), (ιP e τ ε).degBoundS = M.Went e τ ε
  cellP : ∀ e (τ : T.State e), M.Cell e τ → Polynomial ℚ
  cellP_deg : ∀ e (τ : T.State e) (c : M.Cell e τ), (cellP e τ c).natDegree ≤ T.Wstate e τ
  cellP_nonzero : ∀ e ∈ Finset.Icc 1 n, ∀ (τ : T.State e) (c : M.Cell e τ), cellP e τ c ≠ 0
  cellP_count : ∀ e (τ : T.State e) (c : M.Cell e τ) (q₀ : ℚ),
    q₀ ∈ M.Pools → M.activeState q₀ e τ →
    ((cellP e τ c).eval q₀ : ℚ) = ((M.cellInst e τ c q₀ (M.cellLvl e τ c)).card : ℚ)
  act_iff : ∀ q₀ ∈ M.Pools, ∀ e ∈ Finset.Icc 1 n, ∀ τ : T.State e,
    M.activeState q₀ e τ ↔ ∀ c : M.Cell e τ, (cellP e τ c).eval q₀ ≠ 0

variable {M : MeasuredSide T}

noncomputable abbrev RatBurdens.TG (RB : RatBurdens T M) (e : ℕ) (τ : T.State e)
    (o : T.Out e τ) : Qq := (RB.tgP e τ o).val
noncomputable abbrev RatBurdens.J (RB : RatBurdens T M) (e : ℕ) (τ : T.State e)
    (o : T.Out e τ) : Qq := (RB.jP e τ o).val
noncomputable def RatBurdens.ι (RB : RatBurdens T M) (e : ℕ) : T.State e → Qq :=
  fun τ => ∑ ε : M.EntShape e τ, (RB.ιP e τ ε).val

noncomputable def splitOuts (T : TableShape n) (e : ℕ) (τ : T.State e) :
    Finset (T.Out e τ) :=
  {o : T.Out e τ | routeOf (T.odata e τ o) = .split}.toFinset

section KTarget
variable {V : Type*} {St : ℕ → Type*}

private theorem kcol_route_c_ne (o : Outcome V St) (hk : routeOf o = .kcol) :
    o.c ≠ 0 := by
  intro h
  unfold routeOf at hk
  rw [if_pos h] at hk
  exact Route.noConfusion hk

private theorem kcol_route_m_one (o : Outcome V St) (hk : routeOf o = .kcol) :
    o.m = 1 := by
  have hc := kcol_route_c_ne o hk
  unfold routeOf at hk
  rw [if_neg hc] at hk
  by_contra h
  rw [if_neg h] at hk
  exact Route.noConfusion hk

/-- In a kcol outcome (c ≥ 1, m = 1) the single member is continuing. -/
private theorem kcol_head_isRight (o : Outcome V St) (hk : routeOf o = .kcol) :
    (o.mem.head o.hm).status.isRight = true := by
  have hall : ∀ μ ∈ o.mem, μ.status.isRight = true := by
    have hsub : (o.mem.filter (fun μ => μ.status.isRight)).Sublist o.mem :=
      List.filter_sublist
    have hle : o.c ≤ o.m := hsub.length_le
    have hc := kcol_route_c_ne o hk
    have hm := kcol_route_m_one o hk
    have hlen : (o.mem.filter (fun μ => μ.status.isRight)).length = o.mem.length := by
      have h1 : o.c = (o.mem.filter (fun μ => μ.status.isRight)).length := rfl
      have h2 : o.m = o.mem.length := rfl
      omega
    have heq := hsub.eq_of_length hlen
    intro μ hμ
    have hμf : μ ∈ o.mem.filter (fun μ => μ.status.isRight) := by
      rw [heq]; exact hμ
    exact (List.mem_filter.mp hμf).2
  exact hall _ (List.head_mem o.hm)

private theorem isRight_cast {a b : ℕ} (h : a = b) (x : V ⊕ St a) :
    (h ▸ x : V ⊕ St b).isRight = x.isRight := by
  subst h; rfl

end KTarget

/-- The kcol outcome's target state (the single continuing member's state, cast to
block size e via the SCS-supplied `hK`). -/
noncomputable def kTarget (T : TableShape n) (e : ℕ) (τ : T.State e) (o : T.Out e τ)
    (hk : routeOf (T.odata e τ o) = .kcol)
    (hK : ∀ μ ∈ (T.odata e τ o).mem, μ.size = e) : T.State e :=
  Sum.getRight
    ((hK ((T.odata e τ o).mem.head (T.odata e τ o).hm)
        (List.head_mem (T.odata e τ o).hm)) ▸
      ((T.odata e τ o).mem.head (T.odata e τ o).hm).status : T.VType ⊕ T.State e)
    (by rw [isRight_cast]; exact kcol_head_isRight _ hk)

/-- The per-block hypothesis U-6 (`scs`) produces: every kcol member has size e. -/
abbrev KmatHyp (T : TableShape n) (e : ℕ) : Prop :=
  ∀ (τ : T.State e) (o : T.Out e τ), routeOf (T.odata e τ o) = .kcol →
    ∀ μ ∈ (T.odata e τ o).mem, μ.size = e

/-- K_e: the kernel-column matrix — Σ_{kcol o → β} RB.TG e τ o. -/
noncomputable def Kmat (T : TableShape n) {M : MeasuredSide T} (RB : RatBurdens T M)
    (e : ℕ) (hK : KmatHyp T e) : Matrix (T.State e) (T.State e) Qq :=
  fun τ β => ∑ o : T.Out e τ,
    if hk : routeOf (T.odata e τ o) = .kcol then
      (if kTarget T e τ o hk (hK τ o hk) = β then RB.TG e τ o else 0)
    else 0

/-- b_e^{term,fin}(σ′): Σ_{termFin o, verdicts o = σ'} RB.TG e τ o (any σ';
supported on `verdictImage`). -/
noncomputable def bTerm (T : TableShape n) {M : MeasuredSide T} (RB : RatBurdens T M)
    (e : ℕ) (σ' : Multiset T.VType) : T.State e → Qq :=
  fun τ => ∑ o : T.Out e τ,
    if routeOf (T.odata e τ o) = .termFin ∧ (T.odata e τ o).verdicts = σ'
    then RB.TG e τ o else 0

/-- ESCAPE(E0) at an evaluated kernel: nonneg entries + escaping total mass.
`[DecidableEq ι]`: Matrix `1`/`^` need it (Fable#4-F1 batch, R29). -/
structure EscapeE0 {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℚ) :
    Prop where
  nonneg : ∀ i j, 0 ≤ A i j
  escape : Filter.Tendsto (fun k => (A ^ k) *ᵥ (fun _ => (1 : ℚ)))
    Filter.atTop (nhds 0)

/-- Per-pool package (S.4).  `Act` is DETERMINED by CTS-M(ii)'s classification
(R2-8: `act_spec` is an iff — an empty Act needs the note's own no-realized-state
situation, never a modeling choice). -/
structure PoolHyp (T : TableShape n) (M : MeasuredSide T) (RB : RatBurdens T M)
    (e : ℕ) (hK : KmatHyp T e) (q₀ : ℚ) where
  pool_mem : q₀ ∈ M.Pools
  Act : Finset (T.State e)
  act_spec : ∀ τ, τ ∈ Act ↔ M.activeState q₀ e τ
  entry_ok : ∀ τ β, τ ∈ Act → β ∈ Act → Kmat T RB e hK τ β ∈ OKat q₀
  A : Matrix Act Act ℚ
  A_eval : ∀ τ β, A τ β = evalAt q₀ ⟨Kmat T RB e hK τ.1 β.1, entry_ok τ.1 β.1 τ.2 β.2⟩
  inactive_vanish : ∀ τ β (hok : Kmat T RB e hK τ β ∈ OKat q₀), τ ∈ Act → β ∉ Act →
    evalAt q₀ ⟨Kmat T RB e hK τ β, hok⟩ = 0
  e0 : EscapeE0 A

/-- D11's ONE coercion point (R19): the active matrix over ℝ.  Det transported by
`RingHom.map_det` + `Rat.cast_injective` (the E-phase simp lemma `Aℝ_det_iff` lives
with U-24a1's plumbing). -/
noncomputable def Aℝ {RB : RatBurdens T M} {e : ℕ} {hK : KmatHyp T e} {q₀ : ℚ}
    (P : PoolHyp T M RB e hK q₀) : Matrix P.Act P.Act ℝ :=
  P.A.map (algebraMap ℚ ℝ)

/-- CTS-M(ii-c)'s per-pool read-off gate, ℝ-typed via Aℝ (R19): "the evaluated
object's q₀-value (after cancellation — OKat membership is post-cancellation)
equals the active-subsystem solve there".  Junk-block determinants stay
census-side: recorded, never required nonzero. -/
def AVAgree {RB : RatBurdens T M} {e : ℕ} {hK : KmatHyp T e} {q₀ : ℚ}
    (P : PoolHyp T M RB e hK q₀) (v : Qq) (bA : P.Act → ℝ) (τ : P.Act) : Prop :=
  ∃ hok : v ∈ OKat q₀, ((evalAt q₀ ⟨v, hok⟩ : ℚ) : ℝ) = ((1 - Aℝ P)⁻¹ *ᵥ bA) τ

/-- The global determinant hypothesis every solve consumer carries (U-22's target). -/
abbrev DetHyp (T : TableShape n) {M : MeasuredSide T} (RB : RatBurdens T M)
    (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e) : Prop :=
  ∀ e (he : e ∈ Finset.Icc 1 n), (1 - Kmat T RB e (hK e he)).det ≠ 0

/-! ## §2.D (BDY), shapes, RegP (the Defs-part; RS1Bundle/RS4Chain/ReadOffBundle
live in `MovesS/Interfaces.lean` per R25/R29 — the §W4-SYNC pins have NO E-phase
file). -/

/-- The μ̂ fence (no Add, no coercion). -/
structure MuHat where val : Qq

inductive ReadOwner | entrance | block
  deriving DecidableEq

def bdyEdgeOwner (fe r : ℕ) : ReadOwner := if r ≤ fe then .entrance else .block
def bdyNodeOwner (fe r : ℕ) : ReadOwner := if fe ≤ r then .block else .entrance

/-- Length-matched shape record (REV 2); `δOf` per CONVENTION DELTA-ABS (R17). -/
structure Shape (T : TableShape n) where
  k    : ℕ
  eOf  : Fin k → ℕ
  eIcc : ∀ i, eOf i ∈ Finset.Icc 1 n
  τOf  : ∀ i : Fin k, T.State (eOf i)
  δOf  : Fin k → ℕ+
  σ0   : Multiset T.VType

/-- [2a] finiteness; CUT-3's image is the intended instance (W-7, seam). -/
structure ShapeFam (T : TableShape n) where
  Sh : Finset (Shape T)

/-- The δ-factor pool: split-leg δ's over the full roster ∪ the shape legs' δ's. -/
noncomputable def deltaFactors (T : TableShape n) (F : ShapeFam T) : Finset ℕ+ :=
  ((Finset.Icc 1 n).biUnion fun e =>
    (Finset.univ : Finset (T.State e)).biUnion fun τ =>
      (Finset.univ : Finset (T.Out e τ)).biUnion fun o =>
        if routeOf (T.odata e τ o) = .split
        then ((T.odata e τ o).mem.map Member.δ).toFinset else ∅)
  ∪ F.Sh.biUnion fun Ŝ => Finset.image Ŝ.δOf Finset.univ

/-- MULTIPLICATIVE CLOSURE (R17, DELTA-ABS): all products of AT MOST n factors from
`deltaFactors`, incl. the empty product 1 (finite; (K-TRI) bounds nesting depth by n).
The closure lemma `nested_delta_mem` is U-16a3's spec obligation. -/
noncomputable def consumedDeltas (T : TableShape n) (F : ShapeFam T) : Finset ℕ+ :=
  (fun s : Finset ℕ+ => s ∪ Finset.image₂ (· * ·) (deltaFactors T F) s)^[n] {1}

/-- CL-1's per-pool quantifier along one base prime: E0/ACT packages at δ = 1 AND
every consumed base-change leg pool p^δ. -/
def RegP (T : TableShape n) (M : MeasuredSide T) (RB : RatBurdens T M) (p : ℕ)
    (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e) (F : ShapeFam T) : Prop :=
  ∀ e (he : e ∈ Finset.Icc 1 n), ∀ δ ∈ consumedDeltas T F,
    Nonempty (PoolHyp T M RB e (hK e he) ((p : ℚ) ^ (δ : ℕ)))

end LeanUrat.MovesS

--- lean/LeanUrat/MovesS/Interfaces.lean (full) ---

/-
MovesS/Interfaces — §2.D's hypothesis interfaces: RS1Meas, RS1Bundle, RS4Chain,
ReadOffBundle (R25/R29: THE one canonical location; elaborated AFTER the S2/S4
definition units so `evalRe`/`Rsh`/`markedPairing`/`bhatMeas` are in scope).
The §W4-SYNC seam entries (W-pins, TreeIface/FiberIface/ReadLedger, the packages)
are NOT built at E-phase — this file contains NOTHING from that section.
Blueprint: lean/notes/MOVESS_LEAN_BLUEPRINT_2026-07-28.md (REV 13) §2.D.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.BSplitDef
import LeanUrat.MovesS.EvalReDef
import LeanUrat.MovesS.ConsumedDeltas
import LeanUrat.MovesS.BlockSolve
import LeanUrat.MovesS.BlockSolveTot
import LeanUrat.MovesS.RshDef
import LeanUrat.MovesS.MarkedDef

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix

-- The abstract box carrier has no computable equality; `shevt_grouping`'s biUnion
-- takes the classical one (proof-irrelevant, last-resort priority).
attribute [local instance 0] Classical.decEq

variable {n : ℕ}

/-- The RAW measured family (R32): NO hypothesis fields — the carrier the W-2/W-3
pins are stated OVER, so the pins are obligations, not projections.  βmeas is the
h_ent-indexed measured conditional subtree value (owner [3t]). -/
structure RS1Meas (T : TableShape n) (M : MeasuredSide T) where
  βmeas : ∀ e, e ∈ Finset.Icc 1 n → ℕ → ∀ τ : T.State e, Multiset T.VType → ℚ → ℝ
  β_bdd : ∀ e (he : e ∈ Finset.Icc 1 n) (h_ent : ℕ) (τ : T.State e)
    (σ' : Multiset T.VType) (q₀ : ℚ), q₀ ∈ M.Pools →
    βmeas e he h_ent τ σ' q₀ ∈ Set.Icc (0 : ℝ) 1
  βfull : ∀ e, e ∈ Finset.Icc 1 n → ℕ → ∀ τ : T.State e, Multiset T.VType → ℚ → ℝ

/-- RS.1's interface — NO symbolic β input (R8/R2-9): measured objects only.
Instantiating this at wave 4 requires PROVING the pinned W-2/W-3 for the raw
family from their displayed packages (R32) — the fields cannot be self-supplied.
`xrb` is (XRB) CL-9 OPEN, POINTWISE AT POOLS (R40); `recursion_meas` is
ACTIVITY-GUARDED (R16(i)) — junk-block rows at wild pools make NO demand
(det(I − D_{q₀}) = 0 stays a tolerated FINDING); discharge = the pinned W-3. -/
structure RS1Bundle (T : TableShape n) (M : MeasuredSide T) (RB : RatBurdens T M)
    (hdc : DegCons T) (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e)
    extends RS1Meas T M where
  xrb : ∀ e (he : e ∈ Finset.Icc 1 n) (h h' : ℕ) (τ : T.State e)
    (σ' : Multiset T.VType) (q₀ : ℚ), q₀ ∈ M.Pools →
    βmeas e he h τ σ' q₀ = βmeas e he h' τ σ' q₀
  recursion_meas : ∀ e (he : e ∈ Finset.Icc 1 n) (τ : T.State e)
    (σ' : Multiset T.VType) (q₀ : ℚ), q₀ ∈ M.Pools → M.activeState q₀ e τ →
    ∀ h_ent : ℕ, βmeas e he h_ent τ σ' q₀
      = evalRe T M RB hdc e he τ σ' q₀ (fun e' he' => βmeas e' he' h_ent)
  nsNull : Prop
  rexact : nsNull → ∀ e (he : e ∈ Finset.Icc 1 n) (h_ent : ℕ) (τ : T.State e)
    (σ' : Multiset T.VType) (q₀ : ℚ), q₀ ∈ M.Pools →
    βfull e he h_ent τ σ' q₀ = βmeas e he h_ent τ σ' q₀

/-- RS.4's chain — the FULL displayed inherited set as explicit components (R2-19),
σ-index = verdict multisets (R2-11).  `pools_e0` is RE-SCOPED to all-active BASE
pools (R51); `legs_reg` carries CL-1's full per-pool quantifier at EVERY base prime
(R21); `wsh_ok` is denominator regularity ONLY (R53) — CL-17(ii)'s production burden
is the seam pin W17ii (S-8), its inheritance the NAMED TYPED field `wsh17_pin`
(R57): wave 4 instantiates it with W17ii's statement; U-28 takes `h17 : C.wsh17_pin`
as an explicit premise; NO unconditional marking while it is open. -/
structure RS4Chain (T : TableShape n) (M : MeasuredSide T) (RB : RatBurdens T M)
    (hdc : DegCons T) (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e)
    (F : ShapeFam T) where
  L : LedgerIV T M
  B : RS1Bundle T M RB hdc hK
  hns : B.nsNull
  PrimePools : Set ℚ
  prime_sub : PrimePools ⊆ M.Pools
  prime_base : ∀ q₀, q₀ ∈ PrimePools ↔ ∃ p : ℕ, p.Prime ∧ q₀ = (p : ℚ)
  pools_e0 : ∀ e (he : e ∈ Finset.Icc 1 n), ∀ q₀ ∈ PrimePools ∩ allActivePools M,
    Nonempty (PoolHyp T M RB e (hK e he) q₀)
  legs_reg : ∀ p : ℕ, (p : ℚ) ∈ PrimePools → RegP T M RB p hK F
  Sigmas : Finset (Multiset T.VType)
  sig_exact : ∀ σ, σ ∈ Sigmas ↔ (σ.map fun v => ((T.vdeg v : ℕ))).sum = n
  WshP : Shape T → PolyGeom
  wsh_ok : ∀ Ŝ ∈ F.Sh, ∀ q₀ ∈ M.Pools, (WshP Ŝ).val ∈ OKat q₀
  wsh17_pin : Prop
  WshVal : Shape T → ℚ → ℝ
  wsh_interp : ∀ Ŝ (hŜ : Ŝ ∈ F.Sh), ∀ q₀ (h : q₀ ∈ M.Pools),
    ((evalAt q₀ ⟨(WshP Ŝ).val, wsh_ok Ŝ hŜ q₀ h⟩ : ℚ) : ℝ) = WshVal Ŝ q₀
  wshval_bdd : ∀ Ŝ ∈ F.Sh, ∀ q₀ ∈ M.Pools, WshVal Ŝ q₀ ∈ Set.Icc (0 : ℝ) 1
  -- TYPED SHALLOW CARRIERS (R34 — fields, not prose):
  shDom  : Shape T → Set M.Hgt
  shEvtH : Shape T → M.Hgt → ∀ (q₀ : ℚ) (N : ℕ), Finset (M.Box q₀ N)
  visH   : Shape T → ∀ (q₀ : ℚ) (N : ℕ), Finset M.Hgt
  shEvt  : Shape T → ∀ (q₀ : ℚ) (N : ℕ), Finset (M.Box q₀ N)
  shWeightH : Shape T → M.Hgt → ℚ → ℝ
  shevt_grouping : ∀ Ŝ (q₀ : ℚ) (N : ℕ),
    shEvt Ŝ q₀ N = (visH Ŝ q₀ N).biUnion (fun h => shEvtH Ŝ h q₀ N)
  shDom_ne : ∀ Ŝ ∈ F.Sh, (shDom Ŝ).Nonempty
  sh_realized : ∀ Ŝ ∈ F.Sh, ∀ q₀ ∈ allActivePools M,
    ∃ N₀, ∀ N ≥ N₀, (shEvt Ŝ q₀ N).Nonempty
  shweight_card : ∀ Ŝ ∈ F.Sh, ∀ h : M.Hgt, h ∈ shDom Ŝ → ∀ q₀ ∈ M.Pools,
    ∃ N₀, ∀ N ≥ N₀, shWeightH Ŝ h q₀ * (Fintype.card (M.Box q₀ N) : ℝ)
      = ((shEvtH Ŝ h q₀ N).card : ℝ)
  wshval_card : ∀ Ŝ ∈ F.Sh, ∀ q₀ ∈ M.Pools, ∃ N₀, ∀ N ≥ N₀,
    WshVal Ŝ q₀ * (Fintype.card (M.Box q₀ N) : ℝ) = ((shEvt Ŝ q₀ N).card : ℝ)
  Rval : Multiset T.VType → ℚ → ℝ
  r_bdd : ∀ σ (q₀ : ℚ), q₀ ∈ M.Pools → Rval σ q₀ ∈ Set.Icc (0 : ℝ) 1
  decidedTotal : ℚ → ℝ
  x3_total : ∀ p ∈ PrimePools, decidedTotal p = 1
  rs1_equates : ∀ p ∈ PrimePools, (∑ σ ∈ Sigmas, Rval σ p) = decidedTotal p
  rsh_interp : ∀ σ ∈ Sigmas, ∀ p ∈ PrimePools, ∀ hdet : DetHyp T RB hK,
    ∃ hok : Rsh T M RB hdc hK hdet F WshP σ ∈ OKat p,
      ((evalAt p ⟨Rsh T M RB hdc hK hdet F WshP σ, hok⟩ : ℚ) : ℝ) = Rval σ p

/-- R23: the read-off bundle U-24b consumes — coordinate coverage as TYPED DATA.
EVERY e ∈ Icc 1 n, EVERY τA : Act (= every τ — the pools are all-active), EVERY σ',
every h_ent: total coordinate coverage, auditable from the type. -/
structure ReadOffBundle {T : TableShape n} {M : MeasuredSide T}
    {RB : RatBurdens T M} {hdc : DegCons T}
    {hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e}
    (S : Set ℚ) (hS : S ⊆ allActivePools M) (B : RS1Bundle T M RB hdc hK)
    (hdet : DetHyp T RB hK) where
  pkg : ∀ q₀, q₀ ∈ S → ∀ e (he : e ∈ Finset.Icc 1 n), PoolHyp T M RB e (hK e he) q₀
  read : ∀ q₀ (hq : q₀ ∈ S), ∀ e (he : e ∈ Finset.Icc 1 n),
    ∀ τA : (pkg q₀ hq e he).Act, ∀ σ' : Multiset T.VType, ∀ h_ent : ℕ,
    AVAgree (pkg q₀ hq e he) (blockSolve T RB hdc hK hdet e he (↑τA) σ')
      (bhatMeas (pkg q₀ hq e he) (fun e' he' => B.βmeas e' he' h_ent) σ') τA

end LeanUrat.MovesS

--- §W4-SYNC (MOVESS_LEAN_BLUEPRINT_2026-07-28.md lines 1116-1346) ---

## §W4-SYNC — THE SEAM CONTRACT (REV 10; replaces §2.E as a build target)

**NOT LEAN UNITS. NOT BUILT AT E-PHASE.** The typed forms below (carried from
REV 9) are each entry's CURRENT PIN — the contract MovesT/MovesV re-key when
their vocabulary exists. Every Codex tie-demand across rounds 1–9 is recorded at
its entry; a seam entry is DONE only when re-keyed against the real corpora and
re-audited. The former file plan (`MovesS/Interfaces.lean`) is retired for these
declarations; the CORE keeps `RS1Bundle`/`RS4Chain`/`ReadOffBundle` (§2.D — typed,
tree-free) in `Interfaces.lean`, which at E-phase contains NOTHING from this
section.

**THE SEAM LIST (11 entries; tie-demand union + re-keying charge):**
- **S-1 `W1_RS1SH`** (+ **S-1e `W1e_equates`**, **S-1m `W1m_marked`**): current
  forms below. DEMANDS: premise all three on `RS1GivenPackage` (+ `Wsh17Package`
  at W1's CL-17(ii) leg) — Fable#7-GAP-1, FIXED at this contract: the S.2 GIVEN
  list premises ALL THREE RS.1 clauses; adjudication recorded — RS.1 is
  theorem-under-hypotheses in THIS note (not a consumed [5]-style item), so the
  pins carry the package. RE-KEY: package fields → the real MovesT statements.
- **S-2 `W2_xrb`**: DEMANDS (Codex#6-1): package fields must REFER to T/M/ledger/
  owner interfaces — re-key each Prop field to the real [2b]/[3t]/[2r] statement;
  until then the field-registry form stands as the contract shape ONLY.
- **S-3 `W3_recursion`**: DEMANDS (Codex#6-2): assume XRB's CONCLUSION (the
  invariance equality, or the thirteen premises + W2), not the bare implication;
  re-keyed form: `(hxrb : ∀ …, B₀.βmeas … = B₀.βmeas …) → …`.
- **S-4 `W4_x3`**: consumed-item pin ([5]'s package displayed THERE); unchanged.
- **S-5 `W7_cutWD` + TreeIface**: DEMANDS (Codex#6-5): the no-reclassification
  fence must say "a deep split has a FIRST-ENTRANCE ANCESTOR" (placed strictly in
  an entered block subtree), not `¬isEntrance`; re-keyed clause:
  `∀ t ν, TI.isDeepSplit t ν → ∃ ν', TI.isEntrance t ν' ∧ TI.onPath t ν' ν`.
- **S-6 `W8_bdy` + ReadLedger**: DEMANDS (Codex#6-6): tie ReadLedger to the tree
  — a per-entered-path assignment `RL : (t, first-entrance ν) → ReadLedger` with
  charges = the tree's read masses, Wcharge feeding WshVal, βcharge feeding βmeas.
- **S-7 `W10_convergence` + FiberIface**: DEMANDS (Codex#6-9): `Fib` must MAP to
  canonical-tree fibers (TREE-N's complete finite subtrees; disjointness; the
  ONE-F partition) — add `fibOf : Fib → TI.Tree`-style keying; βmeas = 0 must not
  trivialize (fiber nonemptiness where βmeas > 0).
- **S-8 `W17ii` + Wsh17Package**: DEMANDS (Codex#6-7/8): add the `xhd_s` face to
  the package; exclude the empty menu (`F.Sh.Nonempty`, or premise W7's tree_ne
  through S-5); package fields re-keyed to real interfaces. RE-KEYING REPLACES
  (R46): the gate's DEVICE fields `WshP`/`WshVal`/`shDom`/`shEvtH`/`visH`/
  `shEvt`/`shWeightH` (from the device batch n2_wshp_device/n2_sh_events/
  n2_sh_laws — R56) by the real production objects.
- **S-9 packages as registries** (Codex#6-1, global): every abstract Prop field
  in XRBPackage/RS1GivenPackage/Wsh17Package is a NAME AWAITING RE-KEYING — the
  contract's whole point; none is consumed by a core unit.
- **S-10 RS4Chain's tree-tied provenance**: `rs1_equates`/`rsh_interp`/
  `sh_realized`/`wshval_card` keep their field forms in core; their DISCHARGE
  provenance (TREE-EXP/CUT-WD/ONE-F) is seam. RE-KEYING REPLACES (R46): the
  device-satisfied instances of these laws at the gate by production-derived ones.
- **S-11 `n2_treeiface`** (ex-U-29d6): the gate's TreeIface instance + W7 check,
  built when TreeIface is re-keyed.

The REV-9 typed forms (the contract's current shapes):

```lean
-- minimal carriers for statements whose native vocabulary is MovesT's:
structure TreeIface (T : TableShape n) where       -- W-7's carrier — R41-COMPLETED
  Tree : Type
  tree_ne : Nonempty Tree                           -- no empty-carrier vacuity
                                                    --   (Codex#5-3)
  Node : Tree → Type
  finN : ∀ t, Fintype (Node t)
  node_ne : ∀ t, Nonempty (Node t)                  -- a tree has a root
  onPath : ∀ t, Node t → Node t → Prop              -- ν ≼ ν′: ν on ν′'s root-path
  path_refl : ∀ t ν, onPath t ν ν                   -- ROOT-PATH ORDER LAWS (R41):
  path_trans : ∀ t ν₁ ν₂ ν₃, onPath t ν₁ ν₂ → onPath t ν₂ ν₃ → onPath t ν₁ ν₃
  path_antisymm : ∀ t ν ν', onPath t ν ν' → onPath t ν' ν → ν = ν'
  path_total : ∀ t ν₁ ν₂ ν, onPath t ν₁ ν → onPath t ν₂ ν →   -- ancestors of a node
    onPath t ν₁ ν₂ ∨ onPath t ν₂ ν₁                            -- are comparable
  isEntrance : ∀ t, Node t → Prop                   -- the CL-13 entrance predicate
  decE : ∀ t, DecidablePred (isEntrance t)          --   (CTS-M(i)/(iii) supply)
  isDeepSplit : ∀ t, Node t → Prop                  -- b_e^split sites (R41: typed,
                                                    --   for the reclassification
                                                    --   fence — Fable#6-G3)
  blockOf : ∀ t (ν : Node t), isEntrance t ν → Σ e, T.State e   -- the entered block
  entδ : ∀ t (ν : Node t), isEntrance t ν → ℕ+      -- the entrance's δ-leg factor
  leafHalt : ∀ t, Node t → Option T.VType           -- shallow τ-halt leaves (σ₀ feed)
  shapeOf : Tree → Shape T                          -- CUT-3's choice-free assignment
structure FiberIface (T) (M : MeasuredSide T) where -- W-10's carrier
  Fib : ∀ e, T.State e → Multiset T.VType → Type    -- complete finite subtrees w/ leaf
  ctbl : ∀ e τ σ', Countable (Fib e τ σ')           --   multiset of type σ′ (TREE-N)
  fibMass : ∀ e τ σ', Fib e τ σ' → ℕ → ℚ → ℝ        -- per-fiber mass given h_ent
structure ReadLedger where                          -- W-8's carrier (one entered path)
  L fe : ℕ ; hfe : fe ≤ L
  charge : ℕ → ℝ                                    -- per-read mass attribution
  Wcharge βcharge : ℝ                               -- the W_Ŝ-side / β-side totals

-- the pinned deferrals (each cites its owner; NONE is a wave-2 unit):
def W1_RS1SH (Π' : RS1GivenPackage) (Πw : Wsh17Package) (Π : XRBPackage)
    (L : LedgerIV T M) (C : RS4Chain …) (hdet) : Prop :=   -- RS.1-SH, PREMISED on
  Π'.tree_exp_fin → Π'.tree_exp_ns → Π'.tree_n → Π'.one_f → Π'.sib →   -- the S.2
  Π'.tb_cap → Π'.vp → Π'.pci →                                          -- GIVEN
  Π'.rel2_a → Π'.rel2_b → Π'.rel2_c → Π'.rel2_d → Π'.rel2_e →           -- list +
  Πw.c15_volumes → Πw.cts_counts → Πw.sib_count →       -- CL-17(ii)'s leg + XRB
  W2_xrb Π (B₀-of C) →                                  -- (Fable#7-GAP-1, fixed at
  ∀ σ ∈ C.Sigmas, ∀ p ∈ C.PrimePools,                   --  the contract): the S.2
    ∃ hok : Rsh T M RB hdc hK hdet F C.WshP σ ∈ OKat p, --  GIVEN list premises ALL
      ((evalAt p ⟨Rsh T M RB hdc hK hdet F C.WshP σ, hok⟩ : ℚ) : ℝ) = C.Rval σ p
  -- THREE RS.1 clauses; the symbolic half is definitional (U-18 defines Rsh).
  -- ADJUDICATION (recorded): RS.1 is THIS note's theorem-under-hypotheses (S.2),
  -- not a consumed [5]-style item — so its pins CARRY the package (contrast W4).
def RS1Given.holds (Π' : RS1GivenPackage) : Prop :=  -- the premise row, named once
  Π'.tree_exp_fin ∧ Π'.tree_exp_ns ∧ Π'.tree_n ∧ Π'.one_f ∧ Π'.sib ∧
  Π'.tb_cap ∧ Π'.vp ∧ Π'.pci ∧
  Π'.rel2_a ∧ Π'.rel2_b ∧ Π'.rel2_c ∧ Π'.rel2_d ∧ Π'.rel2_e
def W1e_equates (Π' : RS1GivenPackage) (C : RS4Chain …) : Prop :=
  RS1Given.holds Π' →                                -- the S.2 GIVEN list (GAP-1)
  ∀ p ∈ C.PrimePools, (∑ σ ∈ C.Sigmas, C.Rval σ p) = C.decidedTotal p
def W1m_marked (Π' : RS1GivenPackage) (B : RS1Bundle …) (hdet) : Prop :=
  RS1Given.holds Π' →                               -- RS.1-MARKED, premised (GAP-1)
  ∀ e (he : e ∈ Finset.Icc 1 n) q₀ (h : q₀ ∈ M.Pools)   -- + GATED per pool:
    (hok : (markedPairing T M RB hdc hK hdet e he).val ∈ OKat q₀),
      ((evalAt q₀ ⟨_, hok⟩ : ℚ) : ℝ) = M.markedVal e q₀
    -- the OKat membership (no pole surviving cancellation — the (ii-c) PASS) is a
    -- HYPOTHESIS, agreement the conclusion: "the sealed check … must pass BEFORE it
    -- may be read off; a pole SURVIVING cancellation at a wild pool is (ii-c)'s
    -- FAIL" — the pin demands nothing at pools where the gate fails
/-- S.1's displayed hypothesis package as TYPED FIELDS (R37/R38, Codex#5-1): each
    an abstract owner-tagged Prop, instantiated by its owner's REAL statement at
    wave 4. Owners per the S.1 STATUS LINE. -/
structure XRBPackage where
  xhd_w : Prop ; xhd_u : Prop ; xhd_d : Prop ; xhd_s : Prop  -- [2b]; discharge
                                                              --   = [1v]-FULL
  jc_inv : Prop                                               -- [2b] (rev-2, NEW)
  sib : Prop ; jc_multi : Prop                                -- CL-10, [3t], OPEN
  tb_cap : Prop ; vp : Prop                                   -- [3t] §T.2 statuses
  rel2_a : Prop ; rel2_b : Prop ; rel2_d : Prop               -- CL-8, [2r], OPEN
  ns_null : Prop                                              -- [3t] §T.2, CLOSED

def W2_xrb (Π : XRBPackage) (B₀ : RS1Meas T M) : Prop :=      -- the obligation that
  Π.xhd_w → Π.xhd_u → Π.xhd_d → Π.xhd_s → Π.jc_inv →          -- CREATES
  Π.sib → Π.jc_multi → Π.tb_cap → Π.vp →                      -- RS1Bundle.xrb at
  Π.rel2_a → Π.rel2_b → Π.rel2_d → Π.ns_null →                -- wave 4: XRB GIVEN
  ∀ e he h h' τ σ' q₀, q₀ ∈ M.Pools →                          -- the package — the
    B₀.βmeas e he h τ σ' q₀ = B₀.βmeas e he h' τ σ' q₀         -- S.1 theorem-under-
  -- hypotheses SHAPE, typed (R38); pool-quantified (R40). No premise in comments.
/-- S.2's GIVEN-list as TYPED FIELDS (R37/R38, Codex#5-2). The nine-input ledger
    enters as the REAL `LedgerIV` (already typed); the XRB leg as W2's statement. -/
structure RS1GivenPackage where
  tree_exp_fin : Prop ; tree_exp_ns : Prop ; tree_n : Prop ; one_f : Prop  -- [3t]
  sib : Prop                                                   -- CL-10, [3t], OPEN
  tb_cap : Prop ; vp : Prop                                    -- [3t] §T.2
  pci : Prop                                                   -- [3t] (PCI =
                                                               --  REL.2(a)(b)(d) +
                                                               --  (iv)-REP + XRB)
  rel2_a : Prop ; rel2_b : Prop ; rel2_c : Prop ; rel2_d : Prop ; rel2_e : Prop
                                                               -- CL-8, [2r], OPEN

def W3_recursion (Π' : RS1GivenPackage) (Π : XRBPackage) (L : LedgerIV T M)
    (B₀ : RS1Meas T M) : Prop :=                    -- CREATES recursion_meas:
  Π'.tree_exp_fin → Π'.tree_exp_ns → Π'.tree_n → Π'.one_f → Π'.sib →
  Π'.tb_cap → Π'.vp → Π'.pci →
  Π'.rel2_a → Π'.rel2_b → Π'.rel2_c → Π'.rel2_d → Π'.rel2_e →
  W2_xrb Π B₀ →                                     -- "XRB (S.1, proved above)"
  ∀ e he τ σ' q₀ (h : q₀ ∈ M.Pools), M.activeState q₀ e τ →
    ∀ h_ent, B₀.βmeas e he h_ent τ σ' q₀
    = evalRe T M RB hdc e he τ σ' q₀ (fun e' he' => B₀.βmeas e' he' h_ent)
  -- the S.2 GIVEN-list ("the [3t] package (TREE-EXP fin/ns + TREE-N + ONE-F;
  -- (SIB), CL-10; TB-CAP/VP), the S.0 nine-input ledger (CL-5), XRB (S.1), and
  -- [2r]'s REL.2 obligations at every base-changed leg (CL-8)") — EVERY item a
  -- typed premise (L is the real ledger; the rest owner-tagged Props per R37);
  -- activity-guarded, identical quantifier to the field (R16(i)).
def W4_x3 (C : RS4Chain …) : Prop := ∀ p ∈ C.PrimePools, C.decidedTotal p = 1
def W7_cutWD (F : ShapeFam T) (TI : TreeIface T) : Prop :=   -- (CUT-WD), R41-complete
  -- (CUT-1) — with TreeIface's order laws, ancestors are comparable; the clause is
  -- LEAST-FIRST-ENTRANCE (not mere antisymmetry — Codex#5-3):
  (∀ t (ν : TI.Node t), (∃ ν', TI.isEntrance t ν' ∧ TI.onPath t ν' ν) →
    ∃! ν₀, TI.isEntrance t ν₀ ∧ TI.onPath t ν₀ ν ∧
      ∀ ν', TI.isEntrance t ν' → TI.onPath t ν' ν → TI.onPath t ν₀ ν') ∧
  -- (CUT-2) exhaustive/nonoverlapping is the ∃!-dichotomy the above induces
  -- (shallow := no entrance ancestor; else the UNIQUE first entrance) — plus the
  -- TYPED NO-RECLASSIFICATION FENCE (Fable#6-G3, a clause not a comment):
  (∀ t (ν : TI.Node t), TI.isDeepSplit t ν → ¬ TI.isEntrance t ν) ∧
  -- shallow τ-halts feed σ₀(Ŝ):
  (∀ t, (TI.shapeOf t).σ0 =
    (Finset.univ.filter (fun ν : TI.Node t =>
      ¬ ∃ ν', TI.isEntrance t ν' ∧ TI.onPath t ν' ν)).val.filterMap
      (TI.leafHalt t)) ∧
  -- (CUT-3) with the ENTRANCE-BOUNDARY-DATA clause (Fable#6-G2): the shape's
  -- entrance lists ARE the tree's first entrances, blocks and δ-legs matching —
  -- "entrance and halt boundary data retained":
  (∀ t, ∃ enum : Fin (TI.shapeOf t).k ≃
      {ν : TI.Node t // TI.isEntrance t ν ∧
        ∀ ν', TI.isEntrance t ν' → TI.onPath t ν' ν → ν' = ν},
    ∀ i, ∃ hE : TI.isEntrance t (enum i).1,
      TI.blockOf t (enum i).1 hE
        = ⟨(TI.shapeOf t).eOf i, (TI.shapeOf t).τOf i⟩ ∧
      TI.entδ t (enum i).1 hE = (TI.shapeOf t).δOf i) ∧
  (∀ t, TI.shapeOf t ∈ F.Sh)                        -- choice-free, listed
-- The (BDY) mass clause (node block-side as STATE INDEX = blockOf's type,
-- structural; the entering EDGE entrance-side) is the SEPARATE pin W8_bdy
-- (ReadLedger), cited per entered path. Non-vacuity: TreeIface.tree_ne/node_ne.
def W8_bdy (RL : ReadLedger) : Prop :=              -- (BDY) consumption: the entering
  RL.Wcharge = ∑ r ∈ Finset.Icc 0 RL.fe, RL.charge r ∧                -- read is W-side
  RL.βcharge = ∑ r ∈ Finset.Icc (RL.fe + 1) RL.L, RL.charge r         -- β charges none
def W10_convergence (B : RS1Bundle …) (FI : FiberIface T M) : Prop :=
  ∀ e he h_ent τ σ' q₀, q₀ ∈ M.Pools →              -- S.2 CONVERGENCE display:
    (∀ f : FI.Fib e τ σ' , 0 ≤ FI.fibMass e τ σ' f h_ent q₀) ∧    -- POSITIVE series
    HasSum (fun f : FI.Fib e τ σ' => FI.fibMass e τ σ' f h_ent q₀)  -- (Codex-6:
      (B.βmeas e he h_ent τ σ' q₀)                  -- summand nonneg + bounded by 1
                                                    -- via β_bdd = the note's
                                                    -- "positive series bounded by 1,
                                                    -- rearrangements licit (Tonelli)")

/-- CL-17(ii)'s production faces as TYPED owner-tagged Props (R37/R42). -/
structure Wsh17Package where
  c15_volumes : Prop                                -- §C C.1.5 node volumes
  cts_counts : Prop                                 -- CTS/[1] counts ([1v])
  sib_count : Prop                                  -- (SIB)'s COUNT face across
                                                    --   shallow splits ([3t]/CL-10)

def W17ii (Π : Wsh17Package) (C : RS4Chain …) : Prop :=   -- CL-17(ii), OPEN — now
  Π.c15_volumes → Π.cts_counts → Π.sib_count →            -- INSIDE the fence
  ∀ Ŝ ∈ F.Sh, ∀ q₀ (h : q₀ ∈ M.Pools),                    -- (Fable#6-G4) and
    (∃ hok : (C.WshP Ŝ).val ∈ OKat q₀,                    -- PREMISED on the typed
      ((evalAt q₀ ⟨(C.WshP Ŝ).val, hok⟩ : ℚ) : ℝ) = C.WshVal Ŝ q₀) ∧   -- production
    HasSum (fun hh : C.shDom Ŝ => C.shWeightH Ŝ hh q₀) (C.WshVal Ŝ q₀)  -- package
  -- "every W_Ŝ is PRODUCED by the stated rational machinery (C.1.5 node volumes ×
  -- CTS/[1] counts × XHD-s shallow height sums, with (SIB)'s COUNT face across
  -- shallow splits)": the height-sum face over the TYPED carriers shDom/shWeightH
  -- (card-pinned by shweight_card; nonempty by shDom_ne/sh_realized — no ∅/0
  -- model, R42); owners [1v]/[3t]; remains OPEN (CL-17).
```

W-5 (nsNull's discharge) is the field `RS4Chain.hns` — demanded, not deferred-loose.
W-6 (wild-pool read-off) is the Prop `AVAgree` (§2.C), cited per consumption site.
W-9 is RETIRED (subsumed by the R7 event carrier in LedgerIV). W-11 (instantiation of
every §2 structure by the REAL CTS objects) is a wave-4 PROCESS gate (§5), not a Prop.

---


---

==================================================================
# PART 4 — THE BLUEPRINT UNDER AUDIT: MOVESV_LEAN_BLUEPRINT_2026-07-28.md, REV 4 (full text, ~3817 lines)
==================================================================

# MOVESV LEAN BLUEPRINT — REV 4 (wave 4)

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
   tied to the step layer ONLY at length 1) and the realization def `TReal`;
   `XHDd`'s exactness is re-keyed to `TReal`; **HMC is the TYPED LINK** —
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
   within-cell sum meas_card needs is the NAMED burden `MarkDisj`);
   σ_sel's entries tied BY FIELD to the taken continuation's shape-level
   rank (`hrank`, §2.D); `mdom` tied to XHDd's length-1 domain by the
   displayed coherence structure `MDomTie` (§2.G); `hent` upgraded from the
   lossy sum to the INJECTIVE retained-tuple code `hentCode` (SF-1 stands,
   re-verified: no MovesS law reads the field); ENT-AGG split into the
   note-exact aggregation (V3-8a, GIVEN the shallow summability face — NO
   (ENT-U)) and the ιval identification (V3-8b, GIVEN (ENT-U), where the
   note itself lists it); V4-12's iff restated at the note's EXACT
   quantifier (the FIXED XHD weight system — the ∀-E-family quantifier is
   struck; the only-if leg is recorded process-scoped with a machine-checked
   inderivability witness); `tgt_supported` gains the note's active-source
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
  named Prop (body DISPLAYED, §2.G, re-based on `TmplEvents`).
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
weight system, every template (V4-12(a); the ONLY-IF leg is process-scoped
and recorded NOT interface-derivable — its coincidence witness and the
false-HMC failure fence are machine-checked, V4-12(b′)/(c)); and the V.6
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
| `MovesD` (PROVED core, rev 9 seam split) | `Shape n`/`ShapePrefix`/`ShapeRead` (L3 rev 9: retains per-read (h, u*) — fields `h`, `ustar`; per-read `(g, μ)` — fields `g`, `μ`), `Presented`/`PrefIdx`/`Presented.fiber`/`mult`, `Box`, `D4R1_SUM` (D10), `D0b_thmCtop`, `mult_sum` (D11a), `D4R4_all`, `ShapePrefix.A`/`A'`/`W`, `ShapeRead.len`/`.mbar`, the L5/L11 eligibility apparatus BY NAME: `EligibleImage`, `selRank` (L11's s_r), `eligible_card_le` (E6), `E5_gmuLe`, `E8_rankInj`/`E9_encInj`, `ShapePrefix.gamTie` (the u*-determinacy law) | §2.D entrance shapes ε (P̂ concrete WITH heights; entry-read/eligibility WF ties); ι's counting-native def; A(ε) = A(P̂), W_ent(ε) = W(P̂); the marked-event census V5-1 |
| `MovesS` core (E-phase built) | `Qq`, `PolyGeom`, `OKat`/`evalAt`, `MuHat`, `TableShape`, `MeasuredSide`, `RatBurdens`, `LedgerIV`, `DegCons`, `KmatHyp`, `SCSData`, `EscapeE0`, `AVAgree` | §4 SEAM-SUPPLY: layer V7 instantiates; §2 reuses the ℚ(q) plumbing verbatim (NO re-derivation) |
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

/-- (D1)–(D4) for ONE skeleton — CL-13's COMPUTED-PARTITION DELIVERABLE, one
typed record (V.2: "the meet symbol is a construction RECIPE; the clause-(i)
deliverable is the DISPLAYED LIST"). The MEET CELLS are the fibers of the
product of generator maps — "explicit cell predicates as boolean combinations
of (D2)'s generators" is DEFINITIONAL here. REV 2 adds `evalObs`: the letters'
evaluation-map carrier, so (iv)-REP's per-species proviso `ObsCheck` (§2.G)
has a typed referent (C29 repair). -/
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
  -- (D4) the target data per CONTINUING OUTCOME, landing in the TARGET
  -- block's cells "under the SAME global definition" (typed by codomain):
  cont : ∀ m, Outc m → Prop
  decCont : ∀ m, DecidablePred (cont m)
  tgtSk : ∀ m (o : Outc m), cont m o → Skeleton n
  tgt_menu : ∀ m (o : Outc m) (h : cont m o), (letterSp m).isLeft
    -- a continuing OUTCOME forces the species side; a letter may carry
    -- terminal outcomes besides ((D4)'s duty covers continuing outcomes only)
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
column label. -/
inductive TargetIx (n : ℕ) {s : Skeleton n} (B : BlockData n s)
    (B' : ∀ s', BlockData n s') (m : B.Letter) (o : B.Outc m) where
  | cell (h : B.cont m o) (β : (B' (B.tgtSk m o h)).CellIdx)
  | term (v : VLabel n)

/-- THE TABLE FAMILY over one n: per-skeleton BlockData + the globally-typed
(D4) cell maps + the per-entry count tables (CTS-T). THIS is the record the
SEAM instantiates into MovesS.TableShape (unit V7-3a). REV 4 (Codex-2):
`tcell`/`T`/`vlabOf` keyed per (letter, OUTCOME). -/
structure CtsFamily (n : ℕ) where
  bd : ∀ s : Skeleton n, BlockData n s
  tcell : ∀ (s : Skeleton n) (m : (bd s).Letter) (o : (bd s).Outc m)
    (h : (bd s).cont m o),
    (bd s).CellIdx → (bd ((bd s).tgtSk m o h)).CellIdx
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
    ((Phat : MovesD.ShapePrefix).reads.filter IsBranchingRead).length
  hmenu  : ∀ i (hi : i < selRec.length),
    selRec.get ⟨i, hi⟩ < branchMenuCard n Phat i
  hrank  : ∀ i (hi : i < selRec.length),
    selRec.get ⟨i, hi⟩ = shapeRank n Phat i (takenGm n Phat gsel musel i)
    -- [REV 4, Codex-4: the entry IS the rank OF THE TAKEN CONTINUATION —
    --  the tie is a FIELD, no longer prose; takenGm/shapeRank below]
```

**σ_sel's SEMANTIC PIN — REV 4 (Codex-4: rev 3's prose said the entries
"ARE the L11 ranks" but the TYPE carried only bounded naturals, "no selected
continuation and no equality to `MovesD.selRank`").** The tie is now the
FIELD `hrank`: the i-th entry of `selRec` EQUALS the shape-level rank of THE
CONTINUATION THE PREFIX ACTUALLY TAKES at its i-th branching read — the
taken continuation is a FUNCTION of the label's own data (`takenGm`: the
successor read's (g, μ) at interior branching reads; the designated entry
selection (gsel, musel) at the last), and `shapeRank` is the displayed
shape-level enumeration index in the m̄-menu. The VALUE-level identification
of shape ranks with actual ψ-selection ranks is MovesD's own collapse —
"selRank, mod-collapsed into `Fin m̄` — the collapse is the identity on
members, where E7 gives selRank < m̄" (MovesD/Defs.lean 522–523) — cited
with `E8_rankInj`/`E9_encInj` at the instance layer (V3-1(b), V5-1), never
re-derived. ESCALATION HATCH (recorded): if MovesD's member enumeration
order differs from `shapeRank`'s lex order, `shapeRank` re-keys to MovesD's
enumeration THERE, with a fresh audit — never silently. The entrance events
and the instance census (§2.F) take the FULL label ε (selRec included)
as their key, so distinct selections cut distinct events by construction.
The displayed defs (closed, keyed to NAMED MovesD declarations — Codex-18):
```lean
/-- shape-level eligibility of a (g, μ) pair at a read: the L5 budget
(E5_gmuLe is MovesD's law that every realized node's own pair satisfies it). -/
def EligPair (R : MovesD.ShapeRead) (g μ : ℕ) : Prop :=
  1 ≤ g ∧ 1 ≤ μ ∧ g * μ ≤ R.len

/-- a branching read: its same-shape eligible menu has ≥ 2 slots — the
shape-level menu card is m̄ = ⌊len/(g·μ)⌋ (`ShapeRead.mbar`; MovesD's
`eligible_card_le` bounds the value-level census by it). -/
def IsBranchingRead (R : MovesD.ShapeRead) : Prop := 2 ≤ R.mbar

def branchMenuCard (n : ℕ) (P : MovesD.Shape n) (i : ℕ) : ℕ :=
  (((P : MovesD.ShapePrefix).reads.filter IsBranchingRead).getD i default).mbar

/-- the (g, μ) of the continuation TAKEN at the i-th branching read: the
read FOLLOWING it in P̂ (the prefix's own next step), or the designated
entry selection at the final read (REV 4, Codex-4). -/
def takenGm (n : ℕ) (P : MovesD.Shape n) (gsel musel : ℕ) (i : ℕ) : ℕ × ℕ :=
  let reads := (P : MovesD.ShapePrefix).reads
  let bIdx  := (List.range reads.length).filter
                 (fun j => IsBranchingRead (reads.getD j default))
  match reads.get? (bIdx.getD i 0 + 1) with
  | some R => (R.g, R.μ)
  | none   => (gsel, musel)     -- the entry read: b's designated selection

/-- the shape-level rank of a (g, μ) pair in the branching read's eligible
menu — the `Fin m̄` index MovesD's selRank collapses onto (Defs 522-523). -/
def shapeRank (n : ℕ) (P : MovesD.Shape n) (i : ℕ) (gm : ℕ × ℕ) : ℕ :=
  ((eligMenu (branchingRead n P i)).indexOf gm)
  -- eligMenu R := the lex-sorted list of {(g,μ) // EligPair R g μ};
  -- branchingRead n P i := the i-th filtered read — closed defs, this file
```

```lean
/-- HEIGHT PROJECTION (rev 4): h_ent(ε) := the tuple of ε's RETAINED height
data — the (h_r, u*_r) pair vector over P̂'s reads. A FUNCTION of ε,
displayed; "one concrete ε FIXES its entrance heights". -/
def EntShapeV.hent {n : ℕ} (ε : EntShapeV n) : List (ℕ × ℚ) :=
  (ε.Phat : MovesD.ShapePrefix).reads.map (fun R => (R.h, R.ustar))

/-- the INJECTIVE ℕ-code of the retained height data (REV 4, Codex-6: the
seam's `MeasuredSide.hent : … → ℕ` slot is supplied by THIS code, never by
a lossy sum — distinct retained tuples get distinct codes; u*_r rides via
its γ-code, determined by `gamTie`): fold Nat.pair over (h_r, zig(γ_r)).
(`zig` : ℤ ≃ ℕ — displayed with the u*-slot encoding below; the E-file
declares it before this def.) -/
def EntShapeV.hentCode {n : ℕ} (ε : EntShapeV n) : ℕ :=
  ((ε.Phat : MovesD.ShapePrefix).reads.map
    (fun R => Nat.pair R.h (zig R.gam))).foldr Nat.pair 0

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

def EntShapeV.template {n : ℕ} (ε : EntShapeV n) : EntTemplate n :=
  { word := MovesSp.collapseRuns (spWord n (ε.Phat : MovesD.ShapePrefix)),
    gsel := ε.gsel, musel := ε.musel, selRec := ε.selRec,
    hne := …, hMem := …, hWalk := …, hEntry := …, hlen := …, hmenu := … }
    -- the six WF anonymous fields are PROOF TERMS (not data), each the named
    -- V3-3(b) bridge law (spWord lands in the catalogue, SuccStep-linked;
    -- collapse strikes the runs; selection/menu ties preserved) — E-phase
    -- fills them from that unit; no data freedom hides here.

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
/-- write the height/depth point into the template's slots: re-expand the
collapsed self-loop letters by the depth slots, then fold `readOfLetter`
(V3-3(d)'s reconstruction: species letter + (h-slot, u*-code slot) + the
prefix-so-far ↦ the unique WF ShapeRead with those data — ustar via the
zig/gamTie inversion above) along the expanded word; selection data carried
verbatim; the EntShapeV WF fields are V3-3(d)'s proof terms. -/
def writeHeights {n : ℕ} (ε̊ : EntTemplate n) (h : Hpt ε̊.entDim) :
    EntShapeV n :=
  { Phat := shapeOfSlots n (expandRuns ε̊.word (depthSlots ε̊ h)) (pairSlots ε̊ h),
    gsel := ε̊.gsel, musel := ε̊.musel, selRec := ε̊.selRec,
    hne := …, hentry := …, helig := …, hlen := …, hmenu := … }
-- shapeOfSlots := List.foldl (readOfLetter n) emptyPrefix; expandRuns /
-- depthSlots / pairSlots are the three Fin-arithmetic slot projections of
-- 2.A's take/drop idiom (closed defs in this file). The anonymous fields are
-- V3-3(d) proof terms.
```

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
structure CtsMeasured (n : ℕ) (C : CtsFamily n) (S : StepSys n) where
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
    stepKey p ≠ stepKey p' → Disjoint (evtOfStep p N) (evtOfStep p' N)
    -- AStep S αc x := (Σ β (mv : S.Move αc β) (h : Hpt (S.dim mv)),
    --   S.Assign mv x h) ⊕ (Σ v (mv : S.MoveT αc v) (h : Hpt (S.dimT mv)),
    --   S.AssignT mv x h) — a closed def of this file; evtOfStep unpacks to
    -- evtOf/evtOfT; stepKey p := the (MoveData/TermData datum, cellOfA-image,
    -- Σ-embedded height) triple — a closed def (the mark coordinate — WHICH
    -- assignment within the digit cell, and for continuing steps WHICH
    -- target β the mark selects — is NOT part of the key). [tie]
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
    -- a component (V2-5, V4-5, V5-8, V7-5(a)); [1v] states its lists
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
    ∀ N ≥ entLvl ε.template,
    ((entEvt ε β₀ q₀ N).card : ℚ) * q₀ ^ (ε.A : ℕ)
      = ((entInst ε β₀ q₀ (entLvl ε.template)).card : ℚ) * q₀ ^ (n * N)
    -- [tie] gate B (q₀ = 2, n = 3, A = 3, N = 3): 128·2³ = 2·2⁹ ✓ — the
    -- event card is I^ent·q^{nN−A} = 128, and the census is I^ent(2) = 2:
    -- F-1's 128-not-8192 acceptance number
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

/-- THE MARK-DISJOINTNESS BURDEN (NEW at REV 4, Codex-3's other half):
within ONE digit cell at one height, distinct marks realize disjoint
f-events. NOT a CtsMeasured law (the note explicitly allows equal
f-projections across marks — offspring mass may exceed 1); a NAMED, typed
hypothesis that V7-6a1's meas_card derivation displays (at the n = 3 gate
rosters it follows from emult ≤ 1, by decide — V4-8's census; beyond them
it is open, exactly where PART-2's surplus lives). -/
def MarkDisj {n C S} (V : CtsMeasured n C S) : Prop :=
  ∀ (d : MoveData n C) {q₀} (x : S.Hist q₀ _) (c) (h)
    (a a' : S.Assign (V.moveOf d) x h), V.cellOfA d x h a = c →
    V.cellOfA d x h a' = c → a ≠ a' →
    ∀ N, Disjoint (V.evtOf (V.moveOf d) x h a N) (V.evtOf (V.moveOf d) x h a' N)

/-- THE ε-INSTANCE COUNT — a DEF (card of the census at the defining level):
I^ent_{ε,β₀}(q₀), the note's marked-prefix count. NOT an event card at a
box level (F-2's repair): its q₀-dependence is the polynomial ENT-COUNT
burden (deg ≤ W_ent), never a q^{nN−A} scaling. -/
noncomputable def CtsMeasured.entCensus (V : CtsMeasured n C S)
    (ε : EntShapeV n) (β₀ : S.Cell) (q₀ : ℚ) : ℕ :=
  (V.entInst ε β₀ q₀ (V.entLvl ε.template)).card

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
  V.entCensus (writeHeights i.1.1 ((V.entDom i.1.1).comps.get i.1.2).base) β₀ q₀
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
  -- NO composite-template law relates tevt/tinst at (.cons m γ) to the step
  -- layer. In particular NO census recursion exists: marks may fail to be
  -- f-realized at composites (empty deep fibers — (HMC-AUG)'s cone
  -- coupling), which is exactly what keeps (v) OPEN below. The (COMP-h)
  -- mass identity at REALIZED points is the THEOREM V5-2, GIVEN (U-A) +
  -- (XHD-u), never a carrier law.

/-- PROCESS REALIZATION: the marked event of (γ, h) from x is realized —
eventual nonemptiness at x's pool (the entrance layer's `Realizable`
pattern, §2.G below, now uniform across both layers). -/
def TReal {n S} (TE : TmplEvents n S) {α} (γ : Template n S α)
    {q₀} (x : S.Hist q₀ α) (h : Hpt γ.D) : Prop :=
  ∃ N₀, ∀ N ≥ N₀, (TE.tevt γ x h N).Nonempty

/-- (XHD-d) DOMAINS, typed — RE-KEYED at REV 4 (N-1 adjudication): per
template an EXPLICITLY LISTED pairwise-disjoint semilinear PARTITION of the
EXACT realizable height domain, exact two-sidedly. The note's display
(MOVES 7948–7949): "(no orphan) T_γ(x, h) > 0 for some representative x ⟹
h ∈ H(γ); (no stray) h ∈ H(γ) ⟹ T_γ(x, h) > 0 for EVERY representative x
of α" — with T_γ(x,h) > 0 READ PROCESS-SIDE per the adjudication ("chains
from x REALIZING (γ, h)" = realized marked events, MOVES 7921–7923 +
8225–8232), i.e. `TReal`. The rev-3 keying to the recursive `chainCount`
is STRUCK (it proved HMC). Owner [2b]. -/
structure XHDd (n : ℕ) (S : StepSys n) (TE : TmplEvents n S) where
  dom : ∀ {α} (γ : Template n S α), SemilinPart γ.D
  no_orphan : ∀ {α} (γ : Template n S α) {q₀} (x : S.Hist q₀ α) (h : Hpt γ.D),
    q₀ ∈ S.Pools → S.zc x → TReal TE γ x h → (dom γ).Mem h
  no_stray : ∀ {α} (γ : Template n S α) (h : Hpt γ.D),
    (dom γ).Mem h → ∀ {q₀}, q₀ ∈ S.Pools → ∀ x : S.Hist q₀ α, S.zc x →
    TReal TE γ x h
  -- COUNT SUPPLY (derived, not a field): membership ⟹ positive TABLE-side
  -- count at every zc representative, via Mem → (no_stray) TReal →
  -- (real_marks) 0 < census → (marks_chains: census ≤ chainCount)
  -- 0 < chainCount. Stated as unit V1-3's lemma `mem_chainCount_pos`;
  -- V2-5/V4-5/V5-8 consume it. The CONVERSE (chainCount > 0 → TReal) is
  -- NOT derivable at composite templates — combinatorial chains need not
  -- be f-realized ((HMC-AUG)'s coupling) — and that one-way gap is
  -- precisely what keeps HMC below out of theorem-hood.

/-- THE mdom COHERENCE TIE (NEW at REV 4, Codex-5: rev 3 had "no law
identifying `mdom d` with `XHDd.dom (.last (moveOf d))`"). [1v] lists its
one-step domains XHD-free (VAL(a)); when the [2b] package is in scope, the
lists coincide — a displayed hypothesis of every base-point transport
(V2-5(b), V4-5, V5-8, V7-5(a)). Base realizability follows: base ∈ mdom d
= dom(.last …) → no_stray → TReal → count > 0 (V1-3's lemma) — u_T's
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
        (q₀ : ℝ) ^ (-(((writeHeights i.1.1 h.1).A : ℕ) : ℤ)))
      ((evalAt q₀ ⟨Gent β₀ i, Gent_ok β₀ i q₀ hq⟩ : ℚ) : ℝ)
    -- WEIGHT-ONLY: the count I^ent multiplies OUTSIDE, through ENT-COUNT +
    -- (ENT-U) at V3-9c/V7-4b — the burdens stay burdens
  -- THE SHALLOW MASS-SUMMABILITY FACE (NEW at REV 4, Codex-7: the note's
  -- ENT-AGG ledger line reads "CONVERGENCE of the full aggregate … is GIVEN
  -- XHD-s on the shallow layer" — convergence of the MASS aggregate is the
  -- shallow face's own content, NOT an (ENT-U) consequence. Summability
  -- ONLY: no ℚ(q)-value is asserted, so INIT-RAT is decided by nothing):
  mass_summable : ∀ (β₀ : S.Cell) (q₀ : ℚ), q₀ ∈ V.Pools →
    Summable (fun p : Σ i : V.EntIx β₀,
        {h // ((V.entDom i.1.1).comps.get i.1.2).Mem h} =>
      (V.entCensus (writeHeights p.1.1.1 p.2.1) β₀ q₀ : ℝ)
        * (q₀ : ℝ) ^ (-(((writeHeights p.1.1.1 p.2.1).A : ℕ) : ℤ)))
    -- (the summand IS ιshH's body, inlined for declaration order; the def
    --  below and this field are matched by rfl at V3-8a)

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
  no_orphanE : ∀ (ε̊ : EntTemplate n) (h : Hpt ε̊.entDim) (β₀ : S.Cell),
    Realizable V (writeHeights ε̊ h) β₀ → (V.entDom ε̊).Mem h
  no_strayE : ∀ (ε̊ : EntTemplate n) (h : Hpt ε̊.entDim) (β₀ : S.Cell),
    V.entLands ε̊ β₀ → (V.entDom ε̊).Mem h → Realizable V (writeHeights ε̊ h) β₀
  lands_of_realizable : ∀ (ε̊ : EntTemplate n) (h : Hpt ε̊.entDim) (β₀ : S.Cell),
    Realizable V (writeHeights ε̊ h) β₀ → V.entLands ε̊ β₀
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
  (V.entCensus (writeHeights ε̊ h) β₀ q₀ : ℝ)
    * (q₀ : ℝ) ^ (-(((writeHeights ε̊ h).A : ℕ) : ℤ))

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
against `TReal` and the composite `tevt`/`tinst` free, the four-line proof
is blocked in BOTH directions at composite tails — no census recursion, no
count→realization link. (The ⊆-flavored fragment at length-2 composites
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
    -- S.Assign m (histOf α' x') h. `castMove`/`castHpt`/`castAssign` are the
    -- three ▸-transport helpers along hα/β'.2/dim_eq — closed defs of this
    -- file (Eq.mpr wrappers, displayed at E-phase in one line each); the
    -- Σ-domain and the target fiber are otherwise verbatim as shown.
  -- terminal twins [+T]: moveProjT / dimT_eq / assignOfT / massT_eq /
  -- assign_coverT, by the §2.B substitution table (targets: the SAME
  -- absorbing label v on both sides — VLabel does not refine).

def HMCAug {n : ℕ} (S : StepSys n) : Prop :=
  ∃ (R : Refinement n S) (TE' : TmplEvents n R.S') (D' : XHDd n R.S' TE'),
    HMC TE' D'
  -- an unrelated witness stays impossible: D' is exact against TE''s
  -- process realization, TE' is tied to R.S''s step layer at length 1
  -- (tevt_last_iff over R.S''s cntraw), and R.S''s assignments partition
  -- S's through assign_cover — the refinement is keyed to S by
  -- construction. [REV 4: quantifies its own TmplEvents over the refined
  -- system — the reason TmplEvents is a standalone carrier, not a
  -- CtsMeasured field]

/-- (ENT-U)'s affine-A face (M4a), DISPLAYED (C29): A(ε̊[h]) is affine in h
across instantiations of one template (dependent codomain — the rev-2 `_`
made explicit). -/
structure AffEnt (n : ℕ) where
  AE : ∀ ε̊ : EntTemplate n, AffineE ε̊.entDim
  A_eq : ∀ (ε̊ : EntTemplate n) (h : Hpt ε̊.entDim),
    (writeHeights ε̊ h).A = (AE ε̊).eval h

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
  route : ∀ (s : Skeleton n) (m : (C.bd s).Letter), C.Outc s m → RouteTag
    -- the (K-SUB) classification datum; V7-3a carries the compatibility law
    -- `route_eq` tying it to MovesS's routeOf ∘ odata at the seam instance
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
supplies `MovesS.RatBurdens.jP`. GATE (F-6's acceptance): at the root's
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
C20 repair; `censusP` deleted).

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
noncomputable instance : Field F4 :=
  { add := f4add, mul := f4mul, zero := (0 : Fin 4), one := (1 : Fin 4),
    neg := id, sub := f4add, inv := fun a => [0,1,3,2].get a,
    -- every remaining structure field/law is discharged `by decide` over
    -- the Fin-4 tables (add_assoc, mul_comm, left_distrib, mul_inv_cancel
    -- at a ≠ 0, …) — the full field-instance skeleton is mechanical and
    -- one `decide` per law [REV 4, Codex-14: no `…laws` stand-in]
    .. }

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
-- Field instances for F8/F9: the F4 pattern verbatim (neg = id at char 2;
-- F9's neg a := f9mul 2 a i.e. the mod-3 componentwise negation table);
-- every law `by decide` over the pasted tables, in-kernel.
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
`takenGm`/`shapeRank` §2.D · `hentCode` §2.D · `BlockData.CellIdx` §2.C
(moved into Defs — order fixed) · the F8/F9 add/mul tables §2.I (pasted
literals) · `stepKey` §2.F (the digit-cell key of evt_disj_cell, closed
def). Residual E-phase freedom: the `castMove/castHpt/castAssign`
transport helpers (§2.G), the `eligMenu`/`branchingRead` one-liners
(§2.D), and zig's orientation token — mechanical, zero design content,
each recorded in §5's inventory.

## §3 The unit DAG — 95 units (32 easy / 59 medium / 4 hard)

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

**V1-3 `xhdd_exact_supp` · `V1_xhdd.lean` · easy — RE-KEYED at REV 4 (N-1:
the rev-3 count-keyed iff was the HMC-proving over-commitment).**
ROSTER (2): (a) `xhdd_exact : (D.dom γ).Mem h ↔ ∀ q₀ ∈ Pools, ∀ x : Hist q₀ α,
zc x → TReal TE γ x h` at pool-inhabited zc histories (both directions from
no_orphan/no_stray + zc_ne) — the exactness iff over PROCESS realization;
(b) `mem_chainCount_pos : (D.dom γ).Mem h → ∀ q₀ ∈ Pools, ∀ x, zc x →
0 < chainCount S γ x h` — THE ONE-WAY COUNT SUPPLY (no_stray → real_marks →
marks_chains), the lemma V2-5/V4-5/V5-8 consume; its converse is NOT stated
(underivable at composites — exactly HMC's openness, §2.G).
moves_ref: "(no orphan) T_γ(x, h) > 0 for some representative x ⟹ h ∈ H(γ);
(no stray) h ∈ H(γ) ⟹ T_γ(x, h) > 0 for EVERY representative" (V.0, the
process reading per the N-1 adjudication). deps: Defs 2.G.
sketch: unfold; chain the three TE ties. hyp_fields: XHDd + TmplEvents ties
(owner [2b] / carrier).

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

**V1-6 `UA_fixed_history` · `V1_UA.lean` · medium.**
(U-A) AS THE NOTE PROVES IT — this corpus's ONE §C-derivable clause:
`theorem UA (P : C15Pack n S) {α β} (m : S.Move α β) (x : S.Hist α)
(hzc : S.zc x) (h : Hpt (S.dim m)) (a a' : S.Assign m x h) (q₀ ∈ S.Pools) :
S.massOf m x h a q₀ = S.massOf m x h a' q₀`.
moves_ref: "Fix ONE realizable prefix satisfying (ZC) … BOTH factors are
functions of the read's NOMINAL DIGIT INVENTORY … Hence all fresh assignments
realizing (m, o, β) at h FROM THAT PREFIX carry one common conditional
mass. ∎" (V.0 (U-A)). deps: Defs (C15Pack).
sketch: two `mass_factors` rewrites; both sides = `F (invOf m x h) q₀`.
hyp_fields: `C15Pack` (owner §C/HC-2 — the typed C.1.5(1)+TYP(b) supply; the
PROOF is unconditional given the pack, exactly the note's GIVEN).

**V1-7 `ua_split_fence` · `V1_fence.lean` · medium.**
THE HONEST-SPLIT WITNESS, display Prop-corrected (A-7): `theorem ua_fence :
∃ S : StepSys n, ∃ _P : C15Pack n S, ¬ (∀ {α β} (m : S.Move α β) x x' h a a'
(q₀ …), S.massOf m x h a q₀ = S.massOf m x' h a' q₀)` — nested existentials,
no Type-as-conjunct. moves_ref: "NOT §C-derivable, HYPOTHESIZED in (XHD-u)
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
productivity `out_ne`, now pool-guarded), a `C15Pack` (incl. the T-twin
fields), an `XHDw` (E = h + 1; zc guards trivial), an `XHDu` (incl.
T-twins). moves_ref: the V.0 package displays (each quantifier realized at
a true instance). deps: Defs. sketch: decide/norm_num.
hyp_fields: none — a PROVED instance.

**V1-8b `xhdds_realized` · `V1_witnessB.lean` · medium — SPLIT (Codex-19);
REV 4: the PROCESS SIDE realized.**
Over V1-8a's instance: a `TmplEvents` toy (Box q₀ N := Fin 1; tevt/tinst :=
the full box on the product-of-listed-domains points, ∅ off them — all four
ties by decide: length-1 iff, real_marks, marks_chains), an `XHDd` over it
(exactness against the toy TReal holds by decide), and an `XHDs` (one
geometric sum — the V0-4 pattern at dim 1); `MDomTie` holds by rfl on the
toy's lists. moves_ref: (XHD-d)/(XHD-s) displays + the §2.G process carrier.
deps: V1-8a, V0-4's pattern. sketch: one geometric series + decide.
hyp_fields: none — a PROVED instance. [At THIS toy HMC happens to be true —
the false-HMC instance is V4-11's, with a COUPLED composite tevt; together
they bracket the kernel: satisfiable both ways, provable neither.]

**V1-8c `measured_faces_realized` · `V1_witnessC.lean` · medium — SPLIT
(Codex-19).** Over a one-cell/one-template `CtsMeasured` toy on the same
system (incl. the REV-3 census/tie fields entInst/ent_card/box_card/
evt_card/stInst_card AND the REV-4 fields — evt_disj_cell,
XHDsEnt.mass_summable — realized by explicit finite data): the faces
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

**V2-2 `cellidx_delete` · `V2_cells.lean` · easy.**
ROSTER (3 — C28): (a) `def BlockData.CellIdx (B) := {a : ∀ g, (B.gen g).idx
// B.sizeP a ≠ 0}`; (b) `instance : Fintype B.CellIdx`; (c) `deleted_empty`:
deleted cells have empty fibers at every prime power (`size_count` + eval 0
⟹ card 0). moves_ref: "cells with IDENTICALLY-zero size polynomial are
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
with fields: (a) `tbl_count : ∀ (d : MoveData n C) (β) {q₀} (x : S.Hist q₀ _)
(hzc : S.zc x) (hq : q₀ ∈ V.Pools) (j : Fin (V.mdom d).comps.length),
((C.T d.s d.m d.o d.α β).eval q₀ : ℚ) = S.cntraw (V.moveOf d) x
(((V.mdom d).comps.get j).base)` — the polynomial valued at the count AT THE
LISTED BASE POINTS of the one-step domain, ∀ representatives AT THE POOL
(REV 4, N-2: the count is a count of q₀-histories' fibers — the law is
now satisfiable at non-constant tables. THE ACCEPTANCE NUMBERS, displayed:
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
(+ `tbl_countT`, the [+T] twin over mdomT/cntrawT);
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
`pathProdPoly C γ := ∏ᵢ C.T (step-i data of γ) (its TargetIx)` (a displayed
def of this file over `dataOf`), CONNECTED to ValA and evaluated at q₀.
REV-4 ROUTE (N-1 ripple): realized-ness now comes from V1-3(b)'s
`mem_chainCount_pos` (Mem → TReal → marks → 0 < chainCount — the ONE-WAY
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
`decide` over the DefsGate lists; PLUS the shape lemma producing
`MovesS.DegCons gateTS` for V7-3b. moves_ref: "DEG-CONS … m ≥ 2 children,
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
what the LABEL layer owns); (b) the SEMANTIC LEG, correctly keyed: σ_sel's
entries ARE the L11 ranks (`MovesD.selRank` — the §2.D semantic pin), and
DISTINCT designated ψ-selections at a branching read have DISTINCT ranks by
MovesD's PROVED `E8_rankInj` — stated as the instance-layer lemma "two
entrance CUTS (2.E) induced by different selections at read i produce labels
with different selRec i-entries", citing E8_rankInj, never re-deriving it.
The note's "siblings … differ in s_r" is the CONJUNCTION (a) + (b).
moves_ref: "siblings at a shallow split differ in s_r, hence carry DISTINCT
ε — ι never aggregates a pre-split f-event or a joint-sibling locus"
(V.3(iii)) + "σ_sel = (s_r … — L11's encoding data, lifted into the label)".
deps: Defs 2.D/2.E, MovesD.E8_rankInj. sketch: structure injectivity +
rank-injectivity transport. hyp_fields: none.

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

**V3-3b `spword_collapse` · `V3_spwordB.lean` · medium.**
The COLLAPSE law: `EntShapeV.template` lands in `EntTemplate` (the collapsed
word is a `CollapsedWalk`; entry/menu WF fields transported from ε's §2.D
ties — incl. the REV-4 `hrank` field, transported through `takenGm`'s
letter-level image). moves_ref: as V3-3a + [2a]'s collapse convention.
deps: V3-3a. sketch: CollapsedWalk transport. hyp_fields: as V3-3a.

**V3-3c `entshape_bridge` · `V3_spwordC.lean` · medium.**
The ENTRANCE-SHAPE BRIDGE: from (ε̊, h) construct the
`MovesSp.EntranceShape n gsel musel` behind it (word + hMem + hChain +
hEntry from ε̊'s fields; heights h into the slot functions) — the §1
consumption tie A-3 demanded. moves_ref: as V3-3a. deps: V3-3a/b.
sketch: field transport. hyp_fields: as V3-3a.

**V3-3d `spword_faithful` · `V3_spwordD.lean` · HARD — the Codex-6
reconstruction bridge (the corpus's real E-phase risk).**
`readOfLetter` (species letter + (h-slot, u*-code slot) + the WF
prefix-so-far ↦ the unique WF `ShapeRead` with those data — e/g/μ/s0/wSide/
Dwidth/w from the letter's stage fields and the WF chains (width chain,
wchain), ustar via zig + `gamTie`'s inversion, a/gam via
`anchorTie`/`gamTie`) and `spWord_faithful`: two shallow WF prefixes with
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
THE NOTE-EXACT AGGREGATION: `theorem ent_agg_conv (XsEnt : XHDsEnt n S V)
(DE : XHDdEnt …) (β₀) (q₀ ∈ Pools) : ∃ v : ℝ, HasSum (fun p : Σ i :
V.EntIx β₀, {h // comp-Mem i h} => ιshH V p.1.1.1 p.2.1 β₀ q₀) v` —
convergence from the REV-4 shallow MASS-SUMMABILITY face
`XsEnt.mass_summable` (the ledger line's own premise, typed; summability
only, so INIT-RAT is decided by nothing); entrance heights summed HERE and
nowhere else; each concrete realizable ε hit EXACTLY ONCE (V3-5's bijection
composed with the disjoint component listing + lands_of_realizable — no
realizable entrance omitted). NO (ENT-U). moves_ref: "ι_{e,β₀} := Σ_{ε̊}
Σ_{h ∈ H(ε̊)} ι_{e,ε̊[h],β₀} … CONVERGENCE of the full aggregate … is GIVEN
XHD-s on the shallow layer" (ENT-AGG). deps: V3-5a/b/c, V3-7, V0-3.
sketch: Summable → HasSum to its tsum; the exactly-once structure is the
content. hyp_fields: XHD-s shallow (mass_summable) + XHD-d shallow (owner
[2b]); (iv)-REP invoked NOWHERE (the note: "never for the sum's
definition").

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

### Layer V4 — clauses (ii), (iv), (v) [14]

**V4-1 `act_no_entry` · `V4_act.lean` · medium — GUARD RESTORED (C15);
REV 4 (Codex-9): the guard now ALSO sits on ValA's `tgt_supported` FIELD
(V2-4(c)) — the theorem's premise and the hypothesis's premise match, and
inactive-source rows are formal junk at BOTH layers.**
(ii-a) NO-ENTRY, GIVEN ValA (whose `tbl_count`/`tgt_supported` fields carry
(iv)-POLY's correct valuation + the GUARDED landing tie), WITH the note's
active-source guard: `theorem no_entry (hVA : ValA …) … (hact :
V.activeState q₀ αc) (hin : ¬ V.activeState q₀ βc) :
(C.T s m o α β).eval q₀ = 0` — zero is claimed ONLY for active sources
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

**V4-3 `act_agreement_stmt` · `V4_agree.lean` · easy (statement unit).**
(ii-c) ACTIVE-VALUE as the typed per-(n, q₀) check — the Prop this corpus
RECORDS, never proves: `def ActiveValueAgree … : Prop := ∀ q₀ ∈ finitely
many empty-cell pools, AVAgree-shaped agreement after cancellation` — stated
via `MovesS.AVAgree` at the instantiated PoolHyp; removability of
det(I − D)(q₀) = 0 carried as the OKat membership hypothesis (MovesS's
"(ii-c) PASS" gate shape, verbatim consumption). moves_ref: "(ii-c)
ACTIVE-VALUE — … the burden is AGREEMENT: at the finitely many q₀ with empty
cells, the symbolic ℚ(q)-solution's value component, after cancellation,
EVALUATES to the active-subsystem value" (V.1(ii)).
deps: MovesS.Interfaces, V7-4c. sketch: def only. hyp_fields: (ii-c) itself —
"a finite per-(n, q₀) verification duty … exercised by RESUM-n3's wild-p
layer ([3]'s gate), recorded here as the clause's standing check, never a
blanket det ≠ 0 claim" (V.3(ii), finding 8: NO general theorem claimed).

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

**V4-10 `meas_marked` · `V4_meas.lean` · medium.**
(iv)-MEAS in the RETYPED (rev 3) marked-space form: each (m, o, β,
height-class) summand is a finite-level digit-cell union WITH the
continuation mark ADJOINED — a fiber of a finite-level map ON the marked
space; summands pairwise disjoint IN THE MARKED SPACE; as f-events only the
DIGIT CELLS are disjoint (and two summands' f-projections CAN be equal —
stated as: disjointness is claimed on Σ-marked carriers only, plus an
explicit two-continuation instance where f-projections coincide, keyed to
D4-R L5). moves_ref: "the summands are pairwise disjoint IN THE MARKED
SPACE; as f-events only the DIGIT CELLS are disjoint. No ordinary-source
disjointness is claimed anywhere" (V.1(iv), pass-2 finding 2).
deps: Defs 2.E/2.F, MovesD (L12/D4R.4 finite-level realization).
sketch: the marked event's carrier is `Σ (cell × mark)`; disjointness from
the mark coordinate (BY CONSTRUCTION on the Σ-carrier — REV 4, Codex-3: no
box-level cross-mark law exists any more) + `evt_disj_cell` at distinct
digit-cell keys; the equal-projection witness from L5's two eligible
(side, ψ) continuations — now REALIZABLE as an instance (rev 3's blanket
evt_disj CONTRADICTED it; the re-key makes this unit's witness and the
carrier laws jointly satisfiable). hyp_fields: XHD-d (height classes
listed); the L5 eligibility roster (MovesD-keyed field).

**V4-11 `hmc_typing` · `V4_hmc.lean` · medium — RE-KEYED TO THE PROCESS
SIDE at REV 4 (N-1: the rev-3 spec was UNSATISFIABLE — with count-keyed
exactness no false-HMC XHDd existed; Fable N-1's four-line proof. With
`TReal`-keyed exactness and FREE composite events the toy exists again).**
The HMC/HMCAug Prop shapes compile against NON-degenerate instances, BOTH
WAYS: (i) THE FALSE-HMC TOY — over V1-8a's StepSys, a `TmplEvents` with a
COUPLED composite: the 2-step template's `tevt`/`tinst` empty at the
product point (h₁, h₂) = (0, 0) while both one-step events are realized
there (the ⊇ direction of the factorization FAILS; all four TE ties hold
by decide — the coupling lives entirely in the free composite data, exactly
(HMC-AUG)'s "global cone inequality couples successive steps"), with the
`XHDd` listing dom(cons) = the coupled set: `HMC TE D` is FALSE, by decide;
(ii) V1-8b's toy, where HMC is TRUE — the kernel is a REAL hypothesis,
satisfiable both ways, provable neither; + the terminal-final signature
check: `Template.lastT` instances type against `HMC`'s quantifier (the
probe's step 2 is a literal instance BY TYPE); + the HONESTY REMARK,
recorded (from §2.G's underivability audit): the ⊆-flavored fragment at
single-step tails is derivable GIVEN the mark facts + tevt_last_iff — the
toy therefore couples ⊇, which is the note's open direction.
moves_ref: "(v) HMC — … OPEN KERNEL, displayed hypothesis … TERMINAL-
FINAL EXTENSION (rev 4 …): templates INCLUDE those whose FINAL step carries a
terminal outcome" (V.1(v), MOVES 8198–8213). deps: Defs 2.G, V1-8a/b.
sketch: two decide-scale toy models. hyp_fields: none proved ABOUT the CTS
instance; HMC itself OPEN (V.5(2)) — "until HMC closes, K_e(p)^k is NOT a
theorem about the process".

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
it is NOT an interface-general theorem, by (b′), and NO unit consumes it
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
displayed; consumed by V5-2a/b/c and V5-4).

**V5-2a `comp_h_one` · `V5_comphA.lean` · medium — REAL UNIT ID at REV 4
(Codex-16; the parent V5-2 dissolves into a/b/c).**
(COMP-h)'s ONE-STEP case at a fixed entrance mark: the counting-native
`(one-step event).card × normalization = cnt · q₀^{−E} × |Box|-power` at
stabilized levels — evt_card + (U-A) at the fixed history + w_eq.
moves_ref: "(COMP-h) at every concrete ε and fixed h ∈ H(γ): μ̂(marked
event of (ε, γ, h) at p) = ι_{e,ε,β₀}(p) · ∏_{i=1}^k [T·g](p)" (V.1(vi)).
deps: V5-1, V1-6, V4-5. hyp_fields: (U-A) pack (§C/HC-2) + (XHD-u)
(owner [2b]).

**V5-2b `comp_h_step` · `V5_comphB.lean` · HARD.**
THE INDUCTION STEP along γ through `ext`: each step contributes cnt·g by
(U-A) at the fixed history + (u-R) across the histories reaching βᵢ —
REV 4: the per-mark fiber decomposition at REALIZED points rides V5-1's
census lemma (the (COMP-h) scope guard: h ∈ H(γ), supplied by no_stray →
TReal); the count positivity along the chain from V1-3(b). NO unguarded
composite recursion is consumed (none exists — §2.G).
deps: V5-2a, V5-1, V1-3, V2-5. hyp_fields: as V5-2a + XHD-d (the scope
guard's face).

**V5-2c `comp_h` · `V5_comphC.lean` · medium.**
(COMP-h) ASSEMBLED, GIVEN (U-A)'s pack + (XHD-u), ε concrete and h FIXED
in H(γ): `μ̂N (markedEvent ε γ h) q₀ N = ιN ε β₀ q₀ N * ∏ i, (T_i *
g_i(h_i))` in counting-native form (exact at stabilized levels, the MovesC
idiom) — group by entrance mark (V5-1), multiply out (V5-2a/b).
moves_ref: as V5-2a + the V.4 route "Group the marked event by its entrance
prefix … Per entrance mark, the continuation mass along γ at h is the
C.1.5 conditional chain". deps: V5-2a/b, V3-6.
hyp_fields: (U-A) pack (§C/HC-2) + (XHD-u) (owner [2b]) + `MarkFiberTie`
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
over the gate data — F-6's acceptance test). moves_ref: "J_{τ,o}(q) := the
CELL-LEVEL resummed branching mass — the sum, over the branching digit
CELLS of outcome class o at state τ, of the XHD-resummed conditional cell
mass …, EACH CELL ONCE. [o branching := the (c ≥ 1, m ≥ 2) row of (K-SUB)'s
(m, c) CLASSIFICATION]" (§S-RESUM S.0, the CL-18 display; owner-side record
per the PLAN-SYNC flag). deps: Defs 2.H, DefsGate. sketch: definitional +
decide + norm_num. hyp_fields: none (def-layer).

**V5-7b `j_rat` · `V5_jrat.lean` · medium — PER-(τ,o) (C8).**
(J-RAT) = CL-18, the deliverable, now quantified over EVERY outcome
INCLUDING split-route ones (the §2.H carrier is (s, m, o, α)-keyed; split
outcomes are ordinary index values, not missing single-target moves):
`theorem jRat (XsC : XHDsC …) (hcell : CellPolyPack …) : ∀ (d : MoveData …
with route = split), ∃ P : MovesS.PolyGeom, P.degBoundT = Wloc ∧
P.degBoundS = Wstate ∧ ∀ q₀ ∈ Pools, ((evalAt q₀ ⟨P.val, _⟩ : ℚ) : ℝ)
= Jval J hcell XsC d q₀` — J_{τ,o} ∈ ℚ(q) ENTRYWISE, "a deliverable BEYOND
PART-1's TOTAL cell-partition mass"; supplies `RatBurdens.jP/j_ok/j_interp/
j_degT/j_degS` at MovesS's ∀ (e, τ, o) quantifier through V7-3a's roster
equivalence. NO DOUBLE COUNT (Codex-9's second horn closed): Jval's cell
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
= ((C.T d.s d.m d.o d.α (its TargetIx)).eval q₀ : ℝ) *
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

### Layer V7 — CTS-M assembly + the seam instances [18] (Codex-19/REV-4 splits: every former multi-lemma unit is now one display per unit)

**V7-1 `ctsm_ledger` · `V7_ledger.lean` · easy (typing unit).**
THE PER-CLAUSE HYPOTHESIS LEDGER as ONE record (V.1's rev-2 finding-7 list,
verbatim — "each clause is asserted GIVEN exactly its listed set, nothing
less"): `structure CtsmLedger …` with one field per clause line: (i) the
BlockData family + computed lists at consumed skeletons; (ii) (ii-a/b) ←
ValA's (iv)-POLY ties, (ii-c) ← ActiveValueAgree; (iii) primitives free;
ENT-AGG ← XHD-s/-d shallow; ENT-COUNT named; INIT-RAT ← XHD shallow +
(ENT-U) + AffEnt; (iv) ← computed tables / + (XHD-u) / + PART-1's four legs /
measured ← XHD-w + (U-A) + (XHD-u) / resummed ← XHD-d/s (+ cell face); (v)
OPEN + (HMC-AUG) separate; (vi) ← per-identity sets + the solve sentence's
ESCAPE(E0)/(ii-c)/ENT-COUNT/INIT-RAT. REV-3 additions: the (J-RAT) cell
pack (`CellPolyPack`) and (ENT-U) ride as their own ledger fields (they are
consumed by the REV-3 defs, V7-4b/c), and the general table-build law supply
is the TYPED field `stage_laws : StageLawBurden n C` (V7-3d — Codex-20's
missing closed structure). REV-4 additions: the process-side carrier
`TE : TmplEvents n S` rides as ledger DATA (the (v)/(vi) clauses quantify
over it), and `MDomTie`/`MarkDisj` ride as their own ledger fields (the
coherence tie and the within-cell disjointness burden — Codex-5/Codex-3). Every field TYPED to the §3 unit statements (no
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
field — open kernel). Representative `*_Stmt` displays for three fields
(part1/step_row/comp_agg) are in this unit's roster; the rest follow the
same rule. moves_ref: the V.1 clause list. deps: statement layers.
sketch: structure decl + Stmt defs. hyp_fields: none (typing unit).

**V7-2b `ctsm_given` · `V7_ctsm.lean` · medium — SPLIT (Codex-19).**
THEOREM CTS-M assembled: `theorem ctsM (L : CtsmLedger …) :
CtsmConclusions L` — apply each cited unit; assemble. The [1v]-COND capstone
of this corpus. moves_ref: "This note proves CTS-M's clauses EACH GIVEN
EXACTLY the hypothesis set displayed in V.1's per-clause ledger" (header).
deps: V7-1, V7-2a + cited units. sketch: apply; assemble.
hyp_fields: = V7-1's ledger, displayed in the signature.

**V7-3a `tableShape_inst` · `V7_ts.lean` · medium — SPLIT (Codex-19).**
The `MovesS.TableShape n` instance from `CtsFamily`: State e := block-e CTS
cells (s, α) (via `toStepCells` and the block-size datum); VType := `VLabel
n` with `vEquiv := Equiv.refl`-keyed and `vdeg_spec` by rfl; Out/odata from
the letter+outcome rosters with member data from DEG-CONS's tuples;
Wloc/Wstate transported; PLUS `route_eq` (the §2.H compatibility law):
JCells.route s m o = MovesS.routeOf (odata …) under the roster wiring —
F-6's classification is the seam's own. moves_ref: "Downstream discipline
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
--  VERBATIM MovesS.SCSData laws (Defs.lean 1509–1531 of the pasted source)
--  with those data substituted — displayed in full at REV 4, Codex-14.)
structure StageLawBurden (n : ℕ) (C : CtsFamily n) : Prop where
  kmat_all : ∀ e, MovesS.KmatHyp (tableShapeOf C) e
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
  `cellOut` := the Σ-projection); `Rep e τ := {x // S.zc x}` (rep_ne ← zc_ne);
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
  base-coordinate SUM to the INJECTIVE retained-tuple code (§2.D
  `hentCode`: Nat.pair-fold over the reads' (h_r, zig(γ_r)) — distinct
  retained height data get distinct ℕ values; "identifies distinct entrance
  heights" is dead). WHAT REMAINS STRUCTURAL AND STAYS SF-1: the frozen
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
Codex-9's second horn; per-(τ,o) incl. split routes via V7-3a's route_eq);
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
GIVEN V + X (with the dC face) + cp + `hMD : MarkDisj V` (REV 4, Codex-3:
the within-cell disjointness meas_card's biUnion-card step uses is NO
LONGER a carrier law — it rides as the DISPLAYED premise; at the n = 3
gates it holds by decide via emult ≤ 1 (V4-8's census), beyond them it is
open exactly where PART-2's surplus lives):
- `meas_card` (gwt·|Box| = |cellEvt| eventually): gwt = P_c·g by V7-4c's
  DEF; |cellEvt| = Σ_a |evtOf a| (hMD within the cell — the displayed
  premise — since cross-cell/height needs nothing here); each |evtOf a| =
  massOf·|Box| eventually (V.evt_card); massOf = g (X.w.w_eq, zc-guarded);
  P_c.eval = cntc on the domain (cp.count + X.dC.no_strayC realizedness) —
  assemble;
- `xhd_no_stray`: h ∈ HDom → cntc > 0 (X.dC.no_strayC) → cellEvt nonempty
  for N ≥ stabLvl (evt_card with massOf = g > 0);
- `xhd_no_orphan`: h ∉ HDom → cntc = 0 (X.dC.no_orphanC contrapositive) →
  the filter is empty → cellEvt = ∅ at EVERY N (definitional).
moves_ref: the CL-5 nine-input ledger's counting faces (S.0). deps: Defs
2.F/2.G, V7-4a/b/c. sketch: as listed, field by field. hyp_fields: XHD
(w + dC faces) + CellPolyPack + MarkDisj — displayed.

**V7-6a2 `ledgerIV_counts` · `V7_livA2.lean` · medium — the other half of
the G-2 re-split. THE DISJOINTNESS/CENSUS SUITE:** GIVEN V + X + cp:
- `d4r0` (cross-(c,h) disjointness incl. h ≠ h′, one x): `evt_disj_cell`
  at DISTINCT DIGIT-CELL KEYS — cross-cell (same h: the cellOfA key
  differs), cross-HEIGHT, cross-outcome, terminal included, are ALL
  distinct-key instances (REV 4: the frozen d4r0 quantifies (c, h) ≠
  (c′, h′) — a KEY difference, never a within-cell mark pair, so the
  re-keyed law supplies it exactly; no cross-mark claim is consumed);
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
  T·ΣGc = Σ_c P_c·ΣGcell = rowVal — the F-4 acceptance identity);
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
THE XRB RE-KEY, shared-parameter form: the wave-4 instantiation of
`W2_xrb`'s obligation is stated over ONE typed variable
`X : XHD n S_cts TE_cts V_cts`; the four field NAMES become PROJECTION
ALIASES — `xhd_w ↦ X.w`, `xhd_u ↦ X.u`, `xhd_d ↦ X.d` (+ dC/dEnt faces),
`xhd_s ↦ X.s` (+ sC/sEnt faces) — so (i) coherence is BY SHARING (same
weights, same domains, same sums — C27's demand still met: four unrelated
incompatible witnesses are impossible), and (ii) NO premise is
strengthened: the S.1 proof may consume exactly the faces its ledger line
names, per-face accounting preserved (Codex-10's demand). `xhdStmt :=
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
DISPLAYED full-roster `Wsh17PackageV` and flags the rest.
moves_ref: MovesS §W4-SYNC S-2/S-8/S-9 +
this note's V.0 package. deps: V7-4a/b/c, V2-4, V3-9a.
sketch: defs + one structure. hyp_fields: none (names for open obligations —
their TYPES pin their content, per doctrine; inhabitation stays with the
owners).

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
| `TableShape n` (State/VType/vEquiv/Out/odata/Wloc/Wstate) | [MovesV: V7-3a from `CtsFamily` (§2.C); vEquiv via `VLabel` = the R20 pin verbatim; + route_eq (F-6's classification tie)] |
| `DegCons T` | [MovesV: V2-9 (gate rosters, decide) + the CL-11 full-roster burden field for uncomputed skeletons — carried, not discharged] |
| `KmatHyp T e` (a PROP: kcol members size e) | [MovesV: V7-3b PROVES it at the gate instance by decide; general = the TYPED `StageLawBurden.kmat_all` (V7-3d — Codex-20; no prose burden). (C25 repair stands: it is a proposition, and no MovesS theorem derives it.)] |
| `SCSData T` (W/D/ℓ/g/μsel/W'/D'/flankCount/flankWidth/resFactors/selIdx/memberOf + 12 laws) | [SPLIT (C25 repair): DATA fields ← V7-3c from MovesSp species stage fields (s.D, s.w, s.W, s.sel, s.lam) through the roster wiring; LAWS decided at the gate rosters (V7-3c) AND, beyond them, carried as the TYPED `StageLawBurden` (V7-3d — Codex-20: a closed hypothesis structure with all twelve law fields + kmat_all + degcons_all, a `CtsmLedger` field; no prose burden survives)] |
| `MeasuredSide T` (all fields) | [MovesV: V7-4a/b/c from `CtsMeasured` (§2.F) + the XHD package + `CellPolyPack` as data + MovesD boxes; `Hgt` carrier = Σ D, Hpt D ("MovesV instantiates the carrier at wave 4" — DONE here); entrance side = EntIx with the CENSUS wiring (entCount/entInst = the ε-instance census, ιshH = census·q^{−A} — F-1/F-2); cellLvl/cellInst = the STATE census stLvl/stInst (F-5); gwt/μcell/rowVal/kstep = count-polynomial × weight-only sums, kstep with ∏T (F-4) AND the REV-4 k = 0 Kronecker-δ case (N-3); `hent` = the INJECTIVE `hentCode` of the base instantiation (REV 4, Codex-6) + seam flag SF-1 (V7-4b — the round-2/3 disagreement and its computed-evidence resolution on file)] |
| `MeasuredSide`/`TableShape` MECHANICAL INSTANCE FIELDS, named per Codex-17 (`fin`, `deq`, `deqV`, `finV`, `finO`, `finC`, `finB`, `finE`, `decA`, `boxpos`, `rep_ne`) | [MovesV: V7-3a (TableShape side: Fintype/DecidableEq from the §2.C Fintype fields + `Skeleton`'s SP2-finite catalogue; `finO` ← `BlockData.finO`) and V7-4a/b (measured side: `finB/boxpos` ← V's box fields; `finC` ← `finDO` + finite outcomes; `finE` ← V3-4 × list length; `decA` ← `act_size` + polynomial-eval decidability at ℚ points; `rep_ne` ← `zc_ne`) — each an EXPLICIT instance line in the unit's roster, none silently assumed] |
| `RatBurdens T M`: `tgP/tg_ok/tg_interp/tg_degT/tg_degS` | [MovesV: V7-5(a) from ValA (V2-4) × the XHDs/XHDsC geometric faces — CL-6 (iv)-POLY, GIVEN the table-build coverage AND the [2b] height-sum face (C23: rowVal is resummed; counts alone cannot interpolate it)] |
| `RatBurdens.jP/j_ok/j_interp/j_degT/j_degS` | [MovesV: V7-5(b) from V5-7b — **(J-RAT)/CL-18, THE PLAN-SYNC DELIVERABLE recorded owner-side**; per-(τ,o) incl. split routes (C8); height-sum face tagged [2b]] |
| `RatBurdens.ιP/ι_ok/ι_interp/ι_countS_one/ι_count/ι_degT/ι_degS` | [MovesV: V7-5(c) from V3-9c(a)'s PER-COMPONENT PolyGeoms (the C23 type fix) + V3-9a (ENT-COUNT); GIVEN XHD-shallow + (ENT-U) + AffEnt] |
| `RatBurdens.cellP/cellP_deg/cellP_nonzero/cellP_count/act_iff` | [MovesV: V7-5(d), the REV-3 REVERT to the rev-1 sizeP wiring (F-5): cellP = the state-size polynomial; cellP_count ← `stInst_card` (the state census, G4 pattern); act_iff ← `act_size`; the rev-2 CellPolyPack keying and its ActIff premise are STRUCK (they violated cellP_deg at both gates and act_iff at q₀ = 2)] |
| `LedgerIV T M` (all nine inputs) | [MovesV: V7-6a/b/c, CONDITIONALLY — the field-by-field map with the REV-3 TYPED TIES (meas_card ← evt_card + w_eq + cp.count + XHDdC; no_stray/no_orphan ← XHDdC + evt_card; d4r0 ← the AStep disjointness law; xhd_sum ← weight-only Gcell sums × P_c; kstep_one ← V5-8's DERIVED cell_refine; init_count ← ent_card + box_card + the census ιshH (gate: 128 ✓); ent_count_card ← rfl against the census; comp_once ← Gent_hasSum × (ENT-U); hmc ← hHMC explicit — no unconditional instance until (v) closes)] |
| `EscapeE0`, `PoolHyp`, `DetHyp`, `RegP` | [owner [3] MovesS — CL-1; MovesV only supplies the entries' OKat memberships through RatBurdens] |

### 4.2 `MovesS/Interfaces.lean` fields

| field | supplier |
|---|---|
| `RS1Meas.βmeas/β_bdd/βfull` | [owner [3t] → MovesT: measured subtree values; MovesV supplies NO per-f or subtree object — the [3t] fence; h_ent binding per seam flag SF-1] |
| `RS1Bundle.xrb` (W-2) | [owner [3]: the S.1 theorem; its `XRBPackage.xhd_w/xhd_u/xhd_d/xhd_s` premise fields RE-KEYED to the FOUR FACE PROJECTIONS of ONE SHARED package parameter `X : XHD n S_cts TE_cts V_cts` — V7-7 (REV 4, Codex-10: coherence by sharing, per-face accounting preserved; the rev-3 all-fields-=-full-bundle form is STRUCK)] |
| `RS1Bundle.recursion_meas` (W-3) | [owner [3t]/[3]: the RS1GivenPackage route; MovesV contributes the PCI leg's (iv)-REP statement (V4-9) as the re-key target for `pci`'s REP conjunct] |
| `RS1Bundle.nsNull/rexact` | [owner [3t] §T.2 — CLOSED there; tag displayed] |
| `RS4Chain.L` | [MovesV: V7-6c (conditional instance)] |
| `RS4Chain.B/hns/PrimePools/prime_*/Sigmas/sig_exact` | [owner: wave-4 assembly (MovesT + MovesS gate)] |
| `RS4Chain.pools_e0/legs_reg` | [owner [3] — CL-1 E0; consumes MovesV's RatBurdens entries] |
| `RS4Chain.WshP/wsh_ok/WshVal/wsh_interp/wshval_bdd` | [owner [3t]/[3] — CL-17(ii) production; MovesV supplies the `cts_counts` leg: V7-7's `cts_counts_stmt` (ValA ∧ EntCount) + the demanded `xhd_s` face `wsh_xhd_s_stmt` (seam S-8, C26)] |
| `RS4Chain.wsh17_pin` | [owner [3]: instantiated with W17ii's statement at wave 4; the [1v] ingredients = V7-7; the empty-menu exclusion = [3t] tree_ne through S-5 (routed, C26)] |
| `RS4Chain.shDom/shEvtH/visH/shEvt/shWeightH/shevt_grouping/shDom_ne/sh_realized/shweight_card/wshval_card` | [SPLIT: the per-ε̊ shallow ingredients (entrance domains entDom/H(ε̊), entrance events entEvt/entEvtH, ιshH weights — §2.F/§2.G) are MovesV's, at V7-4b's entrance side; the per-SHAPE Ŝ assembly over trees is MovesT's (shapes are [3t] vocabulary). The re-keying REPLACES MovesS's device fields by production objects only when BOTH halves exist — per S-8/S-10's re-keying charge] |
| `RS4Chain.Rval/r_bdd/decidedTotal/x3_total/rs1_equates/rsh_interp` | [owners [3t]/[5]/[3] — W-1/W-4 pins; μ̂/density fence: nothing here is MovesV's to state] |
| `ReadOffBundle.pkg` | [owner [3] — E0 packages] |
| `ReadOffBundle.read` (AVAgree) | [MovesV: V4-3 states the (ii-c) duty in MovesS's own AVAgree shape; the CHECK is RESUM-n3's ([3]'s gate) — recorded, never a blanket claim] |

### 4.3 The seam entries RE-KEYED by this blueprint (count: 6)

1. **S-2 (`W2_xrb` package fields)** — REV 4 (Codex-10): the four `xhd_*`
   Prop placeholders in `XRBPackage` re-keyed to the FOUR FACE PROJECTIONS
   of ONE SHARED parameter `X : XHD n S_cts TE_cts V_cts` (xhd_w ↦ X.w,
   xhd_u ↦ X.u, xhd_d ↦ X.d + dC/dEnt, xhd_s ↦ X.s + sC/sEnt) — coherence
   BY SHARING (C27's demand kept: no four unrelated existentials), no
   premise strengthened (each alias grants exactly its face; the S.1 proof's
   per-face ledger accounting survives). The rev-3 every-field-=-`xhdStmt`
   re-key is STRUCK; `xhdStmt` remains only as V1-5's [1v]-FULL
   discharge-event Prop. `jc_inv`/`sib`/`tb_cap`/`vp`/`rel2_*` stay with
   their owners ([2b]/[3t]/[2r]).
2. **S-8 (`W17ii` + `Wsh17Package`)** — the `cts_counts` field re-keyed to
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
   is the [1v]-side citation form.
5. **W-11 (instantiation of every §2 structure by the REAL CTS objects)** —
   the process gate is now the concrete unit list V7-3a/b/c/d, V7-4a/b/c,
   V7-5, V7-6a/b/c (+ V2-9); DONE when those build. The SCSData/KmatHyp rows
   are part of this gate (C25/Codex-20).
6. **CL-18 (J-RAT) owner-side record** — the PLAN-SYNC flag's demand ("the
   owner notes' NEXT revision rounds must record these deliverables on their
   side") is discharged FOR THE LEAN CORPUS by §2.H + V5-7a/b/c: the
   per-cell tables are typed PER (τ, o) INCLUDING split routes (C8), their
   ℚ(q)-membership stated in the (iv)-POLY pattern, the not-the-marked-T·G
   fence machine-checked. (The NOTE text itself is accepted and unedited —
   this is the Lean-side record, exactly as the flag prescribes cross-note
   binding through the ledger.)

NOT re-keyed here (recorded): MovesS seam entries S-1/S-1e/S-1m, S-3, S-4,
S-5, S-6, S-7, S-10, S-11 (MovesT's vocabulary — trees, fibers, read
ledgers, RS.1); MovesD's §2.5 entries W4-1..W4-4 (TreeModel semantics,
VerdictModel, D4R_CYL consumer, NP-ID — MovesT/HC-2's). (JC-INV)/CL-19 is
[2b]'s and appears in NO MovesV statement. SEAM FLAG SF-1 (V7-4b): MovesT's
h_ent binding must use the Hgt-indexed entrance carriers, not
`MeasuredSide.hent` (retained at REV 3 over Codex-7's objection, on Fable's
round-2 source verification that no MovesS law reads the field — the
disagreement and its resolution are on the record at V7-4b). SEAM FLAG SF-2
(new, V7-7/S-8): W17ii's empty-menu vacuity fence is OWNER-SIDE OPEN — [3t]
owes `tree_ne` + the W7_cutWD first-entrance-ancestor retype; MovesV's S-8
delivery is exactly the two `Wsh17PackageV` fields.

## §5 Build order, process, and the census

**Build order (E-phase):** Defs → DefsGate → V0 → V1 → {V2, V6} (parallel;
V6 depends only on DefsGate + 2.A) → V3 → V4 → V5 → V7. The gate layer V6
is deliberately early-buildable: it is the corpus's non-vacuity anchor (the
sealed numbers re-derived in-kernel before any measured clause elaborates).

**Difficulty census: 95 units = 32 easy / 59 medium / 4 hard.**
Per layer: V0[4: 2e/2m] V1[10: 5e/5m] V2[10: 6e/4m] V3[17: 4e/11m/2h]
V4[14: 3e/10m/1h] V5[12: 3e/8m/1h] V6[10: 5e/5m] V7[18: 4e/14m].
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
declaring), V4-11 (the coupled-toy decide budget).

**THE DESIGN-FREEDOM INVENTORY — COMPLETE, ALL FIVE SLOTS, ALL RESOLVED
(A-5 repair; per campaign §3(ii) each resolution is recorded WITH the audit
round, and no slot remains open into E-phase):**
1. `StepSys.inv` (rev-1 stub) → RESOLVED: DELETED. `C15Pack` already carries
   the pinned inventory carrier (`Inv`/`invOf`/`F`/`mass_factors` — the
   note's C.1(ii) role); nothing in the note demands a slot on `StepSys`
   (adjudicated at A-5, adopted here).
2. `XHDd.chain`'s recursion tie (rev-1 "field the E-designer adds") →
   RESOLVED: NO FREEDOM EXISTS. The note DEFINES T_γ; Lean encodes the
   definition (`chainCount` by recursion through `StepSys.ext`, §2.G); the
   exactness laws quantify over the defined count (C2/C9/A-2).
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
10. (NEW at REV 4) `shapeRank`'s enumeration order (Codex-4) → RESOLVED:
   lex order on the eligible (g, μ) menu, with the recorded
   tighten-at-MovesD hatch (§2.D) if MovesD's Fin m̄ collapse enumerates
   differently.
11. (NEW at REV 4) `zig`'s orientation (Codex-15) → RESOLVED: pinned at
   E-phase (`Denumerable.eqv ℤ` vs its `.symm` — one token, recorded).

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
(V1-2(b)) + the (U-A)-does-not-imply-(u-R) fence V1-7 + V1-8a; XHD-d/XHD-dC:
two-sided exactness against the DEFINED counts (V1-3; degenerate domains
violate no_stray outright) + listed partition BY TYPE (2.A) + V1-8b/c;
XHD-s (all three faces, WEIGHT-ONLY): the PROVED A2-format witness V0-4 +
V1-8b/c — and the count factors live in the [1v] burdens, so no package
field can silently decide INIT-RAT/(J-RAT) (Codex-8/9); the counting ties:
realized by V1-8c's literal census data (ent_card/evt_card/box_card/
stInst_card all checked on the toy); HMC: the false-instance/true-instance
pair V4-11 + V1-8b (REV 4: BOTH exist again — the false one couples the
free composite tevt, the ⊇ direction) + V4-12(c)'s fixed-system
factorization-failure fence + V4-12(b′)'s sum-level coincidence record;
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

**Honest-perimeter recap (what a corpus record may claim when all 95 build):**
CTS-M's clauses machine-checked EACH GIVEN EXACTLY its V.1-ledger set
(V7-2b, conclusions displayed at V7-2a); (U-A) proved given the typed §C
pack; the V-n3 displays re-derived in-kernel at all nine census points
(V6-4c's threshold conditional on the typed CoprimeLiftPack premise); the
MovesS seam supplied per §4 — with XHD (all faces incl. dC)/(XHD-u)/
(ENT-U)/HMC/ENT-COUNT/INIT-RAT-premises/(J-RAT)-cell-pack/(ii-c)/
CL-13-coverage/ContTwo/StageLawBurden/MDomTie/MarkDisj/MarkFiberTie all
OPEN, riding as typed arguments — and the W17ii vacuity fence OWNER-SIDE OPEN (SF-2).
CLAUSE (v)'s record in particular: HMC typed, linked, probed by units both
ways (V4-11/V1-8b), and PROVED BY NOTHING — the REV-4 restoration. NOTHING
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

*(End of MOVESV blueprint REV 4. Next per campaign §3 + the audit-budget
policy: fresh-Fable intermediate audit of this revision + Defs; Codex
reserved for the final confirmation pass; REJECT loops until ACCEPT; then
E-phase.)*

warning: Codex could not find bubblewrap on PATH. Install bubblewrap with your OS package manager. See the sandbox prerequisites: https://developers.openai.com/codex/concepts/sandboxing#prerequisites. Codex will use the bundled bubblewrap in the meantime.
codex
I’ll audit the pasted REV 4 against the frozen displays and the real MovesS signatures, with special attention to the HMC split, pool threading, J-RAT, and the seam field roster. I’ll report every round-3 disposition explicitly, then any fresh defects.
codex
1. **CRITICAL — the pool-index repair does not reach the real MovesS seam.**  
   Offending unit V7-4a says:

   > “`Rep e τ := {x // S.zc x}`”

   But REV 4 changed histories to:

   > “`Hist : ℚ → Cell → Type`”

   Thus `S.zc x` cannot determine the missing pool index, while the frozen `MeasuredSide.Rep : ∀ e, State e → Type` is pool-independent. Likewise, `MeasuredSide.cellEvt` later receives an arbitrary `q₀`, with no equality connecting it to the pool of `x`. Consequently V7-4a cannot instantiate `MeasuredSide.Rep` or `cellEvt`. The local seven-carrier threading is present—`Hist`, `Assign`, `cntraw`, `cntc`, `massOf`, `chainCount`, `evtOf/cellEvt` all carry the history’s pool—but the seam producer is ill-typed.

2. **CRITICAL — V7-3a cannot construct `TableShape.odata`; the required outcome-member data do not exist.**  
   Offending unit:

   > “`Out/odata from the letter+outcome rosters with member data from DEG-CONS's tuples`”

   `BlockData.Outc` is merely an abstract type. Neither `BlockData` nor `CtsFamily` supplies the list of `MovesS.Member`s, their `size`, `δ`, or `status`, nor the required proof that the list is nonempty. `DegCons` is a law about an already-constructed `odata`; it cannot manufacture that data. Therefore the supplied object cannot have the frozen type `TableShape.odata : … → Outcome VType State`.

3. **CRITICAL — the target-index type admits terminal targets for continuing outcomes and does not pin the actual successor skeleton.**  
   Offending Defs:

   > “`| term (v : VLabel n)`”

   in `TargetIx`, with no premise `¬ B.cont m o`; and:

   > “`tgt_menu … : (letterSp m).isLeft`”

   which says only that the letter is a species, not that `tgtSk m o h` is that species’ actual successor skeleton. Thus a continuing outcome has spurious terminal table entries, and its continuing target may be an unrelated skeleton. This is stronger/looser than the frozen `(D4)` target map and CTS-T index.

4. **CRITICAL — Y-3 remains open: `evt_disj_cell` still does not exclude continuation-mark differences by type.**  
   The proposed key is described as:

   > “the `(MoveData/TermData datum, cellOfA-image, Σ-embedded height)` triple”

   `MoveData` contains `m` and `o`; distinct eligible continuations represented by distinct move/outcome data therefore have distinct keys, causing `evt_disj_cell` to assert ordinary-box disjointness. Yet the note explicitly permits their f-projections to be equal. The prose:

   > “for continuing steps WHICH target β the mark selects — is NOT part of the key”

   is not enforced by the displayed type and conflicts with using the whole `MoveData` datum in the key.

5. **CRITICAL — the new `MarkDisj` burden cannot supply terminal-cell `meas_card`.**  
   `MarkDisj` quantifies only over:

   > “`d : MoveData n C`” and “`S.Assign (V.moveOf d)`”

   There is no `TermData`/`AssignT` twin. But V7-4a’s `MeasuredSide.Cell` includes terminal outcome cells, and the frozen `LedgerIV.meas_card` quantifies over every cell. V7-6a1 therefore lacks the within-cell union-cardinality premise for terminal cells.

6. **CRITICAL — Y-4 is not repaired at the value level.**  
   The new field states:

   > “`selRec.get … = shapeRank … (takenGm …)`”

   but `shapeRank` is an independently invented lexicographic enumeration:

   > “`((eligMenu …).indexOf gm)`”

   No typed equality relates it to `MovesD.selRank`. The claimed MovesD identification appears only in prose and an “escalation hatch.” `E8_rankInj` proves injectivity of the real rank; it does not prove that this new enumeration equals it.

7. **CRITICAL — Y-6 remains open: `hentCode` is not injective as claimed.**  
   Offending definition:

   > “`(...map (fun R => Nat.pair R.h (zig R.gam))).foldr Nat.pair 0`”

   A fold with terminal seed `0` does not encode list length; under the standard pairing, zero-coded entries can collide with the terminator. More importantly, it encodes `gam`, not `ustar`; recovering `ustar` also uses `e`, `STR`, `s0`, and `wSide`, none of which enter the code. Thus distinct retained `(h_r,u_r^*)` tuples can receive the same value. SF-1’s observation that the current MovesS core does not consume `hent` is valid, but it does not make the asserted supplier value injective.

8. **CRITICAL — Y-7 is repaired by silently strengthening XHD-s.**  
   REV 4 adds to `XHDsEnt`:

   > “`mass_summable : … Summable (fun … => entCensus … * q₀ ^ (-A))`”

   Frozen XHD-s asserts geometric summability of weight products, not summability of the count-weighted entrance mass. The latter is precisely what V3-8a needs. Making it a new owner-[2b] field assumes the conclusion instead of deriving the note’s “convergence GIVEN XHD-s” from the displayed XHD-s and count bounds. This is an extra open hypothesis silently folded into XHD-s.

9. **CRITICAL — V5-2 drops the note’s explicit XHD-w premise.**  
   V5-2a says:

   > “`hyp_fields: (U-A) pack … + (XHD-u)`”

   and V5-2c repeats the same set. But their statements use the identification of per-assignment mass with `q₀^{-E(h)}`, which is `XHDw.w_eq`. The frozen COMP-h ledger explicitly requires “XHD-w’s (U-A) face + (XHD-u).” A dependency on V4-5 does not discharge its open XHD-w argument.

10. **CRITICAL — V5-7b does not supply J-RAT at the frozen per-`(τ,o)` type.**  
    Offending statement:

    > “`∀ (d : MoveData … with route = split), ∃ P : MovesS.PolyGeom …`”

    `RatBurdens.jP/j_interp` are indexed by every `(e,τ,o)` split outcome, without a chosen continuing target. `MoveData` requires one continuing target and therefore cannot represent a general split outcome with multiple continuing members. The proposed supplier consequently does not produce the frozen `jP` field, even though its intended arithmetic correctly uses `CellPolyPack × XHDsC` rather than marked `T·G`.

11. **CRITICAL — Y-10’s XRB re-key is not a Lean-typed mapping to the real package.**  
    V7-7 says:

    > “`xhd_w ↦ X.w`, `xhd_u ↦ X.u`, `xhd_d ↦ X.d`, `xhd_s ↦ X.s`”

    But the frozen `XRBPackage` fields have type `Prop`, whereas `X.w`, `X.u`, etc. are structure values, not propositions. No adapter structure or re-keyed `W2_xrb` declaration is displayed. The shared-package idea is sound, but the actual frozen field types remain unsupplied.

12. **CRITICAL — the hypothesis structures still admit empty-pool vacuity.**  
    `StepSys` has:

    > “`Pools : Set ℚ`”  
    > “`pools_pp : ∀ q₀ ∈ Pools, …`”  
    > “`hist_ne : ∀ q₀ ∈ Pools, …`”

    but no `Pools.Nonempty` or infinitude field. Hence `Pools = ∅` satisfies `hist_ne`, `zc_ne`, `out_ne`, XHD-w, XHD-u, and the TmplEvents ties vacuously. V1-8’s existence of one good witness does not prevent degenerate instances from satisfying theorem hypotheses. This violates the stated non-vacuity doctrine for standalone StepSys/XHD-face units.

13. **CRITICAL — `StageLawBurden.kmat_all` silently strengthens the required seam hypothesis.**  
    It requires:

    > “`kmat_all : ∀ e, MovesS.KmatHyp (tableShapeOf C) e`”

    The frozen solve interface uses `hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e`. Requiring KmatHyp at every natural block index, including indices outside `1…n`, is strictly stronger and is not supplied by the note’s roster laws.

14. **GAP — V1-6 was not retyped after pool indexing.**  
    Offending statement:

    > “`(x : S.Hist α)`”  
    > “`S.massOf m x h a q₀ = …`”

    `Hist` now requires `q₀`, while `massOf` obtains the pool through `x` and has no trailing `q₀` argument. The displayed unit does not elaborate.

15. **GAP — Y-14/Y-15 remain materially incomplete as Lean skeletons.**  
    Examples include:

    > “`.. }`” in the F4 `Field` instance  
    > “Field instances for F8/F9: the F4 pattern verbatim”  
    > “`eligMenu …; branchingRead … — closed defs`”  
    > “`castMove/castHpt/castAssign … one line each at E-phase`”  
    > “if the library form is ℕ-first, the fix is `.symm`”

    These are unresolved declarations, not displayed Lean definitions. The F8/F9 arithmetic tables are pasted, but their required `Field` instances are still only comments.

16. **GAP — `BlockData.CellIdx` is declared twice.**  
    §2.C declares:

    > “`def BlockData.CellIdx …`”

    while V2-2’s roster again includes:

    > “`def BlockData.CellIdx (B) := …`”

    The second declaration would be a duplicate-name error. The unit should only contain the instance and deletion lemma, but the blueprint has not made that declaration ownership unambiguous.

17. **GAP — Y-16 is only partially closed: V7-2a remains a hidden transcription suite.**  
    V7-2a declares a 24-field structure and says:

    > “each `*_Stmt` def is the VERBATIM ∀-closure … the rest follow the same rule”

    Only three representative statement bodies are promised. The other 21 are not quoted, so their quantifiers and hypotheses cannot be audited. This is exactly an underspecified Defs dependency and a concealed multi-declaration unit.

18. **GAP — the design-freedom inventory contradicts the operative HMC repair.**  
    Inventory slot 2 still says:

    > “the exactness laws quantify over the defined count”

    whereas the REV-4 Defs correctly re-key `XHDd` exactness to `TReal`. This stale normative statement leaves the E-phase implementation rule ambiguous and could reintroduce the N-1 collapse.

### Round-3 disposition audit

- **N-1:** **REPAIRED in the operative Defs.** `TmplEvents`/`TReal`, TReal-keyed XHDd, and the displayed HMC link do leave composite realization free and make both true- and false-HMC toys possible. V5-5 and V7-6c retain explicit `hHMC`. The stale §5 sentence is GAP 18, not a second operative HMC definition.
- **N-2 = Y-1:** **PARTIALLY REPAIRED.** The seven named local carriers are pool-threaded and XHDu is same-pool. The seam regression in finding 1 prevents the repaired carrier from supplying MovesS.
- **N-3:** **REPAIRED.** V7-4c gives the Kronecker delta at `k = 0`; the frozen recursion’s zero case computes correctly.
- **Y-2:** **PARTIALLY REPAIRED.** Outcome-level `Outc/cont` keying is present, but findings 2–3 leave outcome data and target typing unsound.
- **Y-3:** **STILL OPEN.** Findings 4–5.
- **Y-4:** **STILL OPEN.** Finding 6.
- **Y-5:** **REPAIRED.** `MDomTie.mdom_eq/mdomT_eq` is explicit at V2-5, V4-5, V5-8, and V7-5a.
- **Y-6:** **STILL OPEN.** Finding 7. The source-level SF-1 observation itself is consistent with the pasted MovesS files.
- **Y-7:** **PARTIALLY REPAIRED.** V3-8a has no ENT-U premise and V3-8b places ENT-U at the identification, but finding 8 strengthens XHD-s.
- **Y-8:** **REPAIRED under the binding adjudication.** The IF leg is fixed-system, `UpgradeOnlyIf` is named and unconsumed, and the coincidence/failure fences are separated.
- **Y-9:** **REPAIRED.** `tgt_supported` has zc and active-source guards; `ent_supported` correctly has no source guard.
- **Y-10:** **STILL OPEN.** Finding 11.
- **Y-11:** **REPAIRED locally.** `Wsh17PackageV` contains `c15_volumes`, `cts_counts`, and `sib_count`; SF-2 remains explicitly owner-side open.
- **Y-12:** **REPAIRED.** zc guards appear on XHD-w, all six XHD-u laws, XHDd, and XHDdC exactness.
- **Y-13:** **REPAIRED.** V6-2b’s `moves_ref` no longer attributes `6t+3u+1` to the note.
- **Y-14:** **STILL OPEN.** Finding 15.
- **Y-15:** **PARTIALLY REPAIRED.** CellIdx/Realizable order and `ringV` installation are addressed, but findings 15–16 remain.
- **Y-16:** **PARTIALLY REPAIRED.** The five named suites and V7-6a split have real IDs; finding 17 remains.
- **Y-17:** **PARTIALLY REPAIRED.** The mechanical-instance row is present, but findings 1–2 show that listed suppliers do not actually produce several field types.
- **G-1:** **REPAIRED.** `cell_ne_inst` is explicitly part of V7-5c.
- **G-2:** **REPAIRED.** V7-6a1 and V7-6a2 each have three named supply lemmas.

The two arithmetic acceptance checks are correct: `T21(2)=2`, `T21(3)=6`; and `(X−1)²(2)=1`, `(X−1)²(3)=4`. The A2 chart identity and gate-B `128 = (1/4)·512` arithmetic remain correct. V6-4c also keeps `CoprimeLiftPack` as an explicit typed premise and a fenced published-axiom candidate, never an unconditional axiom.

Counts: **13 CRITICAL / 5 GAP**

**REJECT (13 crit / 5 gap)**
tokens used
153,659
1. **CRITICAL — the pool-index repair does not reach the real MovesS seam.**  
   Offending unit V7-4a says:

   > “`Rep e τ := {x // S.zc x}`”

   But REV 4 changed histories to:

   > “`Hist : ℚ → Cell → Type`”

   Thus `S.zc x` cannot determine the missing pool index, while the frozen `MeasuredSide.Rep : ∀ e, State e → Type` is pool-independent. Likewise, `MeasuredSide.cellEvt` later receives an arbitrary `q₀`, with no equality connecting it to the pool of `x`. Consequently V7-4a cannot instantiate `MeasuredSide.Rep` or `cellEvt`. The local seven-carrier threading is present—`Hist`, `Assign`, `cntraw`, `cntc`, `massOf`, `chainCount`, `evtOf/cellEvt` all carry the history’s pool—but the seam producer is ill-typed.

2. **CRITICAL — V7-3a cannot construct `TableShape.odata`; the required outcome-member data do not exist.**  
   Offending unit:

   > “`Out/odata from the letter+outcome rosters with member data from DEG-CONS's tuples`”

   `BlockData.Outc` is merely an abstract type. Neither `BlockData` nor `CtsFamily` supplies the list of `MovesS.Member`s, their `size`, `δ`, or `status`, nor the required proof that the list is nonempty. `DegCons` is a law about an already-constructed `odata`; it cannot manufacture that data. Therefore the supplied object cannot have the frozen type `TableShape.odata : … → Outcome VType State`.

3. **CRITICAL — the target-index type admits terminal targets for continuing outcomes and does not pin the actual successor skeleton.**  
   Offending Defs:

   > “`| term (v : VLabel n)`”

   in `TargetIx`, with no premise `¬ B.cont m o`; and:

   > “`tgt_menu … : (letterSp m).isLeft`”

   which says only that the letter is a species, not that `tgtSk m o h` is that species’ actual successor skeleton. Thus a continuing outcome has spurious terminal table entries, and its continuing target may be an unrelated skeleton. This is stronger/looser than the frozen `(D4)` target map and CTS-T index.

4. **CRITICAL — Y-3 remains open: `evt_disj_cell` still does not exclude continuation-mark differences by type.**  
   The proposed key is described as:

   > “the `(MoveData/TermData datum, cellOfA-image, Σ-embedded height)` triple”

   `MoveData` contains `m` and `o`; distinct eligible continuations represented by distinct move/outcome data therefore have distinct keys, causing `evt_disj_cell` to assert ordinary-box disjointness. Yet the note explicitly permits their f-projections to be equal. The prose:

   > “for continuing steps WHICH target β the mark selects — is NOT part of the key”

   is not enforced by the displayed type and conflicts with using the whole `MoveData` datum in the key.

5. **CRITICAL — the new `MarkDisj` burden cannot supply terminal-cell `meas_card`.**  
   `MarkDisj` quantifies only over:

   > “`d : MoveData n C`” and “`S.Assign (V.moveOf d)`”

   There is no `TermData`/`AssignT` twin. But V7-4a’s `MeasuredSide.Cell` includes terminal outcome cells, and the frozen `LedgerIV.meas_card` quantifies over every cell. V7-6a1 therefore lacks the within-cell union-cardinality premise for terminal cells.

6. **CRITICAL — Y-4 is not repaired at the value level.**  
   The new field states:

   > “`selRec.get … = shapeRank … (takenGm …)`”

   but `shapeRank` is an independently invented lexicographic enumeration:

   > “`((eligMenu …).indexOf gm)`”

   No typed equality relates it to `MovesD.selRank`. The claimed MovesD identification appears only in prose and an “escalation hatch.” `E8_rankInj` proves injectivity of the real rank; it does not prove that this new enumeration equals it.

7. **CRITICAL — Y-6 remains open: `hentCode` is not injective as claimed.**  
   Offending definition:

   > “`(...map (fun R => Nat.pair R.h (zig R.gam))).foldr Nat.pair 0`”

   A fold with terminal seed `0` does not encode list length; under the standard pairing, zero-coded entries can collide with the terminator. More importantly, it encodes `gam`, not `ustar`; recovering `ustar` also uses `e`, `STR`, `s0`, and `wSide`, none of which enter the code. Thus distinct retained `(h_r,u_r^*)` tuples can receive the same value. SF-1’s observation that the current MovesS core does not consume `hent` is valid, but it does not make the asserted supplier value injective.

8. **CRITICAL — Y-7 is repaired by silently strengthening XHD-s.**  
   REV 4 adds to `XHDsEnt`:

   > “`mass_summable : … Summable (fun … => entCensus … * q₀ ^ (-A))`”

   Frozen XHD-s asserts geometric summability of weight products, not summability of the count-weighted entrance mass. The latter is precisely what V3-8a needs. Making it a new owner-[2b] field assumes the conclusion instead of deriving the note’s “convergence GIVEN XHD-s” from the displayed XHD-s and count bounds. This is an extra open hypothesis silently folded into XHD-s.

9. **CRITICAL — V5-2 drops the note’s explicit XHD-w premise.**  
   V5-2a says:

   > “`hyp_fields: (U-A) pack … + (XHD-u)`”

   and V5-2c repeats the same set. But their statements use the identification of per-assignment mass with `q₀^{-E(h)}`, which is `XHDw.w_eq`. The frozen COMP-h ledger explicitly requires “XHD-w’s (U-A) face + (XHD-u).” A dependency on V4-5 does not discharge its open XHD-w argument.

10. **CRITICAL — V5-7b does not supply J-RAT at the frozen per-`(τ,o)` type.**  
    Offending statement:

    > “`∀ (d : MoveData … with route = split), ∃ P : MovesS.PolyGeom …`”

    `RatBurdens.jP/j_interp` are indexed by every `(e,τ,o)` split outcome, without a chosen continuing target. `MoveData` requires one continuing target and therefore cannot represent a general split outcome with multiple continuing members. The proposed supplier consequently does not produce the frozen `jP` field, even though its intended arithmetic correctly uses `CellPolyPack × XHDsC` rather than marked `T·G`.

11. **CRITICAL — Y-10’s XRB re-key is not a Lean-typed mapping to the real package.**  
    V7-7 says:

    > “`xhd_w ↦ X.w`, `xhd_u ↦ X.u`, `xhd_d ↦ X.d`, `xhd_s ↦ X.s`”

    But the frozen `XRBPackage` fields have type `Prop`, whereas `X.w`, `X.u`, etc. are structure values, not propositions. No adapter structure or re-keyed `W2_xrb` declaration is displayed. The shared-package idea is sound, but the actual frozen field types remain unsupplied.

12. **CRITICAL — the hypothesis structures still admit empty-pool vacuity.**  
    `StepSys` has:

    > “`Pools : Set ℚ`”  
    > “`pools_pp : ∀ q₀ ∈ Pools, …`”  
    > “`hist_ne : ∀ q₀ ∈ Pools, …`”

    but no `Pools.Nonempty` or infinitude field. Hence `Pools = ∅` satisfies `hist_ne`, `zc_ne`, `out_ne`, XHD-w, XHD-u, and the TmplEvents ties vacuously. V1-8’s existence of one good witness does not prevent degenerate instances from satisfying theorem hypotheses. This violates the stated non-vacuity doctrine for standalone StepSys/XHD-face units.

13. **CRITICAL — `StageLawBurden.kmat_all` silently strengthens the required seam hypothesis.**  
    It requires:

    > “`kmat_all : ∀ e, MovesS.KmatHyp (tableShapeOf C) e`”

    The frozen solve interface uses `hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e`. Requiring KmatHyp at every natural block index, including indices outside `1…n`, is strictly stronger and is not supplied by the note’s roster laws.

14. **GAP — V1-6 was not retyped after pool indexing.**  
    Offending statement:

    > “`(x : S.Hist α)`”  
    > “`S.massOf m x h a q₀ = …`”

    `Hist` now requires `q₀`, while `massOf` obtains the pool through `x` and has no trailing `q₀` argument. The displayed unit does not elaborate.

15. **GAP — Y-14/Y-15 remain materially incomplete as Lean skeletons.**  
    Examples include:

    > “`.. }`” in the F4 `Field` instance  
    > “Field instances for F8/F9: the F4 pattern verbatim”  
    > “`eligMenu …; branchingRead … — closed defs`”  
    > “`castMove/castHpt/castAssign … one line each at E-phase`”  
    > “if the library form is ℕ-first, the fix is `.symm`”

    These are unresolved declarations, not displayed Lean definitions. The F8/F9 arithmetic tables are pasted, but their required `Field` instances are still only comments.

16. **GAP — `BlockData.CellIdx` is declared twice.**  
    §2.C declares:

    > “`def BlockData.CellIdx …`”

    while V2-2’s roster again includes:

    > “`def BlockData.CellIdx (B) := …`”

    The second declaration would be a duplicate-name error. The unit should only contain the instance and deletion lemma, but the blueprint has not made that declaration ownership unambiguous.

17. **GAP — Y-16 is only partially closed: V7-2a remains a hidden transcription suite.**  
    V7-2a declares a 24-field structure and says:

    > “each `*_Stmt` def is the VERBATIM ∀-closure … the rest follow the same rule”

    Only three representative statement bodies are promised. The other 21 are not quoted, so their quantifiers and hypotheses cannot be audited. This is exactly an underspecified Defs dependency and a concealed multi-declaration unit.

18. **GAP — the design-freedom inventory contradicts the operative HMC repair.**  
    Inventory slot 2 still says:

    > “the exactness laws quantify over the defined count”

    whereas the REV-4 Defs correctly re-key `XHDd` exactness to `TReal`. This stale normative statement leaves the E-phase implementation rule ambiguous and could reintroduce the N-1 collapse.

### Round-3 disposition audit

- **N-1:** **REPAIRED in the operative Defs.** `TmplEvents`/`TReal`, TReal-keyed XHDd, and the displayed HMC link do leave composite realization free and make both true- and false-HMC toys possible. V5-5 and V7-6c retain explicit `hHMC`. The stale §5 sentence is GAP 18, not a second operative HMC definition.
- **N-2 = Y-1:** **PARTIALLY REPAIRED.** The seven named local carriers are pool-threaded and XHDu is same-pool. The seam regression in finding 1 prevents the repaired carrier from supplying MovesS.
- **N-3:** **REPAIRED.** V7-4c gives the Kronecker delta at `k = 0`; the frozen recursion’s zero case computes correctly.
- **Y-2:** **PARTIALLY REPAIRED.** Outcome-level `Outc/cont` keying is present, but findings 2–3 leave outcome data and target typing unsound.
- **Y-3:** **STILL OPEN.** Findings 4–5.
- **Y-4:** **STILL OPEN.** Finding 6.
- **Y-5:** **REPAIRED.** `MDomTie.mdom_eq/mdomT_eq` is explicit at V2-5, V4-5, V5-8, and V7-5a.
- **Y-6:** **STILL OPEN.** Finding 7. The source-level SF-1 observation itself is consistent with the pasted MovesS files.
- **Y-7:** **PARTIALLY REPAIRED.** V3-8a has no ENT-U premise and V3-8b places ENT-U at the identification, but finding 8 strengthens XHD-s.
- **Y-8:** **REPAIRED under the binding adjudication.** The IF leg is fixed-system, `UpgradeOnlyIf` is named and unconsumed, and the coincidence/failure fences are separated.
- **Y-9:** **REPAIRED.** `tgt_supported` has zc and active-source guards; `ent_supported` correctly has no source guard.
- **Y-10:** **STILL OPEN.** Finding 11.
- **Y-11:** **REPAIRED locally.** `Wsh17PackageV` contains `c15_volumes`, `cts_counts`, and `sib_count`; SF-2 remains explicitly owner-side open.
- **Y-12:** **REPAIRED.** zc guards appear on XHD-w, all six XHD-u laws, XHDd, and XHDdC exactness.
- **Y-13:** **REPAIRED.** V6-2b’s `moves_ref` no longer attributes `6t+3u+1` to the note.
- **Y-14:** **STILL OPEN.** Finding 15.
- **Y-15:** **PARTIALLY REPAIRED.** CellIdx/Realizable order and `ringV` installation are addressed, but findings 15–16 remain.
- **Y-16:** **PARTIALLY REPAIRED.** The five named suites and V7-6a split have real IDs; finding 17 remains.
- **Y-17:** **PARTIALLY REPAIRED.** The mechanical-instance row is present, but findings 1–2 show that listed suppliers do not actually produce several field types.
- **G-1:** **REPAIRED.** `cell_ne_inst` is explicitly part of V7-5c.
- **G-2:** **REPAIRED.** V7-6a1 and V7-6a2 each have three named supply lemmas.

The two arithmetic acceptance checks are correct: `T21(2)=2`, `T21(3)=6`; and `(X−1)²(2)=1`, `(X−1)²(3)=4`. The A2 chart identity and gate-B `128 = (1/4)·512` arithmetic remain correct. V6-4c also keeps `CoprimeLiftPack` as an explicit typed premise and a fenced published-axiom candidate, never an unconditional axiom.

Counts: **13 CRITICAL / 5 GAP**

**REJECT (13 crit / 5 gap)**
