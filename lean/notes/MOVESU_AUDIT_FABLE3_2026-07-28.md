# MovesU blueprint REV 5 — fresh-instance confirmation audit (Fable #3)

- **Date**: 2026-07-28
- **Auditor**: fresh Fable instance #3 (no prior context; parallel to the Codex REV 5 re-verdict)
- **Scope**: REV 5 confirmation — (1) sub-bundle citation-list check (FinStack/SolveStack/LowerStack
  vs the note's own displays, verified hardest), (2) delta discipline rev 4 → rev 5
  (rev 4 fetched via `git show 93bafb6`), (3) the six rev-4 pressure points, (4) fresh sweep.
- **Ground truth**: `lean/notes/MOVES_2026-07-24.md` lines 12879–13630 (§U-SQUEEZE), read in full.
- **Blueprint**: `lean/notes/MOVESU_LEAN_BLUEPRINT_2026-07-28.md` @ 572a622 (1099 lines), read in full.
- **Charge**: `lean/notes/CAMPAIGN_AUDIT_CHARGE_2026-07-28.md` (below its `---`).

---

## 1. Citation-list verification (the REV 5 delta's substance)

I enumerated the three governing displays myself before reading the bundles.

**(U-n) upper side (note 13140–13145):** "the UPPER side GIVEN the finiteness stack
{SQ.0's budgets with TRACK-COUNT + D(n) + the genuine-increment sub-claim (CL-7); the
[3t] package (CL-10)} AND the solve stack {E0 (CL-1); the CL-5 nine; CL-6; the CL-8
(e1)–(e5) legs; CL-9's displayed set (XRB proved-under-hypotheses); CL-11;
CL-13…CL-16's table inputs; CL-17; CL-18; CL-19}".

**SQ.2 partial-claim display (U3's; note 13079–13081 routed through SQ.1 13043–13045):**
"decided_σ(N)/p^{nN} is a PARTIAL SUM (the thr ≤ N slice)…"; SQ.1: "decided_σ(N) =
Σ_{T : typemult(T) = σ, thr(T) ≤ N} #fiber(T) is a FINITE sum (SQ.0/CL-7) of exact
fiber counts (TREE-N/CL-10)". Cites: CL-7, CL-10, and the TREE-N identity itself.

**(U-n) lower / checksum leg (note 13145–13146 + SQ.3 13130–13132):** "the LOWER side
additionally GIVEN RS.4's inherited set (X.3/CL-4 included)"; SQ.3 spells the inherited
set: "E0, the CL-5 nine, RS.1's set, X.3/CL-4, and the whole RS.2 rationality chain
incl. (J-RAT)/CL-18".

**Verdicts per bundle:**

- **FinStack** (`cl7 : trackCount ∧ dnDuty ∧ genuineIncrement`; `cl10 : sib ∧ jcMulti ∧
  treeExpTreeN`; `finiteness_stack` identity): `cl7` = exactly the note's CL-7 triple
  ("TRACK-COUNT + its D(n) and positive-genuine-increment companions", ledger 13243–13244) —
  the derived budgets (a)/(b)/(d) correctly carry no slots. `finiteness_stack` = exactly
  SQ.1's displayed identity. `cl10` — **one finding, §2 below**: it is CL-10 **minus
  VP-SOUND**, and the omission is neither licensed by a note citation nor documented.
  Nothing OVER: no CL-1–6/8/9/11–19, no RS.4, no CL-4, no O3, no env→0. Confirmed.
- **SolveStack** (`cl1, cl5 (nine conjuncts), cl6, cl8 (six conjuncts), cl9, cl11
  (noEqualEFeedback ∧ KsubM1C1 M), cl13 (ctsmSyntax ∧ MenuWF M), cl14, cl15, cl16,
  cl17, cl18, cl19, solve_stack`): matched item-by-item against the upper display's
  solve-stack list — **exact**. CL-5's nine conjuncts match SQ.6 item 6's enumeration
  (i)–(ix); cl9 = RS.0(α)+(β)=XRB per the display's "CL-9's displayed set"; cl14 (CLOSED
  upstream) rightly included since the display cites the range "CL-13…CL-16". The
  operative `solve_stack` (finiteness + identification + explicit `0 ≤ evalℝ`, RegP-guarded)
  is SQ.2's "FINITENESS … and IDENTIFICATION … carry the tagged stack" + "R_σ(p) ≥ 0
  stated EXPLICITLY" — the accepted rev-2 interface, unmoved. NO CL-2/CL-3/CL-4, NO
  RS.4, NO VP-SOUND, NO O3 — confirmed against the display. **Exact.**
- **LowerStack** (`cl4, rs4_checksum, rs4_eval`): as the ADDITIONAL slice this is exact —
  the rest of RS.4's inherited set (E0 → cl1; the CL-5 nine → cl5; RS.1's set → cl10/cl17
  via FinStack+SolveStack; the RS.2 chain → cl6 + cl18) already rides the union U6
  consumes; the genuinely additional members are exactly X.3/CL-4 and the checksum.
  Carrying both checksum forms (ℚ(q) identity + RegP-guarded evaluation) is faithful:
  both are readings of "RS.4's checksum … consumed WITH its full inherited set", and the
  evaluated form is what SQ.3's arithmetic literally uses. No CL-2/CL-3. **Exact.**
- **CL-2/CL-3 confinement**: note 13156–13158 — "The RATE form (gate SQUEEZE-n3's
  theory-env bracket) … additionally inherits CL-2/CL-3 + the (X2-*) family". The rate
  form is the gate (a census artifact, seal-specified, chained behind RESUM-n3), not a
  displayed theorem of the note beyond the gate spec; U10's qualitative limit consumes
  "the QUALITATIVE form — the limit consumes no envelope constant" (13146–13147).
  CL-2/CL-3 appearing in NO premise except `CapstoneLedger` (U10) — where Theorem U's
  "CONDITIONAL — on the COMPLETE capstone ledger" requires them — is **faithful**;
  grep confirms `weightCharge`/`progressX2` occur only in KernelStatements + cl2/cl3.
  "No U6b" is a correct scope call. Confirmed.
- **Literal-copy check (G9's own demand)**: every field formula in the three sub-bundles
  compared character-for-character against the corresponding `CapstoneLedger` field —
  identical (cl5/cl8 conjunction orders included). The three projection defs are pure
  `⟨…⟩` re-bundlings in declared field order (FinStack 3, SolveStack 14, LowerStack 3
  components — counts match). No strengthening, no weakening, no re-packing at U10
  (its sketch fires `L.finStack`/`L.solveStack`/`L.lowerStack`). Confirmed.

## 2. Findings

**Finding 1 — GAP (missing hypothesis-field / note-internal ambiguity): FinStack's
"CL-10" is CL-10 minus VP-SOUND, undocumented.**

Spec text (DefsLedger, FinStack docstring): "SQ.2-partial's EXACT stack (D12): the
finiteness stack {CL-7; CL-10} + the operative TREE-N identity — nothing else"; the
bundle carries `cl10 : K.sib ∧ K.jcMulti ∧ K.treeExpTreeN` and NOT `cl10_vpsound`.
D12 likewise: "U3 ← FinStack (the (U-n) upper side's 'finiteness stack {… the [3t]
package (CL-10)}' …)".

Note displays pulling the other way (≤ 2 lines each):
> "CL-10 the [3t] TREE-ASSEMBLY package (§4t): (SIB) … TREE-EXP … + TREE-N … VP … and
> VP-SOUND (a citation obligation …)" (ledger, 13253–13282)
> "[3t]-FULL carries (SIB)/(SIB-STEP), (JC-multi), and VP-SOUND's two cites — i.e.
> TREE-N/TREE-EXP's CL-10 tags, which SQ.1's fiber counts, SQ.2's partial-sum reading,
> and the sibling products consume" (implication audit, 13429–13431)

By the note's own ledger definition VP-SOUND is a component OF CL-10, and the
implication-audit gloss lists it (in the same breath as (JC-multi), whose inclusion in
FinStack rests on exactly that sentence) among what SQ.2's partial-sum reading consumes.
The blueprint's exclusion follows the note's fine-grained consumption map instead —
VP-SOUND's in-note consumption sites are Theorem U's identification parenthetical
("X.3/CL-4 + [3t] VP, with VP-SOUND's citation duty", 13172) and X.3's own tag list
(13051), neither on the upper side — and follows Codex-FINAL 1/2's enumeration, which
phrases VP-SOUND as separate from the CL items (an enumeration the note's CL-10 entry
does not support). So FinStack matches NEITHER consistent reading: the narrow reading
(SQ.1's inline "(SIB)" tags) excludes jcMulti too; the package reading includes vpsound.
Under D12's own banner ("a unit's hypothesis is EXACTLY the display's citation list")
this is a silent carve-out at one conjunct: U3/U4/U6's Lean statements are (inertly)
stronger than the display's conditional claim if the package reading governs.

REPAIR (either suffices): add `cl10_vpsound` to FinStack (and to the projection), or
add one documenting sentence at FinStack/D12 recording the carve-out with the SQ.4
parenthetical as its citation and the orchestrator's adjudication of the
implication-audit gloss. Classification: GAP (the charge's own taxonomy lists
"missing hypothesis-field" and ambiguity as gap-class; the omitted conjunct is inert
in every proof and the full ledger at U10 drops no tag at the statement-of-record).

No other findings: no over-hypothesization anywhere (checked every bundle field against
its display), no under-citation beyond Finding 1, no new vacuity channel (the slices are
Prop field-selections; ledger ⟹ slices by the projections, so U10 remains firable).

## 3. Delta discipline (rev 4 = 93bafb6 → rev 5 = 572a622)

Full diff read: 10 hunks, 254 diff lines. Complete enumeration:
1. Header + REV 5 preamble paragraph (meta).
2. D12 inserted (its four display quotes checked against the note — verbatim-accurate).
3. DefsLedger code block: FinStack/SolveStack/LowerStack + 3 projection defs INSERTED
   after `UInstance`. `CapstoneLedger`, `KernelStatements`, `UInstance` byte-untouched.
4. U3, U4 statement/sketch/hypothesis_fields re-sliced (premises only; conclusions
   byte-identical to rev 4).
5. U6 likewise (conclusion byte-identical).
6. U10 **sketch line only** — the bracket now fired on the ledger's projections;
   U10's statement block and hypothesis_fields are byte-identical to rev 4. A benign
   proof-route note, consistent with "nothing else"; recorded here for completeness.
7. G9 inserted (§4 flags).
8.–9. §6 status/counts + next-gate sentence (meta; "29 cumulative findings" checks out:
   13 + 7 + 6 + 3).
10. §7 CF table appended (its CF-1/2/3 rows match the actual Codex-FINAL verdict text,
   which I read: REJECT 3 crit / 0 gap, all over-hypothesization).

Defs.lean skeleton, U0/U0b/U1/U2/U5/U7/U8/U9/U11: NO hunks — byte-identical to the
rev-4 text that Fable #2 accepted 0/0. **Delta discipline CONFIRMED** (with the one
benign U10-sketch note above).

## 4. The six rev-4 pressure points — re-confirmed on the rev-5 text

1. **KsubM1C1 halt exemption**: `o.sameSize = true → o.c ≠ 0 → o.m = 1 ∧ o.c = 1` —
   same-size continuations only, halts (c = 0, the b_e^{term,fin} leaves) exempt;
   matches "equal-e continuation rides EXCLUSIVELY in K_e's (c = 1, m = 1) rows"
   (13116–13118). Untouched. ✓
2. **ctsmSyntax full carrier**: `ctsmSyntax : Prop` slot present with the full CL-13
   content in its docstring; `cl13 : K.ctsmSyntax ∧ MenuWF M` in BOTH CapstoneLedger
   and SolveStack — no open tag dropped in the slice. ✓
3. **p-uniform M/K**: `theoremU` binds one `S`, one `M`, one `K` before `∀ p`;
   `UInstance n S M K p` per-prime. Untouched. ✓
4. **Menu pins**: `menuCount` + `menu_card` + `menu_not_all_empty` (single empty menu =
   halt convention still allowed). Untouched. ✓
5. **Equation pins**: `bidx_card`/`JIdx_card`/`WIdx_card`/`legIdx_card`; positivity only
   at `instBiNe`/`blockDim_pos`; no `cellCount_pos`/`shapeCount_pos`; G8's owed
   owner-table confirmation still recorded. Untouched. ✓
6. **Spine**: U1 (BOX-N), U2 (Tonelli existence/domination), U5 (SQ.3 as arithmetic),
   U7 (limit forcing) = exactly the note's four tag-free steps (13618–13622); U10's
   ∃-R-before-∀p + three-clause conclusion + D8 restricted quantifier; U11's second
   squeeze (sandwich decided ≤ trueCount ≤ decided + undec — re-derived by me, sound).
   All byte-untouched. ✓

## 5. Fresh sweep (whole rev-5 text, checklist items 1–5 of the charge)

- FAITHFULNESS: U4/U6 conclusions = SQ.2/(U-n) displays verbatim (measured env =
  undec/p^{nN} per SQ.1's notation); U6's `hreg` = the rev-3 (REG-p) qualifier binding
  the bounds themselves; RegP = the full rev-3 schema (r1 full determinant + r2 over the
  DEFINED seven-family union at every pool + the ruling-(D) evaluability clause). ✓
- NON-VACUITY: unchanged from the accepted rev 4 (concrete Box/toPoly counts, pinned
  pools/blocks/index families, D9's declared boundary); the new Prop bundles add no
  degenerate-instance channel. ✓
- HYPOTHESIS FIDELITY: every open kernel appears (KernelStatements slots + typed
  fields); nothing silently strengthened into a definition; no axiom anywhere. The one
  slice-boundary issue is Finding 1. ✓ otherwise
- DEFS SOUNDNESS: no new definition decides anything open. Elaboration note (not a
  finding, consistent with "elaboration-phase target"): the three projection defs use
  `n p X F S D M K` as free variables — DefsLedger will need the corresponding
  `variable` binders in scope; constructor arities/orders check out.
- DECOMPOSITION: units remain one-display each; U3/U4/U6 sketches still fit. ✓

## 6. Counts and verdict

Findings: 0 CRITICAL / 1 GAP (Finding 1, §2 — the FinStack CL-10/VP-SOUND carve-out,
undocumented; repair is one conjunct or one sentence).

Citation-list check: SolveStack exact; LowerStack exact; CL-2/CL-3 confinement exact;
FinStack exact except the gap. Delta discipline: confirmed. Six pressure points: all
survive untouched.

**REJECT (0 crit / 1 gap)**
