# WMULTDCX-PE2 — round-2 hostile content verification (fresh context)

Object: `lean/notes/openmath/WMULTDCX_2026-08-08.md` at commit **03635d0**
(the W-r1 repaired text; confirmed via `git log -1 --format=%h -- <file>`;
working tree = commit, diff empty).  Round 1: PE1 NOT-CLEAN 1C/2G+2n
(report `WMULTDCX_passPE1_report.md`, instrument `wmultdcx_pe1_ext.py`).
Charge: (1) hostile discharge check of all five W-r1 remedies; (2) full
re-verification sweep of the repaired spine; (3) machine re-run + spot
re-derivations.  Role: verify only; nothing fixed.  New file added by this
pass: `verification/openmath/wmultdcx_pe2_ext.py` (spot instrument riding
PE1's independent machinery read-only).

## Part A — machine section (charge 3)

* **Pins.**  `wmultdcx_derive_checks.py` md5
  bea1a43d619a3c91a9a0b2f32c0920c0, output
  2b5395adca632fa0c2e3564db12e668d, results
  000ac228dc4aa4ea6309cf24d0a648ec — all three MATCH the note's S0 and
  dependency-line pins.  Stress chain on disk unchanged
  (15315cca…/2ff1cdc7…/41cbf2f1… — match the PE1-recorded pins).  The
  W-r1 commit (03635d0) touched ONLY the note + a 30-line
  BRIDGE_ADJUDICATIONS record; `RMENGINE_2026-08-08.md` untouched.
* **Read-only re-run.**  `wmultdcx_derive_checks.py` re-executed in a
  sandbox copy (/tmp/pe2_rerun; committed artifacts untouched, md5s
  re-verified after): all 11 DCK families GREEN [0 violations], output
  IDENTICAL modulo elapsed, results JSON IDENTICAL modulo `elapsed`.
  Counters reproduce the note verbatim: 412 rows, 858 cells, 801
  junk-free, 112 beyond-floor, minnz 286/0, stock 302 ok / 0 fail,
  greedy 218.
* **The 126/126 zero-cell census, re-computed from the committed JSONs
  (charge 1a machine leg).**  Derive results: 412 rows = 286 live + 126
  dead; **all 858 cells sit on live rows; every one of the 126 dead rows
  has ncells = 0** (126/126).  Stress results: 412 traced rows, 126
  dead, **0 dead rows with q1nz or any nonzero part; 0/72 divergences on
  dead rows**; gap distribution 70×(+1), 2×(+2).  Bonus census: liveness
  coincides with the law clause c_{m−1} ≥ k on ALL 412 rows (0
  mismatches) — consistent with (EMPTY-(m+1)) on every probed instance.
* **Disclosures verified in source (charge 1e).**  (STK): the
  `stock1_ok` counter increments only inside the `if allg1:` guard
  (runner lines 345–363), so the denominator is exactly the 302 traced
  rows of the 16 all-g = 1 towers; the 110 g₀ = 2-tower rows are never
  stock-censused (JSON: allg1 rows = 302, g₀ = 2 rows = 110).  LED:
  DCK-LEDGER iterates over `q2sink` (terminal Q¹ cells) only.  Both W-r1
  disclosures are accurate.  Greedy tie: allg1 ∧ live = 218 rows = the
  greedy_cell_found counter, matching "(STK) ∧ clause" (clause ⟺ live on
  the battery).
* **Spot re-derivations (2 instances, 4 of the 72 sealed records; both
  towers ABSENT from PE1's 8-instance detailed list).**  Instrument:
  `wmultdcx_pe2_ext.py`.  Hand derivations first (this report), machine
  second:
  - **W3FTOP (77,77)** (reads (2,1,1),(2,1,1),(1,1,1),(2,1,1); m = 3,
    flat top e₂ = 1).  Hand: γ-chain 1, 5, 11, 23; u-chain u₃ = 23,
    s₃(u₃) = 0 (e₂ = 1), u₂ = 23, s₂ = 1, u₁ = (23−5)/2 = 9, s₁ = 1.
    Split of 77: s₄ = 1 (TRACK), s₃ = 0, s₂ = 1, s₁ = 1, tail 5; σ =
    (2,2,0).  pool₁ = 3, c₁ = 1; pool₂ = 2+1+1 = 4, c₂ = 2; D = 0,
    k = 2·1−0 = 2; clause 0+2 ≥ 2 live.  W-D7(i) hand-checked: a =
    (1,1), r₁ = 0, r₂ = 1, b = (0,1); a+b = (1,2) = c ✓.  Machine:
    HAND-DERIVATION TIE OK; maxnz = [2,3]; **both sealed records
    (level 1: 2 > 1; level 2: 3 > 2) CONFIRMED**; W-D4/W-D6/W-D6c
    0 fails; 2 beyond-floor cells, both riding dumps (dmp = [1,1,0],
    principal) — the W-D6c channel exact.  W-D4 hand-checked on all 3
    Q¹ cells from the dump: π₂ = 2 = k+1·0+0 (r = 0, j₂ = 0) and
    π₂ = 3 = k+1·1+0 (r = 1) ✓.
  - **W3NEST (295,295)** (reads (2,1,1),(2,1,1),(2,3,1),(2,1,1); m = 3).
    Hand: γ-chain 1, 5, 23, 93; u₃ = 93, s₃ = 1 (h₂ = 3), u₂ = 35,
    s₂ = 1, u₁ = 15, s₁ = 1.  Split of 295: s₄ = 1 (TRACK), s₃ = 1,
    s₂ = 1, s₁ = 1, tail 8; σ = (2,2,2).  pool₁ = 3, c₁ = 1; pool₂ = 4,
    c₂ = 2; D = 3, k = 1; live.  Machine: HAND TIE OK; maxnz = [2,3];
    **both sealed records (level 1: 2 > 1; level 2: 3 > 2) CONFIRMED**;
    W-D4/W-D6/W-D6c 0 fails; 4 beyond-floor cells; the level-1 divergent
    cells carry dmp₀ = 1 (dump channel), W-D4 identity checked on the
    dumped cells (e.g. pc = [2,1,2], j = [0,1,0], ncorr₂ = 0: π₂ = 1 =
    k+0+0 ✓; pc = [1,2,2], j = [1,0,1]: π₂ = 2 = 1+0+1 ✓).
  PE2 SPOT VERDICT: ALL CONFIRMED (exit 0).

## Part B — the five W-r1 remedies, hostile discharge check (charge 1)

* **(a) PE1-C1, the rewritten S9 paragraph — DISCHARGED.**  The three
  withdrawn assertions ("cancellation phenomenon, not path
  non-existence"; "derived, not just measured"; "provably NOT closable
  by mass arguments") are gone from the live text (survive only inside
  quoted withdrawal brackets: head bracket, S9 W-r1 bracket, claims row,
  S11 — each labeled WITHDRAWN).  The replacement paragraph's every
  factual claim re-verified against the committed artifacts: 126/126
  dead rows zero-cell (both JSONs, Part A); 112 beyond-floor cells and
  72 sealed parts entirely on live rows ✓; the a-fortiori consistency
  remark (a dead-TRACK-row Q¹ cell would have π_{m−1} ≥ k > c_{m−1} by
  W-D4, hence be beyond-floor and ride a W-D6c channel — none occurs) is
  a valid inference from W-D4 + W-D6c + the zero-channel census ✓; "a
  mass-conservation UPPER bound at the floor is unavailable on the full
  tree" ✓ (the 72 live witnesses); the (i)/g₀ ≥ 2 leg is now marked
  "MEASURED, instance-grade, not derived" ✓.  Consumption re-check:
  nothing graded PROVED consumes the withdrawn claim — re-confirmed by
  reading every W-D proof body and the PID† assembly on the repaired
  text (the S4(b)/S5 census inputs stay marked "input to S9, not a
  proved claim").  RESIDUE at S6 and in the box gloss: see findings
  G-1/N-1 — neither is a consumption by a PROVED item.
* **(b) the (EMPTY-(m+1)) display — DISCHARGED, and the reduction is
  VALID.**  Grading: the display carries "[CONJECTURE-grade route]", the
  lead header "conjecture-grade, NOT a result", battery status
  "measured, not derived on any class" — no proof-grade language on the
  conjecture itself.  The embedded reduction claim ("By W-D4 + W-D6c it
  suffices to show: when c_{m−1} < k the two excess channels cannot fund
  π_{m−1} ≥ k on any legal path") RE-DERIVED: suppose a two-exit path
  exists with terminal Q¹ cell X.  W-D4 ((H2), displayed) gives
  π_{m−1}(X) ≥ k > c_{m−1}.  If X's path is dump-free with principal
  d-cell, W-D6 (P-divisor form, hypothesis-free beyond the setting, with
  ĉ_l ≤ c_l always) caps π_{m−1}(X) ≤ c_{m−1} — contradiction; otherwise
  X rides an excess channel (W-D6c, the contrapositive) AND has
  π_{m−1} ≥ k — excluded by the sufficient statement.  So no two-exit
  path, Q¹ an empty sum = 0 = (SURV)(ii).  Hypothesis display is exactly
  right: (H1) enters through W-D0 (tree = Q¹), (H2) through W-D4;
  W-D6/W-D6c need no (H3)/g₀ pin in the P-divisor form (the t⃗ = 0 cell
  has λ-chain = u-chain g-free).  The sharpening (no cells, a fortiori
  Q¹ = 0) and the EMPTY ⟹ (ii) implication are trivially sound ✓.
* **(c) W-D7(iii) as restated — DISCHARGED at the lemma and at five of
  six displayed sites; ONE residual site (finding G-1).**  Both
  directions re-derived under the pins: cap ≤ from W-D6 + ĉ_l = c_l at
  (H3) ∧ g₀ = 1 (numeric identity, P = e), holding for every dump-free
  principal Q¹ cell with NO (STK)/clause input ✓; equality from
  W-D7(ii)'s greedy maximizer, which is legal under (STK) and reaches
  the second exit IFF D + c_{m−1} ≥ 2e_{m−1} (the rearrangement via (i)
  re-checked: (σ_m + a_{m−1} − e_{m−1}) + s_m(u_m) + b_{m−1} ≥ e_{m−1}
  ⟺ D + a_{m−1} + b_{m−1} ≥ 2e_{m−1} ⟺ the clause) — so the max is
  attained exactly under (STK) ∧ clause ✓.  W-D7(i) re-derived
  algebraically (carry-split identity, induction with a₀ = b₀ = 0) and
  hand-verified on W3FTOP (77,77) ✓.  The empty-max case is displayed
  and instance-accurate (clause-failing traced rows = the 126 dead rows;
  zero Q¹ cells there) ✓.  Pin audit, site by site: W-D7(iii) ✓, S0
  reconciliation bold ✓, S8(b) ✓, S8 closing sentence ✓, F6 ✓, W-D7
  claims row ✓.  Residual: the S0 trailer sentence and the W-D6
  statement gloss still carry unqualified attainment language — G-1.
* **(d) W-D2(0)'s (H3) any-d-cell argument — DISCHARGED.**  Re-derived:
  a d-cell D of Ĉ_m is reduced, ON-LINE at γ_{m+1}, ON-GRID (RM-GEN S2.1
  certified inventory, quoted verbatim from RMENGINE lines 384–390 —
  "EVERY cell of Ĉ_m is reduced, ON-LINE at γ_{m+1}, ON-GRID, with
  nonzero residue").  λ_m(D) = γ_{m+1} = u_m; the on-grid recursion
  j_l(D) = s_{l+1}(λ_{l+1}) + t_{l+1}e_l with t = 0 forced at l = m−1 by
  standing (H2) (g_{m−1} = 1) and at 1 ≤ l ≤ m−2 by (H3), so λ_l = u_l
  down to level 1 by the recursion λ_{l−1} = (λ_l − j_{l−1}γ_l)/e_{l−1};
  the level-0 t-freedom (g₀ free) touches only j₀/w₀(b), not λ_l for
  l ≥ 1 ✓.  So u₁..u_m are truncation lines of ANY d-cell, ≥ 0 by
  L-GRID; Ĉ_m ≠ 0 supplies a cell — grounded in the SAME consumption the
  lemma already displays (RM-GEN S2.1 / [ILN]† (R1) + (Ĉ1)–(Ĉ3): the
  (Ĉ3) certificate Σ res(c̄_D)𝔷(D; γ_{m+1}) = τ_m with realize_m placing
  "nonzero τ's only"), NOT in F3 (principal-cell existence at g₀ ≥ 2) —
  the F3 consumption is genuinely gone.  ((H2)'s role rides the standing
  hypotheses of the whole note, S1; the "(under (H3))" display reads as
  "additionally", consistent with the note's convention.)  The (H3) pin
  is carried in the proof line and the claims row; the named downstream
  consumers of u ≥ 0 (W-D6 e-form, W-D7) carry (H3) explicitly ✓.
* **(e) the disclosures — ACCURATE** (verified in runner source + JSON,
  Part A: stock census all-g = 1-guarded, denominator 302, the 110
  g₀ = 2 rows never censused; DCK-LEDGER terminal-cells-only, with the
  interior coverage correctly attributed to the edge-by-edge proof and
  PE1's hand trace).

## Part C — spine re-verification sweep (charge 2)

* **W-D1–W-D7 chain.**  Re-read in full on the repaired text; the W-r1
  edits touch NO lemma mathematics except the W-D2(0) rebase (checked in
  (d)) and the W-D7(iii)/bracket displays (checked in (c)); the diff
  9bec735 → 03635d0 confirms every other proof body byte-unchanged.  PE1
  re-derived each lemma independently (fresh instrument, set-equal 72,
  28-edge hand audit); this pass re-verified W-D7(i) algebraically,
  W-D4's specialization (dmp_{m−1} = 0 since corrections dump strictly
  below their level and Y-dumps land at level 0 < m−1; cons_{m−1} =
  (2+r)e_{m−1} at g_{m−1} = 1), W-D6's induction (floor-monotonicity,
  ĉ_l ≤ c_l from P ≥ e), W-D6c's contrapositive — all sound — and
  hand-checked LED/W-D4 arithmetic on the two fresh spot instances
  (Part A).
* **PID† assembly.**  (a)/(c)/(d)/(e) unchanged and re-checked against
  their lemmas; (b) now carries (H3) ∧ g₀ = 1 + (STK) ∧ clause with the
  empty-max caveat — matches exactly what W-D6 + W-D7 prove.  Nothing
  calls PID† two-sided without the pins except the S0 trailer (G-1).
* **Refutation section.**  Row 11c literal stays REFUTED, with the
  mechanism (W-D6c) machine-keyed 112/112; re-verified the 72's
  live-row-only location and the "twice +2" census from the sealed JSON
  (Part A); my two fresh instances exhibit the dump channel exactly.
* **Grades/fences/claims table.**  Header (0/2 clean, round-1 verdict
  disclosed) honest; W-D2 row carries the W-r1 regrade parenthetical;
  W-D7 row carries (STK) ∧ clause; (SURV) row records the withdrawal and
  the conjecture-grade lead; LAW-DCX-(m+1) row + F5: UNCHANGED (m = 1
  proved, m ≥ 2 conjecture) ✓.  F1–F7 match the proof bodies (F6 now
  carries the clause + the census denominator).  S11 dispositions match
  the PE1 report's findings one-for-one (with the G-1 caveat below on
  "at every site").
* **No silent RM-GEN row-11c upgrade.**  RMENGINE_2026-08-08.md is
  untouched by 03635d0; its S8 row 11c still reads "HEURISTIC —
  conjecture-supported … NOT derived" (no upgrade).  Cross-note sync
  observation: see N-2.

## Part D — findings (quote-and-classify)

### G-1. JUSTIFICATION GAP — residual unqualified two-sidedness language at two sites; one of them a display PE1-G1 explicitly quoted

Quotes (both byte-identical to the pre-repair text):

> (S0, closing the reconciliation paragraph)  Row 11c as worded is false
> on the full tree and true verbatim on the dump-free principal subtree.

> (W-D6 statement)  Under (H3) with g₀ = 1 (all P_l = e_l): **ĉ_l = c_l
> — the S6.1 floors are exactly the maximal dump-free promotion
> counts.**

Derivation.  "True verbatim" and "exactly the maximal" are attainment
claims; attainment is proved only under (STK) ∧ the law clause (the
greedy maximizer of W-D7(ii) is the only exhibited one, and on
clause-failing rows the dump-free principal Q¹ population is empty on
every probed instance).  W-D6 itself proves only the cap ≤.  PE1-G1
quoted the S0 trailer VERBATIM as an offending display ("the S0
reconciliation sentence and the 'true verbatim on the dump-free
principal subtree' line display no condition at all"); W-r1 pinned the
bolded reconciliation sentence two lines above but left this trailer
unchanged, while S11 records PE1-G1 as "REPAIRED by hypothesis pin …
pinned at … the S0 reconciliation sentence …".  So the PE1-G1 discharge
is incomplete at one of its own quoted sites, plus one uncharged site of
the same shape (the W-D6 gloss).  Mitigation: the immediately preceding
S0 sentence and every graded claim (W-D7(iii), S8(b), claims rows) carry
the pins; no lemma body is affected.  Classification: JUSTIFICATION GAP
(display/scope residual; repair is two sentence-level qualifiers).

### G-2. JUSTIFICATION GAP — the S6 fence still asserts an impossibility meta-claim of the withdrawn genre, over-broad for its displayed evidence

Quote (S6, the g₀ ≥ 2 fence paragraph; byte-identical pre/post repair):

> So no mass-only argument can produce the e₀-divisor; the literal-e₀
> floor is irreducibly a statement about which recycled mass SURVIVES in
> residue (S9).

Derivation.  The displayed evidence (the sealed m = 2 record: live
deficit-1 rows at pool₁ = 2 = e₀ < 4 = P₀, feeds riding recycled dumps)
supports only: DUMP-FREE mass caps carry the P₀ divisor and cannot see
the e₀ boundary.  It does not support the universal "no mass-only
argument can" over dump-AWARE counting arguments — and the note's own
new conjecture-grade lead (EMPTY-(m+1)), stated at (H1)–(H2) with no
g₀ = 1 restriction, is exactly such a route: if proved, it would produce
the literal-e₀-divisor dead-side boundary (c_{m−1} is computed with
e-divisors) by pure tree counting, contradicting this sentence's
universal reading.  The battery is CONSISTENT with that route (path
existence coincides with the e₀-clause on all 412 traced rows including
the four g₀ = 2 towers — re-computed this pass).  "Irreducibly" is the
same ∀-over-arguments shape that PE1-C1 forced out of S9; the repaired
S9 states the fence correctly (scoped to (i), "MEASURED, instance-grade,
not derived", "any proof of (i) there must account for recycled-mass
survival"), but the S6 origin sentence was not harmonized.  Not refuted
by artifacts (unlike PE1-C1) and consumed by nothing graded PROVED
(fence prose feeding the S9 fence citation), hence a gap, not a
critical.  Repair shape: scope it to dump-free/cap arguments and to the
survival direction, or delete the "irreducibly" clause and point at the
S9 rewrite.

### N-1. NOTE — the (SURV) box gloss retains the pre-repair vocabulary

Box line: "liveness = residue survival of the depth-≥ max(k,0)
promotion-profile parts, deadness = their total cancellation."
Mathematically exact (an empty part family sums to 0, so the phrasing is
vacuous-compatible and the paragraph below immediately supplies the
zero-cell facts), but "total cancellation" is the withdrawn claim's
vocabulary and a box-only reader could re-import the cancellation
picture.  Cosmetic.

### N-2. NOTE — cross-note: RMENGINE's own row 11c carries no refutation bracket (outside this note's perimeter)

At HEAD, RMENGINE_2026-08-08.md S8 row 11c reads "HEURISTIC —
conjecture-supported (DCX3 C2/C3 seals, S9 D5, PE census); NOT derived"
with no reference to the stress seal d3950f2/d774ecb that REFUTED the
literal wording.  This note handles the refutation correctly (head, S0,
S8, claims row) and no silent upgrade occurred anywhere; the sync is
RMENGINE's supersession arc's business (the r5 "supersede-at-refutation"
standing rule), flagged here for the orchestrator only.

---

## Verdict block

The W-r1 repair is substantively sound: the withdrawn S9 claim is gone
and its replacement is artifact-accurate (126/126 zero-cell re-computed
from both committed JSONs and re-confirmed by fresh spot runs); the
(EMPTY-(m+1)) lead is honestly conjecture-graded and its W-D4 + W-D6c
reduction is VALID (re-derived); W-D7(iii)'s two directions re-derive
exactly under (STK) ∧ clause and the pin is present at the lemma, S0
(bold), S8(b), S8 close, F6, and the claims row; W-D2(0)'s any-d-cell
argument is correct and F3-free; both disclosures verified in source.
Machine legs reproduce exactly (md5s, read-only re-run, 72-set census,
two fresh spot instances with hand-derivation ties, 4 sealed records
confirmed).  Two justification gaps remain, both prose-level residuals
of the same genre the repair targeted: G-1 — attainment language without
the (STK) ∧ clause qualifier survives at the S0 trailer (a site PE1-G1
explicitly quoted) and in the W-D6 statement gloss; G-2 — the S6 fence's
"no mass-only argument can produce the e₀-divisor / irreducibly …
residue" universal is unsupported by its displayed evidence and now
internally in tension with the note's own (EMPTY-(m+1)) route.  No
critical: nothing false-as-stated survives against the artifacts, and
nothing graded PROVED consumes either residual.

WMULTDCX-PE2 FINDINGS: 0 critical, 2 gaps
VERDICT: GAPS-ONLY
