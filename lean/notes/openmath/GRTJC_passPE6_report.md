# GRTJC pass PE6 — HOSTILE VERIFICATION REPORT (fresh context; fixes nothing)

**Target:** `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md` **at HEAD**, i.e.
after the r5 NOTE-ONLY round (commit `3870bc8`: the §9.5 census remark struck +
restated as the per-alias contribution table, FGMN (a)(b) completed at the
stack displays, "nonzero" at §2.8's RHS display, the header + §10.1 arcs
through PE5 → r5 → "JC-PE6 next"; note **byte-identical `3870bc8` → HEAD**,
verified; `3870bc8` touches ONLY the note, 181 insertions / 11 deletions).
Runners: `grt_jc_checks.py` (r0), `grt_jc_r1_checks.py` (r1),
`grt_jc_r2_checks.py` (r2), instrument `grt_jc_probe.py` — all in
`verification/openmath/`, all BYTE-FROZEN at r5 as claimed (all four md5s at
their sealed values, §M).
**Verifier role:** quote-and-classify only. CRITICAL ERROR = breaks the logical
chain (dependents not checked further); JUSTIFICATION GAP = assume and continue.
Fences and boxes are graded as part of the statement.
**Pass date:** 2026-08-06 wallclock (campaign 2026-08-08). **SIXTH acceptance
attempt** (two consecutive clean passes accept; a clean pass here would START
the count).

## VERDICT

**0 CRITICAL · 1 GAP — NOT CLEAN.** Counter stays **0/2**.

**The r5 diff's substance is exact, everywhere I could machine-check it.** I
re-executed the per-alias contribution table from scratch at `edbb966` and
reproduced **every one of its 18 numbers** — union 144; totals 39/30/2/48/11/
13/30/36; exclusives 26/12/0/32/4/5/9/16; Σ exclusives 104; exactly 40 lines
carrying ≥ 2 aliases; union-minus-`4.8` = 140 — and the four `4.8`-only lines
are exactly **L383, L401, L1782, L1801** with the claimed dispositions (L1782
verified INSIDE the struck r0 JC-BOX-3; L1801 in the live [r1] box; L383/L401
the two group-1 declaration lines), and `Theorem 4.2`'s two hits are exactly
the two pattern displays (L132, L2291) (§A1). The [r5, G-2] consumption
attribution is source-true line by line ((IN-3)(a) at L626/L638 in JC-DOM and
L993/L1005 in G6-1/G6-3; (IN-3)(b) at L627, L968, L1210 + L1247) (§A2). The
m-1 word is correct and I re-derived its warrant — JC-SCAL, this pass's
decorrelated re-derivation, with a fresh numeric leg on 6 rows including both
g_m = 2 rows: the attained set is EXACTLY the nonzero canonical degree-<g_m
representatives, never zero for c ∈ K^*, in fact with line-wise unit 1 (§A4).
The arc-accounting system at HEAD is consistent: all 18 hashes resolve in
`git log` with matching subjects, exactly two CURRENT arc displays (header,
§10.1), both ending "JC-PE6 next", the [r2]..[r5] grade-delta lines present
and true, strike system 112 `~~` tokens / 0 odd paragraphs (= PE5's 108 + the
two r5 strike-pairs) (§A3). Machine legs 4/4: exit 0, 0 violations, r0/r2/
instrument stdout **exactly byte-identical** to the committed artifacts this
run (r1: two wallclock digits), `git status verification/openmath/` clean
(§M). The union grep re-run PE5 asked for: **172 at HEAD**, and every hit-line
added since `edbb966` is r5 record/annotation text or the corrected §0
one-liner — zero new lines stating the refuted content (§A1).

The one gap is r5-bred, inside the [r5, G-2] round-record determination:

* **GAP 1** — r5 re-classified §10.2's [r1]/[r2] stack displays as
  ROUND-RECORDS and installed the completed form as "the CURRENT stack"
  ([r5, G-2] at §10.2), but §0's [r4, G-1] bracket still says, un-annotated,
  that those same displays are "**the current stacks** (§10.2 [r1]/[r2],
  **which supersede this display**)" — both clauses now inverted at HEAD (the
  [r1]/[r2] displays are declared round-records that omit (a)(b), and §0's
  display now carries the completion IN PLACE and is itself live) — while the
  new [r5, G-2] parenthetical asserts those displays are "quoted **as such**
  [as round-records] by later brackets, §0 [r4, G-1] included", which is not
  what [r4, G-1] says. The arc's own convention (the r4 annotation of the
  [r3] block's "returns 0 hits" claim: "[r4 — true at the r3 commit …]")
  annotates dated present-tense claims that later rounds falsify; this one —
  in the exact geography r5 was editing, and the exact clause PE5's GAP 2
  quoted as the authority transfer — received none.

---

## §A WHAT I VERIFIED (the charges, checked to the bottom)

### A1. Charge (1a): the per-alias contribution table — REPRODUCED EXACTLY, all 18 numbers, from my own grep at `edbb966`

Independent script (fresh, not the note's protocol text): extract the note at
`edbb966` via `git show`, substring-match the eight aliases
`(IN-3) | Thm 4.2 | Theorem 4.2 | FGMN | 4.8 | Cor 2.7 | (COORD) | (MULT)`
(the literal closing paren excludes `-B` forms automatically), count
hit-lines; "exclusive" computed exactly as the table defines it (union count
minus the union-with-that-alias-removed count).

| alias | table total / my total | table excl. / my excl. |
|---|---|---|
| (IN-3) | 39 / **39** | 26 / **26** |
| Thm 4.2 | 30 / **30** | 12 / **12** |
| Theorem 4.2 | 2 / **2** | 0 / **0** |
| FGMN | 48 / **48** | 32 / **32** |
| 4.8 | 11 / **11** | 4 / **4** |
| Cor 2.7 | 13 / **13** | 5 / **5** |
| (COORD) | 30 / **30** | 9 / **9** |
| (MULT) | 36 / **36** | 16 / **16** |

Union **144** ✓; Σ exclusives **104** ✓; lines carrying ≥ 2 aliases **40** ✓
(so Σ-exclusives + multi-alias = 144 closes); union-minus-`4.8` **140** ✓.
The `4.8`-only lines are **{383, 401, 1782, 1801}** at `edbb966` — exactly the
table's four, and I verified each disposition at source: L383 (the §S6a
quotation line, whose only swept substring is `Thm 4.8` — "Thm" of "Thm 4.2"
sits on the previous line) and L401 ((d)'s `[Thm 4.8 / Cor 4.9]` tag) are the
census's own group-1 LIVE lines ✓; L1801 sits in JC-BOX-3 [r1] item 1, LIVE
group 10 ✓; **L1782 sits inside the `~~…~~` struck r0 JC-BOX-3** (strike
opens at L1779, closes L1787), STRUCK ✓. `Theorem 4.2`'s two hits are L132
(the r4 disposition-header pattern display) and L2291 (the §9.5 census pattern
display) — "both hits = the two pattern displays" ✓, RECORD ✓. So the r5
restatement's asymmetric verdict (spelled-out variant's half TRUE, bare
numeral's half FALSE) is exactly right, and matches PE5 §A2's own
parenthetical. The struck clause is preserved inside the strike with the
[r5, G-1] pointer bracket; the census's recorded totals 144 = 42/28/74 are
untouched (they come from the same grep, which I reproduced).

**The self-reference discipline holds.** Union at HEAD = **172**; diffing
hit-line CONTENT against `edbb966`: one line replaced (§0's one-liner,
`FGMN ~~(c)~~(d)(e)` → `FGMN (a)(b)~~(c)~~(d)(e)`, still LIVE and stating the
corrected footprint) + 29 added, ALL of them the r5 disposition block, the
table's own rows, the [r5, G-2] brackets, and the §10.1 arc line — census
record under the disclosed conventions. **Zero new lines state
(IN-3)(c)-on-gr, (COORD), (MULT), the Thm-4.2-on-gr_{O[x]} transport, or the
bare "FGMN (c)" alias.** The table's disclosure that its own lines shift any
future count, with re-execution owed at the future committing state, is the
honest fence and matches what I measured.

### A2. Charge (1b): the round-record vs live-display determinations — the DETERMINATION is sound; its RECORD has one leak (GAP 1)

* **§0's one-liner = live display, edited in place** — correct: it is the
  note's front conditionality display ("read before any clause"), and the
  in-place completion `FGMN (a)(b)~~(c)~~(d)(e) CITED` now matches the
  declared (IN-3) block above it and the current stack below. ✓
* **§10.2's r0/[r1]/[r2] displays = round-records, annotated not edited** —
  the classification is genuine (each is round-stamped in its own text: "after
  r1", "for JC-PE3") and the annotate-don't-edit choice is defensible on
  quotation-stability grounds (PE4 GAP 1 and PE5 GAP 2 quote these displays
  verbatim; editing them would corrupt the reports' quotations). ✓
* **The [r5, G-2] consumption attribution, verified at source:** (IN-3)(a)
  consumed at JC-DOM L626 ("By (IN-3)(a) w is multiplicative") + L638 (the
  remark: "which is (IN-3)(a), a literature fact") and at JC-LOC's G6-1 (L993)
  / G6-3 (L1005); (IN-3)(b) at JC-DOM L627, JC-LOC's proof L968, (MULT-B)
  L1210 + its |gr display L1247. Census groups 2/4/6 certify exactly these ✓.
  W-6's [r1] grade line reads "(IN-3)(a)(b)(e) + (IN-5) unchanged" (L612) as
  the bracket claims ✓. ((a) appears in JC-DOM's *proof* once and its
  *remark* once — "JC-DOM's proof twice" is PE5's transcribed wording,
  content-true for the consumption claim; sub-minor, not graded.)
* **The current-stack reading** ("the [r2] tier-split form with FGMN (a)(b) +
  (DMULT-w) on B + Thm 4.8/Cor 4.9 + Cor 2.7") is the true footprint — it is
  exactly the [r2] stack plus the two clauses whose live consumption A2's
  source-check confirms, and "no ranking moves" is right: (a)/(b) were never
  refuted (PE1 §C1, PE4 §A5), and nothing in the [r2] weakest-links order is
  displaced by adding never-refuted package clauses. ✓
* **The leak:** the determination's own record contradicts the un-annotated
  [r4, G-1] pointer at §0 and mischaracterizes it — **GAP 1** below.

### A3. Charge (2): the arc-accounting system at HEAD — CONSISTENT

* **[r5] S-STATUS** (CURRENT): FIVE passes, FIVE rounds ✓. All 18 recorded
  hashes verified in `git log` with matching subjects: seal/verdict
  `6ad01d1`/`8f07904`, PE1 `1a27be3`, r1 `85d5811`/`54904cc` + mini-seal
  `f45b63c`/`66263ce`, PE2 `4a76d52`, r2 `5742e25` + `79611a4`/`db12666`,
  PE3 `e4b6fbf`, r3 `126c33f`, PE4 `d5072b6`, r4 `edbb966`, PE5 `b38f3f4`
  (0 CRITICAL + 2 gaps + 1 minor ✓), instrument `7212e56`/`fc89b03`. ✓
* **Supersession chain:** [r1] struck; [r2]/[r3]/[r4] annotated SUPERSEDED
  with the embedded-ARC reason (the [r4] header's annotation is the r5 edit,
  consistent with the [r2]/[r3] precedents); [r5] CURRENT. Stale
  "JC-PE-n next" pointers live only inside strikes, annotated-superseded
  blocks, or quotation narrative. Exactly two current displays end
  "**JC-PE6 next**" (header L142, §10.1 L2548). ✓
* **§10.1:** the [r4, G-2] arc display struck (not deleted) with the [r5]
  extension per the same convention; the extension's figures match the five
  reports (2C+8G / 9G / 8G / 4G / 2G+1m) ✓; the quoted fragments resolve
  verbatim at their pins ("the r4 diff's mathematics is EXACT" = `b38f3f4`'s
  commit message; "both gaps in the census/stack record surface" = the report
  body) ✓; "[r5] Grade deltas: NONE" present and TRUE (the r5 diff touches no
  grade cell and no measured quantity — verified from the diff itself; commit
  shape note-only) ✓.
* **Strike system:** **112 `~~` tokens at HEAD, 0 paragraphs with an odd
  count** (my own paragraph-split check) = PE5's 108 + the §9.5 remark strike
  + the §10.1 [r4, G-2] display strike. All three r5 keys placed: [r5, G-1]
  ×2 sites + disposition, [r5, G-2] at §0 + §10.2 + disposition, [r5, m-1] at
  §2.8 + disposition. Nothing silently deleted. ✓
* **Hygiene:** counter 0/2 at all 41 occurrences; no gate fires/retires; no
  density/menu/count statement; headline figures unmoved. ✓

### A4. Charge (4): the decorrelated re-derivation — LEMMA JC-SCAL (§2.6), the r5 m-1 fix's warrant, re-derived from REALIZE R1/R2/R3 + a fresh numeric leg

Chosen because it is the ONE lemma the r5 diff newly leans on (the [r5, m-1]
bracket's argument) and no prior pass re-derived it beyond a one-line check
(PE5 §A4: "JC-SCAL via REALIZE ✓").

* **(a) re-derived.** s_{NR}(N) = 0: E | N and s_{NR} is E-periodic with
  s_{NR}(0) = 0 (JC-PER/JC-FIB) ✓. REALIZE expands τ = (c_0,…,c_{g_m−1}) with
  digits at abscissas k_i = s_{NR}(N) + i·e_m = i·e_m and deg child_i <
  deg Φ_m (R1), so on-line slots are exactly {i : c_i ≠ 0} ⊆ [0, g_m), slot-i
  digit the ε-corrected c_i; R3 packs read(N, Λ_N(c)) = c. ✓
* **The m-1 warrant re-derived.** read(N, Λ_N(c)) = 𝑅_N(Λ_N(c))(z̄) = c (§1's
  definitional identity + R3), so c ≠ 0 forces 𝑅_N(Λ_N(c)) ≠ 0 — exactly the
  [r5, m-1] bracket's "packs back to c under R3" argument. And the attained
  set is EXACTLY the nonzero canonical representatives: p ↦ p(z̄) is a
  K_m-linear bijection {deg < g_m} → K (dimension g_m both sides, injective
  since deg ψ_m = g_m), so c ↦ (canonical rep of c) is a bijection
  K^* → {nonzero polys of deg < g_m}, and a fixed unit constant scales that
  set bijectively — the [r4, G-3] parenthetical's mechanism. The iff is
  unaffected (LHS b_×·u·y^δ ≠ 0). ✓ JC-SCAL(c)'s own §2.6 display ("exactly
  𝑅_N(X_N)·{K_m-polynomials of degree < g_m}") quantifies over c ∈ K
  (including 0 ↦ the zero polynomial), so §2.6 needs no "nonzero" — the
  defect was confined to the §2.8 display over K^*, which r5 fixed. ✓
* **Fresh numeric leg** (read-only probe, this pass, in-memory only — nothing
  staged; imports the frozen `grt_jc_probe`/`iterlawn_pe_reimpl`, builds the
  canonical-representative map INDEPENDENTLY by enumerating all K_m-tuples):
  on C2I, C4I (both g_m = 2 rows), C2A, C4H (the e_m = 1 row), C3I, I4C —
  for every c ∈ K^*: 𝑅_N(Λ_N(c)) nonzero **6/6 rows, 0 exceptions**; slots
  ⊆ [0, g_m) ✓; read packs back to c ✓; c ↦ 𝑅 injective ✓; attained set ==
  {nonzero canonical reps} **exactly** ✓; and on all 6 rows the digit dict
  EQUALS the canonical representative (line-wise unit = 1 — sharper than
  JC-SCAL(a)'s "up to one line-wise unit", consistent with JC4's sealed
  "𝑅_N(X_N) == 1 exactly").

### A5. Charge (3): the five reports' unnumbered observations — swept; three dangling items CHECKED, none re-gradeable, none abandoned silently

* **PE1 §C7: the c_val ↔ [ILN]† identification "the note never states".**
  Still unstated at HEAD — §3.3 defines c_val as the read-ratio and asserts
  "By [ILN]† (IN-1, ACCEPTED on exactly this stratum) c_val = c_T" without
  displaying that [ILN]†'s cocycle is definitionally that ratio. **I
  re-verified the tie myself at the source** (`ITERLAWN_PROOF_2026-08-08.md`
  §S0.2: "c_{n+1}(γ,γ′) := val(φ_γ·φ_{γ′}) / val(φ_{γ+γ′})" with
  val = R_{n+1}v, the harness read — the note's c_val verbatim). TRUE;
  cleared by PE1 §C7 and re-affirmed by PE3 §A5; stands as
  cleared-but-unwritten. Not re-graded (no new information; a verifier does
  not re-open cleared material), recorded here so it stops dangling.
* **PE2 §M(e): R1-PSIK-HI's prereg row "for EVERY residue ν ∈ ℤ/E" vs the
  NU_CAP = 8.** Still uncapped in the frozen prereg quote at HEAD (L2101);
  the cap is disclosed in the SAME table's verdict cell ("all E classes per
  row, capped at 8") and in the runner docstring. PE2 weighed it and did not
  number it; stands as disclosed.
* **PE1 §C7: (IN-2) declared but not consumed in §§2–5.** Unchanged at HEAD
  ((IN-2)'s own declaration places its consumption at J-C(i), the last-read
  layer); over-declaration in §0's stack remains safe-direction. Stands.
* **PE3 §A1 / JC-BOX-3 item 2: the printed-source numbering Codex leg.**
  Still owed, still boxed, still honestly displayed — a standing disclosed
  leg, not a dangling defect. (Observation, ungraded: the newly completed
  FGMN entry cites (a)/(b) without pinned theorem numbers; they enter via the
  same §S6a pinned quotation the owed leg covers.)
* **PE4 §A2's borderline STRUCK-vs-RECORD lines** — adopted as convention at
  r4 (census text) ✓; **PE5 §R item 4's "re-run the union grep"** — done,
  §A1. Nothing else in the five reports' unnumbered text is actionable.

---

## GAP 1 — the r5 round-record determination left §0's [r4, G-1] "current stacks / supersede this display" pointer INVERTED and un-annotated, and the new [r5, G-2] parenthetical misdescribes that bracket's citation

**Offending passages (verbatim).** §0, the [r4, G-1] bracket (L513–520), at
HEAD un-annotated:

> What is true, and what the **current stacks** (§10.2 [r1]/[r2], **which
> supersede this display**) say: clause (c)'s content is consumed in this
> note ONLY as (DMULT-w) via JC-LOC …

and §10.2, the [r5, G-2] block (L2624–2627):

> (annotation, not edit: the r0/[r1]/[r2] stack displays above are
> ROUND-RECORDS — each states the stack AS OF its round and **is quoted as
> such by later brackets, §0 [r4, G-1] included** — so their wording stays; …)

**Why this is a gap.** At HEAD the note carries two contradictory "current"
designations for the stack. The [r5, G-2] block declares the [r1]/[r2]
displays ROUND-RECORDS and states "The CURRENT stack is therefore the [r2]
tier-split form with its FGMN entry read as: FGMN (a)(b) + (DMULT-w) …";
§0's own display now "carries the same completion **in place**" and is called
"§0's **live** one-line display" by r5's own text. The [r4, G-1] bracket —
sitting directly under the completed §0 display, in the exact geography r5
edited — still asserts in the present tense that §10.2's [r1]/[r2] are "the
current stacks" and that they "supersede this display": both clauses are now
false at HEAD (those displays omit (a)(b), which is PRECISELY the defect r5
repaired; and the supersession r4 installed was dissolved by r5's in-place
completion). This is the clause PE5's GAP 2 quoted as the authority transfer
("transferring authority to displays that carry the same omission") — r5
repaired the displays' content and the transfer's endpoint, but left the
transfer text itself pointing at declared-round-records under the name
"current". The arc's own convention handles exactly this: when the [r3]
census block's present-tense "returns 0 hits anywhere in the note" was
falsified at r4, it received the in-place annotation "[r4 — true at the r3
commit; …]". No such annotation here. Compounding it, the new [r5, G-2]
parenthetical cites §0 [r4, G-1] as quoting those displays "as such" — as
round-records stating the stack as of their round — which is not what
[r4, G-1] says (it cites them as current and superseding). (A third,
weakest-form site: the §9.5 census group-12 audit line "VALID — the current
stack, which §0's display now points to", L2497 — inside the r4 census
record, which carries an explicit executed-at-`edbb966` pin, so it is
arguably covered; noted, not weighted.) Nothing false is concluded about the
mathematics — the corrected footprint is displayed immediately adjacent at
BOTH sites ([r5, G-2] at §0 sits directly above [r4, G-1]; the CURRENT-stack
display sits in the same §10.2 block) — but the record system's pointer
semantics contradict themselves at HEAD, one round after PE5 flagged the
same bracket. **Classification: JUSTIFICATION GAP** (record/annotation
surface; the same stale-pointer species as PE4 GAP 2, in the r5 diff's own
geography; one dated annotation on [r4, G-1] + one word-level fix in the
[r5, G-2] parenthetical discharge it).

---

## §M MACHINE LEG (mandatory; re-run this pass, nothing edited)

Nothing in the repo was modified by this pass except this report file. All
runs from the working tree at HEAD. **All four legs RUN** (no NOT-RUN legs).

### (a) Seals, md5s, commit shape

* Note **byte-identical** at `3870bc8` and HEAD (`git diff` empty); `3870bc8`
  touches ONLY the note (181 insertions / 11 deletions, no `verification/`
  file, no `.lean`) — "batteries + instrument BYTE-FROZEN" literally true. ✓
* md5s at HEAD, all at their sealed values: r0
  `adb555e1134d3ae0b0174d62e8b3446c`, r1
  `7f896bfa27d06158f95c5987c7299770`, r2
  `c02bf06029a72259512ea005bd2562fd`, instrument
  `03811b695cf7aa1bd5b52d5b0cd8bcd6`. ✓

### (b) The three batteries + instrument — all reproduced, exit 0

* **r0** `grt_jc_checks.py`: exit **0**, 2.0 s, 0 violations, silent teeth
  NONE; stdout **exactly byte-identical** to the committed output this run
  (0-line diff). 8,566 samples / 10 families / 1,054 firings / cyclic 6/14/9.
* **r1** `grt_jc_r1_checks.py`: exit **0**, 2.6 s, 0 violations; stdout
  differs on TWO per-row wallclock digits only (C3A 0.4→0.3, C3G 0.7→0.6).
  R1-DMULT 2,784, R1-COB 2,607 (869 pairs), R1-UNIT 869/0/0/0, PSIK 197/197,
  TOOTH-ROW 145, teeth 1,885 — 10,330 + 145 as the [r2, G-8] decomposition
  states.
* **r2** `grt_jc_r2_checks.py`: exit **0**, 7.4 s, 0 violations; stdout
  **exactly byte-identical**. 3,655 rows, U1 261/261, U2 261/261, dense
  bilinear content on exactly C2I/C4I.
* **instrument** `grt_jc_probe.py`: exit **0**, 18.3 s, total violations 0;
  stdout **exactly byte-identical** (0-line diff — PE5 saw four wallclock
  digits; this run none). P1-RAW 134 == 134, H-B 215 / H-C 73 / H-D 138 of
  669, MT2 14/6/9 — the note's figures.
* `git status verification/openmath/` after all four re-runs: **clean** —
  every committed JSON artifact reproduced byte-for-byte. ✓

### (c) The r5-added figures — every one checked this pass

* Per-alias table: **18/18 numbers reproduced** by independent grep at
  `edbb966`; the four `4.8`-only line numbers and dispositions verified at
  source; `Theorem 4.2` = the two pattern displays ✓ (§A1).
* Union at HEAD 172; added hit-lines all census-record/annotation; zero new
  refuted-content lines ✓ (§A1).
* Strike census 112 / 0 odd ✓; [r5] bracket keys all placed ✓ (§A3).
* Arc hashes 18/18 ✓; grade-deltas [r5] TRUE ✓ (§A3).
* m-1's warrant: JC-SCAL probe, 6 rows, 0 exceptions ✓ (§A4).

---

## §C WHAT SURVIVED THE PASS (beyond §A; re-checked, no defect found)

1. **The [r5] S-STATUS + disposition block** — every figure, hash, and quoted
   fragment resolves (PE5's verdict figures; the census claims transcribed
   with unit and commit; "16/16 hashes" as PE5 stated). The compressed
   "re-ran … byte-identical" phrasing (true of the JSON artifacts; stdout had
   wallclock-digit diffs at PE5) repeats the r4 block's wording that PE5
   already reviewed without objection — species cleared, not re-graded.
2. **The [r5, G-1] restatement** — census-not-prose applied to the remark
   itself; the struck clause preserved verbatim inside the strike; the
   asymmetric verdict (spelled-out TRUE / bare numeral FALSE) machine-exact;
   the self-reference fence honest.
3. **The [r5, m-1] bracket** — argument sound (§A4), "the [r4, G-3] bracket
   below already uses the nonzero form" verified at L829, iff untouched.
4. **The [r5, G-2] completion's CONTENT** — the completed FGMN entry is the
   true footprint at both sites; "nothing false was concluded" and "no
   ranking moves" both check out (§A2). Only its pointer RECORD leaks (GAP 1).
5. **Header/status hygiene** — counter 0/2 at all 41 occurrences; no gate
   fires/retires; no density/menu/count statement; JC-BOX-2/8(i) residues
   still displayed as having no machine leg on any runner.
6. **The dangling-observation sweep** (§A5) — all three standing items
   verified at source this pass (the ITERLAWN §S0.2 tie independently
   re-confirmed); none silently abandoned, none re-gradeable.

---

## §R RECOMMENDATION

**Not clean; 0 CRITICAL, 1 gap; counter stays 0/2.** The r5 diff's substance
is exact — the per-alias table is the census-grade form the [r3, G-2] species
demanded and reproduces to the last digit, the FGMN completion states the
true footprint, and the m-1 word is warranted by a lemma that survives
decorrelated re-derivation with margin. The one gap is a two-edit repair:

1. Annotate §0's [r4, G-1] pointer with a dated bracket ("[r6 — true at the
   r4/edbb966 state; since r5 those displays are round-records and the
   current stack is §10.2 [r5, G-2]'s completed form; §0's display above
   carries it in place]"), and
2. fix the [r5, G-2] parenthetical's "quoted as such" characterization to
   what [r4, G-1] actually does (cites their content as of r4).

PE7 should verify those two edits, re-run the union grep at its own state,
and — if clean — START the acceptance count. The weakest mathematical links
remain §10.2 [r2]'s ranking, headed by (DMULT-w) + W-1's transport; nothing
found this pass moves that ranking.

— GRTJC pass PE6, hostile verifier unit (fresh context), fixes nothing.
