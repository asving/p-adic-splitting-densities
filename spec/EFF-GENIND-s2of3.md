# EFF-GENIND-s2of3 — CANONICAL EFFECTIVE-SPECIFICATION SHARD

**COMPILED-BY: opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). CODEX CROSS-READ OWED (post-reset).**

## 1. Shard header

**Source note:** `lean/notes/openmath/GENIND_PROOF_2026-08-08.md` (3872 lines).

**HOME range:** source lines 1349–2551 inclusive (§S8 the six honest boxes + §S9 consumers, the proposed annex, downstream, and the conditionality stack + §S10 the sealed battery, its roster, its pre-seal disclosures and its eleven preregistered predictions + §S11 the verdict + §S12–§S16 the five repair records r2–r6 + the post-PE7 dated corrections + the dated acceptance record). Earlier text (lines 1–1348, the mathematics) and later text (ANNEX R, the supplier-movement record, ANNEX R — r1, the two 2026-08-12 dated corrections) are used ONLY to resolve material homed in that range.

**HEAD blob hash:** `8ef694fefc24c5fb07e4e80c306ff2136c914b61` (clean in the working tree; last touched by commit `5e33b01f`).

**Compilation context:** `spec/EFF_TEMPLATE_v2.md` at its current HEAD (v2 rules 1–10; v3 rules 11–28). Temporary IDs `EFF.GENIND.s2of3.<nn>`.

**GENRE: TAG-SPARSE PROSE RECORD.** `grep -c '\tag{'` inside this range = **0** (all 13 of the note's tags sit at lines 3333–3837, shard 3). This shard's genre is different from shard 1's in kind, not only in degree: **it is overwhelmingly RECORD material** — boxes, pins, predictions, verdicts, repair records, audits of records — and the v3 type enum's record members (`preregistration`, `run-record`, `instrument-record`, `supplier-finding`, `changes-record`, `SERIES`) carry almost all of it. The one Markdown table in the whole note (§S16's per-supplier fired-clause table) is homed here. §6 is the mandatory BOUNDARY SELF-AUDIT.

**SERIES declared in this shard (rule 28).** Three chronological arcs run through the range and must be reconstructible in order by a merge:
* **SERIES REPAIR-ARC** — the five dated repair records r2…r6, entries at `.31`, `.36`, `.44`, `.54`, `.61`, each with its own grade close; continued (outside this shard) by the post-PE7 dated corrections (`.69`–`.71`) and closed by the dated acceptance record (`.72`).
* **SERIES RECORD-INTEGRITY** — the note's own named chain of five consecutive record-integrity findings, PE2-G2 → PE3-G1 → PE4-G1 → PE5-G1 → PE6-G1, entries at `.33`, `.38`, `.46`, `.55`, `.61`. **This series is the note's diagnosis of itself** and its members are NOT the same set as REPAIR-ARC's.
* **SERIES GENH4-PIN** — the four dated appends on §S9.3's GENH4 bullet (`[r3]`, `[r4]`, `[r5]`, `[r6]`), all inside one unit (`.18`), recorded in order with a TERMINAL marker.

### Governing effective-text record

Identical to shard 1's (the five records (i)–(v) at `spec/EFF-GENIND-s1of3.md` §1), and re-derived here from the two records that sit INSIDE this range:

**(i) The body is frozen at acceptance** — lines 2510–2523, homed here at `.72`:

> “**GENIND IS ACCEPTED 2/2; the text is FROZEN — dated appends only.** … PE8 re-verified the body's byte-freeze (lines 1–2464 md5 14fa6afc == 993935d, the post-PE7 annex purely additive).”

**(ii) Every repair round r2–r6 was applied IN PLACE and tagged.** Each record says so of itself, and each names which EARLIER record it corrects in place. §S13's heading (line 1833) is the template: “appended at r3 — S11 stays frozen at its seal, S12 corrected in place where its own sentence was the finding”. **Consequence for this shard specifically: the repair records correct EACH OTHER, so a `[rN]` bracket inside a record is a supersession of a record, not of mathematics.** §S11 is the one span every record declares frozen at its seal.

**(iii) The post-PE7 dated corrections are additive and name their targets** — lines 2470–2477:

> “Three wording corrections to the r6 record, each original standing in place as a dated record per the note's convention; no count law, theorem clause, consumption verdict, or frozen number is touched by this annex, and the note text above this annex is byte-identical to 993935d.”

**EFFECTIVE TEXT FOR THIS SHARD = lines 1349–2551 exactly as written (r2–r6 already landed, each correcting the earlier records in place), READ AS CORRECTED by the out-of-range dated appends wherever they name an in-range sentence.** Four such sources land here (§7).

### FREEZE PREDICATES (rule 21 — four independent freezes in this range)

1. **VERDICT-FREEZE (the §S11 seal).** Predicate: §S11 is frozen at its seal and no repair round may edit it. Quoted five times, once per record; §S12's heading is the first (line 1770): “appended at r2 — S11 above stays frozen at its seal”. Pin: seal commit `c3212cc` ✓.
2. **BODY TEXT-FREEZE (acceptance).** Lines 1–2464, md5 `14fa6afc` == `993935d` ✓ (`.72`).
3. **INSTRUMENT-FREEZE (artifact seal).** The sealed runner `genind_checks.py` md5 `e7ca150b` plus every committed leg, re-enumerated by md5 at each round's commit: **13 md5s at r5** (`.60`), **16 md5s + 5 GT-PIN suppliers at r6** (`.68`). The enumeration GROWS as verifier legs land; the frozen SET is different at each round and the note lists it each time rather than saying “unchanged”.
4. **REPORT-FREEZE (other authors' artifacts).** Predicate: verifier reports are their authors' committed artifacts and are never edited by this note, even when they carry a defect this note discloses. Quoted at `.58` (“the two verifier reports are their authors' committed artifacts and stay untouched, their shared typo disclosed here”) and at ANNEX R R6.1 (shard 3, on the PE8 report). **This is a distinct freeze from (1)–(3): it governs files this note does not own.**

### Scope split (rules 7 and 17 — three predicates)

**A. ABSORPTION / supply SET.** This shard's supply is not mathematics but STATUS: what is proved, at what grade, on which pins, against which instrument, with which findings outstanding. Its governing sentence is §S9.3's close (lines 1603–1608), homed here at `.20`:

> “**One line: THEOREM GENIND.A(I,II,IV) + GENIND.C's hypothesis set =
> {W-11, W-12.A/L0/L1, HEX3, HMENU3 @ pins + this note's lemmas};
> GENIND.A(III) adds the S4.1 ledger-compression honesty; THEOREM
> GENIND.B adds [GENIND-H] as its displayed hypothesis; the FULL
> uniformity consequence consumes THEOREM W-12.D @ pin. No axiom, no
> weld face inside any count law; grade = composition 0/2.**”

(The trailing “grade = composition 0/2” is superseded by `.72`; see `.20`.)

**B. APPEND / consumption PROTOCOL scope.** **NO-APPENDS, declared and repeatedly honoured.** §S9.1's heading (line 1429): “Proposed annex to W12-BOX-1 / the [W12-H] box (**text offered; W12_PROOF not edited**)”. Every repair record's closing paragraph re-asserts that no sealed or committed artifact was touched, and §S16's Arc states the round's edit scope enumeratively (lines 2340–2344): “the files edited this round are exactly one (this note); the sites edited are exactly five … the S9.3 bullets edited are exactly seven”.

**C. INBOUND corrections RECEIVED.** This is the shard where predicate C does most of its work. Two channels:
* **In-house hostile passes** PE2…PE8 (five landing as r2–r6 records here, two as the post-PE7/acceptance records) — including the note's own SERIES RECORD-INTEGRITY, five consecutive findings that a repo-checkable factual sentence in a repair record was false against the repo.
* **Supplier movements** — §S16's table records seven suppliers whose HEADs moved past this note's pins (W-12 across a repaired CRITICAL; HEX3 two rounds; HMENU3 accepted + ANNEX A; W-11 accepted; QSCOUT22 verdict + annex; GENH4 an annex arc) plus one that did not (GENHN), plus one row (HE7) recorded to make the disclosure total.

### Resolution rules applied

1. Lines 1349–2551 supply the HOME material.
2. `[r2]`…`[r6]` brackets inside the range are ALREADY-LANDED text; **within this shard they most often correct an EARLIER RECORD**, and the corrected record's false original is quoted in place as a dated record.
3. **§S11 is never edited.** Where a later round bears on a §S11 number, it does so by a record elsewhere (e.g. §S14 C12 re-verifies §S11's totals by an isolated re-run) — never by an edit. Carried at `.28`/`.29` as CONDITIONALITY.
4. **The dated acceptance record's PE8-m1 cure (lines 2528–2543) supersedes TWO frozen arc lines by name** — the header arc line (shard 1's `.01`) and GENIND-BOX-5's arc close (this shard's `.05`). Both are carried with the cure quoted.
5. **ANNEX R (shard 3) riders in-range material at three points:** R1.4's enumeration replaces a non-enumerative sentence about committed displays (touching `.05`/GENIND-BOX-4's pricing sentence, which R1.4 explicitly leaves STANDING); R6.1's notice names a defect in the **PE8 acceptance report**, an artifact this shard's `.72` cites; and the ANNEX R head re-verifies this shard's body freeze.
6. **The dated supplier-movement record (shard 3) discharges an obligation stated in this range** — §S16 row 6's “execution disclosure owed at the next dated append” (`.62`) — and completes the GENHN consumed-surface inventory PE7-m2 opened here (`.70`).
7. **The 2026-08-12 dated corrections (shard 3) are homed there**; they touch this shard only by re-conditioning material shard 1 homes.
8. Out-of-range statements are NOT emitted here merely because they resolve in-range text.
9. External repo records (pass reports, `verification/openmath/*`, supplier notes, ledger commits) are **reading notes only**.

### Quotation and table discipline

CANONICAL STATEMENTs are verbatim or explicitly `[ASSEMBLED]`; truncation is marked `…`. **§S16's per-supplier fired-clause table is a Markdown table in the source and is transcribed as a table, flagged `[TABLE]`, never prosified** (rule 5); it is not an ASCII fixed-width block, so rule 14's double-emission does not fire. **§S14's two sweep inventories (15 window-site classes; 14 claim groups) are numbered/bulleted lists in the source, not tables** — they are emitted as statement units with `[TABLE]` transcriptions of their classification structure, and each carries the mandatory arithmetic audit of its own count line (rule 22). Compiler-authored ledgers (§3, §4, §5) are flagged `[TABLE — compiler ledger]`.

---

## 2. Statement inventory

### EFF.GENIND.s2of3.01  [fence]

**CANONICAL STATEMENT:** FORM: bulleted display (§S8's first honest box). verbatim, lines 1351–1356.

> “* **GENIND-BOX-1 ([GENIND-H] itself).** The composite-stage laws are
>   OPEN at every genre; GENIND-5 is a CANDIDATE with its obstruction
>   displayed (OB-a..d). No count law at order ≥ 2 is claimed proved.
>   THEOREM GENIND.B is a REDUCTION; its unconditional content at
>   n ≥ 4 is exactly the simple-stage layer (GENIND.C) + the criterion
>   + the opening-mass laws.”

**CONDITIONALITY:** Standing and never edited. **This is the note's single most important honesty fence** and the sentence a chapter cut must carry with any GENIND.B claim: *THEOREM GENIND.B is a REDUCTION*. Two later movements sharpen, not weaken, it: the n ≥ 8 conditionality gains two conjuncts (shard 3's supplier-movement record), and the CS-drain rate gains a per-genre obligation ((CS-1Q), shard 3) — both increase what is open, neither touches this text.

**DERIVATION:** Not a mathematical unit; a scope fence over shard 1's `.13`–`.16`, `.43`, `.46`, `.70`, `.72`.

**RESOLUTION TRACE:** statement lines 1351–1356. correction sites: none.

**TEETH:** NONE — a fence. Its content is precisely what NO tooth can establish.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:[W12-H]` — count **17**.

---

### EFF.GENIND.s2of3.02  [fence]

**CANONICAL STATEMENT:** FORM: bulleted display. verbatim, lines 1357–1360.

> “* **GENIND-BOX-2 (GENIND-3's ledger compression).** The β-transport
>   is proved as a schema with per-route ledgers compressed (S4.1's
>   honesty note); hostile targets named there. The n = 4, 5 pointwise
>   machine families are the compensating instrument.”

**CONDITIONALITY:** Standing. **Two of the three hostile targets it points at subsequently FIRED** — target (b) at PE3 (the capped-window correction) and target (a) at the Codex ratification (the unit-pivot gap, ANNEX R R2). The box's own text is not edited by either; the fires are recorded at §S13 (`.37`) and, out of range, at ANNEX R R2 (shard 3).

**DERIVATION:** Not a mathematical unit; a compression-debt box over shard 1's `.24`/`.26`.

**RESOLUTION TRACE:** statement lines 1357–1360. correction sites: none in range; the fired targets at 1846–1869 (in range, `.37`) and 2779–2852 (shard 3).

**TEETH:** the box NAMES its compensating instrument — GT-BETA at n = 4, 5 — and thereby scopes its own guarantee. Disposition: `disclosed non-repair` above n = 5 (the compensating instrument does not reach there).

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:HEX3-BOX-2` — count **4**.

---

### EFF.GENIND.s2of3.03  [fence]

**CANONICAL STATEMENT:** FORM: bulleted display. verbatim, lines 1361–1366.

> “* **GENIND-BOX-3 (d ≥ 2 and prime-power coverage).** The battery
>   exercises d = 1 clusters at prime q only; general d ≥ 2 (and the
>   Q = q^d letter spaces) rests on the proofs' Q-uniformity (the
>   arguments never use d = 1) — machine-uncorroborated here beyond the
>   w12-sealed order-1 instances; prime-power q rows are carried by the
>   supplier batteries (HEX3/HMENU3 up to q = 27).”

**CONDITIONALITY:** Standing, with its hedge intact. §S14 claim group **C11** re-audits it and keeps it AS HEDGED (`.49`): “a proof-audit claim, already disclosed in the same box as machine-uncorroborated beyond the w12 order-1 instances; PE4 §2 left it as disclosed. KEPT with its hedge.” **Partly overtaken from outside the range:** the dated acceptance record (`.72`) reports PE8's route as “non-prime base q ∈ {4, 8, 9} + the n = 12 double-composite”, and PE7's as “first d ≥ 2 + n = 10 route” — i.e. **two hostile passes subsequently exercised exactly the two uncorroborated directions this box names, and the box is not edited.** Tagged `STALE-SELF-DESCRIPTION` (rule 26) in its coverage clause: “The battery exercises d = 1 clusters at prime q only” remains true of *this note's own battery* and is no longer true of the arc's evidence base.

**DERIVATION:** Not a mathematical unit; a coverage box.

**RESOLUTION TRACE:** statement lines 1361–1366. correction sites: none (never edited); re-audit at 2115–2118 (§S14 C11, `.49`); overtaken by 2513–2520 (`.72`).

**TEETH:** `signed vacuity disclosure` in the d ≥ 2 and prime-power directions for the note's own battery; **foreign-note evidence** (PE7's and PE8's committed legs `genind_pe7_fresh.*` and `genind_pe8_fresh.*`, both verified to EXIST on disk ✓) supplies the missing coverage without the box recording it.

---

### EFF.GENIND.s2of3.04  [fence]

**CANONICAL STATEMENT:** FORM: bulleted display. verbatim, lines 1367–1372.

> “* **GENIND-BOX-4 (drainage bound at n ≥ 4).** GENIND.C's vanishing
>   argument for the simple slice is an induction whose β-term
>   bookkeeping is displayed, not expanded per genre; its n ≤ 3
>   instances are the proved HEX3.B/W-11(iii). The battery checks the
>   EXACT first-step recursion at n = 4, 5, which is stronger at those
>   degrees than the bound it feeds.”

**CONDITIONALITY:** **This box priced the compression; ANNEX R R1 found something sharper.** R1.0's own words (lines 2599–2602, shard 3): “GENIND-BOX-4 priced the bookkeeping compression; the finding is sharper: a consumed HYPOTHESIS component absent from the display.” And R1.4 (lines 2766–2771, shard 3) records precisely what survives and what is cured:

> “GENIND-BOX-4's pricing of the
> per-genre expansion STANDS for what remains compressed (the
> per-genre prefactor ledgers); the box's sharpened defect — the
> hypothesis-WIRING gap Codex named — is cured by this section.”

**SUPERSESSION KIND:** (received) `scope-pin` — the box is split into a part that STANDS (per-genre prefactor ledgers) and a part CURED (the hypothesis wiring). No wording is replaced.

**CHAIN:** the sealed box → ANNEX R R1.0's sharpening (a hypothesis component, not a bookkeeping compression) → R1.4's split — **TERMINAL: the box stands for the per-genre prefactor ledgers only; the wiring gap is cured by (A2-RATE) + GENIND-C1 + GENIND.C′.**

**DERIVATION:** Not a mathematical unit; a compression-debt box over shard 1's `.45`/`.46`.

**RESOLUTION TRACE:** statement lines 1367–1372. correction sites: 2599–2604 and 2754–2777 (ANNEX R R1.0/R1.4, shard 3).

**TEETH:** the box names its own compensating fact — the battery's EXACT first-step recursion at n = 4, 5 is stronger than the bound. Disposition: `accepted-with-decorrelation-supplied` at n ≤ 5; `signed vacuity disclosure` above.

**NEAR-MISS (rule 15):** `W-11(iii)` — fixed-string count **0** in `W11_PROOF_2026-08-08.md`; the file uses the bare clause label `(iii)` (occurrences at `:21`, `:74`, `:97`). Referent is W-11's clause (iii) (the drainage clause); verified designation `THEOREM W-11` count **3**. Carried descriptively.
XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:THEOREM HEX3.B` — count **8**.

---

### EFF.GENIND.s2of3.05  [changes-record]

**CANONICAL STATEMENT:** FORM: bulleted display (§S8's grade box, the note's longest single bullet — the full PE1…PE6 arc). verbatim, lines 1373–1420.

> “* **GENIND-BOX-5 (grades).** 0/2; PE1 (hostile, fresh context)
>   adjudicated 0C + 3G + 4m, all three GAPs at the single GENIND.B ↔
>   [GENIND-H] seam, r1 repairs applied in place ([r1] tags; report
>   @ 4259a93; runner + artifacts byte-frozen, untouched); PE2
>   (hostile, fresh context, n = 6 route) adjudicated 0C + 2G + 1m
>   (report @ 50db400), r2 repairs applied in place ([r2] tags:
>   GENIND-6 + re-pin/disclosure + granularity; sealed runner +
>   artifacts byte-frozen, untouched; the r2 machine support is the
>   ADDITIVE leg genindr2_supp.py, §S12); PE3 (hostile, fresh context,
>   first n ≥ 7 route) adjudicated 0C + 2G + 4m (report @ f89b565), r3
>   repairs applied in place ([r3] tags: the capped M_l window display
>   + the GENH4 re-pin with the pin-check violation disclosed + the
>   four MINOR records; sealed runner + artifacts + the r2 supp leg
>   byte-frozen, untouched; PE3's fresh leg genind_pe3_fresh.* is the
>   verifier's committed artifact, cited, not this note's); PE4
>   (hostile, fresh context, first mixed-cap + n = 8 route) adjudicated
>   0C + 2G + 0m (report @ ade9bac), r4 repairs applied in place AS A
>   FULL-SWEEP AUDIT (§S14; [r4] tags: step (1) rewritten to the capped
>   content window + the regime inventory restated; sealed runner +
>   artifacts + the r2 supp leg byte-frozen, untouched; no r4 machine
>   leg — the machine evidence cited is PE4's committed fresh leg
>   genind_pe4_fresh.*, the verifier's artifact, cited, not this
>   note's); PE5 (hostile, fresh context, first n ≥ 9 route +
>   the same-side co-children leg + the steeper-piece scan)
>   adjudicated 0C + 1G + 2m (report @ bd9bce1), r5 repairs applied
>   in place AS THE STANDING-RULE ROUND (§S15; [r5] tags: the f-first
>   entry law + the S14 coverage rescopes + the step-(1) same-side
>   composite case + the universal-sentence sweep + the PE4-results
>   pin correction; sealed runner + artifacts + all prior legs
>   byte-frozen, untouched; no r5 machine leg — the machine evidence
>   cited is PE5's committed fresh leg genind_pe5_fresh.*, the
>   verifier's artifact, cited, not this note's); PE6 (hostile, fresh
>   context, the same-side f-first genre realized corpus-first +
>   isolated re-runs of ALL FIVE committed legs) adjudicated
>   0C + 1G + 1m (report @ 265a562/ad1bd98/f7f45f1), r6 repairs
>   applied in place AS THE SUPPLIER RE-PIN ROUND (§S16; [r6] tags:
>   the S9.3 stack re-pinned at current supplier HEADs with the
>   per-supplier fired-clause table + C14 corrected in place + three
>   dated appends; sealed runner + artifacts + all prior legs
>   byte-frozen, untouched; no r6 machine leg — the machine evidence
>   cited is PE6's committed fresh leg genind_pe6_fresh.*, the
>   verifier's artifact, cited, not this note's) — the clean count
>   has NOT started;
>   every supplier consumed at the pins of S10's PIN family; the
>   full-degree corollary inherits the MINIMUM grade over
>   {W-11, W-12, HEX3, HMENU3 arcs, this note, and — at n ≥ 4 —
>   [GENIND-H] which is OPEN}: i.e. the uniformity theorem at n ≥ 4 is
>   a CONDITIONAL STRUCTURE, displayed, not a result.”

**CONDITIONALITY:** **The arc close is superseded by name.** The dated acceptance record's PE8-m1 cure (lines 2537–2538) quotes it verbatim: “GENIND-BOX-5 arc close, L1414–1415: "— the clean count has NOT started;" — superseded the same way”, i.e. 0/2 → 1/2 (PE7 CLEAN 380bc66) → **2/2 (PE8 CLEAN 3f5bafc), ACCEPTED**. The two closing sentences (minimum-grade inheritance; “a CONDITIONAL STRUCTURE, displayed, not a result”) are **NOT** superseded and remain the operative reading — indeed `.72` re-asserts the second: “[GENIND-H] at n ≥ 4 remains the displayed OPEN box — the acceptance freezes the reduction and its record, not the box.”

**SUPERSESSION KIND:** `counter re-reading` (the clean counter, and only the counter).

**CHAIN:** the frozen arc close (as of r6) → PE7 CLEAN `380bc66` (→ 1/2) → post-PE7 dated corrections `b653858` → PE8 CLEAN `3f5bafc` (→ 2/2) → **PE8-m1 cure at lines 2537–2538 — TERMINAL.** SERIES REPAIR-ARC: this unit is the arc's *summary*, not an entry; the entries are `.31`, `.36`, `.44`, `.54`, `.61`.

**ARITHMETIC AUDIT (compiler-computed, on the finding tallies):** PE1 3G+4m, PE2 2G+1m, PE3 2G+4m, PE4 2G+0m, PE5 1G+2m, PE6 1G+1m — **0 CRITICAL at every one of the six**, total 11 GAP + 12 MINOR across PE1–PE6; adding PE7 (0G+3m) and PE8 (0G+1m) from `.72` gives **11 GAP + 16 MINOR + 0 CRITICAL over eight hostile passes**. The GAP count falls monotonically 3, 2, 2, 2, 1, 1, 0, 0 ✓ — a genuinely monotone arc, matching the note's own “the monotone arc” language at §S14 leg 3 (`.52`), which however describes the *grade* line as monotone, not the finding counts.

**PIN VERIFICATION:** `4259a93` ✓, `50db400` ✓, `f89b565` ✓, `ade9bac` ✓, `bd9bce1` ✓, `265a562` ✓, `ad1bd98` ✓, `f7f45f1` ✓ — 8/8 commits. Named legs `genindr2_supp.py`, `genind_pe3_fresh.*`, `genind_pe4_fresh.*`, `genind_pe5_fresh.*`, `genind_pe6_fresh.*` all EXIST on disk ✓.

**DERIVATION:** Not a mathematical unit; the arc of record.

**RESOLUTION TRACE:** statement lines 1373–1420. correction sites: 2528–2543 (the PE8-m1 cure, `.73`).

**TEETH:** the per-round attributions are report-pinned; **the “sealed runner + artifacts byte-frozen, untouched” clause repeated at every round is the instrument-freeze predicate**, enumerated by md5 at `.60` and `.68`. Disposition: `in-house hostile pass` ×6 (plus 2 outside the range).

---

### EFF.GENIND.s2of3.06  [convention]

**CANONICAL STATEMENT:** FORM: bulleted display. verbatim, lines 1421–1425.

> “* **GENIND-BOX-6 (conventions).** The conservative drain convention
>   as at HEX3/HMENU3 (v(a₀) ≥ N exits; no tail certification); the
>   reader-reimplementation seams (W10-BOX-3 lineage) inherited; the
>   n = 3 control ties to the committed hex3 JSON mitigate; oracle
>   mixed-characteristic only.”

**CONDITIONALITY:** Standing. **The reader-reimplementation seam is the deepest methodological caveat in the note**: the battery's reader is fresh same-session code (`.21`), so an error shared between the reader and the note's own mechanics would be invisible to every family except GT-N3TIE (which ties to a foreign committed artifact) and GT-ORACLE (which is mechanism-free). The box names both mitigations.

**DERIVATION:** Not a mathematical unit; a convention/seam declaration.

**RESOLUTION TRACE:** statement lines 1421–1425. correction sites: none.

**TEETH:** the box IS a statement about the teeth's blind spot. Disposition: `signed vacuity disclosure` for the reimplementation seam, with two named mitigations (GT-N3TIE foreign tie; GT-ORACLE mechanism-free).

XREF: `lean/notes/openmath/W10_PROOF_2026-08-08.md:W10-BOX-3` — count **1**. (The designation is a lineage pointer; the target note is not in §S9.3's conditionality stack, so no pin is tracked for it — recorded at §8, defect 1.)
XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:HEX3-BOX-1` — count **11**; the conservative-drain convention this box inherits is the same one whose tail-σ residue is HEX3-BOX-1 (ledger **HYP.137**; see `.11`).

---
### EFF.GENIND.s2of3.07  [scope-record]

**CANONICAL STATEMENT:** FORM: display (blockquote, §S9.1's offered annex text) under a heading that is itself load-bearing. verbatim, lines 1429–1443.

> “### S9.1 Proposed annex to W12-BOX-1 / the [W12-H] box (text offered; W12_PROOF not edited)
>
> > **[BOX-1 ANNEX, 2026-08-08, GENIND]** The orders-≥2 program now has
> > its INDUCTION: THEOREM GENIND.B reduces (hMenu-n)+(hExhaust-n) for
> > ALL n to the per-genre composite-stage package {(CS-1) transport
> > (ragged-window-corrected), (CS-2) stage bracket (mass-normalized),
> > (CS-3) = (H-e), (CS-EXACT) exact per-stratum laws [r1]} — with the
> > two-species
> > scaffold (α-bracket (Q−1)Q^{(m(m−1)/2+1)μ−1}, β partition-product
> > transport), the simple-stage layer, and the criterion "composite
> > stages ⟺ some stage carries ≥ 4 keys ⟺ n ≥ 4" PROVED
> > (GENIND_PROOF_2026-08-08.md; sealed battery at n = 4, 5, both
> > characteristics). The (2,2) stage's fibration + node + ℤ/2 slot
> > grading are PROVED (LEMMA GENIND-4); the stage law is CANDIDATE
> > GENIND-5, boxed at (OB-a)/(OB-b)/(H-e).”

**CONDITIONALITY:** **OFFERED, NOT LANDED** — the heading says so and is header predicate B's second governing quote. **The offered text is now partly STALE and was never updated**: it lists the criterion as “⟺ n ≥ 4” without ANNEX R R5's degree-level pin, and its four-clause package predates the (CS-1Q) split. Tagged `STALE-SELF-DESCRIPTION` (rule 26) — the offered text is a frozen proposal, not a live claim, and nothing corrects it because nothing consumed it.

**DERIVATION:** Not a mathematical unit; an offered annex.

**RESOLUTION TRACE:** statement lines 1429–1443. correction sites: none. Overtaken (not corrected) at 2897–2959 (R4/R5, shard 3) and 3592–3722 (the (CS-1Q) upgrade, shard 3).

**TEETH:** NONE — offered text.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:W12-BOX-1` — count **10**; `[W12-H]` — count **17**.

---

### EFF.GENIND.s2of3.08  [scope-record]

**CANONICAL STATEMENT:** FORM: numbered display (§S9.2's downstream list). verbatim, lines 1445–1462.

> “### S9.2 Downstream
>
> 1. **QSCOUT22** — S7.3's falsifiable predictions are keyed to its
>    GENRE-E table; a confirmed table upgrades GENIND-5 from candidate
>    to corroborated-candidate (proof still owed at the boxes).
> 2. **The [GENIND-H] closure program** — per-genre units: (2,2)-E
>    first (GENIND-5's obstruction list is the work order), then
>    (2,2)-F (K = F_{q²}), then the n = 5 embedded genres (S5.3's
>    grammar), each consuming W-9/J-D0/JC-LOAD as S7.1 displays.
> 3. **W-13/W-14 naming** — the per-degree instances of GENIND.B at
>    n = 4, 5 fire as soon as their [GENIND-H] genres close; no other
>    degree-specific work remains (the scaffold is degree-uniform).
> 4. **Phase-B Lean** — GENIND.B's scaffold is a finite recursion over
>    (A1) data: the natural Lean target once the hostile arcs mature
>    (math-first: Lean waits).
> 5. **Public exposition** — at the next milestone fold: the map's
>    general-n panel can now show the honest structure (proved
>    scaffold + boxed stage laws), per the standing directive.”

**CONDITIONALITY:** A work plan, not a claim. **Item 1 is the upgrade rule for shard 1's `.73` preregistration, and no unit anywhere records whether it fired** (shard 1 OPEN-CALL 4; re-raised here as OPEN-CALL 2). **Item 3's “no other degree-specific work remains” is qualified from outside the range** by the n ≥ 8 conditionality movement (shard 3), which adds [GENHN-TOW-1] as a degree-specific dependency above 7 — not degree-specific *work inside this note*, but degree-specific conditionality nonetheless.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1445–1462. correction sites: none in range; item 3 qualified at 3076–3088 (shard 3).

**TEETH:** NONE — a plan.

XREF: `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md:W-9` — count **13**; `JC-LOAD` — count **31**.
XREF: `lean/notes/openmath/JD0_PROOF_2026-08-08.md:J-D0` — count **25**.

---

### EFF.GENIND.s2of3.09  [scope-record]

**CANONICAL STATEMENT:** FORM: bulleted display with an `[r6]` dated append (§S9.3's W-12 bullet — the stack's heaviest). verbatim, lines 1466–1482.

> “* **THEOREM W-12.D + W-12.A + S2.4/S2.5 + W12-L0/L1** @ w12 seal
>   f669cb0 / verdict c16c717 / r1 ba0d1a4 / r2 99f1813 (arc 0/2, PE2
>   adjudicated + r2, PE3 owed) — the reduction, the order-1 leaves at
>   every degree, the [r1 F3] refine taxonomy, the (1²) frontier law.
>   [r6, PE6-G1 + PE6-m1, dated append + RE-PIN, git-log-checked at
>   commit time: the parenthetical above was true when written (08-08
>   10:16) and went stale across THREE undisclosed W12 repair rounds —
>   r3 b17238a (PE3 GAP: undecided(n,q,N) σ-pinned to BOX-7's
>   notion), r4 d2d91b7/5728258 (PE4 F1 **CRITICAL** repaired: S3.2's
>   b₂ = 0 witness pair; plus the (A1) σ-LABELING clause + the FIRING
>   CHECK at all suppliers), r5 be4a1dc/ee17210 (PE5 GAP + 3m; the
>   HM3.C (A0) supply re-derived at the disc ≠ 0 form). **NEW PIN =
>   r5 HEAD be4a1dc/ee17210** (arc 0/2; runner + artifacts byte-frozen
>   at seal f669cb0 throughout, per each repair's own commit).
>   Consumption verdict SURVIVES — S16 table row 1: zero S3.2 cites in
>   this note (grep executed this round); W-12.D re-read at the new
>   pin and re-matched to Step 5, quoted at S16.]”

**CONDITIONALITY:** **The sealed parenthetical “(arc 0/2, PE2 adjudicated + r2, PE3 owed)” is a STALE-SELF-DESCRIPTION corrected by dated append, not by edit** — it sat true at 08-08 10:16 and went stale across three undisclosed supplier rounds, one of which repaired a **CRITICAL**. The `[r6]` append supplies the new pin and the survival evidence. **The survival evidence is itself corrected once more**: PE7-m1 (`.69`) re-words “zero S3.2 cites in this note” to “zero S3.2 cites outside this round's own disclosure sentences (grep: 4 string hits, all four disclosure)”.

**SUPERSESSION KIND:** `as-of scoping` (the pin) + `counter re-reading` (the arc parenthetical) + a further `wording-rider` from PE7-m1 on the grep claim. **Three kinds on one bullet.**

**CHAIN:** sealed pin `r2 99f1813` with a stale arc parenthetical → `[r6]` RE-PIN to **`r5 HEAD be4a1dc/ee17210`**, three intervening rounds enumerated including a repaired CRITICAL → PE7-m1's correction of the grep claim — **TERMINAL: pin = r5 be4a1dc/ee17210; verdict SURVIVES; the S3.2 claim reads “zero consuming cites; 4 string hits, all disclosure”.**

**DERIVATION:** Not a mathematical unit; a supplier pin + consumption verdict. The verdict's substance is re-verified verbatim at `.64`.

**RESOLUTION TRACE:** statement lines 1466–1482. correction sites: 2354 (§S16 row 1), 2376–2399 (`.64`, the verbatim re-verification), 2479–2487 (PE7-m1, `.69`).

**TEETH:** GT-PIN guards the w12 **runner** md5, not the note pin; the note pin is git-log-checked. Disposition: `in-house hostile pass` (PE6 found the staleness) + `transfer audit` (rule 27 — the survival verdict is a clause-by-clause transfer check across a supplier's repair arc, which no battery row could perform).

**PIN VERIFICATION:** `f669cb0`, `c16c717`, `ba0d1a4`, `99f1813`, `b17238a`, `d2d91b7`, `5728258`, `be4a1dc`, `ee17210` — **all resolve as commits ✓** (9/9).
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:THEOREM W-12.D` — count **5**; `THEOREM W-12.A` — count **8**; `S2.4` — count **10**; `S2.5` — count **9**; `W12-L0` — count **32**; `W12-L1` — count **30**; `σ-LABELING` — count **7**; `b₂ = 0` — count **15**.

---

### EFF.GENIND.s2of3.10  [scope-record]

**CANONICAL STATEMENT:** FORM: bulleted display with an `[r6]` dated append. verbatim, lines 1483–1490.

> “* **THEOREM W-11(n = 2)** @ seal 7020ceb / r2 31506b3 / PE3 CLEAN
>   839b735 (counter 1/2 — the first clean pass) — through W12-L0 and
>   R(M). [r6, PE6-m1 dated append, git-log-checked at commit time:
>   **ACCEPTED 2/2** @ 35e6545 (08-08 10:53, PE3 + PE4 clean;
>   append-only acceptance annotation, body byte-frozen since r2
>   31506b3). **NEW PIN = 35e6545.** Consumption verdict SURVIVES —
>   S16 table row 4: an honest strengthening, zero content diff to
>   the consumed body.]”

**CONDITIONALITY:** An **honest strengthening**: the supplier's grade improved and its body did not move. This is the cleanest row in the stack and the note flags it as such.

**SUPERSESSION KIND:** `as-of scoping` + `counter re-reading` (the supplier's clean counter 1/2 → 2/2).

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1483–1490. correction sites: 2357 (§S16 row 4).

**TEETH:** GT-PIN guards the w11 runner md5 (`500aae15`, `.68`). Disposition: `transfer audit`, trivial (zero content diff).

**PIN VERIFICATION:** `7020ceb` ✓, `31506b3` ✓, `839b735` ✓, `35e6545` ✓.
XREF: `lean/notes/openmath/W11_PROOF_2026-08-08.md:THEOREM W-11` — count **3**.
XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:R(M)` — count **21**.

---

### EFF.GENIND.s2of3.11  [scope-record]

**CANONICAL STATEMENT:** FORM: bulleted display with an `[r6]` dated append (§S9.3's HEX3 bullet). verbatim, lines 1491–1504.

> “* **HEX3 (H-1..H-4, HEX3.A/B/C)** @ seal e3f3459 / verdict 671a126 /
>   r1 2580f12 — the n = 3 transport instances, u₃(M), the committed
>   species tables (GT-N3TIE's target). [r6, PE6-G1 dated append +
>   RE-PIN, git-log-checked at commit time: two repair rounds after
>   the r1 pin — r2 a707430 (08-08 12:13: never-measured census
>   11 → 12 pairs; S8.2's k = 1 mass regains its (1 − q^{−(N−3)})
>   factor), r3 b6a1d69 (17:53: the S8.2 W-12.B consistency clause
>   conditionalized on the open HEX3-BOX-1 tail-σ lemma). **NEW PIN =
>   r3 HEAD b6a1d69** (arc counter 0/2; runner + artifacts byte-frozen
>   at seal e3f3459 throughout). Consumption verdict SURVIVES — S16
>   table row 2: both corrected items are S8.2/census records this
>   note never cites; the consumed species tie is at the md5-frozen
>   `hex3_checks_results.json` ce6f4116, GT-PIN re-verified 5/5 this
>   round.]”

**CONDITIONALITY — the exact conditionality wording, compiled with care (this is ledger row HYP.137's named live consumer).**

*What GENIND asserts, verbatim, is a two-part claim:*
1. **The supplier's S8.2 W-12.B consistency clause is now conditionalized on an OPEN lemma:** “r3 b6a1d69 (17:53: **the S8.2 W-12.B consistency clause conditionalized on the open HEX3-BOX-1 tail-σ lemma**)”.
2. **GENIND's own consumption is unaffected, and the reason is a non-citation:** “**both corrected items are S8.2/census records this note never cites**; the consumed species tie is at the md5-frozen `hex3_checks_results.json` ce6f4116”.

*The ledger's independent classification of the same object* (`spec/HYPOTHESIS_LEDGER.md:1086–1094`), quoted because it is the authority on what rides on this pin and it names GENIND explicitly:

> “HYP.137  `HEX3-BOX-1` tail-σ-certification lemma
> WHERE: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md` L437, L681–693; `GENIND_PROOF_2026-08-08.md` L1498; `TIGHTNESS_CENSUS_2026-08-11.md` O-10 L93.
> STATEMENT: The exact law for the σ-undecided mass is not derived — “q^N ≤ U₃^σ ≤ U₃^conv = q·u(q,N) and its exact law is NOT derived” (HEX3 L437) — because the TRP tail-σ transport loses ghost digits.
> CONSUMED BY: GENIND’s S8.2 W-12.B consistency clause, pinned open at HEAD: “r3 b6a1d69 (17:53: the S8.2 W-12.B consistency clause conditionalized on the open HEX3-BOX-1 tail-σ lemma)”. Failure price displayed at HEX3 L684–686: undecided(3,q,N)·q^(−2N) diverges linearly in N and “W-12.B would be FALSE at n = 3”. NOT consumed by drainage: HEX3 L692–693 — “the (hExhaust-3) discharge never needed the split; only this aside’s W-12.B corroboration is conditional on it.”
> CLASS: conditional-theorem-leg
> PROPOSED DISPOSITION: MATH — the tail-σ lemma is unproved and now has a named live consumer, so it is no longer index-only under HYP.29.”

*Compiler verification of the ledger's supporting quotes against the supplier file* (reading notes, grep-checked at HEAD): `HEX3_PROOF_2026-08-08.md:437` reads “q^N ≤ U₃^σ ≤ U₃^conv = q·u(q,N) and its exact law is NOT derived” ✓ (verified verbatim at that line); `:692–693` reads “the (hExhaust-3) discharge never needed the split; only this aside's W-12.B corroboration is conditional on it.” ✓; `:686` reads “W-12.B would be FALSE at n = 3” ✓. Fixed-string `HEX3-BOX-1` count in `HEX3_PROOF_2026-08-08.md` = **11**.

*The precise scope, stated so a chapter cut cannot over- or under-read it:* **HEX3-BOX-1 conditions a CORROBORATION ASIDE, not a load-bearing leg.** The supplier's own sentence draws the line (`hExhaust3` never needed it); GENIND's own sentence draws the same line from the other side (it never cites the S8.2 clause). **What rides on the pin is therefore: nothing in GENIND's induction, and the W-12.B cross-check at n = 3 in HEX3.** The ledger's disposition is MATH (an unproved lemma) with an owner answer already recorded — question 9, answered “NAMED PARENTHETICALLY”: `HEX3-BOX-1` appears in the capstone preview's n = 3 perimeter clause, **disclosed but not promoted to a Display A conjunct**, precisely because `hExhaust3` provably never needed it. The ledger also records a **premise correction** worth carrying: *“the n≤3 menus and drainage **DO** enter the final proof — they are the induction's base cases, and GENIND consumes HMENU3/HEX3 as base data. What stays out of the load-bearing chain is **HEX3-BOX-1 specifically**, not the n=3 work around it.”*

**SUPERSESSION KIND:** `as-of scoping` (the pin moves r1 → r3) + `inventory completion` (the two intervening rounds enumerated). **NOT a `scope-pin` on GENIND's own claims** — nothing of GENIND's is conditionalized by this append; the conditionalization happened at the supplier and GENIND records that it does not consume the conditionalized clause.

**CHAIN:** sealed pin `r1 2580f12` → `[r6]` RE-PIN to **`r3 HEAD b6a1d69`** with two intervening rounds (r2 census 11 → 12; r3 the S8.2 conditionalization) — **TERMINAL: pin = b6a1d69; GENIND's consumption SURVIVES because it never cites either corrected item.**

**ARITHMETIC AUDIT (compiler-computed, on the r2 item this bullet reports):** the census correction is “11 → 12 pairs”, i.e. a never-measured census undercounted by one pair, with the consequence that “S8.2's k = 1 mass regains its (1 − q^{−(N−3)}) factor”. **The compiler cannot recompute either figure from anything in GENIND** — both live entirely in the supplier. Recorded as `UNPINNED-BY-DISPLAY` for this note's purposes: the numbers are cited, not derived, and GENIND's survival claim does not depend on them being right (it depends on them being uncited).

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1491–1504. correction sites: 2355 (§S16 row 2). External authority: `spec/HYPOTHESIS_LEDGER.md:1086–1094` (HYP.137) and its question-9 disposition at `:1480–1481`.

**TEETH:** GT-PIN 5/5 (the md5-frozen `hex3_checks_results.json` `ce6f4116`) + GT-N3TIE (0/16, the species tie both ways). **The species tie is the only thing GENIND consumes from HEX3's machine side, and it is pinned to a frozen artifact rather than to the note** — which is exactly why the note's two repair rounds cannot disturb it. Disposition: executable regression + `transfer audit`.

**PIN VERIFICATION:** `e3f3459`, `671a126`, `2580f12`, `a707430`, `b6a1d69` — all resolve as commits ✓ (5/5).
XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:H-1` — count **5**; `H-2` — count **11**; `H-3` — count **5**; `H-4` — count **2**; `THEOREM HEX3.A` — count **11**; `THEOREM HEX3.B` — count **8**; `HEX3-BOX-1` — count **11**.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:W-12.B` — count **19**.
**NEAR-MISS (rule 15):** `HEX3.C` — fixed-string `HEX3.C` count **0** in `HEX3_PROOF_2026-08-08.md`; the file's addressable theorem designations that verify are `THEOREM HEX3.A` (11) and `THEOREM HEX3.B` (8). Carried descriptively; recorded as source defect 2 (§8).
**NEAR-MISS:** `u₃(M)` — count **0** in the supplier (which writes `u(q,N)` / `u(M)`); GENIND-local notation, as at shard 1 `.45`.

---

### EFF.GENIND.s2of3.12  [scope-record]

**CANONICAL STATEMENT:** FORM: bulleted display with an `[r6]` dated append. verbatim, lines 1505–1517.

> “* **HMENU3 (HM3-1..4, HM3.A/B/C/D)** @ seal 64d3ff9 / verdict 625fa49
>   (0/2, PE1 = 0C+1G+1m @ f4f7b03, r1 owed) — the two-phase chain
>   template, the raw-key dictionary, the n = 3 bracket instance.
>   [r6, PE6-G1 + PE6-m1, dated append + RE-PIN, git-log-checked at
>   commit time: the "r1 owed" parenthetical went stale through r1
>   3235e1b, r2 e1280be, **ACCEPTED 2/2** @ 050425d (08-08 12:44), and
>   **ANNEX A** @ 19c0285 (20:27: HM3.C's (A0) quantifier corrected to
>   the disc ≠ 0 form at two sites, accepted body byte-frozen). **NEW
>   PIN = accepted body 050425d + ANNEX A 19c0285.** Consumption
>   verdict SURVIVES — S16 table row 3: ANNEX A corrects the
>   quantifier exactly TO the disc ≠ 0 form this note's S5.2
>   certificate-transport argument and S6 Step 4's exact-complement
>   cite consume.]”

**CONDITIONALITY:** **The strongest SURVIVES verdict in the stack, and the only one where the supplier's correction moves TOWARD this note's usage rather than merely past it.** §S16 row 3 re-reads the annex text this round: “HMENU3 annex text re-read this round: "every disc ≠ 0 lift of that member has σ = the leaf table's entry"”.

**SUPERSESSION KIND:** `as-of scoping` + `counter re-reading` (0/2 → ACCEPTED 2/2) + `inventory completion` (ANNEX A added to the pin).

**CHAIN:** sealed pin `seal 64d3ff9 / verdict 625fa49` with “r1 owed” → r1 `3235e1b` → r2 `e1280be` → **ACCEPTED 2/2 `050425d`** → **ANNEX A `19c0285`** — **TERMINAL: pin = accepted body 050425d + ANNEX A 19c0285.**

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1505–1517. correction sites: 2356 (§S16 row 3), 2425–2427 (PE6 trace (i)/(iv)).

**TEETH:** GT-PIN guards the hmenu3 runner md5 (`65326f85`, `.68`). Disposition: `transfer audit` — a clause-level check that the supplier's quantifier correction lands on the form consumed.

**PIN VERIFICATION:** `64d3ff9` ✓, `625fa49` ✓, `f4f7b03` (cited; not re-verified here — shard-2 note: it resolves), `3235e1b` ✓, `e1280be` ✓, `050425d` ✓, `19c0285` ✓.
XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:HM3-1` — count **4**; `HM3-2` — count **5**; `HM3-3` — count **3**; `HM3-4` — count **11**; `HM3.A` — count **18**; `HM3.B` — count **19**; `HM3.C` — count **15**; `HM3.D` — count **13**.

---

### EFF.GENIND.s2of3.13  [scope-record]

**CANONICAL STATEMENT:** FORM: bulleted display. verbatim, lines 1518–1519.

> “* **LEMMA J-D0** @ 1642275/9387eb1 — the count-gauge-blindness frame
>   (S7's letter-blindness; the char-tally legs corroborate again).”

**CONDITIONALITY:** Unmoved. §S16's unmoved-pin list (lines 2365–2366): “J-D0 @ 1642275/9387eb1 — note last touched 9387eb1 (08-07 16:54), pre-seal, pin = HEAD ✓”.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1518–1519. correction sites: 2365–2366 (`.63`).

**TEETH:** Indirect — the char-tally legs (GT-PART's Zp/F_q[[t]] identity at all 11 shared (m,q,N)) are the standing corroboration of letter-blindness.

**PIN VERIFICATION:** `1642275` ✓, `9387eb1` ✓.
XREF: `lean/notes/openmath/JD0_PROOF_2026-08-08.md:LEMMA J-D0` — count **4**.

---

### EFF.GENIND.s2of3.14  [scope-record]

**CANONICAL STATEMENT:** FORM: bulleted display. verbatim, lines 1520–1522.

> “* **GRTJC W-6..W-9 (ACCEPTED 2/2 @ 83f47f4; JC-F1/JC-F2 [r1/r2])** —
>   consumed ONLY in S7's display: dim_K 𝒜(T) = E, the carry cocycle,
>   JC-LOAD's no-cancellation. No count law of S2–S6 consumes them.”

**CONDITIONALITY:** Unmoved body. §S16's unmoved-pin list (lines 2367–2369): “GRTJC (accepted 2/2 @ 83f47f4) — note last touched 63091ce (08-07 20:06, pre-seal annex), body unmoved ✓”. **The second sentence is a NON-IMPORT fence** and is one of the three quotes that make header predicate A's scope split honest.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1520–1522. correction sites: 2367–2369 (`.63`).

**TEETH:** NONE — a citation + fence.

**PIN VERIFICATION:** `83f47f4` ✓, `63091ce` ✓.
XREF: `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md:W-6` — count **18**; `W-8` — count **35**; `W-9` — count **13**; `JC-F1` — count **18**; `JC-LOAD` — count **31**; `dim_K 𝒜(T) = E` — count **3**.
**NEAR-MISS:** `W-7` is named only inside the range designation “W-6..W-9”; fixed-string `W-7` is not separately cited in GENIND and is not emitted as an XREF.
**NEAR-MISS:** `JC-F2` — cited here as one of the two GRTJC findings; not separately grep-recorded (the bullet's substantive cites are JC-F1 and JC-LOAD). Recorded so the merge does not treat `JC-F2` as a verified consumed designation.

---

### EFF.GENIND.s2of3.15  [scope-record]

**CANONICAL STATEMENT:** FORM: bulleted display. verbatim, lines 1523–1524.

> “* **WELDMASTER / DULEMMA / [W12-H]** @ their accepted pins — named in
>   S7.1's (CS-1..3) pricing only.”

**CONDITIONALITY:** Unmoved bodies. §S16's unmoved-pin list (lines 2366–2371): “DULEMMA @ f819f26 — last touched f819f26 (08-07 18:59), pin = HEAD ✓; … WELDMASTER (accepted) — note last touched fdf1d99 (08-07 19:20, pre-seal fold-carry annexes), body unmoved ✓ … [W12-H] is W12-note-internal and rides row 1.” **The bullet cites no pin of its own** (“@ their accepted pins”) — a non-enumerative pin reference of exactly the species the standing rule (`.54`) later bans in RECORDS; §S16 supplies the enumeration.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1523–1524. correction sites: 2363–2371 (`.63`, which supplies the missing enumeration).

**TEETH:** NONE.

**PIN VERIFICATION:** `f819f26` ✓, `fdf1d99` ✓. Target files `WELDMASTER_2026-08-08.md` ✓ and `DULEMMA_PROOF_2026-08-08.md` ✓ EXIST.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:[W12-H]` — count **17**.

---

### EFF.GENIND.s2of3.16  [scope-record]

**CANONICAL STATEMENT:** FORM: bulleted display with an `[r6]` dated append. verbatim, lines 1525–1534.

> “* **QSCOUT22** @ 240a56c (skeleton) — the (2,2) empirical instrument;
>   S7.3's predictions target its table; nothing consumed from it.
>   [r6, PE6-G1 dated append + RE-PIN, git-log-checked at commit time:
>   the skeleton pin predates the scout's own arc — seal 970197d,
>   VERDICT dd67cda (08-08 10:00, GREEN 7,614,473/0), L3-correction
>   annex fcaf268 (14:23; the genre-E UND display's h = 1 slip, the
>   same slip GENH4-BOX-7 discloses). **NEW PIN = verdict dd67cda +
>   annex fcaf268.** Consumption verdict trivially SURVIVES — S16
>   table row 5: nothing was or is consumed; S7.3's prediction targets
>   are the committed artifacts @ dd67cda, byte-fixed.]”

**CONDITIONALITY:** **“nothing consumed from it” is declared twice and is what makes the survival trivial.** But the append also records that the scout's table — the very object shard 1's `.73` predictions target — carried a display slip (“the genre-E UND display's h = 1 slip”) corrected by an annex. **Nothing in GENIND records whether the predictions were scored against the pre- or post-correction display, or at all** (OPEN-CALL 2).

**SUPERSESSION KIND:** `as-of scoping` (skeleton → verdict + annex).

**CHAIN:** skeleton `240a56c` → seal `970197d` → **VERDICT `dd67cda`** → L3-correction annex `fcaf268` — **TERMINAL: pin = dd67cda + fcaf268.**

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1525–1534. correction sites: 2358 (§S16 row 5).

**TEETH:** NONE consumed. The scout's own GREEN (7,614,473/0) is foreign evidence for the scout's predictions, **not for GENIND's `.73`**; the note does not claim otherwise, and this compilation does not infer otherwise.

**PIN VERIFICATION:** `240a56c` ✓, `970197d` ✓, `dd67cda` ✓, `fcaf268` ✓.
XREF: `lean/notes/openmath/GENH4_PROOF_2026-08-08.md:GENH4-BOX-7` — count **1**.
XREF: `lean/notes/openmath/QSCOUT22_2026-08-08.md:GENRE E` — count **2**.

---

### EFF.GENIND.s2of3.17  [scope-record]

**CANONICAL STATEMENT:** FORM: bulleted display with `[r3]` and `[r6]` dated appends (§S9.3's GENHN bullet). verbatim, lines 1535–1550.

> “* **GENHN (THEOREM GENHN.A(iv)(v) + LEMMA GENHN-3 + S6.2)**
>   @ 850e77e [r3, PE3-m4: consumed since r1/r2, omitted from this
>   stack until now] — A(iv) (the stage node floor κ ≥ S_b + 1) inside
>   LEMMA GENIND-6(b); A(v) (the ragged-window-corrected stage read)
>   at (CS-1); LEMMA GENHN-3 (ragged-band confinement) at (CS-1) and
>   Step 4; S6.2 (the ghost × letter reconciliation) at (CS-2).
>   [r6, as-of disclosure, git-log-checked at commit time: note HEAD
>   = 850e77e, THE PIN, unmoved — but THREE errata are QUEUED against
>   the GENHN arc, unexecuted (ledger: PROJECT_STATE 2026-08-09
>   append, "GENHN's erratum queue now 3 items (UND phrasing;
>   comp-weighting; A(i) transport)" — the third is the Codex-GENH4
>   F3 filing this bullet's GENH4 neighbor already discloses).
>   Per-clause check at ledger granularity: none of the three names
>   A(iv), A(v), GENHN-3, or S6.2 — the four clauses consumed here —
>   and A(i) is uncited in this note; the next dated append owes
>   their execution disclosure. S16 table row 6.]”

**CONDITIONALITY:** **Two obligations are created here and both are discharged from outside the range.**
1. **The four-clause consumed surface is INCOMPLETE.** PE7-m2 (`.70`) completes it to seven: “beyond the four listed clauses (A(iv), A(v), GENHN-3, S6.2), this note leans on GENHN at three further sites — the GENHN S11.F schema cite at the GENIND-6(a) proof (L684), the GENHN S6.3 display cite at S6 Step 4 (L1094), and the embedded-genre echo at the GENIND-6(a) statement (L623) — screen future GENHN errata against the seven sites, not four”.
2. **“the next dated append owes their execution disclosure”** — an explicitly owed obligation, discharged by the dated supplier-movement record (lines 3032–3094, shard 3), which opens: “**Owed disclosure discharged (S16 row 6: "execution disclosure owed at the next dated append")**”, reports E1/E2/E3 executed plus GENHN r2, and screens all seven PE7-m2 sites clause by clause. **That record also changes GENIND's own conditionality at n ≥ 8** (shard 1 `.15`).

**SUPERSESSION KIND:** `[r3, PE3-m4]` = `inventory completion` (a bullet consumed since r1/r2 is added to the roster). `[r6]` = `as-of scoping` **with an owed obligation attached** — a form the v3 enum does not name; recorded as `as-of scoping + owed-disclosure`. PE7-m2 = `inventory completion` (four sites → seven).

**CHAIN:** consumed-but-unlisted (r1/r2) → `[r3, PE3-m4]` added to the stack, four clauses → `[r6]` as-of disclosure, three errata queued, disclosure owed → **PE7-m2: seven sites, not four** → **dated supplier-movement record: errata E1–E3 EXECUTED + GENHN r2, all seven sites screened, all SURVIVE; conditionality at n ≥ 8 gains [GENHN-TOW-1] — TERMINAL.**

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1535–1550. correction sites: 2359 (§S16 row 6), 2488–2498 (PE7-m2, `.70`), 3032–3094 (the supplier-movement record, shard 3).

**TEETH:** NONE — a pin + consumed-clause inventory. Disposition: `transfer audit` at ledger granularity (the note says so: “Per-clause check at ledger granularity”), later re-run at diff granularity by the supplier-movement record (“screened against the 850e77e → HEAD diff this round”).

**PIN VERIFICATION:** `850e77e` ✓. The errata/r2 commits named in shard 3 — `bc1b996` ✓, `961d0ff` ✓, `46bf675` ✓, `58b1080` ✓, `d16869c` ✓, `7650b20` ✓, `438608a` ✓, `9636b7e` ✓ — all resolve (8/8), recorded here because they discharge this bullet's owed obligation.
XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN.A(iv)` — count **3**; `GENHN.A(v)` — count **6**; `LEMMA GENHN-3` — count **3**; `S6.2` — count **6**; `S11.F` — count **10**; `S6.3` — count **3**; `GENHN.A(i)` — count **11**.

---
### EFF.GENIND.s2of3.18  [scope-record] · **SERIES GENH4-PIN, all four entries**

**CANONICAL STATEMENT:** FORM: bulleted display carrying FOUR dated appends in chronological order (§S9.3's GENH4 bullet — the stack's most-appended). verbatim, lines 1551–1599.

> “* **GENH4 (THEOREM GENH4.A/B + GENH4-1F, the Q22-L1/L3 package)**
>   @ r3 4b0d946 [r3, PE3-G1 + PE3-m4: re-pinned at the actual repair
>   HEAD; arc since: PE4 CLEAN @ e15308d, its count 1/2] [r4, dated
>   append, checked against the git log at commit time: GENH4 is now
>   ACCEPTED 2/2 — passPE5 CLEAN @ 11dbd23 (0C + 0G + 2 display
>   MINORs) with the post-acceptance annex @ baf05ed (accepted body
>   byte-frozen = this r3 pin 4b0d946, 3-way md5-verified per baf05ed;
>   annex = the 2 display MINORs + ANNEX-LEMMA GENH4-7, none touching
>   the GENH4.A/B laws consumed here); no adjudicated unrepaired
>   finding at the pin — an honest strengthening of the (CS-EXACT)
>   n = 4 de facto discharge, which now cites an ACCEPTED supplier]
>   [r5, dated append, checked against the git log at commit time:
>   AFTER r4 landed (05:34/05:38), the Codex GENH4 ratification pass
>   adjudicated CHALLENGE @ 5c8d2fd (06:00:22; F1/F5 MINOR, F2 GAP on
>   post-acceptance ANNEX-LEMMA GENH4-7, F3 display-scope with a
>   GENHN.A(i) transport erratum owed, F4 scoped to a sharpness
>   clause) — so S14's C14 and the [r4] append above were TRUE at
>   their commit time and this bullet gains the disclosure at the
>   next dated append, per the standing rule. ANNEX R (the CHALLENGE
>   repair) applied @ b10a5a7, accepted body byte-frozen (md5
>   a584cb3e 3-way verified per that commit). None of the CHALLENGE
>   findings touches a clause consumed here: this discharge cites
>   THEOREM GENH4.A/B + GENH4-1F + the comp-weighted census
>   ("eleven densities untouched" per the adjudication); GENH4-7 is
>   annex material this note never cites; and GENIND consumes
>   GENHN.A(iv)(v)/GENHN-3/S6.2, not the A(i) clause of F3's queued
>   erratum. GENH4 note HEAD at this commit = b10a5a7; GENHN note
>   HEAD = 850e77e, the pin above, unmoved] [r6, dated append,
>   git-log-checked at commit time: AFTER r5 (07:06:56) the GENH4
>   annex arc moved twice — annex-pass #1 NOT CLEAN (0C + 1G + 4m
>   @ a8dec16, fresh leg fed3cff: GAP-1 = ANNEX R R2's N-even
>   band-pinned leg machine-refuted, a clause this note never cites;
>   the W-12.D-consumed supply clause (b) was re-derived CLEAN in the
>   same pass) and its repair **ANNEX R2** @ 760d20f (07:41: the
>   refuted legs WITHDRAWN, clause (c) restated as (c') at key level,
>   explicitly unconsumed — "W-12.D consumes (b) only" per its own
>   commit record). **NEW PIN = accepted body 4b0d946 (byte-frozen;
>   3-way md5 prefix checks at baf05ed/b10a5a7/760d20f) + annex stack
>   through R2 @ 760d20f**; the annex-stack count is 0/2 with its
>   pass #2 in flight this wave (not landed at this commit).
>   Consumption verdict SURVIVES — S16 table row 7: none of the annex
>   findings touches THEOREM GENH4.A/B, GENH4-1F, or the
>   comp-weighted census consumed here; GENH4.B re-read at the
>   accepted body and re-matched to the Step 4 use-site, quoted at
>   S16] —
>   the
>   (CS-EXACT) n = 4 de facto discharge geography (drain =
>   GENH4.B/Q22-L3, menu = GENH4.A/Q22-L1 + GENH4-1F, comp-weighted
>   census), Step 4 + S7.1 only.”

**SERIES membership (rule 28).** **SERIES GENH4-PIN**, four dated entries in source order, all inside this one bullet:
| # | Entry | Date/commit | What it records | Pin after |
|---|---|---|---|---|
| 1 | `[r3, PE3-G1 + PE3-m4]` | 2026-08-09, GENH4 `4b0d946` | Re-pin to GENH4's ACTUAL repair HEAD; PE4 CLEAN `e15308d`, count 1/2 | `4b0d946` |
| 2 | `[r4]` | GENH4 `11dbd23` + annex `baf05ed` | GENH4 ACCEPTED 2/2; annex = 2 display MINORs + ANNEX-LEMMA GENH4-7 | `4b0d946` (accepted body) |
| 3 | `[r5]` | Codex `5c8d2fd`; repair `b10a5a7` | Ratification **CHALLENGE** (F1–F5) disclosed; ANNEX R applied | `b10a5a7` (note HEAD) |
| 4 | `[r6]` | `a8dec16`/`fed3cff` → **`760d20f`** | Annex-pass #1 NOT CLEAN (GAP-1 machine-refuted); ANNEX R2 withdraws the refuted legs | **accepted body `4b0d946` + annex stack through `760d20f` — TERMINAL** |

**CONDITIONALITY:** **The n = 4 de facto discharge of (CS-EXACT) rests on a supplier whose ANNEX STACK is 0/2 and whose pass #2 was in flight and unlanded at this note's commit.** The note is explicit about the split: the **accepted body** (4b0d946) is byte-frozen and carries the consumed laws; the **annex stack** (through 760d20f) is the unaccepted layer, and everything the CHALLENGE and annex-pass #1 touched lives there. Entry 3 also records the note's own standing-rule compliance in a subtle form: the r4 append was TRUE at its commit time and became stale 22 minutes later, so the disclosure lands at the NEXT append rather than by editing r4 — the rule working as designed.

**SUPERSESSION KIND, per entry:** 1 = `as-of scoping` (re-pin) + `counter re-reading` (GENH4's clean count 0/2 → 1/2); 2 = `counter re-reading` (→ ACCEPTED 2/2) + `inventory completion` (annex contents enumerated); 3 = `provenance-rider` (the r4 append's truth is time-scoped, not withdrawn) + `as-of scoping`; 4 = `as-of scoping` + `inventory completion`. **Four entries, six kind-instances; a flat “this supersedes that” field could not represent it.**

**DERIVATION:** Not a mathematical unit; a supplier pin arc + consumption verdict. The verdict's substance is re-verified verbatim at `.65`.

**RESOLUTION TRACE:** statement lines 1551–1599. correction sites: 2360 (§S16 row 7), 2401–2421 (`.65`, the verbatim re-verification), 2129–2151 (§S14 C14, whose close this bullet's r5/r6 entries falsify and replace, `.50`).

**TEETH:** NONE in this note — the discharge is a citation. Its guard is the **verbatim text match performed at `.65`** against `git show 4b0d946`, plus the negative screen (“none of the annex findings touches …”). Disposition: `transfer audit`.

**PIN VERIFICATION:** `4b0d946` ✓, `e15308d` ✓, `11dbd23` ✓, `baf05ed` ✓, `5c8d2fd` ✓, `b10a5a7` ✓, `a8dec16` ✓, `fed3cff` ✓, `760d20f` ✓ — **9/9 commits resolve.** (`a584cb3e` is an md5, not a commit.)
XREF: `lean/notes/openmath/GENH4_PROOF_2026-08-08.md:THEOREM GENH4.A` — count **5**; `THEOREM GENH4.B` — count **6**; `GENH4-1F` — count **10**; `Q22-L1` — count **7**; `Q22-L3` — count **3**; `ANNEX-LEMMA GENH4-7` — count **11**.
XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN.A(i)` — count **11**; `GENHN.A(iv)` — count **3**; `GENHN.A(v)` — count **6**; `LEMMA GENHN-3` — count **3**; `S6.2` — count **6**.

---

### EFF.GENIND.s2of3.19  [scope-record]

**CANONICAL STATEMENT:** FORM: bulleted display. verbatim, lines 1600–1601.

> “* **Classical:** Hensel (coprime + monic-factor lifting), Ore/GMN
>   order-1, lower-hull geometry, generating functions.”

**CONDITIONALITY:** The classical-only base. **Load-bearing for the axiom question**: `.20`'s close says “No axiom, no weld face inside any count law”, and this bullet is what that sentence quantifies over. Note that **Ore/GMN order-1 is classical here while the order-≥2 GMN leaf theorem is (CS-3)/(H-e), OPEN** (shard 1 `.65`) — the line between cited-classical and open-hypothesis runs exactly at order 1.

**DERIVATION:** Not a mathematical unit; a classical-supplier list.

**RESOLUTION TRACE:** statement lines 1600–1601. correction sites: none.

**TEETH:** NONE.

---

### EFF.GENIND.s2of3.20  [scope-record]

**CANONICAL STATEMENT:** FORM: bold display closing §S9.3. verbatim, lines 1603–1608.

> “**One line: THEOREM GENIND.A(I,II,IV) + GENIND.C's hypothesis set =
> {W-11, W-12.A/L0/L1, HEX3, HMENU3 @ pins + this note's lemmas};
> GENIND.A(III) adds the S4.1 ledger-compression honesty; THEOREM
> GENIND.B adds [GENIND-H] as its displayed hypothesis; the FULL
> uniformity consequence consumes THEOREM W-12.D @ pin. No axiom, no
> weld face inside any count law; grade = composition 0/2.**”

**CONDITIONALITY:** **Header predicate A's governing quote.** Its final clause “grade = composition 0/2” is superseded by the acceptance (`.72`): the note is ACCEPTED 2/2. The rest stands. **Two things a chapter cut must not over-read:** (i) “No axiom, no weld face inside any count law” is a claim about COUNT LAWS, not about the reduction's hypothesis box — [GENIND-H] is a displayed hypothesis, not an axiom, and the sentence does not claim otherwise; (ii) the hypothesis set is stated “@ pins”, and every one of those pins moved (`.09`–`.18`).

**SUPERSESSION KIND:** `counter re-reading` on the grade clause only.

**DERIVATION:** Not a mathematical unit; the note's own one-line self-inventory.

**RESOLUTION TRACE:** statement lines 1603–1608. correction sites: 2510–2526 (`.72`).

**TEETH:** NONE — an inventory sentence.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:THEOREM W-12.D` — count **5**; `THEOREM W-12.A` — count **8**; `W12-L0` — count **32**; `W12-L1` — count **30**.
XREF: `lean/notes/openmath/W11_PROOF_2026-08-08.md:THEOREM W-11` — count **3**.

---

### EFF.GENIND.s2of3.21  [instrument-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (§S10's runner description). verbatim, lines 1612–1619.

> “**Runner:** `verification/openmath/genind_checks.py`. Exact integer
> arithmetic; deterministic; cypari2 only in GT-ORACLE. Self-contained
> reader (fresh same-session code — GENIND-BOX-6's seam), consuming the
> suppliers ONLY as md5 pins + the committed hex3 JSON tie. The reader
> implements the general recursive conservative read: drain rule first,
> exact hull, per-side residuals, α by in-frame recentering, β children
> by c = k scaling (D = weighted min) + monic Hensel extraction at
> window W − D, CS-EXIT at composite openings.”

**CONDITIONALITY:** **This description is what makes the capped-window concordance checkable**: “β children by c = k scaling (D = weighted min) + monic Hensel extraction at window W − D”. §S14's window-site inventory classifies this very sentence as site class 14 and verifies it against the pinned source (`.47`): “CAPPED; matches `extract_child` (md5 e7ca150b), which implements D = min_j(v(a_j) + j·k) literally.” **So the runner implemented the capped window from the seal, while the note's display did not** — the whole PE3-G2/PE4-G1 arc is a display-versus-implementation divergence in which the implementation was right.

**DERIVATION:** Not a mathematical unit; the apparatus.

**RESOLUTION TRACE:** statement lines 1612–1619. correction sites: 2062–2065 (§S14 site class 14, `.47`).

**TEETH:** self-referential. **PIN VERIFICATION:** `verification/openmath/genind_checks.py` EXISTS ✓; md5 pin `e7ca150b` (the note's own repeatedly re-verified value); seal commit `c3212cc` ✓.

---

### EFF.GENIND.s2of3.22  [instrument-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (§S10's family list with evidence classes). verbatim, lines 1621–1631.

> “**Families** (evidence class): GT-PIN [NONE] (5 pins: w11/w12/hex3/
> hmenu3 runners + hex3 results JSON); GT-PART [SAME] (partition + the
> Zp/Fqt tally equality at every shared (m, q, N)); GT-DEPTH0 [SAME,
> both directions]; GT-BDRAIN [SAME] (the n = 4 FULL-side β drain laws
> in closed form — the β-transport consuming the PROVED n ≤ 3 drains
> R(M)/u₃(M)); GT-ALPHA [SAME, pointwise + fibers + onto]; GT-BETA
> [SAME, pointwise Hensel reconstruction]; GT-RECUR [SAME] (α-drain
> self-similarity against fully-enumerated reduced windows);
> GT-BRACKETID [SYM] (LEMMA GENIND-2(b) at m ∈ {2,3,4,5}, μ ∈ {1,2,3},
> q ∈ {2,3}); GT-CRIT [SAME]; GT-N3TIE [NONE]; GT-CONS [SAME]
> (constructed loci); GT-ORACLE [IND].”

**CONDITIONALITY:** **TWELVE families, enumerated.** `GT-AGGDEEP`, cited at shard 1 `.23`, is **not among them** — the compiler records this as shard 1's source defect 1 and confirms it here from the authoritative list.

**ARITHMETIC AUDIT (compiler-computed):** the list contains exactly 12 named families (GT-PIN, GT-PART, GT-DEPTH0, GT-BDRAIN, GT-ALPHA, GT-BETA, GT-RECUR, GT-BRACKETID, GT-CRIT, GT-N3TIE, GT-CONS, GT-ORACLE) ✓. §S11 scores **eleven** predictions P-1…P-11 over them, so the families-to-predictions map is not 1:1 (P-6 covers GT-BETA and GT-RECUR jointly; P-9 covers GT-N3TIE and GT-ORACLE jointly; P-10 covers the four teeth; P-11 is the falsifier set) — recomputed: 12 families − 2 doubled-up pairs = 10 prediction slots + P-10 (teeth) + P-11 (falsifiers) = **12 predictions** if teeth and falsifiers count, but the note lists **11**. Reconciled: GT-CONS has **no prediction of its own** — it appears inside P-11's falsifier clause (“a GT-DEPTH0/GT-CONS α or CS mismatch”) and in the ROSTER's constructed legs, but no P-n scores it by name. **Recorded as a disclosed gap in the preregistration coverage (§8, defect 3), not as an error** — the constructed legs are scored inside GT-ALPHA/GT-DEPTH0's counts.

**DERIVATION:** Not a mathematical unit; the family inventory.

**RESOLUTION TRACE:** statement lines 1621–1631. correction sites: none.

**TEETH:** this unit IS the family index for §5's inverse table.

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:R(M)` — count **21**.
**NEAR-MISS:** `u₃(M)` — count **0** in HEX3 (GENIND-local notation), as at shard 1 `.45`.

---

### EFF.GENIND.s2of3.23  [instrument-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (§S10's roster). verbatim, lines 1633–1641.

> “**ROSTER (full sweeps, per-center, states = q^{m(N−1)}, both ring
> kinds):** n = 3 control: (2,5), (3,4). n = 4: (2,4), (2,5), (2,6),
> (3,3), (3,4), (5,3). n = 5: (2,4), (2,5), (3,3). Total 22 sweep rows
> = 6,422,014 per-center states [2·23,779 + 2·2,046,835 + 2·1,140,393].
> CONSTRUCTED: n=4 α(2) @ (Zp,2,9)
> [4,096]; n=5 α(1) @ (Zp,2,6), (Fqt,2,6) [1,024 each], (Zp,3,6)
> [118,098]; n=4 BFULL(1) types 22/31/2Q @ (Zp,3,6) [59,049 + 118,098 +
> 354,294]. ORACLE (Zp): (2,4) n=4, (3,3) n=4, (2,4) n=5 — every DEC
> member.”

**CONDITIONALITY:** The roster fixes the coverage every SAME-class family inherits. **Max full-sweep window is N = 6**, which is why TWOCHILD (first visible N = 7) is beyond it and PSTEEP3/PSTEEP4 (N = 5, 6) are inside it — the fact §S14's C1/C2 turn on.

**ARITHMETIC AUDIT (compiler-computed, every number re-derived; rule 22):**
* **Row count:** 2 (n = 3) + 6 (n = 4) + 3 (n = 5) = 11 distinct (q, N) rows × **2 ring kinds** = **22 sweep rows** ✓.
* **n = 3 control states**, m = 3: (q,N) = (2,5) → `2^{3·4}` = 4,096; (3,4) → `3^{3·3}` = 19,683. Sum = **23,779** ✓ — matching the bracket's first term.
* **n = 4 states**, m = 4: (2,4) → `2^{12}` = 4,096; (2,5) → `2^{16}` = 65,536; (2,6) → `2^{20}` = 1,048,576; (3,3) → `3^{8}` = 6,561; (3,4) → `3^{12}` = 531,441; (5,3) → `5^{8}` = 390,625. Sum = 4,096 + 65,536 + 1,048,576 + 6,561 + 531,441 + 390,625 = **2,046,835** ✓ — matching the bracket's second term exactly.
* **n = 5 states**, m = 5: (2,4) → `2^{15}` = 32,768; (2,5) → `2^{20}` = 1,048,576; (3,3) → `3^{10}` = 59,049. Sum = 32,768 + 1,048,576 + 59,049 = **1,140,393** ✓ — matching the third term exactly.
* **Grand total:** 2·23,779 + 2·2,046,835 + 2·1,140,393 = 47,558 + 4,093,670 + 2,280,786 = **6,422,014** ✓ — the displayed figure, recomputed from first principles. **All four state counts and the total reproduce exactly from `q^{m(N−1)}`.**
* **Constructed legs:** n = 4 α(2) at (Zp, 2, 9) — a *reduced* window count 4,096 = `2^{12}`, not `2^{4·8}` (the α(2) node is a slice, not the full space); n = 5 α(1) at (2,6) → 1,024 = `2^{10}`; (3,6) → 118,098 = `2·3^{10}` = 2·59,049 ✓; BFULL(1) at (3,6): 59,049 = `3^{10}`, 118,098 = `2·3^{10}`, 354,294 = `6·3^{10}` ✓ — the three type multiplicities are 1 : 2 : 6 for types 22/31/2Q. **Consistent as slice counts; NOT full-space counts** — the same reading hazard shard 1 records at its `.27`/`.28`.
* **Constructed total:** 4,096 + 1,024 + 1,024 + 118,098 + 59,049 + 118,098 + 354,294 = **655,683**. The note gives no constructed total; recorded here for the merge.

**DERIVATION:** Not a mathematical unit; the roster.

**RESOLUTION TRACE:** statement lines 1633–1641. correction sites: none. Re-verified out of range by PE4's isolated re-run (§S14 C12, `.49`).

**TEETH:** the roster IS the coverage the families inherit; the constructed legs are the note's answer to state-space blowup (“CONSTRUCTED targeted loci where it does not”, shard 1 `.02`).

---
### EFF.GENIND.s2of3.24  [run-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (§S10's pre-seal disclosures). verbatim, lines 1643–1653.

> “**PRE-SEAL SMOKE + PROBES DISCLOSED** (the runner docstring carries
> the same record): smoke run 1 RED with exactly one violation — the
> predictor listed V4E2(1,1) at (Zp,2,4,n5), refuted by the trace: the
> hull convexity at the (4, v₄) vertex forces h ≥ 2v₄+1, a MATH-side
> correction folded into S5.3 (V4E2 first visible at N = 8:
> predicted-absent here); smoke run 2 GREEN (736 checks / 0). Three
> targeted probes of paths smoke misses: GT-N3TIE clean; GT-ORACLE on
> (Zp,2,4,n4) clean (3,264 scored, 0 bad — the full run repeats this
> row, disclosed); cost probe (Fqt,2,6,n4) 13.6 s / 0 violations
> (verdicts 939,520 DEC / 42,496 DRAIN / 66,560 CS). No full battery
> run before the seal.”

**CONDITIONALITY:** **A pre-seal RED that produced a MATH-side correction** — the strongest possible provenance for shard 1's `.51` VERTEX CONDITION: the condition was not derived and then checked, it was *forced* by a refuted prediction. The last sentence (“No full battery run before the seal”) is the two-commit protocol's own guarantee: the predictions at `.25` were sealed unrun.

**ARITHMETIC AUDIT (compiler-computed):** cost probe at (q, m, N) = (2, 4, 6) has `q^{m(N−1)} = 2^{20} = 1,048,576` per-centre states; the reported verdict split is 939,520 + 42,496 + 66,560 = **1,048,576** ✓ — **exact partition of the full space**, and an independent confirmation of shard 1's `.08` (every state is EXACTLY ONE of five events; here DEC/DRAIN/CS with α and β folded into the DEC/DRAIN totals is not claimed — the three printed classes sum to the whole space, so no state is unclassified). Cross-check on the CS total: `66,560 = E4(1) + F4(1) = 65,536 + 1,024` ✓ (shard 1 `.48`/`.49`), and §S11 P-3 repeats the identity. Cross-check on DRAIN: shard 1's DRAIN locus law `q^{d(m−1)(N−1)} = 2^{15} = 32,768` is the *depth-0* drain, while 42,496 is the probe's total DRAIN over all depths — **42,496 − 32,768 = 9,728**, the deeper drains; not separately displayed, recorded for the merge.

**DERIVATION:** Not a mathematical unit; an executed pre-seal record.

**RESOLUTION TRACE:** statement lines 1643–1653. correction sites: none.

**TEETH:** the smoke IS a tooth in the strongest sense — it fired, RED, on a real defect, before the seal. Disposition: **planted-free discovery** (an unarmed run that caught a predictor error), recorded in the enum as `executable regression`, fired. **PIN:** the runner docstring is named as carrying the same record; the docstring is inside the md5-pinned `genind_checks.py` ✓.

---

### EFF.GENIND.s2of3.25  [preregistration]

**CANONICAL STATEMENT:** FORM: bold-headed numbered display (§S10's predictions P-1…P-10, sealed at commit 1 before any full run). verbatim, lines 1655–1684.

> “**PREREGISTERED PREDICTIONS (commit 1; spot values computed from the
> sealed predictor pre-run):**
> * P-1 [NONE] GT-PIN 0/5.
> * P-2 [SAME] GT-PART 0 violations; Zp/Fqt depth-0 tallies IDENTICAL
>   at all 11 shared (m, q, N).
> * P-3 [SAME] GT-DEPTH0 0 violations both directions. Never-measured
>   spots (per center): (·,2,6,n4): ALPHA(1) = 1,024, E4(1) = 65,536,
>   F4(1) = 1,024, B2Q(1) = 1,024, DRAIN₀ = 32,768 (the cost probe's
>   66,560 CS = E4+F4 exactly); (·,3,4,n4): E4(1) = 13,122, DRAIN₀ =
>   19,683, ALPHA/F4/BFULL ABSENT (4k ≤ 3 impossible); (·,5,3,n4):
>   E4(1) = 2,500, DRAIN₀ = 15,625; (·,2,5,n5): V1E2(1) = 12,288,
>   DRAIN₀ = 65,536, V4E2 ABSENT (vertex condition); (·,3,3,n5): NO CS
>   key at all (V1E2 headroom = 0), DRAIN₀ = 6,561.
> * P-4 [SAME] GT-BDRAIN 0 violations — spot: (·,2,6,n4) B2Q(1) drained
>   = 512 of 1,024 (M = 2: R(2) = 2 of q^{2(M−1)} = 4 block states).
> * P-5 [SAME] GT-ALPHA 0 violations — every fiber exactly
>   q^{k·m(m−1)/2}, scaled states onto.
> * P-6 [SAME] GT-BETA 0 reconstruction failures; GT-RECUR 0 (α-drain
>   = (q−1)q^{k·c(m)}·u_m(N−mk) exactly, per realized k).
> * P-7 [SYM] GT-BRACKETID 24/24 identities.
> * P-8 [SAME] GT-CRIT: ZERO CS events on all four n = 3 rows; every
>   n = 4/5 CS event obeys μ ≥ 2, e·γ ≥ 2, 4 ≤ e·μ·γ ≤ m_frame; no
>   genre outside the S5.3 grammar.
> * P-9 [NONE/IND] GT-N3TIE: both legs exact (HEX3 S5.1 closed forms
>   AND the committed JSON species tables, key by key); GT-ORACLE
>   0 bad on all three rows.
> * P-10 teeth at EXACTLY: GT-T-ALPHA = 12 (8 sweep rows with α keys +
>   4 constructed legs), GT-T-CS = 12 (every n = 4 row), GT-T-CRIT = 4
>   (the n = 5 rows with CS visible: (2,4),(2,5) × 2 kinds; (3,3)
>   correctly excluded), GT-T-BRACKET = 24.”

**CONDITIONALITY:** **A genuine two-commit preregistration** — “commit 1; spot values computed from the sealed predictor pre-run”, with “No full battery run before the seal” (`.24`). Under rule 19 this unit and `.29` (the scored run-record) are TWO units and must stay two: the prediction's truth condition is *was it stated in advance*, the run-record's is *what did the instrument return*.

**ARITHMETIC AUDIT (compiler-computed; every spot value re-derived from the displayed laws of shard 1 — this is the audit that tests whether the preregistration was honestly derivable rather than back-fitted):**
* **(·,2,6,n4):** `E4(1) = (q−1)q^{4N−5h−3} = 1·2^{24−5−3} = 2^{16} = 65,536` ✓. `F4(1) = (q(q−1)/2)q^{4N−10k−4} = 1·2^{24−10−4} = 2^{10} = 1,024` ✓. `DRAIN₀ = q^{d(m−1)(N−1)} = 2^{3·5} = 32,768` ✓. `ALPHA(1) = (Q−1)Q^{m(N−1)−k·m(m+1)/2} = 1·2^{20−10} = 2^{10} = 1,024` ✓. CS total `65,536 + 1,024 = 66,560` ✓ = the cost probe's figure.
* **(·,3,4,n4):** `E4(1) = 2·3^{16−5−3} = 2·3^8 = 2·6,561 = 13,122` ✓. `DRAIN₀ = 3^{3·3} = 19,683` ✓. `F4 ABSENT` because `4k ≤ N−1 = 3` is impossible ✓ (the floor R4 later had to add to the display — **and the preregistration already applied it**, which is the sharpest evidence that the defect was display-only). `ALPHA ABSENT`: α needs `mk ≤ N−1`, i.e. `4k ≤ 3`, impossible ✓.
* **(·,5,3,n4):** `E4(1) = 4·5^{12−5−3} = 4·5^4 = 4·625 = 2,500` ✓. `DRAIN₀ = 5^{3·2} = 15,625` ✓.
* **(·,2,5,n5):** `V1E2(1) = (q−1)q^{4N−5h−3}(q^{N−(5h+1)/2}−1) = 1·2^{20−5−3}·(2^{5−3}−1) = 2^{12}·3 = 12,288` ✓. `DRAIN₀ = 2^{4·4} = 65,536` ✓. `V4E2 ABSENT` by the vertex condition (min entry height 7 > N−1 = 4) ✓.
* **(·,3,3,n5):** headroom `N − (5h+1)/2 = 3 − 3 = 0` → factor `3⁰ − 1 = 0` ✓ NO CS key. `DRAIN₀ = 3^{4·2} = 6,561` ✓.
* **P-4:** `R(2) = 2` of `q^{2(M−1)} = 2² = 4` block states → half of 1,024 = **512** ✓.
* **P-10 tooth counts:** GT-T-CS = 12 = “every n = 4 row” = 6 (q,N) rows × 2 ring kinds ✓. GT-T-CRIT = 4 = 2 rows × 2 kinds ✓. GT-T-BRACKET = 24 = 4 values of m × 3 values of μ × 2 values of q ✓ **exactly**. GT-T-ALPHA = 12 = “8 sweep rows with α keys + 4 constructed legs” ✓ (the four constructed α legs are (Zp,2,9) n=4, (Zp,2,6) n=5, (Fqt,2,6) n=5, (Zp,3,6) n=5 = 4 ✓).
* **Zp/Fqt shared cells:** the roster has 11 distinct (q,N) rows across the three degrees, each run in both ring kinds ✓ — P-2's “all 11 shared (m, q, N)” checks against `.23`'s row inventory exactly.
**Verdict of the audit: all twenty-one preregistered spot values and all four tooth counts are re-derivable from the displayed laws.** Two of them (F4's absence at (·,3,4,n4); V4E2's absence at (·,2,5,n5)) depend on visibility floors that the S5.3 display did NOT carry at seal time — the predictor carried them anyway.

**DERIVATION:** Not a mathematical unit; a preregistration. Its derivability is audited above.

**RESOLUTION TRACE:** statement lines 1655–1684. correction sites: none — §S11 scores it, never edits it.

**TEETH:** this unit IS the tooth specification; `.29` is its scoring.

---

### EFF.GENIND.s2of3.26  [preregistration]

**CANONICAL STATEMENT:** FORM: bulleted display (§S10's P-11 — the falsifier set, a distinct preregistration kind). verbatim, lines 1685–1695.

> “* P-11 falsifiers: a GT-DEPTH0/GT-CONS α or CS mismatch with the
>   n = 3 control clean refutes the S2/S5 laws at n ≥ 4 (diagnose the
>   slot counts first); a GT-BDRAIN violation with GT-BETA clean
>   refutes the β drain composition (LEMMA GENIND-3's consumption of
>   R/u₃ — check HEX3's laws before this note's); a GT-ALPHA pointwise
>   divergence refutes LEMMA GENIND-2(a) at that (m, k); a GT-CRIT
>   event outside the grammar refutes S5.1/S5.3's completeness — the
>   criterion itself dies only if a CS event has e·μ·γ < 4; an
>   ORACLE mismatch hits the σ dictionary (Ore composition, S4.1
>   step 3); a tooth off its count voids the battery, not the
>   theorems.”

**CONDITIONALITY:** **Preregistered falsifiers with explicit LOCALIZATION rules** — each names which unit dies and, in three cases, which supplier to check first. **The last clause is a scoping fence of unusual quality**: “a tooth off its count voids the battery, not the theorems.” Emitted separately from `.25` because a falsifier set and a point prediction have different truth conditions (a falsifier is *not* confirmed by a clean run; it is merely not triggered).

**ARITHMETIC AUDIT:** the criterion's death condition `e·μ·γ < 4` is exactly the negation of shard 1 `.11`'s necessity bound `e·μ·deg ψ ≥ 4` ✓ — the falsifier is stated at the sharpest possible place, and P-8's scored clause `4 ≤ e·μ·γ ≤ m_frame` is its direct machine form ✓.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1685–1695. correction sites: none. Scored at 1750 (`.29`: “P-11 ✓ — no falsifier fired”).

**TEETH:** the falsifier set is the battery's own theory of what would count as refutation. Disposition: `preregistration`; **none fired**.

---

### EFF.GENIND.s2of3.27  [changes-record]

**CANONICAL STATEMENT:** FORM: bold display (§S10's closing verdict placeholder). verbatim, lines 1697–1699.

> “**VERDICT: PENDING — commit 1 seals this note + the runner; commit 2
> appends §S11 from `genind_checks_output.txt` /
> `genind_checks_results.json`.**”

**CONDITIONALITY:** **SUPERSEDED by §S11** (`.28`), which is the commit-2 append this sentence promises. The sentence is preserved as a dated record of the two-commit protocol; it is not live.

**SUPERSESSION KIND:** `replacement` — the placeholder is replaced by the verdict it schedules. (The text is not edited; the note simply appends §S11 below it.)

**CHAIN:** `VERDICT: PENDING` (commit 1, seal `c3212cc`) → **§S11 GREEN (commit 2) — TERMINAL.**

**DERIVATION:** Not a mathematical unit; a protocol placeholder.

**RESOLUTION TRACE:** statement lines 1697–1699. correction sites: 1701–1750 (§S11, `.28`/`.29`).

**TEETH:** the two-commit protocol IS the guard against post-hoc prediction editing. **PIN VERIFICATION:** both named artifacts EXIST ✓.

---

### EFF.GENIND.s2of3.28  [run-record]

**CANONICAL STATEMENT:** FORM: bold display (§S11's headline). verbatim, lines 1703–1710.

> “**GREEN. 163,536 checks, 0 violations in every family, all four teeth
> fired at their EXACTLY-preregistered counts (12/12/4/24), zero
> skips.** 22/22 sweep rows (6,422,014 per-center states, both ring
> kinds) + all 7 constructed legs + 3/3 oracle rows; single fresh run,
> elapsed 164.5 s, exit 0; artifacts `genind_checks_output.txt`
> (md5 c157dc318af13eb10a126cdb9f08f87d),
> `genind_checks_results.json` (md5 366f214322fee97c9669f0584696b3f6);
> runner byte-identical to the sealed commit c3212cc (empty `git diff`).”

**CONDITIONALITY:** **FROZEN AT ITS SEAL — every later repair record says so and none edits it.** §S14's claim group C12 (`.49`) re-verifies it independently: “verdict record, matches the committed artifacts; re-verified by PE4's isolated re-run of the sealed battery (163,536/0, leaf-diff = elapsed only). KEPT.”

**ARITHMETIC AUDIT (compiler-computed):** `22/22 sweep rows` ✓ = `.23`'s 11 (q,N) rows × 2 ring kinds. `6,422,014` ✓ re-derived at `.23` from first principles. `7 constructed legs` ✓ = 1 (n=4 α(2)) + 3 (n=5 α(1) at three (ring,q)) + 3 (BFULL types 22/31/2Q) = 7 ✓. `3/3 oracle rows` ✓ = the three ORACLE rows at `.23`. Tooth tuple `(12/12/4/24)` ✓ = P-10's four preregistered counts, matched one for one. **`163,536 checks` is a check count, not a state count** — it is not reconstructible from the roster (states are inputs, checks are assertions); recorded as UNPINNED-BY-DISPLAY but backed by the two md5-pinned artifacts.

**DERIVATION:** Not a mathematical unit; the sealed run.

**RESOLUTION TRACE:** statement lines 1703–1710. correction sites: **none, at any round** — §S11's freeze is the note's most-repeated invariant. Independent re-verification at 2119–2122 (§S14 C12).

**TEETH:** this unit IS the run of record. **PIN VERIFICATION:** both artifacts EXIST ✓; seal commit `c3212cc` ✓; the “empty `git diff`” claim is a commit-time assertion, not re-checkable at HEAD (the runner's md5 pin `e7ca150b` is the standing proxy and is re-verified at every round).

---

### EFF.GENIND.s2of3.29  [run-record]

**CANONICAL STATEMENT:** FORM: bulleted display (§S11's eleven-item prediction scorecard). verbatim, lines 1712–1750.

> “Prediction scorecard (all eleven confirmed):
> * P-1 ✓ GT-PIN 0/5 — all five frozen suppliers unmoved.
> * P-2 ✓ GT-PART 0/33 — partition exact on every row; Zp/Fqt depth-0
>   tallies IDENTICAL at all 11 shared (m, q, N) — visible already at
>   row level: every Zp/Fqt pair printed identical
>   DEC/DRAIN/CS triples.
> * P-3 ✓ GT-DEPTH0 0/108 both directions. Every never-measured spot
>   EXACT: (·,2,6,n4) ALPHA(1) = 1,024, E4(1) = 65,536, F4(1) = 1,024,
>   B2Q(1) = 1,024, DRAIN₀ = 32,768 (row CS total 66,560 = E4+F4);
>   (·,3,4,n4) E4(1) = 13,122 with ALPHA/F4/BFULL correctly ABSENT;
>   (·,5,3,n4) E4(1) = 2,500; (·,2,5,n5) V1E2(1) = 12,288 with V4E2
>   ABSENT (the vertex condition); (·,3,3,n5) ZERO CS keys (the
>   visibility floor) — the criterion's fine structure on the nose.
> * P-4 ✓ GT-BDRAIN 0/4 — B2Q(1) drained = 512/1,024 at (·,2,6,n4):
>   the β drain composition through R(M) exact.
> * P-5 ✓ GT-ALPHA 0/2,474 — every pointwise scaled re-read agrees
>   (verdict + σ), every ghost fiber exactly q^{k·m(m−1)/2}, scaled
>   states onto the full reduced-window space.
> * P-6 ✓ GT-BETA 0/87,156 Hensel reconstructions coefficient-exact;
>   GT-RECUR 0/8 — the α-drain self-similarity
>   (q−1)q^{k·c(m)}·u_m(N−mk) exact at every realized k.
> * P-7 ✓ GT-BRACKETID 24/24 — LEMMA GENIND-2(b) integer-exact at
>   m ∈ {2,3,4,5} (exponent coefficients 2/4/7/11).
> * P-8 ✓ GT-CRIT 0/22 — ZERO CS events on all four n = 3 control rows
>   (the criterion's negative half); every n = 4/5 CS event (all
>   depths) obeys μ ≥ 2, e·γ ≥ 2, 4 ≤ e·μ·γ ≤ m_frame; no genre
>   outside the S5.3 grammar.
> * P-9 ✓ GT-N3TIE 0/16 — my fresh reader's n = 3 depth-0 species
>   tables equal BOTH the HEX3 S5.1 closed forms AND the committed
>   hex3 JSON, key by key (locus AND drained): the reader IS the
>   suppliers' convention where they overlap. GT-ORACLE 0 bad /
>   73,676 checks — PARI (nfinit/idealprimedec) confirms the σ
>   multiset of EVERY decided member on all three rows (3,264 + 5,670
>   + 27,904 = 36,838 members: the FIRST independent σ verification of
>   quartic and quintic cluster reads in this corpus, wild p = 2
>   strata included), 0 disc-0 lifts.
> * P-10 ✓ teeth — GT-T-ALPHA = 12, GT-T-CS = 12, GT-T-CRIT = 4,
>   GT-T-BRACKET = 24: every count exactly as preregistered.
> * P-11 ✓ — no falsifier fired.”

**CONDITIONALITY:** Frozen at seal. **One scored figure is re-audited from outside the range and does NOT move**: §S14 C12 re-runs the whole battery in isolation and reports “163,536/0, leaf-diff = elapsed only”.

**ARITHMETIC AUDIT (compiler-computed, rule 22 — every count-bearing line):**
* **P-3:** all nine spot values re-derived at `.25` from the displayed laws ✓; `66,560 = 65,536 + 1,024` ✓.
* **P-4:** `512/1,024` ✓ (audited at `.25`).
* **P-9 oracle members:** `3,264 + 5,670 + 27,904 = 36,838` ✓ **the note's own sum checks.** Checks-to-members ratio `73,676 / 36,838 = 2.000` **exactly** ✓ — two checks per member.
* **P-7:** `24 = 4 × 3 × 2` ✓ (m, μ, q).
* **P-2:** `0/33` — 33 = 11 shared (m,q,N) × 3? or 22 rows + 11 tallies? **Not reconstructible from the displayed data**; recorded as UNPINNED-BY-DISPLAY. (Candidate reading: 22 sweep-row partition checks + 11 cross-ring tally checks = 33 ✓ — arithmetically exact and consistent with the two clauses P-2 states, but the note does not say so, so it is recorded as a *candidate*, not a verification.)
* **P-8:** `0/22` = one check per sweep row ✓.
* **P-6:** `GT-RECUR 0/8` — eight realized α(k) instances; not reconstructible from the roster alone (it depends on which (m,k) pairs are realized). UNPINNED-BY-DISPLAY.
* **P-5:** `0/2,474` and **P-6:** `0/87,156` — pointwise counts, not reconstructible. UNPINNED-BY-DISPLAY, backed by the md5-pinned results JSON.
* **Total consistency:** the displayed per-family counts sum to 5 + 33 + 108 + 4 + 2,474 + 87,156 + 8 + 24 + 22 + 16 + 73,676 = **163,526**, against the headline **163,536** — a difference of **10**. The residual is evidently the four tooth counts scored as items plus the six unlisted family/leg checks; the note does not itemize. **Recorded as a disclosed non-reconstruction (§8, defect 4), NOT as a discrepancy** — the artifacts are the authority and are md5-pinned, and the compiler has no basis for calling either figure wrong. Flagged because it is exactly the kind of gap a chapter cut should not paper over.

**DERIVATION:** Not a mathematical unit; the scorecard.

**RESOLUTION TRACE:** statement lines 1712–1750. correction sites: none.

**TEETH:** this unit IS §5's scoring column. Disposition per row is recorded there.

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:S5.1` — count **9**; `R(M)` — count **21**.

---

### EFF.GENIND.s2of3.30  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (§S11's closing consequence). verbatim, lines 1752–1768.

> “**Consequence for the grade box:** THEOREM GENIND.A's clauses (I),
> (II), (IV) and the GENIND.C layer stand as composed,
> machine-corroborated at n = 4 AND n = 5 both characteristics — the
> general α-bracket exercised at m = 4, 5 (exponents 7, 11), the
> β-transport pointwise-Hensel-verified and its drain composition
> consuming the PROVED n ≤ 3 laws confirmed in closed form, and the
> composite-stage criterion confirmed in BOTH directions (n = 3 clean;
> n = 4, 5 CS at exactly the predicted genres, visibility floors
> included). THEOREM GENIND.B stands as the displayed reduction:
> (hMenu-n)+(hExhaust-n) for ALL n — hence, with THEOREM W-12.D, the
> FULL uniformity theorem — is now conditional exactly on the
> composite-stage package [GENIND-H] per genre plus the supplier arc
> grades; at n ≤ 3 it is the proved chain. CANDIDATE GENIND-5 (the
> (2,2) stage law with stage bracket (q−1)q^{2μ−1}) remains boxed at
> (OB-a)/(OB-b)/(OB-c)/(OB-d), with LEMMA GENIND-4 (the fibration +
> the ℤ/2 slot grading) PROVED and its predictions handed to QSCOUT22.
> Attempt 0/2; the hostile arc has not begun.”

**CONDITIONALITY:** Frozen at seal, and therefore **two clauses are STALE by construction**: “Attempt 0/2; the hostile arc has not begun” (eight passes have since run; ACCEPTED 2/2 at `.72`) and “conditional exactly on the composite-stage package [GENIND-H] per genre plus the supplier arc grades” (at n ≥ 8 two further conjuncts enter, shard 3). **Neither is corrected in place** — §S11 is frozen — and the PE8-m1 cure explicitly does NOT reach here: it names only the header arc line and GENIND-BOX-5's close (`.73`). Tagged `STALE-SELF-DESCRIPTION` (rule 26) on both clauses. **This is a genuine gap in the cure's coverage** and is recorded as OPEN-CALL 3.

**ARITHMETIC AUDIT:** “the general α-bracket exercised at m = 4, 5 (exponents 7, 11)” ✓ — `c(4)+1 = 7`, `c(5)+1 = 11` (shard 1 `.23`), and P-7 scored all four values 2/4/7/11 ✓.

**DERIVATION:** Not a mathematical unit; a verdict-consequence statement.

**RESOLUTION TRACE:** statement lines 1752–1768. correction sites: **none — and that is the finding.** Overtaken at 2512–2526 (`.72`) and at 3076–3088 (shard 3).

**TEETH:** the consequence is read off `.29`'s scorecard.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:THEOREM W-12.D` — count **5**.

---
### EFF.GENIND.s2of3.31  [changes-record] · **SERIES REPAIR-ARC, entry 1 of 5**

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (§S12's Arc). verbatim, lines 1770–1778.

> “## S12. [r2] REPAIR RECORD (PE2 adjudication; appended at r2 — S11 above stays frozen at its seal)
>
> **Arc.** Hostile pass PE2 (fresh context, the corpus's first n = 6
> route; report `GENIND_passPE2_report.md` @ 50db400) adjudicated
> 0 CRITICAL + 2 GAP + 1 MINOR. This r2 repairs exactly those findings,
> [r2]-tagged, minimality contract; the sealed runner
> (`genind_checks.py`, md5 e7ca150b) and its committed artifacts are
> BYTE-FROZEN — the r2 machine support is the ADDITIVE leg
> `verification/openmath/genindr2_supp.py` (+ output + results JSON).”

**SERIES:** REPAIR-ARC entry **1 of 5** (r2). Predecessor: r1 (applied in place, no record section — recorded only in the header arc and GENIND-BOX-5). Successor: `.36` (r3).

**CONDITIONALITY:** Three of this record's sentences are later found FALSE and are corrected in place by successors: the PE2-G2 pin-check sentence (by `[r3]` at `.33`) and the PE2-m1 grep claim (by `[r5 sweep]` at `.34`). The Arc paragraph itself is untouched.

**DERIVATION:** Not a mathematical unit. **PIN VERIFICATION:** `50db400` ✓; `genindr2_supp.py` + output + results all EXIST ✓.

**RESOLUTION TRACE:** statement lines 1770–1778. correction sites: none for this paragraph; its record's items at 1795–1808 and 1809–1817.

**TEETH:** the “minimality contract” + “BYTE-FROZEN” pair is the repair protocol's own guard; enumerated by md5 from r5 onward (`.60`, `.68`).

---

### EFF.GENIND.s2of3.32  [changes-record]

**CANONICAL STATEMENT:** FORM: bulleted display (§S12's PE2-G1 item — the mathematical one). verbatim, lines 1780–1794.

> “* **PE2-G1 (the mathematical one) → LEMMA GENIND-6 (S4.3).** Mixed
>   CS+β-child openings — a composite stage whose polygon also carries
>   a repeated-linear e = 1 child, first live at n = 6 — fell between
>   GENIND-3's stated scope and (CS-1)'s displayed fibration. GENIND-6
>   states and proves the transport (split factor-genericity +
>   permanence extended to CS frames + fibration/product with
>   stage-count independence + read/menu/drain composition), derived
>   from GENIND-2/3's own machinery + GENHN.A(iv)(v) @ 850e77e — with
>   the verifier's constructed instance M6 at (2,6,5)/(2,6,6)/(3,5)
>   as the exhaustively machine-checked worked ledger, INCLUDING the
>   sharp certified windows its own tooth surfaced. Wired at S4.1
>   (scope note), S6 Step 2 (mixed menu bucket), S6 Step 4 (mixed
>   drain composition), S7.1 ((CS-1) rider). Conditional structure
>   unchanged: the stage-side clauses of GENIND-6(d) consume
>   [GENIND-H] exactly as (CS-1) does.”

**CONDITIONALITY:** **The largest mathematical addition of the whole arc** — a new lemma with four clauses, a worked ledger and a machine leg, added at r2 in response to a gap between two displayed scopes. Its four wiring sites are enumerated and all four are verifiable in shard 1 (`.29`, `.55`, `.57`, `.63`). **The closing sentence's “Conditional structure unchanged … no more” is later narrowed** by the (CS-1Q) upgrade (shard 1 `.37`).

**SUPERSESSION KIND:** `inventory completion` (a transport that fell between two scopes is supplied) — **not** a `replacement`: nothing displayed was withdrawn.

**DERIVATION:** Not a mathematical unit; the mathematics is shard 1's `.31`–`.42`.

**RESOLUTION TRACE:** statement lines 1780–1794. correction sites: none in range; the clause's conditionality is narrowed at 3712–3721 (shard 3).

**TEETH:** `genindr2_supp.py` (`.35`); the M6 instance is the verifier's construction, adopted and displayed in full.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN.A(iv)` — count **3**; `GENHN.A(v)` — count **6**.

---

### EFF.GENIND.s2of3.33  [changes-record] · **SERIES RECORD-INTEGRITY, entry 1 of 5**

**CANONICAL STATEMENT:** FORM: bulleted display (§S12's PE2-G2 item), carrying an in-place `[r3, PE3-G1]` correction of its own false sentence. verbatim, lines 1795–1808.

> “* **PE2-G2 → Step 4 + S7.1 [r2] re-pin + disclosure.** The
>   (CS-EXACT) n = 4 de facto discharge now cites GENH4 @ r2
>   (fd35416 + 5279a11; the r2 text here also asserted "no GENH4 r3
>   existed at this commit — checked" — [r3, PE3-G1]: that sentence
>   was FALSE; GENH4 r3 = 4b0d946 landed 00:50:10, 10–45 minutes
>   BEFORE all three r2 commits (01:00:35 / 01:21:44 / 01:35:30), and
>   at the pinned r2 there WAS an adjudicated not-yet-repaired finding
>   (GENH4 passPE3's MINOR 1, the dv0 = N trichotomy, adjudicated
>   00:24:06) — corrected at S13, re-pinned at r3 in Step 4/S7.1/S9.3)
>   with BOTH halves named (drain GENH4.B, menu GENH4.A + GENH4-1F,
>   r2 comp-weighted census), and the 49-second timing race at the r1
>   pin dff23f8 is disclosed in full at Step 4. Standing rule adopted:
>   pin suppliers at their repair HEAD and disclose any adjudicated,
>   not-yet-repaired findings at the pin.”

**SERIES:** RECORD-INTEGRITY entry **1 of 5** (PE2-G2). The note's own naming of the class, at `.44`: “PE4-G1 is the arc's THIRD consecutive record-integrity defect (class PE2-G2 → PE3-G1 → PE4-G1: a repo-checkable factual sentence in a repair record, false against the repo)”; extended to five at `.61`.

**CONDITIONALITY:** **A record that adopts a standing rule and is itself found in violation of that rule by the very next pass** — the `[r3]` layer quoted here is the finding. The rule adopted (“pin suppliers at their repair HEAD and disclose any adjudicated, not-yet-repaired findings at the pin”) is restated at `.38` as a COMMIT-TIME action.

**SUPERSESSION KIND:** the `[r3, PE3-G1]` layer = `counter re-reading` (a factual claim about the repo is re-checked and reversed) + `as-of scoping` (the re-pin). The rule adoption itself = `license` on the note's record protocol.

**ARITHMETIC AUDIT (compiler-computed, on the timing claim):** GENH4 r3 landed 00:50:10; the three r2 commits at 01:00:35, 01:21:44, 01:35:30 — differences **10m25s, 31m34s, 45m20s** ✓, matching “10–45 minutes BEFORE all three r2 commits”. The adjudication at 00:24:06 precedes all four ✓.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1795–1808. correction sites: `[r3]` in situ 1798–1803; §S13's PE3-G1 item at 1870–1893 (`.38`).

**TEETH:** **`stale self-description`** — the record's own claim about the repo was falsified by the repo. **PIN VERIFICATION:** `fd35416` ✓, `5279a11` ✓, `4b0d946` ✓, `dff23f8` ✓, `2abf419` ✓, `ad6f31d` ✓, `52fb6ff` ✓, `3b88321` ✓.

---

### EFF.GENIND.s2of3.34  [changes-record]

**CANONICAL STATEMENT:** FORM: bulleted display (§S12's PE2-m1 item), carrying an `[r5 sweep]` rescope. verbatim, lines 1809–1817.

> “* **PE2-m1 → granularity.** "ONE exact q-power per stratum" corrected
>   to "one exact closed form per stratum — a finite sum of q-powers
>   (two-term at GENH4's genre-F even-N CAP(F) band)" at the S1 box,
>   Step 4, and S7.1; S7.4 and S9.1 already carried the correct
>   "exact per-stratum closed forms/laws" granularity (checked by
>   grep for the one-term phrasing: its consumer sites were the S1
>   box, Step 4, and S7.1, all corrected here [r5 sweep: was
>   "checked — no other consumer of the one-term form" — rescoped to
>   the executed grep and its enumerated hits]).”

**CONDITIONALITY:** A granularity correction applied at **three enumerated sites** (shard 1 `.14`, `.57`/`.58`, `.66`). Its coverage claim was universal and is rescoped by `[r5 sweep]` to the executed grep — rewrite (5) of `.59`'s seven.

**SUPERSESSION KIND:** the correction itself = `wording-rider` (a granularity phrase substituted at three displays); the `[r5 sweep]` layer = `counter re-reading` (a universal coverage claim rescoped to an enumerated one).

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1809–1817. correction sites: `[r5 sweep]` in situ 1815–1817; `.59`.

**TEETH:** `arithmetic recount` of a grep's hit set — the species the standing rule (`.54`) exists to enforce.

XREF: `lean/notes/openmath/GENH4_PROOF_2026-08-08.md:GENH4-CAP(F)` — count **11**.

---

### EFF.GENIND.s2of3.35  [run-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph + grade line (§S12's Machine paragraph and close). verbatim, lines 1819–1831.

> “**Machine.** `genindr2_supp.py` GREEN: **2,128,163 checks,
> 0 violations, 357.7 s**; fibration exhaustive at (2,6,5) 8,192 /
> (2,6,6) 524,288 / (3,6,5)-slice 1,594,323 states, constant fibers
> q⁹ (ledger windows) and q⁷ (sharp windows), onto both products;
> exact-factor certification stable at all displayed windows incl.
> sampled (2,6,7); PARI read-composition 360/360; teeth T1 (sharpness,
> 38/40 + 40/40), T2 (pin, 20/20), T4 (PARI counter-prediction,
> 360/360) all FIRED. Instrument arc (run-1 RED on its own tooth →
> truncation-artifact diagnosis → exact-factor redesign) disclosed in
> the leg's docstring and S4.3's machine record.
>
> **Grade: stays 0/2. The consecutive-clean count has NOT started; PE3
> (a fresh hostile pass) attempts the first clean.**”

**CONDITIONALITY:** The grade line is a **round-dated record**, correct as of r2 — the acceptance record says so explicitly for the whole series (`.72`): “(The per-round grade closes … are round-dated records, correct as of their rounds; this append is the current state.)” **So the five grade closes are NOT stale-self-descriptions: the note pre-emptively scopes them.** A rare and worth-copying move.

**ARITHMETIC AUDIT:** the three fibration row totals restated here are identical to shard 1 `.40`'s ✓; the headline 2,128,163 is the same non-reconstructible total recorded at shard 1's defect 4. `38/40 + 40/40` matches shard 1 `.40` ✓.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1819–1831. correction sites: none; scoped by 2540–2543 (`.72`).

**TEETH:** as shard 1 `.40`/`.41`.

---

### EFF.GENIND.s2of3.36  [changes-record] · **SERIES REPAIR-ARC, entry 2 of 5**

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph (§S13's Arc). verbatim, lines 1833–1844.

> “## S13. [r3] REPAIR RECORD (PE3 adjudication; appended at r3 — S11 stays frozen at its seal, S12 corrected in place where its own sentence was the finding)
>
> **Arc.** Hostile pass PE3 (fresh context, the corpus's first n ≥ 7
> route; report `GENIND_passPE3_report.md` @ f89b565) adjudicated
> 0 CRITICAL + 2 GAP + 4 MINOR. This r3 repairs exactly those findings,
> [r3]-tagged, minimality contract; the sealed runner
> (`genind_checks.py`, md5 e7ca150b), its committed artifacts, and the
> r2 supp leg (`genindr2_supp.py` + output + results) are all
> BYTE-FROZEN — no machine leg was added at r3; the machine evidence
> cited below is PE3's own committed fresh leg
> (`verification/openmath/genind_pe3_fresh.py` + output + results
> @ f89b565: GREEN, 705,133 checks, 0 violations).”

**SERIES:** REPAIR-ARC entry **2 of 5** (r3). **The heading itself states the round's own supersession discipline** — “S12 corrected in place where its own sentence was the finding” — which is the pattern every later record repeats.

**CONDITIONALITY:** **A round with NO machine leg of its own**, citing the verifier's artifact instead. This becomes the arc's standing practice from r3 on (r4, r5, r6 all do the same, each saying so).

**DERIVATION:** Not a mathematical unit. **PIN VERIFICATION:** `f89b565` ✓; `genind_pe3_fresh.py` + output + results all EXIST ✓.

**RESOLUTION TRACE:** statement lines 1833–1844. correction sites: none for this paragraph.

**TEETH:** foreign-note (verifier) evidence, adopted by citation with an explicit ownership disclaimer.

---

### EFF.GENIND.s2of3.37  [changes-record]

**CANONICAL STATEMENT:** FORM: bulleted display (§S13's PE3-G2 item — the capped window formula), carrying an in-place `[r4, PE4-G1]` correction. verbatim, lines 1846–1869.

> “* **PE3-G2 (the mathematical one) → the capped window formula.**
>   GENIND-3's M_l display (inherited verbatim by GENIND-6(a)) charged
>   every co-block its OWN slope-mass — false under its literal
>   reading at multi-child genres with DISTINCT slopes. Corrected
>   display (re-derived from the polygon geometry: the content of the
>   scaled monic frame is the root-sum Σ min(v(ρ), k_l)):
>   **M_l = N − D_l, D_l = μ_l·k_l + Σ_{other blocks} deg·min(own
>   slope, k_l)** — co-blocks contribute their slope-mass CAPPED at
>   the extracted child's slope; equivalently D_l = min_j (v(a_j) +
>   j·k_l). Corrected at S4.1 (statement + new honesty-note
>   paragraph), S4.3 GENIND-6(a) ("the SAME explicit window" echo),
>   the proof of (a)'s gloss, and the M6 ledger (which sits in the
>   capped = uncapped agreeing regime, now said so). Adjudicating
>   instance: TWOCHILD (hull (0,6)–(2,2)–(4,0), children at slopes 2
>   and 1) — true child-B window N−4, old display N−6, machine-refuted
>   on ALL 2,048 (2,7) + 177,147 (3,7) states with the capped window
>   lift-stable (80 × 5 + 60 × 4). CONCORDANCE: the sealed runner's
>   `extract_child` ALWAYS implemented the capped value (D = weighted
>   min), so every sealed and committed number stands unchanged — the
>   defect was display-only [r4, PE4-G1: the r3 record's closing gloss
>   here, "invisible at n ≤ 6 first-visible windows", was FALSE — the
>   disagreeing regime is first visible at N = 5, n = 3, inside the
>   sealed roster (PSTEEP3 at the (2,5) control row); see S14 and the
>   S4.1 concordance paragraph].”

**CONDITIONALITY:** The mathematics is shard 1's `.24`/`.27`; this is the record of it. **Its own closing gloss was FALSE and is corrected in place** — the second RECORD-INTEGRITY finding's target.

**SUPERSESSION KIND:** the item = `replacement` (of the display, at four enumerated sites); the `[r4]` layer = `counter re-reading` (a visibility inventory reversed).

**ARITHMETIC AUDIT:** the four enumerated correction sites are all verifiable in shard 1 (`.24` statement, `.34` echo, `.34` proof gloss, `.38` M6 ledger) ✓. TWOCHILD windows N−4 / N−6 re-derived at shard 1 `.27` ✓.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1846–1869. correction sites: `[r4]` in situ 1865–1869; §S14's PE4-G2/PE4-G1 items (`.45`, `.46`) and claim group C4 (`.49`).

**TEETH:** PE3's fresh leg (foreign-note evidence, exhaustive at two rows).

---

### EFF.GENIND.s2of3.38  [changes-record] · **SERIES RECORD-INTEGRITY, entry 2 of 5**

**CANONICAL STATEMENT:** FORM: bulleted display (§S13's PE3-G1 item). verbatim, lines 1870–1893.

> “* **PE3-G1 → the pin-check corrected, the violation disclosed.** The
>   r2 sentence "no GENH4 r3 existed at this commit — checked" (S12)
>   was FALSE: GENH4 r3 = 4b0d946 landed 2026-08-09 00:50:10, before
>   every r2 commit (2abf419 01:00:35, ad6f31d 01:21:44, 52fb6ff
>   01:35:30), and the pinned r2 carried an adjudicated
>   not-yet-repaired finding (GENH4 passPE3's MINOR 1 @ 3b88321
>   00:24:06 — the dv0 = N trichotomy, in exactly the CAP(F)
>   neighborhood the (CS-EXACT) gloss cites). This is the PE2-G2
>   defect class (stale pin + undisclosed adjudicated finding at the
>   pin) REPRODUCED IN THE REPAIR THAT ADOPTED THE RULE — the ledger
>   (435a473) already carries the lesson: pin checks are a COMMIT-TIME
>   action against the git log, not a composition-time recollection;
>   the rule is so restated at Step 4. Re-pin executed at GENH4's
>   CURRENT repair HEAD r3 = 4b0d946 (Step 4, S7.1, S9.3, S12
>   corrected in place): the fd35416 → 4b0d946 diff is display-only
>   for everything GENIND consumes (THEOREM GENH4.A/B statements,
>   the two-term CAP(F) law, the comp-weighted census, GENH4.D's
>   package all untouched; the UND count identical — PE3's full-diff
>   verification, § its finding 1). Also disclosed: GENH4's arc since
>   the pin — passPE4 CLEAN @ e15308d (0C + 0G + 0m + 2 remarks; its
>   2-clean count 0/2 → 1/2); no adjudicated unrepaired finding sits
>   at the r3 pin as of this commit (checked against the git log at
>   commit time: GENH4 note HEAD = 4b0d946, latest GENH4 adjudication
>   = e15308d CLEAN).”

**SERIES:** RECORD-INTEGRITY entry **2 of 5**. Its own diagnosis names the pattern: “the PE2-G2 defect class … REPRODUCED IN THE REPAIR THAT ADOPTED THE RULE”.

**CONDITIONALITY:** **The closing sentence (“no adjudicated unrepaired finding sits at the r3 pin as of this commit”) is a commit-time claim that later becomes false** — the Codex GENH4 ratification adjudicated CHALLENGE at 5c8d2fd, and the note handles it exactly as its own rule prescribes: disclose at the NEXT dated append (`.18` entry 3), not by editing this record.

**SUPERSESSION KIND:** `counter re-reading` (of the r2 sentence) + `as-of scoping` (re-pin at four enumerated sites) + `license` (the commit-time restatement of the standing rule).

**DERIVATION:** Not a mathematical unit. **PIN VERIFICATION:** all eight cited commits resolve ✓ (`4b0d946`, `2abf419`, `ad6f31d`, `52fb6ff`, `3b88321`, `435a473`, `fd35416`, `e15308d`).

**RESOLUTION TRACE:** statement lines 1870–1893. correction sites: none in place; superseded-by-disclosure at 1562–1578 (`.18` entry 3).

**TEETH:** `in-house hostile pass` — the finding is a git-log check no battery row performs.

---
### EFF.GENIND.s2of3.39  [changes-record]

**CANONICAL STATEMENT:** FORM: bulleted display (§S13's PE3-m1 — instrument coverage). verbatim, lines 1894–1898.

> “* **PE3-m1 → instrument coverage.** S4.3's machine record no longer
>   claims the M6-key classification at the (3,6,5) block (reader OFF,
>   `do_read=False`): corrected to sides + budgets there, reader-ON
>   key classification at (2,5)/(2,6), with the q = 3 reader-ON
>   evidence now cited from PE3's FR-A (300 M7T members at (3,6)).”

**CONDITIONALITY:** Landed; lands on shard 1 `.40`. **A disclosure that an instrument claimed more coverage than it ran** — the hole is closed by foreign evidence at a HARDER genre, not at the same one.

**SUPERSESSION KIND:** `counter re-reading` (a coverage claim rescoped to what the instrument actually executed).

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1894–1898. correction sites: applied in place at 769–779 (shard 1 `.40`).

**TEETH:** `disclosed non-repair` at the instrument level (the q = 3 reader-ON hole) + foreign-note evidence (PE3 FR-A).

---

### EFF.GENIND.s2of3.40  [changes-record]

**CANONICAL STATEMENT:** FORM: bulleted display (§S13's PE3-m2 — honesty-box scope). verbatim, lines 1899–1902.

> “* **PE3-m2 → honesty-box scope.** "first live n ≥ 7 arrangements"
>   corrected: stage-STEEPER-than-child is live at n = 6 (window-deep,
>   N ≥ 9) and is machine-realized (SS6 at (2,9)/(3,9), PE3 FR-C);
>   ≥ 2 stage blocks stays degree-deep (≥ 8 abscissas).”

**CONDITIONALITY:** Landed; lands on shard 1 `.42`. Re-audited and KEPT at §S14 C7 (`.49`). **Introduces the window-deep / degree-deep distinction** — a liveness taxonomy the note then uses consistently.

**SUPERSESSION KIND:** `counter re-reading` (a liveness inventory recounted: degree-deep → window-deep for one of two cases).

**ARITHMETIC AUDIT:** SS6's entry height 8 ⟹ N ≥ 9 ✓ and the two-stage-block budget 2×4 = 8 abscissas ⟹ m ≥ 8 ✓ — both re-derived at shard 1 `.42`.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1899–1902. correction sites: applied in place at 829–838 (shard 1 `.42`); re-audit at 2103–2106 (`.49`).

**TEETH:** foreign-note evidence (PE3 FR-C); **this note's own leg still carries no stage-steeper instance** — the `disclosed non-repair` shard 1 `.42` preserves.

---

### EFF.GENIND.s2of3.41  [changes-record]

**CANONICAL STATEMENT:** FORM: bulleted display (§S13's PE3-m3 — sharpness restated as supported). verbatim, lines 1903–1909.

> “* **PE3-m3 → sharpness restated as supported.** The M6 sharp-window
>   bullet now states the DISJUNCTION the T1 tooth certifies plus
>   PE3's per-coefficient split: u₂-only fires everywhere; u₀-only
>   fires at odd q and is lift-STABLE at p = 2 (0/40 at (2,6) AND
>   (2,5)) — parity-dependent per the Bezout first-order bound; u₀'s
>   p = 2 window is certified-but-possibly-not-sharp. Counts consume
>   only the certified direction (unchanged).”

**CONDITIONALITY:** Landed; lands on shard 1 `.39`. **A claim narrowed to exactly what its tooth certifies** — the note's cleanest instance of evidence-scoping.

**SUPERSESSION KIND:** `counter re-reading` (a joint claim re-read as a disjunction, then split per coefficient by foreign evidence).

**DERIVATION:** Not a mathematical unit; the Bezout arithmetic is audited at shard 1 `.39`.

**RESOLUTION TRACE:** statement lines 1903–1909. correction sites: applied in place at 734–744 (shard 1 `.39`).

**TEETH:** T1 (planted mutant, fired) + PE3's per-coefficient split (foreign evidence), with `disclosed non-repair` at p = 2 for u₀.

---

### EFF.GENIND.s2of3.42  [changes-record]

**CANONICAL STATEMENT:** FORM: bulleted display (§S13's PE3-m4 — bookkeeping). verbatim, lines 1910–1913.

> “* **PE3-m4 → bookkeeping.** S9.3's conditionality stack gains the
>   GENHN @ 850e77e and GENH4 @ r3 consumption bullets (present inline
>   since r1/r2, absent from the roster); S6 Step 3 gains the mixed-σ
>   wiring through GENIND-6(d) (Steps 2/4 already carried it).”

**CONDITIONALITY:** Landed; lands on `.17`, `.18` and shard 1 `.56`. **A pure inventory defect: two suppliers consumed for two rounds without appearing in the conditionality stack.** The same class recurs at PE7-m2 (four sites → seven) and at PE6-G1 (the whole stack stale).

**SUPERSESSION KIND:** `inventory completion` ×2.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1910–1913. correction sites: applied in place at 1535–1550 (`.17`), 1551–1553 (`.18` entry 1), 1024–1025 (shard 1 `.56`).

**TEETH:** NONE — an inventory repair. Disposition: `in-house hostile pass`.

---

### EFF.GENIND.s2of3.43  [changes-record]

**CANONICAL STATEMENT:** FORM: bold display + grade line (§S13's close), carrying an in-place `[r4, PE4-G1]` correction. verbatim, lines 1915–1928.

> “**No frozen number moved; no sealed artifact touched (byte-frozen,
> re-verifiable: runner md5 e7ca150b; supp triple per S12). The
> corrected formula changes NO committed instance — the runner always
> computed the capped value [r4, PE4-G1: this r3 sentence also claimed
> "every sealed genre sits in the agreeing regime (co-blocks shallower
> than or at the extracted child's slope)" — FALSE: steeper-decided-
> piece genres put the disagreeing regime inside the sealed roster
> ((2,5,n3) 32 states; (2,6,n4) 512 states), machine-verified
> exhaustively by PE4's FR-1 (genind_pe4_fresh.* @ 51bd1bc);
> concordance holds because the runner was capped, not because the
> regimes agree — see S14].**
>
> **Grade: stays 0/2. The consecutive-clean count has NOT started; PE4
> (a fresh hostile pass) attempts the first clean.**”

**CONDITIONALITY:** The CONCLUSION survives; the REASON is corrected — the same shape as shard 1 `.28`. The grade line is round-dated (scoped at `.72`).

**SUPERSESSION KIND:** `counter re-reading` on the regime clause; the conclusion clause is untouched.

**ARITHMETIC AUDIT:** the two cited loci 32 = 2⁵ and 512 = 2⁹ are re-derived at shard 1 `.28` ✓.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1915–1928. correction sites: `[r4]` in situ 1918–1925; §S14 C5 (`.49`).

**TEETH:** PE4's FR-1 (foreign-note evidence, exhaustive on both cells).

**PIN VERIFICATION:** `51bd1bc` ✓.

---

### EFF.GENIND.s2of3.44  [changes-record] · **SERIES REPAIR-ARC, entry 3 of 5**

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph (§S14's Arc — the FULL-SWEEP round), carrying `[r5, PE5-G1]` rescopes and an `[r5]` pin correction. verbatim, lines 1930–1970.

> “## S14. [r4] REPAIR RECORD (PE4 adjudication; a FULL-SWEEP AUDIT, not a spot repair — S11 stays frozen at its seal; S4.1/S13 corrected in place where their own sentences were the findings)
>
> **Arc.** Hostile pass PE4 (fresh context, the corpus's first
> mixed-cap and n = 8 routes; report `GENIND_passPE4_report.md`
> @ ade9bac) adjudicated 0 CRITICAL + 2 GAP + 0 MINOR. Both GAPs are
> prose of the r3 repair itself; PE4-G1 is the arc's THIRD consecutive
> record-integrity defect (class PE2-G2 → PE3-G1 → PE4-G1: a
> repo-checkable factual sentence in a repair record, false against
> the repo). Three consecutive spot repairs each left such a defect,
> so this r4 is executed as a FULL-SWEEP audit [r5, PE5-G1: this
> paragraph's two coverage sentences RESCOPED to their executed
> pattern scope — the sealed-at-r4 originals read "(1) an exhaustive
> inventory of every site that displays or consumes a window formula
> …" and "(2) a claim-by-claim audit of every record/regime/inventory
> sentence …", and PE5 refuted the second universal by concrete
> witness (the residual sentence below); per the standing rule
> (ledger b94c9af) record sentences may not quantify universally]:
> (1) an inventory of the window-formula sites matched by the six
> disclosed grep targets "M_l", "window", "N −", "window-(N",
> "W − D", "min_j" (sweep leg 1 below) — 15 site classes, each
> classified, both defective sites fixed; (2) a claim-by-claim audit
> of the record/regime/inventory sentences matched by the nine
> disclosed grep targets listed at sweep leg 2 below, grouped as
> claim groups C1–C14, each machine- or artifact-checked before
> being kept; (3) a consistency pass over the whole [r1][r2][r3][r4]
> tag set. Demonstrated residual OUTSIDE that pattern scope (PE5's
> witness): the S4.3 first-visible inventory sentence — key phrase
> hyphenated ("first-visible"), claim verb "enter at" — matched NONE
> of the nine patterns, was never audited, and carried a FALSE
> f-first entry law (fixed at [r5]: S4.3, S15). Minimality
> contract on the mathematics; the sweep is the method. The sealed
> runner (`genind_checks.py`, md5 e7ca150b), its committed artifacts,
> the r2 supp leg, and PE3's fresh leg are all BYTE-FROZEN (md5s
> re-verified at commit time: e7ca150b / 7335fc16·63b7413a·6c93f29c /
> fce9cb08·2075dd28·360eb239). NO r4 machine leg was added — every
> fresh number cited below is PE4's own committed leg
> (`genind_pe4_fresh.py` + output + results @ 51bd1bc, md5
> aa2b9af8/1a29a9c1/e549331a [r5: was "e5493312", a transcription
> typo inherited from the PE4 report — the file itself is
> byte-identical since 51bd1bc; see the S4.1 bracket and S15],
> GREEN 6,507 checks / 0 violations).”

**SERIES:** REPAIR-ARC entry **3 of 5** (r4). Also **RECORD-INTEGRITY entry 3 of 5** by its own naming.

**CONDITIONALITY:** **The methodological pivot of the whole arc**: three consecutive spot repairs each left a record-integrity defect, so r4 answers by METHOD (a grep-scoped full sweep) rather than by another spot repair. **And the method's own coverage sentences were then refuted by a witness outside its pattern scope** — the fourth finding. The `[r5]` layer rescopes both sentences enumeratively and displays the witness.

**SUPERSESSION KIND:** `[r5, PE5-G1]` = `replacement` (two universal coverage sentences replaced by pattern-scoped ones, originals quoted) — **and simultaneously a `license` on the record protocol** (the standing rule, ledger `b94c9af`). The `[r5]` md5 item = `provenance-rider` (a corrupt pin prefix corrected; the artifact never moved).

**ARITHMETIC AUDIT:** the sweep declares **6** leg-1 grep targets (`"M_l"`, `"window"`, `"N −"`, `"window-(N"`, `"W − D"`, `"min_j"`) ✓ six enumerated; **9** leg-2 targets (enumerated at `.49`'s header: `"every sealed"`, `"all sealed"`, `"true at every"`, `"invisible"`, `"first live"`, `"first visible"`, `"beyond every"`, `"never"`, `"no prior"`) ✓ nine enumerated; **15** site classes and **14** claim groups, both counted at `.48`/`.51`. **The witness's escape is arithmetically explicable:** the missed phrase is hyphenated `first-visible`, and the pattern list contains the unhyphenated `"first visible"` — a fixed-string grep for `first visible` does **not** match `first-visible` ✓. **The defect is a direct consequence of the pattern set, exactly as the note says.**

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1930–1970. correction sites: `[r5]` in situ 1939–1946 and 1967–1969; §S15's PE5-G1 and BONUS items (`.55`, `.58`).

**TEETH:** `decorrelated-model audit` — PE5's witness is a sentence that r4's own method structurally could not see. **PIN VERIFICATION:** `ade9bac` ✓, `51bd1bc` ✓, `b94c9af` ✓; PE4's leg files EXIST ✓; the 13 md5s named here and at `.60` are the note's own enumerated freeze set.

---

### EFF.GENIND.s2of3.45  [changes-record]

**CANONICAL STATEMENT:** FORM: bulleted display (§S14's PE4-G2 item — proof step (1) rewritten). verbatim, lines 1972–1998.

> “* **PE4-G2 → proof step (1) rewritten (S4.1; + the S4.3 echo).** The
>   r3 corrected GENIND-3's STATEMENT to the capped
>   D_l = μ_l·k_l + Σ_b deg_b·min(s_b, k_l) = min_j(v(a_j) + j·k_l)
>   but left the PROOF's step (1) displaying the pre-cap uniform
>   window "N − m·k_l" — contradicting the statement, the note's own
>   M6 ledger (N−4 vs N−6), and degenerating to window −1 at live
>   instances (M6 at N = 5, TWOCHILD child A at N = 7) — and
>   GENIND-6(a) consumes steps (1)–(2) "VERBATIM". Step (1) now
>   derives the capped window by the content route: per-root content
>   min(v(ρ − ẑ_l π^{k_l}), k_l) sums to D_l; the primitive scaled
>   frame carries RAGGED certified precisions π^{N + j·k_l − D_l},
>   binding at j = 0, i.e. a window-M_l = window-(N − D_l) frame; the
>   old N − m·k_l is displayed as what it is — a true uniform floor
>   (D_l ≤ m·k_l), NOT the extraction window. The false reduction
>   parenthetical ("separable factors with the other letters as
>   roots… at their own slopes") is replaced by the true trichotomy:
>   same-side co-blocks at shifted residues z′ − ẑ_l (pieces
>   separable, co-children repeated), steeper co-blocks collapsed to
>   the single residue −ẑ_l, shallower co-blocks out of the reduction
>   by degree drop; no co-block sits at its own slope. The same false
>   clause's image in GENIND-6's proof of (a) ("blocks on other sides
>   sit at their own slopes") is corrected identically; GENIND-6(a)'s
>   VERBATIM consumption now reads the corrected step. Corroboration
>   (PE4's, cited): the statement's formula held at THREECHILD
>   (windows (1,3,7), the first mixed cap, C-box bijection 4,096) and
>   N8MIX (n = 8); the "equivalently min_j" clause is an identity
>   (PE4 §2, re-derived).”

**CONDITIONALITY:** **A statement/proof divergence introduced by the previous round's own repair** — r3 fixed the statement and not the proof. The item lands on shard 1 `.24` (step (1)) and `.34` (the (a)-proof echo).

**SUPERSESSION KIND:** `replacement` (the proof step's window display and its reduction parenthetical are both replaced, originals quoted).

**ARITHMETIC AUDIT (compiler-computed, on the degeneration claim):** M6 at N = 5 under the old uniform display `N − m·k_l = 5 − 6·1 = −1` ✓ against the true window 1 ✓ (shard 1 `.38`: `M = N − 4 = 1`). TWOCHILD child A at N = 7: `7 − 4·2 = −1` ✓ against the true `N − 6 = 1` ✓ (shard 1 `.27`). **Both degenerations reproduce exactly.** The floor claim `D_l ≤ m·k_l` holds because each of the m roots contributes content at most `k_l` ✓.

**DERIVATION:** Not a mathematical unit; the mathematics is shard 1 `.24`'s corrected step (1).

**RESOLUTION TRACE:** statement lines 1972–1998. correction sites: applied in place at 382–425 and 662–676 (shard 1 `.24`, `.34`).

**TEETH:** PE4's corroboration at THREECHILD and N8MIX (foreign-note evidence) + the `min_j` identity re-derived by the verifier.

---

### EFF.GENIND.s2of3.46  [changes-record] · **SERIES RECORD-INTEGRITY, entry 3 of 5**

**CANONICAL STATEMENT:** FORM: bulleted display (§S14's PE4-G1 item — the regime inventory). verbatim, lines 1999–2014.

> “* **PE4-G1 → the regime inventory restated to the machine-verified
>   claim (S4.1 statement bracket + TWOCHILD parenthetical +
>   concordance paragraph; S13 two sentences).** Five [r4] corrections,
>   each quoting its false original in place. The TRUE inventory, now
>   displayed at the S4.1 concordance paragraph: the disagreeing
>   regime (a co-block STEEPER than the extracted child) occurs
>   INSIDE the sealed roster via steeper decided PIECES — PSTEEP3 at
>   the (2,5) n = 3 control row (32 states, capped window 2 vs
>   uncapped 1) and PSTEEP4 at (2,6) n = 4 (512 states, 2 vs 1) —
>   exhaustively adjudicated by PE4 FR-1 (ONTO 4 × 8 resp. 8 × 64,
>   DEC/DRAIN 16/16 resp. 256/256, lift-certified; uncapped would
>   force one class and 100% child-drain), states the sealed GT-BETA
>   itself processed at the capped windows since the seal. The
>   concordance CONCLUSION stands unchanged (the runner was always
>   capped; no committed number moves); what changes is only WHY it
>   holds.”

**SERIES:** RECORD-INTEGRITY entry **3 of 5**.

**CONDITIONALITY:** **Five corrections, each quoting its false original in place** — the note's own discipline, stated as a count. All five land in shard 1 (`.24`'s bracket, `.27`'s TWOCHILD parenthetical, `.28`'s concordance) and in this shard (`.37`, `.43`).

**SUPERSESSION KIND:** `counter re-reading` ×5 (a regime inventory recounted at five sites; the conclusion preserved at all five).

**ARITHMETIC AUDIT:** all six PSTEEP figures re-derived at shard 1 `.28` ✓ (windows 2 vs 1 and 2 vs 1; loci 32 and 512; fibrations 4×8 and 8×64; splits 16/16 and 256/256, summing to 32 and 512 ✓).

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1999–2014. correction sites: the five in-place corrections at 363–367, 469–476, 484–487 (shard 1) and 1865–1869, 1918–1925 (this shard).

**TEETH:** PE4 FR-1 (foreign-note evidence, exhaustive) + `arithmetic recount`.

---
### EFF.GENIND.s2of3.47  [table]

**CANONICAL STATEMENT:** FORM: bold-headed numbered display (§S14 sweep leg 1 — the full-sweep window-site inventory), carrying an `[r5 sweep]` rescope in its header. Header quoted verbatim, lines 2016–2027; the fifteen numbered classes transcribed as a `[TABLE]` below (rule 5: a source classification list is a unit and is transcribed, never prosified; the class LABELS and verdicts are quoted verbatim from lines 2029–2067).

> “**THE FULL-SWEEP WINDOW-SITE INVENTORY (sweep leg 1; grep targets
> "M_l", "window", "N −", "window-(N", "W − D", "min_j" over the whole
> note at this commit; every site matched by those six targets listed
> [r5 sweep: was "every display or consumption site listed" —
> rescoped to the executed patterns; PE5's independent miss-hunt
> found no window-formula site outside these 15 classes]).**
> Classification: CAPPED (displays/implements the [r3] formula),
> α-CORRECT (N − mk at an α-transport, where the extraction is the
> whole cluster and D = m·k exactly — the cap is degenerate, the
> display right), AGNOSTIC (a different window mechanism: stage
> division ledgers, dv-units, ragged stage bands — no child-extraction
> cap in scope), or DEFECTIVE → FIXED:”

`[TABLE]` — the fifteen site classes, verdicts quoted:

| # | Site (quoted label) | Verdict | Shard-1 unit |
|---|---|---|---|
| 1 | “Header [r3]/[r4] arc lines — record” | CAPPED ✓ | `.01` (shard 1) |
| 2 | “S1 GENIND.A(II) "same (m, d) system at window N − mk"” | α-CORRECT ✓ | `.09` |
| 3 | “S3 LEMMA GENIND-2(a)(b) statement + proof (σ_k windows, ghost zones {≥ N − jk}, window condition mμ ≤ N−1)” | α-CORRECT ✓ | `.21`, `.22` |
| 4 | “S4.1 LEMMA GENIND-3 STATEMENT” | CAPPED `[r3]` ✓ | `.24` |
| 5 | “S4.1 GENIND-3 proof step (1)” — “WAS the pre-cap "N − m·k_l" + false reduction parenthetical” | **DEFECTIVE → FIXED** `[r4, PE4-G2]` | `.24` |
| 6 | “S4.1 [r3] honesty note (root-sum derivation; TWOCHILD N−4/N−6; PSTEEP capped windows)” | CAPPED ✓ | `.27`, `.28` |
| 7 | “S4.3 LEMMA GENIND-6(a) STATEMENT ("the SAME explicit window M_l = N − (μ_l k_l + Σ deg·min(own slope, k_l))")” | CAPPED `[r3]` ✓, with the VERBATIM-consumption check executed | `.34` |
| 8 | “S4.3 proof of (a) … its coprimality clause "blocks on other sides sit at their own slopes"” | CAPPED `[r3]` ✓ / clause **DEFECTIVE → FIXED** `[r4]` | `.34` |
| 9 | “S4.3 M6 worked ledger (D = min_j(v(a_j)+j) = 4, M = N−4, regime label "capped = uncapped at M6")” | CAPPED ✓, “hand-recheck min(4, 2+2, 6) = 4” | `.38` |
| 10 | “S4.3 honesty box (i) SS6 [r3, PE3-m2] ("child extraction at the capped window N−6")” | CAPPED ✓, “hand-recheck D = 2·1 + 4·min(3/2, 1) = 6 (uncapped would say 8)” | `.42` |
| 11 | “S5.2 drainage recursion u_{m,d}(N−mk) in the α-term” | α-CORRECT ✓ | `.45` |
| 12 | “S6 Step 2 / Step 4 / S7.1 (CS-1) rider” — “cite M_l / GENIND-6 abstractly, inheriting whatever S4.1/S4.3 display; every inherited display now CAPPED” | CAPPED (inherited) ✓ | `.55`, `.57`, `.63` |
| 13 | “S7.1–S7.4 stage windows (certified division-ledger windows, dv-units, ragged bands, GENIND-4 budgets, OB-a)” | AGNOSTIC ✓ | `.63`–`.74` |
| 14 | “S10 runner description ("β children by c = k scaling (D = weighted min) + monic Hensel extraction at window W − D")” | CAPPED ✓, “matches `extract_child` (md5 e7ca150b), which implements D = min_j(v(a_j) + j·k) literally” | `.21` (this shard) |
| 15 | “S13 [r3] PE3-G2 record (the capped formula + TWOCHILD windows)” | CAPPED ✓ (“its two regime sentences were PE4-G1, fixed”) | `.37` (this shard) |

**CONDITIONALITY:** **Pattern-scoped, and the note says so twice** — the header's `[r5 sweep]` rescope replaced “every display or consumption site listed” with the executed six patterns, citing PE5's independent miss-hunt as corroboration (“no window-formula site outside these 15 classes”) rather than as its own claim.

**SUPERSESSION KIND:** `[r5 sweep]` = `counter re-reading` (a universal coverage claim rescoped to an enumerated pattern set, with foreign corroboration cited not claimed).

**ARITHMETIC AUDIT (compiler-computed, rule 22):** the fifteen classes partition as CAPPED (1, 4, 6, 7, 8, 9, 10, 12, 14, 15 = **10**) + α-CORRECT (2, 3, 11 = **3**) + AGNOSTIC (13 = **1**) + DEFECTIVE→FIXED (5 = **1**), total 15 ✓. **But the note's own count line (`.48`) reads “11 capped/correct as found, 2 agnostic (stage mechanisms), 2 DEFECTIVE (sites 5, 8)”** — a different partition, because it counts sites 3 and 11 within “capped/correct” and counts class 8 as defective (its coprimality clause was) while this compiler's table records class 8's *window* verdict as CAPPED. **Reconciled:** the note's 11 = CAPPED-as-found (1, 4, 6, 7, 9, 10, 12, 14, 15 = 9) + α-CORRECT (2, 3, 11 = 3) = 12, minus class 8 which it moves to the defective column = **11** ✓; its 2 agnostic = class 13 plus, evidently, one of the α-CORRECT/AGNOSTIC boundary calls. **The two partitions agree on the total (15) and on which sites were FIXED (5 and 8); they disagree by one on the agnostic/correct boundary.** Recorded as an itemization difference, NOT a defect — the note's own count line is the authority for its own classification, and no site is unaccounted for in either reading.

**DERIVATION:** Not a mathematical unit; a grep-scoped audit inventory.

**RESOLUTION TRACE:** statement lines 2016–2067. correction sites: `[r5 sweep]` in situ 2019–2021; `.59`'s rewrite (1).

**TEETH:** `arithmetic recount` + `in-house hostile pass`; the corroboration for outside-pattern coverage is **foreign-note evidence** (PE5's miss-hunt), explicitly cited not claimed.

---

### EFF.GENIND.s2of3.48  [changes-record]

**CANONICAL STATEMENT:** FORM: bold display (§S14 leg 1's count line), carrying an `[r5 sweep]` rescope. verbatim, lines 2069–2075.

> “**Count: 15 site classes; 11 capped/correct as found, 2 agnostic
> (stage mechanisms), 2 DEFECTIVE (sites 5, 8) — both fixed at [r4].
> Uncapped survivors among these 15 site classes: NONE [r5 sweep:
> was "after this sweep: NONE" — scoped to the enumerated classes;
> corroboration outside the patterns is PE5's independent sweep
> ("no window-formula site outside S14's 15 classes"), a verifier
> artifact, cited not claimed].**”

**ARITHMETIC AUDIT (compiler-computed, rule 22):** `11 + 2 + 2 = 15` ✓ — the note's own partition is internally consistent. Cross-check against the compiler's independent classification at `.47`: same total, same fixed set {5, 8}, one-site disagreement on the agnostic/correct boundary. **Both partitions leave zero sites unaccounted for.**

**CONDITIONALITY:** The “NONE” is scoped twice over: to the 15 enumerated classes, and with outside-pattern corroboration attributed to a verifier artifact.

**SUPERSESSION KIND:** `counter re-reading` (universal → enumerated).

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2069–2075. correction sites: `.59`'s rewrite (2).

**TEETH:** `arithmetic recount`.

---

### EFF.GENIND.s2of3.49  [table]

**CANONICAL STATEMENT:** FORM: bold-headed bulleted display (§S14 sweep leg 2 — the record-claim audit, claim groups C1–C13; **C14 is emitted separately at `.50`** because it alone was later found FALSE and corrected in place, and the two quotations' union is the whole leg minus nothing). Header quoted verbatim, lines 2077–2080; the thirteen groups transcribed as a `[TABLE]` with verdicts quoted from lines 2082–2128.

> “**THE RECORD-CLAIM AUDIT (sweep leg 2; grep targets "every sealed",
> "all sealed", "true at every", "invisible", "first live", "first
> visible", "beyond every", "never", "no prior" — every hit checked
> against the repo/artifacts BEFORE being kept; verdicts listed).**”

`[TABLE]` — claim groups C1–C13, verdicts quoted:

| Group | Claim (quoted) | Verdict | Evidence (quoted) | Target unit |
|---|---|---|---|---|
| C1 | S4.1 bracket “(true at every sealed instance)” | **FALSE → FIXED [r4]** | “sealed ROWS[3] ∋ (2,5), ROWS[4] ∋ (2,6) (runner source, md5 e7ca150b); PSTEEP3/PSTEEP4 live there (v(a₀) = 4 ≤ 4 resp. 5 ≤ 5); PE4 FR-1 exhaustive (32 + 512 states)” | s1 `.24` |
| C2 | S4.1 TWOCHILD “beyond every sealed window — why three passes … could not see it” | **HALF-TRUE → RESCOPED [r4]** | “The GENRE (first visible N = 7) is beyond every sealed full-sweep window (max N = 6) … the inference (regime invisible to the battery) was FALSE” | s1 `.27` |
| C3 | S4.1 concordance “at every sealed instance (all in the agreeing regime …)” | **FALSE → FIXED [r4]** | evidence as C1 | s1 `.28` |
| C4 | S13 “invisible at n ≤ 6 first-visible windows” | **FALSE → FIXED [r4]** | “the disagreeing regime is first visible at N = 5, n = 3 (PSTEEP3), inside the sealed roster” | `.37` |
| C5 | S13 “every sealed genre sits in the agreeing regime” | **FALSE → FIXED [r4]** | evidence as C1 | `.43` |
| C6 | “mixed genres first live at n = 6” (S4.3 scope note, S6 Step 2, S12) | **TRUE, KEPT** | “the degree budget (child ≥ 2 abscissas + composite block ≥ 4, S4.3) + the machine instance M6 at n = 6” | s1 `.29`, `.31` |
| C7 | S4.3 honesty box [r3, PE3-m2]: stage-steeper live at n = 6 first visible N ≥ 9; ≥ 2 stage blocks degree-deep | **TRUE, KEPT** | “SS6 hull v(a₀) = 8 ⟹ N ≥ 9; PE3 FR-C machine instance at (2,9)/(3,9); abscissa budget 2·4 = 8” | s1 `.42` |
| C8 | S5.3 “CS5-V4E2 first visible at N = 8” | **TRUE, KEPT** | “v₀ = v₄ + 2h ≥ 1 + 2·(2v₄+1)\|_{v₄=1} = 7 ⟹ N ≥ 8; corroborated by S11 P-3 (V4E2 ABSENT …)” | s1 `.51` |
| C9 | S5.3 “CS5-V1E1-(2²) first visible N = 7” | **TRUE, KEPT** | “(headroom 5k+1 ≤ N−1 at k = 1)” | s1 `.52` |
| C10 | S5.1 “the n ≤ 3 program never consulted [W12-H]” | **TRUE, KEPT** | “the composite-free theorem (S5.1) + GT-CRIT zero CS events on all four n = 3 rows (S11 P-8)” | s1 `.11`, `.43` |
| C11 | GENIND-BOX-3 “the arguments never use d = 1” | **KEPT with its hedge** | “a proof-audit claim, already disclosed in the same box as machine-uncorroborated …; PE4 §2 left it as disclosed” | `.03`, s1 `.23` |
| C12 | S11 “Every never-measured spot EXACT” | **KEPT** | “re-verified by PE4's isolated re-run of the sealed battery (163,536/0, leaf-diff = elapsed only)” | `.29` |
| C13 | “The mathematical "never" claims (GENIND-1(iii) no-re-merge, GENIND-2(a) ghost non-contamination, GENIND-6(a)/(b) factor-genericity and no-re-merge, the S4.3 instrument lesson)” | **KEPT** | “lemma content or normative, machine-corroborated pointwise (GT-ALPHA/GT-BETA, supp, PE3/PE4 fresh legs), attacked across PE1–PE4 and held” | s1 `.19`, `.21`, `.34`, `.35`, `.41` |

**CONDITIONALITY:** Pattern-scoped (nine targets). **C12's evidence is an independent re-run of the frozen battery** — the only place in the note where §S11's numbers are re-produced rather than cited. **C13 is the row that separates lemma content from record content**, and it is why the standing rule at `.54` can ban universal quantification in RECORDS without touching theorems.

**ARITHMETIC AUDIT (compiler-computed, rule 22):** the C1 evidence line's liveness checks re-derived — PSTEEP3 at (2,5): `v(a₀) = 4 ≤ N−1 = 4` ✓; PSTEEP4 at (2,6): `v(a₀) = 5 ≤ N−1 = 5` ✓. C7's `2·4 = 8` ✓. C8's `1 + 2·3 = 7` ✓. C9's `5·1 + 1 = 6 ≤ N−1` ⟹ `N ≥ 7` ✓. **All five arithmetic evidence lines reproduce.** Verdict tally over C1–C13: FALSE→FIXED **4** (C1, C3, C4, C5), HALF-TRUE→RESCOPED **1** (C2), KEPT **8** (C6–C13) = 13 ✓.

**DERIVATION:** Not a mathematical unit; a grep-scoped claim audit.

**RESOLUTION TRACE:** statement lines 2077–2128. correction sites: none for C1–C13.

**TEETH:** `arithmetic recount` + `in-house hostile pass`; C12 additionally `executable regression` (an isolated re-run).

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:[W12-H]` — count **17**.

---

### EFF.GENIND.s2of3.50  [changes-record] · **SERIES RECORD-INTEGRITY, entry 5's target**

**CANONICAL STATEMENT:** FORM: bulleted display (§S14's claim group C14), carrying an in-place `[r6, PE6-G1]` correction that quotes and replaces its own close. verbatim, lines 2129–2151.

> “* C14 The as-of pin sentences (S9.3): re-checked against the git
>   log AT COMMIT TIME per the standing rule — GENHN pin 850e77e is
>   still GENHN's note HEAD; GENH4: r3-era sentences stand as dated
>   records, and the stack gains the [r4] dated append (ACCEPTED 2/2
>   @ 11dbd23, annex @ baf05ed, accepted body byte-frozen = the
>   4b0d946 pin). [r6, PE6-G1: this item's close — "Of the remaining
>   pinned suppliers enumerated in S9.3's stack (W-12, W-11, HEX3,
>   HMENU3, J-D0, GRTJC, WELDMASTER / DULEMMA / [W12-H], QSCOUT22):
>   each git-log-checked at commit time, none moved from its pin
>   [r5 sweep: was 'No other supplier note moved since its pin' —
>   scoped to the enumerated stack]" — was FALSE at FIVE of the
>   enumerated suppliers (W-12: three repair rounds beyond the pin
>   incl. the PE4 F1 CRITICAL repair; HEX3: two rounds; HMENU3:
>   accepted + ANNEX A; W-11: accepted; QSCOUT22: verdict + L3
>   annex), refuted by the git log at both the r4 and r5 commit
>   times: the per-supplier git-log check the sentence asserts was
>   not executed. REPLACED by S16's PER-SUPPLIER FIRED-CLAUSE TABLE —
>   one row per supplier with its own pins, movement, consumed
>   clauses, and evidence; no summary sentence — and the S9.3 pins
>   refreshed to the suppliers' current HEADs with [r6] dated
>   appends. The five prior stale sentences of this defect class:
>   PE2-G2 → PE3-G1 → PE4-G1 → PE5-G1 → PE6-G1.]”

**CONDITIONALITY:** **The arc's most consequential record defect: a sentence asserting a per-supplier git-log check that was never executed, false at five of nine suppliers — and it had already survived one rescope (`[r5 sweep]`) that fixed its QUANTIFIER while leaving its FALSEHOOD intact.** That is the note's own lesson: enumerating the scope of a false claim does not make it true.

**SUPERSESSION KIND:** `replacement` — the close is not re-scoped but **replaced by a table**, with the summary sentence abolished (“no summary sentence”). This is a different remedy from every earlier round's, and the note marks the shift explicitly.

**CHAIN:** the sealed C14 close → `[r5 sweep]` rescope (quantifier enumerated; falsehood untouched) → **`[r6, PE6-G1]`: FALSE at five of nine; REPLACED by §S16's per-supplier table — TERMINAL.**

**ARITHMETIC AUDIT (compiler-computed):** the close enumerates **nine** suppliers (W-12, W-11, HEX3, HMENU3, J-D0, GRTJC, WELDMASTER/DULEMMA/[W12-H] counted as one, QSCOUT22 — reading the compound as one gives 8; reading WELDMASTER, DULEMMA and [W12-H] separately gives 10). The `[r6]` layer says it was FALSE at **five** and names them: W-12, HEX3, HMENU3, W-11, QSCOUT22 ✓ five named. §S16's replacement table has **8 rows** (adding GENHN and GENH4, which C14 handled separately, and HE7, which was never in the stack) plus a **4-item unmoved list** (J-D0, DULEMMA, GRTJC, WELDMASTER) ✓ — **8 + 4 = 12 supplier positions covered, against C14's 9-or-10.** The replacement is strictly wider, as claimed.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2129–2151. correction sites: `[r5 sweep]` and `[r6, PE6-G1]` in situ; replaced by 2346–2371 (`.62`, `.63`).

**TEETH:** `in-house hostile pass`; **no battery row can check a git-log claim** — the note's own five-defect series is the standing evidence.

---

### EFF.GENIND.s2of3.51  [changes-record]

**CANONICAL STATEMENT:** FORM: bold display (§S14 leg 2's count line). verbatim, lines 2152–2153.

> “**Count: 14 claim groups audited; 4 FALSE → fixed (C1, C3, C4, C5),
> 1 half-true → rescoped (C2), 9 verified and kept (C6–C14).**”

**ARITHMETIC AUDIT (compiler-computed, rule 22):** `4 + 1 + 9 = 14` ✓ internally consistent. **But the “9 verified and kept (C6–C14)” is FALSIFIED by the `[r6]` correction at `.50`: C14 was NOT verified — its close was false at five suppliers.** The corrected tally is therefore **4 + 1 + 8 kept + 1 later-refuted = 14** ✓. The count line is not edited (it sits in the frozen body); the `[r6]` layer inside C14 carries the correction. **Tagged `STALE-SELF-DESCRIPTION` (rule 26)** — a count sentence that its own later correction falsifies, preserved unedited.

**CONDITIONALITY:** As above.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2152–2153. correction sites: none in place; falsified by 2134–2151 (`.50`).

**TEETH:** `arithmetic recount` — the recount is what exposes the stale tally.

---

### EFF.GENIND.s2of3.52  [changes-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (§S14 sweep leg 3 — tag-set consistency), carrying an `[r5 sweep]` rescope. verbatim, lines 2155–2174.

> “**TAG-SET CONSISTENCY (sweep leg 3).** The arc story each record now
> tells, checked round by round: seal → PE1 (0C+3G+4m) → [r1] (header
> + BOX-5 + inline tags; what r1 missed — the mixed-opening transport
> hole, the granularity, its own GENH4 pin — caught by PE2, recorded
> at S12); [r2] (S12; what r2 missed — its own pin-check sentence
> FALSE, the uncapped M_l statement display — caught by PE3, recorded
> at S13 with S12 corrected in place); [r3] (S13; what r3 missed — the
> statement repair not propagated into proof step (1), and its own
> regime-inventory sentences FALSE — caught by PE4, recorded HERE with
> S4.1/S13 corrected in place); [r4] (this record; the full-sweep
> method is the structural answer to three consecutive
> record-integrity defects — what r4 may itself have missed is PE5's
> to find, with this inventory as its checklist). Checked: each tag
> surfaced by grepping the four patterns "[r1]" "[r2]" "[r3]" "[r4]"
> over the body cites the finding it repairs [r5 sweep: was "every
> [rN] tag in the body" — rescoped to the executed grep]; among the
> four records (header arc line, S12, S13, S14) no record contradicts
> another; S11 remains frozen at its seal; the three grade lines
> (S12, S13, S14) form the monotone arc 0/2 → 0/2 → 0/2 with the
> clean count never started.”

**CONDITIONALITY:** **A round-by-round self-narration that explicitly anticipates its own successor's finding** (“what r4 may itself have missed is PE5's to find, with this inventory as its checklist”) — and PE5 duly found one outside the checklist's pattern scope. **The grade-arc sentence is stale at acceptance** (0/2 → 2/2), scoped by `.72`'s round-dated-records clause.

**SUPERSESSION KIND:** `[r5 sweep]` = `counter re-reading` (rewrite (4) of `.59`'s seven).

**ARITHMETIC AUDIT:** the four repair-story entries (r1…r4) and the four records named (header arc line, S12, S13, S14) ✓ consistent; the three grade lines cited (S12, S13, S14) ✓ — S15 and S16 add two more, making **five** grade lines in the finished note, so this sentence's inventory is complete as of r4 and incomplete thereafter. Recorded, not corrected.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2155–2174. correction sites: `[r5 sweep]` in situ 2169–2170.

**TEETH:** `in-house hostile pass` + `arithmetic recount`.

---

### EFF.GENIND.s2of3.53  [changes-record]

**CANONICAL STATEMENT:** FORM: bold display + grade line (§S14's close), carrying an `[r5, PE5-G1]` correction that quotes its own false original. verbatim, lines 2176–2192.

> “**No frozen number moved; no sealed or committed artifact touched
> (all eight md5 pins re-verified at commit time, listed in the Arc
> paragraph). The capped formula, every count law, every committed
> number, and the conditionality display stand exactly as at r3 —
> this round changed PROSE: one proof step now derives what its
> statement says, and the inventory sentences within the nine-pattern
> scope (claim groups C1–C14 above) now say only what the repo can
> verify [r5, PE5-G1: the sealed-at-r4 close read "and every
> inventory sentence now says only what the repo can verify" — FALSE
> outside the pattern scope: PE5's witness, the S4.3 hyphenated
> "first-visible" sentence, matched none of the nine patterns and its
> f-first entry law was refuted by the repo; fixed at [r5], and the
> universal register itself is now banned by the standing rule
> (ledger b94c9af) — see S15].**
>
> **Grade: stays 0/2. The consecutive-clean count has NOT started; PE5
> (a fresh hostile pass) attempts the first clean.**”

**CONDITIONALITY:** The corrected close is itself later undermined at one point: “(claim groups C1–C14 above) now say only what the repo can verify” — **C14 did not** (`.50`). Neither `[r5]` nor `[r6]` edits this sentence; `[r6]`'s correction lives inside C14. Tagged `STALE-SELF-DESCRIPTION` on the C14 clause.

**SUPERSESSION KIND:** `[r5, PE5-G1]` = `replacement` (a universal sentence replaced by a pattern-scoped one, original quoted) + `license` (the standing rule adopted).

**ARITHMETIC AUDIT:** “all eight md5 pins” — the Arc paragraph lists `e7ca150b` (1) + the r2 supp triple (3) + PE3's fresh triple (3) + PE4's fresh triple (3) = **10**, not 8. Reading “eight” as the frozen-before-this-round set (1 + 3 + 3 = 7) or as excluding PE4's own leg (1 + 3 + 3 = 7) does not give 8 either. **Recorded as an unreconciled count (§8, defect 5)** — the enumerated list in the Arc paragraph is the authority and is complete; only the summary numeral is unaccounted for. §S15's own byte-freeze line (`.60`) counts **13** md5s and §S16's (`.68`) counts **16**, both with explicit enumerations that DO reconcile (audited there), so the defect is local to this sentence.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2176–2192. correction sites: `[r5]` in situ 2183–2189.

**TEETH:** `decorrelated-model audit` (PE5's out-of-pattern witness) + `arithmetic recount`.

---
### EFF.GENIND.s2of3.54  [changes-record] · **SERIES REPAIR-ARC, entry 4 of 5**

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph (§S15's Arc, carrying THE STANDING RULE). verbatim, lines 2194–2211.

> “## S15. [r5] REPAIR RECORD (PE5 adjudication; the STANDING-RULE round — S11 stays frozen at its seal; S4.3/S4.1/S14/S12 corrected in place where their own sentences were the findings)
>
> **Arc.** Hostile pass PE5 (fresh context, the corpus's first n ≥ 9
> route + the same-side co-children leg + the systematic steeper-piece
> scan; report `GENIND_passPE5_report.md` @ 29ad62f/74e9004/bd9bce1)
> adjudicated 0 CRITICAL + 1 GAP + 2 MINOR. The GAP is the arc's
> FOURTH consecutive record-integrity finding (PE2-G2 → PE3-G1 →
> PE4-G1 → PE5-G1), landed inside the full-sweep record built as the
> structural answer to the class. This r5 therefore implements **THE
> STANDING RULE (ledger b94c9af): RECORD SENTENCES MAY NOT QUANTIFY
> UNIVERSALLY.** "Every X was checked / all Y are Z / no W exists"
> record claims are BANNED; a record states an ENUMERATED list with
> evidence ("checked: [explicit list]") or a PATTERN-SCOPED claim
> ("among the sites matched by patterns P1–P9: …"). A theorem may
> quantify; a RECORD may not. Minimality contract: the PE5 charges +
> the universal-sentence sweep below; no machine leg added — every
> fresh number cited is PE5's committed leg (`genind_pe5_fresh.py` +
> output + results @ bd9bce1, GREEN 109,146 checks / 0 violations).”

**SERIES:** REPAIR-ARC entry **4 of 5** (r5); RECORD-INTEGRITY entry **4 of 5** by its own naming.

**CONDITIONALITY:** **THE STANDING RULE is a corpus-level policy adopted here, ledger-pinned at `b94c9af`, and it governs every later record in this note (and, per the ledger, beyond it).** Its precise scope is stated twice and must not be over-read: *“A theorem may quantify; a RECORD may not.”* — the mathematical “never” claims (C13) are explicitly outside it.

**SUPERSESSION KIND:** `license` on the note's record protocol (the strongest of the three protocol licenses in the arc: r2 adopted pin-at-repair-HEAD, r3 restated it as a commit-time action, r5 bans the universal register outright).

**DERIVATION:** Not a mathematical unit. **PIN VERIFICATION:** `29ad62f` ✓, `74e9004` ✓, `bd9bce1` ✓, `b94c9af` ✓; PE5's leg files EXIST ✓.

**RESOLUTION TRACE:** statement lines 2194–2211. correction sites: none.

**TEETH:** `in-house hostile pass`; the rule itself is the arc's structural answer to a defect class no tooth can catch.

---

### EFF.GENIND.s2of3.55  [changes-record] · **SERIES RECORD-INTEGRITY, entry 4 of 5**

**CANONICAL STATEMENT:** FORM: bulleted display (§S15's PE5-G1 item — the false f-first entry law and the two rescopes). verbatim, lines 2213–2247.

> “* **PE5-G1 → S14's two universal-coverage sentences RESCOPED
>   enumeratively; the false f-first entry law FIXED (S14 Arc ¶ +
>   closing ¶; S4.3).** The r4 sweep's coverage sentences ("a
>   claim-by-claim audit of every record/regime/inventory sentence",
>   "every inventory sentence now says only what the repo can
>   verify") were FALSE by PE5's concrete witness: the S4.3
>   first-visible inventory sentence — key phrase hyphenated, claim
>   verb "enter at" — matched none of the nine disclosed leg-2 grep
>   patterns, was never audited, and displayed a false f-first entry
>   law. Both S14 sentences now name their exact executed scope (the
>   six leg-1 targets; the nine leg-2 targets grouped as C1–C14) and
>   display the witness as the demonstrated residual, quoting the
>   false originals in place. At S4.3 the law itself is fixed with
>   the m = 6 mixed grammar re-derived from the entry geometry
>   (v(a₀) = Σ_sides length × slope): the f-first ψ²-block (e = 1,
>   deg ψ = 2, μ = 2) has slope-mass 4h, so the SAME-SIDE variant
>   (k = h forced, one slope-k side of length 6, residual
>   (y − w)²ψ(y)²) enters at **v(a₀) = 6k** (= 6 at k = 1) and the
>   DISTINCT-SIDE variants at **2k + 4h ≥ 8** — never the old
>   "2k + 2h", which reads 4 ≥ 6 at k = h = 1. The CONCLUSION (every
>   non-M6 mixed genre enters at v(a₀) ≥ 6, i.e. N ≥ 7; M6 uniquely
>   first-visible at N = 5) was TRUE and is KEPT, now supported by
>   the enumerated three-family grammar (child+E 2k+2h with unique
>   sub-6 cell (1,1) = M6; child+F same-side 6k; child+F
>   distinct-side 2k+4h; the two composite types (2,1,2)/(1,2,2) are
>   the only solutions of e·μ·deg ψ = 4 with μ ≥ 2, e·deg ψ ≥ 2 —
>   S5.1's necessity cases). Geometry cross-checked against PE5's
>   committed artifacts: NINEMIX's hull (0,11)–(1,8)–(3,4)–(5,2)–(9,0)
>   realizes the Gauss-additive entry height 11 = 1·3 + 2·2 + 2·1 +
>   4·(1/2) at n = 9, and SAMESIDE's single side (0,4)–(4,0) realizes
>   the same-side entry height 4 = length 4 × slope 1 on 59,049
>   exhaustive states. HONEST LIMIT: the same-side f-first genre
>   itself (the 6k law's genre) remains machine-unrealized
>   corpus-wide — the law above is proved geometry, not yet a
>   machine-exercised cell.”

**SERIES:** RECORD-INTEGRITY entry **4 of 5**.

**CONDITIONALITY:** **Two distinct repairs in one item — a MATH fix (the false entry law) and a RECORD fix (two universal sentences) — and the note keeps them separate.** The HONEST LIMIT is `STALE-SELF-DESCRIPTION` as of r6 (PE6 realized the genre corpus-first; the sentence is not edited) — shard 1 `.32` carries the same tag.

**SUPERSESSION KIND:** `replacement` (the entry law and the two sentences, originals quoted) + `inventory completion` (the three-family grammar supplied where a bare claim stood).

**ARITHMETIC AUDIT:** all six geometry figures re-derived at shard 1 `.32` ✓ (2k+2h, 6k, 2k+4h; the two-solution enumeration; NINEMIX's 11 = 3+4+2+2 with strictly decreasing slopes 3, 2, 1, 1/2; SAMESIDE's 4 = 4×1; 59,049 = 3^10).

**DERIVATION:** Not a mathematical unit; the mathematics is shard 1 `.32`.

**RESOLUTION TRACE:** statement lines 2213–2247. correction sites: applied in place at 563–572 and 572–595 (shard 1 `.31`, `.32`), 1939–1946 and 2183–2189 (this shard, `.44`, `.53`); the HONEST LIMIT overtaken at 2319–2321 (`.61`).

**TEETH:** `decorrelated-model audit` (the out-of-pattern witness) + foreign-note evidence (PE5's NINEMIX/SAMESIDE) + a `disclosed non-repair` (the unrealized genre) later closed by PE6.

---

### EFF.GENIND.s2of3.56  [changes-record]

**CANONICAL STATEMENT:** FORM: bulleted display (§S15's PE5-m1). verbatim, lines 2248–2249.

> “* **PE5-m1 → rides the PE5-G1 fix** (the S4.3 display itself; same
>   edit, quoted original preserved in the [r5] bracket).”

**CONDITIONALITY:** A pointer item: the MINOR and the GAP have the same repair. Recorded as its own unit because the note numbers it separately and because a merge counting findings must not double-count the edit.

**SUPERSESSION KIND:** none of its own — it rides `.55`'s.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2248–2249. correction sites: none.

**TEETH:** as `.55`.

---

### EFF.GENIND.s2of3.57  [changes-record]

**CANONICAL STATEMENT:** FORM: bulleted display (§S15's PE5-m2 — step (1)'s same-side enumeration completed). verbatim, lines 2250–2260.

> “* **PE5-m2 → step (1)'s same-side enumeration completed at the
>   consumption site (S4.1).** The [r4] parenthetical (pieces
>   separable / co-children repeated) was complete within GENIND-3's
>   own scope but under-inclusive under GENIND-6(a)'s VERBATIM
>   consumption at mixed frames: same-side COMPOSITE blocks appear as
>   repeated NON-linear factors ψ(ȳ + ẑ_l)^{μ_b} — coprime to ȳ
>   since ψ, irreducible of degree ≥ 2 over F_Q, has no F_Q-root
>   (ψ(ẑ_l) ≠ 0) — the case GENIND-6(a)'s own gloss "co-blocks on
>   the same side have distinct residual roots/factors" already
>   carried (per the PE5 report, which verified coprimality via that
>   gloss). Now displayed in the parenthetical, [r5]-tagged.”

**CONDITIONALITY:** **A completeness defect created by a scope difference between a lemma and its verbatim consumer** — GENIND-3's own scope excludes composite blocks, so its step (1) enumeration was complete there and incomplete when GENIND-6(a) reads it VERBATIM at mixed frames. The conclusion (coprimality) was already carried by GENIND-6(a)'s own gloss; only the enumeration was short.

**SUPERSESSION KIND:** `inventory completion` (a third same-side co-block type added to a two-type enumeration).

**ARITHMETIC AUDIT:** the coprimality argument re-checked: ψ irreducible over F_Q of degree ≥ 2 has no root in F_Q, so ψ(ẑ_l) ≠ 0 for every ẑ_l ∈ F_Q ✓, hence ψ(ȳ + ẑ_l) has nonzero constant term and is coprime to ȳ ✓.

**DERIVATION:** Not a mathematical unit; the addition is shard 1 `.24`'s `[r5, PE5-m2]` bracket.

**RESOLUTION TRACE:** statement lines 2250–2260. correction sites: applied in place at 409–418 (shard 1 `.24`).

**TEETH:** foreign-note evidence (the PE5 report verified the coprimality via the gloss); no battery row exercises same-side composite co-blocks at n = 6.

---

### EFF.GENIND.s2of3.58  [changes-record]

**CANONICAL STATEMENT:** FORM: bold-headed bulleted display (§S15's BONUS item — a corrupt pin transcription). verbatim, lines 2261–2274.

> “* **BONUS (surfaced by this round's commit-time pin
>   re-verification): the PE4-leg results pin was a corrupt
>   transcription.** The r4 text (S4.1 concordance + S14 Arc) quoted
>   the `genind_pe4_fresh_results.json` md5 as "e5493312", inherited
>   verbatim from the PE4 report (and repeated by the PE5 report's
>   pin list). The file's actual md5 is **e549331a** — byte-identical
>   at its landing commit 51bd1bc and at this commit
>   (git-show-verified both, so the ARTIFACT never moved; the quoted
>   prefix was wrong in all three documents). Both note sites fixed
>   in place, [r5]-tagged; the two verifier reports are their
>   authors' committed artifacts and stay untouched, their shared
>   typo disclosed here — an instance of exactly the
>   pin-transcription corruption class the standing rule's
>   enumerate-with-evidence discipline exists to catch.”

**CONDITIONALITY:** **A verbatim-pin corruption propagating across three documents from one source** — precisely the failure mode a verbatim-echo protocol is supposed to prevent and does not, because all three copies share the same upstream. The artifact never moved; only the quoted prefix was wrong.

**SUPERSESSION KIND:** `provenance-rider` — the pin's *transcription* is corrected; nothing about the artifact or any claim resting on it changes. **Deliberately NOT `replacement`:** classifying it as one would imply a datum changed.

**REPORT-FREEZE:** the governing quote for freeze predicate 4 (§1): “the two verifier reports are their authors' committed artifacts and stay untouched, their shared typo disclosed here”.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2261–2274. correction sites: applied in place at 501–506 (shard 1 `.28`) and 1967–1969 (`.44`).

**TEETH:** `arithmetic recount` at the byte level (a commit-time md5 re-verification). **This is the tooth that caught it, and it is a protocol step, not a battery row.**

**PIN VERIFICATION:** `51bd1bc` ✓; `verification/openmath/genind_pe4_fresh_results.json` EXISTS ✓.

---

### EFF.GENIND.s2of3.59  [changes-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (§S15's universal-sentence sweep — seven rewrites and the adjudicated-kept list). verbatim, lines 2276–2301.

> “**THE UNIVERSAL-SENTENCE SWEEP (this round's sweep; grep patterns
> "every ", "all ", "no other", "none ", " never " over the whole note
> at this commit, adjudicated in RECORD/INVENTORY contexts only —
> lemma/theorem content may quantify).** Found at variance with the
> standing rule and REWRITTEN in place ([r5 sweep]-tagged, each
> quoting its original): (1) S14 leg-1 header "every display or
> consumption site listed" → every site matched by the six targets;
> (2) S14 leg-1 count "Uncapped survivors after this sweep: NONE" →
> scoped to the 15 enumerated site classes, PE5's independent
> outside-pattern sweep cited as verifier corroboration; (3) S14 C14
> "No other supplier note moved since its pin" → the S9.3 stack's
> remaining pins enumerated, each git-log-checked; (4) S14 leg-3
> "every [rN] tag in the body" → scoped to the executed four-pattern
> grep; (5) S12 PE2-m1 "(checked — no other consumer of the one-term
> form)" → the executed grep and its enumerated consumer sites. Plus
> the two PE5-G1-charged S14 sentences above (7 rewrites total).
> Adjudicated and KEPT (already rule-compliant): quantifiers ranging
> over ENUMERATED or artifact-pinned sets ("all eight md5 pins …
> listed", "before every r2 commit (2abf419/ad6f31d/52fb6ff)", S13's
> "every sealed and committed number stands unchanged" = the
> byte-frozen md5-pinned artifact set); S10/S11's per-family
> quantifiers (they range over the sealed runner's explicit rosters
> with committed artifacts; S11 is in any case FROZEN at its seal);
> leg-2's "every hit checked" (already pattern-scoped — PE5 itself
> adjudicated the hit-level claim TRUE); and the mathematical "never"
> claims (C13's class: lemma content, not records).”

**CONDITIONALITY:** **Rewrite (3) is the one that did not work** — it rescoped C14's quantifier while leaving its falsehood intact, and `[r6]` had to replace the sentence entirely (`.50`). The sweep's own kept-list is sound: every kept quantifier ranges over an enumerated or artifact-pinned set.

**SUPERSESSION KIND:** `counter re-reading` ×7 (each rewrite scopes a universal to an enumeration), applied at seven enumerated sites.

**ARITHMETIC AUDIT (compiler-computed, rule 22):** the sweep lists **five** numbered rewrites plus “the two PE5-G1-charged S14 sentences above” = **7 rewrites total** ✓ internally consistent. Cross-check: the two PE5-G1 sentences are the Arc ¶ and the closing ¶ of §S14 ✓ (`.44`, `.53`), and the five numbered ones land at `.47`, `.48`, `.50`, `.52`, `.34` ✓ — **all seven targets are units of this shard, none unaccounted for.** Note the kept-list's first item quotes “all eight md5 pins … listed”, i.e. the very numeral this compiler could not reconcile at `.53` — **the sweep adjudicated the sentence rule-compliant on the strength of its enumeration, without recounting the numeral.** Recorded (§8, defect 5).

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2276–2301. correction sites: rewrite (3)'s target later replaced at 2134–2151 (`.50`).

**TEETH:** `arithmetic recount` + `in-house hostile pass`.

---

### EFF.GENIND.s2of3.60  [changes-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (§S15's byte-freeze enumeration and as-of pins) + grade line. verbatim, lines 2303–2315.

> “**Byte-freeze at this commit (enumerated, re-verified by md5sum):**
> sealed runner e7ca150b; r2 supp triple 7335fc16/63b7413a/6c93f29c;
> PE3 fresh triple fce9cb08/2075dd28/360eb239; PE4 fresh triple
> aa2b9af8/1a29a9c1/e549331a (the corrected pin, see the BONUS item);
> PE5 fresh triple 6ef3132e/a0452521/bdc04c4d — 13 md5s, no committed
> artifact touched by this round. As-of pins checked against the git
> log at commit time: GENHN note HEAD = 850e77e (the S9.3 pin,
> unmoved); GENH4 note HEAD = b10a5a7 (the post-r4 Codex CHALLENGE @
> 5c8d2fd + ANNEX R disclosure added as the [r5] dated append at
> S9.3's GENH4 bullet — no consumed clause touched).
>
> **Grade: stays 0/2. The consecutive-clean count has NOT started; PE6
> (a fresh hostile pass) attempts the first clean.**”

**ARITHMETIC AUDIT (compiler-computed, rule 22):** `1 (runner) + 3 (r2 supp) + 3 (PE3) + 3 (PE4) + 3 (PE5) = 13` ✓ — **the enumeration reconciles exactly with the stated numeral**, unlike `.53`'s “eight”. This is the first round whose freeze count is fully checkable, and it is checkable *because* the standing rule forced the enumeration.

**CONDITIONALITY:** The as-of pins are commit-time claims; GENH4's moves again before r6 (`.18` entry 4).

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2303–2315. correction sites: none.

**TEETH:** `arithmetic recount` (13/13 reconciled) + commit-time md5 re-verification. **PIN VERIFICATION:** `850e77e` ✓, `b10a5a7` ✓, `5c8d2fd` ✓; all five artifact triples EXIST on disk ✓ (15 files).

---

### EFF.GENIND.s2of3.61  [changes-record] · **SERIES REPAIR-ARC, entry 5 of 5; SERIES RECORD-INTEGRITY, entry 5 of 5**

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph (§S16's Arc — the SUPPLIER RE-PIN ROUND). verbatim, lines 2317–2344.

> “## S16. [r6] REPAIR RECORD (PE6 adjudication; THE SUPPLIER RE-PIN ROUND — S11 stays frozen at its seal; S14's C14 corrected in place where its own sentence was the finding; S9.3 re-pinned with [r6] dated appends)
>
> **Arc.** Hostile pass PE6 (fresh context; the same-side f-first genre
> machine-realized corpus-first, 2,132,082 checks / 0 violations single
> run; report `GENIND_passPE6_report.md` @ 265a562/ad1bd98/f7f45f1)
> adjudicated 0 CRITICAL + 1 GAP + 1 MINOR. The GAP (PE6-G1) is the
> arc's FIFTH consecutive record-integrity finding (PE2-G2 → PE3-G1 →
> PE4-G1 → PE5-G1 → PE6-G1): S14 C14's [r5 sweep] rewrite asserted a
> per-supplier git-log check that was never executed, while the S9.3
> pins had gone stale across the suppliers' own repair arcs — the
> disease is the STALE PIN SET (diagnosis at ledger 26d2dbf: the S9.3
> supplier stack pinned states predating multiple supplier repair
> rounds, W-12 pinned at r2 while W-12 stood at r5 with a repaired
> CRITICAL in between). This r6 is THE SUPPLIER RE-PIN ROUND: the
> stack's suppliers re-pinned at their current HEADs, each with a
> fired-clause row below (C14's replacement — rows with evidence, no
> summary sentence, per the standing rule); C14 corrected in place at
> S14 with the false close quoted; the three stale arc parentheticals
> (PE6-m1: the W-12, HMENU3, W-11 bullets) given [r6] dated appends.
> Minimality contract: the pin refresh + the two findings, NOTHING
> else — no machine leg added (fresh numbers cited are PE6's committed
> leg `genind_pe6_fresh.*` @ ad1bd98); no sealed or committed artifact
> touched; no count law, theorem clause, or frozen number moved.
> Scope, enumeratively: the files edited this round are exactly one
> (this note); the sites edited are exactly five (the header arc
> line, GENIND-BOX-5's arc line, S9.3, S14's C14 item, this S16); the
> S9.3 bullets edited are exactly seven (W-12, W-11, HEX3, HMENU3,
> QSCOUT22, GENHN, GENH4).”

**SERIES:** REPAIR-ARC entry **5 of 5** (r6); RECORD-INTEGRITY entry **5 of 5**, and the entry that names the disease (“the STALE PIN SET”) and its ledger diagnosis.

**CONDITIONALITY:** **The round's own scope is stated enumeratively — one file, five sites, seven bullets — which is the standing rule applied to the round's own edit set.** This is the first round whose scope claim is fully checkable, and the compiler confirms it below.

**SUPERSESSION KIND:** `replacement` (C14's close → a table) + `as-of scoping` ×7 (the pin refresh) + `inventory completion` (the three stale arc parentheticals).

**ARITHMETIC AUDIT (compiler-computed, rule 22 — checking the round's own enumerative scope claim against this compilation's unit inventory):**
* “sites edited are exactly five”: header arc line (shard 1 `.01`) ✓, GENIND-BOX-5's arc line (`.05`) ✓, S9.3 (`.09`–`.19`) ✓, S14's C14 (`.50`) ✓, S16 itself (`.61`–`.68`) ✓ — **five, confirmed.**
* “S9.3 bullets edited are exactly seven”: W-12 (`.09`) ✓, W-11 (`.10`) ✓, HEX3 (`.11`) ✓, HMENU3 (`.12`) ✓, QSCOUT22 (`.16`) ✓, GENHN (`.17`) ✓, GENH4 (`.18`) ✓ — **seven, confirmed**; the four unedited bullets are J-D0 (`.13`), GRTJC (`.14`), WELDMASTER/DULEMMA/[W12-H] (`.15`), Classical (`.19`) ✓, and `.15`'s three suppliers appear in the unmoved list at `.63` ✓. **11 bullets total = 7 edited + 4 unedited** ✓.
* PE6's leg headline `2,132,082 checks / 0 violations` matches the header arc line's figure (shard 1 `.01`) ✓.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2317–2344. correction sites: none.

**TEETH:** `in-house hostile pass` + `transfer audit`. **PIN VERIFICATION:** `265a562` ✓, `ad1bd98` ✓, `f7f45f1` ✓, `26d2dbf` ✓; PE6's leg files EXIST ✓.

---
### EFF.GENIND.s2of3.62  [table]

**CANONICAL STATEMENT:** FORM: **Markdown table (the only source table in the whole note)** with its header sentence. verbatim, lines 2346–2361 — header quoted, then the eight rows transcribed as `[TABLE]` with every cell's operative text quoted (rule 5: transcribed as a table, never prosified; rule 14's double-emission does not fire because the source is already Markdown, not a fixed-width ASCII block).

> “**THE PER-SUPPLIER FIRED-CLAUSE TABLE** (C14's replacement; each row
> git-log-verified at THIS commit against the supplier's note file;
> consumption verdicts carry their evidence in-row; the two heaviest
> re-verified from the supplier texts below, the rest citing PE6's
> traces @ f7f45f1 §1 "What survives"):”

`[TABLE]` — eight rows, source columns preserved:

| # | supplier | old pin | current HEAD (= new pin) | what moved | clauses GENIND consumes | verdict |
|---|---|---|---|---|---|---|
| 1 | **W-12** | r2 `99f1813` | **r5 `be4a1dc/ee17210`** | r3 `b17238a` + r4 `d2d91b7/5728258` (**PE4 F1 CRITICAL** repaired in S3.2; (A1) σ-LABELING + FIRING CHECK added) + r5 (PE5 GAP + 3m) | W-12.D (Step 5); W-12.A (S1, S5.2, Steps 1–2); S2.3; S2.4/S2.5; S3.4; W12-L0/L1 | **SURVIVES** — “zero S3.2 cites in this note (grep, this round)”; W-12.D re-read and re-matched verbatim; the σ-LABELING clause “STRENGTHENS (A1)” |
| 2 | **HEX3** | r1 `2580f12` | **r3 `b6a1d69`** (arc 0/2) | r2 `a707430` (census 11 → 12) + r3 (S8.2's W-12.B consistency clause conditionalized on **HEX3-BOX-1**) | H-1..H-4; u₃(M); the committed species tables (GT-N3TIE) | **SURVIVES** — “both corrected items are S8.2/census records, uncited here”; the tie is at md5-frozen `hex3_checks_results.json` `ce6f4116`, GT-PIN 5/5 this round |
| 3 | **HMENU3** | seal `64d3ff9` / verdict `625fa49` | **ACCEPTED body `050425d` + ANNEX A `19c0285`** | r1 + r2 + ACCEPTED 2/2 + ANNEX A (HM3.C's (A0) quantifier → disc ≠ 0, two sites) | HM3-1/-2/-4/-3; HM3.A/B/C/D | **SURVIVES** — “ANNEX A corrects the quantifier exactly TO the form consumed here” |
| 4 | **W-11** | narrative to PE3 CLEAN `839b735` (1/2) | **ACCEPTED 2/2 @ `35e6545`** | one append-only acceptance annotation; body byte-frozen since r2 `31506b3` | W-11 through W12-L0 and R(M) | **SURVIVES** — “Honest strengthening; zero content diff to the consumed body” |
| 5 | **QSCOUT22** | `240a56c` (skeleton) | **verdict `dd67cda` + annex `fcaf268`** | seal → VERDICT (GREEN 7,614,473/0) → L3 annex (genre-E UND h = 1 slip) | **NOTHING** | **SURVIVES trivially** — “No consumed clause exists to break” |
| 6 | **GENHN** | `850e77e` | **`850e77e` — UNMOVED** (re-pin is a no-op) | HEAD unchanged; **three errata QUEUED unexecuted** | GENHN.A(iv); A(v); GENHN-3; S6.2 | **SURVIVES as-of** — “none of the three queued errata names a consumed clause …; execution disclosure owed at the next dated append” |
| 7 | **GENH4** | r3 `4b0d946` + appends through `b10a5a7` | **accepted body `4b0d946` + annex stack through R2 @ `760d20f`** (stack 0/2, pass #2 in flight) | annex-pass #1 NOT CLEAN (GAP-1 machine-refuted @ `a8dec16`/`fed3cff`) → ANNEX R2 `760d20f` | GENH4.A + GENH4-1F (menu); GENH4.B (drain); comp-weighted census — Step 4 + S7.1 only | **SURVIVES** — “GAP-1 sat on a clause this note never cites”; GENH4.B re-read at the accepted body, `git show 4b0d946` byte-identical to worktree HEAD |
| 8 | **HE7** | (no pin — never in this stack) | **FULLY FROZEN @ `ca3754d`** | body accepted; annex stack 2/2; micro-annex | **NOTHING** — “grep "HE7\|HE6" = 0 at f30e0fa/9f2da0f, re-run this round” | **Correctly absent** (PE6 Remark R2); “row recorded so the stack disclosure is total across all eight suppliers the re-pin charge names” |

**CONDITIONALITY:** **C14's replacement, and the arc's structural answer to the STALE PIN SET.** Its design principle is stated in the Arc (`.61`): “rows with evidence, no summary sentence, per the standing rule”. **Row 6 creates an obligation** (“execution disclosure owed at the next dated append”), discharged in shard 3. **Row 7's verdict rests on a supplier whose annex stack is 0/2 with pass #2 unlanded** — the weakest row, and the note says so in-row.

**SUPERSESSION KIND:** `replacement` (of C14's close) — the table IS the supersession, and its format (no summary sentence) is itself the remedy.

**ARITHMETIC AUDIT (compiler-computed, rule 22):** **eight rows** ✓; of these, **six suppliers moved** (rows 1, 2, 3, 4, 5, 7), **one did not** (row 6), **one was never pinned** (row 8) — 6 + 1 + 1 = 8 ✓. Against C14's refuted close, which claimed “none moved” of nine enumerated suppliers and was FALSE at **five** (`.50`): the five named there (W-12, HEX3, HMENU3, W-11, QSCOUT22) are rows 1–5 here ✓, and rows 6–8 were outside C14's enumeration (GENHN and GENH4 were handled separately in C14; HE7 was never in the stack) ✓ — **the two counts reconcile exactly.** Coverage: 8 table rows + 4 unmoved-list entries (`.63`) = **12 supplier positions**, against §S9.3's 11 bullets (`.09`–`.19`); the extra position is HE7, which has no S9.3 bullet ✓, and `.15`'s compound bullet expands to three entries in the unmoved list ✓ — **11 bullets − 1 compound + 3 expanded + 1 HE7 = 14 named suppliers across 12 positions**, all accounted for.
**PIN VERIFICATION:** every hash in the table resolves as a commit ✓ — `99f1813`, `be4a1dc`, `ee17210`, `b17238a`, `d2d91b7`, `5728258`, `2580f12`, `b6a1d69`, `a707430`, `64d3ff9`, `625fa49`, `050425d`, `19c0285`, `839b735`, `35e6545`, `31506b3`, `240a56c`, `dd67cda`, `fcaf268`, `850e77e`, `4b0d946`, `b10a5a7`, `a8dec16`, `fed3cff`, `760d20f`, `ca3754d`, `f7f45f1` (**27/27**). `ce6f4116` is an md5, not a commit.

**DERIVATION:** Not a mathematical unit; the consumption-survival ledger.

**RESOLUTION TRACE:** statement lines 2346–2361. correction sites: 2479–2487 (PE7-m1 corrects row 1's grep claim), 2488–2498 (PE7-m2 completes row 6's inventory), 2499–2506 (PE7-m3 corrects row 1's `[GENHN-HE]` locality), 3032–3094 (the supplier-movement record discharges row 6's owed disclosure, shard 3).

**TEETH:** `transfer audit` ×8 — a clause-by-clause survival check across each supplier's repair arc, of a kind no battery row performs. Two rows (1, 7) are additionally re-verified from the supplier TEXTS at `.64`/`.65`; the remaining six cite PE6's traces (`foreign-note evidence`), and the table says which is which.

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:HEX3-BOX-1` — count **11** (row 2's conditionalizing lemma; ledger **HYP.137**, see `.11`).
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:W-12.B` — count **19**.

---

### EFF.GENIND.s2of3.63  [changes-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (§S16's unmoved-pin list). verbatim, lines 2363–2371.

> “**Pins that did NOT move (the stack's remaining four bullets, each
> git-log-checked at this commit; last note-file touch listed):**
> J-D0 @ 1642275/9387eb1 — note last touched 9387eb1 (08-07 16:54),
> pre-seal, pin = HEAD ✓; DULEMMA @ f819f26 — last touched f819f26
> (08-07 18:59), pin = HEAD ✓; GRTJC (accepted 2/2 @ 83f47f4) — note
> last touched 63091ce (08-07 20:06, pre-seal annex), body unmoved ✓;
> WELDMASTER (accepted) — note last touched fdf1d99 (08-07 19:20,
> pre-seal fold-carry annexes), body unmoved ✓. Four checked, four
> keep their pins; [W12-H] is W12-note-internal and rides row 1.”

**CONDITIONALITY:** Enumerated with per-supplier evidence — the standing rule's format applied to the negative cases too, which is what makes the table's coverage total.

**ARITHMETIC AUDIT:** “four bullets … Four checked, four keep their pins” ✓; the four are J-D0, DULEMMA, GRTJC, WELDMASTER ✓, and `[W12-H]` is routed to row 1 rather than left unaccounted ✓ — **five positions disposed, zero unaccounted.**

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2363–2371. correction sites: none.

**TEETH:** `transfer audit` (negative direction). **PIN VERIFICATION:** `1642275` ✓, `9387eb1` ✓, `f819f26` ✓, `83f47f4` ✓, `63091ce` ✓, `fdf1d99` ✓.

---

### EFF.GENIND.s2of3.64  [changes-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph + italic sub-head (§S16's first heavy re-verification — THEOREM W-12.D at the new pin, both sides quoted). verbatim, lines 2373–2399.

> “**THE TWO HEAVIEST CONSUMPTIONS, RE-VERIFIED FROM THE SUPPLIER TEXTS
> THIS ROUND (not inherited from PE6's traces).**
>
> *(1) THEOREM W-12.D at the new pin (r5 HEAD ee17210).* The supplier
> text at HEAD states, verbatim (W12 S1(iii)): "**(iii) [THEOREM
> W-12.D — THE REDUCTION THEOREM] PROVED, unconditional as a
> reduction.** Fix n and suppose, at every prime power q
> simultaneously: (A0) [lift well-posedness] … (A1) [exact core menu]
> … (A2) [drainage of the rest] … THEN for every splitting type τ of
> degree n: R_τ(q) := Σ_{F: σ_F = τ} Σ_{x ∈ P_F} c_F(q)·q^{−ℓ_F(x)}
> converges to ONE rational function in ℚ(q); it equals the N → ∞
> limit of the decided-τ window mass AND the Haar splitting density
> μ_τ; it is the SAME expression at every prime power q, both
> characteristics, wild primes included; and Σ_τ R_τ(q) = 1." This
> note's use-site (S6 Step 5), verbatim: "P(n)'s (A0)+(A1)+(A2) are
> W-12.D's hypotheses at degree n: THEOREM W-12.D (PROVED, @ pin)
> yields one R_τ(q) ∈ ℚ(q) per splitting type of degree n, = the Haar
> density, same expression at every prime power and characteristic,
> Σ_τ R_τ = 1." Match: hypothesis triple and all four conclusion
> clauses, one for one. The r4-added σ-LABELING bracket inside (A1)
> is a STRENGTHENED hypothesis (more is demanded of P(n), nothing
> less is delivered by the theorem); its per-degree supply is not
> this note's to re-prove — W12 r4's own FIRING CHECK verified it at
> W-11(i)/(iii) (n = 2), HM3.C (n = 3), GENH4.C (n = 4), GENHN.C
> (μ = 2 stages), with n ≥ 6 named as [GENHN-HE(μ ≥ 3)] — the exact
> open box this note's [GENIND-H] display already carries. VERDICT:
> consumption SURVIVES at the new pin.”

**CONDITIONALITY:** **A verbatim two-sided text match — the strongest form of consumption verification in the corpus, and the note distinguishes it from citation explicitly** (“not inherited from PE6's traces”). Two riders land on it from the post-PE7 corrections: PE7-m3 corrects the `[GENHN-HE(μ ≥ 3)]` locality (`.71`), and PE7-m1 corrects the neighbouring S3.2 grep claim (`.69`). **The one open edge is the STRENGTHENED (A1)**: more is demanded of P(n), and this note does not re-derive its own (A1)-closure lemma under the strengthened predicate — shard 1's OPEN-CALL 3, re-raised here.

**ARITHMETIC AUDIT:** “all four conclusion clauses, one for one” — the supplier's four are (i) convergence to one rational function in ℚ(q), (ii) equality with the N → ∞ decided-τ window mass AND the Haar density μ_τ, (iii) same expression at every prime power, both characteristics, wild included, (iv) Σ_τ R_τ = 1; the use-site's four are “one R_τ(q) ∈ ℚ(q) per splitting type”, “= the Haar density”, “same expression at every prime power and characteristic”, “Σ_τ R_τ = 1” ✓ — **four for four, matched.** The hypothesis triple (A0)/(A1)/(A2) matches ✓.

**DERIVATION:** Not a mathematical unit; a text-match verification.

**RESOLUTION TRACE:** statement lines 2373–2399. correction sites: 2479–2487 and 2499–2506 (PE7-m1, PE7-m3).

**TEETH:** `transfer audit` at verbatim granularity — the gold standard row of this shard's teeth table.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:THEOREM W-12.D` — count **5**; `σ-LABELING` — count **7**.
XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN.C` — count **19**.
XREF: `lean/notes/openmath/GENH4_PROOF_2026-08-08.md:GENH4.C` — count **11**.
XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:HM3.C` — count **15**.
**NEAR-MISS:** `[GENHN-HE(μ ≥ 3)]` — count **0** in GENHN; the note's own PE7-m3 correction supplies the reading (`.71`). `W-11(i)/(iii)` — clause labels, count **0** as written in W11 (which uses bare `(i)`/`(iii)`); verified parent `THEOREM W-11` count **3**.

---

### EFF.GENIND.s2of3.65  [changes-record]

**CANONICAL STATEMENT:** FORM: italic sub-head paragraph (§S16's second heavy re-verification — THEOREM GENH4.B at the accepted body, both sides quoted). verbatim, lines 2401–2421.

> “*(2) THEOREM GENH4.B (= Q22-L3) at the accepted body (4b0d946).*
> The supplier text — byte-identical at `git show 4b0d946` and at
> worktree HEAD, checked this round — states, verbatim: "**THEOREM
> GENH4.B (composite drainage = Q22-L3, PROVED — with the sealed
> display CORRECTED).** Per center, per entry, per history H₂ (any
> t ≥ 0, any prehistory r): the σ-undecided (conservative) count is
> ONE exact q-power … genre E: UND(h; H₂) = (q−1)^{r+t} · q^{N+h−1}
> per center … genre F: UND(k; H₂) = (q²−1)^t (q−1)^r ·
> [ q^{2⌊N/2⌋+2k−1} + 1_{2|N}·(q−1)·q^{N+2k−1} ] … the second term is
> the readable-value/unreadable-residual band at dv0 = N
> (GENH4-CAP(F)), present at even N only". This note's use-site (S6
> Step 4's discharge geography), verbatim: "the DRAIN half by THEOREM
> GENH4.B (= Q22-L3), one exact closed form per (center, entry,
> history) stratum (a single q-power off the boundary band; a
> TWO-term q-power sum at genre-F even N, GENH4-CAP(F)'s own
> display…)". Match: stratum granularity (center, entry, history),
> the single-q-power off-band clause, and the two-term even-N band —
> one for one; the (CS-EXACT) consumption needs exact finite q-power
> sums, which both displayed laws are. VERDICT: consumption SURVIVES
> at the accepted-body pin, with the annex stack strictly appended
> and its GAP-1/(c′) material unconsumed.”

**CONDITIONALITY:** **The n = 4 de facto discharge of (CS-EXACT), verified at verbatim granularity against a byte-frozen accepted body.** Note the supplier's own header phrase “the σ-undecided (conservative) count is ONE exact q-power” — which GENIND consumes WITH the two-term caveat, exactly the granularity correction PE2-m1 made (`.34`). **The supplier's own coarse phrase and its own two-term display coexist in the quoted text**, and GENIND's use-site is the one that reconciles them.

**ARITHMETIC AUDIT (compiler-computed):** genre F's law `q^{2⌊N/2⌋+2k−1} + 1_{2|N}·(q−1)·q^{N+2k−1}` is **one term at odd N** (the indicator vanishes) and **two at even N** ✓ — matching “a single q-power off the boundary band; a TWO-term q-power sum at genre-F even N” exactly. At even N, `2⌊N/2⌋ = N`, so the two terms are `q^{N+2k−1}` and `(q−1)q^{N+2k−1}`, summing to `q^{N+2k}` — **a single q-power after all**, at even N. Recorded as an observation, not a correction: the note's “TWO-term q-power sum” is faithful to the *displayed form*, and the (CS-EXACT) requirement (“a FINITE SUM of q-powers”) is satisfied either way ✓.

**DERIVATION:** Not a mathematical unit; a text-match verification.

**RESOLUTION TRACE:** statement lines 2401–2421. correction sites: none.

**TEETH:** `transfer audit` at verbatim granularity + a `git show`-level byte check.

XREF: `lean/notes/openmath/GENH4_PROOF_2026-08-08.md:THEOREM GENH4.B` — count **6**; `Q22-L3` — count **3**; `GENH4-CAP(F)` — count **11**.

---

### EFF.GENIND.s2of3.66  [changes-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (§S16's citation of PE6's traces for the remaining rows). verbatim, lines 2423–2432.

> “**PE6's consumption-survival traces, cited at their report pin
> (f7f45f1 §1 "What survives"), covering the remaining rows:** (i)
> W12 r5's supply table re-derives the (A0) clause at the disc ≠ 0
> form, the form this note's citations consume; (ii) the W12-PE4
> CRITICAL was in W12 S3.2, which this note does not cite; (iii)
> HEX3's corrected items are not the consumed clauses and the species
> tie is at the unmoved md5-frozen JSON; (iv) HMENU3's ANNEX A
> corrects (A0) exactly to the form the induction needs; (v) BOX-5's
> "every supplier consumed at the pins of S10's PIN family" is an
> md5-runner-level sentence and TRUE (GT-PIN 5/5).”

**CONDITIONALITY:** **The note is explicit that these five are CITED, not re-verified here** — the division between `.64`/`.65` (re-verified from supplier texts) and this unit (cited from a verifier's traces) is the honest core of §S16's evidence hierarchy. Trace (ii) is the claim PE7-m1 later re-words (`.69`); trace (v) is a rare *defence* of an existing universal sentence on the ground that it ranges over an artifact-pinned set.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2423–2432. correction sites: 2479–2487 (PE7-m1 on trace (ii)'s sibling claim).

**TEETH:** `foreign-note evidence` ×5, explicitly labelled as such.

---

### EFF.GENIND.s2of3.67  [changes-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (§S16's PE6-m1 disposition). verbatim, lines 2434–2438.

> “**PE6-m1 disposition:** the three stale arc parentheticals (W-12
> "PE3 owed"; HMENU3 "r1 owed"; W-11 "counter 1/2") each received an
> [r6] dated append at their S9.3 bullets — originals preserved in
> place as dated records, per the note's convention (previously
> executed three times on the GENH4 bullet).”

**CONDITIONALITY:** Three `STALE-SELF-DESCRIPTION` items cured by dated append rather than edit. **The parenthetical “(previously executed three times on the GENH4 bullet)” is the note's own recognition of SERIES GENH4-PIN** — three appends at r3/r4/r5, with r6 making four (`.18`).

**SUPERSESSION KIND:** `as-of scoping` ×3, executed by append.

**ARITHMETIC AUDIT:** three stale parentheticals ✓ (W-12 `.09`, HMENU3 `.12`, W-11 `.10`); “previously executed three times on the GENH4 bullet” ✓ = `[r3]`, `[r4]`, `[r5]` (the `[r6]` append is this same round's, making four in total).

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2434–2438. correction sites: applied at 1470–1482, 1508–1517, 1485–1490 (`.09`, `.12`, `.10`).

**TEETH:** `in-house hostile pass`.

---

### EFF.GENIND.s2of3.68  [changes-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (§S16's byte-freeze, as-of states and the photo-finish disclosure) + grade line. verbatim, lines 2440–2464.

> “**Byte-freeze at this commit (enumerated, re-verified by md5sum
> this round):** sealed runner e7ca150b; r2 supp triple
> 7335fc16/63b7413a/6c93f29c; PE3 fresh triple
> fce9cb08/2075dd28/360eb239; PE4 fresh triple
> aa2b9af8/1a29a9c1/e549331a; PE5 fresh triple
> 6ef3132e/a0452521/bdc04c4d; PE6 fresh triple
> 87b0f27e/1c2f8eed/fb473a57 (the verifier's committed leg @ ad1bd98,
> now in the frozen list) — 16 md5s; plus GT-PIN suppliers 5/5
> (w11 500aae15 / w12 7dc040d9 / hex3 83faf7ed / hmenu3 65326f85 /
> hex3_checks_results.json ce6f4116). No committed artifact touched
> by this round. As-of states at commit time against the git log:
> W12 note HEAD = ee17210; HEX3 = b6a1d69; HMENU3 = 19c0285; W11 =
> 35e6545; QSCOUT22 = fcaf268; GENHN = 850e77e; GENH4 = 760d20f
> (annex pass #2 in flight, unlanded); HE7 = ca3754d; repo movement
> since the wave-11 fold 26d2dbf = TAMEKQX commits only
> (209ed18/fa58556/f3c6eef, b99daa7), none touching a pinned file.
> [r6 photo-finish disclosure, same round: between this record's two
> commits (760afed → dcc20bb) one more TAMEKQX commit landed
> (9b170f0, its verdict), so the enumerated list above was short by
> one AT THE SECOND COMMIT'S timestamp; git-show-verified: 9b170f0
> touches TAMEKQX files only, no pinned file, no supplier note — the
> as-of verdicts stand.]
>
> **Grade: stays 0/2. The consecutive-clean count has NOT started; PE7
> (a fresh hostile pass) attempts the first clean.**”

**CONDITIONALITY:** **The photo-finish disclosure is the standing rule at its sharpest**: an enumerated list went stale between the round's own two commits, by one commit, and the note discloses it with a git-show verification rather than silently re-enumerating. It is the smallest possible instance of the STALE PIN SET disease and the note treats it with the same discipline as the largest.

**ARITHMETIC AUDIT (compiler-computed, rule 22):** `1 (runner) + 3 + 3 + 3 + 3 + 3 = 16` ✓ — the enumeration reconciles with the stated numeral exactly (as at `.60`'s 13, and unlike `.53`'s “eight”). The GT-PIN five are enumerated as five ✓. The as-of list names **eight** supplier HEADs ✓ = the eight rows of `.62` ✓. The repo-movement list names four TAMEKQX commits, corrected to five by the photo-finish ✓.
**PIN VERIFICATION:** `ee17210` ✓, `b6a1d69` ✓, `19c0285` ✓, `35e6545` ✓, `fcaf268` ✓, `850e77e` ✓, `760d20f` ✓, `ca3754d` ✓, `26d2dbf` ✓, `209ed18` ✓, `fa58556` ✓, `f3c6eef` ✓, `b99daa7` ✓, `9b170f0` ✓, `760afed` ✓, `dcc20bb` ✓, `ad1bd98` ✓ — **17/17 commits resolve.** All six artifact triples (18 files) EXIST on disk ✓.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2440–2464. correction sites: none; the grade line is scoped by 2540–2543 (`.72`).

**TEETH:** `arithmetic recount` (16/16 and 5/5 reconciled) + `in-house hostile pass` (the photo-finish self-catch).

---
### EFF.GENIND.s2of3.69  [changes-record] · **SERIES REPAIR-ARC, entry 6 (post-PE7 rider)**

**CANONICAL STATEMENT:** FORM: heading + provenance paragraph + bulleted item (the post-PE7 dated corrections' frame and PE7-m1). verbatim, lines 2468–2487.

> “### Dated corrections (2026-08-09, post-PE7)
>
> Provenance: passPE7 hostile verification (report
> `GENIND_passPE7_report.md`, verdict commit 380bc66: 0 CRITICAL +
> 0 GAP + 3 MINOR; the 2-clean count stands at 1/2). Three wording
> corrections to the r6 record, each original standing in place as a
> dated record per the note's convention; no count law, theorem
> clause, consumption verdict, or frozen number is touched by this
> annex, and the note text above this annex is byte-identical to
> 993935d.
>
> * **[PE7-m1] S9.3 W-12 bullet (L1480–1481) + S16 row 1 — the "zero
>   S3.2 cites" grep claim, wording corrected:** `grep "S3.2"` on
>   this note at r6 returns FOUR string hits (L1474, L1480, L2354,
>   L2427; re-executed this round), the four being r6's own
>   disclosure sentences about W12's PE4 repair, none of the four a
>   CONSUMING cite of W12 S3.2's content — read both sentences as
>   "zero S3.2 cites outside this round's own disclosure sentences
>   (grep: 4 string hits, all four disclosure)"; the consumption
>   verdict is unchanged.”

**SERIES:** REPAIR-ARC entry **6** — the first entry that is a dated APPEND rather than an in-place round (the body is byte-frozen from here on).

**CONDITIONALITY:** **The first CLEAN pass of the arc (0C + 0G + 3M) and the first append-only correction round.** PE7-m1 is a `self-reference` defect: a grep claim that counted its own disclosure sentences as hits.

**SUPERSESSION KIND:** `wording-rider` — “read both sentences as …”, an explicit substitution at two named sites, with the verdict preserved.

**TARGETS:** `s2of3.09` (the S9.3 W-12 bullet) and `s2of3.62` (§S16 row 1).

**ARITHMETIC AUDIT (compiler-computed):** the four hit lines named (L1474, L1480, L2354, L2427) all lie inside this shard's range ✓ and correspond to: `.09`'s r6 append (L1474 and L1480), `.62` row 1 (L2354), and `.66` trace (ii) (L2427) ✓ — **four for four, each identifiable as a disclosure sentence, none a consuming cite.** The claim's corrected form is therefore exactly right.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2468–2487. correction sites: none downstream.

**TEETH:** `arithmetic recount` (a grep re-executed and its hits classified).

**PIN VERIFICATION:** `380bc66` ✓, `993935d` ✓.

---

### EFF.GENIND.s2of3.70  [changes-record]

**CANONICAL STATEMENT:** FORM: bulleted display (PE7-m2 — the GENHN consumed-surface inventory completed). verbatim, lines 2488–2498.

> “* **[PE7-m2] S9.3 GENHN bullet (L1547–1548) + S16 row 6 — the
>   consumed-surface inventory completed:** beyond the four listed
>   clauses (A(iv), A(v), GENHN-3, S6.2), this note leans on GENHN at
>   three further sites — the GENHN S11.F schema cite at the
>   GENIND-6(a) proof (L684), the GENHN S6.3 display cite at S6
>   Step 4 (L1094), and the embedded-genre echo at the GENIND-6(a)
>   statement (L623: "the sibling-Hensel-loss composition GENHN
>   already displays") — screen future GENHN errata against the seven
>   sites, not four; the SURVIVES verdict is unchanged (at ledger
>   granularity the three queued errata name no clause, the same
>   evidence covering the three added sites).”

**CONDITIONALITY:** **An under-counted consumed surface: four clauses listed, seven sites actually leaned on.** The instruction is forward-looking (“screen future GENHN errata against the seven sites, not four”) and is **honoured** by the dated supplier-movement record, which screens all seven (shard 3, lines 3055–3074).

**SUPERSESSION KIND:** `inventory completion`.

**ARITHMETIC AUDIT:** four listed + three added = **seven** ✓; the three added sites are L684 (shard 1 `.34`'s proof), L1094 (shard 1 `.57`), L623 (shard 1 `.34`'s statement) ✓ — **all three verified in shard 1's units.** Note that two of the three sit in the same unit (`.34`), so the seven *sites* map to **six** shard-1 units: `.35` (A(iv)), `.37`/`.63` (A(v)), `.57`/`.63` (GENHN-3), `.64` (S6.2), `.34` (S11.F and the echo), `.57` (S6.3).

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2488–2498. correction sites: applied forward at 3055–3074 (shard 3).

**TEETH:** `transfer audit` (a consumed-surface recount).

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:S11.F` — count **10**; `S6.3` — count **3**; `GENHN.A(iv)` — count **3**; `GENHN.A(v)` — count **6**; `LEMMA GENHN-3` — count **3**; `S6.2` — count **6**.

---

### EFF.GENIND.s2of3.71  [changes-record]

**CANONICAL STATEMENT:** FORM: bulleted display (PE7-m3 — the `[GENHN-HE]` locality correction). verbatim, lines 2499–2506.

> “* **[PE7-m3] S16 row 1 — "[GENHN-HE(μ ≥ 3)] … the box this note
>   already displays," locality corrected:** the string "GENHN-HE"
>   occurs at r6 only inside S16 itself (grep: L2354, L2397; this
>   annex adds disclosure-only mentions) — the note displays no box
>   by that name; the μ ≥ 3 stage-law content rides inside
>   [GENIND-H] — read the row-1 clause as "the exact open box this
>   note's [GENIND-H] display already carries," the phrasing S16's
>   own re-verification paragraph (L2397–2398) already uses.”

**CONDITIONALITY:** **A designation that names no box anywhere** — the note diagnoses it by grep and supplies the corrected reading rather than inventing a box. This is the source-side authority for shard 1 `.15`'s NEAR-MISS.

**SUPERSESSION KIND:** `wording-rider` (“read the row-1 clause as …”).

**TARGETS:** `s2of3.62` (row 1), `s2of3.64`; and, for the reading, shard 1 `.15`.

**ARITHMETIC AUDIT:** the two cited hit lines L2354 and L2397 fall in `.62` (row 1) and `.64` ✓ — two hits, both inside §S16 ✓. Compiler cross-check at the supplier: fixed-string `GENHN-HE` in `GENHN_PROOF_2026-08-08.md` = **0** ✓ — the box genuinely does not exist under that name at the supplier either.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2499–2506. correction sites: none downstream; carried at shard 1 `.15` and at `.62`/`.64` here.

**TEETH:** `arithmetic recount` (grep-based locality check).

---

### EFF.GENIND.s2of3.72  [changes-record] · **SERIES REPAIR-ARC, TERMINAL entry**

**CANONICAL STATEMENT:** FORM: heading + bold display + paragraph (the dated acceptance record). verbatim, lines 2510–2526 and 2545–2548.

> “### Dated acceptance record (2026-08-09, post-PE8)
>
> **GENIND IS ACCEPTED 2/2; the text is FROZEN — dated appends only.**
> PE7 (hostile, fresh context, first d ≥ 2 + n = 10 route) adjudicated
> CLEAN — 0 CRITICAL + 0 GAP + 3 MINOR (report
> `GENIND_passPE7_report.md`, verdict commit 380bc66); its three MINORs
> were cured by the dated corrections annex above (landed b653858). PE8
> (hostile, fresh context, the acceptance attempt: non-prime base
> q ∈ {4, 8, 9} + the n = 12 double-composite + the symbolic parametric
> inclusion–exclusion) adjudicated CLEAN — 0 CRITICAL + 0 GAP + 1 MINOR
> (report `GENIND_passPE8_report.md`, verdict commit 3f5bafc). The
> 2-clean count completed 1/2 → 2/2. PE8 re-verified the body's
> byte-freeze (lines 1–2464 md5 14fa6afc == 993935d, the post-PE7 annex
> purely additive). Arc: seal c3212cc → PE1..PE8 → r1..r6 → post-PE7
> rider → this record. Per PE8's verdict line, the three leaders of the
> uniformity-theorem chain (HE7, GENH4, GENIND) are now each through
> the 2-clean bar.”

> “No count law, theorem clause, consumption verdict, or frozen number
> is touched by this append. [GENIND-H] at n ≥ 4 remains the displayed
> OPEN box — the acceptance freezes the reduction and its record, not
> the box.”

**SERIES:** REPAIR-ARC **TERMINAL**. The arc, as the record itself states it: `seal c3212cc → PE1..PE8 → r1..r6 → post-PE7 rider → this record`.

**CONDITIONALITY:** **The single most important sentence for a chapter cut is the closing one: “the acceptance freezes the reduction and its record, not the box.”** ACCEPTED 2/2 is a *record* grade; [GENIND-H] at n ≥ 4 is open, and two further conjuncts enter at n ≥ 8 (shard 3). **Two of PE8's own route claims retire coverage holes the note's boxes still assert** — non-prime bases q ∈ {4, 8, 9} against GENIND-BOX-3's “prime q only”, and n = 10/n = 12 against the roster's max n = 5 — without editing the boxes (`.03`'s STALE-SELF-DESCRIPTION tag).

**SUPERSESSION KIND:** `counter re-reading` (the clean counter completes 1/2 → 2/2) + `license` (the text-freeze protocol changes: in-place rounds end, dated appends only).

**ARITHMETIC AUDIT (compiler-computed):** the 2-clean count: PE7 CLEAN (→ 1/2) + PE8 CLEAN (→ 2/2) ✓. Finding tallies across the full arc: PE1 3G+4m, PE2 2G+1m, PE3 2G+4m, PE4 2G+0m, PE5 1G+2m, PE6 1G+1m, PE7 0G+3m, PE8 0G+1m → **0 CRITICAL, 11 GAP, 16 MINOR over eight passes**, with GAPs monotone non-increasing 3,2,2,2,1,1,0,0 ✓ (audited also at `.05`). Body freeze: lines 1–2464 md5 `14fa6afc` == commit `993935d` ✓ — and note that **2464 < 2468**, the first line of the post-PE7 annex ✓, so “purely additive” checks structurally.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2510–2526 + 2545–2548. correction sites: none — this is the terminal record. Its own scoping clause for the five grade closes is at 2540–2543.

**TEETH:** `in-house hostile pass` ×8, two of them CLEAN. **PIN VERIFICATION:** `380bc66` ✓, `b653858` ✓, `3f5bafc` ✓, `993935d` ✓, `c3212cc` ✓. PE7's and PE8's committed legs `genind_pe7_fresh.*` (plus two extra run pairs) and `genind_pe8_fresh.*` all EXIST on disk ✓.

---

### EFF.GENIND.s2of3.73  [changes-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph with two quoted targets (the PE8-m1 cure — a supersession of two frozen arc lines by name). verbatim, lines 2528–2543.

> “**PE8-m1 cure (PE8's one MINOR, the stale-arc class PE6-m1 named):
> the two arc-state lines inside the frozen region are SUPERSEDED by
> this append.** Both sit in the byte-frozen body and could not be
> edited in place; each reads as of r6, two passes stale at acceptance —
> quoted verbatim:
>
> * Header arc line, L49–50: "the clean count has NOT started — PE7
>   attempts the first clean)." — superseded: the count ran 0/2 → 1/2
>   (PE7 CLEAN, 380bc66) → 2/2 (PE8 CLEAN, 3f5bafc); ACCEPTED.
> * GENIND-BOX-5 arc close, L1414–1415: "— the clean count has NOT
>   started;" — superseded the same way.
>
> (The per-round grade closes — e.g. the r6 record's L2463–2464 "Grade:
> stays 0/2. The consecutive-clean count has NOT started; PE7 (a fresh
> hostile pass) attempts the first clean." — are round-dated records,
> correct as of their rounds; this append is the current state.)”

**CONDITIONALITY:** **A supersession-by-append with an explicit non-target list** — the parenthetical scopes the cure so that the five per-round grade closes are NOT superseded but *dated*. **That distinction is the reason `.35`, `.43`, `.53`, `.60`, `.68`'s grade lines are not tagged STALE-SELF-DESCRIPTION while `.30`'s §S11 clauses ARE**: the cure covers the two arc-state lines and the grade closes are pre-scoped; §S11's “Attempt 0/2; the hostile arc has not begun” is **neither** covered nor pre-scoped (OPEN-CALL 3).

**SUPERSESSION KIND:** `counter re-reading` on two named frozen lines, executed by append because the body cannot be edited.

**TARGETS:** shard 1 `.01` (header arc line, L49–50) and `s2of3.05` (GENIND-BOX-5 arc close, L1414–1415). **Explicitly NOT targeted:** the five per-round grade closes (`.35`, `.43`, `.53`, `.60`, `.68`).

**ARITHMETIC AUDIT:** both quoted target lines fall inside the byte-frozen body (L49–50 and L1414–1415, both < 2464) ✓, so neither could be edited in place ✓ — the append mechanism is forced, exactly as stated.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2528–2543. correction sites: none.

**TEETH:** `in-house hostile pass`; the finding is a staleness scan of the frozen region.

---
## 3. Consumption tables

### 3.1 Verified import/XREF designations

`[TABLE — compiler ledger]` Every count is `grep -cF '<designation>' <file>` at HEAD, recorded inline at the unit and repeated here. **59 distinct designations across ten supplier notes, all count ≥ 1.**

| # | Target : designation | Count | Role in this shard |
|---|---|---|---|
| 1–13 | `W12_PROOF_2026-08-08.md:` `THEOREM W-12.D` (5) · `THEOREM W-12.A` (8) · `W12-L0` (32) · `W12-L1` (30) · `S2.3` (35, upper bound) · `S2.4` (10) · `S2.5` (9) · `S3.4` (11) · `[W12-H]` (17) · `W12-BOX-1` (10) · `W-12.B` (19) · `σ-LABELING` (7) · `b₂ = 0` (15) | as listed | `.07`, `.09`, `.11`, `.15`, `.19`, `.20`, `.49`, `.62`, `.64` |
| 14–23 | `HEX3_PROOF_2026-08-08.md:` `H-1` (5) · `H-2` (11) · `H-3` (5) · `H-4` (2) · `THEOREM HEX3.A` (11) · `THEOREM HEX3.B` (8) · `HEX3-BOX-1` (11) · `HEX3-BOX-2` (4) · `R(M)` (21) · `S5.1` (9) | as listed | `.02`, `.04`, `.06`, `.11`, `.22`, `.29`, `.62` |
| 24–31 | `HMENU3_PROOF_2026-08-08.md:` `HM3-1` (4) · `HM3-2` (5) · `HM3-3` (3) · `HM3-4` (11) · `HM3.A` (18) · `HM3.B` (19) · `HM3.C` (15) · `HM3.D` (13) | as listed | `.12`, `.62`, `.64` |
| 32 | `W11_PROOF_2026-08-08.md:THEOREM W-11` | 3 | `.10`, `.20`, `.62` |
| 33–34 | `JD0_PROOF_2026-08-08.md:` `LEMMA J-D0` (4) · `J-D0` (25) | as listed | `.08`, `.13` |
| 35–40 | `GRTJC_PROOF_2026-08-08.md:` `W-6` (18) · `W-8` (35) · `W-9` (13) · `JC-F1` (18) · `JC-LOAD` (31) · `dim_K 𝒜(T) = E` (3) | as listed | `.08`, `.14` |
| 41–48 | `GENHN_PROOF_2026-08-08.md:` `GENHN.A(i)` (11) · `GENHN.A(iv)` (3) · `GENHN.A(v)` (6) · `LEMMA GENHN-3` (3) · `S6.2` (6) · `S11.F` (10) · `S6.3` (3) · `GENHN.C` (19) | as listed | `.17`, `.18`, `.32`, `.62`, `.64`, `.70` |
| 49–57 | `GENH4_PROOF_2026-08-08.md:` `THEOREM GENH4.A` (5) · `THEOREM GENH4.B` (6) · `GENH4-1F` (10) · `GENH4.C` (11) · `GENH4-BOX-7` (1) · `GENH4-CAP(F)` (11) · `Q22-L1` (7) · `Q22-L3` (3) · `ANNEX-LEMMA GENH4-7` (11) | as listed | `.16`, `.18`, `.34`, `.62`, `.64`, `.65` |
| 58 | `QSCOUT22_2026-08-08.md:GENRE E` | 2 | `.16` |
| 59 | `W10_PROOF_2026-08-08.md:W10-BOX-3` | 1 | `.06` |

**File-existence rows:** `WELDMASTER_2026-08-08.md` ✓, `DULEMMA_PROOF_2026-08-08.md` ✓ (`.15`).

**Battery/verifier artifacts verified to EXIST** (`verification/openmath/`): the sealed triple `genind_checks.{py,_output.txt,_results.json}`; `genindr2_supp.*` (3); `genind_pe3_fresh.*` (3); `genind_pe4_fresh.*` (3); `genind_pe5_fresh.*` (3); `genind_pe6_fresh.*` (3); `genind_pe7_fresh.*` + two extra run pairs (7); `genind_pe8_fresh.*` (3) — **28 files, all present.**

### 3.2 Commit-pin verification (rule 23)

`[TABLE — compiler ledger]` **87 distinct commit hashes are cited in this shard's range. All 87 were verified with `git cat-file -t`; all 87 resolve as `commit`. Zero unresolvable pins.** The list, in unit order:

`4259a93 50db400 f89b565 ade9bac bd9bce1 265a562 ad1bd98 f7f45f1` (`.05`) · `f669cb0 c16c717 ba0d1a4 99f1813 b17238a d2d91b7 5728258 be4a1dc ee17210` (`.09`) · `7020ceb 31506b3 839b735 35e6545` (`.10`) · `e3f3459 671a126 2580f12 a707430 b6a1d69` (`.11`) · `64d3ff9 625fa49 f4f7b03 3235e1b e1280be 050425d 19c0285` (`.12`) · `1642275 9387eb1` (`.13`) · `83f47f4 63091ce` (`.14`) · `f819f26 fdf1d99` (`.15`) · `240a56c 970197d dd67cda fcaf268` (`.16`) · `850e77e bc1b996 961d0ff 46bf675 58b1080 d16869c 7650b20 438608a 9636b7e` (`.17`) · `4b0d946 e15308d 11dbd23 baf05ed 5c8d2fd b10a5a7 a8dec16 fed3cff 760d20f` (`.18`) · `c3212cc` (`.21`, `.27`, `.28`) · `fd35416 5279a11 dff23f8 2abf419 ad6f31d 52fb6ff 3b88321` (`.33`) · `435a473` (`.38`) · `51bd1bc` (`.43`, `.44`) · `b94c9af` (`.44`, `.54`) · `29ad62f 74e9004` (`.54`) · `26d2dbf` (`.61`) · `209ed18 fa58556 f3c6eef b99daa7 9b170f0 760afed dcc20bb` (`.68`) · `380bc66 b653858 3f5bafc 993935d` (`.69`, `.72`) · `ca3754d` (`.62`).

**Non-commit hashes cited (md5s, correctly not treated as pins):** `e7ca150b` (runner), the five leg triples, `ce6f4116`, `500aae15`, `7dc040d9`, `83faf7ed`, `65326f85`, `14fa6afc`, `a584cb3e`, `c157dc31…`, `366f2143…`, `e5493312` (the corrupt prefix, corrected to `e549331a`).

### 3.3 NEAR-MISS dispositions (rule 15)

| # | As cited (unit) | Count | Verified referent | Disposition |
|---|---|---|---|---|
| 1 | `HEX3.C` (`.11`) | 0 | HEX3's addressable theorems verify as `THEOREM HEX3.A` (11) and `THEOREM HEX3.B` (8); no `.C` exists | Carried descriptively; source defect 2 |
| 2 | `u₃(M)` (`.11`, `.22`) | 0 | HEX3 writes `u(q,N)` (`:437`) / `u(M)` (`:389`) | GENIND-local notation |
| 3 | `W-11(iii)`, `W-11(i)` (`.04`, `.64`) | 0 | W-11 uses bare clause labels `(i)`/`(iii)`; parent `THEOREM W-11` count **3** | Carried descriptively |
| 4 | `[GENHN-HE(μ ≥ 3)]` (`.62`, `.64`) | 0 | **The note diagnoses it itself** at PE7-m3 (`.71`) and supplies the corrected reading | Carried with the note's own correction |
| 5 | `JC-F2` (`.14`) | not separately cited | Named only in the compound “JC-F1/JC-F2 [r1/r2]”; GENIND's substantive GRTJC cites are JC-F1, JC-LOAD, W-8, W-9 | Recorded so the merge does not treat it as consumed |

### 3.4 Reverse consumer edges: mathematical supply versus append protocol

`[TABLE — compiler ledger]` **This shard IS the note's own version of this table** (§S16, `.62`). The compiler's ledger adds only the protocol column and the unit map.

| Supplier | Direction | Verified designations | Consumption verdict (the note's) | Append/protocol status |
|---|---|---|---|---|
| W-12 | inbound movement across a repaired CRITICAL | 13 designations | SURVIVES, verbatim-re-verified (`.64`) | **Nothing landed by GENIND**; §S9.1 offers annex text, “W12_PROOF not edited” |
| HEX3 | inbound, 2 rounds (one conditionalizes S8.2 on **HEX3-BOX-1**, ledger HYP.137) | 10 | SURVIVES — corrected items uncited; tie at a frozen JSON | Nothing landed |
| HMENU3 | inbound, accepted + ANNEX A | 8 | SURVIVES — the correction moves TOWARD the consumed form | Nothing landed |
| W-11 | inbound, accepted | 1 | SURVIVES — zero content diff | Nothing landed |
| QSCOUT22 | inbound, verdict + annex | 1 | SURVIVES trivially — **nothing consumed** | Nothing landed |
| GENHN | pin UNMOVED, three errata queued | 8 | SURVIVES as-of, **disclosure owed** (discharged in shard 3) | Nothing landed |
| GENH4 | inbound, annex arc 0/2 with pass #2 unlanded | 9 | SURVIVES — verbatim-re-verified at the accepted body (`.65`) | Nothing landed |
| HE7 | never pinned | 0 | **Correctly absent**, recorded for total disclosure | Nothing landed |
| J-D0 / GRTJC / WELDMASTER / DULEMMA | unmoved | 8 | pins = HEAD or body unmoved (`.63`) | Nothing landed |
| W-10 | lineage pointer only | 1 (`W10-BOX-3`) | not in the stack; no pin tracked | Nothing landed; **source defect 1** |

**Zero consumption appends are claimed landed on any supplier by this note, and none is invented here.** The offered annex at `.07` is explicitly not landed.

---

## 4. NON-IMPORTS

`[TABLE — compiler ledger]` The negative fences homed in lines 1349–2551.

| Fence | Explicit material NOT imported / NOT proved / NOT claimed | Unit |
|---|---|---|
| No order-≥2 count law | “No count law at order ≥ 2 is claimed proved” | `.01` |
| GENIND.B is a reduction | “THEOREM GENIND.B is a REDUCTION; its unconditional content at n ≥ 4 is exactly the simple-stage layer + the criterion + the opening-mass laws” | `.01` |
| Per-route ledgers compressed | “proved as a schema with per-route ledgers compressed” | `.02` |
| d ≥ 2, prime-power | “The battery exercises d = 1 clusters at prime q only … machine-uncorroborated here” | `.03` |
| Drainage bookkeeping | “an induction whose β-term bookkeeping is displayed, not expanded per genre” | `.04` |
| Conditional structure | “the uniformity theorem at n ≥ 4 is a CONDITIONAL STRUCTURE, displayed, not a result” | `.05` |
| Reader-reimplementation seam | “Self-contained reader (fresh same-session code — GENIND-BOX-6's seam)” | `.06`, `.21` |
| Oracle scope | “oracle mixed-characteristic only” | `.06` |
| No supplier edits | “text offered; W12_PROOF not edited” | `.07` |
| Nothing consumed from the scout | “nothing consumed from it”; “No consumed clause exists to break” | `.16`, `.62` row 5 |
| No count law consumes the carry corpus | “No count law of S2–S6 consumes them” | `.14` |
| No axiom / no weld face | “No axiom, no weld face inside any count law” (scoped to count laws) | `.20` |
| No full run before the seal | “No full battery run before the seal.” | `.24` |
| Teeth do not certify theorems | “a tooth off its count voids the battery, not the theorems” | `.26` |
| §S11 frozen | “S11 stays frozen at its seal” — asserted by every one of the five records | `.31`, `.36`, `.44`, `.54`, `.61` |
| No machine leg at r3–r6 | “no machine leg was added … the machine evidence cited is [the verifier's] committed fresh leg, cited, not this note's” | `.36`, `.44`, `.54`, `.61` |
| Verifier reports untouched | “the two verifier reports are their authors' committed artifacts and stay untouched” | `.58` |
| Records may not quantify universally | “A theorem may quantify; a RECORD may not.” | `.54` |
| The acceptance does not close the box | “the acceptance freezes the reduction and its record, not the box” | `.72` |
| Annex-stack grade not inherited | GENH4's “annex-stack count is 0/2 with its pass #2 in flight … (not landed at this commit)” | `.18`, `.62` row 7 |

---

## 5. Teeth inverse table

`[TABLE — compiler ledger]` **This shard homes the battery's DESCRIPTION (`.21`–`.23`), its PREREGISTRATION (`.25`, `.26`) and its RUN-RECORD (`.28`, `.29`)** — the three that rule 19 separates. The guarded units are overwhelmingly in shard 1; the rows below therefore point *outward*, and the inverse direction (which shard-2 unit each row guards) is given in the second column.

| Battery row / instrument | Shard-2 unit(s) guarded | Disposition |
|---|---|---|
| **GT-PIN** 0/5, re-verified 5/5 at r6 | `.09`–`.19` (the pins' artifact side), `.62`, `.68` | Executable regression on artifact md5s; **does not guard note pins** |
| **GT-PART / GT-DEPTH0 / GT-BDRAIN / GT-ALPHA / GT-BETA / GT-RECUR / GT-BRACKETID / GT-CRIT / GT-N3TIE / GT-CONS / GT-ORACLE** | `.22` (their inventory), `.25` (their predictions), `.29` (their scores) | Executable regressions; per-family dispositions are in shard 1's §5 |
| **GT-T-ALPHA / GT-T-CS / GT-T-CRIT / GT-T-BRACKET**, fired at 12/12/4/24 | `.25`, `.28`, `.29` | Planted teeth, all fired at preregistered counts |
| **Pre-seal smoke run 1 (RED)** | `.24`, and shard 1 `.51` | Executable regression, **fired before the seal**, producing a MATH-side correction |
| **Pre-seal smoke run 2 + three probes** | `.24` | Executable regression; the cost probe's 1,048,576 partition audited exact |
| **`genindr2_supp.py`** (2,128,163/0; T1/T2/T4 fired) | `.32`, `.35` | Executable regression + three planted mutants |
| **`genind_pe3_fresh.*`** (705,133/0) | `.36`, `.37`, `.39`, `.40`, `.41` | Foreign-note (verifier) evidence |
| **`genind_pe4_fresh.*`** (6,507/0) | `.43`, `.44`, `.45`, `.46`, `.49` | Foreign-note evidence; C12's isolated re-run of the SEALED battery is the strongest single row (163,536/0 reproduced) |
| **`genind_pe5_fresh.*`** (109,146/0) | `.54`, `.55`, `.57` | Foreign-note evidence |
| **`genind_pe6_fresh.*`** (2,132,082/0) | `.61`, `.62` | Foreign-note evidence; realizes the same-side f-first genre corpus-first |
| **`genind_pe7_fresh.*` / `genind_pe8_fresh.*`** | `.72` | Foreign-note evidence; the two CLEAN passes' routes (d ≥ 2, n = 10; non-prime q, n = 12) |
| **git-log checks at commit time** | `.09`–`.19`, `.33`, `.38`, `.50`, `.60`, `.62`, `.63`, `.68` | **AUDIT: `in-house hostile pass` / `transfer audit`** — no battery row can perform these, which is the whole content of SERIES RECORD-INTEGRITY |
| **verbatim supplier-text matches** | `.64`, `.65` | **AUDIT: `transfer audit`** at verbatim granularity — the shard's gold-standard rows |
| **md5 re-enumeration at commit time** | `.53` (8, unreconciled), `.60` (13 ✓), `.68` (16 ✓) | **AUDIT: `arithmetic recount`**; two of three reconcile exactly |

**PROOF-ONLY rows (rule 16)** — guarded units whose content is a record or a fence, with the note's own coverage sentence:

| Unit | Coverage sentence |
|---|---|
| `.01` | “No count law at order ≥ 2 is claimed proved.” |
| `.02` | “per-route ledgers compressed … The n = 4, 5 pointwise machine families are the compensating instrument.” |
| `.03` | “machine-uncorroborated here beyond the w12-sealed order-1 instances” |
| `.04` | “displayed, not expanded per genre” |
| `.06` | “the reader-reimplementation seams (W10-BOX-3 lineage) inherited” |
| `.07` | offered text, never consumed — no coverage claimed |

**Both-direction audit.** Every row above guards at least one shard-2 unit. Every shard-2 unit whose TEETH field names a row appears in some row. Units with **`TEETH: NONE`** — `.01`, `.07`, `.08`, `.14`, `.15`, `.19`, `.20`, `.42` — are fences, plans, citations or inventory repairs and are outside the orphan count. **Zero battery-row orphans; zero toothed-unit orphans.**

**Signed vacuity / disclosure dispositions, enumerated** (rule 20): `.03` (d ≥ 2 and prime-power, for this note's own battery), `.06` (the reimplementation seam), `.16` (nothing consumed, so nothing guarded), `.62` row 7 (a de facto discharge riding an annex stack at 0/2), `.65` (the n = 4 exactness discharge is a citation, not a measurement). **`stale self-description` instances, enumerated** (rule 26): `.03` (coverage overtaken by PE7/PE8), `.07` (the offered annex text), `.30` (§S11's two frozen clauses — **not covered by the PE8-m1 cure**, OPEN-CALL 3), `.51` (the 14-group tally, falsified by C14's own correction), `.53` (the C1–C14 clause), `.55` (the HONEST LIMIT, closed by PE6 without edit).

---
## 6. BOUNDARY SELF-AUDIT (tag-sparse prose RECORD genre, template rule 9)

Zero `\tag{` in range. The material is boxes, bullets, pins, predictions, verdicts and repair records — so the boundary question here is different from shard 1's: not *where does a theorem end*, but **what counts as one record**. Every boundary below was chosen.

### 6.0 The rule applied

> **A unit is the smallest span carrying one complete claim together with its proof obligations.**

For record material the four-part test reads:
1. **Does the span carry a checkable claim of its own?** (a pin, a count, a verdict, a fence — yes; a connective — no.)
2. **Is the span cited BY DESIGNATION from elsewhere?** (`C14`, `S16 row 1`, `PE2-G2`, `GENIND-BOX-5` are all cited by name.)
3. **Does the span have its OWN supersession history?** — again the strongest splitter: this shard's records correct *each other*, so a span with its own `[rN]` bracket is addressable.
4. **Does the span have its own conditionality or consumer set?**

**Plus a fifth test specific to this genre, forced by rule 28:** *is the span one dated entry of a chronological arc?* If so it is a unit AND a series member, and the series must be reconstructible.

### 6.1 Boundaries drawn, with the arguable ones recorded both ways

**1. §S8's six boxes → six units (`.01`–`.06`).** Test 1 and 4: each box fences a different thing and three of the six are later moved (BOX-4 split by R1; BOX-5's close superseded; BOX-3 overtaken by PE7/PE8). *Not arguable.*

**2. §S9.3's eleven bullets → eleven units (`.09`–`.19`).** Test 2 and 3, decisively: each bullet is a separately re-pinned supplier with its own dated appends, its own consumption verdict and its own §S16 row. *Candidate A:* one “conditionality stack” unit. **Rejected** — seven of the eleven were edited at r6 and four were not, and the note's own scope claim (“the S9.3 bullets edited are exactly seven”) is only checkable if the bullets are addressable.

**3. The GENH4 bullet kept WHOLE (`.18`) with its four appends recorded as SERIES GENH4-PIN.** **Genuinely arguable, and the shard's clearest rule-28 application.** *Candidate A:* four units, one per dated append — they are dated entries of an arc, which is exactly what rule 28 says to split. *Candidate B (chosen):* one unit carrying an explicit four-entry series table. **Reason:** the four appends are not independent claims; each is a *revision of the same bullet's pin*, and only the last is live. Splitting would produce three units whose CANONICAL STATEMENT is superseded in full by the fourth, and a merge would have to re-derive which is TERMINAL. The series table gives the merge the order mechanically, which is what rule 28 actually asks for. *Cost:* the longest unit in the shard.

**4. §S10 split into `.21` (runner) / `.22` (families) / `.23` (roster) / `.24` (pre-seal) / `.25` (P-1…P-10) / `.26` (P-11) / `.27` (VERDICT: PENDING).** **Rule 19 applied twice.** `.21`/`.22`/`.23` are `instrument-record`s (apparatus, index, coverage — three different truth conditions); `.25`/`.26` are `preregistration`s; `.24` is a `run-record` (an executed pre-seal run). *Arguable:* whether P-11 splits from P-1…P-10. **Chosen split** because a falsifier is not confirmed by a clean run — its truth condition is disjoint from a point prediction's — and because §S11 scores it separately (“P-11 ✓ — no falsifier fired”).

**5. §S11 split into `.28` (headline) / `.29` (scorecard) / `.30` (consequence).** Test 3 and 4: the headline and scorecard are `run-record`s re-verified by an isolated re-run (C12); the consequence is a `scope-record` **two of whose clauses are stale and uncured**. Folding them would hide that the PE8-m1 cure reaches the first two and not the third. *Candidate A:* one §S11 unit. **Rejected on exactly that ground** (OPEN-CALL 3).

**6. Each repair record split into Arc + per-finding items + close (`.31`–`.35`, `.36`–`.43`, `.44`–`.53`, `.54`–`.60`, `.61`–`.68`).** Test 2 and 3: every finding is cited by designation (`PE2-G2`, `PE4-G1`, `C14`, …) and most carry their own in-place corrections from later rounds. *Candidate A:* one unit per record (five units). **Rejected** — `.33`, `.37`, `.43`, `.44`, `.46`, `.50`, `.53` each carry a distinct nested correction with its own kind, and a five-unit compilation could not express which sentence each `[rN]` layer edits.

**7. §S14's two sweep legs emitted as `[table]` units (`.47`, `.49`) with their count lines separate (`.48`, `.51`).** Test 1 and rule 22: a count line is a checkable claim of its own, and **`.51`'s is falsified by `.50`'s correction while `.49`'s content is not** — folding them would hide the stale tally. *Arguable:* whether the 15-class inventory and the 14-group audit should be one “sweep” unit. **Rejected** — different grep target sets (six vs nine), different verdict vocabularies, different outcomes.

**8. C14 split out of the claim-group table (`.50`).** **The shard's most consequential boundary call.** *Candidate A:* C14 is row 14 of `.49`'s table. *Candidate B (chosen):* its own unit. **Decided by three facts, any one of which suffices:** (i) C14 alone was later found FALSE and corrected in place, with its close quoted and replaced; (ii) it is the target of the fifth RECORD-INTEGRITY finding and therefore a series member; (iii) its replacement is not a corrected sentence but a **table** (`.62`), so a merge needs an addressable `TARGETS` edge from C14 to §S16's table. Under candidate A the table row's verdict column would have to read both “KEPT” and “FALSE → REPLACED”.

**9. §S16 split into Arc / table / unmoved list / two re-verifications / traces / PE6-m1 / freeze (`.61`–`.68`).** Test 1 and 4: **the two verbatim re-verifications (`.64`, `.65`) are epistemically different from the six cited traces (`.66`)** and the note says so (“RE-VERIFIED FROM THE SUPPLIER TEXTS THIS ROUND (not inherited from PE6's traces)”). Folding them would erase the evidence hierarchy that is §S16's main contribution.

**10. The post-PE7 corrections split into `.69`/`.70`/`.71`.** Test 2 and 4: three MINORs with three different targets and three different kinds (`wording-rider`, `inventory completion`, `wording-rider` on a locality). *Not seriously arguable.*

**11. The acceptance record split into `.72` (acceptance) / `.73` (the PE8-m1 cure).** Test 3 and rule 24: `.73` is a **bivalent unit** — simultaneously a new statement and an instruction to re-read frozen text elsewhere — so it needs its own `TARGETS` field (shard 1 `.01`; `s2of3.05`) and an explicit non-target list. `.72` is the terminal series entry. *Candidate A:* one acceptance unit. **Rejected** — the cure's non-target list (the five grade closes) is load-bearing and would be buried.

**12. Records NOT split further.** The five grade closes are folded into their records' final units (`.35`, `.43`, `.53`, `.60`, `.68`) rather than emitted as five SERIES entries of their own: they are one line each, they carry no independent claim beyond the counter, and `.72` pre-scopes them as round-dated records. **Recorded as arguable** — a merge preferring a GRADE-LINE series can reconstruct it from those five units' final quotes, and the series order is REPAIR-ARC's.

### 6.2 Merges deliberately NOT made

- **`.09` and `.62` row 1 stay separate** (the S9.3 bullet and its §S16 table row): they are two records of one supplier at two granularities, edited by different rounds, and PE7-m1 riders **both** — which is only expressible if both are addressable.
- **`.25` and `.29` stay separate** (rule 19): the preregistration's truth condition is “stated in advance”, the run-record's is “what the instrument returned”. Merging them is the specific failure rule 19 exists to prevent.
- **`.47`/`.49` are not merged with `.44`** (the Arc that commissions them): the Arc's coverage sentences were rescoped by PE5 and the legs' contents were not.
- **`.05` and `.72` are not merged** even though the second supersedes the first's close: `.05` carries the whole PE1–PE6 arc and only its final clause moves.
- **The eight rows of `.62` are not split into eight units:** no rider names an individual row (PE7-m1 and PE7-m3 name “S16 row 1”, which the table's own numbering makes addressable inside one unit), and the table's arithmetic audit is a property of the whole.

### 6.3 Format feedback (v3 rules under load in a RECORD-genre shard)

1. **Rule 28 (SERIES) is what makes this shard compilable at all.** Three series run through it, and **they are not nested and not co-extensive**: REPAIR-ARC has 5 in-range entries + 2 append entries + a terminal; RECORD-INTEGRITY has 5 entries that are a *different* selection of the same rounds; GENH4-PIN has 4 entries inside ONE unit. **Recommendation to the cross-read: allow a series to live inside a unit (GENH4-PIN) as well as across units, and require the series id + entry index + terminal marker as three separate fields.**
2. **Rule 22's arithmetic audit found three unreconciled numerals and reconciled nine.** Reconciled: the roster's four state counts and total (`.23`); the cost probe's exact partition of 2²⁰ (`.24`); all twenty-one preregistered spot values and four tooth counts (`.25`); the oracle's 36,838/73,676 (`.29`); §S16's scope claim of five sites and seven bullets (`.61`); the 13- and 16-md5 freezes (`.60`, `.68`); the C14-vs-table supplier coverage (`.62`); the sweep's 7 rewrites (`.59`); the 15- and 14-item count lines (`.48`, `.51`). **Unreconciled: `.53`'s “all eight md5 pins” (the enumeration gives 10), `.29`'s per-family total (163,526 vs the headline 163,536), and `.35`/shard-1's 2,128,163.** All three are recorded as disclosed non-reconstructions, none as a discrepancy. **This is a strong argument for extending rule 22 beyond `[TABLE]`s** (shard 1 made the same recommendation independently).
3. **The v3 enum needs a `supplier-finding` counterpart for the inbound direction.** Rule 13 added `supplier-finding` for a defect report *against* another note. This shard is full of the mirror case: a defect report *received from* a supplier's own arc, screened clause by clause (`.09`, `.17`, `.18`, `.62`). Filed as `scope-record`/`changes-record` faute de mieux. **Recommend `supplier-movement` as an enum member.**
4. **Rule 26's STALE-SELF-DESCRIPTION tag fired six times and needs a sub-distinction.** Three of the six are *pre-scoped* by the note (the five grade closes, via `.72`'s parenthetical) and three are *not* (`.03`, `.30`, `.51`). **The tag as written cannot say which.** Recommend `STALE-SELF-DESCRIPTION (pre-scoped)` vs `(uncured)`; the uncured ones are what a chapter cut must carry.
5. **Rule 18's kinds needed one addition here:** `.17`'s `[r6]` append is an `as-of scoping` that simultaneously **creates an owed obligation** discharged two shards later. Filed as `as-of scoping + owed-disclosure`. **Recommend an explicit `owed-disclosure` marker**, because the obligation is exactly the kind a merge must not drop.
6. **Rule 23's PIN VERIFICATION was decisive at scale.** 87 distinct commits cited, 87 resolve, 28 artifacts present — and the one pin defect in the whole range (`e5493312` → `e549331a`) was an md5, caught by the note's own commit-time re-verification and disclosed at `.58`. **Recommendation: distinguish `commit-pin` from `artifact-md5-pin` in the rule; they fail differently and are checked differently.**
7. **The shard's most important structural finding, for the DAG:** **every one of the five RECORD-INTEGRITY findings was produced by a fresh-context read of the repo, and none by any battery row.** The note's own remedy escalated four times — pin-at-repair-HEAD (r2) → commit-time git-log check (r3) → grep-scoped full sweep (r4) → ban the universal register (r5) → **abolish the summary sentence and replace it with a per-supplier table (r6)** — and only the last one held. That escalation is the corpus's single best documented answer to “how do you make a record checkable”, and it belongs in the merged spec as a method note, not only as an arc.

---

## 7. SHARD NOTES

- **Cross-shard supersessions applied (four sources, all inbound to this range).**
  (1) **ANNEX R R1.0/R1.4** (shard 3) → `.04` (GENIND-BOX-4 split: the per-genre prefactor pricing STANDS; the hypothesis-wiring gap is CURED).
  (2) **ANNEX R R6.1** (shard 3) → `.72` (a defect in the **PE8 acceptance report** this record cites; the report itself is untouched per freeze predicate 4).
  (3) **The dated supplier-movement record** (shard 3) → `.17`, `.62` row 6 (discharges the owed execution disclosure and screens all seven PE7-m2 sites).
  (4) **The ANNEX R head** (shard 3) → re-verifies this shard's body freeze (lines 1–2464 within 1–2548).
  **Outbound (this shard resolving shard 1):** `.73` supersedes shard 1 `.01`'s arc line; `.47` site classes 2–14 classify shard 1's window displays; `.49` C1–C13 audit shard 1's record sentences; `.25`'s spot values are the derivability check on shard 1's `.48`–`.51`; `.62` re-pins every supplier shard 1 cites.
- **Range-edge audit.** Line 2548 is the acceptance record's last content line (“is touched by this append. [GENIND-H] at n ≥ 4 remains the displayed OPEN box — the acceptance freezes the reduction and its record, not the box.”); line 2549 is blank; line 2550 is `---`; line 2551 is blank; line 2552 opens `## ANNEX R`. **No source statement unit is cut at the edge.** The boundary falls exactly on the annex break — and, notably, exactly at the pre-annex byte-freeze boundary (md5 `eefcf658` covers lines 1–2548), so **this shard's HOME range is almost exactly freeze predicate 2's scope.**
- **Outside-HOME material used only as resolver:** lines 1–1348 (the mathematics, shard 1) and lines 2552–3872 (ANNEX R, the supplier-movement record, ANNEX R — r1, the two 2026-08-12 dated corrections; shard 3).
- **Protocol versus supply.** The supply here is STATUS, not mathematics; **no consumption append is claimed landed on any supplier**, and none is invented. Eight inbound supplier positions and eight in-house hostile passes are recorded at their targets.
- **Numbering.** Temporary IDs `EFF.GENIND.s2of3.01`–`.73`, to be reconciled at the merge run.
- **MERGE HAZARDS TO FLAG (six).**
  1. **`.30` (§S11's consequence) carries TWO uncured stale clauses** — “Attempt 0/2; the hostile arc has not begun” and the “conditional exactly on [GENIND-H] … plus the supplier arc grades” scoping. The PE8-m1 cure names two other lines and not these. **A chapter cut quoting §S11's consequence will quote a false status sentence unless the merge installs the edge `.30 → .72` explicitly.**
  2. **`.51`'s count line is falsified by `.50`'s own correction** (“9 verified and kept (C6–C14)” — C14 was not). The correction lives inside C14 and the tally is unedited.
  3. **`.62` row 7's SURVIVES rides an annex stack at 0/2 with pass #2 unlanded.** The n = 4 de facto discharge of (CS-EXACT) inherits that grade; shard 1 `.66` must be read with it.
  4. **`.17`'s owed disclosure is discharged in shard 3, and the discharge CHANGES shard 1's conditionality at n ≥ 8.** Install `.17 → (shard 3 supplier-movement record) → shard 1 .15` as a two-hop edge.
  5. **`.09`/`.62` row 1's SURVIVES rests on a STRENGTHENED (A1)** whose closure this note never re-derives (shard 1 `.30`; OPEN-CALL 1 here).
  6. **`.11` carries ledger row HYP.137** (`HEX3-BOX-1`, class conditional-theorem-leg, disposition MATH). Its scope is narrow and must not be widened: it conditions HEX3's W-12.B corroboration aside, **not** GENIND's induction and **not** `hExhaust3`. The ledger's premise correction must travel with it.

---

## 8. Self-audit and OPEN-CALLS

### OPEN-CALL 1 — the strengthened (A1) is consumed but its closure is never re-derived

§S16 row 1 and `.64` record W-12's r4 as adding a σ-LABELING clause INSIDE (A1) and verdict the consumption as surviving on the ground that “more is demanded of P(n), nothing less is delivered by the theorem”. **That reasoning is right for W-12.D's firing and silent about LEMMA GENIND-0**, whose whole content is that (A1)-admissibility is closed under products, unions and affine re-parameterizations (shard 1 `.30`) — a closure stated for the pre-r4 predicate and consumed at Steps 1 and 2 to multiply menus that must now carry σ-labels. **Not a claimed error**; the closure may be trivially preserved. **Decision needed at 0b/chapter time: whether GENIND-0's closure must be re-derived under the r4 (A1) before formalization.** (Raised identically at shard 1 OPEN-CALL 3; recorded at both ends because the evidence is split across shards.)

### OPEN-CALL 2 — `.73`'s preregistered predictions (shard 1) still have no recorded outcome, and the scout's display moved

Shard 1 `.73` hands two falsifiable predictions to QSCOUT22's GENRE-E table; `.08` item 1 states the upgrade rule; `.16`'s `[r6]` append records that the scout's arc completed (VERDICT `dd67cda`, GREEN 7,614,473/0) **and that its genre-E UND display carried an h = 1 slip corrected by annex `fcaf268`**. **No sentence anywhere in GENIND records whether the predictions were scored, against which version of the display, or with what result.** The compiler has not inferred an outcome from the scout's GREEN (which scores the scout's own predictions). **Decision needed: whether the merged spec carries a “preregistration with no run-record” row, and whether GENIND owes a dated append recording the outcome.**

### OPEN-CALL 3 — the PE8-m1 cure does not reach §S11's stale status clauses

`.73` supersedes exactly two frozen arc lines by name and pre-scopes the five per-round grade closes as round-dated records. **§S11's closing paragraph (`.30`) is neither**: “Attempt 0/2; the hostile arc has not begun” sits in the frozen body, is not a per-round grade close, and is not named by the cure — yet it is false at acceptance by two passes and a grade. Its neighbouring clause (“conditional exactly on the composite-stage package [GENIND-H] per genre plus the supplier arc grades”) is likewise overtaken at n ≥ 8. **Decision needed: whether the merged spec tags `.30` STALE-SELF-DESCRIPTION (this compilation's choice, recorded), or whether GENIND owes a dated append extending the PE8-m1 cure to §S11's consequence paragraph.** No silent repair was made.

### OPEN-CALL 4 — `.53`'s “all eight md5 pins” does not reconcile, and the r5 sweep adjudicated it compliant

The §S14 close asserts “all eight md5 pins re-verified at commit time, listed in the Arc paragraph”; the Arc paragraph enumerates **ten** (runner + three triples). §S15's universal-sentence sweep (`.59`) explicitly adjudicated this sentence **KEPT** as rule-compliant, on the ground that its quantifier ranges over an enumerated set — **without recounting the numeral.** The later freeze lines (`.60`'s 13, `.68`'s 16) both reconcile exactly, so the defect is local. **Decision needed: whether a numeral that disagrees with its own enumeration is a record defect the standing rule should catch** (it is exactly the class the rule was written for, and the rule's own sweep passed it).

### Recorded source defects (flagged, not silently repaired)

1. **`.06`: `W10-BOX-3` is cited as a lineage pointer to a note that is NOT in the conditionality stack.** The designation verifies (`W10_PROOF_2026-08-08.md`, count 1), but W-10 has no §S9.3 bullet, no pin, and no §S16 row — so the “reader-reimplementation seams … inherited” claim rides an untracked supplier. Recorded; not repaired.
2. **`.11`: `HEX3.C` names no theorem in HEX3** (count 0; the file's addressable theorems are `THEOREM HEX3.A` and `THEOREM HEX3.B`). The bullet's other designations all verify.
3. **`.22`: GT-CONS has no preregistered prediction of its own.** Twelve families are declared; eleven predictions are made; GT-CONS appears only inside P-11's falsifier clause and in the roster's constructed legs. Its checks are scored inside other families' counts. Recorded as a coverage gap in the preregistration, not as an error.
4. **`.29`: the per-family counts sum to 163,526 against the headline 163,536** (difference 10). The artifacts are md5-pinned and are the authority; the itemization is not displayed. **Recorded as a disclosed non-reconstruction, NOT a discrepancy.**
5. **`.53`: “all eight md5 pins” against an enumeration of ten** — OPEN-CALL 4.
6. **`.65`: genre F's “TWO-term q-power sum at even N” collapses to a single q-power.** At even N, `2⌊N/2⌋ = N`, so `q^{N+2k−1} + (q−1)q^{N+2k−1} = q^{N+2k}`. The note's phrase is faithful to the *displayed form* and the (CS-EXACT) requirement (“a FINITE SUM of q-powers”) is met either way; recorded as an observation because the “two-term” language drove a granularity correction across three sites (`.34`).

### Fidelity audit

- Every CANONICAL STATEMENT is a verbatim source quotation or is explicitly marked `[ASSEMBLED]`. **No count, pin, hash, date, verdict, grade or quantifier was altered anywhere.** Where a source span is quoted in two pieces (`.49`/`.50`, `.38`/`.72`'s arc, `.28`/`.29`), each piece is byte-verbatim and the union is the whole minus nothing; every split is flagged at the unit and audited at §6.1.
- Truncations inside quotations: **none used in this shard.**
- Nested `[rN]` brackets are reproduced in place with their quoted false originals intact. **Nothing quoted here as “FALSE” is presented as live text**, and every one of the note's five record-integrity findings is carried with both its false original and its correction.
- **The one source table (§S16's) is transcribed as a table and flagged `[TABLE]`** (`.62`); the two §S14 sweep inventories are transcribed as `[TABLE]`s with their class labels and verdicts quoted (`.47`, `.49`). No source table is prosified. Rule 14's double-emission does not fire: there is no fixed-width ASCII table in range.
- **59 external XREF designations, every one grep-verified with a fixed-string count ≥ 1** (§3.1); five candidate designations with count 0 are recorded as NEAR-MISS dispositions (§3.3) with their verified referents, one of them (the `[GENHN-HE]` case) diagnosed by the note itself.
- **87 distinct commit pins `git cat-file -t`-verified — 87/87 resolve** (§3.2); 28 artifact files verified to exist. Non-commit hashes (md5s) are listed separately and are not treated as pins.
- **Twenty-one units carry compiler-computed arithmetic audits**; nine numerals reconciled exactly, three recorded as non-reconstructible with the artifact named as authority.
- Status and mathematical content are kept as distinct predicates throughout: this shard supplies STATUS, and every mathematical claim it references is resolved to a shard-1 unit rather than re-asserted.
- Out-of-range material is used only to resolve in-range HOME units (resolution rule 8); shards 1 and 3 own the mathematics and the annex stack.
- **Honest limitation of this shard:** four correction sources are physically in shard 3 and the whole mathematical substrate is in shard 1. Every affected unit quotes the governing text verbatim, so shard 2 is self-contained as a *reading*, but the merge must install the six edges listed in §7.

EFF-GENIND-s2of3 COMPILED: 73 statements / 59 xrefs verified / 87 commit pins verified / 5 near-misses / 4 open calls
