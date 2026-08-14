# EFF-GENIND-s1of3 — CANONICAL EFFECTIVE-SPECIFICATION SHARD

**COMPILED-BY: opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). CODEX CROSS-READ OWED (post-reset).**

## 1. Shard header

**Source note:** `lean/notes/openmath/GENIND_PROOF_2026-08-08.md` (3872 lines).

**HOME range:** source lines 1–1348 inclusive (title + Unit/Status/Instrument front matter + §S0 reconciliation + §S1 THEOREM GENIND.A / THEOREM GENIND.B + §S2 LEMMA GENIND-1 + §S3 LEMMA GENIND-2 + §S4.1 LEMMA GENIND-3 + §S4.2 LEMMA GENIND-0 + §S4.3 LEMMA GENIND-6 + §S5 the composite-stage criterion, the simple-stage layer and the n = 4/5 CS genre tables + §S6 the proof of THEOREM GENIND.B + §S7 the [GENIND-H] display, LEMMA GENIND-4, CANDIDATE GENIND-5 and the work order). Later text (§S8–§S16, the dated corrections/acceptance records, ANNEX R, the dated supplier-movement record, ANNEX R — r1, and the two 2026-08-12 dated corrections) is used ONLY to resolve material homed in that range.

**HEAD blob hash:** `8ef694fefc24c5fb07e4e80c306ff2136c914b61` (clean in the working tree; last touched by commit `5e33b01f`).

**Compilation context:** `spec/EFF_TEMPLATE_v2.md` at its current HEAD (rules 1–10 = v2; rules 11–28 = v3, the prose-genre rules). Temporary IDs `EFF.GENIND.s1of3.<nn>`.

**GENRE: TAG-SPARSE PROSE PROOF.** `grep -c '\tag{'` over the whole note = **13**, and **all 13 sit at lines 3333–3837** (the two 2026-08-12 dated corrections' LaTeX displays, shard 3). Inside this shard's HOME range the tag count is **0**. Statement boundaries here are therefore CHOSEN, not read off display tags; §6 is the mandatory BOUNDARY SELF-AUDIT (template rule 9), with both candidates recorded wherever the call was genuinely arguable. What the note has instead of tags: bold `LEMMA/THEOREM/CANDIDATE THEOREM/ANNEX-LEMMA` openers inside blockquotes (marking *some* units), bold prose headers (`**Honesty note (the GENIND-3 grade).**`, `**The gap this closes.**`, `**Instances …**`), indented ASCII displays, `[r1]`…`[r6]` correction brackets (frequently mid-sentence and frequently NESTED — `[r3 …[r4 …[r5 …]]]`), and long unmarked prose.

### Governing effective-text record

The note states no single "the effective text is …" sentence. It states the rule in five places, and the five agree; the effective text is DERIVED from them (template v2 header rule; the T3 precedent's "derive it and state the facts that fix it").

**(i) The body is frozen at acceptance** (Dated acceptance record, lines 2510–2523, out of HOME range):

> “**GENIND IS ACCEPTED 2/2; the text is FROZEN — dated appends only.**
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
> purely additive).”

**(ii) Every repair round r1–r6 was applied IN PLACE and tagged, not by append.** Each repair record says so of itself; §S16's Arc paragraph is the last (lines 2330–2339): “This r6 is THE SUPPLIER RE-PIN ROUND … C14 corrected in place at S14 with the false close quoted”. §S13's heading (line 1833) is representative of the whole series: “appended at r3 — S11 stays frozen at its seal, S12 corrected in place where its own sentence was the finding”. **So every `[r1]`/`[r2]`/`[r3]`/`[r4]`/`[r5]`/`[r6]` bracket inside lines 1–1348 is already-landed base text, not a supersession to be applied.** Where a bracket quotes the false original it superseded, the quoted original is a dated record, not live text.

**(iii) Post-acceptance repairs are dated annexes that name their exact target.** ANNEX R's head (lines 2567–2571):

> “The accepted text above is BYTE-FROZEN: full file before this append
> = 158,427 bytes, md5 `eefcf6584bbb0917875e77c9fcab7a9e` (2,548
> lines), verified identical before and after; within it the
> PE8-verified body freeze (lines 1–2464 md5 `14fa6afc…`) was
> re-executed this round and matches.”

**(iv) The annex layer is itself frozen and separately re-verified.** ANNEX R — r1's Provenance (lines 3106–3111): “The accepted body stays byte-frozen (lines 1–2548 md5 eefcf658, re-verified at this commit); the ANNEX R text above is edited at exactly five [ar1 2026-08-10]-tagged sites”.

**(v) The 2026-08-12 dated corrections append below the annex layer without touching it:** “Everything above this heading is byte-untouched by this append.” (line 3306).

**EFFECTIVE TEXT FOR THIS SHARD = lines 1–1348 exactly as written (r1–r6 already landed), READ AS CORRECTED by the out-of-range dated appends wherever they name an in-range sentence.** Eleven such correction sources land in this shard's range (§7 lists them with their targets); each is applied at its unit and its governing text is quoted there. **No in-range sentence is deleted by any later round** — every correction is a supersession that quotes or names its target and leaves it byte-intact.

### FREEZE PREDICATES (template rule 21 — three independent freezes; one must never stand for another)

1. **BODY TEXT-FREEZE (acceptance).** Predicate: lines 1–2464 are byte-frozen as of the PE8 acceptance. Quote: “PE8 re-verified the body's byte-freeze (lines 1–2464 md5 14fa6afc == 993935d, the post-PE7 annex purely additive)” (lines 2521–2523). Pin: `993935d` (`git cat-file -t` = commit ✓); acceptance verdict commits `380bc66` (PE7) and `3f5bafc` (PE8), both ✓.
2. **PRE-ANNEX TEXT-FREEZE (annex baseline).** Predicate: lines 1–2548 (body + the two dated records) are byte-frozen at md5 `eefcf658…`, re-verified at every annex commit. Quote: “full file before this append = 158,427 bytes, md5 `eefcf6584bbb0917875e77c9fcab7a9e` (2,548 lines), verified identical before and after” (lines 2567–2569). This is a DIFFERENT predicate from (1): it covers 84 lines that (1) does not.
3. **INSTRUMENT-FREEZE (artifact seal).** Predicate: the sealed runner and every committed artifact are byte-frozen since the seal and re-verified by md5 at each round's commit time. Quote (§S16, lines 2440–2449): “**Byte-freeze at this commit (enumerated, re-verified by md5sum this round):** sealed runner e7ca150b; r2 supp triple 7335fc16/63b7413a/6c93f29c; PE3 fresh triple fce9cb08/2075dd28/360eb239; PE4 fresh triple aa2b9af8/1a29a9c1/e549331a; PE5 fresh triple 6ef3132e/a0452521/bdc04c4d; PE6 fresh triple 87b0f27e/1c2f8eed/fb473a57 … — 16 md5s”. Pin: seal commit `c3212cc` ✓. The instrument freeze is what makes “no committed number moves” checkable independently of either text freeze.

### Scope split (template rule 7 + rule 17 — three predicates, never conflated)

**A. ABSORPTION / supply SET** (what the note claims to prove). In range, §S0's closing line and the two GRADE boxes fix it; the note's own one-line inventory is out of HOME range (§S9.3, lines 1603–1608, homed in shard 2):

> “**One line: THEOREM GENIND.A(I,II,IV) + GENIND.C's hypothesis set =
> {W-11, W-12.A/L0/L1, HEX3, HMENU3 @ pins + this note's lemmas};
> GENIND.A(III) adds the S4.1 ledger-compression honesty; THEOREM
> GENIND.B adds [GENIND-H] as its displayed hypothesis; the FULL
> uniformity consequence consumes THEOREM W-12.D @ pin. No axiom, no
> weld face inside any count law; grade = composition 0/2.**”

The in-range supply proper is: LEMMAs GENIND-0, -1, -2, -3, -4, -6; THEOREM GENIND.A(I)–(IV) with its GRADE; THEOREM GENIND.B with its GRADE; THEOREM GENIND.C; the S5.1 criterion; the S5.3 genre laws; and CANDIDATE THEOREM GENIND-5 as an explicitly unproved candidate.

**B. APPEND / consumption PROTOCOL scope** (what has been landed on other notes). **GENIND lands NOTHING on any supplier — an explicit NO-APPENDS declaration.** In range, §S0's last line (line 112):

> “This note edits no supplier note. Proposed annex texts: §S9.”

and out of range but governing, §S9.1's heading (line 1429): “Proposed annex to W12-BOX-1 / the [W12-H] box (**text offered; W12_PROOF not edited**)”. No dated “absorbed by GENIND” append is claimed landed on W-12, W-11, HEX3, HMENU3, GENHN, GENH4, GRTJC, J-D0, QSCOUT22 or WELDMASTER/DULEMMA, and none is invented below.

**C. INBOUND corrections RECEIVED** (rule 17). Two channels, both live:
* **From the note's own hostile arc** — eight passes PE1–PE8 plus the Codex ratification leg plus two sol certification runs. Six of those (r1–r6) landed IN PLACE inside this shard's range and are therefore already base text (record (ii)); the rest land as dated appends in shards 2–3 and are applied at their units.
* **From suppliers.** The GENHN arc moved after this note's pin: the dated supplier-movement record (lines 3032–3094, shard 3) discharges the owed disclosure and CHANGES this note's displayed conditionality at n ≥ 8. GENH4's annex arc moved twice after r5 (§S16 row 7). Both are inbound; neither is an append GENIND made on a supplier.

### Resolution rules applied

1. Lines 1–1348 supply the HOME material listed in HOME range above.
2. `[r1]`…`[r6]` brackets inside the range are ALREADY-LANDED text (record (ii)), applied at their own sites in chronology; a later bracket governs the earlier text it names, and **nested brackets are read outermost-first in date order** (e.g. at `.24` the chain is sealed display → `[r3, PE3-G2]` → `[r4, PE4-G1]`, with `[r4]` correcting `[r3]`'s own gloss, not the sealed display).
3. **The dated acceptance record's PE8-m1 cure (lines 2528–2538, shard 2) supersedes the header arc line by name**, quoting it verbatim; carried at `.01`.
4. **ANNEX R (lines 2552–3028, shard 3) supersedes or riders six in-range items:** R1 pins P(k)'s fourth member to (A2-RATE) (`.13`) and supplies §S5.2's consumed vanishing rate (`.45`, `.46`); R2's unit-pivot rider covers GENIND-6(c) AND GENIND-3 step (3) (`.36`, `.24`); R3's window-1 convention rider extends S1's conventions and four consumption sites (`.07`, `.21`, `.24`, `.34`, `.38`, `.45`); R4 adds CS4-F's missing visibility floor at TWO displays (`.11`, `.49`); R5 scopes GENIND.A(IV)'s converse to DEGREE level (`.11`); R6 riders Step 4's frozen `[r1]` record with the identity-vs-bound separation (`.58`).
5. **The dated supplier-movement record (lines 3032–3094, shard 3) moves the conditionality of the GENIND.B consequence clause at n ≥ 8** (`.15`, and by inheritance `.13`, `.61`), and completes the GENHN consumed-surface inventory that touches `.34` and `.57`.
6. **The two 2026-08-12 dated corrections (lines 3298–3872, shard 3) are homed in shard 3** (ANNEX-LEMMA GENIND-C2 / C2Q / C2D and the C2-G1/G2/G3 repairs), but their consumer sweeps reach in-range units: the `(CS-1) only` → `(CS-1Q), verified per genre` upgrade re-conditions the CS-drain rate consumed at `.37`(d) and `.57` (Step 4). Carried as CONDITIONALITY at both.
7. Where an out-of-range correction lands on an in-range unit, the corrected reading is carried in that unit's CANONICAL STATEMENT (when the correction is a “read X as Y” substitution on a display) or in its CONDITIONALITY (when it is a scope pin or a hypothesis upgrade), and the superseded sentence is quoted whenever it is load-bearing — the note keeps it byte-intact above.
8. Out-of-range statements are NOT emitted as units here merely because they resolve in-range text. §S8's boxes, §S9's stack, §S10/§S11's battery and verdict, §S12–§S16's repair records, ANNEX R's R1–R6 and GENIND-C1/C′, ANNEX R — r1's GENIND-C2, and the 2026-08-12 C2Q/C2D/C2-G1/G2/G3 material are homed in shards 2 and 3.
9. External repo records (pass reports, `verification/openmath/*` artifacts, supplier notes, `runs/cert*/…` logs) are **reading notes only**, never edits.

### Quotation and table discipline

CANONICAL STATEMENTs are verbatim source quotation or explicitly marked `[ASSEMBLED]`; truncation inside a quotation is marked `…`. The note's indented ASCII displays are reproduced with their line structure intact; the only presentational change is Markdown blockquote framing. **This shard's HOME range contains NO source table** (Markdown or ASCII-fixed-width): §S5.3's "genre tables" are bulleted law lists and are emitted as statement units, not tables; the note's only Markdown table is §S16's per-supplier fired-clause table (shard 2). Rule 14's double-emission therefore does not fire in this shard. Compiler-authored ledgers (§3, §4, §5) are flagged `[TABLE — compiler ledger]` and are not source statement units.

---

## 2. Statement inventory

### EFF.GENIND.s1of3.01  [changes-record]

**CANONICAL STATEMENT:** FORM: display (title) + bold-headed paragraph (Status). [ASSEMBLED — the title headline, line 1, plus the Unit/Status arc block, lines 3–50, both quoted verbatim]

> “# GENIND — THE GENERAL TWO-SPECIES INDUCTION (the (hMenu-n)+(hExhaust-n) package for ALL n at once): every refinement history decomposes into α-nodes (self-similar, bracket (Q−1)Q^{(m(m−1)/2+1)μ−1}) and β-nodes (products of strictly-lower-degree systems indexed by the realized partition), the induction scaffold PROVED conditional on the per-stage classification, the simple-stage layer delivered by W-12.A + the transports, the composite-stage criterion DERIVED EXACTLY (a stage with ≥ 4 keys: n ≥ 4, NOT primality — n = 5 is composite-bearing), and the composite-stage law displayed as the frontier with the quartic (2,2) bracket attempted from the weld corpus”

> “**Unit:** GENIND (the general-induction composer; Asvin's 2026-08-08
> directive on reading HMENU3: "we now have the shape of a general
> inductive argument! Exhilarating, lets keep going!" — ledger 66057f4).
> **Attempt grade 0/2** (composed; hostile pass PE1 adjudicated
> UNREFUTED NOT CLEAN, 0 CRITICAL + 3 GAP + 4 MINOR, all three GAPs at
> the GENIND.B ↔ [GENIND-H] seam — `GENIND_passPE1_report.md`
> @ 4259a93; r1 repairs applied in place, [r1]-tagged; hostile pass PE2
> adjudicated UNREFUTED NOT CLEAN, 0 CRITICAL + 2 GAP + 1 MINOR —
> `GENIND_passPE2_report.md` @ 50db400 — r2 repairs applied in place,
> [r2]-tagged: LEMMA GENIND-6 at S4.3 (PE2-G1, the mixed-opening
> transport, with the additive supp leg §S12) + the (CS-EXACT)
> discharge re-pin/disclosure (PE2-G2) + the granularity gloss
> (PE2-m1); hostile pass PE3 adjudicated UNREFUTED NOT CLEAN,
> 0 CRITICAL + 2 GAP + 4 MINOR — `GENIND_passPE3_report.md` @ f89b565
> — r3 repairs applied in place, [r3]-tagged: the capped M_l window
> display (PE3-G2, S4.1 + S4.3) + the GENH4 re-pin corrected with the
> pin-check violation disclosed (PE3-G1, Step 4/S7.1/S12/S13) + the
> four MINOR records; hostile pass PE4 adjudicated UNREFUTED NOT
> CLEAN, 0 CRITICAL + 2 GAP + 0 MINOR — `GENIND_passPE4_report.md`
> @ ade9bac — r4 repairs applied in place as a FULL-SWEEP audit (§S14:
> exhaustive window-site inventory + record-claim audit, the arc's
> third consecutive record-integrity defect answered by method, not
> spot repair), [r4]-tagged: GENIND-3's proof step (1) rewritten to
> the capped content window with the corrected reduction parenthetical
> (PE4-G2, S4.1 + the S4.3 proof-of-(a) echo) + the regime inventory
> restated to the machine-verified claim (PE4-G1, S4.1 statement
> bracket + honesty note + S13); hostile pass PE5 adjudicated
> UNREFUTED NOT CLEAN, 0 CRITICAL + 1 GAP + 2 MINOR —
> `GENIND_passPE5_report.md` @ bd9bce1 — r5 repairs applied in place
> (§S15), [r5]-tagged, implementing the STANDING RULE (ledger
> b94c9af: record sentences may not quantify universally — enumerated
> or pattern-scoped only): the false f-first entry law fixed with the
> m = 6 mixed grammar enumerated (PE5-G1/PE5-m1, S4.3), S14's two
> universal-coverage sentences rescoped to their executed pattern
> scope with PE5's outside-scope witness displayed (PE5-G1), the
> same-side COMPOSITE case added to step (1)'s enumeration (PE5-m2,
> S4.1), a 7-rewrite universal-sentence sweep, and the corrupt
> PE4-results pin transcription corrected (e549331a); hostile pass
> PE6 adjudicated UNREFUTED NOT CLEAN, 0 CRITICAL + 1 GAP + 1 MINOR —
> `GENIND_passPE6_report.md` @ 265a562/ad1bd98/f7f45f1, the same-side
> f-first genre machine-realized corpus-first (2,132,082/0) — r6
> repairs applied in place (§S16), [r6]-tagged, THE SUPPLIER RE-PIN
> ROUND: the S9.3 stack re-pinned at the suppliers' current HEADs
> with per-supplier fired-clause rows (PE6-G1; S14 C14's false
> git-log-check close corrected in place and replaced by the S16
> table) + three dated appends on the stale arc parentheticals
> (PE6-m1); every consumption verdict SURVIVES at the new pins — the
> clean count has NOT started — PE7 attempts the first clean).”

**CONDITIONALITY:** **STALE-SELF-DESCRIPTION → then superseded.** The grade sentence “**Attempt grade 0/2**” and the arc close “the clean count has NOT started — PE7 attempts the first clean” were true as of r6 and are **explicitly superseded by name** by the dated acceptance record's PE8-m1 cure (lines 2528–2538, shard 2), which quotes the arc close verbatim and cannot edit it because it sits inside the byte-frozen body:

> “**PE8-m1 cure (PE8's one MINOR, the stale-arc class PE6-m1 named):
> the two arc-state lines inside the frozen region are SUPERSEDED by
> this append.** Both sit in the byte-frozen body and could not be
> edited in place; each reads as of r6, two passes stale at acceptance —
> quoted verbatim:
> * Header arc line, L49–50: "the clean count has NOT started — PE7
>   attempts the first clean)." — superseded: the count ran 0/2 → 1/2
>   (PE7 CLEAN, 380bc66) → 2/2 (PE8 CLEAN, 3f5bafc); ACCEPTED.”

**SUPERSESSION KIND:** `counter re-reading` (the grade counter is re-read 0/2 → 2/2; no wording of the frozen sentence is replaced and no scope is pinned).

**CHAIN:** frozen header arc line (L49–50, as of r6) → PE7 CLEAN 380bc66 (0C+0G+3M; count → 1/2) → post-PE7 dated corrections annex b653858 (cures the three MINORs) → PE8 CLEAN 3f5bafc (0C+0G+1M; count → 2/2) → **Dated acceptance record L2512 “GENIND IS ACCEPTED 2/2; the text is FROZEN — dated appends only.” — TERMINAL.** A chapter cut must read the TERMINAL member; the frozen text is a dated record only.

**DERIVATION:** Not a mathematical unit; the record is the note's own status chronology, each round pinned to its report commit. All eight report pins `git cat-file -t`-verified: 4259a93 ✓, 50db400 ✓, f89b565 ✓, ade9bac ✓, bd9bce1 ✓, 265a562 ✓, ad1bd98 ✓, f7f45f1 ✓, 380bc66 ✓, 3f5bafc ✓.

**RESOLUTION TRACE:** statement lines 1, 3–50. proof lines — none (record). correction sites: 1414–1415 (§S8 GENIND-BOX-5's identical arc close, shard 2, superseded by the same append), 2528–2543 (the PE8-m1 cure, shard 2).

**TEETH:** The counts quoted (PE1 0C+3G+4m … PE6 0C+1G+1m) are report-pinned, not battery-guarded; the “2,132,082/0” figure is PE6's committed leg `genind_pe6_fresh.*` @ ad1bd98 (md5 triple 87b0f27e/1c2f8eed/fb473a57, in §S16's frozen list). Battery rows are inventoried in shard 2.

---

### EFF.GENIND.s1of3.02  [instrument-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph. verbatim, lines 51–63.

> “**Instrument:**
> sealed two-commit battery `verification/openmath/genind_checks.py` —
> the two-species classification machine-checked at n = 4 AND n = 5 on
> targeted rosters (full-sweep rows where the state space permits;
> CONSTRUCTED targeted loci where it does not, e.g. the first n = 5
> α-node at N = 6 and the first n = 4 depth-2 α at N = 9), with the
> depth-0 species partition both directions, the α-transport pointwise,
> the β-fracture pointwise (scale-then-Hensel + child re-read), the
> drainage first-step recursion, the composite-stage criterion with two
> flagship genre laws per degree, an n = 3 negative control tied to the
> committed hex3 artifacts, a PARI σ-oracle leg, and ≥ 3 teeth at
> preregistered exact fire counts. Verdict §S11, appended at commit 2
> FROM the committed artifacts.”

**CONDITIONALITY:** Unconditional as a description of the apparatus. Two disclosed limits, both stated by the note itself out of range: the battery “exercises d = 1 clusters at prime q only” (GENIND-BOX-3, lines 1361–1366, shard 2), and the runner is a **fresh same-session reimplementation** (“Self-contained reader (fresh same-session code — GENIND-BOX-6's seam), consuming the suppliers ONLY as md5 pins + the committed hex3 JSON tie”, §S10 lines 1614–1616, shard 2). Under template rule 19 this is an `instrument-record`, distinct from the §S10 `preregistration` and the §S11 `run-record` that shard 2 homes.

**DERIVATION:** Not a mathematical unit. **PIN VERIFICATION (rule 23):** `verification/openmath/genind_checks.py` EXISTS on disk ✓; the seal commit `c3212cc` ✓; the runner md5 `e7ca150b` is the note's own repeatedly re-verified pin (§S12/§S13/§S14/§S15/§S16). The named artifacts `genind_checks_output.txt` and `genind_checks_results.json` both EXIST ✓.

**RESOLUTION TRACE:** statement lines 51–63. correction sites: none — no later round edits the instrument description; §S12–§S16 each re-assert its byte-freeze instead.

**TEETH:** self-referential (this unit IS the instrument). Its four teeth GT-T-ALPHA / GT-T-CS / GT-T-CRIT / GT-T-BRACKET are preregistered at §S10 and scored at §S11 (both shard 2); the “≥ 3 teeth” claim of this display is satisfied at 4.

---

### EFF.GENIND.s1of3.03  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (division-of-labor disclosure). verbatim, lines 63–68.

> “**Division of labor (disclosed):** the
> parallel scout QSCOUT22 (@ 240a56c, skeleton) owns the INSIDE of the
> quartic (2,2) composite stage (genres E/F, the four-slot model, the
> level-2 empirical table); this unit owns the induction, the
> opening-level laws, and the criterion — the two units' machine legs
> are disjoint by design.”

**CONDITIONALITY:** The pin `240a56c` is a **skeleton** pin, superseded by §S9.3's `[r6]` dated append (lines 1527–1534, shard 2): “**NEW PIN = verdict dd67cda + annex fcaf268.** Consumption verdict trivially SURVIVES — S16 table row 5: nothing was or is consumed”. So the division-of-labor statement stands; only the pin moves.

**SUPERSESSION KIND:** (received) `as-of scoping` — the r6 append re-dates the pin without altering the disclosure.

**DERIVATION:** Not a mathematical unit. **PIN VERIFICATION:** `240a56c` ✓ commit. Target note `lean/notes/openmath/QSCOUT22_2026-08-08.md` EXISTS ✓.

**RESOLUTION TRACE:** statement lines 63–68. correction sites: 1525–1534 (§S9.3 QSCOUT22 bullet, shard 2).

**TEETH:** NONE — a disclosure. Its factual content (machine-leg disjointness) is corroborated only by the two rosters' non-overlap, not by any tooth.

XREF: `lean/notes/openmath/QSCOUT22_2026-08-08.md:GENRE E` — count **2**.
XREF: `lean/notes/openmath/QSCOUT22_2026-08-08.md:GENRE F` — count **1**.

---

### EFF.GENIND.s1of3.04  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph. verbatim, lines 70–87.

> “**What GENIND is (one breath).** THEOREM W-12.D (PROVED, an
> unconditional reduction) turns {(A0) lift well-posedness + (A1) exact
> disjoint q-uniform core menu + (A2) drainage} at degree n into ONE
> R_τ ∈ ℚ(q) per splitting type at every prime power, both
> characteristics, wild included. At n = 2 it fires on W-11; at n = 3 on
> HEX3 + HMENU3. The n = 3 proof had a SHAPE — LEMMA HM3-1's two-species
> chain classification (α self-similar + β re-entry into lower degree),
> the α-bracket telescoping, the β raw-key dictionary — and this unit
> composes that shape AS the induction on n it visibly is: the package
> (hMenu-k)+(hExhaust-k) for all k < n, in history-resolved form, is
> exactly what a degree-n history consumes at every β-fracture, and the
> only genuinely new ingredient at each n is the PER-STAGE
> CLASSIFICATION of refine events — which is complete order-1 knowledge
> (PROVED, from W-12.A's depth-0 completeness) except at COMPOSITE
> stages, which exist precisely when some stage carries ≥ 4 keys (first
> instance: the quartic (2,2)). So the distance from the n = 3 theorem
> to the FULL uniformity theorem is exactly ONE displayed hypothesis
> family — the composite-stage law [GENIND-H] — plus hostile arcs.”

**CONDITIONALITY:** This is the note's own orientation claim and it is **load-bearing for the DAG**: the last sentence (“the distance … is exactly ONE displayed hypothesis family”) is the headline the downstream chapter cut will quote. It is true only under the note's own grade split — GENIND.B is a REDUCTION, not a theorem (`.16`, and GENIND-BOX-1 at lines 1351–1356, shard 2: “THEOREM GENIND.B is a REDUCTION; its unconditional content at n ≥ 4 is exactly the simple-stage layer (GENIND.C) + the criterion + the opening-mass laws”). It is further **widened at n ≥ 8** by the dated supplier-movement record (lines 3081–3084, shard 3): the conditionality there is “**[GENIND-H(n)] + [GENHN-HE(μ ≥ 3)] + [GENHN-TOW-1]**”, i.e. **three** hypothesis families, not one, above degree 7.

**SUPERSESSION KIND:** (received) `scope-pin` — the n ≥ 8 conditionality record does not replace this sentence's wording; it pins the range in which “exactly ONE” is the whole story to n ≤ 7.

**DERIVATION:** Not a proof; the claim is discharged by §S6 (the reduction, `.54`–`.61`) and §S5.1 (the criterion, `.11`/`.43`).

**RESOLUTION TRACE:** statement lines 70–87. proof lines 983–1113 (§S6) + 847–887 (§S5.1). correction sites: 3076–3088 (the conditionality-movement paragraph, shard 3).

**TEETH:** Indirect — guarded only through the composite corroboration of §S11's GT-CRIT (zero CS events at n = 3; CS exactly at the predicted genres at n = 4, 5), which is the criterion half of the claim.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:THEOREM W-12.D` — count **5**.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:THEOREM W-12.A` — count **8**.
XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:HM3-1` — count **4**.

---

### EFF.GENIND.s1of3.05  [scope-record]

**CANONICAL STATEMENT:** FORM: bulleted display under a §-heading. verbatim, lines 91–110 (§S0's positive-import list).

> “## S0. RECONCILIATION (what the suppliers proved; what this unit adds)
>
> * **W-12.D** (@ r2 HEAD 99f1813): the reduction. Its per-degree
>   hypothesis package {(A0), (A1), (A2)} is what (hMenu-n)+(hExhaust-n)
>   abbreviate throughout.
> * **W-12.A** (same pin): the order-1 decided-shape count law AT EVERY
>   DEGREE — the leaves of the induction, already unconditional.
> * **W12-L0 / HM3.A** (pins below): the HISTORY-RESOLVED menus at
>   n = 2, 3 — the form the induction's β-consumption needs (aggregate
>   menus do not suffice: β-children enter at their own refine loci,
>   HM3's β3).
> * **HEX3 H-1..H-4 + HM3-1..HM3-4**: the n = 3 instances of every
>   scaffold lemma below; each general lemma names its instance.
> * **The carry corpus** (J-D0, GRTJC W-6..W-9, WELDMASTER, DULEMMA,
>   [W12-H]): consumed ONLY at the composite-stage frontier (S7), where
>   it is the counting engine — J-D0 (shape-only counts), W-9
>   (dim_K 𝒜(T) = E: the stage slot lattice), JC-LOAD/W-8
>   (no-cancellation), (H-e) (order-≥2 σ-decision).
> * **QSCOUT22** (@ 240a56c): the (2,2) empirical instrument; S7's
>   predictions are keyed to its table, not re-measured here.”

**CONDITIONALITY:** Every pin in this list is **superseded** by §S9.3's `[r6]` SUPPLIER RE-PIN ROUND (lines 1464–1599, shard 2) and its per-supplier fired-clause table (§S16, lines 2352–2361, shard 2). The W-12 pin in particular moves **r2 99f1813 → r5 be4a1dc/ee17210**, crossing a repaired **CRITICAL** in W-12 §S3.2; the consumption verdict is recorded SURVIVES with its evidence (“zero S3.2 cites in this note”, itself re-worded by PE7-m1 to “zero S3.2 cites outside this round's own disclosure sentences (grep: 4 string hits, all four disclosure)”, lines 2479–2487, shard 2). The carry-corpus bullet's fence (“consumed ONLY at the composite-stage frontier (S7)”) is re-asserted at §S9.3 (“No count law of S2–S6 consumes them”, line 1522, shard 2) and is a NON-IMPORT (§4).

**SUPERSESSION KIND:** (received) `as-of scoping` for every pin (the pins are re-dated, the supply claims are not re-worded).

**DERIVATION:** Not a mathematical unit; a supplier inventory.

**RESOLUTION TRACE:** statement lines 91–110. correction sites: 1464–1599 (§S9.3 stack, shard 2), 2352–2371 (§S16 table + the four unmoved pins, shard 2), 2479–2498 (PE7-m1/PE7-m2, shard 2), 3032–3094 (the GENHN supplier-movement record, shard 3).

**TEETH:** GT-PIN [NONE] — 5 md5 pins (w11/w12/hex3/hmenu3 runners + the hex3 results JSON), scored 0/5 at §S11 P-1, re-verified 5/5 at §S16. This guards the *artifact* pins, not the *note* pins; the note pins are git-log-checked, not tooth-guarded.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:W12-L0` — count **32**.
XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:HM3.A` — count **18**.
XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:H-2` — count **11**; `H-3` — count **5**; `H-4` — count **2**.
XREF: `lean/notes/openmath/JD0_PROOF_2026-08-08.md:LEMMA J-D0` — count **4**.
XREF: `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md:W-6` — count **18**; `W-8` — count **35**; `W-9` — count **13**; `JC-LOAD` — count **31**; `dim_K 𝒜(T) = E` — count **3**.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:[W12-H]` — count **17**.
XREF: `lean/notes/openmath/WELDMASTER_2026-08-08.md` EXISTS ✓; `lean/notes/openmath/DULEMMA_PROOF_2026-08-08.md` EXISTS ✓.
**NEAR-MISS (rule 15):** `HEX3 H-1` — designation absent as written (fixed-string count **0** in `HEX3_PROOF_2026-08-08.md`); verified referent at `HEX3_PROOF_2026-08-08.md:188` under the actual string `## S2. THE DEPTH-0 PARTITION (LEMMA H-1)`, and at `:723` under “**This note's own lemmas** H-1..H-4”; fixed-string `H-1` count **5**. The prefix “HEX3 ” is GENIND's own qualifier, not part of the supplier's designation.

---

### EFF.GENIND.s1of3.06  [fence]

**CANONICAL STATEMENT:** FORM: inline sentence. verbatim, line 112.

> “This note edits no supplier note. Proposed annex texts: §S9.”

**CONDITIONALITY:** Unconditional and **never contradicted**: §S9.1's heading repeats it (“text offered; W12_PROOF not edited”, line 1429, shard 2), and every later round re-asserts that no supplier artifact was touched. This is header predicate B's governing quote (the NO-APPENDS declaration, rule 17).

**DERIVATION:** Not a mathematical unit; a protocol declaration.

**RESOLUTION TRACE:** statement line 112. correction sites: none. Re-assertions at 1429 and at every §S12–§S16 byte-freeze paragraph (shard 2).

**TEETH:** NONE — a protocol fence, outside the orphan count.

---
### EFF.GENIND.s1of3.07  [definition]

**CANONICAL STATEMENT:** FORM: unheaded prose paragraph opening §S1. verbatim, lines 116–125.

> “Conventions as W-12 §S1 (O a complete DVR, residue field F_q, either
> characteristic; window N ≥ 2; the recursive OM-convention conservative
> read: v(current a₀) ≥ N ⟹ UNDECIDED exit, no tail certification).
> A CLUSTER SYSTEM (m, d, N): fix a monic irreducible P̄ of degree d
> over F_q and the read's monic lift Φ; states = monic degree-md f over
> O/π^N with f̄ = P̄^m, coordinatized by the Φ-adic development
> f = Φ^m + Σ_{j<m} a_j Φ^j, a_j ∈ (O/π^N)[x]_{<d} with ā_j = 0
> (W-12 S2.2's bijection); q^{dm(N−1)} states; Q := q^d. The full-space
> degree-n problem reduces to cluster systems by the level-0 Hensel
> product (W12-S2.1). Write c(m) := m(m−1)/2.”

**CONDITIONALITY:** **The stated window bound `N ≥ 2` is EXTENDED to `N = 1` by ANNEX R R3** (lines 2865–2889, shard 3), which was filed as a CONFIRMED GAP (a scope leak: the note's own transports invoke the system at window 1). R3's rider, verbatim:

> “**R3.1 The convention rider.** Extend S1's cluster-system
> conventions and the P-package reading to **window N = 1**, whose
> content is FORCED by S1's own definitions read at N = 1:
> * states: a_j ∈ (O/π¹)[x]_{<d} with ā_j = 0 forces every a_j = 0 —
>   exactly q^{dm(N−1)} = q⁰ = 1 state;
> * read: a₀ = 0 gives v(a₀) ≥ 1 = N, so the conservative read exits
>   UNDECIDED before consulting any digit — DRAIN;
>   u_{m,d}(1) = total = 1;
> * grammar coherence: DRAIN's locus law q^{d(m−1)(N−1)} = 1 = the
>   whole space; α needs mk ≤ N−1 = 0 (none); DEC/β/CS need a polygon,
>   i.e. v(a₀) < N (none) — of the five events exactly one is
>   inhabited;
> * the window-1 package: menu = {DRAIN} (exact; (A1)-admissible with
>   count 1 = q⁰), (A0) vacuous (no decided leaves), complement
>   u = total exactly.”

R3 also fixes the scope of the extension, enumeratively: “window-1 systems arise in this note only as TRANSPORT TARGETS (S1's ambient window stays ≥ 2)”, with three named sites — GENIND-2(a)'s α(k) endpoint mk = N−1 (`.21`), GENIND-3/GENIND-6 child extractions at M_l = 1 (`.24`, `.34`, `.38`), and the S5.2 recursion boundary u(1) = 1 (`.45`).

**SUPERSESSION KIND:** `inventory completion` — the convention's five-event grammar is not re-worded; the missing boundary member of its own definition is supplied and its three consumption sites enumerated.

**TARGETS:** `s1of3.07` (this unit), `s1of3.21`, `s1of3.24`, `s1of3.34`, `s1of3.38`, `s1of3.45`.

**DERIVATION:** Definitional. The state count `q^{dm(N−1)}` is W-12 S2.2's bijection, cited not re-proved; the level-0 reduction is W12-S2.1, cited not re-proved.

**RESOLUTION TRACE:** statement lines 116–125. proof lines — none (definitional). correction sites: 2854–2895 (ANNEX R R3, shard 3), with its verification leg at 2891–2895.

**TEETH:** R3.2's machine leg I (`genind_annexr_supp.py` @ f5271e4, GREEN): “(m, Q) ∈ {2, 3, 4} × {2, 3, 4} — 1 state, v(a₀) ≥ 1 = N, DRAIN, u(1) = total = 1”, plus a decorrelated leg (“Codex's sympy re-solve of the S5.2 recursion under exactly this boundary (m = 2 closed forms exact at N = 2..12)”) — disposition `accepted-with-decorrelation-supplied`.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:S2.2` — count **19**.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:W12-S2.1` — count **9**.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:S1` — count **24** (an upper bound: the string matches §-anchors and prose alike).

**PIN VERIFICATION:** `f5271e4` ✓ commit; `verification/openmath/genind_annexr_supp.py` EXISTS ✓; `verification/openmath/genind_annexr_supp_output.txt` EXISTS ✓.

---

### EFF.GENIND.s1of3.08  [theorem]

**CANONICAL STATEMENT:** FORM: display (blockquote, clause (I) of THEOREM GENIND.A). verbatim, lines 127–146.

> “**THEOREM GENIND.A (candidate: the general two-species recursion).**
> For every prime power q, both characteristics, every cluster system
> (m, d, N) with m ≥ 2:
>
> **(I) [the event grammar]** Every state is EXACTLY ONE of:
>   * **DRAIN**: v(a₀) ≥ N (conservative exit); locus q^{d(m−1)(N−1)}.
>   * **DEC**: all residuals separable — an order-1 decided shape;
>     locus = THEOREM W-12.A's law; σ by Ore.
>   * **α(k)**, 1 ≤ k, mk ≤ N−1: one side (0, mk)–(m, 0), integer
>     slope k, residual (y−z)^m, z ∈ F_Q^×; locus
>     (Q−1)·Q^{m(N−1) − k·m(m+1)/2}.
>   * **β**: at least one repeated residual factor, every repeated
>     factor linear with e = 1, and not α: the cluster FRACTURES into
>     child clusters (μ_l, d) at their sides' slopes — the partition
>     datum {μ_l} ∪ {decided piece degrees}, a nontrivial partition of
>     m — plus decided pieces.
>   * **CS** (composite opening): some repeated residual factor
>     (ψ, μ) with μ ≥ 2 and e·deg ψ ≥ 2 — the read exits the order-1
>     calculus into a degree-(e·d·deg ψ) key stage ([W12-H]).”

**CONDITIONALITY:** PROVED at order 1, both characteristics (the GRADE box, `.12`). The word “candidate” in the theorem's title is scoped by that GRADE box to clause (III) only. The five-event grammar is **completed at window 1** by ANNEX R R3's third bullet (“of the five events exactly one is inhabited”, `.07`) — a boundary case the display's `mk ≤ N−1`/`v(a₀) < N` side conditions already imply but do not display.

**DERIVATION:** The proof is LEMMA GENIND-1(i) (`.17`), whose statement re-displays the α-locus law and whose proof paragraph (i) derives exhaustiveness from the deterministic read + W-12 §S1's `[r1 F3]`-corrected refine taxonomy. This unit and `.17`(i) are the same mathematical content at two granularities (the §S1 forward display and the §S2 lemma); the relation is recorded at both.

**RESOLUTION TRACE:** statement lines 127–146. proof lines 231–234 + 245–264 (LEMMA GENIND-1(i) and its proof paragraph (i)). correction sites: 2873–2876 (R3's grammar-coherence bullet, shard 3).

**TEETH:** GT-PART [SAME] (partition exact on every row; §S11 P-2 “0/33”, with Zp/F_q[[t]] depth-0 tallies IDENTICAL at all 11 shared (m, q, N)) · GT-DEPTH0 [SAME, both directions] (§S11 P-3 “0/108 both directions”) · GT-CRIT (§S11 P-8 “0/22”: the CS clause's side conditions μ ≥ 2, e·γ ≥ 2, 4 ≤ e·μ·γ ≤ m_frame checked at every CS event, all depths). All three are executable regressions on the sealed roster; rows inventoried in shard 2.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:THEOREM W-12.A` — count **8**.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:[W12-H]` — count **17**.

---

### EFF.GENIND.s1of3.09  [theorem]

**CANONICAL STATEMENT:** FORM: display (blockquote, clause (II) of THEOREM GENIND.A) with an indented ASCII display inside. verbatim, lines 148–159.

> “> **(II) [α-transport + THE GENERAL BRACKET]** α(k) recenters
> bijectively onto the node D_k ≅ (ghost fiber Q^{k·c(m)}) × (the SAME
> (m, d) system at window N − mk), key-sheared; the α-prefix histories
> aggregate with the bracket
>
>     b_{m,d}(μ) = (Q−1) · Q^{(c(m)+1)·μ − 1}   (μ ≥ 1; b(0) = 1;
>     WINDOW CONDITION mμ ≤ N−1 [r1, PE1-M1] — the per-step
>     admissibilities m·k_i ≤ (current window) − 1 conjoin along the
>     chain to exactly this, so the unrestricted composition sum is
>     the realized-history aggregate precisely for mμ ≤ N−1),
>
> exponent coefficient c(m)+1 = m(m−1)/2 + 1 (= 2, 4, 7, 11 at
> m = 2, 3, 4, 5): the n-dependence of HM3-4's (q−1)q^{4μ−1}.”

*(The leading `> ` inside the first line is the source's own blockquote marker, reproduced.)*

**CONDITIONALITY:** PROVED (GRADE box `.12`). The `[r1, PE1-M1]` window condition is **already-landed base text** (resolution rule 2), not a pending correction: without it the bracket is the unconditional generating-function identity and only the realized-history reading needs `mμ ≤ N−1`. The `N − mk = 1` endpoint of the transport is supplied by ANNEX R R3 (`.07`).

**SUPERSESSION KIND:** (internal, already landed) `scope-pin` — `[r1, PE1-M1]` pins the aggregate's validity range without touching the identity.

**DERIVATION:** LEMMA GENIND-2(a) + (b) (`.21`, `.22`) with their proofs; the exponent instances are `.23`.

**RESOLUTION TRACE:** statement lines 148–159. proof lines 290–332 (LEMMA GENIND-2 statement + proof). correction sites: `[r1, PE1-M1]` in situ at 153–156 (landed); 2882–2884 (R3's site (a), shard 3).

**TEETH:** GT-BRACKETID [SYM] — “LEMMA GENIND-2(b) at m ∈ {2,3,4,5}, μ ∈ {1,2,3}, q ∈ {2,3}”, §S11 P-7 “24/24 … integer-exact … (exponent coefficients 2/4/7/11)”, with tooth GT-T-BRACKET firing at its preregistered count 24. Executable regression (symbolic identity check).

XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:HM3-4` — count **11**.

---

### EFF.GENIND.s1of3.10  [theorem]

**CANONICAL STATEMENT:** FORM: display (blockquote, clause (III) of THEOREM GENIND.A). verbatim, lines 161–165.

> “**(III) [β-transport]** each β-genre fibers, route-explicitly, over
> the PRODUCT of its child systems (μ_l, d) at explicitly shifted
> windows and entry loci, with q-power fibers and letter censuses —
> children evolve independently (fracture permanence) and consume the
> lower-degree history-resolved menus.”

**CONDITIONALITY:** **The weakest of GENIND.A's four clauses, and the note says so.** The GRADE box (`.12`) grades it “proved as the displayed schema with the n = 3 routes as consumed instances and the n = 4, 5 instances machine-checked pointwise — the general per-route ledger is compressed exactly as HEX3-BOX-2 priced its own”. Its honest residue is `.26` (the GENIND-3 honesty note) and GENIND-BOX-2 (lines 1357–1360, shard 2). The clause's *window* content was DEFECTIVE as sealed and was corrected at `[r3]`/`[r4]` — see `.24`, `.27`, `.28`; the clause as displayed here says only “explicitly shifted windows”, which survives the correction unchanged.

**DERIVATION:** LEMMA GENIND-3 (`.24`) with its three-step schema proof; the mixed (CS + β-child) extension is LEMMA GENIND-6 (`.34`–`.37`).

**RESOLUTION TRACE:** statement lines 161–165. proof lines 346–443 (LEMMA GENIND-3 statement + proof). correction sites: 355–369 and 380–425 (the `[r3]`/`[r4]`/`[r5]` in-place window and reduction corrections, landed); 2779–2852 (ANNEX R R2's unit-pivot rider on the fibration's onto/constant-fiber step, shard 3).

**TEETH:** GT-BETA [SAME] — “pointwise Hensel reconstruction”; §S11 P-6 “0/87,156 Hensel reconstructions coefficient-exact”. Executable regression, pointwise, member by member. Disposition note: this is the *compensating instrument* the note itself names for the compressed ledger (GENIND-BOX-2: “The n = 4, 5 pointwise machine families are the compensating instrument”), i.e. `accepted-with-decorrelation-supplied` at n ≤ 5 and unguarded above it.

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:HEX3-BOX-2` — count **4**.

---

### EFF.GENIND.s1of3.11  [theorem]

**CANONICAL STATEMENT:** FORM: display (blockquote, clause (IV) of THEOREM GENIND.A). verbatim, lines 167–177.

> “**(IV) [THE COMPOSITE-STAGE CRITERION]** a CS event at a stage with
> m keys requires a side of abscissa length e·μ·deg ψ ≥ 4, hence
> m ≥ 4; conversely m ≥ 4 realizes CS with positive locus at every q.
> Therefore: composite stages occur at degree n IFF n ≥ 4 (realized
> already at d = 1); n = 2, 3 are composite-free (the PE2-verified
> fact, now a theorem); n = 5 is NOT composite-free despite being
> prime — the criterion is "some stage carries ≥ 4 keys", NOT a
> factorization property of n. First instances at n = 4: the e-first
> genre QRT-G2(h; (1²)) (locus (q−1)q^{4N−5h−3} per center) and the
> f-first genre FULL(k)-(2²) (locus (Q(Q−1)/2)·q^{4N−10k−4},
> Q = q here); at n = 5 the embedded genres of S5.3.”

**CONDITIONALITY:** **TWO independent riders from ANNEX R land on this display, on two different clauses.**

*(a) The converse clause is scoped to DEGREE level.* ANNEX R R5 (lines 2936–2955, shard 3), curing CODEX F6:

> “**R5.1 The rider.** Read GENIND.A(IV)'s converse clause
> ("conversely m ≥ 4 realizes CS with positive locus at every q") at
> DEGREE level: **every degree n ≥ 4 realizes a CS event with
> positive locus at every q, both characteristics** — which is what
> S5.1's sufficiency proof delivers … The
> STAGE-level parse — for each m ≥ 4, an m-KEY stage itself opening a
> CS event with positive locus — is NOT claimed by this note.
> Displayed stage-level instances exist at m = 4 (the QRT genres are
> the 4-key system's own), m = 5 (S5.3's embedded genres), and m = 6
> (S4.3's M6/SS6, machine-realized); at general m the stage-level
> statement is left unclaimed (the adjudication marks it likely true
> via general-m embedded genres, not shown).”

*(b) The f-first first-instance law is missing its visibility floor.* ANNEX R R4 (lines 2906–2915, shard 3), curing CODEX F5:

> “**R4.1 The erratum, floor re-derived.** Read BOTH displays — S5.3's
> CS4-F(k) entry and GENIND.A(IV)'s first-instances clause ("the
> f-first genre FULL(k)-(2²)…") — WITH the floor: **CS4-F(k) has
> VISIBILITY FLOOR 4k ≤ N−1.** Derivation (the same one PE1-M3 ran
> for the E-sibling's 2h ≤ N−1): the genre's heights are
> (4k, 3k, 2k, k) (S5.3's own display), so v(a₀) = 4k on the locus;
> the keying fires DRAIN first at v(a₀) ≥ N (GENIND.A(I)), so the
> genre is inhabited iff 4k ≤ N−1. At (q, N, k) = (2, 2, 1) the
> unfloored display returns (2·1/2)·2^{8−10−4} = 2^{−6} — a
> NON-INTEGER against a true locus of 0.”

The e-first sibling's floor `2h ≤ N−1` is already carried in range at `.48` via `[r1, PE1-M3]`; this display carries neither floor, so R4 is the only source of the f-first one.

**SUPERSESSION KIND:** R5 = `scope-pin` (the converse's quantifier is pinned to degrees, not stages; no wording is replaced). R4 = `wording-rider` (“Read BOTH displays … WITH the floor”, an explicit substitution on the displayed law). **The two are NOT interchangeable and must not be merged**: R5 narrows what is claimed, R4 adds a missing side condition to what is displayed.

**TARGETS:** R4 targets `s1of3.11` and `s1of3.49`; R5 targets `s1of3.11` only.

**DERIVATION:** §S5.1's *Necessity* and *Sufficiency* paragraphs, lines 849–877, verbatim:

> “*Necessity.* A CS event is a repeated residual factor (ψ, μ) with
> μ ≥ 2 and e·deg ψ ≥ 2 on a side of the stage polygon. The side's
> abscissa length is e·g with g ≥ μ·deg ψ, so length ≥ e·μ·deg ψ ≥
> 2·2·1 = 4 (case e ≥ 2, ψ linear) or ≥ 1·2·2 = 4 (case e = 1,
> deg ψ ≥ 2) — in every case ≥ 4. The polygon of a stage with m keys
> spans abscissas [0, m]: m ≥ 4. A stage with m keys of degree D inside
> a degree-n read has mD ≤ n, so n ≥ 4D ≥ 4. Refinements only shrink or
> preserve multiplicities (α preserves m; β-children have μ_l < m;
> composite children have m′ = μ ≤ m/(e·deg ψ) ≤ m/2), so ALL stages of
> a degree-≤3 read have m ≤ 3: n = 2, 3 are composite-free — the
> ledger's PE2-verified observation, now a theorem, and the reason the
> n ≤ 3 program never consulted [W12-H].
>
> *Sufficiency (realization at every n ≥ 4, every q, both
> characteristics).* At d = 1, m = 4: the QRT-G2(h; (1²)) stratum
> exists with positive locus (q−1)q^{4N−5h−3} > 0 at every window with
> 2h ≤ N−1 [r1, PE1-M3] (W-12 S2.5, PROVED); at n > 4 pad with ONE
> monic irreducible of degree n−4 at level 0 (Hensel product,
> W12-S2.1): it is coprime to the linear center automatically (at
> n−4 = 1 take any of the q−1 other monic linears; at n−4 ≥ 2 an
> irreducible of that degree exists over every F_q and shares no root
> with the center), and the padding block is separable at level 0,
> hence a decided piece — the degree-n state opens the same CS stage
> with positive locus **[r1, PE1-M2: the sealed text's "n−4 distinct
> simple roots" padding is impossible over F_2 for n ≥ 6 (only two
> monic linears exist and the cluster's center takes one); the
> single-irreducible padding delivers the same Hensel-product
> realization]** — or realize the embedded genres of S5.3 inside the
> full cluster. ∎”

Justification tags: necessity — `computation` (side-length arithmetic, two exhaustive cases) + `by XREF W-12 S1`'s refine taxonomy (through GENIND-1(i)) + `computation` (the refinement-monotonicity induction). Sufficiency — `by XREF W-12 S2.5` (the QRT-G2 law, PROVED at the w12 seal) + `by XREF W12-S2.1` (Hensel product) + `computation` (existence of a monic irreducible of every degree over every F_q). The `[r1, PE1-M2]` bracket is a landed repair of the padding construction, not an open item.

**RESOLUTION TRACE:** statement lines 167–177. proof lines 849–877 (§S5.1). correction sites: `[r1, PE1-M2]`/`[r1, PE1-M3]` in situ at 865 and 872–876 (landed); 2897–2925 (ANNEX R R4, shard 3); 2927–2959 (ANNEX R R5, shard 3).

**TEETH:** GT-CRIT [SAME], both directions — §S11 P-8 “✓ GT-CRIT 0/22 — ZERO CS events on all four n = 3 control rows (the criterion's negative half); every n = 4/5 CS event (all depths) obeys μ ≥ 2, e·γ ≥ 2, 4 ≤ e·μ·γ ≤ m_frame; no genre outside the S5.3 grammar”, with tooth GT-T-CRIT firing at its preregistered count 4. Executable regression + planted grammar-acceptance mutant. **Disclosed limit:** the sufficiency half is machine-realized only at n = 4, 5 (and, off-roster, at n = 6 via M6/SS6); at general n it rests on the padding construction, which no tooth exercises.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:QRT-G2` — count **10**.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:S2.5` — count **9**.

---

### EFF.GENIND.s1of3.12  [scope-record]

**CANONICAL STATEMENT:** FORM: bold display (the GRADE box closing THEOREM GENIND.A). verbatim, lines 179–184.

> “**GRADE: (I), (II), (IV) PROVED below (S2–S5) at order 1, both
> characteristics; (III) proved as the displayed schema with the
> n = 3 routes as consumed instances and the n = 4, 5 instances
> machine-checked pointwise — the general per-route ledger is
> compressed exactly as HEX3-BOX-2 priced its own. Machine-sealed on
> the S10 roster.**”

**CONDITIONALITY:** This is the grade of record for `.08`–`.11`. It is not superseded; it is *narrowed twice* from outside the range — R5 narrows (IV)'s converse to degree level (`.11`), and the C2-G1 certification-status paragraph (lines 3712, shard 3) records that the general (CS-1)/GENIND-6(a)/GENHN references “do not establish (CS-1Q.b) for every embedded or mixed genre”, which touches the (III)-adjacent mixed transport rather than (III) itself. “Machine-sealed on the S10 roster” is an as-of claim against the sealed battery (`.02`).

**DERIVATION:** Not a mathematical unit; a grade declaration whose four sub-claims are `.08`–`.11`.

**RESOLUTION TRACE:** statement lines 179–184. correction sites: 2936–2955 (R5, shard 3); 3712 (the C2-G1 certification-status paragraph, shard 3).

**TEETH:** PROOF-ONLY for clause (III)'s general-degree half — the note's own coverage-hole sentence is `.26`'s “What is NOT written here: the closed-form fiber exponent of every genre at every degree”. Clauses (I)/(II)/(IV) are toothed as at `.08`/`.09`/`.11`.

---

### EFF.GENIND.s1of3.13  [theorem]

**CANONICAL STATEMENT:** FORM: display (blockquote, THEOREM GENIND.B's hypothesis block). verbatim, lines 186–196 (the (CS-EXACT) insertion that physically continues the display is emitted separately at `.14`; the two pieces are byte-verbatim and their union is the whole hypothesis block minus nothing).

> “**THEOREM GENIND.B (the induction; conditional structure displayed
> the montes_unconditional way).** Fix n ≥ 2. Define the package
> P(k) := {history-resolved exact menu (HM3.A-form) + finite
> (A1)-admissible aggregate menu + (A0) + exact-complement (A2)} for
> the degree-k problem. ASSUME:
>   (IH) P(k) for all 2 ≤ k < n;
>   [GENIND-H(n)] for every composite-stage genre realizable at
>   degree ≤ n: (CS-1) the stage transport (the stage system is
>   count-fibred over an explicit lower-complexity system), (CS-2) the
>   stage bracket (the stage's own refine aggregation), (CS-3) the
>   order-≥2 σ-decision theorem ((H-e), = (A0) at the stage's leaves),”

**CONDITIONALITY:** **P(k)'s fourth member is superseded by ANNEX R R1's species pin** (lines 2641–2661, shard 3), which was the heaviest CONFIRMED GAP of the Codex ratification (F3: the vanishing rate consumed but not supplied by the displayed P(k)). R1's rider, verbatim:

> “**The species pin (the fourth member's rider).** Read P(k)'s fourth
> member "exact-complement (A2)" WITH the species the proved instances
> exhibit — for each consumed cluster system (μ, d) at window M:
>
> > **(A2-RATE)** the conservative complement u_{μ,d}(M) is an exact
> > finite sum of signed q-power terms whose term count and
> > coefficients are polynomially bounded in M; in particular there
> > are constants (K, B, c) depending on (μ, d) only with
> >
> >     u_{μ,d}(M) / Q^{μ(M−1)} ≤ K·M^B·Q^{−(M−c)}.”

R1 adds, of the closure this creates: “This is a strengthening of the DISPLAY, not of the truth: the m = 2 and n = 3 members already sit in the species at their proved pins, and the induction below PROPAGATES the rate clause, so the package that closes under GENIND.B's strong induction is P(k)-with-(A2-RATE).” **That closure sentence is itself riddered** by `[ar1 2026-08-10, GAP-1 repair]` (lines 2662–2675, shard 3): as sealed it “exceeded its displayed support”, and the split now reads “simple part by GENIND.C′ unconditionally; CS-drain part by GENIND-C2 given (CS-1)”. **And the GENIND-C2 leg is itself re-conditioned** by the 2026-08-12 round-2 correction (line 3712, shard 3): “‘conditional on (CS-1) only’ must be replaced by ‘conditional on (CS-1Q), verified per genre.’”

**SUPERSESSION KIND:** R1's fourth-member rider = `inventory completion` (a consumed hypothesis component absent from the display is supplied; nothing is re-worded). The `[ar1]` closure repair = `scope-pin`. The 2026-08-12 upgrade = `replacement` (the conditionality label “(CS-1) only” is replaced by “(CS-1Q), verified per genre”).

**CHAIN:** sealed P(k) fourth member “exact-complement (A2)” → **R1's (A2-RATE) species pin** → `[ar1]` GAP-1 split (simple part / CS-drain part) → 2026-08-12 GENIND-C2 replacement (Q = q^d retained through the height sum) → **2026-08-12 round-2 C2-G1: the CS-drain leg is conditional on (CS-1Q), verified per genre — TERMINAL.** A chapter cut must read the TERMINAL member: P(k)'s fourth member carries (A2-RATE), whose CS-drain half rides an explicitly *per-genre unverified* clause family.

**TARGETS:** `s1of3.13` (this unit), `s1of3.45`, `s1of3.46`, `s1of3.57`.

**DERIVATION:** §S6 Steps 1–5 (`.54`–`.60`); the conditionality geography is `.61`.

**RESOLUTION TRACE:** statement lines 186–196. proof lines 985–1106 (§S6). correction sites: 2580–2777 (ANNEX R R1, shard 3), 3117–3226 (ANNEX R — r1's GENIND-C2, shard 3), 3298–3588 and 3592–3872 (the two 2026-08-12 dated corrections, shard 3), 3076–3088 (the n ≥ 8 conditionality movement, shard 3).

**TEETH:** NONE directly — GENIND.B is a reduction, and no battery row certifies a reduction. Its *components* are toothed (`.08`–`.11`, `.44`–`.46`); its consequence is scored only through §S11's “Consequence for the grade box” paragraph. This is a **PROOF-ONLY** unit in the sense of rule 16; the note's own coverage sentence is GENIND-BOX-1 (lines 1351–1356, shard 2): “THEOREM GENIND.B is a REDUCTION; its unconditional content at n ≥ 4 is exactly the simple-stage layer (GENIND.C) + the criterion + the opening-mass laws.”

XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:HM3.A` — count **18**.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:[W12-H]` — count **17** (the `(H-e)` cite rides inside it).

---

### EFF.GENIND.s1of3.14  [hypothesis]

**CANONICAL STATEMENT:** FORM: bracketed rider inside the THEOREM GENIND.B display (the `[r1, PE1-G1]` insertion, with a nested `[r2, PE2-m1]` granularity correction). verbatim, lines 197–214.

> “  **[r1, PE1-G1: and (CS-EXACT) the EXACTNESS clause — the stage
>   menu and stage drain that (CS-1)+(CS-2) deliver are EXACT: one
>   exact closed form per stratum, a FINITE SUM of q-powers [r2,
>   PE2-m1: not always a single q-power — GENH4.B's genre-F law at
>   even N is a TWO-term sum (the CAP(F) boundary band), so the r1
>   gloss "one closed-form q-power family per stratum" was satisfiable
>   only at a finer granularity than the stratum it names; Step 4's
>   inclusion–exclusion consumes exact finite closed forms, which
>   finite q-power sums are], not asymptotic bounds.
>   This clause is load-bearing, not decorative: P(n)'s fourth member
>   is the exact-COMPLEMENT (A2), and the induction CONSUMES it at
>   higher degrees — S5.2's drainage bullet runs inclusion–exclusion
>   over the child systems' u's, an identity only if those u's are
>   exact — so without (CS-EXACT) the antecedent would admit bound-
>   only stage laws under which P(n)'s fourth member fails while
>   (CS-1)(CS-2)(CS-3) hold, and the strong induction would not close
>   on that member. See Step 4's [r1] record for the consumption path
>   and the discharge geography.]**”

**CONDITIONALITY:** OPEN at general n — a hypothesis on the box, de facto discharged at n = 4 only (`.66`). Its stated *rationale* (the second half of the bracket) is riddered by ANNEX R R6.2 (lines 2986–2997, shard 3), which separates two different consumers that the sealed rationale ran together:

> “The rider: **(CS-EXACT) is required because the induction propagates
> the exact-complement IDENTITY (P's fourth member — the
> inclusion–exclusion as an equality), NOT because bounds fail to
> propagate: upper bounds propagate by monotonicity + union bound
> (R6.1), which is exactly the mechanism GENIND-C1(ii) (R1.2 above)
> uses for the vanishing-rate BOUND. The two consumers want different
> strengths; only the identity consumer needs (CS-EXACT).**”

R6.2 explicitly preserves the load-bearing sentences: “The record's load-bearing sentences STAND ("an identity only if those u's are exact" — true; P(n)'s fourth member fails under bound-only inputs — true, the member is an equality).”

**SUPERSESSION KIND:** R6.2 = `provenance-rider` — the clause's own content is untouched; what is replaced is the *reason* the note gives for needing it. Distinguishing this from a `wording-rider` matters: a merge that treats R6.2 as re-wording (CS-EXACT) would corrupt the DAG by implying the clause changed.

**DERIVATION:** The consumption path is §S6 Step 4's `[r1]` record (`.58`), quoted there in full.

**RESOLUTION TRACE:** statement lines 197–214. proof lines 1049–1100 (Step 4's `[r1]` record). correction sites: `[r2, PE2-m1]` in situ at 201–206 (landed); 1172–1190 (§S7.1's own (CS-EXACT) display, `.66`); 2961–3004 (ANNEX R R6, shard 3).

**TEETH:** `signed vacuity disclosure` in the de-facto direction: the n = 4 discharge is a citation of GENH4.A/B, not a battery row of this note; no GENIND tooth exercises exactness at any degree. R6.3's machine leg F (`genind_annexr_supp.py` @ f5271e4, GREEN, symbolic) guards the *separation*, not the clause: “dF/du₁ = T₂ − u₂; ∂G/∂u_i = Π_{j≠i}(T_j − u_j) at r = 2, 3; the union-bound dominance certificates”, with a decorrelation record (“the fold's scaffold P-4 PREREGISTERED the same arithmetic before the run and its sympy leg confirmed it — two decorrelated models, same kill”) — disposition `accepted-with-decorrelation-supplied`.

XREF: `lean/notes/openmath/GENH4_PROOF_2026-08-08.md:THEOREM GENH4.B` — count **6**.
XREF: `lean/notes/openmath/GENH4_PROOF_2026-08-08.md:GENH4-CAP(F)` — count **11**.

---

### EFF.GENIND.s1of3.15  [theorem]

**CANONICAL STATEMENT:** FORM: display (blockquote, THEOREM GENIND.B's conclusion + consequence). verbatim, lines 215–223.

> “> THEN P(n) holds. CONSEQUENTLY, by strong induction from the proved
> bases P(2) (W-11/W12-L0) and P(3) (HEX3+HMENU3): given [GENIND-H(n)]
> for all n, the packages (hMenu-n)+(hExhaust-n) hold for ALL n, and
> THEOREM W-12.D fires at every degree — THE FULL UNIFORMITY THEOREM:
> one R_τ(q) ∈ ℚ(q) per splitting type at every degree, every prime
> power, both characteristics, wild primes included, Σ_τ R_τ = 1.
> At n ≤ 3, [GENIND-H] is EMPTY (S5): the theorem is unconditional
> there and reproduces the proved instances. At n = 4, 5 the entire
> conditional surface is the (2,2)-type stages of S5.3/S7.”

**CONDITIONALITY:** **The displayed conditionality is WIDENED at n ≥ 8 by an inbound supplier movement.** The dated supplier-movement record (lines 3076–3088, shard 3), after GENHN's PE1 refuted LEMMA GENHN-T(b) and its r2 proved T(b)′ behind a new box:

> “**THE CONDITIONALITY MOVEMENT (this record's point).** S16 row 1's
> firing geography names GENHN.C at μ = 2 stages with n ≥ 6 =
> [GENHN-HE(μ ≥ 3)] (read per PE7-m3: the content rides inside
> [GENIND-H]'s display). After T(b)'s refutation and T(b)′'s proof,
> GENHN.B carries its tower clause at n ≥ 8 through the boxed
> [GENHN-TOW-1]. Accordingly, read THIS note's conditionality at
> n ≥ 8 as: **[GENIND-H(n)] + [GENHN-HE(μ ≥ 3)] + [GENHN-TOW-1]** —
> the n ≥ 8 leg rests on [GENHN-TOW-1] IN ADDITION TO
> [GENHN-HE(μ ≥ 3)], per GENHN.B's restated clause; at n ≤ 7 nothing
> moves (sealed grade, the same clause). No count law, theorem
> clause, consumption verdict at n ≤ 7, or frozen number of this note
> moves — the movement is conditionality bookkeeping at the open
> frontier.”

The “At n = 4, 5 the entire conditional surface is the (2,2)-type stages” sentence is unaffected (n ≤ 7 explicitly unmoved).

**SUPERSESSION KIND:** `scope-pin` — the conclusion's wording is untouched; the hypothesis conjunction is re-read range-by-range (n ≤ 7 unchanged; n ≥ 8 gains two named conjuncts).

**TARGETS:** `s1of3.15`, and by inheritance `s1of3.04`, `s1of3.13`, `s1of3.61`.

**DERIVATION:** §S6 Step 5 (`.60`) fires W-12.D; the strong induction is Steps 1–4 plus the two proved bases. The base pins are §S9.3's (shard 2): W-11 @ **ACCEPTED 2/2 35e6545**; HEX3 @ **r3 b6a1d69**; HMENU3 @ **ACCEPTED body 050425d + ANNEX A 19c0285**.

**RESOLUTION TRACE:** statement lines 215–223. proof lines 1102–1106 (Step 5). correction sites: 1483–1517 (§S9.3's re-pins of the two bases, shard 2); 3032–3094 (the supplier-movement record, shard 3).

**TEETH:** NONE — the consequence is a theorem application, not a measured quantity. **Note for the merge:** §S11's closing paragraph (lines 1760–1764, shard 2) states the *machine* status of this clause (“THEOREM GENIND.B stands as the displayed reduction … conditional exactly on the composite-stage package [GENIND-H] per genre plus the supplier arc grades”), which is a verdict record, not a tooth.

XREF: `lean/notes/openmath/W11_PROOF_2026-08-08.md:THEOREM W-11` — count **3**.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:W12-L0` — count **32**.
XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN-TOW-1` — count **19**.
XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN.C` — count **19**.
**NEAR-MISS (rule 15):** `[GENHN-HE(μ ≥ 3)]` — designation absent as written in `GENHN_PROOF_2026-08-08.md` (fixed-string count **0**); the note itself records the locality defect at PE7-m3 (lines 2499–2506, shard 2): “the string "GENHN-HE" occurs at r6 only inside S16 itself (grep: L2354, L2397 …) — the note displays no box by that name; the μ ≥ 3 stage-law content rides inside [GENIND-H]”. Verified referent: the μ ≥ 3 stage-law content of `[GENIND-H]`. Carried descriptively; **not** emitted as a clean XREF.

---

### EFF.GENIND.s1of3.16  [scope-record]

**CANONICAL STATEMENT:** FORM: bold display (the GRADE box closing THEOREM GENIND.B). verbatim, lines 225–227.

> “**GRADE: the reduction (IH)+[GENIND-H] ⟹ P(n) PROVED at the S6
> level of detail (scaffold); [GENIND-H] OPEN (the frontier), with
> the (2,2) instance attacked in S7.**”

**CONDITIONALITY:** Stands. Two qualifications from outside the range, neither editing it: GENIND-BOX-1 (lines 1351–1356, shard 2) prices “the S6 level of detail” — “No count law at order ≥ 2 is claimed proved”; and the ANNEX R close (lines 3022–3025, shard 3) discloses that the annex layer which supplies R1's rate leg “has NOT itself been through a hostile pass”, so the (A2-RATE) strengthening of `.13` carries a **lower** grade than the frozen body it repairs.

**DERIVATION:** Not a mathematical unit; a grade declaration.

**RESOLUTION TRACE:** statement lines 225–227. correction sites: 1351–1356 (GENIND-BOX-1, shard 2); 3022–3028 (the ANNEX R close, shard 3); 3285–3294 (the ANNEX R — r1 grade line, shard 3: “The annex stack remains 0/2”).

**TEETH:** NONE — a grade declaration.

---
### EFF.GENIND.s1of3.17  [lemma]

**CANONICAL STATEMENT:** FORM: display (blockquote, LEMMA GENIND-1 clause (i)). verbatim, lines 231–235.

> “**LEMMA GENIND-1.** In the cluster system (m, d, N), m ≥ 2:
> (i) [partition] every state is exactly one of DRAIN / DEC / α(k) /
> β / CS as in GENIND.A(I), and the α-locus law is
> (Q−1)·Q^{m(N−1) − k·m(m+1)/2};”

**CONDITIONALITY:** Unconditional at order 1, both characteristics, all (m, d) with m ≥ 2. It consumes W-12 §S1's `[r1 F3]`-corrected refine taxonomy as a cited supplier, and the exactness-of-the-hull argument is “the w12 reader's mechanics, HEX3 S2 verbatim at general m”. The window-1 boundary is supplied by ANNEX R R3 (`.07`).

**DERIVATION:** verbatim, lines 245–264 (the proof's paragraph (i)):

> “*Proof.* (i) The read is deterministic: the drain rule fires first
> (v(a₀) ≥ N); otherwise the exact polygon is computed (exactness of the
> hull with window-hidden points: every hull line lies weakly below the
> chord from (0, v(a₀)) to (m, 0), hence strictly below height N, so a
> point with v(a_j) ≥ N is strictly above every candidate line — the
> w12 reader's mechanics, HEX3 S2 verbatim at general m); per side the
> residual over F_Q factors uniquely; the residual trichotomy per factor
> (separable / repeated linear on e = 1 / repeated with e·deg ψ ≥ 2) is
> exhaustive by definition, and W-12 S1's [r1 F3]-corrected taxonomy
> says exactly: separable factors are Ore-decided pieces, repeated
> linear factors on e = 1 sides recenter (order 1), everything else
> repeated opens a composite key of degree e·d·deg ψ > d. α is the case
> "one side, integer slope, residual (y−z)^m" — the unique case in
> which the fracture partition is the trivial partition (m). The
> α-locus count is the S2.2 slot count: m pinned digits (the
> coefficients of (y−z)^m at the m lattice points j = 0..m−1, one
> letter z ∈ F_Q^×: the pins are universal polynomial identities in z,
> degenerating but never merging in small characteristic — J-D0's
> blindness, HEX3 S2's (α) bullet at general m), all deeper digits
> free: Q^{Σ_j (N−1−(m−j)k)} = Q^{m(N−1) − k·m(m+1)/2}.”

Justification tags: determinism + hull exactness = `computation` (the chord/convexity inequality) `by XREF` the w12 reader's mechanics; the trichotomy = `by XREF W-12 S1` `[r1 F3]` taxonomy; exhaustiveness = `by definition`; the α-locus count = `computation` (S2.2 slot count, arithmetic-audited below) + `by XREF LEMMA J-D0` for small-characteristic non-degeneracy of the letter.

**ARITHMETIC AUDIT (compiler-computed, rule 22 in spirit — a displayed count identity):** the free-digit sum is Σ_{j=0}^{m−1} (N−1−(m−j)k) = m(N−1) − k·Σ_{j=0}^{m−1}(m−j) = m(N−1) − k·(m + (m−1) + … + 1) = m(N−1) − k·m(m+1)/2 ✓ — the displayed exponent, recomputed fresh. Cross-check against `.09`'s ghost-fiber count: `.21` charges Σ_{j<m} jk = k·m(m−1)/2 = k·c(m) ghost slots, and c(m) + m(m+1)/2 − m(m−1)/2 = c(m) + m; consistent with `.21`'s statement that the α(k)-slice's menu is (Q−1)·Q^{k·c(m)} × the window-(N−mk) menu, since the window-(N−mk) system has Q^{m(N−mk−1)} states and (Q−1)·Q^{k·c(m)}·Q^{m(N−mk−1)} = (Q−1)·Q^{m(N−1) − k·m(m+1)/2} ✓ (exponent check: k·c(m) + m(N−mk−1) = k·m(m−1)/2 + m(N−1) − km² = m(N−1) − k·m(m+1)/2 ⟺ m(m−1)/2 − m² = −m(m+1)/2 ✓).

**RESOLUTION TRACE:** statement lines 231–235. proof lines 245–264. correction sites: 2873–2876 (R3's grammar-coherence bullet at window 1, shard 3). No `[rN]` bracket touches this clause.

**TEETH:** GT-PART [SAME] (§S11 P-2 “0/33 — partition exact on every row”) · GT-DEPTH0 [SAME, both directions] (§S11 P-3 “0/108”, with every never-measured spot exact) · GT-CRIT (the CS-branch side conditions). Executable regressions on the sealed roster.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:S2.2` — count **19**.
XREF: `lean/notes/openmath/JD0_PROOF_2026-08-08.md:LEMMA J-D0` — count **4**.
**NEAR-MISS (rule 15):** `HEX3 S2` — designation absent as written (fixed-string count **0** in `HEX3_PROOF_2026-08-08.md`); verified referent at `HEX3_PROOF_2026-08-08.md:188` under `## S2. THE DEPTH-0 PARTITION (LEMMA H-1)`. GENIND's `HEX3 S2` is a note-qualified section pointer, not a supplier designation.

---

### EFF.GENIND.s1of3.18  [lemma]

**CANONICAL STATEMENT:** FORM: display (blockquote, LEMMA GENIND-1 clause (ii)). verbatim, lines 236–238.

> “(ii) [α preserves the cluster] the α(k)-recentering is a bijection
> of the z-slice onto the node D_k := {v(a_j) ≥ (m−j)k + 1 ∀j};”

**CONDITIONALITY:** Unconditional; explicitly characteristic-free (“the binomial identities … valid in every characteristic”).

**DERIVATION:** verbatim, lines 264–269 (the proof's paragraph (ii)):

> “(ii) is HEX3
> H-2(iii)'s computation at general m: recentering by ẑπ^k cancels all
> m pinned digits (the binomial identities Σ_i C(·)z^i from
> (y−z)^m expanded at y = z + ·, valid in every characteristic), is
> injective (a shift), and #slice = (Q−1)·Q^{m(N−1)−k·m(m+1)/2}/(Q−1) =
> #D_k — a bijection.”

Justification tags: `by XREF HEX3 H-2(iii)` (the n = 3 instance, generalized by parameter substitution) + `computation` (binomial cancellation, injectivity, cardinality).

**ARITHMETIC AUDIT:** `#slice = (Q−1)·Q^{m(N−1)−k·m(m+1)/2}/(Q−1) = Q^{m(N−1)−k·m(m+1)/2}`; and `#D_k = Π_{j<m} Q^{N−1−(m−j)k} = Q^{m(N−1)−k·m(m+1)/2}` ✓ — the two sides agree, recomputed fresh from the node's defining inequalities `v(a_j) ≥ (m−j)k + 1` (which pin exactly (m−j)k of the N−1 free digit levels at abscissa j).

**RESOLUTION TRACE:** statement lines 236–238. proof lines 264–269. correction sites: none.

**TEETH:** GT-ALPHA [SAME, pointwise + fibers + onto] — §S11 P-5 “✓ GT-ALPHA 0/2,474 — every pointwise scaled re-read agrees (verdict + σ), every ghost fiber exactly q^{k·m(m−1)/2}, scaled states onto the full reduced-window space”, with tooth GT-T-ALPHA firing at its preregistered count 12. Executable regression, pointwise + surjectivity.

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:H-2` — count **11**.

---

### EFF.GENIND.s1of3.19  [lemma]

**CANONICAL STATEMENT:** FORM: display (blockquote, LEMMA GENIND-1 clause (iii) — **fracture permanence**). verbatim, lines 239–243.

> “(iii) [fracture permanence] after a β-event the separation
> valuations of the child clusters are CONSTANT along the rest of the
> chain: every later recentering is strictly deeper than every
> separation depth, so children never re-merge, each child's
> continuing read is a function of that child's own state alone, and
> the top-level chain grammar is α* [optional fracture, then the
> children's independent grammars] — two species and nothing else.”

**CONDITIONALITY:** Unconditional at order 1 within GENIND-3's scope. **Extended to mixed CS+child frames by LEMMA GENIND-6(b)** (`.35`), which re-runs this valuation argument with stage blocks in the frame and consumes GENHN.A(iv)'s stage node floor to do it. **INTERFACE FLAG (compiler note, not a note claim):** this clause is the load-bearing consumer named at ledger row **HYP.121** (`spec/HYPOTHESIS_LEDGER.md:970–974`) — *“GENIND-1, essential to W12-HT Step 3 and termination/compatibility, is valid over arbitrary complete DVRs. … CLASS: interface-generality. PROPOSED DISPOSITION: CARRY.”* The Q1 generality audit's own wording (`runs/qgen/HYPLEDGER_crossread.md:922–924`): *“**INTERFACE — load-bearing, unaudited**. `GENIND-1` is essential in W12-HT Step 3 and termination/compatibility, but its statement and proof were not pasted. Its generality cannot be certified here.”* **The note itself makes no all-`O` claim beyond its S1 convention “O a complete DVR … either characteristic” (`.07`), and the proof below uses no residue-characteristic hypothesis** — but the audit's point stands: no pass has certified the generality, and the note's machine leg is prime-q, d = 1 (GENIND-BOX-3). Carried as an OPEN-CALL (§8, OPEN-CALL 1).

**DERIVATION:** verbatim, lines 269–282 (the proof's paragraph (iii)):

> “(iii) is HM3-1(iii)'s valuation argument at
> general m: at the fracture, the polygon of the recentered/scaled
> frame splits the roots into groups by valuation (one group per side,
> one subgroup per residual root); for a child C entering at depth k_C,
> every non-C root differs from the C-cluster at valuation exactly its
> separation depth s ≤ k_C, while all subsequent recenterings within C
> have v(s′) > k_C ≥ s — so the separation digits are never touched:
> the hull of the full frame remains [child hull, sheared] ∪ [the
> other sides], with residual coefficients equal to the child's up to
> the unit Π(−ρ̄_i) of the split-off factors' values (LEMMA W12-L1(b)'s
> computation, product form: letters move by a unit, hulls/lattice
> points/separability types do not). Hence the continuing read of C is
> the (μ_C, d) system's read of C's own state, and no later event can
> involve two children at once. ∎”

Justification tags: `by XREF HM3-1(iii)` (the n = 3 instance, generalized by parameter substitution) + `computation` (the valuation comparison s ≤ k_C < v(s′)) + `by XREF LEMMA W12-L1(b)` (letters move by a unit; hulls/lattice points/separability types do not).

**RESOLUTION TRACE:** statement lines 239–243. proof lines 269–282. correction sites: none in range; extended (not corrected) at 626–634 and 685–695 (GENIND-6(b) statement and proof, `.35`).

**TEETH:** Guarded jointly by GT-BETA (pointwise Hensel reconstruction + child re-read, §S11 P-6 “0/87,156”) and by §S14's claim-group **C13**, which classifies exactly this sentence: “The mathematical "never" claims (GENIND-1(iii) no-re-merge, GENIND-2(a) ghost non-contamination, GENIND-6(a)/(b) factor-genericity and no-re-merge, the S4.3 instrument lesson) — lemma content or normative, machine-corroborated pointwise (GT-ALPHA/GT-BETA, supp, PE3/PE4 fresh legs), attacked across PE1–PE4 and held. KEPT.” Disposition: executable regression (pointwise) + `in-house hostile pass` (rule 27) — four passes attacked it and none refuted it.

XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:HM3-1` — count **4**.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:W12-L1` — count **30**.

---

### EFF.GENIND.s1of3.20  [instance-record]

**CANONICAL STATEMENT:** FORM: inline sentence pair closing §S2. verbatim, lines 284–286.

> “The n = 3 instances: (i) = HEX3 H-1; (ii) = HEX3 H-2(iii); (iii) =
> HM3-1(iii). At n = 2, (iii) is vacuous (no nontrivial fracture) —
> which is why W-11 never needed it.”

**CONDITIONALITY:** A provenance + vacuity record. The vacuity claim at n = 2 is what makes W-11 an admissible base for the strong induction without a fracture-permanence supply (`.15`).

**DERIVATION:** Not a proof; an instance attribution. The three attributions are the same three the proof paragraphs of `.17`–`.19` name internally.

**RESOLUTION TRACE:** statement lines 284–286. correction sites: none.

**TEETH:** GT-N3TIE [NONE] — §S11 P-9: “my fresh reader's n = 3 depth-0 species tables equal BOTH the HEX3 S5.1 closed forms AND the committed hex3 JSON, key by key (locus AND drained): the reader IS the suppliers' convention where they overlap”, 0/16. `foreign-note evidence` consumed as a convention tie.

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:S5.1` — count **9**.
**NEAR-MISS:** `HEX3 H-1` — as at `.05`; referent `LEMMA H-1`, `HEX3_PROOF_2026-08-08.md:188`, fixed-string `H-1` count **5**.

---

### EFF.GENIND.s1of3.21  [lemma]

**CANONICAL STATEMENT:** FORM: display (blockquote, LEMMA GENIND-2 clause (a)). verbatim, lines 290–299.

> “**LEMMA GENIND-2.** (a) [window coherence + shear] With
> σ_k(a_j) := a_j/π^{(m−j)k} mod π^{N−mk} coordinatewise: the chain of
> X ∈ D_k and the chain of σ_k(X) (a window-(N−mk) state of the same
> (m, d) system) correspond step for step, heights shearing by
> (j, v) ↦ (j, v − (m−j)k); every consulted digit of X sits strictly
> below the ghost zone {≥ N − jk} at abscissa j; each scaled state has
> exactly Q^{k·c(m)} ghost-fiber preimages (Σ_{j<m} jk = k·m(m−1)/2
> ghost slots), all key-constant. Hence the α(k)-slice's
> history-resolved menu = (Q−1)·Q^{k·c(m)} × the window-(N−mk) menu,
> key-sheared.”

**CONDITIONALITY:** Unconditional for `mk ≤ N−1`. **At the endpoint `mk = N−1` the target window is 1**, outside S1's stated `N ≥ 2`; ANNEX R R3 supplies it (`.07`), naming this site first: “(a) GENIND-2(a)'s α(k) endpoint mk = N−1, first at (m, N, k) = (2, 3, 1)”. §S14's window-site inventory classifies this display **α-CORRECT** (site class 3): “S3 LEMMA GENIND-2(a)(b) statement + proof (σ_k windows, ghost zones {≥ N − jk}, window condition mμ ≤ N−1) — α-CORRECT. ✓” — i.e. the `N − mk` window here is NOT the child-extraction window that `[r3]` capped, and it is right as displayed.

**DERIVATION:** verbatim, lines 308–328 (the proof's paragraph (a)):

> “*Proof.* (a) The three parts are HEX3 H-2(i)(ii)(iii) with the n = 3
> exponents replaced by their general forms, plus HM3-2's upgrade of the
> correspondence from drain-verdict resolution to KEY resolution. Ghost
> zones: along any chain from D_k every recentering has v(s) ≥ k+1; the
> consulted heights at abscissa j are ≤ the hull height ≤ (m−j)(N−1)/m
> (convexity from (0, ≤ N−1) to (m, 0)), and (m−j)(N−1)/m < N − jk for
> all 0 ≤ j < m and mk ≤ N−1 (cross-multiply: m(N−jk) − (m−j)(N−1) =
> j(N−1−mk) + m ≥ m > 0; at j = 0 it reads N−1 < N; the HEX3 [r1 F1]
> corrected pairing, generalized — the ghost
> zone at abscissa j is {≥ N − jk}, deepest at the constant coefficient
> j = 0 which has NO ghosts). Updates: the recentering substitution
> x ↦ x + s (v(s) ≥ k+1) determines each a_j′ mod π^{N−jk} from the
> a_{j′≥j} mod their own windows (ring homomorphism per quotient; the
> binomial update matrix is triangular with unit diagonal), so ghost
> digits never contaminate consulted windows — in both ring types
> (carries move upward only). Shear/scaling: f(π^k(y + s̃)) =
> π^{mk}·f̃(y + s̃) makes recentering commute with σ_k; hulls, lattice
> points, side subdivisions and residual positions are preserved by the
> affine-in-j map; v(a₀) ≥ N ⟺ v(ã₀) ≥ N−mk. Fibers: coordinate j
> carries jk ghost digit-slots of size Q each. The count of ghost slots
> and the bijection (ii) of GENIND-1 give the displayed menu transport.”

Justification tags: `by XREF HEX3 H-2(i)(ii)(iii)` + `by XREF HM3-2` (drain-verdict → KEY resolution upgrade); the ghost-zone separation = `computation` (the displayed cross-multiplication); the update triangularity = `computation` (binomial matrix, unit diagonal) — **this is the pivot ANNEX R R2 later names as a UNIT pivot** (`.36`'s rider: “the update of the Φ-adic coordinates under x ↦ x + s is the binomial matrix, displayed at S3 as "triangular with unit diagonal" — the diagonal entries are the binomials C(j, j) = 1. Pivot = 1.”); the shear = `computation`; the fiber count = `computation` (Σ_{j<m} jk).

**ARITHMETIC AUDIT (compiler-computed):** the displayed cross-multiplication, recomputed: m(N − jk) − (m−j)(N−1) = mN − mjk − mN + m + jN − j = j(N − 1 − mk) + m. With mk ≤ N−1 the first summand is ≥ 0 and the second is m > 0 ✓. Ghost-slot total Σ_{j=0}^{m−1} jk = k·(m−1)m/2 = k·c(m) ✓.

**RESOLUTION TRACE:** statement lines 290–299. proof lines 308–328. correction sites: 2882–2884 (ANNEX R R3's site (a), shard 3); 2032–2033 (§S14 site class 3's α-CORRECT classification, shard 2); 2815–2819 (ANNEX R R2's RECENTER-ledger pivot entry, shard 3).

**TEETH:** GT-ALPHA [SAME] (pointwise + fibers + onto), §S11 P-5 “0/2,474 … every ghost fiber exactly q^{k·m(m−1)/2}, scaled states onto the full reduced-window space” · GT-RECUR [SAME] (α-drain self-similarity against fully-enumerated reduced windows), §S11 P-6 “GT-RECUR 0/8 — the α-drain self-similarity (q−1)q^{k·c(m)}·u_m(N−mk) exact at every realized k”. Executable regressions.

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:H-2` — count **11**.
XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:HM3-2` — count **5**.

---

### EFF.GENIND.s1of3.22  [lemma]

**CANONICAL STATEMENT:** FORM: display (blockquote, LEMMA GENIND-2 clause (b) — the general bracket). verbatim, lines 300–306.

> “(b) [the bracket] Σ over all finite sequences (k₁, …, k_r), k_i ≥ 1,
> Σk_i = μ, of Π_i (Q−1)Q^{c(m)·k_i} = (Q−1)·Q^{(c(m)+1)μ−1} =:
> b_{m,d}(μ) [r1, PE1-M1: as the aggregate of REALIZED α-prefix
> histories this carries the window condition mμ ≤ N−1 — each step is
> admissible iff m·k_i ≤ (its window) − 1, and the conjunction along
> the chain is exactly mμ ≤ N−1; the generating-function identity
> itself is unconditional].”

**CONDITIONALITY:** The generating-function identity is unconditional; the *realized-history* reading carries `mμ ≤ N−1` (already-landed `[r1, PE1-M1]`). Nothing later touches it.

**SUPERSESSION KIND:** (internal, already landed) `scope-pin`.

**DERIVATION:** verbatim, lines 328–332 (the proof's paragraph (b)):

> “(b) Generating function, exactly HM3-4's: one step contributes
> A₁(x) = Σ_{k≥1}(Q−1)Q^{c·k}x^k = (Q−1)Q^c x/(1−Q^c x) (c := c(m));
> chains contribute A₁/(1−A₁) = (Q−1)Q^c x/(1 − Q^{c+1}x), whose
> x^μ-coefficient is (Q−1)Q^{(c+1)μ−1}. ∎”

Justification tags: `computation` (geometric series + the chain composition A₁/(1−A₁)) `by XREF HM3-4` for the n = 3 template.

**ARITHMETIC AUDIT (compiler-computed):** A₁/(1−A₁) with A₁ = (Q−1)Q^c x/(1−Q^c x) gives numerator (Q−1)Q^c x and denominator (1−Q^c x) − (Q−1)Q^c x = 1 − Q^c x·(1 + Q − 1) = 1 − Q^{c+1}x ✓; the x^μ coefficient of (Q−1)Q^c x/(1 − Q^{c+1}x) is (Q−1)Q^c·Q^{(c+1)(μ−1)} = (Q−1)Q^{(c+1)μ − 1} ✓. Instance check at m = 2 (c = 1), Q = 4, μ = 2 — the note's own numeric check at `.64` gives 48 + 144 = 192 = (|K|−1)|K|³ = 3·64 = 192 ✓, matching (Q−1)Q^{2·2−1} = 3·4³ = 192 ✓.

**RESOLUTION TRACE:** statement lines 300–306. proof lines 328–332. correction sites: none after `[r1]`.

**TEETH:** GT-BRACKETID [SYM] — §S11 P-7 “24/24 — LEMMA GENIND-2(b) integer-exact at m ∈ {2,3,4,5} (exponent coefficients 2/4/7/11)”, tooth GT-T-BRACKET at its preregistered count 24. Executable regression (symbolic identity).

XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:HM3-4` — count **11**.

---

### EFF.GENIND.s1of3.23  [instance-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph. verbatim, lines 334–340.

> “**Instances (the exponent's n-dependence displayed).** c(m)+1 = 2 at
> m = 2 (W-11/HEX3-S4's R-recursion telescoping coefficient
> (q−1)q^{2l−1}), 4 at m = 3 (HM3-4's (q−1)q^{4μ−1} — verified on 41
> rows at the HMENU3 seal), 7 at m = 4, 11 at m = 5 (machine: GT-AGGDEEP
> at n = 4, 5, this battery). At d ≥ 2 the same formulas hold in
> Q = q^d (roster limit: the battery exercises d = 1 plus one (m, d) =
> (2, 2) targeted row; GENIND-BOX-3).”

**CONDITIONALITY:** The d ≥ 2 sentence is the note's own disclosed coverage hole, priced at GENIND-BOX-3 (lines 1361–1366, shard 2): “general d ≥ 2 (and the Q = q^d letter spaces) rests on the proofs' Q-uniformity (the arguments never use d = 1) — machine-uncorroborated here beyond the w12-sealed order-1 instances”. §S14's claim group **C11** re-audits exactly that: “GENIND-BOX-3 "the arguments never use d = 1" — a proof-audit claim, already disclosed in the same box as machine-uncorroborated beyond the w12 order-1 instances; PE4 §2 left it as disclosed. KEPT with its hedge.”

**ARITHMETIC AUDIT (compiler-computed):** c(m)+1 = m(m−1)/2 + 1 at m = 2, 3, 4, 5 → 1+1 = 2 ✓, 3+1 = 4 ✓, 6+1 = 7 ✓, 10+1 = 11 ✓ — the four displayed values, recomputed fresh. They match §S11 P-7's scored tuple “(exponent coefficients 2/4/7/11)” ✓.

**DERIVATION:** Instantiation of `.22`'s closed form; no separate proof.

**RESOLUTION TRACE:** statement lines 334–340. correction sites: none. Related out-of-range records: 1361–1366 (GENIND-BOX-3), 2115–2118 (§S14 C11), both shard 2.

**TEETH:** GT-BRACKETID / GT-T-BRACKET as at `.22`. **Disposition caveat — `stale self-description` risk flagged, not asserted:** this display names the battery family **`GT-AGGDEEP`**, a family name that appears **nowhere else in the note**: §S10's family list (lines 1621–1631, shard 2) enumerates GT-PIN, GT-PART, GT-DEPTH0, GT-BDRAIN, GT-ALPHA, GT-BETA, GT-RECUR, GT-BRACKETID, GT-CRIT, GT-N3TIE, GT-CONS, GT-ORACLE — twelve families, no GT-AGGDEEP; and §S11 scores none. Recorded as a source defect (§8, defect 1), not repaired.

XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:HM3-4` — count **11**.
**NEAR-MISS:** `HEX3-S4` — designation absent as written in `HEX3_PROOF_2026-08-08.md` (fixed-string count **0**); the referent is HEX3's §S4 (the R-recursion), reachable through `R(M)` — fixed-string `R(M)` count **21**. Carried descriptively.

---

### EFF.GENIND.s1of3.24  [lemma]

**CANONICAL STATEMENT:** FORM: display (blockquote, LEMMA GENIND-3), carrying a **nested three-layer correction bracket** in situ. verbatim, lines 346–378.

> “**LEMMA GENIND-3.** Fix a β-genre at the (m, d, N) system: a polygon
> P with sides S₁, …, S_r, per-side residual factorization types with
> repeated factors all linear on e = 1 sides — child data
> (μ_l, k_l)_l (child sizes and entry depths, k_l = the slope of the
> child's side; children on one side share its slope) — and decided
> pieces (the separable factors). Then the genre's locus fibers over
>
>     Π_l [ the (μ_l, d) cluster system at window M_l ],
>
> M_l = N − D_l, **D_l = μ_l·k_l + Σ_{other blocks b} deg_b·min(s_b, k_l)**
> (s_b = block b's slope: every co-block — child, composite stage, or
> decided piece — contributes its slope-mass CAPPED at the extracted
> child's slope k_l; equivalently D_l = min_j (v(a_j) + j·k_l), the
> content of the scaled frame) — the explicit affine window of the
> scale-then-Hensel extraction at the child's frame [r3, PE3-G2:
> display corrected — the sealed display charged every co-block its
> OWN slope-mass (Σ_j μ_j k_j + Σ_pieces deg·slope-mass), which
> equals D_l iff every co-block sits at slope ≤ k_l [r4, PE4-G1: the
> r3 bracket glossed this condition "(true at every sealed
> instance)" — FALSE: steeper DECIDED PIECES violate it INSIDE the
> sealed roster, at the (2,5) n = 3 control row and the (2,6) n = 4
> row — see the honesty note below] and is FALSE for the shallower
> child at distinct-slope multi-child genres; see the honesty note
> below] —
> with fiber = (letter census of the
> genre: vertex units, child letters z_l, decided-piece residual
> letters) × Q^{(affine exponent in the genre parameters)}: the free
> digits of the decided pieces and the ghost digits of the scalings.
> Children entering at their own refine locus carry the entry datum j
> into the lower system's history key (the β3 mechanism).”

*(The display's closing clause — “Drain composition … Ore types}).” — is emitted separately at `.25`; the two quotations are byte-verbatim and their union is the whole display minus nothing. The split is a rule-18/test-3 call, audited at §6.1 item 7.)*

**CONDITIONALITY:** Schema grade, not closed form (`.26`). Hypothesis explicitly excludes CS-bearing polygons (`.29`). **The M_l display is the CAPPED one** — the reading a chapter cut must use — and its correction chain is three layers deep.

**SUPERSESSION KIND:** `[r3, PE3-G2]` = `replacement` (the sealed uncapped display is replaced by the capped formula; the sealed text is quoted inside the bracket as a dated record). `[r4, PE4-G1]` = `counter re-reading` on the r3 bracket's own inventory gloss (the *regime* inventory is re-counted; the formula does not move). **These two are not the same kind and must not be merged.**

**CHAIN:** sealed display (uncapped: “Σ_j μ_j k_j + Σ_pieces deg·slope-mass”) → `[r3, PE3-G2]` capped display `D_l = μ_l·k_l + Σ_b deg_b·min(s_b, k_l) = min_j(v(a_j) + j·k_l)` → `[r4, PE4-G1]` (the r3 gloss “(true at every sealed instance)” is FALSE; regime inventory restated) → `[r5, PE5-m2]` (step (1)'s same-side enumeration completed for GENIND-6(a)'s verbatim consumption) — **TERMINAL for the display: the `[r3]` capped formula, read with `[r4]`'s corrected regime inventory.** The `[r5]` layer is TERMINAL for the *proof*'s step (1) enumeration.

**DERIVATION:** verbatim, lines 380–443 (the three-step schema proof, with its `[r4]`/`[r5]` in-place corrections):

> “*Proof (schema; instance-proved, machine-checked pointwise).* Three
> steps, each the general form of an n = 3 route: (1) RECENTER +
> SCALE + NORMALIZE BY CONTENT [r4, PE4-G2: this step rewritten — the
> sealed-through-r3 text displayed the pre-cap uniform window
> "N − m·k_l", contradicting the corrected statement above and the
> note's own M6 ledger (N−4, not N−6) and degenerating at live
> instances (M6 at N = 5: window −1 against the ledger's 1; TWOCHILD
> child A at N = 7: 7 − 8 = −1 against the live extraction at 1); its
> reduction parenthetical ("separable factors with the other letters
> as roots… at their own slopes") was false at distinct-slope genres]:
> for the side S_l of slope k_l (integer, e = 1), recenter at the
> child's residual root (ẑ_l π^{k_l}) and scale x = π^{k_l}y. Each
> linear factor of the monic frame contributes content
> min(v(ρ − ẑ_l π^{k_l}), k_l) to f(π^{k_l}(y + ẑ_l)), so the total
> content is exactly D_l = μ_l k_l + Σ_b deg_b·min(s_b, k_l) =
> min_j(v(a_j) + j·k_l) — the statement's formula. Coefficient j of
> the substituted frame is determined mod π^{N + j·k_l} (GENIND-2(a)'s
> triangular-update mechanics: the a_{i≥j} enter it with the factor
> π^{ik_l}), so the primitive frame π^{−D_l}·f(π^{k_l}(y + ẑ_l)) is a
> level-0 frame with RAGGED certified coefficient precisions
> π^{N + j·k_l − D_l}, binding at the constant coefficient j = 0: a
> window-(N − D_l) = window-M_l frame. (The old uniform floor
> N − m·k_l is a true lower bound on every coefficient's precision —
> D_l ≤ m·k_l via the monic j = m term — but it is NOT the extraction
> window, and it undersells M_l strictly at every genre with a
> shallower co-block.) The reduction of the primitive frame is
> ȳ^{μ_l}·(a cofactor coprime to ȳ): same-side co-blocks appear at
> their SHIFTED residues z′ − ẑ_l ≠ 0 (decided pieces as separable
> factors, same-side co-CHILDREN as repeated factors
> (ȳ − (z′ − ẑ_l))^{μ} [r5, PE5-m2: within GENIND-3's own scope —
> repeated factors all linear on e = 1 sides — these two are the only
> same-side co-block types; under GENIND-6(a)'s VERBATIM consumption
> of this step at MIXED frames a third occurs: same-side COMPOSITE
> blocks as repeated NON-linear factors ψ(ȳ + ẑ_l)^{μ_b} (first
> visible at the same-side f-first genre, n = 6, N ≥ 7 — S4.3's
> grammar), coprime to ȳ because ψ, irreducible of degree ≥ 2 over
> F_Q, has no F_Q-root, so ψ(ẑ_l) ≠ 0 — the case GENIND-6(a)'s own
> coprimality gloss "co-blocks on the same side have distinct
> residual roots/factors" already carries, per the PE5 report]);
> co-blocks STEEPER than k_l all collapse to
> the single nonzero residue −ẑ_l (their letters leave the
> reduction); co-blocks SHALLOWER than k_l leave the reduction
> entirely by degree drop (each contributes deg_b·s_b to the content
> and drops the reduction's degree by deg_b — the monic-factor Hensel
> form with non-unit-lead cofactor). In the scaled frame NO co-block
> sits at its own slope.
> (2) HENSEL SPLIT: LEMMA W12-S2.1 at the scaled frame splits the state
> into the product of its branch states — the child (μ_l, d) blocks and
> the decided pieces — bijectively with multiplicative count transport;
> this is where the level-0 product structure re-enters BELOW level 0,
> exactly as W12-L1(a) did for n = 3's DBL. (3) READ EQUIVALENCE: by
> GENIND-1(iii) the continuing read of each child block equals the
> child system's own read with letters unit-scaled (W12-L1(b)'s
> computation, product form) — so histories, leaves, drains and σ
> transport verbatim, and the frame's raw key is the dictionary image
> of the children's (hist, leaf) tuples (HM3.A's dictionary, one entry
> per genre). The fiber count per genre is the S2.2 slot count of the
> genre's pinned/priced/free digits, an affine-exponent q-power times
> the letter census — the same bookkeeping that produced HEX3 H-3's
> three routes; the general per-route ledger is compressed into this
> schema plus: the three n = 3 routes PROVED and sealed (HEX3/HMENU3,
> consumed at pin), and the n = 4, 5 depth-0 genres checked POINTWISE
> by this battery (GT-BETA: Hensel product reconstruction + child
> re-read + drain/σ composition, member by member). ∎”

Justification tags: step (1) content = `computation` (per-root content sum) + `by XREF GENIND-2(a)` (triangular update mechanics, `.21`); step (2) = `by XREF LEMMA W12-S2.1` + `by XREF W12-L1(a)`; step (3) = `by XREF GENIND-1(iii)` (`.19`) + `by XREF W12-L1(b)` + `by XREF HM3.A` (the dictionary) + `by XREF W-12 S2.2` (slot count) + `by XREF HEX3 H-3` (the three n = 3 routes).

**ADDITIONAL CONDITIONALITY (from outside the range).** Step (3)'s fiber sentence is one of the **two** targets of ANNEX R R2's unit-pivot rider (lines 2792–2794, shard 3): “The same sentence pattern is consumed at GENIND-3 step (3) ("the fiber count per genre is the S2.2 slot count…"), so the rider covers both sites.” Read “triangular” there as **triangular with UNIT pivots** — see `.36` for the rider's full text and its per-ledger supply. Child extraction at `M_l = 1` is supplied by ANNEX R R3 (`.07`, site (b)).

**RESOLUTION TRACE:** statement lines 346–378. proof lines 380–443. correction sites: in situ `[r3]` 359–369, `[r4]` 363–367 and 382–389, `[r5]` 409–418 (all landed); out of range — 2779–2852 (R2's unit-pivot rider on step (3), shard 3), 2880–2886 (R3's site (b), shard 3); §S14 site classes 4, 5, 6 at 2034–2038 (shard 2) record the display as CAPPED ✓ and step (1) as DEFECTIVE → FIXED.

**TEETH:** GT-BETA [SAME] (pointwise Hensel reconstruction; §S11 P-6 “0/87,156 … coefficient-exact”) · GT-BDRAIN [SAME] (the n = 4 FULL-side β drain laws in closed form, consuming the PROVED n ≤ 3 drains R(M)/u₃(M); §S11 P-4 “0/4 — B2Q(1) drained = 512/1,024 at (·,2,6,n4)”) · the capped-window correction is guarded by PE3's committed fresh leg (`genind_pe3_fresh.*` @ f89b565, GREEN 705,133/0) and PE4's (`genind_pe4_fresh.*` @ 51bd1bc, GREEN 6,507/0) — both **foreign-note (verifier) evidence**, cited not claimed. Disposition for the ledger-compression half: **PROOF-ONLY**, with the note's own coverage-hole sentence at `.26`.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:W12-S2.1` — count **9**; `W12-L1` — count **30**; `S2.2` — count **19**.
XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:HM3.A` — count **18**.
XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:H-3` — count **5**.

---
### EFF.GENIND.s1of3.25  [lemma]

**CANONICAL STATEMENT:** FORM: display (the closing clause of LEMMA GENIND-3's blockquote; second byte-verbatim piece of the display whose first piece is `.24`). verbatim, lines 376–378.

> “Drain
> composition: the frame drains iff some child drains; decidedness:
> the frame is decided iff every child is (and then σ = ⊎_l σ_l ⊎
> {decided pieces' Ore types}).”

**CONDITIONALITY:** Unconditional inside GENIND-3's hypothesis (no composite block on the polygon). **Extended, not replaced, at mixed frames** by GENIND-6(d) (`.37`): “the frame is conservative-undecided iff SOME block is (inclusion–exclusion prices it: children's u's exact by (IH) member 4, stage drains exact by (CS-EXACT))”. **Quantitatively analysed from outside the range** by ANNEX-LEMMA GENIND-C1(ii) (lines 2694–2702, shard 3), which is the unit that turns this iff into a bound:

> “(ii) [composition through the fibration] the genre's contribution to
> u_{m,d}(N) is (prefactor count)·[Π_l T_l − Π_l (T_l − u_l)] —
> GENIND-3(c)'s product fibration (onto, constant fiber) with "the
> frame is conservative-undecided iff some child is". Bounding the
> inclusion–exclusion by the UNION BOUND (leg F: the difference
> Σ_l u_l·Π_{j≠l}T_j − [ΠT − Π(T−u)] expands with nonnegative
> coefficients in (u_l, T_l − u_l) at r = 2, 3 — no exactness is
> needed for the BOUND direction; see R6), the relative contribution
> is ≤ ρ_g · Σ_l u_l/T_l.”

and by R6.1's monotonicity correction (lines 2974–2981, shard 3), which refutes a *supplier report's* rationale, not this clause: “∂/∂u_i[Π_j T_j − Π_j(T_j − u_j)] = Π_{j≠i}(T_j − u_j) ≥ 0 — the composed undecided mass is coordinatewise NONDECREASING in the child u's”.

**SUPERSESSION KIND:** none received — GENIND-C1(ii) and R6.1 are *consumers/analyses* of this clause, not supersessions of it. Recorded here so a merge does not mistake them for edits.

**DERIVATION:** step (2)'s Hensel split (bijective, multiplicative count transport) + step (3)'s read equivalence, quoted in `.24`'s DERIVATION; the σ-union is the branchwise composition of W12-S2.1.

**RESOLUTION TRACE:** statement lines 376–378. proof lines 426–435 (steps (2)–(3)). correction sites: none in range; consumed/extended at 647–657 (GENIND-6(d)) and, out of range, at 2694–2702 and 2972–2997 (shard 3).

**TEETH:** GT-BDRAIN [SAME] — §S11 P-4 “✓ GT-BDRAIN 0/4 — B2Q(1) drained = 512/1,024 at (·,2,6,n4): the β drain composition through R(M) exact”; GT-BETA's per-member drain/σ composition. Executable regression, consuming the PROVED n ≤ 3 drains as inputs. **ARITHMETIC AUDIT of the quoted spot value:** the note's P-4 preregistration says “B2Q(1) drained = 512 of 1,024 (M = 2: R(2) = 2 of q^{2(M−1)} = 4 block states)”; recomputed at q = 2: the child block space at window M = 2 has q^{2(M−1)} = 2² = 4 states, R(2) = 2 of them drain, so the drained fraction is 1/2 and 1/2 × 1,024 = 512 ✓, matching §S11's scored “512/1,024”.

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:R(M)` — count **21**.

---

### EFF.GENIND.s1of3.26  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph. verbatim, lines 445–456.

> “**Honesty note (the GENIND-3 grade).** What is proved outright at
> general (m, d): steps (1)–(3) as stated — each is a supplier lemma's
> argument with m, d as parameters, none uses n = 3 specifics. What is
> NOT written here: the closed-form fiber exponent of every genre at
> every degree (there are finitely many genres per degree; each is a
> mechanical S2.2 evaluation, as S5.3 does for the n = 4, 5 flagship
> genres). A hostile pass should attack the ledger compression exactly
> as HEX3-BOX-2 invited: (a) onto-ness of the route maps at multi-child
> genres, (b) the M_l window bookkeeping when children sit on different
> sides, (c) the unit-scaling of letters when several pieces split at
> once. The pointwise machine leg is designed so that an error in ANY
> of (a)–(c) at n ≤ 5 surfaces as an integer mismatch.”

**CONDITIONALITY:** This is the note's own coverage-hole sentence for `.24` and the sentence GENIND-BOX-2 (lines 1357–1360, shard 2) prices. **Two of its three named hostile targets subsequently FIRED:** target (b) landed at PE3 (`.27`), and target (a) — “onto-ness of the route maps” — landed at the Codex ratification as F1, cured by ANNEX R R2's unit-pivot rider (`.36`). Target (c) has not fired.

**DERIVATION:** Not a proof; a grade declaration with a hostile-attack invitation.

**RESOLUTION TRACE:** statement lines 445–456. correction sites: none (the note never edits this paragraph); the two fired targets are recorded at 458–515 (in range, `[r3]`) and 2779–2852 (out of range, shard 3).

**TEETH:** **PROOF-ONLY** (rule 16). The note's own coverage-hole sentence, quoted for the row: “What is NOT written here: the closed-form fiber exponent of every genre at every degree”. Compensating instrument named by the paragraph itself: “The pointwise machine leg is designed so that an error in ANY of (a)–(c) at n ≤ 5 surfaces as an integer mismatch” — i.e. GT-BETA at n ≤ 5 only; above n = 5 the compression is unguarded.

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:HEX3-BOX-2` — count **4**.

---

### EFF.GENIND.s1of3.27  [changes-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (`[r3, PE3-G2]` correction record) with nested `[r4]`/`[r5]` layers. verbatim, lines 458–483.

> “**[r3, PE3-G2] The (b)-attack landed — the window display corrected
> above.** PE3 executed exactly attack (b) (children on different
> sides) and the sealed display's literal reading FELL: derivation —
> after recentering and scaling x = π^{k_l}·y, each linear factor
> (π^{k_l}y − ρ) of the monic frame has content min(v(ρ), k_l), so the
> extraction's content is D_l = Σ_roots min(v(ρ), k_l) = μ_l k_l +
> Σ_{other blocks} deg·min(own slope, k_l) — co-blocks STEEPER than the
> extracted child are capped at k_l, and the sealed display (own
> slope-mass, uncapped) overcharges exactly there. Counter-genre
> TWOCHILD at (q, 4, 1): hull (0,6)–(2,2)–(4,0), child A on [0,2] at
> slope 2, child B on [2,4] at slope 1, first visible N = 7 — beyond
> every sealed full-sweep window [r4, PE4-G1: the r3 parenthetical
> continued "why three passes and the battery could not see it" —
> FALSE as an inventory claim: the GENRE TWOCHILD is beyond the sealed
> windows, but the disagreeing REGIME (a co-block steeper than the
> extracted child) is NOT — steeper decided pieces realize it inside
> the sealed roster (the concordance paragraph below), so the uncapped
> display was refutable against sealed data since the seal; what no
> pass executed there was the display-vs-runner comparison]. True
> child-B window N − (2·1 + 2·min(2,1)) = N−4; the old
> display said N−6. Machine (genind_pe3_fresh, committed @ f89b565):
> ALL 2,048 states at (2,7) and ALL 177,147 at (3,7) extract child B at
> N−4, fibering ONTO the full 16-/81-class child space with constant
> fiber q⁷ — impossible at window N−6 (the child space would be one
> class); lift-stability 80 × 5 + 60 × 4 certifies N−4 as content. The
> steeper child A extracts at N−6, where both readings agree (the
> control).”

**CONDITIONALITY:** A landed correction record; the corrected display it installs is `.24`'s. Its own inventory parenthetical was FALSE and is corrected in place by the nested `[r4, PE4-G1]` layer, which quotes it.

**SUPERSESSION KIND:** `replacement` (of `.24`'s sealed display) — and, within itself, `counter re-reading` at the `[r4]` layer (the *regime* inventory is re-counted; the window formula does not move).

**ARITHMETIC AUDIT (compiler-computed, on every number this record displays):**
* Child-B capped window: `D_B = μ_B·k_B + Σ_other deg·min(s, k_B) = 2·1 + 2·min(2,1) = 2 + 2 = 4`, so `M_B = N − 4` ✓ (matches the display). Uncapped: `2·1 + 2·2 = 6`, so `N − 6` ✓ (matches “the old display said N−6”).
* Child-A window: `D_A = 2·2 + 2·min(1,2) = 4 + 2 = 6`, so `M_A = N − 6` under BOTH readings (uncapped: `2·2 + 2·1 = 6`) ✓ — which is exactly why A is the control.
* Hull consistency: (0,6)–(2,2)–(4,0) has left side [0,2] of slope (6−2)/2 = 2 ✓ and right side [2,4] of slope (2−0)/2 = 1 ✓; entry height v(a₀) = 6, so first visible at N ≥ 7 ✓.
* State counts: `(q, N) = (2, 7)` at m = 4, d = 1 gives `q^{m(N−1)} = 2^{24}` per centre — but the record's “ALL 2,048 states at (2,7)” is `2^{11}`, i.e. **a genre-restricted locus count, not the full sweep**; likewise `177,147 = 3^{11}` at (3,7) ✓ (same exponent 11, base q). Consistent as a genre locus; recorded because a reader who takes 2,048 for a state-space count will mis-scale it (§8, defect 2).
* Child space: 16 = 2^4 = q^{2(M_B−1)} at M_B = 7−4 = 3 ✓; 81 = 3^4 ✓. At the uncapped window M = 7−6 = 1 the child space would be q^{2·0} = 1 class ✓ — exactly the record's “impossible at window N−6”.
* Fibre: 2,048/16 = 128 = 2^7 ✓ and 177,147/81 = 2,187 = 3^7 ✓ — the “constant fiber q⁷” checks in both bases.

**DERIVATION:** The derivation is displayed inside the record (the per-root content sum), and is the same computation `.24`'s corrected step (1) now carries.

**RESOLUTION TRACE:** statement lines 458–483 (the `[r3]` record). proof lines 460–466 (the displayed derivation) + 392–405 (step (1)'s corrected content route). correction sites: `[r4]` in situ 469–476; §S13's own PE3-G2 record at 1846–1869 (shard 2), itself corrected in place by `[r4]`; §S14's PE4-G2/PE4-G1 items at 1972–2014 (shard 2).

**TEETH:** PE3's committed fresh leg `genind_pe3_fresh.*` @ f89b565 (GREEN 705,133 checks / 0 violations) — **foreign-note (verifier) evidence**, exhaustive at (2,7) and (3,7), plus lift-stability certification. **PIN VERIFICATION:** `f89b565` ✓ commit; `verification/openmath/genind_pe3_fresh.py`, `_output.txt`, `_results.json` all EXIST ✓ (md5 triple fce9cb08/2075dd28/360eb239 per §S15's enumerated freeze).

---

### EFF.GENIND.s1of3.28  [changes-record]

**CANONICAL STATEMENT:** FORM: bold-headed continuation (the CONCORDANCE paragraph, restated at `[r4, PE4-G1]`). verbatim, lines 483–515.

> “CONCORDANCE [r4, PE4-G1: restated — the r3 text here
> closed "at every sealed instance (all in the agreeing regime: every
> co-block shallower than or at the extracted child's slope)", which
> is FALSE]: the sealed runner's `extract_child` always computed
> D = min_j (v(a_j) + j·k) — the capped value — so no machine artifact
> or committed number moves; the defect was the display alone,
> silently corrected by the mechanics. NOT because the sealed roster
> sits in the agreeing regime: the disagreeing regime occurs INSIDE
> the sealed roster via steeper DECIDED PIECES (a piece needs one
> abscissa where a second child needs two) — PSTEEP3 at the (2,5)
> n = 3 CONTROL row (hull (0,4)–(1,2)–(3,0): decided piece on [0,1] at
> slope 2 over the (2,1)-child on [1,3] at slope 1; live, v(a₀) = 4 ≤
> N−1; capped D = 2·1 + 1·min(2,1) = 3 → child window 2, uncapped
> D = 4 → window 1; 32 states) and PSTEEP4 at the (2,6) n = 4 row
> (hull (0,5)–(1,3)–(4,0): capped D = 4 → window 2, uncapped 5 → 1;
> 512 states). Both cells were adjudicated EXHAUSTIVELY by PE4's
> committed fresh leg (`verification/openmath/genind_pe4_fresh.py` +
> output + results @ 51bd1bc, md5 aa2b9af8/1a29a9c1/e549331a [r5:
> the r4 text here read "e5493312" — a transcription typo of the
> results-JSON md5 inherited from the PE4 report's own listing; the
> file is byte-identical (md5 e549331a…) at its landing commit
> 51bd1bc and at this commit, git-show-verified both — the ARTIFACT
> never moved, only the quoted prefix was corrupt; see S15], GREEN
> 6,507/0): every state extracts at the CAPPED window, fibering ONTO
> 4 × fiber 8 resp. 8 × 64 child classes with verdict splits DEC/DRAIN
> 16/16 resp. 256/256 — where the uncapped window would force a single
> child class and 100% instant child-drain — plus a 972-state odd-q
> companion at (3,5) n = 3 (off-roster; odd-q pins live). The sealed
> battery's GT-BETA processed exactly these states at the capped
> windows since the seal (`run_row` beta-checks every BOTHER member,
> `do_beta_pointwise=True` on all rows): concordance holds because the
> runner was ALWAYS capped, not because the regimes agree.”

**CONDITIONALITY:** The CONCLUSION (“no committed number moves”) is unchanged across r3 → r4; only the REASON changes. §S14's PE4-G1 item states this explicitly (lines 2012–2014, shard 2): “The concordance CONCLUSION stands unchanged (the runner was always capped; no committed number moves); what changes is only WHY it holds.”

**SUPERSESSION KIND:** `counter re-reading` — the regime inventory is recounted (agreeing-everywhere → disagreeing-inside-the-roster) with the conclusion preserved. The nested `[r5]` layer is a `provenance-rider` on the artifact pin (a corrupt md5 prefix corrected; the artifact never moved). **Two different kinds inside one paragraph; a merge that flattens them loses the fact that the r5 item touched no mathematics.**

**ARITHMETIC AUDIT (compiler-computed, every number recomputed fresh):**
* PSTEEP3, hull (0,4)–(1,2)–(3,0): left side [0,1] drop 4−2 = 2 over length 1 → slope 2 ✓ (the decided piece); right side [1,3] drop 2 over length 2 → slope 1 ✓ (the (2,1)-child). Capped `D = μ·k + Σ deg·min(s, k) = 2·1 + 1·min(2,1) = 2 + 1 = 3` ✓ → child window N − 3 = 5 − 3 = **2** ✓. Uncapped `2·1 + 1·2 = 4` → window **1** ✓. Live check `v(a₀) = 4 ≤ N−1 = 4` ✓. State count: m = 3, d = 1, q = 2, N = 5 → the genre locus is quoted at **32 = 2⁵**; the full per-centre space is `q^{m(N−1)} = 2^{12}` — again a genre locus, not a sweep count (same reading caveat as `.27`).
* PSTEEP4, hull (0,5)–(1,3)–(4,0): left side [0,1] drop 2 → slope 2; right side [1,4] drop 3 over 3 → slope 1. Capped `D = 3·1 + 1·min(2,1) = 4` ✓ → window N − 4 = 6 − 4 = **2** ✓; uncapped `3·1 + 1·2 = 5` → window **1** ✓. Locus **512 = 2⁹**.
* Fibrations: “ONTO 4 × fiber 8” — child space at window 2 for a (2,1) child is `q^{2(M−1)} = 2² = 4` ✓, and 32/4 = **8** ✓. “8 × 64”: child space for a (3,1) child at window 2 is `q^{3(M−1)} = 2³ = 8` ✓, and 512/8 = **64** ✓. Both fibre sizes recomputed and matching.
* Verdict splits: “DEC/DRAIN 16/16” sums to 32 ✓ = PSTEEP3's locus; “256/256” sums to 512 ✓ = PSTEEP4's locus.
* Uncapped counterfactual: at window 1 the child space is `q^{μ·0} = 1` class and (by `.07`'s R3 rider) that single state DRAINs — exactly “a single child class and 100% instant child-drain” ✓.
* Odd-q companion: 972 = 4·3⁵ = 2²·3⁵; at (3,5), n = 3 this is a genre locus, not recomputable from the displayed data alone — **recorded as UNPINNED-BY-DISPLAY** (the number is backed by PE4's committed leg, which is pinned; the derivation is not displayed).

**DERIVATION:** Not a proof; a regime inventory with machine adjudication. Its mathematical content (the capped formula) is `.24`'s.

**RESOLUTION TRACE:** statement lines 483–515. correction sites: `[r4]` in situ 484–487, `[r5]` in situ 501–506; §S13's two corrected sentences at 1865–1869 and 1918–1925 (shard 2); §S14 claim groups C1/C2/C3 at 2082–2093 (shard 2); §S15's BONUS item at 2261–2274 (shard 2).

**TEETH:** PE4's committed fresh leg `genind_pe4_fresh.*` @ 51bd1bc (GREEN 6,507/0) — foreign-note (verifier) evidence, exhaustive on both cells; plus the sealed GT-BETA's own since-the-seal processing of those states. **PIN VERIFICATION:** `51bd1bc` ✓ commit; `verification/openmath/genind_pe4_fresh.py`, `_output.txt`, `_results.json` all EXIST ✓. Disposition: `arithmetic recount` (rule 27's AUDIT class) — the finding that produced this restatement is a recount of which sealed rows sit in which regime, which no battery row could have produced because the runner and the display never disagreed numerically.

---

### EFF.GENIND.s1of3.29  [fence]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph. verbatim, lines 517–521.

> “**[r2, PE2-G1] Scope note.** GENIND-3's hypothesis ("repeated factors
> all linear on e = 1 sides") excludes polygons that ALSO carry a
> composite block — those states are classified CS, and their
> transport (this fibration COMPOSED with the stage fibration over the
> same polygon) is LEMMA GENIND-6 (S4.3), first live at n = 6.”

**CONDITIONALITY:** Landed at r2; never corrected. Its “first live at n = 6” claim was re-audited at §S14 claim group **C6** and KEPT: “‘mixed genres first live at n = 6’ (S4.3 scope note, S6 Step 2, S12) — TRUE, KEPT. Evidence: the degree budget (child ≥ 2 abscissas + composite block ≥ 4, S4.3) + the machine instance M6 at n = 6.”

**DERIVATION:** The exclusion is definitional (GENIND-1(i)'s classification: “any factor with e·deg ψ ≥ 2 wins the classification”); the degree budget is `.31`'s.

**RESOLUTION TRACE:** statement lines 517–521. correction sites: none. Re-audit at 2099–2102 (§S14 C6, shard 2).

**TEETH:** NONE — a scope fence; outside the orphan count. Its factual claim (n = 6 first live) is guarded by the M6 machine instance (`.40`).

---

### EFF.GENIND.s1of3.30  [lemma]

**CANONICAL STATEMENT:** FORM: display (blockquote, LEMMA GENIND-0). verbatim, lines 525–534.

> “**LEMMA GENIND-0.** Finite products, finite disjoint unions, and
> affine re-parameterizations (unimodular integer changes of
> coordinates with shifts, e.g. (w₁, w₂) ↦ (w₁, δ = w₂−w₁−1)) of
> (A1)-admissible family data are (A1)-admissible: parameter sets
> stay finite unions of shifted products of arithmetic progressions;
> exponents ℓ = Σ ℓ_l stay affine with strictly positive integer
> coefficients after coordinate normalization; c_F = Π c_{F_l};
> visibility ν = max_l ν_l is handled by splitting the parameter set
> along the (finitely many) affine dominance regions, each rewritten
> as a shifted product by the δ-coordinate trick.”

**CONDITIONALITY:** Unconditional, given W-12's (A1) definition as the standard. **NOTE for the merge:** W-12's r4 round added a σ-LABELING clause INSIDE (A1) (§S16 row 1, shard 2: “The r4 σ-LABELING clause STRENGTHENS (A1)”), i.e. the *predicate this lemma preserves* moved at the supplier after this note's pin. §S16 records the consumption as SURVIVING (“more is demanded of P(n), nothing less is delivered by the theorem”), but **this lemma's closure claim is stated for the pre-r4 (A1)** and no round re-derives closure under the strengthened predicate. Carried as OPEN-CALL 3 (§8).

**DERIVATION:** verbatim, lines 536–543:

> “*Proof.* Products and unions: coordinatewise. Positivity: each ℓ_l is
> affine with positive coefficients in its own variables; the
> concatenated variable set keeps them. Dominance regions: for two
> affine forms ν₁, ν₂ with integer coefficients, {ν₁ ≥ ν₂} ∩ (shifted
> product) is a finite union of shifted products: induct on dimension,
> solving ν₁ − ν₂ = δ ≥ 0 by the substitution used at W-12 S3.4's
> 2SIDED instance ((w₁, w₂) = (w₁, w₁+1+δ)); finitely many regions for
> finitely many pairs. ν = the region's dominating form, affine. ∎”

with the consumption note, verbatim, lines 545–547:

> “(Consumed by S6 wherever a β-family multiplies lower menus; the n = 2
> instance is W-12 S3.4's own 2SIDED handling, the n = 3 instances are
> HM3.B's B-families.)”

Justification tags: products/unions = `computation` (coordinatewise); dominance regions = `computation` (induction on dimension) `by XREF W-12 S3.4` (the δ-substitution instance).

**RESOLUTION TRACE:** statement lines 525–534. proof lines 536–547. correction sites: none.

**TEETH:** NONE directly — (A1)-admissibility is a structural predicate no battery row measures. Guarded only Indirectly, through the fact that every menu the battery reconstructs is a finite q-power expression. **PROOF-ONLY**; the note supplies no coverage sentence for it, which is itself worth flagging to the cross-read.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:S3.4` — count **11**.
XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:HM3.B` — count **19**.

---

### EFF.GENIND.s1of3.31  [changes-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph opening §S4.3, carrying an `[r5, PE5-G1/PE5-m1]` correction bracket that quotes its false original in place. verbatim, lines 551–572.

> “**The gap this closes.** A state can open a composite stage AND carry
> a coexisting repeated-linear e = 1 child on another side of the same
> polygon. Such a state is classified CS (GENIND-1(i): any factor with
> e·deg ψ ≥ 2 wins the classification), but its TRANSPORT fell between
> two displayed scopes: GENIND-3 excludes it by definition ("repeated
> factors all linear on e = 1 sides"), and (CS-1)'s fibration display
> has no slot for a co-evolving child system — the S5.3 embedded
> co-pieces are all DECIDED (static). PE2 constructed the first live
> instance at n = 6. Degree budget: a child consumes ≥ 2 abscissas and
> a composite block ≥ 4 (S5.1), so mixed genres need m ≥ 6; at m = 6
> the budget is tight — exactly ONE (2, d) child at integer slope k
> and ONE composite block with e·μ·deg ψ = 4, no decided pieces
> [r5, PE5-G1/PE5-m1: the sealed-through-r4 text here continued "The
> first-visible genre (all others sit at deeper visibility floors —
> k ≥ 2, stage-steeper arrangements, and the f-first ψ²-block variants
> enter at v(a₀) = 2k + 2h ≥ 6, i.e. N ≥ 7) is PE2's" — FALSE at its
> last-listed subject: an f-first ψ²-block (e = 1, deg ψ = 2, μ = 2)
> spans 4 abscissas at INTEGER slope h, so its slope-mass is 4h, not
> 2h, and the displayed chain "2k + 2h ≥ 6" reads 4 ≥ 6 at the f-first
> minimum k = h = 1; the sentence also sat outside all nine of r4's
> record-audit grep patterns (key phrase hyphenated "first-visible",
> claim verb "enter at") — see S15].”

**CONDITIONALITY:** The gap statement and the degree budget stand; the entry-law sentence inside was FALSE and is replaced by the enumerated grammar `.32`. §S15's PE5-G1 item (lines 2213–2247, shard 2) records that “The CONCLUSION (every non-M6 mixed genre enters at v(a₀) ≥ 6, i.e. N ≥ 7; M6 uniquely first-visible at N = 5) was TRUE and is KEPT, now supported by the enumerated three-family grammar”.

**SUPERSESSION KIND:** `replacement` (the false entry law is replaced by an enumerated grammar; the quoted original stays as a dated record).

**ARITHMETIC AUDIT (compiler-computed):** degree budget — a repeated-linear e = 1 child of size μ_l ≥ 2 spans ≥ 2 abscissas; a composite block spans `e·μ·deg ψ ≥ 4` (`.11`'s necessity). 2 + 4 = 6 ✓, so m ≥ 6, and at m = 6 the budget is exactly saturated with no room for decided pieces ✓. The refuted chain, recomputed: at the f-first minimum k = h = 1 the old display gives 2·1 + 2·1 = 4, and 4 ≥ 6 is **false** ✓ — the note's own refutation checks.

**DERIVATION:** The classification citation is GENIND-1(i) (`.17`); the abscissa budget is §S5.1's necessity arithmetic (`.11`'s DERIVATION).

**RESOLUTION TRACE:** statement lines 551–572. correction sites: `[r5]` in situ 563–572; §S15's PE5-G1/PE5-m1 items at 2213–2249 (shard 2); §S14's Arc paragraph at 1939–1959 (shard 2, where the same witness is displayed as the demonstrated residual of r4's pattern scope).

**TEETH:** The n = 6 first-live claim is guarded by the M6 machine instance (`.40`). The **method** finding (a false sentence outside the audit's pattern scope) is a `decorrelated-model audit` disposition (rule 27): PE5, a fresh hostile context, found a sentence that r4's nine-pattern grep sweep structurally could not see; no battery row could have produced it.

---

### EFF.GENIND.s1of3.32  [lemma]

**CANONICAL STATEMENT:** FORM: bulleted display (the complete m = 6 mixed grammar, three arrangement families with their entry heights). verbatim, lines 572–595.

> “The complete m = 6 mixed grammar,
> entry heights re-derived from the polygon geometry (v(a₀) = Σ_sides
> length × slope, Gauss additivity), has exactly THREE arrangement
> families — the two composite types are (e, deg ψ, μ) = (2, 1, 2)
> and (1, 2, 2), the only solutions of e·μ·deg ψ = 4 with μ ≥ 2 and
> e·deg ψ ≥ 2 (S5.1's necessity cases) — and every cell other than
> M6's enters at v(a₀) ≥ 6:
>
> * **child + E-block** ((2, 1, 2); slope h/2, h odd — never the
>   child's side, half-integer vs integer slope): enters at
>   v(a₀) = 2k + 2h. The UNIQUE cell < 6 is (k, h) = (1, 1) — genre
>   M6 below, v(a₀) = 4; k ≥ 2 gives ≥ 6, and the stage-steeper
>   arrangement (h/2 > k, i.e. h ≥ 2k + 1) gives ≥ 8.
> * **child + f-first ψ²-block** ((1, 2, 2); integer slope h)
>   SAME-SIDE: k = h forced — one slope-k side of length 6, residual
>   (y − w)²·ψ(y)² — enters at v(a₀) = 6k ≥ 6 (= 6 at k = 1: the
>   f-first family's N ≥ 7 minimum).
> * **child + f-first ψ²-block DISTINCT-SIDE** (h ≠ k): enters at
>   v(a₀) = 2k + 4h ≥ 8 (minimum at (k, h) = (2, 1)).
>
> No other arrangement fits the 2 + 4 = 6 abscissa budget. So every
> non-M6 mixed genre enters at v(a₀) ≥ 6, i.e. N ≥ 7, and the
> first-visible mixed genre — uniquely, at v(a₀) = 4, N = 5 — is
> PE2's:”

**CONDITIONALITY:** Proved geometry with a **disclosed machine gap**, stated by §S15 (lines 2244–2247, shard 2): “HONEST LIMIT: the same-side f-first genre itself (the 6k law's genre) remains machine-unrealized corpus-wide — the law above is proved geometry, not yet a machine-exercised cell.” **That limit was subsequently closed from outside the note**: §S16's Arc records PE6 as “the same-side f-first genre machine-realized corpus-first, 2,132,082 checks / 0 violations single run” (lines 2319–2321, shard 2) — a verifier artifact, cited not claimed, and **the honest-limit sentence at §S15 is not edited**, so it is a `STALE-SELF-DESCRIPTION` as of r6 (rule 26).

**ARITHMETIC AUDIT (compiler-computed, every displayed entry height re-derived by Gauss additivity v(a₀) = Σ_sides length × slope):**
* Composite-type enumeration: solutions of `e·μ·deg ψ = 4` with `μ ≥ 2`, `e·deg ψ ≥ 2`. Factorizations of 4 with μ ≥ 2: (μ, e·deg ψ) ∈ {(2,2), (4,1)}; (4,1) fails `e·deg ψ ≥ 2`. At μ = 2, e·deg ψ = 2 splits as (e, deg ψ) = (2,1) or (1,2) ✓ — **exactly two**, as displayed.
* child + E-block: child length 2 at slope k contributes 2k; E-block length 4 at slope h/2 contributes 4·(h/2) = 2h ✓ → v(a₀) = 2k + 2h ✓. Minimum at k = h = 1 gives 4 ✓; k ≥ 2 with h ≥ 1 gives ≥ 6 ✓; stage-steeper h ≥ 2k+1 with k ≥ 1 gives 2k + 2(2k+1) = 6k + 2 ≥ 8 ✓.
* child + f-first SAME-SIDE: one side of length 6 at slope k contributes 6k ✓; = 6 at k = 1 ✓, so N ≥ 7 ✓.
* child + f-first DISTINCT-SIDE: child 2k + f-block length 4 at integer slope h contributes 4h ✓ → 2k + 4h. With h ≠ k and both ≥ 1: (k,h) = (2,1) gives 8 ✓; (k,h) = (1,2) gives 10; so the minimum is **8** ✓ as displayed.
* Budget: 2 + 4 = 6 = m ✓, saturated.
* Cross-check against the OLD false law: it charged the f-block 2h instead of 4h — the exact error `.31`'s bracket names ✓.

**DERIVATION:** Displayed inside the statement (polygon geometry + Gauss additivity + the two-solution enumeration). Cross-checked at §S15 against PE5's committed artifacts (lines 2239–2244, shard 2): “NINEMIX's hull (0,11)–(1,8)–(3,4)–(5,2)–(9,0) realizes the Gauss-additive entry height 11 = 1·3 + 2·2 + 2·1 + 4·(1/2) at n = 9, and SAMESIDE's single side (0,4)–(4,0) realizes the same-side entry height 4 = length 4 × slope 1 on 59,049 exhaustive states.” **Compiler recount of that cross-check:** 1·3 + 2·2 + 2·1 + 4·(1/2) = 3 + 4 + 2 + 2 = 11 ✓; the hull's side slopes are (11−8)/1 = 3, (8−4)/2 = 2, (4−2)/2 = 1, (2−0)/4 = 1/2 ✓ (strictly decreasing, so it is a genuine lower hull); 59,049 = 3^10 ✓ (a (q, N) = (3, ·) enumeration).

**RESOLUTION TRACE:** statement lines 572–595 (as re-derived at `[r5]`; the pre-r5 text is quoted at `.31`). proof lines — displayed in statement; cross-check at 2239–2247 (shard 2). correction sites: 2213–2247 (§S15 PE5-G1, shard 2); 2319–2321 (§S16 Arc's PE6 machine realization, shard 2).

**TEETH:** `disclosed non-repair` → later closed: at r5 the same-side f-first cell was machine-unrealized (the note says so); at r6 PE6 realized it corpus-first (2,132,082/0), a **foreign-note (verifier) regression** consumed as coverage. The two other families are exercised: distinct-side arrangements by PE5's NINEMIX/SAMESIDE legs, the child+E family by M6 (`.40`).

**PIN VERIFICATION:** PE5's leg `verification/openmath/genind_pe5_fresh.py`, `_output.txt`, `_results.json` all EXIST ✓ (md5 triple 6ef3132e/a0452521/bdc04c4d); PE6's `genind_pe6_fresh.*` all EXIST ✓ (87b0f27e/1c2f8eed/fb473a57); `bd9bce1` ✓, `ad1bd98` ✓ commits.

---

### EFF.GENIND.s1of3.33  [instance-record]

**CANONICAL STATEMENT:** FORM: display (blockquote, genre M6). verbatim, lines 597–602.

> “**genre M6** at (q, m, d) = (q, 6, 1): hull (0,4)–(2,2)–(6,0);
> left side [0, 2] slope 1, e = 1, residual c(y−w)² — a (2, 1)
> β-child entering at depth 1; right side [2, 6] slope 1/2 (h = 1,
> e = 2), residual (y−z)² with c = z² the shared vertex unit — a
> composite stage (m′, D′, E, K) = (2, 1·2, 2, F_q). Locus law
> (q−1)²·q^{6N−17}, visible iff 4 ≤ N−1.”

**CONDITIONALITY:** Unconditional as a genre definition; the locus law is derived by S2.2 slot counting and exhaustively machine-confirmed at its first two visible windows (`.40`).

**ARITHMETIC AUDIT (compiler-computed):** hull (0,4)–(2,2)–(6,0): left side [0,2] drop 4−2 = 2 over length 2 → slope 1 ✓; right side [2,6] drop 2 over length 4 → slope 1/2 ✓ (so e = 2, h = 1 ✓, and the block length 4 = e·μ·deg ψ = 2·2·1 ✓). Entry height by Gauss additivity: 2·1 + 4·(1/2) = 2 + 2 = 4 ✓ = v(a₀), matching `.32`'s child+E cell (k, h) = (1, 1) → 2k + 2h = 4 ✓. Visibility `v(a₀) ≤ N−1` ⟺ `4 ≤ N−1` ✓ (first visible N = 5). Stage datum: D′ = e·d·deg ψ = 2·1·1 = 2 ✓ (“1·2” as displayed), m′ = μ = 2 ✓, E = e = 2 ✓, |K| = q^{d·deg ψ} = q ✓. **Locus-law consistency check against `.40`'s exhaustive counts:** the law (q−1)²·q^{6N−17} at (q, N) = (2, 5) gives 1·2^{13} = 8,192 ✓ — exactly the “(2, 5): 8,192 states” of the machine record; at (2, 6) it gives 2^{19} = 524,288 ✓ — exactly the machine record's figure; at (3, 5) the full law gives 4·3^{13} = 6,377,292, of which the record's “full (z, w) = (1,1) letter slice” is 3^{13} = 1,594,323 ✓ (the (q−1)² = 4 letter pairs divided out). **All three machine row totals are reproduced from the displayed law.**

**DERIVATION:** Not separately proved here; the law is an S2.2 slot count (the pinned/priced/free digit accounting displayed at `.38`'s FIBRATION bullet).

**RESOLUTION TRACE:** statement lines 597–602. proof lines 746–751 (the FIBRATION bullet's free-digit accounting). correction sites: none.

**TEETH:** `genindr2_supp.py` FIBRATION leg — exhaustive at every enumerable window of the genre (`.40`). Executable regression.

---
### EFF.GENIND.s1of3.34  [lemma]

**CANONICAL STATEMENT:** FORM: display (blockquote, LEMMA GENIND-6 preamble + clause (a) [SPLIT]). verbatim, lines 604–624.

> “**LEMMA GENIND-6 (mixed-opening transport).** Fix a CS genre at the
> (m, d, N) system whose polygon/residual datum comprises β-children
> (μ_l, d) on e = 1 sides at integer slopes k_l, composite blocks
> (ψ_b, μ_b) with e_b·deg ψ_b ≥ 2 on their sides, and decided pieces.
> Then:
> **(a) [SPLIT]** GENIND-3's steps (1)–(2) apply VERBATIM — they are
> factor-generic: the recenter-and-scale extraction at an e = 1 side
> followed by the Hensel split (LEMMA W12-S2.1 at the scaled frame,
> monic-factor form with non-unit-lead cofactor) consults ONLY the
> coprimality of the reduction blocks, never the separability or
> linearity of the repeated factors. Iterating over the children
> extracts each as a (μ_l, d) cluster state at the SAME explicit
> window M_l = N − (μ_l k_l + Σ_{other blocks} deg·min(own slope,
> k_l)) as in GENIND-3 [r3, PE3-G2: capped, as corrected at S4.1 —
> the sealed echo here inherited the uncapped display] — composite
> blocks contribute their capped slope-mass exactly like decided
> pieces — and leaves each composite
> block as a monic cofactor with PER-COEFFICIENT certified windows
> (the triangular division ledger; the sibling-Hensel-loss
> composition GENHN already displays for embedded genres, "N ↦ N −
> (sibling Hensel loss) coordinate-wise").”

**CONDITIONALITY:** Unconditional at GENIND-3's schema grade (the display's own Conditionality line, `.37`). Three live riders:
1. **The “VERBATIM” consumption of step (1) is of the CORRECTED step**, per `[r4]`'s echo (quoted in the DERIVATION below) and `[r5, PE5-m2]`'s completion of step (1)'s same-side enumeration (`.24`). §S14 site class 7 records the check (lines 2039–2043, shard 2): “its "steps (1)–(2) VERBATIM" now consumes the corrected step (checked: the (a) statement, the (a) proof gloss, and step (1) display the same D_l). ✓”
2. **Child extraction at `M_l = 1`** is supplied by ANNEX R R3 (`.07`, site (b)).
3. **The GENHN consumed surface named in this clause is larger than §S9.3's four-clause list.** PE7-m2 (lines 2488–2498, shard 2) completes the inventory and names two sites inside this unit: “the GENHN S11.F schema cite at the GENIND-6(a) proof (L684) … and the embedded-genre echo at the GENIND-6(a) statement (L623: "the sibling-Hensel-loss composition GENHN already displays") — screen future GENHN errata against the seven sites, not four; the SURVIVES verdict is unchanged”.

**SUPERSESSION KIND:** `[r3]` echo = `replacement` (uncapped → capped). PE7-m2 = `inventory completion`. R3 = `inventory completion` (boundary case). **Three distinct kinds; none is a re-wording of the clause.**

**DERIVATION:** verbatim, lines 662–684 (the proof's paragraph (a)):

> “*Proof.* (a) Re-read GENIND-3's proof: step (1) (recenter + scale,
> GENIND-2(a) mechanics) and step (2) (Hensel split at the scaled
> frame) nowhere consult the type of the residual factors — the split
> needs the child block's reduction ȳ^{μ_l} (after recentering) to be
> coprime to the co-blocks' reduction, which holds because co-blocks
> on the same side have distinct residual roots/factors and blocks on
> other sides reduce coprime to ȳ or leave the reduction: STEEPER
> blocks collapse to the single nonzero residue −ẑ_l, SHALLOWER blocks
> contribute the content drop / degree-dropped cofactor (the
> monic-factor Hensel form, already listed among this note's classical
> suppliers) [r4, PE4-G2 echo: the r3-era clause "blocks on other
> sides sit at their own slopes" was the step-(1) defect's image here —
> no co-block sits at its own slope in the scaled frame; the
> coprimality CONCLUSION was and is right, per the corrected step
> (1)]. The
> window bookkeeping is the same content computation D = min_j
> (v(a_j) + j·k_l), M_l = N − D, with every co-block contributing its
> CAPPED slope-mass deg·min(own slope, k_l) to D regardless of type
> [r3, PE3-G2]. The cofactor's per-coefficient
> certified windows are the triangular division f/g: each u_j is a_·
> minus products of known-window terms whose valuation floors (the
> genre budgets) push the error terms deeper — an explicit affine
> ledger per genre, exactly the GENHN S11.F computation.”

Justification tags: factor-genericity = `by XREF` GENIND-3 steps (1)–(2) (`.24`) read as corrected; coprimality = `computation` (distinct residual roots/factors on a side; steeper/shallower dichotomy) with the same-side composite case supplied at `[r5, PE5-m2]` (`.24`); the window = `computation` (the content identity); the certified windows = `by XREF GENHN S11.F` (an explicit affine ledger per genre, **compressed here, not displayed** — see `.42`).

**RESOLUTION TRACE:** statement lines 604–624. proof lines 662–684. correction sites: `[r3]` in situ 617–619, `[r4]` in situ 672–676; out of range — 2039–2043 (§S14 site class 7, shard 2), 2044–2047 (site class 8: the (a)-proof coprimality clause DEFECTIVE → FIXED at r4), 2250–2260 (§S15 PE5-m2, shard 2), 2488–2498 (PE7-m2's inventory completion, shard 2), 2880–2886 (R3 site (b), shard 3), 3055–3074 (the GENHN per-clause survival screen, shard 3).

**TEETH:** `genindr2_supp.py` FIBRATION + CERTIFICATION legs at M6 (`.40`) — exhaustive at (2,5)/(2,6) and a (3,5) letter slice; PE3's FR-C (SS6, stage STEEPER than child, at (2,9)/(3,9)) and FR-A (300 M7T members at (3,6), reader ON) as **foreign-note evidence**. **Disclosed gap** (the note's own, at `.42`): the certified-window ledger at genres with ≥ 2 stage blocks is “not live at n ≤ 7”, and this note's own machine leg carries no stage-steeper instance.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:W12-S2.1` — count **9**.
XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:S11.F` — count **10**.

---

### EFF.GENIND.s1of3.35  [lemma]

**CANONICAL STATEMENT:** FORM: display (blockquote, LEMMA GENIND-6 clause (b) [PERMANENCE, extended]). verbatim, lines 625–634.

> “**(b) [PERMANENCE, extended]** GENIND-1(iii)'s valuation argument
> covers the mixed frame: every separation valuation between two
> blocks is ≤ min of their slopes; every post-opening move inside a
> child sits at depth > k_l (GENIND-1(iii) verbatim), and every
> post-opening move inside a stage block sits at ambient depth
> κ/e_b ≥ (S_b + 1)/e_b > h_b/e_b = that block's slope (stage refines
> recenter the key by dv-depth-κ monomials with κ ≥ S_b + 1 — the
> stage node floor, GENHN.A(iv) @ 850e77e). Hence blocks never
> re-merge, and each block's continuing read is a function of that
> block's own state alone.”

**CONDITIONALITY:** Unconditional GIVEN the cited stage node floor **GENHN.A(iv) @ 850e77e** — an external supplier clause, not proved here. The pin's survival is tracked: §S16 row 6 records GENHN as “**850e77e — UNMOVED** (re-pin is a no-op)” with three errata queued; the dated supplier-movement record (lines 3057–3059, shard 3) then discharges the disclosure — “GENHN.A(iv), consumed at GENIND-6(b) (the stage node floor S_b + 1): clause text not in the diff; its node-floor arithmetic was re-derived and STANDS at 7650b20 — SURVIVES.”

**ARITHMETIC AUDIT (compiler-computed):** the displayed chain `κ/e_b ≥ (S_b + 1)/e_b > h_b/e_b` requires `S_b + 1 > h_b`. With the stage's own convention `S_b = e_b·h_b` (used at `.68`: “S := 2h” at e = 2), `S_b + 1 = e_b h_b + 1 > h_b` holds for every `e_b ≥ 1, h_b ≥ 0` ✓. The proof paragraph makes the same step explicitly with `S_b = e_b h_b`: “a stage refine at dv-depth κ ≥ S_b + 1 = e_b h_b + 1 moves the key at ambient valuation κ/e_b > h_b ≥ h_b/e_b” ✓ — and note the display's right-hand comparand is `h_b/e_b` (the block's slope) while the proof's is the stronger `h_b`; both are correct, the proof being sharper.

**DERIVATION:** verbatim, lines 685–695 (the proof's paragraph (b)):

> “(b) The separation valuation between roots of distinct blocks is
> min(slope, slope′) (distinct sides) or the common slope (same side,
> distinct residual factors) — in every case ≤ each block's own slope.
> Child-internal moves are deeper than k_l ≥ its slope (GENIND-1(iii)).
> Stage-internal moves: a stage refine at dv-depth κ ≥ S_b + 1 =
> e_b h_b + 1 moves the key at ambient valuation κ/e_b > h_b ≥
> h_b/e_b; deeper stage nodes only increase κ. So no move inside any
> block ever reaches any separation digit: blocks never re-merge, and
> W12-L1(b)'s computation (letters move by the co-blocks' unit values;
> hulls, lattice points, residual types do not move) gives each
> block's continuing read as its own.”

Justification tags: separation valuations = `computation` (two cases, distinct/same side); child-internal = `by XREF GENIND-1(iii)` (`.19`); stage-internal = `by XREF GENHN.A(iv)` (the node floor) + `computation`; the read decomposition = `by XREF W12-L1(b)`.

**RESOLUTION TRACE:** statement lines 625–634. proof lines 685–695. correction sites: none in range. Out of range: 1535–1550 (§S9.3's GENHN bullet, added at `[r3, PE3-m4]` after being consumed since r1/r2 — an inventory defect the note discloses), 3057–3059 (the survival screen, shard 3).

**TEETH:** §S14 claim group **C13** covers “GENIND-6(a)/(b) factor-genericity and no-re-merge” as machine-corroborated pointwise and hostile-attacked across PE1–PE4; the M6 PARI read-composition leg (`.40`) is the mechanism-free evidence at the one fully-worked instance. Disposition: executable regression + `in-house hostile pass`.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN.A(iv)` — count **3**.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:W12-L1` — count **30**.
**PIN VERIFICATION:** `850e77e` ✓ commit.

---

### EFF.GENIND.s1of3.36  [lemma]

**CANONICAL STATEMENT:** FORM: display (blockquote, LEMMA GENIND-6 clause (c) [FIBRATION/PRODUCT]) with an indented ASCII display inside. verbatim, lines 635–646.

> “**(c) [FIBRATION/PRODUCT]** the genre's locus fibers as
>
>     (letter census) × q^{affine} × Π_l [(μ_l, d) system at M_l]
>                                  × Π_b [stage state space at the
>                                         certified windows],
>
> ONTO the full product with CONSTANT q-power fiber: the coordinate
> map is the triangular division ledger of (a), so the counted
> measure is the PRODUCT measure — in particular the stage-window
> count is INDEPENDENT of the child-system states and vice versa,
> with the letter unit-scalings absorbed by J-D0 letter-blindness
> (W12-L1(b) product form), exactly as in GENIND-3 step (3).”

**CONDITIONALITY:** **This clause was a CONFIRMED GAP at the Codex ratification (F1) and is repaired by a rider, not a re-proof.** ANNEX R R2.0 quotes the finding (lines 2783–2790, shard 3):

> “GENIND-6(c)'s onto-with-constant-fiber is carried by 'triangular
> with exact budget floors' + 'the same S2.2 slot bookkeeping' — and
> triangularity alone does NOT give surjectivity/constant fibers
> over truncated DVRs (Codex's valid toy: (x, y) ↦ (x, (x+π)y)
> mod π², triangular, fiber collapses at x = 0). The missing
> displayed step is the unit-pivot condition (the division ledger's
> pivots are units because the extracted factors are MONIC — true,
> used, never displayed as the load-bearing condition).”

R2.1's rider (lines 2796–2810, shard 3):

> “In GENIND-6(c)'s coordinate map
> and GENIND-3 step (3)'s fiber sentence, read "triangular" as
> **triangular with UNIT pivots**: in a coordinate order realizing the
> triangular structure, each solved output slot is
> c·(its input slot) + (a function of strictly earlier input slots)
> with pivot c a unit of that slot's truncated ring O/π^w. Unit pivots
> are what license the S2.2 slot bookkeeping: back-substitution solves
> any target slot by slot (input = c⁻¹·(target − earlier-part), c⁻¹
> existing because units of O/π^w invert), so the map is ONTO; and the
> fiber over every target is exactly the free slots (each
> pinned/priced slot solved uniquely, each free slot unconstrained) —
> a target-independent q-power.”

with the supply (R2.2, lines 2812–2840): the RECENTER ledger's pivot is the binomial diagonal `C(j,j) = 1`; SCALE/CONTENT moves are digit-slot relabelings with no pivot; DIVISION ledgers divide by a MONIC factor, pivot = 1; LETTER scalings are units by W12-L1(b)/J-D0 — “So each ledger row's pivot is the literal unit 1 (or a W12-L1(b) unit): MONICITY is the load-bearing condition, now displayed.”

R2.3 adds an explicit **scope honesty** sentence: “the rider displays the condition and its supply; the per-genre ledgers remain compressed per the S4.3 honesty box, and the multi-block hostile targets it names stay named.”

**SUPERSESSION KIND:** `license` — R2 supplies an underived step that the clause's proof consumed silently. It is **not** a `replacement` (no displayed text is withdrawn) and **not** a `wording-rider` (the word “triangular” is re-read, but the operative content added is a *condition with a supply*, not a phrasing substitution). Conflating it with either would misrepresent the DAG: the clause was **incomplete**, not **wrong**.

**TARGETS:** `s1of3.36` and `s1of3.24` (step (3)'s fiber sentence) — R2.0 names both sites explicitly.

**DERIVATION:** verbatim, lines 696–700 (the proof's paragraph (c)):

> “(c) By (a) the map (state digits) → (children's digits at M_l,
> cofactors' digits at certified windows, fiber digits) is triangular
> with exact budget floors; surjectivity with constant q-power fiber
> is the same S2.2 slot bookkeeping as GENIND-3's fiber count, and
> J-D0 lifts the count over the letter twists.”

Justification tags: triangularity = `by XREF` (a); surjectivity + constant fiber = `computation` (S2.2 slot bookkeeping) — **the step R2 identifies as requiring the unit-pivot condition**; letter-blindness = `by XREF LEMMA J-D0`.

**RESOLUTION TRACE:** statement lines 635–646. proof lines 696–700. correction sites: 2779–2852 (ANNEX R R2 in full, shard 3), with its machine leg at 2842–2849.

**TEETH:** R2.3's machine leg G (`genind_annexr_supp.py` @ f5271e4, GREEN): “over ℤ/4, (x+2)·y is bijective in y iff x is odd (a unit) — the toy's collapse — while the monic-pivot form (1+2x)·y is bijective at every x” — a **planted mutant** exercising exactly the failure mode. Instance contact: the committed exhaustive onto-with-constant-fiber enumerations at M6 (`.40`), of which R2.3 says “a non-unit pivot would surface there as a fiber-size split, the signature those runs exclude at their windows”. Disposition: `decorrelated-model audit` for the *finding* (rule 27 — a fresh-context model produced a counterexample shape no battery row could have produced, because the battery only ever ran monic ledgers), plus a planted mutant for the repair.

XREF: `lean/notes/openmath/JD0_PROOF_2026-08-08.md:LEMMA J-D0` — count **4**.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:S2.2` — count **19**; `W12-L1` — count **30**.

---

### EFF.GENIND.s1of3.37  [lemma]

**CANONICAL STATEMENT:** FORM: display (blockquote, LEMMA GENIND-6 clause (d) [READ + MENU/DRAIN COMPOSITION] + the display's closing Conditionality line). verbatim, lines 647–660.

> “**(d) [READ + MENU/DRAIN COMPOSITION]** by (b) the frame's
> continuing read is the tuple of the blocks' own reads: children
> read as their own (μ_l, d, M_l) systems ((IH), history-resolved,
> β3 entry mechanism); stage blocks read as their stage systems per
> (CS-1) = GENHN.A(v) ragged-window-corrected AT the certified
> windows; pieces are Ore-decided. Hence menu = GENIND-0 product of
> the children's (IH) menus × the stage menus ((CS-1)+(CS-2)) ×
> piece censuses; the frame is conservative-undecided iff SOME block
> is (inclusion–exclusion prices it: children's u's exact by (IH)
> member 4, stage drains exact by (CS-EXACT)); at all-decided leaves
> σ = ⊎_l σ_l ⊎_b σ_b ⊎ pieces ((CS-3) at the stages).
> **Conditionality: (a)–(c) are unconditional at GENIND-3's schema
> grade; (d)'s stage clauses consume [GENIND-H] at the stage genres
> — the same conditionality as (CS-1) itself, no more.**”

**CONDITIONALITY:** As displayed — (d)'s stage clauses consume [GENIND-H]. **Two later movements narrow the “no more”:**
1. **The mixed-drain RATE leg is re-conditioned.** The 2026-08-12 round-2 C2-G1 consumer sweep (lines 3714–3721, shard 3) writes: “In GENIND.B Step 4 and the GENIND-6(d) mixed-drain union bound, child terms remain supplied by GENIND-C1; stage terms are supplied by GENIND-C2Q” — and C2Q is conditional on **(CS-1Q), verified per genre**, not on bare (CS-1). The Certification status paragraph (line 3712) is explicit: “The displayed general (CS-1), GENIND-6(a), and GENHN references do not establish (CS-1Q.b) for every embedded or mixed genre … Accordingly, "conditional on (CS-1) only" must be replaced by "conditional on (CS-1Q), verified per genre." A universal discharge for embedded and mixed genres remains obstructed until those affine ledgers are displayed and checked.” **This is the ledger's (CS-1Q) row, HYP.36** (`spec/HYPOTHESIS_LEDGER.md:310–315`): *“WHERE: `GENIND_PROOF_2026-08-08.md`, §C2-G1 L3592–3722. STATEMENT: Both clauses hold: M_G≥e(N−1−H)−Δ_G, and the displayed digit-loss rate follows; the rate does not by itself assert all residual mass is zero. CONSUMED BY: DRAIN-N4/A2. CLASS: named-obligation. PROPOSED DISPOSITION: CARRY — embedded/mixed affine ledgers are not universally checked.”*
2. **The exactness leg's rationale is separated from the bound leg's** by R6.2 (`.14`): the inclusion–exclusion in this clause needs (CS-EXACT) *as an identity*; the bound direction needs only monotonicity + the union bound.

**SUPERSESSION KIND:** the C2-G1 sweep = `replacement` (of the conditionality LABEL on the rate leg: “(CS-1) only” → “(CS-1Q), verified per genre”); R6.2 = `provenance-rider`. Distinct kinds, distinct legs.

**CHAIN (for the mixed-drain rate):** (d)'s displayed “same conditionality as (CS-1) itself, no more” → ANNEX R — r1's GENIND-C2 “conditional on (CS-1) only” → 2026-08-12 GENIND-C2 (Q-normalized) → **2026-08-12 round-2 C2-G1/C2Q: conditional on (CS-1Q), verified per genre — TERMINAL.**

**DERIVATION:** verbatim, lines 701–704 (the proof's paragraph (d)):

> “(d) is the composition of (b)'s read decomposition with the blocks'
> own packages: (IH) at children (their entry data enter the history
> key by the β3 mechanism), [GENIND-H]'s (CS-1)+(CS-2)+(CS-3)+(CS-EXACT)
> at stage blocks, Ore at pieces. ∎”

Justification tags: `by XREF` (b) (`.35`) + `by XREF` (IH) + `by XREF [GENIND-H]`'s four clauses (`.63`–`.66`) + Ore (classical).

**RESOLUTION TRACE:** statement lines 647–660. proof lines 701–704. correction sites: 1010–1013 (S6 Step 2's mixed bucket wiring, `[r2]`), 1023–1025 (Step 3's σ wiring, `[r3, PE3-m4]`), 1043–1047 (Step 4's mixed drain composition, `[r2]`) — all in range and landed; out of range — 2961–3004 (R6, shard 3), 3159–3165 (GENIND-C2(iii)'s mixed composition, shard 3), 3702–3721 (C2Q + the C2-G1 sweep, shard 3).

**TEETH:** M6's PARI read-composition leg (`.40`): “120 child-DECIDED states × 3 disc ≠ 0 lifts — the val-1 block is ONE RAMIFIED QUADRATIC (= σ_child {(2,1)} composed into the ambient) in 360/360, and the val-1/2 stage block has degree 4 on every lift”, plus the ungated drain-honesty diagnostic and the fired counter-prediction tooth T4. Disposition: executable regression on a **mechanism-free** oracle (PARI) — the strongest available guard for a composition claim — but **only at the child side**: `.42`'s honesty box says “Clause (d) is a COMPOSITION statement: its stage-side content is [GENIND-H]'s, not discharged here; its child-side content (σ-composition through the split) is machine-checked mechanism-free (PARI) at M6.” Disposition for the stage side: **`signed vacuity disclosure`** — no GENIND tooth exercises it at any degree.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN.A(v)` — count **6**.

---

### EFF.GENIND.s1of3.38  [instance-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph with a bulleted ledger. verbatim, lines 706–724 and 745–758 (the CHILD, STAGE, FIBRATION and READ-COMPOSITION bullets; the STAGE-SHARP bullet that sits between them is emitted at `.39` — the two quotations are byte-verbatim and their union with `.39` is the whole ledger minus nothing).

> “**The M6 worked ledger (the first-live instance, derived BY HAND
> before any machine run; q arbitrary, both characteristics).** Write
> f = g·u, g = the child block (monic, degree 2, roots of valuation 1),
> u = the stage block (monic, degree 4, roots of valuation 1/2).
> * CHILD: the (factor-generic) scale-then-Hensel extraction at k = 1
>   has D = min_j(v(a_j) + j) = 4 (attained at j = 0 and the vertex
>   j = 2), so the child is a full (2, 1, N−4) cluster state — window
>   M = N − (2·1 + 4·(1/2)) = N − 4, the GENIND-3 formula with the
>   stage block contributing capped slope-mass 4·min(1/2, 1) = 2
>   [r3, PE3-G2: capped = uncapped at M6 — the stage (slope 1/2) is
>   SHALLOWER than the child (slope 1), the agreeing regime].
> * STAGE: the division ledger certifies u's coefficients at the
>   RAGGED windows (u₀, u₁, u₂, u₃) mod (π^{N−1}, π^{N−2}, π^{N−2},
>   π^{N−3}) — e.g. u₃ = a₅ − g₁ with g₁ known mod π^{N−3}; u₀ = a₂ −
>   g₀u₂ − g₁u₁ with every error term of valuation ≥ N−1 by the entry
>   budgets — carrying the stage-entry budgets v(u₀) = 2 with
>   digit₂(u₀) = z², v(u₁) ≥ 2, digit₁(u₂) = −2z (so v(u₂) ≥ 2 in
>   char 2, = 1 at odd q), v(u₃) ≥ 1: the embedded CS4-E(h = 1) stage
>   entry at its sibling-loss-corrected windows.”

> “* FIBRATION: free-digit accounting — locus (q−1)²q^{6N−17}; child
>   space q^{2(N−5)}; stage space q^{4(N−5)+4} per letter pair at the
>   division-ledger windows (q^{4(N−5)+6} at the sharp windows); so
>   the fiber exponent is **9 at the ledger windows, 7 at the sharp
>   windows — both N-independent**: the locus fibers as (q−1)² ×
>   q^{fiber} × [child space] × [stage space], verified at BOTH window
>   sets.
> * READ COMPOSITION at the first window pair: at N = 5 the child
>   window is 1 — the child DRAINS instantly (its entry datum is the
>   whole certified content), so every M6 state at N = 5 is
>   conservative-undecided through the child leg regardless of the
>   stage; at N = 6 the child window is 2 and the child leg splits
>   DRAIN (v(b₀) ≥ 2) / DECIDED σ_child = {(2,1)} (v(b₀) = 1), the
>   latter composing with the stage read as (d) displays.”

**CONDITIONALITY:** A fully displayed instance ledger, exhaustively machine-checked at its first two enumerable windows (`.40`). **The N = 5 child-window-1 read is exactly ANNEX R R3's site (b)** — R3 says so verbatim (lines 2883–2886, shard 3): “the M6 ledger at N = 5 ("the child DRAINS instantly — its entry datum is the whole certified content" is this rider's content verbatim at that instance)”. Before R3 this consumption sat outside S1's stated `N ≥ 2` convention.

**ARITHMETIC AUDIT (compiler-computed; every displayed exponent re-derived):**
* CHILD window: `D = 2·1 + 4·min(1/2, 1) = 2 + 2 = 4` ✓, so `M = N − 4` ✓. §S14 site class 9's own hand-recheck agrees: “hand-recheck min(4, 2+2, 6) = 4” ✓ (the three j-values of `min_j(v(a_j) + j·1)` on the M6 hull: j = 0 gives 4+0, the vertex j = 2 gives 2+2, j = 6 gives 0+6).
* Capped = uncapped at M6: uncapped charges the stage `4·(1/2) = 2` too, since the stage is SHALLOWER ✓ — the agreeing regime, as the `[r3]` bracket says.
* FIBRATION, ledger windows: locus exponent `6N − 17`; child space `2(N−5) = 2N − 10`; stage space `4(N−5) + 4 = 4N − 16`. Fiber exponent = `(6N − 17) − (2N − 10) − (4N − 16) = 6N − 17 − 6N + 26 = 9` ✓ — **N-independent, and exactly the displayed 9.**
* FIBRATION, sharp windows: stage space `4(N−5) + 6 = 4N − 14`. Fiber = `(6N − 17) − (2N − 10) − (4N − 14) = 7` ✓ — **exactly the displayed 7.**
* Cross-check against `.40`'s measured fibres: at q = 2 the predicted fibres are `2⁹ = 512` and `2⁷ = 128` ✓ (the record measures `{512}` and `{128}`); at q = 3, `3⁹ = 19,683` and `3⁷ = 2,187` ✓ (the record measures exactly these).
* Child-space cross-check at (2, 5): `q^{2(N−5)} = 2⁰ = 1` class ✓ — the record's “ONTO 1 × 16”; at (2, 6): `2² = 4` ✓ — the record's “ONTO 4 × 256”.
* Stage-space cross-check at (2, 5): ledger `2^{4·0+4} = 16` ✓ (record: “1 × 16”), sharp `2^{4·0+6} = 64` ✓ (record: “1 × 64”). At (2, 6): ledger `2^{4+4} = 256` ✓, sharp `2^{4+6} = 1024` ✓ — both match the record exactly. At (3, 5): ledger `3⁴ = 81` ✓, sharp `3⁶ = 729` ✓.
* Total consistency at (2,6): locus `2^{6·6−17} = 2^{19} = 524,288`; product `(q−1)² × fiber × child × stage = 1 × 512 × 4 × 256 = 524,288` ✓ **exactly**. And with the sharp windows: `1 × 128 × 4 × 1024 = 524,288` ✓. **Both window sets reproduce the locus exactly** — the “verified at BOTH window sets” claim checks arithmetically, not just by citation.

**DERIVATION:** The ledger IS the derivation (a hand-computed instance of `.34`–`.37`); the division-ledger entries are the triangular division `f/g` of `.34`'s proof.

**RESOLUTION TRACE:** statement lines 706–724 + 745–758. proof lines — displayed in statement. correction sites: `[r3]` in situ 715–716; 2048–2050 (§S14 site class 9's hand-recheck, shard 2); 2883–2886 (R3's site (b), shard 3).

**TEETH:** `genindr2_supp.py` FIBRATION + CERTIFICATION + READ-COMPOSITION legs (`.40`), exhaustive at (2,5) and (2,6), letter-slice at (3,5), sampled at (2,7).

---

### EFF.GENIND.s1of3.39  [lemma]

**CANONICAL STATEMENT:** FORM: bulleted display (the STAGE-SHARP Bezout refinement bullet of the M6 ledger), carrying an `[r3, PE3-m3]` correction. verbatim, lines 725–744.

> “* STAGE, SHARP (the Bezout refinement — surfaced by this leg's own
>   armed tooth, instrument arc disclosed in the machine record): the
>   adjugate solve of u·Δg ≡ δ mod g bounds the factor perturbation by
>   Δg₁, Δg₀ ≥ N−2 because v(r₁) ≥ 2 is FORCED by the stage budget
>   v(u₁) ≥ 2 (r = u mod g, every q, both characteristics); pushing
>   Δg through the division ledger gives the SHARP certified windows
>   **(u₀, u₁, u₂, u₃) mod (π^{N−1}, π^{N−1}, π^{N−2}, π^{N−2})** —
>   one deeper at u₁ and u₃ than the plain division ledger — and
>   sharp as the evidence supports [r3, PE3-m3: the T1 tooth deepens
>   u₀ AND u₂ jointly, so it certifies the DISJUNCTION "u₀ → π^N or
>   u₂ → π^{N−1} is lift-UNSTABLE" — true as worded; PE3's
>   per-coefficient split resolves it: u₂-only-deeper fires everywhere
>   (39/40, 39/40, 40/40 at (2,6)/(2,5)/(3,5)); u₀-only-deeper fires
>   at odd q (40/40 at (3,5)) but is lift-STABLE at p = 2 (0/40 at
>   BOTH (2,6) and (2,5)) — parity-dependent, per the Bezout
>   first-order bound: at p = 2 the char-2 budget v(u₂) ≥ 2 puts every
>   Δu₀ term at ≥ N, while at odd q the term Δg₀·u₂ = (N−2) + 1 = N−1
>   bites. So u₂'s window is sharp at every tested point; u₀'s is
>   sharp at odd q and certified-but-possibly-not-sharp at p = 2 —
>   counts consume only the certified direction].”

**CONDITIONALITY:** **Sharpness is claimed only in the certified DIRECTION, and only at M6.** `.42`'s honesty box: “At M6 the sharpness question is SETTLED both ways (the sharp windows displayed above, the one-deeper tooth firing); at GENERAL mixed genres only the certified DIRECTION is claimed — counts consume only that direction.” The `[r3, PE3-m3]` layer replaces a joint claim by a per-coefficient one and discloses that **u₀'s window at p = 2 is certified but possibly not sharp**. The Bezout input `v(r₁) ≥ 2` is genre-local: `.42`(ii) names “the Bezout refinement's budget input v(r₁) ≥ 2 at other genres (here it follows from v(u₁) ≥ 2 + v(u₂g₁) ≥ 2; a genre where the stage budgets are weaker would lose the refinement, not the ledger)”.

**SUPERSESSION KIND:** `[r3, PE3-m3]` = `counter re-reading` — the tooth's evidence is re-read from a joint disjunction to a per-coefficient split, with the sharpness *claim* narrowed accordingly. (It is not a `replacement`: the displayed sharp windows are unchanged.)

**ARITHMETIC AUDIT (compiler-computed):** the odd-q term the bracket cites, `Δg₀·u₂` at valuation `(N−2) + 1 = N−1` ✓ (Δg₀ ≥ N−2 from the adjugate bound, v(u₂) = 1 at odd q) — so a perturbation reaches depth N−1 and u₀'s window `π^{N−1}` is sharp ✓. At p = 2 the char-2 budget gives v(u₂) ≥ 2, so the same term sits at `(N−2) + 2 = N` ≥ N ✓ — no perturbation inside the window, i.e. lift-STABLE ✓, exactly the measured 0/40. The measured tooth counts are consistent with the split: u₂-only fires 39/40, 39/40, 40/40 and u₀-only fires 0/40, 0/40, 40/40 at (2,6)/(2,5)/(3,5) — and the joint T1 tooth reported at `.40` fires “38/40 at (2,6) and 40/40 at (3,5)”, which is ≤ the per-coefficient maxima ✓ (38 ≤ 39 at (2,6); 40 = 40 at (3,5)) — **consistent, and the (2,5) joint figure is not displayed at `.40`**, recorded as a display gap (§8, defect 3).

**DERIVATION:** Displayed in the statement (adjugate solve + budget input + push-through). Justification tags: `computation` (Bezout/adjugate first-order bound) + `by XREF` the stage budgets of `.38`'s STAGE bullet.

**RESOLUTION TRACE:** statement lines 725–744. proof lines — displayed. correction sites: `[r3, PE3-m3]` in situ 734–744; §S13's PE3-m3 item at 1903–1909 (shard 2).

**TEETH:** T1 (sharpness) of `genindr2_supp.py` — “one window deeper than the sharp set is exact-factor-UNSTABLE on 38/40 states at (2,6) and 40/40 at (3,5)”, a **planted mutant that fired**, plus PE3's per-coefficient split as **foreign-note evidence**. Disposition: planted mutant, fired, **with a disclosed parity-dependent non-sharpness at p = 2** (`disclosed non-repair`: the u₀-only guard never fires at p = 2, and the note says so rather than claiming sharpness).

---
### EFF.GENIND.s1of3.40  [run-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph with a bulleted result ledger. verbatim, lines 760–798 (the INSTRUMENT ARC bullet that closes the record is emitted at `.41`; the two quotations are byte-verbatim and their union is the whole record minus nothing).

> “**Machine record (genindr2_supp.py — ADDITIVE leg; sealed runner
> md5-pinned e7ca150b, imported read-only; sealed artifacts
> byte-frozen). GREEN: 2,128,163 checks, 0 violations, 357.7 s.**
> * FIBRATION, exhaustive at every enumerable window of the genre:
>   (q, N) = (2, 5): 8,192 states ONTO 1 × 16 (coarse windows, fibers
>   {512} = q⁹) AND 1 × 64 (sharp windows, fibers {128} = q⁷);
>   (2, 6): 524,288 ONTO 4 × 256 / fibers {512} AND 4 × 1024 / {128};
>   (3, 5) full (z, w) = (1,1) letter slice: 1,594,323 ONTO 1 × 81 /
>   fibers {19,683} = q⁹ AND 1 × 729 / {2,187} = q⁷ — the odd-q pins
>   live (digit₁(u₂) = −2z ≠ 0, v(u₂) = 1). [r3, PE3-m1] Coverage as
>   actually run: at (2,5) and (2,6) every member classifies to the M6
>   key with the child side present (reader ON); the (3,6,5)
>   letter-slice block ran reader-OFF (`do_read=False`) — checked
>   there: child side present on every member + every stage cofactor
>   hits the entry budgets exactly, NOT the full key classification
>   (the sealed sentence "every member classifies to the M6 key"
>   overstated the q = 3 instrument). The q = 3 reader-ON hole is
>   closed at the HARDER genre by PE3's fresh leg: 300 M7T members at
>   (3,6) with the reader ON, all CS at the stable key
>   (genind_pe3_fresh FR-A).
> * CERTIFICATION (exact-factor lift-stability: factors Hensel-lifted
>   to each independent random lift's FULL precision, truncations
>   compared — see the instrument arc below): stable at BOTH displayed
>   window sets, 80 × 6 lifts (2,5), 80 × 6 (2,6), 60 × 5 (3,5),
>   300 × 4 at the sampled beyond-enumeration window (2,7) (+ 400
>   sampled (2,7) states all classifying to the M6 key).
> * READ COMPOSITION, mechanism-free (PARI factorpadic at p = 2,
>   N = 6): 120 child-DECIDED states × 3 disc ≠ 0 lifts — the val-1
>   block is ONE RAMIFIED QUADRATIC (= σ_child {(2,1)} composed into
>   the ambient) in 360/360, and the val-1/2 stage block has degree 4
>   on every lift; drain-honesty diagnostic (ungated): all 8 sampled
>   child-DRAIN states realize ≥ 2 distinct val-1 σ-shapes across
>   lifts ({two linears} and {ramified quadratic}) — the conservative
>   drain is genuinely undecided data.
> * TEETH (all fired): T1 sharpness — one window deeper than the
>   sharp set is exact-factor-UNSTABLE on 38/40 states at (2,6) and
>   40/40 at (3,5); T2 — corrupting the vertex pin digit₂(a₂) exits
>   the genre signature 20/20; T4 — the counter-prediction "σ_child
>   unramified (1,2)" refuted by every PARI sample (360/360).”

**CONDITIONALITY:** An ADDITIVE leg, not part of the sealed battery — the sealed runner and artifacts are byte-frozen and this leg imports the runner read-only. The `[r3, PE3-m1]` layer **corrects the record's own coverage claim in place**, quoting the overstatement: the q = 3 block ran reader-OFF, so the sealed sentence “every member classifies to the M6 key” overstated the instrument. **STALE-SELF-DESCRIPTION check:** none — the correction landed in place, and the hole it discloses is closed by an external leg (PE3 FR-A), cited not claimed.

**SUPERSESSION KIND:** `[r3, PE3-m1]` = `counter re-reading` (the coverage claim is re-scoped to what the instrument actually ran; no number moves).

**ARITHMETIC AUDIT (compiler-computed, cross-checking every row against `.33`'s locus law and `.38`'s fibre exponents):**
* (2,5): law `(q−1)²q^{6N−17}` = `1·2^{13}` = **8,192** ✓ matches. Product check, ledger windows: `1 (child) × 16 (stage) × 512 (fiber)` = 8,192 ✓. Sharp: `1 × 64 × 128` = 8,192 ✓.
* (2,6): law `1·2^{19}` = **524,288** ✓. Ledger: `4 × 256 × 512` = 524,288 ✓. Sharp: `4 × 1024 × 128` = 524,288 ✓.
* (3,5) letter slice: law/(q−1)² = `3^{13}` = **1,594,323** ✓. Ledger: `1 × 81 × 19,683` = 1,594,323 ✓. Sharp: `1 × 729 × 2,187` = 1,594,323 ✓.
* Fibre values against `.38`'s exponents: `q⁹` at q = 2 → 512 ✓, at q = 3 → 19,683 ✓; `q⁷` → 128 ✓ / 2,187 ✓.
* PARI leg: `120 states × 3 lifts = 360` ✓ = the reported 360/360, twice (read composition and tooth T4).
* Certification lift counts: 80×6 + 80×6 + 60×5 + 300×4 = 480 + 480 + 300 + 1,200 = **2,460** lift comparisons.
* **Total-check attempt on “2,128,163 checks”:** the three exhaustive fibration rows alone sum to 8,192 + 524,288 + 1,594,323 = **2,126,803**; adding the 2,460 certification comparisons gives 2,129,263 — which OVERSHOOTS the reported 2,128,163 by 1,100, so the reported total is *not* fibration + certification as counted here. The residual `2,128,163 − 2,126,803 = 1,360` is the number of non-fibration checks the leg counts (360 PARI + 40 + 40 + 20 + … ), and the certification comparisons are evidently counted differently from 80×6-style products. **The compiler cannot reconstruct the total from the displayed rows; recorded as a disclosed non-reconstruction (§8, defect 4), not as a discrepancy** — the artifact `genindr2_supp_results.json` is the authority and is byte-frozen.
* §S12's independent restatement of the same run (lines 1819–1826, shard 2) reports the identical headline “2,128,163 checks, 0 violations, 357.7 s” and the identical row structure ✓ — internally consistent across the two displays.

**DERIVATION:** Not a mathematical unit; an executed instrument's result.

**RESOLUTION TRACE:** statement lines 760–798. correction sites: `[r3, PE3-m1]` in situ 769–779; §S13's PE3-m1 item at 1894–1898 (shard 2); §S12's Machine paragraph at 1819–1828 (shard 2).

**TEETH:** this unit IS the teeth row for `.33`–`.39`; its own three teeth T1/T2/T4 all fired. **Disposition, per-tooth:** T1 planted mutant, fired (with `.39`'s disclosed p = 2 non-sharpness at u₀); T2 planted mutant (pin corruption), fired 20/20; T4 planted counter-prediction, refuted 360/360. **Disclosed instrument hole:** the q = 3 block ran reader-OFF (`disclosed non-repair` at the instrument level), closed only by foreign evidence.

**PIN VERIFICATION:** `verification/openmath/genindr2_supp.py`, `genindr2_supp_output.txt`, `genindr2_supp_results.json` all EXIST ✓ (md5 triple 7335fc16/63b7413a/6c93f29c per §S15's enumerated freeze); sealed runner md5 pin `e7ca150b` is the note's own repeatedly re-verified value.

---

### EFF.GENIND.s1of3.41  [instrument-record]

**CANONICAL STATEMENT:** FORM: bulleted display (the INSTRUMENT ARC bullet closing the machine record). verbatim, lines 799–812.

> “* INSTRUMENT ARC (disclosed; full narrative in the leg's
>   docstring): run 1 of this leg went RED on ITS OWN TOOTH — the
>   tooth "u₃ one deeper than the division ledger must be unstable"
>   did not fire (sole RED item; every mathematical check green).
>   Diagnosis: (i) the division-ledger u₃ window is certified but NOT
>   sharp (the Bezout refinement above — a real mathematical finding
>   the tooth surfaced); (ii) run 1's stability test measured
>   ALGORITHM DETERMINISM, not certification (a truncating extraction
>   reproduces its own zero-filled deep digits on every lift). The
>   test was redesigned to compare exact factors of independent lifts
>   (this version), under which the sharp windows are stable and the
>   one-deeper tooth fires. Corpus lesson: certified-window claims
>   must be tested against exact factors of INDEPENDENT lifts, never
>   against a truncating extraction's own reproducibility.”

**CONDITIONALITY:** A disclosure of an instrument redesign between runs. **The redesign is not a re-run of a failed check but a change of what the check measures** — the honest reading is that run 1's stability test was *invalid*, not that it disagreed. The corpus lesson is normative and is re-asserted as a hostile target at `.42`(iv).

**DERIVATION:** Not a mathematical unit. Its one mathematical by-product — “the division-ledger u₃ window is certified but NOT sharp” — is `.39`'s Bezout refinement, which the tooth surfaced.

**RESOLUTION TRACE:** statement lines 799–812. correction sites: none; re-asserted at 843 (`.42`(iv)) and at §S12's Machine paragraph (lines 1826–1828, shard 2).

**TEETH:** the *subject* of this record is a tooth that failed to fire and the diagnosis of why. Disposition: **`stale self-description`** in the strict sense of rule 20 — run 1's self-description (“stability tested”) was falsified by the instrument's own result, and the note preserves that history rather than deleting it. This is the shard's clearest instance of a tooth doing work by NOT firing.

---

### EFF.GENIND.s1of3.42  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (the GENIND-6 honesty box) with an `[r3, PE3-m2]` correction bracket. verbatim, lines 814–843.

> “**Honesty box (the GENIND-6 grade).** (a)–(c) are proved at exactly
> GENIND-3's schema grade — the per-genre certified-window ledgers are
> mechanical affine computations, compressed here as GENIND-3
> compresses its per-route ledgers (S4.1 honesty note; HEX3-BOX-2
> pricing), with the M6 instance's ledger displayed IN FULL and
> machine-checked exhaustively at its first two visible windows.
> Clause (d) is a COMPOSITION statement: its stage-side content is
> [GENIND-H]'s, not discharged here; its child-side content
> (σ-composition through the split) is machine-checked mechanism-free
> (PARI) at M6. At M6 the sharpness question is SETTLED both ways (the
> sharp windows displayed above, the one-deeper tooth firing); at
> GENERAL mixed genres only the certified DIRECTION is claimed —
> counts consume only that direction. A hostile pass should attack:
> (i) the certified-window ledger at genres with ≥ 2 stage blocks
> (not live at n ≤ 7: two composite blocks consume ≥ 8 abscissas,
> S5.1) or a stage block STEEPER than a child [r3, PE3-m2: the sealed
> line said "first live n ≥ 7 arrangements — no machine instance
> here"; the stage-steeper case is live already at n = 6 —
> window-deep (first visible N ≥ 9), not degree-deep — and is now
> machine-realized by PE3's fresh leg: genre SS6 at (q, 6, 1), hull
> (0,8)–(4,2)–(6,0), stage [0,4] at slope 3/2 STEEPER than the child
> [4,6] at slope 1, 250 + 120 members at (2,9)/(3,9), all CS, child
> extraction at the capped window N−6, stage budgets exact, certified
> windows lift-stable (genind_pe3_fresh FR-C); this note's own machine
> leg still carries no instance]; (ii) the Bezout refinement's budget
> input v(r₁) ≥ 2 at other genres (here it follows from v(u₁) ≥ 2 +
> v(u₂g₁) ≥ 2; a genre where the stage budgets are weaker would lose
> the refinement, not the ledger); (iii) the odd-q pins (the battery's
> q = 3 slice is the only odd-q machine point of this leg); (iv) the
> instrument lesson in the machine record (stability vs determinism).”

**CONDITIONALITY:** The grade of record for `.34`–`.39`. Its `[r3, PE3-m2]` layer corrects the sealed scope claim in place and discloses that **this note's own machine leg carries no stage-steeper instance** — a `disclosed non-repair` preserved verbatim.

**SUPERSESSION KIND:** `[r3, PE3-m2]` = `counter re-reading` (a liveness inventory is recounted: degree-deep → window-deep), plus `inventory completion` (the machine realization is added from a foreign leg). §S14 claim group **C7** re-audits and KEEPS it.

**ARITHMETIC AUDIT (compiler-computed, on the SS6 datum):** hull (0,8)–(4,2)–(6,0): left side [0,4] drop 8−2 = 6 over length 4 → slope **3/2** ✓ (so e = 2, and the composite block spans 4 abscissas ✓); right side [4,6] drop 2 over length 2 → slope **1** ✓ (the (2,1) child). Stage slope 3/2 > child slope 1 ✓ — genuinely stage-steeper. Entry height by Gauss additivity: `4·(3/2) + 2·1 = 6 + 2 = 8` ✓, so first visible at N ≥ 9 ✓ — matching the bracket and §S14 C7's evidence line (“SS6 hull v(a₀) = 8 ⟹ N ≥ 9”). Child extraction window: `D = μ·k + Σ deg·min(s, k) = 2·1 + 4·min(3/2, 1) = 2 + 4 = 6` ✓ → capped window `N − 6` ✓, matching §S14 site class 10's own hand-recheck (“hand-recheck D = 2·1 + 4·min(3/2, 1) = 6 (uncapped would say 8)”); uncapped would charge `2·1 + 4·(3/2) = 8` ✓. **A genuine disagreeing-regime instance** — capped 6 vs uncapped 8. Two-stage-block budget: `2 × 4 = 8` abscissas ✓ ⟹ m ≥ 8, i.e. degree-deep as claimed ✓.

**DERIVATION:** Not a proof; a grade declaration with four named hostile targets.

**RESOLUTION TRACE:** statement lines 814–843. correction sites: `[r3, PE3-m2]` in situ 829–838; §S13's PE3-m2 item at 1899–1902 (shard 2); §S14 site class 10 at 2051–2053 and claim group C7 at 2103–2106 (shard 2).

**TEETH:** **PROOF-ONLY** for the compressed per-genre ledgers; the note's own coverage-hole sentence for the row is “the per-genre certified-window ledgers are mechanical affine computations, compressed here”. Target (i) is covered only by **foreign-note evidence** (PE3 FR-C), and the box says so: “this note's own machine leg still carries no instance” — `disclosed non-repair`. Target (iii) records the single odd-q machine point as the whole odd-q coverage of the leg — `signed vacuity disclosure` in the odd-characteristic direction.

---

### EFF.GENIND.s1of3.43  [theorem]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph closing §S5.1. verbatim, lines 879–887.

> “**The criterion in one line: composite stages exist at degree n ⟺
> n ≥ 4 (⟺ some stage can carry ≥ 4 keys).** The charge's candidate
> criterion "n has a nontrivial factorization d·e with e ≥ 2" is
> REFUTED: n = 5 is prime yet composite-bearing — the key degree of a
> composite stage divides no invariant of n; it consumes 4 of the n
> abscissa units and leaves the rest to split off. (Machine: GT-CRIT —
> n = 3 rows show ZERO CS events; n = 4, 5 rows show CS events exactly
> at the S5.3 genre grammar, with two flagship laws per degree checked
> both directions.)”

**CONDITIONALITY:** The ⟺ is at DEGREE level throughout — which is what ANNEX R R5 later pins explicitly for GENIND.A(IV) (`.11`). Nothing here claims the stage-level parse, so R5 leaves this display unedited; recorded so a merge does not attach R5's rider to it by association.

**DERIVATION:** §S5.1's *Necessity* and *Sufficiency*, quoted in full at `.11`'s DERIVATION.

**RESOLUTION TRACE:** statement lines 879–887. proof lines 849–877. correction sites: none. (R5 targets `.11`, not this unit — verified by R5.1's own naming: it quotes “conversely m ≥ 4 realizes CS with positive locus at every q”, the GENIND.A(IV) wording, not this paragraph's.)

**TEETH:** GT-CRIT [SAME], both directions (§S11 P-8 “0/22”), tooth GT-T-CRIT at its preregistered count 4. **The refutation half** (n = 5 prime yet composite-bearing) is machine-witnessed by the n = 5 CS events at (·,2,4) and (·,2,5) — §S11 P-3 records V1E2(1) = 12,288 at (·,2,5,n5) — and by the negative control (·,3,3,n5) “ZERO CS keys (the visibility floor)”. Executable regression, both directions.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:[W12-H]` — count **17** (the “never consulted [W12-H]” claim of the necessity proof; re-audited and KEPT at §S14 C10).

---

### EFF.GENIND.s1of3.44  [scope-record]

**CANONICAL STATEMENT:** FORM: bulleted display (§S5.2's simple-slice ingredient list, first five bullets; the sixth — drainage — is emitted at `.45`, and the two quotations' union is the whole list minus nothing). verbatim, lines 891–905.

> “Call a history SIMPLE if no CS event occurs along it. The simple
> slice of the degree-n problem is generated by exactly the S2–S4
> machinery over the W-12.A leaves — every ingredient PROVED:
> * the leaves: THEOREM W-12.A (all degrees, order 1) [pin];
> * the α-aggregation: LEMMA GENIND-2 (bracket b_{m,d});
> * the β-fibrations: LEMMA GENIND-3 over the LOWER-degree simple
>   slices (strong induction; at n ≤ 3 the simple slice is everything
>   and the induction grounds in W-11/HEX3/HMENU3);
> * (A1)-form: LEMMA GENIND-0 + the affine exponent bookkeeping
>   (window variables enter the exponents with the strictly positive
>   integer coefficients displayed in GENIND-2/3);
> * (A0) on simple leaves: Ore at the terminal frame + window coherence
>   transporting the certificate (W-12 S2.3 + GENIND-2(a), exactly
>   HM3.C's S5.2 argument at general n);”

**CONDITIONALITY:** “every ingredient PROVED” is true of the five bullets listed here at the grade each ingredient carries (`.10`/`.26` price the β-fibration schema grade). **The (A0) bullet's supplier moved:** HMENU3's ANNEX A corrected HM3.C's (A0) quantifier to the disc ≠ 0 form, and §S16 row 3 records the consumption as SURVIVING *because* “ANNEX A corrects the quantifier exactly TO the form consumed here — this note's citations quantify over disc ≠ 0 lifts only”. W-12's r5 likewise “re-derived the (A0) clause at the disc ≠ 0 form” (§S16 PE6 trace (i)).

**DERIVATION:** Not a proof; an ingredient inventory, each item pointing at its own unit.

**RESOLUTION TRACE:** statement lines 891–905. correction sites: 1505–1517 (§S9.3's HMENU3 re-pin, shard 2), 2356 (§S16 row 3, shard 2), 2425–2427 (PE6 trace (i), shard 2).

**TEETH:** the ingredients' own rows (`.17`–`.24`). Nothing new.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:S2.3` — count **35** (upper bound: the string matches §-anchors and prose alike).
XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:HM3.C` — count **15**.

---

### EFF.GENIND.s1of3.45  [lemma]

**CANONICAL STATEMENT:** FORM: bulleted display (§S5.2's drainage bullet — the first-step recursion and the vanishing clause). verbatim, lines 906–914.

> “* drainage of the simple slice: the first-step recursion
>   u_{m,d}(N) = Q^{(m−1)(N−1)} + Σ_k (Q−1)Q^{k·c(m)}·u_{m,d}(N−mk) +
>   Σ_{β-genres} (route prefactor)·[children: at least one drains,
>   inclusion–exclusion over the child systems' u's and totals] — every
>   term supplied by GENIND-2/3 + IH, telescoping by GENIND-2(b)
>   exactly as HEX3 S5.2 (the α-part's telescoped coefficient is
>   b_{m,d}); vanishing: u/Q^{m(N−1)} → 0 by induction (head Q^{−(N−1)};
>   α-terms geometric; β-terms lose at least one child's full mass by
>   the IH bound — each contributes O(poly(N)·Q^{−(N−c)}) relative
>   mass).”

**CONDITIONALITY:** **This is the single most heavily repaired sentence in the shard, and the vanishing clause as displayed is NOT self-supporting.** ANNEX R R1.0 (lines 2582–2604, shard 3) quotes this exact bullet as the site of CODEX F3, the heaviest CONFIRMED GAP:

> “**R1.0 The defect, exactly.** S5.2's vanishing bullet consumes a rate:
> [the bullet quoted] … while THEOREM GENIND.B's displayed package supplies only
> “P(k) := {… + exact-complement (A2)}”
> and W-12's (A2) is a bare o(1) (r(N)/q^{nN} → 0 — Codex's instance:
> 1/log(M+1) is o(1) with no exponential rate). Codex F3's two halves,
> both confirmed at adjudication: (i) "exact" supplies a VALUE, not a
> rate — the displayed fourth member does not carry the O(poly·Q^{−·})
> the bullet consumes; (ii) a capped child window M_l = N − D_l can
> stay BOUNDED while the genre depth D_l grows with N, and there the
> child's own M_l → ∞ vanishing cannot be applied — those β-terms
> vanish only through the route prefactor, and no bounded-vs-growing
> split was displayed.”

The repair supplies both halves from outside the range: the **(A2-RATE)** species pin on P(k) (`.13`), **ANNEX-LEMMA GENIND-C1** (the β-term estimate with the explicit GROWING/BOUNDED regime split), and **ANNEX-THEOREM GENIND.C′** (the quantitative vanishing clause, proved by lexicographic induction on (degree, window)). R1.4 states the substitution at this site verbatim: “Step 4's simple part consumes GENIND.C′ verbatim in place of the bare bullet”. The window-1 boundary `u(1) = 1` that the m = 2 telescope needs is ANNEX R R3's site (c) (`.07`).

**SUPERSESSION KIND:** `license` for the rate (an underived quantitative step is supplied) + `inventory completion` for the bounded/growing split (a case the display omitted). **Not a `replacement`:** the recursion itself is untouched and the bullet's α/head legs “were never in question” (R1.4).

**CHAIN:** the sealed bullet → R1's (A2-RATE) + GENIND-C1 + GENIND.C′ → `[ar1]` GAP-1 (the closure is split: simple part by C′, CS-drain part by GENIND-C2) → 2026-08-12 GENIND-C2 (Q-normalized) → **2026-08-12 round-2 C2Q under (CS-1Q), verified per genre — TERMINAL** for the CS-drain half; **GENIND.C′ — TERMINAL** for the simple half (unconditional).

**DERIVATION:** As displayed, the recursion's terms are supplied by GENIND-2/3 + IH and telescoped by GENIND-2(b) “exactly as HEX3 S5.2”. The vanishing *rate* is not derived here; it is derived at GENIND.C′ (shard 3).

**RESOLUTION TRACE:** statement lines 906–914. proof lines — none in range for the rate half (this is the defect). correction sites: 2580–2777 (ANNEX R R1 in full, shard 3), 2886–2889 (R3's site (c), shard 3), 3117–3226 and 3298–3872 (the GENIND-C2 chain, shard 3).

**TEETH:** GT-BDRAIN [SAME] (§S11 P-4 “0/4”) and GT-RECUR [SAME] (§S11 P-6 “GT-RECUR 0/8 — the α-drain self-similarity … exact at every realized k”) guard the **recursion**; **nothing in the sealed battery guards the vanishing RATE**, which is why the gap was invisible to eight hostile passes and surfaced only at a decorrelated-model read. Disposition: `decorrelated-model audit` (rule 27) — the note's own framing at R1.0 is that GENIND-BOX-4 “priced the bookkeeping compression; the finding is sharper: a consumed HYPOTHESIS component absent from the display.” The rate's later machine support is ANNEX R — r1's own two-commit leg (`genind_annexr1_checks.py`, 144 preregistered checks, 143 GREEN + 1 flagged), homed in shard 3.

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:S5.1` — count **9** (the HEX3 §S5 telescoping family; see the NEAR-MISS below for the exact section cited).
**NEAR-MISS (rule 15):** `HEX3 S5.2` — designation absent as written (fixed-string count **0** in `HEX3_PROOF_2026-08-08.md`). The referent is HEX3's own drainage/telescoping section; the addressable neighbouring designations that DO verify are `R(M)` (count **21**) and `THEOREM HEX3.B` (count **8**), the rate HEX3 displays. Carried descriptively.
**NEAR-MISS (rule 15):** `u₃(M)` — GENIND's name for HEX3's n = 3 conservative complement; fixed-string count **0** in `HEX3_PROOF_2026-08-08.md`, which writes `u(q,N)` (count **1**, at `:437`) and `u(M)` (at `:389`). GENIND-local notation, not a supplier designation; carried descriptively.

---

### EFF.GENIND.s1of3.46  [theorem]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (THEOREM GENIND.C) + its GRADE sentence. verbatim, lines 916–927.

> “So: **THEOREM GENIND.C (the simple-stage layer).** For every n, the
> simple slice carries a finite (A1)-admissible menu with exact counts,
> (A0), and an exactly-recursed conservative drain, unconditionally on
> [GENIND-H] (conditional only on the S0 supplier pins). For n ≤ 3 the
> simple slice is the whole problem and GENIND.C reproduces the proved
> packages P(2), P(3). For n ≥ 4 the complement of the simple slice —
> the CS strata — has EXACTLY KNOWN entry mass (the opening loci are
> order-1 shapes priced by W-12.A: e.g. Σ_h (q−1)q^{4N−5h−3} at the
> quartic e-first genre) but positive density: it can NOT be absorbed
> into (A2) by bounds, which is precisely why [GENIND-H] is
> load-bearing and not a technicality. GRADE: proved modulo the
> GENIND-3 ledger honesty note; machine-checked at n = 4, 5 as S10.”

**CONDITIONALITY:** “unconditionally on [GENIND-H]” — the strongest unconditional claim in the note, and the one GENIND-BOX-1 names as the reduction's unconditional content at n ≥ 4. **Its drainage member inherits `.45`'s gap and repair**: the *quantitative* form is ANNEX-THEOREM GENIND.C′ (lines 2728–2752, shard 3), which is where “exactly-recursed conservative drain” acquires a rate. C′'s own statement is scoped to the simple slice, matching this theorem exactly:

> “**R1.3 ANNEX-THEOREM GENIND.C′ (the vanishing clause, quantitative
> form — the induction closed).** For the simple slice of each (m, d):
> there are (K, B, c) with u^{simple}_{m,d}(N)/Q^{m(N−1)} ≤
> K·N^B·Q^{−(N−c)} at every window N ≥ 1.”

The `[ar1 2026-08-10, MINOR-1]` layer displays the c-choice `c := c′ + 1` at source and certifies no circularity. Note the `N ≥ 1` in C′ — it consumes R3's window-1 rider (`.07`).

**SUPERSESSION KIND:** `license` (C′ supplies the quantitative form the displayed theorem asserts qualitatively). Not a `replacement`.

**DERIVATION:** The five ingredients of `.44` plus the recursion of `.45`; the “positive density” claim is the CS entry-mass computation cited to W-12.A and instantiated at `.48`.

**ARITHMETIC AUDIT:** the displayed CS entry mass `Σ_h (q−1)q^{4N−5h−3}` is `.48`'s CS4-E(h) law summed over h; relative to the per-centre total `q^{4N}` it is `Σ_h (q−1)q^{−5h−3}`, an h-geometric series with N-independent sum — i.e. **positive density, N-independent** ✓, exactly the claim. (Constant order in N, not vanishing: `(q−1)q^{−3}·(1−q^{−5})^{−1}` at the unrestricted sum.) This is the arithmetic behind “it can NOT be absorbed into (A2) by bounds”.

**RESOLUTION TRACE:** statement lines 916–927. proof lines 891–914 (§S5.2's ingredient list + recursion). correction sites: 2728–2752 (GENIND.C′, shard 3), 2662–2675 (`[ar1]` GAP-1's split, shard 3), 3159–3182 (GENIND-C2's role for the CS complement, shard 3).

**TEETH:** GT-BDRAIN + GT-RECUR + GT-BETA at n = 4, 5 (the “machine-checked at n = 4, 5 as S10” clause). **PROOF-ONLY above n = 5**, and PROOF-ONLY for the rate at every n until C′ (which carries its own machine legs A–C in shard 3: the m = 2 closed forms solved symbolically at N = 2..14 and matched to W-11's R(M) at M = 1..14).

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:THEOREM W-12.A` — count **8**.

---
### EFF.GENIND.s1of3.47  [convention]

**CANONICAL STATEMENT:** FORM: inline paragraph opening §S5.3. verbatim, lines 931–934.

> “Per center, window N, d = 1; z-letters ∈ F_q^×; ψ = irreducible
> quadratics over F_q (#ψ = q(q−1)/2). Derivations: direct S2.2 slot
> counts (this session; the two n = 4 laws are W-12 S2.5's and its
> (2²) sibling).”

**CONDITIONALITY:** Fixes the normalization for every law in `.48`–`.51` — **per center, d = 1**. A reader who compares these laus to a whole-space count without dividing by the level-0 centre census will mis-scale them; the note flags the same hazard nowhere else in range.

**ARITHMETIC AUDIT (compiler-computed):** #{monic irreducible quadratics over F_q} = (q² − q)/2 = q(q−1)/2 ✓.

**DERIVATION:** Definitional; the derivations of the laws themselves are S2.2 slot counts, one of which (CS4-E) is cited to W-12 S2.5 as PROVED at the w12 seal.

**RESOLUTION TRACE:** statement lines 931–934. correction sites: none.

**TEETH:** NONE — a normalization convention.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:S2.5` — count **9**; `S2.2` — count **19**.

---

### EFF.GENIND.s1of3.48  [lemma]

**CANONICAL STATEMENT:** FORM: bulleted display (the n = 4 e-first genre law), carrying a landed `[r1, PE1-M3]` floor bracket. verbatim, lines 936–944.

> “**n = 4 (the whole polygon is the side):**
> * **CS4-E(h)** [e-first: e = 2, ψ linear, μ = 2; = QRT-G2(h;(1²))]:
>   slope h/2, h odd, residual (y−z)²: (q−1)·q^{4N−5h−3}, VISIBILITY
>   FLOOR 2h ≤ N−1 [r1, PE1-M3: displayed like every sibling law —
>   v(a₀) = 2h must sit below the window or DRAIN fires first; at
>   (N, h) = (2, 1) the unfloored display would return q−1 against a
>   true locus of 0; the sealed runner already gates on it
>   (`while 2*h <= N-1`), so this is display-only]. [pin: proved
>   at the w12 seal; QSCOUT22's GENRE E entry.]”

**CONDITIONALITY:** PROVED at the W-12 seal (cited, not re-proved here); the floor is landed at `[r1]`. Not touched by any later round — R4 (`.49`) explicitly leaves it alone: “the E-law's existing floor sentence at S5.3 stands unchanged”.

**ARITHMETIC AUDIT (compiler-computed):** entry height on the whole-polygon side of length 4 at slope h/2 is `4·(h/2) = 2h` ✓ = v(a₀); DRAIN fires at `v(a₀) ≥ N`, so inhabited iff `2h ≤ N−1` ✓. At (N, h) = (2, 1) the unfloored law gives `(q−1)q^{8−5−3} = (q−1)q⁰ = q−1` ✓ against a true locus of 0 ✓ — the bracket's own check. Cross-check against §S11 P-3's scored spots: at (·,2,6,n4) the law with h = 1 gives `1·2^{24−5−3} = 2^{16} = 65,536` ✓ = the reported `E4(1) = 65,536`; at (·,3,4,n4), `2·3^{16−5−3} = 2·3^{8} = 13,122` ✓ = the reported `E4(1) = 13,122`; at (·,5,3,n4), `4·5^{12−5−3} = 4·5^{4} = 2,500` ✓ = the reported `E4(1) = 2,500`. **All three never-measured spots reproduce from the displayed law.**

**DERIVATION:** Cited: “[pin: proved at the w12 seal]”, i.e. W-12 §S2.5's QRT-G2 stratum law. Not re-derived in this note. The slot-count route is `.68`'s LEMMA GENIND-4, whose free-digit total independently recomputes the same exponent (`4N − 5h − 3`) as a no-over/undercount check.

**RESOLUTION TRACE:** statement lines 936–944. proof lines — external (W-12 S2.5); the internal cross-derivation is at 1243–1245 (GENIND-4's free-digit total). correction sites: `[r1, PE1-M3]` in situ 939–943 (landed).

**TEETH:** GT-DEPTH0 [SAME, both directions] (§S11 P-3, the three E4(1) spots above, exact) · GT-CRIT (the genre appears exactly where the grammar predicts, and is ABSENT below its floor) · tooth GT-T-CS at its preregistered count 12 (“every n = 4 row”). Executable regressions.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:QRT-G2` — count **10**; `S2.5` — count **9**.
XREF: `lean/notes/openmath/QSCOUT22_2026-08-08.md:GENRE E` — count **2**.

---

### EFF.GENIND.s1of3.49  [lemma]

**CANONICAL STATEMENT:** FORM: bulleted display (the n = 4 f-first genre law). verbatim, lines 945–947.

> “* **CS4-F(k)** [f-first: e = 1, residual ψ², deg ψ = 2]: integer
>   slope k, heights (4k, 3k, 2k, k), L = 4:
>   (q(q−1)/2)·q^{4N−10k−4}. [QSCOUT22's GENRE F entry.]”

**CONDITIONALITY:** **The display is INCOMPLETE as written and is corrected by ANNEX R R4** (CODEX F5, CONFIRMED, regraded MINOR display) — the visibility floor `4k ≤ N−1` is missing. R4.0 quotes the finding and R4.1 supplies the floor; both are quoted in full at `.11`'s CONDITIONALITY, which is R4's other target. R4.2 pins the committed-number impact to zero (lines 2917–2925, shard 3):

> “**R4.2 Committed numbers unaffected — the gate lines cited.** The
> sealed runner gates its genre-F predictor on exactly the floor:
> `while 4 * k <= N - 1:` at **genind_checks.py lines 709 and 869**
> (md5-pinned e7ca150b, consulted read-only). Machine leg H
> (@ f5271e4, GREEN): both gate lines verified verbatim in the pinned
> file; (2,2,1) gated to 0 where the bare display says 2^{−6};
> (2,5,1) above the floor with law 2^{20−10−4} = 2⁶ = 64.
> Display-only, the exact defect species as PE1-M3 — the E-law's
> existing floor sentence at S5.3 stands unchanged.”

**SUPERSESSION KIND:** `wording-rider` — “Read BOTH displays … WITH the floor”, an explicit addition to the displayed law's side conditions. Deliberately NOT `replacement`: no exponent moves, and no committed number moves.

**TARGETS:** `s1of3.49` and `s1of3.11`.

**ARITHMETIC AUDIT (compiler-computed):** heights (4k, 3k, 2k, k) on a length-4 side at integer slope k ✓ (the supporting line drops by k per abscissa), so `v(a₀) = 4k` ✓ and the floor is `4k ≤ N−1` ✓. Unfloored at (q, N, k) = (2, 2, 1): `(2·1/2)·2^{8−10−4} = 1·2^{−6} = 2^{−6}` ✓ — **a non-integer**, the sharpest possible signature of a missing floor. Above the floor at (2, 5, 1): `1·2^{20−10−4} = 2⁶ = 64` ✓ matching R4.2. Cross-check against §S11 P-3: at (·,2,6,n4) with k = 1 the law gives `1·2^{24−10−4} = 2^{10} = 1,024` ✓ = the reported `F4(1) = 1,024`. At (·,3,4,n4) the note reports `F4 ABSENT (4k ≤ 3 impossible)` — recomputed: `4·1 = 4 > N−1 = 3` ✓ **absent**, and this is precisely the floor R4 says was undisplayed, applied correctly by the runner. **The runner and the display disagreed; the runner was right.**
Row-total cross-check: §S11 P-3 reports “row CS total 66,560 = E4+F4” at (·,2,6,n4); recomputed `65,536 + 1,024 = 66,560` ✓, and §S10's cost probe independently reported “66,560 CS” at (Fqt,2,6,n4) ✓ — three independent agreements.

**DERIVATION:** Direct S2.2 slot count (per `.47`); not displayed. Sibling to `.48`, whose exponent is independently re-derived at `.68`.

**RESOLUTION TRACE:** statement lines 945–947. proof lines — none displayed. correction sites: 2897–2925 (ANNEX R R4 in full, shard 3).

**TEETH:** GT-DEPTH0 (the F4(1) spot, exact; and correctly ABSENT where the floor excludes it) · GT-CRIT · R4.2's machine leg H (`genind_annexr_supp.py` @ f5271e4, GREEN) — a **source-code gate verification**, an unusual and strong disposition: the tooth reads the pinned runner's two gate lines verbatim and confirms the runner implements the floor the display omitted. **PIN VERIFICATION:** `genind_checks.py` EXISTS ✓; the cited gate lines are `709` and `869` — verified present in the pinned file by R4.2's own leg, not re-verified here (the file is md5-pinned and byte-frozen).

XREF: `lean/notes/openmath/QSCOUT22_2026-08-08.md:GENRE F` — count **1**.

---

### EFF.GENIND.s1of3.50  [lemma]

**CANONICAL STATEMENT:** FORM: bulleted display (the n = 5 flagship, vertex-at-1 genre). verbatim, lines 949–958.

> “**n = 5 (the side has length 4; the fifth root splits off — the
> criterion's "consumes 4, leaves the rest" made flesh):**
> * **CS5-V1E2(h)**: vertex at 1, side (1, 2h)–(5, 0), h odd, e = 2,
>   residual (y−z)² on lattice {1, 3, 5}; v(b₀) strictly above the
>   extended side (≥ (5h+1)/2) and NOT window-zero (else DRAIN fires
>   first): (q−1)·q^{4-coordinate exponent}·(q^{N−(5h+1)/2} − 1) with
>   4-coordinate exponent = (N−1−2h) + (N−(3h+1)/2) + (N−1−h) +
>   (N−(h+1)/2) = 4N − 2 − 3h − (4h+2)/2 = 4N − 5h − 3, i.e.
>   **(q−1)·q^{4N−5h−3}·(q^{N−(5h+1)/2} − 1)** — the CS4-E law times
>   the b₀ headroom factor (the split root's fiber).”

**CONDITIONALITY:** Derived here (this session), not cited. Its structure — CS4-E's law × a headroom factor — is exactly the criterion's “consumes 4, leaves the rest”. ANNEX-LEMMA GENIND-C2's displayed checks (shard 3) re-use this law's entry mass and record the same structural reading: “the fifth root's headroom is a decided-piece fiber; it does not weaken the stage-drain estimate”.

**ARITHMETIC AUDIT (compiler-computed, re-deriving the displayed 4-coordinate exponent):** the four summands are (N−1−2h) + (N−(3h+1)/2) + (N−1−h) + (N−(h+1)/2). Sum = 4N − 2 − 3h − [(3h+1) + (h+1)]/2 = 4N − 2 − 3h − (4h+2)/2 = 4N − 2 − 3h − 2h − 1 = **4N − 5h − 3** ✓ — the displayed value, recomputed fresh. (The note's own intermediate display “4N − 2 − 3h − (4h+2)/2” checks ✓.) Cross-check against §S11 P-3: at (·,2,5,n5) with h = 1 the full law gives `1·2^{20−5−3}·(2^{5−3} − 1) = 2^{12}·3 = 4,096·3 = 12,288` ✓ = the reported `V1E2(1) = 12,288`. At (·,3,3,n5) the note reports “NO CS key at all (V1E2 headroom = 0)”; recomputed: `N − (5h+1)/2 = 3 − 3 = 0`, so the headroom factor is `q⁰ − 1 = 0` ✓ **zero locus** — the criterion's fine structure reproduces exactly.

**DERIVATION:** Displayed in the statement (a direct S2.2 slot count over the lattice {1,3,5} plus the b₀ headroom factor). Justification tags: `computation` throughout; the “NOT window-zero” side condition is the DRAIN-first rule of `.08`.

**RESOLUTION TRACE:** statement lines 949–958. proof lines — displayed. correction sites: none. Consumed out of range at 3189–3193 and 3526–3541 (GENIND-C2's CS5-V1E2 check, shard 3).

**TEETH:** GT-DEPTH0 (the V1E2(1) spot, exact at (·,2,5,n5)) · GT-CRIT (the zero-headroom absence at (·,3,3,n5)) · tooth GT-T-CRIT at its preregistered count 4, whose scope is exactly “the n = 5 rows with CS visible: (2,4),(2,5) × 2 kinds; (3,3) correctly excluded”. Executable regression, both directions.

---

### EFF.GENIND.s1of3.51  [lemma]

**CANONICAL STATEMENT:** FORM: bulleted display (the n = 5 flagship, vertex-at-4 genre) with a PREDICTED-ABSENT disposition. verbatim, lines 959–968.

> “* **CS5-V4E2(v₄, h)**: vertex at 4, left side (0, v₄+2h)–(4, v₄),
>   h odd, e = 2, residual (y−z)² (pins at abscissae 0, 2), right side
>   (4, v₄)–(5, 0) a split simple root (letter at the vertex):
>   **(q−1)²·q^{5N−5v₄−5h−4}**, v₄ ≥ 1, VERTEX CONDITION h ≥ 2v₄+1
>   (hull convexity at (4, v₄): the left drop (v₀−v₄)/4 must exceed the
>   right drop v₄ — caught by the battery's smoke: at h < 2v₄+1 the
>   same digits read as a single e = 5 decided side), visibility
>   v₀ = v₄+2h ≤ N−1: first visible at N = 8 — beyond this roster's
>   windows, so machine-checked as PREDICTED-ABSENT (its law is
>   derivation-only here).”

**CONDITIONALITY:** **Derivation-only; the law is never machine-exercised** — the genre's first visible window (N = 8) is beyond the sealed roster (max N = 6). What IS machine-checked is its *absence* where predicted. The VERTEX CONDITION itself is a MATH-side correction that the pre-seal smoke forced: §S10's disclosure (lines 1643–1648, shard 2) — “smoke run 1 RED with exactly one violation — the predictor listed V4E2(1,1) at (Zp,2,4,n5), refuted by the trace: the hull convexity at the (4, v₄) vertex forces h ≥ 2v₄+1, a MATH-side correction folded into S5.3”.

**ARITHMETIC AUDIT (compiler-computed):** vertex condition — the left side drops `(v₄+2h) − v₄ = 2h` over 4 abscissas, slope `h/2`; the right side drops `v₄` over 1 abscissa, slope `v₄`. Lower-hull convexity demands the LEFT slope exceed the right: `h/2 > v₄` ⟺ `h > 2v₄` ⟺ (h odd, v₄ integer) `h ≥ 2v₄+1` ✓ — the displayed condition, re-derived. First visibility: minimize `v₀ = v₄ + 2h` subject to `v₄ ≥ 1`, `h ≥ 2v₄+1`, h odd → `v₄ = 1, h = 3` gives `v₀ = 7`, so `N ≥ 8` ✓. §S14 claim group **C8** states the same computation and KEEPS it: “v₀ = v₄ + 2h ≥ 1 + 2·(2v₄+1)|_{v₄=1} = 7 ⟹ N ≥ 8”. **Compiler note on that evidence line:** as written it reads `1 + 2·3 = 7` ✓, correct. Absence corroboration: §S11 P-3 reports “V4E2 ABSENT (the vertex condition)” at (·,2,5,n5) ✓ — at N = 5 the minimum entry height 7 exceeds N−1 = 4 ✓.

**DERIVATION:** Displayed in the statement (slot count + hull convexity). Not independently machine-corroborated.

**RESOLUTION TRACE:** statement lines 959–968. proof lines — displayed. correction sites: none after the pre-seal fold; the smoke disclosure is at 1643–1648 (shard 2), the scored absence at 1722–1723 (shard 2), the re-audit at 2107–2109 (§S14 C8, shard 2).

**TEETH:** **`signed vacuity disclosure`** — the law is checked only in the negative direction (PREDICTED-ABSENT), and the note says so in the display itself (“its law is derivation-only here”). The positive direction is unexercised at every window of every roster in this note. Also a **`disclosed non-repair`** in the pre-seal history: the smoke's RED was a genuine predictor defect, repaired in the mathematics before the seal.

---

### EFF.GENIND.s1of3.52  [scope-record]

**CANONICAL STATEMENT:** FORM: bulleted display (the non-flagship n = 5 genres) with a grammar-acceptance fence. verbatim, lines 969–976.

> “* Non-flagship (classified, laws not preregistered): CS5-V1E1-(2²)
>   (side (1, 4k)–(5, 0), integer slope, residual ψ², first visible
>   N = 7 — the b₀ headroom 5k+1 ≤ N−1), CS5-V4E1-(2²), CS5-FULL-(2²1)
>   (full side, residual ψ²·(y−w), N ≥ 6) — all beyond this roster's
>   windows, enumerated in the criterion grammar (GT-CRIT accepts
>   exactly the grammar, so an unlisted CS genre on any row is a
>   violation, and a listed-but-early genre appearing below its
>   visibility floor is one too).”

**CONDITIONALITY:** Classified but unpriced — “laws not preregistered”, all beyond the roster. The **fence** in the parenthesis is the load-bearing part for the DAG: GT-CRIT is a *grammar acceptor*, so completeness of `.48`–`.52`'s genre list is testable in both directions on every row.

**ARITHMETIC AUDIT (compiler-computed):** CS5-V1E1-(2²) — side (1,4k)–(5,0) has length 4 at integer slope k, so `v(a₀) ≥ 4k + 1` from the vertex at abscissa 1 and the headroom condition is `5k+1 ≤ N−1` as displayed; at k = 1 that is `6 ≤ N−1`, i.e. **N ≥ 7** ✓ — matching the display and §S14 claim group C9 (“TRUE, KEPT (headroom 5k+1 ≤ N−1 at k = 1)”). CS5-FULL-(2²1): a full side of length 5 carrying `ψ²·(y−w)` needs `deg = 2·2 + 1 = 5` ✓ and enters at integer slope ≥ 1 with `v(a₀) = 5`, so **N ≥ 6** ✓.

**DERIVATION:** Classification only; no laws derived.

**RESOLUTION TRACE:** statement lines 969–976. correction sites: none. Re-audit at 2110–2111 (§S14 C9, shard 2).

**TEETH:** GT-CRIT as a grammar acceptor (§S11 P-8: “no genre outside the S5.3 grammar”), plus the P-11 falsifier “a GT-CRIT event outside the grammar refutes S5.1/S5.3's completeness”. Disposition: executable regression **in the completeness direction only** — the three genres' own laws are `signed vacuity disclosure` (never priced, never measured).

---

### EFF.GENIND.s1of3.53  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph closing §S5.3. verbatim, lines 978–981.

> “**Deeper CS openings** (behind α/β prefixes) inherit these tables at
> sheared windows through GENIND-2/3 — self-similarly, no new genre
> (machine: the full-history classifier tallies CS events at all
> depths; every one must parse in the grammar).”

**CONDITIONALITY:** A self-similarity claim: no *new* genre appears at depth. Machine-guarded at all depths on the sealed roster only.

**DERIVATION:** The shear is GENIND-2(a)'s (`.21`); the β-inheritance is GENIND-3's (`.24`). No separate proof displayed.

**RESOLUTION TRACE:** statement lines 978–981. correction sites: none.

**TEETH:** GT-CRIT at all depths — §S11 P-8: “every n = 4/5 CS event (all depths) obeys μ ≥ 2, e·γ ≥ 2, 4 ≤ e·μ·γ ≤ m_frame; no genre outside the S5.3 grammar”. Executable regression. **Coverage limit:** depth coverage is bounded by the roster's windows (max N = 6 on full sweeps), plus the constructed deep legs (“the first n = 4 depth-2 α at N = 9”).

---

### EFF.GENIND.s1of3.54  [theorem]

**CANONICAL STATEMENT:** FORM: italic-headed paragraph (§S6's Step 1). verbatim, lines 985–996.

> “Fix n; assume (IH) [P(k), history-resolved, for k < n] and
> [GENIND-H(n)].
>
> *Step 1 (level 0).* By W12-S2.1 the degree-n problem is the disjoint
> union over level-0 configurations of products of cluster systems
> (m_i, d_i) and simple branches. Configurations with every m_i·d_i < n
> are products of strictly-lower-degree data: (IH) supplies each
> factor's package; LEMMA GENIND-0 multiplies the menus, W-12.A's
> level-0 censuses supply C₀(q); drains compose by "some factor
> drains". The only configurations not covered by (IH) are the full
> clusters m·d = n, m ≥ 2 (and the trivial separable ones, decided at
> level 0).”

**CONDITIONALITY:** Under (IH) + [GENIND-H(n)] as stated. Inherits `.30`'s OPEN-CALL 3 (GENIND-0's closure claim is stated for the pre-r4 (A1)).

**DERIVATION:** Displayed. Justification tags: `by XREF W12-S2.1` (the level-0 product decomposition) + `by XREF LEMMA GENIND-0` (`.30`) + `by XREF THEOREM W-12.A` (level-0 censuses) + `by XREF` (IH).

**RESOLUTION TRACE:** statement lines 985–996. correction sites: none.

**TEETH:** Indirect — the level-0 product structure is exercised by every GT-BETA reconstruction and by the constructed BFULL legs, but no row targets Step 1 as such.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:W12-S2.1` — count **9**; `THEOREM W-12.A` — count **8**.

---

### EFF.GENIND.s1of3.55  [theorem]

**CANONICAL STATEMENT:** FORM: italic-headed paragraph (§S6's Step 2), carrying a landed `[r2, PE2-G1]` mixed-bucket insertion. verbatim, lines 998–1018.

> “*Step 2 (the full cluster: menu).* In the (m, d, N) system, LEMMA
> GENIND-1 partitions every state; the recursion on histories
> terminates because α strictly reduces the window (GENIND-2), β
> strictly reduces every child's degree (GENIND-1(iii) + GENIND-3, then
> (IH) at the children — history-resolved, so children entering at
> their own refine loci are consumable, the β3 mechanism), and CS
> events exit into [GENIND-H]'s stages, whose (CS-1)+(CS-2) supply the
> stage's own resolved menu and (CS-3) its σ/(A0). Aggregating: the
> α-prefixes by GENIND-2(b)'s bracket (a finite relabeling per family,
> HM3-BOX-5's pedantry inherited); the β-genres by GENIND-0 products of
> the children's finite (A1) menus; the CS stages by [GENIND-H]; the
> MIXED CS genres (a stage with coexisting β-children on the same
> polygon, first live at n = 6) by LEMMA GENIND-6(c)(d) [r2, PE2-G1]:
> GENIND-0 products of the stage menus ((CS-1)+(CS-2)) WITH the
> children's (IH) menus and the piece censuses — the bucket the r1
> text's two-bucket sentence did not license. Every
> family's data is a single q-polynomial expression by construction
> (slot counts + censuses; J-D0's frame) — q- and characteristic-
> uniform. Disjointness: the deterministic read keys partition
> (GENIND-1(i)). This is (hMenu-n) = (A1) + the history-resolved form
> of P(n).”

**CONDITIONALITY:** Under (IH) + [GENIND-H(n)]. **Termination** rests on three separate descent facts (window strictly reduces at α; child degree strictly reduces at β; CS exits into a lower-complexity stage) — and the third is exactly what the 2026-08-12 round-2 C2-G2 repair later has to make well-founded for the *rate* induction (ANNEX-LEMMA GENIND-C2D + the lexicographic measure, lines 3723–3793, shard 3). The menu-side termination here is not re-opened by that repair; recorded so a merge does not conflate the two descents.

**DERIVATION:** Displayed. Justification tags: partition `by XREF GENIND-1` (`.17`); termination `by XREF GENIND-2`/`GENIND-1(iii)`+`GENIND-3` + `by XREF` (IH); aggregation `by XREF GENIND-2(b)` (`.22`), `by XREF GENIND-0` (`.30`), `by XREF [GENIND-H]`, `by XREF GENIND-6(c)(d)` (`.36`, `.37`); uniformity `by XREF LEMMA J-D0`; disjointness `by XREF GENIND-1(i)`.

**RESOLUTION TRACE:** statement lines 998–1018. correction sites: `[r2]` in situ 1010–1013 (landed); §S12's PE2-G1 item at 1780–1794 (shard 2); §S14 site class 12 at 2056–2058 (shard 2, “cite M_l / GENIND-6 abstractly, inheriting whatever S4.1/S4.3 display; every inherited display now CAPPED ✓”).

**TEETH:** GT-PART + GT-DEPTH0 + GT-ALPHA + GT-BETA jointly; no row targets the aggregation as such. **PROOF-ONLY** for the aggregation step; the note supplies no coverage sentence specific to it.

XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:HM3-BOX-5` — count **4**.
XREF: `lean/notes/openmath/JD0_PROOF_2026-08-08.md:LEMMA J-D0` — count **4**.

---

### EFF.GENIND.s1of3.56  [theorem]

**CANONICAL STATEMENT:** FORM: italic-headed paragraph (§S6's Step 3), carrying a landed `[r3, PE3-m4]` wiring insertion. verbatim, lines 1020–1025.

> “*Step 3 (A0).* Order-1 leaves: Ore at the terminal frame + window
> coherence (S5.2 bullet). CS leaves: (CS-3) = (H-e). Products: σ and
> certificates compose branchwise (W12-S2.1, GENIND-3); at MIXED
> CS+child frames the σ-composition routes through LEMMA GENIND-6(d)
> (σ = ⊎_l σ_l ⊎_b σ_b ⊎ pieces) [r3, PE3-m4: the wiring Steps 2 and 4
> already carry, added here].”

**CONDITIONALITY:** The CS-leaf half is `(CS-3) = (H-e)`, **OPEN** ((OB-c), `.72`). The order-1 half is unconditional given W-12 S2.3 + GENIND-2(a), and consumes HM3.C's (A0) argument at the **disc ≠ 0** quantifier — the form HMENU3's ANNEX A later corrected TO (§S16 row 3).

**SUPERSESSION KIND:** `[r3, PE3-m4]` = `inventory completion` (a wiring already carried at Steps 2 and 4 is added at Step 3; nothing changes mathematically, and the bracket says so).

**DERIVATION:** Displayed. Justification tags: `by XREF W-12 S2.3` + `by XREF GENIND-2(a)` (window coherence) + Ore (classical) + `by XREF [W12-H](H-e)` + `by XREF W12-S2.1`/`GENIND-3` (branchwise composition) + `by XREF GENIND-6(d)` (`.37`).

**RESOLUTION TRACE:** statement lines 1020–1025. correction sites: `[r3]` in situ 1024–1025 (landed); §S13's PE3-m4 item at 1910–1913 (shard 2).

**TEETH:** GT-ORACLE [IND] — §S11 P-9: “GT-ORACLE 0 bad / 73,676 checks — PARI (nfinit/idealprimedec) confirms the σ multiset of EVERY decided member on all three rows (3,264 + 5,670 + 27,904 = 36,838 members: the FIRST independent σ verification of quartic and quintic cluster reads in this corpus, wild p = 2 strata included), 0 disc-0 lifts.” **ARITHMETIC AUDIT:** 3,264 + 5,670 + 27,904 = **36,838** ✓ (the note's own sum checks). The relation between 36,838 members and 73,676 checks is exactly ×2 ✓ (two checks per member). Disposition: executable regression on a **mechanism-free decorrelated oracle** — the strongest row in the shard's teeth table. **Coverage limit:** the oracle leg covers order-1 decided leaves only; **`(CS-3)` is exercised by nothing**, at any degree.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:S2.3` — count **35** (upper bound).

---
### EFF.GENIND.s1of3.57  [theorem]

**CANONICAL STATEMENT:** FORM: italic-headed paragraph (§S6's Step 4, the inventory and routing half; the `[r1, PE1-G1]` record that physically continues it is emitted at `.58` and the discharge geography at `.59` — the three quotations are byte-verbatim and their union is the whole Step minus nothing). verbatim, lines 1027–1049.

> “*Step 4 (A2).* r(N) = conservative drains + window-boundary (tail)
> families + the CS stages' RAGGED BANDS [r1, PE1-G2: (CS-1)'s
> ragged-window correction produces per-genre N-boundary slot
> families — see S7.1's corrected (CS-1)] + CS-internal residues. The
> simple part: GENIND.C's recursion telescopes and vanishes; the
> boundary families route through (A2) exactly as W-12 S3.4 [r2]
> displays at n = 2, 3 (their masses are the transported
> SPLIT-TAIL-type aggregates, N-dependent counts, vanishing after
> normalization); the ragged bands route through (A2) the same way
> [r1, PE1-G2: finitely many per genre, N-boundary slot strings — at
> the (2,2)-E stage the last ~⌊h/2⌋ window slots of S7.3's parity-
> ragged window; their confinement below every consulted height at
> the discharged genres is LEMMA GENHN-3 (GENHN @ 850e77e)]; the
> CS-internal part: (CS-1)+(CS-2) resolve each stage into its own
> decided menu + drain, with the stage drains vanishing by the same
> telescoping run inside the stage ([GENIND-H]'s content); at the
> MIXED CS genres the drain composes across the blocks by LEMMA
> GENIND-6(d) [r2, PE2-G1] — the frame is undecided iff some block is,
> inclusion–exclusion over (children's u's: exact by (IH) member 4) ×
> (stage drains: exact by (CS-EXACT)), the composition the r1
> inventory had no lemma for. Summing:
> r(N)/q^{nN} → 0, with the same exact-complement sharpening HM3.C
> S5.3 achieved at n = 3.”

**CONDITIONALITY:** Four live movements, all from outside the range:
1. **The simple part's rate.** R1.4 (lines 2772–2773, shard 3): “Step 4's simple part consumes GENIND.C′ verbatim in place of the bare bullet” — i.e. the “telescopes and vanishes” clause is discharged by the quantitative ANNEX-THEOREM GENIND.C′, not by `.45`'s displayed bullet (`.45`, `.46`).
2. **The CS-internal part's rate.** R1.4's closing rider (lines 2773–2777, shard 3): “the CS legs keep their [GENIND-H]/(CS-EXACT) conditionality unchanged [ar1 2026-08-10: for menu + exactness — the CS legs' RATE is now supplied separately by ANNEX-LEMMA GENIND-C2 under (CS-1) alone (the r1 append below); (CS-EXACT) supplies exactness, not a rate, per R6.2's identity-vs-bound separation]” — and that “(CS-1) alone” is itself upgraded to **“(CS-1Q), verified per genre”** by the 2026-08-12 round-2 C2-G1 consumer sweep (lines 3714–3721, shard 3), which names this Step: “In GENIND.B Step 4 and the GENIND-6(d) mixed-drain union bound, child terms remain supplied by GENIND-C1; stage terms are supplied by GENIND-C2Q.”
3. **The mixed inclusion–exclusion's strength.** R6.2 separates identity from bound (`.14`, `.37`).
4. **The GENHN cite inventory.** PE7-m2 (lines 2488–2498, shard 2) names “the GENHN S6.3 display cite at S6 Step 4 (L1094)” as a consumed site beyond §S9.3's four-clause list — one of the three sites that make the GENHN surface seven, not four. LEMMA GENHN-3's own band-exit clause was then conditionalized by GENHN erratum E1, and the survival screen records (lines 3064–3067, shard 3): “LEMMA GENHN-3, consumed at (CS-1) + S6 Step 4 (ragged-band CONFINEMENT at the discharged genres): E1 conditionalizes the f₁ ≥ 2 band-EXIT phrasing; the discharged genres consumed here are f₁ = 1 — SURVIVES.”

**SUPERSESSION KIND:** (1) and (2) are `license` (a consumed rate is supplied) followed by `replacement` of the conditionality label at (2); (3) is `provenance-rider`; (4) is `inventory completion`. **Four kinds on one Step; flattening them would misstate three of the four.**

**DERIVATION:** Displayed. Justification tags: simple part `by XREF GENIND.C`/GENIND.C′; boundary families `by XREF W-12 S3.4`; ragged bands `by XREF LEMMA GENHN-3`; CS-internal `by XREF [GENIND-H]`'s (CS-1)+(CS-2); mixed drain `by XREF GENIND-6(d)`; the sharpening `by XREF HM3.C S5.3`.

**RESOLUTION TRACE:** statement lines 1027–1049. proof lines — the Step is itself the proof of P(n)'s fourth member. correction sites: `[r1, PE1-G2]`, `[r2]`, `[r2, PE2-G1]` in situ (landed); out of range — 2754–2777 (R1.4, shard 3), 2986–2997 (R6.2, shard 3), 3064–3074 (the GENHN screen, shard 3), 3714–3721 (the C2-G1 sweep, shard 3), 2488–2498 (PE7-m2, shard 2).

**TEETH:** GT-BDRAIN + GT-RECUR at n = 4, 5 (the first-step recursion, exact — “stronger at those degrees than the bound it feeds”, GENIND-BOX-4). **Nothing guards the ragged-band routing or the CS-internal drainage at any degree in this note's own battery.** Disposition: `signed vacuity disclosure` for those two legs; the CS-drain rate's only machine support is ANNEX R — r1's leg (shard 3), which is n = 4-only and walks the PINNED GENH4 battery.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:LEMMA GENHN-3` — count **3**; `S6.3` — count **3**.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:S3.4` — count **11**.
XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:HM3.C` — count **15**.

---

### EFF.GENIND.s1of3.58  [changes-record]

**CANONICAL STATEMENT:** FORM: bracketed rider inside §S6 Step 4 (the `[r1, PE1-G1]` record — WHY P(n) needs the exact form). verbatim, lines 1049–1062.

> “**[r1, PE1-G1: the sealed text hedged this
> last clause "wherever the stage laws are exact" — a hedge the box's
> three sealed members nowhere secured. The hedge is now the box's own
> (CS-EXACT) clause, so given [GENIND-H(n)] the sharpening holds
> unconditionally. WHY P(n) needs the exact form and not a bound: the
> exact-complement (A2) member is consumed at HIGHER degrees — a
> degree-n′ > n β-fracture into a degree-n child runs S5.2's
> inclusion–exclusion over the child systems' u's and totals, which is
> an identity only if the children's u's are exact closed forms; with
> bound-only stage laws the first-step recursion at n′ degrades to an
> inequality and P(n′)'s fourth member fails (the verifier's
> n = 8-through-a-degree-4-child scenario), i.e. the induction would
> not propagate the very member it assumed. Discharge geography,
> honestly …”

*(The record continues into the discharge geography, emitted at `.59`.)*

**CONDITIONALITY:** The record's two load-bearing sentences **STAND** — R6.2 says so explicitly (lines 2987–2989, shard 3): “The record's load-bearing sentences STAND ("an identity only if those u's are exact" — true; P(n)'s fourth member fails under bound-only inputs — true, the member is an equality).” What R6.2 corrects is the *inference the PE8 acceptance report drew from it*, not this record: R6.1's notice (lines 2972–2984, shard 3) refutes “PE8 §4.1's necessity rationale” — “∂/∂u₁(u₁T₂ + T₁u₂ − u₁u₂) = T₂ − u₂ ≥ 0 identically on the admissible domain u₂ ≤ T₂” — and states “The defect sits in the acceptance report's elaboration of WHY (CS-EXACT) is needed, not in this note's accepted text.”

**SUPERSESSION KIND:** `provenance-rider` (the reason is separated into two consumers of different strengths; the clause and its conclusion are untouched). **This is the shard's cleanest example of why rule 18's kinds are not interchangeable:** a merge that recorded R6 as a `replacement` on this record would imply (CS-EXACT)'s necessity was withdrawn, which is the opposite of what R6.2 concludes.

**ARITHMETIC AUDIT (compiler-computed, on the monotonicity R6.1 asserts):** at r = 2 the composed undecided mass is `G = T₁T₂ − (T₁−u₁)(T₂−u₂) = u₁T₂ + T₁u₂ − u₁u₂`; `∂G/∂u₁ = T₂ − u₂ ≥ 0` on `u₂ ≤ T₂` ✓. General r: `G = Π_j T_j − Π_j(T_j − u_j)`, so `∂G/∂u_i = Π_{j≠i}(T_j − u_j) ≥ 0` ✓. Union-bound dominance: `Σ_i u_i Π_{j≠i} T_j ≥ G` since expanding `Π T − Π(T−u)` by inclusion–exclusion gives Σ_i u_i Π_{j≠i}T_j minus nonnegative cross terms ✓. **The refuted report sentence — “not monotone in u₁ once u₂ > T₂ − u₂” — is false because `∂G/∂u₁ = T₂ − u₂` never changes sign on the admissible domain** ✓.

**DERIVATION:** The record IS an argument (the n′-propagation scenario). Justification tags: `computation` (the inclusion–exclusion identity requires exact inputs) + a named verifier scenario (“the verifier's n = 8-through-a-degree-4-child scenario”).

**RESOLUTION TRACE:** statement lines 1049–1062. correction sites: 2961–3004 (ANNEX R R6 in full, shard 3).

**TEETH:** R6.3's machine leg F (symbolic, GREEN) with the **decorrelation record**: “the fold's scaffold P-4 PREREGISTERED the same arithmetic before the run and its sympy leg confirmed it — two decorrelated models, same kill”. Disposition: `accepted-with-decorrelation-supplied` + `decorrelated-model audit` for the finding itself (a false rationale inside an *acceptance report* — a document class no battery row inspects).

---

### EFF.GENIND.s1of3.59  [changes-record]

**CANONICAL STATEMENT:** FORM: bracketed rider continuing §S6 Step 4's `[r1]` record (the discharge geography, the timing disclosure and the STANDING RULE), with nested `[r2, PE2-G2 + PE2-m1]` and `[r3, PE3-G1]` layers. verbatim, lines 1062–1100.

> “Discharge geography,
> honestly [r2, PE2-G2 + PE2-m1: re-pinned, split into its two halves,
> and the timing race disclosed] [r3, PE3-G1: re-pinned again at
> GENH4's ACTUAL repair HEAD r3 = 4b0d946 (note-only; the dv0 = N
> trichotomy restated with pairwise-disjoint antecedents, the W-12.A
> mnemonic scoped, the stack box refreshed — display-only for
> everything consumed here, PE3's full-diff verification; the UND
> count GENH4.B rests on is identical across fd35416 → 4b0d946);
> GENH4's arc since: passPE4 CLEAN @ e15308d, 0C + 0G + 0m + 2
> remarks, its 2-clean count 1/2 — no adjudicated unrepaired finding
> at the r3 pin]: at n = 4 the clause is supplied DE
> FACTO by GENH4 @ r3 (4b0d946; laws as at fd35416 note + 5279a11
> supp leg) — the DRAIN
> half by THEOREM GENH4.B (= Q22-L3), one exact closed form per
> (center, entry, history) stratum (a single q-power off the boundary
> band; a TWO-term q-power sum at genre-F even N, GENH4-CAP(F)'s own
> display — the r1 gloss "ONE exact q-power" overstated the
> granularity), and the MENU half by THEOREM GENH4.A (= Q22-L1) +
> GENH4-1F (per GENH4.D's own package: CS-1 = GENIND-4 + GENH4-1F +
> GENH4-2/-3/-4), with the census factor in its r2-corrected
> comp-weighted form (q^{comp}−1 per RAM/2SIDED pin, NOT Q−1 at
> genre-F boundary-band pins). TIMING DISCLOSURE: the r1 text cited
> GENH4 @ dff23f8 and named only GENH4.B — but the clause needs both
> halves, and at that pin GENH4.A's census display carried a
> ledger-adjudicated CRITICAL (GENH4 passPE2 2618e9b at 23:01:28,
> folded 0089f9b at 23:07:17, BEFORE GENIND r1 landed at 23:18:53 =
> 66200f2; the cure fd35416 landed at 23:19:42, 49 seconds AFTER r1 —
> uncitable at r1, but the adjudicated defect was on the ledger and
> went undisclosed). Standing rule applied from this repair on: pin
> suppliers at their repair HEAD and disclose any adjudicated,
> not-yet-repaired findings at the pin — AS A COMMIT-TIME ACTION
> against the git log, not a composition-time recollection [r3,
> PE3-G1: the r2 text violated the rule in the very repair that
> adopted it — see S12/S13]. GENHN S6.3 (@ 850e77e)
> displays the same shape at general genres (its header phrase "one
> exact q-power per stratum" carries the same genre-F granularity
> caveat when consumed here: read it as one exact FINITE q-power SUM
> per stratum); at general n, (CS-EXACT) remains a HYPOTHESIS on the
> box, which is exactly what [GENIND-H] is for — no claim of general
> discharge is made.]**”

**CONDITIONALITY:** **The n = 4 de facto discharge is a CITATION, and its pin has moved four times since.** The chain, all out of range: §S9.3's GENH4 bullet (lines 1551–1599, shard 2) carries `[r3]` (re-pin to 4b0d946), `[r4]` (GENH4 ACCEPTED 2/2 @ 11dbd23 + annex baf05ed), `[r5]` (the Codex GENH4 ratification adjudicated **CHALLENGE** @ 5c8d2fd; ANNEX R applied @ b10a5a7), `[r6]` (annex-pass #1 NOT CLEAN @ a8dec16 with GAP-1 machine-refuted; **ANNEX R2** @ 760d20f withdrew the refuted legs). §S16 row 7's verdict: “**SURVIVES.** GAP-1 sat on a clause this note never cites; the W-12.D-consumed supply clause (b) was re-derived CLEAN at annex-pass #1 … GENH4.B re-read at the accepted body — `git show 4b0d946` display byte-identical to worktree HEAD — and re-matched to Step 4”. **NEW PIN = accepted body 4b0d946 (byte-frozen) + annex stack through R2 @ 760d20f; the annex-stack count is 0/2 with its pass #2 in flight, not landed.**

**SUPERSESSION KIND:** each re-pin is `as-of scoping`; the `[r2]` split into two halves is `inventory completion`; the granularity correction (“ONE exact q-power” → finite q-power sum) is `wording-rider`; the STANDING RULE adoption is a `license` on the note's own record protocol. **Four kinds inside one bracket chain.**

**CHAIN:** r1's pin `dff23f8` (GENH4.B only, undisclosed adjudicated CRITICAL at the pin) → `[r2]` pin `fd35416 + 5279a11`, both halves named, 49-second race disclosed → `[r3]` pin `4b0d946` (GENH4's actual repair HEAD; the r2 pin-check sentence was FALSE) → `[r4]` GENH4 ACCEPTED 2/2 → `[r5]` Codex CHALLENGE disclosed, ANNEX R @ b10a5a7 → **`[r6]`: accepted body `4b0d946` + annex stack through R2 @ `760d20f` — TERMINAL.**

**PIN VERIFICATION (rule 23):** `4b0d946` ✓, `fd35416` ✓, `5279a11` ✓, `dff23f8` ✓ — all commits. The timing-race commits `2618e9b`, `0089f9b`, `66200f2`, and the later `e15308d`, `11dbd23`, `baf05ed`, `5c8d2fd`, `b10a5a7`, `a8dec16`, `fed3cff`, `760d20f` are cited in shard-2 text and are that shard's to verify.

**DERIVATION:** Not a mathematical unit; a discharge-geography record with a disclosed protocol failure and its remedy.

**RESOLUTION TRACE:** statement lines 1062–1100. correction sites: `[r2]`/`[r3]` in situ (landed); §S12's PE2-G2 item at 1795–1808 (itself corrected in place by `[r3]`), §S13's PE3-G1 item at 1870–1893, §S9.3's GENH4 bullet at 1551–1599, §S16 row 7 at 2360 and the re-verification at 2401–2421 — all shard 2.

**TEETH:** **`stale self-description`** is the exact species this record documents: the r2 sentence “no GENH4 r3 existed at this commit — checked” was FALSE against the git log, and the note preserves it with its refutation. Disposition for the record class: `in-house hostile pass` (five consecutive record-integrity findings PE2-G2 → PE3-G1 → PE4-G1 → PE5-G1 → PE6-G1, each caught by a fresh hostile context, none by any battery row). This is the strongest evidence in the shard that **record integrity is not tooth-guarded and never can be**.

XREF: `lean/notes/openmath/GENH4_PROOF_2026-08-08.md:THEOREM GENH4.B` — count **6**; `THEOREM GENH4.A` — count **5**; `GENH4-1F` — count **10**; `GENH4.D` — count **8**; `Q22-L1` — count **7**; `Q22-L3` — count **3**; `GENH4-CAP(F)` — count **11**; `GENH4-2` — count **15**.
XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:S6.3` — count **3**.

---

### EFF.GENIND.s1of3.60  [theorem]

**CANONICAL STATEMENT:** FORM: italic-headed paragraph (§S6's Step 5). verbatim, lines 1102–1106.

> “*Step 5 (fire W-12.D).* P(n)'s (A0)+(A1)+(A2) are W-12.D's
> hypotheses at degree n: THEOREM W-12.D (PROVED, @ pin) yields one
> R_τ(q) ∈ ℚ(q) per splitting type of degree n, = the Haar density,
> same expression at every prime power and characteristic, Σ_τ R_τ = 1.
> Strong induction over n completes THEOREM GENIND.B. ∎”

**CONDITIONALITY:** Depends on the W-12.D pin. **§S16 re-verified this exact use-site against the supplier text at the NEW pin** (lines 2376–2399, shard 2), quoting both sides and matching them clause by clause: “Match: hypothesis triple and all four conclusion clauses, one for one. The r4-added σ-LABELING bracket inside (A1) is a STRENGTHENED hypothesis (more is demanded of P(n), nothing less is delivered by the theorem); its per-degree supply is not this note's to re-prove — W12 r4's own FIRING CHECK verified it at W-11(i)/(iii) (n = 2), HM3.C (n = 3), GENH4.C (n = 4), GENHN.C (μ = 2 stages), with n ≥ 6 named as [GENHN-HE(μ ≥ 3)] … VERDICT: consumption SURVIVES at the new pin.” **The strengthened (A1) is the one open edge here:** more is demanded of P(n), and this note does not re-derive `.30`'s (A1)-closure under the strengthened predicate (OPEN-CALL 3).

**SUPERSESSION KIND:** (received) `as-of scoping` on the pin + a **strengthened supplier hypothesis** that the note records as surviving. The strengthening is not a supersession of this Step's text.

**DERIVATION:** Displayed; the substance is W-12.D, cited.

**RESOLUTION TRACE:** statement lines 1102–1106. correction sites: 1466–1482 (§S9.3's W-12 re-pin, shard 2), 2354 (§S16 row 1, shard 2), 2376–2399 (the verbatim re-verification, shard 2), 2479–2487 (PE7-m1's grep-claim correction, shard 2).

**TEETH:** NONE — a theorem application. **PIN VERIFICATION:** `99f1813` ✓ (the old pin, in-range); the new pin `be4a1dc/ee17210` is cited in shard 2 and is that shard's to verify.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:THEOREM W-12.D` — count **5**.

---

### EFF.GENIND.s1of3.61  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph closing §S6. verbatim, lines 1108–1113.

> “**Where the conditionality lives, exactly.** (IH) grounds at the
> PROVED P(2), P(3). Steps 1–2's order-1 content is S2–S5 (this note,
> proved). The ONLY consumption of [GENIND-H(n)] is: Step 2's CS-stage
> menus, Step 3's CS-leaf σ, Step 4's CS-internal drainage. At n ≤ 3
> these consumptions are vacuous (S5.1) — GENIND.B degenerates to the
> proved n ≤ 3 chain, which is the reduction's non-vacuity check.”

**CONDITIONALITY:** **“The ONLY consumption of [GENIND-H(n)]” is a three-item universal claim, and it is the sentence the merge must handle most carefully.** Three later movements bear on it, none editing it:
1. **A fourth consumption exists in the repaired proof**: the CS-drain RATE, supplied by GENIND-C2/C2Q under **(CS-1Q)** — a clause family *inside* [GENIND-H]'s (CS-1) as originally displayed, but explicitly **not** discharged by it (line 3712, shard 3: the displayed (CS-1) “do[es] not establish (CS-1Q.b) for every embedded or mixed genre”). So the three-item list remains true at the level of *clause names* and becomes incomplete at the level of *what must be verified per genre*.
2. **At n ≥ 8 two further conjuncts enter** ([GENHN-HE(μ ≥ 3)], [GENHN-TOW-1]) per the supplier-movement record (`.15`).
3. **The n ≤ 3 vacuity claim is re-audited and KEPT** (§S14 C10, shard 2): “S5.1 "the n ≤ 3 program never consulted [W12-H]" — TRUE, KEPT. Evidence: the composite-free theorem (S5.1) + GT-CRIT zero CS events on all four n = 3 rows (S11 P-8).”

**SUPERSESSION KIND:** (received) `scope-pin` at (1) and (2). Neither is a replacement; the sentence is true as written and *incomplete* as a checklist.

**DERIVATION:** A summary of Steps 1–5; no separate proof.

**RESOLUTION TRACE:** statement lines 1108–1113. correction sites: 2112–2114 (§S14 C10, shard 2), 3076–3088 (the n ≥ 8 movement, shard 3), 3712–3721 (the (CS-1Q) upgrade + consumer sweep, shard 3).

**TEETH:** the non-vacuity check itself is toothed: GT-CRIT's negative half (zero CS events on all four n = 3 rows) is exactly the machine form of “at n ≤ 3 these consumptions are vacuous”. Executable regression, and the note's own designed **non-vacuity gate**.

---

### EFF.GENIND.s1of3.62  [definition]

**CANONICAL STATEMENT:** FORM: inline paragraph opening §S7.1. verbatim, lines 1119–1122.

> “A CS opening hands the read a stage (m′, D′, E, K): key polynomial
> Φ′ of degree D′ = e·d·deg ψ, stage multiplicity m′ = μ, value-group
> index E = e (the new denominator), stage residue field K
> (|K| = q^{d·deg ψ}). [GENIND-H] at this stage is:”

**CONDITIONALITY:** Definitional; fixes the stage datum every (CS-·) clause quantifies over.

**ARITHMETIC AUDIT (compiler-computed):** `|K| = q^{d·deg ψ} = Q^{deg ψ}` with `Q = q^d` ✓ — consistent with shard 3's C2 normalization `|K| = q^{dγ} = Q^γ`. At the M6 stage (`.33`): `d = 1, deg ψ = 1` → `|K| = q` ✓ and `D′ = e·d·deg ψ = 2` ✓, matching the displayed `(m′, D′, E, K) = (2, 1·2, 2, F_q)`. At genre F (`.49`): `e = 1, deg ψ = 2, d = 1` → `D′ = 2`, `|K| = q²` ✓, matching shard 3's “genre F — … over K = F_{q²}”.

**DERIVATION:** Definitional.

**RESOLUTION TRACE:** statement lines 1119–1122. correction sites: none.

**TEETH:** NONE — a definition.

---
### EFF.GENIND.s1of3.63  [hypothesis]

**CANONICAL STATEMENT:** FORM: bulleted display ((CS-1), with two landed correction brackets). verbatim, lines 1123–1146.

> “* **(CS-1) the stage transport** — the order-≥2 analogue of the
>   per-center transport: the opening locus fibers as (letter census) ×
>   q^{affine} × [the stage state space], with the stage states = the
>   Φ′-adic development (A_{m′−1}, …, A₀), deg A_j < D′, carrying ONE
>   K-digit slot per (abscissa, v′-height) in the stage's value
>   normalization — and the stage read (polygon, residuals over K,
>   refine events) is count-isomorphic to a degree-m′ cluster-system
>   read over K at an explicit stage window, RAGGED-WINDOW-CORRECTED
>   [r1, PE1-G2: the E residue classes' slot strings end at different
>   v′-heights (at the (2,2)-E stage: even slots at dv = 2N−2, odd at
>   2N+h−2 — S7.3), so the count-isomorphism is asserted BELOW the
>   ragged threshold, uniform there, with the ragged band a boundary
>   family routed through (A2) — it enters Step 4's inventory
>   explicitly. This is the form the note's own (OB-a) requires and
>   the form the discharger proves: GENHN.A(v) @ 850e77e reads "the
>   stage read IS the (μ, K)-cluster read in dv-units at the S-node,
>   ragged-window-corrected", with the band confined by LEMMA GENHN-3.
>   The sealed statement omitted the correction.] [r2, PE2-G1: at
>   MIXED openings — the polygon also carrying β-children — this
>   fibration COMPOSES with the child product over the same polygon:
>   the display gains the factor Π_l [(μ_l, d) child system at M_l],
>   with the stage-window count independent of the child states —
>   LEMMA GENIND-6 (S4.3), whose clause (d) also supplies the σ/drain
>   composition. The sealed display had no child-system slot.]”

**CONDITIONALITY:** **OPEN at every genre** (GENIND-BOX-1); de facto discharged at n = 4 by GENH4's package (`.59`, `.66`). Two landed corrections (ragged-window; mixed-opening child slot). **The clause is then split in two from outside the range**: the 2026-08-12 round-2 correction introduces a strictly stronger quantitative sub-clause family **(CS-1Q.a–b)** and declares the displayed (CS-1) insufficient for it (line 3712, shard 3):

> “The displayed general (CS-1), GENIND-6(a), and GENHN references do not establish (CS-1Q.b) for every embedded or mixed genre: they assert affine per-coordinate windows and boundary routing, but do not relate the resulting loss to entry codimension. Accordingly, “conditional on (CS-1) only” must be replaced by “conditional on (CS-1Q), verified per genre.” A universal discharge for embedded and mixed genres remains obstructed until those affine ledgers are displayed and checked.”

The two new clauses, verbatim (lines 3623–3635, shard 3):

> “\[ M_{\mathcal G} \ge e(N-1-H)-\Delta_{\mathcal G}, \tag{CS-1Q.a} \]
> and
> \[ \gamma\Delta_{\mathcal G} \le C_{\mathcal G}^{\mathrm{extra}} +\left(b_S-a-\frac12\right)H+O_{\mathcal G}(1). \tag{CS-1Q.b} \]
> Clause (CS-1Q.b) is the explicit price of the ragged boundary and sibling-Hensel losses. It says that every lost \(K\)-digit is paid either by an additional entry condition or by the supporting-line slack beyond the load-bearing coefficient \(a+\tfrac12\).”

**This is ledger row HYP.36** (`spec/HYPOTHESIS_LEDGER.md:310–315`), disposition **CARRY** — *“embedded/mixed affine ledgers are not universally checked.”*

**SUPERSESSION KIND:** `[r1, PE1-G2]` = `inventory completion` (a correction the sealed statement omitted is restored, and the boundary family it creates is added to Step 4's inventory). `[r2, PE2-G1]` = `inventory completion` (the display gains a missing factor). The 2026-08-12 (CS-1Q) upgrade = **`replacement`** of the conditionality label for every rate consumer, with the ORIGINAL (CS-1) clause itself left standing for its menu/transport consumers. **Three kinds; the third does not withdraw the first two.**

**CHAIN:** sealed (CS-1) → `[r1]` ragged-window-corrected → `[r2]` mixed-opening child factor → **2026-08-12 round-2: for RATE consumers, (CS-1Q.a–b) verified per genre — TERMINAL for the rate; the `[r2]`-corrected (CS-1) remains TERMINAL for menu/transport.** A chapter cut must carry BOTH terminals; they govern different consumers.

**DERIVATION:** Not proved here — this is a displayed hypothesis. Its mechanism supply is `.67`; its n = 4 instance is `.68` (LEMMA GENIND-4, PROVED).

**RESOLUTION TRACE:** statement lines 1123–1146. proof lines — none (hypothesis). correction sites: `[r1]`/`[r2]` in situ (landed); 3055–3074 (the GENHN A(v)/GENHN-3 survival screen, shard 3), 3592–3722 (C2-G1 and its certification-status paragraph, shard 3).

**TEETH:** NONE in this note's battery — (CS-1) is a hypothesis, not a measured quantity. Its n = 4 instance's *fibration geometry* is PROVED at `.68` and its M6 mixed instance is exhaustively enumerated at `.40`. Disposition: **`signed vacuity disclosure`** at general genres.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN.A(v)` — count **6**; `LEMMA GENHN-3` — count **3**.
**PIN VERIFICATION:** `850e77e` ✓ commit.

---

### EFF.GENIND.s1of3.64  [hypothesis]

**CANONICAL STATEMENT:** FORM: bulleted display ((CS-2), with a landed `[r1, PE1-G3]` NORMALIZATION DECLARATION and an in-line numeric check). verbatim, lines 1147–1168.

> “* **(CS-2) the stage bracket** — the stage's own α-aggregation:
>   b_{m′,K}(μ″) = (|K|−1)·|K|^{(c(m′)+1)μ″−1} in stage units, i.e.
>   GENIND-2(b) run inside the stage. NORMALIZATION DECLARED [r1,
>   PE1-G3]: this bracket is MASS-NORMALIZED — it includes the ghost
>   fibers |K|^{c(m′)·k_i} of the stage α-transport, totalling
>   |K|^{c(m′)·μ″} over the chain — whereas a ladder-telescoped
>   LETTER-SUM (per-node laws carrying the floors, GENH4 S6.2's form)
>   reads (|K|−1)·|K|^{μ″−1} at m′ = 2; the two compose as
>   (|K|−1)|K|^{2μ″−1} = |K|^{μ″} · (|K|−1)|K|^{μ″−1} (ghost ×
>   letters), the reconciliation GENHN S6.2 displays (@ 850e77e). At
>   the e-first genre E (|K| = q; the ladder has δ = 2μ″ integer
>   dv-points, so the letter-sum (q−1)q^{δ−1} coincides numerically
>   with this display) the gap is invisible; it surfaces only at
>   f-first genres — GENH4 S6.2's genre-F (q²−1)(q²)^{μ−1} vs this
>   box's instantiation (q²−1)(q²)^{2μ−1}, differing by exactly the
>   ghost (q²)^μ. A discharge of (CS-2) must therefore be read in THIS
>   (mass) normalization, or composed with its ghost fiber. Checked
>   numerically this round at (q, μ″) = (2, 2), |K| = 4 (genre F,
>   c(2) = 1): composition sum Σ_{(k₁..k_r), Σk_i=2} Π_i
>   (|K|−1)|K|^{k_i} = 48 + 144 = 192 = (|K|−1)|K|³ (mass form);
>   letters-only Σ (|K|−1)^r = 3 + 9 = 12 = (|K|−1)|K|¹ (GENH4 form);
>   ghost |K|² = 16; 16 · 12 = 192. [r1]”

**CONDITIONALITY:** OPEN as a hypothesis; the **normalization declaration is the load-bearing part** — a discharge in the wrong normalization would be off by the ghost factor `|K|^{μ″}`, invisible at genre E and visible at genre F. §S9.3's GENHN bullet lists S6.2 as one of the four consumed clauses, and the survival screen (lines 3068–3069, shard 3) records: “S6.2, consumed at (CS-2): E2's tag reaches its assembly sentence's census factor, the same alignment as A(v) — SURVIVES.”

**SUPERSESSION KIND:** `[r1, PE1-G3]` = `license` — the bracket is not re-worded; the *reading* under which a discharge counts is declared, and a numeric certificate is supplied. Reading it as a `wording-rider` would lose the point that the display never changed.

**ARITHMETIC AUDIT (compiler-computed, re-deriving the note's own numeric check at (|K|, μ″) = (4, 2), c(2) = 1):**
* Compositions of μ″ = 2: `(2)` and `(1,1)`. Mass form terms: `(|K|−1)|K|^{k}` per step → `(4−1)·4² = 48` for `(2)`; `[(4−1)·4¹]² = 12² = 144` for `(1,1)`. Sum = **192** ✓.
* Closed form: `(|K|−1)|K|^{(c+1)μ″−1} = 3·4^{2·2−1} = 3·4³ = 3·64 = 192` ✓.
* Letters-only: `Σ_r (|K|−1)^r` over the two compositions = `3¹ + 3² = 3 + 9 = 12` ✓; closed form `(|K|−1)|K|^{μ″−1} = 3·4¹ = 12` ✓.
* Ghost: `|K|^{c·μ″} = 4^{1·2} = 16` ✓; `16 × 12 = 192` ✓ — the reconciliation checks exactly.
* Genre-E invisibility claim: with `|K| = q` and `δ = 2μ″` dv-points, the letter-sum reads `(q−1)q^{δ−1} = (q−1)q^{2μ″−1}`, which equals the mass form `(q−1)q^{(c(2)+1)μ″−1} = (q−1)q^{2μ″−1}` ✓ — **numerically coincident, exactly as claimed**, so the normalization gap is genuinely invisible at genre E.
* Genre-F gap: mass `(q²−1)(q²)^{2μ−1}` ÷ letters `(q²−1)(q²)^{μ−1}` = `(q²)^{μ}` ✓ = the stated ghost.

**DERIVATION:** `.22`'s generating-function identity, run in stage units; the reconciliation is cited to GENHN S6.2 and checked numerically in place.

**RESOLUTION TRACE:** statement lines 1147–1168. proof lines 328–332 (GENIND-2(b)'s proof, in stage units). correction sites: `[r1, PE1-G3]` in situ (landed); 3068–3069 (the GENHN S6.2 survival screen, shard 3).

**TEETH:** the in-line numeric check IS a tooth of a kind the rest of the shard lacks — a **compiler-verifiable arithmetic certificate embedded in the statement** (audited above, all five identities reproduce). Disposition: `arithmetic recount` (rule 27), self-supplied. No battery row exercises (CS-2) at any genre.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:S6.2` — count **6**.
**NEAR-MISS (rule 15):** `GENH4 S6.2` — the string `S6.2` has fixed-string count **0** in `GENH4_PROOF_2026-08-08.md` (the count **6** above is GENHN's, a different file). GENIND cites “GENH4 S6.2's form” and “GENH4 S6.2's genre-F (q²−1)(q²)^{μ−1}”; the verified GENH4 designations in the neighbourhood are `THEOREM GENH4.A` (5), `THEOREM GENH4.B` (6) and `GENH4-CAP(F)` (11). Referent carried descriptively; **not** emitted as a clean XREF. Flagged as source defect 5 (§8) — a section pointer into a note that does not carry that section number.

---

### EFF.GENIND.s1of3.65  [hypothesis]

**CANONICAL STATEMENT:** FORM: bulleted display ((CS-3)). verbatim, lines 1169–1171.

> “* **(CS-3) the σ-decision** — the order-≥2 GMN leaf theorem
>   ([W12-H](H-e)): separable stage residuals ⟹ σ-decided with (e·E,
>   f·[K-ext]) read off, for ALL disc ≠ 0 lifts — (A0) at the stage.”

**CONDITIONALITY:** **OPEN, and open as its own theorem** — `.72`'s (OB-c): “σ/(A0) at stage leaves = (H-e) — open exactly as [W12-H] prices it; the COUNT claims of GENIND-5 do not consume it, the (A0) claims do.” §S7.1's closing sentence (`.67`) repeats: “(CS-3) is its own theorem ((H-e), open)”. The `for ALL disc ≠ 0 lifts` quantifier is the same form HMENU3's ANNEX A corrected HM3.C to (§S16 row 3) — i.e. this note consistently quantifies (A0) over disc ≠ 0 lifts.

**DERIVATION:** None — a cited open hypothesis.

**RESOLUTION TRACE:** statement lines 1169–1171. correction sites: none.

**TEETH:** **NONE, at any degree, anywhere in this note.** The GT-ORACLE leg (`.56`) verifies σ at **order-1 decided leaves only**. Disposition: `signed vacuity disclosure` — the strongest such disclosure in the shard, since (CS-3) is a full (A0) supply at every composite stage.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:[W12-H]` — count **17**.

---

### EFF.GENIND.s1of3.66  [hypothesis]

**CANONICAL STATEMENT:** FORM: bulleted display ((CS-EXACT), §S7.1's copy — the second display of the clause first stated at `.14`), with landed `[r2, PE2-m1]`, `[r3, PE3-G1]` and `[r2, PE2-G2]` brackets. verbatim, lines 1172–1190.

> “* **(CS-EXACT) the exactness clause [r1, PE1-G1]** — the stage menu
>   and stage drain delivered by (CS-1)+(CS-2) are EXACT: one exact
>   closed form per stratum — a finite sum of q-powers [r2, PE2-m1:
>   two terms at GENH4's genre-F even-N CAP(F) band, one term
>   elsewhere; the r1 gloss "one closed-form q-power family" named too
>   coarse a stratum], not asymptotic bounds. A genuine fourth member,
>   consumed by GENIND.B Step 4 (see its [r1] record: the induction
>   propagates P(n)'s exact-complement (A2) member only through exact
>   stage laws). De facto discharge at n = 4 [r3, PE3-G1: pin advanced
>   to GENH4 r3 = 4b0d946 (display-only diff for these consumptions;
>   PE4 CLEAN e15308d, 1/2) — see Step 4's [r3] record] [r2, PE2-G2:
>   re-pinned at
>   GENH4 r2 = fd35416 + 5279a11, BOTH halves named — drain = THEOREM
>   GENH4.B (= Q22-L3), menu = THEOREM GENH4.A (= Q22-L1) + GENH4-1F
>   with the r2-corrected comp-weighted census; the r1 cite @ dff23f8
>   named only the drain half and sat on a pin whose menu half carried
>   a then-adjudicated, undisclosed CRITICAL — full timing disclosure
>   at Step 4's [r2] record]; at general n this clause is a hypothesis
>   on the box — not claimed discharged.”

**CONDITIONALITY:** Identical in content to `.14`; the two displays are riddered by **different** later texts, which is why they are two units (rule 21's analogue for statements stated twice — HE7 precedent 21). `.14`'s rationale is riddered by R6.2; **this** display's *pin* is riddered by the `[r3]`/`[r4]`/`[r5]`/`[r6]` chain at §S9.3 (`.59`'s CHAIN). Its granularity gloss is riddered by `[r2, PE2-m1]` in place.

**SUPERSESSION KIND:** `[r2, PE2-m1]` = `wording-rider` (a granularity phrase is substituted). `[r2, PE2-G2]`/`[r3, PE3-G1]` = `as-of scoping` (pins). **Two kinds in one bullet.**

**RELATION TO `.14`:** same clause, two displays, different rider sets. **Format consequence, recorded for the merge:** a hypothesis stated twice at different granularities is TWO units when different riders name each display — the HE7 pilot's item-21 finding, reproduced here independently.

**DERIVATION:** None — a displayed hypothesis. The consumption path is `.58`.

**RESOLUTION TRACE:** statement lines 1172–1190. correction sites: `[r2]`/`[r3]` in situ (landed); 1551–1599 (§S9.3's GENH4 bullet chain, shard 2), 2360 and 2401–2421 (§S16 row 7 + the re-verification, shard 2), 2986–2997 (R6.2, shard 3).

**TEETH:** as `.14` — `signed vacuity disclosure` in this note; the n = 4 evidence is a supplier citation, re-verified verbatim at §S16 against the accepted-body text.

XREF: `lean/notes/openmath/GENH4_PROOF_2026-08-08.md:THEOREM GENH4.B` — count **6**; `THEOREM GENH4.A` — count **5**; `GENH4-1F` — count **10**; `Q22-L1` — count **7**; `Q22-L3` — count **3**; `GENH4-CAP(F)` — count **11**.

---

### EFF.GENIND.s1of3.67  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph closing §S7.1 — **positive supply and its explicit negative fence in one span**. verbatim, lines 1192–1206.

> “**Where the carry corpus delivers (the displayed mechanism).** The
> stage slot claim in (CS-1) — one K-digit per (abscissa, v′-height) —
> is exactly COROLLARY W-9 + FINDING JC-F1's **dim_K 𝒜(T) = E**
> (GRTJC @ pin): the transported carry algebra at the stage is the
> twisted group algebra K^c[ℤ/E], E graded K-lines per integer height —
> E slots per old v-unit, one per v′-unit. The stage residual reads are
> the GRADED reads with no cancellation across the ℤ/E-degrees —
> JC-LOAD/W-8's warrant (wild composite stages included). And the
> letters the stage read consumes are ζ-twisted by the carry cocycle
> (W-9(iii)) — units, which COUNTS NEVER SEE: LEMMA J-D0 lifts the
> count laws over the twist. So the corpus supplies the stage's
> SLOT GEOMETRY and LETTER-BLINDNESS outright; what it does not supply
> by itself is the step-for-step READ CORRESPONDENCE (the stage
> analogue of W12-L1(b)'s case check) — that is the exact residue of
> (CS-1), and (CS-3) is its own theorem ((H-e), open).”

**CONDITIONALITY:** The positive half is a citation of ACCEPTED suppliers (GRTJC accepted 2/2 @ 83f47f4). The negative half — “what it does not supply by itself is the step-for-step READ CORRESPONDENCE … the exact residue of (CS-1)” — is the sharpest NON-IMPORT in the shard and the exact statement of what (CS-1) still owes.

**DERIVATION:** Citation, not proof.

**RESOLUTION TRACE:** statement lines 1192–1206. correction sites: none. Pin: §S9.3's GRTJC bullet (lines 1520–1522, shard 2), “consumed ONLY in S7's display: dim_K 𝒜(T) = E, the carry cocycle, JC-LOAD's no-cancellation. No count law of S2–S6 consumes them”; §S16's unmoved-pin list (lines 2367–2368, shard 2) records GRTJC's body unmoved.

**TEETH:** NONE — a supply/fence record. **PIN VERIFICATION:** `83f47f4` ✓ commit.

XREF: `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md:COROLLARY W-9` — count **2**; `JC-F1` — count **18**; `dim_K 𝒜(T) = E` — count **3**; `JC-LOAD` — count **31**; `W-8` — count **35**.
XREF: `lean/notes/openmath/JD0_PROOF_2026-08-08.md:LEMMA J-D0` — count **4**.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:W12-L1` — count **30**.

---

### EFF.GENIND.s1of3.68  [lemma]

**CANONICAL STATEMENT:** FORM: display (blockquote, LEMMA GENIND-4 — the one PROVED order-≥2 result in the note) preceded by its frame sentence. verbatim, lines 1210–1233.

> “The first instance, the quartic e-first genre CS4-E(h) (= QSCOUT22
> GENRE E): m′ = 2, D′ = 2, E = 2, K = F_q, Φ′ = x² − s, s = ẑπ^h.
>
> > **LEMMA GENIND-4.** On the CS4-E(h, z) opening locus (per center
> > AND letter z: q^{4N−5h−3} members — the (q−1) belongs to the
> > h-genre's sum over z ∈ F_q^×, not to the fixed-(h, z) slice this
> > lemma fibrates [r1, PE1-M4]), the Φ′-adic development f = Φ′² +
> > A₁Φ′ + A₀ (A₁ = α₁x + α₀, A₀ = β₁x + β₀) is a TRIANGULAR digit
> > bijection from the opening coordinates (b₃, b₂, b₁, b₀):
> >
> >     b₃ = α₁,  b₂ = α₀ − 2s,  b₁ = β₁ − sα₁,  b₀ = β₀ − sα₀ + s²,
> >
> > with stage-initial budgets v(α₁) ≥ (h+1)/2, v(α₀) ≥ h+1,
> > v(β₁) ≥ (3h+1)/2, v(β₀) ≥ 2h+1 — total free exponent 4N−5h−3, the
> > opening locus EXACTLY (no overcount, no undercount). In doubled
> > units dv := 2v (the stage normalization v′, E = 2), each coordinate
> > A_j carries ONE q-digit slot per integer dv-height (h odd forces
> > the parities apart: even dv-slots from the constant coefficient,
> > odd from the x-coefficient — the ℤ/2 carry grading of W-9 made
> > literal), and the stage-initial node is
> >
> >     { dv(A₀) ≥ 2S+1, dv(A₁) ≥ S+1 }  with  S := 2h
> >
> > — the W-11 refine node C(2S+1, S+1) ON THE NOSE, in stage units.”

**CONDITIONALITY:** **PROVED, unconditionally, at this genre.** It is the (A1)-side geometry of the (2,2)-E stage — “so the first stage-polygon classification is well-posed” (`.71`). It does **not** prove (CS-1) at the genre: the read correspondence is (OB-a)/(OB-b) (`.72`). The `[r1, PE1-M4]` bracket is a landed locus-scoping correction (the `(q−1)` letter factor belongs to the h-genre sum, not the fixed-(h,z) slice).

**SUPERSESSION KIND:** `[r1, PE1-M4]` = `scope-pin` (which locus the lemma fibrates), plus, inside the proof, a `wording-rider` repairing an editing scar. Two kinds, one round.

**DERIVATION:** verbatim, lines 1235–1253:

> “*Proof.* The development identities are the direct expansion of
> (x²−s)² + (α₁x+α₀)(x²−s) + (β₁x+β₀); triangularity (each b_j = its
> A-coordinate + terms in later coordinates) makes the map a bijection
> of digit spaces. Budgets: the opening pins v(b₃) ≥ (h+1)/2,
> digit_h(b₂) = −2z, v(b₁) ≥ (3h+1)/2, digit_{2h}(b₀) = z² (W-12 S2.5)
> translate coordinatewise: α₁ = b₃; α₀ = b₂ + 2s has its h-digit
> cancelled (−2z + 2z), so v ≥ h+1; β₁ = b₁ + sα₁ has v ≥
> min((3h+1)/2, h + (h+1)/2) = (3h+1)/2; β₀ = b₀ + sα₀ − s² has its
> 2h-digit cancelled (z² + 0 − z²), so v ≥ 2h+1. Free-digit total:
> (N − (h+1)/2) + (N−1−h) + (N − (3h+1)/2) + (N−1−2h) = 4N − 5h − 3 ✓
> — matching the opening law exactly, which is the no-over/undercount
> check. dv-arithmetic: dv(a·x + b) = min(2v(a) + h, 2v(b)) (the root
> has v = h/2); 2v(b) is even, 2v(a)+h odd — distinct parities, no
> ties, one slot per integer dv. Node: dv(A₁) ≥ min(2·(h+1)/2 + h,
> 2(h+1)) = min(2h+1, 2h+2) = 2h+1 = S+1; dv(A₀) ≥ min(2·(3h+1)/2 + h,
> 2(2h+1)) = min(4h+1, 4h+2) = 4h+1 = 2S+1 [r1, PE1-M4: the sealed
> line's editing scar "= 2h+1 = S+... = 2h+1" repaired; both minima now
> displayed, values unchanged]. With S = 2h: (2S+1, S+1) =
> (4h+1, 2h+1). ∎”

Justification tags: development identities = `computation` (direct expansion); budgets = `by XREF W-12 S2.5` (the opening pins) + `computation` (coordinatewise cancellation); the free-digit total = `computation` (audited below); dv-parity = `computation`; the node = `computation` + `by XREF` W-11's refine node C(·,·); the ℤ/2 grading = `by XREF W-9`.

**ARITHMETIC AUDIT (compiler-computed, every displayed number re-derived):**
* Expansion: `(x²−s)² + (α₁x+α₀)(x²−s) + (β₁x+β₀)` = `x⁴ − 2sx² + s² + α₁x³ + α₀x² − sα₁x − sα₀ + β₁x + β₀` = `x⁴ + α₁x³ + (α₀ − 2s)x² + (β₁ − sα₁)x + (β₀ − sα₀ + s²)` ✓ — the four displayed identities `b₃ = α₁`, `b₂ = α₀ − 2s`, `b₁ = β₁ − sα₁`, `b₀ = β₀ − sα₀ + s²`, **exactly**.
* Triangularity: each b_j is its A-coordinate plus terms in *later* (higher-index-s) coordinates ✓; the pivots are all 1 — **note that this is precisely the unit-pivot condition ANNEX R R2 later requires globally** (`.36`), satisfied here by inspection.
* Budget translations: `α₀ = b₂ + 2s` with `digit_h(b₂) = −2z` and `s = ẑπ^h` → the h-digits cancel (`−2z + 2z = 0`) → `v(α₀) ≥ h+1` ✓. `β₁ = b₁ + sα₁`: `v ≥ min((3h+1)/2, h + (h+1)/2) = min((3h+1)/2, (3h+1)/2) = (3h+1)/2` ✓ (the two are equal, so the min is attained twice — the display's “min” is exact). `β₀ = b₀ + sα₀ − s²`: `2h`-digits `z² + 0 − z² = 0` → `v(β₀) ≥ 2h+1` ✓.
* Free-digit total: `(N − (h+1)/2) + (N−1−h) + (N − (3h+1)/2) + (N−1−2h)` = `4N − 2 − 3h − [(h+1) + (3h+1)]/2` = `4N − 2 − 3h − (4h+2)/2` = `4N − 2 − 3h − 2h − 1` = **`4N − 5h − 3`** ✓ — matching CS4-E's law at `.48` exactly, which is the stated no-over/undercount check. **(Identical in form to the `.50` audit; the two computations are the same four-summand pattern.)**
* Node: `dv(A₁) ≥ min(2·(h+1)/2 + h, 2(h+1)) = min(h+1+h, 2h+2) = min(2h+1, 2h+2) = 2h+1` ✓; `dv(A₀) ≥ min(2·(3h+1)/2 + h, 2(2h+1)) = min(3h+1+h, 4h+2) = min(4h+1, 4h+2) = 4h+1` ✓. With `S = 2h`: `S+1 = 2h+1` ✓ and `2S+1 = 4h+1` ✓ — **the W-11 node C(2S+1, S+1) on the nose**.
* Parity separation: `dv(a·x + b) = min(2v(a) + h, 2v(b))`; with h odd, `2v(a)+h` is odd and `2v(b)` is even ✓ — no ties, one slot per integer dv ✓.

**RESOLUTION TRACE:** statement lines 1210–1233. proof lines 1235–1253. correction sites: `[r1, PE1-M4]` in situ at 1215–1216 and 1250–1252 (both landed). No later round touches it.

**TEETH:** No direct battery row (GENIND-4 is order-≥2 geometry, and the sealed battery's CS legs check *classification*, not stage development). Guarded instead by (i) the exponent tie to the machine-scored CS4-E law (`.48`, three exact spots), (ii) the disclosed independent derivation at `.69`, and (iii) — out of range — ANNEX R — r1's leg, which walks the PINNED GENH4 sealed walker over genre-E rows. Disposition: **`accepted-with-decorrelation-supplied`** (the QSCOUT22 cross-derivation) plus an arithmetic recount (this compiler's, above — every displayed identity and exponent reproduces).

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:S2.5` — count **9**.
XREF: `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md:W-9` — count **13**.
XREF: `lean/notes/openmath/QSCOUT22_2026-08-08.md:GENRE E` — count **2**.

---

### EFF.GENIND.s1of3.69  [instance-record]

**CANONICAL STATEMENT:** FORM: parenthetical inline sentence. verbatim, lines 1255–1257.

> “(QSCOUT22's LEMMA Q22-B states the same budgets from the scout side;
> the two derivations were made independently — the numbers agree,
> disclosed as a cross-check, not two units citing one computation.)”

**CONDITIONALITY:** A decorrelation disclosure with an explicit anti-double-counting fence (“not two units citing one computation”). **This is the note's own guard against exactly the failure mode the standing memory note calls extraction-corruption decorrelation** — a shared source masquerading as two witnesses.

**DERIVATION:** Not a proof; a provenance record.

**RESOLUTION TRACE:** statement lines 1255–1257. correction sites: none.

**TEETH:** `accepted-with-decorrelation-supplied` — an independent derivation at a second unit, disclosed as such. Its own limit: the scout's pin at the time was a *skeleton* (`.03`), and §S9.3's `[r6]` re-pin advances it to “verdict dd67cda + annex fcaf268” while recording “nothing was or is consumed”.

XREF: `lean/notes/openmath/QSCOUT22_2026-08-08.md:Q22-B` — count **6** (`LEMMA Q22-B` — count **1**).

---
### EFF.GENIND.s1of3.70  [hypothesis]

**CANONICAL STATEMENT:** FORM: display (blockquote, CANDIDATE THEOREM GENIND-5 — explicitly NOT proved). verbatim, lines 1261–1279.

> “**CANDIDATE THEOREM GENIND-5 (the (2,2) stage law; NOT proved —
> boxed at the displayed obstruction).** The CS4-E(h) stage read is
> count-isomorphic to the W-11 n = 2 system over F_q in dv-units at
> the stage node C(4h+1, 2h+1): its history-resolved menu = W12-L0's
> laws with (N, depth) read in dv-units and the PARITY-RAGGED window
> (even slots end at dv = 2N−2, odd at 2N+h−2; uniform statements
> hold below dv = 2N−2, the ragged band routes through (A2) as a
> boundary family); in particular THE COMPOSITE-STAGE BRACKET IS THE
> m = 2 BRACKET IN STAGE UNITS:
>
>     b_stage(μ) = (q−1)·q^{2μ−1}   (dv-depth aggregation),
>
> the (CS-2) instance — same exponent coefficient c(2)+1 = 2 as the
> order-1 quadratic cluster, because W-9's dim = E already flattened
> the stage lattice to one slot per unit height. Stage leaves map to
> σ by: stage-RAM (odd dv-side) ↦ {(4,1)} (e doubles again);
> stage-2SIDED/SPLITEQ ↦ {(2,1),(2,1)}; stage-INERTDEEP ↦ {(2,2)};
> stage-refine ↦ recurse with b_stage. [Wild p = 2 included: the
> pins degenerate (−2z ≡ 0), the slot counts do not — J-D0.]”

**CONDITIONALITY:** **NOT PROVED — a candidate, boxed at (OB-a)–(OB-d)** (`.72`). GENIND-BOX-1 (lines 1351–1353, shard 2): “GENIND-5 is a CANDIDATE with its obstruction displayed (OB-a..d). No count law at order ≥ 2 is claimed proved.” §S11's closing paragraph re-states it after the sealed run (lines 1764–1767, shard 2): “CANDIDATE GENIND-5 … remains boxed at (OB-a)/(OB-b)/(OB-c)/(OB-d), with LEMMA GENIND-4 (the fibration + the ℤ/2 slot grading) PROVED and its predictions handed to QSCOUT22.”

**ARITHMETIC AUDIT (compiler-computed):** the stage bracket `b_stage(μ) = (q−1)q^{2μ−1}` is `.22`'s `b_{m,d}(μ)` at `m′ = 2`, `|K| = q`, `c(2)+1 = 2` ✓. Node `C(4h+1, 2h+1)` = `.68`'s `(2S+1, S+1)` at `S = 2h` ✓. Parity-ragged ends: even slots at `dv = 2N−2` and odd at `2N+h−2`; their difference is `h` ✓, and with h odd the two ends have opposite parities, consistent with `.68`'s parity separation ✓. **Consistency with `.64`'s normalization declaration:** `.64` says the mass form at genre E “coincides numerically” with the letter-sum because `δ = 2μ″`; here the displayed `(q−1)q^{2μ−1}` is exactly that coincident value ✓ — so GENIND-5's bracket is stated in the normalization `.64` requires.

**DERIVATION:** Partial only — see `.71`. The count-isomorphism itself is the unproved part.

**RESOLUTION TRACE:** statement lines 1261–1279. proof lines 1281–1293 (partial, `.71`). correction sites: none — no later round touches the candidate; ANNEX R and the 2026-08-12 corrections all act elsewhere.

**TEETH:** **NONE — and deliberately so.** The candidate's falsifiable content is handed to an external instrument as preregistered predictions (`.73`). Disposition: `signed vacuity disclosure`; the note's own coverage sentence is the title parenthetical “NOT proved — boxed at the displayed obstruction”.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:W12-L0` — count **32**.
XREF: `lean/notes/openmath/JD0_PROOF_2026-08-08.md:J-D0` — count **25**.
XREF: `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md:W-9` — count **13**.

---

### EFF.GENIND.s1of3.71  [lemma]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph. verbatim, lines 1281–1293.

> “**What is PROVED toward it:** GENIND-4 (the fibration + node + slot
> grading — the stage's (A1)-side geometry), so the first stage-polygon
> classification is well-posed. And the stage-refine RECENTERING
> Φ′ ↦ Φ′ + w (deg w ≤ 1) is computed here to be triangular-WITH-CARRY:
> expanding f = (Φ′+w)² + A₁″(Φ′+w) + A₀″ and reducing mod Φ′ gives
> A₁″ = A₁ − 2w + c, A₀″ = A₀ − wA₁ + w² − c·(…) with c = the Φ′-carry
> of the degree-2 overflow of wA₁ (the x² ≡ s (mod Φ′) wrap — LITERALLY
> the cocycle multiplication of W-9: odd·odd dv-slots landing on even
> slots twisted by s). The parities (h odd) keep the carry's landing
> slots disjoint from the pinned slots — JC-LOAD's no-cancellation
> holds here BY PARITY, elementarily — so the one-step update is again
> a digit bijection killing the refined pin: the SINGLE-STEP refine
> isomorphism is within reach of exactly the S7.2 computation.”

**CONDITIONALITY:** **A one-step result only.** The display itself scopes it: “the SINGLE-STEP refine isomorphism is within reach” — the chain-level iteration is (OB-a) and the general-step residual identification is (OB-b). Note the elegance the note claims and the fence it draws in the same breath: JC-LOAD's no-cancellation is obtained here *by parity, elementarily*, i.e. **without** consuming the GRTJC warrant at this genre — a genre-local simplification that does not generalize.

**ARITHMETIC AUDIT (compiler-computed):** expanding `(Φ′+w)² + A₁″(Φ′+w) + A₀″` = `Φ′² + 2wΦ′ + w² + A₁″Φ′ + A₁″w + A₀″`. Matching against `f = Φ′² + A₁Φ′ + A₀` gives `A₁ = A₁″ + 2w` (modulo the Φ′-carry of the degree-2 overflow) → `A₁″ = A₁ − 2w + c` ✓, and `A₀ = w² + A₁″w + A₀″` → `A₀″ = A₀ − wA₁″ − w² = A₀ − w(A₁ − 2w + c) − w² = A₀ − wA₁ + w² − wc` ✓ — matching the displayed `A₀″ = A₀ − wA₁ + w² − c·(…)` with the elided factor being `w` ✓. **The displayed identities check.** The `x² ≡ s (mod Φ′)` wrap is exactly `Φ′ = x² − s` ✓, so a degree-2 overflow term `x²` reduces to the unit `s` — “odd·odd dv-slots landing on even slots twisted by s” ✓ (odd dv-slots come from the x-coefficient per `.68`, and a product of two x-coefficients is a degree-2 term).

**DERIVATION:** Displayed in the statement (the direct expansion + the parity argument).

**RESOLUTION TRACE:** statement lines 1281–1293. proof lines — displayed. correction sites: none.

**TEETH:** NONE — no battery row exercises stage-refine recentering. **PROOF-ONLY**; the coverage sentence is the display's own “SINGLE-STEP … within reach”.

XREF: `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md:JC-LOAD` — count **31**; `W-9` — count **13**.

---

### EFF.GENIND.s1of3.72  [fence]

**CANONICAL STATEMENT:** FORM: bold-headed bulleted display (the four boxed obstructions). verbatim, lines 1295–1318.

> “**The EXACT OBSTRUCTION (boxed, not hand-waved):**
> * **(OB-a) chain-level window coherence in dv-units.** The one-step
>   bijection must be iterated: ghost zones of the stage (which
>   dv-digits of A₁, A₀ a depth-κ stage chain may consult) need the
>   H-2(i) argument re-run on the RAGGED window (even/odd slots end at
>   different dv-heights). Until that ledger is written, deep stage
>   histories might consult a ragged-band digit and break uniformity
>   at the last ⌊h/2⌋-ish window slots. Expected resolution: the
>   consulted-height bound (m−j)(window)/m of GENIND-2 lands below
>   BOTH parities' ends; the n = 3 analogue was exactly HEX3's [r1 F1]
>   corner.
> * **(OB-b) the stage residual = the block residual up to units, at
>   EVERY step.** One step is the parity argument above; the general
>   step needs the graded-read identification (W-8/JC-LOAD consumed as
>   warrant — accepted 2/2, but its consumption here as a POINTWISE
>   digit statement on (α₁, α₀, β₁, β₀) coordinates is a new
>   transcription that must be written and machine-checked, not
>   cited).
> * **(OB-c) σ/(A0) at stage leaves = (H-e)** — open exactly as
>   [W12-H] prices it; the COUNT claims of GENIND-5 do not consume it,
>   the (A0) claims do.
> * **(OB-d) genre F** (residue-field-first, K = F_{q²}) — untouched
>   here; QSCOUT22's territory; the analogue of GENIND-5 there has
>   K-letters and the F_{q²} censuses.”

**CONDITIONALITY:** All four OPEN. **(OB-a) is the same object (CS-1)'s `[r1, PE1-G2]` ragged-window correction names** — the note says so at `.63`: “This is the form the note's own (OB-a) requires and the form the discharger proves: GENHN.A(v) @ 850e77e …”, i.e. **(OB-a) is discharged at the genres GENHN covers and open in general**. (OB-b) explicitly refuses to cite: “a new transcription that must be written and machine-checked, not cited” — an unusually sharp anti-citation fence. (OB-c) = (CS-3) = `.65`. (OB-d) is a division-of-labor fence (`.03`).

**BOUNDARY NOTE (rule 9 self-audit, recorded here as well as at §6.1):** the four OBs are kept as ONE unit because the note cites them as a group in every consuming sentence — “boxed at (OB-a)/(OB-b)/(OB-c)/(OB-d)” (§S11), “(OB-a)/(OB-b) per genre plus (H-e) once” (§S7.4), “boxed at (OB-a)/(OB-b)/(H-e)” (§S9.1) — and no rider names an individual OB. Recorded as arguable: (OB-c) alone has a life outside the box (it IS (CS-3)) and a merge may prefer to wire it to `.65` directly.

**DERIVATION:** Not a proof; an obstruction inventory with an expected-resolution note at (OB-a).

**RESOLUTION TRACE:** statement lines 1295–1318. correction sites: none in range. Related out-of-range: 1136–1140 (the (CS-1) `[r1]` bracket naming (OB-a)), 1764–1767 (§S11's re-statement, shard 2), 1442–1443 (§S9.1's proposed annex text, shard 2).

**TEETH:** NONE — the unit IS the coverage-hole inventory. **PROOF-ONLY** by construction, and the shard's canonical instance of rule 16's row class.

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:H-2` — count **11**.
XREF: `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md:W-8` — count **35**; `JC-LOAD` — count **31**.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:[W12-H]` — count **17**.

---

### EFF.GENIND.s1of3.73  [preregistration]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (falsifiable predictions stated in advance, handed to an EXTERNAL instrument). verbatim, lines 1319–1327.

> “**Falsifiable predictions handed to QSCOUT22's table** (keyed to its
> GENRE E; per opening (h, z), per center, window N, dv-window
> M₂ := 2N−2): the stage's undecided (conservative) count =
> q^{#A₁-slots} at A₀ ≡ 0: q^{(N−(h+1)/2)+(N−1−h)} = q^{2N−(3h+3)/2};
> the first-step stage-RAM(u₂) law (q−1)q^{...} with exponents read
> from W12-L0 at (M₂, node S = 2h) — if the scout's measured table
> matches these at its smoke rows, GENIND-5's transport is corroborated
> before its proof; a mismatch localizes to (OB-a)/(OB-b) and refutes
> the candidate as stated.”

**CONDITIONALITY:** A genuine preregistration (rule 19): a prediction stated before the measuring run, with an explicit falsification target and an explicit localization rule. **No matching `run-record` is homed in this note** — the scoring instrument is QSCOUT22's, and §S9.3 records that “nothing [is] consumed from it”. §S9.2 states the upgrade rule: “a confirmed table upgrades GENIND-5 from candidate to corroborated-candidate (proof still owed at the boxes)”.

**ARITHMETIC AUDIT (compiler-computed):** `#A₁-slots` from `.68`'s budgets: the α₁ coordinate is free from `v ≥ (h+1)/2` up to the window, giving `N − (h+1)/2` slots; the α₀ coordinate is free from `v ≥ h+1`, giving `N − 1 − h` slots. Sum = `2N − (h+1)/2 − 1 − h` = `2N − (h + 1 + 2 + 2h)/2` = `2N − (3h+3)/2` ✓ — the displayed exponent, re-derived. Consistency with the total: `.68`'s four free-digit counts sum to `4N − 5h − 3`; the A₁-half alone is `2N − (3h+3)/2`, so the A₀-half is `4N − 5h − 3 − 2N + (3h+3)/2` = `2N − (7h+3)/2`; and indeed `.68`'s β-budgets give `(N − (3h+1)/2) + (N−1−2h) = 2N − 1 − 2h − (3h+1)/2 = 2N − (7h+3)/2` ✓ — **the split checks exactly**, so “undecided = A₁-slots at A₀ ≡ 0” is arithmetically the right complement.
`M₂ := 2N−2` matches `.70`'s even-slot end `dv = 2N−2` ✓; node `S = 2h` matches `.68` ✓.

**DERIVATION:** Read off `.68`'s budgets and W12-L0's laws in stage units; displayed.

**RESOLUTION TRACE:** statement lines 1319–1327. correction sites: none. Downstream rule at 1447–1449 (§S9.2, shard 2).

**TEETH:** **UNPINNED (rule 23).** The prediction names no artifact filename of its own; its scoring instrument is QSCOUT22's committed table, whose pin moved from the skeleton `240a56c` to “verdict dd67cda + annex fcaf268” (§S9.3 `[r6]`) — and **no unit of this note records whether the predictions were scored**. Disposition: `preregistration` with **no matching run-record anywhere in the note**. Flagged as OPEN-CALL 4 (§8).

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:W12-L0` — count **32**.
XREF: `lean/notes/openmath/QSCOUT22_2026-08-08.md:GENRE E` — count **2**.

---

### EFF.GENIND.s1of3.74  [scope-record]

**CANONICAL STATEMENT:** FORM: unheaded paragraph closing §S7.4 (the [GENIND-H] work order). verbatim, lines 1331–1347.

> “The (2,2) pattern generalizes as the work order: at a stage
> (m′, D′, E, K), (CS-1) = a GENIND-4-style triangular development
> fibration (the entry pins cancel coordinatewise; expected budgets =
> the entry law's exponent, the E parities/residues mod E separating
> slots — W-9's ℤ/E grading) + the stage read's identification with
> the (m′, 1) cluster system over K in v′-units; (CS-2) = GENIND-2(b)
> inside the stage: b_{m′,K}(μ) = (|K|−1)|K|^{(c(m′)+1)μ−1} (mass
> normalization — S7.1's [r1] declaration); (CS-3) = (H-e);
> (CS-EXACT) [r1, PE1-G1] = deliver the stage menu and drain as exact
> per-stratum closed forms (a GENIND-4-style fibration does this by
> construction when it lands). Each is per-genre finite work at each
> degree; the corpus
> supplies grading + blindness + no-cancellation; the residue is the
> transcription (OB-a)/(OB-b) per genre plus (H-e) once. NOTHING in
> the scaffold consumes a stage law before its genre is realized
> (criterion, S5.1), so the program is finitely enumerable
> degree-by-degree while the SCAFFOLD stays uniform in n.”

**CONDITIONALITY:** A work order, not a result. **Its closing claim — “finitely enumerable degree-by-degree while the SCAFFOLD stays uniform in n” — is the note's strongest structural assertion and rests on the criterion (`.11`/`.43`)**: no stage law is consumed before its genre is realized, and realization requires n ≥ 4 with finitely many genres per degree. **The 2026-08-12 round-2 certification-status paragraph adds a per-genre obligation the work order does not list**: (CS-1Q.b)'s affine ledgers, “a named obligation” (line 3869, shard 3), which is per-genre work of exactly the kind this order enumerates but was not enumerated by it.

**SUPERSESSION KIND:** (received) `inventory completion` — the work order's per-genre residue list gains (CS-1Q.b) from outside the range.

**DERIVATION:** Generalization of `.68`'s pattern; no proof claimed.

**RESOLUTION TRACE:** statement lines 1331–1347. correction sites: 3712 and 3866–3871 (the (CS-1Q) obligation, shard 3). Related: 1329 (§S7.4's heading), 2953–2955 (R5's three-site consumer walk, which names “S7.4's finite enumerability (the necessity half)” as a consumer of GENIND.A(IV) — confirming that this paragraph consumes only the necessity direction, so R5's degree-level pin does not disturb it).

**TEETH:** NONE — a work order.

XREF: `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md:W-9` — count **13**.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:[W12-H]` — count **17**.

---
## 3. Consumption tables

### 3.1 Verified import/XREF designations

`[TABLE — compiler ledger]` Every row's count is `grep -cF '<designation>' <file>` run at HEAD, recorded inline at the unit and repeated here. **59 distinct designations, all count ≥ 1**, across nine supplier notes; plus 2 file-existence rows and 7 NEAR-MISS dispositions (§3.1b).

| # | Target : designation | Count | Role in this shard |
|---|---|---|---|
| 1 | `W12_PROOF_2026-08-08.md:THEOREM W-12.D` | 5 | The reduction fired at Step 5 (`.60`); the whole uniformity consequence (`.15`) |
| 2 | `W12_PROOF_2026-08-08.md:THEOREM W-12.A` | 8 | Order-1 decided-shape law at every degree — the induction's leaves (`.05`, `.08`, `.44`, `.46`, `.54`) |
| 3 | `W12_PROOF_2026-08-08.md:W12-L0` | 32 | History-resolved n = 2 menus; P(2) base; GENIND-5's stage laws (`.05`, `.15`, `.70`, `.73`) |
| 4 | `W12_PROOF_2026-08-08.md:W12-L1` | 30 | (a) the level-0 product re-entry; (b) letters move by a unit, hulls do not (`.19`, `.24`, `.35`, `.36`, `.67`) |
| 5 | `W12_PROOF_2026-08-08.md:W12-S2.1` | 9 | Level-0 Hensel product; the Hensel split at step (2) (`.07`, `.24`, `.34`, `.54`, `.56`) |
| 6 | `W12_PROOF_2026-08-08.md:S2.2` | 19 | The Φ-adic bijection and every slot count (`.07`, `.17`, `.36`, `.47`) |
| 7 | `W12_PROOF_2026-08-08.md:S2.3` | 35 (upper bound) | Certificate transport at simple leaves (`.44`, `.56`) |
| 8 | `W12_PROOF_2026-08-08.md:S2.5` | 9 | The QRT-G2 opening law, PROVED at the w12 seal (`.11`, `.47`, `.48`, `.68`) |
| 9 | `W12_PROOF_2026-08-08.md:S3.4` | 11 | The δ-substitution instance; boundary-family routing (`.30`, `.57`) |
| 10 | `W12_PROOF_2026-08-08.md:S1` | 24 (upper bound) | Conventions; the `[r1 F3]`-corrected refine taxonomy (`.07`, `.17`) |
| 11 | `W12_PROOF_2026-08-08.md:[W12-H]` | 17 | The composite-stage box; (H-e) (`.05`, `.08`, `.43`, `.65`, `.72`, `.74`) |
| 12 | `W12_PROOF_2026-08-08.md:QRT-G2` | 10 | The n = 4 e-first first instance (`.11`, `.48`) |
| 13 | `HEX3_PROOF_2026-08-08.md:H-1` | 5 | Depth-0 partition; the n = 3 instance of GENIND-1(i) (`.05`, `.20`) |
| 14 | `HEX3_PROOF_2026-08-08.md:H-2` | 11 | α-transport (i)(ii)(iii); the n = 3 instance of GENIND-1(ii)/GENIND-2(a) (`.05`, `.18`, `.21`, `.72`) |
| 15 | `HEX3_PROOF_2026-08-08.md:H-3` | 5 | The three β routes (`.05`, `.24`) |
| 16 | `HEX3_PROOF_2026-08-08.md:H-4` | 2 | The n = 3 scaffold instance list (`.05`) |
| 17 | `HEX3_PROOF_2026-08-08.md:R(M)` | 21 | The n = 2 drain law consumed by the β drain composition (`.25`, `.45`) |
| 18 | `HEX3_PROOF_2026-08-08.md:S5.1` | 9 | The n = 3 closed forms tied by GT-N3TIE (`.20`, `.45`) |
| 19 | `HEX3_PROOF_2026-08-08.md:HEX3-BOX-2` | 4 | The ledger-compression pricing precedent (`.10`, `.26`, `.42`) |
| 20 | `HEX3_PROOF_2026-08-08.md:THEOREM HEX3.A` | 11 | The n = 3 exact law (consumed by ANNEX R R1's rate leg; named in range at `.45`'s neighbourhood) |
| 21 | `HEX3_PROOF_2026-08-08.md:THEOREM HEX3.B` | 8 | The n = 3 rate — the species (A2-RATE) generalizes (`.45`, `.46`) |
| 22 | `HMENU3_PROOF_2026-08-08.md:HM3-1` | 4 | Two-species classification template (`.04`, `.05`, `.19`, `.20`) |
| 23 | `HMENU3_PROOF_2026-08-08.md:HM3-2` | 5 | Drain-verdict → KEY resolution upgrade (`.05`, `.21`) |
| 24 | `HMENU3_PROOF_2026-08-08.md:HM3-3` | 3 | The n = 3 β-transport instance (`.05`) |
| 25 | `HMENU3_PROOF_2026-08-08.md:HM3-4` | 11 | The n = 3 bracket (q−1)q^{4μ−1} (`.05`, `.09`, `.22`, `.23`) |
| 26 | `HMENU3_PROOF_2026-08-08.md:HM3.A` | 18 | History-resolved menu form; the raw-key dictionary (`.05`, `.13`, `.24`) |
| 27 | `HMENU3_PROOF_2026-08-08.md:HM3.B` | 19 | The n = 3 (A1) B-families (`.30`) |
| 28 | `HMENU3_PROOF_2026-08-08.md:HM3.C` | 15 | The (A0) argument at general n; the S5.3 exact-complement sharpening (`.44`, `.57`) |
| 29 | `HMENU3_PROOF_2026-08-08.md:HM3-BOX-5` | 4 | The finite-relabeling pedantry inherited at Step 2 (`.55`) |
| 30 | `W11_PROOF_2026-08-08.md:THEOREM W-11` | 3 | P(2) base (`.15`) |
| 31 | `JD0_PROOF_2026-08-08.md:LEMMA J-D0` | 4 | Count-gauge blindness (`.05`, `.17`, `.36`, `.55`, `.67`) |
| 32 | `JD0_PROOF_2026-08-08.md:J-D0` | 25 | Same, in the note's short form (`.70`) |
| 33 | `GRTJC_PROOF_2026-08-08.md:W-6` | 18 | Carry-corpus member (`.05`) |
| 34 | `GRTJC_PROOF_2026-08-08.md:W-8` | 35 | No-cancellation warrant (`.05`, `.67`, `.72`) |
| 35 | `GRTJC_PROOF_2026-08-08.md:W-9` | 13 | The ℤ/E carry grading (`.05`, `.67`, `.68`, `.71`, `.74`) |
| 36 | `GRTJC_PROOF_2026-08-08.md:COROLLARY W-9` | 2 | The precise form cited for dim_K 𝒜(T) = E (`.67`) |
| 37 | `GRTJC_PROOF_2026-08-08.md:JC-F1` | 18 | The finding paired with COROLLARY W-9 (`.67`) |
| 38 | `GRTJC_PROOF_2026-08-08.md:JC-LOAD` | 31 | No-cancellation across ℤ/E degrees (`.05`, `.67`, `.71`, `.72`) |
| 39 | `GRTJC_PROOF_2026-08-08.md:dim_K 𝒜(T) = E` | 3 | The stage slot lattice, verbatim (`.05`, `.67`) |
| 40 | `GENHN_PROOF_2026-08-08.md:GENHN.A(iv)` | 3 | The stage node floor κ ≥ S_b + 1 (`.35`) |
| 41 | `GENHN_PROOF_2026-08-08.md:GENHN.A(v)` | 6 | The ragged-window-corrected stage read (`.37`, `.63`) |
| 42 | `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-3` | 3 | Ragged-band confinement (`.57`, `.63`) |
| 43 | `GENHN_PROOF_2026-08-08.md:S6.2` | 6 | The ghost × letter reconciliation (`.64`) |
| 44 | `GENHN_PROOF_2026-08-08.md:S11.F` | 10 | The per-coefficient certified-window computation (`.34`) |
| 45 | `GENHN_PROOF_2026-08-08.md:S6.3` | 3 | The general-genre exactness shape (`.57`, `.59`) |
| 46 | `GENHN_PROOF_2026-08-08.md:GENHN.C` | 19 | Named in the W-12 r4 FIRING CHECK geography (`.15`) |
| 47 | `GENHN_PROOF_2026-08-08.md:GENHN-TOW-1` | 19 | The n ≥ 8 conjunct added by the supplier-movement record (`.15`) |
| 48 | `GENH4_PROOF_2026-08-08.md:THEOREM GENH4.A` | 5 | The menu half of the n = 4 de facto discharge (`.59`, `.66`) |
| 49 | `GENH4_PROOF_2026-08-08.md:THEOREM GENH4.B` | 6 | The drain half (`.14`, `.59`, `.66`) |
| 50 | `GENH4_PROOF_2026-08-08.md:GENH4-1F` | 10 | Menu-half companion (`.59`, `.66`) |
| 51 | `GENH4_PROOF_2026-08-08.md:GENH4.D` | 8 | The package sentence CS-1 = GENIND-4 + GENH4-1F + GENH4-2/-3/-4 (`.59`) |
| 52 | `GENH4_PROOF_2026-08-08.md:GENH4-2` | 15 | Named inside GENH4.D's package (`.59`) |
| 53 | `GENH4_PROOF_2026-08-08.md:Q22-L1` | 7 | GENH4.A's scout-side name (`.59`, `.66`) |
| 54 | `GENH4_PROOF_2026-08-08.md:Q22-L3` | 3 | GENH4.B's scout-side name (`.59`, `.66`) |
| 55 | `GENH4_PROOF_2026-08-08.md:GENH4-CAP(F)` | 11 | The two-term genre-F even-N band (`.14`, `.59`, `.66`) |
| 56 | `QSCOUT22_2026-08-08.md:GENRE E` | 2 | The (2,2)-E scout table; prediction target (`.03`, `.48`, `.68`, `.73`) |
| 57 | `QSCOUT22_2026-08-08.md:GENRE F` | 1 | The (2,2)-F scout table (`.03`, `.49`) |
| 58 | `QSCOUT22_2026-08-08.md:Q22-B` | 6 | The independent budget derivation (`.69`) |
| 59 | `QSCOUT22_2026-08-08.md:LEMMA Q22-B` | 1 | Same, in its full designation form (`.69`) |

**File-existence rows** (rule 23): `lean/notes/openmath/WELDMASTER_2026-08-08.md` EXISTS ✓ and `lean/notes/openmath/DULEMMA_PROOF_2026-08-08.md` EXISTS ✓ — both named at `.05` with no addressable designation cited in range (§S9.3 pins them “@ their accepted pins — named in S7.1's (CS-1..3) pricing only”, shard 2).

**Battery artifacts verified to EXIST on disk** (`verification/openmath/`): `genind_checks.py`, `genind_checks_output.txt`, `genind_checks_results.json`, `genindr2_supp.py`, `genindr2_supp_output.txt`, `genindr2_supp_results.json`, `genind_pe3_fresh.py` (+ output, results), `genind_pe4_fresh.py` (+ output, results), `genind_pe5_fresh.py` (+ output, results), `genind_pe6_fresh.py` (+ output, results), `genind_annexr_supp.py` (+ output), `genind_annexr1_checks.py` (+ output, results) — **all present**. (`genind_pe7_fresh.*`, `genind_pe8_fresh.*` and `genind_annexr_pass2_fresh.*` also exist; they are shard-2/3 material.)

**Commit pins verified with `git cat-file -t`** (rule 23), all = `commit`: `4259a93`, `50db400`, `f89b565`, `ade9bac`, `bd9bce1`, `265a562`, `ad1bd98`, `f7f45f1`, `c3212cc`, `99f1813`, `7020ceb`, `2580f12`, `64d3ff9`, `850e77e`, `4b0d946`, `240a56c`, `83f47f4`, `1642275`, `f5271e4`, `a1525ea`, `51bd1bc`, `380bc66`, `3f5bafc`, `993935d`, `b653858`, `b6a1d69`, `fd35416`, `5279a11`, `dff23f8` — **29/29 resolve.**

### 3.1b NEAR-MISS dispositions (rule 15)

`[TABLE — compiler ledger]` Cited designations that fail fixed-string grep at the target, with the verified referent. **None is emitted as a clean XREF; none is suppressed.**

| # | As cited (unit) | Count as written | Verified referent | Disposition |
|---|---|---|---|---|
| 1 | `HEX3 H-1` (`.05`, `.20`) | 0 | `HEX3_PROOF_2026-08-08.md:188` — `## S2. THE DEPTH-0 PARTITION (LEMMA H-1)`; fixed-string `H-1` count **5** | Note-qualified prefix; XREF emitted at `H-1` |
| 2 | `HEX3 S2` (`.17`) | 0 | Same line 188 (`## S2.`) — a section pointer, not a designation | Carried descriptively |
| 3 | `HEX3 S5.2` (`.45`) | 0 | HEX3's drainage/telescoping section; addressable neighbours `R(M)` (21) and `THEOREM HEX3.B` (8) | Carried descriptively |
| 4 | `HEX3-S4` (`.23`) | 0 | HEX3's §S4 R-recursion; addressable neighbour `R(M)` (21) | Carried descriptively |
| 5 | `u₃(M)` (`.45`) | 0 | GENIND-local notation for HEX3's conservative complement; HEX3 writes `u(q,N)` (`:437`) and `u(M)` (`:389`) | Carried descriptively |
| 6 | `GENH4 S6.2` (`.64`) | 0 in `GENH4_PROOF_2026-08-08.md` | GENH4's ladder-telescoped letter-sum form; addressable neighbours `THEOREM GENH4.A` (5), `GENH4-CAP(F)` (11). **The count 6 for `S6.2` is GENHN's file, a different note** | Carried descriptively; source defect 5 |
| 7 | `[GENHN-HE(μ ≥ 3)]` (`.15`) | 0 | The note discloses the defect itself at PE7-m3: “the string "GENHN-HE" occurs at r6 only inside S16 itself … the note displays no box by that name; the μ ≥ 3 stage-law content rides inside [GENIND-H]” | Carried descriptively, quoting the note's own correction |

### 3.2 Reverse consumer edges: mathematical supply versus append protocol

`[TABLE — compiler ledger]`

| Consumer / supplier | Verified designation | Shard-1 supply or consumption | Mathematical status | Append/consumption-protocol status |
|---|---|---|---|---|
| W-12 (supplier) | `THEOREM W-12.D` (5) | consumed at `.60` | Fires at degree n on P(n) | **No append landed by GENIND.** §S9.1 offers annex text: “text offered; W12_PROOF not edited” |
| W-12 (supplier) | `THEOREM W-12.A` (8) | consumed at `.08`, `.44`, `.46`, `.54` | The leaves, unconditional | Not landed |
| HEX3 / HMENU3 / W-11 (suppliers) | `H-1`(5) `H-2`(11) `H-3`(5) `HM3-1`(4)…`HM3.C`(15) `THEOREM W-11`(3) | consumed as the n ≤ 3 bases and instances | P(2), P(3) proved at their pins | Not landed. GENIND records supplier movement inbound only |
| GENHN (supplier) | `GENHN.A(iv)`(3) `A(v)`(6) `GENHN-3`(3) `S6.2`(6) `S11.F`(10) `S6.3`(3) | consumed at `.35`, `.37`, `.57`, `.63`, `.64`, `.34` | Seven consumed sites after PE7-m2's completion, not four | Not landed. Movement is INBOUND: errata E1–E3 executed + GENHN r2, with a per-clause survival screen (shard 3) |
| GENH4 (supplier) | `GENH4.A`(5) `GENH4.B`(6) `GENH4-1F`(10) `GENH4-CAP(F)`(11) | consumed at `.59`, `.66` (n = 4 de facto discharge only) | (CS-EXACT) de facto at n = 4 | Not landed. Movement INBOUND across five re-pins |
| GRTJC / J-D0 / WELDMASTER / DULEMMA (suppliers) | `COROLLARY W-9`(2) `JC-F1`(18) `JC-LOAD`(31) `LEMMA J-D0`(4) | consumed ONLY at §S7's display (`.67`) | Slot geometry + letter-blindness supplied outright | Not landed. §S9.3: “No count law of S2–S6 consumes them” |
| QSCOUT22 (peer) | `GENRE E`(2) `Q22-B`(6) | `.03`, `.69`, `.73` | **Nothing consumed** — division of labor + an independent cross-check + preregistered predictions handed over | Not landed; nothing consumed, by declaration |
| W12-BOX-1 / [W12-H] (downstream) | `W12-BOX-1` (10 in W12) | §S9.1 offers an annex text (shard 2) | GENIND.B is the induction the box asked for | **Offered, not landed** — the heading says so |

**The last column is not an inference.** GENIND states the protocol in its own words at `.06` (“This note edits no supplier note. Proposed annex texts: §S9.”) and again at §S9.1's heading. **Zero consumption appends are claimed landed on any supplier by this note, and none is invented here.** In the reverse direction GENIND *received* two supplier movements (GENHN's errata + r2; GENH4's annex arc) plus eight in-house hostile passes, one Codex ratification and two sol certification runs.

---

## 4. NON-IMPORTS

`[TABLE — compiler ledger]` The note's explicit negative fences homed in lines 1–1348.

| Fence | Explicit material NOT imported or NOT proved | Unit |
|---|---|---|
| No supplier edits | “This note edits no supplier note.” | `.06` |
| Carry corpus scope | “consumed ONLY at the composite-stage frontier (S7)” — no count law of S2–S6 consumes W-6..W-9, JC-LOAD, WELDMASTER, DULEMMA, [W12-H] | `.05`, `.67` |
| Nothing consumed from the scout | “S7's predictions are keyed to its table, not re-measured here”; “the two units' machine legs are disjoint by design” | `.03`, `.05` |
| Ledger compression (β) | “What is NOT written here: the closed-form fiber exponent of every genre at every degree” | `.26` |
| Ledger compression (mixed) | “the per-genre certified-window ledgers are mechanical affine computations, compressed here” | `.42` |
| GENIND-3's hypothesis | “excludes polygons that ALSO carry a composite block” | `.29`, `.24` |
| No order-≥2 count law | “No count law at order ≥ 2 is claimed proved” (GENIND-BOX-1, shard 2) — in range: GENIND-5 is a CANDIDATE | `.70`, `.72` |
| (CS-3)/(H-e) | “open exactly as [W12-H] prices it”; “(CS-3) is its own theorem ((H-e), open)” | `.65`, `.67`, `.72` |
| The read correspondence | “what it does not supply by itself is the step-for-step READ CORRESPONDENCE … that is the exact residue of (CS-1)” | `.67` |
| (OB-b) refuses citation | “a new transcription that must be written and machine-checked, **not cited**” | `.72` |
| Genre F untouched | “(OB-d) genre F … untouched here; QSCOUT22's territory” | `.72` |
| Stage-level converse unclaimed | ANNEX R R5: “The STAGE-level parse … is NOT claimed by this note … at general m the stage-level statement is left unclaimed” | `.11` |
| CS4-F/CS5 laws unpriced | “Non-flagship (classified, laws not preregistered)”; CS5-V4E2 “its law is derivation-only here” | `.51`, `.52` |
| No stage law consumed early | “NOTHING in the scaffold consumes a stage law before its genre is realized” | `.74` |
| d ≥ 2 uncorroborated | “machine-uncorroborated here beyond the w12-sealed order-1 instances” (GENIND-BOX-3, shard 2); in range: “roster limit: the battery exercises d = 1 plus one (m, d) = (2, 2) targeted row” | `.23` |
| No machine instance for stage-steeper | “this note's own machine leg still carries no instance” | `.42` |
| Two-stage-block genres not live | “not live at n ≤ 7: two composite blocks consume ≥ 8 abscissas” | `.42` |
| Same-side f-first unrealized (as of r5) | “the same-side f-first genre itself … remains machine-unrealized corpus-wide” — later closed by PE6, the sentence not edited (STALE-SELF-DESCRIPTION) | `.32` |
| No general (CS-1Q) discharge | “A universal discharge for embedded and mixed genres remains obstructed until those affine ledgers are displayed and checked” (shard 3) — lands on `.37`, `.57`, `.63` | `.37`, `.57`, `.63` |
| No rate from (CS-EXACT) | R6.2: “(CS-EXACT) supplies exactness, not a rate” | `.14`, `.66` |
| n ≤ 3 never consulted [W12-H] | “the reason the n ≤ 3 program never consulted [W12-H]” (§S14 C10: TRUE, KEPT) | `.11`, `.43`, `.61` |

---

## 5. Teeth inverse table

`[TABLE — compiler ledger]` Battery row → guarded unit(s) → disposition. Disposition enum, as widened by v3 rules 20 and 27: {executable regression, planted mutant, measurement, signed non-applicability, foreign-note evidence, signed vacuity disclosure, disclosed non-repair, accepted-with-decorrelation-supplied, stale self-description, AUDIT: decorrelated-model audit / in-house hostile pass / transfer audit / arithmetic recount}. **The sealed battery's rows are DESCRIBED at §S10 and SCORED at §S11, both shard 2; they are listed here because they guard in-range units, per rule 6's both-directions requirement.**

| Battery row / tooth | Guarded unit(s) | Disposition |
|---|---|---|
| **GT-PIN** [NONE] — 5 md5 pins (w11/w12/hex3/hmenu3 runners + hex3 results JSON), P-1 scored 0/5, re-verified 5/5 at §S16 | `.05` | Executable regression on artifact pins (NOT on note pins — those are git-log-checked, untoothed) |
| **GT-PART** [SAME] — partition exact on every row; P-2 0/33; Zp/F_q[[t]] tallies identical at all 11 shared (m,q,N) | `.08`, `.17`, `.55` | Executable regression, both ring kinds |
| **GT-DEPTH0** [SAME, both directions] — P-3 0/108; every never-measured spot exact | `.08`, `.17`, `.48`, `.49`, `.50`, `.51` | Executable regression; **all six of this shard's scored spot values reproduce from the displayed laws** (audited at `.48`–`.51`) |
| **GT-BDRAIN** [SAME] — the n = 4 FULL-side β drain laws in closed form; P-4 0/4, B2Q(1) 512/1,024 | `.24`, `.25`, `.45`, `.46`, `.57` | Executable regression consuming the PROVED n ≤ 3 drains |
| **GT-ALPHA** [SAME, pointwise + fibers + onto] — P-5 0/2,474; tooth GT-T-ALPHA = 12 | `.18`, `.21` | Executable regression + surjectivity check |
| **GT-BETA** [SAME] — pointwise Hensel reconstruction; P-6 0/87,156 | `.10`, `.19`, `.24`, `.25`, `.28` | Executable regression, member by member |
| **GT-RECUR** [SAME] — α-drain self-similarity; P-6 0/8 | `.21`, `.45`, `.46` | Executable regression |
| **GT-BRACKETID** [SYM] — P-7 24/24 at m ∈ {2,3,4,5}, μ ∈ {1,2,3}, q ∈ {2,3}; tooth GT-T-BRACKET = 24 | `.09`, `.22`, `.23` | Executable regression (symbolic identity) |
| **GT-CRIT** [SAME] — P-8 0/22, both directions; tooth GT-T-CRIT = 4 | `.08`, `.11`, `.43`, `.48`, `.49`, `.50`, `.52`, `.53`, `.61` | Executable regression + grammar acceptor; the note's own **non-vacuity gate** at n ≤ 3 |
| **GT-N3TIE** [NONE] — P-9 0/16, both legs (HEX3 closed forms AND the committed JSON) | `.20` | Foreign-note evidence consumed as a convention tie |
| **GT-ORACLE** [IND] — P-9 0 bad / 73,676 checks over 36,838 members, PARI nfinit/idealprimedec, wild p = 2 included | `.56` | Executable regression on a mechanism-free decorrelated oracle — **order-1 decided leaves only** |
| **GT-CONS** [SAME] — constructed targeted loci (n = 4 α(2) @ (Zp,2,9); n = 5 α(1); n = 4 BFULL(1)) | `.18`, `.21`, `.53` | Executable regression at loci the sweeps cannot reach |
| **GT-T-CS** = 12 (every n = 4 row) | `.48`, `.49` | Planted tooth, fired at its preregistered count |
| **`genindr2_supp.py` FIBRATION** — (2,5) 8,192 → 1×16/1×64; (2,6) 524,288 → 4×256/4×1024; (3,5) slice 1,594,323 → 1×81/1×729 | `.33`, `.36`, `.38` | Executable regression, exhaustive at every enumerable window; **all nine products recomputed and exact** (`.38`, `.40`) |
| **`genindr2_supp.py` CERTIFICATION** — exact-factor lift-stability, 2,460 lift comparisons across four (q,N) | `.38`, `.39` | Executable regression, redesigned after the instrument arc |
| **`genindr2_supp.py` PARI READ COMPOSITION** — 360/360 | `.37`, `.40` | Executable regression, mechanism-free |
| **T1 (sharpness)** — 38/40 at (2,6), 40/40 at (3,5) | `.39`, `.40` | Planted mutant, fired — **with a disclosed p = 2 non-sharpness at u₀** (`disclosed non-repair`) |
| **T2 (vertex pin)** — 20/20 | `.33`, `.40` | Planted mutant, fired |
| **T4 (σ_child counter-prediction)** — 360/360 refuted | `.37`, `.40` | Planted counter-prediction, fired |
| **run-1 RED on its own tooth** (the instrument arc) | `.41`, `.39` | `stale self-description` — the instrument's own result falsified its self-description; produced a real mathematical finding (the Bezout refinement) |
| **`genind_pe3_fresh.*` @ f89b565** (705,133/0): TWOCHILD exhaustive at (2,7)/(3,7); FR-A 300 M7T at (3,6) reader-ON; FR-C SS6 at (2,9)/(3,9) | `.24`, `.27`, `.40`, `.42` | Foreign-note (verifier) evidence — closes two holes this note's own leg does not cover |
| **`genind_pe4_fresh.*` @ 51bd1bc** (6,507/0): PSTEEP3/PSTEEP4 exhaustive; THREECHILD; N8MIX | `.24`, `.28` | Foreign-note evidence; `arithmetic recount` for the regime inventory |
| **`genind_pe5_fresh.*` @ bd9bce1** (109,146/0): NINEMIX, SAMESIDE | `.32` | Foreign-note evidence (geometry cross-check) |
| **`genind_pe6_fresh.*` @ ad1bd98** (2,132,082/0): the same-side f-first genre, corpus-first | `.32` | Foreign-note evidence; closes the r5 honest limit without editing it |
| **`genind_annexr_supp.py` legs F/G/H/I @ f5271e4** — monotonicity (symbolic), the unit-pivot toy, the CS4-F gate lines, the window-1 base | `.07`, `.14`, `.36`, `.49`, `.58` | Planted mutants + source-code gate verification + `accepted-with-decorrelation-supplied` |
| **`genind_annexr1_checks.py`** (P1–P5 + T-SLOPE/T-WIN; 143 GREEN, 1 flagged) | `.45`, `.46` (through GENIND-C2, shard 3) | Executable regression, n = 4 only; **the flagged P3 line is adjudicated an instrument cap literal**, homed in shard 3 |

**PROOF-ONLY rows (rule 16) — guarded units whose interesting content is a proof, with the note's own coverage-hole sentence quoted:**

| Unit | The note's own coverage sentence |
|---|---|
| `.12` (III)'s general-degree half, `.26` | “What is NOT written here: the closed-form fiber exponent of every genre at every degree” |
| `.13` (GENIND.B) | “THEOREM GENIND.B is a REDUCTION; its unconditional content at n ≥ 4 is exactly the simple-stage layer (GENIND.C) + the criterion + the opening-mass laws” (GENIND-BOX-1) |
| `.30` (GENIND-0) | **none supplied by the note** — flagged (§8, OPEN-CALL 3) |
| `.42` (GENIND-6 grade) | “the per-genre certified-window ledgers are mechanical affine computations, compressed here” |
| `.55` (Step 2's aggregation) | **none supplied by the note** — recorded |
| `.70`, `.71`, `.72` | “NOT proved — boxed at the displayed obstruction”; “the SINGLE-STEP refine isomorphism is within reach” |

**Both-direction audit.** Every battery row above guards at least one in-range unit. Every in-range unit whose `TEETH` field names a row appears in some row. Units with **`TEETH: NONE`** — `.03`, `.06`, `.07`(base), `.12`, `.13`, `.15`, `.16`, `.29`, `.47`, `.60`, `.62`, `.65`, `.67`, `.70`, `.71`, `.72`, `.74` — are declarations, definitions, grade boxes, fences, hypotheses or theorem applications and are outside the orphan count. Units flagged **`TEETH: Indirect`** — `.04`, `.54` — are guarded only through composite agreement. **Zero battery-row orphans; zero toothed-unit orphans.**

**Signed vacuity / non-applicability disclosures, enumerated** (rule 20): `.14`/`.66` ((CS-EXACT) at general n), `.51` (CS5-V4E2's law, negative direction only), `.52` (three genres never priced), `.57` (ragged-band routing and CS-internal drainage, unguarded at every degree), `.63` ((CS-1) at general genres), `.65` (**(CS-3), unguarded at every degree, anywhere**), `.70` (GENIND-5), `.42`(iii) (odd-q coverage of the mixed leg = one slice).

**Rows recorded but not counted here (homed in shard 2):** §S10's twelve family descriptions and eleven preregistered predictions P-1…P-11 as `preregistration` units; §S11's verdict scorecard as a `run-record` unit; the pre-seal smoke and three probes; the four teeth's preregistered counts. **Rule 19's split applies at the shard boundary:** the preregistration (§S10) and the run-record (§S11) are two units and shard 2 must emit them as such.

---
## 6. BOUNDARY SELF-AUDIT (tag-sparse prose genre, template rule 9)

GENIND carries **zero `\tag{` displays inside this shard's range** (all 13 in the note sit at lines 3333–3837, shard 3). Nothing in lines 1–1348 announces "this span is one statement". What it has instead: bold `LEMMA/THEOREM/CANDIDATE THEOREM` openers inside blockquotes (marking *some* units), bold prose headers (`**Honesty note …**`, `**The gap this closes.**`, `**Instances …**`, `**Machine record …**`), indented ASCII displays, `[r1]`…`[r6]` brackets (frequently mid-sentence, frequently **nested up to three deep**), and long unmarked prose. Every boundary below was **chosen**.

### 6.0 The rule applied

> **A unit is the smallest span carrying one complete claim together with its proof obligations.**

Operationally, the same four-part test the HE7 pilot fixed, applied in this order:

1. **Does the span have a proof obligation of its own?**
2. **Is the span cited BY DESIGNATION from elsewhere?**
3. **Does the span have its OWN supersession history?** — the strongest splitter here, because GENIND carries six in-place repair rounds plus four post-freeze append layers.
4. **Does the span have its own conditionality or its own consumer set?**

Proofs are NOT units (DERIVATION is a field): §S2's three proof paragraphs, §S3's (a)/(b) paragraphs, §S4.1's three-step schema, §S4.3's (a)–(d) paragraphs, §S5.1's necessity/sufficiency, §S7.2's proof are all carried inside their statements' units.

### 6.1 Boundaries drawn, with the arguable ones recorded both ways

**1. Front matter → `.01` (title + Status/arc) / `.02` (Instrument) / `.03` (Division of labor) / `.04` (What GENIND is).** Test 3 and 4. `.01`'s grade line is the target of a named supersession (PE8-m1); `.02` is an instrument description with its own pin set; `.03` is a disclosure with its own supplier pin; `.04` is a substantive orientation claim whose last sentence is riddered at n ≥ 8. *Alternative:* one front-matter unit. *Rejected* — four different supersession sources land on four different sentences.

**2. §S0 → `.05` (positive imports) / `.06` (the no-append fence).** Test 4 and template rule 3: NON-IMPORTS is a section of its own, and `.06` is header predicate B's governing quote. *Not arguable.*

**3. THEOREM GENIND.A split FOUR ways (`.08` (I), `.09` (II), `.10` (III), `.11` (IV)) plus `.12` (the GRADE box).** **The shard's most consequential boundary call.** *Candidate A:* one unit — one theorem, one name, one blockquote. *Candidate B (chosen):* five units. **Decided by four independent facts, any one of which suffices:** (i) the GRADE box itself grades the clauses *differently* — (I)(II)(IV) PROVED, (III) schema-only — so one CONDITIONALITY field would have to say both; (ii) **ANNEX R R4 riders (IV)'s first-instances clause by name and leaves (I)–(III) alone**; (iii) **ANNEX R R5 riders (IV)'s converse clause by name, quoting it**, and is a *different kind* of rider from R4's; (iv) each clause is cited by designation from elsewhere (`GENIND.A(I)` at S4.3 and S6 Step 2; `GENIND.A(IV)` at R4/R5). Under candidate A a single unit would carry two riders of different kinds on one clause and a grade split it cannot express. *Cost:* the blockquote is quoted in five pieces; all five are byte-verbatim and their union is the whole display minus nothing.

**4. THEOREM GENIND.B split FOUR ways (`.13` hypotheses / `.14` (CS-EXACT) / `.15` conclusion+consequence / `.16` GRADE).** Test 3, decisively. `.13`'s fourth member is riddered by R1's (A2-RATE); `.14`'s *rationale* is riddered by R6.2; `.15`'s conditionality is widened at n ≥ 8 by an inbound supplier movement; `.16` is a grade box qualified by the annex's own lower grade. **Four riders from four different sources on four different spans of one display.** *Candidate A:* one unit. *Rejected* — the CONDITIONALITY field would have to attach four riders to one text and the merge could not tell which sentence each edits.

**5. LEMMA GENIND-1 split THREE ways (`.17` (i) / `.18` (ii) / `.19` (iii)) + `.20` (the n = 3 instances).** Test 2 and 1: all three clauses are cited independently by designation (`GENIND-1(i)`, `GENIND-1(iii)` appear at many sites), and the proof is written as three self-contained paragraphs with no shared setup — so no duplication cost. **`.19` additionally carries an external INTERFACE flag** (ledger HYP.121) that (i) and (ii) do not. *Candidate A:* one lemma unit (the HE7 item-14 merge rule: shared proof obligations). *Rejected because* the proof obligations are NOT shared — “(ii) is HEX3 H-2(iii)'s computation … (iii) is HM3-1(iii)'s valuation argument” are independent citations. `.20` is separate on test 1 (it carries a negative claim: (iii) is vacuous at n = 2, which is what licenses W-11 as a base).

**6. LEMMA GENIND-2 split (`.21` (a) / `.22` (b)) + `.23` (Instances).** Test 2 and 3: (a) and (b) are cited separately everywhere, and **only (a) is a target of ANNEX R R3's window-1 rider**. `.23` is separate on test 4 (its d ≥ 2 sentence has its own audit history at §S14 C11 and its own box, GENIND-BOX-3). *Weakly arguable* whether `.23` folds into `.22`; chosen split because the GT-AGGDEEP naming defect (§8 defect 1) is localized there.

**7. LEMMA GENIND-3 split (`.24` fibration / `.25` drain-decidedness composition).** **Genuinely arguable.** *Candidate A:* one unit — one lemma, one blockquote, one proof. *Candidate B (chosen):* two. **Reason:** the two clauses have disjoint rider sets and disjoint consumers — the fibration half is one of ANNEX R R2's two named unit-pivot targets, while the composition half is what GENIND-C1(ii) turns into a bound and what R6.1's monotonicity notice analyses; GENIND-6(d) extends the composition half only. Under candidate A the CONDITIONALITY field would attribute R2's license to the drain clause, which it does not touch. *Cost:* one display quoted in two pieces (union = whole, verified byte-for-byte).

**8. §S4.1's post-proof prose split THREE ways (`.26` honesty note / `.27` the `[r3]` record / `.28` the CONCORDANCE paragraph).** Test 3 and 4: `.26` is untouched by every round; `.27` carries a nested `[r4]` correction of its own inventory parenthetical; `.28` carries BOTH an `[r4]` counter re-reading AND an `[r5]` provenance-rider on an artifact md5, and is the target of §S14's claim groups C1/C3. *Candidate A:* one “[r3] correction” unit. *Rejected* — three different supersession histories, and `.28`'s two nested kinds are different from each other.

**9. LEMMA GENIND-6 split FOUR ways (`.34` (a) / `.35` (b) / `.36` (c) / `.37` (d)).** Test 3, decisively, and the closest structural parallel to the HE7 pilot's item-17 decision to keep LEMMA HE7-12 WHOLE — **decided the other way here, and the reason is instructive.** HE7-12's clauses shared one proof and one hypothesis set; GENIND-6's do not: (a) is riddered by `[r3]` and by PE7-m2's inventory completion, (b) consumes an external supplier clause (GENHN.A(iv)) that (a),(c),(d) do not, (c) is the sole target of ANNEX R R2's license, and (d) is the sole target of the 2026-08-12 (CS-1Q) re-conditioning. **Four clauses, four disjoint rider sets, four separately-cited designations.** *Candidate A:* one unit with four CONDITIONALITY paragraphs (the HE7-12 shape). *Rejected* because the display's own closing Conditionality line already partitions (a)–(c) from (d) at different grades, and because a merge run building the edge list mechanically would need four TARGETS anyway.

**10. The M6 ledger split (`.38` ledger / `.39` STAGE SHARP).** Test 1 and 3: `.39` is a self-contained Bezout argument with its own `[r3, PE3-m3]` correction, its own tooth (T1), and its own disclosed parity-dependent limit; `.38`'s bullets carry no correction. *Arguable:* the FIBRATION bullet cites BOTH window sets and so straddles. *Chosen* to keep FIBRATION with `.38` because its arithmetic (audited) is a property of the ledger, not of the sharpening.

**11. The machine record split (`.40` run-record / `.41` instrument arc).** **Template rule 19 applied directly:** an executed instrument's result and a description of the apparatus are different unit kinds with different truth conditions. `.41` additionally has content `.40` does not: a normative corpus lesson and a falsified self-description. *Not seriously arguable* once rule 19 is in force; under v2 it would have been one `regression-record`.

**12. §S5.2 split (`.44` ingredients / `.45` drainage) + `.46` GENIND.C.** **The shard's highest-value split.** *Candidate A:* one §S5.2 unit. *Candidate B (chosen):* three. **Reason:** ANNEX R R1.0 quotes **exactly the drainage bullet** as the site of the heaviest CONFIRMED GAP in the note's entire arc, and R1.4 replaces its consumption at Step 4 by GENIND.C′. If the drainage bullet were folded into the ingredient list, the repair would have no addressable target and the spec would report the whole of §S5.2 as gap-bearing, which is false — the other five ingredients were never in question (“the α/head legs were never in question”, R1.4).

**13. §S5.3 split into six units (`.47`–`.52`) + `.53`.** Template rule 5's spirit (the genre tables are units) plus test 3: **CS4-E carries its floor and CS4-F does not**, and ANNEX R R4 riders only the latter. *Arguable:* whether CS4-E and CS4-F should be one “n = 4” unit, as the source's own bold header suggests. *Rejected* — one is riddered and the other is explicitly left unchanged by the same rider (“the E-law's existing floor sentence at S5.3 stands unchanged”). The two n = 5 flagships split from the non-flagship list on test 4 (priced vs unpriced).

**14. §S6 split into eight units (`.54`–`.61`).** Test 1 for each Step (each discharges a different member of P(n)), test 3 for the Step 4 trilogy. **Step 4 alone splits three ways (`.57` inventory / `.58` the `[r1]` record / `.59` the discharge geography)** because R6.2 riders the record, the (CS-1Q) sweep riders the inventory, and five re-pins land on the geography — three different sources on three spans of one Step. *Candidate A:* one Step 4 unit. *Rejected* on the same ground as item 4.

**15. §S7.1 split into six units (`.62` datum / `.63`–`.66` the four clauses / `.67` the corpus paragraph).** Test 2 and 3: the four (CS-·) clauses are cited by designation everywhere in the corpus and carry four disjoint rider sets. `.67` is separate on test 4: it is the only span that states what the corpus does NOT supply.

**16. (CS-EXACT) emitted TWICE (`.14` = §S1's display inside GENIND.B, `.66` = §S7.1's display).** **Genuinely arguable, and decided by an external fact — the HE7 pilot's item-21 finding reproduced independently.** *Candidate A:* one unit — same clause, same name, one is a forward statement. *Candidate B (chosen):* two units. **Reason:** ANNEX R R6.2 riders *§S1's* record (“Step 4's frozen `[r1]` record”) while the `[r2]`/`[r3]` GENH4 re-pins ride *§S7.1's* display; and the `[r2, PE2-m1]` granularity correction is applied to BOTH displays separately, in different words. Under candidate A the unit's CONDITIONALITY would attach a provenance rider and a pin chain to one text. **Format consequence, confirmed a second time: in prose notes a hypothesis stated twice at different granularities is TWO units when different riders name each display.**

**17. §S7.3's four obstructions kept as ONE unit (`.72`).** *Candidate A:* four units — each OB is a named object. *Candidate B (chosen):* one. **Reason:** every consuming sentence in the note cites them as a group (“boxed at (OB-a)/(OB-b)/(OB-c)/(OB-d)”, “(OB-a)/(OB-b) per genre plus (H-e) once”), and **no rider names an individual OB**. Test 2 requires an *independently* cited designation; these are always grouped. *Recorded as arguable:* (OB-c) has an independent life as (CS-3) (`.65`), and a merge may prefer an explicit `.72 → .65` edge, which §7 installs.

**18. `.73` emitted as a `preregistration` (rule 19) with NO matching run-record.** Test 1 and rule 19. The predictions are stated before the measuring run and name their falsifier and their localization rule — the defining shape of a preregistration. **The absence of a run-record is a finding, not an omission of this compilation** (OPEN-CALL 4).

**19. Proofs NOT emitted as units.** §S5.1's necessity/sufficiency → `.11`'s DERIVATION, **590 lines after** the statement it proves. §S2/§S3/§S4.1/§S4.3/§S7.2's proofs sit adjacent to their statements. **Format observation, confirming the HE7 pilot's item 23:** the DERIVATION field routinely reaches across hundreds of lines and the RESOLUTION TRACE's three slots (rule 12) are load-bearing — `.11` alone has statement lines 167–177, proof lines 849–877, and correction sites at 2897–2925 and 2927–2959, three ranges in three different thousand-line regions.

### 6.2 Merges deliberately NOT made

- **The five (I)–(IV)+GRADE pieces of GENIND.A are not merged back** even though (I) and (II) carry no rider: merging them would make the GRADE box's clause-differentiated verdict unrepresentable.
- **`.27` and `.28` stay separate** although both are `[r3]`-era records of one finding: `.28`'s conclusion survived r4 and `.27`'s parenthetical did not.
- **`.48` and `.49` stay separate** although the source lists them under one bold header: R4 riders one and explicitly not the other.
- **`.63`'s (CS-1) is not split into (CS-1) and (CS-1Q).** (CS-1Q) is homed in shard 3 (it is *stated* there, at §C2-G1); `.63` carries it as CONDITIONALITY with the chain marked TERMINAL. A merge that promoted (CS-1Q) to a unit here would duplicate shard 3's statement.
- **The four (CS-·) clauses are not merged into one “[GENIND-H]” unit** even though the note often cites the box as a whole: each has a distinct discharge status ((CS-1) de facto at n = 4; (CS-2) normalization-declared; (CS-3) fully open; (CS-EXACT) de facto at n = 4 via a different supplier half).
- **`.11` and `.43` are not merged** (GENIND.A(IV) and “the criterion in one line”): R5's rider names the former's wording and not the latter's, and the latter carries the refutation of the charge's candidate criterion, which the former does not.

### 6.3 Which v3 rules were load-bearing here (format feedback, one line each)

Recorded as evidence for the remaining prose shards (GENIND s2/s3, GENH4, GRTJB, GRTJC).

1. **Rule 18 (SUPERSESSION KIND) earned its place immediately.** This shard needed **all eight kinds**: `replacement` (`.24`, `.31`, `.37`, `.63`), `license` (`.36`, `.45`, `.46`, `.64`), `wording-rider` (`.49`, `.66`), `provenance-rider` (`.14`, `.28`, `.58`), `scope-pin` (`.04`, `.09`, `.11`, `.15`, `.61`, `.68`), `as-of scoping` (`.03`, `.05`, `.59`, `.60`), `counter re-reading` (`.01`, `.24`, `.27`, `.28`, `.39`, `.40`, `.42`), `inventory completion` (`.07`, `.13`, `.34`, `.56`, `.63`, `.74`). Several units carry **two or three kinds in one bracket chain** (`.28`, `.59`, `.63`, `.66`) — the field must be per-rider, not per-unit, and a merge should treat it as a list.
2. **Rule 25 (CHAIN + TERMINAL) is not optional in this note.** Four chains run three or more layers deep (`.01`, `.13`, `.24`, `.45`, `.59`, `.63`), and in two cases (`.63`, `.13`) the TERMINAL member is *different for different consumers* — (CS-1) is terminal-as-`[r2]`-corrected for menu consumers and terminal-as-(CS-1Q) for rate consumers. **Recommendation to the cross-read: allow a CHAIN to carry more than one TERMINAL, each labelled with its consumer class.** The v3 rule as written assumes one.
3. **Rule 22 (arithmetic audit) paid for itself repeatedly and should be extended beyond `[TABLE]`s.** This shard has **no source table at all**, yet twenty-one units carry displayed counts, exponents or identities, and recomputing them fresh (a) reproduced every scored spot value in §S11 P-3/P-4 from the displayed laws, (b) confirmed the M6 locus law against three exhaustive machine rows to the digit, (c) re-derived `4N − 5h − 3` twice by two independent routes, and (d) surfaced **one number the compiler could not reconstruct** (`.40`'s 2,128,163 total) and **one scale hazard** (`.27`/`.28`'s genre-locus counts read as state-space counts). **Recommendation: make the arithmetic audit attach to any unit displaying a count or exponent, not only to `[TABLE]`s.**
4. **Rule 12's three-slot trace is essential and still slightly short.** `.11` needs three ranges in three thousand-line regions; several units need a FOURTH slot — *re-audit sites* (§S14/§S15's claim groups, which neither state nor correct the unit but record that it was checked and kept). Filed under `correction sites` here with an explicit “re-audit” marker; **recommend a fourth slot or a documented convention.**
5. **Rule 27's AUDIT class is the right home for this note's most important findings.** Three of the arc's heaviest items — the (A2-RATE) gap (`.45`), the unit-pivot gap (`.36`), and the five consecutive record-integrity defects (`.59`) — were produced by fresh-context reads and **could not have been produced by any battery row**, since the runner and the display never disagreed numerically in any of the three. The note's own five-defect chain PE2-G2 → PE3-G1 → PE4-G1 → PE5-G1 → PE6-G1 is the strongest corpus evidence that record integrity is structurally untoothable.
6. **Rule 20's `signed vacuity disclosure` is the shard's most-used disposition** (eight enumerated instances, §5), and the single most consequential is `.65`: **(CS-3) is exercised by nothing, at any degree, anywhere in this note** — a fact that no single unit's TEETH field would have made visible without the enumerated list the rule requires.
7. **Rule 11's FORM sub-field discriminated real cases.** Of 74 units, 31 are `display`, 26 `bold-headed paragraph`, 9 `bracketed rider`, 8 `inline sentence`. **Nine units are bracketed riders that are themselves substantive statements** (`.14`, `.27`, `.28`, `.31`, `.39`, `.58`, `.59`, plus the in-situ layers at `.24` and `.63`) — in a v2 compilation these would have been invisible inside their parents.
8. **A gap in the v3 enum, surfaced here:** rule 19 splits `regression-record` into `preregistration` / `run-record` / `instrument-record`, but this shard needed a fourth: **a record whose content is an instrument's FAILURE and the diagnosis of why** (`.41`). Filed as `instrument-record`; it is not a description of the apparatus so much as of the apparatus's error. **Recommend either widening `instrument-record`'s definition explicitly or adding `instrument-failure-record`.**

---

## 7. SHARD NOTES

- **Cross-shard supersessions applied (eleven sources, all inbound to this range).**
  (1) **Dated acceptance record's PE8-m1** → `.01` (the header arc line, superseded by name; counter 0/2 → 2/2, ACCEPTED).
  (2) **ANNEX R R1** → `.13` ((A2-RATE) pins P(k)'s fourth member), `.45`/`.46` (GENIND-C1 + GENIND.C′ supply the consumed vanishing rate), `.57` (Step 4's simple part consumes C′ verbatim).
  (3) **ANNEX R R2** → `.36` (the unit-pivot license) and `.24` (step (3)'s fiber sentence — R2 names both sites).
  (4) **ANNEX R R3** → `.07` (window-1 convention), with named consumption sites `.21`, `.24`, `.34`, `.38`, `.45`.
  (5) **ANNEX R R4** → `.49` and `.11` (the CS4-F visibility floor, at both displays).
  (6) **ANNEX R R5** → `.11` (the converse read pinned to DEGREE level).
  (7) **ANNEX R R6** → `.14`, `.58` (identity-vs-bound separated), `.25`, `.37` (the monotonicity notice).
  (8) **ANNEX R — r1 (`[ar1]` layer)** → `.13`, `.45`, `.46` (the full-vs-simple complement split; GENIND-C2 supplies the CS-drain rate).
  (9) **Dated supplier-movement record (GENHN)** → `.15` (n ≥ 8 conditionality gains two conjuncts), `.35`, `.57` (per-clause survival screen), `.04`, `.61` (by inheritance).
  (10) **The two 2026-08-12 dated corrections** → `.37`, `.57`, `.63` (the `(CS-1) only` → `(CS-1Q), verified per genre` upgrade), `.13`, `.74`.
  (11) **Post-PE7 dated corrections (PE7-m2)** → `.34`, `.57` (the GENHN consumed surface completed from four sites to seven).
  **Not a supersession:** GENIND-C1(ii) and R6.1 are *consumers/analyses* of `.25`, not edits — recorded at `.25` so the merge does not install a false edge.
- **Range-edge audit.** Line 1345 is §S7.4's “so the program is finitely enumerable”; line 1347 closes it (“degree-by-degree while the SCAFFOLD stays uniform in n.”); line 1348 is blank; line 1349 opens `## S8. HONEST BOXES`. **No source statement unit is cut at the edge.** The shard boundary falls exactly on a section break.
- **Outside-HOME material used only as resolver, never inventoried here:** §S8's six honest boxes, §S9's proposed annex + downstream list + the conditionality stack, §S10's battery description and eleven preregistered predictions, §S11's verdict, §S12–§S16's five repair records (including §S14's 15-class window-site inventory, its C1–C14 claim audit, §S15's universal-sentence sweep and §S16's per-supplier fired-clause table), the post-PE7 dated corrections, the dated acceptance record, ANNEX R's R1–R6 and the ANNEX R close, the dated supplier-movement record, ANNEX R — r1's GENIND-C2 and machine record, and the two 2026-08-12 dated corrections (GENIND-C2 Q-normalized; C2-G1/G2/G3 with GENIND-C2Q and GENIND-C2D). Shards 2 and 3 own them.
- **Protocol versus supply.** §S1–§S7's supply set is inventoried; **no consumption append is claimed landed on any supplier note**, and none is invented. Two inbound supplier movements are recorded at their targets.
- **Numbering.** Temporary IDs `EFF.GENIND.s1of3.01`–`.74`, to be reconciled with shards 2 and 3 at the merge run.
- **MERGE HAZARDS TO FLAG (six).**
  1. **(CS-1) has TWO terminal readings** (`.63`): `[r2]`-corrected (CS-1) for menu/transport consumers; **(CS-1Q), verified per genre** for rate consumers. A merge that installs one edge will misstate the other consumer class. Ledger row **HYP.36**.
  2. **The effective forms of four in-range statements are homed in shard 3**: `.45`/`.46` → ANNEX-THEOREM GENIND.C′ and ANNEX-LEMMA GENIND-C1; `.13` → (A2-RATE); `.37`/`.57` → ANNEX-LEMMA GENIND-C2Q and GENIND-C2D. Wire `.45 → C′`, `.45 → C1`, `.13 → (A2-RATE)`, `.37 → C2Q`, `.57 → C2Q`, `.46 → C′` as explicit edges, or a chapter cut will read the frozen bodies as current.
  3. **`.14` and `.66` are the same clause at two displays with disjoint rider sets.** Do not deduplicate.
  4. **`.08` and `.17`(i) are the same content at two granularities** (§S1's forward display and §S2's lemma). Both are emitted; the relation is recorded at both. A merge should keep both and mark the §S1 display as the forward summary.
  5. **`.72`(OB-c) ≡ `.65`(CS-3).** Install the edge explicitly; the note treats them as the same open theorem in different words.
  6. **`.19` (GENIND-1(iii), fracture permanence) carries an EXTERNAL interface obligation the note itself does not state** — ledger row **HYP.121**, CLASS interface-generality, disposition CARRY, flagged INTERFACE (“load-bearing, unaudited”) by the Q1 generality audit. The note's own S1 convention says “O a complete DVR … either characteristic” and the proof uses no residue-characteristic hypothesis, but no pass has certified the generality and the machine leg is prime-q, d = 1. **A chapter cut must carry HYP.121 with `.19`.**

---

## 8. Self-audit and OPEN-CALLS

### OPEN-CALL 1 — `.19`'s all-`O` generality is an external obligation with no note-side sentence

Ledger row **HYP.121** (`spec/HYPOTHESIS_LEDGER.md:970–974`) states: *“GENIND-1, essential to W12-HT Step 3 and termination/compatibility, is valid over arbitrary complete DVRs. CONSUMED BY: history transfer. CLASS: interface-generality. PROPOSED DISPOSITION: CARRY.”* The Q1 audit's wording is sharper (`runs/qgen/HYPLEDGER_crossread.md:922–924`): *“INTERFACE — load-bearing, unaudited … Its generality cannot be certified here.”* **The note contains no sentence asserting or denying all-`O` generality for GENIND-1 specifically** — only the blanket S1 convention (`.07`) and GENIND-BOX-3's d ≥ 2 disclosure (`.23`). The compiler has emitted the convention and the flag and has **not** synthesized a generality claim. **Decision needed: whether the merged spec carries HYP.121 as a conditionality on `.19` (and hence on every consumer of fracture permanence: `.24`, `.25`, `.35`, `.55`), or leaves it as a ledger-side obligation.** The choice changes whether `.19`'s CONDITIONALITY field reads “unconditional” or “unconditional over complete DVRs, generality uncertified”.

### OPEN-CALL 2 — the (CS-1Q) upgrade's reach into the frozen body is not stated by any sentence

The 2026-08-12 round-2 consumer sweep (line 3718, shard 3) says: *“In R1.1's full-complement closure and GENIND-C1(iii)'s growing-window use, read the CS-drain rate as conditional on (CS-1Q), not bare (CS-1)”* and (line 3719) *“In GENIND.B Step 4 and the GENIND-6(d) mixed-drain union bound, child terms remain supplied by GENIND-C1; stage terms are supplied by GENIND-C2Q.”* **Both named targets inside the frozen body — Step 4 (`.57`) and GENIND-6(d) (`.37`) — are reached by a consumer sweep, not by a rider that quotes their text.** The compiler has carried the upgrade as CONDITIONALITY at both, quoting the sweep. **Decision needed: whether the merged spec treats a consumer-sweep bullet as a supersession of the frozen text it names (installing the edge), or as a downstream reading note (recording it without an edge).** This is a general question about the C2-G1/G2/G3 sweep format and will recur in shard 3 and in GENH4.

### OPEN-CALL 3 — LEMMA GENIND-0's closure is stated for the PRE-r4 (A1)

`.30` proves that (A1)-admissibility is closed under finite products, unions and affine re-parameterizations. **W-12's r4 round added a σ-LABELING clause inside (A1)** (§S16 row 1: “The r4 σ-LABELING clause STRENGTHENS (A1)”), and §S16 records the *consumption* of W-12.D as surviving because a strengthened hypothesis demands more of P(n) and delivers no less. **But no unit re-derives `.30`'s closure under the strengthened predicate**, and Step 1 (`.54`) and Step 2 (`.55`) both use GENIND-0 to multiply menus that must now carry σ-labels. **Not a claimed error** — the strengthening may be trivially preserved by a coordinatewise argument. Recorded because a formalization blueprint cannot assume it. **Decision needed at 0b/chapter time: whether GENIND-0's closure must be re-derived under the r4 (A1) before formalization.**

### OPEN-CALL 4 — `.73`'s preregistered predictions have no recorded outcome anywhere in the note

`.73` states two falsifiable predictions, names their falsification consequence (“a mismatch localizes to (OB-a)/(OB-b) and refutes the candidate as stated”) and hands them to QSCOUT22's table. §S9.2 states the upgrade rule (“a confirmed table upgrades GENIND-5 from candidate to corroborated-candidate”). **The scout's arc subsequently completed** — §S9.3's `[r6]` re-pin records “seal 970197d → VERDICT dd67cda (08-08 10:00, GREEN 7,614,473/0), L3-correction annex fcaf268” — **and no sentence anywhere in GENIND records whether the predictions were scored, matched, or missed.** The compiler has emitted the preregistration with an explicit UNPINNED disposition and has NOT inferred an outcome from the scout's GREEN verdict (which scores the scout's own predictions, not these). **Decision needed: whether the merged spec must carry a “preregistration with no run-record” row, and whether GENIND owes a dated append recording the outcome.**

### OPEN-CALL 5 — `.51`'s CS5-V4E2 law is derivation-only and its exponent has no independent check

`.51`'s law `(q−1)²·q^{5N−5v₄−5h−4}` is displayed once, never machine-exercised (first visible at N = 8, beyond every roster), and — unlike `.48`, `.49`, `.50` — has **no second derivation, no scored spot, and no cross-check against any other displayed number.** The compiler verified its VERTEX CONDITION and its visibility floor arithmetically (both check) but **could not verify the exponent `5N − 5v₄ − 5h − 4`** from any other datum in the note. **Decision needed: whether a derivation-only law with no arithmetic cross-check may enter a chapter cut as a displayed law, or must be re-derived first.** Recorded, not repaired.

### Recorded source defects (flagged, not silently repaired)

1. **`.23`: the battery family `GT-AGGDEEP` does not exist.** The Instances paragraph cites “(machine: GT-AGGDEEP at n = 4, 5, this battery)”. §S10's family list (shard 2) enumerates twelve families — GT-PIN, GT-PART, GT-DEPTH0, GT-BDRAIN, GT-ALPHA, GT-BETA, GT-RECUR, GT-BRACKETID, GT-CRIT, GT-N3TIE, GT-CONS, GT-ORACLE — and no `GT-AGGDEEP`; §S11 scores none. The referent is evidently GT-BRACKETID (which is exactly “LEMMA GENIND-2(b) at m ∈ {2,3,4,5}”, scored 24/24 with exponent coefficients 2/4/7/11). Carried descriptively; **not** emitted as a battery row.
2. **`.27`/`.28`: genre-locus counts are displayed in the same register as state-space counts.** “ALL 2,048 states at (2,7)” is `2^{11}`, a genre locus, while the full per-centre space at (m, q, N) = (4, 2, 7) is `2^{24}`; likewise 177,147 = `3^{11}`, 32 = `2⁵`, 512 = `2⁹`. Every figure is internally consistent (all fibre and child-space checks reproduce), but a reader or a merge that treats them as sweep totals will mis-scale by many orders of magnitude. No number moves; recorded as a reading hazard.
3. **`.39`/`.40`: the T1 tooth's (2,5) joint count is not displayed.** `.40` reports T1 firing “38/40 at (2,6) and 40/40 at (3,5)”; `.39`'s `[r3]` per-coefficient split reports three windows including (2,5). The joint figure at (2,5) appears nowhere. Consistency checks pass where both are given (38 ≤ 39; 40 = 40); recorded as a display gap.
4. **`.40`: the headline check total 2,128,163 cannot be reconstructed from the displayed rows.** The three exhaustive fibration rows sum to 2,126,803; the residual 1,360 is not itemized, and adding the 2,460 certification comparisons overshoots. The artifact `genind_annexr…`/`genindr2_supp_results.json` is the authority and is byte-frozen. **Recorded as a disclosed non-reconstruction, NOT as a discrepancy** — the compiler has no basis for calling the total wrong.
5. **`.64`: `GENH4 S6.2` is a section pointer into a note that does not carry that section number.** Fixed-string `S6.2` count **0** in `GENH4_PROOF_2026-08-08.md` (the count 6 belongs to GENHN's file). Two sentences cite it, both load-bearing for the normalization declaration. Referent carried descriptively; a precise designation would have to come from GENH4's own spec (shard-owner: the GENH4 queue).
6. **`.15`: `[GENHN-HE(μ ≥ 3)]` names no box in GENHN.** The note discloses this itself at PE7-m3 and instructs the corrected reading; carried with the note's own correction quoted. Recorded here so the merge does not re-derive it.
7. **`.32`'s honest-limit sentence is STALE as of r6** (rule 26): “the same-side f-first genre itself … remains machine-unrealized corpus-wide” was true at r5 and was falsified by PE6's corpus-first realization at r6, without the sentence being edited (it sits in the byte-frozen body). Tagged `STALE-SELF-DESCRIPTION`, not `superseded`.

### Fidelity audit

- Every CANONICAL STATEMENT is a verbatim source quotation or is explicitly marked `[ASSEMBLED]`. **No inverse, sign, quantifier, index, degree, slope, window, inequality direction, or implication direction was altered anywhere.** Where a display is quoted in two or more pieces (`.24`/`.25`, `.38`/`.39`, `.40`/`.41`, and the five pieces of GENIND.A, the four of GENIND.B, the four of GENIND-6), each piece is byte-verbatim and the union is the whole display minus nothing; every such split is flagged at the unit and audited at §6.1.
- Truncations inside quotations: **one**, at `.58`, marked `…` where the record continues into the discharge geography emitted at `.59`.
- Nested `[rN]` brackets are reproduced in place with their quoted false originals intact; no bracket is silently flattened. **The note's convention — corrections applied in place, originals preserved as dated records — is honoured throughout: nothing quoted here as “FALSE” is presented as live text.**
- **59 external XREF designations, every one grep-verified with a fixed-string count ≥ 1 recorded inline and in §3.1.** Seven candidate designations with count 0 are NOT emitted as XREFs and are recorded as NEAR-MISS dispositions (§3.1b) with their verified referents. Two `S1`/`S2.3` XREFs carry an explicit upper-bound caveat.
- **29 commit pins `git cat-file -t`-verified; 25 artifact filenames verified to exist.** One reported figure is marked UNPINNED-BY-DISPLAY (`.28`'s 972-state companion), one preregistration is marked UNPINNED (`.73`), and one total is marked non-reconstructible (`.40`).
- **Twenty-one units carry compiler-computed arithmetic audits**, all recomputed fresh from the source's own data rather than assumed from its labels. Every scored spot value in §S11's P-3/P-4 that a shard-1 law predicts was reproduced (E4(1) at three rosters, F4(1), B2Q(1), V1E2(1), the V4E2 and F4 absences, the row CS total 66,560); the M6 locus law reproduced all three exhaustive machine rows and both fibre exponents exactly; `4N − 5h − 3` was re-derived by two independent routes (`.50`'s four-coordinate sum and `.68`'s free-digit total).
- Status and mathematical content are kept as distinct predicates: the acceptance chronology governs grade (`.01`, `.16`), the note's own no-append protocol governs consumption (`.06`, §3.2), and no append is claimed landed.
- Out-of-range material is used only to resolve in-range HOME units (resolution rule 8); shards 2 and 3 own §S8–§S16, the dated records, and the whole annex stack.
- **Honest limitation of this shard:** all eleven correction sources are physically in other shards. Every affected unit quotes the governing corrective text verbatim, so shard 1 is self-contained as a *reading*, but the merge run must still install the edges listed in §7's six merge hazards.

EFF-GENIND-s1of3 COMPILED: 74 statements / 59 xrefs verified / 7 near-misses / 5 open calls
