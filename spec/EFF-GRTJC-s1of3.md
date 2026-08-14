# EFF-GRTJC-s1of3 — CANONICAL EFFECTIVE-SPECIFICATION SHARD

**COMPILED-BY: opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). CODEX CROSS-READ OWED (post-reset).**

## 1. Shard header

**Source note:** `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md` (3059 lines, 217,445 bytes).

**HOME range:** source lines **1–661** inclusive — the title, the `**Unit:**`/`**Genre:**`/`**Author:**` block, the instrument and own-machine-leg declarations, the six-member `S-STATUS` series `[r1]`–`[r6]`, the **six repair-round blocks** (in source order r6, r5, r4, r3, r1, r2 — the note's own reverse-chronological layout), **§0 INPUTS AND THE CONDITIONALITY STACK** (`(IN-1)`–`(IN-5)` and THE STACK, ONE LINE), and **§1 OBJECTS** (the definitional layer: keys, weights, residues, split, anchors, the level read and digit polynomial, the scalar lift, the TC chain and `𝒜(T)`, the harness cocycle). Later text (§2–§10, the acceptance record, Annexes #1–#3, and the 2026-08-12 sol adjudication with Annexes #4–#8) is used ONLY to resolve material homed here.

**HEAD blob hash:** `b07f08f52c1cf2d84af7e8167b8daf2f791a4f8c` (clean in the working tree; last touched by commit `e2403a2b`, “SOL cert E4 FOLDED: GRTJC”).

**Compilation context:** `spec/EFF_TEMPLATE_v2.md` at HEAD (rules 1–28); temporary IDs `EFF.GRTJC.s1of3.<nn>`.

### SHARD-COUNT RECONCILIATION (OPEN-CALL 1 — recorded, not silently resolved)

`runs/qgen/sweep_manifest.txt` lines 47–50 shard GRTJC into **FOUR** ranges (1–661, 662–1937, 1938–2802, 2803–3059); the Q7 charge names **THREE**. The compiler did not invent a fourth file and did not drop 257 lines. **Resolution applied: the manifest's rows 49+50 are MERGED into shard 3** (2803–3059 is the appended-annex tail, whose whole content supersedes statements homed in 1938–2802 and in §§2–7; splitting it from §§8–10 would put an annex and its target in different files with no unit able to carry the edge). The three-shard cover is therefore

| shard | source lines | manifest rows merged |
|---|---|---|
| **s1of3 (this)** | 1–661 | s1of4, unchanged |
| s2of3 | 662–1937 | s2of4, unchanged |
| s3of3 | 1938–3059 | s3of4 (1938–2802) + s4of4 (2803–3059) |

**Union = 1–3059, the whole note; no line is compiled twice and none is dropped.** Boundaries verified at HEAD: L660 `---`, L661 blank, L662 `## §2.`; L1936 `---`, L1937 blank, L1938 `## §8.`. **Note the contrast with GRTJB, where the merge fell at the FRONT** (rows 43+44): the merge point is chosen per note so that an annex never lands in a different shard from the whole of what it supersedes. See §8 OPEN-CALL 1.

**GENRE: TAG-SPARSE PROSE PROOF (density 0.00 in the note's own prose).** `grep -cF '\tag{'` returns **2** across all 3059 lines — but **both are LaTeX equation tags inside the sol-transcribed Annexes #4 and #6** (`\tag{W8-q}` at L2859, `\tag{RM}` at L2930, both in shard 3), not statement-boundary markers in the note's own writing. **In this shard the tag density is exactly 0.** What the range has instead: bold `**(IN-k)**` input labels, six `S-STATUS` blocks each carrying a fixed-width `ARC:` display, six bold-headed `[REPAIR ROUND rk …]` blocks with `* **G-#**` bullets, and §1's bulleted definition list. **Boundaries are chosen; §6 is the mandatory BOUNDARY SELF-AUDIT.**

### FREEZE PREDICATES (rule 21 — GRTJC carries FOUR independent freezes)

**FREEZE PREDICATE 1 — INSTRUMENT FREEZE (three batteries + the instrument, byte-frozen).** Stated identically in five round blocks; the r6 form (L179–180):

> “all three batteries, the
>                   instrument, and every artifact stay BYTE-FROZEN”

**PIN VERIFICATION (rule 23), the two md5s the note pins, re-computed at HEAD by this compiler — 2/2 EXACT:**

| script | md5 cited in-note | md5 at HEAD | verdict |
|---|---|---|---|
| `verification/openmath/grt_jc_r1_checks.py` | `7f896bfa27d06158f95c5987c7299770` (L2208) | `7f896bfa27d06158f95c5987c7299770` | **EXACT** |
| `verification/openmath/grt_jc_r2_checks.py` | `c02bf06029a72259512ea005bd2562fd` (L2319) | `c02bf06029a72259512ea005bd2562fd` | **EXACT** |

**All twelve `grt_jc_*` artifacts verified to EXIST** (`grt_jc_probe.py`/`_output.txt`/`_results.json`, `grt_jc_checks.py`/`_output.txt`/`_results.json`, `grt_jc_r1_checks.py`/`grt_jc_r1_output.txt`/`grt_jc_r1_results.json`, `grt_jc_r2_checks.py`/`grt_jc_r2_output.txt`/`grt_jc_r2_results.json`). **The r0 battery and the instrument carry no md5 pin in the note** — their freeze is asserted, not hashed. Recorded as source defect 1.

**FREEZE PREDICATE 2 — LITERATURE-PIN FREEZE (the FGMN PDF).** Annex #3 (shard 3, L2809): “Pin: `docs/references/fgmn_residual_ideals_1305.0775v3.pdf`, md5 `da846c82f1fcb619cefb3feb8164191e` (confirmed at read time).” **RE-COMPUTED AT HEAD BY THIS COMPILER: `da846c82f1fcb619cefb3feb8164191e` — EXACT.**

**FREEZE PREDICATE 3 — SWEEP-CENSUS FREEZE (a governance rule, like GRTJB's §0M rule but different in kind).** From r5/G-1 and r3/G-2, the standing discipline: **any sweep or diversity figure in this note must be a SCORED or CENSUSED fact with its unit and its committing commit, never prose** — “Standing rule from this history: any sampling-diversity claim in this note must be a SCORED or CENSUSED fact, never prose” (L2355–2357, shard 3), and “a fixed-point claim must be grepped AT the committing state” (L2410–2411, shard 3). **This shard homes the rounds that established it** (`.13`, `.23`, `.24`).

**FREEZE PREDICATE 4 — TEXT FREEZE (post-acceptance).** Annexes #1, #2, #3 each close “**No text of this note is edited**”; the 2026-08-12 adjudication head (L2831): “**Everything above this heading is byte-untouched by this append.**” **Consequence: every correction in Annexes #4–#8 is an APPEND, and this shard's frozen text must be read through them.**

### Governing effective-text record

The note states no single "the effective text is …" sentence; four statements fix it.

**(i) Supersession is IN-PLACE, strike-and-replace, never deletion** (r1 block, L355–357):

> “each edit carrying a dated `[r1, F#]` (critical) or `[r1, G#]`
> (gap) bracket, strike-and-replace (the refuted r0 wording is quoted inside the
> bracket that supersedes it, never silently deleted)”

**(ii) A struck STATUS block may be kept ANNOTATED rather than struck when it contains a display** — a device GRTJB does not use. Every `[r2]`–`[r6]` S-STATUS block says so, e.g. L44–46:

> “**[r2] S-STATUS (SUPERSEDED at r3 by the block below; kept annotated rather
> than struck because of the embedded ARC display; supersedes the r1 status line
> above, which is kept struck rather than deleted) …**”

**(iii) Round blocks appear in REVERSE CHRONOLOGICAL ORDER in the source** — r6 first (L187), then r5 (L222), r4 (L261), r3 (L304), r1 (L344), r2 (L421). **This is a genuine reading hazard and the compiler flags it: line order ≠ time order in lines 187–496.** The `ARC:` displays inside the S-STATUS blocks are the authoritative chronology.

**(iv) Post-acceptance appends supersede body text WITHOUT editing it, and Annex #7 does so EXPRESSLY** (shard 3, L3006) — unlike GRTJB, GRTJC names each stale passage. Quoted at `.05`–`.10`.

**EFFECTIVE TEXT FOR THIS SHARD = lines 1–661 exactly as written (all `[r1]`–`[r6]` brackets already landed in place, strike markup preserved), READ AS CORRECTED by the out-of-range appends wherever they name an in-range sentence.** **Three such appends land here** — Annex #1 ((DMULT-s) PROVED-conditional), Annex #3 (the FGMN cites PDF-VERIFIED), Annex #7 (the status supersession) — plus Annex #6, which withdraws a characterisation of `(IN-3)(c)` homed at `.43`. Each is applied at its unit and recorded in §7.

### Scope split (rule 7 + rule 17 — three predicates)

**A. ABSORPTION / supply SET.** The note's own headline (L1): the composite-stage graded target exists (localize + gauge, with the ℤ → ℤ/E collapse proved); TC-3 load-bearing EXACTLY at δ ≥ g_m; the anchor-transport isomorphism Ψ with the measured inner normalization ∏_{j≤m} z_j^{D_j}; harness-val = TC-read; and the cocycle semantics — **“four separately boxed clauses, each an honest proof or an honestly boxed obstruction”**. The clauses themselves (W-6, W-7, W-8, W-9) are shard 2.

**B. APPEND / consumption PROTOCOL scope. NO-APPENDS, and NO GATE RETIRES.** Stated in the header (L4–9) and repeated at the close of every S-STATUS block:

> “No `.lean` touched, no gate fires, **no gate
> retires**: DITERSUP §S3 gate J3b stays BLOCKED-ON-CARRIER-TIE (this note
> DISPLAYS the tie it would need, and by construction cannot retire it — J3b
> retires only when (J-C)(ii) survives its own hostile arc), the Asvin P0
> application gate stands, and no density/menu/count statement is made anywhere.”

**Zero dated consumption appends are claimed landed on any supplier by this note, and none is invented here.**

**C. INBOUND CORRECTIONS RECEIVED (rule 17).** **One inbound supplier correction reaches this shard's range: GRTJB's own fences**, inherited verbatim at `(IN-4)` (`.44`) — “whose JB-BOX-2 conditionality … rides in wherever a print-residual statement is used”. **In the reverse direction GRTJC is itself the consumer that GRTJB's `s2of3.54` names**, and GRTJC's §3.3 both CONFIRMS J-B's value law on 27 stages and REFUTES the brief's guess built on it. Additionally, **five post-acceptance corrections were received FROM a decorrelated certifier** (Annexes #4–#8), three of which name text homed in this shard or in §1's objects.

### Resolution rules applied

1. Lines 1–661 supply the HOME material listed under HOME range.
2. `[r1]`…`[r6]` brackets inside the range are ALREADY-LANDED text applied in place; the later bracket governs. **Read the round blocks by their `ARC:` chronology, not by line order** (rule (iii) above).
3. `~~…~~` is supersession, never deletion; struck text is quoted whenever the superseding bracket cannot be read without it. **A struck-but-ANNOTATED block (the S-STATUS series) is quoted at its annotation.**
4. Multi-layer stacks carry `CHAIN:` with TERMINAL marked (rule 25); this shard has two (`.43`/`.46`'s `(IN-3)(c)` alias chain, and `.05`–`.10`'s status series).
5. Out-of-range appends are applied as CONDITIONALITY at the in-range units they name, with the annex text quoted; **no in-range sentence is edited.**
6. Out-of-range statements are NOT emitted as units here. Shard 2 owns §§2–7; shard 3 owns §§8–10, the acceptance record and all five annexes.
7. External repo records are reading notes only.
8. **CITE-SCOPE rows are compiled AS THE NOTE STATES THEM**, with `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` **NS-9/NS-10** recorded as READING NOTES at `.43`. **Recorded, not applied.**

### Quotation and table discipline

CANONICAL STATEMENTs are verbatim or `[ASSEMBLED]`; truncation marked `…`. **The six `ARC:` displays are fixed-width blocks and are DOUBLE-EMITTED** (rule 14) — once verbatim at the TERMINAL series member, once as a compiler `[TABLE]` covering the whole series with an arithmetic audit. §1's definition bullets are quoted with their displays intact. Compiler ledgers are flagged `[TABLE — compiler ledger]`.

---

## 2. Statement inventory

### EFF.GRTJC.s1of3.01  [scope record]

**CANONICAL STATEMENT:** verbatim, line 1.
**FORM:** display (the note's H1 title).

> “# GRTJC — J-C, THE CARRY-ALGEBRA JUNCTION (W-6..W-9): the composite-stage graded target exists (localize + gauge, with the ℤ → ℤ/E collapse proved), TC-3 is load-bearing EXACTLY at δ ≥ g_m (theorem, not observation), the anchor-transport isomorphism Ψ with the measured inner normalization ∏_{j≤m} z_j^{D_j}, harness-val = TC-read, and the cocycle semantics — four separately boxed clauses, each an honest proof or an honestly boxed obstruction”

**CONDITIONALITY:** Five supply items, each fenced differently in shard 2. **Two are corrected from shard 3:** “TC-3 is load-bearing EXACTLY at δ ≥ g_m” is re-displayed by **Annex #5** (the outer factor is *always* `q(y^δ) = z̄^δ`; it is *unavailable as a pre-TC-3 scalar* exactly when `δ ≥ g_m`), and “harness-val = TC-read” is re-proved by **Annex #4** as a quotient computation, conclusion unchanged. **“the measured inner normalization” is honest wording**: OB-3's VALUE rides `[ILN]†`'s scored stratum and the sharp form rides the MEASURED tier `(DMULT-s)`.

**DERIVATION:** Not a mathematical unit; the title is the supply headline. Discharged at §2 (W-6), §3 (W-7), §4 (W-8), §5 (W-9) — all shard 2.

**RESOLUTION TRACE:** statement line 1; proof lines 662–1843 (shard 2); correction sites 2840–2884 (Annex #4), 2890–2911 (Annex #5) — shard 3.

XREF: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md:ITER-LAW-n` — grep-verified count **11**.

**TEETH:** composite — the instrument (22 families) plus three own batteries (§9, shard 3).

---

### EFF.GRTJC.s1of3.02  [scope record]

**CANONICAL STATEMENT:** verbatim, lines 3–10.
**FORM:** bold-headed paragraph.

> “**Unit:** GRTJC COMPOSER (Phase 1 of `docs/in-progress/GRTJC_BRIEF_2026-08-05.md`,
> dispatched on the instrument's verdict). **Genre: PROOF NOTE at attempt grade —
> own acceptance counter 0/2.** No `.lean` touched, no gate fires, **no gate
> retires**: DITERSUP §S3 gate J3b stays BLOCKED-ON-CARRIER-TIE (this note
> DISPLAYS the tie it would need, and by construction cannot retire it — J3b
> retires only when (J-C)(ii) survives its own hostile arc), the Asvin P0
> application gate stands, and no density/menu/count statement is made anywhere.
> **Author:** Fable composer unit, campaign date 2026-08-08 (wallclock 2026-08-05).”

**CONDITIONALITY:** **STALE-SELF-DESCRIPTION on the grade (rule 26), and — unlike GRTJB — EXPRESSLY SUPERSEDED.** Annex #7 (shard 3, L3006–3008):

> “The ★ ACCEPTANCE RECORD (orchestrator, 2026-08-06) ★ expressly **supersedes**
> `[r6] S-STATUS (CURRENT)`, §10.1's “acceptance counter 0/2,” every body-local
> “JC-PE7 next” phrase, and every body-local prohibition on proof-grade
> consumption that is based solely on this note's former 0/2 counter. Those
> passages are ROUND-RECORDS describing the state after r6 and before PE7/PE8;
> their word “CURRENT” is no longer live. … **Current status at HEAD:** this note
> is **ACCEPTED at 2/2**, conditionally on exactly the input stack and fences
> named by the Acceptance Record together with the post-acceptance corrections in
> Annexes #4–#8.”

**SUPERSESSION KIND:** `replacement` (the grade), executed by an express status annex. **The three GATE clauses are NOT superseded and are LIVE at HEAD:** J3b stays BLOCKED-ON-CARRIER-TIE, the P0 gate stands, no density/menu/count statement is made. **Annex #7 says so in its own last sentence: “Acceptance of this note does not upgrade any upstream ATTEMPT-grade input or remove any displayed scope fence.”**

**DERIVATION:** Declaration.

**RESOLUTION TRACE:** statement lines 3–10; status superseded 3004–3008 (Annex #7, shard 3); the acceptance record 2787–2799 (shard 3); the gate's own consumer entry 2752–2759 (§10.3, shard 3).

XREF: `docs/in-progress/GRTJC_BRIEF_2026-08-05.md` — **file EXISTS** (path pin).

**TEETH:** NONE (declaration).

---

### EFF.GRTJC.s1of3.03  [instrument-record]  ★ the instrument, and its REFUTATION of the brief

**CANONICAL STATEMENT:** verbatim, lines 12–21.
**FORM:** bold-headed paragraph.

> “**Instrument consumed:** `lean/notes/openmath/GRTJC_PROBE_2026-08-08.md` (seal
> `7212e56` → verdict `fc89b03`; runner `verification/openmath/grt_jc_probe.py`):
> 29 towers, m ∈ {1,2,3}, 669 scored pairs, **22 families all GREEN, 0
> violations**, all 29 rows EXHAUSTIVE (structure constant determined with zero
> witness input from the harness side; per-pair uniqueness machine-proved). Its
> five measurements M1–M5 are this note's structure constants. **Its refutation is
> honored:** the brief's germ hypothesis ("the inner normalization factor at
> general m is −z_{m+1}") is reading H-D and FAILS on 138/669 pairs; the measured
> inner factor is ∏_{j=1}^{m} z_j^{D_j} — the INNER letters. This note proves the
> instrument's law, not the brief's guess.”

**TYPE JUSTIFICATION (rule 19):** `instrument-record` — the apparatus and its standing. The `run-record`s are §9 (shard 3).

**★ THE DEFINING FACT OF THIS NOTE, and it belongs at the top of any chapter cut:** **the brief's own hypothesis was REFUTED by the instrument before the proof was written, and the note proves the measured law instead.** “This note proves the instrument's law, not the brief's guess.” **The refuted reading is H-D — “the inner normalization factor at general m is −z_{m+1}” — which is exactly the letter GRTJB's carry-seed remark supplies** (`spec/EFF-GRTJB-s2of3.md` `.54`). **So the J-B ↔ J-C interface is precisely where the brief went wrong**, and §3.3 (shard 2) splits it honestly: CONFIRMED as a value law on 27 eligible `g_m = 1` stages; REFUTED as OB-3's inner factor on 138/669 pairs.

**CONDITIONALITY:** “all 29 rows EXHAUSTIVE (structure constant determined with **zero witness input from the harness side**; per-pair uniqueness machine-proved)” is the tautology-fence property §3.5 (shard 2) rests on. **The instrument carries no md5 pin in the note** (source defect 1).

**ARITHMETIC AUDIT (rule 22):** 138 of 669 pairs ⇒ H-D holds on **531** — so the refuted reading is right on ~79% of pairs and wrong on ~21%. **That is why a numerical spot-check could have missed it and why the exhaustive determination mattered.** Cross-check: §3.2 (shard 2) reports H-B fails on **215** pairs and H-C on **73** — three rival readings, three distinct failure counts, all from the same 669. ✔

**PIN VERIFICATION:** `7212e56` → `git cat-file -t` = **commit**; `fc89b03` → **commit**; `GRTJC_PROBE_2026-08-08.md` **EXISTS**; `verification/openmath/grt_jc_probe.py` **EXISTS** (+ `_output.txt`, `_results.json`).

**DERIVATION:** Instrument description.

**RESOLUTION TRACE:** statement lines 12–21; the honest split 1525–1548 (§3.3, shard 2); the structural explanation 1497–1501 (§3.2, shard 2); the J-B side `spec/EFF-GRTJB-s2of3.md` `.54`.

**TEETH:** 22 families GREEN, 669 scored pairs, **all 29 rows EXHAUSTIVE with zero harness-side witness input**. Disposition: **executable regression on a decorrelated determination** — the strongest architectural property in the note.

---

### EFF.GRTJC.s1of3.04  [instrument-record]  the note's own battery

**CANONICAL STATEMENT:** verbatim, lines 23–32.
**FORM:** bold-headed paragraph.

> “**Own machine leg:** `verification/openmath/grt_jc_checks.py` (two-commit seal;
> predictions §9.1 sealed BEFORE the run at commit `6ad01d1`) — it tests THIS
> note's clauses, not the instrument's: the slot-span theorem, the scalar-image
> lemma, the ψ-kernel witness, the fibred-index bijection, the cocycle identity,
> the cyclic-genre law, with five planted teeth. **VERDICT (§9.2): 10 families,
> 8,566 scored samples, 0 violations, all five teeth fired (1,054 firings),
> 29 rows, 2.0 s** — including the note's own new sharp prediction (slot set of an
> anchor product == {δ}) at **609/609**, and one battery-driven correction applied
> to §6(d) (the cyclic law's converse is FALSE — 13 collapse-geography rows are
> NOT-CYCLIC).”

**CONDITIONALITY:** **The separation is the point: this battery tests THIS note's clauses, not the instrument's.** **And it produced a correction against the note's own draft law** — the converse of JC-CYC(d) is FALSE, 13 collapse-geography rows are NOT-CYCLIC. **A battery that disconfirmed its author.**

**ARITHMETIC AUDIT (rule 22) — checked against §9.2 (shard 3):** the §9.2 verdict table's family samples are EXT-GATE 1 + JC1 2,594 + JC2 570 + JC3 2,484 + JC3-FLAT 24 + JC4 443 + JC5 855 + JC6 116 + JC7 581 + JC8 898 = **8,566** ✔ **matches the headline exactly.** Teeth firings: MJ1 103 + MJ2 285 + MJ3 4 + MJ4 29 + MJ5 633 = **1,054** ✔ **matches exactly.** **Both headline figures are reconstructible from the note's own table — in contrast to GRTJB's §7.1, whose 6,700 is not.** ✔

**PIN VERIFICATION:** `6ad01d1` → **commit**; `grt_jc_checks.py`, `grt_jc_checks_output.txt`, `grt_jc_checks_results.json` **all EXIST**. **No md5 pin is given for this runner** (source defect 1).

**DERIVATION:** Instrument description.

**RESOLUTION TRACE:** statement lines 23–32; the verdict 2109–2158 (§9.2, shard 3); the sealed predictions 2062–2107 (§9.1, shard 3); the §6(d) correction 1890–1902 (shard 2).

**TEETH:** 10 families, 0 violations, **all five planted teeth fired**; the sharp new prediction 609/609. Disposition: **executable regression + planted mutants, all fired**.

---

### EFF.GRTJC.s1of3.05 — .10  [SERIES: `S-STATUS`, six dated members]  [run-record ×6]

**SERIES DECLARATION (rule 28).** Lines 34–185 carry **six** dated `S-STATUS` blocks, `[r1]`…`[r6]`, in source order and in time order. **The note uses TWO retention devices, and the distinction is load-bearing:** `[r1]` is **STRUCK** (`~~…~~`); `[r2]`–`[r6]` are **KEPT ANNOTATED, not struck**, each saying why — “kept annotated rather than struck because of the embedded ARC display”. **A merge run must not treat an annotated block as live text.** Emitted as six units with membership and order recorded. **TERMINAL member: `.10` (`[r6]`), and it is EXPRESSLY superseded by Annex #7.**

`[TABLE — compiler ledger]` **The series.**

| unit | member | source lines | retention | passes run | rounds applied | the pass it answers | that pass's verdict |
|---|---|---|---|---|---|---|---|
| `.05` | `[r1]` | 34–42 | **STRUCK** | ONE | 1 | JC-PE1 (`1a27be3`) | **2 CRITICAL + 8 gaps, NOT CLEAN** |
| `.06` | `[r2]` | 44–60 | annotated | TWO | 2 | JC-PE2 (`4a76d52`) | 0C + 9 gaps — “the structural repair itself survives a full hostile re-derivation … **no false statement**” |
| `.07` | `[r3]` | 62–84 | annotated | THREE | 3 | JC-PE3 (`e4b6fbf`) | 0C + 8 gaps — “every gap is a labelling, disclosure, or record defect” |
| `.08` | `[r4]` | 86–113 | annotated | FOUR | 4 | JC-PE4 (`d5072b6`) | 0C + 4 gaps — “the r3 diff itself is sound and every machine-checkable figure it added is exact”; **all four gaps sit in what r3 left untouched** |
| `.09` | `[r5]` | 115–147 | annotated | FIVE | 5 | JC-PE5 (`b38f3f4`) | 0C + 2 gaps + 1 minor — “the r4 diff's mathematics is EXACT … both gaps are in the census/stack RECORD surface, not in any proof” |
| `.10` | `[r6]` | 149–185 | **annotated, CURRENT** | SIX | 6 | JC-PE6 (`66760f6`) | 0C + 1 gap — “the r5 diff's substance is exact, everywhere I could machine-check it”; the gap is **r5-bred**, entirely in the pointer RECORD |

**Double-emission (rule 14) — the TERMINAL member's `ARC:` display, verbatim (lines 153–183):**

>     ARC:  composed (seal 6ad01d1 -> verdict 8f07904)
>       ->  JC-PE1  (GRTJC_passPE1_report.md, 1a27be3)   2 CRITICAL + 8 gaps
>       ->  r1      STRUCTURAL repair (85d5811/54904cc; mini-seal f45b63c/66263ce)
>       ->  JC-PE2  (GRTJC_passPE2_report.md, 4a76d52)   0 CRITICAL + 9 gaps
>       ->  r2      LABELLING + FOOTPRINT + one new machine leg
>                   (5742e25; mini-seal 79611a4/db12666)
>       ->  JC-PE3  (GRTJC_passPE3_report.md, e4b6fbf)   0 CRITICAL + 8 gaps
>       ->  r3      NOTE-ONLY: re-route + disclosure + record corrections
>                   (126c33f)
>       ->  JC-PE4  (GRTJC_passPE4_report.md, d5072b6)   0 CRITICAL + 4 gaps
>       ->  r4      NOTE-ONLY: the final alias sweep + arc and tier bookkeeping
>                   (edbb966)
>       ->  JC-PE5  (GRTJC_passPE5_report.md, b38f3f4)   0 CRITICAL + 2 gaps
>                                                        + 1 minor
>       ->  r5      NOTE-ONLY: three record repairs (per-alias census table;
>                   FGMN (a)(b) at the stack displays; "nonzero" at §2.8)
>                   (3870bc8)
>       ->  JC-PE6  (GRTJC_passPE6_report.md, 66760f6)   0 CRITICAL + 1 gap
>                   — "the r5 diff's substance is exact, everywhere I could
>                     machine-check it"; the one gap is r5-bred, entirely in
>                     the pointer RECORD …
>       ->  r6      THIS round: NOTE-ONLY (the two-edit pointer repair PE6
>                   prescribed …)
>       ->  JC-PE7  = the next acceptance attempt (a fresh hostile pass on THIS
>                     post-r6 text)

**CANONICAL STATEMENT of the TERMINAL member `.10`:** verbatim, lines 149–151 and 184–185 (the head and tail; the `ARC:` display is quoted above).

> “**[r6] S-STATUS (CURRENT; supersedes the [r5] status block above): attempt
> grade, acceptance counter 0/2, SIX hostile passes RUN and SIX repair rounds
> applied.**”

> “A repair round is NOT a pass, so the counter stays **0/2**. No gate fires, none
> retires; no `.lean` touched; no density/menu/count statement anywhere.”

**SUPERSESSION KIND:** `replacement` (each member supersedes its predecessors), with the retention device varying — `.05` struck, `.06`–`.10` annotated.

**★ CONDITIONALITY — EXPRESSLY SUPERSEDED, and this is where GRTJC differs sharply from GRTJB.** Annex #7 (shard 3, L3006) names `[r6] S-STATUS (CURRENT)` **by designation** and declares it superseded, adding: “Those passages are ROUND-RECORDS describing the state after r6 and before PE7/PE8; **their word ‘CURRENT’ is no longer live.**” **Current status at HEAD: ACCEPTED at 2/2** (PE7 `782000e` CLEAN, PE8 `9d240b6` CLEAN). **The three gate clauses are NOT superseded** (Annex #7's own last sentence). **Tag: `superseded`, NOT `STALE-SELF-DESCRIPTION`** — and the difference is exactly what GRTJB's OPEN-CALL 1 asks for.

**MANDATORY ARITHMETIC AUDIT (rule 22) — the arc, cross-checked three ways:**
- Passes: PE1…PE6 = **6** ✔ matches “SIX hostile passes RUN”; rounds r1…r6 = **6** ✔.
- Verdicts across the six members: 2C+8G, 0C+9G, 0C+8G, 0C+4G, 0C+2G+1m, 0C+1G — **identical in all six blocks' cumulative recitals** ✔ and **identical to §10.1's arc** (shard 3, L2632–2649) ✔ and **identical to the acceptance record's “Full arc”** (shard 3, L2791–2793) ✔. **Three independent statements, all consistent.**
- **Trend:** criticals 2 → 0 from PE2 onward; gaps 8 → 9 → 8 → 4 → 2 → 1. **Monotone to zero from PE3.**
- Total with the clean passes: PE1…PE8 = **8 hostile passes, 6 repair rounds** ✔ matches the acceptance record's “Eight hostile passes, six repair rounds”.
- **Commit census: 23 distinct hashes named across the series and the round blocks; `git cat-file -t` returns `commit` for ALL 23** — `7212e56 fc89b03 6ad01d1 8f07904 1a27be3 6ed4680 85d5811 54904cc f45b63c 66263ce 4a76d52 5742e25 79611a4 db12666 e4b6fbf 126c33f d5072b6 edbb966 b38f3f4 3870bc8 66760f6 782000e 9d240b6`. **23/23 EXACT.**
- **Report files: `GRTJC_passPE1_report.md` … `GRTJC_passPE6_report.md` verified to EXIST (6/6).** PE7 and PE8 are pinned by commit only (see source defect 2).

**DERIVATION:** Round-arc records. The mathematical content each round moved is homed at its own repair-round unit (`.11`–`.39`).

**RESOLUTION TRACE:** statement lines 34–185; the arc re-stated at 2605–2649 (§10.1, shard 3) and 2791–2793 (the acceptance record, shard 3); **status expressly superseded at 3004–3008 (Annex #7, shard 3)**.

**TEETH:** the three batteries + the instrument, byte-frozen and re-run at exit 0 in every round; **2/2 md5 pins EXACT at HEAD**.

---

### EFF.GRTJC.s1of3.11  [run-record]  REPAIR ROUND r6 — the two-edit pointer repair

**CANONICAL STATEMENT:** verbatim, lines 187–220.
**FORM:** bold-headed bracketed block + one `* **G-1**` bullet.

> “**[REPAIR ROUND r6 — 2026-08-08 campaign (wallclock 2026-08-06). NOTE-ONLY.**
> Applied against JC-PE6 (`GRTJC_passPE6_report.md`, commit `66760f6`: **0
> CRITICAL + 1 gap** — PE6 reproduced the r5 per-alias contribution table to the
> last digit (18/18 numbers by independent grep at `edbb966`, the four
> `4.8`-only lines verified at source with their dispositions), verified the
> [r5, G-2] consumption attribution source-true line by line, re-derived the
> m-1 warrant decorrelated (JC-SCAL from REALIZE R1/R2/R3 + a fresh 6-row
> numeric leg, 0 exceptions), re-ran the union grep at HEAD (172; zero new
> refuted-content lines), found the arc system consistent (18/18 hashes), and
> re-ran all three batteries + the instrument at exit 0, stdouts byte-identical
> on r0/r2/instrument). The one gap lives entirely in the pointer RECORD; no
> measured quantity moves at r6; nothing in `verification/` is touched.
> Disposition, keyed `[r6, G-1]`:
>
> * **G-1 (the stale pointer r5's own re-classification created)** — r5
>   declared §10.2's [r1]/[r2] stack displays ROUND-RECORDS and completed §0's
>   display in place, but §0's [r4, G-1] bracket still said, un-annotated and
>   in the present tense, that those displays are "the current stacks …
>   which supersede this display" — both clauses inverted at HEAD — while the
>   new [r5, G-2] parenthetical said [r4, G-1] quotes them "as such" [as
>   round-records], which it did not (it cited them as current and
>   superseding). The two edits PE6 prescribed, per the arc's own
>   dated-annotation convention …: (i) a dated
>   [r6, G-1] annotation inside §0's [r4, G-1] bracket stating the post-r5
>   truth …; (ii) the [r5, G-2] parenthetical's "as such" struck
>   and replaced by what [r4, G-1] actually does … Plus the
>   one-liner PE6 noted but did not weight: the §9.5 group-12 audit line's
>   "the current stack" gains an [r6] as-of pin …”

**SUPERSESSION KIND:** `as-of scoping` — a present-tense pointer annotated with the date at which it was true.

**★ BRED-DEFECT RECORD (the marker shards of GRTJB recommend).** **The gap r6 repairs was CREATED BY r5's own re-classification.** r5 declared two displays ROUND-RECORDS; a bracket written at r4 still described them in the present tense as “current” and “superseding”. **Neither round was wrong when written; the combination was.** **This is the third such instance in the GRT weld corpus** (cf. GRTJB's r2/G2-1 certification and its r6/m-1 overclaim).

**CONDITIONALITY:** **NOTE-ONLY; no measured quantity moves; nothing in `verification/` is touched.** PE6's own verification is itemised and is unusually thorough: an independent grep reproducing 18/18 numbers, a decorrelated re-derivation of the m-1 warrant, a union grep at HEAD, an arc-system hash check, and all four instruments re-run byte-identically.

**PIN VERIFICATION:** `66760f6` → **commit**; `edbb966` → **commit**; `GRTJC_passPE6_report.md` **EXISTS**.

**DERIVATION:** Round record + a pointer-consistency argument.

**RESOLUTION TRACE:** statement lines 187–220; the target bracket 587–602 (`.46`); the §10.2 displays 2727–2748 (shard 3); the §9.5 as-of pin 2580–2582 (shard 3).

**TEETH:** PE6's 18/18 independent grep reproduction and the byte-identical re-runs. Disposition: **AUDIT — in-house hostile pass** (a pointer defect no battery can see) + **arithmetic recount**.

---

### EFF.GRTJC.s1of3.12  [run-record]  REPAIR ROUND r5 — header

**CANONICAL STATEMENT:** verbatim, lines 222–233.
**FORM:** bold-headed bracketed block opener.

> “**[REPAIR ROUND r5 — 2026-08-08 campaign (wallclock 2026-08-06). NOTE-ONLY.**
> Applied against JC-PE5 (`GRTJC_passPE5_report.md`, commit `b38f3f4`: **0
> CRITICAL + 2 gaps + 1 minor**, both gaps in the census/stack RECORD surface —
> PE5 re-derived the [r4, G-3] b_× re-tiering from the note's own lemmas and
> found it EXACT, re-executed the union census independently at HEAD
> (144 = 42/28/74 bucket for bucket, all twelve content groups reproduced,
> zero live hits stating the refuted content), verified the arc-accounting
> system CONSISTENT for the first time in the arc (16/16 hashes), and re-ran
> all three batteries + the instrument at exit 0, byte-identical). No measured
> quantity moves at r5; nothing in `verification/` is touched. Dispositions,
> each edit carrying an `[r5, G-#]` or `[r5, m-1]` bracket keyed to PE5's
> findings:”

**CONDITIONALITY:** **“verified the arc-accounting system CONSISTENT for the first time in the arc” is a notable admission** — the arc bookkeeping had been inconsistent through r4. **PE5 re-executed the union census INDEPENDENTLY at HEAD and reproduced it bucket for bucket (144 = 42/28/74)** — a decorrelated confirmation of r4's own count.

**ARITHMETIC AUDIT (rule 22):** 42 + 28 + 74 = **144** ✔ matches the r4 census total (`.17`).

**PIN VERIFICATION:** `b38f3f4` → **commit**; `GRTJC_passPE5_report.md` **EXISTS**.

**DERIVATION:** Round record.

**RESOLUTION TRACE:** statement lines 222–233; the dispositions 235–259 (`.13`–`.15`); the census 2476–2532 (shard 3).

**TEETH:** PE5's independent census re-execution + byte-identical instrument re-runs. Disposition: **accepted-with-decorrelation-supplied**.

---

### EFF.GRTJC.s1of3.13  [supplier-finding]  ★ r5/G-1 — the census species' THIRD recurrence, inside the block written to end it

**CANONICAL STATEMENT:** verbatim, lines 235–246.
**FORM:** bold-headed bullet.

> “* **G-1 (the [r3, G-2] species' THIRD recurrence, inside the block written
>   to end it)** — the r4 census's completeness parenthetical was FALSE on its
>   own grep: `4.8` contributes FOUR hit-lines of its own (union-minus-`4.8`
>   returns 140, not 144: L383 + L401 LIVE in group 1, L1801 LIVE in group 10,
>   L1782 STRUCK — line numbers at `edbb966`), not "RECORD by construction".
>   The clause is struck and the remark restated the census way — a PER-ALIAS
>   CONTRIBUTION TABLE, every number from the grep, with unit (hit-lines) and
>   commit (`edbb966`), at §9.5 [r5, G-1]. The census's recorded totals
>   144 = 42 LIVE + 28 STRUCK + 74 RECORD are a decomposition invariant of
>   that same grep and are UNCHANGED; the species' cure (census-not-prose) is
>   now applied to the census's own protocol remark, the one place it had not
>   reached.”

**SUPERSESSION KIND:** `counter re-reading` — a prose redundancy claim refuted by two greps.

**★ BRED-DEFECT / SPECIES RECORD.** **The defect recurred INSIDE the block written to end the species.** The note names the species and its three instances explicitly (r3/G-2 → r4/G-1 → r5/G-1), and states the cure as a standing rule: **“every number from the grep, with unit (hit-lines) and commit”**. **This is FREEZE PREDICATE 3.**

**ARITHMETIC AUDIT (rule 22):** union = 144; union-minus-`4.8` = 140 ⇒ `4.8` contributes **4** exclusive hit-lines ✔; the four are itemised (L383, L401 LIVE group 1; L1801 LIVE group 10; L1782 STRUCK) = **4** ✔; **3 LIVE + 1 STRUCK = 4** ✔. Totals 42 + 28 + 74 = **144, UNCHANGED** ✔ — the correction is to the REMARK, not the buckets, and the note says so.

**CONDITIONALITY:** **The buckets and totals were RIGHT; only the redundancy remark was wrong.** The note is careful to say so — “so the buckets and totals were right; only the redundancy REMARK was wrong” (shard 3, L2509–2511).

**DERIVATION:** Two greps at a named commit.

**RESOLUTION TRACE:** statement lines 235–246; the per-alias table 2476–2516 (shard 3); the species' first two instances 320–324 (r3/G-2, `.23`) and 271–282 (r4/G-1, `.17`).

**PIN VERIFICATION:** `edbb966` → **commit**. The four cited line numbers are “at `edbb966`”, i.e. against a historical state; **not re-verified at that commit by this compiler** (recorded as a checkable pin).

**TEETH:** **AUDIT — arithmetic recount** (rule 27). PE6 later “reproduced the r5 per-alias contribution table to the last digit (18/18 numbers by independent grep)”. Disposition: **accepted-with-decorrelation-supplied**.

---

### EFF.GRTJC.s1of3.14  [changes-record]  r5/G-2 — the FGMN footprint completed at the stack displays

**CANONICAL STATEMENT:** verbatim, lines 247–255.
**FORM:** bold-headed bullet.

> “* **G-2 (the unrepaired half of PE4's GAP 1)** — every one-line stack
>   display omitted the consumed FGMN clauses (a)/(b) from the cited
>   footprint, while the r4 census itself certifies those consumptions LIVE
>   (groups 2, 4, 6: JC-DOM, JC-LOC/G6, (MULT-B)). §0's live one-liner now
>   carries (a)(b) in place [r5, G-2 at §0]; §10.2's r0/[r1]/[r2] stack
>   displays are ROUND-RECORDS and carry the completion by ANNOTATION, not
>   edit (§10.2 [r5, G-2], which also displays the current stack with the
>   completed FGMN entry). Nothing false was concluded; the summary displays
>   understated the literature footprint by two consumed clauses.”

**SUPERSESSION KIND:** `inventory completion` — two consumed literature clauses added to a footprint display that omitted them.

**CONDITIONALITY:** **“Nothing false was concluded; the summary displays UNDERSTATED the literature footprint by two consumed clauses.”** The direction is conservative — the note was claiming a SMALLER literature dependence than it had. **The r4 census is what proved the consumptions live** (groups 2, 4, 6), which is the census discipline paying off.

**★ THIS IS THE RE-CLASSIFICATION THAT BRED r6's GAP** (`.11`): declaring §10.2's displays ROUND-RECORDS is what made §0's `[r4, G-1]` bracket's present-tense description false.

**DERIVATION:** The census's own LIVE groups.

**RESOLUTION TRACE:** statement lines 247–255; the §0 completion 574–586 (`.46`); the §10.2 annotation 2727–2748 (shard 3); the census groups 2547–2563 (shard 3); the bred gap 201–220 (`.11`).

XREF: `docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt` — **file EXISTS** (the source of (a)/(b)).

**TEETH:** the r4 census (**AUDIT — arithmetic recount**), reproduced by PE6 18/18.

---

### EFF.GRTJC.s1of3.15  [changes-record]  r5/m-1 — “nonzero” at §2.8

**CANONICAL STATEMENT:** verbatim, lines 256–259.
**FORM:** bold-headed bullet.

> “* **m-1** — §2.8's re-set RHS display gains the word "nonzero"
>   ({nonzero polynomials of degree < g_m} is the attained set for c ∈ K^*,
>   as the [r4, G-3] bracket's own parenthetical already stated); the iff is
>   unaffected (the LHS b_×·u·y^δ is nonzero).”

**SUPERSESSION KIND:** `wording-rider` — one word restoring a quantifier the display had silently widened.

**CONDITIONALITY:** **The iff is unaffected** and the note says why: the LHS `b_×·u·y^δ` is nonzero, so admitting the zero polynomial on the RHS changed nothing about solvability. **But the correction matters downstream**: **Annex #8** (shard 3) later generalises exactly this point into a scope repair on `Λ_N` and JC-SCAL — “No value `Λ_N(0)` is supplied by REALIZE. The zero polynomial represents the zero class and has zero read, but it does not have weight `N`.” **So r5/m-1 is the first symptom of the defect Annex #8 fixes properly.**

**DERIVATION:** The attained set of `𝑅_N(Λ_N(c))` for `c ∈ K^*` is the NONZERO degree-`< g_m` polynomials (JC-SCAL(a): the representative packs back to `c` under R3, so `c ≠ 0` forces it nonzero).

**RESOLUTION TRACE:** statement lines 256–259; the target display 900–907 (shard 2); the generalised repair 3014–3037 (Annex #8, shard 3).

**TEETH:** `jc4` / `R1-SURJ` (the scalar-image families); Annex #8 notes their counts stand but “evidence only defined nonzero lifts and nonzero polynomial targets”.

---

### EFF.GRTJC.s1of3.16  [run-record]  REPAIR ROUND r4 — header

**CANONICAL STATEMENT:** verbatim, lines 261–269.
**FORM:** bold-headed bracketed block opener.

> “**[REPAIR ROUND r4 — 2026-08-08 campaign (wallclock 2026-08-06). NOTE-ONLY.**
> Applied against JC-PE4 (`GRTJC_passPE4_report.md`, commit `d5072b6`: **0
> CRITICAL + 4 gaps**, all in what r3 left untouched — PE4 re-derived the r3
> re-route at both §2.8 sites, reproduced the r3 alias census EXACTLY
> (90 = 23/25/42, bucket for bucket), verified every r3-added figure
> machine-exact, and re-ran all three batteries + the instrument byte-identically
> at exit 0). No measured quantity moves at r4; nothing in `verification/` is
> touched. Dispositions, each edit carrying an `[r4, G-#]` bracket keyed to
> PE4's gap numbers:”

**ARITHMETIC AUDIT (rule 22):** 23 + 25 + 42 = **90** ✔ matches the r3 census total (`.23`). **PE4 reproduced it bucket for bucket** — a decorrelated confirmation.

**CONDITIONALITY:** **“all in what r3 left untouched”** — the pattern that repeats across this arc: each round's gaps sit in the surface the previous round did not sweep.

**PIN VERIFICATION:** `d5072b6` → **commit**; `GRTJC_passPE4_report.md` **EXISTS**.

**DERIVATION:** Round record.

**RESOLUTION TRACE:** statement lines 261–269; the dispositions 271–302 (`.17`–`.20`).

**TEETH:** PE4's exact census reproduction + byte-identical re-runs. Disposition: **accepted-with-decorrelation-supplied**.

---

### EFF.GRTJC.s1of3.17  [supplier-finding]  ★ r4/G-1 — the FOURTH alias, and the union-pattern sweep

**CANONICAL STATEMENT:** verbatim, lines 271–282.
**FORM:** bold-headed bullet.

> “* **G-1 (the FOURTH alias — the species ended the census way)** — §0's "THE
>   STACK, ONE LINE" still cited the re-routed input as "FGMN (c)(d)(e) CITED":
>   a live conditionality display under a fourth alias matching NONE of the
>   swept names, un-superseded since r0. (c) is STRUCK from that display, with
>   the bracket saying what is true (its content is consumed in this note only
>   as (DMULT-w) via JC-LOC, on B — §10.2's [r1]/[r2] stacks are the current
>   form). And the sweep protocol is widened one final time, to the UNION
>   pattern over every name the input has ever carried in this note —
>   `(IN-3) | Thm 4.2 | Theorem 4.2 | FGMN | 4.8 | Cor 2.7 | (COORD) | (MULT)`
>   (the last two excluding `-B` forms) — with the complete census recorded in
>   §9.5 [r4, G-1] and, the PE4 upgrade, every LIVE hit audited **by content**
>   (what the line SAYS), not only by name.”

**SUPERSESSION KIND:** `counter re-reading` (the fourth alias struck) + `inventory completion` (the sweep pattern widened to a union).

**CHAIN (rule 25) — the `(IN-3)(c)` alias chain, FOUR layers:**
1. **r1/F1** — `(IN-3)(c)`-on-`gr` REFUTED (CRITICAL 1); the coordinate calculus re-based on `B`.
2. **r2/G-4** — every live site naming the STRUCK `(COORD)`/`(MULT)` re-pointed; grep to fixed point.
3. **r3/G-1** — the sweep was **ALIAS-BLIND**; `(IN-3)(c)`-by-name survived at two sites; re-routed; pattern widened.
4. **r4/G-1** — a **FOURTH** alias found in §0's stack one-liner; struck; pattern widened to the UNION and the LIVE bucket audited **by content**.
**TERMINAL = the r4 union sweep, as verified by PE4/PE5/PE6.** `CHAIN HOME: s1of3.43` (the `(IN-3)` declaration).

**★ THE METHODOLOGICAL LESSON, stated by the note:** a name-pattern sweep can reach fixed point under its own pattern and still miss the input under an alias. **The cure is a union pattern over every name the input ever carried, PLUS a content audit of the live bucket.** **And even that has a disclosed resolution limit** (`.20`).

**CONDITIONALITY:** The struck clause was “live … un-superseded since r0” — it survived four rounds.

**DERIVATION:** A union grep + a content audit.

**RESOLUTION TRACE:** statement lines 271–282; the §0 display 573–602 (`.46`); the census 2452–2597 (shard 3); the earlier chain members 316–319 (r3/G-1, `.22`), 464–469 (r2/G-4, `.38`), 359–377 (r1/F1, `.31`).

**TEETH:** **AUDIT — arithmetic recount**, reproduced independently by PE5 (144 = 42/28/74 bucket for bucket) and PE6 (18/18 numbers). Disposition: **accepted-with-decorrelation-supplied**.

---

### EFF.GRTJC.s1of3.18  [changes-record]  r4/G-2 — the arc record brought forward

**CANONICAL STATEMENT:** verbatim, lines 283–288.
**FORM:** bold-headed bullet.

> “* **G-2** — §10.1's grade box still ended its arc "→ JC-PE3 next" at HEAD
>   (r3 broke the note's own convention of extending that arc, leaving two
>   contradictory arc displays). The arc is brought forward through
>   JC-PE3 → r3 → JC-PE4 (0 CRITICAL + 4 gaps) → r4 → "JC-PE5 next", and the
>   missing convention lines "[r3] Grade deltas: NONE" and "[r4] Grade deltas:
>   NONE" are added.”

**SUPERSESSION KIND:** `inventory completion` — a convention line the previous round omitted.

**CONDITIONALITY:** **“leaving two contradictory arc displays” at HEAD** — the header's current one and §10.1's stale one. **This is the same defect class as GRTJB's status asymmetry**, caught and fixed here rather than left open.

**DERIVATION:** Record.

**RESOLUTION TRACE:** statement lines 283–288; §10.1's arc 2605–2649 (shard 3); the convention lines 2650–2662 (shard 3).

**TEETH:** NONE (record). Disposition: **AUDIT — in-house hostile pass**.

---

### EFF.GRTJC.s1of3.19  [supplier-finding]  r4/G-3 — JC-LOAD's constant re-tiered

**CANONICAL STATEMENT:** verbatim, lines 289–296.
**FORM:** bold-headed bullet.

> “* **G-3** — JC-LOAD's re-routed proof body retained two EXACT-TIER constant
>   displays ("the constant 𝑅(X_N)") under its newly declared citable-tier
>   fence. Re-worded to the (DMULT-w)-tier truth PE4 §A1 verified: the
>   multiplier is the anchor coboundary a_{λ+N}/(a_λa_N), λ := γ+γ′ (the
>   in-note κ = 1 pinning; = 𝑅(X_N) = 1 exactly when ω(λ,N) ≡ 1, i.e. on
>   (DMULT-s), the MEASURED tier), and the iff conclusion is unaffected — the
>   same constant appears on both sides (both are the line pair (γ+γ′, N), and
>   ω(λ,μ) = c_{λ+μ}/(c_λc_μ) is symmetric), so it cancels exactly.”

**SUPERSESSION KIND:** `scope-pin` — an exact-tier value inside a proof whose declared footprint is the weak tier, re-worded to the weak tier.

**CONDITIONALITY:** **A genuine tier-hygiene repair: the proof body was using a `(DMULT-s)`-tier value under a `(DMULT-w)`-tier fence.** **The iff conclusion is unaffected**, and the reason is displayed: the same constant appears on both sides (both at the line pair `(γ+γ′, N)`) and `ω(λ,μ) = c_{λ+μ}/(c_λc_μ)` is symmetric, so it cancels exactly. **PE4 §A1 verified it.**

**DERIVATION:** Displayed: `b_× := a_{λ+N}/(a_λ a_N)` with `λ := γ+γ′`; equality with `𝑅(X_N) = 1` holds exactly when `ω(λ,N) ≡ 1`, i.e. on `(DMULT-s)`.

**RESOLUTION TRACE:** statement lines 289–296; the target site 885–912 (§2.8's proof, shard 2); the tier split 1188–1267 (§2.10, shard 2); the m-1 follow-up 256–259 (`.15`).

**TEETH:** PE4 §A1's verification (**AUDIT — in-house hostile pass**); the tier's own machine legs R1-DMULT / R2-BIL (shard 3).

---

### EFF.GRTJC.s1of3.20  [changes-record]  ★ r4/G-4 — the CONTENT line invisible to every name census

**CANONICAL STATEMENT:** verbatim, lines 297–302.
**FORM:** bold-headed bullet.

> “* **G-4** — §0's (c) CONTENT line (the display PE1's CRITICAL 1 quoted;
>   invisible to every name-pattern census because its `[Thm 4.2]` tag sits on
>   the adjacent line) is annotated in place with the re-route pointer every
>   other formerly-misaimed display already carries, and §9.5's protocol now
>   DISCLOSES that the census is NAME-pattern-based (content lines without
>   name tags are outside its resolution).”

**SUPERSESSION KIND:** `inventory completion` (an annotation added) + a **DISCLOSED PROTOCOL LIMIT**.

**★ THE DISCLOSED RESOLUTION LIMIT, quoted from §9.5 (shard 3, L2591–2597):**

> “**DISCLOSED PROTOCOL LIMIT [r4, G-4]: this census counts hit-LINES by NAME.**
> A content line whose name-tag sits on an adjacent line is outside its
> resolution — §0's clause-(c) display was exactly such a line, and is now
> annotated in place [r4, G-4]. The limit was discharged this round by a
> read-through of §0's input block, the only place the package's clauses are
> DISPLAYED as propositions rather than consumed by name; the census cannot
> certify the absence of further such lines by grep, and says so.”

**CONDITIONALITY:** **The census's own resolution limit is disclosed and is not closed by grep — it was discharged by a targeted read-through of §0, “the only place the package's clauses are DISPLAYED as propositions rather than consumed by name”.** **So the completeness of the alias sweep rests, at the last step, on a human/model read of one section, not on a mechanical fixed point.** The note says exactly this.

**DERIVATION:** A read-through, with the residual limit stated.

**RESOLUTION TRACE:** statement lines 297–302; the annotated line 536–546 (`.43`); the disclosed limit 2591–2597 (shard 3).

**TEETH:** **AUDIT — in-house hostile pass with a signed resolution limit.** Disposition: **disclosed non-repair** on the general question (“the census cannot certify the absence of further such lines by grep, and says so”).

---

### EFF.GRTJC.s1of3.21  [run-record]  REPAIR ROUND r3 — header

**CANONICAL STATEMENT:** verbatim, lines 304–312.
**FORM:** bold-headed bracketed block opener.

> “**[REPAIR ROUND r3 — 2026-08-08 campaign (wallclock 2026-08-06). NOTE-ONLY.**
> Applied against JC-PE3 (0 CRITICAL + 8 gaps, all labelling/disclosure/record:
> PE3 re-derived the r2 tier split, the κ = 1 pinning, the full consumer split
> (no hidden (DMULT-s) consumption), the G6 derivation and the residual = W-1 tie
> and found them SOUND; all three batteries reproduced byte-identically, exit 0,
> all seals verified). No measured quantity moves at r3; nothing in
> `verification/` is touched (the diversity fix is DISCLOSURE, not a new
> battery, per the effort directive). Dispositions, each edit carrying an
> `[r3, G-#]` bracket keyed to PE3's gap numbers:”

**CONDITIONALITY:** **“the diversity fix is DISCLOSURE, not a new battery, per the effort directive”** — an explicit statement that a known evidence gap was disclosed rather than closed, and why. **PE3 verified the r2 tier split SOUND, including “the full consumer split (no hidden (DMULT-s) consumption)”** — which is the check that makes the two-tier honesty load-bearing rather than decorative.

**DERIVATION:** Round record.

**RESOLUTION TRACE:** statement lines 304–312; the dispositions 314–342 (`.22`–`.29`); the tier split 1188–1267 (shard 2).

**PIN VERIFICATION:** `e4b6fbf` (PE3, from the ARC display) → **commit**; `126c33f` (r3) → **commit**; `GRTJC_passPE3_report.md` **EXISTS**.

**TEETH:** three batteries reproduced byte-identically, all seals verified.

---

### EFF.GRTJC.s1of3.22  [supplier-finding]  ★ r3/G-1 — the alias-blind sweep, and the live re-route

**CANONICAL STATEMENT:** verbatim, lines 314–319.
**FORM:** bold-headed bullet.

> “* **G-1 (the live one)** — JC-LOAD's proof body and honest fence (§2.8) still
>   consumed the PE1-refuted `(IN-3)(c)`-on-gr BY NAME: the r2 sweep's grep was
>   ALIAS-BLIND (`(COORD)`/`(MULT)` only). Both sites re-routed through
>   §4.2 = (MULT-B)|gr (riding (DMULT-w)) — the step actually used, at δ = 0 —
>   and the ALIAS-COMPLETE re-sweep ((IN-3) + Thm 4.2 + (COORD)/(MULT)) is now
>   §9.5's protocol, census recorded there.”

**CHAIN:** member 3 of the `(IN-3)(c)` alias chain (`.17`). `CHAIN-MEMBER: s1of3.43 position 3.`

**SUPERSESSION KIND:** `scope-pin` — a refuted input's consumption re-routed to the step actually used.

**CONDITIONALITY:** **“the live one”** — the note's own label distinguishing this from the round's seven record/labelling gaps. **The re-route is mathematically substantive**: the step actually used is §4.2's offset-transport lemma `= (MULT-B)|gr` at `δ = 0`, riding `(DMULT-w)`, not `(IN-3)(c)`-on-`gr`. **The refuted input survived TWO rounds after its refutation because the sweep pattern did not include its own name.**

**DERIVATION:** Identification of the step actually used, plus a widened sweep.

**RESOLUTION TRACE:** statement lines 314–319; the two re-routed sites 885–889 and 918–921 (§2.8, shard 2); §4.2 1747–1756 (shard 2); the census 2421–2450 (shard 3).

**TEETH:** **AUDIT — in-house hostile pass** (PE3 found it; no battery keys a citation name).

---

### EFF.GRTJC.s1of3.23  [supplier-finding]  ★ r3/G-2 — a sweep record wrong at its own commit

**CANONICAL STATEMENT:** verbatim, lines 320–324.
**FORM:** bold-headed bullet.

> “* **G-2** — §9.5's sweep record misreported its own machine-verifiable count
>   AT ITS OWN COMMIT (22 claimed; the grep returns 37 at `5742e25` and at the
>   pre-r3 HEAD). Corrected from greps executed at the committing states; the
>   load-bearing half ("0 live consuming sites" for the old pattern) was
>   independently re-verified by PE3 and stands.”

**SUPERSESSION KIND:** `counter re-reading` — a count refuted by re-running its own grep at its own commit.

**★ THE FIRST MEMBER OF THE CENSUS SPECIES**, and the origin of FREEZE PREDICATE 3's rule: **“a fixed-point claim must be grepped AT the committing state”** (shard 3, L2410–2411). **The species then recurred twice more** (r4/G-1 at `.17`, r5/G-1 at `.13`), each time inside the block written to end it.

**ARITHMETIC AUDIT (rule 22):** claimed **22**, actual **37** at `5742e25` and at pre-r3 HEAD; the corrected classification (shard 3, L2412–2416): 17 strikes + 4 r1-header + 1 r2-header + 2 R1-BND + 11 §9.5-self + 2 quotation = **37** ✔. **The 15-line gap is explained: the count was taken before §9.5's own record and some `[r2]` brackets were written, then committed unrefreshed** — a self-reference effect the note names.

**CONDITIONALITY:** **The load-bearing half survived: “0 live consuming sites” for the old pattern, independently re-verified by PE3.** Only the total was wrong.

**PIN VERIFICATION:** `5742e25` → **commit**.

**DERIVATION:** Greps executed at the committing states.

**RESOLUTION TRACE:** statement lines 320–324; the corrected count 2400–2419 (shard 3); the species' later members 271–282 (`.17`), 235–246 (`.13`).

**TEETH:** **AUDIT — arithmetic recount**, re-verified by PE3 line by line (37 hits classified independently).

---

### EFF.GRTJC.s1of3.24  [instrument-record]  ★ r3/G-3 — the sampling-diversity overstatement (species, 3rd recurrence)

**CANONICAL STATEMENT:** verbatim, lines 325–328.
**FORM:** bold-headed bullet.

> “* **G-3** — R2-BIL's "THREE elements on all 29 rows" overstated the sample
>   diversity: mix2 == ones2 BYTE-IDENTICAL on 13/29 rows, including BOTH
>   g_m = 2 rows. Honest census now in §9.4 [r3, G-3], with the species history
>   (THIRD recurrence) and the candidate leg NAMED, NOT built.”

**SUPERSESSION KIND:** `counter re-reading` — a diversity claim refuted by inspecting the frozen builder's own code.

**★ THE WORST PLACEMENT OF THE THREE:** the collapse hits **BOTH `g_m = 2` rows (C2I, C4I)** — “exactly the rows where ψ_m has interior content”, i.e. **precisely the rows where bilinear resolution mattered most** (shard 3, L2344–2346). **And the leg that would fix it is NAMED, NOT BUILT** — an explicit, disclosed evidence gap.

**ARITHMETIC AUDIT (rule 22), from §9.4's disclosure (shard 3, L2336–2343):** on **13 of 29** rows `alt = 1` — **ten** rows where the enumeration's second nonzero element is 1 (C2A, C2B, C2E, C3A, C3D, C3E, C3I, C4B, C4G, I4A) plus **three** rows where `K_m^* = {1}` (C2I, C4A, C4I) → **10 + 3 = 13** ✔. On those rows `D = {f, f, f′}`, so the 9 ordered pairs contain only **4 distinct** pairs ✔ (from 2 distinct elements: 2² = 4). **What stands undiminished, and the note says so:** ones2 × ones2, ones2 × ones3, ones3 × ones3 are genuinely dense × dense with live cross-term convolutions; **U2 fired 261/261**.

**CONDITIONALITY:** **“the defect is RESOLUTION overstatement, not a wrong verdict, and no measured quantity moves.”** The standing rule this produced: “any sampling-diversity claim in this note must be a SCORED or CENSUSED fact, never prose” (FREEZE PREDICATE 3).

**DERIVATION:** Composition re-verified against the frozen code; byte-identity of the builds verified by PE3 on C2I/C4I/C2A.

**RESOLUTION TRACE:** statement lines 325–328; the census 2333–2362 (§9.4 [r3, G-3], shard 3); the species history — PE2/G-2 → r2's fix → PE3/GAP 3.

**TEETH:** **signed vacuity disclosure** (the “mixed variant” adds zero resolution on 13/29 rows, including both `g_m = 2` rows) + **disclosed non-repair** (the candidate leg named, not built).

---

### EFF.GRTJC.s1of3.25  [supplier-finding]  r3/G-4 — a false divisibility attached to a true measured fact

**CANONICAL STATEMENT:** verbatim, lines 329–331.
**FORM:** bold-headed bullet.

> “* **G-4** — §9.4's R2-PHI cell justified a true measured fact by a false
>   divisibility ("E | wΦ_NR", false on 25/29 rows): replaced by e_m | wΦ_NR
>   (true 29/29, re-verified this round).”

**SUPERSESSION KIND:** `replacement` — a false justification replaced by the true one; the measured fact is unchanged.

**★ THE CLEANEST INSTANCE IN THE CORPUS OF “right conclusion, wrong reason”.** The measured fact (`δ = 0` on every row) is true; the reason given (`E | wΦ_NR`) is **false on 25 of 29 rows**; the true reason is `e_m | wΦ_NR` (since `wΦ_NR = e_m·g_m·γ_{m+1}`), **true 29/29**.

**ARITHMETIC AUDIT (rule 22):** false on **25** of 29 ⇒ `E | wΦ_NR` holds on **4** rows (named in shard 3, L2329: C2D, C2I, C2J, I4A) ✔; the counterexample given there (C2A has `E = 4`, `wΦ_NR = 10`) checks: `4 ∤ 10` ✔ while `e_m | 10` holds since `wΦ_NR = e_m g_m γ_{m+1}` ✔.

**CONDITIONALITY:** The correction is to the JUSTIFICATION only; the R2-PHI verdict (0 violations on 29/29) stands.

**DERIVATION:** `wΦ_NR = e_m·g_m·γ_{m+1}` gives `e_m | wΦ_NR` unconditionally, hence `s_NR(wΦ_NR) = 0`, hence `δ = 0`.

**RESOLUTION TRACE:** statement lines 329–331; the corrected cell 2329 (§9.4, shard 3); the same `δ = 0` fact used at §2.10's ideal display 1365–1373 (shard 2).

**TEETH:** R2-PHI (29/29, 0 violations) — the fact is measured; **the reason was AUDIT-caught** (in-house hostile pass).

---

### EFF.GRTJC.s1of3.26  [changes-record]  r3/G-5 — the TC-3 display's load-bearing one-liner

**CANONICAL STATEMENT:** verbatim, lines 332–333.
**FORM:** bold-headed bullet.

> “* **G-5** — the TC-3 display's load-bearing one-liner δ(wΦ_NR, n−wΦ_NR) = 0
>   (what makes "corresponds to ψ_m(y)·Δ" an EQUALITY) written into §2.10.”

**SUPERSESSION KIND:** `inventory completion` — an unwritten step supplied.

**CONDITIONALITY:** **The step is what turns an inclusion into an equality of ideal pieces**, and the note spells out the consequence at the site (shard 2, L1370–1373): “were δ = 1 the quotient `B_n/(𝔦^B ∩ B_n)` would strictly contain a K-line and §3.1's ‘each 𝒜_ν is a 1-dimensional K-space’ would fail”. **So an unwritten one-liner was load-bearing for W-7's whole dimension count.**

**DERIVATION:** `e_m | wΦ_NR` (= `e_m g_m γ_{m+1}`) gives `s_NR(wΦ_NR) = 0`; and `s_NR(n − wΦ_NR) = s_NR(n)`; so `δ = (0 + s_NR(n) − s_NR(n))/e_m = 0`. **Note this is the same divisibility r3/G-4 corrected** (`.25`) — one round supplied the step and fixed its stated reason at the same time.

**RESOLUTION TRACE:** statement lines 332–333; the target display 1354–1381 (§2.10, shard 2); the consumer 1460–1475 (§3.1, shard 2).

**TEETH:** JC7's cocycle families indirectly; the step itself is arithmetic.

---

### EFF.GRTJC.s1of3.27  [supplier-finding]  ★ r3/G-6 — the TR-3′-GEN gloss misquoted its own record twice

**CANONICAL STATEMENT:** verbatim, lines 334–336.
**FORM:** bold-headed bullet.

> “* **G-6** — the TR-3′-GEN closed-scope gloss corrected to the record's truth
>   (ONE order-3 stratum; exactness where closed on stratum (i); units-only
>   phrasing PERMANENTLY REFUTED on (ii) — the record quoted).”

**SUPERSESSION KIND:** `counter re-reading` — a gloss on a supplier's open lemma corrected against that supplier's own record.

**★ THE CORRECTION IN FULL (shard 2, L1232–1243), because it is load-bearing for the `(DMULT-s)` tier's honesty:**

> “that gloss misquoted the record twice. The
> closed scope of record is {all order-2} ∪ {order-3 all-e_j = 1}: **ONE** order-3
> stratum … And where closed the record is NOT a per-argument-units statement: on
> stratum (i) the accepted closures deliver **EXACTNESS** — TR3-S1
> “σ₁(R^F₂(f)) = R_λ(f) EXACTLY”, TR3-S3 “σ₂(R^F₃(f)) = R_λ₃(f) EXACTLY —
> discrepancy ≡ 1, per-argument units ≡ 1” — while on stratum (ii) the
> record's own bracket rules the units phrasing OUT: “the units-only phrasing
> of the record statement below is PERMANENTLY REFUTED on (ii)” … What
> this passage needs is unchanged and true: **TR-3′-GEN is OPEN beyond
> that closed scope**.”

**CONDITIONALITY:** **The correction cuts BOTH ways and the note takes both.** It weakens the note's characterisation (one order-3 stratum, not two) AND strengthens it (where closed, the record delivers EXACTNESS, not units-up-to). **What the passage NEEDS is unchanged: TR-3′-GEN is OPEN beyond its closed scope, so no corpus-pinned statement delivers `ω ≡ 1`.** **That is the load-bearing claim for the `(DMULT-w)`/`(DMULT-s)` split.**

**DERIVATION:** Quotation of the supplier's own record.

**RESOLUTION TRACE:** statement lines 334–336; the corrected gloss 1226–1247 (§2.10, shard 2); the tier split 1188–1267 (shard 2).

XREF: `lean/notes/openmath/GRB_ORDER2_2026-08-05.md:TR-3′-GEN` — grep-verified count **57** · `S3.4` — count **25**.

**TEETH:** **AUDIT — transfer audit** (a supplier's record read against the consumer's gloss).

---

### EFF.GRTJC.s1of3.28  [changes-record]  r3/G-7 — a byte-frozen prereg row annotated with its blast radius

**CANONICAL STATEMENT:** verbatim, lines 337–338.
**FORM:** bold-headed bullet.

> “* **G-7** — §9.3's byte-frozen R1-COB prereg row annotated with the
>   post-tier-split blast radius (quote untouched, annotation only).”

**SUPERSESSION KIND:** `as-of scoping` — a frozen preregistration quote left byte-untouched and annotated with what its failure would now mean.

**★ WHY THIS IS THE RIGHT MOVE, and worth a chapter cut's attention.** A preregistration's value is that it is frozen; but the tier split (r2/G-1) changed what a failure would REFUTE. **The note keeps the quote byte-exact and adds the two-mode blast radius as an annotation** (shard 3, L2181): “a failure with the slot set still {δ} would refute only the exact tier (DMULT-s) and with it JC-COB's sharp value (ω ≢ 1), **NOT** (COORD-B)(2); only a failure of the SLOT-SET half would refute (DMULT-w) and (COORD-B)(2)”. **A two-mode falsifier, declared after the fact but without editing the prediction.**

**DERIVATION:** The tier split applied to the prereg's own predicate.

**RESOLUTION TRACE:** statement lines 337–338; the annotated row 2181 (§9.3, shard 3); the tier split 1188–1267 (shard 2).

**TEETH:** R1-COB (2,607 samples, 0 violations, 869/869 anchor pairs — shard 3). Disposition: **preregistration with a post-hoc-annotated, two-mode falsifier**.

---

### EFF.GRTJC.s1of3.29  [supplier-finding]  r3/G-8 — JC-CYC(b)'s false trigger

**CANONICAL STATEMENT:** verbatim, lines 339–342.
**FORM:** bold-headed bullet.

> “* **G-8** — JC-CYC(b)'s false trigger ("two multiplicatively distinct
>   (δ, D)-words") replaced by the true one (two distinct non-1 VALUES of the
>   word), with the note's own C2C/C3I mechanism-2 rows displayed as the
>   counterexample.”

**SUPERSESSION KIND:** `replacement` — a false sufficient condition replaced by the true one.

**★ A GENUINE MATHEMATICAL CORRECTION, refuted by the note's own roster.** The full text (shard 2, L1876–1882): “**FALSE as stated: two multiplicatively distinct words can evaluate to {1, v}, a SINGLE non-1 value, where (α) holds with ζ′ = v and (CYC) can only fail through (β); clause (d) below exhibits exactly that genre on the note's own roster (C2C, C3I — ‘a single value whose carry pattern no integer relabeling realizes’, NOT-CYCLIC by (β), not (α)). The true trigger: … two distinct non-1 VALUES of the (δ, D)-word**”.

**CONDITIONALITY:** **The obstruction direction of JC-CYC is what does the work in the fence**, so getting its trigger right is load-bearing. **And the counterexample is internal — C2C and C3I are rows of the note's own roster.**

**DERIVATION:** A counterexample class from the note's own measured table: rows NOT-CYCLIC by clause (β) (the carry-pattern condition) rather than by clause (α) (the single-value condition).

**RESOLUTION TRACE:** statement lines 339–342; the corrected law 1865–1886 (§6, shard 2); the roster rows 2146–2153 (§9.2's finding 1, shard 3).

**TEETH:** the note's own battery — **finding 1 of §9.2**: “13 rows sit in the collapse geography and still come back NOT-CYCLIC”, with two mechanisms visible, C2C and C3I being the single-value ones. Disposition: **measurement, refuting**.

---

### EFF.GRTJC.s1of3.30  [run-record]  REPAIR ROUND r1 — header (the STRUCTURAL round)

**CANONICAL STATEMENT:** verbatim, lines 344–358.
**FORM:** bold-headed bracketed block opener.

> “**[REPAIR ROUND r1 — 2026-08-08 campaign (wallclock 2026-08-05).** Applied
> against JC-PE1. PE1's machine leg reproduced this note's battery **bit-for-bit**
> (8,566 scored samples, 0 violations, exit 0, every §9.2 cell identical, runner
> md5 identical at both seal commits and at HEAD, instrument re-run clean), so
> **no measured quantity moves at r1** and the sealed runner + artifacts are
> BYTE-FROZEN … PE1 also re-derived, hostilely and independently, JC-DOM,
> JC-GAUGE (unit hypothesis satisfied, TC-1 strictly before TC-2), JC-PER,
> JC-FIB, JC-ANCHMON, JC-SCAL, JC-SPAN, JC-LOAD's iff in both directions,
> JC-PSIKER's witness computation, W-8's cancellation and JC-F1's algebra —
> **all CLEARED**. What failed was one object identification and one quantifier.
> Dispositions, each edit carrying a dated `[r1, F#]` (critical) or `[r1, G#]`
> (gap) bracket, strike-and-replace (the refuted r0 wording is quoted inside the
> bracket that supersedes it, never silently deleted):”

**★ THE ROUND'S DIAGNOSIS IN ONE SENTENCE, and it is unusually precise:** **“What failed was one object identification and one quantifier.”** Eleven named lemmas were re-derived hostilely and CLEARED; the two failures were **F1** (the coordinate calculus stated on the wrong object) and **F2** (an over-quantified corollary).

**CONDITIONALITY:** **“no measured quantity moves at r1”** despite two CRITICALs — because both defects were about WHERE the statements lived, not about what the machine measured.

**ARITHMETIC AUDIT (rule 22):** “8,566 scored samples” reproduced bit-for-bit ✔ matches `.04`'s headline and §9.2's family sum.

**PIN VERIFICATION:** `1a27be3` (PE1) → **commit**; `6ed4680` (ledger) → **commit**; `85d5811`, `54904cc` (r1) → **commit**; `GRTJC_passPE1_report.md` **EXISTS**.

**DERIVATION:** Round record.

**RESOLUTION TRACE:** statement lines 344–358; the dispositions 359–405 (`.31`–`.33`); the new leg 407–419 (`.34`).

**TEETH:** bit-for-bit reproduction + eleven independent hostile re-derivations. Disposition: **accepted-with-decorrelation-supplied**.

---

### EFF.GRTJC.s1of3.31  [supplier-finding]  ★★ r1/F1 (CRITICAL 1) — the coordinate calculus was stated on the WRONG OBJECT

**CANONICAL STATEMENT:** verbatim, lines 359–377.
**FORM:** bold-headed bullet.

> “* **F1 (CRITICAL 1) — the coordinate calculus was stated on the WRONG OBJECT.**
>   §2.10's `(COORD)` ("𝑅_λ : gr_λ(w) → Δ = K_m[y] is a K_m-linear isomorphism")
>   and its display ("gr_λ/(𝔦 ∩ gr_λ) ≅ K, a ONE-dimensional K-space") are **FALSE
>   on this note's own gr(w)**: the ambient ring is O[x] and w ≥ 0 there, so every
>   gr_λ is a FINITE-dimensional K_m-space (explicit slot bound below), and PE1's
>   machine counter-instance sits on the battery's own row C2I at the battery's
>   own window base. **REPAIRED, inside the note's own machinery**: (COORD),
>   (MULT) and TC-3's display are restated on the **post-TC-1 pieces**
>   `B_n = ∪_k in(π)^{-k}gr_{n+kE}` (JC-DOM's object), with four new lemmas —
>   **JC-LOC** (B ≅ gr_{K[x]}(w): B *is* the object FGMN's theorems speak about),
>   **JC-PIINV** (the digit polynomial is π-equivariant, so the colimit coordinate
>   is well defined, and ρ is exactly invariant), **JC-BSURJ** (the colimit
>   coordinate is ONTO Δ — PROVED from REALIZE-(m), not cited), and the reduction
>   of the Δ-module half to a single cited input **(DMULT)** (composite-stage
>   residual multiplicativity). **All five PE1-listed consumers RE-DERIVED and
>   THROUGH** (§3.1, JC-IND/OB-4, W-7's bijectivity, JC-F1's dimension count,
>   (MULT)) — none downgraded; W-7 is in fact STRENGTHENED (𝒜(T) is the whole
>   transported ring). New corollary **JC-COB** (u = a_γ·a_{γ′}: the inner factor
>   is the anchor-constant coboundary) with its own scored machine family.”

**TYPE JUSTIFICATION (rule 13):** `supplier-finding` — a defect report about a cited theorem transported to the wrong ambient object, discharged by re-basing the calculus rather than by weakening the theorem.

**SUPERSESSION KIND:** `replacement` — the coordinate calculus is restated on a different object.

**★ THE CENTRAL REPAIR OF THE WHOLE NOTE, and the shape a chapter cut must carry:**
- **What was false:** `(COORD)` and its 1-dimensionality display, **on `gr_{O[x]}(w)`**. The reason is displayed at §2.10 (shard 2): the ambient ring is `O[x]`, so `w ≥ 0` and every `gr_λ` is a FINITE-dimensional `K_m`-space with an explicit slot bound; `𝑅_λ` is NOT onto `K_m[y]`.
- **Why the literature is NOT at fault:** FGMN's `Δ ≅ K_m[y]` is about `K[x]` with `π` INVERTED — “and that object is exactly what JC-DOM builds one page earlier”.
- **The repair, inside the note's own machinery:** four new lemmas (**JC-LOC**, **JC-PIINV**, **JC-BSURJ**, plus the reduction to **(DMULT)**), with the calculus restated on `B_n`.
- **The literature footprint SHRINKS, not grows:** JC-BSURJ PROVES the surjectivity half that r0 had cited, so “the only cited input left in the coordinate calculus is the multiplicativity (DMULT)”.
- **All five consumers re-derived THROUGH; one STRENGTHENED** (`𝒜(T)` is the whole transported ring — spanning promoted from definition to theorem).

**CONDITIONALITY:** **`(DMULT)` was later SPLIT into two tiers by r2/G-1** (`.36`) and, post-acceptance, **Annex #6 withdraws the claim that `(DMULT-w)` is itself a quoted FGMN identity and DERIVES it instead** from the PDF-verified rank-one theorem via **LEMMA JC-RANKMULT**. **So the “single cited input” of r1 became, at the end, a DERIVED consequence of a different cited input.** `CHAIN HOME: s1of3.43`, member 1.

**PIN VERIFICATION:** PE1's counter-instance is on “the battery's own row C2I at the battery's own window base”; the corresponding scored fact is R1-BND (`maxslot(G0) == 0` on 29/29, shard 3). **Both re-verifiable from the committed artifacts; not re-run here.**

**DERIVATION:** The slot bound (shard 2, L1007–1022) plus JC-DOM/JC-LOC.

**RESOLUTION TRACE:** statement lines 359–377; the repair 992–1414 (§2.10, shard 2); the five consumers' verdict table 1402–1408 (shard 2); the later tier split 1188–1267 (shard 2); **Annex #6's re-derivation 2917–3000 (shard 3)**.

XREF: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md:REALIZE` — count **17** · `S4.1` — count **35**.

**TEETH:** **PE1's machine counter-instance** (row C2I, 3,072 integral `f` with `w(f) = 4`, slot set `{0}` throughout, `𝔦 ∩ gr_4 = 0`, so `gr_4 ≅ K_m` while `[K:K_m] = g_m = 2`), reproduced as the scored family **R1-BND** (0 violations on 29/29) with tooth **T1** (the refuted universal claim, must fire — 29/29 firings). **A refutation converted into a permanent scored regression.** Disposition: **planted mutant from a refuted claim; fired**.

---

### EFF.GRTJC.s1of3.32  [supplier-finding]  ★ r1/F2 (CRITICAL 2) — an over-quantified corollary

**CANONICAL STATEMENT:** verbatim, lines 378–384.
**FORM:** bold-headed bullet.

> “* **F2 (CRITICAL 2) — JC-PSIKER's closing sentence was over-quantified.** "TC-3
>   has a nonzero kernel on every graded piece" is FALSE for λ < wΦ_NR (all 29
>   rows at their own base). The **witness computation is CORRECT** and W-6(v)'s
>   fenced wording is CORRECT; only the universal generalization went wrong.
>   RE-QUANTIFIED to the exact range (§2.9(ii)(iii)): ZERO for every λ < wΦ_NR,
>   NONZERO for every λ ∈ wΦ_NR + W, and — the form §2.10 actually consumes —
>   nonzero on **every** graded piece of the POST-TC-1 object B.”

**SUPERSESSION KIND:** `counter re-reading` — a universal generalization refuted and replaced by an exact range.

**★ THE PRECISION OF THE DIAGNOSIS IS THE POINT:** the witness computation is CORRECT; W-6(v)'s fenced wording is CORRECT; **only the universal generalization went wrong** — and the form the downstream proof actually consumes (on `B`, not on `gr`) is TRUE. **So the CRITICAL cost the note nothing downstream**, and the note verifies that: “Nothing downstream used the refuted universal form on gr: §2.10 [r1, F1] now states and consumes (iii)” (shard 2, L963–964).

**CONDITIONALITY:** The corrected statement is three-clause: (i) the witness at `λ = wΦ_NR` (unchanged, PROVED); (ii) the exact range on `gr` (ZERO below `wΦ_NR`, NONZERO on `wΦ_NR + W`); (iii) **nonzero on EVERY graded piece of `B`** — the form §2.10 consumes, true because `in(π)` is a unit in `B` so no piece of `B` is zero.

**DERIVATION:** `𝔦 := in(Φ_{m+1})·gr(w)` is homogeneous with a single generator of degree `wΦ_NR`, so `𝔦 ∩ gr_λ = in(Φ_{m+1})·gr_{λ−wΦ_NR}`, and weights are `≥ 0` on `O[x]` — hence the kernel is ZERO whenever `λ < wΦ_NR`.

**RESOLUTION TRACE:** statement lines 378–384; the corrected corollary 926–990 (§2.9, shard 2); the consumed form 1354–1396 (§2.10, shard 2).

**TEETH:** **R1-PSIK-LO** (197 window lines below `wΦ_NR`, no class certified dead — with the certifier's disclosed one-sidedness) and **R1-PSIK-HI** (197 residue classes with a certified nonzero witness), plus tooth **T1** (the refuted universal claim, 29/29 firings). Disposition: **executable regression in both directions + a planted mutant from the refuted claim**.

---

### EFF.GRTJC.s1of3.33  [changes-record]  r1 — the eight gap dispositions, assembled

**CANONICAL STATEMENT:** [ASSEMBLED — the r1 bullets G1–G8, lines 385–405, quoted verbatim in source order.]

**MERGE CRITERION (stated):** these eight are interface, definition, labelling, census and hygiene corrections, each fully resolved inside its own bullet, none carrying a supersession history of its own, and none cited by designation from another unit. **The two CRITICALs (F1, F2) are separate units** (`.31`, `.32`) because each moves an object or a quantifier.

`[TABLE — compiler ledger]` r1's eight gaps.

| bullet | lines | what it corrects | the corrected content |
|---|---|---|---|
| **G1** | 385–386 | W-6(ii)'s interface | `A_ν ≅ B_n` (JC-GAUGE(iii)'s actual conclusion), **not** “the `gr_n(w)`-piece”; **`B_n ⊋ gr_n` in general** |
| **G2** | 387–390 | `𝒜(T)`'s definition | the “degree-0 component” reading **CORRECTED** (it contradicted the note's own degree-separation proof) and flagged as **FINDING JC-F2**, an inherited blueprint/design-note/brief display defect, **REVIEW-OWED** |
| **G3** | 391–394 | an evidence label | §9.2's JC8 cell RE-LABELLED honestly — **the sealed battery filters zeros before the predicate exists**, so it does NOT evidence “every structure constant is a unit”; the falsifiable version + a skipped-pair census live in the NEW r1 script (family R1-UNIT + tooth T4) |
| **G4** | 395–396 | a roster label | §7 case 1's `g_m` labels corrected against the runner (**C2I/C4I are the two `g_m = 2` rows**; C2B/C3I are `g_m = 1`), with the “27 `g_m = 1` stages” recount |
| **G5** | 397–398 | a scope | §2.8(c)'s “THEOREM” aligned with JC-LOAD's own `e_m ≥ 2` fence (**theorem on the 28 rows with `e_m ≥ 2`; MEASURED on the one top-flat row C4H**) |
| **G6** | 399–401 | a dropped disclosure | §3.4's SPAN-M census restored to the instrument's own disclosure (“**606 skipped for non-integrality**”), and “no case is owed” re-justified in the repaired frame |
| **G7** | 402–403 | two unproved identifications | §4.1 remark (a)'s two identifications **STRUCK**, replaced by what is provable (the definitional same-line cancellation + JC-COB) |
| **G8** | 404–405 | fence hygiene | the battery's own calls to `T.constants` (δ) and `T.read` are **DISCLOSED**, with the non-circularity argument spelled out |

**★ THREE OF THE EIGHT ARE EVIDENCE DOWNGRADES, and they deserve a chapter cut's attention:**
- **G3** — a GREEN family that evidenced nothing: “the sealed battery filters zeros before the predicate exists, so … the violation branch is unreachable and the skipped pairs were never censused”. **The same disease as GRTJB's SAME-computation class**, found here in a different form (a filter upstream of a predicate).
- **G6** — **606 of 934** SPAN-M perturbations skipped for non-integrality; after the r1 repair those are exactly the elements that live in `B` but not in `gr(w)`, i.e. **in the newly covered part of the statement, with no machine leg**. Boxed as JC-BOX-8(i).
- **G8** — the note's own battery DOES call `T.constants` and `T.read` (the instrument does not), and r0 disclosed only half of it. **The non-circularity argument is spelled out rather than assumed.**

**CONDITIONALITY:** **G2's FINDING JC-F2 is REVIEW-OWED at three external sources** (the design note, the blueprint, the brief) and is not repaired there by this note. **G5's split (theorem on 28 rows, measured on C4H) is later CONDITIONALLY CLOSED on `(DMULT-w)`** (r1's JC-BOX-4 addition, noted at r2/G-7).

**DERIVATION:** Per item, inside the bullet.

**RESOLUTION TRACE:** statement lines 385–405; the targets 664–699 (W-6's box, shard 2), 644–654 (§1's `𝒜(T)`, `.55`), 2127 (§9.2's JC8 cell, shard 3), 1924 (§7 case 1, shard 2), 877–883 (§2.8(c), shard 2), 1580 (§3.4's SPAN-M row, shard 2), 1712–1732 (§4.1 remark (a), shard 2), 1635–1652 (§3.5's fence hygiene, shard 2).

**TEETH:** G3 → **R1-UNIT** (869 unit / 0 zero / 0 undefined / 0 out-of-window) **+ tooth T4** (a planted zero, caught on every row — proving the predicate CAN fire, which the r0 predicate could not). Disposition: **the cleanest example in the corpus of a vacuous GREEN replaced by a falsifiable one.**

---

### EFF.GRTJC.s1of3.34  [instrument-record]  r1 — the new machine leg

**CANONICAL STATEMENT:** verbatim, lines 407–419.
**FORM:** bold-headed paragraph.

> “**New machine leg (r1):** `verification/openmath/grt_jc_r1_checks.py` under its
> own two-commit mini-seal (sealed UNRUN at `f45b63c`), testing the REPAIRED
> statements only. **VERDICT (§9.3): ~~10 families, 10,475 scored samples~~
> [r2, G-8: **10 families = 10,330 scored samples + TOOTH-ROW 145 = 10,475 over
> the 11-row table** — the r1 headline summed an 11-row table under a 10-family
> label], 0 violations, 29 rows, 2.6 s, exit 0; all five teeth fired (1,885
> firings)** —
> including (DMULT) exact on 2,784 samples, JC-COB's u = a_γa_{γ′} on 869/869
> anchor pairs, the corrected PSIKER range in both directions (197 lines below
> wΦ_NR with kernel 0; 197 residue classes with a certified nonzero witness), and
> G3's missing unit census (869 unit / 0 zero / 0 undefined / 0 out-of-window)
> with a planted-zero tooth proving the predicate can fire. The r0 battery, the
> instrument, and all their artifacts stay byte-frozen.**]**”

**SUPERSESSION KIND:** `counter re-reading` (r2/G-8: a headline that summed an 11-row table under a 10-family label).

**ARITHMETIC AUDIT (rule 22) — checked against §9.3's table (shard 3):** EXT-GATE 1 + R1-BND 29 + R1-PER 841 + R1-INJ 585 + R1-SURJ 841 + R1-DMULT 2,784 + R1-COB 2,607 + R1-PSIK-LO 591 + R1-PSIK-HI 1,182 + R1-UNIT 869 = **10,330** ✔; **+ TOOTH-ROW 145 = 10,475** ✔. **Both figures reconstruct exactly.** Teeth: T1 29 + T2 29 + T3 1,392 + T4 29 + T5 406 = **1,885** ✔ matches “1,885 firings”.

**PIN VERIFICATION:** `f45b63c` → **commit**; md5 `7f896bfa27d06158f95c5987c7299770` **EXACT at HEAD**; `grt_jc_r1_checks.py`, `grt_jc_r1_output.txt`, `grt_jc_r1_results.json` **all EXIST**.

**CONDITIONALITY:** **“testing the REPAIRED statements only”** — the leg is scoped to r1's own repairs, and the r0 battery is untouched. **Its own disclosed weakness (monomial-dominated samples + an undisclosed skip) is r2/G-2** (`.37`).

**DERIVATION:** Instrument description + verdict.

**RESOLUTION TRACE:** statement lines 407–419; the full table 2160–2253 (§9.3, shard 3); the disclosure 2255–2274 (shard 3).

**TEETH:** 10 families, 0 violations, **five teeth all fired**; **T4 is the tooth that proves R1-UNIT's predicate can fire at all** — the direct answer to G3.

---

### EFF.GRTJC.s1of3.35  [run-record]  REPAIR ROUND r2 — header

**CANONICAL STATEMENT:** verbatim, lines 421–432.
**FORM:** bold-headed bracketed block opener.

> “**[REPAIR ROUND r2 — 2026-08-08 campaign (wallclock 2026-08-05/06).** Applied
> against **JC-PE2** (`GRTJC_passPE2_report.md`, commit `4a76d52`): **0 CRITICAL,
> 9 gaps**. PE2 re-derived the whole r1 structure hostilely and independently —
> JC-LOC, JC-PIINV, JC-BSURJ, (COORD-B)(1)(2), (MULT-B), JC-COB,
> JC-PSIKER(ii)(iii) and **all five PE1 consumers** — and found **no false
> statement**; it also reproduced both batteries byte-for-byte and verified both
> seals. So r2 is a **labelling / footprint / disclosure round with ONE new
> machine leg**, not a restatement: **no clause changes grade, no measured
> quantity moves, and the r0 battery, the r1 battery, the instrument and all
> their artifacts stay BYTE-FROZEN** (r2 adds one new runner and touches nothing
> else in `verification/`). Dispositions, each edit carrying a dated `[r2, G#]`
> bracket, strike-and-replace:”

**★ THE STRONGEST INDEPENDENT ENDORSEMENT IN THE ARC:** PE2 re-derived **the whole r1 structural repair** hostilely and independently — eight named lemmas plus all five consumers — and found **no false statement**. **The r1 repair, which was the note's central move, survived a full hostile re-derivation.**

**PIN VERIFICATION:** `4a76d52` → **commit**; `GRTJC_passPE2_report.md` **EXISTS**.

**DERIVATION:** Round record.

**RESOLUTION TRACE:** statement lines 421–432; the dispositions 434–483 (`.36`–`.38`); the new leg 485–496 (`.39`).

**TEETH:** both batteries reproduced byte-for-byte, both seals verified. Disposition: **accepted-with-decorrelation-supplied**.

---

### EFF.GRTJC.s1of3.36  [supplier-finding]  ★★ r2/G-1 — the (DMULT) TIER SPLIT (the round's one item with content)

**CANONICAL STATEMENT:** verbatim, lines 434–447.
**FORM:** bold-headed bullet.

> “* **G-1 (the one with content) — `(DMULT)` was labelled "CITED, not proved
>   here" in its EXACT (multiplier-1) form, which §0's own transport statement
>   cannot deliver.** Split into two honest tiers in §2.10: **(DMULT-w)**, the
>   up-to-a-unit-cocycle form, **DERIVED here from §0's transport** (derivation
>   displayed), and **(DMULT-s)**, the exact form, **MEASURED (R1-DMULT 2,784/0
>   and r2's new R2-BIL/R2-PHI), NOT cited** — the attempt to verify the exact
>   form against the sources the note names FAILED in a specific, reportable
>   way: (IN-3)'s own transport clause delivers `𝑅 = c·R^{GMN}` only up to a
>   line-wise unit, and the corpus's sharpest harness↔literature read
>   dictionary, **open lemma TR-3′-GEN** (`GRB_ORDER2_2026-08-05.md` §S3.4), is
>   itself stated *"together with per-argument units"* and is OPEN beyond its
>   order-≤ 3 closed strata — so no corpus-pinned statement delivers
>   multiplier 1 (§2.10 [r2, G-1] quotes both). JC-COB's sharp `u = a_γa_{γ′}` is
>   re-fenced to ride **(DMULT-s)** explicitly, at every site.”

**SUPERSESSION KIND:** `replacement` — one mislabelled input split into two tiers with different epistemic statuses.

**★ THE NOTE'S SIGNATURE HONESTY MOVE, and the thing a chapter cut most needs from GRTJC.** Two tiers:
- **(DMULT-w)** — `𝑅_{λ+μ}(fg) = ω(λ,μ)·y^{δ}·𝑅_λ(f)·𝑅_μ(g)` with `ω(λ,μ) ∈ K_m^*` depending only on the lines. **DERIVED, with the derivation displayed** (substituting `𝑅_λ = c_λ·R^{GMN}_λ` into the literature identity gives `ω = c_{λ+μ}/(c_λc_μ)`, the 2-coboundary of the line-wise unit system). **This is the CITABLE tier and it carries everything load-bearing.**
- **(DMULT-s)** — `ω ≡ 1`. **MEASURED, NOT CITED.** The attempt to cite it **FAILED in a specific, reportable way**, and the note reports it: `(IN-3)`'s transport prices `𝑅 = c·R^{GMN}` at a line-wise unit, and TR-3′-GEN is OPEN beyond its closed strata. **“nothing gives ω ≡ 1.”**
- **Who rides which** is enumerated (shard 2, L1249–1260): `(COORD-B)(2)`, `(MULT-B)`, JC-CARRY-m, W-8 and JC-BOX-4's corner closure need only **(DMULT-w)**; **only JC-COB's sharp value rides (DMULT-s)**, and on the weak tier it degrades gracefully to JC-SPAN's already-proved `u ∈ K_m^*`. **“No clause GRADE changes between tiers.”**

**CONDITIONALITY — TWO POST-ACCEPTANCE ANNEXES LAND ON THIS UNIT:**
- **Annex #1** (shard 3, L2805): **(DMULT-s) is PROVED-conditional** on the measured perimeter (the `[ILN]†` scored stratum, `m ≥ 1`, `e_m ≥ 2`) by `DULEMMA_PROOF_2026-08-08.md` THEOREM DU, “riding [ILN]†+GRTJC+WELDMASTER as accepted plus DU-A/DU-B at 0/2”; “the `e_m = 1` row stays measured and off-stratum pairs stay open (DU-BOX-1/2)”. **So the MEASURED tier acquired a conditional proof after acceptance.**
- **Annex #6** (shard 3, L2917): **“The statement that (DMULT-w) is itself a quoted FGMN residual-product identity is WITHDRAWN.”** It is instead **DERIVED** from the PDF-verified rank-one theorem via **LEMMA JC-RANKMULT**. **So the CITABLE tier stopped being a citation and became a derivation — a strictly better footprint, and the third re-characterisation of this input.**

**CHAIN (rule 25) — the `(IN-3)(c)` / `(DMULT)` chain, FIVE layers.** r0: `(IN-3)(c)` on `gr` CITED → **r1/F1**: refuted on `gr`, re-based on `B`, reduced to the single cited input `(DMULT)` → **r2/G-1**: split into `(DMULT-w)` DERIVED / `(DMULT-s)` MEASURED → **Annex #1**: `(DMULT-s)` PROVED-conditional on the measured perimeter → **Annex #6**: `(DMULT-w)` itself WITHDRAWN as a citation and DERIVED from Thm 4.2's rank-one freeness. **TERMINAL = Annex #6's derivation + Annex #1's conditional proof.** `CHAIN HOME: s1of3.43.`

**DERIVATION:** Displayed at §2.10 (shard 2, L1208–1218).

**RESOLUTION TRACE:** statement lines 434–447; the tier split 1188–1267 (shard 2); the consumer split 1249–1260 (shard 2); **Annex #1 at 2805, Annex #6 at 2917–3000 (shard 3)**.

XREF: `lean/notes/openmath/GRB_ORDER2_2026-08-05.md:TR-3′-GEN` — count **57** · `S3.4` — count **25** · `S6a` — count **8**. `lean/notes/openmath/DULEMMA_PROOF_2026-08-08.md` — **file EXISTS**.

**TEETH:** **(DMULT-s)** is measured by **R1-DMULT** (2,784/0, exact multiplier 1) and **R2-BIL/R2-PHI** (261 dense bilinear pairs, 0 violations), with teeth **T3** (1,392 firings) and **U1/U2** (261/261 each). **(DMULT-w)** carries no separate leg — it is implied by the exact tier's measurements and, post-Annex #6, derived. Disposition: **executable regression for the exact tier; DERIVATION for the weak tier**.

---

### EFF.GRTJC.s1of3.37  [instrument-record]  ★ r2/G-2 — monomial-dominated samples and an undisclosed skip

**CANONICAL STATEMENT:** verbatim, lines 448–460.
**FORM:** bold-headed bullet.

> “* **G-2 — R1-DMULT's samples are monomial-dominated and its one
>   non-monomial × non-monomial pair was `continue`d UNDISCLOSED.** (a) the
>   sample composition and the skip are now disclosed in §9.3 [r2, G-2]; (b) the
>   real leg is r2's new runner `verification/openmath/grt_jc_r2_checks.py`
>   (§9.4, own two-commit mini-seal), which builds **dense multi-slot digit
>   polynomials on BOTH factors** by the JC-BSURJ construction and tests (DMULT)
>   on genuinely bilinear input (family **R2-BIL**), scores the r1-skipped pair
>   (Φ_{m+1}, Φ_{m+1}) on every row (**R2-PHI**), machine-checks the r1 sample
>   composition itself (**R2-MONO**: ≤ 1 multi-slot element per row, every
>   r1-tested pair had a single-slot factor), and plants the **cross-term tooth
>   U2** — the convolution-killing mutation that is provably SILENT on every
>   r1-tested pair (censused at 0 fires there) and must fire on the new dense
>   pairs.”

**SUPERSESSION KIND:** `counter re-reading` (the sample composition re-read) + `inventory completion` (the undisclosed skip disclosed).

**★ THE FINDING AND ITS REPAIR ARE BOTH EXEMPLARY, and the pattern is worth naming.** **The finding:** R1-DMULT's per-row sample list has seven elements, **six of them single-slot (monomial)**, and the loop `continue`d the one non-monomial × non-monomial pair `(Φ_{m+1}, Φ_{m+1})` — **so on every one of its 48 ordered pairs per row, `y^δ·𝑅(f)·𝑅(g)` is a shift-and-scale of one factor, and the identity's genuinely BILINEAR content was NEVER exercised.** The verdict cell was “true but weaker than it reads”. **The repair does four things:** builds genuinely dense × dense input (R2-BIL); scores the skipped pair (R2-PHI); **machine-checks the sample-composition claim itself rather than asserting it (R2-MONO)**; and plants a tooth (U2) that is **provably silent on every r1-tested pair and must fire on the new ones** — a separation the tooth was designed to exhibit, and it did (261/261 vs 0).

**CONDITIONALITY:** **The r2 leg has its OWN disclosed weakness, found at r3/G-3** (`.24`): the dense set's “mixed variant” collapses to the “ones” variant on 13/29 rows, including both `g_m = 2` rows. **So the species recurred inside the fix.**

**ARITHMETIC AUDIT (rule 22):** seven sample elements, six single-slot, one multi-slot (`Φ_{m+1}`, whose digit polynomial is `ψ_m`) ✔; “48 ordered pairs per row” is consistent with 7 elements minus the skipped pair under the loop's own ordering ✔ (7×7 = 49, minus 1 skip = 48) — **and this compiler notes the arithmetic works exactly, which is itself evidence the disclosure is accurate.**

**PIN VERIFICATION:** `grt_jc_r2_checks.py` **EXISTS**, md5 `c02bf06029a72259512ea005bd2562fd` **EXACT at HEAD**; `grt_jc_r2_output.txt`, `grt_jc_r2_results.json` **EXIST**.

**DERIVATION:** A code audit of the byte-frozen r1 runner, confirmed against source.

**RESOLUTION TRACE:** statement lines 448–460; the disclosure 2255–2274 (§9.3, shard 3); the r2 leg 2282–2331 (§9.4, shard 3); the recurrence 2333–2362 (§9.4 [r3, G-3], shard 3).

**TEETH:** **U2 — the cross-term drop**, “PROVABLY equal to the true product whenever either factor has ≤ 2 occupied slots … hence silent on every r1-tested pair (scored as R2-MONO(c)) — and provably different on a dense deg-2 × dense deg-2 pair”. **Fired 261/261 on the new pairs, 0 on the r1 pairs.** Disposition: **planted mutant with a machine-proved resolution separation** — the strongest tooth design in either note.

---

### EFF.GRTJC.s1of3.38  [changes-record]  r2 — the seven remaining dispositions, assembled

**CANONICAL STATEMENT:** [ASSEMBLED — the r2 bullets G-3 … G-9, lines 461–483, quoted verbatim in source order.]

**MERGE CRITERION (stated):** seven labelling/footprint/disclosure corrections with no grade movement and no independent citation. **G-1 and G-2 are separate units** (`.36`, `.37`) because one splits an input into two tiers and the other rebuilds an instrument.

`[TABLE — compiler ledger]` r2's seven remaining gaps.

| bullet | lines | what it corrects | the corrected content |
|---|---|---|---|
| **G-3** | 461–463 | a stale smoke value | §2.10's pre-seal `c_π` quote (`{1, z̄, z̄²}`, a **6-row smoke value labelled “across the roster”**) replaced by the as-of-r1 ROSTER value set from the committed artifact: **`c_π ∈ {1, z̄, z̄², z̄³, z̄⁴, z̄⁶, z̄⁸}`** — 1 on 9 rows, z̄ on 9, z̄² on 7, and the rest on single rows |
| **G-4** | 464–469 | the `[r1]` bracket leak | every live site still naming the STRUCK `(COORD)`/`(MULT)` re-pointed to `(COORD-B)`/`(MULT-B)`, **including the two honesty defects PE2 named** — the **W-7 THEOREM box's OB-4 grade line** (which graded OB-4 on the refuted input and denied r1's own machine leg) and §4.1 remark (b)'s footprint sentence. Re-grepped to fixed point |
| **G-5** | 470–472 | an unlicensed quantifier | `(MULT-B)`'s and TC-3's all-of-ℤ quantifiers: the window/virtual-anchor transport is now an **explicit displayed step**, not a parenthesis |
| **G-6** | 473–478 | an asserted identification | JC-LOC's identification of the note's own extension of `w` with the literature's valuation: **DERIVED** (three displayed steps G6-1/G6-2/G6-3), with the **additivity** of the degreewise map supplied. The residual tie is **W-1, already in §0's stack — not a new input** |
| **G-7** | 479–480 | a box's status | “JC-BOX-4 (unchanged)” corrected at both sites — **the box DID change**: it gained an `[r1]` conditional closure |
| **G-8** | 481–482 | a headline figure | §9.3's headline decomposed: **10 families = 10,330 scored samples**, plus TOOTH-ROW 145 = **11 rows / 10,475** |
| **G-9** | 483 | an unwritten step | the one-line **ideal transport along JC-GAUGE(iii)** written out |

**★ TWO OF THE SEVEN ARE HONESTY DEFECTS PE2 NAMED BY THAT WORD (G-4).** The W-7 THEOREM box's OB-4 grade line **graded a clause on an input PE1 had REFUTED, and simultaneously denied the note's own machine leg for it** — surviving an entire round inside a THEOREM box. **A strike system can leak into the very boxes it is meant to protect.**

**CONDITIONALITY:** G-6's derivation is load-bearing: it converts “B *is* the object FGMN's theorems speak about” from a phrase (“the same construction on K[x]”) into three displayed steps, and the note is careful that **“G-6 adds no new conditionality; it removes the ‘same construction’ hand-wave.”** G-5's transport step is what licenses every all-of-ℤ quantifier downstream.

**DERIVATION:** Per item.

**RESOLUTION TRACE:** statement lines 461–483; the targets 1135–1143 (`c_π`, shard 2), 1444–1455 (the OB-4 grade line, shard 2), 1297–1315 (the (G5-i)/(G5-ii) transport, shard 2), 1064–1099 (G6-1..3, shard 2), 2004–2027 (JC-BOX-4, shard 3), 2209–2215 (§9.3's headline, shard 3), 1389–1396 (the ideal transport, shard 2); the sweep record 2371–2419 (§9.5, shard 3).

**TEETH:** G-3 → **R1-PER**'s per-row `c_π` census (841 samples, 0 violations; **`c_π ≠ 1` on 20 of 29 rows**, which is why the ρ-normalization is load-bearing rather than cosmetic). G-8 → the arithmetic audit at `.34`. Others: record.

---

### EFF.GRTJC.s1of3.39  [instrument-record]  r2 — the bilinearity leg

**CANONICAL STATEMENT:** verbatim, lines 485–496.
**FORM:** bold-headed paragraph.

> “**New machine leg (r2):** `verification/openmath/grt_jc_r2_checks.py` under its
> own two-commit mini-seal (commit 1 = the runner, sealed UNRUN at `79611a4`,
> prereg in its docstring = §9.4's table; commit 2 = the verdict FROM the
> committed artifacts), testing ONLY the bilinearity content of (DMULT) and the
> disclosure census. **VERDICT (§9.4): ALL 4 FAMILIES GREEN — 3,655 table rows
> (3,597 in-family + TOOTH-ROW 58), 0 violations, 29 rows, exit 0; U1 261/261,
> U2 261/261, no silent tooth; (DMULT-s) exact on 261 dense bilinear pairs; the
> r1-skipped pair scored on 29/29 (bilinear content on exactly C2I/C4I, the two
> g_m = 2 rows); U2 fired 0 times on the r1-tested pairs — the r1 leg had zero
> resolution against the cross-term class.** See **§9.4** for the
> preregistration and verdict, and **§9.5** for the r2 bracket-sweep
> record.**]**”

**ARITHMETIC AUDIT (rule 22) — checked against §9.4 (shard 3):** EXT-GATE 1 + R2-BIL 696 + R2-PHI 87 + R2-MONO 2,813 = **3,597** ✔; **+ TOOTH-ROW 58 = 3,655** ✔. **Both reconstruct exactly.** R2-PHI 87 = 29 rows × 3 checks ✔. U1 = U2 = 261 = 29 rows × 9 ordered pairs ✔.

**★ THE SHARPEST SENTENCE IN THE NOTE'S EVIDENCE RECORD:** **“U2 fired 0 times on the r1-tested pairs — the r1 leg had zero resolution against the cross-term class.”** That is a *machine proof that a prior leg was blind to a specific mutation class* — not an argument, a measurement. **And the r1-skipped pair turns out to have genuine bilinear content on exactly the two `g_m = 2` rows (C2I, C4I): “on those two, r1's one true bilinear pair was the skipped one.”**

**CONDITIONALITY:** **The leg imports the byte-frozen r1 helpers on purpose** — “imported, not re-typed, so the (DMULT) predicate is the SAME predicate PE2 audited as independent”. **So it is not a decorrelated second implementation; it is the same predicate on better input.** And its own diversity is overstated until r3/G-3 (`.24`).

**PIN VERIFICATION:** `79611a4` → **commit**; `db12666` → **commit**; md5 **EXACT at HEAD**; all three artifacts **EXIST**.

**DERIVATION:** Instrument description + verdict.

**RESOLUTION TRACE:** statement lines 485–496; the table 2282–2331 (§9.4, shard 3); the diversity disclosure 2333–2362 (shard 3).

**TEETH:** **U2's resolution separation (261/261 on dense pairs, 0/48-per-row on r1 pairs)** is the design; **R2-MONO scores the sample-composition claim itself** rather than asserting it. Disposition: **planted mutant + a scored disclosure** — the pattern FREEZE PREDICATE 3 generalises.

---

### EFF.GRTJC.s1of3.40  [fence]  §0 — the conditionality-stack head

**CANONICAL STATEMENT:** verbatim, lines 500–503.
**FORM:** display (an H2 heading) + paragraph.

> “## §0. INPUTS AND THE CONDITIONALITY STACK (read before any clause)
>
> Every clause below is stated with its inputs named. There are five, and no
> clause is stronger than the weakest input it uses.”

**CONDITIONALITY:** **“no clause is stronger than the weakest input it uses” is the note's governing conditionality rule** — the analogue of GRTJB's §0M matrix, but stated as a principle rather than a table. **The consequence is that §10.2's one-line stack IS the note's conditionality of record**, and every grade in §10.1 is read against it.

**DERIVATION:** Declaration.

**RESOLUTION TRACE:** statement lines 500–503; the five inputs 505–571 (`.41`–`.45`); the one-line stack 573–604 (`.46`); §10.2's restatements 2687–2748 (shard 3).

**TEETH:** NONE (declaration).

---

### EFF.GRTJC.s1of3.41  [hypothesis]  (IN-1) [ILN]† — the accepted closed form, and its residuals

**CANONICAL STATEMENT:** verbatim, lines 505–517.
**FORM:** bold-headed paragraph + display.

> “**(IN-1) [ILN]† = (ITER-LAW-n), ACCEPTED** (`ITERLAWN_PROOF_2026-08-08.md`,
> arc closed 2026-08-03 at the 2-clean model-diverse bar; PC6 CLEAN + PE7 CLEAN).
> Scope as accepted: for all n ≥ 1 on the (n+1)-read **standard-lift** harness
> class, the closed form for the harness value cocycle
>
>     c_{n+1}(γ,γ′) = z̄^δ · ∏_{j=1}^{n} z_j^{D_j},   δ = ⌊(s_{n+1}(γ)+s_{n+1}(γ′))/e_n⌋,
>
> with residuals: the open engine families (RM-m, m ≥ 2) and (W-MULT-DCX-m), the
> fenced corners, and DCX-(n) = ∪_m DCX_m excluded. **In this note c_T denotes
> this closed form**, and "the scored stratum" means [ILN]†'s own: all D_j
> integral ∧ the pair off DCX. (Instrument census: on its 29-row roster **DCX
> pairs 0, non-integral-D pairs 0** — the whole grid sat inside the accepted
> stratum.)”

**CONDITIONALITY:** **ACCEPTED, but with four named residuals riding through**: the open engine families `(RM-m, m ≥ 2)` and `(W-MULT-DCX-m)`, the fenced corners, and `DCX-(n)` excluded. **Plus standard-lift only** — JC-BOX-6 (shard 3) adds the `(ITER-LAW-LIFT)` residual, “open exactly at `g_0 = 1 ∧ δ_1 = 1`”. **The instrument's grid sat entirely inside the accepted stratum (0 DCX pairs, 0 non-integral-D pairs) — which means the off-stratum half of §3.2's existence claim has ZERO machine support** (JC-BOX-2, shard 3).

**GENERALITY NOTE (Q7, recorded not applied).** Q7 classifies GRTJC's base formulation **GENERAL**: *“‘Fix a complete DVR O with uniformizer π and finite residue field’ — **GENERAL FORMULATION.** The base object is not restricted to a finite extension of ℚ_p.”* No edit; recorded.

**DERIVATION:** Consumption declaration.

**RESOLUTION TRACE:** statement lines 505–517; `c_T`'s definition 655–658 (`.56`); the off-stratum box 1946–1951 (JC-BOX-2, shard 3); the lift residual 2039–2048 (JC-BOX-6, shard 3).

XREF: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md:ITER-LAW-n` — count **11** · `PC6` — count **3** · `PE7` — count **3** · `DCX` — count **115**.

**TEETH:** the instrument's own census (0 DCX, 0 non-integral-D on 29 rows). Disposition: **measurement**, and it is the measurement that makes JC-BOX-2's disclosure necessary.

---

### EFF.GRTJC.s1of3.42  [hypothesis]  (IN-2) GRB / D-REAL / CARRY-1 / (W-MULT) — the last-read layer

**CANONICAL STATEMENT:** verbatim, lines 519–526.
**FORM:** bold-headed paragraph.

> “**(IN-2) GRB Lemma D-REAL + CARRY-1 + (W-MULT), ACCEPTED-WITH-CONDITIONS**
> (`GRB_ORDER2_2026-08-05.md` §S5.2/§S6a; conditional on the GRB §0 ladder
> ((V1)_{≤i+1}, (KP)_{≤i−1}, (H-CHAIN)) and the §3.3 [T] pins — that
> conditionality is inherited here forever). This is the **last-read layer**: the
> gauged anchor system at the last read is K_{m+1}[u]/(u^{e_m} − z̄), CARRY-1 is
> φ_γφ_{γ′} = φ_{γ+γ′}·ȳ^δ at that layer, and (W-MULT) is
> R^{gr}_{γ+γ′}(αβ) = y^{δ}R^{gr}_γ(α)R^{gr}_{γ′}(β). **CONSUMED, NOT RE-PROVED.**
> J-C(i) is this layer; §§2–5 below are the composite-stage content.”

**CONDITIONALITY:** **“ACCEPTED-WITH-CONDITIONS … that conditionality is inherited here forever”** — an unusually strong inheritance statement. The conditions are the GRB §0 ladder `((V1)_{≤i+1}, (KP)_{≤i−1}, (H-CHAIN))` and the §3.3 `[T]` pins.

**★ THE STRUCTURAL ROLE:** this is the **last-read layer**, where the anchor system is `K_{m+1}[u]/(u^{e_m} − z̄)` and CARRY-1 has **no extra factor**. **§3.2's THEOREM JC-CARRY-m is the composite-stage generalization, and the whole content of the generalization is that ONE extra `K_m`-unit appears** — “the extra factor at a composite stage is exactly one K_m-unit, and the theorem locates it” (shard 2, L1491–1495).

**GENERALITY NOTE (Q7, recorded not applied).** Q7's INTERFACE row for GRB: *“Its ladder hypotheses and last-read carry algebra must not rely on `v(p) < ∞`, `p` odd, or characteristic zero.”* — an out-of-slice obligation, **not audited by Q7 and not discharged here**. Recorded.

**DERIVATION:** Consumption declaration.

**RESOLUTION TRACE:** statement lines 519–526; the composite-stage generalization 1479–1508 (§3.2, shard 2); the stack 573–604 (`.46`).

XREF: `lean/notes/openmath/GRB_ORDER2_2026-08-05.md:D-REAL` — count **44** · `CARRY-1` — **19** · `(W-MULT)` — **8** · `S5.2` — **12** · `S6a` — **8** · `(V1)` — **4** · `(KP)` — **10** · `(H-CHAIN)` — **35**.

**TEETH:** consumed, not re-proved; the composite-stage instance is keyed by JC3 (JC-SPAN, 609/609).

---

### EFF.GRTJC.s1of3.43  [hypothesis]  ★★ (IN-3) — THE FGMN GRADED PACKAGE (the CITE-SCOPE unit and the chain home)

**CANONICAL STATEMENT:** verbatim, lines 528–557 — the package header, the five clauses (a)–(e) with the `[r4, G-4]` content-line annotation on (c), and the arbitrary-order/transport paragraph.
**FORM:** bold-headed paragraph + a fixed-width clause list.

> “**(IN-3) The FGMN graded package, CITED LITERATURE, transported by W-1.** As
> pinned and quoted in the corpus (`GRB_ORDER2_2026-08-05.md` §S6a verbatim: "Thm
> 4.2 three times … gr_K(w) is a domain … Thm 4.8 (evaluation at ȳ is an
> isomorphism F_r[y] → Δ) … ord_y-additivity from s(gh) = s(g) + s(h), Cor 2.7"):
>
>     (a) w = w_{m+1} is multiplicative: w(fg) = w(f) + w(g);
>     (b) gr(w) is a DOMAIN, and in(fg) = in(f)·in(g);
>     (c) gr_γ(w) is FREE OF RANK ONE over Δ ≅ K_m[y] on the anchor basis
>         in(φ_γ) at attained γ  [Thm 4.2]
>         [r4, G-4 — CONTENT-LINE ANNOTATION (this clause's first line carries
>         no swept name — its tag sits on the line above — so it is invisible
>         to §9.5's NAME-pattern census; PE1's CRITICAL 1 quoted exactly this
>         display): the freeness displayed here is FGMN's statement about
>         FGMN's OWN object, gr = gr_K(w) on K[x] (the §S6a quotation above);
>         on THIS note's gr(w) — §1's O[x] object — the transported claim is
>         REFUTED (PE1 CRITICAL 1; §2.10 [r1, F1]). This note consumes the
>         clause ONLY through JC-LOC, as (DMULT-w) on B ≅ gr_{K[x]}(w)
>         (§2.10, JC-BOX-3 [r1]) — the same re-route pointer every other
>         formerly-misaimed display carries.];
>     (d) evaluation y ↦ z̄ is an isomorphism K_m[y]/(ψ_m) ≅ K_{m+1}
>         [Thm 4.8 / Cor 4.9]
>     (e) the minimal on-line Φ_m-abscissa is additive: s(fg) = s(f)+s(g)
>         [Cor 2.7].
>
> FGMN state these for types of ARBITRARY order, so the composite-stage instance
> is a citation, not an extrapolation by this note — **but the theorem numbering
> above is the corpus's pinned quotation, re-verified against no printed source in
> this session (citation-precision owed; flagged in JC-BOX-3).** Their transport to
> the HARNESS objects (w = v_{m+1} in the sheared frame; R_{m,λ} = c·R_λ^{GMN} with
> c a line-wise unit) is **W-1 (J-A), ATTEMPT GRADE**.”

**Double-emission (rule 14) — the five clauses as a `[TABLE]`, with their status at HEAD:**

| clause | statement | cited as | status at HEAD |
|---|---|---|---|
| **(a)** | `w = w_{m+1}` is multiplicative: `w(fg) = w(f)+w(g)` | §S6a | **LIVE, never refuted** — consumed by JC-DOM (twice) and JC-LOC's G6-1/G6-3. **Added to the stack displays only at r5/G-2** |
| **(b)** | `gr(w)` is a DOMAIN, and `in(fg) = in(f)·in(g)` | §S6a | **LIVE, never refuted** — JC-DOM, JC-LOC's proof, (MULT-B) and its `\|gr` display. **Added at r5/G-2** |
| **(c)** | `gr_γ(w)` is FREE OF RANK ONE over `Δ ≅ K_m[y]` on `in(φ_γ)` at attained `γ` | **Thm 4.2** | **REFUTED as transported to `gr_{O[x]}` (PE1 CRITICAL 1).** Consumed ONLY through JC-LOC as `(DMULT-w)` on `B ≅ gr_{K[x]}(w)`. **Struck from the stack one-liner at r4/G-1. Post-acceptance, Annex #6 DERIVES (DMULT-w) from this clause rather than quoting a product law** |
| **(d)** | evaluation `y ↦ z̄` is an isomorphism `K_m[y]/(ψ_m) ≅ K_{m+1}` | **Thm 4.8 / Cor 4.9** | **LIVE, unchanged.** Consumed at §4.3 (the residue chain) and at TC-3's identification. **PDF-VERIFIED as a pair-cite at Annex #3** |
| **(e)** | the minimal on-line `Φ_m`-abscissa is additive: `s(fg) = s(f)+s(g)` | **Cor 2.7** | **LIVE, unchanged.** Consumed by JC-SPAN's lower-end argument. **PDF-VERIFIED at Annex #3, with a display-precision note** |

**★ CHAIN HOME (rule 25) — the `(IN-3)(c)` / `(DMULT)` chain, FIVE layers.** Recorded once, here, with every member's home:
1. **r0** — `(IN-3)(c)` CITED on `gr` (this display).
2. **r1/F1** (`.31`) — REFUTED on `gr`; re-based on `B`; reduced to the single cited input `(DMULT)`.
3. **r2/G-1** (`.36`) — SPLIT: `(DMULT-w)` DERIVED from §0's transport / `(DMULT-s)` MEASURED, not cited.
4. **Annex #1** (shard 3) — `(DMULT-s)` **PROVED-conditional** on the measured perimeter by DULEMMA THEOREM DU.
5. **Annex #6** (shard 3) — the claim that `(DMULT-w)` is a quoted FGMN product identity is **WITHDRAWN**; it is **DERIVED** from the PDF-verified rank-one theorem via **LEMMA JC-RANKMULT**.
**TERMINAL: Annex #6's boxed stack entry** — “FGMN (a)(b) + Thm 4.2 rank-one freeness on `B` via JC-LOC + Thm 4.8/Cor 4.9 + Cor 2.7; **(DMULT-w) derived above**; (DMULT-s) as in Annex #1.”
**Alias-sweep members (the parallel chain):** r2/G-4 → r3/G-1 (`.22`) → r4/G-1 (`.17`) → the disclosed protocol limit (`.20`).

**★ READING NOTE (external, not an edit) — THE CITE-SCOPE ROW AND ITS RESOLUTION.** `runs/qgen/Q7_output.log` flags GRTJC at **H6** twice, and calls one of them *“the only potentially mixed-characteristic-sensitive citation gap I found”*:

> “‘Print: “Let `g∈K[x]` be a non-zero polynomial … `𝒫_α(µ)/𝒫_α^+(µ)` is a free `Δ`-module of rank one.”’ — **CITE-SCOPE.** The annex verifies the printed conclusion and numbering, but the pasted quotation does not include the paper's standing assumptions on `K` and `µ`. That missing published scope is the only potentially mixed-characteristic-sensitive citation gap I found.”
> “‘Print: “For non-zero `g,h∈K[x]`, we have `S_λ(gh)=S_λ(g)+S_λ(h)`.”’ — **CITE-SCOPE, same source-scope issue.** The formula itself is characteristic-free.”

`docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` resolves BOTH, and the verdicts are the strongest in the whole resolution document:

- **NS-10** (clause (c), the rank-one freeness) — **verdict COVERS-ALL-O**, with the flag diagnosed: *“**[FGMN] §4, layout line 1030**, verbatim: ‘In particular, `P_α(µ)/P_α^+(µ) = φ_r(α)Δ` is a free `Δ`-module of rank one.’ — inside [FGMN]'s §1 standing setting (‘Let `K` be a field equipped with a discrete valuation `v`’). … ***The audit's flag was a pasting artefact, not a real gap:*** the quotation omitted [FGMN]'s standing hypotheses, which are already the general ones. **No edit to the mathematics is needed — only re-paste the §1 setting sentence next to the quote.**”*
- **NS-9** (clause (e), Cor 2.7) — **verdict COVERS-ALL-O**: *“[FGMN] **Theorem 2.8** (layout line 546) and **Corollary 2.7** (line 525, verbatim): ‘For non-zero `g,h∈K[x]`, we have `S_λ(gh)=S_λ(g)+S_λ(h)`.’ — **the exact sentence GRTJC prints, at FGMN's “field equipped with a discrete valuation” scope.** … **The GRTJC row is a *verbatim* re-cite: same sentence, wider scope.**”* With an independent second source: **[AGNPRW] Theorem 4.6 + Corollary 2.9**.

**PIN VERIFICATION BY THIS COMPILER (rule 23) — the FGMN standing setting and every cited line, re-read at HEAD in `docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt`:**

| cite | note's / NS's line pin | text at that line | verdict |
|---|---|---|---|
| **§1 standing setting** | 137 | “Let K be a field equipped with a discrete valuation v : K ∗ −→ Z, normalized so that…” | **EXACT — and it is the GENERAL setting, no completeness, no residue-field hypothesis** |
| Cor 2.7 | 525 | “Corollary 2.7. For non-zero g, h ∈ K[x], we have Sλ (gh) = Sλ (g) + Sλ (h).” | **EXACT** |
| Thm 2.8 | 546 | “Theorem 2.8. Let µ be a valuation and φ a key polynomial for µ. Then, Nµ,φ (gh) =…” | **EXACT** |
| §3.3 def of ψ_i | 862 | “ψi ∈ Fi [y], minimal polynomial of zi over Fi .” | **EXACT** |
| eq (14) | 1004 | “(14)  Ri,α (φsi ) = y ⌊s/ei ⌋ , Ri (φsi ) = 1, 1 ≤ i ≤ r.” | **EXACT** |
| Thm 4.2 | 1028 | “Theorem 4.2. Let g ∈ K[x] be a non-zero polynomial and let α = µ(g). Then,” | **EXACT** |
| the rank-one clause | 1030 | “In particular, Pα (µ)/Pα+ (µ) = ϕr (α)∆ is a free ∆-module of rank one.” | **EXACT** |
| Cor 4.7 | 1121 | “Corollary 4.7. Let 0 ≤ i ≤ r and α ∈ Γi .” | **EXACT** |
| Thm 4.8 | 1136 | “Theorem 4.8. The mapping Rr,0 : ∆ −→ Fr [y] is an isomorphism of Fr -algebras and” | **EXACT** |
| **Cor 4.9** | **note says 1153** | line 1153 reads “κ(µ)alg ≃ Fr and the next result follows.”; **Corollary 4.9 is at line 1151** | **NEAR-MISS — off by two. Content EXACT at L1151: “Corollary 4.9. For all 0 ≤ i < r, Fi+1 = Fi [zi ] = F0 [z0 , . . . , zi ] and deg ψi = fi .”** |
| Lemma 5.13 | 1403 | “Lemma 5.13. For non-zero g, h ∈ K[x] with g µ-proper, we have R(gh) = R(g)R(h).” | **EXACT** |

**10 of 11 line pins EXACT; one NEAR-MISS off by two lines with the content verified.** Recorded as source defect 3. **PDF md5 `da846c82f1fcb619cefb3feb8164191e` re-computed at HEAD: EXACT.**

**The note's own text is compiled as written; the NS-9/NS-10 retargets are RECORDED, NOT APPLIED.**

**CONDITIONALITY:** **The transport to the HARNESS objects is W-1 (J-A) at ATTEMPT GRADE** — and that transport, not the citation, is the live weak link: “Transport of the harness `w` and `𝑅` to the FGMN objects is still W-1 (ATTEMPT)”, with TR-3′-GEN “OPEN at general order and unit-valued where closed” (JC-BOX-3 item 3, shard 3). **The citation-precision flag (“re-verified against no printed source in this session”) was DISCHARGED post-acceptance by Annex #3 against the PDF.**

**DERIVATION:** Consumption declaration; the corpus's pinned quotation from GRB §S6a.

**RESOLUTION TRACE:** statement lines 528–557; the refutation and repair 992–1414 (§2.10, shard 2); the box 1960–1992 (JC-BOX-3, shard 3); **Annexes #2, #3 (numbering discharged) at 2807–2815, Annex #6 (the derivation) at 2917–3000 (shard 3)**.

XREF: `lean/notes/openmath/GRB_ORDER2_2026-08-05.md:S6a` — count **8**. `docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt` — **EXISTS**. `docs/references/fgmn_residual_ideals_1305.0775v3.pdf` — **EXISTS, md5 EXACT**.

**TEETH:** **AUDIT — decorrelated-model audit** (Q7's CITE-SCOPE flag) **+ transfer audit** (Annexes #2/#3's numbering verification, first at the text extraction then at the PDF under the extraction-decorrelation rule). **The mathematics itself is measured by R1-DMULT / R2-BIL.**

---

### EFF.GRTJC.s1of3.44  [hypothesis]  (IN-4) W-2 / J-A / J-B — and the inherited J-B geography

**CANONICAL STATEMENT:** verbatim, lines 559–565.
**FORM:** bold-headed paragraph.

> “**(IN-4) W-2 / J-A / J-B, ATTEMPT GRADE (counter 0/2).** W-2 (the lift junction,
> `GRTW2_PROOF_2026-08-08.md`), J-A (the dictionary), J-B (the tree;
> `GRTJB_PROOF_2026-08-08.md`, whose JB-BOX-2 conditionality — (VD-m) free only at
> m ≤ 1, JA-VDIND at m ≥ 2, JA-BOX-2's (R-coll) at m ≥ 3, the pinned-ℓ orbit,
> the shared-key perimeter q ≤ qcap — rides in wherever a print-residual statement
> is used). §5's germ display cites J-B's JB-CREAD + JB-EPS and inherits their
> fences verbatim.”

**★ THE J-B ↔ J-C INTERFACE, from the consumer side — and the compiler's cross-read anchor.** This unit is the exact counterpart of `spec/EFF-GRTJB-s2of3.md` `.54` (GRTJB's carry-seed remark). **Both sides agree, and the agreement is verifiable:**
- **GRTJB supplies** “`ρ_m(R) = −z_{m+1}·ρ_m(f)` … the semantic germ the J-C carrier block (W-6..W-9) needs — displayed here as an identity of READ VALUES only; no graded-ring (gr) object is constructed or claimed, and BLOCKED-ON-CARRIER-TIE stands.”
- **GRTJC receives** it here at ATTEMPT grade with JB-BOX-2's geography riding in verbatim, and **§3.3 (shard 2) splits it honestly** — CONFIRMED as a value law on all 27 eligible `g_m = 1` stages; **REFUTED as OB-3's inner factor on 138/669 pairs.**
- **Neither side retires the gate.** GRTJB: “BLOCKED-ON-CARRIER-TIE stands”. GRTJC §10.3: “**The tie is displayed, the gate stands.**”

**CONDITIONALITY:** **STALE on the supplier grades.** “W-2 / J-A / J-B, ATTEMPT GRADE (counter 0/2)” — at HEAD **all three are ACCEPTED at 2/2** (GRTW2 `adc6cf3`, GRTJA `17d2a32`, GRTJB PE9/PE10). **No GRTJC append records this** (unlike GRTJB, whose 2026-08-08 annex records its own suppliers' upgrades). **Recorded as OPEN-CALL 3.** **The inherited JB-BOX-2 geography is NOT stale and rides at HEAD**; and GRTJB's own post-acceptance annexes E-3/E-4 further correct two of its displayed statements, **which GRTJC cannot know about** — see OPEN-CALL 3.

**GENERALITY NOTE (Q7, recorded not applied).** Q7's INTERFACE row: *“The transported MacLane valuation and residual operator must be available over equal-characteristic complete DVRs. **J-B's external GMN cite-scope issue above remains inherited.**”* — i.e. GRTJB's H6 CITE-SCOPE row (NS-11) propagates here. Recorded.

**DERIVATION:** Consumption declaration.

**RESOLUTION TRACE:** statement lines 559–565; the germ display 1525–1548 (§3.3, shard 2); the consumer entry 2752–2759 (§10.3, shard 3); the supplier side `spec/EFF-GRTJB-s2of3.md` `.54` and `spec/EFF-GRTJB-s3of3.md` `.32`/`.33`.

XREF: `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md:JB-BOX-2` — grep-verified count **45** at HEAD. `GRTJB_PROOF_2026-08-08.md:JB-CREAD` — count **36**. `GRTJB_PROOF_2026-08-08.md:JB-EPS` — count **30**. `GRTJB_PROOF_2026-08-08.md:JB-BOX-4` — count **2**. (The reverse edges are verified from the GRTJB side too: `spec/EFF-GRTJB-s2of3.md` §3.1 rows 64–67 record `GRTJC:JB-CREAD` **2**, `JB-EPS` **4**, `JB-BOX-2` **3**, `JB-BOX-4` **2**.)
XREF: `lean/notes/openmath/GRTW2_PROOF_2026-08-08.md:W2-C1` — count **22**.

**TEETH:** inherited; §3.3's confirmation is the instrument's 27-stage measurement.

---

### EFF.GRTJC.s1of3.45  [hypothesis]  (IN-5) — the construction layer

**CANONICAL STATEMENT:** verbatim, lines 567–571.
**FORM:** bold-headed paragraph.

> “**(IN-5) The corpus's own construction layer, ACCEPTED as part of [ILN]†:** the
> class pin ([ILN]† S0.1: ψ_j monic irreducible with ψ_j(0) ≠ 0, gcd(e_j,h_j) = 1,
> g_j ≥ 1), the split/anchor conventions (S0.2), REALIZE-(m) with its R1/R2/R3 laws
> (S4.1: deg < deg Φ_m, w = β, read = τ), and the level reads. Everything in §1 is
> definition, not claim.”

**★ “Everything in §1 is definition, not claim” is the sentence that makes §1 emittable as pure definitions** (`.47`–`.56`) with no proof obligations of their own.

**CONDITIONALITY:** ACCEPTED as part of [ILN]†, so it inherits `(IN-1)`'s four residuals. **REALIZE's R1/R2/R3 are load-bearing throughout**: R1 at JC-ANCHMON and §4(ii)'s digit list, R2/R3 at the scalar lift, R3 at `c_m = ψ_{m,0}`.

**GENERALITY NOTE (Q7, recorded not applied).** Q7 on the class pin: *“‘ψ_j monic irreducible with ψ_j(0) ≠ 0’ — **BENIGN.** Again, only the field quotient and unit status are used. **No derivative or separability assertion occurs.**”* No edit; recorded.

**DERIVATION:** Consumption declaration.

**RESOLUTION TRACE:** statement lines 567–571; §1's objects 608–658 (`.47`–`.56`); **Annex #8's scope repair on `Λ_N`/REALIZE at 3014–3037 (shard 3)**.

XREF: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md:S0.1` — count **13** · `S0.2` — count **5** · `S4.1` — count **35** · `REALIZE` — count **17** · `WELL-DEF` — count **32**.

**TEETH:** JC5 (JC-ANCHMON, 855 samples), JC4 (JC-SCAL, 443), R1-SURJ (841) — all GREEN. **Annex #8 later re-scopes REALIZE's quantifier to `c ∈ K^*`**, noting the historical machine rows “retain their numerical counts but evidence only defined nonzero lifts”.

---

### EFF.GRTJC.s1of3.46  [scope record]  ★ THE STACK, ONE LINE — with its three-layer correction

**CANONICAL STATEMENT:** verbatim, lines 573–604.
**FORM:** bold display + two nested bracketed riders.

> “**THE STACK, ONE LINE.** Every clause of §§2–5 rides
> `[ILN]† ACCEPTED (scored stratum) + GRB/CARRY-1 ACCEPTED-conditional (§0 ladder) + FGMN (a)(b)~~(c)~~(d)(e) CITED + W-1/W-2/J-A/J-B ATTEMPT (0/2)`,
> **[r5, G-2 — (a)(b) ADDED to this display (PE4 GAP 1's second half, printed
> verbatim there and left unrepaired at r4; PE5 GAP 2). The note's live proofs
> consume **(IN-3)(a)** (w multiplicative: JC-DOM's proof twice; JC-LOC's
> G6-1/G6-3) and **(IN-3)(b)** (gr a domain + in(fg) = in(f)·in(g): JC-DOM,
> JC-LOC's proof, (MULT-B) and its |gr display) as CITED literature — the r4
> census itself certifies exactly these consumptions LIVE (§9.5 [r4, G-1],
> groups 2, 4, 6). Nothing false was concluded — the (IN-3) declaration block
> above carries (a)/(b) as CITED, and W-6's [r1] grade line reads
> "(IN-3)(a)(b)(e) + (IN-5) unchanged" — but the one-line summary displays
> understated the cited-literature footprint by two consumed clauses. §10.2's
> r0/[r1]/[r2] stack displays are round-records and carry the same completion
> by ANNOTATION, not edit: §10.2 [r5, G-2].]**
> **[r4, G-1 — (c) STRUCK from this display. This r0 one-liner was the
> PE1-refuted input's FOURTH alias, live here since r0 and outside every earlier
> sweep pattern (none of `(IN-3)`, `Thm 4.2`, `(COORD)`, `(MULT)` occurs on it).
> What is true, and what the current stacks (§10.2 [r1]/[r2], which supersede
> this display) **[r6, G-1 — 2026-08-08 campaign (wallclock 2026-08-06), per
> PE6 GAP 1: "current stacks" and "supersede this display" were both true at
> the r4 state (`edbb966`) and are inverted since r5 — §10.2's [r1]/[r2]
> displays are ROUND-RECORDS ([r5, G-2]), the current stack is §10.2
> [r5, G-2]'s completed form (FGMN (a)(b) + (DMULT-w) on B + Thm 4.8/Cor 4.9 +
> Cor 2.7), and this §0 display above carries the same completion IN PLACE and
> is itself live, superseded by nothing. The clause-(c) content this bracket
> goes on to state is unchanged and remains true.]** say: clause (c)'s content
> is consumed in this note ONLY as
> (DMULT-w) via JC-LOC, on B ≅ gr_{K[x]}(w) — never on gr_{O[x]} — with the
> (DMULT-w)/(DMULT-s) tier split of [r2, G-1]; clauses (d)(e) remain unchanged
> citations. Final census: §9.5 [r4, G-1].]**
> and this note's own arc starts at **0/2**. Nothing here may be consumed at proof
> grade before its hostile arc.”

**CHAIN (rule 25) — THREE layers on ONE display:** r0's one-liner → **r4/G-1** ((c) STRUCK; the fourth alias) → **r5/G-2** ((a)(b) ADDED) → **r6/G-1** (the pointer annotated: this display is LIVE and superseded by nothing). **TERMINAL: the display as it stands at HEAD, reading `[ILN]† ACCEPTED + GRB/CARRY-1 ACCEPTED-conditional + FGMN (a)(b)(d)(e) CITED [with (c) only via (DMULT-w) on B] + W-1/W-2/J-A/J-B ATTEMPT`.** `CHAIN-MEMBER: s1of3.43 (alias sweep), positions 4 and after.`

**★ THE POINTER INVERSION, and why it matters for a merge.** r4's bracket called §10.2's `[r1]`/`[r2]` stacks “the current stacks … which supersede this display”. r5 then declared those displays ROUND-RECORDS and completed §0's display **in place**. **So after r5 BOTH clauses were false: §10.2's are not current, and they do not supersede §0's — §0's is the live one.** r6 annotates rather than edits, per the arc's dated-annotation convention. **A merge run that follows the r4 pointer without the r6 annotation will read a round-record as the current stack.**

**CONDITIONALITY:** **STALE on two counts at HEAD.** (i) “W-1/W-2/J-A/J-B ATTEMPT (0/2)” — all three notes are now ACCEPTED (OPEN-CALL 3). (ii) “this note's own arc starts at 0/2. Nothing here may be consumed at proof grade before its hostile arc” — **EXPRESSLY superseded by Annex #7**, which names “every body-local prohibition on proof-grade consumption that is based solely on this note's former 0/2 counter”. **(iii) The FGMN entry itself is superseded by Annex #6's boxed form** (“(DMULT-w) derived above”).

**DERIVATION:** The stack is a conjunction of the five inputs' own grades.

**RESOLUTION TRACE:** statement lines 573–604; the five inputs 505–571 (`.41`–`.45`); §10.2's stacks 2687–2748 (shard 3); the dispositions 271–282 (r4/G-1), 247–255 (r5/G-2), 201–220 (r6/G-1); **Annexes #6 and #7 at 2917–3008 (shard 3)**.

**TEETH:** NONE (a conditionality display). Disposition: **AUDIT — in-house hostile pass** for the alias and pointer findings.

---

### EFF.GRTJC.s1of3.47  [definition]  §1 — the base setting

**CANONICAL STATEMENT:** verbatim, lines 610–612.
**FORM:** paragraph.

> “Fix a complete DVR O with uniformizer π and finite residue field, and a
> standard-lift tower T of the [ILN]† class with reads (e_j,h_j,g_j), j = 0..m,
> so NR := m+1 reads. Write E := e_0e_1⋯e_m (= E_{m+1} of the blueprint), and:”

**★ THE GENERALITY ANCHOR OF THE WHOLE NOTE, and Q7's headline finding.** Q7 (recorded not applied): *“‘Fix a complete DVR O with uniformizer π and finite residue field’ — **GENERAL FORMULATION.** The base object is not restricted to a finite extension of ℚ_p.”* **Every hazard Q7 checks against this note comes back BENIGN or GENERAL except the two FGMN cite-scope rows (`.43`), and both of those are resolved COVERS-ALL-O by NS-9/NS-10.**

**CONDITIONALITY:** `standard-lift only` — the `(ITER-LAW-LIFT)` residual rides (JC-BOX-6). `E > 1` is assumed throughout (JC-BOX-7).

**DERIVATION:** Definition.

**RESOLUTION TRACE:** statement lines 610–612; the boxes 2039–2056 (JC-BOX-6/7, shard 3).

**TEETH:** NONE (definition). The machine scope is `m ≤ 3, |K| ≤ 25, g_j ≤ 2, d_0 ≤ 3, orders ≤ 4, p ∈ {2,3,5}`, base rings ℤ_p **and F_p[[t]]** (JC-BOX-1, shard 3) — **equal-characteristic rows are IN the roster**.

---

### EFF.GRTJC.s1of3.48  [definition]  §1 — keys and weights

**CANONICAL STATEMENT:** verbatim, lines 614–619.
**FORM:** bulleted definitions.

> “* **keys** Φ_0 (monic, deg d_0, irreducible mod π), and Φ_{j+1} built by
>   REALIZE: Φ_{j+1} = Φ_j^{e_jg_j} + Σ_{k<g_j} C_kΦ_j^{e_jk} with
>   deg C_k < deg Φ_j. Hence **deg Φ_{j+1} = e_jg_j·deg Φ_j**.
> * **weights** γ_1 = h_0, wΦ_{j+1} = e_jg_jγ_{j+1}, γ_{j+1} = e_jwΦ_j + h_j;
>   the MacLane weight w_{j+1}(f) = min_a (e_j w_j(A_a) + aγ_{j+1}) over the
>   Φ_j-development f = Σ_a A_aΦ_j^a, and w_0 = the coefficientwise π-valuation.
>   **w := w_{m+1}** throughout; gr(w) := ⊕_{γ∈ℤ} P_γ/P_{γ+1}, P_γ := {w ≥ γ},
>   and in(f) := the class of f in gr_{w(f)}.”

**★ `w_0` IS THE COEFFICIENTWISE π-VALUATION ON `O[x]` — the single fact that made `(COORD)` false on `gr_{O[x]}`** (`.31`). §2.10's refutation runs: the ambient ring is `O[x]`, so `w_0 ≥ 0`, so every `Φ_m`-digit has `w_m(A_a) ≥ 0`, so an on-line abscissa at level `λ` satisfies `a·γ_{m+1} ≤ λ` — giving the finite slot bound. **The definition and the refutation are two lines apart in logical distance.**

**CONDITIONALITY:** Definitions. **`gr(w)` here is the `O[x]` object throughout §1**, which the r1 repair makes explicit and which JC-LOC then relates to `gr^K(w)`.

**DERIVATION:** Definitions; `deg Φ_{j+1} = e_jg_j·deg Φ_j` follows from the REALIZE form with `deg C_k < deg Φ_j`.

**RESOLUTION TRACE:** statement lines 614–619; the slot bound 1007–1022 (§2.10, shard 2); JC-LOC 1037–1062 (shard 2).

XREF: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md:REALIZE` — count **17**.

**TEETH:** JC1 keys `w(π) = E` on all 29 rows (2,594 samples).

---

### EFF.GRTJC.s1of3.49  [definition]  §1 — residues, split, anchors

**CANONICAL STATEMENT:** verbatim, lines 620–628.
**FORM:** bulleted definitions.

> “* **residues** K_0 = k_0[x]/(Φ̄_0), K_{j+1} = K_j[y]/(ψ_j) = K_j[z_{j+1}],
>   g_j = deg ψ_j; **z̄ := z_{m+1}**, K := K_{m+1}. Note ψ_j(0) ≠ 0 ⟹ z_{j+1} ≠ 0,
>   so every letter is a unit.
> * **split** γ ↦ (s_1..s_{NR}, u_1) by iterated eq-(12): s_{NR},u_{NR} = eq12(γ,e_m,h_m),
>   β_{j-1} = u_j − s_jwΦ_{j-1}, s_{j-1},u_{j-1} = eq12(β_{j-1},e_{j-2},h_{j-2});
>   s_{j+1} ∈ [0,e_j) always. **Window** W := {γ : u_1(γ) ≥ 0}.
> * **anchors** φ_γ := π^{u_1}∏_{j=0}^{m}Φ_j^{s_{j+1}} for γ ∈ W (Tower.tanch).”

**CONDITIONALITY:** **“every letter is a unit” rests on the class pin `ψ_j(0) ≠ 0`** and is used everywhere a letter is inverted. **The WINDOW `W := {γ : u_1(γ) ≥ 0}` is the standing restriction** — “outside, `gr_γ = 0` and no anchor exists” (JC-BOX-7) — and it is exactly what TC-1 removes (`in(π)` becomes a unit, so `B_j ≅ B_{j+E}` and “the window restriction disappears”, (COORD-B)(1)).

**GENERALITY NOTE (Q7, recorded not applied).** Q7: *“`w_0(π)=1` … `w(π)=e_0e_1⋯e_m=E` — **BENIGN.** This uses the chosen uniformizer `π`, not the integer prime `p`, and nowhere assumes `v(p)<∞`. **In `F_q[[t]]`, take `π=t`.**”* No edit; recorded.

**DERIVATION:** Definitions.

**RESOLUTION TRACE:** statement lines 620–628; the window's removal after TC-1 1177–1182 ((COORD-B)(1), shard 2); JC-BOX-7 2049–2056 (shard 3).

XREF: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md:S0.1` — count **13** (the class pin) · `S0.2` — count **5** (the split/anchor conventions).

**TEETH:** JC2 (the s-tuple map injective on E consecutive γ, 570 samples); JC5 (JC-ANCHMON, 855).

---

### EFF.GRTJC.s1of3.50  [definition]  ★ §1 — the level read and the digit polynomial

**CANONICAL STATEMENT:** verbatim, lines 629–639.
**FORM:** bulleted definition + display.

> “* **the level read** at line λ: develop f in Φ_m, keep the digits at abscissas
>   a ≡ s_{NR}(λ) (mod e_m) that lie ON the line (weight exactly λ), ε-correct
>   them, and pack them as read(λ,f) = Σ_j C_j z̄^{\,j}, **grid slot**
>   j := (a − s_{NR}(λ))/e_m. Define the **digit polynomial**
>
>       𝑅_λ(f) := Σ_j C_j y^{\,j} ∈ K_m[y]     (Tower.read_coeffs, packed in y)
>
>   so that **read(λ,f) = 𝑅_λ(f)(z̄) = 𝑅_λ(f) mod ψ_m** — a definitional identity
>   of the corpus's own read. By the definition of w as a min, **𝑅_λ(f) = 0 ⟺
>   w(f) > λ** (for f with w(f) ≥ λ); so 𝑅_λ is an injective K_m-linear map on
>   gr_λ.”

**★ THE OBJECT THE WHOLE NOTE TURNS ON.** `𝑅_λ` is the digit polynomial in `K_m[y]`; `read(λ,f)` is its evaluation at `z̄`. **The separation between the two is what makes TC-3 (the quotient by `ψ_m`) load-bearing rather than a relabeling** — JC-PSIKER's witness is exactly an element whose digit polynomial is `ψ_m(y) ≠ 0` while its read is `ψ_m(z̄) = 0`.

**CONDITIONALITY:** **Injectivity on `gr_λ` is DEFINITIONAL** (from `w` being a min) and is used throughout; **surjectivity onto `K_m[y]` is FALSE on `gr_λ`** (the slot bound) and is what JC-BSURJ has to prove for the colimit `B_n` instead. **The two halves have opposite provenances, and r1's CRITICAL 1 is precisely the confusion of the two.**

**DERIVATION:** Definition + a one-line consequence (`𝑅_λ(f) = 0 ⟺ w(f) > λ` by the min-definition of `w`).

**RESOLUTION TRACE:** statement lines 629–639; the injectivity used at (COORD-B)(1) 1177–1182 (shard 2); the surjectivity proved at JC-BSURJ 1145–1166 (shard 2); the witness 926–990 (JC-PSIKER, shard 2).

**TEETH:** **R1-INJ** — “§1's injectivity, both directions: `𝑅_λ(f) == 0 ⟺ w(f) > λ`”, 585 samples, 0 violations (shard 3).

---

### EFF.GRTJC.s1of3.51  [definition]  §1 — the scalar lift

**CANONICAL STATEMENT:** verbatim, lines 640–641.
**FORM:** bulleted definition.

> “* **the scalar lift** Λ_N(c) := realize(NR,c,N) for c ∈ K, N ≡ 0 (mod E) with
>   N ≥ wΦ_{NR}: by R2/R3, w(Λ_N(c)) = N and read(N,Λ_N(c)) = c. X_N := Λ_N(1).”

**★ CONDITIONALITY — SUPERSEDED BY ANNEX #8 (shard 3, L3014–3026).** The quantifier `c ∈ K` is **too wide** and the annex re-displays it:

> “**[ANNEX 2026-08-12 #8, post-acceptance correction — nonzero scalar lifts and zero coordinates.]** The scalar-lift definition and every JC-SCAL quantifier are re-displayed at their true proved-and-consumed scope:
> `Λ_N(c) := realize(NR,c,N)`, `c ∈ K^*`, `N ≡ 0 (mod E)`, `N ≥ wΦ_{NR}`.
> For these and only these targets, REALIZE R2/R3 give `w(Λ_N(c)) = N`, `read(N,Λ_N(c)) = c`.
> **No value `Λ_N(0)` is supplied by REALIZE. The zero polynomial represents the zero class and has zero read, but it does not have weight `N`.**”

**SUPERSESSION KIND:** `scope-pin` — a quantifier narrowed to the proved-and-consumed range. **TARGETS:** this unit, JC-SCAL (§2.6, shard 2), JC-BSURJ's zero-target wording, and the historical JC4/R1-SURJ machine rows (“their phrases ‘every c ∈ K’ are superseded by this annex”).

**★ THE CONSUMER SWEEP IS REASSURING AND THE ANNEX SAYS SO:** “JC-LOAD already quantifies `c ∈ K^*` and survives. W-8's `c_{m+1}` is a unit by JC-CARRY-m, so its lift remains defined. `X_N = Λ_N(1)` is unchanged. JC-SCAL, JC-BSURJ, COORD-B, and all downstream carrier-dimension arguments survive.” **r5/m-1 (`.15`) was the first symptom of exactly this defect, caught seven months of rounds earlier at one display.**

**DERIVATION:** Definition, with REALIZE R2/R3 supplying the two properties.

**RESOLUTION TRACE:** statement lines 640–641; **correction site 3014–3037 (Annex #8, shard 3)**; the first symptom 256–259 (`.15`); JC-SCAL 807–825 (shard 2).

XREF: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md:S4.1` — count **35** (REALIZE's laws).

**TEETH:** JC4 (443 samples: `Λ_N(c)`'s slot set == supp(c), `𝑅_N(X_N) == 1` exactly) and R1-SURJ (841). **Annex #8: their counts stand but “evidence only defined nonzero lifts and nonzero polynomial targets”.** Disposition: **executable regression with a post-hoc scope narrowing on what it evidences.**

---

### EFF.GRTJC.s1of3.52  [definition]  ★ §1 — the TC chain and 𝒜(T), with the r1/G2 correction

**CANONICAL STATEMENT:** verbatim, lines 642–654.
**FORM:** bulleted definition + a struck clause with its `[r1, G2]` replacement.

> “* **the TC chain** (blueprint S2.3): TC-1 localize gr(w) at in(π); TC-2 gauge
>   π ↦ 1 (the [F.0] weight gauge), collapsing ℤ → ℤ/E; TC-3 the residue quotient
>   Δ = K_m[y] ↠ K_m[y]/(ψ_m) = K_{m+1}. ~~**𝒜(T)** := the K-span of the anchor
>   classes in the degree-0 component of the TC-transported gr(w).~~ **[r1, G2 —
>   the "degree-0 component" reading is WRONG and is replaced; see FINDING JC-F2
>   (§5).]** **𝒜(T)** := the K-span of the anchor classes **[φ_{γ_ν}], ν ∈ ℤ/E,
>   ACROSS ALL ℤ/E-degrees** of the TC-transported ring 𝒜 = (gr(w)[in(π)^{-1}] /
>   (in(π)−1)) / image(in(Φ_{m+1})·gr(w)[in(π)^{-1}]) — equivalently (and now
>   PROVED, §2.10 [r1]) **𝒜(T) = 𝒜, the whole transported ring**, since each of
>   its E graded pieces 𝒜_ν is the K-line K·[φ_{γ_ν}]. The anchor class of γ sits
>   in 𝒜_{γ mod E}, which is the degree-0 component only for ν = 0, so the r0
>   wording contradicted this note's own degree-separation argument (§3.4) and
>   would have made W-7's Ψ map an E-dimensional carrier onto one K-line.”

**SUPERSESSION KIND:** `replacement` — a definition inherited from three upstream documents, refuted by the note's own proof.

**★ FINDING JC-F2 — a display defect INHERITED from the corpus, REVIEW-OWED at three sources.** §5 (shard 2, L1826–1842) states it: the corpus defines the carry-algebra target as “the K-span of the anchor classes **in the degree-0 component**” — **verbatim in `GRW2_TIE_DESIGN` §S2.2, the blueprint §S2.3, the GRTJC brief, and (until r1) §1 and W-7 of this note.** “**That reading is wrong, and it contradicts this note's own OB-4 proof**”: the anchor class of `γ` lives in degree `γ mod E`, which is degree 0 only for `ν = 0`; under the literal reading the degree-separation argument is unavailable and **Ψ would map an E-dimensional carrier onto a single K-line (false for `E > 1`)**. **r0 used the CORRECTED reading in its proofs while DISPLAYING the inherited one** — PE1's GAP 2. **REVIEW-OWED: the three upstream sources still carry the defective display.**

**CONDITIONALITY:** **“Nothing measured moves; no clause's proof changes.”** The correction is to the DISPLAY. **But the review obligation is live at HEAD** (JC-BOX-5's rider, shard 3): “it must be fixed in those sources before any downstream text repeats it.”

**DERIVATION:** The degree-separation argument (§3.4, shard 2): `[φ_{γ_ν}] ∈ 𝒜_ν` with `ν = γ_ν mod E` pairwise distinct (JC-FIB), so a relation splits degreewise; and each `𝒜_ν` is the K-line `K·[φ_{γ_ν}]`, so the span is the whole ring and `dim_K 𝒜(T) = E`.

**RESOLUTION TRACE:** statement lines 642–654; the disposition 387–390 (r1/G2, `.33`); FINDING JC-F2 1826–1842 (§5, shard 2); the box rider 2032–2038 (JC-BOX-5, shard 3); the proof 1552–1572 (§3.4, shard 2).

**GENERALITY NOTE (Q7, recorded not applied).** Q7 on the TC chain: *“‘TC-1 localize `gr(w)` at `in(π)`; TC-2 gauge `π↦1`’ — **BENIGN.** This is localization and quotient by a homogeneous unit associated to an arbitrary uniformizer. **It is not Witt-vector or unramified-ℤ_p structure.**”* And on the collapse: *“‘the grading collapses `ℤ→ℤ/E`’ — **BENIGN.** … There is no division by `E` in the coefficient field and no extraction of an `E`-th root.”* No edit; recorded.

**TEETH:** JC1/JC2 (periodicity and the fibred index); the dimension count is proved, not measured — **and JC8's unit half was VACUOUS as coded until r1's R1-UNIT replaced it** (`.33` G3).

---

### EFF.GRTJC.s1of3.53  [definition]  §1 — the harness cocycle `c_T`

**CANONICAL STATEMENT:** verbatim, lines 655–658.
**FORM:** bulleted definition.

> “* **the harness cocycle** c_T(γ,γ′) := z̄^{δ}∏_{j=1}^{m}z_j^{D_j} with δ, D_j the
>   [ILN]† recursion data; δ = (s_{NR}(γ)+s_{NR}(γ′) − s_{NR}(γ+γ′))/e_m.
>   **Since s_{NR} ∈ [0,e_m) on both arguments, δ ∈ {0,1} always** (used
>   constantly below).”

**★ `δ ∈ {0,1}` IS THE FACT THE WHOLE TC-3 ANALYSIS TURNS ON.** Because `δ ∈ {0,1}`, the load set `{δ ≥ g_m}` is `{δ = 1 ∧ g_m = 1}` — “a *geography*, not a growing set — it is empty on every `g_m ≥ 2` stage” (§3.2 consequence 3, shard 2).

**CONDITIONALITY:** `c_T` is `(IN-1)`'s closed form and is defined only on `[ILN]†`'s scored stratum. **§3.2's existence/structure theorem is strictly WIDER** (every window pair, DCX or not) — “with **zero machine support**, since the instrument's grid contained 0 DCX and 0 non-integral-D pairs” (JC-BOX-2).

**GENERALITY NOTE (Q7, recorded not applied).** Q7: *“‘`s_NR(γ+E)=s_NR(γ)`’ and ‘`u_1(γ+E)=u_1(γ)+1`’ — **BENIGN — integer congruence arithmetic.** It uses only divisibility among products of the integer ramification indices.”* No edit; recorded.

**DERIVATION:** Definition + a one-line bound: `s_{NR} ∈ [0, e_m)` on both arguments, so the numerator is in `(−e_m, 2e_m)` and the quotient is 0 or 1.

**RESOLUTION TRACE:** statement lines 655–658; the load-set consequence 1507–1508 (§3.2, shard 2); JC-LOAD 859–924 (shard 2); the off-stratum box 1946–1951 (shard 3).

**TEETH:** JC7 keys the integer carry identity `δ(r,s)+δ(r+s,t) = δ(s,t)+δ(r,s+t)` on 261 triples; MJ1 (the “TC-3 never load-bearing” tooth) fired 103 times, **all 103 in the `δ ≥ g_m` load set, 0 anomalies in either direction — JC-LOAD's dichotomy machine-confirmed both ways.**

---

## 3. Consumption tables

### 3.1 Verified import/XREF designations

`[TABLE — compiler ledger]` Counts are `grep -cF '<designation>' <file>` at HEAD. **28 distinct designations, all count ≥ 1.**

| # | Target : designation | Count | Role in this shard |
|---|---|---|---|
| 1 | `ITERLAWN_PROOF_2026-08-08.md:ITER-LAW-n` | 11 | `(IN-1)` = [ILN]†, the accepted closed form for `c_T` |
| 2 | `ITERLAWN_PROOF_2026-08-08.md:PC6` | 3 | one of the two clean passes closing [ILN]†'s arc |
| 3 | `ITERLAWN_PROOF_2026-08-08.md:PE7` | 3 | the other |
| 4 | `ITERLAWN_PROOF_2026-08-08.md:S0.1` | 13 | the class pin (`ψ_j(0) ≠ 0`, `gcd(e_j,h_j) = 1`, `g_j ≥ 1`) — every letter a unit |
| 5 | `ITERLAWN_PROOF_2026-08-08.md:S0.2` | 5 | the split/anchor conventions |
| 6 | `ITERLAWN_PROOF_2026-08-08.md:S4.1` | 35 | REALIZE-(m) with R1/R2/R3 |
| 7 | `ITERLAWN_PROOF_2026-08-08.md:REALIZE` | 17 | the key construction and the scalar lift |
| 8 | `ITERLAWN_PROOF_2026-08-08.md:WELL-DEF` | 32 | the standard-lift class |
| 9 | `ITERLAWN_PROOF_2026-08-08.md:DCX` | 115 | the excluded stratum; the instrument's census found **0 DCX pairs** |
| 10 | `GRB_ORDER2_2026-08-05.md:D-REAL` | 44 | `(IN-2)`'s last-read layer |
| 11 | `GRB_ORDER2_2026-08-05.md:CARRY-1` | 19 | `φ_γφ_{γ′} = φ_{γ+γ′}·ȳ^δ` at the last read — **no extra factor**, which is what §3.2 generalizes |
| 12 | `GRB_ORDER2_2026-08-05.md:(W-MULT)` | 8 | the last-read residual multiplicativity |
| 13 | `GRB_ORDER2_2026-08-05.md:S5.2` | 12 | the source section for D-REAL/CARRY-1 |
| 14 | `GRB_ORDER2_2026-08-05.md:S6a` | 8 | **the corpus's pinned FGMN quotation** — the provenance of `(IN-3)` |
| 15 | `GRB_ORDER2_2026-08-05.md:TR-3′-GEN` | 57 | **the OPEN harness↔literature read dictionary — why `(DMULT-s)` cannot be cited** |
| 16 | `GRB_ORDER2_2026-08-05.md:S3.4` | 25 | TR-3′-GEN's home section |
| 17 | `GRB_ORDER2_2026-08-05.md:(V1)` | 4 | GRB §0 ladder condition, inherited “forever” |
| 18 | `GRB_ORDER2_2026-08-05.md:(KP)` | 10 | GRB §0 ladder condition |
| 19 | `GRB_ORDER2_2026-08-05.md:(H-CHAIN)` | 35 | GRB §0 ladder condition |
| 20 | `GRTJB_PROOF_2026-08-08.md:JB-BOX-2` | 45 | **the inherited J-B geography — `(IN-4)`'s load-bearing clause** |
| 21 | `GRTJB_PROOF_2026-08-08.md:JB-CREAD` | 36 | the germ's supplier theorem |
| 22 | `GRTJB_PROOF_2026-08-08.md:JB-EPS` | 30 | the unconditional ε-collapse |
| 23 | `GRTJB_PROOF_2026-08-08.md:JB-BOX-4` | 2 | the `g_m = 1` fence for the `Ĉ_m` instance |
| 24 | `GRTW2_PROOF_2026-08-08.md:W2-C1` | 22 | W-2's admissibility, inherited through `(IN-4)` |
| 25 | `GRW2_TIE_DESIGN_2026-08-08.md` | file EXISTS | one of the three sources carrying the **JC-F2** defective display (REVIEW-OWED) |
| 26 | `DITERSUP_STMT_2026-08-08.md` | file EXISTS | the home of gate **J3b**, which this note displays the tie for and does NOT retire |
| 27 | `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md` | file EXISTS | §S2.3's TC chain and the second JC-F2 source |
| 28 | `docs/in-progress/GRTJC_BRIEF_2026-08-05.md` | file EXISTS | the brief whose germ hypothesis the instrument REFUTED; third JC-F2 source |

**LITERATURE PIN VERIFICATION (rule 23) — `docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt`, all lines re-read at HEAD.** **10 of 11 EXACT; one NEAR-MISS.** Full table at `.43`. Summary: **§1 setting @137 ✔ · Cor 2.7 @525 ✔ · Thm 2.8 @546 ✔ · §3.3 ψ_i def @862 ✔ · eq (14) @1004 ✔ · Thm 4.2 @1028 ✔ · rank-one clause @1030 ✔ · Cor 4.7 @1121 ✔ · Thm 4.8 @1136 ✔ · Lemma 5.13 @1403 ✔ · Cor 4.9 — note says @1153, actual @1151 (content EXACT).** **PDF md5 `da846c82f1fcb619cefb3feb8164191e` re-computed at HEAD: EXACT.**

**COMMIT VERIFICATION (rule 23): 23/23 resolve** (`git cat-file -t` → `commit`): `7212e56 fc89b03 6ad01d1 8f07904 1a27be3 6ed4680 85d5811 54904cc f45b63c 66263ce 4a76d52 5742e25 79611a4 db12666 e4b6fbf 126c33f d5072b6 edbb966 b38f3f4 3870bc8 66760f6 782000e 9d240b6`.

**md5 VERIFICATION: 2/2 EXACT** (`grt_jc_r1_checks.py`, `grt_jc_r2_checks.py`). **No md5 is pinned for `grt_jc_checks.py` or `grt_jc_probe.py`** — source defect 1.

**ARTIFACTS: 12/12 EXIST** in `verification/openmath/` (`grt_jc_probe.py`/`_output.txt`/`_results.json`; `grt_jc_checks.py`/`_output.txt`/`_results.json`; `grt_jc_r1_checks.py`/`grt_jc_r1_output.txt`/`grt_jc_r1_results.json`; `grt_jc_r2_checks.py`/`grt_jc_r2_output.txt`/`grt_jc_r2_results.json`).

**REPORT FILES: 6/6 EXIST** (`GRTJC_passPE1_report.md` … `GRTJC_passPE6_report.md`). **PE7 and PE8 are pinned by commit only** (`782000e`, `9d240b6`, both resolve) — source defect 2.

### 3.2 Reverse consumer edges: mathematical supply versus append protocol

`[TABLE — compiler ledger]`

| Consumer / supplier | Verified designation | Shard-1 supply | Mathematical status | Append/consumption-protocol status |
|---|---|---|---|---|
| **GRTJB (J-B)** | `JB-BOX-2` (45), `JB-CREAD` (36), `JB-EPS` (30), `JB-BOX-4` (2) | `.44` | **INBOUND**: GRTJC consumes J-B's germ and inherits JB-BOX-2's geography verbatim. **GRTJC then CONFIRMS the value law on 27 stages and REFUTES the brief's use of it (H-D, 138/669)** | **Not landed on GRTJB.** Neither side retires J3b; both say so |
| [ILN]† | `ITER-LAW-n` (11) | `.41`, `.45` | ACCEPTED with four named residuals riding | **Not landed** |
| GRB | `D-REAL` (44), `CARRY-1` (19), `TR-3′-GEN` (57) | `.42`, `.36` | ACCEPTED-WITH-CONDITIONS, “inherited here forever”. **TR-3′-GEN's OPEN status is what forces the (DMULT-w)/(DMULT-s) split** | **Not landed.** r3/G-6 CORRECTS this note's own gloss on TR-3′-GEN's record, at the source's wording |
| FGMN (literature) | layout/PDF line pins | `.43` | CITED; **numbering discharged post-acceptance at Annexes #2/#3**; **(DMULT-w) later DERIVED rather than cited (Annex #6)** | **Not landed.** NS-9/NS-10 retargets RECORDED, not applied |
| W-2 | `W2-C1` (22) | `.44` | ATTEMPT at write time; **ACCEPTED at HEAD** (unrecorded here — OPEN-CALL 3) | **Not landed** |
| **Downstream: DITERSUP gate J3b** | `DITERSUP_STMT_2026-08-08.md` (EXISTS) | `.02` | **Supplies exactly the missing item (ii)** — “the gr(w₂) semantics wrapper” — at attempt grade and at general `m`. **The gate does NOT retire** | **Not landed; the gate stands.** §10.3 (shard 3) states it twice |
| Downstream: `Scaffold/HDischarge/H1/DIterCarrier.lean` JS1/JS2 | — | `.02` | §5's W-9(i)(ii) is JS1's **semantic home** | **“No Lean hypothesis is discharged by this note”** (§10.3, shard 3) |
| Downstream: MOVES B2-DEF, the (H1)(a) GR-B carry side | — | `.02` | display/semantic home only | **Not landed;** “It does **not** discharge (H1)” |
| **THREE upstream docs carrying the JC-F2 defective display** | `GRW2_TIE_DESIGN`, the blueprint, the brief (all EXIST) | `.52` | **REVIEW-OWED at the source** — “it must be fixed in those sources before any downstream text repeats it” | **Not landed by this note**; the note owns the finding, not the fix |

**Zero dated consumption appends are claimed landed on any supplier by this note, and none is invented here.**

---

## 4. NON-IMPORTS

`[TABLE — compiler ledger]` Negative fences homed in lines 1–661.

| Fence | Explicit material NOT imported / NOT claimed | Unit |
|---|---|---|
| **No gate retires** | “no gate fires, **no gate retires**: DITERSUP §S3 gate J3b stays BLOCKED-ON-CARRIER-TIE (this note DISPLAYS the tie it would need, and **by construction cannot retire it**)” | `.02`, `.05`–`.10` |
| **No `.lean` touched** | “No `.lean` touched” — repeated in all six S-STATUS blocks | `.02`, `.05`–`.10` |
| **No density/menu/count statement** | “no density/menu/count statement is made anywhere” | `.02`, `.05`–`.10` |
| **The P0 application gate stands** | “the Asvin P0 application gate stands” | `.02` |
| **The brief's germ hypothesis is NOT proved** | “**This note proves the instrument's law, not the brief's guess**” — reading H-D FAILS on 138/669 pairs | `.03` |
| **`(IN-3)(c)` is NOT consumed on `gr_{O[x]}`** | “on THIS note's gr(w) — §1's O[x] object — the transported claim is REFUTED … This note consumes the clause **ONLY through JC-LOC**, as (DMULT-w) on B ≅ gr_{K[x]}(w) — **never on gr_{O[x]}**” | `.43`, `.31`, `.46` |
| **`(DMULT-s)` is NOT cited** | “the attempt to verify the exact form against the sources the note names **FAILED in a specific, reportable way** … **no corpus-pinned statement delivers multiplier 1**” | `.36` |
| **`(IN-2)` is NOT re-proved** | “**CONSUMED, NOT RE-PROVED.**” | `.42` |
| **Everything in §1 is definition** | “**Everything in §1 is definition, not claim.**” | `.45` |
| **No new battery at r3** | “the diversity fix is **DISCLOSURE, not a new battery**, per the effort directive” | `.21` |
| **The candidate diversity leg is NOT built** | “**Candidate repair leg, NAMED, NOT BUILT** (r3 is note-only per the effort directive)” | `.24` |
| **The census cannot certify by grep** | “**the census cannot certify the absence of further such lines by grep, and says so**” | `.20` |
| **No supplier upgrade** | “no clause is stronger than the weakest input it uses” | `.40` |
| **JC-F2's fix is NOT made here** | REVIEW-OWED at `GRW2_TIE_DESIGN`, the blueprint and the brief | `.52` |
| **`Λ_N(0)` is not supplied** | **From shard 3 (Annex #8):** “**No value `Λ_N(0)` is supplied by REALIZE.** The zero polynomial … does not have weight `N`.” | `.51` |

---

## 5. Teeth inverse table

`[TABLE — compiler ledger]` Vocabulary as in the GRTJB shards.

| Battery row / instrument leg | Guarded unit(s) | Disposition |
|---|---|---|
| **The instrument** (`grt_jc_probe.py`) — 29 towers, 669 scored pairs, 22 families GREEN, **all 29 rows EXHAUSTIVE with zero harness-side witness input** | `.03`, `.41`, `.53` | Executable regression **on a decorrelated determination**; per-pair uniqueness machine-proved. **The architectural property §3.5's tautology fence rests on** |
| **The instrument's refutation** — H-D fails 138/669; H-B 215; H-C 73 | `.03` | **Measurement, REFUTING the brief's germ hypothesis before the proof was written** |
| **r0 battery** (`grt_jc_checks.py`) — 10 families, 8,566 samples, 0 violations, 5 teeth (1,054 firings) | `.04` | Executable regression + planted mutants. **Headline reconstructs exactly from §9.2's table** |
| **JC3** — the note's own NEW sharp prediction, slot set == {δ} | `.53`; shard 2 §2.7 | Executable regression, **609/609 on `e_m ≥ 2` rows** |
| **JC8's unit half** | `.33` (G3) | **VACUOUS AS CODED** — “the sealed battery filters zeros before the predicate exists … the violation branch is unreachable and the skipped pairs were never censused”. `signed vacuity disclosure`; replaced by R1-UNIT + tooth T4 |
| **MJ1** — “TC-3 never load-bearing” | `.53`; shard 2 §2.8 | Planted mutant; **103 firings, ALL 103 in the `δ ≥ g_m` load set, 0 anomalies either way** — JC-LOAD's dichotomy machine-confirmed in both directions |
| **r1 battery** (`grt_jc_r1_checks.py`) — 10 families, 10,330 + TOOTH-ROW 145, 0 violations, 5 teeth (1,885 firings) | `.34` | Executable regression; **both headline figures reconstruct exactly** |
| **R1-BND** — `maxslot(G0) == 0` on 29/29 | `.31`, `.48` | **A refutation converted into a permanent scored regression** — the r0 `(COORD)` is refuted at the note's own base on every row |
| **T1** — the refuted r0 universal kernel claim | `.31`, `.32` | Planted mutant from a refuted claim; **29/29 firings** |
| **R1-INJ** — `𝑅_λ(f) == 0 ⟺ w(f) > λ`, both directions | `.50` | Executable regression, 585 samples |
| **R1-PER** — `𝑅_{λ+kE}(π^kf) == c_π^k·𝑅_λ(f)`, ρ exactly invariant | `.38` (G-3) | Executable regression, 841 samples; **`c_π ≠ 1` on 20 of 29 rows** — the ρ-normalization is load-bearing, not cosmetic |
| **R1-DMULT** — `(DMULT-s)` exact on sampled pairs | `.36` | Executable regression, 2,784/0 — **but monomial-dominated, with an undisclosed skip** (`.37`) |
| **R1-COB** — `u == a_γ·a_{γ′}` with slot set {δ} | `.28`, `.36` | Executable regression, 2,607 samples / 869 anchor pairs; **prereg row annotated post-tier-split with a TWO-MODE falsifier** |
| **R1-UNIT + T4** — the falsifiable replacement for JC8's vacuous half | `.33` | **869 unit / 0 zero / 0 undefined / 0 out-of-window**, with a planted zero caught on every row. **The cleanest vacuous-GREEN → falsifiable conversion in the corpus** |
| **R1-PSIK-LO / R1-PSIK-HI** | `.32` | Executable regression in both directions (197 lines below `wΦ_NR`; 197 residue classes with a certified witness), **with the certifier's one-sidedness disclosed** (JC-BOX-8(ii)) |
| **r2 battery** (`grt_jc_r2_checks.py`) — 4 families, 3,597 + TOOTH-ROW 58, 0 violations | `.39` | Executable regression; **both figures reconstruct exactly** |
| **R2-BIL** — `(DMULT-s)` on dense multi-slot × multi-slot pairs | `.37`, `.39` | Executable regression, 261 ordered pairs — **the bilinear content finally exercised**. **Resolution overstated until r3/G-3** (`.24`) |
| **R2-PHI** — the r1-skipped pair scored on 29/29 | `.37`, `.39` | Executable regression; **the skip cost nothing on 27 rows and cost the ONLY true bilinear pair on the two `g_m = 2` rows** |
| **R2-MONO** — the r1 sample composition SCORED, not asserted | `.37`, `.39` | **The disclosure-as-scored-fact pattern that became FREEZE PREDICATE 3** |
| **U2 — the cross-term drop** | `.37`, `.39` | **Planted mutant with a machine-proved resolution separation: 261/261 on dense pairs, 0 on r1-tested pairs.** “the r1 leg had zero resolution against the cross-term class” |
| **The alias/union censuses** (r3 → r4 → r5) | `.13`, `.17`, `.22`, `.23`, `.24` | **AUDIT — arithmetic recount**, each reproduced independently by the next pass (PE4 90 = 23/25/42; PE5 144 = 42/28/74; PE6 18/18 numbers) |
| **PE7 / PE8** (the clean passes) | shard 3's acceptance record | **accepted-with-decorrelation-supplied**: PE7 re-proved JC-GAUGE via coarsened grading + a fresh out-of-roster `p = 7` leg; PE8 re-proved W-8 + JC-LOAD's iff by a double-`(DMULT-w)` + ω-symmetry route with the **FIRST `g_m = 3` instances and an order-5 (m = 4, E = 8) tower, 885/0** |

**PROOF-ONLY rows (rule 16), with the note's own coverage-hole sentence:**
1. **`.41` / JC-BOX-2 — the off-stratum existence claim.** “the instrument's grid contained **0 DCX and 0 non-integral-D pairs**, so the wider half has **no machine support whatsoever** — it is proof-only, and a hostile pass should attack it there first.”
2. **`.33` G6 / JC-BOX-8(i) — the 606 skipped non-integral perturbations.** “they lie in the newly covered part of the statement and have **no machine leg**.”
3. **`.24` — the dense-set diversity on 13/29 rows.** The candidate repair leg is **NAMED, NOT BUILT**.
4. **`.52` — `dim_K 𝒜(T) = E`.** Proved, not measured; and JC8's unit half was vacuous until R1-UNIT.
5. **`.20` — the census's own completeness.** “the census cannot certify the absence of further such lines by grep, and says so.”

**AUDIT rows (rule 27):**

| finding | class | the “no tooth applies” ground |
|---|---|---|
| `.31` r1/F1 | in-house hostile pass | an object identification — no battery keys which ring a theorem is about |
| `.32` r1/F2 | in-house hostile pass | a quantifier — the witness was correct and measured; the generalization was not |
| `.33` G3 | in-house hostile pass | “the violation branch is unreachable” — a battery cannot report its own unreachability |
| `.36` r2/G-1 | transfer audit | a failed citation search, reported as a finding |
| `.37` r2/G-2 | in-house hostile pass → **converted to a scored fact** (R2-MONO) | a code audit of a byte-frozen runner |
| `.22`/`.17`/`.13` | arithmetic recount | three census recounts, each reproduced by the next pass |
| `.24` r3/G-3 | in-house hostile pass | a diversity claim refuted by reading the frozen builder's code |
| `.25` r3/G-4 | arithmetic recount | a false divisibility under a true measured fact |
| `.27` r3/G-6 | transfer audit | a supplier's record quoted against the consumer's gloss |
| `.29` r3/G-8 | measurement, refuting | a false trigger refuted by the note's own C2C/C3I rows |
| `.11` r6/G-1 | in-house hostile pass | a pointer inversion created by the previous round |
| `.43` (Q7 H6) | **decorrelated-model audit** | “the pasted quotation does not include the paper's standing assumptions on `K` and `µ`” |

**Both-direction audit.** Every leg guards at least one unit; every unit whose `TEETH` field names a leg appears. Units with **`TEETH: NONE`** — `.02`, `.18`, `.26`, `.40`, `.46`, `.47` — are declarations, records or conditionality displays. **Zero battery-row orphans; zero toothed-unit orphans; five signed PROOF-ONLY units; twelve AUDIT findings.**

---

## 6. BOUNDARY SELF-AUDIT (prose genre, rule 9)

GRTJC carries **zero `\tag{`** in its own prose (the two in the file are LaTeX equation tags inside shard 3's transcribed annexes). **This shard's structure is: a header block, a six-member status series, six reverse-chronological round blocks, a five-input conditionality section, and a bulleted definition section.** Boundaries were chosen; the five arguable calls are recorded.

### 6.0 The rule applied

> **A unit is the smallest span carrying one complete claim together with its proof obligations.**

Same four-part test as the GRTJB shards. **Two genre-specific additions:**
- **A REPAIR-ROUND DISPOSITION is a unit iff it moves an input's status, an object, a quantifier, a fence or an evidence class**; otherwise it merges into its round's assembled unit. (Same criterion as GRTJB, applied here to six rounds.)
- **§1's definitions are units even though `(IN-5)` declares “Everything in §1 is definition, not claim”** — because each is cited by name from §§2–5 and several carry corrections (`.51` from Annex #8, `.52` from r1/G2).

### 6.1 Boundaries drawn, with the arguable ones recorded both ways

**1. The six S-STATUS blocks as a SERIES (`.05`–`.10`).** Rule 28. *Candidate A:* one status unit quoting the live `[r6]` block. *Candidate B (chosen):* six, with an explicit ledger. **Reason beyond GRTJB's:** GRTJC uses **two different retention devices** — `[r1]` struck, `[r2]`–`[r6]` annotated-not-struck — and the distinction is load-bearing (**an annotated block is not live text**). A merge run must be able to see which is which. *Cost:* six near-identical units; mitigated by tabulating and quoting only the TERMINAL member's `ARC:` display.

**2. Round blocks in REVERSE CHRONOLOGICAL source order, emitted in SOURCE order (`.11`–`.39`).** **Genuinely arguable, and the compiler chose against chronology.** *Candidate A:* emit in time order (r1, r2, r3, r4, r5, r6) so the CHAIN fields read forwards. *Candidate B (chosen):* emit in SOURCE order (r6, r5, r4, r3, r1, r2), because **RESOLUTION TRACE line ranges must increase monotonically for a merge run to locate them**, and because the shard's job is to compile the text as laid out. **Mitigation: the reading hazard is flagged twice — in the header's governing-text rule (iii) and here — and every CHAIN field gives its members in TIME order regardless of unit order.** *Honest cost:* a reader going unit by unit meets r6's repair before the r1 defect it descends from.

**3. `.31` and `.32` (the two CRITICALs) as separate units, with r1's eight gaps assembled at `.33`.** The stated criterion. **Not arguable** — F1 moves an object and F2 a quantifier, while G1–G8 are interface/label/census corrections. *But note:* **G3 and G6 are evidence downgrades of real weight**, and a case could be made for pulling them out. *Chosen:* keep them in `.33` with a per-item ledger and a highlighted note, because neither carries its own supersession history.

**4. `.43` ((IN-3)) as ONE unit carrying five clauses, the CITE-SCOPE row AND the chain home.** **The shard's most consequential merge decision.** *Candidate A:* five units, one per clause — each is cited independently and clause (c) alone has a five-layer history. *Candidate B (chosen):* one. **Reasons:** (i) the note declares them as one package with one provenance (“the corpus's pinned quotation”); (ii) the alias-sweep saga is about the PACKAGE's names, not about individual clauses; (iii) the `(IN-3)(c)` chain's members live in five different rounds and two annexes, so the chain needs ONE declared home and this is it. *Cost:* the longest unit in the shard. **Mitigation and merge recommendation: give `.43` per-clause sub-IDs (`.43/a` … `.43/e`), since (a)/(b), (c), and (d)/(e) have three different statuses at HEAD.**

**5. `.46` (THE STACK, ONE LINE) as its own unit rather than folded into `.43`.** Test 2 and 3: it is cited as “§0's live one-liner” from three later rounds, and it carries a three-layer correction chain of its own including the pointer inversion. *Not arguable* once the r6 finding is seen.

**6. §1 split into seven units (`.47`–`.53`) rather than one “objects” unit.** Test 2: `𝑅_λ`, `Λ_N`, `𝒜(T)`, `c_T`, the window `W`, the anchors and the split are each cited by name dozens of times in §§2–5. Test 3: `.51` is superseded by Annex #8 and `.52` by r1/G2, while `.47`–`.50` and `.53` are not. *Not arguable.*

**7. `.52` (the TC chain + 𝒜(T)) kept as one unit though the TC chain and `𝒜(T)` are separable.** **Arguable.** *Candidate A:* two units — the three-step TC chain is a construction, `𝒜(T)` is a definition with a refuted predecessor. *Candidate B (chosen):* one, because **the corrected `𝒜(T)` definition is stated in terms of the TC-transported ring**, i.e. in terms of the chain, and the JC-F2 finding is about exactly that relationship (“the degree-0 component **of** the TC-transported gr(w)”). *Cost:* a long unit; mitigated by the finding being separately homed at §5 (shard 2).

**8. `.03` (the instrument) as its own unit, separate from `.04` (the own battery).** Test 4, decisively: **opposite epistemic roles.** `.03` is a consumed, decorrelated determination whose refutation the note honors; `.04` is the note's own test of its own clauses. **Folding them would blur exactly the separation §3.5's tautology fence depends on.**

### 6.2 Merges deliberately NOT made

- **The five `(IN-k)` inputs** are five units, not one §0 unit: each has a different grade, different residuals and a different correction history.
- **`.36`'s two tiers** stay inside one unit: the split IS the disposition, and the two tiers are defined by contrast.
- **`.24`'s species history** stays inside the G-3 unit rather than becoming a “species” unit: it is a record of three instances already homed at `.13`, `.17`, `.22`/`.23`.
- **The six round headers** are not merged with their dispositions: each header carries a distinct independent-verification record (what that pass re-derived and reproduced), which is the round's own evidence.

### 6.3 Which template rules fought this note's genre

1. **★ Rule 12's three-slot RESOLUTION TRACE is not enough when the SOURCE ORDER is reversed.** In lines 187–496 the round blocks run r6 → r1 → r2, so a trace's “statement lines” are anti-correlated with chronology. **Fix: add a `SOURCE-ORDER NOTE` field, or require the shard header to declare when line order ≠ time order.** This shard declares it twice; it should be a rule.
2. **A retention device other than the strike needs its own vocabulary.** GRTJC's “kept annotated rather than struck because of the embedded ARC display” is a THIRD state between live and struck, and a merge run that treats annotated blocks as live will read five superseded status lines as current. **Fix: a `RETENTION: live | struck | annotated-superseded` sub-field on any unit quoting a status or stack display.**
3. **(Confirming both GRTJB shards.) `partial-withdrawal` is needed, and GRTJC needs it three times** — Annexes #4 (W-8's route redone, conclusion unchanged), #5 (W-6(iv) re-displayed with a load-set qualifier) and #8 (`Λ_N`'s quantifier narrowed with a replacement display). **Three more instances; the enum gap is now confirmed from four independent directions.**
4. **★ Rule 27's AUDIT class needs a `bred-defect` companion, and GRTJC is the strongest evidence yet.** This note has **four** rounds whose findings were created by the previous round: r5/G-1 (inside the block written to end the species), r6/G-1 (created by r5's re-classification), r3/G-3 (the r2 dense leg's own collapse), and r2/G-2 (the r1 leg's undisclosed skip). **The pattern is not incidental — it is what a long repair arc DOES, and a spec that cannot name it loses the corpus's most transferable lesson.**
5. **Rule 22's arithmetic audit is where this note SHINES, and the contrast with GRTJB is instructive.** **Every headline figure in GRTJC reconstructs exactly from its own table** (8,566; 1,054; 10,330; 10,475; 1,885; 3,597; 3,655; 144 = 42/28/74; 90 = 23/25/42), whereas GRTJB's §7.1 headline 6,700 does not. **The difference is FREEZE PREDICATE 3** — GRTJC was forced, by three census failures, into a standing rule that every figure come from a grep with its unit and commit. **Recommend the merge record that as a corpus-level lesson.**

---

## 7. SHARD NOTES

- **Cross-shard supersessions applied (four inbound to this range, all from shard 3's annexes).**
  (1) **Annex #7** → `.02`, `.05`–`.10`, `.46`. **EXPRESS status supersession**, naming `[r6] S-STATUS (CURRENT)`, §10.1's counter, every “JC-PE7 next”, and every proof-grade prohibition based on the 0/2 counter. **Tag `superseded`, not STALE.**
  (2) **Annex #1** → `.36`. `(DMULT-s)` becomes **PROVED-conditional** on the measured perimeter (DULEMMA THEOREM DU), with `e_m = 1` and off-stratum pairs still open.
  (3) **Annex #6** → `.36`, `.43`. The claim that `(DMULT-w)` is a quoted FGMN product identity is **WITHDRAWN**; it is **DERIVED** via LEMMA JC-RANKMULT from the PDF-verified rank-one theorem. **TERMINAL of the `(IN-3)(c)` chain.**
  (4) **Annex #8** → `.51`. `Λ_N`'s quantifier narrowed to `c ∈ K^*`; the zero-target wording repaired at JC-BSURJ too.
  **Also inbound:** **Annexes #2/#3** discharge `.43`'s citation-precision flag (first at the text extraction, then — under the extraction-decorrelation rule — at the PDF).
- **Range-edge audit.** Head: line 1 is the H1 title. Tail: L658 closes §1's last bullet, L659 blank, L660 `---`, L661 blank, L662 `## §2.`. **No source statement unit is cut at either edge**; the tail boundary is the manifest's own and falls on a section break.
- **Outside-HOME material used only as resolver:** §§2–7's theorem chain (shard 2); §§8–10's boxes, machine bracket, grade box, stack and consumers, the acceptance record, and Annexes #1–#8 (shard 3).
- **Protocol versus supply.** §0 and §1 are inputs and definitions; the supply is shard 2. **No consumption append is claimed landed on any supplier, and none is invented.**
- **Numbering.** Temporary IDs `EFF.GRTJC.s1of3.01`–`.53`, to be reconciled at the merge run.
- **MERGE HAZARDS TO FLAG (six).**
  1. **`.43` needs per-clause sub-IDs** (`.43/a`…`.43/e`): (a)/(b) are live citations added late; (c) is refuted-as-transported and now DERIVED; (d)/(e) are unchanged and PDF-verified. **Three different statuses under one ID.**
  2. **The `(IN-3)(c)` chain spans five layers and two shards, HOME at `.43`.** The merge must install `.31`, `.36`, `.46` → `.43` as CHAIN-MEMBER edges and mark **Annex #6 TERMINAL**.
  3. **Line order ≠ time order in `.11`–`.39`.** Any merge that sorts by source line will reverse the repair chronology.
  4. **Five S-STATUS blocks are ANNOTATED, not struck.** A live-text extractor will pick them up as current.
  5. **`.44`'s supplier grades are STALE and NOTHING in GRTJC records the upgrade** — W-2, J-A and J-B are all ACCEPTED at HEAD. **And GRTJB's own post-acceptance E-3/E-4 corrections cannot be known to this note.** See OPEN-CALL 3.
  6. **`.52`'s JC-F2 is REVIEW-OWED at three upstream documents** that still carry the defective “degree-0 component” display. The merge should carry that obligation forward explicitly.

---

## 8. Self-audit and OPEN-CALLS

### OPEN-CALL 1 — the manifest shards GRTJC into FOUR ranges; the charge names THREE

Recorded in the header. **Resolution applied: manifest rows 49+50 merged into shard 3**, so the annex tail stays with the sections it supersedes. **No line is dropped and none is compiled twice.** **Note the deliberate contrast with GRTJB, where the merge fell at the FRONT.** **Decision needed: whether the merge run treats these notes as 3-shard or 4-shard in its ID scheme** — if 4-shard, GRTJC's shard 3 splits at L2802 and the annexes get their own IDs. Nothing mathematical turns on it; no silent choice was made.

### OPEN-CALL 2 — the CITE-SCOPE flag was Q7's ONLY substantive generality finding against this note, and it is a pasting artefact

`.43` records Q7's H6 flags — the FGMN rank-one and abscissa-additivity quotations “do not include the paper's standing assumptions on `K` and `µ`”, which Q7 calls *“the only potentially mixed-characteristic-sensitive citation gap I found”*. **`CITE_SCOPE_RESOLUTION` NS-10 diagnoses it precisely: “The audit's flag was a pasting artefact, not a real gap … No edit to the mathematics is needed — only re-paste the §1 setting sentence next to the quote.”** **This compiler verified FGMN's §1 setting at layout line 137: “Let K be a field equipped with a discrete valuation v : K∗ −→ Z” — the general setting, no completeness, no residue-field hypothesis.** **Decision needed: whether the fix (pasting FGMN §1's setting sentence beside the `(IN-3)` quotations) lands as a dated annex on GRTJC, or in a corpus-level cite table the chapter blueprints read.** The compiler recorded the resolution and refused to choose. **This is the single cheapest generality repair in the whole weld corpus: one sentence, no mathematics.**

### OPEN-CALL 3 — GRTJC's supplier grades are stale, and it cannot know about GRTJB's post-acceptance corrections

`.44` and `.46` state “W-2 / J-A / J-B, ATTEMPT GRADE (counter 0/2)”. **At HEAD all three are ACCEPTED at 2/2** (GRTW2 `adc6cf3`, GRTJA `17d2a32`, GRTJB via PE9/PE10). **GRTJB recorded its own suppliers' upgrades in a dated annex; GRTJC has no equivalent.** **Worse for the DAG: GRTJB has since received TWO post-acceptance corrections to displayed mathematics (E-3, the shear's non-unimodularity; E-4, the off-perimeter negation withdrawn), and GRTJC's `(IN-4)` inherits “JB-BOX-2's conditionality … verbatim” without any pointer to them.** Neither correction touches JB-BOX-2's perimeter enumeration (E-4 explicitly: “JB-BOX-2's perimeter enumeration survives verbatim”), **so the inheritance is almost certainly unaffected** — but nothing in GRTJC says so. **Decision needed: whether GRTJC owes a supplier-grade annex, and whether the E-3/E-4 corrections need an explicit no-impact note on the `(IN-4)` inheritance.** The compiler flagged both and asserted neither.

### OPEN-CALL 4 — the alias census's completeness rests, at the last step, on a read-through rather than a fixed point

`.20` records the disclosed protocol limit verbatim: the census counts hit-LINES by NAME; a content line whose tag sits on an adjacent line is outside its resolution; **“the census cannot certify the absence of further such lines by grep, and says so.”** The limit was discharged “by a read-through of §0's input block, **the only place the package's clauses are DISPLAYED as propositions rather than consumed by name**”. **That argument is good but it is an argument, not a fixed point** — it depends on the claim that §0 is the only such place, which is itself a read-through result. **Decision needed: whether the blueprint phase wants a structural check** (e.g. a grep for display-block openers not followed by a swept name within N lines) **or accepts the read-through.** Recorded because the alias saga cost four rounds and its closure is the one step not mechanised.

### OPEN-CALL 5 — three upstream documents still carry the JC-F2 defective display

`.52` records FINDING JC-F2: the “degree-0 component” definition of `𝒜(T)` is **wrong**, contradicts this note's own OB-4 proof, and **would make Ψ map an E-dimensional carrier onto a single K-line**. It is carried verbatim in **`GRW2_TIE_DESIGN` §S2.2, the GRT weld blueprint §S2.3, and the GRTJC brief** — all three verified to EXIST at HEAD. **JC-BOX-5's rider: “it must be fixed in those sources before any downstream text repeats it.”** **Decision needed: whether the fix is dispatched now** (three one-line display corrections) **or carried as a standing REVIEW-OWED row into the blueprint phase.** The risk is concrete: the blueprint is one of the three sources, and the chapter blueprints are about to be written from it.

### Recorded source defects (flagged, not silently repaired)

1. **`.03`, `.04`:** neither the instrument (`grt_jc_probe.py`) nor the r0 battery (`grt_jc_checks.py`) carries an md5 pin in the note, although the r1 and r2 runners do (**both re-verified EXACT at HEAD**). The r0 freeze is asserted (“stay BYTE-FROZEN”) and was verified by PE1/PE2 re-runs, but there is no in-note hash to check against.
2. **`.05`–`.10`:** PE7 and PE8 are pinned by commit (`782000e`, `9d240b6`, both resolve) but **no report filenames are given**, unlike PE1–PE6 which all have `GRTJC_passPE<k>_report.md` files present on disk. **Same defect as GRTJB's PE9/PE10.**
3. **`.43`:** Annex #2's line pin for **Corollary 4.9 is off by two** — the note says layout line **1153**; the corollary is at line **1151** (line 1153 reads “κ(µ)alg ≃ Fr and the next result follows.”). **The CONTENT is EXACT at 1151** and matches the note's gloss word for word. **10 of 11 pins exact.** A line-number slip in a fold that was itself a numbering-verification exercise.
4. **`.11`–`.39`:** the round blocks appear in **reverse chronological order**, which no header sentence of the note itself flags. The `ARC:` displays are the chronology. **Recorded as a reading hazard, not an error.**
5. **`.13`:** the four cited line numbers (L383, L401, L1801, L1782) are given “at `edbb966`”, a historical commit. **Not re-verified at that commit by this compiler** — recorded as a checkable pin.
6. **`.46`:** the r4 bracket's pointer (“the current stacks (§10.2 [r1]/[r2], which supersede this display)”) was **inverted by r5 and is corrected only by an r6 ANNOTATION inside it**. A reader who stops at the r4 bracket gets the wrong stack. The note chose annotation over edit per its own convention; **the hazard is real and is flagged at merge hazard 4.**

### Fidelity audit

- Every CANONICAL STATEMENT is a verbatim source quotation or explicitly `[ASSEMBLED]`. **No inverse, sign, quantifier, index, level, inequality direction, or implication direction was altered anywhere.** Truncations are marked `…` and are used in `.05`–`.10` (the six ARC recitals, tabulated instead), `.11`, `.30`, `.33`, `.38`.
- **Strike markup is preserved**, and the note's THIRD retention state (annotated-not-struck) is recorded explicitly at `.05`–`.10` with the note's own reason quoted.
- **The TERMINAL `ARC:` display is DOUBLE-EMITTED** (rule 14) — verbatim, then as a compiler `[TABLE]` over the whole series with an arithmetic audit. **`(IN-3)`'s five clauses are likewise double-emitted** with a status column.
- **MANDATORY ARITHMETIC AUDITS performed on eleven count surfaces** (`.03`, `.04`, `.05`–`.10`, `.12`, `.13`, `.16`, `.23`, `.24`, `.25`, `.34`, `.37`, `.39`). **Every one is internally consistent.** **Notably, every headline figure in this note reconstructs exactly from its own table** — 8,566; 1,054; 10,330 + 145 = 10,475; 1,885; 3,597 + 58 = 3,655; 144 = 42/28/74; 90 = 23/25/42 — **which is FREEZE PREDICATE 3 paying off, and is the sharpest contrast with GRTJB's §7.1.**
- **28 external XREF designations, every one grep-verified with a count ≥ 1 recorded inline and in §3.1** (four of them are file-existence pins for documents cited by path).
- **PIN VERIFICATION: 23/23 commits resolve; 2/2 md5s EXACT; 12/12 artifacts exist; 6/6 PE1–PE6 reports exist; the FGMN PDF md5 EXACT; 10 of 11 FGMN layout line pins EXACT with the eleventh a verified off-by-two.** Three items recorded as checkable-but-unverified (the r0/instrument freeze without a hash, PE7/PE8 report filenames, the `edbb966`-era line numbers).
- **CITE-SCOPE handled per resolution rule 8:** the Q7 H6 flags and the NS-9/NS-10 resolutions are recorded IN FULL at `.43`, with FGMN's §1 standing setting re-read at layout line 137 by this compiler and quoted. **Recorded, not applied.** **The `(IN-4)` inheritance of GRTJB's own H6 row (NS-11) is recorded at `.44`.**
- **Q7 GENERALITY NOTES recorded, not applied, at six units** (`.41`, `.42`, `.45`, `.47`, `.49`, `.52`, `.53`) — every one a **GENERAL** or **BENIGN** classification, quoted verbatim. **Q7's verdict on this note is CITE-SCOPE, and the two cite rows are the whole of it.**
- Status and mathematical content are kept as distinct predicates: the status series is `superseded` (expressly, by Annex #7), the input grades are stale-and-unrecorded (OPEN-CALL 3), and the mathematics is shard 2's.
- **One XREF count asserted in an earlier draft of `.44` was WRONG and was corrected against the file before commit** (`JB-BOX-2` in GRTJB is **45**, not 17) — recorded because the fidelity rule is that counts come from the grep, never from memory.
- **Honest limitation of this shard:** every clause these inputs condition lives in shard 2, and all five annex corrections live in shard 3. Every affected unit quotes the governing corrective text verbatim, so shard 1 is self-contained as a *reading*, but the merge run must install the six edges listed in §7.

EFF-GRTJC-s1of3 COMPILED: 53 statements / 28 xrefs verified / 5 open calls
