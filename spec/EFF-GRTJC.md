# EFF-GRTJC — CANONICAL EFFECTIVE-SPECIFICATION (MERGED)

**COMPILED-BY: sonnet (2026-08-14, Asvin-authorized PHASE-0a sweep, the campaign's final two
merges) — mixed provenance carried forward from all three shards (each independently
stamped `opus, 2026-08-14, PROJECT_STATE #51`). CODEX CROSS-READ OWED (post-reset) — none
of the three shards, and no fold performed by this merge run, has been through an
adversarial pass; that obligation is inherited whole. This merge follows the
EFF-HE7/EFF-GENIND/EFF-GRTJB established pattern for tag-sparse three-shard prose notes.**

## 1. Merge header

**Source note:** `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md` (3059 lines, 217,445 bytes).

**HEAD blob hash:** `b07f08f52c1cf2d84af7e8167b8daf2f791a4f8c` — cited identically by all
three source shards' headers (each also recording the file's last-touching commit as
`e2403a2b`, "SOL cert E4 FOLDED: GRTJC"), and independently confirmed by fresh
`git hash-object` against the working-tree file at merge time (2026-08-14):

```
$ git hash-object lean/notes/openmath/GRTJC_PROOF_2026-08-08.md
b07f08f52c1cf2d84af7e8167b8daf2f791a4f8c
```

**No divergence found — this was the merge run's STOP condition and it did not trigger.**

**Compilation context:** `spec/EFF_TEMPLATE_v2.md` at HEAD (v2 rules 1–10; v3 rules 11–28).

**Merged from:** `spec/EFF-GRTJC-s1of3.md` (HOME lines 1–661; 53 statements, 28 xrefs,
5 open calls), `spec/EFF-GRTJC-s2of3.md` (HOME lines 662–1937; 43 statements, 19 xrefs,
5 open calls), `spec/EFF-GRTJC-s3of3.md` (HOME lines 1938–3059; 36 statements, 14 xrefs,
5 open calls). **132 statements, 61 raw XREF citations, 15 raw open calls total before
merge-time dedup.** This file supersedes the three shards as the citable unit for all
downstream consumption; any consumer citing `EFF.GRTJC.*` cites the contiguous IDs below,
not the shard-local `EFF.GRTJC.sKof3.*` IDs. The three shard files are **not deleted** —
they remain the run-of-record trace, including each unit's own §6 BOUNDARY SELF-AUDIT
entry; this file's §6 carries forward only the format-level SERIES/CHAIN conclusions and
the consolidated edge list.

### The rows-49+50 boundary OPEN-CALL (carried forward, not resolved by this merge)

`runs/qgen/sweep_manifest.txt` shards GRTJC into **FOUR** ranges (1–661, 662–1937,
1938–2802, 2803–3059); the compilation charge names **THREE**. Shard 1's own header
records the resolution applied: **manifest rows 49+50 were MERGED into shard 3**
(2803–3059 is the appended-annex tail, whose whole content supersedes statements homed in
1938–2802 and in §§2–7; splitting it from §§8–10 would put an annex and its target in
different files with no unit able to carry the edge). Union = 1–3059, no line compiled
twice, none dropped; both merge boundaries verified at source-line section breaks
(L1936/1937/1938, and the manifest's own internal L2802/2803 split, now interior to
shard 3). **This is the load-bearing CONTRAST with the companion GRTJB merge**: GRTJB's
own excess range merged at the **front** (rows 43+44 into shard 1); GRTJC's merged at the
**back** (rows 49+50 into shard 3) — shard 1 flags this explicitly ("Note the deliberate
contrast with GRTJB, where the merge fell at the FRONT") and leaves open **whether a merge
run should treat these notes as 3-shard or 4-shard in its ID scheme** — carried below as
OPEN-CALL 1, unresolved, nothing mathematical riding on the choice either way.

### SHARD-MAP (old shard-local ID → new contiguous ID)

Shard 1's offset is **0** (01–53, already contiguous from 1). Shard 2 carries a **+53**
offset (01–43 → 54–96). Shard 3 carries a **+96** offset (01–36 → 97–132). The rewrite
used the same context-tracking script and disambiguation rule as the companion GRTJB
merge (§1 there), extended with an **EXTERNAL-NOTE GUARD**: GRTJC's own shards cite GRTJB's
shard files by path five times (e.g. "`spec/EFF-GRTJB-s2of3.md` `.54`", the J-B ↔ J-C
interface germ) — such bare refs name a unit in a **different note entirely** and were
left byte-unchanged rather than renumbered under GRTJC's own offsets; verified by grep
that all five such external citations survive the merge with their original GRTJB
shard-local numbers intact (§7's fidelity audit).

Two "range" headings resolve as combined single blocks (no separate sub-heading per
member): `s1of3.05 — .10` (the six-member `S-STATUS` SERIES) and `s3of3.01 — .08` (the
eight honest boxes). A third, `s3of3.26 — .37`, is a **zero-width SERIES OVERVIEW**
exactly as the source itself states: **"Unit IDs `.26`–`.36`; the series header occupies
no ID of its own"** — the heading's own declared endpoint (`.37`, "ten dated members")
over-states by one against its actual eleven-row table (26 through 36); the overview text
was folded as a preamble onto unit `.26`, matching the note's own explicit rule.

The rewrite was performed **mechanically** and then audited: **zero leftover `sKof3`
substrings anywhere in the merged statement inventory (§3)**, **zero out-of-range
renumbered IDs** (every resolved ID lies in 1–132), and the ID sequence covers 1..132
exactly once with no gap and no duplicate (script-verified).

| shard | local range | offset | merged range |
|---|---|---|---|
| s1of3 | 01–53 | +0 | 01–53 |
| s2of3 | 01–43 | +53 | 54–96 |
| s3of3 | 01–36 | +96 | 97–132 |

### Header unification and blob-hash check

All three shards' front matter carries the identical compiled-by/cross-read-owed stamp
and the identical HEAD blob hash; re-verified against the working tree rather than
trusting the shards' mutual citation alone.

### Governing effective-text record (unified; the note's own status-handling is the
sharpest methodological contrast with the companion GRTJB note)

The base body (§§0–7, the four weld faces W-6..W-9, the eight honest boxes, the machine
bracket) is frozen after six repair rounds; the acceptance record (2026-08-06, PE7/PE8
CLEAN) and eight numbered Annexes (#1–#8, the last five from the 2026-08-12 sol
certification) are dated appends, read as correcting the frozen text wherever they name
a sentence — never deleting it. **Unlike GRTJB, GRTJC's status supersession is EXPRESS**:
**Annex #7** (unit `.130`) names `[r6] S-STATUS (CURRENT)` **by designation** and declares
it superseded — "Those passages are ROUND-RECORDS describing the state after r6 and before
PE7/PE8; their word 'CURRENT' is no longer live" — while the three GATE clauses (no gate
retires, the P0 application gate stands, no density/menu/count statement) are explicitly
**NOT** superseded. **This is the model GRTJB's own OPEN-CALL 1 (companion merge) says
GRTJB lacks**, and this merge preserves the contrast rather than harmonizing it.

**★ Annex #4 cures a CRITICAL, and its discharge status is "awaiting sol discharge
(cert3)" — carried forward exactly, not silently closed.** §4.1's frozen proof "lifted a
quotient equality" to `Δ`, which **contradicts the note's own JC-LOAD** on the load set
`δ ≥ g_m`; Annex #4 (unit `.127`) repairs it exactly, conclusion unchanged, "JC-LOAD's
load-set obstruction now respected rather than contradicted." **The acceptance record
(2026-08-06) predates the certifier annex (2026-08-12) by six days**, so GRTJC was
**ACCEPTED at 2/2 on a text containing a CRITICAL against a live proof of one of its four
faces** — Annex #7's status-supersession language ("together with the post-acceptance
corrections in Annexes #4–#8") is the note's own honest acknowledgement of this, and it is
**more than GRTJB's silence**, but it is an orchestrator declaration, not a fresh hostile
pass on the corrected text. Unit `.132`'s own closing ledger: "row 22 → **all five repairs
folded, awaiting sol discharge (cert3)**" — reproduced verbatim at `.127`/`.132` in §3
below and recorded again as OPEN-CALL 2 in §7.

### Scope of record — mandatory THREE-predicate split (rule 7 + rule 17)

**A. ABSORPTION / mathematical supply set.** The four weld faces THEOREM W-6 (`.54`),
THEOREM W-7 (`.75`), THEOREM W-8 (`.84`), and **COROLLARY W-9** (`.89`, "the four supply
clauses", the note's special-care unit — quoted byte-verbatim and untruncated in §3, with
its per-clause WELDZERO consumer table intact), plus the cyclic fence LAW JC-CYC and the
eleven-genre case split, all shard 2. §0's five inputs and §1's objects (shard 1) are the
definitional layer these rest on.

**B. APPEND / consumption-protocol scope.** GRTJC lands nothing on any supplier's own
frozen text as a proof-grade consumption append. §10.3's own gate discipline: "no gate
fires, **no gate retires**: DITERSUP §S3 gate J3b stays BLOCKED-ON-CARRIER-TIE (this note
DISPLAYS the tie it would need, and by construction cannot retire it)"; "no density/menu/
count statement is made anywhere." **Zero dated consumption appends are claimed landed on
GRTJB, GRTW2, GRTJA, or `DITERSUP`, and none is invented here.**

**C. INBOUND corrections received.** GRTJC receives **nothing from GRTJB** at the level of
a correction (the J-B ↔ J-C interface at `.03`/`.79` is a one-directional consumption, not
a correction), but its own suppliers correct it internally via the eight Annexes, all
homed in shard 3, landing on shard 1/shard 2 text — see §6's edge list.

### Resolution rules applied (merged; each shard's own numbered list is a restriction of
this one to its HOME range)

1. Lines 1–661 / 662–1937 / 1938–3059 supply the HOME material of shards 1/2/3
   respectively (title, S-STATUS series, §0 inputs, §1 objects / the four weld faces,
   LAW JC-CYC, the case split / the eight boxes, the machine bracket, the grade box, the
   acceptance record, all eight annexes).
2. `[r1]`…`[r6]` brackets are already-landed text; `[r1]` is struck, `[r2]`–`[r6]` are
   **KEPT ANNOTATED, not struck** — a second retention convention distinct from GRTJB's
   pure strike-and-replace, load-bearing because "a merge run must not treat an annotated
   block as live text" (the note's own words). Where three-plus layers stack, the full
   `CHAIN:` is recorded with TERMINAL marked — this note has **five** distinct chains,
   all converging on one HOME: `.43` (the `(IN-3)(c)`/`(DMULT)` alias-and-tier chain, the
   note's deepest at five layers, with body-site continuations at `.17`, `.36`, `.69`,
   `.120`), plus two independent single-site chains at `.46` and `.54` — §6 below.
3. `~~…~~` (shard 1's `[r1]` only) and the "kept annotated" convention (`[r2]`–`[r6]`, and
   GRTJC's dated Annexes generally) are both supersession markers, never deletion.
4. Annexes #1–#8 are applied as CONDITIONALITY at the in-range units they name, with the
   annex's own text quoted; no in-range sentence is edited. **Annex #7 is the note's
   express status supersession** (predicate distinct from the other seven's mathematical
   corrections).
5. Out-of-range statements are **not** emitted as units merely because they resolve
   in-range text — each is homed once, at its own physical section.
6. External repo records (report files, `runs/qgen/WELD_FACE_AUDIT.md`,
   `WELDZERO_2026-08-14.md`, the FGMN PDF) are reading notes only, never edits.
7. **CITE-SCOPE rows compiled as the note states them.** Two Q7 H6 rows (the FGMN
   rank-one and abscissa-additivity quotations) are both resolved **COVERS-ALL-O** by
   NS-9/NS-10 ("a pasting artefact, not a real gap"); recorded once, in full, at `.43`.
8. **`LEMMA J-D0` (the corpus's count-gauge-blindness frame, consumed elsewhere by
   `GENTOW5`/`W-12`) is cited NOWHERE in any of GRTJC's three shards** (exhaustive grep,
   this merge) — GRTJC's own twist-blind result, `LAW JC-CYC` clause (c) ("PROVED, general
   m — the twist-blind direction"), is a **locally-derived** consequence of `LAW JC-CYC`'s
   own hypotheses, not an import of `J-D0`. Recorded as an explicit compiler-verified
   NON-IMPORTS row (§2 below) since no source shard states the negative itself.

### Quotation and table discipline

CANONICAL STATEMENTs are verbatim source quotation or explicitly marked `[ASSEMBLED]`;
truncation marked `…`. **Unit `.89` (COROLLARY W-9) is quoted BYTE-VERBATIM AND
UNTRUNCATED**, per the charge's special-care direction for this unit, with its source
range independently re-read at HEAD to confirm `WELDZERO_2026-08-14.md`'s citation
(L1777–1788) is exact. Eleven displays are **double-emitted** (rule 14): the W-6 clause
list, the two (DMULT) tiers, the (G5-i)/(G5-ii) transport, JC-GAUGE's three-part
conclusion, the W-7 obligations, **W-9's four supply clauses with a per-clause consumer
column**, JC-CYC's five clauses, §7's eleven genres, §3.4's three census genres, and two
further consumer/clause tables. **This note's only two `\tag{}` LaTeX equation tags**
(`\tag{W8-q}`, `\tag{RM}`) are both inside sol-transcribed Annexes #4/#6 and are
reproduced with their tags intact. Compiler-authored ledgers (§2, §4, §5, §6) are flagged
`[TABLE — compiler ledger]`.

---

## 2. NON-IMPORTS (consolidated from all three shards; dedup marked; one compiler-added row)

`[TABLE — compiler ledger, consolidated from shard 1 §4 (15 rows), shard 2 §4 (14 rows),
shard 3 §4 (13 rows) = 42 raw rows, plus 1 compiler-verified negative-import row not stated
by any shard = 43 rows below, 2 dedup pairs folded]`

**Dedup count for this section: 2.** "The 606 non-integral perturbations have no leg" is
asserted at its home (`.81`) and restated at §9.5's closing line (`.100`) — one fact,
folded. "The census cannot certify by grep" is asserted identically at `.20` (shard 1's
alias census) and `.117` (shard 3's own name-pattern census) — the note itself calls these
"the same class of limit"; folded to one row citing both.

| Fence | Explicit material NOT imported, NOT claimed, or NOT supplied | Unit(s) |
|---|---|---|
| No gate retires | "no gate fires, **no gate retires**: DITERSUP §S3 gate J3b stays BLOCKED-ON-CARRIER-TIE … by construction cannot retire it" | `.02`, `.05`–`.10`, `.104`, `.121` |
| No `.lean` touched | "No `.lean` touched" — repeated in all six S-STATUS blocks | `.02`, `.05`–`.10` |
| No density/menu/count statement | "no density/menu/count statement is made anywhere" | `.02`, `.05`–`.10`, `.104`, `.121` |
| The P0 application gate stands | "the Asvin P0 application gate stands" | `.02` |
| The brief's germ hypothesis is NOT proved | "This note proves the instrument's law, not the brief's guess" — H-D FAILS 138/669 | `.03` |
| `(IN-3)(c)` is NOT consumed on `gr_{O[x]}` | "the transported claim is REFUTED … consumed ONLY through JC-LOC, as (DMULT-w) on B ≅ gr_{K[x]}(w) — never on gr_{O[x]}" | `.43`, `.31`, `.46`, `.64`, `.69`, `.99` |
| `(DMULT-s)` is NOT cited (pre-Annex-#1) | "FAILED in a specific, reportable way … no corpus-pinned statement delivers multiplier 1" | `.36`, `.69` |
| `(IN-2)` is NOT re-proved | "CONSUMED, NOT RE-PROVED." | `.42` |
| Everything in §1 is definition | "Everything in §1 is definition, not claim." | `.45` |
| No new battery at r3 | "the diversity fix is DISCLOSURE, not a new battery, per the effort directive" | `.21` |
| The candidate diversity leg is NOT built | "Candidate repair leg, NAMED, NOT BUILT" | `.24`, `.116` |
| **The census cannot certify by grep [DEDUP — `.20` and `.117`, the note's own "same class of limit"]** | "the census cannot certify the absence of further such lines by grep, and says so" | `.20`, `.117` |
| No supplier upgrade | "no clause is stronger than the weakest input it uses" | `.40` |
| JC-F2's fix is NOT made here | REVIEW-OWED at `GRW2_TIE_DESIGN`, the blueprint and the brief | `.52`, `.102` |
| `Λ_N(0)` is not supplied | "No value `Λ_N(0)` is supplied by REALIZE. The zero polynomial … does not have weight N." | `.51`, `.60`, `.67`, `.131` |
| Surjectivity NOT cited (pre-r0) | "the surjectivity half that r0 also cited is PROVED here (JC-BSURJ)" | `.67`, `.82` |
| `c_T` NOT used on the gr side | "𝒜(T)'s multiplication is gr(w)'s OWN (never c_T)"; "Deleting §3.3 leaves §§2–3.2 and 3.4 standing" | `.75`, `.83` |
| No harness read inside the determination | the instrument's certifier calls neither `Tower.constants` nor `Tower.read` "inside the determination or the certification" | `.83` |
| JB-EPS's authority NOT importable here | "importing J-B's authority for this step was unwarranted"; the two identifications STRUCK | `.86` |
| The abstract-cyclicity reading NOT the fence | "'𝒜(T) is NOT F′[u′]/(u′^E − ζ′)' cannot be read as an abstract-isomorphism claim" | `.91`, `.94`(a) |
| The converse of JC-CYC(d) NOT claimed | "The CONVERSE IS FALSE and this note does not claim it" — 13 named counterexamples | `.94`(d), `.102` |
| `c_T`'s VALUE NOT claimed off-stratum | genre 9: "the VALUE c_T is not claimed and has no machine support" | `.77`(2), `.96`, `.98` |
| No case owed at the interior-flat legs | genre 6: "the [RMG] fenced-corner genre is inherited via J-B, not re-opened" | `.96` |
| **The 606 non-integral perturbations have no leg [DEDUP — `.81` home, `.100` restatement]** | "no machine leg … the one place r1 leaves a measurement owed" | `.81`, `.100` |
| R1-PSIK-LO is one-sided | "the machine leg only confirms that no sampled class is *certified dead*" — the probe's own disclosed limitation | `.100` |
| The top-flat corner, FGMN-free | "stays OPEN for one who wants it independent of the FGMN input" | `.101` |
| Annex #5: the universal non-obtainability (withdrawn from shard 3) | the outer factor is always `q(y^δ)`; only its pre-TC-3 availability is at issue | `.54`(iv), `.62`(a) |
| Annex #4: the lift to Δ (withdrawn from shard 3) | only the CONGRUENCE descends; the polynomial equality is scoped to `δ < g_m` | `.85`, `.127` |
| Annex #6: the quoted product law (withdrawn from shard 3) | "the statement that (DMULT-w) is itself a quoted FGMN residual-product identity is withdrawn" | `.69`, `.129` |
| JC8's unit half evidenced nothing | "the violation branch is unreachable and the skipped pairs were never censused" | `.107` |
| The cyclic-split agreement is not independent | "the verdict-identity is a *consistency* check of W-8, not a second independent measurement" | `.108` |
| The r1 bilinear content was never exercised | "the identity's genuinely BILINEAR content … was NEVER exercised by r1" | `.113` |
| The r2 dense leg is not decorrelated | the r1 helpers are "imported, not re-typed, so the (DMULT) predicate is the SAME predicate" | `.114` |
| No Lean hypothesis discharged | "the compiled file's `hTrack` still needs a Lean-level supplier, and this note is not it" | `.121` |
| Acceptance upgrades nothing | "does not upgrade any upstream ATTEMPT-grade input or remove any displayed scope fence" | `.130` |
| No PDF multiplier formula is claimed | "no claim that the PDF itself supplies a multiplier formula is made" | `.129` |
| Citation precision, owed then discharged | JC-BOX-3 item 2 "still not re-verified against a printed source" → DISCHARGED by Annexes #2/#3; the W-1 transport legs it also names remain open | `.99`, `.125` |
| **`LEMMA J-D0` is consumed NOWHERE in GRTJC (compiler-verified negative, no shard states it)** | Exhaustive grep of all three source shards for `JD0`/`J-D0` returns **zero hits**; GRTJC's own twist-blind result (LAW JC-CYC clause (c), "PROVED, general m — the twist-blind direction") is derived locally from JC-CYC's own hypotheses (`\|K\|=2 ⇒ c≡1` and the ≤-one-non-1-value case), not by importing the corpus's shared count-gauge-blindness lemma `J-D0` (consumed elsewhere by `GENTOW5`/`W-12`). Recorded here because a DAG built from citation-presence alone would wrongly assume every corpus note touching "twist-blindness" routes through `J-D0`. | `.94`(c) [compiler cross-check, not a source citation] |

---

## 3. Statement inventory (132 units, contiguous, in source order)

### EFF.GRTJC.01  [scope record]

**CANONICAL STATEMENT:** verbatim, line 1.
**FORM:** display (the note's H1 title).

> “# GRTJC — J-C, THE CARRY-ALGEBRA JUNCTION (W-6..W-9): the composite-stage graded target exists (localize + gauge, with the ℤ → ℤ/E collapse proved), TC-3 is load-bearing EXACTLY at δ ≥ g_m (theorem, not observation), the anchor-transport isomorphism Ψ with the measured inner normalization ∏_{j≤m} z_j^{D_j}, harness-val = TC-read, and the cocycle semantics — four separately boxed clauses, each an honest proof or an honestly boxed obstruction”

**CONDITIONALITY:** Five supply items, each fenced differently in shard 2. **Two are corrected from shard 3:** “TC-3 is load-bearing EXACTLY at δ ≥ g_m” is re-displayed by **Annex #5** (the outer factor is *always* `q(y^δ) = z̄^δ`; it is *unavailable as a pre-TC-3 scalar* exactly when `δ ≥ g_m`), and “harness-val = TC-read” is re-proved by **Annex #4** as a quotient computation, conclusion unchanged. **“the measured inner normalization” is honest wording**: OB-3's VALUE rides `[ILN]†`'s scored stratum and the sharp form rides the MEASURED tier `(DMULT-s)`.

**DERIVATION:** Not a mathematical unit; the title is the supply headline. Discharged at §2 (W-6), §3 (W-7), §4 (W-8), §5 (W-9) — all shard 2.

**RESOLUTION TRACE:** statement line 1; proof lines 662–1843 (shard 2); correction sites 2840–2884 (Annex #4), 2890–2911 (Annex #5) — shard 3.

XREF: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md:ITER-LAW-n` — grep-verified count **11**.

**TEETH:** composite — the instrument (22 families) plus three own batteries (§9, shard 3).

---
### EFF.GRTJC.02  [scope record]

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
### EFF.GRTJC.03  [instrument-record]  ★ the instrument, and its REFUTATION of the brief

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
### EFF.GRTJC.04  [instrument-record]  the note's own battery

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
### EFF.GRTJC.05 — .10  [SERIES: `S-STATUS`, six dated members]  [run-record ×6]

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
### EFF.GRTJC.11  [run-record]  REPAIR ROUND r6 — the two-edit pointer repair

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
### EFF.GRTJC.12  [run-record]  REPAIR ROUND r5 — header

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
### EFF.GRTJC.13  [supplier-finding]  ★ r5/G-1 — the census species' THIRD recurrence, inside the block written to end it

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
### EFF.GRTJC.14  [changes-record]  r5/G-2 — the FGMN footprint completed at the stack displays

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
### EFF.GRTJC.15  [changes-record]  r5/m-1 — “nonzero” at §2.8

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
### EFF.GRTJC.16  [run-record]  REPAIR ROUND r4 — header

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
### EFF.GRTJC.17  [supplier-finding]  ★ r4/G-1 — the FOURTH alias, and the union-pattern sweep

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
**TERMINAL = the r4 union sweep, as verified by PE4/PE5/PE6.** `CHAIN HOME: .43` (the `(IN-3)` declaration).

**★ THE METHODOLOGICAL LESSON, stated by the note:** a name-pattern sweep can reach fixed point under its own pattern and still miss the input under an alias. **The cure is a union pattern over every name the input ever carried, PLUS a content audit of the live bucket.** **And even that has a disclosed resolution limit** (`.20`).

**CONDITIONALITY:** The struck clause was “live … un-superseded since r0” — it survived four rounds.

**DERIVATION:** A union grep + a content audit.

**RESOLUTION TRACE:** statement lines 271–282; the §0 display 573–602 (`.46`); the census 2452–2597 (shard 3); the earlier chain members 316–319 (r3/G-1, `.22`), 464–469 (r2/G-4, `.38`), 359–377 (r1/F1, `.31`).

**TEETH:** **AUDIT — arithmetic recount**, reproduced independently by PE5 (144 = 42/28/74 bucket for bucket) and PE6 (18/18 numbers). Disposition: **accepted-with-decorrelation-supplied**.

---
### EFF.GRTJC.18  [changes-record]  r4/G-2 — the arc record brought forward

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
### EFF.GRTJC.19  [supplier-finding]  r4/G-3 — JC-LOAD's constant re-tiered

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
### EFF.GRTJC.20  [changes-record]  ★ r4/G-4 — the CONTENT line invisible to every name census

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
### EFF.GRTJC.21  [run-record]  REPAIR ROUND r3 — header

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
### EFF.GRTJC.22  [supplier-finding]  ★ r3/G-1 — the alias-blind sweep, and the live re-route

**CANONICAL STATEMENT:** verbatim, lines 314–319.
**FORM:** bold-headed bullet.

> “* **G-1 (the live one)** — JC-LOAD's proof body and honest fence (§2.8) still
>   consumed the PE1-refuted `(IN-3)(c)`-on-gr BY NAME: the r2 sweep's grep was
>   ALIAS-BLIND (`(COORD)`/`(MULT)` only). Both sites re-routed through
>   §4.2 = (MULT-B)|gr (riding (DMULT-w)) — the step actually used, at δ = 0 —
>   and the ALIAS-COMPLETE re-sweep ((IN-3) + Thm 4.2 + (COORD)/(MULT)) is now
>   §9.5's protocol, census recorded there.”

**CHAIN:** member 3 of the `(IN-3)(c)` alias chain (`.17`). `CHAIN-MEMBER: .43 position 3.`

**SUPERSESSION KIND:** `scope-pin` — a refuted input's consumption re-routed to the step actually used.

**CONDITIONALITY:** **“the live one”** — the note's own label distinguishing this from the round's seven record/labelling gaps. **The re-route is mathematically substantive**: the step actually used is §4.2's offset-transport lemma `= (MULT-B)|gr` at `δ = 0`, riding `(DMULT-w)`, not `(IN-3)(c)`-on-`gr`. **The refuted input survived TWO rounds after its refutation because the sweep pattern did not include its own name.**

**DERIVATION:** Identification of the step actually used, plus a widened sweep.

**RESOLUTION TRACE:** statement lines 314–319; the two re-routed sites 885–889 and 918–921 (§2.8, shard 2); §4.2 1747–1756 (shard 2); the census 2421–2450 (shard 3).

**TEETH:** **AUDIT — in-house hostile pass** (PE3 found it; no battery keys a citation name).

---
### EFF.GRTJC.23  [supplier-finding]  ★ r3/G-2 — a sweep record wrong at its own commit

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
### EFF.GRTJC.24  [instrument-record]  ★ r3/G-3 — the sampling-diversity overstatement (species, 3rd recurrence)

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
### EFF.GRTJC.25  [supplier-finding]  r3/G-4 — a false divisibility attached to a true measured fact

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
### EFF.GRTJC.26  [changes-record]  r3/G-5 — the TC-3 display's load-bearing one-liner

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
### EFF.GRTJC.27  [supplier-finding]  ★ r3/G-6 — the TR-3′-GEN gloss misquoted its own record twice

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
### EFF.GRTJC.28  [changes-record]  r3/G-7 — a byte-frozen prereg row annotated with its blast radius

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
### EFF.GRTJC.29  [supplier-finding]  r3/G-8 — JC-CYC(b)'s false trigger

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
### EFF.GRTJC.30  [run-record]  REPAIR ROUND r1 — header (the STRUCTURAL round)

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
### EFF.GRTJC.31  [supplier-finding]  ★★ r1/F1 (CRITICAL 1) — the coordinate calculus was stated on the WRONG OBJECT

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

**CONDITIONALITY:** **`(DMULT)` was later SPLIT into two tiers by r2/G-1** (`.36`) and, post-acceptance, **Annex #6 withdraws the claim that `(DMULT-w)` is itself a quoted FGMN identity and DERIVES it instead** from the PDF-verified rank-one theorem via **LEMMA JC-RANKMULT**. **So the “single cited input” of r1 became, at the end, a DERIVED consequence of a different cited input.** `CHAIN HOME: .43`, member 1.

**PIN VERIFICATION:** PE1's counter-instance is on “the battery's own row C2I at the battery's own window base”; the corresponding scored fact is R1-BND (`maxslot(G0) == 0` on 29/29, shard 3). **Both re-verifiable from the committed artifacts; not re-run here.**

**DERIVATION:** The slot bound (shard 2, L1007–1022) plus JC-DOM/JC-LOC.

**RESOLUTION TRACE:** statement lines 359–377; the repair 992–1414 (§2.10, shard 2); the five consumers' verdict table 1402–1408 (shard 2); the later tier split 1188–1267 (shard 2); **Annex #6's re-derivation 2917–3000 (shard 3)**.

XREF: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md:REALIZE` — count **17** · `S4.1` — count **35**.

**TEETH:** **PE1's machine counter-instance** (row C2I, 3,072 integral `f` with `w(f) = 4`, slot set `{0}` throughout, `𝔦 ∩ gr_4 = 0`, so `gr_4 ≅ K_m` while `[K:K_m] = g_m = 2`), reproduced as the scored family **R1-BND** (0 violations on 29/29) with tooth **T1** (the refuted universal claim, must fire — 29/29 firings). **A refutation converted into a permanent scored regression.** Disposition: **planted mutant from a refuted claim; fired**.

---
### EFF.GRTJC.32  [supplier-finding]  ★ r1/F2 (CRITICAL 2) — an over-quantified corollary

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
### EFF.GRTJC.33  [changes-record]  r1 — the eight gap dispositions, assembled

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
### EFF.GRTJC.34  [instrument-record]  r1 — the new machine leg

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
### EFF.GRTJC.35  [run-record]  REPAIR ROUND r2 — header

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
### EFF.GRTJC.36  [supplier-finding]  ★★ r2/G-1 — the (DMULT) TIER SPLIT (the round's one item with content)

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

**CHAIN (rule 25) — the `(IN-3)(c)` / `(DMULT)` chain, FIVE layers.** r0: `(IN-3)(c)` on `gr` CITED → **r1/F1**: refuted on `gr`, re-based on `B`, reduced to the single cited input `(DMULT)` → **r2/G-1**: split into `(DMULT-w)` DERIVED / `(DMULT-s)` MEASURED → **Annex #1**: `(DMULT-s)` PROVED-conditional on the measured perimeter → **Annex #6**: `(DMULT-w)` itself WITHDRAWN as a citation and DERIVED from Thm 4.2's rank-one freeness. **TERMINAL = Annex #6's derivation + Annex #1's conditional proof.** `CHAIN HOME: .43.`

**DERIVATION:** Displayed at §2.10 (shard 2, L1208–1218).

**RESOLUTION TRACE:** statement lines 434–447; the tier split 1188–1267 (shard 2); the consumer split 1249–1260 (shard 2); **Annex #1 at 2805, Annex #6 at 2917–3000 (shard 3)**.

XREF: `lean/notes/openmath/GRB_ORDER2_2026-08-05.md:TR-3′-GEN` — count **57** · `S3.4` — count **25** · `S6a` — count **8**. `lean/notes/openmath/DULEMMA_PROOF_2026-08-08.md` — **file EXISTS**.

**TEETH:** **(DMULT-s)** is measured by **R1-DMULT** (2,784/0, exact multiplier 1) and **R2-BIL/R2-PHI** (261 dense bilinear pairs, 0 violations), with teeth **T3** (1,392 firings) and **U1/U2** (261/261 each). **(DMULT-w)** carries no separate leg — it is implied by the exact tier's measurements and, post-Annex #6, derived. Disposition: **executable regression for the exact tier; DERIVATION for the weak tier**.

---
### EFF.GRTJC.37  [instrument-record]  ★ r2/G-2 — monomial-dominated samples and an undisclosed skip

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
### EFF.GRTJC.38  [changes-record]  r2 — the seven remaining dispositions, assembled

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
### EFF.GRTJC.39  [instrument-record]  r2 — the bilinearity leg

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
### EFF.GRTJC.40  [fence]  §0 — the conditionality-stack head

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
### EFF.GRTJC.41  [hypothesis]  (IN-1) [ILN]† — the accepted closed form, and its residuals

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
### EFF.GRTJC.42  [hypothesis]  (IN-2) GRB / D-REAL / CARRY-1 / (W-MULT) — the last-read layer

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
### EFF.GRTJC.43  [hypothesis]  ★★ (IN-3) — THE FGMN GRADED PACKAGE (the CITE-SCOPE unit and the chain home)

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
### EFF.GRTJC.44  [hypothesis]  (IN-4) W-2 / J-A / J-B — and the inherited J-B geography

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
### EFF.GRTJC.45  [hypothesis]  (IN-5) — the construction layer

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
### EFF.GRTJC.46  [scope record]  ★ THE STACK, ONE LINE — with its three-layer correction

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

**CHAIN (rule 25) — THREE layers on ONE display:** r0's one-liner → **r4/G-1** ((c) STRUCK; the fourth alias) → **r5/G-2** ((a)(b) ADDED) → **r6/G-1** (the pointer annotated: this display is LIVE and superseded by nothing). **TERMINAL: the display as it stands at HEAD, reading `[ILN]† ACCEPTED + GRB/CARRY-1 ACCEPTED-conditional + FGMN (a)(b)(d)(e) CITED [with (c) only via (DMULT-w) on B] + W-1/W-2/J-A/J-B ATTEMPT`.** `CHAIN-MEMBER: .43 (alias sweep), positions 4 and after.`

**★ THE POINTER INVERSION, and why it matters for a merge.** r4's bracket called §10.2's `[r1]`/`[r2]` stacks “the current stacks … which supersede this display”. r5 then declared those displays ROUND-RECORDS and completed §0's display **in place**. **So after r5 BOTH clauses were false: §10.2's are not current, and they do not supersede §0's — §0's is the live one.** r6 annotates rather than edits, per the arc's dated-annotation convention. **A merge run that follows the r4 pointer without the r6 annotation will read a round-record as the current stack.**

**CONDITIONALITY:** **STALE on two counts at HEAD.** (i) “W-1/W-2/J-A/J-B ATTEMPT (0/2)” — all three notes are now ACCEPTED (OPEN-CALL 3). (ii) “this note's own arc starts at 0/2. Nothing here may be consumed at proof grade before its hostile arc” — **EXPRESSLY superseded by Annex #7**, which names “every body-local prohibition on proof-grade consumption that is based solely on this note's former 0/2 counter”. **(iii) The FGMN entry itself is superseded by Annex #6's boxed form** (“(DMULT-w) derived above”).

**DERIVATION:** The stack is a conjunction of the five inputs' own grades.

**RESOLUTION TRACE:** statement lines 573–604; the five inputs 505–571 (`.41`–`.45`); §10.2's stacks 2687–2748 (shard 3); the dispositions 271–282 (r4/G-1), 247–255 (r5/G-2), 201–220 (r6/G-1); **Annexes #6 and #7 at 2917–3008 (shard 3)**.

**TEETH:** NONE (a conditionality display). Disposition: **AUDIT — in-house hostile pass** for the alias and pointer findings.

---
### EFF.GRTJC.47  [definition]  §1 — the base setting

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
### EFF.GRTJC.48  [definition]  §1 — keys and weights

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
### EFF.GRTJC.49  [definition]  §1 — residues, split, anchors

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
### EFF.GRTJC.50  [definition]  ★ §1 — the level read and the digit polynomial

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
### EFF.GRTJC.51  [definition]  §1 — the scalar lift

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
### EFF.GRTJC.52  [definition]  ★ §1 — the TC chain and 𝒜(T), with the r1/G2 correction

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
### EFF.GRTJC.53  [definition]  §1 — the harness cocycle `c_T`

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
### EFF.GRTJC.54  [lemma]  ★ THEOREM W-6 — the face box

**CANONICAL STATEMENT:** verbatim, lines 664–699 — the theorem box with its five clauses, the GRADE line and the `[r1]` post-repair grade.
**FORM:** display (a blockquoted face box).

> “**THEOREM W-6.** For every tower T of the [ILN]† class and every level m with
> E > 1: (i) TC-1 and TC-2 are legitimate ring-level operations on gr(w_{m+1});
> (ii) the gauged ring A(T) := gr(w)[in(π)^{-1}]/(in(π) − 1) is **ℤ/E-graded**,
> with ~~A_ν ≅ gr_n(w)-piece for any n ≡ ν~~ **[r1, G1: corrected to JC-GAUGE's
> actual conclusion]** `A_ν ≅ B_n` **for any n ≡ ν, where
> B_n = ∪_{k≥0}in(π)^{-k}gr_{n+kE} is JC-DOM's POST-TC-1 piece** — strictly
> bigger than gr_n in general (the slot bound maxslot(n+kE) of §2.10 grows
> strictly along the ladder infinitely often, so the injective transition maps
> in(π)·gr_{n+kE} ⊆ gr_{n+(k+1)E} are not onto and B_n is the strictly larger
> colimit; PE1's C2I ladder [(0,0),(1,0),(2,1),(3,1),(4,2),…] exhibits it). The
> lemma was always right; the r0 statement quoting it was not, and the
> distinction is load-bearing: B_n, not gr_n, is where Δ ≅ K_m[y] lives (§2.10
> [r1, F1]) — and the surviving index is the
> abscissa-coset index of §1's split (LEMMA JC-FIB); (iii) the anchor map
> γ ↦ [φ_γ] is E-periodic on the nose (LEMMA JC-PER), so it is defined on ℤ/E;
> (iv) **TC-3 is load-bearing exactly on the pairs with δ ≥ g_m** (THEOREM
> JC-LOAD), and the outer factor z̄^δ of c_T is TC-3's image of the graded slot
> shift y^δ — not obtainable from TC-1/TC-2 alone; (v) TC-3 is not a relabeling:
> the level-NR read is non-injective on a graded piece, with the classifier's own
> next key Φ_{m+1} as the kernel witness (COROLLARY JC-PSIKER).
>
> **GRADE: PROVED at general m** on inputs (IN-3)(a)(b)(c)(e) + (IN-5), with the
> single located exception of the **top-flat corner e_m = 1 ∧ g_m = 1** in
> JC-LOAD's sharp form (JC-BOX-4). Attempt grade 0/2.
>
> **[r1] GRADE, post-repair (supersedes the input list only).** Still **PROVED
> at general m**, and on a SMALLER literature footprint: the coordinate calculus
> now rides `(DMULT-w)` **[r2, G-1: the citable tier; the exact tier (DMULT-s)
> is MEASURED-only and carries JC-COB's sharp form alone]** (composite-stage
> residual multiplicativity) instead of
> (IN-3)(c)-on-gr, with (IN-3)(a)(b)(e) + (IN-5) unchanged; clause (ii)'s object
> is B_n (G1); clause (v) is re-quantified (F2). Boxes: ~~JC-BOX-4 (unchanged)~~
> **[r2, G-7: the box DID change at r1 — it gained a CONDITIONAL CLOSURE on
> (DMULT) (the corner is closed for a reader who grants (DMULT-w), open for one
> who wants it FGMN-independent); see JC-BOX-4 [r1]]** and
> JC-BOX-3 **re-cut to box APPLICABILITY, not literature truth**. Attempt 0/2.”

**Double-emission (rule 14) — the five clauses as a `[TABLE]` with their status at HEAD:**

| clause | statement | proved by | status at HEAD |
|---|---|---|---|
| **(i)** | TC-1 and TC-2 are legitimate ring-level operations on `gr(w_{m+1})` | JC-DOM (`.55`), JC-GAUGE (`.56`) | **PROVED, general m** |
| **(ii)** | `A(T) := gr(w)[in(π)^{-1}]/(in(π)−1)` is **ℤ/E-graded**, with `A_ν ≅ B_n` for any `n ≡ ν` | JC-GAUGE(iii) + JC-DOM | **PROVED**; **object corrected at r1/G1 from `gr_n` to `B_n`** — “`B_n`, not `gr_n`, is where `Δ ≅ K_m[y]` lives” |
| **(iii)** | the anchor map `γ ↦ [φ_γ]` is **E-periodic on the nose**, so defined on `ℤ/E` | JC-PER (`.57`) | **PROVED**, byte-exact |
| **(iv)** | **TC-3 is load-bearing exactly on the pairs with `δ ≥ g_m`**; the outer factor `z̄^δ` is TC-3's image of `y^δ` — **“not obtainable from TC-1/TC-2 alone”** | JC-LOAD (`.62`) | **SUPERSEDED IN DISPLAY by Annex #5** — the outer factor is *always* `q(y^δ) = z̄^δ`; it is *unavailable as a pre-TC-3 scalar* **exactly when `δ ≥ g_m`** |
| **(v)** | TC-3 is not a relabeling: the level-NR read is non-injective **on a graded piece**, with `Φ_{m+1}` as the kernel witness | JC-PSIKER (`.63`) | **PROVED; the fenced wording “on a graded piece” was ALREADY CORRECT and stands unamended** — only r0's unfenced generalization was refuted (r1/F2) |

**CHAIN (rule 25) — the input list, THREE layers:** r0 “(IN-3)(a)(b)(c)(e) + (IN-5)” → **r1**: `(IN-3)(c)`-on-`gr` replaced by `(DMULT)`, **a SMALLER footprint** → **r2/G-1**: `(DMULT)` split, only `(DMULT-w)` load-bearing. **TERMINAL: `(IN-3)(a)(b)(e) + (IN-5) + (DMULT-w)`, with `(DMULT-w)` itself DERIVED post-acceptance (Annex #6).** `CHAIN HOME: .43.`

**★ CONDITIONALITY — Annex #5 re-displays clause (iv), and the correction is REAL** (shard 3, L2890–2911):

> “**[ANNEX 2026-08-12 #5, post-acceptance correction — exact scope of outer-factor non-obtainability.]** This annex supersedes W-6(iv), JC-LOAD(a), and **every unqualified occurrence of “`z̄^δ` is not obtainable from TC-1/TC-2 alone”** by the following display:
> **The outer factor is always `q(y^δ) = z̄^δ`, and it is unavailable as a pre-TC-3 scalar exactly when `δ ≥ g_m`.**
> … * if `δ < g_m`, then `y^δ` is already the canonical degree-`< g_m` representative of `z̄^δ`, so the outer factor — and, after multiplication by the inner `K_m^*`-unit, the complete scalar — **is obtainable before TC-3**;
> * if `δ ≥ g_m`, no nonzero polynomial of degree `< g_m` equals `u y^δ` with `u ∈ K_m^*`, so **TC-3 is indispensable**.”

**SUPERSESSION KIND: `partial-withdrawal`** (the enum gap the GRTJB shards identified — a display is re-issued, most of the clause survives). **Annex #5's own consumer sweep:** “JC-LOAD's iff and its sealed set identity survive unchanged. §3.2's structural outer/inner split survives … §7 genres 1–2 remain RAW-solvable and genres 3–4 retain the stated `g_m = 1` split. W-7, W-8, and W-9 consume the factor's value or shape, **not the refuted universal interpretation**, and survive.”

**Also conditional:** the **top-flat corner `e_m = 1 ∧ g_m = 1`** is the single located exception (JC-BOX-4), **CONDITIONALLY CLOSED at r1 on `(DMULT-w)`** — “closed for a reader who grants (DMULT-w), open for one who wants it FGMN-independent”. **The grade line's “Attempt grade 0/2” is EXPRESSLY superseded by Annex #7.**

**DERIVATION:** Clause by clause, `.55`–`.63`.

**RESOLUTION TRACE:** statement lines 664–699; proof lines 701–1414 (§2's lemmas); correction sites 2890–2911 (Annex #5), 3004–3008 (Annex #7), 2004–2027 (JC-BOX-4, shard 3), 1960–1992 (JC-BOX-3, shard 3).

XREF: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md:ITER-LAW-n` — grep-verified count **11**.

**TEETH:** JC1–JC6 + MJ1–MJ5 (§9.2, shard 3): 8,566 samples, 0 violations, all five teeth fired.

---
### EFF.GRTJC.55  [lemma]  LEMMA JC-DOM — TC-1 is legitimate

**CANONICAL STATEMENT:** verbatim, lines 703–716 (statement and proof).
**FORM:** bold-headed lemma with `*Statement.*` / `*Proof.*`.

> “*Statement.* gr(w) is a commutative ℤ-graded domain; in(π) is homogeneous of
> degree **E** and is a nonzerodivisor; hence the localization
> B := gr(w)[in(π)^{-1}] exists as a ℤ-graded ring, gr(w) ↪ B, and
> B_n = ∪_{k≥0} in(π)^{-k}·gr_{n+kE}.
>
> *Proof.* By (IN-3)(a) w is multiplicative, so for f,g ≠ 0,
> in(f)in(g) = in(fg) ≠ 0 in gr_{w(f)+w(g)}: gr(w) is a domain ((IN-3)(b), the
> same domain property the accepted GRB S6a cancellation uses). For the degree:
> w_0(π) = 1 and, since the Φ_j-development of the constant π is A_0 = π,
> w_{j+1}(π) = e_jw_j(π); hence **w(π) = e_0e_1⋯e_m = E** by induction. A
> nonzerodivisor homogeneous element of a graded domain may be inverted: the
> graded localization at the multiplicative set {in(π)^k} is a ℤ-graded ring, with
> the stated degree pieces, and the localization map is injective because gr(w) is
> a domain. ∎”

**CONDITIONALITY:** **Consumes `(IN-3)(a)` and `(IN-3)(b)` — the two clauses NEVER refuted**, and the two that r5/G-2 had to ADD to the stack displays (shard 1 `.14`). **`w(π) = E` is proved by induction here, not cited.**

**★ THE REMARK IS THE POINT** (lines 718–721): “GRW2_TIE_DESIGN's OB-1 asked for exactly this at the composite stage and recorded ‘no accepted clause supplies it’. **The supply is multiplicativity of w — which is (IN-3)(a), a literature fact for types of every order, not a last-read-layer accident.**” **So an open design-note obligation is discharged by identifying the right citation.**

**GENERALITY NOTE (Q7, recorded not applied):** *“`w_0(π)=1` … `w(π)=e_0e_1⋯e_m=E` — **BENIGN.** This uses the chosen uniformizer `π`, not the integer prime `p`, and nowhere assumes `v(p)<∞`. **In `F_q[[t]]`, take `π=t`.**”*

**DERIVATION:** Displayed in full above. Three steps: multiplicativity ⇒ domain; the induction `w_{j+1}(π) = e_j w_j(π)` from the constant's development ⇒ `w(π) = E`; graded localization at a homogeneous nonzerodivisor.

**RESOLUTION TRACE:** statement lines 703–721; consumed at `.56` (as the source of `ϑ = in(π) ∈ B_E`), `.65`, `.68`, `.73`.

XREF: `lean/notes/openmath/GRB_ORDER2_2026-08-05.md:S6a` — count **8**. `GRW2_TIE_DESIGN_2026-08-08.md` — **file EXISTS**.

**TEETH:** **JC1** — “JC-PER + `w(π) = E`: `φ_{γ+kE} == π^k φ_γ` byte-for-byte at `k = 1,2,3`; s-tuple E-periodic; `u_1 ↦ u_1+k`” — **2,594 samples, 0 violations, `w(π) = E` on all 29 rows**.

---
### EFF.GRTJC.56  [lemma]  LEMMA JC-GAUGE — TC-2 is legitimate, and ℤ collapses to ℤ/E

**CANONICAL STATEMENT:** verbatim, lines 725–752 (statement, proof and application).
**FORM:** bold-headed lemma with a fixed-width three-part conclusion.

> “*Statement.* Let B = ⊕_{n∈ℤ}B_n be any commutative ℤ-graded ring containing a
> **unit** ϑ ∈ B_E, E ≥ 1. Put A := B/(ϑ−1)B. Then
>
>     (i)  (ϑ−1)B = ⊕_{ν∈ℤ/E} (ϑ−1)B^{(ν)},  B^{(ν)} := ⊕_{n≡ν (E)} B_n,
>     (ii) A = ⊕_{ν∈ℤ/E} A_ν  is ℤ/E-GRADED, A_ν := image of B^{(ν)},
>          A_νA_{ν′} ⊆ A_{ν+ν′},
>     (iii) for each ν and EACH n ≡ ν (mod E) the composite B_n → A_ν is an
>           isomorphism of additive groups; in particular A_0 ≅ B_0 as rings.”

**With its proof (lines 734–743) and application (745–752), the application quoted:**

> “*Application.* Take B from JC-DOM and ϑ := in(π) ∈ B_E (a unit after TC-1, of
> degree E by JC-DOM — the harness check w(π) = E the design note wanted). TC-2 is
> therefore a legitimate ring-level operation at **every** stage, its output is
> ℤ/E-graded, and the design note's C13 objection ("p ↦ 1 is not a graded
> homomorphism from TC-1's output alone") is answered in the only way it can be:
> the gauge is not a graded map but a **quotient by a non-homogeneous principal
> ideal whose ideal splits along the E residue classes**, which is exactly why the
> grading survives modulo E and not on the nose.”

**★ THE LEMMA IS STATED FOR AN ARBITRARY GRADED RING — a deliberate abstraction, and it is what makes the answer to C13 clean.** The application then instantiates it. **The C13 objection is answered structurally, not by construction: “the gauge is not a graded map but a quotient by a non-homogeneous principal ideal whose ideal splits along the E residue classes.”**

**CONDITIONALITY:** Unconditional as an abstract lemma (`B` any commutative ℤ-graded ring with a unit `ϑ ∈ B_E`, `E ≥ 1`). **Its instantiation needs TC-1 first** — `in(π)` is a unit only after localization — and the note stresses the order: “TC-1 strictly before TC-2” (PE1 verified it).

**GENERALITY NOTE (Q7, recorded not applied):** *“‘TC-1 localize `gr(w)` at `in(π)`; TC-2 gauge `π ↦ 1`’ — **BENIGN.** … not Witt-vector or unramified-ℤ_p structure.”* And: *“‘the grading collapses ℤ → ℤ/E’ — **BENIGN.** … no division by `E` in the coefficient field and no extraction of an `E`-th root.”*

**DERIVATION:** Displayed in full (lines 734–743). (i) For homogeneous `b ∈ B_n`, `(ϑ−1)b` has both terms in `B^{(n mod E)}`. (iii) is the substantive step: `σ(Σ_k b_{n+kE}) := Σ_k ϑ^{-k}b_{n+kE}` is additive, surjective, kills `(ϑ−1)B^{(ν)}`, and conversely `x ≡ σ(x)` modulo `(ϑ−1)B^{(ν)}`, so `ker σ = (ϑ−1)B^{(ν)}`.

**RESOLUTION TRACE:** statement lines 725–752; the interface correction 385–386 (r1/G1, shard 1 `.33`); consumed at `.01`(ii), `.20` (the ideal transport), `.23`, `.27`.

**TEETH:** JC1 (the periodicity half); **PE7 re-proved JC-GAUGE via coarsened grading + a fresh out-of-roster `p = 7` leg** (the acceptance record, shard 3) — **a method-diverse re-derivation.**

---
### EFF.GRTJC.57  [lemma]  LEMMA JC-PER — the anchor system is E-periodic on the nose

**CANONICAL STATEMENT:** verbatim, lines 756–772.
**FORM:** bold-headed lemma with `*Statement.*` / `*Proof.*` / `*Machine:*`.

> “*Statement.* For every γ ∈ W and k ≥ 0: the split satisfies
> s_{j+1}(γ+kE) = s_{j+1}(γ) for all j and u_1(γ+kE) = u_1(γ) + k; hence
> **φ_{γ+kE} = π^k·φ_γ as polynomials (byte-for-byte)**, and after TC-2
> [φ_{γ+E}] = [φ_γ]. So u_γ ↦ [φ_γ] is well defined on ℤ/E, and (choosing window
> representatives) independent of the representative.”

**★ “BYTE-FOR-BYTE” IS NOT RHETORICAL — it is what the machine keys.** *Machine* (lines 770–772): “instrument **P0-OB2 = 0/285 byte-for-byte** on every anchor of every row (OB-2/COR-4 exact); this note's own battery re-tests it at `k = 1,2,3` (family JC1).”

**CONDITIONALITY:** Requires `γ ∈ W` (the window). **This is OB-2 and it is the cleanest clause in the note — PROVED at general `m`, byte-exact, double-measured.**

**DERIVATION:** Displayed (lines 762–768): induction down the split. At the top `e_m | E` gives `s_{NR}(γ+E) = s_{NR}(γ)` and `u_{NR}(γ+E) = u_{NR}(γ) + E/e_m`; the same step at each level leaves `s_j` unchanged and increases `β_{j−1}`; at the bottom `u_1(γ+E) = u_1(γ) + 1`. The anchor formula then differs by exactly one factor `π`.

**GENERALITY NOTE (Q7, recorded not applied):** *“‘`s_NR(γ+E)=s_NR(γ)`’ and ‘`u_1(γ+E)=u_1(γ)+1`’ — **BENIGN — integer congruence arithmetic.**”*

**RESOLUTION TRACE:** statement lines 756–772; consumed at `.54`(iii), `.56` (the application), `.66`, `.71` (the virtual-anchor transport), `.76`, `.91`(iv).

**TEETH:** **instrument P0-OB2 0/285 byte-for-byte** + **JC1 (2,594 samples)** + tooth **MJ2** (“mutated periodicity `φ_{γ+E} == π²φ_γ`”, **285 firings — fired on every row**). Disposition: **executable regression, double-instrumented, with a planted mutant.**

---
### EFF.GRTJC.58  [lemma]  LEMMA JC-FIB — which ℤ/E-indexing survives

**CANONICAL STATEMENT:** verbatim, lines 776–789.
**FORM:** bold-headed lemma.

> “*Statement.* γ ↦ (s_1(γ),…,s_{NR}(γ)) ∈ ∏_{j=0}^{m}ℤ/e_j is E-periodic and
> induces a **bijection ℤ/E ≅ ∏_j ℤ/e_j**. Hence the ℤ/E-grading of JC-GAUGE is
> indexed equivalently by γ mod E and by the abscissa-coset tuple — the fibred
> ℤ/E-indexing of DITER_RESTATE §S3 obligation 1 (design-note G19).”

**★ ANOTHER DESIGN-NOTE OBLIGATION DISCHARGED BY IDENTIFICATION** — “the fibred ℤ/E-indexing of DITER_RESTATE §S3 obligation 1 (design-note G19)”.

**CONDITIONALITY:** Unconditional given the split's definition. **The bijection is what lets W-7's Ψ be indexed by `ℤ/E` and simultaneously by abscissa cosets** — the two indexings the design note asked to be reconciled.

**DERIVATION:** Displayed (lines 781–786). Periodicity is JC-PER. Both sides have `E` elements, so injectivity on `[0,E)` suffices: equal `s_{NR}` forces `γ ≡ γ′ (mod e_m)` (as `s_{NR} = ℓ_mγ mod e_m` with `ℓ_m` invertible); descending, equality of `s_{NR−1}` forces `(γ−γ′)/e_m ≡ 0 (mod e_{m−1})`, and so on down to `E | γ−γ′`.

**RESOLUTION TRACE:** statement lines 776–789; consumed at `.54`(ii), `.60`, `.70`, `.80`.

**TEETH:** **JC2** (“the s-tuple map is injective on `E` consecutive `γ` + periodicity”, **570 samples, 0 violations, every row**); the instrument's **P4-DEG (0/29)** is “its weaker shadow”.

---
### EFF.GRTJC.59  [lemma]  LEMMA JC-ANCHMON — the anchor is a single Φ_m-digit

**CANONICAL STATEMENT:** verbatim, lines 793–805.
**FORM:** bold-headed lemma with a four-part conclusion.

> “*Statement.* For γ ∈ W: (a) Σ_{j<m}s_{j+1}·deg Φ_j < deg Φ_m; hence (b) the
> Φ_m-development of φ_γ has exactly one nonzero digit, at abscissa s_{NR}(γ);
> hence (c) 𝑅_γ(φ_γ) is a nonzero **constant** in K_m (slot set {0}) and
> (d) deg φ_γ < (s_{NR}(γ)+1)·deg Φ_m.”

**★ CLAUSE (c) IS THE DEFINITION OF `a_λ`, THE ANCHOR CONSTANT — the object the whole ρ-normalization is built on** (`ρ_λ := 𝑅_λ/a_λ`, `.66`). **Clause (d) is the degree bound JC-SPAN's upper end uses**, and it is exactly what makes JC-SPAN `e_m`-sensitive (JC-BOX-4's corner).

**CONDITIONALITY:** `γ ∈ W`. Unconditional otherwise — **pure digit arithmetic, and PE1 re-derived it independently and CLEARED it.**

**DERIVATION:** Displayed (lines 798–805). (a) `s_{j+1} ≤ e_j − 1` and `deg Φ_{j+1} = e_jg_j deg Φ_j ≥ e_j deg Φ_j`, so `s_{j+1}degΦ_j ≤ degΦ_{j+1} − degΦ_j`; summing telescopes to `≤ deg Φ_m − deg Φ_0 < deg Φ_m`. (b) `φ_γ = (π^{u_1}∏_{j<m}Φ_j^{s_{j+1}})·Φ_m^{s_{NR}}` with the parenthesis of degree `< deg Φ_m` by (a) — **that IS the `Φ_m`-development**. (c) the single digit sits at the line's base abscissa, so slot 0; nonzero and on the line.

**RESOLUTION TRACE:** statement lines 793–805; consumed at `.61` (both ends), `.66`(c), `.69` (the `a_γ` constants), `.72`.

**TEETH:** **JC5** (“the telescoping degree bound, the single-digit development, slot set {0}, `a_λ ≠ 0`”, **855 samples, 0 violations**).

---
### EFF.GRTJC.60  [lemma]  LEMMA JC-SCAL — the scalar image (and the Annex #8 quantifier repair)

**CANONICAL STATEMENT:** verbatim, lines 809–825.
**FORM:** bold-headed lemma with a three-part conclusion.

> “*Statement.* For N ≡ 0 (mod E), N ≥ wΦ_{NR}, and c = Σ_{i<g_m}c_iz̄^i ∈ K
> (c_i ∈ K_m, the canonical representative): (a) s_{NR}(N) = s_{NR}(0) = 0 and
> the on-line slot set of Λ_N(c) is contained in {0,…,g_m−1}, with slot i digit
> the ε-corrected c_i; so **𝑅_N(Λ_N(c)) is the canonical degree-<g_m
> representative of c, up to one line-wise unit**; (b) 𝑅_N(X_N) is a nonzero
> CONSTANT (slot set {0}); (c) consequently the "scalar image" at line N is
> exactly 𝑅_N(X_N)·{K_m-polynomials of degree < g_m}.”

**★ CONDITIONALITY — SUPERSEDED IN QUANTIFIER BY ANNEX #8** (shard 3, L3014–3037). Two changes, both narrowing:

> “Accordingly **JC-SCAL is re-displayed with `c ∈ K^*`**. Its scalar-image conclusion is
> `𝑅_N(X_N)·{ p ∈ K_m[y] : p ≠ 0, deg p < g_m }`.”

and the ground: “**No value `Λ_N(0)` is supplied by REALIZE.** The zero polynomial represents the zero class and has zero read, but it does not have weight `N`.”

**SUPERSESSION KIND: `partial-withdrawal`** — clause (c)'s image set is re-displayed with “nonzero”; clauses (a)/(b) survive with the narrowed quantifier. **r5/m-1 (shard 1 `.15`) had already patched the §2.8 display of this same set — Annex #8 is the general repair.**

**Annex #8's consumer sweep (quoted):** “**JC-LOAD already quantifies `c ∈ K^*` and survives.** W-8's `c_{m+1}` is a unit by JC-CARRY-m, so its lift remains defined. `X_N = Λ_N(1)` is unchanged. **JC-SCAL, JC-BSURJ, COORD-B, and all downstream carrier-dimension arguments survive.** Historical JC4/R1-SURJ machine rows retain their numerical counts but **evidence only defined nonzero lifts and nonzero polynomial targets**.”

**DERIVATION:** Displayed (lines 817–822). `s_{NR}(N) = 0` because `E | N` and `s_{NR}` is E-periodic with `s_{NR}(0) = 0`. REALIZE's construction expands `τ = (c_0,…,c_{g_m−1})` as `Σ_i child_i·Φ_m^{k_i}` with `k_i = s_{NR}(N) + i·e_m`, `deg child_i < deg Φ_m` — so the abscissas are exactly `{i·e_m : c_i ≠ 0}` and the packed read is `c` by R3. For `c = 1` only `i = 0` survives.

**RESOLUTION TRACE:** statement lines 809–825; **correction site 3014–3037 (Annex #8, shard 3)**; the early symptom 256–259 (shard 1 `.15`); consumed at `.09` (the RHS of RAW), `.33` (W-8's normalization).

**TEETH:** **JC4** (443 samples: slot set `== supp(c) ⊆ {0..g_m−1}`, slot-`i` digit `== c_i`, **`𝑅_N(X_N) == 1` exactly**, every row and every `c ∈ K`); instrument shadows **P0-LIFT (0/138)**, **P0-SCAL (0/293)**; tooth **MJ3** (“mutated scalar image ‘slots ⊆ {0}’”, 4 firings — **fired on every `g_m ≥ 2` row**; “2 of the 6 opportunities are the `c`'s whose slot 1 is genuinely empty”). **Annex #8 narrows what these evidence, not their counts.**

---
### EFF.GRTJC.61  [lemma]  ★ THEOREM JC-SPAN — the slot span is the singleton {δ}

**CANONICAL STATEMENT:** verbatim, lines 829–857.
**FORM:** bold-headed theorem with `*Statement.*` / `*Proof.*` / `*Comment.*` / `*Machine:*`.

> “*Statement.* Let γ,γ′ ∈ W with γ+γ′ ∈ W, and let δ = δ(γ,γ′) ∈ {0,1} be the top
> carry. Assume **e_m ≥ 2**. Then the on-line slot set of φ_γφ_{γ′} at its own
> weight γ+γ′ is exactly **{δ}**, i.e.
>
>     𝑅_{γ+γ′}(φ_γφ_{γ′}) = u·y^{δ}  for some u ∈ K_m^*.
>
> If e_m = 1 (so δ = 0), the same argument gives slot set ⊆ {0,1} with 0 attained,
> i.e. deg 𝑅 ≤ 1.”

**★ THE COMMENT IS THE STRUCTURAL PAYLOAD** (lines 849–854):

> “*Comment.* This is the composite-stage replacement for CARRY-1
> (φ_γφ_{γ′} = φ_{γ+γ′}ȳ^δ, last-read layer, IN-2): at a composite stage the
> identity acquires **exactly one extra K_m-unit u**, and the theorem proves that
> the extra factor is a unit of K_m — a scalar that TC-3 never touches — while the
> y-degree is exactly δ. **The outer/inner split of c_T is therefore structural,
> not a coordinate choice**: outer = the slot shift y^δ; inner = u ∈ K_m^*.”

**This is the sentence that refutes the brief's guess structurally**, complementing the instrument's numerical refutation (shard 1 `.03`): the inner factor is a unit of `K_m`, and `−z_{m+1} ∉ K_m` whenever `g_m ≥ 2`.

**CONDITIONALITY:** **`e_m ≥ 2` for the sharp form.** At `e_m = 1` only `deg 𝑅 ≤ 1`, which suffices when `g_m ≥ 2` but not at `e_m = 1 ∧ g_m = 1` — **JC-BOX-4's corner, MEASURED there (C4H) and CONDITIONALLY CLOSED at r1 on `(DMULT-w)` by a second, `e_m`-blind proof.** Consumes **`(IN-3)(e)` = Cor 2.7** at the lower end — **a CITE-SCOPE row, resolved COVERS-ALL-O by NS-9** (shard 1 `.43`).

**DERIVATION:** Displayed in full (lines 838–847). **Lower end:** by `(IN-3)(e)` the minimal on-line abscissa of `φ_γφ_{γ′}` is `s_{NR}(γ)+s_{NR}(γ′)`, and the line's base abscissa at `λ = γ+γ′` is `s_{NR}(λ) = s+s′ − δe_m`; so the minimal slot is `δ`, attained. **Upper end:** by JC-ANCHMON(d), `deg(φ_γφ_{γ′}) < (s+1)degΦ_m + (s′+1)degΦ_m`, so the largest abscissa is `≤ s+s′+1`; on-line abscissas are `≡ s+s′−δe_m (mod e_m)`, so slots satisfy `k ≤ δ + 1/e_m`, i.e. **`k ≤ δ` when `e_m ≥ 2`**.

**RESOLUTION TRACE:** statement lines 829–857; consumed at `.62`, `.71` (`A` is a monomial of degree `δ`), `.72`, `.77`, `.86`; the corner box 2004–2027 (shard 3).

XREF: the `(IN-3)(e)` = **[FGMN] Cor 2.7** pin re-read at HEAD by this compiler: `docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt` **line 525** = “Corollary 2.7. For non-zero g, h ∈ K[x], we have Sλ (gh) = Sλ (g) + Sλ (h).” — **EXACT.**

**TEETH:** **JC3 — the note's OWN NEW sharp prediction**, sealed before the run: “the on-line slot set of `φ_γφ_{γ′}` at its own weight is EXACTLY `{δ}`”. **Verdict: 2,484 samples, 0 violations, slot set == {δ} on 609/609 pairs with `e_m ≥ 2`.** Plus **JC3-FLAT** (the `e_m = 1` corner: “census: **0 of 24 pairs have a slot > 0**” — the unproved sharp form measured true on C4H) and tooth **MJ5** (“slot set == {δ+1}”, **633 firings, fired on every pair**). Disposition: **a preregistered sharp prediction, hit exactly.**

---
### EFF.GRTJC.62  [lemma]  ★ THEOREM JC-LOAD — TC-3 is load-bearing EXACTLY at δ ≥ g_m

**CANONICAL STATEMENT:** verbatim, lines 861–924 — the statement, the three consequences with their `[r1, G5]` scoping, the proof with its `[r3, G-1]` re-route and `[r4, G-3]`/`[r5, m-1]` corrections, and the honest fence.
**FORM:** bold-headed theorem.

> “*Statement.* Fix a pair (γ,γ′) as above with e_m ≥ 2, and consider the
> **pre-TC-3** (RAW) equation in gr(w) localized and gauged but NOT quotiented by
> ψ_m: does there exist c ∈ K^* with
>
>     𝑅(φ_γφ_{γ′}·X_N) = 𝑅(Λ_N(c)·φ_{γ+γ′})   at the line γ+γ′+N ?   (RAW)
>
> Then: **(RAW) is solvable ⟺ δ < g_m.** Equivalently (δ ∈ {0,1}): the pre-TC-3
> scalar exists on every pair except those with δ = 1 ∧ g_m = 1, where the
> ψ_m-relation — i.e. TC-3 — is unavoidable. Consequently:
>
>     (a) c_T's OUTER factor z̄^δ is the image under TC-3 (y ↦ z̄) of the graded
>         slot shift y^δ; it is NOT obtainable from TC-1/TC-2 alone;
>     (b) c_T's INNER factor ∏_j z_j^{D_j} lies in K_m^* and needs no quotient;
>     (c) the sealed set identity {no pre-TC-3 scalar} = {δ ≥ g_m} of the
>         instrument (0/29 set-mismatches, 134/669 pairs) is a THEOREM, not an
>         observation.
>         [r1, G5 — SCOPED to the theorem's own fence.]  JC-LOAD is stated with
>         e_m ≥ 2, so the THEOREM covers the 28 roster rows with e_m ≥ 2; on the
>         one top-flat row (C4H, e_m = 1 …) the identity is MEASURED, not proved, and is boxed at
>         JC-BOX-4.  So: theorem where proved (28 rows), measured where measured
>         (C4H).  The instrument's 0/29 set-mismatch count is unchanged — what is
>         corrected is the r0 wording, which implied the theorem covered all 29.”

**★ THE TITLE CLAIM — “theorem, not observation” — is the note's headline, and clause (c) states exactly what was upgraded**: the instrument's sealed SET IDENTITY `{no pre-TC-3 scalar} = {δ ≥ g_m}` (0/29 set-mismatches over 134/669 pairs) is proved, on the 28 rows the theorem covers.

**★ CONDITIONALITY — Annex #5 supersedes clause (a)** (shard 3, L2890–2911), and W-6(iv) with it (`.54`). **The corrected reading:** the outer factor is **always** `q(y^δ) = z̄^δ`; it is **unavailable as a pre-TC-3 scalar exactly when `δ ≥ g_m`**. **Annex #5's own note: “JC-LOAD itself proves the counterexample supplied by the finding”** — i.e. the note's own iff already contained the correction, and only the gloss over-reached. **“JC-LOAD's iff and its sealed set identity survive unchanged.”**

**Two further in-range corrections, both quoted at the proof:**
- **`[r3, G-1]`**: the proof's transport step had cited the PE1-refuted `(IN-3)(c)`; **re-routed to §4.2 = `(MULT-B)|gr` at `δ = 0`, riding `(DMULT-w)`** — “the step actually used”.
- **`[r4, G-3]` + `[r5, m-1]`**: the multiplier is the anchor coboundary `b_× := a_{λ+N}/(a_λa_N)`, **not the exact-tier `𝑅(X_N)`**; and the RHS set is the **nonzero** polynomials of degree `< g_m`. **“the iff below is tier-blind”** — the same constant appears on both sides and cancels exactly (PE4 §A1 verified).

**DERIVATION:** Displayed (lines 885–916). Multiplying by `X_N` transports lines additively and multiplies the digit polynomial by a `K_m^*`-constant `b_×` **without changing its y-degree** (offset transport, §4.2; `s_{NR}(N) = 0` so `δ(γ+γ′,N) = 0`). By JC-SPAN the LHS has digit polynomial `b_×·u·y^δ` of exact y-degree `δ`; by JC-SCAL(a)(c) the RHS ranges over `b_×·{nonzero polynomials of degree < g_m}`. **Since `K_m[y]` is a polynomial ring, `u y^δ` (`u ≠ 0`) equals a polynomial of degree `< g_m` iff `δ < g_m`.** For (a): after TC-3 the class of `y^δ` is `z̄^δ`, and `y^δ` is not in the `K_m`-span of `{y^i}_{i<g_m}` when `δ ≥ g_m`.

**★ THE HONEST FENCE, verbatim (lines 918–924):**

> “*Honest fence.* The proof of the ⟸ direction rides the offset-transport step
> (§4.2), which rides ~~(IN-3)(c)~~ **(MULT-B)|gr and with it (DMULT-w)
> [r3, G-1 …]**; the ⟹ direction (the obstruction) rides only
> JC-SPAN + JC-SCAL. The instrument's k-distribution **{0 : 669}** says the
> π-clearing ladder is never needed on its roster: the canonical division by
> Φ_{m+1} alone discharges TC-3 there.”

**The two directions have different footprints, and the note separates them** — the obstruction direction (the one that matters for the fence) rides only in-note lemmas.

**RESOLUTION TRACE:** statement lines 861–924; §4.2 1747–1760 (`.88`); **correction sites 2890–2911 (Annex #5)**, 314–319 (r3/G-1, shard 1 `.22`), 289–296 (r4/G-3, shard 1 `.19`), 256–259 (r5/m-1, shard 1 `.15`).

**TEETH:** **MJ1** — the tooth “TC-3 is never load-bearing”: **333 tested, 103 firings, and ALL 103 lie in the `δ ≥ g_m` load set; 0 anomalies in either direction — JC-LOAD's dichotomy machine-confirmed BOTH WAYS.** Plus the instrument's own **0/29 set-mismatches over 134/669 pairs.** Disposition: **planted mutant confirming an iff in both directions** — the strongest tooth design in this note.

---
### EFF.GRTJC.63  [lemma]  ★ COROLLARY JC-PSIKER — TC-3 is not a relabeling (and the r1/F2 re-quantification)

**CANONICAL STATEMENT:** verbatim, lines 928–990 — the witness, the struck over-quantified sentence, the `[r1, F2]` three-clause replacement, the machine record and the proof.
**FORM:** bold-headed corollary with a fixed-width three-clause conclusion.

> “*Statement.* At every stage the level-NR read is **non-injective on a graded
> piece**: with λ := wΦ_{NR} = e_mg_mγ_{m+1},
>
>     𝑅_λ(Φ_{m+1}) = ψ_m(y) ≠ 0   in K_m[y],  but  read(λ, Φ_{m+1}) = ψ_m(z̄) = 0,
>
> so in(Φ_{m+1}) ≠ 0 in gr_λ lies in the kernel of the read; and (when λ ∈ W, so
> that the anchor φ_λ exists — otherwise use the π-translate) Φ_{m+1} + φ_λ and
> φ_λ are two elements of gr_λ with equal reads and different classes. ~~Hence
> TC-3 has a nonzero kernel on every graded piece (namely ψ_m·Δ under the anchor
> coordinate) and **cannot be a relabeling of scalars.**~~”

**The `[r1, F2]` replacement, verbatim (lines 939–961):**

> “**[r1, F2 — CRITICAL (PE1): that closing sentence is OVER-QUANTIFIED, and is
> replaced by the exact range. The witness above is UNCHANGED and correct.]**
> PE1's finding, in one line: `𝔦 := in(Φ_{m+1})·gr(w)` is homogeneous with a
> single generator of degree wΦ_NR, so its degree-λ part is
> `𝔦 ∩ gr_λ = in(Φ_{m+1})·gr_{λ−wΦ_NR}`, and weights are ≥ 0 on O[x] — hence the
> kernel is **ZERO whenever λ < wΦ_NR**, which is the case at the window base G0
> on **29/29 roster rows** … The corrected statement, in three clauses:
>
>     (i)   [WITNESS — unchanged, PROVED] at λ = wΦ_NR the display above holds:
>           𝑅_λ(Φ_{m+1}) = ψ_m(y) ≠ 0 while read(λ,Φ_{m+1}) = ψ_m(z̄) = 0.
>     (ii)  [EXACT RANGE on gr] for λ ∈ W, 𝔦 ∩ gr_λ = in(Φ_{m+1})·gr_{λ−wΦ_NR},
>           which is ZERO for every λ < wΦ_NR and NONZERO for every
>           λ ∈ wΦ_NR + W (the anchor φ_{λ−wΦ_NR} supplies the element, and
>           gr(w) is a domain).  Under the note's standing convention that
>           gr_γ = 0 off the window (JC-BOX-7) the range is exactly
>           W ∩ (wΦ_NR + W).
>     (iii) [THE FORM §2.10 CONSUMES — PROVED] after TC-1 the kernel is nonzero on
>           EVERY graded piece: 𝔦^B ∩ B_n = in(Φ_{m+1})·B_{n−wΦ_NR} ≅ ψ_m(y)·Δ
>           ≠ 0 for every n ∈ ℤ, because in(π) is a unit in B and hence
>           B_j ≅ B_{j+E} for all j — no piece of B is zero.  So TC-3 **cannot be
>           a relabeling of scalars** on the object TC-3 is actually applied to.”

**SUPERSESSION KIND:** `counter re-reading` — a universal generalization refuted and replaced by an exact range.

**★ WHY THE CRITICAL COST NOTHING, and the note verifies it:** “Nothing downstream used the refuted universal form on gr: §2.10 [r1, F1] now states and consumes (iii). **W-6(v)'s own wording (‘the level-NR read is non-injective on a graded piece, with the classifier's own next key Φ_{m+1} as the kernel witness’) was already correct as written and stands unamended.**”

**CONDITIONALITY:** Clause (ii)'s range uses the standing convention `gr_γ = 0` off the window (JC-BOX-7). **Clause (iii) is the form the coordinate calculus consumes and it is TRUE on `B` for a structural reason — `in(π)` is a unit, so no piece of `B` is zero.**

**DERIVATION:** Displayed (lines 975–981). `Φ_{m+1} = Φ_m^{e_mg_m} + Σ_{k<g_m}C_kΦ_m^{e_mk}` with `w(C_kΦ_m^{e_mk}) = λ` for every `k` with `ψ_{m,k} ≠ 0` (REALIZE's construction of `C_k` at weight `(g_m−k)γ_{m+1}`) — **“that is the defining property of the key polynomial: all its terms sit on the λ-line, its slot digits are the coefficients of `ψ_m`, and `w(Φ_{m+1}) = λ` exactly.”** So `𝑅_λ(Φ_{m+1}) = ψ_m(y) ≠ 0` while its evaluation at `z̄` is `ψ_m(z̄) = 0`.

**★ INSTRUMENT CORROBORATION FROM THE OTHER SIDE (lines 983–987):** “the build-phase disclosure that the naive class identity `[π·Λ_N(c)] = [Λ_{N+E}(c)]` is **FALSE** — two weight-`(N+E)` lifts with the same read need not be the same class — is the same phenomenon measured from the other side, and is why the instrument's offset clause (P2-OFF, 0/116) is stated on the CONSTANTS.”

**RESOLUTION TRACE:** statement lines 928–990; the disposition 378–384 (r1/F2, shard 1 `.32`); the consumed form 1354–1396 (`.20`); JC-BOX-7 2049–2056 (shard 3).

**TEETH:** **JC6** (116 samples: `w(Φ_{m+1}) == wΦ_NR`, `𝑅(Φ_{m+1}) == ψ_m` coefficientwise, `read == 0`, and the equal-read/different-class pair) + tooth **MJ4** (“the read is injective on `gr_λ`”, **29 firings — fired on every row**) + **R1-PSIK-LO** (197 window lines below `wΦ_NR`, no class certified dead — **with the certifier's one-sidedness disclosed**, JC-BOX-8(ii)) + **R1-PSIK-HI** (197 residue classes with a certified nonzero witness) + tooth **T1** (the refuted universal claim, **29/29 firings**).

---
### EFF.GRTJC.64  [supplier-finding]  ★★ §2.10 — the struck `(COORD)` and WHY it is false

**CANONICAL STATEMENT:** verbatim, lines 992–1035 — the section head, the struck r0 display, the slot-bound refutation, and the “why the literature is NOT at fault” paragraph.
**FORM:** display (an H3 head) + a struck blockquote + two bold-headed paragraphs.

> “## 2.10 [r1, F1] What TC-3 IS in this note, and WHERE the coordinate calculus lives (the post-TC-1 pieces B_n)
>
> **[r1, F1 — CRITICAL (PE1). The r0 text stated the coordinate calculus on
> gr_λ(w), where it is FALSE; it is restated here on this note's own B_n, where it
> is proved. The struck r0 wording, verbatim:]**
>
> > ~~Two facts fix the coordinate calculus used from here on. Both are named
> > inputs, not new claims.~~
> >
> > ~~**(COORD)** For λ ∈ W the digit map 𝑅_λ : gr_λ(w) → Δ := K_m[y] is a
> > K_m-linear **isomorphism**, carrying in(φ_λ) to a nonzero constant
> > a_λ ∈ K_m^* (JC-ANCHMON(c)). Injectivity is definitional (§1: 𝑅_λ(f) = 0 ⟺
> > w(f) > λ); surjectivity/rank-one is (IN-3)(c) — FGMN Thm 4.2's freeness of
> > gr_λ over Δ on the anchor basis.~~
>
> **Why the r0 statement is false (the slot bound).** §1's ambient ring is O[x]:
> w_0 is the coefficientwise π-valuation on INTEGRAL polynomials, and the window
> W = {γ : u_1(γ) ≥ 0} together with the anchors φ_γ = π^{u_1}∏Φ_j^{s_{j+1}} exist
> precisely to keep the π-exponent ≥ 0. Hence every Φ_m-digit A_a of an f in the
> ring has w_m(A_a) ≥ 0, so an on-line abscissa at level λ satisfies
> e_m·w_m(A_a) + a·γ_{m+1} = λ with w_m(A_a) ≥ 0, i.e. a·γ_{m+1} ≤ λ. Writing
>
>     maxslot(λ) := ⌊(⌊λ/γ_{m+1}⌋ − s_NR(λ))/e_m⌋,
>
> the on-line slot set at λ is contained in {0,…,maxslot(λ)}: **gr_λ is a
> FINITE-dimensional K_m-space**, 𝑅_λ is NOT onto K_m[y], and
> gr_λ/(𝔦 ∩ gr_λ) is not a 1-dimensional K-space. At this note's own window base
> maxslot(G0) = **0 on 29/29 roster rows** (r1 family R1-BND; PE1 §CRITICAL 1
> measured the same, and sampled 3,072 integral f with w(f) = 4 on row C2I —
> m = 1, E = 4, g_m = 2, e_m = 2, γ_{m+1} = 5, wΦ_NR = 20, G0 = 4 — finding slot
> set {0} throughout and 𝔦 ∩ gr_4 = 0, so gr_4 ≅ K_m while [K:K_m] = g_m = 2).
>
> **Why the literature is NOT at fault, and where the repair lives.** FGMN's
> Δ ≅ K_m[y] is the degree-0 part of the graded algebra of a MacLane valuation on
> **K[x]** — π INVERTED — and that object is exactly what JC-DOM (§2.1) builds one
> page earlier: `B := gr(w)[in(π)^{-1}]`, `B_n = ∪_{k≥0}in(π)^{-k}gr_{n+kE}`. So
> the coordinate calculus — (COORD-B)/(MULT-B) below — and TC-3 belong strictly
> AFTER TC-1, on B **[r2, G-4: this sentence formerly named the struck
> (COORD)/(MULT) here]**. Four lemmas do it. Note
> that this makes the note's literature footprint SMALLER, not larger: the
> surjectivity half becomes a theorem of this note (JC-BSURJ, from REALIZE-(m)),
> and the only cited input left in the coordinate calculus is the multiplicativity
> (DMULT) **[r2, G-1: in its citable tier (DMULT-w); the exact tier (DMULT-s) is
> MEASURED, not cited — see the split below]**.”

**SUPERSESSION KIND:** `replacement` — a false display struck and the calculus re-based.

**★ THE THREE-PART SHAPE A CHAPTER CUT MUST CARRY, and it is unusually clean:**
1. **What is false and why:** the ambient ring is `O[x]`, so `w_0 ≥ 0`, so `a·γ_{m+1} ≤ λ` and `gr_λ` is FINITE-dimensional with the explicit bound `maxslot(λ)`. **`𝑅_λ` is NOT onto `K_m[y]`.**
2. **Why the literature is not at fault:** FGMN's `Δ ≅ K_m[y]` is about `K[x]` with `π` INVERTED — **which is exactly the object JC-DOM had already built one page earlier.** The defect was transport, not truth.
3. **The repair SHRINKS the footprint:** JC-BSURJ PROVES the surjectivity half that r0 cited, leaving `(DMULT)` as the only cited input — and even that becomes DERIVED at Annex #6.

**CONDITIONALITY:** The refutation is measured, not merely argued: **`maxslot(G0) = 0` on 29/29 roster rows**, with PE1's independent sampling on row C2I (3,072 integral `f` with `w(f) = 4`; slot set `{0}` throughout; `𝔦 ∩ gr_4 = 0`; so `gr_4 ≅ K_m` while `[K:K_m] = g_m = 2`).

**DERIVATION:** Displayed in full above.

**RESOLUTION TRACE:** statement lines 992–1035; the four repair lemmas 1037–1172 (`.65`–`.67`); the disposition 359–377 (r1/F1, shard 1 `.31`); the object 614–619 (shard 1 `.48`).

**TEETH:** **R1-BND** — “the slot bound: `maxslot(G0) == 0`”, **29 samples, 0 violations, 0 on 29/29 rows**, with the ladder census `maxslot(G0+kE)`, `k = 0..3`, showing the growth that makes `B_n ⊋ gr_n` (e.g. C2A `[0,0,1,1]`, C2D `[0,1,1,1]`, I4C `[0,0,0,0]` — “slower but unbounded”). Plus tooth **T2** (“no k-shift needed”, **29/29 firings**). **A refutation converted into a permanent scored regression.**

---
### EFF.GRTJC.65  [lemma]  ★ LEMMA JC-LOC — B *is* the object FGMN's theorems speak about

**CANONICAL STATEMENT:** verbatim, lines 1037–1104 — the lemma, its proof with the `[r2, G-6]` additivity supplement, and the three-step `[r2, G-6]` identification with its honest residue.
**FORM:** bold-headed lemma + a fixed-width three-step derivation.

> “**LEMMA JC-LOC [r1] (B *is* the object FGMN's theorems speak about).** Write
> gr^O(w) for §1's graded ring (built on O[x]) and gr^K(w) for the same
> construction on K[x] = O[x][π^{-1}], with w extended by w(π^{-k}g) := w(g) − kE.
> Then the degreewise map
>
>     B = gr^O(w)[in(π)^{-1}] → gr^K(w),   in(π)^{-k}·in(g) ↦ in(π^{-k}g),
>
> is an isomorphism of ℤ-graded rings. In particular B_n ≅ gr^K_n(w) for every
> n ∈ ℤ, and B_0 ≅ the degree-0 subring of gr^K(w).”

**The three-step identification, verbatim (lines 1071–1091):**

>     (G6-1) THE EXTENSION IS FORCED.  Every f ∈ K[x] is π^{-k}g with g ∈ O[x],
>            and any valuation w^K on K[x] restricting to w with w^K(π) = E
>            (JC-DOM) must satisfy w^K(π^{-k}g) = w(g) − kE.  Well-defined: if
>            π^{-k}g = π^{-k′}g′ (k′ ≥ k) then g′ = π^{k′−k}g, and w(πf) =
>            w(π) + w(f) ((IN-3)(a)) gives w(g′) − k′E = w(g) − kE.  So there is
>            exactly ONE candidate, the displayed one.
>     (G6-2) §1's MIN-FORMULA COMPUTES IT ON ALL OF K[x] … So gr^K(w) is the graded ring of the MacLane
>            min-formula valuation on K[x] — the object of FGMN's graded package
>            — not of an ad-hoc extension.
>     (G6-3) IT IS A VALUATION.  Multiplicative: … Ultrametric: …

**★ THE HONEST RESIDUE, verbatim (lines 1092–1099) — and it is the sentence that keeps the note's conditionality straight:**

> “*Honest residue of this derivation (unchanged input, not a new one).* Steps
> G6-1..3 identify the extension with **the min-formula valuation on K[x] in the
> harness normalization**. The remaining tie — that §1's recursion (the harness
> w = w_{m+1}, sheared frame) is the literature's inductive valuation v_{m+1},
> and 𝑅 its residual-polynomial operator up to the line-wise unit — is exactly
> **(IN-3)'s W-1 transport clause, already priced in §0's stack** (and the
> subject of the open dictionary TR-3′-GEN quoted at [r2, G-1] below). G-6 adds
> no new conditionality; it removes the "same construction" hand-wave.”

**SUPERSESSION KIND:** `inventory completion` (r2/G-6 supplies a derivation for a phrase that had been asserted) — **explicitly NOT a new conditionality.**

**CONDITIONALITY:** **The remaining tie is W-1 (J-A) at ATTEMPT grade**, and the note says so rather than absorbing it. **TR-3′-GEN is OPEN** — the same fact that forces the `(DMULT-w)`/`(DMULT-s)` split (`.69`).

**DERIVATION:** The isomorphism's four properties are displayed (well-defined, graded+multiplicative, surjective in degree `n`, injective), **plus the `[r2, G-6]` additivity supplement** — “previously unchecked (needed because homogeneous elements are `in(f)` or 0, and sums can drop degree)”, resolved by bringing two degree-`n` elements to a common denominator and checking the same dichotomy on both sides.

**RESOLUTION TRACE:** statement lines 1037–1104; the disposition 473–478 (r2/G-6, shard 1 `.38`); consumed at `.15`, `.16`, `.20`, `.27`; the box 1960–1992 (JC-BOX-3, shard 3).

XREF: `docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt` — **file EXISTS**; the standing setting at **line 137** re-read EXACT (shard 1 `.43`).

**TEETH:** **PE2 re-derived JC-LOC hostilely and independently and found no false statement.** No battery keys a ring isomorphism; disposition **AUDIT — in-house hostile pass** plus the indirect evidence of every family that computes in `B`.

---
### EFF.GRTJC.66  [lemma]  LEMMA JC-PIINV — π-equivariance, and why ρ is the right coordinate

**CANONICAL STATEMENT:** verbatim, lines 1106–1143 (lemma, proof, machine).
**FORM:** bold-headed lemma with a three-part conclusion.

> “**LEMMA JC-PIINV [r1] (the digit polynomial is π-equivariant; the colimit
> coordinate is well defined).** For every λ ∈ ℤ and every f ∈ O[x] with
> w(f) ≥ λ:
>
>     (a) the on-line abscissas and slot indices at (λ+E, πf) are exactly those
>         at (λ, f);
>     (b) there is a constant c_π ∈ K_m^*, depending only on T, with
>         𝑅_{λ+E}(π f) = c_π·𝑅_λ(f);
>     (c) hence, with ρ_λ := 𝑅_λ/a_λ and a_λ := 𝑅_λ(φ_λ) ∈ K_m^* (JC-ANCHMON(c)),
>         ρ_{λ+E}(π f) = ρ_λ(f)  EXACTLY, for λ, λ+E ∈ W.”

**★ CLAUSE (c) IS WHY THE NORMALIZATION EXISTS, and the machine proves it is not cosmetic.** *Machine* (lines 1135–1143): the measured roster value set is **`c_π ∈ {1, z̄, z̄², z̄³, z̄⁴, z̄⁶, z̄⁸}` — 1 on 9 rows, `z̄` on 9, `z̄²` on 7, and `z̄³/z̄⁴/z̄⁶/z̄⁸` on the single rows C2G/C3H/C2H/I4C** — “a nontrivial constant, which is exactly why the ρ-normalization is the one that makes the colimit well defined”. **r1's own finding 3: “`c_π ≠ 1` on 20 of 29 rows. The colimit coordinate would NOT be well defined in the un-normalized `𝑅`.”**

**CONDITIONALITY:** **The r0 text quoted a 6-row SMOKE value set `{1, z̄, z̄²}` and labelled it “across the roster”** — corrected at r2/G-3 (shard 1 `.38`) to the as-of-r1 roster value set from the committed artifact. **A stale smoke figure presented as a roster figure.**

**DERIVATION:** Displayed (lines 1117–1133). (a) `deg(πA) = deg A`, so the development of `πf` is that of `f` multiplied coefficientwise; `w_m(πA) = w_m(A) + E/e_m` and `s_NR(λ+E) = s_NR(λ)`, so the on-line condition and the slot index are unchanged. (b) only the digit VALUES move, and two inductions down the levels show both corrections are independent of the slot and of `β`, so the whole digit polynomial is multiplied by one constant `c_π := δ_m·c^{(m)}`. (c) JC-PER gives `φ_{λ+E} = π·φ_λ` byte-for-byte, so `a_{λ+E} = c_π·a_λ` and `c_π` cancels.

**RESOLUTION TRACE:** statement lines 1106–1143; the disposition 461–463 (r2/G-3, shard 1 `.38`); consumed at `.15` (well-definedness of `ρ^B`), `.17` (the `κ = 1` pinning), `.18` ((G5-ii)).

**TEETH:** **R1-PER** — “`𝑅_{λ+kE}(π^kf) == c_π^k·𝑅_λ(f)` with ONE `c_π` per row (independent of `f`, `λ`, slot, `k`), and `ρ_{λ+kE}(π^kf) == ρ_λ(f)` EXACTLY, `k = 1,2`” — **841 samples, 0 violations, every row**; plus tooth **T5** (“mutated JC-PIINV `ρ_{λ+E}(πf) == y·ρ_λ(f)`”, **406 firings**).

---
### EFF.GRTJC.67  [lemma]  LEMMA JC-BSURJ — the colimit coordinate is ONTO Δ (proved, not cited)

**CANONICAL STATEMENT:** verbatim, lines 1145–1172 (lemma, proof, machine).
**FORM:** bold-headed lemma.

> “**LEMMA JC-BSURJ [r1] (the colimit coordinate is ONTO Δ — proved, not cited).**
> Fix n ∈ W and p = Σ_{j≤d}c_jy^j ∈ Δ = K_m[y]. For every k with
>
>     (n + kE) − (s_NR(n) + d·e_m)·γ_{m+1}  ≥  e_m·wΦ_m
>
> there is an INTEGRAL f with w(f) = n+kE and 𝑅_{n+kE}(f) = p on the nose; only
> finitely many k are excluded. Hence ρ^B_n := colim_k ρ_{n+kE} : B_n → Δ is
> SURJECTIVE, while ρ_n itself is not (its image has degree ≤ maxslot(n), which is
> 0 at every roster row's base).”

**★ “PROVED, NOT CITED” IS THE POINT — this is the half r0 had cited from FGMN and r1 proves in-note, which is why the repair SHRINKS the literature footprint.**

**CONDITIONALITY:** **SUPERSEDED IN QUANTIFIER BY ANNEX #8** (shard 3, L3034–3035): “The same zero convention repairs JC-BSURJ: for every **nonzero** `p = Σ_{j≤d}c_jy^j`, its displayed REALIZE construction produces an integral `f` with `w(f) = n+kE` and `𝑅_{n+kE}(f) = p`. **For `p = 0`, surjectivity uses the zero element of `B_n`; no exact finite-weight representative is asserted.** Thus `ρ_n^B : B_n → Δ` **remains surjective**.” **SUPERSESSION KIND: `partial-withdrawal`** — the construction's quantifier narrows, the surjectivity conclusion survives.

**DERIVATION:** Displayed (lines 1155–1166), and it is constructive. Put `λ := n+kE`, `s := s_NR(λ) = s_NR(n)`, `a_j := s + j·e_m`, `β_j := (λ − a_jγ_{m+1})/e_m`. **Each `β_j` is an INTEGER** (shown by a congruence: `γ_{m+1} ≡ h_m` and `λ ≡ s·h_m (mod e_m)`). The displayed inequality is `β_d ≥ wΦ_m`, and `β_j` decreases in `j`, so REALIZE-(m) supplies `A_j := realize(m, ε_m(β_j)^{-1}c_j, β_j)` with `deg A_j < deg Φ_m`. Put `f := Σ_j A_jΦ_m^{a_j}` — **since `deg A_j < deg Φ_m` this IS the `Φ_m`-development**, so `w(f) = λ` and the slot-`j` digit is `c_j`.

**RESOLUTION TRACE:** statement lines 1145–1172; **correction site 3034–3035 (Annex #8, shard 3)**; consumed at `.68`, `.69`, `.82`.

XREF: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md:REALIZE` — count **17** · `S4.1` — count **35**.

**TEETH:** **R1-SURJ** — “for targets `p` of y-degree 0,1,2 the REALIZE construction at the predicted `k` gives integral `f` with `w(f) == n+kE` and `𝑅(f) == p` ON THE NOSE; the minimal `k` is censused” — **841 samples, 0 violations**, with the census showing **degree 0 at `k = 0` on 28 rows (`k = 2` on C4H), degree 1 at `k = 2..16`, degree 2 at `k = 5..34` — “the k-shift is structural, not a convenience”**. Plus tooth **T2** (29/29).

---
### EFF.GRTJC.68  [definition]  ★ (COORD-B) — the repaired coordinate calculus

**CANONICAL STATEMENT:** verbatim, lines 1174–1186.
**FORM:** bold-headed named display with a fixed-width two-part conclusion.

> “**(COORD-B) [r1 — REPLACES (COORD)].** Fix ν ∈ ℤ/E and n ∈ W with n ≡ ν (mod E);
> Δ := K_m[y].
>
>     (1) [PROVED at general m, in this note]  ρ^B_n : B_n → Δ,
>         in(π)^{-k}α ↦ ρ_{n+kE}(α), is a well-defined (JC-PIINV(c)), injective
>         (§1: 𝑅_λ(f) = 0 ⟺ w(f) > λ, compatibly along the system) and surjective
>         (JC-BSURJ) K_m-linear map, with ρ^B_n(in φ_n) = 1.  Moreover in(π) is a
>         unit in B of degree E, so B_j ≅ B_{j+E} for EVERY j ∈ ℤ: after TC-1 no
>         graded piece is zero and the window restriction disappears.
>     (2) [PROVED at general m from (1) + (DMULT-w) — the CITABLE tier suffices,
>         [r2, G-1]]  B_0 ≅ Δ as K_m-ALGEBRAS via
>         ρ^B_0, and B_n is FREE OF RANK ONE over B_0 ≅ Δ on in(φ_n), with ρ^B_n
>         the coordinate of that module structure.”

**★ THE TWO CLAUSES HAVE DIFFERENT FOOTPRINTS AND THE NOTE SEPARATES THEM SHARPLY:** **(1) is PROVED IN-NOTE with no literature input at all** (JC-PIINV + §1's injectivity + JC-BSURJ); **(2) needs `(DMULT-w)` — the citable tier — and nothing more.** **“after TC-1 no graded piece is zero and the window restriction disappears”** is what makes the all-of-`ℤ` quantifiers of `.71` and `.73` possible.

**SUPERSESSION KIND:** `replacement` — it REPLACES the struck `(COORD)`.

**CONDITIONALITY:** (2) rides `(DMULT-w)`, which **Annex #6 later DERIVES rather than cites** — so at HEAD (COORD-B)(2) rests on a derivation from the PDF-verified rank-one theorem, not on a quoted product law. **Annex #6's consumer sweep says exactly this: “(COORD-B)(2) survives at every `m`, now directly from JC-RANKMULT rather than from an unquoted product law.”**

**DERIVATION:** (1) from JC-PIINV(c) (well-defined), §1's injectivity, JC-BSURJ (surjective). (2) is `.70`.

**RESOLUTION TRACE:** statement lines 1174–1186; the proof of (2) 1269–1285 (`.70`); the four supporting lemmas 1037–1172; **Annex #6 at 2917–3000 (shard 3)**.

**TEETH:** R1-SURJ, R1-INJ, R1-PER (all GREEN); the Δ-module half is measured in its equivalent digit form by **R1-DMULT** and **R1-COB**.

---
### EFF.GRTJC.69  [hypothesis]  ★★ (DMULT) AND ITS TWO TIERS — the note's signature honesty move

**CANONICAL STATEMENT:** verbatim, lines 1188–1267 — the (DMULT) display with its `[r2, G-1]` split header, the (DMULT-w) tier with its displayed derivation, the (DMULT-s) tier with its reportable citation failure, and the consumer split.
**FORM:** bold-headed named displays.

> “**(DMULT) [r1 — the one cited input of the coordinate calculus] [r2, G-1 —
> SPLIT INTO TWO HONEST TIERS; the r1 status line is struck below].** For
> f,g ∈ O[x] with λ := w(f), μ := w(g):
>
>     𝑅_{λ+μ}(fg) = y^{δ(λ,μ)}·𝑅_λ(f)·𝑅_μ(g),
>     δ(λ,μ) := (s_NR(λ) + s_NR(μ) − s_NR(λ+μ))/e_m ∈ {0,1}.
>
> This is the composite-stage form of (IN-2)'s (W-MULT) … and of Montes/FGMN residual-polynomial multiplicativity; via
> JC-LOC it is the content of (IN-3)(c) on the object (IN-3)(c) is about. ~~It is
> **CITED, not proved here**~~ **[r2, G-1: PE2 caught that r1 labelled the EXACT
> (multiplier-1) display "CITED" while §0's own transport statement can only
> deliver it up to a line-wise unit — and simultaneously called the exactness "a
> finding of the r1 battery". The honest form is two tiers:]**
>
> **(DMULT-w) [the citable tier — DERIVED from the citation + §0's transport].**
> There is a unit ω(λ,μ) ∈ K_m^*, independent of f and g, with
>
>     𝑅_{λ+μ}(fg) = ω(λ,μ)·y^{δ(λ,μ)}·𝑅_λ(f)·𝑅_μ(g).
>
> *Derivation (displayed, the step r1 skipped).* The literature identity is
> stated for the FGMN operator R^{GMN}; (IN-3)'s transport clause is
> 𝑅_λ = c_λ·R^{GMN}_λ with c_λ a LINE-WISE unit (W-1). Substituting,
>
>     𝑅_{λ+μ}(fg) = c_{λ+μ}·R^{GMN}_{λ+μ}(fg)
>                 = c_{λ+μ}·y^δ·R^{GMN}_λ(f)·R^{GMN}_μ(g)
>                 = (c_{λ+μ}/(c_λc_μ))·y^δ·𝑅_λ(f)·𝑅_μ(g),
>
> so ω(λ,μ) = c_{λ+μ}/(c_λc_μ) — the 2-coboundary of the line-wise unit system.
> That ω depends only on the lines is what the transport gives; **nothing gives
> ω ≡ 1.**
>
> **(DMULT-s) [the exact tier — MEASURED, NOT CITED].** ω(λ,μ) ≡ 1 … *Status:* **MEASURED**
> (R1-DMULT 2,784/0 with tooth T3; §9.3 finding 1 "multiplier exactly 1"; r2's
> bilinear leg R2-BIL/R2-PHI, §9.4) and **not cited**: the r2 attempt to locate
> a multiplier-1 statement for the harness 𝑅 in the sources the note names
> FAILED reportably … So no
> corpus-pinned citation delivers ω ≡ 1; proving it would mean proving the
> ε-kit's unit system multiplicative (c_{λ+μ} = c_λc_μ), which this note does
> not do. The standing printed-source Codex leg (JC-BOX-3 item 2) rides
> unchanged.”

**Double-emission (rule 14) — the two tiers as a `[TABLE]` with their status at HEAD:**

| tier | statement | status as written | who rides it | status at HEAD |
|---|---|---|---|---|
| **(DMULT-w)** | `𝑅_{λ+μ}(fg) = ω(λ,μ)·y^{δ}·𝑅_λ(f)·𝑅_μ(g)`, `ω(λ,μ) ∈ K_m^*` depending only on the lines | **DERIVED** from the citation + §0's transport (derivation displayed) | **(COORD-B)(2), (MULT-B), JC-CARRY-m, W-8, JC-BOX-4's corner closure — everything load-bearing** | **DERIVED from Thm 4.2's rank-one freeness via LEMMA JC-RANKMULT (Annex #6); the “quoted product identity” claim WITHDRAWN** |
| **(DMULT-s)** | `ω ≡ 1` | **MEASURED, NOT CITED** — the citation attempt FAILED reportably | **only JC-COB's sharp `u = a_γa_{γ′}`** (and its §4.1 restatement) | **PROVED-conditional on the measured perimeter ([ILN]† scored stratum, `m ≥ 1`, `e_m ≥ 2`) by DULEMMA THEOREM DU (Annex #1); `e_m = 1` stays measured, off-stratum pairs stay open** |

**★ THE CONSUMER SPLIT, verbatim (lines 1249–1260) — the paragraph that makes the tiering load-bearing rather than decorative:**

> “**Who consumes which tier (checked by PE2, GAP 1 blast radius).** (COORD-B)(2),
> (MULT-B), JC-CARRY-m, W-8 and JC-BOX-4's [r1] corner closure need only
> **(DMULT-w)**, and the mechanism is one line: the normalized coordinate
> ρ_λ = 𝑅_λ/a_λ with a_λ = 𝑅_λ(φ_λ) is **invariant under ANY line-wise
> rescaling of 𝑅** (the unit c_λ cancels between numerator and denominator), so
> the whole ρ-calculus can be run in the R^{GMN} gauge, where the cited identity
> is exact; equivalently, ω is absorbed into the anchor cocycle A(λ,μ), and the
> monomial-shape/degree-δ statements are ω-blind. Riding **(DMULT-s)** and
> downgraded with it: COROLLARY JC-COB's sharp value u = a_γa_{γ′} FOR THE
> HARNESS constants a (and its §4.1 restatement and second half) — on (DMULT-w)
> alone it degrades to JC-SPAN's already-proved u ∈ K_m^*. **No clause GRADE
> changes between tiers.**”

**CHAIN (rule 25) — FIVE layers. `CHAIN HOME: .43`; this unit is body site B.** r0 CITED on `gr` → r1/F1 re-based on `B`, reduced to `(DMULT)` → **r2/G-1 SPLIT (this unit)** → Annex #1 `(DMULT-s)` PROVED-conditional → **Annex #6 `(DMULT-w)` WITHDRAWN-as-citation and DERIVED. TERMINAL = Annex #6 + Annex #1.**

**★ THE WELD-AUDIT ROW, verified:** `runs/qgen/WELD_FACE_AUDIT.md` L106 records that **the one reachable GRTJC weld face, COROLLARY W-9, rides the CITABLE tier**, and quotes this note's own blast-radius sentence (JC-BOX-3 item 3, shard 3): *“If **(DMULT-w)** failed at composite order, (COORD-B)(2), (MULT-B), §§2.7–3.4, **W-8 and W-9 fail together**; if only **(DMULT-s)** failed (ω ≢ 1), JC-COB's sharp values and R1-COB's exact predicate fail while **the structural clauses stand**.”* **Consistent with this unit's consumer split; verified by this compiler against both sources.**

**CONDITIONALITY:** **The citation failure is REPORTED, not hidden** — `(IN-3)`'s transport prices `𝑅 = c·R^{GMN}` at a line-wise unit, and **TR-3′-GEN is OPEN beyond its closed strata** (with its closed-scope gloss itself corrected at r3/G-6, shard 1 `.27`).

**DERIVATION:** The `(DMULT-w)` derivation is displayed in full above. **`(DMULT-s)` has no derivation in this note** — that is the whole point of the tier.

**RESOLUTION TRACE:** statement lines 1188–1267; the disposition 434–447 (r2/G-1, shard 1 `.36`); **Annex #1 at 2805, Annex #6 at 2917–3000 (shard 3)**; the box 1960–1992 (JC-BOX-3, shard 3).

XREF: `lean/notes/openmath/GRB_ORDER2_2026-08-05.md:TR-3′-GEN` — count **57** · `S3.4` — count **25**. `lean/notes/openmath/DULEMMA_PROOF_2026-08-08.md` — **file EXISTS**.

**TEETH:** **(DMULT-s)** is measured by **R1-DMULT** (2,784/0, exact multiplier 1) with tooth **T3** (1,392 firings), and by **R2-BIL/R2-PHI** (261 dense bilinear pairs + the r1-skipped pair on 29/29) with teeth **U1/U2** (261/261 each). **(DMULT-w)** carries no separate leg. **Disposition: the exact tier is the measured one and the citable tier is the derived one — an unusual and honest inversion.**

---
### EFF.GRTJC.70  [lemma]  the proof of (COORD-B)(2), and the κ = 1 pinning

**CANONICAL STATEMENT:** verbatim, lines 1269–1285.
**FORM:** `*Proof of (2) …*` block.

> “*Proof of (2) from (1) + (DMULT-w) [r2, G-1 — re-run on the citable tier].*
> Represent t ∈ B_0 at a line kE (so
> s_NR(kE) = 0, JC-FIB) and β ∈ B_n at a line n+k′E. Then δ(kE, n+k′E) = 0, so
> (DMULT-w) gives 𝑅(tβ) = ω·𝑅(t)𝑅(β) with ω = ω(kE, n+k′E) depending on the
> LINES only; dividing by the anchor constants this reads
> ρ^B_n(tβ) = κ·ρ^B_0(t)·ρ^B_n(β) with κ := ω·a_{kE}a_{n+k′E}/a_{n+(k+k′)E},
> again line-dependent only. **The in-note lemmas pin κ = 1** [r2, G-1]: take
> t = in(φ_{kE}) = in(π^k) (the anchor at line kE, JC-PER); then
> ρ^B_0(t) = 1 and ρ^B_n(π^kβ) = ρ^B_n(β) EXACTLY by JC-PIINV(c) (proved, not
> cited), so κ·1·ρ^B_n(β) = ρ^B_n(β) for a β with ρ^B_n(β) ≠ 0 forces κ = 1 —
> for every representative line pair, since κ never saw t or β. Hence
> ρ^B_n(tβ) = ρ^B_0(t)·ρ^B_n(β) for the B_0-action on B_n and, at n = 0,
> multiplicativity of ρ^B_0 (using a_0 = 𝑅_0(φ_0) = 1, φ_0 = 1, 0 ∈ W). So
> ρ^B_0 : B_0 → Δ is a bijective K_m-algebra map
> (bijective by (1)), and for β ∈ B_n the element t ∈ B_0 with ρ^B_0(t) = ρ^B_n(β)
> satisfies ρ^B_n(t·in φ_n) = ρ^B_0(t)·1 = ρ^B_n(β), hence β = t·in φ_n by
> injectivity: B_n = Δ·in(φ_n), free of rank one because ρ^B_n is injective. ∎”

**★ THE `κ = 1` PINNING IS THE STEP THAT MAKES THE WEAK TIER SUFFICE**, and it is done with IN-NOTE lemmas only: `ρ^B` is invariant under any line-wise rescaling (JC-PIINV(c), **proved, not cited**), so the unknown unit `ω` is pinned away by evaluating at `t = in(π^k)`. **This is the mechanism the consumer split at `.69` refers to as “one line”.**

**CONDITIONALITY:** Rides `(DMULT-w)` only. **PE3 re-derived “the κ = 1 pinning” and found it SOUND** (shard 1 `.21`).

**DERIVATION:** Displayed in full above.

**RESOLUTION TRACE:** statement lines 1269–1285; the statement 1174–1186 (`.68`); the tier 1203–1218 (`.69`).

**TEETH:** the module structure is measured in its digit form by R1-DMULT / R1-COB / R2-BIL.

---
### EFF.GRTJC.71  [definition]  (MULT-B) — the anchor cocycle, and the all-of-ℤ transport

**CANONICAL STATEMENT:** verbatim, lines 1287–1333 — the struck `(MULT)`, the `(MULT-B)` replacement, the `[r2, G-5]` virtual-anchor transport, the JC-SPAN consequence, the proof, and the `[r2, G-4]` gr-level restriction.
**FORM:** struck display + bold-headed named display + a fixed-width two-part transport.

> “~~**(MULT)** in(fg) = in(f)in(g) ((IN-3)(b)) plus (COORD) give a unique **anchor
> cocycle** A(λ,μ) ∈ Δ with ρ_{λ+μ}(αβ) = A(λ,μ)·ρ_λ(α)·ρ_μ(β) … for α ∈ gr_λ,
> β ∈ gr_μ, λ,μ,λ+μ ∈ W.~~
>
> **(MULT-B) [r1 — REPLACES (MULT); the object is B, and the input is the Δ-MODULE
> half, not mere K_m-linearity].** in(fg) = in(f)in(g) ((IN-3)(b)) plus
> (COORD-B)(2) give a unique **anchor cocycle** A(λ,μ) ∈ Δ with
>
>     ρ^B_{λ+μ}(αβ) = A(λ,μ)·ρ^B_λ(α)·ρ^B_μ(β),  A(λ,μ) = ρ^B_{λ+μ}(in φ_λ·in φ_μ),
>
> for α ∈ B_λ, β ∈ B_μ and **all λ,μ ∈ ℤ**.”

**The `[r2, G-5]` transport, verbatim (lines 1299–1315):**

>     (G5-i)  VIRTUAL ANCHOR.  For λ ∈ ℤ choose k ≥ 0 with λ+kE ∈ W (all large
>             k qualify) and set  in φ_λ := in(π)^{-k}·in(φ_{λ+kE}) ∈ B_λ.
>             k-independence: for k ≤ k′ with both lines in W, JC-PER gives
>             φ_{λ+k′E} = π^{k′−k}·φ_{λ+kE} byte-for-byte, so the two candidates
>             differ by in(π)^{-(k′−k)}in(π^{k′−k}) = 1 in B.
>     (G5-ii) ρ^B OFF THE WINDOW.  ρ^B_λ := ρ^B_{λ+kE} ∘ (in π)^k (multiply into
>             a window line, read there).  k-independence is exactly
>             JC-PIINV(c): ρ is π-invariant on the nose.

**And the consequence (lines 1315–1317):** “By JC-SPAN, `A(λ,μ) = (u/a_{λ+μ})·y^{δ(λ,μ)}` with `u ∈ K_m^*`, so **A is a MONOMIAL of y-degree exactly δ** (`e_m ≥ 2`).”

**★ THE PROOF NAMES THE STEP r0 SKIPPED, and it is a real distinction** (lines 1319–1325): “**This is the step the r0 text skipped**: a K_m-linear isomorphism `gr_λ ≅ Δ` transports the multiplication to *some* K_m-bilinear map `Δ × Δ → Δ`, and **only Δ-BILINEARITY — i.e. compatibility with the degree-0 action, (COORD-B)(2) — makes that map ‘multiply and scale by A(λ,μ)’.**”

**CONDITIONALITY:** `(MULT-B)` needs the **Δ-MODULE half**, not mere `K_m`-linearity — which is why `(COORD-B)(2)`, and hence `(DMULT-w)`, is load-bearing. **The all-of-ℤ quantifier is licensed by (G5-i)/(G5-ii), “not a parenthesis”** (r2/G-5). **The `[r2, G-4]` gr-level restriction (lines 1327–1333) is recorded ONCE so the proof bodies can cite it:** for `α ∈ gr_λ ⊆ B_λ`, `β ∈ gr_μ ⊆ B_μ`, `αβ ∈ gr_{λ+μ}` and `ρ^B_λ|_{gr_λ} = ρ_λ`, so `(MULT-B)|gr` reads `ρ_{λ+μ}(αβ) = A(λ,μ)ρ_λ(α)ρ_μ(β)` — **“the identity the proofs of §3.2, §4.1, §4.2 and §5 apply at gr level”**, and every site formerly invoking the struck `(MULT)` is re-pointed here.

**DERIVATION:** Displayed. The transport steps are each k-independent, with the reasons given (JC-PER for (G5-i), JC-PIINV(c) for (G5-ii)).

**RESOLUTION TRACE:** statement lines 1287–1333; the dispositions 470–472 (r2/G-5) and 464–469 (r2/G-4), shard 1 `.38`; consumed at `.24`, `.33`, `.35`, `.38`.

**TEETH:** JC7 (the cocycle identity, 581 samples, 261 triples); the module half by R1-DMULT/R1-COB.

---
### EFF.GRTJC.72  [lemma]  COROLLARY JC-COB — the inner factor IS the anchor coboundary

**CANONICAL STATEMENT:** verbatim, lines 1335–1352.
**FORM:** bold-headed corollary with an `[r2, G-1]` re-fence.

> “**COROLLARY JC-COB [r1] (what the slot-δ unit u actually is) [r2, G-1 —
> re-fenced onto the EXACT tier].** On ~~(DMULT)~~ **(DMULT-s)**:
> A(λ,μ) = (a_λa_μ/a_{λ+μ})·y^{δ(λ,μ)}, i.e. JC-SPAN's unit is
> **u = a_λ·a_μ** — the product of the two anchors' own digit constants. Hence the
> structure constant of §3.2 is c_{m+1}(γ,γ′) = (a_γa_{γ′}/a_{γ+γ′})·z̄^δ: the
> INNER factor is exactly the **coboundary of the anchor normalization**, and (on
> [ILN]†'s scored stratum, composing with §3.3) ∏_{j≤m}z_j^{D_j} =
> a_γa_{γ′}/a_{γ+γ′}. *Fences [r2, G-1]:* this rides **(DMULT-s), the MEASURED
> tier** — on the citable (DMULT-w) alone the sharp values here degrade to
> JC-SPAN's u ∈ K_m^* — and the second half additionally rides [ILN]†; it does
> NOT trivialize the (CYC) property … and it re-scores no measured verdict.”

**★ THE MATHEMATICAL PAYLOAD: the inner factor of the carry cocycle is a COBOUNDARY** — `∏_{j≤m}z_j^{D_j} = a_γa_{γ′}/a_{γ+γ′}` on the scored stratum. **That is a structural explanation of the instrument's measured `M1–M5` constants**, and it is the sharpest statement in the note.

**CONDITIONALITY:** **THE ONLY CLAUSE RIDING `(DMULT-s)`.** On `(DMULT-w)` alone it degrades gracefully to JC-SPAN's already-proved `u ∈ K_m^*`. **The second half additionally rides [ILN]†.** **And the note fences the obvious over-read: it does NOT trivialize (CYC)**, which is a statement about the anchor-INDEXED presentation. **Annex #1 upgrades the tier: `(DMULT-s)` is PROVED-conditional on the measured perimeter, and “COROLLARY JC-COB's sharp `u = a_γa_{γ′}` inherits (DU-COB)”.**

**DERIVATION:** From `(DMULT-s)` (ω ≡ 1) applied at the two anchors, whose digit polynomials are the constants `a_γ`, `a_{γ′}` (JC-ANCHMON(c)).

**RESOLUTION TRACE:** statement lines 1335–1352; the tier 1220–1247 (`.69`); **Annex #1 at 2805 (shard 3)**; the box 1993–2003 (JC-BOX-8(iii), shard 3: “JC-COB's second half rides [ILN]† in addition to (DMULT-s), and the identity is displayed, not consumed by any clause”).

**TEETH:** **R1-COB** — “`𝑅_{γ+γ′}(φ_γφ_{γ′}) == a_γ·a_{γ′}·y^δ` exactly on the full anchor grid of every row” — **2,607 samples, 869/869 anchor pairs, all 29 rows, 0 violations, including the `e_m = 1` row C4H**. **With a TWO-MODE falsifier annotated post-tier-split** (r3/G-7, shard 1 `.28`): a failure with the slot set still `{δ}` refutes only `(DMULT-s)`; only a SLOT-SET failure refutes `(DMULT-w)` and `(COORD-B)(2)`.

---
### EFF.GRTJC.73  [definition]  TC-3 as the quotient by 𝔦^B, and the ℤ/E-graded target 𝒜

**CANONICAL STATEMENT:** verbatim, lines 1354–1396 — the definition, the struck r0 display, the ideal-piece computation with its `[r3, G-5]` one-liner, the K-line conclusion, and the `[r2, G-9]` ideal transport.
**FORM:** bold-headed display + struck quotation + derivations.

> “**TC-3 = the quotient by the homogeneous ideal 𝔦^B := in(Φ_{m+1})·B** (this is
> exactly what the instrument's certifier operationalizes as division by Φ_{NR}),
> taken on B, i.e. **strictly after TC-1**. ~~[r0: "𝔦 := in(Φ_{m+1})·gr(w) … Hence
> for every λ ∈ W, gr_λ/(𝔦 ∩ gr_λ) ≅ Δ/(ψ_m) = K, a ONE-dimensional K-space" …]~~
> — struck at [r1, F1] … On B, by (COORD-B)+(MULT-B),
>
>     𝔦^B ∩ B_n = in(Φ_{m+1})·B_{n−wΦ_NR}  corresponds to  ψ_m(y)·Δ,
>
> because ρ^B(in Φ_{m+1}·β) = A·ψ_m(y)·ρ^B(β) with
> ρ^B(in Φ_{m+1}) = ψ_m(y)/a_{wΦ_NR} **[r3, G-5 — the one-liner that makes the
> display an EQUALITY of ideal pieces rather than an inclusion, previously
> unwritten: A = A(wΦ_NR, n−wΦ_NR) = (unit)·y^{δ(wΦ_NR, n−wΦ_NR)} by
> (MULT-B) + JC-SPAN, and δ(wΦ_NR, n−wΦ_NR) = 0 for EVERY n, because
> e_m | wΦ_NR (= e_m·g_m·γ_{m+1}) gives s_NR(wΦ_NR) = 0 and
> s_NR(n−wΦ_NR) = s_NR(n), so δ = (0 + s_NR(n) − s_NR(n))/e_m = 0. Hence A is
> a CONSTANT and the image is ψ_m(y)·Δ on the nose — **were δ = 1 the quotient
> B_n/(𝔦^B ∩ B_n) would strictly contain a K-line and §3.1's "each 𝒜_ν is a
> 1-dimensional K-space" would fail**]** … Hence for **every n ∈ ℤ** …
>
>     B_n/(𝔦^B ∩ B_n)  ≅  Δ/(ψ_m)  =  K_{m+1} = K       (via y ↦ z̄),
>
> a ONE-dimensional K-space with basis the image of in(φ_n). This is the precise
> sense in which TC-3 turns the Δ-coordinate into a K-scalar — and JC-PSIKER(iii)
> says its kernel ψ_m·Δ ≠ 0 on every piece of B, so no relabeling can replace it.
> Write 𝒜 := (B/(in(π)−1))/image(𝔦^B) for the TC-transported ring; it is
> ℤ/E-graded … with 𝒜_ν = A_ν/(𝔦 ∩ A_ν) ≅ K·[φ_{γ_ν}] and 𝒜_0 = K.”

**★ THE `[r3, G-5]` ONE-LINER IS LOAD-BEARING AND WAS UNWRITTEN FOR THREE ROUNDS.** It is what turns an inclusion into an EQUALITY of ideal pieces, and the note spells out the counterfactual: **“were δ = 1 the quotient would strictly contain a K-line and §3.1's ‘each 𝒜_ν is a 1-dimensional K-space' would fail”** — i.e. **W-7's entire dimension count depended on an unwritten step.** (And the divisibility it uses, `e_m | wΦ_NR`, is the one r3/G-4 had to correct elsewhere — shard 1 `.25`.)

**CONDITIONALITY:** The `[r2, G-9]` ideal transport (lines 1389–1396) supplies the other unwritten step: JC-GAUGE(iii)'s isomorphism is only ADDITIVE, so carrying `image(𝔦^B) ∩ A_ν` onto `𝔦^B ∩ B_n` needs an argument — supplied, using that `𝔦^B` is an IDEAL of `B` and `ϑ^{-k} ∈ B`.

**DERIVATION:** Displayed in full.

**RESOLUTION TRACE:** statement lines 1354–1396; the dispositions 332–333 (r3/G-5) and 483 (r2/G-9), shard 1 `.26`/`.38`; JC-PSIKER(iii) 957–961 (`.10`); consumed at `.23`, `.27`, `.39`.

**TEETH:** JC6 (the kernel witness); the certifier's own division by `Φ_{NR}` is what the instrument operationalizes.

---
### EFF.GRTJC.74  [TABLE]  the five PE1-listed consumers, re-derived

**CANONICAL STATEMENT:** verbatim, lines 1398–1413 — the header and the five-row table.
**FORM:** bold-headed paragraph + Markdown table.

> “**[r1] THE FIVE CONSUMERS, RE-DERIVED ONE BY ONE.** PE1 listed exactly five
> places that consumed the refuted r0 form. Each is re-derived on (COORD-B); none
> needed downgrading, and one is strengthened.”

`[TABLE]` transcribed verbatim:

| consumer (PE1's list) | what it needs | r1 verdict |
|---|---|---|
| §3.1 "every A_ν is 1-dimensional over K after TC-3" | `A_ν ≅ B_n` (JC-GAUGE(iii)) + the display above | **THROUGH** — restated in §3.1 on `B_n` |
| §3.4 THEOREM JC-IND / OB-4 (independence) | ℤ/E degree separation + each `𝒜_ν` a K-line with basis `[φ_{γ_ν}] ≠ 0` | **THROUGH** — §3.4, with the base-changed module now existing (`B_n` free rank one over Δ, (COORD-B)(2)) |
| W-7's bijectivity of Ψ | injectivity = JC-IND; surjectivity = spanning | **THROUGH and STRENGTHENED**: `dim_K 𝒜 = E`, so the K-span of the anchor classes is ALL of `𝒜` — **spanning is now a theorem, not a definition** (this is also G2's repair) |
| §5 FINDING JC-F1's dimension count | `dim_K 𝒜(T) = E` | **THROUGH** — E graded K-lines |
| (MULT) for arbitrary α,β | Δ-bilinearity of the multiplication | **THROUGH** as (MULT-B), on (COORD-B)(2) = (1) + (DMULT-w) [r2, G-1] |

**And the closing sentence (lines 1410–1413):** “Nothing else in §§2–5 used the refuted form: JC-DOM, JC-GAUGE, JC-PER, JC-FIB, JC-ANCHMON, JC-SCAL, JC-SPAN, JC-LOAD and JC-PSIKER's witness are statements about integral digit arithmetic and are untouched (**PE1 re-derived all of them independently and found no defect**).”

**★ THIS IS THE BLAST-RADIUS AUDIT OF A CRITICAL, DONE PROPERLY: the finder listed the consumers, the round re-derived each, and the outcome is recorded per consumer — including one STRENGTHENING.** **“spanning is now a theorem, not a definition”** is the strengthening, and it is what makes W-7's Ψ surjective onto the whole transported ring rather than onto a span by fiat.

**ARITHMETIC AUDIT (rule 22):** consumers listed = **5** ✔ matches “PE1 listed exactly five places”; verdicts = 5 THROUGH, of which 1 STRENGTHENED, **0 downgraded** ✔ matches “none needed downgrading, and one is strengthened”.

**CONDITIONALITY:** **PE2 independently re-derived all five and “found no false statement”** (shard 1 `.35`).

**DERIVATION:** Per row, at the cited section.

**RESOLUTION TRACE:** statement lines 1398–1413; the consumers at 1460–1475 (`.76`), 1550–1572 (`.80`), 1419–1458 (`.75`), 1801–1824 (`.92`), 1287–1333 (`.71`).

**TEETH:** the r1 battery's ten families (§9.3, shard 3) test the repaired statements; PE2's independent re-derivation is the AUDIT leg.

---
### EFF.GRTJC.75  [lemma]  ★ THEOREM W-7 — the face box (the anchor-transport isomorphism Ψ)

**CANONICAL STATEMENT:** verbatim, lines 1419–1458 — the theorem box with its structure-constant display and the six per-obligation grades.
**FORM:** display (a blockquoted face box).

> “**THEOREM W-7.** Fix T of the [ILN]† class, m with E > 1, and window
> representatives γ_0,…,γ_{E−1} ∈ W of the E classes mod E (they exist: all
> large γ lie in W). Let 𝒜(T) be the K-span of the anchor classes [φ_{γ_ν}]
> ~~in the degree-0 component of~~ **[r1, G2]** across all ℤ/E-degrees of the
> TC-transported ring (§1, §2.10 [r1]; by §2.10's consumer table this span is
> the WHOLE transported ring). Then the K-linear
> extension of u_ν ↦ [φ_{γ_ν}] is an isomorphism of K-algebras
>
>     Ψ : (⊕_{ν∈ℤ/E} K·u_ν, u_νu_{ν′} = c_{m+1}(ν,ν′)u_{ν+ν′})  ≅  𝒜(T),
>
> where 𝒜(T)'s multiplication is gr(w)'s OWN (never c_T), and the structure
> constant is
>
>     c_{m+1}(γ,γ′) = (u/a_{γ+γ′})·z̄^{δ}          [always, §3.2 EXISTENCE]
>                   = z̄^{δ}·∏_{j=1}^{m} z_j^{D_j} = c_T(γ,γ′)
>                                                  [on [ILN]†'s scored stratum]
>
> with u = the slot-δ coefficient of JC-SPAN and a_λ = 𝑅_λ(φ_λ) ∈ K_m^* the
> anchor's own digit constant.”

**Double-emission (rule 14) — the six graded obligations as a `[TABLE]`:**

| obligation | statement | grade as written | scope |
|---|---|---|---|
| **OB-2** | well-defined | **PROVED, general m** — JC-PER, **byte-exact** | — |
| **OB-3 EXISTENCE + STRUCTURE** | there is a constant, and it is `(K_m^*-unit)·z̄^δ` | **PROVED, general m, on ALL window pairs** — **no [ILN]†, no stratum fence** | sharp form needs `e_m ≥ 2` (JC-BOX-4) |
| **OB-3 VALUE** | the unit is `∏_{j≤m}z_j^{D_j}` | **PROVED, general m, on [ILN]†'s scored stratum** (D integral ∧ off DCX) | by transport through W-8 + [ILN]† ACCEPTED |
| **OB-4** | independence | **PROVED, general m** | ~~(COORD)/(IN-3)(c) base change; the Δ-rank input is literature-carried, NOT measured~~ **→ [r2, G-4]: (COORD-B)(2) base change on `B_{γ_ν}`, riding (DMULT-w); the Δ-module input IS measured in its equivalent digit form** |
| **OB-5** | tautology fence | **DISCHARGED as an architecture statement** | with the instrument's independent-code leg as its machine bracket |
| — | the whole clause | Attempt grade 0/2 (**EXPRESSLY superseded by Annex #7**); rides §0's stack | — |

**★ THE `[r2, G-4]` CORRECTION TO OB-4'S GRADE LINE IS AN HONESTY DEFECT PE2 NAMED BY THAT WORD**, and it survived a full round inside a THEOREM box (lines 1449–1455):

> “**[r2, G-4: that grade line
> survived r1 un-superseded inside this THEOREM box — it graded OB-4 on the
> input PE1 REFUTED and denied r1's own machine leg.** As §3.4 [r1] actually
> states: (COORD-B)(2) base change on B_{γ_ν}, riding (DMULT-w); the
> Δ-module input IS measured in its equivalent digit form (R1-DMULT
> 2,784/0, R1-COB 869/869; bilinear leg R2-BIL at §9.4), with the exact
> tier (DMULT-s) measured-not-cited (JC-BOX-3).]**”

**★ THE TAUTOLOGY-FENCE PHRASE IN THE BOX IS THE NOTE'S ARCHITECTURAL COMMITMENT:** “**where 𝒜(T)'s multiplication is gr(w)'s OWN (never c_T)**”. The whole point of W-7 is that the structure constant is COMPUTED on the gr side and only THEN compared with the accepted closed form — see `.83`.

**CONDITIONALITY:** **The two lines of the structure-constant display have DIFFERENT scopes and the box marks them:** the `(u/a_{γ+γ′})·z̄^δ` form holds **ALWAYS** (§3.2, every window pair); the identification with `c_T = z̄^δ∏z_j^{D_j}` holds **only on [ILN]†'s scored stratum** (§3.3). **The wider half has ZERO machine support** (JC-BOX-2: 0 DCX, 0 non-integral-D pairs on the grid). **The `𝒜(T)` definition carries FINDING JC-F2** (shard 1 `.52`), REVIEW-OWED at three upstream sources.

**DERIVATION:** `.76`–`.83`.

**RESOLUTION TRACE:** statement lines 1419–1458; proof lines 1460–1652; the disposition 464–469 (r2/G-4, shard 1 `.38`), 387–390 (r1/G2, shard 1 `.33`); correction site 3004–3008 (Annex #7).

**TEETH:** JC1/JC2 + the instrument's **P0-OB2 0/285**, **P2-REP 0/174**, **P4-DEG 0/29**; r1's R1-PER/R1-SURJ/R1-DMULT for the repaired coordinate.

---
### EFF.GRTJC.76  [lemma]  §3.1 OB-2 — well-definedness, re-derived on the repaired object

**CANONICAL STATEMENT:** verbatim, lines 1462–1475.
**FORM:** paragraph with a struck sentence and its `[r1, F1]` replacement.

> “JC-PER gives φ_{γ+kE} = π^kφ_γ as polynomials, so [φ_{γ+kE}] = [φ_γ] after TC-2
> (JC-GAUGE gauges in(π) to 1). Hence u_ν ↦ [φ_{γ_ν}] does not depend on which
> window representative of ν is chosen, and Ψ is defined on ℤ/E. ~~Every A_ν is
> 1-dimensional over K after TC-3 (§2.10), so Ψ maps the ν-summand onto A_ν's
> K-line.~~ **[r1, F1 — RE-DERIVED on the repaired object.]** By JC-GAUGE(iii) the
> gauged piece is A_ν ≅ **B_n** for any n ≡ ν (mod E) — JC-DOM's post-TC-1 piece,
> not gr_n (G1) — and by §2.10's repaired display
> B_n/(𝔦^B ∩ B_n) ≅ Δ/(ψ_m) = K with basis the image of in(φ_n). So after TC-3
> each 𝒜_ν is a 1-dimensional K-space with basis [φ_{γ_ν}], and Ψ maps the
> ν-summand ONTO it. The step is now available at every ν and every n ≡ ν, with no
> window and no attainment side-condition (COORD-B(1)). **PROVED, general m**, on
> (DMULT-w) + (IN-5) [r2, G-1].”

**★ THE REPAIR IMPROVED THE STATEMENT: “with no window and no attainment side-condition”.** The r0 version needed `λ ∈ W` and attainment; the `B`-based version needs neither, because `in(π)` is a unit after TC-1.

**CONDITIONALITY:** Rides `(DMULT-w)` + `(IN-5)`.

**DERIVATION:** JC-PER + JC-GAUGE(iii) + §2.10's repaired display (`.73`).

**RESOLUTION TRACE:** statement lines 1462–1475; JC-PER 756–772 (`.57`); the display 1354–1381 (`.73`); consumer row 1 of `.74`.

**TEETH:** JC1 (`k = 1,2,3`); the instrument's P0-OB2 0/285 and P2-REP 0/174; r1's R1-PER/R1-SURJ/R1-DMULT.

---
### EFF.GRTJC.77  [lemma]  ★ §3.2 THEOREM JC-CARRY-m — the composite CARRY law (no [ILN]† used)

**CANONICAL STATEMENT:** verbatim, lines 1479–1508 — the theorem, its proof, and the three displayed consequences.
**FORM:** bold-headed theorem + numbered consequences.

> “**THEOREM JC-CARRY-m.** For γ,γ′ ∈ W with γ+γ′ ∈ W and e_m ≥ 2:
>
>     in(φ_γ)·in(φ_{γ′}) = (u/a_{γ+γ′})·y^{δ}·in(φ_{γ+γ′})   in the ρ-coordinate,
>     u ∈ K_m^*,  δ = δ(γ,γ′) ∈ {0,1},
>
> and after TC-3 the scalar (u/a_{γ+γ′})·z̄^δ ∈ K^* is the structure constant of
> 𝒜(T) at (γ,γ′). Pre-TC-3 it is a K-scalar iff δ < g_m (JC-LOAD).
>
> *Proof.* JC-SPAN computes 𝑅_{γ+γ′}(φ_γφ_{γ′}) = u·y^δ with u ∈ K_m^*; divide by
> a_{γ+γ′} to pass to ρ, which is the definition of A(γ,γ′) in ~~(MULT)~~
> **(MULT-B)|gr [r2, G-4]**. TC-3 sends y ↦ z̄ (§2.10). ∎”

**★ THE THREE CONSEQUENCES, verbatim (lines 1495–1508), because each is separately consumed:**

> “1. **The outer/inner split is structural.** Outer = y^δ (slot shift, TC-3's
>    z̄^δ); inner = a K_m^*-unit (TC-3-blind). No coordinate choice enters. In
>    particular the instrument's rival readings H-B (inner dropped) and H-C
>    (germ-signed outer) are refuted structurally as well as numerically (H-B
>    fails on exactly the 215 pairs with nontrivial inner; H-C on 73).
> 2. **Existence is unconditional in the window.** The constant exists on EVERY
>    window pair, including pairs off [ILN]†'s scored stratum (non-integral D_j,
>    DCX pairs) where the closed form c_T is not even defined. This is a STRICT
>    extension of the accepted law's scope — with **zero machine support**, since
>    the instrument's grid contained 0 DCX and 0 non-integral-D pairs (JC-BOX-2).
> 3. **δ ∈ {0,1} always**, so "TC-3 load-bearing" ⟺ δ = 1 ∧ g_m = 1: the load
>    set is a *geography*, not a growing set — it is empty on every g_m ≥ 2 stage.”

**★ CONSEQUENCE 2 IS THE NOTE'S MOST EXPOSED CLAIM AND IT SAYS SO:** a STRICT extension of the accepted law's scope, **with zero machine support**, boxed at JC-BOX-2 with the instruction “a hostile pass should attack it there first”.

**CONDITIONALITY:** **`e_m ≥ 2`** (JC-SPAN's fence). **Rides `(DMULT-w)` via `(MULT-B)`.** **This is the composite-stage generalization of CARRY-1** (`(IN-2)`, where there is NO extra factor); the whole content is that exactly one `K_m`-unit appears.

**ARITHMETIC AUDIT (rule 22):** the three rival readings fail on **138** (H-D), **215** (H-B), **73** (H-C) of 669 pairs respectively — three distinct counts from one grid ✔, and H-D's 138 is the figure the header cites (shard 1 `.03`) ✔.

**DERIVATION:** Two lines, displayed: JC-SPAN gives `u·y^δ`; divide by `a_{γ+γ′}`; TC-3 sends `y ↦ z̄`.

**RESOLUTION TRACE:** statement lines 1479–1508; JC-SPAN 829–857 (`.61`); (MULT-B) 1291–1333 (`.71`); JC-LOAD 859–924 (`.62`); the box 1946–1951 (JC-BOX-2, shard 3).

**TEETH:** JC3 (609/609); the instrument's rival-reading counts are the refutation evidence. **Consequence 2 has NONE — proof-only, disclosed.**

---
### EFF.GRTJC.78  [lemma]  §3.3 THEOREM JC-INNER — the inner normalization is ∏ z_j^{D_j}

**CANONICAL STATEMENT:** verbatim, lines 1512–1523.
**FORM:** bold-headed theorem.

> “**THEOREM JC-INNER.** On [ILN]†'s scored stratum (all D_j integral, pair off
> DCX), for γ,γ′ ∈ W with γ+γ′ ∈ W and e_m ≥ 2:
>
>     c_{m+1}(γ,γ′) = c_T(γ,γ′) = z̄^{δ}·∏_{j=1}^{m}z_j^{D_j},
>     equivalently   u = a_{γ+γ′}·∏_{j=1}^{m}z_j^{D_j}  in K_m^*.
>
> *Proof.* By THEOREM W-8 (§4, proved independently of c_T) the gr-side constant
> equals the harness ratio: c_{m+1}(γ,γ′) = c_val(γ,γ′) :=
> read(γ+γ′,φ_γφ_{γ′})/read(γ+γ′,φ_{γ+γ′}). By [ILN]† (IN-1, ACCEPTED on exactly
> this stratum) c_val = c_T. Compose. For the second form, divide by z̄^δ (a unit,
> since ψ_m(0) ≠ 0) and use that ∏z_j^{D_j} and u/a lie in K_m, on which
> y ↦ z̄ reduction is the injection K_m ↪ K. ∎”

**★ THE PROOF IS A TWO-STEP COMPOSITION AND THE ORDER MATTERS FOR THE TAUTOLOGY FENCE:** W-8 (proved **independently of `c_T`**) identifies the gr-side constant with the harness ratio; **only then** does `[ILN]†` identify that ratio with the closed form. **“Deleting §3.3 leaves §§2–3.2 and 3.4 standing”** (§3.5).

**CONDITIONALITY:** **`[ILN]†`'s scored stratum (all `D_j` integral ∧ off DCX) AND `e_m ≥ 2`.** **This is OB-3's VALUE half — the narrower of W-7's two scopes.**

**DERIVATION:** Displayed. Note the care in the second form: dividing by `z̄^δ` is legitimate because `ψ_m(0) ≠ 0` makes it a unit, and the identification lands in `K_m` where `y ↦ z̄` is injective.

**RESOLUTION TRACE:** statement lines 1512–1523; W-8 1656–1771 (`.85`–`.89`); `(IN-1)` 505–517 (shard 1 `.41`); the coboundary form 1335–1352 (`.19`).

**TEETH:** the instrument's **P5-OB6 0/669** (both sides computed independently per pair) is W-8's leg; JC7/JC8 for the constant table.

---
### EFF.GRTJC.79  [scope record]  ★★ §3.3 — the germ, split honestly (THE J-B ↔ J-C INTERFACE)

**CANONICAL STATEMENT:** verbatim, lines 1525–1548.
**FORM:** bold-headed paragraph + two bulleted halves.

> “**The germ, split honestly (M3, and J-B's fence).** J-B's JB-CREAD gives the
> (C-READ) transport constant c_m = ψ_{m,0} = −z_{m+1} at the level-m read, with
> the ε-carry cancelling in print coordinates (LEMMA JB-EPS, unconditional). The
> instrument measured this in the carrier and split it:
>
> * **CONFIRMED as a value law**: on all **27 eligible (g_m = 1) stages**,
>   val(Ĉ_m) = −z̄ = −z_{m+1} exactly, where Ĉ_m := Φ_{m+1} − Φ_m^{e_m} is the
>   canonical correction digit (J-B's g_m = 1 well-definedness fence, JB-BOX-4);
>   and the carrier-side class constant κ of multiplication by [Ĉ_m] satisfies
>   **κ·val(φ_{e_mγ_{m+1}}) = −z_{m+1} on all 27 stages (0 violations)**, with κ
>   itself ranging over {1, z̄, z̄², z̄³, z̄⁴}. In this note's coordinates that
>   identity is the a_λ-normalization of §3.2: κ is the class constant of the
>   correction digit measured against the anchor, so the bare letter appears
>   **exactly when the anchor's own digit constant is 1**. The claim
>   "c_m = −z_{m+1}" is therefore a statement about the transport constant modulo
>   the anchor's value normalization — J-B's fence is honored, not widened (and
>   J-B's own scope fences ride: (VD-m) free only at m ≤ 1, JA-VDIND above,
>   g_m = 1 for the Ĉ_m instance).
> * **REFUTED as OB-3's inner factor**: the brief's literal hypothesis is reading
>   H-D (inner letters replaced by −z_{m+1}) and it FAILS on **138 of 669** scored
>   pairs. §3.2 explains why structurally: the inner factor is a unit of **K_m**,
>   and −z_{m+1} ∉ K_m whenever g_m ≥ 2; on g_m = 1 stages K_{m+1} = K_m and the
>   two can coincide numerically without coinciding as laws (the instrument's own
>   printer caveat, S6.2).”

**★★ THIS IS THE J-B ↔ J-C INTERFACE, AND IT IS THE MOST IMPORTANT CROSS-READ FINDING IN THE QUEUE.** The compiler verified BOTH sides:

- **GRTJB's side** (`spec/EFF-GRTJB-s2of3.md` `.54`, source L2303–2308): the germ `ρ_m(R) = −z_{m+1}·ρ_m(f)` is “the semantic germ the J-C carrier block (W-6..W-9) needs — **displayed here as an identity of READ VALUES only**; no graded-ring (gr) object is constructed or claimed, and BLOCKED-ON-CARRIER-TIE stands.”
- **GRTJC's side (this unit)** receives it and **splits it in two**: **CONFIRMED as a value law** on all 27 eligible `g_m = 1` stages, **REFUTED as OB-3's inner factor** on 138/669 pairs.
- **The two are CONSISTENT and the note explains why:** J-B's statement is about READ VALUES at the level-`m` read; OB-3's inner factor is a unit of `K_m`; **`−z_{m+1} ∉ K_m` whenever `g_m ≥ 2`**, and on `g_m = 1` stages `K_{m+1} = K_m` so “the two can coincide numerically without coinciding as laws”.
- **J-B's fence is HONORED, NOT WIDENED**, and GRTJC names the inherited fences explicitly: “(VD-m) free only at `m ≤ 1`, JA-VDIND above, `g_m = 1` for the `Ĉ_m` instance”.

**★ THE PRECISE MECHANISM, and it is worth a chapter cut's attention:** “κ is the class constant of the correction digit measured against the anchor, so **the bare letter appears exactly when the anchor's own digit constant is 1**.” **So the brief's guess was a coordinate artefact of the `a_λ`-normalization** — true at `a_λ = 1`, false otherwise.

**CONDITIONALITY:** **27 eligible `g_m = 1` stages** (of 29 rows; the two `g_m = 2` rows C2I, C4I are ineligible). **J-B's own scope fences ride in.** **NOTE: GRTJB has since received post-acceptance corrections E-3/E-4; neither touches JB-CREAD, JB-EPS or JB-BOX-2's enumeration** (E-4: “JB-BOX-2's perimeter enumeration survives verbatim”), **so this inheritance is unaffected — but nothing in GRTJC says so** (shard 1 OPEN-CALL 3).

**ARITHMETIC AUDIT (rule 22):** 29 rows − 2 (`g_m = 2`: C2I, C4I) = **27 eligible** ✔ matches “27 eligible (g_m = 1) stages” and §7's “the 27 g_m = 1 stages counted in rows 3/4” ✔.

**DERIVATION:** The confirmation is measured; the refutation is measured AND explained structurally by §3.2's consequence 1.

**RESOLUTION TRACE:** statement lines 1525–1548; the supplier `spec/EFF-GRTJB-s2of3.md` `.54` (GRTJB L2303–2308); `(IN-4)` 559–565 (shard 1 `.44`); the structural explanation 1497–1501 (`.24`); the instrument's refutation 12–21 (shard 1 `.03`).

XREF: `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md:JB-CREAD` — grep-verified count **36** · `JB-EPS` — **30** · `JB-BOX-4` — **2** · `JB-BOX-2` — **45**.

**TEETH:** **the instrument, both ways**: 27/27 stages 0 violations for the value law; 138/669 failures for the refuted reading. Disposition: **measurement, confirming AND refuting the same object under two different readings** — the cleanest instance in the corpus of an instrument separating a true statement from a false generalization of it.

---
### EFF.GRTJC.80  [lemma]  §3.4 THEOREM JC-IND — K-linear independence, and spanning promoted to a theorem

**CANONICAL STATEMENT:** verbatim, lines 1552–1572.
**FORM:** bold-headed theorem with a struck passage and its `[r1, F1]` replacement.

> “**THEOREM JC-IND.** The classes [φ_{γ_0}],…,[φ_{γ_{E−1}}] are K-linearly
> independent in 𝒜(T), and each spans its own ℤ/E-graded line; so Ψ is bijective.
>
> *Proof.* By JC-GAUGE the transported ring is ℤ/E-graded and [φ_{γ_ν}] ∈ 𝒜_ν
> with ν = γ_ν mod E pairwise distinct (JC-FIB); the TC-3 ideal is generated by one
> homogeneous element, so the quotient keeps the ℤ/E-grading and 𝒜_0 = K. A
> relation Σ_ν c_ν[φ_{γ_ν}] = 0 with c_ν ∈ K = 𝒜_0 therefore splits into
> c_ν[φ_{γ_ν}] = 0 in 𝒜_ν for each ν. ~~By §2.10 each A_ν (after TC-3) is a
> 1-dimensional K-space with basis [φ_{γ_ν}] — the base change of the free
> rank-one Δ-module gr_{γ_ν} along Δ ↠ Δ/(ψ_m) = K.~~ **[r1, F1 — the base-changed
> module is now the RIGHT one, and it exists:]** by (COORD-B)(2) the free rank-one
> Δ-module is **B_{γ_ν}** (gr_{γ_ν} is not free over Δ — it is a
> finite-dimensional K_m-space, §2.10), and JC-GAUGE(iii) gives A_ν ≅ B_{γ_ν}; its
> base change along Δ ↠ Δ/(ψ_m) = K is the K-line 𝒜_ν with basis the image of
> in(φ_{γ_ν}), which is NONZERO because ρ^B(in φ_{γ_ν}) = 1 ∉ (ψ_m). Hence
> c_ν = 0. **[r1, G2/F1 — spanning is no longer definitional:]** by §2.10's
> display every 𝒜_ν equals K·[φ_{γ_ν}], so the K-span of the anchor classes is the
> whole transported ring and dim_K 𝒜(T) = E. (The r0 text said "spanning is
> definitional (design note C18)"; that reading is what G2 corrects.) This is the
> composite-stage instance of FGMN Thm 4.2's rank-one freeness, applied — after
> JC-LOC — to the object Thm 4.2 is about. ∎”

**★ TWO STRENGTHENINGS IN ONE PROOF:** (i) **the base-changed module now EXISTS** (it is `B_{γ_ν}`, free rank one over Δ, whereas `gr_{γ_ν}` is not); (ii) **spanning is promoted from a definition to a theorem** — “the r0 text said ‘spanning is definitional (design note C18)'; that reading is what G2 corrects.” **So Ψ is onto the WHOLE transported ring, not onto a span by fiat.**

**CONDITIONALITY:** Rides `(COORD-B)(2)`, hence `(DMULT-w)`. **The final sentence is the note's own summary of the whole repair: “the composite-stage instance of FGMN Thm 4.2's rank-one freeness, applied — after JC-LOC — to the object Thm 4.2 is about.”**

**DERIVATION:** Displayed in full above.

**RESOLUTION TRACE:** statement lines 1552–1572; (COORD-B)(2) 1174–1186 (`.68`); JC-LOC 1037–1062 (`.65`); the §2.10 display 1354–1381 (`.73`); consumer row 2 of `.74`.

**TEETH:** the census genres at `.81`; **JC8's unit half was VACUOUS until R1-UNIT** (869 unit / 0 zero / 0 undefined / 0 out-of-window, with tooth T4 proving the predicate can fire).

---
### EFF.GRTJC.81  [TABLE]  §3.4 — the case split FROM the census (examples-first)

**CANONICAL STATEMENT:** verbatim, lines 1574–1581 — the header and the three-genre table.
**FORM:** bold-headed paragraph + Markdown table.

> “**The case split FROM the census (examples-first).** The instrument's OB-4
> censuses give exactly three genres, and each is now accounted for:”

`[TABLE]` transcribed (long cells condensed with `…`, every figure preserved):

| genre (instrument) | count | this note's status |
|---|---|---|
| anchor classes (P4-DEG) | **29/29 rows bijective** | never zero: `a_λ ∈ K_m^*`, coordinate a unit constant, not divisible by `ψ_m` |
| monomial perturbations (SPAN-M) | **328 certified / 0 zero-class / 0 FAILED (606 skipped for non-integrality)** — **[r1, G6]** the parenthesis is the instrument's own verdict row, **dropped in r0 and restored here** | coordinate `= (unit)·y^k` reducing into K ⟹ certifies; 0 genre rows, so ~~no case is owed~~ **[r1, G6]** no case is owed MATHEMATICALLY — (COORD-B) covers every element of `B_n`, integral or not — while as MACHINE evidence the census covers only the **328 of 934** perturbations that stayed integral. **The 606 skipped are exactly the ones that left `O[x]`; after the r1 repair they are legitimate elements of `B` … i.e. they lie in the newly covered part of the statement and have NO machine leg.** Disclosed as a resolution limit, **“it is the one place r1 leaves a measurement owed”** |
| weight-matched sums (SPAN-S, unscored) | 435 certified / **60 zero-class** / 0 unexplained | **PROVED AWAY**: a class dies in TC-3 iff its Δ-coordinate `∈ (ψ_m)` (§2.10). The 60 are exactly that kernel; they are not anchors and carry no information about OB-4 |

**★ THE SPAN-M ROW IS THE NOTE'S SHARPEST SELF-INFLICTED IRONY, and it is disclosed as such:** the r1 repair made the statement WIDER (covering non-integral elements of `B`), and **the 606 perturbations the instrument skipped for non-integrality are exactly the newly covered ones** — so the repair moved 606 samples from “out of scope” to “in scope but unmeasured”. **“the one place r1 leaves a measurement owed”** (JC-BOX-8(i)).

**ARITHMETIC AUDIT (rule 22):** 328 certified + 606 skipped = **934** ✔ matches “328 of 934”. SPAN-S: 435 + 60 = **495** with 0 unexplained ✔.

**CONDITIONALITY:** The SPAN-M measurement gap is boxed at JC-BOX-8(i) and is **untouched by every runner** (shard 3, §9.4's closing: “the non-integral residue JC-BOX-8(i) is still untouched by every runner”).

**DERIVATION:** The three genres are the instrument's censuses; the note's job is to account for each.

**RESOLUTION TRACE:** statement lines 1574–1581; the disposition 399–401 (r1/G6, shard 1 `.33`); the box 1993–2003 (JC-BOX-8, shard 3); the kernel 1354–1396 (`.20`).

**TEETH:** P4-DEG 29/29; SPAN-M 328/934 with **606 unmeasured (PROOF-ONLY)**; SPAN-S PROVED AWAY.

---
### EFF.GRTJC.82  [scope record]  §3.4 — the honest rider, restated on the repaired footprint

**CANONICAL STATEMENT:** verbatim, lines 1583–1601.
**FORM:** bold-headed paragraph with a struck predecessor.

> “**Honest rider.** ~~The Δ-rank input (IN-3)(c) is *literature-carried*: the
> instrument explicitly did NOT measure freeness over Δ before TC-3 (only its
> degree-separation shadow and post-TC-3 spanning). If Thm 4.2's composite-order
> instance failed, (COORD) and hence §§2.7–3.4 would fail together.~~ **[r1 —
> re-stated on the repaired footprint.]** The Δ-module input is now exactly
> **(DMULT-w)** **[r2, G-1: the CITABLE tier …]** (§2.10), applied to B = gr^K(w) (JC-LOC), and it is the
> ONLY cited
> input of the coordinate calculus: the surjectivity half that r0 also cited is
> PROVED here (JC-BSURJ). PE1's observation stands and is now answered on its own
> terms — the instrument did not measure Δ-freeness, so **r1 measures its
> equivalent digit form**: family R1-DMULT (the exact-tier identity (DMULT-s),
> 𝑅_{λ+μ}(fg) = y^δ𝑅_λ(f)𝑅_μ(g) with multiplier 1) plus its sharp corollary
> R1-COB (u = a_γa_{γ′}, riding (DMULT-s)), with tooth T3, **[r2, G-2]** on
> monomial-dominated samples — the genuinely bilinear leg is r2's R2-BIL (§9.4).
> If (DMULT-w) failed at composite order,
> (COORD-B)(2), (MULT-B) and §§2.7–3.4 would fail together — JC-BOX-3, which r1
> re-cuts to box APPLICABILITY and citation precision rather than literature
> truth.”

**★ “PE1's observation stands and is now answered on its own terms”** — the finder said the instrument did not measure Δ-freeness; the round's answer is not to argue but to **measure its equivalent digit form**. **That is the note's characteristic response to a finding: build the leg.**

**CONDITIONALITY:** **The blast radius is stated: if `(DMULT-w)` failed, `(COORD-B)(2)`, `(MULT-B)` and §§2.7–3.4 fail together.** **JC-BOX-3 is re-cut to box APPLICABILITY, not literature truth** — “the danger was never ‘Thm 4.2 might be false at composite order' but that Thm 4.2 (true, and about `K[x]`) had been transported to the wrong ambient object”.

**DERIVATION:** Record + the measurement programme it announces.

**RESOLUTION TRACE:** statement lines 1583–1601; the tier 1188–1267 (`.69`); the r2 leg 485–496 (shard 1 `.39`); the box 1960–1992 (JC-BOX-3, shard 3).

**TEETH:** R1-DMULT (2,784/0, **monomial-dominated — disclosed**), R1-COB (2,607/869), R2-BIL (261 dense pairs), teeth T3/U1/U2.

---
### EFF.GRTJC.83  [fence]  ★ §3.5 OB-5 — the tautology fence, and the fence-hygiene disclosure

**CANONICAL STATEMENT:** verbatim, lines 1605–1652 — the dependency order, the machine bracket, and the `[r1, G8]` disclosure.
**FORM:** paragraph + numbered dependency order + bold-headed disclosure.

> “The fence demands that 𝒜(T)'s multiplication be computed in gr(w) *before* c_T
> is mentioned, and only then compared. This note's chain does exactly that, and
> the dependency order is auditable:
>
> 1. **gr-side only** (no c_T, no harness read): JC-DOM, JC-GAUGE, JC-PER, JC-FIB,
>    JC-ANCHMON, JC-SCAL, JC-SPAN, JC-LOAD, JC-PSIKER, §2.10's ~~(COORD)/(MULT)~~
>    **[r1, F1]** (COORD-B)/(MULT-B) with JC-LOC/JC-PIINV/JC-BSURJ/JC-COB,
>    JC-CARRY-m, JC-IND. Inputs used: the corpus's definitions of w, split,
>    anchors, REALIZE, and FGMN (b)(e) + (DMULT) **[r1: (c) enters only through
>    (DMULT), on B]**. **The structure constant's existence,
>    its outer/inner shape, its y-degree, and the TC-3 load set are all fixed
>    here.**
> 2. **comparison only** (c_T enters ONCE): §3.3 evaluates the already-computed
>    constant against the accepted closed form, through W-8's read identity.
>    Deleting §3.3 leaves §§2–3.2 and 3.4 standing.”

**The machine bracket for the fence, verbatim (lines 1621–1633), quoted because it is the instrument's architectural property:**

> “the
> gr-side constant is the unique solution of a weight inequality whose decision
> procedure calls exactly four primitives — schoolbook O[x] arithmetic, the weight
> w by iterated Φ-development, the graded scalar lift REALIZE, and the classifier's
> own next key Φ_{NR} — while `Tower.constants` (c_T) and `Tower.read` (the harness
> val) are **never called inside the determination or the certification**; all 29
> rows ran EXHAUSTIVE over K (zero witness input) with per-pair uniqueness
> machine-proved; and the tautology tooth MT3 (one anchor rescaled by a nontrivial
> scalar class) was **caught on 197/206 pairs, ≥ 1 per non-skipped row (28/28)**,
> while the c_T-defined "check" reports 0 violations by construction. The 9
> escapes are disclosed (single-pair, all prime-residue-field rows |K| ∈ {3,5},
> planted rescaling coincides with a lawful constant) — they weaken the tooth's
> resolution, not the fence's architecture.”

**★ THE `[r1, G8]` FENCE-HYGIENE DISCLOSURE IS THE MODEL OF ITS GENRE** (lines 1635–1652): the paragraph above is correctly attributed to the **instrument**, whose certifier calls neither primitive. **“This note's own battery (`grt_jc_checks.py`) DOES call both, and r0 disclosed only the c_val half.”** The full disclosure follows with the non-circularity argument spelled out: (i) `T.constants(ga, gb)['delta']` supplies only the **integer δ**, computed from the SPLIT data alone — “byte-identically §1's definition” — and the closed-form value “is a different field of the same return dict, **never read by the scored predicates**”; (ii) `T.read` is called in JC6 as the *claim under test* and in JC7/JC8 to build the constant table, “which is by construction the harness ratio `c_val` — the §9.2 disclosure”. **“Nothing circular follows, but a hostile reader should not have to re-derive that: r1 states it.”**

**CONDITIONALITY:** **The MT3 tooth has 9 disclosed escapes** (single-pair, all prime-residue-field rows with `|K| ∈ {3,5}`, where the planted rescaling coincides with a lawful constant) — “they weaken the tooth's resolution, not the fence's architecture”.

**ARITHMETIC AUDIT (rule 22):** 197 caught + 9 escapes = **206 pairs** ✔; “≥ 1 per non-skipped row (28/28)” — 29 rows minus 1 skipped ✔ (C4A, `|K| = 2`, where no nontrivial scalar class exists — §7 genre 7).

**DERIVATION:** Architectural; the dependency order is auditable by construction.

**RESOLUTION TRACE:** statement lines 1605–1652; the disposition 404–405 (r1/G8, shard 1 `.33`); the instrument 12–21 (shard 1 `.03`); §9.2's disclosure 2136–2142 (shard 3).

**TEETH:** **MT3 — the tautology tooth**, 197/206 caught, ≥1 per non-skipped row; **and the contrast the note draws is the point: “the c_T-defined ‘check' reports 0 violations by construction”.** Disposition: **planted mutant with disclosed escapes, guarding an architectural property no ordinary family could test.**

---
### EFF.GRTJC.84  [lemma]  ★ THEOREM W-8 — the face box (harness-val = TC-read)

**CANONICAL STATEMENT:** verbatim, lines 1658–1671.
**FORM:** display (a blockquoted face box).

> “**THEOREM W-8.** For γ,γ′ ∈ W with γ+γ′ ∈ W, and N ≡ 0 (mod E), N ≥ wΦ_{NR}:
> the gr-side structure constant of §3.2 equals the harness value ratio,
>
>     c_{m+1}(γ,γ′)  =  c_val(γ,γ′) := read(γ+γ′, φ_γφ_{γ′}) / read(γ+γ′, φ_{γ+γ′}),
>
> exactly, with every line-wise normalization cancelling; and the residue chain
> K_0 ⊂ … ⊂ K_{m+1} used by both sides is one and the same tower (J-C(iii)).
> **GRADE: PROVED at general m** on inputs ~~(COORD)+(MULT)~~ **[r1, F1]**
> (COORD-B)+(MULT-B) **on B, i.e. (DMULT-w) [r2, G-1] + the in-note lemmas
> JC-LOC/JC-PIINV/JC-BSURJ** +JC-SPAN+JC-SCAL+R3
> ~~(i.e. FGMN (b)(c)(e) via W-1, ATTEMPT)~~ **[r2, G-4: (i.e. FGMN (b)(e) +
> (c)-ENTERING-ONLY-THROUGH-(DMULT-w)-on-B (§3.5), via W-1, ATTEMPT)]**.
> Attempt 0/2. Machine: the instrument's
> **P5-OB6 0/669** (both sides computed independently per pair).”

**★ W-8 IS THE HINGE OF THE TAUTOLOGY FENCE: it identifies the gr-side constant with the harness ratio, and it is “proved independently of `c_T`”** — which is what lets §3.3 compose it with `[ILN]†` without circularity.

**CONDITIONALITY:** **Rides `(DMULT-w)`** (the citable tier) plus the in-note lemmas. **Its proof was found CRITICALLY DEFECTIVE post-acceptance and REPAIRED — see `.85`, Annex #4. The CONCLUSION is unchanged.**

**DERIVATION:** `.85`.

**RESOLUTION TRACE:** statement lines 1658–1671; **correction site 2840–2884 (Annex #4, shard 3)**; the footprint correction 464–469 (r2/G-4, shard 1 `.38`).

**TEETH:** the instrument's **P5-OB6 0/669** — both sides computed independently per pair, on every scored pair of every row.

---
### EFF.GRTJC.85  [lemma]  ★★ §4.1 — the proof, SUPERSEDED by Annex #4 (the cured CRITICAL)

**CANONICAL STATEMENT:** verbatim, lines 1673–1710 — the read identity (†), the fence-clean defining equation, the (‡) derivation, the lift normalization and the conclusion.
**FORM:** `### 4.1 Proof` + displays.

> “Both sides are computed in the ρ-coordinate of §2.10.
>
> *The read is the reduced coordinate.* By §1 (definition), read(λ,f) = 𝑅_λ(f)(z̄).
> Hence for any f with w(f) = λ,
>
>     read(λ,f) / read(λ,φ_λ) = 𝑅_λ(f)(z̄)/a_λ = ρ_λ(in f)(z̄)          (†)
>
> (a_λ ∈ K_m^* is a constant, so its reduction is itself). **No unit is
> unaccounted for: (†) is an identity of the corpus's own definitions, and the
> line-wise ε-kit lives inside 𝑅_λ on both sides of the quotient.**
>
> *The gr-side constant.* Let c := c_{m+1}(γ,γ′) be defined by the fence-clean
> equation at the offset line λ+N, λ := γ+γ′:
>
>     in(φ_γ)in(φ_{γ′})in(X_N) = in(Λ_N(c))·in(φ_λ)   in the TC-transported ring.
>
> Apply ρ_{λ+N} and ~~(MULT)~~ **(MULT-B)|gr [r2, G-4]** to both sides.
> LHS = A(γ,γ′)·A(λ,N)·ρ_N(in X_N) and
> RHS = A(λ,N)·ρ_N(in Λ_N(c)); A(λ,N) ≠ 0 cancels (Δ is a domain), leaving
>
>     ρ_N(in Λ_N(c)) = A(γ,γ′)·ρ_N(in X_N).                              (‡)
>
> *The lift is exactly normalized.* By JC-SCAL(b), 𝑅_N(X_N) is a constant, and by
> R3 its reduction is read(N,X_N) = 1; a constant equal to 1 after the injection
> K_m ↪ K **is** 1, so 𝑅_N(X_N) = 1 and ρ_N(in X_N) = 1/a_N. By JC-SCAL(a),
> 𝑅_N(Λ_N(c)) is a polynomial of y-degree < g_m whose reduction is
> read(N,Λ_N(c)) = c (R3); the canonical degree-<g_m representative of c is unique,
> so **𝑅_N(Λ_N(c)) = c̃(y)** on the nose and ρ_N(in Λ_N(c)) = c̃(y)/a_N.
>
> *Conclusion.* (‡) becomes c̃(y) = A(γ,γ′) = (u/a_λ)y^{δ} (JC-CARRY-m). Reducing
> mod ψ_m: c = (u/a_λ)·z̄^{δ}. On the other side, by (†) with f = φ_γφ_{γ′} and
> JC-SPAN,
>
>     c_val = ρ_λ(in φ_γ·in φ_{γ′})(z̄) = ((u/a_λ)y^{δ})(z̄) = (u/a_λ)z̄^{δ}.
>
> The two agree. ∎”

**★★ CONDITIONALITY — THIS PROOF IS SUPERSEDED BY ANNEX #4, WHICH CURES A CRITICAL.** The sol certification's finding 1 was **“REAL — W-8 improperly lifts a quotient equality”**, and the annex (shard 3, L2840–2884) supersedes §4.1 **“from ‘Apply ρ_{λ+N}' through ‘The two agree.'”** — i.e. exactly the span quoted above from `Apply ρ_{λ+N}` onward. **The repaired route, verbatim:**

> “Put `q : Δ = K_m[y] ⟶ Δ/(ψ_m) = K`. The fence-clean defining equation for `c = c_{m+1}(γ,γ′)` holds in the **TC-transported ring**, hence **after TC-3**. Therefore applying the coordinate calculus gives the **congruence**
> `q(A(γ,γ′)A(λ,N)ρ_N(in X_N)) = q(A(λ,N)ρ_N(in Λ_N(c)))`, `λ := γ+γ′`,
> **not the corresponding equality in Δ.** By the offset-transport lemma, `A(λ,N) ∈ K_m^*`, so its image in `K` is nonzero and cancels. JC-SCAL and R3 give `ρ_N(in X_N) = 1/a_N`, `ρ_N(in Λ_N(c)) = c̃(y)/a_N`, `q(c̃) = c`. Cancelling `a_N ∈ K_m^*` yields exactly
> **`c = q(A(γ,γ′))`  (W8-q).**
> Independently, the same-line read identity `(†)`, applied to `f = φ_γφ_{γ′}`, gives `c_val(γ,γ′) = q(ρ_λ(in φ_γ in φ_{γ′})) = q(A(γ,γ′))`. Thus **`c_{m+1}(γ,γ′) = c_val(γ,γ′)` exactly.** …
> **The former display `c̃(y) = A(γ,γ′)` is valid only when both polynomials have degree `< g_m`, in particular when `δ < g_m`. On the load set `δ ≥ g_m`, only the congruence `c̃(y) ≡ A(γ,γ′) (mod ψ_m)` holds; this is exactly compatible with JC-LOAD's proof that RAW polynomial equality fails there.**”

**★ THE DEFECT IN ONE LINE: the proof lifted a quotient equality to `Δ`, and on the load set `δ ≥ g_m` that lift is exactly what JC-LOAD proves impossible.** So §4.1 as written **contradicted the note's own JC-LOAD** on the load set. **The repair replaces the lift by a congruence, and the conclusion survives unchanged.** **Annex #4's consumer sweep:** “**W-8 survives with conclusion unchanged by (W8-q).** JC-INNER and W-7 OB-3 VALUE consume only `c_{m+1} = c_val`, so both survive unchanged. W-9's cocycle semantics and the residue-chain statement survive. **JC-LOAD is not weakened; its load-set obstruction is now explicitly respected rather than contradicted.**”

**SUPERSESSION KIND: `partial-withdrawal`** — a proof route replaced with the conclusion preserved and the invalid step named.

**★ ORCHESTRATOR VERIFICATION, quoted (shard 3, L3041–3048):** “Annex #4's quotient route re-checked (the defining equation holds after TC-3, so only the congruence descends; `A(λ,N)` and `a_N` in `K_m^*` cancel in `K`, giving `c = q(A(γ,γ′)) = c_val` exactly, with the polynomial-equality display scoped to `δ < g_m` — **now consistent with JC-LOAD's RAW ⟺ δ < g_m rather than contradicting it**, and the C4 counter-configuration (`g_m = 1, δ = 1`: `deg A = 1` vs `deg c̃ < 1`) is resolved as a congruence, not an equality)”.

**INDEPENDENT CHECK BY THIS COMPILER:** at `g_m = 1, δ = 1`, `A(γ,γ′) = (u/a_λ)y^1` has `deg = 1`, while `c̃(y)` is the canonical representative of `c ∈ K` of degree `< g_m = 1`, i.e. **a constant**. **So `c̃ = A` is impossible as a polynomial equality while `c̃ ≡ A (mod ψ_m)` is unproblematic** — the counter-configuration is exact, and it is precisely JC-LOAD's load set. ✔

**DERIVATION:** As displayed, with the `Apply ρ_{λ+N}`-onward span replaced by Annex #4's quotient route.

**RESOLUTION TRACE:** statement lines 1673–1710; **correction site 2840–2884 (Annex #4, shard 3)**; JC-LOAD 859–924 (`.62`); the offset lemma 1747–1760 (`.88`); the verification record 3039–3059 (shard 3).

**TEETH:** **P5-OB6 0/669** — and note that the instrument computed both sides independently and agreed, **so the machine never saw the defect**: the error was in the written route, not in the identity. **Disposition: AUDIT — decorrelated-model audit; the strongest single argument in this note for rule 27.**

---
### EFF.GRTJC.86  [changes-record]  §4.1 — the two remarks, with r1/G7's struck identifications

**CANONICAL STATEMENT:** verbatim, lines 1712–1745.
**FORM:** bold-headed remarks with a struck passage and its `[r1, G7]` replacement.

> “*Two remarks the design note asked for.* (a) ~~The a_λ's — the anchor's own digit
> constants, i.e. the ε-normalization the harness carries — **cancel** because both
> reads in c_val sit on the SAME line λ; this is why no coboundary condition is
> needed, and it is the general-m form of the ε-collapse J-B proved
> unconditionally (JB-EPS).~~ **[r1, G7 — the two identifications inside that
> sentence are STRUCK as unproved; W-8 needs neither.]** Struck: (i) the apposition
> identifying a_λ = 𝑅_λ(φ_λ) with "the ε-normalization the harness carries", and
> (ii) the claim that the cancellation is "the general-m form of" JB-EPS — JB-EPS
> is a statement about the print-twist cocycle
> (t_m(V+V′) − t_m(V) − t_m(V′) = ε′, GRTJB §5, unconditional at every m ≥ 1) and
> so about a different object; **importing J-B's authority for this step was
> unwarranted.** What is TRUE, and all W-8 uses, is: **both reads in c_val are taken
> at the SAME line λ = γ+γ′ by the definition of c_val, so the single constant a_λ
> cancels in the ratio** — definitional, hence no coboundary condition.”

**★ “IMPORTING J-B'S AUTHORITY FOR THIS STEP WAS UNWARRANTED” — a self-caught borrowed-authority defect, and the cross-read notes it.** **GRTJB's JB-EPS is about the print-twist cocycle; GRTJC's `a_λ`-cancellation is about the anchor's digit constant on one line.** Different objects. **The true reason is definitional and one line long: both reads sit on the SAME line, so the single constant cancels.** **This is the second J-B ↔ J-C interface point** (the first is `.79`), and it is a NEGATIVE one: **a place where GRTJC initially over-claimed a J-B connection and then withdrew it.**

**The sharper true statement is then recorded (lines 1726–1732):** what IS additionally proved — **conditional on `(DMULT-s)`, the MEASURED tier** — is JC-COB's statement that “the a's do not merely cancel, they ARE the inner factor”.

**Remark (b) (lines 1732–1745)** records the footprint correction: C15's separation stands; what is used is `(COORD-B)+(MULT-B)`, i.e. the carrier-level content — with the `[r2, G-4]` correction of a footprint sentence that “contradicted r1's own headline”.

**SUPERSESSION KIND:** `counter re-reading` ×2 (two unproved identifications struck) + `inventory completion` (the footprint sentence regenerated).

**CONDITIONALITY:** The sharper statement rides `(DMULT-s)` and is therefore MEASURED-tier only.

**DERIVATION:** The surviving claim is definitional.

**RESOLUTION TRACE:** statement lines 1712–1745; the disposition 402–403 (r1/G7, shard 1 `.33`) and 464–469 (r2/G-4); JC-COB 1335–1352 (`.19`); the GRTJB object `spec/EFF-GRTJB-s2of3.md` `.46`.

XREF: `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md:JB-EPS` — grep-verified count **30**.

**TEETH:** none of its own; R1-COB measures the sharper statement.

---
### EFF.GRTJC.87  [lemma]  §4.2 — the offset-transport lemma

**CANONICAL STATEMENT:** verbatim, lines 1749–1760.
**FORM:** bold-headed lemma.

> “*Statement.* For λ ∈ W and N ≡ 0 (mod E), N ≥ wΦ_{NR}: s_{NR}(N) = 0,
> δ(λ,N) = 0, A(λ,N) is a **constant**, and multiplication by X_N carries ρ_λ
> isomorphically onto ρ_{λ+N} up to that constant — in particular it preserves
> y-degrees.
>
> *Proof.* s_{NR}(N) = 0 by JC-FIB (E | N); then s_{NR}(λ+N) = s_{NR}(λ)
> (JC-PER), so δ(λ,N) = 0 and JC-SPAN gives A(λ,N) constant. Apply ~~(MULT)~~
> **(MULT-B)|gr [r2, G-4]** with ρ_N(in X_N) = 1/a_N ∈ K_m^*. ∎”

**★ SMALL BUT LOAD-BEARING IN THREE PLACES: it is the step JC-LOAD's ⟸ direction rides (and the step r3/G-1 re-routed to), the step (‡) uses in W-8's proof, and the step Annex #4's repaired route uses to cancel `A(λ,N)`.** “in particular it preserves y-degrees” is what makes the JC-LOAD dichotomy a statement about `δ` alone.

**CONDITIONALITY:** Rides `(MULT-B)`, hence `(DMULT-w)`.

**DERIVATION:** Displayed; three cited steps (JC-FIB, JC-PER, JC-SPAN) plus `(MULT-B)|gr`.

**RESOLUTION TRACE:** statement lines 1749–1760; consumed at 885–889 (`.62`'s re-routed step), 1691–1695 (`.85`), and Annex #4's route (shard 3).

**TEETH:** the instrument's **P2-OFF 0/116** (constants independent of the scalar offset) and **P0-SCAL 0/293** (scalar multiplicativity in gr), plus this note's family JC4.

---
### EFF.GRTJC.88  [lemma]  §4.3 J-C(iii) — the residue chain

**CANONICAL STATEMENT:** verbatim, lines 1764–1771.
**FORM:** paragraph.

> “The chain used on the gr side is K_0 = k_0[x]/(Φ̄_0) and K_{j+1} = K_j[y]/(ψ_j)
> (§1), which is the classifier's residual tower `ResidueTower` by construction of
> the type: ψ_j is the residual polynomial of Φ_{j+1} at level j, and TC-3's
> identification Δ/(ψ_m) ≅ K_{m+1} is (IN-3)(d). Compatibility with (i)/(ii)'s
> scalars is the statement that the K_m ⊂ K_{m+1} used by JC-CARRY-m's inner factor
> is the same inclusion — true by construction, since the inner unit is literally a
> product of the letters z_1..z_m of the same tower. **GRADE: PROVED, general m,
> by construction — no independent content beyond the identification (IN-3)(d).**”

**★ THE GRADE LINE IS UNUSUALLY HONEST: “no independent content beyond the identification (IN-3)(d)”.** The clause is true by construction; the only imported fact is Thm 4.8/Cor 4.9.

**CONDITIONALITY:** Consumes `(IN-3)(d)` — **PDF-VERIFIED as a pair-cite at Annex #3** (shard 3), with the one line-pin slip on Cor 4.9 recorded at shard 1 `.43` (note says @1153; actual @1151; **content EXACT**).

**DERIVATION:** By construction, plus `(IN-3)(d)`.

**RESOLUTION TRACE:** statement lines 1764–1771; `(IN-3)(d)` 547–548 (shard 1 `.43`); **Annex #3's verification 2809–2815 (shard 3)**.

XREF: `docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt` **line 1136** (Thm 4.8) and **line 1151** (Cor 4.9) — **both re-read EXACT at HEAD by this compiler**; **line 862** (the §3.3 definition of `ψ_i`) — **EXACT**.

**TEETH:** JC6 indirectly; the identification is definitional.

---
### EFF.GRTJC.89  [lemma]  ★★★ COROLLARY W-9 — THE FOUR SUPPLY CLAUSES (special-care unit)

**CANONICAL STATEMENT:** **verbatim and UNTRUNCATED**, lines 1777–1788 — the complete face box, exactly the span WELDZERO cites.
**FORM:** display (a blockquoted face box).

> “**COROLLARY W-9.** Given W-6, W-7, W-8: (i) c_{m+1} descends to a map
> ℤ/E × ℤ/E → K^* and **is a 2-cocycle**: c(a,b)c(a+b,c) = c(b,c)c(a,b+c) — this
> is [ILN]†'s COR-2, and on the gr side it is nothing but **associativity of
> gr(w)'s multiplication**; (ii) its y-degree part δ satisfies the integer
> cocycle identity δ(a,b) + δ(a+b,c) = δ(b,c) + δ(a,b+c) (the {0,1}-valued
> carry cocycle); (iii) 𝒜(T) is the **twisted group algebra** K^{c}[ℤ/E] of the
> abscissa-coset group over the carry cocycle; (iv) COR-4's monodromy is the
> **gauge period**: φ_{γ+E} = π·φ_γ (JC-PER) is the period, in(π) is the
> gauge unit of degree E (JC-DOM), and the E-fold orbit product
> ζ_T := ∏_{k=1}^{E−1}c(1,k) is exactly the K-scalar by which the E-fold anchor
> product differs from the π-power that TC-2 sets to 1.
> **GRADE: PROVED given W-6..W-8 (general m), S-priced as the blueprint says.**”

**★★ SOURCE-RANGE VERIFICATION (the charge's special-care requirement).** `WELDZERO_2026-08-14.md` L151 cites this as “`GRTJC_PROOF_2026-08-08.md` **L1777–1788**”. **This compiler re-read GRTJC L1777–1788 at HEAD: the range opens exactly at `> **COROLLARY W-9.** Given W-6, W-7, W-8: (i) …` and closes exactly at the `> **GRADE: …**` line. The four clauses lie wholly inside. WELDZERO's citation is EXACT, and its quotation (elided with `…`) alters no wording.** ✔

**Double-emission (rule 14) — the four supply clauses as a `[TABLE]`, with per-clause consumer and replacement.** **This is the table the charge asks for.**

| clause | exact supply | proved by | what a consumer takes from it | WELDZERO's in-cone replacement (COROLLARY WZ-B) | class |
|---|---|---|---|---|---|
| **(i)** | `c_{m+1}` descends to `ℤ/E × ℤ/E → K^*` and **is a 2-cocycle**, `c(a,b)c(a+b,c) = c(b,c)c(a,b+c)`; **= [ILN]†'s COR-2**; on the gr side **nothing but associativity of gr(w)'s multiplication** | JC-PER (descent) + associativity of `gr(w)` expanded with `(MULT-B)|gr`, reduced mod `ψ_m` | “a graded ring in which the residual assembly is associative/multiplicative” | **WZ-1**: `gr(L)` is a commutative graded ring with all nonzero homogeneous elements invertible — **associativity is free**. The concrete cocycle is `τ(a,b)` with its normalized law, **WZ-2(a)** — a monomial identity | **elementary** |
| **(ii)** | the y-degree part `δ` satisfies the INTEGER cocycle identity `δ(a,b) + δ(a+b,c) = δ(b,c) + δ(a,b+c)` — **the {0,1}-valued carry cocycle** | take y-degrees in the same Δ-identity (`deg A(a,b) = δ(a,b)` by JC-CARRY-m); **degrees add, so the identity is the additive one** | “the integer wrap bookkeeping” | **WZ-2(a)**: `wrap(a,b) = ⌊(i(a)+i(b))/e₁⌋ ∈ {0,1}` with the additive identity, from `i(a)+i(b) = i(a+b) + e₁·wrap` | **elementary** |
| **(iii)** | `𝒜(T)` is the **twisted group algebra `K^{c}[ℤ/E]`** of the abscissa-coset group over the carry cocycle | restatement of W-7's Ψ | “one K-line per dv-height”, i.e. `dim_K 𝒜(T) = E` | **WZ-1(c) + LEMMA GENHN-2**. GENHN already records the implication in this direction: “**W-9's `dim_K 𝒜(T) = E = e₁` is this statement's graded shadow (cited as frame)**” | **already in-cone** |
| **(iv)** | COR-4's monodromy is the **gauge period**: `φ_{γ+E} = π·φ_γ` is the period, `in(π)` the gauge unit of degree `E`, and `ζ_T := ∏_{k=1}^{E−1}c(1,k)` is exactly the K-scalar by which the E-fold anchor product differs from the π-power TC-2 sets to 1 | JC-PER + JC-DOM + iterating `(MULT-B)|gr` along the orbit | — | **NOT CONSUMED**: “no occurrence in S6.1. The wrap letter layer 1 actually uses is `ϑ_t`, **derived** at WZ-2(c) from the monomials” | **n/a** |

**★ THE CONSUMPTION FACTS, verified by this compiler against three sources:**
1. **WHERE W-9 is consumed:** `runs/qgen/WELD_FACE_AUDIT.md` L123 — “**COROLLARY W-9 / `GENHN-BOX-2`** (GRTJC's twisted algebra at **GENHN-4 layer 1, μ ≥ 3**) — **R&C — the only weld face inside a count law**”. **W-9 is the ONLY GRTJC face that reaches a count law**, and it does so at exactly one site.
2. **The grep footprint is one line.** WELDZERO L146–149: “`W-9` occurs in GENHN S6.1 at **exactly one line (L874)**; layers 2 and 3 (L890–904) cite no weld label. GENHN-BOX-2's own wording agrees (‘layer 1’). **So the interface to be discharged is layer 1 and nothing else.**”
3. **WHICH TIER W-9 rides:** `WELD_FACE_AUDIT.md` L106 — “The one reachable GRTJC face, **COROLLARY W-9, rides the citable tier**” `(DMULT-w)`, **not** the measured `(DMULT-s)`. **Consistent with this note's own blast radius** (JC-BOX-3 item 3, shard 3): “If **(DMULT-w)** failed …, **W-8 and W-9 fail together**; if only **(DMULT-s)** failed …, **the structural clauses stand**.” ✔
4. **WELDZERO's method note, quoted because it bounds what the replacement achieves:** “WZ-B does **not** re-derive GENHN's layer-1 *prose* from weld-free inputs — that is what SG-2 tried and found impossible. **It proves layer 1's *conclusion* from scratch.** Any unstated content hiding inside ‘the organizing frame' is therefore **bypassed**, not audited.”

**CONDITIONALITY:** **PROVED GIVEN W-6..W-8** — the corollary adds no new input; it inherits the whole stack. **“S-priced as the blueprint says”** is the blueprint's own costing. **Everything W-9 rides, W-8 and W-7 ride: `(DMULT-w)`, `[ILN]†`'s scored stratum for the VALUE half, `e_m ≥ 2` for the sharp forms, and — via W-8 — Annex #4's repaired route.** **Annex #4 explicitly preserves it: “W-9's cocycle semantics and the residue-chain statement survive.”** **Annex #5 likewise: “W-7, W-8, and W-9 consume the factor's value or shape, not the refuted universal interpretation, and survive.”** **Annex #6 likewise: “(MULT-B), JC-IND, W-7's bijectivity, and W-9 survive at every `m` by (RM).”** **Three annexes, three explicit survivals.**

**DERIVATION:** `.90`.

**RESOLUTION TRACE:** statement lines 1777–1788; proof lines 1790–1799 (`.90`); W-6 664–699 (`.54`), W-7 1419–1458 (`.75`), W-8 1658–1671 (`.84`); the consumers `lean/notes/openmath/WELDZERO_2026-08-14.md` L151–156 and L425–443, `runs/qgen/WELD_FACE_AUDIT.md` L106, L123; the annex survivals 2884, 2911, 2990 (shard 3).

XREF: `lean/notes/openmath/WELDZERO_2026-08-14.md` — **file EXISTS**; `runs/qgen/WELD_FACE_AUDIT.md` — **file EXISTS**; `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md:ITER-LAW-n` — count **11** (COR-2's home).

**TEETH:** **JC7** — “COROLLARY W-9: the mod-E 2-cocycle identity …, the integer carry identity `δ(r,s)+δ(r+s,t) = δ(s,t)+δ(r,s+t)`, and the E-fold chain `c(φ_1^E) == ∏_{k=1}^{E−1}c_val(γ_1,kγ_1)` (monodromy = gauge period, **two ways**; E ≤ 8)” — **581 samples, 0 violations; 261 triples satisfy BOTH the K^*-cocycle identity and the integer carry identity; the E-fold chain matched the orbit product on all 15 rows with E ≤ 8.** Disposition: **executable regression covering all four clauses, with clause (iv) checked two independent ways.**

---
### EFF.GRTJC.90  [lemma]  W-9's proofs — four one-liners

**CANONICAL STATEMENT:** verbatim, lines 1790–1799.
**FORM:** `*Proofs.*` block.

> “*Proofs.* (i) Descent is JC-PER. Associativity of gr(w) gives
> (in φ_a·in φ_b)·in φ_c = in φ_a·(in φ_b·in φ_c); expanding both with ~~(MULT)~~
> **(MULT-B)|gr [r2, G-4]**
> yields A(a,b)A(a+b,c) = A(b,c)A(a,b+c) in Δ, and reducing mod ψ_m gives the
> K^*-cocycle identity. (ii) Take y-degrees in the same Δ-identity (JC-CARRY-m:
> deg A(a,b) = δ(a,b)) — degrees add, so the identity is the additive one. (iii)
> Restatement of W-7's Ψ. (iv) With the representative γ_0 = 0 ∈ W we have
> φ_0 = 1, and JC-PER gives φ_{kE} = π^k, whose gauged class is 1; iterating
> ~~(MULT)~~ **(MULT-B)|gr [r2, G-4]** along the orbit of the class 1 gives
> [φ_1]^E = ζ_T·[φ_0] = ζ_T. ∎”

**★ THE ELEGANCE IS THE POINT, and it is what makes WELDZERO's replacement feasible:** **(i) IS associativity** — the cocycle identity is not an extra hypothesis but a consequence of the ring being a ring. **(ii) is the SAME identity read in degrees** — one Δ-identity yields both the `K^*`-cocycle law and the integer carry law. **That is why WELDZERO can replace (i) with “associativity is free” in a graded field and (ii) with a monomial wrap identity.**

**CONDITIONALITY:** All four ride `(MULT-B)|gr`, hence `(COORD-B)(2)`, hence `(DMULT-w)`. **Clause (iii) is a restatement, so it carries W-7's scopes exactly.**

**DERIVATION:** Displayed in full above; each clause one line.

**RESOLUTION TRACE:** statement lines 1790–1799; JC-PER 756–772 (`.57`); `(MULT-B)|gr` 1327–1333 (`.71`); JC-CARRY-m 1479–1489 (`.77`); W-7's Ψ 1419–1458 (`.75`).

**TEETH:** **JC7's two-way check of clause (iv)** — the E-fold chain computed both as `c(φ_1^E)` and as the orbit product `∏_{k=1}^{E−1}c_val(γ_1,kγ_1)`, matching on all 15 rows with `E ≤ 8`. **A genuinely independent second computation of the monodromy.**

---
### EFF.GRTJC.91  [supplier-finding]  ★ FINDING JC-F1 — the blueprint's cyclic fence, corrected

**CANONICAL STATEMENT:** verbatim, lines 1801–1824.
**FORM:** bold-headed finding + display + an `[r1, F1]` dimension-count re-derivation.

> “**FINDING JC-F1 (blueprint display correction, REVIEW-OWED — read with §6).**
> (iv)'s computation has a consequence the blueprint's cyclic-fence wording does
> not survive as literally stated. Put v := [φ_{γ_1}] (the anchor class of the
> residue class 1 ∈ ℤ/E). Then v^k = β_k·[φ_{γ_k}] with β_k := ∏_{i=1}^{k−1}c(1,i)
> ∈ K^* for k = 1..E−1, so {1,v,…,v^{E−1}} is a K-basis of 𝒜(T) and v^E = ζ_T:
>
>     **𝒜(T) ≅ K[v]/(v^E − ζ_T) as a K-algebra — at EVERY composite stage.**
>
> So "𝒜(T) is NOT F′[u′]/(u′^E − ζ′)" cannot be read as an abstract-isomorphism
> claim; it is (and, in its own adjudication procedure, always was) a claim about
> the ANCHOR-INDEXED presentation — see §6. Nothing measured is re-scored by this;
> what is corrected is a display, exactly as J-B's JB-BOX-1 corrected the J-B(iii)
> display.”

**★ A CONSEQUENCE OF W-9(iv) THAT REFUTES A BLUEPRINT DISPLAY: as an ABSTRACT K-algebra, `𝒜(T)` IS cyclic at every composite stage.** So the blueprint's fence — “`𝒜(T)` is NOT `F′[u′]/(u′^E − ζ′)`” — **cannot be an abstract-isomorphism claim**; it is a claim about the anchor-INDEXED presentation. **The note's own parallel is exact: “exactly as J-B's JB-BOX-1 corrected the J-B(iii) display”** — both notes found and corrected a blueprint display, and both boxed it REVIEW-OWED.

**CONDITIONALITY:** **REVIEW-OWED** (JC-BOX-5): “it must be adjudicated before any text repeats the fence in the abstract-isomorphism wording.” **The dimension count it needs was itself repaired at r1** (lines 1815–1824): the input `dim_K 𝒜(T) = E` came from the refuted “each `A_ν` is 1-dimensional on `gr_λ`” and now comes from §2.10's repaired display. **“THROUGH, general m, on (DMULT-w) + JC-IND.”**

**DERIVATION:** Displayed: `v^k = β_k·[φ_{γ_k}]` with `β_k := ∏_{i=1}^{k−1}c(1,i) ∈ K^*`; the powers lie in pairwise distinct `ℤ/E`-degrees, hence independent; so `{1,v,…,v^{E−1}}` is a K-basis and the K-algebra map `K[v]/(v^E − ζ_T) → 𝒜(T)` is well defined, surjective, and injective by comparing dimensions `E = E`.

**RESOLUTION TRACE:** statement lines 1801–1824; W-9(iv) 1785–1788 (`.89`); §6's law 1848–1916 (`.93`, `.94`); the box 2028–2038 (JC-BOX-5, shard 3); consumer row 4 of `.74`.

**TEETH:** **JC8** (“a CYCLIC verdict ⟹ the collapse geography; every structure constant is a UNIT so JC-F1's power basis exists”) — 898 samples; **its unit half was VACUOUS as coded (r1/G3) and was replaced by R1-UNIT + tooth T4**. The E-fold chain leg (15 rows with `E ≤ 8`) is real evidence for the power basis.

---
### EFF.GRTJC.92  [supplier-finding]  ★ FINDING JC-F2 — the inherited “degree-0 component” defect

**CANONICAL STATEMENT:** verbatim, lines 1826–1842.
**FORM:** bold-headed finding.

> “**FINDING JC-F2 [r1, G2] (blueprint display correction, REVIEW-OWED — the second
> inherited-display defect, same treatment as JC-F1).** The corpus defines the
> carry-algebra target as "the K-span of the anchor classes **in the degree-0
> component** of the TC-transported gr(w)" — verbatim in `GRW2_TIE_DESIGN` §S2.2,
> the blueprint §S2.3, the GRTJC brief, and (until r1) §1 and W-7 of this note.
> **That reading is wrong, and it contradicts this note's own OB-4 proof:** the
> anchor class of γ lives in the ℤ/E-degree γ mod E (JC-GAUGE + JC-FIB), which is
> the degree-0 component only for ν = 0; under the literal reading the entire
> degree-separation argument of §3.4 is unavailable and W-7's Ψ would map an
> E-dimensional carrier onto a single K-line (false for E > 1). r0 used the
> CORRECTED reading in its proofs while displaying the inherited one — PE1's GAP 2.
> **The correct definition** (now in §1 and W-7): 𝒜(T) := the K-span of the anchor
> classes across ALL ℤ/E-degrees of the TC-transported ring, which by §2.10 [r1] is
> the whole transported ring, of K-dimension E. Nothing measured moves; no clause's
> proof changes. **REVIEW-OWED**: the design note, the blueprint and the brief
> carry the defective display and must be corrected there before any downstream
> text repeats it (JC-BOX-5's JC-F1 rider now covers JC-F2 as well).”

**★ THE DEFECT IS INHERITED FROM THREE UPSTREAM DOCUMENTS AND IS STILL LIVE THERE AT HEAD.** All three verified to exist: `GRW2_TIE_DESIGN_2026-08-08.md`, `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md`, `docs/in-progress/GRTJC_BRIEF_2026-08-05.md`. **The blueprint is one of the three — and the chapter blueprints are about to be written from it** (shard 1 OPEN-CALL 5).

**★ THE COUNTERFACTUAL IS DECISIVE:** under the literal reading, **W-7's Ψ would map an E-dimensional carrier onto a single K-line — false for `E > 1`, which is the standing hypothesis.** So the inherited display is not merely imprecise; it is inconsistent with the theorem it defines the target of.

**CONDITIONALITY:** **“Nothing measured moves; no clause's proof changes.”** r0 used the corrected reading in its proofs while displaying the inherited one — **a display/proof divergence, caught by PE1 as GAP 2.**

**DERIVATION:** The degree-separation argument (§3.4): `[φ_{γ_ν}] ∈ 𝒜_ν` with `ν = γ_ν mod E`, pairwise distinct by JC-FIB.

**RESOLUTION TRACE:** statement lines 1826–1842; the corrected definition 644–654 (shard 1 `.52`) and 1421–1424 (`.22`); the disposition 387–390 (r1/G2, shard 1 `.33`); the box 2028–2038 (JC-BOX-5, shard 3).

XREF: `GRW2_TIE_DESIGN_2026-08-08.md` — **EXISTS** · `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md` — **EXISTS** · `docs/in-progress/GRTJC_BRIEF_2026-08-05.md` — **EXISTS**.

**TEETH:** none — a display defect. Disposition: **AUDIT — in-house hostile pass** (PE1 GAP 2), with a **standing REVIEW-OWED obligation at three external documents**.

---
### EFF.GRTJC.93  [definition]  §6 — the cyclic fence and the (CYC) property

**CANONICAL STATEMENT:** verbatim, lines 1848–1863.
**FORM:** paragraph + bold-headed definition.

> “The blueprint carries the fence as LAW: *at composite stages 𝒜(T) is NOT
> F′[u′]/(u′^E − ζ′) (adjudicated NOT-CYCLIC at 22/28 towers, value set
> {z₁, z̄, z̄z₁^b}, byte-frozen); only the last-read layer is cyclic.* The
> instrument, computing the same adjudication from a completely different side
> (gr-side certification instead of the harness value cocycle), returned
> **14 NOT-CYCLIC / 6 CYCLIC / 9 UNDECIDED**, with the 6 cyclic rows
> C2A/C2E/C2G/C2J/C3A/C4A. Both records stand. Here is the law that has both as
> instances.
>
> **(CYC), the property actually adjudicated (definition, quoted from both
> runners).** The anchor-indexed presentation is *cyclic* iff
> (α) image(c) ⊆ {1, ζ′} for a single ζ′ ∈ K^*, **and** (β) there are integers
> σ_r (σ_0 = 0) with σ_r + σ_s = σ_{r+s} + E·carry(r,s) reproducing the table.
> This is the **letter-monomial** shape: the anchors are, up to ζ′-power
> normalization, the power basis of one generator — precisely the shape D-REAL
> supplies one level down (K_{m+1}[u]/(u^{e_m} − z̄), anchors = powers of u).”

**★ TWO RECORDS, TWO ROSTERS, ONE LAW — and the note reconciles them without amending either.** The byte-frozen record says 22/28 NOT-CYCLIC; the instrument, “computing the same adjudication from a completely different side”, says 14/6/9. **“Both records stand.”**

**★ THE (CYC) DEFINITION IS TWO-PART AND BOTH PARTS MATTER** — (α) a single non-1 value, AND (β) an integer relabeling reproducing the table. **r3/G-8 (shard 1 `.29`) corrected the obstruction trigger precisely because clause (β) can fail alone** (C2C, C3I).

**ARITHMETIC AUDIT (rule 22):** 14 + 6 + 9 = **29** ✔ (the instrument's roster). The 6 cyclic rows are named and counted: C2A, C2E, C2G, C2J, C3A, C4A = **6** ✔.

**CONDITIONALITY:** The two rosters are different and the note says so; it claims only that both are instances of one law.

**DERIVATION:** Definition, “quoted from both runners”.

**RESOLUTION TRACE:** statement lines 1848–1863; the law 1865–1910 (`.94`); `(IN-2)`'s D-REAL 519–526 (shard 1 `.42`); §9.2's reproduction 2134–2142 (shard 3).

XREF: `lean/notes/openmath/GRB_ORDER2_2026-08-05.md:D-REAL` — count **44**.

**TEETH:** JC8 (898 samples) reproducing the instrument's split exactly — “**the same six rows, and the same 14/6/9 split, as the instrument's MT2**”, with the disclosure that this is “a *consistency* check of W-8, not a second independent measurement of the split”.

---
### EFF.GRTJC.94  [lemma]  ★ LAW JC-CYC — five parts, each graded

**CANONICAL STATEMENT:** verbatim, lines 1865–1910 — the five clauses (a)–(e) with their grades and the `[r3, G-8]` trigger correction.
**FORM:** bold-headed law + five bulleted clauses.

**Double-emission (rule 14) — the five clauses as a `[TABLE]` with their grades:**

| clause | grade | content |
|---|---|---|
| **(a)** | **PROVED, general m** | As an abstract K-algebra `𝒜(T) ≅ K[v]/(v^E − ζ_T)` **always** (JC-F1). “Hence the fence's content is (CYC), not abstract cyclicity, and **the operative dead route is the letter-monomial one** … The design note's S4 dead end (‘one-anchor-unit normalization does not trivialize a coset progression') is exactly this, and **it stays dead**.” |
| **(b)** | **PROVED, general m — the obstruction direction** | If the measured value table has **two distinct non-1 VALUES**, (CYC) fails by (α). ~~“two multiplicatively distinct (δ, D)-words”~~ **[r3, G-8 — FALSE as stated: two multiplicatively distinct words can evaluate to {1, v}, a SINGLE non-1 value, where (α) holds with ζ′ = v and (CYC) can only fail through (β); clause (d) exhibits exactly that genre on the note's own roster (C2C, C3I)]** |
| **(c)** | **PROVED, general m — the twist-blind direction** | If `\|K\| = 2` then `K^* = {1}`, so `c ≡ 1` and (CYC) holds with `ζ′ = 1, σ ≡ 0`. Likewise if the table has at most one non-1 value AND (β) is solvable |
| **(d)** | **MEASURED, m ≤ 3 — ONE-DIRECTIONAL** | On both rosters the cyclic side is CONTAINED in the twist-blind/collapse geography: every CYCLIC row has `\|K\| = 2` (C4A), or `g_m = 1` so `K_{m+1} = K_m` and `z̄ ∈ ⟨z_1⟩` (C2A/C2E/C2G/C3A), or `e_0 = 1` (C2J) — **0 violations of “CYCLIC ⟹ collapse” on 29 rows.** **“The CONVERSE IS FALSE and this note does not claim it”**: **13 collapse-geography rows are NOT-CYCLIC** (C2B, C2C, C2D, C2H, C3D, C3E, C3F, C3H, C3I, C4B, C4G, I4B, I4C), by two visible mechanisms — **≥ 2 distinct non-1 values (up to 7 on I4C)**, or **a single value whose carry pattern no integer relabeling realizes (C2C, C3I)**. **The general form of the inclusion is OPEN (JC-BOX-5), and its measured resolution is LOW: only 2 of 29 rows lie off the collapse geography** |
| **(e)** | consistency record | The 22/28 adjudication and its value set `{z₁, z̄, z̄z₁^b}` are **unamended**; no row is re-scored; the instrument's 14/6/9 “is a different roster and a different computation, and it **reproduces the same SPLIT SHAPE**”. **The fence's program consequence is unchanged: any route through a letter-monomial cyclic presentation at a composite stage is DEAD**, and (b) now says why |

**★ CLAUSE (d) IS THE MODEL OF A HONESTLY-STATED ONE-DIRECTIONAL LAW:** the inclusion is measured (0 violations on 29 rows), **the converse is explicitly FALSE with 13 named counterexamples**, the general form is OPEN, **and the measured resolution is disclosed as LOW — “only 2 of 29 rows lie off the collapse geography”, so the law “was tested against few potential counterexamples”** (§9.2's finding 2). **A law, its refuted converse, its open general form and its weak evidence, all in one clause.**

**ARITHMETIC AUDIT (rule 22):** cyclic rows accounted: C4A (`|K| = 2`) 1 + C2A/C2E/C2G/C3A (`g_m = 1`) 4 + C2J (`e_0 = 1`) 1 = **6** ✔ matches the 6 cyclic rows of `.93`. NOT-CYCLIC collapse rows named = C2B, C2C, C2D, C2H, C3D, C3E, C3F, C3H, C3I, C4B, C4G, I4B, I4C = **13** ✔. Off-collapse rows = **2** (C2I, C4I per §9.2 finding 2) ✔, and 6 + 13 + 2 = 21; the remaining 8 of 29 are UNDECIDED-and-in-collapse (9 UNDECIDED total, of which C4I is the off-collapse one) — **consistent**. ✔

**CONDITIONALITY:** **(a)(b)(c) PROVED at general m; (d) MEASURED at m ≤ 3 and ONE-DIRECTIONAL; the general inclusion OPEN (JC-BOX-5).** **The 9 UNDECIDED rows are “a compute fence on (β)'s relabeling search”, not a finding.**

**DERIVATION:** (a) from JC-F1. (b) from the (CYC) definition's clause (α). (c) from `|K| = 2 ⇒ K^* = {1}`. (d) measured. (e) record.

**RESOLUTION TRACE:** statement lines 1865–1910; JC-F1 1801–1813 (`.91`); the disposition 339–342 (r3/G-8, shard 1 `.29`); §9.2's two findings 2144–2158 (shard 3); the box 2028–2038 (shard 3).

**TEETH:** **JC8** (898 samples, 0 violations for the ONE falsifiable half — “no CYCLIC verdict off the collapse geography”, 29 rows) **+ the note's own battery-driven finding 1**, which REFUTED the converse. Disposition: **measurement, one-directional, with the converse refuted by the same battery and the resolution disclosed as low.**

---
### EFF.GRTJC.95  [scope record]  §6 — the consequence for the case split

**CANONICAL STATEMENT:** verbatim, lines 1912–1916.
**FORM:** bold-headed paragraph.

> “**Consequence for the case split.** The genre column "cyclic / not-cyclic /
> undecided" is carried into §7, and the cyclic side is *not* only the last-read
> layer: it includes composite stages whose residual tower collapses (g_m = 1 ⟹
> K_{m+1} = K_m). That was the instrument's M5, and it is now a stated law with a
> proved obstruction direction.”

**CONDITIONALITY:** **This CORRECTS the blueprint's “only the last-read layer is cyclic”** — composite stages with a collapsing residual tower are cyclic too. **A third blueprint-display correction in this note**, after JC-F1 and JC-F2, though this one is folded into the law rather than boxed as a FINDING.

**DERIVATION:** From JC-CYC(c)(d).

**RESOLUTION TRACE:** statement lines 1912–1916; the law 1865–1910 (`.94`); §7's genre column 1920–1934 (`.96`).

**TEETH:** the instrument's M5.

---
### EFF.GRTJC.96  [TABLE]  §7 — the eleven-genre case split

**CANONICAL STATEMENT:** verbatim, lines 1920–1934 — the header and the eleven-row table.
**FORM:** display (an H2 head) + Markdown table.

> “## §7. THE CASE SPLIT (derived FROM the instrument's genre censuses; the case list matches the observed genre list)”

`[TABLE]` transcribed (long cells condensed with `…`, every figure and every verdict preserved):

| # | genre | rows / pairs | status |
|---|---|---|---|
| 1 | `g_m ≥ 2`, `δ = 0` | ~~C2B/C2I/C3I/C4I…~~ **[r1, G4:** the runner's own per-row print contradicts that list — **the `g_m ≥ 2` rows are EXACTLY C2I (m = 1, E = 4) and C4I (m = 3, E = 16), 2 of 29**, the complement of the 27 `g_m = 1` stages (29 − 2 = 27, consistent); C2B and C3I belong to rows 3/4**]**; the majority of pairs on those two rows | JC-CARRY-m + JC-INNER; RAW-solvable; canonical outer/inner split — **PROVED** |
| 2 | `g_m ≥ 2`, `δ = 1` | the carry-boundary pairs on `g_m = 2` rows | `δ = 1 < g_m` ⟹ still RAW-solvable (**the smoke correction that sharpened the sealed identity from `{δ≥1}` to `{δ≥g_m}`**) — **PROVED** |
| 3 | `g_m = 1`, `δ = 0` | most pairs on the 27 `g_m = 1` stages | `K_{m+1} = K_m` collapse: value identity holds; the outer/inner split is canonical on the gr side (y-degree) but **NOT recoverable from the VALUE alone** — **PROVED, with the display fence** |
| 4 | **`g_m = 1`, `δ = 1` — the TC-3 load set** | **134 of 669 pairs, 0/29 set-mismatches** | THEOREM JC-LOAD: no pre-TC-3 scalar exists; the `ψ_m`-relation is unavoidable — **PROVED** (the case that makes TC-3 load-bearing) |
| 5 | top-flat stage `e_m = 1` | C4H (+ any I4x with `e_m = 1` — **[r1, G5]** the roster has **NONE**: C4H is the unique `e_m = 1` row) | `δ ≡ 0`; JC-SPAN gives `deg ρ ≤ 1` instead of the singleton; sharp form **MEASURED not proved** **[r2, G-7: and CONDITIONALLY CLOSED on (DMULT-w) since r1 — the two statuses coexist because they have different footprints]** — JC-BOX-4 |
| 6 | interior-flat legs `e_j = 1`, `j < m` | C2J, C3E, C4H | no special role; the [RMG] fenced-corner genre is inherited via J-B, not re-opened — **PROVED (no case owed)** |
| 7 | twist-blind `\|K\| = 2` | C4A | `c ≡ 1`; cyclic by JC-CYC(c); **MT3 skipped there (no nontrivial scalar class)** — **PROVED** |
| 8 | zero-class genre (SPAN-S) | 60 samples | the TC-3 kernel `ψ_m·Δ` (§2.10) — **PROVED AWAY**, not a failure genre |
| 9 | DCX / non-integral-D | **0 rows, 0 pairs observed** | existence + structure PROVED (§3.2); **the VALUE `c_T` is not claimed and has no machine support** — JC-BOX-2 |
| 10 | prime-residue-field rows (MT3's 9 escapes) | 9 rows, `\|K\| ∈ {3,5}` | a tooth-resolution artifact, not a clause genre — disclosed, JC-BOX-7 |
| 11 | UNDECIDED cyclic rows (`E > 8`) | 9 rows | compute fence on (β)'s relabeling search — **no clause depends on them** |

**★ THE SUBTITLE IS THE METHOD, and it is the “examples-first” directive applied: “derived FROM the instrument's genre censuses; the case list matches the observed genre list”.** **The cases are not invented and then checked; they are read off the measured genres and then accounted for.**

**MANDATORY ARITHMETIC AUDIT (rule 22):**
- `g_m ≥ 2` rows = **2** (C2I, C4I); `g_m = 1` stages = **27**; **2 + 27 = 29** ✔ and the note states the check itself.
- `e_m = 1` rows = **1** (C4H, unique per the r1 census R1-CEN) ✔ — hence JC-LOAD's theorem covers **28** rows ✔ (`.62` G5).
- Load set: **134 of 669 pairs, 0/29 set-mismatches** ✔ consistent with `.62`(c).
- MT3: 9 escapes ✔ consistent with `.83`'s 197/206.
- UNDECIDED: **9** ✔ consistent with `.93`'s 14/6/9.
- Genre 9: **0 rows, 0 pairs** ✔ consistent with `(IN-1)`'s census (shard 1 `.41`) — **and this is the genre with zero machine support.**
- **Genre count = 11**, matching the header's implicit claim that the case list matches the observed genre list ✔.

**CONDITIONALITY:** **Genre 9 is the exposed one** (proof-only, JC-BOX-2). **Genre 5's two coexisting statuses (MEASURED not proved / CONDITIONALLY CLOSED on `(DMULT-w)`) are deliberate** — “the two statuses coexist because they have different footprints”. **Annex #5 confirms genres 1–4 survive its re-display: “§7 genres 1–2 remain RAW-solvable and genres 3–4 retain the stated `g_m = 1` split.”**

**DERIVATION:** Per genre, at the cited clause.

**RESOLUTION TRACE:** statement lines 1920–1934; the dispositions 395–398 (r1/G4, G5, shard 1 `.33`), 479–480 (r2/G-7, shard 1 `.38`); the boxes 1946–2056 (shard 3); **Annex #5's sweep 2911 (shard 3)**.

**TEETH:** per genre; **genre 9 has NONE and the table says so.**

---
### EFF.GRTJC.97 — .104  [the eight honest boxes]  [fence ×8]

**MERGE NOTE:** the eight boxes are eight units (test 2: each is cited by name from §§2–7 and from the annexes; test 3: three carry live riders from different rounds). They are presented together here with a shared ledger, then each box's load-bearing content quoted.

`[TABLE — compiler ledger]` **The eight boxes.**

| unit | box | lines | subject | status at HEAD |
|---|---|---|---|---|
| `.97` | **JC-BOX-1** | 1940–1945 | proof scope vs machine scope | live |
| `.98` | **JC-BOX-2** | 1946–1951 | the off-stratum existence claim | **live; PROOF-ONLY with zero machine support** |
| `.99` | **JC-BOX-3** | 1952–1992 | the literature leg — **RE-CUT at r1 to APPLICABILITY, not literature truth** | live; **item 2 DISCHARGED by Annexes #2/#3** |
| `.100` | **JC-BOX-8** | 1993–2003 | what the r1 repair does NOT supply (three residues) | live; **residue (i) untouched by every runner** |
| `.101` | **JC-BOX-4** | 2004–2027 | the top-flat corner `e_m = 1 ∧ g_m = 1` | live; **CONDITIONALLY CLOSED on `(DMULT-w)`, open FGMN-free** |
| `.102` | **JC-BOX-5** | 2028–2038 | the cyclic characterization | live; **the general inclusion OPEN; JC-F1/JC-F2 REVIEW-OWED** |
| `.103` | **JC-BOX-6** | 2039–2048 | inherited conditionality, itemized | live; **the supplier grades in it are STALE** |
| `.104` | **JC-BOX-7** | 2049–2056 | standing fences; nothing fires | **the gate clauses live; the counter EXPRESSLY superseded by Annex #7** |

**`.98` — JC-BOX-2, quoted in full because it is the note's most exposed claim:**

> “* **JC-BOX-2 (off-stratum).** §3.2's existence/structure statement is strictly
>   wider than [ILN]†'s scope (it holds for every window pair, DCX or not,
>   D-integral or not); the VALUE statement §3.3 is exactly [ILN]†'s stratum. The
>   instrument's grid contained **0 DCX and 0 non-integral-D pairs**, so the wider
>   half has **no machine support whatsoever** — it is proof-only, and a hostile
>   pass should attack it there first.”

**`.99` — JC-BOX-3's three items, quoted at their load-bearing clauses:** “**WHICH OBJECT.** The note uses FGMN Thm 4.2 **only on `B = gr(w)[in(π)^{-1}] ≅ gr_{K[x]}(w)`** (LEMMA JC-LOC), **never on `gr_{O[x]}`**, and it uses it **only** through the single statement (DMULT) — **[r2, G-1]** in its CITABLE tier … The surjectivity half r0 also cited is now PROVED in-note (JC-BSURJ) …”; “**CITATION PRECISION — STANDING CODEX LEG (owed, unchanged in status).** The numbers … are **still not re-verified against a printed source**. … A numbering error would not by itself refute (DMULT) … but the note's citation would be wrong and must be re-pointed.”; “**WHAT DIES WITH IT.** If (DMULT-w) failed at composite order, (COORD-B)(2), (MULT-B), §§2.7–3.4, **W-8 and W-9 fail together**; if only (DMULT-s) failed (ω ≢ 1), JC-COB's sharp values and R1-COB's exact predicate fail while **the structural clauses stand**.” **★ Item 2 is DISCHARGED by Annexes #2/#3** (`.125`, `.126`). **★ Item 3 is the blast-radius sentence the weld audit cites** to establish that W-9 rides the citable tier.

**`.100` — JC-BOX-8's three residues:** “(i) the **606 skipped non-integral SPAN-M perturbations** … **no machine evidence** … ; (ii) **R1-PSIK-LO's one-sidedness** … the probe's own disclosed limitation; (iii) **JC-COB's second half** … rides [ILN]† in addition to (DMULT-s) …, and the identity is displayed, not consumed by any clause.”

**`.101` — JC-BOX-4's two coexisting statuses:** the corner is **MEASURED** (C4H: all pairs RAW-solvable, 0 violations) **and unproved** on the r0 proof, **but CONDITIONALLY CLOSED on `(DMULT-w)`** by a second, `e_m`-blind proof — “**the corner is CLOSED for a reader who grants (DMULT-w) … and stays OPEN for one who wants it independent of the FGMN input** — r0's proof and r1's proof have different footprints, and **the note keeps both**.” **Machine: R1-COB scores C4H's 24 grid pairs with the sharp form, 0 violations.**

**`.102` — JC-BOX-5:** “JC-CYC(b)(c) are proved; the general form of (d)'s **inclusion** (CYCLIC ⟹ collapse geography) is **OPEN**, its measured resolution is **low (only 2 of 29 rows lie off the collapse geography)**, and the **converse is FALSE** — 13 collapse-geography rows are NOT-CYCLIC. The 9 UNDECIDED rows are a compute fence. **JC-F1 … is a blueprint-display correction and is REVIEW-OWED** … **[r1, G2] The same rider now covers FINDING JC-F2** …, and **it must be fixed in those sources before any downstream text repeats it**.”

**`.103` — JC-BOX-6, the itemized inheritance:** “[ILN]† ACCEPTED but with its own residuals riding through: the open engine families **(RM-m, m ≥ 2)** and **(W-MULT-DCX-m)**, the fenced corners, DCX-(n) excluded, standard-lift only (so the **(ITER-LAW-LIFT)** residual — **open exactly at `g_0 = 1 ∧ δ_1 = 1`** — is displayed wherever a non-standard lift could enter). GRB/CARRY-1/D-REAL ACCEPTED-conditional on the GRB §0 ladder … **W-1/W-2/J-A/J-B at ATTEMPT (0/2)**, and §3.3's germ display additionally rides **JB-BOX-2's geography** ((VD-m) free only at m ≤ 1; JA-VDIND at m ≥ 2; JA-BOX-2's (R-coll) at m ≥ 3; the pinned-ℓ orbit; q ≤ qcap) and **JB-BOX-4's `g_m = 1` fence** for `Ĉ_m`.” **★ The supplier-grade clause is STALE — all of W-2, J-A, J-B are ACCEPTED at HEAD, and no GRTJC append records it** (shard 1 OPEN-CALL 3).

**`.104` — JC-BOX-7:** “Statements are for γ in the window W at attained weights (outside, `gr_γ = 0` and no anchor exists); **E > 1 throughout**; **no gate fires and none retires** — DITERSUP §S3 gate J3b stays BLOCKED-ON-CARRIER-TIE …, the Asvin P0 application gate stands; no `.lean` file is touched; no density/menu/count statement is made; MT3's 9 single-pair escapes and the 9 UNDECIDED cyclic rows are disclosed above; **own acceptance counter 0/2** …” **The counter clause is EXPRESSLY superseded by Annex #7; the gate clauses are NOT.**

**CONDITIONALITY (all eight):** see the ledger's status column. **Three boxes carry live OPEN content: JC-BOX-2 (off-stratum, no machine support), JC-BOX-5 (the general inclusion), JC-BOX-8(i) (606 unmeasured perturbations).**

**DERIVATION:** Declarations and fences; each box's mathematical content is homed in shard 2.

**RESOLUTION TRACE:** statement lines 1940–2056; the clauses they fence 662–1934 (shard 2); **correction sites 2805 (Annex #1 → `.99`), 2807–2815 (Annexes #2/#3 → `.99` item 2), 3006–3008 (Annex #7 → `.104`)**.

XREF: `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md:JB-BOX-2` — grep-verified count **45** · `JB-BOX-4` — **2**. `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md:DCX` — **115**. `lean/notes/openmath/GRB_ORDER2_2026-08-05.md:(H-CHAIN)` — **35**.

**TEETH:** JC-BOX-2 **NONE (proof-only, signed)**; JC-BOX-4 R1-COB 24/24 on C4H; JC-BOX-5 JC8 (one falsifiable half); JC-BOX-8(i) **NONE (signed, still owed)**; the rest are records.

---
### EFF.GRTJC.105  [preregistration]  ★ §9.1 — the sealed predictions

**CANONICAL STATEMENT:** verbatim, lines 2062–2088 — the runner declaration and the fourteen-row prediction table.
**FORM:** display (an H3 head) + paragraph + Markdown table.

> “Runner: `verification/openmath/grt_jc_checks.py`, whose docstring carries the
> authoritative preregistration and **is part of this seal**. It imports the
> instrument's tower/stage construction (`grt_jc_probe.ROSTER`/`Stage`, the same 29
> rows) and then tests **this note's clauses**, several of which the instrument
> never measured. Deterministic, exact arithmetic, no randomness.”

`[TABLE]` **the sealed predictions**, transcribed (long cells condensed; every predicate and prediction preserved):

| family | the note's clause it tests | sealed prediction |
|---|---|---|
| EXT-GATE | engine_ext `install()`+`check_pins()`+`agreement_gate()` (standing rule) | **0** |
| JC1 | LEMMA JC-PER + JC-DOM's `w(π) = E`: `φ_{γ+kE} == π^k φ_γ` byte-for-byte at `k = 1,2,3`; s-tuple E-periodic; `u_1 ↦ u_1+k` | **0** |
| JC2 | LEMMA JC-FIB: the s-tuple map is injective on E consecutive `γ`; `s_{j+1} ∈ [0,e_j)` | **0** |
| **JC3** | **THEOREM JC-SPAN, the note's NEW sharp prediction**: the on-line slot set of `φ_γφ_{γ′}` at its own weight is EXACTLY `{δ}`, `δ ∈ {0,1}`, slot-δ digit `u ≠ 0`; `w(φ_γφ_{γ′}) = γ+γ′` | **0** on `e_m ≥ 2` rows |
| JC3-FLAT | the `e_m = 1` corner (JC-BOX-4): min slot = 0 PROVED (scored); “max slot = 0” the unproved sharp form | **0 scored violations**; census reports pairs with a slot > 0 — **measured, NOT scored** |
| JC4 | LEMMA JC-SCAL + §4.1's normalization; **`𝑅_N(X_N) == 1` exactly** | **0** |
| JC5 | LEMMA JC-ANCHMON | **0** |
| JC6 | COROLLARY JC-PSIKER: `w(Φ_{m+1}) == wΦ_NR`; `𝑅(Φ_{m+1}) == ψ_m` coefficientwise; read `== 0`; equal reads, different classes | **0** |
| **JC7** | **COROLLARY W-9**: the mod-E 2-cocycle identity, the integer carry identity, and the E-fold chain `c(φ_1^E) == ∏_{k=1}^{E−1}c_val(γ_1,kγ_1)` (**monodromy = gauge period, two ways**; `E ≤ 8`) | **0** |
| JC8 | LAW JC-CYC + FINDING JC-F1: a CYCLIC verdict ⟹ the collapse geography; every structure constant is a UNIT | **0** |
| **MJ1** | tooth: “TC-3 is never load-bearing” | **≥ 1 firing**; and **0 pairs where RAW fails at `δ < g_m` or succeeds at `δ ≥ g_m` (either would REFUTE JC-LOAD)** |
| **MJ2** | tooth: mutated periodicity `φ_{γ+E} == π²φ_γ` | **≥ 1 firing per row** |
| **MJ3** | tooth: mutated scalar image “slots ⊆ {0}” | **≥ 1 firing per `g_m ≥ 2` row** |
| **MJ4** | tooth: “the read is injective on `gr_λ`” | **≥ 1 firing per row** |
| **MJ5** | tooth: mutated span law “slot set == {δ+1}” | **≥ 1 firing per row** |

**And the exit convention (line 2088): “A silent tooth is a RED. Exit code = (violations + silent teeth).”**

**★ MJ1's PREDICTION IS A TWO-SIDED FALSIFIER OF JC-LOAD AND IS PREREGISTERED AS SUCH:** “0 pairs where RAW fails at `δ < g_m` **or** succeeds at `δ ≥ g_m` (**either would REFUTE JC-LOAD**)”. **A preregistered refutation condition for the note's headline theorem.**

**★ JC7 PREREGISTERS ALL FOUR W-9 CLAUSES, with clause (iv) checked TWO WAYS.**

**CONDITIONALITY:** **The runner IMPORTS the instrument's roster and stage builder** — so it is not roster-independent; what it adds is that it tests THIS note's clauses, “several of which the instrument never measured”. **“A silent tooth is a RED” is the strongest single design commitment in the note's machine apparatus.**

**PIN VERIFICATION:** `6ad01d1` (the seal, from shard 1 `.04`) → **commit**; `grt_jc_checks.py` + its two artifacts **EXIST**; **no md5 pinned** (source defect 1).

**DERIVATION:** Preregistration.

**RESOLUTION TRACE:** statement lines 2062–2088; the verdict 2109–2158 (`.107`); the smoke disclosure 2090–2107 (`.106`).

**TEETH:** this unit IS the preregistration; the teeth are MJ1–MJ5.

---
### EFF.GRTJC.106  [instrument-record]  §9.1 — the build-phase smoke disclosure

**CANONICAL STATEMENT:** verbatim, lines 2090–2107.
**FORM:** bold-headed paragraph.

> “**BUILD-PHASE SMOKE DISCLOSURE (pre-seal, honest; part of this seal).** One
> 3-row smoke of this runner (C2A / C2I / C3A — one g_m = 1 wild row, one g_m = 2
> row, one m = 2 row) ran during construction, elapsed 0.2 s. Result:
> **0 violations in every family (JC1 147, JC2 32, JC3 224, JC4 30, JC5 48,
> JC6 12, JC7 81, JC8 99 samples), all five teeth FIRED** (MJ1 8, MJ2 16, MJ3 2,
> MJ4 3, MJ5 56 firings). Specifically: JC3's sharp slot-span prediction held on
> **56/56** pairs; MJ1 found **8 of 32** tested pairs with no pre-TC-3 scalar and
> **all 8 were in the δ ≥ g_m load set** (JC-LOAD's dichotomy, both directions);
> JC7's E-fold chain matched the orbit product on all three rows
> (C2A z̄¹ = z̄¹, C2I z̄² = z̄², C3A z̄² = z̄²); JC8 returned CYCLIC for C2A and
> C3A (both g_m = 1 = collapse geography) and NOT-CYCLIC for C2I (g_m = 2) —
> **agreeing row-for-row with the instrument's independent MT2 verdicts**. **No
> sealed prediction was changed by the smoke, and no clause of §§2–6 was edited
> because of it.** Two construction-time design choices were fixed BEFORE the
> smoke and are disclosed: (i) JC7/JC8 use the full E² constant table when E ≤ 8
> and the probe's designed subset above it (at E > 8 the adjudicator returns
> UNDECIDED, so a truncated table cannot manufacture a CYCLIC verdict);
> (ii) per-row tooth obligations are scored as their own family (TOOTH-ROW).”

**★ THE MODEL OF A HONEST PRE-SEAL DISCLOSURE:** the smoke is declared **part of the seal**; its full results are given; **the key sentence is “No sealed prediction was changed by the smoke, and no clause of §§2–6 was edited because of it”**; and the two design choices made BEFORE it are disclosed **with the reason one of them cannot bias the verdict** (“at E > 8 the adjudicator returns UNDECIDED, so a truncated table cannot manufacture a CYCLIC verdict”).

**ARITHMETIC AUDIT (rule 22):** smoke samples 147+32+224+30+48+12+81+99 = **673**; teeth firings 8+16+2+3+56 = **85**. **Both internally consistent** (no headline is claimed for them). MJ1: **8 of 32 tested, all 8 in the load set** ✔ — consistent with the full run's 103 of 333, all in the load set.

**CONDITIONALITY:** A 3-row smoke, not a verdict. **Its agreement with the instrument's MT2 “row-for-row” is a cross-check, not independent evidence** (the full-run version of the same point is disclosed at `.108`).

**DERIVATION:** Run record.

**RESOLUTION TRACE:** statement lines 2090–2107; the sealed predictions 2062–2088 (`.105`); the verdict 2109–2158 (`.107`).

**TEETH:** all five fired on 3 rows. Disposition: **executable regression, pre-seal, disclosed as part of the seal.**

---
### EFF.GRTJC.107  [run-record]  ★ §9.2 — the r0 verdict, and JC8's re-labelled cell

**CANONICAL STATEMENT:** verbatim, lines 2109–2132 — the artifacts line, the headline, and the fourteen-row verdict table.
**FORM:** display + Markdown table.

> “**Artifacts:** `verification/openmath/grt_jc_checks_output.txt`,
> `grt_jc_checks_results.json` (deterministic; 29 rows, elapsed **2.0 s**; seal
> commit `6ad01d1`). **ALL 10 FAMILIES GREEN — 0 violations, every sealed
> prediction hit exactly; ALL FIVE TEETH FIRED (no silent tooth).**”

`[TABLE]` **the verdict**, transcribed with every count:

| family | the clause | samples | violations | verdict |
|---|---|---|---|---|
| EXT-GATE | engine_ext standing rule | 1 | **0** | GREEN |
| JC1 | JC-PER + `w(π) = E` | 2,594 | **0** | GREEN — byte-for-byte at `k = 1,2,3`, `w(π) = E` on all 29 rows |
| JC2 | JC-FIB | 570 | **0** | GREEN |
| **JC3** | **JC-SPAN (the new sharp prediction)** | 2,484 | **0** | GREEN — **slot set == {δ} on 609/609 pairs** with `e_m ≥ 2` |
| JC3-FLAT | the `e_m = 1` corner | 24 | **0** scored | GREEN; **census: 0 of 24 pairs have a slot > 0** |
| JC4 | JC-SCAL + the lift normalization | 443 | **0** | GREEN — `𝑅_N(X_N) == 1` exactly, every row, every `c ∈ K` |
| JC5 | JC-ANCHMON | 855 | **0** | GREEN |
| JC6 | JC-PSIKER | 116 | **0** | GREEN |
| **JC7** | **W-9 cocycle semantics** | 581 | **0** | GREEN — **261 triples** satisfy BOTH the `K^*`-cocycle and the integer carry identity; **the E-fold chain matched the orbit product on all 15 rows with `E ≤ 8`** |
| **JC8** | JC-CYC + JC-F1 | 898 | **0** | ~~GREEN — every structure constant a unit~~ **[r1, G3 — RE-LABELLED: this battery does NOT evidence the unit property.]** GREEN for the ONE falsifiable half only: **no CYCLIC verdict off the collapse geography** (29 rows). **The unit half is VACUOUS as coded**: the JC7 block builds the table with `if v is None or K.is_zero(v): continue`, so **zeros and undefined constants are filtered out BEFORE the JC8 predicate `if K.is_zero(v)` can see them — the violation branch is unreachable and the skipped pairs were never censused.** … The falsifiable replacement … is r1 family **R1-UNIT** + tooth **T4** |
| MJ1 | tooth: “TC-3 never load-bearing” | 333 tested | **103 firings** | FIRED — **all 103 lie in the `δ ≥ g_m` load set; 0 anomalies in either direction (JC-LOAD's dichotomy machine-confirmed both ways)** |
| MJ2 | tooth: `φ_{γ+E} = π²φ_γ` | 285 | **285 firings** | FIRED on every row |
| MJ3 | tooth: “`Λ_N` slots ⊆ {0}” | 6 | **4 firings** | FIRED on every `g_m ≥ 2` row (2 of 6 opportunities genuinely empty) |
| MJ4 | tooth: “the read is injective on `gr_λ`” | 29 | **29 firings** | FIRED on every row |
| MJ5 | tooth: slot set == {δ+1} | 633 | **633 firings** | FIRED on every pair |

**MANDATORY ARITHMETIC AUDIT (rule 22) — computed fresh:**
- **Family samples:** 1 + 2,594 + 570 + 2,484 + 24 + 443 + 855 + 116 + 581 + 898 = **8,566** ✔ **matches the header's headline exactly** (shard 1 `.04`).
- **Teeth firings:** 103 + 285 + 4 + 29 + 633 = **1,054** ✔ **matches the header exactly.**
- **Families:** the table lists 10 scored families (EXT-GATE … JC8) + 5 teeth = 15 rows; the headline says “ALL 10 FAMILIES GREEN” and separately “ALL FIVE TEETH FIRED” ✔ **the 10/5 split is consistent.**
- **MJ3:** 4 firings of 6 opportunities, with 2 explained ✔.
- **★ Contrast with GRTJB: both GRTJC headline figures reconstruct EXACTLY from this table; GRTJB's §7.1 headline does not** (`spec/EFF-GRTJB-s3of3.md` source defect 2).

**★ THE JC8 RE-LABELLING IS THE CLEANEST VACUOUS-GREEN DISCLOSURE IN THE CORPUS.** The mechanism is displayed in code: an upstream `continue` filters zeros before the downstream predicate can see them, **so the violation branch is unreachable and the skipped pairs were never censused**. **The note does not merely disclose it — r1 builds the falsifiable replacement (R1-UNIT) with a planted-zero tooth (T4) proving the new predicate CAN fire.**

**CONDITIONALITY:** “every sealed prediction hit exactly” is true of the ten scored families; **JC8's unit half evidenced nothing and the cell says so.**

**DERIVATION:** Executed run from the committed artifacts.

**RESOLUTION TRACE:** statement lines 2109–2132; the predictions 2062–2088 (`.105`); the disposition 391–394 (r1/G3, shard 1 `.33`); the replacement 2184, 2231 (`.16`).

**TEETH:** as tabulated. **Disposition: executable regression with one signed vacuity disclosure, repaired in the next round.**

---
### EFF.GRTJC.108  [run-record]  §9.2 — the cyclic split reproduced, with its resolution disclosure

**CANONICAL STATEMENT:** verbatim, lines 2134–2142.
**FORM:** bold-headed paragraph.

> “**The cyclic split reproduced: CYCLIC 6 / NOT-CYCLIC 14 / UNDECIDED 9**, with the
> cyclic rows **C2A / C2E / C2G / C2J / C3A / C4A** — *the same six rows, and the
> same 14/6/9 split, as the instrument's MT2*. **Disclosure (resolution, honest):**
> this battery's constant table is the harness ratio c_val (via the probe's
> `Stage.cval`), whereas the instrument's MT2 used the fence-clean gr-side
> certified constant c_gr; the two tables agree because W-8/P5-OB6 says
> c_gr = c_val (0/669), so the verdict-identity is a *consistency* check of W-8,
> not a second independent measurement of the split. The adjudicator itself is a
> fresh transcription.”

**★ THE DISCLOSURE IS EXACTLY RIGHT AND RARE: an agreement between two runs is declared NOT to be independent evidence, with the reason given.** Because W-8 says `c_gr = c_val`, agreement is **entailed**; what the agreement tests is W-8, not the split. **“The adjudicator itself is a fresh transcription”** is the one genuinely independent component.

**ARITHMETIC AUDIT (rule 22):** 6 + 14 + 9 = **29** ✔; the six named cyclic rows = **6** ✔; consistent with shard 2 `.93`/`.94`.

**CONDITIONALITY:** A consistency check of W-8. **And W-8's own proof route was later found CRITICALLY defective and repaired (Annex #4) — though the identity it asserts is what P5-OB6 measured 0/669, so the consistency reading survives.**

**DERIVATION:** Run record + the entailment argument.

**RESOLUTION TRACE:** statement lines 2134–2142; W-8 1658–1671 (shard 2 `.84`); **Annex #4 at 2840–2884 (`.85`)**; the law 1865–1910 (shard 2 `.94`).

**TEETH:** P5-OB6 0/669 (the instrument's). Disposition: **measurement, declared non-independent.**

---
### EFF.GRTJC.109  [run-record]  ★ §9.2 — the two battery-driven findings

**CANONICAL STATEMENT:** verbatim, lines 2144–2158.
**FORM:** bold-headed paragraph + two numbered findings.

> “**TWO BATTERY-DRIVEN FINDINGS, applied above:**
>
> 1. **The collapse geography does NOT imply cyclic** (the converse of JC-CYC(d) is
>    FALSE): 13 rows sit in the collapse geography and still come back NOT-CYCLIC
>    (C2B, C2C, C2D, C2H, C3D, C3E, C3F, C3H, C3I, C4B, C4G, I4B, I4C). Two
>    mechanisms are visible in the printed table: **≥ 2 distinct non-1 values**
>    (C2B/C2D/C2H/C3D/C3E/C3F/C3H/C4B/C4G/I4B/I4C — up to **7** distinct values on
>    I4C) and **a single value whose carry pattern is not realizable by any integer
>    relabeling** (C2C, C3I). §6(d) is stated one-directionally because of this,
>    and JC-CYC(b)'s obstruction direction is what does the work.
> 2. **The law's resolution on this roster is low and is disclosed**: only **2 of
>    29 rows (C2I, C4I) are OFF the collapse geography**, and both are
>    NOT-CYCLIC / UNDECIDED — so "CYCLIC ⟹ collapse" was tested against few
>    potential counterexamples. A hostile pass should build g_m ≥ 2 rows with
>    small tables.”

**★ A BATTERY THAT DISCONFIRMED ITS AUTHOR, TWICE — and both findings were APPLIED, not merely noted.** Finding 1 refuted the converse of a draft law and forced §6(d) to be one-directional; finding 2 disclosed that the surviving direction has weak evidence and **named the experiment that would strengthen it** (“build `g_m ≥ 2` rows with small tables”). **Eight hostile passes did not build them** (shard 2 OPEN-CALL 4).

**ARITHMETIC AUDIT (rule 22):** the 13 named NOT-CYCLIC collapse rows = **13** ✔; mechanism-1 rows named = C2B, C2D, C2H, C3D, C3E, C3F, C3H, C4B, C4G, I4B, I4C = **11**; mechanism-2 rows = C2C, C3I = **2**; **11 + 2 = 13** ✔. Off-collapse rows = **2** (C2I, C4I) ✔. **And 6 cyclic + 13 not-cyclic-in-collapse + 2 off-collapse = 21 of 29; the remaining 8 are UNDECIDED-in-collapse, and 8 + 1 (C4I, UNDECIDED and off-collapse) = 9 UNDECIDED ✔ — the whole roster reconciles.**

**CONDITIONALITY:** Finding 1 is what makes JC-CYC(d) one-directional and is the counterexample class r3/G-8 used to fix clause (b)'s trigger (shard 1 `.29`).

**DERIVATION:** Measurement + inspection of the printed table.

**RESOLUTION TRACE:** statement lines 2144–2158; the law 1865–1910 (shard 2 `.94`); the trigger fix 339–342 (r3/G-8, shard 1 `.29`); the box 2028–2038 (`.06`).

**TEETH:** JC8's 898 samples. Disposition: **measurement, refuting the note's own draft converse.**

---
### EFF.GRTJC.110  [preregistration]  §9.3 — the r1 battery's sealed table

**CANONICAL STATEMENT:** verbatim, lines 2162–2191 — the runner declaration, the fourteen-row prediction table and the exit convention.
**FORM:** display + Markdown table.

> “**Runner:** `verification/openmath/grt_jc_r1_checks.py`, whose docstring carries
> the authoritative preregistration and **is part of this mini-seal** (commit 1 =
> runner + this table, battery NOT yet run; commit 2 = the verdict written FROM the
> committed artifacts …). It … tests **only the statements r1 introduced or repaired**.
> The sealed r0 battery, the instrument, and all their artifacts are untouched.
> Fence hygiene as in §3.5 [r1, G8]: `T.constants` is used only for the integer δ,
> `T.read`/`T.read_coeffs` supply the digit data that the repaired statements are
> *about*.”

`[TABLE]` **the r1 predictions**, transcribed at their predicates:

| family | the r1 statement it tests | sealed prediction |
|---|---|---|
| EXT-GATE | engine_ext standing rule | **0** |
| **R1-BND** | §2.10's slot bound: `maxslot(G0) == 0` on every row — **i.e. the r0 (COORD)'s surjectivity onto Δ is FALSE at the note's own window base** (PE1's counter-instance, **reproduced as a scored fact**) | **0** violations; census printed |
| **R1-PER** | JC-PIINV: `𝑅_{λ+kE}(π^kf) == c_π^k·𝑅_λ(f)` with ONE `c_π` per row; `ρ` exactly invariant, `k = 1,2` | **0** |
| **R1-INJ** | §1's injectivity, both directions: `𝑅_λ(f) == 0 ⟺ w(f) > λ` | **0** |
| **R1-SURJ** | JC-BSURJ: targets of y-degree 0,1,2 realized at the predicted `k` ON THE NOSE; the minimal `k` censused (**`k > 0` for degree ≥ 1 — the k-shift is structural**) | **0** |
| **R1-DMULT** | (DMULT) EXACTLY (not merely up to a unit) on sampled pairs — **the Δ-module half, the leg neither prior runner had** | **0** |
| **R1-COB** | JC-COB on the full anchor grid **[r3, G-7 — prereg quotation BYTE-FROZEN, annotated only: post-tier-split the blast radius is TWO-MODE …]** | **0** |
| **R1-PSIK-LO** | JC-PSIKER(ii) lower half (**one-sided certifier, JC-BOX-8(ii)**) | **0** |
| **R1-PSIK-HI** | JC-PSIKER(iii): for EVERY residue `ν ∈ ℤ/E` a certified witness | **0** |
| **R1-UNIT** | **G3's falsifiable replacement**: every constant of the FULL E×E grid classified (unit / zero / undefined-denominator / out-of-window), with the skipped-pair census printed | **0**, census printed |
| **T1** | tooth: **the REFUTED r0 universal claim** | **≥ 1 firing per row** |
| **T2** | tooth: “no k-shift is needed” | **≥ 1 firing per row** |
| **T3** | tooth: mutated (DMULT) with the shift `y^{δ+1}` | **≥ 1 firing per row** |
| **T4** | tooth: **a PLANTED ZERO injected into the constant table, to prove R1-UNIT's predicate can fire at all (the exact defect G3 found in JC8)** | **≥ 1 firing per row** |
| **T5** | tooth: mutated JC-PIINV | **≥ 1 firing per row** |

**★ TWO TEETH ARE THE NOTE'S OWN REFUTED CLAIMS TURNED INTO PERMANENT MUTANTS (T1, T2), AND ONE (T4) EXISTS SOLELY TO PROVE A PREDICATE IS NOT VACUOUS.** **T4 is the direct structural answer to JC8's failure** — the note builds a tooth whose only job is to show the new predicate can fire.

**CONDITIONALITY:** **Scoped to “only the statements r1 introduced or repaired”.** **Fence hygiene is re-declared** (the `T.constants`/`T.read` call sites).

**PIN VERIFICATION:** `f45b63c` → **commit**; md5 `7f896bfa27d06158f95c5987c7299770` **EXACT at HEAD**; all three artifacts **EXIST**.

**DERIVATION:** Preregistration.

**RESOLUTION TRACE:** statement lines 2162–2191; the smoke 2193–2204 (`.111`); the verdict 2206–2240 (`.112`).

**TEETH:** T1–T5, all preregistered with per-row obligations.

---
### EFF.GRTJC.111  [instrument-record]  §9.3 — the pre-seal smoke disclosure

**CANONICAL STATEMENT:** verbatim, lines 2193–2204.
**FORM:** bold-headed paragraph.

> “**PRE-SEAL SMOKE DISCLOSURE (honest, part of this mini-seal).** Two read-only
> /tmp scripts were run BEFORE the seal to fix the design and the cost: (a) a
> 6-row mechanism probe (C2A/C2I/C3A/C3I/C4H/C4I) which found — and is why the
> predictions above are stated in this exact form — that c_π is a single row
> constant taking values in {1, z̄, z̄²}, that ρ-invariance is EXACT, that (DMULT)
> holds with multiplier exactly **1** (so JC-COB's u = a_γa_{γ′} is the right
> sharp form), that the REALIZE construction reproduces degree-1 and degree-2
> targets on the nose, and that the PSIKER witness behaves as JC-PSIKER(iii) says;
> (b) a 29-row cost probe fixing the k-search caps (minimal k ≤ 34 for degree 2,
> psiker line offset ≤ 14 steps). No scored predicate was weakened by either probe,
> and the two teeth T1/T2 are the r0 text's own refuted claims, fixed before the
> probes were written.”

**★ THE DISCLOSURE ADMITS THAT THE PREDICTIONS WERE SHAPED BY THE SMOKE — “which is why the predictions above are stated in this exact form”.** That is the honest thing to say, and it correctly downgrades the preregistration's strength for those specific predicates. **The countervailing facts are also stated: no scored predicate was WEAKENED, and T1/T2 predate the probes.**

**★ AND THE SMOKE IS WHERE THE `c_π ∈ {1, z̄, z̄²}` VALUE SET CAME FROM — the 6-row figure that r2/G-3 later caught being presented as a roster figure** (shard 1 `.38`). **The disclosure that would have prevented the defect is right here, in the same round.**

**CONDITIONALITY:** Read-only, /tmp, **no committed artifact** — so the smoke itself is **UNPINNED** (rule 23), like GRTJB's r5 probe. **Unlike GRTJB's case, nothing rides on it: it fixed design and cost, not evidence.**

**DERIVATION:** Disclosure.

**RESOLUTION TRACE:** statement lines 2193–2204; the mislabelled value set 1137–1143 (shard 2 `.66`); its correction 461–463 (r2/G-3, shard 1 `.38`).

**TEETH:** none of its own. Disposition: **instrument-record with an UNPINNED probe, non-load-bearing.**

---
### EFF.GRTJC.112  [run-record]  ★ §9.3 — the r1 verdict, the eleven-row table, and the three findings

**CANONICAL STATEMENT:** verbatim, lines 2206–2253 — the verdict with its `[r2, G-8]` decomposition, the eleven-row family table, the five-row tooth table, and the three findings.
**FORM:** bold verdict + two Markdown tables + numbered findings.

> “**VERDICT (written FROM the committed artifacts … runner
> md5 `7f896bfa27d06158f95c5987c7299770`, sealed UNRUN at commit `f45b63c`).**
> ~~**ALL 10 FAMILIES GREEN — 10,475 scored samples**~~ **[r2, G-8 — the split,
> displayed: ALL 10 FAMILIES GREEN with 10,330 scored samples (EXT-GATE 1 +
> R1-BND 29 + R1-PER 841 + R1-INJ 585 + R1-SURJ 841 + R1-DMULT 2,784 + R1-COB
> 2,607 + R1-PSIK-LO 591 + R1-PSIK-HI 1,182 + R1-UNIT 869), plus the ELEVENTH
> table row TOOTH-ROW 145 (a family by §9.1's own convention) = 10,475 rows
> scored over the 11-row table; the r1 headline attached the 11-row total to a
> 10-family label]**, **0 violations, 29 rows,
> elapsed 2.6 s, exit 0; ALL FIVE TEETH FIRED (1,885 firings, no silent tooth,
> every per-row obligation met: TOOTH-ROW 145/145).** Every sealed prediction hit
> exactly.”

`[TABLE]` **the eleven rows**, transcribed at their load-bearing results:

| family | samples | violations | result |
|---|---|---|---|
| EXT-GATE | 1 | 0 | GREEN |
| **R1-BND** | 29 | 0 | **`maxslot(G0) = 0` on 29/29 — the r0 (COORD) refuted at the note's own base on every row**; the ladder census `maxslot(G0+kE)`, `k = 0..3`, shows the growth making `B_n ⊋ gr_n` (C2A `[0,0,1,1]`, C2D `[0,1,1,1]`, I4C `[0,0,0,0]` — “slower but unbounded”) |
| **R1-PER** | 841 | 0 | `c_π` is ONE constant per row; `ρ` EXACTLY π-invariant; **measured `c_π = 1` on 9 rows and `z̄^a`, `a ∈ {1,2,3,4,6,8}`, on the other 20 — “the un-normalized `𝑅` is genuinely NOT π-invariant and the ρ-normalization is doing real work”** |
| R1-INJ | 585 | 0 | both directions |
| **R1-SURJ** | 841 | 0 | every target realized on the nose at the predicted `k`; **minimal `k`: degree 0 at `k = 0` on 28 rows (`k = 2` on C4H), degree 1 at `k = 2..16`, degree 2 at `k = 5..34` — “the k-shift is structural, not a convenience”** |
| **R1-DMULT** | 2,784 | 0 | **`𝑅_{λ+μ}(fg) == y^{δ}𝑅_λ(f)𝑅_μ(g)` EXACTLY (multiplier 1, not merely proportional)** on every sampled pair of every row, with `w(fg) = w(f)+w(g)`. **“This is the Δ-module leg PE1 recorded as unmeasured”** |
| **R1-COB** | 2,607 | 0 | **`u == a_γ·a_{γ′}` with slot set exactly `{δ}` on 869/869 anchor pairs, all 29 rows, including the `e_m = 1` row C4H (0 out-of-window skips)** |
| R1-PSIK-LO | 591 | 0 | **197 window lines below `wΦ_NR`**, no class certified dead (one-sided certifier, JC-BOX-8(ii)) |
| R1-PSIK-HI | 1,182 | 0 | **197 residue classes** carry a witness with `w` exact, digit polynomial `== a_ν·y^δ·ψ_m(y)` on the nose, read `== 0`, death CERTIFIED |
| **R1-UNIT** | 869 | 0 | **869 unit / 0 zero / 0 undefined-denominator / 0 out-of-window over 869 grid pairs — and tooth T4 proves the predicate can fire (a planted zero caught on every row, which the r0 JC8 predicate could not do)** |
| TOOTH-ROW | 145 | 0 | all five teeth fire on all 29 rows |

`[TABLE]` **the five teeth:** T1 29/29 · T2 29/29 · T3 1,392/1,392 · T4 29/29 · T5 406/406.

**MANDATORY ARITHMETIC AUDIT (rule 22):**
- Family samples: 1 + 29 + 841 + 585 + 841 + 2,784 + 2,607 + 591 + 1,182 + 869 = **10,330** ✔ **matches the corrected headline exactly.**
- **+ TOOTH-ROW 145 = 10,475** ✔ **matches the struck headline — so r2/G-8's diagnosis (“the r1 headline attached the 11-row total to a 10-family label”) is arithmetically exact.**
- Teeth: 29 + 29 + 1,392 + 29 + 406 = **1,885** ✔ **matches “1,885 firings”.**
- TOOTH-ROW 145 = 5 teeth × 29 rows = **145** ✔.
- **Every figure reconstructs. Four independent cross-checks, all consistent.**

**★ THE THREE FINDINGS (lines 2242–2253), quoted at their operative clauses:**
1. **“(DMULT) holds with multiplier exactly 1**, not merely up to a line-wise unit — which is why JC-COB can be stated in the sharp form” **[r2, G-1: this measured finding IS the exact tier (DMULT-s) — it is the note's evidence FOR that tier, not a citation of it.]**
2. “**The `e_m = 1` corner's sharp form is measured true by R1-COB on C4H** (slot set exactly `{δ} = {0}` on all 24 of its grid pairs), and on (DMULT) it is in fact PROVED — see JC-BOX-4 [r1].”
3. “**`c_π ≠ 1` on 20 of 29 rows.** The colimit coordinate would NOT be well defined in the un-normalized `𝑅`; JC-PIINV(c)'s ρ-normalization is **load-bearing, not cosmetic**.”

**CONDITIONALITY:** **R1-DMULT's samples are monomial-dominated with an undisclosed skip — found at r2/G-2 and disclosed at `.113`.** **R1-PSIK-LO's certifier is one-sided and the note says so.**

**DERIVATION:** Executed run from committed artifacts.

**RESOLUTION TRACE:** statement lines 2206–2253; the predictions 2162–2191 (`.110`); the disclosure 2255–2274 (`.113`); the tier 1188–1267 (shard 2 `.69`).

**TEETH:** as tabulated; **T4's existence is the answer to JC8's vacuity.**

---
### EFF.GRTJC.113  [instrument-record]  ★ §9.3 — the r2/G-2 disclosure the r1 battery owed

**CANONICAL STATEMENT:** verbatim, lines 2255–2274.
**FORM:** bold-headed bracketed block.

> “**[r2, G-2 — INSTRUMENT DISCLOSURE the r1 battery owed: R1-DMULT's sample
> composition and its silent skip.]** PE2's code audit of the byte-frozen
> `grt_jc_r1_checks.py`, confirmed here against the source: the per-row sample
> list has SEVEN elements — up to three anchors φ_r, the scalar lift X_N, one
> anchor product φ_0φ_{1 mod E}, (1+π)φ_0, and Φ_{m+1} — of which **six have
> SINGLE-SLOT (monomial) digit polynomials** …, and the DMULT loop **`continue`s the one
> non-monomial × non-monomial pair** `(Φ_{m+1}, Φ_{m+1})` — a skip the r1 text
> did not disclose. Consequence: on every one of R1-DMULT's 48 ordered pairs
> per row, y^δ·𝑅(f)·𝑅(g) is a shift-and-scale of one factor — **the identity's
> genuinely BILINEAR content (cross-term convolution of two multi-slot digit
> polynomials) was NEVER exercised** by r1 … **The verdict cell above
> ("on every sampled pair") is therefore true but weaker than it reads.** This is
> the same defect species r1 repaired in G3/G6, reintroduced in the new leg;
> the repair is r2's own machine leg (§9.4) …”

**★ “TRUE BUT WEAKER THAN IT READS” IS THE EXACT DIAGNOSIS, AND IT IS A BRED DEFECT: “the same defect species r1 repaired in G3/G6, REINTRODUCED IN THE NEW LEG”.** The round that fixed two vacuity defects created a third in its own instrument.

**ARITHMETIC AUDIT (rule 22):** 7 sample elements, 6 single-slot, 1 multi-slot (`Φ_{m+1}`, digit polynomial `ψ_m`) ✔; 7 × 7 = 49 ordered pairs minus the 1 skipped = **48** ✔ matching “48 ordered pairs per row”. **The arithmetic corroborates the disclosure exactly.**

**CONDITIONALITY:** **R1-PSIK-HI's `Φ_{m+1}·φ_ν` leg is “non-monomial × monomial, still one-sided”** — so no leg in r1 exercised true bilinearity.

**DERIVATION:** A code audit of a byte-frozen runner, confirmed against source.

**RESOLUTION TRACE:** statement lines 2255–2274; the disposition 448–460 (r2/G-2, shard 1 `.37`); the repair 2282–2331 (`.18`, `.19`).

**TEETH:** the repair's **R2-MONO** SCORES this disclosure rather than asserting it — “(a) exactly ONE of the r1 sample elements per row has a multi-slot digit polynomial; (b) every r1-TESTED DMULT pair has ≥ 1 single-slot factor; (c) the U2 mutation, replayed on the r1-tested pairs, fires **0** times there — **machine proof that the r1 leg had zero resolution against it**”. **Disposition: a prose disclosure converted into a scored fact — the pattern that became FREEZE PREDICATE 3.**

---
### EFF.GRTJC.114  [preregistration]  §9.4 — the r2 bilinearity leg, preregistered

**CANONICAL STATEMENT:** verbatim, lines 2284–2308 — the runner declaration and the six-row prediction table.
**FORM:** display + Markdown table.

> “**Runner:** `verification/openmath/grt_jc_r2_checks.py`, whose docstring
> carries the authoritative preregistration and **is part of this mini-seal**
> (commit 1 = the runner alone, SEALED and UNRUN, exactly the r1 protocol;
> commit 2 = the verdict below …). It imports the
> instrument's roster and stage builder … and the byte-frozen r1 helpers
> (`grt_jc_r1_checks.Rpoly`/`pmul`/`surj_build` — **imported, not re-typed, so the
> (DMULT) predicate is the SAME predicate PE2 audited as independent**), and
> tests **only what G-2 found missing: the bilinear content of (DMULT-s)**.”

`[TABLE]` **the r2 predictions:**

| family | the statement it tests | sealed prediction |
|---|---|---|
| EXT-GATE | engine_ext standing rule | **0** |
| **R2-BIL** | (DMULT-s) on genuinely BILINEAR input: both factors built by JC-BSURJ with **dense multi-slot targets**, every ordered pair tested; `w(fg) == w(f)+w(g)` and the identity EXACTLY (**dict equality — the cross-term convolution finally exercised**) | **0** |
| **R2-PHI** | **the pair r1 silently skipped**, scored on every row: `f = g = Φ_{m+1}` | **0** |
| **R2-MONO** | **§9.3 [r2, G-2]'s disclosure as SCORED fact, not prose** — (a), (b), and (c) the U2 mutation replayed on the r1-tested pairs fires **0** times there | **0** |
| **U1** | tooth: the `y^{δ+1}` shift on the new dense pairs | **≥ 1 firing per row** |
| **U2** | tooth: **the CROSS-TERM DROP** — deletes exactly the interior×interior convolution terms. **PROVABLY equal to the true product whenever either factor has ≤ 2 occupied slots — hence silent on every r1-tested pair — and provably different on a dense deg-2 × dense deg-2 pair over a field** | **≥ 1 firing per row** |

**★ U2 IS THE BEST-DESIGNED TOOTH IN EITHER NOTE: a mutation with a PROVED silence condition and a PROVED firing condition, so its firing pattern MEASURES a leg's resolution rather than merely testing a claim.**

**CONDITIONALITY:** **The leg imports the frozen r1 helpers ON PURPOSE** — “so the (DMULT) predicate is the SAME predicate PE2 audited as independent”. **So it is not a decorrelated second implementation; it is the same predicate on better input**, and the note says so.

**PIN VERIFICATION:** `79611a4` → **commit**; md5 `c02bf06029a72259512ea005bd2562fd` **EXACT at HEAD**; all three artifacts **EXIST**.

**DERIVATION:** Preregistration.

**RESOLUTION TRACE:** statement lines 2284–2308; the smoke 2310–2315; the verdict 2317–2331 (`.115`).

**TEETH:** U1, U2 with per-row obligations.

---
### EFF.GRTJC.115  [run-record]  §9.4 — the r2 verdict

**CANONICAL STATEMENT:** verbatim, lines 2317–2331 — the verdict and the four-row result table.
**FORM:** bold verdict + Markdown table.

> “**VERDICT** … **ALL 4 FAMILIES GREEN — 3,597 scored samples in the
> four families (EXT-GATE 1 + R2-BIL 696 + R2-PHI 87 + R2-MONO 2,813) plus
> TOOTH-ROW 58 = 3,655 table rows, 0 violations, 29 rows, elapsed 7.4 s, exit
> 0; BOTH TEETH FIRED ON EVERY OPPORTUNITY (U1 261/261, U2 261/261, no silent
> tooth).** Every sealed prediction hit exactly.”

`[TABLE]` **the four families**, at their load-bearing results:

| family | result |
|---|---|
| **R2-BIL** | **0 violations on 261 dense multi-slot × multi-slot ordered pairs** (9 per row) — **(DMULT-s) holds EXACTLY (dict equality, multiplier 1) on genuinely bilinear input, cross-term convolution finally exercised**, with `w(fg) = w(f)+w(g)` on every pair. **[r3, G-3 — three BUILDS, not three distinct elements: on 13/29 rows mix2 == ones2 byte-identically]** |
| **R2-PHI** | **0 violations on 29/29 rows** for the r1-skipped pair: `𝑅(Φ_{m+1}) = ψ_m`, `w(Φ_{m+1}²) = 2wΦ_NR`, `𝑅(Φ²) = y^δ·ψ_m(y)²` exactly (`δ = 0` on every row — ~~`E \| wΦ_NR`~~ **[r3, G-4: false divisibility … the correct one-liner is `e_m \| wΦ_NR`, true 29/29]**). **Census: the skipped pair has genuine bilinear content on exactly the two `g_m = 2` rows, C2I and C4I — on the other 27 ψ_m is 2-slot and the skip cost nothing; on those two, r1's one true bilinear pair was the skipped one** |
| **R2-MONO** | **0 violations**: exactly ONE multi-slot element among the r1 samples on every row; every r1-TESTED pair has ≥ 1 single-slot factor (29/29); **and U2 replayed on the r1-tested pairs fired 0 times across the whole roster — machine proof that the r1 leg had zero resolution against the cross-term mutation class** |
| **U1 / U2** | U1 261/261; **U2 261/261 — fires on EVERY dense pair and NEVER on an r1-tested pair, which is exactly the separation the tooth was designed to exhibit** |

**MANDATORY ARITHMETIC AUDIT (rule 22):** 1 + 696 + 87 + 2,813 = **3,597** ✔; **+ TOOTH-ROW 58 = 3,655** ✔ — **both headline figures reconstruct exactly.** R2-PHI 87 = 29 × 3 ✔. U1 = U2 = 261 = 29 × 9 ✔. TOOTH-ROW 58 = 2 teeth × 29 rows ✔. **Five cross-checks, all consistent.**

**★ THE R2-PHI CENSUS IS A SHARP RETROSPECTIVE ON THE SKIP: it cost nothing on 27 rows and cost the ONLY true bilinear pair on the two `g_m = 2` rows — precisely the rows where `ψ_m` has interior content.** **The skip was maximally badly placed, and the census says so.**

**CONDITIONALITY:** **Diversity overstated until r3/G-3** (`.116`).

**DERIVATION:** Executed run from committed artifacts.

**RESOLUTION TRACE:** statement lines 2317–2331; the disclosure 2333–2362 (`.116`); the r3/G-4 divisibility fix 329–331 (shard 1 `.25`).

**TEETH:** U2's resolution separation; R2-MONO's scored disclosure.

---
### EFF.GRTJC.116  [instrument-record]  ★ §9.4 — the r3/G-3 diversity disclosure, and the species record

**CANONICAL STATEMENT:** verbatim, lines 2333–2369.
**FORM:** bold-headed bracketed block + a closing scope paragraph.

> “**[r3, G-3 — DIVERSITY DISCLOSURE (the census the R2-BIL cell owed), and the
> species record.** The frozen runner's `build_dense` sets
> `alt = elems[1] if len(elems) > 1 else elems[0]` over the nonzero elements of
> K_m and gives mix2 the target {0: 1, 1: alt, 2: 1}. On **13 of 29 rows** that
> `alt` IS 1 — on ten rows (C2A, C2B, C2E, C3A, C3D, C3E, C3I, C4B, C4G, I4A)
> the enumeration's second nonzero element is 1, and on three rows (C2I, C4A,
> C4I) K_m^* = {1} so no other choice exists — hence mix2's target equals
> ones2's target and the deterministic `surj_build` returns the
> **byte-identical polynomial** … On those 13 rows D = {f, f, f′}: the 9 ordered pairs contain only **4
> distinct** pairs, and the "mixed variant" adds zero resolution — including on
> **BOTH g_m = 2 rows (C2I, C4I)**, exactly the rows where ψ_m has interior
> content. What stands, undiminished: ones2 × ones2, ones2 × ones3,
> ones3 × ones3 are genuinely dense × dense with live cross-term convolutions,
> U2 fired 261/261, and (DMULT-s)'s bilinear evidence is real — **the defect is
> RESOLUTION overstatement, not a wrong verdict, and no measured quantity
> moves.** **Species record (the THIRD recurrence of the sampling-diversity
> overstatement, ended here the way such sagas end — by censusing composition
> instead of asserting it):** PE2 G-2 (r1's monomial-dominated samples and the
> undisclosed (Φ_{m+1}, Φ_{m+1}) skip) → r2's fix (the dense leg + R2-MONO
> scoring the composition) → PE3 GAP 3 (the dense leg's own mix2 == ones2
> collapse, undisclosed). Standing rule from this history: **any
> sampling-diversity claim in this note must be a SCORED or CENSUSED fact,
> never prose.** **Candidate repair leg, NAMED, NOT BUILT** …]**”

**★★ THE SPECIES RECORD IS THE MOST TRANSFERABLE ARTEFACT IN EITHER NOTE.** Three recurrences of one defect, each inside the fix for the previous one, and the cure stated as a standing rule: **“any sampling-diversity claim in this note must be a SCORED or CENSUSED fact, never prose.”** **That rule is FREEZE PREDICATE 3, and it is why every GRTJC headline reconstructs from its own table while GRTJB's §7.1 does not.**

**★ AND THE COLLAPSE IS WORST WHERE IT MATTERS MOST: “including on BOTH `g_m = 2` rows (C2I, C4I), exactly the rows where `ψ_m` has interior content.”**

**ARITHMETIC AUDIT (rule 22):** 10 rows (second nonzero element is 1) + 3 rows (`K_m^* = {1}`) = **13** ✔; on those rows `D = {f, f, f′}` gives 2 distinct elements, so `2² = 4` distinct ordered pairs of the 9 ✔.

**CONDITIONALITY:** **“the defect is RESOLUTION overstatement, not a wrong verdict, and no measured quantity moves.”** **The candidate repair is NAMED, NOT BUILT** — a disclosed, standing evidence gap.

**DERIVATION:** Composition re-verified against the frozen code; byte-identity verified by PE3 on C2I/C4I/C2A.

**RESOLUTION TRACE:** statement lines 2333–2369; the disposition 325–328 (r3/G-3, shard 1 `.24`); the species' first two members 448–460 (r2/G-2) and 2255–2274 (`.17`).

**TEETH:** **signed vacuity disclosure** on the mixed variant + **disclosed non-repair** on the candidate leg. **The surviving evidence is named precisely: ones2×ones2, ones2×ones3, ones3×ones3.**

---
### EFF.GRTJC.117  [instrument-record]  ★ §9.5 — the alias/bracket-sweep record and its DISCLOSED PROTOCOL LIMIT

**CANONICAL STATEMENT:** [ASSEMBLED — §9.5's four nested census blocks, lines 2371–2597: the r2 fixed-point record with its `[r3, G-2]` correction, the r3 alias-complete re-sweep, the r4 union sweep with the `[r5, G-1]` per-alias table, the LIVE-bucket content audit, and the closing DISCLOSED PROTOCOL LIMIT. Quoted at each block's load-bearing figures.]

**The r2 count, corrected at r3/G-2 (lines 2400–2419):**

> “~~Count at r2 close: the grep returns **22 hit-lines** …~~ **[r3, G-2 — that count was WRONG AT ITS
> OWN COMMIT (evidently taken before this §9.5 record and some [r2] brackets
> were themselves written, then committed unrefreshed — **a fixed-point claim
> must be grepped AT the committing state**): executed at `5742e25` … the recorded grep
> returns 37 hit-lines both times (24 pre-r2 at `66263ce`), classified …:
> 17 inside strikes …, 4 in the r1 repair-history header, 1 in the r2
> dispositions header, 2 R1-BND rows, 11 in this §9.5 record itself, 2 in
> [r2, G-4]'s own quotation brackets = 37.]** The load-bearing half stands:
> **0 live consuming sites** for this pattern — PE3 re-verified it by
> independent classification of all 37 hits …”

**The r4 union sweep and its census (lines 2452–2532), at the figures:** the union pattern `(IN-3) | Thm 4.2 | Theorem 4.2 | FGMN | 4.8 | Cor 2.7 | (COORD) | (MULT)`; **“Census at r4 close, grep executed AT THE COMMITTING STATE (the [r3, G-2] lesson): 144 hit-lines = 42 LIVE + 28 STRUCK + 74 RECORD.”**

**The `[r5, G-1]` per-alias contribution table (lines 2476–2516), transcribed:**

`[TABLE]` **per-alias contributions, unit: hit-lines, executed at `edbb966`:**

| alias | total | exclusive |
|---|---|---|
| `(IN-3)` | 39 | 26 |
| `Thm 4.2` | 30 | 12 |
| `Theorem 4.2` | 2 | 0 (both hits = the two pattern displays) |
| `FGMN` | 48 | 32 |
| `4.8` | 11 | **4** (L383 + L401 LIVE group 1; L1801 LIVE group 10; L1782 STRUCK) |
| `Cor 2.7` | 13 | 5 |
| `(COORD)` | 30 | 9 |
| `(MULT)` | 36 | 16 |
| — | — | **Σ 104** (the other 40 of the 144 lines carry ≥ 2 aliases) |

**And the self-reference disclosure:** “this table's own lines add hit-lines to any later execution of the union grep; they are census record … and **any future count must be re-executed at ITS committing state** — the [r3, G-2] lesson, kept.”

**★ THE DISCLOSED PROTOCOL LIMIT (lines 2591–2597), quoted in full because it is the honest ceiling on the whole alias saga:**

> “**DISCLOSED PROTOCOL LIMIT [r4, G-4]: this census counts hit-LINES by NAME.**
> A content line whose name-tag sits on an adjacent line is outside its
> resolution — §0's clause-(c) display was exactly such a line, and is now
> annotated in place [r4, G-4]. The limit was discharged this round by a
> read-through of §0's input block, the only place the package's clauses are
> DISPLAYED as propositions rather than consumed by name; **the census cannot
> certify the absence of further such lines by grep, and says so.**”

**MANDATORY ARITHMETIC AUDIT (rule 22):**
- r4 census: 42 + 28 + 74 = **144** ✔.
- Per-alias exclusives: 26 + 12 + 0 + 32 + 4 + 5 + 9 + 16 = **104** ✔ **matches the table's own Σ**; and **144 − 104 = 40** ✔ matches “the other 40 of the 144 lines carry ≥ 2 aliases”.
- `4.8`'s four exclusive lines are itemised: 3 LIVE + 1 STRUCK = **4** ✔.
- r3 census (from shard 1 `.16`): 23 + 25 + 42 = **90** ✔, reproduced EXACTLY by PE4.
- r2's corrected count: 17 + 4 + 1 + 2 + 11 + 2 = **37** ✔.
- **PE5 re-executed the union census independently at HEAD and reproduced 144 = 42/28/74 bucket for bucket; PE6 reproduced the per-alias table to the last digit (18/18 numbers).**
- **Six cross-checks, all consistent, three of them by independent passes.**

**★ THE LIVE BUCKET IS AUDITED BY CONTENT, NOT JUST BY NAME — twelve groups, all 42 lines** (lines 2534–2589), concluding: “**The verified fixed point, at the union pattern and by content: ZERO live hits state (IN-3)(c)-on-gr, (COORD), (MULT), the Thm-4.2-on-gr_{O[x]} transport, or the bare ‘FGMN (c)' stack alias.**”

**CONDITIONALITY:** **The fixed point is verified at the union pattern AND by content — but the protocol limit means completeness rests, at the last step, on a read-through of §0** (shard 1 OPEN-CALL 4).

**DERIVATION:** Greps executed at committing states, plus a content audit of the live bucket.

**RESOLUTION TRACE:** statement lines 2371–2597; the dispositions 320–324 (r3/G-2), 271–282 (r4/G-1), 297–302 (r4/G-4), 235–246 (r5/G-1) — shard 1 `.23`, `.17`, `.20`, `.13`.

**TEETH:** **AUDIT — arithmetic recount**, three times independently reproduced. Disposition: **accepted-with-decorrelation-supplied, with a signed resolution limit.**

---
### EFF.GRTJC.118  [changes-record]  §10.1 — the grade box, the arc, and the deltas

**CANONICAL STATEMENT:** verbatim, lines 2605–2662 — the post-repair grade box with its four struck arc displays, the live `[r6]` arc, and the five “Grade deltas” convention lines.
**FORM:** bold-headed block with nested strikes.

> “**[r1] GRADE BOX, POST-REPAIR (read this first; the r0 table below stands except
> where this block supersedes it).** ~~Arc: … → JC-PE2 next.~~ ~~**[r2] Arc: … → JC-PE3 next.**~~ **[r4, G-2 — PE4: r3 did not
> extend this arc record (the note's own per-round convention, set when r2
> struck r1's arc line here), **leaving two contradictory arc displays at HEAD**
> — the header's current one and this box's stale "JC-PE3 next". Extended: ~~Arc: … → JC-PE5 next.~~]** ~~**[r5 — arc extended per the
> same convention …]**~~ **[r6 — arc extended per the same
> convention (the [r5] display above is struck, not deleted): Arc:
> composed (0/2) → JC-PE1 (2 CRITICAL + 8 gaps) → r1 (STRUCTURAL) → JC-PE2
> (0 CRITICAL + 9 gaps; "no false statement") → r2 … → JC-PE3 (0 CRITICAL + 8 gaps;
> all labelling/disclosure/record defects) → r3 … → JC-PE4 (0 CRITICAL + 4 gaps; all in what
> r3 left untouched) → r4 … → JC-PE5 (0 CRITICAL + 2 gaps + 1 minor; "the r4 diff's
> mathematics is EXACT" …) → r5 … → JC-PE6 (0 CRITICAL + 1 gap; "the r5 diff's substance is exact,
> everywhere I could machine-check it"; the gap entirely in the pointer
> record r5's own re-classification created) → r6 … →
> JC-PE7 next.]** Acceptance counter
> **0/2** (a repair round is not a pass). **[r2] Grade deltas at r2: NONE — the
> one status that MOVES is (DMULT)'s label (its exact tier from "CITED" to
> MEASURED …), which downgrades no clause grade but re-fences
> JC-COB's sharp form onto the measured tier.** **[r3] Grade deltas: NONE …** **[r4] Grade deltas: NONE …** **[r5] Grade deltas: NONE …** **[r6] Grade deltas: NONE …**”

**★ FIVE CONSECUTIVE ROUNDS WITH “Grade deltas: NONE” IS ITSELF THE FINDING: after r1's structural repair, no round moved a grade.** The one status that moved was `(DMULT)`'s LABEL, and the note is careful that this “downgrades no clause grade but re-fences JC-COB's sharp form onto the measured tier”.

**ARITHMETIC AUDIT (rule 22):** the arc's verdicts — 2C+8G, 0C+9G, 0C+8G, 0C+4G, 0C+2G+1m, 0C+1G — **identical to the S-STATUS series (shard 1 `.05`–`.10`) and to the acceptance record's “Full arc” (`.27`)**. **Three independent recitals, all consistent.** ✔ Rounds with “deltas NONE” = r2, r3, r4, r5, r6 = **5** ✔.

**CONDITIONALITY:** **“Acceptance counter 0/2” is EXPRESSLY superseded by Annex #7, which names §10.1's counter by designation.** **The r4/G-2 note records that r3 left “two contradictory arc displays at HEAD”** — the same defect class GRTJB never fixed (its OPEN-CALL 1), caught and repaired here.

**DERIVATION:** Record.

**RESOLUTION TRACE:** statement lines 2605–2662; the series 34–185 (shard 1 `.05`–`.10`); the disposition 283–288 (r4/G-2, shard 1 `.18`); **status superseded 3006–3008 (Annex #7, `.35`)**.

**TEETH:** the three batteries + instrument, re-run byte-identically each round.

---
### EFF.GRTJC.119  [TABLE]  §10.1 — the two per-clause grade tables

**CANONICAL STATEMENT:** verbatim, lines 2664–2685 — the r0-vs-r1 delta table and the r0 per-clause grade table.
**FORM:** two Markdown tables.

`[TABLE]` **what changed at r1** (lines 2664–2670):

| clause | r0 grade | r1 grade | what changed |
|---|---|---|---|
| **W-6** | PROVED general m | **PROVED general m** | (ii) re-keyed to `B_n` (G1); (v) re-quantified (F2); ~~box JC-BOX-4 unchanged~~ **[r2, G-7: JC-BOX-4 CHANGED at r1 — it gained the conditional closure on (DMULT-w)]** |
| **W-7** | PROVED on stated scopes | **PROVED on stated scopes, one clause STRENGTHENED** | OB-4 re-derived on `B` (F1); **spanning promoted from definition to theorem, so Ψ is onto the WHOLE transported ring** |
| **W-8** | PROVED general m | **PROVED general m** | inputs re-listed as (COORD-B)+(MULT-B)+JC-SPAN+JC-SCAL+R3; remark (a)'s two identifications struck (G7) and replaced by JC-COB |
| **W-9** | PROVED given W-6..W-8 | **PROVED given W-6..W-8** | JC-F1's dimension count now rests on the repaired display; **JC-F2 added as a second REVIEW-OWED display correction** |
| cyclic fence | REFINED, not refuted | **unchanged** | no measured verdict moves at r1 |

**And the r1 newly-proved list (lines 2672–2677):** “**Newly PROVED at r1** (all at general m, on the inputs named): JC-LOC, JC-PIINV, JC-BSURJ, (COORD-B)(1), (COORD-B)(2) from (1)+(DMULT), (MULT-B), JC-COB, JC-PSIKER(ii)(iii). **Newly boxed:** JC-BOX-8. **Nothing was downgraded to boxed at r1** — every one of PE1's five listed consumers re-derived through, **which is the round's substantive claim and the first thing JC-PE2 should attack**.”

`[TABLE]` **the r0 per-clause grades** (lines 2679–2685), transcribed at their grades:

| clause | grade |
|---|---|
| **W-6** | **PROVED at general m**, attempt 0/2, **one located box: the top-flat corner `e_m = 1 ∧ g_m = 1`** (JC-BOX-4) |
| **W-7** | **PROVED on the stated scopes**, attempt 0/2; the germ split displayed honestly (**val law CONFIRMED on 27 stages; H-D REFUTED 138/669**) |
| **W-8** | **PROVED at general m** on (COORD-B)+(MULT-B)+JC-SPAN+JC-SCAL+R3, attempt 0/2 |
| **W-9** | **PROVED given W-6..W-8** (S-priced, as the blueprint priced it), attempt 0/2 |
| **cyclic fence** | **REFINED, not refuted**; byte-frozen 22/28 record unamended; the inclusion MEASURED with its general form OPEN and its **converse REFUTED by this note's own battery** |

**★ “Nothing was downgraded to boxed at r1 … which is the round's substantive claim and the first thing JC-PE2 should attack” — the note NAMES ITS OWN MOST ATTACKABLE CLAIM and directs the next pass at it. PE2 attacked it and found no false statement.**

**CONDITIONALITY:** All four “attempt 0/2” labels are **EXPRESSLY superseded by Annex #7**. **W-8's grade line is the one whose PROOF was later found critically defective and repaired (Annex #4) — the GRADE survives because the conclusion does.**

**DERIVATION:** Grade records.

**RESOLUTION TRACE:** statement lines 2664–2685; the four faces 664–1843 (shard 2); **Annexes #4 and #7 at 2840–2884 and 3006–3008**.

**TEETH:** per clause, as in shard 2's inventory.

---
### EFF.GRTJC.120  [scope record]  ★ §10.2 — the conditionality stack, four dated forms

**CANONICAL STATEMENT:** verbatim, lines 2687–2748 — the r0 one-liner, the struck weakest-links ranking, the `[r1]` re-statement, the `[r2]` tier-split form, and the `[r5, G-2]` completion with its `[r6, G-1]` wording fix.
**FORM:** four bold one-line displays + ranked lists.

**The r0 stack (line 2689):**

> “**`[ILN]† ACCEPTED (scored stratum; residuals (RM-m ≥ 2), (W-MULT-DCX-m), (ITER-LAW-LIFT), standard-lift only) + GRB/CARRY-1/D-REAL ACCEPTED-conditional (§0 ladder + [T] pins) + FGMN Thm 4.2 / Thm 4.8 / Cor 2.7 CITED (composite order; numbering re-verification owed) + W-1/W-2/J-A/J-B ATTEMPT 0/2 (with JB-BOX-2's (VD-m) geography) ⟹ this note, attempt 0/2.`**”

**The `[r1]` re-statement (line 2702):**

> “**`… + (DMULT) on B [= FGMN Thm 4.2's content via JC-LOC] + Thm 4.8/Cor 4.9 + Cor 2.7 CITED (numbering re-verification still owed) + W-1/W-2/J-A/J-B ATTEMPT 0/2 ⟹ this note, attempt 0/2 after r1.`**”

**The `[r2]` tier split (lines 2713–2725):** “The single FGMN entry divides: **(DMULT-w)** … stays CITED with the numbering re-verification owed; **(DMULT-s)** … is **MEASURED-only**, carrying exactly JC-COB's sharp form.” With the weakest links **re-ranked for each pass** — six ranked lists across the four forms.

**The `[r5, G-2]` completion (lines 2727–2748), with the `[r6, G-1]` fix nested:**

> “**[r5, G-2 — THE FGMN ENTRY COMPLETED (annotation, not edit: the r0/[r1]/[r2]
> stack displays above are ROUND-RECORDS — each states the stack AS OF its
> round and is quoted ~~as such~~ **for its content as of the citing round
> [r6, G-1 — wording corrected per PE6 GAP 1: §0 [r4, G-1] cites those
> displays as "the current stacks … which supersede this display", NOT as
> round-records; that bracket now carries its own dated [r6] annotation in
> place]** by later brackets, §0 [r4, G-1] included — so
> their wording stays; PE5 GAP 2 …).** … **The
> CURRENT stack is therefore the [r2] tier-split form with its FGMN entry read
> as: FGMN (a)(b) + (DMULT-w) on B [= Thm 4.2's content via JC-LOC;
> (DMULT-s) MEASURED-only] + Thm 4.8/Cor 4.9 + Cor 2.7 CITED (numbering
> re-verification still owed)**. §0's live one-line display carries the same
> completion in place …”

**CHAIN (rule 25) — FOUR dated stack forms.** r0 → r1 (the FGMN entry narrowed and correctly aimed) → r2 (the tier split) → r5/G-2 (the (a)(b) completion) → **and, post-acceptance, Annex #6's boxed form is TERMINAL:** “**FGMN (a)(b) + Thm 4.2 rank-one freeness on `B` via JC-LOC + Thm 4.8/Cor 4.9 + Cor 2.7; (DMULT-w) derived above; (DMULT-s) as in Annex #1.**” `CHAIN HOME: .43.`

**★ THE WEAKEST-LINKS RANKINGS ARE RE-DONE FOR EVERY PASS, AND THAT IS THE NOTE'S BEST SERVICE TO A HOSTILE READER.** The `[r2]` ranking for JC-PE3: “(1) (DMULT-w) at composite order + W-1's transport (with TR-3′-GEN … OPEN at general order); (2) JC-BOX-2's off-stratum existence claim (**zero machine support**); (3) the non-integral residue JC-BOX-8(i); (4) (DMULT-s)'s measured-only status …; (5) the top-flat corner …; (6) JC-F1/JC-F2 REVIEW-OWED.”

**CONDITIONALITY:** **“W-1/W-2/J-A/J-B ATTEMPT 0/2” is STALE at HEAD** — all three notes are ACCEPTED, unrecorded here (shard 1 OPEN-CALL 3). **“numbering re-verification still owed” is DISCHARGED by Annexes #2/#3.** **“this note, attempt 0/2” is EXPRESSLY superseded by Annex #7.** **The three older stack displays are ROUND-RECORDS and must not be read as current** (shard 1 merge hazard 4).

**DERIVATION:** Conjunctions of the five inputs' grades.

**RESOLUTION TRACE:** statement lines 2687–2748; §0's live display 573–604 (shard 1 `.46`); the dispositions 247–255 (r5/G-2) and 201–220 (r6/G-1), shard 1 `.14`/`.11`; **Annexes #2/#3/#6/#7 at 2807–2815, 2917–3000, 3006–3008**.

**TEETH:** NONE (a conditionality display).

---
### EFF.GRTJC.121  [fence]  ★ §10.3 — the named consumers, and what each may NOT take

**CANONICAL STATEMENT:** verbatim, lines 2752–2781 — the five consumer bullets.
**FORM:** bulleted list.

> “* **DITERSUP §S3 gate J3b (BLOCKED-ON-CARRIER-TIE).** This note supplies exactly
>   the missing item (ii) of J3b's three-item residual list — "the gr(w₂) semantics
>   wrapper", i.e. §S3's *missing tie* — at **attempt grade 0/2 and at general m**,
>   not only at order 2. **The gate does NOT retire here and this note does not
>   retire it**: J3b retires only when (J-C)(ii) survives its own hostile arc, and
>   its other legs (BLOCKED-ON-APPLICATION, the (ITER-LAW-LIFT) residual at
>   g_0 = 1 ∧ δ_1 = 1, orders ≥ 3 of DITERSUP's own queue) are untouched. **The tie
>   is displayed, the gate stands.**
> * **`Scaffold/HDischarge/H1/DIterCarrier.lean` — JS1 / JS2.** JS1
>   (`gateJS1_cocycle_assoc`, PROVED with the honest `hTrack : D.OuterTrackAdd`
>   hypothesis) is the harness-side 2-cocycle/associativity gate; **§5's COROLLARY
>   W-9(i)(ii) is its *semantic home*** … JS2 … is the e_0 = 1 D-REAL degeneration, which §6's
>   genre law places in the *collapse geography* … **No Lean hypothesis is discharged by this note** — the compiled file's `hTrack` still
>   needs a Lean-level supplier, and this note is not it (attempt grade, no Lean
>   layer exists for gr(w_{m+1})).
> * **MOVES B2-DEF.** Its accepted induction gains its intended **semantic home** …
>   Display only; B2-DEF's own statements and grade are unchanged.
> * **The (H1)(a) GR-B carry side.** §§3–4 give the composite-stage carry law that
>   the (H1)(a) package's carry side asks for, on the scored stratum and at attempt
>   grade … It does **not** discharge (H1) — the
>   faithfulness handoff is J-D1 (W-12), not composed here.
> * **The MOVES B2-FINAL bridge and bare-interface discharges stay DEAD** (brief
>   fence 3): nothing above routes through them, and the option-(ii) vacuity trap
>   (P1-FLAG-1/J3B-FLAG-1) is not re-opened.”

**★ THE CONSUMER LIST IS ENTIRELY NEGATIVE IN ITS OPERATIVE CLAUSES, AND THAT IS THE POINT.** Five consumers named; for each, what it gets is a **semantic home** or a **display**, and what it does NOT get is stated: **the gate does not retire; no Lean hypothesis is discharged; B2-DEF's grade is unchanged; (H1) is not discharged; the dead bridges stay dead.**

**★ W-9(i)(ii) IS NAMED AS JS1's SEMANTIC HOME — the second downstream consumer of W-9 after WELDZERO** (shard 2 `.89`). **And the note is explicit that this is semantics, not discharge: “the compiled file's `hTrack` still needs a Lean-level supplier, and this note is not it”.**

**CONDITIONALITY:** **The “attempt grade 0/2” qualifiers are superseded by Annex #7 — but the GATE clauses are NOT**, and Annex #7 says so: “Acceptance of this note does not upgrade any upstream ATTEMPT-grade input or **remove any displayed scope fence**.”

**DERIVATION:** Consumption declaration.

**RESOLUTION TRACE:** statement lines 2752–2781; W-9 1777–1799 (shard 2 `.89`, `.90`); §6's genre law 1865–1916 (shard 2 `.94`); **Annex #7 at 3006–3008 (`.88`)**.

XREF: `lean/notes/openmath/DITERSUP_STMT_2026-08-08.md` — **file EXISTS**.

**TEETH:** NONE (a consumer fence).

---
### EFF.GRTJC.122  [SERIES: the POST-ACCEPTANCE ARC, ten dated members]

**SERIES DECLARATION (rule 28).** Lines 2785–3059 carry a chronological arc of dated appends. Emitted with membership and order recorded. **TERMINAL: Annexes #4–#8 (2026-08-12), the sol fold.**

`[TABLE — compiler ledger]` **the post-acceptance arc.**

| unit | member | lines | date | kind | what it does |
|---|---|---|---|---|---|
| `.122` | ★ ACCEPTANCE RECORD | 2785–2799 | 2026-08-06 | `acceptance-box` | **ACCEPTED at 2/2** (PE7 `782000e` CLEAN, PE8 `9d240b6` CLEAN) |
| `.123` | ANNEX #1 | 2805 | 2026-08-08 | `changes-record` | **(DMULT-s) PROVED-conditional** on the measured perimeter by DULEMMA THEOREM DU |
| `.124` | ANNEX #2 | 2807 | 2026-08-08 | `changes-record` | the FGMN numbering **DISCHARGED at the local text extraction** |
| `.125` | ANNEX #3 | 2809–2815 | 2026-08-12 | `changes-record` | the FGMN cites **PDF-VERIFIED**; the extraction leg's decorrelation debt paid |
| `.126` | the sol C4/E4 adjudication head | 2819–2834 | 2026-08-12 | `changes-record` | a CHALLENGE with a **CRITICAL**; **all five findings REAL** |
| `.127` | **ANNEX #4** | 2836–2884 | 2026-08-12 | `supplier-finding` | **the W-8 quotient route — the CRITICAL cured** |
| `.128` | **ANNEX #5** | 2886–2911 | 2026-08-12 | `supplier-finding` | the load-set qualifier on outer-factor non-obtainability |
| `.129` | **ANNEX #6** | 2913–3000 | 2026-08-12 | `supplier-finding` | **LEMMA JC-RANKMULT — the multiplicativity bridge DERIVED** |
| `.130` | **ANNEX #7** | 3002–3008 | 2026-08-12 | `changes-record` | **the EXPRESS status supersession** |
| `.131` | **ANNEX #8** | 3010–3037 | 2026-08-12 | `supplier-finding` | nonzero scalar lifts and zero coordinates |
| `.132` | the orchestrator verification record | 3039–3059 | 2026-08-12 | `changes-record` | five findings re-checked before transcription |

*(Unit IDs `.122`–`.132`; the series header occupies no ID of its own.)*

---

### EFF.GRTJC.122  [acceptance-box]  ★ THE ACCEPTANCE RECORD

**CANONICAL STATEMENT:** verbatim, lines 2787–2799.
**FORM:** display (a starred H2 block).

> “**THIS NOTE IS ACCEPTED at 2/2** — PE7 (782000e, CLEAN 0C/0G; JC-GAUGE
> re-proved via coarsened grading + the fresh p = 7 out-of-roster leg) and
> PE8 (9d240b6, CLEAN; W-8 + JC-LOAD's iff by the double-(DMULT-w) +
> ω-symmetry route + the FIRST g_m = 3 instances and an order-5 (m = 4,
> E = 8) tower, 885/0). Full arc: composed → PE1 (2C+8G) → r1 STRUCTURAL
> ((COORD-B) on B_n) → PE2 (0C+9G) → r2 → PE3 (0C+8G) → r3 → PE4 (0C+4G)
> → r4 → PE5 (0C+2G+1m) → r5 → PE6 (0C+1G) → r6 → PE7 CLEAN → PE8 CLEAN.
> Eight hostile passes, six repair rounds. **WHAT IS ACCEPTED**: W-6/W-7/
> W-8 at general m and W-9 given them, on the (COORD-B)-on-B_n
> restatement, with the (DMULT-w)/(DMULT-s) two-tier honesty (load-bearing
> clauses ride the DERIVED weak tier; the exact tier MEASURED with
> numbering-verification owed) and the cyclic-genre law as fenced. Machine
> record: three byte-frozen batteries + instrument, all green.”

**★ THE TWO CLEAN PASSES BROUGHT GENUINELY NEW MATHEMATICS AND NEW SCOPE:**
- **PE7:** JC-GAUGE re-proved **via coarsened grading** (a different method) **+ a fresh `p = 7` out-of-roster leg** — the first evidence outside the 29-row roster's `p ∈ {2,3,5}`.
- **PE8:** W-8 **+ JC-LOAD's iff** re-proved by a **double-`(DMULT-w)` + ω-symmetry route** (a method that avoids the exact tier entirely) **+ the FIRST `g_m = 3` instances and an order-5 (`m = 4`, `E = 8`) tower, 885/0** — **beyond the roster's `g_j ≤ 2` and `orders ≤ 4`.**
**Both passes extended the machine scope JC-BOX-1 declares, which is exactly what that box asked for.**

**★ “WHAT IS ACCEPTED” IS UNUSUALLY PRECISE and names the two-tier honesty as part of what was accepted:** “W-6/W-7/W-8 at general m and W-9 given them, **on the (COORD-B)-on-B_n restatement**, with the **(DMULT-w)/(DMULT-s) two-tier honesty (load-bearing clauses ride the DERIVED weak tier; the exact tier MEASURED with numbering-verification owed)** and the cyclic-genre law **as fenced**.”

**ARITHMETIC AUDIT (rule 22):** passes PE1…PE8 = **8** ✔; rounds r1…r6 = **6** ✔ — matching “Eight hostile passes, six repair rounds”. The verdict recital matches the S-STATUS series and §10.1's arc **exactly** ✔ (three independent recitals). **Trend: criticals 2 → 0 from PE2; gaps 8 → 9 → 8 → 4 → 2 → 1 → 0 → 0.**

**CONDITIONALITY:** **“numbering-verification owed” was DISCHARGED six days later by Annex #3.** **The acceptance PREDATES the sol adjudication by six days and cannot have contemplated Annexes #4–#8 — but Annex #7 closes that gap explicitly**, making the current status “ACCEPTED at 2/2, **conditionally on exactly the input stack and fences named by the Acceptance Record together with the post-acceptance corrections in Annexes #4–#8**”. **GRTJB has no equivalent** (its OPEN-CALL 1).

**PIN VERIFICATION:** `782000e` → **commit**; `9d240b6` → **commit**. **No report filenames for PE7/PE8** (source defect 2).

**DERIVATION:** Orchestrator record of two clean hostile passes.

**RESOLUTION TRACE:** statement lines 2787–2799; the arc 34–185 (shard 1) and 2605–2649 (`.118`); **Annex #7 at 3006–3008 (`.130`)**.

**TEETH:** **PE7's coarsened-grading re-proof + `p = 7` leg; PE8's ω-symmetry route + `g_m = 3` and order-5 instances, 885/0.** Disposition: **accepted-with-decorrelation-supplied, with SCOPE EXTENSION** — both passes tested outside the sealed roster.

---
### EFF.GRTJC.123  [changes-record]  ANNEX #1 — (DMULT-s) becomes PROVED-conditional

**CANONICAL STATEMENT:** verbatim, line 2805.
**FORM:** blockquoted dated annex.

> “**[ANNEX 2026-08-08, orchestrator, post-acceptance] (DMULT-s) — §2.10's MEASURED tier — is PROVED-conditional on the measured perimeter (the [ILN]† scored stratum, m ≥ 1, e_m ≥ 2) by `DULEMMA_PROOF_2026-08-08.md` THEOREM DU (∂u ≡ 1 via the four-line WM-COB compose; the one new identity a_γ = E(γ), LEMMA DU-A), riding [ILN]†+GRTJC+WELDMASTER as accepted plus DU-A/DU-B at 0/2 — machine leg `dulemma_checks.py` two-commit seal, all families green; COROLLARY JC-COB's sharp u = a_γa_{γ′} inherits (DU-COB); the e_m = 1 row stays measured and off-stratum pairs stay open (DU-BOX-1/2); no text of this note is edited.**”

**SUPERSESSION KIND:** `provenance-rider` — a MEASURED tier acquires a conditional proof from a later note.

**★ THE UPGRADE IS REAL BUT PARTIAL AND THE ANNEX FENCES IT PRECISELY:** PROVED-conditional **on the measured perimeter only** (`[ILN]†` scored stratum, `m ≥ 1`, `e_m ≥ 2`); **riding DULEMMA's own DU-A/DU-B at 0/2**; **`e_m = 1` stays MEASURED and off-stratum pairs stay OPEN.** **And there is a circularity to note: DULEMMA rides “[ILN]†+GRTJC+WELDMASTER as accepted” — i.e. it consumes GRTJC, whose `(DMULT-s)` it then proves.** The scope split saves it (DU proves the tier on a perimeter, using GRTJC's OTHER accepted clauses), but **a merge should record the dependency direction explicitly.**

**CONDITIONALITY:** JC-COB's sharp form inherits (DU-COB) — so shard 2 `.72` is upgraded from MEASURED to PROVED-conditional on the same perimeter.

**PIN VERIFICATION:** `lean/notes/openmath/DULEMMA_PROOF_2026-08-08.md` — **file EXISTS**. `dulemma_checks.py` — cited; **not verified to exist by this compiler** (recorded as a checkable pin).

**DERIVATION:** External (DULEMMA's THEOREM DU).

**RESOLUTION TRACE:** statement line 2805; the tier 1220–1247 (shard 2 `.69`); JC-COB 1335–1352 (shard 2 `.72`).

**TEETH:** DULEMMA's `dulemma_checks.py` under a two-commit seal, all families green — **foreign-note evidence**.

---
### EFF.GRTJC.124  [changes-record]  ANNEX #2 — the FGMN numbering discharged at the extraction

**CANONICAL STATEMENT:** verbatim, line 2807.
**FORM:** blockquoted dated annex.

> “**[ANNEX 2026-08-08 #2, orchestrator, post-acceptance] The "numbering re-verification still owed" parenthetical on the FGMN cites is DISCHARGED at the local print (`docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt`): Thm 4.2 @ 1028, Thm 4.8 @ 1136, Cor 2.7 @ 525, Cor 4.7 @ 1121, eq (14) @ 1004, Lemma 5.13 @ 1403 … + **Cor 4.9 @ 1153 (this fold)**: the print states "Fᵢ₊₁ = Fᵢ[zᵢ] = F₀[z₀,…,zᵢ], deg ψᵢ = fᵢ"; this note's gloss "Δ/(ψ_m) ≅ K_{m+1}" is the composite of Thm 4.8 … + the print's §3.3 DEFINITION … (@ 862 …) + Cor 4.9 … — FAITHFUL as the pair-cite, no extra hypotheses. Caveat (extraction-decorrelation rule): **verified against the local text extraction; the cited formulas' non-textual legs are the sealed batteries (R1-DMULT etc.)**. No text of this note is edited.**”

**SUPERSESSION KIND:** `provenance-rider` — a standing “owed” flag discharged.

**★ PIN VERIFICATION BY THIS COMPILER — all seven line pins re-read at HEAD. SIX EXACT, ONE OFF BY TWO:**

| cite | annex's pin | text at that line | verdict |
|---|---|---|---|
| Thm 4.2 | 1028 | “Theorem 4.2. Let g ∈ K[x] be a non-zero polynomial and let α = µ(g). Then,” | **EXACT** |
| Thm 4.8 | 1136 | “Theorem 4.8. The mapping Rr,0 : ∆ −→ Fr [y] is an isomorphism of Fr -algebras and” | **EXACT** |
| Cor 2.7 | 525 | “Corollary 2.7. For non-zero g, h ∈ K[x], we have Sλ (gh) = Sλ (g) + Sλ (h).” | **EXACT** |
| Cor 4.7 | 1121 | “Corollary 4.7. Let 0 ≤ i ≤ r and α ∈ Γi .” | **EXACT** |
| eq (14) | 1004 | “(14)  Ri,α (φsi ) = y ⌊s/ei ⌋ , Ri (φsi ) = 1, 1 ≤ i ≤ r.” | **EXACT** |
| Lemma 5.13 | 1403 | “Lemma 5.13. For non-zero g, h ∈ K[x] with g µ-proper, we have R(gh) = R(g)R(h).” | **EXACT** |
| §3.3 ψ_i def | 862 | “ψi ∈ Fi [y], minimal polynomial of zi over Fi .” | **EXACT** |
| **Cor 4.9** | **1153** | line 1153 reads “κ(µ)alg ≃ Fr and the next result follows.”; **Corollary 4.9 is at line 1151** | **NEAR-MISS — off by two; CONTENT EXACT at 1151: “Corollary 4.9. For all 0 ≤ i < r, Fi+1 = Fi [zi ] = F0 [z0 , . . . , zi ] and deg ψi = fi .”** |

**Recorded as source defect 3.** The annex's own quoted content (“Fᵢ₊₁ = Fᵢ[zᵢ] = F₀[z₀,…,zᵢ], deg ψᵢ = fᵢ”) **matches line 1151 word for word**, so the referent is unambiguous. **A line-number slip inside a numbering-verification fold.**

**★ THE EXTRACTION-DECORRELATION CAVEAT IS THE ANNEX'S OWN HONESTY, AND IT IS WHAT FORCED ANNEX #3:** “verified against the local text extraction; the cited formulas' non-textual legs are the sealed batteries”. **The note flags that a text-extraction leg inherits any extraction corruption — and then pays that debt six days later by reading the PDF.**

**DERIVATION:** Line-by-line reading of the local extraction.

**RESOLUTION TRACE:** statement line 2807; the owed flag 553–557 (shard 1 `.43`); **the PDF leg 2809–2815 (`.29`)**.

**TEETH:** **AUDIT — transfer audit**; superseded in strength by `.125`.

---
### EFF.GRTJC.125  [changes-record]  ★ ANNEX #3 — the FGMN cites PDF-VERIFIED

**CANONICAL STATEMENT:** verbatim, lines 2809–2815 — the head, the three verdicts and the net.
**FORM:** blockquoted dated annex with three numbered verdicts.

> “**[ANNEX 2026-08-12 #3, FGMN-WELD cite verification unit, post-acceptance] The FGMN cites are PDF-VERIFIED at the displayed numbering — the census row I-4 `cite-UNVERIFIED` is discharged.** Annex #2 above verified against the local TEXT EXTRACTION only; **under the extraction-decorrelation rule that leg inherits any extraction corruption, so this fold reads the PDF itself.** Pin: `docs/references/fgmn_residual_ideals_1305.0775v3.pdf`, md5 `da846c82f1fcb619cefb3feb8164191e` (confirmed at read time). Method: GENTOW2 S6.1 two-leg — leg 1 quotes this note's own rendering, leg 2 the printed statement. Verdicts, all three **VERIFIED**: …”

**The three verdicts, at their load-bearing clauses:**
1. **Cor 2.7 — printed p. 10 — VERIFIED.** With a **display-precision note, not drift**: “the s-additivity is a display inside Cor 2.7's proof rather than its headline segment identity; **a maximally precise cite is ‘Cor 2.7 (component form) / Lemma 2.6(2)'**. Consumption survives unchanged.”
2. **Thm 4.2 — printed p. 20 — VERIFIED.** With **two disclosed renderings, neither adding a hypothesis**: (i) “Δ ≅ K_m[y]” imports Thm 4.8; (ii) the generator is printed as `φ_r(α) := x_r^{s(α)}p_r^{u(α)}`, **associate to a power of `in(φ_r)`** by Lemma 3.14 — “identifying it with THIS note's own anchor `in(φ_γ)` is the transport, **already graded W-1 ATTEMPT and fenced in JC-BOX-3 [r1] item 1 — no undisclosed gap**”.
3. **Thm 4.8 (+ Cor 4.9) — printed p. 22 — VERIFIED as the pair-cite.** With a **scope note**: “Cor 4.9 is stated for `0 ≤ i < r`, so the cite is in range exactly when `K_{m+1}` exists (`m < r`), which is the note's standing usage.”

**And the Net:** “Numbering correct on all three; hypotheses and conclusions match; the only rendering differences are the two disclosed ones under item 2 … and the display-precision remark under item 1. **No consumption changes** … **JC-BOX-3 [r1] item 2 (“CITATION PRECISION — STANDING CODEX LEG, owed”) is hereby DISCHARGED against the printed source; the transport legs it also names (W-1 ATTEMPT) are untouched and remain open.**”

**★★ THIS IS THE EXTRACTION-DECORRELATION RULE BEING OBEYED, AND IT IS THE CLEANEST INSTANCE IN THE CORPUS.** Annex #2 verified against a text extraction and **flagged that the leg inherits extraction corruption**; Annex #3 **pays the debt by reading the PDF**, pins the PDF by md5, and uses a **two-leg method** (this note's rendering vs the printed statement). **This compiler re-computed the PDF md5 at HEAD: `da846c82f1fcb619cefb3feb8164191e` — EXACT.**

**★ AND WHAT IS *NOT* DISCHARGED IS STATED: “the transport legs it also names (W-1 ATTEMPT) are untouched and remain open.”** **The citation is now verified; the TRANSPORT of the cited theorem to the harness objects remains the live weak link** — exactly as JC-BOX-3 item 3 and the `(DMULT-w)` derivation say.

**CONDITIONALITY:** Item 2's second rendering is precisely the anchor identification that **rides W-1 at ATTEMPT grade** — the annex declines to launder it and points at the existing fence.

**DERIVATION:** A two-leg PDF read.

**RESOLUTION TRACE:** statement lines 2809–2815; the owed flag 553–557 and JC-BOX-3 item 2 1976–1984; the extraction leg 2807 (`.124`); the CITE-SCOPE resolution at shard 1 `.43`.

**TEETH:** **AUDIT — transfer audit at the printed source, with the extraction leg's decorrelation debt explicitly paid.** Disposition: **accepted-with-decorrelation-supplied** — two legs, two media, one md5 pin.

---
### EFF.GRTJC.126  [changes-record]  the 2026-08-12 sol C4/E4 adjudication — head

**CANONICAL STATEMENT:** verbatim, lines 2819–2834.
**FORM:** display (an H3 head) + paragraph.

> “The sol-5.6 as-built read of this note (gpt-5.6-sol high,
> runs/cert/C4_grtjc_output.log, 2026-08-12) returned CHALLENGE with a
> CRITICAL (the W-8 quotient-lifting error on the TC-3 load set). The
> E4 certification run (gpt-5.6-sol high,
> runs/cert2/E4_grtjc_output.log) adjudicated **all five findings REAL**
> and derived the repairs below (Annexes #4–#8): the W-8 route redone
> as a quotient computation with conclusion unchanged; the load-set
> qualifier for outer-factor obtainability; LEMMA JC-RANKMULT deriving
> (DMULT-w) from the PDF-verified FGMN rank-one theorem; the status
> supersession; and the nonzero-scalar re-display of Λ_N/JC-SCAL.
> Everything above this heading is byte-untouched by this append. The
> E4 adjudication, transcribed unaltered:
>
> All five findings are REAL at HEAD. **None is cured by Annexes #1–#3 or by the acceptance record alone.** Each defect is repairable from the note's existing inputs; **no experiment or new unproved mathematics is needed.**”

**★★ THE MOST CONSEQUENTIAL SINGLE FACT IN THE GRTJC STACK: a DECORRELATED MODEL, reading the note as-built AFTER eight hostile passes and an acceptance at 2/2, found FIVE REAL defects — including a CRITICAL against a live proof of one of the four faces.** **Compare GRTJB: the same certifier found 2 REAL of 4 there. Here it is 5 of 5.**

**★ AND THE TWO MITIGATING CLAUSES ARE EQUALLY IMPORTANT:** “**Each defect is repairable from the note's existing inputs**; **no experiment or new unproved mathematics is needed.**” **So the five findings are about how the note SAYS things, not about whether they are true** — and every repair is derived from what the note already had.

**ARITHMETIC AUDIT (rule 22):** findings = 5; all 5 REAL; repairs = Annexes #4–#8 = **5** ✔ **a clean one-to-one map, unlike GRTJB's 4 findings → 2 repairs.**

**CONDITIONALITY:** **The freeze is declared in this very paragraph** (“Everything above this heading is byte-untouched by this append”) and the transcription discipline (“transcribed unaltered”).

**PIN VERIFICATION:** `runs/cert/C4_grtjc_output.log` and `runs/cert2/E4_grtjc_output.log` are named as evidence; **this compiler did not re-read them** (run logs, not repo statements) — recorded as checkable pins.

**DERIVATION:** Adjudication record.

**RESOLUTION TRACE:** statement lines 2819–2834; the five repairs 2836–3037 (`.127`–`.131`); the verification record 3039–3059 (`.132`).

**TEETH:** **AUDIT — decorrelated-model audit** (rule 27). **This is the finding class the rule exists for, and GRTJC is its strongest single case in the corpus.**

---
### EFF.GRTJC.127  [supplier-finding]  ★★ ANNEX #4 — the W-8 quotient route (the CRITICAL cured)

**CANONICAL STATEMENT:** verbatim, lines 2836–2884 — the finding head and the annex with its two tagged displays and consumer sweep.
**FORM:** H3 finding head + blockquoted annex with LaTeX displays.

> “### 1. REAL — W-8 improperly lifts a quotient equality
>
> The acceptance record mentions PE8's correct congruence route but does not amend §4.1. Transcribe:
>
> > **[ANNEX 2026-08-12 #4, post-acceptance correction — W-8 is a quotient computation, not a polynomial lifting.]** This annex supersedes §4.1 from “Apply \(\rho_{\lambda+N}\)” through “The two agree.” Put
> > \[ q:\Delta=K_m[y]\longrightarrow \Delta/(\psi_m)=K. \]
> > The fence-clean defining equation for \(c=c_{m+1}(\gamma,\gamma')\) holds in the **TC-transported ring**, hence after TC-3. Therefore applying the coordinate calculus gives the **congruence** … **not the corresponding equality in** \(\Delta\). By the offset-transport lemma, \(A(\lambda,N)\in K_m^*\), so its image in \(K\) is nonzero and cancels. … Cancelling \(a_N\in K_m^*\) yields exactly
> > \[ c=q\!\left(A(\gamma,\gamma')\right). \tag{W8-q} \]
> > Independently, the same-line read identity \((\dagger)\) … gives \(c_{\mathrm{val}}(\gamma,\gamma') =q(\rho_\lambda(\operatorname{in}\phi_\gamma\operatorname{in}\phi_{\gamma'})) =q(A(\gamma,\gamma'))\). Thus \(c_{m+1}(\gamma,\gamma')=c_{\mathrm{val}}(\gamma,\gamma')\) exactly. …
> > **The former display \(\widetilde c(y)=A(\gamma,\gamma')\) is valid only when both polynomials have degree \(<g_m\), in particular when \(\delta<g_m\). On the load set \(\delta\ge g_m\), only the congruence \(\widetilde c(y)\equiv A(\gamma,\gamma')\pmod{\psi_m}\) holds; this is exactly compatible with JC-LOAD's proof that RAW polynomial equality fails there.**
> >
> > **Consumer sweep.** W-8 survives with conclusion unchanged by (W8-q). JC-INNER and W-7 OB-3 VALUE consume only \(c_{m+1}=c_{\mathrm{val}}\), so both survive unchanged. **W-9's cocycle semantics and the residue-chain statement survive.** **JC-LOAD is not weakened; its load-set obstruction is now explicitly respected rather than contradicted.**”

**TYPE JUSTIFICATION (rule 13):** `supplier-finding`, **INBOUND from a decorrelated certifier** — a defect report against this note's own displayed proof.

**SUPERSESSION KIND: `partial-withdrawal`** — a proof ROUTE replaced, conclusion preserved, the invalid step named. **(The enum gap all four shards of this queue have now confirmed.)**

**★ THE DEFECT IN ONE SENTENCE: §4.1 lifted a quotient equality to `Δ`, and ON THE LOAD SET that lift is exactly what JC-LOAD proves impossible — so the note's own W-8 proof contradicted its own JC-LOAD.** **The repair replaces the lift by a congruence; `c = q(A(γ,γ′))` is all W-8 needs.**

**★ THE HEAD SENTENCE IS ALSO A FINDING ABOUT THE ACCEPTANCE: “The acceptance record mentions PE8's correct congruence route but does not amend §4.1.”** **PE8 used the right route in its re-proof — and the body was never brought into line.** So the defect survived a clean pass that had itself avoided it.

**INDEPENDENT CHECK BY THIS COMPILER:** at `g_m = 1, δ = 1` (the load set), `A(γ,γ′) = (u/a_λ)y^1` has degree 1 while `c̃(y)`, the canonical representative of `c ∈ K` of degree `< g_m = 1`, is a **constant**. **`c̃ = A` is impossible as a polynomial identity; `c̃ ≡ A (mod ψ_m)` is unproblematic.** **The counter-configuration is exact and is precisely JC-LOAD's load set.** ✔

**CONDITIONALITY:** **Four survivals are stated and one strengthening: JC-LOAD's obstruction is “now explicitly respected rather than contradicted”.**

**DERIVATION:** Displayed: the defining equation holds after TC-3, so only the congruence descends; `A(λ,N)` and `a_N` are in `K_m^*` and cancel in `K`.

**RESOLUTION TRACE:** statement lines 2836–2884; **the superseded span 1691–1710 (shard 2 `.85`)**; JC-LOAD 859–924 (shard 2 `.62`); the verification 3041–3048 (`.89`).

**TEETH:** **AUDIT — decorrelated-model audit.** **P5-OB6 agreed 0/669 — the machine never saw the defect, because the IDENTITY is true; only the written route was invalid.** **The strongest argument in this note for rule 27.**

---
### EFF.GRTJC.128  [supplier-finding]  ★ ANNEX #5 — the load-set qualifier

**CANONICAL STATEMENT:** verbatim, lines 2886–2911.
**FORM:** H3 finding head + blockquoted annex with a boxed display.

> “### 2. REAL — “not obtainable before TC-3” needs the load-set qualifier
>
> **JC-LOAD itself proves the counterexample supplied by the finding.** Transcribe:
>
> > **[ANNEX 2026-08-12 #5 …]** This annex supersedes W-6(iv), JC-LOAD(a), and **every unqualified occurrence** of “\(\bar z^\delta\) is not obtainable from TC-1/TC-2 alone” by the following display:
> > **The outer factor is always \(q(y^\delta)=\bar z^\delta\), and it is unavailable as a pre-TC-3 scalar exactly when \(\delta\ge g_m\).**
> > * if \(\delta<g_m\), then \(y^\delta\) is already the canonical degree-\(<g_m\) representative of \(\bar z^\delta\), so the outer factor—and, after multiplication by the inner \(K_m^*\)-unit, the complete scalar—**is obtainable before TC-3**;
> > * if \(\delta\ge g_m\), no nonzero polynomial of degree \(<g_m\) equals \(u\,y^\delta\) with \(u\in K_m^*\), so **TC-3 is indispensable**. …
> > **Consumer sweep.** **JC-LOAD's iff and its sealed set identity survive unchanged.** §3.2's structural outer/inner split survives … §7 genres 1–2 remain RAW-solvable and genres 3–4 retain the stated \(g_m=1\) split. **W-7, W-8, and W-9 consume the factor's value or shape, not the refuted universal interpretation, and survive.**”

**SUPERSESSION KIND: `partial-withdrawal`.**

**★ “JC-LOAD ITSELF PROVES THE COUNTEREXAMPLE SUPPLIED BY THE FINDING” — the note's own iff already contained the correction; only the surrounding GLOSS over-reached.** **So the defect is a prose over-generalization of a correctly-stated theorem** — the same shape as GRTJB's E-4, and the same class of defect the arc had already fought at r1/F2 (an over-quantified closing sentence).

**★ A SWEEP-SCOPE HAZARD: the annex supersedes “EVERY UNQUALIFIED OCCURRENCE” of a phrase, not a named site list.** **This compiler found two in range (W-6(iv) at shard 2 `.54`, JC-LOAD(a) at shard 2 `.62`); the sweep is not certified complete** — the same limitation class GRTJC itself discloses for its name-pattern census.

**CONDITIONALITY:** All four faces survive; the sealed set identity is untouched.

**DERIVATION:** Displayed: JC-SCAL identifies the pre-TC-3 scalar image with the nonzero polynomials of degree `< g_m`; JC-SPAN gives the anchor-product coordinate `u y^δ`; equality is possible exactly when `δ < g_m` — **which is JC-LOAD's proved equivalence.**

**RESOLUTION TRACE:** statement lines 2886–2911; the targets 679–683 (W-6(iv), shard 2 `.54`) and 871–873 (JC-LOAD(a), shard 2 `.62`); the verification 3048–3050 (`.89`).

**TEETH:** **AUDIT — decorrelated-model audit.** MJ1's 103 firings, all in the load set, corroborate the corrected reading exactly.

---
### EFF.GRTJC.129  [supplier-finding]  ★★ ANNEX #6 — LEMMA JC-RANKMULT, the derived bridge

**CANONICAL STATEMENT:** verbatim, lines 2913–3000 — the finding head, LEMMA JC-RANKMULT with its (RM) display and proof, the derived (DMULT-w) corollary, the `e_m = 1` fence, the consumer sweep and the boxed stack entry.
**FORM:** H3 finding head + blockquoted annex with tagged LaTeX displays.

> “### 3. REAL — the multiplicativity bridge was absent, but is derivable
>
> Annex #3 verifies rank-one freeness, not the quoted product formula. The needed bridge can instead be proved from that freeness plus the note's anchor calculation:
>
> > **[ANNEX 2026-08-12 #6 …]** **The statement that (DMULT-w) is itself a quoted FGMN residual-product identity is withdrawn.** The load-bearing coordinate calculus is instead derived from the PDF-verified rank-one theorem as follows.
> >
> > **LEMMA JC-RANKMULT.** After JC-LOC and W-1 transport, for every \(n\in\mathbb Z\), \(B_n\) is a free rank-one module over \(B_0\simeq\Delta=K_m[y]\) on the virtual anchor \(\operatorname{in}\phi_n\), and \(\rho_n^B\) is its coefficient map. Consequently, for all \(\lambda,\mu\in\mathbb Z\),
> > \[ \rho_{\lambda+\mu}^B(\alpha\beta) =A(\lambda,\mu)\rho_\lambda^B(\alpha)\rho_\mu^B(\beta), \qquad A(\lambda,\mu) =\rho_{\lambda+\mu}^B(\operatorname{in}\phi_\lambda\operatorname{in}\phi_\mu). \tag{RM} \]
> >
> > *Proof.* PDF-verified FGMN Thm 4.2 states that the attained graded piece is a free rank-one \(\Delta\)-module on its printed anchor … JC-LOC identifies its graded ring with \(B\). W-1 identifies the printed residual operator with the harness operator by \(\mathcal R_n=c_nR_n^{\mathrm{GMN}}\), \(c_n\in K_m^*\) … Since \(a_n=\mathcal R_n(\phi_n)\), normalizing gives \(\rho_n^B=\mathcal R_n/a_n\); **the line unit \(c_n\) and the anchor-associate unit cancel.** … For \(\alpha=p\,\operatorname{in}\phi_\lambda\) and \(\beta=q\,\operatorname{in}\phi_\mu\) … \(\alpha\beta =pq\,A(\lambda,\mu)\operatorname{in}\phi_{\lambda+\mu}\), which proves (RM). …∎
> >
> > **COROLLARY (DMULT-w, derived where consumed).** Assume \(e_m\ge2\). … \[ \mathcal R_{\lambda+\mu}(fg) = \underbrace{\frac{u_{\lambda,\mu}}{a_\lambda a_\mu}}_{\omega(\lambda,\mu)\in K_m^*} y^{\delta(\lambda,\mu)} \mathcal R_\lambda(f)\mathcal R_\mu(g). \]
> > **This is (DMULT-w), derived from the note's cited rank-one theorem and its proved anchor-slot lemma.** … Clearing powers of \(\pi\), followed by JC-PIINV, gives the same formula on all transported lines.
> >
> > For \(e_m=1\), JC-RANKMULT and (RM) remain proved at general \(m\), but the last monomial-shape deduction stops at JC-SPAN's existing top-flat bound. **Thus JC-BOX-4 retains its honest FGMN-independent open/measured branch; no claim that the PDF itself supplies a multiplier formula is made.**
> >
> > **Consumer sweep.** * (COORD-B)(2) survives at every \(m\), **now directly from JC-RANKMULT rather than from an unquoted product law.** * (MULT-B), JC-IND, W-7's bijectivity, and **W-9 survive at every \(m\) by (RM).** * JC-CARRY-m and JC-LOAD survive on their displayed \(e_m\ge2\) scope by the derived (DMULT-w). * **W-8 survives at general \(m\)**: it needs (RM), offset multiplication by the \(\pi\)-periodic anchor, and the quotient calculation in Annex #4 — **not a separately quoted residual-product theorem.** * JC-COB's exact multiplier-one refinement remains on (DMULT-s) …
> >
> > The current FGMN stack entry is therefore:
> > **FGMN (a)(b) + Thm 4.2 rank-one freeness on \(B\) via JC-LOC + Thm 4.8/Cor 4.9 + Cor 2.7; (DMULT-w) derived above; (DMULT-s) as in Annex #1.**”

**SUPERSESSION KIND: `partial-withdrawal`** — a CITATION CLAIM withdrawn and replaced by a DERIVATION.

**★★ THIS IS THE TERMINAL OF THE `(IN-3)(c)` CHAIN, AND IT MAKES THE NOTE STRICTLY BETTER.** The finding is that **Annex #3 verified rank-one freeness, NOT the quoted product formula** — so the note had been citing a product law it had not verified. **The repair does not weaken anything: it DERIVES the product law from the freeness it did verify, plus JC-SPAN and the anchor normalization.** **The literature footprint shrinks again: no product law is cited at all.**

**★ THE `e_m = 1` FENCE IS SCRUPULOUS: “JC-BOX-4 retains its honest FGMN-independent open/measured branch; no claim that the PDF itself supplies a multiplier formula is made.”** **The annex refuses to launder the corner.**

**★ AND W-9 IS EXPLICITLY CARRIED: “(MULT-B), JC-IND, W-7's bijectivity, and W-9 survive at every `m` by (RM).”** — the third of three annex survival statements for the face WELDZERO consumes.

**CONDITIONALITY:** Rides **JC-LOC** and **W-1 (ATTEMPT)**, as before — the transport is untouched and remains the live weak link.

**DERIVATION:** Displayed in full: rank-one freeness + the coefficient-map identification (with `c_n` and the anchor-associate unit cancelling in `ρ^B_n = 𝑅_n/a_n`) ⇒ (RM); then JC-SPAN's `u_{λ,μ}y^δ` for the anchor product ⇒ `A(λ,μ)`; substituting `ρ_ν = 𝑅_ν/a_ν` ⇒ `(DMULT-w)` with `ω = u_{λ,μ}/(a_λa_μ)`.

**RESOLUTION TRACE:** statement lines 2913–3000; the tier 1188–1267 (shard 2 `.69`); JC-LOC 1037–1104 (shard 2 `.65`); JC-SPAN 829–857 (shard 2 `.61`); the verification 3050–3054 (`.89`); Annex #3 2809–2815 (`.82`).

**TEETH:** **AUDIT — decorrelated-model audit.** **R1-DMULT/R2-BIL measured the EXACT tier all along; what the annex fixes is the weak tier's provenance.**

---
### EFF.GRTJC.130  [changes-record]  ★★ ANNEX #7 — the EXPRESS status supersession (the model GRTJB lacks)

**CANONICAL STATEMENT:** verbatim, lines 3002–3008.
**FORM:** H3 finding head + blockquoted annex.

> “### 4. REAL — the live status records conflict
>
> The later acceptance record states the intended result but never expressly supersedes the body's still-“CURRENT” r6 status and proof-grade prohibition. Transcribe:
>
> > **[ANNEX 2026-08-12 #7, orchestrator status correction.]** The ★ ACCEPTANCE RECORD (orchestrator, 2026-08-06) ★ expressly **supersedes** `[r6] S-STATUS (CURRENT)`, §10.1's “acceptance counter 0/2,” every body-local “JC-PE7 next” phrase, and every body-local prohibition on proof-grade consumption that is based solely on this note's former \(0/2\) counter. Those passages are ROUND-RECORDS describing the state after r6 and before PE7/PE8; **their word “CURRENT” is no longer live.**
> >
> > **Current status at HEAD:** this note is **ACCEPTED at 2/2**, conditionally on exactly the input stack and fences named by the Acceptance Record **together with the post-acceptance corrections in Annexes #4–#8**. PE7 and PE8 are completed clean passes, not future attempts. **Acceptance of this note does not upgrade any upstream ATTEMPT-grade input or remove any displayed scope fence.**”

**SUPERSESSION KIND: `replacement`** — an express, itemised status supersession.

**★★ THIS IS THE UNIT GRTJB'S OPEN-CALL 1 ASKS FOR, AND IT SHOULD BE THE CORPUS TEMPLATE.** It does four things GRTJB's acceptance record does not:
1. **Names each stale passage by designation** — `[r6] S-STATUS (CURRENT)`, §10.1's counter, every “JC-PE7 next”, every proof-grade prohibition **based solely on the former counter**.
2. **Classifies them correctly** — “ROUND-RECORDS describing the state after r6 and before PE7/PE8”.
3. **States the current status WITH its conditionality** — accepted “conditionally on exactly the input stack and fences named by the Acceptance Record **together with the post-acceptance corrections in Annexes #4–#8**”. **So the acceptance is explicitly extended over the later corrections**, closing the chronology gap that GRTJB leaves open.
4. **Fences the acceptance** — “does not upgrade any upstream ATTEMPT-grade input or remove any displayed scope fence”. **So the gate clauses, JC-BOX-2's open half, JC-BOX-5's OPEN row and JC-BOX-8's residues all survive intact.**

**★ THE QUALIFIER “based solely on this note's former 0/2 counter” IS PRECISE AND MATTERS:** prohibitions grounded in something else — the gates, the boxes — are NOT superseded. **A blanket supersession would have retired J3b by accident; this one cannot.**

**CONDITIONALITY:** None; it is the status of record.

**DERIVATION:** Orchestrator status correction, prompted by the certifier's finding 4.

**RESOLUTION TRACE:** statement lines 3002–3008; the targets 149–185 (shard 1 `.10`), 2649 (`.22`), 2049–2056 (`.08`), and every face box's “Attempt 0/2” (shard 2 `.54`, `.75`, `.84`, `.89`); the acceptance record 2787–2799 (`.79`).

**TEETH:** NONE (status). Disposition: **AUDIT — decorrelated-model audit** on the finding; **record-grade** on the repair (the orchestrator's own verification calls it exactly that: “Annex #7 is a status-record supersession (record-grade)”).

---
### EFF.GRTJC.131  [supplier-finding]  ★ ANNEX #8 — nonzero scalar lifts and zero coordinates

**CANONICAL STATEMENT:** verbatim, lines 3010–3037.
**FORM:** H3 finding head + blockquoted annex with displays.

> “### 5. REAL — \(\Lambda_N(0)\) and the zero-target quantifiers are false
>
> Restricting the lift to the nonzero scalars actually consumed is the simplest correct display. The same repair should close JC-BSURJ's related zero-target wording.
>
> > **[ANNEX 2026-08-12 #8 …]** The scalar-lift definition and every JC-SCAL quantifier are re-displayed at their true proved-and-consumed scope:
> > \[ \Lambda_N(c):=\operatorname{realize}(NR,c,N), \qquad c\in K^*,\quad N\equiv0\pmod E,\quad N\ge w\Phi_{NR}. \]
> > For these and only these targets, REALIZE R2/R3 give \(w(\Lambda_N(c))=N\), \(\operatorname{read}(N,\Lambda_N(c))=c\).
> > **No value \(\Lambda_N(0)\) is supplied by REALIZE. The zero polynomial represents the zero class and has zero read, but it does not have weight \(N\).**
> > Accordingly JC-SCAL is re-displayed with \(c\in K^*\). Its scalar-image conclusion is \(\mathcal R_N(X_N)\cdot\{p\in K_m[y]:p\ne0,\ \deg p<g_m\}\).
> > The same zero convention repairs JC-BSURJ: for every **nonzero** \(p\) … For \(p=0\), surjectivity uses the zero element of \(B_n\); no exact finite-weight representative is asserted. **Thus \(\rho_n^B:B_n\to\Delta\) remains surjective.**
> > **Consumer sweep.** JC-LOAD already quantifies \(c\in K^*\) and survives. W-8's \(c_{m+1}\) is a unit by JC-CARRY-m, so its lift remains defined. \(X_N=\Lambda_N(1)\) is unchanged. **JC-SCAL, JC-BSURJ, COORD-B, and all downstream carrier-dimension arguments survive.** Historical JC4/R1-SURJ machine rows **retain their numerical counts but evidence only defined nonzero lifts and nonzero polynomial targets**; their phrases “every \(c\in K\)” are superseded by this annex.”

**SUPERSESSION KIND: `partial-withdrawal`** — a quantifier narrowed with a replacement display.

**★ THE DEFECT IS SMALL AND THE HANDLING IS EXEMPLARY: a definition quantified over `c ∈ K` when REALIZE supplies nothing at `c = 0`, because the zero polynomial “does not have weight `N`”.** **Everything survives, and the annex says exactly what the historical machine rows now evidence: “their numerical counts but … only defined nonzero lifts and nonzero polynomial targets”.**

**★ AND THE NOTE HAD ALREADY CAUGHT A SYMPTOM: r5/m-1 added “nonzero” to §2.8's RHS display seven rounds earlier** (shard 1 `.15`). **The general repair is Annex #8's.** **A local patch that did not generalize — a recognisable pattern in this arc.**

**CONDITIONALITY:** **`ρ_n^B` remains surjective** — the conclusion the whole coordinate calculus needs is untouched, using the zero element of `B_n` for `p = 0`.

**DERIVATION:** REALIZE's own scope (R2/R3 give `w = N` and `read = c` only for `c ∈ K^*`).

**RESOLUTION TRACE:** statement lines 3010–3037; the targets 640–641 (shard 1 `.51`), 807–825 (shard 2 `.60`), 1145–1166 (shard 2 `.67`); the early symptom 256–259 (shard 1 `.15`); the verification 3055–3057 (`.36`).

**TEETH:** **AUDIT — decorrelated-model audit.** JC4 (443) and R1-SURJ (841) keep their counts with a narrowed evidentiary reading.

---
### EFF.GRTJC.132  [changes-record]  the orchestrator verification record

**CANONICAL STATEMENT:** verbatim, lines 3039–3059.
**FORM:** italic parenthetical closing block.

> “*(The adjudication above was produced by the E4 certification run
> (gpt-5.6-sol high, runs/cert2/E4_grtjc_output.log, 2026-08-12);
> orchestrator verification before transcription — **Annex #4's quotient
> route re-checked** (the defining equation holds after TC-3, so only
> the congruence descends; A(λ,N) and a_N in K_m^* cancel in K, giving
> c = q(A(γ,γ′)) = c_val exactly, with the polynomial-equality display
> scoped to δ < g_m — **now consistent with JC-LOAD's RAW ⟺ δ < g_m
> rather than contradicting it**, and the C4 counter-configuration
> (g_m = 1, δ = 1: deg A = 1 vs deg c̃ < 1) is resolved as a
> congruence, not an equality); **Annex #5's boxed criterion checked**
> against JC-SCAL/JC-SPAN …; **Annex #6's (RM) re-derived**
> (free rank-one coefficient maps multiply through the anchor product)
> and the (DMULT-w) substitution algebra re-checked (a_{λ+μ} cancels,
> multiplier u/(a_λa_μ) ∈ K_m^* depends on the two lines only), with
> the e_m = 1 branch honestly left at JC-SPAN's top-flat bound;
> **Annex #7 is a status-record supersession (record-grade)**; **Annex #8's
> scoping checked** (REALIZE supplies weight-N reads for c ∈ K^* only;
> the zero polynomial has no weight N). Transcribed unaltered per the
> standing division of labor. Ledger: row 22 → **all five repairs folded,
> awaiting sol discharge (cert3)**.)*”

**★ ALL FIVE ANNEXES WERE RE-DERIVED BEFORE TRANSCRIPTION, and the record itemises what was checked for each — three of them are mathematics re-done independently** (Annex #4's quotient route with the counter-configuration resolved; Annex #5's criterion against JC-SCAL/JC-SPAN; Annex #6's (RM) and the substitution algebra). **The same discipline GRTJB's certifier annex uses, applied to five findings instead of two.**

**INDEPENDENT RE-DERIVATION BY THIS COMPILER (Annex #4's counter-configuration):** at `g_m = 1, δ = 1`, `deg A(γ,γ′) = 1` while `c̃` has degree `< 1`, i.e. is constant. **A polynomial equality is impossible; a congruence mod `ψ_m` (which has degree `g_m = 1`) is not.** **EXACT.** ✔ **(Annex #6's substitution algebra also re-checked: `𝑅_{λ+μ}(fg)/a_{λ+μ} = (u_{λ,μ}/a_{λ+μ})y^δ · (𝑅_λ(f)/a_λ)(𝑅_μ(g)/a_μ)` ⇒ multiplying by `a_{λ+μ}` gives `ω = u_{λ,μ}/(a_λa_μ)`, depending only on the two lines. EXACT.** ✔)

**CONDITIONALITY:** **“awaiting sol discharge (cert3)” — the arc is NOT closed.** The repairs are folded; the discharge is pending. **Same status as GRTJB's.**

**DERIVATION:** Verification record.

**RESOLUTION TRACE:** statement lines 3039–3059; the five annexes 2836–3037 (`.127`–`.131`).

**TEETH:** **AUDIT — decorrelated-model audit with in-house re-derivation before transcription**, re-derived a third time here for two of the five.

---

---

## 4. XREF verification ledger and local supply/consumption ledger (summary)

**61 raw XREF citations across the three shards (28 + 19 + 14), every one individually
grep-verified with a fixed-string count ≥ 1 by its home shard, recorded inline at its
unit.** This merge re-sampled **12 citations** against the working tree; all 12 matched
the shard's recorded count exactly (the GRTJB-side interface count `JB-BOX-2` **45**,
`JB-CREAD` **36**, `JB-EPS` **30**, `JB-BOX-4` **2** — cross-verified from the GRTJB side
too, `spec/EFF-GRTJB-s2of3.md` §3.1 rows 64–67, agreeing after one earlier-draft
correction the shard itself records: `JB-BOX-2` is 45, not the 17 an earlier draft
asserted). **23 commit hashes verified `git cat-file -t = commit`** (23/23); **2 md5 pins
re-computed EXACT**; **12 battery artifacts and 6 PE1–PE6 report files verified to exist**;
**the FGMN PDF md5 EXACT at HEAD**; **10 of 11 FGMN layout line pins EXACT, the eleventh
(Annex #2's Corollary 4.9 pin) a verified off-by-two** (says 1153, actual 1151; content
exact).

**Local supply/consumption ledger.** GRTJC supplies THEOREM W-6/W-7/W-8 and **COROLLARY
W-9** (the four weld-junction faces), LAW JC-CYC, and the eleven-genre case split, to
consumer `WELDZERO_2026-08-14.md` (which discharges GENHN-BOX-2 by replacing W-9's four
clauses one-for-one — clause-by-clause, not as one opaque face — per the per-clause
consumer table reproduced at `.89` in §3) and to `runs/qgen/WELD_FACE_AUDIT.md`. **GRTJC
consumes GRTJB's `.03`/`.79`-side germ `ρ_m(R) = −z_{m+1}·ρ_m(f)`** as the J-C carrier
block's semantic input — displayed as an identity of READ VALUES only, no gr object
constructed, `DITERSUP` gate J3b NOT retired by either side. **Neither side retires the
gate; both notes say so.**

---

## 5. TEETH inverse table (condensed; full per-row detail in the three shard files' own §5)

`[TABLE — compiler ledger]` Vocabulary as the companion GRTJB merge (§5 there).

| Battery row / instrument leg | Guarded unit(s) | Disposition |
|---|---|---|
| The instrument (`grt_jc_probe.py`) — 29 towers, 669 scored pairs, 22 families GREEN | `.03`, `.41`, `.53` | Executable regression **on a decorrelated determination** |
| The instrument's refutation — H-D fails 138/669; H-B 215; H-C 73 | `.03` | **Measurement, refuting the brief's germ hypothesis before the proof was written** |
| r0 battery (`grt_jc_checks.py`) — 10 families, 8,566 samples, 0 violations, 5 teeth (1,054 firings) | `.04` | Executable regression + planted mutants. **Headline reconstructs exactly** |
| JC3 — the new sharp prediction, slot set == {δ} | `.53` | Executable regression, **609/609 on `e_m ≥ 2` rows** |
| JC8's unit half | `.107` | **VACUOUS AS CODED** — "the violation branch is unreachable and the skipped pairs were never censused". `signed vacuity disclosure`; replaced by R1-UNIT + T4 |
| MJ1 — "TC-3 never load-bearing" | `.53` | Planted mutant; **103 firings, all in the δ ≥ g_m load set, 0 anomalies** |
| r1 battery (`grt_jc_r1_checks.py`) — 10 families, 10,330 + 145, 0 violations, 5 teeth (1,885 firings) | `.34` | Executable regression; both headlines reconstruct exactly |
| R1-BND — `maxslot(G0) == 0` on 29/29 | `.31`, `.48` | A refutation converted into a permanent scored regression |
| T1 — the refuted r0 universal kernel claim | `.31`, `.32` | Planted mutant from a refuted claim; 29/29 firings |
| R1-PER — `𝑅_{λ+kE}(π^kf) == c_π^k·𝑅_λ(f)` | `.38` | Executable regression, 841 samples; `c_π ≠ 1` on 20/29 rows — normalization load-bearing |
| R1-DMULT — `(DMULT-s)` exact on sampled pairs | `.36` | Executable regression, 2,784/0 — **monomial-dominated, undisclosed skip** |
| R1-UNIT + T4 — falsifiable replacement for JC8's vacuous half | `.33` | 869 unit / 0 zero / 0 undefined; a planted zero caught on every row |
| MT3 — the cyclic-split, 9 single-pair escapes | `.83`, `.94` | Measurement, **9 escapes disclosed and mechanism understood**; permanently limited on small residue fields |
| §9.2/§9.3/§9.4 — r0 verdict, r1 verdict (eleven-row table), r2 bilinearity leg | `.107`, `.110`, `.113` | Executable regression ×3; **the r2 bilinear content was NEVER exercised by r1** (disclosed) |
| DULEMMA THEOREM DU (Annex #1's own machine leg `dulemma_checks.py`) | `.123` | **Cited, not independently verified to exist by this compiler** |

Full per-family disposition detail (roughly 15 additional rows) is preserved verbatim in
each shard's own §5 and is not re-typed here.

---

## 6. SERIES, supersession CHAINs, and cross-shard boundary resolution

### 6.1 The dated-arc SERIES: `S-STATUS` (GRTJC's grade chronology, 6 members) — the
sharpest methodological contrast with the companion GRTJB merge

Unit `.05 — .10` is a single combined block. **GRTJC uses TWO retention devices, load-
bearing for a merge:** `.05` (`[r1]`) is **STRUCK**; `.06`–`.10` (`[r2]`–`[r6]`) are **KEPT
ANNOTATED, not struck** — "a merge run must not treat an annotated block as live text."

| Member | Round | Verdict | Retention |
|---|---|---|---|
| `.05` | r1 | JC-PE1: 2 CRITICAL + 8 gaps | struck |
| `.06` | r2 | JC-PE2: 0C + 9 gaps | annotated |
| `.07` | r3 | JC-PE3: 0C + 8 gaps | annotated |
| `.08` | r4 | JC-PE4: 0C + 4 gaps | annotated |
| `.09` | r5 | JC-PE5: 0C + 2 gaps + 1 minor | annotated |
| `.10` (TERMINAL) | r6 | JC-PE6: 0C + 1 gap | annotated, CURRENT |

**Continuation:** JC-PE7 (`782000e`, CLEAN) → JC-PE8 (`9d240b6`, CLEAN) → **ACCEPTED 2/2**
(`.122`). **★ Unlike GRTJB, this terminal status is EXPRESSLY superseded**: Annex #7
(`.130`) names `[r6] S-STATUS (CURRENT)` by designation — "their word 'CURRENT' is no
longer live" — while the three GATE clauses (no gate retires, P0 gate stands, no
density/menu/count) are explicitly **NOT** superseded. **Tag: `superseded`, not
`STALE-SELF-DESCRIPTION`** — the distinction GRTJB's own text says it cannot make.

### 6.2 The post-acceptance arc (units `.26`–`.36`; the series' true continuation; "the
series header occupies no ID of its own")

| Unit | Content | Date |
|---|---|---|
| `.26` | ★ ACCEPTANCE RECORD — ACCEPTED 2/2 (PE7, PE8 CLEAN) | 2026-08-06 |
| `.27` | ANNEX #1 — (DMULT-s) PROVED-conditional (DULEMMA THEOREM DU) | 2026-08-08 |
| `.28` | ANNEX #2 — FGMN numbering discharged at the extraction | 2026-08-08 |
| `.29` | ★ ANNEX #3 — FGMN cites PDF-VERIFIED | 2026-08-12 |
| `.30` | the sol C4/E4 adjudication head — a CHALLENGE, **all five findings REAL** | 2026-08-12 |
| `.31` | ★★ ANNEX #4 — the W-8 quotient route (the CRITICAL cured) | 2026-08-12 |
| `.32` | ★ ANNEX #5 — the load-set qualifier | 2026-08-12 |
| `.33` | ★★ ANNEX #6 — LEMMA JC-RANKMULT, the derived bridge | 2026-08-12 |
| `.34` | ★★ ANNEX #7 — the express status supersession | 2026-08-12 |
| `.35` | ★ ANNEX #8 — nonzero scalar lifts and zero coordinates | 2026-08-12 |
| `.36` | the orchestrator verification record | 2026-08-12 |

**Merged IDs (adding this note's own SHARD-MAP offset +96):** `.122`–`.132`.

### 6.3 Supersession CHAINs (five distinct chains, all but two converging on one HOME)

| Chain | Layers | TERMINAL |
|---|---|---|
| **`.43`** — the `(IN-3)(c)`/`(DMULT)` alias-and-tier chain (the note's deepest, five layers; HOME, body sites at `.17`, `.36`, `.69`, `.120`) | r0 CITED on `gr` → r1/F1 refuted on `gr`, re-based on `B`, reduced to `(DMULT)` → r2/G-1 split into `(DMULT-w)` DERIVED / `(DMULT-s)` MEASURED → Annex #1 `(DMULT-s)` PROVED-conditional → Annex #6 `(DMULT-w)` WITHDRAWN-as-citation and DERIVED from Thm 4.2's rank-one freeness | Annex #6's derivation + Annex #1's conditional proof, jointly, at `.129`/`.127` |
| `.17` — the alias chain, 4 layers (body site of `.43`) | r0 → r4/G-1 (fourth alias) → r5/G-2 → r6/G-1 | reading as it stands at HEAD |
| `.46` — THE STACK, ONE LINE, 3 layers | r0 one-liner → r4/G-1 ((c) struck) → r5/G-2 ((a)(b) added) → r6/G-1 (annotated, live, superseded by nothing) | the display as it stands at HEAD |
| `.54` — THEOREM W-6's input list, 3 layers | r0 "(IN-3)(a)(b)(c)(e)+(IN-5)" → r1 `(IN-3)(c)`-on-`gr` replaced by `(DMULT)` → r2/G-1 split, only `(DMULT-w)` load-bearing | `(IN-3)(a)(b)(e)+(IN-5)+(DMULT-w)`, with `(DMULT-w)` DERIVED post-acceptance (Annex #6) |
| `.120` — §10.2's conditionality stack, 4 dated forms (body site of `.43`) | r0 → r1 (FGMN entry narrowed) → r2 (tier split) → r5/G-2 ((a)(b) completion) | Annex #6's boxed form, post-acceptance |

**All five chains' TERMINAL markers verified unique** by an exhaustive scan of every
`CHAIN (rule 25)` declaration in the merged 132-unit inventory (§3).

### 6.4 Full cross-shard supersession edge list (consolidated from all three shards' own
SHARD NOTES, with SUPERSESSION KIND)

| From (all homed in shard 3) | To | Kind | Content |
|---|---|---|---|
| Annex #1 (`.127`) | `.55`, `.72` | measured-perimeter proof | `(DMULT-s)` PROVED-conditional; JC-COB's sharp form inherits (DU-COB) |
| Annex #2/#3 (`.128`, `.129`) | `.43` (citation-precision flag), `.99` (JC-BOX-3 item 2) | discharge | FGMN cites PDF-VERIFIED |
| **Annex #4 (`.127`)** | **`.85` (§4.1's proof span, "Apply ρ_{λ+N}" through "The two agree.")**, `.84` | replacement, **cures a CRITICAL** | JC-LOAD's load-set obstruction now respected, not contradicted |
| Annex #5 (`.128`) | `.54`(iv), `.62`(a), and "every unqualified occurrence" elsewhere | wording-rider, **sweep not certified complete** | outer factor always `q(y^δ)`; only pre-TC-3 availability at issue |
| Annex #6 (`.129`) | `.69`(`/w` tier), `.68`, `.71`, `.80`, `.89` (survival only) | as-of scoping + derivation, **TERMINAL of the `.43` chain** | `(DMULT-w)` DERIVED via LEMMA JC-RANKMULT |
| **Annex #7 (`.130`)** | `.02`, `.05`–`.10`, `.46`; `.54`/`.75`/`.84`/`.89` (the four "Attempt 0/2"); `.104`, `.118`, `.119`, `.120` | **express status supersession** | `[r6] S-STATUS (CURRENT)` and every proof-grade prohibition based on the 0/2 counter superseded; GATE clauses NOT superseded |
| Annex #8 (`.131`) | `.51`, `.60`, `.67` | wording-rider | `Λ_N`'s quantifier narrowed to `c ∈ K^*`; JC-BSURJ's zero-target repaired |
| Acceptance record (`.122`) | the whole S-STATUS series `.05`–`.10` | grade update | ACCEPTED 2/2 |

**J-B ↔ J-C interface (inbound, from GRTJB):** `.03`/`.79` are the exact counterpart of
`spec/EFF-GRTJB-s2of3.md` `.54` (GRTJB's carry-seed remark, external, left un-renumbered
by design — §1's EXTERNAL-NOTE GUARD). **Both sides agree, and the agreement is
verifiable** (CONFIRMED as a value law on 27 eligible `g_m = 1` stages; REFUTED as OB-3's
inner factor on 138/669 pairs). Neither side retires `DITERSUP` gate J3b.

**★ W-9's per-clause consumer table (the load-bearing DAG anchor the charge specifically
asks to be carried byte-verbatim WITH its consumer column intact):** reproduced in full
at unit `.89` in §3 above — not re-typed here, per the same discipline HE7's merge used
for its own once-only tables. Summary only: clause (i) → WZ-1+WZ-2(a); clause (ii) →
WZ-2(a); clause (iii) → WZ-1(c)+GENHN-2; clause (iv) → **NOT CONSUMED**. The retirement of
GENHN-BOX-2 turns on exactly this per-clause split; a merge treating W-9 as one opaque
face would lose the whole discharge argument — the hazard both shard 2 and shard 3 flag as
their highest-severity merge item, discharged here by verbatim preservation.

### 6.5 Range-edge audit

Shard 1/2 boundary (660/661/662): `---`/blank/`## §2.` — clean section break. Shard 2/3
boundary (1936/1937/1938): `---`/blank/`## §8.` — clean section break. File end (3059) is
shard 3's own last line (the certification record's closing `(cert3).)*`). **Zero units
span a shard boundary.**

---

## 7. Self-audit and OPEN-CALLS (merged, dedup marked)

**15 raw OPEN-CALLs (5 per shard) — no two are self-identified duplicates, so all 15 are
carried distinctly, renumbered 1–15 in shard order.** None is discharged by the act of
merging.

### OPEN-CALL 1 — the manifest shards GRTJC into FOUR ranges; the charge names THREE
*(= shard 1 OPEN-CALL 1)*

See §1's dedicated subsection above (the rows-49+50 boundary resolution, merged at the
BACK — contrast with GRTJB's front-merge). **Decision needed: whether a merge run treats
GRTJC as 3-shard or 4-shard in its ID scheme.**

### OPEN-CALL 2 — Annex #4 cures a CRITICAL, and the acceptance predates it by six days
*(= shard 2 OPEN-CALL 2, restated by shard 3 OPEN-CALL 1)*

**GRTJC was ACCEPTED 2/2 on a text containing a CRITICAL against a live proof of W-8.**
Annex #7 handles the STATUS question ("together with the post-acceptance corrections in
Annexes #4–#8"), more than GRTJB does — but it is an orchestrator declaration, not a fresh
hostile pass on the corrected text. **Decision needed: whether W-8's acceptance needs
re-confirming on the post-annex text, and whether cert3's discharge (the GRTJB analogue is
"awaiting sol discharge (cert3)") is a prerequisite for the chapter blueprints.** The
compiler records that PE8's own clean pass used the CORRECT congruence route — the
mathematics was verified by a hostile reader before the body was amended. **This status is
carried forward exactly as found, unresolved by this merge.**

### OPEN-CALL 3 — W-9's consumer (WELDZERO) bypasses, rather than audits, the frame
*(= shard 2 OPEN-CALL 1)*

WELDZERO "does not re-derive GENHN's layer-1 *prose* … It proves layer 1's *conclusion*
from scratch"; W-9's clause (i) content is never checked against what GENHN-4 layer 1
actually used. **Decision needed: whether a residual check is owed** (the grep footprint
is one line, GENHN S6.1 L874 — strong evidence but a NAME grep, and this note's own r4/G-4
showed a name grep can miss a content line).

### OPEN-CALL 4 — the off-stratum existence claim is the note's most exposed statement,
signed as such *(= shard 2 OPEN-CALL 3, restated by shard 3 OPEN-CALL 3)*

`.77`(2)'s structure-constant existence claim off `[ILN]†`'s scored stratum has **zero
machine support**; eight hostile passes did not attack it despite JC-BOX-2's own
invitation. Not load-bearing for anything WELDZERO consumes — dropping it would cost
nothing.

### OPEN-CALL 5 — JC-CYC(d)'s measured resolution is low, and the note says so
*(= shard 2 OPEN-CALL 4)*

MEASURED at `m ≤ 3`, 0 violations on 29 rows — but only 2 of 29 rows lie OFF the collapse
geography. The program consequence downstream rides clause (b) (PROVED), not (d).

### OPEN-CALL 6 — three annexes each say "W-9 survives", but none re-checks its proof
*(= shard 2 OPEN-CALL 5)*

Annexes #4, #5, #6 each assert W-9 survives; **none re-derives its four clauses on the
corrected footing.** Cheap to close (the proofs are four lines); not yet done.

### OPEN-CALL 7 — five REAL findings after eight passes, and every one was a WRITING
defect *(= shard 3 OPEN-CALL 2 — flagged by the compiler as the single most transferable
methodological finding of the whole queue)*

"All five findings are REAL at HEAD. None is cured by Annexes #1–#3 or by the acceptance
record alone… no experiment or new unproved mathematics is needed." Eight hostile passes
verified the mathematics; a decorrelated as-built read found five statement-level defects
(one CRITICAL) that no in-arc pass caught. **GRTJB shows the same pattern at lower
intensity (2 REAL of 4). Decision needed: whether a decorrelated as-built read should be a
STANDARD terminal step for every accepted note, not an ad-hoc certification.**

### OPEN-CALL 8 — the off-stratum claim, the diversity gap, and the 606 perturbations were
all explicitly nominated as attack targets, and none was attacked
*(= shard 3 OPEN-CALL 3, related to OPEN-CALL 4 above)*

Three items the note itself invited hostile passes to attack ("a hostile pass should
attack it there first"; "should build `g_m ≥ 2` rows with small tables"; "NAMED, NOT
BUILT"). Eight passes attacked none. None is load-bearing for what WELDZERO consumes.

### OPEN-CALL 9 — Annex #1's proof of (DMULT-s) comes from a note (DULEMMA) that itself
consumes GRTJC *(= shard 3 OPEN-CALL 4)*

DULEMMA's THEOREM DU rides "[ILN]†+GRTJC+WELDMASTER as accepted" while proving `(DMULT-s)`
for GRTJC. **The scope split almost certainly saves it** (DU uses GRTJC's *other* clauses,
not the tier itself) — but neither note states the non-circularity argument explicitly.
A DAG built from the annexes alone would draw this edge backwards.

### OPEN-CALL 10 — "awaiting sol discharge (cert3)" on both weld-junction notes, and the
blueprints are next *(= shard 3 OPEN-CALL 5)*

Both GRTJB and GRTJC carry folded-but-undischarged post-acceptance repairs at HEAD.
**Decision needed: whether cert3's discharge gates the blueprint phase.** The repairs are
all narrowings or provenance corrections — safe in direction; what is unverified is
whether the folds are COMPLETE (Annex #5's "every unqualified occurrence" sweep is the
clearest place a fold could be partial).

### OPEN-CALL 11 — the `(IN-3)(c)` chain's per-clause status needs sub-IDs
*(= shard 1 OPEN-CALL/hazard, cross-referenced to §6.3's chain table)*

`.43` needs per-clause sub-IDs (a)/(b)/(c)/(d)/(e): three different statuses live under
one ID (live citations, refuted-as-transported-now-derived, unchanged-PDF-verified).

### OPEN-CALL 12 — the CITE-SCOPE flag was Q7's only substantive generality finding, and
it is a pasting artefact *(= shard 1 OPEN-CALL 2)*

NS-10: "The audit's flag was a pasting artefact, not a real gap … re-paste the §1 setting
sentence next to the quote." **The single cheapest generality repair in the whole weld
corpus.**

### OPEN-CALL 13 — GRTJC's supplier grades are stale, and it cannot know about GRTJB's
post-acceptance corrections *(= shard 1 OPEN-CALL 3)*

`.44`/`.46` state W-2/J-A/J-B at ATTEMPT grade; at HEAD all three are ACCEPTED. **GRTJC
cannot know about GRTJB's own E-3/E-4 corrections** (both post-date this note's freeze).
Neither correction touches JB-BOX-2's perimeter enumeration, so the inheritance is
**almost certainly unaffected** — but nothing in GRTJC says so.

### OPEN-CALL 14 — the alias census's completeness rests on a read-through, not a fixed
point *(= shard 1 OPEN-CALL 4)*

The census counts hit-lines by NAME; its completeness argument ("§0 is the only place the
package's clauses are DISPLAYED as propositions") is itself a read-through result, not a
structural check.

### OPEN-CALL 15 — three upstream documents still carry the JC-F2 defective display
*(= shard 1 OPEN-CALL 5)*

`GRW2_TIE_DESIGN` §S2.2, the GRT weld blueprint §S2.3, and the GRTJC brief all still
repeat the wrong "degree-0 component" definition. **The blueprint is one of the three
sources, and the chapter blueprints are about to be written from it.**

### Recorded source defects (flagged, not silently repaired; 17 raw, consolidated)

1. `.03`/`.04`: neither `grt_jc_probe.py` nor `grt_jc_checks.py` carries an in-note md5
   pin (unlike the r1/r2 runners, both EXACT); the r0/instrument freeze is asserted and
   verified only by PE1/PE2 re-runs.
2. `.05`–`.10`/`.122`: PE7/PE8 pinned by commit only (`782000e`, `9d240b6`, both resolve);
   no report filenames — **identical to GRTJB's PE9/PE10 defect.**
3. `.43`/`.124`: Annex #2's line pin for Corollary 4.9 is off by two (1153 vs actual 1151);
   content exact.
4. `.11`–`.39`: the round blocks appear in reverse chronological order, unflagged by any
   header sentence — a reading hazard, not an error.
5. `.13`: four line pins given "at `edbb966`", a historical commit — not re-verified at
   that commit by this compiler.
6. `.46`: the r4 bracket's pointer was inverted by r5, corrected only by an r6
   ANNOTATION inside it — a reader stopping at r4 gets the wrong stack.
7. `.54`/`.75`/`.84`/`.89`: all four face boxes carry "Attempt grade 0/2", **EXPRESSLY
   superseded by Annex #7** but not edited — tagged `superseded`, not stale.
8. `.85`/`.127`: §4.1's frozen proof carries **no inline pointer to Annex #4** at the
   defect site — a reader of §4.1 alone gets no warning.
9. `.62`(a)/`.54`(iv)/`.128`: Annex #5's "every unqualified occurrence" sweep is not
   certified complete — this compiler found two in range, the same limit class the note
   discloses for its own name-pattern census.
10. `.69`: `(DMULT)`'s status changed FOUR times; no single place states the terminal
    status — assembled from §2.10, Annex #1, Annex #6; Annex #6's boxed entry treated as
    TERMINAL.
11. `.117`: 22-vs-37 discrepancy in a headline, corrected in-text; flagged for
    completeness.
12. `.123`: `dulemma_checks.py` cited as Annex #1's machine leg; not verified to exist by
    this compiler.
13. `.107`: JC8's headline reporting a vacuous-as-coded unit half, replaced downstream by
    R1-UNIT+T4 — recorded, not silently merged into the replacement's own figures.
14. `.112`: a vacuous evidence claim struck and corrected in place (arc display).
15. `.118`: four struck arc displays in the grade box, superseded by Annex #7's express
    supersession.
16. `.129`: "no claim that the PDF itself supplies a multiplier formula is made" — a
    scope fence, not a defect, recorded for completeness alongside the withdrawn quoted
    product law.
17. `.30` vs `.126`: the C4/E4 run's "a CHALLENGE with a CRITICAL" head-count and the
    certifier's own "all five findings REAL" summary use slightly different framing
    language for the same five findings — not a numeric mismatch, recorded for reading
    clarity only.

### Fidelity audit (merge-level, in addition to each shard's own three independent audits)

- All 132 canonical statement units carry CANONICAL STATEMENT, CONDITIONALITY,
  DERIVATION, RESOLUTION TRACE, and TEETH fields, verbatim-or-`[ASSEMBLED]` per template
  v2/v3. No inverse, sign, quantifier, index, level, inequality, or implication direction
  was altered anywhere in the renumbering pass.
- **The ID-renumbering rewrite was performed mechanically** (the same Python
  context-tracking script as the companion GRTJB merge, extended with the EXTERNAL-NOTE
  GUARD verified necessary and correct here — five GRTJB cross-citations preserved
  byte-unchanged, confirmed by direct inspection of the rewritten output). Script output
  audit: **zero leftover `sKof3` substrings, zero out-of-range IDs (every ID in 1–132),
  the ID sequence covers 1..132 exactly once.**
- **10+5 fresh sample verification, zero drift found:** 10 cross-shard citations
  re-checked against the shard's own recorded value — the `.43` chain's four body-site
  edges `.17`/`.36`/`.69`/`.120` (EXACT ×4), the W-9 unit `.89`'s source-range citation
  (L1777–1788, independently re-read at HEAD, EXACT), the Annex #4 edge `.127`→`.85`/`.84`
  (EXACT), the Annex #7 status-supersession edge `.130`→ the whole S-STATUS series
  `.05`–`.10` (EXACT), the J-B↔J-C external edge `.03`/`.79`→`spec/EFF-GRTJB-s2of3.md .54`
  (EXACT, and confirmed left un-renumbered by design), the five external-GRTJB citations
  scattered through §3 (all five confirmed still reading their original GRTJB shard-local
  numbers, not GRTJC merged IDs). **5 additional spot samples:** the blob hash (EXACT,
  STOP condition did not trigger), the SHARD-MAP offset arithmetic (53, 96, 132 — EXACT),
  the S-STATUS arithmetic audit's own commit census (23/23 `git cat-file -t = commit`,
  independently re-checked on 5 of the 23), the JD0-negative grep claim (re-run at write
  time: `grep -c "JD0\|J-D0" spec/EFF-GRTJC-s*.md` = 0, confirmed), and unit `.127`'s
  Annex #4 counter-configuration re-derivation cross-checked against shard 3's own
  independent re-derivation (both EXACT, matching). **Zero drift across all 15.**
- Absorption (predicate A), append/consumption protocol (predicate B), and inbound
  corrections (predicate C) kept distinct throughout.
- **Honest limitation of this merge, stated once:** the per-shard BOUNDARY SELF-AUDIT
  reasoning is not reproduced here — only the format-level SERIES/CHAIN conclusions and
  the consolidated edge list survive in §6. The TEETH table (§5) is condensed to the
  load-bearing rows; roughly 15 additional per-family disposition rows live only in the
  three shards' own §5 sections. A reader needing the full per-boundary reasoning or the
  complete TEETH table should consult the shard files directly (§1).

---
