# EFF-GENTOW5 — CANONICAL EFFECTIVE-SPECIFICATION (MERGED)

**COMPILED-BY: opus (2026-08-14, Asvin-authorized substitution). CODEX CROSS-READ OWED (post-reset) — neither shard, and no fold performed by this merge run, has been through an adversarial pass; that obligation is inherited whole.**

## 1. Merge header

**Source note:** `lean/notes/openmath/GENTOW5_PROOF_2026-08-09.md` (2,313 lines).

**HEAD blob hash:** `5cc4c0f783c524b25ba7f6d6c55f576ae41cfcac` — cited identically by both
source shards' headers, and independently confirmed by fresh `git hash-object` against
the working-tree file at merge time (2026-08-14):

```
$ git hash-object lean/notes/openmath/GENTOW5_PROOF_2026-08-09.md
5cc4c0f783c524b25ba7f6d6c55f576ae41cfcac
```

**No divergence found — this was the merge run's STOP condition and it did not trigger.**
Both shards additionally record the file's last-touching commit as `cb010522`.

**Compilation context:** `spec/EFF_TEMPLATE_v2.md` AT HEAD (rules 1–39).

**Merged from:** `spec/EFF-GENTOW5-s1of2.md` (HOME lines 1–1474; 43 statements, 57 xrefs
verified, 3 open calls), `spec/EFF-GENTOW5-s2of2.md` (HOME lines 1475–2313; 41 statements,
20 xrefs verified, 3 open calls). **84 statements, 77 raw XREF/artifact citations, 6 raw
open calls total before merge-time dedup.** This file supersedes the two shards as the
citable unit for all downstream consumption; any consumer citing `EFF.GENTOW5.*` from this
point on cites the contiguous IDs below, not the shard-local `EFF.GENTOW5.sKof2.*` IDs. The
two shard files are **not deleted** — they remain the run-of-record trace of the sharded
compilation, and in particular remain the place where each unit's own §6 BOUNDARY
SELF-AUDIT entry (which unit-boundary candidate was chosen and why) lives in full; this
merged file's own boundary section (§7) carries forward only the cross-shard edge list
and the format-level conclusions, not the individual boundary arguments each shard
records for its own range.

### Rule-39 fresh self-count check (both shards' own tallies re-verified; no discrepancy found)

Unlike `spec/EFF-LIFTCORNER.md`'s merge (a genuine "fifteen" vs 20 miscount) and
`spec/EFF-GRTW2.md`'s merge (a genuine chain-count self-tally mismatch, "CHAIN ×4" vs a
fresh count of five), this merge's fresh recounts reproduce both shards' own stated
tallies exactly, with no discrepancy to book:

| Tally | Shard 1 states | Fresh recount | Shard 2 states | Fresh recount |
|---|---:|---:|---:|---:|
| Statement units (`### EFF.GENTOW5.sKof2.NN` headers) | 43 | **43** | 41 | **41** |
| XREF/designation rows (§3.1 table) | 57 | **57** | 20 | **20** |
| OPEN-CALLs (`### OPEN-CALL` headers) | 3 | **3** | 3 | **3** |

All six figures reproduce exactly (`grep -c '^### EFF.GENTOW5.s1of2\.'`,
`grep -c '^### EFF.GENTOW5.s2of2\.'`, direct table-row counts, and
`grep -c '^### OPEN-CALL'` against each shard file). **No rule-39 discrepancy is booked
in this merge.** (The inline `XREF:` prose-line count is lower than the table-row count in
both shards — 67 lines / 57 rows in shard 1, 19 lines / 20 rows in shard 2 — because
several inline `XREF:` lines bundle more than one designation on one line, e.g. shard 1's
six-designation `[Q7]`/`[Q6]`/`[Q4]`/`[Q1]`/`[Q2]`/`[Q8]` line; the §3.1 tables are the
shards' own authoritative, already-expanded ledgers, and it is those the closing tallies
count — verified by direct row count, not by the inline-line proxy.)

### SHARD-MAP (old shard-local ID → new contiguous ID)

Shard 1's offset is **0** (its own numbering, 01–43, is already contiguous from 1).
Shard 2 carries a **+43** offset (01–41 → 44–84).

**This note's cross-shard citation shape is the simplest of the precedents to date: zero
bare `` `.NN` `` cross-shard citations exist in either direction.** Verified exhaustively
against both shards' full text (not assumed from the charge's premise):

- **Shard 1 never cites a shard-2-homed unit by ID, bare or full-form.** Every "shard 2"
  mention in shard 1's text is descriptive prose naming a SECTION (S7/S8/S9/S10, S11, S12)
  or a disposition ("homed in shard 2"), never an `EFF.GENTOW5.*` designation. Confirmed
  by an exhaustive sweep of every `shard 1`/`shard 2`/`s1of2`/`s2of2` occurrence in shard
  1's source text (11 total; none attaches a unit ID).
- **Shard 2 never cites a shard-1-homed unit by ID, bare or full-form, either.** Every
  "shard 1" mention in shard 2's text names the mathematical OBJECT it targets — "shard
  1's clause (a)", "shard 1's K_i-digit-lift unit", "shard 1's LEMMA GENTOW5-D", "shard
  1's THEOREM GENTOW5-A and clause (d)" — never a bare `` `.NN` `` or full-form ID.
  Confirmed by an exhaustive sweep of every `shard 1` occurrence in shard 2's source text
  (21 total, all descriptive-by-name).
- One meta-mention survives in shard 2's own §7 SHARD NOTES ("to be reconciled with shard
  1's `.01`–`.43` at the merge run") — this is shard 2 describing shard 1's numbering
  RANGE at compilation time, not citing an individual unit, and it lives in the
  shard-bookkeeping section this merge does not reproduce verbatim (format-level
  conclusions only survive — see §7 below).

**Per rule 38, the definitive-mapping audit table for this merge has zero rows** — a
different shape from `spec/EFF-LIFTCORNER.md`'s merge (18 lines, 22 protected tokens) and
`spec/EFF-GRTW2.md`'s merge (52 line-range citations resolved by a lookup table), but
arrived at the same way: by first enumerating every labelled cross-shard occurrence in
both shards' full text (32 total: 11 in shard 1, 21 in shard 2 — the counts above) and
finding that **none of them attaches a bare `` `.NN` `` or full-form ID** needing
exemption from the offset. Since there is nothing to protect, the rewrite is a uniform
mechanical shift: **every bare `` `.NN` `` and every `EFF.GENTOW5.s2of2.NN` in shard 2's
text gains `+43`; every bare `` `.NN` `` and `EFF.GENTOW5.s1of2.NN` in shard 1's text is
unchanged.** The rewrite was still performed unit by unit against this compiler's own
reading of both shards' full text (never a blind global substitution) — shard 2's
descriptive "shard 1's X"-by-name citations are exactly what let this compiler VERIFY,
independently of the mechanical shift, which specific merged unit each one resolves to
(§7.2's cross-shard edge table is built from that verification, not assumed from the
shift arithmetic).

**Per rule 37 (foreign-note citation guard):** an exhaustive sweep for the pattern
`"<Capitalized-note-name>['s] shard N"` — covering GENIND, HE3, GENHN, GENTOW5_WI,
GENTOW1, GENTOW2, HE7 — found **zero** occurrences in either shard. GENTOW5 cross-cites
`GENTOW5_WI_2026-08-10.md`, `GENTOW2_PROOF`, `GENTOW1_PROOF`, `GENHN_PROOF`, `HE7_PROOF`
and `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` extensively (§4 below), but always by
the foreign note's own DESIGNATION (`[GENTOW5-W(i)]`, `LEMMA GENHN-2′`, ledger row
numbers), never by a foreign note's own shard-numbering scheme. **Nothing needed
protecting from the offset; the guard applies to zero tokens in this merge.**

Audited afterward by exhaustive regex sweep, matching rule 38's closing requirement:
**zero leftover `sKof2` substrings within the merged statement inventory (§3)** — the
handful that survive in this header are deliberate quotations of the original shard-local
notation and filenames — and **zero out-of-range renumbered IDs** (every resolved
`` `.NN` `` token in the merged inventory lies in 1–84, confirmed by an explicit scan of
the transformed text before assembly).

### Header unification and blob-hash check

Both shards' front matter carries the **identical** compiled-by/cross-read-owed stamp
(reproduced verbatim above, modulo the PROJECT_STATE line number the shards additionally
carry) and the identical HEAD blob hash; both independently record the file's
last-touching commit (`cb010522`) — confirmed by this merge against the working tree
rather than trusting the shards' mutual citation alone.

### Genre note (carried from both shards, verbatim discipline)

**GENRE: TAG-SPARSE PROSE PROOF throughout — `grep -c '\tag{'` = 0 over the whole
2,313-line note (re-verified fresh at merge time).** Shard 1's HOME range (front matter
through §S7) is a conventional lemma/theorem/proof sequence with in-place dated brackets
(`[GT5-r1]`–`[GT5-r3]`, each governing the text it names, later governing earlier per the
same nested-bracket reading rule the GRTW2/HE3 precedents use). Shard 2's HOME range
shifts genre twice more: first to a REPAIR-ROUND + ACCEPTANCE-RECORD discipline (§S8–§S10,
the dated acceptance record), then to a DATED-APPEND-BY-SUPERSESSION discipline (§S11–S12
and the post-D3i corrigendum), each stating its own freeze rule explicitly in the note's
own words (quoted below). The note's own S11-head text states the supersession
convention directly: "these are dated corrections BY SUPERSESSION — the superseded
sentences are quoted, stay byte-intact above, and read as corrected here."

### Governing effective-text record (unified from both shards)

**FREEZE PREDICATES (rule 21 — TWO, both stated in the note's own words):**

**(F1) TEXT-FREEZE at acceptance.** Lines 1671–1741 (`.56`):

> "**GENTOW5 IS ACCEPTED 2/2** — passPE4 CLEAN (0 CRITICAL + 0 GAP + 2 MINOR,
> GENTOW5_passPE4_report.md @ b22b37b; counter 0/2 -> 1/2) followed by passPE5 CLEAN (0
> CRITICAL + 0 GAP + 3 MINOR, GENTOW5_passPE5_report.md @ 18900e03; counter 1/2 -> 2/2):
> two consecutive clean hostile passes, the standing acceptance bar.
> **THE NOTE IS FROZEN AT THIS RECORD: dated appends and dated brackets only; statement
> displays and sealed artifacts stay byte-untouched.**"

Unlike GRTW2's acceptance, GENTOW5's carries **no explicit "WHAT IS ACCEPTED" scope
enumeration** — its scope is instead fixed by the dated-append machinery that follows
(§S11–S12), which is why this merge does not invent a third, GRTW2-style
acceptance-scope-enumeration freeze predicate here: the note's own text supplies only
two. **Acceptance is annotated, not downgraded, twice**: "Grade: ACCEPTED 2/2 stands,
ANNOTATED by RUN A" (S11.6, `.73`) and "acceptance 2/2 remains ANNOTATED" (S12 head,
`.60`).

**(F2) INSTRUMENT-FREEZE — the three sealed artifacts, byte-frozen at composition and
re-verified at every round.** From `.37` (S5): "INSTRUMENT: `verification/openmath/
gentow5_checks.py`, sealed at commit 4b279a7 … BEFORE the first run." The freeze is
re-verified by md5 at every subsequent round (`.44` PE2's, `.49` PE3's, `.59` the
acceptance round's, and `.73` S11.6's own byte-freeze ledgers), plus one rider helper
(`gentow5_rider_f32dev.py`) committed mid-arc and itself frozen thereafter (`.59`, `.73`).
**The prefix-md5 discipline is itself load-bearing evidence** — `.73` records two commits
each verified by prefix-md5 against the prior state, not merely "no diff since last
time."

### Scope of record — mandatory THREE-predicate split (unified from both shards)

**A. ABSORPTION / mathematical supply SET.** TARGET 1: THEOREM GENTOW5-A + LEMMAS
GENTOW5-A0/A1 — LEMMA GENTOW-2 layer 1 at general mu2 (GENTOW-BOX-1 RETIRED as a
mathematical box, `.10`, `.13`). TARGET 2: DEF GENTOW5-1 + LEMMAS GENTOW5-C/D + THEOREM
GENTOW5-B — the level-r ladder grammar and the general-depth composition theorem, clauses
(a)–(e), with the depth-4 witness exact on two independent routes (`.34`–`.37`). **Shard 2
does not add supply; it narrows and range-completes it**: S11.2/S12.1 fence clauses
(a)/(b)/(c)/(e) at every index n ≥ 3 behind the open lemma `[GENTOW5-W(i)]` (see the
special OPEN-CALL entry, §8); S12.2 discharges the lift-rung range obligation that S11.4
had mis-stated (`.71`, superseded by `.78`); S11.1 corrects LEMMA GENTOW5-D's converse
direction (`.61`–`.67`, landing on shard-1-homed `.25`).

**B. APPEND / consumption PROTOCOL scope — what GENTOW5 lands on other notes.**
**Nothing.** S6 (`.42`): "**Consumption path (not executed here):** GENTOW1_PROOF's S3
grade note and S6 GENTOW-BOX-1, GENHN_PROOF's GENHN-BOX-2 and [GENHN-TOW-1] item (6)
depth->=4 sentence, and GENTOW2_PROOF S7's depth->=4 bullet are candidates for the
orchestrator's dated consumption updates after this note's own hostile arc; the four
source notes are byte-untouched by this unit." **Zero dated consumption appends are
claimed landed on any supplier or consumer by this note, and none is invented here** —
verified across both shards' HOME ranges.

**C. INBOUND CORRECTIONS RECEIVED — nine streams, spanning both shards' ranges. The
"Targets" column is a fresh grep-hit list for each round's own tag/phrase against the
merged inventory (`awk`-scripted per round, reported below) — a floor on what each round
touched, not hand-certified as exhaustive; the authoritative record for any single unit
remains that unit's own CONDITIONALITY/RESOLUTION TRACE field in §3:**

| # | Source | Landing form | Count | Targets (grep-hit, merged IDs) |
|---|---|---|---|---|
| 1 | PE1 hostile pass @ 0160b94 | in-place `[GT5-r1]`, §S7 record `.43` | 1 CRITICAL + 2 GAP + 3 MINOR | `.18`, `.22`, `.24`, `.25`, `.26`, `.27`, `.33`, `.34`, `.35`, `.37`, `.39`, `.40`, `.43` |
| 2 | PE2 hostile pass @ 40f313a | in-place `[GT5-r2]`, §S8 records `.44`–`.48` | 0C + 2 GAP + 2 MINOR | `.04`, `.17`, `.18`, `.25`, `.27`, `.28`, `.32`, `.38`, `.40`, `.43` |
| 3 | PE3 hostile pass @ 39c36aa | in-place `[GT5-r3]`, §S9 records `.49`–`.52` | 0C + 1 GAP + 2 MINOR | `.27`, `.29`, `.31`, `.32`, `.38` |
| 4 | PE4 hostile pass @ b22b37b (CLEAN) | dated `[rider]`, §S10 `.53`–`.55` | 0C + 0G + 2 MINOR | `.14`, `.26`, `.29`, `.31` |
| 5 | PE5 hostile pass @ 18900e03 (CLEAN) | dated `[acceptance fold]`, `.56`–`.59` | 0C + 0G + 3 MINOR | `.12`, `.22`, `.26`, `.27`, `.30`, `.34` |
| 6 | Codex TOWERRAT2 RUN A (adversarial, decorrelated) | dated §S11, `.60`–`.73` | 1 CRITICAL + 2 GAP + 2 MINOR (5/5 REAL) | `.25`, `.28` (narrow A-F-tag hits — the fuller propagation is row 7's) |
| 7 | sol certification D1a → E12 (2026-08-12), the 𝒲≤n propagation | dated §S12.1–S12.2, `.74`–`.83` | 2 residuals (INSUFFICIENT + NEW-ISSUE) | `.04`, `.06`, `.08`, `.10`, `.14`, `.17`, `.18`, `.22`, `.26`, `.27`, `.28`, `.29`, `.30`, `.31`, `.32`, `.34`, `.38` |
| 8 | sol certification D3i (post-D3i corrigendum) | dated append `.84` | 1 NEW-ISSUE + 1 DISCHARGED | corrects `.75` item 2 and fixes how `.76`'s chain reads (both shard-2-internal; R-i4/lift-rung discharge confirmed unaffected) |
| 9 | External SOL ledger rows 10/18 (reading notes, not edits) | none — recorded only | — | see §8 OPEN-CALLs |

### Resolution rules applied (merged; each shard's own numbered rule-list is a
restriction of this one to its HOME range — nothing below is dropped, only consolidated)

1. Shard 1's lines 1–1474 supply the base statements: front matter/ARC records, CHARGE,
   SOURCES CONSUMED, STATUS TABLE, §S0–§S7. Dated brackets `[GT5-r1]`–`[GT5-r3]` are
   already-landed in-place text there.
2. Shard 2's lines 1475–2313 supply three repair records (§S8/S9/S10), the dated
   acceptance record, and two dated appends (§S11, §S12) with the post-D3i corrigendum —
   all corrections BY SUPERSESSION, quoting and preserving their targets byte-intact.
3. **The acceptance record governs STATUS for the whole note**: every "grade 0/2",
   "counter stays 0/2", "PEn next" sentence anywhere in shard 1's range is historical,
   superseded by **ACCEPTED 2/2** (`.56`), itself later ANNOTATED (not downgraded) by
   `.73` and `.60`.
4. **In-range supersession chains, applied in chronological order**: S12.2 (`.78`)
   supersedes S11.4 (`.71`) on the lift-rung threshold; S12.1 (`.74`) supersedes S11.2's
   (`.69`) "unaffected scope" list; the post-D3i corrigendum (`.84`) supersedes S12.1
   item 2 (`.75`)'s twist index.
5. **HOME is determined by an edit's destination, not physical drafting location** — the
   rule the GRTW2/HE7/HE3/T1 merges also used. Every PE2-F-*/PE3-F-*/PE4-F-*/A-F* item
   targets a base sentence homed in shard 1's range 1–1474, but is itself HOMED in shard
   2 (its drafting/append location) and emitted there as a changes-record; the
   corresponding shard-1 unit's own CONDITIONALITY/RESOLUTION TRACE carries the corrected
   reading. No base statement is re-emitted twice.
6. Every cited commit hash was checked for existence; every cited artifact was verified
   to exist; the runner's own sha256 prefix is recorded as it is in the note (see the
   XREF ledger, §4, for any truncation findings).
7. Out-of-range material (from either shard's perspective) is used only to resolve
   in-range HOME units; no unit is invented merely because it resolves another unit's
   text (rule 8/9 of each shard's own list).

### Quotation and table discipline

Unchanged from both shards: CANONICAL STATEMENTs are verbatim source quotations except
where explicitly marked `[ASSEMBLED]` under the same fidelity rules; strike-through and
nested brackets are reproduced exactly; truncations marked `…`; every statement unit
carries `FORM:`. The one source table (shard 1's STATUS TABLE, `.04`) is transcribed as a
table per rule 5; shard 2's §S12 LaTeX displays are reproduced as LaTeX (the note itself
switches notation there for the certification-derived corrections), and §§S8–S11's ASCII
displays keep their line structure, matching each shard's own discipline. Compiler-authored
ledgers (XREF tables, consumption ledgers, TEETH inverse tables, the cross-shard edge
table of §7) are marked `[TABLE — compiler ledger]` and are not source statement units.

---

## 2. NON-IMPORTS (consolidated from both shards; dedup marked)

`[TABLE — compiler ledger, consolidated from shard 1 §4 (15 rows) and shard 2 §4 (12 rows)
= 27 raw rows, 0 dedup pairs found → 27 distinct rows below]`

**Dedup count for this section: 0.** As with GRTW2's and HE3's merges, no fence in either
GENTOW5 shard restates a near-identical negative claim already stated by the other shard
— shard 1's fences are about the base proof's own scope boundaries (the graded frame, the
weight functional, index-0, depth ≥ 3 measurement, the machine record's coverage gaps);
shard 2's are about the acceptance/append machinery's own non-closures (the withdrawn
grid closure, the open `[GENTOW5-W(i)]` form, the lift-rung correction, the terminal
certification state). Every row below is specific to its own shard and asserted once.

| Fence | Explicit material NOT imported, NOT proved, or NOT claimed | Source |
|---|---|---|
| Sources | "SOURCES CONSUMED (never edited)" — consumption is one-directional; "the four source notes are byte-untouched by this unit." | s1 `.03` |
| Graded frame | "No W-9-analogue weld face is consumed; the graded frame is gr(L2) itself." | s1 `.13`, `.38` |
| Normalizer systems | "no invariance under CHANGING systems mid-argument is consumed (that stronger claim is false — HE7-T-BADTWIST)." | s1 `.23` |
| Weight functional | "wt_i consumes NO data beyond the depth-i datum: u_{i+1} does not appear." | s1 `.24` |
| GENTOW5-D strictness | "nondecreasing is all any named consumer of this lemma uses … the strict FLOW-UP pricing there comes from lam > E separately, never from this lemma's strict clause." | s1 `.25` |
| B-2 | "never B-2 on-the-nose (u = 1), which is FALSE at letter-live grades" — the `y -> eps*y` fallback is "deleted as false at its source". | s1 `.27`, `.43` |
| Alternative key | The re-parameterized prescription "builds a DIFFERENT key from the pinned recipe … it is not repo-constructible; the statement stays at the pinned key and the twisted residual." | s1 `.27` |
| Lift display | "GENTOW1 S3's fixed-base READING of its lift display fails the same way at seam-live heights — a display-level defect there, flagged for that note's own arc, not consumed here." | s1 `.17` |
| Clause (c) pairing | The composed `(i+2)`-read pairing is refuted by the residual-degree count and at committed rows; "no sentence in the note consumes the retired (i+2)-read pairing." | s1 `.29` |
| Index 0 | (a)@0 and (b)@0 "NOT claimed"; the entry locus `T_1` "stays unclaimed", "Left unclaimed rather than cited." | s1 `.26`, `.29` |
| Depth ≥ 3 measurement | "no count law at depth >= 3 is claimed measured." | s1 `.33` |
| Open list | "tower COUNT laws at depth >= 3 … partial inner sides … the genre-general faithfulness geography … sigma laws behind [GENHN-HE(mu >= 3)] — none of these is touched by GENTOW5-B, which is a carrier/read/budget/refine theorem, not a density display." | s1 `.41` |
| External consumers | "External consumers: none executed (S6's consumption path is candidates only); any future consumption of (a)/(b) must ride the w-annotation." | s1 `.32` |
| Instrument strength | The sealed `C3a`/`C3b` lines "machine-assert only nfactors … the e = 4 values (and C3b's deg) are PRINTED … not chk-asserted". | s1 `.37` |
| PARI-free route | The withdrawn "(P-B4 is the exact witness either way)" — the per-root ladder needs the single-prime read. | s1 `.35` |
| Grid closure | The two-directional grid closure is WITHDRAWN; only the forward direction and the single-step top-rung converse survive; "no two-directional grid agreement is consumed anywhere in the repaired chain." | s2 `.62`, `.67` |
| Converse direction | "The converse rewriting … is weight-nondecreasing by the same displays." — "FALSE as written." | s2 `.61` |
| Annex ride | "the ride carries (SLOT_i)/(LIFT_i) counting statements, not GENTOW2-B‴s normalizer-cocycle monomial computation." | s2 `.68` |
| Single-`w` form | `[GENTOW5-W(i)]` at i ≥ 3 is "NOT PROVED … this note does not reproduce" it — "the honest-sorry analogue". | s2 `.68` |
| w-blindness | "A fixed per-grade unit family is not enough: 'w-blind' means invariance AFTER the family has been proved to have the single-w_i geometric form. It does not construct that form." | s2 `.74` |
| i = 1 tie | "the tie u1 = w_1 = R_{2,kbar_1}(nhat_1(u_2)) is OPEN"; the fold's "exponent-level tie … is NOT claimed". | s2 `.70` |
| Automatic floor | At n ≥ 3 "only its claimed automatic derivation from the recipe is conditional" — the inequality may be a datum, but is not derived. | s2 `.75` |
| Lift rung | "No recipe consumer needs \(m_t>\operatorname{bound}_{i+1}\)"; S11.4's `bound_{i+1}` assertion is WITHDRAWN. | s2 `.80` |
| Machine discrimination | "The S4 depth-4 witness is w-trivial (K_i = F_2), so the machine record does not discriminate this fence." | s2 `.69` |
| Sealed artifacts | "no runner edited, no sealed re-run" (S11.6); "Sealed artifacts untouched this round". | s2 `.73` |
| Statement displays | "Statement displays above stay byte-intact; corrections are by dated supersession … and dated fences." | s2 `.73` |
| Certification | "Awaiting sol re-confirmation in the next queue." — the note does not claim the corrigendum re-confirmed. | s2 `.84` |

---

## 3. Statement inventory (84 units, contiguous, in source order)


### EFF.GENTOW5.01  [changes-record]

**CANONICAL STATEMENT:** [ASSEMBLED — front-matter status line plus the four in-range ARC verdict sentences, quoted verbatim; the repair-item bodies of each bracket are inventoried at their own repair-record units]

> “**2026-08-09 — SKELETON (per-section commits follow). Unit: GENTOW-5, BOX-CLOSURE campaign wave B1. Grade target 0/2 (attempt; hostile arc owed).**”

> “**[ARC — passPE1 2026-08-09: NOT CLEAN, 1 CRITICAL + 2 GAP + 3 MINOR (GENTOW5_passPE1_report.md @ 0160b94); counter stays 0/2.”

> “**[ARC — passPE2 2026-08-10: NOT CLEAN, 0 CRITICAL + 2 GAP + 2 MINOR (GENTOW5_passPE2_report.md @ 40f313a); counter stays 0/2.”

> “**[ARC — passPE3 2026-08-10: NOT CLEAN, 0 CRITICAL + 1 GAP + 2 MINOR (GENTOW5_passPE3_report.md @ 39c36aa); counter stays 0/2.”

> “**[ARC — passPE4 2026-08-10: CLEAN, 0 CRITICAL + 0 GAP + 2 MINOR (GENTOW5_passPE4_report.md @ b22b37b); counter 0/2 -> 1/2 — the arc's first clean pass.”

**CONDITIONALITY:** Historical. Every counter value above is superseded by the out-of-range acceptance record (**ACCEPTED 2/2**, resolution rule 3). The bracket bodies duplicate, in summary form, the repair records S7 (in range, `.43`) and S8/S9/S10 (shard 2).

**DERIVATION:** Not a mathematical unit; the record is the arc's own chronology, each verdict pinned to its committed report file and commit hash.

**RESOLUTION TRACE:** Base front matter lines 4–86; status superseded at lines 1671–1741.

**TEETH:** The arc itself is the note's tooth of record; per-pass batteries are inventoried at `.37` and §5.

---

### EFF.GENTOW5.02  [scope-record]

**CANONICAL STATEMENT:**

> “CHARGE: (1) PROVE or box-with-obstruction GENTOW-BOX-1 — LEMMA GENTOW-2 layer 1 at general mu2 (the composed graded frame; GENTOW1_PROOF S3/S6). (2) THE LEVEL-r LADDER GRAMMAR: the normalizer recursion n-hat_i(m), the composed key recipe Phi_{i+1}, the digit ladder at general i, the general-depth composition theorem (FGMN Cor 6.4 is level-general; HE7 ANNEX R's HE7-2'/R1-a/R1-b is the template one level down); depth-4 witness at n = 32, q = 2 if reachable.”

**CONDITIONALITY:** None — this is the unit's charge, not a claim.

**DERIVATION:** Charge text; no derivation.

**RESOLUTION TRACE:** Base lines 88–95; untouched by later rounds.

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:LEMMA GENTOW-2` — grep-verified count **7**.

XREF: `lean/notes/openmath/HE7_PROOF_2026-08-08.md:ANNEX-LEMMA R1-a` — grep-verified count **6**.

XREF: `lean/notes/openmath/HE7_PROOF_2026-08-08.md:ANNEX-THEOREM R1-b` — grep-verified count **4**.

**TEETH:** The depth-4 witness clause is discharged at `.34`–`.36`; the “if reachable” proviso was met (GREEN both routes).

---

### EFF.GENTOW5.03  [fence]

**CANONICAL STATEMENT:**

> “SOURCES CONSUMED (never edited): GENTOW1_PROOF_2026-08-09.md (S0 notation, LEMMA GENTOW-1 + Step 0, LEMMA GENTOW-2 + grade note, LEMMA GENTOW-5, S6 boxes); GENTOW2_PROOF_2026-08-09.md (FGMN quotes [Q1]-[Q10] at verified numbering, THEOREM GENTOW2-A, LEMMA GENTOW2-B + honesty box, S7 depth->=4 scope sentence); GENHN_PROOF_2026-08-08.md (S6.1 LEMMA GENHN-4 + GENHN-BOX-2, S8 [r2] annex T(b)' + GENHN-2', [GENHN-TOW-1] r3 item (6) text); HE7_PROOF_2026-08-08.md ANNEX R (ANNEX-DEF HE7-2', ANNEX-LEMMA R1-a, ANNEX-THEOREMS R1-b/R1-c, R1.2 audit, R1.3 run record).”

**CONDITIONALITY:** “never edited” is the note's own import fence: consumption is one-directional, and the four source notes stay byte-untouched (cross-checked against S6's consumption-path sentence, header scope split).

**DERIVATION:** Declaration, not derivation.

**RESOLUTION TRACE:** Base lines 97–105; reaffirmed at S6 line 1394 (“the four source notes are byte-untouched by this unit”).

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:LEMMA GENTOW-1` — grep-verified count **7**.

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:LEMMA GENTOW-5` — grep-verified count **6**.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:THEOREM GENTOW2-A` — grep-verified count **8**.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B` — grep-verified count **30**.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:LEMMA GENHN-4` — grep-verified count **3**.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN-BOX-2` — grep-verified count **5**.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:[GENHN-TOW-1]` — grep-verified count **19**.

XREF: `lean/notes/openmath/HE7_PROOF_2026-08-08.md:ANNEX-THEOREM R1-c` — grep-verified count **3**.

**READING NOTE (designation orthography, not an edit).** GENTOW5's body is ASCII; three consumed designations carry a Unicode prime in their home notes. Verified forms and counts: `GENHN-2′` **3** (the ASCII `GENHN-2'` also occurs, count **5**); `LEMMA GENHN-T(b)` **11** (`T(b)′` **31**; the ASCII `T(b)'` has count **0** in GENHN_PROOF); `ANNEX-DEF HE7-2′` **6** (the ASCII `ANNEX-DEF HE7-2'` has count **0** in HE7_PROOF). No invented designation is emitted; the Unicode form is the verified one.

**TEETH:** NONE (import declaration).

---

### EFF.GENTOW5.04  [TABLE] [scope-record]

**CANONICAL STATEMENT:** [TABLE — the note's STATUS TABLE, transcribed]

> “STATUS TABLE (updated per section as composed):”

| target | item | status |
|---|---|---|
| (1) | THEOREM GENTOW5-A (composed graded frame, general mu2) | PROVED (S1) |
| (1) | GENTOW-BOX-1 disposition | RETIRED into GENTOW5-A's pin stack (S1.5) |
| (2) | DEF GENTOW5-1 (level-r ladder grammar) | STATED (S2.1) |
| (2) | LEMMA GENTOW5-C ((SLOT_i) for the tower ladder) | PROVED at annex-template grade (S2.3) |
| (2) | LEMMA GENTOW5-D (Step-0 carry monotonicity is level-agnostic) | PROVED (S2.4) |
| (2) | THEOREM GENTOW5-B (general-depth composition) | PROVED with named pins (S3) [GT5-r2: (a) at the twisted residual psi^{(w_i)}; w_i = 1 open] |
| (2) | depth-4 witness n = 32 q = 2 | GREEN: ladder (16,40,84,170,341) exact, resultant + PARI routes (S4.3) |
| battery | gentow5_checks.py | GREEN 92 checks / 0 violations, 5/5 teeth-and-flags as predicted (S5) |

**CONDITIONALITY:** The “PROVED with named pins” row for GENTOW5-B is further conditioned by the out-of-range appends: at i ≥ 3 clauses (a), (b), (c), (e) are conditional on `[GENTOW5-W(i)]` (S12.1, resolution rule 5), at i = 1 clause (a) reads at S11.3's re-scoped form, and clause (b)'s residual display reads at S11.5's re-index with the post-D3i twist index.

**DERIVATION:** Status ledger; each row's derivation is the section it names.

**RESOLUTION TRACE:** Base lines 107–118. The `[GT5-r2]` annotation is landed inside the table row. No later round rewrites the table; the conditional narrowing lives in S11/S12.

**TEETH:** Battery row of the table itself is `.37` (92 checks / 0 violations).

---

### EFF.GENTOW5.05  [hypothesis]

**CANONICAL STATEMENT:** [ASSEMBLED — §S0 SETTING, quoted in full]

> “Depth-2 tower per T(b)' (accepted): outer genre (Q; e1, f1, mu1; h), key Phi' of degree D' = e1f1; inner side data (u2, e2, psi2, mu2) with gcd(u2, e2) = 1, f2 = deg psi2, e2f2mu2 = mu1; composed key Phi2, deg D2 = D'e2f2; composed ladder dv2 = e1e2*v; K = F_{Q^{f1}}, K2 = F_{Q^{f1f2}}; E2 := e2f2u2; node floor u2 > e2D'h. Ladder normalizers n2hat(m) := pi^{a} x^{i} Phi'^{b} (i < e1, b < e2, e1e2*a + i*e2h + b*u2 = m; unique (i,b) per residue class mod e1e2 — GENTOW-1 S3). GENHN-2' (accepted, T(b)'(ii)): on the tower-node locus, dv2(A(x0)) = the slot minimum EXACTLY, one K2-digit per dv2-height per coordinate. Event setting of LEMMA GENTOW-2: f in the tower locus whose composed polygon (j, p_j), p_j = dv2(C_j(x0)), is ONE side of integer dv2-slope lam > E2 with residual (T - s)^{mu2} over K2, s in K2^x; refine Phi2+ := Phi2 - lift(s; lam). GENTOW-2's layers 2 (corrections land strictly deeper) and 3 (triangular bijection) are PROVED at general mu2 in GENTOW1_PROOF S3; layer 1 (the graded kills) is proved there at mu2 = 2 pointwise only — GENTOW-BOX-1 is exactly that gap. L2 := the completion of the leaf at a fixed root x0 (v extended, normalized v(Q-uniformizer of the BASE) = 1 as everywhere in the corpus); k(L2) its residue field; iota: K2 -> k(L2) the transport of T(b)'/S4 convention.”

**CONDITIONALITY:** The whole setting is hypothesis, imported at the accepted grade: `T(b)′` and `GENHN-2′` are accepted corpus; the event hypothesis carries `lam > E2` (the composed node floor) and `s in K2^x`.

**DERIVATION:** Restatement, explicitly labelled “one-pass restate; GENTOW-1 S0 + HE7-2' names”. The only derived content is the identification of the box: GENTOW-2's layers 2 and 3 are already general-mu2, layer 1 is pointwise at mu2 = 2, so the gap is exactly layer 1.

**RESOLUTION TRACE:** Base §S0, lines 120–142; untouched by any later round.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN-2′` — grep-verified count **3**; supplies the exact-slot-minimum/one-digit-per-height clause.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:LEMMA GENHN-T(b)` — grep-verified count **11**; the accepted depth-2 tower datum.

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:LEMMA GENTOW-2` — grep-verified count **7**; the event setting and the boxed layer 1.

**TEETH:** §S5's P-A1/A2/A3 rows exercise this setting at mu2 = 3 across three frames.

---

### EFF.GENTOW5.06  [lemma]

**CANONICAL STATEMENT:** LEMMA GENTOW5-A0 (gr of a valued field is a graded division ring)

> “For the dv2-rescaled valuation on L2 (values in (1/e1e2)Z on the relevant subfield, rationals in general), set for each rational m
>
>     gr(L2)_m := {a in L2 : dv2(a) >= m} / {a : dv2(a) > m},
>     gr(L2)   := (+)_m gr(L2)_m,   [a] := the class of a in degree dv2(a).
>
> Then gr(L2) is a commutative graded ring, multiplication induced by L2's; every nonzero homogeneous element is invertible; in particular gr(L2) is a domain on homogeneous elements: [a][b] = [ab] != 0 for a, b in L2^x.”

**CONDITIONALITY:** Unconditional — “elementary, self-contained” (S1.5's own characterization). Requires only that L2 is a field with a valuation.

**DERIVATION:** Quoted proof:

> “*Proof.* Well-definedness and distributivity are the ultrametric axioms. Invertibility: for a in L2^x, dv2(a^{-1}) = -dv2(a) and [a][a^{-1}] = [1] != 0 (1 is not in the >0 part). [a][b] = [ab] is dv2(ab) = dv2(a) + dv2(b), a valuation identity on a FIELD (no zero divisors to break it). Degree-0 part: gr(L2)_0 = k(L2). ∎”

With the framing consequence the note attaches (lines 179–183):

> “The point of A0: **pointwise, at a root, there is no carry problem.** Carries are a phenomenon of the slot GRID (rewriting a polynomial between monomial bases); evaluation at x0 is blind to them. The graded frame the box asked for is gr(L2) + the two bookkeeping lemmas below, which translate between grid data and gr(L2) classes.”

**RESOLUTION TRACE:** Base §S1.1, lines 159–183; untouched by every later round (S12.1's unaffected-scope sentence explicitly re-affirms: “LEMMAS GENTOW5-A0/A1 … remain unaffected”).

**TEETH:** NONE dedicated; it is the frame every S5 A-row runs inside.

---

### EFF.GENTOW5.07  [definition]

**CANONICAL STATEMENT:** DEFINITION (multiplicative side residual), with its normalizer class

> “Fix the event slope lam and set N := [n2hat(lam)(x0)] in gr(L2)_{lam} — invertible by A0 (n2hat(lam)(x0) != 0 and its dv2 is lam exactly, GENHN-2' at the single-monomial slot).”

> “**DEFINITION (multiplicative side residual).** For the development f = Sum_{j <= mu2} C_j Phi2^j (C_{mu2} = 1, deg C_j < D2) with pins on or above the side of slope lam through (mu2, 0), the **multiplicative residual** of the side at x0 is
>
>     R_N(T) := Sum_{j} c_j T^j in k(L2)[T],
>     c_j := [C_j(x0)] * N^{-(mu2-j)}  if dv2(C_j(x0)) = (mu2-j)lam,
>     c_j := 0                          if dv2(C_j(x0)) > (mu2-j)lam,
>
> (c_{mu2} = 1 since C_{mu2} = 1 at height 0).”

**CONDITIONALITY:** Requires the pins on or above the side, and `GENHN-2′` for the exactness of the normalizer's height.

**DERIVATION:** The convention's justification, quoted:

> “This is the convention under which residual-of-product = product-of-residuals holds by A0 alone, and it is the corpus's operative convention: GENTOW-1 Step 1 consumes exactly this multiplicativity ("graded layer of a product = product of graded layers"), the level-1 assembly carries the z^{fl}-powers relating n(kappa)^t to n(t*kappa) (GENHN-4 layer 1's display), and FGMN's R-operators — the dictionary target of GENTOW2_PROOF S2 — are multiplicative by Cor 4.7(3) [Q8 @ GENTOW2].”

**RESOLUTION TRACE:** Base §S1.2, lines 185–208; untouched by later rounds.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:[Q8]` — grep-verified count **8**; the pinned FGMN Corollary 4.7. **Clause check:** the `[Q8]` quote block (GENTOW2_PROOF line 147) prints clause “(3) Ri (gh) = Ri (g)Ri (h) for all g, h ∈ K[x]”, so GENTOW5's `Cor 4.7(3)` citation for un-graded multiplicativity is the correct clause (GENTOW2's own consumption uses clauses (1) and (2)).

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:LEMMA GENHN-4` — grep-verified count **3**; the level-1 assembly display.

**TEETH:** §S5's T-A4W (“THE CONVENTION TOOTH FIRED: the naive-digit twin keeps its pin at 22 exactly”).

---

### EFF.GENTOW5.08  [lemma]

**CANONICAL STATEMENT:** LEMMA GENTOW5-A1 (dictionary to the per-height coherent digits)

> “Let gamma_j := the coherent per-height residue of C_j(x0) (the GENHN-2'/S4 digit read against n2hat((mu2-j)lam)). Then
>
>     c_j = iota(gamma_j) * theta_{mu2-j}^{-1},
>     theta_t := [n2hat(lam)(x0)]^t * [n2hat(t*lam)(x0)]^{-1}
>              = iota(vartheta_t),  vartheta_t in K2^x FIXED
>     (theta_0 = theta_1 = 1; equivalently gamma_j = c_j*vartheta_{mu2-j}),
>
> with vartheta_t independent of x0 and of the polynomial read, given by the telescoping vartheta_{t+1} = vartheta_t * res(tau(t*lam, lam)) where tau(a,b) := n2hat(a)n2hat(b)/n2hat(a+b) is the ladder cocycle. tau(a,b) is a Laurent monomial in pi, x, Phi' of dv2-value 0 whose residue at every tower-node point is the transport of a fixed element of K2^x (the two-wrap letter monomial).”

**CONDITIONALITY:** Consumes `GENHN-2′` (coherent digit read) and the S4/T(b)′(iii) wrap letters — “all accepted corpus” per S1.5.

**DERIVATION:** Quoted proof:

> “*Proof.* The first display is A0 arithmetic: [C_j(x0)] = iota(gamma_j)*[n2hat((mu2-j)lam)(x0)] by the definition of the coherent digit, and N^{mu2-j}/[n2hat((mu2-j)lam)(x0)] = theta_{mu2-j}. Telescoping: n2hat(lam)^{t+1}/n2hat((t+1)lam) = [n2hat(lam)^t/n2hat(t*lam)] * [n2hat(t*lam)n2hat(lam)/n2hat((t+1)lam)], the second bracket = tau(t*lam, lam). Cocycle shape: write n2hat(a)n2hat(b) = pi^{a1+a2} x^{i1+i2} Phi'^{b1+b2}; reducing the exponents to ladder range costs one x-wrap x^{e1} = (unit)*pi^{h}*(1 + Phi'-tail/x^{e1}-side data) per overflow and one Phi'-wrap Phi'^{e2} = (unit)*n(u2)*(1 + strictly-above) per overflow — at a tower-node point x0 both wraps have dv2-value 0 with residues the two letters (the eta-wrap z1 := res(x(x0)^{e1}/pi^h * n-correction) and the eta2-wrap z2 := res(Phi'(x0)^{e2}/n(u2)(x0))); both are the transports iota of fixed K2-elements: z1 by GENHN's S4 level-1 cocycle (accepted; the ITER-LAW z-letter), z2 by T(b)'(iii)'s (T22)-transport (Phi'(x0)^{e2}/n(u2)(x0) has residue a fixed unit times psi2-data of eta2(x0), transported through iota — the same S4 computation GENTOW-1 Step 5 runs). Hence res(tau(a,b)(x0)) = iota(z-letter monomial), fixed in K2^x, x0-free through iota. This is ANNEX-LEMMA R1-a(iii) [HE7_PROOF ANNEX R] specialized to the depth-2 tower ladder — reproved here in the tower's own letters rather than cited, since the base conventions differ (HE7's base is varpi-powers; ours is the ladder monomials pi^a x^i). ∎”

**RESOLUTION TRACE:** Base §S1.2, lines 209–247; untouched (S12.1: “LEMMAS GENTOW5-A0/A1 … remain unaffected”).

XREF: `lean/notes/openmath/HE7_PROOF_2026-08-08.md:ANNEX-LEMMA R1-a` — grep-verified count **6**; the precedent whose (iii) clause this lemma re-proves tower-side.

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:Step 5` — grep-verified count **3**; the S4 computation re-run for the second wrap letter.

**TEETH:** §S5's P-A4 / T-A4W (the live-twist mu2 = 2 kill and its naive-digit twin).

---

### EFF.GENTOW5.09  [fence]

**CANONICAL STATEMENT:** Convention consequence (displayed for honesty)

> “At mu2 = 2 only vartheta_2 can differ from 1 (vartheta_0 = vartheta_1 = 1 by definition), and in char 2 every element of K2 is a square, so "R is a perfect square" is convention-independent there and the root s re-parameterizes by vartheta_2^{1/2} — which is why the mu2 = 2 battery rows never saw the convention. At mu2 >= 3 with a live cocycle the per-height-digit coefficient vector of a perfect power is NOT itself a perfect-power vector unless the vartheta_t are carried: **fixing the multiplicative convention is part of the box's content**, not a cosmetic choice. All event statements below are in the multiplicative convention; LEMMA GENTOW5-A1 is the exact translation, with fixed re-parameterization only (J-D0: counts are twist-blind, letters re-coordinatize).”

**CONDITIONALITY:** Scope declaration for every downstream event statement: they are all read in the multiplicative convention.

**DERIVATION:** The char-2/mu2 = 2 degeneration argument quoted above is itself the derivation of why the earlier batteries could not see the convention.

**RESOLUTION TRACE:** Base §S1.2, lines 249–261; untouched.

**TEETH:** §S5's T-A4W is the convention tooth this fence predicts.

---

### EFF.GENTOW5.10  [lemma]

**CANONICAL STATEMENT:** THEOREM GENTOW5-A (the substitution theorem = LEMMA GENTOW-2 layer 1 at general mu2)

> “Setting as in S0 (the GENTOW-2 event), with the residual hypothesis read in the multiplicative convention: R_N(T) = (T - w)^{mu2} in k(L2)[T], where w := [lift(s; lam)(x0)] * N^{-1} = iota(s) ON THE NOSE (theta_1 = 1: at the single height lam the two conventions coincide, so the lift's digit IS the root's coordinate — coherence, not invariance, per HE7 ANNEX R R1.2 item 3).
> Set what := -lift(s; lam), Phi2+ := Phi2 + what, and let C_k+ be the Phi2+-development coefficients of f. Then for every k < mu2:
>
>     dv2(C_k+(x0)) > (mu2 - k) * lam        (ALL mu2 PINS DIE),
>
> and the new multiplicative residual of the side is T^{mu2}.”

**CONDITIONALITY:** The S0 event hypotheses (one side of integer slope `lam > E2`, residual `(T-s)^{mu2}` in the multiplicative convention) plus GENTOW-2 layer 2 at general mu2, which is imported from `GENTOW1_PROOF` S3.

**DERIVATION:** Quoted proof, both steps:

> “*Proof.* Substitute Phi2 = Phi2+ - what into the development and expand IN THE POLYNOMIAL RING (no reduction yet):
>
>     f = Sum_j C_j (Phi2+ - what)^j = Sum_k B_k Phi2+^k,
>     B_k := Sum_{j >= k} binom(j, k) (-what)^{j-k} C_j
>          = Sum_{j >= k} binom(j, k) lift^{j-k} C_j.
>
> Step A (the graded identity, in gr(L2)). Evaluate B_k at x0 — a SUM OF PRODUCTS in the field L2; A0 gives, writing [lift(x0)] = w*N:
>
>     class of Sum_j binom(j,k) lift(x0)^{j-k} C_j(x0) at height
>     (mu2-k)lam  =  N^{mu2-k} * Sum_j binom(j, k) w^{j-k} c_j
>                 =  N^{mu2-k} * (coefficient of T^k in R_N(T + w)),
>
> the second equality the Taylor/substitution identity in k(L2)[T] (if R(T) = Sum c_j T^j then R(T + w) = Sum_k [Sum_j binom(j,k) w^{j-k} c_j] T^k — an identity of polynomials, valid over any commutative ring, both characteristics). By hypothesis R_N(T + w) = (T + w - w)^{mu2} = T^{mu2}: for k < mu2 the coefficient is 0, i.e. the height-(mu2-k)lam class of B_k(x0) VANISHES:
>
>     dv2(B_k(x0)) > (mu2 - k) * lam   for every k < mu2.
>
> Note the identity is a SUBSTITUTION identity — the binomials appear transiently but the conclusion (T - w)^{mu2}|_{T -> T+w} = T^{mu2} is binomial-free; char q divides some binom(mu2, k) harmlessly (the corresponding c-coefficients vanish on BOTH sides).
>
> Step B (from B_k to C_k+: layer 2, already proved at general mu2). B_k has x-degree up to (mu2 - k + 1)D2 - ish; the canonical coefficients C_k+ are obtained from the B_k by reduction mod the monic Phi2+ (carries between coordinates) and in-coordinate x-/Phi'-carries. GENTOW-2 layer 2 (PROVED at general mu2 — GENTOW1_PROOF S3, whose grade note restricts only layer 1) prices every such correction: in-coordinate carries are weight-nondecreasing (GENTOW-1 Step 0), and each flow UP one Phi2-coordinate trades weight >= (mu2-k)lam at coordinate k for a contribution at coordinate k+1 of weight >= (mu2-k)lam - E2 > (mu2-k-1)lam (using lam > E2, the composed node floor) — strictly above coordinate (k+1)'s threshold. Weights lower-bound dv2 at x0 on the tower-node locus (GENTOW-1 Step 0 + GENHN-2'). Hence
>
>     dv2(C_k+(x0) - B_k(x0)-contribution) > (mu2 - k) * lam,
>
> and with Step A, dv2(C_k+(x0)) > (mu2 - k)lam for k < mu2. The top coefficient C_{mu2}+ = 1 and the new side's multiplicative residual is T^{mu2} by the same Step-A display at k = mu2. ∎”

**RESOLUTION TRACE:** Base §S1.3, lines 263–325. Step B's grid translation consumes LEMMA GENTOW5-D in the FORWARD direction only, which is exactly what survives S11.1's withdrawal of the two-directional closure (S11.1's consumption walk: “VERIFIED at GENTOW5-A Step B”). S12.1's unaffected-scope sentence keeps the refine-transfer content at its stated event hypotheses.

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:Step 0` — grep-verified count **11**; the carry pricing consumed in Step B.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN-2′` — grep-verified count **3**; weights lower-bound dv2 on the tower-node locus.

**TEETH:** §S5's P-A1/P-A2/P-A3 (the three mu2 = 3 pointwise re-division kills) and T-A1W/T-A2W (wrong height, wrong digit).

---

### EFF.GENTOW5.11  [lemma]

**CANONICAL STATEMENT:** COROLLARY GENTOW5-A′ (i) — GENTOW-2 closes at general mu2

> “(i) LEMMA GENTOW-2's clauses (ii), (iii), (iv) hold at general mu2: (ii) is THEOREM GENTOW5-A; (iii)'s triangularity/bijection consumed layer 1 only through (ii) (GENTOW1_PROOF S3 layer 3, general-mu2 as written); (iv)'s reverse transport is the SAME Step-A computation run on Phi2 = Phi2+ + lift with R_N(T) = T^{mu2} at the refined frame: coordinate j receives minimal class binom(mu2, j) w^{mu2-j} N^{mu2-j} from C_{mu2}+ = 1 — pin (mu2-j)lam with multiplicative residue binom(mu2, j)(-w)^{mu2-j} exactly where q does not divide binom(mu2, j), strictly above where it does. (ii)'s GRADE NOTE restriction is hereby lifted.”

**CONDITIONALITY:** Inherits THEOREM GENTOW5-A's hypotheses; the reverse-transport residue statement is characteristic-sensitive by design (“exactly where q does not divide binom(mu2, j), strictly above where it does”).

**DERIVATION:** As quoted — clause (ii) is `.10`; clause (iii) is imported unchanged from GENTOW1_PROOF S3 layer 3; clause (iv) is the Step-A computation of `.10` re-run at the refined frame.

**RESOLUTION TRACE:** Base §S1.4(i), lines 330–339; untouched by later rounds.

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:LEMMA GENTOW-2` — grep-verified count **7**; the clauses whose grade-note restriction is lifted.

**TEETH:** §S5's P-A1/A2/A3 rows are the pointwise instances of the lifted clause.

---

### EFF.GENTOW5.12  [instance-record]

**CANONICAL STATEMENT:** COROLLARY GENTOW5-A′ (ii) — the level-1 rider

> “(ii) *Level-1 rider (display, no new claim on frozen text).* The S1.1–S1.3 argument runs verbatim one level down (gr(L1) at a stage leaf, N := [n(kappa)(x0)], GENHN-2 in place of GENHN-2', GENHN-4 layer 2 in place of GENTOW-2 layer 2): it is an elementary general-mu carry display of exactly the kind GENHN-BOX-2's text names as its retirement condition ("the GENH4-S5 computation at general (e1, f1, mu)"). GENHN_PROOF is frozen; recording the consumption there is the orchestrator's dated update, not this note's edit.”

**CONDITIONALITY:** Explicitly “no new claim on frozen text”: the rider is a display, and the corresponding GENHN consumption append is NOT landed. Downstream, S3's index-0 scope fold *does* claim clause (d) at index 0 “via S1.4(ii)'s level-1 rider” (see `.26`, `.30`).

**DERIVATION:** The rider's derivation is the verbatim transport of §§S1.1–S1.3 one level down, with the two named substitutions.

**RESOLUTION TRACE:** Base §S1.4(ii), lines 341–349; consumed by the post-PE5 acceptance fold at S3 (lines 769–773) for (d)@0.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN-BOX-2` — grep-verified count **5**; the box whose retirement condition this rider matches.

**TEETH:** None inside this note's battery — the rider is not machine-exercised at level 1 here.

---

### EFF.GENTOW5.13  [scope-record]

**CANONICAL STATEMENT:** S1.5 GENTOW-BOX-1 DISPOSITION

> “**RETIRED as a mathematical box; the residue is grade-only.** What LEMMA GENTOW-2 layer 1 at mu2 >= 3 now consumes: LEMMA GENTOW5-A0 (elementary, self-contained), LEMMA GENTOW5-A1 (self-contained given GENHN-2' + the S4/T(b)'(iii) wrap letters — all accepted corpus), THEOREM GENTOW5-A (this note), and GENTOW-2 layer 2 @ GENTOW1_PROOF (grade 0/2). No W-9-analogue weld face is consumed; the graded frame is gr(L2) itself. Honest conditionality: this note is at grade 0/2 (hostile arc owed), GENTOW-1/GENTOW-2 are at 0/2, and the accepted pins are T(b)'(i)/(ii)/(iii) + S4's coherent normalizers (GENHN accepted 2/2 at PE4). Machine leg: S5's CHECK-A rows are the FIRST mu2 = 3 pointwise re-division kills anywhere in the program (the GN-REFINE3 pattern at the composed key), including a char-3 row and an f2 = 2 two-flavor-lift row.”

**CONDITIONALITY:** The “grade 0/2” self-assessment is superseded by the acceptance record (**ACCEPTED 2/2**, resolution rule 3); the *pin-stack* conditionality (GENTOW-1/GENTOW-2 at their own grades) is not superseded by this note.

**DERIVATION:** The disposition is read off `.06`, `.08`, `.10`: the frame the box demanded is `gr(L2)`, which A0 supplies for free, so no weld face is needed.

**RESOLUTION TRACE:** Base §S1.5, lines 351–365; grade sentence superseded at lines 1671–1741.

**NON-IMPORT (explicit):** “No W-9-analogue weld face is consumed.”

**TEETH:** §S5 CHECK-A rows (P-A1/A2/A3, incl. the char-3 and f2 = 2 frames).

---

### EFF.GENTOW5.14  [definition]

**CANONICAL STATEMENT:** DEF GENTOW5-1 (the depth-r tower data) — indices, ladders, floor chain

> “Indices: level 1 = the outer stage (key Phi_1 := Phi', deg D_1 = e1f1); level i has stage data (e_i, f_i) with properness l_i := e_i f_i >= 2 at every i >= 2 (an improper stage is a refinement, not a level — FGMN Lemma 3.5/Prop 3.7 collapsing, per GENTOW2 S6 (H-f)). Write ehat_i := e_1 ... e_i, D_i := l_1 ... l_i (l_1 := e1f1), K_0 := F_Q, K_i := F_{Q^{f_1...f_i}}.”

> “* **Ladders.** dv_i := ehat_i * v. Heights at level-(i+1) points: u_1 := h = dv_1(x); u_{i+1} := dv_{i+1}(Phi_i(xi)) with gcd(u_{i+1}, e_{i+1}) = 1; so dv_i(Phi_j) = (ehat_i/ehat_{j+1}) * u_{j+1} for j < i. Side constants E_i := e_i f_i u_i (E_1 = D_1 h). **Floor chain:** u_{i+1} > e_{i+1} E_i (provenance: the level-i budgets' node corollary, S3(e); at i = 1 this is the [r1] node floor u_2 > e_2 D'h verbatim since E_1 = D'h).”

**CONDITIONALITY:** Datum-level hypotheses: properness `l_i >= 2` at `i >= 2`, coprimality `gcd(u_{i+1}, e_{i+1}) = 1`, and the floor chain. The floor chain's *provenance* is S3(e), which at index n ≥ 3 is itself conditional on `[GENTOW5-W(i)]` after S12.1 — S12.1 makes the distinction explicit:

> “Later arguments may still use that inequality unconditionally when it is included explicitly in the fixed tower datum; only its claimed automatic derivation from the recipe is conditional.”

Rung 1 of the chain is unconditional: it “rides the accepted [r1] node floor u_2 > e_2 E_1 = e_2 D'h directly”.

**DERIVATION:** Definitional. The one derived line is `dv_i(Phi_j) = (ehat_i/ehat_{j+1}) * u_{j+1}` for `j < i`, which is the ladder rescaling of the level-(j+1) height `u_{j+1}`.

**RESOLUTION TRACE:** Base §S2.1, lines 372–385. Floor-chain provenance re-verified at the post-PE4 rider (lines 874–876) and re-scoped at S12.1 item 4 (out of range).

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:Lemma 3.5` — grep-verified count **1**; the FGMN collapsing statement for improper stages.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:Prop 3.7` — grep-verified count **1**; same clause.

**TEETH:** §S5's P-B1/B2 (“floor chain tight (u = 5, 21, 85, 341)”).

---

### EFF.GENTOW5.15  [definition]

**CANONICAL STATEMENT:** DEF GENTOW5-1 — the normalizer recursion

> “* **Normalizers (the recursion of HE7-2', tower-based).** n1hat(m) := pi^a x^{i0} (i0 < e1, e1*a + i0*h = m); for i >= 1
>
>       nhat_{i+1}(k) := nhat_i(m_i(k)) * Phi_i^{b_i(k)},
>       e_{i+1} m_i(k) + b_i(k) u_{i+1} = k,  0 <= b_i(k) < e_{i+1}
>
>   (unique since gcd(u_{i+1}, e_{i+1}) = 1). Unrolled: nhat_i(m) = pi^a x^{i0} Phi_1^{b_1} ... Phi_{i-1}^{b_{i-1}} with i0 < e1, b_j < e_{j+1}. At i = 2 this is GENTOW-1 S3's n2hat verbatim. NOTE the base differs from HE7-2's varpi-powers (varpi^k has unreduced x-degree); the two systems differ per height by a fixed unit — S2.3's remark.”

**CONDITIONALITY:** Uniqueness needs `gcd(u_{i+1}, e_{i+1}) = 1` from `.14`. Existence at a given height is not universal: S11.4 (out of range) records that a flavor base can demand a negative-height normalizer, and the note's own proviso excludes those (see `.17`).

**DERIVATION:** Definitional recursion; the unrolled form follows by iterating the two-line solve, and uniqueness of `(m_i(k), b_i(k))` is the coprimality solve mod `e_{i+1}`.

**RESOLUTION TRACE:** Base §S2.1, lines 387–398. The `i = 2` verbatim identification with GENTOW-1's `n2hat` is re-checked numerically at §S2.2 (`.21`).

XREF: `lean/notes/openmath/HE7_PROOF_2026-08-08.md:ANNEX-DEF HE7-2′` — grep-verified count **6** (Unicode prime; the ASCII form used in GENTOW5's body has count 0 in HE7_PROOF — see the reading note at `.03`).

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:S3` — grep-verified count **14**; the level-2 normalizer this recursion reproduces.

**TEETH:** §S2.2's worked pins (`.21`) and §S5's P-B1/B2.

---

### EFF.GENTOW5.16  [definition]

**CANONICAL STATEMENT:** DEF GENTOW5-1 — cocycle and letters

> “* **Cocycle + letters.** tau_i(a, b) := nhat_i(a) nhat_i(b) / nhat_i(a+b); the level letters Lam_i := Phi_i^{e_{i+1}} / nhat_i(u_{i+1}) (dv-value 0 at level-(i+1) points), beta_{i,xi} := res(Lam_i(xi)); transport tower iota^{(i+1)} extending iota^{(i)} by beta_i -> beta_{i,xi} — ANNEX-DEF HE7-2''s attached objects, tower-instantiated.”

**CONDITIONALITY:** The value-0 claim for `Lam_i` holds at level-(i+1) points (the node locus of `.19`).

**DERIVATION:** Definitional; the `dv`-value-0 claim is the height arithmetic `dv_i(Phi_i^{e_{i+1}}) = e_{i+1} u_{i+1} / e_{i+1}`-normalized against `nhat_i(u_{i+1})`, i.e. equal heights by `.14`'s ladder.

**RESOLUTION TRACE:** Base §S2.1, lines 400–405; the residue computation for `res(tau_i)` is carried out at §S2.3 step (3) (`.22`) and, at level 2, at `.08`.

XREF: `lean/notes/openmath/HE7_PROOF_2026-08-08.md:ANNEX-DEF HE7-2′` — grep-verified count **6**.

**TEETH:** §S5's T-A4W (letter-live twist) and the PE1 fresh frame FR-1 cited at `.18`.

---

### EFF.GENTOW5.17  [definition]

**CANONICAL STATEMENT:** DEF GENTOW5-1 — K_i-digit lifts, at the `[GT5-r2]` CORRECTED DISPLAY

> “* **K_i-digit lifts. [GT5-r2 CORRECTED DISPLAY — PE2 F-2: the composed display bound the base exponents (i0, b_j) to nhat_i(m)'s and stepped only x and Phi_j; at seam-live heights the stepped monomial's compensating pi-exponent goes NON-INTEGER and the displayed flavor DOES NOT EXIST. The corrected display RE-SOLVES the base per flavor.]** For c in K_i and height m, the f_1 f_2 ... f_i within-class FLAVOR MONOMIALS at height m are
>
>       M_{r,t}(m) := nhat_i(m - Delta(r,t)) * x^{e_1 r} *
>                     Phi_1^{e_2 t_1} ... Phi_{i-1}^{e_i t_{i-1}},
>       Delta(r,t) := e_1 r * (ehat_i/e_1) h
>                     + Sum_{j<i} e_{j+1} t_j (ehat_i/ehat_{j+1})
>                       u_{j+1},
>
>   indexed by 0 <= r < f_1, 0 <= t_j < f_{j+1} (a flavor is absent when nhat_i(m - Delta(r,t)) has no ladder solution). Each M_{r,t}(m) sits at dv_i-height m EXACTLY, and its exponents stay in ladder range (x-exponent i0' + e_1 r < e_1 f_1 = D_1 since i0' < e_1; Phi_j-exponent b_j' + e_{j+1} t_j < e_{j+1} f_{j+1} = l_{j+1} since b_j' < e_{j+1}), so deg M_{r,t} < D_i. Then
>
>       lift_i(c; m) := Sum_{r,t} d_{r,t} * M_{r,t}(m),
>
>   O-digit coefficients d_{r,t} realizing c in the coherent normalization (res((lift_i(c; m)/nhat_i(m))(xi)) = iota^{(i)}(c)); existence/freeness is LEMMA GENTOW5-C's (LIFT_i) clause, and the derivation IS the class-separation lemma: within the height-m class mod ehat_i the slots differ by the steps e_1 r, e_{j+1} t_j, each slot's base is the normalizer of the COMPLEMENTARY height m - Delta(r,t) — NOT nhat_i(m)'s base — and the flavor residues res((M_{r,t}(m)/nhat_i(m))(xi)) are the FIXED letter units of the tau_i-cocycle (S2.3 step (3)), so the d_{r,t} are the inverse-twisted K_{i-1}-expansion digits of c.”

**CONDITIONALITY:** Two later corrections govern the height range of this display, in sequence.

S11.4 (out of range) attaches an m-range:

> “the flavor display and the realization sentence ("O-digit coefficients d_{r,t} realizing c") read AT HEIGHTS m IN (LIFT_i)'S VALIDITY RANGE — k-uniformly above the bound_{i+1} recursion of LEMMA GENTOW5-C”

S12.2 (out of range) **withdraws** that bracket and fixes the correct rung:

> “**Superseded S11.4 bracket.** The sentence placing the displayed \(\operatorname{lift}_i(c;m)\) above \(\operatorname{bound}_{i+1}\) is WITHDRAWN. That display realizes \(c\in K_i\) by a polynomial of degree \(<D_i\); hence it consumes the PRECEDING lift instance and has threshold \(\operatorname{bound}_i\), not \(\operatorname{bound}_{i+1}\).”

**Effective reading:** the display is valid for `m > bound_i`, supplied by `(LIFT_{i-1})` at `i >= 2` and by the accepted base lift at `i = 1`; the “flavor is absent when nhat_i(m - Delta(r,t)) has no ladder solution” proviso already excludes negative-height bases (S11.4's own worked failure: `i = 1, e_1 = 2, f_1 = 2, h = 1, m = 0`, where the `r = 1` flavor demands `pi^{-1}`).

**DERIVATION:** [ASSEMBLED — the note's own derivation sentence plus its machine verification] The derivation named in the display is LEMMA GENTOW5-C's class-separation step (3): flavor residues are the fixed tau_i-cocycle letter units, so the coefficients are the inverse-twisted `K_{i-1}`-expansion digits. The corrected base-solve is verified numerically:

> “VERIFICATION AT PE2's FR-A (p = 3, e_1 = 2, h = 1, e_2 = 1, u_2 = 3; m = 14, nhat_2(14) = 3^7): the t_1 = 1 flavor is M_{0,(1)}(14) = nhat_2(14 - 3) * Phi_1 = 3^5 * x * Phi_1 (nhat_2(11) = 3^5 x — the x-exponent RE-SOLVES 0 -> 1); the composed fixed-base display demanded pi-exponent (14 - 0 - 3)/2 = 11/2, NO such monomial. Machine row: check FA1-LIFT (gentow5_pe2_fresh.py @ 40f313a, 22/0) asserts the fixed-base flavor's non-existence AND the green chain runs on the re-solved member 3^5*x*Phi_1 = FR-A's khat_0.”

And its ripple fence:

> “Ripple (checked): the recipe's khat_t and S2.4's value-blind leg read HEIGHTS only — each M_{r,t}(m) sits at height m exactly, unchanged; (LIFT_i)'s bound arithmetic and deg < D_i are as displayed; no other consumer in this note reads the flavor bases.”

**RESOLUTION TRACE:** Base §S2.1 display, replaced in place by `[GT5-r2]` (PE2 F-2, lines 407–458); m-range bracket added by S11.4; that bracket superseded by S12.2 (resolution rule 5).

**NON-IMPORT (explicit):** “GENTOW1 S3's fixed-base READING of its lift display fails the same way at seam-live heights — a display-level defect there, flagged for that note's own arc, not consumed here.”

**TEETH:** `FA1-LIFT` (gentow5_pe2_fresh.py @ 40f313a, 22 checks / 0 violations).

---

### EFF.GENTOW5.18  [definition]

**CANONICAL STATEMENT:** DEF GENTOW5-1 — THE COMPOSED KEY RECIPE, at the `[GT5-r1]` GAUGE PIN

> “* **THE COMPOSED KEY RECIPE (the charge's display). [GT5-r1 GAUGE PIN — the governing pin of the r1 round; PE1 F-1 CRITICAL].** Given stage data (e_{i+1}, f_{i+1}) and monic irreducible psi_{i+1} = y^{f_{i+1}} - Sum_{t<f_{i+1}} c_t y^t over K_i with c_0 != 0:
>
>       Phi_{i+1} := Phi_i^{e_{i+1} f_{i+1}}
>                    - Sum_{t < f_{i+1}} khat_t * Phi_i^{e_{i+1} t},
>       khat_t := lift_i(c_t * vartheta_{i, f_{i+1}-t};
>                        u_{i+1}(f_{i+1} - t))        (0 if c_t = 0),
>
>   where vartheta_{i,s} := res(nhat_i(u_{i+1})^s / nhat_i(s*u_{i+1})) in K_i^x is the FIXED telescope unit of the tau_i-cocycle (S1.2's vartheta and S2.3 step (3), run at level i and heights multiples of u_{i+1}): vartheta_{i,0} = vartheta_{i,1} = 1, vartheta_{i,s+1} = vartheta_{i,s} * res(tau_i(s*u_{i+1}, u_{i+1})).”

> “  Monic of degree D_{i+1}; every side term at dv_{i+1}-height E_{i+1} exactly (e_{i+1} * u_{i+1}(f_{i+1}-t) + e_{i+1} t u_{i+1} = E_{i+1}; the top term e_{i+1} f_{i+1} u_{i+1} = E_{i+1} — the vartheta twist is a residue-level unit, height-blind). At i = 1 this is T(b)''s Phi2 AT ITS ERRATUM-CORRECTED DISPLAY (59c1966), NOT the gauge-naive original; at i = 2 the r3 box's Phi3 with vartheta_2-corrected digits.”

**CONDITIONALITY:** The recipe's lifts must exist in range. S12.2 discharges exactly that, unconditionally:

> “For a nonzero recipe coefficient \(c_t\), put \(s=f_{i+1}-t\). Since \(t<f_{i+1}\), one has \(s\ge1\), and the recipe height is \[ m_t=s\,u_{i+1}\ge u_{i+1} >e_{i+1}E_i\ge E_i>\operatorname{bound}_i. \]”

with the boxed inequality it rests on: `bound_i < E_i for every i >= 1`.

**DERIVATION:** [ASSEMBLED — the r1 gauge-pin derivation, quoted] The twist is derived in the building direction from `.08`'s dictionary:

> “[GT5-r1 derivation, NOT a transcription. Why the twist: grouping the recipe in Phi_i-slots, the slot-t MULTIPLICATIVE residual coefficient (S1.2's convention — the side residual's read; [GT5-r2] per the landed GENTOW2 r3 B-law the FGMN R-read differs from it by the cross-frame unit w_i per grade — the S3(a) re-scope) is res(khat_t / nhat_i(u_{i+1})^{f-t}) = digit(khat_t) * res(nhat_i((f-t)u_{i+1}) / nhat_i(u_{i+1})^{f-t}) = digit(khat_t) * vartheta_{i,f-t}^{-1} (f := f_{i+1}); for that coefficient to equal psi_{i+1}'s c_t, the prescribed COHERENT digit must be c_t * vartheta_{i,f-t} — LEMMA GENTOW5-A1's dictionary gamma = c * vartheta, applied in the BUILDING direction. The plain lift lift_i(c_t; ·) is the GAUGE-NAIVE form: its multiplicative coefficient is c_t * vartheta^{-1}, wrong wherever the letters are live.”

Level-2 recovery, the derivation's own consistency check against the accepted GENHN erratum:

> “Level-2 recovery: n1hat monomials are pi^a x^{i0}; multiplying s copies of n1hat(u_2) accumulates x-exponent s*i(u_2), reduced to ladder range by floor(s*i(u_2)/e1) x-wraps x^{e1} = pi^h * (x^{e1}/pi^h), so vartheta_{1,s} = eta^{floor(s*i(u_2)/e1)}; at s = f_2 - t this is EXACTLY the GENHN dated erratum's corrected chat_t := lift(c_t*eta^{W(t)}), W(t) = floor((f_2-t)*i(u_2)/e1) (erratum 59c1966, provoked by HETOW PE1 F-1; pinned at GENTOW1 by [GT1-r1] 477b1b1).”

Degeneracy fence and the machine tooth:

> “At any frame where each c_t * (vartheta_{i,f-t} - 1) = 0 — in particular all letters = 1, or f_{i+1} = 1 (only s = 1 occurs, vartheta_{i,1} = 1) — corrected = naive. MACHINE VERIFICATION at a letter-live frame (the PE1 fresh instrument gentow5_pe1_fresh.py @ 0160b94, FR-1: p = 3, Phi_1 = x^2 - 6, eta = 2, (e_2,f_2) = (1,2), u_2 = 3, psi_2 = y^2 + y + 2, i(u_2) = 1 so W(1) = 0, W(0) = 1): the corrected key Phi_1^2 - 6x*Phi_1 - 54 is the carrier — sigma = (2,2), nfeltval(Phi_1) = 3 exact; the gauge-naive key Phi_1^2 - 6x*Phi_1 - 27 has sigma = {(4,1)} with degenerate residual (y-1)^2 — THEOREM GENTOW5-B (a)/(b) fail at the naive display there.”

**RESOLUTION TRACE:** Base §S2.1 recipe display, pinned by `[GT5-r1]` (PE1 F-1, lines 460–520) with the `[GT5-r2]` parenthetical inserted at the R-read sentence. Its governing scope is declared inside the pin: “This pin governs khat_t at its uses below (S2.4's INV-j heights — value-blind, see there; S3's statement + (a), (b), (c) Step 5, (d); S4.1's witness keys — seam-blind, see there).”

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:W(t) = ⌊(f₂−t)·i(u₂)/e₁⌋` — grep-verified count **1** (GENHN_PROOF line 1990); the erratum's exponent law that the level-2 specialization reproduces. The erratum's corrected digit is printed there as `ĉ_t := lift(c_t·η^{W(t)})` — grep-verified count **1** (line 1997); GENTOW5's ASCII `chat_t` is the transliteration of that Unicode designation (the ASCII string `chat_t` has count **0** in GENHN_PROOF).

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:[GT1-r1]` — grep-verified count **5**; the round at which the erratum was pinned there.

**TEETH:** PE1 fresh frame FR-1 (gentow5_pe1_fresh.py @ 0160b94, 15/0 — the corrected/naive key discrimination); §S5's T-A4W convention tooth.

---

### EFF.GENTOW5.19  [definition]

**CANONICAL STATEMENT:** DEF GENTOW5-1 — the depth-(i+1) node locus

> “* **The depth-(i+1) node locus P_{i+1}** := roots xi with v(x(xi)) = h/e1 exactly, eta(xi) a psi_1-root, and inductively v(Phi_j(xi)) = u_{j+1}/ehat_{j+1} exactly with the level-(j+1) residue class a psi_{j+1}-root, for j < i+1 — the tower transport chain (T(b)'(iii) at i = 1; GENTOW2-A(d)'s data at i = 2).”

**CONDITIONALITY:** Definitional; nonemptiness of `P_{i+1}` is a hypothesis wherever it is consumed (explicitly assumed in LEMMA GENTOW5-C, `.22`).

**DERIVATION:** Definition; the claim that recipe roots lie in it is clause (b) of THEOREM GENTOW5-B (`.28`), not part of this definition.

**RESOLUTION TRACE:** Base §S2.1, lines 522–526; untouched by later rounds.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:THEOREM GENTOW2-A` — grep-verified count **8**; its clause (d) supplies the i = 2 data.

**TEETH:** §S4.2's P-B4/P-C2 ladder rows are the witness's `P`-membership evidence (exact ladder 16, 40, 84, 170, 341).

---

### EFF.GENTOW5.20  [lemma]

**CANONICAL STATEMENT:** first-live arithmetic

> “First-live arithmetic: a depth-r tower with a live top problem mu_r >= 2 needs n = D_r * mu_r >= 2^{r+1}; depth 4 first lives at n = 32 (S4's witness is exactly minimal).”

**CONDITIONALITY:** Uses properness `l_i >= 2` at `i >= 2` from `.14` (so `D_r >= 2^r`) and a live top problem `mu_r >= 2`.

**DERIVATION:** [ASSEMBLED — from the note's own datum] `D_r = l_1...l_r` with every `l_i >= 2` gives `D_r >= 2^r`, and `mu_r >= 2` gives `n = D_r mu_r >= 2^{r+1}`; at `r = 4` this is `n >= 32`, attained by §S4's witness.

**RESOLUTION TRACE:** Base §S2.1, lines 528–530; untouched.

**TEETH:** §S4's witness is the attainment instance (`deg 32 = the first-live depth-4 degree`).

---

### EFF.GENTOW5.21  [regression-record]

**CANONICAL STATEMENT:** §S2.2 Consistency checks on the recursion (worked pins)

> “n3hat(85) at the S4 chain ((e_i) = (2,2,2,2), h = 1, u = 5, 21, 85): recursion: b_3... level 3: 2m + 21b = 85, b < 2 -> b = 1, m = 32; level 2: 2m' + 5b' = 32, b' < 2 -> b' = 0, m' = 16; base: 2a + i0 = 16 -> i0 = 0, a = 8. n3hat(85) = 2^8 * Phi_2 — matching the direct unrolled solve (16a + 8 i0 + 20 b_1 + 42 b_2 : mod-parity forces b_2 = 1, then b_1 = 0, i0 = 0, a = 8... on the dv_4 ladder; see S4). The r3 witness n2hat(21) = 16 Phi' is the recursion at level 2: 2m + 5b = 21 -> b = 1, m = 8 -> 2a + i0 = 8 -> 2^4. Both match the committed runners' values (genhnr2_supp L388-389; gentow2 W1).”

**CONDITIONALITY:** Two worked instances of `.15`, not a general claim.

**DERIVATION:** The displayed solves are the derivation.

**RESOLUTION TRACE:** Base §S2.2, lines 532–542; untouched.

**TEETH:** Cross-checked against committed runner values (`genhnr2_supp` L388–389; `gentow2` W1) and reproduced in §S4.1's key list.

---

### EFF.GENTOW5.22  [lemma]

**CANONICAL STATEMENT:** LEMMA GENTOW5-C ((SLOT_i) + (LIFT_i) for the tower ladder)

> “**Statement.** Let i >= 1 and assume the tower data of DEF GENTOW5-1 through level i+1 with P_{i+1} nonempty, and (SLOT_{i-1}) at level i (base: i = 1 is GENHN-2 + HE6-1's transport identity; i = 2 is GENHN-2' — both accepted). Let xi in P_{i+1}, C in O[x] with 0 != deg C < D_{i+1}, developed C = Sum_{b < e_{i+1} f_{i+1}} c_b Phi_i^b with deg c_b < D_i. Then dv_{i+1}(C(xi)) equals the slot minimum EXACTLY; the minimizing b lie in one class mod e_{i+1}; and the height-k residue against nhat_{i+1}(k)(xi) is iota^{(i+1)}(Sum_t gamma_t vartheta_t beta_i^t) != 0 with gamma_t the level-i digit symbols ((SLOT_{i-1})) and vartheta_t the FIXED twist units of the telescoped tau_i-cocycle — i.e. one K_{i+1}-digit per dv_{i+1}-height, class separation mod e_{i+1} between Phi_i-slots and mod ehat_{i+1} overall. (LIFT_i): k-uniformly above the bound recursion bound_{i+1} = (l_{i+1}-1)u_{i+1} + e...*bound_i, every K_{i+1}-residue at height k is realized by some C with deg < D_{i+1} (inverse-twisted digits).”

The truncated token in the bound display is restored by the in-range acceptance fold:

> “[acceptance fold 2026-08-10 (PE5-F-3): the bound display's truncated token "e..." reads e_{i+1} — bound_{i+1} = (l_{i+1}-1)u_{i+1} + e_{i+1}*bound_i. Re-derived at the primary source, not restored from memory: ANNEX-THEOREM R1-c displays the recursion bound_{i+1} := (L_i - 1)u_i + l_i*bound_i with L_i = l_i g_i the stage size and l_i the ramification multiplier (HE7_PROOF ANNEX R; its arithmetic line m_0 = (k - s_0 u_i)/l_i >= (g_i - 1)u_i + bound_i), and in this lemma's tower names the step-(1) height split is k = e_{i+1}*m + b*u_{i+1} with b <= l_{i+1} - 1 (slots b < e_{i+1}f_{i+1}), so the slot term saturates at (l_{i+1}-1)u_{i+1} and the level-i threshold scales by the ramification factor e_{i+1}. Grep-scoped this fold: bound_i appears in this note only at this statement display — no numeric consumption site found (the proof's own remark: the bound arithmetic never sees residues).]”

**CONDITIONALITY:** Induction hypothesis `(SLOT_{i-1})` at level i, `P_{i+1}` nonempty, and the DEF GENTOW5-1 datum through level i+1. Base cases i ≤ 2 rest on accepted corpus; at i ≥ 3 the argument rides the HE7 ANNEX R precedent pin (now at acceptance grade — see the DERIVATION's dated fold). Note that S12.2 (out of range) keeps `(LIFT_i)`'s own threshold at `bound_{i+1}` — it is `lift_i`, not `(LIFT_i)`, whose rung was mis-stated:

> “By contrast, the clause labelled \(({\rm LIFT}_i)\) in LEMMA GENTOW5-C constructs \(K_{i+1}\)-digits of degree \(<D_{i+1}\) and therefore correctly has threshold \(\operatorname{bound}_{i+1} =(l_{i+1}-1)u_{i+1} +e_{i+1}\operatorname{bound}_i.\)”

**DERIVATION:** Quoted proof:

> “**Proof: ANNEX-THEOREM R1-b/R1-c's proofs, re-based.** The HE7 ANNEX R proofs consume exactly four clauses of their level-i datum: (a) values exact one level down ((SLOT_{i-1}), our induction hypothesis); (b) the defining clause w_{i+1}(Phi_i(xi)) = u_{i+1} exactly (our P_{i+1}, clause j = i); (c) gcd(u_{i+1}, e_{i+1}) = 1 (DEF GENTOW5-1); (d) {1, beta_i, ..., beta_i^{g-1}} a K_i-basis of K_{i+1} with beta_i := the level-(i+1) residue letter, r_i := its minimal polynomial irreducible (our psi_{i+1}-root clause of P_{i+1}, f_{i+1} = deg psi_{i+1}). Steps: (1) values of c_b(xi)Phi_i(xi)^b are e_{i+1}*w_i(c_b) + b*u_{i+1} exactly by (a)+(b); (2) cross-class ties impossible: b*u_{i+1} mod e_{i+1} bijective by (c); (3) within one class, slots b0 + e_{i+1}t: the monomial identity of R1-b (R1.2) with theta_t telescoping into tau_i-values; each theta_t has residue a fixed K_i^x-unit by the S1.2-style cocycle computation run at level i (the letter monomial — tau_i is a Laurent monomial in pi, x, Phi_1, ..., Phi_{i-1} of dv-value 0, residue a fixed product of the letters beta_1 ... beta_{i-1} through iota^{(i)}); (4) summing the class, the residue is the displayed K_i-combination of beta_i-powers, nonzero by (d) since the gamma_t vanish iff their slots do not attain and at least one attains — no cancellation, value exact. (LIFT_i): R1-c verbatim — prescribe the level-i digits INVERSE-twisted by vartheta_t^{-1} ((LIFT_{i-1}) supplies them one level down; base = the level-1/2 lift lemmas, accepted); the bound arithmetic never sees residues.”

Grade fold on the precedent pin:

> “**Grade honesty:** this is HE7 ANNEX R's R1-b/R1-c argument transported onto the tower ladder — [GT5-r1 DATED FOLD 2026-08-10, orchestrator-authorized (ledger B8, 87a7b61): the annex stack is now ACCEPTED 2/2 (annexpass CLEAN 4a613d8 -> annexpass2 CLEAN a472155, "the annex stack is ACCEPTED 2/2"; the HETOW acceptance record e38df9f consumes it); the composition-time wording "POST-RATIFICATION, UNPASSED (annex grade)" is superseded in the CONSERVATIVE direction — the pin claimed weaker support than the truth]; the transport itself (the four-clause instantiation table above) is this note's, and the base cases i <= 2 rest only on accepted corpus. Every i >= 3 consumer below carries this pin explicitly, now at the acceptance grade. ∎”

**RESOLUTION TRACE:** Base §S2.3, lines 544–613, with the `[GT5-r1]` grade fold inside the proof and the post-PE5 `[acceptance fold]` on the bound token. Step (3) of this proof is the derivation cited by `.17` and by `.27`'s i ≥ 3 leg — and it is precisely the leg that S11.2 (out of range) fences: it carries per-grade fixedness, **not** the single-w monomial form.

XREF: `lean/notes/openmath/HE7_PROOF_2026-08-08.md:ANNEX-THEOREM R1-b` — grep-verified count **4**.

XREF: `lean/notes/openmath/HE7_PROOF_2026-08-08.md:ANNEX-THEOREM R1-c` — grep-verified count **3**.

XREF: `lean/notes/openmath/HE7_PROOF_2026-08-08.md:R1.2` — grep-verified count **7**; the monomial identity consumed at step (3).

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN-2` — grep-verified count **28**; the accepted `i = 1` base (`GENHN-2′`, count **3**, is the `i = 2` base).

**TEETH:** No dedicated committed row at i ≥ 3; the note's own coverage box (`.40`) names this as the machine-side gap. §S5's A-rows exercise the i ≤ 2 instances.

---

### EFF.GENTOW5.23  [fence]

**CANONICAL STATEMENT:** Remark (HE7 base vs tower base)

> “*Remark (HE7 base vs tower base).* HE7-2''s n_1 = varpi-powers and our n1hat differ per height by the fixed wrap letter (both are value-m monomials; the quotient is a value-0 Laurent monomial in x, pi with residue a fixed power of the level-1 letter). By J-D0 (counts twist-blind, letters re-coordinatize; R1.2 item 7) every count/degree/vanishing statement transports between the two systems; residue letters re-coordinatize by fixed units. We work in the tower base throughout; no invariance under CHANGING systems mid-argument is consumed (that stronger claim is false — HE7-T-BADTWIST).”

**CONDITIONALITY:** The transport is asserted for count/degree/vanishing statements only.

**DERIVATION:** The quotient of the two normalizer systems is a value-0 Laurent monomial, so J-D0 applies.

**RESOLUTION TRACE:** Base §S2.3 remark, lines 615–623; untouched.

**NON-IMPORT (explicit):** “no invariance under CHANGING systems mid-argument is consumed (that stronger claim is false — HE7-T-BADTWIST)”.

XREF: `lean/notes/openmath/HE7_PROOF_2026-08-08.md:R1.2` — grep-verified count **7**; item 7 is the twist-blindness audit.

**TEETH:** NONE.

---

### EFF.GENTOW5.24  [definition]

**CANONICAL STATEMENT:** the level-i weight functional, at the `[GT5-r1]` top-grid repair

> “**Weight. [GT5-r1 — PE1 F-3: the top-grid term is now DEFINED.]** On monomials M = pi^v x^{a} Phi_1^{J_1} ... Phi_i^{J_i} (exponents unbounded) define
>
>     wt_i(M) := ehat_i*v + a*(ehat_i/e1)h
>                + Sum_{j<i} J_j * (ehat_i/ehat_{j+1}) u_{j+1}
>                + J_i * E_i,
>
> i.e. the TOP variable Phi_i carries weight E_i = e_i f_i u_i per unit exponent — the in-datum lower bound (dv_i(Phi_i(xi)) > E_i on the tower locus by the field floor, vs the EXACT interior values dv_i(Phi_j(xi)) = (ehat_i/ehat_{j+1})u_{j+1} for j < i); the pre-repair display left this term as an undefined "E-part". Note wt_i consumes NO data beyond the depth-i datum: u_{i+1} does not appear.”

**CONDITIONALITY:** The top term is a *lower bound*, not an exact value — that asymmetry is the whole content of the r1 repair.

**DERIVATION:** Definitional; the top weight is fixed at `E_i` because the exact value `dv_i(Phi_i(xi))` is only known to exceed `E_i` (field floor), while interior values are exact.

**RESOLUTION TRACE:** Base §S2.4 weight display, replaced by `[GT5-r1]` (PE1 F-3, lines 628–642).

**NON-IMPORT (explicit):** “wt_i consumes NO data beyond the depth-i datum: u_{i+1} does not appear.”

**TEETH:** §S7's F-3 worked grid-4 equality instance (170 = 170 = 170).

---

### EFF.GENTOW5.25  [lemma]

**CANONICAL STATEMENT:** LEMMA GENTOW5-D (Step-0 carry monotonicity is level-agnostic), at the `[GT5-r1]`/`[GT5-r2]` restatement

> “**Statement [GT5-r1 restated — strictness weakened to what the induction needs].** For every level i, the i reduction moves — the x-carry (a >= D_1) and the Phi_j-carries (J_j >= l_{j+1}, j < i) — are wt_i-NONDECREASING; lift-generated terms preserve weight exactly; the key-part of each INTERIOR carry (the x-carry WHEN i >= 2, and the Phi_j-carries with j < i-1) strictly raises it, while the TOP carry's key-part (j = i-1: key-part Phi_i at weight E_i = wt(Phi_{i-1}^{l_i})) PRESERVES it exactly.”

> “[GT5-r2 — PE2 F-3, the i = 1 edge: at i = 1 the ONLY move is the x-carry and it IS the top carry (j = 0 = i-1): key-part Phi_1 at wt_1(Phi_1) = E_1 = D_1 h = wt_1(x^{D_1}) — PRESERVED, not strict; and the proof's rung range "1 (x-carry) through i-1" is EMPTY there (no floor rung consumed — the x-carry's strict pricing would reference u_2, out-of-datum at depth 1, the same disease [GT5-r1] cured at the top grid). Unconsumed edge: the named consumers instantiate i >= 2 (GENTOW5-A Step B at i = 2; S3(c)/(d) at i + 2 >= 3).]”

**Superseded consequence clause (quoted; corrected out of range).** The base text continues:

> “Hence "all slots at weight >= W" is the same condition on every grid of the tower (the two-directional rewriting closes), and per-slot weight arithmetic converts to the digit floors verbatim as in GENTOW-1 Step 0.”

and closes its proof with:

> “The converse rewriting (Phi_{j+1} = Phi_j^{l_{j+1}} - weight-E_{j+1} lifts) is weight-nondecreasing by the same displays. ∎”

S11.1 `[A-F1, CRITICAL]` withdraws both:

> “— FALSE as written. And the statement's consequence clause: "Hence 'all slots at weight >= W' is the same condition on every grid of the tower (the two-directional rewriting closes)" — WITHDRAWN to the one-directional form below.”

**Effective reading:** forward carry moves are `wt_i`-nondecreasing (statement untouched); the converse rewriting is weight-NONINCREASING — preserved exactly at the top rung, strictly lowered at each interior rung by the corresponding floor rung. The one surviving converse remnant is the SINGLE-STEP top-rung expansion, which preserves slot weights exactly.

**CONDITIONALITY:** Consumes only `(INV-j)` and `(FLOOR-j)`, both in-datum:

> “The only inputs are (INV-j): the recipe keys' side terms at exact height E_{j+1} (DEF GENTOW5-1's construction, gauge-pin-stable) and (FLOOR-j): u_{j+1} > e_{j+1} E_j, consumed at rungs 1 (x-carry) through i-1 (deepest interior carry; the range is EMPTY at i = 1, where no rung is consumed — the [GT5-r2] edge clause) — all inside the depth-i datum.”

**DERIVATION:** Quoted proof (the two displays, uniform in j):

> “* x-carry: x^{D_1} = Phi_1 + tail, tail monomials x^c pi^g with g >= (D_1 - c)h/e1 (Phi_1's one side): tail wt >= (ehat_i/e1) D_1 h = wt(x^{D_1}), equality on the side lattice; Phi_1-part wt = (ehat_i/ehat_2) u_2 > (ehat_i/ehat_2) e_2 E_1 = (ehat_i/e1) D_1 h — STRICT by the floor chain at j = 1 [GT5-r2: this pricing reads rung 1 (u_2), in-datum only when i >= 2; at i = 1 Phi_1 is the TOP variable, priced at wt_1(Phi_1) = E_1 = wt_1(x^{D_1}) — PRESERVED, the statement's edge clause].
> * Phi_j-carry: Phi_j^{l_{j+1}} = Phi_{j+1} + Sum_t khat_t Phi_j^{e_{j+1}t}; each lift term has wt = (ehat_i/ehat_{j+1}) [e_{j+1} u_{j+1}... ] — compute: khat_t's monomials all sit at dv_j-height u_{j+1}(f_{j+1}-t) exactly (single-height lifts, DEF GENTOW5-1 — [GT5-r1] the gauge pin's vartheta twist is a residue unit, so the corrected khat_t sits at the SAME heights: this display is value-blind, the GENTOW1 [GT1-r1] Step-0 immunity verbatim), contributing (ehat_i/ehat_{j+1}) e_{j+1} u_{j+1}(f_{j+1}-t) + e_{j+1} t (ehat_i/ehat_{j+1}) u_{j+1} = (ehat_i/ehat_{j+1}) E_{j+1} = wt(Phi_j^{l_{j+1}}) — PRESERVED exactly; the key-part splits [GT5-r1]:
>     - INTERIOR (j <= i-2): the Phi_{j+1}-part has wt = (ehat_i/ehat_{j+2}) u_{j+2} > (ehat_i/ehat_{j+2}) e_{j+2} E_{j+1} = (ehat_i/ehat_{j+1}) E_{j+1} — STRICT by floor rung j+1 (u_{j+2} > e_{j+2}E_{j+1}), which is IN-DATUM since j+2 <= i;
>     - TOP (j = i-1): the Phi_i-part has wt = E_i = l_i u_i = wt(Phi_{i-1}^{l_i}) — PRESERVED exactly, NO floor rung consumed (the pre-repair uniform pricing read the top key-part at u_{i+1}/e_{i+1}: non-integer, and at the top grid of a depth-r tower rung r references u_{r+1} = EVENT data outside the statement's floor chain — PE1 F-3's audit; the repair prices it at the defined weight E_i instead).”

**Failure-mode fence carried by the statement** (the r1 consumer note):

> “[GT5-r1 consumer note: nondecreasing is all any named consumer of this lemma uses (GENTOW5-A Step B's grid translation, S3(c) Steps 0/3, S3(d)); the strict FLOW-UP pricing there comes from lam > E separately, never from this lemma's strict clause. The pre-repair blanket "the key-part of each carry strictly raises it" was FALSE at the top carry — and contradicted the lemma's own i = 2 instance: GENTOW1_PROOF S2 Step 0 prices the Phi_2-part "at weight E2 exactly" (PRESERVED). … Failure mode fenced, worked at the S4 witness chain's grid 4 (u = (1,5,21,85), E_4 = 170): the top carry Phi_3^2 = Phi_4 + 2^8*Phi_2 has wt_4(Phi_3^2) = 2*(ehat_4/ehat_4)*u_4 = 2*85 = 170, Phi_4-part = E_4 = 170, and lift-part wt(2^8*Phi_2) = 16*8 + 2*21 = 170 — all three EQUAL: any downstream lean on top-carry strictness would be unsound; none exists in this note (checked at PE1 and re-checked this round).]”

**RESOLUTION TRACE:** Base §S2.4, lines 644–727, restated by `[GT5-r1]` and edged by `[GT5-r2]`; the consequence clause and the converse-direction sentence are superseded out of range by S11.1 (resolution rule 4). S11.1's own consumption walk re-verifies that the in-range consumers (`.10` Step B, `.29` Steps 0/3, `.30`) use only the forward direction.

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:S2 Step 0` — grep-verified count **2**; the i = 2 instance whose “Phi_2-part at weight E2 exactly” the restatement now matches.

**TEETH:** §S7 F-3's grid-4 equality instance (170 = 170 = 170); out of range, S11.1's isolated re-check `gentow5_af1_direction_check.py` (8 checks / 0 violations) exercises both directions.

---

### EFF.GENTOW5.26  [scope-record]

**CANONICAL STATEMENT:** THEOREM GENTOW5-B — statement header, plus the post-PE5 INDEX-0 SCOPE fold

> “**Statement.** Fix a base (Q; h) and a depth-r tower datum per DEF GENTOW5-1: stage data (e_i, f_i, psi_i) with properness l_i >= 2 (i >= 2), heights u_i satisfying the floor chain u_{i+1} > e_{i+1} E_i, keys Phi_1, ..., Phi_r built by THE RECIPE [GT5-r1: in its GAUGE-CORRECTED form — the S2.1 pin's vartheta-twisted khat_t; every clause below reads AT that form, and (a)/(b) are FALSE at the gauge-naive display on letter-live frames (PE1 FR-1's machine counter-instance, quoted at the S2.1 pin)], and the terminal inductive valuation nu_r (the MacLane chain mu_0 -(x, lam_1)-> mu_1 -(Phi_1, lam_2)-> ... -> mu_r = nu_r in FGMN coordinates, the GENTOW2 S2 dictionary at every level). Then, by induction on i < r:”

The index-0 scope, per the in-range acceptance fold (PE5-F-1), clause by clause:

> “[acceptance fold 2026-08-10 (PE5-F-1) — INDEX-0 SCOPE for (a)/(b)/(d), completing the post-PE4 rider's (c)/(e) scoping to the clause list. The blanket header's index i = 0 is claimed for (d) ONLY; (a) and (b), like (c) and (e), are claimed at induction indices i >= 1. Per clause, derived from this note's own displays: (a) at i = 0 is NOT claimed — its display dereferences w_0 = R_{1,kbar_0}(nhat_0(u_1)), and nhat_0 is not a DEF GENTOW5-1 object (the normalizer recursion bases at n1hat; nhat_i exists at i >= 1), so the twisted form is not well-formed at index 0. … (b) at i = 0 is NOT claimed by this proof (the (b)-cite enters through (a)'s certificate at the same index: Thm 6.3 consumes Phi_{i+1} in KP(nu_i) + prime, Cor 6.4 the non-equivalence step); its index-0 instance reduces to the j = 1 leg … (d) at i = 0 IS claimed and covered: its display is well-formed at index 0 (lift_1, dv_1, E_1 are DEF objects) and the instance is S1.4(ii)'s level-1 rider … The index-0 entry locus T_1 stays unclaimed per the (c) rider below; the PE5 fresh route instantiated it TRUE at one frame (f4 = Phi_1^2 - 25x over p = 5: level-0 read one side of kappa_1 = 1/2, residual (y-1)^2 = psi_1^2 mod 5, box at 5 = 2E_1 + 1 — gentow5_pe5_fresh.py, GREEN 40/0), so leaving it unclaimed costs the note nothing at the checked frame.]”

The fold also fixes how the header's own “keys built by THE RECIPE” reads:

> “Phi_1 := Phi' is the DEF-datum (S2.1 — so "keys Phi_1, ..., Phi_r built by THE RECIPE" reads honestly as Phi_2, ..., Phi_r recipe-built over the datum Phi_1; the recipe consumes nhat_i at i >= 1)”

**CONDITIONALITY:** Claimed index set by clause: (a) i ≥ 1; (b) i ≥ 1; (c) i ≥ 1; (d) i ≥ 0; (e) i ≥ 1. All clauses read at the gauge-corrected recipe. Out of range, S12.1 adds the `[GENTOW5-W(i)]` conditionality at every index n ≥ 3 for (a), (b), (c), (e).

**DERIVATION:** The fold's per-clause derivations are quoted above (well-formedness of the index-0 display for each clause, and where the index-0 content instead lives — the accepted T(b)′ datum and the GENTOW2 S2 dictionary).

**RESOLUTION TRACE:** Base §S3 statement header, lines 731–742, with `[GT5-r1]`'s gauge clause inline; the index-0 scope is the post-PE5 `[acceptance fold]` at lines 744–779, itself completing the post-PE4 `[rider]` scoping of (c)/(e) at lines 864–880.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:S2` — grep-verified count **15**; the MacLane-chain dictionary consumed at every level.

**TEETH:** `gentow5_pe5_fresh.py` (GREEN 40/0) instantiates the unclaimed T_1 case TRUE at one frame; FR-1 is the counter-instance for the gauge clause.

---

### EFF.GENTOW5.27  [lemma]

**CANONICAL STATEMENT:** THEOREM GENTOW5-B clause (a) — KEY CERTIFICATE, at the `[GT5-r2]` re-scope

> “(a) [KEY CERTIFICATE, level-general — GT5-r2 RE-SCOPED (PE2 F-1): the realized residual is the w-TWISTED form] Phi_{i+1} is a key polynomial for nu_i and a PRIME polynomial (monic, O-coefficients, irreducible over K_v), with
>
>     R_{nu_i}(Phi_{i+1}) = psi_{i+1}^{(w_i)}
>                         := w_i^{f_{i+1}} * psi_{i+1}(y / w_i),
>
> where w_i := R_{i+1,kbar_i}(nhat_i(u_{i+1})) in K_i^x is the single slot-independent CROSS-FRAME UNIT of the landed GENTOW2 r3 B-law (kbar_i := u_{i+1}/e(mu_i), the top slot's grade; at i = 2 this is LEMMA GENTOW2-B [r3 RESTATED] + LEMMA GENTOW2-B'''s w verbatim, GENTOW2_PROOF S5 @ d798529). psi_{i+1}^{(w_i)} is GENTOW2-A-ADMISSIBLE at each value of w_i — monic irreducible of degree f_{i+1} with nonzero constant term (y -> w*y is a substitution automorphism; B'' + the PE5 verification "psi_3^{(w)} is verifiably admissible for every w in K_2^x", GENTOW2_passPE5_report @ 75923bc) — and GENTOW2-A's hypothesis (ii) quantifier accepts it … THE w_i = 1 CASE IS OPEN: w_i is the uncomputed cross-frame unit ("not computed anywhere in the corpus" — GENTOW2 S5), and verdict-level machine data is w-blind, so no committed run discriminates it; R_{nu_i}(Phi_{i+1}) = psi_{i+1} on the nose is NOT claimed.”

with the in-range dated measurement note:

> “[DATED NOTE (2026-08-10, post-GENTOW2-PE6): GENTOW2's PE6 pass MEASURED w for the first time (fresh route GREEN 68/0, seal ade1727; report GENTOW2_passPE6_report.md @ deba21b, GENTOW2 ACCEPTED 2/2 there): w-avatar = z_1 (LD1), z_1^2 (LD3), z_2^2 (GA1), z_2 (GA3) — != 1 at each of the 6 measured primes across the 4 frames, and u_3-DEPENDENT within each tower. On the measured record the open w_i = 1 case is NOT the generic one: the psi^{(w)} form of this clause is the operative one. The quoted "not computed anywhere in the corpus" is dated by GENTOW2's post-PE6 acceptance record — measured at 4 frames; the closed-form letter derivation of w stays open, and the measured record does not decide w_i at unmeasured frames or levels i > 2.]”

and the clause's own w-blindness list:

> “sigma, values, degrees, irreducibility, and the REPO-side residue classes are w-blind — checked per consumer in the [GT5-r2] walk after (e).”

**CONDITIONALITY — three regimes, after the out-of-range appends.** S11.3 corrects the i = 1 instance:

> “Dated statement correction (honest re-scope, standing authority): clause (a) AT i = 1 reads
>
>     R_{nu_1}(Phi_2) = psi_2^{(u1)},  u1 in K_1^x a FIXED
>     z_1-letter-power unit (the letter formula's species);
>     the tie u1 = w_1 = R_{2,kbar_1}(nhat_1(u_2)) is OPEN.”

S11.2 fences i ≥ 3 behind the open lemma:

> “NOT PROVED at i >= 3: the single-w geometric form
>
>       [GENTOW5-W(i)]   u_i(beta_t) = theta_i(t) * w_i^{f_{i+1}-t},
>                        w_i = R_{i+1,kbar_i}(nhat_i(u_{i+1})),
>
>   which per-grade fixedness underdetermines (fixed families exist that fit no single w) — this is GENTOW2-B'''s computation run at level i, which this note does not reproduce. [GENTOW5-W(i)] is hereby an OPEN transported lemma, the honest-sorry analogue.”

S11.3's own summary of the three regimes:

> “Net position after S11.2 + S11.3: the pinned-w_i form is unconditionally realized at i = 2 exactly; at i = 1 the shape is proved with the tie open; at i >= 3 the form is open behind [GENTOW5-W(i)].”

S12.1 adds that at n ≥ 3 the certificate legs go with it: “Without \([{\rm GENTOW5\!-\!W}(n)]\), per-grade fixedness supplies no single substitution \(y\mapsto w_ny\), so none of those certificate legs is established for the pinned key.”

**DERIVATION:** [ASSEMBLED — the (B-1)/(B-2) legs and the FGMN certificate run, quoted] The proof opens by naming GENTOW2's level-uniformity proviso:

> “*(a) — GENTOW2-A's proof with r+1 for 4.* GENTOW2 S7 already recorded that THEOREM GENTOW2-A's proof pattern is level-uniform ("Cor 6.4 is proved for chains of any length r, and the recipe/bridge argument reads verbatim with r+1 in place of 4 PROVIDED the level-r analogues of (B-1)/(B-2) are proved"). The two provisos are now supplied:”

(B-1):

> “  (B-1 at level i) the dv_i ladder value of a deg < D_i ladder element equals its mu_i-value — this is LEMMA GENTOW5-C's (SLOT_i) value clause (exactness of the slot minimum), which identifies the grid minimum with the inductive-valuation value on deg < D_i polynomials at level-i points; at i <= 2 it is the accepted GENHN-2/2'.”

(B-2), at the landed GENTOW2 r3 B-law, with the cancellation computation that produces the surviving w-leg:

> “      u_i(beta_t) = theta_i(t) * w_i^{f_{i+1}-t},
>       theta_i(t) := res(nhat_i(u_{i+1}(f_{i+1}-t)) /
>                         nhat_i(u_{i+1})^{f_{i+1}-t}),
>       w_i := R_{i+1,kbar_i}(nhat_i(u_{i+1})) in K_i^x,
>
>   and theta_i(t) = vartheta_{i,f_{i+1}-t}^{-1} — the definitions are RECIPROCAL (S2.1's vartheta_{i,s} = res(nhat_i(u)^s / nhat_i(su)); same monomial quotient, inverse read). At the S2.1-pinned digit string — the statement's OWN keys, coherent digit c_t * vartheta_{i,f_{i+1}-t} — the B-law residual coefficient at y^t is therefore
>
>       u_i(beta_t) * (c_t * vartheta_{i,f_{i+1}-t})
>         = theta_i(t) * w_i^{f_{i+1}-t} * c_t * theta_i(t)^{-1}
>         = c_t * w_i^{f_{i+1}-t},
>
>   i.e. R_{nu_i}(Phi_{i+1}) = y^{f_{i+1}} - Sum_t c_t w_i^{f_{i+1}-t} y^t = w_i^{f_{i+1}} psi_{i+1}(y/w_i) = psi_{i+1}^{(w_i)}: the vartheta twist cancels the theta LEG ONLY; the w-leg SURVIVES.”

with the honesty fence attached to it:

> “Honest conditionality, named: what is consumed is the landed cocycle law (measured to its theta leg at PE4's decode 14/0 and derived as B''), never B-2 on-the-nose (u = 1), which is FALSE at letter-live grades; the w-leg is UNMEASURED (w-blind verdict data) and w_i = 1 is OPEN. (The alternative prescription c_t -> u_i(beta_t)^{-1}c_t would realize psi_{i+1} on the nose but builds a DIFFERENT key from the pinned recipe, and w_i being uncomputed it is not repo-constructible; the statement stays at the pinned key and the twisted residual.)”

and the certificate run itself:

> “With (B-1)/(B-2 as corrected), LEMMA GENTOW2-B's proof runs at level i on the pinned prescription: additivity (Cor 4.7(1) [Q8]) + eq (14) [Q7] give R_{nu_i}(Phi_{i+1}) = y^{f_{i+1}} - Sum c_t w_i^{f_{i+1}-t} y^t = psi_{i+1}^{(w_i)} as displayed; the degree-forcing display [Q6] + Lemma 5.3(2) [Q4] certify Phi_{i+1} in KP(nu_i) (admissibility of psi^{(w)} at each w — the statement's (a) clause); Lemma 1.11 [Q1] + Cor 1.13 [Q2] give prime. Non-equivalence to the previous key: R(Phi_{i+1}) = psi_{i+1}^{(w_i)} != 1 = R(Phi_i) by eq (14), Prop 5.7 [Q7]. ∎(a)”

The i = 1 line of the two level lists is supplied by the in-range acceptance fold (PE5-F-2), whose own disclaimer is what S11.3 then makes the statement's:

> “an exponent-level tie of the w_1 display to the letter formula is NOT claimed (no consumer on the record read needs it).”

**RESOLUTION TRACE:** Base §S3(a) statement (lines 781–820) and proof (lines 894–1003), rewritten by `[GT5-r1]` (F-2, the deleted `y -> eps*y` fallback), re-scoped by `[GT5-r2]` (PE2 F-1) at the landed GENTOW2 r3 law, dated by `[GT5-r3]` (PE3 F-2) at the measured record, completed at i = 1 by the post-PE5 `[acceptance fold]`; then corrected out of range by S11.2 (i ≥ 3 fence), S11.3 (i = 1 re-scope) and S12.1 (certificate legs conditional at n ≥ 3).

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B″` — grep-verified count **10** (Unicode double prime; GENTOW5's ASCII `LEMMA GENTOW2-B''` has count **1** in GENTOW2_PROOF — see `.03`'s reading note).

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B′` — grep-verified count **8**; the B′(3)/(5) per-grade-unit law the r1 discharge consumed.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:S5.1` — grep-verified count **42**; the letter formula and the u(beta) definition.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:S7` — grep-verified count **1**; the level-uniformity proviso quoted verbatim above.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:[Q7]` — grep-verified count **9** (Prop 5.7 + eq (14)); `[Q6]` — count **4**; `[Q4]` — count **5** (Lemma 5.3); `[Q1]` — count **4** (Lemma 1.11); `[Q2]` — count **4** (Cor 1.13); `[Q8]` — count **8** (Cor 4.7).

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:Def 3.16` — grep-verified count **3**; the epsilon-normalized coordinate the u_i-family compares against.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:Lemma 3.17` — grep-verified count **7**; consumed in the B′(3) derivation.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:Cor 5.6` — grep-verified count **6**; the i = 1 fold's FGMN residual identification.

**TEETH:** PE1 fresh FR-1 (corrected vs gauge-naive key); GENTOW2 PE4 `@ 2f95be6` (B-2 on-the-nose machine-REFUTED at letter-live grades); GENTOW2 PE6 (w measured ≠ 1 at 6 primes / 4 frames); GENTOW2 PE5 `@ 75923bc` (admissibility of `psi_3^{(w)}` for every w).

---

### EFF.GENTOW5.28  [lemma]

**CANONICAL STATEMENT:** THEOREM GENTOW5-B clause (b) — ONE-SIDEDNESS AT EVERY LEVEL

> “(b) [ONE-SIDEDNESS AT EVERY LEVEL — the FGMN cite, arbitrary chain length] for every j <= i+1, the level-(j-1) polygon N_j(Phi_{i+1}) is one-sided of slope -lam_j with residual R_{j-1}(Phi_{i+1}) = psi_{j-1}^{l_j ... l_{i+1}}, and every root xi of Phi_{i+1} has the EXACT intermediate values v(Phi_{j-1}(xi)) = u_j / ehat_j — i.e. xi in P_{i+1}: the recipe's roots ARE depth-(i+1) node points.”

> “[GT5-r2 rider (PE2 F-1(iii)): each psi in the residual display reads at ITS level's twisted form per the re-scoped (a) — the FGMN residual powers inherit the per-level w-twists (psi^{(w)}-powers). The exact-value clause and the P_{i+1} clause are w-blind: P_{i+1} is defined by REPO residue classes, and the FGMN class is w times the repo class (B''), so a psi^{(w)}-root FGMN-side IS a psi-root repo-side — FR-A's machine leg carried psi_3 exactly repo-side.]”

**Superseded residual display (quoted; corrected out of range).** S11.5 `[A-F5]`:

> “Dated bracket on the statement's (b): the residual display "R_{j-1}(Phi_{i+1}) = psi_{j-1}^{l_j ... l_{i+1}}" dereferences psi_0 at j = 1 and fails the residual-degree count. Corrected, in this note's stage numbering:
>
>     R_{j-1}(Phi_{i+1}) = psi_j^{l_{j+1} ... l_{i+1}}
>     (1 <= j <= i+1; empty product = 1 at j = i+1),”

S12.1 then attaches the per-level twist, and the post-D3i corrigendum fixes the twist's index:

> “\[ R_{j-1}(\Phi_{n+1}) =\bigl(\psi_j^{(\omega_j)}\bigr)^{\,l_{j+1}\cdots l_{n+1}} \qquad(1\le j\le n+1), \]”

> “read every ψ_j^{(ω_j)} in S12.1's clause (b) as ψ_j^{(ω_{j−1})} with ω₁ = the S11.3 unit (the outer ψ₁ leg handled separately as accepted). The display as first written demanded w_{n+1} at the top term, exceeding the assumed 𝒲_{≤n}.”

**CONDITIONALITY:** At i = 2 unconditional (landed GENTOW2 law); at n ≥ 3 **all** of clause (b) is conditional on `𝒲_{≤n} := ⋀_{3≤q≤n}[GENTOW5-W(q)]`, S12.1 having withdrawn S11.2's contrary claim:

> “but its subsequent assertion that exact values, repo-side residue classes, \(P\)-membership, clause (c), and clause (e) remain unconditional is WITHDRAWN. A fixed per-grade unit family is not enough: “\(w\)-blind” means invariance AFTER the family has been proved to have the single-\(w_i\) geometric form. It does not construct that form.”

> “Corollary 6.4 fires only after clause (a) has supplied the key-polynomial/prime certificate for \(\Phi_{n+1}\).”

**DERIVATION:** Quoted proof:

> “*(b) — the cite fires at arbitrary r.* Theorem 6.3 [Q9] with F = phi = Phi_{i+1}, mu = nu_i (F = phi so phi |_mu F); Corollary 6.4 [Q10] with the length-(i+1) chain: its quantifier is "for any 1 <= j <= r" — THE ONE-SIDEDNESS IS LEVEL-GENERAL IN THE SOURCE; no per-level work remains. Its display (23) gives the residual powers R_{j-1}(F) = psi_{j-1}^{l_j...} and the middle clause mu(phi_j) = v(phi_j(theta)) gives the exact intermediate values at every root — with the psi_{j}-root residue classes from the residual power (no root besides psi_j's, the GENTOW2-A consumption note verbatim), every root lies in P_{i+1}. [GT5-r2: with the re-scope the FGMN residual powers are psi^{(w)}-powers, whose roots are w times the psi-roots; the repo transport divides by that w (B''), so the P_{i+1} membership — a REPO-class condition — is as stated. Statement rider + consumer walk below.] The repo polygon = FGMN polygon under the S2 shear (GENTOW2 S2, level-general as an affine map per level). ∎(b)”

S11.5's re-derivation of the corrected index (out of range, but it is the derivation of the effective display):

> “re-derived from the note's own rows: the level-(j-1) polygon of Phi_{i+1} has length l_j...l_{i+1}, and one full side of slope lam_j (gcd(u_j, e_j) = 1) carries residual degree l_j...l_{i+1}/e_j = f_j * l_{j+1}...l_{i+1} = deg of the corrected display (the composed display's degree f_{j-1}*l_j...l_{i+1} fails this count)”

**RESOLUTION TRACE:** Base §S3(b) statement (lines 821–833) and proof (lines 1005–1020); rider by `[GT5-r2]`; residual display re-indexed by S11.5; twist attached by S12.1 and re-indexed by the post-D3i corrigendum; conditionality set by S12.1 item 2.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:[Q9]` — grep-verified count **4**; FGMN Theorem 6.3.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:[Q10]` — grep-verified count **6**; FGMN Corollary 6.4. **Source-display check:** the `[Q10]` quote block prints display (23) as “R_{i−1}(F) = (ψ_{i−1})^{ℓ_i}”, confirming S11.5's diagnosis that the base display transcribed the source's own index convention rather than this note's stage numbering.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:(23)` — grep-verified count **4**.

**TEETH:** §S4.2's P-B3 (10 polygons one-sided with on-chord support exactly the char-2 binomial spots) and §S5's P-B3 verdict row; FR-A's repo-side `psi_3` class row.

---

### EFF.GENTOW5.29  [lemma]

**CANONICAL STATEMENT:** THEOREM GENTOW5-B clause (c) — BUDGETS AT LEVEL i+1, at the `[GT5-r3]` RE-INDEXING

> “(c) [BUDGETS AT LEVEL i+1 — GENTOW-1 re-based. GT5-r3 RE-INDEXED (PE3 F-1): the composed display paired these (i+1)-anchored degree/weight/pin/floor clauses with an (i+2)-anchored entry-read clause ("level-(i+1) read, slope kappa_{i+2}, residual psi_{i+2}^{mu}"). That pairing fails the residual-degree count … and is refuted at the committed witness rows P-B3 f32@Phi4 and Phi4@Phi3 … The read clause below is the uniform GENTOW-1 transport 2 -> i+1 …] the level-(i+1) tower-entry locus T_{i+1} (monic f of degree n = mu * D_{i+1} whose level-i stage read exhibits the full side of slope kappa_{i+1} := u_{i+1}/e_{i+1} with residual psi_{i+1}^{mu} — the Phi_i-adic polygon of length mu * l_{i+1}, one side, residual degree mu*l_{i+1}/e_{i+1} = mu*f_{i+1} = deg psi_{i+1}^{mu}) is weight-characterized: f in T_{i+1} iff every slot of f - Phi_{i+1}^{mu} clears weight mu*E_{i+1} + 1, with the per-slot digit floors, the fibration, the node pins p_j >= (mu-j)E_{i+1} + 1, and the field floor dv_{i+1}(Phi_{i+1}(xi)) > E_{i+1}, exactly as in LEMMA GENTOW-1 (a)-(d).”

with the post-PE4 index scope:

> “[rider (post-PE4, 2026-08-10; PE4-F-1): SCOPE — clause (c), and clause (e) whose proof consumes (c)'s pins at the same index, are claimed at induction indices i >= 1 only (the entry loci T_2, ..., T_r): the proof's base is GENTOW-1 = the index-1 instance and each step enters at Phi_{i+2} (proving index i+1 from index-i data, i = 1..r-2), so the blanket header's index 0 is not covered and is NOT claimed. … Left unclaimed rather than cited.]”

**CONDITIONALITY:** Index `i >= 1` only. At n ≥ 3 conditional on `𝒲_{≤n}` (S12.1 item 3): “Thus clause (c) at index \(n\ge3\), including its sufficiency direction, deeper-read ascent, fibration, node pins, and field-floor conclusion, is conditional on \(\mathcal W_{\le n}\).”

**DERIVATION:** Quoted proof (the substitution table plus the five audited steps), with the r3 anchoring note:

> “*(c) — GENTOW-1's Steps 0-5 with the substitution table (D', e2, u2, E2, GENHN-2') -> (D_{i+1} composition data, e_{i+2}, u_{i+2}, E_{i+2}, (SLOT_{i+1})). [GT5-r3 (PE3 F-1): the table and the step displays below sit at ONE anchoring — the entered stage Phi_{i+2} (the composed table's garbled "E_{i+1} -> E_{i+2}" entry resolved to E_{i+2}). At that anchoring they prove the re-indexed statement (c) AT INDEX i+1 … with GENTOW-1 as the index-1 instance verbatim, indices 1..r-1 are covered.]*”

> “  Step 0 = LEMMA GENTOW5-D (proved level-agnostic; the ONLY level-sensitive content was the carry pricing, now uniform).
>   Step 1 (the key power's own development): R_{nu}(Phi_{i+2}^{mu}) = psi_{i+2}^{mu} by multiplicativity Cor 4.7(3) [Q8] — cleaner than the level-2 hand display; slots at weight >= mu*E_{i+2} with the graded layer psi-power by (b) + LEMMA GENTOW5-D's grid translation.
>   Step 2 (realizability): digits above floors put every slot of g := f - Phi_{i+2}^{mu}… above the side; the level-(i+1) stage read then shows the full side with residual psi^{mu} exactly ((SLOT_{i+1}) + Step 1). THE DEEPER READS: rather than the level-2 x-polygon display, run the entry ladder bottom-up: at level j (j <= i), given xi forced to P_j, the level-j read of f has pins = Phi_{i+2}^{mu}'s (g strictly above, by GENTOW5-D both grids agree on "above"), whose side residual is the psi_j-power of (b)+Cor 4.7(3); the zero-sum 0 = f(xi) forces the level-j side polynomial to vanish at the next residue class, i.e. the class is a psi_j-root: xi in P_{j+1}. Induction up to j = i+1, then Thm 6.3 fires on each prime factor (v(Phi_{i+1}(theta)) > nu(Phi_{i+1}) read off the top side) and Cor 6.4 pins the factor's data. [This replaces GENTOW-1 Step 2's outer-grammar display, which does not transpose as one line; the ladder argument is the classical Ore/Montes ascent and each rung is one (SLOT_j) read.]
>   Step 3 (necessity + fibration): verbatim — lattice-digit cancellation to one digit higher, off-lattice strictly above, Step 0 conversion, triangularity via monic division unipotent in the x-filtration (a composition of i+2 monic divisions now — the same unipotence).
>   Step 4 (node): (SLOT_{i+1}) reads p_j as the slot-min; equality realized in every residue class mod ehat_{i+2} by the ITERATED class separation (the CRT solve now runs down the recursion: choose b_{i+1} mod e_{i+2}, then descend — DEF GENTOW5-1's uniqueness clause).
>   Step 5 (field floor): every recipe side term at dv-height E_{i+2} exactly, common coherent normalizer, residue assembles to (unit)*psi_{i+2}(class) = 0, ultrametric strict — verbatim with the S1.2 cocycle in place of the level-2 wraps. ∎(c)”

**Superseded step (quoted; corrected out of range).** S11.1 identifies Step 2's parenthetical as the broken consumption of the withdrawn two-directional closure:

> “* S3(c) Step 2's parenthetical "(g strictly above, by GENTOW5-D both grids agree on 'above')" — THE BROKEN CONSUMPTION (the deeper reads at level j <= i sit across interior rungs, where the grids do NOT agree). Superseded by the derivation S11.1.1-S11.1.3; the ladder's conclusion stands on the new route.”

**Effective reading:** Step 2's aboveness is re-derived one-directionally through S11.1.1 (descent floor), S11.1.2 (the rho-ladder = the floor chain) and S11.1.3 (aboveness), all homed in shard 2; Step 1 and Step 3's necessity leg survive as written (S11.1's consumption walk).

**RESOLUTION TRACE:** Base §S3(c) statement (lines 834–880) and proof (lines 1022–1075), re-indexed by `[GT5-r3]` (PE3 F-1) and scoped by the post-PE4 `[rider]`; Step 2 superseded by S11.1; conditionality set by S12.1 item 3.

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:LEMMA GENTOW-1` — grep-verified count **7**; the index-1 instance the transport re-bases.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:[Q8]` — grep-verified count **8**; Cor 4.7(3) multiplicativity at Step 1 (clause (3) verified at the quote block, see `.07`).

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:Theorem 6.3` — grep-verified count **5**; fired on each prime factor at Step 2.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:Cor 6.4` — grep-verified count **11**; pins the factor's data at Step 2.

**TEETH:** §S4.2/§S5's P-B3 rows: `f32@Phi4` and `Phi4@Phi3` REFUTE the retired (i+2)-pairing; `f32@Phi3` and `Phi4@Phi2` VERIFY the corrected pairing (both re-derived by hand at S9 and machine-checked at the post-PE4 rider's `gentow5_rider_f32dev.py`, 7 checks / 0 violations).

---

### EFF.GENTOW5.30  [lemma]

**CANONICAL STATEMENT:** THEOREM GENTOW5-B clause (d) — REFINE TRANSFER AT LEVEL i+1, GENERAL mu

> “(d) [REFINE TRANSFER AT LEVEL i+1, GENERAL mu] at a composed event of integer dv_{i+1}-slope lam > E_{i+1} with residual (T-s)^{mu} (multiplicative convention), the refine Phi_{i+1}+ := Phi_{i+1} - lift_{i+1}(s; lam) kills the mu pins and bijects onto the lam-floored node — THEOREM GENTOW5-A's statement with 2 -> i+1.”

**CONDITIONALITY:** Claimed at index i ≥ 0 (the only clause the PE5 fold claims at index 0, discharged there by `.12`'s level-1 rider). S12.1's unaffected-scope sentence keeps it out of the `[GENTOW5-W(i)]` chain: “LEMMAS GENTOW5-A0/A1, the refine-transfer clause (d) at its stated event hypotheses, … remain unaffected.” Its lift is in range by S12.2: “THEOREM GENTOW5-A and clause (d)'s refine lifts also land in their required ranges”, since `λ > E_{i+1} > bound_{i+1}`.

**DERIVATION:** Quoted proof:

> “*(d)* — S1's proof is level-blind: LEMMA GENTOW5-A0 holds at any leaf field; LEMMA GENTOW5-A1's cocycle computation is S2.3's step (3) (the tau_i letter monomial); layer 2 = LEMMA GENTOW5-D + the flow-up pricing lam > E_{i+1} (the floor); layer 3 as in GENTOW-2. ∎(d)”

**RESOLUTION TRACE:** Base §S3(d) statement (lines 881–885) and proof (lines 1076–1080); index-0 coverage by the post-PE5 `[acceptance fold]`; lift-range discharge by S12.2.

**TEETH:** §S5's P-A1/A2/A3 (the pointwise mu2 = 3 kills at the composed key) are the i = 1 instances of this clause's mechanism.

---

### EFF.GENTOW5.31  [lemma]

**CANONICAL STATEMENT:** THEOREM GENTOW5-B clause (e) — NODE-FLOOR COROLLARY

> “(e) [NODE-FLOOR COROLLARY = the floor chain's provenance] every side of the level-(i+1) composed polygon of an f in T_{i+1} has dv-slope > E_{i+1} > dv_{i+1}(x^{D_{i+1}}); hence the NEXT stage's height obeys u_{i+2} > e_{i+2} E_{i+1} automatically at tower leaves — the induction feeds itself (COR GENTOW-1.1 at every level).”

**CONDITIONALITY:** Index i ≥ 1 (the post-PE4 rider scopes (e) with (c)). At n ≥ 3 conditional on `𝒲_{≤n}` (S12.1 item 4), with the explicit carve-out that the inequality may still be used unconditionally when it is part of the fixed tower datum — only its *automatic derivation* is conditional.

**DERIVATION:** Quoted proof:

> “*(e)* — COR GENTOW-1.1's two-line convexity argument with E_2 -> E_{i+1}: pins >= (mu-j)E_{i+1} + 1 with right endpoint (mu, 0) force every side slope > E_{i+1}; and E_{i+1} = e_{i+1}f_{i+1} u_{i+1} > e_{i+1}f_{i+1} e_{i+1} E_i >= dv_{i+1}(x^{D_{i+1}}) = D_{i+1} * (ehat_{i+1}/e1) h by telescoping the floor chain down to E_1 = D_1 h. ∎(e)”

**RESOLUTION TRACE:** Base §S3(e) statement (lines 886–890) and proof (lines 1081–1086); scoped with (c) by the post-PE4 `[rider]`; conditionality set by S12.1 item 4. Re-verified at `[GT5-r3]`: “(e) consumes the pins + box at E_{i+1} (the sound half) and its conclusion u_{i+2} > e_{i+2}E_{i+1} matches DEF GENTOW5-1's floor-chain provenance one index down”.

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:COR GENTOW-1.1` — grep-verified count **4**; the two-line convexity argument transported.

**TEETH:** §S5's P-B1/B2 (“floor chain tight (u = 5, 21, 85, 341)”).

---

### EFF.GENTOW5.32  [changes-record]

**CANONICAL STATEMENT:** `[GT5-r2]` THE RE-SCOPE'S CONSUMER WALK

> “**[GT5-r2] THE RE-SCOPE'S CONSUMER WALK (PE2 F-1 ripple — checked per consumer, no blanket claim).** Consumers of (a)/(b) inside this note, each read against the twisted residual psi^{(w_i)}:
> * (b)'s cite legs (Thm 6.3 [Q9] / Cor 6.4 [Q10]): consume Phi_{i+1} in KP(nu_i) + prime + the chain data — an ADMISSIBLE residual suffices (the (a) admissibility clause); the residual DISPLAYS inherit the per-level twists — carried by the (b) rider, no on-the-nose psi identification consumed.
> * (b)'s P_{i+1} clause: a REPO-class condition; FGMN class = w * repo class (B''), so it reads THROUGH the twist unchanged. Machine leg: FR-A's corrected key carried the psi_3-class repo-side exactly (gentow5_pe2_fresh.py, 22/0).
> * (c)'s budgets: T_{i+1} is DEFINED by the repo stage read (multiplicative convention) — weights, digit floors, fibration, node pins, field floor are value/repo-class data. Step 1's FGMN read becomes R_{nu}(Phi_{i+2}^{mu}) = (psi_{i+2}^{(w_{i+1})})^{mu} (Cor 4.7(3)); its repo-side translation is psi_{i+2}^{mu} by the SAME per-grade w-dictionary applied at the power — the repo-side clauses of (c) are w-blind. Step 2's ladder ascent consumes repo-side (SLOT_j) reads; w never enters.
> * (d)'s refine transfer: THEOREM GENTOW5-A is stated and proved in the multiplicative (repo) convention throughout — w-free.
> * (e)'s node floor: value arithmetic only — w-blind.
> * The S4 witness: K_i = F_2 at each rung, so K_i^x = {1} and w_i = 1 trivially — the witness does not discriminate the w-leg (its w-triviality is recorded at S6's TARGET-2 bullet's [GT5-r2] rider; the coverage box tracks the SEAM axis — S4.1's re-check — and carries no w row) [GT5-r3 pointer corrected, PE3 F-3].
> * sigma / degrees / irreducibility / factor patterns: y -> w*y is a substitution automorphism of K_i[y], factor patterns preserved at each w (B''; PE5's admissibility verification) — w-blind.
> * External consumers: none executed (S6's consumption path is candidates only); any future consumption of (a)/(b) must ride the w-annotation.”

**CONDITIONALITY — the walk's w-blindness verdicts are PARTIALLY WITHDRAWN out of range.** S12.1 states the distinction that breaks them at n ≥ 3:

> “A fixed per-grade unit family is not enough: “\(w\)-blind” means invariance AFTER the family has been proved to have the single-\(w_i\) geometric form. It does not construct that form.”

**Effective reading:** the walk stands as written at i = 2 (landed law) and at the S4 witness (K_i^× = {1}, “each required geometric law is tautological there”). At n ≥ 3 the (b)/(c)/(e) rows are conditional on `𝒲_{≤n}`; the (d) row survives (S12.1's unaffected list), and the sigma/degree/irreducibility row survives only downstream of an established twist.

**DERIVATION:** Per-consumer audit, quoted above; each row cites the mechanism (repo-class definition, value arithmetic, substitution automorphism) that makes it w-blind.

**RESOLUTION TRACE:** Base §S3, lines 1088–1121, added by `[GT5-r2]` (PE2 F-1 ripple), one pointer corrected by `[GT5-r3]` (PE3 F-3); partially withdrawn by S12.1.

**TEETH:** FR-A (`gentow5_pe2_fresh.py`, 22/0); PE5's admissibility verification.

---

### EFF.GENTOW5.33  [scope-record]

**CANONICAL STATEMENT:** What the induction consumes, per rung (the honest pin stack)

> “**What the induction consumes, per rung (the honest pin stack).** Accepted 2/2: T(b)'(i)/(ii)/(iii) + GENHN-2/2' + S4 normalizers (rungs i <= 2). Cited at verified numbering: FGMN [Q1]-[Q10] (level-general by their own quantifiers; faithfulness per GENTOW2 S6, unchanged). Grade 0/2: GENTOW-1 (budgets pattern), GENTOW-2 (refine pattern), GENTOW2-A/B (cite pattern), THIS NOTE. HE7 ANNEX R's R1-b/R1-c ARGUMENT, consumed at rungs i >= 3 through LEMMA GENTOW5-C (the proof is reproduced tower-side, but its correctness precedent is the annex's — named, not hidden) [GT5-r1 dated fold: ACCEPTED 2/2 since a472155; see the S2.3 fold]. The depth->=4 region has machine contact ONLY through S4's witness (one exact instance) + HE7 R1.3's level-3 leg one ladder over; no count law at depth >= 3 is claimed measured.”

**CONDITIONALITY:** The “Grade 0/2 … THIS NOTE” row is superseded by the acceptance record (ACCEPTED 2/2); the grades of GENTOW-1/GENTOW-2/GENTOW2-A/B are their own notes' business and are not updated here.

**DERIVATION:** Inventory, not derivation.

**RESOLUTION TRACE:** Base §S3, lines 1123–1135; the annex-pin row folded by `[GT5-r1]`; this note's own grade superseded at lines 1671–1741.

XREF: `lean/notes/openmath/HE7_PROOF_2026-08-08.md:R1.3` — grep-verified count **5**; the level-3 machine leg named as the only other depth ≥ 3 contact.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:S6` — grep-verified count **25**; the FGMN faithfulness audit relied on for the cite row.

**NON-IMPORT (explicit):** “no count law at depth >= 3 is claimed measured.”

**TEETH:** S4's witness is the sole depth-4 machine contact (`.34`–`.36`).

---

### EFF.GENTOW5.34  [instance-record]

**CANONICAL STATEMENT:** §S4.1 The minimal chain (u_{i+1} = 4u_i + 1 — every floor tight)

> “q = 2, h = 1, all stages (e_i, f_i) = (2, 1), all psi_i = y - 1 (K_i = F_2 throughout — the minimal alphabet; properness l_i = 2). The floor chain u_{i+1} > e_{i+1}E_i = 4u_i admits the MINIMAL odd solutions u_{i+1} = 4u_i + 1 from u_1 = h = 1:
>
>     u = (1,) 5, 21, 85, 341;   E_i = 2u_i = (2,) 10, 42, 170;
>     dv_i = 2^i v;  D_i = 2^i.
>
> Keys by THE RECIPE (each khat = nhat_i(u_{i+1}), digit 1; S2.2's recursion solves):
>
>     Phi_1 = x^2 - 2
>     Phi_2 = Phi_1^2 - 4x            (nhat_1(5)  = 4x)
>     Phi_3 = Phi_2^2 - 16 Phi_1      (nhat_2(21) = 16 Phi_1)
>     Phi_4 = Phi_3^2 - 256 Phi_2     (nhat_3(85) = 256 Phi_2)
>
> (Phi_2, Phi_3 are the committed W1 objects of GENTOW2; Phi_4 is NEW — the first depth-4 key anywhere in the program.)”

> “The degree-32 member, one more tight rung (m\* = 4\*341/4... the top height m\* > e\*E_4 = 340, minimal odd 341 on dv_4):
>
>     f32 := Phi_4^2 - 2^16 Phi_3     (nhat_4(341) = 2^16 Phi_3),
>
> deg 32 = the first-live depth-4 degree (S2.1's arithmetic 2^{r+1}).”

**Seam re-check attached to the chain** (`[GT5-r1]`):

> “[GT5-r1 SEAM RE-CHECK (PE1 F-1's charge): this witness chain is GAUGE-SEAM-BLIND on two INDEPENDENT grounds — (i) K_i = F_2 at every level, so every letter (eta, beta_j) = 1 and vartheta is identically 1; (ii) every stage has f_{i+1} = 1, so the recipe's only slot is t = 0 with s = f - t = 1 and vartheta_{i,1} = 1 BY DEFINITION, letters notwithstanding. Corrected = naive khat at every rung; the displayed keys Phi_2/Phi_3/Phi_4 and f32 ARE the gauge-corrected recipe's outputs unchanged, and the committed sealed artifacts stand as-is. The witness therefore does not discriminate the seam — the seam-live machine leg is the PE1 fresh instrument's FR-1 frame, cited at the S2.1 pin.]”

**CONDITIONALITY:** One constructed chain, not a sweep. It is seam-blind (above) and w-trivial (`K_i^× = {1}`), so it discriminates neither the gauge seam nor the w-leg — both disclosed by the note and re-affirmed by S12.1 (“At S4 every \(K_i^\times=\{1\}\), so each required geometric law is tautological there”).

**DERIVATION:** The floor chain of `.14` forces `u_{i+1} > 4u_i`; the minimal odd solutions give the displayed ladder; the keys are `.18`'s recipe with digit 1 and the normalizers solved by `.15`/`.21`.

**RESOLUTION TRACE:** Base §S4.1, lines 1139–1175, with the `[GT5-r1]` seam re-check inserted at 1159–1169.

**RECORDED SOURCE DEFECT (not repaired by any later round):** the parenthetical “m\* = 4\*341/4...” is a truncated token in the source, of the same species as the `(LIFT_i)` bound's “e...” which PE5-F-3 restored. The sentence's conclusion is nevertheless complete and self-checking (`m* > e*E_4 = 340`, minimal odd `341`), and the value 341 is machine-confirmed at P-B4/P-C2. No repair is invented here.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:S5.1` — grep-verified count **42**; W1's committed Phi_2/Phi_3 objects live in the GENTOW2 witness stack.

**TEETH:** P-B1/B2 (floor chain tight); P-B4 and P-C2 (the two independent ladder routes); `genhnr2_supp.py` L387–389 independently carries `Phi3 = Phi2^2 - 16*Phi'` with `n2(21) = 16*Phi'`, matching `.21`.

---

### EFF.GENTOW5.35  [battery-frame]

**CANONICAL STATEMENT:** §S4.2 Preregistered predictions (sealed in the battery docstring)

> “By THEOREM GENTOW5-B (b)+(e) every root xi of f32 carries the EXACT ladder v(x) = 1/2, v(Phi_1) = 5/4, v(Phi_2) = 21/8, v(Phi_3) = 85/16, v(Phi_4) = 341/32; f32 is irreducible over Q_2 with e = 32, f = 1 (RAM leaf at the odd top height). Machine forms:
> * P-B4 (RESULTANT LADDER, exact-integer — the "nfeltval-only" route, PARI-free): v_2(Res(f32, g)) = 32\*v(g(xi)) for g = x, Phi_1, Phi_2, Phi_3, Phi_4 -> (16, 40, 84, 170, 341); and at the depth-4 KEY itself: v_2(Res(Phi_4, g)) -> (8, 20, 42, 85).
> * P-B3 (ONE-SIDEDNESS AT EVERY LEVEL — Cor 6.4's display, exact): the Phi_j-adic polygons of Phi_{i+1} and f32 are one-sided of the predicted slopes (5, 21, 85/2, 341/2 at the top reads; chords with on-chord support ONLY at the char-2-surviving binomial spots {0, l...}: e.g. Phi_1-adic Phi_4 on-chord at j in {0, 8} only, Phi_2-adic Phi_4 at j in {0, 4} only — (y+1)^{2^k} = y^{2^k}+1).
> * P-B1/B2 (grammar arithmetic): floor chain tight; every recipe side term at height E_{i+1} exactly.
> * P-C (PARI leg, DETACHED): factorpadic(f32, 2) returns ONE factor of degree 32; nfinit([f32,[2]]) + idealprimedec gives a single prime with (e, f) = (32, 1) and nfeltval ladder (16, 40, 84, 170, 341). Budgeted with timeout; infeasibility disclosed, not fatal.”

> “* T-B1 (tooth, the even-height mutant AT the node — STRONG FORM, hand-derived before the seal): f32m := Phi_4^2 - 2^20 Phi_1 (height 340 = 2\*E_4 exactly, gcd(340, 2) != 1). Derivation (pre-seal, disclosed): f32m = Phi_3^4 - 512 Phi_2 Phi_3^2 + 2^16(Phi_2^2 - 16 Phi_1) = Phi_3 \* (Phi_3^3 - 512 Phi_2 Phi_3 + 2^16) since Phi_2^2 - 16 Phi_1 = Phi_3 — the node-height digit hits the key relation exactly and the mutant COLLAPSES INTO THE DRAIN: Phi_3 | f32m over Z. Machine form: remainder(f32m, Phi_3) = 0, hence Res(f32m, Phi_3) = 0 (ladder entry infinite != 170) and the single-(e = 32)-factor read is refuted without PARI. The gcd != 1 proviso is machine-load-bearing at depth 4.”

**CONDITIONALITY:** Predictions are preregistered (sealed in the docstring before the first run, commit `4b279a7`); the PARI leg is detached and budgeted. The withdrawn over-claim about the PARI-free route's standalone strength is quoted at `.43` (F-6).

**DERIVATION:** The predicted ladder is clause (b)+(e) of THEOREM GENTOW5-B applied to the `.34` chain; the T-B1 derivation is the displayed exact factorization over `Z` using the key relation `Phi_2^2 - 16 Phi_1 = Phi_3`.

**RESOLUTION TRACE:** Base §S4.2, lines 1179–1219, with the `[GT5-r1]` F-6 wording correction inserted inside the P-C bullet.

**TEETH:** This unit IS the battery frame; its rows are inventoried in §5's inverse table.

---

### EFF.GENTOW5.36  [regression-record]

**CANONICAL STATEMENT:** §S4.3 Run record (VERDICT)

> “**GREEN on both routes.** Exact-integer route (P-B4, artifact `gentow5_output_exact.txt`): v2(Res(f32, g)) = (16, 40, 84, 170, 341) for g = (x, Phi_1, Phi_2, Phi_3, Phi_4) and v2(Res(Phi_4, g)) = (8, 20, 42, 85) — EXACT at the predicted rungs. PARI route (P-C, artifact `gentow5_output_full.txt`): factorpadic(f32, 2) = one degree-32 factor; nfinit([f32,[2]]) + idealprimedec = one prime with (e, f) = (32, 1); nfeltval ladder [16, 40, 84, 170, 341] EXACT. Polygon reads (P-B3): 10 polygons one-sided with on-chord support exactly the char-2 binomial spots, pin tables printed in the artifacts. T-B1 fired (drain collapse exact + `C4 nfactors=2 degs=[8, 24]`). **f32 = Phi_4^2 - 2^16 Phi_3 is the first depth-4 contact anywhere in the program: a degree-32, e = 32 witness whose four-rung intermediate ladder is exact on two independent routes.**”

**CONDITIONALITY:** One instance. Both artifacts are committed and byte-frozen at their md5s (`dc499a49…`, `839a8660…`).

**DERIVATION:** Run verdict, appended from the committed artifacts after the sealed run.

**RESOLUTION TRACE:** Base §S4.3, lines 1224–1236; untouched.

**TEETH:** This unit IS the verdict for P-B3/P-B4/P-C/T-B1.

---

### EFF.GENTOW5.37  [regression-record]

**CANONICAL STATEMENT:** §S5 MACHINE LEG (gentow5_checks.py, two-commit seal)

> “INSTRUMENT: `verification/openmath/gentow5_checks.py`, sealed at commit 4b279a7 (predictions P-A1..A4, T-A1W/T-A2W/T-A4W, P-B1..B4, T-B1, P-C1..C4 in the docstring BEFORE the first run; the T-B1 drain factorization and the A-row residual arithmetic were hand-derived pre-seal and disclosed in S4.2/S1.2). Run 1: 85/86 — the single flag was an instrument-wiring defect in T-A1W's survivor comparison (the predicted survivor (j=2, slotmin 10) WAS in the alive list; the check read the first list entry — the wrong-height refine also drags the j = 0, 1 coordinates below their event pins, which is additional tooth-firing). Repaired + disclosed in the docstring (committed before re-run); no prediction changed; no reader/kill logic touched. UNIT NOTE (disclosed): the f32@\* and Phi4@Phi3 polygon rows print one dv-scale above the canonical N_j normalization; one-sidedness and on-chord support are affine-invariant.”

> “VERDICT RUN (exact leg, artifact `gentow5_output_exact.txt`):
>
>     GREEN — 86 checks, 0 violations, exit 0.
>     * P-A1/A2/A3 mu2 = 3 KILLS: all three pins die at all three
>       frames (q = 2; q = 3 char-3; K2 = F4 two-flavor lift) — the
>       FIRST mu2 = 3 pointwise re-division transports at the composed
>       key anywhere in the program (GN-REFINE3 one level up).
>     * P-A4 live-twist mu2 = 2 kill: the vartheta_2-corrected member
>       dies; T-A4W THE CONVENTION TOOTH FIRED: the naive-digit twin
>       keeps its pin at 22 exactly — LEMMA GENTOW5-A1's fixed-unit
>       dictionary is machine-load-bearing, not decorative.
>     * T-A1W (wrong height) and T-A2W (wrong digit, char 3, surviving
>       pin 33 exactly) FIRED as predicted.
>     * P-B1/B2: floor chain tight (u = 5, 21, 85, 341), recipe side
>       heights (10, 42, 170) = (E2, E3, E4) and top event 341 exact.
>     * P-B3: 10 polygons (Phi2/Phi3/Phi4/f32 at every lower key)
>       one-sided with on-chord support EXACTLY the char-2 binomial
>       spots {0, L} — Cor 6.4's display verified at depth 4, incl.
>       the pin tables printed in the artifact.
>     * P-B4 THE RESULTANT LADDERS: v2(Res(f32, ·)) =
>       (16, 40, 84, 170, 341) and v2(Res(Phi4, ·)) = (8, 20, 42, 85)
>       EXACT — the depth-4 witness by the PARI-free integer route.
>     * T-B1 FIRED: Phi3 | f32m exactly (remainder 0, resultant 0) —
>       the even-height-at-node mutant collapses into the drain.”

> “**GREEN — full run 92 checks, 0 violations** (86 exact + 6 PARI; `grep -c VIOLATION` = 0).”

**CONDITIONALITY:** Instrument-strength disclosure inside the C3 lines (`[GT5-r1]`, PE1 F-5):

> “[GT5-r1 instrument-strength disclosure (PE1 F-5): the sealed chk lines machine-assert only `C3a nfactors=1` + a deg=4 occurrence and `C3b nfactors=1`; the e = 4 values (and C3b's deg) are PRINTED to the committed artifact and human-verified in the quoted lines here, not chk-asserted — the sealed runner is byte-frozen, so the gap is recorded rather than retro-patched; any future battery revision should assert e and deg on both rows]”

**DERIVATION:** Run record; the preregistration discipline (docstring sealed before first run) is the derivation of its evidential weight.

**RESOLUTION TRACE:** Base §S5, lines 1240–1302; the F-5 disclosure inserted by `[GT5-r1]`.

**TEETH:** This unit IS the battery of record (92 checks / 0 violations); the inverse mapping is §5 below.

---

### EFF.GENTOW5.38  [scope-record]

**CANONICAL STATEMENT:** §S6 — What this note PROVES

> “**What this note PROVES (grade 0/2, hostile arc owed):**
> * TARGET 1: THEOREM GENTOW5-A + LEMMAS GENTOW5-A0/A1 — LEMMA GENTOW-2 layer 1 at GENERAL mu2. GENTOW-BOX-1 is RETIRED as a mathematical box: the "composed graded frame" is gr(leaf field) (a graded division ring — elementary) + GENHN-2' (accepted) + the fixed-unit dictionary; no W-9-analogue weld face. Residue: this note's own arc grade; and the mu2 >= 3 machine rows are three constructed frames, not a sweep (GENTOW-BOX-2's coverage discipline applies to them verbatim).
> * TARGET 2: DEF GENTOW5-1 + LEMMAS GENTOW5-C/D + THEOREM GENTOW5-B — the level-r ladder grammar and the general-depth composition theorem, with the depth-4 witness EXACT on two independent routes. [GT5-r2: (a) holds at the TWISTED residual psi_{i+1}^{(w_i)} (GENTOW2-A-admissible at each w_i); w_i = 1 — the on-the-nose psi_{i+1} — is OPEN, the uncomputed cross-frame unit.] [GT5-r3 DATED 2026-08-10 (PE3 F-2): "uncomputed" is dated — w is MEASURED != 1 at the 7 measured primes (GENTOW2 PE6's 6 across LD1/LD3/GA1/GA3 + the PE3 fresh leg W's carrier-(8,4) prime at GA3\*, where psi_3^{(w)}(Y) = 0 held on the nose at w = z2); the closed-form w-law and unmeasured frames/levels stay open — see the S3(a) dated note.]”

**CONDITIONALITY:** “grade 0/2, hostile arc owed” is superseded by the acceptance record (**ACCEPTED 2/2**). The TARGET 2 supply is further narrowed out of range: at i ≥ 3 clauses (a)/(b)/(c)/(e) are conditional on `𝒲_{≤n}` (S12.1), at i = 1 clause (a) reads at S11.3's form.

**DERIVATION:** Supply inventory; each bullet's derivation is its named section.

**RESOLUTION TRACE:** Base §S6, lines 1306–1326, with the `[GT5-r2]` and `[GT5-r3]` brackets landed inline; grade superseded at lines 1671–1741; conditional narrowing at S11.2/S11.3/S12.1.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:COROLLARY W-9` — grep-verified count **3**; the twisted-algebra pin the note declares it does NOT need an analogue of.

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:GENTOW-BOX-2` — grep-verified count **2**; the coverage discipline imported for the three constructed frames.

**NON-IMPORT (explicit):** “no W-9-analogue weld face”.

**TEETH:** §S5's A-rows for TARGET 1; §S4/§S5's B-rows for TARGET 2.

---

### EFF.GENTOW5.39  [scope-record]

**CANONICAL STATEMENT:** §S6 — Named conditionality stack (per consumer)

> “**Named conditionality stack (per consumer):**
> * Accepted 2/2: LEMMA GENHN-T(b)'(i)/(ii)/(iii), GENHN-2/2', the S4 coherent normalizers, the [r1] node floor (= floor chain rung 1).
> * Cited at verified numbering: FGMN [Q1]-[Q10] via GENTOW2_PROOF S3 (Cor 6.4's level quantifier "for any 1 <= i <= r" carries the one-sidedness at every depth; faithfulness audit GENTOW2 S6).
> * Grade 0/2 (same campaign, hostile arcs owed): GENTOW-1, GENTOW-2 layers 2-3, GENTOW2-A/B, THIS NOTE.
> * HE7 ANNEX R's R1-a/R1-b/R1-c ARGUMENT — consumed at rungs i >= 3 through LEMMA GENTOW5-C (reproved tower-side, but the argument's precedent and its hostile scrutiny live in the annex). [GT5-r1 DATED FOLD 2026-08-10 (PE1 F-4; orchestrator-authorized, ledger B8 87a7b61): the annex stack is ACCEPTED 2/2 — annexpass CLEAN 1/2 (4a613d8), annexpass2 CLEAN "the annex stack is ACCEPTED 2/2" (a472155); the HETOW acceptance record (e38df9f) consumes it. The composition-time cap sentence ("THE GRADE CAP FOR DEPTH >= 3 CLAIMS IS THIS PIN plus this note's arc") is LIFTED to the acceptance grade on the annex leg: the remaining depth >= 3 grade cap is this note's own arc plus the campaign-0/2 notes it consumes (GENTOW-1/-2, GENTOW2-A/B) — the annex pin no longer caps below acceptance.]”

**CONDITIONALITY:** “THIS NOTE” at grade 0/2 is superseded (ACCEPTED 2/2). The other notes' grades are as recorded here and are not updated by this shard.

**DERIVATION:** Inventory.

**RESOLUTION TRACE:** Base §S6, lines 1328–1348; annex row folded by `[GT5-r1]`.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:LEMMA GENHN-T(b)` — grep-verified count **11**.

XREF: `lean/notes/openmath/HE7_PROOF_2026-08-08.md:ANNEX-LEMMA R1-a` — grep-verified count **6**.

**READING NOTE (external, not an edit).** The FGMN cite row is covered corpus-wide by `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` **NS-12**, whose verdict for the `[Q1]`–`[Q10]` inventory consumed by GENTOW2/GENTOW5 is **COVERS-ALL-O** — i.e. no retarget is needed for these cites (unlike the Ore/GMN rows handled elsewhere in that document).

**TEETH:** NONE (inventory).

---

### EFF.GENTOW5.40  [open-obligation]

**CANONICAL STATEMENT:** §S6 — Machine coverage (GENTOW5-BOX-A), the seam axis, and the compound row

> “* Machine coverage (GENTOW5-BOX-A): CHECK-A exercises mu2 in {2,3}, q in {2,3}, K2 in {F2, F3, F4}, e2 in {1,2}, f2 in {1,2}, d = 1, depth 2; CHECK-B exercises ONE depth-4 chain (all-(2,1) stages, q = 2, minimal heights). The proofs are uniform in the stage data; the coverage gap is machine-side, named here. The vartheta direction (theta vs theta^{-1}) is machine-tested only up to self-inverse units (F3; disclosed at T-A4W) — an F5-frame or F4-live-twist row would pin it; proof-side the direction is S1.2's derivation.”

> “[GT5-r1 THE SEAM AXIS (PE1 F-1's coverage finding — the axis this box omitted at composition): the committed battery is GAUGE-SEAM-BLIND BY CONSTRUCTION. CHECK-B is q = 2 with every f_i = 1 (vartheta trivialized twice over — S4.1 re-check); CHECK-A's only eta != 1 frame (A-2/A-4, p = 3, eta = 2) has f2 = 1, where W = 0 and naive = corrected. No committed row exercises the recipe at a letter-live frame with f_stage >= 2. The seam-live row that exists is the PE1 fresh instrument's FR-1 (gentow5_pe1_fresh.py + artifact @ 0160b94, 15/0: corrected key = carrier sigma (2,2) + exact ladder; naive key sigma {(4,1)} — the tooth). A letter-live recipe row inside this note's OWN battery remains a named gap (sealed runner byte-frozen; the fresh instrument is the current coverage).]”

> “[GT5-r2 THE COMPOUND ROW (PE2 F-4): seam-live x e_stage >= 2. The seam-live machine contact that exists is e-TRIVIAL at the live stage — FR-1 has e_2 = 1, and PE2's FR-A (the first seam-live depth-3 chain) has e_2 = e_3 = 1 — while the committed battery is seam-blind (above); the program's committed rows thus leave the compound (vartheta live x e_{i+1} >= 2) with NO machine contact. That compound is where the multiplicative slot convention reads THROUGH the mod-e_{i+1} class separation (S2.3 step (3)). Proof-side the S2.3 derivation is uniform in e_{i+1}; this row is a coverage fact — an honest named gap, coverage-box precision only.]”

**CONDITIONALITY:** These are declared *machine-side* gaps, not proof gaps: the note asserts the proofs are uniform in the stage data and locates the missing coverage precisely (letter-live × f_stage ≥ 2; letter-live × e_stage ≥ 2; the vartheta direction beyond self-inverse units).

**DERIVATION:** Coverage audit of the committed rows against the parameter axes.

**RESOLUTION TRACE:** Base §S6, lines 1349–1380, with the seam axis added by `[GT5-r1]` and the compound row by `[GT5-r2]`.

**TEETH:** This unit IS the note's honest teeth-coverage record; FR-1 and FR-A are its named partial coverage.

---

### EFF.GENTOW5.41  [open-obligation]

**CANONICAL STATEMENT:** §S6 — What stays OPEN (not claimed)

> “**What stays OPEN (not claimed):** tower COUNT laws at depth >= 3 (no ledger, no measurement); partial inner sides ([GENHN-TOW-1] item (4)) at every depth; the genre-general faithfulness geography (item (3)); sigma laws behind [GENHN-HE(mu >= 3)] wherever the top problem has mu >= 3 — none of these is touched by GENTOW5-B, which is a carrier/read/budget/refine theorem, not a density display.”

**CONDITIONALITY:** The list is the note's own negative claim set.

**DERIVATION:** Declaration.

**RESOLUTION TRACE:** Base §S6, lines 1382–1387; untouched.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:[GENHN-TOW-1]` — grep-verified count **19**; items (3) and (4) are named there.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:[GENHN-HE(μ ≥ 3)]` — grep-verified count **7** (Unicode form; GENTOW5's ASCII rendering `[GENHN-HE(mu >= 3)]` has count **0** in GENHN_PROOF — orthography, see `.03`).

**TEETH:** NONE (negative claim).

---

### EFF.GENTOW5.42  [scope-record]

**CANONICAL STATEMENT:** §S6 — Consumption path (not executed here)

> “**Consumption path (not executed here):** GENTOW1_PROOF's S3 grade note and S6 GENTOW-BOX-1, GENHN_PROOF's GENHN-BOX-2 and [GENHN-TOW-1] item (6) depth->=4 sentence, and GENTOW2_PROOF S7's depth->=4 bullet are candidates for the orchestrator's dated consumption updates after this note's own hostile arc; the four source notes are byte-untouched by this unit.”

**CONDITIONALITY:** This is the APPEND/consumption PROTOCOL predicate of the header's scope split. It asserts that **no** dated append had been landed on any source note by this unit; the four named targets are *candidates*.

**DERIVATION:** Declaration.

**RESOLUTION TRACE:** Base §S6, lines 1389–1394; untouched by S7–S12 (none of the later appends claims to land a consumption append on a source note).

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:GENTOW-BOX-1` — grep-verified count **5**; the candidate consumption site.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN-BOX-2` — grep-verified count **5**; likewise.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:S7` — grep-verified count **1**; the depth ≥ 4 bullet.

**TEETH:** NONE (protocol declaration).

---

### EFF.GENTOW5.43  [changes-record]

**CANONICAL STATEMENT:** §S7 `[GT5-r1]` PE1 REPAIR RECORD (2026-08-10, post-passPE1)

> “PE1 verdict (GENTOW5_passPE1_report.md @ 0160b94): NOT CLEAN — 1 CRITICAL (F-1) + 2 GAP (F-2, F-3) + 3 MINOR (F-4, F-5, F-6); counter stays 0/2. This section is the r1 repair round. Tag convention: this round's edits are marked [GT5-r1]; bare [r1] in the body refers, as composed, to GENHN-1's node-floor erratum. Sealed machine artifacts BYTE-FROZEN at their committed md5s (gentow5_checks.py 5fa684c7..., gentow5_output_exact.txt dc499a49..., gentow5_output_full.txt 839a8660...); no runner edited, no re-run. Pre-r1 note body md5 02deb7e0 (43,779 bytes = the 87a7b61-era file, the PE1 target state).”

The six items, each landing on an in-range unit:

> “* **F-1 (CRITICAL) -> REPAIRED at the S2.1 GAUGE PIN.** … Ripple pins: S3 statement (keys = corrected recipe), S2.4 (value-blind), S4.1 (witness seam-blind on two grounds), S6 coverage box (the seam axis added). No fresh frames composed: FR-1 suffices as the seam-live verification, per the charge.
> * **F-2 (GAP) -> REPAIRED in S3(a).** The y -> eps\*y fallback (deleted as false at its source, GENTOW2 r1 dd44d20) is replaced by GENTOW2-B'(3)/(5)'s per-grade-unit law with the re-parameterization discharge; B-2 on-the-nose is named machine-REFUTED at letter-live grades (GENTOW2 PE4 @ 2f95be6) and is NOT consumed. …
> * **F-3 (GAP) -> REPAIRED in S2.4.** Top-grid weight DEFINED (Phi_i at E_i); strict clause restricted to interior carries (rungs 1..i-1, in-datum); top carry priced PRESERVED — the i = 2 instance now matches GENTOW1 S2 Step 0 verbatim; grid-4 equality instance worked (170 = 170 = 170).
> * **F-4 (MINOR) -> FOLDED (orchestrator-authorized, ledger B8 87a7b61).** HE7 ANNEX R pin lifted to ACCEPTED 2/2 (4a613d8 -> a472155; HETOW acceptance e38df9f consumes it) at S2.3, the S3 pin stack, and the S6 cap sentence.
> * **F-5 (MINOR) -> DISCLOSED at S5's C3 lines** (chk asserts nfactors only; e/deg human-verified from the artifact; runner byte-frozen).
> * **F-6 (MINOR) -> WITHDRAWN at S4.2 P-C** (the "either way" clause; the as-run two-route record stands).”

F-2's mid-round update carries its own later correction, landed in place:

> “[GT5-r2 CORRECTION (PE2 F-1): the clause "consistent both ways; the S3(a) text stands as written" that closed this bullet was WRONG at the w-leg, as was the S3(a) in-flight pin's sentence (removed at the r2 rewrite there) "realizes psi_{i+1} with NO re-parameterization (its vartheta twist IS the u-family)": the vartheta twist cancels theta(t) ONLY, and the landed law's second leg w^{f_3-t} survives — at the pinned recipe the realized residual is psi_{i+1}^{(w_i)}, not psi_{i+1} (open unless w_i = 1, the uncomputed cross-frame unit). The PRECISE statement: (i) the landed u IS an instance of the per-grade x0-free family, so the r1 discharge's EXISTENCE leg stands; (ii) the r1 discharge's re-parameterized key is NOT the statement's pinned key (digits differ by w-powers), so (a) at the pinned key required the r2 re-scope to psi^{(w_i)} — S3(a) as rewritten this round.]”

> “Grade: 0/2 UNCHANGED (this is a repair round, not a pass); PE2 next. TARGET 1 (GENTOW5-A/A0/A1) was not at stake and is untouched beyond the pins named here.”

**CONDITIONALITY:** Historical record; its closing grade sentence is superseded by the acceptance record. The F-6 withdrawal is the note's own retraction of a counterfactual claim, quoted at `.35`'s trace.

**DERIVATION:** Repair-round bookkeeping; each item's mathematical derivation lives at the unit it repaired (`.18`, `.27`, `.24`/`.25`, `.22`, `.37`, `.35`).

**RESOLUTION TRACE:** Base §S7, lines 1396–1473; F-2's closing clause corrected in place by `[GT5-r2]`. This is the last section homed in the shard: S8 begins at line 1475.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN-1` — grep-verified count **11**; the note whose node-floor erratum the bare `[r1]` tag denotes.

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:S2 Step 0` — grep-verified count **2**; F-3's matching instance.

**TEETH:** F-3's grid-4 equality instance; FR-1 for F-1; GENTOW2 PE4 `@ 2f95be6` for F-2.

---

### EFF.GENTOW5.44  [changes-record]

**CANONICAL STATEMENT:** §S8 `[GT5-r2]` PE2 REPAIR RECORD — head

> “PE2 verdict (GENTOW5_passPE2_report.md @ 40f313a): NOT CLEAN — 0 CRITICAL + 2 GAP (PE2-F-1, PE2-F-2) + 2 MINOR (PE2-F-3, PE2-F-4); counter stays 0/2. This section is the r2 repair round; this round's edits are tagged [GT5-r2]. Sealed machine artifacts BYTE-FROZEN at their committed md5s (gentow5_checks.py 5fa684c7..., gentow5_output_exact.txt dc499a49..., gentow5_output_full.txt 839a8660...; the PE1/PE2 fresh instruments live at their own commits, 0160b94 / 40f313a); no runner edited, no re-run.”

**CONDITIONALITY:** Historical. “counter stays 0/2” is superseded by the acceptance record (`.56`).

**DERIVATION:** Round bookkeeping; the mathematical derivations live at the four items below and at the base sentences they repaired (shard 1).

**RESOLUTION TRACE:** Base §S8, lines 1477–1484.

**TEETH:** Byte-freeze assertion on three sealed artifacts (md5 prefixes recorded).

---

### EFF.GENTOW5.45  [changes-record]

**CANONICAL STATEMENT:** PE2-F-1 (GAP) — the `psi^{(w_i)}` re-scope

> “* **PE2-F-1 (GAP) -> RE-SCOPED at S3(a).** THEOREM GENTOW5-B(a) now reads: the pinned recipe realizes R_{nu_i}(Phi_{i+1}) = psi_{i+1}^{(w_i)} := w_i^{f_{i+1}} psi_{i+1}(y/w_i) — the landed GENTOW2 r3 B-law (u_i(beta_t) = theta_i(t) w_i^{f_{i+1}-t}; LEMMA GENTOW2-B [r3 RESTATED] + B'' @ d798529) applied at the S2.1 digits: theta_i(t) = vartheta_{i,f_{i+1}-t}^{-1} cancels the vartheta twist, the w-leg survives. Admissibility at each w_i: B'' + the PE5 verification (GENTOW2_passPE5_report @ 75923bc); GENTOW2-A's hypothesis (ii) quantifier accepts the twisted form — the same re-scope GENTOW2's own S4 consumer took (acdf97a). w_i = 1 stated OPEN (the uncomputed cross-frame unit; verdict-level machine data w-blind). Ripple: the [GT5-r2] consumer walk after S3(e) checks (b)'s cite legs, (b)'s P_{i+1} clause (repo classes; FR-A's psi_3 row), (c)'s repo-side stage read, (d), (e), the S4 witness (w_i = 1 trivially at K_i = F_2), and the sigma/degree/irreducibility data — per consumer; (b) gains the per-level twist rider; the S2.1 FGMN-R-read parenthetical fixed. S7's "consistent both ways" corrected in place to the two-clause statement (the instance leg stands; the no-re-parameterization identification was false at the w-leg).”

**CONDITIONALITY:** The re-scope is unconditional *as a re-scope*; the resulting clause (a) is later fenced at i ≥ 3 (`.68`), corrected at i = 1 (`.70`), and its certificate legs made conditional at n ≥ 3 (`.75`).

**DERIVATION:** The cancellation `theta_i(t) = vartheta_{i,f_{i+1}-t}^{-1}` applied to the landed B-law at the pinned digits; the full computation is quoted in shard 1's clause-(a) unit.

**RESOLUTION TRACE:** Base §S8, lines 1486–1506; lands on shard 1's clause (a), its consumer walk, and §S7's F-2 bullet.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B` — grep-verified count **30**; and `[r3 RESTATED]` — grep-verified count **1**. **Composite check:** the composite designation as GENTOW5 writes it, `LEMMA GENTOW2-B [r3 RESTATED]`, has count **0** in GENTOW2_PROOF; both components verify and the referent is unique, so the composite is recorded as GENTOW5's own compression, not an invented designation.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B″` — grep-verified count **10** (Unicode double prime; the ASCII `LEMMA GENTOW2-B''` has count **1** there).

XREF: `lean/notes/openmath/GENTOW2_passPE5_report.md:verifiably admissible` — grep-verified count **1**. The report's line 10 reads “algebra and ψ₃^{(w)} is verifiably admissible for every w ∈ K₂^×”; GENTOW5's `psi_3^{(w)} is verifiably admissible for every w in K_2^x` is the ASCII transliteration of that sentence.

**TEETH:** FR-A (`gentow5_pe2_fresh.py` @ 40f313a, 22/0) for the repo-side `psi_3` class; GENTOW2 PE5 @ 75923bc for admissibility.

---

### EFF.GENTOW5.46  [changes-record]

**CANONICAL STATEMENT:** PE2-F-2 (GAP) — the per-flavor base re-solve

> “* **PE2-F-2 (GAP) -> CORRECTED at S2.1's lift display.** lift_i(c; m) re-displayed as the per-flavor base re-solve: flavor monomials M_{r,t}(m) = nhat_i(m - Delta(r,t)) * (step monomial), derived from LEMMA GENTOW5-C's class separation (flavor residues = the tau_i-cocycle letter units; inverse-twisted digits). Verified at FR-A's numbers: the fixed-base t_1 = 1 flavor at m = 14 demands pi-exponent 11/2 — no monomial; the re-solved member 3^5*x*Phi_1 = FR-A's khat_0. Machine row FA1-LIFT (gentow5_pe2_fresh.py @ 40f313a, 22/0). Ripple pins: heights and deg < D_i unchanged (khat_t + S2.4 read heights only); GENTOW1 S3's fixed-base reading flagged for that note's own arc, not consumed here.”

**CONDITIONALITY:** The corrected display's own height range is settled later, at `.78` (`m > bound_i`).

**DERIVATION:** Class separation (LEMMA GENTOW5-C step (3)) plus the FR-A numerical falsification of the fixed-base display.

**RESOLUTION TRACE:** Base §S8, lines 1507–1518; lands on shard 1's K_i-digit-lift unit.

**TEETH:** `FA1-LIFT` (22/0) — asserts the fixed-base flavor's non-existence AND runs the re-solved member.

---

### EFF.GENTOW5.47  [changes-record]

**CANONICAL STATEMENT:** PE2-F-3 (MINOR) — the i = 1 edge of LEMMA GENTOW5-D

> “* **PE2-F-3 (MINOR) -> STATED at S2.4.** The i = 1 edge: the x-carry IS the top carry (j = 0 = i-1), key-part Phi_1 PRESERVED at E_1 = D_1 h = wt_1(x^{D_1}); the rung range 1..i-1 is EMPTY there; the strict clause now reads "the x-carry when i >= 2". Unconsumed edge (named consumers at i >= 2).”

**CONDITIONALITY:** Declared unconsumed: the named consumers instantiate i ≥ 2.

**DERIVATION:** At i = 1 the only reduction move is the x-carry, and `wt_1(Phi_1) = E_1 = D_1 h = wt_1(x^{D_1})`, so no strictness is available and no floor rung is consumed.

**RESOLUTION TRACE:** Base §S8, lines 1519–1523; lands on shard 1's LEMMA GENTOW5-D unit.

**TEETH:** Covered by the S7 F-3 grid equality fence; no dedicated row.

---

### EFF.GENTOW5.48  [open-obligation]

**CANONICAL STATEMENT:** PE2-F-4 (MINOR) — the compound coverage row

> “* **PE2-F-4 (MINOR) -> NAMED at S6's coverage box.** The compound seam-live x e_stage >= 2: the existing seam-live rows (FR-1, FR-A) are e-trivial at the live stage and the committed battery is seam-blind, so the compound has no machine contact in the program's committed rows — honest uncovered row; proof-side uniform (S2.3 step (3)).”

**CONDITIONALITY:** Machine-side coverage gap only; the proof is asserted uniform in `e_{i+1}`.

**DERIVATION:** Coverage audit of the committed rows against the (letter-live × e_stage) axes.

**RESOLUTION TRACE:** Base §S8, lines 1524–1529; lands on shard 1's coverage-box unit.

**TEETH:** This IS a teeth-coverage record: the named gap has NO committed row.

---

### EFF.GENTOW5.49  [changes-record]

**CANONICAL STATEMENT:** §S9 `[GT5-r3]` PE3 REPAIR RECORD — head

> “PE3 verdict (GENTOW5_passPE3_report.md @ 39c36aa): NOT CLEAN — 0 CRITICAL + 1 GAP (PE3-F-1) + 2 MINOR (PE3-F-2, PE3-F-3); counter stays 0/2. This section is the r3 repair round; this round's edits are tagged [GT5-r3]. Sealed machine artifacts BYTE-FROZEN, md5s re-verified this round (gentow5_checks.py 5fa684c7..., gentow5_output_exact.txt dc499a49..., gentow5_output_full.txt 839a8660...; the PE1/PE2/PE3 fresh instruments live at their own commits, 0160b94 / 40f313a / 9f0eca7); no runner edited, no re-run.”

**CONDITIONALITY:** Historical; counter superseded at `.56`.

**DERIVATION:** Round bookkeeping.

**RESOLUTION TRACE:** Base §S9, lines 1537–1544.

**TEETH:** md5 re-verification of the three sealed artifacts.

---

### EFF.GENTOW5.50  [lemma]

**CANONICAL STATEMENT:** PE3-F-1 (GAP) — clause (c)'s entry read RE-INDEXED, with the refutation of the composed pairing

> “* **PE3-F-1 (GAP) -> RE-INDEXED at S3(c).** The entry-read clause is RE-DERIVED as the uniform GENTOW-1 transport 2 -> i+1: the template (GENTOW1_PROOF S2, re-read at source this round) anchors its read one level BELOW the key with all stage data the KEY'S OWN (level-1 read, kappa_2 = u_2/e_2, psi_2^{mu2}, box vs Phi_2^{mu2} at mu2*E_2+1, pins (mu2-j)E_2+1, floor dv_2(Phi_2) > E_2), so T_{i+1}'s read clause is "level-i stage read, slope kappa_{i+1}, residual psi_{i+1}^{mu}" — the anchoring the display's degree/weight/pin/floor half already had; GENTOW-1 is the i = 1 instance verbatim. The composed (i+2)-read pairing is killed by the residual-degree count (level-(i+1) polygon length mu, full kappa_{i+2}-side residual degree mu/e_{i+2} vs deg psi_{i+2}^{mu} = mu*f_{i+2}: forces l_{i+2} = 1, improper) and refuted at the committed P-B3 rows f32@Phi4 (pins [682,inf,0]: kappa_5-side, residual degree 1 = psi_5, box 341 = 2E_4+1 holds) and Phi4@Phi3 (pins [170,inf,0]: same shape, box 85 = 2E_3+1).”

> “The corrected pairing VERIFIES at both committed witnesses, re-derived by hand this round from the digit expansions f32 = Phi_3^4 - 512 Phi_2 Phi_3^2 - 2^16 Phi_3 + 2^16 Phi_2^2 and Phi_4 = Phi_2^4 - 32 Phi_1 Phi_2^2 + 1024x (after Phi_1^2 = Phi_2 + 4x) … : f32@Phi3 (pins [340,inf,186,inf,0]: one kappa_4-side, j=2 digit 186 strictly above the chord 170, on-chord support {0,4}, residual y^2+1 = (y-1)^2 = psi_4^2 in F_2) and Phi4@Phi2 (pins [84,inf,50,inf,0]: one kappa_3-side, support {0,4}, residual psi_3^2) — LHS and RHS both hold at each.”

> “Proof side: the (c)-proof's substitution table entry "E_{i+1} -> E_{i+2}" resolved to E_{i+2} and the Step-2 parenthetical re-anchored — the step displays sit uniformly at the entered stage Phi_{i+2} and prove the corrected (c) at index i+1, consuming (b) at Phi_{i+2} + (SLOT_{i+1}) (step-(i+1) data of the same induction); with the index-1 base, indices 1..r-1 are covered. Consumers re-verified: (e) consumes the pins + box at E_{i+1} (the sound half) and its conclusion u_{i+2} > e_{i+2}E_{i+1} matches DEF GENTOW5-1's floor-chain provenance one index down; (d) is self-contained (GENTOW5-A's pattern); the S4 witness consumes (b)+(e); no sentence in the note consumes the retired (i+2)-read pairing.”

**Embedded rider (post-PE4, PE4-F-2) correcting this record's own display:**

> “[rider (post-PE4, 2026-08-10; PE4-F-2): the f32 display above is a true identity but HALFWAY reduced — its constant slot 2^16 Phi_2^2 has degree 8 = deg Phi_3, not a legal Phi_3-adic digit. Completing with the key relation Phi_2^2 = Phi_3 + 16 Phi_1 (the Phi_3-analogue of the Phi_1^2 = Phi_2 + 4x parenthetical) rewrites 2^16 Phi_2^2 = 2^16 Phi_3 + 2^20 Phi_1, and the +2^16 Phi_3 term CANCELS the -2^16 Phi_3 term: the CANONICAL dev is f32 = Phi_3^4 - 512 Phi_2 Phi_3^2 + 2^20 Phi_1, slots C_3 = C_1 = 0 (the quoted p_1 = p_3 = inf) and C_0 = 2^20 Phi_1 at dv_4 = 16*(20 + 5/4) = 340. Re-derived and machine-checked this fold by exact integer polynomial arithmetic (gentow5_rider_f32dev.py: halfway identity TRUE, completion relation exact, canonical slot degrees (4, 2) < 8, pins reproduced against the committed artifact row "f32@Phi3: pins [340, 'inf', 186, 'inf', 0]", gentow5_output_exact.txt byte-frozen at dc499a49). Conclusions invariant: one kappa_4-side, on-chord support {0,4}, residual psi_4^2, box 341 = 2E_4+1 unchanged.]”

**CONDITIONALITY:** The re-indexing is unconditional (a degree count plus committed rows). The *clause* it repairs is later made conditional at n ≥ 3 by `.75`.

**DERIVATION:** Two independent legs, both quoted: (i) the residual-degree count — a full `kappa_{i+2}`-side of a length-`mu` polygon carries residual degree `mu/e_{i+2}`, while `deg psi_{i+2}^{mu} = mu f_{i+2}`, and equality forces `e_{i+2} f_{i+2} = 1`, excluded by properness; (ii) the committed P-B3 rows, which refute the composed pairing and verify the corrected one.

**RESOLUTION TRACE:** Base §S9, lines 1546–1599, with the post-PE4 `[rider]` inserted inside the display at lines 1566–1583. Lands on shard 1's clause (c) and its proof.

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:S2` — grep-verified count **16**; the template re-read at source for the anchoring.

**TEETH:** P-B3 rows `f32@Phi4`, `Phi4@Phi3` (REFUTING) and `f32@Phi3`, `Phi4@Phi2` (VERIFYING); `gentow5_rider_f32dev.py` (7 checks / 0 violations) for the canonical development.

---

### EFF.GENTOW5.51  [changes-record]

**CANONICAL STATEMENT:** PE3-F-2 (MINOR) — the “uncomputed” claims DATED at both flank sites

> “* **PE3-F-2 (MINOR) -> DATED at both flank sites.** One dated bracket each at the S6 TARGET-2 bullet and the (a)-proof parenthetical: w is measured at the 7 measured primes (GENTOW2 PE6's 6 across LD1/LD3/GA1/GA3 + PE3 leg W's carrier-(8,4) prime at GA3*); the w_i = 1-OPEN claims themselves stand (closed-form law + unmeasured frames/levels), per the S3(a) dated note.”

**CONDITIONALITY:** The measurement dates the word “uncomputed”; it does not close `w_i = 1`, and it does not extend to unmeasured frames or to levels i > 2.

**DERIVATION:** Measurement record from GENTOW2 PE6 plus this note's own PE3 fresh leg W.

**RESOLUTION TRACE:** Base §S9, lines 1600–1606; lands on shard 1's clause-(a) dated note and §S6 TARGET-2 bullet.

XREF: `lean/notes/openmath/GENTOW2_passPE6_report.md:w-avatar` — grep-verified count **6**; the per-frame w measurements.

**TEETH:** GENTOW2 PE6 fresh route (GREEN 68/0, seal `ade1727`); this note's PE3 fresh leg W (`gentow5_pe3_fresh.py` @ 9f0eca7).

---

### EFF.GENTOW5.52  [changes-record]

**CANONICAL STATEMENT:** PE3-F-3 (MINOR) — the consumer-walk pointer correction

> “* **PE3-F-3 (MINOR) -> POINTER CORRECTED at the consumer walk.** The S4-witness bullet now points the w-triviality record at S6's TARGET-2 [GT5-r2] rider; the coverage box carries the seam axis (S4.1's re-check) and no w row.”

> “Grade: 0/2 UNCHANGED (repair round, not a pass). TARGET 1 (GENTOW5-A/A0/A1) was not at stake at PE3 and is untouched this round; the r2 repairs, the w-note rider, LEMMA GENTOW5-D, and (a)/(b)/(d)/(e) all survived PE3's attack and are untouched beyond the three sites named here.”

**CONDITIONALITY:** Historical; the grade line is superseded at `.56`.

**DERIVATION:** Bookkeeping correction — two records were conflated (w-triviality vs the seam axis) and are separated.

**RESOLUTION TRACE:** Base §S9, lines 1607–1616; lands on shard 1's consumer-walk unit.

**TEETH:** NONE (pointer hygiene).

---

### EFF.GENTOW5.53  [changes-record]

**CANONICAL STATEMENT:** §S10 post-PE4 fold — head and PE4-F-1 (index scope of (c)/(e))

> “PE4 verdict (GENTOW5_passPE4_report.md @ b22b37b): CLEAN — 0 CRITICAL + 0 GAP + 2 MINOR; counter 0/2 -> 1/2, the arc's first clean pass. This fold applies the two minors as dated [rider] brackets (no repair round owed; both are display hygiene at the r3 repair's edges, neither moves a conclusion). Both fixes were RE-DERIVED from the note's own lemmas and the committed artifacts, not transcribed from the report.”

> “* **PE4-F-1 (MINOR) -> SCOPED at the statement's (c) clause.** The blanket header "by induction on i < r" left (c)'s index-0 instance (T_1, level-0 read) formally in scope while the r3 coverage sentence names indices 1..r-1. The rider bracket states the honest scope: (c) — and (e), whose proof consumes (c)'s pins at the same index — are claimed at i >= 1 only (entry loci T_2..T_r; base = the index-1 GENTOW-1 instance, steps enter at Phi_{i+2} for i = 1..r-2). Verified at source this fold: DEF GENTOW5-1's floor-chain rung 1 rides the accepted [r1] node floor u_2 > e_2 E_1 = e_2 D'h directly (S2.1's provenance sentence), NOT (e)@index-0; S2.4's Phi_1-part weight bound consumes that same DEF hypothesis; a grep audit (T_1 / kappa_1 / psi_1^mu / level-0 read) found no other sentence instantiating (c) or (e) at index 0. T_1 is left unclaimed rather than cited.”

**CONDITIONALITY:** A scope narrowing, not a weakening of a proved statement: the r3 proof already had this scope; the rider records it.

**DERIVATION:** The induction's own base (GENTOW-1 = index 1) and step structure (steps enter at `Phi_{i+2}`), plus a grep audit for index-0 instantiations.

**RESOLUTION TRACE:** Base §S10, lines 1620–1645; lands on shard 1's clause (c)/(e) scope rider.

**TEETH:** The grep audit is the negative check; PE5's fresh route later instantiates the unclaimed `T_1` TRUE at one frame (`.58`).

---

### EFF.GENTOW5.54  [regression-record]

**CANONICAL STATEMENT:** PE4-F-2 (MINOR) — the canonical f32 development COMPLETED

> “* **PE4-F-2 (MINOR) -> COMPLETED at S9's f32 display.** The displayed f32 digit expansion was a true identity but halfway reduced (constant slot 2^16 Phi_2^2 of degree 8 = deg Phi_3 — not a legal Phi_3-adic digit). Re-derived this fold: Phi_2^2 = Phi_3 + 16 Phi_1 (the defining relation of Phi_3) completes the reduction and the resulting +2^16 Phi_3 cancels the -2^16 Phi_3 term, giving the canonical dev f32 = Phi_3^4 - 512 Phi_2 Phi_3^2 + 2^20 Phi_1 (C_3 = C_1 = 0, C_0 at dv_4 = 340). Machine leg (new helper, committed this fold): gentow5_rider_f32dev.py — exact integer polynomial arithmetic, 7 checks / 0 violations: halfway identity, completion relation, canonical dev, slot legality (degrees 4, 2 < 8), pins (340, inf, 186, inf, 0) = the committed artifact row f32@Phi3 (gentow5_output_exact.txt, byte-frozen at dc499a49), strict j = 2 chord clearance (186 > 170), and the Phi_4@Phi_2 display confirmed already-canonical. Conclusions invariant: one kappa_4-side, on-chord support {0,4}, residual psi_4^2, box 341 = 2E_4+1.”

**CONDITIONALITY:** Display hygiene inside a repair record; conclusions explicitly invariant.

**DERIVATION:** The key relation `Phi_2^2 = Phi_3 + 16 Phi_1` completes the Phi_3-adic reduction; the cancellation of `±2^16 Phi_3` is exact; all seven legs machine-checked.

**RESOLUTION TRACE:** Base §S10, lines 1646–1663; lands inside `.50`'s display (the rider is quoted there in place).

**TEETH:** `gentow5_rider_f32dev.py` — 7 checks / 0 violations, cross-checked against the byte-frozen artifact row.

---

### EFF.GENTOW5.55  [fence]

**CANONICAL STATEMENT:** §S10 grade line and statement fence

> “Grade after this fold: counter 1/2 (PE4's verdict; a rider is not a pass). The statement fence: no theorem statement weakened — the PE4-F-1 bracket records the scope the r3 proof already had; the PE4-F-2 bracket corrects a display inside a repair record. PE5 next.”

**CONDITIONALITY:** Historical counter, superseded at `.56`. The statement fence itself is the note's own no-weakening declaration for this fold.

**DERIVATION:** Declaration, with per-bracket justification quoted.

**RESOLUTION TRACE:** Base §S10, lines 1665–1669.

**TEETH:** NONE (declaration).

---

### EFF.GENTOW5.56  [acceptance-box]

**CANONICAL STATEMENT:** Dated acceptance record (2026-08-10, post-PE5)

> “**GENTOW5 IS ACCEPTED 2/2** — passPE4 CLEAN (0 CRITICAL + 0 GAP + 2 MINOR, GENTOW5_passPE4_report.md @ b22b37b; counter 0/2 -> 1/2) followed by passPE5 CLEAN (0 CRITICAL + 0 GAP + 3 MINOR, GENTOW5_passPE5_report.md @ 18900e03; counter 1/2 -> 2/2): two consecutive clean hostile passes, the standing acceptance bar.
> **THE NOTE IS FROZEN AT THIS RECORD: dated appends and dated brackets only; statement displays and sealed artifacts stay byte-untouched.**”

> “Grade after this record: **ACCEPTED 2/2**. Dated appends only beyond this line.”

**CONDITIONALITY:** Acceptance is a *process* verdict (two consecutive clean hostile passes), not a discharge of the note's named conditionality stack. It is later ANNOTATED — not downgraded — by S11 (“Grade: ACCEPTED 2/2 stands, ANNOTATED by RUN A”) and S12 (“acceptance 2/2 remains ANNOTATED”).

**DERIVATION:** The standing acceptance bar applied to the arc's counter.

**RESOLUTION TRACE:** Base lines 1671–1741. This record governs STATUS for the whole note, including every earlier “grade 0/2 / counter stays 0/2 / PEn next” sentence in shard 1's range.

**TEETH:** The two clean passes are the teeth of record; the byte-freeze is verified by the ledger at `.59`.

---

### EFF.GENTOW5.57  [changes-record]

**CANONICAL STATEMENT:** The arc in one breath

> “The arc in one breath: seal (2026-08-09) -> PE1 (1C+2G+3m) -> r1 (the GAUGE PIN: vartheta-twisted khat_t, machine-caught at the letter-live FR-1) -> PE2 (0C+2G+2m) -> r2 (the psi^{(w_i)} re-scope on the landed GENTOW2 r3 B-law + the per-flavor lift re-solve) -> PE3 (0C+1G+2m) -> r3 (the (c) entry-read RE-INDEXED to the uniform GENTOW-1 transport; the composed (i+2)-pairing killed by the residual-degree count and at committed rows) -> PE4 CLEAN (2 minors; counter 1/2) -> rider (both minors folded; f32 canonical dev machine-checked 7/7) -> PE5 CLEAN (3 minors; counter 2/2 — the (c) <-> GENTOW-1 seam adjudicated BINDING at the post-R2a/b/c GENTOW1 HEAD 4caf0fb; fresh route GREEN 40/0 with the first mu = 3 (c)-read anywhere and the first odd-p proper-(2,2) mid-stage tower at depths 3 and 4).”

**CONDITIONALITY:** Chronology only.

**DERIVATION:** Summary of the arc; each leg's derivation lives at its repair record.

**RESOLUTION TRACE:** Base lines 1682–1694.

**TEETH:** PE5 fresh route GREEN 40/0 (first mu = 3 (c)-read; first odd-p proper-(2,2) mid-stage tower at depths 3 and 4).

---

### EFF.GENTOW5.58  [changes-record]

**CANONICAL STATEMENT:** The companion fold — PE5-F-1, PE5-F-2, PE5-F-3

> “This append's companion fold (commit "GENTOW5 dated acceptance record (commit 1/2)") folded PE5's three MINORs at source as dated [acceptance fold] brackets, each RE-DERIVED from the note's own lemmas and the primary sources, not transcribed from the report:
> * PE5-F-1 -> the S3 statement header gains the INDEX-0 SCOPE bracket, completing the post-PE4 rider's (c)/(e) scoping to the clause list (a)/(b)/(d): (a)/(b) are claimed at i >= 1 ((a)@0's display dereferences nhat_0, not a DEF object — the index-0 content is the accepted chain data, T(b)' setting + GENTOW2 S2 dictionary; (b)@0 reduces to the j = 1 leg, the same accepted datum); (d)@0 IS claimed, via S1.4(ii)'s level-1 rider; Phi_1 is named the DEF-datum (recipe-built keys = Phi_2, ..., Phi_r); T_1 stays unclaimed, with PE5's fresh TRUE instantiation (f4 over p = 5) recorded in the conservative direction.
> * PE5-F-2 -> the (B-2) discharge's level lists gain their i = 1 line: the accepted GENTOW2-A(c) letter-formula content, verified at source this fold (GENTOW2_PROOF @ HEAD 33f8620: Cor 5.6(2) + S5.1's LETTER FORMULA z_2 = eta_2 * z_1^{-floor(l_1 u_2/e_1)} + the R3-4 disambiguation fence), with the i = 1 KP-membership leg at Lemma 5.3(1) [Q4] (the GENTOW2 [r1] F4-cure); an exponent-level tie of the w_1 display to the letter formula is NOT claimed.
> * PE5-F-3 -> S2.3's (LIFT_i) bound recursion's truncated token restored: e_{i+1}*bound_i, re-derived from ANNEX-THEOREM R1-c's displayed recursion plus the lemma's own step-(1) height split (grep-scoped: no numeric bound_i consumer in the note).”

**CONDITIONALITY:** PE5-F-2's closing disclaimer (“an exponent-level tie of the w_1 display to the letter formula is NOT claimed”) is what S11.3 later promotes into a statement correction (`.70`).

**DERIVATION:** Each fold is re-derived at the primary source, not transcribed — the note states this explicitly and names the source HEADs it re-read (`33f8620` for GENTOW2).

**RESOLUTION TRACE:** Base lines 1696–1724; the three brackets themselves are landed inside shard 1's range (S3 header, S3(a)'s (B-2) leg, S2.3's bound display) and are inventoried there.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:Cor 5.6` — grep-verified count **6**.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:S5.1` — grep-verified count **42**; the LETTER FORMULA's home.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:[Q4]` — grep-verified count **5**; Lemma 5.3(1), the KP-membership leg.

XREF: `lean/notes/openmath/HE7_PROOF_2026-08-08.md:ANNEX-THEOREM R1-c` — grep-verified count **3**; the bound recursion's primary source.

**TEETH:** PE5 fresh route (GREEN 40/0), which instantiates `T_1` TRUE at `f4 = Phi_1^2 - 25x` over `p = 5`.

---

### EFF.GENTOW5.59  [changes-record]

**CANONICAL STATEMENT:** BYTE-FREEZE LEDGER (acceptance round)

> “BYTE-FREEZE LEDGER (this round): pre-fold body md5 85efc5b4 (85efc5b445aa2d738301338c6075e118; 1,592 lines, 90,017 bytes) = the rider state @ cc7c944; the three fold brackets landed insertions-only (+77/-0; prefix through the first insertion byte-identical, md5 e9c5a20d at L561; commit a803a2ce), giving post-fold body md5 4292d8c8 (4292d8c86d58389ce91d38cb2aa759b7; 1,669 lines, 94,765 bytes); this record is a PURE APPEND on that body, verified by prefix md5 after the append. Sealed artifacts byte-frozen, md5s re-verified this round: gentow5_checks.py 5fa684c7..., gentow5_output_exact.txt dc499a49..., gentow5_output_full.txt 839a8660...; the rider helper gentow5_rider_f32dev.py 81bbb5db... untouched; no runner edited, no re-run.”

**CONDITIONALITY:** Protocol record. The md5s are of the note body and the artifacts at that round, not of the current HEAD state (the note has since grown by S11 and S12).

**DERIVATION:** Prefix-md5 verification of an insertions-only edit plus a pure append.

**RESOLUTION TRACE:** Base lines 1726–1738.

**TEETH:** The prefix-md5 discipline is itself the tooth: `+77/-0`, prefix byte-identical at L561.

---

### EFF.GENTOW5.60  [scope-record]

**CANONICAL STATEMENT:** §S11 `[GT5-r4]` — head, provenance and supersession discipline

> “## S11. [GT5-r4] CODEX TOWERRAT2 RUN A REPAIRS (2026-08-10 — dated append; acceptance 2/2 stands ANNOTATED, per the batch charter)”

> “Provenance: decorrelated-model adversarial RUN A (record CODEX_TOWERRAT2_2026-08-10.md S2 @ eeac45f6; raw log verification/openmath/towerrat2_runA_gentow5_output.txt), adjudicated 5/5 REAL (1 CRITICAL A-F1 + 2 GAP A-F2/A-F3 + 2 display MINOR A-F4/A-F5). Every correction below is RE-DERIVED from this note's own displays and the committed artifacts, not transcribed from the verifier. The note is frozen: these are dated corrections BY SUPERSESSION — the superseded sentences are quoted, stay byte-intact above, and read as corrected here. Pure-append discipline: the ledger at S11.6 carries the per-commit prefix md5s.”

**CONDITIONALITY:** The append annotates, it does not downgrade: “acceptance 2/2 stands ANNOTATED”.

**DERIVATION:** Adjudication of an external adversarial run; 5/5 findings judged REAL, each repaired from the note's own displays.

**RESOLUTION TRACE:** Base §S11 head, lines 1743–1755.

XREF: `lean/notes/openmath/CODEX_TOWERRAT2_2026-08-10.md:A-F1` — grep-verified count **3**; and `A-F2` — count **2**. The record's GENTOW5 section is `S2` (count **6** in that file; `GENTOW5` appears **12** times).

**READING NOTE:** the raw log `verification/openmath/towerrat2_runA_gentow5_output.txt` exists in the repo (checked).

**TEETH:** The decorrelated-model run itself; its per-finding machine legs are at `.61`.

---

### EFF.GENTOW5.61  [lemma]

**CANONICAL STATEMENT:** S11.1 `[A-F1, CRITICAL]` — the converse-rewriting direction CORRECTED

**Superseded sentences (quoted by the note itself):**

> “**Superseded sentences (quoted).** S2.4's proof close: "The converse rewriting (Phi_{j+1} = Phi_j^{l_{j+1}} - weight-E_{j+1} lifts) is weight-nondecreasing by the same displays." — FALSE as written. And the statement's consequence clause: "Hence 'all slots at weight >= W' is the same condition on every grid of the tower (the two-directional rewriting closes)" — WITHDRAWN to the one-directional form below.”

**The corrected statement:**

> “**The corrected direction (from S2.4's own displays).** The converse rewriting replaces the single slot Phi_{j+1} — priced (ehat_i/ehat_{j+2})u_{j+2} at an interior rung (j+1 <= i-1), E_i at the top rung (j+1 = i) — by the slots {Phi_j^{l_{j+1}}, khat_t Phi_j^{e_{j+1}t}}, all of which the Phi_j-carry display prices at (ehat_i/ehat_{j+1})E_{j+1} exactly. Hence the converse rewriting is weight-NONINCREASING: preserved exactly at the top rung (the lemma's own worked grid-4 instance Phi_4 = Phi_3^2 - 2^8 Phi_2, three slots at 170), and STRICTLY LOWERED at each interior rung by floor rung j+1 ((ehat_i/ehat_{j+2})u_{j+2} > (ehat_i/ehat_{j+1})E_{j+1}) — the same rung that makes the forward key-part strict.”

**CONDITIONALITY:** Consumes only the S2.4 displays and the floor chain — no new input. The LEMMA GENTOW5-D *statement* is explicitly untouched (see `.62`).

**DERIVATION:** [ASSEMBLED — the note's own pricing comparison, quoted above, plus its worked witness instance]

> “Witness instance (S4.1 chain, ehat_i = 2^i, E_3 = 42; committed ladder @ dc499a49): grid i = 4, interior rung j+1 = 3: Phi_3 = Phi_2^2 - 16 Phi_1 trades wt_4(Phi_3) = u_4 = 85 for wt_4(Phi_2^2) = 2*2*21 = 84 and wt_4(16 Phi_1) = 64 + 20 = 84 = (ehat_4/ehat_3)E_3; the drop 85 -> 84 is floor rung 3's tight margin (u_4 = 85 > e_4 E_3 = 84). Machine leg (ISOLATED repair-round re-check, not a sealed battery): gentow5_af1_direction_check.py — GREEN, 8 checks 0 violations (C1 rung, C2 the 85 -> 84 drop, C3 the 170 top-rung preservation, C4 forward nondecreasing, C5 the exact Z[x] identity + canonical Phi_1-adic development of Phi_3, C6 its level-1 polygon/descmin, C7 the rho-ladder, C8 the margin instance); md5s at S11.6.”

**RESOLUTION TRACE:** Base §S11.1, lines 1757–1789. Supersedes two sentences homed in shard 1 (LEMMA GENTOW5-D's consequence clause and its proof's closing sentence).

**READING NOTE:** the isolated instrument `verification/openmath/gentow5_af1_direction_check.py` and its output file both exist in the repo (checked).

**TEETH:** `gentow5_af1_direction_check.py` — 8 checks / 0 violations, explicitly flagged as an isolated re-check, NOT part of the sealed battery.

---

### EFF.GENTOW5.62  [fence]

**CANONICAL STATEMENT:** S11.1 — what survives (one-directional)

> “**What survives (one-directional).** The lemma's STATEMENT is untouched: forward carry moves are wt_i-nondecreasing, so "all slots at weight >= W" propagates from a representation to its carry-reductions (the canonical direction). One true remnant of the withdrawn closure, used below: the SINGLE-STEP converse at the TOP rung (expanding only Phi_i = Phi_{i-1}^{l_i} - lifts, i.e. the grid-i <-> level-(i-1)-read translation) preserves slot weights exactly — that is the top-rung display read backwards, no floor rung consumed.”

**CONDITIONALITY:** The surviving converse is single-step and top-rung only; interior descent is not available.

**DERIVATION:** The top-rung display of LEMMA GENTOW5-D read backwards — an equality, hence direction-independent.

**RESOLUTION TRACE:** Base §S11.1, lines 1791–1799.

**NON-IMPORT (explicit):** the two-directional grid closure is withdrawn; “no two-directional grid agreement is consumed anywhere in the repaired chain” (S11.1.3).

**TEETH:** `gentow5_af1_direction_check.py` C3 (top-rung preservation at 170) and C4 (forward nondecreasing).

---

### EFF.GENTOW5.63  [changes-record]

**CANONICAL STATEMENT:** S11.1 — consumption walk (the charged sites, re-audited)

> “**Consumption walk (the charged sites, re-audited).**
> * S2.4's consumer note ("nondecreasing is all any named consumer uses") — VERIFIED at GENTOW5-A Step B, S3(c) Steps 0/3, S3(d): each consumes forward reduction and/or (SLOT)-exactness. S3(c) Step 3's necessity leg reads the ENTERED level-(i+1) read against grid-(i+2) slots: that translation expands Phi_{i+2} only — the top rung, weight-preserving (the true remnant), not interior descent.
> * S3(c) Step 1 — SURVIVES: Phi_{i+2}^mu's slots at weight >= mu E_{i+2} come from reducing the mu-fold recipe product by FORWARD carries from side terms at E_{i+2} exactly.
> * S3(c) Step 2's parenthetical "(g strictly above, by GENTOW5-D both grids agree on 'above')" — THE BROKEN CONSUMPTION (the deeper reads at level j <= i sit across interior rungs, where the grids do NOT agree). Superseded by the derivation S11.1.1-S11.1.3; the ladder's conclusion stands on the new route.”

**CONDITIONALITY:** Exactly one consumer is broken; the other three survive with reasons given.

**DERIVATION:** Site-by-site audit against the corrected direction.

**RESOLUTION TRACE:** Base §S11.1, lines 1801–1816. Lands on shard 1's GENTOW5-A Step B, clause (c) Steps 0/1/2/3 and clause (d).

**TEETH:** The grep audit recorded at S11.1's honest residue (`.67`).

---

### EFF.GENTOW5.64  [lemma]

**CANONICAL STATEMENT:** S11.1.1 (descent floor)

> “**S11.1.1 (descent floor).** Fix the ladder rung j and write L_k := l_{j+1}...l_k (L_j := 1), lam := (ehat_j/ehat_{j+1})u_{j+1}. For j < k <= i+2, clause (b) at index k-1 ((b)@(i+1) is proved before (c) inside the same induction step; k-1 <= i is induction data) plus (SLOT_{j-1})-exactness give: the level-j polygon of Phi_k is one-sided from (0, L_k lam) to (L_k, 0), and since each pin is the slot-min of that coefficient, every slot of the canonical Phi_j-adic development of Phi_k satisfies
>
>     (slot weight of the coefficient part) + m*lam >= L_k * lam,
>
> with equality at the monic leading slot ("descmin(Phi_k) = L_k lam"). Here coefficient parts are grid-(j-1) monomials, priced exactly at level-j points; witness instance: Phi_3's level-1 read Phi_1^4 - 8x Phi_1^2 - 16 Phi_1 + 16 x^2, pins (10, 8, 7, -, 0), descmin = 10 = L_3 lam (re-check C5/C6).”

**CONDITIONALITY:** Consumes clause (b) at index k−1 and `(SLOT_{j-1})`-exactness. Because it consumes (b), S12.1 places it inside the `𝒲_{≤n}` chain at n ≥ 3 (`.75` item 3).

**DERIVATION:** One-sidedness from (b) plus pin-as-slot-min from (SLOT), giving the displayed inequality with equality at the monic leading slot; the witness instance is the level-1 read of `Phi_3` with its pins.

**RESOLUTION TRACE:** Base §S11.1.1, lines 1818–1833; conditionality set by S12.1 item 3.

**TEETH:** `gentow5_af1_direction_check.py` C5 (exact `Z[x]` identity + canonical `Phi_1`-adic development of `Phi_3`) and C6 (its level-1 polygon/descmin).

---

### EFF.GENTOW5.65  [lemma]

**CANONICAL STATEMENT:** S11.1.2 (the rho-ladder = the floor chain)

> “**S11.1.2 (the rho-ladder = the floor chain).** Scale the box's weight functional to level j: price\*(Phi_k) := (ehat_j/ehat_{k+1})u_{k+1} for j <= k <= i+1 and price\*(Phi_{i+2}) := (ehat_j/ehat_{i+2})E_{i+2} (wt_{i+2}'s own top price, scaled); x, pi, and Phi_k with k < j at their exact dv_j prices. Set rho_k := price\*(Phi_k)/L_k - lam. Then rho_j = 0, and
>
>     rho_k < rho_{k+1} (j <= k <= i)  <=>  u_{k+2} > e_{k+2}E_{k+1}
>                                           (floor rung k+1);
>     rho_{i+2} = rho_{i+1}            (E_{i+2} = l_{i+2}u_{i+2}: the
>                                       top price per Phi_j-degree IS
>                                       the deepest interior one).
>
> So rho\* := rho_{i+2} = max_k rho_k, consuming floor rungs j+1..i+1 — in-datum. Witness (j = 1, entered stage 3): rho = (0, 1/8, 1/8), strictness at rung 2 (21 > 20) — re-check C7.”

**CONDITIONALITY:** Unconditional floor arithmetic — S12.1 says so explicitly: “The numerical \(\rho\)-ladder of S11.1.2 is unconditional floor arithmetic”.

**DERIVATION:** The equivalence `rho_k < rho_{k+1} ⟺ u_{k+2} > e_{k+2}E_{k+1}` is the floor rung restated after scaling; the top equality is `E_{i+2} = l_{i+2}u_{i+2}`.

**RESOLUTION TRACE:** Base §S11.1.2, lines 1835–1850.

**TEETH:** `gentow5_af1_direction_check.py` C7 (the rho-ladder), witness `rho = (0, 1/8, 1/8)`.

---

### EFF.GENTOW5.66  [lemma]

**CANONICAL STATEMENT:** S11.1.3 (Step 2's aboveness, one-directional)

> “**S11.1.3 (Step 2's aboveness, one-directional).** Let T be a grid-(i+2) slot of g (the (c) box: wt_{i+2}(T) >= mu E_{i+2} + 1; scaled, wt\*(T) >= mu L_{i+2}(lam + rho\*) + ehat_j/ehat_{i+2}). Descend T to canonical Phi_j-adic form: the lam-priced weight is additive on monomial products, each deep factor Phi_k contributes at least L_k lam = price\*(Phi_k) - L_k rho_k (S11.1.1), and the re-reduction of coefficient products to deg < D_j is by grid-j FORWARD carries, nondecreasing also under the lam-pricing (the grid-j top carry prices Phi_j at lam > E_j by floor rung j, in-datum). With deg_j(T) = Sum_k J_k L_k < mu L_{i+2} =: M (from deg g < mu D_{i+2}, D_k = L_k D_j):
>
>     descmin(T) >= wt*(T) - Sum_k J_k L_k rho_k
>                >= wt*(T) - rho* M
>                >= M lam + ehat_j/ehat_{i+2}  >  M lam.
>
> By the ultrametric bound (only a LOWER bound on g's side is consumed), every Phi_j-adic coefficient of g satisfies dv_j(c_m(xi)) > (M - m) lam at xi in P_j: g's level-j pins sit STRICTLY ABOVE Phi_{i+2}^mu's side, whose own pins are (M - m) lam on the side ((b) + the power multiplicativity of Step 1, (SLOT)-exact). The level-j polygon of f = Phi_{i+2}^mu + g therefore carries Phi_{i+2}^mu's side and side residual verbatim — the ladder rung's exact need; the ascent proceeds as written, and no two-directional grid agreement is consumed anywhere in the repaired chain. Margin instance at the witness: 43/4 - 1/2 = 41/4 > 10 (re-check C8).”

**CONDITIONALITY:** Consumes S11.1.1 (hence clause (b)) — so at n ≥ 3 it sits inside the `𝒲_{≤n}` chain (`.75` item 3). Forward direction of LEMMA GENTOW5-D only.

**DERIVATION:** The displayed three-line chain: additivity of the lam-priced weight, the per-factor floor from S11.1.1, the uniform bound by `rho*` from S11.1.2, and the degree bound `deg_j(T) < M`; then the ultrametric comparison against `Phi_{i+2}^mu`'s side.

**RESOLUTION TRACE:** Base §S11.1.3, lines 1852–1878; replaces shard 1's clause-(c) Step 2 parenthetical.

**TEETH:** `gentow5_af1_direction_check.py` C8 (the margin instance `41/4 > 10`).

---

### EFF.GENTOW5.67  [fence]

**CANONICAL STATEMENT:** S11.1 — honest residue

> “**Honest residue.** The repaired Step 2 consumes (b)@(i+1) before (c)@(i+1) inside the step (the note's stated order), floor rungs j..i+1, (SLOT_{j-1}), and the forward direction of LEMMA GENTOW5-D — nothing outside the note's own pin stack. A grep audit this round ("same condition on every grid", "two-directional", "both grids agree") finds the withdrawn closure consumed at S3(c) Step 2's parenthetical and nowhere else in the body above.”

**CONDITIONALITY:** The audit's scope is the three quoted search strings; it establishes single-site consumption of the withdrawn closure.

**DERIVATION:** Consumption census plus a negative grep audit.

**RESOLUTION TRACE:** Base §S11.1, lines 1880–1886.

**TEETH:** The grep audit is the negative check.

---

### EFF.GENTOW5.68  [open-obligation]

**CANONICAL STATEMENT:** S11.2 `[A-F2, GAP]` — the i ≥ 3 B″-transport FENCED; `[GENTOW5-W(i)]` declared open

**Superseded reading (quoted by the note):**

> “**Superseded reading (quoted).** S3(a)'s (B-2) leg: "at i >= 3 the same derivation transports with (SLOT_i) = LEMMA GENTOW5-C in place of B-1" and "transported to i >= 3 on the same S2.3 annex-precedent ride". As consumption of the MONOMIAL LAW those sentences overclaim: the ride carries (SLOT_i)/(LIFT_i) counting statements, not GENTOW2-B'''s normalizer-cocycle monomial computation.”

**What is proved, per level, and what is not:**

> “**What IS proved, per level (the accepted GENTOW2 consumption-walk shape):**
> * i = 2 — VERBATIM: the landed GENTOW2 r3 B-law (LEMMA GENTOW2-B [r3 RESTATED] + LEMMA GENTOW2-B'' @ d798529), u_2(beta_t) = theta_2(t) * w_2^{f_3 - t} with the single cross-frame unit w_2 — the level this note's (a)/(B-2) display cites at source.
> * i >= 3 — PROVED by this note's own sections: per-grade FIXEDNESS of u_i(beta) (S2.3 step (3)'s tau_i-cocycle letter computation: each grade's unit is a fixed K_i^x-value), x0-freeness and g-freeness (the (SLOT_i) value clause), and the definitional reciprocity theta_i(t) = vartheta_{i,f_{i+1}-t}^{-1} (S2.1's same monomial quotient, inverse read). NOT PROVED at i >= 3: the single-w geometric form
>
>       [GENTOW5-W(i)]   u_i(beta_t) = theta_i(t) * w_i^{f_{i+1}-t},
>                        w_i = R_{i+1,kbar_i}(nhat_i(u_{i+1})),
>
>   which per-grade fixedness underdetermines (fixed families exist that fit no single w) — this is GENTOW2-B'''s computation run at level i, which this note does not reproduce. [GENTOW5-W(i)] is hereby an OPEN transported lemma, the honest-sorry analogue.”

**CONDITIONALITY:** This unit IS a conditionality declaration. Its own scope statement (`.69`) is partly withdrawn by S12.1.

**DERIVATION:** The gap is exhibited, not merely asserted: per-grade fixedness underdetermines the single-w form because “fixed families exist that fit no single w”.

**RESOLUTION TRACE:** Base §S11.2, lines 1888–1918.

XREF: `lean/notes/openmath/GENTOW5_WI_2026-08-10.md:[GENTOW5-W(i)]` — grep-verified count **9**. **This is the reverse edge**: the WI note is the companion whose title line reads “[GENTOW5-W(i)] — the i >= 3 monomial form of the B''-transport, PROVED”. GENTOW5 itself declares the lemma OPEN; see OPEN-CALL 1.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B″` — grep-verified count **10**; the level-2 computation this note does not reproduce at level i.

**TEETH:** None — the note states the machine record cannot discriminate this fence (`.69`).

---

### EFF.GENTOW5.69  [scope-record]

**CANONICAL STATEMENT:** S11.2 — scope of the fence

> “**Scope of the fence (what rides on [GENTOW5-W(i)] at i >= 3 and what does not).** Conditional on it: clause (a)'s realized-residual display psi_{i+1}^{(w_i)} AND the (a)-certificate legs that consume that form (KP membership via admissibility of psi^{(w)}, prime, non-equivalence), and with them (b)'s FGMN-side residual DISPLAYS at i >= 3 (the (b)-cite enters through (a)'s certificate at the same index). Not conditional (the [GT5-r2] per-consumer walk, unchanged): sigma, values, degrees, irreducibility transport, the repo-side residue classes and P-membership clauses, (c)'s budgets, (d), (e) — w-blind there. At i = 2 the display is unconditional (the landed law); at i = 1 see S11.3. The S4 depth-4 witness is w-trivial (K_i = F_2), so the machine record does not discriminate this fence — disclosed at S6's coverage box already.”

**CONDITIONALITY — PARTLY WITHDRAWN in range.** S12.1's opening supersedes the second sentence:

> “but its subsequent assertion that exact values, repo-side residue classes, \(P\)-membership, clause (c), and clause (e) remain unconditional is WITHDRAWN.”

**Effective reading:** the *conditional* list stands and grows; the *not-conditional* list shrinks to what S12.1's unaffected-scope paragraph names (`.77`). The two clauses that survive from the original not-conditional list are (d) at its stated event hypotheses and the formal/arithmetic content; `(c)`, `(e)`, exact values, repo-side classes and P-membership move to the conditional side at n ≥ 3.

**DERIVATION:** The original scope split rested on “w-blindness” of repo-side data; S12.1 identifies the flaw in that reasoning (`.74`).

**RESOLUTION TRACE:** Base §S11.2, lines 1919–1931; superseded in part by S12.1 (resolution rule 4).

**TEETH:** Explicitly none: “the machine record does not discriminate this fence”.

---

### EFF.GENTOW5.70  [lemma]

**CANONICAL STATEMENT:** S11.3 `[A-F3, GAP]` — clause (a) at i = 1 RE-SCOPED

> “**The two sentences in tension (quoted).** The statement's (a) displays R_{nu_i}(Phi_{i+1}) = psi_{i+1}^{(w_i)} at the pinned w_i = R_{i+1,kbar_i}(nhat_i(u_{i+1})), claimed at i >= 1; the PE5-F-2 acceptance fold discharges the i = 1 line at the shape "a psi_2^{(u)} with u a fixed z_1-letter power" and closes "an exponent-level tie of the w_1 display to the letter formula is NOT claimed."”

> “**Adjudicated from the fold's own scope bracket: the DISCLAIMER is right; the statement's i = 1 instance is corrected.** The fold's derivation is GENTOW2-A(c)'s letter-formula content (z_2 = eta_2 * z_1^{-floor(l_1 u_2/e_1)}): it pins the SPECIES of the twist unit (a fixed z_1-letter power) and never evaluates the residue R_{2,kbar_1}(nhat_1(u_2)) — so it cannot identify the unit with the pinned w_1, and different units give different residual polynomials (the twist acts on coefficients grade-by-grade). Dated statement correction (honest re-scope, standing authority): clause (a) AT i = 1 reads
>
>     R_{nu_1}(Phi_2) = psi_2^{(u1)},  u1 in K_1^x a FIXED
>     z_1-letter-power unit (the letter formula's species);
>     the tie u1 = w_1 = R_{2,kbar_1}(nhat_1(u_2)) is OPEN.”

> “Consumers: the fold's grep audit (zero instantiations of the w_1 display against the letter formula; no consumer on the record read needs the tie) re-verified this round. Net position after S11.2 + S11.3: the pinned-w_i form is unconditionally realized at i = 2 exactly; at i = 1 the shape is proved with the tie open; at i >= 3 the form is open behind [GENTOW5-W(i)].”

**CONDITIONALITY:** At i = 1 the *species* is proved; the *identification* with the pinned `w_1` is OPEN. Declared consumer-free (grep audit).

**DERIVATION:** The letter formula fixes the species but never evaluates the residue that defines `w_1`; since different units give different residual polynomials, species does not determine the twist. Hence the statement is re-scoped rather than the tie asserted.

**RESOLUTION TRACE:** Base §S11.3, lines 1933–1964. This is a **statement correction** on a clause homed in shard 1, taken under “standing authority” and in the conservative direction (it weakens the note's own claim; the statement fence in the parent CLAUDE.md concerns weakening a *target* to make it provable, which this is not — here the note narrows its own asserted conclusion).

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:S5.1` — grep-verified count **42**; the LETTER FORMULA's home.

**READING NOTE:** the clause-level pointer `GENTOW2-A(c)` is not separately greppable (`GENTOW2-A(c)` count **0** in GENTOW2_PROOF); the parent `THEOREM GENTOW2-A` is verified (count **8**). Carried descriptively, not as a designation.

**TEETH:** The grep audit (zero consumer instantiations), re-verified at this round.

---

### EFF.GENTOW5.71  [changes-record]

**CANONICAL STATEMENT:** S11.4 `[A-F4, MINOR]` — the `lift_i(c; m)` m-range bracket **(SUPERSEDED IN RANGE)**

> “Dated bracket on the S2.2 K_i-digit-lifts display: the flavor display and the realization sentence ("O-digit coefficients d_{r,t} realizing c") read AT HEIGHTS m IN (LIFT_i)'S VALIDITY RANGE — k-uniformly above the bound_{i+1} recursion of LEMMA GENTOW5-C, whose (LIFT_i) clause the display's existence/freeness sentence already cites. Unrestricted m is overbroad: below the range a flavor can fail integrality (at i = 1, e_1 = 2, f_1 = 2, h = 1, m = 0 the r = 1 flavor's base nhat_1(-2) demands pi^{-1} — no such monomial in O[x]; the "flavor is absent when nhat_i(m - Delta(r,t)) has no ladder solution" proviso already excludes negative-height bases, and the m-range bracket makes the realization claim's scope match it). Consumers unchanged: the recipe's khat_t heights and the floor chain sit in-range per the lemma's own bound arithmetic.”

**CONDITIONALITY:** **Superseded by S12.2 in this same range** (resolution rule 3): the `bound_{i+1}` threshold is WITHDRAWN and replaced by `bound_i`. What survives from this bracket is (i) the observation that unrestricted `m` is overbroad, and (ii) the worked integrality failure at `i = 1, e_1 = 2, f_1 = 2, h = 1, m = 0`.

**DERIVATION:** The negative-height base `nhat_1(-2)` would demand `pi^{-1}`, which is not in `O[x]`.

**RESOLUTION TRACE:** Base §S11.4, lines 1966–1980; superseded at §S12.2, lines 2137–2142.

**RECORDED SOURCE DEFECT (flagged, not silently repaired):** the bracket is addressed to “the S2.2 K_i-digit-lifts display”, but that display is homed in §S2.1 (§S2.2 is the consistency-checks section). The referent is unique in the note, so the bracket is applied to the §S2.1 display; the mis-pointer is recorded. S12.2, which supersedes the bracket, refers to it without a section number.

**TEETH:** The worked `pi^{-1}` failure instance.

---

### EFF.GENTOW5.72  [lemma]

**CANONICAL STATEMENT:** S11.5 `[A-F5, MINOR]` — clause (b)'s residual display RE-INDEXED

> “Dated bracket on the statement's (b): the residual display "R_{j-1}(Phi_{i+1}) = psi_{j-1}^{l_j ... l_{i+1}}" dereferences psi_0 at j = 1 and fails the residual-degree count. Corrected, in this note's stage numbering:
>
>     R_{j-1}(Phi_{i+1}) = psi_j^{l_{j+1} ... l_{i+1}}
>     (1 <= j <= i+1; empty product = 1 at j = i+1),
>
> re-derived from the note's own rows: the level-(j-1) polygon of Phi_{i+1} has length l_j...l_{i+1}, and one full side of slope lam_j (gcd(u_j, e_j) = 1) carries residual degree l_j...l_{i+1}/e_j = f_j * l_{j+1}...l_{i+1} = deg of the corrected display (the composed display's degree f_{j-1}*l_j...l_{i+1} fails this count); checked at the committed rows — the j = 1 leg (level-0 read, residue class a psi_1-root: psi_1, exponent l_2...l_{i+1} consistent), the top leg j = i+1 (level-i read, residual psi_{i+1} of degree f_{i+1}), and P-B3's Phi_4@Phi_2 (level-2 read, j = 3: psi_3^{l_4} = (y-1)^2, measured residual degree 2, S10). The (b) proof's citation line "R_{j-1}(F) = psi_{j-1}^{l_j...}" transcribes [Q10]'s display (23) in the source's own numbering; the consumed content (one-sidedness, exact intermediate values, root classes) is index-convention-blind, and no psi_0 is consumed anywhere in the proof. [Per S11.2, at i >= 3 the psi symbols in this display read at their levels' twisted forms per the re-scoped (a), now behind [GENTOW5-W(i)].]”

**CONDITIONALITY:** The re-index is a display correction with no consumption change (“the consumed content … is index-convention-blind”). At i ≥ 3 the display's psi symbols carry the twists, indexed as the post-D3i corrigendum fixes (`.84`).

**DERIVATION:** The residual-degree count: polygon length `l_j...l_{i+1}`, one full side with `gcd(u_j, e_j) = 1` gives residual degree `l_j...l_{i+1}/e_j = f_j·l_{j+1}...l_{i+1}` — matching the corrected display, not the composed one; three committed rows check it.

**RESOLUTION TRACE:** Base §S11.5, lines 1982–2008; further twisted by S12.1 item 2 and re-indexed by the post-D3i corrigendum.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:[Q10]` — grep-verified count **6**; and `(23)` — count **4**. **Source-display check:** GENTOW2's `[Q10]` quote block prints “R_{i−1}(F) = (ψ_{i−1})^{ℓ_i}”, confirming the diagnosis that the base display transcribed FGMN's own index convention.

**TEETH:** P-B3's `Phi_4@Phi_2` row (level-2 read, `psi_3^{l_4} = (y-1)^2`, measured residual degree 2).

---

### EFF.GENTOW5.73  [changes-record]

**CANONICAL STATEMENT:** S11.6 `[GT5-r4]` BYTE-FREEZE + APPEND LEDGER

> “Pre-append state: post-acceptance body @ 43b42e9c, md5 d9e6b5ba (d9e6b5ba069c19eb5f528b03c1807f14; 1,741 lines, 98,509 bytes). Commit 1 (S11 head + S11.1): PURE APPEND, prefix-98,509 md5 re-verified d9e6b5ba; post state md5 0b850dda (1,886 lines, 106,419 bytes); machine leg gentow5_af1_direction_check.py md5 82acd3d2 (output 503279ef, GREEN 8 checks / 0 violations, exit 0). Commit 2 (S11.2-S11.6): PURE APPEND on that state, prefix-106,419 md5 re-verified at commit (recorded in the commit message). Sealed artifacts untouched this round: gentow5_checks.py 5fa684c7..., gentow5_output_exact.txt dc499a49..., gentow5_output_full.txt 839a8660..., gentow5_rider_f32dev.py 81bbb5db... — no runner edited, no sealed re-run. Statement displays above stay byte-intact; corrections are by dated supersession (S11.1 direction + closure, S11.3 (a)@i=1 re-scope, S11.5 (b) re-index) and dated fences (S11.2 [GENTOW5-W(i)], S11.4 m-range). Grade: ACCEPTED 2/2 stands, ANNOTATED by RUN A; the repairs above discharge the adjudication's charges A-F1/A-F3/A-F4/A-F5 in full and convert A-F2 into the named open lemma [GENTOW5-W(i)].”

**CONDITIONALITY:** Protocol record. Note the asymmetric disposition: four charges discharged, one (A-F2) **converted into an open lemma** rather than discharged.

**DERIVATION:** Prefix-md5 verification per commit.

**RESOLUTION TRACE:** Base §S11.6, lines 2010–2029.

**TEETH:** Prefix-md5 re-verification at each of the two commits; the isolated instrument's own md5/output pair.

---

### EFF.GENTOW5.74  [scope-record]

**CANONICAL STATEMENT:** S12.1 `[R-i2]` — the withdrawal, and the cumulative condition `𝒲_{≤n}`

> “**Superseded scope in S11.2.** S11.2 correctly leaves open, for every \(i\ge 3\),
>
> \[
> [{\rm GENTOW5\!-\!W}(i)]\qquad
> u_i(\beta_t)=\theta_i(t)\,w_i^{\,f_{i+1}-t},
> \qquad
> w_i=R_{i+1,\bar k_i}(\widehat n_i(u_{i+1})),
> \]
>
> but its subsequent assertion that exact values, repo-side residue classes, \(P\)-membership, clause (c), and clause (e) remain unconditional is WITHDRAWN. A fixed per-grade unit family is not enough: “\(w\)-blind” means invariance AFTER the family has been proved to have the single-\(w_i\) geometric form. It does not construct that form.”

> “For \(n\ge3\), write
>
> \[
> \mathcal W_{\le n}:=
> \bigwedge_{3\le q\le n}[{\rm GENTOW5\!-\!W}(q)].
> \]
>
> The cumulative condition records the induction history; locally, the new input at rung \(n\) is \([{\rm GENTOW5\!-\!W}(n)]\).”

**CONDITIONALITY:** This unit defines the conditionality vocabulary used by `.75`–`.77` and by shard 1's clauses (a)/(b)/(c)/(e). The post-D3i corrigendum adds how the chain diagram reads under it: “the dependency chain diagram is read under the ambient hypothesis 𝒲_{≤n} as a whole (its first arrow consumes [GENTOW5-W(n)] with the earlier instances ambient)”.

**DERIVATION:** The one-sentence defeater, quoted above: per-grade fixedness is a weaker property than single-`w` geometry, so “w-blindness” arguments presuppose exactly what is unproved.

**RESOLUTION TRACE:** Base §S12.1, lines 2037–2055; supersedes §S11.2's scope paragraph (`.69`).

XREF: `lean/notes/openmath/GENTOW5_WI_2026-08-10.md:[GENTOW5-W(i)]` — grep-verified count **9**; the companion note that claims the lemma (see OPEN-CALL 1).

**TEETH:** None — this is a conditionality re-display; the note states no committed row discriminates it.

---

### EFF.GENTOW5.75  [lemma]

**CANONICAL STATEMENT:** S12.1 `[R-i2]` — the correct conditional scope, clause by clause

> “1. **Clause (a).** At index \(n\ge3\), conditional on \(\mathcal W_{\le n}\), the pinned recipe has
>
>    \[
>    R_{\nu_n}(\Phi_{n+1})
>    =\psi_{n+1}^{(w_n)}
>    :=w_n^{f_{n+1}}\psi_{n+1}(y/w_n),
>    \]
>
>    and the admissibility, key-polynomial membership, prime/irreducibility certificate, and non-equivalence conclusions follow as written. Without \([{\rm GENTOW5\!-\!W}(n)]\), per-grade fixedness supplies no single substitution \(y\mapsto w_ny\), so none of those certificate legs is established for the pinned key.”

> “2. **Clause (b), including exact values and \(P\)-membership.** Corollary 6.4 fires only after clause (a) has supplied the key-polynomial/prime certificate for \(\Phi_{n+1}\). Consequently, at index \(n\ge3\), ALL of clause (b) is conditional on \(\mathcal W_{\le n}\): one-sidedness at every lower level, the corrected residual powers
>
>    \[
>    R_{j-1}(\Phi_{n+1})
>    =\bigl(\psi_j^{(\omega_j)}\bigr)^{\,l_{j+1}\cdots l_{n+1}}
>    \qquad(1\le j\le n+1),
>    \]
>
>    the exact intermediate values
>
>    \[
>    v(\Phi_{j-1}(\xi))=\frac{u_j}{\widehat e_j},
>    \]
>
>    the repo-side residue-class identifications, and therefore \(\xi\in P_{n+1}\). Here \(\omega_1\) is S11.3's proved fixed \(z_1\)-letter-power unit, \(\omega_2=w_2\) from the landed GENTOW2 law, and \(\omega_j=w_j\) for \(j\ge3\). The B'' root correspondence is usable only after the corresponding common \(\omega_j\) exists; it cannot turn an arbitrary per-grade unit family into a geometric twist.”

> “3. **S11.1 and clause (c).** The numerical \(\rho\)-ladder of S11.1.2 is unconditional floor arithmetic, but S11.1.1 and S11.1.3 consume clause (b): S11.1.1 obtains the one-sided polygons and
>
>    \[
>    \operatorname{descmin}(\Phi_k)=L_k\lambda
>    \]
>
>    from \((b)@(k-1)\), while S11.1.3 compares \(g\) against those sides and their exact pins. Thus clause (c) at index \(n\ge3\), including its sufficiency direction, deeper-read ascent, fibration, node pins, and field-floor conclusion, is conditional on \(\mathcal W_{\le n}\). Step 1 already consumes \((b)@n\); the repaired Step 2 additionally consumes the earlier \((b)@q\) instances occurring in its descent.”

> “4. **Clause (e) and the induction feed.** Clause (e) at index \(n\ge3\) consumes clause (c)'s pins, so its automatic next-floor conclusion
>
>    \[
>    u_{n+2}>e_{n+2}E_{n+1}
>    \]
>
>    is conditional on \(\mathcal W_{\le n}\) as well. Later arguments may still use that inequality unconditionally when it is included explicitly in the fixed tower datum; only its claimed automatic derivation from the recipe is conditional.”

**CONDITIONALITY:** Item 2's twist indexing is itself corrected by the post-D3i corrigendum (`.84`): read `ψ_j^{(ω_j)}` as `ψ_j^{(ω_{j−1})}`.

**DERIVATION:** A dependency audit, each step quoted: (a) needs the single substitution; Cor 6.4 needs (a)'s certificate; S11.1.1/S11.1.3 consume (b); (e) consumes (c)'s pins.

**RESOLUTION TRACE:** Base §S12.1, lines 2057–2119; item 2 re-indexed at lines 2299–2313. Lands on shard 1's clauses (a), (b), (c), (e) and on this shard's `.64`, `.66`.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:Cor 6.4` — grep-verified count **11**; the corollary whose firing order is the load-bearing step of item 2.

**TEETH:** None; explicitly a conditionality propagation. Its own provenance leg is the D1a/E12 certification pair (`.83`).

---

### EFF.GENTOW5.76  [scope-record]

**CANONICAL STATEMENT:** S12.1 — the complete dependency chain

> “The complete dependency chain is therefore
>
> \[
> [{\rm GENTOW5\!-\!W}(n)]
> \Longrightarrow (a)@n
> \Longrightarrow {\rm Corollary\ 6.4}\Longrightarrow (b)@n
> \Longrightarrow {\rm S11.1.1/S11.1.3}
> \Longrightarrow (c)@n
> \Longrightarrow (e)@n
> \Longrightarrow\text{the next automatic floor}.
> \]”

**CONDITIONALITY:** Read under the ambient hypothesis `𝒲_{≤n}` per the post-D3i corrigendum:

> “Correspondingly, the dependency chain diagram is read under the ambient hypothesis 𝒲_{≤n} as a whole (its first arrow consumes [GENTOW5-W(n)] with the earlier instances ambient).”

**DERIVATION:** The chain is the composition of `.75`'s four items.

**RESOLUTION TRACE:** Base §S12.1, lines 2121–2131; ambient reading fixed at lines 2309–2312.

**TEETH:** None (dependency diagram).

---

### EFF.GENTOW5.77  [fence]

**CANONICAL STATEMENT:** S12.1 — unaffected scope

> “**Unaffected scope.** The \(i=2\) rung remains unconditional by the landed GENTOW2 law; the \(i=1\) residual remains exactly S11.3's fixed-letter-power statement with only its identification with the displayed \(w_1\) open. LEMMAS GENTOW5-A0/A1, the refine-transfer clause (d) at its stated event hypotheses, LEMMA GENTOW5-D under an explicitly supplied floor-chain datum, formal monicity/degrees and recipe-height arithmetic, and the S4 witness remain unaffected. At S4 every \(K_i^\times=\{1\}\), so each required geometric law is tautological there.”

**CONDITIONALITY:** This is the post-narrowing positive list — the units of shard 1 that stay unconditional. Note the qualifier on LEMMA GENTOW5-D: “under an explicitly supplied floor-chain datum” (bearing on OPEN-CALL 3).

**DERIVATION:** Complement of the dependency chain; the S4 clause is derived from `K_i^× = {1}`.

**RESOLUTION TRACE:** Base §S12.1, line 2133.

**TEETH:** The S4 witness (w-trivial by construction) is named as the tautological case.

---

### EFF.GENTOW5.78  [lemma]

**CANONICAL STATEMENT:** S12.2 `[R-i4]` — the lift rung CORRECTED

> “**Superseded S11.4 bracket.** The sentence placing the displayed \(\operatorname{lift}_i(c;m)\) above \(\operatorname{bound}_{i+1}\) is WITHDRAWN. That display realizes \(c\in K_i\) by a polynomial of degree \(<D_i\); hence it consumes the PRECEDING lift instance and has threshold \(\operatorname{bound}_i\), not \(\operatorname{bound}_{i+1}\).”

> “Precisely,
>
> \[
> \operatorname{lift}_i(c;m)\in\mathcal O[x],\qquad
> \deg\operatorname{lift}_i(c;m)<D_i,\qquad
> \operatorname{res}\!\left(
>  \frac{\operatorname{lift}_i(c;m)}{\widehat n_i(m)}
> \right)=\iota^{(i)}(c)
> \]
>
> is valid for
>
> \[
> m>\operatorname{bound}_i.
> \]
>
> For \(i\ge2\) this is supplied by \(({\rm LIFT}_{i-1})\); for \(i=1\) it is the accepted base lift. By contrast, the clause labelled \(({\rm LIFT}_i)\) in LEMMA GENTOW5-C constructs \(K_{i+1}\)-digits of degree \(<D_{i+1}\) and therefore correctly has threshold
>
> \[
> \operatorname{bound}_{i+1}
> =(l_{i+1}-1)u_{i+1}
>  +e_{i+1}\operatorname{bound}_i.
> \]”

**CONDITIONALITY:** Unconditional rung arithmetic; independent of `[GENTOW5-W(i)]`. The post-D3i corrigendum confirms: “R-i4 (the lift rung) is unaffected and was DISCHARGED.”

**DERIVATION:** The threshold is fixed by *what the object realizes*: `lift_i` realizes `K_i` with degree `< D_i`, hence it is the level-`i` instance and consumes the preceding rung's bound; `(LIFT_i)` realizes `K_{i+1}` with degree `< D_{i+1}` and keeps `bound_{i+1}`.

**RESOLUTION TRACE:** Base §S12.2, lines 2137–2169; supersedes `.71` (S11.4) and lands on shard 1's K_i-digit-lift unit.

XREF: `lean/notes/openmath/HE7_PROOF_2026-08-08.md:ANNEX-THEOREM R1-c` — grep-verified count **3**; the source of the `bound_{i+1}` recursion restored at PE5-F-3.

**TEETH:** The depth-4 numeric separation at `.81`.

---

### EFF.GENTOW5.79  [lemma]

**CANONICAL STATEMENT:** S12.2 — the boxed bound inequality

> “**The bound needed by every recipe lift is automatically met.** At the base,
>
> \[
> \operatorname{bound}_1=(l_1-1)u_1<E_1=l_1u_1.
> \]
>
> Inductively, if \(\operatorname{bound}_{i-1}<E_{i-1}\), the floor rung \(u_i>e_iE_{i-1}\) gives
>
> \[
> e_i\operatorname{bound}_{i-1}<u_i
> \]
>
> and hence
>
> \[
> \operatorname{bound}_i
> =(l_i-1)u_i+e_i\operatorname{bound}_{i-1}
> <l_i u_i=E_i.
> \]
>
> Thus
>
> \[
> \boxed{\operatorname{bound}_i<E_i\quad\text{for every }i\ge1.}
> \]”

**CONDITIONALITY:** Consumes the floor chain `u_i > e_i E_{i-1}` — which at n ≥ 3 is itself either a datum hypothesis or a conditional consequence (`.77`, OPEN-CALL 3). The induction is otherwise elementary arithmetic.

**DERIVATION:** The two-line induction quoted above.

**RESOLUTION TRACE:** Base §S12.2, lines 2171–2198.

**TEETH:** `.81`'s depth-4 numbers `(1, 7, 35, 155)` vs `E_i = (2, 10, 42, 170)` instantiate the box.

---

### EFF.GENTOW5.80  [lemma]

**CANONICAL STATEMENT:** S12.2 — every recipe lift lands in range, and the corrected consumer sweep

> “For a nonzero recipe coefficient \(c_t\), put \(s=f_{i+1}-t\). Since \(t<f_{i+1}\), one has \(s\ge1\), and the recipe height is
>
> \[
> m_t=s\,u_{i+1}\ge u_{i+1}
> >e_{i+1}E_i\ge E_i>\operatorname{bound}_i.
> \]
>
> Therefore the required preceding-rung lift exists and gives
>
> \[
> \widehat k_t
> =\operatorname{lift}_i
>  \bigl(c_t\vartheta_{i,s};\,s u_{i+1}\bigr)
> \in\mathcal O[x],\qquad
> \deg\widehat k_t<D_i,
> \]
>
> with exact \(dv_i\)-height \(s u_{i+1}\) and the prescribed coherent \(K_i\)-digit. When \(c_t=0\), \(\widehat k_t=0\) and no lift is required. Consequently every nonzero recipe side term has exact \(dv_{i+1}\)-height
>
> \[
> e_{i+1}s u_{i+1}+e_{i+1}t u_{i+1}
> =e_{i+1}f_{i+1}u_{i+1}=E_{i+1},
> \]
>
> and its degree is \(<D_{i+1}\).”

> “No recipe consumer needs \(m_t>\operatorname{bound}_{i+1}\). The corrected consumer sweep is:
>
> * DEF GENTOW5-1 and clause (a) need the preceding-rung \(K_i\)-digit lift above \(\operatorname{bound}_i\), proved above.
> * LEMMA GENTOW5-D's \(({\rm INV}\!-\!j)\) carry display needs only \(\deg\widehat k_t<D_i\) and the exact height \(s u_{i+1}\), both now proved in the correct range.
> * Clause (c), including Step 1 and Step 5, consumes those same exact side heights and coherent digits; it does not consume \(\operatorname{bound}_{i+1}\) for a recipe coefficient.
> * The S4 recipe keys consume respectively \(\operatorname{bound}_1,\operatorname{bound}_2, \operatorname{bound}_3,\operatorname{bound}_4\), never the next bounds.”

**CONDITIONALITY:** Uses `u_{i+1} > e_{i+1}E_i` (floor chain) and the boxed `bound_i < E_i`. No `[GENTOW5-W(i)]` dependence.

**DERIVATION:** The displayed inequality chain `m_t ≥ u_{i+1} > e_{i+1}E_i ≥ E_i > bound_i`, then the height/degree arithmetic of the recipe side terms.

**RESOLUTION TRACE:** Base §S12.2, lines 2200–2245; discharges the range obligation for shard 1's recipe unit and (INV-j) display.

**TEETH:** `.81`'s witness separation.

---

### EFF.GENTOW5.81  [instance-record]

**CANONICAL STATEMENT:** S12.2 — the depth-4 witness makes the rung distinction explicit

> “The depth-4 witness makes the rung distinction explicit:
>
> \[
> (\operatorname{bound}_1,\operatorname{bound}_2,
>   \operatorname{bound}_3,\operatorname{bound}_4)
> =(1,7,35,155),
> \]
>
> while its successive recipe heights are
>
> \[
> 5,\ 21,\ 85,\ 341.
> \]
>
> Thus \(5>1\), \(21>7\), \(85>35\), and \(341>155\), exactly as required. The rejected next-rung demands would be \(5>7\), \(21>35\), \(85>155\), and \(341>651\), explaining why S11.4's range assertion was false while every actual recipe lift remains valid.”

**CONDITIONALITY:** One chain (the S4.1 all-(2,1) tower); it exhibits the rung distinction rather than proving the general statement, which is `.78`–`.80`.

**DERIVATION:** `bound_i` computed from the recursion of `.78` on the S4.1 datum, compared rung by rung with the recipe heights `u_{i+1}` of shard 1's witness chain.

**RESOLUTION TRACE:** Base §S12.2, lines 2247–2265.

**TEETH:** The four-fold numeric separation is itself the check; it is re-computed independently in the orchestrator verification note (`.83`).

---

### EFF.GENTOW5.82  [lemma]

**CANONICAL STATEMENT:** S12.2 — the refine consumers use the other rung correctly

> “Finally, genuine refine consumers use the other rung correctly: \(\operatorname{lift}_{i+1}(s;\lambda)\) realizes \(K_{i+1}\) with degree \(<D_{i+1}\), so it needs \(\lambda>\operatorname{bound}_{i+1}\). Their event hypothesis gives
>
> \[
> \lambda>E_{i+1}>\operatorname{bound}_{i+1},
> \]
>
> by the boxed inequality. Hence THEOREM GENTOW5-A and clause (d)'s refine lifts also land in their required ranges. This proves every actual lift consumption; no qualification of the recipe or refine statements is needed.”

**CONDITIONALITY:** Uses the event hypothesis `λ > E_{i+1}` (shard 1's clause (d) / THEOREM GENTOW5-A setting) and the boxed inequality of `.79`.

**DERIVATION:** `λ > E_{i+1} > bound_{i+1}` by the box, so the `(i+1)`-rung lift exists at the event slope.

**RESOLUTION TRACE:** Base §S12.2, lines 2267–2279; closes the lift-range obligation for shard 1's THEOREM GENTOW5-A and clause (d).

**TEETH:** Covered by `.81`'s numeric instance.

---

### EFF.GENTOW5.83  [changes-record]

**CANONICAL STATEMENT:** S12 provenance and orchestrator verification

> “*(The S12 append above was derived by the E12 certification run (gpt-5.6-sol high, runs/cert2/E12_gentow5_output.log, 2026-08-12), repairing the two D1a residuals (INSUFFICIENT finding 2 and NEW-ISSUE finding 4); orchestrator verification before transcription — R-i2's dependency chain checked against the D1a finding ((a)@n needs [W(n)]; Corollary 6.4 fires only after (a); (b) ⟹ S11.1.1/S11.1.3 ⟹ (c) ⟹ (e)), with the unaffected scope (i = 2 by the landed GENTOW2 law; S4's trivial K_i^×) named; R-i4's rung logic checked (lift_i realizes K_i with deg < D_i, so its threshold is bound_i — the level-i instance) and the depth-4 witness re-computed (bounds (1,7,35,155) vs recipe heights (5,21,85,341): each exceeds its level-i bound, none the next-rung bound — 5>1, 21>7, 85>35, 341>155 vs the failing 5>7 etc.); refine consumers correctly use lift_{i+1} at λ > E_{i+1} > bound_{i+1}. Transcribed unaltered per the standing division of labor. Ledger: row 10 → both residuals repaired, awaiting sol discharge (cert3).)*”

**CONDITIONALITY:** Declares a two-stage provenance: derived by a decorrelated model, hand-verified by the orchestrator before transcription, transcribed unaltered. The ledger line (“awaiting sol discharge (cert3)”) is a protocol state, later advanced by the post-D3i corrigendum and by the external ledger (§8 reading note).

**DERIVATION:** Verification record, with the re-computed numbers quoted.

**RESOLUTION TRACE:** Base §S12, lines 2281–2296.

XREF: `runs/cert/D1a_gentow5_output.log:INSUFFICIENT` — grep-verified count **2**; and `NEW-ISSUE` — count **2**. **Provenance check:** the two finding labels live in the **D1a** discharge output, as the note says (“the two D1a residuals”); the E12 log is the deriving run and restates them in its charge brief `runs/cert2/E12_gentow5_brief.txt` (“the INSUFFICIENT finding 2”, “the NEW-ISSUE finding 4”). Both files exist in the repo.

**TEETH:** The orchestrator's independent re-computation of the depth-4 bounds is the check of record for `.81`.

---

### EFF.GENTOW5.84  [lemma]

**CANONICAL STATEMENT:** Dated corrigendum (2026-08-12, post-D3i) — S12.1's residual-twist index

> “**Dated corrigendum (2026-08-12, post-D3i — S12.1's residual-twist index).** The D3i discharge pass (gpt-5.6-sol high, runs/cert3/D3i_gentow5_output.log) adjudicated S12.1 NEW-ISSUE at one index: clause (a) at index r supplies the twist w_r for ψ_{r+1}, so in clause (b)'s corrected residual display the twist attached to ψ_j is INDEXED j−1: ψ₂ carries S11.3's fixed letter-power unit, ψ₃ carries w₂, and ψ_j carries w_{j−1} for j ≥ 4 — read every ψ_j^{(ω_j)} in S12.1's clause (b) as ψ_j^{(ω_{j−1})} with ω₁ = the S11.3 unit (the outer ψ₁ leg handled separately as accepted). The display as first written demanded w_{n+1} at the top term, exceeding the assumed 𝒲_{≤n}. Correspondingly, the dependency chain diagram is read under the ambient hypothesis 𝒲_{≤n} as a whole (its first arrow consumes [GENTOW5-W(n)] with the earlier instances ambient). R-i4 (the lift rung) is unaffected and was DISCHARGED. Awaiting sol re-confirmation in the next queue.”

**CONDITIONALITY:** This is the **last** correction in the note; nothing in the note supersedes it. Its closing protocol sentence (“Awaiting sol re-confirmation in the next queue”) is a certification-protocol state, not a mathematical qualifier — see §8's reading note and OPEN-CALL 2.

**DERIVATION:** Index bookkeeping made forced by the hypothesis set: clause (a) at index `r` supplies `w_r` for `ψ_{r+1}`, so the twist on `ψ_j` must be `ω_{j−1}`; the original indexing would have demanded `w_{n+1}`, which `𝒲_{≤n}` does not supply.

**RESOLUTION TRACE:** Base lines 2299–2313; corrects `.75` item 2 and fixes how `.76`'s chain reads. It is the governing reading of clause (b)'s twisted residual display at i ≥ 3.

XREF: `runs/cert3/D3i_gentow5_output.log:NEW-ISSUE` — grep-verified count **2**; and `DISCHARGED` — count **2**.

**TEETH:** None; an index correction with no machine leg. The `ψ₁` leg is explicitly carved out (“handled separately as accepted”).

---
## 4. XREF verification ledger (consolidated, deduplicated)

Every designation below was checked with fixed-string grep (`grep -cF '<designation>' <file>`)
or file-existence, per rule 2. **77 raw XREF/artifact citations across the two shards
(57 from shard 1, 20 from shard 2 — matching each shard's own closing line) reduce to 67
distinct targets; ten are cited identically by both shards** (all ten targeting
`GENTOW2_PROOF_2026-08-09.md` or `HE7_PROOF_2026-08-08.md`, with matching counts on both
sides — verified programmatically, not by eye) **and are marked `**DEDUP**`.**

`[TABLE — compiler ledger]`

| # | Target : designation | Count | Material consumed | Source shard(s) | Dedup |
|---:|---|---:|---|---|---|
| 1 | `GENTOW1_PROOF_2026-08-09.md:LEMMA GENTOW-1` | 7 | Budgets template re-based at clause (c) | s1 | — |
| 2 | `GENTOW1_PROOF_2026-08-09.md:LEMMA GENTOW-2` | 7 | The event setting; layers 2/3 imported, layer 1 is the box | s1 | — |
| 3 | `GENTOW1_PROOF_2026-08-09.md:LEMMA GENTOW-5` | 6 | Named in SOURCES CONSUMED | s1 | — |
| 4 | `GENTOW1_PROOF_2026-08-09.md:COR GENTOW-1.1` | 4 | Clause (e)'s convexity argument | s1 | — |
| 5 | `GENTOW1_PROOF_2026-08-09.md:Step 0` | 11 | Carry pricing consumed at GENTOW5-A Step B | s1 | — |
| 6 | `GENTOW1_PROOF_2026-08-09.md:S2 Step 0` | 2 | The i = 2 instance matched by the GENTOW5-D restatement | s1 | — |
| 7 | `GENTOW1_PROOF_2026-08-09.md:Step 5` | 3 | The S4 computation re-run for the second wrap letter | s1 | — |
| 8 | `GENTOW1_PROOF_2026-08-09.md:S3` | 14 | Level-2 normalizers; layers 2/3 at general mu2 | s1 | — |
| 9 | `GENTOW1_PROOF_2026-08-09.md:GENTOW-BOX-1` | 5 | The box this note retires; a consumption candidate | s1 | — |
| 10 | `GENTOW1_PROOF_2026-08-09.md:GENTOW-BOX-2` | 2 | Coverage discipline for constructed frames | s1 | — |
| 11 | `GENTOW1_PROOF_2026-08-09.md:[GT1-r1]` | 5 | Erratum pin precedent for the gauge twist | s1 | — |
| 12 | `GENTOW2_PROOF_2026-08-09.md:THEOREM GENTOW2-A` | 8 | Admissibility quantifier; clause (d)'s i = 2 node data (s1) / Hypothesis-(ii) quantifier accepting the twisted residual (s2) | s1+s2 | **DEDUP** |
| 13 | `GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B` | 30 | The cite pattern run at level i (s1) / The landed r3 B-law re-scoping clause (a) (s2) | s1+s2 | **DEDUP** |
| 14 | `GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B′` | 8 | Per-grade unit family (B′(3)/(5)) | s1 | — |
| 15 | `GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B″` | 10 | The landed r3 B-law's `w` and the root correspondence (s1) / The single cross-frame unit `w`; the root correspondence; the level-i computation NOT reproduced (s2) | s1+s2 | **DEDUP** |
| 16 | `GENTOW2_PROOF_2026-08-09.md:S5.1` | 42 | `u(beta)` definition + the letter formula (s1) / The LETTER FORMULA behind the i = 1 re-scope (s2) | s1+s2 | **DEDUP** |
| 17 | `GENTOW2_PROOF_2026-08-09.md:S2` | 15 | MacLane-chain dictionary / polygon shear | s1 | — |
| 18 | `GENTOW2_PROOF_2026-08-09.md:S6` | 25 | FGMN faithfulness audit | s1 | — |
| 19 | `GENTOW2_PROOF_2026-08-09.md:S7` | 1 | Level-uniformity proviso; depth ≥ 4 bullet (consumption candidate) | s1 | — |
| 20 | `GENTOW2_PROOF_2026-08-09.md:[Q1]` | 4 | FGMN Lemma 1.11 (prime) | s1 | — |
| 21 | `GENTOW2_PROOF_2026-08-09.md:[Q2]` | 4 | FGMN Cor 1.13 (prime) | s1 | — |
| 22 | `GENTOW2_PROOF_2026-08-09.md:[Q4]` | 5 | FGMN Lemma 5.3(1)/(2) (KP membership) (s1) / Lemma 5.3(1), the i = 1 KP-membership leg (s2) | s1+s2 | **DEDUP** |
| 23 | `GENTOW2_PROOF_2026-08-09.md:[Q6]` | 4 | Degree-forcing display | s1 | — |
| 24 | `GENTOW2_PROOF_2026-08-09.md:[Q7]` | 9 | FGMN Prop 5.7 + eq (14) | s1 | — |
| 25 | `GENTOW2_PROOF_2026-08-09.md:[Q8]` | 8 | FGMN Cor 4.7 — clause (1) additivity, clause (3) multiplicativity | s1 | — |
| 26 | `GENTOW2_PROOF_2026-08-09.md:[Q9]` | 4 | FGMN Theorem 6.3 | s1 | — |
| 27 | `GENTOW2_PROOF_2026-08-09.md:[Q10]` | 6 | FGMN Corollary 6.4 + display (23) (s1) / FGMN Corollary 6.4 (the (b) cite) (s2) | s1+s2 | **DEDUP** |
| 28 | `GENTOW2_PROOF_2026-08-09.md:(23)` | 4 | The source display re-indexed by S11.5 (s1) / The source display re-indexed by S11.5 (s2) | s1+s2 | **DEDUP** |
| 29 | `GENTOW2_PROOF_2026-08-09.md:Def 3.16` | 3 | ε-normalized coordinate (the u_i-family's other side) | s1 | — |
| 30 | `GENTOW2_PROOF_2026-08-09.md:Lemma 3.17` | 7 | Consumed in the B′(3) derivation | s1 | — |
| 31 | `GENTOW2_PROOF_2026-08-09.md:Cor 5.6` | 6 | The i = 1 fold's FGMN residual identification (s1) / The FGMN residual identification at i = 1 (s2) | s1+s2 | **DEDUP** |
| 32 | `GENTOW2_PROOF_2026-08-09.md:Lemma 3.5` | 1 | Improper-stage collapsing | s1 | — |
| 33 | `GENTOW2_PROOF_2026-08-09.md:Prop 3.7` | 1 | Improper-stage collapsing | s1 | — |
| 34 | `GENTOW2_PROOF_2026-08-09.md:Theorem 6.3` | 5 | Fired per prime factor at (c) Step 2 | s1 | — |
| 35 | `GENTOW2_PROOF_2026-08-09.md:Cor 6.4` | 11 | Pins the factor data at (c) Step 2 (s1) / Firing order in the S12.1 dependency chain (s2) | s1+s2 | **DEDUP** |
| 36 | `GENHN_PROOF_2026-08-08.md:GENHN-2′` | 3 | Exact slot minimum, one digit per height (i = 2 base) | s1 | — |
| 37 | `GENHN_PROOF_2026-08-08.md:GENHN-2` | 28 | The i = 1 base of (SLOT) | s1 | — |
| 38 | `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-4` | 3 | Level-1 assembly display; layer-2 substitute in the rider | s1 | — |
| 39 | `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-T(b)` | 11 | The accepted depth-2 tower datum (i)/(ii)/(iii) | s1 | — |
| 40 | `GENHN_PROOF_2026-08-08.md:GENHN-BOX-2` | 5 | Retirement condition matched by the level-1 rider; consumption candidate | s1 | — |
| 41 | `GENHN_PROOF_2026-08-08.md:[GENHN-TOW-1]` | 19 | Items (3)/(4)/(6): open list + consumption candidate | s1 | — |
| 42 | `GENHN_PROOF_2026-08-08.md:[GENHN-HE(μ ≥ 3)]` | 7 | The sigma-law gate left open | s1 | — |
| 43 | `GENHN_PROOF_2026-08-08.md:COROLLARY W-9` | 3 | The twisted-algebra pin explicitly NOT needed | s1 | — |
| 44 | `GENHN_PROOF_2026-08-08.md:GN-REFINE3` | 5 | The pattern the mu2 = 3 kills instantiate one level up | s1 | — |
| 45 | `GENHN_PROOF_2026-08-08.md:T22` | 9 | The (T22)-transport for the second wrap letter | s1 | — |
| 46 | `GENHN_PROOF_2026-08-08.md:GENHN-1` | 11 | The bare `[r1]` node-floor erratum's home | s1 | — |
| 47 | `GENHN_PROOF_2026-08-08.md:W(t) = ⌊(f₂−t)·i(u₂)/e₁⌋` | 1 | The erratum exponent law reproduced by `vartheta_{1,s}` | s1 | — |
| 48 | `GENHN_PROOF_2026-08-08.md:ĉ_t := lift(c_t·η^{W(t)})` | 1 | The erratum's corrected digit (GENTOW5's ASCII `chat_t`) | s1 | — |
| 49 | `HE7_PROOF_2026-08-08.md:ANNEX-DEF HE7-2′` | 6 | The normalizer recursion re-based tower-side | s1 | — |
| 50 | `HE7_PROOF_2026-08-08.md:ANNEX-LEMMA R1-a` | 6 | Clause (iii) = the cocycle letter statement | s1 | — |
| 51 | `HE7_PROOF_2026-08-08.md:ANNEX-THEOREM R1-b` | 4 | (SLOT_i) precedent proof | s1 | — |
| 52 | `HE7_PROOF_2026-08-08.md:ANNEX-THEOREM R1-c` | 3 | (LIFT_i) precedent proof + the bound recursion (s1) / The `bound_{i+1}` recursion's primary source (s2) | s1+s2 | **DEDUP** |
| 53 | `HE7_PROOF_2026-08-08.md:R1.2` | 7 | Monomial identity; item 3 (coherence) and item 7 (twist-blindness) | s1 | — |
| 54 | `HE7_PROOF_2026-08-08.md:R1.3` | 5 | The level-3 machine leg named in the pin stack | s1 | — |
| 55 | `HE7_PROOF_2026-08-08.md:HE7-T-BADTWIST` | 7 | The false stronger claim the S2.3 remark fences off | s1 | — |
| 56 | `HE6_PROOF_2026-08-08.md:LEMMA HE6-1` | 15 | The transport identity in GENTOW5-C's i = 1 base | s1 | — |
| 57 | `JD0_PROOF_2026-08-08.md:J-D0` | 25 | Counts twist-blind / letters re-coordinatize | s1 | — |
| 58 | `GENTOW2_PROOF_2026-08-09.md:[r3 RESTATED]` | 1 | The r3 restatement tag of that law | s2 | — |
| 59 | `GENTOW1_PROOF_2026-08-09.md:S2` | 16 | The GENTOW-1 template re-read at source for the (c) re-index | s2 | — |
| 60 | `GENTOW5_WI_2026-08-10.md:[GENTOW5-W(i)]` | 9 | The companion note claiming the fenced lemma (OPEN-CALL 1) | s2 | — |
| 61 | `CODEX_TOWERRAT2_2026-08-10.md:A-F1` | 3 | RUN A's CRITICAL finding | s2 | — |
| 62 | `CODEX_TOWERRAT2_2026-08-10.md:A-F2` | 2 | RUN A's first GAP (→ the open lemma) | s2 | — |
| 63 | `CODEX_TOWERRAT2_2026-08-10.md:S2` | 6 | The record's GENTOW5 section | s2 | — |
| 64 | `GENTOW2_passPE5_report.md:verifiably admissible` | 1 | Admissibility of `ψ₃^{(w)}` for every `w ∈ K₂^×` | s2 | — |
| 65 | `GENTOW2_passPE6_report.md:w-avatar` | 6 | The first measurements of `w` (≠ 1 at every measured prime) | s2 | — |
| 66 | `runs/cert/D1a_gentow5_output.log:INSUFFICIENT` (2) and `NEW-ISSUE` (2) | 2 / 2 | The two D1a residual findings S12 repairs | s2 | — |
| 67 | `runs/cert3/D3i_gentow5_output.log:NEW-ISSUE` (2) and `DISCHARGED` (2) | 2 / 2 | The twist-index adjudication and the R-i4 discharge | s2 | — |

**Designations counted but NOT emitted as an XREF (3, consolidated, no dedup possible —
each is a distinct clause-letter or composite-string pointer):**

| Candidate designation | Count | Disposition |
|---|---:|---|
| `GENTOW2-A(d)` | 0 (in `GENTOW2_PROOF`) | Parent `THEOREM GENTOW2-A` verified (row 12); clause letter not separately greppable — carried descriptively (s1 `.27`) |
| `LEMMA GENTOW2-B [r3 RESTATED]` (composite) | 0 (in `GENTOW2_PROOF`) | Both components verify (`LEMMA GENTOW2-B` = 30, `[r3 RESTATED]` = 1); referent unique — recorded as GENTOW5's own compression, not an invented designation (s2 `.45`, `.68`) |
| `GENTOW2-A(c)` | 0 (in `GENTOW2_PROOF`) | Parent `THEOREM GENTOW2-A` verified (row 12); clause letter carried descriptively (s2 `.70`) |

**Files verified to exist (path checks, not designations; from shard 2's §3.1):**
`verification/openmath/towerrat2_runA_gentow5_output.txt`,
`verification/openmath/gentow5_af1_direction_check.py` and its `_output.txt`,
`runs/cert2/E12_gentow5_output.log`, `runs/cert2/E12_gentow5_brief.txt`,
`runs/cert3/D3i_gentow5_output.log` — all re-confirmed present at merge time.

### Commit-pin and artifact-freeze verification (rule 23, performed fresh by this merge —
neither shard's own text records having run this)

**39 distinct hex tokens (7–10 hex characters) appear across both shards' text.**
Checked exhaustively with `git cat-file -t <hash>`: **27 resolve to `commit`** (all
real, existing commits — the composition/round/annex/erratum/certification commits named
throughout the arc, e.g. `0160b94` (PE1), `40f313a` (PE2), `39c36aa` (PE3), `b22b37b`
(PE4), `18900e03` (PE5), `cb010522` (the note's own last-touching commit), `9f0eca7`
(PE3's fresh leg W), `75923bc`/`deba21b` (GENTOW2 PE5/PE6), `59c1966` (the GENHN erratum),
`4a613d8`/`a472155` (the HE7 annex-stack acceptance), `87a7b61` (ledger B8),
`e38df9f` (the HETOW acceptance record), `477b1b1` (GT1-r1), `acdf97a` (GENTOW2's own S4
consumer), `4caf0fb` (GENTOW1 HEAD), `dd44d20` (GENTOW2 r1), `33f8620` (GENTOW2 HEAD at
the PE5 fold), `eeac45f6` (the RUN A record), `43b42e9c`/`a803a2ce` (post-acceptance
append commits)). **The remaining 12 do NOT resolve** (`git cat-file -t` reports "not a
valid object name") — these are **artifact/body md5-hash prefixes, not commits**
(`02deb7e0`, `0b850dda`, `4292d8c8`, `503279ef`, `5fa684c7`, `81bbb5db`, `82acd3d2`,
`839a8660`, `85efc5b4`, `d9e6b5ba`, `dc499a49`, `e9c5a20d`), correctly excluded from
commit verification and checked instead as file/body-state fingerprints (below).

**Bonus fresh verification — the four sealed artifacts' current md5s, computed
independently at merge time and compared against every prefix the note cites:**

```
$ md5sum verification/openmath/gentow5_checks.py verification/openmath/gentow5_output_exact.txt \
         verification/openmath/gentow5_output_full.txt verification/openmath/gentow5_rider_f32dev.py
5fa684c74326aea31d2b065b373fcf22  gentow5_checks.py
dc499a4967537d157756905c21104acb  gentow5_output_exact.txt
839a866006f9f6fc341a789c463a763a  gentow5_output_full.txt
81bbb5db3a8a40b211a7f1101d865e91  gentow5_rider_f32dev.py
```

**All four match the 8-character prefixes cited at every one of their occurrences across
both shards, exactly.** This independently confirms freeze predicate (F2) at HEAD — not
merely that the shards agree with each other, but that the artifacts are still
byte-identical to what both shards describe.

**Pin-quality finding (rule 23), distinct from GRTW2's UNPINNED runner-hash finding but
the same species.** Unlike the note-BODY md5s (which the note gives in FULL 32-hex-char
form alongside the 8-char prefix at every byte-freeze-ledger citation — e.g. "`85efc5b4`
(85efc5b445aa2d738301338c6075e118; …)", `.58`, `.73`), **the four sealed ARTIFACT md5s are
truncated to an 8-character prefix at every one of their occurrences in both shards
(never a full 32-hex-char hash anywhere in the note)**. This merge computed the full
current md5 fresh (above) and confirms an exact prefix match at all four, so — unlike
GRTW2's runner hash, which stayed formally UNPINNED — **this merge upgrades the
disposition to VERIFIED-BY-INDEPENDENT-RECOMPUTATION** rather than leaving it merely
plausible: the note's own truncation practice is a stylistic economy, not evidence of an
unchecked claim, now that a fresh full-hash computation confirms it.

### Sample re-verification (10 of 67, grep/exists-rerun at merge time against the working
tree — spanning both shards, both DEDUP and non-DEDUP rows, and the cross-note/external
ledger designations)

`[TABLE — compiler ledger]`

| Target : designation | Recorded | Re-verified | Match |
|---|---:|---:|---|
| `GENTOW1_PROOF_2026-08-09.md:LEMMA GENTOW-2` | 7 | 7 | OK |
| `GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B` (DEDUP) | 30 | 30 | OK |
| `GENHN_PROOF_2026-08-08.md:GENHN-2′` | 3 | 3 | OK |
| `HE7_PROOF_2026-08-08.md:ANNEX-THEOREM R1-c` (DEDUP) | 3 | 3 | OK |
| `HE6_PROOF_2026-08-08.md:LEMMA HE6-1` | 15 | 15 | OK |
| `JD0_PROOF_2026-08-08.md:J-D0` | 25 | 25 | OK |
| `GENTOW5_WI_2026-08-10.md:[GENTOW5-W(i)]` | 9 | 9 | OK |
| `CODEX_TOWERRAT2_2026-08-10.md:A-F1` | 3 | 3 | OK |
| `GENTOW2_passPE6_report.md:w-avatar` | 6 | 6 | OK |
| `runs/cert3/D3i_gentow5_output.log:NEW-ISSUE` / `DISCHARGED` | 2 / 2 | 2 / 2 | OK |

**10/10 sampled targets match exactly — no drift found.** The sample deliberately covers
both DEDUP rows, a Unicode-orthography designation, an in-repo cross-note designation
(`GENTOW5_WI`), an external adversarial-run record, a foreign hostile-pass report, and a
sol-certification log with a two-string composite count. Blob hash of the source note
re-verified identical to the header's pin (§1): no STOP condition triggered.

### Sample statement-quote re-verification (5 of 84, checked verbatim against the source
note `lean/notes/openmath/GENTOW5_PROOF_2026-08-09.md` by line number)

`[TABLE — compiler ledger]`

| Statement | Quoted fragment | Source lines | Match |
|---|---|---|---|
| `.01` (front-matter ARC status) | "**2026-08-09 — SKELETON (per-section commits follow). Unit: GENTOW-5, BOX-CLOSURE campaign wave B1. Grade target 0/2 (attempt; hostile arc owed).**" | 4–6 | OK, byte-exact |
| `.10` (THEOREM GENTOW5-A / S1.3) | "### S1.3 THEOREM GENTOW5-A (the substitution theorem = LEMMA GENTOW-2 layer 1 at general mu2)" | 263 | OK, byte-exact |
| `.27` (clause (a) KEY CERTIFICATE) | "(a) [KEY CERTIFICATE, level-general — GT5-r2 RE-SCOPED (PE2 F-1): the realized residual is the w-TWISTED form] Phi_{i+1} is a key polynomial for nu_i…" | 781 | OK, byte-exact |
| `.56` (dated acceptance record) | "**GENTOW5 IS ACCEPTED 2/2** — passPE4 CLEAN (0 CRITICAL + 0 GAP + 2 MINOR, GENTOW5_passPE4_report.md @ b22b37b; counter 0/2 -> 1/2) followed by passPE5 CLEAN…" | 1673 | OK, byte-exact |
| `.84` (post-D3i corrigendum, the note's final unit) | "**Dated corrigendum (2026-08-12, post-D3i — S12.1's residual-twist index).** The D3i discharge pass (gpt-5.6-sol high, runs/cert3/D3i_gentow5_output.log) adjudicated S12.1 NEW-ISSUE at one index…Awaiting sol re-confirmation in the next queue." | 2299–2313 (note's last line) | OK, byte-exact |

**All 5 sampled quotes are byte-identical to the source note at the cited lines; no drift
introduced by the renumbering pass.** The sample deliberately covers the note's first
statement unit and its last, one theorem statement, one heavily-corrected clause, and the
acceptance record — the widest span the 84-unit inventory offers.

---

## 5. Local supply/consumption ledger

GENTOW5's own protocol (header predicate B, stated in the note's own words, `.42`):
**"Consumption path (not executed here): … the four source notes are byte-untouched by
this unit."** It names four candidate consumption sites for the orchestrator's dated
updates and executes none of them. The table below merges both shards' independent §3.2
tables (shard 1: 6 rows; shard 2: 5 rows = 11 raw) into one consumer-direction ledger,
deduping the one row both shards separately tracked from complementary vantage points
(the `[GENTOW5-W(i)]` reverse edge to `GENTOW5_WI_2026-08-10.md`).

### 5.1 Consumer-direction ledger (mathematical supply versus append/consumption
protocol, kept strictly distinct per the header's predicate split)

`[TABLE — compiler ledger, 11 raw rows → 10 distinct, 1 DEDUP pair]`

| Consumer (candidate) | Exact verified designation | GENTOW5 supply | Mathematical status | Append/consumption-protocol status |
|---|---|---|---|---|
| GENTOW1_PROOF | `GENTOW-BOX-1` (5) | `.10`, `.11`, `.13` | Box RETIRED as a mathematical box; residue grade-only | **Not landed** — "candidates for the orchestrator's dated consumption updates"; source byte-untouched |
| GENTOW1_PROOF | `S3` (14) | `.11` | The S3 grade-note restriction on layer 1 is lifted by COROLLARY GENTOW5-A′ | **Not landed** (same sentence) |
| GENHN_PROOF | `GENHN-BOX-2` (5) | `.12` | The level-1 rider matches the box's stated retirement condition; explicitly "no new claim on frozen text" | **Not landed**; "recording the consumption there is the orchestrator's dated update, not this note's edit" |
| GENHN_PROOF | `[GENHN-TOW-1]` (19) | `.38`, `.41` | Item (6)'s depth ≥ 4 sentence is a candidate; items (3)/(4) are declared still open | **Not landed** |
| GENTOW2_PROOF | `S7` (1) | `.27`, `.33` | The depth ≥ 4 bullet's proviso ((B-1)/(B-2) at level r) is supplied — at i = 2 unconditionally, at i ≥ 3 behind `[GENTOW5-W(i)]` | **Not landed** |
| GENTOW2_PROOF | `LEMMA GENTOW2-B″` (10) | `.27`, `.32`, `.75` | Level-2 law consumed verbatim; the level-i version is NOT reproduced (exactly the gap `[GENTOW5-W(i)]` fences) | No append landed on GENTOW2 by this note |
| **`GENTOW5_WI_2026-08-10.md` (both shards, complementary vantage — DEDUP)** | `[GENTOW5-W(i)]` (9) | **Reverse direction: WI supplies the lemma GENTOW5 fences as open**, governing `.27`–`.29`, `.31` at i ≥ 3 | GENTOW5 says OPEN (fenced at `.68`, S11.2); WI's own title says PROVED | GENTOW5 carries **no** dated append recording WI's discharge — the fence text is unamended at HEAD. Cross-note; see the consolidated OPEN-CALL, §8 |
| `CODEX_TOWERRAT2_2026-08-10.md` | `A-F1` (3), `A-F2` (2) | External adversarial run consumed | 5/5 adjudicated REAL; 4 discharged, A-F2 converted to the open lemma | `.60` is the note-side record; the codex record is byte-separate |
| `runs/cert/D1a_gentow5_output.log` / `runs/cert2/E12_gentow5_output.log` | `INSUFFICIENT` (2), `NEW-ISSUE` (2) | Certification findings consumed | Both residuals repaired at S12 (`.74`–`.83`) | Ledger line inside the note: "row 10 → both residuals repaired, awaiting sol discharge (cert3)" |
| `runs/cert3/D3i_gentow5_output.log` | `NEW-ISSUE` (2), `DISCHARGED` (2) | Certification findings consumed | Twist index corrected (`.84`); R-i4 lift-rung DISCHARGED | Note's last sentence: "Awaiting sol re-confirmation in the next queue." See §8 OPEN-CALL |

**The protocol column is not an inference.** GENTOW5 states its own consumption-path
protocol in its own words (`.42`) and executes none of the four candidates it names;
`.60`'s and `.74`–`.83`'s external-record consumption is likewise never claimed landed on
the external record itself (the D1a/E12/D3i logs and the codex RUN A record are read and
repaired-from, never edited by this note). **Zero dated consumption appends are claimed
landed on any consumer by this note, and none is invented here.**

### 5.2 Reading notes on the external certification chain (not a mathematical supply
edge, carried here because §5's ledger is where cross-note protocol status lives)

The note's OWN terminal words ("row 10 → both residuals repaired, awaiting sol discharge
(cert3)", `.83`; "Awaiting sol re-confirmation in the next queue", `.84`) describe the
certification chain as still pending. `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md`
independently records both as complete: **row 10** ("GENTOW5 … **CERTIFIED 2026-08-12** —
D1a 3/5 + E12 residual repairs (S12 conditionality chain, lift rung) DISCHARGED at D3i +
the ψ_j^{(ω_{j−1})} twist-index corrigendum DISCHARGED at RC2") and **row 18** (the WI
companion note, "**CERTIFIED 2026-08-12** — R10 pass 3: zero findings on all five
charges, sol verdict 'CERTIFIED 2/2'"). Both rows re-verified fresh at merge time (§4's
commit/artifact checks extend to this file-existence check; the exact row text is
grep-matched in §8's OPEN-CALL entries). **This is a status-field question only — no
mathematical statement in the merged inventory turns on which reading is taken** — kept
here as the ledger-side record, cross-referenced from §8's consolidated OPEN-CALLs where
the DAG-level decision is recorded.

---

## 6. TEETH inverse table (unified from both shards; presented as two sub-tables by
shard-of-origin — shard 1 carries the core sealed battery, the depth-4 witness legs, and
the pre-acceptance fresh instruments; shard 2 carries the RUN A isolated re-check, the
rider helper, and the sol-certification chain — with one combined zero-orphan statement
closing both)

### 6.1 Shard 1's core sealed battery, witness legs, and pre-acceptance fresh instruments
(IDs unchanged, offset 0)

`[TABLE — compiler ledger]` Battery row / tooth → guarded unit(s) → disposition.

| Battery row / tooth | Guarded unit(s) | Disposition |
|---|---|---|
| §S5 P-A1 / P-A2 / P-A3 (mu2 = 3 kills, three frames incl. char 3 and K2 = F4) | `.05`, `.10`, `.11`, `.13`, `.30`, `.38` | Executable regression (sealed battery, 86 exact checks) |
| §S5 P-A4 (live-twist mu2 = 2 kill) | `.07`, `.08`, `.09`, `.10` | Executable regression |
| §S5 T-A1W (wrong-height refine) | `.10`, `.37` | Planted mutant; fired as predicted |
| §S5 T-A2W (wrong digit, char 3, surviving pin 33) | `.10`, `.17` | Planted mutant; fired as predicted |
| §S5 T-A4W (the convention tooth — naive-digit twin keeps pin 22) | `.07`, `.08`, `.09`, `.18`, `.40` | Planted mutant; fired — "machine-load-bearing, not decorative" |
| §S4.2/§S5 P-B1 + P-B2 (floor chain tight; recipe side heights = E_i) | `.14`, `.18`, `.31`, `.34` | Executable regression |
| §S4.2/§S5 P-B3 (10 one-sided polygons, char-2 binomial on-chord support) | `.28`, `.29`, `.34`, `.35`, `.36` | Executable regression; also the REFUTING rows (`f32@Phi4`, `Phi4@Phi3`) for the retired (i+2)-pairing |
| §S4.2/§S5 P-B4 (resultant ladders 16,40,84,170,341 / 8,20,42,85) | `.19`, `.34`, `.35`, `.36` | Executable regression (PARI-free integer route) |
| §S4.2/§S5 T-B1 (even-height mutant at the node → drain collapse) | `.35`, `.36`, `.37` | Planted mutant; fired (remainder 0, resultant 0) |
| §S5 P-C1/C2/C3/C4 (PARI leg: factorpadic, nfeltval ladder, refined keys, mutant split) | `.34`, `.36`, `.37` | Executable regression, detached leg; C3's e/deg values disclosed as printed-not-asserted |
| PE1 fresh FR-1 (`gentow5_pe1_fresh.py` @ 0160b94, 15/0) | `.18`, `.26`, `.27`, `.40` | Executable regression on a fresh (unsealed) instrument — the only seam-live recipe row |
| PE2 fresh FR-A / `FA1-LIFT` (`gentow5_pe2_fresh.py` @ 40f313a, 22/0) | `.17`, `.28`, `.32`, `.40`, `.45`, `.46` | Executable regression; asserts the fixed-base flavor's NON-existence and runs the re-solved member |
| PE3 fresh leg W (`gentow5_pe3_fresh.py` @ 9f0eca7) | `.27`, `.38`, `.51` | Measurement (w ≠ 1 at the GA3\* carrier prime, plus GENTOW2 PE6's 6-prime cross-check) |
| PE5 fresh (`gentow5_pe5_fresh.py`, GREEN 40/0) | `.26`, `.29`, `.53`, `.57`, `.58` | Executable regression; instantiates the unclaimed `T_1` TRUE at one frame; first mu = 3 (c)-read; first odd-p proper-(2,2) mid-stage tower at depths 3/4 |
| post-PE4 rider helper (`gentow5_rider_f32dev.py`, 7/0) | `.29`, `.35`, `.36`, `.50`, `.54` | Executable regression on the canonical f32 development |
| §S2.2 worked pins (`n3hat(85)`, `n2hat(21)`) vs `genhnr2_supp.py` L387–389 / `gentow2` W1 | `.15`, `.21`, `.34` | Hand computation cross-checked against committed runner values |
| §S7 F-3 grid-4 equality instance (170 = 170 = 170) | `.24`, `.25` | Signed failure-mode fence (no downstream lean on top-carry strictness exists) |
| GENTOW2 PE4 @ 2f95be6 (B-2 on-the-nose REFUTED at letter-live grades) | `.27`, `.43` | Foreign-note regression consumed as a negative result |
| GENTOW2 PE6 (w measured ≠ 1, 6 primes / 4 frames) + PE5 @ 75923bc (psi^{(w)} admissible for every w) | `.27`, `.38`, `.45` | Foreign-note measurement + verification |

**Both-direction audit (shard-1 range).** Every row guards at least one unit; every
toothed unit appears. Units with **`TEETH: NONE`** — `.03`, `.23`, `.39`, `.41`, `.42` —
are headlines, declarations, hypotheses, fences or negative claims. **Zero battery-row
orphans; zero toothed-unit orphans in shard 1's range.** One out-of-range tooth was
recorded but not counted in shard 1's own table: S11.1's isolated
`gentow5_af1_direction_check.py`, which guards the corrected direction of `.25` and is
now itself homed at **`.61`–`.66`** in the merged inventory (§6.2 below resolves the
cross-reference shard 1's own text left as "homed in shard 2").

### 6.2 Shard 2's RUN A isolated re-check, rider helper, and sol-certification chain
(renumbered, `.44`–`.84`)

`[TABLE — compiler ledger]`

| Battery row / tooth | Guarded unit(s) | Disposition |
|---|---|---|
| `gentow5_af1_direction_check.py` C1 (interior rung) | `.61` | Executable regression, ISOLATED re-check (not the sealed battery) — **this is the tooth shard 1's own `.25` cites as "homed in shard 2"** |
| C2 (the 85 → 84 drop at floor rung 3's tight margin) | `.61`, `.65` | Executable regression |
| C3 (170 top-rung preservation) | `.61`, `.62` | Executable regression |
| C4 (forward nondecreasing) | `.62`, `.63` | Executable regression |
| C5 (exact `Z[x]` identity + canonical `Phi_1`-adic development of `Phi_3`) | `.64` | Executable regression |
| C6 (level-1 polygon / descmin = 10) | `.64` | Executable regression |
| C7 (the rho-ladder `rho = (0, 1/8, 1/8)`, strict at rung 2: 21 > 20) | `.65` | Executable regression |
| C8 (margin instance `43/4 − 1/2 = 41/4 > 10`) | `.66` | Executable regression |
| `gentow5_rider_f32dev.py` (7 checks / 0 violations: halfway identity, completion relation, canonical dev, slot legality, pins vs the byte-frozen artifact row, chord clearance 186 > 170, `Phi_4@Phi_2` already canonical) | `.50`, `.54` | Executable regression, rider helper |
| P-B3 committed rows `f32@Phi4`, `Phi4@Phi3` (pins `[682,inf,0]`, `[170,inf,0]`) | `.50` | Executable regression used as a REFUTATION of the composed (i+2)-pairing |
| P-B3 committed rows `f32@Phi3`, `Phi4@Phi2` (pins `[340,inf,186,inf,0]`, `[84,inf,50,inf,0]`) | `.50`, `.72` | Executable regression VERIFYING the corrected pairing and the re-indexed residual |
| `FA1-LIFT` (`gentow5_pe2_fresh.py` @ 40f313a, 22/0) | `.45`, `.46` | Executable regression; asserts a non-existence and runs the re-solved member |
| PE5 fresh route (`gentow5_pe5_fresh.py`, GREEN 40/0; first mu = 3 (c)-read; first odd-p proper-(2,2) mid-stage tower at depths 3 and 4) | `.53`, `.57`, `.58` | Executable regression on a fresh instrument |
| PE3 fresh leg W (`gentow5_pe3_fresh.py` @ 9f0eca7) + GENTOW2 PE6 (`w-avatar`, 6 hits; fresh route GREEN 68/0, seal ade1727) | `.51` | Measurement (7 primes; `w ≠ 1` at each) |
| GENTOW2 PE5 @ 75923bc (`verifiably admissible`, 1 hit) | `.45` | Foreign-note verification of admissibility at every `w` |
| Byte-freeze / prefix-md5 discipline (S11.6 two commits; the acceptance-round ledger `+77/-0`, prefix md5 `e9c5a20d` at L561) | `.59`, `.73` | Document-integrity check (append-only proof) — **cross-checked fresh at this merge (§4): the four sealed artifacts' current md5s match every cited prefix exactly** |
| Grep audits: S11.1's three-string closure audit; PE4-F-1's `T_1 / kappa_1 / psi_1^mu / level-0 read` audit; S11.3's w_1-consumer audit | `.53`, `.67`, `.70` | Signed non-applicability (negative checks) |
| Orchestrator re-computation of `(bound_1..bound_4) = (1,7,35,155)` vs heights `(5,21,85,341)` | `.79`, `.80`, `.81`, `.83` | Hand computation, independently re-run before transcription |
| D1a → E12 → D3i certification chain (`INSUFFICIENT`/`NEW-ISSUE`/`DISCHARGED` labels grep-verified in the logs) | `.74`–`.78`, `.84` | Decorrelated-model adversarial certification |

**Both-direction audit (shard-2 range).** Every row guards at least one unit; every
toothed unit appears. Units with **`TEETH: NONE`** — `.52`, `.55`, `.68`, `.69`, `.74`,
`.75`, `.76`, `.84` — are conditionality declarations, pointer hygiene, or index
corrections with no machine leg; the note says so explicitly for the two that matter
("the machine record does not discriminate this fence", `.69`; and `.68`). **Zero
orphans in shard 2's range.**

### 6.3 Combined zero-orphan statement

**Both-direction audit, unified across all 84 units.** Every battery row in either
sub-table guards at least one unit in the merged inventory; every unit whose `TEETH`
field names a battery row appears in some row above. Combining both shards'
`TEETH: NONE` lists — `.03`, `.23`, `.39`, `.41`, `.42` (shard 1) and `.52`, `.55`, `.68`,
`.69`, `.74`, `.75`, `.76`, `.84` (shard 2, renumbered) — gives **13 declaration/fence/
status/conditionality units outside the orphan count**. **Zero battery-row orphans; zero
toothed-unit orphans across all 84 units.** The one cross-shard pointer shard 1 left
unresolved ("homed in shard 2") is closed here: `gentow5_af1_direction_check.py` lives at
`.61`–`.66` in the merged inventory, and every one of its eight lettered checks (C1–C8)
is accounted for in §6.2's rows.

---

## 7. SERIES, CHAINs, cross-shard supersession edges, and boundary resolution

### 7.1 On the SERIES construct (rule 28) — not applied by either shard; flagged, not
silently supplied

Unlike `spec/EFF-GRTW2.md`'s merge (whose GRTW2-GRADE-ARC SERIES was built by the SHARDS
themselves, across their own CONDITIONALITY fields, before the merge assembled it),
**neither GENTOW5 shard uses the word "SERIES" or applies rule 28's vocabulary anywhere**
(`grep -n SERIES` returns nothing in either shard). This is a genuine gap against the
template, not a finding this merge can silently fill in as if it were shard-sourced. The
note's own `.57` ("The arc in one breath") IS exactly the chronological dated-entry
construct rule 28 targets — seal → PE1 → r1 → PE2 → r2 → PE3 → r3 → PE4 (CLEAN) → rider →
PE5 (CLEAN) — so this merge **constructs the arc here as a compiler addition**, explicitly
marked as such rather than presented as a shard finding:

`[TABLE — compiler-constructed, GENTOW5-GRADE-ARC, 6 links, TERMINAL — not sourced from
either shard's own SERIES vocabulary since neither shard used it]`

| Link | Unit | Grade movement | Content |
|---:|---|---|---|
| 1 (origin) | `.01` | **0/2** | "Grade target 0/2 (attempt; hostile arc owed)"; PE1 NOT CLEAN recorded in the same unit's ARC chronology |
| 2 | `.43` | **stays 0/2** | §S7 PE1 repair record: "Grade: 0/2 UNCHANGED (this is a repair round, not a pass); PE2 next" |
| 3 | `.44` | **stays 0/2** | §S8 PE2 repair record head: PE2 NOT CLEAN (0C+2G+2m) |
| 4 | `.49` | **stays 0/2** | §S9 PE3 repair record head: PE3 NOT CLEAN (0C+1G+2m) |
| 5 | `.53`/`.55` | **0/2 → 1/2** | §S10 post-PE4 fold: PE4 CLEAN (0C+0G+2m) — "the arc's first clean pass" |
| 6 (**TERMINAL**) | `.56` | **1/2 → 2/2, ACCEPTED** | Dated acceptance record: PE5 CLEAN (0C+0G+3m) — "two consecutive clean hostile passes, the standing acceptance bar" |

**Six links, no gap, no duplicate — verified by an exhaustive scan of every "counter"/
"grade"/"CLEAN"/"ACCEPTED" sentence in the 84-unit merged inventory for a competing grade
transition; none exists outside these six.** `.57`'s own "arc in one breath" restates
exactly this six-step chronology in one sentence (plus internal detail at each repair
round), confirming the six links independently rather than adding a seventh. **This merge
flags, as template feedback, that GENTOW5 is a second confirmed instance (after GRTW2) of
a dated grade-arc that a compiler can reconstruct mechanically even where the source note
never names the construct** — a candidate argument for making rule 28's SERIES
recognition a compiler duty rather than a shard-discretionary one.

### 7.2 Cross-shard supersession edges (consolidated, with SUPERSESSION KIND)

Every PE2-F-\*/PE3-F-\*/PE4-F-\*/A-F\*/R-i\* item targeting a base sentence homed in shard
1 is HOMED in shard 2 (its drafting/append location, per rule 7 — the same rule
GRTW2/HE7/HE3/T1 used). The table below lists every such edge using the vocabulary already
exercised throughout the merged inventory: **replacement | license | scope-pin |
provenance-rider | as-of scoping | inventory completion | withdrawal**.

`[TABLE — compiler ledger, consolidated from both shards' own RESOLUTION TRACE fields]`

| From | To | Kind | Content |
|---|---|---|---|
| `.45` (PE2-F-1) | `.27` | replacement | Clause (a)'s realized residual RE-SCOPED from "psi_{i+1}" to the w-TWISTED "psi_{i+1}^{(w_i)}" — the landed GENTOW2 r3 B-law applied at the pinned digits |
| `.46` (PE2-F-2) | `.17` | replacement | The K_i-digit-lift display's fixed-base flavor construction replaced by the per-flavor base re-solve (FR-A's numerical falsification of the fixed-base reading) |
| `.47` (PE2-F-3) | `.25` | wording-rider | States the i = 1 edge of LEMMA GENTOW5-D explicitly (the x-carry IS the top carry there); declared "unconsumed" — no named consumer instantiates i = 1 |
| `.48` (PE2-F-4) | `.40` | scope-pin | Names the compound seam-live × e_stage ≥ 2 coverage gap explicitly (no committed row) |
| `.50` (PE3-F-1) | `.29` | replacement | Clause (c)'s entry-read RE-INDEXED to the uniform GENTOW-1 transport (index i+1, not i+2); the composed (i+2)-read pairing REFUTED by the residual-degree count and at committed P-B3 rows |
| `.51` (PE3-F-2) | `.27`, `.38` | as-of scoping | Dates the word "uncomputed" (w) at both flank sites — measured ≠ 1 at 7 primes as of GENTOW2 PE6 + this note's own PE3 leg W; does not close `w_i = 1` |
| `.52` (PE3-F-3) | `.32` | provenance-rider | Pointer-hygiene correction: the S4-witness w-triviality record repointed at the correct rider, separated from the coverage box's seam axis |
| `.53` (PE4-F-1) | `.29`, `.31` | scope-pin | States the honest index scope explicitly: clauses (c)/(e) claimed at i ≥ 1 only (T_1 left unclaimed rather than cited) — a scope the r3 proof already had |
| `.58` (companion fold, PE5-F-1) | `.26` | inventory completion | Completes the INDEX-0 SCOPE bracket for clauses (a)/(b)/(d), alongside PE4-F-1's existing (c)/(e) scoping |
| `.58` (companion fold, PE5-F-2) | `.27` | inventory completion → **later superseded, see CHAIN-1 below** | Adds the i = 1 line to clause (a)'s discharge (a fixed z_1-letter-power species), with the disclaimer "an exponent-level tie … is NOT claimed" |
| `.58` (companion fold, PE5-F-3) | `.22` | replacement | Restores the truncated `(LIFT_i)` bound-recursion token ("e...") to `e_{i+1}*bound_i`, re-derived from `ANNEX-THEOREM R1-c`, not from memory |
| `.61` (S11.1, A-F1 CRITICAL) | `.25` | replacement | WITHDRAWS "the converse rewriting is weight-nondecreasing" (FALSE as written) and the two-directional grid-closure consequence clause; replaces with the one-directional (weight-NONINCREASING converse, forward-nondecreasing statement unchanged) reading, proved at `.62`–`.67` |
| `.66` (S11.1.3) | `.29` | replacement | Replaces clause (c) Step 2's "both grids agree on 'above'" parenthetical with the one-directional aboveness argument (consumes clause (b), hence conditional at n ≥ 3 per `.75`) |
| `.68` (S11.2, A-F2 GAP) | `.27`, `.28`, `.29`, `.31` | scope-pin | Declares `[GENTOW5-W(i)]` an OPEN transported lemma at i ≥ 3, fencing clause (a)'s single-w geometric form; the note's own "not-conditional" list for (b)/(c)/(e) at this link is itself narrower than what survives — **see the next row** |
| `.74`/`.75` (S12.1, R-i2) | `.27`, `.28`, `.29`, `.31` | withdrawal (of `.68`'s "unaffected scope" list) + scope-pin (the corrected, wider conditionality) | WITHDRAWS `.68`'s claim that exact values/repo-side classes/P-membership/(c)/(e) remain unconditional at i ≥ 3; establishes that ALL of clauses (a)/(b)/(c)/(e) are conditional on `𝒲_{≤n}` at n ≥ 3 |
| `.78` (S12.2, R-i4) | `.17` | replacement | CORRECTS the lift-rung threshold: `lift_i(c;m)` realizes `K_i` (degree `< D_i`), hence its threshold is `bound_i`, not `bound_{i+1}` — supersedes shard 2's own `.71` (S11.4), which had asserted the wrong rung |
| `.80` (S12.2, recipe-range discharge) | `.18`, `.25` | license | Discharges the range obligation for every actual recipe-lift consumer: `m_t = s·u_{i+1} > bound_i` always, so no qualification of the recipe or `(INV-j)` display is needed |
| `.82` (S12.2, refine consumers) | `.10`, `.30` | license | Discharges the lift-range obligation for THEOREM GENTOW5-A and clause (d)'s refine lifts: `λ > E_{i+1} > bound_{i+1}` by the boxed inequality |
| `.84` (post-D3i corrigendum) | `.28` (via `.75` item 2) | replacement | Fixes the twist INDEX on clause (b)'s corrected residual display: `ψ_j^{(ω_j)}` read as `ψ_j^{(ω_{j−1})}` — the display as first written over-demanded `w_{n+1}`, exceeding `𝒲_{≤n}` |

**Nineteen rows, every one resolving to a unit that exists in the merged inventory; zero
dangling targets** (verified by scanning every `To` entry against the 84-unit ID range).
Three targets receive more than one edge (`.25`: PE2-F-3 wording-rider + S11.1 replacement;
`.27`: PE2-F-1 + companion-fold PE5-F-2 + S11.2 scope-pin; `.29`: PE3-F-1 + PE4-F-1 +
S11.1.3) — each is a genuine multi-link CHAIN, resolved with an explicit TERMINAL below
(§7.3), not left as competing undated edges.

### 7.3 CHAINs with TERMINAL markers (rule 25/30)

**CHAIN-1 — clause (a) at i = 1.** `.27` (base, general i ≥ 1 form) → `.58`/PE5-F-2 (adds
the i = 1 line: "a psi_2^{(u)} with u a fixed z_1-letter power") → `.70` (S11.3,
RE-SCOPES: the fold's own disclaimer — "an exponent-level tie … is NOT claimed" — is
adjudicated correct, and the *identification* with the pinned `w_1` is OPEN; only the
*species* is proved). **TERMINAL: `.70`.** Three-membered, matching the note's own three
citations of the same fact (the fold's own disclaimer, S11.3's adjudication, and the
"net position" summary at `.70` itself).

**CHAIN-2 — the lift-rung threshold.** `.17` (base K_i-digit-lift display) → `.46`
(PE2-F-2, per-flavor re-solve) → `.71` (S11.4, asserts `bound_{i+1}`) → `.78` (S12.2,
WITHDRAWS `.71`'s threshold, correct = `bound_i`). **TERMINAL: `.78`**, with `.80`/`.82`
as its downstream discharge (every actual consumer confirmed in-range).

**CHAIN-3 — LEMMA GENTOW5-D's converse direction.** `.25` (base: "the converse rewriting
… is weight-nondecreasing … the two-directional rewriting closes") → `.61` (S11.1,
A-F1 CRITICAL: FALSE as written, WITHDRAWN) → `.62`–`.67` (the one-directional repair:
what survives, the consumption walk, and the three numbered sub-lemmas S11.1.1–S11.1.3).
**TERMINAL: `.61`'s corrected statement, proved by `.62`–`.67`.**

**CHAIN-4 — the `[GENTOW5-W(i)]` conditionality (the special-instruction chain; full
citation detail is consolidated in §8's OPEN-CALL, not repeated here).** `.27`/`.28`/`.29`/
`.31` (base) → `.68` (S11.2, A-F2: fences (a) at i ≥ 3, states a NARROWER not-conditional
list for (b)/(c)/(e)) → `.74`/`.75` (S12.1, R-i2: WITHDRAWS the narrower list, establishes
ALL of (a)/(b)/(c)/(e) conditional on `𝒲_{≤n}`) → `.84` (post-D3i: fixes the twist INDEX
of the propagated form). **TERMINAL: `.75` (the clause-by-clause scope) as corrected by
`.84` (the index).** The lemma itself, `[GENTOW5-W(i)]`, remains OPEN at HEAD in this
note's own text — the chain's TERMINAL is a conditionality reading, not a discharge.

**CHAIN-5 — clause (c)'s entry-read (rule 30, TWO TERMINALS by consumer class).** `.29`
(base: the composed `(i+2)`-anchored entry-read pairing) → `.50` (PE3-F-1, RE-INDEXED to
the uniform GENTOW-1 transport at index i+1, refuting the composed pairing) → `.53`
(PE4-F-1, the honest index SCOPE: claimed at i ≥ 1 only) → `.66` (S11.1.3, the repaired
Step 2 aboveness argument, one-directional). **This chain has two TERMINALs governing
different consumer classes, per rule 30**: **`.53` is TERMINAL for index-scope
consumers** (which indices does clause (c) cover — the answer a chapter cut needs to know
before citing the clause at all), while **`.66` is TERMINAL for proof-mechanism
consumers** (how Step 2's aboveness is actually established, needed only by a reader
re-deriving or re-checking the proof itself). A merge that installed only one of these
would misstate the other consumer class exactly as rule 30's GENIND precedent warns.

**Uniqueness verified for CHAINs 1–3:** an exhaustive scan of every CONDITIONALITY and
RESOLUTION TRACE field naming `.25`, `.17`, and `.27`'s i = 1 clause as a supersession
TARGET confirms no fourth-layer correction exists anywhere in the 84-unit merged inventory
beyond what is listed above.

### 7.4 Boundary-unit resolution (merge rule 4/7)

Per rule 7 (HOME follows edit destination, not drafting location), all nineteen edges
above are **HOMED in shard 2** even though most target shard-1-HOME units. **Verified:
none of the nineteen edge-source units is duplicated as a second unit inside shard 1's
range** — an exhaustive scan of the merged inventory's 84 unit headers (§3) confirms
`.44`–`.84` appear exactly once each, and no unit numbered `.01`–`.43` independently
re-states any repair-round finding, acceptance-record content, or dated-append correction
as its own content (they are only *cited*, by ID, from the shard-1-HOME units they
target, via each unit's own CONDITIONALITY/RESOLUTION TRACE). Symmetrically, shard 1's own
§6 BOUNDARY SELF-AUDIT records no unit drafted in shard 2 but homed in shard 1 — the
traffic is entirely one-directional (shard 2 → shard 1), matching every precedent merge
in this campaign.

### 7.5 Range-edge audit

Both shards independently record the same clean physical break: shard 1's own note —
"line 1473 is S7's closing sentence … line 1474 is blank and line 1475 opens `## S8`" —
and shard 2's own note — "line 1475 opens `## S8` (line 1474 is blank; S7 closes at 1473
in shard 1)". **Both descriptions name the identical boundary (1474/1475) and agree it
falls on a section break.** The file's own end (source line 2313) is shard 2's own last
line, the post-D3i corrigendum's closing sentence ("Awaiting sol re-confirmation in the
next queue."), independently confirmed against the working-tree file at merge time (§4's
quote sample). **Zero units span the shard boundary.**

---

## 8. Self-audit and OPEN-CALLs

**6 raw OPEN-CALLs (3 shard 1 + 3 shard 2) carry forward as 4 distinct — two dedup
pairs, both justified below** (unlike GRTW2's merge, where two substantively-close pairs
were flagged as related but explicitly NOT merged because neither shard self-flagged the
duplication; here one pair is merged under this task's own explicit special instruction,
and the second pair IS self-flagged by shard 2's own closing sentence).

### OPEN-CALL 1 (shard 1) — the `ITER-LAW` designation is not in the note it is
attributed to

LEMMA GENTOW5-A1's proof (`.08`) sources the first wrap letter as "z1 by GENHN's S4
level-1 cocycle (accepted; the ITER-LAW z-letter)". Fixed-string grep for `ITER-LAW` in
`GENHN_PROOF_2026-08-08.md` returns **0** (re-verified fresh at merge time). The
designation does exist in the corpus — `DITER_RESTATE_2026-08-08.md` (16) and
`GRTJC_PROOF_2026-08-08.md` (5) — but attributing it to GENHN's S4 cannot be verified,
and no XREF is emitted for it. The verified part of the same sentence (`T22`, count 9 in
GENHN_PROOF, for the second wrap letter) is emitted. **Decision needed:** whether the
z-letter's supplier for this note is GENHN's S4 cocycle (designation unnamed there) or the
DITER `ITER-LAW` unit. Carried unresolved, per shard 1's own disposition.

### OPEN-CALL 2 — `[GENTOW5-W(i)]`: note-internal OPEN versus corpus-level PROVED/CERTIFIED
(CONSOLIDATED from shard 1's OPEN-CALL 2 and shard 2's OPEN-CALL 1 — the same question from
each shard's own vantage point, per this merge's special instruction)

`.68` (S11.2) declares `[GENTOW5-W(i)]` "an OPEN transported lemma, the honest-sorry
analogue", and `.75` (S12.1) propagates that conditional through clauses (a) ⟹ (b) ⟹
`.64`/`.66` (S11.1.1/S11.1.3) ⟹ (c) ⟹ (e) at every index n ≥ 3 — the governing
conditionality for `.27`, `.28`, `.29`, `.31`, and hence for `.04`'s status row and `.38`'s
supply set. **Three distinct citations are in play, all re-verified fresh at this merge,
and all three are carried forward intact:**

(a) **The note's own text**: `[GENTOW5-W(i)]` is declared an OPEN transported lemma at
S11.2 (`.68`, "the honest-sorry analogue"), propagated by S12.1 (`.75`).

(b) **`lean/notes/openmath/GENTOW5_WI_2026-08-10.md`'s own title line** reads "**[GENTOW5-W(i)]
— the i >= 3 monomial form of the B''-transport, PROVED**". Both shards cite the
designation's count in that file as 9; **re-verified fresh at this merge**
(`grep -cF '[GENTOW5-W(i)]' lean/notes/openmath/GENTOW5_WI_2026-08-10.md` = **9**, exact
match).

(c) **`docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` row 18** records the WI note as
**CERTIFIED 2026-08-12** ("R10 pass 3: zero findings on all five charges, sol verdict
'CERTIFIED 2/2'"). **Re-verified fresh at this merge**: row 18 reads "| 18 | WI
([GENTOW5-W(i)]) | r1 landed; sol PE2 was the challenge | **CERTIFIED 2026-08-12** — R10
pass 3: zero findings on all five charges, sol verdict 'CERTIFIED 2/2' …" — present and
matching.

**Correction to this merge's own charge, recorded honestly rather than silently
absorbed**: the charge that produced this merge asserted citation (c) "appears ONLY in
shard 1's OPEN-CALL 2, NOT in shard 2's OPEN-CALL 1." **A fresh read of both shard files
shows this premise is not quite right: shard 2's own OPEN-CALL 1 independently carries the
identical row-18 reading note** ("Reading note (external records, not edits):
`docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` row 18 records the WI note as CERTIFIED
2026-08-12 …"). **Both shards, independently, already cite all three sources** — which
strengthens rather than weakens the case for carrying all three forward; nothing was at
risk of being dropped either way, and this merge flags the discrepancy between the
charge's premise and the source text per the same "book it, don't paper over it" standing
discipline that governs rule-39 self-count checks.

Compiling what the NOTE says leaves every i ≥ 3 clause conditional; compiling the corpus
would discharge it. **This is a DAG decision above the compiler** (the T3 precedent's
"PERIMETER-UNRESOLVED → cross-spec reconciliation" shape, as shard 1 named it). **No
silent choice is made here**: every affected unit (`.04`, `.27`, `.28`, `.29`, `.31`,
`.38`, `.68`, `.74`, `.75`) carries the note's own conditional reading, and this call
records the alternative and both external certifications without resolving the DAG
question. It is the single largest downstream consequence in this merge, since it decides
whether THEOREM GENTOW5-B is a conditional or an unconditional supply at depth ≥ 3.

### OPEN-CALL 3 — the floor chain's provenance: datum hypothesis or derived consequence
(CONSOLIDATED — shard 2 self-flags this as "one call, recorded in both shards", the
explicit dedup trigger this merge's standing charge requires)

`.14` states the floor chain `u_{i+1} > e_{i+1} E_i` as part of DEF GENTOW5-1, with
provenance "the level-i budgets' node corollary, S3(e)"; clause (e) (`.31`) derives the
next floor from clause (c)'s pins; and `.75` (S12.1 item 4) makes (e) at n ≥ 3 conditional
on `𝒲_{≤n}`, adding that the inequality "may still be used unconditionally when it is
included explicitly in the fixed tower datum; only its claimed automatic derivation from
the recipe is conditional." `.77` (S12.1's unaffected-scope list) qualifies LEMMA
GENTOW5-D as unaffected "under an explicitly supplied floor-chain datum." **Which framing
the effective spec should carry — floor chain as a DATUM hypothesis (unconditional, but
then the induction does not "feed itself") or as a DERIVED consequence (conditional at
n ≥ 3) — is not settled by the note's own text**, which uses both framings; shard 2's own
closing sentence ("Shard 1 raises the same call from the DEF side; it is one call,
recorded in both shards") is the self-flag that triggers this merge's dedup, per the
standing charge's instruction to merge only self-flagged duplicate pairs. Rung 1 is
unproblematic either way (it rides the accepted `[r1]` node floor directly).

### OPEN-CALL 4 (shard 2) — the note's terminal protocol state versus the external ledger

The note's last sentence is "Awaiting sol re-confirmation in the next queue." (`.84`), and
`.83`'s provenance parenthetical records "Ledger: row 10 → both residuals repaired,
awaiting sol discharge (cert3)." The external ledger, however, records the step as
complete: `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` row 10 reads "**CERTIFIED
2026-08-12** — D1a 3/5 + E12 residual repairs (S12 conditionality chain, lift rung)
DISCHARGED at D3i + the ψ_j^{(ω_{j−1})} twist-index corrigendum DISCHARGED at RC2"
(re-verified fresh at this merge, present and matching). **Decision needed:** whether the
effective spec's certification field takes the note's own text (awaiting) or the ledger
(certified). Compiled here as the note states it, with the ledger recorded as a reading
note (§5.2). **This is a status field only — no mathematical statement turns on it**,
distinct from OPEN-CALL 2 above (which decides a mathematical conditionality, not merely a
certification-protocol label).

### Recorded source defects (flagged, not silently repaired; 7 raw from the two shards,
one dedup'd — the S11.4 bracket mis-pointer, described from each shard's own vantage — =
6 distinct)

1. **`.34` (S4.1):** the parenthetical "m\* = 4\*341/4..." is a truncated token in the
   source, of the same species as the `(LIFT_i)` bound's "e..." which PE5-F-3 (`.58`)
   restored. No later round repairs it. The sentence's arithmetic conclusion is complete
   without it (`m* > e*E_4 = 340`, minimal odd `341`, machine-confirmed at P-B4/P-C2).
2. **`.17`/`.71` (DEDUP'd across both shards):** S11.4's bracket is addressed to "the
   S2.2 K_i-digit-lifts display", but the `lift_i(c; m)` display is homed in §S2.1 (§S2.2
   is the consistency-checks section). Shard 1 records this from the target side (its
   own `.17`); shard 2 records it from the bracket's own drafting side (its own `.71`,
   S11.4) — the same mis-pointer, described from each shard's own vantage, consolidated
   into one defect here. The referent is unique in the note, so the bracket is applied to
   the §S2.1 display regardless; `.78` (S12.2), which supersedes the bracket, refers to it
   without a section number either.
3. **`.27`:** the clause-level references `GENTOW2-A(d)` and `HE7 ANNEX R R1.2 item 3` are
   sub-designation pointers: the parent designations are verified (`THEOREM GENTOW2-A` =
   8; `R1.2` = 7) but the clause/item letters are not separately greppable. Carried
   descriptively.
4. **`.70`:** the clause pointer `GENTOW2-A(c)` is likewise not separately greppable
   (count 0); the parent `THEOREM GENTOW2-A` is verified (count 8, row 12 of §4). A
   **different clause letter from defect 3** ((c) versus (d)) — not itself a duplicate of
   it, kept as a separate row.
5. **`.45`, `.68`:** the composite designation `LEMMA GENTOW2-B [r3 RESTATED]` does not
   occur verbatim in `GENTOW2_PROOF_2026-08-09.md` (count 0); both components do (`LEMMA
   GENTOW2-B` = 30, `[r3 RESTATED]` = 1). Recorded as the note's own compression, not
   emitted as a designation.
6. **`.83`:** the provenance sentence attributes the finding labels "INSUFFICIENT finding
   2" and "NEW-ISSUE finding 4" to D1a while naming the E12 log as the deriving run; grep
   confirms the labels live in `runs/cert/D1a_gentow5_output.log` (2 each) and are
   restated in `runs/cert2/E12_gentow5_brief.txt`, not in the E12 output log itself (0
   each). **The attribution as written is correct** — this is a positive verification
   finding shard 2 chose to record alongside its defects, kept here in that spirit rather
   than reclassified, since the cross-read need not re-derive it.

### Fidelity audit

- Every CANONICAL STATEMENT across all 84 units is either a verbatim source quotation or
  explicitly marked `[ASSEMBLED]` under the same fidelity rules both shards used; no
  inverse, sign, quantifier, index, level, or implication direction was altered anywhere,
  in either the original shard compilations or this merge's renumbering pass — which
  matters unusually here, since the arc contains a genuine direction reversal (`.25`'s
  converse-rewriting CRITICAL, CHAIN-3) and its quoted correction, both reproduced with
  their strike/withdrawal markers intact.
- The one source table (`.04`, the STATUS TABLE) is marked `[TABLE]`; §S12's LaTeX
  displays (`.74`–`.84`) are reproduced as LaTeX, matching the note's own notational
  switch there; no source table was prosified at merge time.
- **67 distinct external XREF/artifact targets** (from 77 raw citations, ten clean DEDUPs
  — §4) have fixed-string counts ≥ 1 or verified presence, with **zero mismatches found**
  in a 10-target fresh re-sample (§4) — unlike `spec/EFF-HE3.md`'s merge, which found a
  genuine count error. A 5-quote sample was re-checked verbatim against the source note
  by line number and matched byte-exact (§4). **27 distinct commit hashes** were
  independently confirmed real commits via `git cat-file -t` (§4); the four sealed
  artifacts' current md5s were independently recomputed and match every cited prefix
  exactly (§4) — a positive finding beyond what either shard's own text records.
- **The ID-renumbering rewrite was performed unit by unit against this compiler's own
  reading of both shards' full text** (not a blind global substitution), under the
  simplest disambiguation shape found in this campaign to date: **zero bare `` `.NN` ``
  cross-shard citations exist in either direction** (§1's SHARD-MAP), so the rewrite
  reduces to a uniform +43 shift on shard 2 with nothing to protect (rule 37's guard
  applies to zero tokens; rule 38's audit table has zero rows). An exhaustive regex sweep
  confirms **zero leftover `sKof2` substrings within the merged statement inventory (§3)**
  and **zero out-of-range renumbered IDs** (every resolved `` `.NN` `` token lies in 1–84).
- **Rule-39 fresh self-count check found no discrepancy** in this merge (§1) — statement
  counts, XREF-row counts, and OPEN-CALL counts all reproduce both shards' own stated
  tallies exactly, unlike `spec/EFF-LIFTCORNER.md`'s and `spec/EFF-GRTW2.md`'s merges,
  each of which found a genuine one.
- **Nineteen cross-shard supersession edges are consolidated (§7.2), organized into five
  named CHAINs (§7.3), one of which (CHAIN-5) carries two TERMINALs by consumer class per
  rule 30** — the same shape rule 30's GENIND precedent established, confirmed
  independently here rather than assumed.
- **Six raw OPEN-CALLs carry forward as four distinct** — two dedup pairs: one under this
  merge's own special instruction (the `[GENTOW5-W(i)]` thread, OPEN-CALL 2 above,
  carrying all three citations from both shards' own vantage points, with the charge's
  premise about citation (c)'s exclusivity corrected rather than silently reproduced), and
  one self-flagged by shard 2's own text (the floor-chain provenance question, OPEN-CALL 3
  above).
- **Every `[GENTOW5-W(i)]` STATUS/CONDITIONALITY row is carried byte-verbatim or
  `[ASSEMBLED]`-flagged**, per the special instruction: `.27`, `.28`, `.29`, `.31` (the
  base clauses), `.68` (S11.2's fence), `.74`/`.75` (S12.1's withdrawal and corrected
  scope), and `.84` (the post-D3i twist-index correction) all reproduce their source text
  without paraphrase or compression — verified by re-reading each unit's CANONICAL
  STATEMENT against the transformed shard text before assembly.
- **Honest limitation of this merge, stated once:** the per-boundary reasoning in each
  shard's own §6 (which unit-boundary candidate was chosen and why) is not reproduced here
  in full — only the format-level conclusions (§7.1's SERIES-construction finding, the
  CHAIN/TERMINAL vocabulary, the cross-shard edge list) survive here. A reader who needs
  the per-boundary reasoning for a specific unit should consult that unit's home shard file
  directly (`spec/EFF-GENTOW5-s1of2.md` for `.01`–`.43`, `spec/EFF-GENTOW5-s2of2.md` for
  `.44`–`.84`); the shard files are retained for exactly this purpose (§1). **Codex
  cross-read remains owed** (header) — this merge performed the fold, the fresh-verification
  passes, and the commit/artifact audits, not the adversarial read.

---

EFF-GENTOW5 MERGED: 84 statements / 67 xrefs / 4 open calls
