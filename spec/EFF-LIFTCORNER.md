# EFF-LIFTCORNER — CANONICAL EFFECTIVE-SPECIFICATION (MERGED)

**COMPILED-BY: opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). CODEX CROSS-READ OWED (post-reset) — neither shard, and no fold performed by this merge run, has been through an adversarial pass; that obligation is inherited whole.**

## 1. Merge header

**Source note:** `lean/notes/openmath/LIFTCORNER_2026-08-08.md` (2,083 lines / 133,230 bytes).

**HEAD blob hash:** `d93c2aa253cdf5192f2e1525aa9f7b412b85b925` — cited identically by both source
shards' headers, and independently confirmed by fresh `git hash-object` against the
working-tree file at merge time (2026-08-14):

```
$ git hash-object lean/notes/openmath/LIFTCORNER_2026-08-08.md
d93c2aa253cdf5192f2e1525aa9f7b412b85b925
$ wc -lc lean/notes/openmath/LIFTCORNER_2026-08-08.md
2083 133230 lean/notes/openmath/LIFTCORNER_2026-08-08.md
$ git log -1 --format=%h -- lean/notes/openmath/LIFTCORNER_2026-08-08.md
33225dd9
```

**No divergence found — this was the merge run's STOP condition and it did not trigger.**
Both shards additionally record the file's last-touching commit as `33225dd9`, independently
confirmed.

**Compilation context:** `spec/EFF_TEMPLATE_v2.md` AT HEAD (rules 1–28), Stage 0a; shard 1
additionally cites `docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md` for the Stage-0a charge — the
two citations name the same governing phase and are not in tension.

**Merged from:** `spec/EFF-LIFTCORNER-s1of2.md` (HOME lines 1–1167; 72 statements, 25 xrefs
verified, 6 open calls), `spec/EFF-LIFTCORNER-s2of2.md` (HOME lines 1168–2083; 46 statements,
25 xrefs verified, 6 open calls). **118 statements, 50 raw XREF citations, 12 raw open calls
total before merge-time dedup.** This file supersedes the two shards as the citable unit for
all downstream consumption; any consumer citing `EFF.LIFTCORNER.*` from this point on cites
the contiguous IDs below, not the shard-local `EFF.LIFTCORNER.sKof2.*` IDs. The two shard
files are **not deleted** — they remain the run-of-record trace of the sharded compilation,
and in particular remain the place where each unit's own §7 BOUNDARY SELF-AUDIT entry (which
unit-boundary candidate was chosen and why) lives in full; this merged file's own boundary
section (§7 below) carries forward only the cross-shard edge list and the format-level
conclusions (the SERIES, the CHAINs, the authorship-marker recommendation), not the full set
of individual boundary arguments each shard records for its own range.

### SHARD-MAP (old shard-local ID → new contiguous ID)

Shard 1's offset is **0** (its own numbering, 01–72, is already contiguous from 1).
Shard 2 carries a **+72** offset (01–46 → 73–118). Every `EFF.LIFTCORNER.sKof2.NN`
occurrence — the full form used in header lines and in `TARGETS:`/cross-shard-supersession
fields — has been rewritten below to the new contiguous ID. **This note's disambiguation
problem is simpler than the precedent (EFF-HE3)'s**: LIFTCORNER's two shards never leave a
bare `` `.NN` `` ambiguous between shards. The governing facts, verified exhaustively against
both shards' full text rather than assumed:

> **Every bare `` `.NN` `` reference resolves to its OWN drafting shard** — shard 1's bare
> refs are shard-1 unit numbers, shard 2's bare refs are shard-2 unit numbers — **with the
> single exception of a bare `` `.NN` `` that is explicitly labelled** by an adjacent `shard 1`
> tag (e.g. “shard 1 `` `.NN` ``”, or the label placed after the number, “`` `.NN` `` (shard
> 1)”) or written in the unambiguous full form `s1of2.NN` / `s2of2.NN`. **Every labelled or
> full-form occurrence in shard 2 points into shard 1** (verified: shard 1 contains zero
> occurrences of `s2of2.NN` and zero bare refs labelled “shard 2 `` `.NN` ``” — every “shard
> 2” mention inside shard 1 is descriptive prose pointing at a line range or a disposition
> name, never at an EFF unit ID). **A label's scope persists across a comma-separated list
> under one shared label** (e.g. shard 2's “shard 1 `` `.42`, `.44`, `.46`, `.48`, `.51` ``”)
> **and resets at the next unlabelled token** — verified at shard 2 line 477, where “shard 1
> `` `.10` ``” protects only the first bare ref on that line; the second, unlabelled `` `.12`
> `` on the same line is shard 2's own unit and shifts with the rest of that shard's numbering.
> One instance inverts the label's position (“LIFTCORNER's own `` `.42` `` (shard 1)”, shard 2)
> and is resolved the same way: the label still governs the number it sits beside.

Since shard 1's offset is 0, every bare `.NN` that resolves to a shard-1 unit — whether
drafted in shard 1 itself or cited with a `shard 1` label from inside shard 2 — keeps its
number unchanged by this merge; only unlabelled bare refs inside shard 2's own prose (and
every `s2of2.NN` occurrence) gain the `+72` offset. The rewrite was applied mechanically
against a table of every labelled exception (18 lines: 276, 345, 375, 426, 477, 481, 511,
536, 696, 740, 768, 790, 798, 853, 959, 1228, 1230, 1398 of shard 2's own source, carrying 22
protected tokens in total, one of them — line 477 — a mixed line with one protected and one
shifted token), built by reading every `shard 1` occurrence in shard 2's full text (35
occurrences; the ones outside this table are prose with no attached unit ID, or fall inside
front-/back-matter this merge rewrites from scratch rather than mechanically renumbers) —
never by a blind global substitution — and audited afterward by exhaustive regex sweep:
**zero leftover `sKof2` substrings within the merged statement inventory (§3)** — the handful
that survive in this header and in §7 are deliberate quotations of the original shard-local
notation, illustrating the rewrite rule itself — and **zero out-of-range renumbered IDs**
(every resolved ID lies in 1–118).

### Header unification and blob-hash check

Both shards' front matter carries the **identical** compiled-by/cross-read-owed stamp
(reproduced verbatim above) and the identical HEAD blob hash; both independently record the
file's last-touching commit (`33225dd9`) — confirmed by this merge against the working tree
rather than trusting the shards' mutual citation alone.

### Genre note (carried from both shards, verbatim discipline)

**GENRE: TAG-SPARSE PROSE PROOF + SEALED-PREREGISTRATION NUMERICS over shard 1's range,
shifting to a MIXED record-surface / TRANSCRIBED-CERTIFIER-PROOF genre over shard 2's
range.** `grep -c '\tag{'` = **6** over the whole note, and **all six sit inside shard 2**,
specifically inside AC-5's (T1)–(T6) displays (re-verified fresh at merge time: `grep -c
'\tag{' lean/notes/openmath/LIFTCORNER_2026-08-08.md` = 6). Shard 1's HOME range (title
through §S4.3) carries **zero** `\tag{` and its unit boundaries are compiler choices (§7).
Shard 2's HOME range (§S5 through the end) is itself two genres: the record surface (§S5,
the STATUS BLOCK, the archive, the acceptance record, the FC annexes — tag-sparse, boundaries
chosen the same way as shard 1) and the **TRANSCRIBED external certifier proof** (AC-1…AC-5 —
tag-carrying from AC-5 onward, boundaries read off the source's own numbered findings, named
annexes and `\tag{}`ed displays). **Twenty units in this merged inventory (`.94`–`.100`,
`.103`–`.108`, `.111`–`.117`) carry the `[TRANSCRIBED — certifier]` authorship marker** —
they are *in* this note but *by* the sol certification arc, transcribed unaltered, never
LIFTCORNER's own mathematics. **Source defect, newly surfaced by this merge's own recount:**
shard 2's own text asserts “fifteen” certifier units in two places (its rule-3 boundary
finding and its §8 SHARD NOTES numbering line), but shard 2's own cited ranges — `.22`–`.28`
(7), `.31`–`.36` (6), `.39`–`.45` (7) — sum to **20**, matching the 20 headers that actually
carry the marker (re-counted fresh: `grep -c '\[TRANSCRIBED — certifier\]'` restricted to
`### EFF.LIFTCORNER…` header lines = 20). The undercount is carried unedited in the shard file
per this repo's freeze discipline; it is corrected here rather than silently reconciled. The
template's TYPE ENUM has no author field; this merge inherits shard 2's recommendation that
one be added for the format generally, since the DAG edge “LIFTCORNER supplies X” is false
for all twenty of them while “LIFTCORNER carries X” is true.

### FREEZE PREDICATES (rule 21 — FOUR across the merged note; the three from shard 1 stay
separated exactly as shard 1 insists, and shard 2 contributes a genuinely new fourth)

**Special care, per the merge charge:** the three freeze predicates named in shard 1's header
must not be conflated with one another (shard 1 is explicit that conflating FREEZE-2 and
FREEZE-3 is “the exact error [r3, F-C] corrects”), and shard 2's own fourth predicate
(FREEZE-1a) must not be read as a restatement of FREEZE-1 — it is a **second, later, and
wider** text freeze with its own date and its own scope.

**(FREEZE-1) TEXT FREEZE AT ACCEPTANCE.** `.89`: “**THIS NOTE IS ACCEPTED at 2/2**”,
reinforced by the ANNEX heading (source line 1457) “**ANNEX (dated appends; the frozen body
is not edited)**”. Pins verified: `git cat-file -t c6097d7` = commit; `git cat-file -t
9b5175c` = commit.

**(FREEZE-1a) A SECOND, LATER TEXT FREEZE at the 2026-08-12 certifier appends.** Source line
1495: “Everything above this heading is byte-untouched by this append.” This is a **distinct**
predicate from FREEZE-1: distinct date (2026-08-12 vs the 2026-08-06/07 acceptance), and a
**wider** scope — it freezes everything above source line 1485, which by 2026-08-12 already
includes the acceptance record and both FC annexes that FREEZE-1 alone does not mention.
Shard 1 has no occasion to state FREEZE-1a (it lies entirely inside shard 2's HOME range);
a compilation using shard 1 alone would miss it.

**(FREEZE-2) INSTRUMENT-FREEZE — the SEALED runner, two-commit seal, from commit 1
onward.** Re-verified at compile time: `md5sum verification/openmath/liftcorner_checks.py` =
`ccb4351c92573f5f962cae4ae952d8dd`, matching every one of the note's four quotations of the
figure (`.03`, `.06`, `.28`, the acceptance record `.90`) and `git cat-file -t dafc0b5` =
commit.

**(FREEZE-3) INSTRUMENT-FREEZE — the POST-HOC children generator, frozen only from repair
round r3 onward.** A *different* freeze with a *later* start date and an explicitly
non-sealed status (pinned by reproducibility — `diff` empty — rather than by the two-commit
seal). Re-verified: `md5sum verification/openmath/liftcorner_tailstab_children_table.txt` =
`bf9106e7edc535edf2b7a6b6a64f0f55` (2,986 lines), matching `.05`/`.06`. **Conflating FREEZE-2
and FREEZE-3 is the exact error shard 1 records the note itself repairing at `[r3, F-C]`**
(`.10`) — the merge preserves the separation for that reason, not merely for template
compliance.

### Governing effective-text record (unified from both shards)

Four source facts fix the rule, and the two shards' independent derivations of it agree
exactly (verified by direct comparison, not assumed from shared authorship).

**(i) The seven repair rounds (r1–r7) were applied IN-TEXT, strike-and-replace, never by
append**, entirely inside shard 1's range — every `[r1, F#]` … `[r7, F7-#]` bracket in source
lines 1–1167 is already-landed text, and wording quoted inside such a bracket is dead.
**(ii) The refuted wording inside a bracket is never live** — stated for the extreme case at
the archive preamble (`.84`, source lines 1269–1272): “superseded wholesale … kept only
because this note's discipline never silently deletes superseded wording.” **(iii) Sealed
text is NOT edited even when refuted; the correcting bracket is the record** — both for the
S1 CANDIDATE display (`.90` [F4-5], correcting `.20`) and for the sealed runner's own
docstring (`.27`, `[r3, F-A]`). **(iv) After acceptance (line 1433, `.89`) the body is closed
to everything but dated appends**, and the discipline itself SHIFTS at that boundary: shard
1's range never has an append (every correction there is in-place strike-and-replace); shard
2's range from the acceptance record onward is append-only, and three of its appends state
their own transcription discipline explicitly (“transcribed unaltered”, source lines 1496,
1616, 1831).

**EFFECTIVE TEXT = the whole 2,083-line file exactly as written** — r1–r7 already landed in
place over lines 1–1167 (struck text is REFUTED text preserved for the record, never
current), the archive region (source lines 1297–1418, `.84`–`.87`) explicitly dead, and the
whole body READ AS CORRECTED by every later dated append that names an earlier sentence, with
no earlier sentence ever deleted. **Eleven dated corrections land on this note's own text**:
seven repair rounds in shard 1's range (`.07`, `.09`, `.11`–`.15`), FC-1 and FC-2 (`.90`,
`.92`), and the five 2026-08-12 sol-certification annexes AC-1…AC-5 (`.95`, `.98`, `.99`,
`.103`, `.111`) — each is applied at its unit and tabulated in §7 below.

### Scope of record — mandatory THREE-predicate split (unified from both shards)

**A. ABSORPTION / mathematical supply SET.** The note's own inventory is fixed by the unit
line and the acceptance record: **one sub-lemma (CONTENT), three lemmas/theorems
((TAIL-STAB), (READ-EQ), THE THEOREM), two corollaries (COR 1, COR 2)** over the corner
\(g_0=1\wedge\delta_1=1\) — the acceptance record's own inventory (`.90`) confirms exactly
this five-item set and its fence. **PROP (the all-rung propagation statement) is explicitly
NOT among the accepted five** — the fact CHAIN-P's whole reversal turns on, and a positive
scope finding both shards record independently rather than infer. **The supply set GREW
after acceptance** by three transcribed certifier results the note now carries as
dated appends: AC-2's CONTENT (integral-key form, `.98`), AC-3's READ-EQ degree correction
(`.99`), AC-4's constructor/telescope opacity sublemma (`.104`–`.105`), and AC-5's
(RM-1-TRANSPORT) (statement `.107`; proof `.111`–`.115`) — none of the four is inside the
accepted 2/2 scope;
each is an append dated after acceptance and is marked `[TRANSCRIBED — certifier]` since none
of the four is authored by this note.

**B. APPEND / consumption PROTOCOL scope — what this note has LANDED on other notes.**
**Zero** landed appends during shard 1's HOME range (FENCES, `.17`: “nothing here closes
NR-1's ledger entry until this note's own acceptance arc runs”). **Exactly one** landed
append after acceptance, verified positively: the ITERLAWN fold annex
(`grep -cF '## ★ FOLD ANNEX (orchestrator, 2026-08-07): THE NR-1 RIDER-REWRITE, LICENSED AND
EXECUTED ★' lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md` = 1, line 1518 — re-verified
fresh at merge time). **Everything else is verified UNLANDED**, independently re-confirmed at
merge time (all four checks return 0): `OPACITY`, `AC-4`, `AC-5` on `ITERLAWN_PROOF`; and
`LIFTCORNER` (unhyphenated) on `ILNRES` — whose single hit under the hyphenated `LIFT-CORNER`
spelling (count 1, line 180) is the pre-existing S5.1 spec heading, i.e. the CHARGE, not an
absorption append. **AC-5's own closing parenthetical schedules the first three**
(“transcription-confirm owed”); the consequence is carried forward as OPEN-CALL 8 below, not
asserted as an error.

**C. INBOUND CORRECTIONS RECEIVED (v3 rule 17).** **Ten**, all from the sol certification
arc, none from a supplier note: five land inside shard 1's HOME range as out-of-range dated
appends resolved at their in-range target (FC-1 → `.02`/`.72`; AC-1 → `.63` via CHAIN-P;
AC-2 → `.34`, replacing its statement; AC-3 → `.55`, replacing its statement; the AC-4/AC-5
pair → `.63` via CHAIN-P and `.64` via the census-of-record scope-pin) — and five land
natively inside shard 2's own HOME range as the AC-1…AC-5 annexes' own text (`.95`–`.117`)
plus FC-2 (`.92`). Verified to exist: `runs/cert/C1_liftcorner_output.log`,
`runs/cert2/E1_liftcorner_output.log`, `runs/cert4/P3_opacity_output.log`,
`runs/cert5/P4_rm1_output.log` (all four). This is a class distinct from both A and B, and it
is the class that changed two proved statements (`.34`, `.55`) and reversed one proposition's
scope twice (`.63`, CHAIN-P, terminal `.117`).

### Resolution rules applied (merged; each shard's own numbered rule-list is preserved in
full at its own file — the nine below are the ones that govern the merged statement
inventory)

1. Source lines 1–1167 supply shard 1's HOME material; lines 1168–2083 supply shard 2's.
   Every `[rN, …]` bracket in shard 1's range is already-landed text; wording quoted inside a
   superseding bracket is dead and is emitted only when load-bearing for a consumer.
2. Where a later in-range round touches text an earlier round already touched, the LATER
   round governs; four internal, single-shard collisions are tabulated as CHAIN-A…CHAIN-D in
   §7 with their TERMINALs named — all four resolve entirely inside shard 1 (`.01`–`.72`).
3. Where an out-of-range dated append names an in-range sentence, the corrected reading is
   carried in the unit's CANONICAL STATEMENT when the append is a “is SUPERSEDED by”
   replacement (AC-2 → `.34`; AC-3 → `.55`), and in CONDITIONALITY when it is a scope pin, a
   license, or a counter re-reading (FC-1, CHAIN-P's AC-1/AC-4/AC-5, the acceptance record).
4. **The sealed pre-run text of §S1 and §S2 is never rewritten.** Where the sealed text is
   wrong (the `c′` collision, `.90`/`.91`), the unit carries the sealed bytes as its CANONICAL
   STATEMENT and the correcting bracket as CONDITIONALITY — never the reverse.
5. **Preregistrations and run-records are separate units even when the source displays them
   adjacently** (v3 rule 19): shard 1's thirteen-family sheet (`.22`) is a `preregistration`;
   its verdict (`.28`–`.30`) is a `run-record`; the runners are `instrument-record`s.
6. **Certifier annexes are emitted as units of this note but attributed to their author**
   (rule 3's genre gap, filled by the `[TRANSCRIBED — certifier]` marker, twenty units — see
   the source-defect note above on shard 2's own undercount).
   **The orchestrator-verification parentheticals are separate units** (`.101`, `.109`,
   `.118`), not footnotes — they record an independent pre-transcription re-derivation, a
   different warrant from the certifier's own.
7. A dead wording is emitted as its own unit only when a consumer could otherwise re-import
   it (six such sites across the merged inventory: `.19` (r0's strict-descent clause), `.61`
   (r0's W2-OPEN-1 identification), `.62` (r0's promotion of assert (i)), `.68` (PE6's "42
   occurrences" figure), and the three archived STATUS LINEs `.85`–`.87`).
8. **Numbers are re-computed, never transcribed.** Every count in shard 1's §S2/§S3/§S4.1 and
   every arithmetic claim in shard 2's AC-1…AC-5 annexes was re-derived at compile time from
   the committed artifacts or from the displayed algebra, independently of the note's own
   tables; both shards report zero discrepancies, and this merge's own fresh sample (below)
   found a third zero.
9. Designations cited by the AC-annexes into `ITERLAWN_PROOF_2026-08-08.md` that instantiate
   a schematic name (`CASE-SPLIT-(2)` for `CASE-SPLIT-(n)`, `READ-ADD-(1)` for
   `READ-ADD-(m)`) are recorded as **NEAR-MISS** (v3 rule 15), never suppressed and never
   emitted as a clean XREF.

### Quotation and table discipline

CANONICAL STATEMENTs are verbatim source quotation or explicitly marked `[ASSEMBLED]`;
truncation is marked `…`. Strike-through markers (`~~…~~`) are not present in this note (its
in-place repair mechanism uses bracketed `[rN, F#: …]` riders, not strike-through); the
bracket-and-supersede discipline is reproduced verbatim. AC-5's LaTeX displays are reproduced
in source form (`\[…\]` inside blockquotes, tags included) rather than transliterated, since
they are the note's only `\tag{}`-carrying displays. The four source tables (shard 1's S2
prediction sheet and S4.1 seven-genre census; shard 2's AC-4 census partition, transcribed
twice per v3 rule 14 since the source also renders a plain bulleted list) are emitted as
tables and flagged `[TABLE]`; none is prosified. Compiler-authored ledgers in §§4–6 below are
flagged `[TABLE — compiler ledger]` and are not source statement units.

---

## 2. NON-IMPORTS (consolidated from both shards; zero duplicates found across the two lists)

The note's explicit negative fences, load-bearing for the DAG. Shard 1 supplied ten (NI-1
through NI-10, all about mathematical/protocol non-consumption inside the HOME range's own
argument); shard 2 supplied eight (NI-1 through NI-8, all about the record surface's and the
certifier annexes' own non-claims). **Compared item by item, no pair names the same fact** —
they are kept as eighteen distinct entries rather than merged, renumbered contiguously.

**NI-1 — no accepted text is edited, and no engine is written to.** `.17`: “No edit to any
accepted text (ITERLAW/ITERLAWN/ILNRES bodies, sealed falsifiers, wave-18 artifacts);
committed engines consumed READ-ONLY (in-memory ledger override only, engine_ext
precedent)”.

**NI-2 — no Lean edge.** `.17`: “no Lean change”. Neither shard creates any edge to the Lean
corpus.

**NI-3 — no orders-≥3 machine claim.** `.17`: “no orders-≥3 machine claim (the battery is
2-read)”. Every measured and every proved statement in the note is 2-read.

**NI-4 — no gr(w₂) claim.** `.17`: “no gr(w₂) claim”. The NR-2 gr-semantics wrapper is a
different residual (ILNRES [NR-2]) and is not touched.

**NI-5 — the runner's two asserts are consumed by NOTHING.** `.25`: “**NO CHAIN STEP CONSUMES
EITHER**”. No edge runs from the asserts to any proof step; the soundness edge runs from
`mk_field_ext`'s g = 1 reading instead (`.26`).

**NI-6 — the r-to-q gain equality is consumed by nothing.** `.42`: the 896/896 equality is
“an artifact of those instances' shapes, and no step below consumes it.”

**NI-7 — the branching count's VALUE is consumed by nothing.** `.48`: “**ONLY FINITENESS of
this count is consumed** … no step anywhere uses the count's VALUE.”

**NI-8 — COR 2 imports no slice of W2-OPEN-1.** `.62`: “no equivalence between COR 2 and any
slice of W2-OPEN-1 is derived anywhere in this note”, with (a) and (b) named as what a tie
would still need.

**NI-9 — Q6 LOC is not an independent leg.** `.30`: “A reader tallying S2's thirteen
prediction families as thirteen independent legs over-counts by one.”

**NI-10 — the CERT family's PARI leg is not re-run.** `.22`: “PARI leg NOT re-run: wave-18 T11
on the same base roster is on file — disclosed reuse”.

**NI-11 — the note edits no ledger.** `.75`: “this note edits no ledger.” The ITERLAWN fold
annex is a separate, later, append-only act by the orchestrator, not an edit by this note
itself.

**NI-12 — this unit does not choose between the two NR-1 readings.** `.76`: “The two readings
live in different notes of record, and this unit does not choose between them.”

**NI-13 — no residual is created or repriced.** `.77`: “this unit has no authority to create
a residual … Until ILNRES rules, **nothing here re-prices anything**”.

**NI-14 — FC-1 corrects the W-2 cap and NOTHING else.** `.97`: “FC-1 is explicitly a
correction only of “the W-2 cap”; it changes the supplier grade … and does not erase the
`[r4, F4-6]` scope fence.”

**NI-15 — Θ does not commute with arbitrary division.** `.104`: “It is not asserted to
commute with arbitrary division or re-development in \(\mathcal O[x]\).”

**NI-16 — full R,Q proof-data equality is neither proved nor claimed.** `.116`.

**NI-17 — AC-5 enlarges no ITERLAWN perimeter.** `.117`: “This does not enlarge ITERLAWN's
DCX, higher-\((RM)\), T-scope or deeper-noncanonical-lift perimeter.”

**NI-18 — the deeper-level fence survives every repair.** `.117`: “The fence excluding
independently chosen noncanonical higher keys remains unchanged.”

Accordingly **no edge is created** from this note to the Lean corpus, to any orders-≥3
statement, to gr(w₂), to W2-OPEN-1's battery, to ITERLAWN's DCX/higher-(RM-m)/T-scope/deeper-
noncanonical-lift perimeter, to ILNRES's residual list, to any statement of complete R,Q
invariance, or from the runner's asserts to any proof step.

---

## 3. Statement inventory (118 units, contiguous, in source order)

### EFF.LIFTCORNER.01  [convention]

**CANONICAL STATEMENT:**

> “**Unit:** LIFT-CORNER (NR-1 of ILNRES S1; spec ILNRES S5.1, price M; route =
> the W-2 shift-descent covariance + window-calculus tail bookkeeping).
> Wallclock 2026-08-04, campaign date 2026-08-08. Genre: sealed-preregistration
> numerics (two-commit seal) + a conditional COMPOSE (S4; written only on a
> 0-violation verdict, per the probe-first discipline).”

**FORM:** bold-headed paragraph.

**DERIVATION:** `[IMPORTED]` The unit identity and its route are set by the spec of record, not derived here. XREF X01 verifies `**S5.1 (NR-1 LIFT-CORNER unit), price M.**` in `ILNRES_2026-08-08.md` at count 1; XREF X02 verifies `**[NR-1] (ITER-LAW-LIFT), open exactly at g₀ = 1 ∧ δ₁ = 1.**` at count 1.

**CONDITIONALITY:** none (identification).

**RESOLUTION TRACE:** statement lines 3–7. Untouched by r1–r7.

**TEETH:** none directly; the delivery-vs-spec match is checked by the §S5 delivery paragraph (shard 2), which states PE4 confirmed it independently.

---

### EFF.LIFTCORNER.02  [scope record]

**CANONICAL STATEMENT:**

> “**Grade cap (read
> first): everything this unit proves is at attempt grade 0/2 AND capped by its
> W-2 consumption (GRTW2_PROOF, itself attempt 0/2, no acceptance arc run).**”

**FORM:** bold-headed paragraph (the note's own “read first” instruction).

**DERIVATION:** `[RECORD]` A grade declaration, not a derivation.

**CONDITIONALITY:** **BOTH halves of this sentence are superseded from out of range, by two different instruments, and a consumer must apply both.** (a) “attempt grade 0/2” → the acceptance record's **ACCEPTED at 2/2** (line 1433). (b) “capped by its W-2 consumption (GRTW2_PROOF, itself attempt 0/2)” → **FC-1** (line 1459):

> “The cap's supplier has
> since been ACCEPTED at 2/2 — GRTW2 at adc6cf3 (2026-08-07), with
> W2-OPEN-2/OPEN-2a accepted AS A BOX (the weld's one fenced open lemma) …
> Wherever this note bills GRTW2 at "0/2 / arc open"
> (the record above; the grade box's W-2 cap), read: capped by an ACCEPTED
> supplier at its fenced scope”

SUPERSESSION KIND: **counter re-reading** (both halves). The cap does not vanish — it becomes a cap by an ACCEPTED supplier at a FENCED scope, GRTW2's own open box (W2-OPEN-2/OPEN-2a) still standing. `git cat-file -t adc6cf3` = commit (pin P16).

**RESOLUTION TRACE:** statement lines 6–9; correction sites 1433 (grade) and 1459–1471 (cap).

**TEETH:** the grade-box SERIES (`.65`–`.70`) re-states this counter six times in range; all six are stale in the same way.

---

### EFF.LIFTCORNER.03  [instrument-record]  *(SERIES MACHINE-LEG, link 1)*

**CANONICAL STATEMENT:**

> “**Machine leg:** `verification/openmath/liftcorner_checks.py` (this header +
> the runner commit BEFORE any full run; verdict appended in commit 2 from the
> artifacts `liftcorner_checks_output.txt` / `liftcorner_checks_results.json`).”

**FORM:** bold-headed paragraph.

**DERIVATION:** `[RECORD]` The two-commit seal protocol: the instrument and its predictions are committed before the run, so the verdict cannot be back-fitted.

**CONDITIONALITY:** the seal binds only what is in commit 1. The post-hoc children generator (`.04`) is explicitly OUTSIDE it.

**RESOLUTION TRACE:** statement lines 11–13. Machine-leg brackets at 14–41 extend but do not replace it.

**TEETH:** PIN VERIFICATION (v3 rule 23), executed fresh at compile time: all three filenames exist; `md5sum liftcorner_checks.py` = `ccb4351c92573f5f962cae4ae952d8dd`, identical to the note's figure; `git cat-file -t dafc0b5` = commit.

---

### EFF.LIFTCORNER.04  [instrument-record]  *(SERIES MACHINE-LEG, link 2 — dated r1)*

**CANONICAL STATEMENT:**

> “[r1] A SECOND, post-hoc machine leg was added at repair round r1 and is NOT
> part of the sealed prediction battery: `liftcorner_tailstab_children.py` +
> its committed output `liftcorner_tailstab_children_table.txt` — the
> examples-first child-type table the repaired S4.1 induction is derived from
> (disclosed as written AFTER the refutation, hence evidence for a repair, not
> a prediction). The sealed runner is byte-untouched (md5 unchanged, S3).”

**FORM:** bracketed rider (dated).

**DERIVATION:** `[RECORD]` + the standing examples-first directive: the r1 round record (lines 60–63) states the case list “is DERIVED FROM the examples-first table (standing directive, Asvin 2026-08-05), which is committed with this round”.

**CONDITIONALITY:** **evidence for a repair, not a prediction.** A consumer may not count this leg as sealed-battery evidence. The disclosure is the note's own, and it is the correct one: the table was generated after PE1's refutation.

**RESOLUTION TRACE:** statement lines 14–19; the derivation-of-the-case-list claim at lines 60–64.

**TEETH:** disposition `disclosed non-prediction` — the note itself fences the leg out of the sealed battery, so no battery row guards it; §S4.1's A1–A7 assertions (`.44`) are its own teeth.

---

### EFF.LIFTCORNER.05  [instrument-record]  *(SERIES MACHINE-LEG, link 3 — dated r2)*

**CANONICAL STATEMENT:**

> “[r2] That post-hoc generator was AMENDED at repair round r2 (assertion **A7**
> added, curing PE2's G3: the enumerated children now have to reconstruct the
> very polynomial A6 develops) and its output recommitted; its r1 data sections
> (§§1–6) regenerate byte-identically, A7 adds assertions only. The sealed
> runner is STILL byte-untouched at r2 (md5 `ccb4351c92573f5f962cae4ae952d8dd`).”

**FORM:** bracketed rider (dated).

**DERIVATION:** `[RECORD]` The amendment's *content* is unit `.44`; this unit records only the instrument event and the regeneration discipline.

**CONDITIONALITY:** the r1 data sections' byte-identity is a `diff`-level claim over §§1–6 only; A7's verdict lines are new insertions (see `.44`'s 7-insertion / 0-deletion / 0-modification record).

**RESOLUTION TRACE:** statement lines 20–24.

**TEETH:** compile-time PIN VERIFICATION: `liftcorner_tailstab_children.py` md5 `11f2d7858a66d4b8231b38b11f8751c3`; the committed table md5 `bf9106e7edc535edf2b7a6b6a64f0f55`, 2,986 lines. The sealed runner's md5 is re-verified identical to the quoted figure.

---

### EFF.LIFTCORNER.06  [instrument-record]  *(SERIES MACHINE-LEG, link 4 — dated r3 + r4)*

**CANONICAL STATEMENT:**

> “[r3] **BOTH MACHINE LEGS ARE BYTE-FROZEN AT r3** — repair round r3 is
> note-level only, and PE3 verified both legs before the round: sealed runner
> `git diff dafc0b5 HEAD` = **0 bytes**, md5 still
> `ccb4351c92573f5f962cae4ae952d8dd`, exit 0 at 25,409/0; children generator +
> its committed table regenerate **byte-identically** (`diff` empty) with A7's
> four legs PASS (752 nodes / 5,336 children, 0/0/0/0). No script or table is
> touched at r3.”

with the r4 extension, quoted in full because it carries the disclosure the r3 bracket lacks:

> “[r4] **STILL BYTE-FROZEN AT r4** … exit 0 at 25,409/0 with every counted family at 0 violations (its output
> differs from the committed artifact `liftcorner_checks_output.txt` at exactly
> 4 wall-clock lines — three per-block stamps plus `elapsed 4.3s` vs `4.4s` —
> and the diff is empty under timing normalisation); children generator
> regenerates its committed table **byte-identically** (`diff` empty) with A7's
> four legs PASS (752 nodes / 5,336 children, 0/0/0/0). No script or table is
> touched at r4.”

**FORM:** two bracketed riders, emitted as one unit (r4 re-states r3's predicate verbatim over a fresh re-run and adds the wall-clock disclosure).

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** “byte-frozen” is asserted of the SCRIPTS and of the children TABLE; it is explicitly NOT asserted of the sealed runner's OUTPUT FILE, which carries wall-clock fields. That distinction is CHAIN-B's whole content (`.10`).

**RESOLUTION TRACE:** statement lines 25–41.

**TEETH:** compile-time re-verification of the counted quantities against the committed artifact — see the arithmetic audit in §6, which reproduces 25,409 exactly from the artifact's own per-family column (56 + 656 + 5×4,176 + 3,816 + 0 + 0 + 1 = 25,409) and confirms `elapsed 4.4s` in the committed file.

---

### EFF.LIFTCORNER.07  [repair-round record]  *(SERIES REPAIR-ARC, link 1 — r1)*

**CANONICAL STATEMENT:** `[ASSEMBLED]` from the round's own header and its four numbered dispositions (lines 43–88). The head, verbatim:

> “**[REPAIR ROUND r1 — 2026-08-08 campaign (wallclock 2026-08-05).** Applied
> against LIFTCORNER-PE1 (hostile pass, fresh context, report
> `LIFTCORNER_passPE1_report.md`, commit 30e570c: **1 CRITICAL + 3 gaps**;
> ledger entry BRIDGE_ADJUDICATIONS_2026-07-30.md "PE1 VERDICTS"). PE1's
> machine leg was bit-identical (exit 0, 25,409/0, fires 1,576, all roster
> counts independently re-derived, two-commit seal verified), so nothing in
> S1–S3 or in the corner measurement moved; the critical finding is confined
> to one line of the S4.1 PROOF.”

The four dispositions, verbatim in brief: **F1** (CRITICAL) “the S4.1 strict-descent clause "every child has m′ ≤ m−1" is FALSE at the top-mid q-digit child (k = e₀−1, which sits at m′ = m; PE1's counter-instance reproduced numerically in S4.1). REPAIRED, statement byte-unchanged, by replacing the single induction on m with the LEXICOGRAPHIC (m, deg a) induction”; **F2** the b₀-split “is now defined in-note at first use (S4 setting)”; **F3** “COR 2's identification with "W2-OPEN-1 RESTRICTED to the base junction" is WITHDRAWN as underived”; **F4** “S2 disclosure (c) now says exactly what the runner asserts”.

The round closes:

> “Acceptance counter unchanged at 0/2 — a repair round is not a pass; round r2
> (a fresh hostile pass on THIS text) is the next acceptance attempt.]**”

**FORM:** bold-headed bracketed round record.

**DERIVATION:** `[RECORD]` of a hostile pass and its dispositions.

**CONDITIONALITY:** **F4 is DEAD — refuted twice from inside the note.** The round record itself carries the two strikes inline (`.08`). The closing sentence's naming of “round r2” for the pass is corrected by r2's own record (`.09`): the pass was PE2; r2 is the repair round. The counter is superseded (`.02`).

**RESOLUTION TRACE:** statement lines 43–88; correction sites 74–86 (in-round strikes), 90–96 (the naming fix), 1433 (the counter).

**TEETH:** `LIFTCORNER_passPE1_report.md` exists; `git cat-file -t 30e570c` = commit. PIN NOTE: “fires 1,576” is re-verified against the committed artifact, which reads `WRONGLET total fires 1576 (pred > 0)`.

---

### EFF.LIFTCORNER.08  [supersession rider]  *(CHAIN-A, links 3–4 as sited inside the r1 round record)*

**CANONICAL STATEMENT:**

> “[**r3, F-A:** that F4 repair landed on the WRONG HALF of its own sentence —
> "full ψ₁-byte carryover" is a snapshot-consistency no-op that cannot fail, and
> the demoted one-element K₂ check is the only substantive half of the pair. See
> S2 disclosure (c)'s [r3, F-A] bracket; the `mk_field_ext` relocation, which is
> where the soundness actually lives, stands.
> **[r4, F4-1 — the SECOND half of that r3 sentence is stricken too.]** "the
> demoted one-element K₂ check is the only substantive half of the pair" is
> FALSE: `C.K2["one"]` is a structural constant of (d₀, g₀, g₁) that never reads
> a ψ₁ coefficient, so assert (ii) is as incapable of firing as assert (i).
> **BOTH asserts are inert**; nothing in this note consumes either; the
> soundness is in `mk_field_ext`'s g = 1 reading. Final description: S2
> disclosure (c)'s **[r4, F4-1]** bracket. What survives of r3's F-A is (i)'s
> no-op diagnosis and the `mk_field_ext` relocation.]”

**FORM:** nested bracketed riders inside a round record.

**DERIVATION:** for (i)'s no-op status, the mutation trace at `.24`; for (ii)'s inertness, the `mk_field_ext` source reading at `.25`.

**CONDITIONALITY:** SUPERSESSION KIND: **replacement** (r4 over r3) nested inside **replacement** (r3 over r1/F4). TERMINAL for CHAIN-A is the S2 bracket at `.25`, as re-scoped by [r5, F5-2]; this unit is the *restatement site* and points at it explicitly (“Final description: S2 disclosure (c)'s [r4, F4-1] bracket”).

**RESOLUTION TRACE:** statement lines 74–86; the governing description at 493–509; the F5-2 re-scoping at 266–268.

**TEETH:** the `mk_field_ext` reading is a source-code claim; §3.5 records the file/line pins the note gives and their disposition.

---

### EFF.LIFTCORNER.09  [repair-round record]  *(SERIES REPAIR-ARC, link 2 — r2)*

**CANONICAL STATEMENT:** `[ASSEMBLED]` from lines 90–161. The head and the naming fix, verbatim:

> “**[REPAIR ROUND r2 — 2026-08-08 campaign (wallclock 2026-08-05).** Applied
> against LIFTCORNER-PE2 (hostile pass, fresh context, on the r1 text; report
> `LIFTCORNER_passPE2_report.md`, commit 3367f3c: **0 CRITICAL + 5 gaps**;
> ledger entry BRIDGE_ADJUDICATIONS_2026-07-30.md "LIFT PE2: THE REPAIR HOLDS").
> Naming, since r1's closing sentence used "round r2" for the pass: the hostile
> pass on the r1 text was **PE2**; **r2 is this REPAIR round**; the next
> acceptance attempt is **PE3**, a fresh hostile pass on THIS text.”

The confirmation of the F1 repair, verbatim:

> “**F1 IS
> CURED and HELD** — PE2 re-derived every load-bearing piece of the lex repair
> independently (9 ↦ 7 mapping total and disjoint; row 7b's degree drop correct
> at the deg a = 0 and deg b = 0 edges; both emptiness strata PROVED not merely
> measured; ρ strictly drops on every edge, so the lex order well-founds both
> consumers)”

The five dispositions **G1**–**G5** are compiled at their own home sites: G1 at `.48`, G2 at `.51`, G3 at `.44`, G4 at `.42`, G5 at `.46`. The round closes:

> “Acceptance counter
> unchanged at **0/2**: PE2 was a hostile pass but returned 5 gaps, and the r2
> repairs are themselves unaudited.]**”

**FORM:** bold-headed bracketed round record.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** the clause “the r2 repairs are themselves unaudited” is superseded in the archive by [r3, F-D] (shard 2, line 1337: “PE3 has now read them”). The counter is superseded (`.02`).

**RESOLUTION TRACE:** statement lines 90–161 minus the two nested r3/r4 brackets (102–131, unit `.10`); correction sites 1337–1355 (shard 2), 1433.

**TEETH:** `LIFTCORNER_passPE2_report.md` exists; `git cat-file -t 3367f3c` = commit.

---

### EFF.LIFTCORNER.10  [supplier-finding / provenance-rider]  *(CHAIN-B — TERMINAL)*

**CANONICAL STATEMENT:** the terminal reading, verbatim ([r4, F4-3], lines 115–131):

> “**[r4, F4-3 — the PROVENANCE in the sentence above is corrected; the FACTS
> are unchanged.]** The r3 wording, quoted and superseded: "**"bit-identically"
> STRICKEN here as an overstatement of PE2's own record** … PE2's report says
> something weaker for the sealed leg". That misassigns the origin. PE2's report
> (`LIFTCORNER_passPE2_report.md`, 3367f3c) states the UNQUALIFIED form for the
> sealed runner at **three** sites — its verdict summary (line 33, "The sealed
> runner re-runs **bit-identically**"), its section header (line 54, "### (a)
> The SEALED runner — **bit-identical**, seal intact") and its closing
> machine-legs line (line 471) — and the qualified form at **one** (line 67,
> the family-table paragraph: "identical line-for-line modulo the
> `elapsed`/per-block timestamp fields only"). So the overstatement
> **ORIGINATES in PE2's report**; the r2 round **transcribed** PE2's own
> headline word rather than dropping a qualification the source only ever gave
> qualified. The truth, unchanged and independently re-confirmed at PE3 and at
> PE4 (4 differing lines, all wall-clock): the runner's OUTPUT FILE is
> **identical modulo timing fields**, not bit-identical, while every COUNTED
> quantity is identical; the children-generator table IS bit-identical.”

**FORM:** bracketed rider, dated, quoting and superseding its predecessor in full.

**DERIVATION:** a four-site count over an external report, done at r4.

**CONDITIONALITY:** SUPERSESSION KIND: **provenance-rider** — it moves the *origin* of a defect, not the defect's factual correction. Distinguishing this from a `replacement` matters for the DAG: the factual half (the timing-field qualification) descends from [r3, F-C] and is NOT superseded; only the attribution is.

**RESOLUTION TRACE:** statement lines 115–131; predecessor at 102–114; the same correction re-lands inside the shard-2 archive at 1282–1289.

**TEETH:** `AUDIT` disposition, class **decorrelated-model audit** — no battery could have produced this finding; it required reading PE2's report against the note's own transcription. Compile-time PIN VERIFICATION of the four cited sites is recorded in §3.5 as **PARTIAL**: the report file exists and `git cat-file -t 3367f3c` = commit, but the four line numbers cited (33, 54, 67, 471) are asserted of the report AT THAT COMMIT, and the working-tree copy is not pinned to it. See OPEN-CALL 4.

---

### EFF.LIFTCORNER.11  [repair-round record]  *(SERIES REPAIR-ARC, link 3 — r3)*

**CANONICAL STATEMENT:** `[ASSEMBLED]` from lines 163–212. The head and the mathematics verdict, verbatim:

> “**[REPAIR ROUND r3 — 2026-08-08 campaign (wallclock 2026-08-05).** Applied
> against LIFTCORNER-PE3 (hostile pass, fresh context, on the r2 text — the
> FIRST acceptance attempt of the arc; report `LIFTCORNER_passPE3_report.md`,
> commit 39ea0db: **0 CRITICAL + 5 gaps**). PE3 was directed at the veins the
> first two passes had not mined: S2/S3's measurement design, the (TAIL-STAB)
> consumer interface, the r2 patches themselves, and the arc's own grade
> arithmetic. **The mathematics held at every point it touched** — PE3
> re-derived independently all eight per-digit ω-gain bounds, the 2e₀+3
> branching arithmetic, the counter-instance's two passes and its
> double-development tie, the whole S2 applicability arithmetic (16 → 48 → 56 →
> 656/4,176/3,816 → 25,409), and the (TAIL-STAB) interface at every downstream
> site; both machine legs re-ran clean … All five gaps land in the
> EVIDENCE-DESCRIPTION layer, not in the chain.”

Dispositions **F-A** (`.24`/`.25`), **F-B** (`.42`), **F-C** (`.10`), **F-D** (shard 2 archive), **F-E** (`.30`).

**FORM:** bold-headed bracketed round record.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** F-A's own promotion of assert (ii) is itself refuted at r4 (CHAIN-A); the round record's summary of F-A is therefore not the terminal reading. Counter superseded (`.02`).

**RESOLUTION TRACE:** statement lines 163–212; correction sites 186–192 (the nested r4 strike), 1433.

**TEETH:** ARITHMETIC AUDIT of the applicability chain quoted here — “16 → 48 → 56 → 656/4,176/3,816 → 25,409”. Recomputed at compile time from the sheet's own parameters: 16 twistable (ring,row) instances × (≤2 c′-draws) × 2 variants = 48 twisted towers; 48 + 8 ξ = 1 dense controls = 56 orbit towers; the committed artifact's per-family column then gives 656 (AV), 4,176 (TLAW/PV/INT/CHI/TRS), 3,816 (WRONGLET), and 56 + 656 + 5×4,176 + 3,816 + 1 (ENGGATE) + 0 (LOC) + 0 (COV) = **25,409**. Every link of the chain reproduces. `git cat-file -t 39ea0db` = commit; report file exists.

---

### EFF.LIFTCORNER.12  [repair-round record]  *(SERIES REPAIR-ARC, link 4 — r4)*

**CANONICAL STATEMENT:** `[ASSEMBLED]` from lines 214–257. The head, verbatim:

> “**[REPAIR ROUND r4 — 2026-08-08 campaign (wallclock 2026-08-05).** Applied
> against LIFTCORNER-PE4 (hostile pass, fresh context, on the r3 text — the
> arc's SECOND acceptance attempt; report `LIFTCORNER_passPE4_report.md`,
> commit 8b53efa: **0 CRITICAL + 6 gaps**). PE4 was directed at S1's
> definitions, S4.2/S4.3 end to end, COR 1 + the PROP rider, S5 as the note's
> summary of record, the bracket system as a system, and the ILNRES NR-1
> interplay. **The mathematics held everywhere it pushed** …”

and the POSITIVE fact the round records — the only round in the arc to add one:

> “it also
> established a POSITIVE fact this note now records (S5 STATUS BLOCK, PROVED bullet): **δ₁ = 1 is
> empty at e₀ = 1**, so S4's e₀ ≥ 2 Setting costs COR 1 nothing and the corner
> is covered in full.”

and its structural disposition:

> “**STRUCTURAL:** S5's
> status block — which produced findings in three consecutive passes — is
> REGENERATED from a minimal five-line template; every removed sentence is
> quoted verbatim inside S5's `[r4, ARCHIVE]` bracket.”

Dispositions **F4-1** (`.25`), **F4-2** (shard 2), **F4-3** (`.10`), **F4-4** (`.64`), **F4-5** (`.58`), **F4-6** (shard 2).

**FORM:** bold-headed bracketed round record.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** the δ₁ = 1 emptiness fact is stated here as a PE4 finding and homed in §S5's status block (shard 2). Its pointer was itself wrong at r4 and was corrected at r5/F5-5 — “the r4 header's "(S4.3, COR 1)" pointer re-aimed at the true site, the S5 STATUS BLOCK PROVED bullet”. The text quoted above is the post-r5 reading. Counter superseded (`.02`).

**RESOLUTION TRACE:** statement lines 214–257 (as corrected in place by r5/F5-5, line 273); the target bullet at 1245–1250 (shard 2).

**TEETH:** `LIFTCORNER_passPE4_report.md` exists; `git cat-file -t 8b53efa` = commit.

---

### EFF.LIFTCORNER.13  [repair-round record]  *(SERIES REPAIR-ARC, link 5 — r5)*

**CANONICAL STATEMENT:**

> “**[REPAIR ROUND r5 — 2026-08-08 campaign (wallclock 2026-08-06): MINIMAL round
> against LIFTCORNER-PE5 (`LIFTCORNER_passPE5_report.md`, commit a5212e8:
> **0 CRITICAL + 5 gaps**, all five in the r4 edits), per the ledgered
> arc-dynamics diagnosis (each round's new prose has bred ~5 defects) — exactly
> five one-line fixes, each superseding the quoted prior wording: **F5-1** the
> STATUS BLOCK PROVED line drops "and PROP's rung propagation" (the
> CONDITIONALITY line's "(5) PROP's rung-≥2 clause-(ii) census is OWED" is its
> status of record); **F5-2** the [r4, F4-1] parenthetical "(ψ₁ and K₂ enter no
> counted predicate of S3 and no step of S4)" re-scoped to the ASSERTS (ψ₁ and
> K₂ themselves DO enter S4.2 as shared read data); **F5-3** S3's Q7 bullet
> "c_base = c′·ξ^{D₁}" renamed to c^{Φ′}·ξ^{D₁} and the [r4, F4-5]
> correction-of-record clause extended to S2's sealed Q7 sheet row; **F5-4** the
> [r4, F4-4] bracket's "ITERLAWN_PROOF's S9" corrected to **S7** (the 22-row
> sweep sits in ITERLAWN S7, verified at source; ITERLAWN's S9 is a table-free
> scope box); **F5-5** the r4 header's "(S4.3, COR 1)" pointer re-aimed at the
> true site, the S5 STATUS BLOCK PROVED bullet — plus the STATUS BLOCK ARC-line
> update, NOTHING else; both machine legs BYTE-FROZEN and untouched. Acceptance
> counter unchanged at **0/2**; **PE6 — a fresh hostile pass on THIS text — is
> the next acceptance attempt.**]**”

**FORM:** bold-headed bracketed round record (single paragraph; the round is deliberately one-line-per-fix).

**DERIVATION:** `[RECORD]` The round's own governing principle is the ledgered arc-dynamics diagnosis quoted inline (“each round's new prose has bred ~5 defects”), which is why the round is minimal.

**CONDITIONALITY:** F5-1's removal of “and PROP's rung propagation” from the PROVED line is a **scope-pin** that PRE-DATES AC-1 by four days and independently anticipates it: the note had already stopped claiming PROP as proved before the certifier suspended it. Recorded because it bears on how much AC-1 actually changed (see `.63` and OPEN-CALL 1).

**RESOLUTION TRACE:** statement lines 259–277; targets at 1245 (F5-1), 498–501 (F5-2), 555 (F5-3), 1045 (F5-4), 225 (F5-5).

**TEETH:** F5-4's claim is independently re-verified at compile time: `ITERLAWN_PROOF_2026-08-08.md` line 1148 is `## S7. THE CONDITIONALITY LEDGER (the exact grade of every clause, per rung)`, whose sweep table carries **22 data rows** (24 pipe-lines minus header and separator) — the “22-row sweep sits in ITERLAWN S7” claim reproduces exactly (XREF X07). `git cat-file -t a5212e8` = commit; report file exists.

---

### EFF.LIFTCORNER.14  [repair-round record]  *(SERIES REPAIR-ARC, link 6 — r6)*

**CANONICAL STATEMENT:** `[ASSEMBLED]` from lines 279–309, with the embedded [r7, F7-1] bracket quoted at its own unit (`.59`). The head and the arc's turning point, verbatim:

> “**[REPAIR ROUND r6 — 2026-08-08 campaign (wallclock 2026-08-06): MINIMAL round
> against LIFTCORNER-PE6 (`LIFTCORNER_passPE6_report.md`, commit f2b48e7:
> **0 CRITICAL + 3 gaps** — the arc's first ZERO-defect diff: all 32 r5
> insertions verified true, all five fixes correctly placed, the mathematics
> clean on its sixth hostile reading; all three gaps in record surfaces r5 did
> not touch), same discipline — exactly three record-surface fixes, each
> superseding the quoted prior wording”

The three fixes: **F6-1** brings the STATUS BLOCK and the S4.3 grade box forward to their own r5-updated ARC line; **F6-2** extends the [r4, F4-5] correction-of-record clause to S2's sealed Q9 row, “the THIRD bare-`c′`-as-cocycle site”; **F6-3** supplies the footer dating record's missing r5 line.

**FORM:** bold-headed bracketed round record.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** F6-2's completeness warrant — PE6's “all 42 `c′` occurrences” — is superseded by [r7, F7-1] (`.59`) for its UNIT. The *conclusion* (no fourth site) survives; only the count and its unit change.

**RESOLUTION TRACE:** statement lines 279–309; the embedded correction at 298–303.

**TEETH:** `LIFTCORNER_passPE6_report.md` exists; `git cat-file -t f2b48e7` = commit, `git cat-file -t 46e6e88` = commit.

---

### EFF.LIFTCORNER.15  [repair-round record]  *(SERIES REPAIR-ARC, link 7 — r7, TERMINAL of the series in this shard)*

**CANONICAL STATEMENT:** `[ASSEMBLED]` from lines 311–339. The head, verbatim:

> “**[REPAIR ROUND r7 — 2026-08-08 campaign (wallclock 2026-08-06): ONE-CLAUSE
> round against LIFTCORNER-PE7 (`LIFTCORNER_passPE7_report.md`, commit 58f7060:
> **0 CRITICAL + 1 gap (minor)** — all four r6 hunks verified true and
> correctly placed except one clause; the record system judged CONSISTENT AND
> TRUE AT HEAD for the first time in the arc; r6's disclosed NEXT/AUDIT
> deviation judged CORRECT; the mathematics clean on its SEVENTH hostile
> reading; both machine legs re-run clean), exactly one fix: **F7-1** …”

and the STANDING RULE the round derives — the single most portable output of the whole arc:

> “PROVENANCE: the figure and its unit word originate in PE6's report (its
> F6-2 sweep sentence); r6 TRANSCRIBED them inside quotation marks — the
> arc's documented transcription mechanism, now its THIRD recurrence ([r3,
> F-C]/[r4, F4-3]: PE2's "bit-identically"; [r5] F5-4: PE4's "S9") — standing
> rule henceforth: quote counts only WITH THEIR UNIT AND COMMIT.”

**FORM:** bold-headed bracketed round record.

**DERIVATION:** the standing rule is derived by INDUCTION OVER THE ARC'S OWN DEFECT HISTORY: three independent recurrences of one mechanism (transcribing a supplier's figure without its unit or its commit), each caught by a different pass. This is a `[DERIVED]` methodological conclusion, not a record.

**CONDITIONALITY:** the rule is stated “henceforth”, i.e. it binds later rounds of this note; it is not declared binding on other notes. Whether the corpus adopts it is a Phase-0d question (OPEN-CALL 5).

**RESOLUTION TRACE:** statement lines 311–339; the three cited recurrences at 102–131, 115–131 and 271–273.

**TEETH:** disposition `AUDIT / in-house hostile pass`. The three recurrences are re-verified present in the note at the lines cited. `LIFTCORNER_passPE7_report.md` exists; `git cat-file -t 58f7060` = commit; `git cat-file -t 91f0cde` = commit.

---

### EFF.LIFTCORNER.16  [fence]

**CANONICAL STATEMENT:**

> “**Sources of record:** ILNRES_2026-08-08.md S1 [NR-1] + S5.1 (the spec);
> ITERLAWLIFT_CORNER_2026-08-08.md (wave 18: the LAWFUL slice measured
> 104,404/0; the S7 sketch + its one open step (TAIL-STAB)); ITERLAWN_PROOF
> S0.1 (the standard-lift class pin + the verbatim residual propagation rider);
> GRTW2_PROOF §3.4 (χ-chain/shift-descent), §5 (clause 3 ψ-transport, W2-OPEN-1).”

**FORM:** bold-headed paragraph (inventory).

**DERIVATION:** `[RECORD]` — the note's own import inventory.

**CONDITIONALITY:** this list is the note's declared import set. **It is incomplete as an account of what the note's ARGUMENTS consume**: the four out-of-range certifier annexes (AC-1…AC-5) later import ITERLAWN S4.6's (RM-1) engine and its r6 machine census, neither of which appears here. That is expected — the list is dated 2026-08-08 and the annexes are dated 2026-08-12 — but a DAG built from this sentence alone would miss two live edges.

**RESOLUTION TRACE:** statement lines 341–345.

**TEETH:** all four sources verified to exist and all four designations grep-verified at count 1 — XREFs X01, X02 (ILNRES), X03, X04 (wave 18), X05, X06 (ITERLAWN S0.1), X09, X10 (GRTW2). §3 records counts and lines.

---

### EFF.LIFTCORNER.17  [fence]

**CANONICAL STATEMENT:**

> “**FENCES.** No edit to any accepted text (ITERLAW/ITERLAWN/ILNRES bodies,
> sealed falsifiers, wave-18 artifacts); committed engines consumed READ-ONLY
> (in-memory ledger override only, engine_ext precedent); no Lean change; no
> orders-≥3 machine claim (the battery is 2-read); no gr(w₂) claim; nothing
> here closes NR-1's ledger entry until this note's own acceptance arc runs.”

**FORM:** bold-headed paragraph.

**DERIVATION:** `[RECORD]` — a self-imposed protocol fence.

**CONDITIONALITY:** the final clause is **spent, and its condition was met**: the arc closed (2/2), and the ITERLAWN fold annex then executed the rider rewrite (XREF X14). But the fence's other five clauses are permanent and are the note's NON-IMPORT declaration; see §5.

**RESOLUTION TRACE:** statement lines 347–351; the discharge at 1451 and at ITERLAWN's fold annex.

**TEETH:** verified negatively — `grep -c 'LIFTCORNER\|LIFT-CORNER' ILNRES_2026-08-08.md` = 1, and the single hit is the pre-existing S5.1 spec heading, NOT an absorption append. So NR-1's ILNRES ledger entry is verifiably still unfolded (N2).

---

### EFF.LIFTCORNER.18  [definition]

**CANONICAL STATEMENT:**

> “At g₀ = 1: ψ₀ = y + c₀ (c₀ ≠ 0), K₁ = K₀, z₁ = −c₀ a SCALAR. The full monic
> lift orbit at the corner (deg = e₀d₀, w₁ = e₀h₀, nonzero order-1 residual):
> Φ′ = Φ₀^{e₀} + Σ_{k<e₀} b_kΦ₀^k, deg b_k < d₀, with w₀(b₀) = h₀,
> c′ := res(b₀/π^{h₀}) ≠ 0, and w₀(b_k) ≥ amin(k) := ⌈(e₀−k)h₀/e₀⌉ (k ≥ 1;
> strict-above automatic, gcd(e₀,h₀) = 1).”

**FORM:** display-carrying paragraph (inline ASCII display).

**DERIVATION:** `[DEFINITIONAL]` The orbit is the set of monic lifts with the stated invariants; the constraint `w₀(b_k) ≥ amin(k)` is lawfulness at the corner. The parenthetical “strict-above automatic, gcd(e₀,h₀) = 1” is the fact re-used in S4.1's gain bounds (`.42`) and again by AC-5's (T1).

**CONDITIONALITY:** g₀ = 1 throughout; c₀ ≠ 0; gcd(e₀, h₀) = 1.

**RESOLUTION TRACE:** statement lines 355–359. Untouched by r1–r7. This is SEALED pre-run text (resolution rule 4).

**TEETH:** the notation `c′` defined here is the RESIDUE SCALAR; the collision with the cocycle is fixed at `.58` and censused at `.59`.

---

### EFF.LIFTCORNER.19  [definition]

**CANONICAL STATEMENT:**

> “Stratification by the residue c′:
>
> * c′ = c₀ — the LAWFUL class of ψ₀ (wave-18's slice: measured exact, 0/104,404);
> * c′ ≠ c₀ — the lawful class of the ξ-CONJUGATE ψ₀^{(ξ)} := ξ^{−1}ψ₀(ξy)
>   = y + c₀/ξ at ξ := c₀/c′; letters z₁ = ξ·z₁′, z₁′ := −c′. This is exactly
>   W-2 clause 3's ψ-transport, DEGENERATE at the corner: K₁ = K₀ carries no
>   letter, so the tower transport is the bare scalar substitution z₁ ↦ z₁′
>   (the clause-3 re-coordination step is vacuous). The ε-degeneration the
>   charge names: ε₁-corrections are z₁-powers of a scalar, so the whole
>   value layer transports by one character — the χ-law.”

**FORM:** bulleted display.

**DERIVATION:** `[IMPORTED]` from GRTW2 clause 3 (ψ-transport), specialized: at g₀ = 1 the level-1 residue field extension is trivial, so the transport degenerates to a scalar substitution. The note derives the degeneration, not the clause.

**CONDITIONALITY:** this is the W-2 consumption that caps the unit's grade (`.02`, `.72`); at FC-1 the cap becomes a cap by an accepted supplier.

**RESOLUTION TRACE:** statement lines 359–368. Sealed pre-run text.

**TEETH:** XREF X09 verifies GRTW2 §3.4 exists as `### 3.4 THE (ξ, w) CLOSED FORM (the display of record)` (count 1, line 394); X10 verifies `### 5.3 The value layer: W2-OPEN-1 (displayed open lemma, machine-confirmed)` (count 1, line 881). The wave-18 figure 104,404 is verified in the source at count 3 (X04).

---

### EFF.LIFTCORNER.20  [preregistration]

**CANONICAL STATEMENT:**

> “**CANDIDATE (the transport law, preregistered).** On the tower built on ANY
> orbit member Φ′ (ledger transported: ψ₀ ↦ y + c′, all deeper data
> byte-identical, canonical Φ₂ rebuilt on the transported letter), the accepted
> 2-read display holds WITH THE LETTER THE LIFT CARRIES:
>
>     c′(γ,γ′) = z̄^{δ₂} · (z₁′)^{D₁},   D₁ := (s₁+s₁′−s₁″+ℓ₀γ₂δ₂)/e₀,
>     equivalently  c_base(γ,γ′) = c′(γ,γ′) · ξ^{D₁}   (the χ-ratio law),
>
> with all integer data (splits, D₁, δ₂, windows) lift-independent. The ξ = 1
> slice is wave-18's measured law; the ξ ≠ 1 direction is NEW — no instance
> evidence exists anywhere in the corpus before this battery.”

**FORM:** bold-headed paragraph with an indented ASCII display.

**DERIVATION:** `[PREREGISTERED]` — stated before the run, by construction of the two-commit seal. Its eventual PROOF is `.57` (THE THEOREM) and `.61` (COR 2); its MEASUREMENT is `.28`–`.29`.

**CONDITIONALITY:** **the two occurrences of `c′(γ,γ′)` in this display are the COCYCLE, not the residue scalar of `.18`.** The collision is real, is inside sealed text, and is NOT edited; [r4, F4-5] (`.58`) is the correction of record and [r7, F7-1] (`.59`) counts these two occurrences among the four covered-cocycle sites. A consumer must read `c′(γ,γ′)` here as `c^{Φ′}(γ,γ′)`.

**RESOLUTION TRACE:** statement lines 370–380; correction sites 970–992 (F4-5 + F7-1).

**TEETH:** Q3 TLAW is this prediction's battery row; run-record at `.29` (4,176 checks / 0 violations).

---

### EFF.LIFTCORNER.21  [preregistration]

**CANONICAL STATEMENT:**

> “Roster: the wave-18 rows CA–CF verbatim (all g₀ = 1, E₂ ∈ {4,6,8,6,10,3}),
> × rings {ℤ₂, ℤ₃, F₂[[t]], F₃[[t]]}; windows W1×W1 + mixed W1×W3. Twists
> exist iff |K₀| > 2 (deterministic applicability: d₀ = 2 rows on all rings;
> d₀ = 1 rows on p = 3 rings only; 16 twistable (ring,row) instances). Per
> instance: c′-draws (≤ 2, deterministic enumeration) × variants {pure twist,
> twist + dense tails/mids} = 48 twisted towers; plus the ξ = 1 dense controls
> (rows CB/CF × 4 rings) and the 24 base (standard) towers for the χ-cache.”

**FORM:** inline paragraph (sealed sheet preamble).

**DERIVATION:** `[DESIGN]` The applicability rule (“Twists exist iff |K₀| > 2”) is deterministic, so the instance count is derived, not sampled.

**CONDITIONALITY:** sealed pre-run text; not edited by any round.

**RESOLUTION TRACE:** statement lines 384–390.

**TEETH:** ARITHMETIC AUDIT (v3 rule 22), computed fresh: 16 twistable instances × ≤2 draws × 2 variants ⇒ 48 twisted towers; 48 + 8 dense controls (rows CB/CF × 4 rings) = **56**, which is exactly the committed artifact's GATE count (`GATE      pred 0  obs     0  (    56)  GREEN`) and exactly S3's “56/56 orbit towers”. The two independent routes to 56 agree. The 24 base towers (6 rows × 4 rings) are the χ-cache and are NOT gate-counted — consistent with GATE = 56, not 80.

---

### EFF.LIFTCORNER.22  [preregistration] `[TABLE]`

**CANONICAL STATEMENT:** the sealed thirteen-family prediction sheet, transcribed as a table (source lines 392–406; the source itself renders it as a Markdown table, so no double emission is required):

| family | content | prediction |
|---|---|---|
| Q1 GATE | every generated tower passes the lawfulness gate FOR ITS OWN ψ₀′ (residual = y + c′) | 0 failures |
| Q2 AV | ANCHOR-VAL with the transported ε₁′ (z₁′-powers), letters W1+W3 | 0 |
| Q3 TLAW | **THE CANDIDATE: measured cocycle = transported display (z₁′)** | 0 |
| Q4 PV | L7 PAIR-VAL both forms + single-slot shape, transported letters | 0 |
| Q5 INT | exponent integrality | 0 |
| Q6 LOC | δ₁ = 0 sub-violations (lift-form-free legs; bug detector) | 0 |
| Q7 CHI | cross-tower χ-ratio: c_base == c′·ξ^{D₁}, measured vs MEASURED | 0 |
| Q8 COV | per twisted block: ≥ 1 δ₁ = 1 pair AND ≥ 1 pair with ξ^{D₁} ≠ 1 | met |
| Q9 WRONGLET | control: per-pair (c′ ≠ wrong-letter form) ⟺ (ξ^{D₁} ≠ 1), exact set equivalence; total fires > 0 | 0 / fires |
| Q10 XI1 | the ξ = 1 dense slice reproduces the UNCHANGED display (wave-18 tie) | 0 |
| TRS | closed-form transcription vs C.iter_law (transported automatically) | 0 |
| CERT | base towers: G.T1_T2(nf=4) + G.T5 internal (PARI leg NOT re-run: wave-18 T11 on the same base roster is on file — disclosed reuse) | 0 |
| ENG-GATE | engine_ext.agreement_gate(full=False) re-run in-unit (standing rule) | 0 new |

**FORM:** table (source Markdown table, reproduced as `[TABLE]`).

**DERIVATION:** `[PREREGISTERED]` Committed in commit 1, before any full run.

**CONDITIONALITY:** two rows carry sealed-text defects corrected out of band and neither is edited: **Q7**'s `c′` is the COCYCLE (F4-5/F5-3, `.58`), and **Q9**'s `c′` is likewise the cocycle (F6-2, `.59`). Two rows are NOT independent legs: **Q6 LOC** is a nested derived counter (`.30`), and **CERT**'s PARI leg is disclosed reuse of wave-18 T11 rather than a fresh run.

**RESOLUTION TRACE:** statement lines 392–406; correction sites 970–992 (Q7, Q9), 558–571 (Q6).

**TEETH:** thirteen rows; every row's run-record is `.29`. Zero orphans — see §6.

---

### EFF.LIFTCORNER.23  [instrument-record]

**CANONICAL STATEMENT:**

> “**Disclosures (pre-seal):** (a) a `--shakedown` crash-freedom run (1 ring,
> 2 rows, 1 twist, no json) runs before commit 1; (b) exact arithmetic,
> deterministic full windows, no sampling beyond the seeded pert residues;
> (c) the ledger override (ψ₀ ↦ y + c′) is IN-MEMORY on a fresh Tower object —
> sound because at g₀ = 1 the degree-1 extension arithmetic of K₁ is
> modulus-independent (mk_field_ext at g = 1: products never touch the reducer),
> so ψ₁ and every deeper byte carries over verbatim; **(d) SP bug-detector
> counters recorded.**”

with the structural restoration that governs how the list is read:

> “**[r4, structural — item (d) is RESTORED to the pre-seal list.]** r3 inserted
> its F-A bracket between (c) and (d), leaving (d) hanging off the end of a
> post-hoc correction so that a reader could not tell it belonged to the SEALED
> pre-run disclosure (PE4 §3(e), recorded there but not numbered). The list
> (a)–(d) is now complete and unbroken; the r3/r4 correction brackets follow it.
> No claim changes.”

**FORM:** bold-headed list + a bracketed structural rider.

**DERIVATION:** `[RECORD]` for (a), (b), (d); for (c), the soundness half is DERIVED by reading `mk_field_ext` — see `.26`.

**CONDITIONALITY:** SUPERSESSION KIND: **inventory completion** (the r4 rider restores an item's membership in a list; it changes no claim). Note that (c)'s sentence “so ψ₁ and every deeper byte carries over verbatim” is the sealed claim CHAIN-A is about: it is TRUE, but not for the reason the runner's asserts suggest.

**RESOLUTION TRACE:** statement lines 408–415; the restoration at 417–422.

**TEETH:** disposition `signed vacuity disclosure` for the pair of asserts (`.25`): both are structurally incapable of firing, disclosed as such by the note itself.

---

### EFF.LIFTCORNER.24  [instrument-record]  *(CHAIN-A, link 3)*

**CANONICAL STATEMENT:**

> “* **assert (i) is a SNAPSHOT-CONSISTENCY NO-OP: it cannot fail, and it
>   certifies NOTHING about carryover.** `psi1_base` is snapshotted from the SAME
>   object `T` that is then mutated — `liftcorner_checks.py:36`, one line after
>   `T = LC.make_tower(...)` — and nothing between the snapshot and the assert
>   writes `T.psi1`. Exhaustively: `T.psi1` is assigned exactly ONCE, in
>   `Tower.__init__` (`grb_order2_check.py:515` …), i.e. BEFORE `make_orbit_tower` ever sees `T` (and with
>   no override on this path — `LC.make_tower` passes none); the override block
>   writes only `T.psi0`, `T.K1`, `T.z1`, `T.Phi1_std`; `LC.apply_pert`
>   (`iterlawlift_corner.py:145–155`) writes only `T.Phi1` and `T.Phi2`, as its
>   own docstring says; and `build_Phi2` (`grb_order2_check.py:651`) only READS
>   `self.psi1`. So (i) compares `T.psi1` against a copy of itself across code
>   that provably never touches it. In particular it never RECOMPUTES ψ₁ on the
>   transported K₁ — the one act that could have made it a carryover check.
>   Its honest job is a REGRESSION GUARD against a future edit that makes the
>   override path (or `apply_pert`/`build_Phi2`) recompute ψ₁.”

**FORM:** bulleted display inside a dated bracket.

**DERIVATION:** an EXHAUSTIVE MUTATION TRACE over the runner's write sites — the note enumerates every assignment to `T.psi1` and every writer between snapshot and assert. This is a source-reading derivation, not a measurement.

**CONDITIONALITY:** the trace is pinned to specific file:line coordinates in four scripts. Those pins are NOT covered by the two-commit seal in the way the runner is; see §3.5 and OPEN-CALL 4.

**RESOLUTION TRACE:** statement lines 439–455; the round record's summary at 74–78; the r1 wording it supersedes, quoted in full at 426–433.

**TEETH:** `AUDIT` disposition, class **decorrelated-model audit** — the note is explicit that no tooth caught this: “both later passes signed off on the unfixed half — PE1 called (i) "genuine", PE2 checked only that the quoted source line matched verbatim (a text match, not a semantic one) — so the overstatement survived two hostile readings before PE3 traced the mutations.”

---

### EFF.LIFTCORNER.25  [instrument-record]  *(CHAIN-A — TERMINAL)*

**CANONICAL STATEMENT:**

> “**[r4, F4-1 — THE FINAL DESCRIPTION OF THE PAIR, promoting nothing.] BOTH
> asserts are INERT: neither can fire on any input this battery generates.**
> (i) is a snapshot-consistency no-op — a regression guard against a future edit
> that recomputes ψ₁ on the transported K₁; (ii) is a comparison of two
> occurrences of a constant — a regression guard against a future change of the
> (d₀, g₀, g₁) ↦ identity-element representation. **NO CHAIN STEP CONSUMES
> EITHER**: the ψ₁-site walk below establishes it for (i), and the same walk
> gives it for (ii) verbatim (the ASSERTS enter no counted predicate of S3 and
> no proof step of S4; ψ₁ and K₂ themselves enter S4.2 as shared read data).
> **The soundness of the K₂ layer lives in `mk_field_ext`'s g = 1
> reading** — `grb_order2_check.py:345`, where the reduction loop
> `range(len(out)−1, g−1, −1)` is `range(0, 0, −1)`, empty, so products never
> touch the reducer — **not in either assert.**”

with the arc sentence the round writes to prevent recurrence:

> “*Arc of this pair, recorded in
> one sentence so that no future round re-promotes either half:* r0 described it
> ("ψ₁ bytes equal, K₂ arithmetic representation shared"), r1 promoted (i), r3
> promoted (ii), and **r4 demotes both** — every promotion so far has been an
> overclaim, and there is no third half left to promote.”

**FORM:** bold-headed bracketed rider.

**DERIVATION:** for (ii), a two-level composition argument read off `mk_field_ext`'s source (lines 466–478): `g = len(psi) − 1` and `one = tuple([K["one"]] + [K["zero"]]*(g−1))` never read a coefficient of `psi`, so `K2["one"]` is a constant of `(d₀, g₀, g₁)`; verified “at r4 from source AND empirically on the note's own d₀ = 2 row CB over ℤ₂ … `K2["one"] = (((1,0),),)` on the base tower, on both twist draws c′, and again with ψ₁ perturbed”.

**CONDITIONALITY:** the parenthetical is **re-scoped by [r5, F5-2]**: the claim of non-entry belongs to the ASSERTS, not to ψ₁ and K₂ themselves, which DO enter S4.2 as shared read data. The text quoted above is already the post-F5-2 reading (the note applied the fix in place). SUPERSESSION KIND: **scope-pin**.

**RESOLUTION TRACE:** statement lines 493–509; the derivation for (ii) at 456–485; the F5-2 re-scoping recorded at 266–268; the restatement site at 79–86.

**TEETH:** disposition `signed vacuity disclosure` + `disclosed non-repair` — two guards that never fired and provably cannot, disclosed rather than removed. The note's positive replacement (the `mk_field_ext` reading) is `.26`.

---

### EFF.LIFTCORNER.26  [derivation]

**CANONICAL STATEMENT:**

> “The modulus-independence itself is
> verified by READING `mk_field_ext`: at g = 1 its reduction loop
> `range(len(out)-1, g-1, -1)` is empty, so products never touch the reducer —
> that is where the override's soundness lives (PE1 F4 re-derived it there
> independently; PE3 re-derived it independently again AND checked the consequence
> the sheet actually needs, which no assert checks: at g₀ = 1 the K₁ elements are
> 1-tuples over K₀ with modulus-free multiplication, so `_field_elems(K1)`
> enumerates them in a c′-independent order and `pick_irreducible(K1, g1, idx)`
> returns the same ψ₁ bytes for every residue c′ — i.e. the transported ψ₁ IS
> the base ψ₁, as a fact about the code, not as a machine assertion) — not in
> the runner's asserts.”

together with the ψ₁-site walk that fences the asserts out of the chain:

> “Checked at r3 by walking every ψ₁ site in the note: S2 (c)'s own soundness
> claim is discharged by READING `mk_field_ext` (next sentence), not by the
> asserts; S3's figures are the runner's counted families (GATE/AV/TLAW/PV/INT/
> CHI/COV/WRONGLET/TRS/CERT/ENG-GATE), and ψ₁ enters none of their predicates;
> and S4.2 READ-EQ's "the towers share every read datum (reads, ψ₁, K₂, …)" is a
> statement about the Φ′- and Φ″-TOWERS OF THE PROOF, proved from the S4 setting
> (both are monic lifts over the same K₁ = K₀ at g₀ = 1), with no dependence on
> any runner assert.”

**FORM:** inline paragraphs.

**DERIVATION:** a source reading (the empty reduction loop) plus an exhaustive site walk. **This is the unit that actually discharges disclosure (c)'s soundness claim**; `.23`, `.24`, `.25` are the wrong-turn history around it.

**CONDITIONALITY:** the walk is over “every ψ₁ site in the note” as of r3; nothing later re-opens it.

**RESOLUTION TRACE:** derivation lines 511–530; the site walk at 511–519.

**TEETH:** independently re-derived by two hostile passes (PE1 F4, PE3), per the note's own parenthetical — disposition `accepted-with-decorrelation-supplied`.

---

### EFF.LIFTCORNER.27  [supersession rider]

**CANONICAL STATEMENT:**

> “**[r3, F-A, fence disclosure]** The SEALED runner's own
> module docstring carries the same overstatement ("the runner ASSERTS psi1-byte
> carryover and shared K2 representation", `liftcorner_checks.py:14`); it is
> BYTE-FROZEN by the two-commit seal and is therefore NOT corrected — the seal
> outranks the wording, and this bracket is the correction of record. Anyone
> reading that docstring should read it as **[r4, F4-1 — the re-reading
> instruction is corrected; the r3 wording, quoted and superseded, was "assert
> (i) is a regression guard, assert (ii) is a one-element check on two objects,
> and the soundness is in `mk_field_ext`"]**: **BOTH asserts are inert
> regression guards that certify nothing about carryover**, and the soundness is
> in `mk_field_ext`'s g = 1 reading.”

**FORM:** bracketed rider with a nested dated correction.

**DERIVATION:** `[RECORD]` + the general principle that a byte-frozen instrument is corrected by a bracket, not by an edit (effective-text rule (iii)).

**CONDITIONALITY:** SUPERSESSION KIND: **license** — it licenses a re-reading of a frozen artifact's text without editing it. **TARGETS:** `verification/openmath/liftcorner_checks.py:14` (an artifact, not a note span), plus the S1 CANDIDATE display (`.20`) and S2's Q7/Q9 rows (`.22`) under the parallel precedent named at `.58`.

**RESOLUTION TRACE:** statement lines 530–540.

**TEETH:** PIN VERIFICATION: `liftcorner_checks.py` exists and is md5-frozen as quoted. The docstring line number (`:14`) is asserted of the sealed file; the file is byte-frozen by the seal, so the pin is stable — this is the one code pin in the note whose stability is *guaranteed* by a freeze predicate.

---

### EFF.LIFTCORNER.28  [run-record]

**CANONICAL STATEMENT:**

> “**ALL GREEN, FIRST RUN, exit 0** — 25,409 checks, **0 violations in every
> family**, elapsed 4.4 s (`liftcorner_checks_output.txt`,
> `liftcorner_checks_results.json`; these govern on any transcription
> discrepancy)”

**FORM:** bold-headed paragraph, under the §S3 heading whose own text carries the seal pins: “**S3. VERDICT (commit 2; from the artifacts; seal dafc0b5, runner byte-untouched, md5 ccb4351c92573f5f962cae4ae952d8dd)**”.

**DERIVATION:** `[RUN]` — read off the committed artifacts, which the note declares governing on any transcription discrepancy. That declaration is what makes the compile-time recount below authoritative rather than presumptuous.

**CONDITIONALITY:** “FIRST RUN” is a design claim (no re-run to green); it is warranted by the two-commit seal, not by the artifact.

**RESOLUTION TRACE:** statement lines 542–548.

**TEETH:** RE-VERIFIED AT COMPILE TIME against `verification/openmath/liftcorner_checks_output.txt`: the artifact's final block reads `TOTAL checks 25409  elapsed 4.4s` and `VERDICT: ALL GREEN`, and every family line reads `pred 0  obs     0`. Exact match, including the 4.4 s the later rounds contrast with the 4.3 s re-runs.

---

### EFF.LIFTCORNER.29  [run-record] `[TABLE]`

**CANONICAL STATEMENT:** the per-family results, source lines 550–578. The source renders them as a bulleted narrative, so per v3 rule 14 the *source display* is quoted first, then transcribed as a table. Source, verbatim (abridged only where a bullet is compiled at its own unit, marked `…`):

> “* Q1 GATE 56/56 orbit towers pass the lawfulness gate for their OWN ψ₀′
>   (48 twisted + 8 ξ = 1 dense controls — exactly the deterministic
>   applicability counts of the sheet); Q2 AV 656/0;
> * **Q3 TLAW 4,176/0 — THE CANDIDATE: the display holds with the letter the
>   lift carries (z₁′ = −c′) on every ξ-twisted tower**, both pair blocks;
> * **Q7 CHI 4,176/0 — the χ-ratio law c_base = c^{Φ′}·ξ^{D₁} EXACT, measured
>   against measured** (no closed form in the comparison): the W-2 covariance
>   carries the corner;
> * Q4 PV / Q5 INT / TRS 4,176/0 each; … [Q6 LOC: unit `.30`]
> * Q8 COV met — min 6 δ₁ = 1 pairs and min 6 teeth pairs (ξ^{D₁} ≠ 1) per
>   twisted block; Q9 WRONGLET: per-pair set equivalence EXACT on 3,816
>   samples, total fires 1,576 > 0 (the wrong-letter form fails exactly where
>   ξ^{D₁} ≠ 1 — the transport is sharp, not slack);
> * Q10 XI1: the ξ = 1 dense slice reproduces the unchanged display (wave-18
>   tie re-confirmed); CERT internal 0; ENG-GATE 0 new (full=False disclosed);
>   SP bug-detector 0.”

`[TABLE]` — transcription, with the compiler's independent recount from the committed artifact in the last column:

| family | note's reported result | artifact line (`liftcorner_checks_output.txt`) | agrees |
|---|---|---|:-:|
| Q1 GATE | 56/56 towers pass | `GATE      pred 0  obs     0  (    56)  GREEN` | ✓ |
| Q2 AV | 656/0 | `AV        pred 0  obs     0  (   656)  GREEN` | ✓ |
| Q3 TLAW | 4,176/0 | `TLAW      pred 0  obs     0  (  4176)  GREEN` | ✓ |
| Q4 PV | 4,176/0 | `PV        pred 0  obs     0  (  4176)  GREEN` | ✓ |
| Q5 INT | 4,176/0 | `INT       pred 0  obs     0  (  4176)  GREEN` | ✓ |
| Q6 LOC | 0 checks / 0 violations | `LOC       pred 0  obs     0  (     0)  GREEN` | ✓ |
| Q7 CHI | 4,176/0 | `CHI       pred 0  obs     0  (  4176)  GREEN` | ✓ |
| Q8 COV | met (min 6 / min 6) | `COV       pred 0  obs     0  (     0)  GREEN` + `coverage min d1-pairs 6; teeth min 6` | ✓ |
| Q9 WRONGLET | 3,816 samples, 1,576 fires | `WRONGLET  pred 0  obs     0  (  3816)  GREEN` + `WRONGLET total fires 1576 (pred > 0)` | ✓ |
| TRS | 4,176/0 | `TRS       pred 0  obs     0  (  4176)  GREEN` | ✓ |
| ENG-GATE | 0 new | `ENGGATE   pred 0  obs     0  (     1)  GREEN` | ✓ |
| CERT | internal 0 | `CERT      pred 0  obs     0  internal T1/T2(nf=4)+T5  GREEN` | ✓ |
| Q10 XI1 | reproduces the unchanged display | (no separate counter; carried inside the TLAW/CHI blocks over the 8 dense controls) | see note |

**MANDATORY ARITHMETIC AUDIT (v3 rule 22), computed fresh:**
56 + 656 + 4,176 + 4,176 + 4,176 + 0 + 4,176 + 0 + 3,816 + 4,176 + 1 + 0 = **25,409**, matching `TOTAL checks 25409` exactly. Cross-check against the note's own applicability chain “16 → 48 → 56 → 656/4,176/3,816 → 25,409” (`.11`): reproduces at every link. **Compiler observation, not in the note:** the single ENG-GATE check is load-bearing for the total — without it the family column sums to 25,408. The note nowhere displays ENG-GATE's count of 1, so a reader recomputing 25,409 from §S3's prose alone will be one short. Recorded as a completeness gap in the note's evidence display, not as an error (OPEN-CALL 2).

**FORM:** bulleted display (source) → table (transcription).

**DERIVATION:** `[RUN]`

**CONDITIONALITY:** Q10 XI1 has no counter of its own in the artifact; its verdict rides the TLAW/CHI counts restricted to the 8 dense controls. The note asserts the tie re-confirmed; the artifact cannot be used to isolate it. Disposition `UNPINNED` for the Q10-specific figure (there is none), `verified` for every other row.

**RESOLUTION TRACE:** statement lines 550–578; the Q6 bullet is unit `.30`; the Q7 bullet already carries the F5-3 rename in place (`c^{Φ′}`, not `c′`).

**TEETH:** this unit IS the teeth for `.22`'s thirteen preregistered rows; the inverse map is §6.

---

### EFF.LIFTCORNER.30  [run-record / disclosure]

**CANONICAL STATEMENT:**

> “**[r3, F-E — the one omitted family
> count, supplied; the r2 wording "Q6 LOC 0 (no δ₁ = 0 anomaly)" STRICKEN as
> reading like an affirmative observation on a probed stratum]** Q6 LOC
> **0 checks counted / 0 violations**: the runner emits no `note("LOC")` call
> at all, so LOC has no check counter and contributes 0 of the 25,409 (the
> committed artifact reads `LOC       pred 0  obs     0  (     0)  GREEN`), and
> `viol("LOC", …)` fires only NESTED inside the violation branches of PV, INT
> and TLAW. So LOC's content is LOGICALLY IMPLIED by those three being green and
> carries no information they do not already carry — it is the nested bug
> detector S2's sheet row calls it, not an independent leg. A reader tallying
> S2's thirteen prediction families as thirteen independent legs over-counts by
> one. (Q8 COV also counts 0 but is NOT in this position: its `if ncov == 0` /
> `nteeth == 0` checks can fire independently of every other family, and its
> substance is reported explicitly in the next bullet.)”

**FORM:** bracketed rider replacing a bullet.

**DERIVATION:** a source reading of the runner's emit sites (`note("LOC")` never called; `viol("LOC", …)` only nested), plus the logical consequence.

**CONDITIONALITY:** SUPERSESSION KIND: **replacement** (of the r2 bullet). The disclosure DOWNGRADES the evidence base by one leg — thirteen families, twelve independent.

**RESOLUTION TRACE:** statement lines 558–571; the r2 wording it strikes is quoted inside the bracket.

**TEETH:** disposition `disclosed non-repair` — a guard that never fired, disclosed rather than removed. The artifact quotation is re-verified verbatim at compile time: the committed file's line 31 is exactly `LOC       pred 0  obs     0  (     0)  GREEN`, spacing included.

---

### EFF.LIFTCORNER.31  [scope record]

**CANONICAL STATEMENT:**

> “STATUS EFFECT of S3 alone (before S4): the ξ ≠ 1 orbit direction — where NO
> corpus evidence existed — is now MEASURED-TRANSPORT-EXACT: the displays
> change under the lift orbit by EXACTLY the χ-law, W-2 clause 3's prediction
> degenerate at the corner. The S4 compose is earned per the seal condition.”

**FORM:** inline paragraph.

**DERIVATION:** `[RECORD]` The “earned” clause discharges the probe-first condition stated in the header (`.01`): the COMPOSE is “written only on a 0-violation verdict”.

**CONDITIONALITY:** “MEASURED-TRANSPORT-EXACT” is an instance claim over the 56-tower roster; it is not, and is not stated as, a proof. The proof is `.57`.

**RESOLUTION TRACE:** statement lines 580–583.

**TEETH:** guarded by `.28`/`.29`; the seal condition itself is guarded by the two-commit protocol at `.03`.

---
### EFF.LIFTCORNER.32  [convention]

**CANONICAL STATEMENT:**

> “Setting: the S1 corner (g₀ = 1, e₀ ≥ 2; at e₀ = 1 no Case II exists —
> COR-3's degeneration, theorem-backed, outside this unit). Φ′ an orbit member
> with residue c′; Φ″ := Φ₀^{e₀} + lift(c′)·π^{h₀} the STANDARD lift of
> ψ₀^{(ξ)} = y + c′. Base facts as [IL S1]/[ILN] S0.2 (division algorithm by
> monic keys, w₀ a valuation, res additive + kills strict π-excess), plus:”

**FORM:** inline paragraph (section setting).

**DERIVATION:** `[IMPORTED]` base facts from [IL]/[ILN] S0.2; the e₀ ≥ 2 restriction is justified by COR-3's degeneration.

**CONDITIONALITY:** e₀ ≥ 2 throughout §S4. **The cost of this restriction is ZERO and that is a proved fact, not an assumption**: PE4 established “δ₁ = 1 is EMPTY at e₀ = 1” (`.12`, homed at the §S5 STATUS BLOCK PROVED bullet in shard 2), so COR 1's corner is covered in full.

**RESOLUTION TRACE:** statement lines 587–591; the emptiness fact at 225–227 and 1245–1249.

**TEETH:** PE4 re-derived READ-EQ “digit by digit on both towers”; the e₀ = 1 emptiness is the round's one positive finding.

---

### EFF.LIFTCORNER.33  [definition]

**CANONICAL STATEMENT:**

> “**[r1, F2 — notation, defined here at first use.]** The b₀-SPLIT, used by the
> S4.1 branch table and by S4.2 and imported from wave-18 S1
> (ITERLAWLIFT_CORNER_2026-08-08.md S1, a source of record above; it was used
> in the r0 text without an in-note binding):
>
>     b₀ = ĉ′·π^{h₀} + t₀,   deg ĉ′ < d₀, res(ĉ′) = c′ ≠ 0 (so w₀(ĉ′) = 0),
>                             deg t₀ < d₀, w₀(t₀) ≥ h₀ + 1.”

**FORM:** bracketed rider carrying a display.

**DERIVATION:** existence and uniqueness given a choice of lift, proved in place:

> “Existence and uniqueness given a choice of the lift ĉ′ of c′: w₀(b₀) = h₀ (S1)
> lets one divide b₀ by π^{h₀}, take ĉ′ := any degree-<d₀ lift of the residue
> c′ = res(b₀/π^{h₀}), and set t₀ := b₀ − ĉ′π^{h₀}, whose residue at level h₀
> vanishes — i.e. w₀(t₀) ≥ h₀+1. "ĉ′π^{h₀}" is the b₀-MAIN part, "t₀" the
> b₀-TAIL; the STANDARD lift Φ″ is the orbit member with ĉ′ = lift(c′) and
> t₀ = 0 and all mids b_k = 0 (k ≥ 1).”

**CONDITIONALITY:** uniqueness is relative to the choice of lift ĉ′ — the note says so explicitly. A consumer must not read the split as canonical.

**RESOLUTION TRACE:** statement lines 593–599; derivation 601–606. Added at r1 (the r0 text used it unbound).

**TEETH:** charge item (3) covers the base-fact status of the surrounding sub-lemma; the split itself is imported from wave-18 S1 (XREF X03).

---

### EFF.LIFTCORNER.34  [lemma]

**CANONICAL STATEMENT (frozen text):**

> “**CONTENT (sub-lemma).** For monic Φ, the digits of dev(F, Φ) satisfy
> w₀-content ≥ w₀-content(F). *Proof:* induction through the division step —
> each subtraction removes lc(F)·x^i·Φ with lc(F) a coefficient of the current
> remainder; w₀ is a valuation. ∎”

**CANONICAL STATEMENT (EFFECTIVE — this is what a consumer must use):** superseded out of range by **AC-2** (lines 1541–1552):

> “**CONTENT (integral-key form).** Let \(\Phi\in\mathcal O[x]\) be monic and \(F\in\mathcal O[x]\). Every coefficient of every digit of \(\operatorname{dev}(F,\Phi)\) has valuation at least \(w_0\text{-content}(F)\).”

**FORM:** bold-headed paragraph with an inline proof (frozen); replacement is a bold-headed display lemma.

**DERIVATION (effective):** AC-2's proof, quoted in full at shard-2 unit for AC-2; its load-bearing step is that **every coefficient of Φ lies in 𝒪**, so `λx^iΦ` keeps valuation ≥ c under subtraction. The frozen proof's “for monic Φ” omitted integrality and is literally too broad.

**CONDITIONALITY:** SUPERSESSION KIND: **replacement**. AC-2's consumer sweep is explicit that nothing downstream moves:

> “**Consumer sweep.** S4.1 applies CONTENT only to
> \(a b=r+q\Phi_0\), where \(a,b,\Phi_0\in\mathcal O[x]\) and \(\Phi_0\) is monic. Hence the bounds \(w_0(r),w_0(q)\ge w_0(ab)\), all eight per-digit \(\omega\)-gain bounds, the lexicographic induction, TAIL-STAB, READ-EQ, the THEOREM and both corollaries survive unchanged. No consumer uses CONTENT for a monic polynomial with a nonintegral coefficient. The counterexample \(\Phi=x+p^{-1}\) is excluded precisely because \(\Phi\notin\mathcal O[x]\).”

**TARGETS:** `34` (this unit) only. No other in-range span is touched.

**RESOLUTION TRACE:** statement lines 608–611; correction site 1535–1552 (shard 2, finding 3 REAL + AC-2).

**TEETH:** charge item (3) — “the CONTENT sub-lemma's base-fact status” — is precisely the item the certifier's finding hit. The teeth were correctly aimed and the in-house passes did not fire: disposition `AUDIT / decorrelated-model audit`.

---

### EFF.LIFTCORNER.35  [lemma]

**CANONICAL STATEMENT:**

> “For X = a·Φ₀^m·Φ′^j (a ∈ O[x], deg a < d₀) put the LEDGER weight
> ω(X) := e₁(e₀·w₀(a) + m·h₀) + j·γ₂, γ₂ = e₁e₀h₀ + h₁. Then in the double
> development X = Σ_j A_jΦ′^j, A_j = Σ_i a_{ji}Φ₀^i (dev by Φ′ then Φ₀):
>
>     (LEDGER)  every nonzero digit obeys e₁(e₀·w₀(a_{ji}) + i·h₀) + jγ₂ ≥ ω(X).”

**FORM:** display lemma under the §S4.1 heading “**LEMMA (TAIL-STAB) — the wave-18 open step, closed (proof REPAIRED at r1; statement byte-unchanged)**”.

**DERIVATION:** the lexicographic induction of `.37`–`.42`, closed at `.47`–`.48`.

**CONDITIONALITY:** the STATEMENT is byte-unchanged across the whole arc, including through the CRITICAL. That is load-bearing: the r1 repair replaced a proof, not a theorem. Note the deliberate uniformity: “the statement is proved for every (a, m, j) with deg a < d₀, uniformly in j.”

**RESOLUTION TRACE:** statement lines 615–619; heading 613; proof lines 625–849 (three ranges, per v3 rule 12: statement 615–619, proof 625–849, correction sites 676–723 and 802–812 and 822–843).

**TEETH:** charge items (1), (2) and (7); PE2, PE3 and PE4 each re-derived the load-bearing pieces independently. This is the note's central theorem and the wave-18 open step: XREF X03 verifies wave-18's `**Step 2 (THE ONE OPEN STEP — displayed lemma (TAIL-STAB)).**` at count 1, line 191, and its honesty box `**Honesty box.** (TAIL-STAB) is UNPROVED` at line 207.

---

### EFF.LIFTCORNER.36  [lemma]

**CANONICAL STATEMENT:**

> “Hence w₂(X) ≥ ω(X), and for any read weight Γ < ω(X) every level-2 read of X
> at Γ contributes 0 at every grid slot (on-line: strict-excess summands die in
> res; off-line: C_j = 0; digit collisions: w₀ ultrametric, min bounds survive).”

**FORM:** inline sentence (the consumer-facing form of `.35`).

**DERIVATION:** immediate from (LEDGER) plus the ultrametric and the res-kills-strict-excess base fact of `.32`.

**CONDITIONALITY:** this is the form READ-EQ actually consumes (“by TAIL-STAB every digit they generate stays > Γ”, `.56`).

**RESOLUTION TRACE:** statement lines 621–623.

**TEETH:** charge item (4) covers the READ-EQ close that consumes it; PE1 re-verified “the (LEDGER) ⟹ w₂(X) ≥ ω(X) tie and the read-kill close”.

---

### EFF.LIFTCORNER.37  [derivation]

**CANONICAL STATEMENT:**

> “*Proof (r1).* Induction on the pair (m, deg a) in the LEXICOGRAPHIC order on
> ℕ × ({−∞} ∪ {0,…,d₀−1}) — m first, then deg a, with deg 0 := −∞ (a zero
> coefficient contributes no digit and generates no child). Lex products of
> well-orders are well-founded, which is all the induction uses; the statement
> is proved for every (a, m, j) with deg a < d₀, uniformly in j.
>
> **Base m < e₀** (any deg a): deg(aΦ₀^m) ≤ (d₀−1) + (e₀−1)d₀ < e₀d₀ = deg Φ′,
> so by dev uniqueness the double dev is the single digit a at (i, j) = (m, j):
> (LEDGER) with equality.”

**FORM:** italic-headed proof paragraph.

**DERIVATION:** self-contained (degree count + dev uniqueness).

**CONDITIONALITY:** the base case is the ONLY base the induction needs — `.46` proves the second coordinate needs none.

**RESOLUTION TRACE:** proof lines 625–633. NEW at r1 (the r0 proof used a single induction on m).

**TEETH:** PE1 re-verified the base case; charge item (2) covers the order's well-foundedness.

---

### EFF.LIFTCORNER.38  [derivation]

**CANONICAL STATEMENT:**

> “**Step m ≥ e₀:** one pass of the orbit identity Φ₀^{e₀} = Φ′ − b₀ −
> Σ_{k≥1}b_kΦ₀^k gives X = aΦ₀^{m−e₀}Φ′^{j+1} − ab₀Φ₀^{m−e₀}Φ′^j −
> Σ_{k≥1} ab_kΦ₀^{m−e₀+k}Φ′^j, with b₀ = ĉ′π^{h₀} + t₀ split as above. Each
> level-0 coefficient is a product a·b with b ∈ {1, ĉ′π^{h₀}, t₀, b_1, …,
> b_{e₀−1}}, so deg(a·b) ≤ deg a + d₀ − 1 < 2d₀ and its Φ₀-redigit
> a·b = r + qΦ₀ has deg r, deg q < d₀ with w₀(r), w₀(q) ≥ w₀(a·b) ≥
> w₀(a) + w₀(b) by CONTENT. Every child is again of the lemma's shape.”

**FORM:** bold-headed proof paragraph.

**DERIVATION:** the orbit identity of `.18`, the b₀-split of `.33`, and CONTENT (`.34`, effective = AC-2's integral-key form).

**CONDITIONALITY:** the two-digits-per-branch bound rests on `deg(a·b) < 2d₀`, which forbids a redigit cascade. PE2 re-derived both independently (see `.45`).

**RESOLUTION TRACE:** proof lines 635–641.

**TEETH:** charge item (1) (census completeness) is exactly the claim that this pass produces no branch outside rows 1–7; the durable machine leg is A7 (`.44`).

---

### EFF.LIFTCORNER.39  [table]  `[TABLE]`

**CANONICAL STATEMENT:** the seven-genre child census, source lines 644–657. Source preamble, verbatim:

> “**(A) THE CHILD CENSUS — seven genres** (this case list matches the genre
> list of the r1 examples-first table under the explicit 9 ↦ 7 label mapping
> displayed in the machine-leg bracket below; the two coordinates are read off
> per row, then justified):”

`[TABLE]` — the source's own Markdown table, transcribed unaltered:

| # | child genre | a′ | (m′, j′) | m-descent | lex (m, deg a) descent | ω-gain ≥ |
|---|---|---|---|---|---|---|
| 1 | key | a | (m−e₀, j+1) | m′ ≤ m−2 | 1st coord | γ₂ − e₁e₀h₀ = h₁ > 0 |
| 2 | b₀-main r-digit | −r(aĉ′π^{h₀}) | (m−e₀, j) | m′ ≤ m−2 | 1st | **0** (the only 0-gain genre) |
| 3 | b₀-main q-digit | −q(aĉ′π^{h₀}) | (m−e₀+1, j) | m′ ≤ m−1 | 1st | e₁h₀ |
| 4 | b₀-tail r-digit | −r(a t₀) | (m−e₀, j) | m′ ≤ m−2 | 1st | e₁e₀ |
| 5 | b₀-tail q-digit | −q(a t₀) | (m−e₀+1, j) | m′ ≤ m−1 | 1st | e₁e₀ + e₁h₀ |
| 6 | mid r-digit, 1 ≤ k ≤ e₀−1 | −r(a b_k) | (m−e₀+k, j) | m′ ≤ m−1 | 1st | e₁ |
| 7a | mid q-digit, 1 ≤ k ≤ e₀−2 | −q(a b_k) | (m−e₀+k+1, j) | m′ ≤ m−1 | 1st | e₁(h₀+1) |
| 7b | **mid q-digit at k = e₀−1 (the TOP mid)** | −q(a b_{e₀−1}) | **(m, j)** | **NONE: m′ = m** | **2nd: deg a′ ≤ deg a − 1** | e₁(h₀+1) |

**FORM:** table.

**DERIVATION:** read off the pass identity (`.38`); each column justified at `.40` (m′), `.41` (row 7b's second coordinate), `.42` (gains).

**CONDITIONALITY:** the table is the effective replacement for the r0 four-row per-branch table; the eight per-digit gain entries are NEW at r1 (charge item (7)).

**RESOLUTION TRACE:** statement lines 644–657.

**TEETH:** ARITHMETIC AUDIT: the row inventory yields the branching bound of `.48` — 1 (row 1) + 4 (rows 2–5, per digit) + (e₀−1) (row 6) + (e₀−1) (rows 7a+7b) = **2e₀+3**, reproduced independently below. The committed table's observed genre labels map 9 ↦ 7 as claimed (`.43`).

---

### EFF.LIFTCORNER.40  [derivation]

**CANONICAL STATEMENT:**

> “*The m′ column.* Read off the pass identity (a q-digit sits one Φ₀-power
> above its r-digit). Rows 1–5 use e₀ ≥ 2 (the S4 setting; e₀ = 1 is COR-3's
> degeneration, out of scope): m−e₀ ≤ m−2 and m−e₀+1 ≤ m−1. Row 6:
> k ≤ e₀−1 ⟹ m−e₀+k ≤ m−1. Row 7a: k ≤ e₀−2 ⟹ m−e₀+k+1 ≤ m−1. Row 7b:
> k = e₀−1 gives m′ = m exactly — the one m-preserving genre.”

**FORM:** italic-headed proof paragraph.

**DERIVATION:** arithmetic on the exponents, case by case. Verified at compile time: each of the five inequalities is elementary and holds as stated under e₀ ≥ 2.

**CONDITIONALITY:** rows 1–5 CONSUME e₀ ≥ 2; at e₀ = 1 the m-descent claim of rows 1–5 fails. AC-5 later handles exactly that flat case for its own DEV-1 reduction (“At \(e_0=1\), the analogous \(b_0\) \(q\)-child can preserve \(m\), but its coefficient degree likewise drops”) — which is a NEW fact, not a LIFTCORNER one, and does not retroactively widen this unit.

**RESOLUTION TRACE:** proof lines 659–663.

**TEETH:** A1/A2 (`.44`) assert lex descent and the 7b characterization on 752 nodes.

---

### EFF.LIFTCORNER.41  [derivation]

**CANONICAL STATEMENT:**

> “*Row 7b drops the second coordinate.* Its q-digit is nonzero only if
> deg(a b_{e₀−1}) ≥ d₀, and then, using only deg b_k < d₀ (S1),
>
>     deg a′ = deg q = deg(a b_{e₀−1}) − d₀ ≤ deg a + (d₀−1) − d₀ = deg a − 1.
>
> So every one of the seven genres has (m′, deg a′) <_lex (m, deg a) and the IH
> applies to every child.”

**FORM:** italic-headed proof paragraph with a display.

**DERIVATION:** a degree count using only `deg b_k < d₀` from `.18`.

**CONDITIONALITY:** none beyond the S1 orbit constraints. This is the single inequality that repairs the CRITICAL.

**RESOLUTION TRACE:** proof lines 665–671.

**TEETH:** PE2 re-derived it “correct at the deg a = 0 and deg b = 0 edges”; A2 asserts it on all 220 observed 7b children (`.44`).

---

### EFF.LIFTCORNER.42  [derivation]  *(CHAIN-C — TERMINAL)*

**CANONICAL STATEMENT:** the effective per-digit gain derivation, verbatim (source lines 673–687):

> “*The ω-gains.* For a branch with factor b at Φ₀-exponent M = m−e₀+k and
> w₀(b) ≥ β, a digit a′ landing at Φ₀-exponent M′ has
> gain = e₁[e₀(w₀(a′) − w₀(a)) + (M′−m)h₀], with M′ = M for the r-digit and
> M′ = M+1 for the q-digit. **[r2, G4 — the q-digit bound RE-DERIVED; the r1
> identity STRICKEN.]** CONTENT is applied to EACH digit separately: from
> a·b = r + qΦ₀ it gives w₀(r) ≥ w₀(a·b) ≥ w₀(a) + β AND w₀(q) ≥ w₀(a·b) ≥
> w₀(a) + β, i.e. w₀(a′) − w₀(a) ≥ β for either digit. Hence
>
>     gain(r-digit) ≥ e₁[e₀β − (e₀−k)h₀],
>     gain(q-digit) ≥ e₁[e₀β − (e₀−k)h₀ + h₀],
>
> the q-digit's extra e₁h₀ coming from its Φ₀-exponent being one higher, NOT
> from any relation between w₀(q) and w₀(r). The r1 text's
> "gain(q-digit) = gain(r-digit) + e₁h₀" is STRICKEN: it is not an identity.
> The ultrametric only forces min(w₀(r), w₀(q)) = w₀(a·b), so the other digit
> may sit strictly higher.”

and the per-row instantiation that closes the column (lines 723–727):

> “Row 1:
> b = 1, but j′ = j+1 adds γ₂ and the Φ₀-drop costs e₁e₀h₀, net h₁ > 0. Rows
> 2–3: β = h₀, k = 0. Rows 4–5: β = h₀+1. Rows 6–7: β = amin(k) with
> e₀·amin(k) ≥ (e₀−k)h₀ + 1, forced by gcd(e₀, h₀) = 1 (e₀ | kh₀ ⟺ e₀ | k,
> impossible for 1 ≤ k < e₀). Every gain is ≥ 0 and the ONLY zero is row 2.”

**FORM:** italic-headed proof paragraph with two displays and an embedded dated strike.

**DERIVATION:** CONTENT applied to EACH digit separately (the r2 correction); the gcd argument for rows 6–7.

**CONDITIONALITY:** **CHAIN-C, three layers.** (1) The r1 identity is STRICKEN and stays stricken. (2) The r2 witness `a·b = 4x²+2` is NOT realizable as a branch product at d₀ = 2 and is REPLACED by [r3, F-B]'s legal-mid witness:

> “    a = x  (deg 1 < d₀)   and the mid   b₁ = 4x+2  (deg 1 < d₀,
>                                         w₀(b₁) = 1 = amin(1), so a LEGAL mid):
>     a·b₁ = 4x²+2x = 4·Φ₀ + (−2x−4),  i.e.  q = 4,  r = −2x−4,
>     w₀(a·b₁) = 1,   **w₀(q) = 2 > 1 = w₀(r) = w₀(a·b₁)**,”

(3) The equality is demoted to an OBSERVATION with an explicit non-consumption fence: “the equality did hold on all **896** r/q branch pairs of the committed battery (PE2 checked gain(q) − gain(r) == e₁h₀ pairwise, 0 exceptions) — an artifact of those instances' shapes, and no step below consumes it.” TERMINAL = the r2 strike + the r3 witness.

**RESOLUTION TRACE:** statement/derivation lines 673–687; correction sites 688–723 (F-B, with its exact-integer re-verification and the ℚ₂-square-root non-realizability argument); per-row instantiation 723–727.

**TEETH:** charge item **(7)** — the eight per-digit bounds. Disposition: `accepted-with-decorrelation-supplied` (PE2 re-derived all eight and found them “CORRECT and, against the battery's minimal (e₁, h₀, e₀), TIGHT”; PE3 and PE4 re-derived them again from scratch). ARITHMETIC AUDIT of the F-B witness, recomputed at compile time: 4x² + 2x = 4(x²+x+1) + (−2x−4) ✓; w₀ values 1 / 2 / 1 ✓; gain(q) − gain(r) = e₁[e₀·1 + h₀] = 3e₁ ≠ e₁h₀ = e₁ at (e₀,h₀) = (2,1) ✓. The non-realizability of 4x²+2: (αδ)² = −8 with v₂(−8) = 3 odd ✓.

---

### EFF.LIFTCORNER.43  [run-record]

**CANONICAL STATEMENT:**

> “**[r1 MACHINE LEG for (A)/(B) — the examples-first table.]**
> `verification/openmath/liftcorner_tailstab_children.py`, output committed as
> `liftcorner_tailstab_children_table.txt` (exit 0, ALL GREEN; independent of
> the sealed battery, which is byte-untouched). 29 towers spanning p ∈ {2,3,5},
> d₀ ∈ {1,2,3}, e₀ ∈ {2,3,4,5,6} (the e₀ = 2 boundary and e₀ ≥ 3 both), all
> four lift genres (pure = Φ″, dense = tail + mids, mids-only, tail-only), plus
> PE1's counter-instance verbatim as row CTR; 752 (a, m, j) probes; **2,668
> child rows**. Its §3 genre summary reports NINE normalized labels, which map
> onto the seven rows above exactly: `key` = 1, `b0-main-r/q` = 2/3,
> `b0-tail-r/q` = 4/5, `mid[k<e0-1]-r` and `mid[TOP=e0-1]-r` both = 6 (same
> bound m′ ≤ m−1), `mid[k<e0-1]-q` = 7a, `mid[TOP=e0-1]-q` = 7b. Observed lex
> deltas per label: `m-DROP` for all eight non-7b labels, `degA-DROP` for all
> 220 instances of 7b; **0 children dropping NEITHER coordinate**. Observed
> ω-gains per label agree with the table's bounds, with `b0-main-r` the unique
> label whose gain set is exactly {0}. The 220 m′ = m children are ALL of
> genre 7b, all with deg a′ < deg a, all at deg a ≥ 1, all at d₀ ≥ 2 (the (B)
> predictions), min gain +2.”

**FORM:** bold-headed bracketed record.

**DERIVATION:** `[RUN]`

**CONDITIONALITY:** the note fences the leg itself: “The table is evidence for the case split, not a substitute for (A)–(C): it is a finite battery, and the proof above is what carries the ∀.”

**RESOLUTION TRACE:** statement lines 729–752.

**TEETH:** RE-VERIFIED AT COMPILE TIME against the committed table: `total child rows: 2668` ✓; `mid[TOP=e0-1]-q     220  [('degA-DROP', 220)]` ✓ (all 220 degA-DROP, none m-DROP); `total m'=m children: 220; genres: ['mid[1]-q', 'mid[2]-q', 'mid[3]-q', 'mid[4]-q', 'mid[5]-q']; all with deg a' < deg a: True; all with deg a >= 1: True; all with d0 >= 2: True; min gain: 2` ✓ — every one of the four (B) predictions and the min-gain figure reproduce exactly. Disposition `run-record, verified`.

---

### EFF.LIFTCORNER.44  [instrument-record + run-record]

**CANONICAL STATEMENT:**

> “**[r2, G3 — the completeness leg made DURABLE: assertion A7.]** PE2's G3:
> A1–A6 cannot certify the census's COMPLETENESS, which is exactly charge item
> (1). A6 recomputes the double development of X *directly* and never calls
> `children()`, so an enumeration missing a whole branch would have left every
> assertion green — the prose and the script shared ONE transcription of the pass
> identity (the standing extraction-corruption trap: a second leg pinned to the
> first inherits its corruption). PE2 supplied the missing leg ad hoc
> (Σ children == X, 0 mismatches on 752 nodes); r2 puts it INSIDE the committed
> generator as **A7**, over the same 752 (a, m, j) probes A6 walks, with X built
> by direct multiplication from Φ₀ and Φ′ — not from the pass identity — so a
> missing or a spurious branch fails the check:
>
> * **A7(i) SUM IDENTITY** Σ_children a′Φ₀^{m′}Φ′^{j′} = X exactly — **0
>   mismatches over 752 nodes / 5,336 enumerated children**;
> * **A7(ii) SHAPE** deg a′ < d₀ and m′ ≥ 0 for every child (so every child is a
>   legal IH target) — 0 violations;
> * **A7(iii) DIGIT-WISE dev-linearity** — the slot-wise sum of the children's
>   double developments IS X's double development, i.e. the digits A6 walks are
>   exactly the digits the children generate — 0 mismatches; this machine-checks
>   (C)(i)'s additivity step ("polynomial devs carry no carries") at every probe;
> * **A7(iv) BRANCHING** ≤ 2e₀+3 (G1's corrected count) — 0 violations, observed
>   maximum per node exactly 2e₀+3 at e₀ = 2, 3, 4, 5, 6.”

together with the regeneration discipline:

> “Regeneration discipline: the r1 DATA sections (§§1–6 — roster, the 2,668 child
> rows, genre summary, the m′ = m stratum, LEDGER statistics, counter-instance
> tree) come back BYTE-IDENTICAL; the diff old → new is **7 pure INSERTIONS**
> (one provenance line in the header, six A7 verdict lines in §7) with **0
> deleted and 0 modified lines**”

**FORM:** bold-headed bracketed record with a bulleted display.

**DERIVATION:** the diagnosis is the standing **extraction-corruption trap** (a second leg pinned to the first inherits its corruption) — the note names it as such; A7's cure is to build X by direct multiplication rather than from the shared pass identity, i.e. to DECORRELATE the second leg.

**CONDITIONALITY:** the note's own honest limit, quoted at `.45`.

**RESOLUTION TRACE:** statement lines 754–783.

**TEETH:** RE-VERIFIED AT COMPILE TIME: the committed table's §7 reads `nodes reconciled: 752   children enumerated: 5336` ✓, and A6's line reads `probes: 752   all LEDGER-clean: True   digits inspected: 4438   min slack over all digits: 0` ✓ — both the 4,438-digit figure and the realized min slack 0 (the equality thread) reproduce. Disposition `run-record, verified` for A7(i)/(iv); `accepted-with-decorrelation-supplied` for the completeness leg as a whole.

---

### EFF.LIFTCORNER.45  [fence]

**CANONICAL STATEMENT:**

> “HONEST LIMIT: A7 is instance-level. It certifies that AT
> THESE 752 NODES the enumeration is exhaustive and non-spurious; the ∀ is
> carried by (A)'s algebra (Φ₀^{e₀} = Φ′ − Σ_{k<e₀}b_kΦ₀^k gives exactly the key
> + b₀ + (e₀−1) mid terms, and deg(a·b) ≤ 2d₀−2 forces exactly two digits per
> branch and forbids a redigit cascade — PE2 re-derived both independently), and
> A7 says nothing about the genre LABELS, only about the summands.”

**FORM:** bold-headed inline fence.

**DERIVATION:** `[RECORD]` of an evidence limit, with the ∀-carrying argument named.

**CONDITIONALITY:** this is the fence that keeps charge item (1) OPEN as a *proof* obligation despite a green machine leg. A consumer must not upgrade A7 to a proof of completeness.

**RESOLUTION TRACE:** statement lines 784–789.

**TEETH:** disposition `signed vacuity disclosure` is NOT the right label here (the leg does fire meaningfully); the correct label is **instance-level evidence, ∀ carried by algebra** — recorded in §6 as a PROOF-ONLY row with this sentence quoted.

---

### EFF.LIFTCORNER.46  [derivation]

**CANONICAL STATEMENT:**

> “**(B) The deg a = 0 stratum (the second coordinate's base) and the d₀ = 1
> corner.** At deg a = 0 row 7b is EMPTY: deg(a b_{e₀−1}) ≤ 0 + (d₀−1) < d₀,
> so its q-digit vanishes and the top-mid branch contributes only its r-child.
> Hence at deg a = 0 EVERY child drops m, and the lex induction needs no
> separate base for the second coordinate — it bottoms out on the m < e₀ base
> alone. Two consequences worth recording: (i) at most deg a ≤ d₀−1
> consecutive m-preserving steps can occur from any node, so the recursion is
> equally a single induction on m with an inner chain of length < d₀; (ii) at
> d₀ = 1 NO branch ever produces a q-digit (deg(a·b) ≤ 0 < 1 = d₀), so the r0
> single-m induction was in fact valid on the whole flat corner d₀ = 1 — which
> is why no d₀ = 1 row could have exposed the defect, and why the
> counter-instance below is at d₀ = 2.”

**FORM:** bold-headed proof paragraph.

**DERIVATION:** degree counts.

**CONDITIONALITY:** **[r2, G5] STRIKES the r1 characterization**, quoted in full:

> “**[r2, G5 — "exactly" STRICKEN.]** The r1
> wording "valid EXACTLY on the flat corner d₀ = 1" claimed a
> characterization and is false: d₀ = 1 is SUFFICIENT, not necessary. The r0
> clause "every child has m′ ≤ m−1" also holds VACUOUSLY at any node with no
> m-preserving child — in particular on any orbit member whose top mid
> b_{e₀−1} vanishes, since row 7b is then absent for every a. Such instances
> exist at d₀ ≥ 2 in the note's own committed table: `A12` (ℤ₂, d₀ = 2, e₀ = 2,
> genre `pure`) and `B14` (ℤ₂, d₀ = 2, e₀ = 5, genre `pure`) have all mids zero
> and contribute NO row to the table's §4 m′ = m stratum.”

SUPERSESSION KIND: **replacement** (a false characterization by a true sufficiency claim). The consumed consequence is unaffected: “d₀ = 1 rows cannot exhibit the defect, so the counter-instance has to sit at d₀ ≥ 2.”

**RESOLUTION TRACE:** statement lines 791–801; correction site 802–812.

**TEETH:** PE2 proved “both emptiness strata … PROVED not merely measured”; the A12/B14 witnesses are rows of the committed table.

---

### EFF.LIFTCORNER.47  [derivation]

**CANONICAL STATEMENT:**

> “**(C) The two consumers, re-closed on the lex order.** (i) *The induction.*
> The IH is invoked only on the children of one pass; each is strictly lex-below
> its parent by (A), so the appeal is legitimate. With the gains of (A) every
> child satisfies (LEDGER) at its own ω(child) ≥ ω(X); dev-linearity (the
> double dev of X is the digit-wise sum of the children's — polynomial devs
> carry no carries) plus the ultrametric close then gives (LEDGER) for X.”

**FORM:** bold-headed proof paragraph, clause (i).

**DERIVATION:** the lex descent of `.39`–`.41` plus dev-linearity plus the ultrametric.

**CONDITIONALITY:** dev-linearity's additivity step is machine-checked at every probe by A7(iii) but is not proved beyond “polynomial devs carry no carries”; PE1 re-verified it.

**RESOLUTION TRACE:** proof lines 814–819.

**TEETH:** A7(iii) (`.44`); charge item (2).

---

### EFF.LIFTCORNER.48  [derivation]

**CANONICAL STATEMENT:**

> “(ii) *Termination/finiteness* (the job the false clause was doing). The
> recursion tree is FINITELY BRANCHING, and by (A) has no infinite path, hence
> is FINITE (König), so the dev-linearity sum is finite.”

with the corrected branching count, verbatim:

> “**[r2, G1 — the count
> CORRECTED; the r1 number was false.]** The r1 text said "≤ 2e₀+1 children per
> node (row 1, rows 2–5, and ≤ e₀−1 realizations each of rows 6 and 7)"; its own
> parenthetical sums to 1 + 4 + (e₀−1) + (e₀−1) = **2e₀+3**, and the note's own
> committed table exhibits 7 children at e₀ = 2 (row `A1`, a = x+1, m = 2), which
> already refutes "≤ 5". The correct bound is
>
>     #children(node) ≤ 2e₀+3
>       = 1 (row 1) + 4 (rows 2–5, counted per DIGIT: b₀-main r and q,
>                        b₀-tail r and q)
>         + (e₀−1) (row 6) + (e₀−1) (rows 7a+7b),”

and the depth bound:

> “Explicit
> depth bound: ρ(m, deg a) := m·d₀ + max(deg a, 0) strictly drops along every
> child edge (an m-drop of ≥ 1 costs ≥ d₀ and can restore at most d₀−1 in the
> second coordinate; an m-preserving step drops the second coordinate by ≥ 1),
> so every root-to-leaf path has length ≤ m·d₀ + d₀ − 1. The r0 bound
> ⌈m/e₀⌉ survives in its correct scope: it bounds the ω-EQUALITY thread, whose
> only genre is row 2 (gain 0), which drops m by exactly e₀ per step. ∎”

**FORM:** italic-headed proof clause with an embedded dated strike and a display.

**DERIVATION:** König's lemma over a finitely-branching tree with no infinite path; the ρ function's strict drop is proved by the two displayed cases.

**CONDITIONALITY:** the note fences what is consumed: “**ONLY FINITENESS of this count is consumed** — by the König step in the previous sentence and by the finiteness of (i)'s dev-linearity sum; 2e₀+3 is finite, so both go through unchanged, and no step anywhere uses the count's VALUE. The quantitative claim that does matter is the ρ depth bound next, which is independent of the branching count.” SUPERSESSION KIND: **replacement** (a false bound by a true one) with a scope disclosure attached.

**RESOLUTION TRACE:** proof lines 820–849; correction site 822–843.

**TEETH:** A7(iv) asserts ≤ 2e₀+3 per node with observed maximum exactly 2e₀+3 at e₀ = 2,3,4,5,6 (`.44`). ARITHMETIC AUDIT: 1 + 4 + (e₀−1) + (e₀−1) = 2e₀ + 3 ✓; at e₀ = 2,3,4,5,6 this is 7, 9, 11, 13, 15 — exactly the note's observed maxima. Charge item (2).

---

### EFF.LIFTCORNER.49  [scope record]

**CANONICAL STATEMENT:**

> “[This IS the shift-descent bookkeeping: one key up costs h₁, exactly the
> χ-chain's descent step (GRTW2 §3.4 rem. 1); the window-calculus ledger ω is
> the tail-weight bookkeeping ILNRES S5.1 priced. Machine mirror: Q3/Q4 — the
> tail never reaches the read.]”

**FORM:** bracketed inline remark.

**DERIVATION:** `[RECORD]` — an identification of this note's ω with two external objects (the χ-chain descent step; the priced tail-weight bookkeeping).

**CONDITIONALITY:** this is a *route* claim, not a theorem: it says the proof realizes the priced route, not that it derives anything from GRTW2 §3.4. The unit's W-2 consumption proper is `.19`/`.61`/`.72`.

**RESOLUTION TRACE:** statement lines 851–854.

**TEETH:** XREF X09 (GRTW2 §3.4, count 1) and X01 (ILNRES S5.1, count 1) both verified.

---

### EFF.LIFTCORNER.50  [changes-record]

**CANONICAL STATEMENT:**

> “**[r1, F1 — CRITICAL (PE1): what changed, and what did not.]** The r0 proof
> asserted "Every child is again of the lemma's shape with m′ ≤ m−1 (strict
> descent; termination)" and closed "The ONLY 0-gain branch is b₀-main's
> r-digit, which also strictly drops m: the ω(X)-thread terminates in
> ≤ ⌈m/e₀⌉ passes." The first clause is FALSE at row 7b (m′ = m), so the
> strong induction on m alone had no IH at that child and the finiteness claim
> rode the same clause; PE1 graded this CRITICAL and the ledger dropped
> (TAIL-STAB) to PROVED-MODULO-F1. The LEMMA STATEMENT is byte-unchanged. NEW
> at r1: the lex order, the seven-genre census with its per-genre descent
> column, the (B) deg a = 0 / d₀ = 1 analysis, and the (C)(ii) finiteness with
> an explicit depth bound. UNCHANGED in content and re-verified by PE1
> independently: the base case, the one-pass identity, all ω-gains (now
> displayed per digit, hence sharper on rows 3, 5, 7 than r0's per-branch
> lower bounds), the gain-0 census (row 2 only), CONTENT, dev-linearity, the
> (LEDGER) ⟹ w₂(X) ≥ ω(X) tie and the read-kill close, and the ⌈m/e₀⌉
> equality-thread bound in its correct scope.”

**FORM:** bold-headed bracketed changes-record.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** **the “UNCHANGED … re-verified by PE1” list is itself corrected at r2/G2** (`.51`): the ω-gain clause inside it is self-refuting. The r0 wording is quoted here (resolution rule 7) because the lex repair is unintelligible without the clause it replaces; it is DEAD text.

**RESOLUTION TRACE:** statement lines 856–871; correction site 873–902.

**TEETH:** `AUDIT / in-house hostile pass` — PE1 produced the arc's only CRITICAL.

---

### EFF.LIFTCORNER.51  [changes-record]

**CANONICAL STATEMENT:**

> “**[r2, G2 — that attribution is CORRECTED; it was self-refuting.]** The
> sentence above put "all ω-gains (now displayed per digit, hence sharper on rows
> 3, 5, 7 than r0's per-branch lower bounds)" inside the list of things
> "UNCHANGED in content and re-verified by PE1 independently" — but bounds that
> are NEW and SHARPER at r1 are by construction not unchanged, and PE1, which
> read the r0 table, cannot have verified them. The honest split:
>
> * **What PE1 re-verified** (verbatim scope, from its F1 repair observation:
>   "all four ω-gain rows of the branch table (checked, using
>   e₀·amin(k) ≥ (e₀−k)h₀+1 which I re-derived from gcd(e₀,h₀) = 1 …)"): r0's
>   **four PER-BRANCH** ω-gain rows, plus the base case, the one-pass identity,
>   the gain-0 census (row 2 only), CONTENT, dev-linearity, the
>   (LEDGER) ⟹ w₂(X) ≥ ω(X) tie and read-kill close, and the ⌈m/e₀⌉ bound in
>   its correct scope.
> * **What PE1 never saw**: the r1 table's **eight PER-DIGIT** gain entries
>   (rows 1, 2, 3, 4, 5, 6, 7a, 7b). Rows 3, 5, 7a, 7b are new at r1.
> * **Who first hostile-read them**: **PE2** … which
>   re-derived ALL EIGHT independently — row 1 = exactly +h₁; row 2 =
>   e₁e₀[w₀(r) − w₀(a) − h₀] ≥ 0; row 3 ≥ e₁h₀; row 4 ≥ e₁e₀; row 5 ≥ e₁e₀+e₁h₀;
>   row 6 ≥ e₁; rows 7a/7b ≥ e₁(h₀+1), with e₀·amin(k) ≥ (e₀−k)h₀+1 re-derived
>   from gcd(e₀,h₀) = 1 — and found them CORRECT and, against the battery's
>   minimal (e₁, h₀, e₀), TIGHT.”

with the meta-finding and its cure:

> “The r1 charge list also pointed away from these bounds (its items (1)–(6) name
> neither) — the same defect PE1 recorded against r0's charge list, recurring one
> round later on a different step. r2 adds charge item **(7)** for them (grade
> box). Their audit status after r2, stated plainly: displayed at r1, re-derived
> ONCE by a hostile pass (PE2), and now named in the charge list — one
> independent re-derivation, no acceptance credit, PE3 owed.”

**FORM:** bold-headed bracketed correction with a bulleted split.

**DERIVATION:** an attribution audit: what a pass READ bounds what it can have VERIFIED.

**CONDITIONALITY:** SUPERSESSION KIND: **provenance-rider** (it moves credit, not content). The audit-status sentence is superseded by later rounds' counts (three passes by r4); the FINAL in-range status is `.68`/`.70`.

**RESOLUTION TRACE:** statement lines 873–902.

**TEETH:** `AUDIT / in-house hostile pass`, plus a structural lesson the note draws itself: a charge list that names neither the step that broke nor the new argument is a recurring defect genre. Charge item (7) is the cure.

---

### EFF.LIFTCORNER.52  [derivation]

**CANONICAL STATEMENT:**

> “**[r1, F1 — the counter-instance's own descent chain, numerically.]** PE1's
> instance: O = ℤ₂, d₀ = 2, e₀ = 2, h₀ = 1, Φ₀ = x²+x+1, b₀ = 2 (so ĉ′ = 1,
> t₀ = 0, c′ = 1), b₁ = 2x (w₀ = 1 = amin(1)); Φ′ = Φ₀² + b₁Φ₀ + b₀ =
> x⁴+4x³+5x²+4x+3. Take e₁ = h₁ = 1, so γ₂ = e₁e₀h₀+h₁ = 3 and
> ω(aΦ₀^mΦ′^j) = 2w₀(a) + m + 3j. Root X = xΦ₀^2, i.e. (m, deg a) = (2, 1),
> ω(X) = 2. One pass, its four nonzero branches (mid digits from
> 2x² = 2Φ₀ − 2x − 2, i.e. r = −2x−2, q = 2, negated by the identity's sign):
>
>     key        → a′ = x      (m′,j′) = (0,1)  ω = 3  gain +1 = h₁        [m-DROP]
>     b₀-main r  → a′ = −2x              (0,0)  ω = 2  gain  0            [m-DROP]
>     mid[1] r   → a′ = 2x+2             (1,0)  ω = 3  gain +1 = e₁       [m-DROP]
>     mid[1] q   → a′ = −2               (2,0)  ω = 4  gain +2 = e₁(h₀+1)
>                                      [m′ = m = 2, deg a′ = 0 < 1 = deg a: row 7b]
>
> The r0 induction stops dead at the fourth child. Under the lex order that
> child, (m, deg a) = (2, 0), is expanded once more:
>
>     key        → a′ = −2              (0,1)  ω = 5  gain +1             [m-DROP]
>     b₀-main r  → a′ = 4               (0,0)  ω = 4  gain  0            [m-DROP]
>     mid[1] r   → a′ = 4x              (1,0)  ω = 5  gain +1            [m-DROP]
>
> — and NO mid q-child, exactly as (B) predicts at deg a = 0 (a·b₁ = −4x has
> degree 1 < 2 = d₀). All six leaves sit at m ≤ 1 < e₀ = 2, i.e. on the base
> case: the tree is 8 nodes, depth 2, well inside the (C)(ii) bound
> m·d₀ + d₀ − 1 = 5.”

**FORM:** bracketed display (two ASCII child tables).

**DERIVATION:** direct computation on PE1's instance; “(This whole chain is machine-printed in §6 of the r1 table, digit for digit.)”

**CONDITIONALITY:** an instance, not a proof — it exhibits the defect and the repair, and confirms (B)'s prediction at deg a = 0.

**RESOLUTION TRACE:** statement lines 904–929.

**TEETH:** ARITHMETIC AUDIT, recomputed: Φ′ = (x²+x+1)² + 2x(x²+x+1) + 2 = x⁴+2x³+3x²+2x+1 + 2x³+2x²+2x + 2 = x⁴+4x³+5x²+4x+3 ✓. ω(X) = 2·0 + 2 + 0 = 2 ✓. Tree size 4 + 3 + root = 8 nodes ✓; depth bound m·d₀ + d₀ − 1 = 2·2 + 1 = 5 ✓. Machine mirror: the committed table's §6 counter-instance tree (row CTR).

---

### EFF.LIFTCORNER.53  [derivation]

**CANONICAL STATEMENT:**

> “Independent tie (not via the recursion): the honest double
> development of the root is
>
>     xΦ₀² = (x−2)·Φ′ + (6x+2)·Φ₀ + (−2x+4),
>
> digits at (j,i) = (1,0), (0,1), (0,0) with weights 3, 3, 2 against
> ω(X) = 2 — (LEDGER) holds, slacks 1, 1, 0, and the equality thread is the
> (0,0) digit, precisely row 2's gain-0 thread.”

**FORM:** display with an inline reading.

**DERIVATION:** a direct double development, computed without the recursion — a DECORRELATED check of the same instance.

**CONDITIONALITY:** none; it is an exact identity over ℤ₂.

**RESOLUTION TRACE:** statement lines 929–936.

**TEETH:** ARITHMETIC AUDIT, recomputed at compile time: (x−2)(x⁴+4x³+5x²+4x+3) = x⁵+4x⁴+5x³+4x²+3x − 2x⁴−8x³−10x²−8x−6 = x⁵+2x⁴−3x³−6x²−5x−6; (6x+2)Φ₀ = 6x³+6x²+6x + 2x²+2x+2 = 6x³+8x²+8x+2; sum with (−2x+4) gives x⁵+2x⁴+3x³+2x²+x = x(x⁴+2x³+3x²+2x+1) = x(x²+x+1)² = xΦ₀² ✓. Weights: w₀(x−2) = 0 so the Φ′-digit sits at ω = 2·0+0+3·1 = 3 ✓; w₀(6x+2) = 1 at i = 1 gives 2·1+1 = 3 ✓; w₀(−2x+4) = 1 at i = 0 gives 2 ✓. Slacks 1, 1, 0 ✓. This is the strongest single verification in the shard: an exact polynomial identity, re-derived independently of both the note and its machine legs.

---
### EFF.LIFTCORNER.54  [lemma]

**CANONICAL STATEMENT:**

> “Every 2-read battery object (anchors φ_γ = π^{u₁}Φ₀^{s₁}K^{s₂}; pair
> products φ_γφ_{γ′}; K = the tower's own key) has IDENTICAL level-2 reads
> (weight, grid, every slot coefficient) on the Φ′- and Φ″-towers.”

**FORM:** display lemma under the heading “**LEMMA (READ-EQ) — the Φ′-tower reads = the Φ″-tower reads**”.

**DERIVATION:** `.55` (case (a)) + `.56` (case (b)), on the shared-read-datum observation: “The towers share every read datum (reads, ψ₁, K₂, and the LETTER z₁′ = −c′ in ε₁) — only key bytes differ.”

**CONDITIONALITY:** the shared-datum sentence is a statement about the two TOWERS OF THE PROOF, proved from the S4 setting, not an appeal to any runner assert — `.26` establishes exactly this.

**RESOLUTION TRACE:** statement lines 940–942; heading 938; proof 942–958.

**TEETH:** charge item (4) (“the READ-EQ on-line-content/ultrametric close”); PE4 re-derived READ-EQ digit by digit on both towers; PE3 found that “READ-EQ's one pass sits entirely in the deg a = 0 stratum, where the repaired proof shows there are no q-children at all, so the r0 defect could never have propagated there”.

---

### EFF.LIFTCORNER.55  [derivation]

**CANONICAL STATEMENT (frozen text):**

> “(a) Anchors and δ₁ = 0 products are
> π^uΦ₀^sK^S with s < e₀ < deg: single K-slot coefficient π^uΦ₀^s — identical
> bytes, the key power never opened (any δ₂-carry is grid bookkeeping, no
> reduction at the top level of a 2-read).”

**CANONICAL STATEMENT (EFFECTIVE):** superseded out of range by **AC-3** (lines 1560–1573). The clause “with \(s<e_0<\deg\)” is replaced by:

> “with \(s<e_0\); since \(\deg\Phi_0=d_0\) and
> \(\deg\Phi'=\deg\Phi''=e_0d_0\),
> \[
> \deg(\Phi_0^s)=sd_0<e_0d_0=\deg\Phi'=\deg\Phi'',
> \]
> so \(\pi^u\Phi_0^s\) is a single key-slot coefficient and the key power is never opened.”

**FORM:** inline proof clause (frozen); replacement is a display.

**DERIVATION (effective):** the degree comparison is between `deg(Φ₀^s) = s·d₀` and `deg Φ′ = e₀d₀`, not between the integer `e₀` and a degree. The frozen form fails literally at d₀ = 1, where deg Φ′ = e₀ and “e₀ < deg” is false.

**CONDITIONALITY:** SUPERSESSION KIND: **replacement**. AC-3's consumer sweep: “This is exactly the inequality consumed by the anchor and \(\delta_1=0\) parts of READ-EQ. It holds also at \(d_0=1\), where \(\deg\Phi'=e_0\) but \(s<e_0\). The separate \(\delta_1=1\) one-overflow argument is untouched. Therefore READ-EQ, the THEOREM, COR 1 and COR 2 survive unchanged.” **TARGETS:** `55` only.

**RESOLUTION TRACE:** statement line 945; correction site 1554–1573 (shard 2, finding 4 REAL + AC-3).

**TEETH:** `AUDIT / decorrelated-model audit`. Note the pattern: BOTH certifier-found REAL defects in this shard (`.34`, `.55`) are *scope-of-display* errors in one-line statements that four in-house hostile passes read without firing — the note's teeth are aimed at the arguments, and its displays were the soft target.

---

### EFF.LIFTCORNER.56  [derivation]

**CANONICAL STATEMENT:**

> “(b) δ₁ = 1 products (g₀ = 1 ⟹
> s₁+s₁′ ≤ 2e₀−2: EXACTLY one overflow): P = π^UΦ₀^{e₀+S₁″}K^{S₂},
> ω(P) = Γ := γ+γ′ (the split identity γ = e₁(e₀u₁+s₁h₀) + s₂γ₂). One pass on
> each tower; compare children. Key child π^UΦ₀^{S₁″}K^{S₂+1}: identical
> bytes, ledger Γ+h₁ — strictly above on BOTH towers (reads 0 both; it is the
> E₁ digit). b₀-main children: −π^{U+h₀}ĉ′Φ₀^{S₁″}K^{S₂} vs
> −π^{U+h₀}lift(c′)Φ₀^{S₁″}K^{S₂}: single digits; their difference has
> w₀(ĉ′−lift(c′)) ≥ 1 (both lift c′), ledger ≥ Γ + e₁e₀. Φ′-only children
> (t₀, mids): ledger ≥ Γ+1, and by TAIL-STAB every digit they generate stays
> > Γ. So the on-Γ-line digit content coincides; all deviations are strict
> π-excess at their slots; res kills them and the ultrametric keeps w₂ = Γ and
> the on-line status equal on both sides. Reads agree slot-by-slot. ∎”

**FORM:** inline proof clause with an embedded ∎.

**DERIVATION:** one pass of the orbit identity on each tower, then a child-by-child comparison; the only non-elementary input is (TAIL-STAB) (`.36`), applied to the Φ′-only children.

**CONDITIONALITY:** untouched by AC-3 (“The separate \(\delta_1=1\) one-overflow argument is untouched”). The “EXACTLY one overflow” count uses g₀ = 1.

**RESOLUTION TRACE:** proof lines 946–958.

**TEETH:** charge item (4). Machine mirror Q4 PV (`.29`, 4,176/0).

---

### EFF.LIFTCORNER.57  [theorem]

**CANONICAL STATEMENT:**

> “**THEOREM.** For EVERY orbit member Φ′ (any residue c′ ≠ 0), the 2-read
> ITER-LAW display holds on the Φ′-tower with the letter the lift carries:
> c^{Φ′}(γ,γ′) = z̄^{δ₂}·(z₁′)^{D₁}, z₁′ = −c′, all γ,γ′ ∈ W₂. *Proof.* READ-EQ
> transports every anchor value, pair value and cocycle to the Φ″-tower; Φ″ is
> a STANDARD-LIFT instance of the accepted class with ψ₀ ↦ ψ₀^{(ξ)} (same
> (e,h,g) data, ψ₀^{(ξ)}(0) = c′ ≠ 0), where the ACCEPTED ITER-LAW gives the
> display with its letter z₁′. ∎ [Machine: Q3 4,176/0.]”

**FORM:** bold-headed theorem with inline proof.

**DERIVATION:** READ-EQ (`.54`) + the ACCEPTED ITER-LAW applied to the standard lift Φ″. This is the note's central compose: a reduction of the orbit case to the accepted standard-lift case.

**CONDITIONALITY:** rides the accepted [IL] ITER-LAW at its own scope; the display is 2-read only (the FENCES bar any orders-≥3 claim, `.17`).

**RESOLUTION TRACE:** statement lines 962–968. The cocycle symbol `c^{Φ′}` is the post-F4-5 name (`.58`).

**TEETH:** Q3 TLAW 4,176/0 (`.29`); accepted at 2/2 (shard 2). PE4 verified “the THEOREM + COR 2 exactly on a concrete ℤ₂/𝔽₄ orbit member”.

---

### EFF.LIFTCORNER.58  [changes-record]  *(CHAIN-D, link 1)*

**CANONICAL STATEMENT:**

> “**[r4, F4-5 — NOTATION, one line, fixing a `c′` collision inside the unit's
> headline identity; a pure renaming, no content changes.]** From here on
> **`c^{Φ′}(γ,γ′)`** denotes the 2-read COCYCLE on the Φ′-tower and `c_base(γ,γ′)`
> the cocycle on the base standard tower, while **`c′` (no arguments) stays the
> RESIDUE SCALAR** `res(b₀/π^{h₀}) ∈ K₀` of S1. The r1–r3 text wrote the same
> cocycle two ways — `c(γ,γ′)` in the THEOREM and `c′(γ,γ′)` in COR 2 — and the
> second collides with the scalar inside COR 2's own display (`ξ := c₀/c′`); both
> are renamed to `c^{Φ′}` here, and they were always the same function (PE3
> recorded the collision, PE4 numbered it F4-5).”

**FORM:** bold-headed bracketed notation rider.

**DERIVATION:** `[DEFINITIONAL]` — a renaming, explicitly content-free.

**CONDITIONALITY:** SUPERSESSION KIND: **wording-rider**, with a **license** attached for the three sealed sites it cannot edit (S1's CANDIDATE display, S2's Q7 row, S2's Q9 row). **TARGETS:** `20` (the CANDIDATE display, ×2 occurrences), `22` (Q7 row, Q9 row), `61` (COR 2).

**RESOLUTION TRACE:** statement lines 970–982; the Q7 extension at 269–271 (F5-3); the Q9 extension at 293–297 (F6-2).

**TEETH:** the census warrant is `.59`.

---

### EFF.LIFTCORNER.59  [changes-record]  *(CHAIN-D — TERMINAL)*

**CANONICAL STATEMENT:**

> “with Q9 the
> census is COMPLETE — warrant of record at OCCURRENCE level **[r7, F7-1]**:
> PE7's independent re-execution (report `LIFTCORNER_passPE7_report.md`, commit
> 58f7060) counts, at its HEAD 91f0cde, **51 `c′` occurrences on 47 lines =
> 34 residue-scalar + 4 covered-cocycle (S1's CANDIDATE display ×2, S2's Q7
> row, S2's Q9 row — all inside this correction of record) + 13
> mention/quotation — NO fourth bare-`c′`-as-cocycle site**; at PE6's HEAD
> 46e6e88 the same sweep gives 46 occurrences on 42 lines (four lines carry
> two, all scalar pairs) — PE6's "42" was its hit-LINE count, and the four
> uncounted occurrences are scalar second occurrences on already-classified
> lines, so no site was lost.”

**FORM:** bracketed rider embedded in the F4-5 bracket.

**DERIVATION:** an occurrence-level re-execution of the sweep at a named commit, replacing a hit-line count quoted at a different commit.

**CONDITIONALITY:** SUPERSESSION KIND: **counter re-reading** — the conclusion (no fourth site) is unchanged; the UNIT and the COMMIT of the warrant change. **The warrant is commit-pinned and the note is no longer at that commit.**

**RESOLUTION TRACE:** statement lines 983–992; the twin clause in the r6 round record at 298–303.

**TEETH:** ARITHMETIC AUDIT (v3 rule 22), recomputed AT HEAD (blob `d93c2aa2…`, commit `33225dd9`) rather than at either pinned commit: `grep -o "c′" | wc -l` = **54** occurrences on **50** lines. Both figures exceed PE7's 51/47 by exactly 3/3. That is EXPECTED and not a defect: the note grew after 91f0cde (the four 2026-08-12 certifier appends are ~480 lines of new text, and AC-5 uses `c'` in its “For an arbitrary residue \(c'\)” consumer-sweep bullet). The partition PE7 reports (34 + 4 + 13 = 51 ✓) is internally consistent, and the two commit pins verify (`git cat-file -t 91f0cde` = commit; `git cat-file -t 46e6e88` = commit); PE6's 46/42 also self-consistently exceeds 42 by the four doubled lines it names. **Disposition: `stale self-description`** — the census is TRUE as of 91f0cde and is not a HEAD statement; the three new occurrences at HEAD are unclassified by any warrant in the note. Recorded as OPEN-CALL 6, not as an error, because the note itself installed the rule that makes the staleness legible (“quote counts only WITH THEIR UNIT AND COMMIT”, `.15`) — and this compilation is applying that rule to the note's own figure.

---

### EFF.LIFTCORNER.60  [corollary]

**CANONICAL STATEMENT:**

> “**COR 1 ((ITER-LAW-LIFT), the corner).** ξ = 1 slice (c′ = c₀): the display
> holds UNCHANGED for every LAWFUL monic lift — the 2-read (ITER-LAW-LIFT) is
> proved at g₀ = 1 ∧ δ₁ = 1, exactly where it was open (ITERLAW S7: only
> PAIR-VAL Case II consumes Φ₁'s form; all other strata lift-form-free).
> [Machine: Q10 + wave-18's 104,404/0.]”

**FORM:** bold-headed corollary.

**DERIVATION:** the THEOREM (`.57`) at ξ = 1.

**CONDITIONALITY:** **this is the W-2-FREE core.** The grade box states it as a decoupling fact: “the COR 1 chain (TAIL-STAB + READ-EQ + accepted ITER-LAW) is W-2-free — if W-2's arc lags, the ξ = 1 discharge stands on this note's own arc alone.” Its coverage is complete on the corner because δ₁ = 1 is empty at e₀ = 1 (`.32`).

**RESOLUTION TRACE:** statement lines 994–998.

**TEETH:** Q10 XI1 (`.29`, no independent counter — see that unit's UNPINNED note) plus wave-18's 104,404/0 (XREF X04, verified at count 3 in the source).

---

### EFF.LIFTCORNER.61  [corollary]

**CANONICAL STATEMENT:**

> “**COR 2 (the χ-covariance; RESCOPED at r1).** Across the HARNESS monic-lift
> orbit of S1 the 2-read display transports by the letter alone: for every
> orbit member Φ′ with residue scalar c′ and ξ := c₀/c′,
>
>     c_base(γ,γ′) = c^{Φ′}(γ,γ′)·ξ^{D₁}   for all γ, γ′ ∈ W₂.
>
> *Proof.* The THEOREM applied on the Φ′-tower and on the base tower, plus
> z₁ = ξ·z₁′ (S1) and the lift-independence of D₁ (S1/S2). ∎ This is the
> corner-degenerate FORM that W-2 clause 3's value-layer transport predicts,
> and (with Q9's sharpness) evidence that it is the true covariance there.
> Nothing beyond the displayed identity on the harness orbit is claimed.
> [Machine: Q7 4,176/0 measured-vs-measured; Q9 sharpness 1,576 fires exact.]”

**FORM:** bold-headed corollary with a display and an inline proof.

**DERIVATION:** two applications of the THEOREM plus the letter relation and D₁'s lift-independence.

**CONDITIONALITY:** RESCOPED at r1 — the fence “Nothing beyond the displayed identity on the harness orbit is claimed” is the rescoping, and `.62` records what was withdrawn and what remains owed. AC-5's consumer sweep leaves it untouched: “COR 2’s already fenced \(\chi\)-covariance statement is unchanged.”

**RESOLUTION TRACE:** statement lines 1000–1011; rescoping record 1013–1032.

**TEETH:** Q7 CHI 4,176/0 measured-against-measured (the strongest instrument shape in the sheet — no closed form in the comparison) and Q9's exact set equivalence with 1,576 fires, which the note reads as sharpness: “the wrong-letter form fails exactly where ξ^{D₁} ≠ 1 — the transport is sharp, not slack”.

---

### EFF.LIFTCORNER.62  [changes-record]

**CANONICAL STATEMENT:**

> “**[r1, F3 — WITHDRAWN identification + what is still owed for the W2-OPEN-1
> tie.]** The r0 text said this corollary "is W-2 clause 3's value-layer
> statement (W2-OPEN-1) RESTRICTED to the base junction at the corner — now
> PROVED at this note's grade there, upgraded from instance-confirmed". That
> identification is WITHDRAWN as underived (PE1 F3): no equivalence between
> COR 2 and any slice of W2-OPEN-1 is derived anywhere in this note.
> W2-OPEN-1 as recorded (GRTW2 §5.3) quantifies over the committed
> value/cocycle battery — K5/K6/K7, K12 = π-shift/ρ-monodromy, K1–K4/K13
> riding — WITH THE TRANSPORTED CLASSIFIER LIFTS substituted for the harness
> lifts. Two things are therefore owed before even the base-junction slice of
> that statement may be claimed, and NEITHER is in this note: **(a) an
> orbit-membership display** — that the transported CLASSIFIER key at the base
> junction is an S1 orbit member (monic, degree e₀d₀, w₁ = e₀h₀, nonzero
> order-1 residual y + c′), which needs the GMN key-polynomial normalization
> plus W2-C3(ii), not merely the harness parametrization this note uses;
> **(b) the battery legs outside the display/anchor families** — K12 above
> all — under the restriction. Until both are displayed, COR 2 is a statement
> about the harness monic-lift orbit only.”

**FORM:** bold-headed bracketed withdrawal with a labelled (a)/(b) obligation pair.

**DERIVATION:** `[RECORD]` of an underived identification, with the missing derivation itemized.

**CONDITIONALITY:** **(a) and (b) are STILL OWED at HEAD.** Nothing in the acceptance record, FC-1, FC-2 or AC-1…AC-5 discharges either; AC-5 explicitly leaves COR 2 unchanged. The grade-cap consequence is stated in the same bracket: “The unit's W-2 grade cap (grade box) is unaffected: it was and remains driven by S1's and this corollary's consumption of clause 3's FRAMING.”

**RESOLUTION TRACE:** statement lines 1013–1032; the surviving obligation confirmed against 1253 (shard 2 CONDITIONALITY line) and against AC-5's sweep at 2061–2066.

**TEETH:** XREF X10 verifies GRTW2 §5.3's heading at count 1; X11 verifies the `W2-OPEN-1` designation at count 5 in GRTW2, including its ledger row “| W2-OPEN-1 | clause 3 value layer (battery on transported lifts) | **OPEN**, instance-confirmed 684 groups / 0 |”. Charge item (6).

---

### EFF.LIFTCORNER.63  [proposition]  *(CHAIN-P, link 1 — SUPERSEDED; TERMINAL is AC-5)*

**CANONICAL STATEMENT (frozen text):**

> “**PROP (propagation to every level — the S0.1 rider leg).** (ITER-LAW-n)
> for every lawful monic Φ₁ at the corner, all n: the [ILN] chain consumes
> Φ₁'s explicit bytes only through (i) monicity/degree/w₁Φ₁ = e₀g₀h₀ (shared
> by every orbit member) and (ii) the level-1 base package (= [IL], replaced
> here by COR 1; at n = 1 clause (ii) is ITERLAW S7's own display). Riding
> S0.1's verbatim propagation, the discharge lifts to every rung AT [ILN]'s
> OWN conditionality (T-class/(RM-m)/DCX ledger unchanged). VERIFY-TARGET for
> the arc: the clause-(ii) census at rungs ≥ 2 (no rung leg opens Φ₁'s bytes
> outside the level-1 package) is NOT re-proved here.”

**FORM:** bold-headed proposition.

**DERIVATION:** `[CONDITIONAL]` — the propagation rides ITERLAWN S0.1's verbatim rider; the clause-(ii) census is explicitly NOT proved here and is named a VERIFY-TARGET.

**CONDITIONALITY — CHAIN-P, four layers, TERMINAL = AC-5 (see §1):**
1. **Frozen text** (above): all-rung, at [ILN]'s conditionality, census owed.
2. **AC-1 (2026-08-12)** SUSPENDS it: “The all-rung force of three earlier sentences is SUSPENDED: PROP’s “the discharge lifts to every rung”, S5’s “ITER-LAW-\(n\) holds for EVERY lawful monic \(\Phi_1\), every \(n\)”, and FC-2’s execution of that rider rewrite.” The missing lemma is named (Φ₁-OPACITY) and a 57-pair pre-proof numerical certificate is specified.
3. **AC-4 (2026-08-12)** NARROWS it: the constructor/telescope subgraph is PROVED Φ₁-opaque (the Θ-transport sublemma), and “AC-1 is narrowed but not discharged: its alleged opacity problem is absent from the constructor/telescope subgraph and survives exactly at the rung-2 \(RM\)-1 reduction interface.”
4. **AC-5 (2026-08-12) — TERMINAL** DISCHARGES it: (RM-1-TRANSPORT) is proved, and the sweep reads “**LIFTCORNER PROP:** its rung-\(\ge2\) suspension is lifted. The all-rung propagation now follows at ITERLAWN’s own conditionality.”

**A consumer must therefore read PROP as: PROVED at ITERLAWN's own conditionality, via AC-4 + AC-5, NOT via the frozen text's own argument.** The frozen text's clause-(ii) census was never supplied in the form it asked for; what was supplied is a different and stronger pair of lemmas.

**Anticipation, recorded for the DAG:** the note had ALREADY stopped claiming PROP as proved four days before AC-1, at [r5, F5-1] (`.13`): the STATUS BLOCK PROVED line “drops "and PROP's rung propagation"”, with the CONDITIONALITY line's “(5) PROP's rung-≥2 clause-(ii) census is OWED” as its status of record. So AC-1's suspension corrected the S5 rider and FC-2's execution, not the note's own PROVED inventory.

**RESOLUTION TRACE:** statement lines 1034–1042; correction sites 1499–1517 (AC-1), 1618–1815 (AC-4), 1833–2070 (AC-5); the in-range anticipation at 263–265 and 1251–1253.

**TEETH:** charge item **(5)**. Disposition `AUDIT / decorrelated-model audit` — the certifier arc found and then closed this; no in-house tooth could, because ITERLAWN's S4.6 engine is not defined in this note (AC-1's own reasoning: “The missing lemma cannot be derived from the note’s own lemmas because WELL-DEF-\((n)\), the \(C_k\) construction, and the degree telescope are not defined here.”).

---

### EFF.LIFTCORNER.64  [changes-record]

**CANONICAL STATEMENT:**

> “**[r4, F4-4 — the CITE for that census is re-pointed; the r3 wording, quoted
> and superseded, was "is cited from the [ILN]/ILNRES consumption tables, not
> re-proved here".]** That cite was false as to location: ITERLAWN_PROOF's S7
> dependency/exemption sweep (22 rows) and ILNRES S6's "consumption census" are
> both keyed to *accepted-package* consumption (which levels, which of
> [IL]/[IL3]†/(RM-m)/DCX), and NEITHER contains any row about how much of Φ₁'s
> explicit form a rung leg opens (PE4 read all 22 rows; the nearest, rows 1 and
> 10, are level-scope claims). **The true site of record, and the one pin a
> rung-≥2 census must clear, is ITERLAWN's own r4 erratum** …
> **The pin, named explicitly**, is ITERLAWN
> S0.1's Lifts clause, verbatim: "**Φ₁ := the STANDARD LIFT of ψ₀**
> (grb_order2_check :499–507); for 1 ≤ m ≤ n−1, Φ_{m+1} := the CANONICAL
> ε_m-CORRECTED LIFT of ψ_m" — i.e. exactly the clause PROP relaxes on the Φ₁
> axis. So a rung-≥2 clause-(ii) census must show that S4.1/WELL-DEF-(n) and the
> S4.2 telescope read Φ₁ only through monicity, degree e₀d₀ and w₁Φ₁ = e₀g₀h₀
> (plausible — the C_k are built from ψ_m, γ_{m+1}, ε_m, realize_m and Φ_m, and
> Φ₂ = Σ_k C_kΦ₁^{e₁k} uses Φ₁ only as a power) — **an argument this note does
> not make, and which neither the two formerly cited tables nor ITERLAWN's own
> r4 erratum supplies** (PE4 read all 22 sweep rows and ILNRES S6's census; no
> row is about how much of Φ₁ a rung leg opens). Charge item (5)
> is re-scoped to exactly that: the census is OWED, its site of record is
> ITERLAWN's r4 erratum, and the deeper-level fence of S5 is untouched by it.”

**FORM:** bold-headed bracketed cite correction (with `…` marking the elision of the erratum's own quotation, which is verified separately below).

**DERIVATION:** PE4 read all 22 sweep rows and ILNRES S6's census and found no row of the required kind — a negative exhaustive check.

**CONDITIONALITY:** two later corrections land on this bracket. (1) **[r5, F5-4]** fixed its section pointer from S9 to **S7** — already applied in the text above (`.13`). (2) **AC-4 SUPERSEDES the 22-row table as the census of record**: “This adjudication uses ITERLAWN’s machine census of record, not the superseded 22-row or 23-row hand tables.” SUPERSESSION KIND: **scope-pin**. The bracket's admission — that this note does not make the argument — is precisely what AC-1 quotes to justify the suspension, and what AC-4/AC-5 then discharge.

**RESOLUTION TRACE:** statement lines 1043–1069; correction sites 271–273 (F5-4), 1620 (AC-4), 1501–1505 (AC-1 quoting this bracket).

**TEETH:** three independent PIN VERIFICATIONS at compile time, all clean:
- XREF X07 — ITERLAWN S7 exists at line 1148 as `## S7. THE CONDITIONALITY LEDGER (the exact grade of every clause, per rung)`, and its sweep table carries exactly **22 data rows** (24 pipe-lines − header − separator). F5-4's correction is CORRECT.
- XREF X08 — the r4 erratum's quoted L6 row is present verbatim at count 1: `attribution (errata r4, 2026-08-03; PE4-F1): + S4.1 at rungs ≥ 2 — the canonical-lift certification (WELL-DEF-(n)/(R1) + C_k existence) consumed via the S0.1 class pin and the S4.2 degree-telescope input; S4.1's m = 1 base rides [IL3]†; rung 1 given [IL] alone` (ITERLAWN line 278).
- XREF X05/X06 — the S0.1 Lifts clause is present verbatim at count 1 (ITERLAWN line 163).
Additionally, AC-4's 194-hit census partition is cross-verified against ITERLAWN's own machine-census bracket (line 1233): “194 raw hits on 147 lines, 194/194 mapped, ZERO unadjudicated (88 at table-row sites/duplicates/cure-brackets; 21 at the seven site-families F1–F7 …; 53 verification-apparatus; 8 quoted external record; 18 non-genre; 6 positive displays)” — the six-class partition and every class count match AC-4's transcription exactly, and 88+21+53+8+18+6 = **194** ✓.

---

### EFF.LIFTCORNER.65  [acceptance-box]  *(SERIES GRADE-BOX, link 1 — r1, carrying the r0 box)*

**CANONICAL STATEMENT:**

> “**Grade box + W-2 consumption census (the cap).** This note: ATTEMPT 0/2 —
> r1 is a REPAIR round, not a pass; one hostile pass has run (PE1: 1 CRITICAL
> + 3 gaps, all four repaired here) and the arc is OWED on THIS text.”

**FORM:** bold-headed box opening.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** counter superseded — see `.02`. The rule the box states (“a REPAIR round, not a pass”) is the arc's invariant and is restated in all six entries.

**RESOLUTION TRACE:** statement lines 1071–1073.

**TEETH:** superseded by the acceptance record (shard 2).

---

### EFF.LIFTCORNER.66  [acceptance-box]  *(SERIES GRADE-BOX, link 2 — r2)*

**CANONICAL STATEMENT:**

> “**[r2 — grade box updated.]** TWO hostile passes have now run: **PE1** on the
> r0 text (1 CRITICAL + 3 gaps → repair round r1) and **PE2** on the r1 text
> (**0 CRITICAL + 5 gaps** → this repair round r2 …).
> PE2 confirmed the F1 repair
> holds and re-derived its load-bearing pieces independently, but it returned 5
> gaps, so **no acceptance slot closed: the counter stays 0/2**, and the r2 edits
> (G1–G5) are themselves unaudited. **PE3 — a fresh hostile pass on THIS text —
> is the next acceptance attempt.**”

**FORM:** bracketed dated box entry.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** counter superseded (`.02`); “the r2 edits are unaudited” superseded at r3.

**RESOLUTION TRACE:** statement lines 1074–1081.

**TEETH:** as `.65`.

---

### EFF.LIFTCORNER.67  [acceptance-box]  *(SERIES GRADE-BOX, link 3 — r3)*

**CANONICAL STATEMENT:**

> “**[r3 — grade box updated.]** THREE hostile passes have now run … PE3 found no defect in the
> mathematics it audited, and all five of its gaps are evidence-DESCRIPTION
> defects (F-A the ψ₁-assert ranking, F-B the G4 witness display, F-C a machine
> quote attributed to PE2, F-D the grade box's own audit labels, F-E a zero-count
> family reported as a result), so no r3 edit touches the chain either. **The
> counter stays 0/2** — 5 gaps is not a clean pass, and a repair round is not a
> pass. Audit state after r3, plainly: charge items **(1), (2), (7)** have been
> re-derived by TWO hostile passes (PE2, PE3) with no acceptance credit; the r2
> edits have been read ONCE (PE3); **the r3 edits are UNAUDITED**.”

**FORM:** bracketed dated box entry.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** counter superseded (`.02`); audit state superseded at r4/r6/r7.

**RESOLUTION TRACE:** statement lines 1082–1095.

**TEETH:** the “no r3 edit touches the chain” claim is a scope statement about the round; it is consistent with this compilation's own finding that the r3 corrections are all `instrument-record` or `provenance-rider` units.

---

### EFF.LIFTCORNER.68  [acceptance-box]  *(SERIES GRADE-BOX, link 4 — r4)*

**CANONICAL STATEMENT:**

> “**[r4 — grade box updated.]** FOUR hostile passes have now run … PE4 found no defect in the
> mathematics and re-derived, from scratch, the eight per-digit ω-gain bounds,
> the census/lex/ρ consumers, READ-EQ digit by digit on both towers, the
> counter-instance's two passes and its double-development tie, and the THEOREM
> + COR 2 on a concrete ℤ₂/𝔽₄ orbit member; all six of its gaps are
> evidence-description / bookkeeping defects … **The counter stays 0/2** …
> Audit state after r4:
> items **(1), (2), (7)** have been re-derived by **THREE** hostile passes (PE2,
> PE3, PE4) with NO ACCEPTANCE CREDIT; the r2 edits have been read twice (PE3,
> PE4) and the r3 edits once (PE4); **the r4 edits are UNAUDITED**.”

**FORM:** bracketed dated box entry.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** counter superseded (`.02`).

**RESOLUTION TRACE:** statement lines 1096–1114.

**TEETH:** the three-pass re-derivation of items (1), (2), (7) is the strongest in-house warrant in the shard, and the note is scrupulous that it carries NO acceptance credit.

---

### EFF.LIFTCORNER.69  [acceptance-box]  *(SERIES GRADE-BOX, link 5 — r6; note the r5 GAP)*

**CANONICAL STATEMENT:**

> “**[r6 — grade box brought forward (the first since r4; the close just above is
> dated [r4] text).]** SIX hostile passes have now run — the two since the [r4]
> entry: **PE5** on the r4 text, the THIRD acceptance attempt (0 CRITICAL + 5
> gaps → r5, the five one-line fixes …), and **PE6** on the r5 text, the FOURTH acceptance attempt
> (**0 CRITICAL + 3 gaps** → this repair round r6 …). PE6's line-audit found ZERO
> defects in the r5 diff itself (all 32 insertions true, all five fixes
> correctly placed — the arc's first zero-new-defect round) and no defect in the
> mathematics on its sixth hostile reading; all three of its gaps are
> record-surface defects … **The counter
> stays 0/2** …”

**FORM:** bracketed dated box entry.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** counter superseded (`.02`). **SERIES GAP:** there is no r5 grade-box entry; this entry's own parenthetical says so (“the first since r4”). Recorded so a merge run does not interpolate.

**RESOLUTION TRACE:** statement lines 1115–1131.

**TEETH:** `git cat-file -t f2b48e7` = commit; report exists.

---

### EFF.LIFTCORNER.70  [acceptance-box]  *(SERIES GRADE-BOX, link 6 — r7, TERMINAL in range)*

**CANONICAL STATEMENT:**

> “**[r7 — grade box brought forward (the close just above is dated [r6]
> text).]** SEVEN hostile passes have now run — the one since the [r6] entry:
> **PE7** on the r6 text, the FIFTH acceptance attempt (**0 CRITICAL + 1 gap,
> minor** → this repair round r7, the one-clause F7-1 fix …). PE7's line-audit verified
> the r6 diff true and correctly placed at every hunk except the one census
> clause (F7-1, a transcribed unit mismatch: PE6's "42 occurrences" is a
> hit-LINE count), found the record system consistent and true at HEAD for
> the first time in the arc, judged r6's disclosed deviation CORRECT, and
> found no defect in the mathematics on its seventh hostile reading. **The
> counter stays 0/2** — a gap is not a clean pass, and a repair round is not a
> pass. Audit state after r7: the r7 edits are UNAUDITED; the r6 edits were
> line-audited by PE7; **PE8 — a fresh hostile pass on THIS text — is the next
> acceptance attempt.**”

**FORM:** bracketed dated box entry.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** counter superseded (`.02`) — and this is the entry the acceptance record answers: PE8 ran and was CLEAN, then PE9. **STALE-SELF-DESCRIPTION** (v3 rule 26) for the sentence “found the record system consistent and true at HEAD for the first time in the arc”: it was true at PE7's HEAD, and the note is not at that HEAD; `.59`'s three unclassified `c′` occurrences are a concrete instance of the drift.

**RESOLUTION TRACE:** statement lines 1132–1145.

**TEETH:** `git cat-file -t 58f7060` = commit; report exists.

---

### EFF.LIFTCORNER.71  [fence]

**CANONICAL STATEMENT:** the charge list, verbatim (lines 1145–1160):

> “Charge
> (r1-updated, item (7) added at r2 per PE2 G2; the r0 charge list named neither
> the step that broke nor the
> r1 argument — PE1 F1's closing observation, accepted): **(1) the S4.1
> seven-genre child census's COMPLETENESS** — that the pass identity, after
> the b₀-split and the r/q redigit, produces no branch outside rows 1–7 — and
> the row-7b degree drop; **(2) the lex-order finiteness argument** ((C)(ii):
> finite branching + the ρ depth bound); **(3)** the CONTENT sub-lemma's
> base-fact status; **(4)** the READ-EQ on-line-content/ultrametric close;
> **(5)** PROP's census cite; **(6)** COR 2's rescoped statement (the F3 box's
> (a)/(b) are owed for any W2-OPEN-1 tie, and are NOT part of this note's
> claim); **[r2, G2] (7) the EIGHT PER-DIGIT ω-gain bounds** of (A)'s last column
> (rows 1, 2, 3, 4, 5, 6, 7a, 7b) together with the CONTENT application that
> derives them per digit — new at r1, never named by the r1 charge list,
> re-derived once by PE2 (correct and tight) and, per (A)'s [r2, G4] bracket, no
> longer resting on the stricken r-to-q identity.”

**FORM:** inline enumerated fence.

**DERIVATION:** `[RECORD]` — the note's own list of what a reader must audit.

**CONDITIONALITY:** the list is the shard's TEETH SPINE, and its post-arc status differs item by item. Compiler's status table, each cell warranted above:

`[TABLE — compiler ledger]`

| item | content | status at HEAD | warrant |
|---:|---|---|---|
| (1) | census COMPLETENESS + row-7b drop | ∀ carried by algebra; instance-level machine leg A7 | `.38`, `.41`, `.44`, `.45`; three hostile re-derivations |
| (2) | lex-order finiteness (branching + ρ) | closed | `.48`; A7(iv); three hostile re-derivations |
| (3) | CONTENT's base-fact status | **REPAIRED by AC-2** (statement was too broad) | `.34` |
| (4) | READ-EQ close | closed, with its degree clause **REPAIRED by AC-3** | `.55`, `.56` |
| (5) | PROP's census cite | **DISCHARGED via AC-4 + AC-5**, not via the cited census | `.63`, `.64` |
| (6) | COR 2's rescoped statement; (a)/(b) owed | **(a) and (b) STILL OWED** | `.62` |
| (7) | eight per-digit ω-gain bounds | closed; no longer resting on the stricken identity | `.42`; PE2/PE3/PE4 |

**RESOLUTION TRACE:** statement lines 1145–1160.

**TEETH:** this IS the teeth list; the inverse map is §6.

---

### EFF.LIFTCORNER.72  [scope record]

**CANONICAL STATEMENT:**

> “W-2
> consumption: COR 2 and the S1 orbit frame consume GRTW2 clause 3 (the
> ψ-transport definition + its corner degeneration) — GRTW2 is itself 0/2, so
> **the unit's grade is CAPPED at that consumption, as charged**. Honest
> decoupling fact the arc may use: the COR 1 chain (TAIL-STAB + READ-EQ +
> accepted ITER-LAW) is W-2-free — if W-2's arc lags, the ξ = 1 discharge
> stands on this note's own arc alone.”

**FORM:** inline paragraph closing the grade box.

**DERIVATION:** `[RECORD]` of a consumption census with its grade consequence.

**CONDITIONALITY:** SUPERSESSION KIND: **counter re-reading** by FC-1 — “GRTW2 is itself 0/2” is superseded; the cap survives as a cap by an ACCEPTED supplier at its FENCED scope (GRTW2's own W2-OPEN-2/OPEN-2a box remains open). The decoupling fact is unaffected and is restated verbatim in the acceptance record.

**RESOLUTION TRACE:** statement lines 1160–1166; correction site 1459–1471.

**TEETH:** XREF X13 verifies the reverse edge — GRTW2's acceptance record names this consumer at count 1: “the accepted LIFTCORNER's shift-descent consumption; JB's W2-C1 restriction; WM's M4 face) now ride an ACCEPTED supplier at its fenced scope.” This is the ONE fully closed supplier-consumer loop in the shard: LIFTCORNER declares the consumption, GRTW2's acceptance record acknowledges it by name.

---

### EFF.LIFTCORNER.73  [scope record]

**CANONICAL STATEMENT:**

> “ONCE THIS NOTE'S ARC CLOSES (and not before — no ledger or accepted text is
> edited now): ITERLAWN S0.1's rider "(ITER-LAW-LIFT) open exactly at
> g₀ = 1 ∧ δ₁ = 1; nothing is claimed for any non-canonical lawful lift at any
> level" becomes, on the Φ₁ axis: "(ITER-LAW-LIFT) DISCHARGED at attempt grade
> (capped by the W-2 0/2 consumption; ξ = 1 core W-2-free): ITER-LAW-n holds
> for EVERY lawful monic Φ₁, every n, at [ILN]'s own conditionality, and
> covariantly for the full Φ₁-orbit by the χ-law".”

**FORM:** bold-headed paragraph under `## S5. Consequence display (what [ILN]'s rider becomes; at the capped grade, pending arcs)`.

**DERIVATION:** `[RECORD]` — a conditional rewrite instruction for a supplier's rider, not a theorem.

**CONDITIONALITY:** **three separate supersessions land on this one display.**
(a) “ONCE THIS NOTE'S ARC CLOSES” — the condition is MET (`.89`) and the license was EXECUTED (`.92`).
(b) “at attempt grade (capped by the W-2 0/2 consumption)” — superseded by FC-1 (`.91`): read as capped by an ACCEPTED supplier at its fenced scope. SUPERSESSION KIND: **counter re-reading**.
(c) “ITER-LAW-n holds for EVERY lawful monic Φ₁, every n” — **SUSPENDED by AC-1** (`.95`), then **reinstated by AC-5** (`.117`): “**LIFTCORNER S5:** the every-\(n\) rider on the \(\Phi_1\) axis is no longer conditional on \((\Phi_1\)-OPACITY). The fence excluding independently chosen noncanonical higher keys remains unchanged.” SUPERSESSION KIND: **scope-pin**, then **license**. TERMINAL = AC-5.
**Residual scope a consumer must carry:** AC-5 reinstates the rider *at ITERLAWN's own conditionality*, and ITERLAWN's (RM-m) engine is **OPEN at m ≥ 2** by its own STATUS box (XREF Y06: “m ≥ 2: **OPEN.**”). “Every n at [ILN]'s own conditionality” is therefore not an unconditional all-rung theorem, and never was.

**RESOLUTION TRACE:** statement lines 1170–1176; correction sites 1433 (a), 1459–1471 (b), 1509 + 2053–2057 (c).

**TEETH:** XREF Y01 verifies ITERLAWN's rider text and Y10 the landed fold annex, which transcribes this display verbatim and calls it “verbatim from LIFTCORNER S5”, citing “lines 1168–1176 at acceptance” — the exact span of this unit.

---

### EFF.LIFTCORNER.74  [changes-record]  *(CHAIN-S, link 2)*

**CANONICAL STATEMENT:**

> “**[r4, F4-6 — the bookkeeping sentence that followed is STRICKEN and replaced
> by the three paragraphs below. The r3 wording, quoted in full and superseded:**
> "NR-1 then leaves the ILNRES residual list; the T-class(n) conditionality of
> record shrinks to NR-2/NR-3 (+ NR-4's own closing arc). NOT covered, said
> plainly: non-canonical lawful lifts at DEEPER levels (Φ_{m+1}, m ≥ 1) — a
> separate corner (the g_m = 1 analogue), never part of (ITER-LAW-LIFT)'s
> displayed statement (wave-18 S0), stays open as its own priced item."**]**”

**FORM:** bold-headed bracketed strike quoting its target in full.

**DERIVATION:** `[RECORD]`. The reason is given at `.77`: the unit has no authority to create a residual, and an uncited new one would collide with ILNRES S7's recorded completeness.

**CONDITIONALITY:** SUPERSESSION KIND: **replacement** (one sentence by three paragraphs). The quoted r3 wording is DEAD.

**RESOLUTION TRACE:** statement lines 1178–1184; replacement at 1186–1223.

**TEETH:** the collision it avoids is verified — XREF Y03: ILNRES line 288, `S1's FOUR-MEMBER residual list is COMPLETE relative to the sources`, count 1.

---

### EFF.LIFTCORNER.75  [scope record]

**CANONICAL STATEMENT:**

> “**What this note delivers, exactly.** The **Φ₁ corner** of NR-1:
> (ITER-LAW-LIFT) for every lawful monic lift Φ₁ at g₀ = 1 ∧ δ₁ = 1 (COR 1),
> plus the χ-covariance across the harness Φ₁-orbit (COR 2) and PROP's rung
> propagation at [ILN]'s own conditionality. That is exactly the deliverable of
> the spec of record, ILNRES S5.1 — "Extend the [IL] L7 Case-II analysis to an
> arbitrary lawful lift Φ₁′ = Φ₁ + (π-excess) at g₀ = 1 ∧ δ₁ = 1, then ride
> S0.1's verbatim propagation" — and exactly the residual as DISPLAYED at
> wave-18 S0: "the honest OPEN displayed lemma **(ITER-LAW-LIFT)**: ITER-LAW for
> every lawful monic lift Φ₁" (Φ₁ only; both quotes verified at source, and PE4
> independently confirmed the delivery matches the spec). **So the honest claim
> is: NR-1's Φ₁ corner is DISCHARGED PENDING THIS NOTE'S ARC** (attempt 0/2,
> W-2-capped; the ξ = 1 core W-2-free). No residual leaves any list until the arc
> closes, and this note edits no ledger.”

**FORM:** bold-headed paragraph with two embedded source quotations.

**DERIVATION:** a delivery-versus-spec comparison, with both spec quotes cited to source and confirmed by PE4.

**CONDITIONALITY:** “PENDING THIS NOTE'S ARC (attempt 0/2, W-2-capped)” is superseded twice — by `.89` (2/2) and by FC-1 (`.91`). The PROP clause is CHAIN-P (TERMINAL AC-5). “this note edits no ledger” is true of the note and remains true; the ledger edit happened as a separate append on ITERLAWN (`.92`).

**RESOLUTION TRACE:** statement lines 1186–1198.

**TEETH:** **both embedded quotes independently re-verified at compile time under whitespace normalization** (they span source line breaks, so single-line `grep -F` fails; recorded as verified-by-normalized-match per v3 rule 15):
- XREF Y02 — `ILNRES_2026-08-08.md`, `Extend the [IL] L7 Case-II analysis to an arbitrary lawful lift Φ₁′ = Φ₁ + (π-excess) at g₀ = 1 ∧ δ₁ = 1, then ride S0.1's verbatim propagation` — count 1 (line 180).
- XREF Y04 — `ITERLAWLIFT_CORNER_2026-08-08.md`, `the honest OPEN displayed lemma **(ITER-LAW-LIFT)**: ITER-LAW for every lawful monic lift Φ₁` — count 1 (lines 35–36).
The note's parenthetical claim “both quotes verified at source” is therefore itself verified.

---

### EFF.LIFTCORNER.76  [scope record]

**CANONICAL STATEMENT:**

> “**The discrepancy, stated neutrally.** NR-1 as RECORDED in ILNRES S1 is wider
> than the residual as DISPLAYED at wave-18 S0: the recorded statement quotes the
> [IL] rider "nothing is claimed for any non-canonical lawful lift **at any
> level**", which reads on Φ_{m+1} for m ≥ 1 as well. This note covers the Φ₁
> level only. Under the wave-18 / S5.1 reading NR-1 is addressed in full here;
> under the ILNRES S1 "at any level" reading a deeper-level remainder survives.
> The two readings live in different notes of record, and this unit does not
> choose between them.”

**FORM:** bold-headed paragraph.

**DERIVATION:** a comparison of two sources of record that disagree in scope.

**CONDITIONALITY:** **the note declines to adjudicate, and that declination is itself the effective content.** AC-1's finding 2 later cites this paragraph and `.77` as already curing a certifier objection (`.97`), which confirms the fence but does not resolve the discrepancy.

**RESOLUTION TRACE:** statement lines 1200–1207.

**TEETH:** XREF Y05 — `ILNRES_2026-08-08.md`, `nothing is claimed for any non-canonical lawful lift at any level`, count 1 (line 28, verified under normalization across a line break).

---

### EFF.LIFTCORNER.77  [scope record]  *(CHAIN-S — TERMINAL of the in-note layers)*

**CANONICAL STATEMENT:**

> “**Disposition of the deeper levels — NOT a new priced item.** Non-canonical
> lawful lifts at levels m ≥ 1 (Φ_{m+1}, the g_m = 1 analogue) are **not covered
> here and are not priced by this note**; r3's "stays open as its own priced
> item" is withdrawn, because this unit has no authority to create a residual and
> an uncited new one would collide with ILNRES S7's recorded outcome that "S1's
> FOUR-MEMBER residual list is COMPLETE relative to the sources of record — NO
> FIFTH RESIDUAL EXISTS". **Flagged for the next fold as an ILNRES-side ERRATUM
> CANDIDATE (ILNRES is NOT edited here):** ILNRES's own ledger entry should rule
> whether the "at any level" clause of NR-1's recorded statement is (a) a scope
> fence in the genre of its perimeter fact (iii) ("orders ≥ 3 untouched … is
> subsumed by [ILN] itself"), in which case the Φ₁ corner is the whole of NR-1
> and this note discharges it on its arc; or (b) a live conditionality, in which
> case it is a fifth member and the S7 completeness sentence needs amending.
> Until ILNRES rules, **nothing here re-prices anything**, and the consequence
> display above should be read as changing the **Φ₁ axis** of the rider only.”

**FORM:** bold-headed paragraph with a labelled (a)/(b) alternative.

**DERIVATION:** an authority argument (a unit may not create a residual) plus a consistency argument (a new residual would contradict ILNRES S7).

**CONDITIONALITY:** **the ILNRES-side erratum candidate is STILL OPEN at HEAD** — verified negatively: `grep -cF 'LIFTCORNER' ILNRES_2026-08-08.md` = 0 and `grep -cF 'erratum' ILNRES_2026-08-08.md` returns no LIFTCORNER-related entry, so ILNRES has not ruled. See OPEN-CALL 2.

**RESOLUTION TRACE:** statement lines 1209–1223.

**TEETH:** XREF Y03 (the S7 completeness sentence, count 1). The (a)/(b) alternative is the cleanest open decision in the note and is exactly the kind a Phase-0c DAG must carry as a live edge, not a footnote.

---

### EFF.LIFTCORNER.78  [instrument-record]

**CANONICAL STATEMENT:**

> “**STATUS BLOCK [r4; edited r5, r6, r7] — REGENERATED from a minimal five-line template.** This
> block is the note's whole status of record; it replaces the r1, r2 and r3
> STATUS LINEs wholesale (they are quoted verbatim, byte-unchanged, inside the
> [r4, ARCHIVE] region below). The status surface produced findings in three
> consecutive passes — PE2's G2 attribution, PE3's F-C/F-D, PE4's F4-2/F4-3 —
> so it is now five lines and nothing else. **Standing rule for future rounds:
> edit these five lines; do not grow a sixth.**”

**FORM:** bold-headed block preamble carrying a standing rule.

**DERIVATION:** a defect-density argument: three consecutive passes found defects in the status surface, so the surface is minimized. This is the same methodological move as `.15` of shard 1 (the transcription rule) — the arc repeatedly converts a recurrence into a structural rule.

**CONDITIONALITY:** the rule was honoured: the block is still five bullets at HEAD (`.79`–`.83`), edited at r5, r6, r7 and never grown. Verified by inspection.

**RESOLUTION TRACE:** statement lines 1225–1231.

**TEETH:** disposition `instrument-record`; the instrument is the record surface itself. PE6 and PE7 both line-audited it and judged the bring-forward correct.

---

### EFF.LIFTCORNER.79  [acceptance-box]  *(SERIES REPAIR-ARC, continuation)*

**CANONICAL STATEMENT:**

> “* **ARC.** PE1 (1 CRITICAL + 3 gaps) → r1 → PE2 (0C + 5G) → r2 → PE3 (0C + 5G;
>   the arc's FIRST acceptance attempt) → r3 → PE4 (0C + 6G; the SECOND
>   acceptance attempt) → r4 → PE5 (0C + 5G; the THIRD acceptance attempt) →
>   r5 (the five one-line fixes F5-1…F5-5) → PE6 (0C + 3G; the FOURTH
>   acceptance attempt) → r6 (the three record-surface fixes F6-1…F6-3) →
>   PE7 (0C + 1 minor; the FIFTH acceptance attempt) → **r7 (this round: the
>   one-clause census-unit fix F7-1, nothing else)** → **PE8 = the next
>   acceptance attempt.**”

**FORM:** bullet (line 1 of 5).

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** the terminal “PE8 = the next acceptance attempt” is SPENT: `.89` records PE8 CLEAN and PE9 CLEAN. SUPERSESSION KIND: **as-of scoping**.

**RESOLUTION TRACE:** statement lines 1233–1240; continuation at 1437–1439.

**TEETH:** ARITHMETIC AUDIT: seven repair rounds and seven passes are listed here; the acceptance record adds two more passes for **nine hostile passes, seven repair rounds** — which is exactly what it claims (“Nine hostile passes, seven repair rounds”). ✓ All nine report files exist; all nine commit pins resolve (shard 1 §3.4, P06–P15).

---

### EFF.LIFTCORNER.80  [acceptance-box]  *(CHAIN-G, link 1)*

**CANONICAL STATEMENT:**

> “* **COUNTER.** Acceptance **0/2** — no pass has been clean, and a repair round
>   is not a pass. The grade is CAPPED by this unit's W-2 consumption (GRTW2
>   itself 0/2); the COR 1 / ξ = 1 chain is W-2-free, so if W-2's arc lags the
>   ξ = 1 discharge stands on this note's own arc alone.”

**FORM:** bullet (line 2 of 5).

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** **both halves superseded.** 0/2 → 2/2 (`.89`, CHAIN-G TERMINAL); “GRTW2 itself 0/2” → FC-1's accepted supplier (`.91`, CHAIN-W TERMINAL). The decoupling clause survives verbatim into the acceptance record.

**RESOLUTION TRACE:** statement lines 1241–1244; correction sites 1433, 1459–1471.

**TEETH:** as `.89`, `.91`.

---

### EFF.LIFTCORNER.81  [acceptance-box]

**CANONICAL STATEMENT:**

> “* **PROVED (at that grade).** (TAIL-STAB) by S4.1 as repaired at r1, statement
>   byte-unchanged, its argument re-derived independently by PE2, PE3 and PE4;
>   and on it READ-EQ, the THEOREM, **COR 1** ((ITER-LAW-LIFT) at the corner —
>   and δ₁ = 1 is EMPTY at e₀ = 1, so S4's e₀ ≥ 2 Setting costs COR 1 nothing),
>   and COR 2 on the harness orbit. S3's corner
>   measurement (25,409 checks / 0 violations) is machine fact either way.”

**FORM:** bullet (line 3 of 5).

**DERIVATION:** `[RECORD]` of the proved inventory. **This is the unit that homes PE4's one positive finding** (δ₁ = 1 empty at e₀ = 1) — shard 1 `.12` and `.32` point here, and [r5, F5-5] re-aimed the r4 header's pointer at exactly this bullet.

**CONDITIONALITY:** **PROP is absent by design** — [r5, F5-1] removed “and PROP's rung propagation” from this line on 2026-08-06, six days before AC-1 suspended it elsewhere. The inventory here has been correct since r5.

**RESOLUTION TRACE:** statement lines 1245–1250; the F5-1 edit recorded at 263–265 (shard 1); the F5-5 re-pointing at 273–274.

**TEETH:** 25,409/0 re-verified against the committed artifact (shard 1 §6.3). The five proved items match the acceptance record's five (`.90`) exactly — a cross-check that the record surface and the acceptance record agree on the supply set.

---

### EFF.LIFTCORNER.82  [acceptance-box]

**CANONICAL STATEMENT:**

> “* **CONDITIONALITY.** Grade-box charge items (1)–(7), of which **(5) PROP's
>   rung-≥2 clause-(ii) census is OWED** with its site of record re-pointed at
>   [r4, F4-4]; COR 2's W2-OPEN-1 tie needs (a) and (b) of the [r1, F3] box;
>   NR-1's discharge is the **Φ₁ corner** only, pending this note's arc, with the
>   deeper-level reading flagged as an ILNRES-side erratum candidate ([r4,
>   F4-6]); wave-18's price sheet is settled MODULO this note's own arc, not "in
>   full".”

**FORM:** bullet (line 4 of 5).

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** item-by-item at HEAD: **(5) is DISCHARGED** by AC-4+AC-5 (CHAIN-P), though not by the census it asks for; **COR 2's (a)/(b) remain OWED** (AC-5 leaves COR 2 unchanged); **the ILNRES erratum candidate remains OPEN** (`.77`, verified negatively); “pending this note's arc” is spent (`.89`).

**RESOLUTION TRACE:** statement lines 1251–1257.

**TEETH:** the seven-item status table is compiled at shard 1 `.71`.

---

### EFF.LIFTCORNER.83  [acceptance-box]

**CANONICAL STATEMENT:**

> “* **NEXT / AUDIT STATE.** PE8, a fresh hostile pass on THIS text. Unaudited
>   going in: **the r7 edits** (the r6 edits were line-audited by PE7 — all
>   four hunks verified true except the one census clause, its F7-1 — the r5
>   edits by PE6, the r4 edits by PE5; earlier edit sets read twice or more).
>   Items (1), (2), (7): re-derived by three hostile passes, NO acceptance
>   credit. Both machine legs BYTE-FROZEN and re-run clean at PE7
>   (sealed runner exit 0, 25,409/0, md5 `ccb4351c92573f5f962cae4ae952d8dd`,
>   `git diff dafc0b5 HEAD` = 0 bytes, output identical modulo timing fields;
>   children table regenerates byte-identically, A7's four legs PASS).”

**FORM:** bullet (line 5 of 5).

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** **STALE-SELF-DESCRIPTION** (v3 rule 26) — “Unaudited going in: the r7 edits” is superseded by PE8 and PE9, both CLEAN, which audited them. The sentence is not corrected under the freeze; a reader must be told it is no longer true. “Items (1), (2), (7) … NO acceptance credit” is likewise superseded: the acceptance record's “every substantive component re-derived by at least two independent fresh readers” plus 2/2 supplies the credit.

**RESOLUTION TRACE:** statement lines 1258–1266; correction site 1433–1441.

**TEETH:** the md5 and the `git diff dafc0b5 HEAD` = 0 bytes claims are re-verified at compile time (`md5sum` matches; `dafc0b5` resolves).

---

### EFF.LIFTCORNER.84  [changes-record]

**CANONICAL STATEMENT:** the archive preamble and its three inside-archive corrections, `[ASSEMBLED]` from lines 1268–1295. The preamble, verbatim:

> “**[r4, ARCHIVE — the three superseded STATUS LINEs (r1, r2, r3) follow between
> the ARCHIVE-BEGIN / ARCHIVE-END markers, quoted BYTE-UNCHANGED.]** Nothing
> between the markers is live: it is superseded wholesale by the five-line STATUS
> BLOCK above, and is kept only because this note's discipline never silently
> deletes superseded wording. THREE corrections apply INSIDE the archive and are
> stated here so no sentence in it can be misread as current:”

The three, in brief and each quoted at its target unit: **(1) [F4-2]** the r1 STATUS LINE's F4 clause is REFUTED, final description = S2 (c)'s [r4, F4-1] bracket; **(2) [F4-3]** the r2 STATUS LINE's `[r3, F-C]` provenance is wrong (origin is PE2's report); **(3) [F4-1, third site]** the r3 STATUS LINE's own summary of F-A carries the refuted promotion of assert (ii).

**FORM:** bold-headed bracketed archive preamble with three numbered corrections.

**DERIVATION:** `[RECORD]`. The design principle is stated: dead text is retained but must be individually corrected wherever a sentence in it could read as current.

**CONDITIONALITY:** SUPERSESSION KIND: **replacement** (wholesale, of three status lines by one block), with three nested **provenance-rider**/**replacement** corrections inside the dead region. **TARGETS:** `.85`, `.86`, `.87`.

**RESOLUTION TRACE:** statement lines 1268–1295; the archive markers at 1297 (`<!-- ARCHIVE-BEGIN … -->`) and 1418 (`<!-- ARCHIVE-END -->`).

**TEETH:** the three corrections' terminals all live in shard 1 (`.25` for (1) and (3); `.10` for (2)) — this unit is the archive's index into CHAIN-A and CHAIN-B.

---

### EFF.LIFTCORNER.85  [changes-record — DEAD]  *(SERIES ARCHIVE-STATUS, link 1)*

**CANONICAL STATEMENT (dead text, retained byte-unchanged):**

> “**STATUS LINE (r1-honest; supersedes the r0 sentence "The wave-18 sketch's
> one open step (TAIL-STAB) is CLOSED by S4.1 (its ω is this ledger; the
> monomial form is subsumed); wave-18's price sheet is settled in full").**
> As of repair round r1: (TAIL-STAB) is PROVED by S4.1 AS REPAIRED — the r0
> proof's strict-descent clause (m′ ≤ m−1 at every child) was REFUTED by PE1
> at the top-mid q-child (m′ = m), the lemma STATEMENT is byte-unchanged, and
> the argument now rides the lexicographic (m, deg a) descent over a
> seven-genre child census derived from the committed examples-first table … So:
> wave-18's price sheet is settled MODULO this note's own arc, not "in full".
> The three r1 gap repairs, for the record: ĉ′/t₀ now defined in-note (F2);
> COR 2's W2-OPEN-1 identification WITHDRAWN and rescoped, with (a)/(b) owed
> (F3); S2 disclosure (c) corrected to what the runner actually asserts (F4).”

**FORM:** bold-headed status line (dead).

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** DEAD in full (`.84`), and its F4 clause additionally REFUTED by archive correction (1). It carries one fact worth preserving for the DAG: it names the r0 sentence it supersedes (“wave-18's price sheet is settled in full”), which is the note's own first overclaim and the origin of the “MODULO this note's own arc” formula repeated in every later status line.

**RESOLUTION TRACE:** statement lines 1299–1319; the refutation at 1274–1281.

**TEETH:** none (dead text); guarded by `.84`.

---

### EFF.LIFTCORNER.86  [changes-record — DEAD]  *(SERIES ARCHIVE-STATUS, link 2)*

**CANONICAL STATEMENT (dead text, retained byte-unchanged):** the r2 STATUS LINE (lines 1321–1379), which itself carries two nested dated brackets — `[r3, F-D]` (the audit labels on charge items (1)–(2) corrected, and the “never been read by anyone” clause superseded: “PE3 has now read them”) and `[r3, F-C]` (the second site of the “bit-identically” overstatement, corrected to PE2's qualified record). Opening, verbatim:

> “**STATUS LINE [r2] (supersedes the r1 clause "the r1 argument itself has NEVER
> been hostile-read, and the grade box's charge (1)–(2) names exactly which of
> its steps are unaudited" — the r1 argument HAS now been hostile-read, and the
> charge list has grown).** As of repair round r2: **(TAIL-STAB) is PROVED by
> S4.1 as repaired at r1 and confirmed at PE2 — 0 CRITICAL** on the r1 argument,
> with PE2 independently re-deriving the 9 ↦ 7 genre mapping (total, disjoint),
> row 7b's degree drop at every boundary (deg a = 0, deg b = 0, a or b zero), the
> two emptiness strata as PROVED rather than measured, and the ρ depth function's
> strict drop on every child edge.”

**FORM:** bold-headed status line with two nested dated brackets (dead).

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** DEAD in full, and its `[r3, F-C]` bracket additionally corrected for PROVENANCE by archive correction (2) — whose terminal is shard 1 `.10`. **This is a three-deep nesting inside dead text** (dead status line ⊃ live-at-the-time r3 bracket ⊃ r4 correction stated in the archive preamble), and it is the reason `.84` exists as its own unit.

**RESOLUTION TRACE:** statement lines 1321–1379; corrections at 1282–1289.

**TEETH:** none (dead text). The r2 five-repair inventory it records (G1–G5) is compiled live at shard 1 `.42`, `.44`, `.46`, `.48`, `.51`.

---

### EFF.LIFTCORNER.87  [changes-record — DEAD]  *(SERIES ARCHIVE-STATUS, link 3)*

**CANONICAL STATEMENT (dead text, retained byte-unchanged):** the r3 STATUS LINE (lines 1381–1416). Its load-bearing content, verbatim:

> “**THE ARC:** PE1 (1 CRITICAL + 3 gaps) → r1 → PE2 (0 CRITICAL + 5 gaps) → r2 →
> PE3 (0 CRITICAL + 5 gaps; the arc's FIRST acceptance attempt) → **r3 (this
> round, F-A…F-E applied)** → **PE4 = the next acceptance attempt**. Grade:
> **attempt 0/2, unchanged** …
> What r3 changed
> is entirely the note's EVIDENCE-DESCRIPTION layer, never the chain”

and the PE3 finding that matters downstream:

> “the (TAIL-STAB) consumer
> interface at every downstream site (finding that READ-EQ's one pass sits
> entirely in the deg a = 0 stratum, where the repaired proof shows there are no
> q-children at all, so the r0 defect could never have propagated there).”

**FORM:** bold-headed status line (dead).

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** DEAD, and its summary of F-A carries the refuted promotion of assert (ii) per archive correction (3). **But the PE3 propagation finding quoted second is NOT superseded and is not recorded anywhere live** — it is the fact that bounds the blast radius of the r0 CRITICAL (READ-EQ never used a q-child, so the defect could not have propagated). Recorded here so the merge run does not lose it with the archive. See OPEN-CALL 4.

**RESOLUTION TRACE:** statement lines 1381–1416; corrections at 1290–1295.

**TEETH:** none (dead text), except that the propagation finding is independently checkable against shard 1 `.46` (at deg a = 0 row 7b is empty) and `.56` (READ-EQ's one pass) — and it does check out: READ-EQ's b₀-main children are single digits with deg a′ constrained by the S1 degree bounds, and the pass is the deg a = 0 case.

---

### EFF.LIFTCORNER.88  [record]

**CANONICAL STATEMENT:**

> “— LIFT-CORNER unit, campaign date 2026-08-08 (wallclock 2026-08-04);
> repair round r1 applied 2026-08-08 campaign (wallclock 2026-08-05);
> repair round r2 applied 2026-08-08 campaign (wallclock 2026-08-05);
> repair round r3 applied 2026-08-08 campaign (wallclock 2026-08-05);
> repair round r4 applied 2026-08-08 campaign (wallclock 2026-08-05);
> repair round r5 applied 2026-08-08 campaign (wallclock 2026-08-06);
> repair round r6 applied 2026-08-08 campaign (wallclock 2026-08-06);
> repair round r7 applied 2026-08-08 campaign (wallclock 2026-08-06).”

**FORM:** dating footer (seven lines + the unit line).

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** complete for r1–r7. **It stops at r7 and never records the acceptance, the FC annexes, or the four certifier appends** — five dated events after r7 are absent from the note's own dating record. Not an error (the footer is a repair-round log), but a merge run building a chronology must not use it alone.

**RESOLUTION TRACE:** statement lines 1420–1427. The r5 and r6 lines were added at [r6, F6-3] (“the closing dating record gains its missing r5 line … and this round's r6 line”); the r7 line at [r7].

**TEETH:** ARITHMETIC AUDIT: seven repair-round lines for seven repair rounds ✓; the r5/r6 lines' provenance in F6-3 is verified in shard 1 `.14`.

---

### EFF.LIFTCORNER.89  [acceptance-box]  *(CHAIN-G — TERMINAL; SERIES REPAIR-ARC — TERMINAL)*

**CANONICAL STATEMENT:**

> “**THIS NOTE IS ACCEPTED at 2/2** — two consecutive clean hostile passes:
> PE8 (report c6097d7, CLEAN 0C/0G) and PE9 (report 9b5175c, CLEAN 0C/0G,
> including a fresh-instance leg at p = 7 outside the sealed battery's
> roster: 2,178 nonzero digits, 0 violations, the PE1 counter-instance
> identity re-multiplied exact). Full arc: PE1 (1C+3G) → r1 → PE2 (0C+5G)
> → r2 → PE3 (0C+5G) → r3 → PE4 (0C+6G) → r4 → PE5 (0C+5G) → r5 → PE6
> (0C+3G) → r6 → PE7 (0C+1m) → r7 → PE8 CLEAN → PE9 CLEAN. Nine hostile
> passes, seven repair rounds, every substantive component re-derived by
> at least two independent fresh readers.”

**FORM:** bold-headed paragraph under `## ★ ACCEPTANCE RECORD (orchestrator, 2026-08-06) ★`.

**DERIVATION:** `[RECORD]` of two consecutive clean passes.

**CONDITIONALITY:** none on the counter itself. **PE9's fresh-instance leg at p = 7 is the one piece of evidence in the whole note that lies OUTSIDE the sealed roster** — the sealed battery is over p ∈ {2,3} rings and the children generator over p ∈ {2,3,5}; p = 7 is new. Its figures (2,178 nonzero digits, 0 violations) are **UNPINNED to any committed artifact** in this repo: the PE9 report exists, but no `verification/openmath/` file records the p = 7 run. Disposition `UNPINNED` (v3 rule 23), recorded as OPEN-CALL 5.

**RESOLUTION TRACE:** statement lines 1433–1441.

**TEETH:** `git cat-file -t c6097d7` = commit; `git cat-file -t 9b5175c` = commit; both `LIFTCORNER_passPE8_report.md` and `LIFTCORNER_passPE9_report.md` exist. ARITHMETIC AUDIT: the arc lists 9 passes and 7 rounds ✓, matching `.79`'s ARC bullet extended by two.

---

### EFF.LIFTCORNER.90  [acceptance-box]

**CANONICAL STATEMENT:**

> “**WHAT IS ACCEPTED**: this note's theorems as fenced — (TAIL-STAB) via
> lexicographic (m, deg a) descent; READ-EQ; THE THEOREM (the display with
> the letter the lift carries, every orbit member); COR 1 (the ξ = 1
> slice); COR 2 (the corner restriction, as rescoped at r1/F3) — at the
> note's own conditionality: **the shift-descent consumption of GRTW2
> (0/2, arc open) caps the discharge grade; the ξ = 1 core chain is
> W-2-free as displayed.** NR-1's discharge is hereby at ACCEPTED grade
> modulo the W-2 cap. The S5 rider-rewrite display (what [ILN]'s NR-1
> entry becomes) is NOW LICENSED for execution at the next ledger fold.
> Machine record: sealed runner 25,409/0 (md5 ccb4351c… byte-frozen
> dafc0b5 → HEAD); children generator + A7 752/5,336/0.”

**FORM:** bold-headed paragraph.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** three riders. (a) “(0/2, arc open)” → FC-1 (`.91`), CHAIN-W. (b) “NOW LICENSED for execution” → discharged by FC-2 (`.92`), CHAIN-F, then suspended by AC-1 and reinstated by AC-5. (c) **PROP is not in the accepted list** — five items, and the all-rung propagation is not one of them; this is the fact AC-1 exploits and this compilation records it as a positive scope finding in both shards.

**RESOLUTION TRACE:** statement lines 1443–1453; correction sites 1459–1471 (a), 1473–1481 + 1509 + 2058 (b).

**TEETH:** the machine record's three figures re-verified at compile time: md5 ✓, `TOTAL checks 25409` ✓, `nodes reconciled: 752   children enumerated: 5336` ✓.

---

### EFF.LIFTCORNER.91  [changes-record]  *(CHAIN-W — TERMINAL)*

**CANONICAL STATEMENT:**

> “> **[ANNEX 2026-08-08, orchestrator, fold-carry closure FC-1 — the W-2
> cap.]** The acceptance record above reads "the shift-descent consumption
> of GRTW2 (0/2, arc open) caps the discharge grade" and "NR-1's discharge
> is hereby at ACCEPTED grade modulo the W-2 cap". The cap's supplier has
> since been ACCEPTED at 2/2 — GRTW2 at adc6cf3 (2026-08-07), with
> W2-OPEN-2/OPEN-2a accepted AS A BOX (the weld's one fenced open lemma) —
> and the supplier's acceptance record names this consumer: "the accepted
> LIFTCORNER's shift-descent consumption … now ride[s] an ACCEPTED supplier
> at its fenced scope." Wherever this note bills GRTW2 at "0/2 / arc open"
> (the record above; the grade box's W-2 cap), read: capped by an ACCEPTED
> supplier at its fenced scope — NR-1's discharge stands at ACCEPTED grade
> riding accepted suppliers throughout, and the ξ = 1 core chain stays
> W-2-free as displayed. Direction: FAVORABLE.”

**FORM:** dated ANNEX blockquote.

**DERIVATION:** `[RECORD]` of a supplier's grade change, with the supplier's own acknowledgement quoted.

**CONDITIONALITY:** SUPERSESSION KIND: **counter re-reading**, scoped “wherever this note bills GRTW2 at 0/2 / arc open”. **The cap does not disappear** — it becomes a cap by an accepted supplier AT ITS FENCED SCOPE, and GRTW2's fence is its own open box (W2-OPEN-2/OPEN-2a). **TARGETS:** `.02`, `.72`, `.80`, `.90`, and (transitively) the six shard-1 grade-box entries.

**RESOLUTION TRACE:** statement lines 1459–1471.

**TEETH:** the supplier acknowledgement is verified at count 1 — XREF Y07: `GRTW2_PROOF_2026-08-08.md` line 1351, “the accepted LIFTCORNER's shift-descent”, in the sentence “consumers riding W-2 at attempt grade (the accepted LIFTCORNER's shift-descent consumption; JB's W2-C1 restriction; WM's M4 face) now ride an ACCEPTED supplier at its fenced scope.” `git cat-file -t adc6cf3` = commit. **This is a two-way verified edge**: consumer declares, supplier acknowledges, both at count 1.

---

### EFF.LIFTCORNER.92  [changes-record]  *(CHAIN-F, link 2)*

**CANONICAL STATEMENT:**

> “> **[ANNEX 2026-08-08, FC-2 — the rider-rewrite license.]** The record's
> clause "The S5 rider-rewrite display (what [ILN]'s NR-1 entry becomes) is
> NOW LICENSED for execution at the next ledger fold" is DISCHARGED:
> executed at 5054d69 (2026-08-07) as an append-only fold annex on
> `ITERLAWN_PROOF_2026-08-08.md` (the S5 display transcribed verbatim; all
> 8 occurrence sites enumerated and governed; grade = ACCEPTED mod the W-2
> cap), then supplemented at adc6cf3 after GRTW2's acceptance (the cap = an
> accepted supplier). Direction: FAVORABLE (license executed; nothing
> further owed on this item).”

**FORM:** dated ANNEX blockquote.

**DERIVATION:** `[RECORD]` of an executed license.

**CONDITIONALITY:** **“nothing further owed on this item” is FALSE at HEAD, by the note's own later appends.** AC-1: “**FC-2:** its execution of the all-rung rider remains SUSPENDED and must be read conditionally.” AC-5: “**FC-2:** its executed rider rewrite is reinstated on the \(\Phi_1\) axis.” CHAIN-F's TERMINAL is AC-5, so the net state is again FAVORABLE — but the *landed annex on ITERLAWN records neither event* (OPEN-CALL 1). SUPERSESSION KIND: **scope-pin** then **license**.

**RESOLUTION TRACE:** statement lines 1473–1481; correction sites 1509 (AC-1), 2058–2060 (AC-5).

**TEETH:** XREF Y10 verifies the landed annex at `ITERLAWN_PROOF_2026-08-08.md` line 1518, count 1. Its own text corroborates three of FC-2's claims independently: it names the acceptance commit (`08f61e9`, verified), quotes the rider rewrite “verbatim from LIFTCORNER S5”, and enumerates the occurrence sites — “**The rider as written (8 occurrence sites at this commit: lines 49, 118, 341, 686, 1055, 1108, 1248, 1282)**”. Compile-time recount of that enumeration: **8 line numbers listed** ✓, matching FC-2's “all 8 occurrence sites”. `git cat-file -t 5054d69` = commit.

---

### EFF.LIFTCORNER.93  [record]

**CANONICAL STATEMENT:**

> “The sol-5.6 as-built read of this note (gpt-5.6-sol high,
> runs/cert/C1_liftcorner_output.log, 2026-08-12) returned CHALLENGE
> (1 CRITICAL, 2 GAP, 2 MINOR). The E1 certification run (gpt-5.6-sol
> high, runs/cert2/E1_liftcorner_output.log) adjudicated all five:
> finding 2 RESOLVED-ALREADY (the [r4, F4-6] fence), finding 5 ARTIFACT
> (rebutted from the note's own [r3]/[r4] lines), findings 3 and 4 REAL
> with repairs (annexes AC-2, AC-3), and finding 1 OBSTRUCTED with the
> containment annex AC-1 naming the missing lemma (Φ₁-OPACITY) and its
> pre-proof numerical certificate. Everything above this heading is
> byte-untouched by this append. The E1 adjudication, transcribed
> unaltered:”

**FORM:** paragraph preamble under `### Dated adjudication (2026-08-12 — sol certification C1/E1: the as-built challenge adjudicated at HEAD)`.

**DERIVATION:** `[RECORD]` of a two-stage certification: a challenge run (C1) and an adjudication run (E1) by the same model in fresh contexts.

**CONDITIONALITY:** **this is the note's SECOND text freeze** (FREEZE-1a) and the boundary above which nothing is edited. The 1C/2G/2M challenge landed on a note already ACCEPTED at 2/2 by nine hostile passes — the decorrelation is the point, and the outcome (two REAL repairs to displayed statements, one genuine obstruction) is the shard's strongest evidence for the decorrelated-audit discipline.

**RESOLUTION TRACE:** statement lines 1487–1497.

**TEETH:** both run logs verified to exist: `runs/cert/C1_liftcorner_output.log`, `runs/cert2/E1_liftcorner_output.log`. ARITHMETIC AUDIT: 1 CRITICAL + 2 GAP + 2 MINOR = 5 findings; the adjudication dispositions listed are 1 OBSTRUCTED + 1 RESOLVED-ALREADY + 2 REAL + 1 ARTIFACT = **5** ✓, and all five are emitted below (`.94`–`.100`).

---

### EFF.LIFTCORNER.94  [supplier-finding]  `[TRANSCRIBED — certifier]`

**CANONICAL STATEMENT:**

> “1. OBSTRUCTED — PROP’s higher-rung conclusion is unsupported
>
> The finding stands. TAIL-STAB and READ-EQ prove the level-2 comparison, but nothing in the note proves that ITERLAWN’s rung-\(\ge2\) construction is insensitive to the non-leading coefficients of \(\Phi_1\). The note expressly admits this in `[r4, F4-4]`:
>
> > “an argument this note does not make, and which neither the two formerly cited tables nor ITERLAWN's own r4 erratum supplies”
>
> Thus PROP, S5’s all-\(n\) rider, and FC-2 outrun the proved chain. The missing lemma cannot be derived from the note’s own lemmas because WELL-DEF-\((n)\), the \(C_k\) construction, and the degree telescope are not defined here.”

**FORM:** numbered finding with an embedded quotation of the note.

**DERIVATION:** the certifier's own reading, warranted by the note's own admission (quoted).

**CONDITIONALITY:** SUPERSESSION KIND (as applied to PROP): **scope-pin**. Narrowed by AC-4, discharged by AC-5 (CHAIN-P).

**RESOLUTION TRACE:** statement lines 1499–1505; the quoted admission at shard 1 `.64` (lines 1064–1066).

**TEETH:** the quoted admission is verified verbatim in the note at count 1. Designations `WELL-DEF-(n)`, `C_k`, “degree telescope” all resolve in ITERLAWN — XREF Y08 (`WELL-DEF` count 32), Y09 (`### S4.2 L6-(n) (ANCHOR-VAL = the ε-chain; all n, no engine, no DCX)` count 1, the telescope's home). Disposition `AUDIT / decorrelated-model audit`.

---

### EFF.LIFTCORNER.95  [lemma-statement + scope-pin]  `[TRANSCRIBED — certifier]`  *(SERIES CERTIFIER-ARC, link 1; CHAIN-P link 2)*

**CANONICAL STATEMENT:**

> “> **[ANNEX 2026-08-12, certifier AC-1 — PROP’S RUNG-\(\ge2\) CENSUS REMAINS OPEN.]** The all-rung force of three earlier sentences is SUSPENDED: PROP’s “the discharge lifts to every rung”, S5’s “ITER-LAW-\(n\) holds for EVERY lawful monic \(\Phi_1\), every \(n\)”, and FC-2’s execution of that rider rewrite. TAIL-STAB, READ-EQ, the THEOREM, COR 1 and COR 2 remain accepted exactly at their displayed 2-read / harness-\(\Phi_1\)-orbit scope.
> >
> > The missing statement is:
> >
> > **\((\Phi_1\)-OPACITY).** Let \(\Phi_1'\) and \(\Phi_1''\) be lawful monic level-1 keys with the same degree, \(w_1\)-value and accepted level-1 base package. For every rung \(n\ge2\), every use of \(\Phi_1\) in ITERLAWN S4.1/WELL-DEF-\((n)\), the \(C_k\)-existence construction and the S4.2 degree telescope factors through monicity, degree, \(w_1\Phi_1\), and the accepted level-1 package; equivalently, replacing \(\Phi_1''\) by \(\Phi_1'\) leaves every rung-\(\ge2\) proof datum and conclusion invariant after the formal identification \((\Phi_1'')^i\leftrightarrow(\Phi_1')^i\).
> >
> > This lemma is NOT proved by the present note. TAIL-STAB and READ-EQ control level-2 developments and reads; they contain no definitions of WELL-DEF-\((n)\), the higher \(C_k\), or the degree telescope from which \((\Phi_1\)-OPACITY) could be derived. The existing facts that the two keys share monicity, degree, \(w_1\), and the level-1 package do not logically exclude a higher-rung operation from inspecting a non-leading coefficient. Consequently the all-rung repair is **OBSTRUCTED pending a proof of \((\Phi_1\)-OPACITY)**. Until then, PROP and the executed S5/FC-2 rider are conditional on that lemma and carry no accepted conclusion.”

**FORM:** dated ANNEX blockquote carrying a bold-headed lemma statement.

**DERIVATION:** the obstruction argument: sharing monicity/degree/w₁/level-1 package does not logically exclude a coefficient read.

**CONDITIONALITY:** **AC-4 later shows the STATED lemma is the WRONG statement for the (RM-1) site** — “Equality of complete \(R,Q\) proof data should not be required and is generally the wrong statement” (AC-5). So AC-1's (Φ₁-OPACITY) as displayed is never proved; what is proved is the constructor/telescope half (AC-4) plus the weaker interface lemma (AC-5). A consumer must NOT cite “(Φ₁-OPACITY) proved”. SUPERSESSION KIND: **scope-pin**, superseded in turn by AC-4's narrowing and AC-5's discharge.

**RESOLUTION TRACE:** statement lines 1509–1515; narrowing at 1813–1815; discharge at 2068–2070.

**TEETH:** ITERLAWN designations verified: `### S4.1 Lemmas REALIZE-(m), WELL-DEF-(n), READ-ADD-(m)` count 1 line 499 (Y11); `### S4.2 L6-(n) …` count 1 line 575 (Y09). Disposition `AUDIT / decorrelated-model audit`.

---

### EFF.LIFTCORNER.96  [preregistration]  `[TRANSCRIBED — certifier]`

**CANONICAL STATEMENT:**

> “> **PRE-PROOF NUMERICAL CERTIFICATE.** Use, without sampling, the 56 S3 orbit towers—48 twisted towers and 8 \(\xi=1\) dense controls—each paired with its same-residue standard lift \(\Phi''\), plus the exact PE1 counter-instance and its standard-lift mate. Run every pair through rungs \(n\in\{2,3,4,5\}\). At each of ITERLAWN S7’s 22 dependency sites record the branch decisions, degrees, valuations, residual coefficients, \(C_k\), telescope terms, and final read/cocycle data. Normalize each polynomial datum to formal \(\Phi_1\)-adic coordinates by replacing \(\Phi_1^i\) with a common symbol \(U^i\) and identifying the shared coefficient fields. The required predicate is equality of the complete normalized records for \(\Phi_1'\) and \(\Phi_1''\), together with an access trace showing that no non-leading coefficient of \(\Phi_1\) reaches a branch condition, valuation, residual coefficient, \(C_k\), telescope bound, or final read except through the opaque formal-power node \(\Phi_1^i\). Required verdict: zero normalized mismatches and zero forbidden coefficient accesses on all 57 tower pairs, all four tested rungs, and all 22 sites. This is an instance certificate only; the universal conclusion still requires a source-level proof of \((\Phi_1\)-OPACITY).”

**FORM:** bold-headed preregistration inside the AC-1 annex.

**DERIVATION:** `[PREREGISTERED]` — a falsifier specified before any run, with an explicit required verdict.

**CONDITIONALITY:** **NEVER EXECUTED, and superseded as unnecessary.** No artifact in `verification/openmath/` corresponds to it (verified: no file matching `*opacity*` or `*rm1*` exists there), and AC-5 discharged the residual by proof instead. Two of its design premises were also superseded: the “22 dependency sites” universe is replaced by AC-4's 194-hit machine census, and the “equality of the complete normalized records” predicate is exactly what AC-5 says is “generally the wrong statement”. Disposition **`preregistration, superseded-unexecuted`**.

**RESOLUTION TRACE:** statement line 1517; supersession at 1620 (census) and 2017–2024 (predicate).

**TEETH:** ARITHMETIC AUDIT: “57 tower pairs” = 56 orbit towers + the PE1 counter-instance ✓ (consistent with shard 1 `.21`'s independently recomputed 56). “22 sites” matches ITERLAWN S7's 22 data rows, independently recounted (XREF Y12, 24 pipe-lines − header − separator = 22) — so the certificate's design was correctly pinned even though its universe was later widened.

---

### EFF.LIFTCORNER.97  [supplier-finding — rebuttal]  `[TRANSCRIBED — certifier]`

**CANONICAL STATEMENT:**

> “2. RESOLVED-ALREADY — the broader “at any level” reading remains fenced
>
> The finding conflates changing \(\Phi_1\) and propagating that fixed choice through canonical higher rungs with independently choosing a noncanonical \(\Phi_{m+1}\) at a deeper level.
>
> The exact cure is already in `[r4, F4-6]` … The acceptance record accepts “this note’s theorems **as fenced**.” FC-1 is explicitly a correction only of “the W-2 cap”; it changes the supplier grade from \(0/2\) to accepted and does not erase the `[r4, F4-6]` scope fence. Therefore the noncanonical-\(\Phi_2\) counter-configuration was already excluded from the discharged scope.
>
> This does not cure finding 1: propagation of a changed \(\Phi_1\) through canonical higher rungs still needs \((\Phi_1\)-OPACITY).”

**FORM:** numbered finding (rebuttal) quoting `.75` and `.76`.

**DERIVATION:** a scope distinction (changing Φ₁ vs independently choosing a noncanonical Φ_{m+1}) plus a reading of FC-1's scope.

**CONDITIONALITY:** **this unit constrains FC-1's reach and should be read alongside `.91`**: FC-1 is a counter re-reading of the W-2 cap ONLY and erases no scope fence. Nothing here changes; the finding is rebutted.

**RESOLUTION TRACE:** statement lines 1519–1533.

**TEETH:** the two quoted `[r4, F4-6]` sentences are verified verbatim in `.75` and `.76`. Disposition `AUDIT / decorrelated-model audit, rebutted at source`.

---

### EFF.LIFTCORNER.98  [lemma]  `[TRANSCRIBED — certifier]`  *(supersedes shard 1 `.34`)*

**CANONICAL STATEMENT:** finding 3's diagnosis and the replacement lemma, verbatim:

> “3. REAL — CONTENT must be displayed at its integral-key scope
>
> The displayed wording “For monic \(\Phi\)” is literally too broad. The proof uses integrality of every coefficient of \(\Phi\), not merely monicity.”

> “> **[ANNEX 2026-08-12, certifier AC-2 — CONTENT RE-DISPLAYED AT ITS PROVED-AND-CONSUMED SCOPE.]** The S4 CONTENT display
> >
> > “For monic \(\Phi\), the digits of \(\operatorname{dev}(F,\Phi)\) satisfy \(w_0\)-content \(\ge w_0\)-content\((F)\)”
> >
> > is SUPERSEDED by:
> >
> > **CONTENT (integral-key form).** Let \(\Phi\in\mathcal O[x]\) be monic and \(F\in\mathcal O[x]\). Every coefficient of every digit of \(\operatorname{dev}(F,\Phi)\) has valuation at least \(w_0\text{-content}(F)\).”

**FORM:** numbered finding + dated ANNEX carrying a bold-headed replacement lemma.

**DERIVATION:** transcribed verbatim:

> “> *Proof.* Put \(c=w_0\text{-content}(F)\). During monic long division, assume every coefficient of the current dividend has valuation at least \(c\). Its leading coefficient \(\lambda\) then has \(w_0(\lambda)\ge c\). Because every coefficient of \(\Phi\) lies in \(\mathcal O\), every coefficient of \(\lambda x^i\Phi\) has valuation at least \(c\). Subtracting it preserves that lower bound by the ultrametric inequality. Thus both the quotient coefficients and the remainder coefficients have valuation at least \(c\). Repeating the same division on successive quotients produces the \(\Phi\)-adic development and preserves the bound at every digit. ∎”

**CONDITIONALITY:** SUPERSESSION KIND: **replacement**. **TARGETS:** `.34`. The consumer sweep (quoted at shard 1 `.34`) certifies that every consumer survives unchanged, and names the excluded counterexample: “The counterexample \(\Phi=x+p^{-1}\) is excluded precisely because \(\Phi\notin\mathcal O[x]\).”

**RESOLUTION TRACE:** statement lines 1535–1552.

**TEETH:** ORCHESTRATOR VERIFICATION quoted at `.101` re-checked the division proof independently. Compile-time check of the counterexample: for Φ = x + p⁻¹ and F = 1·x (content 0), dev gives digits involving p⁻¹, so the frozen “for monic Φ” statement is indeed false as displayed and the integrality hypothesis is load-bearing ✓. Disposition `AUDIT / decorrelated-model audit`.

---

### EFF.LIFTCORNER.99  [derivation]  `[TRANSCRIBED — certifier]`  *(supersedes shard 1 `.55`)*

**CANONICAL STATEMENT:** finding 4's diagnosis and the replacement clause, verbatim:

> “4. REAL — correct the degree comparison in READ-EQ
>
> The literal \(e_0<\deg\Phi'\) fails when \(d_0=1\). The consumed inequality is the degree of the coefficient against the key degree.”

> “> **[ANNEX 2026-08-12, certifier AC-3 — READ-EQ DEGREE CORRECTION.]** In S4.2(a), the clause
> >
> > “with \(s<e_0<\deg\)”
> >
> > is SUPERSEDED by:
> >
> > “with \(s<e_0\); since \(\deg\Phi_0=d_0\) and
> > \(\deg\Phi'=\deg\Phi''=e_0d_0\),
> > \[
> > \deg(\Phi_0^s)=sd_0<e_0d_0=\deg\Phi'=\deg\Phi'',
> > \]
> > so \(\pi^u\Phi_0^s\) is a single key-slot coefficient and the key power is never opened.”
> >
> > **Consumer sweep.** This is exactly the inequality consumed by the anchor and \(\delta_1=0\) parts of READ-EQ. It holds also at \(d_0=1\), where \(\deg\Phi'=e_0\) but \(s<e_0\). The separate \(\delta_1=1\) one-overflow argument is untouched. Therefore READ-EQ, the THEOREM, COR 1 and COR 2 survive unchanged.”

**FORM:** numbered finding + dated ANNEX carrying a replacement clause with a display.

**DERIVATION:** the corrected comparison is between degrees, not between an integer and a degree.

**CONDITIONALITY:** SUPERSESSION KIND: **replacement**. **TARGETS:** `.55` only.

**RESOLUTION TRACE:** statement lines 1554–1573.

**TEETH:** ARITHMETIC AUDIT: at d₀ = 1, deg Φ′ = e₀·1 = e₀, so the frozen “e₀ < deg Φ′” reads e₀ < e₀, false ✓; the corrected form gives s·1 < e₀·1, true for s < e₀ ✓. Disposition `AUDIT / decorrelated-model audit`.

---

### EFF.LIFTCORNER.100  [supplier-finding — rebuttal]  `[TRANSCRIBED — certifier]`

**CANONICAL STATEMENT:**

> “5. ARTIFACT — “bit-exactly modulo timing fields” does not claim raw-file identity
>
> The quoted PE9 sentence is not part of the note at HEAD. Moreover, its parenthetical explicitly states the equivalence relation: equality after removing disclosed wall-clock fields.
>
> That is consistent with the note’s corrections:
>
> - `[r3, F-C]`: “identical line-for-line **modulo the `elapsed`/per-block timestamp fields only**”
> - `[r4, F4-3]`: the runner output is “**identical modulo timing fields, not bit-identical**”
> - `[r4]` machine record: the raw output differs at wall-clock lines, while timing normalization gives an empty diff.
>
> The acceptance record itself calls the runner bytes “byte-frozen” and separately calls the children table reproducible; it never asserts that the raw timed runner output is byte-identical. No repair is needed.”

**FORM:** numbered finding (rebuttal) with a three-item citation list.

**DERIVATION:** three in-note citations plus a reading of the acceptance record's own wording.

**CONDITIONALITY:** none — the finding is rebutted and nothing changes. **The rebuttal vindicates CHAIN-B** (shard 1 `.10`): the note's three-round correction of “bit-identically” is exactly what makes the challenge answerable from the text.

**RESOLUTION TRACE:** statement lines 1575–1585.

**TEETH:** the three cited in-note corrections verified at their lines (102–114, 115–131, 32–41). Disposition `AUDIT / decorrelated-model audit, rebutted at source`.

---

### EFF.LIFTCORNER.101  [instrument-record]

**CANONICAL STATEMENT:**

> “*(The adjudication above was produced by the E1 certification run
> (gpt-5.6-sol high, runs/cert2/E1_liftcorner_output.log, 2026-08-12);
> orchestrator verification before transcription — AC-2's division
> proof re-checked (integral Φ keeps every λx^iΦ coefficient at
> valuation ≥ c; ultrametric subtraction preserves the bound; the
> C1 counterexample Φ = x + p^{−1} is excluded by Φ ∉ O[x], and every
> consumer site is in O[x]); AC-3's inequality re-checked
> (s·d₀ < e₀·d₀ = deg Φ′, valid at d₀ = 1 where the sealed e₀ < deg
> failed); the RESOLVED-ALREADY and ARTIFACT rebuttals checked against
> the note's own [r4, F4-6] fence and [r3, F-C]/[r4, F4-3] lines at
> HEAD; AC-1's containment matches the note's own [r4, F4-4] admission,
> and the (Φ₁-OPACITY) statement + 57-pair certificate spec are
> recorded as the proof unit. Transcribed unaltered per the standing
> division of labor. Ledger: row 19 → AC-2/AC-3 folded; OPEN pending
> (Φ₁-OPACITY) + discharge.)*”

**FORM:** italic parenthetical.

**DERIVATION:** `[RECORD]` of an independent pre-transcription check — a SECOND warrant, distinct from the certifier's own.

**CONDITIONALITY:** the ledger line “row 19 → AC-2/AC-3 folded; OPEN pending (Φ₁-OPACITY) + discharge” is superseded by `.109` and `.118`, which carry row 19 forward to “the (Φ₁-OPACITY) program is complete … transcription-confirm owed”.

**RESOLUTION TRACE:** statement lines 1587–1601.

**TEETH:** XREF Y13 — `docs/PROJECT_STATE.md` carries the row-19 tracking at count 1: `row 19 also ((Φ₁-OPACITY), numerical certificate` (line 3996). Disposition `accepted-with-decorrelation-supplied`: the orchestrator's re-derivations are independent of the certifier's.

---

### EFF.LIFTCORNER.102  [record]

**CANONICAL STATEMENT:**

> “The P3 certification run (gpt-5.6-sol high,
> runs/cert4/P3_opacity_output.log) adjudicated (Φ₁-OPACITY) directly
> against ITERLAWN's r6 census of record (194 mapped hits): the
> constructor/telescope subgraph is PROVED opaque (the Θ-transport
> sublemma below), and the obstruction survives at exactly one site —
> ITERLAWN S4.6's (RM-1) reduction, which divides by Φ₁ and reads its
> non-leading coefficients. The residual obligation is the (RM-1)
> INTERFACE LEMMA named inside the annex (the four consumed interface
> clauses survive the key swap; full R,Q proof-data equality is the
> wrong statement). Transcribed unaltered:”

**FORM:** paragraph preamble under `### Dated source adjudication (2026-08-12 — sol certification P3: (Φ₁-OPACITY) narrowed to the (RM-1) interface)`.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** none; superseded in outcome by P4 (`.110`–`.117`), which proves the named residual.

**RESOLUTION TRACE:** statement lines 1607–1616.

**TEETH:** `runs/cert4/P3_opacity_output.log` exists. The “194 mapped hits” figure is verified against ITERLAWN's own machine-census bracket (XREF Y14, count 1, line 1233).

---

### EFF.LIFTCORNER.103  [table + scope record]  `[TRANSCRIBED — certifier]`  *(SERIES CERTIFIER-ARC, link 2; CHAIN-P link 3)*

**CANONICAL STATEMENT:** AC-4's census partition and its reduction to five source-operation classes, verbatim:

> “> This adjudication uses ITERLAWN’s machine census of record, not the superseded 22-row or 23-row hand tables. The r6 universe is **194 mapped hits on 147 lines**, partitioned as follows:
> >
> > 1. **88** table-row occurrences, duplicates and dated cure-brackets;
> > 2. **21** occurrences in the seven substantive site-families \(F1\)–\(F7\);
> > 3. **53** verification-apparatus occurrences;
> > 4. **8** quotations of external records;
> > 5. **18** non-genre occurrences;
> > 6. **6** positive proof displays.
> >
> > The apparatus, quotation, archive and duplicate classes perform no polynomial operation and therefore cannot inspect a coefficient of \(\Phi _1\). The operative occurrences in the remaining classes reduce to five source-operation classes:
> >
> > * shared numerical and field data: \(e_j,h_j,g_j,\gamma_j,w_j\Phi_j,\psi_j,K_j,z_j,\epsilon_j\);
> > * the recursive realizers \(\operatorname{realize}_m\);
> > * the \(C_k\)-existence and canonical-key construction;
> > * TRUNC, WELL-DEF and the S4.2 degree telescope;
> > * the S4.6 reduction engines \((RM\text{-}m)\).
> >
> > The first four classes are \(\Phi _1\)-opaque in the required formal-power sense. The fifth is not shown opaque and, at \(m=1\), genuinely opens \(\Phi _1\).”

`[TABLE]` — the partition, transcribed:

| class | count | opaque? |
|---|---:|---|
| 1. table rows / duplicates / cure-brackets | 88 | n/a (no polynomial operation) |
| 2. seven substantive site-families F1–F7 | 21 | reduces to the five operation classes |
| 3. verification apparatus | 53 | n/a |
| 4. quotations of external records | 8 | n/a |
| 5. non-genre | 18 | n/a |
| 6. positive proof displays | 6 | reduces to the five operation classes |
| **total** | **194** | |

**FORM:** blockquote with a numbered partition and a bulleted class list.

**DERIVATION:** `[IMPORTED]` — the partition is ITERLAWN's own machine census, re-used as the adjudication universe.

**CONDITIONALITY:** SUPERSESSION KIND: **scope-pin** — it retires the 22-row hand table as the census of record (targeting shard 1 `.64`).

**RESOLUTION TRACE:** statement lines 1620–1637.

**TEETH:** **MANDATORY ARITHMETIC AUDIT (v3 rule 22), computed fresh: 88 + 21 + 53 + 8 + 18 + 6 = 194** ✓, and the total matches the stated universe. **Cross-checked against the source**: ITERLAWN's own bracket (Y14, line 1233) reads “194 raw hits on 147 lines, 194/194 mapped, ZERO unadjudicated (88 at table-row sites/duplicates/cure-brackets; 21 at the seven site-families F1–F7, ALL content-true, each re-derived; 53 verification-apparatus; 8 quoted external record; 18 non-genre; 6 positive displays)” — **every one of the six class counts and both totals (194 hits, 147 lines) match AC-4's transcription exactly.** This is the strongest cross-note figure verification in either shard.

---

### EFF.LIFTCORNER.104  [lemma]  `[TRANSCRIBED — certifier]`

**CANONICAL STATEMENT:**

> “> **Proved sublemma — constructor/telescope opacity.** Let \(\Phi _1'\) and \(\Phi _1''\) be lawful monic level-1 keys having the same residue package, degree, \(w_1\)-value and accepted level-1 data. Fix all remaining tower parameters. In every displayed construction in ITERLAWN S4.1 and S4.2, transport an explicitly displayed \(\Phi _1''\)-normal form by
> > \[
> > \Theta\!\left(\sum_i A_i(\Phi _1'')^i\right)
> >   :=\sum_i\Theta(A_i)(\Phi _1')^i,
> > \]
> > recursively replacing each constructed higher key by its corresponding primed key. Then:
> >
> > 1. \(\Theta(\operatorname{realize}_m''(\tau,\beta))
> >    =\operatorname{realize}_m'(\tau,\beta)\);
> > 2. \(\Theta(C_k'')=C_k'\) for every canonical-lift coefficient;
> > 3. \(\Theta(\Phi _{m+1}'')=\Phi _{m+1}'\);
> > 4. all degree, weight and explicitly constructed single-digit read data in REALIZE-\((m)\), WELL-DEF-\((n)\), TRUNC and L6-\((n)\) agree;
> > 5. the S4.2 degree telescope is identical on the two sides.
> >
> > Here \(\Theta\) is asserted only on the normal forms supplied by the displayed constructions. It is not asserted to commute with arbitrary division or re-development in \(\mathcal O[x]\).”

**FORM:** bold-headed display lemma with a numbered five-clause conclusion.

**DERIVATION:** `.105`.

**CONDITIONALITY:** **the last sentence is the load-bearing fence and must travel with the lemma**: Θ is asserted only on displayed normal forms, NOT as commuting with arbitrary division. That fence is precisely why the (RM-1) division survives as an obstruction (`.106`).

**RESOLUTION TRACE:** statement lines 1639–1653; proof 1655–1729.

**TEETH:** designations verified in ITERLAWN: `### S4.1 Lemmas REALIZE-(m), WELL-DEF-(n), READ-ADD-(m)` (Y11, count 1); `### S4.2 L6-(n) …` (Y09, count 1); `TRUNC` count 14; `WELL-DEF` count 32; `realize_m(τ, β)` count 1.

---

### EFF.LIFTCORNER.105  [derivation]  `[TRANSCRIBED — certifier]`

**CANONICAL STATEMENT:** AC-4's proof of `.104`, source lines 1655–1729, `[ASSEMBLED]` from its five stages (each quoted verbatim below in the DERIVATION field rather than duplicated here).

**FORM:** italic-headed proof with five stages and three displays.

**DERIVATION:** induction on m, in five stages.
- **Base m = 1:** “the displayed formula \(\operatorname{realize}_1(\tau,\beta) =\sum_i \operatorname{realize}_0\!\left( \epsilon_0(\gamma^{(i)})^{-1}\tau_i,\gamma^{(i)} \right)\Phi_0^{k_i}\) contains no \(\Phi _1\). Its coordinates \(\tau_i\), slots \(k_i\), weights \(\gamma^{(i)}\), field operations and \(\epsilon\)-factors are shared. Hence the two realizers are literally equal at this level.”
- **Step:** the level-m realizer's inputs “depend only on the shared field/read package. By induction the coefficients correspond, and the final occurrence of \(\Phi_{m-1}\) is an opaque formal power.”
- **REALIZE clauses:** “Clauses (R2) and (R3) use the already displayed sum as its \(\Phi_{m-1}\)-development: the coefficient-degree bound makes every summand a single legal digit, and distinct \(i\) give distinct slots. Thus no coefficient of \(\Phi_{m-1}\), and hence no non-leading coefficient of \(\Phi _1\), is opened.”
- **C_k and the canonical key:** “Its field input, weight and \(\epsilon_m\)-factor are shared, so the realizer induction gives \(\Theta(C_k'')=C_k'\) … Monicity comes from the top term \(\Phi_m^{e_mg_m}\); every lower term has smaller degree by (R1).”
- **TRUNC and the telescope:** “TRUNC merely discards the top level. On the two towers “identical lifts” must be read as “corresponding lifts under \(\Theta\)”… Finally, S4.2 uses only \(\deg a=\sum_{j<n}s_{j+1}\deg\Phi_j \le\sum_{j<n}(\deg\Phi_{j+1}-\deg\Phi_j) =\deg\Phi_n-d_0<\deg\Phi_n\). … It establishes that \(a\) is a single \(\Phi_n\)-digit without opening \(\Phi_n\). ∎”

**CONDITIONALITY:** every stage turns on the same mechanism — the key appears only as a formal power, never as a divisor. The proof does not and cannot cover a step that divides by the key; that is `.106`.

**RESOLUTION TRACE:** proof lines 1655–1729.

**TEETH:** ARITHMETIC AUDIT of the telescope inequality, recomputed: Σ_{j<n} s_{j+1}·deg Φ_j ≤ Σ_{j<n}(deg Φ_{j+1} − deg Φ_j) telescopes to deg Φ_n − deg Φ_0 = deg Φ_n − d₀ < deg Φ_n ✓. The step uses s_{j+1}·deg Φ_j ≤ deg Φ_{j+1} − deg Φ_j, i.e. (s_{j+1}+1)·deg Φ_j ≤ deg Φ_{j+1}, which holds under the class's degree recursion deg Φ_{j+1} = e_j g_j deg Φ_j with s_{j+1} ≤ e_j g_j − 1 — the same bound (R1) uses. ✓ Disposition `derivation, transcribed; arithmetic verified`.

---

### EFF.LIFTCORNER.106  [supplier-finding]  `[TRANSCRIBED — certifier]`

**CANONICAL STATEMENT:**

> “> **Exact obstruction to the stated all-rung lemma.** ITERLAWN S4.6 contains
> > the load-bearing display
> > \[
> > f\,\widehat C_m=R+Q\Phi_m,\qquad
> > \deg R,\deg Q<\deg\Phi_m,
> > \]
> > with weight bounds and a prescribed read of \(R\). At \(m=1\) this is
> > \[
> > \boxed{\,f\,\widehat C_1=R+Q\Phi_1\,}.
> > \]
> > Its displayed proof status is:
> >
> > > “\(m=1\): PROVED — [IL3] DIGIT-SPLIT + DEV-1 … each coefficient product
> > > splits by DIGIT-SPLIT and reduces by DEV-1.”
> >
> > This reduction genuinely inspects the non-leading coefficients of
> > \(\Phi _1\). In ordinary long division, cancelling a leading term
> > \(\lambda x^t\) subtracts \(\lambda x^{t-d}\Phi _1\); for every \(r<d\)
> > it therefore reads \([x^r]\Phi _1\) … Algebraically, if
> > \(\Delta=\Phi _1'-\Phi _1''\) and
> > \(F=R''+Q''\Phi _1''\), then
> > \[
> > F=(R''-Q''\Delta)+Q''\Phi _1'.
> > \]
> > Thus the new remainder already contains the non-leading coefficients of
> > \(\Delta\); if its degree is too large, further reductions read them
> > again. Same residue and same \(w_1\)-value can make these new terms
> > strictly above a relevant read line, but do not make them zero and do not
> > make the complete \(R,Q\) data invariant. Formal replacement
> > \((\Phi _1'')^i\leftrightarrow(\Phi _1')^i\) does not remove this
> > difference because \(R\) is a coefficient—the \(U^0\) digit—rather than
> > an opaque key power.”

**FORM:** bold-headed obstruction with two displays and a nested source quotation.

**DERIVATION:** the algebraic identity F = (R″ − Q″Δ) + Q″Φ₁′ exhibits the difference explicitly.

**CONDITIONALITY:** this is the surviving obstruction after `.104`. It is what AC-5 discharges — not by removing the coefficient reading (“coefficient-reading by division is real”, AC-5's closing sentence) but by showing its effect lies strictly above every consumed interface line.

**RESOLUTION TRACE:** statement lines 1731–1771; the discharge at 2068–2070.

**TEETH:** the quoted ITERLAWN status is verified **verbatim at count 1** — XREF Y15: `m = 1: PROVED — [IL3] DIGIT-SPLIT + DEV-1` (ITERLAWN line 794, inside the boxed (RM-m) display at S4.6, Y16 count 1 line 777). ARITHMETIC AUDIT of the identity: R″ + Q″Φ₁″ = R″ + Q″(Φ₁′ − Δ) = (R″ − Q″Δ) + Q″Φ₁′ ✓.

---

### EFF.LIFTCORNER.107  [lemma-statement]  `[TRANSCRIBED — certifier]`

**CANONICAL STATEMENT:**

> “> **\((RM\text{-}1\text{-TRANSPORT})\).** Under replacement by a lawful
> > same-residue \(\Phi _1\), the four *consumed interface clauses* of
> > \(RM\)-1—degree bounds, the two weight bounds and the prescribed read of
> > \(R\)—survive for every input class used in constructing ITER-PKG-2.”

with its framing, verbatim:

> “> LIFTCORNER’s TAIL-STAB makes an \(RM\)-interface transport plausible:
> > strict-excess terms may be invisible to the particular consumed weight
> > and read clauses. No displayed argument, however, proves that statement
> > for every \(RM\)-1 input \(f\), and TAIL-STAB does not make the complete
> > quotient/remainder records equal. The missing repair is therefore a
> > weaker and accurately scoped lemma”

and the closing scope instruction:

> “> Proving this interface lemma, followed by the S4.4–S4.6 rung-2 package
> > construction, could discharge the all-rung rider. Equality of complete
> > \(R,Q\) proof data should not be required and is generally the wrong
> > statement.”

**FORM:** bold-headed display lemma statement (the named residual obligation).

**DERIVATION:** `[STATED]` here; PROVED at `.111`–`.115`.

**CONDITIONALITY:** **this statement REPLACES AC-1's (Φ₁-OPACITY) as the thing to prove.** SUPERSESSION KIND: **replacement** of a proof obligation. A consumer citing “(Φ₁-OPACITY) was proved” would be wrong on two counts: the constructor half was proved as a different lemma (`.104`), and the (RM-1) half was proved as this weaker one.

**RESOLUTION TRACE:** statement lines 1787–1795; proof at 1833–2024.

**TEETH:** `ITER-PKG-2` verified at count 1 in ITERLAWN (Y17). **Scope note carried forward:** ITERLAWN's own ledger row for the package reads “the induction package (ITER-PKG-r) | STATED; base r = 1 ACCEPTED, r = 2 = [IL3] 0/2” (line 279) — so ITER-PKG-2 itself rides [IL3] at grade 0/2. AC-5 constructs it for arbitrary same-residue Φ₁′ *on ITERLAWN's own proved perimeter*, and inherits that grade.

---

### EFF.LIFTCORNER.108  [scope record]  `[TRANSCRIBED — certifier]`

**CANONICAL STATEMENT:** AC-4's consumer sweep, verbatim:

> “> **Consumer sweep.**
> >
> > * **LIFTCORNER PROP:** remains SUSPENDED. Constructor/telescope opacity
> >   repairs the S4.1 \(\to\) L6 edge but does not supply arbitrary-\(\Phi _1\)
> >   ITER-PKG-2 across \(RM\)-1.
> > * **LIFTCORNER S5:** its every-\(n\) rider remains conditional on the
> >   missing \(RM\)-1 transport/rung-2 package. TAIL-STAB, READ-EQ, the
> >   THEOREM, COR 1 and COR 2 retain their accepted 2-read scopes.
> > * **FC-2:** its execution of the all-rung rider remains SUSPENDED and must
> >   be read conditionally. The fold’s standard-lift ITERLAWN theorem and
> >   all unrelated accepted conclusions are unchanged.
> > * **ITERLAWN:** S4.1, WELL-DEF-\((n)\), canonical \(C_k\)-existence,
> >   TRUNC and L6-\((n)\) are certified \(\Phi _1\)-opaque in the formal
> >   constructor sense proved above. Its existing standard-lift theorem,
> >   integer layer, EXP-KIT and conditional \(RM\)-ledger are unaffected.
> >
> > Accordingly, AC-1 is narrowed but not discharged: its alleged opacity
> > problem is absent from the constructor/telescope subgraph and survives
> > exactly at the rung-2 \(RM\)-1 reduction interface.”

**FORM:** bold-headed bulleted sweep.

**DERIVATION:** `[RECORD]` of scope consequences.

**CONDITIONALITY:** **every one of the first three bullets is SUPERSEDED by AC-5's sweep** (`.117`), which lifts all three suspensions. The fourth bullet (the ITERLAWN certification) is NOT superseded — it stands and is strengthened. A consumer must read `.117`, not this unit, for PROP/S5/FC-2.

**RESOLUTION TRACE:** statement lines 1797–1815; supersession at 2053–2060.

**TEETH:** the fourth bullet's claim is a certification LANDED NOWHERE: `grep -cF 'OPACITY' ITERLAWN_PROOF_2026-08-08.md` = 0 (N1). ITERLAWN is certified Φ₁-opaque by an annex in another note that ITERLAWN does not reference. OPEN-CALL 1.

---

### EFF.LIFTCORNER.109  [instrument-record]

**CANONICAL STATEMENT:**

> “*(Orchestrator verification: the census partition sums to 194
> (88+21+53+8+18+6); the Θ-transport's five clauses ride the same
> block-unitriangular mechanisms verified at P1; the (RM-1) division
> genuinely opens Φ₁ (the m = 1 display f·Ĉ₁ = R + QΦ₁ is proved by
> DIGIT-SPLIT + DEV-1 reduction mod Φ₁ — coefficient-reading is real).
> AC-1 is NARROWED, not discharged. Ledger: row 19 → open on the
> (RM-1) interface lemma only (P4, next queue).)*”

**FORM:** italic parenthetical.

**DERIVATION:** `[RECORD]` of an independent pre-transcription check.

**CONDITIONALITY:** the ledger line is superseded by `.118`.

**RESOLUTION TRACE:** statement lines 1817–1823.

**TEETH:** the orchestrator's arithmetic check (88+21+53+8+18+6 = 194) is re-verified independently at `.103` and agrees. `runs/cert4/P3_opacity_output.log` exists.

---

### EFF.LIFTCORNER.110  [record]

**CANONICAL STATEMENT:**

> “The P4 certification run (gpt-5.6-sol high,
> runs/cert5/P4_rm1_output.log) PROVED the (RM-1) interface lemma AC-4
> demanded. Transcribed unaltered:”

**FORM:** paragraph preamble under `### Dated proof (2026-08-12 — sol certification P4: the (RM-1) interface lemma; AC-1/AC-4 discharged)`.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** none.

**RESOLUTION TRACE:** statement lines 1829–1831.

**TEETH:** `runs/cert5/P4_rm1_output.log` exists.

---

### EFF.LIFTCORNER.111  [lemma]  `[TRANSCRIBED — certifier]`  *(SERIES CERTIFIER-ARC, link 3; CHAIN-P — TERMINAL begins)*

**CANONICAL STATEMENT:** AC-5's setting and its first tagged result, verbatim:

> “> **[ANNEX 2026-08-12, certifier AC-5 — \((RM\text{-}1\text{-TRANSPORT})\) PROVED; THE \((\Phi _1)\)-OPACITY RESIDUAL IS DISCHARGED.]**
> >
> > Let \(\Phi _1'\) and \(\Phi _1''\) be lawful monic level-1 keys with the same residue package at \(g_0=1\). Put
> > \[
> > d:=\deg\Phi _1'=\deg\Phi _1''=e_0d_0,\qquad
> > W:=w_1\Phi _1'=w_1\Phi _1''=e_0h_0,
> > \]
> > and
> > \[
> > \Delta:=\Phi _1'-\Phi _1''.
> > \]
> > For a \(\Phi _0\)-development \(G=\sum_i a_i\Phi _0^i\), write
> > \[
> > \nu(G):=\min_i\{e_0w_0(a_i)+ih_0\}=w_1(G).
> > \]”

> “> **Strictness of the key difference.** … Same residue gives
> > \[
> > w_0(b_0'-b_0'')\ge h_0+1.
> > \]
> > For \(1\le k<e_0\), lawfulness and the ultrametric inequality give
> > \[
> > w_0(b_k'-b_k'')\ge
> > \operatorname{amin}(k)
> > =\left\lceil\frac{(e_0-k)h_0}{e_0}\right\rceil .
> > \]
> > Since \(\gcd(e_0,h_0)=1\), for \(1\le k<e_0\),
> > \[
> > e_0\operatorname{amin}(k)+kh_0\ge e_0h_0+1=W+1.
> > \]
> > The \(k=0\) term has weight at least
> > \(e_0(h_0+1)\ge W+1\). Therefore
> > \[
> > \boxed{\nu(\Delta)\ge W+1.}\tag{T1}
> > \]”

**FORM:** dated ANNEX with tagged displays — `\tag{T1}` is the first of the note's six `\tag{}` occurrences, all in this annex.

**DERIVATION:** the gcd argument, identical in mechanism to shard 1 `.42`'s rows 6–7 bound.

**CONDITIONALITY:** the setting is the LIFTCORNER corner (g₀ = 1) with the S1 lawfulness constraints; `amin(k)` is S1's own function (shard 1 `.18`).

**RESOLUTION TRACE:** statement lines 1833–1872.

**TEETH:** **MANDATORY ARITHMETIC AUDIT, recomputed:** since gcd(e₀,h₀) = 1 and 0 < k < e₀, e₀ ∤ (e₀−k)h₀, so ⌈(e₀−k)h₀/e₀⌉ ≥ ((e₀−k)h₀ + 1)/e₀, hence e₀·amin(k) ≥ (e₀−k)h₀ + 1 and e₀·amin(k) + kh₀ ≥ e₀h₀ + 1 = W + 1 ✓. For k = 0: weight ≥ e₀(h₀+1) = e₀h₀ + e₀ ≥ W + 1 since e₀ ≥ 1 ✓. (T1) is correct as displayed. **This is the same inequality LIFTCORNER's own `.114` derives**, re-used at a different level — a genuine reuse of the note's mathematics by its certifier.

---

### EFF.LIFTCORNER.112  [lemma]  `[TRANSCRIBED — certifier]`

**CANONICAL STATEMENT:**

> “> **Strict DEV-1 consequence.** Let \(K\) be any lawful key of the displayed form and let
> > \[
> > H=A+BK,\qquad \deg A,\deg B<d
> > \]
> > be its monic division. Then
> > \[
> > \boxed{\nu(A)\ge\nu(H),\qquad
> >        \nu(B)\ge\nu(H)-W.}\tag{T2}
> > \]”

**FORM:** bold-headed display lemma with `\tag{T2}`.

**DERIVATION:** the displayed DEV-1 reduction, run explicitly:

> “> Substitution of
> > \[
> > \Phi _0^{e_0}=K-\sum_{k<e_0}b_k\Phi _0^k
> > \]
> > emits a quotient term \(a\Phi _0^{m-e_0}\), whose weight is the parent
> > weight minus \(W\). Each lower coefficient product \(ab_k\) has degree
> > \(<2d_0\), so DIGIT-SPLIT gives
> > \[
> > ab_k=r+q\Phi _0,\qquad
> > w_0(r),w_0(q)\ge w_0(a)+w_0(b_k).
> > \]
> > Hence every resulting remainder child has weight at least its parent …
> > Collisions cannot lower
> > these bounds by the ultrametric inequality.”

with the termination argument:

> “> The reduction terminates on the same lexicographic
> > \((m,\deg a)\) measure used by LIFTCORNER’s repaired TAIL-STAB proof.
> > For \(e_0\ge2\), only the top-mid \(q\)-child can preserve \(m\), and then
> > its coefficient degree drops. At \(e_0=1\), the analogous \(b_0\)
> > \(q\)-child can preserve \(m\), but its coefficient degree likewise
> > drops. Thus the DEV-1 reduction is finite, including the flat case needed
> > for the strict-excess correction below. This proves (T2).”

**FORM:** display lemma + proof.

**DERIVATION:** as quoted — and note that it **reuses LIFTCORNER's own lex measure**, extending it to e₀ = 1, which LIFTCORNER's §S4 setting excluded.

**CONDITIONALITY:** **SCOPE TENSION, recorded not adjudicated.** ITERLAWN's own (RM-m) STATUS box fences the m = 1 engine: “SCOPE inherited from the DEV-1 erratum: proved for e₀ ≥ 2, and at e₀ = 1 ∧ d₀ = 1 (junkΦ ≡ 0); at {e₀ = 1 ∧ d₀ ≥ 2} general inputs enter [IL3]'s fenced DEV-1 corner — open there” (XREF Y18, verified verbatim). AC-5's termination paragraph asserts finiteness at e₀ = 1 by the lex measure, “including the flat case needed for the strict-excess correction below”. **Whether AC-5's argument closes ITERLAWN's fenced DEV-1 corner, or is confined to the strict-excess division it needs and leaves the corner open, is not decided by either text.** See OPEN-CALL 3. It does not affect LIFTCORNER's own corner (e₀ ≥ 2 by the S4 setting; δ₁ = 1 empty at e₀ = 1).

**RESOLUTION TRACE:** statement lines 1874–1911.

**TEETH:** the DIGIT-SPLIT bound is LIFTCORNER's CONTENT (`.34`, effective = AC-2's integral-key form); the lex measure is `.37`. ARITHMETIC AUDIT of the displayed child bound: e₀w₀(r) + (m−e₀+k)h₀ ≥ e₀(w₀(a)+w₀(b_k)) + (m−e₀+k)h₀, and with w₀(b_k) ≥ amin(k) satisfying e₀·amin(k) ≥ (e₀−k)h₀, this is ≥ e₀w₀(a) + (e₀−k)h₀ + (m−e₀+k)h₀ = e₀w₀(a) + mh₀ ✓, exactly as displayed.

---

### EFF.LIFTCORNER.113  [derivation]  `[TRANSCRIBED — certifier]`

**CANONICAL STATEMENT:**

> “> Now take any nonzero input \(f\) occurring in the construction of
> > ITER-PKG-2, with
> > \[
> > \deg f<d,\qquad
> > \lambda:=w_1(f),\qquad
> > v:=R_{1,\lambda}(f),\qquad
> > \mu:=\lambda+\gamma _2.
> > \]
> > No correspondence between complete primed and double-primed input
> > polynomials is required: apply the established \((RM\text{-}1)\) theorem
> > for \(\Phi _1''\) to this same literal polynomial \(f\). The quantities
> > \(\lambda\) and \(v\) are computed from its \(\Phi _0\)-development and
> > are therefore independent of which level-1 key is later used for
> > division.
> >
> > The correction digit is shared:
> > \[
> > \widehat C_1'
> > =\widehat C_1''
> > =\operatorname{realize}_1(\tau _1,\gamma _2).
> > \]
> > Indeed, AC-4’s \(m=1\) constructor calculation contains no \(\Phi _1\);
> > same residue makes \(z_1,\epsilon _1,\tau _1\) and all field inputs
> > identical.”

**FORM:** inline derivation with two displays.

**DERIVATION:** the key move — apply the ESTABLISHED (RM-1) theorem to the SAME literal polynomial f on the double-primed side, so no input correspondence is needed.

**CONDITIONALITY:** **this step CONSUMES ITERLAWN's (RM-1) theorem at its own scope**, which is the m = 1 engine fenced as in `.112`'s scope tension. The shared correction digit rides AC-4's `.105` base case.

**RESOLUTION TRACE:** statement lines 1913–1936.

**TEETH:** the (RM-1) interface's four consumed clauses are verified against ITERLAWN's boxed statement (Y16): the box displays `f·Ĉ_m = R + Q·Φ_m,   w_m(R) ≥ λ + γ_{m+1},   w_m(Q) ≥ λ + γ_{m+1} − w_mΦ_m   (Q = 0 allowed),   R_{m,λ+γ_{m+1}}(R) = z_m^{ε′}·v·τ_m` — **exactly the two degree bounds, two weight bounds and prescribed read that (RM-1-TRANSPORT) transports.** The correspondence is exact and was re-checked line by line at compile time.

---

### EFF.LIFTCORNER.114  [derivation]  `[TRANSCRIBED — certifier]`

**CANONICAL STATEMENT:** the swap computation, verbatim (source lines 1938–1984), carrying tags (T3)–(T6):

> “> The established \((RM\text{-}1)\) interface for \(\Phi _1''\) supplies
> > \[
> > f\widehat C_1=R''+Q''\Phi _1'',\qquad
> > \deg R'',\deg Q''<d,
> > \]
> > with
> > \[
> > w_1(R'')\ge\mu,\qquad
> > w_1(Q'')\ge\mu-W,
> > \]
> > and
> > \[
> > R_{1,\mu}(R'')=z_1^{\epsilon'}v\tau _1.
> > \tag{T3}
> > \]
> >
> > Put \(H:=Q''\Delta\). DIGIT-SPLIT’s product bound together with (T1)
> > and (T3) gives
> > \[
> > \nu(H)\ge\nu(Q'')+\nu(\Delta)
> > \ge(\mu-W)+(W+1)=\mu+1.
> > \tag{T4}
> > \]
> > Divide \(H\) by \(\Phi _1'\):
> > \[
> > Q''\Delta=A+B\Phi _1',\qquad \deg A,\deg B<d.
> > \]
> > Applying (T2) to (T4),
> > \[
> > w_1(A)\ge\mu+1,\qquad
> > w_1(B)\ge\mu+1-W.
> > \tag{T5}
> > \]
> >
> > Since \(\Phi _1''=\Phi _1'-\Delta\),
> > \[
> > \begin{aligned}
> > f\widehat C_1
> > &=R''+Q''\Phi _1''\\
> > &=R''-Q''\Delta+Q''\Phi _1'\\
> > &=(R''-A)+(Q''-B)\Phi _1'.
> > \end{aligned}
> > \]
> > Define
> > \[
> > \boxed{R':=R''-A,\qquad Q':=Q''-B.}\tag{T6}
> > \]”

**FORM:** tagged display chain (T3)–(T6).

**DERIVATION:** (T4) is the crux: the swap correction Q″Δ lands STRICTLY ABOVE the consumed line μ.

**CONDITIONALITY:** (T4) cites “DIGIT-SPLIT’s product bound together with (T1) and (T3)”. **The (T3) citation is doing no work in that inequality** — the bound needs ν(Q″) ≥ μ−W (a weight bound displayed just above (T3)) and ν(Δ) ≥ W+1 (T1); (T3) is the prescribed READ, used later at interface clause 4. Recorded as a citation looseness, not an error; the inequality is correct as computed below. See OPEN-CALL 6.

**RESOLUTION TRACE:** statement lines 1938–1984.

**TEETH:** **MANDATORY ARITHMETIC AUDIT, recomputed independently:**
- (T4): ν(Q″Δ) ≥ ν(Q″) + ν(Δ) ≥ (μ−W) + (W+1) = **μ+1** ✓.
- (T5): applying (T2) with ν(H) ≥ μ+1 gives ν(A) ≥ μ+1 and ν(B) ≥ (μ+1) − W ✓.
- (T6): R″ + Q″Φ₁″ = R″ + Q″(Φ₁′ − Δ) = (R″ − Q″Δ) + Q″Φ₁′ = (R″ − A − BΦ₁′) + Q″Φ₁′ = (R″ − A) + (Q″ − B)Φ₁′ ✓.
Every step reproduces exactly. **The whole discharge turns on (T4)'s single unit of strictness** — W+1 rather than W — which comes from (T1), which comes from the gcd(e₀,h₀) = 1 argument that LIFTCORNER's own `.42` (shard 1) uses. The provenance chain of the +1 is: S1's lawfulness bound → gcd argument → (T1) → (T4) → interface clause 4's strict-above kill.

---

### EFF.LIFTCORNER.115  [lemma]  `[TRANSCRIBED — certifier]`

**CANONICAL STATEMENT:** the four consumed interface clauses, verbatim:

> “> Then the four consumed interface clauses are:
> >
> > 1. **Degree bounds**
> >    \[
> >    \deg R',\deg Q'<d.
> >    \]
> >
> > 2. **Remainder-weight bound**
> >    \[
> >    w_1(R')\ge\min\{w_1(R''),w_1(A)\}\ge\mu.
> >    \]
> >
> > 3. **Quotient-weight bound**
> >    \[
> >    w_1(Q')\ge\min\{w_1(Q''),w_1(B)\}\ge\mu-W.
> >    \]
> >
> > 4. **Prescribed read of the remainder.** Since \(w_1(A)>\mu\),
> >    READ-ADD-\((1)\)’s strict-above kill gives
> >    \[
> >    R_{1,\mu}(R')
> >      =R_{1,\mu}(R''-A)
> >      =R_{1,\mu}(R'')
> >      =z_1^{\epsilon'}v\tau _1.
> >    \]
> >
> > Thus every \((RM\text{-}1)\) input class used in constructing
> > ITER-PKG-2 retains exactly the interface consumed by ITERLAWN S4.6.
> > The argument is uniform in \(f\); it does not require equality or a
> > preselected correspondence between the complete primed and
> > double-primed input records.”

**FORM:** numbered four-clause display list — the proof of `.107`.

**DERIVATION:** clauses 1–3 by the ultrametric on the differences of (T6); clause 4 by READ-ADD-(1)'s strict-above kill applied to w₁(A) ≥ μ+1 > μ.

**CONDITIONALITY:** **the uniformity claim is the whole point** — “The argument is uniform in \(f\)” answers AC-4's objection that no displayed argument covers every RM-1 input.

**RESOLUTION TRACE:** statement lines 1985–2015.

**TEETH:** **NEAR-MISS XREF (v3 rule 15)** — `READ-ADD-(1)` is absent from ITERLAWN as written (`grep -cF 'READ-ADD-(1)'` = 0); the verified referent is the schematic `READ-ADD-(m)`, at `ITERLAWN_PROOF_2026-08-08.md` line 499 (`### S4.1 Lemmas REALIZE-(m), WELL-DEF-(n), READ-ADD-(m)`, count 1) and line 564 (`**Lemma READ-ADD-(m) (read additivity with strict-above kill; generic).**`, count 1), whose title confirms the strict-above kill the clause invokes. Recorded as NEAR-MISS, not as a clean XREF and not suppressed. ARITHMETIC AUDIT: clauses 2 and 3 follow from (T5) and the displayed R″/Q″ bounds by the ultrametric ✓; clause 4 needs w₁(A) > μ, which (T5) gives as ≥ μ+1 ✓.

---

### EFF.LIFTCORNER.116  [fence]  `[TRANSCRIBED — certifier]`

**CANONICAL STATEMENT:**

> “> **Why full proof-data equality is false and unnecessary.** Equations
> > (T5)–(T6) explicitly give
> > \[
> > R'-R''=-A,\qquad Q'-Q''=-B.
> > \]
> > The strictly excessive polynomials \(A,B\) need not vanish. Therefore
> > complete equality of \(R,Q\) is neither proved nor claimed. What is
> > invariant is precisely their degree/weight/read interface.”

**FORM:** bold-headed fence with a display.

**DERIVATION:** direct from (T6).

**CONDITIONALITY:** **this fence retires AC-1's (Φ₁-OPACITY) as stated.** AC-1 asked for “every rung-\(\ge2\) proof datum and conclusion invariant”; this says that is false and unnecessary. A consumer must carry the interface-invariance statement, never the data-invariance one.

**RESOLUTION TRACE:** statement lines 2017–2024; the retired statement at 1513.

**TEETH:** disposition `signed non-applicability` — the stronger statement is checked *against* and explicitly declined.

---

### EFF.LIFTCORNER.117  [scope record]  `[TRANSCRIBED — certifier]`  *(CHAIN-P, CHAIN-F — TERMINAL)*

**CANONICAL STATEMENT:** AC-5's consumer sweep, verbatim:

> “> **Consumer sweep.**
> >
> > * **S4.4 CASE-SPLIT-\((2)\):** consumes the accepted ITER-PKG-1
> >   support, degree, weight and read package and makes no division by
> >   \(\Phi _1\). AC-4 and LIFTCORNER’s accepted level-1 comparison already
> >   transport those inputs.
> > * **S4.5 Case I:** makes no \((RM\text{-}1)\) call and is unchanged.
> > * **S4.6 Case II-1:** consumes the two degree bounds, both weight bounds
> >   and the prescribed \(R\)-read. All four are supplied above …
> > * **S4.6 Case II-2:** the \(E_0\)-call consumes all four clauses; the
> >   \(E_1\)-call consumes the degree and weight clauses only. Both calls
> >   survive. The off-DCX condition is evaluated using the quotient actually
> >   produced on the primed tower; no equality of \(Q'\) and \(Q''\), nor
> >   equality of their zero loci, is required.
> > * **S4.6 Case II-3:** consumes only the degree and weight clauses for the
> >   \(E_1\)-call. Its collision terms remain strictly above the prescribed
> >   line, so READ-ADD kills them exactly as before.
> > * Consequently S4.4–S4.6 construct **ITER-PKG-2 for every lawful
> >   same-residue \(\Phi _1'\)**, on ITERLAWN’s own proved perimeter and
> >   with its existing DCX/\((RM\text{-}m)\) conditionality unchanged.
> > * AC-4 then transports REALIZE, the \(C_k\), canonical higher keys,
> >   WELL-DEF, TRUNC, L6 and the degree telescope. From rung \(3\) onward
> >   ITERLAWN calls only \((RM\text{-}m)\) with \(m\ge2\); those retain
> >   exactly their pre-existing conditional ledger. Hence the induction
> >   climbs from the newly established arbitrary-\(\Phi _1\) ITER-PKG-2.
> > * **LIFTCORNER PROP:** its rung-\(\ge2\) suspension is lifted. The
> >   all-rung propagation now follows at ITERLAWN’s own conditionality.
> > * **LIFTCORNER S5:** the every-\(n\) rider on the \(\Phi _1\) axis is no
> >   longer conditional on \((\Phi _1\)-OPACITY). The fence excluding
> >   independently chosen noncanonical higher keys remains unchanged.
> > * **FC-2:** its executed rider rewrite is reinstated on the \(\Phi _1\)
> >   axis. This does not enlarge ITERLAWN’s DCX, higher-\((RM)\), T-scope or
> >   deeper-noncanonical-lift perimeter.
> > * For an arbitrary residue \(c'\), compare the lawful key with its
> >   same-residue standard mate. LIFTCORNER’s accepted theorem supplies
> >   that standard-mate base package, the present lemma supplies
> >   ITER-PKG-2, and AC-4 supplies the higher constructor/telescope
> >   transport. COR 2’s already fenced \(\chi\)-covariance statement is
> >   unchanged.
> >
> > Therefore AC-1’s final residual and AC-4’s unique obstruction are
> > discharged: coefficient-reading by division is real, but its effect is
> > strictly above every interface line consumed by the rung-2 construction.”

**FORM:** bold-headed bulleted sweep, ten bullets + a closing sentence.

**DERIVATION:** `[RECORD]` of scope consequences, each keyed to a named ITERLAWN section.

**CONDITIONALITY:** **the three lifted suspensions come with an inherited conditionality a consumer MUST carry**, stated in the sweep itself: “on ITERLAWN’s own proved perimeter and with its existing DCX/\((RM\text{-}m)\) conditionality unchanged”, and “From rung \(3\) onward ITERLAWN calls only \((RM\text{-}m)\) with \(m\ge2\); those retain exactly their pre-existing conditional ledger.” **ITERLAWN's ledger for those is OPEN**: its (RM-m) STATUS box reads “m ≥ 2: **OPEN.**” (XREF Y19, count 1, line 806). So “the all-rung propagation now follows at ITERLAWN's own conditionality” means: follows modulo an engine ITERLAWN itself has not proved at m ≥ 2. This is honest and explicitly stated — but a chapter cut that quotes only “its rung-≥2 suspension is lifted” would misrepresent it.

**RESOLUTION TRACE:** statement lines 2026–2070.

**TEETH:** all five ITERLAWN section designations verified: `### S4.4 CASE-SPLIT-(n) (the exact partition at the top of rung n)` count 1 line 709; `### S4.5 W-MULT-(n), Case I (single top digit) — PROVED, generic` count 1 line 750; `### S4.6 The engine (RM-m), and Cases II-1/II-2/II-3 — PROVED generic MODULO (RM-(n−1)), off DCX-(n)` count 1 line 777. **NEAR-MISS (v3 rule 15):** `CASE-SPLIT-(2)` is absent as written (`grep -cF` = 0); the verified referent is `CASE-SPLIT-(n)` at line 709 with its n = 2 instance named at line 737 (“At n = 2 this is [IL3] CASE-SPLIT verbatim”). Disposition of the whole unit: `scope record, transcribed; every designation verified or NEAR-MISS-resolved`.

---

### EFF.LIFTCORNER.118  [instrument-record]

**CANONICAL STATEMENT:**

> “*(Orchestrator verification before transcription — (T1)'s strictness
> re-derived (gcd(e₀,h₀) = 1 makes e₀ ∤ (e₀−k)h₀ for 0 < k < e₀, so
> the ceiling adds ≥ 1; the k = 0 term rides the residue pin); the
> (T4) crux re-computed (ν(Q″Δ) ≥ (μ−W) + (W+1) = μ+1 — the swap
> correction lands strictly above the consumed line); the R′ = R″ − A,
> Q′ = Q″ − B bookkeeping checked against (T2); the sweep's rung-≥3
> claim checked against AC-4 (only (RM-m), m ≥ 2, is called there, at
> its existing conditional ledger). The PROP/S5/FC-2 suspensions of
> annex AC-1 are LIFTED as stated. Transcribed unaltered per the
> standing division of labor. Ledger: row 19 → the (Φ₁-OPACITY)
> program is complete (AC-1 containment → AC-4 narrowing → AC-5
> discharge); transcription-confirm owed.)*”

**FORM:** italic parenthetical — the note's final line.

**DERIVATION:** `[RECORD]` of an independent pre-transcription check of exactly the two crux steps.

**CONDITIONALITY:** **“transcription-confirm owed” is the note's LAST OPEN OBLIGATION and it is verifiably still open**: `grep -cF 'OPACITY'` = 0, `grep -cF 'AC-4'` = 0, `grep -cF 'AC-5'` = 0 on `ITERLAWN_PROOF_2026-08-08.md`. OPEN-CALL 1.

**RESOLUTION TRACE:** statement lines 2072–2083 (the note's final lines).

**TEETH:** **both re-derivations independently reproduced at compile time and both are correct** — (T1)'s ceiling argument at `.111` and (T4)'s arithmetic at `.114`. `runs/cert5/P4_rm1_output.log` exists. Disposition `accepted-with-decorrelation-supplied`.

---

## 4. XREF verification ledger (consolidated, deduplicated)

Every positive XREF was checked with fixed-string `grep -cF` at compile time (2026-08-14)
against the working tree; commit pins with `git cat-file -t`; artifacts by existence + md5.
**Seven exact cross-shard duplicates were found** — both shards independently re-verified the
same (designation, file, line) triple because the fact is load-bearing on both sides of the
line-1167/1168 boundary. Each is merged into one row below, with both original IDs retained
for provenance.

### 4.1 Source-of-record and cross-note designations (deduplicated)

`[TABLE — compiler ledger]`

| Merged ID | Target file | Verified designation | count | line | Role / original ID(s) |
|---|---|---|---:|---:|---|
| X01 | `ILNRES_2026-08-08.md` | `**S5.1 (NR-1 LIFT-CORNER unit), price M.**` | 1 | 180 | the spec of record; shard 1 only |
| X02 | same | `**[NR-1] (ITER-LAW-LIFT), open exactly at g₀ = 1 ∧ δ₁ = 1.**` | 1 | 25 | the residual this note attacks; shard 1 only |
| X03 | `ITERLAWLIFT_CORNER_2026-08-08.md` | `**Step 2 (THE ONE OPEN STEP — displayed lemma (TAIL-STAB)).**` | 1 | 191 | wave-18's open step = `.35`; shard 1 only |
| X18 | same | `**Honesty box.** (TAIL-STAB) is UNPROVED` | 1 | 207 | the supplier's pre-state `.35` closes; shard 1 only |
| X04 | same | `104,404` | 3 | 122 | the LAWFUL slice measurement (`.19`, `.60`); shard 1 only |
| X05 | `ITERLAWN_PROOF_2026-08-08.md` | `### S0.1 The (n+1)-read standard-lift harness class (the class pin)` | 1 | 144 | the class pin PROP rides; shard 1 only |
| **X06 / Y01** | same | `* Lifts: Φ₁ := the STANDARD LIFT of ψ₀ (grb_order2_check :499–507); for` | 1 | 163 | **DEDUP** — cited identically by both shards (shard 1's PROP-cite bracket `.64`; shard 2's S0.1-rider rewrite `.73`) |
| X09 | `GRTW2_PROOF_2026-08-08.md` | `### 3.4 THE (ξ, w) CLOSED FORM (the display of record)` | 1 | 394 | the χ-chain source (`.19`, `.49`); shard 1 only |
| X10 | same | `### 5.3 The value layer: W2-OPEN-1 (displayed open lemma, machine-confirmed)` | 1 | 881 | the clause-3/W2-OPEN-1 source (`.62`); shard 1 only |
| **X07 / Y12** | `ITERLAWN_PROOF_2026-08-08.md` | `## S7. THE CONDITIONALITY LEDGER (the exact grade of every clause, per rung)` | 1 | 1148 | **DEDUP** — the sweep's true home, 22 data rows; shard 1's `[r5,F5-4]` re-pointing check AND shard 2's AC-1-certificate-design check both land here |
| X08 | same | `[attribution (errata r4, 2026-08-03; PE4-F1): + S4.1 at rungs ≥ 2` | 1 | 278 | the r4 erratum's L6 row (`.64`); shard 1 only |
| **X15 / Y14** | same | `194 raw hits on 147 lines, 194/194 mapped, ZERO` | 1 | 1233 | **DEDUP** — ITERLAWN's own machine census, the object AC-4 uses (`.103`) |
| **X17 / Y16** | same | `### S4.6 The engine (RM-m), and Cases II-1/II-2/II-3` (shard 1's quoted substring) / `… — PROVED generic MODULO (RM-(n−1)), off DCX-(n)` (shard 2's fuller quotation, same line) | 1 | 777 | **NEAR-DUPLICATE** — same target line, two quotation granularities of the same one-line heading; both verify. Merged row quotes the fuller (shard 2) form. |
| **X16 / Y03** | `ILNRES_2026-08-08.md` | `S1's FOUR-MEMBER residual list is COMPLETE relative to the sources` | 1 | 288 | **DEDUP** — the completeness sentence `.77` will not collide with, and `.87`'s collision-avoidance check |
| Y02 | `ILNRES_2026-08-08.md` | `Extend the [IL] L7 Case-II analysis to an arbitrary lawful lift Φ₁′ = Φ₁ + (π-excess) at g₀ = 1 ∧ δ₁ = 1, then ride S0.1's verbatim propagation` | 1 (normalized) | 180 | the spec deliverable quoted at `.75`; shard 2 only |
| Y04 | `ITERLAWLIFT_CORNER_2026-08-08.md` | `the honest OPEN displayed lemma **(ITER-LAW-LIFT)**: ITER-LAW for every lawful monic lift Φ₁` | 1 (normalized, spans lines 35–36) | 35 | the wave-18 residual quoted at `.75`; shard 2 only |
| Y05 | `ILNRES_2026-08-08.md` | `nothing is claimed for any non-canonical lawful lift at any level` | 1 (normalized) | 28 | the “at any level” clause of `.76`; shard 2 only |
| Y06 | `ITERLAWN_PROOF_2026-08-08.md` | `m ≥ 2: **OPEN.**` | 1 | 806 | the inherited conditionality of `.73`/`.117`; shard 2 only |
| **X13 / Y07** | `GRTW2_PROOF_2026-08-08.md` | `the accepted LIFTCORNER's shift-descent` | 1 | 1351 | **DEDUP** — the shard's one fully closed supplier-consumer loop, cited by `.72` (the consumption declaration) AND by `.91` (FC-1's acknowledgement quote) |
| X11 | same | `W2-OPEN-1` | 10 | 127 | the designation `.62` says two things are owed against; ledger row at line 982 reads “**OPEN**, instance-confirmed 684 groups / 0”; shard 1 only |
| **X14 / Y10** | `ITERLAWN_PROOF_2026-08-08.md` | `## ★ FOLD ANNEX (orchestrator, 2026-08-07): THE NR-1 RIDER-REWRITE, LICENSED AND EXECUTED ★` | 1 | 1518 | **DEDUP** — FC-2's execution, LANDED; cited by `.64` (from the PROP-cite side) AND `.92` (FC-2's own record) |
| Y08 | same | `WELL-DEF` | 32 | — | AC-1/AC-4's constructor target; shard 2 only |
| Y09 | same | `### S4.2 L6-(n) (ANCHOR-VAL = the ε-chain; all n, no engine, no DCX)` | 1 | 575 | the degree telescope's home; shard 2 only |
| Y11 | same | `### S4.1 Lemmas REALIZE-(m), WELL-DEF-(n), READ-ADD-(m)` | 1 | 499 | AC-4's constructor subgraph; shard 2 only |
| **RX22 / Y13** | `docs/PROJECT_STATE.md` | `row 19 also ((Φ₁-OPACITY), numerical certificate` | 1 | 3996 | **DEDUP** — the certification-ledger row tracking the whole AC-1→AC-5 arc |
| Y15 | `ITERLAWN_PROOF_2026-08-08.md` | `m = 1: PROVED — [IL3] DIGIT-SPLIT + DEV-1` | 1 | 794 | the proof status AC-4 quotes (`.106`); shard 2 only |
| Y17 | same | `ITER-PKG-2` | 1 | 1458 | the package AC-5 constructs; its schematic form graded `STATED; base r=1 ACCEPTED, r=2 = [IL3] 0/2` at line 279; shard 2 only |
| Y18 | same | `{e₀ = 1 ∧ d₀ ≥ 2} general inputs enter [IL3]'s fenced DEV-1 corner —` | 1 | 803 | the scope tension of `.112` (OPEN-CALL 8); shard 2 only |
| Y19 | same | `### S4.4 CASE-SPLIT-(n) (the exact partition at the top of rung n)` | 1 | 709 | AC-5's sweep target (NEAR-MISS-resolved, `.117`); shard 2 only |
| Y20 | same | `### S4.5 W-MULT-(n), Case I (single top digit) — PROVED, generic` | 1 | 750 | AC-5's sweep target; shard 2 only |
| Y21 | same | `**Lemma READ-ADD-(m) (read additivity with strict-above kill; generic).**` | 1 | 564 | NEAR-MISS resolution for `READ-ADD-(1)` (`.115`); shard 2 only |
| RX19 | `spec/HYPOTHESIS_LEDGER.md` | `HYP.76  \`W2-VALUE\`` | 1 | 596 | the W-2 value-layer row adjudicating the LIFTCORNER/W-2 seam NOT-REACHED; shard 1 only |
| RX20 | same | `HYP.110  \`W12-BOX-5\`` | 1 | 893 | “Lean omCount is order-0 and W-2/LIFTCORNER lift-convention seam is unconsumed”; shard 1 only |
| RX21 | `docs/in-progress/LEAN_SCOPING_consumption_map_2026-08-12.md` | `LIFTCORNER` | 5 | — | the Lean-scoping consumption read; shard 1 only |

**Zero-drift confirmation, re-run fresh at merge time (2026-08-14) as this merge's own
mandatory sample, spanning both shards:** X01, X02, X03, X09, X10 (shard 1's designations)
and Y01, Y06, Y13, Y16, Y19 (shard 2's) — **10 of the ledger's ~30 distinct rows** —
re-executed with fresh `grep -cF`/`grep -cE` against the current working tree:

```
$ grep -cF '**S5.1 (NR-1 LIFT-CORNER unit), price M.**' ILNRES_2026-08-08.md            → 1
$ grep -cF '**[NR-1] (ITER-LAW-LIFT), open exactly at g₀ = 1 ∧ δ₁ = 1.**' ILNRES...      → 1
$ grep -cF '**Step 2 (THE ONE OPEN STEP — displayed lemma (TAIL-STAB)).**' ITERLAWLIFT... → 1
$ grep -cF '### 3.4 THE (ξ, w) CLOSED FORM (the display of record)' GRTW2_PROOF...       → 1
$ grep -cF '### 5.3 The value layer: W2-OPEN-1 (displayed open lemma...' GRTW2_PROOF...  → 1
$ grep -cF '* Lifts: Φ₁ := the STANDARD LIFT of ψ₀ (grb_order2_check :499–507); for' ...  → 1
$ grep -cF 'm ≥ 2: **OPEN.**' ITERLAWN_PROOF...                                          → 1
$ grep -cF 'row 19 also ((Φ₁-OPACITY), numerical certificate' docs/PROJECT_STATE.md      → 1
$ grep -cF '### S4.6 The engine (RM-m), and Cases II-1/II-2/II-3 — PROVED generic...'    → 1
$ grep -cF '### S4.4 CASE-SPLIT-(n) (the exact partition at the top of rung n)' ...      → 1
```

**All ten reproduce their claimed count exactly; zero drift.** Combined with the header
blob-hash re-derivation and the negative-edge re-runs below, this merge independently
re-executed **16 distinct checks** against the working tree rather than trusting either
shard's transcription.

### 4.2 Sample statement-quote re-verification (5 of 118, checked verbatim against the
source note by line number, fresh at merge time)

| Unit | Claimed source lines | Fresh check | Result |
|---|---|---|---|
| `.18` (DEFINITION, the corner orbit) | 355–359 | `sed -n '355,359p' LIFTCORNER_2026-08-08.md` | verbatim match, byte-for-byte, including the ASCII display |
| `.57` (THEOREM) | 962–968 | `sed -n '962,968p' LIFTCORNER_2026-08-08.md` | verbatim match, including the bracketed `[Machine: Q3 4,176/0.]` tail |
| `.89` (acceptance record, “THIS NOTE IS ACCEPTED at 2/2”) | 1433–1441 | `sed -n '1433,1441p' LIFTCORNER_2026-08-08.md` | verbatim match, including the exact pass/round arc string |
| `.111` (AC-5, boxed inequality (T1)) | ends at the `\tag{T1}` line, source ≈1870–1872 | `grep -n 'boxed{\\nu(\\Delta)' LIFTCORNER_2026-08-08.md` | verbatim match, tag included |
| source title (context check, not itself a canonical statement — `.01`'s statement is lines 3–7) | line 1 | `sed -n '1p' LIFTCORNER_2026-08-08.md` | matches both shards' shared title citation in their own headers |

**Zero drift found in any of the five.**

### 4.3 Artifact and commit pins (consolidated; shard 1's P-series and shard 2's Q-series
overlap almost entirely — every one of shard 2's six re-verified pins was already present in
shard 1's P15/P16/P17, because both shards independently needed the same six commits for
their own FREEZE-1/acceptance-record material)

`[TABLE — compiler ledger]`

| Pin | Kind | Verified | Origin |
|---|---|---|---|
| `verification/openmath/liftcorner_checks.py` | artifact | EXISTS; md5 `ccb4351c92573f5f962cae4ae952d8dd` — identical at every one of the note's four quotation sites (`.03`, `.06`, `.28`, `.90`) | shard 1 (P01) = shard 2 (Q04), DEDUP |
| `verification/openmath/liftcorner_checks_output.txt` | artifact | EXISTS; `TOTAL checks 25409  elapsed 4.4s`, `VERDICT: ALL GREEN` | shard 1 only (P02) |
| `verification/openmath/liftcorner_checks_results.json` | artifact | EXISTS | shard 1 only (P03) |
| `verification/openmath/liftcorner_tailstab_children.py` | artifact | EXISTS; md5 `11f2d7858a66d4b8231b38b11f8751c3` | shard 1 only (P04) |
| `verification/openmath/liftcorner_tailstab_children_table.txt` | artifact | EXISTS; md5 `bf9106e7edc535edf2b7a6b6a64f0f55`, 2,986 lines; `nodes reconciled: 752  children enumerated: 5336` | shard 1 (P05) + shard 2's independent re-check (Q05), DEDUP in substance |
| `LIFTCORNER_passPE1..PE9_report.md` (nine files) | artifacts | ALL NINE EXIST in `lean/notes/openmath/` | shard 1 (P06–P14) ⊇ shard 2 (Q03, PE8/PE9 only), DEDUP |
| nine report commits: `30e570c 3367f3c 39ea0db 8b53efa a5212e8 f2b48e7 58f7060 c6097d7 9b5175c` | commits | ALL NINE resolve (`git cat-file -t` = commit) | shard 1 only (P15); shard 2's Q02 re-checks the last two (c6097d7, 9b5175c) as a subset, DEDUP |
| `dafc0b5` (the seal), `46e6e88` (PE6 HEAD), `91f0cde` (PE7 HEAD), `adc6cf3` (GRTW2 acceptance), `5054d69` (FC-2 execution), `08f61e9` (this note's acceptance) | commits | ALL SIX resolve | shard 1 (P16) ⊇ shard 2 (Q02, four of the six re-checked independently), DEDUP |
| `runs/cert/C1_liftcorner_output.log`, `runs/cert2/E1_liftcorner_output.log`, `runs/cert4/P3_opacity_output.log`, `runs/cert5/P4_rm1_output.log` | artifacts | ALL FOUR EXIST — the certifier arc behind AC-1…AC-5 | shard 1 (P17) = shard 2 (Q01), EXACT DEDUP |
| `LIFTCORNER_passPE8_report.md`, `LIFTCORNER_passPE9_report.md` | artifacts | BOTH EXIST (subset of P06–P14 above) | shard 2 only, redundant with P06–P14 (Q03) |
| PE9's p = 7 fresh-instance leg (2,178 nonzero digits, 0 violations) | — | **UNPINNED** — no committed artifact in `verification/openmath/` records it; only the PE9 report does | shard 2 only (Q06); OPEN-CALL 10 |
| AC-1's 57-pair pre-proof numerical certificate | — | **NEVER EXECUTED** — no corresponding artifact exists; superseded by AC-5's proof (`.96`) | shard 2 only (Q07); recorded at `.96` |

### 4.4 NEAR-MISS dispositions (v3 rule 15; all three are shard 2's, all inside the
transcribed-certifier units — the certifier instantiates schematic ITERLAWN names)

`[TABLE — compiler ledger]`

| Cited as | `grep -cF` | Verified referent | Disposition |
|---|---:|---|---|
| `CASE-SPLIT-(2)` (`.117`) | 0 | `CASE-SPLIT-(n)` at line 709, count 1, with the n = 2 instance named at line 737 | NEAR-MISS: instantiated name vs schematic name; referent unambiguous |
| `READ-ADD-(1)` (`.115`) | 0 | `READ-ADD-(m)` at lines 499 and 564, count 1 each; the lemma's own title carries “strict-above kill” | NEAR-MISS: same pattern |
| `f\,\widehat C_m=R+Q\Phi_m` (`.106`) | 0 as LaTeX | the source renders it as an ASCII box inside Y16's display, count 1 | NEAR-MISS: notation transliteration, referent verified line by line |

### 4.5 Verified NEGATIVE edges (consolidated; three of the eight raw checks are exact
cross-shard duplicates, re-verified fresh at merge time — all eight reproduce)

`[TABLE — compiler ledger]`

| ID | Check | count | Meaning | Origin |
|---|---|---:|---|---|
| **N1** | `grep -cF 'OPACITY' ITERLAWN_PROOF_2026-08-08.md` | 0 | the (Φ₁-OPACITY) program is UNLANDED on ITERLAWN | shard 1 = shard 2, DEDUP; re-verified fresh |
| **N2** | `grep -cF 'AC-4' ITERLAWN_PROOF...` / `grep -cF 'AC-5' ITERLAWN_PROOF...` | 0 / 0 | neither AC-4's nor AC-5's discharge is LANDED on ITERLAWN (shard 1 checked AC-5 alone; shard 2 checked both — the merged check is the union) | shard 1 (AC-5 half) ⊂ shard 2 (both); re-verified fresh |
| **N3** | `grep -cF 'LIFTCORNER' ILNRES_2026-08-08.md` | 0 | ILNRES carries no absorption append; its one hit under the hyphenated `LIFT-CORNER` spelling (count 1, line 180, re-verified) is the pre-existing S5.1 spec heading, i.e. the CHARGE, not a fold | shard 1 = shard 2, DEDUP; re-verified fresh |
| N4a | `grep -cF 'NR-1 discharged' ILNRES_2026-08-08.md` | 0 | NR-1's ILNRES ledger entry is unfolded; the §S5 rider rewrite landed on ITERLAWN only (X14/Y10) | shard 1 only; re-verified fresh |
| N4b | `grep -cF 'SUSPENDED' ITERLAWN_PROOF_2026-08-08.md` | 0 | the fold annex records neither AC-1's suspension nor AC-5's reinstatement | shard 2 only; re-verified fresh |

---

## 5. Local supply/consumption ledger (state at HEAD; consolidates and supersedes both
shards' separate §4 tables, which recorded the state at their own respective HOME ranges)

`[TABLE — compiler ledger]`

| Source conclusion or obligation | Effective supply | Surviving fence | Protocol status at HEAD |
|---|---|---|---|
| wave-18's open step (TAIL-STAB) (X03, X18) | `.35`+`.36`, proved by the lex descent `.37`–`.48` | census completeness carried by algebra, machine leg instance-level (`.45`) | **CLOSED**; wave-18's honesty box is answered |
| ILNRES S5.1's deliverable (X01) | `.57` + `.60` + `.61` + PROP `.63` (CHAIN-P terminal `.117`) | Φ₁ axis only; deeper levels fenced, ILNRES-side erratum candidate still open (`.77`, OPEN-CALL 7) | **DELIVERED and ACCEPTED (2/2, `.89`)**; ILNRES ledger fold **NOT LANDED** (N3) |
| [ILN] S0.1's rider on the Φ₁ axis (X05, X06/Y01) | `.63` (PROP), discharged via CHAIN-P (AC-1 suspend `.95` → AC-4 narrow `.103`–`.108` → AC-5 discharge `.111`–`.117`) | ITERLAWN's own DCX/(RM-m ≥ 2)/T-scope conditionality unchanged and OPEN (Y06) | **LANDED as FC-2 on ITERLAWN** (X14/Y10) — landed BEFORE AC-1's suspension and never updated with either AC-1 or AC-5 (OPEN-CALL 3) |
| GRTW2 clause 3 ψ-transport (X09, X10) | `.19` (the corner degeneration) and `.61` (COR 2) | COR 2 is about the HARNESS orbit only; (a)/(b) of `.62` owed for any W2-OPEN-1 tie | **CONSUMED**; acknowledged by name in GRTW2's acceptance record (X13/Y07) |
| the accepted [IL] ITER-LAW (standard lift) | consumed at `.57`'s reduction to Φ″ | 2-read only; no orders-≥3 claim (`.17`) | **CONSUMED, unmodified** |
| CONTENT (sub-lemma) | `.34`, effective statement = AC-2's integral-key form (`.98`) | Φ ∈ 𝒪[x] | statement REPAIRED at appendix; every consumer survives unchanged (consumer sweep at `.98`) |
| READ-EQ's degree comparison | `.55`, effective statement = AC-3's corrected clause (`.99`) | holds also at d₀ = 1 | statement REPAIRED at appendix; THEOREM/COR 1/COR 2 survive unchanged |
| the note's five accepted theorems ((TAIL-STAB), READ-EQ, THE THEOREM, COR 1, COR 2) | `.35`, `.54`, `.57`, `.60`, `.61` | at the note's own conditionality; COR 2's (a)/(b) owed | **ACCEPTED 2/2** (`.89`); W-2 cap re-read as an accepted-supplier cap (CHAIN-W, `.91`) |
| constructor/telescope Φ₁-opacity | `.104`, `.105` (AC-4) | Θ asserted only on displayed normal forms (NI-15) | **APPENDED here; ITERLAWN not informed** (N1) |
| (RM-1-TRANSPORT) | statement `.107`; proof `.111`–`.115` (AC-5) | the four interface clauses only; NOT full R,Q equality (`.116`) | **APPENDED here; ITERLAWN not informed** (N1) |
| all-rung PROP | `.63` (CHAIN-P TERMINAL `.117`) | at ITERLAWN's own conditionality, whose (RM-m) is OPEN at m ≥ 2 (Y06) and whose ITER-PKG-2 rides [IL3] at 0/2 (line 279) | **DISCHARGED conditionally**; transcription-confirm owed (`.118`, OPEN-CALL 3) |
| ITERLAWN S4.6's (RM-1) engine (X17/Y16) | NOT consumed pre-acceptance; consumed by AC-5 | AC-5 proves only the four interface clauses, explicitly not full R,Q equality | **CONSUMED by the certifier arc; UNLANDED on ITERLAWN** (N1, N2) |

---

## 6. TEETH inverse table (unified from both shards; presented as two sub-tables by
shard-of-origin — shard 1 carries the core sealed battery, the machine-generator legs and
the seven charge items, shard 2 carries the acceptance bar, the certification-arc findings
and the AC-4/AC-5 arithmetic — with one combined zero-orphan statement closing both)

Disposition vocabulary: `{proved-in-note, executable regression, AUDIT (decorrelated-model |
in-house hostile pass), signed vacuity disclosure, disclosed non-repair,
accepted-with-decorrelation-supplied, stale self-description, PROOF-ONLY}`.

### 6.1 Shard 1's core battery, machine-generator legs and charge items (IDs unchanged,
offset 0)

`[TABLE — compiler ledger]`

| # | Battery row / charge item (abbreviated) | Guarded EFF units | Disposition |
|---:|---|---|---|
| 1 | Q1 GATE — every tower passes the lawfulness gate for its OWN ψ₀′ | `.18`, `.19`, `.21` | executable regression (56/56) |
| 2 | Q2 AV — ANCHOR-VAL with the transported ε₁′ | `.19`, `.54` | executable regression (656/0) |
| 3 | Q3 TLAW — THE CANDIDATE: measured cocycle = transported display | `.20`, `.57`, `.35` | executable regression (4,176/0) |
| 4 | Q4 PV — L7 PAIR-VAL both forms + single-slot shape | `.54`, `.56`, `.36` | executable regression (4,176/0) |
| 5 | Q5 INT — exponent integrality | `.20` | executable regression (4,176/0) |
| 6 | Q6 LOC — δ₁ = 0 sub-violations (bug detector) | `.30` | **disclosed non-repair** (nested, not independent) |
| 7 | Q7 CHI — cross-tower χ-ratio, measured vs MEASURED | `.61`, `.19` | executable regression (4,176/0) |
| 8 | Q8 COV — coverage per twisted block | `.21`, `.29` | executable regression (met: min 6 / min 6) |
| 9 | Q9 WRONGLET — per-pair set equivalence; fires > 0 | `.61` (sharpness) | executable regression (3,816 exact, 1,576 fires) |
| 10 | Q10 XI1 — ξ = 1 dense slice reproduces the unchanged display | `.60` | executable regression, **UNPINNED figure** (no independent counter) |
| 11 | TRS — closed-form transcription vs `C.iter_law` | `.20`, `.57` | executable regression (4,176/0) |
| 12 | CERT — base towers G.T1_T2(nf=4) + G.T5 internal | `.22` | **disclosed reuse** (PARI leg not re-run) |
| 13 | ENG-GATE — `engine_ext.agreement_gate(full=False)` | `.22` | executable regression (1 check, 0 new — undisplayed in §S3, OPEN-CALL 2) |
| 14 | A1–A6 (children generator, r1) | `.39`, `.40`, `.41`, `.43`, `.46` | executable regression (752 probes / 4,438 digits / min slack 0) |
| 15 | A7(i)–(iv) (children generator, r2) | `.38`, `.44`, `.47`, `.48` | **accepted-with-decorrelation-supplied** |
| 16 | Charge item (1) — census COMPLETENESS + row-7b drop | `.38`, `.41`, `.45` | **PROOF-ONLY** — ∀ carried by algebra, A7 instance-level |
| 17 | Charge item (2) — lex-order finiteness | `.47`, `.48` | proved-in-note; three hostile re-derivations |
| 18 | Charge item (3) — CONTENT's base-fact status | `.34` | **AUDIT / decorrelated-model** — repaired by AC-2 (`.98`) |
| 19 | Charge item (4) — READ-EQ close | `.55`, `.56` | **AUDIT / decorrelated-model** on the degree clause (AC-3, `.99`); rest proved-in-note |
| 20 | Charge item (5) — PROP's census cite | `.63`, `.64` | **AUDIT / decorrelated-model** — CHAIN-P (AC-1 `.95` → AC-4 `.103`–`.108` → AC-5 `.111`–`.117`) |
| 21 | Charge item (6) — COR 2 rescoped; (a)/(b) owed | `.61`, `.62` | **OPEN** — no instrument closes it |
| 22 | Charge item (7) — eight per-digit ω-gain bounds | `.42`, `.39` | **accepted-with-decorrelation-supplied** |

### 6.2 Shard 2's acceptance bar, certification-arc findings and AC-4/AC-5 arithmetic
(renumbered, `.73`–`.118`)

`[TABLE — compiler ledger]`

| # | Obligation | Guarded units | Disposition |
|---:|---|---|---|
| 23 | PE8 CLEAN + PE9 CLEAN (the acceptance bar) | `.89`, `.90` | **AUDIT / in-house hostile pass** — two consecutive clean, model-diverse passes |
| 24 | PE9's fresh-instance p = 7 leg | `.89` | executable regression, **UNPINNED** (OPEN-CALL 10) |
| 25 | the sealed runner's machine record | `.83`, `.90` | executable regression, re-verified (md5, 25,409/0) |
| 26 | the children generator + A7 | `.90` | executable regression, re-verified (752/5,336) |
| 27 | C1's 5 findings adjudicated by E1 | `.93`–`.100` | **AUDIT / decorrelated-model audit**: 2 REAL repairs, 1 OBSTRUCTED, 2 rebutted |
| 28 | AC-1's 57-pair numerical certificate | `.96` | **preregistration, superseded-unexecuted** |
| 29 | AC-4's census partition | `.103` | arithmetic recount ✓ against ITERLAWN's own census (X15/Y14) |
| 30 | AC-4's Θ-transport sublemma | `.104`, `.105` | derivation, transcribed; telescope arithmetic re-verified |
| 31 | AC-5's (T1)–(T6) | `.111`–`.115` | **arithmetic recount** ✓ every step; independent orchestrator re-derivation (`.118`) |
| 32 | the four consumed interface clauses vs ITERLAWN's box | `.113`, `.115` | verified line by line against X17/Y16 |
| 33 | the three landed/unlanded protocol facts | `.91`, `.92`, `.108`, `.118` | 1 LANDED (X14/Y10), 3 UNLANDED (N1–N4) |
| 34 | the archive's three inside corrections | `.84`–`.87` | dead-text discipline; terminals in `.25`, `.10` (shard 1) |

**Zero-orphan check (combined):** shard 1's 22-obligation zero-orphan tally (13 sealed-sheet
families + 2 machine-generator assertion suites + 7 charge items) plus shard 2's 12-obligation
tally (acceptance bar + 5 certification findings + AC-4/AC-5's arithmetic + the archive) =
**34 obligations, all mapped, 0 orphan rows.** Units carrying no tooth of their own — `.01`,
`.02`, `.16`, `.17`, `.31`, `.49`, `.65`–`.72` (shard 1's identification/scope/record units,
guarded by the acceptance record and the pin ledger instead), `.73`–`.82`, `.101`, `.109`,
`.116` (shard 2's scope/record/preamble units) — total 22 of 118, exactly matching each
shard's own reverse-direction count. Every other unit — 96 of 118 — appears in at least one
row above.

### 6.3 Arithmetic audit summary (v3 rule 22; consolidated, both shards' figures cross-checked
against each other where they share an input)

- **25,409** = 56 + 656 + 5×4,176 + 3,816 + 0 + 0 + 1 ✓ (shard 1)
- **56** towers = 48 twisted + 8 dense controls = 16 twistable × ≤2 draws × 2 variants + 8 ✓
  (shard 1's `.21`; independently re-cited by shard 2's `.96` as “57 tower pairs = 56 + the
  PE1 counter-instance” — **the two shards' 56-figures agree**)
- **2e₀+3**, **220** m′=m children, **752/5,336/4,438**, all reproduce (shard 1, §6.3 of its
  own file; re-cited without alteration by shard 2's `.83`, `.90`)
- **194** = 88+21+53+8+18+6 ✓ — AC-4's partition (`.103`), cross-checked against ITERLAWN's
  own census bracket (X15/Y14): every one of the six class counts and both totals match
- **51** = 34+4+13 ✓ (PE7's `c′` partition, `.68`); at HEAD the raw counts are 54/50, three
  above PE7's 51/47 — explained by the four post-91f0cde certifier appends (`stale
  self-description`, not an error)
- **(T1)**: gcd(e₀,h₀) = 1 ⇒ e₀·amin(k) + kh₀ ≥ e₀h₀+1 = W+1 ✓ — **the identical mechanism
  as shard 1's `.42` rows 6–7 bound**, re-used at a different level; both shards' independent
  re-derivations agree
- **(T4)**: (μ−W) + (W+1) = μ+1 ✓ — the single unit of strictness the whole (RM-1-TRANSPORT)
  discharge rests on, traced all the way back to shard 1's S1 lawfulness bound
- Φ′ = Φ₀² + 2xΦ₀ + 2 = x⁴+4x³+5x²+4x+3 ✓; the counter-instance double-development identity
  ✓ (shard 1, `.53`)

**Zero arithmetic discrepancies found across either shard or across this merge's own
cross-checks between them.** Two completeness gaps (the undisplayed ENG-GATE count; the
staleness of the `c′` census) are carried forward as OPEN-CALLs, not as errors.

---

## 7. SERIES, cross-shard supersession edges, and boundary resolution

### 7.1 Internal supersession CHAINs (all four resolve entirely inside shard 1, `.01`–`.72`;
IDs unchanged by the merge)

`[TABLE]`

| Chain | Layers, in source order | TERMINAL |
|---|---|---|
| **CHAIN-A (the assert pair)** | r0 description → `[r1,F4]` promotes (i) → `[r3,F-A]` inverts, promotes (ii) → `[r4,F4-1]` demotes BOTH → `[r5,F5-2]` re-scopes | **`[r4,F4-1]` as re-scoped by `[r5,F5-2]`** (`.25`, restated at `.08`) |
| **CHAIN-B (“bit-identically”)** | r2 wording → `[r3,F-C]` strikes it → `[r4,F4-3]` corrects the PROVENANCE, facts unchanged | **`[r4,F4-3]`** (`.10`) |
| **CHAIN-C (the r-to-q gain identity)** | r1 identity → `[r2,G4]` STRIKES it → `[r3,F-B]` replaces the witness; the strike itself stands | **`[r2,G4]` strike + `[r3,F-B]` witness** (`.42`) |
| **CHAIN-D (the `c′` census warrant)** | `[r4,F4-5]` renames the cocycle and opens the census → `[r6,F6-2]` extends it, citing PE6's “42 occurrences” → `[r7,F7-1]` corrects the UNIT and installs PE7's occurrence-level warrant | **`[r7,F7-1]`** (`.59`) |

### 7.2 Cross-shard supersession CHAINs (all five span both shards; renumbered, TERMINALs
verified unique)

**SPECIAL CARE, per the merge charge: CHAIN-P is the note's central reversal — a chain cut
mid-way misstates the note's law.** The four-layer sequence PROP frozen text → AC-1 SUSPENDS
→ AC-4 NARROWS → AC-5 DISCHARGES is preserved whole below, in source order, with its TERMINAL
verified unique among the five chains in this table.

`[TABLE]`

| Chain | Layers, in source order | TERMINAL |
|---|---|---|
| **CHAIN-P (PROP / the all-rung rider)** | frozen S4.3 text (`.63`): “the discharge lifts to every rung AT [ILN]'s OWN conditionality” → **AC-1** (`.95`) SUSPENDS all three (PROP, S5's rider, FC-2's execution): “The all-rung force of three earlier sentences is SUSPENDED”, naming the missing lemma (Φ₁-OPACITY) → **AC-4** (`.103`–`.108`) NARROWS: constructor/telescope subgraph PROVED opaque, “AC-1 is narrowed but not discharged”, obstruction surviving at exactly one site (ITERLAWN S4.6's (RM-1)) → **AC-5** (`.111`–`.117`) — **TERMINAL** — proves (RM-1-TRANSPORT) and DISCHARGES: “**LIFTCORNER PROP:** its rung-≥2 suspension is lifted. The all-rung propagation now follows at ITERLAWN's own conditionality.” | **`.117`** — PROP itself is stated at `.63`; the reading a chapter cut must use is the AC-5 layer (`.117`), not AC-1's suspension (`.95`), which is live history, not live scope — quoting it as current would misstate the note's law exactly as quoting the grade box's stale 0/2 would |
| **CHAIN-G (the grade counter)** | grade box “ATTEMPT 0/2” (×6, `.65`–`.70`) + STATUS BLOCK COUNTER “0/2” (`.80`) → **ACCEPTANCE RECORD 2/2** | **`.89`** |
| **CHAIN-W (the W-2 cap)** | “GRTW2 is itself 0/2” (`.72`) + the acceptance record's cap clause (`.90`) → **FC-1**: read as “capped by an ACCEPTED supplier at its fenced scope” | **`.91`** |
| **CHAIN-S (the S5 deeper-level bookkeeping)** | r3 wording “stays open as its own priced item” → **`[r4,F4-6]`** strikes it, replaces with three paragraphs (`.74`–`.77`) → **AC-1 finding 2** re-affirms the fence as already curing the certifier's own objection | **`[r4,F4-6]`, re-affirmed by finding 2** (`.74`–`.77`) |
| **CHAIN-F (FC-2's executed rider)** | acceptance record licenses (`.90`) → **FC-2** executes at `5054d69`, reports DISCHARGED (`.92`) → **AC-1** SUSPENDS the execution (`.95`) → **AC-5** reinstates it | **`.117`** — with the landed ITERLAWN annex still recording none of it (OPEN-CALL 3) |

**Verification that the nine chains' TERMINAL anchors are pairwise distinct except one
deliberate, verified share**, checked mechanically against the nine cells above: CHAIN-A
`.25`, CHAIN-B `.10`, CHAIN-C `.42`, CHAIN-D `.59`, CHAIN-P `.117`, CHAIN-G `.89`, CHAIN-W
`.91`, CHAIN-S `.77`, CHAIN-F `.117` — **eight distinct final anchors across nine chains**,
with CHAIN-P and CHAIN-F correctly SHARING `.117` as their common terminal event (both are
discharged by the same AC-5 sweep) without being the same chain — a genuine shared-terminal
case, not a merge error, verified by re-reading AC-5's sweep (`.117`) itself naming both PROP
and FC-2 in separate bullets.

### 7.3 SERIES (dated-arc, rule 28; three span or are contained within one shard, two are
shard-1-only, one is shard-2-only)

**SERIES REPAIR-ARC (spans both shards).** Seven links inside shard 1 — `.07`(r1) →
`.09`(r2) → `.11`(r3) → `.12`(r4) → `.13`(r5) → `.14`(r6) → `.15`(r7) — continued by shard
2's STATUS BLOCK ARC bullet (`.79`) and TERMINATED at the acceptance record (`.89`, PE8 CLEAN
→ PE9 CLEAN). **Nine members total when the two record-surface continuation points are
counted with the seven rounds.**

**SERIES GRADE-BOX (shard 1 only).** Six dated entries inside §S4.3: `.65`([r1]) →
`.66`([r2]) → `.67`([r3]) → `.68`([r4]) → `.69`([r6]) → `.70`([r7]). **Deliberate GAP at r5**
— no r5 grade-box entry exists, and `[r6,F6-1]` (folded into `.69`) says so explicitly. This
merge preserves the gap; it must not be silently interpolated.

**SERIES MACHINE-LEG (shard 1 only).** `.03`(sealed leg, r0) → `.04`([r1] second leg added)
→ `.05`([r2] A7 amendment) → `.06`([r3]+[r4], one unit).

**SERIES ARCHIVE-STATUS (shard 2 only).** Three dead status lines, in source order: `.85`(r1)
→ `.86`(r2, carrying two nested r3 brackets) → `.87`(r3). All three DEAD; recorded so the
three archive corrections (`.84`) point at the right member.

**SERIES CERTIFIER-ARC (shard 2 only).** The (Φ₁-OPACITY) program, one unit per dated
adjudication: **AC-1** (`.95`, containment) → **AC-4** (`.103`–`.108`, narrowing) → **AC-5**
(`.111`–`.117`, discharge). Shares one ledger row (“row 19”, RX22/Y13) with CHAIN-P.

### 7.4 Boundary-unit resolution (merge rule 4/7)

No unit is split across source line 1167/1168, the shard boundary. The break falls at a `##`
section boundary (§S4.3's grade box closes at 1166; §S5's heading opens at 1168) and is
independently corroborated by ITERLAWN's fold annex, which cites LIFTCORNER's S5 display as
“lines 1168–1176 at acceptance” (X14/Y10) — the exact span shard 2's `.73` occupies.

### 7.5 Range-edge audit

Material shard 1 REFERENCES but does not emit (all six correctly homed in shard 2): the §S5
consequence display and its `[r4,F4-6]` strike (`.73`, `.74`); the delivery/discrepancy/
disposition paragraphs (`.75`–`.77`); the five-line STATUS BLOCK and the three archived
STATUS LINEs (`.79`–`.87`); the footer dating record (`.88`); the acceptance record (`.89`,
`.90`); FC-1 and FC-2 (`.91`, `.92`); the E1 adjudication's five findings including AC-1/AC-2/
AC-3 (`.93`–`.100`); AC-4 (`.101`–`.108`); AC-5 (`.109`–`.117`); the three orchestrator-
verification parentheticals (`.101`, `.109`, `.118`). Material shard 2 RECEIVES from shard 1
that changes no statement: CHAIN-A and CHAIN-B's terminals are quoted inside the archive
corrections (`.84`), and shard 1's `.13`'s F5-1 edit is what shaped `.81`'s PROVED line. **No
material is referenced by neither shard, and no material is emitted twice as a live
statement** (the archive's three dead lines are emitted once, explicitly marked DEAD, per
resolution rule 2).

---

## 8. Self-audit and OPEN-CALLs (consolidated; 12 raw calls, 1 exact duplicate found and
merged, 11 contiguous below)

### 8.1 Resolved compilation calls

- The effective-text rule is DERIVED (the note states none) from four agreeing source facts
  in shard 1 and two additional ones specific to shard 2's append-only discipline, with the
  strike-and-replace / dated-append distinction reconciled at the acceptance boundary (line
  1433).
- **Four independent FREEZE PREDICATES were separated** (§1 above) — one more than either
  shard alone reports (shard 1 sees three; shard 2 sees four counting only its own range).
  Conflating FREEZE-2/FREEZE-3 is the note's own documented error (`[r3,F-C]`); conflating
  FREEZE-1/FREEZE-1a would silently widen the acceptance-time freeze to cover text that was
  not yet frozen at that date.
- Four internal supersession CHAINs (shard 1) and five cross-shard CHAINs were reconstructed
  with TERMINALs named and verified pairwise distinct (§7.2). **CHAIN-P's reversal is the
  note's central law**: a compilation that stopped at AC-1 would record PROP as suspended,
  which is false at HEAD.
- Five SERIES were declared with explicit membership and order, including the r5 GAP in
  SERIES GRADE-BOX, invisible without per-entry emission, and the two shard-spanning series
  (REPAIR-ARC, and CHAIN-P/CHAIN-F's shared terminal event across the CERTIFIER-ARC).
- The scope split is THREE-way across the whole note: zero appends landed during shard 1's
  HOME range, one landed afterward (the ITERLAWN fold annex, independently verified twice),
  and ten inbound corrections were RECEIVED from the sol certification arc — a class neither
  predicate A nor B can hold.
- Every number in both shards was recomputed from primary artifacts or displayed algebra
  rather than transcribed; this merge's own fresh sample (§4.1–§4.2) adds a third independent
  zero-discrepancy pass. Two figures neither shard's source displays were supplied by the
  audits (shard 1's ENG-GATE count; nothing new from shard 2).
- **Seven exact cross-shard XREF duplicates and one near-duplicate were found and merged**
  (§4.1) — both shards independently re-verified several of the same cross-note facts because
  those facts matter on both sides of the shard boundary; none is a contradiction, all seven
  pairs agree exactly.
- **One duplicate OPEN-CALL was found** (shard 1's OPEN-CALL 3 and shard 2's OPEN-CALL 1 are
  the same underlying finding — the (Φ₁-OPACITY) program's unlanded status on ITERLAWN — at
  two different levels of completeness) and merged below as OPEN-CALL 3, retaining shard 2's
  fuller statement (it additionally covers AC-4, which shard 1's narrower framing, focused
  only on the FC-2 rider, had no occasion to name).
- **One arithmetic self-count error was found in shard 2's own text and corrected here**: shard
  2 asserts “fifteen” `[TRANSCRIBED — certifier]` units in two places (its rule-3 boundary
  finding and its own §8 numbering line), but its own cited ranges (`.22`–`.28`, `.31`–`.36`,
  `.39`–`.45`, i.e. 7+6+7) and a fresh header recount both give **20**. Recorded as a new
  source-defect finding at §1's genre note, not silently reconciled — the same discipline the
  precedent merge (EFF-HE3) applied to its own one genuine drift.
- All source artifacts, commits, run logs and designation XREFs cited by either shard were
  independently re-verified at merge time; zero negative-edge drift (§4.5).

### 8.2 OPEN-CALLs

**OPEN-CALL 1 — Does AC-1's suspension change anything the note itself still claimed?
FOR-0b.** `[r5,F5-1]` had already removed “and PROP's rung propagation” from the STATUS BLOCK
PROVED line on 2026-08-06, four days before AC-1, leaving “(5) PROP's rung-≥2 clause-(ii)
census is OWED” as the status of record. AC-1 (2026-08-12) then SUSPENDS “PROP's… S5's… and
FC-2's execution”. So AC-1's real targets are the S5 rider and the LANDED ITERLAWN annex, not
the note's own PROVED inventory. Whether the arc treats this as “AC-1 found a live overclaim”
or “AC-1 found a stale display F5-1 had already fenced” is a note-owner judgment; AC-1 does
not cite F5-1.

**OPEN-CALL 2 — The ENG-GATE check is undisplayed but load-bearing for the headline total.
FOR-0b.** §S3 reports “ENG-GATE 0 new (full=False disclosed)” and never gives its check
count; the committed artifact gives it as 1, and 25,409 does not reconcile without it.
Proposed disposition: a one-line minors-only rider giving ENG-GATE's count — compiler
suggestion, not source text; needs the note owner.

**OPEN-CALL 3 (MERGED — shard 1's OPEN-CALL 3 + shard 2's OPEN-CALL 1) — the entire
(Φ₁-OPACITY) program is unlanded on ITERLAWN, and the annex it repairs IS landed there.
FOR-0c/protocol — NEEDS ASVIN.** FC-2 executed the rider rewrite on ITERLAWN at `5054d69`
(X14/Y10, verified landed). AC-1 then SUSPENDED that execution; AC-4 additionally certifies
four ITERLAWN objects Φ₁-opaque; AC-5 reinstated the execution. **None of the three annexes is
recorded on ITERLAWN** (N1, N2, N4b — all re-verified 0 at merge time), and AC-5's own closing
parenthetical schedules the fix (“transcription-confirm owed”). The net state is favorable
(suspension lifted), so nothing on ITERLAWN is currently false — but (i) ITERLAWN's rung-≥2
propagation now depends on a lemma proved in another note's annex with no pointer, and (ii)
the S4.1/WELL-DEF/C_k/TRUNC/L6 opacity certification exists nowhere in the note it certifies.
Landing AC-4+AC-5 on ITERLAWN is a protocol action, not a compiler decision.

**OPEN-CALL 4 — three of the four cited script files carry no freeze predicate. FOR-0d.**
`.24`/`.25`/`.26` pin `grb_order2_check.py`, `iterlawlift_corner.py` and `strata_probe.py` by
line number; only `liftcorner_checks.py` is frozen (FREEZE-2). The note's arguments about
those files are structural and survive line drift, but the pins do not. Similarly, `.10`'s
four PE2-report line numbers are asserted at commit `3367f3c`, and the working-tree report is
not pinned to it.

**OPEN-CALL 5 — is `.15`'s standing rule (“quote counts only WITH THEIR UNIT AND COMMIT”)
corpus-binding? FOR-0d.** Stated inside one note's round record after three recurrences of the
same defect in that note; whether it is adopted corpus-wide is not a compiler decision.

**OPEN-CALL 6 — the `c′` census is commit-pinned and the note has moved. FOR-0b
(bookkeeping).** PE7's warrant counts 51 occurrences / 47 lines at `91f0cde`; at HEAD the
counts are 54/50. The three additional occurrences post-date that commit (the certifier
annexes) and none is a bare-`c′`-as-cocycle site by inspection, but no warrant of record
covers them. Classified `stale self-description`, not error.

**OPEN-CALL 7 — ILNRES has not ruled on the (a)/(b) alternative. FOR-0c.** `.77` flags an
ILNRES-side erratum candidate with a clean binary: is “at any level” (a) a scope fence — the
Φ₁ corner is all of NR-1 — or (b) a live conditionality — NR-1 has a fifth member and
ILNRES S7's completeness sentence needs amending? Verified unanswered at merge time
(`grep -cF 'LIFTCORNER' ILNRES...` = 0). A live DAG edge, not a footnote.

**OPEN-CALL 8 — does AC-5's e₀ = 1 termination argument reach ITERLAWN's fenced DEV-1 corner?
FOR-0b/0d.** ITERLAWN's (RM-m) STATUS box fences m = 1 at `{e₀=1 ∧ d₀≥2}` as open (Y18);
AC-5's (T2) proof asserts termination at e₀ = 1 via the lex measure. Two readings — AC-5
narrows the fence, or AC-5's argument is confined to the strict-excess division it needs —
and neither text decides. LIFTCORNER's own corner is unaffected either way (e₀ ≥ 2 by the S4
setting; δ₁ = 1 empty at e₀ = 1).

**OPEN-CALL 9 — PE3's blast-radius finding lives only inside dead archive text. FOR-0b.** The
r3 STATUS LINE (`.87`, DEAD) records that PE3 found READ-EQ's one pass sits entirely in the
deg a = 0 stratum, where the repaired proof shows there are no q-children at all — a
substantive fact bounding the arc's only CRITICAL's blast radius, appearing nowhere in the
live text. Proposed disposition: a one-line minors-only rider; compiler suggestion, needs the
note owner.

**OPEN-CALL 10 — PE9's p = 7 leg is unpinned. FOR-0b (bookkeeping).** The acceptance record
cites a fresh-instance leg at p = 7 outside the sealed battery's roster (p ∈ {2,3}) and the
children generator's roster (p ∈ {2,3,5}) — the note's best generalization evidence, backed by
no committed artifact, only the PE9 report. Disposition `UNPINNED`. Committing the p = 7 run
would close it.

**OPEN-CALL 11 — (T4) cites (T3), which it does not use. FOR-0b (wording).** AC-5's (T4)
citation names (T1) and (T3); the inequality actually needs the quotient-weight bound
displayed immediately above (T3) and (T1) — (T3) itself (the prescribed READ) enters only at
interface clause 4. The arithmetic is correct (recomputed at `.114`); the citation names the
wrong neighbour. Since the annex is “transcribed unaltered”, a correction would have to be a
rider, not an edit — a note-owner call.

### 8.3 Fidelity audit (compile-time, mechanical)

Every CANONICAL STATEMENT in §3 is a verbatim quotation from `LIFTCORNER_2026-08-08.md`, or is
explicitly marked `[ASSEMBLED]` (nine units total: `.07`, `.09`, `.11`, `.12`, `.14`, `.15`
from shard 1's seven round records; `.84`, `.86`, `.105` from shard 2's archive preamble and
AC-4's five-stage proof), or is an out-of-range quotation from an AC/FC annex explicitly
attributed to it (`.34`'s effective statement from AC-2, `.55`'s from AC-3). Truncation is
marked `…` at every occurrence. No
quantifier, index, inequality, direction, row number, tag number, or scope was altered
anywhere in either shard's transcription, independently re-checked by this merge against a
further five source spans (§4.2). No table was prosified; the note's four source tables
(`.22`, `.39`, `.103`'s dual emission) are reproduced as tables. Cross-file quotations were
each independently verified at count 1 under whitespace normalization where they span a
source line break; three are recorded as NEAR-MISS per v3 rule 15 rather than suppressed or
falsely emitted as clean.

---

EFF-LIFTCORNER MERGED: 118 statements.
