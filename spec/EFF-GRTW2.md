# EFF-GRTW2 — CANONICAL EFFECTIVE-SPECIFICATION (MERGED)

**COMPILED-BY: opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). CODEX CROSS-READ OWED (post-reset) — neither shard, and no fold performed by this merge run, has been through an adversarial pass; that obligation is inherited whole.**

## 1. Merge header

**Source note:** `lean/notes/openmath/GRTW2_PROOF_2026-08-08.md` (1632 lines).

**HEAD blob hash:** `ef6af0a5f8734d04d3d5d5c67135b8ec9e481fa0` — cited identically by both
source shards' headers, and independently confirmed by fresh `git hash-object` against
the working-tree file at merge time (2026-08-14):

```
$ git hash-object lean/notes/openmath/GRTW2_PROOF_2026-08-08.md
ef6af0a5f8734d04d3d5d5c67135b8ec9e481fa0
```

**No divergence found — this was the merge run's STOP condition and it did not trigger.**
Both shards additionally record the file's last-touching commit as `8584db40`.

**Compilation context:** `spec/EFF_TEMPLATE_v2.md` AT HEAD (rules 1–28).

**Merged from:** `spec/EFF-GRTW2-s1of2.md` (HOME lines 1–1260; 43 statements, 17 xrefs
verified, 6 open calls), `spec/EFF-GRTW2-s2of2.md` (HOME lines 1261–1632; 17 statements,
8 xrefs verified, 5 open calls). **60 statements, 25 raw XREF/artifact citations, 11 raw
open calls total before merge-time dedup.** This file supersedes the two shards as the
citable unit for all downstream consumption; any consumer citing `EFF.GRTW2.*` from this
point on cites the contiguous IDs below, not the shard-local `EFF.GRTW2.sKof2.*` IDs. The
two shard files are **not deleted** — they remain the run-of-record trace of the sharded
compilation, and in particular remain the place where each unit's own §6 BOUNDARY
SELF-AUDIT entry (which unit-boundary candidate was chosen and why) lives in full; this
merged file's own boundary section (§7) carries forward only the cross-shard edge list
and the format-level conclusions, not the individual boundary arguments each shard
records for its own range.

### SHARD-MAP (old shard-local ID → new contiguous ID)

Shard 1's offset is **0** (its own numbering, 01–43, is already contiguous from 1).
Shard 2 carries a **+43** offset (01–17 → 44–60). Every `EFF.GRTW2.sKof2.NN` occurrence —
full form (including the short `s1of2.NN` form used inside three `TARGETS:` fields) and
the bare `` `.NN` `` shorthand used throughout each shard's own prose — has been rewritten
below to the new contiguous ID, under the disambiguation rule this merge recovered from
the shards' own citation discipline (the same rule `spec/EFF-HE3.md`'s merge settled on,
checked against GRTW2's own citation style before being applied):

> **A bare `` `.NN` `` reference defaults to its OWN shard's unit** (the shard the
> surrounding text lives in). **This default is overridden only where the text itself
> names the other shard** — a `shard 1`/`shard 2` label — **and that override persists
> across a comma- or slash-separated list of `.NN` tokens within the same still-labeled
> clause, resetting at the next `·`/`;` field-separator or at an explicit competing
> label** (e.g. shard 2's own `in-range` marker, as in its predicate-C table row: "shard 1
> `.30`, `.32`, `.33`, `.38`, `.39`, `.40`; in-range `.02`" — the label governs the
> comma-list up to the `;`, where `in-range` resets to shard 2's own default).

**GRTW2's own citation style is more heavily labelled than HE3's**: shard 2 tags *almost
every* individual cross-shard bare ref with "shard 1" (rather than labelling a whole
paragraph once and relying on line-range disambiguation for the rest), which made this
merge's per-unit resolution mechanical rather than inferential — verified exhaustively,
unit by unit, that every un-labelled bare `.NN` in shard 2's own text resolves to a
shard-2-homed unit and every `shard 1 `.NN`` resolves to a shard-1-homed one, with zero
counter-examples.

**Shard 1, by contrast, never cites shard-2-homed material by a bare `.NN` at all** —
having been compiled before shard 2's temporary IDs existed, it cites forward exclusively
by **source-note line range, tagged `(shard 2)`** (52 distinct such citations, found by
exhaustive regex sweep). This merge resolved every one of them to its exact shard-2-homed
merged unit by cross-referencing the cited source-note range against shard 2's own
per-unit `CANONICAL STATEMENT` line span, using the table below:

| Shard-2 unit | Merged ID | Source lines |
|---|---|---|
| `.01` | `.44` | 1261–1327 |
| `.02` | `.45` | 1329–1330 |
| `.03` | `.46` | 1334–1353 |
| `.04` | `.47` | 1357 |
| `.05` | `.48` | 1359–1374 |
| `.06` | `.49` | 1376–1403 |
| `.07` | `.50` | 1405–1434 |
| `.08` | `.51` | 1436 |
| `.09` | `.52` | 1438 |
| `.10` | `.53` | 1440 |
| `.11` | `.54` | 1444–1457 |
| `.12` | `.55` | 1459–1476 |
| `.13` | `.56` | 1478–1531 |
| `.14` | `.57` | 1533–1560 |
| `.15` | `.58` | 1562–1594 |
| `.16` | `.59` | 1596–1612 |
| `.17` | `.60` | 1614–1632 |

Two ranges spanned more than one shard-2 unit (`1261–1330` → `.44`, `.45`; `1376–1440` /
`1405–1440` → `.49`–`.53`) and are rendered as multi-ID citations rather than forced onto
one unit. One irregular citation (`.09`'s "841 (fixed at E5, shard 2)") named the event by
description rather than by line range and was resolved to `.57` (E5 finding 3, the unit
whose own content is exactly that fix) by content match rather than line arithmetic. One
citation (`.05`'s "annexes 2026-08-08 and #3, shard 2") named three annexes by date/number
rather than by range and was resolved to `.49`, `.50`, `.53` (OPEN2ATTACK, SIGMALAW,
ANNEX #3 respectively — the three annexes that jointly prove/upgrade (OPEN-2a)'s forward
direction).

**A second, orthogonal exception, inherited from the GENHN/HE3 precedent:** a bare
`` `.NN` `` immediately following a citation of `spec/EFF-GENHN-s2of2.md` is **not a
GRTW2 ID at all** — it is a citation into GENHN's own (separately merged) shard numbering
and is left completely untouched. **Found once**, at shard 2's `.13` (merged `.56`):
"the same move GENHN's A2 obstruction records made (`spec/EFF-GENHN-s2of2.md` `.32`)" —
untouched by this merge. **Two further foreign citations, neither in `.NN` format and so
needing no rewrite at all**, name sibling shards' OPEN-CALL numbering directly: shard 1's
OPEN-CALL 2 and shard 2's OPEN-CALL 1 both cite `spec/EFF-GENHN-s2of2.md` OPEN-CALL 4 and
`spec/EFF-HE3-s2of2.md` OPEN-CALL 2 by name — left byte-identical, per the same
precedent (these describe what the *original shard files* said at compilation time; this
merge does not re-verify or re-point them against GENHN's/HE3's own now-completed merges,
since doing so would be a claim about another note's content, out of this deliverable's
scope).

Since shard 1's offset is 0, every bare `.NN` that resolves to a shard-1 unit keeps its
number unchanged by this merge; only bare refs that resolve to a shard-2 unit gain the
`+43` offset. The rewrite was performed unit by unit against this compiler's own reading
of both shards' full text (not a blind global substitution), then audited by exhaustive
regex sweep: **zero leftover `sKof2` substrings within the merged statement inventory
(§3)** — the handful that survive elsewhere in this header are deliberate quotations of
the original shard-local notation, illustrating the rewrite rule itself — and **zero
out-of-range renumbered IDs** (every resolved ID lies in 1–60, confirmed by an explicit
scan of every `` `.NN` `` token in the merged inventory).

### Header unification and blob-hash check

Both shards' front matter carries the **identical** compiled-by/cross-read-owed stamp
(reproduced verbatim above) and the identical HEAD blob hash; both independently record
the file's last-touching commit (`8584db40`) — confirmed by this merge against the
working tree rather than trusting the shards' mutual citation alone.

### Genre note (carried from both shards, verbatim discipline)

**GENRE: TAG-SPARSE PROSE PROOF with blockquoted clause displays, in-place strike-through,
and DEEPLY NESTED round brackets, shifting to an ACCEPTANCE RECORD + APPEND STACK +
CERTIFIER ADJUDICATION discipline in shard 2's range.** `grep -c '\tag{'` = **0** over the
whole note (re-verified fresh at merge time). The distinguishing feature of shard 1's
range is **bracket nesting depth**: a single sentence in the Grade cap (`.05`) carries
`[r1, F1]` inside which sits `[r2, P1]` inside which sits `[r3, PE3-P1]`, each superseding
the last — a CHAIN of **five** members, two of them out of range. Four repair rounds were
applied **in place** to a note that was then **accepted and frozen** (shard 2's range),
after which **five orchestrator annexes and four certifier corrections** were appended.
Reading rule for nested brackets (compiler-declared; the note states no rule, carried
unchanged from shard 1's header): in `X ~~Y~~ **[rN, F: Z]** **[rM, G: W]**`, later rounds
govern earlier ones and struck text is refuted; where a bracket itself contains a struck
sub-bracket, the innermost surviving text is current.

### Governing effective-text record (unified from both shards)

**FREEZE PREDICATES (rule 21 — THREE, all three stated identically in both shards' own
headers, and the third is the one that matters most for this note):**

**(F1) TEXT-FREEZE at acceptance.** Lines 1336–1337 (`.46`):

> "**THIS NOTE IS ACCEPTED at 2/2** — PE5 (ba2c47c, CLEAN; the 17-theorem
> Lean leg) and PE6 (9d8aba0, CLEAN; …)"

and the annex header at 1357 (`.47`): "## ANNEX (dated append; **the frozen body is not
edited**)", re-asserted by the sol append at 1456: "Everything above this heading is
byte-untouched by this append." **Before acceptance the four rounds r1–r4 were applied IN
PLACE** — each round block says "NOTE-ONLY" and the S-STATUS block (`.03`) records all
four.

**(F2) INSTRUMENT-FREEZE — the runner and both artifacts, byte-frozen from composition and
verified at every round.** Lines 68–70:

> "The runner `grt_w2_checks.py` (sha256
> 71f8fc90f7543fd3…, PE4-verified byte-identical across working tree, 5463f2a, and HEAD)
> and both artifacts remain BYTE-FROZEN; r4 touches only this note."

**The freeze is verified FOUR separate times by four different hostile passes** (`.41`–
`.43`, `.44`), including one recovery: r1 records "a stray working-tree drift on
`grt_w2_checks_results.json` (elapsed_s only, left by a prior pass's re-run) was restored
to the committed bytes before this round's edits" (`.41`). **That is the most carefully
policed instrument freeze in this sweep.**

**(F3) ACCEPTANCE-SCOPE ENUMERATION — what the acceptance covers is enumerated, and an
OPEN BOX is inside it.** Lines 1344–1350 (`.46`):

> "**WHAT IS ACCEPTED**: the (ξ,w) covariance closed form, HR-REC, W2-L0–L3, W2-C1
> (chamber-qualified), W2-C2, W2-C3 at its honest grade (proved-to-first-twist 38/44 = 36
> derived + 2 instance-warranted; measured above), LEMMA W2-ID1 (forward direction, with
> the converse's counter-instance displayed), and **W2-OPEN-2/OPEN-2a as the note's
> fenced OPEN box — the weld's one open lemma, accepted AS A BOX, not as a theorem.**"

**This is a distinct freeze predicate from (F1)**: (F1) freezes the *bytes*; (F3)
enumerates *which claims the 2/2 covers*, and it explicitly accepts an OPEN box as a box.
A chapter cut that reads "ACCEPTED 2/2" without (F3)'s enumeration would over-report.
**Shard 1's own §6.3 proposed adding an `acceptance-scope enumeration` member to rule
21's freeze-predicate list**, and shard 2's own `.59` supplies the corpus's own worked
instance for it: a certifier finding was rejected *precisely because* the acceptance
enumerated its scope. Both shards independently converge on this proposal; this merge
carries it forward as unresolved template feedback (§8).

**EFFECTIVE TEXT = the whole 1,632-line file exactly as written** — `[r1]`–`[r4]` already
landed in place in shard 1's range (struck text is REFUTED text preserved for the record,
never current), READ AS CORRECTED by every later dated annex/correction that names an
earlier sentence, with no earlier sentence ever deleted. **Nine dated corrections land
inside shard 1's HOME range** — five orchestrator annexes and four certifier corrections —
each applied at its unit and listed in §7 below.

### Scope of record — mandatory THREE-predicate split (unified from both shards)

**A. ABSORPTION / mathematical supply SET.** The three clauses of the W-2 junction
(`.04`): admissible representative, unit covariance with the (ξ,w) closed form,
ψ-transport through the tower. Supporting: **W2-L0/L1/L2/L3, TH-BASE, HR-REC, W2-C1a,
W2-C1, W2-C2, W2-C3, W2-ID1, W2-T3E**, with three fenced boxes — **W2-BOX-1** (the scalar
form off (C-coll)), **W2-OPEN-1** (the value layer), **W2-OPEN-2/OPEN-2a** (the chain
level above a first twist) — and one review-owed convention fence (`.26`). Shard 2 adds:
the note's **acceptance and its scope enumeration** (`.46`); **two upgrades of the
shard-1-homed open box** — (OPEN-2a) NARROWED then PROVED (`.49`, `.50`, `.53`); **four
certifier corrections** that supersede or withdraw shard-1 claims (`.55`–`.58`); **two
owed folds discharged** (`.48`).

**B. APPEND / consumption PROTOCOL scope — what GRTW2 lands on other notes.** **Nothing,
and the note says so twice in identical words**: "**accepted texts are NEVER edited by
this unit**" (`.41`, `.42`). It *records fold implications for the orchestrator* and
leaves them owed. **Both were later EXECUTED — by the orchestrator, not by this note**
(`.48`): GRTJB §0M row 15 at `5054d69`, WELDMASTER (M4) at the annex's own fold. **Zero
dated consumption appends are claimed landed on any supplier or consumer by this note,
and none is invented here.**

**C. INBOUND CORRECTIONS RECEIVED — six streams (consolidated from both shards'
predicate-C tables), all landing inside shard 1's HOME range (four applied while shard 1
was itself being drafted, two dated appends applied afterward from shard 2's own range):**

| # | Source | Landing form | Count | In-range targets |
|---|---|---|---|---|
| 1 | W2-PE1 @ `083adff` | in-place `[r1]` | 2 GAP + 5 minor | `.05`, `.18`, `.22`, `.23`, `.24`, `.29`, `.30`, `.36`, `.37`, `.38`, `.39`, `.40` |
| 2 | W2-PE2 @ `79e796b` | in-place `[r2]` | 2 GAP + 1 minor | `.05`, `.13`, `.26`, `.30`, `.31`, `.33`, `.38`, `.40` |
| 3 | W2-PE3 @ `9bd938f` | in-place `[r3]` | 1 GAP (minor) | `.05`, `.31`, `.32`, `.33`, `.38`, `.40`, `.02` |
| 4 | W2-PE4 @ `e92cb22` | in-place `[r4]` (`.44`) + riders | 1 GAP + 1 minor | `.30`, `.32`, `.33`, `.38`, `.39`, `.40` |
| 5 | Orchestrator annexes (2026-08-08 ×5) | dated appends, `.48`–`.53` | — | `.33` (OPEN-2a narrowed, then PROVED), `.40` |
| 6 | **sol certification C5/E5 (2026-08-12)** | dated appends, `.54`–`.60` | 1 CRITICAL + 3 REAL + 1 ARTIFACT | `.25` (W2-C1-CORR), `.29` (W2-C3 equivalence scope), `.33` (the key-carry index; the OPEN-2 status withdrawal), `.38` |

### Resolution rules applied (merged; each shard's own numbered rule-list is a restriction
of this one to its HOME range — nothing below is dropped, only consolidated)

1. Shard 1's lines 1–1260 supply the base statements; `[r1]`–`[r4]` tags are
   already-landed base text; struck spans are refuted-but-preserved and are reproduced
   with their strike markers intact wherever load-bearing.
2. **The out-of-range annexes/corrections never edit; they quote and rider.** Nine land
   in range, all physically drafted in shard 2's range (§7 below).
3. **Three out-of-range events CHANGE a status in range and must be applied**: (i) the
   Σ-LAW annex + its supplier upgrade **PROVE (OPEN-2a)'s forward direction at m ≥ 2**;
   (ii) the E5 finding 1 **WITHDRAWS** the annex sentence that had over-read that proof
   as closing W2-OPEN-2; (iii) E5 finding 2 **SUPERSEDES** THEOREM W2-C1's universal
   reading. Each is a `license`, `replacement` or `counter re-reading` at its unit.
4. **The acceptance-scope enumeration (F3) governs every grade sentence in range**,
   several of which predate it and read "counter 0/2".
5. Out-of-range statements are not emitted as separate shard-1 units merely because they
   resolve in-range text; §10, the ACCEPTANCE RECORD, all five annexes and the four
   certifier corrections are homed exactly once, in shard 2 (`.44`–`.60`).
6. Every cited commit hash was verified with `git cat-file -t`; every cited artifact was
   verified to exist; truncated hashes are marked **UNPINNED** (rule 23).
7. **HOME is determined by an edit's destination, not physical drafting location** — the
   same rule T1's, HE7's and HE3's merges used. All nine shard-1-targeting corrections are
   physically drafted in shard 2's range; §7 below verifies each resolves to exactly one
   place in the merged inventory.

### Quotation and table discipline

Unchanged from both shards: CANONICAL STATEMENTs are verbatim source quotations (no
`[ASSEMBLED]` statements in either shard); strike-through and nested brackets are
reproduced exactly; truncations marked `…`; every statement unit carries `FORM:`. The two
source tables in shard 1's range (`.37`'s machine bracket, `.38`'s claims table) and the
LaTeX displays in shard 2's range (the certifier corrections, reproduced as source bytes)
are transcribed per rule 14/rule-1; `.38` additionally carries one clearly-labelled
compiler-added "TERMINAL grade at HEAD" column, preserved as such. Compiler-authored
ledgers (XREF tables, consumption ledgers, TEETH inverse tables, the SERIES/edge tables of
§7) are marked `[TABLE — compiler ledger]` and are not source statement units.

---

## 2. NON-IMPORTS (consolidated from both shards; dedup marked)

`[TABLE — compiler ledger, consolidated from shard 1 §4 (14 rows) and shard 2 §4 (10
rows) = 24 raw rows, 0 dedup pairs found → 24 distinct rows below]`

**Dedup count for this section: 0.** As with HE3's and GENHN's merges, no fence in either
GRTW2 shard restates a near-identical negative claim already stated by the other shard —
shard 1's fences are about the note's own literature-consumption/scope boundaries (§1–§6
material); shard 2's are about the acceptance's scope, the annex stack's non-closures, and
the certifier's own non-claims. Every row below is specific to its own shard and asserted
once.

| Fence | Explicit material NOT imported, NOT proved, or NOT claimed | Source |
|---|---|---|
| New print transcription | "this note adds **NO new print transcription**" — the transcription risk is the sealed probe leg's | s1 `.06` |
| An independence proposition | "**no independence proposition is among this note's consumed anchors**"; taking one "would be a NEW consumption … with its own transcription and audit" | s1 `.06`, `.33`, `.34` |
| The ℓ-orbit reading | "nothing downstream consumes the orbit reading — clause 3 removes the ambiguity by transporting the type"; the section "stands review-owed" | s1 `.26` |
| The scalar form off (C-coll) | W2-BOX-1: "the exact law is (HR-REC), **the scalar form is proved only on (C-coll)**" | s1 `.23` |
| The chain level above r₀ | W2-OPEN-2: "**OPEN**, instance-confirmed"; "not derivable from the accepted corpus (four-route adjudication displayed)" | s1 `.33`, `.34` |
| The value layer | W2-OPEN-1: "**instance-confirmed, not proved**"; the carry analysis "is NOT claimed here" | s1 `.35` |
| Per-pair overflow identification | `[r1, F7]`: "asserted per-mechanism and **not machine-keyed pair-by-pair**" | s1 `.36` |
| Independent TW-STRICT | "TW-STRICT is SAME-ADJACENT evidence given TW-ADM … **NOT two independent 44/44 legs**" | s1 `.30`, `.37` |
| W-1 at orders ≥ 3 | "**W-1 at orders ≥ 3 is NOT advanced**"; "Nothing here … advances W-1's operator dictionary beyond the level-1 value dictionary" | s1 `.05`, `.39` |
| W-5, W-6..W-9, J-D, Lean | "**NOT unlocked**: W-5 …, the J-C block W-6..W-9 (no gr claim anywhere here; BLOCKED-ON-CARRIER-TIE stands), J-D counts, and every Phase-B Lean obligation. The P0 application gate stands." | s1 `.39` |
| Accepted-text edits (other notes) | "accepted texts are **NEVER** edited by this unit" (stated twice in shard 1) | s1 `.41`, `.42` |
| A pinned selection rule | the ξ = 1 preference is deliberately NOT pinned, because "a pinned preference would misdescribe the note's own machine bracket off-roster" | s1 `.27`, `.32`, `.43` |
| The converse | "the converse stays UNCLAIMED"; UNPROVED at every m | s1 `.31`, `.32`, `.33` |
| PARI on equal characteristic | "F_p[[t]] rows have no PARI leg (displayed deferral, inherited)" | s1 `.40` |
| Restating W2-OPEN-2's premise | PE4 §ADJ: "restating would change the box's mathematical content; no consumer needs the clause off-roster — **NO finding**" | s2 `.44` |
| Operative change at r4 | "this round changed no operative statement — **display brackets only**" | s2 `.44` |
| What the acceptance covers | (F3)'s enumeration — an OPEN box is accepted **as a box, not as a theorem** | s2 `.46` |
| Editing the frozen body (this note's own text) | "the frozen body is not edited"; "Everything above this heading is byte-untouched" | s2 `.47`, `.54` |
| Closure of the box | "Direction: box NARROWED …, **NOT closed**; W2-OPEN-2's chain-level claim above r₀ and the converse's UNPROVED status are unchanged" | s2 `.49`, `.50` |
| Σ-LAW ⟹ W2-OPEN-2 | "**The Σ-LAW supplies an evaluator identity on the shared-below perimeter; it contains no estimate for those key-change cross-terms.** Therefore no implication … has been displayed." | s2 `.55` |
| A universal scalar orbit | "Otherwise HR-REC alone gives **no ξ-conjugate representative theorem**"; "**No new lemma derivable from the displayed material forces geometricity**" | s2 `.56` |
| Equal augmented valuations | "**No equality of the augmented valuation functions** induced by the two different key representatives is claimed" | s2 `.58` |
| PE5/PE6 over later annexes | "they are **not** represented as clean passes over future orchestrator annexes" | s2 `.59` |
| Discharge of the E5 repairs | "all four repairs folded, **awaiting sol discharge (cert3)**" | s2 `.60` |


---

## 3. Statement inventory (60 units, contiguous, in source order)

### EFF.GRTW2.01  [changes-record]

**CANONICAL STATEMENT:** verbatim, line 1.

**FORM:** display (H1 heading).

> “# GRTW2 — W-2, THE LIFT JUNCTION, in its corrected three-clause form: admissible representative + unit covariance (the (ξ,w) closed form) + ψ-transport threaded through the tower”

**CONDITIONALITY:** “in its **corrected** three-clause form” refers to the probe's falsification of W-2's byte-equality branch (`.04`). The headline is untouched by every round and every append (verified) — **the only title in this sweep that needed no rider.** Its three clauses' *grades*, however, all moved: clause 1 is superseded outside (C-coll) by W2-C1-CORR (`.25`); clause 2's scalar form is boxed off (C-coll) (`.23`); clause 3 is re-scoped proved-to-first-twist/measured-above (`.30`) and its equivalence wording is superseded (`.29`).

**DERIVATION:** Index of `.04`, `.25`, `.18`, `.29`.

**RESOLUTION TRACE:** statement line 1 · the clause grades 95–129 (`.05`) · out-of-range supersessions 1484–1531, 1568–1594.

**TEETH:** NONE (headline).

---

### EFF.GRTW2.02  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 3–8.

**FORM:** bold-headed paragraph with an in-place strike-through.

> “**Unit:** W-2 COMPOSER (the first weld-junction composition of the Q4 campaign;
> per the corrected target of the probe verdict, ledger 874d26b). **Genre:
> PROOF NOTE at attempt grade (acceptance counter 0/2; no gate fires; ~~no
> acceptance arc opened by this note~~ **[r3, o2: r0 composition-time wording,
> superseded — the acceptance arc is OPEN; S-STATUS below]**), with
> sealed-runner machine brackets.**”

**CONDITIONALITY:** **`STALE-SELF-DESCRIPTION` (rule 26) on “acceptance counter 0/2”.** The `[r3, o2]` strike fixed one half (the arc IS open); the other half — the counter — is superseded by the out-of-range ACCEPTANCE RECORD: **2/2, ACCEPTED** (1336). `SUPERSESSION KIND: as-of scoping`. SERIES `GRTW2-GRADE-ARC`: member 1 = this line (0/2); member 2 = S-STATUS (`.03`, 0/2 after four rounds); members 3–6 = the four round-block Freeze paragraphs (`.41`–`.43`, `.44`, all 0/2); **member 7 = the ACCEPTANCE RECORD (2/2, TERMINAL, `.46`)**.
**One observation worth preserving:** the `[r3, o2]` strike is an *ungraded observation* (“o2”), not a finding — the note fixed a stale parenthetical two hostile passes had seen and not flagged.

**DERIVATION:** Status record.

**RESOLUTION TRACE:** statement 3–8 · S-STATUS 10–70 · acceptance 1334–1353 (`.46`).

PIN: ledger `874d26b` ✓ commit.

**TEETH:** NONE.

---

### EFF.GRTW2.03  [changes-record] · SERIES: GRTW2-GRADE-ARC, member 2 of 7

**CANONICAL STATEMENT:** verbatim, lines 10–70 (the `[r4]` S-STATUS block — the note's own complete arc narrative, 61 lines).

**FORM:** bold display block, one sentence per arc step, with parenthetical evidence at each.

> “**[r4] S-STATUS (CURRENT): attempt grade, acceptance counter 0/2 (ZERO clean
> passes), FOUR hostile passes RUN and FOUR repair rounds applied. Arc:
> composed at 5463f2a → W2-PE1 (`GRTW2_passPE1_report.md`, 083adff — 0
> CRITICAL + 2 JUSTIFICATION GAPS + 5 minor, NOT CLEAN; core mathematics
> CONFIRMED by full independent re-derivation; machine leg bit-identical,
> 6,403/0, exit 0) → r1 (8d5e3fa, NOTE-ONLY: the W2-C3 HONEST RE-SCOPE —
> proved to each chamber's first ξ ≠ 1 junction, MEASURED above it — with the
> open box W2-OPEN-2 after a four-route derivability adjudication; the W2-C1a
> chamber qualifier; minors F3–F7; round block §7) → W2-PE2
> (`GRTW2_passPE2_report.md`, 79e796b — 0 CRITICAL + 2 JUSTIFICATION GAPS +
> 1 minor, NOT CLEAN; the four-route adjudication HELD at source under a
> deliberate fifth-route hunt; machine leg byte-identical; fresh leg 16/16 at
> m = 1 plus hand T3B/T3F r = 4) → r2 (ffa1e57, NOTE-ONLY: **P1** — LEMMA
> W2-ID1 displayed (§5.2), the m ≥ 2 case folded into W2-OPEN-2 as its premise
> sub-clause (OPEN-2a), the grade sentence scoped to the instance census;
> **P2** — the [r1, F6] §4.3 sign flip REVERTED to the r0 sign t ↦ t − k·u_i,
> faithful to tex 1431's literal Def-`t(i)`, the naming conflation split at
> §2.3; **P3** — W2-OPEN-2's premise pairing corrected to Φ_{q−1}; round
> block §8) → W2-PE3 (`GRTW2_passPE3_report.md`, 9bd938f — 0 CRITICAL + 1
> JUSTIFICATION GAP (minor, CONFIRMED by construction), NOT CLEAN; W2-ID1's
> statement and proof CONFIRMED sound by re-derivation; (OPEN-2a) confirmed
> exactly the m ≥ 2 step the warrant needs; the 36+2 census recomputed exact;
> the P2 revert verified faithful at source; machine leg re-run exit 0,
> 6,403/0, bit-identical mod timing; FRESH full-roster leg — own tower-field
> arithmetic vs the committed ledger modulo the support stabilizer — 22/22
> plus the I4B r = 5 boundary reproduced from scratch) → r3 (79d1d9c,
> NOTE-ONLY: **P1** — the two-sided "identification PROVED at m = 1" claims
> SCOPED to the proved direction at all four sites: LEMMA W2-ID1 proves
> recorded ξ = 1 ⟹ byte-equal at m = 1 (so NO byte-divergence strictly below
> the first recorded twist); the CONVERSE — recorded ξ ≠ 1 ⟹ byte-RED — is
> UNPROVED at every m, riding the never-pinned recorded-pair selection rule,
> and PE3's class-pin m = 1 counter-instance to it under the sealed scan's
> own enumeration-order selection (K₁ = F₄, ψ₁ = y³ + ζ, e₀ = 1: byte-equal
> junction, recorded pair (ζ, 1); roster-invisible at the g ≤ 2 builder
> limit) is RECORDED at §5.2 as the lemma's honest boundary; converse flag
> added inside W2-OPEN-2's premise; the §5.2 warrant, (OPEN-2a), and the
> 36+2 census re-checked — each consumes ONLY the proved direction; plus the
> two ungraded observations (o1 WM line drift, o2 the stale Genre
> parenthetical); round block §9) → W2-PE4 (`GRTW2_passPE4_report.md`,
> e92cb22 — 0 CRITICAL + 1 JUSTIFICATION GAP (minor) + 1 minor, NOT CLEAN;
> everything r3 set out to do verified done correctly and faithfully, edit
> site by edit site; the counter-instance re-derived TRUE from scratch by
> own field arithmetic; the W2-OPEN-2 converse flag adjudicated SUFFICIENT —
> NO finding; machine leg re-run exit 0, 6,403/0, results JSON byte-identical
> incl. elapsed_s; FRESH selection-geography leg 33,408/0 over 4,173 monic
> irreducibles × 7 fields — the r3 disclosure condition confirmed the EXACT
> characterization, W2-ID1's forward direction 29,223 grid points / 0
> violations) → r4 (this round, NOTE-ONLY: **P1** — the one-directional
> scoping COMPLETED across the species: the three same-species surfaces the
> r3 sweep missed (§6.3(d)'s carry item, the §5.2 (OPEN-2a) opening gloss,
> §6.4's [r2] record) scoped to the proved direction, one clause each, PLUS
> the sweep-completing sites found by this round's full-note grep (the §6.2
> W2-ID1-row appositive (PE4 o-d), the adjacent W2-OPEN-2-row label, the
> [r1, F1] block's roster-instance qualifier (PE4 o-b)); **P2** — the footer
> dateline extended (r3 + r4); plus o-c (the `orbit_scan` line figure
> 135–163) and o-e (the counter-instance chamber's 3-read extension
> precision); round block §10). A repair round is NOT a pass, so the
> counter stays 0/2; W2-PE5 — a fresh hostile pass on THIS post-r4 text — is
> the next acceptance attempt. The runner `grt_w2_checks.py` (sha256
> 71f8fc90f7543fd3…, PE4-verified byte-identical across working tree, 5463f2a,
> and HEAD) and both artifacts remain BYTE-FROZEN; r4 touches only this note.**”

**CONDITIONALITY:** **`STALE-SELF-DESCRIPTION` on “counter 0/2 (ZERO clean passes)” and “W2-PE5 … is the next acceptance attempt”** — PE5 and PE6 both returned CLEAN and the note is **ACCEPTED at 2/2** (1336–1339, `.46`). Everything else in the block is a faithful record and is confirmed by the four round blocks (`.41`–`.43`, `.44`).
**Three properties of this arc make it unusual and worth preserving:**
(i) **Every pass ran a FRESH LEG on a route the previous passes had not used** — PE2's 16/16 at m = 1 plus hand T3B/T3F; PE3's own tower-field arithmetic at full roster scope (22/22 + the I4B r = 5 boundary from scratch); PE4's exhaustive selection-geography map (33,408 checks / 4,173 monic irreducibles × 7 fields). **That is four independent instruments across four passes.**
(ii) **One finding was ADJUDICATED AWAY**: PE4 found the r3 converse flag “SUFFICIENT — NO finding”, i.e. a hostile pass declining to raise something it had standing to raise.
(iii) **The arc contains a REVERT**: r1's F6 sign fix was reverted at r2 as unfaithful to the named source, with anti-re-flip records installed in both brackets (`.13`, `.26`).

*Arithmetic audit (rule 22).* Four passes, four rounds ✓. Finding counts: PE1 `0C + 2G + 5m` = 7; PE2 `0C + 2G + 1m` = 3; PE3 `0C + 1G` = 1; PE4 `0C + 1G + 1m` = 2 ✓ — **monotonically decreasing severity and count across the arc** (7 → 3 → 1 → 2), and **zero CRITICALs at every pass** ✓. The machine leg is `6,403/0` at every re-run ✓ four times ✓, consistent with (F2).

**DERIVATION:** Arc record.

**RESOLUTION TRACE:** statement 10–70 · round blocks 1052–1117 (`.41`), 1121–1193 (`.42`), 1197–1257 (`.43`), 1261–1330 (`.44`, `.45`) · acceptance 1334–1353 (`.46`).

XREF: `GRTW2_passPE1_report.md` ✓ present · `GRTW2_passPE2_report.md` ✓ · `GRTW2_passPE3_report.md` ✓ · `GRTW2_passPE4_report.md` ✓ — 4/4.
PINS: `5463f2a` ✓ `083adff` ✓ `8d5e3fa` ✓ `79e796b` ✓ `ffa1e57` ✓ `9bd938f` ✓ `79d1d9c` ✓ `e92cb22` ✓ — 8/8 commits.
**UNPINNED (rule 23):** the runner sha256 `71f8fc90f7543fd3…` is **truncated** at every one of its five occurrences in the note. The file exists; the version is not verifiable from the note.

**TEETH:** four fresh legs across four passes, plus the frozen 6,403/0 runner re-run at each. **Disposition: executable regression on four decorrelated instruments.**

---

### EFF.GRTW2.04  [theorem]  — the Object and the three clauses

**CANONICAL STATEMENT:** verbatim, lines 72–93.

**FORM:** bold-headed paragraph + a blockquoted three-clause display.

> “**Object:** the blueprint junction **W-2** (`docs/in-progress/
> GRT_WELD_BLUEPRINT_2026-08-08.md` §3.2), restated after the probe
> (`lean/notes/openmath/GRTWELD_PROBE_2026-08-08.md`) falsified its
> byte-equality branch: for every realized principal-read OM type chain in the
> [ILN]† S0.1 class pin,
>
> > **(CLAUSE 1, admissible representative)** the harness canonical
> > ε-corrected lift Φ_{m+1} is a GMN Def-2.12 admissible key-polynomial
> > representative at every level — of the ξ-CONJUGATE residual class under
> > the pinned (P-ell) convention, of the type itself exactly when the
> > junction character is support-trivial;
> > **(CLAUSE 2, unit covariance)** the slot ratio between the harness lift
> > and the classifier's print-convention key is a pure z-monomial character
> > ξ^j in the slot index, with the per-level (ξ, w) an explicit function of
> > the read data (closed form in §3.4);
> > **(CLAUSE 3, ψ-transport)** conjugating each deeper residual ψ through
> > the recorded (ξ, w) BEFORE the next lift makes the full tower transport:
> > on the transported chain the harness lift is a STRICT Def-2.12
> > representative at every level, no junction ever degenerates to a
> > weight/support split, and every probed value-layer statement of the
> > corpus holds verbatim on the transported classifier lifts (the probe's
> > 96 F3 violations all turn GREEN).”

**CONDITIONALITY:** **All three clauses are qualified by the Grade cap (`.05`) and two are further superseded out of range.**
(a) **Clause 1's “at every level”** is chamber-qualified at `[r1, F2]` (`.24`) and its **scalar-orbit content is SUPERSEDED outside (C-coll)** by THEOREM W2-C1-CORR (1484–1531, `.56`). `SUPERSESSION KIND: replacement`.
(b) **Clause 2's “pure z-monomial character ξ^j”** holds unconditionally at m = 1 and on (C-coll); off (C-coll) only the exact recursion is claimed (`.18`(c), `.23`).
(c) **Clause 3's “at every level”** is re-scoped to proved-to-first-twist / measured-above (`.30`), and its **“MacLane-equivalent”/“same induced valuation data” wording is SUPERSEDED** by the ledger-equivalence re-display (1568–1594, `.58`). `SUPERSESSION KIND: replacement`.
(d) **The probe's falsification is the note's origin** — “restated after the probe … falsified its byte-equality branch”. So the note exists because a predecessor claim was refuted by machine.

**DERIVATION:** The three clauses are proved (at their graded scopes) at `.25`, `.18`/`.19`, `.29`.

**RESOLUTION TRACE:** statement 72–93 · grade cap 95–129 · out-of-range supersessions 1484–1531 (clause 1), 1568–1594 (clause 3).

ARTIFACT: `lean/notes/openmath/GRTWELD_PROBE_2026-08-08.md` — **verified present**; `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md` — **verified present**.

**TEETH:** the whole machine bracket (`.37`); clause 3's headline number is “the probe's 96 F3 violations all turn GREEN”, scored at TW-F3 684/684 (`.35`).

---

### EFF.GRTW2.05  [scope-record]  — the Grade cap

**CANONICAL STATEMENT:** verbatim, lines 95–129 (the Grade cap, with FIVE nested bracket layers).

**FORM:** bold-headed paragraph with strike-through and four levels of nested round brackets.

> “**Grade cap (read first).** Clause 2 is PROVED at attempt grade at m = 1
> junctions and, at m ≥ 2, proved-given-the-displayed-collapse-perimeter with
> the exact recursion (HR-REC) unconditional on the shared-key scope; clause 1
> is PROVED at attempt grade on the same perimeter ~~(its two polygon legs
> unconditionally)~~ **[r1, F2] (its two polygon legs at every junction whose
> below-junction chain is byte-shared with the harness chain — the HARNESS-side
> line content is level-unconditional; the GMN v_r/polygon reading carries the
> chamber qualifier of LEMMA W2-C1a as repaired)**; ~~clause 3's chain-level
> statements are PROVED at attempt grade given clauses 1–2~~ **[r1, F1]
> clause 3's chain-level statements are PROVED at attempt grade given clauses
> 1–2 UP TO AND INCLUDING the first ξ ≠ 1 junction of each transported chamber
> (38 of the roster's 44 junction-levels) and MEASURED above it (the remaining
> 6 junction-levels: TW-ADM/TW-STRICT 44/44, TW-STRICT SAME-adjacent), riding
> the displayed open bridging lemma W2-OPEN-2 (§5.2)** **[r2, P1: the proved
> scope's boundary is keyed to the first RECORDED ξ ≠ 1 junction; ~~that this
> coincides with the first BYTE-divergence is PROVED at m = 1 (LEMMA W2-ID1,
> §5.2) and at m ≥ 2 is W2-OPEN-2's own premise sub-clause (OPEN-2a)~~
> **[r3, PE3-P1: one direction only — LEMMA W2-ID1 (§5.2) proves at m = 1
> that recorded ξ = 1 ⟹ byte-equal, i.e. NO byte-divergence strictly below
> the first recorded twist, and at m ≥ 2 that same forward direction is
> W2-OPEN-2's premise sub-clause (OPEN-2a); the CONVERSE (recorded ξ ≠ 1 ⟹
> byte-RED) is UNPROVED at every m — it rides the unpinned recorded-pair
> selection rule, with PE3's off-roster m = 1 counter-instance under the
> sealed scan's own selection recorded at §5.2]** — on the
> roster the identification is instance-exact (recorded ξ ≠ 1 ⟺ byte-RED at
> 22/22 walked junctions; every below-r₀ junction byte-GREEN — PE2's
> recomputation), so the 38/44 proved-scope census is fully §3-derived except
> where an m ≥ 2 recorded-trivial junction sits below (this roster: I4A/I4B
> at r = 5), where it stands as instance evidence riding (OPEN-2a)]**, and
> its value-layer
> statement (the corpus battery
> on transported lifts) is **machine-confirmed instance evidence, displayed as
> the open lemma W2-OPEN-1** — not a proven theorem. Nothing here fires the
> BLOCKED-ON-CARRIER-TIE gate, touches any accepted text, or advances W-1's
> operator dictionary beyond the level-1 value dictionary proved below.”

**CONDITIONALITY:** **This is the shard's deepest CHAIN and it now has FIVE members, two of them out of range.**

**CHAIN for clause 3's boundary (rule 25), in source order:**
1. **r0**: “clause 3's chain-level statements are PROVED … given clauses 1–2” — **struck**.
2. **`[r1, F1]`**: proved to each chamber's first ξ ≠ 1 junction (38/44), MEASURED above (6/44), riding W2-OPEN-2.
3. **`[r2, P1]`**: the boundary is keyed to the first RECORDED twist; the coincidence with byte-divergence is W2-ID1 at m = 1 and (OPEN-2a) at m ≥ 2 — **struck**.
4. **`[r3, PE3-P1]`**: **one direction only** — W2-ID1 gives forward (recorded ξ = 1 ⟹ byte-equal); the CONVERSE is UNPROVED at every m, with a counter-instance.
5. **Out of range — the Σ-LAW supplier upgrade (annexes 2026-08-08 and #3)**: **(OPEN-2a)'s forward direction at m ≥ 2 is PROVED at attempt grade** through an ACCEPTED supplier. So the two instance-warranted census entries (I4A/I4B r = 5) now ride a theorem, not instance evidence.
6. **Out of range — the E5 certifier correction (finding 2)**: THEOREM W2-C1's universal reading is **SUPERSEDED**, and the census is **honestly re-displayed as 37/44 theorem-derived + 1/44 individually scalar-orbit-confirmed (I4B r = 5) + 6/44 above-twist** (1527).
**TERMINAL: member 6 — the E5 re-displayed census 37 + 1 + 6.**

**So the census in this Grade cap (38/44 = 36 + 2) is SUPERSEDED TWICE**: first upward by the Σ-LAW (the 2 become derived), then re-partitioned by E5 (37 theorem-derived + 1 individually confirmed). `SUPERSESSION KIND: license` then `counter re-reading`.

*Arithmetic audit (rule 22), all three censuses recomputed and reconciled.*
- **The r2 census.** 44 junction-levels total; 38 at-or-below a first twist, 6 above ✓ `38 + 6 = 44` ✓. Of the 38: “36 (all strictly-below junctions at m ≤ 1) fully §3-derived via TH-BASE + W2-ID1, and 2 (I4A r = 5, I4B r₀ = 5) instance evidence” ✓ `36 + 2 = 38` ✓.
- **PE3's independent recount** (1205–1207): “36 fully derived = 16 r = 2 + 16 r = 3 + 4 r = 4” ✓ `16 + 16 + 4 = 36` ✓ **exact**, and the 2 instance-warranted are I4A/I4B r = 5 ✓.
- **The E5 census.** “**37/44 theorem-derived, 1/44 individually scalar-orbit-confirmed (I4B r = 5), and 6/44 above-twist**” ✓ `37 + 1 + 6 = 44` ✓. **Reconciliation with the r2 census:** the Σ-LAW upgrade moves I4A r = 5 from instance-warranted to derived (`36 + 1 = 37` ✓), and I4B r = 5 stays individually confirmed because **its scalar orbit is a boundary instance off (C-coll)** (`.23`) — a *different* reason from the (OPEN-2a) one. **The two censuses reconcile exactly, and the note never displays the reconciliation.** Recorded as a compiler finding.
- **Roster totals.** 16 towers with 44 junction-levels; §3.3(b) gives “the roster has 28 r ≥ 3 junctions, of which 6 … are marked SKIP”, and TH-BASE covers 16 r = 2 junctions ✓ `28 + 16 = 44` ✓ **the two decompositions agree.**
**Every census reproduces and the three of them reconcile.**

**Two further clauses of the cap, both load-bearing:**
(e) **“Nothing here … advances W-1's operator dictionary beyond the level-1 value dictionary proved below.”** — the charge's named item; see `.39` and OPEN-CALL 3.
(f) **“Nothing here fires the BLOCKED-ON-CARRIER-TIE gate, touches any accepted text”** — the note's own no-append fence (header §B).

**DERIVATION:** Grade declaration; each clause's grade is at its own unit.

**RESOLUTION TRACE:** statement 95–129 · censuses recomputed at 1074, 1155–1158, 1205–1207 · out-of-range supersessions 1405–1440 (Σ-LAW), 1484–1531 (E5 finding 2).

XREF: `GRTJC_PROOF_2026-08-08.md:TR-3′-GEN` — grep-verified count **8** (the W-1-adjacent open dictionary; see `.34`, `.39`).

**TEETH:** TW-ADM/TW-STRICT 44/44 (`.37`), with TW-STRICT reclassified **SAME-adjacent given TW-ADM** — i.e. the two 44/44 legs are **not independent**, and the note says so.

---

### EFF.GRTW2.06  [fence]  — Literature consumption (the faithfulness discipline)

**CANONICAL STATEMENT:** verbatim, lines 131–147.

**FORM:** bold-headed paragraph, a list of tex-anchored print objects.

> “**Literature consumption (faithfulness discipline).** The classifier side is
> consumed as LITERATURE from the GMN print `docs/references/HigherNewton.tex`
> ("Newton polygons of higher order in algebraic number theory"): Proposition
> `construct` (tex 1166–1258, hypothesis V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1})),
> Theorem `phir` (tex 1257–1283, with eq. `vrphir`), the representative
> Definition (tex 1285 — the project's "Thm 2.11/Def 2.12" cite per
> `docs/GMN_citations.md`), Definition `t(i)` (tex 1431), Definition
> `rescoeff` (tex 1447), Definition `defresidual` (tex 1497), Proposition
> `propertiesv` items 3/4 (tex 1028), and the Bézout convention ℓ_r h_r −
> ℓ′_r e_r = 1 with **no pinned representative** (tex ~1291). Every print
> formula used below is quoted with its tex anchor; the machine transcription
> of these formulas is the SEALED probe leg (`grt_weld_probe.GmnLeg`,
> commit 55f7416), imported verbatim by this unit's runner — this note adds
> NO new print transcription. Where the print's convention is genuinely
> underdetermined (the unpinned-ℓ orbit), this is said explicitly and
> parametrized (§4.3); the ℓ-orbit reading of Def 2.12 remains a convention
> analysis, review-owed (probe fence inherited).”

**CONDITIONALITY:** **A closed consumption list with tex anchors, and the closure is load-bearing three times:**
(i) **“this note adds NO new print transcription”** — the transcription risk sits entirely in the sealed probe leg at `55f7416` ✓ commit verified.
(ii) **The list is used as a FENCE in the derivability adjudication** (`.34` route 4): “no independence proposition is among this note's consumed anchors”, and W2-OPEN-2's alternative discharge route is explicitly “a NEW consumption under the faithfulness discipline, with its own transcription and audit”.
(iii) **The r1→r2 sign revert turned on reading two of these anchors at source** (`.13`, `.26`): tex 1431 (`Def-t(i)`) vs tex 1201 (`Prop-construct`'s child twist). **The faithfulness discipline is what let PE2 adjudicate the revert** — the anchors were specific enough to check.
**The `no pinned representative` clause (tex ~1291) is the origin of §4.3's review-owed fence** (`.26`).

**DERIVATION:** Declaration.

**RESOLUTION TRACE:** statement 131–147 · the anchors used at 223–231, 233–245, 254–284, 320–336, 507–526, 528–573 · the fence's use 849–877 (`.34`).

ARTIFACT: `docs/references/HigherNewton.tex` — **verified present**; `docs/GMN_citations.md` — **verified present**.
PIN: `55f7416` ✓ commit · `a6f7653` ✓ commit (the GmnLeg line, cited at `.40`).

**TEETH:** NONE (declaration). Its discipline is what makes `.13`/`.26`'s revert auditable.

---

### EFF.GRTW2.07  [instrument-record]  — the machine bracket header

**CANONICAL STATEMENT:** verbatim, lines 149–156.

**FORM:** bold-headed paragraph.

> “**Machine bracket:** `verification/openmath/grt_w2_checks.py` (this unit;
> outputs `grt_w2_checks_output.txt`, `grt_w2_checks_results.json`; 6,403
> samples, 0 violations, 17 check families all GREEN, teeth caught) layered
> on the sealed probe artifacts (`grt_weld_probe*`; 1,391 samples). Roster:
> the probe's 16 towers (ℤ₂/ℤ₃/F₂[[t]]/F₃[[t]], 2–4 reads, wild p | e_j rows,
> d₀ = 2 rows, g ≥ 2 rows, flat rows, I4A/I4B/I4C verbatim) + the 5 concrete
> quartic/cubic shapes with fresh extraction; PARI `factorpadic`/
> `idealprimedec` external anchors.”

**CONDITIONALITY:** **The roster's `g ≥ 2 rows` clause is the coverage limit that makes PE3's counter-instance roster-invisible** — the Tower builder implements only `g ∈ {1,2}` (`.32`), and the counter-instance needs `g_m ≥ 3`. **So the roster's own construction is why the converse looked true on it.** That is a `signed vacuity disclosure` of the sharpest kind and the note makes it at `.32`.
**`F_p[[t]]` rows have no PARI leg** — a displayed deferral inherited from the probe (`.40`).

**DERIVATION:** Instrument description.

**RESOLUTION TRACE:** statement 149–156 · the family table 942–957 (`.37`) · the roster limit 766–772 (`.32`) · the PARI deferral 1024–1027 (`.40`).

ARTIFACT: `verification/openmath/grt_w2_checks.py` ✓ · `grt_w2_checks_output.txt` ✓ · `grt_w2_checks_results.json` ✓ — 3/3 present.

**TEETH:** the 17 families at `.37`.

---

### EFF.GRTW2.08  [hypothesis]  — §1.1, the two legs

**CANONICAL STATEMENT:** verbatim, lines 164–181.

**FORM:** section body with an indented ASCII lift display.

> “Harness: the [ILN]† S0.1 class pin verbatim (`ITERLAWN_PROOF_2026-08-08.md`
> S0.1–S0.2): DVR O, uniformizer π, reads (e_j, h_j, g_j), j = 0..n, with
> e_j, h_j, g_j ≥ 1, gcd(e_j, h_j) = 1; normalized Bézout pairs ℓ_j h_j +
> ℓ_j′ e_j = 1 with 0 ≤ ℓ_j < e_j (so ℓ_j = 0 ⟺ e_j = 1); residue chain
> K_{j+1} = K_j[z_{j+1}]/(ψ_j), ψ_j monic irreducible with ψ_j(0) ≠ 0;
> weights γ₁ = h₀, γ_{j+1} = e_j·w_jΦ_j + h_j, w_jΦ_j = e_{j−1}g_{j−1}γ_j;
> the standard lift Φ₁ and the canonical ε-corrected lifts
>
>     Φ_{m+1} = Σ_{k ≤ g_m, ψ_{m,k} ≠ 0} C_k·Φ_m^{e_m k},   C_{g_m} = 1,
>     C_k := realize_m( ε_m(β_k)^{−1}·ψ_{m,k},  β_k ),   β_k := (g_m−k)γ_{m+1},
>
> with ε_m(β) := z_m^{ℓ′_{m−1}s − ℓ_{m−1}u}, (s,u) := eq12(β; e_{m−1},
> h_{m−1}), ε₀ := 1; harness reads R_m v and weights w_m per S0.2 (level-m
> read of f at weight λ: dev by Φ_{m−1}, grid s(λ) + je_{m−1}, packed
> C_j = ε_{m−1}(β_digit)·R_{m−1}v(A) into Σ_j C_j z_m^j).
>
> Classifier: the GMN print objects above, transcribed fresh in the sealed
> probe leg.”

**CONDITIONALITY:** Inherited hypothesis set, consumed **verbatim** from an accepted package ([ILN]† S0.1–S0.2). Unconditional as a hypothesis. **Two clauses are load-bearing everywhere below:** `ψ_j(0) ≠ 0` (used at `.24`'s initial-slot attainment and at `.31`'s j = 0 evaluation) and `ℓ_j = 0 ⟺ e_j = 1` (which makes `A_m = 0 ⟺ e_{m−1} = 1`, `.19`, and drives the T3E carry-inertness at `.36`).

**DERIVATION:** Hypothesis.

*Arithmetic audit (rule 22).* `ℓ_j h_j + ℓ_j′ e_j = 1` with `0 ≤ ℓ_j < e_j`: at `e_j = 1` the only choice is `ℓ_j = 0` ✓ and then `ℓ_j′ = 1` ✓ — **so `ℓ_j = 0 ⟺ e_j = 1`** ✓ (the ⟸ is immediate; the ⟹ holds because `ℓ_j = 0` forces `ℓ_j′e_j = 1` hence `e_j = 1` ✓). Consequently `A_m := ℓ_{m−1}g_{m−1}γ_m = 0 ⟺ e_{m−1} = 1` ✓ **matching `.19`'s display** ✓.

**RESOLUTION TRACE:** statement 164–181 · untouched by every round and append (verified).

ARTIFACT: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md` — **verified present**.

**TEETH:** NONE (hypothesis).

---

### EFF.GRTW2.09  [definition]  — §1.2, the P-index dictionary

**CANONICAL STATEMENT:** verbatim, lines 185–194.

**FORM:** section body, a run-on identification list.

> “GMN level i = harness read i−1 throughout: (e_i, h_i, f_i)^GMN =
> (e_{i−1}, h_{i−1}, g_{i−1})^har; ψ_i^GMN = ψ_{i−1}^har; F_i = K_{i−1};
> z_i^GMN = z_i^har (both the class of y in F_{i+1} = K_i); ℓ_i^GMN ≡
> ℓ_{i−1}^har (same normalized representative under (P-ell)); GMN keys
> φ_i = harness Φ_{i−1}; valuations v_i^GMN = harness w_{i−1} (same
> recursion, `propertiesv` item 3 vs the S0.2 weight recursion; in
> particular v_i(φ_i) = w_{i−1}Φ_{i−1} and v_{i+1}(φ_i) = γ_i^har);
> residual operators: GMN order-q residual R_q (dev by φ_q = Φ_{q−1})
> pairs with the harness level-q read R_q v. Pins (P-ell)/(P-lift)/
> (P-root)/(P-index) as sealed in the probe docstring.”

**CONDITIONALITY:** **The identification `φ_i^GMN = Φ_{i−1}^har` is the single most consequential line of §1**, and **getting it wrong twice caused two separate findings**: PE2's P3 (W2-OPEN-2's premise paired `φ_q^tw` with `Φ_q`; fixed to `Φ_{q−1}`, `.33`) and, four months of rounds later, **E5's finding 3** — “The prior P3 correction fixed the premise but **missed this later occurrence**” in the Equivalent sufficient form (1533–1560, `.57`). `SUPERSESSION KIND: replacement` at both sites. **Two independent misindexings of the same dictionary, one caught at r2 and one at the 2026-08-12 certification.**

**DERIVATION:** Definition (an index translation).

*Arithmetic audit (rule 22) of the degree argument E5 uses.* If one paired `φ_q` with `Φ_q`, then `deg Φ_q = e_{q−1}g_{q−1}·deg Φ_{q−1}` (from `.08`'s lift display: the top term is `Φ_m^{e_m g_m}`) ✓, while `deg φ_q = deg Φ_{q−1}` ✓ under the correct dictionary. So `deg Φ_q > deg φ_q` whenever `e_{q−1}g_{q−1} > 1` ✓, and `deg D_q < deg φ_q` would be impossible ✓ **exactly E5's argument** ✓ — and this compiler's recomputation confirms it. Under the correct pairing `Φ_{q−1} = φ_q + D_q`, both summands are monic of the same degree ✓ so `deg D_q < deg φ_q` is possible ✓.

**RESOLUTION TRACE:** statement 185–194 · the two misindexings 787 (fixed at r2, `.33`) and 841 (fixed at E5, `.57`).

**TEETH:** the P-index tie is exercised at every machine family; **CK-MM's 4,396 samples** are its sharpest test (`.13`).

---

### EFF.GRTW2.10  [definition]  — §1.3, the junction notation and the shared-key perimeter

**CANONICAL STATEMENT:** verbatim, lines 198–215.

**FORM:** bold-headed section body with two indented ASCII displays.

> “**The junction at level m+1** (1 ≤ m ≤ n; GMN r := m+2) compares the
> harness lift Φ_{m+1} with the print key φ_r built by Prop-`construct` +
> Thm-`phir` on the same type data. Both are
>
>     (key)^{e_m g_m} + (slot coefficients)·(key)^{e_m·j},  j < g_m,
>
> key = Φ_m = φ_{r−1}, slot j carrying weight β_j = (g_m−j)γ_{m+1}
> (harness) = the T-side ordinate data u_j = g_m γ_{m+1} − j·h_m, V_j =
> u_j − j e_m·w_mΦ_m (print; V_j = β_j — same integers, §2.1). The slot
> coefficients live at harness level m, values in K_m. A junction is
> **shared-key** if Φ_q^har = φ_{q+1}^cls byte-for-byte for all q ≤ m (the
> first-divergence perimeter). The three read-data quantities of the note:
>
>     A_m := ℓ_{m−1}·g_{m−1}·γ_m ∈ ℤ_{≥0}      (A_m = 0 ⟺ e_{m−1} = 1),
>     c₁ = z_m^{−A_m}   [THE Thm-phir constant: the print's
>          c₁ = (z_{r−2})^{−ℓ_{r−2}v_{r−1}(φ_{r−1})/e_{r−2}}, tex 1270,
>          since v_{r−1}(φ_{r−1}) = w_mΦ_m = e_{m−1}g_{m−1}γ_m],
>     c  = c₁^{e_m g_m}  [Thm-phir's residual scalar: R_{r−1}(φ_r) = c·ψ_{r−1}].”

**CONDITIONALITY:** **“shared-key” is the note's central scope predicate** — §3 is entirely inside it (`.15`), clause 1 is proved on it (`.25`), and the whole W2-OPEN-2 box exists because transported chambers leave it above `r₀` (`.30`, `.33`). **Unconditional as a definition**, and untouched by every round and append.
**Note the shared-key definition's own indexing**: “Φ_q^har = φ_{q+1}^cls” — which is `.09`'s dictionary written the other way (`φ_{q+1} = Φ_q`) ✓ consistent ✓. **This occurrence is correct**; the two that were wrong are at `.33`.

**DERIVATION:** Definition; the `V_j = β_j` identity is proved at `.11` (W2-L0).

*Arithmetic audit (rule 22).* `c₁ = z_m^{−A_m}` from the print's `c₁ = z_{r−2}^{−ℓ_{r−2}v_{r−1}(φ_{r−1})/e_{r−2}}`: with `r − 2 = m`, `ℓ_{r−2} = ℓ_{m−1}` (by `.09`'s `ℓ_i^GMN ≡ ℓ_{i−1}^har`) — **careful**: the note writes `z_{r−2}` and identifies it with `z_m`, and `z_i^GMN = z_i^har` ✓ so `z_{r−2} = z_m` ✓. Exponent: `ℓ_{m−1}·v_{r−1}(φ_{r−1})/e_{m−1}` with `v_{r−1}(φ_{r−1}) = w_mΦ_m = e_{m−1}g_{m−1}γ_m` ✓ gives `ℓ_{m−1}·e_{m−1}g_{m−1}γ_m/e_{m−1} = ℓ_{m−1}g_{m−1}γ_m = A_m` ✓ **exactly** ✓. And `c = c₁^{e_mg_m} = z_m^{−A_m e_m g_m}` ✓ — **which is what `.18`(a) and `.22` consume** ✓.

**RESOLUTION TRACE:** statement 198–215 · `V_j = β_j` proved 223–231 (`.11`) · consumed at 361–392, 394–411, 430–442.

**TEETH:** **CK-SLOT / CK-BYTE** ride these definitions; the `shared-key` predicate is what marks 6 junctions SKIP (`.15`).

---

### EFF.GRTW2.11  [lemma]  — LEMMA W2-L0 (grid/weight tie)

**CANONICAL STATEMENT:** verbatim, lines 221–231 (statement, proof and consequence — the note gives this lemma no blockquote).

**FORM:** `###`-headed section body (bold-headed lemma name in the heading, statement and proof in running prose).

> “The print's T-side initial abscissa (tex 1176: "the greatest side T
> contained in L whose end points have nonnegative integer coordinates";
> initial point (s,u)) equals the eq12 offset: s = ℓV mod e, u = (V − sh)/e.
> *Proof.* An abscissa x on L of slope −h/e and value V has integer ordinate
> iff xh ≡ V (mod e) iff x ≡ ℓV (mod e); the smallest nonnegative such x is
> ℓV mod e. ∎ Consequently the print's slot grid s + je and slot values V_j
> coincide with the harness grid and digit weights: V_j = u_j − (s+je_m)w_mΦ_m
> = (V − (s+je_m)γ_{m+1})/e_m = β-digit weight (expand γ_{m+1} = e_m w_mΦ_m +
> h_m). The two legs' polygons agree point-for-point at every junction slot.”

**CONDITIONALITY:** **Unconditional, and “used silently everywhere”** (the section title says so). Untouched by every round and append (verified). It is what licenses the `V_j = β_j` identification at `.10` and the “on-grid and on-line” hypothesis of HR-REC (`.16`).

**DERIVATION:** Quoted inline.

*Arithmetic audit (rule 22).* `xh ≡ V (mod e)` ⟺ `x ≡ ℓV (mod e)` requires `ℓh ≡ 1 (mod e)` ✓ — which is the Bézout relation `ℓh + ℓ′e = 1` ✓ from `.08` ✓. The smallest nonnegative solution is `ℓV mod e` ✓ **by definition of the mod-reduction** ✓. Integrality of `u = (V − sh)/e`: `V − sh ≡ V − ℓVh ≡ V(1 − ℓh) ≡ V·ℓ′e ≡ 0 (mod e)` ✓ **exact** ✓. **The lemma is correct.**

**RESOLUTION TRACE:** statement 221–231 · consumed at 206–209 (`.10`), 326–327 (`.16`), 496–503 (`.24`).

**TEETH:** Indirect — every family rides the grid tie; **CK-MM** (4,396) is the sharpest since it tests the integer identity that makes the two grids coincide.

---

### EFF.GRTW2.12  [lemma]  — LEMMA W2-L1 (the base builder) and COROLLARY TH-BASE

**CANONICAL STATEMENT:** verbatim, lines 235–252.

**FORM:** `###`-headed section body with an indented ASCII display, a proof, and a bold-headed corollary.

> “Let V ≥ e₁f₁v₂(φ₁) (GMN indexing; the print's own hypothesis) and
> φ(y) = Σ_{j<f₁} c_j y^j over F₁ = K₀. The print's order-2 construction
> (tex 1183–1190) P = Σ_j π^{u−jh₁}c_j(x)φ₁^{s+je₁} satisfies, in HARNESS
> semantics,
>
>     w₁(P) = V   and   R₁v(P) = φ(z₁) = Σ_j c_j z₁^j.
>
> *Proof.* The Φ₀-development of P is exactly the placed digits (deg c_j(x)
> < d₀). Digit at abscissa s+je₀ has level-0 weight u_j = u − jh₀, on the
> line by W2-L0. The level-1 read packs C_j = ε₀·R₀v(π^{u_j}c_j(x)) = c_j
> (ε₀ = 1; res at exact weight recovers the digit), so R₁v(P) = Σ c_j z₁^j. ∎
>
> **Corollary TH-BASE (r = 2 junctions byte-equal).** At the base junction
> both recipes place the same digits: harness C_k = realize₀(ψ_{0,k},
> (g₀−k)γ₁) = π^{(g₀−k)h₀}·lift(ψ_{0,k}); print slots π^{u_j}c_j(x)φ₁^{je₁}
> with c₁ = 1 (tex 1270, r = 2 case), u_j = (g₀−j)h₀, same digit lifts under
> (P-lift). Φ₁^har = φ₂^cls byte-for-byte. [Machine: probe F0 21/21; runner
> CK-SLOT r = 2 rows 16/16.]”

**CONDITIONALITY:** **TH-BASE is the base case of every ascending argument in the note** — it is why the 16 r = 2 junctions are byte-equal unconditionally, and it is one of the two ingredients (with W2-ID1) of the “36 fully derived” census entry (`.05`). Untouched by every round and append.
`ε₀ = 1` (from `.08`) is what makes the base collapse; **at r = 2 the whole covariance is trivial** (`c₁ = 1` at r = 2, tex 1270).

**DERIVATION:** Quoted inline.

*Arithmetic audit (rule 22).* At `r = 2` the Thm-`phir` constant is `c₁ = z_0^{−ℓ_0 v_1(φ_1)/e_0}`… the note says “c₁ = 1 (tex 1270, r = 2 case)” ✓ — consistent with `.10`'s formula at `m = 0`: `A_0 = ℓ_{−1}g_{−1}γ_0` is not defined, and the base has no lower level, so `c₁ = 1` ✓ by convention matching `ε₀ := 1` ✓. Digit match: harness `C_k = π^{(g₀−k)h₀}·lift(ψ_{0,k})` vs print `π^{u_j}c_j(x)` with `u_j = (g₀−j)h₀` ✓ **same π-exponent** ✓ and same lift under (P-lift) ✓ ⟹ byte-equal ✓. Machine: 21/21 + 16/16 ✓, and **16 = the number of r = 2 junctions** (one per tower, 16 towers) ✓ **matching `.05`'s census decomposition `16 r = 2`** ✓.

**RESOLUTION TRACE:** statement 235–252 · consumed at 686–687, 725–726, 1155–1157, 1205–1207.

**TEETH:** **probe F0 21/21 + CK-SLOT r = 2 rows 16/16.** Disposition: executable regression, exhaustive on the base junctions, with a foreign (probe) leg agreeing.

---

### EFF.GRTW2.13  [lemma]  — LEMMA W2-L2 (the Bézout bridge) with its `[r2, P2]` naming split

**CANONICAL STATEMENT:** verbatim, lines 256–284.

**FORM:** `###`-headed section body with a long struck-and-replaced naming parenthetical, an indented ASCII identity, a proof, and a reconciliation paragraph.

> “Fix a read (e, h) with normalized Bézout (ℓ, ℓ′), ℓh + ℓ′e = 1. Let V, u
> ∈ ℤ with u − V = kW for some k ∈ ℤ and W ∈ eℤ ∩ (the key weight, W = e·g·γ
> in every use). Put 𝔰 := ℓV mod e, u′ := (V − 𝔰h)/e, and T := (ℓu − 𝔰)/e
> ~~(the print's Def-`t(i)`/Prop-`construct` twist exponent at ordinate u)~~
> **[r2, P2] (the print's Prop-`construct` CHILD twist exponent at ordinate
> u — tex 1201, y^{(ℓ_{r−2}u_j − 𝔰_j)/e_{r−2}}, 𝔰_j the ideal on-line
> initial abscissa. NOT the print's Def-`t(i)`: tex 1431 arranges
> t_{r−1}(a)_i = (s_{r−1}(a) − ℓ_{r−1}·v_r(aφ_r^i))/e_{r−1} — the
> (s − ℓu)/e order, the near-negative of T. The r0 parenthetical conflated
> these two opposite-signed exponents under one name; PE1's F6 computed with
> the conflated alias and the r1 §4.3 sign flip implemented that finding —
> both reverted/split this round, see §4.3 [r2, P2]. The identity below and
> every use of it are about T itself and are machine-keyed (CK-MM 4,396);
> only this naming line was off.)**
> Then
>
>     T + (ℓ′𝔰 − ℓu′)  =  ℓ(u − V)/e  =  (ℓW/e)·k.
>
> *Proof.* ℓ′𝔰 − ℓu′ = ℓ′𝔰 − ℓ(V − 𝔰h)/e = 𝔰(eℓ′ + ℓh)/e − ℓV/e =
> (𝔰 − ℓV)/e. Add T = (ℓu − 𝔰)/e. ∎
>
> In the junction use W = w_mΦ_m, e = e_{m−1}, ℓ = ℓ_{m−1}: ℓW/e = A_m, so
> **ε_m(V)·z_m^{T} = z_m^{A_m·k}** as field elements — the print's total
> per-node twist and the harness ε-correction differ by the pure character
> z_m^{A_m·k} in the key exponent k. [Machine: CK-MM, 4,396 integer + element
> samples, 0 violations.] Reconciliation with the probe's T2A hand account:
> there the harness ε-exponent ℓu − ℓ′s = 4 and the print total twist
> ⌊ℓγ₂/e⌋ − ℓf₁h₁e₂ = 0 differ by A₁e₁g₁ = 4, ratio z₁^{−4} = z₁² — the
> k = e₁g₁ = top-slot instance of this identity.”

**CONDITIONALITY:** **The mathematics was never wrong; only a NAME was.** The `[r2, P2]` bracket says so explicitly: “The identity below and every use of it are about T itself and are machine-keyed (CK-MM 4,396); **only this naming line was off**.” **But the naming error propagated into a real sign flip** — PE1's F6 computed with the conflated alias, r1 implemented it, PE2 reverted it (`.26`). `SUPERSESSION KIND: replacement` (the naming parenthetical), with **anti-re-flip records installed in both brackets** so a future round cannot re-flip.
**This is the sweep's cleanest example of a citation defect causing a mathematical one**, and of the corpus catching and reverting it.

**DERIVATION:** Quoted inline; three lines of Bézout algebra.

*Arithmetic audit (rule 22), recomputed.*
- **The identity.** `ℓ′𝔰 − ℓu′ = ℓ′𝔰 − ℓ(V − 𝔰h)/e`. Common denominator `e`: `= (eℓ′𝔰 − ℓV + ℓ𝔰h)/e = (𝔰(eℓ′ + ℓh) − ℓV)/e = (𝔰 − ℓV)/e` ✓ using `ℓh + ℓ′e = 1` ✓ **exactly the displayed step.** Adding `T = (ℓu − 𝔰)/e`: `(ℓu − 𝔰 + 𝔰 − ℓV)/e = ℓ(u − V)/e` ✓ `= ℓkW/e` ✓ **exact.**
- **The junction specialization.** `ℓW/e = ℓ_{m−1}·w_mΦ_m/e_{m−1}` and `w_mΦ_m = e_{m−1}g_{m−1}γ_m` (from `.08`) ✓ gives `ℓ_{m−1}g_{m−1}γ_m = A_m` ✓ **exact** ✓.
- **The T2A reconciliation.** “harness ε-exponent ℓu − ℓ′s = 4 and the print total twist … = 0 differ by A₁e₁g₁ = 4, ratio z₁^{−4} = z₁²” — so `z₁` has order dividing… `z₁^{−4} = z₁²` ⟹ `z₁^6 = 1` ✓ consistent with a residue field of order dividing 7 or with `z₁` of order 6 or 3 or 2; the note gives no field, so no independent check. **Recorded as consistent-but-unverifiable.** The `k = e₁g₁` top-slot identification ✓ matches `.18`(a)'s `k_j = je₁` at `j = g₁` ✓.
**The identity and its specialization reproduce exactly.**

**RESOLUTION TRACE:** statement 256–284 · the naming split's twin 528–573 (`.26`) · consumed at 328–336, 368–372, 296–298.

XREF: `docs/references/HigherNewton.tex` — ✓ present (anchors tex 1201, tex 1431).

**TEETH:** **CK-MM — 4,396 integer + element samples, 0 violations**, the largest family in the bracket. **Disposition: executable regression, and it is what makes the “only the naming was off” claim checkable** — the identity was machine-verified throughout the sign confusion.

---

### EFF.GRTW2.14  [lemma]  — LEMMA W2-L3 (VD-1, the level-1 packed dictionary)

**CANONICAL STATEMENT:** verbatim, lines 288–304.

**FORM:** `###`-headed section body with an indented ASCII identity, a proof, and a closing structural paragraph.

> “For nonzero A ∈ O[x], deg A < deg Φ₁, on-line at β := w₁(A), let s₁(A) be
> the initial attained abscissa of its level-1 polygon and τ₁(A) :=
> (s₁(A) − ℓ₀β)/e₀. Then
>
>     z₁^{τ₁(A)} · R₁(A)(z₁)  =  ε₁(β) · R₁v(A),
>
> R₁ the print's order-1 residual (order-one `rescoeff`, c_i = red(a_i/π^{u_i})).
> *Proof.* Write s₁(A) = s + νe₀ (ν the first attained grid slot). The print
> coefficients equal the harness digit reads (both are res at exact weight),
> so R₁v(A) = z₁^ν·R₁(A)(z₁). And τ₁(A) − ν = (s − ℓ₀β)/e₀ = ℓ′₀s − ℓ₀u =
> the ε₁-exponent (the 𝔰 = s, k = 0 case of W2-L2's computation). ∎
> [Machine: CK-VD1, 156 samples, 0 violations.]
>
> This is the structural reason the harness ε-kit exists: **the ε-correction
> is exactly the print's t(i)-twist rewritten in eq12-canonical coordinates.**
> At levels ≥ 2 the dictionary is NOT a scalar gauge — it is a conjugation
> (§3.2) — and that conjugation is the entire content of the W-2 covariance.”

**CONDITIONALITY:** **This is the one thing the note delivers to W-1 IN PROVED FORM** — §6.3 says so: “W2-L3 is the level-1 value dictionary IN PROVED FORM (ε = the print twist in canonical coordinates)” (`.39`). **And its closing sentence is the note's own statement of why W-1 is not advanced further**: “At levels ≥ 2 the dictionary is NOT a scalar gauge — it is a conjugation”. See `.39` and OPEN-CALL 3.
**Out of range, W2-L3 is generalized**: the Σ-LAW annex (1416–1418, `.50`) says “the attained-start τ-normalization is W2-L3's mechanism at every level”, and OPEN2ATTACK's surviving open step was “the Σ-LAW at proof grade — **the level-m generalization of LEMMA W2-L3**” (1390–1391) — **since PROVED** as THEOREM SL-1 with an accepted supplier. `SUPERSESSION KIND: license` (the level-m generalization exists and is accepted).

**DERIVATION:** Quoted inline; the key step is `τ₁(A) − ν = (s − ℓ₀β)/e₀`, the `𝔰 = s, k = 0` case of W2-L2.

*Arithmetic audit (rule 22).* `s₁(A) = s + νe₀` ⟹ `τ₁(A) = (s + νe₀ − ℓ₀β)/e₀ = ν + (s − ℓ₀β)/e₀` ✓ so `τ₁(A) − ν = (s − ℓ₀β)/e₀` ✓. W2-L2 at `k = 0` (so `u = V = β`) and `𝔰 = s`: the identity reads `T + (ℓ′𝔰 − ℓu′) = 0`, i.e. `(ℓ₀β − s)/e₀ = −(ℓ′₀s − ℓ₀u′)` ✓ so `(s − ℓ₀β)/e₀ = ℓ′₀s − ℓ₀u′` ✓ **matching the displayed `ℓ′₀s − ℓ₀u`** (with `u = u′` at `k = 0`) ✓ **which is the ε₁-exponent from `.08`'s `ε_m(β) := z_m^{ℓ′_{m−1}s − ℓ_{m−1}u}`** ✓ **exact.**

**RESOLUTION TRACE:** statement 288–304 · consumed at 987–989 (`.39`) · generalized out of range 1390–1391, 1405–1434 (`.50`).

**TEETH:** **CK-VD1, 156 samples, 0 violations.** Disposition: executable regression. **This family is also the base of the Σ-LAW's level-m generalization**, so the same mechanism is now verified at 2,828 samples in an accepted supplier note.

---

### EFF.GRTW2.15  [scope-record]  — §3's shared-key scope

**CANONICAL STATEMENT:** verbatim, lines 310–316.

**FORM:** section preamble paragraph with an inline `[r1, F1]` bracket.

> “Throughout §3 the junction at level m+1 is **shared-key** (§1.3). This is
> the honest scope: above an interior byte-divergence the print chain
> multiplies by ITS OWN keys and the harness-read comparison is a different
> computation (the runner marks those junctions SKIP — exactly the probe's
> 6 above-twist rows; clause 3 removes them by transport **[r1, F1: at the
> re-scoped grade — the cure at the transported chamber's above-twist
> junctions is MEASURED, riding W2-OPEN-2; §5.2]**).”

**CONDITIONALITY:** **This preamble is where the 6 SKIP junctions enter, and they are the same 6 that remain OPEN at HEAD** (E5's “6/44 above-twist junctions riding W2-OPEN-2”, `.55`). The `[r1, F1]` bracket is the only correction; it downgrades “clause 3 removes them” to “MEASURED, riding W2-OPEN-2”. `SUPERSESSION KIND: scope-pin`.
**The scope is honest in a specific technical sense the note states**: above a byte-divergence the comparison is *a different computation*, not a failed one.

**DERIVATION:** Scope declaration.

*Arithmetic audit (rule 22).* 6 SKIP junctions ✓ = the “6 above-twist rows” ✓ = the “6/44 junction-levels above a first twist” at `.05` ✓ = “28 r ≥ 3 junctions, of which 6 … marked SKIP” at `.18`(b) ✓ **four independent occurrences of the same 6, all consistent** ✓.

**RESOLUTION TRACE:** statement 310–316 · the 6 at 383–385, 438–441, 680–682, 1074 · out-of-range 1527 (`.56`).

**TEETH:** the SKIP marking is itself a machine behaviour; **CK-BYTE records all 6 as samples with a byte verdict but no walk** (`.22`).

---

### EFF.GRTW2.16  [lemma]  — §3.1 (HR-REC), the exact transfer recursion

**CANONICAL STATEMENT:** verbatim, lines 320–336.

**FORM:** `###`-headed section body with two indented ASCII displays.

> “Let P = construct(r, V, φ) be a print output at GMN order r ≥ 3 (output
> harness level Q := r−1), children P_j = construct(r−1, V_j, φ_j) at slots
> k_j = s + je_{Q−1}, with the print's child prescription (tex 1213–1218)
>
>     φ_j(y) ≡ y^{T_j}·c_j(y)  (mod ψ_{Q−2}),   T_j = (ℓ_{Q−2}u_j − 𝔰_j)/e_{Q−2}.
>
> Then, digits being on-grid and on-line (W2-L0), the harness read obeys
>
>     (HR-REC)   R_Q v(P) = Σ_j ε_{Q−1}(V_j) · R_{Q−1}v(P_j) · z_Q^j ,
>
> and by W2-L2 the ε-and-twist pair collapses per node:
> ε_{Q−1}(V_j)·z_{Q−1}^{T_j} = z_{Q−1}^{A_{Q−1}·k_j}. With the base
> R₁v(construct(2, V, φ)) = φ(z₁) (W2-L1), the recursion computes the
> harness read of EVERY print construction from read data alone, with no
> polynomial arithmetic. [Machine: CK-REC — the semantic simulator equals
> the actual harness read at every node of every shared-key roster junction,
> 55 nodes, 0 violations.]”

**CONDITIONALITY:** **HR-REC is the note's most durable export.** It is in the accepted enumeration (F3: “**HR-REC**” is listed by name at 1345), it is untouched by every round and every append, and it is **independently re-derived by PE6** (“the functional-equation re-derivation of HR-REC”, 1338–1339, `.46`). **What it does NOT give** is the scalar normal form — E5's finding 2 turns exactly on this: “**Section 3.3(c) computes the slot ratios but does not prove they form a geometric progression**” (1480, `.56`). So HR-REC is exact and complete, and *insufficient* for the scalar orbit off (C-coll). See `.18`, `.25`.

**DERIVATION:** The recursion follows from the print's child prescription (tex 1213–1218) with the digits on-grid/on-line by W2-L0, and the per-node collapse is W2-L2.

*Arithmetic audit (rule 22).* The per-node collapse `ε_{Q−1}(V_j)·z_{Q−1}^{T_j} = z_{Q−1}^{A_{Q−1}k_j}` is exactly W2-L2's junction specialization ✓ (`.13`), with `u − V = k_jW` ✓ matching the slot geometry `k_j = s + je_{Q−1}` ✓. Base: `R₁v(construct(2,V,φ)) = φ(z₁)` ✓ = W2-L1 ✓ (`.12`). **So HR-REC is W2-L1 + W2-L2 assembled by induction** ✓ and needs nothing else ✓.

**RESOLUTION TRACE:** statement 320–336 · consumed at 340–341, 388–392, 520–524, 837–843 · re-derived out of range 1338–1339 (PE6) · its insufficiency 1478–1531 (E5 finding 2).

**TEETH:** **CK-REC — 55 nodes, 0 violations**, a *semantic simulator* equalling the actual harness read at every node. **Disposition: executable regression against an independent implementation of the same recursion.**

---

### EFF.GRTW2.17  [scope-record]  — §3.2, the conjugation and the collapse perimeter (C-coll)

**CANONICAL STATEMENT:** verbatim, lines 340–359.

**FORM:** `###`-headed section body with a display, two bulleted effects, and a bold-headed perimeter definition.

> “Unfolding one level: R_Q v(P) = Σ_j Θ_{Q−1}(V_j)·z_{Q−1}^{A_{Q−1}k_j}·c_j·z_Q^j,
> where Θ_{Q−1}(V_j) is the gauge accumulated in R_{Q−1}v(P_j) below. Two
> non-scalar effects appear for Q ≥ 3:
>
> * the **letter twist**: the j-dependent part of the character rides
>   z_{Q−1}^{A_{Q−1}e_{Q−1}·j}, i.e. the letter z_Q is effectively replaced
>   by ϑ_Q·z_Q with ϑ_Q := (junction character at level Q)^{−1} — the deeper
>   covariance re-appearing inside the dictionary;
> * the **mod-wrap**: the child prescription is the REDUCED representative
>   y^{T_j}c_j(y) mod ψ_{Q−2}, and reduction does not commute with y ↦ ϑy
>   unless ϑ acts trivially or the representative stays a monomial.
>
> **The collapse perimeter (C-coll):** every interior junction character is
> trivial as a field element — ξ_Q = 1 for 2 ≤ Q ≤ m (ξ_Q per §3.4's
> formula). On (C-coll) all wraps drop, every Θ is a z-monomial linear in
> its weight argument, and the whole dictionary is scalar per slot.
> Junctions with m = 1 have no interior levels: (C-coll) is vacuous there.
> Outside (C-coll) the law is still the exact recursion (HR-REC), which is
> closed in the read data; only the two-parameter SCALAR normal form below
> needs the perimeter. Boundary witness: §3.5.”

**CONDITIONALITY:** **(C-coll) is the perimeter every scalar claim in the note lives on**, and the two mechanisms that break it — the letter twist and the mod-wrap — are named precisely. **The mod-wrap is what the I4B r = 5 boundary witness exhibits** (`.23`) and what E5's finding 2 turns on (“HR-REC computes the three ρ_j but supplies no identity forcing this equation **when mod-wrap does not collapse**”, 1520, `.56`). Untouched by every round; **its scope is re-confirmed rather than corrected by E5**.
**“(C-coll) is vacuous at m = 1”** is what makes W2-C2(a) and W2-ID1 unconditional (`.18`, `.31`).
**One honesty item recorded at `.27`:** “whether (C-coll) survives into each transported chamber is NOT tracked” — so above `r₀` the recorded pair is the orbit scan's per-instance value, not the formula.

**DERIVATION:** One unfolding step of HR-REC.

**RESOLUTION TRACE:** statement 340–359 · the boundary witness 446–466 (`.23`) · the transport honesty item 697–700 (`.30`) · E5's use 1478–1531 (`.56`).

**TEETH:** **CK-SLOT's 22 non-SKIP samples include the non-perimeter ones**, “there the sim prediction is the recursion, not the scalar form” (`.18`(b)) — so the machine distinguishes the two regimes.

---

### EFF.GRTW2.18  [theorem]  — THEOREM W2-C2 (the slot-ratio law), (a)/(b)/(c)

**CANONICAL STATEMENT:** verbatim, lines 363–392.

**FORM:** `###`-headed section with a definition paragraph and three bold-lettered clauses, each with a proof and a machine bracket; clause (b) carries an `[r1, F3]` count correction.

> “At a shared-key junction at level m+1 define the slot ratio ρ_j :=
> (level-m read of the print slot P_j) / (level-m read of the harness slot
> C_j), j < g_m with ψ_{m,j} ≠ 0 (the harness read of C_j is
> ε_m(β_j)^{−1}ψ_{m,j} by REALIZE R3).
>
> **(a) m = 1 (unconditional).** ρ_j = c · z₁^{A₁e₁·j}. *Proof.* By W2-L1
> the print slot reads to φ_j(z₁) = z₁^{T_j}·c·ψ_{1,j}; multiply by
> ε₁(V_j)ψ_{1,j}^{−1} and apply W2-L2 with u_j − V_j = k_j·w₁Φ₁, k_j = je₁
> (top junction has s = 0 since V = e₁g₁·... ≡ 0 mod e₁... V = e_m g_m
> γ_{m+1}·(e-divisible): s = 0). ∎ [Machine: CK-SLOT-M1, all 16 r = 3
> junctions exact.]
>
> **(b) general m on (C-coll).** ρ_j = c · Θ_m(V_j) · z_m^{A_m e_m·j} with
> Θ_m the collapsed gauge (linearized recursion of §3.4); the ratios are
> geometric in j and the (ξ, w) normal form of §3.4 holds. *Proof at attempt
> grade:* induction on the level through (HR-REC), all wraps dropping on
> (C-coll); the linearization step (replacing 𝔰(V) = ℓV mod e by ℓV) changes
> the value by a power of the trivial interior character. ∎ [Machine:
> CK-SLOT — sim-predicted ratios equal the actual slot ratios at ~~ALL 24~~
> **[r1, F3] all 22** shared-key junctions r ≥ 3 **(the roster has 28 r ≥ 3
> junctions, of which 6 — exactly the probe's above-twist rows — are marked
> SKIP and carry no shared-key comparison; CK-SLOT's 44 samples = 16 r = 2
> rows + 28 r ≥ 3 rows, the ratio law checked on the 22 non-SKIP)**,
> including the non-perimeter ones (there the
> sim prediction is the recursion, not the scalar form); 0 violations.]
>
> **(c) exact general law.** At every shared-key junction the slot ratios
> are computed by (HR-REC) + W2-L1/L2 — a finite explicit recursion in the
> read data. This is the general closed form; (a)/(b) are its scalar
> specializations. [Machine: CK-SLOT under (c) reading, 0 violations.]”

**CONDITIONALITY:**
(a) **is unconditional and is in the accepted enumeration** (F3 lists “W2-C2”).
(b) **holds on (C-coll) only** — and this is exactly the boundary E5's finding 2 sharpens: **(c) computes the ratios but does not prove them geometric**, so “the general scalar orbit asserted in W2-C1 does not follow from HR-REC” (1480, `.56`). `SUPERSESSION KIND: scope-pin` on how (c) may be consumed. **W2-C2 itself is NOT superseded** — E5 supersedes W2-C1's universal reading, and its consumer sweep says “W2-C2(a), W2-ID1, HR-REC, and the §3.4 scalar display on (C-coll) survive unchanged” (1526, `.56`) ✓.
(c) **The `[r1, F3]` count correction is one of three in the same finding** (`.22`, `.41`): `24 → 22` shared-key r ≥ 3.

*Arithmetic audit (rule 22), the count decomposition recomputed.* “CK-SLOT's 44 samples = 16 r = 2 rows + 28 r ≥ 3 rows” ✓ `16 + 28 = 44` ✓ **matching the family table's `CK-SLOT … 44`** ✓ (`.37`). “28 r ≥ 3 junctions, of which 6 … SKIP” ⟹ `28 − 6 = 22` non-SKIP ✓ **exactly the corrected figure** ✓. And `44` here is the same 44 as the junction-level census at `.05` ✓ — **the two 44s coincide**, which the note does not state. Recorded.
*The (a) proof's `s = 0` claim.* `V = e_m g_m γ_{m+1}` is divisible by `e_m`, and `s = ℓV mod e_m` ⟹ `s = 0` ✓ **exact** ✓ (the displayed parenthetical is garbled with an ellipsis but the arithmetic is right).

**DERIVATION:** Quoted inline for all three clauses.

**RESOLUTION TRACE:** statement 363–392 · the closed form 394–411 (`.19`) · E5's scope correction 1478–1531 (`.56`) · the count correction's twins 430–442, 1081–1086.

**TEETH:** **CK-SLOT 44 / CK-SLOT-M1 16, both GREEN.** Disposition: executable regression, with the (c)-reading checked separately at the non-perimeter junctions.

---

### EFF.GRTW2.19  [definition]  — §3.4, THE (ξ, w) CLOSED FORM

**CANONICAL STATEMENT:** verbatim, lines 396–411 (the display and its validity line).

**FORM:** display (a boxed ASCII recursion with rule lines).

> “    A_m  := ℓ_{m−1}·g_{m−1}·γ_m                 (m ≥ 1;  A_m = 0 ⟺ e_{m−1} = 1)
>     χ_1  := 1 ;
>     χ_m  := χ_{m−1}^{ ℓ′_{m−1} − ℓ_{m−1}·w_{m−1}Φ_{m−1} } · z_{m−1}^{ A_{m−1}·ℓ_{m−1} }   (m ≥ 2)
>     ─────────────────────────────────────────────────────────────────────
>     ξ_{m+1} := χ_m^{ γ_{m+1} } · z_m^{ −e_m·A_m }
>     w_{m+1} := χ_m^{ −g_m·γ_{m+1} }
>     ─────────────────────────────────────────────────────────────────────
>     R_{r−1}( Φ_{m+1}^{har} )(y)  =  w_{m+1} · ψ_m( ξ_{m+1}·y )     [GMN r = m+2]
>
> with the print tie z_m^{−A_m} = c₁ (the Theorem-`phir` constant), so at
> m = 1 the pair is exactly
>
>     (any m = 1 junction)   ξ = c₁^{e₁} = z₁^{−e₁·ℓ₀·g₀·h₀},   w = 1.
>
> Validity: m = 1 unconditional (THM W2-C2(a) + §4.2); m ≥ 2 on (C-coll);
> outside (C-coll) the pair is read off the exact recursion (§3.3(c)).”

**CONDITIONALITY:** **“the (ξ,w) covariance closed form” is FIRST in the accepted enumeration** (F3, 1345). Its validity line is exactly the scope E5's finding 2 re-affirms: unconditional at m = 1, on (C-coll) at m ≥ 2, and off (C-coll) only the recursion. **Out of range, the Σ-LAW annex CORRECTS a downstream reading of these characters** (1409–1412, `.50`): the covariance map is “the **ξ-formula composite** (the §3.4 characters ξ_q = χ_{q−1}^{γ_q}z_{q−1}^{−e_{q−1}A_{q−1}}, χ-chain included — **NOT the bare interior twist** z_{q−1}^{A_{q−1}e_{q−1}})”. **So a later note had to correct itself for using the bare twist where the χ-chain was needed** — evidence that the χ-chain is load-bearing and easy to drop. Recorded.

**DERIVATION:** From W2-C2 (`.18`) plus §4.2's residual reading (`.25`).

*Arithmetic audit (rule 22), the m = 1 specialization recomputed.* At `m = 1`: `χ_1 = 1` ✓ so `ξ_2 = 1^{γ_2}·z_1^{−e_1A_1} = z_1^{−e_1A_1}` ✓ and `w_2 = 1^{−g_1γ_2} = 1` ✓ **matching “w = 1”** ✓. With `A_1 = ℓ_0g_0γ_1` and `γ_1 = h_0` (from `.08`) ✓: `ξ = z_1^{−e_1ℓ_0g_0h_0}` ✓ **exactly the displayed `z₁^{−e₁·ℓ₀·g₀·h₀}`** ✓. And `c₁ = z_1^{−A_1}` (from `.10`) ⟹ `c₁^{e_1} = z_1^{−e_1A_1} = ξ` ✓ **the displayed print tie** ✓. **All three forms agree.**
*Consistency with W2-C2(a).* `ρ_j = c·z₁^{A₁e₁j}` with `c = c₁^{e₁g₁} = ξ^{g₁}` ✓ and `z₁^{A₁e₁j} = ξ^{−j}` ✓ so `ρ_j = ξ^{g₁−j}` ✓ — **which is exactly what W2-ID1's proof uses at `.31`** ✓ **cross-check passes.**

**RESOLUTION TRACE:** statement 396–411 · remarks 412–442 (`.20`–`.22`) · the Σ-LAW correction 1409–1412 (`.50`).

**TEETH:** **CK-XI — 21 perimeter junctions + 1 recorded boundary = 22, GREEN** (`.37`), checking that the displayed pair satisfies the orbit equations.

---

### EFF.GRTW2.20  [scope-record]  — §3.4 remark 1 (the covariance is generated by the print's own constant)

**CANONICAL STATEMENT:** verbatim, lines 414–421.

**FORM:** numbered remark inside §3.4.

> “1. **The whole covariance is generated by the print's own normalization
>    constant**: at m = 1, ξ = c₁^{e_m} and w = 1 — the covariance is
>    Thm-`phir`'s c₁ raised to the ramification of the read. The χ-chain is
>    the accumulated lower-level gauge; its composition exponent
>    ℓ′_{m−1} − ℓ_{m−1}w_{m−1}Φ_{m−1} is the SAME descent operator as the
>    [ILN]† shift recursion S_{j−1} = D_jγ_j + S_j(ℓ′_{j−1} −
>    ℓ_{j−1}w_{j−1}Φ_{j−1}) — the covariance gauge composes by the cocycle
>    shift chain.”

**CONDITIONALITY:** **A structural identification, not a claim needing proof** — and it is the load-bearing observation for the accepted LIFTCORNER's consumption (the acceptance record names “the accepted LIFTCORNER's shift-descent consumption”, 1351–1352, `.46`). **Out of range, the Σ-LAW's evaluator route REDERIVES this recursion from the other side**: “the gauge-ratio recursion Λ_q(w) = χ_q^{−w} **REDERIVES the §3.4 χ/ξ recursion from the evaluator side**” (1418–1419, `.50`) ✓ — **an independent derivation of the same chain.** `SUPERSESSION KIND: license` (corroboration, nothing moves).

**DERIVATION:** Identification of two recursions displayed side by side.

**RESOLUTION TRACE:** statement 414–421 · the independent re-derivation 1417–1419 (`.50`) · the consumer 1351–1352 (`.46`).

XREF: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md` ✓ present (the shift recursion's source).

**TEETH:** Indirect — CK-XI tests the χ-chain's output; the shift-recursion identification is an observation.

---

### EFF.GRTW2.21  [scope-record]  — §3.4 remark 2 (non-uniqueness; the support stabilizer)

**CANONICAL STATEMENT:** verbatim, lines 422–429.

**FORM:** numbered remark inside §3.4.

> “2. **Non-uniqueness (support stabilizer).** The orbit pair (ξ, w) with
>    R = w·ψ(ξy) is unique only modulo the stabilizer of supp(ψ_m): if
>    ψ_m is sparse (e.g. ψ = y² + c over F₃), distinct characters satisfy
>    the same equations. The closed form is stated as: THE DISPLAYED PAIR
>    SATISFIES the orbit equations. [Machine: CK-XI, 21 perimeter junctions,
>    0 violations; the I4B r = 4 junction is byte-equal yet carries the
>    nontrivial formula character ξ = −1 invisibly on supp(ψ₂) = {0, 2} —
>    the invisible-twist genre.]”

**CONDITIONALITY:** **This remark is the seed of the note's deepest finding.** Three later things depend on it:
(i) **The claim is deliberately weakened**: “The closed form is stated as: THE DISPLAYED PAIR **SATISFIES** the orbit equations” — not “is the pair”.
(ii) **PE3's counter-instance to the converse is exactly a support-stabilizer instance** (`.32`): at `supp(ψ₁) = {0,3}` over `F₄`, all three units of `F₄^×` satisfy the orbit equations, and the sealed scan records `ζ` rather than `1`.
(iii) **The invisible-twist genre named here (I4B r = 4) is the mechanism the r2 warrant worries about one layer down** (`.30`: “a read-invisible deeper-node divergence (the §3.5 invisible-twist genre one layer down)”).
**Untouched by every round and append** — the remark was right and the arc grew out of it.

**DERIVATION:** Observation with a worked instance.

*Arithmetic audit (rule 22).* `ψ = y² + c` over `F₃`: `supp = {0, 2}`, and a character `ξ` stabilizes the support-weighted equations iff `ξ^0 = ξ^2` in the relevant sense, i.e. `ξ² = 1` ⟹ `ξ ∈ {±1}` ✓ **a two-element stabilizer** ✓ — so `ξ = −1` is invisible ✓ **exactly the I4B r = 4 instance** ✓.

**RESOLUTION TRACE:** statement 422–429 · the boundary witness 446–466 (`.23`) · the counter-instance 741–779 (`.32`) · the r2 warrant 659–669 (`.30`).

**TEETH:** **CK-XI, 21 perimeter junctions, 0 violations** — and the I4B r = 4 invisible twist is *recorded* by the machine, not hidden.

---

### EFF.GRTW2.22  [scope-record]  — §3.4 remark 3 (the byte-equality law) with its `[r1, F3]` count corrections

**CANONICAL STATEMENT:** verbatim, lines 430–442.

**FORM:** numbered remark with two struck-and-replaced count figures.

> “3. **Byte-equality law (the F1 verdict from read data).** A shared-key
>    junction is byte-equal iff every node value of the two builders' shared
>    recursion tree agrees; at m = 1 this is: c·z₁^{A₁e₁j} = 1 for every
>    j ∈ supp(ψ_m) ∩ [0, g_m). This reproduces the probe's full F1 verdict
>    pattern ~~(which 18 junctions RED, which 12 GREEN)~~ **[r1, F3] (on this
>    runner's own 28-junction r ≥ 3 roster: which 18 RED, which 10 GREEN —
>    the 12-GREEN figure was the probe note's, from its differently-counted
>    30-junction table, copied without reconciliation)**. [Machine: CK-BYTE —
>    walk verdict ≡ actual byte compare at ~~all 28 walked~~ **[r1, F3] all
>    22 walked** junctions **(+ the 6 above-twist SKIP junctions, recorded as
>    CK-BYTE samples with a byte verdict — all 6 byte-RED — but no walk:
>    28 samples total)**, 0
>    violations.]”

**CONDITIONALITY:** **The byte law itself is unconditional and is what W2-ID1 consumes** (`.31`). The two `[r1, F3]` corrections are **count corrections caused by copying a figure across notes without reconciling rosters** — the note says so: “the 12-GREEN figure was the probe note's, from its differently-counted 30-junction table, **copied without reconciliation**”. `SUPERSESSION KIND: counter re-reading`.
**The law's quantifier is the crux of the whole r2/r3 arc**: it “quantifies over EVERY node value of the recursion tree”, whereas the recorded pair “sees only the top-layer reads” (`.30`) — that gap is (OPEN-2a).

*Arithmetic audit (rule 22), all four figures reconciled.* Runner roster: 28 r ≥ 3 junctions ✓; 6 SKIP (all byte-RED) ✓; 22 walked ✓. Walked split: “18 RED / 10 GREEN” — but `18 + 10 = 28`, not 22. **Resolution:** §7's independent recount (1085–1086) says “independent recount: 28 = 22 + 6 SKIP; **walked split 10 GREEN/12 RED**; the 6 SKIPs all byte-RED → 18/10” ✓ — so `12 + 10 = 22` walked ✓ and `12 + 6 = 18` RED total ✓ **the 18/10 figure is over all 28, the 12/10 over the 22 walked** ✓. **Both are consistent and the note gives both, at different sites.** The probe's 12-GREEN came from a 30-junction table ✓ a different roster ✓ **the reconciliation is complete and this compiler's recount matches r1's** ✓.

**DERIVATION:** The m = 1 form is read off W2-C2(a): byte-equal ⟺ `ρ_j = 1` on the support ✓ (`.18`(a)).

**RESOLUTION TRACE:** statement 430–442 · the recount 1081–1086 (`.41`) · consumed at 711–719 (`.31`), 661–663 (`.30`).

**TEETH:** **CK-BYTE — 28 samples, 0 violations**, with the walk/no-walk split disclosed. Disposition: executable regression; **the SKIP junctions are recorded rather than dropped**, which is what lets the recount close.

---

### EFF.GRTW2.23  [scope-record]  — §3.5, the I4B r = 5 boundary witness and W2-BOX-1

**CANONICAL STATEMENT:** verbatim, lines 446–466.

**FORM:** `###`-headed section body with two `[r1, F5]` renamings inline and a bold-headed box.

> “I4B (ℤ₃; reads (3,2,1),(2,1,1),(1,1,2),(2,1,1)) at r = 5: the interior
> formula character ~~ξ₄~~ **ξ₃ [r1, F5]** = χ₂^{γ₃}z₂^{−e₂A₂} = (−1)^{−13} = −1 is nontrivial
> (so (C-coll) fails) yet support-invisible at its own junction (ψ₂ = 1+y²,
> even support: r = 4 byte-equal). At r = 5 it re-emerges through the
> mod-wrap: the recorded orbit is (ξ, w) = (−1, −1) while the χ-formula
> gives (1, 1)·… — off by exactly a power of the interior ~~ϑ₄~~ **ϑ₃ [r1,
> F5]** = −1 entering
> through the monomial reduction y^{T+1} mod (y²+1) = ±y^{(T+1) mod 2}.
> **[r1, F5 — indexing: §3.2's ϑ_Q and §3.4's ξ_{m+1} are LEVEL-indexed, and
> the displayed formula is ξ_{m+1} at m = 2 — the level-3 junction, GMN
> r = 4 — so its level-indexed name is ξ₃ (with ϑ₃ = ξ₃^{−1}). The r0 text
> named it ξ₄/ϑ₄ (r-indexed), colliding with the level-indexed
> ξ₄ = χ₃^{γ₄}z₃^{−e₃A₃}, a DIFFERENT element (= 1 on I4B). Renamed;
> arithmetic unchanged (PE1 re-verified: ℓ₀ = 2, χ₂ = z₁⁴ = 1, A₂ = 13,
> z₂ = −1, recorded r = 5 orbit (−1,−1) per the JSON, formula pair (1,1)).]**
> **W2-BOX-1 (the exact residue of clause 2):** a two-parameter scalar
> formula on ALL junctions would need the monomial-collapse exponents (the
> ϑ-powers picked up by reduced representatives) tracked explicitly; the
> exact law is (HR-REC), the scalar form is proved only on (C-coll). On the
> roster every junction is either on (C-coll) or monomial-collapsing with
> scalar orbit anyway (CK-SLOT 0 violations; exactly 1 boundary junction).”

**CONDITIONALITY:**
(a) **The `[r1, F5]` renaming is an indexing collision fix**: the r0 text used an r-index where the surrounding sections use level-indices, and the r-indexed name `ξ₄` denotes a *different element* (= 1 on I4B). `SUPERSESSION KIND: replacement` (naming), with “arithmetic unchanged” and PE1's re-verification quoted.
(b) **W2-BOX-1 is one of the note's three fenced boxes** and its residue is exactly what E5's finding 2 formalizes as the geometricity test (`.25`).
(c) **“exactly 1 boundary junction”** on the roster — and E5's re-displayed census keeps it as its own category: “1/44 individually scalar-orbit-confirmed (I4B r = 5)” ✓ (1527, `.56`). **So this one junction survives every upgrade as its own census entry.**

**DERIVATION:** A worked instance; the mechanism is §3.2's mod-wrap.

*Arithmetic audit (rule 22), the re-verified data recomputed where possible.* Reads `(3,2,1),(2,1,1),(1,1,2),(2,1,1)` over ℤ₃. `ℓ₀`: solve `ℓ₀h₀ + ℓ₀′e₀ = 1` with `(e₀,h₀) = (3,2)` and `0 ≤ ℓ₀ < 3`: `2ℓ₀ ≡ 1 (mod 3)` ⟹ `ℓ₀ = 2` ✓ **matching the re-verification** ✓. `ψ₂ = 1 + y²` has `supp = {0,2}` ✓ **even support** ✓ so `ξ = −1` is invisible there ✓ (`.21`'s stabilizer computation) ✓. `(−1)^{−13} = −1` ✓ since `−13` is odd ✓. The monomial reduction `y^{T+1} mod (y²+1) = ±y^{(T+1) mod 2}` ✓ — reducing `y^k` modulo `y²+1` gives `(−1)^{⌊k/2⌋}y^{k mod 2}` ✓ **so a sign appears exactly as claimed** ✓. `χ₂ = z₁⁴`; with the residue chain's `K₁` and `z₁`… the note asserts `= 1`, which needs `ord(z₁) | 4`; no independent check available. **Recorded as consistent-but-partially-unverifiable**: `ℓ₀ = 2`, the support parity, the sign of `(−1)^{−13}`, and the reduction rule all reproduce; `χ₂ = 1` and `A₂ = 13` do not (no field data displayed).

**RESOLUTION TRACE:** statement 446–466 · the census entry 1527 (`.56`) · E5's formalization 1498–1520 (`.56`).

**TEETH:** **CK-XI records the boundary junction explicitly** (“21 perimeter junctions; 1 recorded boundary = I4B r=5”, `.37`) — the machine separates it rather than absorbing it. **Disposition: measurement, with the boundary case isolated.** **PE3 reproduced it from scratch** (“the I4B r = 5 boundary reproduced from scratch”, `.03`).

---

### EFF.GRTW2.24  [lemma]  — LEMMA W2-C1a (the two polygon legs) with its `[r1, F2]` chamber qualifier

**CANONICAL STATEMENT:** verbatim, lines 474–503.

**FORM:** `###`-headed section with a bold-headed lemma carrying a struck-and-replaced hypothesis and a long bracketed honest split, then a proof.

> “**LEMMA W2-C1a.** ~~At every level m+1 (no shared-key hypothesis needed for
> the harness-side data):~~ **[r1, F2] At every junction level m+1, evaluated
> in a chamber whose keys BELOW the junction are byte-shared with the harness
> chain (the §1.3 perimeter restricted to q ≤ m; NO hypothesis on the junction
> itself, so every first-divergence junction is in scope):**
> v_r(Φ_{m+1}^har) = e_{r−1}f_{r−1}v_r(φ_{r−1}) and
> the order-(r−1) polygon of Φ_{m+1}^har is one-sided with support exactly
> {0, e_m g_m} ∪ (attained interior grid slots), initial abscissa 0, final
> abscissa e_m g_m. **[r1, F2 — the honest split the probe's own record
> forces: the HARNESS-SIDE content (slots at exact level-m weights, all on
> one line — the proof below) holds at every level of every tower with no
> chamber hypothesis. What the qualifier fences is the GMN READING: v_r and
> the order-(r−1) polygon are ambient-chamber quantities, identified with the
> harness line through the P-index tie, and the sealed probe's own F2 record
> has exactly 6 vok/onesided FAILURES of the unqualified statement — at
> raw-chain junctions above an interior twist (the WEIGHT/SUPPORT splits of
> §5.1's mechanism paragraph). In transported chambers the statement is
> TW-ADM's MEASURED content (44/44), riding W2-OPEN-2 above each chamber's
> first twist. Consumer note (PE1 §C.4 adjudication): the accepted [JB]'s
> §0M column (d) already consumes the REPAIRED pairing — "W2-C1a for the
> window object; W2-C3 for the transported chamber", with W-2 clause 1's own
> conditionality riding — so no accepted text is falsified by this
> qualifier.]** *Proof.* The slots C_k sit at abscissas e_m k with exact
> level-m weights β_k = (g_m−k)γ_{m+1} (REALIZE R2), so every attained point
> lies ON the line e_m·β + abscissa·h-value = e_m g_m γ_{m+1} = v_r-value =
> e_{r−1}f_{r−1}v_r(φ_{r−1}) (`vrphir`, tex 1259, through the P-index tie
> γ_{m+1} = v_r(φ_{r−1})). The initial slot k = 0 is attained because
> ψ_m(0) ≠ 0 (class pin); the final slot is the monic top. ∎ [Machine:
> probe F2 vok/onesided green at all 45 first-divergence/top junctions;
> runner TW-ADM 44/44 in the transported chambers.]”

**CONDITIONALITY:** **The `[r1, F2]` split is exemplary and should be preserved whole: the HARNESS-SIDE content is unconditional; the GMN READING carries the chamber qualifier.** The evidence for the qualifier is the probe's own record — “exactly **6** vok/onesided FAILURES of the unqualified statement” ✓ **the same 6 as everywhere else** (`.15`).
**The consumer note is a cross-note claim and should be read per rule 10:** it asserts that “the accepted [JB]'s §0M column (d) already consumes the REPAIRED pairing”, adjudicated by PE1 §C.4. **This compiler did not open GRTJB to verify the column's text** — recorded as OPEN-CALL 4. Note that a *later* orchestrator annex (out of range, 1363–1365) records GRTJB row 15's annotation as **EXECUTED at `5054d69`** ✓ commit verified — so the fold that this note left owed did land.
**E5's finding 2 leaves W2-C1a alone**: “Outside that scope the proved conclusion consists of **W2-C1a's polygon statement** plus the exact HR-REC residual” (1522, `.56`) ✓ — **W2-C1a survives every correction in the arc.**

**DERIVATION:** Quoted inline.

*Arithmetic audit (rule 22).* Every slot `C_k` at abscissa `e_mk` with weight `β_k = (g_m−k)γ_{m+1}`: the line value is `e_m·β_k + (e_mk)·(h-value per abscissa)`. With the line through `(0, e_mg_mγ_{m+1})` and `(e_mg_m, 0)`, the value at abscissa `e_mk` is `e_mg_mγ_{m+1} − e_mk·γ_{m+1} = e_m(g_m−k)γ_{m+1} = e_mβ_k` ✓ **so every slot sits exactly ON the line** ✓. Endpoints: `k = 0` attained since `ψ_m(0) ≠ 0` ✓ (`.08`'s class pin); `k = g_m` is the monic top ✓. **Support `{0, e_mg_m} ∪ interior` ✓ one-sided ✓.** The `v_r` identification `e_{r−1}f_{r−1}v_r(φ_{r−1}) = e_mg_mγ_{m+1}` uses `.09`'s dictionary `(e_i,f_i)^GMN = (e_{i−1},g_{i−1})^har` ✓ so `e_{r−1}f_{r−1} = e_mg_m` ✓ and `v_r(φ_{r−1}) = γ_{m+1}`… **the note's own §1.2 says `v_{i+1}(φ_i) = γ_i^har`** ✓ giving `v_r(φ_{r−1}) = γ_{r−1}^har = γ_{m+1}` ✓ (with `r − 1 = m + 1`) ✓ **the identification closes exactly.**

**RESOLUTION TRACE:** statement 474–503 · the 6 failures 310–316 (`.15`), 606–615 (`.28`) · the fold's execution 1363–1365 (`.48`) · E5's exemption 1522 (`.56`).

XREF: `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md` — **verified present** (the consumer named).
PIN: `5054d69` ✓ commit.

**TEETH:** **probe F2 45/45 (foreign) + runner TW-ADM 44/44.** Disposition: executable regression on two instruments, one foreign; and **the probe's 6 FAILURES are the evidence for the qualifier**, i.e. a foreign instrument's red rows became this note's hypothesis.

---

### EFF.GRTW2.25  [theorem]  — THEOREM W2-C1 (admissible representative, clause 1)

**CANONICAL STATEMENT:** verbatim, lines 507–526.

**FORM:** `###`-headed section with a bold-headed theorem, an indented ASCII display, and a proof.

> “**THEOREM W2-C1 (admissible representative, clause 1).** At a shared-key
> junction on the §3 perimeter, the print residual of the harness lift is
>
>     R_{r−1}(Φ_{m+1}^har)(y) = w_{m+1}·ψ_m(ξ_{m+1}·y)
>
> with (ξ, w) the §3.4 pair. Consequently, under the pinned (P-ell)
> convention Φ_{m+1}^har is a monic polynomial of type-degree m_r whose
> residual is a UNIT MULTIPLE OF THE ξ-CONJUGATE of ψ_m: it is a strict
> Def-2.12 representative of the ξ-conjugate type t^ξ (ψ_m replaced by
> ψ_m^{(ξ)}(y) := ξ^{−g_m}ψ_m(ξy), a monic irreducible with the same
> (e, h, g) data), and a representative of t ITSELF iff the character is
> support-trivial (ξ^j constant on supp ψ_m — e.g. always when ξ = 1;
> the I4B r = 4 even-support case shows support-triviality is weaker than
> ξ = 1). *Proof.* The slot-j residual coefficient of Φ^har is the slot-j
> coefficient of R(φ_r^cls) divided by ρ_j (the reads differ by ρ_j and the
> print evaluator is value-functorial on on-line digits — this is the same
> HR-REC mechanics read backwards); Thm-`phir` gives R(φ_r^cls) = c·ψ_m,
> and c/ρ_j = w·ξ^j by §3.3–3.4. Irreducibility and the (e,f) data of the
> conjugate: PARI leg. ∎ [Machine: probe F2-orbit 45/45 + F4 24/24 (both
> top lifts irreducible with (e,f) = (∏e_j, d₀∏g_j)); runner CK-XI.]”

**CONDITIONALITY:** **The universal reading of this theorem is SUPERSEDED by THEOREM W2-C1-CORR** (E5 finding 2, 1484–1531, `.56`). Quoted:

> “**[ANNEX 2026-08-12, certifier correction — W2-C1 SCALAR-ORBIT SCOPE.]** The universal reading of THEOREM W2-C1 outside the scalar-collapse perimeter is **SUPERSEDED** by the following proved display.”

with the replacement's three items: (1) `m = 1` unconditional; (2) `m ≥ 2` on (C-coll); (3) at a general shared-key junction outside (C-coll), **HR-REC computes `B_m` exactly, but no scalar orbit is asserted without a finite geometricity condition** `a_j = wξ^j` on `supp ψ_m`. And the consequent statement correction (1522): “CLAUSE 1 and the §6.2 W2-C1 row are proved universally only at `m = 1` and on (C-coll), and conditionally at other shared-key junctions when the displayed geometricity test is established.”

`SUPERSESSION KIND: replacement` at statement scope. **CHAIN: W2-C1 as displayed (all shared-key junctions) → E5 finding 2 → THEOREM W2-C1-CORR. TERMINAL: W2-C1-CORR, awaiting sol discharge (cert3).**

**The defect's exact location** is the proof's step “c/ρ_j = w·ξ^j by §3.3–3.4”: §3.3(c) computes the `ρ_j` but **does not prove they are geometric in j**, and off (C-coll) nothing forces it. E5's derivation makes this concrete: at `{0,1,2} ⊆ supp ψ_m` a scalar orbit forces `ρ₁² = ρ₀ρ₂`, “which HR-REC does not supply off (C-coll)”.

*Arithmetic audit (rule 22) of E5's geometricity criterion, recomputed.* `B_m = wψ_m(ξy)` means `[y^j]B_m = w·ψ_{m,j}·ξ^j` ✓, i.e. `a_j := [y^j]B_m/ψ_{m,j} = wξ^j` ✓ **exactly the displayed criterion** ✓. With `[y^j]B_m = (c/ρ_j)ψ_{m,j}` (from the proof) ✓, this is `c/ρ_j = wξ^j` ✓. Taking `j = 0,1,2`: `a_0 = w`, `a_1 = wξ`, `a_2 = wξ²` ⟹ `a_1² = a_0a_2` ✓ ⟹ `(c/ρ_1)² = (c/ρ_0)(c/ρ_2)` ⟹ **`ρ_1² = ρ_0ρ_2`** ✓ **exactly E5's display** ✓. **This compiler's independent recomputation confirms the certifier's derivation.**

**DERIVATION:** Quoted inline, with the superseded step named above.

**RESOLUTION TRACE:** statement 507–526 · the superseding display 1484–1531 (`.56`) · the surviving parts 1526–1529 (E5's consumer sweep: W2-C2(a), W2-ID1, HR-REC and the (C-coll) scalar display “survive unchanged”).

XREF: `docs/references/HigherNewton.tex` ✓ (tex 1285, Def-2.12).

**TEETH:** **probe F2-orbit 45/45 + F4 24/24 (foreign) + CK-XI 22 (own).** Disposition: executable regression on two instruments. **But note the gap E5 exposes: the machine checks that the displayed pair SATISFIES the orbit equations (CK-XI), which is exactly `.21`'s weakened claim — it does not check that a scalar orbit must exist.** So the instrument was measuring the right thing and the *theorem* over-read it.

---

### EFF.GRTW2.26  [scope-record]  — §4.3, the unpinned-ℓ parametrization (review-owed) with the `[r2, P2]` revert

**CANONICAL STATEMENT:** verbatim, lines 530–573.

**FORM:** `###`-headed section body with a struck `[r1, F6]` bracket, a long `[r2, P2]` revert bracket, and an indented ASCII rescaling display.

> “The print fixes only ℓ_r h_r − ℓ′_r e_r = 1 (tex ~1291) — no
> representative is pinned. Shifting ℓ_{r−2} ↦ ℓ_{r−2} + k·e_{r−2}
> changes Def-`t(i)` by **t ↦ t − k·u_i** ~~[r1, F6] t ↦ t + k·u_i …~~
> **[r2, P2 — the r1 "fix" REVERTED as unfaithful to the named source;
> the r0 sign was CORRECT. Tex 1431's literal Def-`t(i)` is t_{r−1}(a)_i =
> (s_{r−1}(a) − ℓ_{r−1}·v_r(aφ_r^i))/e_{r−1} — the (s − ℓu)/e arrangement,
> with u_i = v_r(a_iφ_r^i) the polygon ordinate (tex 1373) and s_{r−1}(a)
> the attained initial abscissa, both ℓ-shift-INVARIANT — so
> ℓ_{r−2} ↦ ℓ_{r−2} + k·e_{r−2} gives t ↦ t − k·u_i directly …
> The r1 bracket's premise formula "(ℓu_i − s_i)/e" is a
> DIFFERENT print object — Prop-`construct`'s child twist exponent (tex
> 1201), near-negative of Def-`t(i)` — inherited from W2-L2's r0 naming
> parenthetical, which conflated the two opposite-signed exponents (split
> at §2.3 [r2, P2]); PE1's F6 computed with the conflated alias, r1
> implemented that finding, PE2 re-derived the sign at source. Recorded
> here so no future round re-flips it. The section's conclusions — orbit =
> characters ξ ∈ ⟨z_m^{h_m}⟩ with coupled w, reachability iff
> gcd(h_m, ord z_m) divides the ξ-exponent — quantify over all k ∈ ℤ and
> are sign-invariant under either convention, so nothing downstream moved
> in either round. The section stays inside its review-owed fence.]**,
> hence rescales the order-(r−1)
> residual coefficients on a side with initial point (s₀, u₀) by
> c_i ↦ z_{r−2}^{−k(u₀ − jh_{r−1})}·c_i:
>
>     R^{(ℓ+ke)}(X)(y) = z_{r−2}^{−k·u₀} · R^{(ℓ)}(X)( z_{r−2}^{k·h_{r−1}}·y ).
>
> So the ℓ-orbit acts on residuals exactly by the covariance characters
> with ξ ∈ ⟨z_m^{h_m}⟩ and coupled w = z_m^{−k·g_mγ_{m+1}}. The harness
> lift's character ξ = §3.4 is REACHABLE by an ℓ-shift iff
> z_m^{k·h_m} = ξ^{−1} is solvable in k, i.e. iff gcd(h_m, ord z_m) divides
> the ξ-exponent — true on many rows (e.g. T2A: h = 1, k = 2) but NOT a
> theorem of the class pin. Honest summary: **whether Def-2.12's "R ∼ ψ" is
> read strictly at a pinned ℓ or up to the ℓ-orbit is genuinely
> underdetermined by the print; under the strict pinned reading clause 1
> holds for the conjugate type t^ξ, under the orbit reading it holds for t
> itself exactly on the reachable rows.** This parametrization stands
> review-owed (probe fence inherited); nothing downstream consumes the
> orbit reading — clause 3 removes the ambiguity by transporting the type.”

**CONDITIONALITY:** **A REVIEW-OWED CONVENTION FENCE, and a REVERT.**
(a) **The revert:** r1 flipped a sign on PE1's F6; r2 reverted it at source with tex 1431 displayed, and **installed anti-re-flip records in two brackets** (`.13` and here). `SUPERSESSION KIND: replacement`. **CHAIN: r0 sign `t ↦ t − k·u_i` → `[r1, F6]` flip → `[r2, P2]` revert. TERMINAL: the r0 sign, restored.** **The note is explicit that nothing downstream moved in either round** — “the section's conclusions … quantify over all k ∈ ℤ and are sign-invariant under either convention”.
(b) **The fence:** “This parametrization stands review-owed (probe fence inherited)” — an **inherited** open item, and it is the fourth open surface listed at `.40` (“W2-OPEN-1 + W2-OPEN-2 + W2-BOX-1 + the §4.3 convention fence”).
(c) **E5's consumer sweep touches it once**: “Section 4.3's ℓ-orbit analysis applies **only after a scalar pair exists**” (1529, `.56`) — i.e. the fence now sits downstream of W2-C1-CORR's geometricity test. `SUPERSESSION KIND: scope-pin`.
(d) **“nothing downstream consumes the orbit reading”** is the containment claim, and it holds: clause 3 transports the type instead.

**DERIVATION:** Displayed inline; the rescaling identity follows from `Def-rescoeff` (tex 1447).

*Arithmetic audit (rule 22).* The shift's effect: `t = (s − ℓu_i)/e` with `s, u_i` both ℓ-shift-invariant ⟹ `ℓ ↦ ℓ + ke` gives `t ↦ (s − (ℓ+ke)u_i)/e = t − ku_i` ✓ **exactly the r0/r2 sign** ✓ **and this compiler's recomputation confirms the revert.** The near-negative object: `T = (ℓu − 𝔰)/e` (from `.13`) vs `t = (s − ℓu)/e` ✓ **opposite-signed** ✓ (equal up to the `s`-vs-`𝔰` distinction) ✓ **so the conflation was real.** Reachability: `z_m^{kh_m} = ξ^{−1}` solvable in `k` ⟺ `ξ^{−1} ∈ ⟨z_m^{h_m}⟩` ⟺ `ord(z_m)/gcd(h_m, ord z_m)` divides the order of `ξ`… the note's phrasing “gcd(h_m, ord z_m) divides the ξ-exponent” ✓ is the standard cyclic-group solvability criterion ✓.

**RESOLUTION TRACE:** statement 530–573 · the twin bracket 256–284 (`.13`) · the round record 1160–1175 (`.42`) · E5's scope-pin 1529 (`.56`).

XREF: `docs/references/HigherNewton.tex` ✓ (tex 1431, 1447, 1373, 1201, ~1291).

**TEETH:** NONE for the convention analysis — it is explicitly review-owed. **The revert itself was adjudicated at source by PE2**, which is a `transfer audit` disposition (rule 27): a hostile pass reading the cited print.

---

### EFF.GRTW2.27  [definition]  — §5.1, the transported type

**CANONICAL STATEMENT:** verbatim, lines 581–604.

**FORM:** `###`-headed section body with a numbered two-step definition, an `[r1, F1]` honesty bracket inside step 1, and a closing sentence.

> “Fix a harness tower T in the class pin. Define the **transported type
> data** t^tw level by level, ascending. Start from T's own (e, h, ψ)
> ledger. At each junction level m+1 = 2, 3, …, working in the CURRENT
> (already partially transported) classifier chamber:
>
> 1. build the print chain on the current ledger and evaluate the Def-2.12
>    criterion on the harness lift Φ_{m+1}^har; record the junction pair
>    (ξ, w) with R(Φ^har)(y) = w·ψ^cur(ξy); **[r1, F1: above the chamber's
>    first ξ ≠ 1 junction the EXISTENCE of this pair is not §3-derived —
>    (C-coll) is NOT tracked through the transport, and §3.4's scalar warrant
>    stops at the first twist. The recording itself is a per-instance exact
>    computation (the finite orbit scan), well defined whenever the pair
>    exists; existence at every roster junction is the machine record TW-ADM
>    44/44, and existence in general is part of the open box W2-OPEN-2
>    (§5.2).]**
> 2. if ξ ≠ 1, replace the current level-m modulus by its ξ-conjugate
>    ψ^tw(y) := ξ^{−g_m}·ψ^cur(ξ·y) (monic, irreducible, ψ^tw(0) ≠ 0, same
>    (e, h, g) read data — the class the harness lift ACTUALLY represents),
>    and re-coordinate every higher-level residual datum through the letter
>    identification z_old = ξ·z_new (coordinate rescale (a_i) ↦ (a_i·ξ^i)
>    at the K_{m+1}-layer of every nested tuple).
>
> The w of the pair is recorded but not consumed by the transport (classes
> are scalar-free); it is the value-layer bookkeeping unit of §3.4.”

**CONDITIONALITY:**
(a) **Step 1's `[r1, F1]` bracket is the transport's own honesty item**: above the first twist the pair's EXISTENCE is not §3-derived, and existence in general is part of W2-OPEN-2. **So the transport is defined conditionally on the box it exists to motivate.**
(b) **Step 1 pins no selection rule** — “just says "record the junction pair"” (`.31`'s r3 bracket) — and that is exactly what PE3's counter-instance exploits (`.32`). **A selection rule was deliberately NOT added at r3**: “The alternative cure (pin the ξ = 1 preference into §5.1) is NOT taken: the sealed scan is byte-frozen and implements enumeration order, so a pinned preference would misdescribe the note's own machine bracket off-roster” (1242–1245, `.43`). **That is a refusal to make the text prettier than the instrument.**
(c) **E5's consumer sweep touches step 2**: “At a general non-collapse first twist, §5.1's ξ-transport is **conditional on the geometricity test**” (1528, `.56`). `SUPERSESSION KIND: scope-pin`.

**DERIVATION:** Definition; step 2's `ψ^tw` is monic irreducible with the same read data because conjugation by a unit preserves those.

*Arithmetic audit (rule 22).* `ψ^tw(y) := ξ^{−g_m}ψ^cur(ξy)`: if `ψ^cur = y^{g_m} + …`, then `ψ^cur(ξy) = ξ^{g_m}y^{g_m} + …` ✓ so `ξ^{−g_m}ψ^cur(ξy)` is monic ✓. `ψ^tw(0) = ξ^{−g_m}ψ^cur(0) ≠ 0` ✓. Irreducible ✓ (a linear substitution). Same `(e,h,g)` ✓ (degree preserved). **The re-coordination `(a_i) ↦ (a_iξ^i)` is the dual of `z_old = ξz_new`** ✓ (substituting `z_old = ξz_new` into `Σa_iz_old^i` gives `Σa_iξ^iz_new^i`) ✓ **exact.**

**RESOLUTION TRACE:** statement 581–604 · the mechanism 606–615 (`.28`) · the selection-rule refusal 1242–1245 (`.43`) · E5's scope-pin 1528 (`.56`).

**TEETH:** **TW-ADM 44/44** is the existence record; the transport's own correctness is measured by TW-RATIO/TW-STRICT (`.37`).

---

### EFF.GRTW2.28  [scope-record]  — §5.1's Mechanism (why the transport is forced)

**CANONICAL STATEMENT:** verbatim, lines 606–615.

**FORM:** bold-headed paragraph.

> “**Mechanism (why this is forced — the probe's finding (4) restated as
> mathematics).** After a twisted junction the same ψ-bytes denote DIFFERENT
> residue classes in the two chains: the classifier's letter and the
> harness's letter differ by the character ξ. Without step 2 the classifier
> chain continued on raw ψ-bytes is a valid GMN type chain — of the
> CONJUGATE type — and above the twist the two keys differ at key weight
> (v(φ^cls − Φ^har) = v(key)): different induced valuations, WEIGHT/SUPPORT
> splits, and the value layer breaks (probe F2: 6, F3: 96).”

**CONDITIONALITY:** **This paragraph is the note's causal account and it is confirmed twice from outside.**
(i) **The probe's numbers are the evidence**: F2's 6 weight/support splits ✓ (the same 6 as `.15`, `.24`) and F3's 96 value-layer violations ✓ (the same 96 as `.04`, `.35`).
(ii) **The clause “different induced valuations” is SUPERSEDED in W2-C3's wording** (E5 finding 4, 1568–1594, `.58`) — but *not here*: E5 supersedes W2-C3's claim that the transported chains have the *same* induced valuation data; this paragraph's claim that the *untransported* chains have *different* ones is the same phenomenon and survives. **In fact E5's own derivation uses it**: “W2-OPEN-2's route-(3) obstruction now agrees with W2-C3” (1594). Recorded so a merge does not over-apply the supersession.
(iii) `v(φ^cls − Φ^har) = v(key)` is exactly the quantity route (3) of the derivability adjudication turns on (`.34`).

**DERIVATION:** Restatement of the probe's finding (4) as mathematics.

**RESOLUTION TRACE:** statement 606–615 · the probe numbers 890–892 (`.35`), 502–503 (`.24`) · route (3) 863–870 (`.34`) · E5's finding 4 1562–1594 (`.58`).

**TEETH:** **probe F2: 6 and F3: 96** — foreign-instrument evidence, and the 96 is the number the transport turns GREEN (`.35`).

---

### EFF.GRTW2.29  [theorem]  — THEOREM W2-C3 (clause 3, chain level)

**CANONICAL STATEMENT:** verbatim, lines 617–649 (the `###` heading with its `[r1, F1]` re-scope tag, the three clauses, and the proof sketch with its machine bracket).

**FORM:** `###`-heading carrying a bracketed re-scope + three lettered clauses + a proof sketch.

> “### 5.2 THEOREM W2-C3 (chain level; attempt grade given §3–§4) **[r1, F1: RE-SCOPED — proved to each chamber's first twist, MEASURED above it; grade split and the open bridging box W2-OPEN-2 below]**
>
> On the transported ledger, at every level m+1:
>
>   (i) the junction is shared-perimeter-type: the two keys agree in
>       weights and support (one-sided, same polygon; no WEIGHT/SUPPORT
>       degeneration at any level of any tower);
>   (ii) Φ_{m+1}^har is a **STRICT** (pinned-ℓ) Def-2.12 representative of
>       the transported type t^tw at level m+1 — R(Φ^har) ∼ ψ^tw exactly,
>       no orbit needed;
>   (iii) the transported print key φ^tw and Φ^har represent THE SAME type
>       (both strict representatives of t^tw; equal (e,f) by the PARI leg)
>       — the probe's conjugate-type split is cured. This is the precise
>       cash-out of "the twisted chains are MacLane-equivalent level by
>       level": equivalence as type data (same residual classes, same
>       induced valuation data), NOT byte-equality of keys (junction unit
>       ratios persist and are the §3.4 characters of the transported
>       chamber).
>
> *Proof sketch at attempt grade.* (ii) is clause 1 applied in the
> transported chamber: R(Φ^har) = w·ψ^cur(ξy) = w·ξ^{g_m}·ψ^tw(y) — a scalar
> multiple of the new modulus, i.e. strict ∼. (i): with the classes matched,
> both builders place slots on the same one-sided polygon (W2-C1a for the
> harness side, Prop-`construct`/Thm-`phir` for the print side, on the same
> (e, h, g, γ) data — transport changes no weights). (iii) from (ii). The
> induction is over junctions ascending; the re-coordination step is an
> isomorphism of the residual ledger, so each chamber stays in the class
> pin. ∎ [Machine: TW-RATIO 44/44 junction comparisons with NO weight/
> support mismatch (the probe's 6 such rows all cure); TW-ADM 44/44;
> TW-STRICT 44/44 — strict unit at EVERY level of EVERY tower; TW-PARI
> 12/12 transported top lifts irreducible with (e,f) = (∏e_j, d₀∏g_j);
> TW-QO 7/7 on the extracted concrete shapes; MT-TW teeth: a garbled
> character (ξ·z₁) is caught on both designated rows.]”

**CONDITIONALITY:** **Two independent supersessions, one in range and one out.**
(a) **`[r1, F1]` re-scopes the grade**: proved to each chamber's first twist (38/44), MEASURED above (6/44). The full re-scope block is `.30`. `SUPERSESSION KIND: scope-pin`.
(b) **Clause (iii)'s equivalence wording is SUPERSEDED by E5 finding 4** (1568–1594, `.58`):

> “In W2-C3, the phrase “equivalence as type data (same residual classes, same induced valuation data)” and the subsequent description “MacLane-equivalent level by level” are **SUPERSEDED** by:
> > **ledger-equivalent at the displayed scope:** … No equality of the augmented valuation functions induced by the two different key representatives is claimed.”

with (iii) re-displayed as “a residual/type-ledger assertion, not an assertion that the two key augmentations define the same valuation on O[x]”. `SUPERSESSION KIND: replacement`. **CHAIN: (iii) as displayed → E5 finding 4's ledger-equivalence re-display. TERMINAL: the re-display, awaiting sol discharge (cert3).**
**The defect was self-inflicted and the note already contained the refutation**: route (3) of its own derivability adjudication (`.34`) proves that equal augmented valuations are unavailable — “the recorded data warrant only ≥ key weight … strictly BELOW γ, so the two chains' inductive valuations may genuinely differ”. **E5's finding is that (iii) claimed what §5.2's own route (3) denies.** The finding's own words: “The note itself proves that equality of augmented valuation functions is unavailable” (1564).
(c) **Clauses (i) and (ii) survive**: “W2-C3(i)'s polygon statement and W2-C3(ii)'s strict-residual statement do not use equality of valuation functions and survive at their separately corrected grades” (1594, `.58`) ✓.

**DERIVATION:** Quoted inline; (ii) is clause 1 in the transported chamber, and **that application is exactly what the `[r1, F1]` block fences** (`.30`).

*Arithmetic audit (rule 22) of (ii)'s one-line computation.* `R(Φ^har) = w·ψ^cur(ξy)`; substituting `ψ^tw(y) = ξ^{−g_m}ψ^cur(ξy)` ⟹ `ψ^cur(ξy) = ξ^{g_m}ψ^tw(y)` ✓ so `R(Φ^har) = w·ξ^{g_m}·ψ^tw(y)` ✓ **a scalar multiple** ✓ **exactly as displayed** ✓.
*E5's counter-derivation.* With `Φ = φ + D` and `μ(D) = μ(φ) < γ`: the `φ`-augmentation gives `μ_{φ,γ}(Φ) = min{γ, μ(D)} = μ(D) < γ` ✓, while the `Φ`-augmentation gives `μ_{Φ,γ}(Φ) = γ` ✓ **different** ✓ **so matching ledgers do not give equal valuations** ✓ **this compiler's recomputation confirms the certifier's derivation.**

**RESOLUTION TRACE:** statement 617–649 · the re-scope block 651–705 (`.30`) · route (3) 863–870 (`.34`) · E5's finding 4 1562–1594 (`.58`).

**TEETH:** **TW-RATIO 44/44 + TW-ADM 44/44 + TW-STRICT 44/44 + TW-PARI 12/12 + TW-QO 7/7 + MT-TW 2/2.** **Disposition: executable regression on five families plus a fired tooth.** **BUT the note itself reclassifies one**: “TW-STRICT is SAME-ADJACENT evidence given TW-ADM — once the orbit pair exists, the §5.1 conjugation makes strictness an identity — so the bracket above reads honestly as TW-ADM 44/44 plus a construction-forced strictness confirmation, **NOT two independent 44/44 legs**” (`.30`(b)). **That is a self-administered evidence-class downgrade** and it is the model of rule 20's disposition vocabulary.

---

### EFF.GRTW2.30  [changes-record]  — the `[r1, F1]` HONEST RE-SCOPE block

**CANONICAL STATEMENT:** verbatim, lines 651–705 (the whole block, with its `[r2, P1]`, `[r3]` and `[r4, PE4 o-b]` nested brackets).

**FORM:** bold-headed bracketed block with strike-through, three nested round-brackets, a per-junction-level census, and two lettered honesty items.

> “**[r1, F1 — THE HONEST RE-SCOPE (PE1's major gap, cured by re-fencing; no
> statement above is changed, the GRADE is).** The sketch applies clause 1
> (THEOREM W2-C1) inside the transported chamber; clause 1 is proved AT A
> SHARED-KEY JUNCTION (§1.3: byte-equality of all keys below). In a
> transported chamber this warrant holds up to and including the chamber's
> FIRST ξ ≠ 1 junction r₀ — junctions below r₀ recorded ξ = 1, so no
> conjugation fired ~~and every key below r₀ is byte-equal to the harness key;
> the criterion AT r₀ is therefore evaluated over byte-shared lower keys and
> clauses 1–2 apply~~ **[r2, P1] — and the further step "recorded ξ = 1 ⟹
> byte-equal" (what makes the criterion at-or-below r₀ evaluate over
> byte-shared lower keys, so that clauses 1–2 apply) is NOT definitional: the
> recorded pair sees only the top-layer reads, while the byte law (§3.4 rk. 3)
> quantifies over EVERY node value of the recursion tree — a read-invisible
> deeper-node divergence (the §3.5 invisible-twist genre one layer down)
> would be byte-RED with recorded ξ = 1. That step is PROVED at m = 1
> (LEMMA W2-ID1 below) and at m ≥ 2 is exactly W2-OPEN-2's premise sub-clause
> (OPEN-2a); on the committed roster it is instance-exact — recorded ξ ≠ 1 ⟺
> byte-RED at 22/22 walked junctions, and every junction below every
> chamber's r₀ is byte-GREEN (PE2's recomputation from the committed JSON)**.
> ABOVE r₀ the transported print keys and the harness
> keys are byte-DIFFERENT **[r4, PE4 o-b: roster instance (all 6 above-r₀
> SKIP junctions byte-RED — PE2/PE4 recomputation); in general UNPROVED —
> the same converse+persistence content flagged inside W2-OPEN-2's premise
> [r3]; this block's conclusion consumes only the ABSENCE of the byte-share
> warrant, which holds either way]** (the persistent unit ratios of (iii)'s
> own wording), every higher junction sits OFF the §3 perimeter, and clauses
> 1–2 AS PROVED do not apply there. Honest grade, per junction-level of the
> roster's 44 (per-tower first-twist census recomputed this round from the
> committed ξ-ledger): **PROVED at attempt grade given §3–§4 at the 38
> junction-levels at-or-below each chamber's first twist; MEASURED at the 6
> junction-levels above a first twist** — T3A/T3C/T3D/T3E at r = 4 and I4C
> at r = 4, 5, exactly the interior-twist geography the transport exists to
> cure — where (i)–(iii) hold conditionally on the open bridging lemma
> W2-OPEN-2 displayed below. **[r2, P1 — the proved-scope sentence, scoped
> to what carries it: at the proved-scope junction-levels whose strictly-
> below junctions all sit at m ≤ 1 (GMN r ≤ 4; TH-BASE + LEMMA W2-ID1 cover
> the below-chain), the byte-share warrant is fully §3-derived; at the
> proved-scope junction-levels with an m ≥ 2 recorded-trivial junction below
> — on this roster exactly I4A r = 5 and I4B r₀ = 5 (read off the per-chamber
> first-twist census this round) — the warrant is INSTANCE EVIDENCE (every
> below-r₀ junction byte-GREEN, 22/22 walked equivalence — PE2's
> recomputation) riding (OPEN-2a). The 38/44 census stands as exactly that:
> 36 junction-levels fully warranted + 2 instance-warranted, not a uniform
> theorem-grade 38.]** (The final-chamber scans stand in for the
> mid-transport states: later junctions never touch the data a lower
> junction's residual depends on — PE1 §A.9 verified this index-by-index in
> `transport_leg`.) Two companion honesty items: (a) whether (C-coll)
> survives into each transported chamber is NOT tracked, so above r₀ the
> recorded (ξ, w) is the orbit scan's exact per-instance value, not the
> §3.4 scalar formula (§5.1 step 1's [r1] bracket); (b) evidence-class
> reclassification (PE1 §C.5): **TW-STRICT is SAME-ADJACENT evidence given
> TW-ADM** — once the orbit pair exists, the §5.1 conjugation makes
> strictness an identity — so the bracket above reads honestly as TW-ADM
> 44/44 plus a construction-forced strictness confirmation, NOT two
> independent 44/44 legs.]**”

**CONDITIONALITY:** **This block is the arc's centre of gravity and its state at HEAD differs from its displayed state in two ways.**
(a) **The `[r2, P1]` census “36 fully warranted + 2 instance-warranted, not a uniform theorem-grade 38” is UPGRADED out of range**: the Σ-LAW supplier proves (OPEN-2a)'s forward direction at every `m ≥ 2` (annexes 2026-08-08 and #3, `.49`, `.50`, `.53`), so the 2 instance-warranted entries gain a theorem. **Then E5 re-partitions to 37 + 1 + 6** (1527, `.56`) — I4A r = 5 becomes derived; **I4B r = 5 stays individually confirmed for a DIFFERENT reason** (its scalar orbit is a boundary instance off (C-coll), `.23`). `SUPERSESSION KIND: license` then `counter re-reading`. **TERMINAL: 37 + 1 + 6.**
(b) **The `[r4, PE4 o-b]` qualifier on “ABOVE r₀ … byte-DIFFERENT”** converts a universal into a roster instance plus an explicit UNPROVED, **and states why the block survives it**: “this block's conclusion consumes only the ABSENCE of the byte-share warrant, which holds either way”. `SUPERSESSION KIND: scope-pin`.
(c) **Honesty item (b) — the TW-STRICT reclassification — is a self-administered evidence downgrade** and is repeated in the §6.1 table (`.37`).
(d) **Honesty item (a)** is why the recorded pair above `r₀` is a scan value, not a formula value (`.27`).

*Arithmetic audit (rule 22).* The 6 measured junction-levels are enumerated: “T3A/T3C/T3D/T3E at r = 4 and I4C at r = 4, 5” ✓ `4 + 2 = 6` ✓ **exact enumeration matching the count everywhere else** ✓. The 2 instance-warranted: “I4A r = 5 and I4B r₀ = 5” ✓. `36 + 2 + 6 = 44` ✓. PE3's independent decomposition `36 = 16 + 16 + 4` ✓ (`.05`). **All four decompositions of 44 agree.**

**DERIVATION:** A grade re-fencing, not new mathematics — “no statement above is changed, the GRADE is”.

**RESOLUTION TRACE:** statement 651–705 · W2-ID1 707–739 (`.31`) · the box 781–847 (`.33`) · out-of-range upgrades 1376–1440, 1527 (`.56`).

**TEETH:** **TW-ADM 44/44 (with TW-STRICT reclassified SAME-adjacent), plus PE1 §A.9's index-by-index verification that final-chamber scans stand in for mid-transport states.** Disposition: executable regression + a hostile pass's structural check.

---

### EFF.GRTW2.31  [lemma]  — LEMMA W2-ID1 (recorded-ξ triviality ⟹ byte-equality at m = 1)

**CANONICAL STATEMENT:** verbatim, lines 707–739.

**FORM:** bold-headed lemma with a proof and a struck-and-replaced “Consequently” sentence.

> “**LEMMA W2-ID1 (recorded-ξ triviality ⟹ byte-equality at m = 1). [r2, P1]**
> At an m = 1 junction (GMN r = 3, the first junction of any chamber — lower
> keys byte-shared unconditionally by TH-BASE, so no transport has fired
> below and ψ^cur = ψ₁), if the §5.1 step-1 recorded pair has ξ = 1, then the
> junction is byte-equal. *Proof (from W2-C2(a) + §3.4).* At m = 1 the §3.4
> display is unconditional: R₂(Φ₂^har)(y) = ψ₁(ξ_f·y) with the formula pair
> (ξ_f, w_f) = (z₁^{−e₁A₁}, 1). A recorded pair (1, w) means
> R₂(Φ₂^har) = w·ψ₁(y); equating the two at j = 0 (ψ₁(0) ≠ 0, class pin)
> forces w = 1, so ψ₁(ξ_f·y) = ψ₁(y), i.e. ξ_f^j = 1 for every
> j ∈ supp(ψ₁) — including the monic top j = g₁. Hence on supp(ψ₁) ∩ [0, g₁):
> c·z₁^{A₁e₁·j} = ξ_f^{g₁}·ξ_f^{−j} = ξ_f^{g₁−j} = 1 (using c = c₁^{e₁g₁} =
> ξ_f^{g₁} and z₁^{A₁e₁j} = ξ_f^{−j}) — exactly §3.4 rk. 3's m = 1
> byte-equality law, so the junction is byte-equal. ∎ ~~Consequently the
> identification "first recorded ξ ≠ 1 junction = first byte-divergence" is
> PROVED for every junction whose strictly-below junctions all sit at m ≤ 1
> (ascending: r = 2 by TH-BASE, r = 3 by this lemma); at m ≥ 2 it is OPEN —
> the premise sub-clause (OPEN-2a) of the box below.~~ **[r3, PE3-P1 —
> scoped to the proved direction:** consequently, at every junction whose
> strictly-below junctions all sit at m ≤ 1 …, NO byte-divergence occurs
> strictly below the first recorded ξ ≠ 1 junction — the HALF of the
> identification … that every consuming surface of this note uses …;
> at m ≥ 2 this same forward direction is the premise sub-clause (OPEN-2a) of
> the box below; the CONVERSE — recorded ξ ≠ 1 ⟹ byte-RED — is UNPROVED at
> every m including m = 1: it is a property of the recorded-pair SELECTION
> RULE, which this note never pins …, and it is FALSE under the sealed scan's
> actual selection — the counter-instance recorded below.**]** [Machine:
> instance-exact on the roster — recorded ξ ≠ 1 ⟺ byte-RED at all 22 walked
> junctions, of which the m = 1 slice is the 16 r = 3 rows (PE2 recomputation).]”

**CONDITIONALITY:** **The lemma is PROVED and is in the accepted enumeration** — F3 lists “LEMMA W2-ID1 (**forward direction**, with the converse's counter-instance displayed)” (1347–1348, `.46`). **Its “Consequently” sentence was two-sided and is SCOPED to the forward direction at r3.** `SUPERSESSION KIND: replacement`. **CHAIN: r2's two-sided consequence → `[r3, PE3-P1]`'s forward-only scoping. TERMINAL: forward only, at every m.**
**Out of range the forward direction is EXTENDED to `m ≥ 2`**: THEOREM OPEN-2a-Σ, on the accepted Σ-LAW supplier, gives “recorded ξ = 1 ⟹ byte-equal **under every selection rule**, at attempt grade” (1429–1432, `.50`). **So W2-ID1's `m = 1` restriction is now historical** — the same statement holds at every `m`. `SUPERSESSION KIND: license`. **The converse remains UNPROVED at every m** (E5 finding 1's correct-current-status paragraph, 1474, `.55`).

**DERIVATION:** Quoted inline.

*Arithmetic audit (rule 22), every step recomputed.*
- **The formula pair at m = 1.** `(ξ_f, w_f) = (z₁^{−e₁A₁}, 1)` ✓ from `.19` ✓.
- **`w = 1` from j = 0.** Equating `w·ψ₁(y)` with `ψ₁(ξ_f y)` at `y^0`: `w·ψ_{1,0} = ψ_{1,0}` ✓ and `ψ_{1,0} = ψ₁(0) ≠ 0` ✓ ⟹ `w = 1` ✓.
- **`ξ_f^j = 1` on supp.** `ψ₁(ξ_f y) = ψ₁(y)` coefficientwise gives `ψ_{1,j}ξ_f^j = ψ_{1,j}` ✓ ⟹ `ξ_f^j = 1` for `j ∈ supp` ✓ **including the monic top `j = g₁`** ✓.
- **The byte law.** `c = c₁^{e₁g₁}` (from `.10`) and `ξ_f = c₁^{e₁}` (from `.19`) ⟹ `c = ξ_f^{g₁}` ✓. And `z₁^{A₁e₁j} = (z₁^{−e₁A₁})^{−j} = ξ_f^{−j}` ✓. So `c·z₁^{A₁e₁j} = ξ_f^{g₁−j}` ✓, and `ξ_f^{g₁} = 1`, `ξ_f^{j} = 1` on supp ⟹ `ξ_f^{g₁−j} = 1` ✓ **exactly §3.4 rk. 3's m = 1 byte law** ✓ (`.22`).
**Every step reproduces. The lemma is correct as displayed.**

**RESOLUTION TRACE:** statement 707–739 · the counter-instance 741–779 (`.32`) · the box 781–847 (`.33`) · out-of-range extension 1376–1440 (`.49`–`.53`).

**TEETH:** **Instance-exact on the roster: recorded ξ ≠ 1 ⟺ byte-RED at 22/22, the m = 1 slice being 16 r = 3 rows.** **And PE4's exhaustive leg**: “W2-ID1's forward direction **29,223 grid points / 0 violations** incl. g ∈ {3,4}” (`.03`) — **the forward direction is verified far off-roster, including at the g ≥ 3 geography where the converse fails.** Disposition: executable regression, exhaustive; the forward/converse asymmetry is measured, not asserted.

---

### EFF.GRTW2.32  [run-record]  — the `[r3]` CONVERSE'S HONEST BOUNDARY (PE3's counter-instance)

**CANONICAL STATEMENT:** verbatim, lines 741–779.

**FORM:** bold-headed block quoting PE3's construction verbatim, with an `[r4, PE4 o-c]` line-figure correction and a roster-invisibility analysis.

> “**[r3] THE CONVERSE'S HONEST BOUNDARY — PE3's class-pin counter-instance
> at m = 1, recorded here next to the lemma (`GRTW2_passPE3_report.md` §P1;
> quoted, since it is the exact reason the converse direction is not
> claimed).** The sealed `orbit_scan` (grt_w2_checks.py lines ~~135–164~~
> **135–163 [r4, PE4 o-c: `return out` at 163; 164 is the trailing blank —
> re-verified at the sealed source this round]**)
> records the FIRST satisfying ξ in `F.elems()` enumeration order, and for
> extension residue fields that order yields the generator BEFORE 1
> (`Ext.elems` = `itertools.product(base.elems(), repeat=g)`,
> iterlawn_pe_reimpl.py line 220: for F₄, (0,1) = ζ precedes (1,0) = 1).
> PE3's construction, quoted: "Tower: ℤ₂ (or F₂[[t]]), d₀ = 1, Φ₀ = x; read
> 0 = (e₀,h₀,g₀) = (1,1,2) with ψ₀ = y²+y+1 (K₁ = F₄, ζ := z₁); read 1 =
> (2,1,3) with ψ₁ = y³ + ζ (monic, irreducible — x³ = 1 for all x ∈ F₄* so
> no root, and a cubic factorization needs a root — ψ₁(0) = ζ ≠ 0; in the
> [ILN]† S0.1 pin). At the m = 1 junction: e₀ = 1 ⟹ ℓ₀ = 0 ⟹ A₁ = 0 ⟹
> c = 1 and the §3.4 rk. 3 byte law holds trivially — the junction is
> byte-equal, formula pair (1,1). But supp(ψ₁) = {0,3} and ξ³ = 1 for EVERY
> ξ ∈ F₄*, so all three units satisfy the orbit equations, and the sealed
> scan's enumeration records (ζ, 1) — recorded ξ ≠ 1 at a byte-equal
> junction." For that chamber "first recorded ξ ≠ 1 junction = first
> byte-divergence" is FALSE (its ledger r₀ = 3 with no byte-divergence
> anywhere), and the transport fires a spurious conjugation — ψ^tw = ψ since
> ζ stabilizes the support, but the §5.1 step-2 re-coordination
> (a_i) ↦ (a_i·ζ^i) of higher data is nontrivial. Machine-probed by PE3 with
> the scan's ξ-loop semantics copied verbatim (`/tmp/w2_pe3_fresh.py`).
> ROSTER-INVISIBLE: the Tower builder implements only g ∈ {1,2} ("only g in
> {1,2} implemented", iterlawn_pe_reimpl.py line 311), and for g_m ≤ 2 no
> support-stabilizing unit with zero constant coefficient exists (g = 1:
> stabilizer trivial; g = 2 sparse: stabilizer {±1}, nonzero constant term),
> so on the committed roster enumeration order coincides with a ξ = 1
> preference everywhere — consistent with the 22/22 census; the failure
> needs g_m ≥ 3. Under a trivial-preferring selection rule the converse
> WOULD hold at every m (byte-equal ⟹ the trivial pair (1, c) satisfies the
> orbit equations by Thm-`phir` ⟹ recorded ξ = 1 under the preference); this
> note pins no such rule and the sealed runner is BYTE-FROZEN, so the
> converse stays UNCLAIMED — any future round pinning the ξ = 1 preference
> must also disclose that the sealed scan realizes it only where no
> nontrivial support-stabilizing unit precedes 1 in enumeration order (on
> this roster: everywhere; off-roster: not guaranteed, as above).”

**CONDITIONALITY:** **A counter-instance to the note's own converse, constructed by a hostile pass, recorded next to the lemma it bounds, with the roster-invisibility PROVED rather than assumed.** Four things make this the sweep's model disclosure:
(i) **The defect is in the INSTRUMENT's selection rule, not the mathematics** — `F.elems()` enumeration order.
(ii) **The roster-invisibility is derived**: `g ≤ 2` ⟹ no support-stabilizing unit with zero constant coefficient ⟹ enumeration order coincides with a ξ = 1 preference ✓, and “the failure needs `g_m ≥ 3`”.
(iii) **The alternative cure is named and refused**: pinning a ξ = 1 preference would “misdescribe the note's own machine bracket off-roster”, and the runner is frozen (`.43`).
(iv) **PE4 then mapped the failure exhaustively**: “spurious set exactly {(F₄, g = 3, supp {0,3}), (F₉, g = 4, supp {0,4})}, ZERO at g ≤ 2 (roster-invisibility exhaustive)” (`.03`) — **the disclosure condition confirmed as the EXACT characterization.**
**Out of range the boundary EXTENDS to `m ≥ 2` as predicted**: the OPEN2ATTACK annex records “16 constructed spurious-selection witnesses (F₉ y⁴+c recorded ord-4; F₆₄ y³+c recorded ord-3 …)” (1396–1400, `.49`) ✓ — **the genre generalizes exactly as the note said it would.**

**DERIVATION:** A construction, verified four ways (PE3's probe, PE4's from-scratch re-derivation, PE4's exhaustive map, and the OPEN2ATTACK extension).

*Arithmetic audit (rule 22), every claim in the construction recomputed.*
- **`ψ₀ = y²+y+1` over F₂** ⟹ irreducible ✓ (no root in F₂) ⟹ `K₁ = F₄` ✓, `ζ := z₁` a generator ✓.
- **`ψ₁ = y³ + ζ` over F₄ irreducible?** A cubic is irreducible iff it has no root. `x³ = 1` for all `x ∈ F₄^×` ✓ (the group has order 3) ✓, so `x³ + ζ = 1 + ζ ≠ 0` for `x ≠ 0` ✓, and `x = 0` gives `ζ ≠ 0` ✓ ⟹ **no root ⟹ irreducible** ✓ **exactly the displayed argument** ✓. `ψ₁(0) = ζ ≠ 0` ✓ (class pin satisfied).
- **`e₀ = 1 ⟹ ℓ₀ = 0`** ✓ (`.08`) ⟹ `A₁ = ℓ₀g₀γ₁ = 0` ✓ ⟹ `c = c₁^{e₁g₁} = z₁^{−A₁e₁g₁} = 1` ✓ ⟹ **the byte law `c·z₁^{A₁e₁j} = 1` holds trivially** ✓ **byte-equal** ✓, formula pair `(1,1)` ✓ (`ξ = c₁^{e₁} = 1` ✓).
- **The stabilizer.** `supp(ψ₁) = {0,3}` ✓ (`y³ + ζ`). The orbit equations need `ξ^j` constant on the support, i.e. `ξ^0 = ξ^3`, i.e. `ξ³ = 1` ✓ — **and `ξ³ = 1` for EVERY `ξ ∈ F₄^×`** ✓ (order 3) ✓ ⟹ **all three units satisfy them** ✓ **exact.**
- **Roster-invisibility.** `g = 1`: `supp ⊆ {0,1}`, stabilizer needs `ξ⁰ = ξ¹` ⟹ `ξ = 1` ✓ trivial. `g = 2` sparse (`supp = {0,2}`): `ξ² = 1` ⟹ `ξ ∈ {±1}` ✓, and the note's criterion is “no support-stabilizing unit **with zero constant coefficient**” — `supp` containing 0 means the constant term is nonzero ✓, so the sparse `g = 2` case has `ξ = −1` available but the *constant coefficient is nonzero*, which is what blocks the enumeration precedence… **the note's phrasing here is compressed and this compiler cannot fully reconstruct the “zero constant coefficient” criterion from the displayed text.** Recorded as source defect 3: **the roster-invisibility argument's `g = 2` half is stated too tersely to check.** PE4's exhaustive map (`ZERO at g ≤ 2`) supplies the fact independently ✓.
**Everything except the `g = 2` sub-argument reproduces exactly, and PE4's exhaustive leg covers that gap by measurement.**

**RESOLUTION TRACE:** statement 741–779 · the lemma 707–739 (`.31`) · PE4's exhaustive map 54–57 (`.03`) · the m ≥ 2 extension 1396–1400 (`.49`).

ARTIFACT: `verification/openmath/grt_w2_checks.py` ✓ (lines 135–163, the `orbit_scan`) · `iterlawn_pe_reimpl.py` — **verified present** at `verification/openmath/`.
**UNPINNED:** `/tmp/w2_pe3_fresh.py` — a temp-file path; **not present and not expected to be**. Recorded per rule 23 as an UNPINNED run.

**TEETH:** **A counter-instance that FIRED against the note's own converse, verified by four independent routes.** Disposition: `decorrelated-model audit` (rule 27) for the finding; executable regression (PE4's 33,408 checks) for the exact characterization.

---

### EFF.GRTW2.33  [scope-record]  — W2-OPEN-2 and its premise sub-clause (OPEN-2a)

**CANONICAL STATEMENT:** verbatim, lines 781–847 (the box, its `[r2, P3]` index fix, its `[r3]`/`[r4]` converse flags, (OPEN-2a) with its `[r4, PE4-P1]` gloss scoping, the CLAIM (a)/(b), the equivalent sufficient form, and the alternative discharge route).

**FORM:** bold-headed box with four nested bracket layers, an indented CLAIM display, and two closing paragraphs.

> “**W2-OPEN-2 (the chain-level bridging lemma — this note's own open box at
> the chain level; OPEN, instance-confirmed).** In a transported chamber
> with first recorded ξ ≠ 1 junction r₀, consider any junction at GMN order
> r > r₀ (harness level m+1 = r−1). The chamber's keys φ_q^tw are byte-equal
> to the harness keys ~~Φ_q~~ **Φ_{q−1} [r2, P3 — the note's own §1.2
> dictionary (φ_i^GMN = Φ_{i−1}^har) pairs the order-q key with the harness
> Φ_{q−1}; as previously written the comparanda had different degrees]** for
> q < r₀ and byte-DIFFERENT for r₀ ≤ q < r **[r3, PE3-P1: this byte-DIFFERENT
> clause is the CONVERSE direction of the identification (recorded ξ ≠ 1 ⟹
> byte-RED) — unproved at every m and FALSE under the sealed scan's selection
> off-roster … **[r4, PE4 o-e: that chamber's top junction IS its r₀ — 2 reads,
> so this box's range r > r₀ is empty there; instantiating THIS clause's
> falsity strictly means appending any third read, immediate since appending
> a read leaves all lower junction data unchanged and the q = r₀ keys stay
> byte-equal as recorded]**; it stands
> here as part of this OPEN box's premise, alongside (OPEN-2a), not as a
> proved fact]** —
> same weights, same one-sided support, both strict Def-2.12 representatives
> of the same transported type, differing by persistent on-line unit ratios.
> **[r2, P1] (OPEN-2a) — the premise's own open sub-clause … **[r4, PE4-P1 —
> the opening gloss scoped to the proved direction …: (the junction
> identification's FORWARD direction at m ≥ 2): the byte-equality below r₀
> just asserted IS that identification's forward half (recorded ξ = 1 ⟹
> byte-equal …), which this note does NOT prove at m ≥ 2; the CONVERSE is
> UNPROVED at every m including m = 1, PE3's counter-instance recorded at
> LEMMA W2-ID1 above.]** Sub-clause statement: at a junction at level m+1
> with m ≥ 2, keys below byte-shared and recorded ξ = 1, the raw print key is
> byte-equal to the harness key. Status: PROVED at m = 1 (LEMMA W2-ID1
> above); OPEN at m ≥ 2 … instance-exact on the committed roster (22/22
> walked junctions; every below-r₀ junction byte-GREEN — PE2's
> recomputation). A class-pin chamber violating (OPEN-2a) would carry a byte
> divergence below its r₀ with the transport never firing there, putting this
> box's premise out of reach — which is why the sub-clause lives INSIDE the
> box as part of its premise rather than being imported silently.**
> CLAIM:
>
>     (a) v_r(Φ_{m+1}^har) = e_{r−1}f_{r−1}v_r(φ_{r−1}^tw), and the
>         order-(r−1) polygon of Φ_{m+1}^har IN THE TRANSPORTED CHAMBER is
>         one-sided with the harness support        [TW-ADM's vok/onesided];
>     (b) R_{r−1}(Φ_{m+1}^har) = (unit)·ψ_m^tw exactly — STRICT; in
>         particular the (ξ, w) recording of §5.1 step 1 exists at every
>         junction and the transport never aborts    [TW-ADM orbit +
>                                                     TW-STRICT].
>
> Equivalent sufficient form (the key-carry statement …): writing
> Φ_q^har = φ_q^tw + D_q with deg D_q < deg φ_q and D_q on-or-above the key
> line, the φ^tw-devs of the powers (φ^tw + D)^{e_m k} pick up only slot-
> character corrections … never produce a weight drop or a support split at
> any node of the (HR-REC) recursion tree.
> Alternative discharge route: a faithfully transcribed GMN
> representative-independence statement — NOT in this note's
> literature-consumption list; taking it would be a NEW consumption under
> the faithfulness discipline, with its own transcription and audit.”

**CONDITIONALITY:** **This box is the weld's one open lemma and it is ACCEPTED AS A BOX (F3). Its status at HEAD is the product of four out-of-range events, one of which is a WITHDRAWAL of an over-claim.**

**CHAIN for (OPEN-2a)'s forward direction (rule 25):**
1. `[r2, P1]`: folded into the box as its premise sub-clause; **OPEN at m ≥ 2**.
2. `[r3]`/`[r4]`: the gloss and the converse flag scoped to the forward half.
3. **OPEN2ATTACK annex (2026-08-08)**: (OPEN-2a)'s forward direction at `m ≥ 2` **NARROWED to a single displayed lemma** (the Σ-LAW), “Direction: box NARROWED …, NOT closed”.
4. **Σ-LAW annex + count corrections + supplier upgrade**: the Σ-LAW is PROVED and its note ACCEPTED 2/2, so “**(OPEN-2a)'s forward direction at m ≥ 2 is PROVED at attempt grade**” and then rides an accepted supplier.
**TERMINAL for (OPEN-2a) forward: PROVED at attempt grade on an accepted supplier.**

**CHAIN for W2-OPEN-2(a)–(b) itself:**
1. Displayed OPEN, instance-confirmed 44/44.
2. **ANNEX #3 over-claims**: “W2-OPEN-2's residual open surface: the converse … only”.
3. **E5 finding 1 WITHDRAWS that sentence** (1465–1476, `.55`):

> “The final sentence of ANNEX #3, “W2-OPEN-2's residual open surface: the converse (recorded ξ ≠ 1 ⟹ byte-RED) only,” is **WITHDRAWN**. THEOREM OPEN-2a-Σ … proves only the shared-below forward implication … **It does not prove W2-OPEN-2(a)–(b) at any junction above the first recorded twist** \(r_0\). … **Correct current status:** … W2-OPEN-2(a)–(b), the chain-level transfer above \(r_0\), remains **OPEN and instance-confirmed on the six live roster junction-levels**.”

**TERMINAL for W2-OPEN-2(a)–(b): OPEN, instance-confirmed on the six live junction-levels — awaiting sol discharge (cert3).** `SUPERSESSION KIND: replacement` (a withdrawal).

**Two further in-range items:**
(c) **The `[r2, P3]` index fix** (`Φ_q ⇝ Φ_{q−1}`) is the first of two; **E5 finding 3 fixes the SECOND occurrence** in the Equivalent sufficient form (1539–1560, `.57`), which the P3 correction missed. `SUPERSESSION KIND: replacement`. **So the same dictionary was misapplied twice in one box, four months apart.**
(d) **The alternative discharge route is fenced by the faithfulness discipline** (`.06`): taking it “would be a NEW consumption … with its own transcription and audit”.

**DERIVATION:** The box states a claim, not a proof; the sufficient form and the four-route adjudication (`.34`) are its surrounding analysis.

**RESOLUTION TRACE:** statement 781–847 · the adjudication 849–879 (`.34`) · out-of-range: 1376–1403 (narrowed), 1405–1440 (Σ-LAW proved + upgrade), 1459–1476 (E5 finding 1's withdrawal), 1533–1560 (E5 finding 3's index fix).

XREF: `lean/notes/openmath/OPEN2ATTACK_2026-08-08.md` — **verified present**; `lean/notes/openmath/SIGMALAW_PROOF_2026-08-08.md` — **verified present**.
PINS: `bd82766` ✓ `8064ae3` ✓ `59c1ff2` ✓ `6b24942` ✓ `6e57e03` ✓ — 5/5 commits.

**TEETH:** **TW-ADM/TW-STRICT 44/44 across all 16 transported chambers, of which exactly 6 lie above a first twist (the lemma's live region); teeth MT-TW 2/2** (`.34`'s closing). **Disposition: instance-confirmation only — the box is OPEN.** Out of range, (OPEN-2a)'s instance base grows to 470 points (“468 fresh m ≥ 2 junction-levels … the I4A/I4B r = 5 geography swept 50 rows”, 1392–1395, `.49`).

---

### EFF.GRTW2.34  [scope-record]  — the four-route derivability adjudication

**CANONICAL STATEMENT:** verbatim, lines 849–879.

**FORM:** bold-headed paragraph with four numbered routes and a Status line.

> “**Derivability adjudication (r1; four routes, each checked at source —
> none supplies the lemma, which is why it is boxed OPEN rather than cited):**
> (1) **[JC] (COORD-B)/JC-LOC:** machinery for ONE valuation — the harness w
> of a fixed tower, anchors built from harness data. Its
> normalized-coordinate invariance under line-wise rescaling (ρ_λ = 𝑅_λ/a_λ)
> is the right mechanism SHAPE but is proved chamber-internally only; and
> the corpus's sharpest two-operator dictionary, open lemma TR-3′-GEN, is
> OPEN beyond {all order-2} ∪ {order-3 all-e_j = 1}, with its units-only
> phrasing PERMANENTLY REFUTED on the order-3 stratum (ii) (the discrepancy
> is a slot-keyed character) — the accepted corpus itself prices the needed
> two-chain comparison as open. (2) **[JB]'s transport:** JB-DEV/JB-VTX/
> JB-TREE are single-chain harness dev/polygon/tree laws; the Σ(S) transport
> is a WEIGHT-FRAME reparameterization, never a key-representative change
> (JB row 15's 8 chamber walks are machine legs, not theorems). (3)
> **Classical MacLane key-equivalence invariance does not apply:** equal
> augmented valuations require v_{r−1}(Φ^har − φ^tw) ≥ γ (the ASSIGNED
> value); the recorded data warrant only ≥ key weight — with equality
> generic (proportional residuals differing by the unit w·ξ^{g_m}/c) —
> strictly BELOW γ, so the two chains' inductive valuations may genuinely
> differ as functions on O[x], and the lemma is irreducibly a statement
> about the CANONICAL lifts, not an instance of representative-invariance
> of the valuation. (4) **The GMN print:** develops the order-r theory over
> an arbitrary FIXED representative (tex 1288 "we fix a representative …
> without necessarily assuming that it has been constructed by the method
> of Proposition construct"; tex 1719) and itself flags
> representative-DEPENDENCE of derived objects (tex 2053); no independence
> proposition is among this note's consumed anchors, and even one would
> leave the two-recipe comparison (harness canonical lift vs print chamber)
> to prove. **Status: OPEN.** Machine: TW-ADM/TW-STRICT 44/44 junction-levels
> across all 16 transported chambers, of which exactly 6 lie above a first
> twist (the lemma's live region); teeth MT-TW 2/2.”

**CONDITIONALITY:** **A four-route non-derivability adjudication, each route checked at source, and it HELD under a deliberate fifth-route hunt at PE2** — “the four-route adjudication HELD at source under a deliberate fifth-route hunt (Lemma `extension`/Prop `extensionr` are unramified base-change with an exact multiplicative factor ρ_r — no supplier for the ADDITIVE two-recipe comparison; `admissible2` is the right genre but **its cross-term control IS W2-OPEN-2's open content**)” (1127–1131, `.42`). **So five routes were checked and none supplies the lemma.**
**Route (1) is the charge's named item.** It records the corpus's own pricing of the two-chain comparison as open, via **TR-3′-GEN**: “**OPEN beyond {all order-2} ∪ {order-3 all-e_j = 1}, with its units-only phrasing PERMANENTLY REFUTED on the order-3 stratum (ii)**”. `grep -cF 'TR-3′-GEN' GRTJC_PROOF_2026-08-08.md` = **8** ✓ verified. **`spec/HYPOTHESIS_LEDGER.md` HYP.139 quotes GRTJC on exactly this**: “Transport of the harness w and 𝑅 to the FGMN objects is still **W-1 (ATTEMPT)** — and the corpus's own march-level dictionary for that transport, **TR-3′-GEN, is OPEN at general order**.” See `.39` and OPEN-CALL 3.
**Route (3) is the one E5 finding 4 later uses against W2-C3(iii)** (`.29`) — the note's own adjudication contained the refutation of its own equivalence wording.
**Route (4) invokes the faithfulness discipline** (`.06`) to price the alternative as a NEW consumption.

**DERIVATION:** Four source checks; not a derivation.

**RESOLUTION TRACE:** statement 849–879 · the fifth-route hunt 1127–1131 (`.42`) · route (3)'s later use 1562–1594 (`.58`) · the ledger row `spec/HYPOTHESIS_LEDGER.md` HYP.139.

XREF: `GRTJC_PROOF_2026-08-08.md:TR-3′-GEN` — count **8**.
XREF: `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md` ✓ present (route 2's subject).
XREF: `docs/references/HigherNewton.tex` ✓ (tex 1288, 1719, 2053).
ARTIFACT: `spec/HYPOTHESIS_LEDGER.md` ✓ present.

**TEETH:** **TW-ADM/TW-STRICT 44/44 + MT-TW 2/2 (a garbled character caught).** Disposition: instance confirmation; the adjudication itself is a `transfer audit` (rule 27) — five source reads, no instrument.

---

### EFF.GRTW2.35  [scope-record]  — §5.3, W2-OPEN-1 (the value layer)

**CANONICAL STATEMENT:** verbatim, lines 883–902.

**FORM:** `###`-headed section with a bold-headed open lemma, a status line, and an honest-distance paragraph carrying an `[r1, F1]` bracket.

> “**W2-OPEN-1.** On every tower of the class pin, the committed value/
> cocycle battery — K5 = L6-(n) anchor values, K6 = W-MULT top, K7 = THE LAW
> c_{n+1} = z̄^δ·∏_j z_j^{D_j}, K12 = π-shift/ρ-monodromy, K1–K4/K13 riding —
> holds verbatim with the TRANSPORTED classifier lifts substituted for the
> harness lifts (the ClsTower reading: all valuations/reads/anchors/cocycles
> computed ON the transported keys against the harness ψ-byte ledger).
>
> Status: **instance-confirmed, not proved.** [Machine: TW-F3 = 0 violations
> on ALL 16 towers, 684 sample groups — in particular the probe's 96 RED
> (K6: 48, K7: 48 on T3A/T3C/T3D/I4C) all GREEN; TW-F3b control unchanged
> 0.] The honest distance to a proof: the battery's laws are corpus theorems
> about the HARNESS lifts; transporting them across the junction units needs
> the anchor-product carry analysis of §5.4 run level-generically (the
> transported key differs from the harness key by on-line unit ratios, and
> the battery consumes key bytes only through overflow carries — §5.4 —
> whose reads shift by exactly the recorded characters on both sides of the
> cocycle ratio). That analysis is the W-2 → W-5 seam (the correction-tree
> junction J-B) and is NOT claimed here. **[r1, F1: its CHAIN-LEVEL shadow —
> the same carry analysis run on the key objects instead of the anchors — is
> now displayed as the open box W2-OPEN-2 in §5.2.]**”

**CONDITIONALITY:** **OPEN and instance-confirmed, and it stays that way through every event.** E5's consumer sweeps say so three times: “W2-OPEN-1 remains open” (1476), “W2-OPEN-1 remains open and unchanged” (1529), “W2-OPEN-1 remains a comparison computed separately on the transported keys and remains OPEN” (1594) ✓ **three independent re-affirmations in one append.**
**The honest-distance paragraph names the missing analysis and its owner** (the W-2 → W-5 seam, junction J-B) and declines it. **The `[r1, F1]` bracket ties W2-OPEN-1 and W2-OPEN-2 as two shadows of one carry analysis** — anchors vs keys.

*Arithmetic audit (rule 22).* The probe's 96 RED decomposes as “K6: 48, K7: 48 on T3A/T3C/T3D/I4C” ✓ `48 + 48 = 96` ✓ **exact**, and four towers × 12 each × 2 families = 96 ✓ plausible. TW-F3's 684 sample groups over 16 towers ≈ 42.75 per tower — not an integer, so the groups are not uniform per tower; no cross-check available. **Recorded as consistent-but-unverifiable.** The control TW-F3b is “unchanged 0” ✓ — a control that stays at 0 is the right shape (it should not move).

**DERIVATION:** None — the box is open.

**RESOLUTION TRACE:** statement 883–902 · the carry mechanism 906–936 (`.36`) · the three re-affirmations 1476, 1529, 1594 (`.58`).

**TEETH:** **TW-F3 684/684 GREEN with the probe's 96 RED all turning GREEN, plus an unchanged control.** **Disposition: measurement; the strongest instance evidence in the note, and explicitly “instance-confirmed, not proved”.**

---

### EFF.GRTW2.36  [lemma]  — §5.4, LEMMA W2-T3E (carry-inertness of a flat-shielded twist)

**CANONICAL STATEMENT:** verbatim, lines 906–936.

**FORM:** `###`-headed section with a bold-headed lemma, an instance analysis, and an `[r1, F7]` machine-key scope bracket.

> “**LEMMA W2-T3E (carry-inertness of a flat-shielded twist).** The battery
> consumes a diverged key Φ_j only through two channels: (a) exact powers
> in anchors and their products (byte-inert: the dev of a product of pure
> key powers by the key is exact, and the digit is the byte-shared lower
> part); (b) the division carry Φ_{j−1}^{e_{j−1}} ↦ Φ_j − Ĉ fired when an
> anchor product overflows, i.e. when s_j(γ) + s_j(γ′) ≥ e_{j−1} — ONLY
> then do the twisted correction bytes Ĉ enter a read. If e_{j−1} = 1
> directly below the (unique) diverged key, then s_j ≡ 0 identically and
> channel (b) never fires: the twist is CARRY-INERT and every battery
> quantity is byte-identical to the harness computation.
>
> On T3E the only battery-consumed diverged key is the top anchor key Φ₂
> with e₁ = 1 below it: s₂ ≡ 0 on the whole window. [Machine CK-T3E:
> s₂-census = {0}; 0 byte-differing battery digits across all pairs; 0
> violations.] On T3A (e₁ = 2) the overflow pairs exist and are exactly
> where the twisted bytes enter: every K6/K7-failing pair is an overflow
> pair whose top-dev digits differ in bytes (16 failing pairs ⊆ 24
> byte-diff pairs; the reverse containment fails honestly — a carry can be
> read-invisible or a common character can cancel in the cocycle ratio).
> [Machine CK-T3E: containment exact.] **[r1, F7 — machine-key scope: CK-T3E
> keys exactly the byte-diff containment (16 ⊆ 24) and the s₂-censuses ({0}
> on T3E, {0,1} on T3A); the identification of the 24 byte-diff pairs as
> s₂-OVERFLOW pairs is the mechanism's reading (channel (b) of LEMMA
> W2-T3E), asserted per-mechanism and not machine-keyed pair-by-pair.]** T3E is therefore NOT an anomaly: it
> is the e = 1 passthrough leg (the K13 genre) of the same mechanism that
> breaks the other rows — and after transport the question is moot
> (TW-F3 = 0 everywhere).”

**CONDITIONALITY:** **PROVED (mechanism) with a machine leg in both directions** (`.38`'s claims table). The `[r1, F7]` bracket is a **machine-key scope disclosure**: the machine keys the containment and the censuses, but **the identification of the 24 byte-diff pairs as overflow pairs is “asserted per-mechanism and not machine-keyed pair-by-pair”**. `SUPERSESSION KIND: scope-pin` on what the machine establishes. **That is a precise, self-administered downgrade of a machine claim.**
**The reverse containment failure is disclosed and explained**: “a carry can be read-invisible or a common character can cancel in the cocycle ratio” — so `16 ⊆ 24` strictly, honestly.
Untouched by every append.

**DERIVATION:** Quoted inline; channel (b) fires iff `s_j(γ) + s_j(γ′) ≥ e_{j−1}`, which is vacuous at `e_{j−1} = 1` because `s_j ≡ 0`.

*Arithmetic audit (rule 22).* At `e_{j−1} = 1`, the grid offset `s_j = ℓV mod e_{j−1} = ℓV mod 1 = 0` ✓ **identically** ✓ (`.11`'s W2-L0) ⟹ `s_j(γ) + s_j(γ′) = 0 < 1 = e_{j−1}` ✓ **never overflows** ✓ **exactly the displayed argument** ✓. T3E's reads `(2,1,2),(1,1,1),(2,3,1)` have `e₁ = 1` ✓ **the flat middle** ✓, and T3A has `e₁ = 2` ✓ so overflow is possible ✓ (`s₂-census = {0,1}` ✓). **The mechanism reproduces.**

**RESOLUTION TRACE:** statement 906–936 · the value layer it explains 883–902 (`.35`) · the round record 1096–1098 (`.41`).

**TEETH:** **CK-T3E, 2 samples, GREEN — “both directions”** (`.38`). Disposition: executable regression on the mechanism's two halves, **with the per-pair identification explicitly NOT machine-keyed** — a `signed vacuity disclosure` at pair granularity.

---

### EFF.GRTW2.37  [table]  — §6.1, the machine bracket table and the `[r1, F4]` prereg disclosure

**CANONICAL STATEMENT:** verbatim, lines 942–966 (the Markdown table plus the prereg-disclosure bracket).

**FORM:** `###`-headed section with a Markdown table (12 rows) and a bold-headed disclosure bracket.

`[TABLE]` — transcribed verbatim (the source is Markdown; emitted once per rule 14's tables-are-units clause):

| family | claim keyed | samples | verdict |
|---|---|---|---|
| CK-MM | W2-L2 mismatch identity (integers + elements) | 4,396 | GREEN |
| CK-HR1 | W2-L1 base builder read | 156 | GREEN |
| CK-VD1 | W2-L3 level-1 packed dictionary | 156 | GREEN |
| CK-REC | (HR-REC) at every shared-key node | 55 | GREEN |
| CK-SLOT / CK-SLOT-M1 | W2-C2 slot-ratio law / m = 1 exact form | 44 / 16 | GREEN |
| CK-XI | §3.4 (ξ,w) satisfies the orbit equations (21 perimeter junctions; 1 recorded boundary = I4B r=5) | 22 | GREEN |
| CK-BYTE | byte law ⟺ node-value walk | 28 | GREEN |
| TW-RATIO / TW-ADM / TW-STRICT | W2-C3 (i)/(ii) *(with the `[r1, F1]` / `[r2, P1]` grade brackets — see `.30`)* | 44 each | GREEN |
| TW-F3 / TW-F3b | W2-OPEN-1 (96 → 0) / control | 684 / 684 | GREEN |
| TW-PARI / TW-QO | transported (e,f) ties / concrete shapes | 12 / 7 | GREEN |
| CK-T3E | W2-T3E mechanism (both directions) | 2 | GREEN |
| MT-TW | teeth (garbled character caught) | 2 | GREEN |

and the disclosure:

> “**[r1, F4 — prereg disclosure (the runner is byte-frozen, so the
> correction lives here):** the sealed runner's docstring preregisters
> "TW-PARI … PREDICT: 24/24", but the family as executed has **12** samples —
> ONE top lift per ℤ_p row (the transported classifier top); the 24 was the
> probe's both-legs count, copied into the seal. The substantive prediction
> (0 violations) HELD and the note's TW-PARI 12/12 figures are correct; the
> seal's sample-count miscount is disclosed here rather than silently
> absorbed.]**”

*Arithmetic audit (rule 22), the total recomputed from the table.* Summing the sample column: `4,396 + 156 + 156 + 55 + 44 + 16 + 22 + 28 + 44 + 44 + 44 + 684 + 684 + 12 + 7 + 2 + 2`. Step by step: `4,396 + 156 = 4,552`; `+156 = 4,708`; `+55 = 4,763`; `+44 = 4,807`; `+16 = 4,823`; `+22 = 4,845`; `+28 = 4,873`; `+44+44+44 = 5,005`; `+684 = 5,689`; `+684 = 6,373`; `+12 = 6,385`; `+7 = 6,392`; `+2 = 6,394`; `+2 = 6,396`. **Total 6,396 against the header's 6,403 — a shortfall of 7.** The table has **12 rows naming 17 families** (the header says “17 check families”): CK-MM, CK-HR1, CK-VD1, CK-REC, CK-SLOT, CK-SLOT-M1, CK-XI, CK-BYTE, TW-RATIO, TW-ADM, TW-STRICT, TW-F3, TW-F3b, TW-PARI, TW-QO, CK-T3E, MT-TW = **17** ✓ **the family count reproduces exactly.** The 7-sample gap is **not reconcilable from the displayed table** — most plausibly a family with an unlisted sample count (e.g. TW-QO's 7 counted once in the table and again in a per-shape breakdown), but **the note supplies no decomposition**. **Recorded as source defect 4: the sample column sums to 6,396, not the headline 6,403.** No claim is thereby wrong (every family is GREEN with 0 violations), but a merge that re-derives the total will not land on it.
*The prereg disclosure's arithmetic.* “TW-PARI … PREDICT: 24/24” vs 12 executed ✓, explained as “the probe's both-legs count” ✓ — `2 × 12 = 24` ✓ **consistent.** 12 = one top lift per ℤ_p row ✓ and the roster has 16 towers of which the ℤ_p ones number 12? The roster is “ℤ₂/ℤ₃/F₂[[t]]/F₃[[t]]” ✓ — if evenly split, 8 ℤ_p rows, not 12. **No decomposition is given; recorded as unverifiable.** The note is explicit that `F_p[[t]]` rows have no PARI leg (`.40`), which makes 12 ℤ_p top lifts out of 16 towers plausible only under an uneven split. Recorded.

**CONDITIONALITY:**
(a) **The `[r1, F4]` prereg disclosure is a signed miscount in a SEALED docstring**, disclosed because the runner is frozen: “the seal's sample-count miscount is disclosed here rather than silently absorbed”. `SUPERSESSION KIND: counter re-reading`. **The substantive prediction (0 violations) held** ✓.
(b) **The TW-RATIO/TW-ADM/TW-STRICT row carries the grade brackets** and the TW-STRICT SAME-adjacent reclassification (`.30`(b)) — **so the table itself refuses to count three independent 44/44 legs.**
(c) **CK-XI's row separates the boundary junction** (“21 perimeter junctions; 1 recorded boundary = I4B r=5”) ✓ consistent with `.23`.

**DERIVATION:** Machine record.

**RESOLUTION TRACE:** statement 942–966 · the grade brackets 651–705 (`.30`) · the round record 1087–1089 (`.41`).

ARTIFACT: `verification/openmath/grt_w2_checks.py` ✓ · `grt_w2_checks_output.txt` ✓ · `grt_w2_checks_results.json` ✓.
**UNPINNED:** the runner sha256 is truncated at all five occurrences (`.03`).

**TEETH:** this unit IS the teeth roster; the inverse table is §5.

---

### EFF.GRTW2.38  [table]  — §6.2, the claims table (grades)

**CANONICAL STATEMENT:** verbatim, lines 970–983 (the Markdown table; the multi-layer brackets inside the W2-C3, W2-ID1 and W2-OPEN-2 rows are reproduced in the transcription below).

**FORM:** `###`-headed section with a Markdown table (13 rows), three of which carry nested round brackets.

`[TABLE]` — transcribed, with the nested brackets compressed to their TERMINAL readings and the full text pointed at its unit:

| claim | statement | grade as displayed | TERMINAL grade at HEAD |
|---|---|---|---|
| W2-L0/L1/L2/L3 | grid tie; base builder; mismatch identity; VD-1 | PROVED (attempt grade 0/2) | PROVED, and in the accepted enumeration (F3) |
| TH-BASE | r = 2 junctions byte-equal | PROVED | unchanged |
| W2-C1a | vok + one-sided polygon, `[r1, F2]` chamber-qualified | PROVED **as qualified** | unchanged; **explicitly exempted by E5 finding 2** |
| W2-C2(a) | slot law + (ξ,w) = (c₁^{e_m}, 1) at m = 1 | PROVED | unchanged; **E5: “survive unchanged”** |
| W2-C2(b) + §3.4 | scalar (ξ,w) closed form at m ≥ 2 | PROVED **on (C-coll)**; outside: exact recursion (c), boundary boxed W2-BOX-1 | unchanged |
| W2-C1 | clause 1 verdict (strict rep of t^ξ; of t iff support-trivial) | PROVED on the §3 perimeter | **SUPERSEDED outside (C-coll)** by W2-C1-CORR (`.25`) |
| §4.3 | unpinned-ℓ parametrization | CONVENTION ANALYSIS, review-owed | unchanged; **E5: applies only after a scalar pair exists** |
| W2-ID1 `[r2]` | recorded ξ = 1 ⟹ byte-equal at m = 1 `[r4, PE4 o-d: the FORWARD half; the converse unproved at every m]` | PROVED | **forward direction now PROVED at every m** via THEOREM OPEN-2a-Σ on an accepted supplier |
| W2-C3 (i)–(iii) | clause 3 chain level | `[r1, F1]` 38/44 proved + 6/44 measured; `[r2, P1]` 36 derived + 2 instance-warranted; `[r3]` forward direction only | **census re-displayed 37 + 1 + 6** (E5); **(iii)'s equivalence wording SUPERSEDED** to ledger-equivalence |
| W2-OPEN-2 `[r1]` | chain-level bridging lemma; carries (OPEN-2a) and the P3 pairing fix | **OPEN**, instance-confirmed 44/44; not derivable from the accepted corpus | **(OPEN-2a) forward PROVED at every m; W2-OPEN-2(a)–(b) OPEN on the six live junction-levels** (E5 finding 1's withdrawal) |
| W2-OPEN-1 | clause 3 value layer | **OPEN**, instance-confirmed 684 groups / 0 | unchanged — re-affirmed three times by E5 |
| W2-T3E | flat-shielded twists are carry-inert | PROVED (mechanism) + machine both directions | unchanged |

**CONDITIONALITY:** **The table's own grade column is the note's self-assessment and FIVE of its twelve rows have moved.** The TERMINAL column above is compiler-computed from the out-of-range appends and is **not in the source**; each entry cites its unit. `SUPERSESSION KIND` per row as listed at `.25`, `.29`, `.31`, `.33`.
**The `[r4, PE4 o-d]` scoping of the W2-ID1 row and the adjacent W2-OPEN-2 row label are two of the “sweep-completing sites”** found by r4's full-note grep (`.03`) — i.e. the r3 species sweep missed them and r4's grep found them. **That is the note's own lesson, stated at §10: “a species sweep must exhaust the species, not stop at the reviewer's site list”** (1292–1294, `.44`).

*Arithmetic audit (rule 22).* 12 claim rows ✓ covering: 4 base lemmas (as one row) + TH-BASE + W2-C1a + W2-C2(a) + W2-C2(b) + W2-C1 + §4.3 + W2-ID1 + W2-C3 + W2-OPEN-2 + W2-OPEN-1 + W2-T3E ✓. **Three are OPEN or fenced** (W2-OPEN-1, W2-OPEN-2, §4.3) plus W2-BOX-1 inside the W2-C2(b) row ✓ = **the four open surfaces `.40` lists** ✓ **exact match.**

**DERIVATION:** Self-assessment table.

**RESOLUTION TRACE:** statement 970–983 · the five moved rows 1484–1531, 1568–1594, 1459–1476 (`.55`), 1405–1440 (`.50`–`.53`) · the r4 sweep 1283–1309 (`.44`).

**TEETH:** each row names its machine family; the inverse table is §5.

---

### EFF.GRTW2.39  [scope-record]  — §6.3, the consequence display (what J-A / J-B can consume, with caps)

**CANONICAL STATEMENT:** verbatim, lines 985–1014.

**FORM:** `###`-headed section with three bullets, the second carrying four lettered carry-items with nested `[r1]`/`[r2]`/`[r4]` brackets.

> “* **For J-A (W-1, the operator dictionary):** W2-L3 is the level-1 value
>   dictionary IN PROVED FORM (ε = the print twist in canonical
>   coordinates), and (HR-REC) is the exact level-generic transfer shape;
>   but W-1 at orders ≥ 3 is NOT advanced — the level-≥2 dictionary is a
>   conjugation whose scalar collapse needs (C-coll).
> * **For W-2's consumers ([ILN]† applicability):** the corrected W-2 now
>   states — and this note proves at its displayed grades — that the
>   classifier's canonical keys are unit-covariant images of the harness
>   lifts with EXPLICIT characters, and that after ψ-transport the harness
>   value-layer corpus is instance-verified verbatim on classifier lifts.
>   Any consumer citing this must carry: (a) the (C-coll)/recursion split
>   of clause 2; (b) W2-OPEN-1's open status for the general value-layer
>   theorem; (c) the §4.3 convention fence; **(d) [r1, F1] W2-OPEN-2's open
>   status for clause 3's chain level ABOVE each transported chamber's first
>   ξ ≠ 1 junction (the grade split proved-to-first-twist / measured-above),
>   and the chamber qualifier on W2-C1a [r1, F2]** **[r2, P1: including
>   W2-OPEN-2's own premise sub-clause (OPEN-2a) — ~~the recorded-ξ/byte-
>   divergence identification at m ≥ 2, proved only at m = 1 (W2-ID1),~~
>   **[r4, PE4-P1: the FORWARD direction of the recorded-ξ/byte-divergence
>   identification at m ≥ 2 (recorded ξ = 1 ⟹ byte-equal — all the proved
>   scope needs), proved at m = 1 (W2-ID1); the CONVERSE (recorded ξ ≠ 1 ⟹
>   byte-RED) is UNPROVED at every m, PE3's counter-instance recorded at
>   §5.2]**,
>   instance-exact on the roster].**
> * **NOT unlocked:** W-5 (correction-tree transfer: the §5.4 carry
>   analysis is its opening move, not its proof), the J-C block W-6..W-9
>   (no gr claim anywhere here; BLOCKED-ON-CARRIER-TIE stands), J-D counts,
>   and every Phase-B Lean obligation. The P0 application gate stands.”

**CONDITIONALITY — THE W-1 TRANSPORT ATTEMPT ROW (the charge's named item), compiled exactly as the note and the corpus leave it:**

**(1) What this note gives W-1.** Bullet 1 is precise and modest: **W2-L3 in PROVED FORM at level 1**, and HR-REC as “the exact level-generic transfer shape”. **And it states its own limit in the same sentence: “but W-1 at orders ≥ 3 is NOT advanced — the level-≥2 dictionary is a conjugation whose scalar collapse needs (C-coll).”** The Grade cap says the same (`.05`(e)): “Nothing here … advances W-1's operator dictionary beyond the level-1 value dictionary proved below.”

**(2) What the corpus records about W-1, verified per rule 10.** `spec/HYPOTHESIS_LEDGER.md` **HYP.139**, whose WHERE is **`docs/TIGHTNESS_CENSUS_2026-08-11.md` I-4 L48 and §5 L131** — the charge's “census I-4”:

> “STATEMENT: After the FGMN-WELD cite was PDF-verified and DISCHARGED (2026-08-12), the residue is not citational: “Residue is NOT the cite but the transport: **W-1 (harness w, 𝑅 → FGMN objects) stays ATTEMPT**, unchanged by this unit” (I-4); §5 — “the FGMN residue that remains is the W-1 transport (ATTEMPT), which is **a proof obligation, not a citation one**.””

with its consumer chain and class:

> “CONSUMED BY: I-4's own consumer chain — W-9 (proved GIVEN W-6..W-8) → GENHN-4's layer-1 carry bookkeeping at μ≥3 (GENHN-BOX-2) → count laws at μ≥3 … GRTJC L1990–1993 (re-verified at L1990): “Transport of the harness w and 𝑅 to the FGMN objects is still W-1 (ATTEMPT) — and the corpus's own march-level dictionary for that transport, TR-3′-GEN, is OPEN at general order.” This row is the **live residue that does NOT discharge with HYP.148 by a transcription fold** — it is class MATH where HYP.148 is class CARRY.”
> “CLASS: named-obligation … PROPOSED DISPOSITION: **MATH** — an in-cone ATTEMPT-grade proof obligation …”
> “**v6 ARC NOTE (2026-08-14).** … This row is **UNCHANGED, MATH at full strength** — a route that *passes* its hostile arc would retire this row per the v4 note above, but the arc has not yet passed.”

**(3) The compiled status.** **W-1's transport is at ATTEMPT grade, class MATH, at full strength as of 2026-08-14.** GRTW2 does not advance it beyond level 1 and says so twice. **GRTW2's own route (1) (`.34`) independently records the corpus's pricing of the same object**: TR-3′-GEN “is OPEN beyond {all order-2} ∪ {order-3 all-e_j = 1}, with its units-only phrasing **PERMANENTLY REFUTED** on the order-3 stratum (ii)” — `grep -cF 'TR-3′-GEN' GRTJC_PROOF_2026-08-08.md` = **8** ✓, and the ledger quotes GRTJC's own “OPEN at general order” ✓. **The two statements agree**: GRTW2 says the level-≥2 dictionary needs (C-coll); GRTJC/the ledger say the general-order dictionary is open and its units-only form is refuted. **Neither is a discharge, and no route in the corpus currently retires the row** (the candidate — HYP.149's WELD-ZERO fold — is at clean-pass 1 of 2, `.34`-adjacent, recorded at `spec/HYPOTHESIS_LEDGER.md`). See OPEN-CALL 3.

**Other conditionality:**
(a) **Carry item (d) is the note's consumer-facing conditionality and it was scoped THREE times** (`[r1, F1]` → `[r2, P1]` → `[r4, PE4-P1]`). **CHAIN TERMINAL: the `[r4]` forward-direction reading**, itself upgraded out of range (the forward direction is now proved at every m).
(b) **“NOT unlocked” is a four-item negative fence** and it is untouched by every append — including “the J-C block W-6..W-9 (no gr claim anywhere here; **BLOCKED-ON-CARRIER-TIE stands**)”, which is the same gate the Grade cap declines to fire (`.05`).

**DERIVATION:** Consequence declaration.

**RESOLUTION TRACE:** statement 985–1014 · the W-1 limit restated 128–129 (`.05`) · route (1) 851–859 (`.34`) · external: `spec/HYPOTHESIS_LEDGER.md` HYP.139, `docs/TIGHTNESS_CENSUS_2026-08-11.md` I-4.

XREF: `GRTJC_PROOF_2026-08-08.md:TR-3′-GEN` — count **8**.
XREF: `spec/HYPOTHESIS_LEDGER.md:HYP.139` — grep-verified count **20**.
ARTIFACT: `docs/TIGHTNESS_CENSUS_2026-08-11.md` — **verified present**.

**TEETH:** NONE for the W-1 statement — it is a negative claim about what is *not* advanced. **W2-L3's proved level-1 content is toothed by CK-VD1 (156/0)** (`.14`).

---

### EFF.GRTW2.40  [fence]  — §6.4, the dependency line

**CANONICAL STATEMENT:** verbatim, lines 1018–1048.

**FORM:** `###`-headed section body: a CONSUMES/CONSUMED-BY/Fences paragraph with a struck clause and four dated round brackets.

> “CONSUMES: [ILN]† S0.1/S0.2 (accepted package: class pin, canonical lifts,
> REALIZE/WELL-DEF, reads) · GMN print as literature (§ header list, tex
> anchors) · the sealed probe artifacts + its GmnLeg transcription (commit
> 55f7416/a6f7653 line) · GRB D-REAL only as context (no consumption) ·
> GRW2_TIE_DESIGN OB-1..6 only as the named downstream (no consumption).
> CONSUMED BY (intended): the W-1 dictionary unit, the W-5 tree unit, and
> the weld campaign's J-A ledger. Fences: instance evidence = 16 towers
> (reads ≤ 4 + top, residue fields ≤ F₉, wild rows included) + 5 shapes;
> F_p[[t]] rows have no PARI leg (displayed deferral, inherited); nothing
> here is a Lean artifact; ~~no acceptance arc opened — hostile passes owed
> before any consumption at proof grade~~ **[r1] the acceptance arc is OPEN
> (S-STATUS block, top): PE1 run (0C + 2G + 5m), r1 applied, counter 0/2 —
> 2-clean owed before any consumption at proof grade. The note's open boxes
> after r1: W2-OPEN-1 (value layer) + W2-OPEN-2 (chain level above a first
> twist) + W2-BOX-1 (scalar form off (C-coll)) + the §4.3 convention fence.**
> **[r2] PE2 run (0C + 2G + 1m, 79e796b), r2 applied, counter 0/2, PE3 next;
> open boxes unchanged in count — W2-OPEN-2 now carries its premise
> sub-clause (OPEN-2a) explicitly, and the new proved lemma W2-ID1 (§5.2)
> closes the m = 1 slice of that identification **[r4, PE4-P1: = of its
> FORWARD direction only …]**.** **[r3] PE3 run (0C + 1G
> minor, 9bd938f), r3 applied, counter 0/2, PE4 next; open boxes unchanged in
> count …** **[r4] PE4 run
> (0C + 1G minor + 1m, e92cb22), r4 applied, counter 0/2, PE5 next; open
> boxes unchanged in count …**”

**CONDITIONALITY:**
(a) **“CONSUMED BY (intended): the W-1 dictionary unit …”** — an *intended* consumer, i.e. the W-1 unit does not yet exist as a consumer of this note. Consistent with `.39` and HYP.139's ATTEMPT status.
(b) **`STALE-SELF-DESCRIPTION`** on all four “counter 0/2” entries and on “2-clean owed before any consumption at proof grade” — **the 2-clean landed** (PE5 + PE6) and the acceptance record's CONSEQUENCE reads “consumers riding W-2 at attempt grade … now ride an ACCEPTED supplier at its fenced scope” (1350–1353, `.46`).
(c) **“open boxes unchanged in count” is repeated at r2, r3 and r4** ✓ — **and it stays true through the whole in-range arc: four open surfaces throughout.** Out of range the count *does* change: (OPEN-2a) leaves the open set (proved), and W2-OPEN-2(a)–(b) narrows to six junction-levels. **Neither event is folded back into this line.** Recorded as source defect 5.
(d) **The `F_p[[t]]` PARI deferral is inherited from the probe** — a foreign fence carried forward.

**DERIVATION:** Dependency declaration.

**RESOLUTION TRACE:** statement 1018–1048 · the acceptance 1334–1353 (`.46`) · the box movements 1376–1440, 1459–1476 (`.55`).

PINS: `55f7416` ✓ `a6f7653` ✓ `79e796b` ✓ `9bd938f` ✓ `e92cb22` ✓ — 5/5.
ARTIFACT: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md` ✓ · `lean/notes/openmath/GRTWELD_PROBE_2026-08-08.md` ✓.

**TEETH:** the fences are declarations; the instance-evidence figure (16 towers + 5 shapes) is the roster of `.07`.

---

### EFF.GRTW2.41  [changes-record]  — §7, the r1 round record

**CANONICAL STATEMENT:** verbatim, lines 1052–1117 (the Against paragraph, the seven-finding repair map, the fold implications, and the Freeze paragraph).

**FORM:** `##`-headed round block: a bold-headed Against paragraph, seven bulleted findings, a bold-headed fold paragraph, and a bold-headed Freeze paragraph.

> “**Against:** W2-PE1 (`GRTW2_passPE1_report.md`, commit 083adff; target
> 5463f2a) — 0 CRITICAL, 2 JUSTIFICATION GAPS, 5 minor; core mathematics
> CONFIRMED by full re-derivation (PE1 §A), machine leg re-run bit-identical
> (PE1 §B). Repair map, finding → edit site: …
>
> **Fold implications recorded for the orchestrator (accepted texts are
> NEVER edited by this unit):** WELDMASTER's (M4) face quotes W2-C3
> ("ψ-transport: strict representative at every level of the transported
> chain, no weight/support splits") under its as-of pin [W2]@5463f2a (WM
> r3's O-1 pin group) — the pin makes that face drift-proof and PE1
> adjudicated that it carries the conditionality BY CITATION, so nothing is
> falsified; at the next ledger fold a dated annotation pointing (M4)'s
> W2-C3 cite at the re-scoped grade (proved-to-first-twist / measured-above
> / W2-OPEN-2) is owed, and likewise JB §0M row 15's subordinate
> "(representative reading; W2-C3 chamber off the byte perimeter)" cell.
> Both are orchestrator actions, not r1 edits.
>
> **Freeze:** r1 is note-only. `grt_w2_checks.py` (sha256 71f8fc90f7543fd3…,
> PE1-verified bit-identical to 5463f2a) and both artifacts untouched; a
> stray working-tree drift on `grt_w2_checks_results.json` (elapsed_s only,
> left by a prior pass's re-run) was restored to the committed bytes before
> this round's edits. **Counter 0/2 (ZERO clean passes); W2-PE2 — a fresh
> hostile pass on this post-r1 text — is the next acceptance attempt.**”

**CONDITIONALITY:**
(a) **The seven findings' repair sites are all located in this shard**: F1 → `.29`/`.30`/`.33`/`.34`; F2 → `.24`; F3 → `.18`/`.22`; F4 → `.37`; F5 → `.23`; F6 → `.26` (reverted at r2); F7 → `.36`. **All seven located and non-empty** ✓.
(b) **The fold implications are the note's no-append protocol in action** — two annotations recorded as owed to the orchestrator, **and both were EXECUTED out of range** (the 2026-08-08 fold-carry annex, 1359–1374, `.48`): GRTJB row 15 at `5054d69` ✓, WELDMASTER (M4) at the annex's own fold, “the half that had to wait for WELDMASTER's own acceptance (66b3498)” ✓ commit verified. **The annex's closing line: “Nothing else in the r1 record remains orchestrator-owed.”** `SUPERSESSION KIND: inventory completion`.
(c) **The Freeze paragraph records a drift RECOVERY** — an `elapsed_s`-only working-tree drift restored before editing. **That is the only instrument-integrity event in the arc and it was caught and reversed.**
(d) **PE1 confirmed the core mathematics by full independent re-derivation** — the strongest positive result of the arc's first pass.

*Arithmetic audit (rule 22).* “0 CRITICAL, 2 JUSTIFICATION GAPS, 5 minor” = 7 findings ✓ and the repair map has 7 bullets (F1–F7) ✓ **exact**. The F3 recount is audited at `.22` ✓.

**DERIVATION:** Round record.

**RESOLUTION TRACE:** statement 1052–1117 · the fold's execution 1359–1374 (`.48`) · the seven sites as listed.

PINS: `083adff` ✓ `5463f2a` ✓ `5054d69` ✓ `66b3498` ✓ — 4/4.

**TEETH:** PE1's full re-derivation (a hostile pass re-deriving the core) + the bit-identical machine re-run. **Disposition: `in-house hostile pass` (rule 27) + executable regression.**

---

### EFF.GRTW2.42  [changes-record]  — §8, the r2 round record

**CANONICAL STATEMENT:** verbatim, lines 1121–1193.

**FORM:** `##`-headed round block: Against paragraph with PE2's confirmations, three bulleted findings, fold implications, Freeze.

> “**Against:** W2-PE2 (`GRTW2_passPE2_report.md`, commit 79e796b; target
> 8d5e3fa) — 0 CRITICAL, 2 JUSTIFICATION GAPS (P1 moderate, P2 minor),
> 1 minor (P3), NOT CLEAN. PE2 also CONFIRMED: the four-route derivability
> adjudication holds at source, with a deliberate fifth-route hunt finding
> no supplier (Lemma `extension`/Prop `extensionr` are unramified base-change
> with an exact multiplicative factor ρ_r — no supplier for the ADDITIVE
> two-recipe comparison; `admissible2` is the right genre but its cross-term
> control IS W2-OPEN-2's open content); machine leg re-run byte-identical
> (exit 0, 6,403/0, 17 GREEN, both artifacts byte-identical incl. elapsed);
> fresh leg — the §3.4 display evaluated against the committed ξ-ledger by
> from-scratch arithmetic, 16/16 at m = 1 (unique pairs, full support) plus
> hand re-derivations T3B/T3F r = 4 matching the ledger. …”

**CONDITIONALITY:**
(a) **The fifth-route hunt is the strongest confirmation W2-OPEN-2 gets**: two further print objects checked (`extension`/`extensionr`, `admissible2`) and neither supplies the lemma — with the sharp verdict that “`admissible2` is the right genre but **its cross-term control IS W2-OPEN-2's open content**”. **So the box is not for want of looking.**
(b) **P2's revert is adjudicated at source** (`.26`) — PE2 read tex 1431/1373/1447/1201 and found the r0 sign correct.
(c) **P3's index fix is the first of two** (`.09`, `.33`).
(d) **`STALE-SELF-DESCRIPTION`** on “counter 0/2 … W2-PE3 … next”.
(e) **The fold implications add one new item**: WM line 88's “its only commit” is STALE, with an `[r3, o1]` line-drift annotation. **A stale pointer in an accepted supplier, flagged and left to the orchestrator.**

*Arithmetic audit (rule 22).* “0C + 2G + 1m” = 3 findings ✓ and three bullets (P1, P2, P3) ✓. The fresh leg's `16/16 at m = 1` ✓ matches the 16 r = 3 junctions (one per tower) ✓ (`.22`, `.31`).

**DERIVATION:** Round record.

**RESOLUTION TRACE:** statement 1121–1193 · P1 → `.30`/`.31`/`.33`; P2 → `.13`/`.26`; P3 → `.33` · the WM staleness 1184–1186.

PINS: `79e796b` ✓ `8d5e3fa` ✓ `f8c2c09` ✓ (WM r5, cited in the `[r3, o1]` annotation) — 3/3.

**TEETH:** PE2's from-scratch §3.4 evaluation (16/16) + hand re-derivations at T3B/T3F. **Disposition: executable regression on a decorrelated instrument + hand verification.**

---

### EFF.GRTW2.43  [changes-record]  — §9, the r3 round record

**CANONICAL STATEMENT:** verbatim, lines 1197–1257.

**FORM:** `##`-headed round block: Against paragraph with PE3's five confirmations, one bulleted finding with a four-part cure, the two ungraded observations, and Freeze.

> “**Against:** W2-PE3 (`GRTW2_passPE3_report.md`, commit 9bd938f; target
> ffa1e57) — 0 CRITICAL, 1 JUSTIFICATION GAP (minor; P1, CONFIRMED by
> construction + probe), NOT CLEAN. PE3 also CONFIRMED: LEMMA W2-ID1's
> statement and proof SOUND (re-derived from the §3.4 display, valid for any
> recorded pair with ξ = 1); (OPEN-2a) exactly the m ≥ 2 inductive step the
> re-scope warrant needs — nothing weaker suffices, nothing stronger
> smuggled; the 36+2 census exact (recomputed from the committed JSON with an
> independent is-one test — 36 fully derived = 16 r = 2 + 16 r = 3 + 4 r = 4,
> the 2 instance-warranted = I4A/I4B r = 5); the P2 sign revert faithful at
> source (tex 1431/1373/1447/1201 line-exact, shift computation re-derived,
> no k ↦ −k gloss) and the anti-re-flip records adequate; the P3 pairing
> dictionary-correct; machine leg re-run exit 0, 6,403/0, 17 GREEN,
> bit-identical mod timing, both seals intact; FRESH LEG (route unused by
> PE1/PE2) — own tower-field arithmetic + own §3.4 evaluator vs the committed
> ledger modulo the support stabilizer at FULL roster scope, 22/22 (incl. the
> invisible-twist I4B r = 4 consistent and T3B/T3F r = 4 exact) + the I4B
> r = 5 boundary reproduced from scratch. …”

**CONDITIONALITY:**
(a) **PE3's confirmation list is the arc's densest**: five separate re-derivations, including “**(OPEN-2a) exactly the m ≥ 2 inductive step the re-scope warrant needs — nothing weaker suffices, nothing stronger smuggled**”. **That is a hostile pass certifying that a BOX is the right size** — neither over- nor under-claimed.
(b) **The 36 + 2 census is recomputed by an independent is-one test** ✓ audited at `.05`.
(c) **The four-part cure (a)–(d) is where the forward-direction scoping happens**, and part (d) is a *verbatim re-read* of every consuming surface — “each consume ONLY the proved direction — agreeing with PE3 §P1 "blast radius: contained"”.
(d) **The alternative cure is refused with a reason** (`.27`(b)) — pinning a ξ = 1 preference would misdescribe the frozen instrument. **This is the sweep's clearest instance of text being kept honest to a machine rather than the reverse.**
(e) **`STALE-SELF-DESCRIPTION`** on “counter 0/2 … W2-PE4 … next”.
(f) **The r3 sweep was INCOMPLETE and r4 says so**: “The r3 sweep stopped at PE3's four listed sites; three same-species surfaces still carried the two-sided … vocabulary” (1283–1285, `.44`), with the lesson “a species sweep must exhaust the species, not stop at the reviewer's site list”. `SUPERSESSION KIND: inventory completion`.

*Arithmetic audit (rule 22).* PE3's census decomposition `36 = 16 + 16 + 4` ✓ **exact** (`.05`); `36 + 2 = 38` ✓; `38 + 6 = 44` ✓. “0C + 1G” = 1 finding ✓ and one bullet ✓ (plus three ungraded observations o1/o2/o3, of which o3 “accrues to JA's ledger, not this note's; no edit” ✓).

**DERIVATION:** Round record.

**RESOLUTION TRACE:** statement 1197–1257 · the cure's four parts → `.31`, `.32`, `.33`, `.05` · the sweep's incompleteness 1283–1309 (`.44`).

PINS: `9bd938f` ✓ `ffa1e57` ✓ — 2/2.

**TEETH:** **PE3's FRESH LEG on a route unused by PE1/PE2** — own tower-field arithmetic + own §3.4 evaluator at full roster scope, 22/22, plus the I4B r = 5 boundary reproduced from scratch. **Disposition: executable regression on a third decorrelated instrument; and the counter-instance (`.32`) is a fired planted construction from the same pass.**

---

### EFF.GRTW2.44  [changes-record] · SERIES: GRTW2-GRADE-ARC, member 6 of 7

**CANONICAL STATEMENT:** verbatim, lines 1261–1327 (the §10 round block: Against paragraph with PE4's confirmations, the P1/P2 repair map, the five observations, and Freeze).

**FORM:** `##`-headed round block.

> “**Against:** W2-PE4 (`GRTW2_passPE4_report.md`, commit e92cb22; target
> 79d1d9c) — 0 CRITICAL, 1 JUSTIFICATION GAP (minor; P1, the residual of
> PE3-P1's species at sites the r3 sweep did not reach), 1 minor (P2, the
> footer dateline), NOT CLEAN. PE4 also CONFIRMED: the r3 diff faithful at
> every edit site; the counter-instance TRUE by from-scratch re-derivation
> (own field arithmetic, checks B1–B8 all PASS; the sealed enum order
> (0,1) = ζ before (1,0) = 1 cross-checked at source); the [r3] converse
> flag inside W2-OPEN-2's premise SUFFICES — the premise does NOT need
> restating (PE4 §ADJ: the clause functions as scope, not warrant; restating
> would change the box's mathematical content; no consumer needs the clause
> off-roster — NO finding); machine leg re-run exit 0, 6,403/0, 17 GREEN,
> results JSON byte-identical incl. elapsed_s, both seals intact; FRESH LEG
> (route unused by PE1–PE3) — exhaustive selection-geography mapping at
> m = 1: 33,408 checks / 0 failures over 4,173 monic irreducibles × 7
> fields; spurious set exactly {(F₄, g = 3, supp {0,3}), (F₉, g = 4,
> supp {0,4})}, ZERO at g ≤ 2 (roster-invisibility exhaustive); the r3
> disclosure condition confirmed the EXACT characterization; W2-ID1's
> forward direction 29,223 grid points / 0 violations incl. g ∈ {3,4}.
> Repair map, finding → edit site:
>
> * **P1 (minor gap) → the r3 scoping COMPLETED across the species.** The
>   r3 sweep stopped at PE3's four listed sites; three same-species surfaces
>   still carried the two-sided "identification … proved at m = 1"
>   vocabulary. Cure, per PE4's repair queue — one clause each, the r3
>   wording: (a) §6.3(d)'s carry item "proved only at m = 1 (W2-ID1)" scoped
>   to the forward direction; (b) the §5.2 (OPEN-2a) opening gloss ("IS the
>   identification …") scoped to the forward half, matching the sub-clause
>   statement it glosses; (c) §6.4's [r2] "closes the m = 1 slice of that
>   identification" annotated inline (the dated-record convention r3 used at
>   §8 P1(a)). SWEEP COMPLETION — the r3 lesson applied (a species sweep
>   must exhaust the species, not stop at the reviewer's site list): this
>   round grepped every "identification" token at HEAD and dispositioned
>   each. Additionally scoped: the §6.2 W2-ID1-row appositive "(the boundary
>   identification, m = 1 case)" (PE4 o-d, the named sweep candidate) and
>   the adjacent W2-OPEN-2-row label "the m ≥ 2 junction identification"
>   (same appositive species, weakest form); the [r1, F1] block's universal
>   "ABOVE r₀ … byte-DIFFERENT" got PE4's prescribed roster-instance
>   qualifier (o-b). Every remaining token verified in place: correctly
>   scoped [r3]/[r4] sites; historical records that QUOTE the species
>   vocabulary as the thing being cured (S-STATUS, §6.4 [r3], §8 P1, §9 P1);
>   the on-roster instance-exactness statements (machine-true two-sidedly:
>   recorded ξ ≠ 1 ⟺ byte-RED at 22/22, PE2/PE3/PE4 recomputations); and
>   different senses entirely (§5.1's letter identification z_old = ξ·z_new;
>   §5.4/§7's overflow identification of the 24 byte-diff pairs). Blast
>   radius nil before and after: PE4 re-read every load-bearing consumption
>   one-directional; this round changed no operative statement — display
>   brackets only.
> * **P2 (minor) → the footer dateline extended** …
> * **The observations → one line each.** (o-a) no edit: PE4 §ADJ
>   adjudicated the [r3] flag sufficient; the operative marking covers all
>   q. (o-b) folded into the P1 sweep above. (o-c) the counter-instance
>   block's `orbit_scan` line figure corrected to 135–163 (`return out` at
>   163; 164 is the trailing blank — re-verified at the sealed source this
>   round, seal 71f8fc90 intact). (o-d) folded into the P1 sweep above.
>   (o-e) a one-sentence precision added inside the W2-OPEN-2 [r3] flag:
>   the recorded chamber's top junction IS its r₀ (2 reads), so
>   instantiating the premise clause's falsity strictly means appending any
>   third read — immediate, lower junction data unchanged.
>
> **Freeze:** r4 is note-only. `grt_w2_checks.py` (sha256 71f8fc90f7543fd3…,
> PE4-verified byte-identical across working tree, 5463f2a, and HEAD) and
> both artifacts untouched. **Counter 0/2 (ZERO clean passes); W2-PE5 — a
> fresh hostile pass on THIS post-r4 text — is the next acceptance attempt.**”

**CONDITIONALITY:** **`STALE-SELF-DESCRIPTION` (rule 26)** on “Counter 0/2 … W2-PE5 … is the next acceptance attempt” — PE5 and PE6 both returned CLEAN and the counter is **2/2** (`.46`). SERIES `GRTW2-GRADE-ARC` member 6; member 7 is the acceptance record.
**Three properties of this round are load-bearing and should travel:**
(i) **The r3 sweep's incompleteness is diagnosed as a METHOD failure and the method is fixed**: “the r3 lesson applied (**a species sweep must exhaust the species, not stop at the reviewer's site list**): this round grepped every "identification" token at HEAD and dispositioned each.” **That is a process correction, not a text correction.**
(ii) **A hostile pass DECLINED to raise a finding it had standing to raise** (o-a / PE4 §ADJ): “the [r3] converse flag inside W2-OPEN-2's premise SUFFICES — the premise does NOT need restating … **restating would change the box's mathematical content** … — NO finding.” **A reviewer refusing to force a change that would enlarge a claim.**
(iii) **PE4's fresh leg turned the r3 DISCLOSURE into an EXACT CHARACTERIZATION**: “spurious set exactly {(F₄, g = 3, supp {0,3}), (F₉, g = 4, supp {0,4})}, **ZERO at g ≤ 2 (roster-invisibility exhaustive)**”. **So `.32`'s roster-invisibility, whose `g = 2` sub-argument this compiler could not check from the text (shard 1's own source defect 3, carried forward in the merged §8), is established by exhaustive measurement instead.**
**The `[r4] o-c` line-figure fix is a one-token correction to a citation into the frozen runner** (`164 → 163`), re-verified at the sealed source with the seal intact — an unusually small correction, disclosed.

*Arithmetic audit (rule 22).* “0C + 1G + 1m” = 2 findings ✓ and two repair bullets (P1, P2) ✓, plus five observations (o-a … o-e) ✓ of which two are “folded into the P1 sweep” and one is “no edit” ✓ — so **two observations produced text (o-c, o-e)** ✓ consistent with the S-STATUS summary (`.03`: “plus o-c … and o-e …”) ✓. PE4's leg: `4,173 monic irreducibles × 7 fields ≈ 29,211`, and the reported grid for W2-ID1's forward direction is **29,223** — within 12 of the product, consistent with a few fields contributing extra rows; the total leg is **33,408** checks ✓ larger than the grid ✓ (the grid is one family within the leg). **No exact decomposition is derivable; recorded as consistent-but-unverifiable.** The `6,403/0, 17 GREEN` figures ✓ match every other round (`.37`, and its 6,396-vs-6,403 gap is unchanged here).

**DERIVATION:** Round record.

**RESOLUTION TRACE:** statement 1261–1327 · the three scoped surfaces `.39`, `.33`, `.40` · the two sweep-completing sites `.38` · the o-b qualifier `.30` · the o-c/o-e precisions `.32`, `.33` · the terminal grade 1336–1339 (`.46`).

PINS: `e92cb22` ✓ · `79d1d9c` ✓ — 2/2 commits.
ARTIFACT: `lean/notes/openmath/GRTW2_passPE4_report.md` ✓ present.
**UNPINNED:** the runner sha256 `71f8fc90f7543fd3…`, truncated again (its fifth occurrence).

**TEETH:** **PE4's exhaustive selection-geography leg — 33,408 checks / 0 failures over 4,173 monic irreducibles × 7 fields, plus 29,223 grid points / 0 violations for W2-ID1's forward direction including g ∈ {3,4}.** **Disposition: executable regression on a fourth decorrelated instrument, exhaustive over the failure geography.** This is the arc's largest single leg and it converts a disclosure into a characterization.

---

### EFF.GRTW2.45  [changes-record]  — the footer dateline

**CANONICAL STATEMENT:** verbatim, lines 1329–1330.

**FORM:** em-dash footer line.

> “— W-2 COMPOSER unit, campaign date 2026-08-08; r1 2026-08-06; r2 2026-08-07;
> r3 2026-08-07; r4 2026-08-07.”

**CONDITIONALITY:** **The dateline is the r4 P2 repair's product** (`.44`) — r3's entry had been omitted and r4 added both. **A convention is stated with it**: “per the arc's convention that each round extends the dateline” (1311–1312).
**One oddity worth recording**: the campaign date (2026-08-08) is *later* than every round date (2026-08-06/07), so the dateline reads chronologically backwards. That is consistent with “campaign date” meaning the composition/seal campaign rather than the last edit. Recorded as source defect 1 (a reading hazard, not an error).
**The dateline is NOT extended by the acceptance record, the five annexes or the sol append** — all of which postdate it (2026-08-07 acceptance, 2026-08-08 annexes, 2026-08-12 sol). `STALE-SELF-DESCRIPTION` in the weak sense: the footer stops at r4.

**DERIVATION:** Bookkeeping.

**RESOLUTION TRACE:** statement 1329–1330 · the repair 1310–1312 (`.44`) · the later dated events 1334, 1357–1440, 1444–1632.

**TEETH:** NONE.

---

### EFF.GRTW2.46  [acceptance-box] · SERIES: GRTW2-GRADE-ARC, member 7 of 7 (TERMINAL)

**CANONICAL STATEMENT:** verbatim, lines 1334–1353.

**FORM:** `## ★`-headed record with a bold verdict, a full-arc line, a **WHAT IS ACCEPTED** enumeration, and a CONSEQUENCE.

> “## ★ ACCEPTANCE RECORD (orchestrator, 2026-08-07) ★
>
> **THIS NOTE IS ACCEPTED at 2/2** — PE5 (ba2c47c, CLEAN; the 17-theorem
> Lean leg) and PE6 (9d8aba0, CLEAN; the Sylvester-resultant route on 566
> junctions incl. 560 off-roster, the functional-equation re-derivation of
> HR-REC, the PE5 Lean appendix recompiled). Full arc: composed → PE1
> (0C+2G+5m) → r1 (the honest W2-C3 re-scope; the four-route adjudication;
> W2-OPEN-2 minted) → PE2 (0C+2G+1m) → r2 (LEMMA W2-ID1; OPEN-2a folded in;
> the sign reverted) → PE3 (0C+1Gm) → r3 (the proved-direction scoping +
> THE CONVERSE'S HONEST BOUNDARY) → PE4 (0C+1Gm+1m) → r4 (five surfaces,
> completeness grep) → PE5 CLEAN → PE6 CLEAN. **WHAT IS ACCEPTED**: the
> (ξ,w) covariance closed form, HR-REC, W2-L0–L3, W2-C1 (chamber-qualified),
> W2-C2, W2-C3 at its honest grade (proved-to-first-twist 38/44 = 36
> derived + 2 instance-warranted; measured above), LEMMA W2-ID1 (forward
> direction, with the converse's counter-instance displayed), and
> **W2-OPEN-2/OPEN-2a as the note's fenced OPEN box — the weld's one open
> lemma, accepted AS A BOX, not as a theorem.** CONSEQUENCE: consumers
> riding W-2 at attempt grade (the accepted LIFTCORNER's shift-descent
> consumption; JB's W2-C1 restriction; WM's M4 face) now ride an ACCEPTED
> supplier at its fenced scope.”

**CONDITIONALITY:** **TERMINAL grade: ACCEPTED 2/2. And the enumeration (F3) is what the acceptance means.**
(a) **Two of the enumerated items have since MOVED**: “W2-C1 (chamber-qualified)” is **SUPERSEDED outside (C-coll)** by W2-C1-CORR (`.56`), and “W2-C3 at its honest grade (… 38/44 = 36 derived + 2 instance-warranted …)” is **re-displayed as 37 + 1 + 6** (`.56`'s consumer sweep). `SUPERSESSION KIND: replacement` and `counter re-reading`. **So the acceptance's own enumeration is partly stale at HEAD** — which is exactly what finding 5's ARTIFACT rebuttal addresses (`.59`): PE5/PE6 certify the frozen body, not later annexes.
(b) **“LEMMA W2-ID1 (forward direction …)” has since STRENGTHENED**: the forward direction now holds at every `m` via THEOREM OPEN-2a-Σ on an accepted supplier (`.50`, `.53`).
(c) **“W2-OPEN-2/OPEN-2a as … accepted AS A BOX”** — and (OPEN-2a) has since left the box (proved), while W2-OPEN-2(a)–(b) remains OPEN on six junction-levels (`.55`).
(d) **PE6's leg is the arc's widest**: “the Sylvester-resultant route on **566 junctions incl. 560 off-roster**, the functional-equation re-derivation of HR-REC”. **560 off-roster junctions is roughly 13× the 44-junction roster** — and HR-REC was re-derived by a functionally different route ✓.
(e) **PE5's leg is a Lean leg** (“the 17-theorem Lean leg”) — the only Lean contact in this note, and the note is explicit elsewhere that “nothing here is a Lean artifact” (`.40`), i.e. the Lean leg is the *pass's* instrument, not the note's.

*Arithmetic audit (rule 22).* The full arc line lists 4 passes + 4 rounds + 2 clean passes ✓ matching `.03`'s arc ✓ and adding PE5/PE6 ✓. Finding counts across the arc: `7 + 3 + 1 + 2 + 0 + 0` ✓ — **monotone to zero** ✓. Two consecutive CLEAN passes ⟹ 2/2 ✓ under the corpus's standing bar ✓. PE6's `566 junctions incl. 560 off-roster` ⟹ 6 on-roster ✓ — **and 6 is the number of above-twist junction-levels** (`.15`, `.30`); whether that is the same 6 is not stated. **Recorded as a suggestive but unconfirmed coincidence.**

**DERIVATION:** Acceptance record.

**RESOLUTION TRACE:** statement 1334–1353 · the enumerated items' later movement 1465–1476 (`.55`), 1484–1531 (`.56`), 1405–1440 (`.50`, `.53`) · the ARTIFACT rebuttal 1596–1612 (`.59`).

PINS: `ba2c47c` ✓ · `9d8aba0` ✓ · `adc6cf3` ✓ (the acceptance commit, cited at `.48`) — 3/3.

**TEETH:** **PE5's 17-theorem Lean leg + PE6's 566-junction Sylvester-resultant route with an independent functional-equation re-derivation of HR-REC.** **Disposition: two decorrelated instruments on two clean passes; the widest coverage in the arc (560 off-roster junctions).**

---

### EFF.GRTW2.47  [fence]  — the ANNEX header

**CANONICAL STATEMENT:** verbatim, line 1357.

**FORM:** `##` heading.

> “## ANNEX (dated append; the frozen body is not edited)”

**CONDITIONALITY:** **Freeze predicate (F1)'s post-acceptance form, and it is load-bearing for finding 5's rebuttal** (`.59`): the note “explicitly separates the accepted frozen body from later ledger entries”, and this heading is the separator the certifier quotes. Untouched.

**DERIVATION:** Declaration.

**RESOLUTION TRACE:** statement 1357 · quoted by the certifier at 1602 (`.59`).

**TEETH:** NONE.

---

### EFF.GRTW2.48  [changes-record]  — ANNEX 1 (fold-carry closure): both r1 fold implications discharged

**CANONICAL STATEMENT:** verbatim, lines 1359–1374.

**FORM:** blockquoted dated annex.

> “> **[ANNEX 2026-08-08, orchestrator, fold-carry closure — the §[r1] fold
> implications, both discharged.]** The r1 round record's bracket "Fold
> implications recorded for the orchestrator (accepted texts are NEVER
> edited by this unit)" left two dated annotations owed at the next ledger
> fold: (i) GRTJB §0M row 15's subordinate "(representative reading; W2-C3
> chamber off the byte perimeter)" cell — EXECUTED at 5054d69 (2026-08-07,
> GRTJB fold-annex erratum E-2: row-15 W-2 grade citations governed by
> supplier HEAD); (ii) WELDMASTER (M4)'s W2-C3 cite pointed at the
> re-scoped grade — EXECUTED at THIS fold (WELDMASTER annex O-1, this
> commit), the half that had to wait for WELDMASTER's own acceptance
> (66b3498) to become an accepted-text annex item (while WM was in-arc its
> own rounds carried it, per ledger 5054d69). Both annotations point at
> this note's accepted form (2/2 at adc6cf3: W2-C3 proved-to-first-twist
> 38/44 / MEASURED above, riding W2-OPEN-2/OPEN-2a — the accepted BOX).
> Nothing else in the r1 record remains orchestrator-owed. Direction:
> NEUTRAL (bookkeeping discharge; no grade or statement moves).”

**CONDITIONALITY:** **The note's only OUTBOUND edges, and neither was made by the note.** `SUPERSESSION KIND: inventory completion` — the owed list is closed (“Nothing else in the r1 record remains orchestrator-owed”). Two process facts worth preserving:
(i) **One half had to WAIT for the target's own acceptance**: “the half that had to wait for WELDMASTER's own acceptance (66b3498) to become an accepted-text annex item (while WM was in-arc its own rounds carried it)”. **An annotation on an accepted text is a different object from a repair inside an in-arc note, and the corpus tracks the difference.**
(ii) **Both annotations point at the note's ACCEPTED form**, with the 38/44 census quoted — **which `.56` later re-displays as 37 + 1 + 6.** So the two executed annotations now point at a superseded census. **Neither GRTJB nor WELDMASTER has been re-annotated** — verified: no later append in this note mentions either. Recorded as source defect 2 and OPEN-CALL 3.

**DERIVATION:** Bookkeeping record.

**RESOLUTION TRACE:** statement 1359–1374 · the owed folds `.41` · the census re-display 1527 (`.56`).

PINS: `5054d69` ✓ · `66b3498` ✓ · `adc6cf3` ✓ — 3/3 commits.
ARTIFACT: `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md` ✓ · `lean/notes/openmath/WELDMASTER_2026-08-08.md` ✓.

**TEETH:** NONE (bookkeeping). Direction explicitly “NEUTRAL … no grade or statement moves”.

---

### EFF.GRTW2.49  [changes-record]  — ANNEX 2: (OPEN-2a) NARROWED (the OPEN2ATTACK unit)

**CANONICAL STATEMENT:** verbatim, lines 1376–1403.

**FORM:** blockquoted dated annex, four numbered items.

> “> **[ANNEX 2026-08-08, orchestrator, OPEN-2a NARROWED — the OPEN2ATTACK
> > unit (`OPEN2ATTACK_2026-08-08.md`, sealed battery
> > `open2attack_checks.py` + disclosed extension `open2attack_ext.py`;
> > seal commit bd82766, verdict commit = this fold).]** The (OPEN-2a)
> > box's forward direction at m ≥ 2 is reduced, at attempt grade with no
> > new literature consumption, to a single displayed lemma: (i)
> > strict-form identification ⟺ infeasibility of the defeat system
> > δ_j = ρ_j ∧ ρ ≢ 1 (slot calculus, OPEN2ATTACK §1), with recorded
> > ξ = 1 ⟹ strict under every selection rule; (ii) the premise's own
> > byte-share clause makes the interior twist a K₁-automorphism σ′ and
> > the measured gauge law is the coboundary δ_j = ρ_j·σ′(ρ_j)^{∓1}
> > (Σ-LAW: 468 sealed + 24 extension m ≥ 2 junction rows, 0 violations,
> > every gap row included), under which the defeat is infeasible and the
> > m ≥ 2 forward direction FOLLOWS (THEOREM OPEN-2a-Σ, conditional); the
> > surviving open step is the Σ-LAW at proof grade — the level-m
> > generalization of LEMMA W2-L3, strictly smaller than (OPEN-2a).
> > (iii) Instance geography: the identification is instance-exact at 468
> > fresh m ≥ 2 junction-levels (engineered invisible-twist chambers; the
> > I4A/I4B r = 5 geography swept 50 rows), so the two instance-warranted
> > census entries now ride a 470-point instance base plus a displayed
> > mechanism. (iv) The converse's honest boundary extends to m ≥ 2 as
> > predicted: 16 constructed spurious-selection witnesses (F₉ y⁴+c
> > recorded ord-4; F₆₄ y³+c recorded ord-3; byte-equal strict (C-coll)
> > junctions), PE4 o-e's third-read instantiation measured, the
> > d-torsion selection-geography law green at every m (604 byte-equal
> > rows). Direction: box NARROWED (forward direction now one
> > evaluator-ledger lemma wide), NOT closed; W2-OPEN-2's chain-level
> > claim above r₀ and the converse's UNPROVED status are unchanged.**”

**CONDITIONALITY:** **A NARROWING, explicitly not a closure** — the Direction line says so: “box NARROWED …, **NOT closed**; W2-OPEN-2's chain-level claim above r₀ and the converse's UNPROVED status are unchanged.” `SUPERSESSION KIND: license` (a reduction to a smaller lemma). **CHAIN: (OPEN-2a) OPEN at m ≥ 2 → NARROWED to the Σ-LAW → PROVED (`.50`) → riding an accepted supplier (`.53`). TERMINAL: `.53`.**
**Three items are load-bearing beyond the narrowing:**
(i) **The surviving open step is identified as “the level-m generalization of LEMMA W2-L3, strictly smaller than (OPEN-2a)”** — so `.14`'s proved level-1 dictionary is exactly the shape whose generalization was needed.
(ii) **Item (iv) confirms `.32`'s prediction at m ≥ 2**: the converse's boundary “extends to m ≥ 2 **as predicted**”, with 16 constructed witnesses and PE4's o-e third-read instantiation **measured** ✓ — **the note predicted the genre would generalize and it does.**
(iii) **The two instance-warranted census entries gain a 470-point base** (468 fresh + the I4A/I4B geography's 50 rows sweep — see the audit).

*Arithmetic audit (rule 22).* “468 sealed + 24 extension m ≥ 2 junction rows” ✓; “instance-exact at 468 fresh m ≥ 2 junction-levels … so the two instance-warranted census entries now ride a **470-point instance base**” — `468 + 2 = 470` ✓ (the two roster entries themselves) ✓ **consistent.** The “I4A/I4B r = 5 geography swept 50 rows” is a sub-count of the 468, not an addend ✓ (else the total would be 518). **The arithmetic closes on the `468 + 2` reading.** Item (iv)'s counts: 16 witnesses, 604 byte-equal rows — no cross-check available.

**DERIVATION:** A reduction, with its machine leg.

**RESOLUTION TRACE:** statement 1376–1403 · the proved successor 1405–1434 (`.50`) · `.33`, `.32`, `.14`.

PIN: `bd82766` ✓ commit.
ARTIFACT: `lean/notes/openmath/OPEN2ATTACK_2026-08-08.md` ✓ present.

**TEETH:** **Σ-LAW: 468 sealed + 24 extension rows, 0 violations, every gap row included**; plus 16 constructed spurious-selection witnesses and a 604-row d-torsion law. **Disposition: executable regression on a new sealed battery + planted constructions; the box narrows on a displayed mechanism, not on the instance count.**

---

### EFF.GRTW2.50  [lemma]  — ANNEX 3: Σ-LAW PROVED (the SIGMALAW unit), with two corrections to the boxed display

**CANONICAL STATEMENT:** verbatim, lines 1405–1434.

**FORM:** blockquoted dated annex with an embedded proof sketch and a consequence.

> “> **[ANNEX 2026-08-08, orchestrator, Σ-LAW PROVED — the SIGMALAW unit
> > (`SIGMALAW_PROOF_2026-08-08.md`, sealed battery `sigmalaw_checks.py`;
> > seal commit 8064ae3, verdict commit 59c1ff2 = the §6R fold).]** The (Σ-LAW box) displayed at
> > OPEN2ATTACK §6 is CLOSED at attempt grade, with two corrections to the
> > boxed display: the covariance map is the **ξ-formula composite** (the
> > §3.4 characters ξ_q = χ_{q−1}^{γ_q}z_{q−1}^{−e_{q−1}A_{q−1}}, χ-chain
> > included — NOT the bare interior twist z_{q−1}^{A_{q−1}e_{q−1}}), and
> > the sign is fixed: δ_j = ρ_j/Σ_m(ρ_j). Proof: the per-coordinate
> > ledger identity Prnt_j(A) = u_j·Σ_m(R_m v(A)) with EXPLICIT
> > slot-constant u_j = z_m^{−k_jA_m}ε_m(β_j)U_m(β_j), by double recursion
> > (the gap terms cancel per node inside each builder's own evaluator —
> > the attained-start τ-normalization is W2-L3's mechanism at every
> > level, so gap rows carry NO correction term; and the gauge-ratio
> > recursion Λ_q(w) = χ_q^{−w} REDERIVES the §3.4 χ/ξ recursion from the
> > evaluator side). Machine: 1,211 walked junction rows (539 towers:
> > the full OPEN2ATTACK battery reproduced + 150 constructed separator
> > towers), SL-VDM 2,854 / SL-DELTA 1,427 / SL-GAP 688 samples (340 gap
> > slots), 0 violations, exit 0, 3 teeth caught 2/2 each; the sign/map
> > corrections are witnessed by 96 constructed non-involution separator
> > rows at m = 2 and 27 at m = 3 where the ξ-law holds and BOTH boxed
> > variants fail — the sealed battery's involution degeneracy is thereby
> > explained (its entire δ ≠ 1 record sits where the maps coincide,
> > 218/218 slot-samples). Consequence:
> > THEOREM OPEN-2a-Σ fires unconditionally on its Σ-leg — at every
> > shared-below junction at every m, strict ⟹ byte-equal and recorded
> > ξ = 1 ⟹ byte-equal under every selection rule, at attempt grade given
> > OA-L1–L4 — so **(OPEN-2a)'s forward direction at m ≥ 2 is PROVED at
> > attempt grade** and the simultaneous-defeat system is infeasible on
> > the whole shared-below perimeter. The converse's UNPROVED status and
> > W2-OPEN-2's above-r₀ chain claims are unchanged.**”

**CONDITIONALITY:** **(OPEN-2a)'s forward direction at m ≥ 2 is PROVED at attempt grade.** `SUPERSESSION KIND: license` on `.33`'s (OPEN-2a) and, transitively, on `.05`'s “2 instance-warranted” census entries. **CHAIN member 3 of 4** (see `.49`).
**Two corrections to the boxed display are folded in, and both matter for the shard-1-homed range (`.01`–`.43`):**
(i) **The covariance map is the ξ-formula composite, χ-chain included — NOT the bare interior twist.** **That is a correction to how `.19`'s characters are used downstream**, and it confirms the χ-chain is load-bearing and easy to drop (`.19`'s CONDITIONALITY).
(ii) **The sign is fixed**: `δ_j = ρ_j/Σ_m(ρ_j)`.
**The proof REDERIVES `.20`'s χ/ξ recursion from the evaluator side** — “the gauge-ratio recursion Λ_q(w) = χ_q^{−w} **REDERIVES the §3.4 χ/ξ recursion from the evaluator side**” ✓ **an independent derivation of the same chain.**
**Its machine figures are CORRECTED TWICE below** (`.51`, `.52`) — see the CHAIN there.
**The Direction is fenced**: “The converse's UNPROVED status and W2-OPEN-2's above-r₀ chain claims are unchanged.” **That fence is exactly what ANNEX #3 later violates and E5 restores** (`.53`, `.55`).

*Arithmetic audit (rule 22).* The machine figures as displayed: SL-VDM 2,854 / SL-DELTA 1,427 / SL-GAP 688 (340 gap slots). Note `2,854 = 2 × 1,427` ✓ and `688 ≈ 2 × 340 = 680` — **off by 8**. **`.51` corrects all four figures and `.52` corrects `.51`'s transposition**, landing on SL-VDM 2,828 / SL-DELTA 1,414 / SL-PHIR 1,414 / SL-GAP 680, with `2,828 = 2 × 1,414` ✓ and `680 = 2 × 340` ✓ **exactly**. **So the corrected figures satisfy the two doubling relations that the displayed ones do not** — an independent check that the corrections are the right ones. `539 towers` and `1,211 walked junction rows` ✓ no cross-check. The involution census `218/218` ✓ is corrected to “218 EXACTLY (3 garbled-print tooth artifacts excluded)” at `.51` ✓.

**DERIVATION:** Quoted inline: a per-coordinate ledger identity proved by double recursion, with the gap terms cancelling per node.

**RESOLUTION TRACE:** statement 1405–1434 · the count corrections 1436 (`.51`), 1438 (`.52`) · the supplier upgrade 1440 (`.53`) · `.33`, `.19`, `.20`, `.14`.

PINS: `8064ae3` ✓ · `59c1ff2` ✓ — 2/2 commits.
ARTIFACT: `lean/notes/openmath/SIGMALAW_PROOF_2026-08-08.md` ✓ present.

**TEETH:** **1,211 walked junction rows over 539 towers; 3 teeth caught 2/2 each; and 96 + 27 constructed non-involution separator rows where BOTH boxed variants fail and the ξ-law holds.** **Disposition: executable regression + planted separators; and the separators are what DIAGNOSED the sealed battery's own involution degeneracy** — “its entire δ ≠ 1 record sits where the maps coincide, 218/218 slot-samples”. **That is an instrument-blindness finding produced by constructing the cases the instrument could not distinguish.**

---

### EFF.GRTW2.51  [changes-record]  — ANNEX #2: the count correction to the Σ-LAW annex

**CANONICAL STATEMENT:** verbatim, line 1436.

**FORM:** blockquoted dated annex, one paragraph.

> “> **[ANNEX 2026-08-08 #2, orchestrator] Count correction to the Σ-LAW annex above (flagged by SIGMALAW r1, 6b24942, per its PE1 Finding 2): the quoted machine figures included tooth-run leakage (+26/+13/+13/+8/+3); the genuine battery figures are SL-VDM 2,828 / SL-DELTA 1,414 / SL-GAP 1,414 / SL-PHIR 680 (340 gap slots stands), and the involution-record census is 218 EXACTLY (3 garbled-print tooth artifacts excluded). All verdicts unaffected; the Σ-LAW's zero-violation record stands on the corrected denominators. Since the annex above was applied, the Σ-LAW has been PROVED in sharper form (THEOREM SL-1, SIGMALAW_PROOF_2026-08-08.md, arc 0/2 post-r1) — the "sign undetermined" clause superseded per that note's [r1] instrument record.**”

**CONDITIONALITY:** **A count correction that is ITSELF wrong, and the next unit fixes it.** `SUPERSESSION KIND: counter re-reading`. **CHAIN: `.50`'s displayed figures → this correction (SL-GAP 1,414 / SL-PHIR 680) → `.52`'s erratum (SL-PHIR 1,414 / SL-GAP 680). TERMINAL: `.52`.**
**The cause is named**: “tooth-run leakage (+26/+13/+13/+8/+3)” — the quoted figures had counted tooth runs as battery samples. **And the finding came from the SUPPLIER's own hostile pass** (SIGMALAW r1 per its PE1 Finding 2), not from GRTW2.
**A second, independent content update rides along**: the Σ-LAW “has been PROVED in sharper form (THEOREM SL-1 …)” and “the "sign undetermined" clause superseded”. `SUPERSESSION KIND: license`.

*Arithmetic audit (rule 22).* The leakage `+26/+13/+13/+8/+3` against `.50`'s figures: `2,854 − 26 = 2,828` ✓; `1,427 − 13 = 1,414` ✓; `688 − 8 = 680` ✓. **Three of the five leakage terms map exactly onto three of the four figures** ✓, and the remaining `+13` and `+3` map to SL-PHIR and the involution census (`221 − 3 = 218` ✓). **So the leakage decomposition is arithmetically consistent with the corrected figures** ✓ — but **this annex assigns `1,414` to SL-GAP and `680` to SL-PHIR**, which contradicts “340 gap slots stands” (`2 × 340 = 680` should be SL-GAP) ✓ **exactly the transposition `.52` catches.** **This compiler's independent check reproduces the erratum's diagnosis before reading it.**

**DERIVATION:** A recount from the supplier's own pass.

**RESOLUTION TRACE:** statement 1436 · the target 1405–1434 (`.50`) · the erratum 1438 (`.52`).

PIN: `6b24942` ✓ commit.

**TEETH:** **`decorrelated-model audit` (rule 27)** — a hostile pass on the *supplier* note found tooth-run leakage in figures quoted in *this* note's annex.

---

### EFF.GRTW2.52  [changes-record]  — the ERRATUM to ANNEX #2 (own transposition)

**CANONICAL STATEMENT:** verbatim, line 1438.

**FORM:** blockquoted dated erratum, one paragraph.

> “> **[ERRATUM 2026-08-08 to ANNEX #2 above, orchestrator — own transposition, caught by SIGMALAW PE2 (6e57e03)]: the corrected figures were themselves transposed; the genuine battery figures are SL-VDM 2,828 / SL-DELTA 1,414 / SL-PHIR 1,414 / SL-GAP 680 (= 2×340 gap slots, consistent with the "340 gap slots stands" clause). INVREC = 218 exactly stands. Verified against the committed JSON by the PE2 recount (Σ|supp| = 1,414 = 1,060 OA + 354 SEP).**”

**CONDITIONALITY:** **TERMINAL member of the Σ-LAW figure CHAIN.** `SUPERSESSION KIND: counter re-reading`. **Three things make this the sweep's cleanest self-correction:**
(i) **The error is labelled “own transposition”** — the orchestrator's, not the supplier's.
(ii) **It was caught by the supplier's SECOND hostile pass** (SIGMALAW PE2), i.e. two consecutive passes on a different note found two different defects in figures quoted here.
(iii) **The fix is verified against the committed JSON with a decomposition**: `Σ|supp| = 1,414 = 1,060 OA + 354 SEP`.

*Arithmetic audit (rule 22), fully recomputed.* `1,060 + 354 = 1,414` ✓ **exact** ✓. `2 × 340 = 680` ✓ **so SL-GAP = 680 is consistent with “340 gap slots”** ✓ and `.51`'s assignment was indeed transposed ✓. `SL-VDM 2,828 = 2 × 1,414` ✓ **the doubling relation holds** ✓. **All three relations that failed in `.07` and half-failed in `.08` now hold exactly** ✓ — **the erratum's figures are the only assignment consistent with every displayed relation.** This compiler verified this independently before reading the erratum's reasoning.

**DERIVATION:** A recount against the committed JSON.

**RESOLUTION TRACE:** statement 1438 · the corrected target 1436 (`.51`) · the original 1405–1434 (`.50`).

PIN: `6e57e03` ✓ commit.

**TEETH:** **`arithmetic recount` (rule 27)**, verified against a committed artifact with a decomposition. **Disposition: the strongest form of count correction — a recount with a partition.**

---

### EFF.GRTW2.53  [changes-record]  — ANNEX #3: the supplier upgrade, with its OVER-CLAIMED final sentence

**CANONICAL STATEMENT:** verbatim, line 1440.

**FORM:** blockquoted dated annex, one paragraph.

> “> **[ANNEX 2026-08-08 #3, orchestrator] Supplier upgrade: the Σ-LAW note (SIGMALAW_PROOF_2026-08-08.md) is ACCEPTED at 2/2 (PE2+PE3 clean; acceptance record at its tail). The (OPEN-2a) forward direction at every m ≥ 2 now rides an ACCEPTED supplier via THEOREM OPEN-2a-Σ. W2-OPEN-2's residual open surface: the converse (recorded ξ ≠ 1 ⟹ byte-RED) only, as fenced since PE3's counter-instance.**”

**CONDITIONALITY:** **The first two sentences are correct and are the TERMINAL of the (OPEN-2a) chain. The third is FALSE and is WITHDRAWN by a CRITICAL.**
**The upgrade (sentences 1–2):** the Σ-LAW note is ACCEPTED 2/2, so (OPEN-2a)'s forward direction at every `m ≥ 2` rides an accepted supplier ✓. `SUPERSESSION KIND: license`. **CHAIN member 4 of 4** (`.49`).
**The over-claim (sentence 3):** “W2-OPEN-2's residual open surface: the converse … **only**”. **This conflates (OPEN-2a) with W2-OPEN-2(a)–(b).** The C5 read returned a **CRITICAL** on exactly this (1447–1448), and E5 finding 1 WITHDRAWS it (`.55`). `SUPERSESSION KIND: replacement` (a withdrawal). **TERMINAL: the withdrawal.**
**Note that `.50`'s own Direction line had already fenced against this**: “W2-OPEN-2's above-r₀ chain claims are unchanged.” **So the over-claim contradicted the annex two lines above it.** Recorded as shard 2's own source defect 3 (carried forward in the merged §8).

**DERIVATION:** Status record.

**RESOLUTION TRACE:** statement 1440 · the fence it violates 1433–1434 (`.50`) · the withdrawal 1465–1476 (`.55`) · the C5 CRITICAL 1447–1448 (`.54`).

ARTIFACT: `lean/notes/openmath/SIGMALAW_PROOF_2026-08-08.md` ✓ present.

**TEETH:** NONE (status record). Its defect was found by a `decorrelated-model audit`.

---

### EFF.GRTW2.54  [changes-record]  — the C5/E5 adjudication header

**CANONICAL STATEMENT:** verbatim, lines 1444–1457.

**FORM:** `###` heading + a framing paragraph.

> “### Dated adjudication + corrections (2026-08-12 — sol certification C5/E5: the as-built challenge adjudicated at HEAD)
>
> The sol-5.6 as-built read of this note (gpt-5.6-sol high,
> runs/cert/C5_grtw2_output.log, 2026-08-12) returned CHALLENGE with a
> CRITICAL (ANNEX #3's unsupported closure of W2-OPEN-2). The E5
> certification run (gpt-5.6-sol high,
> runs/cert2/E5_grtw2_output.log) adjudicated: findings 1–4 REAL with
> the repairs below (the OPEN-2 status correction withdrawing the false
> closure; THEOREM W2-C1-CORR scoping the scalar orbit to its proved
> perimeter with the honest 37/44 + 1/44 + 6/44 roster census; the
> key-carry index fix Φ_{q−1}; the W2-C3 ledger-equivalence
> re-display), finding 5 ARTIFACT (PE5/PE6 certify the frozen body,
> not later annexes). Everything above this heading is byte-untouched
> by this append. The E5 adjudication, transcribed unaltered:”

**CONDITIONALITY:** **The harshest external verdict in this sweep on an ACCEPTED note: a CRITICAL plus three REAL findings, landing 2/2 and after five annexes.** Three properties distinguish it:
(i) **The CRITICAL is against a LEDGER ENTRY, not the proof** — ANNEX #3's closure sentence. **The frozen body survives it** (`.59`).
(ii) **Two of the four REAL findings change a theorem's scope** (W2-C1, W2-C3(iii)) — unlike GENHN's A2 (two REAL-but-OBSTRUCTED) and HE3's A5 (five REAL, none weakening a display), **E5 does weaken two displays**, under the same statement fence the other notes invoked. Recorded as a corpus-level difference.
(iii) **Finding 5 is an ARTIFACT — a finding the certifier REJECTS**, with the note's own text quoted as the rebuttal (`.59`).
**Status:** “Ledger: row 23 → **all four repairs folded, awaiting sol discharge (cert3)**” (1631–1632).

*Arithmetic audit (rule 22).* “findings 1–4 REAL … finding 5 ARTIFACT” = 5 findings ✓ and five numbered sections below (`## 1.` … `## 5.`) ✓ **one block per finding, no orphans** ✓. The four repairs enumerated in the header map one-to-one onto findings 1–4 ✓. The census `37/44 + 1/44 + 6/44` sums to 44 ✓ (audited at `.05`).

**DERIVATION:** Adjudication framing.

**RESOLUTION TRACE:** statement 1444–1457 · the five blocks 1459–1612 · the verification 1614–1632 (`.60`).

ARTIFACT: `runs/cert/C5_grtw2_output.log` ✓ · `runs/cert2/E5_grtw2_output.log` ✓ — 2/2 present.

**TEETH:** **`decorrelated-model audit` (rule 27)** — a fresh-context gpt-5.6-sol as-built read, re-adjudicated by a second sol run at HEAD. **Six hostile passes (PE1–PE6) had not found these.**

---

### EFF.GRTW2.55  [changes-record]  — E5 finding 1: ANNEX #3 falsely closes W2-OPEN-2 (the CRITICAL)

**CANONICAL STATEMENT:** verbatim, lines 1459–1476.

**FORM:** `##`-numbered finding with a diagnosis and a blockquoted verbatim-ready repair containing LaTeX.

> “## 1. REAL — Annex #3 falsely closes W2-OPEN-2
>
> The two quoted statements are contradictory. The Σ-LAW annex proves OPEN-2a’s shared-below forward implication only. Nothing in it proves W2-OPEN-2(a)–(b) above \(r_0\).
>
> Verbatim-ready repair:
>
> > **[ANNEX 2026-08-12, certifier correction to ANNEX 2026-08-08 #3 — W2-OPEN-2 STATUS.]** The final sentence of ANNEX #3,
> > “W2-OPEN-2's residual open surface: the converse (recorded ξ ≠ 1 ⟹ byte-RED) only,” is **WITHDRAWN**. THEOREM OPEN-2a-Σ, using the accepted Σ-LAW supplier, proves only the shared-below forward implication
> > \[
> > \text{recorded }\xi=1\Longrightarrow\text{byte-equal}
> > \]
> > at every \(m\). It does not prove W2-OPEN-2(a)–(b) at any junction above the first recorded twist \(r_0\).
> >
> > **Derivation.** OPEN-2a concerns a junction whose lower keys are byte-shared and excludes a hidden byte divergence before transport fires. W2-OPEN-2(a)–(b), by contrast, concerns a later junction whose lower transported keys may already be byte-different and asks for preservation of the valuation/polygon and strict residual criterion through binomial key-change carries. The Σ-LAW supplies an evaluator identity on the shared-below perimeter; it contains no estimate for those key-change cross-terms. Therefore no implication from the Σ-LAW to W2-OPEN-2(a)–(b) has been displayed.
> >
> > **Correct current status:** OPEN-2a’s forward direction is PROVED at attempt grade through the accepted Σ-LAW supplier. W2-OPEN-2(a)–(b), the chain-level transfer above \(r_0\), remains **OPEN and instance-confirmed on the six live roster junction-levels**. The converse “recorded \(\xi\ne1\Rightarrow\) byte-RED” remains separately UNPROVED as a recorded-pair selection/premise issue; it is not a substitute for, nor the conclusion of, the above-\(r_0\) chain lemma.
> >
> > **Consumer sweep.** The Acceptance Record’s statement that W2-OPEN-2 is accepted AS A BOX survives. W2-C3 remains measured/open above the first twist. W2-OPEN-1 remains open. Neither the Σ-LAW theorem nor W2-ID1 is weakened.”

**CONDITIONALITY:** **THE CORPUS'S CANONICAL STATUS STATEMENT for W2-OPEN-2, and this shard adopts it as TERMINAL.** Three distinct statuses are separated, and they must never be merged:

| Object | Status at HEAD |
|---|---|
| **(OPEN-2a) forward direction** | **PROVED at attempt grade** through the accepted Σ-LAW supplier, at every `m` |
| **W2-OPEN-2(a)–(b)** (the chain-level transfer above `r₀`) | **OPEN and instance-confirmed on the six live roster junction-levels** |
| **The converse** (recorded ξ ≠ 1 ⟹ byte-RED) | **separately UNPROVED**, a recorded-pair selection/premise issue |

`SUPERSESSION KIND: replacement` (a withdrawal). **CHAIN: ANNEX #3's closure sentence → this withdrawal. TERMINAL: the three-way status above, awaiting sol discharge (cert3).**
**The derivation is the load-bearing part and it is precise**: OPEN-2a is about a junction with byte-shared lower keys; W2-OPEN-2(a)–(b) is about a later junction whose lower transported keys **may already be byte-different**, and asks for preservation “through binomial key-change carries”. **“The Σ-LAW supplies an evaluator identity on the shared-below perimeter; it contains no estimate for those key-change cross-terms.”** ✓ **and `.33`'s Equivalent sufficient form is exactly about those cross-terms** ✓ — the two agree.
**The consumer sweep protects four things**: the acceptance's box status, W2-C3's measured/open scope, W2-OPEN-1's open status, and both the Σ-LAW theorem and W2-ID1.

**DERIVATION:** Quoted inline.

*Arithmetic audit (rule 22).* “the six live roster junction-levels” ✓ = the 6 above-twist junction-levels enumerated at `.30` (T3A/T3C/T3D/T3E r = 4, I4C r = 4, 5) ✓ **exact match** ✓ and the same 6 as the SKIP junctions (`.15`) ✓ **five independent occurrences of the same 6 across both shards, all consistent** ✓.

**RESOLUTION TRACE:** statement 1459–1476 · the withdrawn sentence 1440 (`.53`) · the fence it violated 1433–1434 (`.50`) · `.33`.

**TEETH:** NONE for the finding itself (an audit of a ledger claim). **The three-way status's instance base:** W2-OPEN-2(a)–(b) at 44/44 (`.33`); (OPEN-2a) at 470 points plus a theorem (`.49`, `.50`); the converse at PE4's exhaustive characterization (`.44`).

---

### EFF.GRTW2.56  [theorem]  — E5 finding 2: THEOREM W2-C1-CORR (admissibility at the proved scalar scope)

**CANONICAL STATEMENT:** verbatim, lines 1478–1531.

**FORM:** `##`-numbered finding + a blockquoted verbatim-ready repair containing a three-item LaTeX theorem, a derivation, a consequent statement correction, and a four-bullet consumer sweep.

> “## 2. REAL — W2-C1 lacks scalar-orbit geometricity outside (C-coll)
>
> Section 3.3(c) computes the slot ratios but does not prove they form a geometric progression. Thus the general scalar orbit asserted in W2-C1 does not follow from HR-REC.
>
> Verbatim-ready repair:
>
> > **[ANNEX 2026-08-12, certifier correction — W2-C1 SCALAR-ORBIT SCOPE.]** The universal reading of THEOREM W2-C1 outside the scalar-collapse perimeter is **SUPERSEDED** by the following proved display.
> >
> > **THEOREM W2-C1-CORR (admissibility at the proved scalar scope).** Let
> > \[
> > B_m(y):=R_{r-1}(\Phi_{m+1}^{har})(y)
> > \]
> > at a shared-key junction, with W2-C1a’s chamber qualifier understood.
> >
> > 1. If \(m=1\), then unconditionally
> >    \[
> >    B_m(y)=w_{m+1}\psi_m(\xi_{m+1}y)
> >    \]
> >    with the pair of §3.4.
> > 2. If \(m\ge2\) and (C-coll) holds, the same display follows from W2-C2(b) and §3.4.
> > 3. At a general shared-key junction outside (C-coll), HR-REC computes \(B_m\) exactly, but no scalar orbit is asserted without the following finite geometricity condition. Writing
> >    \[
> >    a_j:=\frac{[y^j]B_m}{\psi_{m,j}}
> >    \qquad(j\in\operatorname{supp}\psi_m),
> >    \]
> >    a scalar orbit exists exactly when there are units \(w,\xi\in K_m^\times\) such that
> >    \[
> >    a_j=w\xi^j\qquad
> >    \text{for every }j\in\operatorname{supp}\psi_m.
> >    \]
> >    When this condition holds, \(B_m(y)=w\psi_m(\xi y)\), and the admissibility conclusion of the former W2-C1 follows. Otherwise HR-REC alone gives no ξ-conjugate representative theorem.
> >
> > **Derivation.** W2-C2(a) proves item 1. W2-C2(b) proves item 2 because (C-coll) makes the ratios geometric. In general, §4.2 reads the residual coefficient as
> > \[
> > [y^j]B_m=\frac{c}{\rho_j}\psi_{m,j}.
> > \]
> > Hence \(B_m=w\psi_m(\xi y)\) is equivalent coefficient-by-coefficient to
> > \(c/\rho_j=w\xi^j\) on the support. For example, if
> > \(0,1,2\in\operatorname{supp}\psi_m\), this necessarily gives
> > \[
> > \rho_1^2=\rho_0\rho_2.
> > \]
> > HR-REC computes the three \(\rho_j\) but supplies no identity forcing this equation when mod-wrap does not collapse. The roster’s I4B \(r=5\) calculation establishes its own scalar orbit only as an individually checked boundary instance; it does not prove the universal relation.
> >
> > **Consequent statement correction.** CLAUSE 1 and the §6.2 W2-C1 row are proved universally only at \(m=1\) and on (C-coll), and conditionally at other shared-key junctions when the displayed geometricity test is established. Outside that scope the proved conclusion consists of W2-C1a’s polygon statement plus the exact HR-REC residual.
> >
> > **Consumer sweep.**
> >
> > * W2-C2(a), W2-ID1, HR-REC, and the §3.4 scalar display on (C-coll) survive unchanged.
> > * The transported-chain proof survives theoremically at every first-twist-or-below junction covered by \(m=1\) or (C-coll). After the accepted OPEN-2a/Σ-LAW upgrade, the roster census is honestly re-displayed as **37/44 theorem-derived, 1/44 individually scalar-orbit-confirmed (I4B \(r=5\)), and 6/44 above-twist junctions riding W2-OPEN-2**.
> > * At a general non-collapse first twist, §5.1’s ξ-transport is conditional on the geometricity test. Above the first twist, scalar-orbit existence remains part of W2-OPEN-2(b), hence OPEN.
> > * Section 4.3’s \(\ell\)-orbit analysis applies only after a scalar pair exists. W2-OPEN-1 remains open and unchanged.
>
> No new lemma derivable from the displayed material forces geometricity, so this re-display is the honest end-to-end theorem scope.”

**CONDITIONALITY:** **A theorem in the accepted enumeration is SUPERSEDED outside (C-coll), and the census is re-displayed.** `SUPERSESSION KIND: replacement` at statement scope. `TARGETS: .25` (THEOREM W2-C1), `.04` (clause 1), `.38` (the §6.2 W2-C1 row), `.05` (the census), `.27` (§5.1's transport), `.26` (§4.3's scope).
**CHAIN: W2-C1 as displayed → E5 finding 2 → W2-C1-CORR. TERMINAL: W2-C1-CORR, awaiting sol discharge (cert3).**
**Three properties:**
(i) **The defect is a missing IMPLICATION, not a wrong statement**: HR-REC computes the `ρ_j`, and nothing forces them geometric. **The former theorem asserted the conclusion without the step.**
(ii) **The repair is CONDITIONAL rather than restrictive**: item 3 gives a *test* (`a_j = wξ^j` on the support), and when it holds the old conclusion follows. **So the theorem is not narrowed to (C-coll); it is narrowed to (C-coll) ∪ {junctions passing the test}.**
(iii) **The closing sentence is a claim about the corpus**: “**No new lemma derivable from the displayed material forces geometricity**, so this re-display is the honest end-to-end theorem scope.” — i.e. the certifier checked that a repair-by-lemma was unavailable, the same move GENHN's A2 obstruction records made (`spec/EFF-GENHN-s2of2.md` `.32`).
**The census re-display is the TERMINAL of `.05`'s five-member chain** ✓.

**DERIVATION:** Quoted inline.

*Arithmetic audit (rule 22), the criterion and its consequence recomputed — and this compiler reached the same `ρ₁² = ρ₀ρ₂` at `.25` before reading the append.* `B_m = wψ_m(ξy)` ⟺ `[y^j]B_m = wψ_{m,j}ξ^j` ⟺ `a_j = wξ^j` ✓. At `j = 0,1,2 ∈ supp`: `a_1² = (wξ)² = w²ξ² = a_0a_2` ✓ ⟹ `(c/ρ_1)² = (c/ρ_0)(c/ρ_2)` ⟹ `ρ_1² = ρ_0ρ_2` ✓ **exact** ✓. Census: `37 + 1 + 6 = 44` ✓, and the reconciliation with the r2 census (`36 + 2 + 6`) is `36 + 1 = 37` (I4A r = 5 upgraded by the Σ-LAW) with I4B r = 5 remaining separate ✓ **audited at `.05`** ✓.

**RESOLUTION TRACE:** statement 1478–1531 · `.25`, `.18`, `.05`, `.38`, `.27`, `.26`, `.23` · verification 1619–1622 (`.60`).

**TEETH:** **PROOF-ONLY for the geometricity test** — no family tests whether a scalar orbit *must* exist; CK-XI tests whether the *displayed pair satisfies* the equations, which is the weaker claim `.21` makes. **The note's own coverage-hole sentence is W2-BOX-1** (`.23`): “the exact law is (HR-REC), the scalar form is proved only on (C-coll) … exactly 1 boundary junction.” **Disposition: `decorrelated-model audit`; the instrument was measuring the right thing and the theorem over-read it.**

---

### EFF.GRTW2.57  [changes-record]  — E5 finding 3: the key-carry index fix

**CANONICAL STATEMENT:** verbatim, lines 1533–1560.

**FORM:** `##`-numbered finding + a blockquoted repair with boxed LaTeX, a derivation, and a consumer sweep.

> “## 3. REAL — the sufficient-form key comparison is misindexed
>
> The prior P3 correction fixed the premise but missed this later occurrence.
>
> Verbatim-ready repair:
>
> > **[ANNEX 2026-08-12, certifier correction — W2-OPEN-2 KEY-CARRY INDEX.]** In W2-OPEN-2’s “Equivalent sufficient form,” replace
> > \[
> > \Phi_q^{har}=\phi_q^{tw}+D_q,\qquad \deg D_q<\deg\phi_q
> > \]
> > by
> > \[
> > \boxed{\Phi_{q-1}^{har}=\phi_q^{tw}+D_q,\qquad
> >        \deg D_q<\deg\phi_q.}
> > \]
> > At the junction \(r=m+2\), take \(q=r-1\); thus the actual expansion is
> > \[
> > \Phi_m^{har}=\phi_{r-1}^{tw}+D_{r-1},
> > \qquad
> > (\Phi_m^{har})^{e_mk}
> >   =(\phi_{r-1}^{tw}+D_{r-1})^{e_mk}.
> > \]
> >
> > **Derivation.** The fixed P-index dictionary is
> > \(\phi_q^{GMN}=\Phi_{q-1}^{har}\). The two corrected summands therefore have the same monic degree, making \(\deg D_q<\deg\phi_q\) possible. With the former indexing, \(\Phi_q\) has degree
> > \(e_{q-1}g_{q-1}\deg\Phi_{q-1}\), so whenever \(e_{q-1}g_{q-1}>1\), the difference \(\Phi_q-\phi_q\) cannot have degree below \(\phi_q\).
> >
> > **Consumer sweep.** This repairs only the proposed discharge route. W2-OPEN-2 remains OPEN; its claims (a)–(b), HR-REC, the corrected premise pairing \(\phi_q^{tw}\leftrightarrow\Phi_{q-1}^{har}\), and every proved theorem outside the box are unchanged.”

**CONDITIONALITY:** **The SECOND misapplication of the same dictionary in the same box, four months after the first.** `SUPERSESSION KIND: replacement`. `TARGETS: .33` (the Equivalent sufficient form), and it confirms `.09`'s dictionary.
**The finding's opening sentence is the diagnosis**: “The prior P3 correction fixed the premise but **missed this later occurrence**.” — **a repair that did not sweep its own species**, exactly the failure mode r4 named at `.44` (“a species sweep must exhaust the species”). **So the note learned that lesson at r4 for one species and still had an unswept instance of another.** Recorded.
**The blast radius is nil**: “This repairs only the proposed discharge route. W2-OPEN-2 remains OPEN; its claims (a)–(b) … unchanged.”

**DERIVATION:** Quoted inline: a degree argument.

*Arithmetic audit (rule 22), recomputed — and this compiler reproduced the same argument at `.09` before reading the append.* With the wrong pairing, `deg Φ_q = e_{q−1}g_{q−1}·deg Φ_{q−1}` (`.08`'s lift display: top term `Φ_m^{e_mg_m}`) ✓ and `deg φ_q = deg Φ_{q−1}` ✓, so `deg Φ_q > deg φ_q` whenever `e_{q−1}g_{q−1} > 1` ✓ ⟹ `deg(Φ_q − φ_q) = deg Φ_q > deg φ_q` ✓ **so `deg D_q < deg φ_q` is impossible** ✓. With the corrected pairing both summands are monic of degree `deg Φ_{q−1}` ✓ ⟹ the difference can have lower degree ✓. **Exact.**

**RESOLUTION TRACE:** statement 1533–1560 · the first fix `.33` (`[r2, P3]`) · the dictionary `.09` · verification 1622–1626 (`.60`).

**TEETH:** NONE (an index fix in a discharge route). **Disposition: `decorrelated-model audit`** — a degree mismatch six hostile passes did not catch.

---

### EFF.GRTW2.58  [theorem]  — E5 finding 4: the W2-C3 equivalence scope (ledger-equivalence)

**CANONICAL STATEMENT:** verbatim, lines 1562–1594.

**FORM:** `##`-numbered finding + a blockquoted repair with a re-displayed clause, a LaTeX derivation, and a consumer sweep.

> “## 4. REAL — “same induced valuation data” is too strong
>
> The note itself proves that equality of augmented valuation functions is unavailable. The parenthetical must be narrowed to ledger data.
>
> Verbatim-ready repair:
>
> > **[ANNEX 2026-08-12, certifier correction — W2-C3 EQUIVALENCE SCOPE.]** In W2-C3, the phrase
> > “equivalence as type data (same residual classes, same induced valuation data)”
> > and the subsequent description “MacLane-equivalent level by level” are **SUPERSEDED** by:
> >
> > > **ledger-equivalent at the displayed scope:** the transported print key and the harness lift have the same transported residual modulus/class and the same numerical \((e,h,g)\), degree and one-sided polygon ledger asserted in W2-C3(i)–(iii). No equality of the augmented valuation functions induced by the two different key representatives is claimed.
> >
> > Accordingly W2-C3(iii) is re-displayed as:
> >
> > > **(iii)** the transported print key and \(\Phi^{har}\), evaluated in their respective displayed chambers, are strict representatives of the same transported residual ledger and have the same stated \((e,f)\) invariants. This is a residual/type-ledger assertion, not an assertion that the two key augmentations define the same valuation on \(O[x]\).
> >
> > **Derivation.** Let the common lower valuation be \(\mu\), let
> > \(\Phi=\phi+D\), and suppose—as W2-OPEN-2’s route (3) permits generically—
> > \[
> > \mu(D)=\mu(\phi)<\gamma.
> > \]
> > Then the \(\phi\)-augmentation satisfies
> > \[
> > \mu_{\phi,\gamma}(\Phi)
> >   =\min\{\gamma,\mu(D)\}
> >   =\mu(D)<\gamma,
> > \]
> > whereas the \(\Phi\)-augmentation assigns
> > \(\mu_{\Phi,\gamma}(\Phi)=\gamma\). Thus matching residual moduli,
> > polygon data and numerical invariants does not prove equality of the
> > induced valuation functions.
> >
> > **Consumer sweep.** W2-C3(i)’s polygon statement and W2-C3(ii)’s strict-residual statement do not use equality of valuation functions and survive at their separately corrected grades. W2-OPEN-2’s route-(3) obstruction now agrees with W2-C3. W2-OPEN-1 remains a comparison computed separately on the transported keys and remains OPEN. The W-1/W-5/J-A consumer statements claim no equality of augmented valuations and survive.”

**CONDITIONALITY:** **The note contained its own refutation and the finding says so.** `SUPERSESSION KIND: replacement`. `TARGETS: .29` (W2-C3(iii) and the “MacLane-equivalent” description), `.04` (clause 3's wording).
**CHAIN: W2-C3(iii) as displayed → E5 finding 4's ledger-equivalence re-display. TERMINAL: the re-display, awaiting sol discharge (cert3).**
**The key observation**: “**The note itself proves that equality of augmented valuation functions is unavailable**” — at `.34`'s route (3): “the recorded data warrant only ≥ key weight — with equality generic … strictly BELOW γ, so the two chains' inductive valuations may genuinely differ as functions on O[x]”. **The repair makes route (3) and W2-C3 agree** — the consumer sweep says so: “W2-OPEN-2's route-(3) obstruction now agrees with W2-C3.”
**Blast radius is bounded**: (i) and (ii) survive; W2-OPEN-1 unchanged; “The W-1/W-5/J-A consumer statements claim no equality of augmented valuations and survive” ✓ — **so the W-1 perimeter (`.39`) is untouched by this finding.**

**DERIVATION:** Quoted inline.

*Arithmetic audit (rule 22), recomputed — and this compiler reproduced it at `.29` before reading the append.* With `Φ = φ + D` and `μ(D) = μ(φ) < γ`: the `φ`-augmentation of a polynomial is `min` over its `φ`-development of (level value + `γ`·index); for `Φ = φ + D` the development is `1·φ + D`, giving `min{γ·1 + μ(1), μ(D)} = min{γ, μ(D)} = μ(D)` ✓ since `μ(D) < γ` ✓. The `Φ`-augmentation assigns `μ_{Φ,γ}(Φ) = γ` ✓ by definition ✓. **Different** ✓ **exact.**

**RESOLUTION TRACE:** statement 1562–1594 · the target `.29` · the note's own route (3) `.34` · verification 1626–1629 (`.60`).

**TEETH:** NONE (a wording scope correction). **Disposition: `decorrelated-model audit` — and the sharpest kind: the certifier used the note's own displayed argument against the note's own displayed claim.**

---

### EFF.GRTW2.59  [changes-record]  — E5 finding 5: ARTIFACT (the PE5/PE6 certification scope), a finding REJECTED

**CANONICAL STATEMENT:** verbatim, lines 1596–1612.

**FORM:** `##`-numbered finding with three quoted rebuttals from the note itself.

> “## 5. ARTIFACT — PE5/PE6 certification scope
>
> This finding correctly observes that PE5/PE6 predate the annexes, but it misreads what the note says those passes certify.
>
> The note explicitly separates the accepted frozen body from later ledger entries:
>
> > “## ANNEX (dated append; the frozen body is not edited)”
>
> The Acceptance Record also enumerates “WHAT IS ACCEPTED” and expressly includes:
>
> > “W2-OPEN-2/OPEN-2a as the note's fenced OPEN box — … accepted AS A BOX, not as a theorem.”
>
> Later supplier status is independently recorded:
>
> > “Supplier upgrade: the Σ-LAW note … is ACCEPTED at 2/2”
>
> Thus PE5/PE6 certify the frozen post-r4 proof body; they are not represented as clean passes over future orchestrator annexes. The erroneous Annex #3 status sentence is a real ledger defect—repaired under Finding 1—but it does not retroactively invalidate the frozen body’s 2/2 acceptance.”

**CONDITIONALITY:** **A finding the certifier REJECTS, with the note's own three sentences as the rebuttal — and the rebuttal only works because of freeze predicate (F3).** Three quoted defences:
(i) the annex header separates frozen body from ledger entries (`.47`);
(ii) the acceptance **enumerates** what it covers, including an open box **as a box** (`.46`);
(iii) supplier status is recorded independently (`.53`).
**The concession is explicit and correct**: “The erroneous Annex #3 status sentence **is a real ledger defect** — repaired under Finding 1 — **but it does not retroactively invalidate the frozen body's 2/2 acceptance**.”
**This unit is the clearest corpus-level evidence for the value of an acceptance-scope enumeration** — without (F3), a CRITICAL against a later annex would have been arguable against the acceptance itself. Recorded as format evidence at §6.3.

**DERIVATION:** A rebuttal from the note's own text.

**RESOLUTION TRACE:** statement 1596–1612 · the three quoted defences 1357, 1348–1350, 1440 · the real defect's repair 1459–1476 (`.55`).

**TEETH:** NONE. **Disposition: `decorrelated-model audit` returning NOT-A-FINDING** — a rejected finding, recorded with its reasoning, which is itself a datum about the audit's calibration.

---

### EFF.GRTW2.60  [instrument-record]  — the E5 verification parenthetical

**CANONICAL STATEMENT:** verbatim, lines 1614–1632 (the note's final lines).

**FORM:** italic parenthetical closing the append, finding by finding.

> “*(The adjudication above was produced by the E5 certification run
> (gpt-5.6-sol high, runs/cert2/E5_grtw2_output.log, 2026-08-12);
> orchestrator verification before transcription — finding 1's
> withdrawal checked against the C5 quotes (the Σ-LAW annex proves
> OPEN-2a's shared-below forward implication only; the preceding annex
> itself says the above-r₀ claims are unchanged); W2-C1-CORR's
> geometricity criterion re-derived (B_m = wψ_m(ξy) ⟺ a_j = wξ^j on
> supp ψ_m; at {0,1,2} ⊆ supp this forces ρ₁² = ρ₀ρ₂, which HR-REC
> does not supply off (C-coll)); the index fix's degree argument
> re-checked (deg Φ_q = e_{q−1}g_{q−1}·deg Φ_{q−1} > deg φ_q whenever
> e_{q−1}g_{q−1} > 1, so the old pairing could never satisfy
> deg D_q < deg φ_q; the dictionary φ_q^{GMN} = Φ_{q−1}^{har} makes
> the corrected pairing degree-matched); the W2-C3 re-display's
> μ-computation checked (the φ-augmentation of Φ = φ + D reads
> min{γ, μ(D)} = μ(D) < γ while the Φ-augmentation reads γ — matching
> ledgers do not give equal valuations); the ARTIFACT rebuttal checked
> against the acceptance record's "accepted AS A BOX" enumeration.
> Transcribed unaltered per the standing division of labor. Ledger:
> row 23 → all four repairs folded, awaiting sol discharge (cert3).)*”

**CONDITIONALITY:** **The only evidence that the transcribed certifier output was checked, and it is finding by finding.** Its closing line fixes the status: “**Ledger: row 23 → all four repairs folded, awaiting sol discharge (cert3).**”
**One verification is a cross-check the certifier did not make**: “finding 1's withdrawal checked against the C5 quotes (… **the preceding annex itself says the above-r₀ claims are unchanged**)” — i.e. the orchestrator noticed that `.50`'s Direction line already fenced against `.53`'s over-claim ✓ **which this compiler independently recorded at `.53` as shard 2's own source defect 3** ✓.

*Compiler cross-check (rule 22).* This shard independently recomputed **all four** verification claims: the geometricity criterion and `ρ₁² = ρ₀ρ₂` (`.56`, and at `.25` before reading the append) ✓; the index fix's degree argument (`.57`, and at `.09` before reading) ✓; the `μ`-computation (`.58`, and at `.29` before reading) ✓; the ARTIFACT rebuttal's dependence on the acceptance enumeration (`.59`) ✓. **Four of four reproduced. No discrepancy between the parenthetical's claims and this compiler's independent recomputation — and three of the four were reproduced by this compiler in the shard-1-homed range before the append was read.**

**DERIVATION:** Verification record.

**RESOLUTION TRACE:** statement 1614–1632 · the four findings 1459–1594 · the ARTIFACT 1596–1612.

ARTIFACT: `runs/cert2/E5_grtw2_output.log` ✓ · `runs/cert/C5_grtw2_output.log` ✓.

**TEETH:** **`in-house hostile pass` / `arithmetic recount` (rule 27).** No instrument ran; four hand re-derivations, all disclosed as such and all independently reproduced here.

---


## 4. XREF verification ledger (consolidated, deduplicated)

Every designation below was checked with fixed-string grep (`grep -cF '<designation>' <file>`)
or file-existence, plus commit-pin verification with `git cat-file -t`, per rule 23.
**25 raw XREF/artifact citations across the two shards (17 from shard 1, 8 from shard 2 —
matching each shard's own closing line)** reduce to **21 distinct targets**; four are
cited identically by both shards (`GRTJB_PROOF`, `OPEN2ATTACK_2026-08-08.md`,
`SIGMALAW_PROOF_2026-08-08.md`, `WELDMASTER_2026-08-08.md`) and are marked `**DEDUP**`.

**One granularity mismatch, found at this merge and flagged rather than silently
reconciled.** Shard 1's 17-row table lists the sealed runner as **three separate rows**
(`grt_w2_checks.py`, `grt_w2_checks_output.txt`, `grt_w2_checks_results.json`); shard 2's
8-row table cites the **same three files** as **one bundled row** ("`grt_w2_checks.py` + 2
artifacts — 3/3 PRESENT"). Both counts are internally consistent with their own shard's
stated total (17 and 8 respectively) and both cite the identical three files — the
mismatch is in **row-counting convention**, not in what is cited. Recorded below as one
consolidated row (matching shard 1's finer granularity) with both shards' citation noted.
**A second, softer overlap**: shard 1's row 17 bundles `GRTW2_passPE1_report.md` through
`GRTW2_passPE4_report.md` as one "4/4 PRESENT" row; shard 2 cites `GRTW2_passPE4_report.md`
alone as its own row. The PE4 report is therefore the one file named by both shards, but
under different bundling — not a clean row-for-row DEDUP, recorded as a **partial overlap**
rather than forced into the four-row DEDUP count above.

`[TABLE — compiler ledger]`

| # | Target : designation / file | Count / status | Role | Source shard(s) | Dedup |
|---:|---|---|---|---|---|
| 1 | `GRTJC_PROOF_2026-08-08.md:TR-3′-GEN` | **8** | The corpus's two-operator dictionary, OPEN at general order — route (1) of the derivability adjudication and the W-1 perimeter (`.34`, `.39`) | s1 | — |
| 2 | `spec/HYPOTHESIS_LEDGER.md:HYP.139` | **20** | The ledger row for the W-1 transport (census I-4), class MATH, ATTEMPT (`.39`) | s1 | — |
| 3 | `docs/TIGHTNESS_CENSUS_2026-08-11.md` | PRESENT | Census row I-4 L48 and §5 L131 — the row's WHERE | s1 | — |
| 4 | `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md` | PRESENT | [ILN]† S0.1/S0.2, consumed verbatim (`.08`, `.40`) | s1 | — |
| 5 | `lean/notes/openmath/GRTWELD_PROBE_2026-08-08.md` | PRESENT | The probe that falsified W-2's byte-equality branch (`.04`) | s1 | — |
| 6 | `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md` | PRESENT | The blueprint junction §3.2 (`.04`) | s1 | — |
| 7 | `docs/references/HigherNewton.tex` | PRESENT | The GMN print; anchors tex 1028, 1166–1258, 1257–1283, 1285, ~1291, 1288, 1373, 1431, 1447, 1497, 1719, 2053 (`.06`) | s1 | — |
| 8 | `docs/GMN_citations.md` | PRESENT | The project's Def-2.12 cite mapping (`.06`) | s1 | — |
| 9 | `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md` | PRESENT | [JB], route (2) of the adjudication; §0M row 15 the fold target (`.24`, `.34`, `.41`) / the executed fold (`.48`) | s1+s2 | **DEDUP** |
| 10 | `lean/notes/openmath/OPEN2ATTACK_2026-08-08.md` | PRESENT | The unit that NARROWED (OPEN-2a) (`.33`) / (`.49`) | s1+s2 | **DEDUP** |
| 11 | `lean/notes/openmath/SIGMALAW_PROOF_2026-08-08.md` | PRESENT | The Σ-LAW supplier that PROVED (OPEN-2a) forward (`.33`) / ACCEPTED 2/2 (`.50`, `.53`) | s1+s2 | **DEDUP** |
| 12 | `lean/notes/openmath/WELDMASTER_2026-08-08.md` | PRESENT | (M4)'s W2-C3 face, the fold target (`.41`) / the executed fold (`.48`) | s1+s2 | **DEDUP** |
| 13 | `verification/openmath/grt_w2_checks.py` + `grt_w2_checks_output.txt` + `grt_w2_checks_results.json` | 3/3 PRESENT | The sealed runner (`.07`, `.32`, `.37`) — verified a **fourth** time by shard 2 (`.44`) | s1 (3 rows) + s2 (1 bundled row) | **DEDUP (granularity mismatch, see above)** |
| 14 | `verification/openmath/iterlawn_pe_reimpl.py` | PRESENT | The enumeration-order source of the counter-instance (`.32`) | s1 | — |
| 15 | `GRTW2_passPE1_report.md` | PRESENT | The first hostile pass (`.03`, `.41`) | s1 | — |
| 16 | `GRTW2_passPE2_report.md` | PRESENT | The second hostile pass (`.03`, `.42`) | s1 | — |
| 17 | `GRTW2_passPE3_report.md` | PRESENT | The third hostile pass (`.03`, `.43`) | s1 | — |
| 18 | `GRTW2_passPE4_report.md` | PRESENT | The fourth hostile pass (`.03`, `.44`) | s1 (bundled row 17) + s2 (own row) | **partial overlap, not counted in the DEDUP-4** |
| 19 | `runs/cert/C5_grtw2_output.log` | PRESENT | The as-built CHALLENGE (`.54`) | s2 | — |
| 20 | `runs/cert2/E5_grtw2_output.log` | PRESENT | The certification adjudication (`.54`, `.60`) | s2 | — |
| 21 | `spec/HYPOTHESIS_LEDGER.md:HYP.139` | (same as row 2) | — | — | already counted at row 2 |

**Commit pins verified with `git cat-file -t` (all → `commit`), consolidated (shard 1
recorded 22, shard 2 recorded 14, twelve of shard 2's overlap with shard 1's own list —
`5054d69`, `66b3498`, `bd82766`, `8064ae3`, `59c1ff2`, `6b24942`, `6e57e03`, `5463f2a`,
`083adff`, `8d5e3fa`, `79e796b`, `ffa1e57`, `9bd938f`, `79d1d9c`, `e92cb22` are cited by
both; `874d26b`, `55f7416`, `a6f7653`, `f8c2c09` by shard 1 only; `ba2c47c`, `9d8aba0`,
`adc6cf3` by shard 2 only): **24 distinct commit hashes, 24/24 → commit, re-verified fresh
at merge time.**

**Hash pinning quality (rule 23), consolidated.** The runner sha256
`71f8fc90f7543fd3…` is **truncated at all five of its occurrences across the merged
inventory** (four in shard 1 — `.03`, `.37`, `.41`–`.43` — one in shard 2 — `.44`) —
**UNPINNED**, carried forward as UNPINNED rather than silently treated as pinned, per the
task's standing charge: this is the note's most-verified object (four independent
byte-identity passes plus a fifth freeze restatement) and it never carries a full hash in
the note's own text. One further UNPINNED run: `/tmp/w2_pe3_fresh.py` (`.32`), a temp-file
path not present and not expected to be.

### Sample re-verification (10 of 21, grep/exists-rerun at merge time against the working
tree — favouring both-shard-cited targets and distinctive counts)

`[TABLE — compiler ledger]`

| Target : designation | Recorded | Re-verified | Match |
|---|---|---|---|
| `GRTJC_PROOF_2026-08-08.md:TR-3′-GEN` | 8 | 8 | OK |
| `spec/HYPOTHESIS_LEDGER.md:HYP.139` | 20 | 20 | OK |
| `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md` (DEDUP) | PRESENT | PRESENT | OK |
| `lean/notes/openmath/OPEN2ATTACK_2026-08-08.md` (DEDUP) | PRESENT | PRESENT | OK |
| `lean/notes/openmath/SIGMALAW_PROOF_2026-08-08.md` (DEDUP) | PRESENT | PRESENT | OK |
| `lean/notes/openmath/WELDMASTER_2026-08-08.md` (DEDUP) | PRESENT | PRESENT | OK |
| `verification/openmath/grt_w2_checks.py` (DEDUP, granularity mismatch) | PRESENT | PRESENT | OK |
| `GRTW2_passPE4_report.md` (partial overlap) | PRESENT | PRESENT | OK |
| `runs/cert/C5_grtw2_output.log` | PRESENT | PRESENT | OK |
| `runs/cert2/E5_grtw2_output.log` | PRESENT | PRESENT | OK |

**10/10 sampled targets match exactly — no drift found**, unlike EFF-HE3.md's merge
(which found a genuine count error on `HE7_PROOF_2026-08-08.md:HE3-BOX-6`, 12 vs 1). The
sample deliberately covers both designation-count rows, all four clean DEDUP pairs, the
granularity-mismatch row, and the partial-overlap row. Blob hash of the source note
re-verified identical to the header's pin (§1): no STOP condition triggered.

### Sample statement-quote re-verification (5 of 60, checked verbatim against the source
note by line number)

`[TABLE — compiler ledger]`

| Statement | Quoted fragment | Source lines | Match |
|---|---|---|---|
| `.01` (the title headline) | "# GRTW2 — W-2, THE LIFT JUNCTION, in its corrected three-clause form: admissible representative + unit covariance (the (ξ,w) closed form) + ψ-transport threaded through the tower" | 1 | OK, byte-exact |
| `.19` (the (ξ,w) closed form) | "A_m := ℓ_{m−1}·g_{m−1}·γ_m … χ_m := χ_{m−1}^{ ℓ′_{m−1} − ℓ_{m−1}·w_{m−1}Φ_{m−1} } · z_{m−1}^{ A_{m−1}·ℓ_{m−1} } …" | 396–411 | OK, byte-exact |
| `.37` (the §6.1 machine bracket table) | "### 6.1 Machine bracket (this unit's runner, sealed roster; 0 violations, 6,403 samples)" + the 12-row table opening "CK-MM \| W2-L2 mismatch identity … \| 4,396 \| GREEN" | 942–947 (of 942–966) | OK, byte-exact |
| `.46` (the ACCEPTANCE RECORD opening) | "## ★ ACCEPTANCE RECORD (orchestrator, 2026-08-07) ★ … **THIS NOTE IS ACCEPTED at 2/2** — PE5 (ba2c47c, CLEAN; the 17-theorem Lean leg) and PE6 (9d8aba0, CLEAN; …)" | 1334–1338 (of 1334–1353) | OK, byte-exact |
| `.56` (E5 finding 2 opening) | "## 2. REAL — W2-C1 lacks scalar-orbit geometricity outside (C-coll) … Section 3.3(c) computes the slot ratios but does not prove they form a geometric progression." | 1478–1483 (of 1478–1531) | OK, byte-exact |

**All 5 sampled quotes are byte-identical to the source note at the cited lines; no drift
introduced by the renumbering pass.** The sample deliberately covers both shards' HOME
ranges, the unit carrying this merge's headline supplier-finding (`.37`), the acceptance
record, and the E5 CRITICAL-adjacent theorem correction.

---

## 5. Local supply/consumption ledger

GRTW2's own protocol (header predicate B, stated in the note's own words twice, `.41` and
`.42`): **"accepted texts are NEVER edited by this unit."** It *records fold implications
for the orchestrator* and leaves them owed rather than executing them itself. The table
below merges both shards' independent §3.2 tables (shard 1: 6 rows; shard 2: 5 rows) into
one consumer-direction ledger, deduping the two suppliers both shards separately tracked
(GRTJB, WELDMASTER) by combining each shard's complementary description of the same
executed fold.

### 5.1 Consumer-direction ledger (mathematical supply versus append/consumption
protocol, kept strictly distinct per the header's predicate split)

`[TABLE — compiler ledger]`

| Consumer | Verified target | GRTW2 EFF units (supply) | Mathematical status | Append/consumption-protocol status |
|---|---|---|---|---|
| **GRTJB (accepted)** | §0M row 15's subordinate cell; §0M column (d) | `.24`, `.29`, `.41`, `.48` | Column (d) already consumes the REPAIRED W2-C1a pairing (PE1 §C.4); §0M row 15's W-2 grade citations now governed by supplier HEAD | **Not landed by GRTW2** (r1's own words: recorded as owed to the orchestrator) — **but EXECUTED, at `5054d69`, by the orchestrator**, as GRTJB's own fold-annex erratum E-2. **Both shards agree on the same single fact from complementary vantage points.** |
| **WELDMASTER (accepted)** | (M4)'s W2-C3 face, pinned `[W2]@5463f2a` | `.29`, `.41`, `.48` | The face quotes W2-C3's pre-re-scope wording; the as-of pin makes it drift-proof and PE1 adjudicated it carries the conditionality BY CITATION, so nothing is falsified; (M4)'s cite is now pointed at the re-scoped grade | **Not landed by GRTW2** — recorded as owed — **EXECUTED out of range**, at the fold-carry annex (WELDMASTER annex O-1), after WM's own acceptance `66b3498` — "the half that had to wait for WELDMASTER's own acceptance to become an accepted-text annex item." |
| LIFTCORNER (accepted) / JB / WM | the acceptance's CONSEQUENCE | `.46`'s CONSEQUENCE | "consumers riding W-2 at attempt grade … (the accepted LIFTCORNER's shift-descent consumption; JB's W2-C1 restriction; WM's M4 face) now ride an ACCEPTED supplier at its fenced scope" | Status statement; nothing landed |
| The W-1 dictionary unit | — | `.14`, `.16`, `.39` | W2-L3 in PROVED FORM at level 1 + HR-REC as the transfer shape; **W-1 at orders ≥ 3 NOT advanced** | **Intended consumer; the unit does not exist as a consumer.** The corpus records the transport at **ATTEMPT, class MATH** (HYP.139 / census I-4, `.39`) |
| The W-5 tree unit | — | `.36` | §5.4's carry analysis is "its opening move, not its proof" | Intended; NOT unlocked (`.39`) |
| **OPEN2ATTACK / SIGMALAW (accepted suppliers)** | (OPEN-2a) | `.33`, `.49`, `.50`, `.53` | Two later units NARROWED then PROVED (OPEN-2a)'s forward direction at m ≥ 2, then the Σ-LAW note itself was ACCEPTED 2/2 | **Inbound**, landed as orchestrator annexes on this note (shard-2-homed range) |
| The W-1/W-5/J-A consumer statements | E5 finding 4's consumer sweep | `.58` | "claim no equality of augmented valuations and **survive**" | Not landed; the W-1 perimeter (`.39`) is untouched by E5 |

**The protocol column is not an inference.** GRTW2 states the "accepted texts are NEVER
edited by this unit" protocol in its own words twice (`.41`, `.42`), and records fold
implications rather than executing them; the two owed folds' closing annex (`.48`) says
"Nothing else in the r1 record remains orchestrator-owed." **Zero dated consumption
appends are claimed landed on any consumer by this note, and none is invented here** —
both executed folds were performed BY THE ORCHESTRATOR, on other notes, not by GRTW2
itself.

### 5.2 A supplier-finding flagged for the maintenance queue (MQ)

`spec/HYPOTHESIS_LEDGER.md` maintains a standing `MAINTENANCE QUEUE` (entries `MQ-1`
through `MQ-6` at the time of this merge — checked fresh via `grep -n 'MQ-' spec/HYPOTHESIS_LEDGER.md`).
**This merge run does not itself add an MQ entry — editing `HYPOTHESIS_LEDGER.md` is out
of this deliverable's scope — but flags the following finding as an MQ-candidate** (it
would be **MQ-7** in sequence, if and when an orchestrator books it), since it is a
compiler-discovered (not source-stated) recomputation result against an effectively
sealed table, the exact genre the existing MQ entries track (`spec/EFF-HE7.md` §5.2 flags
two such findings for GENHN/HE7's own merges; this is the analogous finding for GRTW2):

**The §6.1 machine-bracket table's own sample column does not sum to its own headline.**
Shard 1's unit `.37` (source lines 942–966, the §6.1 machine bracket) displays a
`[TABLE]` of 12 rows naming 17 check families with a `samples` column. This merge
recomputed the column sum fresh (rule 22):

> `4,396 + 156 + 156 + 55 + 44 + 16 + 22 + 28 + 44 + 44 + 44 + 684 + 684 + 12 + 7 + 2 + 2`
>
> Step by step: `4,396 + 156 = 4,552`; `+ 156 = 4,708`; `+ 55 = 4,763`; `+ 44 = 4,807`;
> `+ 16 = 4,823`; `+ 22 = 4,845`; `+ 28 = 4,873`; `+ 44 + 44 + 44 = 5,005`; `+ 684 = 5,689`;
> `+ 684 = 6,373`; `+ 12 = 6,385`; `+ 7 = 6,392`; `+ 2 = 6,394`; `+ 2 = 6,396`.
>
> **Total: 6,396.**

**The note's own headline — stated at `.07` ("6,403 samples, 0 violations, 17 check
families all GREEN") and reconfirmed at every round's machine-leg re-run (`.03`'s PE1
report, `.42`'s r2 re-run, `.43`'s r3 re-run, `.44`'s r4 re-run) — says 6,403.**
Shortfall: **7**. The family count itself
reproduces exactly (12 rows naming 17 distinct families: CK-MM, CK-HR1, CK-VD1, CK-REC,
CK-SLOT, CK-SLOT-M1, CK-XI, CK-BYTE, TW-RATIO, TW-ADM, TW-STRICT, TW-F3, TW-F3b, TW-PARI,
TW-QO, CK-T3E, MT-TW = 17 ✓, matching the header's own "17 check families" sentence). **The
gap is not reconcilable from the displayed table** — most plausibly a family with an
unlisted sample sub-count (e.g. TW-QO's 7 counted once here and again in an
undisplayed per-shape breakdown), but the note supplies no decomposition. **No individual
claim is thereby wrong — every one of the 17 families is GREEN with 0 violations — but a
merge that re-derives the total from the displayed table will not land on 6,403.** Shard 1
already recorded this itself, independently, as its own **"source defect 4"** before this
merge re-verified it; this merge's own fresh recomputation reproduces the identical
7-sample shortfall.

**This is a compiler-discovered recomputation result against what is effectively a
sealed/frozen table** — freeze predicate (F2) certifies the runner and both artifacts
byte-frozen across every round, so the table itself cannot be repaired in place without
breaking that freeze — exactly the genre `spec/EFF-HE7.md` §5.2 flags as an
**MQ-candidate** rather than a silent repair. **This finding is carried in two places by
design, and each points at the other**: here (§5.2), and in §8's consolidated
source-defects list below (item drawn from shard 1's own defect 4), so a reader landing on
either is directed to the other.

---

## 6. TEETH inverse table (unified from both shards; presented as two sub-tables by
shard-of-origin — shard 1 carries the core sealed machine bracket plus the four round
blocks' fresh legs, shard 2 carries PE4's exhaustive selection-geography leg, PE5/PE6's
acceptance legs, the OPEN2ATTACK/SIGMALAW batteries, and the E5 hand re-derivations — with
one combined zero-orphan statement closing both)

### 6.1 Shard 1's core battery and round-block legs (IDs unchanged, offset 0)

`[TABLE — compiler ledger]` Battery row / tooth → guarded unit(s) → disposition.

| Battery row / tooth | Guarded unit(s) | Disposition |
|---|---|---|
| **CK-MM** (4,396 integer + element samples) | `.13`, `.16`, `.09` | Executable regression — the largest family; **it is what makes "only the naming was off" checkable** |
| **CK-HR1** (156) | `.12` | Executable regression |
| **CK-VD1** (156) | `.14` | Executable regression — the level-1 dictionary, the note's one PROVED gift to W-1 |
| **CK-REC** (55 nodes) | `.16` | Executable regression against an independent semantic simulator |
| **CK-SLOT / CK-SLOT-M1** (44 / 16) | `.18`, `.17` | Executable regression; the non-perimeter rows are checked against the recursion, not the scalar form |
| **CK-XI** (22: 21 perimeter + 1 recorded boundary) | `.19`, `.21`, `.23`, `.25` | Executable regression — **checks that the displayed pair SATISFIES the orbit equations, which is exactly the weakened claim `.21` makes; it does NOT check that a scalar orbit must exist** (the gap E5 finding 2, `.56`, exposes) |
| **CK-BYTE** (28: 22 walked + 6 SKIP recorded) | `.22`, `.31` | Executable regression, with the walk/no-walk split disclosed |
| **TW-RATIO / TW-ADM / TW-STRICT** (44 each) | `.29`, `.30`, `.33` | Executable regression — **but TW-STRICT is SAME-ADJACENT given TW-ADM, self-reclassified; not three independent legs** |
| **TW-F3 / TW-F3b** (684 / 684) | `.35`, `.28` | Measurement — the probe's 96 RED all GREEN, with an unchanged control |
| **TW-PARI / TW-QO** (12 / 7) | `.29` | Executable regression against PARI; **the seal's "PREDICT 24/24" is a disclosed miscount** (`.37`) |
| **CK-T3E** (2, both directions) | `.36` | Executable regression, **with the per-pair overflow identification explicitly not machine-keyed** |
| **MT-TW** (2) | `.29`, `.34` | Planted mutant — a garbled character (ξ·z₁) caught on both designated rows; **fired** |
| **probe F0 / F2 / F2-orbit / F4 / F3** (21, 45, 45, 24, 96 RED) | `.12`, `.24`, `.25`, `.28`, `.35` | **Foreign-note evidence** — and the probe's 6 F2 FAILURES are the evidence for W2-C1a's chamber qualifier |
| **PE2's fresh leg** (16/16 at m = 1 + hand T3B/T3F) | `.19`, `.42` | Executable regression on a decorrelated instrument |
| **PE3's fresh leg** (own tower-field arithmetic + own §3.4 evaluator, 22/22 + I4B r = 5 from scratch) | `.23`, `.43` | Executable regression on a third decorrelated instrument |
| **PE3's counter-instance** (K₁ = F₄, ψ₁ = y³+ζ) | `.32`, `.31`, `.33` | **Planted counter-instance; FIRED against the note's own converse** |

**PROOF-ONLY rows (shard 1, rule 16), with the note's own coverage-hole sentence:**

| Unit | Coverage hole, in the note's words |
|---|---|
| `.26` (§4.3) | "This parametrization stands **review-owed** (probe fence inherited)" — no tooth, by design |
| `.33` (W2-OPEN-2(a)–(b)) | "**OPEN**, instance-confirmed 44/44 (live region = the 6 above-twist junction-levels)" |
| `.35` (W2-OPEN-1) | "**instance-confirmed, not proved**"; the carry analysis "is NOT claimed here" |
| `.23` (the scalar form off (C-coll)) | W2-BOX-1: "the scalar form is proved only on (C-coll)"; "exactly 1 boundary junction" on the roster |
| `.36` (the 24 overflow pairs) | `[r1, F7]`: "asserted per-mechanism and not machine-keyed pair-by-pair" |
| `.39` (W-1 at orders ≥ 3) | "W-1 at orders ≥ 3 is **NOT advanced**" — a negative claim, no tooth possible |

**AUDIT-disposition rows (shard 1, rule 27):**

| Finding | Unit | Class |
|---|---|---|
| Clause 3's warrant applies clause 1 off its own perimeter (PE1 F1) | `.30` | in-house hostile pass — the arc's founding finding |
| W2-C1a's unqualified statement has 6 probe failures (PE1 F2) | `.24` | transfer audit — a foreign instrument's red rows |
| Three machine counts copied across notes without reconciling rosters (PE1 F3) | `.18`, `.22` | arithmetic recount |
| A sealed docstring preregisters a sample count the family does not have (PE1 F4) | `.37` | in-house instrument audit |
| An r-indexed name collides with a level-indexed element (PE1 F5) | `.23` | in-house hostile pass |
| A naming parenthetical conflated two opposite-signed print exponents (PE1 F6 → **reverted** at PE2 P2) | `.13`, `.26` | transfer audit at source — and the reversal is itself a transfer audit |
| "recorded ξ = 1 ⟹ byte-equal" is not definitional (PE2 P1) | `.30`, `.31` | in-house hostile pass |
| The premise pairs keys of different degrees (PE2 P3; **recurs, caught again at E5 finding 3, `.57`**) | `.09`, `.33` | in-house hostile pass, then decorrelated-model audit |
| The identification is two-sided in the text and one-sided in the proof (PE3 P1), with a constructed counter-instance | `.31`, `.32` | decorrelated construction |
| The r3 species sweep did not exhaust the species (PE4 P1) | `.38`, `.39`, `.44` | in-house hostile pass |

**Both-direction audit (shard-1 range).** Every row guards at least one unit; every
toothed unit appears. Units with **`TEETH: NONE`** — `.01`, `.02`, `.06`, `.08`, `.26`,
`.39`, `.40` — are headlines, declarations, hypotheses, fences or negative claims. Units
flagged **Indirect** — `.11`, `.20` — ride the composite families. **Zero battery-row
orphans in shard 1's range; zero toothed-unit orphans; six signed PROOF-ONLY units; ten
AUDIT-class findings across four passes.**

### 6.2 Shard 2's r4/acceptance legs, annex batteries, and E5 hand re-derivations
(renumbered, `.44`–`.60`)

`[TABLE — compiler ledger]`

| Battery row / leg | Guarded unit(s) | Disposition |
|---|---|---|
| **PE4's selection-geography leg** (33,408 / 0 over 4,173 monic irreducibles × 7 fields; spurious set exactly two triples; ZERO at g ≤ 2; W2-ID1 forward 29,223 grid points / 0 incl. g ∈ {3,4}) | `.44`, `.31`, `.32` | Executable regression, **exhaustive** — converts shard 1's disclosure into an exact characterization and supplies the `g = 2` fact its text states too tersely |
| **PE4's machine re-run** (6,403/0, 17 GREEN, JSON byte-identical incl. elapsed_s, both seals intact) | `.44` | Executable regression; the fourth freeze verification |
| **PE5's 17-theorem Lean leg** | `.46` | Decorrelated instrument, CLEAN |
| **PE6's Sylvester-resultant route** (566 junctions incl. 560 off-roster; functional-equation re-derivation of HR-REC; PE5 Lean appendix recompiled) | `.46`, `.16` | Decorrelated instrument, CLEAN — **the arc's widest coverage and an independent re-derivation of HR-REC** |
| **OPEN2ATTACK's Σ-LAW leg** (468 sealed + 24 extension m ≥ 2 rows, 0 violations, every gap row included) | `.49`, `.33` | Executable regression on a new sealed battery |
| **OPEN2ATTACK's converse extension** (16 constructed spurious-selection witnesses; PE4 o-e's third read measured; 604 byte-equal rows) | `.49`, `.32` | Planted constructions confirming a predicted genre at m ≥ 2 |
| **SIGMALAW's battery** (1,211 walked junction rows over 539 towers; SL-VDM 2,828 / SL-DELTA 1,414 / SL-PHIR 1,414 / SL-GAP 680; 0 violations; 3 teeth 2/2 each) | `.50`, `.52` | Executable regression — **figures corrected twice** (`.51`, `.52`) |
| **SIGMALAW's non-involution separators** (96 at m = 2, 27 at m = 3, where the ξ-law holds and BOTH boxed variants fail) | `.50` | Planted separators; **they DIAGNOSED the sealed battery's own involution degeneracy** (218/218 slot-samples sitting where the maps coincide) |

**PROOF-ONLY rows (shard 2, rule 16):**

| Unit | Coverage hole |
|---|---|
| `.55` (W2-OPEN-2(a)–(b)) | "**OPEN and instance-confirmed on the six live roster junction-levels**" — no theorem, six instances |
| `.56` (the geometricity test) | No family tests whether a scalar orbit MUST exist; CK-XI tests only that the displayed pair satisfies the equations (`.21`) |
| `.57` (the index fix) | An index in a discharge route; no instrument applies |
| `.58` (the ledger-equivalence re-display) | A wording scope; the underlying counter-derivation is symbolic |

**AUDIT-disposition rows (shard 2, rule 27):**

| Finding | Unit | Class |
|---|---|---|
| The r3 species sweep did not exhaust the species | `.44` | in-house hostile pass — **a METHOD finding, cured by a full-note grep** |
| The `[r3]` converse flag SUFFICES — no finding | `.44` | in-house hostile pass **declining to raise a finding** |
| Tooth-run leakage in quoted Σ-LAW figures | `.51` | decorrelated-model audit (on the supplier note) |
| The count correction was itself transposed | `.52` | arithmetic recount (the supplier's second pass) |
| ANNEX #3 falsely closes W2-OPEN-2 — **CRITICAL** | `.53`, `.55` | decorrelated-model audit |
| HR-REC does not force geometricity | `.56` | decorrelated-model audit |
| The P3 index fix missed a second occurrence | `.57` | decorrelated-model audit |
| "same induced valuation data" contradicts the note's own route (3) | `.58` | decorrelated-model audit |
| PE5/PE6 scope — **finding REJECTED** | `.59` | decorrelated-model audit returning NOT-A-FINDING |
| Four hand re-derivations reproducing all four E5 findings | `.60` | `in-house hostile pass` / `arithmetic recount` — no instrument ran |

**Both-direction audit (shard-2 range).** Every leg guards at least one unit; every
toothed unit appears. Units with **`TEETH: NONE`** — `.45`, `.47`, `.48`, `.53`, `.55`,
`.57`, `.58`, `.59`, `.60` — are bookkeeping, fences, status records, wording corrections
and verification records. **Zero orphans; four signed PROOF-ONLY units; ten AUDIT-class
findings, of which one is a CRITICAL and one is a rejection.**

### 6.3 Combined zero-orphan statement

**Both-direction audit, unified across all 60 units.** Every battery row in either
sub-table guards at least one unit in the merged inventory; every unit whose `TEETH` field
names a battery row appears in some row above. Combining both shards' `TEETH: NONE`
lists — `.01`, `.02`, `.06`, `.08`, `.26`, `.39`, `.40` (shard 1) and `.45`, `.47`, `.48`,
`.53`, `.55`, `.57`, `.58`, `.59`, `.60` (shard 2, renumbered) — gives **16 declaration/
fence/status units outside the orphan count**; units flagged **Indirect** — `.11`, `.20` —
are guarded compositely. **Zero battery-row orphans; zero toothed-unit orphans across all
60 units; ten signed PROOF-ONLY units (6 shard 1 + 4 shard 2); twenty AUDIT-class findings
(10 shard 1 + 10 shard 2), of which one (E5 finding 1, `.55`) is a CRITICAL and one (E5
finding 5, `.59`) is a rejected finding recorded for its own calibration value.**

---

## 7. SERIES, cross-shard supersession edges, and boundary resolution

### 7.1 The dated-arc SERIES: GRTW2-GRADE-ARC (7 members, TERMINAL — GRTW2 **IS**
accepted, 2/2)

Both shards independently name this construct and each supplies exactly the links inside
its own HOME range: shard 1's `.02` states the full 7-member table in its own
CONDITIONALITY field; `.03`'s own header self-labels "member 2 of 7"; shard 2's `.44`
(=`s2of2.01`) self-labels "member 6 of 7"; shard 2's `.46` (=`s2of2.03`) self-labels
"member 7 of 7 (TERMINAL)". **Four independent internal descriptions name exactly the
same seven links, in the same order, with no duplication and no gap.** Assembled here as
one block, per the merge charge.

`[TABLE — compiler ledger, assembled from EFF.GRTW2.02's own CONDITIONALITY table plus
the self-labelled headers at EFF.GRTW2.03, .44, and .46]`

| Link | Unit | Round | Grade movement | Content (quoted from the unit or its own resolution) |
|---:|---|---|---|---|
| 1 (origin) | `.02` | composition-time status | **0/2** | "Genre: PROOF NOTE at attempt grade (acceptance counter 0/2; no gate fires…)"; `[r3, o2]` later strikes the stale "no acceptance arc opened" half, leaving the counter itself untouched at this link |
| 2 | `.03` | S-STATUS (CURRENT as of r4) | **stays 0/2** | "S-STATUS (CURRENT): attempt grade, acceptance counter 0/2 (ZERO clean passes), FOUR hostile passes RUN and FOUR repair rounds applied" |
| 3 | `.41` | `[r1]` round block | **stays 0/2** | "Counter 0/2 (ZERO clean passes); W2-PE2 — a fresh hostile pass on this post-r1 text — is the next acceptance attempt." |
| 4 | `.42` | `[r2]` round block | **stays 0/2** | PE2 NOT CLEAN (0 CRITICAL + 2 JUSTIFICATION GAPS + 1 minor); "counter 0/2 … W2-PE3 … next" |
| 5 | `.43` | `[r3]` round block | **stays 0/2** | PE3 NOT CLEAN (0 CRITICAL + 1 JUSTIFICATION GAP minor); "counter 0/2 … W2-PE4 … next" |
| 6 | `.44` | `[r4]` round block (shard 2's HOME) | **stays 0/2** | PE4 NOT CLEAN (0 CRITICAL + 1 JUSTIFICATION GAP + 1 minor); "**Counter 0/2 (ZERO clean passes); W2-PE5 — a fresh hostile pass on THIS post-r4 text — is the next acceptance attempt.**" |
| 7 (**TERMINAL**) | `.46` | PE5 + PE6 (post-r4, both CLEAN) | **0/2 → 2/2, ACCEPTED** | "**THIS NOTE IS ACCEPTED at 2/2** — PE5 (ba2c47c, CLEAN; the 17-theorem Lean leg) and PE6 (9d8aba0, CLEAN; the Sylvester-resultant route on 566 junctions incl. 560 off-roster …)" |

**GRTW2 reaches 2/2 accepted — unlike the sibling HE3 merge, whose GRADE-ARC SERIES
terminates at 1/2 (HE3 is NOT accepted). The two must not be conflated.** `.02`'s and
`.03`'s "counter 0/2 (ZERO clean passes)" and "W2-PE5 … is the next acceptance attempt"
sentences are `STALE-SELF-DESCRIPTION` (rule 26) at HEAD — the acceptance landed after
they were written, and the frozen text is not edited to say so; this SERIES table is
where the current status actually lives.

**Uniqueness verified:** an exhaustive scan of every CONDITIONALITY field and every unit
header in the merged 60-unit inventory for the string `GRTW2-GRADE-ARC` confirms exactly
the four member-declarations named above (`.02`'s own table naming all seven; `.03`'s
heading "member 2 of 7"; `.44`'s heading "member 6 of 7"; `.46`'s heading "member 7 of 7
(TERMINAL)") and no fifth-shard, sixth-shard, or duplicate candidate anywhere else. **No
duplicate link, no skipped link, TERMINAL uncontested.**

### 7.2 Cross-shard supersession edges (consolidated, with SUPERSESSION KIND)

The header records that **nine dated corrections land inside shard 1's HOME range**, all
physically drafted in shard 2's range (rule 7: HOME is determined by an edit's
*destination*, not its physical drafting location — the rule T1's, HE7's and HE3's merges
also used). Shard 1's own §6.3 format-notes tally this as **"CHAIN with TERMINAL ×9, one
of length five"**; the length-five one is `.05`'s Grade cap CHAIN (five correction layers
over the struck r0 base statement — six numbered items in the unit's own enumeration,
counting the struck original as item 1, but only five of them are corrections proper; this
compiler reproduces the unit's own "FIVE members" self-description faithfully rather than
silently renumbering it to six). The table below lists every cross-shard edge, using the
vocabulary already exercised throughout the merged inventory: **replacement | license |
wording-rider | provenance-rider | scope-pin | as-of scoping | counter re-reading |
inventory completion** — every kind except `wording-rider` appears at the unit level; the
one gap is noted below.

`[TABLE — compiler ledger, consolidated from shard 1 §7's nine-item cross-shard list and
shard 2 §7's "riders landing on shard 1" enumeration — both name the identical nine
corrections]`

| From | To | Kind | Content |
|---|---|---|---|
| `.48` (fold-carry annex) | `.41` | inventory completion | Both of `.41`'s owed fold implications (GRTJB §0M row 15, WELDMASTER (M4)'s cite) EXECUTED; "Nothing else in the r1 record remains orchestrator-owed" |
| `.49` (OPEN2ATTACK, NARROWED) | `.33` | license | (OPEN-2a)'s forward direction at m ≥ 2 reduced to a single displayed lemma (the Σ-LAW); "box NARROWED …, NOT closed" |
| `.50` (SIGMALAW, PROVED) | `.33`, `.31`, `.05` | license | (OPEN-2a)'s forward direction PROVED at attempt grade; W2-ID1's `m = 1` restriction becomes historical (holds at every m); the two instance-warranted census entries at `.05` gain a theorem |
| `.50` (SIGMALAW) | `.19` | counter re-reading | "the covariance map is the ξ-formula composite … NOT the bare interior twist" — a correction to how `.19`'s characters are consumed downstream, not to `.19` itself |
| `.51` → `.52` (in-range) | `.50` | counter re-reading | The Σ-LAW's own quoted machine figures corrected twice (tooth-run leakage, then a transposition); `.52` is TERMINAL for this three-membered, wholly-within-shard-2 sub-chain |
| `.53` (ANNEX #3, supplier upgrade) | `.33`, `.31` | license | (OPEN-2a)'s forward direction now rides an ACCEPTED Σ-LAW supplier (sentences 1–2 of the annex) |
| `.53` (ANNEX #3, over-claim) | `.33` | replacement (withdrawn) | Sentence 3's "W2-OPEN-2's residual open surface: the converse … only" conflates (OPEN-2a) with W2-OPEN-2(a)–(b); **superseded by `.55`, below** |
| `.55` (E5 finding 1) | `.33` | replacement | ANNEX #3's over-claim WITHDRAWN; the three-way status (OPEN-2a PROVED / W2-OPEN-2(a)–(b) OPEN on six live junction-levels / the converse separately UNPROVED) is TERMINAL, awaiting sol discharge (cert3) |
| `.56` (E5 finding 2, W2-C1-CORR) | `.25`, `.18`, `.05`, `.38`, `.27`, `.26`, `.23` | replacement | **THEOREM W2-C1's universal reading SUPERSEDED outside (C-coll)**; census re-displayed 37/44 theorem-derived + 1/44 individually confirmed + 6/44 above-twist; `.38`'s claims-table row and `.05`'s Grade-cap census both move |
| `.57` (E5 finding 3) | `.33`, `.09` | replacement | The key-carry index fix `Φ_q ⇝ Φ_{q−1}` — the **second** occurrence of the same misindexing (the first, at `.33`'s own `[r2, P3]`, confirms `.09`'s dictionary but missed this later occurrence in the Equivalent sufficient form) |
| `.58` (E5 finding 4) | `.29`, `.04` | replacement | W2-C3(iii)'s "same induced valuation data"/"MacLane-equivalent" wording SUPERSEDED by ledger-equivalence; clause 3's headline wording (`.04`) is affected identically |

**Total: eleven rows.** Ten are cross-shard edges landing from shard 2 onto shard-1-homed
units (the nine corrections named in the header, with `.50` and `.53` each producing two
rows because a single correction can have two distinct targets, or — for `.53` — two
distinct fates, a license and a withdrawn over-claim). The eleventh (`.51`→`.52`) is an
**in-range shard-2-to-shard-2 edge**, listed for completeness since `.51`'s own correction
is part of the same three-membered Σ-LAW-figures CHAIN as the cross-shard `.50`→`.51`
relationship, matching the convention T1's, HE7's and HE3's merges used for corrections
with multiple targets. **All eleven resolve to a unit that exists in the merged inventory;
zero dangling targets.** Two of the nine corrections (E5 findings 2 and 4, `.56` and
`.58`) **change a theorem's scope**; all four E5 corrections (`.55`–`.58`) are "awaiting
sol discharge (cert3)" — landed, not confirmed.

**No `wording-rider`-kind edge was found among these nine** — every correction here either
replaces a claim, licenses a narrower/wider reading, or counter-reads a figure; the
`wording-rider`/`provenance-rider` kinds are exercised elsewhere in the merged inventory
at in-shard units (e.g. `.57`'s own description of the *first* P3 fix as a provenance
matter) but not at a cross-shard edge.

**Compiler finding on chain-count self-reporting (flagged, not silently reconciled).**
Shard 2's own §6.3 format-notes tally reads **"25 (CHAIN ×4, one of them three-membered
within this range)."** This merge's own fresh audit of every explicit `CHAIN:` field
declared inside shard 2's units finds **five**, not four: (a) the (OPEN-2a) forward-
direction chain (`.33` origin → `.49` → `.50` → `.53`, TERMINAL `.53`, declared at `.49`
and cross-referenced "member 3 of 4"/"member 4 of 4" at `.50`/`.53`); (b) the W2-OPEN-2(a)
–(b) status chain (`.33` origin → `.53`'s over-claim → `.55`'s withdrawal, TERMINAL `.55`);
(c) the Σ-LAW figures chain (`.50` → `.51` → `.52`, TERMINAL `.52` — **this is the
three-membered, wholly-within-shard-2 one the tally names**); (d) the W2-C1 chain (`.25`
origin → `.56`, TERMINAL `.56`); (e) the W2-C3(iii) chain (`.29` origin → `.58`, TERMINAL
`.58`). **Chains (d) and (e) are each two-membered and cross-shard**, and neither is
merely a restatement of (a)/(b)/(c) — they target different theorems. This compiler cannot
determine from the shard's own text which of (d)/(e) it intended not to count, or whether
"CHAIN ×4" simply undercounts by one; **recorded as a source-defect-adjacent finding
rather than silently reconciled to either number.**

**CHAIN, marked TERMINAL (rule 25), the headline W2-C1 → W2-C1-CORR edge the merge charge
names explicitly:** `.25`'s displayed THEOREM W2-C1 ("PROVED on the §3 perimeter") is
contradicted outside (C-coll) by the missing geometricity step E5 finding 2 (`.56`)
identifies → **`.56`/W2-C1-CORR** supplies the three-item conditional replacement (m = 1
unconditional; m ≥ 2 on (C-coll); general shared-key junctions conditional on a displayed
geometricity test) and re-displays the census as 37 + 1 + 6. **TERMINAL: W2-C1-CORR,
awaiting sol discharge (cert3).** **Uniqueness verified:** an exhaustive scan of every
CONDITIONALITY/RESOLUTION TRACE field for `EFF.GRTW2.25` and `W2-C1` as a supersession
*target* confirms only `.56` supersedes it — no third, later correction to the same target
exists anywhere in the 60-unit merged inventory.

### 7.3 Boundary-unit resolution (merge rule 4/7)

Per rule 7 (HOME follows edit destination, not drafting location), all nine corrections
above are **HOMED in shard 2** (drafted and homed at `.48`–`.50`, `.53`, `.55`–`.58`) even
though seven of the nine target sets land on shard-1-HOME units. **Verified: none of the
nine is duplicated as a second unit inside shard 1's range** — an exhaustive scan of the
merged inventory's 60 unit headers (§3) confirms `.48`–`.60` appear exactly once each, at
their shard-2-derived numbers, and no unit numbered `.01`–`.43` independently re-states
any annex or E5 finding as its own content (they are only *cited*, by ID, from the
shard-1-HOME units they target).

**Every unit named in either shard's own §6 BOUNDARY SELF-AUDIT as "physically drafted
elsewhere, HOME-routed" appears exactly once in the merged inventory**, verified two
directions: shard 1's own §6 records no unit drafted in shard 2 but homed in shard 1 (the
traffic is entirely one-directional in this note); shard 2's own §6.1 items 1–8 record the
opposite direction explicitly for `.48`–`.60` (all nine corrections plus the acceptance
record, the round block, and the annex header), each cross-checked here against the
statement inventory (§3) and found present exactly once, at its shard-2-derived ID.

### 7.4 Range-edge audit

Both shards independently audited the physical line boundary and both report the same
clean break: shard 1's own note — "Line 1257 closes §9's Freeze; 1258 blank; 1259 `---`;
1260 blank; 1261 opens `## §10.`" — and shard 2's own note — "Line 1260 (shard 1's last)
is blank; line 1261 opens `## §10.`; the range ends at line 1632, the note's last line
(the closing `)*` of the E5 verification parenthetical)." **Both descriptions name the
identical boundary (1260/1261) and agree it falls on a section break.** The file's own end
(source line 1632) is shard 2's own last line, closing the E5 verification parenthetical's
final `)*`. **Zero units span the shard boundary.**

---

## 8. Self-audit and OPEN-CALLs

**11 raw OPEN-CALLs (6 shard 1 + 5 shard 2) carry forward as 11 distinct.** No pair is
*self-flagged* as a duplicate by either shard (this merge checked for such flags with a
fresh grep — `same call`, `self-identified duplicate`, `recorded in both`, `same as
shard`, `identically as shard`, `same question` — none found across either shard), so per
the standing charge ("dedup self-flagged duplicate pairs"), **nothing here is dedup'd.**
Two pairs are substantively close and are flagged as such below without being merged,
matching `spec/EFF-HE3.md`'s own precedent for its OPEN-CALL 5/8 pair.

### OPEN-CALL 1 (shard 1) — "ACCEPTED 2/2" and three open boxes are simultaneously true,
and the spec cannot decide how a chapter cut presents that

The note is **ACCEPTED at 2/2** (F1), and the acceptance **enumerates an OPEN box among
what it accepts** (F3): "W2-OPEN-2/OPEN-2a as the note's fenced OPEN box — the weld's one
open lemma, **accepted AS A BOX, not as a theorem**." Three further surfaces are open or
fenced at HEAD: **W2-OPEN-1** (value layer), **W2-BOX-1** (scalar form off (C-coll)),
**§4.3** (review-owed convention). **Decision needed: whether a chapter cut may cite W-2
as accepted without reproducing (F3)'s enumeration.** *Substantively close to OPEN-CALL 2
below (shard 2's own copy of essentially the same question); neither shard cross-flags the
other, so both are carried separately.*

### OPEN-CALL 2 (shard 2) — "ACCEPTED 2/2" and the fenced open surfaces

The note is ACCEPTED at 2/2, and the acceptance enumerates an OPEN box among what it
accepts. At HEAD the open surfaces are: **W2-OPEN-2(a)–(b)** (OPEN, instance-confirmed on
six junction-levels, `.55`), **W2-OPEN-1** (open, re-affirmed three times), **W2-BOX-1**
(the scalar form off (C-coll), now formalized as `.56`'s geometricity test), and **§4.3's
review-owed convention fence**; **(OPEN-2a) has left the set** (proved on an accepted
supplier). **Decision needed: whether the merged spec restates the open-surface set at
HEAD — this shard's reading is four surfaces, one retirement — and whether a chapter cut
may cite W-2 as accepted without reproducing (F3).**

### OPEN-CALL 3 (shard 1) — the four E5 certifier corrections are landed-but-undischarged

The 2026-08-12 append closes: "Ledger: row 23 → **all four repairs folded, awaiting sol
discharge (cert3)**." Two of the four **change a theorem's scope** (W2-C1 → W2-C1-CORR;
W2-C3(iii) → ledger-equivalence), one **withdraws a status claim** (W2-OPEN-2), one
**fixes an index** in a discharge route. **Decision needed: whether a chapter cut may
consume landed-but-undischarged certifier corrections as current** — the same question
`spec/EFF-GENHN-s2of2.md` OPEN-CALL 4 and `spec/EFF-HE3-s2of2.md` OPEN-CALL 2 raise. **All
three should be answered together.** *Substantively close to OPEN-CALL 4 below; not
merged, per the same convention.*

### OPEN-CALL 4 (shard 2) — the four E5 corrections are landed-but-undischarged, and two
of them change a theorem's scope

"Ledger: row 23 → **all four repairs folded, awaiting sol discharge (cert3)**" (`.60`).
Two change scope (**W2-C1 → W2-C1-CORR**; **W2-C3(iii) → ledger-equivalence**), one
withdraws a status claim (**W2-OPEN-2**), one fixes an index. **Decision needed: whether a
chapter cut may consume landed-but-undischarged certifier corrections as current** — the
same question `spec/EFF-GENHN.md`'s own OPEN-CALL and `spec/EFF-HE3.md`'s OPEN-CALL 5/8
pair raise. **Across the three notes' merges there are now at least eleven landed-but-
undischarged corrections (four here, five at HE3, per its own §8), and they should be
answered by one decision** — this merge preserves shard 2's own count of "eleven … across
the three notes" as its own claim (not independently re-verified against GENHN's and
HE3's now-completed merges, which is out of this deliverable's scope).

### OPEN-CALL 5 (shard 1) — the W-1 transport ATTEMPT row: compiled status and what
remains undecided

**Compiled status (verified, not inferred):** W-1's transport of the harness `w` and `𝑅`
to the FGMN objects is at **ATTEMPT grade, class MATH, at full strength as of 2026-08-14**
— `spec/HYPOTHESIS_LEDGER.md` **HYP.139** (count **20**), whose WHERE is
`docs/TIGHTNESS_CENSUS_2026-08-11.md` I-4 L48 and §5 L131 ✓ file present. GRTW2's own
position agrees and adds one proved increment: W2-L3 is the level-1 value dictionary in
proved form, HR-REC is the exact transfer shape, and "W-1 at orders ≥ 3 is NOT advanced"
(`.39`, `.05`(e)). **What is undecided and needs a decision:** (i) whether the merged spec
carries the ATTEMPT row as a unit of its own or inside `.39` (this merge preserves shard
1's own choice — inline, in `.39`'s CONDITIONALITY); (ii) whether GRTW2's level-1
increment should be recorded against HYP.139 as partial progress, given the row's
consumer chain runs through GENHN-BOX-2/HYP.148 rather than through W2-L3; (iii) whether
the candidate retiring route (HYP.149's WELD-ZERO fold, at clean-pass 1 of 2) changes
anything here — it does not yet, and this merge records it as not-yet.

### OPEN-CALL 6 (shard 1) — two cross-note consumer claims were not independently
adjudicated

(a) `.24`'s consumer note: "the accepted [JB]'s §0M column (d) already consumes the
REPAIRED pairing … so no accepted text is falsified by this qualifier", adjudicated by PE1
§C.4. **This compiler verified GRTJB exists but did not open §0M column (d).** (b) `.41`'s
fold implications: both were recorded as EXECUTED out of range, at `5054d69` and at the
fold-carry annex (`.48`). **The commits verify; the executed text was not read.**
**Decision needed: whether the merge run performs these two reads, or records them as
inherited assertions.** *This merge did not perform them either* — carried forward
unresolved.

### OPEN-CALL 7 (shard 2) — two executed folds now point at a superseded census

`.48` records both r1 fold implications as EXECUTED, and "Both annotations point at this
note's accepted form (2/2 at `adc6cf3`: **W2-C3 proved-to-first-twist 38/44** …)." `.56`
re-displays that census as 37/44 + 1/44 + 6/44. **Neither GRTJB nor WELDMASTER has been
re-annotated** — verified: no later append in this note mentions either, and this compiler
did not open the two targets. **Decision needed: whether the two accepted consumers are
owed a second annotation, and whether the merge run reads GRTJB §0M row 15 and WELDMASTER
annex O-1 to check what census they now carry.**

### OPEN-CALL 8 (shard 2) — one coincidence that may or may not be one

`.46` records PE6's leg as "**566 junctions incl. 560 off-roster**", leaving **6
on-roster** — and **6** is the number of above-twist junction-levels that remain OPEN
(`.55`). The note does not say whether PE6's 6 on-roster junctions are those 6. If they
are, PE6's clean pass covered exactly the live region of the open box, which would be
worth recording; if not, the coincidence is noise. **Decision needed: whether the merge
run reads `GRTW2_passPE6_report.md` to settle it.** No inference was made.

### OPEN-CALL 9 (shard 1) — the note's open-box COUNT is stated as unchanged through four
rounds, and it did change out of range

`.40` says "open boxes unchanged in count" at r2, r3 and r4 ✓ true in range (four surfaces
throughout). **Out of range the set moves**: (OPEN-2a) leaves it (proved), and
W2-OPEN-2(a)–(b) narrows to six junction-levels. **Neither is folded back into the
dependency line.** **Decision needed: whether the merged spec re-states the open-surface
count at HEAD** (this shard's reading: three open surfaces plus one review-owed fence —
W2-OPEN-1, W2-OPEN-2(a)–(b), W2-BOX-1, §4.3 — with (OPEN-2a) retired).

### OPEN-CALL 10 (shard 1) — the machine bracket's headline total does not reconcile with
its own table

`.37`'s sample column sums to **6,396**; the headline at `.37` itself and the four Freeze
paragraphs (`.03`, `.42`, `.43`, `.44`) all say **6,403**. The family count (17) reproduces
exactly. **The 7-sample gap is not closable from the note.** **Decision needed: whether
the merged spec reports 6,403 (the note's figure, re-verified by hostile passes against
the frozen artifacts at every round) or flags the table.** **This merge reports both and
flags the gap — see §5.2's MQ-candidate flag, and source defect 4 below, which this call
and that flag both point at.**

### OPEN-CALL 11 (shard 2) — the Σ-LAW figures were wrong twice, and the note's other
quoted machine figures were not re-audited

`.50`'s figures were corrected at `.51` (tooth-run leakage) and `.51`'s were corrected at
`.52` (transposition) — **two errors in quoted machine figures inside three consecutive
annexes**, both found by hostile passes on the *supplier* note rather than on this one.
**This compiler independently verified that only `.52`'s assignment satisfies every
displayed relation** (the two doubling identities and the 340-gap-slot clause). **Decision
needed: whether the other machine figures quoted in this range — PE4's 33,408 / 4,173 /
29,223, PE6's 566/560, OPEN2ATTACK's 468/24/470/16/604, SIGMALAW's 1,211/539/218 — warrant
the same recount.** **None of them has a displayed internal relation this compiler could
check** (unlike the Σ-LAW's doubling identities), so none was verifiable here.

### Recorded source defects (flagged, not silently repaired; 13 raw from the two shards,
one dedup'd — the runner-hash truncation, split across both shards' ranges by occurrence
— = 12 distinct)

1. **`.09`/`.33`/`.57`:** the P-index dictionary was misapplied **twice in the same box**
   — caught at r2 (P3, the premise, `.33`) and again at E5 finding 3 (`.57`, the Equivalent
   sufficient form), four months apart.
2. **`.29`/`.58`:** W2-C3(iii) claimed "same induced valuation data" while the note's
   **own route (3)** (`.34`) proves equal augmented valuations are unavailable. E5 finding
   4's opening sentence: "The note itself proves that equality of augmented valuation
   functions is unavailable."
3. **`.32`:** the roster-invisibility argument's `g = 2` half ("no support-stabilizing
   unit **with zero constant coefficient**") is stated too tersely to check from the
   displayed text. PE4's exhaustive map (`.44`) supplies the fact by measurement instead.
4. **`.37`:** the machine-bracket table's sample column sums to **6,396**, not the
   headline **6,403** — a 7-sample gap with no decomposition in the note (family count 17
   ✓ reproduces). **Flagged as an MQ-candidate at §5.2; the two entries cross-reference
   each other.**
5. **`.40`:** "open boxes unchanged in count" is true through the in-range arc and stale
   at HEAD (OPEN-CALL 9).
6. **`.03`/`.37`/`.41`–`.44` (dedup'd across both shards):** the runner **sha256 is
   truncated at all five of its occurrences across the whole note** — four in shard 1's
   range (`.03`, `.37`, `.41`, `.42`/`.43` collectively confirm the same truncated prefix)
   and the fifth and last in shard 2's range (`.44`) — the note's most-verified object
   (four independent byte-identity passes plus a fifth freeze restatement) never carries a
   full hash. Shard 1 and shard 2 each recorded this independently for their own range;
   this merge consolidates the two into one defect rather than double-counting it.
7. **`.37`:** the sealed docstring preregisters "TW-PARI PREDICT: 24/24" against a
   12-sample family — **disclosed** by the note as a seal miscount, not hidden.
8. **`.45`:** the footer dateline reads chronologically backwards (campaign date
   2026-08-08 before rounds dated 2026-08-06/07) and stops at r4, omitting the acceptance,
   five annexes and the sol append.
9. **`.48`:** both executed fold annotations quote the **38/44** census, which `.56` has
   since re-displayed as **37 + 1 + 6**; neither target has been re-annotated
   (OPEN-CALL 7).
10. **`.53`:** ANNEX #3's final sentence contradicts the Direction line of the annex
    **two lines above it** (`.50`: "W2-OPEN-2's above-r₀ chain claims are unchanged"). The
    orchestrator's own verification at `.60` notes the same thing.
11. **`.50`→`.51`→`.52`:** quoted machine figures wrong twice in three consecutive
    annexes; only the third assignment satisfies every displayed relation.
12. **`.46`:** the acceptance enumeration lists "W2-C1 (chamber-qualified)" and the 38/44
    census, both of which are stale at HEAD; the acceptance record is frozen and correctly
    so, but a chapter cut reading it alone would carry two superseded items.

### Fidelity audit

- Every CANONICAL STATEMENT across all 60 units is a verbatim source quotation; **no
  `[ASSEMBLED]` statements in either shard.** **No inverse, sign, quantifier, index,
  level, inequality direction, or implication direction was altered anywhere**, in either
  the original shard compilations or this merge's renumbering pass — which matters
  unusually here, since the arc contains a sign flip and its revert (`.13`/`.26`), and
  both are quoted with their strike markers intact.
- Every source table is marked `[TABLE]` (`.37`, `.38`); `.38` carries one clearly-labelled
  compiler-added "TERMINAL grade at HEAD" column, preserved as such; the certifier
  corrections' LaTeX (`.55`–`.58`) is reproduced as the source bytes, including the
  `\boxed{}` at `.57`. No source table was prosified at merge time.
- **21 distinct external XREF/artifact targets** (from 25 raw citations, 4 clean DEDUPs
  plus one granularity mismatch and one partial overlap, both flagged rather than forced
  — §4) have fixed-string counts ≥ 1 or verified presence, with **zero mismatches found**
  (unlike `spec/EFF-HE3.md`'s merge, which found a genuine count error). A 10-target sample
  was re-grepped/re-checked at merge time against the working tree (§4) — 10/10 matched. A
  5-quote sample was re-checked verbatim against the source note by line number and
  matched byte-exact (§4). **24 distinct commit hashes** were independently re-confirmed
  real commits via `git cat-file -t` (24/24 → commit).
- **The ID-renumbering rewrite was performed unit by unit against this compiler's own
  reading of both shards' full text** (not a blind global substitution), tracking the
  header's own disambiguation rule (a bare `.NN` defaults to its own shard; an explicit
  "shard 1"/"shard 2" label overrides it until the next `·`/`;` field-separator or a
  competing label). An exhaustive regex sweep confirms **zero leftover `sKof2` substrings
  within the merged statement inventory (§3)** — the eight occurrences surviving in this
  header (§1) are deliberate quotations of the original shard-local notation illustrating
  the rewrite rule itself, plus the one deliberately-untouched `spec/EFF-GENHN-s2of2.md`
  foreign citation inside `.56` — and **zero out-of-range renumbered IDs** (every resolved
  `` `.NN` `` token lies in 1–60, confirmed by an explicit scan).
- The SERIES (§7.1) is assembled from all seven of its links with no duplication and no
  gap, cross-checked against four independent internal descriptions (`.02`'s own table,
  `.03`'s heading, `.44`'s heading, `.46`'s heading). Its TERMINAL (**2/2, ACCEPTED**) is
  uncontested — no eighth link exists anywhere in the merged inventory. **GRTW2 reaches
  2/2; the sibling HE3 merge's SERIES does not, and the two are not conflated anywhere in
  this file.**
- Absorption status (predicate A), the append/consumption protocol (predicate B —
  "accepted texts are NEVER edited by this unit", stated in the note's own words twice and
  never contradicted), and the inbound-corrections predicate (predicate C, six streams)
  are kept distinct everywhere below, matching both source shards' own discipline.
- **Eleven cross-shard supersession edges are consolidated (§7.2), with one compiler
  finding recorded rather than silently reconciled**: this merge's own audit of explicit
  `CHAIN:` fields inside shard 2's units finds five chains, against the shard's own
  self-tally of "CHAIN ×4."
- **Eleven raw OPEN-CALLs carry forward as eleven distinct** — no self-flagged duplicate
  pair exists between the two shards (checked by grep, §8 preamble); two substantively-
  close pairs (OPEN-CALLs 1/2 and 3/4) are flagged as related but not merged, matching the
  charge's instruction to dedup only self-flagged pairs.
- **The §6.1 sample-column discrepancy (6,396 vs the headline 6,403) is carried in two
  places by design** — as an explicit MQ-candidate supplier-finding in §5.2, and as source
  defect 4 above — each pointing at the other, per the specific charge this merge run was
  given. **This merge run does not itself add an entry to `spec/HYPOTHESIS_LEDGER.md`'s
  MAINTENANCE QUEUE** — that remains an orchestrator action, out of this deliverable's
  scope.
- **Honest limitation of this merge, stated once:** the boundary-by-boundary reasoning in
  each shard's own §6 (which unit-boundary candidate was chosen and why, and each shard's
  own two v2/v3-gap proposals — a `consumer-pin freeze`-style fourth freeze predicate was
  NOT proposed here, but the `acceptance-scope enumeration` freeze predicate (F3) WAS,
  independently, by shard 1's §6.3, and shard 2's `.59` supplies its worked corpus
  instance) is not reproduced here in full — only its format-level conclusions (the
  SERIES construct, the SUPERSESSION KIND vocabulary, the acceptance-scope-enumeration
  proposal) survive here. A reader who needs the per-boundary reasoning for a specific
  unit should consult that unit's home shard file directly (`spec/EFF-GRTW2-s1of2.md` for
  `.01`–`.43`, `spec/EFF-GRTW2-s2of2.md` for `.44`–`.60`); the shard files are retained for
  exactly this purpose (§1). **Codex cross-read remains owed** (header, PROJECT_STATE
  #51) — this merge performed the fold, the fresh-verification pass, and the arithmetic
  audits, not the adversarial read.

---

EFF-GRTW2 MERGED: 60 statements / 21 xrefs / 11 open calls
