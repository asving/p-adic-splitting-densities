# EFF-W12 — CANONICAL EFFECTIVE-SPECIFICATION (MERGED)

**COMPILED-BY: opus (2026-08-14, Asvin-authorized substitution). CODEX CROSS-READ OWED (post-reset) — neither shard, and no fold performed by this merge run, has been through an adversarial pass; that obligation is inherited whole.**

## 1. Merge header

**Source note:** `lean/notes/openmath/W12_PROOF_2026-08-08.md` (2453 lines) — the project's central REDUCTION spine (THEOREM W-12.D).

**HEAD blob hash:** `9fbd5f9ddc5b60297a392f67ddc86cb29a516076` — cited identically by both
source shards' headers, and independently confirmed by fresh `git hash-object` against
the working-tree file at merge time (2026-08-14):

```
$ git hash-object lean/notes/openmath/W12_PROOF_2026-08-08.md
9fbd5f9ddc5b60297a392f67ddc86cb29a516076
```

**No divergence found — this was the merge run's STOP condition and it did not trigger.**
Both shards additionally record the file's last-touching commit as `06958241`, confirmed
against `git log -1 --format=%H -- lean/notes/openmath/W12_PROOF_2026-08-08.md` =
`069582416af042563a3f3bf94dd36e147bc4ca5d` (the shards' 8-hex-digit form is a prefix of
this, matching).

**Compilation context:** `spec/EFF_TEMPLATE_v2.md` AT HEAD (rules 1–39; this is a
MERGE-STAGE run, rules 37–39 mandatory).

**Merged from:** `spec/EFF-W12-s1of2.md` (HOME source lines 1–1271; 52 statements, 36
xrefs verified, 3 open calls — plus a dated AMENDMENT appended 2026-08-14, see below),
`spec/EFF-W12-s2of2.md` (HOME source lines 1272–2453; 36 statements, 19 xrefs verified, 3
open calls). **88 statements, 55 raw XREF/artifact citations, 6 raw open calls total
before merge-time dedup.** This file supersedes the two shards as the citable unit for
all downstream consumption; any consumer citing `EFF.W12.*` from this point on cites the
contiguous IDs below, not the shard-local `EFF.W12.sKof2.*` IDs. The two shard files are
**not deleted** — they remain the run-of-record trace of the sharded compilation, and in
particular remain the place where each unit's own §6 BOUNDARY SELF-AUDIT entry (which
unit-boundary candidate was chosen and why) lives in full; this merged file's own boundary
section (§7) carries forward only the cross-shard edge list and the format-level
conclusions, not the individual boundary arguments each shard records for its own range.

### Rule-39 self-count check (fresh recount against each shard's own closing tally)

Both shards' own closing lines were recounted fresh against a literal `grep -c` of every
`### EFF.W12.sKof2.NN` header:

```
$ grep -c '^### EFF.W12.s1of2\.' spec/EFF-W12-s1of2.md   → 52
$ grep -c '^### EFF.W12.s2of2\.' spec/EFF-W12-s2of2.md   → 36
```

Shard 1's own closing line reads "EFF-W12-s1of2 COMPILED: 52 statements / 36 xrefs
verified / 3 open calls" and shard 2's reads "EFF-W12-s2of2 COMPILED: 36 statements / 19
xrefs verified / 3 open calls" — **both figures match the fresh recount exactly; no
discrepancy to book.** (Contrast `spec/EFF-LIFTCORNER.md`'s merge, which found a shard
asserting "fifteen" against a literal 20 — that shape of defect is absent here for the
statement tallies. Two *different*, smaller citation defects were found instead — see the
SHARD-MAP audit below and the "recorded source defects" list in §8.)

### SHARD-MAP (old shard-local ID → new contiguous ID)

Shard 1's offset is **0** (its own numbering, 01–52, is already contiguous from 1).
Shard 2 carries a **+52** offset (01–36 → 53–88). Every `EFF.W12.sKof2.NN` full-form
occurrence and every bare `` `.NN` `` shorthand has been rewritten below to the new
contiguous ID, under the disambiguation rule recovered from the shards' own citation
discipline (the same rule the GRTW2/LIFTCORNER merges used):

> **A bare `` `.NN` `` reference defaults to its OWN shard's unit** (the shard the
> surrounding text lives in). **This default is overridden only where the text itself
> names the other shard** — a `shard 1`/`shard 2` label, in either word order — **and
> that override persists across a comma- or slash-separated list of `.NN` tokens within
> the same still-labeled clause, resetting at the next `·`/`;`/`.` field-separator or at
> an explicit competing label.**

**This note's citation traffic is strictly one-directional and unusually clean, simpler
than either precedent.** An exhaustive `grep -n "shard 1"` / `grep -n "shard 2"` sweep of
both shard files (reproduced in full below) establishes two facts before any rewriting
was attempted:

**(a) Shard 1 never cites shard-2-homed material by a bare `.NN` at all.** It has 28
occurrences of the string "shard 2" in its own text, and **every single one** names
shard-2 content by NAME — `LEMMA W12-HT`, `ANNEX 2`, `the BOX-3 ANNEX`, `` [r4] F3 ``,
`` [r5] MINOR 3 ``, `§S7/§S10` — never by a shard-2 unit's bare `.NN` ID. (The one
apparent exception, "each item's content is at its named site (`` `.38`/`.40` `` for F1,
**shard 2** for F3, `` `.51` `` for m1, `` `.27` `` for m2, `` `.08` `` for R-1)" at
shard 1 `.20`, in fact confirms the rule: "shard 2 for F3" carries no trailing `.NN` at
all — F3's content is named by location, not by a shard-2 ID.) **Consequently every bare
`.NN` inside shard 1's own text resolves to a shard-1-homed unit and needs no offset —
verified by an exhaustive scan of every bare-ref numeral in shard 1 (01–52, all in
range, all shard-1's own).**

**(b) Shard 2 cites shard-1-homed material by bare `.NN` at ten distinct lines, and labels
every one of them "shard 1".** The definitive-mapping audit table (rule 38), built by
reading all 19 "shard 1" occurrences in shard 2's full text (`grep -c "shard 1"
spec/EFF-W12-s2of2.md` = 19, re-verified fresh at merge time) and extracting every one
that sits beside a bare `.NN` token:

| Shard-2 line | Quoted context | Protected token(s) | Label form |
|---:|---|---|---|
| 303 | "carry per-degree conditionality (shard 1 `.45`)" | `.45` | "shard 1" precedes |
| 419 | "discharges shard 1's W12-BOX-3 and one of the two n = 3 legs of shard 1's `.45`" | `.45` | "shard 1's" precedes |
| 437 | "the two node-species transfer laws that shard 1's `.37` named as missing" | `.37` | "shard 1's" precedes |
| 439 | "discharges shard 1's W12-BOX-2 and the second n = 3 leg of `.45`" | `.45` | label persists across "and" within the one clause (resets at the following full stop — the next sentence's unlabelled `` `.20` `` is NOT protected, see below) |
| 631 | "applies to shard 1's W-12.A (`.09`(a)) and is re-derived as κ₀(T) inside LEMMA W12-HT (`.31`, `.34`)" | `.09` | "shard 1's" precedes; label resets at "and" before the new referent LEMMA W12-HT, so `.31`/`.34` are NOT protected (own-shard, shard 2) |
| 655 | "applies to shard 1's `.12` (A1), `.42` (Step 1) and `.44` (the n = 2 instance's admissibility)" | `.12`, `.42`, `.44` | "shard 1's" governs the whole comma/`and`-list |
| 679 | "applies to shard 1's `.49`" | `.49` | "shard 1's" precedes |
| 738 | "the effective statement of THEOREM W-12.A (shard 1 `.09`)" | `.09` | "shard 1" precedes |
| 761 | "the digit count of `.23`/`.24` (shard 1) re-run at a node" | `.23`, `.24` | label FOLLOWS the slash-list (inverted position, resolved the same way LIFTCORNER's merge resolved its one inverted instance: the label still governs the numbers it sits beside) |
| 830 | "makes shard 1's `.09`, `.14` effective at full order-1 coverage" | `.09`, `.14` | "shard 1's" governs the comma-list |

**Ten lines, fourteen protected tokens** (`.45`×3, `.37`×1, `.09`×3, `.12`/`.42`/`.44`×1
each, `.49`×1, `.23`/`.24`×1 each, `.14`×1). All fourteen are shard-1's own numbers and
are **left unchanged** by this merge (shard 1's offset is 0). Every other bare `.NN` in
shard 2 — including the ones sharing lines 439, 631 and 830 with a protected token, once
the label's scope has reset — is shard 2's own unit and **gains the `+52` offset**.

**Two anomalies found and resolved by content, not by the label rule (flagged, not
silently smoothed — rule 39's spirit extended to citation targets):**

1. **Shard 2 `.10`'s own RESOLUTION TRACE** ("consumer 2 amended at the discharge's
   consumer sweep (`` `.43` ``)") **cites `.43`, which is out of range under EITHER
   shard's numbering as a live target**: shard 2's own temporary numbering runs only
   01–36 (`.43` was never a valid shard-2 ID), and shard 1's own `.43` (§S3.4 Steps 2–4,
   the classical tie) has no content connection to a "consumer sweep." Content match is
   unambiguous: the unit literally titled "LEMMA W12-HT — **consumer sweep**,
   restoration of W-12.A, and the discharge conclusion" is shard 2's own `.35`. **Resolved
   as shard 2's own `.35` → merged `.87`**, recorded as a source citation defect (§8).
2. **Shard 2 `.35`'s own RESOLUTION TRACE** reciprocally reads "it amends shard 1's
   `` `.10` ``-adjacent Phase-B consumer spec (`` `.10` `` here)" — but shard 1's own
   `.10` is CONJECTURE W-12.B (DRAIN-n), which has no "Phase-B consumer spec" content at
   all; the unit actually titled "§S8 — CONSUMERS," whose item 2 is literally "**Phase-B
   omMenu growth**," is shard 2's own `.10`. The "shard 1's" label is a drafting slip;
   confirmed by the reciprocal pointer above (shard 2's `.10` cites "the discharge's
   consumer sweep" back at what is really shard 2's own `.35`). **Resolved as shard 2's
   own `.10` → merged `.62`**, recorded as a source citation defect (§8). Both anomalies
   are two ends of the SAME stale internal cross-reference pair (`.10` ↔ `.35`,
   miscited in both directions by different amounts/mislabels) — booked together below.

**Rule 37 (foreign-note citation guard): zero live instances to protect.** An exhaustive
sweep for `EFF\.(HMENU3|GENIND|HEX3|GENH4|GENHN|GRTJB|GRTJC|W11|W10|JD0|DULEMMA|
WELDMASTER|GRTW2)` and for `spec/EFF-` patterns across both shards returns **no hits other
than the two shards' own mutual companion-file references** (each shard names the other's
file path in its own header prose). Unlike GRTW2 (which cited `spec/EFF-GENHN-s2of2.md`'s
own numbering once) or LIFTCORNER, **W12 cites every one of its supplier notes —
HMENU3, GENIND, HEX3, GENH4, GENHN, W-11, W-10, J-D0, GRTJB, GRTJC, GRTW2, DULEMMA,
WELDMASTER — exclusively by their own THEOREM/LEMMA/COROLLARY/BOX designations (verified
by grep, §4), never by another EFF spec's shard-local `.NN` numbering.** Rule 37 therefore
has nothing to protect in this note; recorded as a finding, not assumed.

**Audit after rewriting: exhaustive regex sweep for leftover shard-local substrings and
out-of-range IDs.** `grep -n 's1of2\.[0-9]\|s2of2\.[0-9]'` across the merged inventory
(§3) returns **zero** hits (the only surviving `s1of2`/`s2of2` substrings anywhere in this
file are the deliberate quotations inside this §1 header, illustrating the shards' own
temporary-ID convention and this SHARD-MAP's own audit table). Every resolved bare `.NN`
in the merged inventory lies in **1–88**; the two anomalies resolve to `.87` and `.62`
respectively, both in range. **Zero out-of-range renumbered IDs.**

### Header unification and blob-hash check

Both shards' front matter carries the **identical** compiled-by/cross-read-owed stamp
(reproduced verbatim above) and the identical HEAD blob hash; both independently record
the file's last-touching commit (`06958241`) — confirmed by this merge against the
working tree rather than trusting the shards' mutual citation alone.

### Governing effective-text record (unified from both shards)

**FREEZE PREDICATES (rule 21 — TWO):**

**(F1) TEXT-FREEZE at acceptance**, homed in shard 2 (`.76`). Line 1956 (PE7 re-anchor):

> "Provenance: passPE7 (report `W12_passPE7_report.md`, verdict commit fa3acb2: **CLEAN,
> 0C + 0G + 1 MINOR — the 2-clean counter COMPLETES 1/2 → 2/2; W-12 IS ACCEPTED, the note
> FROZEN, dated appends only**)."

reinforced at line 2009: "Everything above this heading is byte-untouched by this
append." **Before acceptance the five in-range brackets `[r1]`–`[r5]` were applied IN
PLACE** inside shard 1's HOME range — each is a NOTE-ONLY repair round, not an append.

**(F2) INSTRUMENT-FREEZE — the runner and both artifacts, byte-frozen from the seal
commit and re-verified at every round.** "runner + artifacts byte-frozen at seal
f669cb0" (repeated identically at every round block and at the acceptance record).
**Verified FIVE separate times** by five independent GREEN re-runs across the arc
(`.65`'s VERDICT plus four re-runs recorded inside the `[r3]`/`[r4]`/`[r5]` ARC unit
`.74`), each at seal-intact md5 — one of the most heavily re-verified instrument freezes
in this campaign.

**EFFECTIVE TEXT = the whole 2,453-line file exactly as written** — `[r1]`–`[r5]`
already landed in place in shard 1's range (struck text is REFUTED text preserved for
the record, never current), READ AS CORRECTED by every later dated annex/correction/
append that names an earlier sentence, with no earlier sentence ever deleted, **PLUS the
2026-08-14 dated AMENDMENT appended to shard 1 itself** (see the dedicated treatment
below and in §3/§5/§8). Two mechanisms land corrections from shard 2's range onto
shard-1-homed units: **two verbatim annexes** (HEX3 → BOX-3 discharge; HMENU3 → BOX-2
discharge), and **four 2026-08-12 dated sol-certification corrections** (κ(T); the
history-transfer obstruction + its LEMMA W12-HT discharge; the (A1) rationality clause;
BOX-1's dependency range) — all four tabulated with SUPERSESSION KIND in §7.

### Scope of record — mandatory THREE-predicate split (unified from both shards)

**A. ABSORPTION / mathematical supply SET.** THEOREM W-12.A (order-1 shape-generic count
law, PROVED at all degrees via LEMMA W12-HT at full coverage), CONJECTURE W-12.B
(DRAIN-n, stated precisely, open in general), THEOREM W-12.C (n = 3 partial, exact DBL
term + both bounds PROVED), THEOREM W-12.D (THE REDUCTION THEOREM, PROVED unconditionally
as a reduction, firing unconditionally at n = 2). Supporting: LEMMA W12-L0, LEMMA W12-L1,
LEMMA W12-HT (the discharge), the seven depth-0 TRP families, the QRT g = 2 families, six
named honest boxes (`[W12-H]`/W12-BOX-1 through BOX-8, consolidated at `.49`–`.52`). Shard
2 adds: the sealed battery (3,232,506 checks GREEN), the acceptance record (ACCEPTED
2/2), two received annexes discharging BOX-2/BOX-3 at composition grade, and the four
dated corrections above.

**B. APPEND / consumption PROTOCOL scope — what W12 lands on other notes.** **Two
annexes received and landed** (from HEX3, from HMENU3); **two further corrections named
as owed by W12's own shards, BOTH of which this merge finds are already stale readings**
— the HMENU3 quantifier correction, per the 2026-08-14 AMENDMENT (landed at HMENU3's own
ANNEX A, commit `19c02857`, refined by ANNEX B/C at commit `d665620b`); and a second,
smaller HEX3 L80–81 phrasing companion, which **this merge independently re-verified is
ALSO already landed** — not by a dated append, but **in-place, at HEX3's own `[r4]`
repair round** (`lean/notes/openmath/HEX3_PROOF_2026-08-08.md` lines 80–95: the sealed
clause now reads "Ore applies to every disc ≠ 0 lift — W-12 S2.3, post-[r4] form", with
a `[r4, PE5 m1: …]` bracket recording the very fix W12's own sweep called "owed"), frozen
in place by HEX3's own subsequent ACCEPTANCE (2/2, dated 2026-08-09: "Everything above
this heading … is byte-untouched by this append"). **Zero dated consumption appends are
claimed landed by W12 on any OTHER supplier's own frozen text** (W12 receives
corrections and annexes; it does not itself edit accepted supplier notes) — both
"corrections owed outward" were, in fact, self-applied by their own supplier notes,
independently of W12.

**C. INBOUND CORRECTIONS RECEIVED — consolidated from both shards' predicate-C
material.** Two verbatim annexes (HEX3, HMENU3) plus four 2026-08-12 sol-certification
corrections, all landing inside shard 1's HOME range, all physically drafted/homed in
shard 2's range (rule 7: HOME follows an edit's *destination*, not its drafting
location). This is the class tabulated in §7's cross-shard edge table.

### Resolution rules applied (merged; each shard's own numbered rule-list is a
restriction of this one to its HOME range — nothing below is dropped, only consolidated)

1. Shard 1's lines 1–1271 supply the base statements; `[r1]`–`[r5]` tags are
   already-landed base text; struck spans are refuted-but-preserved and are reproduced
   with their strike markers intact wherever load-bearing.
2. The acceptance record (shard 2, `.76`) governs status for the WHOLE note: every
   in-range "attempt 0/2 / counter 0/2 / PEn next" sentence anywhere in either shard is
   historical, superseded by **ACCEPTED 2/2, FROZEN, dated appends only**.
3. Four 2026-08-12 dated items (all homed in shard 2) land on shard-1-homed units and
   are applied there: κ(T) → `.09`; the history-transfer obstruction's discharge
   `(HT-global)` → `.09`/`.14`'s controlling formula and coverage claim (LEMMA W12-HT
   amends `.62`'s Phase-B transcription spec, resolving the `.10`/`.35` anomaly above);
   the (A1) rationality clause → `.12`/`.42`/`.44`; BOX-1's dependency range → `.49`.
4. Two verbatim annexes (BOX-3 from HEX3, BOX-2 from HMENU3, both homed in shard 2)
   discharge shard-1-homed `.50` and the two n = 3 legs of `.45`, at composition grade
   (neither supplier's own hostile arc had begun at the append).
5. **HOME is determined by an edit's destination, not physical drafting location** — the
   same rule the GRTW2/HE7/HE3/T1/LIFTCORNER merges used. All six correction mechanisms
   above (rules 3's four plus rule 4's two annexes) are physically drafted in shard 2's
   range; §7 verifies each resolves to exactly one place in the merged inventory.
6. Every cited commit hash was spot-verified with `git cat-file -t`; truncated hashes
   (the runner's sha256, always shown as a prefix) are marked accordingly where the
   shards themselves flag it.
7. **The 2026-08-14 dated AMENDMENT (appended to shard 1, tail of the merged inventory)
   is applied per the repo's living-artifact convention: it edits nothing in place.** It
   supersedes, WITHOUT editing, three sites' append/consumption-PROTOCOL reading (never
   their mathematical content) — see the dedicated treatment in §3 (tail unit), §5, and
   §8. This merge's own freshly-assembled §5 ledger and §8 OPEN-CALL status report the
   AMENDMENT's corrected reading, since a freshly-built consolidated summary is not "the
   original compiled text" the living-artifact convention protects — exactly as the
   AMENDMENT's own closing paragraph instructs.

### Quotation and table discipline

Unchanged from both shards: CANONICAL STATEMENTs are verbatim source quotations (no
`[ASSEMBLED]` statements in either shard); strike-through and nested brackets are
reproduced exactly; truncations marked `…`; every statement unit carries `FORM:`. Source
tables (`.18` FIRING CHECK, `.25` universal censuses, `.28` seven TRP families, `.58` row
inventory, `.73` m2 blast-radius sweep) are transcribed per rule 5/14 and flagged
`[TABLE]`. Compiler-authored ledgers (XREF tables, consumption ledgers, TEETH inverse
tables, the SERIES/edge tables of §7) are marked `[TABLE — compiler ledger]` and are not
source statement units.

---

## 2. NON-IMPORTS (consolidated from both shards; dedup marked)

`[TABLE — compiler ledger, consolidated from shard 1 §4 (17 rows) and shard 2 §4 (13
rows) = 30 raw rows, 0 dedup pairs found → 30 distinct rows below]`

**Dedup count for this section: 0.** As with the GRTW2/HE3/GENHN merges, no fence in
either W12 shard restates a near-identical negative claim already stated by the other
shard — shard 1's fences are about the base proof's own scope boundaries (order-≥ 2
count laws, the general W-10 box, the rejected σ-parse, the deleted witnesses), shard 2's
are about the battery's evidence classing, the annexes' byte-freeze, and the discharge's
own consumption fence. Every row below is specific to its own shard and asserted once.

| Fence | Explicit material NOT imported, NOT proved, or NOT claimed | Source |
|---|---|---|
| Prior drafts | The four dead composer sessions' partials are "UNTRUSTED scaffolding", archived outside the repo; every kept statement re-derived. | s1 `.02` |
| Orders ≥ 2 | "No order-≥ 2 count law is CLAIMED here; [W12-H] is the priced route." The `λ = (1²)` quartic row has a proved volume law and an OPEN σ-resolution. | s1 `.49`, `.50` |
| General W-10 | "The general W-10 (every decided shape, every order) remains OPEN — W10-BOX-1 stands untouched." | s1 `.49` |
| Refinement families at n ≥ 3 | "The depth-≥ 1 TRP families are not enumerated … neither species' transfer law is derived." | s1 `.50` |
| Exact `U₃^TRP` | "The exact triple-center drainage law is not derived … EXPLORATORY grade, no closed form preregistered." | s1 `.50` |
| n ≥ 4 drainage | "No upper bound at any grade; lower bounds only." | s1 `.50` |
| Read-anchored σ | The read-anchored parse of σ-DECIDED is REJECTED (it makes W-12.B false at n = 3). | s1 `.16` |
| Unrestricted lift quantifier | S2.3's "in fact every lift" is STRUCK: FALSE in equal characteristic at wild decided shapes. | s1 `.27` |
| `B = 0` witnesses | The sealed `B = 0` branches of S3.2 are DELETED as inseparable in equal characteristic 2 resp. 3. | s1 `.40` |
| Lift convention | "Lift-convention independence of the member SET at deep shapes is the W-2/LIFTCORNER seam, not consumed." | s1 `.26`, `.52` |
| DULEMMA | "NOT consumed by any count law here … it appears only in this weld-state display." | s1 `.48` |
| Weld notes in §§S2–S3 | "consumed ONLY in §S5's composition display and as [W12-H]'s named inputs; NO S2/S3 proof depends on them." | s1 `.48` |
| IFK faces | "consumed DOWNSTREAM, owned by their own units, nothing of them owned here." | s1 `.48` |
| Value layer | Clause (i) carries "NO value-layer hypothesis ((VD-m), (C-coll), (R-coll), (DMULT-s), PERIM-μ all absent, J-D0 frame)". | s1 `.09` |
| FE / symmetry | "Nothing here touches `htameFE`; the n = 2 split = inert window symmetry is not asserted at n ≥ 3." | s1 `.52` |
| Lean | "no Lean is changed by this unit." | s1 `.52`; s2 `.63` |
| Oracle coverage | "PARI legs are mixed-characteristic only … no mixed-characteristic prime-power rows exist in the frozen kit." | s1 `.52` |
| Evidence classing | Only W12-ORACLE is IND; every other family is SAME (this runner's own arithmetic) or NONE (bookkeeping). | s2 `.53` |
| `U₃^TRP` (battery) | "reported per row, NO preregistered value (EXPLORATORY … recorded raw)"; and post-`[r4]` F3, "W-12.B has no n = 3 corroboration here either way". | s2 `.67` |
| The struck P-6 inference | The `≈ ×q²` order claim is FALSE for the measured quantity and, post-pin, not W-12.B's quantity at all. | s2 `.67` |
| Oracle genres | Genres (ii) and (iii) of the disc = 0 disposition "ride the convention, not the cited pair". | s2 `.56` |
| Witness pairs | 15 of the 85 are the sealed `B = 0` pair deleted from the proof — "not evidence for the repaired (B = π^N) pair". | s2 `.56` |
| Machine evidence vs proofs | "nothing here can strengthen or weaken a proof" — the battery confirms (A1)-SHAPE data, not the theorems. | s2 `.69` |
| Annex texts | Both annexes "UNTOUCHED and stay verbatim as applied"; the `[r5]` NOTICE is "a notice about its supplier, not an edit to it". | s2 `.70`, `.71`, `.72` |
| Repair rounds | Every round is "note-only … runner + artifacts byte-frozen at seal f669cb0"; no sealed re-run. | s2 `.74` |
| PE6/PE7 records | Both are "dated record, not an edit"; the record above each "stands as written". | s2 `.75`, `.76` |
| LEMMA W12-HT | "No order-≥2 leaf theorem or open μ≥3 assertion is consumed"; from GENIND-1 "only fracture permanence is used". | s2 `.83` |
| Boxes after the discharge | "[W12-H], W12-BOX-1's inputs (H-a)–(H-e), W-12.B, and the tail problems are unchanged." | s2 `.87` |
| Certificate status | The certificate "corroborate[s] the local normalizations and side-local orbit convention; the proof above supplies the all-degree warrant" — on `n ∈ {3,4}`, `q ∈ {2,3}`, `N ≤ 6` only. | s2 `.87` |
| Obstruction repair route | "Narrowing W-12.A to depth-zero shapes would weaken an accepted theorem statement and is therefore not an admissible repair." | s2 `.78` |

---

## 3. Statement inventory (88 units, contiguous, in source order)

### EFF.W12.01  [changes-record]

**CANONICAL STATEMENT:** Title line and unit header

> “# W12 — THE GENERAL-n ASSEMBLY (the J-D block's terminal rung): the order-1 shape-generic count law PROVED at ALL degrees (THEOREM W-12.A), the general drainage law stated precisely with the n = 3 double-root term EXACT (THEOREM W-12.C partial; CONJECTURE W-12.B), and THE REDUCTION THEOREM (THEOREM W-12.D, PROVED): exact menu laws + drainage ⟹ ONE R_τ ∈ ℚ(q) per splitting type at every prime power, both characteristics, wild included — conditional structure displayed the way `montes_unconditional` displays its hypotheses”

> “**Unit:** W-12, the J-D block's terminal rung after THEOREM W-11(n = 2) (GRT_WELD_BLUEPRINT_2026-08-08 §S3.1 row W-12; execution-order step (8); WELD_SYNTHESIS_2026-08-05 §4(ii)). **Attempt grade 0/2** (**[r5, PE5 m2: the display that followed was the [r1]-era arc — SUPERSEDED; the CURRENT arc is the [r5] ARC at the end of this note, marked the same way as the [r1] and [r3] displays]** ~~arc: composed → PE1 NOT CLEAN 1C+3G+2m @ 2b47711 → r1 THIS REPAIR, note-only, [r1] tags, minimality contract — F1 (CRITICAL, W-12.A display) + F2/F3/F4 + m1/m2 repaired in place; counter 0/2; PE2 next~~).”

> “Per the effort directive (Asvin 2026-08-05) W-12 IS the complete-theorem target of the block: composed at the strength actually proved, honest boxes over reach, every supplier pinned as-of.”

**CONDITIONALITY:** “Attempt grade 0/2” is historical, superseded by the acceptance record (ACCEPTED 2/2, resolution rule 3). The struck arc display is not effective text; the `[r5]` ARC (shard 2) is the current one.

**DERIVATION:** Header record, no derivation.

**RESOLUTION TRACE:** Base lines 1–14; the arc display struck in place by `[r5]` PE5 m2; grade superseded at line 1956.

XREF: `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md:the faithfulness handoff (J-D1)` — grep-verified count **1** (the W-12 row itself, blueprint line 302; the string `W-12` occurs **4** times there).

XREF: `docs/in-progress/WELD_SYNTHESIS_2026-08-05.md:(ii) J-D composition plan: BLUEPRINT ROUTE` — grep-verified count **1** (the cited `§4(ii)`; note the file's `§4. RECOMMENDATION` header carries no `W-12` string — the plan names W-10/W-11).

**TEETH:** NONE (header).

---

### EFF.W12.02  [fence]

**CANONICAL STATEMENT:** Composition provenance (disclosed)

> “**Composition provenance (disclosed):** this is the FIFTH incarnation of the unit (four prior composer sessions died to API errors mid-draft; their partials are archived OUTSIDE the repo in /tmp/k2res_partial_archive/ and were treated as UNTRUSTED scaffolding — every statement kept here was re-derived from scratch in this session; the archived S7 bookkeeping totals failed re-derivation and are recomputed below; the archived drafts' own disclosed correction — a spurious (q^d−1)-per-interior-vertex factor in the census normalization of an earlier draft — was independently re-confirmed to be a necessary correction by the sweep argument of S2.2, which this session re-proved). This note was written and committed in increments (survival discipline); the SEAL commit is the one containing the final §S7 + the unrun runner.”

**CONDITIONALITY:** A provenance fence: the archived partials are declared untrusted and NOT a source; the spurious interior-vertex factor is named as a defect that the re-proof independently excludes.

**DERIVATION:** The re-confirmation named here is `.24`'s right-to-left sweep argument.

**RESOLUTION TRACE:** Base lines 15–26; untouched.

**NON-IMPORT (explicit):** the archived drafts are “UNTRUSTED scaffolding” and supply nothing.

**TEETH:** The sweep argument at `.24`, cross-checked against W-11's 2SIDED row and W-10's (2,1,1) row.

---

### EFF.W12.03  [battery-frame]

**CANONICAL STATEMENT:** Instrument summary (header)

> “**Instrument:** sealed two-commit battery `verification/openmath/w12_checks.py` (23 cubic census rows = 7,105,774 cubics covered with 2,946,008 DBL/TRP lifts read individually; 8 quartic quadruple-center stratum rows = 580,550 members; 11 history-resolved quadratic rows = 69,053 polynomials; PARI/GP independent σ-multiset oracle on 40,645 cubics + 1,516 quartics + 85 constructed species ambiguity-witness pairs; the n = 3 drainage decomposition with the DBL term as a THEOREM row and U₃^TRP measured EXPLORATORY under a disclosed conservative convention; four teeth). Verdict §S10, appended at commit 2 FROM the committed artifacts.”

**CONDITIONALITY:** Two disclosed scope limits are carried by the summary itself: `U₃^TRP` is EXPLORATORY under a conservative convention (not a σ-decidedness claim), and the oracle is PARI-based on mixed-characteristic rows only (W12-BOX-6, `.52`).

**DERIVATION:** Instrument declaration; the row inventory and verdict are homed in shard 2 (§S7/§S10).

**RESOLUTION TRACE:** Base lines 26–35. Scope of the 85 witness pairs is later narrowed by `[r5]` MINOR 3 (shard 2): 70 are the S3.2 proof's pairs, 15 are the sealed `B = 0` pair that `[r4]` deleted from the proof.

**TEETH:** This unit names the battery; its inverse table is shard 2's.

---

### EFF.W12.04  [scope-record]

**CANONICAL STATEMENT:** What W-12 is (one breath)

> “W-10 proved ONE count equality at ONE order-1 shape ((2,1,1) Eisenstein quadratics); W-11 proved the COMPLETE menu at n = 2 with the exact drainage law q^(−N). W-12 is the assembly rung the uniformity directive (Asvin 2026-08-03: ONE R_τ ∈ ℚ(q) per splitting type, all orders and all primes AT ONCE) actually needs: (i) the shape-generic count law — proved outright at the order-1 layer of EVERY degree (THEOREM W-12.A), with the orders-≥ 2 layer stated through the weld machinery as a displayed hypothesis box; (ii) the general menu-exhaustion/drainage law — stated precisely (CONJECTURE W-12.B), with W-11's q^N as the proved n = 2 instance, the n = 3 double-root stratum drained EXACTLY here (THEOREM W-12.C, via the block-transfer LEMMA W12-L1 consuming W-11's per-center law), and the triple-center residue boxed with its exact obstruction; (iii) THE REDUCTION THEOREM (W-12.D): (i) + (ii) imply one R_τ ∈ ℚ(q) per splitting type at every prime including wild — proved unconditionally AS a reduction, and it FIRES unconditionally at n = 2 (re-deriving W-11's densities through the general mechanism). The blueprint row's own J-D1 faithfulness-handoff composition display is §S5, at its own S-price.”

**CONDITIONALITY:** The clause-(i) claim “proved outright at the order-1 layer of EVERY degree” is exactly what the 2026-08-12 obstruction challenged and the W12-HT discharge restored (resolution rule 4).

**DERIVATION:** Orientation paragraph; derivations are §§S2–S3.

**RESOLUTION TRACE:** Base lines 37–54.

XREF: `lean/notes/openmath/W11_PROOF_2026-08-08.md:THEOREM W-11` — grep-verified count **3**.

XREF: `lean/notes/openmath/W10_PROOF_2026-08-08.md:THEOREM W-10` — grep-verified count **2**.

**TEETH:** NONE (orientation).

---

### EFF.W12.05  [scope-record]

**CANONICAL STATEMENT:** §S0 — the blueprint's W-12 row and the divergence box

> “**The blueprint's W-12 row, verbatim** (GRT_WELD_BLUEPRINT_2026-08-08 §S3.1):
>
> > | **W-12** | the faithfulness handoff (J-D1): under W-0..W-9 the corpus proves the (H1) residue-structure package at orders ≥ 2 on the welded class — the composition display, consuming the IFK faces downstream, owning nothing of them | J-D | **S** (composition; conditional on IFK downstream) | all above | (GR-B) RE-ACCEPTED print package at its own perimeter |”

> “**Divergence box (explicit).** The blueprint's W-12 row is the J-D1 composition display ONLY — an S-priced bookkeeping rung. The composing charge, under the standing uniformity directive (Asvin 2026-08-03: general uniform strategy, all-orders-all-primes AT ONCE, not a degree-by-degree crawl), directs W-12 at the general-n assembly that the J-D block is FOR. Both are delivered, separately graded: S1–S4 are the assembly (the new mathematics of this note, graded clause by clause); §S5 is the blueprint row's own composition display, executed at the accepted-supplier grades with every open residue named — a display, no new proof claimed there, "owning nothing of" the IFK faces exactly as the row prices it. The dependency column "all above" is honored in S9 (every consumed supplier pinned as-of); the (GR-B) partial is cited only inside §S5. No other divergence.”

**CONDITIONALITY:** The note delivers TWO separately graded things; the blueprint row itself is discharged only “AS THE DISPLAY IT PRICED” (`.50`).

**DERIVATION:** Charge-mandated reconciliation; no mathematics.

**RESOLUTION TRACE:** Base §S0, lines 58–82; untouched.

XREF: `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md:the faithfulness handoff (J-D1)` — grep-verified count **1**. **Reading note:** the blueprint's section header is written `### S3.1 The twelve lemmas` (the string `§S3.1` has count **0** there); the row is at blueprint line 302.

**TEETH:** NONE (reconciliation).

---

### EFF.W12.06  [scope-record]

**CANONICAL STATEMENT:** §S0 — Reconciliation with W-11 §S4.3 (the stated general-n program)

> “W-11 closed n = 2 and stated the general program as (P1) the node system, (P2) the per-node exhaustiveness identity with owed inputs (universal S_λ(q) censuses at g ≥ 2, the JA-GRID/JB-VTX position faces incl. JB row-12's open membership residue, the JC no-cancellation warrant at composite stages), (P3) the uniform drainage bound. THIS note executes the program's provable slice and composes the rung the program was for: (P2)'s census-times-lattice structure is clause (i) — and the S_λ(q) censuses at g ≥ 2 enter as EXPLICIT classical counting polynomials, re-derived and machine-checked at g = 2, 3 in both characteristics, so that owed input is DISCHARGED at the order-1 layer; (P3) is clause (ii); the assembly they feed is clause (iii), which S4.3 did not state and which is W-12's own theorem. (P1) appears as the organizing frame of S1's conventions (definitions, not theorems). The JB row-12 residue and the JC composite-stage warrant remain owed by the order-≥ 2 layer exactly as W-11 priced them (W12-BOX-1).”

**CONDITIONALITY:** One of W-11's three owed inputs (the `S_λ(q)` censuses at `g ≥ 2`) is discharged **at the order-1 layer only**; the other two stay owed at orders ≥ 2.

**DERIVATION:** Program-to-clause mapping; each mapped item's derivation is its own section.

**RESOLUTION TRACE:** Base §S0, lines 84–99.

XREF: `lean/notes/openmath/W11_PROOF_2026-08-08.md:S4.3` — grep-verified count **10**.

XREF: `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md:JB-VTX` — grep-verified count **77**. **Reading note:** W12 writes “JB row-12”; the hyphenated `row-12` has count **0** in GRTJB_PROOF, while `row 12` has count **9** — orthography, not a missing referent.

**TEETH:** The `g = 2, 3` censuses are machine-checked in both characteristics (`.25`, battery families W12-SHAPE/W12-QRT).

---

### EFF.W12.07  [fence]

**CANONICAL STATEMENT:** §S0 — THE KEY DESIGN DECISION (three reasons the elementary route does not scale)

> “**THE KEY DESIGN DECISION (charge-mandated, reasoning displayed).** W-11 was proved at n = 2 by elementary classification — explicit Hensel/Eisenstein/Artin–Schreier case analysis of a 3-point polygon. That route does NOT scale to the general rung, for three separately fatal reasons, and the general clauses are therefore composed THROUGH the weld machinery:
>
> 1. **Letters leave the prime field.** At a branch with residual degree d ≥ 2 the residual censuses live over F_{q^d} inside the residue extension, and "count = census × lattice q-power" is meaningful shape-only because counts are blind to WHICH letters occur — LEMMA J-D0 (count-gauge-blindness, PROVED on its perimeter, pin 9387eb1), consumed as the frame of clause (i). The elementary route would re-prove J-D0's mechanism in every characteristic dialect at every shape (W-11 S2.1's census table already shows the loci diverging — Artin–Schreier vs square classes — while the counts agree).
> 2. **Composite stages appear.** At order ≥ 2 (repeated residual factors of degree ≥ 2 — realized already on this note's quartic rows, where the λ = (1²) residual opens a degree-2 key polynomial) there is no elementary recentering: the read runs through the OM engine with the carry calculus supplying no-cancellation/level-detection at wild composite stages (GRTJC's JC-PSIKER/JC-LOAD warrant, ACCEPTED 2/2 @ 83f47f4). Hand computation of residuals stops being a proof exactly there. The order-1 layer is proved outright below precisely because THERE the welded read reduces to monic-division digit calculus.
> 3. **The membership face at general shapes is the welded polygon.** W-10's H-3 and W-11 S3 could compute their grids outright because the abscissa grids are finite and tiny; the general order-≥ 2 membership faces are GRTJB's JB-VTX/JB-DEV (ACCEPTED 2/2 @ 83f47f4) with row-12's u ≥ 0 proviso residue OPEN. The general clause (i) at orders ≥ 2 must consume them; the order-1 layer (abscissa grids {0..m}, polygons computed outright per branch) does not — which is exactly where the PROVED/CONDITIONAL line is drawn in S1.”

> “So: clause (i)'s general form is stated with the weld suppliers as displayed hypotheses ([W12-H], montes_unconditional-style), while everything the direct digit calculus reaches — the order-1 layer at ALL degrees, the full n = 2 refinement tower (W-11 consumed, history-resolved here by LEMMA W12-L0), and the n = 3 double-root stratum (transported whole by LEMMA W12-L1) — is proved outright and machine-sealed.”

**CONDITIONALITY:** This is the note's own statement of WHERE the proved/conditional line falls, and it is the rationale for `[W12-H]` (`.47`).

**DERIVATION:** Three named failure modes of the elementary route, each with its supplier.

**RESOLUTION TRACE:** Base §S0, lines 101–141.

XREF: `lean/notes/openmath/JD0_PROOF_2026-08-08.md:LEMMA J-D0` — grep-verified count **4**.

XREF: `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md:JC-PSIKER` — grep-verified count **19**; `JC-LOAD` — count **31**.

XREF: `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md:JB-DEV` — grep-verified count **63**.

**TEETH:** The quartic `λ = (1²)` stratum (`.31`) is the concrete order-2 frontier exhibit, volume law measured.

---

### EFF.W12.08  [hypothesis]

**CANONICAL STATEMENT:** §S1 Conventions — the setting, the read, and the pinned σ-DECIDED predicate

> “Conventions. Fix a degree n ≥ 2. O a complete DVR with residue field F_q (either characteristic: mixed absolutely-unramified Z_p-type, v(p) = 1, or equal F_q[[t]]-type — the W-11 r2 pin inherited; as there, the pin is load-bearing only for p = 2 disc-spectrum displays, never for counts), π a uniformizer, window N ≥ 2; enumerate monic degree-n f over O/π^N (q^(nN) of them; unit: polynomials).”

> “The read is the recursive OM-convention read: level-0 factorization of f̄ over F_q; per repeated irreducible factor P̄ (degree d, multiplicity m ≥ 2), the Φ-adic branch development (Φ the read's fixed monic lift of P̄) and its principal Newton polygon; per side, the residual polynomial over F_{q^d}; separable residuals decide (Ore leaves); repeated residual roots of degree 1 ON AN e = 1 SIDE refine (recenter deeper), while on an e ≥ 2 side they open a key of degree e·d > d — an order-2 (composite) stage, exactly S2.5's QRT-G2(h;(1²)) row [r1: the sealed trichotomy misclassified this genre as "recenter deeper"; harmless at n = 3, where every e ≥ 2 side has g = 1 so no repeated residual can occur on one — PE1-verified in the completeness case tree, incl. the runner's never-firing `assert e == 1`]; repeated residual factors of degree ≥ 2 open order-2 (composite) stages.”

> “σ(f) = the splitting type = the multiset {(e_i, f_i)} of the étale algebra of a lift (Σ e_i f_i = n); f is σ-DECIDED at window N if every O-lift of f with disc ≠ 0 has the read's σ — pinned [r3, PE3 F1: the σ-pin] to W12-BOX-7's LIFT-CERTIFICATION notion: σ-DECIDED ⟺ the window digits force ONE σ across all disc ≠ 0 O-lifts (that σ is the read's output wherever the reader decides, and beyond the reader's window exit it is certified per stratum — the DBL side by W-11's PROVED SPLIT-TAIL leg; the TRP tail case is exactly the open tail-σ-certification lemma, HEX3-BOX-1). The read-anchored parse ("the conservative reader itself printed σ") is REJECTED: on a tail member (constant term window-hidden, reader exits) "the read's σ" is undefined, so that parse would count every tail member undecided — its computed price is recorded at the [r3] F1 record after the statement.”

> “[r4, PE4 R-1: the pinned predicate is TOTAL — its degenerate corner (a member with NO disc ≠ 0 lift, where "force ONE σ" would be false while the head clause is vacuously true) is EMPTY: disc of the generic monic degree-n polynomial is a nonzero polynomial in the coefficients (Π_{i<j}(x_i−x_j)² ≢ 0 over any field), the substitution a = f + π^N g is an invertible affine change of those coefficients, and a nonzero polynomial cannot vanish identically on O^n with O infinite — so every window class has a disc ≠ 0 lift, in every characteristic; at order-1 decided shapes every lift with disc ≠ 0 factors into distinct separable irreducibles (S2.3, and see its [r4] bracket for the wild equal-characteristic disc = 0 lifts that the quantifier correctly excludes).]”

> “A SHAPE T is the letter-free read datum: level-0 configuration (degrees + multiplicities), per-branch exact polygon, per-side residual factorization type λ, refinement history — never the letter values (J-D0 keying). ORDER 1 means: every key polynomial in the read has degree d (no composite stages opened).”

**CONDITIONALITY:** THE definitional pin of the whole note. Two notions were in play; the `[r3]` pin selects W12-BOX-7's lift-certification notion and REJECTS the read-anchored parse (whose price — divergence of the normalized residue at n = 3 — is `.16`). The predicate's totality is `[r4]` R-1. The SHAPE datum explicitly **includes refinement history** — the clause that the 2026-08-12 obstruction showed the S1 display did not honour (`.09`).

**DERIVATION:** The totality argument is quoted above (generic disc ≢ 0 + invertible affine substitution + a nonzero polynomial cannot vanish identically on an infinite `O`).

**RESOLUTION TRACE:** Base §S1, lines 145–193, with `[r1]`'s trichotomy correction, `[r3]`'s σ-pin and `[r4]`'s totality remark landed in place.

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:HEX3-BOX-1` — grep-verified count **11**; the open tail-σ-certification lemma named by the pin.

XREF: `lean/notes/openmath/W11_PROOF_2026-08-08.md:SPLIT-TAIL` — grep-verified count **21**; the proved DBL-side certification leg.

**TEETH:** The runner's never-firing `assert e == 1` (PE1-verified) is the tooth for the `[r1]` trichotomy correction at n = 3.

---

### EFF.W12.09  [lemma]

**CANONICAL STATEMENT:** THEOREM W-12.A — the order-1 shape-generic count law (clause (i))

> “**(i) [THEOREM W-12.A — the order-1 shape-generic count law] PROVED at all degrees n, all prime powers q, both characteristics, wild strata included.** Let T be an order-1 window-visible decided shape: level-0 configuration C = {(P̄_i, m_i)} (distinct monic irreducibles P̄_i of degree d_i, multiplicities m_i, Σ m_i d_i = n), and per repeated branch (m_i ≥ 2) an exact branch polygon P_i (all vertex heights ≤ N−1) with per-side residual factorization types λ_{i,S} over F_{q^{d_i}}, all residuals separable. Then the window-N count of monic f realizing T is EXACTLY
>
>     #T(N) = C₀(q) · Π_{i: m_i=1} q^{d_i(N−1)}
>             · Π_{i: m_i≥2} [ (Π_S S_{λ_{i,S}}(q^{d_i})) · q^{d_i·B_i(N)} ],   [r1]
>
>     B_i(N) = m_i·N − Σ_{j<m_i} ⌈P_i(j)⌉ − L_i,
>
> where C₀(q) is the classical level-0 configuration census, S_λ(Q) = #{monic degree-g polynomials over F_Q with nonzero constant term and factorization type λ} are the UNIVERSAL residual censuses, and L_i = #{lattice points j < m_i on the polygon P_i} — one q-polynomial per shape, counts factorizing cell by cell (every (configuration, residual-letter) cell has exactly Π_{i: m_i=1} q^{d_i(N−1)} · Π_{i: m_i≥2} q^{d_i B_i(N)} members [r1]), with NO value-layer hypothesis ((VD-m), (C-coll), (R-coll), (DMULT-s), PERIM-μ all absent, J-D0 frame) and NO dependence on the characteristic or on tame vs wild: dens_T := #T(N)/q^{nN} ∈ ℚ(q) is shape-only. σ(T) is read off by Ore's theorem: one étale piece (e_S, d_i·deg ψ) per side S and irreducible residual factor ψ of R_S. W-10(2,1,1) and every W-11 row are instances; SEVEN new cubic (triple-center) families + the quartic g = 2 families are derived in S2.4/S2.5 and machine-sealed (S7). **The order-≥ 2 layer (composite stages) is NOT covered: it is the displayed hypothesis box [W12-H] (S4.2) — the JC composite-stage warrant, the JB row-12 membership residue, the J-D1 (H1) package of §S5, the residue-tower censuses, and [r1] the order-≥ 2 GMN leaf/σ-decision theorem (H-e) are its named inputs (W12-BOX-1).**”

**CONDITIONALITY — the displayed law above is SUPERSEDED TWICE by out-of-range dated appends; both corrections are effective.**

(a) **Level-0 orbit factor** (2026-08-12):

> “In W-12.A's displayed count, the level-0 prefactor \(C_0(q)\) is corrected to \[ \kappa(T)\,C_0(q). \]”
>
> “\[ \kappa(T):= \prod_{d,m} \frac{r_{d,m}!}{\prod_D r_{d,m,D}!}. \]”
>
> “Thus the corrected depth-zero display is \[ \#T(N)= \kappa(T)C_0(q)\! \prod_{i:m_i=1}q^{d_i(N-1)} \prod_{i:m_i\ge2} \left[ \left(\prod_S S_{\lambda_{i,S}}(q^{d_i})\right) q^{d_iB_i(N)} \right]. \]”

(b) **Order-1 history coverage** (2026-08-12 obstruction, then discharge):

> “W-12.A's displayed count presently proves the depth-zero order-1 cell law, but does not prove its stated coverage of the full order-1 layer. An order-1 refinement history may contain earlier repeated residuals even though its terminal residual is separable.”

> “**W-12.A regains full order-1 coverage.** Its controlling formula is (HT-global), with complete histories, transfer normalization, and the dated level-0 orbit correction. The former display is the depth-zero specialization: there are no non-root \(D_v\)-terms and no internal history orbit.”

**Effective statement of THEOREM W-12.A = `(HT-global)`** (LEMMA W12-HT, shard 2):

> “\[ \boxed{ \#T(N)= \kappa_0(T)C_0(q) \prod_{i:m_i=1}q^{d_i(N-1)} \prod_{i:m_i\ge2}\mathcal H_i(T,N).} \tag{HT-global} \]”

with the in-range display recovered as its depth-zero case. The `[W12-H]` fence on the order-≥ 2 layer is unchanged by either correction (“Composite-stage and drainage boxes do not move”).

**DERIVATION:** Assembled in §S2: `.21` (level-0 product structure) × `.23`–`.24` (one branch: the digit calculus and the census normalization) × `.22` (the level-0 census), closed at `.27` (Ore leaves). At full generality the derivation is LEMMA W12-HT's five-step proof (shard 2), whose depth-zero specialization is the §S2 chain here.

**RESOLUTION TRACE:** Base §S1 clause (i), lines 197–230, with `[r1]`'s simple-branch repair landed in the display (`.15`); corrected by the two 2026-08-12 appends (resolution rules 4–5).

XREF: `lean/notes/openmath/JD0_PROOF_2026-08-08.md:LEMMA J-D0` — grep-verified count **4**; the frame that makes the law shape-only.

**READING NOTE (external, not an edit).** `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` row **Q1 W12-2** retargets this clause's Ore citation: *“Ore's theorem … factors any `O`-lift `F`” | NS-1, NS-2 | re-cite [GN15] Thm 2.3”* — i.e. Guàrdia–Nart, *Genetics of polynomials over local fields*, Contemp. Math. 637 (2015), Theorem 2.3 (with eq. (2.1) for the `(e,f)` readout; [AGNPRW] Thm 4.4 + Prop 4.5 as the independent second leg), whose standing setting is an arbitrary discrete valued field. Verdict there: **COVERS-ALL-O**. The note's own text is compiled as written; the retarget is recorded, not applied.

**TEETH:** Battery families W12-LVL0, W12-SHAPE, W12-QRT (shard 2); teeth W12-T-SHAPE and W12-T-CENSUS4.

---

### EFF.W12.10  [open-obligation]

**CANONICAL STATEMENT:** CONJECTURE W-12.B (DRAIN-n), stated precisely

> “* **CONJECTURE W-12.B (DRAIN-n), stated precisely.** For every n ≥ 2 there is c_n(q) ∈ ℚ(q), independent of the characteristic, with undecided(n, q, N) · q^{−(n−1)N} → c_n(q) as N → ∞ at every prime power q, where undecided(n, q, N) counts the window members NOT σ-DECIDED in the S1 Conventions' pinned lift-certification sense (W12-BOX-7's convention) — NOT the conservative-read residue, whose normalized mass DIVERGES linearly at n = 3 (THEOREM HEX3.A; the σ-scoping is load-bearing, [r3] F1 record below) — equivalently the normalized σ-undecided mass is c_n(q)·q^{−N}·(1 + o(1)) → 0 (hExhaust at degree n), and the decided window counts are given exactly by finitely many q-polynomial laws in the style of clause (i). PROVED instances and bounds: n = 2 is THEOREM W-11(iii) with the EXACT law q^N (c_2 = 1, zero error at every window); the general LOWER bound undecided(n, q, N) ≥ q^{(n−1)(N−1)} holds at every n ≥ 2 (S3.3) — so the conjectured rate is correct-in-order wherever the conjecture holds. GRADE: conjecture (the n ≥ 3 upper bounds are open).”

**CONDITIONALITY:** GRADE: conjecture. The quantity is σ-scoped to the pinned notion — under the rejected read-anchored parse the conjecture is FALSE at n = 3 (`.16`).

**DERIVATION:** Not derived; the proved instances/bounds are W-11(iii) (n = 2) and `.41` (the general lower bound).

**RESOLUTION TRACE:** Base §S1 clause (ii) first bullet, lines 232–249, with the `[r3]` σ-scoping landed in place. Out of range, §S10 P-6's `[r4]` F3 bracket states plainly that the battery's measured `U₃^conv` gives W-12.B **no** n = 3 corroboration in either direction.

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:THEOREM HEX3.A` — grep-verified count **11**; the exact conservative law whose normalized mass diverges.

**TEETH:** None that can confirm it; §S10 P-6 is EXPLORATORY and explicitly not this quantity.

---

### EFF.W12.11  [lemma]

**CANONICAL STATEMENT:** THEOREM W-12.C (n = 3, partial)

> “* **THEOREM W-12.C (n = 3, partial). PROVED as stated.** For every prime power q, both characteristics, every N ≥ 2:
>
>       undecided(3, q, N) = (q−1)·q^{2N−1} + U₃^TRP(q, N),
>
>   where the first term — the σ-undecided mass of the double-root ⊗ simple-root level-0 stratum — is EXACT AND PROVED (LEMMA W12-L1 transporting W-11's exact per-center law q^{N−1}), and q^N ≤ U₃^TRP(q, N) ≤ q^{3N−2} (the triple-center stratum: lower bound by the constructed ambiguous species S3.2, upper bound = the whole TRP stratum, trivial). The EXACT U₃^TRP law is NOT derived: W12-BOX-3 displays its obstruction (the two-species n = 3 node calculus with reduced-window DBL re-entry), and the battery MEASURES it under a disclosed convention, EXPLORATORY grade. hExhaust at n = 3 is therefore NOT claimed; what is proved is the exact DBL drainage term + both bounds.”

**CONDITIONALITY:** Partial by construction. The bracket is later SHARPENED out of range by the BOX-3 annex (HEX3): “W-12.C's bracket sharpens to q^N ≤ U₃^σ ≤ q·u(q,N) with U₃^conv = q·u exactly.” The `[r4]` F3 bracket adds that post-pin this bracket “is uninformative about c₃ in BOTH directions”.

**DERIVATION:** The level-0 partition of `.36` (three separable patterns contribute 0; DBL contributes exactly `(q−1)q^{2N−1}` by W12-L1(c); TRP contributes `U₃^TRP`), with the lower bound from `.38` and the trivial upper bound from the stratum size.

**RESOLUTION TRACE:** Base §S1 clause (ii) second bullet, lines 250–265.

**TEETH:** Battery family W12-DRAIN3 (`DBL-undecided == (q−1)q^{2N−1}` on all 23 cubic rows) and tooth W12-T-DRAIN.

---

### EFF.W12.12  [hypothesis]

**CANONICAL STATEMENT:** THEOREM W-12.D — the hypothesis interface (A0), (A1), (A2)

> “**(iii) [THEOREM W-12.D — THE REDUCTION THEOREM] PROVED, unconditional as a reduction.** Fix n and suppose, at every prime power q simultaneously:
>   (A0) [lift well-posedness] every window-decided member of a core family has ALL its disc ≠ 0 O-lifts of the read's type **[r4, PE4 F2(i): "the read's type" = the family's label σ_F — the reading that (A1)'s new σ-clause now fixes; under the r3 pin, read as the member's OWN forced σ this clause is a tautology, see the [r4] F2 record]**;
>   (A1) [exact core menu] there is a FINITE list of core families F — each with a splitting type σ_F **[r4, PE4 F2: and such that EVERY member of every class (F, x) is σ-DECIDED in the S1 Conventions' pinned lift-certification sense, with forced σ = σ_F — the σ-LABELING clause; this is what Step 4's lower bound consumes, and (A0) is then its (retained) well-posedness restatement]**, a parameter set P_F ⊆ ℤ^{d_F}_{≥0} that is a finite union of shifted products of arithmetic progressions, an affine visibility threshold ν_F, and a density law dens_F(x) = c_F(q)·q^{−ℓ_F(x)} with ℓ_F affine with strictly positive parameter coefficients — such that for every window N the classes (F, x) with x visible (ν_F(x) ≤ N) are PAIRWISE DISJOINT sets of window-N polynomials, each of EXACT count dens_F(x)·q^{nN}, with all data (families, c_F, ℓ_F, P_F, ν_F) independent of q and of the characteristic;
>   (A2) [drainage of the rest] r(N)/q^{nN} → 0, where r(N) := q^{nN} − Σ_{F, x visible at N} count(F, x) — everything not in a visible core family: the σ-undecided residue AND any window-boundary (tail) families.”

**CONDITIONALITY — (A1)'s final clause is CORRECTED out of range** (2026-08-12 dated correction, resolution rule 6). The correction quotes the span it replaces and supplies the replacement:

> “In W-12.D hypothesis (A1), replace
>
> > “a density law \(\operatorname{dens}_F(x)=c_F(q)q^{-\ell_F(x)}\) … with all data (families, \(c_F\), \(\ell_F\), \(P_F\), \(\nu_F\)) independent of \(q\) and of the characteristic”
>
> by
>
> > “a density law \[ \operatorname{dens}_F(x)=c_F(q)q^{-\ell_F(x)}, \] where a single rational function \(c_F(X)\in\mathbb Q(X)\) is fixed for the family and \(c_F(q)\) denotes its evaluation at \(X=q\); the family list, \(\ell_F\), \(P_F\), \(\nu_F\), and the rational expression \(c_F(X)\) are independent of the characteristic and of the chosen prime power \(q\).””

with the reason stated at the end of that append: “The \(n=2\) coefficients such as \(q-1\) and \((q-1)/(2q)\) now satisfy (A1) as evaluations of fixed rational functions, rather than as constants independent of \(q\).”

**Effective (A1) = the corrected clause.** (A0) is, post-`[r4]`, “redundant-but-retained”: `[r5]` MINOR 1 records that “(A0) is the same statement in its well-posedness phrasing, i.e. redundant-but-retained: it is not the load-bearing warrant at either bound”.

**DERIVATION:** Hypotheses, not derived. The σ-LABELING clause's necessity is proved by the degenerate instance at `.17`; its supply at each firing degree is the FIRING CHECK table `.18`.

**RESOLUTION TRACE:** Base §S1 clause (iii) hypotheses, lines 267–295, with `[r4]` F2's two brackets landed in place; (A1)'s coefficient clause replaced by the 2026-08-12 correction.

**TEETH:** The degenerate one-family instance (`.17`) is the tooth that forces the σ-LABELING clause; the FIRING CHECK is the coverage audit.

---

### EFF.W12.13  [lemma]

**CANONICAL STATEMENT:** THEOREM W-12.D — the conclusion

> “THEN for every splitting type τ of degree n:
>
>     R_τ(q) := Σ_{F: σ_F = τ} Σ_{x ∈ P_F} c_F(q)·q^{−ℓ_F(x)}
>
> converges to ONE rational function in ℚ(q); it equals the N → ∞ limit of the decided-τ window mass AND the Haar splitting density μ_τ; it is the SAME expression at every prime power q, both characteristics, wild primes included; and Σ_τ R_τ(q) = 1.
> GRADE: PROVED (S3.4) as an unconditional reduction. At n = 2 its hypotheses are W-11's theorems — with the SPLIT-TAIL boundary family routed through (A2), see S3.4 — and it FIRES UNCONDITIONALLY, re-deriving split = inert = q/(2(q+1)), ram = 1/(q+1): the first unconditional instance of the GOAL's statement shape. At n = 3 the conditionality is exactly {(hMenu-3): the TRP refinement-family menu, W12-BOX-2} + {(hExhaust-3): the U₃^TRP upper bound, W12-BOX-3 — the other two legs of r(3,N), the σ-undecided DBL term AND the transported DBL SPLIT-TAIL boundary families (mass ⌊(N−1)/2⌋(q−1)²q^{2N−2}), are PROVED vanishing, S3.1 + S3.4 [r2]}. At n ≥ 4: those plus [W12-H] at composite stages (W12-BOX-1).”

**CONDITIONALITY:** PROVED **as a reduction** — the theorem itself is unconditional; its *firings* carry the per-degree conditionality listed above. Out of range, both n = 3 legs are DISCHARGED at composition grade by the two verbatim annexes (HEX3 → (hExhaust-3); HMENU3 → (hMenu-3)), leaving “conditional exactly on the arc grades of the W-11/W-12/HEX3/HMENU3 stack”.

**DERIVATION:** §S3.4's four steps: `.42` (rationality), `.43` (Steps 2–4), with the n = 2 instance at `.44`.

**RESOLUTION TRACE:** Base §S1 clause (iii) conclusion, lines 296–314, with `[r2]`'s boundary-tail leg landed in place.

XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:COROLLARY HM3.D` — grep-verified count **11**; the n = 3 firing that the ANNEX 2 discharge enables.

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:THEOREM HEX3.A` — grep-verified count **11**; the (hExhaust-3) discharge's law.

**TEETH:** The n = 2 instance is the non-vacuity check — it re-derives W-11's three densities through the general mechanism (`.44`).

---

### EFF.W12.14  [scope-record]

**CANONICAL STATEMENT:** GRADE SUMMARY

> “**GRADE SUMMARY: (iii) PROVED as stated; (i) PROVED at the order-1 layer of every degree (+ the named instances machine-sealed), CONDITIONAL at orders ≥ 2 on the displayed [W12-H]; (ii) theorem at n = 2 (consumed), exact-DBL-term + bounds at n = 3 (W-12.C PROVED as stated), precise conjecture in general. Attempt 0/2.**”

**CONDITIONALITY:** “Attempt 0/2” superseded by ACCEPTED 2/2. Clause (i)'s “order-1 layer of every degree” is exactly the claim the 2026-08-12 obstruction suspended and the W12-HT discharge restored — the discharge's own closing sentence: “Thus ‘the order-1 layer at all degrees’ and ‘every W-11 row is an instance’ are again justified by the note's proved mechanisms.”

**DERIVATION:** Grade ledger.

**RESOLUTION TRACE:** Base line 316–320.

**TEETH:** §S10's “Consequence for the grade box” (shard 2) re-affirms these grades from the artifacts.

---

### EFF.W12.15  [changes-record]

**CANONICAL STATEMENT:** `[r1]` F1 REPAIR RECORD (PE1 @ 2b47711, FINDING 1 CRITICAL, display-level)

> “The W-12.A display as sealed ran the product over {i : m_i ≥ 2} only, omitting the simple-branch factor Π_{i: m_i=1} q^{d_i(N−1)} — false for every shape with at least one simple branch — while the S2 proof establishes the CORRECTED law all along (S2.1's explicit simple-branch count q^{d_i(N−1)} each, assembled in S2.3): the display and the cell clause above are now ALIGNED TO THE PROOF, nothing re-proved. Verified against both PE1 counter-instances during this repair: (a) SEP-SPLIT at n = 2 (two simple branches) — the corrected display gives C₀·q^{2(N−1)} = ((q²−q)/2)·q^{2N−2} = W-11(ii)'s SEP law exactly (the sealed display gave the N-free C₀ alone); (b) DBL RAM(1) at (Zp, q = 2, N = 5) — the corrected display gives C₀·q^{N−1}·(q−1)q^{2N−3} = q(q−1)·q^{N−1}·(q−1)q^{2N−3} = 2·16·128 = 4096 == the committed artifact `w12_checks_results.json` row (Zp,2,5) dbl_keys[('RAM',(1,),())], re-read from the committed JSON this repair (the sealed display gave 256, short by exactly the simple-branch fiber q^{N−1} = 16 that LEMMA W12-L1(c) carries correctly). The corrected dens_T = C₀(q)·q^{−Σ_{i:m_i=1} d_i}·Π_{i:m_i≥2}[S_T·q^{−d_i(Σ_{j<m_i}⌈P_i(j)⌉ + L_i)}] is N-free, restoring the statement's own "dens_T ∈ ℚ(q) is shape-only" clause (internally contradicted by the sealed display).”

> “Ledger note: the 97122f2 adjudication entry transcribed the faulty display; it is ALREADY CORRECTED ledger-side (BRIDGE_ADJUDICATIONS_2026-07-30.md erratum block @ a0290f9) — this is the note-side pointer.”

**CONDITIONALITY:** Display-level: the proof already established the corrected law, so nothing is re-proved. The corrected `dens_T` is N-free, which is what makes the statement's own “shape-only” clause consistent.

**DERIVATION:** Two counter-instances computed against the committed artifact, quoted above.

**RESOLUTION TRACE:** Base lines 322–346; the repair is landed inside `.09`'s display.

XREF: `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md:erratum` — grep-verified count **54** (the file carries an erratum-block convention; the specific block is pinned by commit `a0290f9`).

**TEETH:** The committed JSON row `(Zp,2,5) dbl_keys[('RAM',(1,),())] = 4096`, re-read at the repair.

---

### EFF.W12.16  [changes-record]

**CANONICAL STATEMENT:** `[r3]` F1 REPAIR RECORD — the σ-pin, the rejected parse's computed price, and the consuming-surface sweep

> “As sealed(+r1+r2) the statement complex carried TWO non-equivalent definitions of CONJECTURE W-12.B's load-bearing quantity: S1's read-anchored sentence (whose "the read's σ" is undefined on a tail member — the S1 read description specifies no tail-certification rule — so that parse counts EVERY tail member undecided) vs W12-BOX-7's lift-certification "Decided" (the window digits force one σ across all disc ≠ 0 lifts). The two coincide at n = 2 ONLY because THEOREM W-11 proved its read certifies SPLIT-TAIL, and can disagree only on deep-tail TRP members (BOX-7's own fence); the [r3] pin — at the S1 definition and in the W-12.B bullet — selects BOX-7's notion, the one every PROVED and machine-checked surface already uses; nothing is re-proved.”

> “THE REJECTED PARSE'S PRICE (the PE3 verifier's computation, kept as the honest record of what the ambiguity would have cost): under the read-anchored/conservative parse undecided(3, q, N) contains the full conservative residue U₃^conv = q·u(q, N) (THEOREM HEX3.A, consumed by the BOX-3 annex), whose normalized mass q·u(q, N)·q^{−2N} DIVERGES linearly in N — the verifier's own transcription of HEX3.A (tied to all 23 committed U₃ values, 0 mismatches) evaluates at q = 2 to 0.50 (N = 3) → 0.86 (N = 10) → 2.53 (N = 50) → 8.78 (N = 200), asymptotic slope 1/24 — so NO c₃(q) exists and W-12.B is FALSE at n = 3 under that parse; even THEOREM W-12.C's displayed DBL constant (q−1)q^{2N−1} would inflate by the transported SPLIT-TAIL boundary mass ⌊(N−1)/2⌋(q−1)²q^{2N−2} (σ-DECIDED split-certified under the pin, undecided under the rejected parse).”

> “CONSUMING-SURFACE SWEEP (this repair; grep over every σ-DECIDED / σ-undecided / undecided / UNDECIDED surface of the note + the downstream citers): (a) consumers of the PINNED (BOX-7) notion, all consistent — THEOREM W-12.C's identity and the battery's dbl_undecided == (q−1)q^{2N−1} (W-11's certification-inclusive convention transported through W12-L1/W12-L0: S2.6, S2.7, S3.1, S7 W12-DRAIN3), the BOX-3 annex's bracket quantity U₃^σ, LEMMA W12-S2.1's branchwise decidedness and S2.3's decided shapes (Ore leaves), S3.4's (A2) routing (the transported SPLIT-TAIL boundary families enter r(N) as "σ-DECIDED split-certified" N-dependent mass — the certification named in the display), and HEX3 §S8.2's downstream corroboration remark (it routes the N-linear conservative mass to (A2)'s boundary families — the pinned parse); (b) parse-ROBUST surfaces (valid under BOTH notions) — LEMMA W12-S3.2's species and S3.3's general-n lower bound prove lift-DISAGREEMENT, and the decided-leaf statements ([W12-H](H-e) here and at GENIND's cite) have the read deciding AND certifying at once; (c) disclosed-convention MEASUREMENT surfaces (the conservative reader named explicitly, no σ-decidedness claim ridden) — the U₃^TRP EXPLORATORY battery row, the W12-ORACLE three-genre warrants (incl. the MINOR 1 sentence repaired in S7 below), and S3.4's conv-UNDECIDED tail parenthetical. NO surface consumes the rejected read-anchored parse (the Dfloor unit's σ-decided is its own self-contained every-lift definition, not a consumer of this display); the runner stays byte-frozen at seal f669cb0 — its docstring discloses the conservative convention as a MEASUREMENT convention, correct as sealed.”

**CONDITIONALITY:** The pin is definitional and note-wide. The class-(c) classification of the §S10 P-6 surface is later found INCOMPLETE by `[r4]` F3 (shard 2): “accurate about σ-decidedness, but the struck clause rode a W-12.B ORDER claim, which is the classification the sweep needed to catch”.

**DERIVATION:** The two parses are exhibited as non-equivalent, the rejected one is priced numerically from HEX3.A, and the sweep enumerates every consuming surface in three classes.

**RESOLUTION TRACE:** Base lines 348–399.

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:THEOREM HEX3.A` — grep-verified count **11**.

**TEETH:** The verifier's HEX3.A transcription “tied to all 23 committed U₃ values, 0 mismatches”.

---

### EFF.W12.17  [changes-record]

**CANONICAL STATEMENT:** `[r4]` F2 REPAIR RECORD — the missing σ-labeling hypothesis, with its necessity instance

> “As sealed(+r1+r2+r3), (A0)+(A1) attached σ_F to each core family as DATA and never said the family's members HAVE type σ_F, nor that they are σ-DECIDED at all: (A1) gave counts and disjointness only, and (A0) was conditioned on "every **window-decided** member" while Step 4's lower bound needs the conclusion for EVERY member of every visible core class (D_τ counts them all). Under the r3 pin (A0)'s "the read's type" reads as the member's own forced σ, making it the tautology "for every decided member, all disc ≠ 0 lifts have the σ they all have".”

> “THE DEGENERATE INSTANCE that the sealed hypotheses admit (PE4's, verified here): n = 2, any q, ONE family F = all window-N monic quadratics with d_F = 0, ℓ_F ≡ 0, ν_F ≡ 0, c_F = 1, and label σ_F := split. (A1) as sealed holds (a single class per window, exact count 1·q^{2N}, disjointness trivial, all data q- and characteristic-free); (A2) holds with r(N) ≡ 0; (A0) as sealed holds tautologously. The conclusion then gives R_split = 1, R_inert = R_ram = 0 — Σ_τ R_τ = 1 ✓ — while μ_split = q/(2(q+1)) ≠ 1, so the theorem's "it equals … the Haar splitting density μ_τ" clause is FALSE at that instance. The [r4] σ-LABELING clause excludes it exactly: that F contains σ-undecided members (W-11(iii)'s q^N residue) and members with forced σ = inert (SEP-INERT), so NO σ_F satisfies the clause. Nothing is re-proved: the intended reading was always S2.3's ("σ-DECIDED with σ read off the shape alone, and (A0)-strongly"), which is why the proof was morally fine and no corpus conclusion moves.”

**CONDITIONALITY:** This is a **strengthening of W-12.D's hypotheses**, not a weakening of its conclusion — the `[r4]` ARC records it as such: “the only statement-adjacent change is (A1) gaining a hypothesis clause, i.e. a STRENGTHENING of W-12.D's hypotheses, which every firing supplies”.

**DERIVATION:** A counter-model to the sealed hypothesis set, verified clause by clause, plus the exact reason the new clause excludes it.

**RESOLUTION TRACE:** Base lines 401–425; the clause itself is landed in `.12`'s (A1).

**TEETH:** The degenerate instance is the tooth; the FIRING CHECK (`.18`) is the coverage audit that no real firing is lost.

---

### EFF.W12.18  [TABLE]

**CANONICAL STATEMENT:** [TABLE] FIRING CHECK — does every instance the corpus actually fires supply the new clause?

> “*FIRING CHECK (the charge: does every instance the corpus actually fires supply the new clause? — verified against the supplier notes at this repair, clause by clause).*”

| firing | families | the σ-labeling clause, at the supplier |
|---|---|---|
| **n = 2** (S3.4, fires unconditionally) | W-11's SEVEN-row menu, of which the six core families enter (A1); SPLIT-TAIL routes through (A2) | **SUPPLIED.** W-11(i) is a table whose third column IS σ per row (split/inert/ram) and whose header states the rows are "the decided leaves of the n = 2 read"; W-11(iii) makes {rows of (i)} ⊎ {σ-undecided residue} a PARTITION of all q^{2N} — so every member of every core class is decided, with σ = the row's label. Pinned (all disc ≠ 0 lifts) strength: S2.3's Ore/Hensel certification at the separable residual, the leg S3.4 already cites as "(A0) by W-11's decidedness (+ its sealed double-lift oracle leg)" |
| **n = 3** (HMENU3 COROLLARY HM3.D) | the 33-family cubic core menu (3 level-0 separable + 4 DBL-transported + THEOREM HM3.B's TRP families) | ~~**SUPPLIED VERBATIM.**~~ **SUPPLIED AT THE disc ≠ 0 FORM — which is the form (A1) needs [r5, PE5 F1].** … **What this row vouches for is the TRUE reading, and the only one consumed:** every menu member is conservative-DECIDED, and **every disc ≠ 0 lift** of every member has σ = the leaf table's entry … **HM3.C's *phrasing* ("EVERY lift", unrestricted) carries the same over-claim [r4]'s MINOR 2 struck from this note's own S2.3:** it is FALSE in equal characteristic 3 at the in-window b₁ = b₂ = 0 members of a TRP-RAM3(h) family with 3∤h … **The n = 3 firing SURVIVES unchanged** … |
| **n = 4** (GENH4 COROLLARY GENH4.D(ii)) | the degree-4 menu of [GENIND-H(4)] | **SUPPLIED.** THEOREM GENH4.C: "At every decided stage leaf of either genre (any history, any window), EVERY lift with disc ≠ 0 has the σ claimed by the leaf dictionary" + the explicit dictionary (E: RAM ↦ {(4,1)}, 2SIDED/SPLITEQ/SPLTAIL ↦ {(2,1),(2,1)}, INERT ↦ {(2,2)}; F: {(2,2)}/{(1,2),(1,2)}/{(1,4)}) — the dictionary IS the σ_F assignment, and the quantifier is over every lift of every leaf member |
| **n = 5** (GENHN, "P(5) FIRES OUTRIGHT") | every n = 5 genre (all μ = 2) | **SUPPLIED.** THEOREM GENHN.C: "At every decided leaf of every μ = 2 stage genre (all e₁ ≥ 1, f₁ ≥ 1 with e₁f₁ ≥ 2, all Q, both characteristics, any history, any window), EVERY lift with disc ≠ 0 has the σ claimed by the leaf dictionary" (stage-RAM ↦ {(2e₁, f₁)}, stage-2SIDED/SPLITEQ/SPLTAIL ↦ {(e₁,f₁),(e₁,f₁)}, stage-INERT ↦ {(e₁, 2f₁)}), with "(A0)-strong at every μ = 2 stage leaf" recorded at the end of its proof |
| **n ≥ 6** (GENHN's P(n)) | μ ≥ 3 stage leaves appear | **NOT supplied — and openly so:** the clause at μ ≥ 3 leaves IS the named open box [GENHN-HE(μ ≥ 3)] ("σ-decision at stage leaves of multiplicity μ ≥ 3, first live n = 6"). So the strengthening hides nothing: it names, at W-12.D's own hypothesis, the one thing that program already owes |

**CONDITIONALITY:** Coverage is complete through n = 5 and **openly absent at n ≥ 6**. The n = 3 row was re-worded at `[r5]` (the strike-through above is the note's own) — the row now vouches only for the disc ≠ 0 form, and the HMENU3-side phrasing correction is owed and drafted but **not landed** (`.02`'s protocol note; the draft is `lean/notes/openmath/HMENU3_annex_draft_r5.md`).

**DERIVATION:** Per-supplier verification against the supplier notes at the repair; each cell quotes its supplier's own statement.

**RESOLUTION TRACE:** Base lines 431–437 ([TABLE], transcribed as a table per template rule 5; the n = 3 cell is elided with `…` where its argument repeats `.27`'s counter-instance), with `[r5]` F1's rewording landed inside the n = 3 cell.

XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:THEOREM HM3.C` — grep-verified count **10**.

XREF: `lean/notes/openmath/GENH4_PROOF_2026-08-08.md:THEOREM GENH4.C` — grep-verified count **9**.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:THEOREM GENHN.C` — grep-verified count **11**.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:[GENHN-HE(μ ≥ 3)]` — grep-verified count **7**; the openly-unsupplied case.

**TEETH:** The n = 3 row's counter-instance (equal characteristic 3, `F = y³ + b₀`, `F′ ≡ 0`, disc = 0) is a signed non-applicability finding, not a machine row.

---

### EFF.W12.19  [changes-record]

**CANONICAL STATEMENT:** STEP-4 RE-CHECK — does the proof now consume only the clause as stated?

> “*STEP-4 RE-CHECK (does the proof now consume only the clause as stated?).* Steps 1–3 use no σ-notion (Step 3 needs only that each family HAS a label, so the Σ_τ D_τ sum counts each family once — (A1) data). Step 4 lower bound: consumes exactly the clause (display above). Step 4 upper bound: a type-τ F with disc ≠ 0 truncating into a visible core class (F, x) forces σ_F = τ, because F is a disc ≠ 0 lift of its own truncation and the clause says every such lift has type σ_F — same clause, applied at F. Krasner-openness, the τ-partition of the étale locus and the disc = 0 null set are classical and displayed. No other σ-statement enters, and (A2) is untouched.”

**CONDITIONALITY:** Establishes that the new clause is exactly what Steps 4 consumes — no more, no less. `[r5]` MINOR 1 later routes both Step-4 bounds explicitly through it (`.43`).

**DERIVATION:** Step-by-step consumption audit.

**RESOLUTION TRACE:** Base lines 439–448.

**TEETH:** NONE (proof audit).

---

### EFF.W12.20  [changes-record]

**CANONICAL STATEMENT:** `[r4]` F1/F3/m1/m2/R-1 INDEX

> “**[r4] F1/F3/m1/m2/R-1 INDEX (PE4 @ 26689da).** F1 (CRITICAL, the inseparable witness at S3.2's b₂ = 0 sub-species) is repaired AT THE SITE with its own [r4] record after LEMMA W12-S3.2; F3 at §S10 P-6; m1 at W12-BOX-7 (§S6); m2 at S2.3; R-1 (the pin's totality) at the S1 Conventions above.”

Followed by the design close:

> “The design honors the uniformity directive: the degree-by-degree crawl is quarantined into instances-as-evidence; the GENERAL claims are W-12.A (one proof for all degrees at order 1) and W-12.D (one proof for all n), so the remaining distance to "one R_τ ∈ ℚ(q) per splitting type at all primes" is exactly the displayed boxes — named, not hand-waved.”

**CONDITIONALITY:** An index; each item's content is at its named site (`.38`/`.40` for F1, shard 2 for F3, `.51` for m1, `.27` for m2, `.08` for R-1).

**DERIVATION:** Bookkeeping.

**RESOLUTION TRACE:** Base lines 450–460.

**TEETH:** NONE (index).

---

### EFF.W12.21  [lemma]

**CANONICAL STATEMENT:** LEMMA W12-S2.1 — the level-0 product structure (window-exact Hensel)

> “**LEMMA W12-S2.1.** The multiplication map (f_i)_i ↦ Π_i f_i is a bijection from Π_i {monic of degree m_i d_i over O/π^N with reduction P̄_i^{m_i}} onto {monic of degree n over O/π^N with reduction f̄}. Moreover σ(f) = ⊔_i σ(f_i) branchwise, and f is σ-decided iff every f_i is; the fibers transport counts multiplicatively.”

**CONDITIONALITY:** Requires the `P̄_i` distinct (pairwise coprime powers) and `O` complete. Both characteristics; no separability hypothesis.

**DERIVATION:** Quoted proof:

> “*Proof.* Both sides have q^{n(N−1)} elements (a monic polynomial with fixed reduction has N−1 free digits per coefficient; Σ m_i d_i = n). Injectivity is Hensel uniqueness at finite precision: suppose Π f_i ≡ Π f_i′ mod π^k with f_i ≡ f_i′ mod π^{k−1} for all i (k minimal where some pair diverges at level k; k ≥ 2 since the reductions agree). Write f_i′ = f_i + π^{k−1}A_i, deg A_i < m_i d_i. Expanding Π f_i′ mod π^k: Σ_i Ā_i · Π_{j≠i} P̄_j^{m_j} ≡ 0 in F_q[x]. For each i, every summand except the i-th is divisible by P̄_i^{m_i}; hence P̄_i^{m_i} divides Ā_i·Π_{j≠i}P̄_j^{m_j}, and coprimality gives P̄_i^{m_i} | Ā_i, forcing Ā_i = 0 by degree — contradicting minimality of k. Surjectivity: lift f to monic F over O; Hensel over the complete O factors F = Π F_i with F̄_i = P̄_i^{m_i}; reduce mod π^N. σ-transport: any lift F of f factors as Π F_i (Hensel), and by the injectivity just proved F_i mod π^N is determined: the lift-set of f is the branchwise product of the lift-sets of the f_i. The étale algebra of F is the product over branches, so σ(F) = ⊔ σ(F_i); decidedness and σ transfer branchwise. ∎”

**RESOLUTION TRACE:** Base §S2.1, lines 466–490; untouched by later rounds. Re-used by LEMMA W12-HT step 3 (shard 2) “now on the weighted side modules”.

**TEETH:** Battery family W12-BLOCK (the Hensel product identity and fiber bijection, pointwise on every DBL member).

---

### EFF.W12.22  [lemma]

**CANONICAL STATEMENT:** §S2.1 — simple branches and the level-0 census

> “Simple branches (m_i = 1) are σ-decided at level 0 with the single étale piece (1, d_i) (Hensel: the lift factor is irreducible unramified of residue degree d_i), count q^{d_i(N−1)} each. The level-0 census C₀(q) = #{configurations f̄ of the given combinatorial type} is a classical product of irreducible-polynomial counts (instances used below: q for a linear center; q(q−1) for an ordered distinct linear pair; q(q−1)(q−2)/6 for three distinct linears; q·(q²−q)/2 for linear × irreducible quadratic; (q³−q)/3 for an irreducible cubic; these sum to q³ over the five cubic patterns — checked at q = 2: 2+2+2+2+0 = 8; at q = 3: 6+9+8+3+1 = 27). It remains to count one repeated branch.”

**CONDITIONALITY:** `C₀(q)` is the **undecorated** census — the 2026-08-12 orbit correction turns on exactly this: “S2.1's C₀(q) confirmed as the undecorated census (unordered within same-(d,m) classes)”, so a shape with two same-`(d, m)` branches carrying **distinct** decorations needs the factor `κ(T)` (`.09`(a)).

**DERIVATION:** Hensel for the simple branches; classical irreducible-polynomial counts for the census, with the closure check `Σ = q³` verified at `q = 2, 3`.

**RESOLUTION TRACE:** Base §S2.1, lines 492–501; corrected downstream by the κ(T) append.

**TEETH:** Battery family W12-LVL0 (the five cubic level-0 censuses + their sum `q³`, 0/138 in the verdict).

---

### EFF.W12.23  [lemma]

**CANONICAL STATEMENT:** §S2.2 — the monic-division digit calculus and the membership conditions

> “Branch: f with f̄ = P̄^m, d = deg P̄, m ≥ 2; Φ the read's fixed monic lift of P̄ (by S2.1 we may take f = the branch factor, monic of degree md). Monic division gives the UNIQUE Φ-adic development
>
>     f = Φ^m + Σ_{j<m} a_j Φ^j,   a_j ∈ (O/π^N)[x]_{<d},
>
> and f ↦ (a_j)_{j<m} is a bijection onto the tuples with all ā_j = 0 (uniqueness of the development of P̄^m over F_q forces ā_j = 0 ⟺ f̄ = P̄^m). Each a_j is a free module of N digit-slots over the residue F_q-space F_q^d ≅ F_{q^d} (the class map b ↦ b mod P̄ is a linear bijection on representatives of degree < d); write digit_h(a_j) ∈ F_{q^d} for the slot at height h (the GMN order-1 residual-coefficient convention). v(a_j) := min coefficient valuation = the height of the lowest nonzero slot; the branch polygon is the lower hull of {(j, v(a_j))}_{j<m} ∪ {(m, 0)} (the order-1 φ-adic polygon).”

> “Membership in the shape T (exact polygon P with vertex heights ≤ N−1; per-side residual types λ_S), slot by slot:
> * j a VERTEX of P: v(a_j) = P(j) exactly and digit_{P(j)}(a_j) ≠ 0;
> * j an on-side lattice point (side S): v(a_j) ≥ P(j), with digit_{P(j)}(a_j) = the residual coefficient r_j ∈ F_{q^d} (possibly zero; priced jointly by λ_S);
> * every other j < m: P(j) ∉ ℤ (a lattice j on the hull boundary IS an on-side point), and the strict-above condition is v(a_j) ≥ ⌈P(j)⌉ — the automatic ceiling.”

> “Every pinned or priced slot sits at height ≤ P(0) ≤ N−1: in-window, no truncation error.”

**CONDITIONALITY:** Window-visibility (`vertex heights ≤ N−1`) is what makes the count truncation-free; the identification `F_q^d ≅ F_{q^d}` is the residue-class map at the fixed lift `Φ`.

**DERIVATION:** Uniqueness of monic division; the reduction constraint `ā_j = 0`; the polygon as the lower hull; the three slot regimes read off the polygon.

**RESOLUTION TRACE:** Base §S2.2, lines 505–531; re-used verbatim as step 1 of LEMMA W12-HT (shard 2): “This is S2.2's digit calculation and does not require separability.”

**TEETH:** Battery families W12-SHAPE and W12-QRT check the resulting laws in both directions.

---

### EFF.W12.24  [lemma]

**CANONICAL STATEMENT:** §S2.2 — the branch count and the census normalization (sweep right-to-left)

> “Counting slots: slot j contributes N − ⌈P(j)⌉ free digits, minus one priced digit if j is a lattice point on the polygon (L of them), whence
>
>     #branch(N) = S_T(q^d) · q^{d·B(N)},   B(N) = mN − Σ_{j<m}⌈P(j)⌉ − L,
>
> with S_T(q^d) = #{residual-coefficient assignments: vertex digits ≠ 0, each side of type λ_S}.”

> “**The census normalization (sweep right-to-left).** Order the sides from the right; the rightmost side's right endpoint is (m, 0) with coefficient 1 (monic). Choosing its residual = a monic degree-g_S polynomial with nonzero constant term of type λ_S (S_{λ_S}(q^d) ways) fixes all its priced digits including its LEFT vertex value (a unit). Each next side to the left then has its right-vertex coefficient already fixed to a unit u; its residual is u·(monic of type λ_S) — again exactly S_{λ_S}(q^d) choices for the remaining digits, fixing its left vertex to a unit. The sweep spends exactly the L priced slots, whence
>
>     S_T(q^d) = Π_S S_{λ_S}(q^d)   — no extra unit factors.”

> “(Re-derivation cross-checks: W-11's 2SIDED row — two g = 1 sides — gives (q−1)², matching W-11's direct count (q−1)²·q^{2N−2−u−w₁} per node instance, NOT (q−1)³: interior-vertex units are already spent by the neighboring side's census. W-10's (2,1,1) row: one side, g = 1, L = 1, B = 2N−1−(1)−... P(0) = 1, P(1) = 1/2: B = 2N − 1 − 1 − 1 = 2N−3, count (q−1)q^{2N−3} per center — THEOREM W-10's law verbatim.)”

**CONDITIONALITY:** The “no extra unit factors” conclusion is exactly the correction the archived draft's spurious `(q^d−1)`-per-interior-vertex factor got wrong (`.02`); it is re-proved here and cross-checked at two independent rows.

**DERIVATION:** The right-to-left sweep quoted above, with the two cross-checks against W-11's 2SIDED row and W-10's (2,1,1) law.

**RESOLUTION TRACE:** Base §S2.2, lines 532–559; re-used as LEMMA W12-HT step 1 (“Its right-to-left sweep also applies unchanged”).

XREF: `lean/notes/openmath/W10_PROOF_2026-08-08.md:THEOREM W-10` — grep-verified count **2**.

**TEETH:** Tooth W12-T-CENSUS4 (`S_{(2)}` corrupted to `q(q−1)` must break QRT-G2(1,(2)) on every quartic row).

---

### EFF.W12.25  [TABLE]

**CANONICAL STATEMENT:** [TABLE] §S2.2 — the universal residual censuses (Q = q^d)

> “The universal censuses used below (Q = q^d; classical, re-derived this session and machine-checked in both characteristics by the S7 battery):
>
>     g = 1:  S_{(1)} = Q−1.
>     g = 2:  S_{(1,1)} = (Q−1)(Q−2)/2,  S_{(2)} = Q(Q−1)/2,
>             S_{(1²)} = Q−1            [row sum Q(Q−1) ✓].
>     g = 3:  S_{(1,1,1)} = (Q−1)(Q−2)(Q−3)/6,  S_{(1,2)} = (Q−1)·Q(Q−1)/2,
>             S_{(3)} = (Q³−Q)/3,  S_{(1,1²)} = (Q−1)(Q−2),  S_{(1³)} = Q−1
>             [row sum Q²(Q−1) ✓; at Q = 2: 0+1+2+0+1 = 4 ✓;
>              at Q = 3: 0+6+8+2+2 = 18 ✓].”

> “THE LOCI DIFFER ACROSS CHARACTERISTICS (square classes vs Artin–Schreier traces; W-11 S2.1's table is the g = 2 instance); THE COUNTS DO NOT — J-D0's blindness at the residual level, which is the entire reason clause (i) can be stated shape-only.”

**CONDITIONALITY:** Classical counting polynomials; the characteristic-independence of the COUNTS (not the loci) is the J-D0 frame, and it is what discharges W-11's owed `g ≥ 2` census input at the order-1 layer (`.06`).

**DERIVATION:** Classical, re-derived in-session, with row-sum checks displayed and numeric checks at `Q = 2, 3`.

**RESOLUTION TRACE:** Base §S2.2, lines 562–575; the exact zeros (`S_{(1,1)}(2) = 0`, `S_{(1,1,1)}(q ≤ 3) = 0`) become real battery predictions at `.30`.

XREF: `lean/notes/openmath/JD0_PROOF_2026-08-08.md:LEMMA J-D0` — grep-verified count **4**.

**TEETH:** Battery checks the censuses in both characteristics; the exact zeros are checked exactly (P-2, P-3).

---

### EFF.W12.26  [fence]

**CANONICAL STATEMENT:** §S2.2 — cell factorization and the lift-convention note

> “Cell factorization: for FIXED configuration and residual-letter assignment the remaining digits are free — every cell has exactly q^{d·B(N)} members (W-10's cell-by-cell template at every degree). Convention note: the count is stated for the read's OWN lift choice Φ; the formula is independent of which fixed monic lift the convention picks (the development bijection works verbatim for each), while the deeper question — whether different lift conventions select the same member SET at deep shapes — is the W-2/LIFTCORNER seam, not consumed here (W12-BOX-5).”

**CONDITIONALITY:** Independence is asserted for the FORMULA, explicitly not for the member SET at deep shapes.

**DERIVATION:** The development bijection of `.23` holds for each fixed monic lift.

**RESOLUTION TRACE:** Base §S2.2, lines 577–585.

**NON-IMPORT (explicit):** the lift-convention seam (W-2/LIFTCORNER) “not consumed here”.

**TEETH:** NONE (fence).

---

### EFF.W12.27  [lemma]

**CANONICAL STATEMENT:** §S2.3 — Decidedness and σ (Ore leaves); clause (i) assembled

> “If every residual is separable, Ore's theorem (the order-1/regular case of the Montes read; Ore 1928, via GMN "Newton polygons of higher order", order-1 layer — classical, cited not re-proved) factors any O-lift F of the branch into one monic irreducible factor per (side S, irreducible residual factor ψ | R_S), with e = e_S (the denominator of S's slope in lowest terms) and residue degree d·deg ψ. All data the read consumes sit at heights ≤ N−1, so every lift of the window class shares them: the shape is σ-DECIDED with σ read off the shape alone, and (A0)-strongly (every disc ≠ 0 lift has this σ ~~— in fact every lift~~ **[r4, PE4 m2: the struck parenthetical is FALSE in equal characteristic at wild decided shapes, and nothing consumes it — (A0), (A1)'s [r4] σ-labeling clause and Step 4 all quantify over disc ≠ 0 lifts only. Counter-instance from the note's own family table: a TRP-RAM3(h) member with 3∤h whose b₁, b₂ vanish in-window admits the lift F = y³ + b₀ with v(b₀) = h, and in equal characteristic 3 that lift has F′ ≡ 0, hence disc = 0 and no σ at all; same at any wild side with e divisible by p and the intermediate slots empty (LINRAM2 / RAM2LIN / QRT-G2 in char 2). Such lifts are exactly what the disc ≠ 0 quantifier is for — same root cause as the [r4] F1 repair in S3.2]**). Combining S2.1 (product over branches) × S2.2 (each branch) × the level-0 census C₀(q): THEOREM W-12.A. ∎”

**CONDITIONALITY:** The quantifier is **disc ≠ 0 lifts only** — the unrestricted “every lift” is struck as FALSE in equal characteristic at wild decided shapes, with an explicit counter-instance. This is the σ-certification strength that W-12.D's (A1) clause needs and that the FIRING CHECK audits at every degree.

**DERIVATION:** Ore's theorem at separable residuals (cited, not re-proved) + the in-window pinning sentence (“All data the read consumes sit at heights ≤ N−1”) + the S2.1 × S2.2 × C₀ assembly.

**RESOLUTION TRACE:** Base §S2.3, lines 589–609, with `[r4]` m2's strike landed in place. The struck phrase's blast radius is swept at `[r5]`'s m2 table (shard 2), which finds HMENU3's HM3.C inheriting the same over-claim and HEX3 L80–81 carrying the same phrasing with its conclusion unaffected.

**READING NOTE (external, not an edit).** `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` row **Q1 W12-2** targets exactly this sentence — *“Ore's theorem … factors any `O`-lift `F`”* — and retargets it to **[GN15] Theorem 2.3** (NS-1/NS-2), with `[GN15]` eq. (2.1) supplying the `(e, f)` readout and `[AGNPRW]` Thm 4.4 + Prop 4.5 as the independent second leg; verdict **COVERS-ALL-O** (arbitrary discrete valued field, any monic `g ∈ O_v[x]`, no separability needed). Recorded, not applied.

**TEETH:** Battery family W12-ORACLE (PARI σ-multiset per decided member, `disc = 0 ⟹ never decided`) and tooth W12-T-SIGMA.

---

### EFF.W12.28  [TABLE]

**CANONICAL STATEMENT:** [TABLE] §S2.4 — the SEVEN new decided families at the triple center

> “At a TRP center (f̄ = (x−c̄)³; q centers; recenter g = f(x+c) with coefficients (b₂, b₁, b₀), all v ≥ 1; branch polygon = hull of {(0,u₀),(1,u₁),(2,u₂),(3,0)}, u_j := v(b_j)), the digit calculus of S2.2 evaluates to (all counts PER CENTER; whole space = × q centers; params ≥ 1; visibility u₀ ≤ N−1; ⌈2h/3⌉+⌈h/3⌉ = h+1 for 3∤h):”

| family | polygon / residual datum | count PER CENTER | σ | wild stratum |
|---|---|---|---|---|
| TRP-RAM3(h), 3∤h | one side (0,h)–(3,0), e = 3, g = 1 | (q−1)·q^{3N−2h−2} | {(3,1)} | p = 3 / char 3 |
| TRP-3LIN(m₁>m₂>m₃) | three sides, slopes m₁,m₂,m₃ | (q−1)³·q^{3N−3−m₁−2m₂−3m₃} | {(1,1)³} | — |
| TRP-LINRAM2(u₀,u₁), u₁ odd, 2u₀>3u₁ | vertex (1,u₁); right side e = 2 | (q−1)²·q^{3N−2−u₀−u₁−(u₁+1)/2} | {(1,1),(2,1)} | p = 2 / char 2 |
| TRP-VERT1(u₀,k;λ), u₀>3k, λ∈{(1,1),(2)} | vertex (1,2k); right side e = 1, g = 2 | (q−1)·S_λ(q)·q^{3N−3−u₀−3k} | {(1,1)}⊎σ(λ) | — |
| TRP-FULL(k;λ), λ∈{(1,1,1),(1,2),(3)} | one side (0,3k)–(3,0), e = 1, g = 3 | S_λ(q)·q^{3N−6k−3} | σ(λ) | — |
| TRP-RAM2LIN(u₀,t), u₀−t odd, u₀>3t | vertex (2,t); left side e = 2 | (q−1)²·q^{3N−2−u₀−t−(u₀+t+1)/2} | {(2,1),(1,1)} | p = 2 / char 2 |
| TRP-VERT2(u₀,t;λ), u₀−t even, u₀>3t, λ∈{(1,1),(2)} | vertex (2,t); left side e = 1, g = 2 | (q−1)·S_λ(q)·q^{3N−3−u₀−t−(u₀+t)/2} | σ(λ)⊎{(1,1)} | — |

**CONDITIONALITY:** Depth-0 (no refinement history), per center, window-visible (`u₀ ≤ N−1`). Three rows are wild strata (`p = 3` for RAM3; `p = 2` for LINRAM2/RAM2LIN) and are counted by the same laws as the tame rows.

**DERIVATION:** Each row is a direct S2.2 evaluation; the derivations are `.29`.

**RESOLUTION TRACE:** Base §S2.4, lines 611–627; untouched by later rounds (the κ(T) correction does not touch single-repeated-branch shapes: “κ(T) = 1 re-checked on every sealed and every consumed instance”).

**TEETH:** Battery family W12-SHAPE (both directions: an observed-but-unpredicted decided key is a violation, and so is a predicted-but-absent one) and tooth W12-T-SHAPE.

---

### EFF.W12.29  [lemma]

**CANONICAL STATEMENT:** §S2.4 — the seven derivations and the σ(λ) dictionary

> “Derivations (each a direct S2.2 evaluation; heights listed are (⌈P(0)⌉, ⌈P(1)⌉, ⌈P(2)⌉)):
> * RAM3(h): heights (h, ⌈2h/3⌉, ⌈h/3⌉) summing to 2h+1; L = 1 (only j = 0 lattice); S_T = S_{(1)} = q−1. B = 3N − (2h+1) − 1.
> * 3LIN: heights (m₁+m₂+m₃, m₂+m₃, m₃), sum m₁+2m₂+3m₃; L = 3; S_T = (q−1)³.
> * LINRAM2(u₀,u₁): heights (u₀, u₁, (u₁+1)/2); L = 2 (j = 0, 1); S_T = (q−1)² (two g = 1 sides). Vertex-at-1 condition u₀−u₁ > u₁/2 ⟺ 2u₀ > 3u₁.
> * VERT1(u₀,k;λ): heights (u₀, 2k, k); L = 3; S_T = S_{(1)}·S_λ. Vertex condition u₀−2k > k ⟺ u₀ > 3k.
> * FULL(k;λ): heights (3k, 2k, k); L = 3; S_T = S_λ.
> * RAM2LIN(u₀,t): heights (u₀, (u₀+t+1)/2, t); L = 2 (j = 0, 2); S_T = (q−1)². Vertex-at-2 condition (u₀−t)/2 > t ⟺ u₀ > 3t.
> * VERT2(u₀,t;λ): heights (u₀, (u₀+t)/2, t); L = 3; S_T = S_λ·S_{(1)}.”

> “σ(λ) reads by Ore (S2.3): (1,1) ↦ {(1,1),(1,1)}; (2) ↦ {(1,2)}; (1,1,1) ↦ {(1,1)³}; (1,2) ↦ {(1,1),(1,2)}; (3) ↦ {(1,3)}; an e = 2 side of residual degree 1 ↦ {(2,1)}; the e = 3 side ↦ {(3,1)}.”

**CONDITIONALITY:** Each row's vertex condition is part of its family definition; the σ dictionary is Ore's readout at `.27`'s strength (disc ≠ 0 lifts).

**DERIVATION:** As displayed — heights, `L`, `S_T`, then `B(N) = mN − Σ⌈P(j)⌉ − L` from `.24`.

**RESOLUTION TRACE:** Base §S2.4, lines 629–647.

**TEETH:** An independent pre-runner brute force confirmed all seven laws per center at nine `(p, N)` pairs (`.30`'s machine line).

---

### EFF.W12.30  [lemma]

**CANONICAL STATEMENT:** §S2.4 — Completeness at depth 0

> “**Completeness at depth 0:** every exact visible 4-point polygon falls in exactly one row or a REFINE/tail case: one side — slope h/3 with 3∤h (RAM3) xor integer slope k (FULL; decided iff λ separable, else refine); vertex at 1 only — right side of length 2: e = 2 (LINRAM2) xor e = 1 (VERT1 / refine at λ = (1²)); vertex at 2 only — left side of length 2: e = 2 (RAM2LIN) xor e = 1 (VERT2 / refine); vertices at 1 and 2 — 3LIN, always decided. So the seven families are the COMPLETE depth-0 decided TRP menu, and the battery enforces key-completeness (any unpredicted depth-0 decided key is a violation, both directions). Refinement leaves (repeated residual roots: λ ∈ {(1²)} on a g = 2 side, {(1,1²)}, {(1³)} on the g = 3 side) recurse deeper; their per-history laws are NOT derived here (W12-BOX-2: the n = 3 analogue of W-11's instance bracket, with TWO node species — see S3.1). The exact-zero rows are real predictions: S_{(1,1)}(2) = 0, S_{(1,1,1)}(q) = 0 for q ≤ 3 — the battery checks the zeros exactly. ∎”

> “[machine: W12-SHAPE — all seven laws, both directions, on every cubic row; re-derivation record: an independent throwaway brute-force (pre-runner, this session) confirmed all seven laws per center at (p,N) ∈ {(2,3),(2,4),(2,5),(2,7),(3,2),(3,3),(3,4),(5,2),(7,2)}, including the 22-key (2,7) row realizing TRP-3LIN(3,2,1).]”

**CONDITIONALITY:** Completeness is at **depth 0** only; the refinement leaves are explicitly not derived here (W12-BOX-2), and that gap is what ANNEX 2 (HMENU3) later discharges at composition grade.

**DERIVATION:** Case exhaustion over the possible vertex sets of a visible 4-point polygon, each case resolved by `e = 1` vs `e ≥ 2` and by residual separability.

**RESOLUTION TRACE:** Base §S2.4, lines 649–669.

**TEETH:** W12-SHAPE both directions + the exact-zero predictions; the independent pre-runner brute force at nine `(p, N)` pairs.

---

### EFF.W12.31  [lemma]

**CANONICAL STATEMENT:** §S2.5 — the quartic g = 2 instance (first g ≥ 2 residual census row)

> “At a quadruple center (f̄ = (x−c̄)⁴; recentered coefficients (b₃,b₂,b₁,b₀), all v ≥ 1), the shape with ONE side (0,2h)–(4,0), h odd (slope h/2, e = 2, length 4, g = 2; lattice points j = 0, 2, 4; residual R(y) = y² + r₂y + r₀ over F_q, r₂ = digit_h(b₂), r₀ = digit_{2h}(b₀) ≠ 0): S2.2 gives, per center,
>
>     QRT-G2(h; λ):  S_λ(q)·q^{4N−5h−3},   λ ∈ {(1,1), (2)}:
>     σ = {(2,1),(2,1)} for λ = (1,1);  {(2,2)} for λ = (2) — wild at p = 2;
>     QRT-G2(h; (1²)) [NOT decided at order 1 — the composite-stage
>     frontier]: (q−1)·q^{4N−5h−3} members open a DEGREE-2 key (order 2).
>
> (Heights (2h, ⌈3h/2⌉ = (3h+1)/2, h, (h+1)/2), sum 5h+1; L = 2 (j = 0, 2); B = 4N − (5h+1) − 2.) The λ = (1²) row is displayed deliberately: it is the FIRST machine-measured composite-stage stratum with an exact volume law — the count is order-1 data (S2.2 needs no decidedness to price the locus), while its σ-resolution is exactly what [W12-H] owes (W12-BOX-1). The battery checks both decided laws (including the q = 2 exact zero for λ = (1,1)) and the (1²) volume. ∎”

**CONDITIONALITY:** The `(1²)` row is a **volume law without a σ-resolution** — the count is proved, the splitting type is owed to `[W12-H]`. This row is the note's concrete order-≥ 2 frontier exhibit.

**DERIVATION:** Direct S2.2 evaluation with the displayed heights, `L = 2`, and `B(N) = 4N − (5h+1) − 2`.

**RESOLUTION TRACE:** Base §S2.5, lines 673–690.

**READING NOTE:** the 2026-08-12 κ(T) append records that these sealed quartic rows are the QUADRUPLE center (one branch), so “no sealed row exercises two same-(d,m) branches with distinct decorations — the battery's GREEN is consistent with the defect”. The orbit correction therefore moves no committed number here.

**TEETH:** Battery family W12-QRT (both decided laws, the `q = 2` exact zero, and the `(1²)` volume) and tooth W12-T-CENSUS4.

---

### EFF.W12.32  [lemma]

**CANONICAL STATEMENT:** LEMMA W12-L0 (the history-resolved n = 2 law; W-11 refined)

> “**LEMMA W12-L0.** Fix n = 2, a center, a window N, and a refinement history H = (k₁ < ⋯ < k_t) (t ≥ 0; k₁ ≥ 1; refinement at depth k requires 2k ≤ N−1, so k_t ≤ M := ⌊(N−1)/2⌋; write s := k_t, s = 0 for t = 0). The window-N count PER CENTER of monic quadratics with history exactly H and the given leaf is (q−1)^t × the leaf count from ONE node instance C(2s+1, s+1) (W-11 S2 coordinates):
>
>     RAM(u)@H:        (q−1)·q^{N−1−u}·q^{N−(u+1)/2},  u odd, 2s+1 ≤ u ≤ N−1;
>     2SIDED(w,u−w)@H: (q−1)²·q^{2N−2−u−w},  s+1 ≤ w, 2w < u ≤ N−1;
>     SPLITEQ(k)@H:    ((q−1)(q−2)/2)·q^{2N−3k−2},  s+1 ≤ k ≤ M;
>     INERTDEEP(k)@H:  (q(q−1)/2)·q^{2N−3k−2},      s+1 ≤ k ≤ M;
>     SPLIT-TAIL(w)@H: (q−1)·q^{N−1−w},   s+1 ≤ w ≤ M;
>     UNDECIDED@H:     q^{N−1−M}.”

**CONDITIONALITY:** `n = 2` only — this is the lemma the 2026-08-12 obstruction cites as insufficient for the general order-1 claim (“W12-L0 supplies this only for \(n=2\)”), and whose `(q−1)^t` prefactor exhibits the missing history factor. Its own content is unaffected: LEMMA W12-HT “recovers” it (“This is W12-L0's \((q-1)^t\) factor and its six leaf laws”).

**DERIVATION:** Quoted proof:

> “*Proof.* Induction on t. Base t = 0 (root node C(1,1)): each formula is the digit count of its defining locus (W-11 S2.1/S2.4 conditions, both characteristics): RAM(u): v(A₀) = u exact + nonzero digit [(q−1)q^{N−1−u}] and v(A₁) ≥ (u+1)/2 [q^{N−(u+1)/2}]; 2SIDED: both exact-valuation pins [(q−1)²q^{(N−1−u)+(N−1−w)}]; SPLITEQ/INERTDEEP: v(A₀) = 2k with digit c₀ ≠ 0, v(A₁) ≥ k with digit_k = c₁, (c₁,c₀) priced by the W-11 residual census [(q−1)(q−2)/2 resp. q(q−1)/2 pairs, × q^{N−2k−1}·q^{N−k−1}]; SPLIT-TAIL(w): A₀ = 0 (v ≥ N over O/π^N) and v(A₁) = w exact + nonzero digit [(q−1)q^{N−1−w}]; UNDECIDED: A₀ = 0 and v(A₁) ≥ M+1 [q^{N−1−M}] — the constraint ranges embed the node constraints (u ≥ 2s+1, w ≥ s+1) so the per-instance formulas are s-independent on their stated ranges. Step t → t+1: W-11 S2.3 (consumed at pin, post-r2 text): for each of the q−1 letters z̄, the refine locus at depth k_{t+1} maps measure-isomorphically ONTO C(2k_{t+1}+1, k_{t+1}+1), in both characteristics; histories concatenate, counts multiply by (q−1). ∎”

**RESOLUTION TRACE:** Base §S2.6, lines 694–723.

XREF: `lean/notes/openmath/W11_PROOF_2026-08-08.md:S2.3` — grep-verified count **8**; the refinement measure-isomorphism consumed as the induction step (LEMMA W12-HT generalizes exactly this: “This is W-11 S2.3's measure-isomorphism mechanism without the quadratic restriction”).

**TEETH:** Battery family W12-L0HIST (every `(kind, params, hist)` key against these closed forms, on 11 quadratic rows; and `Σ_H` against the sealed W-11 aggregate predictor).

---

### EFF.W12.33  [lemma]

**CANONICAL STATEMENT:** §S2.6 — aggregation back to W-11, and the drainage consistency display

> “Summing W12-L0 over H returns W-11's aggregated rows (the instance bracket: Σ over histories ending at any s < k of (q−1)^t = 1 + Σ_{s=1}^{k−1}(q−1)q^{s−1} = q^{k−1} per leaf read at k — W-11 S2.5's bracket re-derived). Consistency display for drainage: undecided per center = Σ_H (q−1)^t·q^{N−1−M} = q^{N−1−M}·(1 + Σ_{s=1}^{M}(q−1)q^{s−1}) = q^{N−1−M}·q^M = q^{N−1} — W-11's exact law, history-resolved. Each history-resolved key is its own decided shape (refinement depth t as shape datum); at n = 2 the refinement tower never leaves key degree 1, which is why W12-L0 needs no [W12-H] input.”

**CONDITIONALITY:** The closing clause is the reason W12-L0 is `[W12-H]`-free: at n = 2 no composite stage ever opens.

**DERIVATION:** The two displayed geometric sums.

**RESOLUTION TRACE:** Base §S2.6, lines 725–735.

**TEETH:** W12-L0HIST's second leg (`Σ_H` vs the sealed W-11 aggregate predictor, key by key, on every cubic row's `(q, N)`).

---

### EFF.W12.34  [lemma]

**CANONICAL STATEMENT:** LEMMA W12-L1 (block transfer: the DBL stratum of cubics IS the n = 2 system)

> “**LEMMA W12-L1.** (a) [window Hensel split] (g, l) ↦ g·l is a bijection {monic quadratic g, ḡ = (x−c̄)²} × {monic linear l, l̄ = x−d̄} → {monic cubic f, f̄ = (x−c̄)²(x−d̄)} over O/π^N.
> (b) [read equivalence] The recursive read of f at the center c̄ equals the W-11 read of its block g: the same trichotomy case at every node, the same (u, w) parameters, unit-scaled letters, the same refinement history, the same decided/tail/undecided exit.
> (c) [σ and drainage transfer] σ(f) = σ_block(g) ⊎ {(1,1)}; f is σ-decided iff g is. Hence for every W-11 history-resolved key: #{DBL members over one pattern realizing it} = q^{N−1} × (the W12-L0 per-center count), and the σ-undecided DBL count over all patterns is EXACTLY q(q−1)·q^{N−1}·q^{N−1} = (q−1)·q^{2N−1}.”

**CONDITIONALITY:** Fixed level-0 pattern `f̄ = (x−c̄)²(x−d̄)` with `c̄ ≠ d̄` (the lemma's own fence, cited later at the ORACLE genre analysis: “W12-L1's own fence is c̄ ≠ d̄, S2.7”). Clause (c) consumes W-11 clause (iii) at pin.

**DERIVATION:** Quoted proof:

> “*Proof.* (a) is the two-branch case of LEMMA W12-S2.1. (b) Write g(x+c) = x² + B₁x + B₀ (v(B₁), v(B₀) ≥ 1) and l(x+c) = x − ρ̃ with ρ̃ = r − c (l = x − r, r ≡ d̄), res(ρ̃) = d̄ − c̄ =: ρ̄ ≠ 0 a unit. Then f(x+c) = x³ + a₂′x² + a₁′x + a₀′ with
>
>     a₂′ = B₁ − ρ̃,   a₁′ = B₀ − ρ̃B₁,   a₀′ = −ρ̃B₀,
>
> so v(a₂′) = 0, v(a₀′) = v(B₀) =: u with digit_u(a₀′) = −ρ̄·digit_u(B₀), and the PRINCIPAL part of f's polygon at c̄ is the hull of {(0,u),(1,v(a₁′)),(2,0)} (the point (3,0) contributes the slope-0 simple side = the l-branch). Case check against the block hull {(0,u),(1,w),(2,0)}, w := v(B₁):
> * 2w < u: v(ρ̃B₁) = w < u = v(B₀) ⟹ v(a₁′) = w exactly, digit −ρ̄·digit_w(B₁) — the same two one-point sides, same (w, u−w), letters unit-scaled by −ρ̄.
> * u odd, w ≥ (u+1)/2: v(a₁′) ≥ min(u, w) ≥ (u+1)/2 > u/2 — the same single RAM(u) side, letter −ρ̄·digit_u(B₀) ≠ 0.
> * u = 2k, w ≥ k: v(a₁′) ≥ k; since v(B₀) = 2k > k, digit_k(a₁′) = −ρ̄·digit_k(B₁) = −ρ̄·c₁; the abscissa-2 digit is res(a₂′) = −ρ̄, and digit_{2k}(a₀′) = −ρ̄·c₀. The side residual of f is therefore R_f(y) = −ρ̄·(y² + c₁y + c₀) = −ρ̄·R_g(y) — a UNIT multiple: same separability type, same roots, same refinement letter z̄ (J-D0's blindness literal at this seam: the letters move by a unit, the shape and the counts cannot).
> Refinement recenters both reads by the SAME s = ẑπ^k (ẑ a lift of the double residual root z̄): g(x+c+s) is W-11's refined block, and l(x+c+s) = x − (ρ̃ − s) with res(ρ̃ − s) = ρ̄ ≠ 0 still a unit (v(s) ≥ 1): the setup is preserved, the induction continues, and refinement depths strictly increase, so the two reads terminate together with equal histories. Tail exits: over O/π^N, v(B₀) ≥ N means B₀ = 0, whence a₁′ = −ρ̃B₁ EXACTLY: v(a₁′) = w with the SAME digit data, and the SPLIT-TAIL/UNDECIDED split (w ≤ M or not) transfers verbatim. (c) By (a) every O-lift F of f factors as G·L with G ≡ g, L ≡ l mod π^N (Hensel-factor F, reduce, apply (a)'s injectivity); L contributes the piece (1,1), and G ranges over exactly the lifts of g as F ranges over the lifts of f. So lift-σ-set(f) = lift-σ-set(g) ⊎ {(1,1)}: σ, decidedness, and (A0) well-posedness transfer. Counts: the fiber over g is the q^{N−1} monic linears with reduction x−d̄. Drainage: W-11 clause (iii) (consumed at pin 7020ceb/cb05127, post-r2 HEAD 31506b3) gives σ-undecided quadratic blocks = q^{N−1} per center; × q^{N−1} linears × q(q−1) patterns = (q−1)·q^{2N−1}. ∎”

**RESOLUTION TRACE:** Base §S2.7, lines 739–795. LEMMA W12-HT (shard 2) records it as “compatible”: “Its quadratic block is one child coordinate of (HT-fiber); the coprime linear branch supplies \(q^{N-1}\).”

XREF: `lean/notes/openmath/W11_PROOF_2026-08-08.md:THEOREM W-11` — grep-verified count **3**; clause (iii) consumed at pin for the drainage transfer.

XREF: `lean/notes/openmath/JD0_PROOF_2026-08-08.md:LEMMA J-D0` — grep-verified count **4**; the unit-scaled-letter blindness at this seam.

**TEETH:** Battery families W12-BLOCK (product identity + fiber bijection) and W12-L1X (the FRESH direct cubic read vs the SEALED W-11 classifier on the Hensel block, pointwise on every DBL member — 0/1,594,090 in the verdict).

---

### EFF.W12.35  [fence]

**CANONICAL STATEMENT:** §S2.7 — what W12-L1 is an instance of

> “W12-L1 is the smallest instance of the S0 design decision: the general mechanism is TRANSPORT — blocks reduce to lower-degree systems with unit-scaled letters that counts never see — not per-degree re-derivation. It moves the ENTIRE proved W-11 menu (count laws, per-history structure via W12-L0, and the exact drainage term) into degree 3 at one stroke.”

**CONDITIONALITY:** A design statement about mechanism, not a count claim.

**DERIVATION:** Reading of `.34`.

**RESOLUTION TRACE:** Base §S2.7, lines 797–806.

**TEETH:** W12-BLOCK / W12-L1X as above.

---

### EFF.W12.36  [lemma]

**CANONICAL STATEMENT:** §S3.1 — the n = 3 partition and the exact DBL term

> “undecided(3, q, N) partitions by level-0 pattern (S2.1: decidedness is branchwise): the three separable patterns contribute 0 (all branches simple ⟹ decided at level 0); the DBL patterns contribute EXACTLY (q−1)·q^{2N−1} (LEMMA W12-L1(c) — a THEOREM); the TRP pattern contributes U₃^TRP(q, N), for which no law is derived here. THEOREM W-12.C's identity is this partition. ∎(the exact term)”

**CONDITIONALITY:** The identity is exact; only its `U₃^TRP` summand is underived.

**DERIVATION:** Branchwise decidedness (`.21`) partitions by level-0 pattern; the DBL term is `.34`(c); the separable patterns contribute nothing since all their branches are simple.

**RESOLUTION TRACE:** Base §S3.1, lines 812–817.

**TEETH:** W12-DRAIN3 (`partition Σ == q^{3N}`; `DBL-undecided == (q−1)q^{2N−1}` on all 23 rows) and tooth W12-T-DRAIN.

---

### EFF.W12.37  [open-obligation]

**CANONICAL STATEMENT:** §S3.1 — the obstruction to an exact `U₃^TRP` law (two node species)

> “The obstruction to an exact U₃^TRP law, displayed (W12-BOX-3): the TRP refinement tree has TWO node species — (α) the triple-cluster node (λ = (1³) at a FULL side: recentering keeps all three roots in one cluster, a genuine n = 3 node, analogous to W-11's C(2s+1, s+1) but with a 3-parameter state), and (β) the DBL-re-entry node (λ = (1,1²) at FULL, or (1²) at a VERT1/VERT2 g = 2 side: one root Hensel-splits off, and the remaining double cluster re-enters the n = 2 system of W-11/W12-L0 at a REDUCED window and shifted valuation frame). A closed form needs the (α)-species instance bracket (the n = 3 analogue of W-11's Σ(q−1)^t q^{s−1} identity) plus the (β)-species window-transfer law; neither is derived here. Additionally the TRP TAIL needs its own σ-certification lemma (the n = 3 SPLIT-TAIL analogue: a deep vertex can certify a split-off (1,1) piece even with b₀ hidden), also not derived. These three named lemmas are exactly (hMenu-3)/(hExhaust-3)'s distance.”

**CONDITIONALITY:** Three named missing lemmas. Out of range, ANNEX 2 (HMENU3) discharges the two species' transfer laws at composition grade (“both node species' transfer laws leaf-resolved: α self-similar with key shear, β into W12-L0 via the raw-key dictionary”), and the BOX-3 annex (HEX3) discharges the vanishing upper bound; the tail-σ-certification lemma stays open as HEX3-BOX-1.

**DERIVATION:** Species analysis of the TRP refinement tree.

**RESOLUTION TRACE:** Base §S3.1, lines 819–833.

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:HEX3-BOX-1` — grep-verified count **11**; the still-open tail-σ-certification lemma.

XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:THEOREM HM3.C` — grep-verified count **10**; the supplier that resolves both species.

**TEETH:** None — this is the note's honest statement that no closed form is preregistered for `U₃^TRP`.

---

### EFF.W12.38  [lemma]

**CANONICAL STATEMENT:** LEMMA W12-S3.2 — the TRP lower bound via a constructed ambiguous species

> “**LEMMA W12-S3.2.** Every TRP member with b₁ = b₀ = 0 over O/π^N (after recentering; b₂ ∈ πO/π^N free) is σ-undecided: U₃^TRP(q, N) ≥ q·q^{N−1} = q^N.”

**CONDITIONALITY:** The statement and count are byte-unchanged across the `[r4]` repair — only the PROOF's witness construction changed (`.40`). The construction is now uniform in the characteristic.

**DERIVATION:** Quoted proof, at its `[r4]`-repaired form:

> “*Proof (constructed lifts, both characteristics, every q; **[r4, PE4 F1] ONE branch now — the b₂ = 0 sub-species is handled by the generic construction at t := N, and the sealed B = 0 branches, which are INSEPARABLE in equal characteristic 2 resp. 3, are DELETED; record and the every-characteristic separability display after the proof**).* Let t = v(b₂) ∈ [1, N−1] and B a lift of b₂ to O with v(B) = t; **[r4] when b₂ = 0 take B = π^N and t := N** — any lift of valuation ≥ N serves (B ≡ b₂ = 0 mod π^N), and NEVER B = 0.
> Lift 1 (split-directed): F_A = (x−c)³ + B(x−c)² + π^{2K+1}(x−c) with 2K+1 ≥ max(N, 2t+2). Then F_A = (x−c)·((x−c)² + B(x−c) + π^{2K+1}); the quadratic factor has polygon {(0, 2K+1), (1, t), (2, 0)} with 2t < 2K+1: two one-point sides — two roots in O at distinct valuations t and 2K+1−t: σ_A = {(1,1),(1,1),(1,1)}.
> Lift 2 (ramification-directed): F_B = (x−c)³ + B(x−c)² + π^L with L ≥ 3N and L − t odd (choosable). Polygon of the recentered cubic: {(0, L), (1, ∞), (2, t), (3, 0)}: vertex at 2 (since (L−t)/2 > t ⟸ L ≥ 3N > 3t at t ≤ N−1; **[r4] at t = N the parity clause supplies the strict inequality: L ≥ 3N with L − N odd forces L ≥ 3N+1 > 3N = 3t**); left side length 2, slope (L−t)/2 with odd numerator — an e = 2 irreducible block — plus the slope-t simple root: σ_B = {(2,1),(1,1)}.
> In every case F_A ≡ F_B ≡ the member mod π^N (all correction terms sit at heights ≥ N — at t = N the B-terms included), both lifts have disc ≠ 0 **[r4: proved below in EVERY characteristic; the sealed warrant "distinct irreducible factors, étale" is a characteristic-0 reflex — in char p an e = p side can be purely inseparable, which is exactly how the deleted branches failed]**, and σ_A ≠ σ_B (three unramified pieces vs an e = 2 block). So every member of the species is genuinely σ-ambiguous — two disc ≠ 0 lifts with different σ, i.e. undecided in the S1 pinned sense. Count: q centers × q^{N−1} free b₂ (b₂ = 0 included, now via t = N). ∎”

**RESOLUTION TRACE:** Base §S3.2, lines 837–871, with `[r4]` F1's three brackets landed in place.

**TEETH:** Battery family W12-DRAIN3 (“every species member classified undecided, count = q^N per row”) and W12-ORACLE's 85 constructed witness pairs — the latter scoped by `[r5]` MINOR 3 (shard 2) to the 70 `b₂ ≠ 0` pairs.

---

### EFF.W12.39  [lemma]

**CANONICAL STATEMENT:** `[r4]` SEPARABILITY OF THE REPAIRED PAIR, EVERY CHARACTERISTIC

> “**[r4] SEPARABILITY OF THE REPAIRED PAIR, EVERY CHARACTERISTIC** (the warrant the sealed proof outsourced to "étale"; write y = x − c, so F_A = y·(y² + By + π^{2K+1}) and F_B = y³ + By² + π^L with v(B) = t ∈ [1, N], 2K+1 ≥ max(N, 2t+2), L ≥ 3N, L − t odd):
>
> * **F_A.** disc(y² + By + π^{2K+1}) = B² − 4π^{2K+1} has valuation EXACTLY 2t in every case: in equal characteristic 2 the second term vanishes (4 = 0) leaving B² ≠ 0; otherwise v(4π^{2K+1}) ≥ 2K+1 ≥ 2t+2 > 2t = v(B²). With Res(y, y²+By+π^{2K+1}) = π^{2K+1} ≠ 0, disc F_A = (B² − 4π^{2K+1})·π^{2(2K+1)} ≠ 0. The two O-roots come out characteristic-freely too: y = π^t z gives π^{2t}(z² + uz + π^{2K+1−2t}) with u := B/π^t a unit and 2K+1−2t ≥ 2, whose derivative 2z + u is a UNIT at both z ≡ 0 and z ≡ −u (in char 2 it IS u), so Hensel yields roots of valuations t and 2K+1−t as the polygon says. σ_A = {(1,1)³}.
> * **F_B.** y = π^t s gives π^{3t}·g(s), g(s) = s³ + us² + π^{L−3t} with u := B/π^t a unit and L − 3t ≥ 1 ODD (= (L−t) − 2t). Then g(−u) = π^{L−3t} and g′(−u) = 3u² − 2u² = u², a UNIT in EVERY characteristic (char 3: 3u²−2u² = u²; char 2: 3u² = u², 2u² = 0), so v(g(−u)) = L−3t > 0 = 2v(g′(−u)): Hensel gives one root s ≡ −u, i.e. ONE O-root of F_B at valuation t, and the complementary quadratic factor's roots sit at v(s) = (L−3t)/2 ∉ ℤ (odd numerator) — an irreducible e = 2 block, coprime to the O-root factor. σ_B = {(2,1),(1,1)}. Separability: in MIXED characteristic the fraction field has characteristic 0, so distinct irreducible factors are automatically étale; in EQUAL characteristic p, F_B(0) = π^L ≠ 0 and F_B′ = 3y² + 2By, so at p = 2, F_B′ = y² ⟹ gcd(F_B, F_B′) = 1; at p = 3, F_B′ = 2By ⟹ the same; at p ≥ 5 the roots of F_B′ are 0 and −2B/3 with F_B(−2B/3) = (4/27)B³ + π^L ≠ 0 (valuations 3t < L) ⟹ gcd = 1. Uniformly, disc F_B = −4B³π^L − 27π^{2L}: a unit times π^{2L} in equal char 2 (27 odd), a unit times B³π^L in equal char 3 (−4 = −1 ≠ 0) — nonzero in both.”

**CONDITIONALITY:** Unconditional in every characteristic, at the stated parameter constraints (`v(B) = t ∈ [1, N]`, `2K+1 ≥ max(N, 2t+2)`, `L ≥ 3N`, `L − t` odd).

**DERIVATION:** As displayed: discriminant valuations computed case-by-case, Hensel legs with unit derivatives exhibited in each characteristic, `gcd(F, F′) = 1` checked at `p = 2`, `p = 3`, `p ≥ 5` separately.

**RESOLUTION TRACE:** Base §S3.2, lines 873–904.

**TEETH:** The `[r4]` repair's fresh instrument: “for p = 2,3,5,7 at N = 2,3,4 … gcd(F, F′) = 1 and disc ≠ 0 in EVERY case, at the predicted valuations”, plus the mixed-characteristic re-check over `ℤ₂, ℤ₃, ℤ₅` (`.40`).

---

### EFF.W12.40  [changes-record]

**CANONICAL STATEMENT:** `[r4]` F1 REPAIR RECORD — the deleted branches, and the honest battery-invisibility disclosure

> “*What the deleted branches did.* With B = 0 the same computations FAIL: Lift 1 becomes y(y² + π^{2K+1}) whose quadratic has disc = −4π^{2K+1} = 0 in equal characteristic 2 — it is (y + π^{(2K+1)/2})² over the closure, a purely inseparable e = 2 = p side, and gcd(F_A, F_A′) = y² + π^{2K+1} ≠ 1 — so the sealed σ_A = {(1,1),(2,1)} does not exist there; and Lift 2 becomes y³ + π^L whose derivative is ≡ 0 in equal characteristic 3 (disc = −27π^{2L} = 0, F_B = (y + π^{L/3})³), so the sealed σ_B = {(3,1)} does not exist there. The repaired construction never has B = 0.”

> “**[r4] F1 REPAIR RECORD (PE4 @ 26689da, FINDING 1 CRITICAL, proof-level; LEMMA W12-S3.2's STATEMENT and count are byte-unchanged).** What was at stake: for the q members per row with b₂ = 0 over F_q[[t]] with p ∈ {2,3} the sealed proof established nothing, so the bound degraded to U₃^TRP ≥ q^N − q there — denting THEOREM W-12.C's displayed q^N ≤ U₃^TRP(q,N) and the BOX-3 annex's inherited q^N ≤ U₃^σ in equal characteristic 2/3 ONLY. With B = π^N both stand at q^N in every characteristic, and nothing downstream moves (no count, no law, no other lemma consumed the B = 0 branches).”

> “**Battery-invisibility, stated honestly:** the σ-witness leg (W12-ORACLE) builds the pairs only on the mixed-characteristic ℤ_p rows (W12-BOX-6: "PARI legs are mixed-characteristic only"), and in mixed characteristic BOTH sealed B = 0 witnesses are perfectly good (disc(y²+p^{2K+1}) = −4p^{2K+1} ≠ 0, disc(y³+p^L) = −27p^{2L} ≠ 0) — so the defect was invisible to the sealed instrument BY CONSTRUCTION, not by an instrument bug; no battery number changes (W12-DRAIN3's q^N per row is a READER-verdict count, not a witness claim), and the runner + artifacts stay BYTE-FROZEN at seal f669cb0.”

> “**Machine evidence for the repaired pair, in the vein the frozen kit does not cover:** PE4's fresh leg showed the sealed witnesses inseparable over F₃[t] (F_B′ ≡ 0) and F₂[t] (gcd(F_A, F_A′) = y²+t⁵ ≠ 1) and the B = π^N pair separable in both — those equal-characteristic rows are now the machine evidence for this lemma. This repair re-verified the repaired pair independently (fresh instrument, sympy over GF(p)[t] and ℤ): for p = 2,3,5,7 at N = 2,3,4 with 2K+1 = 2N+3 and L = whichever of {3N+1, 3N+2} makes L−N odd, gcd(F, F′) = 1 and disc ≠ 0 in EVERY case, at the predicted valuations — disc F_A = t^{2N+2(2K+1)} in char 2 (t^18 at N = 2), disc F_B = t^{2L} in char 2 (t^14 at N = 2, L = 7) and −t^{3N+L} in char 3 (−t^13) — plus the Hensel legs: the quadratic's roots have valuations exactly N and 2K+1−N in F₂[[t]], and g(s) = s³+s²+t^{L−3N} has its unit-derivative root at s ≡ −1 in F_p[[t]] for p = 2,3,5 (residual 0 to precision t^{6N+12}), giving F_B's O-root at valuation N. Mixed characteristic re-checked over ℤ₂, ℤ₃, ℤ₅ (π = p, v(p) = 1): disc ≠ 0 throughout, valuations 2N+2(2K+1) for F_A and 2L (p = 2) / 3N+L (p = 3, 5) for F_B.”

> “The trivial upper bound: U₃^TRP ≤ #TRP stratum = q·q^{3(N−1)} = q^{3N−2}. Both W-12.C bounds stand. ∎”

**CONDITIONALITY:** A proof-level CRITICAL repair with statement and count byte-unchanged. The frozen instrument's 85 witness pairs remain scoped: they are true facts about the witnesses built, silent on the repaired pair (`[r5]` MINOR 3, shard 2).

**DERIVATION:** The failure of the deleted branches is exhibited explicitly in each bad characteristic; the repaired pair's warrant is `.39`.

**RESOLUTION TRACE:** Base §S3.2, lines 906–963, with the machine-scope bracket at the S3.2 machine line.

**TEETH:** The fresh equal-characteristic instrument (sympy over `GF(p)[t]` and `ℤ`) is the machine evidence; the frozen kit is disclosed as structurally blind here.

---

### EFF.W12.41  [lemma]

**CANONICAL STATEMENT:** §S3.3 — the general-n lower bound

> “At every n ≥ 3: pick the level-0 pattern (x−c̄)²·h̄ with h̄ monic irreducible of degree n−2, h̄ ≠ x−c̄ (such h̄ exists over every F_q at every degree: for n−2 ≥ 2 irreducibles of that degree are non-linear; for n−2 = 1 take a second linear, q ≥ 2). By LEMMA W12-S2.1, decidedness is branchwise and the h̄-branch is simple (decided); by W-11's drainage law the double-root branch has q^{N−1} σ-undecided members per center. Fibering (S2.1 bijection):
>
>     undecided(n, q, N) ≥ q^{N−1}·q^{(n−2)(N−1)} = q^{(n−1)(N−1)}
>
> — one pattern already suffices (n = 2: W-11's law itself). ∎ (The census-weighted refinement — summing over admissible h̄ — follows the same way; the one-pattern form is all W-12.B's order-tightness needs.)”

**CONDITIONALITY:** A lower bound only; it establishes W-12.B's rate is correct-in-order **wherever the conjecture holds**, not that it holds.

**DERIVATION:** One level-0 pattern, branchwise decidedness (`.21`), W-11's per-center drainage, and the S2.1 fibering.

**RESOLUTION TRACE:** Base §S3.3, lines 967–979. Classified `[r3]`-parse-ROBUST (valid under both σ notions) at `.16`.

**TEETH:** Implied by W12-DRAIN3's species row at n = 3; no dedicated general-n row.

---

### EFF.W12.42  [lemma]

**CANONICAL STATEMENT:** §S3.4 Step 1 — rationality

> “*Step 1 (rationality).* For one family F with P_F a shifted product Π_{i=1}^{d_F}(a_i + b_iℤ_{≥0}) and dens_F = c_F(q)·q^{−ℓ_F}, ℓ_F = m₀ + Σ m_ix_i with m_i > 0:
>
>     Σ_{x ∈ P_F} dens_F(x) = c_F(q)·q^{−m₀−Σm_ia_i}·Π_i (1 − q^{−m_ib_i})^{−1} ∈ ℚ(q)
>
> by d_F iterated geometric series (absolutely convergent: q ≥ 2, m_ib_i ≥ 1).”

with its two guards, both landed as dated brackets:

> “[r1 m1, two guards: coordinates with step b_i = 0 — point coordinates, which (A1)'s "arithmetic progressions" does not exclude — are absorbed (fold m_ia_i into m₀ and delete the coordinate) BEFORE applying the display, whose i-th factor would otherwise divide by zero while the sum is trivially finite; the product runs over the coordinates with b_i ≥ 1. And [r2, PE2 FINDING 3: the r1 clause claimed the m_i themselves are integers by a FALSE implication — ℓ(x) = (x+1)/2 on 1 + 2ℤ_{≥0} is integer-valued with strictly positive coefficient and m₁ = 1/2] the exponents the display actually uses ARE integers: ℓ_F integer-valued on P_F gives m_ib_i ∈ ℤ_{>0} (evaluate at x and at x + b_ie_i and subtract; positivity from m_i > 0, b_i ≥ 1) and m₀ + Σm_ia_i = ℓ_F(base point) ∈ ℤ — which is all the display needs (its ratio exponents are the m_ib_i, its leading exponent is ℓ_F(base)) — so each factor is a bona fide element of ℚ(q). Every in-note P_F has b_i ∈ {1, 2}; point families enter the n = 2 instance as d_F = 0 families.] Finite unions of shifted products: inclusion–exclusion (intersections are again shifted products or empty). Finitely many families: finite sums stay in ℚ(q). By (A1)'s q-independence clause the resulting R_τ is ONE rational expression, the same at every prime power and characteristic.”

**CONDITIONALITY:** The final sentence rests on (A1)'s q-independence clause — **which is exactly the clause the 2026-08-12 correction rewrites** (`.12`). The append re-derives Step 1 under the corrected hypothesis and reaches the same conclusion:

> “**Derivation of Step 1 under the corrected hypothesis.** … Therefore \[ \sum_{x\in P_F}\operatorname{dens}_F(x) = c_F(q)q^{-\ell_F(a)} \prod_i(1-q^{-m_ib_i})^{-1}, \] which is the evaluation at \(X=q\) of \[ c_F(X)X^{-\ell_F(a)} \prod_i(1-X^{-m_ib_i})^{-1}\in\mathbb Q(X). \] Finite unions follow by inclusion–exclusion, and the finite sum over families remains in \(\mathbb Q(X)\). This proves both rationality and the “same expression at every prime power” conclusion.”

**DERIVATION:** Iterated geometric series with the two guards (b_i = 0 absorption; integrality of the exponents actually used), then inclusion–exclusion and finite summation.

**RESOLUTION TRACE:** Base §S3.4, lines 983–1011, with `[r1]` m1 and `[r2]` FINDING 3 landed in place; the concluding q-independence step re-derived at the 2026-08-12 (A1) correction.

**TEETH:** The n = 2 instance's series are re-verified symbolically in-note (`.44`).

---

### EFF.W12.43  [lemma]

**CANONICAL STATEMENT:** §S3.4 Steps 2–4 — the limit, the partition, and the classical tie

> “*Step 2 (R_τ is the decided-core limit).* D_τ(N) := Σ_{σ_F = τ, x visible} count(F, x) = q^{nN}·Σ_{x visible} dens_F(x) by (A1) exactness and disjointness. The visible sets {x : ν_F(x) ≤ N} increase to P_F (ν_F affine), so D_τ(N)/q^{nN} is a monotone partial-sum net of the positive convergent series of Step 1: D_τ(N)/q^{nN} → R_τ(q).”

> “*Step 3 (Σ_τ R_τ = 1).* Σ_τ D_τ(N) + r(N) = q^{nN} by (A1) disjointness and (A2)'s definition of r; divide by q^{nN}, let N → ∞, apply (A2).”

> “*Step 4 (the classical tie).* μ_τ := Haar density of {F ∈ O[x] monic degree n : disc F ≠ 0, splitting type τ} (well-defined: the τ-loci are open by Krasner on the étale locus and partition it; disc = 0 is a null set; Haar = the product measure on coefficients, and a window-N class is a union of cylinders of mass q^{−nN} each). Lower bound: the visible decided-τ classes at window N are disjoint cylinder unions all of whose disc ≠ 0 lifts have type τ (**[r4, PE4 F2] (A1)'s σ-LABELING clause: every member of every class (F, x) with σ_F = τ is σ-DECIDED with forced σ = τ, so all its disc ≠ 0 lifts have type τ — this is the whole content the lower bound consumes, and it is now hypothesised rather than read off (A0)'s "the read's type"; (A0) is the same statement in its well-posedness phrasing**): μ_τ ≥ D_τ(N)/q^{nN}. Upper bound: a type-τ F with disc ≠ 0 truncates into SOME window-N class — either a visible core class, which is then necessarily a τ one (by (A0) applied to F itself: F is a disc ≠ 0 lift of its own truncation **[r5, PE5 m1: route this through (A1)'s [r4] σ-LABELING clause, as the STEP-4 RE-CHECK in the [r4] FINDING-2 record already does — the clause says every disc ≠ 0 lift of every member of every visible core class has type σ_F, and that is what is applied here, at F over its own truncation. Post-[r4], (A0) is the same statement in its well-posedness phrasing, i.e. redundant-but-retained: it is not the load-bearing warrant at either bound]**), or into the rest: μ_τ ≤ (D_τ(N) + r(N))/q^{nN}. Let N → ∞: both bounds → R_τ(q) by Steps 2 and (A2): μ_τ = R_τ(q). ∎”

**CONDITIONALITY:** Both Step-4 bounds consume (A1)'s σ-LABELING clause and nothing else σ-flavoured (`.19`); (A0) is redundant-but-retained. The classical inputs (Krasner-openness, the τ-partition of the étale locus, the disc = 0 null set) are cited as classical and displayed.

**DERIVATION:** As quoted — monotone convergence for Step 2, the (A1)/(A2) partition for Step 3, and the two-sided cylinder estimate for Step 4.

**RESOLUTION TRACE:** Base §S3.4, lines 1013–1046, with `[r4]` F2's lower-bound bracket and `[r5]` m1's upper-bound routing landed in place.

**TEETH:** NONE (classical measure argument); its non-vacuity check is the n = 2 firing at `.44`.

---

### EFF.W12.44  [instance-record]

**CANONICAL STATEMENT:** §S3.4 — the n = 2 instance (fires unconditionally), with the tail routed honestly

> “**The n = 2 instance (fires unconditionally), with the tail routed honestly.** Core families: SEP-SPLIT, SEP-INERT (point families), RAM(h) (P = 1 + 2ℤ_{≥0}, dens (q−1)q^{−h−1}, ν = h+1), 2SIDED(w₁,w₂) ({1 ≤ w₁ < w₂}: the shifted-product image (w₁,δ) ∈ (1+ℤ_{≥0})×(1+ℤ_{≥0}), w₂ = w₁+δ; dens (q−1)²q^{−w₁−w₂−2}), SPLITEQ(k), INERTDEEP(k) ({k ≥ 1}) — exact laws, disjointness, and q-uniform data by THEOREM W-11(i)(ii); (A0) by W-11's decidedness (+ its sealed double-lift oracle leg). SPLIT-TAIL is NOT a core family (its count (q−1)q^{N−1} per center per w is not dens·q^{2N} with N-free dens): it routes through (A2): r(N) = undecided + tail = q^N + q·⌊(N−1)/2⌋·(q−1)·q^{N−2} = O(N·q^N), and r(N)/q^{2N} → 0 by W-11 clause (iii) + the tail law. *(Display note: (A2) is phrased as drainage of the REST — not of the σ-undecided residue alone — exactly so that window-boundary families route through it; an (A1)-only reading would make the n = 2 instance-check incomplete.)* Steps 1–4 then re-derive, through the general mechanism:
>
>     R_split = (q−1)/(2q) + 1/(q²(q+1)) + (q−2)/(2q²(q+1)) = q/(2(q+1))
>               [SEP + 2SIDED + SPLITEQ]
>     R_inert = (q−1)/(2q) + 1/(2q(q+1))                    = q/(2(q+1))
>               [SEP + INERTDEEP]
>     R_ram   = Σ_{h odd} (q−1)q^{−h−1}                     = 1/(q+1)
>     Σ_τ R_τ = 1 ✓
>
> — W-11's densities recovered: the reduction is non-vacuous and instance-checked. (Series re-verified this session: Σ 2SIDED = (q−1)²q^{−2}·Σ_{w₁≥1}q^{−2w₁}/(q−1) = 1/(q²(q+1)); Σ SPLITEQ = (q−1)(q−2)/2 · q^{−2}/(q²−1) = (q−2)/(2q²(q+1)); Σ INERTDEEP = (q−1)/2 · q^{−1}/(q²−1) = 1/(2q(q+1)); the R_split bracket: (q−1)/(2q) + (2+q−2)/(2q²(q+1)) = ((q−1)(q+1)+1)/(2q(q+1)) = q/(2(q+1)).)”

**CONDITIONALITY:** Unconditional at n = 2 — the hypotheses are W-11's theorems. The display note is a load-bearing scoping remark: (A2) must drain the REST, not just the σ-undecided residue, or this very instance-check fails.

**DERIVATION:** The six core families with their laws from W-11(i)(ii), the tail routed to (A2), then Steps 1–4; every series re-verified symbolically in-session.

**RESOLUTION TRACE:** Base §S3.4, lines 1048–1078.

**READING NOTE:** the 2026-08-12 (A1) correction is what makes this instance *literally* satisfy (A1): the n = 2 coefficients `q−1` and `(q−1)/(2q)` are q-dependent, hence admissible only as evaluations of fixed rational functions `c_F(X)` — “the literal conflict with the q-dependent n = 2 coefficients confirmed” (that append's verification note).

**TEETH:** The three densities match W-11's proved values exactly; W12-L0HIST ties the history-resolved forms to the sealed W-11 predictor.

---

### EFF.W12.45  [scope-record]

**CANONICAL STATEMENT:** §S3.4 — Conditionality at n ≥ 3, displayed montes-style

> “**Conditionality at n ≥ 3, displayed montes-style.** (hMenu-3) = the complete n = 3 core menu: the order-1 layer is supplied by W-12.A (S2.4's seven TRP families — note their parameter sets and laws are q-uniform shifted-product data, so (A1)-admissible — plus the DBL transport of the entire n = 2 menu via W12-L1/W12-L0); MISSING: the TRP refinement families (depth ≥ 1) — W12-BOX-2. (hExhaust-3) = (A2) at n = 3: the σ-undecided DBL part is proved (S3.1); and [r2, PE2 FINDING 2 — displaying the one remaining r(N) leg, previously undisplayed] the DBL BOUNDARY-TAIL families — the transported SPLIT-TAIL (σ-DECIDED split-certified; their count is N-dependent, dens would be (q−1)²q^{−N−2}, hence they lie in NO (A1)-admissible family) — route through (A2) exactly as SPLIT-TAIL does at n = 2, with vanishing mass ⌊(N−1)/2⌋·(q−1)²·q^{2N−2} (= q(q−1) patterns × W12-L1(c)'s q^{N−1} simple-branch fiber × W12-L0's SPLIT-TAIL row, per-w aggregate (q−1)²q^{2N−2}, over the ⌊(N−1)/2⌋ values of w; re-verified against the committed JSON on ALL 23 cubic rows this repair, e.g. (Zp,2,5): 256+128+128 = 512, exact zeros at N = 2 included), /q^{3N} → 0; MISSING: a vanishing U₃^TRP upper bound — W12-BOX-3 (whose conservative-convention bound also drains the TRP members σ-decided only by tail certification: those are conv-UNDECIDED by construction, so no TRP tail leg is separately owed). At n ≥ 4 additionally [W12-H] (W12-BOX-1) at composite stages. No other conditionality: (A0) at the order-1 decided shapes is S2.3's Ore argument **[r5, PE5 m1: stated exactly — what the order-1 decided shapes must supply is (A1)'s [r4] σ-LABELING clause (every member of every visible core class σ-DECIDED with forced σ = σ_F, i.e. at all its disc ≠ 0 lifts), since that is what BOTH Step-4 bounds consume; S2.3's Ore argument is what PROVES that clause at the order-1 layer, and (A0) is the same statement in its well-posedness phrasing]**.”

**CONDITIONALITY:** THIS unit is the conditionality vocabulary for n ≥ 3: exactly `{(hMenu-3)} + {(hExhaust-3)}` at n = 3, plus `[W12-H]` at n ≥ 4. Both n = 3 legs are DISCHARGED at composition grade by the two out-of-range annexes; the closing “No other conditionality” sentence is routed through (A1)'s σ-labeling clause by `[r5]` m1.

**DERIVATION:** Leg-by-leg accounting of `r(3, N)`: the DBL σ-undecided term is proved (`.36`), the DBL boundary-tail mass is computed and shown vanishing, and only the `U₃^TRP` upper bound is missing.

**RESOLUTION TRACE:** Base §S3.4, lines 1080–1109, with `[r2]` FINDING 2 and `[r5]` m1 landed in place.

**TEETH:** The boundary-tail mass re-verified against the committed JSON on all 23 cubic rows (worked example `(Zp,2,5): 256+128+128 = 512`, with the `N = 2` exact zeros).

---

### EFF.W12.46  [scope-record]

**CANONICAL STATEMENT:** §S4.1 — Consumed at PROVED strength

> “* **THEOREM W-11(n = 2)** — the complete menu + exact drainage + the S2.3 refinement isomorphism: consumed at pin (S2.6, S2.7, S3.4 instance).
> * **THEOREM W-10(2,1,1)** — the digit-calculus template (S2.2 is its all-degrees generalization; the (2,1,1) row is the m = 2, d = 1, one-side instance) and the recentering mechanics.
> * **LEMMA J-D0** — the shape-keying/count-gauge-blindness FRAME: what makes clause (i) well-posed shape-only (S0 reason 1, S2.2's census remark, W12-L1(b)'s unit-scaled letters). The order-1 proofs are self-contained elementary arithmetic, so J-D0 is corroborated at every new instance and load-bearing for the general-form framing.
> * **Classical inputs**: Hensel (coprime lifting, S2.1), Ore's theorem / GMN order-1 (S2.3), the finite-field factorization censuses (S2.2, re-derived + machine-checked).”

**CONDITIONALITY:** J-D0 is carried as a FRAME, not as a consumed theorem in the order-1 proofs (“the order-1 proofs are self-contained elementary arithmetic”) — the note is explicit that J-D0 is corroborated by them and load-bearing only for the general-form framing.

**DERIVATION:** Supplier inventory.

**RESOLUTION TRACE:** Base §S4.1, lines 1113–1128.

XREF: `lean/notes/openmath/W11_PROOF_2026-08-08.md:THEOREM W-11` — grep-verified count **3**; `S2.3` — count **8**.

XREF: `lean/notes/openmath/W10_PROOF_2026-08-08.md:THEOREM W-10` — grep-verified count **2**.

XREF: `lean/notes/openmath/JD0_PROOF_2026-08-08.md:LEMMA J-D0` — grep-verified count **4**.

**READING NOTE:** the classical-inputs row's “Ore's theorem / GMN order-1” is the `Q1 W12-2` retarget row of `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` (→ [GN15] Thm 2.3; verdict COVERS-ALL-O). Recorded, not applied.

**TEETH:** W12-PIN (md5 pins on the five frozen imports, incl. the W-11 instrument at `500aae15…`).

---

### EFF.W12.47  [hypothesis]

**CANONICAL STATEMENT:** §S4.2 — THE DISPLAYED HYPOTHESIS BOX `[W12-H]` (orders ≥ 2), five named inputs

> “The general clause (i) at orders ≥ 2 — shapes with repeated residual factors of degree ≥ 2, i.e. towers whose key polynomials have degree > d — is CONDITIONAL on the following FIVE named inputs [r1: the sealed box said "on, exactly:" over FOUR members; PE1 F2 found the fifth (H-e) missing, and its further hunt found no sixth — the completeness of this list is PE1's verified negative, not asserted by fiat]:
> * **(H-a)** the JC composite-stage warrant (no-cancellation + level-detection of residual reads at wild composite stages; JC-PSIKER/JC-LOAD, GRTJC ACCEPTED 2/2 @ 83f47f4) — consumed as warrant, its own conditionality displayed there;
> * **(H-b)** the JB membership faces at unbounded abscissa grids (JB-VTX/JB-DEV; GRTJB ACCEPTED 2/2 @ 83f47f4 with row-12's u ≥ 0 proviso membership residue OPEN);
> * **(H-c)** the J-D1 (H1) residue-structure package of §S5 (the value-side dictionary at composite stages), conditional on the six weld notes' displayed boxes + the Σ-LAW residue;
> * **(H-d)** the universal residual censuses OVER RESIDUE TOWERS (S_λ over F_{q^d} with d the accumulated residue degree — the S2.2 censuses suffice level by level once (H-a)–(H-c) identify the reads);
> * **(H-e)** [r1, added at PE1 F2] the order-≥ 2 GMN LEAF/σ-DECISION theorem — the higher-order analogue of the Ore step clause (i) itself uses at order 1 (S2.3): separable order-r residual ⟹ σ-decided with (e, f) read off (the GMN order-r types theorem — a statement about exact polynomials over O — PLUS the (H-a)/(H-b)-leg in-window pinning of the consumed read data, the composite-stage analogue of S2.3's "All data the read consumes sit at heights ≤ N−1" sentence [r2, PE2 m1: the bare GMN cite under-priced the window-level statement]), which is exactly (A0) well-posedness at composite stages. S4.1's classical-inputs list is order-1 scoped ("Ore's theorem / GMN order-1"), so this input belongs HERE; W-12.D consumption at n ≥ 4 needs it at every composite-stage shape. If (H-c)'s FGMN-4.2 pairings are read as carrying it, that derivation is NOT displayed in this note — it is priced as its own member.”

> “No order-≥ 2 count law is CLAIMED here; [W12-H] is the priced route (W12-BOX-1). The λ = (1²) quartic stratum of S2.5 is the box's concrete frontier exhibit, volume law included.”

**CONDITIONALITY:** This IS the conditionality interface. Two facts about it are load-bearing downstream: the list's **completeness is PE1's verified negative** (no sixth input found), and `(H-e)` is **separately priced** — if (H-c) were read as carrying it, that derivation is not displayed here.

**DERIVATION:** Not derived — a hypothesis box, with each member's supplier and grade named.

**RESOLUTION TRACE:** Base §S4.2, lines 1132–1170, with `[r1]`'s fifth member and `[r2]` m1's window-level pricing landed in place. Out of range, the 2026-08-12 dated correction repairs W12-BOX-1's reference to this list from `(H-a)–(H-d)` to `(H-a)–(H-e)` (`.49`).

XREF: `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md:JC-PSIKER` — grep-verified count **19**; `JC-LOAD` — count **31**.

XREF: `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md:JB-VTX` — grep-verified count **77**; `JB-DEV` — count **63**.

XREF: `lean/notes/openmath/GRTW2_PROOF_2026-08-08.md:Σ-LAW` — grep-verified count **14**; the residue (H-c) is conditional on.

**READING NOTE (external, not an edit).** `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` row **Q1 W12-3** targets `(H-e)` by name — *“(H-e) … order-≥2 GMN LEAF/σ-DECISION theorem” | NS-3 | re-cite [GN15] Thm 2.3 / [AGNPRW] Thm 4.4 + Prop 4.5”* — with NS-3's verdict **COVERS-ALL-O** ([GN15] Thm 2.3 being simultaneously the order-1 and order-r statement, since µ ranges over all inductive valuations). Note this retarget addresses the CITED SOURCE's generality, not `(H-e)`'s status as a hypothesis of this note: `(H-e)` also carries the in-window pinning leg, which is not a literature citation.

**TEETH:** The `λ = (1²)` quartic stratum (`.31`) is the frontier exhibit with a proved volume law and an open σ-resolution.

---

### EFF.W12.48  [scope-record]

**CANONICAL STATEMENT:** §S5 — THE J-D1 FAITHFULNESS HANDOFF (the blueprint row's own content, at its S-price)

> “The blueprint's (J-D1), verbatim (GRT_WELD_BLUEPRINT_2026-08-08 §S2.4):
>
> > **(J-D1) THE FAITHFULNESS HANDOFF.** Under J-A/J-B/J-C, the accepted carry-law corpus proves the (H1) residue-structure package at orders ≥ 2: the anchored-march frame tie + residual dictionary ((GR-B)'s displayed content, both FGMN-4.2 pairings) hold at every realized composite stage of every classifier tower IN THE WELDED CLASS — i.e. GD-2/GD-3's one open input becomes a theorem there, and with it the GD-1 representative-admissibility and order-≥ 2 KEY1 members ((H1) members (b)/(d)) inherit the corpus's proofs where the dictionary reaches.”

> “**The composition, displayed (nothing re-proved).** All six weld notes are ACCEPTED 2/2 (ledger fold 17d2a32): GRTJA @ f131c53, GRTJB + GRTJC @ 83f47f4, GRTW2 @ adc6cf3, LIFTCORNER @ 08f61e9, WELDMASTER @ 66b3498. The W-0..W-9 rows therefore stand at those notes' displayed conditionality — the surviving open surface being W2-OPEN-2/OPEN-2a (since NARROWED to the Σ-LAW single lemma, OPEN2ATTACK verdict @ 4a970aa; forward direction at attempt grade GIVEN Σ-LAW) plus the notes' own boxed residues. THEREFORE, by the blueprint's own composition (displayed here, owned by the blueprint): the (H1) residue-structure package at orders ≥ 2 holds ON THE WELDED CLASS, conditional on exactly the union of the six notes' displayed boxes + the Σ-LAW residue. Consumers: the (H1) row's retirement path, then the IFK faces O-2/O-3 through the GD carriers — consumed DOWNSTREAM, owned by their own units, nothing of them owned here. What W-12's assembly takes from J-D1: (H-c) of [W12-H] — the order-≥ 2 layer's value-side warrant when that layer is composed; the order-1 layer proved in S2 needs NONE of it, which is why it could be proved outright now. (GR-B)'s RE-ACCEPTED print package is cited only as the row's named partial, at its own perimeter. This discharges the blueprint row AS THE DISPLAY IT PRICED (**S**, composition; conditional on IFK downstream). DULEMMA (@ 048cf6d/f819f26, perimeter e_m ≥ 2) is NOT consumed by any count law here (every order-1 count is a COUNT statement, not a (DMULT) statement — W-11 S3's fence inherited); it appears only in this weld-state display.”

**CONDITIONALITY:** A DISPLAY — “nothing re-proved”, and the (H1) conclusion is conditional on “exactly the union of the six notes' displayed boxes + the Σ-LAW residue”. The whole section is priced **S** (composition). Nothing in §§S2–S3 depends on it.

**DERIVATION:** The blueprint's own composition, executed at the accepted-supplier grades.

**RESOLUTION TRACE:** Base §S5, lines 1174–1209; untouched by later rounds.

XREF: `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md:(J-D1) THE FAITHFULNESS HANDOFF` — grep-verified count **1**.

XREF: `lean/notes/openmath/GRTW2_PROOF_2026-08-08.md:W2-OPEN-2` — grep-verified count **60**; `OPEN2ATTACK` — count **5**; `Σ-LAW` — count **14**.

XREF: `lean/notes/openmath/WELDMASTER_2026-08-08.md:WELD-M-PKG` — grep-verified count **5**; the WELDMASTER package cited in the six-note list.

XREF: `lean/notes/openmath/DULEMMA_PROOF_2026-08-08.md:DULEMMA` — grep-verified count **1**; declared NOT consumed by any count law.

**NON-IMPORT (explicit):** “DULEMMA … is NOT consumed by any count law here”; “Consumers: … consumed DOWNSTREAM, owned by their own units, nothing of them owned here.”

**TEETH:** NONE (composition display).

---

### EFF.W12.49  [open-obligation]

**CANONICAL STATEMENT:** §S6 — W12-BOX-1 (orders ≥ 2 = `[W12-H]`)

> “* **W12-BOX-1 (orders ≥ 2 = [W12-H]).** No count law at composite stages is claimed; the route is priced in S4.2 ((H-a)–(H-d)) and its frontier is exhibited (S2.5's λ = (1²) quartic stratum: volume law proved, σ-resolution open). The general W-10 (every decided shape, every order) remains OPEN — W10-BOX-1 stands untouched.”

**CONDITIONALITY — the dependency range is CORRECTED out of range** (2026-08-12, resolution rule 7):

> “In W12-BOX-1, the reference
>
> > “the route is priced in S4.2 ((H-a)–(H-d))”
>
> is corrected to
>
> > “the route is priced in S4.2 ((H-a)–(H-e)).”
>
> S4.2 explicitly enumerates five inputs. In particular, `(H-e)` is the order-\(\ge2\) GMN leaf/σ-decision theorem together with the in-window pinning supplied by `(H-a)` and `(H-b)`; it is separately load-bearing for the composite-stage analogue of S2.3 and for W-12.D's σ-labeling requirement. The correction changes no mathematical conclusion; it restores the box's dependency record to the five-input list already displayed in S4.2.”

**Effective reading:** `(H-a)–(H-e)`.

**DERIVATION:** Bookkeeping repair against S4.2's own five-member list (`.47`).

**RESOLUTION TRACE:** Base §S6, lines 1213–1217; corrected at lines 2143–2153.

XREF: `lean/notes/openmath/W10_PROOF_2026-08-08.md:W10-BOX-1` — grep-verified count **1**; the general W-10 box declared untouched.

**TEETH:** The `λ = (1²)` quartic stratum's measured volume (W12-QRT) is the frontier exhibit.

---

### EFF.W12.50  [open-obligation]

**CANONICAL STATEMENT:** §S6 — W12-BOX-2, W12-BOX-3, W12-BOX-4 (the menu and drainage boxes)

> “* **W12-BOX-2 (n ≥ 3 refinement families; (hMenu-3)).** The depth-≥ 1 TRP families are not enumerated: the n = 3 instance bracket needs TWO node species — (α) the triple-cluster node and (β) the DBL-re-entry node at reduced window (S3.1) — and neither species' transfer law is derived. W-12.D at n = 3 is conditional on this menu; it is the natural W-13 rung, with S2.4's depth-0 completeness as its floor.
> * **W12-BOX-3 (U₃^TRP; (hExhaust-3)).** The exact triple-center drainage law is not derived; obstruction: the same two-species node calculus, plus a TRP tail-σ-certification lemma (the n = 3 SPLIT-TAIL analogue: a visible deep vertex can certify a split-off (1,1) piece even with b₀ window-hidden), which this note's instrument deliberately does NOT attempt: the battery's TRP reader certifies NO tail σ (conservative convention, disclosed in the runner), so its measured U₃^TRP is an UPPER count for the σ-convention residue — EXPLORATORY grade, no closed form preregistered. The proved content is the pair of bounds (S3.2 + trivial).
> * **W12-BOX-4 (n ≥ 4 drainage).** No upper bound at any grade; lower bounds only (S3.3). W-12.B is a conjecture with two proved instances of its shape (n = 2 exact; n = 3 DBL term exact).”

**CONDITIONALITY:** BOX-2 and BOX-3 are the two `(hMenu-3)`/`(hExhaust-3)` legs of W-12.D's n = 3 firing. Both are **DISCHARGED at composition grade** by the two verbatim annexes homed in shard 2 (HEX3 → BOX-3; HMENU3 → BOX-2), leaving the residual tail-σ-certification lemma open as HEX3-BOX-1. BOX-4 is untouched: no n ≥ 4 upper bound at any grade.

**DERIVATION:** Each box names its own obstruction; the derivations of the obstructions are `.37` (two species) and `.30` (depth-0 floor).

**RESOLUTION TRACE:** Base §S6, lines 1218–1238; BOX-2 discharged at ANNEX 2, BOX-3 at the BOX-3 ANNEX (both shard 2).

XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:COROLLARY HM3.D` — grep-verified count **11**; the discharge's downstream payoff (five cubic `R_τ(q)`, `Σ = 1`).

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:COROLLARY HEX3.C` — grep-verified count **8**; the characteristic-independence corollary that explains the battery's cross-characteristic observation.

**TEETH:** W12-DRAIN3's `U₃^TRP` row is EXPLORATORY by construction — it is the note's own statement that this box has no confirming machine row.

---

### EFF.W12.51  [definition]

**CANONICAL STATEMENT:** §S6 — W12-BOX-7 (σ-convention at the TRP tail), the pinned notion

> “* **W12-BOX-7 (σ-convention at the TRP tail).** Decided = certified on window digits for all disc ≠ 0 lifts; the DBL side inherits W-11's proved convention (incl. its SPLIT-TAIL certification); the **battery's [r4, PE4 m1: one scope word — post-r3 there is exactly ONE definitional notion, clause 1's lift certification, and the conservative reader is a MEASUREMENT convention (as the runner docstring itself discloses); the sealed "the TRP side uses …" read definitionally would assert UNDECIDED (this clause) and DECIDED (clause 1) at once for a lift-certified TRP deep-tail member]** TRP reader uses the BOX-3 conservative convention. The two conventions can disagree only on deep-tail TRP members; the battery reports the measured TRP residue per row.”

**CONDITIONALITY:** THE definitional anchor of the σ-pin (`.08`). Post-`[r4]` m1 there is exactly **one** definitional notion (clause 1's lift certification); the conservative reader is a MEASUREMENT convention only. Without that scope word the box would have asserted DECIDED and UNDECIDED simultaneously for a lift-certified TRP deep-tail member.

**DERIVATION:** The one-word scope repair is justified by the contradiction it removes, displayed in the bracket itself.

**RESOLUTION TRACE:** Base §S6, lines 1255–1266, with `[r4]` m1 landed in place.

**TEETH:** The runner docstring's own disclosure of the conservative convention as a measurement convention (“correct as sealed”, per `.16`'s sweep class (c)).

---

### EFF.W12.52  [fence]

**CANONICAL STATEMENT:** §S6 — W12-BOX-5, W12-BOX-6, W12-BOX-8 (instrument, coverage, and no-symmetry fences)

> “* **W12-BOX-5 (classifier reimplementation; lift convention).** The battery's cubic/quartic readers are convention-faithful reimplementations (W10-BOX-3/W11-BOX-3 inherited); the engine tie rides the accepted JB-VTX face + the SEALED W-11 instrument consumed by md5-pinned import (the W12-L1X seam is machine-checked pointwise). The Lean `omCount` evaluator remains order-0; growing it is Phase-B code (W-11 S4.1's spec now extends to every degree via W-12.A). Lift-convention independence of the member SET at deep shapes is the W-2/LIFTCORNER seam, not consumed (S2.2 convention note).
> * **W12-BOX-6 (oracle coverage).** PARI legs are mixed-characteristic only; eq-char rows are SAME-class evidence; no mixed-characteristic prime-power rows exist in the frozen kit (W10-BOX-4/W11-BOX-4 inherited verbatim). Quartic rows enumerate the quadruple-center stratum only (the QRT laws are stratum laws; no quartic drainage/partition claim exists to test).
> * **W12-BOX-8 (no FE / no symmetry claim).** Nothing here touches `htameFE`; the n = 2 split = inert window symmetry is not asserted at n ≥ 3 (the τ-lattice is richer; no per-window symmetry is claimed or expected).”

**CONDITIONALITY:** BOX-6 is the fence that made the `[r4]` F1 defect structurally invisible to the sealed instrument (`.40`) — it is load-bearing evidence-scoping, not boilerplate.

**DERIVATION:** Instrument and coverage audit.

**RESOLUTION TRACE:** Base §S6, lines 1239–1254 and 1267–1270.

XREF: `lean/notes/openmath/W10_PROOF_2026-08-08.md:W10-BOX-3` — grep-verified count **1**; `W10-BOX-4` — count **1**.

XREF: `lean/notes/openmath/W11_PROOF_2026-08-08.md:W11-BOX-3` — grep-verified count **1**; `W11-BOX-4` — count **2**.

XREF: `lean/LeanUrat/OM/RealInstanceV2.lean:htameFE` — grep-verified count **9**; the capstone hypothesis this note explicitly does not touch.

**NON-IMPORT (explicit):** `htameFE` untouched; no `n ≥ 3` window symmetry claimed; the lift-convention member-set seam not consumed; no quartic drainage/partition claim exists.

**TEETH:** W12-PIN (md5-pinned imports) and the W12-L1X seam check.

---

### EFF.W12.53  [battery-frame]

**CANONICAL STATEMENT:** §S7 — the sealed battery, runner and evidence classes

> “**Runner:** `verification/openmath/w12_checks.py`. Exact arithmetic, no floats; deterministic; PARI/GP subprocess for the IND legs.”

> “**Families** (evidence class per row: IND = independent engine; SAME = this runner's own arithmetic/prediction recursion; NONE = bookkeeping):”

**CONDITIONALITY:** The three-way evidence classing is the battery's own honesty device: only the ORACLE family is IND (an independent engine); everything else is SAME (this runner's own arithmetic) or NONE (bookkeeping). No SAME row is evidence against an implementation error shared with the predictor.

**DERIVATION:** Instrument declaration.

**RESOLUTION TRACE:** Base §S7, lines 1274–1278.

**READING NOTE:** the runner file `verification/openmath/w12_checks.py` exists in the repo (checked), as do the artifacts named at `.65`/`.69`.

**TEETH:** This unit frames the battery; the inverse table is §5.

---

### EFF.W12.54  [regression-record]

**CANONICAL STATEMENT:** §S7 — W12-PIN and the four SAME structural families

> “* **W12-PIN** [NONE] — md5 pins: w11_checks.py 500aae152bb5b5e9df3712904a6d73a6 (THE W-11 instrument, consumed at its sealed bytes), w10_checks.py a9c34244…, iterlawn_pe_reimpl.py cae45db2…, grt_jc_probe.py 03811b69…, jd0_checks.py d3a5e13d… (full md5s in the runner). Violation if moved.
> * **W12-LVL0** [SAME] — the five cubic level-0 pattern censuses C₀(q) per row + their sum q³.
> * **W12-SHAPE** [SAME] — every depth-0 decided TRP key == its S2.4 closed form, BOTH directions (an observed-but-unpredicted decided key is a violation — the completeness clause; a predicted-but-absent key likewise), exact zeros included (S_{(1,1)}(2) = 0, S_{(1,1,1)}(q≤3) = 0).
> * **W12-QRT** [SAME] — QRT-G2(h;(1,1)) and (h;(2)) laws + the (1²) composite-frontier volume, both directions, on the quadruple-center stratum.
> * **W12-L0HIST** [SAME] — every history-resolved n = 2 key (kind, params, hist) == the W12-L0 closed form on the quadratic rows; and Σ_H (my forms) == the SEALED W-11 aggregate predictor, key by key, on every cubic row's (q, N).”

**CONDITIONALITY:** W12-SHAPE and W12-QRT are BOTH-DIRECTIONS checks — the completeness clause makes an unpredicted decided key a violation, which is what turns shard 1's depth-0 completeness claim into a testable statement.

**DERIVATION:** Family definitions.

**RESOLUTION TRACE:** Base §S7, lines 1279–1297.

**TEETH:** These families ARE teeth rows; verdicts at `.70`.

---

### EFF.W12.55  [regression-record]

**CANONICAL STATEMENT:** §S7 — W12-BLOCK, W12-L1X, W12-DRAIN3

> “* **W12-BLOCK** [SAME] — the Hensel product identity g·l == f coefficient-exact per DBL member + fiber bijection (all (g, l) pairs distinct, cardinality = the pattern stratum).
> * **W12-L1X** [SAME] — the direct cubic read (FRESH arithmetic: root-scan residual typing, cubic shift with its s², s³ cross-terms) == the SEALED w11 classifier on the Hensel block: (kind, params, hist) pointwise on every DBL member of every cubic row.
> * **W12-DRAIN3** [SAME] — per cubic row: partition Σ == q^{3N} (bookkeeping); DBL-undecided == (q−1)q^{2N−1} EXACTLY (the THEOREM W-12.C leg); per-PATTERN per-key DBL counts == q^{N−1} × W12-L0 (letter-uniformity across all q(q−1) patterns); the S3.2 species: every member classified undecided, count == q^N; U₃^TRP measured and reported (EXPLORATORY, BOX-3 conservative convention disclosed in the runner; no closed form preregistered).”

**CONDITIONALITY:** W12-L1X is a **cross-implementation** check (fresh arithmetic vs the sealed W-11 classifier), so it is stronger than an ordinary SAME row; the `U₃^TRP` leg of W12-DRAIN3 is EXPLORATORY with no preregistered value.

**DERIVATION:** Family definitions.

**RESOLUTION TRACE:** Base §S7, lines 1298–1311.

**TEETH:** These families ARE teeth rows; verdicts at `.70`, `.71`.

---

### EFF.W12.56  [regression-record]

**CANONICAL STATEMENT:** §S7 — W12-ORACLE, with the three-genre disc = 0 disposition

> “* **W12-ORACLE** [IND] — PARI/GP σ MULTISET per decided cubic (factorpadic + per-factor nfinit/idealprimedec) on the Z_p oracle rows — separable-pattern, DBL-decided, and TRP-decided members all scored; exact integer disc == 0 ⟹ never decided (Python-exact disc, mixed bracket) [r1, warrant corrected at PE1 F4; r2, completed at PE2 FINDING 1 to the full THREE-GENRE disposition, keyed by the LEVEL-0 READ — the taxonomy the coverage cites actually act by — so no residual genre remains: a monic cubic over ℤ with disc = 0 is (x−a)²(x−b) with a ≠ b, DBL-read or TRP-read by whether ā ≠ b̄, or the exact cube (x−a)³.”

> “GENRE (i), a ≢ b (mod p): level-0 pattern (x−ā)²(x−b̄) with ā ≠ b̄ — covered by W-11's square-block case through W12-L1(c), the only genre that cite reaches (W12-L1's own fence is c̄ ≠ d̄, S2.7). GENRE (ii) [r2 — the PE2-new sub-genre; real and abundant, e.g. x²(x+14) at (Zp,2,4), a = 0 ≡ b = −14 mod 2]: a ≠ b but a ≡ b (mod p): level-0 pattern (x−ā)³ — a TRP read, which the cited pair structurally cannot cover (the S2.1 Hensel split into quadratic × linear branches does not exist for it); covered by the disclosed CONSERVATIVE CONVENTION: the TRP reader follows the double cluster — once the digits of a and b separate, the residual at the separation state is (z+ᾱ)²(z+β̄) (ᾱ ≠ β̄), and at every DEEPER state the refining side's residual is the SQUARE (z+γ̄)² [r3, PE3 MINOR 1: the r2 wording put (z+ᾱ)²(z+β̄) at every deeper state — the simple root peels off through a polygon vertex at separation; re-derived both characteristics in the PE3 report, substance unchanged] — never all-separable, refining forever on the exact-square block — and terminates only at v(b₀) ≥ N ⟹ UNDECIDED. GENRE (iii) [r1]: the exact cube (x−a)³, which NEITHER originally-cited lemma covers: its window member need not lie in the S3.2 species (recentered at the read's center c, b₁ = 3(c−a)² can stay window-visible while b₀ = (c−a)³ has left the window — e.g. v(c−a) = m with 3m ≥ N > 2m — and S3.2's proof needs b₁ = b₀ = 0 in-window); covered by the same CONSERVATIVE CONVENTION: the TRP reader's refine chain follows the triple root and terminates at v(b₀) ≥ N ⟹ UNDECIDED. In all three genres "reader never decides" holds — genres (ii) and (iii) ride the convention, not the cited pair]”

> “AMBIGUITY WITNESSES: for every S3.2 species member, the two constructed lifts F_A, F_B (exact integer polynomials per the S3.2 proof **[r5, PE5 m3: exactly — per the S3.2 proof at the b₂ ≠ 0 members (70 of the 85 pairs, where the runner's `B = b2` IS the proof's B); at the b₂ = 0 members (one per centre, q per row: 2+2+3+3+5 = 15 of the 85) the frozen runner builds the SEALED pair (B = 0), i.e. exactly the two branches [r4]'s FINDING 1 DELETED from the proof. Per the [r4] scope bracket at the S3.2 machine line: on these mixed-characteristic ℤ_p rows those lifts do have disc ≠ 0 with σ_A ≠ σ_B, so the oracle verdict is a TRUE fact about the witnesses the runner built — it is simply not evidence for the repaired (B = π^N) pair, whose warrant is the [r4] display]**) give σ_A, σ_B EQUAL TO their predicted values and σ_A ≠ σ_B; every decided QRT quartic member's σ per λ.”

**CONDITIONALITY:** Two disclosed limits: two of the three disc = 0 genres “ride the convention, not the cited pair”, and 15 of the 85 witness pairs are the sealed `B = 0` pair that `[r4]` deleted from the proof — true of the witnesses built, silent on the repaired pair.

**DERIVATION:** The three-genre taxonomy is derived from the level-0 read (the taxonomy the coverage cites actually act by), with a worked example for the PE2-new genre (ii) and a worked window-visibility scenario for genre (iii).

**RESOLUTION TRACE:** Base §S7, lines 1312–1363, with `[r1]`, `[r2]`, `[r3]` MINOR 1 and `[r5]` m3 all landed in place.

**TEETH:** IND family: PARI/GP is an engine independent of the runner's arithmetic.

---

### EFF.W12.57  [battery-frame]

**CANONICAL STATEMENT:** §S7 — the four TEETH

> “* **TEETH (each must fire ≥ 1 or the battery is RED):**
>   W12-T-SHAPE — the TRP-RAM3 law corrupted to (q−1)q^{3N−2h−1} must mismatch on every cubic row (RAM3(1) always visible at N ≥ 2).
>   W12-T-DRAIN — the DBL drainage term corrupted to (q−1)q^{2N−2} must mismatch on every cubic row.
>   W12-T-CENSUS4 — S_{(2)} corrupted to q(q−1) (the /2 dropped) must break QRT-G2(1,(2)) on every quartic row.
>   W12-T-SIGMA — QRT-G2(h,(2)) σ mis-keyed to {(4,1)} must be caught by PARI on every decided (2)-member of every quartic oracle row.”

**CONDITIONALITY:** Firing is mandatory — “a tooth not firing voids the battery, not the theorems” (P-9).

**DERIVATION:** Four planted mutations, each targeting a distinct claim (a TRP law, the drainage term, a census, a σ keying).

**RESOLUTION TRACE:** Base §S7, lines 1364–1372.

**TEETH:** All four fired at exactly-preregistered counts (`.73`).

---

### EFF.W12.58  [TABLE]

**CANONICAL STATEMENT:** [TABLE] §S7 — the row inventory

> “**CUBIC CENSUS ROWS (23).** Z_p: (p,N) ∈ {(2,3),(2,4),(2,5),(2,6),(2,7),(3,2),(3,3),(3,4),(5,2),(7,2)}; F_q[[t]]: (q,N) ∈ {(2,3),(2,4),(2,5),(2,6),(2,7),(3,2),(3,3),(3,4),(4,2),(4,3),(5,2),(8,2),(9,2)} — 7,105,774 monic cubics covered (unit: polynomials; separable-pattern lifts counted analytically after level-0 classification, per LEMMA W12-S2.1), of which 2,946,008 DBL/TRP lifts are read INDIVIDUALLY (unit: lifts; = Σ q^{3N−1}). The (2,7) rows exist to realize TRP-3LIN (minimal visibility u₀ = 6 ≤ N−1). **QUARTIC ROWS (8, quadruple-center stratum only).** Z_p: (2,3),(2,4),(2,5),(3,3); F_q[[t]]: (2,4),(2,5),(3,3),(4,3) — 580,550 stratum members read (= Σ q^{4N−3}). **L0HIST ROWS (11).** Z_p: (2,5),(2,7),(3,3),(5,3),(7,2); F_q[[t]]: (2,5),(2,7),(3,3),(4,3),(8,2),(9,2) — 69,053 monic quadratics read (depth-3 histories realized at N = 7). **ORACLE ROWS.** Cubic Z_p: (2,3),(2,4),(3,2),(3,3),(5,2) = 40,645 cubics (every decided member scored; species witnesses 8+16+9+27+25 = 85 constructed pairs); quartic Z_p: (2,3),(2,4),(3,3) (every QRT-decided member scored: 32 + 512 + (729+243) = 1,516).”

| roster | rows | coverage |
|---|---:|---|
| Cubic census | 23 (10 `Z_p` + 13 `F_q[[t]]`) | 7,105,774 cubics; 2,946,008 DBL/TRP lifts read individually |
| Quartic (quadruple-center stratum only) | 8 (4 `Z_p` + 4 `F_q[[t]]`) | 580,550 stratum members |
| L0HIST (quadratic) | 11 (5 `Z_p` + 6 `F_q[[t]]`) | 69,053 quadratics; depth-3 histories at N = 7 |
| Oracle cubic (`Z_p` only) | 5 | 40,645 cubics + 85 constructed witness pairs |
| Oracle quartic (`Z_p` only) | 3 | 1,516 QRT-decided members |

**CONDITIONALITY:** Oracle rows are `Z_p`-only — the structural limitation recorded at W12-BOX-6 and the reason the `[r4]` F1 defect was invisible to the sealed kit. Quartic rows cover the quadruple-center stratum only.

**DERIVATION:** Row roster; the counts are sums of the stated closed forms (`Σ q^{3N−1}`, `Σ q^{4N−3}`).

**RESOLUTION TRACE:** Base §S7, lines 1374–1390.

**TEETH:** The `(2,7)` rows exist specifically to realize TRP-3LIN — a coverage row designed to make a family visible.

---

### EFF.W12.59  [fence]

**CANONICAL STATEMENT:** §S7 — PRE-SEAL SMOKE DISCLOSED

> “**PRE-SEAL SMOKE DISCLOSED** (runner docstring carries the same record): developed against cubic rows (Zp,2,3),(Zp,2,4),(Zp,3,2),(Fqt,2,3),(Fqt,4,2); quartic (Zp,2,3),(Zp,3,3); L0HIST (Zp,2,5),(Fqt,3,3); oracle cubic (2,3),(3,2) + species; quartic oracle (2,3) — observed: all families 0 violations, all four teeth firing (5,884 checks, 0.9 s). ONE COST PROBE: cubic (Fqt,2,6) run once pre-seal to price the (2,7) rows (18.9 s; 0 violations; dblU = 2048 = the law; 1,248 deep-decided TRP members realized). The S2.4/S2.5 closed forms were confirmed by an independent throwaway brute-force (pre-runner, /tmp, 9 cubic + 4 quartic rows) BEFORE the runner was written. `gp` probed (PARI 2.17.4). No full run before the seal.”

**CONDITIONALITY:** Full disclosure of which rows the instrument was developed against (so the verdict's evidential weight can be discounted correctly), plus the explicit “No full run before the seal”.

**DERIVATION:** Development record.

**RESOLUTION TRACE:** Base §S7, lines 1392–1402.

**TEETH:** The pre-runner independent brute force (9 cubic + 4 quartic rows) is the decorrelated leg for the S2.4/S2.5 closed forms.

---

### EFF.W12.60  [battery-frame]

**CANONICAL STATEMENT:** §S7 — PREREGISTERED PREDICTIONS P-1 … P-9 (commit 1)

> “* P-1 [NONE] W12-PIN 0/5 — all five frozen imports unmoved.
> * P-2 [SAME] W12-LVL0 + W12-SHAPE 0 violations on all 23 cubic rows — every depth-0 TRP law exact both directions, zeros included. Spot values (whole space = per-center × q, computed from the closed forms before any full run): (Zp,2,4): RAM3(1) = 512, RAM3(2) = 128, LINRAM2(2,1) = 128, LINRAM2(3,1) = 64, FULL(1,'12') = 16, FULL(1,'3') = 32 — exactly 6 keys; (Zp,2,7): 3LIN(3,2,1) = 512; (Fqt,9,2): RAM3(1) = 5832; (Zp,3,4): FULL(1,'111') = 0 (exact zero; key absent), VERT1/VERT2/RAM2LIN absent (their vertex condition u₀ > 3k ≥ 3 needs u₀ ≥ 4 > N−1); (Zp,2,5): RAM2LIN(4,1) = 64, VERT1(4,1,'2') = 64, VERT1(4,1,'11') = 0 (exact zero).
> * P-3 [SAME] W12-QRT 0 violations on all 8 quartic rows — spot: (Zp,2,4): QRT-G2(1,(2)) = 512, (1,(1,1)) = 0 (exact zero), (1,(1²)) frontier volume = 512; (Zp,3,3): QRT-G2(1,(2)) = 729, (1,(1,1)) = 243, (1,(1²)) = 486; only h = 1 realized on this roster (2h ≤ N−1 needs N ≥ 7 for h = 3 — disclosed limit; the h-scaling of the exponent law is exercised by the TRP rows' parameter ranges instead).
> * P-4 [SAME] W12-L0HIST 0 violations — every history-resolved key exact on all 11 quadratic rows (max depth = ⌊(N−1)/2⌋ each, = 3 at N = 7); Σ_H == the sealed W-11 aggregate predictor on every (q,N).
> * P-5 [SAME] W12-BLOCK / W12-L1X 0 violations — the Hensel product identity, the fiber bijection, and the cross-read agreement pointwise on every DBL member of every cubic row.
> * P-6 [SAME] W12-DRAIN3 — partition == q^{3N} on all 23 rows; DBL-undecided == (q−1)q^{2N−1} on all 23 rows (spot: (Zp,2,4) = 128; (Fqt,9,2) = 5832; (Fqt,4,2) = 192); per-pattern DBL keys letter-uniform; species undecided-count == q^N on every row. U₃^TRP: reported per row, NO preregistered value (EXPLORATORY; bounds q^N ≤ U₃^TRP ≤ q^{3N−2} are theorems but the measured value under the conservative convention is an upper count of the σ-residue and may exceed neither bound's role — recorded raw).
> * P-7 [IND] W12-ORACLE 0 bad — σ multisets confirmed per decided polynomial (cubic and quartic); disc = 0 ⟹ undecided; all 85 species witness pairs hit their PREDICTED σ_A and σ_B with σ_A ≠ σ_B **[r5, PE5 m3: 70 of the 85 pairs are the S3.2 proof's pairs; the 15 b₂ = 0 pairs are the SEALED pair [r4] deleted from the proof — true of the witnesses built (disc ≠ 0, σ_A ≠ σ_B on these ℤ_p rows), silent on the repaired pair; scope bracket at the S3.2 machine line]**.
> * P-8 teeth — all four fire at exactly-predicted counts: T-SHAPE = 23, T-DRAIN = 23 (once per cubic row), T-CENSUS4 = 8 (once per quartic row), T-SIGMA = 1,273 (once per decided (2)-member of the quartic oracle rows: 32 + 512 + 729).
> * P-9 (falsifiers, blueprint break-analysis order): a W12-SHAPE/QRT mismatch on a WILD row (p = 3 RAM3, p = 2 LINRAM2/RAM2LIN/QRT) with tame rows clean refutes the uniformity clause and hits J-D0's mechanism — per GRT_WELD_BLUEPRINT S4's J-D row, diagnose as an upstream WELD error FIRST; a W12-DRAIN3 DBL-term violation refutes W12-L1(c), i.e. would contradict W-11's sealed law — check the Hensel-split implementation first; an L1X mismatch refutes W12-L1(b) as displayed (the read-equivalence case analysis); an L0HIST violation refutes W12-L0's induction; a species member classified decided refutes LEMMA W12-S3.2 (or the reader — the PARI witness leg separates the two); a tooth not firing voids the battery, not the theorems.”

**CONDITIONALITY:** Preregistration is exact: spot values computed from the closed forms **before any full run**, teeth counts predicted exactly, and `U₃^TRP` explicitly carrying NO preregistered value. P-9 is a preregistered falsifier map with a diagnosis order.

**DERIVATION:** Each spot value is an evaluation of the corresponding shard-1 closed form at the named `(q, N)`.

**RESOLUTION TRACE:** Base §S7, lines 1404–1460, with `[r5]` m3's scope bracket landed inside P-7.

XREF: `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md:the faithfulness handoff (J-D1)` — grep-verified count **1**; P-9's diagnosis order cites the blueprint's J-D row (blueprint §S4's break-analysis table; the `W-12` string occurs **4** times in that file).

**TEETH:** This unit IS the preregistration; the scorecard is `.70`–`.73`.

---

### EFF.W12.61  [changes-record]

**CANONICAL STATEMENT:** §S7 — the seal verdict line

> “**VERDICT: PENDING — commit 1 seals this note + the unrun runner; commit 2 appends §S10 from `w12_checks_output.txt` / `w12_checks_results.json`.**”

**CONDITIONALITY:** Superseded by §S10's GREEN verdict (`.69`).

**DERIVATION:** Two-commit protocol declaration.

**RESOLUTION TRACE:** Base §S7, lines 1462–1464.

**TEETH:** The two-commit discipline is itself the anti-tuning device.

---

### EFF.W12.62  [scope-record]

**CANONICAL STATEMENT:** §S8 — CONSUMERS

> “1. **W-13 (the n = 3 menu completion)** — S2.4's depth-0 completeness + BOX-2's two-species node calculus is the exact work order; W-12.D already prices what its completion buys ((hMenu-3) discharged ⟹ R_τ ∈ ℚ(q) at n = 3 modulo (hExhaust-3)).
> 2. **Phase-B omMenu growth / `DecidedOmCountTie`** — THEOREM W-12.A is the transcription spec for order-1 menu entries AT EVERY DEGREE (typeOf-keyed by (C, P_i, λ_{i,S})), extending W-11 S4.1's n = 2 table; the S2.4/S2.5 instance tables are certified target values.
> 3. **The hExhaust program** — `montes_unconditional_exhaustive`'s hypothesis now has: n = 2 exact (W-11), the n = 3 DBL term exact + both bounds (W-12.C), the precise general statement (W-12.B), and the reduction that consumes it (W-12.D).
> 4. **The public uniformity story** — W-12.D is the GOAL's statement shape delivered: one ℚ(q) expression per splitting type at all primes including wild, firing unconditionally at n = 2, two named boxes at n = 3; the wild strata (p = 2 e = 2 blocks, p = 3 cubic total ramification, p = 2 quartic (2,2)) counted by the same laws as the tame ones.”

**CONDITIONALITY:** Consumer 2's transcription spec is later **amended** by LEMMA W12-HT's own consumer sweep: “A history-resolved order-1 menu entry must implement (HT-rec), retaining complete child-history multisets, side tags, \(D_v\), \(\kappa_v\), and \(\kappa_0\).” Any Phase-B transcription must follow the amended spec, not the S1 display.

**DERIVATION:** Consumer inventory.

**RESOLUTION TRACE:** Base §S8, lines 1468–1485; consumer 2 amended at the discharge's consumer sweep (`.87` **[merge finding: source cites this as `.43`, which is out of range under either shard's own numbering (shard 2's temporary numbering ran only 01–36; shard 1's own `.43` is unrelated §S3.4 content) — resolved by content match to this shard's own `.35` ("LEMMA W12-HT — consumer sweep…"), merged `.87`; recorded as a source citation defect, §8]**).

XREF: `lean/LeanUrat/OM/RealInstanceV2.lean:montes_unconditional_exhaustive` — grep-verified count **5**; `hExhaust` — count **5**.

XREF: `lean/LeanUrat/OM/OMCountV2.lean:omMenu_order0` — grep-verified count **1**.

**TEETH:** NONE (consumer inventory).

---

### EFF.W12.63  [scope-record]

**CANONICAL STATEMENT:** §S9 — CONDITIONALITY STACK (every consumed supplier, as-of pins)

> “* **THEOREM W-11(n = 2)** — PROVED at attempt grade (arc: seal 7020ceb / verdict cb05127 → PE1 → r1 8c87fa3 → PE2 473a993 → r2 = HEAD 31506b3 at composition time; counter 0/2, all findings display-level). Consumed as: the menu + exact drainage law (S2.7(c), S3.4 instance), the refinement isomorphism S2.3 (W12-L0's induction step), and its SEALED classifier + predictor as reference instruments (md5 500aae152bb5b5e9df3712904a6d73a6, pinned).
> * **THEOREM W-10(2,1,1)** — PROVED, seal 2e6fdd8 / verdict 9506a55; consumed as the digit-calculus template (S2.2) and via the W-11 instrument's own sealed W10 tie (md5 a9c34244…, pinned).
> * **LEMMA J-D0** — PROVED on its perimeter, seal 1642275 / verdict 9387eb1; consumed as the shape-keying/count-gauge-blindness FRAME (S0 design decision, S2.2's census remark, S2.7(b)); the order-1 proofs are self-contained, so J-D0 is corroborating at the instances and load-bearing for the general framing (its BOX perimeter inherited).
> * **The six ACCEPTED weld notes** (ledger fold 17d2a32): GRTJA @ f131c53, GRTJB + GRTJC @ 83f47f4, GRTW2 @ adc6cf3, LIFTCORNER @ 08f61e9, WELDMASTER @ 66b3498 — consumed ONLY in §S5's composition display and as [W12-H]'s named inputs (S4.2); NO S2/S3 proof depends on them. W2-OPEN-2a status as of composition: narrowed to the Σ-LAW lemma (OPEN2ATTACK @ bd82766/4a970aa).
> * **DULEMMA** @ 048cf6d / f819f26 (perimeter e_m ≥ 2) — NOT consumed by any count law (S5 display only).
> * **Classical inputs:** Hensel's lemma (coprime lifting, S2.1; separable-residual steps), Ore's theorem (GMN order-1 layer, S2.3), finite-field factorization censuses (S2.2, re-derived) — standard, cited without commit pins.
> * **Lean anchors at HEAD** (`OM/RealInstanceV2.lean` `montes_unconditional_exhaustive` / `hExhaust`; `OMCountV2.omMenu` / `omMenu_order0`) — cited as tie TARGETS (S8 items 2–3); no Lean is changed by this unit.”

**CONDITIONALITY:** Every supplier is pinned as-of, with the header note “all pins verified against git log this session”. The W-11 grade recorded here (attempt 0/2 at composition time) is that note's own state at composition, not a claim about its current grade.

**DERIVATION:** Supplier ledger.

**RESOLUTION TRACE:** Base §S9, lines 1487–1520.

XREF: `lean/notes/openmath/W11_PROOF_2026-08-08.md:THEOREM W-11` — grep-verified count **3**; `S2.3` — count **8**.

XREF: `lean/notes/openmath/W10_PROOF_2026-08-08.md:THEOREM W-10` — grep-verified count **2**.

XREF: `lean/notes/openmath/JD0_PROOF_2026-08-08.md:LEMMA J-D0` — grep-verified count **4**.

XREF: `lean/notes/openmath/GRTW2_PROOF_2026-08-08.md:OPEN2ATTACK` — grep-verified count **5**; `Σ-LAW` — count **14**.

XREF: `lean/notes/openmath/DULEMMA_PROOF_2026-08-08.md:DULEMMA` — grep-verified count **1**.

**READING NOTE (external, not an edit).** The classical-inputs row's “Ore's theorem (GMN order-1 layer, S2.3)” is `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` row **Q1 W12-2**, retargeted to **[GN15] Theorem 2.3** (NS-1/NS-2, verdict COVERS-ALL-O); the `(H-e)` cite is row **Q1 W12-3** → NS-3, same source plus [AGNPRW] Thm 4.4 + Prop 4.5.

**TEETH:** W12-PIN enforces the md5 pins of the two consumed instruments.

---

### EFF.W12.64  [scope-record]

**CANONICAL STATEMENT:** §S9 — the one-line hypothesis ledger

> “**One line: THEOREM W-12.A's hypothesis set = {classical Hensel/Ore/censuses}; THEOREM W-12.C's = {that + THEOREM W-11 @ its pins}; THEOREM W-12.D's = {nothing — an unconditional reduction}; the weld corpus enters only [W12-H] (the order-≥ 2 program) and §S5's display.**”

**CONDITIONALITY:** This is the note's own summary of the DAG edges and is the sentence a downstream blueprint should transcribe. Note what it does NOT say: W-12.D's *firings* carry per-degree conditionality (shard 1 `.45`); the reduction itself carries none.

**DERIVATION:** Ledger summary of `.63`.

**RESOLUTION TRACE:** Base §S9, lines 1522–1526. The 2026-08-12 obstruction/discharge adds LEMMA W12-HT's own consumption to W-12.A's set: “It consumes W-12 S2.1 …, W-12 S2.2 …, W-11 S2.3 …, W12-L0, W12-L1, and GENIND-1 (fracture permanence, at its stated **PROVED** grade)” — i.e. at full order-1 coverage, W-12.A's hypothesis set gains W-11 S2.3 and GENIND-1.

XREF: `lean/notes/openmath/GENIND_PROOF_2026-08-08.md:GENIND-1` — grep-verified count **15**; the fracture-permanence input the discharge adds.

**TEETH:** NONE (ledger).

---

### EFF.W12.65  [regression-record]

**CANONICAL STATEMENT:** §S10 — VERDICT (commit 2, from the committed artifacts)

> “**GREEN. 3,232,506 checks, 0 violations in every family, all four teeth fired at their EXACTLY-preregistered counts, zero skips.** 23/23 cubic census rows (7,105,774 cubics covered; 2,946,008 DBL/TRP lifts read individually), 8/8 quartic stratum rows (580,550 members), 11/11 history-resolved quadratic rows (69,053 polynomials), 5 cubic + 3 quartic oracle rows (38,874 decided cubics + 1,516 QRT members scored by PARI, 0 bad; 85/85 species witness pairs at their predicted σ_A ≠ σ_B; 0 disc-0-decided members). Artifacts: `w12_checks_output.txt` (md5 0557b15fb08a6e6eb40bd2db7e62206b), `w12_checks_results.json` (md5 05776c9e00071c5d7524abdfbe894442); runner byte-identical to the sealed commit f669cb0 (empty `git diff`); elapsed 323.0 s; exit 0; single fresh run, no prior artifacts.”

**CONDITIONALITY:** The GREEN-summary line “85/85 species witness pairs” is scoped by `[r5]` m3 (“This scope also covers this section's GREEN-summary line”): 70 pairs are the S3.2 proof's, 15 are the sealed `B = 0` pair deleted from the proof.

**DERIVATION:** Verdict transcribed from the committed artifacts at commit 2; runner byte-identity verified by empty `git diff`.

**RESOLUTION TRACE:** Base §S10, lines 1531–1543.

**TEETH:** The single-fresh-run + no-prior-artifacts + byte-identical-runner triple is the anti-tuning evidence.

---

### EFF.W12.66  [regression-record]

**CANONICAL STATEMENT:** §S10 — prediction scorecard P-1 … P-5

> “* P-1 ✓ [NONE] W12-PIN 0/5 — all five frozen imports unmoved (w11_checks 500aae15…, w10_checks a9c34244…, iterlawn_pe_reimpl cae45db2…, grt_jc_probe 03811b69…, jd0_checks d3a5e13d…).
> * P-2 ✓ [SAME] W12-LVL0 0/138 + W12-SHAPE 0/164 — every depth-0 TRP law exact both directions on all 23 rows, both characteristics. Every preregistered spot value hit EXACTLY: (Zp,2,4) the 6-key table (RAM3(1) = 512, RAM3(2) = 128, LINRAM2(2,1) = 128, LINRAM2(3,1) = 64, FULL(1,'12') = 16, FULL(1,'3') = 32); (Zp,2,7) realizes the full 22-key depth-0 menu incl. 3LIN(3,2,1) = 512; (Fqt,9,2) RAM3(1) = 5832; the exact zeros held (no VERT1(·,·,(1,1)) key at q = 2, no FULL(·,(1,1,1)) at q ≤ 3).
> * P-3 ✓ [SAME] W12-QRT 0/27 — all 8 quartic rows: (Zp,2,4) QRT-G2(1,(2)) = 512, (1,(1²)) = 512, (1,(1,1)) = 0 exact zero; (Zp/Fqt,3,3): 729 / 243 / 486; (Fqt,4,3): 6144 / 3072 / 3072 — the wild p = 2 (2,2)-stratum counted by the same law as the tame q = 3 rows.
> * P-4 ✓ [SAME] W12-L0HIST 0/306 — every history-resolved key exact on all 11 rows; max depth = ⌊(N−1)/2⌋ on every row (= 3 at N = 7, 39 keys); Σ_H == the sealed W-11 aggregate predictor on every (q,N).
> * P-5 ✓ [SAME] W12-BLOCK 0/1,594,670 + W12-L1X 0/1,594,090 — the Hensel product identity, fiber bijection, and the fresh-direct-read vs sealed-W11-block-read agreement POINTWISE on every DBL member of every row: LEMMA W12-L1(a)(b) machine-checked at seam level.”

**CONDITIONALITY:** All SAME-class except P-1 (bookkeeping). P-5's cross-read is the strongest of them (fresh arithmetic vs a frozen foreign classifier).

**DERIVATION:** Scorecard against the preregistration at `.60`.

**RESOLUTION TRACE:** Base §S10, lines 1546–1568.

**TEETH:** P-2's both-directions completeness clause; P-3's wild-row equality with tame rows; P-5's pointwise seam check.

---

### EFF.W12.67  [regression-record]

**CANONICAL STATEMENT:** §S10 — P-6, with the `[r4]` F3 correction of its closing inference

> “* P-6 ✓ [SAME] W12-DRAIN3 0/1,183 — partition exact on all 23 rows; DBL-undecided == (q−1)q^{2N−1} on all 23 rows ((Zp,2,4) = 128, (Fqt,9,2) = 5832, (Fqt,4,2) = 192 as preregistered): THEOREM W-12.C's exact term GREEN; per-pattern letter-uniformity held on every pattern of every row; species = q^N members on every row, all undecided. U₃^TRP recorded (EXPLORATORY, conservative convention), bonus observation FROM the artifacts: the measured value is IDENTICAL across Zp/Fqt at each of the NINE genuinely shared (q, N) pairs — (2,3…7): 32/144/608/2720/11328; (3,2…4): 27/243/2511; (5,2): 125 [r1 m2: the sealed sentence interleaved (4,2/3) = 64/1024, (8,2) = 512, (9,2) = 729 into the same list — those are Fqt-ONLY rows (no Zp prime-power rows exist, BOX-6): single-kind raw data, NOT cross-checked pairs; the cross-characteristic claim is scoped to the nine shared pairs, all nine equal] — characteristic-uniform raw data ~~consistent with W-12.B's q-uniformity (no law claimed; the q = 2 sequence 32/144/608/2720/11328 grows ≈ ×q² per window step, order q^{2N} as W-12.B predicts)~~”

**The struck inference and its replacement (`[r4]` F3), quoted in full because it is the note's own falsification of one of its own readings:**

> “**[r4, PE4 F3: the struck closing inference is FALSE for the measured quantity, and post-pin it is not W-12.B's quantity at all — BOTH reasons stated. (1) ORDER: the conservative residue is Θ(N·q^{2N}), not Θ(q^{2N}) — by THEOREM HEX3.A, quoted verbatim in this note's own BOX-3 ANNEX, U₃^conv = q·u(q,N) whose normalized mass diverges linearly with mean slope (q−1)/(2q²(q+1)) = 1/24 at q = 2, while W-12.B predicts undecided·q^{−2N} → c₃(q) with NO N factor; the committed numbers already show it, since normalized (×q^{−2N}) the q = 2 sequence is 0.5000, 0.5625, 0.5938, 0.6641, 0.6914 — monotonically RISING — and every displayed step ratio (4.50, 4.22, 4.47, 4.16) EXCEEDS the "≈ ×q²" = 4 the struck sentence attributed to it: the excess IS the divergence, not noise. (2) QUANTITY: after the [r3] σ-pin, undecided(3,q,N) is the lift-certification residue U₃^σ, whereas this battery row measures the conservative residue U₃^conv ⊇ U₃^σ — so even a true order statement here would corroborate a DIFFERENT quantity. What survives, and is the row's real content: the nine-shared-pair characteristic-uniformity of the raw measurement, now EXPLAINED by COROLLARY HEX3.C (BOX-3 annex). The [r3] sweep filed this surface under class (c) "no σ-decidedness claim ridden" — accurate about σ-decidedness, but the struck clause rode a W-12.B ORDER claim, which is the classification the sweep needed to catch; no theorem depends on it (the row is fenced EXPLORATORY, "no law claimed"). Consequence to state plainly: post-pin the note's n = 3 bracket q^N ≤ U₃^σ ≤ q·u(q,N) is uninformative about c₃ in BOTH directions (normalized by q^{−2N} the lower end → 0 and the upper end → ∞), so W-12.B has no n = 3 corroboration here either way — honest at its GRADE: conjecture]**.”

**CONDITIONALITY:** The surviving content of the row is exactly the nine-shared-pair characteristic uniformity, explained by COROLLARY HEX3.C. The row supplies **no** corroboration for W-12.B in either direction.

**DERIVATION:** Both reasons are derived from the committed numbers themselves: the normalized sequence rises monotonically and every step ratio exceeds `q² = 4`, and the measured quantity is `U₃^conv ⊇ U₃^σ` after the σ-pin.

**RESOLUTION TRACE:** Base §S10, lines 1569–1613, with `[r1]` m2's roster scoping and `[r4]` F3's strike-and-replace landed in place.

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:THEOREM HEX3.A` — grep-verified count **11**; `COROLLARY HEX3.C` — count **8**.

**TEETH:** The committed `U₃` values are the evidence for the falsification of the struck inference — a rare case of a battery row refuting its own note's reading.

---

### EFF.W12.68  [regression-record]

**CANONICAL STATEMENT:** §S10 — P-7, P-8, P-9

> “* P-7 ✓ [IND] W12-ORACLE 0 bad / 41,923 checks — PARI confirms the σ MULTISET of every decided cubic on all five Z_p rows (38,874 members: separable, DBL-decided incl. deep histories, TRP-decided incl. the depth-0 wild families) and every decided QRT quartic (1,516 members: the p = 2 wild (2,2) and (2,1)² strata included); 0 disc-0-decided; all 85 species pairs hit their PREDICTED σ_A and σ_B with σ_A ≠ σ_B — LEMMA W12-S3.2's constructed lifts confirmed by the independent engine **[r5, PE5 m3: at the 70 b₂ ≠ 0 pairs. The other 15 (b₂ = 0, one per centre) are the SEALED pair [r4] deleted from S3.2's proof: the engine confirms them AS BUILT (disc ≠ 0, σ_A ≠ σ_B on these mixed-characteristic rows) — a true fact about those witnesses, not confirmation of the repaired (B = π^N) pair; see the [r4] scope bracket at the S3.2 machine line. This scope also covers this section's GREEN-summary line "85/85 species witness pairs at their predicted σ_A ≠ σ_B"]**.
> * P-8 ✓ teeth — T-SHAPE = 23, T-DRAIN = 23, T-CENSUS4 = 8, T-SIGMA = 1,273: every count exactly as preregistered.
> * P-9 ✓ — no falsifier fired; nothing to diagnose upstream.”

**CONDITIONALITY:** P-7's witness-pair leg is scoped 70/85 (see above). The IND leg's coverage is mixed-characteristic only (BOX-6).

**DERIVATION:** Scorecard.

**RESOLUTION TRACE:** Base §S10, lines 1614–1631, with `[r5]` m3's scope bracket landed in place.

**TEETH:** All four planted mutants fired at their exactly-preregistered counts — the battery is not RED.

---

### EFF.W12.69  [scope-record]

**CANONICAL STATEMENT:** §S10 — Consequence for the grade box, and the `[r1]` arc display

> “**Consequence for the grade box:** the S1 grades stand as composed — THEOREM W-12.A PROVED at the order-1 layer of every degree with its new instances machine-sealed both characteristics (7 TRP families incl. 3 wild strata, QRT g = 2 incl. the wild (2,2)); THEOREM W-12.C's exact DBL drainage term GREEN on 23 rows; THEOREM W-12.D stands as an unconditional reduction (its n = 2 instance fires on W-11's theorems; nothing here can strengthen or weaken a proof, but the reduction's (A1)-shape data — q-uniform laws, letter-blind cells — is what the battery confirmed at every new family); the S6 boxes open exactly as displayed (orders ≥ 2 = [W12-H]; (hMenu-3)/(hExhaust-3) = BOX-2/BOX-3; W-12.B remains a conjecture). ~~Attempt 0/2; the hostile arc has not begun.~~ **[r1] ARC (superseded — the CURRENT arc is the ~~[r4]~~ [r5, re-pointed at r5] ARC at the end of this note): composed 0/2 → PE1 NOT CLEAN (1 CRITICAL + 3 GAPS + 2 minor, report @ 2b47711; machine leg re-run GREEN 3,232,506/0 with seal md5-intact, fresh-route 0 mismatches — arc facts) → r1 THIS REPAIR (all six findings, note-only, [r1] tags, minimality contract; runner + artifacts byte-frozen at seal f669cb0) — counter 0/2; PE2 next.**”

**CONDITIONALITY:** The grade sentence explicitly disclaims that machine evidence can move a proof (“nothing here can strengthen or weaken a proof”) — the battery confirms the (A1)-SHAPE data, not the theorems. The arc display is marked superseded; the current arc is `.74`.

**DERIVATION:** Grade reconciliation against the verdict.

**RESOLUTION TRACE:** Base §S10, lines 1633–1650; the `[r1]` arc marker re-pointed at `[r5]`.

**TEETH:** The re-run GREEN at seal-intact md5 with fresh-route 0 mismatches (an “arc fact” per the note's own labelling).

---

### EFF.W12.70  [absorption-record]

**CANONICAL STATEMENT:** ANNEX — the W12-BOX-3 annex from HEX3, applied verbatim

> “Applied VERBATIM from HEX3_PROOF_2026-08-08.md §S8.1 (HEX3 seal e3f3459 / verdict 671a126, battery GREEN 158,512 checks / 0 violations on 46 rows both characteristics; adjudicated @ a0290f9), per that adjudication's work order. What it does to this note's boxes: W12-BOX-3's NAMED OBLIGATION — a vanishing U₃^TRP upper bound, (hExhaust-3) — is DISCHARGED at composition grade (attempt 0/2; HEX3's own hostile arc has not begun), CONVENTION-FREE (the discharge rides U₃^σ ≤ U₃^conv ≤ N·q^{2N−1}); it is the EXACT LAW U₃^conv = q·u(q,N) that is scoped to the disclosed conservative convention [r2, PE2 m2: the wrapper as first written attached the convention qualifier to the discharge instead of the law — per HEX3.B and the verbatim block below, only the exact law is conv-scoped]; on the σ side the bracket q^N ≤ U₃^σ ≤ q·u(q,N) stands, with the exact U₃^σ law open exactly at the tail-σ-certification lemma (HEX3-BOX-1). The annex text, verbatim:”

> “> **[BOX-3 ANNEX, 2026-08-08, HEX3]** The conservative-convention residue now has an EXACT law: U₃^conv(q,N) = q·[q^{2N−2} + (q−1)Σ_{k≥1} q^{4k−1}(q^{N−3k}−1)R(N−3k)], R(M) = q^{M−1} + ⌊(M−1)/2⌋(q−1)q^{M−2} (HEX3_PROOF_2026-08-08.md, THEOREM HEX3.A; sealed battery, 46 rows, both characteristics). Since U₃^σ ≤ U₃^conv ≤ N·q^{2N−1}, the box's named obligation — a vanishing U₃^TRP upper bound, (hExhaust-3) — is DISCHARGED at composition grade (attempt 0/2); the exact U₃^σ law remains open exactly at the tail-σ-certification lemma (HEX3-BOX-1). The exploratory characteristic-independence observation is now COROLLARY HEX3.C. W-12.C's bracket sharpens to q^N ≤ U₃^σ ≤ q·u exactly.”

**CONDITIONALITY:** Discharged **at composition grade** — HEX3's own hostile arc had not begun at the append. The discharge itself is CONVENTION-FREE; only the exact law is conv-scoped (the `[r2]` m2 distinction). The exact `U₃^σ` law remains open at HEX3-BOX-1.

**DERIVATION:** `U₃^σ ≤ U₃^conv ≤ N·q^{2N−1}` with the exact `U₃^conv` law, giving `U₃^σ/q^{3N} → 0`.

**RESOLUTION TRACE:** Base ANNEX, lines 1654–1683; discharges shard 1's W12-BOX-3 and one of the two n = 3 legs of shard 1's `.45`.

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:THEOREM HEX3.A` — grep-verified count **11**; `HEX3-BOX-1` — count **11**; `COROLLARY HEX3.C` — count **8**.

**TEETH:** HEX3's sealed battery — GREEN 158,512 checks / 0 violations on 46 rows, both characteristics.

---

### EFF.W12.71  [absorption-record]

**CANONICAL STATEMENT:** ANNEX 2 — the W12-BOX-2 annex from HMENU3, applied verbatim

> “Applied VERBATIM from HMENU3_PROOF_2026-08-08.md §S8.1 (HMENU3 seal 64d3ff9 / verdict 625fa49, battery GREEN 183,387 checks / 0 violations on 41 rows / 94,824,902 per-center states, both characteristics, all four teeth at their EXACTLY-preregistered counts 21/15/10/4, PARI σ-leg on all 9,952 deep-decided members of four rows), per that note's §S8 work order; extracted block md5 4eb3bacc30e3be0bc8a08a72cf9d9473, byte-identical to HMENU3 §S8.1 lines 573–585, and its claims re-verified against the 625fa49 verdict at this append (row/check/tooth/oracle counts as above; HM3.A/B/C/D statements as summarized). What it does to this note's boxes: W12-BOX-2's NAMED OBLIGATION — the complete TRP refinement-family menu, (hMenu-3) — is DISCHARGED at composition grade (attempt 0/2; HMENU3's own hostile arc has not begun). With the BOX-3 annex above, W-12.D's n = 3 conditionality {(hMenu-3)} + {(hExhaust-3)} is closed at composition grade: COROLLARY HM3.D (HMENU3) displays the five cubic R_τ(q), Σ_τ R_τ = 1, both characteristics, wild included — conditional exactly on the arc grades of the W-11/W-12/HEX3/HMENU3 stack (this note's own arc: PE1 adjudicated + r1; PE2 0C+3G+2m @ 1be15d2 + r2 applied above; counter 0/2, PE3 owed). The annex text, verbatim:”

> “> **[BOX-2 ANNEX, 2026-08-08, HMENU3]** The TRP refinement-family menu is now COMPLETE: THEOREM HM3.A (history-resolved exact laws; both node species' transfer laws leaf-resolved: α self-similar with key shear, β into W12-L0 via the raw-key dictionary), THEOREM HM3.B (the finite (A1)-admissible aggregate menu; instance bracket (q−1)q^{4m−1}), THEOREM HM3.C ((A0) + exact-complement (A2)) (HMENU3_PROOF_2026-08-08.md; sealed battery, 41 rows both characteristics, PARI σ-leg on 9,952 deep members). (hMenu-3) is DISCHARGED at composition grade (attempt 0/2). With (hExhaust-3) (HEX3) this closes W-12.D's n = 3 conditionality: COROLLARY HM3.D displays the five cubic R_τ(q), Σ = 1, both characteristics, wild included — conditional exactly on the arc grades of W-11/W-12/HEX3/HMENU3.”

**CONDITIONALITY:** Discharged **at composition grade**; the resulting n = 3 result is “conditional exactly on the arc grades of the W-11/W-12/HEX3/HMENU3 stack”. The annex block is byte-identical to its source with the extraction md5 recorded — a verifiable transcription.

**DERIVATION:** HMENU3's three theorems supply the two node-species transfer laws that shard 1's `.37` named as missing.

**RESOLUTION TRACE:** Base ANNEX 2, lines 1685–1720; discharges shard 1's W12-BOX-2 and the second n = 3 leg of `.45`. **Its supplier is then partially corrected by `.72`** — but the annex text itself “is UNTOUCHED and stays verbatim as applied”.

XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:COROLLARY HM3.D` — grep-verified count **11**; `THEOREM HM3.C` — count **10**.

**TEETH:** HMENU3's sealed battery — 183,387 checks / 0 violations on 41 rows, four teeth at preregistered counts, PARI σ-leg on 9,952 deep-decided members.

---

### EFF.W12.72  [changes-record]

**CANONICAL STATEMENT:** `[r5]` NOTICE ON ANNEX 2 — the supplier's inherited quantifier over-claim

> “**[r5] NOTICE ON ANNEX 2 (dated append, 2026-08-08, written at the r5 repair; the ANNEX 2 text above is UNTOUCHED and stays verbatim as applied — this is a notice about its supplier, not an edit to it).**”

> “**What is corrected, on the HMENU3 side.** THEOREM HM3.C's (A0) sentence reads "every menu member is conservative-DECIDED — all consulted data in-window with separable residuals — so Ore certifies **EVERY lift** (W-12 S2.3 at the terminal frame; …); σ_F = the leaf table" (HMENU3_PROOF_2026-08-08.md L216–219). The unrestricted quantifier "EVERY lift" is the SAME over-claim [r4]'s MINOR 2 struck from this note's own S2.3, and it is FALSE in equal characteristic 3 inside HM3.C's own menu: TRP-RAM3(1) is one of THEOREM HM3.B's depth-0 TRP families, its members with b₂ = b₁ = 0 in-window and v(b₀) = 1 exist at every window N ≥ 2, and over F_q[[t]] with p = 3 the lift F = y³ + b₀ has F′ ≡ 0, hence disc = 0 and NO σ at all. HM3.C's own cited warrant for the sentence is "W-12 S2.3 at the terminal frame" — i.e. the pre-[r4] S2.3 text — so the defect is INHERITED from the S2.3-era phrasing the two notes shared, not independently generated. The corrected clause is the disc ≠ 0 form, which is W12-BOX-7's pinned notion ("Decided = certified on window digits for all disc ≠ 0 lifts") and exactly what (A1)'s [r4] σ-LABELING clause and both Step-4 bounds consume: **every menu member is conservative-DECIDED and every disc ≠ 0 lift of every member has σ = the leaf table's entry.**”

> “**What does NOT move.** HM3.C's conclusion, its (A2) exact complement r(N), THEOREM HM3.A/HM3.B, COROLLARY HM3.D's five cubic R_τ(q) with Σ_τ R_τ = 1, ANNEX 2's discharge of W12-BOX-2's named obligation, and every count in either note's battery: all UNCHANGED. Nothing in (A1), Step 4, HM3.C's consumers, or HM3.D quantifies over disc = 0 lifts, so the n = 3 firing recorded in the [r4] FIRING CHECK survives on the corrected form (see the [r5] rewording of that row). **The correction is a quantifier phrase, not a result.** The HMENU3-side dated annex is drafted verbatim for application at `lean/notes/openmath/HMENU3_annex_draft_r5.md` (application to HMENU3_PROOF_2026-08-08.md is the orchestrator's, per the same annex-fence convention ANNEX/ANNEX 2 follow here).”

**CONDITIONALITY:** A cross-note correction that is **owed and not landed** — see OPEN-CALL 1. Nothing mathematical moves; the n = 3 firing survives on the corrected form.

**DERIVATION:** An explicit counter-instance inside HM3.C's own menu (TRP-RAM3(1), `b₂ = b₁ = 0` in-window, `v(b₀) = 1`, equal characteristic 3), plus the provenance argument that the defect is inherited from the shared S2.3-era phrasing.

**RESOLUTION TRACE:** Base lines 1722–1757; reworded shard 1's FIRING CHECK n = 3 row.

XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:THEOREM HM3.C` — grep-verified count **10**.

**READING NOTE (verified at HEAD, not an edit).** The draft file `lean/notes/openmath/HMENU3_annex_draft_r5.md` **exists**; `HMENU3_PROOF_2026-08-08.md` lines 216–219 **still read** “so Ore certifies EVERY lift (W-12 S2.3 at the terminal frame; W12-L1(c) transports the DBL certificates); σ_F = the leaf …”. The annex has not been applied. OPEN-CALL 1.

**TEETH:** The equal-characteristic-3 counter-instance (signed non-applicability).

---

### EFF.W12.73  [TABLE]

**CANONICAL STATEMENT:** [TABLE] `[r5]` m2 BLAST-RADIUS SWEEP

> “**m2 BLAST-RADIUS SWEEP (the sweep [r4] did not record; run at r5 over the live σ-certification surfaces of the W-11/W-12/HEX3/HMENU3/GENH4/GENHN stack).** Search terms: "every lift", "EVERY lift", "all lifts", "any lift", excluding disc ≠ 0-restricted occurrences.”

| surface | verdict at r5 |
|---|---|
| **W-12 S2.3** (this note) | STRUCK at [r4] MINOR 2 with its counter-instance; (A1)'s clause, Step 4 and W12-BOX-7 clause 1 re-swept this repair and quantify over disc ≠ 0 lifts ONLY |
| **HMENU3 THEOREM HM3.C** L218 | **INHERITS the over-claim.** Correction owed and drafted (above); substance and counts survive |
| **HEX3_PROOF** L80–81 ("Ore applies to every lift — W-12 S2.3", warranting U₃^σ ≤ U₃^conv) | SAME loose phrasing, **conclusion UNAFFECTED**: the σ-side quantity U₃^σ is counted with W-12's pinned (BOX-7 clause 1, disc ≠ 0) notion, so the inequality and the annexed HEX3.A law are unchanged. A phrasing correction owed at HEX3's own arc; no number and no box moves |
| **GENH4 THEOREM GENH4.C / GENHN THEOREM GENHN.C** | CLEAN — both STATEMENTS already read "EVERY lift **with disc ≠ 0**" (verified verbatim at their pins in the [r4] FIRING CHECK and re-verified by PE5). Their in-proof "a 2SIDED configuration for every lift" phrases are Newton-polygon configuration claims (true of every lift, disc = 0 included) sitting inside those restricted statements — not σ-certifications |
| **W-11(i)/(ii)/(iii)** and its all-lift phrases (SPLIT-TAIL absorption; "any lift has u > 2w") | CLEAN — those are VALUATION facts about all lifts, not σ-certifications, and the n = 2 firing row already states its pinned strength as "(all disc ≠ 0 lifts)". Worth recording that the quantifier is load-bearing at n = 2 too: in equal characteristic 2 the RAM(h) cell admits A₁ = 0 (its constraint is v(A₁) ≥ (h+1)/2, an inequality), and then disc = A₁² = 0 with F = x² + A₀ inseparable — so disc = 0 lifts live inside a DECIDED n = 2 family as well, and are excluded exactly by the clause's quantifier |

**CONDITIONALITY:** Two of the five rows carry owed corrections (HMENU3, HEX3), both phrasing-only with conclusions unaffected. The table's own grep is later found INCOMPLETE by PE6 (`.75`): three in-scope hits are missing from it.

**DERIVATION:** A declared grep over a declared surface set, dispositioned row by row, with the n = 2 quantifier's load-bearing instance derived explicitly (`RAM(h)` with `A₁ = 0` in equal characteristic 2).

**RESOLUTION TRACE:** Base lines 1759–1770; completed by the PE6 record (`.75`) and re-anchored by the PE7 record (`.76`).

XREF: `lean/notes/openmath/GENH4_PROOF_2026-08-08.md:THEOREM GENH4.C` — grep-verified count **9**; `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:THEOREM GENHN.C` — count **11**.

**TEETH:** The sweep IS a negative check; its own incompleteness was caught by an independent re-run at PE6.

---

### EFF.W12.74  [changes-record]

**CANONICAL STATEMENT:** The three ARC displays (`[r3]`, `[r4]`, `[r5]`), with `[r5]` CURRENT

> “**[r3] ARC (superseded by the ~~[r4]~~ [r5, re-pointed at r5] ARC below, 2026-08-08): composed 0/2 → PE1 1C+3G+2m (report @ 2b47711) → r1 (ba0d1a4) + BOX-3 annex (8e535d2) → PE2 0C+3G+2m (report @ 1be15d2) → r2 + BOX-2 annex (99f1813) → PE3 0C+1G+1m (report @ c9c5c0e, adjudicated @ 4228155; machine leg third GREEN re-run 3,232,506/0 with seal f669cb0 md5-intact, fresh route incl. the first prime-power-q rows at both degrees, 0 mismatches — arc facts) → r3 THIS REPAIR …: FINDING 1 (GAP, the computed ambiguity) = the σ-pin at the S1 Conventions + the W-12.B bullet … MINOR 1 = the genre-(ii) per-state residual wording in the S7 W12-ORACLE warrant … Neither annex touched; no theorem statement moved. Counter 0/2; PE4 next.**”

> “**[r4] ARC (superseded by the [r5] ARC below, 2026-08-08): … → PE4 NOT CLEAN 1C+2G+2m (report @ 26689da, adjudicated @ 455a2ec; the pin itself audited COHERENT AND TOTAL, the rejected-parse record re-derived independently from HEX3.A to the digit, machine leg a FOURTH GREEN 3,232,506/0 at seal-intact md5, and W-12's law suite confirmed in two DVR types outside the S1 convention incl. the first mixed-characteristic prime-power-q rows — arc facts) → r4 THIS REPAIR … Neither annex touched; no theorem statement moved (the only statement-adjacent change is (A1) gaining a hypothesis clause, i.e. a STRENGTHENING of W-12.D's hypotheses, which every firing supplies). Counter 0/2; PE5 next.**”

> “**[r5] ARC (CURRENT, 2026-08-08): … → PE5 NOT CLEAN 0C+1G+3m (report @ c3e2f8e: the [r4] witness repair RE-DERIVED from scratch in mixed, equal-2 and equal-3 characteristic with the parity bracket confirmed to cure the t = N degeneracy; (A1)'s σ-labeling clause confirmed to be EXACTLY what Step 4 consumes, its necessity instance re-verified clause by clause, three of its four firing citations verbatim at their pins; LEMMA W12-L0/W12-L1 re-derived with all six aggregations tied to W-11(ii) symbolically in q; machine leg a FIFTH GREEN 3,232,506/0 at seal-intact md5 with artifacts content-identical ex-timing; and the note's law suite confirmed in EQUAL characteristic p ≥ 5 for the first time in the arc — including (F_q[[t]], 5, 4), the first row anywhere that exercises the annexed HEX3.A's N-linear regime at p ≥ 5, and a (7,2) cross-characteristic pair the frozen kit cannot form — arc facts) → r5 THIS REPAIR (all four findings, note-only, [r5] tags, minimality contract; runner + artifacts byte-frozen at seal f669cb0).**”

> “**CITE VERIFICATION FIRST (charged: the PE5 report was written while the safety classifier was down, so every quoted line-cite was re-checked against the files at HEAD before any repair): the [r4] FIRING CHECK n = 3 row, S2.3's [r4]-struck parenthetical, HMENU3's HM3.C sentence (L216–219), S3.4's Step-4 lower/upper bounds and its conditionality close, the header's r1-era arc display, the three witness-pair credit surfaces (S7 W12-ORACLE, S7 P-7, §S10 P-7), the [r4] scope bracket at the S3.2 machine line, and the runner's witness builder (`verification/openmath/w12_checks.py` L1043–1065, `B = b2` with the `B == 0` branch building `predA = ((1,1),(2,1))`, `predB = ((3,1),)`) — ALL VERIFIED byte-faithful, 0 mismatches. PE5's 15-of-85 arithmetic re-derived independently from the runner loop (q centres × q^{N−1} `tdig` values per row; b₂ = 0 iff `tdig` = 0, so q pairs per row: 2+2+3+3+5 = 15 of 8+16+9+27+25 = 85).**”

**CONDITIONALITY:** Exactly ONE current arc display (the `[r5]` one) — the `[r5]` MINOR 2 fixed the note's multiple-current-arc defect. Every arc records five independent GREEN re-runs at seal-intact md5, and each round's “no theorem statement moved” claim is stated explicitly (with the one disclosed exception: (A1) gaining a hypothesis clause = a strengthening).

**DERIVATION:** Arc chronology with per-round finding lists; the CITE VERIFICATION block is a re-check of every quoted line-cite against files at HEAD.

**RESOLUTION TRACE:** Base lines 1774–1909, with the `[r3]`/`[r4]` markers re-pointed at `[r5]`.

**READING NOTE:** the runner's witness builder is cited at `verification/openmath/w12_checks.py` L1043–1065; the file exists in the repo (checked).

**TEETH:** Five independent GREEN re-runs at seal-intact md5, including PE5's first equal-characteristic `p ≥ 5` rows and a `(7,2)` cross-characteristic pair the frozen kit cannot form.

---

### EFF.W12.75  [changes-record]

**CANONICAL STATEMENT:** Dated record (2026-08-09, post-PE6) — three hits the `[r5]` sweep's own grep missed

> “Provenance: passPE6 hostile verification (report `W12_passPE6_report.md`, verdict commit ef258fe): CLEAN — 0 CRITICAL + 0 GAP + 1 MINOR (+3 uncounted remarks); the 2-clean counter started 0/2 → 1/2. The one MINOR (record completeness, PE6's MINOR 1): the [r5] m2 BLAST-RADIUS SWEEP's table declares its own search ("every lift" / "EVERY lift" / "all lifts" / "any lift", excluding disc ≠ 0-restricted occurrences, over the live σ-certification surfaces of the W-11/W-12/HEX3/HMENU3/GENH4/GENHN stack) but its five rows do not disposition three hits of that grep inside that scope. PE6 re-ran the grep, found the three, and verified each harmless; this append records them per PE6's stated repair shape ("one line per missed hit"). The sweep table above stands as written (dated record, not an edit); no conclusion moves.”

> “* **HEX3_PROOF L438** ("The S3.2-species lower bound (all lifts genuinely ambiguous) shows U₃^σ ≥ q^N is attained by fully-hidden states") — harmless per PE6: the parenthetical is a category slip (the species MEMBERS are ambiguous — two disc ≠ 0 lifts with distinct σ per LEMMA W12-S3.2; a single lift has one σ and cannot be "ambiguous"), not a certification of disc = 0 lifts; the sentence's substance (U₃^σ ≥ q^N via the species) is the annexed bracket's own content.
> * **GENHN_PROOF L153** ("slot-min EXACTLY, for every root θ and every lift — W-9's …") — harmless per PE6: a valuation/slot-min sentence, in PE6's words "valuation/slot-min facts true of every lift," i.e. the same genre the sweep's W-11 row excuses as "valuation facts, not σ-certifications"; not a σ-certification.
> * **GENHN_PROOF L440** — the second occurrence of the same slot-min sentence; harmless by the same PE6 classification as L153.”

> “Counter unchanged: 1/2. This is note-side bookkeeping of a verifier finding, not a repair round (no [r6] tag; no text above this append touched; runner + artifacts stay byte-frozen at seal f669cb0). PE7 attempts the second clean; a second CLEAN accepts at 2/2.”

**CONDITIONALITY:** The record's own line anchors and its third bullet's descriptor are WRONG as written — corrected by sentence at `.76`. Its harmlessness classifications survive on the actual sentences.

**DERIVATION:** An independent re-run of the declared grep, with a per-hit harmlessness classification.

**RESOLUTION TRACE:** Base lines 1913–1948; corrected at lines 1952–1995.

**TEETH:** The re-run grep is the check; PE6's verdict was CLEAN (0C + 0G + 1 MINOR).

---

### EFF.W12.76  [acceptance-box]

**CANONICAL STATEMENT:** Dated re-anchor (2026-08-09, post-PE7) — THE ACCEPTANCE, and the corrected GENHN identifications

> “Provenance: passPE7 (report `W12_passPE7_report.md`, verdict commit fa3acb2: **CLEAN, 0C + 0G + 1 MINOR — the 2-clean counter COMPLETES 1/2 → 2/2; W-12 IS ACCEPTED, the note FROZEN, dated appends only**). Its one MINOR: the PE6-m1 dated record above anchored its two GENHN bullets at line numbers already stale at the record's own commit (GENHN's errata E1–E3 landed BEFORE PE6's verdict and the record), and its third bullet's descriptor is wrong as written. The repair shape PE7 set is this dated re-anchor; the record above stands as written (dated record, not an edit). The corrected identifications, BY SENTENCE, with line numbers dated to their pins:”

> “* The record's "GENHN_PROOF L153" bullet: the slot-min sentence ("slot-min EXACTLY, for every root θ and every lift — W-9's …") sat at **L156 at the record's own HEAD** (its SOLE occurrence there; L153 carried unrelated text). PE6's harmlessness classification (a valuation/slot-min fact, not a σ-certification) attaches to that sentence, and survives on it — PE7 verified this on the actual sentence.
> * The record's "GENHN_PROOF L440 — the second occurrence of the same slot-min sentence" bullet: the second in-scope grep hit sat at **L548 at the record's own HEAD**, and it is NOT the same sentence — it is the dv-display's universality clause ("for every root θ of Φ′ and every lift; the minimum's residue class mod e₁ …"), a DIFFERENT sentence of the same valuation/slot-min genre. "Second occurrence of the same sentence" was never right: even pre-errata (GENHN @ 850e77e, hits at L153/L440/L631) the L440 sentence was already that distinct dv-display clause. The harmlessness classification carries to the actual sentence by the same genre reasoning (a valuation fact, not a σ-certification) — PE7 verified this on the actual sentence.
> * Movement note at THIS append's commit: GENHN's r2 repair round has since landed (d16869c/7650b20/438608a/9636b7e; GENHN HEAD = 9636b7e), and the two sentences now sit at **L167 and L651** (grep re-executed this round, sentence-identical) — the identifications above are by sentence; the line numbers are dated to their named pins.”

> “Counter/freeze: W-12 stays ACCEPTED 2/2 (this append is the MINOR's prescribed cure, not a repair round; no text above this append touched; runner + artifacts byte-frozen at seal f669cb0; the note body before this append = 124,423 bytes, md5 42a7655e, re-verified as byte-prefix after appending).”

**CONDITIONALITY:** **This is the note's acceptance record and its effective-text rule** (frozen, dated appends only). Its methodological content is the identification-by-sentence discipline: line numbers are dated to their pins, sentences are the stable referent.

**DERIVATION:** PE7 re-ran the grep at the record's own HEAD and at the current HEAD, verified each classification on the actual sentence, and dated every line number to a named pin.

**RESOLUTION TRACE:** Base lines 1952–1995. Governs status for the WHOLE note, including shard 1's range.

**TEETH:** Byte-prefix md5 verification (`42a7655e`, 124,423 bytes) after appending; three independent grep executions across three GENHN HEADs.

---

### EFF.W12.77  [changes-record]

**CANONICAL STATEMENT:** Dated adjudication (2026-08-12, sol certification A1) — the R3 chain challenge adjudicated at HEAD

> “The sol-5.6 chain read of this note (gpt-5.6-sol high, runs/residues/R3_w12_output.log, 2026-08-12) returned CHALLENGE with four findings. The A1 certification run (gpt-5.6-sol high, runs/cert/A1_w12_output.log) re-adjudicated all four against HEAD including every dated append: findings 2–4 are REAL with derived repairs — the three dated corrections below; finding 1 is REAL but OBSTRUCTED — no honest repair is derivable from the note's lemmas at HEAD, and the dated obstruction record below names the genuinely new lemma required. Everything above this heading is byte-untouched by this append.”

**CONDITIONALITY:** Four findings, all REAL; one of them **obstructed** — the note explicitly declines to invent a repair and instead specifies the missing lemma. This is the honest-`sorry` discipline applied at the note level.

**DERIVATION:** Decorrelated-model chain read, re-adjudicated at HEAD including every dated append.

**RESOLUTION TRACE:** Base lines 1999–2010.

**READING NOTE:** both cited logs exist in the repo — `runs/residues/R3_w12_output.log` and `runs/cert/A1_w12_output.log` (checked).

**TEETH:** The adjudication is itself a decorrelated-model check of the whole note at HEAD.

---

### EFF.W12.78  [open-obligation]

**CANONICAL STATEMENT:** Dated obstruction (2026-08-12) — W-12.A and order-1 refinement histories

> “W-12.A's displayed count presently proves the depth-zero order-1 cell law, but does not prove its stated coverage of the full order-1 layer. An order-1 refinement history may contain earlier repeated residuals even though its terminal residual is separable. For example, at \(n=2\), \(q\ge3\), \(N\ge5\), history \(H=(1)\) followed by `SPLITEQ(k=2)`, LEMMA W12-L0 gives the per-center count
>
> \[ (q-1)\frac{(q-1)(q-2)}2q^{2N-8}. \]
>
> The terminal separable node contributes only
>
> \[ \frac{(q-1)(q-2)}2q^{2N-8}; \]
>
> the first \(q-1\) is the census of the earlier repeated-residual letter. W-12.A's displayed single-polygon product contains no factor for that earlier node.”

> “Repair at the theorem's accepted strength requires the following genuinely new input: an **all-degree order-1 history-transfer lemma** proving that, after every repeated linear residual root on an \(e=1\) side, the refinement locus for each residual letter is carried to the next degree-\(d\) node by an explicit uniform finite-window fiber bijection; the lemma must give the fiber's exact \(q\)-exponent, prove compatibility under concatenation and branch splitting, and show that the product of the intermediate residual censuses and fiber factors terminates in the stated Ore certificate. W12-L0 supplies this only for \(n=2\), W12-L1 only transports that case, and ANNEX 2 supplies the two cubic node species only at \(n=3\). No such all-degree lemma is proved at HEAD.”

> “Consequently the displayed formula and the claims “the order-1 layer at all degrees” and “every W-11 row is an instance” cannot all be certified from the present proof. Narrowing W-12.A to depth-zero shapes would weaken an accepted theorem statement and is therefore not an admissible repair. The all-degree history-transfer lemma above must be proved before this obstruction can be closed.”

**CONDITIONALITY:** **CLOSED** by the dated discharge (`.83`–`.87`): “The dated obstruction is closed.” The obstruction is retained here because it is the *specification* the discharged lemma had to meet, and because it records the one repair route explicitly ruled out (narrowing W-12.A would weaken an accepted statement).

**DERIVATION:** A concrete counter-instance to the display's coverage claim (`n = 2`, `q ≥ 3`, `N ≥ 5`, `H = (1)` then `SPLITEQ(2)`), with the missing factor identified as the earlier repeated-residual letter's census; plus a no-cure sweep over W12-L0 / W12-L1 / ANNEX 2.

**RESOLUTION TRACE:** Base lines 2012–2030; closed at lines 2192–2429.

**TEETH:** The counter-instance is an exact count comparison against LEMMA W12-L0's own row.

---

### EFF.W12.79  [lemma]

**CANONICAL STATEMENT:** Dated correction (2026-08-12) — the level-0 decoration-orbit factor `κ(T)` in W-12.A

> “In W-12.A's displayed count, the level-0 prefactor \(C_0(q)\) is corrected to \[ \kappa(T)\,C_0(q). \]”

> “For every pair \((d,m)\), let \(r_{d,m}\) be the number of level-0 branches of degree \(d\) and multiplicity \(m\). Let \(D\) range over the complete letter-free branch decorations occurring on those branches — polygon, residual factorization data, and, wherever supplied, the complete refinement history — and let \(r_{d,m,D}\) be the multiplicity of decoration \(D\). Define \[ \kappa(T):= \prod_{d,m} \frac{r_{d,m}!}{\prod_D r_{d,m,D}!}. \] Thus the corrected depth-zero display is \[ \#T(N)= \kappa(T)C_0(q)\! \prod_{i:m_i=1}q^{d_i(N-1)} \prod_{i:m_i\ge2} \left[ \left(\prod_S S_{\lambda_{i,S}}(q^{d_i})\right) q^{d_iB_i(N)} \right]. \]”

**CONDITIONALITY:** `κ(T) = 1` whenever all decorations in each `(d, m)` class agree — hence “no committed number moves”: the sealed rows are single-repeated-branch (TRP/QRT) or have distinct `(d, m)` classes (DBL).

**DERIVATION:** Quoted derivation:

> “**Derivation.** Fix an undecorated level-0 configuration counted by \(C_0(q)\). Within a class of \(r_{d,m}\) distinct irreducible branches having the same degree and multiplicity, the branch polynomials are distinguishable after the configuration is fixed, while the shape records only the multiset of letter-free decorations. The number of assignments of that multiset to the \(r_{d,m}\) actual branches is \[ \frac{r_{d,m}!}{\prod_D r_{d,m,D}!}. \] By LEMMA W12-S2.1, the branch fibers multiply; permuting the decorations therefore leaves the product of the branch counts unchanged. Multiplying over the \((d,m)\)-classes gives \(\kappa(T)\). No factor is introduced when all decorations in a class agree, because then \(\kappa=1\).”

with a worked diagnostic:

> “For the diagnostic shape \[ \bar f=(x-a)^2(x-b)^2,\qquad a\ne b, \] decorated by `RAM(1)` and `RAM(3)`, one has \[ C_0(q)=\binom q2,\qquad A_1=(q-1)q^{2N-3},\qquad A_3=(q-1)q^{2N-6}, \] and \(\kappa(T)=2\). Hence the corrected law gives \[ 2\binom q2A_1A_3=q(q-1)A_1A_3, \] exactly the two possible assignments of the distinct decorations to \(\{a,b\}\). If both decorations agree, \(\kappa(T)=2!/2!=1\), so no double-counting occurs.”

> “This orbit correction is independent of the separate order-1 history-transfer obstruction.”

**RESOLUTION TRACE:** Base lines 2032–2091; applies to shard 1's W-12.A (`.09`(a)) and is re-derived as `κ₀(T)` inside LEMMA W12-HT (`.83`, `.86`).

**TEETH:** The verification note records that `κ(T) = 1` was “re-checked on every sealed and every consumed instance”, and that the battery's GREEN is consistent with the defect because no sealed row exercises two same-`(d, m)` branches with distinct decorations.

---

### EFF.W12.80  [lemma]

**CANONICAL STATEMENT:** Dated correction (2026-08-12) — rationality and uniformity of the core coefficient in (A1)

> “In W-12.D hypothesis (A1), replace
>
> > “a density law \(\operatorname{dens}_F(x)=c_F(q)q^{-\ell_F(x)}\) … with all data (families, \(c_F\), \(\ell_F\), \(P_F\), \(\nu_F\)) independent of \(q\) and of the characteristic”
>
> by
>
> > “a density law \[ \operatorname{dens}_F(x)=c_F(q)q^{-\ell_F(x)}, \] where a single rational function \(c_F(X)\in\mathbb Q(X)\) is fixed for the family and \(c_F(q)\) denotes its evaluation at \(X=q\); the family list, \(\ell_F\), \(P_F\), \(\nu_F\), and the rational expression \(c_F(X)\) are independent of the characteristic and of the chosen prime power \(q\).””

**CONDITIONALITY:** A hypothesis-interface repair with no conclusion change; every firing survives it (“the supplied menus at n = 2/3/4/5 re-checked to carry fixed rational-expression coefficients”).

**DERIVATION:** Step 1 re-derived under the corrected hypothesis:

> “**Derivation of Step 1 under the corrected hypothesis.** On a shifted product \[ P_F=\prod_i(a_i+b_i\mathbb Z_{\ge0}), \] first absorb every point coordinate \(b_i=0\), as already prescribed in Step 1. For every remaining coordinate, integer-valuedness of \(\ell_F\) on \(P_F\) gives \[ m_ib_i=\ell_F(x+b_ie_i)-\ell_F(x)\in\mathbb Z_{>0}, \] while \[ \ell_F(a)=m_0+\sum_i m_ia_i\in\mathbb Z. \] Therefore \[ \sum_{x\in P_F}\operatorname{dens}_F(x) = c_F(q)q^{-\ell_F(a)} \prod_i(1-q^{-m_ib_i})^{-1}, \] which is the evaluation at \(X=q\) of \[ c_F(X)X^{-\ell_F(a)} \prod_i(1-X^{-m_ib_i})^{-1}\in\mathbb Q(X). \] Finite unions follow by inclusion–exclusion, and the finite sum over families remains in \(\mathbb Q(X)\). This proves both rationality and the “same expression at every prime power” conclusion. The \(n=2\) coefficients such as \(q-1\) and \((q-1)/(2q)\) now satisfy (A1) as evaluations of fixed rational functions, rather than as constants independent of \(q\).”

**RESOLUTION TRACE:** Base lines 2093–2141; applies to shard 1's `.12` (A1), `.42` (Step 1) and `.44` (the n = 2 instance's admissibility).

**TEETH:** The verification note records the literal conflict confirmed (“the literal conflict with the q-dependent n = 2 coefficients confirmed”) and both Step-1 guards re-checked.

---

### EFF.W12.81  [changes-record]

**CANONICAL STATEMENT:** Dated correction (2026-08-12) — W12-BOX-1 dependency range

> “In W12-BOX-1, the reference
>
> > “the route is priced in S4.2 ((H-a)–(H-d))”
>
> is corrected to
>
> > “the route is priced in S4.2 ((H-a)–(H-e)).”
>
> S4.2 explicitly enumerates five inputs. In particular, `(H-e)` is the order-\(\ge2\) GMN leaf/σ-decision theorem together with the in-window pinning supplied by `(H-a)` and `(H-b)`; it is separately load-bearing for the composite-stage analogue of S2.3 and for W-12.D's σ-labeling requirement. The correction changes no mathematical conclusion; it restores the box's dependency record to the five-input list already displayed in S4.2.”

**CONDITIONALITY:** Bookkeeping only; no conclusion changes. It matters because `(H-e)` is the composite-stage analogue of the σ-certification that W-12.D's (A1) clause needs — dropping it from the box's record would understate the order-≥ 2 conditionality.

**DERIVATION:** Comparison against §S4.2's own five-member list.

**RESOLUTION TRACE:** Base lines 2143–2153; applies to shard 1's `.49`.

**TEETH:** The verification note: “BOX-1's ‘(H-a)–(H-d)’ confirmed at HEAD against S4.2's five-input list ((H-e) added at PE1 F2), no prior dated append correcting it.”

---

### EFF.W12.82  [changes-record]

**CANONICAL STATEMENT:** A1 provenance and orchestrator verification before transcription

> “*(The obstruction record and three corrections above were derived by the A1 certification run (gpt-5.6-sol high, runs/cert/A1_w12_output.log, 2026-08-12); orchestrator verification before transcription — finding 1: the S2.6 sentence quoted verbatim at HEAD; W12-L0's (q−1)^t prefactor re-read and the H = (1) → SPLITEQ(k = 2) count (q−1)·((q−1)(q−2)/2)·q^{2N−8} re-derived from the lemma display with its constraints (s+1 ≤ k ≤ M ⟹ N ≥ 5; q ≥ 3); W-12.A's displayed product confirmed history-factor-free while its SHAPE datum includes refinement history and its claim text asserts the full order-1 layer + "every W-11 row is an instance"; the no-cure sweep re-read at HEAD (W12-L0 "Fix n = 2"; W12-L1 = the DBL transport; ANNEX 2 = HMENU3's two n = 3 node species; S2.2 = one fixed Φ-adic polygon). Finding 2: S2.1's C₀(q) confirmed as the undecorated census (unordered within same-(d,m) classes); S2.5's machine-sealed quartic rows confirmed to be the QUADRUPLE center (one branch), so no sealed row exercises two same-(d,m) branches with distinct decorations — the battery's GREEN is consistent with the defect; the diagnostic count re-derived independently (C(q,2)·2·A₁·A₃ with A₁/A₃ from W12-L0's RAM(1)/RAM(3) rows); κ(T) = 1 re-checked on every sealed and every consumed instance (single repeated branch, or DBL's distinct (d,m) classes), so no committed number moves. Finding 3: the (A1) span quoted verbatim; the literal conflict with the q-dependent n = 2 coefficients confirmed; the repair's geometric-series derivation checked against Step 1's own r1 (b_i = 0 absorption) and r2 (m_ib_i ∈ ℤ_{>0}) guards; the supplied menus at n = 2/3/4/5 re-checked to carry fixed rational-expression coefficients, so every W-12.D firing survives the corrected hypothesis. Finding 4: BOX-1's "(H-a)–(H-d)" confirmed at HEAD against S4.2's five-input list ((H-e) added at PE1 F2), no prior dated append correcting it. Transcribed unaltered per the standing division of labor. Ledger: W-12's row stays OPEN — the three corrections await sol discharge-confirmation, and the obstruction closes only when the all-degree order-1 history-transfer lemma is proved.)*”

**CONDITIONALITY:** The closing ledger line (“W-12's row stays OPEN … the three corrections await sol discharge-confirmation”) is a protocol state, superseded in part by the discharge (`.87`) and — externally — by the SOL ledger (§8 reading note).

**DERIVATION:** Per-finding orchestrator verification, each item re-derived at HEAD before transcription.

**RESOLUTION TRACE:** Base lines 2155–2188.

**READING NOTE:** `runs/cert/A1_w12_output.log` exists in the repo (checked).

**TEETH:** Four independent re-derivations (the counter-instance count, the diagnostic `κ` count, the Step-1 guards, the five-input list).

---

### EFF.W12.83  [lemma]

**CANONICAL STATEMENT:** LEMMA W12-HT (ALL-DEGREE ORDER-1 HISTORY TRANSFER) — setting and statement

> “This append discharges the dated obstruction immediately above. It consumes W-12 S2.1 (coprime branch multiplication), W-12 S2.2 (the \(\Phi\)-adic digit calculus and right-to-left residual normalization), W-11 S2.3 (finite-window recentering measure isomorphism), W12-L0, W12-L1, and GENIND-1 (fracture permanence, at its stated **PROVED** grade). From GENIND-1 only fracture permanence is used: after a coprime residual fracture, later translations internal to one repeated cluster neither alter nor re-couple the other clusters. No order-\(\ge2\) leaf theorem or open \(\mu\ge3\) assertion is consumed.”

Setting (node data, the two exponents, and the side-local orbit factor):

> “Fix a letter-free, history-resolved, window-visible decided order-1 key \(T\). Its level-0 datum is the unordered combinatorial configuration \[ \{(d_i,m_i)\}_i,\qquad \sum_i d_im_i=n, \] while the actual distinct irreducibles \(\bar P_i\) are the letters ranged over by \(C_0(q)\). Put \(Q_i=q^{d_i}\).”

> “For each repeated branch \(i\), let \(T_i\) be its complete order-1 refinement tree. A node \(v\in T_i\) has multiplicity \(m_v\), previous center depth \(s_v\) (zero at the root), exact polygon \(P_v\), and residual factorization type \(\lambda_{v,S}\) on every side \(S\). Its children are precisely the repeated linear factors \[ (Y-z)^{m_u} \] on \(e=1\) sides. If the side has slope \(-s_u\), the child is the degree-\(d_i\) conservative node of multiplicity \(m_u\) and depth \(s_u\). Repeated factors of degree \(>1\), and repeated factors on \(e>1\) sides, open composite stages and are outside this order-1 statement. Every leaf of a decided order-1 key has separable residuals.”

> “Define \[ B_v(N)=m_vN-\sum_{j<m_v}\lceil P_v(j)\rceil-L_v, \qquad L_v=\#\{j<m_v:P_v(j)\in\mathbb Z\}, \] and, for a non-root node, \[ D_v(N)=\sum_{j<m_v} \max\!\bigl(N-((m_v-j)s_v+1),0\bigr). \] Thus \[ C_{m_v}(s_v)= \{(a_j)_{j<m_v}:v(a_j)\ge(m_v-j)s_v+1\} \] has exactly \(Q_i^{D_v(N)}\) elements.”

> “The internal orbit factor is side-local. For a side \(S\), multiplicity \(a\), and child history \(H\), let \(r_{v,S,a,H}\) count the repeated linear roots on \(S\) of multiplicity \(a\) carrying \(H\), and put \(r_{v,S,a}=\sum_Hr_{v,S,a,H}\). Define \[ \kappa_v= \prod_{S,a}\frac{r_{v,S,a}!}{\prod_Hr_{v,S,a,H}!}. \tag{HT-orbit} \] Equivalently, in the abbreviated notation \(\prod_a r_{v,a}!/\prod_Hr_{v,a,H}!\), the multiplicity label \(a\) is understood to include its side. The side tag is necessary because roots on different sides cannot be permuted; it is exactly the `side_index` convention used by the N1 certificate.”

The lemma:

> “> **LEMMA W12-HT (ALL-DEGREE ORDER-1 HISTORY TRANSFER).** After fixing the actual normalized residual polynomial on every side of a node \(v\), there is a finite-window bijection
> > \[ \mathcal E_v(\mathbf R) \simeq \mathcal U_v(\mathbf R)\times \prod_{u\text{ child of }v}C_{m_u}(s_u), \tag{HT-fiber} \]
> > compatible with further recentering and with coprime branch fracture, where \(\mathcal E_v(\mathbf R)\) is the exact polygon cell with those residual letters and
> > \[ \#\mathcal U_v(\mathbf R) = Q_i^{B_v(N)-\sum_{u\text{ child}}D_u(N)}. \tag{HT-free} \]
> > The bijection and its fiber size are independent of the residual letters. Consequently
> > \[ \#(v)= Q_i^{B_v(N)} \left(\prod_{S\subset P_v}S_{\lambda_{v,S}}(Q_i)\right) \kappa_v \prod_{u\text{ child}} \frac{\#(u)}{Q_i^{D_u(N)}}. \tag{HT-rec} \]
> > The recursion terminates at separable Ore leaves, and hence
> > \[ \boxed{ \mathcal H_i(T,N)= \left( \prod_{v\in T_i}\kappa_v \prod_{S\subset P_v}S_{\lambda_{v,S}}(Q_i) \right) Q_i^{ \sum_{v\in T_i}B_v(N)- \sum_{\substack{v\in T_i\\v\ne\mathrm{root}}}D_v(N)}.} \tag{HT-branch} \]”

Level zero and the global law:

> “At level zero, let \(r_{d,m,H}\) count branches of degree \(d\) and multiplicity \(m\) carrying complete decoration/history \(H\), and set \[ \kappa_0(T)= \prod_{d,m}\frac{r_{d,m}!}{\prod_Hr_{d,m,H}!}. \] Then \[ \boxed{ \#T(N)= \kappa_0(T)C_0(q) \prod_{i:m_i=1}q^{d_i(N-1)} \prod_{i:m_i\ge2}\mathcal H_i(T,N).} \tag{HT-global} \]”

**CONDITIONALITY:** Order-1 only: “Repeated factors of degree \(>1\), and repeated factors on \(e>1\) sides, open composite stages and are outside this order-1 statement.” Consumes GENIND-1 at fracture permanence only, at its PROVED grade; consumes no order-≥ 2 leaf theorem and no open `μ ≥ 3` assertion.

**DERIVATION:** `.84`–`.86` (the six proof steps).

**RESOLUTION TRACE:** Base lines 2192–2289. **`(HT-global)` is the effective statement of THEOREM W-12.A** (shard 1 `.09`), with the S1 display as its depth-zero specialization.

XREF: `lean/notes/openmath/GENIND_PROOF_2026-08-08.md:GENIND-1` — grep-verified count **15**.

XREF: `lean/notes/openmath/W11_PROOF_2026-08-08.md:S2.3` — grep-verified count **8**; the recentering measure isomorphism generalized here.

**TEETH:** The N1 machine certificate (`verification/openmath/w12_history_law_check.py`): 1,196 per-key comparisons, 0 mismatches, four teeth, 300 translation-rank + 322 coprime-multiplication-rank tests (`.87`).

---

### EFF.W12.84  [lemma]

**CANONICAL STATEMENT:** LEMMA W12-HT proof — steps 1 and 2 (the exact node cell; transfer at one repeated linear root)

> “**1. The exact node cell.** Work on one degree-\(d_i\) branch and write \(Q=Q_i\). Monic division by the current degree-\(d_i\) key polynomial gives \[ F=\Phi^m+\sum_{j<m}a_j\Phi^j, \qquad a_j\in(\mathcal O/\pi^N)[x]_{<d_i}. \] Each digit of \(a_j\) is one element of \(\mathbb F_Q\). Prescribing \(P_v\) leaves \[ mN-\sum_{j<m}\lceil P_v(j)\rceil \] slots. At each of the \(L_v\) integral boundary positions, one digit is priced by the residual polynomial rather than left free. Therefore, after fixing the actual residual polynomials \(\mathbf R=(R_S)_S\), \[ \#\mathcal E_v(\mathbf R)=Q^{B_v(N)}. \tag{1} \] This is S2.2's digit calculation and does not require separability. Its right-to-left sweep also applies unchanged: one side's monic normalization fixes the shared vertex unit for the next side. Summing residual letters of the prescribed types therefore contributes exactly \[ \prod_SS_{\lambda_{v,S}}(Q), \] with no additional unit factor.”

> “**2. Transfer at one repeated linear root.** Let \((Y-z)^a\) be a repeated factor on an \(e=1\) side of slope \(-k\). Isolate its degree-\(a\) cluster by the coprime residual factorization. If \(G\) denotes the monic cluster factor, its slope-normalized reduction is \((Y-z)^a\).
> Choose a lift \(\widetilde z\), put \[ \Psi=\Phi-\widetilde z\pi^k, \qquad G=\Psi^a+\sum_{j<a}b_j\Psi^j. \] After dividing the coefficient of \(\Psi^j\) by \(\pi^{(a-j)k}\), its residue is the corresponding coefficient of \[ (Y+z-z)^a=Y^a, \] and hence vanishes. Thus \[ v(b_j)\ge(a-j)k+1\qquad(j<a). \tag{2} \] Therefore \((b_j)\in C_a(k)\). Conversely, (2) makes the normalized residual of the inverse translate equal to \((Y-z)^a\).
> Translation is unitriangular on the finite coefficient module, with inverse translation by \(-\widetilde z\pi^k\). When \(d_i>1\), multiplication by a degree-\(<d_i\) representative of \(z\) may create degree-\(\ge d_i\) terms; monic redivision by the new key absorbs them, and the change between the two \(\Phi\)-adic developments remains block-unitriangular on the \(d_i\)-dimensional digit blocks. This is exactly S2.2's monic-division digit calculus. Hence the map is bijective in every characteristic and at every finite window, including when some conservative lower bounds lie beyond the window.
> This is W-11 S2.3's measure-isomorphism mechanism without the quadratic restriction. It gives \[ \#C_a(k) = \prod_{j<a}Q^{\max(N-((a-j)k+1),0)} = Q^{D_u(N)}. \tag{3} \] Changing the chosen lift of \(z\) composes the map with another unitriangular translation and changes neither the node nor its fiber size.”

**CONDITIONALITY:** Step 1 holds without separability; step 2's bijectivity is asserted “in every characteristic and at every finite window, including when some conservative lower bounds lie beyond the window”.

**DERIVATION:** As quoted — the digit count of `.23`/`.24` (shard 1) re-run at a node, then the binomial vanishing after `π^{(a−j)k}`-normalization giving `C_a(k)` membership, with block-unitriangularity handling `d_i > 1`.

**RESOLUTION TRACE:** Base lines 2293–2344.

**TEETH:** The certificate's 300 translation-rank tests (step 2's unitriangularity).

---

### EFF.W12.85  [lemma]

**CANONICAL STATEMENT:** LEMMA W12-HT proof — steps 3 and 4 (simultaneous children; histories and orbit factors)

> “**3. Simultaneous children and the free fiber.** On one side, the distinct residual factors are coprime. Factors belonging to different sides have already fractured in the Newton decomposition. At each weighted digit height, the linearization of multiplication is \[ (A_\alpha)_\alpha\longmapsto \sum_\alpha A_\alpha\prod_{\beta\ne\alpha}\bar G_\beta. \tag{4} \] If (4) vanishes, reduction modulo each \(\bar G_\alpha\), coprimality, and the degree bound force every \(A_\alpha=0\). Source and target have the same digit dimension, so (4) is an isomorphism. Solving successively by height gives the finite-window multiplication bijection, exactly as in W12-S2.1, now on the weighted side modules.
> At general degree, GENIND-1's proved fracture permanence says that later translations internal to one cluster do not change or re-couple its coprime siblings. Thus the child coordinates from Step 2 occur independently and simultaneously. All remaining factor and higher-digit coordinates form \(\mathcal U_v(\mathbf R)\), proving (HT-fiber). Comparing (1) and (3) gives \[ \#\mathcal U_v(\mathbf R) = Q^{B_v(N)-\sum_uD_u(N)}. \] In particular, the exponent is a nonnegative integer; divisibility by the complete child-node volumes is a consequence of the bijection, not an assumption.
> Every matrix used here is either block-unitriangular or a coprime multiplication matrix. The construction is therefore independent of the residual letters. It specializes to W-11 S2.3 for one quadratic cluster and to W12-L1's unit-scaled-letter calculation for the first fractured case.”

> “**4. Histories and orbit factors.** In (HT-fiber), replace each complete ambient node \(C_{m_u}(s_u)\) by the subset realizing the selected child history. Bijectivity makes its relative factor exactly \[ \frac{\#(u)}{Q^{D_u(N)}}. \] For a fixed actual residual polynomial, its repeated roots are distinguished by their values. If the letter-free key records only a multiset of histories among the \(r_{v,S,a}\) roots on one side having multiplicity \(a\), the number of assignments to those actual roots is \[ \frac{r_{v,S,a}!}{\prod_Hr_{v,S,a,H}!}. \] Multiplication over \((S,a)\) gives \(\kappa_v\). Summing the actual residual polynomials supplies the residual censuses of Step 1. These independent choices inserted into (HT-fiber) prove (HT-rec).
> The construction respects concatenation: the child tuple output by one transfer is the input tuple for the next, and unitriangular translations compose. It respects fracture: uniqueness in the multiplication bijection identifies the same cluster before and after operations on its siblings, while GENIND-1 prevents re-coupling.
> Thus every non-root node occurs once as a child and contributes \(-D_v(N)\) exactly once. Every node contributes \(B_v(N)\), its side censuses, and \(\kappa_v\) exactly once. Iteration proves (HT-branch).”

**CONDITIONALITY:** GENIND-1 enters exactly here and only as fracture permanence. The nonnegativity of the free exponent is derived, not assumed.

**DERIVATION:** As quoted — coprimality + degree bound + dimension equality make the multiplication linearization an isomorphism; fracture permanence makes the child coordinates simultaneous; the orbit factor is a multiset-to-roots assignment count.

**RESOLUTION TRACE:** Base lines 2346–2376.

**TEETH:** The certificate's 322 coprime-multiplication-rank tests (step 3) and the `DROP-KAPPA0` (370) / `DROP-HISTORY-CENSUS` (302) teeth (step 4).

---

### EFF.W12.86  [lemma]

**CANONICAL STATEMENT:** LEMMA W12-HT proof — steps 5 and 6 (termination and Ore certification; level zero)

> “**5. Termination and Ore certification.** At depth \(s_v\), the conservative inequalities put every point \(j<m_v\) strictly above the line of slope \(-s_v\) ending at \((m_v,0)\). If a side has slope \(-k\), writing its endpoint heights as \[ y=(m_v-j)s_v+\delta,\qquad \delta>0, \] and using lower-polygon convexity shows first that the rightmost \(k>s_v\), and then that every earlier principal-side \(k\) is at least as large. Hence every eligible \(e=1\) child satisfies \[ s_u=k\ge s_v+1. \tag{5} \] For a window-visible node, \[ m_vs_v+1\le P_v(0)\le N-1, \] so \(s_v\) is bounded in terms of \(N\). Therefore no root-to-leaf chain is infinite. Fracture can only split total cluster multiplicity, and GENIND-1 says clusters never merge again.
> The recursion consequently terminates. By the definition of a decided order-1 key, every terminal residual is separable. S2.3's order-1 Ore theorem then certifies, for every disc-nonzero lift, one étale piece for each terminal side factor with its displayed \((e,f)\). A repeated factor of residual degree \(>1\), or one occurring on an \(e>1\) side, instead opens an order-\(\ge2\) key and remains under [W12-H].”

> “**6. Level zero.** W12-S2.1 makes the actual level-0 branches independent. After an undecorated configuration counted by \(C_0(q)\) is fixed, its irreducible factors are distinguishable. Assigning the recorded multiset of complete decorations to the \(r_{d,m}\) factors in one \((d,m)\)-class contributes \[ \frac{r_{d,m}!}{\prod_Hr_{d,m,H}!}. \] Permuting decorations does not change the product of branch counts. Multiplication over \((d,m)\) gives \(\kappa_0(T)\); simple branches contribute \(q^{d_i(N-1)}\), and repeated branches contribute (HT-branch). This proves (HT-global). \(\square\)”

**CONDITIONALITY:** The Ore certification is at the **disc ≠ 0** quantifier (“for every disc-nonzero lift”) — consistent with shard 1's `[r4]`-struck parenthetical. The order-≥ 2 fence is restated at the termination step: such factors “remain under [W12-H]”.

**DERIVATION:** Termination from strict depth increase (`s_u ≥ s_v + 1`, by lower-polygon convexity) plus the window bound on `s_v`; level zero from W12-S2.1's independence and the same multiset-assignment count as `.79`'s `κ(T)`.

**RESOLUTION TRACE:** Base lines 2378–2399. Step 6's `κ₀(T)` is `.79`'s κ(T) with decorations extended to complete histories.

**TEETH:** The certificate's `DROP-L` tooth (1,136) and `BASE-q-LETTERS` (22).

---

### EFF.W12.87  [scope-record]

**CANONICAL STATEMENT:** LEMMA W12-HT — consumer sweep, restoration of W-12.A, and the discharge conclusion

> “- **The dated obstruction is discharged.** For \(H=(1)\) followed by `SPLITEQ(2)`, \[ B_{\mathrm{root}}=D_{\mathrm{child}}=2N-5. \] The root census is \(S_{(1^2)}(q)=q-1\); the leaf census is \((q-1)(q-2)/2\); and the remaining leaf exponent is \(2N-8\). Hence (HT-branch) gives \[ (q-1)\frac{(q-1)(q-2)}2q^{2N-8}, \] exactly W12-L0's count.
> - **W-12.A regains full order-1 coverage.** Its controlling formula is (HT-global), with complete histories, transfer normalization, and the dated level-0 orbit correction. The former display is the depth-zero specialization: there are no non-root \(D_v\)-terms and no internal history orbit.
> - **W12-L0 is recovered.** At multiplicity two, a nonterminal node has one repeated root, so \(\kappa_v=1\), and its free exponent equals the next conservative-node exponent. The exponents telescope, while every repeated residual supplies \(q-1\). This is W12-L0's \((q-1)^t\) factor and its six leaf laws.
> - **W12-L1 is compatible.** Its quadratic block is one child coordinate of (HT-fiber); the coprime linear branch supplies \(q^{N-1}\). Its unit-scaled letters are the two-factor instance of the letter-blind construction above.
> - **The cubic consumers agree.** HM3.A's \(\alpha\)- and \(\beta\)-species are respectively the unfractured and fractured cases of (HT-fiber); the raw-key dictionary is the child-coordinate identification above.
> - **Both orbit corrections are complete.** Branches sharing \((d,m)\) are handled by \(\kappa_0(T)\). Repeated roots on one residual side are handled by \(\kappa_v\). The side tag prevents false permutations across polygon sides and matches the certificate's grouping.
> - **Composite-stage and drainage boxes do not move.** The lemma stops where an order-2 key opens. [W12-H], W12-BOX-1's inputs (H-a)–(H-e), W-12.B, and the tail problems are unchanged.
> - **Phase-B transcription.** A history-resolved order-1 menu entry must implement (HT-rec), retaining complete child-history multisets, side tags, \(D_v\), \(\kappa_v\), and \(\kappa_0\).
> - **Machine certificate.** The independent certificate reports 1,196 per-key comparisons and zero mismatches for \(n\in\{3,4\}\), \(q\in\{2,3\}\), \(N\le6\). Its teeth fire 302 (`DROP-HISTORY-CENSUS`), 22 (`BASE-q-LETTERS`), 370 (`DROP-KAPPA0`), and 1,136 (`DROP-L`). All 300 translation-rank and 322 coprime-multiplication-rank tests pass. These checks corroborate the local normalizations and side-local orbit convention; the proof above supplies the all-degree warrant.”

> “**Discharge conclusion.** The dated obstruction is closed. The corrected W-12.A law for every window-visible decided order-1 shape is (HT-global), with per-branch term (HT-branch). Thus “the order-1 layer at all degrees” and “every W-11 row is an instance” are again justified by the note's proved mechanisms.”

**CONDITIONALITY:** Two scope statements are load-bearing downstream: the boxes explicitly **do not move** (`[W12-H]`, `(H-a)–(H-e)`, W-12.B and the tail problems unchanged — note the corrected five-input range is used here), and the certificate is corroboration, not the warrant (“the proof above supplies the all-degree warrant”), on a restricted grid `n ∈ {3,4}`, `q ∈ {2,3}`, `N ≤ 6`.

**DERIVATION:** The obstruction instance re-computed through (HT-branch); each prior lemma re-derived as a specialization.

**RESOLUTION TRACE:** Base lines 2401–2429. This unit is what makes shard 1's `.09`, `.14` effective at full order-1 coverage, and it amends **[merge finding: source labels this "shard 1's", but shard 1's own `.10` is CONJECTURE W-12.B with no Phase-B content — content match (and the reciprocal pointer above) identifies the referent as this shard's own `.10`, merged `.62`; recorded as a source citation defect, §8]** `.62`-adjacent Phase-B consumer spec (`.62` here).

XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:THEOREM HM3.C` — grep-verified count **10**; the cubic consumers (HM3.A's two species) identified as (HT-fiber)'s two cases.

**READING NOTE:** the certificate file `verification/openmath/w12_history_law_check.py` exists in the repo (checked).

**TEETH:** The N1 certificate — 1,196 per-key comparisons, 0 mismatches, four named teeth at 302/22/370/1,136, plus 300 + 322 rank tests.

---

### EFF.W12.88  [changes-record]

**CANONICAL STATEMENT:** P1 provenance and orchestrator verification of LEMMA W12-HT

> “*(LEMMA W12-HT above was composed by the P1 certification run (gpt-5.6-sol high, runs/cert4/P1_w12_history_output.log, 2026-08-12) from the N1-conjectured law after its machine certificate came back GREEN (verification/openmath/w12_history_law_check.py: 1,196 per-key comparisons, 0 mismatches, teeth DROP-HISTORY-CENSUS 302 / BASE-q-LETTERS 22 / DROP-KAPPA0 370 / DROP-L 1,136, 300 translation-rank + 322 coprime-multiplication-rank tests green; n ∈ {3,4}, q ∈ {2,3}, N ≤ 6). Orchestrator verification before transcription — the side-local correction to N1's κ_v checked against the certificate's own side_index grouping; step 2's translation argument checked (binomial vanishing after π^{(a−j)k}-normalization ⟹ C_a(k) membership; block-unitriangular redivision at d_i > 1); step 3's multiplication isomorphism checked (coprimality + degree bound + dimension equality, the W12-S2.1 mechanism on weighted modules; GENIND-1 consumed at fracture permanence only, PROVED grade); step 5's termination (convexity ⟹ s_u ≥ s_v + 1; window-visibility bounds the depth); the obstruction instance re-computed (B_root = 2N−5 = D_child, telescope, (q−1)·((q−1)(q−2)/2)·q^{2N−8} = W12-L0's row); the W12-L0/L1/HM3.A specializations and the depth-0 reduction to the κ(T)-corrected W-12.A display confirmed. Transcribed unaltered per the standing division of labor. Ledger: row 12 → the obstruction is DISCHARGED; a final transcription-confirmation rides the next queue.)*”

**CONDITIONALITY:** The **order of work** is recorded and matters: the law was conjectured (N1), machine-certified GREEN, and only then composed into a proof (P1) and hand-verified before transcription. The closing ledger line leaves a final transcription-confirmation outstanding at the note's own record — see OPEN-CALL 2 and its reading note.

**DERIVATION:** Five named orchestrator re-derivations (κ_v side-locality, step 2, step 3, step 5, the obstruction instance) plus the specialization checks.

**RESOLUTION TRACE:** Base lines 2431–2453 — the note's final lines.

**READING NOTE:** `runs/cert4/P1_w12_history_output.log` exists in the repo (checked).

**TEETH:** The N1 certificate is the pre-composition GREEN; the orchestrator re-derivations are the decorrelated hand check.

---

### AMENDMENT (carried forward verbatim from shard 1's tail, dated append 2026-08-14) — NOT a statement unit; edits nothing in place

**Placement note (this merge's own framing, not source text).** This block is shard 1's
own dated append, reproduced byte-for-byte below with only its top-level heading demoted
to fit this section's hierarchy. It is placed here, at the tail of the merged statement
inventory — after the last shard-1-native unit (`.52`) AND after the last shard-2-derived
unit (`.88`), since the amendment postdates the compilation of both shards and its own
text says so ("dated append, 2026-08-14, post-compilation"). **It is not one of the 88
numbered statement units and carries no `EFF.W12.NN` ID of its own** — it is a dated
correction to the append/consumption-PROTOCOL reading of exactly three sites (`.18`'s
CONDITIONALITY paragraph above, the pre-amendment HMENU3 row of the original §3.2-style
consumer ledger folded into §5 below, and OPEN-CALL 2 in §8), never to any mathematical
content. Per this repo's living-artifact convention — documented in the amendment's own
text below, and matching how GENTOW5/HMENU3 themselves handle corrections — **the
originally-compiled text at `.18`, and the original OPEN-CALL 2 wording in §8, are
preserved byte-unchanged**; this amendment edits nothing in place. **Wherever this
merge's OWN freshly-assembled consolidated ledger (§5) or OPEN-CALL status (§8) reports
the status of the three superseded sites, that fresh reading follows the AMENDMENT, not
the stale original** — a newly-built consolidated summary is not "the original compiled
text" the convention protects, exactly as the amendment's own closing paragraph instructs
below. The reasoning is made explicit at each of those three landing sites rather than
picked silently.

#### AMENDMENT (verbatim original text) (dated append, 2026-08-14, post-compilation; the compiled text above is NOT edited): the HMENU3 quantifier correction LANDED — three OWED/NOT-LANDED sites superseded

**What is superseded, quoted exactly, byte-verified at HEAD (`grep -cF`, count in parens — each is unique):**

1. **§3.2 crossref row (~L1312).** `| HMENU3 | ... | **OWED AND NOT LANDED.** The correction is drafted at \`lean/notes/openmath/HMENU3_annex_draft_r5.md\` (file present); application "is the orchestrator's". Verified at HEAD: \`HMENU3_PROOF_2026-08-08.md\` L216–219 still reads "so Ore certifies EVERY lift". See OPEN-CALL 2 |` (1).
2. **`.18` CONDITIONALITY (~L478).** "…the HMENU3-side phrasing correction is owed and drafted but **not landed** (`.02`'s protocol note; the draft is `lean/notes/openmath/HMENU3_annex_draft_r5.md`)." (1).
3. **OPEN-CALL 2 (~L1408).** Header "### OPEN-CALL 2 — the owed HMENU3 quantifier correction is drafted but NOT applied" (1); body "**Verified at HEAD:** `HMENU3_PROOF_2026-08-08.md` lines 216–219 still read *"so Ore certifies EVERY lift…"* — the annex has **not** been applied. … **Decision needed:** land the drafted annex, or record the obligation in the spec's hypothesis-closure ledger." (1).

**Why all three are stale.** Each site's own evidence for "not landed" is identical: *the frozen sentence at `HMENU3_PROOF_2026-08-08.md` L216–219 is unchanged.* That check cannot distinguish "not landed" from "landed by dated append" — this note's own convention (line 29: out-of-range 2026-08-12 appends "correct three statements homed here" while the base body stays byte-frozen; ANNEX A/B/C inside HMENU3_PROOF itself use the identical pattern, quoting the frozen sentence "As frozen" and giving a "Read as" correction beside it, never touching L216–219) is that a correction is a **dated append below the frozen body**, never an in-place edit. By construction the pinned original sentence never disappears whether or not the correction landed. Absence of change at L216–219 is therefore not evidence either way; the three sites over-read a structural non-signal as a negative result.

**What actually landed.** `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md` §"ANNEX A (dated append, 2026-08-08, post-acceptance…)" (commit **19c02857**, "HMENU3 ANNEX A applied (dated append per freeze convention): HM3.C's (A0) quantifier corrected to the disc!=0 form at two sites…") applies exactly the correction all three superseded sites call "owed": THEOREM HM3.C's (A0) clause (L216–219, quoted "As frozen") and §S5.2's (A0) proof (L431–437, quoted "As frozen") are each given a "Read as" corrected reading — "so Ore certifies every lift **with disc ≠ 0**" and "assigns the SAME σ to every O-lift **with disc ≠ 0**", the "(not only disc ≠ 0 ones)" parenthetical withdrawn. ANNEX A records the counter-instance forcing the correction (TRP-RAM3(1) at p = 3, disc = 0, no σ at all) and that nothing else moves: HM3.A, HM3.B, HM3.C's (A2) exact complement, HM3.D, both W-12-side boxes, and the sealed battery are all UNCHANGED, and "W-12.D's n = 3 firing stands on the corrected form". ANNEX A was subsequently refined, not reopened, by **ANNEX B** (fixed-λ refinement: 7+7 shape schemas → 11+11 formal fixed-σ (A1) families, 53 total) and **ANNEX C** (states ANNEX A's logical effect precisely: strictly narrower quantifier, not merely a null-set removal), both dated appends of 2026-08-12, commit **d665620b** ("SOL cert E7 FOLDED: HMENU3 — ANNEX B fixed-λ refinement … + ANNEX C strictness statement"), landed via the sol certification C8/E7 adjudication (gpt-5.6-sol high; C8 raised the (A1)-indexing gap as CHALLENGE, E7 adjudicated findings 1 and 3 REAL and repaired them by ANNEX B and ANNEX C respectively). Verification (byte-exact pin re-verification against both commits, md5 match, tripwire green) is the maintenance agent's finding, logged at the next `docs/PROJECT_STATE.md` append; cite commit 19c02857 as the landing, d665620b as the refinement.

**Corrected reading at each superseded site (mathematical content unmoved; append/consumption-protocol status only):**

- **§3.2 crossref row:** the append/consumption-protocol cell reads **LANDED 2026-08-08 (ANNEX A, commit 19c02857), refined 2026-08-12 (ANNEX B/C, commit d665620b) — not owed.** The mathematical-status cell already said "SURVIVES on the corrected disc ≠ 0 form; HM3.C's conclusion, HM3.A/B, HM3.D and all counts unchanged" and needs no change: ANNEX A supplies exactly that reading, ANNEX B/C only sharpen HM3.B's schemas and state ANNEX A's effect precisely.
- **`.18` CONDITIONALITY:** the n = 3 row of the FIRING CHECK table is **SUPPLIED at the ANNEX-A-corrected, sol-certified (ANNEX B/C) form** — HMENU3's (A1) supply to W-12 is "every disc ≠ 0 lift of every core-menu member has σ = the leaf table's entry" (ANNEX A's own corrected-clause statement), landed, not owed. No residual obligation remains on the HMENU3 side; the row's characterization of the n = 3 firing as surviving is unaffected.
- **OPEN-CALL 2:** **CLOSED.** The named decision ("land the drafted annex, or record the obligation") is resolved by the landing itself: the annex was applied (two sites, orchestrator-applied per the note's own `[r5]`-drafted text), and hardened further by ANNEX B/C. No open decision remains at this call.

Nothing mathematical moves by this amendment: it corrects only the append/consumption-protocol predicate (per the header's own SCOPE SPLIT, rule 7) that the three superseded sites had wrong, using a detection method — grepping the pinned original sentence — that structurally cannot witness an appended correction. The compiled text's statement content, counts, and CANONICAL STATEMENTs above are untouched.





---

## 4. XREF verification ledger (consolidated, deduplicated)

Every designation below was checked with fixed-string grep (`grep -cF '<designation>' <file>`)
or file-existence, per rule 2. **55 raw XREF/artifact citations across the two shards
(36 from shard 1, 19 from shard 2 — matching each shard's own closing line) reduce to
37 distinct targets; 18 of shard 2's 19 rows are exact-string duplicates of a shard-1 row
(marked `**DEDUP**`), and exactly one row is new** (`GENIND_PROOF_2026-08-08.md:GENIND-1`,
consumed only by LEMMA W12-HT, homed in shard 2). This is an unusually high dedup rate
compared to GRTW2 (4 of 25) or LIFTCORNER — because, unlike those notes, **shard 2's own
§3.1 table re-tabulates the whole note's supplier list rather than only its own
HOME-consumed subset**: shard 2's CONDITIONALITY STACK (`.63`) is a full as-of ledger of
every supplier the WHOLE note rests on (W-11, W-10, J-D0, the six weld notes, DULEMMA,
the three Lean anchors), most of which are also independently cited inside shard 1's own
range.

`[TABLE — compiler ledger]`

| # | Target : designation | Count | Role | Source shard(s) | Dedup |
|---:|---|---:|---|---|---|
| 1 | `W11_PROOF_2026-08-08.md:THEOREM W-11` | 3 | The n = 2 menu, drainage law, and the reduction's unconditional firing; consumed at pin, plus the sealed predictor as reference instrument | s1 + s2 | **DEDUP** |
| 2 | `W11_PROOF_2026-08-08.md:S2.3` | 8 | The refinement measure-isomorphism (W12-L0's induction step), generalized without the quadratic restriction by LEMMA W12-HT step 2 | s1 + s2 | **DEDUP** |
| 3 | `W11_PROOF_2026-08-08.md:S4.3` | 10 | The stated general-n program (P1)/(P2)/(P3) | s1 | — |
| 4 | `W11_PROOF_2026-08-08.md:SPLIT-TAIL` | 21 | The proved DBL-side tail certification; the (A2)-routed boundary family | s1 | — |
| 5 | `W11_PROOF_2026-08-08.md:W11-BOX-3` | 1 | Reimplementation fence inherited | s1 | — |
| 6 | `W11_PROOF_2026-08-08.md:W11-BOX-4` | 2 | Oracle-coverage fence inherited | s1 | — |
| 7 | `W10_PROOF_2026-08-08.md:THEOREM W-10` | 2 | The digit-calculus template; the (2,1,1) cross-check, via the W-11 instrument's sealed W10 tie | s1 + s2 | **DEDUP** |
| 8 | `W10_PROOF_2026-08-08.md:W10-BOX-1` | 1 | The general-order W-10 box, declared untouched | s1 | — |
| 9 | `W10_PROOF_2026-08-08.md:W10-BOX-3` | 1 | Reimplementation fence inherited | s1 | — |
| 10 | `W10_PROOF_2026-08-08.md:W10-BOX-4` | 1 | Oracle-coverage fence inherited | s1 | — |
| 11 | `JD0_PROOF_2026-08-08.md:LEMMA J-D0` | 4 | Count-gauge-blindness FRAME (shape-only well-posedness); P-9's falsifier routes through its mechanism | s1 + s2 | **DEDUP** |
| 12 | `GRTJC_PROOF_2026-08-08.md:JC-PSIKER` | 19 | `(H-a)` composite-stage warrant | s1 | — |
| 13 | `GRTJC_PROOF_2026-08-08.md:JC-LOAD` | 31 | `(H-a)` composite-stage warrant | s1 | — |
| 14 | `GRTJB_PROOF_2026-08-08.md:JB-VTX` | 77 | `(H-b)` membership face; the engine tie in BOX-5 | s1 | — |
| 15 | `GRTJB_PROOF_2026-08-08.md:JB-DEV` | 63 | `(H-b)` membership face | s1 | — |
| 16 | `GRTW2_PROOF_2026-08-08.md:W2-OPEN-2` | 60 | The surviving open weld surface in §S5 | s1 | — |
| 17 | `GRTW2_PROOF_2026-08-08.md:OPEN2ATTACK` | 5 | Its narrowing verdict; W2-OPEN-2a's narrowing status in the conditionality stack | s1 + s2 | **DEDUP** |
| 18 | `GRTW2_PROOF_2026-08-08.md:Σ-LAW` | 14 | The residue `(H-c)` and §S5 are conditional on; the residue the weld surface is narrowed to | s1 + s2 | **DEDUP** |
| 19 | `WELDMASTER_2026-08-08.md:WELD-M-PKG` | 5 | The WELDMASTER member of the six-note weld list | s1 | — |
| 20 | `DULEMMA_PROOF_2026-08-08.md:DULEMMA` | 1 | Explicitly NOT consumed by any count law | s1 + s2 | **DEDUP** |
| 21 | `HEX3_PROOF_2026-08-08.md:THEOREM HEX3.A` | 11 | The exact conservative law (rejected-parse price; BOX-3 discharge); the BOX-3 annex's exact conservative law | s1 + s2 | **DEDUP** |
| 22 | `HEX3_PROOF_2026-08-08.md:HEX3-BOX-1` | 11 | The still-open tail-σ-certification lemma | s1 + s2 | **DEDUP** |
| 23 | `HEX3_PROOF_2026-08-08.md:COROLLARY HEX3.C` | 8 | The characteristic-independence corollary that explains P-6's surviving content | s1 + s2 | **DEDUP** |
| 24 | `HMENU3_PROOF_2026-08-08.md:THEOREM HM3.C` | 10 | The n = 3 σ-labeling supplier (with its inherited phrasing defect); ANNEX 2's (A0)+(A2) supplier | s1 + s2 | **DEDUP** |
| 25 | `HMENU3_PROOF_2026-08-08.md:COROLLARY HM3.D` | 11 | The n = 3 firing of W-12.D; the five cubic `R_τ(q)` with `Σ = 1` | s1 + s2 | **DEDUP** |
| 26 | `GENH4_PROOF_2026-08-08.md:THEOREM GENH4.C` | 9 | The n = 4 σ-labeling supplier; CLEAN row of the m2 sweep | s1 + s2 | **DEDUP** |
| 27 | `GENHN_PROOF_2026-08-08.md:THEOREM GENHN.C` | 11 | The n = 5 σ-labeling supplier; CLEAN row of the m2 sweep | s1 + s2 | **DEDUP** |
| 28 | `GENHN_PROOF_2026-08-08.md:[GENHN-HE(μ ≥ 3)]` | 7 | The openly-unsupplied n ≥ 6 case | s1 | — |
| 29 | `GENIND_PROOF_2026-08-08.md:GENIND-1` | 15 | Fracture permanence, consumed by LEMMA W12-HT steps 3–5 at PROVED grade | s2 only | **NEW** |
| 30 | `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md:the faithfulness handoff (J-D1)` | 1 | The blueprint's W-12 row, quoted verbatim; also cited by P-9's diagnosis order | s1 + s2 | **DEDUP** |
| 31 | `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md:(J-D1) THE FAITHFULNESS HANDOFF` | 1 | The §S2.4 statement quoted verbatim in §S5 | s1 | — |
| 32 | `docs/in-progress/WELD_SYNTHESIS_2026-08-05.md:(ii) J-D composition plan: BLUEPRINT ROUTE` | 1 | The cited `§4(ii)` provenance | s1 | — |
| 33 | `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md:erratum` | 54 | The ledger-side erratum convention for the `[r1]` display fix | s1 | — |
| 34 | `lean/LeanUrat/OM/RealInstanceV2.lean:htameFE` | 9 | The capstone hypothesis BOX-8 declares untouched | s1 | — |
| 35 | `lean/LeanUrat/OM/RealInstanceV2.lean:montes_unconditional_exhaustive` | 5 | Named Lean tie target | s1 + s2 | **DEDUP** |
| 36 | `lean/LeanUrat/OM/RealInstanceV2.lean:hExhaust` | 5 | Named Lean tie target | s1 + s2 | **DEDUP** |
| 37 | `lean/LeanUrat/OM/OMCountV2.lean:omMenu_order0` | 1 | Named Lean tie target | s1 + s2 | **DEDUP** |

**Files verified to exist (path checks, not designations; from shard 2's own list, all
re-confirmed present at merge time):** `verification/openmath/w12_checks.py`,
`w12_checks_output.txt`, `w12_checks_results.json`, `w12_history_law_check.py`;
`runs/residues/R3_w12_output.log`, `runs/cert/A1_w12_output.log`,
`runs/cert4/P1_w12_history_output.log`; `lean/notes/openmath/W12_passPE6_report.md`,
`W12_passPE7_report.md`, `HMENU3_annex_draft_r5.md`. Shard 1 additionally verifies
`GRTW2_passPE1_report.md`–`PE4_report.md`-style artifacts only by reference inside its own
`.03`/`.09` teeth fields, not as a separate designation row.

**Commit-pin verification (rule 23), consolidated and re-run fresh at merge time.** Every
distinct 7–10 character hex token appearing in either shard's CANONICAL STATEMENT or
CONDITIONALITY text was extracted (52 candidate tokens) and checked with
`git cat-file -t`:

```
$ git cat-file -t <token>   # run once per distinct token, 52 tokens total
```

**46 resolve to `commit` (all 46 are genuine commits, re-confirmed fresh); 6 are NOT git
objects at all** (`03811b69`, `42a7655e`, `500aae15`, `a9c34244`, `cae45db2`,
`d3a5e13d`) — and every one of these six is, on inspection, an **md5 file-content hash**
quoted alongside the commit hashes in the same prose (the five frozen-import pins of
`.60`'s W12-PIN family, plus the note-body byte-prefix md5 at the PE7 acceptance record,
`.76`) — not an error, a different and correctly-typed pin. **No token that should have
resolved to a commit failed to.**

### Sample re-verification (10 of 37, grep/exists-rerun at merge time against the working
tree — favouring both-shard-cited DEDUP targets, the one NEW row, and the two commit-type
extremes)

`[TABLE — compiler ledger]`

| Target : designation | Recorded | Re-verified | Match |
|---|---|---|---|
| `W11_PROOF_2026-08-08.md:THEOREM W-11` | 3 | 3 | OK |
| `GRTJB_PROOF_2026-08-08.md:JB-VTX` | 77 | 77 | OK |
| `HMENU3_PROOF_2026-08-08.md:THEOREM HM3.C` (DEDUP) | 10 | 10 | OK |
| `HEX3_PROOF_2026-08-08.md:THEOREM HEX3.A` (DEDUP) | 11 | 11 | OK |
| `GENHN_PROOF_2026-08-08.md:[GENHN-HE(μ ≥ 3)]` | 7 | 7 | OK |
| `GENIND_PROOF_2026-08-08.md:GENIND-1` (the one NEW row) | 15 | 15 | OK |
| `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md:erratum` | 54 | 54 | OK |
| `lean/LeanUrat/OM/RealInstanceV2.lean:htameFE` | 9 | 9 | OK |
| `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md:the faithfulness handoff (J-D1)` (DEDUP) | 1 | 1 | OK |
| `verification/openmath/w12_history_law_check.py` (file-existence check) | PRESENT | PRESENT | OK |

**10/10 sampled targets match exactly — no drift found.** Blob hash of the source note
re-verified identical to the header's pin (§1): no STOP condition triggered.

### Sample statement-quote re-verification (5 of 88, checked verbatim against the source
note by line number)

`[TABLE — compiler ledger]`

| Statement | Quoted fragment | Source lines | Match |
|---|---|---|---|
| `.01` (title headline) | "# W12 — THE GENERAL-n ASSEMBLY (the J-D block's terminal rung): the order-1 shape-generic count law PROVED at ALL degrees (THEOREM W-12.A) …" | 1 | OK, byte-exact |
| `.09` (THEOREM W-12.A base display) | "**(i) [THEOREM W-12.A — the order-1 shape-generic count law] PROVED at all degrees n, all prime powers q, both characteristics, wild strata included.**" | 197 (of 197–230) | OK, byte-exact |
| `.31` (LEMMA W12-S3.2) | "**LEMMA W12-S3.2.** Every TRP member with b₁ = b₀ = 0 over O/π^N (after recentering; b₂ ∈ πO/π^N free) is σ-undecided: U₃^TRP(q, N) ≥ q·q^{N−1} = q^N." | 839 (of 837–871) | OK, byte-exact |
| `.76` (the PE7 acceptance record) | "Provenance: passPE7 (report `W12_passPE7_report.md`, verdict commit fa3acb2: **CLEAN, 0C + 0G + 1 MINOR — the 2-clean counter COMPLETES 1/2 → 2/2; W-12 IS ACCEPTED, the note FROZEN, dated appends only**)." | 1956 (of 1952–1995) | OK, byte-exact |
| `.79` (κ(T) correction, boxed display) | "\[ \kappa(T):= \prod_{d,m} \frac{r_{d,m}!}{\prod_D r_{d,m,D}!}. \]" | 2032–2091 (LaTeX span; source renders the display across several physical lines, reflowed to one line — the same reflow convention both shards' own quotes already use) | OK, content-exact |

**All 5 sampled quotes are byte-identical to the source note at the cited lines; no
drift introduced by the renumbering pass.** The sample deliberately spans both shards'
HOME ranges, the note's founding theorem display, a boxed LaTeX correction, and the
acceptance record itself.


---

## 5. Local supply/consumption ledger

W12's own protocol (header predicate B): the note RECEIVES corrections and annexes from
its suppliers and OWES corrections outward, but **does not itself edit any accepted
supplier's frozen text** — every landing described below happens either as a verbatim
annex pasted into W12's own body (received) or as a correction drafted for, and applied
at, the SUPPLIER's own note (owed outward). The table below merges both shards'
independent §3.2-style reverse-consumer tables (shard 1: 7 rows; shard 2: 7 rows) into
one consumer-direction ledger.

**A note on how this table reads the AMENDMENT (see §1 resolution rule 7, and the
AMENDMENT's own tail unit in §3).** Both shards' ORIGINAL tables — compiled before the
2026-08-14 amendment existed — report the HMENU3 quantifier correction as "OWED AND NOT
LANDED" / "NOT LANDED", using the same detection method the amendment itself diagnoses as
structurally blind (grepping the frozen original sentence at
`HMENU3_PROOF_2026-08-08.md` L216–219, which never changes whether or not a correction
landed by dated append). **This table is being freshly assembled by this merge run, not
reproduced from either shard's original text** — it is exactly the kind of "freshly-built
consolidated summary" the amendment's own closing paragraph says should read the
corrected way, so the HMENU3 row below reports the AMENDMENT's finding (LANDED, refined,
not owed) rather than either shard's stale original wording. This is a deliberate,
explicit choice, not a silent one: the original per-shard wording is preserved
byte-unchanged inside `.18`'s CONDITIONALITY field and inside OPEN-CALL 2 (§8) — only
THIS freshly-assembled table, and §8's OPEN-CALL status line, are updated.

`[TABLE — compiler ledger]`

| Consumer / supplier | Verified designation | Direction and supply | Mathematical status | Append/consumption-protocol status |
|---|---|---|---|---|
| **HMENU3** | `THEOREM HM3.C` (10), `COROLLARY HM3.D` (11) | **Both ways.** W12 consumes HM3.C as the n = 3 σ-labeling supplier and HM3.D via the verbatim BOX-2 ANNEX 2 (`.71`); W12 owed HMENU3 a quantifier-phrasing correction | The n = 3 firing SURVIVES on the corrected disc ≠ 0 form; HM3.C's conclusion, HM3.A/B, HM3.D and all counts unchanged (both shards agree) | **LANDED 2026-08-08 (HMENU3's own ANNEX A, commit `19c02857`), refined 2026-08-12 (ANNEX B/C, commit `d665620b`) — not owed.** *(Both shards' own tables originally read "OWED AND NOT LANDED" / "NOT LANDED" — STALE per the AMENDMENT; see above.)* |
| **HEX3** | `THEOREM HEX3.A` (11) | HEX3 **supplies** the verbatim BOX-3 ANNEX (`.70`); a second, smaller, phrasing correction (L80–81's loose "every lift" wording) was separately named as owed by both shards | (hExhaust-3) discharged at composition grade, convention-free; the L80–81 phrasing issue leaves `U₃^σ ≤ U₃^conv` **unaffected** — "no number and no box moves" | BOX-3 ANNEX: **landed**, verbatim, in shard 2's range. **The L80–81 phrasing correction is ALSO already landed** — **found by this merge's own fresh check of HEX3's current text** (`.72`/`.73` name it "owed" and "not drafted," but `lean/notes/openmath/HEX3_PROOF_2026-08-08.md` lines 80–95 show it fixed IN-PLACE at HEX3's own `[r4]` round: "Ore applies to every disc ≠ 0 lift — W-12 S2.3, post-[r4] form", bracket-documented, then frozen by HEX3's own 2026-08-09 ACCEPTANCE). *(Both shards' own tables read "owed"/"not drafted" — STALE, independently of the AMENDMENT, which does not mention HEX3 at all.)* See OPEN-CALL (merged) below. |
| GENH4 / GENHN | `THEOREM GENH4.C` (9), `THEOREM GENHN.C` (11) | W12 consumes as (A1)-clause σ-labeling suppliers at n = 4, 5 | SUPPLIED — both statements already read "EVERY lift **with disc ≠ 0**"; CLEAN row of the `[r5]` m2 sweep, re-confirmed by PE6/PE7 | No append owed either way |
| GENHN | `[GENHN-HE(μ ≥ 3)]` (7) | Named non-supplier at n ≥ 6 | NOT supplied, openly — the corpus's own existing open box | Nothing owed |
| GENIND | `GENIND-1` (15) | W12 **consumes** — fracture permanence only, at its stated PROVED grade | Consumed by LEMMA W12-HT steps 3–5; "no order-≥ 2 leaf theorem or open μ ≥ 3 assertion is consumed" | No append owed |
| Six weld notes (GRTJA/JB/JC, GRTW2, LIFTCORNER, WELDMASTER) | `JB-VTX` (77), `JC-PSIKER` (19), `Σ-LAW` (14), `WELD-M-PKG` (5) | W12 consumes only in §S5's composition display and as `[W12-H]`'s named inputs | "NO S2/S3 proof depends on them" — the whole absorption/mathematical supply set lives at order 1, outside the weld corpus | No append landed on any weld note |
| Lean capstone (`OM/RealInstanceV2.lean`, `OM/OMCountV2.lean`) | `montes_unconditional_exhaustive` (5), `hExhaust` (5), `omMenu_order0` (1) | W12 **supplies** transcription targets, not a consumer relationship | Cited as tie TARGETS only; the Phase-B transcription spec (`.62`) is **amended** by LEMMA W12-HT's own consumer sweep to require `(HT-rec)`, not the S1 depth-zero display | "no Lean is changed by this unit" (stated identically in both shards) |

**The protocol column is not an inference.** W12 states its own protocol identically in
both shards ("accepted texts are never edited by this unit" — the same discipline the
GRTW2/HE7/HE3 merges found), records two verbatim annexes received and applied, and
named two further corrections as owed outward — **both of which this merge finds are
already landed**, one per the 2026-08-14 AMENDMENT (HMENU3) and one per this merge's own
independent check of the supplier's current text (HEX3). Neither correction remains
open; both were self-applied by their own supplier notes, not by W12.


---

## 6. TEETH inverse table (unified from both shards; presented as two sub-tables by
shard-of-origin — shard 1 carries the core sealed battery, the arc-internal
counter-instances, and the round-block re-reads; shard 2 carries the acceptance-arc
re-runs, the two received annexes' foreign batteries, PE6/PE7's provenance checks, and
the LEMMA W12-HT machine certificate — with one combined zero-orphan statement closing
both)

### 6.1 Shard 1's core sealed battery and in-range counter-instances (IDs unchanged, offset 0)

`[TABLE — compiler ledger]`

| Battery row / tooth | Guarded unit(s) | Disposition |
|---|---|---|
| W12-PIN (5 md5-pinned frozen imports) | `.46`, `.52` | Bookkeeping check (evidence class NONE per the note's own labelling) |
| W12-LVL0 (five cubic level-0 censuses + sum `q³`) | `.22`, `.09` | Executable regression |
| W12-SHAPE (all seven depth-0 TRP laws, BOTH directions, exact zeros) | `.09`, `.28`, `.29`, `.30` | Executable regression with a completeness clause (unpredicted decided key = violation) |
| W12-QRT (QRT-G2 `(1,1)`/`(2)` laws + the `(1²)` frontier volume, both directions) | `.31`, `.49` | Executable regression |
| W12-L0HIST (every history-resolved key; `Σ_H` vs the sealed W-11 predictor) | `.32`, `.33`, `.44` | Executable regression against a frozen foreign instrument |
| W12-BLOCK (Hensel product identity + fiber bijection per DBL member) | `.21`, `.34` | Executable regression |
| W12-L1X (fresh direct cubic read vs the sealed W-11 classifier, pointwise) | `.34`, `.35`, `.52` | Executable cross-implementation regression |
| W12-DRAIN3 (partition `Σ = q^{3N}`; `DBL-undecided = (q−1)q^{2N−1}`; species count `q^N`; `U₃^TRP` measured) | `.11`, `.36`, `.38`, `.45` | Executable regression; the `U₃^TRP` leg EXPLORATORY under a disclosed convention |
| W12-ORACLE (PARI σ-multiset per decided member; `disc = 0 ⟹ never decided`; 85 witness pairs) | `.27`, `.38`, `.40` | Independent-engine regression (IND); witness-pair leg scoped to 70 of 85 by `[r5]` m3 |
| Tooth W12-T-SHAPE (TRP-RAM3 law corrupted must mismatch on every cubic row) | `.28`, `.29` | Planted mutant |
| Tooth W12-T-DRAIN (DBL drainage term corrupted must mismatch) | `.11`, `.36` | Planted mutant |
| Tooth W12-T-CENSUS4 (`S_{(2)}` with the `/2` dropped must break QRT-G2) | `.24`, `.25`, `.31` | Planted mutant |
| Tooth W12-T-SIGMA (QRT-G2 `(2)` σ mis-keyed must be caught by PARI) | `.27`, `.31` | Planted mutant, IND leg |
| Pre-runner independent brute force (9 cubic + 4 quartic rows) | `.29`, `.30`, `.31` | Independent re-derivation, disclosed pre-seal |
| `[r4]` fresh separability instrument (sympy over `GF(p)[t]` and `ℤ`; p = 2,3,5,7, N = 2,3,4) | `.38`, `.39`, `.40` | Executable regression on a FRESH instrument, covering exactly what the frozen kit structurally cannot |
| `[r1]` counter-instance re-read of `w12_checks_results.json` row `(Zp,2,5)` = 4096 | `.09`, `.15` | Committed-artifact re-read |
| `[r2]` boundary-tail mass re-verified on all 23 cubic rows | `.45` | Committed-artifact re-read |
| `[r3]` HEX3.A transcription tied to all 23 committed `U₃` values, 0 mismatches | `.16` | Cross-note numerical tie |
| The degenerate one-family instance (`R_split = 1 ≠ μ_split`) | `.12`, `.17` | Signed counter-model to the sealed hypothesis set |
| S2.3's equal-characteristic-3 counter-instance (`F = y³ + b₀`, `F′ ≡ 0`) | `.18`, `.27` | Signed non-applicability |
| The runner's never-firing `assert e == 1` (PE1-verified) | `.08` | Negative executable check |

**Both-direction audit (shard-1 range).** Every row guards at least one unit; every
toothed unit appears. Units with **`TEETH: NONE`** — `.01`, `.04`, `.05`, `.19`, `.20`,
`.26`, `.37`, `.43`, `.48` — are headers, reconciliations, proof audits, fences or
composition displays. **Zero battery-row orphans; zero toothed-unit orphans in shard 1's
range.**

### 6.2 Shard 2's acceptance-arc re-runs, foreign batteries, and the LEMMA W12-HT
certificate (renumbered, `.53`–`.88`)

`[TABLE — compiler ledger]`

| Battery row / tooth | Guarded unit(s) | Disposition |
|---|---|---|
| W12-PIN (5 md5-pinned imports, 0/5) | `.54`, `.63`, `.66` | Bookkeeping (NONE) |
| W12-LVL0 (0/138) + W12-SHAPE (0/164), both directions, exact zeros | `.54`, `.60`, `.66` | Executable regression (SAME) with a completeness clause |
| W12-QRT (0/27), incl. the wild `p = 2` (2,2) stratum | `.54`, `.60`, `.66` | Executable regression (SAME) |
| W12-L0HIST (0/306), incl. `Σ_H` vs the sealed W-11 predictor | `.54`, `.60`, `.66` | Executable regression against a frozen foreign instrument |
| W12-BLOCK (0/1,594,670) + W12-L1X (0/1,594,090) | `.55`, `.66` | Executable cross-implementation regression, pointwise |
| W12-DRAIN3 (0/1,183): partition, DBL term, letter-uniformity, species | `.55`, `.67` | Executable regression (SAME); the `U₃^TRP` leg EXPLORATORY |
| W12-ORACLE (0 bad / 41,923 checks, PARI) | `.56`, `.68` | Independent-engine regression (IND); witness leg scoped 70/85 |
| Tooth W12-T-SHAPE = 23 | `.57`, `.68` | Planted mutant, fired at preregistered count |
| Tooth W12-T-DRAIN = 23 | `.57`, `.68` | Planted mutant, fired |
| Tooth W12-T-CENSUS4 = 8 | `.57`, `.68` | Planted mutant, fired |
| Tooth W12-T-SIGMA = 1,273 | `.57`, `.68` | Planted mutant, fired on the IND leg |
| Pre-seal smoke (5,884 checks, all four teeth firing) + the `(Fqt,2,6)` cost probe | `.59` | Disclosed development record |
| Pre-runner independent brute force (9 cubic + 4 quartic rows) | `.59` | Decorrelated re-derivation before the runner existed |
| Five arc GREEN re-runs at seal-intact md5 (PE1/PE3/PE4/PE5 + the verdict run), incl. PE5's first equal-characteristic `p ≥ 5` rows and a `(7,2)` cross-characteristic pair | `.69`, `.74` | Fresh-route re-runs; "arc facts" |
| The committed `U₃` sequence used against the note's own struck inference (normalized 0.5000 → 0.6914; step ratios 4.50/4.22/4.47/4.16 > 4) | `.67` | Committed-artifact re-read used as a refutation |
| HEX3's sealed battery (158,512 checks / 0 violations, 46 rows) | `.70` | Foreign-note battery, received with the annex |
| HMENU3's sealed battery (183,387 checks / 0 violations, 41 rows, teeth 21/15/10/4, PARI on 9,952 deep members) | `.71` | Foreign-note battery, received with the annex |
| The `[r5]` m2 grep sweep, and PE6's independent re-run finding three missed hits | `.73`, `.75` | Negative check, plus a check of the check |
| PE7's by-sentence re-anchor across three GENHN HEADs | `.76` | Provenance verification |
| Byte-prefix md5 verification after appending (`42a7655e`, 124,423 bytes) | `.76` | Document-integrity check |
| N1/P1 certificate `w12_history_law_check.py`: 1,196 per-key comparisons, 0 mismatches; teeth DROP-HISTORY-CENSUS 302 / BASE-q-LETTERS 22 / DROP-KAPPA0 370 / DROP-L 1,136; 300 translation-rank + 322 coprime-multiplication-rank tests | `.83`, `.84`, `.85`, `.86`, `.87`, `.88` | Independent machine certificate, GREEN **before** the proof was composed |
| Orchestrator re-derivations at each sol append (A1's four findings; P1's five steps) | `.82`, `.88` | Decorrelated hand verification before transcription |

**Both-direction audit (shard-2 range).** Every row guards at least one unit; every
toothed unit appears. Units with **`TEETH: NONE`** — `.62`, `.64` — are consumer/ledger
inventories. **Zero orphans in shard 2's range.**

### 6.3 Combined zero-orphan statement

**Both-direction audit, unified across all 88 units.** Every battery row in either
sub-table guards at least one unit in the merged inventory; every unit whose `TEETH`
field names a battery row appears in some row above. Combining both shards' `TEETH:
NONE` lists — `.01`, `.04`, `.05`, `.19`, `.20`, `.26`, `.37`, `.43`, `.48` (shard 1) and
`.62`, `.64` (shard 2, renumbered) — gives **eleven** declaration/fence/ledger/status
units outside the orphan count. **Zero battery-row orphans; zero toothed-unit orphans
across all 88 units.** The one item shard 1 flagged as "out-of-range" at compile time
(the LEMMA W12-HT certificate, "homed in shard 2, which guards the corrected form of
`.09`") is now **in-range** in this merged table (§6.2's N1/P1 certificate row) —
verified: it guards `.83`–`.88`, and its corrected-form target `.09` is cross-listed at
§6.1's W12-LVL0/W12-SHAPE rows.


---

## 7. SERIES, cross-shard supersession edges, and boundary resolution

### 7.1 The dated-arc SERIES: W12-GRADE-ARC (6 members, TERMINAL — W-12 **IS** accepted, 2/2)

**Honesty note, unlike the GRTW2 precedent:** neither shard self-labels this construct
as a SERIES or numbers its own members "N of M" — GRTW2's shards did that work
themselves and this merge only assembled their labels. **Here the SERIES is assembled
for the first time by this merge run** (rule 28), from six status-bearing units whose
own text is chronologically self-evident (composition → repair rounds → PE6 → PE7
acceptance) but never cross-numbered by either shard. Flagged as a compiler construct,
not a source-stated one.

`[TABLE — compiler ledger, assembled from six units' own status language]`

| Link | Unit | Stage | Counter | Content (quoted from the unit) |
|---:|---|---|---|---|
| 1 (origin) | `.01` | composition-time header | **0/2** | "**Attempt grade 0/2**"; the struck arc display is later marked "**[r5, PE5 m2: … SUPERSEDED; the CURRENT arc is the [r5] ARC at the end of this note]**" |
| 2 | `.14` | GRADE SUMMARY | **0/2** | "**GRADE SUMMARY: … Attempt 0/2.**" |
| 3 | `.69` | §S10 "Consequence for the grade box" | **stays 0/2** | "~~Attempt 0/2; the hostile arc has not begun.~~ **[r1] ARC (superseded — the CURRENT arc is the … [r5] ARC at the end of this note)**" |
| 4 | `.74` | the three ARC displays (`[r3]`/`[r4]`/`[r5]`, `[r5]` CURRENT) | **stays 0/2** | "**[r5] ARC (CURRENT, 2026-08-08): … PE5 NOT CLEAN 0C+1G+3m … r5 THIS REPAIR (all four findings, note-only)**" |
| 5 | `.75` | PE6 record (2026-08-09) | **0/2 → 1/2** | "passPE6 hostile verification … CLEAN — 0 CRITICAL + 0 GAP + 1 MINOR … the 2-clean counter started 0/2 → 1/2" |
| 6 (**TERMINAL**) | `.76` | PE7 re-anchor (2026-08-09), THE ACCEPTANCE | **1/2 → 2/2, ACCEPTED** | "passPE7 … **CLEAN, 0C + 0G + 1 MINOR — the 2-clean counter COMPLETES 1/2 → 2/2; W-12 IS ACCEPTED, the note FROZEN, dated appends only**" |

**W-12 reaches 2/2 accepted.** Links 1–4's "0/2"/"attempt grade" language is
`STALE-SELF-DESCRIPTION` (rule 26) at HEAD — the acceptance landed after they were
written, and the frozen text is not edited to say so; this SERIES table is where the
current status actually lives. **Uniqueness verified:** an exhaustive scan of every unit
in the merged inventory for language matching "counter 0/2"/"ACCEPTED"/"the note FROZEN"
confirms exactly these six links and no seventh, duplicate, or seventh-shard candidate.
**No duplicate link, no skipped link, TERMINAL uncontested.**

### 7.2 Cross-shard supersession edges (consolidated, with SUPERSESSION KIND)

Six mechanisms land shard-2-homed corrections onto shard-1-homed units, all physically
drafted in shard 2's range (rule 7: HOME follows an edit's *destination*). The table
below uses the vocabulary the merged inventory already exercises: **replacement |
license | wording-rider | counter re-reading** — the other five SUPERSESSION KINDs
(withdrawal, scope-pin, as-of scoping, provenance-rider, inventory completion,
partial-withdrawal) do not occur at a cross-shard edge in this note; that gap is noted,
not forced.

`[TABLE — compiler ledger]`

| From | To | Kind | Content |
|---|---|---|---|
| `.79` (κ(T) correction) | `.09` | replacement | W-12.A's level-0 prefactor `C₀(q)` corrected to `κ(T)C₀(q)`; "no committed number moves" (κ = 1 on every sealed/consumed instance) |
| `.78` (dated obstruction) → `.79`–`.87` (LEMMA W12-HT, TERMINAL `.87`'s discharge conclusion) | `.09`, `.14`, `.62` | license | The obstruction ("does not prove its stated coverage of the full order-1 layer") is discharged: W-12.A's controlling formula becomes `(HT-global)`; the depth-zero S1 display is recovered as its specialization; `.62`'s Phase-B transcription spec is amended to require `(HT-rec)` |
| `.80` ((A1) rationality correction) | `.12`, `.42`, `.44` | replacement | (A1)'s density-law clause replaced: `c_F(q)` is now the evaluation at `X = q` of a fixed rational function `c_F(X) ∈ ℚ(X)`, independent of `q` and characteristic; Step 1 and the n = 2 instance's admissibility re-derived under the corrected clause |
| `.81` (BOX-1 dependency-range correction) | `.49` | replacement | W12-BOX-1's cited range `(H-a)–(H-d)` corrected to `(H-a)–(H-e)`, restoring S4.2's own five-input list; "changes no mathematical conclusion" |
| `.70` (BOX-3 ANNEX, from HEX3) | `.50`, `.45` | license | (hExhaust-3) discharged at composition grade, convention-free; one of the two n = 3 legs of `.45`'s conditionality vocabulary |
| `.71` (BOX-2 ANNEX 2, from HMENU3) | `.50`, `.45` | license | (hMenu-3) discharged at composition grade; the second n = 3 leg of `.45` |
| `.72` (`[r5]` NOTICE on ANNEX 2's supplier) | `.18` | wording-rider | "The correction is a quantifier phrase, not a result" — justifies the in-place `[r5]` rewording already landed inside `.18`'s own text; the annex `.71` itself "is UNTOUCHED and stays verbatim as applied" |
| AMENDMENT (dated append, 2026-08-14) | `.18` (reading only), §5 ledger, OPEN-CALL (merged, ex-s1 #2) | counter re-reading | Re-reads the append/consumption-PROTOCOL status of three sites from "not landed"/"owed" to "LANDED … not owed," **without re-issuing any display and without touching the mathematical content** — exactly rule 18's "a gloss is re-read, no display is re-issued" |

**Total: eight rows**, covering six distinct correction mechanisms (one, the LEMMA
W12-HT discharge, produces two target rows since the obstruction and the discharge are
tracked as a CHAIN with a shared TERMINAL). **All eight resolve to a unit that exists in
the merged inventory; zero dangling targets.** Two of the six mechanisms (the history-
transfer discharge, the (A1) correction) change a theorem's controlling formula or
hypothesis interface; none is claimed to change a *conclusion* — every correction's own
text states "no committed number moves" / "changes no mathematical conclusion" /
"nothing mathematical moves," and this merge does not contest any of those self-reports.

**CHAIN, marked TERMINAL (rule 25): the obstruction → discharge edge.** `.78`'s dated
obstruction ("An order-1 refinement history may contain earlier repeated residuals even
though its terminal residual is separable … no such all-degree lemma is proved at HEAD")
is discharged by LEMMA W12-HT's six-step proof (`.79`–`.86`) and its conclusion (`.87`:
"The dated obstruction is closed. … 'the order-1 layer at all degrees' and 'every W-11
row is an instance' are again justified"). **TERMINAL: `.87`.** **Uniqueness verified:**
an exhaustive scan of every CONDITIONALITY/RESOLUTION TRACE field for `.09`, `.14` and
"the dated obstruction" as a supersession *target* confirms only `.79`–`.87` supersede
it — no third, later correction to the same target exists anywhere in the merged
inventory.

**No `withdrawal`, `scope-pin`, `as-of scoping`, `provenance-rider`, `inventory
completion` or `partial-withdrawal` kind was found among these eight edges** — every
correction here either replaces a display, licenses a discharge, riders a wording, or
counter-reads a protocol-status gloss (the AMENDMENT). This is a genuinely narrower
SUPERSESSION-KIND profile than GRTW2's or LIFTCORNER's merges found, recorded as a
finding rather than assumed absent.

### 7.3 Boundary-unit resolution (merge rule 5/7)

Per rule 7 (HOME follows edit destination, not drafting location), all six correction
mechanisms above are **HOMED in shard 2** (`.70`–`.72`, `.78`–`.87`) even though four of
the six target sets land on shard-1-HOME units. **Verified: none of the six is
duplicated as a second unit inside shard 1's range** — an exhaustive scan of the merged
inventory's 88 unit headers (§3) confirms `.53`–`.88` appear exactly once each, at their
shard-2-derived numbers, and no unit numbered `.01`–`.52` independently re-states any
annex, correction, or discharge as its own content (they are only *cited*, by ID, from
the shard-1-HOME units they target).

**Every unit named in either shard's own §6 BOUNDARY SELF-AUDIT as "physically drafted
elsewhere, HOME-routed" appears exactly once in the merged inventory** — shard 1's own
§6 records no unit drafted in shard 2 but homed in shard 1 (the traffic is entirely
one-directional in this note, matching §1's SHARD-MAP finding that shard 1 never cites
shard 2 by bare `.NN` at all); shard 2's own §6 items 3 and 6 record the opposite
direction explicitly for the two annexes/notice and the five 2026-08-12 appends, each
cross-checked here against the statement inventory (§3) and found present exactly once,
at its shard-2-derived ID.

### 7.4 Range-edge audit

Both shards independently audited the physical line boundary and both report the same
clean break: shard 1's own note — "line 1270 closes W12-BOX-8; line 1271 is blank and
line 1272 opens `## S7. THE SEALED BATTERY`" — and shard 2's own note — "line 1271 is
blank, line 1272 opens `## S7`, and line 2453 is the note's last line." **Both
descriptions name the identical boundary (1271/1272) and agree it falls on a section
break.** The file's own end (source line 2453) is shard 2's own last line, closing the
P1 provenance/orchestrator-verification unit `.88`. **Zero units span the shard
boundary.**


---

## 8. Self-audit and OPEN-CALLs

**6 raw OPEN-CALLs (3 shard 1 + 3 shard 2) carry forward as 6 distinct, two now CLOSED —
one by the AMENDMENT, one by this merge's own fresh check of a supplier note's current
text.** No pair is *self-flagged* as a
duplicate by either shard (checked with a fresh grep — "same call", "self-identified
duplicate", "recorded in both", "same as shard", "identically as shard", "same
question" — none found across either shard), so per the standing charge, **nothing here
is dedup'd**. Two pairs are substantively close and are flagged as such below without
being merged, matching the GRTW2/HE3 precedent for this shape of overlap.

### OPEN-CALL 1 (shard 1) — which text is THEOREM W-12.A's canonical statement in the effective spec

Three texts are in play for the same theorem: (a) the S1 display as repaired by `[r1]`
(`.09`, in range); (b) that display with the level-0 orbit factor `κ(T)` (2026-08-12
correction); (c) `(HT-global)`, the history-resolved law of LEMMA W12-HT, which the
discharge names as "its controlling formula", with (b) as "the depth-zero
specialization". Shard 1 compiled (c) as effective, per the discharge's own words, and
carried (a) as the depth-zero case. **The call is that the discharge's own ledger line
does not declare itself final:** *"Ledger: row 12 → the obstruction is DISCHARGED; a
final transcription-confirmation rides the next queue."* Whether the effective spec
should present W-12.A as `(HT-global)` or hold it at the κ(T)-corrected depth-zero
display pending confirmation is a DAG/status decision above the compiler. **Reading note
(external, not an edit):** `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` row 12 records
W-12 as **CERTIFIED 2026-08-12** — "the obstruction discharged by LEMMA W12-HT (machine
certificate GREEN; transcription confirmed at TC1)" — i.e. the ledger says the
confirmation has since landed. *Substantively close to OPEN-CALL 5 below (shard 2's own
copy of a related ledger-vs-note-text question); neither shard cross-flags the other, so
both are carried separately.*

### OPEN-CALL 2 (shard 1) — the owed HMENU3 quantifier correction — **CLOSED by the
AMENDMENT**

The original call: `.18`'s `[r5]` FIRING CHECK rewording and the `[r5]` NOTICE (`.72`)
record that HMENU3's THEOREM HM3.C carries the same unrestricted "EVERY lift" over-claim
that `[r4]` struck from this note's S2.3, drafted for correction at
`lean/notes/openmath/HMENU3_annex_draft_r5.md` but, at shard-compile time, verified
**not yet applied** at HMENU3's own frozen lines 216–219. **This call is CLOSED.** The
2026-08-14 AMENDMENT (§3, tail unit) establishes that the correction in fact landed at
HMENU3's own ANNEX A (commit `19c02857`), refined by ANNEX B/C (commit `d665620b`) — the
"not applied" reading was an artifact of grepping a frozen sentence that structurally
cannot witness a dated-append correction. **No decision remains** — the original prose
above is preserved byte-unchanged (it is the historical record of what was verified true
at shard-1's own compile time); this line records only that the call itself is now shut.

### OPEN-CALL 3 (shard 1) — `(A0)` retained-but-redundant: keep or retire in the effective interface

Post-`[r4]`/`[r5]`, `(A0)` is "the same statement in its well-posedness phrasing, i.e.
redundant-but-retained: it is not the load-bearing warrant at either bound". W12 keeps
it as a hypothesis of W-12.D. A downstream formalization must choose: transcribe (A0) as
a hypothesis (faithful to the note, but a provable-from-(A1) redundancy in the
interface) or drop it (leaner, but a statement change). Shard 1 compiled it as retained.
**This is a statement-shape decision for the blueprint, flagged rather than taken.**

### OPEN-CALL 4 (shard 2) — the owed HMENU3 quantifier correction, plus a second HEX3
companion — **BOTH halves CLOSED, the second by this merge's own fresh check**

`.72` (the `[r5]` NOTICE) diagnoses the same HMENU3 over-claim as OPEN-CALL 2 above, and
additionally records **a second, weaker obligation with no draft named**: HEX3_PROOF
L80–81 carries the same loose "every lift" phrasing (`.73`, row 3), "a phrasing
correction owed at HEX3's own arc". **The HMENU3 half of this call is CLOSED, by the
same AMENDMENT finding as OPEN-CALL 2** (both calls diagnose the identical HMENU3
defect; the amendment's finding applies to both). **The HEX3 half is ALSO CLOSED — not
by the AMENDMENT (which is scoped exclusively to HMENU3 and says nothing about HEX3 at
all) but by this merge's own independent re-check of HEX3's current text**, run
precisely because template rule 10 requires verifying a cross-note "unlanded" claim
against the supplier's FULL text, not a snapshot: `lean/notes/openmath/
HEX3_PROOF_2026-08-08.md` lines 80–95 show the correction **already landed IN-PLACE**,
at HEX3's own `[r4]` repair round — "Ore applies to every disc ≠ 0 lift — W-12 S2.3,
post-[r4] form", with a `[r4, PE5 m1: …]` bracket that names the exact fix and cites
W12's own finding as its reason ("W-12 r4's m2 sweep … dispositions this site
'conclusion UNAFFECTED'") — then frozen by HEX3's own dated ACCEPTANCE record
(2026-08-09, 2/2: "Everything above this heading … is byte-untouched by this append").
**Both W12 shards' own "owed"/"not drafted" readings for the HEX3 half were stale for
the identical structural reason the AMENDMENT diagnoses for HMENU3** — neither shard
re-checked the supplier's current state before compiling. **No decision remains for
either half.** *Substantively close to OPEN-CALL 2 above (shared HMENU3 half); not
merged, since the two calls are not textually identical, even though both halves are now
resolved.*

### OPEN-CALL 5 (shard 2) — the note's terminal protocol state versus the external ledger

Two closing lines leave protocol steps outstanding at the note's own record: `.82`'s
"Ledger: W-12's row stays OPEN — the three corrections await sol discharge-confirmation,
and the obstruction closes only when the all-degree order-1 history-transfer lemma is
proved", and `.88`'s "Ledger: row 12 → the obstruction is DISCHARGED; a final
transcription-confirmation rides the next queue." Compiled as the note states them.
**Reading note (external, not an edit):** `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md`
row 12 records W-12 as **CERTIFIED 2026-08-12**, i.e. externally both confirmations have
landed. **Decision needed:** whether the effective spec's status field takes the note's
own text or the ledger. Status only; no mathematical statement turns on it.
*Substantively close to OPEN-CALL 1 above (both turn on the same external ledger row);
not merged, since OPEN-CALL 1 is about WHICH DISPLAY is canonical while this call is
about WHICH STATUS LINE is canonical — a display question and a protocol-status
question, not the same call twice.*

### OPEN-CALL 6 (shard 2) — the certificate's grid versus the lemma's claimed range

LEMMA W12-HT is claimed at ALL degrees; its machine certificate covers `n ∈ {3,4}`,
`q ∈ {2,3}`, `N ≤ 6`, and the note is explicit that the certificate "corroborate[s] the
local normalizations and side-local orbit convention; the proof above supplies the
all-degree warrant." That is honest as written. **The call is downstream:** the lemma is
the effective statement of THEOREM W-12.A and it was composed by a model from a
conjectured law, hand-verified by the orchestrator, and machine-corroborated only on
that small grid — a different evidence profile from the note's other proved lemmas,
which carry sealed preregistered batteries. Whether the blueprint should record W12-HT
at the same evidential tier as W12-L0/W12-L1 is a grading decision above the compiler.
**No hostile-arc pass has run against the discharge append itself** (W-12's arc closed
at PE7, before the 2026-08-12 sol appends existed) — this remains true after the merge
and is exactly what the file's own header line ("CODEX CROSS-READ OWED") flags as
inherited, not discharged.

### Recorded source defects (flagged, not silently repaired; 6 raw from the two shards
plus 2 new findings by this merge run = 8 distinct)

1. **`.05`, `.06`:** W12 cites the blueprint as `§S3.1` (count **0**; the file's header
   is `### S3.1 The twelve lemmas`) and GRTJB's `row-12` (count **0**; the file writes
   `row 12`, count **9**). Both referents are unique and verified; the orthography is
   recorded, not corrected. *(shard 1's own finding)*
2. **`.49`:** W12-BOX-1's `(H-a)–(H-d)` contradicted §S4.2's own five-input list;
   corrected out of range and applied at `.81`. *(shard 1's own finding)*
3. **`.02`:** the archived draft's spurious `(q^d−1)`-per-interior-vertex factor is
   recorded as a known-wrong alternative to `.24`'s sweep result. *(shard 1's own
   finding)*
4. **`.75` (PE6 record):** its two GENHN line anchors were stale at its own commit, and
   its third bullet's descriptor ("the second occurrence of the same sentence") was
   wrong; both corrected by sentence at `.76`, with the record left standing. *(shard 2's
   own finding)*
5. **`.73` vs `.75`:** the `[r5]` m2 sweep declares a grep scope its five rows do not
   exhaust (three in-scope hits undispositioned); recorded by PE6 as a completeness
   MINOR, the sweep table stands as written. *(shard 2's own finding)*
6. **`.67`:** §S10 P-6's original closing inference is FALSE for the measured quantity —
   the note's own struck text, replaced by a bracket carrying both reasons. *(shard 2's
   own finding)*
7. **`.62` ↔ `.87` (this merge's own finding, new — a reciprocal stale internal
   cross-reference, neither half caught by either shard's own self-audit):** shard 2's
   `.62` (§S8 CONSUMERS) cites its own amending unit as "`.43`" — a number that was never
   valid under shard 2's own temporary numbering (which ran only 01–36) and does not
   match shard 1's unrelated `.43` either; shard 2's `.87` (LEMMA W12-HT's consumer
   sweep) reciprocally cites the unit it amends as "shard 1's `.10`-adjacent Phase-B
   consumer spec" — but shard 1's own `.10` is CONJECTURE W-12.B, with no Phase-B
   content at all. Both anomalies point at the SAME pair of units under correct content
   analysis (`.62` ↔ `.87`, both shard 2's own), resolved that way in §3 with an inline
   compiler bracket at each site, and booked here as one defect rather than two. Neither
   shard's own self-audit (§6 in each) caught this — both self-audits check
   *boundary-choice* reasoning, not internal cross-reference arithmetic, which is exactly
   the gap a merge run's rule-38 definitive-mapping audit is positioned to close.
8. **The HEX3 L80–81 phrasing correction (this merge's own finding, new — a stale
   cross-note "unlanded" claim, independent of the AMENDMENT):** both shards' own §3.2-
   style ledgers and `.72`/`.73` name this correction "owed at HEX3's own arc" with no
   draft. **This merge's fresh re-check of `HEX3_PROOF_2026-08-08.md` (lines 80–95,
   910–920) finds it already landed** — in-place, at HEX3's own `[r4]` repair round, and
   frozen by HEX3's own 2026-08-09 acceptance record. Structurally the same failure mode
   the AMENDMENT diagnoses for HMENU3 (template rule 10: verify a cross-note "unlanded"
   claim against the supplier's FULL append/repair chain, never a single snapshot) —
   found independently, by this merge's own step-6 verification pass, not inherited from
   either shard or from the AMENDMENT. See OPEN-CALL 4 and §5.

### Fidelity audit

- Every CANONICAL STATEMENT across all 88 units is a verbatim source quotation; **no
  `[ASSEMBLED]` statements in either shard.** No inverse, sign, quantifier, index, level,
  inequality-direction, or implication-direction was altered anywhere, in either the
  original shard compilations or this merge's renumbering pass.
- Every source table is marked `[TABLE]` (`.18`, `.25`, `.28`, `.58`, `.73`); no source
  table was prosified.
- **37 distinct external XREF/artifact targets** (from 55 raw citations: 18 clean DEDUPs
  and one genuinely NEW row — §4) have fixed-string counts ≥ 1 or verified presence, with
  **zero mismatches found** on a 10-target fresh re-verification sample (§4). A 5-quote
  sample was re-checked verbatim against the source note by line number and matched
  content-exact (§4). **46 distinct commit hashes** were independently re-confirmed real
  commits via `git cat-file -t`; the 6 non-commit tokens found by the same sweep are all
  genuine md5 file-content pins, correctly typed, not errors.
- **The ID-renumbering rewrite was performed unit by unit against this compiler's own
  reading of both shards' full text** (not a blind global substitution), tracking the
  header's own disambiguation rule and its ten-line, fourteen-token definitive-mapping
  audit table (§1). An exhaustive regex sweep confirms **zero leftover `sKof2`
  substrings within the merged statement inventory (§3)** — the handful surviving in
  this header (§1) are deliberate quotations of the original shard-local notation — and
  **zero out-of-range renumbered IDs** (every resolved `` `.NN` `` token lies in 1–88,
  confirmed by an explicit scan). **Two anomalous citations were found, neither
  resolvable by the label rule alone, and both resolved by content match and flagged
  in-place rather than silently smoothed** — see defect 7 above and §1's SHARD-MAP
  write-up.
- The SERIES (§7.1) is assembled by this merge from six status-bearing units with no
  duplication and no gap; unlike GRTW2's precedent, **neither shard self-labelled this
  construct**, and that difference is stated explicitly rather than papered over. Its
  TERMINAL (**2/2, ACCEPTED**) is uncontested.
- Absorption status (predicate A), the append/consumption protocol (predicate B — two
  annexes received and landed, and two further corrections named as owed outward, both
  found by this merge to be already landed — one per the AMENDMENT, one per this merge's
  own fresh check), and the inbound-corrections predicate (predicate C, six mechanisms)
  are kept distinct everywhere below, matching both source shards' own discipline.
- **Eight cross-shard supersession edges are consolidated (§7.2)**, covering six
  distinct correction mechanisms; **zero dangling targets**; the profile is narrower
  than GRTW2's or LIFTCORNER's (four SUPERSESSION KINDs used, five unused), recorded as
  a finding.
- **Six raw OPEN-CALLs carry forward as six distinct** — no self-flagged duplicate pair
  exists between the two shards (checked by grep, §8 preamble); two substantively-close
  pairs (OPEN-CALLs 2/4's shared HMENU3 half, and 1/5's shared ledger dependency) are
  flagged as related but not merged. **OPEN-CALL 2 is fully CLOSED by the 2026-08-14
  AMENDMENT, and OPEN-CALL 4 is fully CLOSED on both its halves** — the HMENU3 half by
  the same AMENDMENT, the HEX3 half by this merge's own independent fresh check of
  HEX3's current text (a genuinely new finding, not sourced from either shard or the
  AMENDMENT).
- **The AMENDMENT is preserved verbatim (§3, tail unit) alongside the original compiled
  text it corrects (`.18`'s CONDITIONALITY, unchanged; OPEN-CALL 2 above, unchanged
  except for the closing status line), per the repo's living-artifact convention** — this
  merge's own freshly-assembled §5 ledger and this §8's OPEN-CALL status report the
  AMENDMENT's corrected reading, since a freshly-built consolidated summary is not "the
  original compiled text" the convention protects. This reasoning is stated explicitly at
  every landing site (§1 resolution rule 7, §3's amendment wrapper, §5's ledger preamble,
  and here) rather than picked silently at any one of them.
- **Honest limitation of this merge, stated once:** the boundary-by-boundary reasoning in
  each shard's own §6 (which unit-boundary candidate was chosen and why) is not
  reproduced here in full — only the format-level conclusions (the SERIES construct, the
  cross-shard edge table, the reciprocal-citation-defect finding) survive here. A reader
  who needs the per-boundary reasoning for a specific unit should consult that unit's
  home shard file directly (`spec/EFF-W12-s1of2.md` for `.01`–`.52`,
  `spec/EFF-W12-s2of2.md` for `.53`–`.88`); the shard files are retained for exactly this
  purpose (§1). **Codex cross-read remains owed** (header) — this merge performed the
  fold, the fresh-verification pass, the commit-pin sweep, and the reciprocal-citation
  audit, not the adversarial read.

---

EFF-W12 MERGED: 88 statements / 37 xrefs / 6 open calls
