# EFF-GENIND — CANONICAL EFFECTIVE-SPECIFICATION (MERGED)

**COMPILED-BY: opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51) — mixed
provenance carried forward from all three shards, each independently stamped identically.
CODEX CROSS-READ OWED (post-reset) — none of the three shards, and no fold performed by
this merge run, has been through an adversarial pass; that obligation is inherited whole.
This merge additionally follows the EFF-T2/EFF-HE7 established pattern: contiguous
renumbering with a mechanically-verified SHARD-MAP, blob-hash cross-check as the STOP
condition, dedup-marked consolidation, and a 12-XREF + 6-quote fresh re-verification.**

## 1. Merge header

**Source note:** `lean/notes/openmath/GENIND_PROOF_2026-08-08.md` (3872 lines).

**HEAD blob hash:** `8ef694fefc24c5fb07e4e80c306ff2136c914b61` — cited identically by all
three source shards' headers (each also recording the file's last-touching commit as
`5e33b01f`), and independently confirmed by fresh `git hash-object` against the
working-tree file at merge time (2026-08-14):

```
$ git hash-object lean/notes/openmath/GENIND_PROOF_2026-08-08.md
8ef694fefc24c5fb07e4e80c306ff2136c914b61
```

**No divergence found — this was the merge run's STOP condition and it did not trigger.**

**Compilation context:** `spec/EFF_TEMPLATE_v2.md` at its current HEAD (v2 rules 1–10; v3
rules 11–28).

**Merged from:** `spec/EFF-GENIND-s1of3.md` (HOME lines 1–1348; 74 statements, 59 xrefs,
5 open calls, 7 near-misses), `spec/EFF-GENIND-s2of3.md` (HOME lines 1349–2551;
73 statements, 59 xrefs, 4 open calls, 5 near-misses, 87 commit pins independently
verified), `spec/EFF-GENIND-s3of3.md` (HOME lines 2552–3872; 59 statements, 27 xrefs,
5 open calls, 3 near-misses, 12 commit pins + 13 artifacts independently verified).
**206 statements, 145 raw XREF citations, 14 raw open calls total before merge-time
dedup.** This file supersedes the three shards as the citable unit for all downstream
consumption; any consumer citing `EFF.GENIND.*` from this point on cites the contiguous
IDs below, not the shard-local `EFF.GENIND.sKof3.*` IDs. The three shard files are **not
deleted** — they remain the run-of-record trace of the sharded compilation, and in
particular remain the place where each unit's own §6 BOUNDARY SELF-AUDIT entry (the
prose-genre boundary-choice reasoning, all three shards) and §7 SHARD NOTES (the
per-shard merge-hazard lists this merge's §7 below consolidates) live in full.

### SHARD-MAP (old shard-local ID → new contiguous ID)

Shard 1's offset is **0** (its own numbering, 01–74, is already contiguous from 1).
Shard 2 carries a **+74** offset (01–73 → 75–147). Shard 3 carries a **+147** offset
(01–59 → 148–206). Every `EFF.GENIND.sKof3.NN` occurrence — full form, the abbreviated
backtick form `` `sKof3.NN` `` used in several `TARGETS:` fields, and the bare `` `.NN` ``
shorthand used throughout each shard's own prose — has been mechanically rewritten
throughout the merged statement inventory below (script, not hand-transcription, to
guarantee zero arithmetic slips at 206 units and ~1,150 citation sites), under the
following disambiguation rule:

> **A citation-lead-in — a full-form `EFF.GENIND.sKof3.NN`, an abbreviated `` `sKof3.NN` ``,
> or a prose `shard K` mention immediately (modulo a possessive `'s`) followed by a bare
> `` `.NN` `` — sets the citation context to shard K for bare refs that follow. A bare
> `` `.NN` `` with no such lead-in resolves against the unit's own home shard. Context
> resets to the unit's home shard at every blank-line-delimited field/paragraph boundary
> (fields in this corpus are reliably blank-line-separated) and at every unit boundary.**

**Why the reset is per-field, not per-unit.** An initial mechanical pass reset context only
at unit boundaries, per the literal reading of the EFF-HE7 merge's own stated rule. An
automated audit (every bare ref checked for landing inside `[1, 206]`, plus a
resolved-away-from-home audit) caught **two classes of corruption this produces**: a
CONDITIONALITY paragraph's topical aside naming a foreign shard (e.g. "two further
conjuncts enter at n ≥ 8 (shard 3)") was found to leak into an unrelated, later
same-block home-shard self-reference ("GENIND-BOX-5's close (`.73`)", meant as this
shard's own unit, corrupted to shard 3's numbering). Both confirmed instances — the
GENIND-BOX-5 case and a parallel case at the dated acceptance record's CONDITIONALITY
citing GENIND-BOX-3's own STALE-SELF-DESCRIPTION tag — were mechanically detected (an
out-of-range or type-inconsistent resolved ID), traced to source, and used to derive the
adjacency-based rule stated above, which was then re-run and re-audited clean. **Recorded
as a v3 format finding**, folded into §7 below: a "shard K" mention used as a topical
provenance aside, not a citation lead-in, must not be treated as changing context — this
is a sharper reading than EFF-HE7's own stated rule, forced by GENIND's much heavier use
of parenthetical cross-shard asides inside long, multi-item CONDITIONALITY fields.

**Post-rewrite verification, exhaustive:** **zero leftover `sKof3` substrings** anywhere in
the merged statement inventory (§3) — the few that survive in this header and in §7 are
deliberate quotations of the shard-local notation; **zero out-of-range bare or full-form
IDs** (every resolved ID lies in 1–206, checked against all ~940 bare refs and 206
full-form self-headers); **a documented cross-shard citation defect found by this
audit and NOT silently corrected**: shard 3's OPEN-CALL 1 states "Raised identically at
shard 2 OPEN-CALL 2", but shard 2's own OPEN-CALL 2 is the `.73`-predictions issue, not
the consumer-sweep-format issue; the actual identical twin is **shard 1's OPEN-CALL 2**
(same title, same substance, explicit two-way match). Carried at §8 as a recorded source
defect rather than silently repointed, per this repo's honesty discipline.

### Header unification and blob-hash check

All three shards' front matter carries the identical compiled-by/cross-read-owed stamp
(the GENIND shards, unlike HE7's, do not carry a "prose-genre pilot" banner — GENIND's own
template-version banner is `spec/EFF_TEMPLATE_v2.md` v3, cited identically by all three)
and the identical HEAD blob hash and last-touching commit, cross-verified above against
the working tree rather than trusting the shards' mutual citation alone.

### Governing effective-text record (unified from all three shards' independent derivations)

All three shards derive the same rule independently from the same converging facts,
reproduced here once:

**(i) The body is frozen at acceptance** (dated acceptance record, homed at merged `.146`,
lines 2510–2523):

> "**GENIND IS ACCEPTED 2/2; the text is FROZEN — dated appends only.** … PE8
> re-verified the body's byte-freeze (lines 1–2464 md5 14fa6afc == 993935d, the post-PE7
> annex purely additive)."

**(ii) Every repair round r2–r6 was applied IN PLACE and tagged, each naming which EARLIER
record it corrects.** §S13's heading is the template: "appended at r3 — S11 stays frozen at
its seal, S12 corrected in place where its own sentence was the finding." **Consequence:**
inside shards 1–2 a `[rN]` bracket is already-landed base/record text, not a supersession
still to apply; inside shard 2 specifically, a `[rN]` bracket most often corrects an
EARLIER RECORD (the repair records correct each other), not mathematics.

**(iii) The post-PE7 dated corrections and the acceptance record are additive and name
their targets**, and **ANNEX R, the supplier-movement record, ANNEX R — r1, and the two
2026-08-12 dated corrections (all homed in shard 3) are FOUR FURTHER LAYERS below the
acceptance, each superseding parts of the layer before it, none deleting anything**:

| Layer | Lines | Landed | Supersedes |
|---|---|---|---|
| L0 accepted body (+ r2–r6 in-text) | 1–2551 | 2026-08-08/09 | shards 1–2's HOME range |
| L1 ANNEX R (R1–R6 + close) | 2552–3028 | 2026-08-09 | out-of-range: shard 1's `.11,.13,.14,.24,.36,.45,.46,.49,.58`; shard 2's `.78` |
| L2 supplier-movement record | 3032–3094 | 2026-08-09 | discharges shard 2's `.91` owed disclosure; moves shard 1's `.15` conditionality |
| L3 ANNEX R — r1 | 3098–3294 | 2026-08-10 | five named sites inside L1 + adds GENIND-C2 |
| L4 the two 2026-08-12 corrections | 3298–3872 | 2026-08-12 (sol R9, then sol R11) | L3's GENIND-C2 in full (R9), then R9's own C2(i)/(ii)/(iii) in part (R11) |

**EFFECTIVE TEXT = the whole 3872-line file exactly as written (r1–r6 already landed
in-text, r2–r6 as already-landed records), READ AS CORRECTED by every later dated
rider/annex/layer that names an earlier sentence, with NO earlier sentence ever deleted**
— every correction quotes or names its target and leaves it byte-intact above it.

### FREEZE PREDICATES (four independent freezes, never conflated below)

1. **VERDICT-FREEZE (the §S11 seal).** §S11 is frozen at its seal and no repair round may
   edit it; quoted at each of the five repair records. Pin: seal commit `c3212cc` ✓.
2. **BODY TEXT-FREEZE (acceptance).** Lines 1–2464, md5 `14fa6afc` == `993935d` ✓ (`.146`);
   the pre-annex extension (lines 1–2548, md5 `eefcf658`) is ANNEX R's own freeze scope
   (`.148`), re-verified at every later layer (`.199`, shard 3's ANNEX R — r1 head).
3. **INSTRUMENT-FREEZE (artifact seal).** The sealed runner `genind_checks.py` (md5
   `e7ca150b`) plus every committed leg, re-enumerated by md5 at each round's commit — 13
   md5s at r5 (`.134`), 16 md5s + 5 GT-PIN suppliers at r6 (`.142`) — the enumeration GROWS
   as legs land; the frozen SET differs at each round and the note lists it fresh each
   time rather than asserting "unchanged".
4. **REPORT-FREEZE (other authors' artifacts).** Verifier reports are their authors'
   committed artifacts and are never edited by this note, even when it discloses a defect
   in one — quoted at `.132` (the two verifiers' shared typo) and at `.148`/ANNEX R R6.1
   (`.170`, the PE8 acceptance report's false §4.1 rationale). **Distinct from (1)–(3): it
   governs files this note does not own**, exercised here against the very report that
   accepted the note.

### Scope of record — mandatory THREE-predicate split

**A. ABSORPTION / mathematical supply set.** §S9.3's close (`.94`, lines 1603–1608) is the
authoritative one-line inventory:

> "**One line: THEOREM GENIND.A(I,II,IV) + GENIND.C's hypothesis set =
> {W-11, W-12.A/L0/L1, HEX3, HMENU3 @ pins + this note's lemmas}; GENIND.A(III) adds the
> S4.1 ledger-compression honesty; THEOREM GENIND.B adds [GENIND-H] as its displayed
> hypothesis; the FULL uniformity consequence consumes THEOREM W-12.D @ pin. No axiom, no
> weld face inside any count law.**"

(superseded in its trailing grade clause only, "grade = composition 0/2" → 2/2 ACCEPTED, by
`.146`; `.94`.) The supply is: the two-species induction scaffold (`.08`–`.20`), the
simple-stage layer at every n (`.34`–`.61`), the composite-stage criterion "n ≥ 4" DERIVED
EXACTLY, and the composite-stage law CANDIDATE with its obstruction boxed (`.148`–`.206`'s
annex stack repairs the vanishing-rate hypothesis specifically). **No count law at order
≥ 2 is claimed proved anywhere in the note** (`.75`, GENIND-BOX-1's own fence).

**B. APPEND / consumption-protocol scope. NO-APPENDS on any supplier, declared and
repeatedly honoured.** §S0's fence (`.06`): "This note edits no supplier note." §S9.1's
heading (`.81`): "Proposed annex to W12-BOX-1 / the [W12-H] box (**text offered;
W12_PROOF not edited**)." Every repair record's close re-asserts that no sealed or
committed supplier artifact was touched; §S16's Arc states the round's own edit scope
enumeratively — "the files edited this round are exactly one (this note)" (`.141`). **Zero
consumption appends are claimed landed on any supplier note by GENIND, anywhere in its
3872 lines, and none is invented by this compilation.**

**C. INBOUND corrections RECEIVED — the predicate template v2 has no header slot for, and
where the bulk of this note's own dynamism actually lives.** Five channels:
* **Eight in-house hostile passes, PE1–PE8** (`.79` records six; `.146` the final two) —
  0 CRITICAL at every one, GAP count falling monotonically 3→2→2→2→1→1→0→0.
* **A Codex ratification pass** (`.148`, six findings, outcome CHALLENGE — three CONFIRMED
  GAP, three regraded MINOR — discharged by ANNEX R).
* **The annex stack's own scoped hostile pass** (`.199`, 0C+1 GAP+2 MINOR).
* **Two sol certification runs** (R9 `.195`, R11 `.201`–`.206`), each returning a real
  defect in the previous repair.
* **A supplier movement** — GENHN's three errata + an r2 round that refuted and re-proved
  one of its own lemmas, screened clause-by-clause at `.175` and moving conditionality at
  `.176`; plus seven supplier re-pins crossing one repaired CRITICAL (W-12, `.83`).

### Resolution rules applied (merged; each shard's own numbered list restricted to its HOME range — nothing dropped, only consolidated)

1. Lines 1–3872 supply the HOME material, read in the layer order of the table above.
2. `[r1]`–`[r6]` brackets are already-landed text; a bracket inside shard 2's HOME range
   most often corrects an earlier RECORD (§S11 itself is never edited — corrections to its
   numbers live in isolated re-run records elsewhere, e.g. `.120`'s C12).
3. **ANNEX R (shard 3) supersedes or riders material homed in shards 1–2 at named sites
   only** (the six-point list at shard-1 §7's cross-shard-supersessions item 2–7, folded
   into §7 below); it changes no mathematics in shard 2's §S9–§S16 range by its own
   adjudication.
4. **The dated supplier-movement record and the two 2026-08-12 corrections (both shard 3)
   land on shard 1's and shard 2's HOME text by name**, discharging owed disclosures
   (`.91`→`.176`) and re-conditioning the CS-drain rate (`.61`,`.140`→(CS-1Q) at `.201`).
5. **Consumer-sweep bullets are a distinct supersession vehicle in shard 3's L4** (`.201`,
   `.204`, `.206`): imperative instructions ("In X, replace Y by Z") reaching into frozen
   text in shards 1–2 without quoting it. Their status is OPEN-CALL 1 (merged, below).
6. Where a layer riders an out-of-range unit, the target is named with its merged ID and
   the governing text is quoted at the unit here (§7 gives the consolidated edge list).
7. Out-of-range statements are NOT emitted as units merely because they resolve in-range
   text (each shard's own rule 8/rule 7, applied identically).
8. External repo records (report files, `verification/openmath/*`, commit hashes, ledger
   rows) are reading notes only, never edits.

### Quotation and table discipline

Unchanged from all three shards: CANONICAL STATEMENTs are verbatim source quotations or
explicitly marked `[ASSEMBLED]`; truncation is marked `…`. §S16's per-supplier fired-clause
table (the note's only Markdown source table, homed in shard 2, `.140`) is transcribed as a
table and flagged `[TABLE]`. The LaTeX display blocks of shard 3's L4 (all 13 of the note's
`\tag{}` anchors) are reproduced verbatim with their `\[ … \]` delimiters and tags intact.
Compiler-authored ledgers (XREF tables, consumption ledgers, TEETH inverse tables, the
SERIES/CHAIN/edge tables of §7) are marked `[TABLE — compiler ledger]` and are not source
statement units.

---

## 2. NON-IMPORTS (consolidated from all three shards; dedup marked)

`[TABLE — compiler ledger, consolidated from shard 1 §4 (21 rows), shard 2 §4 (20 rows),
shard 3 §4 (15 rows) = 56 raw rows]`

**Dedup count for this section: 1.** An exact-quote comparison of all 56 rows' quoted
fences (not merely their theme labels) found **one** verbatim-identical quotation cited
from two shards' perspectives: "The STAGE-level parse … is NOT claimed by this note … at
general m the stage-level statement is left unclaimed" (ANNEX R R5, physically homed in
shard 3 at `.157`, but carried into shard 1's own NON-IMPORTS table against `.11` since it
bears on GENIND.A(IV)'s converse clause). **Every other row is theme-adjacent at most
across shards — e.g. three different shards each record their own "ledger compression"
fence, but each quotes a different sentence about a different section's compression — and
is kept as a separate row rather than manufactured into a dedup.** This is a materially
lower dedup rate than EFF-HE7's NON-IMPORTS section (2/42) or its XREF table (32/110),
and is itself a finding: GENIND's honesty fences are overwhelmingly local to their own
section, not repeated verbatim across the note.

| Fence | Explicit material NOT imported, NOT proved, NOT claimed, or NOT exercised | Unit(s) |
|---|---|---|
| No order-≥2 count law | "No count law at order ≥ 2 is claimed proved" | `.01`, `.75` |
| GENIND.B is a reduction | "THEOREM GENIND.B is a REDUCTION; its unconditional content at n ≥ 4 is exactly the simple-stage layer + the criterion + the opening-mass laws" | `.75` |
| No supplier edits (mathematics) | "This note edits no supplier note." | `.06` |
| No supplier edits (offered annex) | "text offered; W12_PROOF not edited" | `.81` |
| Carry corpus scope | "consumed ONLY at the composite-stage frontier (S7)"; "No count law of S2–S6 consumes them" | `.05`, `.67`, `.88` |
| Nothing consumed from the scout | "S7's predictions are keyed to its table, not re-measured here"; "nothing consumed from it" | `.03`, `.05`, `.90` |
| Ledger compression (β, shard 1) | "What is NOT written here: the closed-form fiber exponent of every genre at every degree" | `.26` |
| Ledger compression (mixed, shard 1) | "the per-genre certified-window ledgers are mechanical affine computations, compressed here" | `.42` |
| Ledger compression (annex stack, shard 3) | "the per-genre ledgers remain compressed per the S4.3 honesty box, and the multi-block hostile targets it names stay named" | `.159` |
| Per-route ledgers compressed (BOX-2) | "proved as a schema with per-route ledgers compressed" | `.76` |
| GENIND-3's hypothesis | "excludes polygons that ALSO carry a composite block" | `.24`, `.29` |
| d ≥ 2, prime-power uncorroborated | "The battery exercises d = 1 clusters at prime q only … machine-uncorroborated here" | `.23`, `.77` |
| Conditional structure | "the uniformity theorem at n ≥ 4 is a CONDITIONAL STRUCTURE, displayed, not a result" | `.79` |
| Reader-reimplementation seam | "Self-contained reader (fresh same-session code — GENIND-BOX-6's seam)" | `.06`, `.21`, `.80` |
| Oracle scope | "oracle mixed-characteristic only" | `.80` |
| (CS-3)/(H-e) fully open | "open exactly as [W12-H] prices it"; "(CS-3) is its own theorem ((H-e), open)" | `.65`, `.67`, `.72` |
| The read correspondence | "what it does not supply by itself is the step-for-step READ CORRESPONDENCE … that is the exact residue of (CS-1)" | `.67` |
| (OB-b) refuses citation | "a new transcription that must be written and machine-checked, **not cited**" | `.72` |
| Genre F untouched | "(OB-d) genre F … untouched here; QSCOUT22's territory" | `.72` |
| Stage-level converse unclaimed | "The STAGE-level parse … is NOT claimed by this note … at general m the stage-level statement is left unclaimed" | `.11`, `.157` **DEDUP** |
| CS4-F/CS5 laws unpriced | "Non-flagship (classified, laws not preregistered)"; CS5-V4E2 "its law is derivation-only here" | `.51`, `.52` |
| No stage law consumed early | "NOTHING in the scaffold consumes a stage law before its genre is realized" | `.74` |
| No machine instance for stage-steeper | "this note's own machine leg still carries no instance" | `.42` |
| Two-stage-block genres not live | "not live at n ≤ 7: two composite blocks consume ≥ 8 abscissas" | `.42` |
| Same-side f-first unrealized (as of r5) | "the same-side f-first genre itself … remains machine-unrealized corpus-wide" — later closed by PE6 without edit (STALE-SELF-DESCRIPTION) | `.106` |
| No general (CS-1Q) discharge | "A universal discharge for embedded and mixed genres remains obstructed until those affine ledgers are displayed and checked" | `.111`, `.140`, `.163` |
| No rate from (CS-EXACT) | "No use of (CS-EXACT) is made: this is a bound, not the exact-complement identity" | `.14`, `.66`, `.163`, `.195` |
| No (CS-2)/(CS-3) consumed | "It consumes neither (CS-2), (CS-3), nor (CS-EXACT)" | `.191` |
| n ≤ 3 never consulted [W12-H] | "the reason the n ≤ 3 program never consulted [W12-H]" | `.11`, `.117`, `.135` |
| The annex's own grade | "the annex has NOT itself been through a hostile pass" (stale as of r1, uncured) | `.199` |
| The annex stack's grade | "The annex stack remains 0/2" | `.148`, `.192` |
| Acceptance scope | "The 2/2 acceptance attaches to the frozen body" | `.199` |
| No verifier prose transcribed | "no verifier sentence is transcribed" (r1) / "Transcribed unaltered per the standing division of labor" (R9, R11) | `.199`, `.195`, `.206` |
| No new hypothesis (claimed, then overturned) | "with no new hypothesis" → **overturned**: "conditional on (CS-1Q), verified per genre" | `.178`, `.195` |
| No upper bound on the ragged window | "No new upper bound on the original ragged stage window is claimed or needed" | `.204` |
| No count weakened | "no existing count is weakened"; "No accepted theorem statement is weakened; no count law or frozen number moves" | `.184`, `.206` |
| Report untouched | "the report itself stays untouched — its author's artifact" | `.163`, `.170` |
| Open at the close | "awaiting a clean re-pass + the (CS-1Q) per-genre ledger obligation" | `.206` |
| Annex-stack grade not inherited | GENH4's "annex-stack count is 0/2 with its pass #2 in flight … (not landed at this commit)" | `.92`, `.136` |
| Records may not quantify universally | "A theorem may quantify; a RECORD may not." | `.128` |
| The acceptance does not close the box | "the acceptance freezes the reduction and its record, not the box" | `.146` |
| §S11 frozen (repeated at every round) | "S11 stays frozen at its seal" | `.105`, `.110`, `.118`, `.128`, `.135` |
| No machine leg at r3–r6 | "no machine leg was added … the machine evidence cited is [the verifier's] committed fresh leg, cited, not this note's" | `.110`, `.118`, `.128`, `.135` |
| Verifier reports untouched | "the two verifier reports are their authors' committed artifacts and stay untouched" | `.132` |
| No full run before the seal | "No full battery run before the seal." | `.98` |
| Teeth do not certify theorems | "a tooth off its count voids the battery, not the theorems" | `.100` |
| No axiom / no weld face | "No axiom, no weld face inside any count law" (scoped to count laws) | `.94` |

---

## 3. Statement inventory (206 units, contiguous, in source order)

### EFF.GENIND.01  [changes-record]

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
### EFF.GENIND.02  [instrument-record]

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
### EFF.GENIND.03  [scope-record]

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
### EFF.GENIND.04  [scope-record]

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
### EFF.GENIND.05  [scope-record]

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
### EFF.GENIND.06  [fence]

**CANONICAL STATEMENT:** FORM: inline sentence. verbatim, line 112.

> “This note edits no supplier note. Proposed annex texts: §S9.”

**CONDITIONALITY:** Unconditional and **never contradicted**: §S9.1's heading repeats it (“text offered; W12_PROOF not edited”, line 1429, shard 2), and every later round re-asserts that no supplier artifact was touched. This is header predicate B's governing quote (the NO-APPENDS declaration, rule 17).

**DERIVATION:** Not a mathematical unit; a protocol declaration.

**RESOLUTION TRACE:** statement line 112. correction sites: none. Re-assertions at 1429 and at every §S12–§S16 byte-freeze paragraph (shard 2).

**TEETH:** NONE — a protocol fence, outside the orphan count.

---
### EFF.GENIND.07  [definition]

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

**TARGETS:** `.07` (this unit), `.21`, `.24`, `.34`, `.38`, `.45`.

**DERIVATION:** Definitional. The state count `q^{dm(N−1)}` is W-12 S2.2's bijection, cited not re-proved; the level-0 reduction is W12-S2.1, cited not re-proved.

**RESOLUTION TRACE:** statement lines 116–125. proof lines — none (definitional). correction sites: 2854–2895 (ANNEX R R3, shard 3), with its verification leg at 2891–2895.

**TEETH:** R3.2's machine leg I (`genind_annexr_supp.py` @ f5271e4, GREEN): “(m, Q) ∈ {2, 3, 4} × {2, 3, 4} — 1 state, v(a₀) ≥ 1 = N, DRAIN, u(1) = total = 1”, plus a decorrelated leg (“Codex's sympy re-solve of the S5.2 recursion under exactly this boundary (m = 2 closed forms exact at N = 2..12)”) — disposition `accepted-with-decorrelation-supplied`.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:S2.2` — count **19**.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:W12-S2.1` — count **9**.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:S1` — count **24** (an upper bound: the string matches §-anchors and prose alike).

**PIN VERIFICATION:** `f5271e4` ✓ commit; `verification/openmath/genind_annexr_supp.py` EXISTS ✓; `verification/openmath/genind_annexr_supp_output.txt` EXISTS ✓.

---
### EFF.GENIND.08  [theorem]

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
### EFF.GENIND.09  [theorem]

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
### EFF.GENIND.10  [theorem]

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
### EFF.GENIND.11  [theorem]

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

**TARGETS:** R4 targets `.11` and `.49`; R5 targets `.11` only.

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
### EFF.GENIND.12  [scope-record]

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
### EFF.GENIND.13  [theorem]

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

**TARGETS:** `.13` (this unit), `.45`, `.46`, `.57`.

**DERIVATION:** §S6 Steps 1–5 (`.54`–`.60`); the conditionality geography is `.61`.

**RESOLUTION TRACE:** statement lines 186–196. proof lines 985–1106 (§S6). correction sites: 2580–2777 (ANNEX R R1, shard 3), 3117–3226 (ANNEX R — r1's GENIND-C2, shard 3), 3298–3588 and 3592–3872 (the two 2026-08-12 dated corrections, shard 3), 3076–3088 (the n ≥ 8 conditionality movement, shard 3).

**TEETH:** NONE directly — GENIND.B is a reduction, and no battery row certifies a reduction. Its *components* are toothed (`.08`–`.11`, `.44`–`.46`); its consequence is scored only through §S11's “Consequence for the grade box” paragraph. This is a **PROOF-ONLY** unit in the sense of rule 16; the note's own coverage sentence is GENIND-BOX-1 (lines 1351–1356, shard 2): “THEOREM GENIND.B is a REDUCTION; its unconditional content at n ≥ 4 is exactly the simple-stage layer (GENIND.C) + the criterion + the opening-mass laws.”

XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:HM3.A` — count **18**.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:[W12-H]` — count **17** (the `(H-e)` cite rides inside it).

---
### EFF.GENIND.14  [hypothesis]

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
### EFF.GENIND.15  [theorem]

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

**TARGETS:** `.15`, and by inheritance `.04`, `.13`, `.61`.

**DERIVATION:** §S6 Step 5 (`.60`) fires W-12.D; the strong induction is Steps 1–4 plus the two proved bases. The base pins are §S9.3's (shard 2): W-11 @ **ACCEPTED 2/2 35e6545**; HEX3 @ **r3 b6a1d69**; HMENU3 @ **ACCEPTED body 050425d + ANNEX A 19c0285**.

**RESOLUTION TRACE:** statement lines 215–223. proof lines 1102–1106 (Step 5). correction sites: 1483–1517 (§S9.3's re-pins of the two bases, shard 2); 3032–3094 (the supplier-movement record, shard 3).

**TEETH:** NONE — the consequence is a theorem application, not a measured quantity. **Note for the merge:** §S11's closing paragraph (lines 1760–1764, shard 2) states the *machine* status of this clause (“THEOREM GENIND.B stands as the displayed reduction … conditional exactly on the composite-stage package [GENIND-H] per genre plus the supplier arc grades”), which is a verdict record, not a tooth.

XREF: `lean/notes/openmath/W11_PROOF_2026-08-08.md:THEOREM W-11` — count **3**.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:W12-L0` — count **32**.
XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN-TOW-1` — count **19**.
XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN.C` — count **19**.
**NEAR-MISS (rule 15):** `[GENHN-HE(μ ≥ 3)]` — designation absent as written in `GENHN_PROOF_2026-08-08.md` (fixed-string count **0**); the note itself records the locality defect at PE7-m3 (lines 2499–2506, shard 2): “the string "GENHN-HE" occurs at r6 only inside S16 itself (grep: L2354, L2397 …) — the note displays no box by that name; the μ ≥ 3 stage-law content rides inside [GENIND-H]”. Verified referent: the μ ≥ 3 stage-law content of `[GENIND-H]`. Carried descriptively; **not** emitted as a clean XREF.

---
### EFF.GENIND.16  [scope-record]

**CANONICAL STATEMENT:** FORM: bold display (the GRADE box closing THEOREM GENIND.B). verbatim, lines 225–227.

> “**GRADE: the reduction (IH)+[GENIND-H] ⟹ P(n) PROVED at the S6
> level of detail (scaffold); [GENIND-H] OPEN (the frontier), with
> the (2,2) instance attacked in S7.**”

**CONDITIONALITY:** Stands. Two qualifications from outside the range, neither editing it: GENIND-BOX-1 (lines 1351–1356, shard 2) prices “the S6 level of detail” — “No count law at order ≥ 2 is claimed proved”; and the ANNEX R close (lines 3022–3025, shard 3) discloses that the annex layer which supplies R1's rate leg “has NOT itself been through a hostile pass”, so the (A2-RATE) strengthening of `.13` carries a **lower** grade than the frozen body it repairs.

**DERIVATION:** Not a mathematical unit; a grade declaration.

**RESOLUTION TRACE:** statement lines 225–227. correction sites: 1351–1356 (GENIND-BOX-1, shard 2); 3022–3028 (the ANNEX R close, shard 3); 3285–3294 (the ANNEX R — r1 grade line, shard 3: “The annex stack remains 0/2”).

**TEETH:** NONE — a grade declaration.

---
### EFF.GENIND.17  [lemma]

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
### EFF.GENIND.18  [lemma]

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
### EFF.GENIND.19  [lemma]

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
### EFF.GENIND.20  [instance-record]

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
### EFF.GENIND.21  [lemma]

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
### EFF.GENIND.22  [lemma]

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
### EFF.GENIND.23  [instance-record]

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
### EFF.GENIND.24  [lemma]

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
### EFF.GENIND.25  [lemma]

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
### EFF.GENIND.26  [scope-record]

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
### EFF.GENIND.27  [changes-record]

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
### EFF.GENIND.28  [changes-record]

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
### EFF.GENIND.29  [fence]

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
### EFF.GENIND.30  [lemma]

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
### EFF.GENIND.31  [changes-record]

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
### EFF.GENIND.32  [lemma]

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
### EFF.GENIND.33  [instance-record]

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
### EFF.GENIND.34  [lemma]

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
### EFF.GENIND.35  [lemma]

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
### EFF.GENIND.36  [lemma]

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

**TARGETS:** `.36` and `.24` (step (3)'s fiber sentence) — R2.0 names both sites explicitly.

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
### EFF.GENIND.37  [lemma]

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
### EFF.GENIND.38  [instance-record]

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
### EFF.GENIND.39  [lemma]

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
### EFF.GENIND.40  [run-record]

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
### EFF.GENIND.41  [instrument-record]

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
### EFF.GENIND.42  [scope-record]

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
### EFF.GENIND.43  [theorem]

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
### EFF.GENIND.44  [scope-record]

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
### EFF.GENIND.45  [lemma]

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
### EFF.GENIND.46  [theorem]

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
### EFF.GENIND.47  [convention]

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
### EFF.GENIND.48  [lemma]

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
### EFF.GENIND.49  [lemma]

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

**TARGETS:** `.49` and `.11`.

**ARITHMETIC AUDIT (compiler-computed):** heights (4k, 3k, 2k, k) on a length-4 side at integer slope k ✓ (the supporting line drops by k per abscissa), so `v(a₀) = 4k` ✓ and the floor is `4k ≤ N−1` ✓. Unfloored at (q, N, k) = (2, 2, 1): `(2·1/2)·2^{8−10−4} = 1·2^{−6} = 2^{−6}` ✓ — **a non-integer**, the sharpest possible signature of a missing floor. Above the floor at (2, 5, 1): `1·2^{20−10−4} = 2⁶ = 64` ✓ matching R4.2. Cross-check against §S11 P-3: at (·,2,6,n4) with k = 1 the law gives `1·2^{24−10−4} = 2^{10} = 1,024` ✓ = the reported `F4(1) = 1,024`. At (·,3,4,n4) the note reports `F4 ABSENT (4k ≤ 3 impossible)` — recomputed: `4·1 = 4 > N−1 = 3` ✓ **absent**, and this is precisely the floor R4 says was undisplayed, applied correctly by the runner. **The runner and the display disagreed; the runner was right.**
Row-total cross-check: §S11 P-3 reports “row CS total 66,560 = E4+F4” at (·,2,6,n4); recomputed `65,536 + 1,024 = 66,560` ✓, and §S10's cost probe independently reported “66,560 CS” at (Fqt,2,6,n4) ✓ — three independent agreements.

**DERIVATION:** Direct S2.2 slot count (per `.47`); not displayed. Sibling to `.48`, whose exponent is independently re-derived at `.68`.

**RESOLUTION TRACE:** statement lines 945–947. proof lines — none displayed. correction sites: 2897–2925 (ANNEX R R4 in full, shard 3).

**TEETH:** GT-DEPTH0 (the F4(1) spot, exact; and correctly ABSENT where the floor excludes it) · GT-CRIT · R4.2's machine leg H (`genind_annexr_supp.py` @ f5271e4, GREEN) — a **source-code gate verification**, an unusual and strong disposition: the tooth reads the pinned runner's two gate lines verbatim and confirms the runner implements the floor the display omitted. **PIN VERIFICATION:** `genind_checks.py` EXISTS ✓; the cited gate lines are `709` and `869` — verified present in the pinned file by R4.2's own leg, not re-verified here (the file is md5-pinned and byte-frozen).

XREF: `lean/notes/openmath/QSCOUT22_2026-08-08.md:GENRE F` — count **1**.

---
### EFF.GENIND.50  [lemma]

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
### EFF.GENIND.51  [lemma]

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
### EFF.GENIND.52  [scope-record]

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
### EFF.GENIND.53  [scope-record]

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
### EFF.GENIND.54  [theorem]

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
### EFF.GENIND.55  [theorem]

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
### EFF.GENIND.56  [theorem]

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
### EFF.GENIND.57  [theorem]

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
### EFF.GENIND.58  [changes-record]

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
### EFF.GENIND.59  [changes-record]

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
### EFF.GENIND.60  [theorem]

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
### EFF.GENIND.61  [scope-record]

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
### EFF.GENIND.62  [definition]

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
### EFF.GENIND.63  [hypothesis]

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
### EFF.GENIND.64  [hypothesis]

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
### EFF.GENIND.65  [hypothesis]

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
### EFF.GENIND.66  [hypothesis]

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
### EFF.GENIND.67  [scope-record]

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
### EFF.GENIND.68  [lemma]

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
### EFF.GENIND.69  [instance-record]

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
### EFF.GENIND.70  [hypothesis]

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
### EFF.GENIND.71  [lemma]

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
### EFF.GENIND.72  [fence]

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
### EFF.GENIND.73  [preregistration]

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
### EFF.GENIND.74  [scope-record]

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
### EFF.GENIND.75  [fence]

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
### EFF.GENIND.76  [fence]

**CANONICAL STATEMENT:** FORM: bulleted display. verbatim, lines 1357–1360.

> “* **GENIND-BOX-2 (GENIND-3's ledger compression).** The β-transport
>   is proved as a schema with per-route ledgers compressed (S4.1's
>   honesty note); hostile targets named there. The n = 4, 5 pointwise
>   machine families are the compensating instrument.”

**CONDITIONALITY:** Standing. **Two of the three hostile targets it points at subsequently FIRED** — target (b) at PE3 (the capped-window correction) and target (a) at the Codex ratification (the unit-pivot gap, ANNEX R R2). The box's own text is not edited by either; the fires are recorded at §S13 (`.111`) and, out of range, at ANNEX R R2 (shard 3).

**DERIVATION:** Not a mathematical unit; a compression-debt box over shard 1's `.24`/`.26`.

**RESOLUTION TRACE:** statement lines 1357–1360. correction sites: none in range; the fired targets at 1846–1869 (in range, `.111`) and 2779–2852 (shard 3).

**TEETH:** the box NAMES its compensating instrument — GT-BETA at n = 4, 5 — and thereby scopes its own guarantee. Disposition: `disclosed non-repair` above n = 5 (the compensating instrument does not reach there).

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:HEX3-BOX-2` — count **4**.

---
### EFF.GENIND.77  [fence]

**CANONICAL STATEMENT:** FORM: bulleted display. verbatim, lines 1361–1366.

> “* **GENIND-BOX-3 (d ≥ 2 and prime-power coverage).** The battery
>   exercises d = 1 clusters at prime q only; general d ≥ 2 (and the
>   Q = q^d letter spaces) rests on the proofs' Q-uniformity (the
>   arguments never use d = 1) — machine-uncorroborated here beyond the
>   w12-sealed order-1 instances; prime-power q rows are carried by the
>   supplier batteries (HEX3/HMENU3 up to q = 27).”

**CONDITIONALITY:** Standing, with its hedge intact. §S14 claim group **C11** re-audits it and keeps it AS HEDGED (`.123`): “a proof-audit claim, already disclosed in the same box as machine-uncorroborated beyond the w12 order-1 instances; PE4 §2 left it as disclosed. KEPT with its hedge.” **Partly overtaken from outside the range:** the dated acceptance record (`.146`) reports PE8's route as “non-prime base q ∈ {4, 8, 9} + the n = 12 double-composite”, and PE7's as “first d ≥ 2 + n = 10 route” — i.e. **two hostile passes subsequently exercised exactly the two uncorroborated directions this box names, and the box is not edited.** Tagged `STALE-SELF-DESCRIPTION` (rule 26) in its coverage clause: “The battery exercises d = 1 clusters at prime q only” remains true of *this note's own battery* and is no longer true of the arc's evidence base.

**DERIVATION:** Not a mathematical unit; a coverage box.

**RESOLUTION TRACE:** statement lines 1361–1366. correction sites: none (never edited); re-audit at 2115–2118 (§S14 C11, `.123`); overtaken by 2513–2520 (`.146`).

**TEETH:** `signed vacuity disclosure` in the d ≥ 2 and prime-power directions for the note's own battery; **foreign-note evidence** (PE7's and PE8's committed legs `genind_pe7_fresh.*` and `genind_pe8_fresh.*`, both verified to EXIST on disk ✓) supplies the missing coverage without the box recording it.

---
### EFF.GENIND.78  [fence]

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
### EFF.GENIND.79  [changes-record]

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

**CONDITIONALITY:** **The arc close is superseded by name.** The dated acceptance record's PE8-m1 cure (lines 2537–2538) quotes it verbatim: “GENIND-BOX-5 arc close, L1414–1415: "— the clean count has NOT started;" — superseded the same way”, i.e. 0/2 → 1/2 (PE7 CLEAN 380bc66) → **2/2 (PE8 CLEAN 3f5bafc), ACCEPTED**. The two closing sentences (minimum-grade inheritance; “a CONDITIONAL STRUCTURE, displayed, not a result”) are **NOT** superseded and remain the operative reading — indeed `.146` re-asserts the second: “[GENIND-H] at n ≥ 4 remains the displayed OPEN box — the acceptance freezes the reduction and its record, not the box.”

**SUPERSESSION KIND:** `counter re-reading` (the clean counter, and only the counter).

**CHAIN:** the frozen arc close (as of r6) → PE7 CLEAN `380bc66` (→ 1/2) → post-PE7 dated corrections `b653858` → PE8 CLEAN `3f5bafc` (→ 2/2) → **PE8-m1 cure at lines 2537–2538 — TERMINAL.** SERIES REPAIR-ARC: this unit is the arc's *summary*, not an entry; the entries are `.105`, `.110`, `.118`, `.128`, `.135`.

**ARITHMETIC AUDIT (compiler-computed, on the finding tallies):** PE1 3G+4m, PE2 2G+1m, PE3 2G+4m, PE4 2G+0m, PE5 1G+2m, PE6 1G+1m — **0 CRITICAL at every one of the six**, total 11 GAP + 12 MINOR across PE1–PE6; adding PE7 (0G+3m) and PE8 (0G+1m) from `.146` gives **11 GAP + 16 MINOR + 0 CRITICAL over eight hostile passes**. The GAP count falls monotonically 3, 2, 2, 2, 1, 1, 0, 0 ✓ — a genuinely monotone arc, matching the note's own “the monotone arc” language at §S14 leg 3 (`.126`), which however describes the *grade* line as monotone, not the finding counts.

**PIN VERIFICATION:** `4259a93` ✓, `50db400` ✓, `f89b565` ✓, `ade9bac` ✓, `bd9bce1` ✓, `265a562` ✓, `ad1bd98` ✓, `f7f45f1` ✓ — 8/8 commits. Named legs `genindr2_supp.py`, `genind_pe3_fresh.*`, `genind_pe4_fresh.*`, `genind_pe5_fresh.*`, `genind_pe6_fresh.*` all EXIST on disk ✓.

**DERIVATION:** Not a mathematical unit; the arc of record.

**RESOLUTION TRACE:** statement lines 1373–1420. correction sites: 2528–2543 (the PE8-m1 cure, `.147`).

**TEETH:** the per-round attributions are report-pinned; **the “sealed runner + artifacts byte-frozen, untouched” clause repeated at every round is the instrument-freeze predicate**, enumerated by md5 at `.134` and `.142`. Disposition: `in-house hostile pass` ×6 (plus 2 outside the range).

---
### EFF.GENIND.80  [convention]

**CANONICAL STATEMENT:** FORM: bulleted display. verbatim, lines 1421–1425.

> “* **GENIND-BOX-6 (conventions).** The conservative drain convention
>   as at HEX3/HMENU3 (v(a₀) ≥ N exits; no tail certification); the
>   reader-reimplementation seams (W10-BOX-3 lineage) inherited; the
>   n = 3 control ties to the committed hex3 JSON mitigate; oracle
>   mixed-characteristic only.”

**CONDITIONALITY:** Standing. **The reader-reimplementation seam is the deepest methodological caveat in the note**: the battery's reader is fresh same-session code (`.95`), so an error shared between the reader and the note's own mechanics would be invisible to every family except GT-N3TIE (which ties to a foreign committed artifact) and GT-ORACLE (which is mechanism-free). The box names both mitigations.

**DERIVATION:** Not a mathematical unit; a convention/seam declaration.

**RESOLUTION TRACE:** statement lines 1421–1425. correction sites: none.

**TEETH:** the box IS a statement about the teeth's blind spot. Disposition: `signed vacuity disclosure` for the reimplementation seam, with two named mitigations (GT-N3TIE foreign tie; GT-ORACLE mechanism-free).

XREF: `lean/notes/openmath/W10_PROOF_2026-08-08.md:W10-BOX-3` — count **1**. (The designation is a lineage pointer; the target note is not in §S9.3's conditionality stack, so no pin is tracked for it — recorded at §8, defect 1.)
XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:HEX3-BOX-1` — count **11**; the conservative-drain convention this box inherits is the same one whose tail-σ residue is HEX3-BOX-1 (ledger **HYP.137**; see `.85`).

---
### EFF.GENIND.81  [scope-record]

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
### EFF.GENIND.82  [scope-record]

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
### EFF.GENIND.83  [scope-record]

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

**CONDITIONALITY:** **The sealed parenthetical “(arc 0/2, PE2 adjudicated + r2, PE3 owed)” is a STALE-SELF-DESCRIPTION corrected by dated append, not by edit** — it sat true at 08-08 10:16 and went stale across three undisclosed supplier rounds, one of which repaired a **CRITICAL**. The `[r6]` append supplies the new pin and the survival evidence. **The survival evidence is itself corrected once more**: PE7-m1 (`.143`) re-words “zero S3.2 cites in this note” to “zero S3.2 cites outside this round's own disclosure sentences (grep: 4 string hits, all four disclosure)”.

**SUPERSESSION KIND:** `as-of scoping` (the pin) + `counter re-reading` (the arc parenthetical) + a further `wording-rider` from PE7-m1 on the grep claim. **Three kinds on one bullet.**

**CHAIN:** sealed pin `r2 99f1813` with a stale arc parenthetical → `[r6]` RE-PIN to **`r5 HEAD be4a1dc/ee17210`**, three intervening rounds enumerated including a repaired CRITICAL → PE7-m1's correction of the grep claim — **TERMINAL: pin = r5 be4a1dc/ee17210; verdict SURVIVES; the S3.2 claim reads “zero consuming cites; 4 string hits, all disclosure”.**

**DERIVATION:** Not a mathematical unit; a supplier pin + consumption verdict. The verdict's substance is re-verified verbatim at `.138`.

**RESOLUTION TRACE:** statement lines 1466–1482. correction sites: 2354 (§S16 row 1), 2376–2399 (`.138`, the verbatim re-verification), 2479–2487 (PE7-m1, `.143`).

**TEETH:** GT-PIN guards the w12 **runner** md5, not the note pin; the note pin is git-log-checked. Disposition: `in-house hostile pass` (PE6 found the staleness) + `transfer audit` (rule 27 — the survival verdict is a clause-by-clause transfer check across a supplier's repair arc, which no battery row could perform).

**PIN VERIFICATION:** `f669cb0`, `c16c717`, `ba0d1a4`, `99f1813`, `b17238a`, `d2d91b7`, `5728258`, `be4a1dc`, `ee17210` — **all resolve as commits ✓** (9/9).
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:THEOREM W-12.D` — count **5**; `THEOREM W-12.A` — count **8**; `S2.4` — count **10**; `S2.5` — count **9**; `W12-L0` — count **32**; `W12-L1` — count **30**; `σ-LABELING` — count **7**; `b₂ = 0` — count **15**.

---
### EFF.GENIND.84  [scope-record]

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

**TEETH:** GT-PIN guards the w11 runner md5 (`500aae15`, `.142`). Disposition: `transfer audit`, trivial (zero content diff).

**PIN VERIFICATION:** `7020ceb` ✓, `31506b3` ✓, `839b735` ✓, `35e6545` ✓.
XREF: `lean/notes/openmath/W11_PROOF_2026-08-08.md:THEOREM W-11` — count **3**.
XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:R(M)` — count **21**.

---
### EFF.GENIND.85  [scope-record]

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
### EFF.GENIND.86  [scope-record]

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

**TEETH:** GT-PIN guards the hmenu3 runner md5 (`65326f85`, `.142`). Disposition: `transfer audit` — a clause-level check that the supplier's quantifier correction lands on the form consumed.

**PIN VERIFICATION:** `64d3ff9` ✓, `625fa49` ✓, `f4f7b03` (cited; not re-verified here — shard-2 note: it resolves), `3235e1b` ✓, `e1280be` ✓, `050425d` ✓, `19c0285` ✓.
XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:HM3-1` — count **4**; `HM3-2` — count **5**; `HM3-3` — count **3**; `HM3-4` — count **11**; `HM3.A` — count **18**; `HM3.B` — count **19**; `HM3.C` — count **15**; `HM3.D` — count **13**.

---
### EFF.GENIND.87  [scope-record]

**CANONICAL STATEMENT:** FORM: bulleted display. verbatim, lines 1518–1519.

> “* **LEMMA J-D0** @ 1642275/9387eb1 — the count-gauge-blindness frame
>   (S7's letter-blindness; the char-tally legs corroborate again).”

**CONDITIONALITY:** Unmoved. §S16's unmoved-pin list (lines 2365–2366): “J-D0 @ 1642275/9387eb1 — note last touched 9387eb1 (08-07 16:54), pre-seal, pin = HEAD ✓”.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1518–1519. correction sites: 2365–2366 (`.137`).

**TEETH:** Indirect — the char-tally legs (GT-PART's Zp/F_q[[t]] identity at all 11 shared (m,q,N)) are the standing corroboration of letter-blindness.

**PIN VERIFICATION:** `1642275` ✓, `9387eb1` ✓.
XREF: `lean/notes/openmath/JD0_PROOF_2026-08-08.md:LEMMA J-D0` — count **4**.

---
### EFF.GENIND.88  [scope-record]

**CANONICAL STATEMENT:** FORM: bulleted display. verbatim, lines 1520–1522.

> “* **GRTJC W-6..W-9 (ACCEPTED 2/2 @ 83f47f4; JC-F1/JC-F2 [r1/r2])** —
>   consumed ONLY in S7's display: dim_K 𝒜(T) = E, the carry cocycle,
>   JC-LOAD's no-cancellation. No count law of S2–S6 consumes them.”

**CONDITIONALITY:** Unmoved body. §S16's unmoved-pin list (lines 2367–2369): “GRTJC (accepted 2/2 @ 83f47f4) — note last touched 63091ce (08-07 20:06, pre-seal annex), body unmoved ✓”. **The second sentence is a NON-IMPORT fence** and is one of the three quotes that make header predicate A's scope split honest.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1520–1522. correction sites: 2367–2369 (`.137`).

**TEETH:** NONE — a citation + fence.

**PIN VERIFICATION:** `83f47f4` ✓, `63091ce` ✓.
XREF: `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md:W-6` — count **18**; `W-8` — count **35**; `W-9` — count **13**; `JC-F1` — count **18**; `JC-LOAD` — count **31**; `dim_K 𝒜(T) = E` — count **3**.
**NEAR-MISS:** `W-7` is named only inside the range designation “W-6..W-9”; fixed-string `W-7` is not separately cited in GENIND and is not emitted as an XREF.
**NEAR-MISS:** `JC-F2` — cited here as one of the two GRTJC findings; not separately grep-recorded (the bullet's substantive cites are JC-F1 and JC-LOAD). Recorded so the merge does not treat `JC-F2` as a verified consumed designation.

---
### EFF.GENIND.89  [scope-record]

**CANONICAL STATEMENT:** FORM: bulleted display. verbatim, lines 1523–1524.

> “* **WELDMASTER / DULEMMA / [W12-H]** @ their accepted pins — named in
>   S7.1's (CS-1..3) pricing only.”

**CONDITIONALITY:** Unmoved bodies. §S16's unmoved-pin list (lines 2366–2371): “DULEMMA @ f819f26 — last touched f819f26 (08-07 18:59), pin = HEAD ✓; … WELDMASTER (accepted) — note last touched fdf1d99 (08-07 19:20, pre-seal fold-carry annexes), body unmoved ✓ … [W12-H] is W12-note-internal and rides row 1.” **The bullet cites no pin of its own** (“@ their accepted pins”) — a non-enumerative pin reference of exactly the species the standing rule (`.128`) later bans in RECORDS; §S16 supplies the enumeration.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1523–1524. correction sites: 2363–2371 (`.137`, which supplies the missing enumeration).

**TEETH:** NONE.

**PIN VERIFICATION:** `f819f26` ✓, `fdf1d99` ✓. Target files `WELDMASTER_2026-08-08.md` ✓ and `DULEMMA_PROOF_2026-08-08.md` ✓ EXIST.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:[W12-H]` — count **17**.

---
### EFF.GENIND.90  [scope-record]

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

**TEETH:** NONE consumed. The scout's own GREEN (7,614,473/0) is foreign evidence for the scout's predictions, **not for GENIND's `.147`**; the note does not claim otherwise, and this compilation does not infer otherwise.

**PIN VERIFICATION:** `240a56c` ✓, `970197d` ✓, `dd67cda` ✓, `fcaf268` ✓.
XREF: `lean/notes/openmath/GENH4_PROOF_2026-08-08.md:GENH4-BOX-7` — count **1**.
XREF: `lean/notes/openmath/QSCOUT22_2026-08-08.md:GENRE E` — count **2**.

---
### EFF.GENIND.91  [scope-record]

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
1. **The four-clause consumed surface is INCOMPLETE.** PE7-m2 (`.144`) completes it to seven: “beyond the four listed clauses (A(iv), A(v), GENHN-3, S6.2), this note leans on GENHN at three further sites — the GENHN S11.F schema cite at the GENIND-6(a) proof (L684), the GENHN S6.3 display cite at S6 Step 4 (L1094), and the embedded-genre echo at the GENIND-6(a) statement (L623) — screen future GENHN errata against the seven sites, not four”.
2. **“the next dated append owes their execution disclosure”** — an explicitly owed obligation, discharged by the dated supplier-movement record (lines 3032–3094, shard 3), which opens: “**Owed disclosure discharged (S16 row 6: "execution disclosure owed at the next dated append")**”, reports E1/E2/E3 executed plus GENHN r2, and screens all seven PE7-m2 sites clause by clause. **That record also changes GENIND's own conditionality at n ≥ 8** (shard 1 `.15`).

**SUPERSESSION KIND:** `[r3, PE3-m4]` = `inventory completion` (a bullet consumed since r1/r2 is added to the roster). `[r6]` = `as-of scoping` **with an owed obligation attached** — a form the v3 enum does not name; recorded as `as-of scoping + owed-disclosure`. PE7-m2 = `inventory completion` (four sites → seven).

**CHAIN:** consumed-but-unlisted (r1/r2) → `[r3, PE3-m4]` added to the stack, four clauses → `[r6]` as-of disclosure, three errata queued, disclosure owed → **PE7-m2: seven sites, not four** → **dated supplier-movement record: errata E1–E3 EXECUTED + GENHN r2, all seven sites screened, all SURVIVE; conditionality at n ≥ 8 gains [GENHN-TOW-1] — TERMINAL.**

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1535–1550. correction sites: 2359 (§S16 row 6), 2488–2498 (PE7-m2, `.144`), 3032–3094 (the supplier-movement record, shard 3).

**TEETH:** NONE — a pin + consumed-clause inventory. Disposition: `transfer audit` at ledger granularity (the note says so: “Per-clause check at ledger granularity”), later re-run at diff granularity by the supplier-movement record (“screened against the 850e77e → HEAD diff this round”).

**PIN VERIFICATION:** `850e77e` ✓. The errata/r2 commits named in shard 3 — `bc1b996` ✓, `961d0ff` ✓, `46bf675` ✓, `58b1080` ✓, `d16869c` ✓, `7650b20` ✓, `438608a` ✓, `9636b7e` ✓ — all resolve (8/8), recorded here because they discharge this bullet's owed obligation.
XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN.A(iv)` — count **3**; `GENHN.A(v)` — count **6**; `LEMMA GENHN-3` — count **3**; `S6.2` — count **6**; `S11.F` — count **10**; `S6.3` — count **3**; `GENHN.A(i)` — count **11**.

---
### EFF.GENIND.92  [scope-record] · **SERIES GENH4-PIN, all four entries**

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

**DERIVATION:** Not a mathematical unit; a supplier pin arc + consumption verdict. The verdict's substance is re-verified verbatim at `.139`.

**RESOLUTION TRACE:** statement lines 1551–1599. correction sites: 2360 (§S16 row 7), 2401–2421 (`.139`, the verbatim re-verification), 2129–2151 (§S14 C14, whose close this bullet's r5/r6 entries falsify and replace, `.124`).

**TEETH:** NONE in this note — the discharge is a citation. Its guard is the **verbatim text match performed at `.139`** against `git show 4b0d946`, plus the negative screen (“none of the annex findings touches …”). Disposition: `transfer audit`.

**PIN VERIFICATION:** `4b0d946` ✓, `e15308d` ✓, `11dbd23` ✓, `baf05ed` ✓, `5c8d2fd` ✓, `b10a5a7` ✓, `a8dec16` ✓, `fed3cff` ✓, `760d20f` ✓ — **9/9 commits resolve.** (`a584cb3e` is an md5, not a commit.)
XREF: `lean/notes/openmath/GENH4_PROOF_2026-08-08.md:THEOREM GENH4.A` — count **5**; `THEOREM GENH4.B` — count **6**; `GENH4-1F` — count **10**; `Q22-L1` — count **7**; `Q22-L3` — count **3**; `ANNEX-LEMMA GENH4-7` — count **11**.
XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN.A(i)` — count **11**; `GENHN.A(iv)` — count **3**; `GENHN.A(v)` — count **6**; `LEMMA GENHN-3` — count **3**; `S6.2` — count **6**.

---
### EFF.GENIND.93  [scope-record]

**CANONICAL STATEMENT:** FORM: bulleted display. verbatim, lines 1600–1601.

> “* **Classical:** Hensel (coprime + monic-factor lifting), Ore/GMN
>   order-1, lower-hull geometry, generating functions.”

**CONDITIONALITY:** The classical-only base. **Load-bearing for the axiom question**: `.94`'s close says “No axiom, no weld face inside any count law”, and this bullet is what that sentence quantifies over. Note that **Ore/GMN order-1 is classical here while the order-≥2 GMN leaf theorem is (CS-3)/(H-e), OPEN** (shard 1 `.65`) — the line between cited-classical and open-hypothesis runs exactly at order 1.

**DERIVATION:** Not a mathematical unit; a classical-supplier list.

**RESOLUTION TRACE:** statement lines 1600–1601. correction sites: none.

**TEETH:** NONE.

---
### EFF.GENIND.94  [scope-record]

**CANONICAL STATEMENT:** FORM: bold display closing §S9.3. verbatim, lines 1603–1608.

> “**One line: THEOREM GENIND.A(I,II,IV) + GENIND.C's hypothesis set =
> {W-11, W-12.A/L0/L1, HEX3, HMENU3 @ pins + this note's lemmas};
> GENIND.A(III) adds the S4.1 ledger-compression honesty; THEOREM
> GENIND.B adds [GENIND-H] as its displayed hypothesis; the FULL
> uniformity consequence consumes THEOREM W-12.D @ pin. No axiom, no
> weld face inside any count law; grade = composition 0/2.**”

**CONDITIONALITY:** **Header predicate A's governing quote.** Its final clause “grade = composition 0/2” is superseded by the acceptance (`.146`): the note is ACCEPTED 2/2. The rest stands. **Two things a chapter cut must not over-read:** (i) “No axiom, no weld face inside any count law” is a claim about COUNT LAWS, not about the reduction's hypothesis box — [GENIND-H] is a displayed hypothesis, not an axiom, and the sentence does not claim otherwise; (ii) the hypothesis set is stated “@ pins”, and every one of those pins moved (`.83`–`.92`).

**SUPERSESSION KIND:** `counter re-reading` on the grade clause only.

**DERIVATION:** Not a mathematical unit; the note's own one-line self-inventory.

**RESOLUTION TRACE:** statement lines 1603–1608. correction sites: 2510–2526 (`.146`).

**TEETH:** NONE — an inventory sentence.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:THEOREM W-12.D` — count **5**; `THEOREM W-12.A` — count **8**; `W12-L0` — count **32**; `W12-L1` — count **30**.
XREF: `lean/notes/openmath/W11_PROOF_2026-08-08.md:THEOREM W-11` — count **3**.

---
### EFF.GENIND.95  [instrument-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (§S10's runner description). verbatim, lines 1612–1619.

> “**Runner:** `verification/openmath/genind_checks.py`. Exact integer
> arithmetic; deterministic; cypari2 only in GT-ORACLE. Self-contained
> reader (fresh same-session code — GENIND-BOX-6's seam), consuming the
> suppliers ONLY as md5 pins + the committed hex3 JSON tie. The reader
> implements the general recursive conservative read: drain rule first,
> exact hull, per-side residuals, α by in-frame recentering, β children
> by c = k scaling (D = weighted min) + monic Hensel extraction at
> window W − D, CS-EXIT at composite openings.”

**CONDITIONALITY:** **This description is what makes the capped-window concordance checkable**: “β children by c = k scaling (D = weighted min) + monic Hensel extraction at window W − D”. §S14's window-site inventory classifies this very sentence as site class 14 and verifies it against the pinned source (`.121`): “CAPPED; matches `extract_child` (md5 e7ca150b), which implements D = min_j(v(a_j) + j·k) literally.” **So the runner implemented the capped window from the seal, while the note's display did not** — the whole PE3-G2/PE4-G1 arc is a display-versus-implementation divergence in which the implementation was right.

**DERIVATION:** Not a mathematical unit; the apparatus.

**RESOLUTION TRACE:** statement lines 1612–1619. correction sites: 2062–2065 (§S14 site class 14, `.121`).

**TEETH:** self-referential. **PIN VERIFICATION:** `verification/openmath/genind_checks.py` EXISTS ✓; md5 pin `e7ca150b` (the note's own repeatedly re-verified value); seal commit `c3212cc` ✓.

---
### EFF.GENIND.96  [instrument-record]

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
### EFF.GENIND.97  [instrument-record]

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
* **Constructed legs:** n = 4 α(2) at (Zp, 2, 9) — a *reduced* window count 4,096 = `2^{12}`, not `2^{4·8}` (the α(2) node is a slice, not the full space); n = 5 α(1) at (2,6) → 1,024 = `2^{10}`; (3,6) → 118,098 = `2·3^{10}` = 2·59,049 ✓; BFULL(1) at (3,6): 59,049 = `3^{10}`, 118,098 = `2·3^{10}`, 354,294 = `6·3^{10}` ✓ — the three type multiplicities are 1 : 2 : 6 for types 22/31/2Q. **Consistent as slice counts; NOT full-space counts** — the same reading hazard shard 1 records at its `.101`/`.102`.
* **Constructed total:** 4,096 + 1,024 + 1,024 + 118,098 + 59,049 + 118,098 + 354,294 = **655,683**. The note gives no constructed total; recorded here for the merge.

**DERIVATION:** Not a mathematical unit; the roster.

**RESOLUTION TRACE:** statement lines 1633–1641. correction sites: none. Re-verified out of range by PE4's isolated re-run (§S14 C12, `.123`).

**TEETH:** the roster IS the coverage the families inherit; the constructed legs are the note's answer to state-space blowup (“CONSTRUCTED targeted loci where it does not”, shard 1 `.02`).

---
### EFF.GENIND.98  [run-record]

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
### EFF.GENIND.99  [preregistration]

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

**CONDITIONALITY:** **A genuine two-commit preregistration** — “commit 1; spot values computed from the sealed predictor pre-run”, with “No full battery run before the seal” (`.98`). Under rule 19 this unit and `.103` (the scored run-record) are TWO units and must stay two: the prediction's truth condition is *was it stated in advance*, the run-record's is *what did the instrument return*.

**ARITHMETIC AUDIT (compiler-computed; every spot value re-derived from the displayed laws of shard 1 — this is the audit that tests whether the preregistration was honestly derivable rather than back-fitted):**
* **(·,2,6,n4):** `E4(1) = (q−1)q^{4N−5h−3} = 1·2^{24−5−3} = 2^{16} = 65,536` ✓. `F4(1) = (q(q−1)/2)q^{4N−10k−4} = 1·2^{24−10−4} = 2^{10} = 1,024` ✓. `DRAIN₀ = q^{d(m−1)(N−1)} = 2^{3·5} = 32,768` ✓. `ALPHA(1) = (Q−1)Q^{m(N−1)−k·m(m+1)/2} = 1·2^{20−10} = 2^{10} = 1,024` ✓. CS total `65,536 + 1,024 = 66,560` ✓ = the cost probe's figure.
* **(·,3,4,n4):** `E4(1) = 2·3^{16−5−3} = 2·3^8 = 2·6,561 = 13,122` ✓. `DRAIN₀ = 3^{3·3} = 19,683` ✓. `F4 ABSENT` because `4k ≤ N−1 = 3` is impossible ✓ (the floor R4 later had to add to the display — **and the preregistration already applied it**, which is the sharpest evidence that the defect was display-only). `ALPHA ABSENT`: α needs `mk ≤ N−1`, i.e. `4k ≤ 3`, impossible ✓.
* **(·,5,3,n4):** `E4(1) = 4·5^{12−5−3} = 4·5^4 = 4·625 = 2,500` ✓. `DRAIN₀ = 5^{3·2} = 15,625` ✓.
* **(·,2,5,n5):** `V1E2(1) = (q−1)q^{4N−5h−3}(q^{N−(5h+1)/2}−1) = 1·2^{20−5−3}·(2^{5−3}−1) = 2^{12}·3 = 12,288` ✓. `DRAIN₀ = 2^{4·4} = 65,536` ✓. `V4E2 ABSENT` by the vertex condition (min entry height 7 > N−1 = 4) ✓.
* **(·,3,3,n5):** headroom `N − (5h+1)/2 = 3 − 3 = 0` → factor `3⁰ − 1 = 0` ✓ NO CS key. `DRAIN₀ = 3^{4·2} = 6,561` ✓.
* **P-4:** `R(2) = 2` of `q^{2(M−1)} = 2² = 4` block states → half of 1,024 = **512** ✓.
* **P-10 tooth counts:** GT-T-CS = 12 = “every n = 4 row” = 6 (q,N) rows × 2 ring kinds ✓. GT-T-CRIT = 4 = 2 rows × 2 kinds ✓. GT-T-BRACKET = 24 = 4 values of m × 3 values of μ × 2 values of q ✓ **exactly**. GT-T-ALPHA = 12 = “8 sweep rows with α keys + 4 constructed legs” ✓ (the four constructed α legs are (Zp,2,9) n=4, (Zp,2,6) n=5, (Fqt,2,6) n=5, (Zp,3,6) n=5 = 4 ✓).
* **Zp/Fqt shared cells:** the roster has 11 distinct (q,N) rows across the three degrees, each run in both ring kinds ✓ — P-2's “all 11 shared (m, q, N)” checks against `.97`'s row inventory exactly.
**Verdict of the audit: all twenty-one preregistered spot values and all four tooth counts are re-derivable from the displayed laws.** Two of them (F4's absence at (·,3,4,n4); V4E2's absence at (·,2,5,n5)) depend on visibility floors that the S5.3 display did NOT carry at seal time — the predictor carried them anyway.

**DERIVATION:** Not a mathematical unit; a preregistration. Its derivability is audited above.

**RESOLUTION TRACE:** statement lines 1655–1684. correction sites: none — §S11 scores it, never edits it.

**TEETH:** this unit IS the tooth specification; `.103` is its scoring.

---
### EFF.GENIND.100  [preregistration]

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

**CONDITIONALITY:** **Preregistered falsifiers with explicit LOCALIZATION rules** — each names which unit dies and, in three cases, which supplier to check first. **The last clause is a scoping fence of unusual quality**: “a tooth off its count voids the battery, not the theorems.” Emitted separately from `.99` because a falsifier set and a point prediction have different truth conditions (a falsifier is *not* confirmed by a clean run; it is merely not triggered).

**ARITHMETIC AUDIT:** the criterion's death condition `e·μ·γ < 4` is exactly the negation of shard 1 `.11`'s necessity bound `e·μ·deg ψ ≥ 4` ✓ — the falsifier is stated at the sharpest possible place, and P-8's scored clause `4 ≤ e·μ·γ ≤ m_frame` is its direct machine form ✓.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1685–1695. correction sites: none. Scored at 1750 (`.103`: “P-11 ✓ — no falsifier fired”).

**TEETH:** the falsifier set is the battery's own theory of what would count as refutation. Disposition: `preregistration`; **none fired**.

---
### EFF.GENIND.101  [changes-record]

**CANONICAL STATEMENT:** FORM: bold display (§S10's closing verdict placeholder). verbatim, lines 1697–1699.

> “**VERDICT: PENDING — commit 1 seals this note + the runner; commit 2
> appends §S11 from `genind_checks_output.txt` /
> `genind_checks_results.json`.**”

**CONDITIONALITY:** **SUPERSEDED by §S11** (`.102`), which is the commit-2 append this sentence promises. The sentence is preserved as a dated record of the two-commit protocol; it is not live.

**SUPERSESSION KIND:** `replacement` — the placeholder is replaced by the verdict it schedules. (The text is not edited; the note simply appends §S11 below it.)

**CHAIN:** `VERDICT: PENDING` (commit 1, seal `c3212cc`) → **§S11 GREEN (commit 2) — TERMINAL.**

**DERIVATION:** Not a mathematical unit; a protocol placeholder.

**RESOLUTION TRACE:** statement lines 1697–1699. correction sites: 1701–1750 (§S11, `.102`/`.103`).

**TEETH:** the two-commit protocol IS the guard against post-hoc prediction editing. **PIN VERIFICATION:** both named artifacts EXIST ✓.

---
### EFF.GENIND.102  [run-record]

**CANONICAL STATEMENT:** FORM: bold display (§S11's headline). verbatim, lines 1703–1710.

> “**GREEN. 163,536 checks, 0 violations in every family, all four teeth
> fired at their EXACTLY-preregistered counts (12/12/4/24), zero
> skips.** 22/22 sweep rows (6,422,014 per-center states, both ring
> kinds) + all 7 constructed legs + 3/3 oracle rows; single fresh run,
> elapsed 164.5 s, exit 0; artifacts `genind_checks_output.txt`
> (md5 c157dc318af13eb10a126cdb9f08f87d),
> `genind_checks_results.json` (md5 366f214322fee97c9669f0584696b3f6);
> runner byte-identical to the sealed commit c3212cc (empty `git diff`).”

**CONDITIONALITY:** **FROZEN AT ITS SEAL — every later repair record says so and none edits it.** §S14's claim group C12 (`.123`) re-verifies it independently: “verdict record, matches the committed artifacts; re-verified by PE4's isolated re-run of the sealed battery (163,536/0, leaf-diff = elapsed only). KEPT.”

**ARITHMETIC AUDIT (compiler-computed):** `22/22 sweep rows` ✓ = `.97`'s 11 (q,N) rows × 2 ring kinds. `6,422,014` ✓ re-derived at `.97` from first principles. `7 constructed legs` ✓ = 1 (n=4 α(2)) + 3 (n=5 α(1) at three (ring,q)) + 3 (BFULL types 22/31/2Q) = 7 ✓. `3/3 oracle rows` ✓ = the three ORACLE rows at `.97`. Tooth tuple `(12/12/4/24)` ✓ = P-10's four preregistered counts, matched one for one. **`163,536 checks` is a check count, not a state count** — it is not reconstructible from the roster (states are inputs, checks are assertions); recorded as UNPINNED-BY-DISPLAY but backed by the two md5-pinned artifacts.

**DERIVATION:** Not a mathematical unit; the sealed run.

**RESOLUTION TRACE:** statement lines 1703–1710. correction sites: **none, at any round** — §S11's freeze is the note's most-repeated invariant. Independent re-verification at 2119–2122 (§S14 C12).

**TEETH:** this unit IS the run of record. **PIN VERIFICATION:** both artifacts EXIST ✓; seal commit `c3212cc` ✓; the “empty `git diff`” claim is a commit-time assertion, not re-checkable at HEAD (the runner's md5 pin `e7ca150b` is the standing proxy and is re-verified at every round).

---
### EFF.GENIND.103  [run-record]

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
* **P-3:** all nine spot values re-derived at `.99` from the displayed laws ✓; `66,560 = 65,536 + 1,024` ✓.
* **P-4:** `512/1,024` ✓ (audited at `.99`).
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
### EFF.GENIND.104  [scope-record]

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

**CONDITIONALITY:** Frozen at seal, and therefore **two clauses are STALE by construction**: “Attempt 0/2; the hostile arc has not begun” (eight passes have since run; ACCEPTED 2/2 at `.146`) and “conditional exactly on the composite-stage package [GENIND-H] per genre plus the supplier arc grades” (at n ≥ 8 two further conjuncts enter, shard 3). **Neither is corrected in place** — §S11 is frozen — and the PE8-m1 cure explicitly does NOT reach here: it names only the header arc line and GENIND-BOX-5's close (`.147`). Tagged `STALE-SELF-DESCRIPTION` (rule 26) on both clauses. **This is a genuine gap in the cure's coverage** and is recorded as OPEN-CALL 3.

**ARITHMETIC AUDIT:** “the general α-bracket exercised at m = 4, 5 (exponents 7, 11)” ✓ — `c(4)+1 = 7`, `c(5)+1 = 11` (shard 1 `.23`), and P-7 scored all four values 2/4/7/11 ✓.

**DERIVATION:** Not a mathematical unit; a verdict-consequence statement.

**RESOLUTION TRACE:** statement lines 1752–1768. correction sites: **none — and that is the finding.** Overtaken at 2512–2526 (`.146`) and at 3076–3088 (shard 3).

**TEETH:** the consequence is read off `.103`'s scorecard.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:THEOREM W-12.D` — count **5**.

---
### EFF.GENIND.105  [changes-record] · **SERIES REPAIR-ARC, entry 1 of 5**

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

**SERIES:** REPAIR-ARC entry **1 of 5** (r2). Predecessor: r1 (applied in place, no record section — recorded only in the header arc and GENIND-BOX-5). Successor: `.110` (r3).

**CONDITIONALITY:** Three of this record's sentences are later found FALSE and are corrected in place by successors: the PE2-G2 pin-check sentence (by `[r3]` at `.107`) and the PE2-m1 grep claim (by `[r5 sweep]` at `.108`). The Arc paragraph itself is untouched.

**DERIVATION:** Not a mathematical unit. **PIN VERIFICATION:** `50db400` ✓; `genindr2_supp.py` + output + results all EXIST ✓.

**RESOLUTION TRACE:** statement lines 1770–1778. correction sites: none for this paragraph; its record's items at 1795–1808 and 1809–1817.

**TEETH:** the “minimality contract” + “BYTE-FROZEN” pair is the repair protocol's own guard; enumerated by md5 from r5 onward (`.134`, `.142`).

---
### EFF.GENIND.106  [changes-record]

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

**CONDITIONALITY:** **The largest mathematical addition of the whole arc** — a new lemma with four clauses, a worked ledger and a machine leg, added at r2 in response to a gap between two displayed scopes. Its four wiring sites are enumerated and all four are verifiable in shard 1 (`.103`, `.129`, `.131`, `.137`). **The closing sentence's “Conditional structure unchanged … no more” is later narrowed** by the (CS-1Q) upgrade (shard 1 `.37`).

**SUPERSESSION KIND:** `inventory completion` (a transport that fell between two scopes is supplied) — **not** a `replacement`: nothing displayed was withdrawn.

**DERIVATION:** Not a mathematical unit; the mathematics is shard 1's `.31`–`.42`.

**RESOLUTION TRACE:** statement lines 1780–1794. correction sites: none in range; the clause's conditionality is narrowed at 3712–3721 (shard 3).

**TEETH:** `genindr2_supp.py` (`.109`); the M6 instance is the verifier's construction, adopted and displayed in full.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN.A(iv)` — count **3**; `GENHN.A(v)` — count **6**.

---
### EFF.GENIND.107  [changes-record] · **SERIES RECORD-INTEGRITY, entry 1 of 5**

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

**SERIES:** RECORD-INTEGRITY entry **1 of 5** (PE2-G2). The note's own naming of the class, at `.118`: “PE4-G1 is the arc's THIRD consecutive record-integrity defect (class PE2-G2 → PE3-G1 → PE4-G1: a repo-checkable factual sentence in a repair record, false against the repo)”; extended to five at `.135`.

**CONDITIONALITY:** **A record that adopts a standing rule and is itself found in violation of that rule by the very next pass** — the `[r3]` layer quoted here is the finding. The rule adopted (“pin suppliers at their repair HEAD and disclose any adjudicated, not-yet-repaired findings at the pin”) is restated at `.112` as a COMMIT-TIME action.

**SUPERSESSION KIND:** the `[r3, PE3-G1]` layer = `counter re-reading` (a factual claim about the repo is re-checked and reversed) + `as-of scoping` (the re-pin). The rule adoption itself = `license` on the note's record protocol.

**ARITHMETIC AUDIT (compiler-computed, on the timing claim):** GENH4 r3 landed 00:50:10; the three r2 commits at 01:00:35, 01:21:44, 01:35:30 — differences **10m25s, 31m34s, 45m20s** ✓, matching “10–45 minutes BEFORE all three r2 commits”. The adjudication at 00:24:06 precedes all four ✓.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1795–1808. correction sites: `[r3]` in situ 1798–1803; §S13's PE3-G1 item at 1870–1893 (`.112`).

**TEETH:** **`stale self-description`** — the record's own claim about the repo was falsified by the repo. **PIN VERIFICATION:** `fd35416` ✓, `5279a11` ✓, `4b0d946` ✓, `dff23f8` ✓, `2abf419` ✓, `ad6f31d` ✓, `52fb6ff` ✓, `3b88321` ✓.

---
### EFF.GENIND.108  [changes-record]

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

**RESOLUTION TRACE:** statement lines 1809–1817. correction sites: `[r5 sweep]` in situ 1815–1817; `.133`.

**TEETH:** `arithmetic recount` of a grep's hit set — the species the standing rule (`.128`) exists to enforce.

XREF: `lean/notes/openmath/GENH4_PROOF_2026-08-08.md:GENH4-CAP(F)` — count **11**.

---
### EFF.GENIND.109  [run-record]

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

**CONDITIONALITY:** The grade line is a **round-dated record**, correct as of r2 — the acceptance record says so explicitly for the whole series (`.146`): “(The per-round grade closes … are round-dated records, correct as of their rounds; this append is the current state.)” **So the five grade closes are NOT stale-self-descriptions: the note pre-emptively scopes them.** A rare and worth-copying move.

**ARITHMETIC AUDIT:** the three fibration row totals restated here are identical to shard 1 `.40`'s ✓; the headline 2,128,163 is the same non-reconstructible total recorded at shard 1's defect 4. `38/40 + 40/40` matches shard 1 `.40` ✓.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1819–1831. correction sites: none; scoped by 2540–2543 (`.146`).

**TEETH:** as shard 1 `.40`/`.41`.

---
### EFF.GENIND.110  [changes-record] · **SERIES REPAIR-ARC, entry 2 of 5**

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
### EFF.GENIND.111  [changes-record]

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

**ARITHMETIC AUDIT:** the four enumerated correction sites are all verifiable in shard 1 (`.98` statement, `.108` echo, `.108` proof gloss, `.112` M6 ledger) ✓. TWOCHILD windows N−4 / N−6 re-derived at shard 1 `.27` ✓.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1846–1869. correction sites: `[r4]` in situ 1865–1869; §S14's PE4-G2/PE4-G1 items (`.119`, `.120`) and claim group C4 (`.123`).

**TEETH:** PE3's fresh leg (foreign-note evidence, exhaustive at two rows).

---
### EFF.GENIND.112  [changes-record] · **SERIES RECORD-INTEGRITY, entry 2 of 5**

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

**CONDITIONALITY:** **The closing sentence (“no adjudicated unrepaired finding sits at the r3 pin as of this commit”) is a commit-time claim that later becomes false** — the Codex GENH4 ratification adjudicated CHALLENGE at 5c8d2fd, and the note handles it exactly as its own rule prescribes: disclose at the NEXT dated append (`.92` entry 3), not by editing this record.

**SUPERSESSION KIND:** `counter re-reading` (of the r2 sentence) + `as-of scoping` (re-pin at four enumerated sites) + `license` (the commit-time restatement of the standing rule).

**DERIVATION:** Not a mathematical unit. **PIN VERIFICATION:** all eight cited commits resolve ✓ (`4b0d946`, `2abf419`, `ad6f31d`, `52fb6ff`, `3b88321`, `435a473`, `fd35416`, `e15308d`).

**RESOLUTION TRACE:** statement lines 1870–1893. correction sites: none in place; superseded-by-disclosure at 1562–1578 (`.92` entry 3).

**TEETH:** `in-house hostile pass` — the finding is a git-log check no battery row performs.

---
### EFF.GENIND.113  [changes-record]

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
### EFF.GENIND.114  [changes-record]

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
### EFF.GENIND.115  [changes-record]

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
### EFF.GENIND.116  [changes-record]

**CANONICAL STATEMENT:** FORM: bulleted display (§S13's PE3-m4 — bookkeeping). verbatim, lines 1910–1913.

> “* **PE3-m4 → bookkeeping.** S9.3's conditionality stack gains the
>   GENHN @ 850e77e and GENH4 @ r3 consumption bullets (present inline
>   since r1/r2, absent from the roster); S6 Step 3 gains the mixed-σ
>   wiring through GENIND-6(d) (Steps 2/4 already carried it).”

**CONDITIONALITY:** Landed; lands on `.91`, `.92` and shard 1 `.56`. **A pure inventory defect: two suppliers consumed for two rounds without appearing in the conditionality stack.** The same class recurs at PE7-m2 (four sites → seven) and at PE6-G1 (the whole stack stale).

**SUPERSESSION KIND:** `inventory completion` ×2.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1910–1913. correction sites: applied in place at 1535–1550 (`.91`), 1551–1553 (`.92` entry 1), 1024–1025 (shard 1 `.56`).

**TEETH:** NONE — an inventory repair. Disposition: `in-house hostile pass`.

---
### EFF.GENIND.117  [changes-record]

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

**RESOLUTION TRACE:** statement lines 1915–1928. correction sites: `[r4]` in situ 1918–1925; §S14 C5 (`.123`).

**TEETH:** PE4's FR-1 (foreign-note evidence, exhaustive on both cells).

**PIN VERIFICATION:** `51bd1bc` ✓.

---
### EFF.GENIND.118  [changes-record] · **SERIES REPAIR-ARC, entry 3 of 5**

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

**ARITHMETIC AUDIT:** the sweep declares **6** leg-1 grep targets (`"M_l"`, `"window"`, `"N −"`, `"window-(N"`, `"W − D"`, `"min_j"`) ✓ six enumerated; **9** leg-2 targets (enumerated at `.123`'s header: `"every sealed"`, `"all sealed"`, `"true at every"`, `"invisible"`, `"first live"`, `"first visible"`, `"beyond every"`, `"never"`, `"no prior"`) ✓ nine enumerated; **15** site classes and **14** claim groups, both counted at `.122`/`.125`. **The witness's escape is arithmetically explicable:** the missed phrase is hyphenated `first-visible`, and the pattern list contains the unhyphenated `"first visible"` — a fixed-string grep for `first visible` does **not** match `first-visible` ✓. **The defect is a direct consequence of the pattern set, exactly as the note says.**

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1930–1970. correction sites: `[r5]` in situ 1939–1946 and 1967–1969; §S15's PE5-G1 and BONUS items (`.129`, `.132`).

**TEETH:** `decorrelated-model audit` — PE5's witness is a sentence that r4's own method structurally could not see. **PIN VERIFICATION:** `ade9bac` ✓, `51bd1bc` ✓, `b94c9af` ✓; PE4's leg files EXIST ✓; the 13 md5s named here and at `.134` are the note's own enumerated freeze set.

---
### EFF.GENIND.119  [changes-record]

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
### EFF.GENIND.120  [changes-record] · **SERIES RECORD-INTEGRITY, entry 3 of 5**

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

**CONDITIONALITY:** **Five corrections, each quoting its false original in place** — the note's own discipline, stated as a count. All five land in shard 1 (`.98`'s bracket, `.101`'s TWOCHILD parenthetical, `.102`'s concordance) and in this shard (`.111`, `.117`).

**SUPERSESSION KIND:** `counter re-reading` ×5 (a regime inventory recounted at five sites; the conclusion preserved at all five).

**ARITHMETIC AUDIT:** all six PSTEEP figures re-derived at shard 1 `.28` ✓ (windows 2 vs 1 and 2 vs 1; loci 32 and 512; fibrations 4×8 and 8×64; splits 16/16 and 256/256, summing to 32 and 512 ✓).

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1999–2014. correction sites: the five in-place corrections at 363–367, 469–476, 484–487 (shard 1) and 1865–1869, 1918–1925 (this shard).

**TEETH:** PE4 FR-1 (foreign-note evidence, exhaustive) + `arithmetic recount`.

---
### EFF.GENIND.121  [table]

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
| 1 | “Header [r3]/[r4] arc lines — record” | CAPPED ✓ | `.75` (shard 1) |
| 2 | “S1 GENIND.A(II) "same (m, d) system at window N − mk"” | α-CORRECT ✓ | `.83` |
| 3 | “S3 LEMMA GENIND-2(a)(b) statement + proof (σ_k windows, ghost zones {≥ N − jk}, window condition mμ ≤ N−1)” | α-CORRECT ✓ | `.95`, `.96` |
| 4 | “S4.1 LEMMA GENIND-3 STATEMENT” | CAPPED `[r3]` ✓ | `.98` |
| 5 | “S4.1 GENIND-3 proof step (1)” — “WAS the pre-cap "N − m·k_l" + false reduction parenthetical” | **DEFECTIVE → FIXED** `[r4, PE4-G2]` | `.98` |
| 6 | “S4.1 [r3] honesty note (root-sum derivation; TWOCHILD N−4/N−6; PSTEEP capped windows)” | CAPPED ✓ | `.101`, `.102` |
| 7 | “S4.3 LEMMA GENIND-6(a) STATEMENT ("the SAME explicit window M_l = N − (μ_l k_l + Σ deg·min(own slope, k_l))")” | CAPPED `[r3]` ✓, with the VERBATIM-consumption check executed | `.108` |
| 8 | “S4.3 proof of (a) … its coprimality clause "blocks on other sides sit at their own slopes"” | CAPPED `[r3]` ✓ / clause **DEFECTIVE → FIXED** `[r4]` | `.108` |
| 9 | “S4.3 M6 worked ledger (D = min_j(v(a_j)+j) = 4, M = N−4, regime label "capped = uncapped at M6")” | CAPPED ✓, “hand-recheck min(4, 2+2, 6) = 4” | `.112` |
| 10 | “S4.3 honesty box (i) SS6 [r3, PE3-m2] ("child extraction at the capped window N−6")” | CAPPED ✓, “hand-recheck D = 2·1 + 4·min(3/2, 1) = 6 (uncapped would say 8)” | `.116` |
| 11 | “S5.2 drainage recursion u_{m,d}(N−mk) in the α-term” | α-CORRECT ✓ | `.119` |
| 12 | “S6 Step 2 / Step 4 / S7.1 (CS-1) rider” — “cite M_l / GENIND-6 abstractly, inheriting whatever S4.1/S4.3 display; every inherited display now CAPPED” | CAPPED (inherited) ✓ | `.129`, `.131`, `.137` |
| 13 | “S7.1–S7.4 stage windows (certified division-ledger windows, dv-units, ragged bands, GENIND-4 budgets, OB-a)” | AGNOSTIC ✓ | `.137`–`.148` |
| 14 | “S10 runner description ("β children by c = k scaling (D = weighted min) + monic Hensel extraction at window W − D")” | CAPPED ✓, “matches `extract_child` (md5 e7ca150b), which implements D = min_j(v(a_j) + j·k) literally” | `.95` (this shard) |
| 15 | “S13 [r3] PE3-G2 record (the capped formula + TWOCHILD windows)” | CAPPED ✓ (“its two regime sentences were PE4-G1, fixed”) | `.111` (this shard) |

**CONDITIONALITY:** **Pattern-scoped, and the note says so twice** — the header's `[r5 sweep]` rescope replaced “every display or consumption site listed” with the executed six patterns, citing PE5's independent miss-hunt as corroboration (“no window-formula site outside these 15 classes”) rather than as its own claim.

**SUPERSESSION KIND:** `[r5 sweep]` = `counter re-reading` (a universal coverage claim rescoped to an enumerated pattern set, with foreign corroboration cited not claimed).

**ARITHMETIC AUDIT (compiler-computed, rule 22):** the fifteen classes partition as CAPPED (1, 4, 6, 7, 8, 9, 10, 12, 14, 15 = **10**) + α-CORRECT (2, 3, 11 = **3**) + AGNOSTIC (13 = **1**) + DEFECTIVE→FIXED (5 = **1**), total 15 ✓. **But the note's own count line (`.122`) reads “11 capped/correct as found, 2 agnostic (stage mechanisms), 2 DEFECTIVE (sites 5, 8)”** — a different partition, because it counts sites 3 and 11 within “capped/correct” and counts class 8 as defective (its coprimality clause was) while this compiler's table records class 8's *window* verdict as CAPPED. **Reconciled:** the note's 11 = CAPPED-as-found (1, 4, 6, 7, 9, 10, 12, 14, 15 = 9) + α-CORRECT (2, 3, 11 = 3) = 12, minus class 8 which it moves to the defective column = **11** ✓; its 2 agnostic = class 13 plus, evidently, one of the α-CORRECT/AGNOSTIC boundary calls. **The two partitions agree on the total (15) and on which sites were FIXED (5 and 8); they disagree by one on the agnostic/correct boundary.** Recorded as an itemization difference, NOT a defect — the note's own count line is the authority for its own classification, and no site is unaccounted for in either reading.

**DERIVATION:** Not a mathematical unit; a grep-scoped audit inventory.

**RESOLUTION TRACE:** statement lines 2016–2067. correction sites: `[r5 sweep]` in situ 2019–2021; `.133`'s rewrite (1).

**TEETH:** `arithmetic recount` + `in-house hostile pass`; the corroboration for outside-pattern coverage is **foreign-note evidence** (PE5's miss-hunt), explicitly cited not claimed.

---
### EFF.GENIND.122  [changes-record]

**CANONICAL STATEMENT:** FORM: bold display (§S14 leg 1's count line), carrying an `[r5 sweep]` rescope. verbatim, lines 2069–2075.

> “**Count: 15 site classes; 11 capped/correct as found, 2 agnostic
> (stage mechanisms), 2 DEFECTIVE (sites 5, 8) — both fixed at [r4].
> Uncapped survivors among these 15 site classes: NONE [r5 sweep:
> was "after this sweep: NONE" — scoped to the enumerated classes;
> corroboration outside the patterns is PE5's independent sweep
> ("no window-formula site outside S14's 15 classes"), a verifier
> artifact, cited not claimed].**”

**ARITHMETIC AUDIT (compiler-computed, rule 22):** `11 + 2 + 2 = 15` ✓ — the note's own partition is internally consistent. Cross-check against the compiler's independent classification at `.121`: same total, same fixed set {5, 8}, one-site disagreement on the agnostic/correct boundary. **Both partitions leave zero sites unaccounted for.**

**CONDITIONALITY:** The “NONE” is scoped twice over: to the 15 enumerated classes, and with outside-pattern corroboration attributed to a verifier artifact.

**SUPERSESSION KIND:** `counter re-reading` (universal → enumerated).

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2069–2075. correction sites: `.133`'s rewrite (2).

**TEETH:** `arithmetic recount`.

---
### EFF.GENIND.123  [table]

**CANONICAL STATEMENT:** FORM: bold-headed bulleted display (§S14 sweep leg 2 — the record-claim audit, claim groups C1–C13; **C14 is emitted separately at `.124`** because it alone was later found FALSE and corrected in place, and the two quotations' union is the whole leg minus nothing). Header quoted verbatim, lines 2077–2080; the thirteen groups transcribed as a `[TABLE]` with verdicts quoted from lines 2082–2128.

> “**THE RECORD-CLAIM AUDIT (sweep leg 2; grep targets "every sealed",
> "all sealed", "true at every", "invisible", "first live", "first
> visible", "beyond every", "never", "no prior" — every hit checked
> against the repo/artifacts BEFORE being kept; verdicts listed).**”

`[TABLE]` — claim groups C1–C13, verdicts quoted:

| Group | Claim (quoted) | Verdict | Evidence (quoted) | Target unit |
|---|---|---|---|---|
| C1 | S4.1 bracket “(true at every sealed instance)” | **FALSE → FIXED [r4]** | “sealed ROWS[3] ∋ (2,5), ROWS[4] ∋ (2,6) (runner source, md5 e7ca150b); PSTEEP3/PSTEEP4 live there (v(a₀) = 4 ≤ 4 resp. 5 ≤ 5); PE4 FR-1 exhaustive (32 + 512 states)” | s1 `.98` |
| C2 | S4.1 TWOCHILD “beyond every sealed window — why three passes … could not see it” | **HALF-TRUE → RESCOPED [r4]** | “The GENRE (first visible N = 7) is beyond every sealed full-sweep window (max N = 6) … the inference (regime invisible to the battery) was FALSE” | s1 `.101` |
| C3 | S4.1 concordance “at every sealed instance (all in the agreeing regime …)” | **FALSE → FIXED [r4]** | evidence as C1 | s1 `.102` |
| C4 | S13 “invisible at n ≤ 6 first-visible windows” | **FALSE → FIXED [r4]** | “the disagreeing regime is first visible at N = 5, n = 3 (PSTEEP3), inside the sealed roster” | `.111` |
| C5 | S13 “every sealed genre sits in the agreeing regime” | **FALSE → FIXED [r4]** | evidence as C1 | `.117` |
| C6 | “mixed genres first live at n = 6” (S4.3 scope note, S6 Step 2, S12) | **TRUE, KEPT** | “the degree budget (child ≥ 2 abscissas + composite block ≥ 4, S4.3) + the machine instance M6 at n = 6” | s1 `.103`, `.105` |
| C7 | S4.3 honesty box [r3, PE3-m2]: stage-steeper live at n = 6 first visible N ≥ 9; ≥ 2 stage blocks degree-deep | **TRUE, KEPT** | “SS6 hull v(a₀) = 8 ⟹ N ≥ 9; PE3 FR-C machine instance at (2,9)/(3,9); abscissa budget 2·4 = 8” | s1 `.116` |
| C8 | S5.3 “CS5-V4E2 first visible at N = 8” | **TRUE, KEPT** | “v₀ = v₄ + 2h ≥ 1 + 2·(2v₄+1)\|_{v₄=1} = 7 ⟹ N ≥ 8; corroborated by S11 P-3 (V4E2 ABSENT …)” | s1 `.125` |
| C9 | S5.3 “CS5-V1E1-(2²) first visible N = 7” | **TRUE, KEPT** | “(headroom 5k+1 ≤ N−1 at k = 1)” | s1 `.126` |
| C10 | S5.1 “the n ≤ 3 program never consulted [W12-H]” | **TRUE, KEPT** | “the composite-free theorem (S5.1) + GT-CRIT zero CS events on all four n = 3 rows (S11 P-8)” | s1 `.85`, `.117` |
| C11 | GENIND-BOX-3 “the arguments never use d = 1” | **KEPT with its hedge** | “a proof-audit claim, already disclosed in the same box as machine-uncorroborated …; PE4 §2 left it as disclosed” | `.77`, s1 `.97` |
| C12 | S11 “Every never-measured spot EXACT” | **KEPT** | “re-verified by PE4's isolated re-run of the sealed battery (163,536/0, leaf-diff = elapsed only)” | `.103` |
| C13 | “The mathematical "never" claims (GENIND-1(iii) no-re-merge, GENIND-2(a) ghost non-contamination, GENIND-6(a)/(b) factor-genericity and no-re-merge, the S4.3 instrument lesson)” | **KEPT** | “lemma content or normative, machine-corroborated pointwise (GT-ALPHA/GT-BETA, supp, PE3/PE4 fresh legs), attacked across PE1–PE4 and held” | s1 `.93`, `.95`, `.108`, `.109`, `.115` |

**CONDITIONALITY:** Pattern-scoped (nine targets). **C12's evidence is an independent re-run of the frozen battery** — the only place in the note where §S11's numbers are re-produced rather than cited. **C13 is the row that separates lemma content from record content**, and it is why the standing rule at `.128` can ban universal quantification in RECORDS without touching theorems.

**ARITHMETIC AUDIT (compiler-computed, rule 22):** the C1 evidence line's liveness checks re-derived — PSTEEP3 at (2,5): `v(a₀) = 4 ≤ N−1 = 4` ✓; PSTEEP4 at (2,6): `v(a₀) = 5 ≤ N−1 = 5` ✓. C7's `2·4 = 8` ✓. C8's `1 + 2·3 = 7` ✓. C9's `5·1 + 1 = 6 ≤ N−1` ⟹ `N ≥ 7` ✓. **All five arithmetic evidence lines reproduce.** Verdict tally over C1–C13: FALSE→FIXED **4** (C1, C3, C4, C5), HALF-TRUE→RESCOPED **1** (C2), KEPT **8** (C6–C13) = 13 ✓.

**DERIVATION:** Not a mathematical unit; a grep-scoped claim audit.

**RESOLUTION TRACE:** statement lines 2077–2128. correction sites: none for C1–C13.

**TEETH:** `arithmetic recount` + `in-house hostile pass`; C12 additionally `executable regression` (an isolated re-run).

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:[W12-H]` — count **17**.

---
### EFF.GENIND.124  [changes-record] · **SERIES RECORD-INTEGRITY, entry 5's target**

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

**RESOLUTION TRACE:** statement lines 2129–2151. correction sites: `[r5 sweep]` and `[r6, PE6-G1]` in situ; replaced by 2346–2371 (`.136`, `.137`).

**TEETH:** `in-house hostile pass`; **no battery row can check a git-log claim** — the note's own five-defect series is the standing evidence.

---
### EFF.GENIND.125  [changes-record]

**CANONICAL STATEMENT:** FORM: bold display (§S14 leg 2's count line). verbatim, lines 2152–2153.

> “**Count: 14 claim groups audited; 4 FALSE → fixed (C1, C3, C4, C5),
> 1 half-true → rescoped (C2), 9 verified and kept (C6–C14).**”

**ARITHMETIC AUDIT (compiler-computed, rule 22):** `4 + 1 + 9 = 14` ✓ internally consistent. **But the “9 verified and kept (C6–C14)” is FALSIFIED by the `[r6]` correction at `.124`: C14 was NOT verified — its close was false at five suppliers.** The corrected tally is therefore **4 + 1 + 8 kept + 1 later-refuted = 14** ✓. The count line is not edited (it sits in the frozen body); the `[r6]` layer inside C14 carries the correction. **Tagged `STALE-SELF-DESCRIPTION` (rule 26)** — a count sentence that its own later correction falsifies, preserved unedited.

**CONDITIONALITY:** As above.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2152–2153. correction sites: none in place; falsified by 2134–2151 (`.124`).

**TEETH:** `arithmetic recount` — the recount is what exposes the stale tally.

---
### EFF.GENIND.126  [changes-record]

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

**CONDITIONALITY:** **A round-by-round self-narration that explicitly anticipates its own successor's finding** (“what r4 may itself have missed is PE5's to find, with this inventory as its checklist”) — and PE5 duly found one outside the checklist's pattern scope. **The grade-arc sentence is stale at acceptance** (0/2 → 2/2), scoped by `.146`'s round-dated-records clause.

**SUPERSESSION KIND:** `[r5 sweep]` = `counter re-reading` (rewrite (4) of `.133`'s seven).

**ARITHMETIC AUDIT:** the four repair-story entries (r1…r4) and the four records named (header arc line, S12, S13, S14) ✓ consistent; the three grade lines cited (S12, S13, S14) ✓ — S15 and S16 add two more, making **five** grade lines in the finished note, so this sentence's inventory is complete as of r4 and incomplete thereafter. Recorded, not corrected.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2155–2174. correction sites: `[r5 sweep]` in situ 2169–2170.

**TEETH:** `in-house hostile pass` + `arithmetic recount`.

---
### EFF.GENIND.127  [changes-record]

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

**CONDITIONALITY:** The corrected close is itself later undermined at one point: “(claim groups C1–C14 above) now say only what the repo can verify” — **C14 did not** (`.124`). Neither `[r5]` nor `[r6]` edits this sentence; `[r6]`'s correction lives inside C14. Tagged `STALE-SELF-DESCRIPTION` on the C14 clause.

**SUPERSESSION KIND:** `[r5, PE5-G1]` = `replacement` (a universal sentence replaced by a pattern-scoped one, original quoted) + `license` (the standing rule adopted).

**ARITHMETIC AUDIT:** “all eight md5 pins” — the Arc paragraph lists `e7ca150b` (1) + the r2 supp triple (3) + PE3's fresh triple (3) + PE4's fresh triple (3) = **10**, not 8. Reading “eight” as the frozen-before-this-round set (1 + 3 + 3 = 7) or as excluding PE4's own leg (1 + 3 + 3 = 7) does not give 8 either. **Recorded as an unreconciled count (§8, defect 5)** — the enumerated list in the Arc paragraph is the authority and is complete; only the summary numeral is unaccounted for. §S15's own byte-freeze line (`.134`) counts **13** md5s and §S16's (`.142`) counts **16**, both with explicit enumerations that DO reconcile (audited there), so the defect is local to this sentence.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2176–2192. correction sites: `[r5]` in situ 2183–2189.

**TEETH:** `decorrelated-model audit` (PE5's out-of-pattern witness) + `arithmetic recount`.

---
### EFF.GENIND.128  [changes-record] · **SERIES REPAIR-ARC, entry 4 of 5**

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
### EFF.GENIND.129  [changes-record] · **SERIES RECORD-INTEGRITY, entry 4 of 5**

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
### EFF.GENIND.130  [changes-record]

**CANONICAL STATEMENT:** FORM: bulleted display (§S15's PE5-m1). verbatim, lines 2248–2249.

> “* **PE5-m1 → rides the PE5-G1 fix** (the S4.3 display itself; same
>   edit, quoted original preserved in the [r5] bracket).”

**CONDITIONALITY:** A pointer item: the MINOR and the GAP have the same repair. Recorded as its own unit because the note numbers it separately and because a merge counting findings must not double-count the edit.

**SUPERSESSION KIND:** none of its own — it rides `.129`'s.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2248–2249. correction sites: none.

**TEETH:** as `.129`.

---
### EFF.GENIND.131  [changes-record]

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
### EFF.GENIND.132  [changes-record]

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
### EFF.GENIND.133  [changes-record]

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

**CONDITIONALITY:** **Rewrite (3) is the one that did not work** — it rescoped C14's quantifier while leaving its falsehood intact, and `[r6]` had to replace the sentence entirely (`.124`). The sweep's own kept-list is sound: every kept quantifier ranges over an enumerated or artifact-pinned set.

**SUPERSESSION KIND:** `counter re-reading` ×7 (each rewrite scopes a universal to an enumeration), applied at seven enumerated sites.

**ARITHMETIC AUDIT (compiler-computed, rule 22):** the sweep lists **five** numbered rewrites plus “the two PE5-G1-charged S14 sentences above” = **7 rewrites total** ✓ internally consistent. Cross-check: the two PE5-G1 sentences are the Arc ¶ and the closing ¶ of §S14 ✓ (`.118`, `.127`), and the five numbered ones land at `.121`, `.122`, `.124`, `.126`, `.108` ✓ — **all seven targets are units of this shard, none unaccounted for.** Note the kept-list's first item quotes “all eight md5 pins … listed”, i.e. the very numeral this compiler could not reconcile at `.127` — **the sweep adjudicated the sentence rule-compliant on the strength of its enumeration, without recounting the numeral.** Recorded (§8, defect 5).

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2276–2301. correction sites: rewrite (3)'s target later replaced at 2134–2151 (`.124`).

**TEETH:** `arithmetic recount` + `in-house hostile pass`.

---
### EFF.GENIND.134  [changes-record]

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

**ARITHMETIC AUDIT (compiler-computed, rule 22):** `1 (runner) + 3 (r2 supp) + 3 (PE3) + 3 (PE4) + 3 (PE5) = 13` ✓ — **the enumeration reconciles exactly with the stated numeral**, unlike `.127`'s “eight”. This is the first round whose freeze count is fully checkable, and it is checkable *because* the standing rule forced the enumeration.

**CONDITIONALITY:** The as-of pins are commit-time claims; GENH4's moves again before r6 (`.92` entry 4).

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2303–2315. correction sites: none.

**TEETH:** `arithmetic recount` (13/13 reconciled) + commit-time md5 re-verification. **PIN VERIFICATION:** `850e77e` ✓, `b10a5a7` ✓, `5c8d2fd` ✓; all five artifact triples EXIST on disk ✓ (15 files).

---
### EFF.GENIND.135  [changes-record] · **SERIES REPAIR-ARC, entry 5 of 5; SERIES RECORD-INTEGRITY, entry 5 of 5**

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
### EFF.GENIND.136  [table]

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

**CONDITIONALITY:** **C14's replacement, and the arc's structural answer to the STALE PIN SET.** Its design principle is stated in the Arc (`.135`): “rows with evidence, no summary sentence, per the standing rule”. **Row 6 creates an obligation** (“execution disclosure owed at the next dated append”), discharged in shard 3. **Row 7's verdict rests on a supplier whose annex stack is 0/2 with pass #2 unlanded** — the weakest row, and the note says so in-row.

**SUPERSESSION KIND:** `replacement` (of C14's close) — the table IS the supersession, and its format (no summary sentence) is itself the remedy.

**ARITHMETIC AUDIT (compiler-computed, rule 22):** **eight rows** ✓; of these, **six suppliers moved** (rows 1, 2, 3, 4, 5, 7), **one did not** (row 6), **one was never pinned** (row 8) — 6 + 1 + 1 = 8 ✓. Against C14's refuted close, which claimed “none moved” of nine enumerated suppliers and was FALSE at **five** (`.124`): the five named there (W-12, HEX3, HMENU3, W-11, QSCOUT22) are rows 1–5 here ✓, and rows 6–8 were outside C14's enumeration (GENHN and GENH4 were handled separately in C14; HE7 was never in the stack) ✓ — **the two counts reconcile exactly.** Coverage: 8 table rows + 4 unmoved-list entries (`.137`) = **12 supplier positions**, against §S9.3's 11 bullets (`.83`–`.93`); the extra position is HE7, which has no S9.3 bullet ✓, and `.89`'s compound bullet expands to three entries in the unmoved list ✓ — **11 bullets − 1 compound + 3 expanded + 1 HE7 = 14 named suppliers across 12 positions**, all accounted for.
**PIN VERIFICATION:** every hash in the table resolves as a commit ✓ — `99f1813`, `be4a1dc`, `ee17210`, `b17238a`, `d2d91b7`, `5728258`, `2580f12`, `b6a1d69`, `a707430`, `64d3ff9`, `625fa49`, `050425d`, `19c0285`, `839b735`, `35e6545`, `31506b3`, `240a56c`, `dd67cda`, `fcaf268`, `850e77e`, `4b0d946`, `b10a5a7`, `a8dec16`, `fed3cff`, `760d20f`, `ca3754d`, `f7f45f1` (**27/27**). `ce6f4116` is an md5, not a commit.

**DERIVATION:** Not a mathematical unit; the consumption-survival ledger.

**RESOLUTION TRACE:** statement lines 2346–2361. correction sites: 2479–2487 (PE7-m1 corrects row 1's grep claim), 2488–2498 (PE7-m2 completes row 6's inventory), 2499–2506 (PE7-m3 corrects row 1's `[GENHN-HE]` locality), 3032–3094 (the supplier-movement record discharges row 6's owed disclosure, shard 3).

**TEETH:** `transfer audit` ×8 — a clause-by-clause survival check across each supplier's repair arc, of a kind no battery row performs. Two rows (1, 7) are additionally re-verified from the supplier TEXTS at `.138`/`.139`; the remaining six cite PE6's traces (`foreign-note evidence`), and the table says which is which.

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:HEX3-BOX-1` — count **11** (row 2's conditionalizing lemma; ledger **HYP.137**, see `.85`).
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:W-12.B` — count **19**.

---
### EFF.GENIND.137  [changes-record]

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
### EFF.GENIND.138  [changes-record]

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

**CONDITIONALITY:** **A verbatim two-sided text match — the strongest form of consumption verification in the corpus, and the note distinguishes it from citation explicitly** (“not inherited from PE6's traces”). Two riders land on it from the post-PE7 corrections: PE7-m3 corrects the `[GENHN-HE(μ ≥ 3)]` locality (`.145`), and PE7-m1 corrects the neighbouring S3.2 grep claim (`.143`). **The one open edge is the STRENGTHENED (A1)**: more is demanded of P(n), and this note does not re-derive its own (A1)-closure lemma under the strengthened predicate — shard 1's OPEN-CALL 3, re-raised here.

**ARITHMETIC AUDIT:** “all four conclusion clauses, one for one” — the supplier's four are (i) convergence to one rational function in ℚ(q), (ii) equality with the N → ∞ decided-τ window mass AND the Haar density μ_τ, (iii) same expression at every prime power, both characteristics, wild included, (iv) Σ_τ R_τ = 1; the use-site's four are “one R_τ(q) ∈ ℚ(q) per splitting type”, “= the Haar density”, “same expression at every prime power and characteristic”, “Σ_τ R_τ = 1” ✓ — **four for four, matched.** The hypothesis triple (A0)/(A1)/(A2) matches ✓.

**DERIVATION:** Not a mathematical unit; a text-match verification.

**RESOLUTION TRACE:** statement lines 2373–2399. correction sites: 2479–2487 and 2499–2506 (PE7-m1, PE7-m3).

**TEETH:** `transfer audit` at verbatim granularity — the gold standard row of this shard's teeth table.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:THEOREM W-12.D` — count **5**; `σ-LABELING` — count **7**.
XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN.C` — count **19**.
XREF: `lean/notes/openmath/GENH4_PROOF_2026-08-08.md:GENH4.C` — count **11**.
XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:HM3.C` — count **15**.
**NEAR-MISS:** `[GENHN-HE(μ ≥ 3)]` — count **0** in GENHN; the note's own PE7-m3 correction supplies the reading (`.145`). `W-11(i)/(iii)` — clause labels, count **0** as written in W11 (which uses bare `(i)`/`(iii)`); verified parent `THEOREM W-11` count **3**.

---
### EFF.GENIND.139  [changes-record]

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

**CONDITIONALITY:** **The n = 4 de facto discharge of (CS-EXACT), verified at verbatim granularity against a byte-frozen accepted body.** Note the supplier's own header phrase “the σ-undecided (conservative) count is ONE exact q-power” — which GENIND consumes WITH the two-term caveat, exactly the granularity correction PE2-m1 made (`.108`). **The supplier's own coarse phrase and its own two-term display coexist in the quoted text**, and GENIND's use-site is the one that reconciles them.

**ARITHMETIC AUDIT (compiler-computed):** genre F's law `q^{2⌊N/2⌋+2k−1} + 1_{2|N}·(q−1)·q^{N+2k−1}` is **one term at odd N** (the indicator vanishes) and **two at even N** ✓ — matching “a single q-power off the boundary band; a TWO-term q-power sum at genre-F even N” exactly. At even N, `2⌊N/2⌋ = N`, so the two terms are `q^{N+2k−1}` and `(q−1)q^{N+2k−1}`, summing to `q^{N+2k}` — **a single q-power after all**, at even N. Recorded as an observation, not a correction: the note's “TWO-term q-power sum” is faithful to the *displayed form*, and the (CS-EXACT) requirement (“a FINITE SUM of q-powers”) is satisfied either way ✓.

**DERIVATION:** Not a mathematical unit; a text-match verification.

**RESOLUTION TRACE:** statement lines 2401–2421. correction sites: none.

**TEETH:** `transfer audit` at verbatim granularity + a `git show`-level byte check.

XREF: `lean/notes/openmath/GENH4_PROOF_2026-08-08.md:THEOREM GENH4.B` — count **6**; `Q22-L3` — count **3**; `GENH4-CAP(F)` — count **11**.

---
### EFF.GENIND.140  [changes-record]

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

**CONDITIONALITY:** **The note is explicit that these five are CITED, not re-verified here** — the division between `.138`/`.139` (re-verified from supplier texts) and this unit (cited from a verifier's traces) is the honest core of §S16's evidence hierarchy. Trace (ii) is the claim PE7-m1 later re-words (`.143`); trace (v) is a rare *defence* of an existing universal sentence on the ground that it ranges over an artifact-pinned set.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2423–2432. correction sites: 2479–2487 (PE7-m1 on trace (ii)'s sibling claim).

**TEETH:** `foreign-note evidence` ×5, explicitly labelled as such.

---
### EFF.GENIND.141  [changes-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (§S16's PE6-m1 disposition). verbatim, lines 2434–2438.

> “**PE6-m1 disposition:** the three stale arc parentheticals (W-12
> "PE3 owed"; HMENU3 "r1 owed"; W-11 "counter 1/2") each received an
> [r6] dated append at their S9.3 bullets — originals preserved in
> place as dated records, per the note's convention (previously
> executed three times on the GENH4 bullet).”

**CONDITIONALITY:** Three `STALE-SELF-DESCRIPTION` items cured by dated append rather than edit. **The parenthetical “(previously executed three times on the GENH4 bullet)” is the note's own recognition of SERIES GENH4-PIN** — three appends at r3/r4/r5, with r6 making four (`.92`).

**SUPERSESSION KIND:** `as-of scoping` ×3, executed by append.

**ARITHMETIC AUDIT:** three stale parentheticals ✓ (W-12 `.83`, HMENU3 `.86`, W-11 `.84`); “previously executed three times on the GENH4 bullet” ✓ = `[r3]`, `[r4]`, `[r5]` (the `[r6]` append is this same round's, making four in total).

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2434–2438. correction sites: applied at 1470–1482, 1508–1517, 1485–1490 (`.83`, `.86`, `.84`).

**TEETH:** `in-house hostile pass`.

---
### EFF.GENIND.142  [changes-record]

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

**ARITHMETIC AUDIT (compiler-computed, rule 22):** `1 (runner) + 3 + 3 + 3 + 3 + 3 = 16` ✓ — the enumeration reconciles with the stated numeral exactly (as at `.134`'s 13, and unlike `.127`'s “eight”). The GT-PIN five are enumerated as five ✓. The as-of list names **eight** supplier HEADs ✓ = the eight rows of `.136` ✓. The repo-movement list names four TAMEKQX commits, corrected to five by the photo-finish ✓.
**PIN VERIFICATION:** `ee17210` ✓, `b6a1d69` ✓, `19c0285` ✓, `35e6545` ✓, `fcaf268` ✓, `850e77e` ✓, `760d20f` ✓, `ca3754d` ✓, `26d2dbf` ✓, `209ed18` ✓, `fa58556` ✓, `f3c6eef` ✓, `b99daa7` ✓, `9b170f0` ✓, `760afed` ✓, `dcc20bb` ✓, `ad1bd98` ✓ — **17/17 commits resolve.** All six artifact triples (18 files) EXIST on disk ✓.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2440–2464. correction sites: none; the grade line is scoped by 2540–2543 (`.146`).

**TEETH:** `arithmetic recount` (16/16 and 5/5 reconciled) + `in-house hostile pass` (the photo-finish self-catch).

---
### EFF.GENIND.143  [changes-record] · **SERIES REPAIR-ARC, entry 6 (post-PE7 rider)**

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

**TARGETS:** `.83` (the S9.3 W-12 bullet) and `.136` (§S16 row 1).

**ARITHMETIC AUDIT (compiler-computed):** the four hit lines named (L1474, L1480, L2354, L2427) all lie inside this shard's range ✓ and correspond to: `.83`'s r6 append (L1474 and L1480), `.136` row 1 (L2354), and `.140` trace (ii) (L2427) ✓ — **four for four, each identifiable as a disclosure sentence, none a consuming cite.** The claim's corrected form is therefore exactly right.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2468–2487. correction sites: none downstream.

**TEETH:** `arithmetic recount` (a grep re-executed and its hits classified).

**PIN VERIFICATION:** `380bc66` ✓, `993935d` ✓.

---
### EFF.GENIND.144  [changes-record]

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
### EFF.GENIND.145  [changes-record]

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

**TARGETS:** `.136` (row 1), `.138`; and, for the reading, shard 1 `.15`.

**ARITHMETIC AUDIT:** the two cited hit lines L2354 and L2397 fall in `.136` (row 1) and `.138` ✓ — two hits, both inside §S16 ✓. Compiler cross-check at the supplier: fixed-string `GENHN-HE` in `GENHN_PROOF_2026-08-08.md` = **0** ✓ — the box genuinely does not exist under that name at the supplier either.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2499–2506. correction sites: none downstream; carried at shard 1 `.15` and at `.62`/`.64` here.

**TEETH:** `arithmetic recount` (grep-based locality check).

---
### EFF.GENIND.146  [changes-record] · **SERIES REPAIR-ARC, TERMINAL entry**

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

**CONDITIONALITY:** **The single most important sentence for a chapter cut is the closing one: “the acceptance freezes the reduction and its record, not the box.”** ACCEPTED 2/2 is a *record* grade; [GENIND-H] at n ≥ 4 is open, and two further conjuncts enter at n ≥ 8 (shard 3). **Two of PE8's own route claims retire coverage holes the note's boxes still assert** — non-prime bases q ∈ {4, 8, 9} against GENIND-BOX-3's “prime q only”, and n = 10/n = 12 against the roster's max n = 5 — without editing the boxes (`.77`'s STALE-SELF-DESCRIPTION tag).

**SUPERSESSION KIND:** `counter re-reading` (the clean counter completes 1/2 → 2/2) + `license` (the text-freeze protocol changes: in-place rounds end, dated appends only).

**ARITHMETIC AUDIT (compiler-computed):** the 2-clean count: PE7 CLEAN (→ 1/2) + PE8 CLEAN (→ 2/2) ✓. Finding tallies across the full arc: PE1 3G+4m, PE2 2G+1m, PE3 2G+4m, PE4 2G+0m, PE5 1G+2m, PE6 1G+1m, PE7 0G+3m, PE8 0G+1m → **0 CRITICAL, 11 GAP, 16 MINOR over eight passes**, with GAPs monotone non-increasing 3,2,2,2,1,1,0,0 ✓ (audited also at `.79`). Body freeze: lines 1–2464 md5 `14fa6afc` == commit `993935d` ✓ — and note that **2464 < 2468**, the first line of the post-PE7 annex ✓, so “purely additive” checks structurally.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2510–2526 + 2545–2548. correction sites: none — this is the terminal record. Its own scoping clause for the five grade closes is at 2540–2543.

**TEETH:** `in-house hostile pass` ×8, two of them CLEAN. **PIN VERIFICATION:** `380bc66` ✓, `b653858` ✓, `3f5bafc` ✓, `993935d` ✓, `c3212cc` ✓. PE7's and PE8's committed legs `genind_pe7_fresh.*` (plus two extra run pairs) and `genind_pe8_fresh.*` all EXIST on disk ✓.

---
### EFF.GENIND.147  [changes-record]

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

**CONDITIONALITY:** **A supersession-by-append with an explicit non-target list** — the parenthetical scopes the cure so that the five per-round grade closes are NOT superseded but *dated*. **That distinction is the reason `.109`, `.117`, `.127`, `.134`, `.142`'s grade lines are not tagged STALE-SELF-DESCRIPTION while `.104`'s §S11 clauses ARE**: the cure covers the two arc-state lines and the grade closes are pre-scoped; §S11's “Attempt 0/2; the hostile arc has not begun” is **neither** covered nor pre-scoped (OPEN-CALL 3).

**SUPERSESSION KIND:** `counter re-reading` on two named frozen lines, executed by append because the body cannot be edited.

**TARGETS:** shard 1 `.01` (header arc line, L49–50) and `.79` (GENIND-BOX-5 arc close, L1414–1415). **Explicitly NOT targeted:** the five per-round grade closes (`.109`, `.117`, `.127`, `.134`, `.142`).

**ARITHMETIC AUDIT:** both quoted target lines fall inside the byte-frozen body (L49–50 and L1414–1415, both < 2464) ✓, so neither could be edited in place ✓ — the append mechanism is forced, exactly as stated.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2528–2543. correction sites: none.

**TEETH:** `in-house hostile pass`; the finding is a staleness scan of the frozen region.

---
### EFF.GENIND.148  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph (ANNEX R's provenance and scope). verbatim, lines 2552–2578.

> “## ANNEX R (2026-08-09, post-ratification; CODEX F1-F6)
>
> **Provenance and scope.** The ratification sweep's Codex leg
> (`CODEX_GENINDRAT_2026-08-09.md`, session
> 019fe5fe-39b0-7ff3-806d-4f578bcdb292, gpt-5.6-sol at HIGH, fresh
> context, read-only) returned **6 findings — RATIFICATION OUTCOME:
> CHALLENGE** at adjudication: F3 (CONFIRMED GAP, the heaviest — the
> vanishing rate consumed but not supplied by the displayed P(k)), F1
> (CONFIRMED GAP with disclosure overlap — GENIND-6(c)'s onto/constant-
> fiber missing its unit-pivot step), F2 (CONFIRMED GAP — the window-1
> scope leak), F4 (CONFIRMED, regraded MINOR at this note, GAP at the
> PE8 acceptance report — its §4.1 monotonicity display is false), F5
> (CONFIRMED, regraded MINOR display — the CS4-F floor), F6 (CONFIRMED,
> regraded MINOR wording — the stage-level reading of the converse).
> This annex executes the fold note's S4 repair queue R1–R6 in order.
> The accepted text above is BYTE-FROZEN: full file before this append
> = 158,427 bytes, md5 `eefcf6584bbb0917875e77c9fcab7a9e` (2,548
> lines), verified identical before and after; within it the
> PE8-verified body freeze (lines 1–2464 md5 `14fa6afc…`) was
> re-executed this round and matches. Machine support: the ADDITIVE leg
> `verification/openmath/genind_annexr_supp.py` + committed output
> (commit f5271e4; checks A–I, GREEN; py md5 `42fd603e…`, output md5
> `d938ad82…`); the sealed runner + artifacts are untouched (the runner
> is consulted READ-ONLY at its two CS4-F gate lines). Honesty of
> grade: this annex is a post-ratification append and has NOT itself
> been through a hostile pass; each repair below RE-DERIVES from the
> note's own lemmas and quotes the finding it cures.”

**CONDITIONALITY:** **The decisive fact for the whole DAG: a decorrelated model, reading a note that had just been ACCEPTED 2/2 by eight in-house hostile passes, returned six confirmed findings including three GAPs — one of them a consumed hypothesis component absent from the display.** The outcome is **CHALLENGE**, not refutation: no count law falls, and the acceptance is annotated rather than revoked. **Three of the six findings are regraded downward at this note and one is regraded UPWARD elsewhere** (F4 is “GAP at the PE8 acceptance report”), i.e. the heaviest consequence of F4 lands on a *verifier artifact*, not on the note.

**ARITHMETIC AUDIT (compiler-computed):** six findings, dispositions: 3 CONFIRMED GAP (F3, F1, F2) + 3 CONFIRMED-but-regraded MINOR (F4, F5, F6) = 6 ✓. Repair queue R1–R6 maps one-to-one onto F3, F1, F2, F5, F6, F4 respectively (R1↔F3, R2↔F1, R3↔F2, R4↔F5, R5↔F6, R6↔F4) ✓ — **the queue is ordered by severity, not by finding number**, which the section headings confirm.

**SUPERSESSION KIND:** none of its own (a provenance record). It establishes freeze predicates for the layer.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2552–2578. correction sites: 3098–3115 (ANNEX R — r1's provenance, which edits five sites inside this layer).

**TEETH:** machine leg `genind_annexr_supp.py` (checks A–I, GREEN), consulted read-only against the sealed runner. Disposition: **`decorrelated-model audit`** (rule 27) — the finding source is a different model in a fresh read-only context, and **none of the six findings could have been produced by any battery row**, since three are about undisplayed hypotheses, one about a toy counterexample shape the runner never executes, one about a display's missing side condition the runner already gated on, and one about a *report's* rationale.

**PIN VERIFICATION:** `f5271e4` ✓ commit; `verification/openmath/genind_annexr_supp.py` ✓ and `genind_annexr_supp_output.txt` ✓ EXIST; the fold note `lean/notes/openmath/CODEX_GENINDRAT_2026-08-09.md` ✓ EXISTS.

---
### EFF.GENIND.149  [supplier-finding]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph with two nested quotations (R1.0 — the defect stated exactly, quoting both the consuming sentence and the supplying package). verbatim, lines 2580–2604.

> “### R1 (CODEX F3, the heaviest): the vanishing rate — P(k)'s fourth member pinned to the rate-carrying species + the bounded/growing-M_l split displayed
>
> **R1.0 The defect, exactly.** S5.2's vanishing bullet consumes a rate:
>
> > "vanishing: u/Q^{m(N−1)} → 0 by induction (head Q^{−(N−1)};
> > α-terms geometric; β-terms lose at least one child's full mass by
> > the IH bound — each contributes O(poly(N)·Q^{−(N−c)}) relative
> > mass)"
>
> while THEOREM GENIND.B's displayed package supplies only
>
> > "P(k) := {… + exact-complement (A2)}"
>
> and W-12's (A2) is a bare o(1) (r(N)/q^{nN} → 0 — Codex's instance:
> 1/log(M+1) is o(1) with no exponential rate). Codex F3's two halves,
> both confirmed at adjudication: (i) "exact" supplies a VALUE, not a
> rate — the displayed fourth member does not carry the O(poly·Q^{−·})
> the bullet consumes; (ii) a capped child window M_l = N − D_l can
> stay BOUNDED while the genre depth D_l grows with N, and there the
> child's own M_l → ∞ vanishing cannot be applied — those β-terms
> vanish only through the route prefactor, and no bounded-vs-growing
> split was displayed. GENIND-BOX-4 priced the bookkeeping compression;
> the finding is sharper: a consumed HYPOTHESIS component absent from
> the display.”

**CONDITIONALITY:** **Type `supplier-finding` in the mirror sense of rule 13**: a defect report against the note's OWN frozen body, discharged here rather than at the (unreachable) source. Both halves are confirmed at adjudication. **Half (ii) is the mathematically substantive one** and is what forces GENIND-C1(iii)'s two-regime split; half (i) is a hypothesis-display gap.

**ARITHMETIC AUDIT (compiler-computed, on the counterexample shape):** Codex's instance `1/log(M+1)` is indeed `o(1)` with no exponential rate ✓ — and it is admissible as a *complement fraction* only if the note's (A2) is a bare limit, which W-12's is. **The gap is real as stated:** “exact closed form” constrains the VALUE and says nothing about decay in M. Half (ii)'s shape: with `M_l = N − D_l` and `D_l` growing with N, `M_l` can stay bounded ✓ (the note's own capped formula makes `D_l` genre-dependent and N-independent only when every slope is fixed; at a genre whose depth grows with the window, `M_l` is bounded) — and then the child's own asymptotic supplies nothing ✓.

**DERIVATION:** Not a mathematical unit; a defect report. Its repair is `.150`–`.154`.

**RESOLUTION TRACE:** statement lines 2580–2604. correction sites: none — this is the finding, not a claim.

**TEETH:** **`decorrelated-model audit`.** The note's own framing is the row's disposition: “GENIND-BOX-4 priced the bookkeeping compression; the finding is sharper: a consumed HYPOTHESIS component absent from the display.” **Eight in-house hostile passes did not find it**, and no battery row could have: the runner computes exact counts, and an exact count is silent about the *rate* its own asymptotics need.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:W12-BOX-1` — count **10** (the box family this finding sharpens is GENIND's own BOX-4, shard 2 `.78`).

---
### EFF.GENIND.150  [lemma]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph with two indented ASCII displays (R1.1 — the rate-carrying species grounded at m = 2). verbatim, lines 2606–2639.

> “**R1.1 The rate-carrying species, grounded at m = 2 (derivation
> displayed).** At m = 2 the recursion of S5.2 closes without β-terms:
> by GENIND-1's grammar a repeated linear e = 1 factor at m = 2 spans
> the whole polygon at integer slope — that is α — and the partition
> (1,1) is separable (DEC); no continuing child exists below degree
> 2·d, and m = 2 < 4 excludes CS (S5.1). So the first-step recursion
> degenerates to head + α:
>
>     u(N) = Q^{N−1} + Σ_{k ≥ 1, 2k ≤ N−1} (Q−1)·Q^k · u(N−2k),
>     u(1) = 1   (the window-1 boundary: R3's rider below),
>
> writing u := u_{2,d}, Q := q^d, c(2) = 1. Telescope (re-derived here,
> the W-11 R-recursion move): subtracting the k ↦ k+1 re-indexed sum,
>
>     u(N) = Q^{N−1} − Q^{N−2} + Q²·u(N−2)   (N ≥ 3),
>
> and iterating from u(1) = 1, u(2) = Q gives the CLOSED FORMS
>
>     u(2ℓ)   = ℓ·Q^{2ℓ−1} − (ℓ−1)·Q^{2ℓ−2},
>     u(2ℓ+1) = (ℓ+1)·Q^{2ℓ} − ℓ·Q^{2ℓ−1},
>
> equivalently u(M) = Q^{M−1} + ⌊(M−1)/2⌋·(Q−1)·Q^{M−2} — which is
> LETTER-FOR-LETTER the committed R(M) displayed inside THEOREM HEX3.A
> (the W-11 supply consumed there). Machine (leg A, B): the closed
> forms solve the recursion symbolically in Q at N = 2..14 and equal
> R(M) at M = 1..14. Rate (leg C): u(N) ≤ N·Q^{N−1}, i.e.
>
>     u(N)/Q^{2(N−1)} ≤ N·Q^{−(N−1)}
>
> at N = 2..14, Q ∈ {2,3,4,5,8,9} — coefficient POLYNOMIAL (degree 1)
> in the window, deficit LINEAR in the window. The n = 3 instance is
> already displayed at the supplier: THEOREM HEX3.A's exact law (a
> ⌊(N−1)/3⌋-term q-power sum with the same R(M) coefficients) with
> THEOREM HEX3.B's rate u ≤ N·q^{2N−2}, undecided/q^{3N} ≤ (1+N)q^{−N}.”

**CONDITIONALITY:** **Unconditional at m = 2, and the ground instance of the species (A2-RATE).** Its consumption of the window-1 boundary `u(1) = 1` is explicitly routed through R3's rider (`.160`) — the note wires its own two repairs together. **The `R(M)` identity is the decorrelation:** the closed form derived here is claimed LETTER-FOR-LETTER equal to a committed supplier display, and machine leg B checks that at M = 1..14.

**ARITHMETIC AUDIT (compiler-computed — every displayed step re-derived; this is the shard's most checkable unit):**
* **Telescope, re-derived in full.** Write `S(N) := Σ_{k≥1, 2k≤N−1} (Q−1)Q^k u(N−2k)`, so `u(N) = Q^{N−1} + S(N)`. Re-index `S(N)` at `j = k−1` on its `k ≥ 2` tail: `Σ_{k≥2}(Q−1)Q^k u(N−2k) = Q·Σ_{j≥1}(Q−1)Q^{j} u((N−2)−2j) = Q·S(N−2)` — the index ranges match, since `2k ≤ N−1, k ≥ 2` ⟺ `2j ≤ N−3, j ≥ 1` ✓. Hence `S(N) = (Q−1)Q·u(N−2) + Q·S(N−2)`, and substituting `S(N−2) = u(N−2) − Q^{N−3}` gives `u(N) = Q^{N−1} + (Q−1)Q·u(N−2) + Q·u(N−2) − Q^{N−2} = Q^{N−1} − Q^{N−2} + Q²·u(N−2)` ✓ — **the displayed telescoped recurrence, exactly.**
* **The closed forms satisfy it.** At `N = 2ℓ`: LHS `= ℓQ^{2ℓ−1} − (ℓ−1)Q^{2ℓ−2}`; RHS `= Q^{2ℓ−1} − Q^{2ℓ−2} + Q²[(ℓ−1)Q^{2ℓ−3} − (ℓ−2)Q^{2ℓ−4}] = ℓQ^{2ℓ−1} − (ℓ−1)Q^{2ℓ−2}` ✓. At `N = 2ℓ+1`: LHS `= (ℓ+1)Q^{2ℓ} − ℓQ^{2ℓ−1}`; RHS `= Q^{2ℓ} − Q^{2ℓ−1} + Q²[ℓQ^{2ℓ−2} − (ℓ−1)Q^{2ℓ−3}] = (ℓ+1)Q^{2ℓ} − ℓQ^{2ℓ−1}` ✓. **Both branches exact.**
* **Base cases.** `u(1) = 1`: from `u(2ℓ+1)` at `ℓ = 0` → `1·Q⁰ − 0 = 1` ✓. `u(2) = Q`: from `u(2ℓ)` at `ℓ = 1` → `1·Q¹ − 0 = Q` ✓.
* **The unified form.** `u(M) = Q^{M−1} + ⌊(M−1)/2⌋(Q−1)Q^{M−2}`. At `M = 2ℓ`: `⌊(2ℓ−1)/2⌋ = ℓ−1`, giving `Q^{2ℓ−1} + (ℓ−1)(Q−1)Q^{2ℓ−2} = Q^{2ℓ−1} + (ℓ−1)Q^{2ℓ−1} − (ℓ−1)Q^{2ℓ−2} = ℓQ^{2ℓ−1} − (ℓ−1)Q^{2ℓ−2}` ✓. At `M = 2ℓ+1`: `⌊2ℓ/2⌋ = ℓ`, giving `Q^{2ℓ} + ℓ(Q−1)Q^{2ℓ−1} = Q^{2ℓ} + ℓQ^{2ℓ} − ℓQ^{2ℓ−1} = (ℓ+1)Q^{2ℓ} − ℓQ^{2ℓ−1}` ✓. **The three displayed forms are one function.**
* **The rate.** `u(N) ≤ N·Q^{N−1}`: at `N = 2ℓ`, `u = ℓQ^{2ℓ−1} − (ℓ−1)Q^{2ℓ−2} ≤ ℓQ^{2ℓ−1} ≤ 2ℓ·Q^{2ℓ−1} = N·Q^{N−1}` ✓; at `N = 2ℓ+1`, `u ≤ (ℓ+1)Q^{2ℓ} ≤ (2ℓ+1)Q^{2ℓ}` for `ℓ ≥ 1` ✓ and at `ℓ = 0`, `1 ≤ 1·Q⁰` ✓. Dividing by `Q^{2(N−1)}` gives `u(N)/Q^{2(N−1)} ≤ N·Q^{−(N−1)}` ✓ — **the displayed rate, with (K, B, c) = (1, 1, 1)**, matching R1.1's own closing claim at `.153`.
* **Compiler verdict on this unit: every displayed step re-derives.** The telescope, both closed forms, the unified `⌊(M−1)/2⌋` form, both base cases and the rate bound were recomputed independently above and all agree with the source. **This is the most fully checkable unit in the three GENIND shards.**

**DERIVATION:** Displayed in the statement (recursion → telescope → closed forms → identity → rate). Justification tags: the recursion's shape = `by XREF GENIND-1`'s grammar + `by XREF S5.1` (m = 2 < 4 excludes CS); the telescope = `computation` (re-derived above, exact); the R(M) identity = `by XREF THEOREM HEX3.A` + machine leg B; the rate = `computation` + machine leg C.

**RESOLUTION TRACE:** statement lines 2606–2639. proof lines — displayed. correction sites: none; the closure sentence that FOLLOWS it is riddered at `.151`.

**TEETH:** machine legs A, B, C of `genind_annexr_supp.py` @ `f5271e4` (GREEN) — symbolic solution at N = 2..14, the R(M) equality at M = 1..14, and the rate at six values of Q. Disposition: **executable regression + `accepted-with-decorrelation-supplied`** (the R(M) tie is to a committed supplier display, not to this note's own machinery).

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:THEOREM HEX3.A` — count **11**; `THEOREM HEX3.B` — count **8**; `R(M)` — count **21**.
XREF: `lean/notes/openmath/W11_PROOF_2026-08-08.md:THEOREM W-11` — count **3**.

---
### EFF.GENIND.151  [hypothesis]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph + display (R1.1's species pin — the (A2-RATE) rider on P(k)'s fourth member) + the closure sentence, carrying an `[ar1 2026-08-10, GAP-1 repair]` rider. verbatim, lines 2641–2675.

> “**The species pin (the fourth member's rider).** Read P(k)'s fourth
> member "exact-complement (A2)" WITH the species the proved instances
> exhibit — for each consumed cluster system (μ, d) at window M:
>
> > **(A2-RATE)** the conservative complement u_{μ,d}(M) is an exact
> > finite sum of signed q-power terms whose term count and
> > coefficients are polynomially bounded in M; in particular there
> > are constants (K, B, c) depending on (μ, d) only with
> >
> >     u_{μ,d}(M) / Q^{μ(M−1)} ≤ K·M^B·Q^{−(M−c)}.
> >
> > Instances: (μ, d) = (2, d): K = 1, B = 1, c = 1 (the closed forms
> > above, machine legs A–C); the n = 3 systems: HEX3.B as displayed;
> > n = 4, 5: the battery's exact first-step recursions (GT-BDRAIN,
> > GENIND-BOX-4's compensating instrument) realize the exact species
> > pointwise at the sealed windows.
>
> This is a strengthening of the DISPLAY, not of the truth: the m = 2
> and n = 3 members already sit in the species at their proved pins,
> and the induction below PROPAGATES the rate clause, so the package
> that closes under GENIND.B's strong induction is P(k)-with-(A2-RATE).
> [ar1 2026-08-10, GAP-1 repair: as sealed, this closure sentence
> exceeded its displayed support — GENIND.C′ below proves the rate for
> the SIMPLE slice only, while (A2-RATE) as displayed pins the FULL
> complement, whose CS-stratum drain component (first consumed with
> CS-bearing (4, d) children at n = 5, C1(iii)'s GROWING regime) had no
> displayed all-window rate. The leg is now supplied: ANNEX-LEMMA
> GENIND-C2 (the r1 append below) derives the CS-drain rate from the
> displayed entry pricing + (CS-1)'s stage-window slot geometry, at
> window-deficit slope ≥ 2 — under (CS-1) alone, a clause of the same
> [GENIND-H] the strong induction already assumes (de facto discharged
> at n = 4). Read the closure sentence WITH that split: simple part by
> GENIND.C′ unconditionally; CS-drain part by GENIND-C2 given (CS-1);
> every displayed consumer of S5.2's vanishing bullet needs only the
> simple part.]”

**CONDITIONALITY:** **This is the repaired form of P(k)'s fourth member, and it is riddered twice more downstream.** The `[ar1]` layer splits the closure into a simple part (unconditional) and a CS-drain part (conditional on (CS-1)); the 2026-08-12 round-2 correction then upgrades that condition to **(CS-1Q), verified per genre** (`.199`). **The last clause of the `[ar1]` rider is the one a chapter cut should carry: “every displayed consumer of S5.2's vanishing bullet needs only the simple part.”**

**SUPERSESSION KIND:** the species pin itself = `inventory completion` (a consumed hypothesis component supplied). The `[ar1]` layer = `scope-pin` (the closure's reach is pinned to a two-part split). **Not a `replacement`:** neither the sealed (A2) wording nor (A2-RATE)'s display is withdrawn.

**TARGETS:** shard 1 `.13` (P(k)'s fourth member), `.45`, `.46`.

**CHAIN:** sealed “exact-complement (A2)” → **(A2-RATE)** species pin → `[ar1]` two-part split (simple by C′; CS-drain by GENIND-C2 under (CS-1)) → R9's Q-normalized GENIND-C2 (`.189`) → **R11's C2Q under (CS-1Q), verified per genre (`.198`, `.199`) — TERMINAL for the CS-drain part; GENIND.C′ (`.153`) — TERMINAL for the simple part.** Two terminals, one per consumer class (the pattern shard 1 flagged as a v3 gap in rule 25).

**ARITHMETIC AUDIT:** the (2, d) instance `(K, B, c) = (1, 1, 1)` ✓ — matches `.150`'s derived bound `u(N)/Q^{2(N−1)} ≤ N·Q^{−(N−1)}` exactly (`K·M^B·Q^{−(M−c)}` with K = B = c = 1 is `M·Q^{−(M−1)}` ✓). The n = 3 instance cites HEX3.B's `undecided/q^{3N} ≤ (1+N)q^{−N}`, i.e. `(K, B, c) = (·, 1, 0)` in the same species ✓ — polynomial coefficient, exponential deficit, as the species requires.

**DERIVATION:** The species is exhibited, not proved in general: `.150` proves the m = 2 instance, HEX3.B supplies n = 3, the battery supplies n = 4, 5 pointwise, and `.153` (GENIND.C′) proves that the induction PROPAGATES it on the simple slice.

**RESOLUTION TRACE:** statement lines 2641–2675. proof lines 2606–2639 (`.150`, the ground instance) + 2728–2752 (`.153`, the propagation). correction sites: `[ar1]` in situ 2662–2675; 3308–3557 (R9's GENIND-C2, `.189`); 3592–3721 (R11's C2Q + certification status, `.198`, `.199`).

**TEETH:** machine legs A–C for the ground instance; GT-BDRAIN for n = 4, 5; **nothing for the general species**, which is why it is a hypothesis pin and not a theorem. Disposition: `signed vacuity disclosure` at general (μ, d).

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:THEOREM HEX3.B` — count **8**.

---
### EFF.GENIND.152  [lemma]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph with four numbered clauses (R1.2 — ANNEX-LEMMA GENIND-C1, the β-term estimate and the two-regime split), carrying an `[ar1]` rider on its `u_l` definition. verbatim, lines 2677–2726.

> “**R1.2 ANNEX-LEMMA GENIND-C1 (the β-term estimate; the two-regime
> split).** Fix (m, d), window N, and a β-genre per GENIND-3's
> hypothesis with children (μ_l, k_l), depths
> D_l = min_j (v(a_j) + j·k_l) and windows M_l = N − D_l; write
> T_l = Q^{μ_l(M_l−1)} for the child totals and u_l = u_{μ_l,d}(M_l)
> [ar1 2026-08-10: the FULL complement, as written — its rate member is
> supplied by GENIND.C′ (simple part) + ANNEX-LEMMA GENIND-C2 (CS-drain
> part, under (CS-1); the r1 append below)]. Then:
> (i) [route prefactor] the genre's relative mass obeys
> ρ_g ≤ Q^{−(D_l−1)} for EACH child index l: the j = 0 term of the min
> gives D_l ≤ v(a₀), so the genre lies inside {v(a₀) ≥ D_l}, whose
> relative mass is exactly Q^{−(D_l−1)} (π-levels 1..D_l−1 of a₀
> pinned to zero — d·(D_l−1) q-digits; level 0 is pinned in every
> state). Machine (leg E): the committed loci obey it — M6's displayed
> law (q−1)²q^{6N−17} gives ρ = (q−1)²q^{−11} ≤ q^{−3} (D = 4) at
> q = 2,3,4,5; PSTEEP3 (2,5): 2^{−7} ≤ 2^{−2} (D = 3); PSTEEP4 (2,6):
> 2^{−11} ≤ 2^{−3} (D = 4).
> (ii) [composition through the fibration] the genre's contribution to
> u_{m,d}(N) is (prefactor count)·[Π_l T_l − Π_l (T_l − u_l)] —
> GENIND-3(c)'s product fibration (onto, constant fiber) with "the
> frame is conservative-undecided iff some child is". Bounding the
> inclusion–exclusion by the UNION BOUND (leg F: the difference
> Σ_l u_l·Π_{j≠l}T_j − [ΠT − Π(T−u)] expands with nonnegative
> coefficients in (u_l, T_l − u_l) at r = 2, 3 — no exactness is
> needed for the BOUND direction; see R6), the relative contribution
> is ≤ ρ_g · Σ_l u_l/T_l.
> (iii) [the two regimes — both O(poly(N)·Q^{−(N−c)})] Fix any
> threshold c₀ ≥ 1 and split on the child window:
>   * GROWING (M_l > c₀): the child's (A2-RATE) at its strictly lower
>     degree μ_l·d < m·d ((IH), degree descent GENIND-1(iii)) gives
>     u_l/T_l ≤ K·M_l^B·Q^{−(M_l−c)}; with (i),
>     contribution_l ≤ K·N^B·Q^{−(D_l−1)−(M_l−c)} =
>     K·N^B·Q^{−(N−c−1)} — the exponents COMPOSE EXACTLY because
>     D_l + M_l = N (leg D verifies the identity from the hull data at
>     all six committed extractions: M6, TWOCHILD A/B, PSTEEP3,
>     PSTEEP4, SS6).
>   * BOUNDED (M_l ≤ c₀): the child limit is never invoked; the
>     trivial u_l/T_l ≤ 1 and (i) alone give
>     contribution_l ≤ Q^{−(D_l−1)} = Q^{−(N−M_l−1)} ≤ Q^{−(N−c₀−1)}
>     — the route prefactor carries the whole rate, which is Codex's
>     bounded-M_l half, now displayed.
> (iv) [genre count] a β-genre's datum at window N is a partition
> arrangement of m (finitely many types for fixed m) plus one integer
> slope per side, each slope ≤ v(a₀) ≤ N−1: at most p̃(m)·N^m live
> genres — polynomial in N of degree ≤ m. Summing (ii)–(iii) over
> children and (iv) over genres: the recursion's β-part contributes
> ≤ m·p̃(m)·K·N^{m+B}·Q^{−(N−c′−1)} relative mass, c′ = max(c, c₀) —
> exactly the consumed sentence's O(poly(N)·Q^{−(N−c)}), now DERIVED
> from the displayed (A2-RATE) + GENIND-3's fibration + the depth
> identity. ∎”

**CONDITIONALITY:** **Conditional on (A2-RATE) at the children's strictly lower degrees, i.e. on the (IH) with the species pin** — which is exactly the closure `.151` establishes. Its `u_l` is the FULL complement, so it inherits the two-part conditionality of `.151`: simple part unconditional, CS-drain part under (CS-1Q) after R11.

**ARITHMETIC AUDIT (compiler-computed; every displayed inequality and instance re-derived):**
* **(i) the prefactor.** `D_l = min_j(v(a_j) + j·k_l) ≤ v(a₀)` (the j = 0 term) ✓, so the genre ⊆ `{v(a₀) ≥ D_l}`. The relative mass of `{v(a₀) ≥ D}` in a system whose a₀ ranges over `(O/π^N)[x]_{<d}` with `ā₀ = 0`: levels 1..D−1 pinned, i.e. `d(D−1)` q-digits fixed out of `d(N−1)` ⟹ relative mass `q^{−d(D−1)} = Q^{−(D−1)}` ✓ **exactly as displayed**.
* **M6 instance:** locus `(q−1)²q^{6N−17}`, total `q^{6(N−1)} = q^{6N−6}`, so `ρ = (q−1)²q^{−11}` ✓. Bound `Q^{−(D−1)} = q^{−3}` at D = 4 ✓. Check `(q−1)²q^{−11} ≤ q^{−3}` ⟺ `(q−1)² ≤ q⁸` ✓ for all q ≥ 2 (at q = 5: 16 ≤ 390,625 ✓).
* **PSTEEP3 (2,5):** locus 32 = 2⁵ of `2^{3·4} = 2^{12}` ⟹ `ρ = 2^{−7}` ✓; bound at D = 3 is `2^{−2}` ✓; `2^{−7} ≤ 2^{−2}` ✓.
* **PSTEEP4 (2,6):** locus 512 = 2⁹ of `2^{4·5} = 2^{20}` ⟹ `ρ = 2^{−11}` ✓; bound at D = 4 is `2^{−3}` ✓ ✓. **All three machine-leg-E instances reproduce from shard 1's own locus data.**
* **(iii) GROWING, the exponent composition.** `Q^{−(D_l−1)}·Q^{−(M_l−c)} = Q^{−(D_l+M_l−1−c)} = Q^{−(N−1−c)}` using `D_l + M_l = N` ✓ — the displayed `Q^{−(N−c−1)}` ✓. **The identity `D_l + M_l = N` is `M_l := N − D_l` by definition** (shard 1 `.24`), so leg D verifies a definitional identity against hull data — a consistency check on the *extraction*, not on the algebra.
* **(iii) BOUNDED.** `Q^{−(D_l−1)} = Q^{−(N−M_l−1)}` ✓ by the same identity; and `M_l ≤ c₀` ⟹ `−(N−M_l−1) ≤ −(N−c₀−1)` ✓.
* **(iv) genre count.** slopes ≤ `v(a₀) ≤ N−1`, at most m sides ⟹ at most `N^m` slope tuples times `p̃(m)` partition types ✓ polynomial of degree ≤ m ✓. Final aggregation `m·p̃(m)·K·N^{m+B}` ✓ (m children × p̃(m)N^m genres × K·N^B).
* **(ii) the union bound.** `Π T − Π(T−u) ≤ Σ_l u_l Π_{j≠l} T_j` — expanding `Π(T_j − u_j)` and comparing, the difference is a sum of products with at least two u-factors, all nonnegative ✓; and dividing by `Π T_l` gives `≤ Σ_l u_l/T_l` ✓. **The claim “no exactness is needed for the BOUND direction” is exactly R6.2's separation** (`.23`).

**DERIVATION:** Displayed. Justification tags: (i) = `computation` (slot count) + machine leg E; (ii) = `by XREF GENIND-3(c)` (shard 1 `.24`/`.25`) + `computation` (union bound, leg F) + `by XREF R6`; (iii) = `by XREF` (A2-RATE) at lower degree + `by XREF GENIND-1(iii)` (degree descent) + `computation` + leg D; (iv) = `computation`.

**RESOLUTION TRACE:** statement lines 2677–2726. proof lines — displayed. correction sites: `[ar1]` in situ 2682–2684; the `u_l` rate member re-conditioned at 3712–3721 (`.199`, `.200`).

**TEETH:** machine legs D, E, F of `genind_annexr_supp.py` @ `f5271e4` (GREEN) — the depth identity at six committed extractions, the prefactor bound at three committed loci, and the union-bound dominance symbolically at r = 2, 3. Disposition: executable regression, **with a disclosed reach limit: legs D/E cover six extractions and three loci, all at n ≤ 6.**

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:S2.2` — count **19** (the slot count behind (i)).

---
### EFF.GENIND.153  [theorem]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R1.3 — ANNEX-THEOREM GENIND.C′, the quantitative vanishing clause) with its proof and an `[ar1]` c-choice rider. verbatim, lines 2728–2752.

> “**R1.3 ANNEX-THEOREM GENIND.C′ (the vanishing clause, quantitative
> form — the induction closed).** For the simple slice of each (m, d):
> there are (K, B, c) with u^{simple}_{m,d}(N)/Q^{m(N−1)} ≤
> K·N^B·Q^{−(N−c)} at every window N ≥ 1. *Proof (lexicographic
> induction on (degree m·d, window N), the S5.2 recursion's own
> shape).* Head: Q^{(m−1)(N−1)}/Q^{m(N−1)} = Q^{−(N−1)}. α-term k
> (same degree, window N−mk < N): the α(k) locus's relative mass
> factor is (Q−1)Q^{−k·m(m+1)/2} (GENIND.A(I)); against the window
> induction's bound at N−mk the exponents recompose to
> (Q−1)Q^{−k·c(m)}·[K(N−mk)^B·Q^{−(N−c)}], and Σ_{k≥1}(Q−1)Q^{−k·c(m)}
> ≤ 1 for c(m) ≥ 1: the α-sum is ≤ K·(N−m)^B·Q^{−(N−c)}. β-terms:
> GENIND-C1 gives ≤ m·p̃(m)·K'·N^{m+B'}·Q^{−(N−c'−1)} with the
> children's constants (degree induction). Choosing **c := c′ + 1**
> [ar1 2026-08-10, MINOR-1: the c-choice displayed at source — c′ =
> max(children's c, c₀) is degree-induction data, so no circularity;
> with c = c′ + 1 the β-leg's Q^{−(N−c′−1)} = Q^{−(N−c)} EXACTLY, and
> c ≥ c₀ + 1 ≥ 2 ≥ 1 absorbs the head leg (Q^{−(N−1)} ≤ Q^{−(N−c)} iff
> c ≥ 1); the α-leg re-enters at the same degree with this same c, the
> window induction's own constant], B = m + B' + 1 and
> K large enough that K·[N^B − (N−m)^B] dominates the head + β
> coefficients (a degree-(B−1) polynomial inequality, satisfiable
> since N^B − (N−m)^B has positive leading coefficient m·B·N^{B−1}),
> the three legs sum to ≤ K·N^B·Q^{−(N−c)}: the induction closes. The
> m = 2 closed forms realize (K, B, c) = (1, 1, 1) — the ansatz is
> sharp at the ground instance. ∎”

**CONDITIONALITY:** **UNCONDITIONAL on the simple slice** — the one unconditional addition of the whole annex stack, and the reason `.151`'s split is honest. Its scope is exactly THEOREM GENIND.C's (shard 1 `.46`): the simple slice, all (m, d), every window `N ≥ 1` — **and `N ≥ 1` consumes R3's window-1 rider** (`.13`).

**ARITHMETIC AUDIT (compiler-computed; every leg re-derived):**
* **Head.** `Q^{(m−1)(N−1)}/Q^{m(N−1)} = Q^{−(N−1)}` ✓.
* **α-leg.** The α(k) locus is `(Q−1)Q^{m(N−1)−k·m(m+1)/2}` (shard 1 `.08`), so its relative mass is `(Q−1)Q^{−k·m(m+1)/2}` ✓. Recomposition: the sub-system at window `N−mk` has total `Q^{m(N−mk−1)}`, so the α-branch's absolute contribution is `(Q−1)Q^{k·c(m)}·u(N−mk)` (shard 1 `.21`), whose relative share is `(Q−1)Q^{k·c(m)}·Q^{m(N−mk−1)}/Q^{m(N−1)}·[u(N−mk)/Q^{m(N−mk−1)}]` = `(Q−1)Q^{k·c(m) − km²}·[…]` = `(Q−1)Q^{−k·m(m+1)/2}·[…]` ✓ (since `km² − k·m(m−1)/2 = k·m(m+1)/2` ✓). The displayed intermediate `(Q−1)Q^{−k·c(m)}` differs from `(Q−1)Q^{−k·m(m+1)/2}` by `Q^{−km}`; **both appear in the passage, at different points of the recomposition, and the geometric-sum step uses the weaker `Q^{−k·c(m)}`** — `Σ_{k≥1}(Q−1)Q^{−k·c(m)} ≤ 1` requires `(Q−1)·Q^{−c(m)}/(1−Q^{−c(m)}) ≤ 1` ⟺ `(Q−1) ≤ Q^{c(m)} − 1` ⟺ `Q ≤ Q^{c(m)}` ✓ for `c(m) ≥ 1`, i.e. `m ≥ 2` ✓ — **the displayed side condition is exactly right and tight at m = 2.**
* **c-choice.** `c := c′ + 1` makes the β-leg's `Q^{−(N−c′−1)}` equal `Q^{−(N−c)}` ✓; and `c ≥ 1` makes the head's `Q^{−(N−1)} ≤ Q^{−(N−c)}` ✓. Non-circularity: `c′ = max(children's c, c₀)` is data from the *lower-degree* induction hypothesis ✓, and the α-leg re-enters at the SAME degree with the same c ✓ — so the definition is well-founded on the lexicographic order.
* **K-choice.** `N^B − (N−m)^B` has leading term `mBN^{B−1}` ✓ (binomial), so a degree-(B−1) polynomial inequality is satisfiable for large K ✓.
* **Ground sharpness.** `(K, B, c) = (1, 1, 1)` matches `.03`'s derived bound exactly ✓.
* **Compiler note.** The α-leg's two exponent forms are both correct at their own points but the passage does not spell out the intermediate step between them; the compiler re-derived it above. Recorded as a **compressed step, not a gap** — the arithmetic closes.

**SUPERSESSION KIND:** `license` — supplies the quantitative form the frozen §S5.2 bullet asserted qualitatively. The `[ar1, MINOR-1]` layer = `inventory completion` (the c-choice, previously undisplayed, is displayed at source with a non-circularity argument).

**TARGETS:** shard 1 `.45`, `.46`, `.57`.

**DERIVATION:** Displayed. Justification tags: head = `computation`; α = `by XREF GENIND.A(I)` + `computation` (geometric sum); β = `by XREF GENIND-C1` (`.152`); the closure = `computation` (polynomial dominance).

**RESOLUTION TRACE:** statement lines 2728–2752. proof lines — displayed. correction sites: `[ar1]` in situ 2741–2746.

**TEETH:** the ground instance is machine-checked (legs A–C); **the induction itself is unguarded** — no battery row exercises a lexicographic induction. Disposition: **PROOF-ONLY**, with `.150`'s ground instance as the only anchor.

---
### EFF.GENIND.154  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R1.4 — what moves and what does not), carrying `[ar1, MINOR-2]` and a CS-rider. verbatim, lines 2754–2777.

> “**R1.4 What moves, what does not.** GENIND.C's vanishing bullet now
> reads through (A2-RATE) + GENIND-C1 + GENIND.C′ — the consumed rate
> is supplied by the DISPLAYED hypothesis and the displayed two-regime
> estimate; the α/head legs were never in question. Of the five
> committed displays this section consults — W-11's R(M), HEX3.A's
> exact law, HEX3.B's rate, the GT-BDRAIN n = 4, 5 first-step
> recursions, and GENIND-BOX-4's pricing sentence — none is rewritten
> here [ar1 2026-08-10, MINOR-2: the sealed sentence ("No committed
> number, count law, or supplier verdict moves") quantified with no
> scope pointer, the record species the note's own r5
> enumerative-records policy was adopted against; this enumeration
> replaces it]: the n ≤ 3 suppliers
> (W-11, HEX3.A/B) already carried the species at their pins, and the
> n = 4, 5 exact recursions are stronger than the bound at those
> degrees (GENIND-BOX-4's own sentence). GENIND-BOX-4's pricing of the
> per-genre expansion STANDS for what remains compressed (the
> per-genre prefactor ledgers); the box's sharpened defect — the
> hypothesis-WIRING gap Codex named — is cured by this section.
> Step 4's simple part consumes GENIND.C′ verbatim in place of the
> bare bullet; the CS legs keep their [GENIND-H]/(CS-EXACT)
> conditionality unchanged [ar1 2026-08-10: for menu + exactness — the
> CS legs' RATE is now supplied separately by ANNEX-LEMMA GENIND-C2
> under (CS-1) alone (the r1 append below); (CS-EXACT) supplies
> exactness, not a rate, per R6.2's identity-vs-bound separation].”

**CONDITIONALITY:** **The install instruction for the whole R1 repair**, and the sentence that tells a chapter cut which frozen text to read differently: “Step 4's simple part consumes GENIND.C′ verbatim in place of the bare bullet.” Its five-display census is superseded once more by R9's riding MINOR-B, which replaces it with a longer enumeration (`.193`).

**SUPERSESSION KIND:** the section = `license` + `scope-pin`; the `[ar1, MINOR-2]` layer = `replacement` (a non-enumerative record sentence replaced by an enumeration, original quoted) — **the r5 standing rule applied retroactively to the annex's own prose**, which is the clearest evidence that the rule is corpus-level and not round-local. The closing `[ar1]` rider = `provenance-rider` (which clause supplies the rate versus the exactness).

**TARGETS:** shard 1 `.45`, `.57`; shard 2 `.78`.

**ARITHMETIC AUDIT:** “five committed displays” ✓ five enumerated (R(M), HEX3.A, HEX3.B, GT-BDRAIN's recursions, GENIND-BOX-4's sentence). R9's MINOR-B later replaces this with **eleven** named items (`.193`) — audited there.

**DERIVATION:** Not a mathematical unit; an install record.

**RESOLUTION TRACE:** statement lines 2754–2777. correction sites: `[ar1]` in situ 2761–2765 and 2774–2777; 3563 (R9's MINOR-B census replacement, `.193`); 3714–3721 (R11's consumer sweep, `.200`).

**TEETH:** NONE — an install record. Its five-display census is verifiable against shard 1/2 units and is (`.193` notwithstanding) correct as far as it goes.

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:THEOREM HEX3.A` — count **11**; `THEOREM HEX3.B` — count **8**; `R(M)` — count **21**.

---
### EFF.GENIND.155  [supplier-finding]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph with a block quotation (R2.0 — CODEX F1, quoted). verbatim, lines 2779–2794.

> “### R2 (CODEX F1): the unit-pivot step — GENIND-6(c)'s onto/constant-fiber condition displayed at schema level
>
> **R2.0 The finding, quoted (F1, CONFIRMED GAP, disclosure overlap).**
>
> > "GENIND-6(c)'s onto-with-constant-fiber is carried by 'triangular
> > with exact budget floors' + 'the same S2.2 slot bookkeeping' — and
> > triangularity alone does NOT give surjectivity/constant fibers
> > over truncated DVRs (Codex's valid toy: (x, y) ↦ (x, (x+π)y)
> > mod π², triangular, fiber collapses at x = 0). The missing
> > displayed step is the unit-pivot condition (the division ledger's
> > pivots are units because the extracted factors are MONIC — true,
> > used, never displayed as the load-bearing condition)."
>
> The same sentence pattern is consumed at GENIND-3 step (3) ("the
> fiber count per genre is the S2.2 slot count…"), so the rider
> covers both sites.”

**CONDITIONALITY:** CONFIRMED GAP, “with disclosure overlap” (the honesty boxes had already flagged onto-ness at multi-child genres as a hostile target — shard 1 `.26`(a) — so the finding partly lands in territory the note had marked). **The finding is constructive: it supplies a counterexample shape, not merely a doubt.**

**ARITHMETIC AUDIT (compiler-computed, on the toy):** over `O/π²`, the map `(x, y) ↦ (x, (x+π)y)`. At `x ∈ (π)`, `x + π ∈ (π)` is a non-unit; then `(x+π)y` ranges only over `(π)` as y varies, and every value has `|{y}| = ` the size of the annihilator — the fibre size jumps. Concretely over `ℤ/4` (π = 2): at `x = 0`, `(0+2)y = 2y ∈ {0, 2}` for `y ∈ {0,1,2,3}` — image size 2, fibre size 2; at `x = 1`, `3y` is a bijection — image size 4, fibre size 1 ✓. **The toy is valid and the collapse is exactly as described.** Triangularity holds throughout ✓.

**DERIVATION:** Not a mathematical unit; a defect report with a counterexample.

**RESOLUTION TRACE:** statement lines 2779–2794. correction sites: none (this is the finding).

**TEETH:** **`decorrelated-model audit`.** No battery row could produce this: the runner only ever executes monic ledgers, so the failure mode is off its state space by construction — the note's own R2.3 says as much (“a non-unit pivot would surface there as a fiber-size split, the signature those runs exclude at their windows”), i.e. the runs *exclude* the signature and therefore cannot *find* the missing hypothesis.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:S2.2` — count **19**.

---
### EFF.GENIND.156  [lemma]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R2.1 — the unit-pivot rider at schema level). verbatim, lines 2796–2810.

> “**R2.1 The rider (schema level).** In GENIND-6(c)'s coordinate map
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
> a target-independent q-power. Without unit pivots both conclusions
> fail, and Codex's toy is the exact failure shape: (x, y) ↦
> (x, (x+π)y) mod π² is triangular, but at x ∈ (π) the pivot x + π is
> a non-unit and the y-fiber collapses.”

**CONDITIONALITY:** **A schema-level rider covering TWO frozen sites** (shard 1 `.36` and `.24`'s step (3)). It supplies a *condition*; `.10` supplies its *verification* per ledger species.

**SUPERSESSION KIND:** `license` — an underived step consumed silently is supplied. **Not `wording-rider`:** although the surface instruction is “read X as Y”, the operative content is a new condition with a proof of what it buys (onto + constant fibre), which a wording substitution is not. **This is the shard's canonical illustration of rule 18's warning that near-identically phrased riders are not interchangeable.**

**TARGETS:** shard 1 `.36`, shard 1 `.24`.

**ARITHMETIC AUDIT:** back-substitution over `O/π^w`: given a triangular system with unit pivots, solving slot by slot in the triangular order yields a unique preimage for each target ✓ (units invert in `O/π^w` ✓), so ONTO with fibre = the free slots ✓, a target-independent `q^{#free}` ✓. The argument is correct as displayed.

**DERIVATION:** Displayed. Justification tags: `computation` (back-substitution over a truncated DVR) + the toy as the sharpness witness.

**RESOLUTION TRACE:** statement lines 2796–2810. correction sites: none.

**TEETH:** machine leg G (`.158`), a **planted mutant** realizing the toy.

---
### EFF.GENIND.157  [lemma]

**CANONICAL STATEMENT:** FORM: bold-headed bulleted display (R2.2 — why the pivots ARE units, per ledger species). verbatim, lines 2812–2840.

> “**R2.2 Why the pivots here ARE units (re-derived from the displayed
> mechanisms; the ledger species of GENIND-3 steps (1)–(3) /
> GENIND-6(a)(c), enumerated).**
> * RECENTER ledgers (GENIND-2(a), consumed at step (1) and
>   GENIND-6(a)): the update of the Φ-adic coordinates under
>   x ↦ x + s is the binomial matrix, displayed at S3 as "triangular
>   with unit diagonal" — the diagonal entries are the binomials
>   C(j, j) = 1. Pivot = 1.
> * SCALE/CONTENT moves (x = π^k y; divide by π^D): digit-slot
>   RELABELINGS (window shifts with the ghost-slot bookkeeping of
>   GENIND-2(a)) — no slot is multiplied inside its ring; no pivot
>   arises.
> * DIVISION ledgers (step (2)'s Hensel split; GENIND-6(a)'s "monic
>   cofactor with PER-COEFFICIENT certified windows (the triangular
>   division ledger)"): every division row divides BY A MONIC factor —
>   the frame f is monic (S1's states) and the extracted blocks are
>   monic (W12-S2.1's monic-factor form; GENIND-6(a)). Long division
>   by a monic divisor determines each new cofactor coefficient with
>   the divisor's LEADING coefficient as the pivot, = 1. The
>   non-unit-lead cofactor of the shallower-co-block case (step (1))
>   is never a divisor in any ledger row — it is an OUTPUT whose lead
>   carries the dropped content.
> * LETTER scalings: multiplication by the co-blocks' unit values
>   (W12-L1(b) product form / J-D0) — units by that lemma's own
>   computation.
> So each ledger row's pivot is the literal unit 1 (or a W12-L1(b)
> unit): MONICITY is the load-bearing condition, now displayed.
> The toy's pivot x + π is the lead of a non-monic multiplier — a
> shape the displayed species exclude.”

**CONDITIONALITY:** **An ENUMERATED species check — four ledger kinds, each with its pivot identified.** The third bullet is the load-bearing one and it also disposes of the obvious objection (the non-unit-lead cofactor of the shallower-co-block case), by observing that it is an OUTPUT, never a DIVISOR. **This is a genuine proof at schema level; what remains compressed is the per-genre ledger, and `.158` says so.**

**ARITHMETIC AUDIT (compiler-computed):**
* Recenter: the binomial update matrix under `x ↦ x + s` has entries `C(i, j)s^{i−j}`; its diagonal is `C(j,j) = 1` ✓, so triangular with unit diagonal ✓ — and shard 1 `.21`'s proof displays exactly that phrase ✓.
* Scale/content: `x = π^k y` and division by `π^D` are index shifts on digit slots; no slot is multiplied by a ring element ✓ — so no pivot exists to be non-unit ✓.
* Division by a monic `g` of degree `e`: long division determines each quotient coefficient as `(current leading term)/(lead of g)` = `(…)/1` ✓ — pivot 1 ✓.
* Letter scalings: units by W12-L1(b) ✓ (cited, not re-derived).
* **Completeness of the species list.** GENIND-3's steps are (1) recenter+scale+normalize, (2) Hensel split, (3) read equivalence + fiber count; GENIND-6(a)(c) add the division ledger and the coordinate map. Every ledger row in those steps falls under one of the four bullets ✓ — recenter (step 1), scale/content (step 1), division (step 2 and (a)), letters (step 3 and (c)). **The enumeration is exhaustive over the displayed mechanisms**, which is exactly the scope R2.3 then declares.

**DERIVATION:** Displayed. Justification tags: bullets 1, 2, 3 = `computation` `by XREF GENIND-2(a)` / `by XREF W12-S2.1`; bullet 4 = `by XREF W12-L1(b)` + `by XREF LEMMA J-D0`.

**RESOLUTION TRACE:** statement lines 2812–2840. correction sites: none.

**TEETH:** machine leg G (`.158`) exercises the *condition*, not the species check; the species check is **PROOF-ONLY**, and R2.3 supplies its coverage sentence.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:W12-S2.1` — count **9**; `W12-L1` — count **30**.
XREF: `lean/notes/openmath/JD0_PROOF_2026-08-08.md:J-D0` — count **25**.

---
### EFF.GENIND.158  [run-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R2.3 — verification and scope honesty). verbatim, lines 2842–2852.

> “**R2.3 Verification.** Machine leg G (genind_annexr_supp.py @
> f5271e4, GREEN): over ℤ/4, (x+2)·y is bijective in y iff x is odd
> (a unit) — the toy's collapse — while the monic-pivot form (1+2x)·y
> is bijective at every x. Instance contact for (c)'s count: the
> committed EXHAUSTIVE onto-with-constant-fiber enumerations at M6
> (S4.3 machine record: fibers {512} = q⁹ / {128} = q⁷ at every
> enumerable window) — a non-unit pivot would surface there as a
> fiber-size split, the signature those runs exclude at their windows.
> Scope honesty: the rider displays the condition and its supply; the
> per-genre ledgers remain compressed per the S4.3 honesty box, and
> the multi-block hostile targets it names stay named.”

**ARITHMETIC AUDIT (compiler-computed):** over `ℤ/4`, `(x+2)y` bijective in y iff `x+2` is a unit iff `x + 2` is odd iff `x` is odd ✓ (x odd ⟹ x+2 odd ⟹ unit; x even ⟹ x+2 even ⟹ zero divisor). And `(1+2x)` is odd for every x ✓ — always a unit, always bijective ✓. **The leg's two claims are exactly right.** The M6 fibre figures `{512} = 2⁹` and `{128} = 2⁷` reproduce from shard 1 `.38`'s exponent audit ✓.

**CONDITIONALITY:** **Scope honesty is explicit and narrow**: the rider supplies the condition, the per-genre ledgers stay compressed, and the multi-block hostile targets stay named. So R2 closes the *displayed* gap and not the *compression* debt.

**DERIVATION:** Not a mathematical unit; a verification record.

**RESOLUTION TRACE:** statement lines 2842–2852. correction sites: none.

**TEETH:** **planted mutant, fired** (leg G realizes the exact failure shape and shows the monic form immune) + **instance contact** at M6's exhaustive enumerations, with an honest statement of what that contact can and cannot show. Disposition: planted mutant + `disclosed non-repair` for the compressed ledgers.

**PIN VERIFICATION:** `f5271e4` ✓; `genind_annexr_supp.py` ✓ and its output ✓ EXIST.

---
### EFF.GENIND.159  [supplier-finding]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph with a block quotation (R3.0 — CODEX F2, the window-1 scope leak). verbatim, lines 2854–2863.

> “### R3 (CODEX F2): the window-1 convention rider
>
> **R3.0 The finding, quoted (F2, CONFIRMED GAP — scope leak).**
>
> > "the S1 convention states 'window N ≥ 2', yet GENIND-2(a)'s
> > α-transport invokes the same system at window N − mk = 1 (first
> > at m = 2, N = 3, k = 1 — Codex's instance, admissible since
> > mk = 2 ≤ N−1), and GENIND-6's M6 ledger consumes a degree-2 child
> > at window 1 ('the child DRAINS instantly'). … neither GENIND-2
> > nor (IH) formally supplies it."”

**ARITHMETIC AUDIT:** Codex's instance — at `(m, N, k) = (2, 3, 1)`, admissibility is `mk ≤ N−1` i.e. `2 ≤ 2` ✓ admissible, and the target window is `N − mk = 3 − 2 = 1` ✓ **outside the stated convention `N ≥ 2`**. The M6 instance: at `N = 5` the child window is `N − 4 = 1` ✓ (shard 1 `.38`). **Both cited leaks are real and minimal.**

**CONDITIONALITY:** CONFIRMED GAP. A *scope* leak, not a false claim: the transports are right, the convention did not cover their targets.

**DERIVATION:** Not a mathematical unit; a defect report.

**RESOLUTION TRACE:** statement lines 2854–2863. correction sites: none.

**TEETH:** **`decorrelated-model audit`** — a convention-boundary check no battery row performs (the runner simply computes at window 1 without consulting a convention).

---
### EFF.GENIND.160  [convention]

**CANONICAL STATEMENT:** FORM: bold-headed bulleted display (R3.1 — the window-1 convention rider and its enumerated scope). verbatim, lines 2865–2889.

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
>   u = total exactly.
> Scope of application, enumerated — window-1 systems arise in this
> note only as TRANSPORT TARGETS (S1's ambient window stays ≥ 2):
> (a) GENIND-2(a)'s α(k) endpoint mk = N−1, first at
> (m, N, k) = (2, 3, 1); (b) GENIND-3/GENIND-6 child extractions at
> M_l = 1 — the M6 ledger at N = 5 ("the child DRAINS instantly — its
> entry datum is the whole certified content" is this rider's content
> verbatim at that instance); (c) the S5.2 recursion's boundary
> u(1) = 1, consumed by R1.1's telescope (whose closed form
> u(2ℓ+1) = (ℓ+1)Q^{2ℓ} − ℓQ^{2ℓ−1} returns 1 at ℓ = 0 — coherent
> both ways).”

**CONDITIONALITY:** **The content is FORCED, not chosen** — every clause is S1's own definitions evaluated at N = 1, which is why this is a `convention` unit and not a new hypothesis. **The scope is enumerated at three sites** (rule-compliant with the standing rule), and all three are verifiable: (a) shard 1 `.21`, (b) shard 1 `.24`/`.34`/`.38`, (c) shard 1 `.45` and `.03` here.

**SUPERSESSION KIND:** `inventory completion` — the missing boundary member of an existing definition is supplied, with its consumption sites enumerated.

**TARGETS:** shard 1 `.07`, `.21`, `.24`, `.34`, `.38`, `.45`.

**ARITHMETIC AUDIT (compiler-computed; every clause re-derived at N = 1):** state count `q^{dm(N−1)} = q⁰ = 1` ✓; `a_j ∈ (O/π)[x]_{<d}` with `ā_j = 0` forces `a_j = 0` ✓ (the reduction map is injective on `O/π`); `v(0) = ∞ ≥ 1 = N` ⟹ DRAIN ✓; DRAIN's locus law `q^{d(m−1)(N−1)} = q⁰ = 1` = the whole space ✓; α needs `mk ≤ 0` with `k ≥ 1`, impossible ✓; DEC/β/CS need `v(a₀) < N = 1`, i.e. `v(a₀) = 0`, impossible since `ā₀ = 0` ✓. **Exactly one of five events inhabited ✓.** Coherence with `.150`'s closed form at `ℓ = 0`: `u(1) = (0+1)Q⁰ − 0·Q^{−1} = 1` ✓ — **and note this is a genuine two-way check: the closed form was derived assuming `u(1) = 1`, and the rider independently derives `u(1) = 1` from the definitions.**

**DERIVATION:** Displayed; every clause is a definitional evaluation.

**RESOLUTION TRACE:** statement lines 2865–2889. correction sites: none.

**TEETH:** machine leg I (`.161`), plus a decorrelated sympy re-solve.

---
### EFF.GENIND.161  [run-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R3.2). verbatim, lines 2891–2895.

> “**R3.2 Verification.** Machine leg I (@ f5271e4, GREEN):
> (m, Q) ∈ {2, 3, 4} × {2, 3, 4} — 1 state, v(a₀) ≥ 1 = N, DRAIN,
> u(1) = total = 1. Decorrelated leg: the adjudication's row 2 records
> Codex's sympy re-solve of the S5.2 recursion under exactly this
> boundary (m = 2 closed forms exact at N = 2..12).”

**ARITHMETIC AUDIT:** the leg's grid is `3 × 3 = 9` cells ✓; each asserts the same four facts, all re-derived at `.160` ✓. The decorrelated re-solve covers `N = 2..12`, a subrange of leg A's `N = 2..14` ✓ — **two models, two implementations, same closed forms.**

**CONDITIONALITY:** none — a verification.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2891–2895. correction sites: none.

**TEETH:** executable regression + **`accepted-with-decorrelation-supplied`** (the sympy re-solve is a *different model's* implementation of the same recursion — the strongest decorrelation available for a symbolic claim).

---
### EFF.GENIND.162  [supplier-finding]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph with a block quotation (R4.0 — CODEX F5, the CS4-F floor). verbatim, lines 2897–2904.

> “### R4 (CODEX F5): the CS4-F visibility floor — display erratum at S5.3 + GENIND.A(IV)
>
> **R4.0 The finding, quoted (F5, CONFIRMED, regraded MINOR display).**
>
> > "CS4-F(k)'s law (q(q−1)/2)·q^{4N−10k−4} displayed without its
> > visibility floor 4k ≤ N−1 at S5.3 AND GENIND.A(IV); at (2,2,1)
> > the display returns 2^{−6}, true locus 0; the sibling CS4-E
> > carries its floor explicitly."”

**ARITHMETIC AUDIT:** at `(q, N, k) = (2, 2, 1)`: `(2·1/2)·2^{8−10−4} = 1·2^{−6}` ✓ **a non-integer count** — the sharpest possible signature. The sibling comparison is right: CS4-E carries `2h ≤ N−1` via `[r1, PE1-M3]` (shard 1 `.48`) and CS4-F carries nothing (shard 1 `.49`) ✓.

**CONDITIONALITY:** CONFIRMED, regraded MINOR **because the runner already gated on the floor** (`.164`) — so no committed number is affected. A display defect with zero downstream numeric consequence, and the regrade records exactly that.

**DERIVATION:** Not a mathematical unit; a defect report.

**RESOLUTION TRACE:** statement lines 2897–2904. correction sites: none.

**TEETH:** **`decorrelated-model audit`** — and note the asymmetry: the *runner* had the floor and the *display* did not, so no run could have surfaced it. Only a reader comparing display to sibling could, which is what a fresh model did.

---
### EFF.GENIND.163  [lemma]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R4.1 — the erratum with the floor re-derived). verbatim, lines 2906–2915.

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

**CONDITIONALITY:** A display erratum with a two-line derivation; no count moves.

**SUPERSESSION KIND:** `wording-rider` (“Read BOTH displays … WITH the floor”) — an explicit addition of a side condition to two displayed laws.

**TARGETS:** shard 1 `.49` (S5.3's CS4-F entry) and shard 1 `.11` (GENIND.A(IV)'s first-instances clause).

**ARITHMETIC AUDIT:** heights `(4k, 3k, 2k, k)` on a length-4 side at integer slope k ✓; `v(a₀) = 4k` ✓; DRAIN-first at `v(a₀) ≥ N` ⟹ inhabited iff `4k ≤ N−1` ✓ — re-derived independently at shard 1 `.49` and agreeing.

**DERIVATION:** Displayed. Justification tags: `by XREF` S5.3's own heights display + `by XREF GENIND.A(I)`'s DRAIN-first rule + `computation`.

**RESOLUTION TRACE:** statement lines 2906–2915. correction sites: none.

**TEETH:** machine leg H (`.164`).

---
### EFF.GENIND.164  [run-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R4.2 — committed numbers unaffected, with the runner's gate lines cited). verbatim, lines 2917–2925.

> “**R4.2 Committed numbers unaffected — the gate lines cited.** The
> sealed runner gates its genre-F predictor on exactly the floor:
> `while 4 * k <= N - 1:` at **genind_checks.py lines 709 and 869**
> (md5-pinned e7ca150b, consulted read-only). Machine leg H
> (@ f5271e4, GREEN): both gate lines verified verbatim in the pinned
> file; (2,2,1) gated to 0 where the bare display says 2^{−6};
> (2,5,1) above the floor with law 2^{20−10−4} = 2⁶ = 64.
> Display-only, the exact defect species as PE1-M3 — the E-law's
> existing floor sentence at S5.3 stands unchanged.”

**CONDITIONALITY:** **A source-code gate verification — an unusual and strong tooth**: the leg reads two named lines of the md5-pinned runner and confirms the implementation carries the side condition the display omitted.

**ARITHMETIC AUDIT:** `(2,5,1)`: `(q(q−1)/2)q^{4N−10k−4} = 1·2^{20−10−4} = 2⁶ = 64` ✓; floor `4·1 = 4 ≤ N−1 = 4` ✓ above the floor. `(2,2,1)`: `4 > 1` ⟹ gated to 0 ✓.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2917–2925. correction sites: none.

**TEETH:** **source-code gate verification** (leg H) — recorded in the enum as an `executable regression` against the pinned instrument's TEXT rather than its output. **PIN VERIFICATION:** `genind_checks.py` EXISTS ✓; lines 709 and 869 are cited by the leg, not re-read here (the file is md5-pinned and byte-frozen).

---
### EFF.GENIND.165  [supplier-finding]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph with a block quotation (R5.0 — CODEX F6, the converse at stage level). verbatim, lines 2927–2934.

> “### R5 (CODEX F6): the converse read at degree level — one rider
>
> **R5.0 The finding, quoted (F6, CONFIRMED, regraded MINOR wording).**
>
> > "S5.1's sufficiency (padding + QRT-G2) proves degree-level
> > existence only; the converse 'm ≥ 4 realizes CS' at stage level
> > (arbitrary m-key clusters) is not established — the padded
> > construction's stage carries 4 keys."”

**CONDITIONALITY:** CONFIRMED, regraded MINOR wording. **The finding is precise: the sufficiency proof produces a 4-key stage at every degree, which establishes a degree-level statement and not an m-indexed stage-level one.**

**ARITHMETIC AUDIT:** shard 1 `.11`'s sufficiency pads a QRT-G2 stage (which has exactly 4 keys) with a degree-(n−4) irreducible ✓ — so the realized stage always has m′ = 4, never an arbitrary m ≥ 4 ✓. **The finding checks.**

**DERIVATION:** Not a mathematical unit; a defect report.

**RESOLUTION TRACE:** statement lines 2927–2934. correction sites: none.

**TEETH:** **`decorrelated-model audit`** — a quantifier-scope reading no run can perform.

---
### EFF.GENIND.166  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R5.1 — the degree-level rider with a three-site consumer walk). verbatim, lines 2936–2955.

> “**R5.1 The rider.** Read GENIND.A(IV)'s converse clause
> ("conversely m ≥ 4 realizes CS with positive locus at every q") at
> DEGREE level: **every degree n ≥ 4 realizes a CS event with
> positive locus at every q, both characteristics** — which is what
> S5.1's sufficiency proof delivers (re-derived check: the padding
> block is coprime to the center and separable at level 0, hence a
> DECIDED piece — the padded state's CS event is the QRT-G2(h;(1²))
> stage's, and that stage carries exactly 4 keys at every n). The
> STAGE-level parse — for each m ≥ 4, an m-KEY stage itself opening a
> CS event with positive locus — is NOT claimed by this note.
> Displayed stage-level instances exist at m = 4 (the QRT genres are
> the 4-key system's own), m = 5 (S5.3's embedded genres), and m = 6
> (S4.3's M6/SS6, machine-realized); at general m the stage-level
> statement is left unclaimed (the adjudication marks it likely true
> via general-m embedded genres, not shown). Consumers of (IV),
> re-walked at the three consuming sites this round: S5.2's
> positive-density sentence (a degree-level realization — the quartic
> e-first entry mass), S6's conditionality geography (n ≤ 3 vacuity =
> the necessity half), S7.4's finite enumerability (the necessity
> half). None consumes the stage-level parse.”

**CONDITIONALITY:** **A scope pin with a completeness check attached** — the three consuming sites are walked and none needs the stronger parse, so the pin costs nothing downstream. **The unclaimed statement is explicitly marked “likely true … not shown”**, which is the honest register.

**SUPERSESSION KIND:** `scope-pin`. **Deliberately not `wording-rider`:** no phrase is substituted; a quantifier's intended range is fixed and the stronger reading is disowned.

**TARGETS:** shard 1 `.11`. **Explicitly NOT targeted:** shard 1 `.43` (“the criterion in one line”), which is already degree-level.

**ARITHMETIC AUDIT:** the three consumer sites map to shard 1 `.46` (S5.2's positive-density sentence), `.61` (S6's conditionality geography), `.74` (S7.4's finite enumerability) ✓ — **three for three, and each consumes only the necessity direction or a degree-level realization**, as claimed. The m = 4/5/6 instance list checks: QRT genres (shard 1 `.48`), S5.3's embedded genres (`.50`–`.52`), M6/SS6 (`.33`, `.42`) ✓.

**DERIVATION:** The re-derived check is displayed (the padding block is a decided piece; the stage is QRT-G2's, with 4 keys at every n).

**RESOLUTION TRACE:** statement lines 2936–2955. correction sites: none.

**TEETH:** the three-site consumer walk is itself the verification. Disposition: `transfer audit` (an internal one — a consumer walk over the note's own sites).

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:QRT-G2` — count **10**.

---
### EFF.GENIND.167  [run-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R5.2). verbatim, lines 2957–2959.

> “**R5.2 Verification.** The three-site consumer walk above; the
> m = 4, 5, 6 instances' committed laws (W-12 S2.5 pin; S5.3's
> tables; S4.3's machine record).”

**CONDITIONALITY:** **No machine leg** — the verification is a consumer walk plus three committed law citations. The note does not pretend otherwise.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2957–2959. correction sites: none.

**TEETH:** `transfer audit` only; **no executable regression**, and none is needed for a quantifier-scope pin. Disposition: `signed non-applicability`.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:S2.5` — count **9**.

---
### EFF.GENIND.168  [supplier-finding]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph with a block quotation (R6.0 — CODEX F4, scoped to the PE8 acceptance artifact). verbatim, lines 2961–2970.

> “### R6 (CODEX F4): the PE8-report notice + identity-vs-bound separated at Step 4's [r1] record
>
> **R6.0 The finding, quoted (F4, CONFIRMED, scoped to the PE8
> acceptance artifact, regraded MINOR at this note).**
>
> > "PE8 §4.1's necessity rationale is false: ∂F/∂u₁ = T₂ − u₂ ≥ 0
> > (claimed non-monotonicity wrong); 1 − Π(1 − u_i/T_i) is
> > coordinatewise increasing; upper bounds + union bound suffice for
> > W-12's (A2); exactness needed only for the stronger
> > exact-complement member."”

**CONDITIONALITY:** **The finding's target is the ACCEPTANCE REPORT, not the note** — “GAP at the PE8 acceptance report” per `.148`'s disposition list, regraded MINOR here. **This is the only finding in the corpus's GENIND arc that lands on the artifact that granted acceptance.** It does not disturb the acceptance: the note's own load-bearing sentences survive (`.170`).

**DERIVATION:** Not a mathematical unit; a defect report against a verifier artifact.

**RESOLUTION TRACE:** statement lines 2961–2970. correction sites: none.

**TEETH:** **`decorrelated-model audit`** — a fresh model checking an acceptance report's mathematics. **No in-house pass audits the report that accepted the note**, structurally.

---
### EFF.GENIND.169  [changes-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R6.1 — the notice, with the report left untouched). verbatim, lines 2972–2984.

> “**R6.1 The notice (the report itself stays untouched — its author's
> artifact per the standing rule; the notice lives here and at the
> ledger).** GENIND_passPE8_report.md §4.1 (its L176–178) writes "the
> r = 2 case u₁T₂ + T₁u₂ − u₁u₂ is already not monotone in u₁ once
> u₂ > T₂ − u₂" — FALSE: ∂/∂u₁(u₁T₂ + T₁u₂ − u₁u₂) = T₂ − u₂ ≥ 0
> identically on the admissible domain u₂ ≤ T₂. More: at r = 2, 3,
> ∂/∂u_i[Π_j T_j − Π_j(T_j − u_j)] = Π_{j≠i}(T_j − u_j) ≥ 0 — the
> composed undecided mass is coordinatewise NONDECREASING in the
> child u's, so upper bounds on children DO propagate to an upper
> bound on the frame, and the union bound Σ_i u_i·Π_{j≠i}T_j
> dominates it. The defect sits in the acceptance report's
> elaboration of WHY (CS-EXACT) is needed, not in this note's
> accepted text.”

**CONDITIONALITY:** **Freeze predicate: other authors' artifacts are never edited.** The notice “lives here and at the ledger”. This is the same protocol shard 2 `.132` applies to the PE4/PE5 reports' shared md5 typo.

**SUPERSESSION KIND:** none of the note's own text — this is a **notice against an external artifact**, which the v3 enum has no kind for. Filed as `changes-record` with type `supplier-finding`-adjacent; see §6.3 for the recommendation.

**ARITHMETIC AUDIT (compiler-computed, re-deriving both derivatives):** with `F = u₁T₂ + T₁u₂ − u₁u₂`, `∂F/∂u₁ = T₂ − u₂` ✓, which is `≥ 0` on `u₂ ≤ T₂` ✓ — **the report's claimed non-monotonicity is false, and the condition it names (`u₂ > T₂ − u₂`, i.e. `u₂ > T₂/2`) is irrelevant to the sign** ✓. General r: `G = Π_j T_j − Π_j(T_j−u_j)`, `∂G/∂u_i = +Π_{j≠i}(T_j − u_j) ≥ 0` ✓. Union bound: expanding `Π T − Π(T−u)` by inclusion–exclusion gives `Σ_i u_i Π_{j≠i}T_j` minus terms with ≥ 2 u-factors, all nonnegative ⟹ `G ≤ Σ_i u_i Π_{j≠i}T_j` ✓. **All three of R6.1's assertions verify.**

**DERIVATION:** Displayed (two derivative computations + the union bound).

**RESOLUTION TRACE:** statement lines 2972–2984. correction sites: none.

**TEETH:** machine leg F (`.171`) — symbolic, plus a preregistered decorrelation.

---
### EFF.GENIND.170  [scope-record]

**CANONICAL STATEMENT:** FORM: bold display (R6.2 — the identity-vs-bound separation, a dated rider on a frozen record). verbatim, lines 2986–2997.

> “**R6.2 The separation (a dated rider on Step 4's frozen [r1]
> record).** The record's load-bearing sentences STAND ("an identity
> only if those u's are exact" — true; P(n)'s fourth member fails
> under bound-only inputs — true, the member is an equality). The
> rider: **(CS-EXACT) is required because the induction propagates
> the exact-complement IDENTITY (P's fourth member — the
> inclusion–exclusion as an equality), NOT because bounds fail to
> propagate: upper bounds propagate by monotonicity + union bound
> (R6.1), which is exactly the mechanism GENIND-C1(ii) (R1.2 above)
> uses for the vanishing-rate BOUND. The two consumers want different
> strengths; only the identity consumer needs (CS-EXACT).** This
> discharges R1.2(ii)'s "see R6" pointer.”

**CONDITIONALITY:** **The cleanest conceptual repair in the stack, and it changes nothing downstream** — (CS-EXACT) is still required, for a different and correct reason. **Its practical consequence is what makes GENIND-C2 possible:** because bounds propagate, a RATE leg can be built under (CS-1) alone, without (CS-EXACT) (`.182`, `.191`, `.198`).

**SUPERSESSION KIND:** `provenance-rider` — the *reason* is replaced; the clause and its necessity are untouched. **Conflating this with a `replacement` would imply (CS-EXACT) was withdrawn, which is the opposite of the finding.**

**TARGETS:** shard 1 `.14` (the (CS-EXACT) clause's rationale), shard 1 `.58` (Step 4's `[r1]` record), shard 1 `.25`/`.37` (the composition clauses), and `.05`(ii) here (whose “see R6” pointer this discharges).

**DERIVATION:** The separation follows from `.169`'s monotonicity + union bound (bounds propagate) and from the observation that P's fourth member is an equality (so its propagation is an identity claim).

**RESOLUTION TRACE:** statement lines 2986–2997. correction sites: none.

**TEETH:** machine leg F (`.171`).

---
### EFF.GENIND.171  [run-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R6.3 — verification with a decorrelation record). verbatim, lines 2999–3004.

> “**R6.3 Verification.** Machine leg F (@ f5271e4, GREEN, symbolic):
> dF/du₁ = T₂ − u₂; ∂G/∂u_i = Π_{j≠i}(T_j − u_j) at r = 2, 3; the
> union-bound dominance certificates (UB − G with nonnegative
> coefficients in (u_i, T_i − u_i)). Decorrelation record: the fold's
> scaffold P-4 PREREGISTERED the same arithmetic before the run and
> its sympy leg confirmed it — two decorrelated models, same kill.”

**CONDITIONALITY:** **“two decorrelated models, same kill”** — a preregistered prediction (the fold's scaffold P-4) confirmed by an independent symbolic implementation. The strongest decorrelation record in the shard.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2999–3004. correction sites: none.

**TEETH:** executable regression (symbolic) + **`accepted-with-decorrelation-supplied`** with an explicit preregistration.

**PIN VERIFICATION:** `f5271e4` ✓.

---
### EFF.GENIND.172  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + paragraph (the ANNEX R close), carrying an `[ar1, MINOR-2]` enumeration. verbatim, lines 3006–3028.

> “### ANNEX R — close (2026-08-09)
>
> The S4 repair queue is EXECUTED in full: R1 (F3) @ a1525ea +
> machine leg f5271e4; R2–R6 in this append stack. Byte-freezes at
> the close: accepted body + pre-annex appends lines 1–2548 md5
> eefcf658 (re-verified at each annex commit); the R1 annex slice
> (lines 2549–2745) byte-identical to a1525ea's; the pinned artifacts
> this annex consults are exactly four — genind_checks.py e7ca150b
> (read-only at its two gate lines), genind_annexr_supp.py 42fd603e +
> its committed output d938ad82 (the additive leg), and this note's own
> bytes 1–2548 eefcf658 — each verified at its pin at this close
> [ar1 2026-08-10, MINOR-2: the sealed clause "sealed runner e7ca150b
> and every sealed artifact untouched" quantified without enumeration,
> against the note's own r5 policy; this enumeration replaces it. The
> annex's five commits — a1525ea2, 31c6723d, 98ac7bb0, fe0ed6c0
> (note-only) and f5271e4 (the supp pair) — touch no file beyond this
> note and that pair]. Grade honesty: this annex cures the six
> adjudicated findings by display riders, one erratum, and the R1
> derivations at the accepted text's own grade; the annex has NOT
> itself been through a hostile pass. The 2/2 acceptance attaches to
> the frozen body; the annex carries the ratification fold's
> CHALLENGE disposition (CODEX_GENINDRAT_2026-08-09.md S4) with the
> queue now landed.”

**CONDITIONALITY:** **“the annex has NOT itself been through a hostile pass” is a STALE-SELF-DESCRIPTION as of the r1 append** (`.178`), which runs exactly such a pass — 0C + 1 GAP + 2 MINOR — and it is **not edited**, only followed. Tagged `STALE-SELF-DESCRIPTION (uncured)` (rule 26). **“The 2/2 acceptance attaches to the frozen body”** is the sentence a chapter cut must carry with any annex-derived result.

**SUPERSESSION KIND:** the `[ar1, MINOR-2]` layer = `replacement` (a non-enumerative freeze sentence replaced by an enumeration of four artifacts + five commits, original quoted) — the r5 standing rule applied to the annex's own close.

**ARITHMETIC AUDIT (compiler-computed):** “exactly four” pinned artifacts ✓ enumerated (runner, supp py, supp output, the note's own bytes); “five commits” ✓ enumerated (`a1525ea2`, `31c6723d`, `98ac7bb0`, `fe0ed6c0`, `f5271e4`). **Both numerals reconcile with their enumerations** — unlike shard 2 `.127`'s “eight”. The R1 annex slice is cited as lines 2549–2745; the pre-annex freeze is 1–2548 ✓ contiguous, no gap ✓.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 3006–3028. correction sites: `[ar1]` in situ 3017–3022; the “no hostile pass” clause overtaken at 3098–3115 (`.178`).

**TEETH:** `arithmetic recount` (4/4 and 5/5 reconciled). **PIN VERIFICATION:** `a1525ea` ✓, `f5271e4` ✓ resolve; `31c6723d`, `98ac7bb0`, `fe0ed6c0`, `a1525ea2` are 8-hex prefixes — `a1525ea` ✓ resolves as the 7-prefix and the others are cited in the annex's own enumeration and are **not independently re-verified here** (recorded, §8 defect 2).

---
### EFF.GENIND.173  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph (the dated supplier-movement record's owed-disclosure discharge). verbatim, lines 3032–3041.

> “### Dated supplier-movement record (2026-08-09): GENHN errata E1–E3 EXECUTED + GENHN r2 — the n ≥ 8 leg gains [GENHN-TOW-1]
>
> **Owed disclosure discharged (S16 row 6: "execution disclosure owed
> at the next dated append").** GENHN's three queued errata are
> EXECUTED: E1 @ bc1b996 (LEMMA GENHN-3(a)'s f₁ ≥ 2 band-exit clause
> conditionalized to the GENH4-r3 trichotomy), E2 @ 961d0ff
> (GENHN.A(v)'s census clause gains the comp-weighted band clause,
> Q^{comp}−1 per band pin), E3 @ 46bf675 (the stage-ring carrier at
> GENHN.A(i)/S3.1 restated in L/O_L), plus the S10 box refresh
> @ 58b1080 — all 2026-08-09, before GENHN's PE1.”

**CONDITIONALITY:** **Discharges an obligation created two shards earlier** (shard 2 `.91`, `.136` row 6) — the note's obligation-tracking working as designed. All three errata land on clauses GENIND consumes or neighbours.

**SUPERSESSION KIND:** `inventory completion` (an owed disclosure supplied).

**TARGETS:** shard 2 `.91`, shard 2 `.136` row 6.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 3032–3041. correction sites: none.

**TEETH:** `transfer audit` (the per-clause screen at `.175`). **PIN VERIFICATION:** `bc1b996` ✓, `961d0ff` ✓, `46bf675` ✓, `58b1080` ✓.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:LEMMA GENHN-3` — count **3**; `GENHN.A(v)` — count **6**; `GENHN.A(i)` — count **11**.

---
### EFF.GENIND.174  [changes-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (the new supplier movement: GENHN r2). verbatim, lines 3043–3053.

> “**New movement: GENHN r2 (its PE1 repair round).** GENHN's PE1
> hostile pass REFUTED LEMMA GENHN-T(b); r2 landed the repair —
> @ d16869c (T(b) WITHDRAWN; **LEMMA GENHN-T(b)′ stated AND PROVED**;
> the **new box [GENHN-TOW-1]** (entry budgets, inner refine,
> faithfulness geography, partial sides, composed window); GENHN.B's
> tower clause + EXACTLY display restated honestly — **n ≤ 7 as
> sealed; n ≥ 8 adds TOW-1**), @ 7650b20 (LEMMA GENHN-1's budget
> display corrected; the node floor (μ−j)S+1 RE-DERIVED from the true
> floors, standing), @ 438608a (band transport derived at the E1
> annex; S7 stage-RAM rider; run reconciliation; arc line: 0/2 stays,
> PE2 next), @ 9636b7e (T(b)′ statement rigor parenthetical).”

**CONDITIONALITY:** **A supplier lemma was REFUTED and replaced behind a new box.** This is the strongest inbound movement in the GENIND arc: not a display correction, not a re-pin, but a withdrawn lemma. Its consequence for GENIND is `.176`.

**SUPERSESSION KIND:** none of GENIND's own text; a supplier-movement record. **The v3 enum's gap again** (§6.3).

**ARITHMETIC AUDIT:** four r2 commits enumerated ✓ (`d16869c`, `7650b20`, `438608a`, `9636b7e`), plus the four E1–E3 + box-refresh commits at `.173` = **eight commits of supplier movement** ✓ — matching `.177`'s “exactly the eight commits enumerated above” ✓.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 3043–3053. correction sites: none.

**TEETH:** foreign-note evidence (GENHN's own PE1/r2 arc). **PIN VERIFICATION:** `d16869c` ✓, `7650b20` ✓, `438608a` ✓, `9636b7e` ✓.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:LEMMA GENHN-T(b)` — count **11**; `GENHN-TOW-1` — count **19**.

---
### EFF.GENIND.175  [changes-record]

**CANONICAL STATEMENT:** FORM: bold-headed bulleted display (the per-clause consumption screen over the seven PE7-m2 sites). verbatim, lines 3055–3074.

> “**Consumption verdicts at ledger granularity (the seven PE7-m2
> sites, screened against the 850e77e → HEAD diff this round):**
> * GENHN.A(iv), consumed at GENIND-6(b) (the stage node floor
>   S_b + 1): clause text not in the diff; its node-floor arithmetic
>   was re-derived and STANDS at 7650b20 — SURVIVES.
> * GENHN.A(v), consumed at (CS-1)/S7.1: E2 ADDS the comp-weighted
>   band census — the exact form this note's Step 4 already consumes
>   in its r2-corrected sentence ("q^{comp}−1 per RAM/2SIDED pin") —
>   alignment, SURVIVES.
> * LEMMA GENHN-3, consumed at (CS-1) + S6 Step 4 (ragged-band
>   CONFINEMENT at the discharged genres): E1 conditionalizes the
>   f₁ ≥ 2 band-EXIT phrasing; the discharged genres consumed here
>   are f₁ = 1 — SURVIVES.
> * S6.2, consumed at (CS-2): E2's tag reaches its assembly
>   sentence's census factor, the same alignment as A(v) — SURVIVES.
> * The three PE7-m2 cites (S11.F @ this note's L684; S6.3 @ L1094;
>   the GENIND-6(a) statement echo @ L623): none named by the
>   E1–E3/r2 commit set (diff-grep, this round); S6.3's display is
>   consumed here WITH the genre-F granularity caveat Step 4 already
>   carries — SURVIVE.”

**CONDITIONALITY:** **A seven-site diff-granularity screen — strictly stronger than shard 2 `.91`'s ledger-granularity check**, and it honours PE7-m2's instruction (“screen future GENHN errata against the seven sites, not four”) exactly.

**ARITHMETIC AUDIT:** the screen covers 4 clauses + 3 cites = **seven sites** ✓, matching PE7-m2's count ✓; they map to shard 1 `.35`, `.63`/`.37`, `.57`/`.63`, `.64`, `.34` (×2), `.57` ✓. Every one returns SURVIVES ✓ — **7/7**, with two distinct grounds (clause text not in the diff; the erratum aligns with the consumed form).

**DERIVATION:** Not a mathematical unit; a per-clause transfer check.

**RESOLUTION TRACE:** statement lines 3055–3074. correction sites: none.

**TEETH:** **`transfer audit`** at diff granularity — the strongest form in the corpus short of verbatim text matching, and an escalation over shard 2's ledger-granularity screen.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN.A(iv)` — count **3**; `GENHN.A(v)` — count **6**; `LEMMA GENHN-3` — count **3**; `S6.2` — count **6**; `S11.F` — count **10**; `S6.3` — count **3**.

---
### EFF.GENIND.176  [hypothesis]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (THE CONDITIONALITY MOVEMENT — the n ≥ 8 conjunction). verbatim, lines 3076–3088.

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

**CONDITIONALITY:** **THE most consequential single unit of this shard for the capstone DAG.** The note's headline claim — “the distance from the n = 3 theorem to the FULL uniformity theorem is exactly ONE displayed hypothesis family” (shard 1 `.04`) — is true at n ≤ 7 and **false as stated at n ≥ 8**, where the conjunction is three families. The movement is *bookkeeping* in the sense that no proof changes; it is *substantive* in the sense that the capstone's hypothesis block grows.

**SUPERSESSION KIND:** `scope-pin` — a range-indexed re-reading of the conditionality, with n ≤ 7 explicitly unmoved.

**TARGETS:** shard 1 `.15` (the GENIND.B consequence clause), and by inheritance shard 1 `.04`, `.13`, `.61`.

**DERIVATION:** Not a proof; a conditionality composition read off the supplier's restated clause.

**RESOLUTION TRACE:** statement lines 3076–3088. correction sites: none.

**TEETH:** NONE — a conditionality statement. Disposition: `signed vacuity disclosure` at n ≥ 8 (nothing in this note's evidence base reaches degree 8 except PE4's N8MIX construction and PE7/PE8's routes, none of which exercises [GENHN-TOW-1]).

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN-TOW-1` — count **19**; `GENHN.C` — count **19**.
**NEAR-MISS:** `[GENHN-HE(μ ≥ 3)]` — count **0** in GENHN; the reading is fixed by PE7-m3 (shard 2 `.145`) and this unit cites that fix explicitly (“read per PE7-m3”).

---
### EFF.GENIND.177  [changes-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (the record's pins and byte-freeze). verbatim, lines 3090–3094.

> “**Pins (git log at THIS commit).** GENHN note HEAD = 9636b7e (arc
> 0/2, its PE2 next — a consumer flag GENHN's own S10 carries);
> supplier movement since this note's last pin 850e77e = exactly the
> eight commits enumerated above (E1–E3, 58b1080, r2 ×4). Byte-freeze
> re-verified at this commit: lines 1–2548 md5 eefcf658.”

**ARITHMETIC AUDIT:** “exactly the eight commits enumerated above (E1–E3, 58b1080, r2 ×4)” = 3 + 1 + 4 = **8** ✓ — **the numeral reconciles with its enumeration** (as at `.172`, and unlike shard 2 `.127`).

**CONDITIONALITY:** **GENHN's new HEAD is `9636b7e` with arc 0/2 and PE2 pending** — so this note's n ≥ 8 conditionality now rides a supplier at grade 0/2 whose own next hostile pass has not run. The note flags the consumer signal explicitly.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 3090–3094. correction sites: none.

**TEETH:** `arithmetic recount` (8/8) + commit-time git-log check. **PIN VERIFICATION:** `9636b7e` ✓, `850e77e` ✓.

---
### EFF.GENIND.178  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph (ANNEX R — r1's provenance and enumerated edit scope). verbatim, lines 3098–3115.

> “## ANNEX R — r1 (2026-08-10; the ANNEX R hostile pass's repair queue)
>
> **Provenance and scope.** The annex stack's scoped hostile pass
> (`GENIND_ANNEXR_pass_report.md`, 2026-08-10) returned **UNREFUTED,
> NOT CLEAN: 0 CRITICAL + 1 GAP + 2 MINOR** — GAP-1 = the
> full-vs-simple complement seam at R1.1's closure sentence; MINOR-1 =
> R1.3's undisplayed c-choice; MINOR-2 = two non-enumerative universal
> record sentences (close + R1.4). This r1 executes all three. The
> accepted body stays byte-frozen (lines 1–2548 md5 eefcf658,
> re-verified at this commit); the ANNEX R text above is edited at
> exactly five [ar1 2026-08-10]-tagged sites — the R1.1 closure rider,
> the R1.2 u_l rider, the R1.3 c-choice, the R1.4 enumeration, the
> close enumeration — plus one rider at R1.4's CS sentence below;
> every other annex line is unchanged. Repairs are RE-DERIVED from the
> note's own lemmas (GENIND-4's budgets, S7.1/S7.3's slot geometry,
> S5.1's criterion arithmetic, S5.3's entry tables, W-11's R(M) tie,
> R6.1's monotonicity); no verifier sentence is transcribed. Annex
> stack stays 0/2.”

**CONDITIONALITY:** **The annex layer gets its own hostile pass, and the pass finds a GAP in the repair that cured the heaviest GAP** — the recursion the whole arc exhibits. “no verifier sentence is transcribed” is a provenance guarantee (the repairs are the note's own derivations, not the verifier's prose).

**ARITHMETIC AUDIT:** “exactly five … sites … plus one rider” ✓ — five enumerated (R1.1 closure `.151`, R1.2 u_l `.152`, R1.3 c-choice `.153`, R1.4 enumeration `.154`, close enumeration `.172`) **plus one at R1.4's CS sentence (`.154`'s closing rider)** = six `[ar1]` tags in the layer ✓. Compiler check: this compilation carries `[ar1]` layers at exactly `.151`, `.152`, `.153`, `.154` (×2 — the MINOR-2 enumeration and the CS rider) and `.172` ✓ — **six, matching.**

**SUPERSESSION KIND:** the layer as a whole = `replacement` at five named sites + `inventory completion` (GENIND-C2 added).

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 3098–3115. correction sites: none for this paragraph.

**TEETH:** `in-house hostile pass` (scoped to the annex stack). **PIN VERIFICATION:** `lean/notes/openmath/GENIND_ANNEXR_pass_report.md` EXISTS ✓. **Compiler note for the merge:** a second report `lean/notes/openmath/GENIND_ANNEXR_pass2_report.md` also exists on disk and **is cited nowhere in the note** — the annex stack's “pass #2”, whose result the note (frozen at 2026-08-12) does not carry. Recorded as source defect 3 (§8): the annex stack's grade line “remains 0/2 … queues for its own scoped hostile pass” (`.186`) may be stale against the repo, and this compilation does not adjudicate it.

---
### EFF.GENIND.179  [supplier-finding]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph (r1.1's defect statement). verbatim, lines 3117–3127.

> “### r1.1 (GAP-1): ANNEX-LEMMA GENIND-C2 — the CS-drain rate
>
> **The defect, exactly.** GENIND.C′ (R1.3) proves the (A2-RATE) decay
> for the SIMPLE slice; (A2-RATE) as displayed (R1.1) pins the FULL
> complement u_{μ,d}(M). The difference — the mass that enters a CS
> event and stays conservative-undecided, the CS-STRATUM DRAIN — had
> exactness ((CS-EXACT)) but no displayed all-window rate, while
> GENIND-C1(iii)'s GROWING regime consumes the full member's rate at
> (4, d) children from n = 5 on. The entry mass alone cannot supply it:
> the CS entry loci have POSITIVE relative density (S5.2's own
> sentence), so the decay must come from inside the stage.”

**CONDITIONALITY:** **A seam between two of the same repair's own components** — C′ covers the simple slice, (A2-RATE) pins the full complement, and the CS-drain difference had no rate. **The last sentence is the sharp one: the decay cannot come from the entry mass, because the entry loci have positive relative density (shard 1 `.46`), so it must come from inside the stage** — which is what forces `.33`'s conditionality on (CS-1).

**ARITHMETIC AUDIT:** “from n = 5 on” — a (4, d) child requires a parent of degree > 4·d, first at n = 5 with d = 1 ✓; and a degree-4 system is the first that can bear CS (shard 1 `.11`) ✓, so the first CS-bearing child appears at n = 5 ✓. The positive-density claim is shard 1 `.46`'s, audited there (`Σ_h (q−1)q^{−5h−3}` is N-independent ✓).

**DERIVATION:** Not a mathematical unit; a defect report.

**RESOLUTION TRACE:** statement lines 3117–3127. correction sites: none.

**TEETH:** `in-house hostile pass` (the annex's own scoped pass).

---
### EFF.GENIND.180  [lemma]

**CANONICAL STATEMENT:** FORM: display (blockquote, ANNEX-LEMMA GENIND-C2 as first stated at r1.1). verbatim, lines 3129–3182. **This statement is SUPERSEDED IN FULL by the 2026-08-12 R9 replacement (`.189`) and then partly by R11 (`.198`); it is emitted because it is the version the r1 machine leg (`.185`) was preregistered and run against.**

> “> **ANNEX-LEMMA GENIND-C2 (the CS-drain rate; conditional on (CS-1)
> > only).** Fix (m, d) with m·d ≥ 4, window N, and a CS genre of the
> > S5.2 recursion's inventory: entry-height datum with v(a₀) = H on
> > the opening locus (the DRAIN-first key height; visibility floor
> > H ≤ N−1, R4's species), stage data (μ, e, ψ, E = e, K,
> > |K| = q^{d·deg ψ}) per S7.1. Assume, of [GENIND-H]'s clauses,
> > **(CS-1) only** — the stage count isomorphism with its slot
> > geometry (one K-digit per (abscissa, v′-height), E slots per
> > v-unit: COROLLARY W-9/JC-F1's dim_K 𝒜(T) = E; ragged-corrected
> > below the uniform threshold). Then the genre's conservative-drain
> > contribution to u_{m,d}(N) obeys the (A2-RATE) species. Precisely:
> >
> > (i) [stage window supply] the stage read is a (μ, K)-cluster read
> > at stage window M★ ≥ E·(N−1−H): every consulted slot string runs
> > from its node height (deepest = E·H) to the uniform boundary
> > E·(N−1) in v′-units; the visibility floor H ≤ N−1 is exactly
> > M★ ≥ 0. Instances: the (2,2)-E stage — GENIND-4's node
> > C(4h+1, 2h+1) in dv-units against S7.3's uniform boundary 2N−2,
> > H = 2h, so M★ = 2N−2−4h (the stage-α(2h) transported window, the
> > W-11 shape); genre F — H = 4k, v′ = v, M★ = N−1−4k over K = F_{q²}.
> >
> > (ii) [stage drain rate] at μ ≤ 3 the stage read is CS-FREE (S5.1's
> > criterion AT the stage: CS needs ≥ 4 keys and the stage has μ), so
> > GENIND.C′ applies to the whole stage complement: stage-drain
> > fraction ≤ K★·M★^{B★}·|K|^{−(M★−c★)}. At μ ≥ 4 (first possible at
> > m ≥ e·μ·deg ψ ≥ 8) recurse this lemma jointly with C′: the stage's
> > product-degree μ·(d·deg ψ) ≤ m·d (S5.1's side-length arithmetic
> > m ≥ e·μ·deg ψ) and its window M★ < N — CS legs enter GENIND.C′'s
> > lexicographic (degree, window) induction exactly as α-legs do.
> >
> > (iii) [composition at slope ≥ 2] drain contribution ≤ (entry
> > relative mass ρ) × (stage drain fraction): decided split-off pieces
> > contribute no drain, and at MIXED genres (stage + β-children
> > coexisting, first at n = 6) the frame drain composes by
> > GENIND-6(d)'s inclusion–exclusion, bounded by the union bound as in
> > GENIND-C1(ii) — bounds propagate by R6.2's separation, no
> > (CS-EXACT) needed. In original q-units,
> > |K|^{−(M★−c★)} ≤ q^{−(e·d·deg ψ)·(N−1−H)+O(1)} with
> > **e·deg ψ ≥ 2 — the CS-DEFINING inequality (S5.1's necessity
> > arithmetic)**: a composite stage certifies at least TWO q-digits
> > per remaining window unit. The entry mass ρ decays geometrically in
> > H (the entry laws are order-1 W-12.A-priced shapes: S5.3's tables
> > at n = 4, 5; S5.2's exactly-known entry mass at general n), so the
> > height sum converges and the genre count is ≤ p̃(m)·N^m
> > (GENIND-C1(iv)'s species). Summing:
> >
> >     CS-drain part of u_{m,d}(N)/Q^{m(N−1)} ≤ K_c·N^{B_c}·q^{−(N−c_c)},
> >
> > with window-deficit slope ≥ 2 where the stage window is live and
> > ≥ 5/2 from the entry mass alone at floor-adjacent strata (E:
> > ρ = (q−1)q^{1−5h} at 2h ≥ N−2; F: (q(q−1)/2)q^{−10k} at
> > 4k ≥ N−2) — the crossover is the visibility floor. In particular
> > an n = 4 CS drain at window-deficit slope < 1 is excluded twice
> > over. ∎”

**CONDITIONALITY:** **SUPERSEDED IN FULL.** Two defects were found later and both are real:
1. **The d-factor defect (R9, `.188`):** “the preceding stage calculation retained \(d\), but the conclusion changed from \(Q=q^d\) to \(q\)” — visible in the displayed conclusion `≤ K_c·N^{B_c}·q^{−(N−c_c)}` against the normalization `Q^{m(N−1)}`.
2. **The stage-window scalar bound (R11, `.196`):** `M★ ≥ e(N−1−H)` is **WITHDRAWN for general embedded and mixed genres**, because (CS-1) supplies ragged per-coordinate windows and permits sibling-Hensel losses without pricing them.
Also withdrawn implicitly: (ii)'s equal-product-degree descent sentence “its window M★ < N”, replaced by a truncation argument (`.202`).

**SUPERSESSION KIND:** received `replacement` (R9, full) then `replacement` again at three named parts (R11).

**CHAIN:** **this statement → R9's Q-normalized GENIND-C2 (`.189`) → R11's C2Q under (CS-1Q) (`.198`) — TERMINAL.** A chapter cut must NOT read this version; it survives only as the object the r1 machine leg was run against.

**ARITHMETIC AUDIT (compiler-computed, on the defect R9 names):** the normalization is `u/Q^{m(N−1)}` with `Q = q^d`; (ii)'s stage estimate is in `|K| = q^{d·deg ψ}` and (iii) converts it to `q^{−(e·d·deg ψ)(N−1−H)}`, retaining d ✓ — **but the displayed conclusion writes `q^{−(N−c_c)}`, base q, against a `Q^{m(N−1)}` denominator.** At `d ≥ 2` the two disagree by a factor `q^{(d−1)(N−c_c)}` ✓ — **the d-factor defect is real and exactly as R9 describes.** The instance displays (E: `M★ = 2N−2−4h` with `H = 2h`, so `E(N−1−H) = 2(N−1−2h) = 2N−2−4h` ✓; F: `M★ = N−1−4k` with `E = 1, H = 4k` ✓) are consistent with the withdrawn scalar bound at `d = 1` ✓.

**DERIVATION:** Displayed. Superseded; the live derivations are `.189` and `.198`.

**RESOLUTION TRACE:** statement lines 3129–3182. correction sites: 3298–3317 and 3319–3557 (R9, `.188`/`.189`); 3592–3721 (R11, `.196`–`.200`).

**TEETH:** the r1 machine leg (`.183`, `.185`) — **preregistered and run against THIS version**, which is why the version is emitted rather than dropped.

XREF: `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md:COROLLARY W-9` — count **2**; `JC-F1` — count **18**; `dim_K 𝒜(T) = E` — count **3**.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:THEOREM W-12.A` — count **8**.

---
### EFF.GENIND.181  [instance-record]

**CANONICAL STATEMENT:** FORM: bold-headed bulleted display (r1.1's displayed instances at n = 4, 5). verbatim, lines 3184–3195.

> “**Displayed instances (n = 4, 5 — the degrees C1 first consumes).**
> * CS4-E(h): ρ = (q−1)q^{1−5h}, M★ = 2N−2−4h, |K| = q: composed
>   contribution ≤ poly(N)·q^{−(2N+h)+O(1)} — h-sum geometric.
> * CS4-F(k): ρ = (q(q−1)/2)·q^{−10k}, M★ = N−1−4k, |K| = q²: composed
>   ≤ poly(N)·q^{−(2N+2k)+O(1)}.
> * CS5-V1E2(h): entry_rel = (q−1)q^{2−(15h+1)/2}·(1−q^{−(N−(5h+1)/2)})
>   — constant-order in N (the S5.2 positive-density display; the
>   fifth root's headroom fiber is a DECIDED piece) — times the same
>   (2,2)-E stage at M★ = 2N−2−4h: composed ≤ poly(N)·q^{−2N+O(h)};
>   the N-decay comes entirely from inside the stage. CS5-V4E2 and the
>   S5.3 siblings: same composition species (entry geometric in its
>   height data × a (2,2)-type stage), displayed by the table.”

**CONDITIONALITY:** Superseded by R9's corrected checks (`.190`), which re-display the same three instances in `Q`-units. **The exponents are unchanged at d = 1**, which R9's own audit confirms.

**ARITHMETIC AUDIT (compiler-computed):**
* CS4-E: `ρ` = law/total = `(q−1)q^{4N−5h−3}/q^{4(N−1)} = (q−1)q^{1−5h}` ✓. Composed: `ρ·q^{−|K|-exponent}` with `|K| = q` and `M★ = 2N−2−4h` gives `q^{1−5h}·q^{−(2N−2−4h)} = q^{−2N+3−h}` ✓ = `q^{−(2N+h)+O(1)}` ✓.
* CS4-F: `ρ = (q(q−1)/2)q^{4N−10k−4}/q^{4N−4} = (q(q−1)/2)q^{−10k}` ✓. Composed with `|K| = q²`, `M★ = N−1−4k`: `q^{−10k}·q^{−2(N−1−4k)} = q^{−2N+2−2k}` ✓ = `q^{−(2N+2k)+O(1)}` ✓.
* CS5-V1E2: entry_rel = law/total = `(q−1)q^{4N−5h−3}(q^{N−(5h+1)/2}−1)/q^{5(N−1)}` = `(q−1)q^{−N−5h+2}(q^{N−(5h+1)/2}−1)` = `(q−1)q^{2−5h−(5h+1)/2}(1 − q^{−(N−(5h+1)/2)})` = `(q−1)q^{2−(15h+1)/2}(1−q^{−(N−(5h+1)/2)})` ✓ **exactly the displayed form** (since `5h + (5h+1)/2 = (15h+1)/2` ✓). Composed: constant-order × `q^{−(2N−2−4h)}` = `q^{−2N+O(h)}` ✓.
**All three displayed compositions re-derive exactly.**

**DERIVATION:** Instantiation of `.180`.

**RESOLUTION TRACE:** statement lines 3184–3195. correction sites: 3508–3541 (R9's corrected checks, `.190`).

**TEETH:** the r1 machine leg's P1–P4 (`.185`).

---
### EFF.GENIND.182  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (r1.1's conditionality). verbatim, lines 3197–3208.

> “**Conditionality, honestly.** GENIND-C2 consumes (CS-1) ONLY — not
> (CS-2), not (CS-3), not (CS-EXACT). At n = 4,
> (CS-1) is de facto discharged (GENH4 @ r3 4b0d946 per Step 4's [r3]
> record: GENIND-4 + GENH4-1F + GENH4-2/-3/-4), so u_{4,d}'s FULL
> (A2-RATE) — the member C1(iii) consumes at n = 5 — rides pinned
> theorems. At n ≥ 5 the CS-drain leg is conditional on (CS-1) ⊂
> [GENIND-H(n)], the box GENIND.B's reduction ALREADY assumes: the
> closure sentence "P(k)-with-(A2-RATE) closes under GENIND.B's strong
> induction" now holds at the theorem's own conditionality, with no
> new hypothesis. Rider on R1.4's last sentence: the CS legs keep
> [GENIND-H]/(CS-EXACT) for menu + exactness; their RATE is GENIND-C2
> under (CS-1) alone.”

**CONDITIONALITY:** **“with no new hypothesis” is the claim R11 later overturns.** The R11 certification-status paragraph (`.199`) replaces “(CS-1) only” with “(CS-1Q), verified per genre” and states that the displayed (CS-1) does **not** establish (CS-1Q.b) for embedded or mixed genres — **so the closure DOES rest on more than the box GENIND.B already assumes, at those genres.** This is the single most important supersession in the shard.

**SUPERSESSION KIND:** received `replacement` (of the conditionality label) — audited at `.199`.

**CHAIN:** “(CS-1) ONLY … with no new hypothesis” → **R11: “(CS-1Q), verified per genre”; “A universal discharge for embedded and mixed genres remains obstructed” — TERMINAL.**

**TARGETS:** shard 1 `.13`, `.37`, `.57`, `.63`; `.04`, `.05` here.

**DERIVATION:** Not a mathematical unit; a conditionality declaration.

**RESOLUTION TRACE:** statement lines 3197–3208. correction sites: 3712 and 3714–3721 (`.199`, `.200`).

**TEETH:** the n = 4 de facto discharge is a citation (shard 1 `.59`, `.66`), riding GENH4's accepted body; the n ≥ 5 leg is `signed vacuity disclosure`.

XREF: `lean/notes/openmath/GENH4_PROOF_2026-08-08.md:GENH4-1F` — count **10**; `GENH4-2` — count **15**.

---
### EFF.GENIND.183  [preregistration]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (r1.1's two-commit machine seal, PENDING — a preregistration with teeth and a roster). verbatim, lines 3210–3226.

> “**Machine leg (two-commit seal; PENDING at this commit).**
> `verification/openmath/genind_annexr1_checks.py`, sealed UNRUN with
> preregistered checks P1 (per-stratum window bound
> UND ≤ entry·M★·|K|^{−(M★−1)} at 10 scored fresh rows), P2 (species
> bound at (K,B,c) = (1,1,2) per swept (q,N)), P3 (slope: consecutive-N
> relative-drain ratio ≤ q^{−3/2} — kills slope ≤ 1; expected ≈ q^{−3}),
> P4 (the CS5-V1E2 entry identity + composed n = 5 bound, sympy + grid
> to N = 40), P5 (C1(iii)'s D+M = N composition identity, sympy), and
> teeth T-SLOPE (a fabricated slope-1/2 n = 4 drain — the pass report's
> failure scenario made flesh — must violate P1) and T-WIN (a
> mis-derived stage window 2N−2−2h must be refuted by the committed
> deep row (Zp, 2, 11, h = 5) of the GENH4 battery). Fresh rows are
> walked by the PINNED GENH4 sealed walker (read-only; its own per-row
> checks stay live and must stay silent), roster E: q=2 h=1 N=4..7,
> q=2 h=3 N=8..9, q=3 h=1 N=4..5; F: q=2 k=1 N=7..9, q=3 k=1 N=6
> (schedule: floor-adjacent, P2 only). Verdict from committed artifacts at
> commit 2.”

*(Compiler note: the parenthetical at the last roster entry reads “(floor-adjacent, P2 only)” in the source; the word “schedule:” is NOT in the source and is a transcription slip in this quotation — **corrected here**: the source reads “q=3 k=1 N=6 (floor-adjacent, P2 only)”. Flagged rather than silently fixed, per the fidelity rules.)*

**CONDITIONALITY:** **A genuine two-commit preregistration with two armed teeth**, one of which (“T-SLOPE — the pass report's failure scenario made flesh”) instantiates the verifier's own worry as a mutant. **“P1 … at 10 scored fresh rows” is corrected to 11 by R9's riding MINOR-A** (`.192`).

**ARITHMETIC AUDIT (compiler-computed):** roster E rows: (2, h=1, N=4..7) = 4 + (2, h=3, N=8..9) = 2 + (3, h=1, N=4..5) = 2 → **8**; roster F rows: (2, k=1, N=7..9) = 3 + (3, k=1, N=6) = 1 → **4**; total **12 fresh rows** ✓ — matching `.185`'s “the 12th, F q=3 N=6, is floor-adjacent M★ = 1: disclosed, not scored” and hence **11 scored** ✓, which is MINOR-A's correction. **The preregistered “10” is wrong against the note's own roster arithmetic** ✓ — MINOR-A is right.
Check the floor-adjacency: at `(q, k, N) = (3, 1, 6)`, `M★ = N−1−4k = 6−1−4 = 1` ✓ floor-adjacent.
T-WIN's control row `(Zp, 2, 11, h = 5)`: the correct window is `M★ = 2N−2−4h = 22−2−20 = 0`… **recomputed: `2·11 − 2 − 4·5 = 0`**, while the mis-derived `2N−2−2h = 22−2−10 = 10`. So the tooth contrasts a true window of 0 against a wrong window of 10 ✓ — and `.185` reports the tooth firing with “UND 32,768 vs wrong-window bound 1,280” ✓, consistent with a wrong window that is far too generous.

**DERIVATION:** Not a mathematical unit; a preregistration.

**RESOLUTION TRACE:** statement lines 3210–3226. correction sites: 3561 (R9's riding MINOR-A, `.192`).

**TEETH:** this unit IS the tooth specification; `.185` is its scoring. **PIN VERIFICATION:** `verification/openmath/genind_annexr1_checks.py` EXISTS ✓, with `_output.txt` ✓ and `_results.json` ✓.

---
### EFF.GENIND.184  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + paragraph (r1.2 and r1.3, executed inline). verbatim, lines 3228–3235.

> “### r1.2 (MINOR-1) and r1.3 (MINOR-2): executed inline
>
> MINOR-1: the c-choice c := c′ + 1 displayed at source in R1.3 (the
> β-leg exponent absorbed exactly; head leg at c ≥ 1; no circularity —
> c′ is degree-induction data). MINOR-2: both record sentences
> rewritten enumeratively at their sites (R1.4: the five consulted
> displays named; close: the four consulted pins + the five annex
> commits named). No further annex sentence was touched in r1.2/r1.3.”

**CONDITIONALITY:** Both executed; both audited at their sites (`.153`, `.154`, `.172`). The closing sentence is an enumerative scope claim (rule-compliant).

**ARITHMETIC AUDIT:** “the five consulted displays” ✓ (`.154`), “the four consulted pins + the five annex commits” ✓ (`.172`) — **all three numerals reconcile with their enumerations.**

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 3228–3235. correction sites: 3563 (MINOR-B later replaces R1.4's five-display census, `.193`).

**TEETH:** `arithmetic recount`.

---
### EFF.GENIND.185  [run-record]

**CANONICAL STATEMENT:** FORM: bold-headed bulleted display (r1's machine record at commit 2, including one FLAGGED line and a RED exit). verbatim, lines 3237–3283.

> “**Machine record (2026-08-10, commit 2 — FROM the committed artifacts
> `genind_annexr1_output.txt` / `genind_annexr1_results.json`; single
> run, no check edited after any output was seen).**
> * Pins: genh4_checks.py ee8024b7 (the sealed GENH4 battery walker,
>   imported read-only; its own per-row law checks — GH-FRESH
>   volume/law ties, GH-UND, GH-BRACKET — ran live at all 12 fresh rows
>   and flagged nothing at any of the 12); genh4_checks_results.json
>   cbcff562; genind_checks.py e7ca150b. 144 preregistered checks
>   (PIN 4 + P1 11 + P2 9 + P3 7 + P4 112 + P5 1): 143 GREEN, 1
>   flagged (adjudicated below); both teeth FIRED.
> * **P1 GREEN 11/0** — the window bound UND ≤ entry·M★·|K|^{−(M★−1)}
>   at all 11 scored fresh rows (the 12th, F q=3 N=6, is
>   floor-adjacent M★ = 1: disclosed, not scored).
> * **P2 GREEN 9/0** — the species bound at (K,B,c) = (1,1,2) at every
>   swept (q,N); margins 10²–10⁴.
> * **P3 6-of-7 + the headline numbers** — genre E's measured
>   window-deficit slope is EXACTLY 2.00 at every consecutive pair:
>   q=2 h=1, UND_rel 2^{−7} → 2^{−9} → 2^{−11} → 2^{−13} at
>   N = 4→5→6→7; q=2 h=3 at 8→9; q=3 h=1 ratio 3^{−2} at 4→5 — the
>   lemma's slope-≥2 claim measured on the nose, slope < 1 excluded
>   with a full q^{±1} margin at 5 of the 7 pairs and q^{±1/2} at the
>   flagged one. **The 1 flagged line (F q=2 k=1, N 7→8: ratio 0.5 =
>   single-step slope 1.00 > the preregistered cap q^{−3/2}) is an
>   INSTRUMENT CAP LITERAL, adjudicated NOT a counter-instance:** the
>   odd→even step is exactly where GENH4.B's committed TWO-term even-N
>   display lands (the CAP(F) boundary band (q−1)q^{N+2k−1} — the same
>   granularity the box's (CS-EXACT) [r2, PE2-m1] correction names).
>   The run's own next step measures slope 3.00 (8→9: ratio 0.125);
>   the parity-PAIRED run data give UND_rel 2^{−15} → 2^{−19} over
>   N = 7→9, i.e. slope 2.00 per step; and the committed und_F law
>   closes it by hand (decorrelated leg): the main term
>   q^{2⌊N/2⌋+2k−1} steps by q²·q⁰ on alternating parities and the
>   even-N extra term is q^{−3N+12k+3+N mod 2} in relative mass —
>   per-stratum paired slope 3.00. The preregistered SINGLE-step cap
>   was miscalibrated for genre F's parity band; no BOUND check
>   (P1/P2) fails at any of the 12 rows. The instrument's own strict
>   gate therefore printed RED (1 violation, script exit 1); artifacts
>   kept byte-frozen as run, per the run-1-RED precedent.
> * **P4 GREEN 112/0** — the CS5-V1E2 entry identity (sympy) + the
>   composed n = 5 drain bound on the grid q ∈ {2,3,7}, N ≤ 40.
> * **P5 GREEN 1/0** — C1(iii)'s D + M = N exponent composition
>   (sympy).
> * **Both teeth FIRED**: T-SLOPE — the pass report's failure scenario
>   made flesh, a fabricated slope-1/2 n = 4 E-drain (262,144) violates
>   the P1 bound (65,536) at (2,7,1); T-WIN — the mis-derived window
>   2N−2−2h is refuted by the committed deep row (Zp,2,11,h=5):
>   UND 32,768 vs wrong-window bound 1,280.”

**CONDITIONALITY:** **A RED run kept and disclosed rather than re-run** — “the instrument's own strict gate therefore printed RED (1 violation, script exit 1); artifacts kept byte-frozen as run, per the run-1-RED precedent”. **The adjudication is that the CAP was miscalibrated, not that the lemma failed**, and it is supported three ways (the next step's slope 3.00; the parity-paired slope 2.00; a by-hand decorrelated derivation from the committed und_F law). **This is the honest handling of a failed preregistered check and should be read as such: the note did not move the goalposts silently — it printed RED, kept the artifact, and argued the adjudication in the open.**

**ARITHMETIC AUDIT (compiler-computed; every displayed number checked):**
* **Check tally:** `PIN 4 + P1 11 + P2 9 + P3 7 + P4 112 + P5 1 = 144` ✓ **exact**; `143 GREEN + 1 flagged = 144` ✓.
* **P3 genre-E slopes:** `2^{−7} → 2^{−9} → 2^{−11} → 2^{−13}` — each step a factor `2^{−2}` ✓ = slope 2.00 per window ✓ at q = 2, h = 1, N = 4→7 (three steps, four values ✓). At q = 3: ratio `3^{−2}` ✓ = slope 2.00 ✓.
* **The flagged F line:** ratio 0.5 = `2^{−1}` = single-step slope 1.00 ✓ > the cap `q^{−3/2} = 2^{−1.5}` ✓ (0.5 > 0.354) — **the check genuinely fails as preregistered.**
* **The adjudication's arithmetic:** the next step's ratio 0.125 = `2^{−3}` = slope 3.00 ✓; the paired data `2^{−15} → 2^{−19}` over two windows = `2^{−4}` = **slope 2.00 per step** ✓; **so the two-window average is 2.00 and the parity oscillation is (1.00, 3.00)** ✓ — arithmetically consistent, and the mean is exactly the lemma's claimed slope ≥ 2 ✓.
* **T-SLOPE:** `262,144 = 2^{18}` against the P1 bound `65,536 = 2^{16}` ✓ — a factor 4 violation ✓, the mutant fires ✓.
* **T-WIN:** `UND 32,768 = 2^{15}` against the wrong-window bound `1,280` ✓ — the wrong window under-bounds by a factor 25.6 ✓, so the tooth fires ✓.
* **Roster:** 12 fresh rows ✓ (audited at `.183`); 11 scored + 1 disclosed ✓.
* **Compiler observation on the flagged line's adjudication.** The three supports are: (a) the next step measures 3.00; (b) the paired data give 2.00/step; (c) a by-hand derivation from the committed und_F law gives per-stratum paired slope 3.00. **(b) and (c) do not agree with each other** — (b) says 2.00 per step over the pair, (c) says “per-stratum paired slope 3.00”. Both may be true of different quantities (a run-level relative mass versus a per-stratum law), but **the note does not reconcile them**, and the compiler cannot from the displayed data. **Recorded as a disclosed non-reconciliation (§8, defect 4), NOT as an error** — no BOUND check fails at any row, which is the load-bearing fact.

**DERIVATION:** Not a mathematical unit; an executed instrument's result.

**RESOLUTION TRACE:** statement lines 3237–3283. correction sites: 3561 (MINOR-A corrects the preregistration's “10 scored rows” to 11, `.192`).

**TEETH:** two planted mutants, both fired; five preregistered checks, four fully GREEN and one flagged with an open adjudication. Disposition: **executable regression with a `disclosed non-repair`** (the miscalibrated cap is not re-preregistered) and an `accepted-with-decorrelation-supplied` for the adjudication's by-hand leg.

**PIN VERIFICATION:** the three artifacts EXIST ✓; the GENH4 walker `verification/openmath/genh4_checks.py` — **verified to EXIST ✓** (md5 pins `ee8024b7`, `cbcff562` are the note's values, not re-computed here).

---
### EFF.GENIND.186  [changes-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (r1's grade line). verbatim, lines 3285–3294.

> “**r1 grade line.** GAP-1's PROVE-FIRST charge LANDED: the CS-drain
> rate is DERIVED (GENIND-C2, conditional on (CS-1) only — within the
> box the closure sentence's theorem already assumes, de facto at
> n = 4), not re-scoped; the n = 4 machine instances measure the
> derived slope-2 mechanism exactly, and the failure scenario (an
> n = 4 CS drain at window-deficit slope < 1) is excluded by P1 at 11
> scored rows, by the measured slopes at 7 ratio pairs, and by the
> fired T-SLOPE tooth. MINOR-1 and MINOR-2 executed inline. The annex
> stack remains 0/2 — this r1 answers the ANNEX R pass and queues for
> its own scoped hostile pass behind the chain notes.”

**CONDITIONALITY:** **“conditional on (CS-1) only” is superseded by R11** (`.199`), so this grade line's central claim is **STALE (uncured)** — the CS-drain rate is now conditional on (CS-1Q), verified per genre, and “A universal discharge for embedded and mixed genres remains obstructed”. The line is not edited. Tagged `STALE-SELF-DESCRIPTION (uncured)` (rule 26). **“The annex stack remains 0/2”** is the grade a chapter cut must carry for everything in this shard.

**ARITHMETIC AUDIT:** “P1 at 11 scored rows” ✓, “7 ratio pairs” ✓ (P3's count), “the fired T-SLOPE tooth” ✓ — all three consistent with `.185`.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 3285–3294. correction sites: none in place; overtaken at 3712 (`.199`).

**TEETH:** as `.185`.

---
### EFF.GENIND.187  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + paragraph (the 2026-08-12 R9 correction's provenance). verbatim, lines 3298–3306.

> “### Dated corrections (2026-08-12 — sol certification R9: the annex-pass d-factor GAP repaired at HEAD)
>
> The sol-5.6 annex read (runs/residues/R1_drainn4_output.log,
> 2026-08-12) found the d-factor GAP in ANNEX-LEMMA GENIND-C2 plus
> three riding MINORs. The R9 certification run (gpt-5.6-sol high,
> runs/cert/R9_drain_repair_output.log) re-adjudicated all four
> against HEAD (all REAL) and derived the repairs — the dated
> replacement passage and three riding folds below. Everything above
> this heading is byte-untouched by this append.”

**CONDITIONALITY:** **A second decorrelated-model channel** (the sol certification campaign) finding a real defect in a repair that had already survived a scoped hostile pass. **All four findings re-adjudicated REAL against HEAD.**

**DERIVATION:** Not a mathematical unit; a provenance record.

**RESOLUTION TRACE:** statement lines 3298–3306. correction sites: none.

**TEETH:** **`decorrelated-model audit`.** **PIN VERIFICATION:** `runs/residues/R1_drainn4_output.log` — **EXISTS ✓** (the directory `runs/residues/` is present in the working tree); `runs/cert/R9_drain_repair_output.log` — **EXISTS ✓**. Both are run logs, not commits.

---
### EFF.GENIND.188  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph (the R9 replacement's supersession declaration and defect statement). verbatim, lines 3308–3317.

> “### Dated correction (2026-08-12): ANNEX-LEMMA GENIND-C2 — the residue-degree factor retained through the height sum
>
> **Supersession and scope.** This passage supersedes r1.1's
> ANNEX-LEMMA GENIND-C2 statement, proof, displayed instances, and
> conditionality paragraph. The defect was confined to the last
> normalization and height summation: the preceding stage calculation
> retained \(d\), but the conclusion changed from \(Q=q^d\) to \(q\).
> The repair below keeps \(Q\) from entry pricing through the final
> sum. No accepted theorem statement is weakened; no count law or
> frozen number moves.”

**CONDITIONALITY:** **A full-statement supersession with a precisely localized defect** — “confined to the last normalization and height summation”. The scope claim (“No accepted theorem statement is weakened”) is true: GENIND-C2 is annex material, not accepted-body material.

**SUPERSESSION KIND:** `replacement` — statement, proof, instances and conditionality, all four, of `.180`/`.181`/`.182`.

**TARGETS:** `.180`, `.181`, `.182`.

**ARITHMETIC AUDIT:** the defect as described is exactly what the compiler independently found at `.180` (the conclusion displays base q against a `Q^{m(N−1)}` denominator, disagreeing by `q^{(d−1)(N−c_c)}` at `d ≥ 2`) ✓ — **the localization is right and the compiler's independent recount agrees with the finding.**

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 3308–3317. correction sites: 3592–3721 (R11's partial re-supersession, `.196`).

**TEETH:** `decorrelated-model audit`.

---
### EFF.GENIND.189  [lemma]

**CANONICAL STATEMENT:** FORM: **display (blockquote) with LaTeX tagged equations** — the R9-replaced ANNEX-LEMMA GENIND-C2 (Q-normalized), statement and proof. verbatim, lines 3319–3506. Quoted in full below with its `\tag{}` anchors intact (rule: the tags are the addressable objects a chapter cut needs).

> “> **ANNEX-LEMMA GENIND-C2 (the CS-drain rate, \(Q\)-normalized;
> > conditional on the (CS-1) clause family only).** Fix a cluster
> > system \((m,d,N)\), put \(Q:=q^d\), and fix a composite block in a
> > CS genre. Write
> >
> > \[
> >   \gamma:=\deg\psi,\qquad a:=e\gamma,\qquad
> >   L:=e\mu\gamma,\qquad |K|=q^{d\gamma}=Q^\gamma .
> > \]
> >
> > Thus \(a\ge2\), \(\mu\ge2\), and
> >
> > \[
> >   L\ge2a,\qquad
> >   b:=\frac{L+1}{2}\ge a+\frac12.                 \tag{C2.0}
> > \]
> >
> > Let \(H\) be the vertical drop of the side carrying the composite
> > block. On a full side \(H=v(a_0)\); at an embedded side the other
> > sides and split-off pieces impose additional conditions and can
> > only decrease the relative entry mass. Assume (CS-1) for this
> > stage and, recursively, for any composite stages occurring inside
> > it. Then the contribution in which this stage remains
> > conservative-undecided satisfies
> >
> > \[
> >   \frac{u^{\mathrm{CS}}_{m,d}(N)}
> >        {Q^{m(N-1)}}
> >       \le K_c N^{B_c}Q^{-(N-c_c)}
> > \]
> >
> > for constants \(K_c,B_c,c_c\) depending only on the fixed
> > degree/genre data.
> >
> > **Proof.**
> >
> > **(i) Stage-window supply in \(Q\)-units.** By (CS-1), the stage is
> > a \((\mu,K)\)-cluster read at a ragged-corrected stage window
> > \(M^\star\) satisfying \(M^\star\ge e(N-1-H)\). This is S7.1's
> > slot geometry: one \(K\)-digit per \(v'\)-height, \(E=e\) such
> > heights per old valuation unit. At the quartic e-first stage, for
> > example, \(M^\star=2N-2-4h=2(N-1-H)\) with \(H=2h\).
> >
> > **(ii) Stage-drain rate.** If \(\mu\le3\), the stage is CS-free by
> > S5.1, so GENIND.C′ applied over \(K\) gives
> > \(\delta_{\mathrm{stage}}(M^\star)\le K_\star(M^\star)^{B_\star}|K|^{-(M^\star-c_\star)}\).
> > If \(\mu\ge4\), use the same estimate by joint lexicographic
> > induction with GENIND.C′ and this lemma. Indeed \(\mu d\gamma\le md\)
> > follows from \(m\ge e\mu\gamma\); when equality of product degrees
> > is possible (\(e=1\)), the visible opening has \(H>0\), hence
> > \(M^\star<N\). Thus either degree or window strictly decreases.
> > In terms of \(Q\), part (i) gives
> > \(\delta_{\mathrm{stage}}(M^\star)\le K_\star N^{B_\star}(Q^\gamma)^{-(M^\star-c_\star)}
> > \le K_\star N^{B_\star}Q^{-e\gamma(N-1-H)+\gamma c_\star}
> > =K_\star N^{B_\star}Q^{-a(N-1-H)+\gamma c_\star}\). \tag{C2.1}
> >
> > **(iii) Entry pricing and the missing height comparison.** S2.2's
> > slot count supplies, for fixed side/partition data,
> > \(\rho_H\le Q^{-bH+C_0}\), \(b=\frac{L+1}{2}\) \tag{C2.2},
> > with \(C_0=O_m(1)\). Indeed, relative to the right endpoint, the
> > supporting line forces the \(L\) coefficient valuations at heights
> > \(\frac{H}{L},\frac{2H}{L},\ldots,\frac{LH}{L}\); their sum is
> > \(\sum_{r=1}^{L}\frac{rH}{L}=\frac{L+1}{2}H=bH\).
> > Passing to lattice ceilings and remembering that the level-zero
> > digits are already pinned changes this by only \(O_m(1)\) slots;
> > the residual-factor and letter census contributes only another
> > \(Q^{O_m(1)}\). Extra sides, vertices, and decided pieces add
> > constraints, so ignoring them is a valid upper bound.
> >
> > Combining (C2.1) and (C2.2), the normalized contribution at height
> > \(H\), while the stage-window estimate is live, is
> > \(\rho_H\,\delta_{\mathrm{stage}}(M^\star)
> > \le K_1N^{B_\star}Q^{-bH-a(N-1-H)+C_1}
> > =K_1N^{B_\star}Q^{-a(N-1)-(b-a)H+C_1}
> > \le K_1N^{B_\star}Q^{-a(N-1)-H/2+C_1}\), \tag{C2.3}
> > where the last inequality is exactly (C2.0):
> > \(b-a=\frac{L+1}{2}-e\deg\psi\ge\frac12\).
> > Thus the stage factor's growth with \(H\) is strictly dominated by
> > the entry-price decay; entry decay alone was not the reason the
> > height sum converges.
> >
> > **(iv) Height summation, retaining \(Q=q^d\).** Summing (C2.3)
> > gives \(\sum_H \rho_H\,\delta_{\mathrm{stage}}(M^\star)
> > \le K_1N^{B_\star}Q^{-a(N-1)+C_1}\sum_{H\ge0}Q^{-H/2}
> > \le K_2N^{B_\star}Q^{-a(N-1)+C_1}\) \tag{C2.4},
> > because \(Q\ge2\) and \(\sum_{H\ge0}Q^{-H/2}\le(1-2^{-1/2})^{-1}\).
> > Since \(a=e\deg\psi\ge2\), the right side is
> > \(\le K_2N^{B_\star}Q^{-(N-c_2)}\) for an \(N\)-independent \(c_2\).
> >
> > For the floor-adjacent range in which the quantitative stage
> > estimate is not invoked, fix its finite threshold \(M_0\).
> > From \(M^\star\ge e(N-1-H)\) and \(M^\star<M_0\) one gets
> > \(H>N-1-\frac{M_0}{e}\). The trivial stage-drain bound \(1\),
> > together with (C2.2), then gives
> > \(\rho_H\le Q^{-b(N-1)+O_{m,M_0}(1)}\le Q^{-(N-c_3)}\),
> > since \(b\ge a+\tfrac12\ge\tfrac52\). Hence the boundary range has
> > the same required species without using a child-window limit.
> >
> > Finally, for fixed \(m\), GENIND-C1(iv) gives at most
> > \(\widetilde p(m)N^m\) live genre/height arrangements. Multiplying
> > (C2.4) by this polynomial and summing over the finitely many
> > composite blocks preserves the form \(K_cN^{B_c}Q^{-(N-c_c)}\).
> >
> > At MIXED genres, the stage-drain term and the β-child drain terms
> > combine by GENIND-6(d); the union bound of GENIND-C1(ii)/R6.2
> > applies. The child terms are supplied by GENIND-C1 and the stage
> > terms by the calculation above. No use of (CS-EXACT) is made:
> > this is a bound, not the exact-complement identity. ∎”

*(Quotation note: the source displays each equation in its own `\[ … \]` block on separate lines; the quotation above preserves every symbol, every `\tag{}` and every inequality direction, and compresses only the line breaks inside multi-line `aligned` environments. No content is elided; nothing is `…`-truncated.)*

**CONDITIONALITY:** **Superseded in three named parts by R11** (`.196`): C2(i)'s scalar stage-window bound is **WITHDRAWN** for general embedded and mixed genres; C2(ii)'s equal-product-degree descent sentence is replaced by a truncation argument; C2(iii)'s entry-pricing display is replaced by one using the ACTUAL side length. **What survives R11 unchanged: the Q-normalization (the whole point of R9), the (C2.0) domination `b − a ≥ 1/2`, and the height-sum convergence.**

**SUPERSESSION KIND:** received `replacement` at three named parts.

**CHAIN:** `.180` (r1.1's version) → **this (R9, Q-normalized)** → R11's C2Q (`.198`) with (CS-1Q) — **TERMINAL.**

**ARITHMETIC AUDIT (compiler-computed; every tagged display re-derived):**
* **(C2.0).** `L = eμγ` with `μ ≥ 2` gives `L ≥ 2eγ = 2a` ✓. Then `b = (L+1)/2 ≥ (2a+1)/2 = a + 1/2` ✓.
* **`a ≥ 2`:** `a = eγ = e·deg ψ ≥ 2` is the CS-defining inequality (shard 1 `.11`) ✓.
* **(C2.1).** `|K| = Q^γ`, so `|K|^{−(M★−c★)} = Q^{−γM★+γc★}`; with `M★ ≥ e(N−1−H)`, `−γM★ ≤ −γe(N−1−H) = −a(N−1−H)` ✓ — giving `Q^{−a(N−1−H)+γc★}` ✓ **as displayed.**
* **(C2.2)'s supporting-line sum.** `Σ_{r=1}^{L} rH/L = (H/L)·L(L+1)/2 = (L+1)H/2 = bH` ✓ **exact.**
* **(C2.3).** `−bH − a(N−1−H) = −a(N−1) − (b−a)H` ✓; and `(b−a) ≥ 1/2` gives `≤ −a(N−1) − H/2` ✓.
* **(C2.4).** `Σ_{H≥0} Q^{−H/2} = (1−Q^{−1/2})^{−1} ≤ (1−2^{−1/2})^{−1}` for `Q ≥ 2` ✓ ≈ 3.414 ✓.
* **The final species.** `a ≥ 2` gives `Q^{−a(N−1)} ≤ Q^{−2(N−1)} ≤ Q^{−(N−c₂)}` for suitable `c₂` ✓ — **and note this is where the slope-≥2 claim of `.33` becomes visible: the exponent is `a(N−1)` with `a ≥ 2`, i.e. window-deficit slope ≥ 2** ✓, matching the r1 machine leg's measured 2.00 (`.38`) ✓.
* **The floor-adjacent branch.** `M★ ≥ e(N−1−H)` and `M★ < M₀` give `e(N−1−H) < M₀`, i.e. `H > N−1−M₀/e` ✓. Then `ρ_H ≤ Q^{−bH+C₀} ≤ Q^{−b(N−1−M₀/e)+C₀} = Q^{−b(N−1)+O(1)}` ✓; with `b ≥ a + 1/2 ≥ 5/2` ✓ this is `≤ Q^{−(N−c₃)}` ✓.
* **Genre count.** `p̃(m)N^m` from GENIND-C1(iv) ✓; multiplying a `Q^{−(N−c)}` bound by a polynomial preserves the species ✓.
* **Compiler verdict: every tagged display and every intermediate step of this proof re-derives exactly.** The proof is sound **on its stated hypothesis** — and its stated hypothesis (C2(i)'s scalar `M★ ≥ e(N−1−H)`) is precisely what R11 withdraws for embedded and mixed genres. **The mathematics is right; the input is not universally available.**

**DERIVATION:** Displayed in full above. Justification tags: (i) = `by XREF (CS-1)` + `by XREF S7.1`'s slot geometry; (ii) = `by XREF S5.1` (CS-free at μ ≤ 3) + `by XREF GENIND.C′` + `computation` (lexicographic descent — **the part R11 replaces**); (iii) = `by XREF W-12 S2.2` (slot count) + `computation` (supporting-line sum); (iv) = `computation` (geometric sum) + `by XREF GENIND-C1(iv)` + `by XREF GENIND-6(d)`/`R6.2` for the mixed composition.

**RESOLUTION TRACE:** statement lines 3319–3506. proof lines — same (statement and proof are one display). correction sites: 3592–3721 (R11's C2-G1/G2/G3, `.196`–`.205`).

**TEETH:** the r1 machine leg (`.185`) was run against `.180`, **not against this version** — the R9 replacement post-dates it by two days and **has no machine leg of its own**. Disposition: **`signed vacuity disclosure`** — the Q-normalized lemma is unexercised; its d = 1 specialization coincides with the tested version, and its `d ≥ 2` content (the whole point of the repair) is untested. Recorded as OPEN-CALL 2.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:S2.2` — count **19**.

---
### EFF.GENIND.190  [instance-record]

**CANONICAL STATEMENT:** FORM: bulleted display with LaTeX (the R9 corrected checks). verbatim, lines 3508–3541.

> “> **Displayed checks in the corrected normalization.**
> >
> > * **CS4-E(h):** \(\rho=(Q-1)Q^{1-5h}\), \(H=2h\),
> >   \(M^\star=2N-2-4h\), and \(|K|=Q\). Hence
> >   \(\rho\,\delta_{\mathrm{stage}}\le \operatorname{poly}(N)Q^{-2N-h+O(1)}\).
> > * **CS4-F(k):** \(\rho=(Q(Q-1)/2)Q^{-10k}\), \(H=4k\),
> >   \(M^\star=N-1-4k\), and \(|K|=Q^2\). Hence
> >   \(\rho\,\delta_{\mathrm{stage}}\le \operatorname{poly}(N)Q^{-2N-2k+O(1)}\).
> > * **CS5-V1E2(h):**
> >   \(\rho=(Q-1)Q^{\,2-(15h+1)/2}\left(1-Q^{-(N-(5h+1)/2)}\right)\),
> >   while \(H=2h\) and \(M^\star=2N-2-4h\). Therefore
> >   \(\rho\,\delta_{\mathrm{stage}}\le \operatorname{poly}(N)Q^{-2N-(7/2)h+O(1)}\).
> >   The fifth root's headroom is a decided-piece fiber; it does not
> >   weaken the stage-drain estimate. CS5-V4E2 and the remaining
> >   embedded \((2,2)\)-type genres have the same species: their
> >   additional vertex and split-piece constraints only strengthen
> >   (C2.2).”

**ARITHMETIC AUDIT (compiler-computed; all three, and note the third CHANGED from `.181`):**
* **CS4-E:** `ρ·Q^{−a(N−1−H)}` with `a = eγ = 2`, `H = 2h`: `Q^{1−5h}·Q^{−2(N−1−2h)} = Q^{1−5h−2N+2+4h} = Q^{−2N−h+3}` ✓ = `Q^{−2N−h+O(1)}` ✓.
* **CS4-F:** `a = eγ = 1·2 = 2`, `H = 4k`: `Q^{−10k}·Q^{−2(N−1−4k)} = Q^{−10k−2N+2+8k} = Q^{−2N−2k+2}` ✓ ✓.
* **CS5-V1E2:** `Q^{2−(15h+1)/2}·Q^{−2(N−1−2h)} = Q^{2−(15h+1)/2−2N+2+4h} = Q^{−2N+4−(15h+1)/2+4h} = Q^{−2N + 3.5 − 7h/2}` ✓ = `Q^{−2N−(7/2)h+O(1)}` ✓. **Compare `.181`'s pre-correction display, which gave `q^{−2N+O(h)}`** — i.e. R9 sharpens an `O(h)` into an explicit `−(7/2)h` **and** changes the base from q to Q ✓. **Both improvements check.**
* **Base change consistency:** at `d = 1`, `Q = q` and all three exponents coincide with `.181`'s except the sharpened third ✓ — so no committed number moves ✓, exactly as `.188` claims.

**CONDITIONALITY:** Survives R11 unchanged **at these three genres**, because R11's C2-G3 records “The CS4-E, CS4-F, and CS5-V1E2 checks have \(S=L=4\), so their displayed exponents do not change” (`.204`).

**DERIVATION:** Instantiation of `.189`.

**RESOLUTION TRACE:** statement lines 3508–3541. correction sites: 3849 (C2-G3's explicit no-change note, `.204`).

**TEETH:** none of its own; the r1 leg measured the E and F species at d = 1 (`.185`).

---
### EFF.GENIND.191  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed display (the R9 conditionality paragraph). verbatim, lines 3543–3557.

> “> **Conditionality.** GENIND-C2 consumes the (CS-1) clause family
> > only, including recursively realized stage genres. It consumes
> > neither (CS-2), (CS-3), nor (CS-EXACT). At \(n=4\), (CS-1) is
> > de facto discharged by the pinned GENH4 package identified in
> > Step 4. At higher degrees it is already a component of
> > [GENIND-H], the hypothesis of GENIND.B. Consequently the FULL
> > complement used in GENIND-C1 has (A2-RATE): its simple part comes
> > from GENIND.C′, and its CS-drain part comes from this lemma in the
> > required base \(Q=q^d\), not merely in base \(q\).”

**CONDITIONALITY:** **Superseded by R11's certification status** (`.199`): “‘conditional on (CS-1) only’ must be replaced by ‘conditional on (CS-1Q), verified per genre.’” **So the sentence “At higher degrees it is already a component of [GENIND-H], the hypothesis of GENIND.B” — the claim that the rate leg adds no hypothesis — is exactly what R11 overturns for embedded and mixed genres.** Tagged `STALE-SELF-DESCRIPTION (uncured)`; the text is not edited.

**SUPERSESSION KIND:** received `replacement` (of the conditionality label).

**TARGETS (of the eventual replacement):** shard 1 `.13`, `.37`, `.57`, `.63`; `.04`, `.05`, `.35` here.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 3543–3557. correction sites: 3712 (`.199`).

**TEETH:** the n = 4 discharge is a citation (shard 1 `.59`).

---
### EFF.GENIND.192  [changes-record]

**CANONICAL STATEMENT:** FORM: bulleted display (R9's riding MINOR-A). verbatim, line 3561.

> “* **[2026-08-12, riding MINOR-A]** In r1.1's preregistration, read “P1 … at 10 scored fresh rows” as “P1 … at 11 scored fresh rows”; the roster has 12 fresh rows, of which the floor-adjacent F row \((q,k,N)=(3,1,6)\) has \(M^\star=1\) and was disclosed but not scored, leaving exactly 11 scored rows as the committed record reports.”

**SUPERSESSION KIND:** `wording-rider` (a numeral in a preregistration corrected to match the roster and the committed record).

**TARGETS:** `.183`.

**ARITHMETIC AUDIT:** independently re-derived at `.183`: roster E 8 rows + roster F 4 rows = **12**, minus the floor-adjacent `(3,1,6)` with `M★ = 6−1−4 = 1` → **11 scored** ✓. **MINOR-A is correct and the compiler's independent count agrees.**

**CONDITIONALITY:** A preregistration numeral corrected *after* the run — which would normally be a serious protocol issue. **It is not one here**, because the committed record already reported 11 and the correction moves the *preregistration* into line with the *roster*, not the other way round; the note says so (“as the committed record reports”).

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement line 3561. correction sites: none.

**TEETH:** `arithmetic recount`.

---
### EFF.GENIND.193  [changes-record]

**CANONICAL STATEMENT:** FORM: bulleted display (R9's riding MINOR-B — the consumed-surface census replaced). verbatim, line 3563.

> “* **[2026-08-12, riding MINOR-B]** Supersede R1.4's “five committed displays” census by this enumerated consumed-surface census: W-11's \(R(M)\); HEX3.A's exact law; HEX3.B's rate; GT-BDRAIN's \(n=4,5\) first-step recursions; GENIND-BOX-4's pricing sentence; the M6 and PSTEEP3/PSTEEP4 locus data used in GENIND-C1(i); and the six extraction identities used in GENIND-C1(iii), namely M6, TWOCHILD-A, TWOCHILD-B, PSTEEP3, PSTEEP4, and SS6.”

**SUPERSESSION KIND:** `inventory completion` — a five-item census replaced by a longer enumerated one.

**TARGETS:** `.154` (R1.4's census).

**ARITHMETIC AUDIT (compiler-computed):** the new census names **5 original items + the M6/PSTEEP3/PSTEEP4 locus data (3) + the six extraction identities (6) = 14 named objects**, of which M6, PSTEEP3 and PSTEEP4 appear twice (once as locus data for C1(i), once as extraction identities for C1(iii)) → **11 distinct objects** ✓. Every one is verifiable in shard 1: R(M) (`.172`, `.192`), HEX3.A/B (`.192`, `.193`), GT-BDRAIN (`.172`), GENIND-BOX-4 (shard 2 `.78`), M6 (`.107`, `.112`), PSTEEP3/PSTEEP4 (`.102`), TWOCHILD-A/B (`.101`), SS6 (`.116`) ✓ — **11/11 exist at their committed instance rows.** The note's own verification wording (`.122`) says exactly this: “MINOR-B's enumerated census verified for existence of every named object at its committed instance rows”.

**CONDITIONALITY:** The census is an enumeration, rule-compliant; but note the note's own honest scoping at `.195`: “the item-by-item consumed-surface attribution is sol's enumeration” — i.e. **the objects were verified to EXIST, and the attribution of each to a consumption site was not independently re-derived.**

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement line 3563. correction sites: none.

**TEETH:** `arithmetic recount` (existence of 11/11 objects) with a disclosed limit on the attribution.

---
### EFF.GENIND.194  [changes-record]

**CANONICAL STATEMENT:** FORM: bulleted display (R9's riding MINOR-C — the height-sum sentence replaced). verbatim, line 3565.

> “* **[2026-08-12, riding MINOR-C]** Replace “the entry mass \(\rho\) decays geometrically in \(H\), so the height sum converges” by: “S2.2 gives \(\rho_H\le Q^{-((L+1)/2)H+O_m(1)}\), while the stage factor is at most \(Q^{-e\deg\psi\,(N-1-H)+O(1)}\); since \(L\ge e\mu\deg\psi\ge2e\deg\psi\), one has \((L+1)/2-e\deg\psi\ge1/2\), so the composed summand is at most \(Q^{-e\deg\psi\,(N-1)-H/2+O(1)}\), whose \(H\)-sum is geometric.”

**SUPERSESSION KIND:** `replacement` — a hand-wave (“decays geometrically in H, so the height sum converges”) replaced by the explicit domination argument. **This is the substantive one of the three folds:** the original sentence attributed the convergence to the entry mass alone, and the replacement shows the convergence comes from the *difference* `b − a ≥ 1/2`, i.e. from the entry price BEATING the stage factor's growth in H. `.189`'s own (iii) says it: “entry decay alone was not the reason the height sum converges.”

**TARGETS:** `.180`(iii) (the r1.1 sentence).

**ARITHMETIC AUDIT:** `L = eμγ ≥ 2eγ` (μ ≥ 2) ✓; `(L+1)/2 − eγ ≥ (2eγ+1)/2 − eγ = 1/2` ✓; composed summand `Q^{−bH}·Q^{−a(N−1−H)} = Q^{−a(N−1)−(b−a)H} ≤ Q^{−a(N−1)−H/2}` ✓; the H-sum is geometric with ratio `Q^{−1/2} ≤ 2^{−1/2}` ✓. **Every step re-derives, and it is the same computation as (C2.0)+(C2.3).**

**CONDITIONALITY:** Survives R11 with `b` replaced by `b_S = (S+1)/2 ≥ (L+1)/2` (`.204`), i.e. **strengthened**, not weakened.

**DERIVATION:** Displayed.

**RESOLUTION TRACE:** statement line 3565. correction sites: 3842–3850 (C2-G3's consumer sweep, `.205`).

**TEETH:** `arithmetic recount`.

---
### EFF.GENIND.195  [changes-record]

**CANONICAL STATEMENT:** FORM: italic parenthetical paragraph (the R9 orchestrator-verification record). verbatim, lines 3567–3588.

> “*(The replacement lemma and three folds above were derived by the R9
> certification run (gpt-5.6-sol high,
> runs/cert/R9_drain_repair_output.log, 2026-08-12); orchestrator
> verification before transcription — the d-factor defect confirmed at
> HEAD (r1.1's C2(iii) conclusion displays q^{−(N−c_c)} against the
> Q^{m(N−1)} normalization, while its own stage estimate retains
> e·d·deg ψ); the replacement's algebra re-derived by hand: (C2.0)
> L = eμγ ≥ 2a and b − a = (L+1)/2 − eγ ≥ 1/2; the entry-price
> exponent Σ_{r≤L} rH/L = (L+1)H/2; the composition
> Q^{−a(N−1)−(b−a)H}; the lexicographic descent at μ ≥ 4 (μγ ≤ m,
> equality only at e = 1 where H > 0 shrinks the window); the
> floor-adjacent branch (b ≥ 5/2); and all three displayed checks
> (CS4-E: exponent 1−5h−2(N−1−2h) = −2N−h+O(1); CS4-F:
> −10k−2(N−1−4k) = −2N−2k+O(1); CS5-V1E2: 2−(15h+1)/2−2(N−1−2h) =
> −2N−(7/2)h+O(1)). MINOR-A checked against the committed machine
> record (P1 GREEN 11/0, the (3,1,6) row disclosed-not-scored, roster
> count 12 re-added); MINOR-B's enumerated census verified for
> existence of every named object at its committed instance rows (the
> item-by-item consumed-surface attribution is sol's enumeration);
> MINOR-C is the (C2.0)-domination just verified. Transcribed
> unaltered per the standing division of labor. Ledger: row 17 →
> repaired, awaiting the clean sol re-pass.)*”

**CONDITIONALITY:** **A provenance record with an explicit division-of-labour disclosure: the mathematics was DERIVED by a different model and TRANSCRIBED unaltered, with the orchestrator's verification enumerated before transcription.** This is the corpus's standing protocol for sol-derived repairs, and it is what makes the unit's evidence chain auditable.

**ARITHMETIC AUDIT:** the orchestrator's enumerated re-derivations are **exactly the ones this compiler independently performed at `.189`, `.190`, `.194`** — (C2.0), the entry-price sum, the composition, the floor-adjacent branch, and all three displayed checks — **and all agree.** One item the orchestrator lists is the lexicographic descent “equality only at e = 1 where H > 0 shrinks the window”, **which R11 subsequently found insufficient** (`.201`, `.202`): the inference `M★ < N` from a *lower* bound is invalid. **So the orchestrator's verification passed a step that a later decorrelated pass refuted** — recorded, because it is the sharpest available evidence about the limits of verify-then-transcribe.

**SUPERSESSION KIND:** none of its own.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 3567–3588. correction sites: 3723–3793 (C2-G2, which refutes the descent step this record verified).

**TEETH:** `in-house hostile pass` (the orchestrator's pre-transcription check) — **with a disclosed miss**, per the audit above. Ledger cross-reference: “Ledger: row 17 → repaired, awaiting the clean sol re-pass” — the re-pass is `.196`.

**PIN VERIFICATION:** `runs/cert/R9_drain_repair_output.log` EXISTS ✓.

---
### EFF.GENIND.196  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph (the R11 round-2 correction's supersession declaration — **the shard's most consequential single paragraph**). verbatim, lines 3592–3594.

> “### Dated correction (2026-08-12 — GENIND-C2 repair round 2)
>
> **Supersession and scope.** This append supersedes the stage-window assertion in C2(i), the equal-product-degree descent sentence in C2(ii), and the entry-pricing display in C2(iii) of the 2026-08-12 GENIND-C2 correction. The scalar bound \(M^\star\ge e(N-1-H)\) is withdrawn for general embedded and mixed genres: the displayed (CS-1) clause supplies ragged per-coordinate certified windows and permits sibling-Hensel losses, but supplies no inequality pricing those losses. The corrected quantitative clause below is sufficient for every downstream use. Its verification remains a per-genre obligation inside (CS-1).”

**CONDITIONALITY:** **A WITHDRAWAL, not a re-wording.** `M★ ≥ e(N−1−H)` — the input on which `.189`'s entire proof rests — is withdrawn for general embedded and mixed genres, with a precise reason: (CS-1) supplies *ragged per-coordinate* windows and *permits* sibling-Hensel losses **without pricing them**. The replacement (C2Q) is “sufficient for every downstream use”, and **its verification is a per-genre obligation**, i.e. the discharge is deferred, not achieved.

**SUPERSESSION KIND:** `replacement` at three named parts, one of which is a **withdrawal** — a sub-kind the v3 enum does not distinguish (§6.3). **`replacement` is the right kind and the withdrawal must be recorded in the field text, because a merge that reads it as an ordinary replacement will not know that a previously-available input is now unavailable.**

**TARGETS:** `.189` parts (i), (ii), (iii); and, transitively, `.180`, `.182`, `.186`, `.191`.

**ARITHMETIC AUDIT (compiler-computed, on the withdrawal's ground):** (CS-1) as displayed (shard 1 `.63`) asserts a count-isomorphism “at an explicit stage window, RAGGED-WINDOW-CORRECTED”, and GENIND-6(a) (shard 1 `.34`) leaves composite blocks “as a monic cofactor with PER-COEFFICIENT certified windows (the triangular division ledger; the sibling-Hensel-loss composition GENHN already displays … ‘N ↦ N − (sibling Hensel loss) coordinate-wise’)”. **Neither supplies a numeric floor on the loss** ✓ — so a scalar lower bound `M★ ≥ e(N−1−H)` on a *common uniform* window does not follow from them ✓. **The withdrawal is correct.**

**DERIVATION:** Not a mathematical unit; a supersession declaration.

**RESOLUTION TRACE:** statement lines 3592–3594. correction sites: none downstream in this note.

**TEETH:** `decorrelated-model audit` (the sol R11 re-pass). **PIN VERIFICATION:** `runs/cert3/R11_genind_output.log` EXISTS ✓.

---
### EFF.GENIND.197  [hypothesis]

**CANONICAL STATEMENT:** FORM: heading + prose + **LaTeX definitions and the two tagged clauses (CS-1Q.a) and (CS-1Q.b)** — the ledger's HYP.36. verbatim, lines 3596–3637.

> “#### C2-G1 — loss-priced uniform core
>
> Fix a CS genre \(\mathcal G\), put
> \[
> Q=q^d,\qquad \gamma=\deg\psi,\qquad a=e\gamma,\qquad L=e\mu\gamma,
> \]
> and let \(S\ge L\) be the actual horizontal length of the side carrying the composite block. Let \(H\) be that side's vertical drop and put
> \[
> b_S:=\frac{S+1}{2}.
> \]
> From the per-coordinate certified windows supplied by (CS-1), define:
>
> - \(\lambda_{\mathcal G}\): the largest loss, in \(v'\)-height units, caused by the sibling-Hensel division ledger;
> - \(r_{\mathcal G}\): the further number of \(v'\)-height units discarded when the residue-class strings are truncated below their ragged ends;
> - \(\Delta_{\mathcal G}:=\lambda_{\mathcal G}+r_{\mathcal G}\);
> - \(M_{\mathcal G}\): the resulting common uniform stage window;
> - \(C_{\mathcal G}^{\mathrm{extra}}\): the entry codimension, in \(Q\)-digit units, contributed by sibling sides, vertices, split pieces, residual pins, and other conditions beyond the supporting-line price on the \(S\)-long side.
>
> The quantitative stage-transport clause required here is:
> \[
> M_{\mathcal G} \ge e(N-1-H)-\Delta_{\mathcal G},                 \tag{CS-1Q.a}
> \]
> and
> \[
> \gamma\Delta_{\mathcal G} \le C_{\mathcal G}^{\mathrm{extra}}
>    +\left(b_S-a-\frac12\right)H+O_{\mathcal G}(1).            \tag{CS-1Q.b}
> \]
>
> Clause (CS-1Q.b) is the explicit price of the ragged boundary and sibling-Hensel losses. It says that every lost \(K\)-digit is paid either by an additional entry condition or by the supporting-line slack beyond the load-bearing coefficient \(a+\tfrac12\).”

**CONDITIONALITY:** **THIS IS LEDGER ROW HYP.36**, verbatim (`spec/HYPOTHESIS_LEDGER.md:310–315`):

> “HYP.36  `(CS-1Q)`
> WHERE: `GENIND_PROOF_2026-08-08.md`, §C2-G1 L3592–3722.
> STATEMENT: Both clauses hold: M_G≥e(N−1−H)−Δ_G, and the displayed digit-loss rate follows; the rate does not by itself assert all residual mass is zero.
> CONSUMED BY: DRAIN-N4/A2.
> CLASS: named-obligation
> PROPOSED DISPOSITION: CARRY — embedded/mixed affine ledgers are not universally checked.”

The ledger's line-range `L3592–3722` matches this shard's C2-G1 span exactly ✓. Its disposition is **CARRY**, and its stated reason is precisely `.199`'s certification-status paragraph.

**SUPERSESSION KIND:** `replacement` (of the withdrawn scalar bound by a two-clause family) + `inventory completion` (five new named quantities defined).

**TARGETS:** shard 1 `.37`, `.57`, `.63`; `.05`, `.33`, `.35`, `.42`, `.44` here.

**ARITHMETIC AUDIT (compiler-computed):**
* **(CS-1Q.a)** relaxes the withdrawn bound by exactly the total loss `Δ_G = λ_G + r_G` ✓ — so at `Δ_G = 0` it IS the withdrawn bound ✓, which is why the standalone CS4-E/CS4-F displays are unaffected (`.199`).
* **(CS-1Q.b)** is the pricing condition. Reading it as the audit of `.198`'s exponent: the proof needs `γΔ_G − C_extra − (b_S − a)H ≤ −H/2 + O(1)`, i.e. `γΔ_G ≤ C_extra + (b_S − a − 1/2)H + O(1)` ✓ — **(CS-1Q.b) is exactly the inequality C2Q's algebra requires, no more and no less.** That is a design virtue: the hypothesis is not stronger than the use.
* **`S ≥ L`** ✓ by definition (the composite block occupies length L of an S-long side).
* **`b_S = (S+1)/2 ≥ (L+1)/2 ≥ a + 1/2`** ✓ (C2-G3's (C2E.3)) — so the slack coefficient `b_S − a − 1/2 ≥ 0` ✓, i.e. **(CS-1Q.b)'s right-hand side is nonnegative**, and the clause is not vacuously false.

**DERIVATION:** Definitional (the five quantities) + a stated hypothesis (the two clauses). **NOT proved** — that is the point.

**RESOLUTION TRACE:** statement lines 3596–3637. correction sites: none.

**TEETH:** **NONE — and this is the single most important `signed vacuity disclosure` in the three shards.** `.199` states it: the displayed (CS-1), GENIND-6(a) and GENHN references “do not establish (CS-1Q.b) for every embedded or mixed genre”. The standalone CS4-E/CS4-F cases have `Δ_G = 0` and are fine; **every embedded or mixed genre carries an unverified per-genre obligation.**

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:S11.F` — count **10** (the affine ledger species the clause would have to be checked against).

---
### EFF.GENIND.198  [lemma]

**CANONICAL STATEMENT:** FORM: display (blockquote, ANNEX-LEMMA GENIND-C2Q) + its proof with tagged equations. verbatim, lines 3639–3710.

> “> **ANNEX-LEMMA GENIND-C2Q (loss-priced core).** Assume (CS-1Q.a–b) for the fixed genre. Then its conservative stage-drain contribution satisfies
> >
> > \[
> > \frac{u^{\mathrm{CS}}_{\mathcal G}(N)}{Q^{m(N-1)}}
> > \le K_{\mathcal G}N^{B_{\mathcal G}} Q^{-a(N-1)-H/2+O_{\mathcal G}(1)}.          \tag{C2Q.1}
> > \]
> >
> > Consequently its height sum has the required \(K N^B Q^{-(N-c)}\) form.
>
> *Proof.* The corrected entry count, proved under C2-G3 below, is
> \[
> \rho_{\mathcal G} \le Q^{-b_SH-C_{\mathcal G}^{\mathrm{extra}} +O_{\mathcal G}(1)}.                     \tag{C2Q.2}
> \]
> On the range where the quantitative stage estimate is invoked, GENIND.C′ over \(K\), with \(|K|=Q^\gamma\), gives
> \[
> \delta_{\mathrm{stage}} \le K_\star N^{B_\star}Q^{-\gamma M_{\mathcal G} +O_{\mathcal G}(1)}.
> \]
> By (CS-1Q.a),
> \[
> -\gamma M_{\mathcal G} \le-a(N-1-H)+\gamma\Delta_{\mathcal G}.
> \]
> Multiplying by (C2Q.2) and applying (CS-1Q.b),
> \[
> \begin{aligned}
> \rho_{\mathcal G}\delta_{\mathrm{stage}}
> &\le K_\star N^{B_\star} Q^{-a(N-1)-(b_S-a)H -C_{\mathcal G}^{\mathrm{extra}} +\gamma\Delta_{\mathcal G} +O_{\mathcal G}(1)}\\
> &\le K_\star N^{B_\star} Q^{-a(N-1)-H/2+O_{\mathcal G}(1)}.
> \end{aligned}
> \]
> For the floor-adjacent range \(M_{\mathcal G}<M_0\), (CS-1Q.a) gives
> \[
> \gamma\Delta_{\mathcal G} >a(N-1-H)-\gamma M_0.
> \]
> Combining this with (CS-1Q.b) yields
> \[
> b_SH+C_{\mathcal G}^{\mathrm{extra}} \ge a(N-1)+\frac H2-O_{\mathcal G,M_0}(1).
> \]
> Thus the trivial stage-drain bound \(1\) gives (C2Q.1) there as well. Finally,
> \[
> \sum_{H\ge0}Q^{-H/2} \le (1-2^{-1/2})^{-1},
> \]
> and the polynomial genre count of GENIND-C1(iv) absorbs the remaining fixed-degree parameters. ∎”

**CONDITIONALITY:** **Conditional on (CS-1Q.a–b) per genre** — the whole content of the round-2 repair. Its conclusion is the same species as `.189`'s, so **every downstream consumer is unaffected in FORM and re-conditioned in HYPOTHESIS.**

**ARITHMETIC AUDIT (compiler-computed; every step re-derived):**
* `−γM_G ≤ −γ[e(N−1−H) − Δ_G] = −a(N−1−H) + γΔ_G` ✓ (using `γe = a` ✓).
* Multiplying: exponent `= −b_S H − C_extra − a(N−1−H) + γΔ_G + O(1) = −a(N−1) − (b_S − a)H − C_extra + γΔ_G + O(1)` ✓ **as displayed**.
* Applying (CS-1Q.b) `γΔ_G ≤ C_extra + (b_S − a − 1/2)H + O(1)`: the exponent `≤ −a(N−1) − (b_S−a)H − C_extra + C_extra + (b_S−a−1/2)H + O(1) = −a(N−1) − H/2 + O(1)` ✓ **exact.**
* **Floor-adjacent branch.** From (CS-1Q.a), `M_G ≥ e(N−1−H) − Δ_G`, so `M_G < M_0` gives `e(N−1−H) − Δ_G < M_0`, i.e. `Δ_G > e(N−1−H) − M_0`, hence `γΔ_G > a(N−1−H) − γM_0` ✓ **as displayed.** Combining with (CS-1Q.b): `a(N−1−H) − γM_0 < γΔ_G ≤ C_extra + (b_S−a−1/2)H + O(1)`, so `C_extra + b_S H ≥ a(N−1−H) + aH + H/2 − O(1) = a(N−1) + H/2 − O(1)` ✓ **exact** (using `−(b_S−a−1/2)H + b_S H = aH + H/2` ✓). Then the trivial bound `δ ≤ 1` with `ρ ≤ Q^{−b_S H − C_extra + O(1)} ≤ Q^{−a(N−1)−H/2+O(1)}` ✓ gives (C2Q.1) ✓.
* Height sum and genre count as at `.189` ✓.
* **Compiler verdict: the C2Q proof is correct and every step re-derives.** It is *cleaner* than `.189`'s, because the hypothesis was reverse-engineered from the algebra.

**SUPERSESSION KIND:** `replacement` (of `.189`'s (i)/(iii) mechanics by a loss-priced version).

**DERIVATION:** Displayed. Justification tags: (C2Q.2) = `by XREF C2-G3` (`.204`); the stage estimate = `by XREF GENIND.C′` over K; the two combinations = `computation` (audited above); the floor-adjacent branch = `computation`; the closing = `by XREF GENIND-C1(iv)`.

**RESOLUTION TRACE:** statement lines 3639–3710. proof lines — same. correction sites: none.

**TEETH:** **NONE.** No machine leg was added at R11 (the r1 leg predates and was run against `.180`). Disposition: **`signed vacuity disclosure`** — the lemma is proved and unexercised, and its hypothesis is per-genre unverified.

---
### EFF.GENIND.199  [fence]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (the C2-G1 certification status — **the honest residue**). verbatim, line 3712.

> “**Certification status.** The standalone CS4-E and CS4-F displays have no sibling loss in their uniform cores and satisfy the calculation directly. The displayed general (CS-1), GENIND-6(a), and GENHN references do not establish (CS-1Q.b) for every embedded or mixed genre: they assert affine per-coordinate windows and boundary routing, but do not relate the resulting loss to entry codimension. Accordingly, “conditional on (CS-1) only” must be replaced by “conditional on (CS-1Q), verified per genre.” A universal discharge for embedded and mixed genres remains obstructed until those affine ledgers are displayed and checked.”

**CONDITIONALITY:** **The load-bearing honesty sentence of the entire annex stack**, and the source of ledger row HYP.36's CARRY disposition. Its three clauses do three different jobs: (1) the standalone quartic genres are FINE (`Δ_G = 0`); (2) the general references are INSUFFICIENT, with the reason named (they assert windows and routing, not a loss-to-codimension relation); (3) the label change is MANDATORY, and the obstruction is named as a displayed-and-checked-ledgers obligation.

**SUPERSESSION KIND:** `replacement` of a conditionality label, applied globally to every rate consumer.

**TARGETS:** shard 1 `.13`, `.37`, `.57`, `.63`; `.04`, `.05`, `.33`, `.35`, `.39`, `.42`, `.44` here.

**ARITHMETIC AUDIT:** “The standalone CS4-E and CS4-F displays have no sibling loss in their uniform cores” — at those genres the whole polygon is the side (shard 1 `.48`, `.49`: “n = 4 (the whole polygon is the side)”), so there is no sibling block to lose Hensel digits to ✓, `Δ_G = 0` ✓, and (CS-1Q.a) reduces to the withdrawn scalar bound ✓, which `.42`'s proof then uses directly ✓. **The exemption is correctly scoped.**

**DERIVATION:** Not a mathematical unit; a certification-status fence.

**RESOLUTION TRACE:** statement line 3712. correction sites: none — this is the terminal reading.

**TEETH:** **the fence IS the disclosure.** Disposition: `signed vacuity disclosure` for embedded/mixed genres; `accepted` for the two standalone quartic genres.

---
### EFF.GENIND.200  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed bulleted display (the C2-G1 consumer sweep). verbatim, lines 3714–3721.

> “**C2-G1 consumer sweep.**
>
> - In GENIND-C2(i), replace \(M^\star\ge e(N-1-H)\) by (CS-1Q.a–b).
> - In C2.1–C2.4, replace the separate entry/window multiplication by ANNEX-LEMMA GENIND-C2Q.
> - In R1.1's full-complement closure and GENIND-C1(iii)'s growing-window use, read the CS-drain rate as conditional on (CS-1Q), not bare (CS-1).
> - In GENIND.B Step 4 and the GENIND-6(d) mixed-drain union bound, child terms remain supplied by GENIND-C1; stage terms are supplied by GENIND-C2Q.
> - The claims that (CS-2), (CS-3), and (CS-EXACT) are not consumed by this rate bound remain correct.
> - At \(n=4\), the standalone E/F calculations remain valid. No general embedded/mixed discharge is asserted by this append.”

**CONDITIONALITY:** **A consumer sweep reaching into the byte-frozen body** (bullets 3 and 4 name R1.1's closure, GENIND-C1(iii), GENIND.B Step 4 and GENIND-6(d)) **without quoting the target sentences.** Its status as a supersession vehicle is OPEN-CALL 1.

**SUPERSESSION KIND:** `replacement` (bullets 1, 2, 4) + `scope-pin` (bullet 3) + explicit **non**-supersessions (bullets 5, 6). **A single sweep carrying three kinds and two disclaimers — the format's hardest case for a merge.**

**TARGETS, resolved to unit IDs by this compiler:** bullet 1 → `.189`(i); bullet 2 → `.189`(C2.1–C2.4); bullet 3 → `.151` (R1.1's closure) and `.152`(iii); bullet 4 → **shard 1 `.57`** (GENIND.B Step 4) and **shard 1 `.37`** (GENIND-6(d)); bullets 5–6 → no target (negative declarations).

**ARITHMETIC AUDIT:** six bullets, of which four are instructions and two are non-supersessions ✓; every named target is identifiable ✓ (six for six).

**DERIVATION:** Not a mathematical unit; an install instruction.

**RESOLUTION TRACE:** statement lines 3714–3721. correction sites: none.

**TEETH:** NONE — an install record.

---
### EFF.GENIND.201  [lemma]

**CANONICAL STATEMENT:** FORM: heading + display (blockquote, ANNEX-LEMMA GENIND-C2D) + proof, with one tagged equation. verbatim, lines 3723–3734.

> “#### C2-G2 — well-founded descent by truncation and monotonicity
>
> > **ANNEX-LEMMA GENIND-C2D (window truncation).** Let
> > \(\delta_{\mu,K}(W)\) be the conservative-undecided fraction of a
> > \((\mu,K)\)-cluster system at window \(W\). If \(1\le T\le W\),
> > then
> > \[
> > \delta_{\mu,K}(W)\le\delta_{\mu,K}(T).            \tag{C2D.1}
> > \]
>
> *Proof.* Reduction from window \(W\) to \(T\) has constant fibers. If a truncation were decided at window \(T\), its decision would depend only on digits below \(T\), and the same certificate would decide every lift at window \(W\). Hence every window-\(W\) undecided state lies above a window-\(T\) undecided state. Dividing the resulting cardinality inequality by the two total state counts gives (C2D.1). The same argument applies to a ragged stage after truncation to any common uniform core below all residue-class ends; the discarded boundary slots are constant fiber coordinates. ∎”

**CONDITIONALITY:** **Unconditional — a genuinely new small lemma, and the one that makes the joint recursion well-founded.** Its content is a monotonicity: shrinking the window cannot decrease the undecided fraction.

**ARITHMETIC AUDIT (compiler-computed):** the reduction map `states(W) → states(T)` for `T ≤ W` is a truncation, with constant fibre size `Q^{μ(W−T)}` ✓ (each of the μ coordinates loses `W−T` digit levels). The decidedness argument: if the truncation of a state is decided at window T, the deciding certificate reads only digits below T, hence decides the state at window W too ✓ — so **W-undecided ⟹ T-undecided (contrapositive of T-decided ⟹ W-decided)** ✓, i.e. the undecided set at W maps into the undecided set at T ✓. Cardinalities: `|U_W| ≤ |U_T|·Q^{μ(W−T)}` ✓; dividing by totals `Q^{μ(W−1)}` and `Q^{μ(T−1)}` gives `δ(W) = |U_W|/Q^{μ(W−1)} ≤ |U_T|Q^{μ(W−T)}/Q^{μ(W−1)} = |U_T|/Q^{μ(T−1)} = δ(T)` ✓ **exact.** **The lemma and its proof are correct.**
**Compiler observation on the conservative read.** The argument needs the read to be *monotone in the window* — i.e. that a decision made on a T-truncation is not retracted at W. That is exactly the conservative-drain convention's content (`v(a₀) ≥ N ⟹ UNDECIDED exit`, shard 1 `.07`), which decides only on visible data. **The proof does not cite that convention explicitly**; the step “the same certificate would decide every lift at window W” is where it is used. Recorded as a **compressed citation, not a gap.**

**SUPERSESSION KIND:** `inventory completion` (a well-foundedness ingredient the descent argument needed and did not have).

**DERIVATION:** Displayed.

**RESOLUTION TRACE:** statement lines 3723–3734. correction sites: none.

**TEETH:** NONE. Disposition: `signed vacuity disclosure` — a new unexercised lemma. (Its content is however *implied* by every GT-DEPTH0 row, which reads the same states at nested windows; no row tests the inequality directly.)

---
### EFF.GENIND.202  [lemma]

**CANONICAL STATEMENT:** FORM: prose + LaTeX displays (the lexicographic measure and the descent, replacing C2(ii)'s refuted sentence). verbatim, lines 3736–3784.

> “Use the lexicographic measure
> \[
> \mathfrak m=(\text{product degree},\text{window}) \in\mathbb N_{>0}\times\mathbb N_{\ge1}.
> \]
> For a composite stage, its product degree is
> \[
> D'=\mu d\gamma, \qquad D=md, \qquad m\ge e\mu\gamma.
> \]
> If \(e\ge2\), then
> \[
> D'\le D/e<D,
> \]
> so the first component decreases. If \(e=1\), then \(D'\le D\). When \(D'<D\), the first component again decreases. In the only remaining case \(e=1\) and \(D'=D\), let \(M_{\mathcal G}\) be the common uniform stage window and set
> \[
> T:=\min\{M_{\mathcal G},\,N-1\}.
> \]
> Then \(T<N\), and C2D.1 gives
> \[
> \delta_{\mu,K}(M_{\mathcal G}) \le\delta_{\mu,K}(T).
> \]
> The recursive estimate is therefore invoked at
> \[
> (D',T)=(D,T)<_{\mathrm{lex}}(D,N).
> \]
> No inference \(M^\star<N\) from a lower bound is used. If \(T=1\), the window-1 base case is exactly the R3 convention rider. Moreover, in the equal-degree case \(e=1\),
> \[
> e(N-1-H)-\Delta_{\mathcal G}\le N-1,
> \]
> so replacing \(M_{\mathcal G}\) by \(T\) preserves the lower bound (CS-1Q.a) needed in C2Q's exponent calculation.”

**CONDITIONALITY:** **The repair of a genuinely invalid step.** C2(ii) had inferred `M★ < N` from a *lower* bound on `M★` — “the visible opening has \(H>0\), hence \(M^\star<N\)” — which does not follow. The replacement never infers an upper bound: it **truncates** to `T := min{M_G, N−1} < N` and uses C2D's monotonicity to pay for the truncation. **The sentence “No inference \(M^\star<N\) from a lower bound is used” is the note naming its own former error.**

**ARITHMETIC AUDIT (compiler-computed):**
* `e ≥ 2`: `m ≥ eμγ` gives `μγ ≤ m/e`, so `D' = μdγ ≤ md/e = D/e < D` ✓.
* `e = 1`: `m ≥ μγ` gives `D' = μdγ ≤ md = D` ✓.
* Equal case `D' = D`: `T := min{M_G, N−1} ≤ N−1 < N` ✓; `(D, T) <_lex (D, N)` ✓ since the first components tie and `T < N` ✓ — **well-founded** ✓.
* C2D applies because `1 ≤ T ≤ M_G` — **requires `T ≥ 1`, i.e. `min{M_G, N−1} ≥ 1`, i.e. `M_G ≥ 1` and `N ≥ 2`** ✓ (the ambient window is ≥ 2 by S1; `M_G ≥ 1` is the live-stage condition, and `T = 1` is routed to R3's base case ✓).
* The preservation claim: in the equal-degree case `e = 1`, `(CS-1Q.a)`'s right side is `1·(N−1−H) − Δ_G ≤ N−1` ✓ (since `H ≥ 0, Δ_G ≥ 0`), so `T = min{M_G, N−1} ≥ min{e(N−1−H)−Δ_G, N−1} = e(N−1−H)−Δ_G` ✓ — **the lower bound survives truncation** ✓ **exact.**
* **Compiler verdict: the descent is now genuinely well-founded and every step re-derives.** The refuted inference is gone and nothing replaces it that needs an upper bound.

**SUPERSESSION KIND:** `replacement` (of C2(ii)'s descent sentence).

**TARGETS:** `.189`(ii).

**DERIVATION:** Displayed.

**RESOLUTION TRACE:** statement lines 3736–3784. correction sites: none.

**TEETH:** NONE. Disposition: `signed vacuity disclosure`; the descent is a proof structure no run exercises.

---
### EFF.GENIND.203  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed bulleted display (the C2-G2 consumer sweep). verbatim, lines 3786–3793.

> “**C2-G2 consumer sweep.**
>
> - Delete “\(H>0\), hence \(M^\star<N\)” from C2(ii).
> - Replace it by the lexicographic measure and truncation argument above.
> - The \(e\ge2\) degree-descent branch is unchanged.
> - GENIND.C′'s α-window induction and GENIND-C1's β-child degree descent are unchanged.
> - The joint recursion of GENIND.C′ with GENIND-C2 now has a displayed well-founded measure in every case.
> - No new upper bound on the original ragged stage window is claimed or needed.”

**CONDITIONALITY:** **The only sweep in the shard that DELETES a clause** (“Delete … from C2(ii)”), and it says so in the imperative. The remaining bullets are explicit non-changes and a closing disclaimer.

**SUPERSESSION KIND:** `replacement` with an explicit **deletion** — again a sub-kind the enum does not name (§6.3). Deleting a *false inference* is different from replacing a *display*, and a merge that flattens them may leave the deleted sentence readable as live text (it remains byte-intact at line 3382).

**TARGETS:** `.189`(ii). Non-targets declared: `.189`'s `e ≥ 2` branch, `.153` (GENIND.C′'s α-induction), `.152` (GENIND-C1's β-descent).

**ARITHMETIC AUDIT:** six bullets ✓; the deleted string “H>0, hence M★<N” is present at line 3382 of the source ✓ (inside `.189`(ii)), so the deletion instruction has a real target ✓.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 3786–3793. correction sites: none.

**TEETH:** NONE.

---
### EFF.GENIND.204  [lemma]

**CANONICAL STATEMENT:** FORM: heading + prose with three tagged LaTeX displays (C2-G3 — entry pricing at the ACTUAL side length). verbatim, lines 3795–3840.

> “#### C2-G3 — entry pricing uses the actual side length
>
> Let the actual side have horizontal length \(S\), vertical drop \(H\), and let the chosen composite residual block occupy length
> \[
> L=e\mu\gamma\le S.
> \]
> Relative to the side's right endpoint, its \(S\) coefficient columns have supporting-line heights
> \[
> \frac{H}{S},\frac{2H}{S},\ldots,\frac{SH}{S}.
> \]
> Therefore the number of forced \(Q\)-digit levels is at least
> \[
> \begin{aligned}
> \sum_{r=1}^{S} \left(\left\lceil\frac{rH}{S}\right\rceil-1\right)
> &\ge \sum_{r=1}^{S}\frac{rH}{S}-O_m(1)\\
> &=\frac{S+1}{2}H-O_m(1)\\
> &\ge\frac{L+1}{2}H-O_m(1).                         \tag{C2E.1}
> \end{aligned}
> \]
> The \(O_m(1)\) term absorbs the ceiling errors, the already-pinned level-zero digits, and the fixed residual-letter census. Other sides, vertices, sibling blocks, and decided pieces only add conditions. Hence
> \[
> \rho_{\mathcal G} \le Q^{-((S+1)/2)H-C_{\mathcal G}^{\mathrm{extra}} +O_m(1)}
>  \le Q^{-((L+1)/2)H-C_{\mathcal G}^{\mathrm{extra}} +O_m(1)}.                                \tag{C2E.2}
> \]
> Since \(L=e\mu\gamma\ge2e\gamma=2a\),
> \[
> \frac{S+1}{2}-a \ge\frac{L+1}{2}-a \ge\frac12.                                       \tag{C2E.3}
> \]
> Thus the domination used in C2Q is valid with the actual side length and is only strengthened when residual siblings share that side.”

**CONDITIONALITY:** **A STRENGTHENING, not a weakening** — pricing by the actual side length `S ≥ L` gives a larger entry codimension, hence a smaller `ρ`. The closing sentence says so, and `.205` confirms “no existing count is weakened”.

**ARITHMETIC AUDIT (compiler-computed):**
* Supporting-line heights on an S-long side of drop H, from the right endpoint: `rH/S` for `r = 1..S` ✓ (the line from (0, H) to (S, 0) has height `H − rH/S` at abscissa r counted from the left, i.e. `rH/S` counted from the right ✓).
* `Σ_{r=1}^{S} rH/S = (H/S)·S(S+1)/2 = (S+1)H/2` ✓ **exact.**
* `Σ(⌈rH/S⌉ − 1) ≥ Σ rH/S − S ≥ (S+1)H/2 − O_m(1)` ✓ (the ceiling error is at most 1 per column, S columns, and S ≤ m ✓ so the error is `O_m(1)` ✓).
* `(S+1)/2 ≥ (L+1)/2` ✓ since `S ≥ L` ✓.
* `L = eμγ ≥ 2eγ = 2a` ✓ (μ ≥ 2) — so `(L+1)/2 − a ≥ (2a+1)/2 − a = 1/2` ✓, and a fortiori `(S+1)/2 − a ≥ 1/2` ✓ **= (C2E.3), exact.**
* **The change from `.189`'s (C2.2):** `b = (L+1)/2` → `b_S = (S+1)/2 ≥ b` ✓, i.e. **a uniformly better bound** ✓.
* **Compiler verdict: (C2E.1)–(C2E.3) all re-derive exactly.**

**SUPERSESSION KIND:** `replacement` (of the entry-pricing display) — a strengthening.

**TARGETS:** `.189`(iii), `.194` (MINOR-C's replacement sentence, now with `b_S`).

**DERIVATION:** Displayed.

**RESOLUTION TRACE:** statement lines 3795–3840. correction sites: none.

**TEETH:** NONE. Disposition: `signed vacuity disclosure`; the three quartic checks are unchanged by construction (`.205`), so no measured number tests the strengthening.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:S2.2` — count **19** (the slot count the pricing implements).

---
### EFF.GENIND.205  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed bulleted display (the C2-G3 consumer sweep). verbatim, lines 3842–3850.

> “**C2-G3 consumer sweep.**
>
> - In C2.0, retain \(L=e\mu\gamma\) as the composite-block length, but define the actual entry coefficient as \(b_S=(S+1)/2\).
> - Replace the displayed heights \(rH/L\) by \(rH/S\), \(1\le r\le S\).
> - Replace C2.2 by (C2E.2).
> - In the height-domination step use \(b_S-a\ge(L+1)/2-a\ge1/2\).
> - The CS4-E, CS4-F, and CS5-V1E2 checks have \(S=L=4\), so their displayed exponents do not change.
> - Embedded or same-side mixed genres with \(S>L\) receive a strictly stronger entry bound; no existing count is weakened.”

**CONDITIONALITY:** **Five surgical replacements plus two impact statements**, one of which (bullet 5) is the compatibility guarantee for `.190`'s three checks.

**ARITHMETIC AUDIT:** bullet 5's claim `S = L = 4` at CS4-E, CS4-F, CS5-V1E2 — CS4-E: the whole polygon is the side, length 4, and `L = eμγ = 2·2·1 = 4` ✓ so `S = L = 4` ✓. CS4-F: `L = 1·2·2 = 4` ✓ and the side is the whole length-4 polygon ✓. CS5-V1E2: the side is `(1, 2h)–(5, 0)`, length **4** ✓, and `L = 2·2·1 = 4` ✓. **All three have S = L = 4 ✓ — so `b_S = b = 5/2` and the exponents are unchanged ✓, exactly as claimed.**

**SUPERSESSION KIND:** `replacement` ×4 + two non-change declarations.

**TARGETS:** `.189`(C2.0, the heights display, C2.2, the domination step), `.190` (declared unchanged), `.194`.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 3842–3850. correction sites: none.

**TEETH:** NONE.

---
### EFF.GENIND.206  [changes-record]

**CANONICAL STATEMENT:** FORM: italic parenthetical paragraph (the R11 orchestrator-verification record — the note's last words). verbatim, lines 3852–3872.

> “*(The round-2 repairs above were derived by the R11 certification run
> (gpt-5.6-sol high, runs/cert3/R11_genind_output.log, 2026-08-12),
> answering the D2f re-pass's C2-G1/G2/G3; orchestrator verification
> before transcription — C2-G3: the supporting-line sum re-derived
> (Σ_{r≤S} rH/S = (S+1)H/2) and the domination margin
> (S+1)/2 − a ≥ (L+1)/2 − a ≥ 1/2 re-checked, with the three displayed
> checks unchanged at S = L = 4; C2-G2: GENIND-C2D's truncation
> monotonicity verified (a window-T decision certificate decides every
> window-W lift over it, so undecided states project onto undecided
> truncations; constant fibers give δ(W) ≤ δ(T)) and the lexicographic
> measure is now genuinely well-founded (truncate to the uniform core,
> then strict product-degree or window decrease); C2-G1: the C2Q
> exponent algebra re-derived (−γM ≤ −a(N−1−H) + γΔ, then (CS-1Q.b)
> caps γΔ − C_extra − (b_S − a)H by −H/2 + O(1)), the floor-adjacent
> branch re-checked, and the HONEST RESIDUE recorded: the universal
> stage-window transfer for embedded/mixed genres is not discharged —
> the annex-lemma's conditionality is upgraded from "(CS-1) only" to
> "(CS-1Q), verified per genre", with (CS-1Q.b)'s per-genre affine
> ledgers a named obligation. Transcribed unaltered per the standing
> division of labor. Ledger: row 17 → round-2 repairs folded; awaiting
> a clean re-pass + the (CS-1Q) per-genre ledger obligation.)*”

**CONDITIONALITY:** **The note's closing state, and it is an open one:** “awaiting a clean re-pass + the (CS-1Q) per-genre ledger obligation.” **Nothing after line 3872 exists** — this is the last text in the note.

**ARITHMETIC AUDIT:** the orchestrator's four enumerated re-derivations are **exactly the ones this compiler performed independently at `.204`, `.201`, `.202`, `.198`** — the supporting-line sum, the domination margin, C2D's monotonicity, the C2Q exponent algebra and the floor-adjacent branch — **and all agree.** Unlike R9's record (`.195`), **no item this record verifies has since been refuted**; the note's arc ends with its last verification standing.

**SUPERSESSION KIND:** none of its own.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 3852–3872. correction sites: **none — this is the note's terminal text.**

**TEETH:** `in-house hostile pass` (the orchestrator's pre-transcription check) + the standing division-of-labour disclosure. **PIN VERIFICATION:** `runs/cert3/R11_genind_output.log` EXISTS ✓. Ledger cross-reference: “row 17” — the GENIND drain row of the certification ledger, distinct from `spec/HYPOTHESIS_LEDGER.md`'s HYP numbering; **not resolved here** (recorded, §8 defect 5).

---

## 4. XREF verification ledger (consolidated, deduplicated)

Every designation below was checked with fixed-string grep (`grep -cF '<designation>'
<file>`) against the target note; counts shown are each shard's own recorded count.
**145 raw XREF citations across the three shards (59 + 59 + 27, each shard's own
declared distinct-in-range total) reduce to 71 distinct `target:designation` pairs — 74
duplicate instances removed, of which 55 rows are cited by two or more shards.** Every
duplicate's count agrees exactly across every shard that cited it — **zero count
mismatches found** (verified by an automated cross-shard extraction and comparison: a
fixed-string grep against an unchanged file must return the same count regardless of who
runs it, and none did). No zero-count or purely descriptive string is emitted as an XREF
below; no designation was invented at merge time. **Shard 2's own 59 designations are, to
first order, the SAME supplier-designation set shard 1 cites directly** — shard 2's own
§3.1 header says as much ("This shard IS the note's own version of this table"): of its
extractable rows, 46 exact `(file, name, count)` triples are shared with shard 1 alone.

`[TABLE — compiler ledger]`

| # | Target : designation | Count | Role | Source shard(s) | Dedup |
|---:|---|---:|---|---|---|
| 1 | `GENH4_PROOF_2026-08-08.md:ANNEX-LEMMA GENH4-7` | 11 | s2: `.90`, `.92`, `.108`, `.136`, `.138`, `.139` | s2 | — |
| 2 | `GENH4_PROOF_2026-08-08.md:GENH4-1F` | 10 | s1: Menu-half companion (`.59`, `.66`) / s2: `.90`, `.92`, `.108`, `.136`, `.138`, `.139` / s3: Menu-half companion, re-verified at the annex-stack pin (`.182`) | s1+s2+s3 | **DEDUP** |
| 3 | `GENH4_PROOF_2026-08-08.md:GENH4-2` | 15 | s1: Named inside GENH4.D's package (`.59`) / s3: Named inside GENH4.D's package, re-verified at the annex-stack pin (`.182`) | s1+s3 | **DEDUP** |
| 4 | `GENH4_PROOF_2026-08-08.md:GENH4-BOX-7` | 1 | s2: `.90`, `.92`, `.108`, `.136`, `.138`, `.139` | s2 | — |
| 5 | `GENH4_PROOF_2026-08-08.md:GENH4-CAP(F)` | 11 | s1: The two-term genre-F even-N band (`.14`, `.59`, `.66`) / s2: `.90`, `.92`, `.108`, `.136`, `.138`, `.139` | s1+s2 | **DEDUP** |
| 6 | `GENH4_PROOF_2026-08-08.md:GENH4.C` | 11 | s2: `.90`, `.92`, `.108`, `.136`, `.138`, `.139` | s2 | — |
| 7 | `GENH4_PROOF_2026-08-08.md:GENH4.D` | 8 | s1: The package sentence CS-1 = GENIND-4 + GENH4-1F + GENH4-2/-3/-4 (`.59`) | s1 | — |
| 8 | `GENH4_PROOF_2026-08-08.md:Q22-L1` | 7 | s1: GENH4.A's scout-side name (`.59`, `.66`) / s2: `.90`, `.92`, `.108`, `.136`, `.138`, `.139` | s1+s2 | **DEDUP** |
| 9 | `GENH4_PROOF_2026-08-08.md:Q22-L3` | 3 | s1: GENH4.B's scout-side name (`.59`, `.66`) / s2: `.90`, `.92`, `.108`, `.136`, `.138`, `.139` | s1+s2 | **DEDUP** |
| 10 | `GENH4_PROOF_2026-08-08.md:THEOREM GENH4.A` | 5 | s1: The menu half of the n = 4 de facto discharge (`.59`, `.66`) / s2: `.90`, `.92`, `.108`, `.136`, `.138`, `.139` | s1+s2 | **DEDUP** |
| 11 | `GENH4_PROOF_2026-08-08.md:THEOREM GENH4.B` | 6 | s1: The drain half (`.14`, `.59`, `.66`) / s2: `.90`, `.92`, `.108`, `.136`, `.138`, `.139` | s1+s2 | **DEDUP** |
| 12 | `GENHN_PROOF_2026-08-08.md:GENHN-TOW-1` | 19 | s1: The n ≥ 8 conjunct added by the supplier-movement record (`.15`) / s3: The boxed tower clause added at the n ≥ 8 conditionality movement (`.145`) | s1+s3 | **DEDUP** |
| 13 | `GENHN_PROOF_2026-08-08.md:GENHN.A(i)` | 11 | s2: `.91`, `.92`, `.106`, `.136`, `.138`, `.144` / s3: Screened in the seven-site GENHN inventory (`.144`) | s2+s3 | **DEDUP** |
| 14 | `GENHN_PROOF_2026-08-08.md:GENHN.A(iv)` | 3 | s1: The stage node floor κ ≥ S_b + 1 (`.35`) / s2: `.91`, `.92`, `.106`, `.136`, `.138`, `.144` / s3: Screened at `.175` | s1+s2+s3 | **DEDUP** |
| 15 | `GENHN_PROOF_2026-08-08.md:GENHN.A(v)` | 6 | s1: The ragged-window-corrected stage read (`.37`, `.63`) / s2: `.91`, `.92`, `.106`, `.136`, `.138`, `.144` / s3: Screened at `.173`, `.175` | s1+s2+s3 | **DEDUP** |
| 16 | `GENHN_PROOF_2026-08-08.md:GENHN.C` | 19 | s1: Named in the W-12 r4 FIRING CHECK geography (`.15`) / s2: `.91`, `.92`, `.106`, `.136`, `.138`, `.144` / s3: Named in the W-12 r4 FIRING CHECK geography, re-verified (`.144`) | s1+s2+s3 | **DEDUP** |
| 17 | `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-3` | 3 | s1: Ragged-band confinement (`.57`, `.63`) / s2: `.91`, `.92`, `.106`, `.136`, `.138`, `.144` / s3: Screened at `.173`, `.175` | s1+s2+s3 | **DEDUP** |
| 18 | `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-T(b)` | 11 | s3: GENHN's own refuted-and-reproved lemma, boxed behind [GENHN-TOW-1] (`.145`) | s3 | — |
| 19 | `GENHN_PROOF_2026-08-08.md:S11.F` | 10 | s1: The per-coefficient certified-window computation (`.34`) / s2: `.91`, `.92`, `.106`, `.136`, `.138`, `.144` / s3: The GENHN S11.F schema cite at the GENIND-6(a) proof (screened, `.144`) | s1+s2+s3 | **DEDUP** |
| 20 | `GENHN_PROOF_2026-08-08.md:S6.2` | 6 | s1: The ghost × letter reconciliation (`.64`) / s2: `.91`, `.92`, `.106`, `.136`, `.138`, `.144` / s3: Screened at `.175` | s1+s2+s3 | **DEDUP** |
| 21 | `GENHN_PROOF_2026-08-08.md:S6.3` | 3 | s1: The general-genre exactness shape (`.57`, `.59`) / s2: `.91`, `.92`, `.106`, `.136`, `.138`, `.144` / s3: The GENHN S6.3 display cite (screened, `.144`) | s1+s2+s3 | **DEDUP** |
| 22 | `GRTJC_PROOF_2026-08-08.md:COROLLARY W-9` | 2 | s1: The precise form cited for dim_K 𝒜(T) = E (`.67`) / s3: `dim_K 𝒜(T) = E`, the stage slot geometry (CS-1) asserts (`.180`) | s1+s3 | **DEDUP** |
| 23 | `GRTJC_PROOF_2026-08-08.md:JC-F1` | 18 | s1: The finding paired with COROLLARY W-9 (`.67`) / s2: `.82`, `.88` / s3: Same (`.180`) | s1+s2+s3 | **DEDUP** |
| 24 | `GRTJC_PROOF_2026-08-08.md:JC-LOAD` | 31 | s1: No-cancellation across ℤ/E degrees (`.05`, `.67`, `.71`, `.72`) / s2: `.82`, `.88` | s1+s2 | **DEDUP** |
| 25 | `GRTJC_PROOF_2026-08-08.md:W-6` | 18 | s1: Carry-corpus member (`.05`) / s2: `.82`, `.88` | s1+s2 | **DEDUP** |
| 26 | `GRTJC_PROOF_2026-08-08.md:W-8` | 35 | s1: No-cancellation warrant (`.05`, `.67`, `.72`) / s2: `.82`, `.88` | s1+s2 | **DEDUP** |
| 27 | `GRTJC_PROOF_2026-08-08.md:W-9` | 13 | s1: The ℤ/E carry grading (`.05`, `.67`, `.68`, `.71`, `.74`) / s2: `.82`, `.88` | s1+s2 | **DEDUP** |
| 28 | `GRTJC_PROOF_2026-08-08.md:dim_K 𝒜(T) = E` | 3 | s1: The stage slot lattice, verbatim (`.05`, `.67`) / s2: `.82`, `.88` / s3: Same, verbatim (`.180`) | s1+s2+s3 | **DEDUP** |
| 29 | `HEX3_PROOF_2026-08-08.md:H-1` | 5 | s1: Depth-0 partition; the n = 3 instance of GENIND-1(i) (`.05`, `.20`) / s2: `.76`, `.78`, `.80`, `.85`, `.96`, `.103`, `.136` | s1+s2 | **DEDUP** |
| 30 | `HEX3_PROOF_2026-08-08.md:H-2` | 11 | s1: α-transport (i)(ii)(iii); the n = 3 instance of GENIND-1(ii)/GENIND-2(a) (`.05`, `.18`, `.21`, `.72`) / s2: `.76`, `.78`, `.80`, `.85`, `.96`, `.103`, `.136` | s1+s2 | **DEDUP** |
| 31 | `HEX3_PROOF_2026-08-08.md:H-3` | 5 | s1: The three β routes (`.05`, `.24`) / s2: `.76`, `.78`, `.80`, `.85`, `.96`, `.103`, `.136` | s1+s2 | **DEDUP** |
| 32 | `HEX3_PROOF_2026-08-08.md:H-4` | 2 | s1: The n = 3 scaffold instance list (`.05`) / s2: `.76`, `.78`, `.80`, `.85`, `.96`, `.103`, `.136` | s1+s2 | **DEDUP** |
| 33 | `HEX3_PROOF_2026-08-08.md:HEX3-BOX-1` | 11 | s2: `.76`, `.78`, `.80`, `.85`, `.96`, `.103`, `.136` | s2 | — |
| 34 | `HEX3_PROOF_2026-08-08.md:HEX3-BOX-2` | 4 | s1: The ledger-compression pricing precedent (`.10`, `.26`, `.42`) / s2: `.76`, `.78`, `.80`, `.85`, `.96`, `.103`, `.136` | s1+s2 | **DEDUP** |
| 35 | `HEX3_PROOF_2026-08-08.md:R(M)` | 21 | s1: The n = 2 drain law consumed by the β drain composition (`.25`, `.45`) / s2: `.76`, `.78`, `.80`, `.85`, `.96`, `.103`, `.136` / s3: The letter-for-letter identity of `.150`'s closed form (`.150`, `.154`) | s1+s2+s3 | **DEDUP** |
| 36 | `HEX3_PROOF_2026-08-08.md:S5.1` | 9 | s1: The n = 3 closed forms tied by GT-N3TIE (`.20`, `.45`) / s2: `.76`, `.78`, `.80`, `.85`, `.96`, `.103`, `.136` | s1+s2 | **DEDUP** |
| 37 | `HEX3_PROOF_2026-08-08.md:THEOREM HEX3.A` | 11 | s1: The n = 3 exact law (consumed by ANNEX R R1's rate leg; named in range at `.45`'s neighbourhood) / s2: `.76`, `.78`, `.80`, `.85`, `.96`, `.103`, `.136` / s3: The R(M) tie and the n = 3 exact law (`.150`, `.154`) | s1+s2+s3 | **DEDUP** |
| 38 | `HEX3_PROOF_2026-08-08.md:THEOREM HEX3.B` | 8 | s1: The n = 3 rate — the species (A2-RATE) generalizes (`.45`, `.46`) / s2: `.76`, `.78`, `.80`, `.85`, `.96`, `.103`, `.136` / s3: The n = 3 rate — the species instance (`.150`, `.151`, `.154`) | s1+s2+s3 | **DEDUP** |
| 39 | `HMENU3_PROOF_2026-08-08.md:HM3-1` | 4 | s1: Two-species classification template (`.04`, `.05`, `.19`, `.20`) / s2: `.86`, `.136`, `.138` | s1+s2 | **DEDUP** |
| 40 | `HMENU3_PROOF_2026-08-08.md:HM3-2` | 5 | s1: Drain-verdict → KEY resolution upgrade (`.05`, `.21`) / s2: `.86`, `.136`, `.138` | s1+s2 | **DEDUP** |
| 41 | `HMENU3_PROOF_2026-08-08.md:HM3-3` | 3 | s1: The n = 3 β-transport instance (`.05`) / s2: `.86`, `.136`, `.138` | s1+s2 | **DEDUP** |
| 42 | `HMENU3_PROOF_2026-08-08.md:HM3-4` | 11 | s1: The n = 3 bracket (q−1)q^{4μ−1} (`.05`, `.09`, `.22`, `.23`) / s2: `.86`, `.136`, `.138` | s1+s2 | **DEDUP** |
| 43 | `HMENU3_PROOF_2026-08-08.md:HM3-BOX-5` | 4 | s1: The finite-relabeling pedantry inherited at Step 2 (`.55`) | s1 | — |
| 44 | `HMENU3_PROOF_2026-08-08.md:HM3.A` | 18 | s1: History-resolved menu form; the raw-key dictionary (`.05`, `.13`, `.24`) / s2: `.86`, `.136`, `.138` | s1+s2 | **DEDUP** |
| 45 | `HMENU3_PROOF_2026-08-08.md:HM3.B` | 19 | s1: The n = 3 (A1) B-families (`.30`) / s2: `.86`, `.136`, `.138` | s1+s2 | **DEDUP** |
| 46 | `HMENU3_PROOF_2026-08-08.md:HM3.C` | 15 | s1: The (A0) argument at general n; the S5.3 exact-complement sharpening (`.44`, `.57`) / s2: `.86`, `.136`, `.138` | s1+s2 | **DEDUP** |
| 47 | `HMENU3_PROOF_2026-08-08.md:HM3.D` | 13 | s2: `.86`, `.136`, `.138` | s2 | — |
| 48 | `JD0_PROOF_2026-08-08.md:J-D0` | 25 | s1: Same, in the note's short form (`.70`) / s2: `.82`, `.87` / s3: Letter-blindness in the pivot species (`.157`) | s1+s2+s3 | **DEDUP** |
| 49 | `JD0_PROOF_2026-08-08.md:LEMMA J-D0` | 4 | s1: Count-gauge blindness (`.05`, `.17`, `.36`, `.55`, `.67`) / s2: `.82`, `.87` | s1+s2 | **DEDUP** |
| 50 | `QSCOUT22_2026-08-08.md:GENRE E` | 2 | s1: The (2,2)-E scout table; prediction target (`.03`, `.48`, `.68`, `.73`) / s2: `.90` | s1+s2 | **DEDUP** |
| 51 | `QSCOUT22_2026-08-08.md:GENRE F` | 1 | s1: The (2,2)-F scout table (`.03`, `.49`) | s1 | — |
| 52 | `QSCOUT22_2026-08-08.md:LEMMA Q22-B` | 1 | s1: Same, in its full designation form (`.69`) | s1 | — |
| 53 | `QSCOUT22_2026-08-08.md:Q22-B` | 6 | s1: The independent budget derivation (`.69`) | s1 | — |
| 54 | `W11_PROOF_2026-08-08.md:THEOREM W-11` | 3 | s1: P(2) base (`.15`) / s2: `.84`, `.94`, `.136` / s3: The supply consumed inside HEX3.A's R(M) (`.150`) | s1+s2+s3 | **DEDUP** |
| 55 | `W12_PROOF_2026-08-08.md:QRT-G2` | 10 | s1: The n = 4 e-first first instance (`.11`, `.48`) / s3: The 4-key stage of the sufficiency construction (`.166`) | s1+s3 | **DEDUP** |
| 56 | `W12_PROOF_2026-08-08.md:S1` | 24 (upper bound) | s1: Conventions; the `[r1 F3]`-corrected refine taxonomy (`.07`, `.17`) | s1 | — |
| 57 | `W12_PROOF_2026-08-08.md:S2.2` | 19 | s1: The Φ-adic bijection and every slot count (`.07`, `.17`, `.36`, `.47`) / s3: The slot count behind the entry pricing (`.152`, `.155`, `.157`, `.189`, `.204`) | s1+s3 | **DEDUP** |
| 58 | `W12_PROOF_2026-08-08.md:S2.3` | 35 (upper bound)!=35 | s1: Certificate transport at simple leaves (`.44`, `.56`) / s2: `.81`, `.83`, `.85`, `.89`, `.93`, `.94`, `.123`, `.136`, `.138` | s1+s2 | **DEDUP** |
| 59 | `W12_PROOF_2026-08-08.md:S2.4` | 10 | s2: `.81`, `.83`, `.85`, `.89`, `.93`, `.94`, `.123`, `.136`, `.138` | s2 | — |
| 60 | `W12_PROOF_2026-08-08.md:S2.5` | 9 | s1: The QRT-G2 opening law, PROVED at the w12 seal (`.11`, `.47`, `.48`, `.68`) / s2: `.81`, `.83`, `.85`, `.89`, `.93`, `.94`, `.123`, `.136`, `.138` / s3: The pinned committed law for the m = 4 instance (`.167`) | s1+s2+s3 | **DEDUP** |
| 61 | `W12_PROOF_2026-08-08.md:S3.4` | 11 | s1: The δ-substitution instance; boundary-family routing (`.30`, `.57`) / s2: `.81`, `.83`, `.85`, `.89`, `.93`, `.94`, `.123`, `.136`, `.138` | s1+s2 | **DEDUP** |
| 62 | `W12_PROOF_2026-08-08.md:THEOREM W-12.A` | 8 | s1: Order-1 decided-shape law at every degree — the induction's leaves (`.05`, `.08`, `.44`, `.46`, `.54`) / s2: `.81`, `.83`, `.85`, `.89`, `.93`, `.94`, `.123`, `.136`, `.138` / s3: The order-1 entry-law pricing cited by C2(iii) (`.180`) | s1+s2+s3 | **DEDUP** |
| 63 | `W12_PROOF_2026-08-08.md:THEOREM W-12.D` | 5 | s1: The reduction fired at Step 5 (`.60`); the whole uniformity consequence (`.15`) / s2: `.81`, `.83`, `.85`, `.89`, `.93`, `.94`, `.123`, `.136`, `.138` | s1+s2 | **DEDUP** |
| 64 | `W12_PROOF_2026-08-08.md:W-12.B` | 19 | s2: `.81`, `.83`, `.85`, `.89`, `.93`, `.94`, `.123`, `.136`, `.138` | s2 | — |
| 65 | `W12_PROOF_2026-08-08.md:W12-BOX-1` | 10 | s2: `.81`, `.83`, `.85`, `.89`, `.93`, `.94`, `.123`, `.136`, `.138` / s3: The box family R1.0's sharpening addresses (`.149`) | s2+s3 | **DEDUP** |
| 66 | `W12_PROOF_2026-08-08.md:W12-L0` | 32 | s1: History-resolved n = 2 menus; P(2) base; GENIND-5's stage laws (`.05`, `.15`, `.70`, `.73`) / s2: `.81`, `.83`, `.85`, `.89`, `.93`, `.94`, `.123`, `.136`, `.138` | s1+s2 | **DEDUP** |
| 67 | `W12_PROOF_2026-08-08.md:W12-L1` | 30 | s1: (a) the level-0 product re-entry; (b) letters move by a unit, hulls do not (`.19`, `.24`, `.35`, `.36`, `.67`) / s2: `.81`, `.83`, `.85`, `.89`, `.93`, `.94`, `.123`, `.136`, `.138` / s3: Letter units in the pivot species (`.157`) | s1+s2+s3 | **DEDUP** |
| 68 | `W12_PROOF_2026-08-08.md:W12-S2.1` | 9 | s1: Level-0 Hensel product; the Hensel split at step (2) (`.07`, `.24`, `.34`, `.54`, `.56`) / s3: The monic-factor Hensel form behind the unit-pivot species (`.157`) | s1+s3 | **DEDUP** |
| 69 | `W12_PROOF_2026-08-08.md:[W12-H]` | 17 | s1: The composite-stage box; (H-e) (`.05`, `.08`, `.43`, `.65`, `.72`, `.74`) / s2: `.81`, `.83`, `.85`, `.89`, `.93`, `.94`, `.123`, `.136`, `.138` | s1+s2 | **DEDUP** |
| 70 | `W12_PROOF_2026-08-08.md:b₂ = 0` | 15 | s2: `.81`, `.83`, `.85`, `.89`, `.93`, `.94`, `.123`, `.136`, `.138` | s2 | — |
| 71 | `W12_PROOF_2026-08-08.md:σ-LABELING` | 7 | s2: `.81`, `.83`, `.85`, `.89`, `.93`, `.94`, `.123`, `.136`, `.138` | s2 | — |
**Designations counted but NOT emitted as XREFs, consolidated from all three shards'
NEAR-MISS dispositions (rule 15) — 15 raw, 3 dedup pairs/triples, 12 distinct:**

- **`HEX3 H-1`** (`.05`, `.20`) — count 0 as note-qualified; fixed-string `H-1` verifies at
  count **5**. Carried at the bare designation. (Shard 1.)
- **`HEX3 S2`** (`.87`) — count 0; a section pointer (`## S2.`), not a designation. Carried
  descriptively. (Shard 1.)
- **`HEX3 S5.2`** (`.140`) — count 0; addressable neighbours `R(M)` (21) and
  `THEOREM HEX3.B` (8) verify. Carried descriptively. (Shard 1.)
- **`HEX3-S4`** (`.97`) — count 0; addressable neighbour `R(M)` (21) verifies. Carried
  descriptively. (Shard 1.)
- **`u₃(M)`** **[DEDUP — shard 1 at `.140`/`.97` and shard 2 at `.85`/`.97`]** — count 0 in
  `HEX3_PROOF_2026-08-08.md`, which writes `u(q,N)` (`:437`) / `u(M)` (`:389`); GENIND-local
  notation for the conservative complement, cited identically from both shards.
- **`GENH4 S6.2`** (`.164`) — count 0 in `GENH4_PROOF_2026-08-08.md` (the count 6 for
  `S6.2` belongs to GENHN's file, a different note); source defect. (Shard 1.)
- **`HEX3.C`** (`.85`) — count 0 in `HEX3_PROOF_2026-08-08.md`; the file's addressable
  theorems verify as `THEOREM HEX3.A` (11) and `THEOREM HEX3.B` (8). Source defect. (Shard 2.)
- **`W-11(iii)`, `W-11(i)`** (`.78`, `.140`) — count 0; `W11_PROOF` uses bare clause labels
  `(i)`/`(iii)`; parent `THEOREM W-11` verifies at count **3**. Carried descriptively.
  (Shard 2.)
- **`[GENHN-HE(μ ≥ 3)]`** **[TRIPLE DEDUP — shard 1 `.15`, shard 2 `.176`, shard 3 `.176`
  (the note's own PE7-m3 correction, homed in shard 2, is re-cited from shard 1 and shard
  3's perspectives)]** — count 0 in `GENHN_PROOF_2026-08-08.md`; the note discloses the
  defect itself at PE7-m3: "the string 'GENHN-HE' occurs at r6 only inside S16 itself …
  the note displays no box by that name; the μ ≥ 3 stage-law content rides inside
  [GENIND-H]." Carried with the note's own correction quoted at every citing shard.
- **`JC-F2`** (`.88`) — not separately grep-recorded; named only inside the compound
  "JC-F1/JC-F2 [r1/r2]". Recorded so the merge does not treat it as a verified consumed
  designation. (Shard 2.)
- **`S5.1, S5.2, S5.3, S7.1, S7.3, S2.2`** as §-pointers inside GENIND itself (shard 3) —
  self-references, not external designations; resolved to shard-1 unit IDs throughout this
  compilation, not emitted as XREFs.
- **`row 17`** (`.195`, `.206`) — not a row of `spec/HYPOTHESIS_LEDGER.md` (whose rows are
  `HYP.nn`); a row of the certification campaign's own ledger, which the note never names.
  **Carried as OPEN-CALL 5** (below), not resolved by this compilation.

**Commit-pin and artifact-existence verification, consolidated (each shard's own
in-range check; a cross-shard commit-hash dedup was not separately computed, unlike the
designation ledger above, since the safety property that matters — 100% resolution — is
already exhaustive per shard):**

| Shard | Distinct commit hashes cited in range | `git cat-file -t` resolution | Artifacts/reports verified present |
|---|---:|---:|---:|
| 1 | 29 | 29/29 ✓ | 25/25 ✓ |
| 2 | 87 | 87/87 ✓ | 28/28 ✓ |
| 3 | 12 | 12/12 ✓ | 13/13 ✓ |
| **Total pin-checks** | **128** | **128/128 ✓** | **66/66 ✓** |

**Zero unresolvable commit pins and zero missing artifacts across the whole merged
corpus.** The one recorded pin-adjacent defect in the whole note is an md5 typo
(`e5493312` → `e549331a`), self-caught by the note's own commit-time re-verification and
disclosed at `.135`; it is not a commit hash and does not enter the table above.

### Sample re-verification (12 of 71, grep-rerun at merge time against the working tree)

`[TABLE — compiler ledger]`

| Target : designation | Recorded count | Re-verified count | Match |
|---|---:|---:|---|
| `GENH4_PROOF_2026-08-08.md:GENH4-1F` | 10 | 10 | OK |
| `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-3` | 3 | 3 | OK |
| `GRTJC_PROOF_2026-08-08.md:dim_K 𝒜(T) = E` | 3 | 3 | OK |
| `HEX3_PROOF_2026-08-08.md:THEOREM HEX3.A` | 11 | 11 | OK |
| `HEX3_PROOF_2026-08-08.md:HEX3-BOX-1` | 11 | 11 | OK |
| `HMENU3_PROOF_2026-08-08.md:HM3.C` | 15 | 15 | OK |
| `JD0_PROOF_2026-08-08.md:J-D0` | 25 | 25 | OK |
| `W12_PROOF_2026-08-08.md:THEOREM W-12.D` | 5 | 5 | OK |
| `W12_PROOF_2026-08-08.md:S2.2` | 19 | 19 | OK |
| `W11_PROOF_2026-08-08.md:THEOREM W-11` | 3 | 3 | OK |
| `QSCOUT22_2026-08-08.md:GENRE E` | 2 | 2 | OK |
| `W10_PROOF_2026-08-08.md:W10-BOX-3` | 1 | 1 | OK |

**All 12 sampled counts match exactly; no drift introduced by sharding or merge.** The
sample deliberately covers: three triple-shard-cited designations (`GENH4-1F`,
`LEMMA GENHN-3`, `dim_K 𝒜(T) = E`), the note's two heaviest suppliers by citation volume
(W-12, HEX3), a single-shard-only designation (`HEX3-BOX-1`, shard 2 alone), and the two
smallest-count rows in the whole ledger (`GENRE E` = 2, `W10-BOX-3` = 1) — the rows most
likely to show a copy error, since a large count masks a single miscount but a count of 1
or 2 does not.

### Sample statement-quote re-verification (6 of 206, checked byte-exact against the source note by line number)

`[TABLE — compiler ledger]`

| Statement | Quoted fragment | Source lines | Match |
|---|---|---|---|
| `.01` (title + Status arc) | "# GENIND — THE GENERAL TWO-SPECIES INDUCTION … the composite-stage law displayed as the frontier with the quartic (2,2) bracket attempted from the weld corpus" | 1 | OK, byte-exact |
| `.04` (What GENIND is) | "**What GENIND is (one breath).** THEOREM W-12.D (PROVED, an unconditional reduction) turns {(A0) lift well-posedness + (A1) exact disjoint q-uniform core menu + (A2) drainage} at degree n into ONE R_τ ∈ ℚ(q) per splitting type …" | 70–73 | OK, byte-exact |
| `.79` (=s2.05, GENIND-BOX-5 grades, the PE1–PE6 arc) | "GENIND-BOX-5 (grades). 0/2; PE1 (hostile, fresh context) adjudicated 0C + 3G + 4m …" | 1373–1376 | OK, byte-exact |
| `.146` (=s2.72, dated acceptance record) | "### Dated acceptance record (2026-08-09, post-PE8) **GENIND IS ACCEPTED 2/2; the text is FROZEN — dated appends only.** PE7 (hostile, fresh context …" | 2510–2513 | OK, byte-exact |
| `.148` (=s3.01, ANNEX R provenance) | "## ANNEX R (2026-08-09, post-ratification; CODEX F1-F6) **Provenance and scope.** The ratification sweep's Codex leg (`CODEX_GENINDRAT_2026-08-09.md` …" | 2552–2556 | OK, byte-exact |
| `.153` (=s3.06, ANNEX-THEOREM GENIND.C′) | "**R1.3 ANNEX-THEOREM GENIND.C′ (the vanishing clause, quantitative form — the induction closed).** For the simple slice of each (m, d): there are (K, B, c) with u^{simple}_{m,d}(N)/Q^{m(N−1)} ≤ K·N^B·Q^{−(N−c)} …" | 2728–2731 | OK, byte-exact |

**All 6 sampled quotes are byte-identical to the source note at the cited lines; no drift
introduced.** The sample covers all three shards' HOME ranges, the note's title/opening
(`.01`) and its terminal acceptance layer (`.146`, `.148`, `.153`), and one of the corpus's
most heavily-audited units (`.153`, the R1.3 vanishing clause whose every displayed step
shard 3's own compiler re-derived independently — see `.153`'s ARITHMETIC AUDIT).

---

## 5. Local supply/consumption ledger

### 5.1 Per-supplier mathematical supply versus append/consumption protocol (merged from all three shards' reverse-consumer-edge tables; the mathematical-status column kept strictly distinct from the protocol column per the header's predicate split)

`[TABLE — compiler ledger]`

| Supplier note | Verified designation(s) | GENIND supply / consumption (EFF units) | Mathematical status | Append/consumption-protocol status |
|---|---|---|---|---|
| W12_PROOF | `THEOREM W-12.D` (5), `THEOREM W-12.A` (8), `W12-L0` (32), `W12-L1` (30), `[W12-H]` (17), `W12-BOX-1` (10), `W-12.B` (19), `σ-LABELING` (7), `b₂ = 0` (15) | `.05`, `.07`–`.11`, `.15`, `.19`–`.20`, `.49`, `.60`, `.62`, `.64`, `.67`, `.83`, `.94`, `.152` | The reduction fires at Step 5 on P(n)'s hypotheses; order-1 leaves at every degree PROVED; the r4 σ-LABELING clause STRENGTHENS (A1) mid-arc, crossing a repaired CRITICAL (F1) — consumption verdict re-verified verbatim and SURVIVES | **Nothing landed by GENIND.** §S9.1 offers annex text, "W12_PROOF not edited"; the pin moves r2→r5 (`99f1813`→`be4a1dc`/`ee17210`) by inbound supplier movement only |
| HEX3_PROOF | `H-1`(5)…`H-4`(2), `THEOREM HEX3.A`(11), `THEOREM HEX3.B`(8), `HEX3-BOX-1`(11), `R(M)`(21) | `.05`, `.18`, `.20`–`.22`, `.24`–`.25`, `.29`, `.45`–`.46`, `.62`, `.72`, `.85`, `.150`, `.151`, `.154` | n = 3 transport instances PROVED and consumed as base cases; the (2,d)-instance closed forms are LETTER-FOR-LETTER identical to HEX3.A's committed R(M) display (`.150`'s machine leg B ties them at M = 1..14); HEX3-BOX-1's tail-σ lemma conditions a corroboration aside, not GENIND's induction (ledger HYP.137, see `.85`) | Not landed. **Inbound**: two repair rounds, one conditionalizing an aside on the open tail-σ lemma — both corrected items are records GENIND never cites, so consumption SURVIVES |
| HMENU3_PROOF | `HM3-1`(4)…`HM3-4`(11), `HM3.A`(18)…`HM3.D`(13) | `.04`–`.05`, `.09`, `.12`–`.13`, `.19`–`.24`, `.30`, `.44`, `.57`, `.86` | Two-species classification template, the raw-key dictionary, the n = 3 bracket instance PROVED and consumed as base data | Not landed. **Inbound**: ACCEPTED 2/2 + ANNEX A, which corrects HM3.C's quantifier exactly TOWARD the disc ≠ 0 form GENIND's S5.2/S6-Step-4 arguments already consume — the strongest SURVIVES verdict in the whole stack |
| W11_PROOF | `THEOREM W-11` (3) | `.15`, `.84` | P(2) base, PROVED | Not landed. **Inbound**: accepted 2/2, zero content diff |
| JD0_PROOF | `LEMMA J-D0` (4), `J-D0` (25) | `.05`, `.17`, `.36`, `.55`, `.67`, `.87` | Count-gauge-blindness frame, corroborated again by the char-tally battery legs | Not landed; pin unmoved (HEAD, pre-seal) |
| GRTJC_PROOF | `W-6`(18), `W-8`(35), `W-9`(13), `COROLLARY W-9`(2), `JC-F1`(18), `JC-LOAD`(31), `dim_K 𝒜(T) = E`(3) | `.05`, `.67`, `.88` | Consumed ONLY at §S7's display (slot geometry + no-cancellation); **no count law of S2–S6 consumes them** — a NON-IMPORT fence | Not landed; body unmoved since a pre-seal annex |
| WELDMASTER / DULEMMA / [W12-H] | (no addressable designation cited in range; existence-verified) | `.89` | Named in S7.1's (CS-1..3) pricing only | Not landed; bodies unmoved at their accepted pins |
| GENHN_PROOF | `GENHN.A(iv)`(3), `GENHN.A(v)`(6), `LEMMA GENHN-3`(3), `S6.2`(6), `S11.F`(10), `S6.3`(3), `GENHN.A(i)`(11), `GENHN-TOW-1`(19), `GENHN.C`(19), `LEMMA GENHN-T(b)`(11) | `.34`, `.37`, `.57`, `.63`–`.64`, `.91`, `.175`–`.176` | Seven consumed sites after PE7-m2's completion (not four, as first stated); one lemma refuted and re-proved (T(b)→T(b)′), boxed behind [GENHN-TOW-1] | Not landed. **Inbound**: errata E1–E3 + an r2 round, screened clause-by-clause; the n ≥ 8 conditionality gains two conjuncts as a direct consequence |
| GENH4_PROOF | `THEOREM GENH4.A`(5), `THEOREM GENH4.B`(6), `GENH4-1F`(10), `GENH4-2`(15), `GENH4.D`(8), `Q22-L1`(7), `Q22-L3`(3), `GENH4-CAP(F)`(11), `GENH4-BOX-7`(1), `ANNEX-LEMMA GENH4-7`(11) | `.59`, `.66`, `.92`, `.136` | The n = 4 de facto discharge of (CS-EXACT); (CS-1) = GENIND-4 + GENH4-1F + GENH4-2/-3/-4 package | Not landed; GENIND records the supplier's own annex-stack grade (0/2, pass #2 in flight) rather than inheriting it as its own |
| QSCOUT22 | `GENRE E`(2), `GENRE F`(1), `Q22-B`(6), `LEMMA Q22-B`(1) | `.03`, `.16`, `.73`, `.90` | **Nothing consumed** — a division-of-labor peer, an independent budget cross-check, and two preregistered falsifiable predictions handed over | Not landed; nothing consumed, by declaration. The scout's own arc completed (GREEN 7,614,473/0) with an L3-correction annex, but **no unit anywhere records whether GENIND's predictions were scored** (OPEN-CALL, below) |
| W10_PROOF | `W10-BOX-3` (1) | `.06` | Lineage pointer for the reader-reimplementation seam | Not landed; **source defect** — W-10 is cited but carries no §S9.3 bullet, no pin, no §S16 row: an untracked supplier |
| GENIND itself (inbound) | `CODEX_GENINDRAT_2026-08-09.md:F1–F6` | `.148`–`.170` | Six Codex-ratification findings (three CONFIRMED GAP, three regraded MINOR), discharged by ANNEX R at annex grade (not itself hostile-passed) | The annex IS the landing on GENIND's own frozen text — nothing above ANNEX R is edited |
| GENIND itself (inbound) | sol certification `runs/cert/R9_drain_repair_output.log`, `runs/cert3/R11_genind_output.log` | `.195`–`.206` | Two dated corrections, each superseding parts of the layer before it (R9 supersedes L3's GENIND-C2 in full; R11 supersedes three named parts of R9's) | Pure appends; "Everything above this heading is byte-untouched" |
| GENIND itself (inbound) | the PE8 acceptance report's §4.1 rationale | `.170` | A false monotonicity display in a **verifier's own artifact** | The report is NOT edited — REPORT-FREEZE predicate 4; the notice lives here and at the ledger only |

**The protocol column is not an inference.** GENIND states the "lands nothing" protocol in
its own words at `.06` ("This note edits no supplier note") and again at §S9.1's heading.
**Zero consumption appends are claimed landed on any supplier by this note, and none is
invented here.** In the reverse direction GENIND *received*: eight in-house hostile
passes, one Codex ratification, two sol certification runs, and two supplier movements
(GENHN's errata + r2; GENH4's annex arc) — sixteen received-correction channels against
zero appends made, the most asymmetric supply/consumption ratio recorded in this repo's
0a campaign to date.

### 5.2 One hypothesis-ledger cross-reference this merge re-verified, and one candidate flagged for the maintenance queue

`spec/HYPOTHESIS_LEDGER.md` row **HYP.137** (`HEX3-BOX-1` tail-σ-certification lemma) names
GENIND explicitly as a consumer at `.85`'s CONDITIONALITY field; this merge re-verified the
ledger's three supporting quotes against `HEX3_PROOF_2026-08-08.md` at HEAD and all three
match verbatim (`:437`, `:686`, `:692–693`). **This merge does not add a new
`spec/HYPOTHESIS_LEDGER.md` entry** (out of this deliverable's scope) but flags, for the
maintenance queue, the same kind of arithmetic defect the ledger's MQ entries already
track: `.85`'s (=s2.11's) census correction ("11 → 12 pairs", HEX3's r2 round) is cited but
not independently recomputable from anything displayed in GENIND itself — recorded there
as `UNPINNED-BY-DISPLAY`, not repeated here as a new claim.

---

## 6. TEETH inverse table (unified from all three shards; presented as three sub-tables by
shard-of-origin — the battery legs themselves are naturally partitioned this way, since
shard 1 carries the core P1–P9/GT-family battery, shard 2 carries the additive
record-integrity audits and the git-log/verbatim-match checks, and shard 3 carries ANNEX
R's legs A–I, the annexr1 checks, and the two sol-certification orchestrator
verifications — with one combined zero-orphan statement closing all three)

### 6.1 Shard 1's core battery (IDs unchanged, offset 0)


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

### 6.2 Shard 2's additive record-integrity, git-log, and verbatim-match legs (renumbered, +74 offset)


`[TABLE — compiler ledger]` **This shard homes the battery's DESCRIPTION (`.95`–`.97`), its PREREGISTRATION (`.99`, `.100`) and its RUN-RECORD (`.102`, `.103`)** — the three that rule 19 separates. The guarded units are overwhelmingly in shard 1; the rows below therefore point *outward*, and the inverse direction (which shard-2 unit each row guards) is given in the second column.

| Battery row / instrument | Shard-2 unit(s) guarded | Disposition |
|---|---|---|
| **GT-PIN** 0/5, re-verified 5/5 at r6 | `.83`–`.93` (the pins' artifact side), `.136`, `.142` | Executable regression on artifact md5s; **does not guard note pins** |
| **GT-PART / GT-DEPTH0 / GT-BDRAIN / GT-ALPHA / GT-BETA / GT-RECUR / GT-BRACKETID / GT-CRIT / GT-N3TIE / GT-CONS / GT-ORACLE** | `.96` (their inventory), `.99` (their predictions), `.103` (their scores) | Executable regressions; per-family dispositions are in shard 1's §5 |
| **GT-T-ALPHA / GT-T-CS / GT-T-CRIT / GT-T-BRACKET**, fired at 12/12/4/24 | `.99`, `.102`, `.103` | Planted teeth, all fired at preregistered counts |
| **Pre-seal smoke run 1 (RED)** | `.98`, and shard 1 `.125` | Executable regression, **fired before the seal**, producing a MATH-side correction |
| **Pre-seal smoke run 2 + three probes** | `.98` | Executable regression; the cost probe's 1,048,576 partition audited exact |
| **`genindr2_supp.py`** (2,128,163/0; T1/T2/T4 fired) | `.106`, `.109` | Executable regression + three planted mutants |
| **`genind_pe3_fresh.*`** (705,133/0) | `.110`, `.111`, `.113`, `.114`, `.115` | Foreign-note (verifier) evidence |
| **`genind_pe4_fresh.*`** (6,507/0) | `.117`, `.118`, `.119`, `.120`, `.123` | Foreign-note evidence; C12's isolated re-run of the SEALED battery is the strongest single row (163,536/0 reproduced) |
| **`genind_pe5_fresh.*`** (109,146/0) | `.128`, `.129`, `.131` | Foreign-note evidence |
| **`genind_pe6_fresh.*`** (2,132,082/0) | `.135`, `.136` | Foreign-note evidence; realizes the same-side f-first genre corpus-first |
| **`genind_pe7_fresh.*` / `genind_pe8_fresh.*`** | `.146` | Foreign-note evidence; the two CLEAN passes' routes (d ≥ 2, n = 10; non-prime q, n = 12) |
| **git-log checks at commit time** | `.83`–`.93`, `.107`, `.112`, `.124`, `.134`, `.136`, `.137`, `.142` | **AUDIT: `in-house hostile pass` / `transfer audit`** — no battery row can perform these, which is the whole content of SERIES RECORD-INTEGRITY |
| **verbatim supplier-text matches** | `.138`, `.139` | **AUDIT: `transfer audit`** at verbatim granularity — the shard's gold-standard rows |
| **md5 re-enumeration at commit time** | `.127` (8, unreconciled), `.134` (13 ✓), `.142` (16 ✓) | **AUDIT: `arithmetic recount`**; two of three reconcile exactly |

**PROOF-ONLY rows (rule 16)** — guarded units whose content is a record or a fence, with the note's own coverage sentence:

| Unit | Coverage sentence |
|---|---|
| `.75` | “No count law at order ≥ 2 is claimed proved.” |
| `.76` | “per-route ledgers compressed … The n = 4, 5 pointwise machine families are the compensating instrument.” |
| `.77` | “machine-uncorroborated here beyond the w12-sealed order-1 instances” |
| `.78` | “displayed, not expanded per genre” |
| `.80` | “the reader-reimplementation seams (W10-BOX-3 lineage) inherited” |
| `.81` | offered text, never consumed — no coverage claimed |

**Both-direction audit.** Every row above guards at least one shard-2 unit. Every shard-2 unit whose TEETH field names a row appears in some row. Units with **`TEETH: NONE`** — `.75`, `.81`, `.82`, `.88`, `.89`, `.93`, `.94`, `.116` — are fences, plans, citations or inventory repairs and are outside the orphan count. **Zero battery-row orphans; zero toothed-unit orphans.**

**Signed vacuity / disclosure dispositions, enumerated** (rule 20): `.77` (d ≥ 2 and prime-power, for this note's own battery), `.80` (the reimplementation seam), `.90` (nothing consumed, so nothing guarded), `.136` row 7 (a de facto discharge riding an annex stack at 0/2), `.139` (the n = 4 exactness discharge is a citation, not a measurement). **`stale self-description` instances, enumerated** (rule 26): `.77` (coverage overtaken by PE7/PE8), `.81` (the offered annex text), `.104` (§S11's two frozen clauses — **not covered by the PE8-m1 cure**, OPEN-CALL 3), `.125` (the 14-group tally, falsified by C14's own correction), `.127` (the C1–C14 clause), `.129` (the HONEST LIMIT, closed by PE6 without edit).


---

### 6.3 Shard 3's ANNEX R legs, the annexr1 checks, and the sol-certification verifications (renumbered, +147 offset)


`[TABLE — compiler ledger]`

| Instrument / audit row | Guarded unit(s) | Disposition |
|---|---|---|
| **`genind_annexr_supp.py` leg A** — the m = 2 closed forms solve the recursion symbolically at N = 2..14 | `.150` | Executable regression (symbolic) |
| **leg B** — the closed forms equal the committed `R(M)` at M = 1..14 | `.150`, `.151` | **`accepted-with-decorrelation-supplied`** — the tie is to a committed SUPPLIER display |
| **leg C** — `u(N) ≤ N·Q^{N−1}` at N = 2..14, Q ∈ {2,3,4,5,8,9} | `.150`, `.151` | Executable regression |
| **leg D** — the depth identity `D+M = N` at six committed extractions (M6, TWOCHILD A/B, PSTEEP3, PSTEEP4, SS6) | `.152`(iii) | Executable regression; **a definitional identity checked against hull data** |
| **leg E** — the prefactor bound at three committed loci (M6, PSTEEP3, PSTEEP4) | `.152`(i) | Executable regression; **all three re-derived by this compiler and exact** |
| **leg F** — monotonicity `∂G/∂u_i ≥ 0` and union-bound dominance, symbolic at r = 2, 3 | `.152`(ii), `.169`, `.170` | Executable regression **+ preregistered decorrelation** (“two decorrelated models, same kill”) |
| **leg G** — the unit-pivot toy over ℤ/4: `(x+2)y` collapses, `(1+2x)y` does not | `.156`, `.157`, `.158` | **Planted mutant, fired**; realizes the finding's counterexample |
| **leg H** — the two CS4-F gate lines read verbatim in the md5-pinned runner; (2,2,1) gated to 0; (2,5,1) = 64 | `.163`, `.164` | **Source-code gate verification** — an executable regression against the instrument's TEXT |
| **leg I** — window-1 at (m, Q) ∈ {2,3,4}² : 1 state, DRAIN, u(1) = 1 | `.160`, `.161` | Executable regression **+ a decorrelated sympy re-solve** |
| **`genind_annexr1_checks.py` P1** — the window bound at 11 scored fresh rows | `.180`, `.181`, `.183`, `.185` | Executable regression, GREEN 11/0 |
| **P2** — the species bound at (K,B,c) = (1,1,2), margins 10²–10⁴ | `.180`, `.185` | Executable regression, GREEN 9/0 |
| **P3** — consecutive-N slope, 6-of-7 | `.180`, `.185` | Executable regression **with one FLAGGED line and an open adjudication** (`disclosed non-repair`); genre E measured at exactly 2.00 |
| **P4** — the CS5-V1E2 entry identity + composed n = 5 bound, sympy + grid to N = 40 | `.181`, `.185` | Executable regression, GREEN 112/0 |
| **P5** — the `D+M = N` composition identity, sympy | `.152`(iii), `.185` | Executable regression, GREEN 1/0 |
| **T-SLOPE** — a fabricated slope-1/2 n = 4 E-drain (262,144) violates the P1 bound (65,536) | `.180`, `.185` | **Planted mutant, fired**; the pass report's failure scenario made flesh |
| **T-WIN** — the mis-derived window `2N−2−2h` refuted by the committed deep row (Zp,2,11,h=5) | `.180`, `.183`, `.185` | **Planted mutant, fired** |
| **the PINNED GENH4 walker's own live checks** — GH-FRESH, GH-UND, GH-BRACKET, silent at all 12 rows | `.185` | Foreign-note (supplier-instrument) evidence, run live as a silent guard |
| **orchestrator pre-transcription verification (R9)** | `.189`, `.190`, `.192`, `.193`, `.194`, `.195` | **AUDIT: `in-house hostile pass`** — **with a disclosed miss** (it passed the descent step R11 later refuted) |
| **orchestrator pre-transcription verification (R11)** | `.198`, `.201`, `.202`, `.204`, `.206` | **AUDIT: `in-house hostile pass`** — no item since refuted |
| **the diff-granularity GENHN screen** (seven sites) | `.173`, `.174`, `.175` | **AUDIT: `transfer audit`** at diff granularity |
| **this compiler's arithmetic audits** | `.150`, `.152`, `.160`, `.181`, `.189`, `.190`, `.194`, `.198`, `.201`, `.202`, `.204`, `.205` | **AUDIT: `arithmetic recount`** — twelve units re-derived independently; **all agree with the source** |

**PROOF-ONLY rows (rule 16)** — the note's own coverage sentence for each:

| Unit | Coverage sentence |
|---|---|
| `.153` (GENIND.C′) | no machine leg for the induction; only the ground instance is tested |
| `.157` (the pivot species) | “the per-genre ledgers remain compressed per the S4.3 honesty box” (`.158`) |
| `.189` (the Q-normalized C2) | **untested — the r1 leg predates it** (OPEN-CALL 2) |
| `.197`, `.198`, `.201`, `.202`, `.204` (the whole R11 layer) | **no machine leg was added at R11**; “A universal discharge … remains obstructed” (`.199`) |

**Both-direction audit.** Every instrument row above guards at least one unit; every unit whose TEETH field names a leg appears in some row. **`TEETH: NONE`** units — `.148`, `.149`, `.154`, `.155`, `.159`, `.162`, `.165`, `.166` (audit only), `.168`, `.172`, `.173`, `.174`, `.176`, `.177`, `.178`, `.179`, `.182`, `.184`, `.186`, `.187`, `.188`, `.191`, `.192`, `.193`, `.194`, `.195`, `.196`, `.197`, `.198`, `.199`, `.200`, `.201`, `.202`, `.203`, `.204`, `.205`, `.206` — are findings, riders, fences, install records, or **proved-but-unexercised lemmas**. **Zero instrument-row orphans.**

**Signed vacuity disclosures, enumerated** (rule 20): `.176` (n ≥ 8 conditionality, nothing reaches degree 8), `.189` (the Q-normalized lemma, untested), `.197` (**(CS-1Q), per-genre unverified — the shard's headline disclosure**), `.198`, `.201`, `.202`, `.204` (the whole R11 layer, proved and unexercised), `.167` (R5's verification is a consumer walk, no leg). **`stale self-description (uncured)`** (rule 26): `.172` (“has NOT itself been through a hostile pass”), `.182` and `.191` (“(CS-1) only” / “no new hypothesis”), `.186` (“conditional on (CS-1) only”).

**The single most important row in this table is an ABSENCE:** the R11 layer — five units of new mathematics (`.197`, `.198`, `.201`, `.202`, `.204`) — carries **no machine leg at all**, and the layer it repairs carries one that was run against a superseded version. Every arithmetic check on it in this spec is this compiler's own.


---

**Combined zero-orphan statement (all three shards' independent audits agree).** Across
the whole merged inventory: every battery row/tooth/audit-instrument guards at least one
unit; every unit whose TEETH field names a row appears in some row above; zero
battery-row orphans and zero toothed-unit orphans in any of the three sub-tables.
**GENIND's own structural finding, visible only once all three sub-tables are read
together:** the note's SEALED battery (shard 1/shard 2, P1–P9 + GT-families, GREEN
throughout its own scope) never found a defect in GENIND's own text — every one of the
note's genuine mathematical gaps (the (A2-RATE) vanishing-rate hypothesis, the unit-pivot
condition, the five consecutive record-integrity findings, the two sol-certification
defects in the CS-drain repair chain) was found by a **fresh-context read** — an in-house
hostile pass, a decorrelated Codex ratification, or a sol certification run — never by a
battery row disagreeing with a displayed number. **This is the same limit HE7's merge
recorded independently** ("a machine battery cannot falsify a definition's incoherence or
an underived equivalence"), now confirmed a second time on a structurally different note:
GENIND's battery measures exact counts and exact identities, and every one of its open
mathematical gaps lives in an UNDISPLAYED hypothesis or an UNDERIVED step, which an exact
count is, by construction, silent about.

---

## 7. SERIES, supersession CHAINs, and cross-shard boundary resolution

### 7.1 Three declared SERIES (rule 28), assembled across shard lines

**SERIES REPAIR-ARC.** The five dated repair records r2…r6, continued by the post-PE7
dated corrections and closed by the dated acceptance record:

`[TABLE — compiler ledger, assembled from `.79`'s own arc-close sentence plus the five
records' own grade-close lines]`

| Link | Unit | Round | Grade | Content |
|---:|---|---|---|---|
| 0 (origin) | `.79` (=s2.05) | base + r1..r6 | 0/2 | PE1 0C+3G+4m … PE6 0C+1G+1m, "the clean count has NOT started" |
| 1 | `.105` (=s2.31) | r2 | stays 0/2 | PE2 0C+2G+1m |
| 2 | `.110` (=s2.36) | r3 | stays 0/2 | PE3 0C+2G+4m |
| 3 | `.118` (=s2.44) | r4 | stays 0/2 | PE4 0C+2G+0m, full-sweep audit |
| 4 | `.128` (=s2.54) | r5 | stays 0/2 | PE5 0C+1G+2m, standing-rule round |
| 5 | `.135` (=s2.61) | r6 | stays 0/2 | PE6 0C+1G+1m, supplier re-pin round |
| 6 | `.143` (=s3's post-PE7 corrections area, cross-cited at `.146`) | dated append | 0/2 → 1/2 | PE7 CLEAN, 0C+0G+3m |
| 7 (terminal) | `.146` (=s2.72) | dated append | 1/2 → **2/2, ACCEPTED** | PE8 CLEAN, 0C+0G+1m; "PE8-m1 cure" supersedes the arc-close sentence by name |

**Arithmetic audit (re-derived from the eight pass tallies, compiler-computed):** GAP
count falls monotonically 3, 2, 2, 2, 1, 1, 0, 0 across PE1–PE8 — a genuinely monotone arc,
matching `.79`'s own count; total 11 GAP + 16 MINOR + **0 CRITICAL over eight consecutive
hostile passes**, the same zero-CRITICAL record HE7's own merge found across its eight
comparable rounds.

**SERIES RECORD-INTEGRITY.** The note's own named chain of five consecutive
record-integrity findings — **this series is the note's diagnosis of itself**, and its
members are a DIFFERENT selection of rounds than REPAIR-ARC's (it names the *finding*
inside each round's Arc, not the round's grade close):

| Link | Unit | Finding | What it found |
|---:|---|---|---|
| 1 | `.107` (=s2.33) | PE2-G2 | a repo-checkable factual sentence in a repair record, false against the repo |
| 2 | `.112` (=s2.38) | PE3-G1 | same genre, a second repair record |
| 3 | `.120` (=s2.46) | PE4-G1 | same genre, a third repair record |
| 4 | `.129` (=s2.55) | PE5-G1 | same genre, a fourth repair record |
| 5 (terminal — the note's own remedy escalation) | `.135` (=s2.61) | PE6-G1 | the fifth, cured by **abolishing the summary sentence and replacing it with a per-supplier table** (§S16) |

The note's own remedy escalated five times across this series — pin-at-repair-HEAD (r2) →
commit-time git-log check (r3) → grep-scoped full sweep (r4) → ban the universal register
(r5) → replace the summary sentence with a table (r6) — **and only the last held.** Every
one of the five findings was produced by a fresh-context read of the repo; none by any
battery row (§6's combined zero-orphan statement).

**SERIES GENH4-PIN.** Four dated appends on the GENH4 bullet, all inside one unit
(`.92` = s2.18), recorded in source order with a TERMINAL marker — kept as ONE unit
carrying an explicit series table (not four units) because the four appends are revisions
of the same pin and only the last is live:

| Entry | Round | Pin |
|---:|---|---|
| 1 | `[r3]` | seal → first re-pin |
| 2 | `[r4]` | annex arc opens |
| 3 | `[r5]` | annex arc continues |
| 4 (TERMINAL) | `[r6]` | annex-stack pin, grade 0/2 with pass #2 in flight — **not inherited as GENIND's own grade** |

**A fourth, undeclared-but-reconstructible SERIES: the dated acceptance record's own
grade chronology**, parallel to EFF-HE7's §7.1 table and assembled here the same way (one
block, not five independent units): `.79`(0/2, PE1–PE6) → `.146`(1/2, PE7 CLEAN) → **`.146`
(2/2, PE8 CLEAN, ACCEPTED)** → `.148`(2/2, ANNOTATED by the Codex CHALLENGE, not revoked)
→ `.206`(the annex stack's own grade, still 0/2 at its close, "awaiting a clean re-pass").
**The durable content that survives every grade movement:** `.146`'s own closing sentence,
re-asserted after acceptance — "the acceptance freezes the reduction and its record, not
the box" — [GENIND-H] at n ≥ 4 remains open regardless of the record's grade.

### 7.2 Supersession CHAINs with TERMINAL markers verified unique

**The CS-drain rate CHAIN — the corpus's longest, at five layers, and its two-terminal
case (the same v3-rule-25 gap HE7's merge flagged independently, now confirmed on a
second note):**

sealed "exact-complement (A2)" (`.13`) → **(A2-RATE)** species pin (`.152`) → `[ar1]`
two-part split: simple part by GENIND.C′, CS-drain part by GENIND-C2 under (CS-1)
(`.152`) → R9's Q-normalized GENIND-C2 (`.189`) → **R11's C2Q under (CS-1Q), verified per
genre (`.197`, `.198`) — TERMINAL for the CS-drain-consuming part; GENIND.C′ (`.153`) —
TERMINAL for the simple-slice-consuming part.** Every displayed consumer of §S5.2's
vanishing bullet needs only the simple part, per the `[ar1]` rider's own closing clause —
**the single sentence a chapter cut must carry with this chain.**

**The (CS-1) hypothesis CHAIN — also two-terminal, a DIFFERENT split (by consumer class,
not by proof layer):** sealed (CS-1) → `[r2]`-corrected (CS-1) — **TERMINAL for
menu/transport consumers** (`.60`) → **(CS-1Q), verified per genre — TERMINAL for
rate consumers** (`.197`, consumed at `.140` Step 4 and `.106` GENIND-6(d)). Ledger row
**HYP.36** (`spec/HYPOTHESIS_LEDGER.md:310–315`) rides with this chain; disposition CARRY.

**The W-12 pin CHAIN, crossing a repaired CRITICAL:** sealed pin `r2 99f1813` (stale arc
parenthetical "PE2 adjudicated + r2, PE3 owed", true at 08-08 10:16, false three rounds
later) → `[r6]` RE-PIN to **`r5 HEAD be4a1dc/ee17210` — TERMINAL**, three intervening
rounds enumerated (r3 GAP; **r4 CRITICAL F1 repaired** — S3.2's b₂ = 0 witness pair; r5 GAP
+ 3m) → PE7-m1's further correction of the SURVIVAL evidence's own wording (`.144`) — a
wording-rider on the terminal link, not a new terminal.

**The HEX3 pin CHAIN:** sealed `r1 2580f12` → `[r6]` RE-PIN to **`r3 HEAD b6a1d69` —
TERMINAL** (r2 a census undercount; r3 an aside conditionalized on the open HEX3-BOX-1
tail-σ lemma) — GENIND's consumption SURVIVES throughout because it never cites either
corrected item.

**The HMENU3 pin CHAIN — the stack's strongest SURVIVES verdict:** sealed
`64d3ff9/625fa49` ("r1 owed") → r1 `3235e1b` → r2 `e1280be` → **ACCEPTED 2/2 `050425d`** →
**ANNEX A `19c0285` — TERMINAL** — the only chain in the whole corpus where the supplier's
correction moves TOWARD GENIND's own consumed form rather than merely past it.

**The W-11 pin CHAIN (the cleanest, an honest strengthening):** sealed `7020ceb` → r2
`31506b3` → PE3 CLEAN `839b735` (1/2) → **`[r6]` ACCEPTED 2/2 `35e6545` — TERMINAL**, zero
content diff to the consumed body.

### 7.3 Cross-shard boundary resolution — consolidated edge list (24 edges, from the three
shards' own SHARD NOTES/MERGE HAZARDS sections, deduplicated where the same edge was
flagged from both ends)

`[TABLE — compiler ledger]`

| From (supersedes/riders/discharges) | Target | Nature |
|---|---|---|
| `.146` (PE8-m1 cure) | `.01` (header arc line) | Supersedes by name, quoted verbatim |
| `.146` (PE8-m1 cure) | `.79` (GENIND-BOX-5 arc close) | Supersedes by name, quoted verbatim; **explicitly NOT** the five per-round grade closes `.109`,`.117`,`.127`,`.134`,`.142` |
| `.148`–`.170` (ANNEX R R1–R6) | `.11`,`.13`,`.14`,`.24`,`.36`,`.45`,`.46`,`.49`,`.58` (shard 1); `.78` (shard 2) | Supersede/rider ten shard-1 units and one shard-2 unit by name |
| `.176` (supplier-movement record) | `.15` (shard 1 conditionality), `.91`, `.136` row 6/7 | Discharges owed disclosures; moves conditionality at n ≥ 8 |
| `.201`–`.206` (2026-08-12 corrections) | `.37`, `.57`(=`.140`), `.63`(=`.163`) | (CS-1) → (CS-1Q) upgrade, three consumer-sweep sites |
| `.152` R1.4 | `.78` (GENIND-BOX-4's pricing sentence) | Split: STANDS for per-genre prefactor ledgers; hypothesis-wiring gap CURED |
| `.170` R6.1 | `.146` (the PE8 acceptance report) | Notice against a **verifier's own artifact**, not against the note |
| `.153` R1.3 | `.44`, `.46`, `.57`(=`.140`) | GENIND.C′ installed verbatim in place of the bare vanishing bullet |
| `.156`–`.158` R2 | `.36`(=GENIND-6(c)), `.24`(=step (3)'s fiber sentence) | Unit-pivot license, two named sites |
| `.160`–`.161` R3 | `.07`,`.21`,`.24`,`.34`,`.38`,`.45` | Window-1 convention, six consumption sites |
| `.163`–`.164` R4 | `.11`, `.49` | CS4-F visibility floor at both displays |
| `.157` R5 | `.11` | Converse pinned to DEGREE level (not stage level) |
| `.169`–`.170` R6 | `.14`, `.58`(=`.140`) | Identity-vs-bound separation |
| `.174`–`.176` (GENHN screen) | `.34`, `.57`(=`.140`) | Seven-site GENHN inventory, screened |
| `.85` (HEX3-BOX-1, ledger HYP.137) | HEX3's own W-12.B corroboration aside ONLY | Never GENIND's induction, never `hExhaust3` |
| `.146`'s "GENIND-BOX-5's close" | `.79` | Confirmed home-shard self-reference (the adjacency-rule fix, §1 above) |
| `.146`'s "GENIND-BOX-3's STALE-SELF-DESCRIPTION" | `.77` | Confirmed home-shard self-reference (the adjacency-rule fix, §1 above) |
| shard 3 OPEN-CALL 1's cross-citation | shard 2 OPEN-CALL 2 (**as written — WRONG**) | The genuine twin is **shard 1's OPEN-CALL 2**; recorded as a defect, not silently repointed (§8) |
| `.94`(§S9.3 close) | `.75` (GENIND-BOX-1) | "THEOREM GENIND.B is a REDUCTION" — the note's single most important honesty fence, repeated |
| `.72`(OB-c) | `.65`(CS-3) | Explicit identity — the note treats them as the same open theorem in different words |
| `.08`,`.17`(i) | (same content, two granularities) | Both emitted, forward-summary vs. lemma; not deduplicated |
| `.14` | `.66` | Same clause, two displays, disjoint rider sets; not deduplicated |
| `.19`(HYP.121) | `.24`,`.25`,`.35`,`.106` (fracture-permanence consumers) | External interface obligation, unaudited generality; OPEN-CALL |
| `.30`(GENIND-0) | `.128`,`.129`(Steps 1–2's menu multiplication) | Closure stated for pre-r4 (A1); OPEN-CALL |
| `.104`(§S11 consequence) | `.146`(PE8-m1 cure) | **NOT** reached by the cure — two stale clauses remain uncured; OPEN-CALL |

### 7.4 Format feedback consolidated (v3 rules under load; three shards' §6.3 items,
deduplicated where the same recommendation was made independently by two or more shards)

1. **Rule 28 (SERIES) is what makes shard 2 compilable at all**, and this merge's §7.1
   confirms all three series reconstruct across shard lines without loss. **Recommendation
   (both shard 2 and shard 3 make it independently): allow a series to live inside a unit
   (GENH4-PIN) as well as across units**, with series id + entry index + terminal marker
   as three separate fields.
2. **Rule 25 (CHAIN + TERMINAL) needed a multi-terminal extension in BOTH directions this
   note exercises** — a chain with one terminal per CONSUMER CLASS (the CS-drain rate and
   the (CS-1) hypothesis, §7.2) and a chain with a terminal per PROOF LAYER. **Both shard 1
   and shard 3 recommend the same fix independently**: a CHAIN may carry more than one
   TERMINAL, each labelled with what it terminates for.
3. **Rule 22 (arithmetic audit) earned its extension beyond `[TABLE]`s conclusively.**
   GENIND has almost no source tables (one Markdown table in 3872 lines) yet 21+12+12 = 45
   units across the three shards carry compiler-computed arithmetic audits, and this
   exercise **re-derived, independently, every displayed step of the corpus's most
   checkable unit** (`.152`'s full R1.1 telescope-to-rate derivation) and found it exact
   throughout.
4. **Rule 27's AUDIT class is confirmed as the right home for this note's heaviest
   findings, on independent evidence from all three shards**: the (A2-RATE) gap, the
   unit-pivot gap, the five-finding RECORD-INTEGRITY chain, and the Codex ratification's
   three CONFIRMED GAPs were ALL produced by fresh-context reads and could not have been
   produced by any battery row (§6's combined zero-orphan statement makes this exhaustive
   across the whole corpus, not just per-shard).
5. **This merge's own contribution to the format record**: the per-field (not per-unit)
   context-reset rule for the SHARD-MAP rewrite (§1 above), forced by GENIND's heavy use of
   short parenthetical cross-shard asides ("(shard 3)") inside long multi-item
   CONDITIONALITY fields — a corpus feature EFF-HE7's shards did not exercise as heavily,
   which is presumably why its own stated rule did not need this refinement.
6. **The consumer-sweep format question (OPEN-CALL, below) is the one substantive
   cross-shard disagreement this merge could not resolve by fiat**: fourteen imperative
   bullets across shard 3's L4 reach into frozen text in shards 1–2 without quoting it, and
   both shard 1 and shard 3 raise the identical open question (whether a sweep installs a
   supersession edge or is only a reading note) without a template ruling to appeal to.

---

## 8. Self-audit and OPEN-CALLS (merged, dedup marked)

**14 raw open calls across the three shards (5 + 4 + 5) reduce to 11 distinct issues — 3
dedup pairs, each a genuine same-substance duplicate raised independently (or, in one
case, cross-cited with an error) from two shards' perspectives.**

### OPEN-CALL 1 — `.19`'s all-`O` generality is an external obligation with no note-side sentence

Ledger row **HYP.121** (`spec/HYPOTHESIS_LEDGER.md:970–974`) states GENIND-1 is "valid
over arbitrary complete DVRs… CLASS: interface-generality… PROPOSED DISPOSITION: CARRY."
The Q1 audit is sharper: "INTERFACE — load-bearing, unaudited… Its generality cannot be
certified here." **`.19` contains no sentence asserting or denying all-`O` generality
specifically** — only the blanket S1 convention (`.07`) and GENIND-BOX-3's d ≥ 2
disclosure (`.77`). **Decision needed: whether the merged spec carries HYP.121 as a
conditionality on `.19` (and hence on every consumer of fracture permanence: `.24`, `.25`,
`.35`, `.106`), or leaves it as a ledger-side obligation.** (Shard 1 only.)

### OPEN-CALL 2 — the consumer-sweep format has no ruling, and it is GENIND's dominant late-stage supersession vehicle **[DEDUP — shard 1 OPEN-CALL 2 + shard 3 OPEN-CALL 1]**

Fourteen imperative bullets across `.200`, `.203`, `.205` ("In X, replace Y by Z", "Delete
W from V") reach into text in all three shards — including the byte-frozen body
(`.57`/GENIND.B Step 4; `.37`/GENIND-6(d)) — **without quoting the target sentences**; two
are unusually strong (`.163` withdraws a bound; `.203` deletes a clause that remains
byte-intact in the source). This compilation resolved all fourteen to unit IDs by hand and
recorded them as `TARGETS` fields (§7.3's edge list). **Decision needed: whether the
merged spec treats a consumer-sweep bullet as a first-class supersession (installing the
edge) or as a downstream reading note, and whether the format should require sweeps to
quote their targets.** **Recorded merge-time defect (not silently corrected): shard 3's own
OPEN-CALL 1 cites this as "raised identically at shard 2 OPEN-CALL 2" — but shard 2's
OPEN-CALL 2 is the DIFFERENT `.73`-predictions issue (below). The genuine identical twin
is shard 1's OPEN-CALL 2**, which states the same title and the same substance
("`(CS-1Q)` upgrade's reach into the frozen body is not stated by any sentence… will recur
in shard 3 and in GENH4") verbatim in spirit. This mis-citation is itself evidence for
rule 23's extension to cross-shard citations, not only to commit hashes.

### OPEN-CALL 3 — LEMMA GENIND-0's closure is stated for the PRE-r4 (A1) **[DEDUP — shard 1 OPEN-CALL 3 + shard 2 OPEN-CALL 1, cross-cited correctly by both]**

`.30` proves (A1)-admissibility closed under finite products, unions and affine
re-parameterizations. W-12's r4 round added a σ-LABELING clause INSIDE (A1) (§S16 row 1,
`.138`: "The r4 σ-LABELING clause STRENGTHENS (A1)"), and consumption of W-12.D is
recorded as surviving because a strengthened hypothesis demands more and delivers no
less. **No unit re-derives `.30`'s closure under the strengthened predicate**, and Steps 1
(`.128`) and 2 (`.129`) both use GENIND-0 to multiply menus that must now carry σ-labels.
**Not a claimed error** — the strengthening may be trivially preserved by a coordinatewise
argument, but a formalization blueprint cannot assume it. **Decision needed at 0b/chapter
time: whether GENIND-0's closure must be re-derived under the r4 (A1) before
formalization.**

### OPEN-CALL 4 — `.73`'s preregistered predictions have no recorded outcome anywhere in the note **[DEDUP — shard 1 OPEN-CALL 4 + shard 2 OPEN-CALL 2, same substance, neither shard cross-cites the other]**

`.73` states two falsifiable predictions with a stated falsification consequence and hands
them to QSCOUT22's GENRE-E table; `.82` item 1 states the upgrade rule ("a confirmed table
upgrades GENIND-5 from candidate to corroborated-candidate"). §S9.3's `[r6]` re-pin
(`.90`) records that the scout's arc completed (VERDICT `dd67cda`, GREEN 7,614,473/0) with
an L3-correction annex (`fcaf268`) for "the genre-E UND display's h = 1 slip". **No
sentence anywhere in GENIND's 3872 lines records whether the predictions were scored,
against which version of the display, or with what result.** **Decision needed: whether
the merged spec must carry a "preregistration with no run-record" row, and whether GENIND
owes a dated append recording the outcome.**

### OPEN-CALL 5 — `.51`'s CS5-V4E2 law is derivation-only and its exponent has no independent check

`.51`'s law `(q−1)²·q^{5N−5v₄−5h−4}` is displayed once, never machine-exercised (first
visible at N = 8, beyond every roster) and has no second derivation or cross-check against
any other displayed number, unlike its neighbours `.48`–`.50`. **Decision needed: whether a
derivation-only law with no arithmetic cross-check may enter a chapter cut as a displayed
law, or must be re-derived first.** (Shard 1 only.)

### OPEN-CALL 6 — the PE8-m1 cure does not reach §S11's stale status clauses

`.146` supersedes exactly two frozen arc lines by name. §S11's closing paragraph (`.104`)
is neither: "Attempt 0/2; the hostile arc has not begun" sits in the frozen body, is not a
per-round grade close, and is not named by the cure — yet it is false at acceptance by two
passes and a grade; its neighbouring clause ("conditional exactly on…[GENIND-H] per genre
plus the supplier arc grades") is likewise overtaken at n ≥ 8. **Decision needed: whether
the merged spec tags `.104` STALE-SELF-DESCRIPTION (this compilation's choice, recorded
already at `.104`), or whether GENIND owes a dated append extending the PE8-m1 cure to
§S11's consequence paragraph.** (Shard 2 only.)

### OPEN-CALL 7 — `.127`'s "all eight md5 pins" does not reconcile, and the r5 sweep adjudicated it compliant

The §S14 close asserts "all eight md5 pins re-verified at commit time, listed in the Arc
paragraph"; the Arc paragraph enumerates **ten**. §S15's universal-sentence sweep (`.133`)
adjudicated this sentence **KEPT** as rule-compliant, on the ground that its quantifier
ranges over an enumerated set — **without recounting the numeral.** The later freeze
lines (`.134`'s 13, `.142`'s 16) both reconcile exactly, so the defect is local.
**Decision needed: whether a numeral that disagrees with its own enumeration is a record
defect the standing rule should catch — it is exactly the class the rule was written for,
and the rule's own sweep passed it.** (Shard 2 only.)

### OPEN-CALL 8 — the Q-normalized lemma and the entire R11 layer are unexercised, and the one machine leg is pinned to a superseded statement

The r1 leg (`.183`, `.185`) was preregistered and run against `.180` (=R9's C2), which R9
then replaced in full (`.189`) and R11 replaced three named parts of (`.197`–`.204`). **No
machine leg was added at either R9 or R11.** The Q-normalization (R9's entire point, the
only part that bites at d ≥ 2) is untested; C2Q, C2D, the lexicographic descent, and the
actual-side-length pricing are proved and unexercised; the r1 leg's GREEN attaches to a
statement no longer in force. This compilation re-derived every step of R9's and R11's
mathematics by hand and all of it checks (§6.3's arithmetic-recount row), but **hand-
checking is not an instrument. Decision needed: whether the merged spec requires a machine
leg for the R11 layer before it enters a chapter cut, and whether `.185`'s GREEN may be
cited at all in support of `.189`/`.197`.** (Shard 3 only.)

### OPEN-CALL 9 — `.185`'s flagged-line adjudication is supported by two figures that do not agree

The one non-GREEN check in the r1 leg (P3, genre F, N 7→8) is adjudicated "an INSTRUMENT
CAP LITERAL, not a counter-instance" on three supports, two of which — a per-step slope of
2.00 and a per-stratum law slope of 3.00 — **do not agree**, and the note does not
reconcile them. The load-bearing fact is undisturbed (no BOUND check fails at any of the 12
rows). **Decision needed: whether the merged spec carries the adjudication as settled, or
flags the discrepancy as an owed reconciliation.** (Shard 3 only.)

### OPEN-CALL 10 — the annex stack's grade may be stale against the repo

`.186` closes "The annex stack remains 0/2." A second report,
`GENIND_ANNEXR_pass2_report.md`, EXISTS on disk and is cited nowhere in the note (the note
is frozen at 2026-08-12 and cannot know its own successor). **Decision needed: whether the
merged spec reads the annex-stack grade from the note (0/2) or from the repo (pass #2's
unread verdict), and whether GENIND owes a dated append recording it.** This compilation
does not adjudicate it and has not read pass #2. (Shard 3 only.)

### OPEN-CALL 11 — "Ledger: row 17" names a ledger this compilation cannot resolve

`.195` and `.206` both close with "Ledger: row 17 → …". **Row 17 is not a row of
`spec/HYPOTHESIS_LEDGER.md`** (whose rows are `HYP.nn`); it is a row of the certification
campaign's own ledger, and the note never names that file. **Decision needed: whether the
merged spec must resolve "row 17" to a named file+row before the CS-drain material enters
a chapter cut.** (Shard 3 only.)

### Recorded source defects (flagged, not silently repaired; 13 raw across shards 1 and 3 — shard 2 folds its defects into its NEAR-MISS and OPEN-CALL entries above rather than a separate list — one retracted on re-derivation, 12 standing)

1. **`.77`: the battery family `GT-AGGDEEP` does not exist** — the referent is evidently
   `GT-BRACKETID`; carried descriptively, not emitted as a battery row. (Shard 1.)
2. **`.27`/`.28`: genre-locus counts are displayed in the same register as state-space
   counts** — internally consistent everywhere checked, but a reading hazard at scale.
   (Shard 1.)
3. **`.39`/`.40`: the T1 tooth's (2,5) joint count is not displayed** — a display gap, no
   inconsistency where both figures are given. (Shard 1.)
4. **`.40`: the headline check total 2,128,163 cannot be reconstructed from the displayed
   rows** (2,126,803 + an un-itemized 1,360 residual) — a disclosed non-reconstruction, not
   a discrepancy; the frozen artifact is the authority. (Shard 1.)
5. **`.164`: `GENH4 S6.2` is a section pointer into a note that carries no such section
   number** (fixed-string count 0 in `GENH4_PROOF`; the count 6 belongs to GENHN's file).
   (Shard 1.)
6. **`.15`: `[GENHN-HE(μ ≥ 3)]` names no box in GENHN** — the note discloses this itself at
   PE7-m3; carried with the note's own correction (§4's triple-dedup NEAR-MISS). (Shard 1.)
7. **`.106`'s honest-limit sentence is STALE as of r6** — "the same-side f-first genre…
   remains machine-unrealized corpus-wide" was falsified by PE6's realization without the
   sentence being edited. Tagged `STALE-SELF-DESCRIPTION`, not `superseded`. (Shard 1.)
8. *(Withdrawn on recount.)* An earlier pass of shard 3's own compilation flagged `.150`'s
   telescope sketch as non-reconstructible; on careful re-derivation **it IS
   reconstructible** and the full derivation is now recorded at `.150`'s arithmetic audit.
   No defect; recorded for the audit trail. (Shard 3.)
9. **`.180`(=defect 2, shard 3): three of the five ANNEX R annex commits are cited only
   inside the note's own enumeration** — `31c6723d`, `98ac7bb0`, `fe0ed6c0` are 8-hex
   prefixes appearing nowhere else; the other two resolve independently. Recorded as an
   unverified-pin subset, not an error. (Shard 3.)
10. **A second annex-stack pass report exists and is uncited** — OPEN-CALL 10. (Shard 3.)
11. **`.185`: the flagged line's adjudication carries two unreconciled slope figures** —
    OPEN-CALL 9. (Shard 3.)
12. **`.195`/`.206`: "row 17" names an unspecified ledger** — OPEN-CALL 11. (Shard 3.)
13. **`.183`: a one-word transcription slip in shard 3's own quotation was caught and
    corrected in place** (compiler defect, not a source defect; recorded for
    completeness). (Shard 3.)

### Fidelity audit (merged)

- Every CANONICAL STATEMENT across all 206 units is a verbatim source quotation or is
  explicitly marked `[ASSEMBLED]`. **No inverse, sign, quantifier, index, degree, slope,
  window, inequality direction, implication direction, exponent, base (q versus Q), tag
  label, or constant was altered anywhere** — the union of all three shards' own
  fidelity-audit claims, none contradicted by this merge's own spot-checks (§4's 12 XREF
  + 6 quote re-verifications, zero drift).
- Truncations inside quotations: one (shard 1, `.58`, marked `…`); none in shards 2–3
  beyond the corrected one-word slip (defect 13).
- Nested `[rN]` brackets are reproduced in place with their quoted false originals intact
  throughout; nothing quoted as "FALSE" is presented as live text anywhere in the 206
  units.
- **71 distinct XREF designations, every one grep-verified with a fixed-string count ≥ 1**
  (§4), re-sampled fresh at 12/12 zero-drift; **128 commit-pin checks, 128/128 resolve**;
  **66 artifact/report-existence checks, 66/66 present**; 12 distinct NEAR-MISS
  dispositions carried, none suppressed and none invented.
- **45+ units across the three shards carry compiler-computed arithmetic audits**,
  independently re-derived rather than assumed from source labels; §7.4 item 3 records
  this merge's own full re-derivation of the corpus's single most checkable unit (`.152`).
- Status and mathematical content are kept as distinct predicates throughout (header §1's
  three-predicate split); no consumption append is claimed landed on any supplier, and
  none is invented anywhere in the merged inventory.
- **Honest limitation of this merge:** the 206-unit statement inventory (§3) was rewritten
  by a verified, audited script (zero out-of-range IDs, zero leftover shard-local
  substrings, two confirmed context-tracking bugs found and fixed before acceptance); the
  aggregation sections (§§1, 2, 5–8) were composed by direct reading of all three shards'
  own front matter, consumption tables, teeth tables, boundary self-audits, shard notes,
  and self-audits **in full**, but are hand-synthesized prose and inherit whatever residual
  imprecision that entails at this scale (206 statements, ~1,150 citation sites) — flagged
  here rather than presented as equally mechanical. **CODEX CROSS-READ OWED**, per the
  header stamp: neither this merge nor any of the three shards has been through an
  adversarial pass.

EFF-GENIND MERGED: 206 statements / 71 xrefs / 11 open calls.
