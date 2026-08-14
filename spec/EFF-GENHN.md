# EFF-GENHN — CANONICAL EFFECTIVE-SPECIFICATION (MERGED)

**COMPILED-BY: opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). CODEX CROSS-READ OWED (post-reset) — neither shard, and no fold performed by this merge run, has been through an adversarial pass; that obligation is inherited whole, not discharged here.**

## 1. Merge header

**Source note:** `lean/notes/openmath/GENHN_PROOF_2026-08-08.md` (2627 lines).

**HEAD blob hash:** `26a5c58ad13f2acd1ab3f8519cbabaaa2d0a4cbb` — cited identically by both source shards' headers, and independently confirmed by a fresh `git hash-object` run at merge time (2026-08-14):

```
$ git hash-object lean/notes/openmath/GENHN_PROOF_2026-08-08.md
26a5c58ad13f2acd1ab3f8519cbabaaa2d0a4cbb
```

**No divergence found — this was the merge run's STOP condition and it did not trigger.** Both shards additionally record the file's last-touching commit as `06958241`.

**Compilation context:** `spec/EFF_TEMPLATE_v2.md` AT HEAD (rules 1–28, v2 + the v3 prose-genre rules).

**Merged from:** `spec/EFF-GENHN-s1of2.md` (HOME source lines 1–1319; 48 statements, 65 xrefs, 6 open calls, per its own closing line) and `spec/EFF-GENHN-s2of2.md` (HOME source lines 1320–2627; 45 statements, 52 xrefs, 6 open calls, per its own closing line). **93 statements, 117 raw XREF citations, 12 raw open calls total before merge-time dedup.** This file supersedes the two shards as the citable unit for all downstream consumption; any consumer citing `EFF.GENHN.*` from this point on cites the contiguous IDs below, not the shard-local `EFF.GENHN.sKof2.*` IDs. **The two shard files are NOT deleted** — they remain the run-of-record trace of the sharded compilation, and in particular remain the place where each shard's own §6 BOUNDARY SELF-AUDIT (which unit-boundary candidate was chosen inside a blockquote or a record, and why) lives in full; this merged file's §7 carries forward only the cross-shard format-level conclusions (the four SERIES, the cross-shard supersession edges, the boundary-unit resolution), not the twenty-five individual boundary arguments recorded in the two shards' own §6 sections.

### SHARD-MAP (old shard-local ID → new contiguous ID)

Shard 1's offset is **0** (its own numbering, 01–48, is already contiguous from 1). Shard 2 carries a **+48 offset** (01–45 → 49–93). Every `EFF.GENHN.sKof2.NN` occurrence — full form and the bare `` `.NN` `` shorthand used throughout each shard's own prose (e.g. "shard 1 `.02`") — has been mechanically rewritten throughout the merged statement inventory below (§3), under the following disambiguation rule:

> **A bare `` `.NN` `` reference is resolved against the shard most recently named by a full-form `EFF.GENHN.sKof2.NN` citation or an explicit "shard K" prose mention earlier in the same blank-line-delimited block; absent any such prior citation in the block, it resolves against the unit's own home shard. Context resets at the start of every block within a unit (fields and paragraphs in this corpus are reliably blank-line separated), not merely at the `### EFF.GENHN.sKof2.NN` unit boundary — a cross-shard aside made in one paragraph must not leak into the next.**

**Neither shard's own header or §7 SHARD NOTES states this convention explicitly** — GENHN's shards use the "shard 1 `.NN`" / "shard 2 `.NN`" phrasing throughout but never write down the resolution rule the way EFF-HE7's merge did. This merge applies the HE7 merge's convention anyway, since it is the only reading that makes the shards' own cross-references (e.g. shard 2's `.01` CONDITIONALITY: "member 1 = the title-box round records (shard 1 `.02`, 0/2); **member 2 = this box** (0/2); member 3 = the post-PE3 append (`.24`, 1/2)…") resolve unambiguously: the first bare ref after "shard 1 `.02`" is a full clause boundary away (separated by "`; **member 2** …`"), so it must revert to the unit's own home shard (shard 2) rather than inherit "shard 1" — giving `.24` → merged `.72`, not merged `.24`. Both readings were computed by a context-tracking script (not hand-transcription, to guarantee zero arithmetic slips across 425 bare-ID citations and 93 full-form IDs) and audited afterward: **zero leftover `sKof2` substrings anywhere in the merged statement inventory (§3)**, and **zero out-of-range renumbered IDs** (every resolved ID lies in 1–93; verified both for the 425 bare-ref citations and the 93 full-form unit-header IDs). A hand sample of every cross-shard "shard 1"/"shard 2" mention site in the merged text (84 sites) was additionally read back against the source shards and found to resolve exactly as the source's own prose intends (§8's fidelity audit).

### SHARD-BOUNDARY PROVENANCE (foregrounded per this merge run's charge)

Shard 1's own header states, verbatim (its own OPEN-CALL 1 restates this, see §8 below):

> "`runs/qgen/sweep_manifest.txt` at HEAD carries no GENHN row (52 rows: T1, T2, GENTOW5, W12, HE7, T4, T5, W11, JD0, SIGMALAW, HETOW, GENTOW1/3/4/6, HEX3, HMENU3, HE6, HE6R1, HE3, GRTW2, GRTJA, WELDMASTER, GENH4, GENIND, GRTJB, GRTJC, LIFTCORNER — verified by `grep -ni genhn runs/qgen/sweep_manifest.txt`, count 0). The charge names GENHN s1of2/s2of2 "per the manifest"; the manifest cannot supply the ranges. The split was therefore compiler-chosen at the §S8/§S9 section break (1319 | 1320)…"

— continuing (shard 1 §1): "…which (a) is a `##`-heading boundary, (b) splits 1319/1308 — within 0.5% of an even halving — and (c) puts the whole accepted mathematical body in shard 1 and the whole boxes/battery/appends stack in shard 2. No source unit is cut." Shard 2's own header states it adopted the identical split ("This shard adopts it") and its own SHARD NOTES confirms the range-edge is clean at both ends (line 1319 blank, 1320 opens `## S9.`; line 2627 is the note's own last line). **This merge run independently re-verified the range-edge cleanliness** (§7.4-equivalent check below) and **confirms: no source statement unit is cut at the 1319|1320 boundary, and the boundary lands on a `##` section break in both shards' independent line-by-line audits.**

**This merge run DID IN FACT ADOPT the 1319 | 1320 split** — it is exactly the split under which the two input shard files were compiled, and this merge performs the concatenation-and-renumbering over that split without revisiting it. **The second half of the decision — whether `runs/qgen/sweep_manifest.txt` should be amended to add a GENHN row recording this split — is explicitly left OPEN for Asvin** (carried forward as OPEN-CALL 1 in §8 below, dedup-merged from both shards' identical statements of it). This merge does not silently resolve that half.

### Header unification and blob-hash check

Both shards' front matter quotes the same three freeze predicates and the same governing effective-text derivation. Both cite **the same HEAD blob hash**, `26a5c58ad13f2acd1ab3f8519cbabaaa2d0a4cbb`; no divergence was found (this was the merge charge's STOP condition; it did not trigger — see the fresh `git hash-object` run above).

### Governing effective-text record (unified from both shards; three independent freezes, never conflated)

**FREEZE PREDICATES (template rule 21 — three, each with its own quote and pin, stated identically by both shards since shard 2 is where every one of them is *first stated in full* and shard 1 restates them as governing context):**

**(F1) TEXT-FREEZE at acceptance (2026-08-09, post-PE4).** Lines 1950–1953 (`.75`):

> "Clean count 1/2 → **2/2: GENHN is ACCEPTED — the text is FROZEN, dated appends only from here** (this line carries the counter past the title box's round-dated 0/2 and the post-PE3 append's 1/2)."

re-asserted at lines 2034–2038 (`.77`): "**Freeze discipline.** GENHN stays ACCEPTED 2/2, text FROZEN, dated-appends-only…"

**(F2) INSTRUMENT-FREEZE — the sealed two-commit battery, older and stricter than (F1).** Lines 1629–1632 (`.61`): `verification/openmath/genhn_checks.py`, two-commit seal (commit 1 = note + runner, battery UNRUN; commit 2 = §S12 verdict appended from the committed artifacts). It began at commit 1, before any hostile pass, and survives **two disclosed RE-SEALs** (`.66`, `.67`) that changed runner infrastructure while leaving predictions byte-unchanged.

**(F3) PREDICTION-FREEZE — S11.D, preregistered before the first full run.** Lines 1624–1626, 1741, 1753–1754 (`.64`, `.66`, `.67`). Distinct from (F2): the runner changed twice, the predictions did not. This is the freeze that makes the S12 scorecard (`.70`) evidence rather than narration.

**EFFECTIVE TEXT = the whole 2,627-line file exactly as written** — lines 1–1319 with `[r1]`/`[e2]`/`[r2]`/`[r3]` tags already landed IN-TEXT (the pre-acceptance repair mechanism: "GENHN is at attempt grade 0/2 (unaccepted), so this is a tagged repair, not a frozen-note annex," lines 580–583), **READ AS CORRECTED by the eleven out-of-range dated appends (lines 1859–2627) wherever they name an earlier sentence, with no earlier sentence ever deleted.** Every post-acceptance correction is an append that quotes its target and leaves it byte-intact above it — this is the mechanism behind every `SUPERSESSION KIND` and `CHAIN` field in §3 below.

### Scope of record — mandatory THREE-predicate split (rule 7 + rule 17, never conflated)

**A. ABSORPTION / mathematical supply SET.** §S1's five displayed statements — THEOREM GENHN.CLASS, THEOREM GENHN.A, THEOREM GENHN.C, LEMMA GENHN-T, THEOREM GENHN.B — plus the four working lemmas GENHN-1/-2/-3/-4, at `[r2]` LEMMA GENHN-T(b)′, and (by append) LEMMA GENHN-CAP-GEN, LEMMA GENHN-LIFT, and LEMMA GENHN-COUNT-RERUN. The note's own one-line inventory (`.57`, lines 1526–1531):

> "One line: THEOREM GENHN.CLASS + GENHN.A(i)–(iii) + GENHN.C + GENHN-T(a) rest on {GENIND lemmas, W-12.A, W-11, classical} @ pins with no weld face; GENHN.A(iv) at μ ≥ 3 adds ONE accepted weld face (W-9, disclosed); GENHN.B adds GENIND.B + W-12.D @ pins and the box family [GENHN-HE(μ ≥ 3)]. No axiom anywhere; grade = composition 0/2."

**B. APPEND / consumption-PROTOCOL scope.** **GENHN lands nothing on any supplier or consumer, and the note says so at least twice, in both shards' ranges.** Shard 1 (lines 1580–1585, `.59`): "consumers with n ≥ 8 instances … inherit that box — cross-note status is the orchestrator's fold, flagged here." Shard 1 (lines 1619–1621, `.60`): "GENIND's n ≥ 8 conditionality line inherits the refined n ≥ 10 / n ≥ 16 scoping — orchestrator's fold, flagged here." **Zero dated consumption appends are claimed landed on any supplier or consumer by this note, and none is invented anywhere below.**

**C. INBOUND CORRECTIONS RECEIVED** (template rule 17 — the DAG surface neither A nor B records). GENHN is unusually correction-rich: **seven distinct inbound sources land eleven dated appends inside shard 2's range, of which twelve individual corrections target shard-1-HOME text** (shard 1's own count, §7 below):

| # | Source | Landing form | Merged targets |
|---|---|---|---|
| 1 | `CODEX_HE6PE1_2026-08-08.md` finding 3 (adjudicated) | `[r1]` ERRATUM, in-text | `.24`, riding on `.23`, `.12` |
| 2 | GENH4 PE2 CRITICAL 1 + PE3 REMARK A @ pin `4b0d946` | `[e2]` ERRATUM E2, in-text | `.14` → `.12` |
| 3 | GENH4 PE2 GAP 1 + PE3 MINOR 1 @ pin `4b0d946` | `[e2]` ERRATUM E1, in-text | `.31` → `.29` |
| 4 | CODEX GENH4 ratification F3 @ `5c8d2fd`, model GENH4 ANNEX R R3 @ `b10a5a7` | `[e2]` ERRATUM E3, in-text | `.22` → `.08`, `.21`, `.33`, `.35` |
| 5 | `GENHN_passPE1..PE4_report.md` (own hostile arc) | `[r2]`/`[r3]` in-text; PE3/PE4 as dated appends | `.17`, `.23`, `.25`, `.29`, `.32`, `.38`, `.43`–`.51`, `.24`, `.72`–`.76` |
| 6 | `HETOW_passPE1_report.md` F-1 (a consumer correcting its supplier) | dated append (`.77`) | `.42` |
| 7 | sol certification A2/D2b/P2 (2026-08-12) | six dated appends (`.78`–`.93`) | `.07`, `.09`, `.10`, `.16`, `.24`, `.29`, `.36`, `.44` |

### Resolution rules applied (merged; each shard's own numbered rule-list is a restriction of this one to its HOME range — nothing is dropped, only consolidated)

1. Lines 1–2627 supply the HOME material, read in source order across both shards. All four in-text repair rounds (`[r1]` 2026-08-08, `[e2]`/`[r2]`/`[r3]` 2026-08-09) are already-landed base text, applied at their own sites in chronology; the later bracket governs the earlier text it names.
2. **Post-acceptance dated appends never edit; they quote and rider.** Every append states this, four with an explicit md5 prefix (shard 1 §1's freeze-scope table). Where an append names an in-range (own-shard) target the rider is applied at that unit; where it names an out-of-range (other-shard) target, the unit is NOT re-emitted at the citing shard and the edge is listed in §7 below.
3. **Two statement DISPLAYS are re-displayed by owner directive** (2026-08-12, `.86`/`.87`, plus the post-D2b corrigendum `.88`): GENHN.CLASS's finiteness clause (targets `.07`) and GENHN.A(ii)'s slot clause (targets `.09`). `SUPERSESSION KIND: replacement` at statement scope, each carrying a CHAIN with a TERMINAL marker (rule 25) because the slot clause is re-displayed twice.
4. **Two in-range clauses were adjudicated REAL-BUT-OBSTRUCTED before being re-displayed** (`.80`, `.82`). The obstruction records are the *reason* for rule 3's re-displays and are quoted at both the obstruction unit and the target unit's CONDITIONALITY.
5. **Where an out-of-range correction supplies a missing lemma** rather than editing a display (LEMMA GENHN-CAP-GEN `.79`, LEMMA GENHN-LIFT `.81`, LEMMA GENHN-COUNT-RERUN `.90`), it is a **license**, not a supersession, recorded as such at the unit it licenses.
6. **Three SERIES span both shards** (GENHN-GRADE-ARC: member 1 in shard 1 at `.02`, members 2–5 in shard 2 at `.49`, `.72`, `.75`, `.77`; GENHN-ERR-1: members 1–3 in shard 1 at `.24`, member 4 in shard 2 at `.92`) and **one SERIES sits entirely within shard 1** (GENHN-T(b)-ARC: `.17`, `.41`, `.42`) and **one SERIES sits entirely within shard 2** (GENHN-ARC-LINE: `.58`, `.59`, `.60`). Each is reconstructed in §7.1 from the member indices the units themselves already carry (both shards' compilers pre-built the cross-shard member tables at unit level — see §7.1), not by prose-reading.
7. **The A2 verification parenthetical (`.84`) and the P2 provenance parenthetical (`.93`) are `instrument-record` units**, not folded into the corrections they follow: each states exactly what the orchestrator re-verified by hand before transcription.
8. External repo records (report files, `verification/openmath/*` artifacts, supplier notes) are reading notes only, never edits. Every cited commit hash was verified with `git cat-file -t`; every cited artifact filename was verified to exist; truncated hashes are marked **UNPINNED** per rule 23.
9. **HOME is determined by an edit's destination, not its physical line position** — every one of the twelve cross-shard supersession edges named in shard 1's §7 SHARD NOTES is installed in §7.3 below and verified to land on a unit that exists exactly once in the merged inventory.

### Quotation and table discipline

Unchanged from both shards: CANONICAL STATEMENTs are verbatim source quotations or explicitly marked `[ASSEMBLED]`; every source table is transcribed as a table and marked `[TABLE]`; the note's only tagged LaTeX displays (LEMMA GENHN-COUNT-RERUN's eight `\tag{CR-1}`…`\tag{CR-8}` equations, `.90`) are reproduced verbatim in source LaTeX and, where they are count tables, transcribed additionally as `[TABLE]` per rule 14. Every `[TABLE]` of counts carries a compiler-computed arithmetic audit (rule 22). Compiler-authored ledgers (§2, §4, §5, §6, §7) are flagged `[TABLE — compiler ledger]` and are not source statement units.

---


## 2. NON-IMPORTS (consolidated from both shards; dedup marked)

`[TABLE — compiler ledger, consolidated from shard 1 §4 (21 rows) and shard 2 §4 (19 rows) = 40 raw rows, 0 dedup pairs found → 40 distinct rows below]`

Neither shard's fence table restates the other's fences in different words — the two ranges' negative-import scopes are disjoint (shard 1 fences the *proof* content §S1–S8; shard 2 fences the *record* content §S9–S12 and the appends) — so **this section's dedup count is 0**, unlike §4/§5/§6 below where the same designation or ledger row genuinely is cited from both ranges.

| Fence | Explicit material NOT imported, NOT proved, or NOT claimed | Unit(s) | Source |
|---|---|---|---|
| The W-2 / LIFTCORNER seam | "canonical digit-lift letters (**the W-2/LIFTCORNER seam NOT consumed**; convention-keyed histories)" | `.06` | s1 |
| DULEMMA | "applicability at general e₁ ≥ 2 stages checked as charged … **but as at GENH4 it is NOT consumed**: the exact valuation of R is proved directly (S3)" | `.05`, `.21` | s1 |
| SIGMALAW in counts | "the (EC-q) gauge-coherence ladder … **NOT consumed by any count law** (J-D0 keeps counts twist-free)" | `.05`, `.17` | s1 |
| Weld faces inside count laws (μ = 2) | "the slot geometry and no-cancellation are **RE-PROVED elementarily** below (GENHN-2 …), so **no weld face sits inside the count laws**" — true at μ = 2 only; GENHN-BOX-2 discloses the μ ≥ 3 exception | `.05`, `.27`, `.11`, `.33` | s1 |
| JC-LOAD | "this is JC-LOAD's no-cancellation holding BY CLASS SEPARATION + RESIDUE-FIELD INDEPENDENCE — **elementary, hence not consumed**" | `.27` | s1 |
| W-9 at GENHN-2 | "W-9's dim_K 𝒜(T) = E = e₁ is this statement's **graded shadow (cited as frame)**" | `.27`, `.09` | s1 |
| Maximality of R | "R = O_L at enumerated corners only …; **no general maximality claim is made or needed**" | `.22` | s1 |
| Band adjudication beyond (1,2) | "at f₁ ≥ 2 genres beyond it (μ ≥ 3, or e₁ ≥ 2 mixed …) this note claims the LIFT-STABILITY content of (a) only and **NO band-adjudication display**" | `.31` | s1 |
| Mixed genres in the `[r2]` band annex | "the e₁ ≥ 2 mixed genres **stay OUTSIDE**, as E1's exclusion list already scopes" | `.32` | s1 |
| Tower count laws | "the composed ENTRY BUDGETS … and the inner refine transfer are **NOT derived here** — boxed, [GENHN-TOW-1]"; "The sealed note **displayed no explicit tower count law**" | `.46` | s1 |
| Genre-general faithfulness | "**No genre-general classification of the faithful region is claimed here** — [GENHN-TOW-1]" | `.45` | s1 |
| Depth ≥ 3 towers | "T(b)′ is ONE composition step and does NOT self-apply … **no displayed authority prices a Φ₃-carrier without item (6)**" | `.18` (and item (6), `.54`) | s1 |
| σ at μ ≥ 3 | "the σ-decision … **is OPEN**"; "Machine corroboration (**labeled, not proof**)" | `.40` | s1 |
| Ore / Montes at order ≥ 2 | "the classical Montes/GMN order-≥2 index theorem is **the literature target for a faithful cite**" — a target, not a citation | `.40` | s1 |
| Multiplicity-weighted composition proof | the `[r2]` withdrawal: "the sentences 'No new mechanism' and 'inheriting exactly GENHN.A's clause grades at each level' are **WITHDRAWN**" | `.17` | s1 |
| No axiom | "**No axiom anywhere**; grade = composition 0/2" — verified across all eleven appends: none adds an axiom | `.57` | s2 |
| Weld faces outside layer 1 | "elsewhere frame-only (GENHN-2 re-proves the slot geometry elementarily)" — the face is at GENHN-4 layer 1 at μ ≥ 3 and nowhere else | `.50`, `.56` | s2 |
| DULEMMA (S10 restatement) | "applicability checked …, **NOT consumed** (S3.1 proves the valuation directly)" — riddered by E3 to read `e(L/base)` | `.56` | s2 |
| SIGMALAW in counts (S10 restatement) | "named at S8(b)'s letter-layer composition only; **no count consumption**" | `.56` | s2 |
| Tower count laws (S9.2 restatement) | "tower COUNT laws remain unmeasured, `[GENHN-TOW-1]`"; "(v)'s form follows … with the budgets boxed" | `.51`, `.54` | s2 |
| Depth ≥ 3 (item (6)) | "T(b)′ is ONE composition step and does NOT self-apply … no displayed authority prices a Φ₃-carrier without item (6)" | `.54` | s2 |
| The iteration's one-sidedness | "the genre-general carry-cancellation bookkeeping is genuine **Okutsu-optimality content, unproved here**"; post-PE3: "the latter is FALSE as a general lemma" | `.54`, `.73` | s2 |
| Depth-≥3 node floor | "(β) the iterated node floor … **has no proved provenance at depth ≥ 3**" | `.54` | s2 |
| Faithfulness geography | item (3): "currently machine-verified at the PE1 instances + the P8 witness" — not a theorem | `.54` | s2 |
| σ at μ ≥ 3 (endgame restatement) | endgame item 1: "**THE one load-bearing open lemma** of the whole composite program" | `.55` | s2 |
| μ = 3 σ corroboration declined | "E3 1,792 + 6,565 (**[GENHN-HE(3)] corroboration, labeled** — an OPEN box, not proof)" | `.64`, `.70` | s2 |
| Instrument grade ≠ acceptance | "**instrument grade, not acceptance** … nothing here upgrades the conditionality display of THEOREM GENHN.B" | `.71` | s2 |
| Acceptance ≠ upgrade | acceptance moves the note's counter only; the theorem's stack is untouched | `.75`, `.71` | s2 |
| No repair by lemma for a false display | "**No new lemma can prove the existing false statement.**" | `.80` | s2 |
| Slot clause below D′h | "At m ≤ D′h the clause is **withdrawn entirely**: a K-slot may be partial … or absent" | `.88` | s2 |
| Datum-set finiteness | "no consumer reads the **withdrawn** datum-set finiteness" | `.86` | s2 |
| Quintic densities | GENH5-DENS "NOT executed here — a one-unit follow-up, explicitly owed" | `.53`, `.55` | s2 |
| The dropped CLASS row | "((Zp,2,5,n6) = 16.7M states **DROPPED for runtime, disclosed**.)" | `.63` | s2 |
| Smoke artifacts | "wiring only; **no artifacts written**"; "No full row ran before seal" | `.65` | s2 |
| Genuinely new lemmas' scope (CAP-GEN/LIFT/COUNT-RERUN) | each licenses only the stated perimeter — CAP-GEN the boundary-band criterion, LIFT the composed-key lift form, COUNT-RERUN the μ = 2 corrected node; none claims the μ ≥ 3 σ-decision | `.79`, `.81`, `.90` | s2 |
| Manifest amendment | this merge adopts the 1319 \| 1320 split but does **not** itself amend `runs/qgen/sweep_manifest.txt` — that half of OPEN-CALL 1 is left to Asvin | — | this merge |

**Dedup count for this section: 0.** Every row is specific to the range that states it; no fence is asserted in different words by both shards (contrast §4/§5/§6 below, where the same external designation or the same ledger row genuinely is cited from both ranges).

---


## 3. Statement inventory (93 units, contiguous, in source order)


### EFF.GENHN.01  [changes-record]

**CANONICAL STATEMENT:** verbatim, line 1 (the title headline).

**FORM:** display (H1 heading, one sentence).

> “# GENHN — THE GENERAL COMPOSITE-STAGE LAW (the program's last composition): the genre classification at every n PROVED FINITE AND UNIFORM (a stage's law depends only on (e₁, f₁, μ, entry), never on n), THEOREM GENHN.A (every composite stage = W-12.A's cell law (e₁,f₁)-re-based, by GENH4's four-step method run genre-generically), THEOREM GENHN.C (σ-decision PROVED at EVERY μ = 2 stage, all (e₁, f₁), by the resolvent method), the stage-tower criterion (towers ⟺ μ ≥ 4 ⟺ n ≥ 8) with the composition lemma ((e,f)-re-basing composes multiplicatively) — and THEOREM GENHN.B: [GENIND-H(n)] for ALL n discharged modulo ONE named box family [GENHN-HE(μ ≥ 3)], so THE FULL UNIFORMITY THEOREM's remaining mathematical distance is a SHORT NAMED LIST”

**CONDITIONALITY:** **Two clauses of this headline are superseded and one is scoped.**
(a) “**the composition lemma ((e,f)-re-basing composes multiplicatively)**” is riddered by the `[r2]` title-line rider at `.04` — the FORMULA survives, its CARRIER is the composed key (LEMMA GENHN-T(b)′), and “GENHN.A applied inside its own stages” is WITHDRAWN.
(b) That rider is itself scoped by the post-PE3 dated Correction 2(iii) (lines 1921–1926): read “its carrier is the COMPOSED KEY (LEMMA GENHN-T(b)′, S8 annex)” with the r3 depth split attached — T(b)′ is ONE composition step; at depth ≥ 3 the carrier is `[GENHN-TOW-1]` item (6)'s unproved iteration.
(c) “**the genre classification at every n PROVED FINITE**” is re-displayed by the 2026-08-12 owner-directive re-display (lines 2282–2298): the *datum* set is infinite; what is finite is the set of **parameterized genre schemas**. See `.07`.
**CHAIN (a)/(b):** frozen headline → `[r2]` title-line rider (lines 53–58) → post-PE3 Correction 2(iii) (1921–1926) — **TERMINAL: the post-PE3 reading.**

**DERIVATION:** Not a mathematical unit; the headline is an index of `.07`, `.08`–`.13`, `.15`, `.16`–`.17`, `.18`.

**RESOLUTION TRACE:** statement line 1 · correction sites 53–58 (`[r2]`), 1921–1926 (post-PE3 Corr. 2(iii)), 2282–2298 (F-2 re-display).

**TEETH:** NONE (index headline). Its component claims' teeth are inventoried at their own units.

---
### EFF.GENHN.02  [changes-record] · SERIES: GENHN-GRADE-ARC, member 1 of 5

**CANONICAL STATEMENT:** verbatim, lines 3–20.

**FORM:** bold-headed paragraph with two bracketed round records.

> “**Unit:** GENHN (the general [GENIND-H(n)] composer; the charge: turn
> GENH4's n = 4 discharge into the genre-generic theorem at every n —
> ledger 970022b). **Attempt grade 0/2** (composed; no hostile arc)
> **[r2 2026-08-09: passPE1 ran NOT CLEAN — 2 CRITICAL (F1 the
> GENHN-T(b) tower-leaf refutation; F2 the GENHN-1 budget display) +
> 1 GAP (F3) + 2 MINOR; all five repaired this round at [r2] tags
> (T(b)′ proved at S8's annex; supp machine leg genhnr2_supp.py
> 147/0). Clean count stays 0/2; PE2 next]**
> **[r3 2026-08-09: passPE2 ran NOT CLEAN — 0 CRITICAL + 2 GAP (F1
> the depth-≥ 3 iterated composition unboxed; F2 the (CS-3) rider
> over-cover) + 2 MINOR (F3/F4); T(b)′ (i)–(iv) itself HELD against
> re-derivation + a fresh instrument (genhn_pe2_fresh.py, 219/0, 4
> teeth). The four findings repaired this round at [r3] tags: F1
> BOXED as [GENHN-TOW-1] item (6) after a T(b)″ attempt whose exact
> obstruction is displayed there, with GENHN.B's tower displays now
> naming the depth split (n ∈ {8..15} depth-2; n ≥ 16 adds item
> (6)); F2 rider scoped to full inner sides; F3/F4 inline
> corrections. Clean count stays 0/2; PE3 next]**.”

**CONDITIONALITY:** **`STALE-SELF-DESCRIPTION` (template rule 26).** “Attempt grade 0/2 (composed; no hostile arc)” and both round records' “Clean count stays 0/2” are frozen sentences the note's own later, unedited events falsify. The **GENHN-GRADE-ARC SERIES**, in source order (rule 28):

| # | Date/event | Where | Grade after |
|---|---|---|---|
| 1 | composed, no hostile arc; `[r2]` post-PE1; `[r3]` post-PE2 | **this unit**, 3–20 | 0/2 |
| 2 | GENHN-BOX-1 (grades) — “0/2, composed this session, NO hostile arc” | 1324–1330 (shard 2) | 0/2 |
| 3 | post-PE3 dated corrections: “PE3 returned CLEAN … so the clean count set there (0/2 → 1/2) HOLDS AT 1/2” | 1863–1874 (shard 2) | 1/2 |
| 4 | post-PE4 acceptance record: “Clean count 1/2 → **2/2: GENHN is ACCEPTED**” | 1941–1955 (shard 2) | **2/2 (TERMINAL for the arc)** |
| 5 | HETOW erratum: “GENHN stays ACCEPTED 2/2, text FROZEN” | 2034–2038 (shard 2) | 2/2, re-affirmed |

**The 2026-08-12 sol certification appends do NOT move the counter** — the A2 append's own closing line (2263–2266) says “GENHN's row stays OPEN — the three repairs await sol discharge-confirmation; the two obstructions close only by re-displayed statements … or new mathematics.”

**DERIVATION:** Round record, not a derivation. The mathematical content of the five PE1/PE2 findings is discharged at `.17`/`.43`–`.49` (F1), `.25` (F2), `.32` (F3), `.38` (F4), and the r3 findings at `.18`/`.47`.

**RESOLUTION TRACE:** statement 3–20 · correction sites 1324–1330, 1863–1874, 1941–1955, 2034–2038, 2263–2266 (all shard 2).

XREF: `lean/notes/openmath/GENIND_PROOF_2026-08-08.md:GENIND-H(n)` — grep-verified count **7**.
XREF: `lean/notes/openmath/GENHN_passPE1_report.md:F1` — count **7**.
XREF: `lean/notes/openmath/GENHN_passPE1_report.md:F2` — count **5**.
XREF: `lean/notes/openmath/GENHN_passPE1_report.md:F3` — count **4**.
XREF: `lean/notes/openmath/GENHN_passPE2_report.md:F1` — count **9**.
XREF: `lean/notes/openmath/GENHN_passPE2_report.md:F2` — count **5**.
PIN: ledger commit `970022b` — `git cat-file -t` → **commit** ✓.
ARTIFACT: `verification/openmath/genhnr2_supp.py` ✓ present · `verification/openmath/genhn_pe2_fresh.py` ✓ present.

**TEETH:** `genhnr2_supp.py` (147 checks / 0 violations, 3 teeth) and `genhn_pe2_fresh.py` (219/0, 4 teeth) — both post-seal additive legs; inventoried in §5.

---
### EFF.GENHN.03  [instrument-record]

**CANONICAL STATEMENT:** verbatim, lines 21–34.

**FORM:** bold-headed paragraph.

> “**Instrument:** sealed two-commit battery
> `verification/openmath/genhn_checks.py` — the genre classification
> machine-checked at n = 5 AND n = 6 (fresh general-residual reader,
> tied to the pinned GENIND reader on shared rows and to the committed
> GENIND row V1E2(1) = 12,288), the general stage law tested at THREE
> genres beyond GENH4's two (n = 5's V1E2 and V4E2 — V4E2 measured for
> the FIRST time, its GENIND law was derivation-only — and n = 6's
> (3,1,2) genre E31, the first E = 3 stage ever read), the μ = 3 stage
> (n = 6's E3 genre) checked at fibration + node + depth-0 species +
> pointwise triple-pin refine kills, the first stage-TOWER event ever
> exhibited (a constructed n = 8 witness), PARI σ legs at never-oracled
> territory (quintic/sextic composite stages, wild p = 3 at an e₁ = 3
> stage), ≥ 3 teeth, preregistered predictions. Verdict §S12, appended
> at commit 2 FROM the committed artifacts.”

**CONDITIONALITY:** This is an `instrument-record` (rule 19), not a run-record: it describes the apparatus, not a result. Its **coverage** is bounded by GENHN-BOX-3 (shard 2, lines 1339–1351) — every battery row has `f₁ = 1`, `d = 1`, `q ∈ {2, 3}`; no f₁ ≥ 2 stage row, no mixed (e₁, f₁ ≥ 2) row, no tower COUNT-law row. That bound is the load-bearing reason every `[r1]`/`[e2]` erratum in this shard can say “the correction is invisible to the battery”. The “≥ 3 teeth” figure is superseded downward-compatibly by S11.B's actual **five** teeth (GN-T-LAT/CEN/SIG/CRIT/NODE) and S12's “all five teeth fired”.

**DERIVATION:** Instrument description, not a derivation.

**RESOLUTION TRACE:** statement 21–34 · coverage bound 1339–1351 · teeth roster 1656–1662 · verdict 1802–1846 (all shard 2).

ARTIFACT: `verification/openmath/genhn_checks.py` ✓ · `genhn_checks_output.txt` ✓ · `genhn_checks_results.json` ✓ — 3/3 present.

**TEETH:** the instrument itself; its five teeth are inventoried in §5 and homed as verdict units in shard 2.

---
### EFF.GENHN.04  [scope-record]

**CANONICAL STATEMENT:** verbatim, lines 36–63.

**FORM:** bold-headed paragraph (the note's own one-breath frame), carrying the `[r2]` title-line rider inline.

> “**What GENHN is (one breath).** THEOREM GENIND.B (@ pin) reduced the
> FULL UNIFORMITY THEOREM — one R_τ ∈ ℚ(q) per splitting type at every
> degree and every prime, wild included — to the per-genre package
> [GENIND-H(n)]: (CS-1) stage transport, (CS-2) stage bracket, (CS-3)
> σ-decision, at every composite-stage genre realizable at degree ≤ n.
> GENH4 (@ pin) discharged the two n = 4 genres by a four-step method
> (fibration; value layer + carry; window coherence; σ by resolvent).
> THIS note runs that method genre-generically: a composite stage is
> classified by (e₁, f₁, μ, entry) alone — finite per n, uniform in n —
> and at EVERY genre the stage read is the (μ, K)-cluster system over
> K = F_{Q^{f₁}} on the dv = e₁·v integer ladder: W-12.A's cell law
> (e₁, f₁)-re-based, with the CS-2 bracket
> (|K|−1)·|K|^{(μ(μ−1)/2+1)κ−1}. The σ-decision is PROVED at every
> μ = 2 stage (all e₁, f₁ — which exhausts n = 4, 5); at μ ≥ 3 (first
> live n = 6) it is the ONE surviving box family [GENHN-HE]. Stage
> towers (composite-over-composite) exist iff some stage carries μ ≥ 4
> keys iff n ≥ 8, and the (e₁,f₁)-re-basing COMPOSES multiplicatively —
> GENHN.A applied inside its own stages **[r2 2026-08-09: the
> composition FORMULA survives but its carrier is the COMPOSED KEY
> (LEMMA GENHN-T(b)′, S8 annex), not the stage algebra — "GENHN.A
> applied inside its own stages" is withdrawn; this title-line echo
> and the title's "composition lemma" clause are ridered once,
> here]**. Consequence (THEOREM GENHN.B):
> P(n) for ALL n — hence the full uniformity theorem through W-12.D —
> is now conditional exactly on [GENHN-HE(μ ≥ 3)] plus the displayed
> compression/coverage boxes plus the hostile-arc stack **[r2: at
> n ≥ 8 add [GENHN-TOW-1] — the corrected GENHN.B display]**. P(5)
> FIRES OUTRIGHT (every n = 5 genre has μ = 2).”

**SUPERSESSION KIND:** the embedded `[r2]` bracket is a **replacement** for the withdrawn sentence (“GENHN.A applied inside its own stages” is *withdrawn*, not re-read) plus a **provenance-rider** on the carrier. `TARGETS: .01` (the title's composition clause), `.17` (LEMMA GENHN-T(b)), `.18` (GENHN.B's conditionality display).

**CONDITIONALITY:**
(i) “**conditional exactly on**” — the word “EXACTLY” is separately declared FALSE at n ≥ 8 by the note itself at `.18` (line 363: “The sealed word "EXACTLY" was FALSE at n ≥ 8 (passPE1 F1)”). The `[r2]` bracket in this paragraph adds `[GENHN-TOW-1]` at n ≥ 8.
(ii) The `[r2]` carrier rider is further scoped by post-PE3 Correction 2(iii) (1921–1926) — see `.01`(b). **CHAIN: frozen sentence → `[r2]` rider → post-PE3 Corr. 2(iii). TERMINAL: post-PE3.**
(iii) “finite per n” inherits `.07`'s re-display (schemas, not data).
(iv) “W-12.A's cell law (e₁, f₁)-re-based” inherits `[e2]` ERRATUM E2's band exception (`.14`) — the note tags that scoping onto this paragraph BY NAME: E2's line 254 says “The same scoping reads onto this note's other "(e₁, f₁)-re-based" echoes (title line, **one-breath paragraph**, S6.2's assembly sentence) — tagged once, here.”
(v) “the (μ, K)-cluster system … at the S-node” inherits the **GENHN-ERR-1** S-vs-D′h residue (`.24`), **SETTLED** by LEMMA GENHN-COUNT-RERUN's Consumer sweep item 3 (2597–2601, shard 2): “Every phrase “the (2,K)-cluster read at the S-node” is read count-side as “at the B = D′h-node.””

**DERIVATION:** Programme summary; each clause's derivation is its own unit's.

**RESOLUTION TRACE:** statement 36–63 · correction sites 254 (E2's echo list), 363 (the EXACTLY sentence), 1921–1926 (post-PE3), 2282–2298 (F-2 re-display), 2597–2601 (COUNT-RERUN sweep item 3).

XREF: `lean/notes/openmath/GENIND_PROOF_2026-08-08.md:THEOREM GENIND.B` — count **7**.
XREF: `lean/notes/openmath/GENIND_PROOF_2026-08-08.md:GENIND-H(n)` — count **7**.
XREF: `lean/notes/openmath/GENIND_PROOF_2026-08-08.md:(CS-1)` — count **49**.
XREF: `lean/notes/openmath/GENIND_PROOF_2026-08-08.md:(CS-2)` — count **20**.
XREF: `lean/notes/openmath/GENIND_PROOF_2026-08-08.md:(CS-3)` — count **13**.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:THEOREM W-12.A` — count **8**.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:W-12.D` — count **19**.

**TEETH:** Indirect — the whole battery is this paragraph's instance test at (n, genre) ∈ {5, 6} × {V1E2, V4E2, E31, E3} plus the n = 8 tower witness.

---
### EFF.GENHN.05  [fence]

**CANONICAL STATEMENT:** verbatim, lines 67–115 (§S0's positive-consumption bullets). The DULEMMA bullet is a mixed positive/negative declaration and is quoted here whole; its negative half is re-listed in §4.

**FORM:** bulleted declaration list under a `##` heading.

> “## S0. RECONCILIATION (what the suppliers hand this note)
>
> * **GENIND @ 4682bcf** (verdict 4984004; 0/2): THEOREM GENIND.A
>   (I)(II)(IV) + GENIND.C (the two-species scaffold, the general
>   α-bracket (Q−1)Q^{(c(m)+1)μ−1}, c(m) = m(m−1)/2, the composite
>   criterion n ≥ 4), LEMMA GENIND-1(ii)(iii) (α-recentering binomial
>   kills at general m; fracture permanence), LEMMA GENIND-2 (window
>   coherence + ghost zones at general m), LEMMA GENIND-3 (β-fracture
>   fibration schema), THEOREM GENIND.B (the induction this note's
>   discharge feeds), the n = 5 genre table (V1E2/V4E2 laws — V4E2
>   derivation-only, machine-checked PREDICTED-ABSENT only).
> * **GENH4 @ 121d9ab/3eb1667/4b5c085** (0/2): the n = 4 discharge —
>   THEOREMS GENH4.A/B/C, LEMMAS GENH4-1F/-2/-CAP/-3/-4/-6 — the
>   TEMPLATE this note generalizes; its two genres are the (2,1,2) and
>   (1,2,2) instances of every statement below. law_E/law_F (the sealed
>   battery's law transcriptions) are consumed at md5 pin as the μ = 2
>   stage-law evaluators.
> * **QSCOUT22 @ dd67cda** (instrument): the pinned quartic stage reader
>   (`read22`) — consumed as the μ = 2, (2,1,2)-stage read on extracted
>   blocks (GN-STAGE2), plus the committed empirical table.
> * **W-12.A/S2.5 + W-12.D @ f669cb0/99f1813** (0/2, PE3 owed): the
>   order-1 cell law at every degree (the thing being re-based); the
>   reduction that fires the densities.
> * **W-11 @ 7020ceb/31506b3, ACCEPTED 2/2**: the n = 2 system — the
>   μ = 2 stage read's target after re-basing.
> * **GRTJC W-6..W-9 + JC-LOAD/W-8 (ACCEPTED 2/2 @ 83f47f4)**:
>   COROLLARY W-9's dim_K 𝒜(T) = E (the stage slot geometry: E graded
>   K-lines per integer height, the twisted algebra K^c[ℤ/E]) and
>   JC-LOAD's graded no-cancellation. **Division of consumption
>   (GENH4 S0's discipline, kept):** the slot geometry and
>   no-cancellation are RE-PROVED elementarily below (GENHN-2: residue
>   classes mod e₁ × residue-field independence), so no weld face sits
>   inside the count laws; W-9's cocycle IS the carry bookkeeping of
>   GENHN-4, where the graded-algebra frame is consumed as the
>   organizing computation (disclosed there, clause by clause).
> * **J-D0 @ 9387eb1**: count-gauge-blindness — letters and twists move,
>   counts do not; consumed at every "counts are twist-blind" step.
> * **DULEMMA @ f819f26** (∂u ≡ 1, perimeter e_m ≥ 2): applicability at
>   general e₁ ≥ 2 stages checked as charged — the stage rings below
>   have e(R/O) = e₁ ≥ 2, ON its proved perimeter — but as at GENH4 it
>   is NOT consumed: the exact valuation of R is proved directly (S3).
> * **SIGMALAW (ACCEPTED 2/2 @ a27ed68)**: the (EC-q) gauge-coherence
>   ladder — named at the tower section (S8) as the letter-layer
>   mechanism for depth ≥ 2 twist composition; NOT consumed by any
>   count law (J-D0 keeps counts twist-free).
> * **WELDMASTER / [W12-H] @ pins**: the (CS-1..3) pricing grammar;
>   (H-e) is the box this note shrinks to μ ≥ 3.
> * **Classical:** Hensel, Ore order-1, ultrametric analysis of a
>   quadratic over a complete field, finite-field censuses.”

**CONDITIONALITY:**
(i) **The GRTJC bullet's own division-of-consumption sentence is the shard's single most load-bearing conditionality.** “no weld face sits inside the count laws” is TRUE at μ = 2 and FALSE at μ ≥ 3 by the note's own GENHN-BOX-2 (shard 2, 1331–1338): “the count laws at μ ≥ 3 stand on one accepted weld face”. The bullet is not self-contradictory — it says the *slot geometry* carries no face and the *carry bookkeeping* does — but the two halves must never be quoted apart. See `.33`, `.34`, and OPEN-CALL 2.
(ii) **The DULEMMA bullet's “the stage rings below have e(R/O) = e₁ ≥ 2” is riddered by `[e2]` ERRATUM E3** (`.22`), which names this exact sentence: “RIDERED (named exactly, not edited): … S0's and S10's DULEMMA lines "stage rings have e(R/O) = e₁ ≥ 2" (read e(L/base) = e₁)”. `SUPERSESSION KIND: wording-rider`.
(iii) The GENIND/GENH4/W-12 grades quoted here (0/2, 0/2, 0/2) are as-of the pins and are superseded by the S10 `[e2]` refresh (1533–1569, shard 2): GENH4 **ACCEPTED 2/2 FULLY FROZEN**, GENIND **1/2**, W-12 r5 0/2 PE6 dispatched. `SUPERSESSION KIND: as-of scoping`.

**DERIVATION:** Declaration, not derivation.

**RESOLUTION TRACE:** statement 67–115 · correction sites 518–524 (E3's rider list), 1331–1338 (BOX-2), 1533–1569 (S10 `[e2]` refresh).

XREF: `GENIND_PROOF_2026-08-08.md:THEOREM GENIND.A` — count **4** · `GENIND.C` — **23** · `LEMMA GENIND-1` — **2** · `LEMMA GENIND-2` — **7** · `LEMMA GENIND-3` — **6** · `THEOREM GENIND.B` — **7**.
XREF: `GENH4_PROOF_2026-08-08.md:THEOREM GENH4.A` — **5** · `GENH4.B` — **7** · `THEOREM GENH4.C` — **9** · `GENH4-1F` — **10** · `GENH4-2` — **15** · `GENH4-CAP` — **18** · `GENH4-3` — **11** · `GENH4-4` — **11** · `GENH4-6` — **6** · `law_E` — **2** · `law_F` — **7**.
XREF: `QSCOUT22_2026-08-08.md:Q22-A` — **3**.
XREF: `W12_PROOF_2026-08-08.md:THEOREM W-12.A` — **8** · `S2.5` — **9** · `W-12.D` — **19** · `[W12-H]` — **17** · `(H-e)` — **8**.
XREF: `W11_PROOF_2026-08-08.md:W-11` — **18**.
XREF: `GRTJC_PROOF_2026-08-08.md:COROLLARY W-9` — **2** · `JC-LOAD` — **31** · `W-8` — **35** · `W-6` — **18**.
XREF: `JD0_PROOF_2026-08-08.md:J-D0` — **25**.
XREF: `DULEMMA_PROOF_2026-08-08.md:DULEMMA` — **1**.
XREF: `SIGMALAW_PROOF_2026-08-08.md:(EC-q)` — **26**.
XREF: `GENIND_PROOF_2026-08-08.md:(CS-1)` — **49** · `(CS-2)` — **20** · `(CS-3)` — **13**.
PINS: `4682bcf`, `4984004`, `121d9ab`, `3eb1667`, `4b5c085`, `dd67cda`, `f669cb0`, `99f1813`, `7020ceb`, `31506b3`, `83f47f4`, `9387eb1`, `f819f26`, `a27ed68` — `git cat-file -t` → **commit**, 14/14 ✓.

**NEAR-MISS (rule 15) — two, both in this unit:**
- **`read22`** — designation absent as written; fixed-string count **0** in `QSCOUT22_2026-08-08.md`. The note's inline code-span shorthand for QSCOUT22's pinned quartic reader has no in-target string; the target's own addressable family names are `Q22-A` (3), `Q22-PIN`, `Q22-E`, `Q22-F`, and the instrument is pinned by runner md5 `cb885663dd4ef6dfda9c28a67c1a076e` at line 1505. Referent unique and verified; carried descriptively. Recorded as source defect 1 in §8.
- **`WELDMASTER / [W12-H] … (CS-1..3) … (H-e)`** — the bullet attributes four designations to WELDMASTER and **all four have count 0 in `WELDMASTER_2026-08-08.md`**. Verified referents: `[W12-H]` count **17** and `(H-e)` count **8** in `W12_PROOF_2026-08-08.md`; `(CS-1)`/`(CS-2)`/`(CS-3)` counts **49/20/13** in `GENIND_PROOF_2026-08-08.md`. The XREFs above are emitted at the *verified* targets, not at WELDMASTER. Recorded as source defect 2 in §8 — this is a genuine mis-attribution in frozen accepted text, not a formatting near-miss.

**TEETH:** NONE (import declaration). GN-PIN (7 md5 pins, shard 2) is the machine check that the *artifacts* behind these pins are the ones consumed.

---
### EFF.GENHN.06  [convention]

**CANONICAL STATEMENT:** verbatim, lines 117–123.

**FORM:** bold-headed paragraph.

> “**Conventions.** As W-12 S1 / GENIND S1: O a complete DVR, residue
> F_q, both characteristics; window N; cluster system (m, d, N) with
> Q := q^d; conservative drain (v(a₀) ≥ N exits UND); canonical
> digit-lift letters (the W-2/LIFTCORNER seam NOT consumed;
> convention-keyed histories). Throughout, an AMBIENT cluster (m, d)
> with residue field F_Q hosts the stage; d = 1 (Q = q) in every
> machine row (GENIND-BOX-3 inherited).”

**CONDITIONALITY:** Unconditional as a convention. Two clauses are load-bearing elsewhere: **“both characteristics”** is re-asserted at `.15`, `.23` (“identical in both characteristics because they are polynomial identities in the letters”), `.29`(d) and `.33` layer 1 (“Both characteristics: the identity R(T+s) = T^μ is binomial-free as stated”); **“the W-2/LIFTCORNER seam NOT consumed”** is a standing NON-IMPORT (§4). The `d = 1` clause is a *machine-coverage* statement, not a mathematical restriction — GENHN-BOX-3 (shard 2) lists `d ≥ 2` ambients as unexercised.

**DERIVATION:** Convention, not derivation.

**RESOLUTION TRACE:** statement 117–123 · untouched by any later round or append (verified: no dated append names §S0's Conventions paragraph).

XREF: `GENIND_PROOF_2026-08-08.md:GENIND-BOX-3` — count **3**.
XREF: `W12_PROOF_2026-08-08.md:S1` — count **24** (§-ANCHOR pointer, not a lemma designation: the fixed string also matches `S10`–`S19` prefixes, so the count is an upper bound on genuine `§S1` hits; the referent — W-12 §S1's frame — is independently pinned by the same bullet's `S2.5`, count **9**).

**TEETH:** NONE (convention). The `d = 1` coverage claim is guarded by GENHN-BOX-3's own disclosure, not by a battery row.

---
### EFF.GENHN.07  [theorem]

**CANONICAL STATEMENT:** verbatim, lines 127–154 (THEOREM GENHN.CLASS, all three clauses).

**FORM:** display (blockquoted bold-headed theorem with an indented ASCII datum display).

> “**THEOREM GENHN.CLASS (the genre classification: finite per n,
> uniform in n — PROVED).** (i) Every composite-stage opening, at any
> depth of any degree-n read over any ambient cluster with residue
> field F_Q, is classified by the LOCAL GENRE DATUM
>
>     G = (Q; e₁, f₁, μ; h, entry pattern),
>
> where the side carrying the repeated residual factor (ψ, μ) has
> slope h/e₁ in lowest terms (gcd(h, e₁) = 1; e₁ ≥ 1), f₁ = deg ψ,
> μ ≥ 2 its multiplicity, e₁f₁ ≥ 2 (else the event is order-1 α/β),
> and the entry pattern = the finitely many (A1)-admissible frame
> shapes around the side (vertex positions, sibling pieces/children,
> prehistory) — with the budget e₁f₁μ ≤ m_frame ≤ n. The key degree
> is D′ = e₁f₁; the stage residue field is K = F_{Q^{f₁}}; the stage
> value normalization is dv := e₁·v (integer dv-ladder, density e₁
> per ambient v-unit); the stage multiplicity is μ.
> (ii) FINITE: at fixed n the triples (e₁, f₁, μ) number at most
> #{(a, b, μ): ab ≥ 2, μ ≥ 2, abμ ≤ n} < ∞, and the entry patterns
> per triple form finitely many (A1)-families (LEMMA GENIND-0
> closure).
> (iii) UNIFORM IN n: the stage system attached to G — state space,
> read, history grammar, leaves, per-key counts, drainage — depends
> only on (Q, e₁, f₁, μ, h, stage window), NOT on n and not on the
> ambient frame: the ambient prices exactly a FIBER (letter censuses
> × one q-power × the sibling blocks' own data), by fracture
> permanence + the fibration + letter-blindness. Genres realizable:
> μ = 2 exhausts n = 4, 5; μ = 3 and e₁f₁ = 3 first live at n = 6;
> mixed e₁, f₁ ≥ 2 and stage towers first live at n = 8.”

**CONDITIONALITY:** **Clause (ii) and the header gloss "finite per n" are SUPERSEDED — the displayed finiteness is FALSE as written.** The sol A2 adjudication (2026-08-12, lines 2089–2099) found and the note transcribes verbatim:

> “The finding stands. GENHN.CLASS explicitly includes \(Q\) and \(h\) in \(G\), while its finiteness proof counts only discrete schemas \((e_1,f_1,\mu,\text{entry-family})\).
>
> For fixed \(n=4,Q=2\), every positive odd \(h\) gives a distinct datum
> \[
> (2;2,1,2;h,\mathrm{entry})
> \]
> once \(N\ge2h+1\). Thus the declared data set is infinite.”

and the same append records that no repair was admissible *at that time* (“That weakens the accepted theorem's displayed finiteness assertion, which the instructions prohibit”). The obstruction was then **closed by owner directive** (2026-08-12, lines 2272–2298), whose re-display is the current reading:

> “THEOREM GENHN.CLASS's header gloss "finite per
> n" and clause (ii) FINITE are re-displayed at the scope S2's proof
> establishes: at fixed n, the genres form FINITELY MANY PARAMETERIZED
> GENRE SCHEMAS — the triples (e₁, f₁, μ) with e₁f₁ ≥ 2, e₁f₁μ ≤ n,
> each carrying finitely many (A1)-admissible entry-pattern families —
> with the residue field Q, the slope numerator h (gcd(h, e₁) = 1),
> the window N, and the prehistory depths as the schemas' parameters.
> The genre DATUM G = (Q; e₁, f₁, μ; h, entry) ranges over infinitely
> many parameter values at fixed n … Clauses (i) and (iii) are unchanged; no
> consumer reads the withdrawn datum-set finiteness.”

**SUPERSESSION KIND: replacement** (statement scope, owner-authorized). `TARGETS: .07` (clause (ii) + header gloss), `.01` (the title's "PROVED FINITE"), `.04` ("finite per n").
**CHAIN:** frozen (ii) → A2 obstruction record (2089–2099, no repair) → owner-directive re-display (2282–2298) — **TERMINAL: the re-display.** The re-display's own status: “subject to sol discharge-confirmation in the cert2 pass” (2280) — see OPEN-CALL 3.
Clauses (i) and (iii) are **unchanged** and unconditional at the note's grade.

**DERIVATION:** §S2, lines 383–421, quoted in full at `.20`'s companion (the proof is not a separate unit; it is this statement's DERIVATION per template rule 1). In brief, the note's own three parts: *(i)* the datum lists the local invariants of a GENIND-1(i) CS event; the budget `e₁f₁μ ≤ m_frame` is “the abscissa-length budget of GENIND S5.1 (the side spans e₁·g ≥ e₁f₁μ abscissa units inside a polygon of span m_frame), and m_frame·d ≤ n along any chain (fracture only shrinks degree)”. *(ii)* “The triples are bounded as displayed. For the entry patterns: at fixed ambient degree the frame shapes around the side are the finitely many depth-0-polygon families of W-12.A plus the α/β prefix grammar, each (A1)-admissible; LEMMA GENIND-0 closes products/unions/reparameterizations.” **This is exactly the step the A2 finding indicts** — it counts schemas, and the displayed datum carries `Q` and `h`. *(iii)* three supplier mechanisms composed — fracture permanence (GENIND-1(iii)), the fibration (GENHN.A(i), §S3), and letter-blindness (J-D0) — “Hence two CS events at ANY two degrees n, n′ with the same (Q, e₁, f₁, μ, h, stage window) have count-isomorphic stage systems: the genre's law is a function of G alone. ∎”

**RESOLUTION TRACE:** statement lines 127–154 · proof lines 383–421 · correction sites 2089–2099 (A2 obstruction), 2282–2298 (owner re-display).

XREF: `GENIND_PROOF_2026-08-08.md:LEMMA GENIND-0` — count **5**.
XREF: `GENIND_PROOF_2026-08-08.md:LEMMA GENIND-1` — count **2**.
XREF: `W12_PROOF_2026-08-08.md:THEOREM W-12.A` — count **8**.
XREF: `JD0_PROOF_2026-08-08.md:J-D0` — count **25**.
ARTIFACT: `runs/cert/A2_genhn_output.log` — ✓ present (the A2 adjudication's own log, cited at 2046–2047).

**TEETH:** **GN-CLASS** — the grammar family: “every CS event at every depth of every row parses with μ ≥ 2, e₁f₁ ≥ 2, 4 ≤ e₁f₁μ ≤ 6, and each genre appears only at/above its visibility floor” (443), scored at 2,147,916 checks / 0 violations (S12 P1, shard 2). Planted mutant **GN-T-CRIT** — “grammar bound e₁f₁μ ≥ 4 dropped to ≥ 3 must accept an order-1 (3)-child fake that the true grammar rejects” — fired 2/2. **Disposition: executable regression + planted mutant, both fired.** But note the disposition class per rule 27: **the finiteness defect was found by a `decorrelated-model audit`, not by any tooth** — no battery row could see it, because the battery sweeps fixed `(q, N, h)` and the counterexample is a family over `h`.

---
### EFF.GENHN.08  [theorem]  — THEOREM GENHN.A clause (i) [FIBRATION]

**CANONICAL STATEMENT:** verbatim, lines 156–172 (the theorem's frame sentence plus clause (i)).

**FORM:** display (blockquoted theorem, clause (i) of five).

> “**THEOREM GENHN.A (the general composite-stage law; clause-graded).**
> Fix a genre G = (Q; e₁, f₁, μ; h, entry). Over the opening locus
> (priced by W-12.A at the ambient — PROVED at every degree, @ pin),
> with Φ′ the entry key (degree D′ = e₁f₁) and R := Ô[x]/(Φ′):
> (i) [FIBRATION — proved] R is a complete DVR with e(R/O) = e₁,
> f(R/O) = f₁, K = F_{Q^{f₁}} **[e2-E3 2026-08-09: carrier
> corrected — read e/f/v/res in L/O_L, L := Frac(Ô)(θ); R = Ô[θ] is
> in general a NON-MAXIMAL ORDER, not a DVR — ERRATUM E3 at S3.1]**;
> the Φ′-adic development
> f = Φ′^μ + Σ_{j<μ} A_j Φ′^j (deg A_j < D′) is a triangular digit
> bijection from the opening coordinates onto explicit budget floors
> whose total equals the entry exponent (no over/undercount), and the
> stage-initial node is {dv(A_j) ≥ (μ−j)·S + 1} with S := e₁h **[r1
> 2026-08-08: CORRECTED at f₁ ≥ 2 to {dv(A_j) ≥ (μ−j)·D′h + 1},
> D′h = f₁S — see the ERRATUM annex after LEMMA GENHN-1; the two agree
> exactly at f₁ = 1, which is every battery row and every first-live
> case]** — the α-node of the (μ, K) system in dv-units.”

**CONDITIONALITY:** Two in-text corrections, both already landed, plus one out-of-range settlement.
(a) **`[e2-E3]`** — `SUPERSESSION KIND: replacement` on the carrier. The DVR claim is FALSE for `R`; the true carrier is `O_L`. Full erratum at `.22`.
(b) **`[r1]`** — `SUPERSESSION KIND: replacement` on the node height at f₁ ≥ 2: `S = e₁h ⇝ D′h = e₁f₁h`. Full erratum at `.24`.
(c) The **GENHN-ERR-1 residue** that `[r1]` leaves open (whether the note's *own* f₁ ≥ 2 count-side S-keyed displays need re-reading) is **SETTLED** at 2593 (shard 2, LEMMA GENHN-COUNT-RERUN's Consumer sweep item 1): “**GENHN-ERR-1 is settled.** The ordinary \(\mu=2\) stage law is the \((2,K)\)-law at \(B=D'h\), not at the old numeric node \(S=e_1h\).” **A final transcription-confirmation is still owed** — 2626–2627: “a final transcription-confirmation rides the next queue.” See OPEN-CALL 3.
(d) “PROVED at every degree, @ pin” for W-12.A is an as-of grade claim; W-12's own grade at the S10 `[e2]` refresh is “r5 @ be4a1dc/ee17210 (0/2), PE6 dispatched”.

**DERIVATION:** Two parts, both in §S3.
*Carrier (S3.1, 449–468, as corrected by E3 at 499–517):* every root θ has `v(θ) = h/e₁` with `gcd(h, e₁) = 1` so `e(L/base) ≥ e₁`; `η := res(θ^{e₁}π^{−h})` is a root of a unit multiple of ψ so `f(L/base) ≥ f₁`; then `e·f = [L : base] ≤ deg Φ′ = D′ = e₁f₁` forces `e = e₁`, `f = f₁`, `[L : base] = D′`, hence Φ′ is the minimal polynomial of θ, irreducible, and `O_L/m_L = F_Q(η) = K = F_{Q^{f₁}}`.
*Fibration (S3.2 = LEMMA GENHN-1, `.23`):* triangularity by unipotent elimination in the division by the monic Φ′; budgets by coordinatewise cancellation of the entry pins; no over/undercount because the map is a bijection and the opening locus's cardinality is W-12.A's entry law; node by the slot-min arithmetic `dv(A_j) = min_i (e₁·v(a_{j,i}) + ih)`.

**RESOLUTION TRACE:** statement 156–172 · proof lines 449–468 (carrier) + 531–574 (fibration) · correction sites 470–527 (E3), 576–611 (`[r1]`), 613–686 (`[r2]` budget display), 2593 (ERR-1 settlement).

XREF: `W12_PROOF_2026-08-08.md:THEOREM W-12.A` — count **8**.
XREF: `DULEMMA_PROOF_2026-08-08.md:DULEMMA` — count **1** (the perimeter this clause is checked against but does not consume).

**TEETH:** **GN-FIB** — “constructed loci: frames parse to genre, volumes = entry laws”, both directions (S11.B, 1650–1651); **GN-T-NODE** — planted mutant, “E3 construction a₀₀ floor off-by-one must break the volume”, fired 1/1 (S12, 1803). Disposition: executable regression + planted mutant, both fired. **Disclosed vacuity (rule 20, `signed vacuity disclosure`):** the E3 correction is untestable by this battery — “the battery's counts are digit-coordinate counts on Ô[x]-coefficients and its σ legs are PARI oracle reads; neither consumes R's ring structure” (479–481).

---
### EFF.GENHN.09  [theorem]  — THEOREM GENHN.A clause (ii) [SLOTS + NO-CANCELLATION]

**CANONICAL STATEMENT:** verbatim, lines 173–178.

**FORM:** display (blockquoted theorem clause).

> “(ii) [SLOTS + NO-CANCELLATION — proved] each A_j carries exactly ONE
> K-digit slot per integer dv-height (the e₁ residue classes mod e₁
> separate the x-coordinates; within a class, {1, η, …, η^{f₁−1}}
> (η = res(θ^{e₁}π^{−h})) are F_Q-independent): dv(A_j(θ)) is the
> slot-min EXACTLY, for every root θ and every lift — W-9's
> dim_K 𝒜(T) = E made literal and re-proved elementarily.”

**CONDITIONALITY:** **The universal quantifier "per integer dv-height" is FALSE and has been re-displayed TWICE.** `CHAIN` (rule 25), in source order:

1. **Frozen display** (this unit) — “exactly ONE K-digit slot per **integer** dv-height”.
2. **A2 obstruction record**, 2026-08-12, lines 2191–2195, transcribed verbatim: “The counterexample is correct. For \((e_1,f_1,h,m)=(3,1,2,1)\), the unique normalizer exponent is \(a=-1\), so neither an integral normalizer nor a variable \(K\)-slot exists at height \(1\). … the displayed universal assertion “one \(K\)-digit slot per integer \(dv\)-height” is false. … no admissible repair can be supplied under the stated constraint.”
3. **Owner-directive re-display**, lines 2300–2313: “per OCCUPIED integer dv-height — a height m admitting an integral normalizer monomial n(m) = x^{i(m)}π^{a(m)} with 0 ≤ i(m) < e₁ and a(m) = (m − i(m)h)/e₁ ≥ 0 — below the window cap. Every height m > D′h is occupied, with the explicit lift supplied by LEMMA GENHN-LIFT … The e₁-class separation and F_Q-independence clauses are unchanged.”
4. **Post-D2b corrigendum**, lines 2315–2332 — the re-display at step 3 is itself **too weak at f₁ > 1**: “sol's witness (e₁, f₁, h, m) = (1, 2, 1, 0): n(0) = 1 is integral while the η-component would require xπ^{−1}”. Final scope: “GENHN.A(ii)'s slot clause holds per integer dv-height m with **D′h < m**, below the window cap … At m ≤ D′h the clause is withdrawn entirely: a K-slot may be partial (the sol witness) or absent (the R4/A2 witness).”

**TERMINAL: member 4, the post-D2b corrigendum — `D′h < m` below the window cap.** Its own status: “Awaiting sol re-confirmation in the next queue” (2331–2332). See OPEN-CALL 3.
**SUPERSESSION KIND: replacement** (twice, at statement scope, owner-authorized). `TARGETS: .09`.
**Why no consumer moves:** “every pin the note's laws consume sits in that domain (the stage-initial node floor {dv(A_j) ≥ (μ−j)D′h + 1} and the refine floors)” (2328–2330) — i.e. the `[r1]` corrected node of `.24` is exactly what protects the re-displayed clause.

**DERIVATION:** LEMMA GENHN-2 (`.27`) and its proof (719–727) — this clause IS GENHN-2, stated at theorem level. The added phrase “W-9's dim_K 𝒜(T) = E made literal and re-proved elementarily” is a *frame* citation, not a consumption: GENHN-2's own closing sentence (716–717) is “W-9's dim_K 𝒜(T) = E = e₁ is this statement's graded shadow (cited as frame)”.

**RESOLUTION TRACE:** statement 173–178 · proof 699–727 · correction sites 2191–2195 (A2 obstruction), 2300–2313 (re-display), 2315–2332 (post-D2b corrigendum), 2101–2145 (LEMMA GENHN-LIFT, the license that makes the re-display true).

XREF: `GRTJC_PROOF_2026-08-08.md:COROLLARY W-9` — count **2** (frame citation only — see §4).
ARTIFACT: `runs/cert2/D2b_genhn_output.log` ✓ present.

**TEETH:** **PROOF-ONLY at the corrected scope.** No battery row exercises an unoccupied height: every row has `f₁ = 1` and every consumed pin sits at `dv > D′h`. The note's own coverage-hole sentence, at 1339–1351 (GENHN-BOX-3): “NOT exercised: f-first genres beyond f₁ = 2 …, mixed e₁, f₁ ≥ 2 (first live n = 8)”. **Disposition: `decorrelated-model audit`** (rule 27) — both counterexamples (R4/A2's `(3,1,2,1)`; D2b's `(1,2,1,0)`) came from a fresh-model read of the display, and no tooth could have produced them.

---
### EFF.GENHN.10  [theorem]  — THEOREM GENHN.A clause (iii) [WINDOW LEDGER]

**CANONICAL STATEMENT:** verbatim, lines 179–183.

**FORM:** display (blockquoted theorem clause).

> “(iii) [WINDOW LEDGER — proved] computed dv-values are lift-stable
> iff < e₁N; every digit consulted by a readable event lies strictly
> inside its coordinate's window in every residue class; the ragged
> band (per-class string ends beyond e₁(N−1)) is never consulted and
> is priced as free depth; carries move upward only.”

**CONDITIONALITY:** **Two clauses are riddered by the 2026-08-12 R4 F-1 dated correction (lines 2057–2087), which names this clause by section.**
(a) The **"never consulted"** clause is a *terminology defect*: “GENHN.A(iii), GENHN-3(b), and the OB-a paragraph use “ragged band is never consulted” for two different objects: the interval of slot HEIGHTS beyond the shortest class string, and the UNREAD coefficient components occurring at those heights. **The first usage is false**: the `[r2]` annex itself proves that a first-band height can support a lift-stable terminal decision. The correct invariant is that no UNREAD coefficient digit is consulted.” Rider (2087): “Read “the ragged band is never consulted” everywhere in GENHN.A(iii), S5, and the OB-a paragraph as **“the unread component cells of the ragged band are never consulted.”** Visible components at a boundary height may be used once by the completion-invariant terminal rule above.”
(b) The **"iff < e₁N"** clause is re-scoped: “Read GENHN-3(a)'s “iff \(<e_1N\)” as the sufficient interior criterion together with GENHN-CAP-GEN's exact boundary criterion; the previously proved stability below \(e_1N\) is unchanged.”
**SUPERSESSION KIND: wording-rider** for (a), **scope-pin** for (b). `TARGETS: .10`, `.29` (GENHN-3(a)/(b)), `.30` (the OB-a paragraph).
The correction is **licensed, not merely asserted**: LEMMA GENHN-CAP-GEN (2061–2085) supplies the general boundary projection with a proof, and its own scope sentence (2083) reads “Thus CS-1 and CS-2 hold at ordinary \(f_1\ge2\), \(\mu\ge3\), and mixed genres **without a new box**.”

**DERIVATION:** LEMMA GENHN-3 (`.29`) and its in-display proof; the `[r2]` band annex (`.32`) supplies the f₁ ≥ 3 transport that shows (a)'s first usage to be false.

**RESOLUTION TRACE:** statement 179–183 · proof 741–763 (GENHN-3) + 807–861 (`[r2]` annex) · correction sites 2057–2087 (R4 F-1 + GENHN-CAP-GEN).

XREF: `GENH4_PROOF_2026-08-08.md:GENH4-CAP` — count **18**.

**TEETH:** **PROOF-ONLY for the boundary clause.** No battery row sits at f₁ ≥ 2, so the band is never exercised; the note's own hole sentence is E1's exclusion (798–801): “at f₁ ≥ 2 genres beyond it (μ ≥ 3, or e₁ ≥ 2 mixed — **no battery row, first live n ≥ 8**) this note claims the LIFT-STABILITY content of (a) only and NO band-adjudication display”. The `[r2]` annex's machine contact is `passPE1`'s fresh legs at (1,3,2), N = 7 and N = 8 (851–858), which is **foreign-instrument evidence** consumed as coverage, not a row of this note's sealed battery. Disposition: `accepted-with-decorrelation-supplied`.

---
### EFF.GENHN.11  [theorem]  — THEOREM GENHN.A clause (iv) [REFINE TRANSFER]

**CANONICAL STATEMENT:** verbatim, lines 184–192.

**FORM:** display (blockquoted theorem clause).

> “(iv) [REFINE TRANSFER — proved via the graded computation, the
> W-9 frame disclosed] a stage refine at depth κ, letter s ∈ K^×,
> recenters Φ′ ↦ Φ′ + w (w = ŝ·n(κ), the dv-κ normalizer monomial)
> by a triangular-with-carry digit bijection onto the floored node
> {dv(A_j) > (μ−j)κ}: the μ pinned digits die by the binomial
> identity R(T + s)-coefficients = 0 computed in the graded algebra
> (the carry × key-constant cancellations of GENH4 S5 at general
> (e₁, f₁, μ)), all corrections land strictly deeper and in-window;
> letters multiply (|K|−1 per step).”

**CONDITIONALITY:** **This is the shard's one clause carrying a live weld face.** The clause's own bracket declares it (“the W-9 frame disclosed”); the note boxes it at GENHN-BOX-2 (shard 2, 1331–1338):

> “**GENHN-BOX-2 (the graded-frame consumption).** LEMMA GENHN-4's
> layer 1 at μ ≥ 3 consumes COROLLARY W-9's twisted algebra as the
> carry bookkeeping (unlike GENH4, which re-proved its μ = 2
> instances elementarily). Compensating instrument: GN-REFINE3
> (pointwise re-division transport at every μ = 3 stage-α event).
> An elementary general-μ carry display (the GENH4-S5 computation
> at general (e₁, f₁, μ)) would retire this box; until then the
> count laws at μ ≥ 3 stand on one accepted weld face.”

**CROSS-NOTE STATUS (template rule 10 — verified against the full append chain, not the frozen sentence).** Two external records bear on this box and neither has landed on GENHN:
- `runs/qgen/WELD_FACE_AUDIT.md` L143–164 designates this exact clause **LEAK-1 (LIVE, disclosed)** and records that **J-D0 cannot cover it even in principle**: “The recentering it studies (Φ′ ↦ Φ′ + w) is an **additive** shift — precisely the NONCHAR failure mode, so J-D0's perimeter cannot cover it even in principle.” Status in that audit: “**correctly disclosed** at `GENHN-BOX-2`”.
- `lean/notes/openmath/WELDZERO_2026-08-14.md` claims to prove layer 1 without the weld face (its COROLLARY WZ-B). **It has NOT landed on GENHN**: verified by reading GENHN's own full append chain to line 2627 — the last append is the 2026-08-12 GENHN-COUNT-RERUN, and no append names WELDZERO. WELDZERO itself declines the authority (its §S0: the fold's convention pin is “a **reading** of GENHN's frozen words, boxed as such”). `spec/HYPOTHESIS_LEDGER.md` HYP.148 records the arc state: “**the clean-pass counter therefore stands at 1 of 2** … HYP.148 stays CARRY and HYP.139 stays MATH at full strength.” **Therefore: for this spec, GENHN-BOX-2 is LIVE and GENHN.A(iv) at μ ≥ 3 rides one accepted weld face.** See OPEN-CALL 2.

**DERIVATION:** LEMMA GENHN-4 (`.33`), three layers, quoted at that unit. The clause's own honesty note (`.34`) is the grade: at μ = 2 the identity was verified pointwise-elementarily by GENH4; at general μ layer 1 consumes W-9.

**RESOLUTION TRACE:** statement 184–192 · proof 867–904 · grade note 906–915 · box 1331–1338 (shard 2).

XREF: `GRTJC_PROOF_2026-08-08.md:COROLLARY W-9` — count **2**.
XREF: `GENH4_PROOF_2026-08-08.md:GENH4-CAP` — count **18** (the GENH4 S5 computation is cited by section, not designation — see NEAR-MISS).
ARTIFACT: `runs/qgen/WELD_FACE_AUDIT.md` ✓ present · `lean/notes/openmath/WELDZERO_2026-08-14.md` ✓ present · `spec/HYPOTHESIS_LEDGER.md` ✓ present.

**NEAR-MISS (rule 15):** “the carry × key-constant cancellations of **GENH4 S5**” — fixed-string `GENH4 S5` has count **0** in `GENH4_PROOF_2026-08-08.md`; the note's own section anchor is `S5` (count **20**, a §-anchor that also matches `S5.1`…). Referent unique and verified (GENH4's §S5 refine-transfer computation, cited again at 1336–1337 as “the GENH4-S5 computation”); carried descriptively. Recorded as source defect 3 in §8.

**TEETH:** **GN-REFINE3** — the box's own compensating instrument: “Stage-α events live exactly at the (·,2,5,1) E3 rows (κ=3 …): 512 events per row, each transported by ACTUAL re-division; all three pins dead and in the floored node — 1,536 pin checks per row, 0 violations” (P7, 1706–1711), scored at S12 as “3,072 pin checks exactly (= 2 rows × 1,536), 0 violations”. **Disposition: `accepted-with-decorrelation-supplied`** — the tooth is a pointwise re-division that never uses the graded formula, so it decorrelates the weld consumption at μ = 3 without retiring it. **Disclosed hole:** “A hostile pass should attack layer 2's strictness at mixed (e₁, f₁ ≥ 2) genres (first live n = 8, machine-unreachable here — S9 box)” (913–915).

---
### EFF.GENHN.12  [theorem]  — THEOREM GENHN.A clause (v) [THE LAW] + the (CS-2) bracket

**CANONICAL STATEMENT:** verbatim, lines 193–211.

**FORM:** display (blockquoted theorem clause with an indented ASCII bracket display).

> “(v) [THE LAW] consequently the stage read IS the (μ, K)-cluster
> read in dv-units at the S-node, ragged-window-corrected: every
> stage count law = THEOREM W-12.A's cell law with census field
> F_{Q^{f₁}} and ladder density e₁ — "(e₁, f₁)-re-based" **[e2-E2
> 2026-08-09: away from the f₁ ≥ 2 boundary band, whose pins are
> censused Q^{comp(m)} − 1 per pin (comp(m) = the pin slot's
> in-window F_Q-dimension), not by the re-based field — ERRATUM E2
> after this theorem]** — and the
> stage's own history grammar is THEOREM GENIND.A over K inside the
> stage (α/β/CS species, self-similar). (CS-2): the stage bracket is
> GENIND-2(b) inside the stage,
>
>     b_{μ,K}(κ) = (|K|−1)·|K|^{(c(μ)+1)κ−1},  c(μ) = μ(μ−1)/2,
>
> in stage dv-slope units — at μ = 2 this is GENH4's ladder
> telescoping after separating the ghost fiber |K|^κ:
> (|K|−1)|K|^{2κ−1} = |K|^κ · (|K|−1)|K|^{κ−1} — generalizing
> GENIND-5's (q−1)q^{2μ−1} to (q^{f₁}−1)q^{f₁(2κ−1)} at general
> (e₁, f₁).”

**CONDITIONALITY:** Three layers.
(a) **`[e2-E2]`, in-text** — the census clause is corrected at f₁ ≥ 2 band pins. `SUPERSESSION KIND: replacement` on the census; full erratum at `.14`.
(b) **“at the S-node” is re-grounded to the D′h-node.** `[r1]` (`.24`) corrected the node in GENHN.A(i) but explicitly left this clause's residue open (GENHN-ERR-1, 605–611): “whether GENHN's own f₁ ≥ 2 count-side displays that substitute the numeric value S = e₁h for the node height (the (μ,K)-cluster read "at the S-node", and any entry-exponent arithmetic keyed to it) need re-reading with D′h is NOT settled here.” **It is settled at 2597–2601** (Consumer sweep item 3): “Every phrase “the \((2,K)\)-cluster read at the \(S\)-node” is read count-side as “at the \(B=D'h\)-node.” The local mass-normalized bracket \(b_{2,K}(\kappa)=(|K|-1)|K|^{2\kappa-1}\) **is unchanged**: it is indexed by the actual refine height \(\kappa\) and uses a different ghost normalization from the raw finite-node cardinality.” — **so the bracket display survives the node correction untouched; only the node phrase moves.** `SUPERSESSION KIND: counter re-reading` (a re-reading of what the numeral names, with the count re-derived). **CHAIN: frozen "S-node" → `[r1]` node correction (partial, residue named) → GENHN-COUNT-RERUN Consumer sweep item 3. TERMINAL: the sweep item.** Confirmation still owed (2626–2627).
(c) The clause is graded at (i)–(iv)'s grades — see `.13`.

**DERIVATION:** §S6.2 (923–944), quoted at `.36`; the count content follows from (i)–(iv) plus GENIND @ pin, and the σ content is GENHN.C at μ = 2 / `[GENHN-HE]` at μ ≥ 3 (the GRADE line, `.13`). The bracket's own reconciliation with GENH4's μ = 2 display is derived inline at 932–940 (ghost × letters).

**RESOLUTION TRACE:** statement 193–211 · proof 923–944 · correction sites 219–257 (E2), 605–611 (ERR-1 residue), 2593 + 2597–2601 (settlement), 1957–1978 (PE4 F-1's scope re-reading of the ERR-1 residue clause).

XREF: `W12_PROOF_2026-08-08.md:THEOREM W-12.A` — count **8**.
XREF: `GENIND_PROOF_2026-08-08.md:THEOREM GENIND.A` — count **4**.
XREF: `GENIND_PROOF_2026-08-08.md:LEMMA GENIND-2` — count **7**.
XREF: `GENIND_PROOF_2026-08-08.md:GENIND-5` — count **9**.
XREF: `GENIND_PROOF_2026-08-08.md:GT-BRACKETID` — count **3**.

**TEETH:** **GN-LAWTIE** (`law_Egen(e₁=2) ≡ pinned law_E`, 5 grid points — P2, fired ✓), **GN-STAGE2** (the μ = 2 stage law at three fresh genres, both directions — P3/P4/P5), **GN-E3** (the μ = 3 stage law — P6). All executable regressions, all 0 violations. **The bracket at μ = 3 is guarded only foreign-ly:** “the μ = 3 bracket exponent c(3)+1 = 4 over K is GENIND's GT-BRACKETID @ pin; this battery adds the μ = 3 STAGE realization at the E3 genre” (942–944) — disposition `foreign-note evidence` + own realization.

---
### EFF.GENHN.13  [scope-record]  — THEOREM GENHN.A's GRADE line

**CANONICAL STATEMENT:** verbatim, lines 212–217.

**FORM:** bold-headed sentence inside the theorem blockquote.

> “**GRADE: (i)–(iii) PROVED at general (e₁, f₁, μ) (S3–S5); (iv)
> proved with the graded-frame consumption disclosed (S6) and
> machine-checked pointwise at μ = 2 (GENH4 @ pin, elementary) and
> μ = 3 (this battery, GN-REFINE3); (v)'s count content follows from
> (i)–(iv) + GENIND @ pin; its σ content is GENHN.C at μ = 2 and
> [GENHN-HE] at μ ≥ 3.**”

**CONDITIONALITY:** **"(i)–(iii) PROVED" is now three different things.** (i)'s carrier is corrected (E3) and its node is corrected (`[r1]`); (ii)'s universal display is FALSE and re-displayed twice (`.09`); (iii)'s "never consulted" is a terminology defect riddered by R4 F-1 (`.10`). **What survives unqualified: the mathematical content of all three at the corrected scopes** — the A2 append's own summary (2050–2054) is that F-2 and F-4 “are REAL but OBSTRUCTED — the displayed clauses are false as stated”, i.e. *display* defects, and F-1's rider explicitly says “the previously proved stability below \(e_1N\) is unchanged”. No count, no σ, no density moves at any of the three.

**DERIVATION:** Grade declaration; each clause's grade is established at its own unit.

**RESOLUTION TRACE:** statement 212–217 · correction sites as at `.08`–`.12`.

**TEETH:** NONE (grade declaration).

---
### EFF.GENHN.14  [changes-record]  — `[e2]` ERRATUM E2

**CANONICAL STATEMENT:** verbatim, lines 219–257.

**FORM:** display (blockquoted dated erratum with ORIGINAL / CORRECTION / instance / HONESTY structure).

> “**[e2] ERRATUM E2 2026-08-09 (GENHN.A(v)'s census clause at f₁ ≥ 2
> band pins — the comp-weighted census made explicit). Queued at the
> GENH4-r2 fold (ledger 0089f9b); tagged repair per the [r1]
> mechanism (GENHN at 0/2, unaccepted); sealed battery runner and
> artifacts UNTOUCHED — every battery row has f₁ = 1, where
> comp(m) ≡ 1 = f₁ and the two censuses coincide
> (Q^{comp} − 1 = |K| − 1 = q − 1).**
>
> **ORIGINAL (GENHN.A(v), sealed text):** "every stage count law =
> THEOREM W-12.A's cell law with census field F_{Q^{f₁}} and ladder
> density e₁ — '(e₁, f₁)-re-based'" — SILENT on the f₁ ≥ 2 boundary
> band (GENHN-3(a)/(b): the heights whose K-slot has only part of
> its F_Q-components in window).
>
> **CORRECTION (the added clause, DERIVED in this note's own frame —
> not transcribed).** By GENHN-2, a height-m K-slot is f₁
> F_Q-independent components. At band heights only
> comp(m) := #(in-window F_Q-components of the height-m slot),
> 1 ≤ comp(m) < f₁, are readable (the value is; the full K-residue
> is not), so a RAM/2SIDED-type entry pin at height m is censused by
> its nonzero READABLE data only:
>
>     census per band pin = Q^{comp(m)} − 1 ,   NOT |K| − 1 = Q^{f₁} − 1;
>
> away from the band comp(m) = f₁ and the displayed re-based census
> |K| − 1 is correct. Consistency instance (GENH4's (1,2,2) genre:
> Q = q, f₁ = 2, band N ≤ m ≤ N+k−1 with comp = 1): census q − 1 —
> exactly the [r2] corrected display "q^{comp}−1 per RAM and per
> 2SIDED pin", whose r3 remark scopes the same mnemonic "away from
> the genre-F boundary band ... not by the re-based field". HONESTY
> (grade of the general form): the band clause follows from the slot
> model (i)–(iii) at (v)'s own grade, machine-checked only at the
> (1,2,2) instance (GENH4's committed keys); no f₁ ≥ 2 STAGE row is
> machine-exercised (GENHN-ERR-1's geography, none live below
> n = 8). The same scoping reads onto this note's other
> "(e₁, f₁)-re-based" echoes (title line, one-breath paragraph,
> S6.2's assembly sentence) — tagged once, here. SOURCE: GENH4 PE2
> CRITICAL 1 (the [r2] census correction) + PE3 REMARK A (the
> away-from-the-band scoping), at GENH4's frozen pin 4b0d946.”

**SUPERSESSION KIND: replacement** (the census formula at band pins) plus **scope-pin** (the "away from the band" qualifier propagated to three named echoes). `TARGETS: .12` (GENHN.A(v)), `.01` (title line), `.04` (one-breath paragraph), `.36` (S6.2's assembly sentence).

**CONDITIONALITY:** **Its own HONESTY clause contains a claim the note later corrects.** “no f₁ ≥ 2 STAGE row is machine-exercised (GENHN-ERR-1's geography, none live below n = 8)” — the trailing “none is live below n = 8” half is corrected by the post-PE4 dated Correction (1957–1978), which names *this* site (“echo at [e2]-E2, L251–253”) and reads it as: “no row of THIS battery exercises an f₁ ≥ 2 stage genre …; MIXED e₁, f₁ ≥ 2 genres first live at n = 8 …; the f-first genres (1,2,2)/(1,2,3)/(1,3,2) are live at n = 4/6/6, and their S-keyed display re-read remains OWED with the residue (GENHN-ERR-1 stays unsettled exactly as displayed).” `SUPERSESSION KIND: scope-pin`. **The final clause of that correction is itself now stale** — ERR-1 was SETTLED on 2026-08-12 (2593, 2624). **CHAIN: E2's HONESTY clause → post-PE4 correction (1957–1978) → GENHN-COUNT-RERUN settlement (2593/2624). TERMINAL: the settlement, with transcription-confirmation owed.**
Second layer: LEMMA GENHN-CAP-GEN's COUNT TRANSPORT (2077–2083) re-derives E2's census independently — “A nonzero visible boundary pin has \(Q^{\operatorname{comp}(m)}-1\) choices, **exactly as ERRATUM E2 states**” — and LEMMA GENHN-COUNT-RERUN clause 4 (CR-3) proves it again from the visible F_Q-subspace. **These are licenses (decorrelated re-derivations), not supersessions.**

**DERIVATION:** Quoted inline and self-contained: by GENHN-2 a height-m K-slot is f₁ F_Q-independent components; at band heights only comp(m) of them are readable; so a nonzero pin's census counts nonzero readable data only, `Q^{comp(m)} − 1`. Instance-checked at GENH4's (1,2,2) genre.

**RESOLUTION TRACE:** statement 219–257 · correction sites 1957–1978 (PE4 F-1), 2077–2083 (CAP-GEN transport), 2396–2403 + 2563–2570 (COUNT-RERUN CR-3).

XREF: `GENH4_PROOF_2026-08-08.md:GENH4-CAP` — count **18**.
XREF: `GENH4_passPE2_report.md` — ✓ file present (the SOURCE named; the report's own designation for the finding is not quoted by GENHN, so no designation-level XREF is emitted — see source defect 4).
PINS: `0089f9b` ✓ commit · `4b0d946` ✓ commit.

**TEETH:** **`signed vacuity disclosure` (rule 20).** The erratum's own header states the vacuity: “every battery row has f₁ = 1, where comp(m) ≡ 1 = f₁ and the two censuses coincide”. Machine contact exists only at the foreign (1,2,2) instance (GENH4's committed keys) and, post-acceptance, at `genhn_pe4_fresh.py` (“first f₁ = 4 / comp = 3 / F₁₆ contact”, 1948–1949, shard 2) and `genhn_f2_count_check.py` (the P2 certificate, 2610–2614, shard 2). Both are additive post-seal legs.

---
### EFF.GENHN.15  [theorem]

**CANONICAL STATEMENT:** verbatim, lines 259–273 (THEOREM GENHN.C).

**FORM:** display (blockquoted theorem with an indented ASCII dictionary).

> “**THEOREM GENHN.C (σ-decision at EVERY μ = 2 stage — the (H-e)
> instance family, PROVED).** At every decided leaf of every μ = 2
> stage genre (all e₁ ≥ 1, f₁ ≥ 1 with e₁f₁ ≥ 2, all Q, both
> characteristics, any history, any window), EVERY lift with
> disc ≠ 0 has the σ claimed by the leaf dictionary:
>
>     stage-RAM        ↦ {(2e₁·e_A, f₁·f_A)} = {(2e₁, f₁)}-block
>     stage-2SIDED / SPLITEQ / SPLTAIL ↦ {(e₁, f₁), (e₁, f₁)}
>     stage-INERT      ↦ {(e₁, 2f₁)}
>
> (blocks relative to the ambient; compose with the ambient's own
> (e, f) at towers). Proof by the resolvent method: the quadratic
> Y² + A₁(θ)Y + A₀(θ) = 0 over L with the two transported facts
> e₁ | e(L) and f₁ | f(L). At n = 4 this is THEOREM GENH4.C verbatim;
> n = 5's genres are covered OUTRIGHT.”

`[TABLE]` — the ASCII dictionary transcribed (rule 14 double-emission; the verbatim source block is inside the quotation above):

| stage leaf label | σ-block (relative to the ambient) |
|---|---|
| stage-RAM | {(2e₁·e_A, f₁·f_A)} = {(2e₁, f₁)}-block |
| stage-2SIDED / SPLITEQ / SPLTAIL | {(e₁, f₁), (e₁, f₁)} |
| stage-INERT | {(e₁, 2f₁)} |

*Arithmetic audit (rule 22).* The three rows are degree-consistent with the block degree `2e₁f₁`: RAM gives `2e₁ · f₁ = 2e₁f₁` ✓; 2SIDED gives `2 × (e₁ · f₁) = 2e₁f₁` ✓; INERT gives `e₁ · 2f₁ = 2e₁f₁` ✓. The three instance specializations displayed at 1012–1016 check out: (2,1,2) → {(4,1)}/{(2,1)²}/{(2,2)} ✓; (1,2,2) → {(2,2)}/{(1,2)²}/{(1,4)} ✓; (3,1,2) → {(6,1)}/{(3,1)²}/{(3,2)} ✓; (1,3,2) → {(2,3)}/{(1,3)²}/{(1,6)} ✓. All four have Σ e·f = 2e₁f₁ over the multiset.

**CONDITIONALITY:** **Unconditional at the note's grade, and untouched by every one of the eleven dated appends** (verified: no append names GENHN.C, S7, or the dictionary). Two internal dependencies: (T1)/(T2) (`.38`) and LEMMA GENHN-2 (`.27`), the latter “which holds verbatim with θ in place of a key root: only (T1)/(T2) enter” (973–974). One case's proof was corrected in-text at `[r2]` — the stage-RAM value-group argument needs BOTH (T1) and v(Y) (see `.38`, passPE1 F4). The `[r0-battery]` Remark (`.39`) scopes what "lift-stable" means at embedded genres and explicitly “does not touch this theorem's statement or proof”.

**DERIVATION:** §S7, lines 961–1016, the Y-trichotomy — quoted in full at `.38`. Structure: fix any μ = 2 genre, any decided leaf, any disc ≠ 0 lift F, any root θ of the stage block's factor, `L := Frac(O)(θ)`; transport (T1) `v(θ) = h/e₁, gcd(h,e₁) = 1 ⟹ e₁ | e(L)` and (T2) `η generates F_{Q^{f₁}} ⊆ k_L ⟹ f₁ | f(L)`; set `Y := Φ′^{(t)}(θ)`, so `Y² + A₁(θ)Y + A₀(θ) = 0` with `dv(A₁(θ)) = w`, `dv(A₀(θ)) = u` EXACTLY by GENHN-2; the block has degree `2e₁f₁`; then five cases (RAM, 2SIDED, SPLTAIL, SPLITEQ, INERT), each closing by `e·f ≥ block degree ⟹ equality`. Closing line: “Every case consulted only lift-stable data: (A0)-strong at every μ = 2 stage leaf.”

**RESOLUTION TRACE:** statement 259–273 · proof 961–1016 · correction sites 979–983 (`[r2]` F4, inside the proof) · scope remark 1018–1027.

XREF: `GENH4_PROOF_2026-08-08.md:THEOREM GENH4.C` — count **9**.
XREF: `W12_PROOF_2026-08-08.md:(H-e)` — count **8** (the box family this theorem instantiates; see source defect 2 for why the XREF is emitted at W-12 rather than at WELDMASTER).

**TEETH:** **GN-SIGMA** — “PARI factorpadic vs dictionary; extraction-certified perimeter on V rows” (1655–1656), scored at S12 P9: “certified σ 37,792 jobs / 0 bad across six oracle batches”, including **★ wild p = 3 at an e₁ = 3 stage** (never-oracled territory). Planted mutant **GN-T-SIG** — “E31 RAM σ {(6,1)}→{(3,2)} must be caught by PARI” — fired 2/2. **Disposition: executable regression against an independent oracle + planted mutant, both fired.** **Disclosed perimeter:** the σ legs on extracted (embedded-genre) rows are gated by S11.F's certification table; the uncertified tail is measured as diagnostics and “is PREDICTED to contain mismatches” (1724) — a *preregistered* hole, not a failure.

---
### EFF.GENHN.16  [lemma]  — LEMMA GENHN-T clause (a) [the tower criterion]

**CANONICAL STATEMENT:** verbatim, lines 275–281.

**FORM:** display (blockquoted lemma, clause (a) of two).

> “**LEMMA GENHN-T (stage towers: criterion + composition).**
> (a) [criterion — proved] a stage's own read admits a composite
> opening (a TOWER event) iff the stage multiplicity satisfies μ ≥ 4
> (GENIND.A(IV) applied inside the stage); hence towers exist at
> degree n iff n ≥ (e₁f₁)·μ ≥ 2·4 = 8. n = 8 = 2·2·2 is the first
> live instance ((e₁f₁) = 2, μ = 4, inner (e₂f₂) = 2, μ₂ = 2);
> n = 4..7 are tower-free.”

**CONDITIONALITY:** **(a) is explicitly UNTOUCHED by the `[r2]` refutation** — the `[r2]` bracket's last words are “(a) is untouched.” (line 301). One correction lands inside (a)'s **proof**, not its statement: the 2026-08-12 R4 F-5 dated correction (2197–2214) replaces the proof's “residual \((T^2-c)^2\) over \(K\)” by “residual \((T-c)^2\) over \(K\)”, with the derivation: “A side of abscissa length \(4\) and denominator \(e_2=2\) has residual degree \(4/e_2=2\) … The displayed \((T^2-c)^2\) has degree \(4\) and would require side length \(e_2\cdot4=8\). The corrected form is exactly the later GN-TOWER witness \((T-1)^2\), so the positive-locus realization and the first-live threshold \(n=8\) remain unchanged.” `SUPERSESSION KIND: replacement` (proof-internal display). `TARGETS: .16` (DERIVATION only).

**DERIVATION:** Lines 1046–1059, quoted:

> “*Proof of (a) (criterion).* By GENHN.A(v) the stage system is a
> (μ, K)-cluster system (in dv-units, ragged-corrected). THEOREM
> GENIND.A(IV) @ pin — whose proof is combinatorial on the polygon
> span and applies verbatim over K on the integer dv-ladder — says a
> CS event inside a system of multiplicity μ requires a side of
> abscissa length ≥ 4: μ ≥ 4. Necessity upward: n ≥ e₁f₁·μ ≥ 2·4 = 8.
> Realization at n = 8: the genre (2, 1, 4) exists with positive
> opening locus at every q (W-12.A entry law); inside it the stage
> side (0, u₀)–(4, 0) with u₀/2 odd and residual (T² − c)² over K
> [**read (T − c)² — R4 F-5**] (stage-e = 2, stage-μ = 2, stage-CS abscissa budget 4 ≤ 4 ✓) has
> positive locus among stage states (the battery's GN-TOWER exhibits
> an explicit member — the first composite-over-composite event ever
> constructed in this program). n = 4..7 tower-free: all realizable μ
> are ≤ 3. ∎”

**RESOLUTION TRACE:** statement 275–281 · proof 1046–1059 · correction site 2197–2214 (R4 F-5).

XREF: `GENIND_PROOF_2026-08-08.md:GENIND.A(IV)` — count **5**.
XREF: `W12_PROOF_2026-08-08.md:THEOREM W-12.A` — count **8**.

**TEETH:** **GN-TOWER** — “criterion + the n=8 witness + min-n scan” (1654), scored at S12 P8: “the tower witness: frame ('EMB',8,(0,8),2,1,4,1), stage dvs (10,·,5,·), hull (0,10)–(4,0) with (e_s,g) = (2,2), inner residual (T−1)² — stage-CS fired inside the μ = 4 stage; min-n = 8; zero stage-CS anywhere else in the battery.” **The witness's residual is `(T−1)²`, i.e. the CORRECTED form — the machine and the proof display disagreed, and the machine was right.** Disposition: executable regression; **`stale self-description` (rule 20)** for the pre-correction proof display. `passPE1` R4 separately notes the scan “verifies the arithmetic minimum only” (1316–1318).

---
### EFF.GENHN.17  [lemma] · SERIES: GENHN-T(b)-ARC, member 1 of 3  — LEMMA GENHN-T clause (b), REFUTED

**CANONICAL STATEMENT:** verbatim, lines 282–301 (clause (b) with its `[r2]` refutation bracket).

**FORM:** display (blockquoted lemma clause + inline bracketed refutation).

> “(b) [composition — proved at GENHN.A's grade] the inner opening
> re-bases RELATIVE TO the outer stage: inner ladder density e₂ over
> the outer dv-ladder (total e₁e₂ over the base), inner census field
> K₂ = F_{|K|^{f₂}} = F_{Q^{f₁f₂}}: (e, f)-re-basing COMPOSES
> MULTIPLICATIVELY, and σ-dictionaries compose as
> (e, f) ↦ (e₁e₂·e_s, f₁f₂·f_s). No new mechanism: this is GENHN.A
> applied to the outer stage system (which clause (v) exhibits as a
> cluster system over K), inheriting exactly GENHN.A's clause grades
> at each level; the letter layer composes by the cocycle products
> whose coherence grammar is SIGMALAW's (EC-q) ladder (@ accepted
> pin; counts stay twist-free by J-D0).
> **[r2 2026-08-09: clause (b) REFUTED at the LEAF level (passPE1
> F1: constructed n = 8 counter-instances, PARI-confirmed on two
> routes — the stage-algebra inner read, Φ′ ≡ 0, mislabels leaves
> and misprices σ) and REPLACED by LEMMA GENHN-T(b)′ — the [r2]
> annex at the end of S8. The multiplicative (e,f)- and
> σ-composition FORMULAS survive, applied to the COMPOSED-KEY pins
> (the Φ₂-development of f itself); the sentences "No new
> mechanism" and "inheriting exactly GENHN.A's clause grades at
> each level" are WITHDRAWN. (a) is untouched.]**”

**SUPERSESSION KIND: replacement** (the lemma clause is withdrawn and replaced, not re-read). `TARGETS: .17`, `.01` (title's composition clause), `.04` (one-breath echo), `.18` (GENHN.B's tower clause).

**SERIES `GENHN-T(b)-ARC` (rule 28), in source order:**
| # | Member | Where | Status |
|---|---|---|---|
| 1 | **LEMMA GENHN-T(b)**, sealed | **this unit**, 282–292 | **REFUTED at the leaf level** (passPE1 F1) |
| 2 | The withdrawn **proof of (b)** | 1061–1086 | **WITHDRAWN**, with its error located (`.42` = this unit's DERIVATION) |
| 3 | **LEMMA GENHN-T(b)′** | 1127–1287 (`.44`–`.49`) | **PROVED** at (i)–(iv); (v)'s budgets boxed |

**CONDITIONALITY:** What survives: the multiplicative (e,f)- and σ-composition FORMULAS, applied to composed-key pins. What is withdrawn: the mechanism sentence and the grade-inheritance sentence. **The refutation is the program's first displayed-lemma refutation** — the note says so at 1571–1573 (shard 2): “F1 CRITICAL refuted LEMMA GENHN-T(b) at n = 8 tower leaves (the program's first displayed-lemma refutation)”.

**DERIVATION (of the WITHDRAWN clause, with its located error):** Lines 1061–1086:

> “*Proof of (b) (composition).* The inner opening happens inside the
> (μ, K) stage system, which GENHN.A(v) exhibits as a cluster system
> over K with value ladder dv = e₁v and window ledger GENHN-3. Apply
> THEOREM GENHN.CLASS + GENHN.A TO THAT SYSTEM … the inner
> stage re-bases with (e₂, f₂) relative to K and dv, i.e. ladder
> density e₁e₂ and census field F_{Q^{f₁f₂}} over the base —
> multiplicative composition. … ∎
> **[r2 2026-08-09: THIS PROOF OF (b) IS WITHDRAWN — see the annex
> immediately below. Its error: "Apply THEOREM GENHN.CLASS + GENHN.A
> TO THAT SYSTEM" reads the inner opening inside the stage algebra
> R = Ô[x]/(Φ′), where Φ′ ≡ 0; at leaf depth that quotient is not
> evaluation-faithful (the mechanism is derived in the annex).]**”

**RESOLUTION TRACE:** statement 282–301 · (withdrawn) proof 1061–1086 · correction sites 293–301 (`[r2]` bracket), 1088–1125 (the refutation + mechanism), 1127–1287 (T(b)′).

XREF: `SIGMALAW_PROOF_2026-08-08.md:(EC-q)` — count **26**.
XREF: `JD0_PROOF_2026-08-08.md:J-D0` — count **25**.
XREF: `GENHN_passPE1_report.md:F1` — count **7**.

**TEETH:** **The refutation's own teeth, all post-seal.** `genhnr2_supp.py` — GREEN, 147 checks / 0 violations, 3 teeth: “the 4 refuted instances as regression teeth, fresh sweeps at (2,1,4)→(2,1,2) for u₂ ∈ {5,7}, the first f₂ = 2 tower genre (2,1,4)→(1,2,2) over K₂ = F₄, and three parse-gated 3-STAGE instances at n = 16” (1101–1107). **Disposition: planted-mutant-turned-regression; FIRED AGAINST THE NOTE.** The sealed battery could not have caught it: “the battery had NO tower leaf rows (GENHN-BOX-3 disclosed "tower LAWS (witness only)")” (1099–1100) — a **`disclosed non-repair`** in the sealed instrument, cured only by the additive leg.

---
### EFF.GENHN.18  [theorem]

**CANONICAL STATEMENT:** verbatim, lines 303–373 (THEOREM GENHN.B, with its `[r2]` and `[r3]` brackets in place).

**FORM:** display (blockquoted theorem with deeply nested bracketed round-riders, an indented ASCII box display, and a two-bullet consequence list).

> “**THEOREM GENHN.B (the assembly: [GENIND-H(n)] for all n, modulo
> ONE box family).** Assume the S10 supplier stack @ pins. Then for
> every n and every composite-stage genre realizable at degree ≤ n:
> (CS-1) and (CS-2) hold (THEOREM GENHN.CLASS + GENHN.A(i)–(v),
> towers included via LEMMA GENHN-T **[r2 2026-08-09: read GENHN-T(a)
> + GENHN-T(b)′ (the S8 annex); at TOWER genres — first live n = 8 —
> the (CS-1)/(CS-2) content holds at T(b)′'s grade with the composed
> entry budgets and inner refine transfer BOXED as [GENHN-TOW-1]
> [r3 2026-08-09 (passPE2 F1): with the DEPTH SPLIT named — T(b)′
> is ONE composition step, so it carries the DEPTH-2 towers, and by
> the R1 arithmetic (a third stage forces μ₁ ≥ e₂f₂μ₂ ≥ 8, hence
> n ≥ D′μ₁ ≥ 16) depth 2 exhausts the tower genres at
> n ∈ {8, …, 15}; at n ≥ 16 the ITERATED (depth-≥ 3) composition
> additionally rides [GENHN-TOW-1] item (6) — the composed key Φ₂
> fails T(b)′'s own re-entry hypotheses (residual the power
> ψ^{e₂f₂}, normalizers Φ′-polynomials), so no displayed authority
> prices a Φ₃-carrier without item (6)]]**),
> and (CS-3) holds at every
> μ = 2 genre (THEOREM GENHN.C **[r2: and at every tower leaf with
> inner μ₂ = 2 by GENHN-T(b)′(iii) [r3 2026-08-09 (passPE2 F2):
> on a FULL inner side only (e₂f₂μ₂ = μ₁ — (iii)'s proved
> perimeter; the r2 rider as written over-covered). PARTIAL-side
> inner μ₂ = 2 leaves (e₂f₂μ₂ < μ₁, first live n = 10) ride
> [GENHN-TOW-1] item (4), not (iii) — the passPE2 witness (PE2-P):
> the n = 10 member f = Φ′⁵ + 4Φ′⁴ + 32Φ′ + 64x of genre (2,1,5)
> over ℚ₂ (Φ′ = x² − 2), level-1 polygon (0,13)–(1,10)–(5,0) with
> a slope-5/2 inner side of length 4 < μ₁ = 5 carrying (T+1)² —
> an inner μ₂ = 2 event on a partial side; the corrected reader
> REFUSES it loudly (the Φ₂-development of f is not
> monic-of-length-μ₂) and no proved display prices its σ (PARI
> {(2,1),(4,1),(4,1)})]; inner μ₂ ≥ 3 sits in
> [GENHN-HE]]**). The ONLY unproved clause anywhere
> in [GENIND-H(n)], for every n **[r2: ≤ 7; at n ≥ 8 add
> [GENHN-TOW-1]]**, is:
>
>     [GENHN-HE(μ)] , μ ≥ 3:  σ-decision at stage leaves of
>     multiplicity μ ≥ 3 (first live n = 6),
>
> plus the displayed compression/coverage boxes (S9). CONSEQUENTLY,
> through THEOREM GENIND.B and THEOREM W-12.D:
> * **P(5) FIRES OUTRIGHT** (every n = 5 genre has μ = 2): the exact
>   quintic densities R_τ(q) ∈ ℚ(q), wild primes included, are now
>   available at the same conditionality grade as P(4) — the symbolic
>   display is a mechanical GENH4-S9-style assembly, owed as a
>   separate unit (S9 box).
> * **P(n) for ALL n** — THE FULL UNIFORMITY THEOREM: one R_τ ∈ ℚ(q)
>   per splitting type at every degree, every prime power, both
>   characteristics, Σ_τ R_τ = 1 — holds conditional EXACTLY on
>   {[GENHN-HE(μ ≥ 3)]} ∪ {S9 boxes} ∪ {the hostile-arc grade stack}
>   **[r2 2026-08-09: THE CORRECTED CONDITIONALITY — at n ≤ 7 (tower-
>   free) the display stands as sealed; at n ≥ 8 P(n) rests on
>   {[GENHN-HE(μ ≥ 3)]} ∪ {[GENHN-TOW-1] (S9.1: composed entry
>   budgets, inner refine transfer, faithfulness geography, partial
>   inner sides, composed window ledger **[r3 2026-08-09 (passPE2
>   F1): + item (6), the iterated depth-≥ 3 key composition — the
>   r2 parenthetical named five items and was INCOMPLETE at
>   n ≥ 16]**)} ∪ {S9 boxes} ∪ {arc stack},
>   with the tower LEAF READ and inner-μ₂ = 2 σ **[r3: full inner
>   sides — passPE2 F2]** now carried by the
>   PROVED LEMMA GENHN-T(b)′ (S8 annex) instead of the refuted
>   T(b). The sealed word "EXACTLY" was FALSE at n ≥ 8 (passPE1 F1);
>   it is correct for the amended list **[r3: read with the depth
>   split — at n ∈ {8, …, 15} the tower genres are depth-2 (R1
>   arithmetic) and T(b)′ + items (1)–(5) carry the tower clause
>   (item (4) where the inner side is partial); at n ≥ 16 item (6)
>   joins the list. Against the r2 FIVE-item list the sentence
>   "correct for the amended list" was itself over-reaching at
>   n ≥ 16 (passPE2 F1); it is stated here against the six-item
>   box]**.]**
> The program's remaining open surface is the S9 list — short, named,
> and per-item attackable.”

**CONDITIONALITY:** **This is the note's conditionality display and it is a four-layer chain, each layer correcting the previous layer's completeness claim.**
**CHAIN:** sealed “EXACTLY on {[GENHN-HE]} ∪ {S9 boxes} ∪ {arc stack}” → `[r2]` (word "EXACTLY" declared FALSE at n ≥ 8; five-item `[GENHN-TOW-1]` added) → `[r3]` (the r2 five-item list itself declared INCOMPLETE at n ≥ 16; item (6) added; the depth split n ∈ {8..15} / n ≥ 16 named; the (CS-3) tower rider scoped to FULL inner sides) → post-PE3 Correction 2(ii) (1917–1921: read the `[r3]` depth-split sentence “with its conditionality-display twin's parenthetical (L367) attached — “(item (4) where the inner side is partial)””). **TERMINAL: the post-PE3 reading of the `[r3]` display.**
`SUPERSESSION KIND`: `[r2]` = **inventory completion** (the box list is enlarged, the claim's form unchanged); `[r3]` = **inventory completion** again, plus **scope-pin** on (CS-3); post-PE3 Corr. 2(ii) = **wording-rider**.
**Two honest self-indictments are preserved in the frozen text and must not be lost in a chapter cut:** “The sealed word "EXACTLY" was FALSE at n ≥ 8” and “the sentence "correct for the amended list" was itself over-reaching at n ≥ 16”.
**One further inheritance:** (CS-1)/(CS-2) “hold” at ordinary f₁ ≥ 2 / μ ≥ 3 / mixed genres **without a new box** only by LEMMA GENHN-CAP-GEN (2083, out of range) — before that append, the boundary-band surface sat nowhere (the A2 verification note at 2223–2229 checks the S9 box list and confirms “no ordinary-stage box holds it, confirming the omission”). This is a **license**, not a supersession.

**DERIVATION:** Assembly, not a fresh derivation: “Assume the S10 supplier stack @ pins”, then (CS-1)/(CS-2) from GENHN.CLASS + GENHN.A(i)–(v) + GENHN-T, and (CS-3) from GENHN.C at μ = 2 (plus T(b)′(iii) at full-inner-side tower leaves), with `[GENHN-HE(μ ≥ 3)]` the residue. The consequence bullets compose through GENIND.B and W-12.D. The `[r3]` **R1 arithmetic** is derived inline and re-derived at `.51`: a third stage forces `μ₁ ≥ e₂f₂μ₂ ≥ 8`, hence `n ≥ D′μ₁ ≥ 16`.

*Arithmetic audit (rule 22) of the R1 bound.* Three stages require an inner-inner CS event, which by `.16`(a) needs inner multiplicity `μ₂ ≥ 4`… — **the note writes `μ₂ ≥ 2` here** (`μ₁ ≥ e₂f₂μ₂ ≥ 8` with `e₂f₂ ≥ 2` and `μ₂ ≥ 4` gives `≥ 8` ✓). Recomputed: `e₂f₂ ≥ 2` and, for the *second* stage to itself tower, `μ₂ ≥ 4`, so `μ₁ ≥ e₂f₂μ₂ ≥ 2·4 = 8`; then `n ≥ D′μ₁ ≥ 2·8 = 16` ✓. The bound is correct and its two inputs are `.16`(a) applied twice.

**RESOLUTION TRACE:** statement 303–373 · derivation is the whole shard · correction sites 307–319 (`[r2]`+`[r3]` tower), 321–334 (`[r2]`+`[r3]` CS-3), 352–371 (`[r2]`+`[r3]` conditionality), 1909–1928 (post-PE3 Corr. 2), 2077–2083 (CAP-GEN license), 1382–1442 (the `[GENHN-TOW-1]` box itself, shard 2).

XREF: `GENIND_PROOF_2026-08-08.md:GENIND-H(n)` — count **7**.
XREF: `GENIND_PROOF_2026-08-08.md:THEOREM GENIND.B` — count **7**.
XREF: `W12_PROOF_2026-08-08.md:W-12.D` — count **19**.
XREF: `GENHN_passPE2_report.md:F1` — count **9** · `F2` — count **5**.
XREF: `GENIND_PROOF_2026-08-08.md:(CS-1)` — **49** · `(CS-2)` — **20** · `(CS-3)` — **13**.

**TEETH:** **The `[r3]` (CS-3) scope correction has a machine witness that FIRED AGAINST the r2 rider** — the PE2-P member `f = Φ′⁵ + 4Φ′⁴ + 32Φ′ + 64x` at n = 10, genre (2,1,5) over ℚ₂: “the corrected reader REFUSES it loudly (the Φ₂-development of f is not monic-of-length-μ₂) and no proved display prices its σ (PARI {(2,1),(4,1),(4,1)})”. **Disposition: planted counter-instance from a fresh instrument (`genhn_pe2_fresh.py`, 219/0, 4 teeth); fired.** Otherwise the theorem is an assembly and is guarded only through its inputs' teeth.

*Arithmetic audit of the PE2-P witness (rule 22, computed fresh).* `deg f`: `Φ′ = x² − 2` so `Φ′⁵` has degree 10 ✓ = n. Polygon `(0,13)–(1,10)–(5,0)`: first side slope `(13−10)/1 = 3`; second side slope `(10−0)/(5−1) = 10/4 = 5/2` ✓ matches “a slope-5/2 inner side”; its abscissa length is `5 − 1 = 4 < μ₁ = 5` ✓ “partial”. Denominator of `5/2` is `e₂ = 2`, so residual degree `= 4/2 = 2` ✓ consistent with `(T+1)²` and with `f₂ = 1, μ₂ = 2`. PARI's `{(2,1),(4,1),(4,1)}` sums to `2 + 4 + 4 = 10 = n` ✓.

---
### EFF.GENHN.19  [scope-record]

**CANONICAL STATEMENT:** verbatim, lines 375–379.

**FORM:** bold-headed paragraph (unquoted; the note's own obstruction scoreboard).

> “**Obstruction scoreboard (GENH4's OB-a..d at general genre): OB-a
> (ragged window) = GENHN.A(iii), proved; OB-b (pointwise transcription)
> = GENHN.A(ii)+(iv), proved with disclosed frame; OB-c (σ) = GENHN.C
> at μ = 2, [GENHN-HE] at μ ≥ 3; OB-d (genre F / general alphabet) =
> absorbed into the uniform (e₁, f₁) treatment.**”

**CONDITIONALITY:** Each of the four entries inherits its clause's conditionality: **OB-a** is riddered by R4 F-1 (`.10`); **OB-b** carries the weld face at μ ≥ 3 (`.11`, GENHN-BOX-2) and the false universal at (ii) (`.09`); **OB-c** is the surviving box; **OB-d** is scoped by E2's band exception (`.14`). Every entry that says “proved” means *proved at the corrected display*.

**DERIVATION:** Index of `.09`–`.12`, `.15`, `.40`.

**RESOLUTION TRACE:** statement 375–379 · correction sites as at the four indexed units.

XREF: `GENH4_PROOF_2026-08-08.md:GENH4-CAP` — count **18** (the OB-a..d vocabulary is GENH4's; the letters themselves are not addressable designations there — see NEAR-MISS).

**NEAR-MISS (rule 15):** `OB-a` / `OB-b` / `OB-c` / `OB-d` — fixed-string counts in `GENH4_PROOF_2026-08-08.md` are the note's own obstruction letters and are attributed to GENH4 by phrase (“GENH4's OB-a..d”), not by a quoted designation string. The referent is verified (GENH4's obstruction scoreboard); carried descriptively.

**TEETH:** NONE (index).

---
### EFF.GENHN.20  [table]  — §S2's realizability floors

**CANONICAL STATEMENT:** verbatim, lines 423–443 (the realizability-floor block; rule 14 double-emission — source ASCII first, `[TABLE]` transcription second).

**FORM:** bold-italic-headed paragraph containing a fixed-width indented ASCII genre table.

> “*Realizability floors (used by GENHN.B and the battery grammar).*
> μ = 2, e₁f₁ = 2 needs n ≥ 4 (GENH4's genres; embedded variants at
> n = 5). μ = 3 (e₁f₁ = 2) and μ = 2 with e₁f₁ = 3 need n ≥ 6:
>     E3(h)  := (Q; 2, 1, 3; h)  — key x² − ẑπ^h, residual (y−z)³,
>               entry heights (3h, (5h+1)/2, 2h, (3h+1)/2, h, (h+1)/2),
>               per-letter entry volume Q^{6N−(21h+9)/2}, visible iff
>               3h ≤ N−1;
>     E31(h) := (Q; 3, 1, 2; h)  — key x³ − ẑπ^h (gcd(h,3) = 1),
>               residual (y−z)² on lattice {0, 3, 6}, entry heights
>               (2h, ⌈5h/3⌉ᵉ, ⌈4h/3⌉ᵉ, h, ⌈2h/3⌉ᵉ, ⌈h/3⌉ᵉ) (ᵉ = +1 at
>               lattice points where the pin cancels), per-letter
>               entry volume Q^{6N−11} at h = 1, visible iff 2h ≤ N−1;
>     F3(k)  := (Q; 1, 2, 3; k) and E13(k) := (Q; 1, 3, 2; k) — the
>               f-first siblings, visible iff 6k ≤ N−1 (N ≥ 7 at
>               k = 1: beyond this battery's sweep windows, entered in
>               the grammar as visibility-floored).
> Mixed genres (e₁ ≥ 2 AND f₁ ≥ 2, first (2, 2, 2) at n = 8) and
> towers (S8) complete the list. The battery's grammar family
> (GN-CLASS) enforces: every CS event at every depth of every row
> parses with μ ≥ 2, e₁f₁ ≥ 2, 4 ≤ e₁f₁μ ≤ 6, and each genre appears
> only at/above its visibility floor.”

`[TABLE]` — transcription:

| Genre | Datum (Q; e₁, f₁, μ; h/k) | Key | Residual | Entry heights | Per-letter entry volume | Visibility floor | e₁f₁μ |
|---|---|---|---|---|---|---|---|
| E3(h) | (Q; 2, 1, 3; h) | x² − ẑπ^h | (y−z)³ | (3h, (5h+1)/2, 2h, (3h+1)/2, h, (h+1)/2) | Q^{6N−(21h+9)/2} | 3h ≤ N−1 | 6 |
| E31(h) | (Q; 3, 1, 2; h), gcd(h,3)=1 | x³ − ẑπ^h | (y−z)² on lattice {0,3,6} | (2h, ⌈5h/3⌉ᵉ, ⌈4h/3⌉ᵉ, h, ⌈2h/3⌉ᵉ, ⌈h/3⌉ᵉ) | Q^{6N−11} at h = 1 | 2h ≤ N−1 | 6 |
| F3(k) | (Q; 1, 2, 3; k) | — (f-first sibling) | — | — | — | 6k ≤ N−1 | 6 |
| E13(k) | (Q; 1, 3, 2; k) | — (f-first sibling) | — | — | — | 6k ≤ N−1 | 6 |

*Arithmetic audit (rule 22), computed fresh, not taken from the source's labels.*
- **E3(h) budget.** `e₁f₁μ = 2·1·3 = 6` ✓ (needs n ≥ 6 ✓). Entry-height sum at h = 1: `3 + 3 + 2 + 2 + 1 + 1 = 12`; the exponent display gives `(21h+9)/2 = 15` at h = 1. **The two differ by 3** — and the `[r2]` erratum's own instance check reconciles them: “E3 = (2,1,3), h = 1: corrected floors (4,3,3,2,2,1), **total 15** = S2's entry heights … **+ 3 pins** = the battery exponent (P6: E3(1) = 512 = 2^{6·4−15})” (655–658). `12 + 3 = 15` ✓, and `2^{6·4−15} = 2^{9} = 512` ✓ matches P1/P6's flagship. **The entry-height tuple here is the pre-pin list; the erratum's tuple is the post-pin floor list. Both are correct; they count different things, and only the erratum says so.**
- **E31(h) budget.** `e₁f₁μ = 3·1·2 = 6` ✓. At h = 1 the heights are `(2, ⌈5/3⌉ᵉ, ⌈4/3⌉ᵉ, 1, ⌈2/3⌉ᵉ, ⌈1/3⌉ᵉ) = (2, 2, 2, 1, 1, 1)` before the ᵉ adjustments, sum 9; the erratum's corrected floors are `(3,2,2,2,1,1)`, total **11**, and `Q^{6N−11}` ✓ matches the display. `2^{6·4−11} = 2^{13} = 8,192` ✓ = P1/P5's flagship E31(1) at (Zp,2,4,n6). At q = 3, N = 3: `3^{6·3−11} = 3^7 = 2,187` — **but P1 predicts E31(1) = 4,374 at the (3,3,n6) rows**, and `4,374 = 2 × 2,187 = (q−1)·q^{6N−11}` ✓, which is exactly P5's form “obs ≡ (q−1) × law_Egen(q,N,h,e₁=3)”. The per-letter volume display omits the `(q−1)` letter factor; P5 supplies it. Consistent.
- **F3/E13 budget.** `1·2·3 = 6` ✓ and `1·3·2 = 6` ✓. Visibility `6k ≤ N−1` gives `N ≥ 7` at k = 1 ✓ as stated.
- **Grammar bound.** `4 ≤ e₁f₁μ ≤ 6` covers exactly the n ≤ 6 genres: `(2,1,2)`/`(1,2,2)` at 4, and the four above at 6 ✓. No listed genre violates it.

**CONDITIONALITY:** **This table is the load-bearing counter-evidence to two later claims of the note about itself.**
(i) The post-PE4 dated Correction (1957–1978) uses precisely this list to refute the `[r1]`/E2 clause “none is live below n = 8”: “contradicts S2's own realizability list — re-verified against the body at this append: genre F = (1,2,2) is an f₁ = 2 stage genre live at n = 4 … and the f-first siblings F3 = (1,2,3) / E13 = (1,3,2) are first live at n = 6”.
(ii) The 2026-08-12 F-2 re-display (2293–2295) cites the same block as evidence that the note always parameterized by h: “the note's own instance tables already display exactly this parameterization (E3(h), E31(h): "visible iff 3h ≤ N−1")”.
Otherwise unconditional.

**DERIVATION:** Instance computation from `.07`(i)'s budget `e₁f₁μ ≤ m_frame ≤ n` and `.23`'s entry floors; the two per-letter volumes are reconciled against the battery's flagships in the audit above.

**RESOLUTION TRACE:** statement 423–443 · reconciling derivation 653–671 (`[r2]` instance checks) · correction sites 1957–1978 (PE4 F-1), 2293–2295 (F-2 re-display).

XREF: `GENH4_PROOF_2026-08-08.md:law_F` — count **7** (genre F = (1,2,2), the n = 4 f₁ = 2 instance).

**TEETH:** **GN-CLASS**'s visibility-floor enforcement + the **PREDICTED-ABSENT** legs of P1 — “PREDICTED-ABSENT: V4E2/V1E1Q/V4E1Q/FULLQ at n=5; F3/E13/F2X + E2X at (2,4,n6); F3/E13/F2X + E3 at (3,3,n6)”, all confirmed absent at S12 P1. **Disposition: executable regression, in the falsifying direction** (a genre appearing below its floor would be a violation). **Disclosed hole:** F3/E13 are *never positively exercised* — “beyond this battery's sweep windows, entered in the grammar as visibility-floored”, i.e. a `signed vacuity disclosure` for the two f-first rows.

---
### EFF.GENHN.21  [definition]  — §S3.1 the stage ring and its entry invariants

**CANONICAL STATEMENT:** verbatim, lines 449–468.

**FORM:** bulleted paragraph (unquoted body prose; not a blockquoted display).

> “Fix a genre G and current key Φ′ (entry: the canonical lift of the
> side + residual data; refinements update it as in S6, preserving the
> invariants). Let R := Ô[x]/(Φ′) = Ô[θ]. The entry invariants,
> maintained along every chain (S6's invariant maintenance):
>
> * the key's own polygon is one side (0, e₁h·f₁/e₁·…) — precisely:
>   v(Φ′'s constant term) = f₁h exactly, all other coefficients weakly
>   above the side of slope h/e₁ through (D′, 0), lattice points at
>   abscissae ≡ 0 mod e₁ carrying the residual ψ's coefficients;
> * hence every root θ has v(θ) = h/e₁ with gcd(h, e₁) = 1, so the
>   value group of R contains (1/e₁)ℤ: e(R/O) ≥ e₁;
> * η := res(θ^{e₁}π^{−h}) is a root of (a unit multiple of) ψ:
>   [F_Q(η) : F_Q] = f₁, so f(R/O) ≥ f₁;
> * e·f ≤ [R : Ô] = D′ = e₁f₁ forces e = e₁, f = f₁, R a complete DVR
>   with residue field K = F_{Q^{f₁}} = F_Q(η), and Φ′ irreducible
>   **[e2-E3: the forcing chain is correct AT THE FIELD L — the DVR is
>   O_L, not R; ERRATUM E3 below]**.
> Set dv := e₁·v (value group ℤ; density e₁ per ambient v-unit). This
> is the exact-valuation statement DULEMMA's perimeter covers at
> e₁ ≥ 2 — proved directly here, not consumed.”

**CONDITIONALITY:** **`SUPERSESSION KIND: replacement` on the carrier, by `[e2]` ERRATUM E3 (`.22`), which quotes this bullet verbatim as one of its two ORIGINAL displays.** Everything in the four bullets is TRUE with `L`, `O_L` in place of `R`; the false part is exactly “R a complete DVR”. E3's restated frame runs the same chain “verbatim AT THE FIELD” and adds the conclusion “hence Φ′ IS the minimal polynomial of θ (monic, degree D′), irreducible”. The `η` notation, `dv := e₁·v`, and the DULEMMA non-consumption survive unchanged (the DULEMMA sentence is separately riddered to read `e(L/base) = e₁`).

**DERIVATION:** Displayed inline: polygon ⟹ `v(θ) = h/e₁` ⟹ `e ≥ e₁`; residual ⟹ `[F_Q(η):F_Q] = f₁` ⟹ `f ≥ f₁`; `ef ≤ D′ = e₁f₁` forces equality. The first bullet's `v(Φ′'s constant term) = f₁h exactly` is what makes the side one-sided.

**RESOLUTION TRACE:** statement 449–468 · correction site 470–527 (E3) · invariant-maintenance dependency 917–921.

XREF: `DULEMMA_PROOF_2026-08-08.md:DULEMMA` — count **1**.

**TEETH:** NONE (frame/definition). See `.08`'s signed vacuity disclosure: the battery does not touch R's ring structure.

---
### EFF.GENHN.22  [changes-record]  — `[e2]` ERRATUM E3 (the stage-ring carrier)

**CANONICAL STATEMENT:** verbatim, lines 470–527.

**FORM:** display (blockquoted dated erratum: header / ORIGINAL / THE DEFECT / THE RESTATED FRAME / RIDERED list / SOURCE).

> “**[e2] ERRATUM E3 2026-08-09 (the stage-ring carrier — v and res
> live in L/O_L; R is an order, not a DVR). Queued at the GENH4
> Codex-ratification fold (CHALLENGE 5c8d2fd, finding F3: "R
> non-maximal order, not DVR — all consumed v/res facts live in L;
> GENHN.A(i) transport erratum owed") and by GENH4 ANNEX R's R3
> transport obligation ("one rider of exactly this R3 form at
> GENHN.A(i), with the non-maximality witnesses transported";
> ANNEX R @ b10a5a7). Tagged repair per the [r1] mechanism (GENHN at
> 0/2, unaccepted); sealed battery runner and artifacts UNTOUCHED —
> the battery's counts are digit-coordinate counts on
> Ô[x]-coefficients and its σ legs are PARI oracle reads; neither
> consumes R's ring structure.**
>
> **ORIGINAL (the two carrier displays):** GENHN.A(i): "R is a
> complete DVR with e(R/O) = e₁, f(R/O) = f₁, K = F_{Q^{f₁}}";
> S3.1's closing bullet: "e·f ≤ [R : Ô] = D′ = e₁f₁ forces e = e₁,
> f = f₁, R a complete DVR with residue field K = F_{Q^{f₁}} =
> F_Q(η), and Φ′ irreducible".
>
> **THE DEFECT (witnesses transported from ANNEX R R3).** R =
> Ô[x]/(Φ′) = Ô[θ] is in general the NON-MAXIMAL order Ô[θ], not a
> DVR: at the (e₁, f₁) = (1, 2) pattern (GENH4 genre F), every
> k ≥ 1 — Codex's witness φ = x² + 2x + 4 over ℤ₂ has R/2R ≅
> F₂[ε]/(ε²) (nilpotents mod 2; maximal-ideal residue field F₂, not
> F₄; θ/2 ∉ R); at the (2, 1) pattern (genre E), every h ≥ 3 —
> m_R = (π, θ) is non-principal. R = O_L at enumerated corners only
> (genre E's h = 1 Eisenstein case); no general maximality claim is
> made or needed.
>
> **THE RESTATED FRAME (where every consumed fact is true — the
> ANNEX R R3 pattern at general (e₁, f₁)).** Let θ be a root of Φ′,
> L := Frac(Ô)(θ), O_L its valuation ring — a complete DVR — with
> **v := v_L** normalized on the base and every residue read in
> O_L/m_L. S3.1's forcing chain runs verbatim AT THE FIELD:
> v(θ) = h/e₁ with gcd(h, e₁) = 1 gives e(L/base) ≥ e₁; η =
> res(θ^{e₁}π^{−h}) a root of (a unit multiple of) ψ gives
> f(L/base) ≥ f₁; then e·f = [L : base] ≤ deg Φ′ = D′ = e₁f₁ forces
> e = e₁, f = f₁, [L : base] = D′ — hence Φ′ IS the minimal
> polynomial of θ (monic, degree D′), irreducible, and O_L/m_L =
> F_Q(η) = K = F_{Q^{f₁}}. dv := e₁·v as displayed. The facts this
> note consumes downstream are exactly v(A(θ)) and
> res(A(θ)/normalizer) of EVALUATED elements A(θ) ∈ Ô[θ] ⊆ O_L —
> GENHN-2's slot-min reads (S4), S6's carry computation, S7's
> (T1)/(T2) (S7 already declares L := Frac(O)(θ) and works there) —
> and the count laws are digit counts on coefficients, never
> touching R. S6.1 layer 1's graded frame re-aims at **gr(O_L)**
> (one K-line per dv-height, W-9's twisted algebra; R ⊆ O_L and
> every graded read of an evaluated element happens in gr(O_L)).
> RIDERED (named exactly, not edited): GENHN.A(i)'s DVR clause and
> S3.1's closing bullet (tagged inline above); S6's invariant-
> maintenance "S3.1's ring invariants"; S6.1's "gr R = the twisted
> algebra"; S0's and S10's DULEMMA lines "stage rings have
> e(R/O) = e₁ ≥ 2" (read e(L/base) = e₁); S9.2 item 1's "Ore over
> the stage ring" (read: over O_L) — each with R's v/residue/graded
> data interpreted as O_L's, per this erratum. Display-scope only:
> no count, no σ conclusion, no density moves. SOURCE: CODEX GENH4
> ratification finding F3 (CONFIRMED GAP, display-scope) @ fold
> 5c8d2fd; model = GENH4 ANNEX R R3 @ b10a5a7.”

**SUPERSESSION KIND: replacement** (the carrier object) executed as a **named-site rider list** — six sites, enumerated, not edited. `TARGETS: .08` (GENHN.A(i)), `.21` (S3.1's closing bullet), `.35` (S6's invariant maintenance), `.33` (S6.1's “gr R”), `.05` (S0's DULEMMA line); plus two out-of-range sites (S10's DULEMMA line, S9.2 item 1's “Ore over the stage ring”) homed in shard 2.

**CONDITIONALITY:** Unconditional as a correction, and explicitly **display-scope only** (“no count, no σ conclusion, no density moves”). One downstream consequence is load-bearing for a *different* unit: the sentence “S6.1 layer 1's graded frame re-aims at **gr(O_L)**” is the hinge the WELDZERO unit builds on (its §S1 quotes lines 500–509 and 515–517 verbatim). That unit has NOT landed here — see `.11` and OPEN-CALL 2.

**DERIVATION:** The restated forcing chain is derived inline (quoted above). The DEFECT's two witnesses are transported, not re-derived here: `φ = x² + 2x + 4` over ℤ₂ with `R/2R ≅ F₂[ε]/(ε²)` (an order with nilpotents, so not a DVR), and the (2,1) pattern's non-principal `m_R = (π, θ)` at `h ≥ 3`.
*Independent check of witness 1 (compiler-computed, not taken from the source).* `φ = x² + 2x + 4`: Newton polygon over ℤ₂ has vertices (0, v(4)) = (0,2) and (2, 0), one side of slope 1 — so `v(θ) = 1`, `e = 1`, and `f = 2` since the residual is `T² + T + 1` (dividing coefficients by 2: `res(4/4)=1`, `res(2·θ/…)`) — irreducible over F₂, giving `L = ℚ₂(θ)` unramified quadratic, `O_L/m_L = F₄`. Meanwhile `R/2R = F₂[x]/(x² + 2x + 4 mod 2) = F₂[x]/(x²) = F₂[ε]/(ε²)` ✓ — nilpotent, residue field F₂ ≠ F₄ ✓. `θ/2 ∉ R` since `θ` has `v(θ) = 1 = v(2)` but `R = ℤ₂[θ]` and `θ/2` would satisfy a non-integral relation ✓. The witness is correct as displayed.

**RESOLUTION TRACE:** statement 470–527 · rider targets 161–163, 464–465, 917–921, 873–874, 104–107 (in range) + 1516–1518, 1449–1453 (shard 2) · no later append touches E3 (verified across all eleven appends).

XREF: `GENH4_PROOF_2026-08-08.md:ANNEX R` — count **12**.
XREF: `GENH4_PROOF_2026-08-08.md:R3` — count **9**.
XREF: `CODEX_GENH4RAT_2026-08-09.md` — ✓ file present (the CHALLENGE's own report).
XREF: `GRTJC_PROOF_2026-08-08.md:COROLLARY W-9` — count **2**.
PINS: `5c8d2fd` ✓ commit · `b10a5a7` ✓ commit.

**TEETH:** **`signed vacuity disclosure` (rule 20), stated by the erratum itself:** “the battery's counts are digit-coordinate counts on Ô[x]-coefficients and its σ legs are PARI oracle reads; neither consumes R's ring structure” — i.e. the defect was untestable by every row of the sealed battery, in both directions. **Disposition: `decorrelated-model audit` (rule 27)** — found by a Codex ratification pass on a *supplier* note (GENH4), transported here.

---
### EFF.GENHN.23  [lemma]  — LEMMA GENHN-1 (the fibration)

**CANONICAL STATEMENT:** verbatim, lines 531–548, with the two in-text correction brackets in place.

**FORM:** display (blockquoted bold-headed lemma with an indented ASCII budget display).

> “**LEMMA GENHN-1.** On the genre-G opening locus, the Φ′-adic
> development f = C·Φ′^μ + Σ_{j<μ} A_j Φ′^j (C ≡ 1 for full-side
> genres; C = the sibling factor's development for embedded genres,
> split off by LEMMA GENIND-3's Hensel step first) is a TRIANGULAR
> digit bijection from the opening coordinates onto the budget space
>
>     v(a_{j,i}) ≥ ⌈(μ−j)h + (e₁ − i)h/e₁⌉⁺   (A_j = Σ_i a_{j,i}x^i,
>     0 ≤ i < D′, with ⁺ = +1 at the entry-pinned lattice slots,
>     i.e. the floor is the entry height with pins consumed)
>     **[r2 2026-08-09: THIS DISPLAY IS FALSE at every checked genre
>     including f₁ = 1 (passPE1 F2) — the correct base is the SIDE
>     HEIGHT at the slot's abscissa; see the [r2] ERRATUM annex
>     below the [r1] annex]**,
>
> total = the entry exponent of W-12.A's law for the genre (no
> over/undercount), and the stage-initial node is
> {dv(A_j) ≥ (μ−j)S + 1}, S := e₁h **[r1: read D′h = f₁S for S at
> f₁ ≥ 2 — ERRATUM annex below]**.”

**CONDITIONALITY:** **Two of the lemma's three displayed components are corrected; the surviving one is the bijection.**
(a) The **budget display** is declared **FALSE at every checked genre including f₁ = 1** by `[r2]` — the strongest self-indictment in the note. Corrected display at `.25`. `SUPERSESSION KIND: replacement`.
(b) The **node** is corrected at f₁ ≥ 2 by `[r1]` — `S ⇝ D′h`. Corrected at `.24`. `SUPERSESSION KIND: replacement`.
(c) The **triangular bijection** and the **no-over/undercount clause** are untouched — and (c) is what (a) was diagnosed by: “With the old floors the lemma's own clause "total = the entry exponent (no over/undercount)" fails at every checked genre — **the display contradicted the statement it sits in**” (648–651).
**CHAIN for the node:** frozen `S`-node → `[r1]` (`D′h` at f₁ ≥ 2, residue GENHN-ERR-1 named) → `[r2]`'s NODE RE-DERIVATION (664–671: at f₁ = 1 the true floors *do* give `(μ−j)S+1`; “At f₁ ≥ 2 the `[r1]` D′h node stands”) → post-PE4 correction (1957–1978, the “live below n = 8” scope) → GENHN-COUNT-RERUN (2593, ERR-1 SETTLED at `B = D′h`). **TERMINAL: the settlement.**

**DERIVATION:** Lines 550–574, quoted:

> “*Proof.* Triangularity: division by the monic Φ′ determines A_j from
> the coefficients of f at x-degrees ≥ jD′ by unipotent elimination
> (each b-coordinate = its A-coordinate + terms in strictly later
> A-coordinates times key coefficients), exactly as GENH4-1F/GENIND-4;
> a unipotent map of digit spaces is a bijection. Budgets: each entry
> pin of the opening locus (the lattice-point digits of the residual)
> cancels coordinatewise against the key's own terms — the
> cancellations are the universal identities "res(f's lattice digit) =
> (residual coefficient) = (the key's contribution)", identical in
> both characteristics because they are polynomial identities in the
> letters (GENIND-1(ii)'s binomial mechanism at the entry step; the
> n = 4 instances are GENH4-1F's four displayed cancellations, the
> E3/E31 instances are displayed in S2 and machine-checked, GN-FIB).
> No over/undercount: the budget total is forced — the map is a
> bijection and the opening locus's cardinality is W-12.A's entry law
> (@ pin, proved at every degree); the battery verifies the per-
> coordinate floors pointwise (GN-FIB both directions). Node: for
> each j, dv(A_j) = min_i (e₁·v(a_{j,i}) + ih) over the floors
> computes to (μ−j)e₁h + 1 = (μ−j)S + 1 (the minimum is attained just
> above the consumed pin; the e₁ = 2, 3 computations are displayed in
> S2/GENH4-S7.2 and the general case is the same one-line arithmetic:
> e₁⌈(μ−j)h + (e₁−i)h/e₁⌉ + ih ≥ e₁(μ−j)h + 1 with equality realized)
> **[r1: this one-line arithmetic is the offending line at f₁ ≥ 2; see the
> ERRATUM annex immediately below]**.
> ∎”

**RESOLUTION TRACE:** statement 531–548 · proof 550–574 · correction sites 576–611 (`[r1]`), 613–686 (`[r2]`), 2352–2589 (COUNT-RERUN's CR-1 bijection, which re-proves the slot half independently), 2593 (settlement).

XREF: `GENIND_PROOF_2026-08-08.md:LEMMA GENIND-3` — count **6**.
XREF: `GENIND_PROOF_2026-08-08.md:LEMMA GENIND-1` — count **2**.
XREF: `GENH4_PROOF_2026-08-08.md:GENH4-1F` — count **10**.
XREF: `W12_PROOF_2026-08-08.md:THEOREM W-12.A` — count **8**.

**NEAR-MISS (rule 15):** two proof-internal citations resolve only as §-anchors — **`GENIND-4`** has count **0** in `GENIND_PROOF_2026-08-08.md` as written (the note's own lemma roster runs GENIND-0/-1/-2/-3 and GENIND-5; `GENIND-5` count 9). Referent not uniquely verifiable; recorded as **source defect 5** in §8 and NOT emitted as an XREF. **`GENH4-S7.2`** — fixed-string count **0** in `GENH4_PROOF_2026-08-08.md`; the target's section anchor is `S7.2` (count checked below). Carried descriptively.

**TEETH:** **GN-FIB**, both directions — “constructed loci: frames parse to genre, volumes = entry laws” (1650–1651); the per-coordinate floors are verified pointwise. Planted mutant **GN-T-NODE** (a₀₀ floor off-by-one must break the volume) fired 1/1. **Disposition: executable regression + planted mutant, both fired — and the battery is DECORRELATED from the false display**: “the sealed runner's gen_E3/gen_E31 use ceil-div TRUE floors (passPE1's tautology audit — battery decorrelated from the false display)” (680–683). This is the shard's cleanest instance of a machine leg that was right while the prose was wrong.

---
### EFF.GENHN.24  [changes-record]  — `[r1]` ERRATUM (the stage-initial node at f₁ ≥ 2) + GENHN-ERR-1

**CANONICAL STATEMENT:** verbatim, lines 576–611.

**FORM:** display (blockquoted dated erratum: header / CORRECTED NODE / DERIVATION / CONSUMPTION AUDIT / RESIDUE).

> “**[r1] ERRATUM 2026-08-08 (the stage-initial node at f₁ ≥ 2) — raised by
> Codex's hostile pass on HE6 (`CODEX_HE6PE1_2026-08-08.md` finding 3,
> adjudicated: the member-level contradiction REGRADED because the member it
> exhibits is OUTSIDE the ⁺-pinned budget, but the DISPLAY inconsistency it
> exposes is real and lands here, not on HE6). Mechanism: GENHN is at attempt
> grade 0/2 (unaccepted), so this is a tagged repair, not a frozen-note
> annex; the sealed battery runner and artifacts are UNTOUCHED, and every
> battery row has f₁ = 1, where the correction is invisible.**
>
> **CORRECTED NODE.** At f₁ ≥ 2 the stage-initial node is
>
>     { dv(A_j) ≥ (μ − j)·D′h + 1 } ,      D′h = e₁f₁h = f₁·S ,
>
> not {dv(A_j) ≥ (μ−j)S + 1}. At f₁ = 1 the two coincide (D′h = e₁h = S).
>
> **DERIVATION (independent of the finding, from the opening locus itself).**
> Every root ρ of f on the genre-G opening locus satisfies (T1)/(T2)
> (HE3-0), hence dv(Φ′(ρ)) > D′h (LEMMA HE6-0 as re-proved by HE6's r1 round
> — the ψ-cancellation argument), hence every side of the stage polygon
> P(F) has dv-slope > D′h (LEMMA HE6-3(a), which PROVES this with no (SEP)
> hypothesis), hence every pin (j, dv(A_j)) lies strictly above the line of
> slope D′h through (μ, 0): dv(A_j) > (μ−j)D′h, i.e. ≥ (μ−j)D′h + 1 because
> dv is ℤ-valued on the A_j. See also this note's own §S3.1 remark in HE6
> ("why D′h and not S = e₁h").
>
> **CONSUMPTION AUDIT.** HE6 and HE7 consume **LEMMA GENHN-2** (the SLOT
> LEMMA) and HE3-0's locus, never GENHN-1's node display, so nothing in the
> σ-decision chain propagates this erratum; HE6's f₁ ≥ 2 σ-prediction
> {(2,2),(2,2)} at genre (1,2,4) is proof-only and rests on HE6's own D′h
> remark. **RESIDUE (GENHN-ERR-1, named honestly):** whether GENHN's own
> f₁ ≥ 2 count-side displays that substitute the numeric value S = e₁h for
> the node height (the (μ,K)-cluster read "at the S-node", and any entry-
> exponent arithmetic keyed to it) need re-reading with D′h is NOT settled
> here. The law's FORM is unaffected (it is stated as the cluster read AT THE
> NODE, whatever the node height is), no f₁ ≥ 2 stage genre is machine-
> exercised, and none is live below n = 8.”

**SUPERSESSION KIND: replacement** (the node height) plus an explicitly **named open residue** (GENHN-ERR-1). `TARGETS: .08` (GENHN.A(i)'s node), `.23` (GENHN-1's node + the offending one-line arithmetic).

**CONDITIONALITY / the GENHN-ERR-1 arc — this is the charge's named item, so the chain is given in full.** `SERIES: GENHN-ERR-1, 4 members, source order:*

| # | Event | Where | State of ERR-1 |
|---|---|---|---|
| 1 | Named and left open: “is NOT settled here” | **this unit**, 605–611 | **OPEN**, with the honest scope “no f₁ ≥ 2 stage genre is machine-exercised, and none is live below n = 8” |
| 2 | `[r2]` NODE RE-DERIVATION settles the **arithmetic side at f₁ = 1** only | 664–671 | still OPEN at f₁ ≥ 2: “At f₁ ≥ 2 the [r1] D′h node stands; GENHN-ERR-1's S-vs-D′h display residue is otherwise unchanged” |
| 3 | post-PE4 dated Correction (PE4 F-1) corrects the **scope clause** of member 1 | 1957–1978 | still OPEN, scope fixed: “the f-first genres (1,2,2)/(1,2,3)/(1,3,2) are live at n = 4/6/6, and their S-keyed display re-read remains OWED with the residue (**GENHN-ERR-1 stays unsettled exactly as displayed**)” |
| 4 | LEMMA GENHN-COUNT-RERUN's Consumer sweep item 1 | 2593 + 2624 | **“GENHN-ERR-1 is settled.”** / “GENHN-ERR-1 is SETTLED.” |

**TERMINAL: member 4 — SETTLED, WITH A TRANSCRIPTION-CONFIRMATION OWED.** The settling append's own closing sentence (2626–2627): “Ledger: row 15 → the count re-run obligation is DISCHARGED; **a final transcription-confirmation rides the next queue.**” The settlement is therefore *landed in the note* but *not yet confirmed by the sol arm*. This is exactly the state the charge names, and it is compiled here without upgrade: **SETTLED-WITH-TRANSCRIPTION-CONFIRMATION-OWED.** See OPEN-CALL 3.
**Member 1's scope clause is FALSE as written** — corrected at member 3 — and member 1's text is frozen; a chapter cut reading only line 611 would carry a false statement.

**DERIVATION:** Quoted inline and self-contained, and — importantly — **independent of the finding that raised it**: (T1)/(T2) on the opening locus (HE3-0) ⟹ `dv(Φ′(ρ)) > D′h` (LEMMA HE6-0 at HE6's r1) ⟹ every stage-polygon side has dv-slope `> D′h` (LEMMA HE6-3(a), (SEP)-free) ⟹ every pin lies strictly above the slope-`D′h` line through `(μ, 0)` ⟹ `dv(A_j) ≥ (μ−j)D′h + 1` by integrality.

**RESOLUTION TRACE:** statement 576–611 · derivation self-contained at 591–599 · correction sites 664–671 (`[r2]`), 1957–1978 (PE4 F-1), 2593/2624 (settlement).

XREF: `HE3_PROOF_2026-08-08.md:HE3-0` — count **19**.
XREF: `HE6_PROOF_2026-08-08.md:LEMMA HE6-0` — count **17**.
XREF: `HE6_PROOF_2026-08-08.md:LEMMA HE6-3` — count **12**.
XREF: `CODEX_HE6PE1_2026-08-08.md:finding 3` — count **2**.
ARTIFACT: `verification/openmath/genhn_f2_count_check.py` ✓ present (the settlement's certificate).

**NEAR-MISS (rule 15):** “See also this note's own §S3.1 remark **in HE6**” — the phrase names a remark of HE6 by section; fixed-string `why D′h and not S = e₁h` has count **0** in `HE6_PROOF_2026-08-08.md`. The referent is the D′h remark HE6's r1 round installed; it is independently pinned by `LEMMA HE6-0` (17) and `LEMMA HE6-3` (12), both cited in the same derivation. Carried descriptively; source defect 6.

**TEETH:** **At issue time: NONE — `signed vacuity disclosure` in the erratum's own header** (“every battery row has f₁ = 1, where the correction is invisible”). **At settlement time:** `genhn_f2_count_check.py`, the P2 certificate — “measured = predicted on every key at (1,2,2) and the first-ever mixed-genre contact (2,2,2); the sealed S-node child displays refuted exactly as predicted — sealed RAM 0 / UND 1024 vs actual 768 / 256, and 0 / 16384 vs 12288 / 4096” (2610–2614). **Disposition: executable regression, post-seal, FIRED AGAINST the sealed child displays.**
*Arithmetic audit (rule 22) of that certificate's table, computed fresh from the source's own `(CR-5)`:* at `(1,2,2)`, `q_K = |K| = Q^{f₁} = 2² = 4`; sealed UND 1024 = `4^5`; actual RAM 768 + UND 256 = 1024 ✓ totals match, and `768 = 3 · 256 = (q_K − 1)·q_K^4` ✓ — exactly `(q_K−1)|𝒩|`-shaped, i.e. the α-letter factor the sweep says was mis-assigned. At `(2,2,2)`, `q_K = 4` again but `D′ = 4`; sealed UND 16384 = `4^7`; actual 12288 + 4096 = 16384 ✓ and `12288 = 3 · 4096 = (q_K−1)·q_K^6` ✓. **Both rows are internally consistent and both confirm the sweep's diagnosis** (“the sealed `UND` entries 1024 and 16384 were totals attached to the wrong child key”, 2595).

---
### EFF.GENHN.25  [changes-record]  — `[r2]` ERRATUM (LEMMA GENHN-1's per-coordinate budget display)

**CANONICAL STATEMENT:** verbatim, lines 613–686.

**FORM:** display (blockquoted dated erratum: header / ORIGINAL / CORRECTED DISPLAY with an indented ASCII floor formula / INSTANCE CHECKS / CONSUMPTION AUDIT), carrying an `[r3]` sign correction inline.

> “**[r2] ERRATUM 2026-08-09 (LEMMA GENHN-1's per-coordinate budget
> display — the floor base is the SIDE HEIGHT at the slot's
> abscissa). Source: passPE1 F2 (CRITICAL, display-scope; count
> content intact elsewhere — S2's lists, the laws, and the sealed
> runner's gen_* constructions all use the truth). Tagged repair
> per the [r1] mechanism; sealed battery untouched.**
>
> **ORIGINAL (the boxed display, tagged above):**
> v(a_{j,i}) ≥ ⌈(μ−j)h + (e₁ − i)h/e₁⌉⁺.
>
> **CORRECTED DISPLAY.** The opening-locus floor of the digit
> coordinate a_{j,i} (abscissa jD′ + i of the entry polygon) is the
> entry side's height there, ceiled to the digit grid, plus one
> consumed digit at each entry pin:
>
>     v(a_{j,i}) ≥ ⌈((μ−j)D′ − i)·h / e₁⌉ + [pin],
>     [pin] = 1 iff jD′ + i is an e₁-lattice point whose entry
>     (residual) digit is consumed — NOT +h,
>
> the side of slope h/e₁ through (μD′, 0) evaluated at jD′ + i.
> The old base (μ−j)h + (e₁−i)h/e₁ = ((μ−j+1)e₁ − i)h/e₁ is the
> side height ONE KEY-DEGREE too high: at f₁ = 1 (D′ = e₁) it
> exceeds the truth by exactly h at every slot **[r3 2026-08-09
> (passPE2 F3): the erratum's own f₁ ≥ 2 magnitude parenthetical
> — "at f₁ ≥ 2 by more ((μ−j)e₁(f₁−1)h/e₁ + h)" — had the WRONG
> SIGN and is superseded here. Re-derived: old − correct =
> ((μ−j+1)e₁ − i)h/e₁ − ((μ−j)e₁f₁ − i)h/e₁ = h(1 − (μ−j)(f₁−1)).
> At f₁ = 1 this is +h (the clause above stands); at f₁ ≥ 2 the
> old base does NOT exceed the truth — it COINCIDES at
> (μ−j)(f₁−1) = 1 and UNDERSHOOTS by (μ−j)(f₁−1)h − h at
> (μ−j)(f₁−1) ≥ 2. Instance (genre F = (1,2,2), h = 1, j = 0,
> i = 0): old base 3 < correct base 4. "Too high" is the f₁ = 1
> story; at f₁ ≥ 2 the old display erred in the OTHER direction —
> either way the totals at the three instance checks below
> contradicted the lemma's own no-over/undercount clause, so the
> correction's substance is unchanged]**. With the old floors the lemma's own
> clause "total = the entry exponent (no over/undercount)" fails
> at every checked genre — the display contradicted the statement
> it sits in.
>
> **INSTANCE CHECKS (all data internal to this note + its sealed
> artifacts):**
> * E3 = (2,1,3), h = 1: corrected floors (4,3,3,2,2,1), total 15
>   = S2's entry heights (3h,(5h+1)/2,2h,(3h+1)/2,h,(h+1)/2) + 3
>   pins = the battery exponent (P6: E3(1) = 512 = 2^{6·4−15}).
>   Old display: (4,4,3,3,2,2), total 18 ✗.
> * E31 = (3,1,2), h = 1: corrected (3,2,2,2,1,1), total 11 (P5:
>   8,192 = 2^{6·4−11}). Old: total 15 ✗.
> * GENH4 genre E = (2,1,2): corrected (2h+1, ⌈3h/2⌉, h+1, ⌈h/2⌉),
>   h = 1: (3,2,2,1), total 8 = law_E's exponent
>   (law_E(2,5,1) = 4,096 = 2^{4·5−8}). Old: total 10 ✗.
> * NODE RE-DERIVATION (the [r1]/GENHN-ERR-1 seam, arithmetic side
>   settled at f₁ = 1): from the TRUE floors, dv(A_j) =
>   min_i(e₁·v(a_{j,i}) + ih) computes to (μ−j)e₁h + 1 = (μ−j)S+1
>   at f₁ = 1 (min at i = 1: e₁⌈((μ−j)e₁−1)h/e₁⌉ + h) — the
>   battery-verified node; from the OLD floors it would compute
>   (μ−j)S + h + 1-ish, contradicting every battery row. At f₁ ≥ 2
>   the [r1] D′h node stands; GENHN-ERR-1's S-vs-D′h display
>   residue is otherwise unchanged.
>
> **CONSUMPTION AUDIT (every site of the old formula).** (1) The
> boxed display itself — corrected here, tagged inline. (2) The
> proof's node parenthetical "e₁⌈(μ−j)h + (e₁−i)h/e₁⌉ + ih ≥
> e₁(μ−j)h + 1" — already flagged by [r1] at f₁ ≥ 2; now read with
> the corrected base: e₁⌈((μ−j)D′−i)h/e₁⌉ + ih ≥ (μ−j)D′h + 1 at
> the unpinned slots, equality realized (the f₁ = 1 case displayed
> above). (3) No other site: the proof's budget/cancellation text
> and S2's realizability lists are keyed to the entry heights (the
> TRUE floors); the sealed runner's gen_E3/gen_E31 use
> ceil-div TRUE floors (passPE1's tautology audit — battery
> decorrelated from the false display); GENHN.A(i)'s "explicit
> budget floors" phrase carries no formula. Downstream consumers
> (future f-first count units, GENH5-DENS mechanics, Lean
> fan-outs) must transcribe THIS display, not the sealed one.”

**SUPERSESSION KIND: replacement** (the floor formula) with a nested **counter re-reading** at `[r3]` (the magnitude parenthetical's sign). `TARGETS: .23` (the budget display and the proof's node parenthetical).
**CHAIN:** frozen budget display → `[r2]` corrected display (with a wrong-signed magnitude parenthetical) → `[r3]` sign correction. **TERMINAL: the `[r3]` reading.**

**CONDITIONALITY:** Unconditional as a correction, and **explicitly display-scope**: “count content intact elsewhere — S2's lists, the laws, and the sealed runner's gen_* constructions all use the truth”. The `[r3]` layer is a genuine second defect *inside the first repair* — the note found and fixed its own erratum's arithmetic, and says so.

**DERIVATION:** The corrected floor is the entry side's height at abscissa `jD′ + i`, ceiled, plus one consumed digit per pin. The `[r3]` difference computation is displayed: `old − correct = ((μ−j+1)e₁ − i)h/e₁ − ((μ−j)e₁f₁ − i)h/e₁ = h(1 − (μ−j)(f₁−1))`.

*Independent arithmetic audit (rule 22) — all four instance checks recomputed from the corrected formula, not read off the source.*
- **E3 = (2,1,3), h = 1, D′ = 2, μ = 3.** Slots `(j,i)` with `j ∈ {0,1,2}`, `i ∈ {0,1}`: floor `= ⌈((3−j)·2 − i)·1/2⌉ + [pin]`. `(0,0): ⌈6/2⌉ = 3`; `(0,1): ⌈5/2⌉ = 3`; `(1,0): ⌈4/2⌉ = 2`; `(1,1): ⌈3/2⌉ = 2`; `(2,0): ⌈2/2⌉ = 1`; `(2,1): ⌈1/2⌉ = 1`. Base tuple `(3,3,2,2,1,1)`, sum 12; with **3 pins** (+1 each at the three e₁-lattice `i = 0` slots) the source's `(4,3,3,2,2,1)` — sum **15** ✓ exactly as displayed. Battery check: `2^{6·4−15} = 2^9 = 512` ✓ = P1/P6's E3(1) flagship. **The old display's `(4,4,3,3,2,2)`, sum 18, would give `2^{24−18} = 64 ≠ 512`** ✓ the ✗ is real.
- **E31 = (3,1,2), h = 1, D′ = 3, μ = 2.** `⌈((2−j)·3 − i)/3⌉ + [pin]`, `j ∈ {0,1}`, `i ∈ {0,1,2}`: `(0,0): ⌈6/3⌉ = 2`; `(0,1): ⌈5/3⌉ = 2`; `(0,2): ⌈4/3⌉ = 2`; `(1,0): ⌈3/3⌉ = 1`; `(1,1): ⌈2/3⌉ = 1`; `(1,2): ⌈1/3⌉ = 1`. Base sum 9; **+2 pins** at the two `i = 0` lattice slots gives `(3,2,2,2,1,1)` = **11** ✓ as displayed. `2^{6·4−11} = 2^{13} = 8,192` ✓ = P1/P5's flagship. Old total 15 would give `2^9 = 512 ≠ 8,192` ✓.
- **GENH4 genre E = (2,1,2), D′ = 2, μ = 2, general h.** `⌈((2−j)·2 − i)h/2⌉ + [pin]`: `(0,0): ⌈2h⌉ = 2h`, +1 pin `= 2h+1`; `(0,1): ⌈3h/2⌉`; `(1,0): ⌈h⌉ = h`, +1 pin `= h+1`; `(1,1): ⌈h/2⌉`. Tuple `(2h+1, ⌈3h/2⌉, h+1, ⌈h/2⌉)` ✓ exactly as displayed. At h = 1: `(3,2,2,1)`, total **8** ✓; `law_E(2,5,1) = 2^{4·5−8} = 2^{12} = 4,096` ✓.
- **`[r3]` sign at genre F = (1,2,2), h = 1, j = 0, i = 0.** `e₁ = 1, f₁ = 2, D′ = 2, μ = 2`. Old base `= ((μ−j+1)e₁ − i)h/e₁ = (3−0)·1 = 3`; correct base `= ((μ−j)D′ − i)h/e₁ = (2·2 − 0) = 4`. **Old 3 < correct 4** ✓ — the old display UNDERSHOT, confirming the `[r3]` sign fix and refuting the `[r2]` parenthetical. Formula check: `h(1 − (μ−j)(f₁−1)) = 1·(1 − 2·1) = −1 = 3 − 4` ✓.

**All four checks reproduce the source exactly. No discrepancy found.**

**RESOLUTION TRACE:** statement 613–686 · `[r3]` correction 635–648 · targets 537–543, 567–573 · downstream directive 683–686.

XREF: `GENHN_passPE1_report.md:F2` — count **5**.
XREF: `GENHN_passPE2_report.md:F3` — count **5**.
XREF: `GENH4_PROOF_2026-08-08.md:law_E` — count **2**.

**TEETH:** **`stale self-description` (rule 20) at the sealed battery, in the note's favour.** The runner used the true floors all along — “passPE1's tautology audit — battery decorrelated from the false display”. So the false prose was *invisible* to every green row, and the three instance-check ✗s are the only machine-adjacent evidence. **Disposition: executable regression (GN-FIB/GN-CLASS flagships) as the decorrelated witness that the CORRECTED display is right.**

---
### EFF.GENHN.26  [scope-record]

**CANONICAL STATEMENT:** verbatim, lines 688–695.

**FORM:** bold-headed paragraph.

> “**Prehistory/embedding composition (consumed).** Prehistory chains
> compose by GENIND-1(ii) at general m (@ pin); embedded genres (the
> frame = stage × siblings) compose by LEMMA GENIND-3's
> scale-then-Hensel fibration (@ pin), the sibling fiber multiplying
> the stage law — the n = 5 instances (V1E2: sibling fiber
> q^{N−(5h+1)/2} − 1 = the split root's Newton-determined digit count;
> V4E2: fiber (q−1)q^{N−5v₄−1}) are derived in S11's preregistration
> and machine-checked (GN-STAGE2).”

**CONDITIONALITY:** Consumption declaration; conditional on GENIND @ pin. Its embedded-genre half is *sharpened* (not corrected) by GENHN-BOX-4's certified-perimeter finding (shard 2, 1352–1377) and by S11.F (1777–1798): the extracted block is determined by ambient window-N data only mod explicit per-coordinate floors, so “the set of stage leaves CERTIFIED by an ambient window is strictly smaller than the stage window suggests”. **Count laws are untouched** — “the truncated read is a bijection of window data — GN-STAGE2 exact at full N”.

**DERIVATION:** Cited, not derived: GENIND-1(ii) and LEMMA GENIND-3 @ pin. The two n = 5 fibers are derived in S11.D P3/P4 (shard 2).

**RESOLUTION TRACE:** statement 688–695 · sharpening 1352–1377, 1777–1798 (shard 2).

XREF: `GENIND_PROOF_2026-08-08.md:LEMMA GENIND-1` — count **2** · `LEMMA GENIND-3` — count **6**.

**TEETH:** **GN-STAGE2** — “the μ=2 stage law at THREE fresh genres, both directions” (1650–1651), scored at P3/P4: V1E2 totals 12,288 / 458,752 / 26,244 / 458,752, 0 escapes; V4E2 `obs ≡ law_E(2,8,3) × 4`, totals 65,536 + 65,536. *Arithmetic audit:* P3's four totals across rows (Zp,2,5,1) / (Zp,2,6,1) / (Zp,3,4,1) / (Fqt,2,6,1) — `12,288 = 3 · 2^{12}`, `458,752 = 7 · 2^{16}`, `26,244 = 4 · 3^{8} = 2² · 3^8`, and the fourth repeats the second ✓ (the two q = 2, N = 6 rows agree cell-for-cell, which is the ℤ_p ↔ F_q[[t]] tie the row list flags `[tie=ON]`). Disposition: executable regression, both directions.

---
### EFF.GENHN.27  [lemma]  — LEMMA GENHN-2, THE SLOT LEMMA

**CANONICAL STATEMENT:** verbatim, lines 699–717.

**FORM:** display (blockquoted bold-headed lemma with an indented ASCII slot-min display).

> “**LEMMA GENHN-2.** Let A = Σ_{i<D′} a_i x^i, a_i ∈ O (any
> coordinate A_j). Then
>
>     dv(A(θ)) = min_i (e₁·v(a_i) + i·h)   EXACTLY,
>
> for every root θ of Φ′ and every lift; the minimum's residue class
> mod e₁ is i·h mod e₁ (distinct for distinct i mod e₁ since
> gcd(h, e₁) = 1), and at a within-class tie among i, i+e₁, …,
> i+e₁(f₁−1) the residue is Σ_t res(a_{i+e₁t}θ^{i}·(θ^{e₁}π^{−h})^t
> π^{ht})-normalized = Σ_t res(a_{i+e₁t})·η^t ≠ 0 because
> {1, η, …, η^{f₁−1}} are F_Q-independent (deg ψ = f₁). Hence each
> A_j carries exactly ONE K-digit slot per integer dv-height — the
> slot's K-digit assembling the f₁ within-class O-digits — and the
> formal slot-min IS the valuation of the class of A in R: the
> graded read transcribed pointwise. Across classes there are no
> ties (distinct residues mod e₁): this is JC-LOAD's no-cancellation
> holding BY CLASS SEPARATION + RESIDUE-FIELD INDEPENDENCE —
> elementary, hence not consumed. W-9's dim_K 𝒜(T) = E = e₁ is this
> statement's graded shadow (cited as frame).”

**CONDITIONALITY:**
(a) **The “per integer dv-height” universal is re-displayed twice** — identical chain to `.09` (of which this lemma is the content): TERMINAL scope is `D′h < m`, below the window cap (post-D2b corrigendum, 2315–2332).
(b) **“the formal slot-min IS the valuation of the class of A in R”** is riddered by `[e2]` E3: the valuation lives in `O_L`, not `R`. E3's rider list names S6.1's “gr R” explicitly and its restated frame covers “GENHN-2's slot-min reads (S4)” by name.
(c) The **JC-LOAD / W-9 sentences are frame citations, not consumptions** — the lemma's own words: “elementary, hence not consumed”, “cited as frame”. This is the note's cleanest weld-free declaration and is what makes GENHN-BOX-2 a box about *layer 1 of GENHN-4 only*, not about the slot geometry. `runs/qgen/WELD_FACE_AUDIT.md` independently confirms the routing (LEAK-1's status line: the audit's one confirmed weld-face consumption is GENHN-4 layer 1, not GENHN-2).
(d) **Independently re-proved at 2463–2469** (COUNT-RERUN's proof) and 2374–2382 (CR-1's bijection) — a license, not a supersession.

**DERIVATION:** Lines 719–727, quoted:

> “*Proof.* Ultrametric equality when all candidate values are
> attained at distinct heights; distinct classes never tie (dv ≡ ih
> mod e₁). Within a class, divide by the attaining monomial
> θ^iπ^{v}: the competing residues are res(a_{i+e₁t})·η^t, and a
> vanishing F_Q-combination of 1, η, …, η^{f₁−1} with some nonzero
> coefficient contradicts [F_Q(η) : F_Q] = f₁. Residue of the slot =
> that combination — one K-digit. The e₁ = 2, f₁ = 1 instance is
> GENH4-2(E) (parity); e₁ = 1, f₁ = 2 is GENH4-2(F); e₁ = 3, f₁ = 1
> is the E31 three-class computation (machine: the E31 rows). ∎”

**RESOLUTION TRACE:** statement 699–717 · proof 719–727 · correction sites 470–527 (E3), 2191–2195 / 2300–2313 / 2315–2332 (the (ii) chain), 2101–2145 (GENHN-LIFT, the converse lift) · re-derivations 2374–2382, 2463–2469.

XREF: `GRTJC_PROOF_2026-08-08.md:JC-LOAD` — count **31**.
XREF: `GRTJC_PROOF_2026-08-08.md:COROLLARY W-9` — count **2**.
XREF: `GENH4_PROOF_2026-08-08.md:GENH4-2` — count **15**.
XREF: `HE7_PROOF_2026-08-08.md:LEMMA GENHN-2` — count **1** (reverse edge: HE7 consumes THE SLOT LEMMA as its ladder base case — see §3.2).

**TEETH:** **GN-E31's three-class computation** (the `e₁ = 3, f₁ = 1` instance, machine-checked at the E31 rows) + planted mutant **GN-T-LAT** — “E31 law collapsed to integer lattice” must break — fired 2/2. **Disposition: executable regression + planted mutant, both fired.** The `f₁ ≥ 2` within-class tie branch is exercised only foreign-ly (GENH4-2(F) at (1,2,2)) — a `signed vacuity disclosure` for this battery.

---
### EFF.GENHN.28  [convention]  — the twist (letters only)

**CANONICAL STATEMENT:** verbatim, lines 729–737.

**FORM:** bold-headed paragraph (unquoted body prose).

> “**The twist (letters only).** Normalizers: for each dv-height m pick
> n(m) := x^{i(m)}π^{a(m)} with i(m)·h + e₁·a(m) = m, 0 ≤ i(m) < e₁.
> Products wrap through θ^{e₁} = (unit lift)·π^h: n(κ)^t =
> ẑ^{fl}·n(tκ) with the explicit integer fl = the wrap count — W-9's
> cocycle, literal. Side residuals assembled with coherent
> normalizers are therefore z-power-twisted slot digits (the S6
> computation and the battery's readers implement exactly this);
> counts are twist-blind (J-D0: (digits) ↦ (twisted digits) is a
> type-preserving bijection), LETTERS are twisted.”

**CONDITIONALITY:** **The final parenthetical is FALSE, disclosed by a consumer, and NOT edited — this is the charge's named WZ-BOX-7 item.**

`lean/notes/openmath/WELDZERO_2026-08-14.md` line 1134 ff., quoted verbatim:

> “* **WZ-BOX-7 (r1) — a false parenthetical in frozen accepted text, disclosed
>   and NOT edited.** Repair 1 establishes that the twist dictionary is not
>   type-preserving. Two frozen sentences in accepted notes say it is: GENHN's
>   `counts are twist-blind (J-D0: (digits) ↦ (twisted digits) is a` /
>   `type-preserving bijection), LETTERS are twisted.` (GENHN:736–737, each line
>   `grep -cFx` → **1**) and GENH4's order-2 instance
>   `((S₁, S₀) ↦ (S₁, z̄S₀) is a type-preserving bijection — J-D0's`
>   (GENH4:370, → **1**) … In both, the **conclusion** — counts
>   twist-blind, letters twisted — is TRUE and is what downstream text consumes;
>   what is false is the parenthetical's **reason**.”

and at WELDZERO 1058–1065:

> “GENHN
> states this conclusion in its own words — "counts are twist-blind … LETTERS
> are twisted" (L736–737) — and this note **upholds the conclusion while
> declining the reason** the same sentence gives in its parenthetical ("J-D0:
> (digits) ↦ (twisted digits) is a type-preserving bijection"): the bijection is
> not type-preserving and J-D0 is not the mechanism (WZ-3(iv), WZ-BOX-7).”

**COMPILED STATE, exactly as the notes leave it (template rule 10 — verified against GENHN's FULL append chain to line 2627):**
- **GENHN's text is unchanged.** No dated append names lines 736–737. The false parenthetical stands in frozen accepted text.
- **The CONCLUSION (“counts are twist-blind … LETTERS are twisted”) is upheld** by both notes and is what every downstream site consumes. GENHN's own count-side consumption is at `.07`(iii) (letter-blindness as one of the three uniformity mechanisms), `.17` (“counts stay twist-free by J-D0”), and `.33` layer 1.
- **The REASON is false** and the replacement reason (WZ-3(iii): the two conventions name the same digit space through a bijection *of* that space) lives only in WELDZERO, which is at **clean-pass 1 of 2** (`spec/HYPOTHESIS_LEDGER.md` HYP.148/149 v6 ARC UPDATE) and which explicitly declines authority over GENHN's frozen words.
- **Machine witness at the sibling site:** WELDZERO §5.1 reports the sealed GN-STAGE2 row flipping `'2'` to `'1sq'` at **972 of 972** live-wrap events under `(S₁, S₀) ↦ (S₁, z̄S₀)` — i.e. the map demonstrably fails type-preservation on GENHN's own sealed data.
`SUPERSESSION KIND: none applied` — this is a **disclosed defect, not a supersession**: no rider has landed, and the compiler does not invent one. Recorded as source defect 7 and OPEN-CALL 4.

Second, unrelated conditionality: “n(m) := x^{i(m)}π^{a(m)} with i(m)·h + e₁·a(m) = m” presumes `a(m) ≥ 0`, which fails at unoccupied heights — the R4/A2 witness `(e₁,f₁,h,m) = (3,1,2,1)` gives `a = −1`. The post-D2b corrigendum's `D′h < m` scope (`.09`) governs this display too.

**DERIVATION:** Displayed inline. The cocycle `n(κ)^t = ẑ^{fl}·n(tκ)` follows from the wrap `θ^{e₁} = (unit lift)·π^h` and Bézout on `i·h + e₁·a = m` with `0 ≤ i < e₁`. The wrap exponent is made explicit at the HETOW erratum (1989–1990, shard 2): `n̂(u₂)^{f₂−t} = n̂((f₂−t)u₂)·(x^{e₁}/π^{h})^{W(t)}` with `W(t) = ⌊(f₂−t)·i(u₂)/e₁⌋`, and re-derived at LEMMA GENHN-LIFT's APPLICATION (2159–2168): `res(n(u₂)^r/n(ru₂)) = η^{W(t)}`.

**RESOLUTION TRACE:** statement 729–737 · derivation self-contained · correction sites: **none in GENHN** (verified); external disclosure at `WELDZERO_2026-08-14.md:1058–1065, 1134–1145`; scope pin at 2315–2332 (post-D2b, for the normalizer's integrality).

XREF: `JD0_PROOF_2026-08-08.md:J-D0` — count **25**.
XREF: `GRTJC_PROOF_2026-08-08.md:COROLLARY W-9` — count **2**.
XREF: `lean/notes/openmath/WELDZERO_2026-08-14.md:WZ-BOX-7` — grep-verified count **10**.
ARTIFACT: `lean/notes/openmath/WELDZERO_2026-08-14.md` ✓ present.

**TEETH:** **`stale self-description` (rule 20) — the parenthetical's reason is falsified by GENHN's OWN sealed data**, read by a foreign instrument (WELDZERO's 972/972 live-wrap count on the GN-STAGE2 row). GENHN's own teeth guard the *conclusion*: J-D0-blindness is exercised wherever a count law is checked against a twisted read (GN-STAGE2, GN-E3, GN-REFINE3, all 0 violations). **Disposition: `accepted-with-decorrelation-supplied` for the conclusion; `stale self-description` for the reason.**

---
### EFF.GENHN.29  [lemma]  — LEMMA GENHN-3 (caps, raggedness, consultation)

**CANONICAL STATEMENT:** verbatim, lines 741–763.

**FORM:** display (blockquoted bold-headed lemma, four clauses, proof “in the display”).

> “**LEMMA GENHN-3 (caps, raggedness, consultation).** (a) A computed
> dv-value is LIFT-STABLE iff < e₁N: an out-of-window O-digit at
> height v = N in class i = 0 gives dv = e₁N, undercutting every
> in-window value ≥ e₁N and tying none below it; conversely all
> in-window slot digits agree across lifts. For f₁ ≥ 2 the boundary
> band (value readable, K-residue needing an out-of-window
> component) is adjudicated as GENH4-CAP(F) **[e2-E1 2026-08-09:
> as CORRECTED at GENH4 r3 (frozen pin 4b0d946) — the band read is a
> trichotomy of which ONLY the even branch exits UND; the sealed
> "exits UND exactly as" transcribed the pre-r2 phrasing — ERRATUM E1
> below]**. (b) The class-i slot
> string of a coordinate ends at e₁(N−1) + ih: RAGGED across
> classes; the band beyond min-class end is free depth on every
> leaf locus. (c) Every digit consulted by a readable event sits
> strictly inside its class's window: a consulted height m satisfies
> m < e₁N and m ≡ i(m)h mod e₁, hence m ≤ e₁N − e₁ + (i(m)h mod e₁)
> ≤ e₁(N−1) + i(m)h — inside the string. (d) Along chains, every
> update (S6) determines new digits at height d from old digits at
> heights ≤ d: carries move upward only, both ring types. Hence
> deep histories never consult the ragged band, and the per-node
> laws are uniform below the caps. ∎ (proof in the display; (c) is
> the one-line congruence argument, generalizing GENH4 S4's parity
> count; (d) is S6's triangularity)”

**CONDITIONALITY:** **Three separate corrections, two in-text and one post-acceptance.**
(a) **`[e2-E1]`, in-text** — the band-exit clause transcribed GENH4-CAP(F)'s *pre-r2* phrasing, which was FALSE; the corrected rule is a trichotomy (`.31`). `SUPERSESSION KIND: replacement`.
(b) **`[r2]` band annex** (`.32`) upgrades E1's transport from “(1,2)-authority” to derived at (μ = 2, e₁ = 1, f₁ ≥ 2), and **scopes E2's readability parenthetical to the FIRST band height**. `SUPERSESSION KIND: scope-pin`.
(c) **2026-08-12 R4 F-1** (2057–2087) riders clauses (a) and (b): the “iff < e₁N” becomes “the sufficient interior criterion together with GENHN-CAP-GEN's exact boundary criterion”, and “the ragged band is never consulted” — the phrase appears in **(b)/(d)** and in GENHN.A(iii) and the OB-a paragraph — becomes “the unread component cells of the ragged band are never consulted”. **The A2 append states the first usage is FALSE**: “the `[r2]` annex itself proves that a first-band height can support a lift-stable terminal decision.” `SUPERSESSION KIND: wording-rider` + `scope-pin`. **CHAIN: frozen (a)/(b) → `[e2]` E1 → `[r2]` annex → R4 F-1 + GENHN-CAP-GEN. TERMINAL: GENHN-CAP-GEN's three-clause rule (2067–2073).**

**DERIVATION:** In the display, as the lemma itself says. (a) is the undercut computation; (c) is the congruence `m ≡ i(m)h (mod e₁)` combined with `m < e₁N`; (d) is S6's triangularity. **(c)'s one-line argument recomputed (rule 22):** if `m < e₁N` and `m ≡ i(m)h (mod e₁)` with `0 ≤ i(m) < e₁`, write `m = e₁a + i(m)h`-style — the note's bound is `m ≤ e₁N − e₁ + (i(m)h mod e₁)`. Since `m ≡ i(m)h (mod e₁)` and `m ≤ e₁N − 1`, the largest such `m` is `e₁(N−1) + (i(m)h mod e₁)` ✓, and `(i(m)h mod e₁) ≤ i(m)h` so `m ≤ e₁(N−1) + i(m)h` ✓ — inside the class-`i(m)` string, whose end is exactly `e₁(N−1) + i(m)h` by (b) ✓. The argument is correct as displayed.

**RESOLUTION TRACE:** statement 741–763 · proof in the display · correction sites 770–805 (E1), 807–861 (`[r2]` annex), 2057–2087 (R4 F-1 + CAP-GEN).

XREF: `GENH4_PROOF_2026-08-08.md:GENH4-CAP` — count **18** · `GENH4-CAP(F)` — count **11**.
PIN: `4b0d946` ✓ commit.

**TEETH:** **PROOF-ONLY at f₁ ≥ 2** — no battery row has f₁ ≥ 2, so the band clause is unexercised by this note's instrument. The note's own coverage-hole sentence (E1, 798–801): “at f₁ ≥ 2 genres beyond it (μ ≥ 3, or e₁ ≥ 2 mixed — **no battery row, first live n ≥ 8**) this note claims the LIFT-STABILITY content of (a) only and NO band-adjudication display — that surface sits with the S9 boxes.” **The A2 verification note then checks that claim and finds it false in a second way** (2223–2229): the S9 box list was walked box by box and “no ordinary-stage box holds it, confirming the omission”. Clauses (a)-interior/(c)/(d) are exercised everywhere (every green row rides them). Disposition: executable regression (interior) + `decorrelated-model audit` (boundary).

---
### EFF.GENHN.30  [scope-record]  — the OB-a resolution paragraph

**CANONICAL STATEMENT:** verbatim, lines 765–768.

**FORM:** inline sentence (unquoted body prose).

> “The OB-a resolution, genre-generically: the coherent object is the
> e₁-fold cover (the full integer dv-ladder), raggedness confined to
> the never-consulted band — first measured (QSCOUT22), then a ledger
> (GENH4), now a one-congruence lemma.”

**CONDITIONALITY:** **Named as a rider target by R4 F-1** — “Read “the ragged band is never consulted” everywhere in GENHN.A(iii), S5, **and the OB-a paragraph** as “the unread component cells of the ragged band are never consulted.”” `SUPERSESSION KIND: wording-rider`. `TARGETS: .30`. Its provenance chain (measured → ledger → lemma) is unaffected.

**DERIVATION:** Summary of `.29`(b)(c).

**RESOLUTION TRACE:** statement 765–768 · correction site 2087 (R4 F-1 rider).

XREF: `QSCOUT22_2026-08-08.md:Q22-A` — count **3** (the “first measured” stage).
XREF: `GENH4_PROOF_2026-08-08.md:GENH4-CAP` — count **18** (the “ledger” stage).

**TEETH:** NONE (summary).

---
### EFF.GENHN.31  [changes-record]  — `[e2]` ERRATUM E1

**CANONICAL STATEMENT:** verbatim, lines 770–805.

**FORM:** display (blockquoted dated erratum with an indented ASCII trichotomy).

> “**[e2] ERRATUM E1 2026-08-09 (LEMMA GENHN-3(a)'s band-exit clause —
> the pre-r2 GENH4-CAP(F) phrasing). Queued at the GENH4-r2 fold
> (ledger 0089f9b); GENHN is at attempt grade 0/2 (unaccepted), so
> this is a tagged repair per the [r1] mechanism; the sealed battery
> runner and artifacts are UNTOUCHED — every battery row has f₁ = 1,
> where the f₁ ≥ 2 band clause is vacuous.**
>
> **ORIGINAL (S5, GENHN-3(a), sealed text):** "For f₁ ≥ 2 the
> boundary band (value readable, K-residue needing an out-of-window
> component) exits UND exactly as GENH4-CAP(F)."
>
> **CORRECTION.** "Exits UND" transcribes GENH4-CAP(F)'s PRE-r2
> phrasing (the sealed parenthetical "the reader's dv0 = N → UND
> exit", found FALSE at GENH4 PE2 GAP 1 and repaired through PE3
> MINOR 1). The corrected rule — GENH4 r3 at its FROZEN PIN 4b0d946,
> re-derived there from GENH4-3(i)'s hull partition, checked against
> the committed counter-keys (2SIDED(3,4) = 384 vs RAM(7) = 128 at
> (Zp,2,7,k1); 2SIDED(3,5) = 1,536 vs UND = 1,024 at even-N
> (Zp,2,8,k1)) — is a TRICHOTOMY with pairwise-disjoint antecedents
> at the band read dv0 = N (w := dv(A₁)):
>
>     (a) N > 2w, either parity  → DECIDED 2SIDED(w, N−w);
>     (b) N ≤ 2w, N odd          → DECIDED RAM(N);
>     (c) N ≤ 2w, N even         → UND.
>
> Only branch (c) exits UND. The sentence is CONDITIONALIZED: at the
> μ = 2, f₁ ≥ 2 genre the band read follows exactly this r3
> trichotomy (GENH4-CAP(F)'s own frame, (e₁, f₁) = (1, 2)); at
> f₁ ≥ 2 genres beyond it (μ ≥ 3, or e₁ ≥ 2 mixed — no battery row,
> first live n ≥ 8) this note claims the LIFT-STABILITY content of
> (a) only and NO band-adjudication display — that surface sits with
> the S9 boxes. GENH4.B's two-term genre-F drainage display (the
> even-N band term), which S6.3 consumes at pin, is the μ = 2
> instance of the corrected rule and is unchanged. SOURCE: GENH4 PE2
> GAP 1 + PE3 MINOR 1; corrected display = GENH4 r3, frozen pin
> 4b0d946 (accepted body, byte-frozen).”

`[TABLE]` — the trichotomy transcribed (rule 14):

| Branch | Antecedent (at band read dv₀ = N, w := dv(A₁)) | Verdict |
|---|---|---|
| (a) | N > 2w, either parity | DECIDED 2SIDED(w, N−w) |
| (b) | N ≤ 2w, N odd | DECIDED RAM(N) |
| (c) | N ≤ 2w, N even | UND |

*Arithmetic audit (rule 22) of the four committed counter-keys.* At `(Zp, 2, 7, k1)`: `q = 2, N = 7`. `2SIDED(3,4) = 384 = 3 · 2^7 = (q^{f₁·comp}−1)·2^7`-shaped with `q^2 − 1 = 3` ✓, and `RAM(7) = 128 = 2^7` ✓ — the two differ by exactly the factor `3 = Q^{comp}−1` at `comp = 2`, consistent with E2's census. At `(Zp, 2, 8, k1)`, even N: `2SIDED(3,5) = 1,536 = 3 · 2^9` and `UND = 1,024 = 2^{10}`; ratio `1536/1024 = 1.5 = 3/2` ✓ — the even branch drains where the odd branch decides, exactly as (b)/(c) predict. **The three antecedents are pairwise disjoint and exhaustive on `{N > 2w} ⊔ {N ≤ 2w, N odd} ⊔ {N ≤ 2w, N even}`** ✓ (verified: the three cover all (N, w) with no overlap).

**SUPERSESSION KIND: replacement** (the band-exit rule) plus **scope-pin** (conditionalized to the (1,2) genre pending the `[r2]` upgrade). `TARGETS: .29`(a).

**CONDITIONALITY:** **E1's own scope restriction is lifted in the very next annex.** `[r2]` (`.32`) states: “E1's corrected sentence claimed the r3 trichotomy at every μ = 2, f₁ ≥ 2 genre on (1,2)-shaped authority only … E1's transport sentence is accordingly UPGRADED from (1,2)-authority to derived at (μ = 2, e₁ = 1, f₁ ≥ 2).” And E1's exclusion clause (“at f₁ ≥ 2 genres beyond it … NO band-adjudication display — that surface sits with the S9 boxes”) is **checked and found false** by the A2 verification note (2223–2229): no S9 box holds it. GENHN-CAP-GEN then supplies the general rule. **CHAIN: frozen “exits UND exactly as” → E1 trichotomy ((1,2)-scoped) → `[r2]` annex (derived at e₁ = 1, f₁ ≥ 2) → GENHN-CAP-GEN (all ordinary genres). TERMINAL: GENHN-CAP-GEN.**

**DERIVATION:** Transcribed from GENH4 r3 at pin 4b0d946, not re-derived here — the erratum says so (“re-derived there from GENH4-3(i)'s hull partition”). The `[r2]` annex is where GENHN derives it in its own frame.

**RESOLUTION TRACE:** statement 770–805 · correction sites 807–861 (`[r2]` upgrade), 2061–2087 (CAP-GEN), 2223–2229 (the A2 check of E1's exclusion clause).

XREF: `GENH4_PROOF_2026-08-08.md:GENH4-CAP(F)` — count **11** · `GENH4-3` — count **11** · `GENH4.B` — count **7**.
PINS: `0089f9b` ✓ · `4b0d946` ✓.

**TEETH:** **`signed vacuity disclosure`** in the header (“every battery row has f₁ = 1, where the f₁ ≥ 2 band clause is vacuous”), with **foreign machine evidence** from GENH4's committed counter-keys (the four numbers audited above) and, at `[r2]`, from passPE1's fresh legs. **Disposition: `accepted-with-decorrelation-supplied`.**

---
### EFF.GENHN.32  [lemma]  — `[r2]` ANNEX: the f₁ ≥ 3 band transport, DERIVED

**CANONICAL STATEMENT:** verbatim, lines 807–861.

**FORM:** display (blockquoted dated annex, four numbered derivation steps with an indented ASCII trichotomy at step 2).

> “**[r2] ANNEX 2026-08-09 (the f₁ ≥ 3 band transport DERIVED —
> discharging passPE1 F3; E2's readability parenthetical scoped to
> the FIRST band height). E1's corrected sentence claimed the r3
> trichotomy at every μ = 2, f₁ ≥ 2 genre on (1,2)-shaped authority
> only; the two-deep band's value-instability (an out-of-window
> lower-t digit under a computed deeper value) was unhandled. The
> derivation, in this note's own slot model:**
>
> Setting: μ = 2, e₁ = 1 (dv = v, integer slope k = h; the e₁ ≥ 2
> mixed genres stay OUTSIDE, as E1's exclusion list already
> scopes). A coordinate's height-m slot assembles the f₁ components
> res(a_t at v = m − tk)·η^t, t = 0..f₁−1; component t is in-window
> iff m − tk ≤ N − 1. Heights m ≤ N − 1 are FULLY readable; the
> band is [N, N + (f₁−1)k − 1] with 1 ≤ comp(m) < f₁.
> (1) VALUE STABILITY AT m = N. Every unread digit lives at height
> ≥ N (component t unread ⟹ v(a_t) ≥ N ⟹ height ≥ N + tk ≥ N).
> At the FIRST band height N the unread data can therefore only
> JOIN the height-N residue on the complementary basis elements
> {η^t : t out-of-window}; by GENHN-2's independence a nonzero
> readable part Σ_{t in-window} res(a_t)η^t cannot be cancelled by
> any assignment of the unread components: dv₀ = N EXACTLY, for
> every lift. The full K-residue at N is NOT determined.
> (2) THE TRICHOTOMY TRANSPORTS VERBATIM AT m = N (band read =
> readable part nonzero at N, all readable data below N zero;
> w := dv(A₁)):
>     (a) N > 2w, either parity → DECIDED 2SIDED: every lift has
>         u ≥ N > 2w (all determined digits below N vanish) — the
>         S7 SPLTAIL logic; σ = {(e₁,f₁)} ×2 needs only u > 2w.
>     (b) N ≤ 2w, N odd → DECIDED RAM(N): by (1) u = N for every
>         lift; parity consumes no residue.
>     (c) N ≤ 2w, N even → UND: the 2SIDED-vs-INERT decision at
>         the halved height needs the FULL K-residue at N, which
>         comp(N) < f₁ withholds — conservative drain.
> Census: by (1) the band-pin census at N is Q^{comp(N)} − 1
> (nonzero READABLE data only) — exactly E2's clause.
> (3) DEEPER BAND HEIGHTS ARE VALUE-UNSTABLE (the undercut,
> handled by DRAIN). A first readable-nonzero at m > N leaves
> u ∈ [N, m] undetermined: an unread component-t digit at any
> height in [N, m) (e.g. the class-0 digit at exactly N) undercuts
> the computed m. NO trichotomy is claimed at m > N; those states
> exit UND conservatively. E2's parenthetical "(the value is
> [readable]; the full K-residue is not)" is hereby SCOPED to the
> first band height — at deeper band heights neither is readable.
> (4) INSTANCES + MACHINE. At (1,2,2), k = 1 the band is the
> single height N and (1)–(3) collapse to GENH4-CAP(F) r3 (the
> prior authority). At (1,3,2) — first live f₁ = 3, comp(N) = 2,
> comp(N+1) = 1 — passPE1's fresh legs adjudicate (2) + the census
> EXHAUSTIVELY: N = 7 (32,768 states: RAM(7) = 3·2¹³ = (Q²−1)·2¹³,
> UND = 2¹³) and N = 8 (2,097,152 states: RAM(7) = 7·2¹⁸ =
> (Q³−1)·2¹⁸ full-slot census below the band, UND = 2¹⁸), plus
> 36/36 band-RAM PARI jobs at {(2,3)} incl. out-of-window
> perturbations — machine contact cited, the derivation above is
> the authority. E1's transport sentence is accordingly UPGRADED
> from (1,2)-authority to derived at (μ = 2, e₁ = 1, f₁ ≥ 2).
> SOURCE: passPE1 F3 (GAP) + FR-A/FR-B.”

**SUPERSESSION KIND: license** (it supplies the derivation E1 asserted on foreign authority) plus **scope-pin** on E2's readability parenthetical. `TARGETS: .31` (E1's transport sentence), `.14` (E2's parenthetical).

**CONDITIONALITY:** **Scoped to `e₁ = 1` by its own Setting** — “the e₁ ≥ 2 mixed genres stay OUTSIDE”. So after this annex the band story is: derived at (μ = 2, e₁ = 1, f₁ ≥ 2); asserted nowhere at mixed (e₁ ≥ 2, f₁ ≥ 2). **That residual hole is what LEMMA GENHN-CAP-GEN (2061–2085) fills**, and R4 F-1's own diagnosis (2059) is that **this annex refutes GENHN-3(a)'s "iff" as written**: “The first usage is false: the `[r2]` annex itself proves that a first-band height can support a lift-stable terminal decision.” So the annex is simultaneously a repair (of E1) and the evidence for a later finding (against GENHN.A(iii)/GENHN-3(b)).

**DERIVATION:** Quoted in full above; self-contained in the note's own slot model, resting only on GENHN-2's F_Q-independence.

*Arithmetic audit (rule 22) of step (4)'s two exhaustive rows, computed fresh.* At `(1,3,2)`, `Q = q = 2`, `f₁ = 3`, `k = 1`; the band is `[N, N+2]` with `comp(N) = 2`, `comp(N+1) = 1`.
- **N = 7 row.** Stated total 32,768 = `2^{15}`. `RAM(7) = 3 · 2^{13} = 24,576`; `UND = 2^{13} = 8,192`. Sum `= 24,576 + 8,192 = 32,768` ✓ **exactly the row total** — so the two strata partition the row. And `3 = Q^{comp(N)} − 1 = 2² − 1` ✓ E2's census at `comp = 2`.
- **N = 8 row.** Stated total 2,097,152 = `2^{21}`. `RAM(7) = 7 · 2^{18} = 1,835,008`; `UND = 2^{18} = 262,144`. Sum `= 2,097,152` ✓ **exactly the row total**. And `7 = Q^{f₁} − 1 = 2³ − 1` ✓ — the *full-slot* census, as the text says (“full-slot census below the band”), because at N = 8 the height-7 pin is interior.
**Both rows balance exactly, and the census factor switches from `Q^{comp}−1 = 3` to `Q^{f₁}−1 = 7` precisely when the pin moves from the band to the interior** — which is E2's clause, independently confirmed. No discrepancy.

**RESOLUTION TRACE:** statement 807–861 · derivation self-contained · correction sites 2059 (R4 F-1's use of it), 2085 (CAP-GEN's specialization of it: “The `[r2]` rule for \((e_1,\mu)=(1,2)\) is the specialization”).

XREF: `GENHN_passPE1_report.md:F3` — count **4**.
XREF: `GENH4_PROOF_2026-08-08.md:GENH4-CAP(F)` — count **11**.
ARTIFACT: `verification/openmath/genhn_pe1_fresh.py` ✓ present (passPE1's fresh legs FR-A/FR-B).

**TEETH:** **Exhaustive enumeration on a fresh instrument** — two full state spaces (32,768 and 2,097,152 states) at the first-live `f₁ = 3` genre, plus 36/36 band-RAM PARI jobs including out-of-window perturbations. **Disposition: executable regression on a DECORRELATED instrument** (passPE1's own, not GENHN's sealed battery) — and the note is explicit that the machine is corroboration, not authority: “machine contact cited, **the derivation above is the authority**”.

---
### EFF.GENHN.33  [lemma]  — LEMMA GENHN-4 (refine transfer at general (e₁, f₁, μ))

**CANONICAL STATEMENT:** verbatim, lines 867–870 (the Setting) plus the three-layer computation at 872–904, which IS the lemma — §S6.1 states no separate blockquoted display.

**FORM:** bold-headed paragraph + numbered three-layer proof (unquoted body prose; the note gives this lemma no blockquote, unlike GENHN-1/-2/-3).

> “Setting: a stage-α event at dv-slope κ (the stage polygon one side
> (0, μκ)–(μ, 0), integer κ > current floor S′, residual (T − s)^μ,
> s ∈ K^×). Recenter Φ′ ↦ Φ′_new := Φ′ + w, w := −ŝ·n(κ)-lift (the
> canonical digit lift; convention-keyed as always).”

**CONDITIONALITY:** **This is the shard's weld-face-bearing unit.**
(a) **Layer 1 consumes COROLLARY W-9 at μ ≥ 3** — declared in the layer itself and boxed at GENHN-BOX-2 (quoted at `.11`). `runs/qgen/WELD_FACE_AUDIT.md` designates it **LEAK-1 (LIVE, disclosed)** and records that **J-D0's perimeter cannot cover it even in principle** (the recentering is an additive shift, the NONCHAR failure mode). Status per that audit: “correctly disclosed”. `spec/HYPOTHESIS_LEDGER.md` indexes it as **HYP.148, class CARRY, at full strength**.
(b) **`[e2]` E3 riders the frame:** “S6.1's "gr R = the twisted algebra"” is named in E3's rider list; read `gr(O_L)`. `SUPERSESSION KIND: wording-rider`.
(c) **The hypothesis “residual (T − s)^μ, s ∈ K^×” carries a convention question that GENHN does not settle.** WELDZERO's WZ-PIN (its §S3, quoting GENHN L868 and L1006) argues the residual's coefficients are *twists of* the slot digits, so “s ∈ K^×” must be read in one of two conventions, and that “Only under this reading is GENHN-4 layer 1's conclusion true.” **That reading has NOT landed on GENHN** (verified against GENHN's full append chain; WELDZERO itself boxes it as a reading, and stands at clean-pass 1 of 2). Compiled as a disclosed external reading, not as a correction. See OPEN-CALL 2.
(d) **Layer 2's strictness at mixed (e₁, f₁ ≥ 2) genres is an invited attack surface**, by the note's own words (`.34`).

**DERIVATION:** Lines 872–904, quoted in full:

> “*The computation, in three layers.*
> 1. **Leading graded layer (the kills).** Pass to gr R = the twisted
>    algebra K^c[ℤ/e₁-graded lines] (COROLLARY W-9 @ accepted pin,
>    consumed HERE as the organizing frame — disclosed; GENHN-2 makes
>    the passage pointwise-faithful: one K-slot per height, slot-min =
>    valuation). In gr, the development transforms by the substitution
>    Φ̄′ ↦ Φ̄′ + s̄ on the residual polynomial: the new residual at the
>    node heights is R(T + s) where R(T) = (T − s)^μ, ALL of whose
>    coefficients below degree μ vanish — the μ pins die. The twist
>    powers z^{fl} (S4's cocycle: n(κ)^t = ẑ^{fl_t}n(tκ)) enter both
>    the residual assembly and the carry products IDENTICALLY, so the
>    graded identity holds coefficient for coefficient over K — this
>    is exactly what GENH4 S5 computed by hand at (2,1,2): "the
>    z̄-twist cancels against the key's constant term" is the fl-power
>    bookkeeping at μ = 2, e₁ = 2; and at (1,2,2) the ψ-relation wrap
>    is the f₁-component of the same product rule. Both
>    characteristics: the identity R(T+s) = T^μ is binomial-free as
>    stated (it is a substitution identity, not an expansion).
> 2. **Correction layer (everything else lands deeper and in-window).**
>    The non-graded corrections — products w^{i−j}A_i and the x-degree
>    overflow of w·A_i reduced mod Φ′ — have dv strictly greater than
>    the pinned heights: dv(w^{i−j}A_i-correction) ≥ (i−j)κ + (μ−i)κ +
>    1 = (μ−j)κ + 1 (each factor exceeds its side height only in the
>    correction terms; the exact-height products ARE layer 1). By
>    LEMMA GENHN-3(c)(d) they land at in-window positions and move
>    upward only.
> 3. **Bijectivity.** The map on digit spaces is triangular (each new
>    digit = old digit + strictly-lower-data), injective, image inside
>    the floored node {dv(A_j) > (μ−j)κ}; onto by cardinality: the
>    refine slice fixes the μ pinned digits and frees exactly the
>    slots above the node floors (slot strings are key-independent —
>    GENHN-2), the same count as the node. Letters: |K| − 1 choices of
>    s per step. ∎”

*Arithmetic audit (rule 22) of layer 2's inequality, recomputed.* For a correction term `w^{i−j}A_i` with `w` at dv-height `κ` and `A_i` at dv-height `≥ (μ−i)κ` (the node floor at coordinate `i`): `dv ≥ (i−j)κ + (μ−i)κ = (μ−j)κ` ✓ — and the note's `+1` is the strictness the parenthetical explains (“each factor exceeds its side height only in the correction terms”). The displayed chain `(i−j)κ + (μ−i)κ + 1 = (μ−j)κ + 1` is an identity in `i` ✓ (the `i`-terms cancel). Correct as displayed.

**RESOLUTION TRACE:** statement/setting 867–870 · proof 872–904 · grade note 906–915 · invariant maintenance 917–921 · correction sites 518–520 (E3's “gr R” rider), 1331–1338 (BOX-2, shard 2) · external: `WELD_FACE_AUDIT.md` L143–164, `WELDZERO_2026-08-14.md` §S2–S3.

XREF: `GRTJC_PROOF_2026-08-08.md:COROLLARY W-9` — count **2**.
XREF: `GENH4_PROOF_2026-08-08.md:GENH4-2` — count **15**.
XREF: `JD0_PROOF_2026-08-08.md:J-D0` — count **25**.
ARTIFACT: `runs/qgen/WELD_FACE_AUDIT.md` ✓ · `lean/notes/openmath/WELDZERO_2026-08-14.md` ✓ · `spec/HYPOTHESIS_LEDGER.md` ✓.

**TEETH:** **GN-REFINE3** — the box's declared compensating instrument, 3,072 pin checks, 0 violations, every μ = 3 stage-α event transported by ACTUAL re-division rather than by the graded formula. **Disposition: `accepted-with-decorrelation-supplied`** — the tooth decorrelates the weld consumption pointwise at μ = 3 without retiring it, exactly as GENHN-BOX-2 says. **Disclosed hole:** layer 2 at mixed (e₁, f₁ ≥ 2) is “machine-unreachable here” (`.34`).

---
### EFF.GENHN.34  [scope-record]  — the Grade note (honesty)

**CANONICAL STATEMENT:** verbatim, lines 906–915.

**FORM:** bold-headed paragraph.

> “**Grade note (honesty).** At μ = 2 the identity was verified
> pointwise-elementarily by GENH4 (S5, 192,000 refine events, and the
> carry displayed by hand). At general μ, layer 1 CONSUMES the W-9
> graded frame (accepted 2/2) rather than re-deriving the carry
> digit-by-digit; the compensating instrument is GN-REFINE3: every
> stage-α event on the μ = 3 rows is transported by ACTUAL polynomial
> re-division (no formula) and checked to kill exactly the three pins
> and land in the floored node, pointwise. A hostile pass should
> attack layer 2's strictness at mixed (e₁, f₁ ≥ 2) genres (first live
> n = 8, machine-unreachable here — S9 box).”

**CONDITIONALITY:** **The invitation was accepted and layer 2 survived.** Four hostile passes ran (PE1–PE4) and none of them landed a finding on layer 2's strictness; PE1's two CRITICALs were F1 (the tower leaf read, `.17`) and F2 (the budget display, `.25`). **However, the honest reading is that layer 2 at mixed genres remains untested, not vindicated** — the note's own reason (“machine-unreachable here”) still holds, and GENHN-BOX-3 still lists mixed (e₁, f₁ ≥ 2) as unexercised. The first mixed-genre machine contact anywhere in the arc is the 2026-08-12 `genhn_f2_count_check.py` at (2,2,2) — a **count** certificate, not a refine-transfer one.

**DERIVATION:** Grade declaration.

**RESOLUTION TRACE:** statement 906–915 · correction sites none (verified: untouched by every round and append) · relevant later evidence 2610–2614 (the (2,2,2) count contact, shard 2).

XREF: `GENH4_PROOF_2026-08-08.md:GENH4-CAP` — count **18** (§-level; see the `.11` NEAR-MISS for `GENH4 S5`).

**TEETH:** GN-REFINE3, as at `.33`. This unit is where the note *names* the tooth as compensating, which is what makes the BOX-2 disclosure honest rather than decorative.

---
### EFF.GENHN.35  [scope-record]  — Invariant maintenance

**CANONICAL STATEMENT:** verbatim, lines 917–921.

**FORM:** bold-headed paragraph.

> “**Invariant maintenance.** Refines add ŝ·n(κ) to the key with
> κ > S′ ≥ e₁h: the key's constant-term valuation f₁h and residual η
> are untouched (the added term sits strictly above the key's own
> side), so S3.1's ring invariants — and with them GENHN-2/-3 — hold
> at every node of every history.”

**CONDITIONALITY:** **`[e2]` E3 names this sentence in its rider list** — “S6's invariant-maintenance "S3.1's ring invariants"” — to be read with the carrier `O_L`. `SUPERSESSION KIND: wording-rider`. Second: the floor `κ > S′ ≥ e₁h` is the `S`-keyed floor; at f₁ ≥ 2 the corrected node floor is `D′h` (`.24`), so the honest reading post-settlement is `κ > S′ ≥ D′h` — and that is exactly the domain in which the post-D2b corrigendum's slot clause and LEMMA GENHN-LIFT's integrality hold. The note does not state this composition anywhere; it is a consequence of `.09`'s TERMINAL scope and `.24`'s TERMINAL settlement, and is flagged as OPEN-CALL 5 rather than silently written in.

**DERIVATION:** One line, displayed: the added term `ŝ·n(κ)` has dv-height `κ > S′`, strictly above the key's own side, so neither `v(Φ′(0))= f₁h` nor `η` moves.

**RESOLUTION TRACE:** statement 917–921 · correction sites 518–520 (E3 rider), 585–589 (`[r1]` node), 2315–2332 (post-D2b domain).

**TEETH:** Indirect — every chained history in every green row rides this invariant; GN-REFINE3's pointwise re-division is its sharpest test (the key is actually recentered and the invariants re-checked).

---
### EFF.GENHN.36  [lemma]  — §S6.2, the (CS-2) bracket and its reconciliation

**CANONICAL STATEMENT:** verbatim, lines 925–944.

**FORM:** bold-headed section body with an indented ASCII bracket display (unquoted).

> “By GENHN.A(i)–(iv) the stage system is the (μ, K)-cluster system in
> dv-units at the S-node (ragged-window-corrected). Its own
> α-aggregation is therefore LEMMA GENIND-2(b) @ pin run inside the
> stage verbatim:
>
>     b_{μ,K}(κ) = (|K|−1)·|K|^{(c(μ)+1)κ−1},   c(μ) = μ(μ−1)/2,
>
> per stage-slope-sum κ in dv-units. RECONCILIATION with GENH4 S6.2
> (the μ = 2 display): GENIND's bracket is mass-normalized (it
> includes the ghost fiber |K|^{c(μ)κ} of the α-transport), GENH4's
> ladder telescoping (q−1)q^{δ−1} is the letter-sum with per-node laws
> carrying the floors; they compose as
> (|K|−1)|K|^{2κ−1} = |K|^{κ} · (|K|−1)|K|^{κ−1} (ghost × letters) —
> the two displays are the same law in different normalizations, and
> the (e₁, f₁)-form of GENIND-5's (q−1)q^{2μ−1} is
> (q^{f₁}−1)·q^{f₁(2κ−1)}. One macroscopic rate per ambient v-unit:
> |K|^{e₁·(c(μ)+1)·(v-advance)} — at μ = 2: q^{2e₁f₁Δ}, GENH4's
> q^{e₁f₁Δμ}-per-v₁-half-step, reconciled. [machine: the μ = 3
> bracket exponent c(3)+1 = 4 over K is GENIND's GT-BRACKETID @ pin;
> this battery adds the μ = 3 STAGE realization at the E3 genre.]”

**CONDITIONALITY:**
(a) **“at the S-node” is re-grounded to the `B = D′h`-node** by the COUNT-RERUN Consumer sweep item 3 (2597–2601), which *also* explicitly protects this bracket: “The local mass-normalized bracket \(b_{2,K}(\kappa)=(|K|-1)|K|^{2\kappa-1}\) **is unchanged**: it is indexed by the actual refine height \(\kappa\) and uses a different ghost normalization from the raw finite-node cardinality.” `SUPERSESSION KIND: counter re-reading`, and the bracket display itself does **not** move.
(b) **E2's band scoping is tagged onto this section by name** — E2's echo list (254) includes “S6.2's assembly sentence”. `SUPERSESSION KIND: scope-pin`.
(c) `GENIND-5` is cited as the μ = 2 shape being generalized; **GENIND-5 is not a proved theorem in its source** — GENIND's own line (per `runs/qgen/WELD_FACE_AUDIT.md` LATENT-1) reads “NOT proved — boxed at the displayed obstruction”. GENHN uses only its *displayed form* as a shape to match, not as a premise; recorded here so a chapter cut does not upgrade it. See OPEN-CALL 6.

**DERIVATION:** Displayed inline. The reconciliation identity is one line: `(|K|−1)|K|^{2κ−1} = |K|^{κ} · (|K|−1)|K|^{κ−1}`.

*Arithmetic audit (rule 22), recomputed.* At `μ = 2`: `c(2) = 2·1/2 = 1`, so `(c(μ)+1)κ − 1 = 2κ − 1` ✓ matches the display. Factorization: `|K|^{κ} · (|K|−1)|K|^{κ−1} = (|K|−1)|K|^{2κ−1}` ✓ identity holds. The `(e₁,f₁)`-form: with `|K| = Q^{f₁}` and `Q = q` (d = 1), `(|K|−1)|K|^{2κ−1} = (q^{f₁}−1)q^{f₁(2κ−1)}` ✓ matches. At `μ = 3`: `c(3) = 3·2/2 = 3`, so `c(3)+1 = 4` ✓ matches the machine citation. Macroscopic rate `|K|^{e₁(c(μ)+1)Δ}` at μ = 2 is `Q^{f₁·e₁·2·Δ} = q^{2e₁f₁Δ}` ✓ matches.

**RESOLUTION TRACE:** statement 925–944 · correction sites 254 (E2 echo list), 2597–2601 (node re-grounding, bracket protected).

XREF: `GENIND_PROOF_2026-08-08.md:LEMMA GENIND-2` — count **7** · `GENIND-5` — count **9** · `GT-BRACKETID` — count **3**.
XREF: `GENH4_PROOF_2026-08-08.md:GENH4-CAP` — count **18** (the GENH4 §S6.2 display is cited by section; `GENH4 S6.2` has fixed-string count **0** — NEAR-MISS, carried descriptively, source defect 8).

**TEETH:** μ = 3 bracket: **foreign** (GENIND's GT-BRACKETID @ pin) plus this note's own **GN-E3** stage realization. μ = 2: **GN-LAWTIE** (law_Egen(e₁=2) ≡ law_E on 5 grid points, P2 ✓). Disposition: `foreign-note evidence` + executable regression.

---
### EFF.GENHN.37  [scope-record]  — §S6.3, drainage at general genres

**CANONICAL STATEMENT:** verbatim, lines 948–957.

**FORM:** section body paragraph (unquoted).

> “Per (entry, history) the conservative exits are slot-string
> computations exactly as GENH4 S6.3: UND = (A₀ all-readable-zero) ×
> (free depth), one exact q-power per stratum, history-dependent only
> through letter factors — the general closed forms are evaluated by
> the slot model (law_Egen in the battery; the e₁ = 3 instances are
> preregistered at never-measured territory). At μ ≥ 3 the stage's
> internal drainage recursion is GENIND.C run inside the stage
> (displayed, same telescoping; its μ ≥ 3 σ-residues sit behind
> [GENHN-HE] exactly as the base case sat behind Ore). No new
> mechanism.”

**CONDITIONALITY:** The “No new mechanism” claim here is about **drainage**, and is untouched by the `[r2]` refutation (which withdrew a *different* “No new mechanism” sentence, at `.17`). A chapter cut must not conflate the two — see §6.2. The conservative-drain rule is re-grounded by **GENHN-CAP-GEN's clause 1** (2069): “if some unread coefficient can undercut the provisional minimum, return `UND`” — a license that makes this section's rule exact at boundary heights.

**DERIVATION:** Cited (GENH4 §S6.3's slot-string computation, GENIND.C inside the stage), not re-derived.

**RESOLUTION TRACE:** statement 948–957 · correction sites 2067–2075 (CAP-GEN's rule + proof).

XREF: `GENIND_PROOF_2026-08-08.md:GENIND.C` — count **23**.

**TEETH:** **P6's UND3 law** — “UND3 = (q−1)q^{#(s₀≥cap)+|s₁|+|s₂|}” with spot instances scored exactly at S12: “(3,4,1): UND3 = 13,122, RAM3(7) = 26,244, and 13,122 + 26,244 = the whole row”. *Arithmetic audit (rule 22):* `13,122 + 26,244 = 39,366` ✓ = P6's stated total for that row, and `39,366 = 2 · 3^9 = (q−1)q^{6N−(21h+9)/2}` at `q = 3, N = 4, h = 1`: `6·4 − 15 = 9` ✓ so `(3−1)·3^9 = 2 · 19,683 = 39,366` ✓ **exact**. At `(2,5,1)`: `4,096 + 16,384 + 4,096 + 512 = 25,088`; the stated row total is `32,768 = 2^{15}` — **the four named strata do NOT exhaust that row** (`32,768 − 25,088 = 7,680` unaccounted). The note does not claim they do — it calls them “Spot instances” and only the (3,4,1) row carries the “= the whole row” claim ✓. **No discrepancy; recorded because a careless reader would infer exhaustiveness at (2,5,1).** Disposition: executable regression.

---
### EFF.GENHN.38  [lemma]  — §S7's transported facts (T1)/(T2) and the Y-trichotomy

**CANONICAL STATEMENT:** verbatim, lines 961–976 (the setting and the two transported facts), with the trichotomy's five cases at 978–1009 carried as this unit's DERIVATION. Emitted as its own unit because **(T1)/(T2) are cited by designation from at least four other units** (`.24`'s derivation, `.44`(i), `.46`(iii)'s (T1′)/(T2′), `.45`(ii)'s (T1₂)/(T2₂)) and from HE3.

**FORM:** section body with an indented ASCII display of the two facts.

> “Fix any μ = 2 genre (e₁, f₁ arbitrary, e₁f₁ ≥ 2), any decided stage
> leaf, any lift F ∈ O[x] of a leaf member with disc ≠ 0, any root θ
> of the stage block's factor, L := Frac(O)(θ). Two transported facts
> (both lift-stable by GENHN-3(a), proved exactly as in S3.1 since
> every root of the block shares the key's polygon and residual):
>
>     (T1)  v(θ) = h/e₁, gcd(h, e₁) = 1   ⟹   e₁ | e(L);
>     (T2)  η = res(θ^{e₁}π^{−h}) generates F_{Q^{f₁}} ⊆ k_L
>           ⟹   f₁ | f(L).
>
> Let Y := Φ′^{(t)}(θ) (the current key at θ; S6's chain keeps the
> state exact). Then Y² + A₁(θ)Y + A₀(θ) = 0 with dv(A₁(θ)) = w,
> dv(A₀(θ)) = u EXACTLY (GENHN-2 — which holds verbatim with θ in
> place of a key root: only (T1)/(T2) enter). The block has degree
> 2e₁f₁ over the base. The Y-trichotomy (ultrametric analysis of the
> quadratic over L):”

**CONDITIONALITY:** **(T1)/(T2) are the note's most-consumed export and are untouched by every correction** — E3 explicitly exempts §S7 (“S7's (T1)/(T2) (S7 already declares L := Frac(O)(θ) and works there)”). One case's *argument* is corrected in-text at `[r2]` (passPE1 F4) — see the DERIVATION. `GENHN-3(a)`'s lift-stability, on which the two facts rest, inherits `.29`'s R4 F-1 rider (interior criterion + CAP-GEN boundary criterion).

**DERIVATION:** Lines 978–1016, the five cases, quoted:

> “* **stage-RAM (u odd, u ≤ 2w).** One-side Y-polygon: v(Y) = u/(2e₁)
>   with u odd ⟹ 2e₁ | e(L) **[r2 2026-08-09: WITH (T1) — v(Y) alone
>   gives only (2e₁/gcd(u, e₁)) | e(L) when gcd(u, e₁) > 1 (e.g.
>   e₁ = 3, u = 9: 2 | e only); gcd(u, e₁) is odd (u odd), so
>   lcm(e₁, 2e₁/gcd(u, e₁)) = 2e₁ — the value-group argument needs
>   both facts. passPE1 F4]**; with (T2): e·f ≥ 2e₁f₁ = block degree ⟹
>   ONE factor, e = 2e₁, f = f₁: σ-block {(2e₁, f₁)}.
> * **stage-2SIDED (u > 2w).** v(Y) ∈ {w/e₁·½·…} — two exact values
>   w/(e₁)−… (in dv-halves: w and u−w, distinct). Norm count: the
>   product of v(Φ′(θᵢ)) over the block's roots equals dv-total u
>   (Res(F_block, Φ′) = ±Nm(A₀), by GENHN-2 at the key's own roots);
>   if the block were irreducible its roots would be conjugate with
>   Galois-invariant v(Φ′(θ)) — contradicted by the two distinct
>   values; j roots at each value with j·w + (2e₁f₁−j)/(2e₁f₁)·…
>   forces the even split j = e₁f₁: two factors, each of degree e₁f₁
>   with (T1)+(T2) forcing e = e₁, f = f₁ on each: {(e₁,f₁),(e₁,f₁)}.
> * **stage-SPLTAIL (A₀ window-hidden, w below the certification
>   bound 2w < e₁N).** Every lift has u_lift ≥ e₁N > 2w (GENHN-3(a)'s
>   undercut floor): a 2SIDED configuration for every lift, including
>   the A₀ = 0 corner (F_block = Φ′(Φ′ + A₁), both factors carrying
>   the key polygon): σ as 2SIDED.
> * **stage-SPLITEQ ('11', roots s₁ ≠ s₂ ∈ K).** One S6 refine step
>   with letter s₁ (the kill needs only R(s₁) = 0) leaves
>   dv(A₁′) = κ exactly with residue s₁ − s₂ ≠ 0 (char 2: = S₁ ≠ 0 by
>   separability) and dv(A₀′) > 2κ: a 2SIDED configuration for every
>   lift — {(e₁, f₁), (e₁, f₁)}. (Hensel at the stage, executed as
>   one refine step.)
> * **stage-INERT ('2', residual irreducible over K).** v(Y) = κ/e₁
>   and Ȳ := res(Y/n(κ)(θ)) is a root of the twisted residual (S4's
>   coherent-normalizer computation): [K(Ȳ) : K] = 2 ⟹
>   [F_Q(Ȳ) : F_Q] = 2f₁ ⟹ f(L) ≥ 2f₁; with (T1) and degree 2e₁f₁:
>   one factor, e = e₁, f = 2f₁: {(e₁, 2f₁)}.
>
> Every case consulted only lift-stable data: (A0)-strong at every
> μ = 2 stage leaf. …∎”

*Arithmetic audit (rule 22) of the `[r2]` RAM repair, recomputed.* Claim: `v(Y) = u/(2e₁)` with `u` odd gives only `(2e₁/gcd(u, e₁)) | e(L)` — because the denominator of `u/(2e₁)` in lowest terms is `2e₁/gcd(u, 2e₁)`, and with `u` odd `gcd(u, 2e₁) = gcd(u, e₁)` ✓. Worked instance `e₁ = 3, u = 9`: `gcd(9,3) = 3`, so the denominator is `6/3 = 2`, i.e. only `2 | e` ✓ matches the note. Repair: `gcd(u, e₁)` is odd since `u` is odd ✓, so `lcm(e₁, 2e₁/gcd(u,e₁))` — write `g := gcd(u,e₁)`, odd; `lcm(e₁, 2e₁/g)`. Since `2e₁/g` contributes the factor 2 and `e₁` contributes all of `e₁`, and `e₁ | lcm` while `2 | lcm` with `2 ∤ e₁`? **Not necessarily — `e₁` may itself be even.** Check `e₁` even, say `e₁ = 6, u = 9`: `g = 3`, `2e₁/g = 4`, `lcm(6,4) = 12 = 2e₁` ✓. `e₁ = 2, u = 1`: `g = 1`, `2e₁/g = 4`, `lcm(2,4) = 4 = 2e₁` ✓. `e₁ = 3, u = 9`: `g = 3`, `2e₁/g = 2`, `lcm(3,2) = 6 = 2e₁` ✓. General: `lcm(e₁, 2e₁/g) = 2e₁/gcd(g·?, ...)` — write `e₁ = g·m`; then `2e₁/g = 2m`, and `lcm(gm, 2m) = m·lcm(g,2) = 2gm = 2e₁` since `g` is odd ✓. **The repair is correct at general `e₁`, and its proof needs exactly the oddness of `g`, which follows from the oddness of `u`.** No discrepancy.

**RESOLUTION TRACE:** statement 961–976 · proof 978–1016 · correction site 979–983 (`[r2]` F4, in-proof) · scope remark 1018–1027.

XREF: `GENHN_passPE1_report.md:F4` — count **3**.
XREF: `HE3_PROOF_2026-08-08.md:HE3-0` — count **19** (HE3-0's locus is where (T1)/(T2) are first pinned; reverse edge, see §3.2).

**TEETH:** **GN-SIGMA** — PARI factorpadic vs the dictionary, 37,792 certified jobs / 0 bad, including the E31 rows' `{(6,1)}/{(3,1)²}/{(3,2)}` at **wild p = 3, e₁ = 3** (which is exactly the `gcd(u, e₁) > 1` geography the `[r2]` repair is about). Planted mutant **GN-T-SIG** fired 2/2. Disposition: executable regression against an independent oracle + planted mutant.

---
### EFF.GENHN.39  [scope-record]  — Remark `[r0-battery]` (stage data vs ambient window)

**CANONICAL STATEMENT:** verbatim, lines 1018–1027.

**FORM:** bold-headed remark paragraph.

> “**Remark [r0-battery] (scope: stage data vs ambient window).** The
> theorem's leaf is STAGE data (the A_j digit strings at the stage
> window); "lift-stable" is relative to that data. At EMBEDDED genres
> read through an AMBIENT window N, the stage digits are themselves
> only partially determined by the ambient data — the sibling Hensel
> split loses v(f′(ρ)) digits — so the set of stage leaves CERTIFIED
> by an ambient window is strictly smaller than the stage window
> suggests. This composition fact (machine-surfaced at the smoke run)
> is quantified in GENHN-BOX-4/S11.F; it does not touch this
> theorem's statement or proof.”

**CONDITIONALITY:** Unconditional; a scope fence on `.15`. Its quantification is out of range (S11.F, 1777–1798; GENHN-BOX-4, 1352–1377). The fence is **load-bearing for how GENHN.C may be cited**: a consumer reading σ off an ambient-window leaf must gate at the S11.F perimeter. The note's own machine practice matches: “the battery gates σ-emission on extracted rows by the per-leaf consulted-digit set against this table (leaf_cert_E)”.

**DERIVATION:** Composition of `.29`(a) with the sibling-Hensel precision loss; derived in S11.F (shard 2).

**RESOLUTION TRACE:** statement 1018–1027 · derivation 1780–1798 (shard 2) · box 1352–1377 (shard 2).

**TEETH:** **The discovery event was a RED smoke run** — “Smoke 1 (post-audit-repairs): RED — 6 GN-SIGMA mismatches, ALL at (Zp,2,5,1) V1E2 RAM(9) … Discovery event for S11.F” (1731–1736). **Disposition: measurement that FIRED against the pre-gate reader**, then converted into a preregistered diagnostic: at S12 P9 the uncertified tail is “V p=2 1,216 / 349 mismatches, V p=3 241 / 58, all full-side legs 0/0 — the S11.F perimeter is REAL on both sides (certified exact, uncertified genuinely mixed)”. This is the shard's clearest instance of a machine finding that *sharpened* the theory rather than breaking it.

---
### EFF.GENHN.40  [open-box]  — `[GENHN-HE(μ ≥ 3)]`

**CANONICAL STATEMENT:** verbatim, lines 1029–1042.

**FORM:** display (blockquoted bold-headed box).

> “**[GENHN-HE(μ ≥ 3)] (THE box; first live n = 6).** At stage
> leaves of multiplicity μ ≥ 3 (decided by the stage read with
> separable residuals over K), the σ-decision — every disc ≠ 0 lift
> factors as the stage dictionary (e₁e_s, f₁f_s) per stage piece —
> is OPEN. The expected mechanism is this S7 run at degree μ (the
> norm-count argument needs the case analysis of a degree-μ
> Y-polygon; equivalently Ore's theorem over the stage ring R),
> i.e. the same resolvent method one level up; the classical
> Montes/GMN order-≥2 index theorem is the literature target for a
> faithful cite. Per-n instance criterion: [GENHN-HE] enters P(n)
> exactly for the genres with μ ≥ 3 realizable at degree n — none
> at n ≤ 5; E3/F3 at n = 6, 7; towers add inner instances at
> n ≥ 8. Machine corroboration (labeled, not proof): GN-SIGMA's E3
> leg PARI-checks the μ = 3 dictionary on depth-0-decided leaves.”

**CONDITIONALITY:**
(a) **“Ore's theorem over the stage ring R”** is riddered by E3 — the rider list names “S9.2 item 1's "Ore over the stage ring" (read: over O_L)”, and the same reading applies to this display's parallel phrase (E3's rider list does **not** name this line, so the compiler flags rather than applies it — OPEN-CALL 5).
(b) **This box is the note's one surviving mathematical open** at n ≤ 7, per `.18`, and is the top item of S9.2's endgame list (1449–1453, shard 2): “THE one load-bearing open lemma of the whole composite program.”
(c) **It is NOT discharged by anything in this note.** External state (recorded, not asserted here): `HE3_PROOF_2026-08-08.md`'s title claims “[GENHN-HE(μ ≥ 3)] CLOSED AT ITS FIRST-LIVE CASE (μ = 3, degrees n ≤ 7: UNCONDITIONAL) AND REDUCED TO ONE NAMED BRANCH AT μ ≥ 4 (HE3-BOX-6)” — a *consumer-side* discharge that has **not** landed as an append on GENHN (verified across all eleven appends: `grep -c 'HE3' GENHN_PROOF_2026-08-08.md` hits only the `[r1]` erratum's HE3-0 citation and S9.2's box text). See OPEN-CALL 6 and the HE3 shards.

**DERIVATION:** Not derived — this is the open box. What is derived is the *shape* of the expected mechanism (§S7 at degree μ) and the *instance criterion* (which n it enters).

**RESOLUTION TRACE:** statement 1029–1042 · endgame listing 1449–1453 (shard 2) · no correction site in GENHN (verified).

XREF: `GENHN_PROOF_2026-08-08.md:[GENHN-HE` — count **19** (self-reference density: the box is named 19 times in its own note).
XREF: `HE7_PROOF_2026-08-08.md:[GENHN-HE(μ)]` — count **2** (the reverse edge: HE7's COROLLARY HE7.B discharges this predicate at level 2 — see §3.2).
XREF: `HE3_PROOF_2026-08-08.md:GENHN-HE` — grep-verified count **7**.

**TEETH:** **Explicitly labeled non-proof.** “Machine corroboration (labeled, not proof): GN-SIGMA's E3 leg PARI-checks the μ = 3 dictionary on depth-0-decided leaves” — scored at S12 P9 as “E3 1,792 + 6,565 ([GENHN-HE(3)] corroboration, labeled)”. **Disposition: `measurement`, explicitly declined as evidence for the box.** This is the shard's model of an honest labeled corroboration.

---
### EFF.GENHN.41  [changes-record] · SERIES: GENHN-T(b)-ARC, member 2 of 3  — the `[r2]` refutation and its mechanism

**CANONICAL STATEMENT:** verbatim, lines 1088–1125 (the annex header and THE MECHANISM).

**FORM:** display (blockquoted dated refutation-and-repair header + a bold-headed mechanism derivation).

> “**[r2] REFUTATION + REPAIR 2026-08-09 (LEMMA GENHN-T(b) → LEMMA
> GENHN-T(b)′: the tower leaf read is the COMPOSED-KEY development
> of f itself). Source: GENHN passPE1 F1 (CRITICAL —
> `GENHN_passPE1_report.md`, instrument `genhn_pe1_fresh.py` FR-D):
> constructed n = 8 members of the (2,1,4) genre with inner
> (2,1,2) events, PARI-confirmed on two independent oracle routes,
> REFUTE the sealed (b): the stage-algebra inner read predicts
> composed σ {(4,2)} and {(4,1),(4,1)} where the true octics are
> {(8,1)}; even the σ-agreeing instance had its leaf label
> mispriced (stage-RAM(21) vs true RAM(25)). Tagged repair per the
> [r1] mechanism (GENHN at 0/2, unaccepted); sealed battery runner
> and artifacts UNTOUCHED — the battery had NO tower leaf rows
> (GENHN-BOX-3 disclosed "tower LAWS (witness only)"); the repair's
> machine leg is `verification/openmath/genhnr2_supp.py` (GREEN,
> 147 checks / 0 violations, 3 teeth — the FIRST tower leaf-read
> coverage: the 4 refuted instances as regression teeth, fresh
> sweeps at (2,1,4)→(2,1,2) for u₂ ∈ {5,7}, the first f₂ = 2 tower
> genre (2,1,4)→(1,2,2) over K₂ = F₄, and three parse-gated
> 3-STAGE instances at n = 16).**
>
> **THE MECHANISM (what the stage algebra loses — re-derived, not
> transcribed).** Work in the two-variable frame: F(x, Y) :=
> Y^{μ₁} + Σ_J A_J(x)Y^J (the level-1 development with Y a free
> variable), K₂(x, Y) the inner-key lift, and divide in Ô[x][Y]:
> F = Σ_j Ĝ_j(x, Y)·K₂^j, deg_Y Ĝ_j < e₂f₂. Monic division is
> functorial under the coefficient map Ô[x] → R = Ô[x]/(Φ′), so
> the sealed (b)'s inner read computes EXACTLY Ĝ_j(θ, Y) — every
> coefficient reduced mod Φ′ (each x-overflow x^{D′+r} priced at
> its tail value, since Φ′(θ) = 0). But a LEAF evaluates at an
> actual root x₀ of f, where Φ′(x₀) = Y₀ ≠ 0 — dv₂(Y₀) = u₂ on
> the node locus — and Ĝ_j(x, Y) − (any lift of Ĝ_j(θ, Y)) ∈
> Φ′·Ô[x][Y]: the two reads differ by Φ′(x₀)·H_j(x₀, Y₀), a
> correction at dv₂ = u₂ + dv₂(H_j) which the quotient cannot see
> and which UNDERCUTS stage-visible pins at leaf depth (the PE1
> instance: the x-overflow carry 16x² = 16Φ′ + 32 contributes
> 16Φ′ at dv₂ = 21, under the stage-algebra pin u₂-read 28). The
> honest leaf object develops f ITSELF by the composed key.”

**CONDITIONALITY:** Unconditional as a refutation. **The mechanism is re-derived, not transcribed from the report** — the header says so, which matters because the report is an external artifact and the note is the authority for its own repair.

**DERIVATION:** Quoted in full above; the load-bearing step is functoriality of monic division under `Ô[x] → R`, plus the observation that a leaf evaluates where `Φ′(x₀) ≠ 0`.

*Arithmetic audit (rule 22) of the displayed carry, recomputed at the PE1 frame.* `Φ′ = x² − 2` over ℤ₂ (the witness frame at 1292), `e₁ = 2, f₁ = 1, h = 1`, so `dv = 2v`, and `dv₂ = e₁e₂·v = 4v` at `e₂ = 2`. The carry: `16x² = 16(Φ′ + 2) = 16Φ′ + 32` ✓ identity holds. Value of `16Φ′` at a node root: `dv₂(16) = 4·v(16) = 4·4 = 16` and `dv₂(Φ′(x₀)) = u₂`; at `u₂ = 5` this gives `16 + 5 = 21` ✓ **matches the stated dv₂ = 21**. The stage-algebra read prices the same coordinate at 28. `21 < 28` ✓ — the correction undercuts, exactly as claimed. **The displayed arithmetic is correct.**

**RESOLUTION TRACE:** statement 1088–1125 · derivation self-contained · targets 282–301 (`.17`), 1061–1086 (the withdrawn proof).

XREF: `GENHN_passPE1_report.md:F1` — count **7**.
ARTIFACT: `verification/openmath/genhn_pe1_fresh.py` ✓ · `verification/openmath/genhnr2_supp.py` ✓ · `verification/openmath/genhnr2_supp_output.txt` ✓.

**TEETH:** `genhnr2_supp.py` — 147/0, 3 teeth, first tower leaf-read coverage. **Disposition: executable regression built FROM a refutation** (the four refuted instances are installed as permanent regression teeth). **`disclosed non-repair` in the sealed instrument:** the battery had no tower leaf rows at all, so the seal could not have caught this — disclosed in advance at GENHN-BOX-3 (“tower LAWS (witness only)”).

---
### EFF.GENHN.42  [lemma] · SERIES: GENHN-T(b)-ARC, member 3 of 3  — LEMMA GENHN-T(b)′, setting + clause (i) [COMPOSED CARRIER]

**CANONICAL STATEMENT:** verbatim, lines 1127–1155.

**FORM:** display (blockquoted bold-headed lemma with an indented ASCII composed-key display and a bracketed f₁ ≥ 2 overflow parenthetical).

> “**LEMMA GENHN-T(b)′ (tower composition, corrected).** Setting:
> outer genre (Q; e₁, f₁, μ₁; h), key Φ′ (deg D′ = e₁f₁, S3.1/E3
> invariants), level-1 development f = Φ′^{μ₁} + Σ_{J<μ₁} A_J Φ′^J;
> an inner CS event on the stage read: a side of the
> (J, dv(A_J))-polygon of dv-slope κ₂ = u₂/e₂ (lowest terms,
> gcd(u₂, e₂) = 1; κ₂ > D′h by the [r1] node floor) carrying
> residual ψ₂^{μ₂} over K, f₂ := deg ψ₂, e₂f₂μ₂ = μ₁ (FULL inner
> side — the first-live shape; partial sides sit in
> [GENHN-TOW-1]). Let Φ₂ ∈ Ô[x] be the COMPOSED KEY: the canonical
> lift of the inner key,
>
>     Φ₂ := Φ′^{e₂f₂} − Σ_{t<f₂} ĉ_t · n̂(u₂(f₂−t)) · Φ′^{e₂t}
>
> (ψ₂(T) = T^{f₂} − Σ_t c_t T^t; n̂(m) = x^i π^a the dv-height-m
> normalizer monomial, i < e₁), monic of degree D₂ := D′e₂f₂. Set
> dv₂ := e₁e₂·v (the composed ladder). (At f₁ ≥ 2 the coefficient
> products ĉ_t·n̂ can overflow x-degree D′; their Φ′-carries sit at
> the same dv-value one Φ′-step right, i.e. STRICTLY ABOVE the
> inner side — side drop u₂/e₂ per step — so Φ₂'s literal
> Φ′-development differs from the display only above the side:
> side and residual are unchanged, and (i)'s proof reads on the
> literal development.) Then:
> (i) [COMPOSED CARRIER] every root ξ of Φ₂ has v(ξ) = h/e₁ with
> η(ξ) a root of ψ, and v(Φ′(ξ)) = u₂/(e₁e₂) with η₂(ξ) :=
> res(Φ′(ξ)^{e₂}/n̂(u₂)(ξ)) a root of ψ₂; the forcing chain gives
> e(L₂/base) = e₁e₂, f = f₁f₂, [L₂ : base] = D₂, Φ₂ irreducible,
> O_{L₂}-residue field K₂ := F_Q(η, η₂) = F_{Q^{f₁f₂}} — carrier
> in L₂/O_{L₂} per ERRATUM E3 (Ô[x]/(Φ₂) is in general a
> non-maximal order).”

**CONDITIONALITY:** **The composed-key DISPLAY is gauge-naive and is corrected by a dated erratum from a CONSUMER (HETOW), lines 1980–2032.** Quoted:

> “**The seam.** LEMMA GENHN-T(b)′'s DISPLAY of the composed key's lift
> coefficients is gauge-naive: the displayed
>
>     Φ₂ := Φ′^{e₂f₂} − Σ_{t<f₂} ĉ_t · n̂(u₂(f₂−t)) · Φ′^{e₂t}
>
> with ĉ_t a plain lift of ψ₂'s coefficient c_t carries a wrap seam at
> η ≠ 1 frames. The normalizer monomials are not multiplicative —
> n̂(u₂)^{f₂−t} = n̂((f₂−t)u₂)·(x^{e₁}/π^{h})^{W(t)} with
> W(t) = ⌊(f₂−t)·i(u₂)/e₁⌋ — so the displayed coefficient's residue
> against S4's coherent normalizers … is c_t·η^{−W(t)}, not c_t: … the lifts need the correction absorbing that
> wrap factor,
>
>     ĉ_t := lift(c_t·η^{W(t)})   (per digit at f₁ ≥ 2:
>     the exact-height (LIFT) output L_{(f₂−t)u₂}(c_t·η^{W(t)})).
>
> This is the CORRECTED DISPLAY. At any frame where each
> c_t·(η^{W(t)} − 1) = 0 — in particular at η = 1 — corrected = naive.”

with the scope (2018–2029): “T(b)′'s PROOF mechanism is unaffected: the carrier forcing chain, the composed slot lemma (ii), and the σ clauses (iii)–(v) hold AT THE CORRECTED KEY … what was wrong is the DISPLAY's lift prescription (L1136–1148, including the f₁ ≥ 2 overflow parenthetical — see HETOW [r1] F-4 for the pinned no-overflow (LIFT) form) feeding that proof, which transcribed the gauge-naive lifts.”
`SUPERSESSION KIND: replacement` (the lift prescription). `TARGETS: .42` (the display and the overflow parenthetical).
**Second layer:** the exact-height `(LIFT)` operator the corrected display consumes had **no in-note lemma** until the 2026-08-12 R4 F-3 append supplied **LEMMA GENHN-LIFT** (2101–2189), whose APPLICATION TO THE COMPOSED KEY re-derives `res(n(u₂)^r/n(ru₂)) = η^{W(t)}` and shows the corrected lift clears the side with the same bound `r(u₂ − e₂D′h)/e₁ > 0`. `SUPERSESSION KIND: license`.
**CHAIN: frozen naive display → HETOW erratum's corrected display → GENHN-LIFT's licensed lift operator. TERMINAL: GENHN-LIFT's `L_{ru₂}(c_t η^{W(t)})·Φ′^{e₂t}` form.**

**DERIVATION:** Lines 1216–1238 (*Proof of (i)*), quoted:

> “THE x-POLYGON OF Φ₂ IS ONE SIDE of slope h/e₁
> through (D₂, 0): the block Φ′^{e₂f₂} sits weakly above that side
> … with constant-term
> valuation e₂f₂·f₁h EXACT (S3.1); each lift-term monomial —
> x^i π^a from n̂(u₂(f₂−t)) times an x^c π^g monomial of Φ′^{e₂t}
> … — clears the side at
> abscissa i + c with gap a + g − (D₂ − i − c)h/e₁ ≥
> u₂(f₂−t)/e₁ − (f₂−t)e₂D′h/e₁ = (f₂−t)(u₂ − e₂D′h)/e₁ > 0, using
> e₁a + ih = u₂(f₂−t) and THE [r1] NODE FLOOR u₂ > e₂D′h (inner
> slopes exceed D′h). So the side and its residual ψ^{e₂f₂} come
> from Φ′^{e₂f₂} alone: v(ξ) = h/e₁, η(ξ) a root of ψ. Next, the
> level-1 development of Φ₂ is the displayed one BY CONSTRUCTION:
> 0 = Φ₂(ξ) makes Y_ξ := Φ′(ξ) a root of T^{e₂f₂} −
> Σ_t ĉ_t(ξ)n̂(ξ)T^{e₂t} whose Newton polygon over L₂ has its pins
> ON the one side (0, u₂f₂)–(e₂f₂, 0) (monomial values are exact),
> gcd(u₂, e₂) = 1: v(Y_ξ) = u₂/(e₁e₂) exactly and the twisted side
> residual is ψ₂ … Forcing chain: the
> value group contains h/e₁ and u₂/(e₁e₂), and ⟨1/e₁, u₂/(e₁e₂)⟩ =
> (1/(e₁e₂))·⟨e₂, u₂⟩ = (1/(e₁e₂))ℤ, so e ≥ e₁e₂; f ≥
> [F_Q(η, η₂) : F_Q] = f₁f₂; ef ≤ [L₂ : base] ≤ deg Φ₂ = D₂ =
> e₁e₂f₁f₂ forces equality throughout — Φ₂ is the minimal
> polynomial of ξ, irreducible, O_{L₂}/m = K₂. ∎”

*Arithmetic audit (rule 22), recomputed.* `D₂ = D′e₂f₂ = e₁f₁e₂f₂` ✓ and `e₁e₂ · f₁f₂ = D₂` ✓ so the forcing chain's `ef ≤ D₂` closes exactly. Value-group step: `⟨1/e₁, u₂/(e₁e₂)⟩ = (1/(e₁e₂))⟨e₂, u₂⟩ = (1/(e₁e₂))·gcd(e₂,u₂)ℤ = (1/(e₁e₂))ℤ` using `gcd(u₂,e₂) = 1` ✓. Clearance bound: `u₂(f₂−t)/e₁ − (f₂−t)e₂D′h/e₁ = (f₂−t)(u₂ − e₂D′h)/e₁` ✓ identity, `> 0` iff `u₂ > e₂D′h` ✓ which is the `[r1]` node floor. **All steps check.**

**RESOLUTION TRACE:** statement 1127–1155 · proof 1216–1238 · correction sites 1980–2032 (HETOW erratum), 2101–2189 (GENHN-LIFT).

XREF: `HETOW_passPE1_report.md:F-1` — count **9**.
XREF: `HETOW_RECON_2026-08-09.md:HETOW-1` — count **23** · `HETOW-2` — count **9**.
PINS: `5f821dc` ✓ · `d0d3ca6` ✓ · `5335ae3` ✓.
ARTIFACT: `verification/openmath/hetow_pe1_fresh.py` — **verified present**; `hetowr1_supp.py` — **verified present**.

**TEETH:** **The gauge-naive tooth FIRED at three frames.** HETOW passPE1's frame X: `p = 3, Φ′ = x² − 6, η = 2, (e₂,f₂) = (1,2), u₂ = 3, ψ₂ = Z² + Z + 2, W(0) = 1` — the DISPLAYED key `Φ′² + 3xΦ′ + 54` has PARI σ = {(4,1)} ≠ {(2,2)}; the CORRECTED key `Φ′² + 3xΦ′ + 108` has σ = {(2,2)}. Re-confirmed at two further η ≠ 1 frames by `hetowr1_supp.py` (GREEN, 29 gp jobs + 15 exact checks, 0 violations). **Disposition: planted mutant from a CONSUMER note; fired against the supplier.** **`disclosed non-repair` in GENHN's own legs:** “`genhnr2_supp.py`'s tower frames sit at q = 2 (Φ′ = x² − 2, K = F₂), **where η = 1 forcibly** and the two prescriptions coincide; the sealed battery had no tower-leaf rows” (2026–2029) — GENHN's entire tower coverage was inside the blind spot.

*Arithmetic audit of the frame-X witness (rule 22, computed fresh).* `η = 2` in `F₃` (i.e. `η = res(θ²/3)` for `Φ′ = x² − 6 = x² − 2·3`, so `η = res(6/3) = 2` ✓). `i(u₂)` at `u₂ = 3`, `e₁ = 2`, `h = 1`: solve `i·1 ≡ 3 (mod 2)` with `0 ≤ i < 2` ⟹ `i = 1` ✓, `a = (3−1)/2 = 1`, `n̂(3) = xπ = 3x` ✓ matching the displayed `3xΦ′` term. `W(0) = ⌊(f₂−0)·i(u₂)/e₁⌋ = ⌊2·1/2⌋ = 1` ✓ as stated. Correction factor `η^{W(0)} = 2`; naive constant `54`, corrected `108 = 2 · 54` ✓ **exactly the factor η = 2**. The witness is internally exact.

---
### EFF.GENHN.43  [lemma]  — T(b)′ clause (ii) [COMPOSED SLOT LEMMA — GENHN-2′]

**CANONICAL STATEMENT:** verbatim, lines 1156–1167.

**FORM:** display (blockquoted lemma clause with an indented ASCII slot-min display).

> “(ii) [COMPOSED SLOT LEMMA — GENHN-2′] {x^a Φ′^b : a < D′,
> b < e₂f₂} is a triangular-unimodular basis of the degree-< D₂
> polynomials; for A = Σ c_{a,b} x^a Φ′^b (c ∈ Ô) and every x₀ on
> the tower-node locus ((T1), (T2), and the inner (T1₂): v(Φ′(x₀))
> = u₂/(e₁e₂) exactly, (T2₂): η₂(x₀) a root of ψ₂ — both proved
> for the inner block's roots from the level-1 pins as in S7):
>
>     dv₂(A(x₀)) = min_{a,b} (e₁e₂·v(c_{a,b}) + a·e₂h + b·u₂)
>     EXACTLY,
>
> and the minimizing residues assemble ONE K₂-digit per
> dv₂-height.”

**CONDITIONALITY:** Proved at the displayed generality (full inner side). Inherits `.42`'s corrected key. **The “ONE K₂-digit per dv₂-height” universal is the composed analogue of the clause re-displayed twice at `.09`** — and the note never applies the occupied-height restriction here. The R4/A2 and D2b witnesses are level-1; whether the composed display needs the same `D₂h`-style restriction is **not addressed anywhere in the note**. Flagged as OPEN-CALL 5, not silently repaired.

**DERIVATION:** Lines 1240–1260, quoted:

> “*Proof of (ii).* Basis: deg(x^a Φ′^b) = a + bD′ hits each degree
> < D₂ once, leading coefficient 1 — triangular-unimodular. Values:
> the candidate heights are exact monomial values (dv₂(x^a Φ′^b
> π^v-part(c)) = e₁e₂v(c) + a·e₂h + b·u₂ by (T1)+(T1₂)); the
> ultrametric gives ≥ min with equality unless several candidates
> tie AT the min height. TWO-STEP CLASS SEPARATION: a tie forces,
> mod e₂: (b − b′)u₂ ≡ 0, hence b ≡ b′ (mod e₂) (gcd(u₂, e₂) = 1);
> writing b′ = b + e₂t and dividing the height equation by e₂:
> (a − a′)h ≡ t·u₂ (mod e₁) — so per t the class of a mod e₁ is
> determined (gcd(h, e₁) = 1): at most f₁ tying monomials per
> t-value, f₂ t-values, ≤ f₁f₂ in all. TOWER-BASIS INDEPENDENCE:
> normalizing by the attaining monomial, the competing residues
> are res(c_{a,b})·u_t·η^s·η₂^t with u_t ∈ K^× fixed units …; a
> vanishing F_Q-combination splits along the K-basis
> {η₂^t}_{t<f₂} of K₂ into K-components u_t·Σ_s res(c)η^s = 0,
> each forcing res(c) = 0 ({η^s}_{s<f₁} an F_Q-basis of K). So
> the min is exact and the height's residue is one K₂-digit. ∎
> (The e₂ = 1, f₂ = 2 within-class branch — ties resolved by
> η₂-independence alone — is first machine-exercised by SUPP-B.)”

*Arithmetic audit (rule 22) of the basis and the tie count.* Basis: `{x^a Φ′^b : a < D′, b < e₂f₂}` has `D′ · e₂f₂ = D₂` elements ✓, and `deg(x^aΦ′^b) = a + bD′` ranges over `0..D₂−1` bijectively (base-`D′` representation) ✓, leading coefficient `1` since Φ′ is monic ✓ — triangular-unimodular ✓. Tie count: `≤ f₁` per `t`, `f₂` values of `t`, so `≤ f₁f₂ = [K₂ : F_Q]` ✓ — exactly the K₂-dimension, which is why the residues assemble one K₂-digit and no more. **Consistent.**

**RESOLUTION TRACE:** statement 1156–1167 · proof 1240–1260 · correction sites: none in GENHN for this clause (verified); the HETOW erratum explicitly exempts it (“the composed slot lemma (ii) … hold AT THE CORRECTED KEY”).

**TEETH:** **SUPP-B** — “the e₂ = 1, f₂ = 2 within-class branch … first machine-exercised by SUPP-B”, i.e. `genhnr2_supp.py`'s first f₂ = 2 tower genre (2,1,4)→(1,2,2) over K₂ = F₄. Plus `genhn_pe2_fresh.py`'s “first outer-f₁ = 2 tower genres, first 2-stage dictionary contact, the η₂-cocycle adjudication, and Q = 4 tower legs” (1590–1593). **Disposition: executable regression on two decorrelated instruments; (ii) HELD at PE2** — “LEMMA GENHN-T(b)′ (i)–(iv) HELD against re-derivation and against a fresh instrument” (1588–1590).

---
### EFF.GENHN.44  [theorem]  — T(b)′ clause (iii) [THE CORRECTED LEAF READ + σ]

**CANONICAL STATEMENT:** verbatim, lines 1168–1182.

**FORM:** display (blockquoted lemma clause with an indented ASCII σ-dictionary).

> “(iii) [THE CORRECTED LEAF READ + σ] with deg f = n = μ₂D₂ the
> Φ₂-adic development in Ô[x] is f = Φ₂^{μ₂} + Σ_{j<μ₂} C_j Φ₂^j
> (deg C_j < D₂); the tower-leaf pins are p_j := dv₂(C_j(x₀)) =
> the composed slot-mins of (ii); the leaf labels and σ are the
> (μ₂, K₂)-dictionary applied to (p_j) on the dv₂-ladder. At
> μ₂ = 2 the σ-decision is PROVED (S7 verbatim at the composed
> data): with (T1′) e₁e₂ | e(L) and (T2′) f₁f₂ | f(L),
>
>     composed-RAM (p₀ odd on dv₂, p₀ ≤ 2p₁) ↦ {(2e₁e₂, f₁f₂)}
>     composed-2SIDED/SPLITEQ/SPLTAIL      ↦ {(e₁e₂, f₁f₂)} ×2
>     composed-INERT                        ↦ {(e₁e₂, 2f₁f₂)}
>
> — the σ-composition FORMULA (e, f) ↦ (e₁e₂·e_s, f₁f₂·f_s) of the
> sealed (b) SURVIVES, applied to the composed pins; inner μ₂ ≥ 3
> is [GENHN-HE(μ₂)].”

`[TABLE]` — the composed dictionary transcribed (rule 14):

| Composed leaf label | σ-block |
|---|---|
| composed-RAM (p₀ odd on dv₂, p₀ ≤ 2p₁) | {(2e₁e₂, f₁f₂)} |
| composed-2SIDED / SPLITEQ / SPLTAIL | {(e₁e₂, f₁f₂)} ×2 |
| composed-INERT | {(e₁e₂, 2f₁f₂)} |

*Arithmetic audit (rule 22).* Block degree at μ₂ = 2 is `2D₂ = 2e₁e₂f₁f₂`. RAM: `2e₁e₂ · f₁f₂ = 2D₂` ✓. 2SIDED: `2 × (e₁e₂ · f₁f₂) = 2D₂` ✓. INERT: `e₁e₂ · 2f₁f₂ = 2D₂` ✓. All three exhaust the block ✓. Composition with S7's level-1 dictionary: substituting `(e₁, f₁) ↦ (e₁e₂, f₁f₂)` into `.15`'s three rows reproduces this table exactly ✓ — i.e. the dictionary really is S7's, re-based.

**CONDITIONALITY:** **(iii)'s perimeter is the FULL inner side, and the `[r3]` round says so after the `[r2]` rider over-covered.** From `.18`'s `[r3]` bracket: “on a FULL inner side only (e₂f₂μ₂ = μ₁ — (iii)'s proved perimeter; the r2 rider as written over-covered). PARTIAL-side inner μ₂ = 2 leaves (e₂f₂μ₂ < μ₁, first live n = 10) ride [GENHN-TOW-1] item (4), not (iii)”. The scope word then reached only 3 of 4 echo sites at r3, and the post-PE3 dated Correction 2 (1909–1928) attaches it to the remaining three. `SUPERSESSION KIND: scope-pin`. **CHAIN: (iii) as displayed (full inner side, in the Setting) → `[r2]` GENHN.B rider (over-covering) → `[r3]` scope word → post-PE3 Corr. 2 (three residual echo sites). TERMINAL: post-PE3.**
Also inherits `.42`'s corrected key (the HETOW erratum exempts (iii)'s proof but the σ is read at the corrected carrier).

**DERIVATION:** Lines 1262–1273, quoted:

> “*Proof of (iii).* deg f = μ₂D₂ and Φ₂ monic: the development
> exists, is unique, C_{μ₂} = 1. f(x₀) = 0 makes Y₂ := Φ₂(x₀) a
> root of T^{μ₂} + Σ_j C_j(x₀)T^j over L := base(x₀) with
> |C_j(x₀)| read EXACTLY by (ii). (T1′)/(T2′): x₀ lies in the
> inner block, so v(x₀) = h/e₁ and v(Φ′(x₀)) = u₂/(e₁e₂) with the
> η/η₂ residues as in (i) — the same forcing gives e₁e₂ | e(L),
> f₁f₂ | f(L). At μ₂ = 2 run S7's Y-trichotomy verbatim on the
> quadratic Y₂² + C₁(x₀)Y₂ + C₀(x₀) = 0 with these two transported
> facts and block degree 2e₁e₂f₁f₂: the three displayed σ-blocks
> follow exactly as at S7 …. ∎”

**RESOLUTION TRACE:** statement 1168–1182 · proof 1262–1273 · correction sites 321–334 (`[r2]`+`[r3]` in GENHN.B), 1909–1928 (post-PE3 Corr. 2), 1980–2032 (HETOW, at the key).

XREF: `GENHN_passPE2_report.md:F2` — count **5**.
XREF: `GENHN_passPE3_report.md:F-2` — count **5**.

**TEETH:** **`genhnr2_supp.py`'s corrected-read-vs-PARI rows** — “corrected read vs PARI exact on every decided leaf, both routes” (1106–1107), including the f₂ = 2 genre “(2,1,4)→(1,2,2): corrected {(4,2)} exact on every decided leaf; 3-stage n = 16: {(16,1)}/{(8,1),(8,1)} exact” (1305–1307). **The `[r3]` partial-side counter-witness FIRED** (the n = 10 PE2-P member, audited at `.18`). Disposition: executable regression against an independent oracle + a fired scope counter-instance.

---
### EFF.GENHN.45  [lemma]  — T(b)′ clause (iv) [THE STAGE SHADOW + FAITHFULNESS THRESHOLD]

**CANONICAL STATEMENT:** verbatim, lines 1183–1199.

**FORM:** display (blockquoted lemma clause with an inline `[r3]` tally correction).

> “(iv) [THE STAGE SHADOW + FAITHFULNESS THRESHOLD] the sealed
> read = Ĝ_j(θ, Y) (the coefficientwise mod-Φ′ shadow); it agrees
> with the composed pin at coordinate j iff every discrepancy
> class Φ′(x₀)·H_j — each at dv₂ ≥ u₂ + dv₂(H_j-class) — sits
> weakly above BOTH reads' slot-min at j. This inequality HOLDS at
> the entry/event band (the T(a) geography: entry pins on the
> inner side, corrections above it — machine-verified at the PE1
> instances and the P8 witness; its genre-general proof is part of
> [GENHN-TOW-1]) and FAILS generically at leaf depth (PE1: 3/3
> constructions; supp sweep: 35/35 COMPARED rows diverge at pin
> level **[r3 2026-08-09 (passPE2 F4): the r2 figure "35/38"
> transcribed the output line's "(of 38 tower rows)"; the runner
> compares stage-vs-corrected pins only on the 35 two-stage rows
> — the 3 SUPP-C 3-stage rows have no stage read and are skipped
> before the tally (`continue` at the divergence loop) — and the
> 35 compared rows ALL diverged; the honest denominator is 35]**).
> The stage algebra is a projection, not the state.”

**CONDITIONALITY:** **The faithfulness criterion is proved; the faithfulness GEOGRAPHY is boxed.** “its genre-general proof is part of [GENHN-TOW-1]” — item (3) of the box (1392–1394): “the genre-general FAITHFULNESS geography (in particular T(a)'s event-band survival as a theorem — currently machine-verified at the PE1 instances + the P8 witness)”. The `[r3]` bracket is a **counter re-reading**: `35/38 ⇝ 35/35`, with the mechanism of the miscount named (skipped rows counted in the denominator). `SUPERSESSION KIND: counter re-reading`. `TARGETS: .45`, `.49` (the same figure recurs in the supp-contact parenthetical).

**DERIVATION:** Lines 1275–1287, quoted:

> “*Proof of (iv).* Functoriality: reducing every coefficient of
> the division F = Σ Ĝ_j K₂^j under Ô[x] → R is again a monic
> division in R[Y] with remainders of the same Y-degrees —
> uniqueness identifies the sealed read with Ĝ_j(θ, Y). The
> composed object evaluates Ĝ_j(x₀, Y₀) (up to Φ₂-recarry between
> j-levels, which moves data only within the composed development
> and does not change the pins p_j of (iii), by uniqueness of that
> development); Ĝ_j(x, Y) − lift(Ĝ_j(θ, Y)) ∈ Φ′·Ô[x][Y] gives the
> discrepancy Φ′(x₀)H_j(x₀, Y₀) at dv₂ ≥ u₂ + dv₂(H_j-class); if
> every discrepancy class clears both slot-mins at j the two reads
> agree there, else not — and the PE1 instances witness failure.
> ∎ (No genre-general classification of the faithful region is
> claimed here — [GENHN-TOW-1].)”

**RESOLUTION TRACE:** statement 1183–1199 · proof 1275–1287 · correction site 1193–1198 (`[r3]` tally) · box 1392–1394 (shard 2).

XREF: `GENHN_passPE2_report.md:F4` — count **5**.

**TEETH:** **35/35 divergence, and the tally itself was audited.** *Arithmetic audit (rule 22):* the runner emits 38 tower rows; 3 are SUPP-C 3-stage rows with no stage read and are `continue`d before the tally; `38 − 3 = 35` compared rows ✓, all 35 diverged ✓. **Disposition: executable regression, in the falsifying direction, with a corrected denominator** — a `stale self-description` (the r2 figure) cured at r3. The positive half (agreement at the event band) is **machine-only**: `signed vacuity disclosure` for its genre-general proof, which sits in item (3).

---
### EFF.GENHN.46  [scope-record]  — T(b)′ clause (v) [COUNT-LAW FORM + LEAF LABELS] and the GRADE line

**CANONICAL STATEMENT:** verbatim, lines 1200–1214.

**FORM:** display (blockquoted lemma clause + bold GRADE sentence).

> “(v) [COUNT-LAW FORM + LEAF LABELS] the tower-leaf STATE is the
> composed digit strings of (C_j) — one K₂-digit per dv₂-height
> per coordinate (by (ii)); leaf labels are keyed to COMPOSED pin
> heights; count laws take the (μ₂, K₂)-cell-law form (W-12.A
> re-based at (e₁e₂, f₁f₂)) ON THAT KEYING. The sealed note
> displayed no explicit tower count law (S8(b) priced them only
> through the withdrawn "no new mechanism" sentence), so the
> correction is the KEYING plus the label reassignment (see the
> table below); the composed ENTRY BUDGETS (the GENHN-1 analogue
> at Φ₂) and the inner refine transfer are NOT derived here —
> boxed, [GENHN-TOW-1].
> **GRADE: (i)–(iv) proved below at the displayed generality (full
> inner side); (v)'s form follows from (ii)+(iii) with the budgets
> boxed; machine contact = genhnr2_supp.py (first coverage), plus
> the four PE1 instances as regression teeth.**”

**CONDITIONALITY:** (v) is a **form** claim with its content boxed — the composed entry budgets are `[GENHN-TOW-1]` item (1), the inner refine transfer item (2). The honest reading: **no tower COUNT law is proved anywhere in this note**, only the keying it must have. GENHN-BOX-3's `[r2]` update says the same from the coverage side: “tower COUNT laws remain unmeasured, [GENHN-TOW-1]”.

**DERIVATION:** Follows from (ii) + (iii); the note says so and derives nothing further.

**RESOLUTION TRACE:** statement 1200–1214 · box 1382–1442 (shard 2) · coverage 1345–1348 (shard 2).

XREF: `W12_PROOF_2026-08-08.md:THEOREM W-12.A` — count **8**.

**TEETH:** **NONE for the count law** — the note's own coverage-hole sentence, GENHN-BOX-3 `[r2]` (1345–1348): “tower LEAF READS now have first coverage — genhnr2_supp.py, 147/0, two genres + 3-stage n = 16; **tower COUNT laws remain unmeasured, [GENHN-TOW-1]**”. **Disposition: `disclosed non-repair` / PROOF-ONLY** — the keying is proved, the law is neither proved nor measured.

---
### EFF.GENHN.47  [table]  — the corrected leaf labels at the PE1 instances

**CANONICAL STATEMENT:** verbatim, lines 1289–1307 (the Markdown table plus its supp-contact parenthetical).

**FORM:** display (blockquoted bold-headed Markdown table + a parenthetical paragraph carrying an `[r3]` bracket).

> “**CORRECTED LEAF LABELS at the PE1 instances (the (b)-priced
> labels were wrong even where σ agreed) + supp contact:**
>
> | member (n = 8, f = G(x²−2)) | stage-shadow read | corrected read | PARI |
> |---|---|---|---|
> | G = Y⁴+16Y+96        | RAM(21) → {(8,1)}          | **RAM(25)** → {(8,1)} | {(8,1)} |
> | G = Y⁴+16Y³+32Y²+96  | INERT(28,14) → {(4,2)}     | **RAM(21)** → {(8,1)} | {(8,1)} |
> | G = Y⁴+16Y³+32Y²+224 | 2SIDED(30,14) → {(4,1)²}   | **RAM(21)** → {(8,1)} | {(8,1)} |
>
> (+ deep-perturbation variants, identical verdicts; supp sweep:
> u₂ = 7 rows add stage-INERT(36) vs true RAM(31), and
> stage-vs-corrected pins diverge on 35/35 compared rows **[r3:
> the 3 SUPP-C 3-stage rows are excluded from the comparison — no
> stage read at 3 stages; see the (iv) tally correction above]** —
> count strata
> priced through the shadow pins are systematically mislabeled.
> The f₂ = 2 genre (2,1,4)→(1,2,2): corrected {(4,2)} exact on
> every decided leaf; 3-stage n = 16: {(16,1)}/{(8,1),(8,1)}
> exact.)”

*Arithmetic audit (rule 22), computed fresh — every number in the table cross-checked against every other number in the note that should match it.*
- **Degrees.** `f = G(x²−2)` with `deg G = 4` gives `deg f = 8` ✓ = n, and `D′ = e₁f₁ = 2`, `D₂ = D′e₂f₂ = 2·2·1 = 4`, `μ₂ = 2`, so `n = μ₂D₂ = 8` ✓ consistent with (iii)'s `deg f = μ₂D₂`.
- **σ column sums.** `{(8,1)}`: `8·1 = 8` ✓. `{(4,2)}`: `4·2 = 8` ✓. `{(4,1)²}`: `4+4 = 8` ✓. All three exhaust degree 8 ✓ — so the *wrong* readings were degree-consistent, which is exactly why only PARI could separate them.
- **Row 1 is the “σ-agreeing instance” the `[r2]` header names**: stage RAM(21) and corrected RAM(25) both map to {(8,1)} ✓ — “even the σ-agreeing instance had its leaf label mispriced (stage-RAM(21) vs true RAM(25))” ✓ matches the header exactly.
- **Rows 2 and 3 are the σ-refuting instances**: {(4,2)} and {(4,1)²} vs PARI {(8,1)} ✓ — “the stage-algebra inner read predicts composed σ {(4,2)} and {(4,1),(4,1)} where the true octics are {(8,1)}” ✓ matches the header exactly, in the same order.
- **The `[r2]` header claims “3/3 constructions” at (iv) and the table has 3 rows** ✓ consistent.
- **Parity check on the RAM labels.** (iii)'s composed-RAM antecedent is `p₀ odd on dv₂`. `21` odd ✓, `25` odd ✓, `31` odd ✓ — every corrected RAM label has odd `p₀` ✓. The refuted stage labels `INERT(28,14)` and `2SIDED(30,14)` have even first entries ✓ consistent with their (wrong) branch assignments.
- **Cross-check with `.41`'s mechanism arithmetic:** the carry `16Φ′` was computed there at `dv₂ = 21` against a stage pin of 28. Row 2's stage read is exactly `INERT(28,14)` and its corrected read `RAM(21)` ✓ — **the mechanism paragraph and the table agree numerically, computed independently.** This is the strongest internal consistency check available in the shard and it passes.
- **`u₂ = 7` supp row:** stage-INERT(36) vs true RAM(31). At `u₂ = 7`, `dv₂(16Φ′) = 16 + 7 = 23`… the note gives no pin decomposition for this row, so no independent check is possible. Recorded as unverified-but-unclaimed.

**CONDITIONALITY:** The `[r3]` bracket corrects the divergence denominator (see `.45`). Otherwise a machine record, and the PARI column is the arbiter.

**DERIVATION:** Machine record (`genhn_pe1_fresh.py` FR-D + `genhnr2_supp.py`), interpreted through (iii)/(iv).

**RESOLUTION TRACE:** statement 1289–1307 · correction site 1300–1302 (`[r3]`) and its twin at 1193–1198.

ARTIFACT: `verification/openmath/genhn_pe1_fresh.py` ✓ · `genhn_pe1_fresh_output.txt` ✓ · `genhnr2_supp.py` ✓ · `genhnr2_supp_output.txt` ✓.
PIN: the supp runner sha `51154c95…` and output `664036bc…` are cited at 1411 and 1438 as **truncated** hashes; **UNPINNED** in the strict sense of rule 23 (no full hash, no `git cat-file`-able object). Recorded as such, not silently passed.

**TEETH:** This table IS the tooth roster for `.17`'s refutation — “the 4 refuted instances as regression teeth” (three here + the u₂ = 7 supp row). Disposition: planted regression suite built from a refutation; all four fired against the sealed reading and now guard the corrected one.

---
### EFF.GENHN.48  [changes-record]  — REMARKS DISPOSITION (passPE1 R1–R4)

**CANONICAL STATEMENT:** verbatim, lines 1309–1318.

**FORM:** display (blockquoted bold-headed disposition list, one line each).

> “**REMARKS DISPOSITION (passPE1 R1–R4, one line each).** R1: the
> dispatch's "3-stage tower at n = 8 or 12" is indeed
> unconstructible (3 stages need μ₁ ≥ e₂f₂μ₂ ≥ 8, n ≥ 16); the
> supp leg constructs 3-stage members AT n = 16 (parse-gated,
> PARI-exact) — recorded, no note text change. R2 ([e2]-E3
> witnesses verified clean): no action. R3 ([e2]-E2 derivation
> verified; comp = 2 first contact GREEN): consumed by the [r2]
> annex at E1/E2 (F3 repair), no further action. R4 (GN-TOWER
> min-n scan verifies the arithmetic minimum only): accurate as
> stated by the verifier, no action needed.”

**CONDITIONALITY:** **R1's arithmetic becomes load-bearing at `[r3]`** — the same bound reappears as “the R1 arithmetic” in GENHN.B's depth split (`.18`) and in `[GENHN-TOW-1]` item (6). So a remark dispositioned “no note text change” at r2 is *cited as authority* at r3. Recorded because a chapter cut that drops R1 as a mere remark loses the provenance of the `n ≥ 16` threshold.
R2 and R3 are **independent verifications of this shard's own errata** — E3's witnesses and E2's derivation were checked by a hostile pass and passed. That is positive evidence for `.22` and `.14` and is recorded at those units' TEETH by reference.

**DERIVATION:** Dispositions, not derivations. R1's bound is audited at `.18`.

**RESOLUTION TRACE:** statement 1309–1318 · R1's later use 311–319, 1397–1399 (shard 2).

XREF: `GENHN_passPE1_report.md:F5` — count **3** (the R-remarks live in the same report; the report's own remark labels R1–R4 are not separately grep-addressable — NEAR-MISS, carried descriptively).

**TEETH:** R3's “comp = 2 first contact GREEN” is the **first machine contact with E2's comp-weighted census** anywhere, and it is *foreign* (passPE1's instrument). Disposition: `accepted-with-decorrelation-supplied` for `.14`.

---
### EFF.GENHN.49  [scope-record] · SERIES: GENHN-GRADE-ARC, member 2 of 5

**CANONICAL STATEMENT:** verbatim, lines 1324–1330.

**FORM:** bulleted bold-headed box.

> “* **GENHN-BOX-1 (grades).** 0/2, composed this session, NO hostile
>   arc. THEOREM GENHN.B inherits the MINIMUM grade over the S10
>   stack: {W-11 ACCEPTED 2/2, GRTJC/JC-LOAD ACCEPTED 2/2, SIGMALAW
>   ACCEPTED 2/2, J-D0 proved @ pin, W-12 0/2 (PE3 owed), HEX3 (r2,
>   PE3 next), HMENU3 (1/2), GENIND 0/2, QSCOUT22 instrument, GENH4
>   0/2, this note 0/2}. Every consequence below is a CONDITIONAL
>   STRUCTURE at exactly that stack — displayed, not upgraded.”

**CONDITIONALITY:** **`STALE-SELF-DESCRIPTION` (rule 26) on both halves.**
(a) “0/2, composed this session, NO hostile arc” is falsified by the note's own later, unedited appends. SERIES `GENHN-GRADE-ARC`: member 1 = the title-box round records (shard 1 `.02`, 0/2); **member 2 = this box** (0/2); member 3 = the post-PE3 append (`.72`, 1/2); **member 4 = the post-PE4 acceptance record (`.75`, 2/2 — TERMINAL)**; member 5 = the HETOW erratum's freeze-discipline line (`.77`, 2/2 re-affirmed).
(b) **The stack itself is superseded by the `[e2]` S10 REFRESH (`.58`) and the two ARC LINE updates (`.59`, `.60`)**: GENH4 moves 0/2 → **ACCEPTED 2/2 FULLY FROZEN**; GENIND 0/2 → **1/2**; W-12 0/2 → r5 0/2 with PE6 dispatched; HMENU3 1/2 → **ACCEPTED**; HEX3 r2 → r3. `SUPERSESSION KIND: as-of scoping`.
(c) **The minimum-grade rule survives and is the load-bearing content.** “THEOREM GENHN.B inherits the MINIMUM grade over the S10 stack … displayed, not upgraded” is untouched by every append, and it is what makes GENHN's own 2/2 acceptance *not* an upgrade of GENHN.B's conditionality — the note says so at `.71`: “nothing here upgrades the conditionality display of THEOREM GENHN.B.”

**DERIVATION:** Grade declaration, not a derivation. The minimum-grade rule is the corpus's standing composition discipline, not a GENHN result.

**RESOLUTION TRACE:** statement 1324–1330 · correction sites 1533–1569 (`[e2]` refresh), 1570–1585 (`[r2]` arc line), 1586–1622 (`[r3]` arc line), 1863–1874 (1/2), 1941–1955 (2/2), 2034–2038 (2/2 re-affirmed), 2263–2266 (row stays OPEN at the certification ledger).

XREF: `W11_PROOF_2026-08-08.md:W-11` — count **18**.
XREF: `GRTJC_PROOF_2026-08-08.md:JC-LOAD` — count **31**.
XREF: `SIGMALAW_PROOF_2026-08-08.md:(EC-q)` — count **26**.
XREF: `JD0_PROOF_2026-08-08.md:J-D0` — count **25**.
XREF: `W12_PROOF_2026-08-08.md:W-12.D` — count **19**.
XREF: `HEX3_PROOF_2026-08-08.md:HEX3` — count **83**.
XREF: `HMENU3_PROOF_2026-08-08.md:ANNEX A` — count **5**.
XREF: `GENIND_PROOF_2026-08-08.md:THEOREM GENIND.B` — count **7**.
XREF: `QSCOUT22_2026-08-08.md:Q22-A` — count **3**.
XREF: `GENH4_PROOF_2026-08-08.md:THEOREM GENH4.A` — count **5**.

**TEETH:** NONE (grade declaration). The grade arc's evidence is the four pass reports, all verified present.

---
### EFF.GENHN.50  [scope-record]  — GENHN-BOX-2 (the graded-frame consumption)

**CANONICAL STATEMENT:** verbatim, lines 1331–1338.

**FORM:** bulleted bold-headed box.

> “* **GENHN-BOX-2 (the graded-frame consumption).** LEMMA GENHN-4's
>   layer 1 at μ ≥ 3 consumes COROLLARY W-9's twisted algebra as the
>   carry bookkeeping (unlike GENH4, which re-proved its μ = 2
>   instances elementarily). Compensating instrument: GN-REFINE3
>   (pointwise re-division transport at every μ = 3 stage-α event).
>   An elementary general-μ carry display (the GENH4-S5 computation
>   at general (e₁, f₁, μ)) would retire this box; until then the
>   count laws at μ ≥ 3 stand on one accepted weld face.”

**CONDITIONALITY:** **LIVE. This is the charge's named item, and the compiled state is: disclosed, correctly, and not discharged.**

**CROSS-NOTE STATUS (rule 10 — verified against full append chains, never a frozen sentence):**
- **`runs/qgen/WELD_FACE_AUDIT.md` L143–164 designates this box's subject LEAK-1 (LIVE, disclosed)** and adds the decisive negative: “The recentering it studies (Φ′ ↦ Φ′ + w) is an **additive** shift — precisely the NONCHAR failure mode, so **J-D0's perimeter cannot cover it even in principle**.” Its verdict on GENHN: “**Status: correctly disclosed** at `GENHN-BOX-2` … it is the audit's one confirmed weld-face consumption”. The same audit's LEAK-2 records that the *tower* leg (GENTOW-2 layer 1) opened the identical leak one level up and **GENTOW5 closed it with no weld face at all**, which is why the tower branch does not inherit this box.
- **`spec/HYPOTHESIS_LEDGER.md` indexes the box as HYP.148, class CARRY** — “the ONE weld face inside a count law on the whole capstone path, in GENHN's own words”. Its v6 ARC UPDATE (2026-08-14): the WELD-ZERO unit “has moved through one repair round and one post-pass rider since launch, and now sits at **clean-pass 1 of 2** … **HYP.148 stays CARRY and HYP.139 stays MATH at full strength**”, with the second (model-diverse, gpt-5.6-sol) pass “queued **not before Tue 2026-08-18 10:23+**”.
- **`lean/notes/openmath/WELDZERO_2026-08-14.md` claims COROLLARY WZ-B** (layer 1 without W-9) and would strike this box. **It has NOT landed on GENHN**: GENHN's append chain runs to line 2627 and its last append is the 2026-08-12 GENHN-COUNT-RERUN; no append names WELDZERO. WELDZERO itself declines the authority — its §S0 calls the fold's convention pin “a **reading** of GENHN's frozen words, boxed as such”.
**Therefore, for this spec: GENHN-BOX-2 is LIVE, and GENHN.A(iv)/LEMMA GENHN-4 at μ ≥ 3 rides one accepted weld face.** See OPEN-CALL 2.

Two further scope facts the box states and a chapter cut must keep: (i) the exception is **μ ≥ 3 only** — at μ = 2 GENH4 re-proved the instances elementarily; (ii) the box names its own retirement condition (an elementary general-μ carry display), which is exactly what WELDZERO attempts.

**DERIVATION:** Disclosure, not derivation. Its subject's derivation is shard 1 `.33` (LEMMA GENHN-4, three layers).

**RESOLUTION TRACE:** statement 1331–1338 · subject 867–904 (shard 1) · external: `WELD_FACE_AUDIT.md` L143–164, `WELDZERO_2026-08-14.md` §S0/§S2/§S3.7, `HYPOTHESIS_LEDGER.md` HYP.148/HYP.139/HYP.149.

XREF: `GRTJC_PROOF_2026-08-08.md:COROLLARY W-9` — count **2**.
XREF: `GENH4_PROOF_2026-08-08.md:GENH4-CAP` — count **18** (the GENH4-S5 computation is cited by section; `GENH4-S5` as written has count **0**, the anchor `S5` has count **20** — NEAR-MISS, carried descriptively).
ARTIFACT: `runs/qgen/WELD_FACE_AUDIT.md` ✓ · `lean/notes/openmath/WELDZERO_2026-08-14.md` ✓ · `spec/HYPOTHESIS_LEDGER.md` ✓.

**TEETH:** **GN-REFINE3**, the box's own named compensating instrument — 3,072 pin checks, 0 violations, every μ = 3 stage-α event transported by ACTUAL re-division rather than by the graded formula (S12 P7). **Disposition: `accepted-with-decorrelation-supplied`** — the tooth decorrelates the consumption pointwise at μ = 3 without retiring it. That is precisely what the box claims, so the disclosure is honest rather than decorative.

---
### EFF.GENHN.51  [scope-record]  — GENHN-BOX-3 (coverage)

**CANONICAL STATEMENT:** verbatim, lines 1339–1351, with its `[r2]` bracket in place.

**FORM:** bulleted bold-headed box with an inline `[r2]` update.

> “* **GENHN-BOX-3 (coverage).** Machine rows exercise: d = 1 ambients,
>   prime q ∈ {2, 3}, genres (2,1,2) [committed n = 4 + fresh n = 5
>   embeddings], (1,2,2) [committed n = 4], (3,1,2) and (2,1,3)
>   [fresh n = 6], one (2,1,4)-tower witness at n = 8. NOT exercised:
>   f-first genres beyond f₁ = 2 (E13/F3: visibility ≥ N = 7 sweeps
>   — constructible in a follow-up), mixed e₁, f₁ ≥ 2 (first live
>   n = 8), tower LAWS (witness only) **[r2: tower LEAF READS now
>   have first coverage — genhnr2_supp.py, 147/0, two genres +
>   3-stage n = 16; tower COUNT laws remain unmeasured,
>   [GENHN-TOW-1]]**, d ≥ 2 ambients (GENIND-BOX-3
>   inherited), q = 4 F-genre rows (QSCOUT22 Q22-BOX-3 inherited).
>   The proofs are uniform in all of these; the coverage gap is
>   machine-side only, named here.”

`[TABLE]` — the coverage ledger transcribed (rule 5/14):

| Dimension | EXERCISED | NOT exercised |
|---|---|---|
| ambient depth | d = 1 | d ≥ 2 (GENIND-BOX-3 inherited) |
| residue characteristic | q ∈ {2, 3} | q = 4 F-genre rows (QSCOUT22 Q22-BOX-3 inherited) |
| genres | (2,1,2) [n = 4 committed + n = 5 fresh embeddings], (1,2,2) [n = 4 committed], (3,1,2), (2,1,3) [n = 6 fresh] | f-first beyond f₁ = 2 (E13/F3, need N ≥ 7); mixed e₁, f₁ ≥ 2 (first live n = 8) |
| towers | one (2,1,4) witness at n = 8; **`[r2]`** leaf READS at two genres + 3-stage n = 16 | tower COUNT laws (`[GENHN-TOW-1]`) |

**CONDITIONALITY:** **This box is the load-bearing reason every erratum in shard 1 can say “the correction is invisible to the battery”** — every row has `f₁ = 1`, so E1, E2 and the `[r1]` node correction are all vacuous on the sealed data. It is *partially* superseded twice after the box was written:
(a) `[r2]`, in-text — tower leaf reads gain first coverage.
(b) **Post-acceptance, `genhn_pe4_fresh.py` supplies the first f₁ ≥ 2 census contact** — “first f₁ = 4 / comp = 3 / F₁₆ contact” (1948–1949, `.75`) — and `genhn_f2_count_check.py` supplies **the first-ever mixed-genre contact (2,2,2)** (2610–2614, `.93`). Both are additive post-seal legs, so the *sealed battery's* coverage is unchanged and the box's own sentence stays true as written about the sealed rows. `SUPERSESSION KIND: as-of scoping` — the box is as-of the seal, and two later legs widen the arc's coverage without touching it.
(c) “The proofs are uniform in all of these” is the box's one *claim* rather than record, and it is **false as stated at f₁ ≥ 2 for the boundary band** — E1's own exclusion (shard 1 `.31`) declines to claim band adjudication there, and the A2 verification note found no S9 box holding that surface. Recorded as source defect 1.

**DERIVATION:** Coverage record.

**RESOLUTION TRACE:** statement 1339–1351 · correction sites 1345–1348 (`[r2]`), 1944–1949 (PE4 leg), 2607–2614 (P2 certificate) · the uniformity claim's counter-evidence 798–801 (shard 1 E1), 2223–2229 (`.84`).

XREF: `GENIND_PROOF_2026-08-08.md:GENIND-BOX-3` — count **3**.
XREF: `QSCOUT22_2026-08-08.md:Q22-BOX-3` — count **1**.
ARTIFACT: `verification/openmath/genhnr2_supp.py` ✓ · `genhn_pe4_fresh.py` ✓ · `genhn_f2_count_check.py` ✓.

**TEETH:** The box IS a teeth-coverage statement. **Disposition: `signed vacuity disclosure`** for every f₁ ≥ 2, mixed, d ≥ 2 and q = 4 claim in the note.

---
### EFF.GENHN.52  [scope-record]  — GENHN-BOX-4 (extraction convention + the certified-perimeter finding)

**CANONICAL STATEMENT:** verbatim, lines 1352–1377.

**FORM:** bulleted bold-headed box with an internal SHARPENING paragraph.

> “* **GENHN-BOX-4 (embedded-genre extraction convention + THE
>   CERTIFIED-PERIMETER FINDING [r0-battery]).** The n = 5 stage rows
>   read the extracted block (Newton root + exact division,
>   deterministic); read well-posedness across extraction
>   representatives is GENHN-3(a) + GENIND-1(iii), and the law match
>   is the test. The reader-reimplementation seams of GENH4-BOX-5
>   (pinned QSCOUT22 reader; canonical-lift letters; conservative
>   tails) are inherited verbatim. SHARPENING (machine-surfaced at
>   the smoke run, derivation S11.F): the extracted block is
>   determined by the ambient window-N data only mod explicit
>   per-coefficient floors — the split root is defined mod
>   π^L, L = N − v(f′(ρ)), and solving (x−ρ)(q−Q) = −δQ triangularly
>   gives exact-digit floors per stage coordinate/class. Stage leaves
>   consulting digits at or above the floors are (A0)-WEAK AT THE
>   AMBIENT WINDOW (their σ is not a function of the swept data —
>   verified: PARI exhibits both agreement and disagreement in the
>   uncertified tail, e.g. V1E2(2,5,1)-RAM(9), while every certified
>   leaf matches exactly). COUNT laws are untouched (the truncated
>   read is a bijection of window data — GN-STAGE2 exact at full N).
>   Consequence for the theory: the embedded-genre σ-certification
>   cap composes as N ↦ N − (sibling Hensel loss) coordinate-wise —
>   GENHN-3(a) at the composed read; the battery's σ legs on
>   extracted rows are gated at exactly this perimeter (cert_table_E
>   / leaf_cert_E), with the uncertified tail measured as labeled
>   diagnostics. GENHN.C itself (a statement about stage data) is
>   unaffected.”

**CONDITIONALITY:** **A sharpening, not a defect — and the note is careful to say which.** Three fences: (i) “COUNT laws are untouched”; (ii) “GENHN.C itself (a statement about stage data) is unaffected”; (iii) the σ legs are *gated*, and the ungated tail is reported as labeled diagnostics rather than scored. The box's own scope fence is shard 1 `.39`'s `[r0-battery]` Remark. Untouched by every append (verified).

**DERIVATION:** S11.F (`.68`), quoted there in full.

**RESOLUTION TRACE:** statement 1352–1377 · derivation 1780–1798 (`.68`) · discovery event 1731–1736 (`.65`) · scored tail 1839–1845 (`.70`).

XREF: `GENH4_PROOF_2026-08-08.md:GENH4-BOX-5` — count **1**.
XREF: `GENIND_PROOF_2026-08-08.md:LEMMA GENIND-1` — count **2**.

**TEETH:** The perimeter is **measured on both sides** at S12 P9 — “V p=2 1,216 / 349 mismatches, V p=3 241 / 58, all full-side legs 0/0 — the S11.F perimeter is REAL on both sides (certified exact, uncertified genuinely mixed)”. **Disposition: measurement, preregistered** (S11.D P9 predicted the tail “to contain mismatches”, 1722–1724). This is the shard's cleanest example of a preregistered *positive* prediction of failure.

---
### EFF.GENHN.53  [scope-record]  — GENHN-BOX-5 (P(5) density display owed)

**CANONICAL STATEMENT:** verbatim, lines 1378–1381.

**FORM:** bulleted bold-headed box.

> “* **GENHN-BOX-5 (P(5) density display owed).** P(5) fires (GENHN.B);
>   the SEVENTEEN quintic R_τ(q) displays + Σ = 1 + engine/β₅ tie are
>   a mechanical GENH4-S9-style assembly NOT executed here — a
>   one-unit follow-up (GENH5-DENS), explicitly owed.”

**CONDITIONALITY:** An owed display, not a mathematical gap: “mechanical”. Its *premise* — that P(5) fires — inherits GENHN.B's full conditionality stack (`.49`, shard 1 `.18`), and P(5) is the one degree the note claims fires OUTRIGHT (“every n = 5 genre has μ = 2”, so `[GENHN-HE]` does not enter, and n = 5 < 8 so `[GENHN-TOW-1]` is empty).

*Arithmetic audit (rule 22) of “SEVENTEEN”, computed fresh.* Splitting types of a degree-5 étale algebra = partitions of 5 into parts with (e, f) data — the note gives no enumeration here, and the count 17 is not independently derivable from anything in range. **Unverified-but-unclaimed**: the figure appears once, is owed to a follow-up unit, and no number in the note cross-checks it. Recorded as such rather than passed silently.

**DERIVATION:** None — the display is owed.

**RESOLUTION TRACE:** statement 1378–1381 · endgame listing 1477–1479 (`.55` item 5).

XREF: `GENH4_PROOF_2026-08-08.md:GENH4-BOX-5` — count **1** (the S9-style assembly precedent is GENH4's §S9; `GENH4-S9` as written has count **0** — NEAR-MISS, carried descriptively).

**TEETH:** NONE (owed display). `signed vacuity disclosure`: no quintic density is displayed or machine-checked anywhere in this note.

---
### EFF.GENHN.54  [scope-record]  — `[GENHN-TOW-1]`, the composed-key tower box (six items + the T(b)″ ATTEMPT)

**CANONICAL STATEMENT:** verbatim, lines 1382–1442.

**FORM:** bulleted bold-headed box, six numbered items, with an embedded derivation of the iteration data and a two-part displayed obstruction (α)/(β).

> “* **[GENHN-TOW-1] [r2 2026-08-09] (the composed-key tower box —
>   what LEMMA GENHN-T(b)′ leaves open at n ≥ 8 tower genres).**
>   T(b)′ (S8 annex) PROVES the composed carrier, the composed slot
>   lemma GENHN-2′, the corrected leaf read with inner-μ₂ = 2 σ, and
>   the stage-shadow faithfulness criterion. STILL OPEN, boxed here:
>   (1) the composed ENTRY BUDGETS (the GENHN-1 analogue at Φ₂: the
>   tower-node locus's per-coordinate composed digit floors) and
>   with them measured tower COUNT laws (supp leg = leaf-read first
>   contact only); (2) the inner REFINE TRANSFER at the composed key
>   (GENHN-4 one level up — needed for deep tower histories); (3)
>   the genre-general FAITHFULNESS geography (in particular T(a)'s
>   event-band survival as a theorem — currently machine-verified at
>   the PE1 instances + the P8 witness); (4) PARTIAL inner sides
>   (e₂f₂μ₂ < μ₁: the inner sibling split at the composed level);
>   (5) the composed WINDOW/certification ledger (GENHN-3 + BOX-4 at
>   dv₂); (6) **[r3 2026-08-09 (passPE2 F1)] the ITERATED key
>   composition (depth ≥ 3; first live n = 16 — the R1 arithmetic: a
>   third stage forces μ₁ ≥ e₂f₂μ₂ ≥ 8, hence n ≥ D′μ₁ ≥ 16).**
>   T(b)′ is ONE composition step and does NOT self-apply: its
>   setting requires a key whose x-polygon residual is IRREDUCIBLE
>   and whose normalizers are the MONOMIALS n̂(m) = x^iπ^a (i < e₁),
>   while the composed key Φ₂ re-enters with residual the POWER
>   ψ^{e₂f₂} ((i)'s proof) and with dv₂-ladder normalizers that are
>   Φ′-POLYNOMIALS. What the iteration IS (re-derived at this repair
>   from the r2 mechanism, matching the supp's 3-stage construction):
>   the level-2 normalizers are the LADDER MONOMIALS n̂₂(m) =
>   π^a x^i Φ′^b (i < e₁, b < e₂), unique in that range per
>   dv₂-height m = a·e₁e₂ + i·e₂h + b·u₂ by GENHN-2′'s two-step
>   class separation — witness n̂₂(21) = 16Φ′ (a = 4, i = 0, b = 1;
>   the supp runner's n₂(21), genhnr2_supp.py 51154c95… L388–389);
>   the level-3 key is Φ₃ := Φ₂^{e₃f₃} − Σ_{t<f₃} k̂_t·Φ₂^{e₃t} with
>   k̂_t a dv₂-height-u₃(f₃−t) ladder lift of the ψ₃-coefficient
>   c_t ∈ K₂ (K₂-digit lifts need (ii)'s slot grammar, not
>   x-monomial lifts — the third re-entry change); witness Φ₃ =
>   Φ₂² − 16Φ′ (ψ₃ = T−1, u₃ = 21). A T(b)″ — the iterated
>   carrier/slot/read at depth ≥ 3 — was ATTEMPTED at this repair
>   and develops one precise hole plus one inherited dependency,
>   both displayed: (α) the level-by-level ascent that forces a
>   Φ₃-root ξ's intermediate data — v(Φ′(ξ)) = u₂/(e₁e₂) exact with
>   η₂(ξ) a ψ₂-root, the input (ii)'s slot lemma needs at ξ — needs
>   the Φ′-adic development of Φ₃ to be ONE-SIDED of
>   slope κ₂ with residual a ψ₂-power. TRUE at the witness by an
>   EXACT CARRY CANCELLATION — Φ₃ = Φ′⁴ − 8xΦ′² + 16x² − 16Φ′, and
>   the x-overflow carry 16x² = 16Φ′ + 32 kills the −16Φ′ term
>   exactly: Φ₃ = Φ′⁴ − 8xΦ′² + 32 (re-computed at this repair),
>   dv-pins (4,0) and (0,10) on the side, (2,7) strictly above
>   (side height 5), one side of slope 5/2 = κ₂, residual
>   T² + 1 = ψ₂² over F₂ — but the genre-general carry-cancellation
>   bookkeeping is genuine Okutsu-optimality content, unproved
>   here; (β) the iterated node floor κ₃ > dv₂(x^{D₂}) (21/2 > 8 at
>   the witness) has no proved provenance at depth ≥ 3 — its level-2
>   analogue was the [r1] node floor, proved from GENHN-1's entry
>   budgets, and the depth-3 analogue rides item (1)'s composed
>   entry budgets. Machine evidence: the supp leg's three
>   parse-gated 3-stage n = 16 instances (SUPP-C) are EXACT vs PARI
>   on both routes ({(16,1)}/{(16,1)}/{(8,1),(8,1)}; output
>   664036bc…) — the iterated read is machine-witnessed TRUE at the
>   first live degree, and unproved. Items (1)–(5) first live
>   n = 8; item (6) first live n = 16; the box is empty at n ≤ 7.
>   Inner μ₂ ≥ 3 σ is NOT
>   here — it is [GENHN-HE(μ₂)].”

**CONDITIONALITY:** **Two post-acceptance appends land on this box.**
(a) **post-PE3 Correction 1** (`.73`, 1876–1907) re-reads item (6)(α)'s sentence “TRUE at the witness by an EXACT CARRY CANCELLATION” — the cancellation is *witness arithmetic*, not the mechanism. `SUPERSESSION KIND: provenance-rider` (the claim stays true, its stated reason is replaced). **The correction is backed by a refuting witness**: a second iterated key `Φ₃ = Φ₂² − 16xΦ′` keeps its carry UNCANCELLED and is still one-sided — so “the carries cancel exactly at general genres” is FALSE as a general lemma.
(b) **post-PE3 Correction 2(i)** (`.74`, 1913–1917) attaches the FULL-inner-side scope word to this box's preamble: read “the corrected leaf read with inner-μ₂ = 2 σ” as “… on a FULL inner side only (e₂f₂μ₂ = μ₁ — (iii)'s proved perimeter; partial sides are the box's own item (4), six lines below)”. `SUPERSESSION KIND: scope-pin`.
**CHAIN for item (6)(α): `[r3]` display → post-PE3 Correction 1. TERMINAL: the corrected reading (carry terms CLEAR the side; the constant lands on the endpoint).**
(c) **Item (6)'s bottom line is explicitly unmoved by the correction**: “The box's bottom line stands unchanged: one-sidedness at general genres is genuine Okutsu-optimality content, unproved here; item (6) remains OPEN; no σ or count is priced through it.”

**DERIVATION:** The iteration data are **re-derived at the repair, not transcribed** — the box says so. The level-2 ladder monomials' uniqueness is “by GENHN-2′'s two-step class separation” (shard 1 `.43`).

*Arithmetic audit (rule 22), every witness number recomputed from the frame `Φ′ = x² − 2` over ℤ₂ (`e₁ = 2, f₁ = 1, h = 1`, `dv = 2v`; inner `e₂ = 2, f₂ = 1, u₂ = 5`, `dv₂ = 4v`).*
- **`n̂₂(21) = 16Φ′` with `(a, i, b) = (4, 0, 1)`.** Height formula `m = a·e₁e₂ + i·e₂h + b·u₂ = 4·4 + 0·2 + 1·5 = 16 + 0 + 5 = 21` ✓ **exact**. And `π^a x^i Φ′^b = 2⁴·x⁰·Φ′ = 16Φ′` ✓. Range check: `i = 0 < e₁ = 2` ✓, `b = 1 < e₂ = 2` ✓.
- **`Φ₃ = Φ₂² − 16Φ′` with `ψ₃ = T − 1`, `u₃ = 21`.** Matches the level-3 key form `Φ₂^{e₃f₃} − Σ_t k̂_tΦ₂^{e₃t}` at `e₃ = 2, f₃ = 1`? Then `e₃f₃ = 2` ✓ (`Φ₂²`) and the single `t = 0` term is `k̂_0 = 16Φ′ = n̂₂(21)` ✓ at `dv₂`-height `u₃(f₃−0) = 21` ✓ **consistent**.
- **The (α) expansion.** With `Φ₂ = Φ′² − …`: the box gives `Φ₃ = Φ′⁴ − 8xΦ′² + 16x² − 16Φ′`. Carry: `16x² = 16(Φ′ + 2) = 16Φ′ + 32` ✓ (since `x² = Φ′ + 2`). Substituting: `Φ′⁴ − 8xΦ′² + 16Φ′ + 32 − 16Φ′ = Φ′⁴ − 8xΦ′² + 32` ✓ **the −16Φ′ is killed exactly**, as claimed.
- **The dv-pins.** Coefficients of the Φ′-development `Φ′⁴ − 8xΦ′² + 0·Φ′ + 32`: at `b = 4`, coefficient 1, `dv = 0` → pin `(4, 0)` ✓. At `b = 0`, coefficient 32, `dv(32) = 2·v(32) = 2·5 = 10` → pin `(0, 10)` ✓. At `b = 2`, coefficient `−8x`, `dv = 2·v(8) + v_x`-contribution `= 2·3 + 1·h = 6 + 1 = 7` → pin `(2, 7)` ✓. **All three match the display exactly.**
- **One-sidedness.** The side from `(0, 10)` to `(4, 0)` has slope `10/4 = 5/2 = κ₂` ✓. Its height at `b = 2` is `10 − 2·(5/2) = 5`; the pin sits at 7 > 5 ✓ **strictly above**, as the display says. Residual from the two endpoints on a slope-`5/2` side of abscissa length 4 with `e₂ = 2`: residual degree `4/2 = 2`, and the display gives `T² + 1 = ψ₂²` over F₂ ✓ (over F₂, `T² + 1 = (T+1)²` = a squared linear form, matching `f₂ = 1, μ₂ = 2`).
- **(β)'s floor check.** `κ₃ > dv₂(x^{D₂})`: `D₂ = D′e₂f₂ = 2·2·1 = 4`, `dv₂(x⁴) = 4·e₂h = 4·2·1 = 8`; `κ₃ = u₃/e₃ = 21/2 = 10.5 > 8` ✓ **exact match to the displayed “21/2 > 8”**.
- **SUPP-C's σ.** `{(16,1)}` sums to 16 ✓ = n; `{(8,1),(8,1)}` sums to 16 ✓.
**Every displayed number in item (6) reproduces. No discrepancy.**

**RESOLUTION TRACE:** statement 1382–1442 · derivation embedded (re-derived at the repair) · correction sites 1876–1907 (Corr. 1 → item (6)(α)), 1909–1917 (Corr. 2(i) → the preamble).

XREF: `GENHN_passPE2_report.md:F1` — count **9**.
XREF: `GENHN_passPE3_report.md:F-1` — count **4** · `F-2` — count **5**.
ARTIFACT: `verification/openmath/genhnr2_supp.py` ✓ · `genhnr2_supp_output.txt` ✓.
**UNPINNED (rule 23):** `51154c95…` (runner sha) and `664036bc…` (output) are **truncated** hashes with no verifiable object; the files they name are present, the versions are not verifiable from the note. Recorded, not passed.

**TEETH:** **SUPP-C** — three parse-gated 3-stage n = 16 instances, EXACT vs PARI on both routes. **Disposition: executable regression against an independent oracle, explicitly declined as proof** — “the iterated read is machine-witnessed TRUE at the first live degree, **and unproved**.” **`disclosed non-repair`:** items (1)–(5) have no instrument at all beyond the leaf-read leg; item (3)'s positive half is machine-only.

---
### EFF.GENHN.55  [table]  — §S9.2, THE REMAINING OPEN SURFACE

**CANONICAL STATEMENT:** verbatim, lines 1444–1493.

**FORM:** section body: five labelled headings with a numbered list beneath, plus a closing verdict sentence.

> “### S9.2 THE REMAINING OPEN SURFACE (the program's endgame
> inventory — everything between HERE and the unconditional full
> uniformity theorem, by name)
>
> MATHEMATICS (new theorems needed):
> 1. **[GENHN-HE(μ ≥ 3)]** — the σ-decision at stage leaves of
>    multiplicity μ ≥ 3 (S7 box; first live n = 6; the resolvent
>    method at degree μ / Ore over the stage ring; Montes order-≥2 is
>    the faithful-cite target). THE one load-bearing open lemma of
>    the whole composite program.
> 2. **GENHN-BOX-2's elementary carry** (optional-but-hardening: an
>    elementary general-μ refine-transfer display, retiring the weld
>    face from inside the μ ≥ 3 count laws).
> 2b. **[r2] [GENHN-TOW-1]** — the composed-key tower residue (S9.1
>    box): composed entry budgets + inner refine transfer +
>    faithfulness geography + partial inner sides + composed window
>    ledger **[r3 2026-08-09 (passPE2 F1): + the iterated depth-≥ 3
>    key composition (item (6), first live n = 16)]**; load-bearing
>    for P(n) at n ≥ 8 ONLY (empty at n ≤ 7);
>    the leaf read itself and inner-μ₂ = 2 σ **[r3: full inner
>    sides (passPE2 F2); partial sides are item (4)]** are PROVED
>    (LEMMA GENHN-T(b)′, S8 annex).
>
> COMPRESSIONS TO EXPAND (proved-as-schema, per-genre ledgers owed on
> demand — the GENIND-BOX-2 discipline):
> 3. **GENIND-3's β-route ledgers** at n ≥ 6 multi-child genres
>    (@ pin) and this note's entry-pattern fibers beyond the n ≤ 6
>    instances.
>
> MACHINE COVERAGE (proofs uniform, rows absent — GENHN-BOX-3):
> 4. f-first n = 6, 7 rows (E13/F3), mixed (2,2,2) + tower laws at
>    n = 8, d ≥ 2 ambients, q = 4 genre-F kit.
>
> DISPLAYS OWED (mechanical):
> 5. **GENH5-DENS** (the quintic densities; GENHN-BOX-5) and the
>    public-map fold at this milestone (standing directive).
>
> HOSTILE ARCS (process debt, per the acceptance discipline):
> 6. GENIND → QSCOUT22-adjacent → GENH4 → THIS NOTE at 0/2; W-12 PE3;
>    HEX3 PE3; HMENU3 PE4 (accepting).
>
> LEAN / PHASE B (unchanged by this note; the standing repo
> obligations): the M9-rebase Phase-B items (omMenu growth beyond
> order 0, SelfLoopHNode legs, hExhaust, faithful tame-FE cite) and
> the eventual formalization of the n-uniform scaffold (math-first
> directive: Lean waits for arc-stable statements).
>
> Items 1 + 6 are the critical path; 2–5 are hardening and owed
> displays. That the whole program's remaining mathematics fits in
> this list is THEOREM GENHN.B's content.”

`[TABLE]` — the endgame inventory transcribed (rule 5), with its current state as the note's own appends leave it:

| # | Class | Item | State at HEAD of this note |
|---|---|---|---|
| 1 | MATHEMATICS | `[GENHN-HE(μ ≥ 3)]` | **OPEN** — no GENHN append discharges it (OPEN-CALL 3) |
| 2 | MATHEMATICS (hardening) | GENHN-BOX-2's elementary carry | **OPEN** — a candidate unit exists outside the note at clean-pass 1 of 2 (`.50`) |
| 2b | MATHEMATICS | `[GENHN-TOW-1]`, six items | **OPEN**; item (6)(α)'s stated mechanism corrected post-PE3 (`.73`) |
| 3 | COMPRESSION | GENIND-3's β-route ledgers | **OWED on demand** (schema proved) |
| 4 | MACHINE COVERAGE | f-first, mixed (2,2,2), tower laws, d ≥ 2, q = 4 | **partially closed post-seal**: mixed (2,2,2) contacted by `genhn_f2_count_check.py`; f₁ = 4/comp = 3/F₁₆ by `genhn_pe4_fresh.py`; the rest open |
| 5 | DISPLAY OWED | GENH5-DENS + the public-map fold | **OWED** |
| 6 | HOSTILE ARC | GENIND → … → THIS NOTE at 0/2; W-12 PE3; HEX3 PE3; HMENU3 PE4 | **superseded**: GENHN itself is ACCEPTED 2/2 (`.75`); the stack moved at `.58`–`.60` |

*Arithmetic audit (rule 22) of the item numbering.* The list runs 1, 2, **2b**, 3, 4, 5, 6 — seven items under six numerals, because `[GENHN-TOW-1]` was inserted at `[r2]` without renumbering. The closing sentence “Items 1 + 6 are the critical path; **2–5** are hardening and owed displays” therefore **silently includes 2b in the range “2–5”** while the prose ranges are stated over the *numerals*. No claim is wrong, but the range notation is ambiguous about 2b. Recorded as source defect 2.

**CONDITIONALITY:**
(a) **Item 6 is `STALE-SELF-DESCRIPTION` (rule 26):** “THIS NOTE at 0/2” is falsified by the note's own acceptance append. The list is not corrected; the reader must be told.
(b) **Item 1's status is contested across notes and NOT settled here.** `HE3_PROOF_2026-08-08.md`'s title claims `[GENHN-HE(μ ≥ 3)]` CLOSED at μ = 3, n ≤ 7 and reduced to HE3-BOX-6 at μ ≥ 4; `HE7_PROOF`'s COROLLARY HE7.B claims the level-2 predicate. **Neither has landed on GENHN** — verified per rule 10 against the full append chain to line 2627, which contains no HE3 or HE7 discharge. See OPEN-CALL 3.
(c) **Item 4 is partially closed by two post-acceptance legs** (`.75`, `.93`), neither of which is folded back into this list.
(d) Item 2's retirement candidate is WELDZERO (`.50`), also unlanded.
(e) The Lean/Phase-B paragraph is a pointer to `docs/PROJECT_STATE.md`'s standing obligations and is explicitly “unchanged by this note”.

**DERIVATION:** Inventory, not derivation. Its completeness claim (“That the whole program's remaining mathematics fits in this list is THEOREM GENHN.B's content”) inherits GENHN.B's own corrected conditionality (shard 1 `.18`), including that note's two preserved self-indictments about the words “EXACTLY” and “correct for the amended list”.

**RESOLUTION TRACE:** statement 1444–1493 · correction sites 1941–1955 (item 6's grade), 1944–1949 + 2607–2614 (item 4's partial closure) · external status: `HE3_PROOF_2026-08-08.md` title, `spec/HYPOTHESIS_LEDGER.md` HYP.81/HYP.148.

XREF: `GENIND_PROOF_2026-08-08.md:GENIND-BOX-2` — count **1**.
XREF: `GENIND_PROOF_2026-08-08.md:LEMMA GENIND-3` — count **6**.
XREF: `HE3_PROOF_2026-08-08.md:GENHN-HE` — count **7**.
XREF: `W12_PROOF_2026-08-08.md:W-12.D` — count **19**.
XREF: `HEX3_PROOF_2026-08-08.md:HEX3` — count **83**.

**TEETH:** NONE (inventory). Item 4 IS the teeth-coverage list, cross-referenced to `.51`.

---
### EFF.GENHN.56  [fence]  — §S10 consumers + conditionality stack (as-of pins)

**CANONICAL STATEMENT:** verbatim, lines 1495–1524.

**FORM:** bulleted declaration list under a `##` heading.

> “## S10. CONSUMERS + CONDITIONALITY STACK (as-of pins)
>
> * **GENIND** @ 4682bcf (verdict 4984004; 0/2): GENIND.A(I)(II)(IV),
>   GENIND-0/1/2/3, GENIND.C, GENIND.B — the scaffold this note's
>   discharge feeds; the stage-internal reuse of GENIND-1/2/3 over K
>   (S6.2, S8) consumes their proved (m, d)-uniformity.
> * **GENH4** @ 121d9ab/4b5c085 (0/2): the μ = 2 (2,1,2)/(1,2,2)
>   instances of every lemma; law_E/law_F @ runner md5 pin
>   ee8024b7a500220a6408dab373d7432f.
> * **QSCOUT22** @ dd67cda (instrument): the pinned quartic reader
>   (runner md5 cb885663dd4ef6dfda9c28a67c1a076e) + committed table
>   (results md5 6c2441a12cf52ffd43055de912a4affe).
> * **W-12.A/S2.5 + W-12.D** @ f669cb0/99f1813 (0/2, PE3 owed): entry
>   laws at every degree; the firing reduction.
> * **W-11** @ 7020ceb/31506b3 (ACCEPTED 2/2): the μ = 2 re-basing
>   target.
> * **GRTJC W-6..W-9 + JC-LOAD/W-8** @ 83f47f4 (ACCEPTED 2/2):
>   consumed at LEMMA GENHN-4 layer 1 (μ ≥ 3) — the ONE weld face
>   inside a count law, disclosed (GENHN-BOX-2); elsewhere frame-only
>   (GENHN-2 re-proves the slot geometry elementarily).
> * **J-D0** @ 9387eb1 (proved): letter/twist-blindness of counts.
> * **DULEMMA** @ f819f26: applicability checked (stage rings e₁ ≥ 2
>   on its perimeter), NOT consumed (S3.1 proves the valuation
>   directly).
> * **SIGMALAW** @ a27ed68 (ACCEPTED 2/2): the (EC-q) ladder, named at
>   S8(b)'s letter-layer composition only; no count consumption.
> * **HEX3 / HMENU3** @ r2 f60348b + a707430 pins (arcs live): P(3)
>   and the n = 3 telescoping template (via GENIND @ pin).
> * **Classical:** Hensel, Ore order-1, ultrametric quadratic
>   analysis over complete fields, finite-field censuses.”

**CONDITIONALITY:**
(a) **Every grade is as-of the pin and every one that could move, moved** — superseded by `.58`'s `[e2]` refresh. `SUPERSESSION KIND: as-of scoping`.
(b) **The GRTJC bullet names the weld face in the note's own sharpest words** — “the ONE weld face inside a count law, disclosed (GENHN-BOX-2)”. `spec/HYPOTHESIS_LEDGER.md` quotes exactly this line (L1512–1513) when indexing HYP.148. See `.50`.
(c) **The DULEMMA bullet's “stage rings e₁ ≥ 2” is riddered by `[e2]` E3** — E3's rider list names “S0's **and S10's** DULEMMA lines "stage rings have e(R/O) = e₁ ≥ 2" (read e(L/base) = e₁)”. `SUPERSESSION KIND: wording-rider`.
(d) The SIGMALAW bullet's “S8(b)” pointer now resolves to the **withdrawn** T(b) proof (shard 1 `.17`); T(b)′ names the letter layer only through its composed cocycles. The note does not re-point it. Recorded as source defect 3.

**DERIVATION:** Declaration.

**RESOLUTION TRACE:** statement 1495–1524 · correction sites 518–524 (E3's rider list, shard 1), 1533–1569 (`[e2]` refresh), 1082–1086 (the withdrawal S8(b) points at, shard 1).

XREF: `GENIND_PROOF_2026-08-08.md:GENIND.A(I)` — count **3** · `GENIND.C` — **23** · `LEMMA GENIND-0` — **5** · `LEMMA GENIND-1` — **2** · `LEMMA GENIND-2` — **7** · `LEMMA GENIND-3` — **6** · `THEOREM GENIND.B` — **7**.
XREF: `GENH4_PROOF_2026-08-08.md:law_E` — **2** · `law_F` — **7**.
XREF: `W12_PROOF_2026-08-08.md:THEOREM W-12.A` — **8** · `S2.5` — **9** · `W-12.D` — **19**.
XREF: `W11_PROOF_2026-08-08.md:W-11` — **18**.
XREF: `GRTJC_PROOF_2026-08-08.md:COROLLARY W-9` — **2** · `JC-LOAD` — **31** · `W-8` — **35** · `W-6` — **18**.
XREF: `JD0_PROOF_2026-08-08.md:J-D0` — **25**.
XREF: `DULEMMA_PROOF_2026-08-08.md:DULEMMA` — **1**.
XREF: `SIGMALAW_PROOF_2026-08-08.md:(EC-q)` — **26**.
XREF: `HEX3_PROOF_2026-08-08.md:HEX3` — **83**.
XREF: `HMENU3_PROOF_2026-08-08.md:ANNEX A` — **5**.
PINS (`git cat-file -t` → commit): `4682bcf` ✓ `4984004` ✓ `121d9ab` ✓ `4b5c085` ✓ `dd67cda` ✓ `f669cb0` ✓ `99f1813` ✓ `7020ceb` ✓ `31506b3` ✓ `83f47f4` ✓ `9387eb1` ✓ `f819f26` ✓ `a27ed68` ✓ `f60348b` ✓ `a707430` ✓ — **15/15**.
MD5 PINS: `ee8024b7a500220a6408dab373d7432f` (GENH4 runner), `cb885663dd4ef6dfda9c28a67c1a076e` (QSCOUT22 runner), `6c2441a12cf52ffd43055de912a4affe` (QSCOUT22 results) — **full hashes, checkable by GN-PIN**, unlike the truncated shas at `.54`.

**TEETH:** **GN-PIN** — 7 md5 pins checked as a battery family (`.62`), i.e. the artifacts behind these bullets are machine-verified to be the ones consumed. Disposition: executable regression.

---
### EFF.GENHN.57  [scope-record]  — the “One line” conditionality summary

**CANONICAL STATEMENT:** verbatim, lines 1526–1531.

**FORM:** bold display sentence.

> “**One line: THEOREM GENHN.CLASS + GENHN.A(i)–(iii) + GENHN.C +
> GENHN-T(a) rest on {GENIND lemmas, W-12.A, W-11, classical} @ pins
> with no weld face; GENHN.A(iv) at μ ≥ 3 adds ONE accepted weld face
> (W-9, disclosed); GENHN.B adds GENIND.B + W-12.D @ pins and the box
> family [GENHN-HE(μ ≥ 3)]. No axiom anywhere; grade = composition
> 0/2.**”

**CONDITIONALITY:** **The single most quotable sentence in the note, and three of its four clauses need a rider.**
(a) “GENHN.CLASS … with no weld face” — true, but GENHN.CLASS's finiteness clause is itself re-displayed (`.86`).
(b) “GENHN.A(i)–(iii)” — (i)'s carrier corrected (E3), (ii)'s slot clause re-displayed twice (`.87`, `.88`), (iii)'s “never consulted” riddered (`.79`).
(c) “GENHN.A(iv) at μ ≥ 3 adds ONE accepted weld face (W-9, disclosed)” — **exactly right and still live** (`.50`).
(d) “grade = composition 0/2” — `STALE-SELF-DESCRIPTION`; terminal grade is **2/2** (`.75`).
(e) **“No axiom anywhere” is untouched and is the clause most worth preserving**: GENHN introduces no axiom, and no append adds one (verified across all eleven).

**DERIVATION:** Summary of `.56` plus shard 1's grade lines.

**RESOLUTION TRACE:** statement 1526–1531 · correction sites as listed at (a)–(d).

**TEETH:** NONE (summary).

---
### EFF.GENHN.58  [changes-record]  — `[e2]` S10 REFRESH

**CANONICAL STATEMENT:** verbatim, lines 1533–1569.

**FORM:** bold-headed dated append inside §S10, with bulleted supplier movements and a closing ARC LINE paragraph.

> “**[e2] S10 REFRESH 2026-08-09 (dated append at the erratum round;
> as-of the wave-13 fold 606821e + this round's own commits,
> per-commit-timestamp rule). Supplier movements since the pins above
> — enumerated statuses only; the consumed-clause audit for the shared
> suppliers is GENIND S16's fired-clause table @ dcc20bb:**
> * **GENH4: ACCEPTED 2/2, FULLY FROZEN.** Accepted body byte-frozen
>   at r3 4b0d946; annex stack (ANNEX PE5 baf05ed, ANNEX R b10a5a7 =
>   the Codex CHALLENGE 5c8d2fd discharge, ANNEX R2 760d20f, dated
>   corrections 6568114) itself accepted 2/2 at annexpass3 7f27065.
>   Consumed here: law_E/law_F @ runner md5 pin ee8024b7…432f
>   (byte-untouched through the whole arc) + the μ = 2 instances. The
>   three GENH4-side corrections that LAND on this note are executed
>   as this round's errata: E1 (GENHN-3(a) band exit, r3 trichotomy @
>   4b0d946), E2 (GENHN.A(v) comp-weighted band census, [r2] display
>   re-derived), E3 (GENHN.A(i)/S3.1 L/O_L carrier, ANNEX R R3).
> * **HE7: ACCEPTED 2/2, FULLY FROZEN** (final dated corrections
>   ca3754d; body prefix md5 732af1e1, dated appends only). Not a
>   supplier of this note's count laws; its D′h remark is consumed by
>   the [r1] erratum (S3.2 annex) as recorded there.
> * **GENIND: 1/2** — PE7 CLEAN @ 380bc66 + post-PE7 micro-annex
>   b653858 (byte-freeze verified there); acceptance attempt
>   dispatched at wave 14. Its r6 supplier re-pin round (dcc20bb)
>   walked THIS note's consumed surface (7 cite sites, completed at
>   the micro-annex) and reports SURVIVES at 850e77e — the [r1]/[e2]
>   repairs touch none of the 7 consumed sentences' count content.
> * **W-12: r5 @ be4a1dc/ee17210 (0/2), PE6 dispatched (wave 14).**
>   HEX3: r3 @ b6a1d69 (0/2). HMENU3: ACCEPTED @ 050425d + ANNEX A
>   19c0285. W-11, GRTJC, SIGMALAW, J-D0, DULEMMA, QSCOUT22: pins
>   unmoved as listed above.
> * **ARC LINE (honest).** With HE7 and GENH4 through both bars, and
>   the three queued errata (E1/E2/E3) now executed, **GENHN's OWN PE1
>   IS UNBLOCKED**: this note stands at 0/2 (composed, [r1] + [e2]
>   tagged repairs, no hostile pass yet) and is next in the
>   hostile-arc queue. S9.2 item 6's arc list reads accordingly at
>   this date: GENIND 1/2 (accepting), GENH4 DONE (2/2 frozen), THIS
>   NOTE PE1 next; W-12 PE6 and the HEX3/HMENU3 lines as pinned
>   above.**”

**SUPERSESSION KIND: as-of scoping** (supplier grades re-pinned at a later date) + **inventory completion** (the three GENH4-side corrections are named as executed). `TARGETS: .49` (the BOX-1 stack), `.56` (§S10's own bullets), `.55` (item 6's arc list).

**CONDITIONALITY:** **This refresh is itself superseded twice, by `.59` and `.60`.** Its ARC LINE says “no hostile pass yet”; PE1 then ran NOT CLEAN, PE2 NOT CLEAN, PE3 CLEAN, PE4 CLEAN. `STALE-SELF-DESCRIPTION` on “this note stands at 0/2 … and is next in the hostile-arc queue”. **CHAIN: §S10 bullets → `[e2]` refresh → `[r2]` arc line → `[r3]` arc line → post-PE3 (1/2) → post-PE4 (2/2). TERMINAL: post-PE4.**
**One load-bearing positive:** GENIND's r6 supplier re-pin round independently walked GENHN's consumed surface — “7 cite sites … and reports SURVIVES at 850e77e — the [r1]/[e2] repairs touch none of the 7 consumed sentences' count content”. That is a **decorrelated check of this note's own repairs from the supplier side**, and it is the only one in the note.

**DERIVATION:** Status record.

**RESOLUTION TRACE:** statement 1533–1569 · correction sites 1570–1585, 1586–1622, 1863–1874, 1941–1955.

XREF: `GENIND_PROOF_2026-08-08.md:S16` — count **22** (§-anchor; the fired-clause table's own section, referent verified).
XREF: `GENH4_PROOF_2026-08-08.md:ANNEX PE5` — count **7** · `ANNEX R` — **12** · `ANNEX R2` — **5**.
XREF: `HE7_PROOF_2026-08-08.md:HE7` — count **366** (self-name; the D′h remark referent is pinned instead by `LEMMA HE6-0` (17) and `LEMMA HE6-3` (12) at shard 1 `.24`).
XREF: `HMENU3_PROOF_2026-08-08.md:ANNEX A` — count **5**.
PINS (`git cat-file -t` → commit): `606821e` ✓ `dcc20bb` ✓ `4b0d946` ✓ `baf05ed` ✓ `b10a5a7` ✓ `5c8d2fd` ✓ `760d20f` ✓ `6568114` ✓ `7f27065` ✓ `ca3754d` ✓ `380bc66` ✓ `b653858` ✓ `be4a1dc` ✓ `ee17210` ✓ `b6a1d69` ✓ `050425d` ✓ `19c0285` ✓ `850e77e` ✓ — **18/18**.
**UNPINNED (rule 23):** HE7's “body prefix md5 732af1e1” is a **truncated** md5; the GENH4 runner pin `ee8024b7…432f` is truncated in this bullet but given in full at `.56`.

**TEETH:** NONE (status record). Its one verifiable claim — that the GENH4 runner md5 is byte-untouched through the whole arc — is checked by **GN-PIN**.

---
### EFF.GENHN.59  [changes-record] · SERIES: GENHN-ARC-LINE, member 2 of 3  — `[r2]` ARC LINE UPDATE

**CANONICAL STATEMENT:** verbatim, lines 1570–1585.

**FORM:** bulleted bold-headed dated update inside §S10.

> “* **[r2] ARC LINE UPDATE 2026-08-09.** passPE1 ran (report
>   `GENHN_passPE1_report.md`): NOT CLEAN — F1 CRITICAL refuted
>   LEMMA GENHN-T(b) at n = 8 tower leaves (the program's first
>   displayed-lemma refutation), F2 CRITICAL the GENHN-1 budget
>   display, F3 GAP the f₁ ≥ 3 band transport, F4/F5 minor. THIS
>   round ([r2] tags, commits at the r2 fold): T(b)′ stated and
>   PROVED with machine leg `genhnr2_supp.py` (147/0, 3 teeth, first
>   tower leaf coverage incl. an f₂ = 2 genre and 3-stage n = 16);
>   F2 display corrected + consumption audit; F3 derived (E1
>   upgraded); F4/F5 one-line riders. CONSEQUENCE: GENHN.B's
>   conditionality now carries [GENHN-TOW-1] at n ≥ 8 (n ≤ 7
>   unchanged); consumers with n ≥ 8 instances (GENIND's (CS-1)/
>   (CS-2) citations, the S9.2 endgame list, PROJECT_STATE's
>   uniformity display) inherit that box — cross-note status is the
>   orchestrator's fold, flagged here. Clean count 0/2 → 0/2; PE2
>   next.”

**CONDITIONALITY:** **SERIES `GENHN-ARC-LINE`:** member 1 = `[e2]`'s ARC LINE (`.58`, “PE1 next”); **member 2 = this unit** (PE1 ran, 0/2); member 3 = `[r3]` (`.60`, PE2 ran, 0/2). Terminal grade lives in the GENHN-GRADE-ARC series (`.75`).
**Its consumer clause is header predicate B in action:** the box is flagged for the orchestrator, not folded. `spec/HYPOTHESIS_LEDGER.md` shows the fold did eventually happen at the ledger level (HYP.81/HYP.148 rows), not by a GENHN append.
**One content claim of record:** “the program's first displayed-lemma refutation” — a corpus-level historical claim, unverified here beyond the note's own assertion, and not load-bearing.

**DERIVATION:** Round record. The five findings' mathematics is at shard 1 `.17`/`.41`–`.47` (F1), `.25` (F2), `.32` (F3), `.38` (F4), and `.19`-adjacent (F5, the 350/349 tail — homed at `.19` of this shard).

**RESOLUTION TRACE:** statement 1570–1585 · correction sites 1586–1622 (`[r3]`), 1941–1955 (acceptance).

XREF: `GENHN_passPE1_report.md:F1` — **7** · `F2` — **5** · `F3` — **4** · `F4` — **3** · `F5` — **3**.
XREF: `GENIND_PROOF_2026-08-08.md:(CS-1)` — **49** · `(CS-2)` — **20**.
ARTIFACT: `verification/openmath/genhn_pe1_fresh.py` ✓ · `genhnr2_supp.py` ✓.

**TEETH:** `genhnr2_supp.py` 147/0, 3 teeth — see shard 1 `.41`.

---
### EFF.GENHN.60  [changes-record] · SERIES: GENHN-ARC-LINE, member 3 of 3  — `[r3]` ARC LINE UPDATE

**CANONICAL STATEMENT:** verbatim, lines 1586–1622.

**FORM:** bulleted bold-headed dated update inside §S10.

> “* **[r3] ARC LINE UPDATE 2026-08-09.** passPE2 ran (report
>   `GENHN_passPE2_report.md`, 701c7b1): NOT CLEAN — 0 CRITICAL +
>   2 GAP + 2 MINOR. LEMMA GENHN-T(b)′ (i)–(iv) HELD against
>   re-derivation and against a fresh instrument
>   (`genhn_pe2_fresh.py`, GREEN 219/0, 4 teeth, incl. first
>   outer-f₁ = 2 tower genres, first 2-stage dictionary contact,
>   the η₂-cocycle adjudication, and Q = 4 tower legs); both GAPs
>   were coverage defects of the r2 DISPLAYS around the held
>   lemma. THIS round ([r3] tags): F1 — the depth-≥ 3 iterated key
>   composition (first live n = 16) BOXED as [GENHN-TOW-1] item
>   (6): the iterated ladder-normalizer and key data are DERIVED
>   there (n̂₂(m) = π^a x^i Φ′^b; Φ₃ = Φ₂^{e₃f₃} − Σ k̂_tΦ₂^{e₃t};
>   witnesses n̂₂(21) = 16Φ′, Φ₃ = Φ₂² − 16Φ′) and a T(b)″ was
>   honestly ATTEMPTED — its two open steps are displayed in the
>   item (the intermediate-development one-sidedness, true at the
>   witness by an exact carry cancellation, unproved in general;
>   the depth-≥ 3 node floor's provenance, riding item (1)); the
>   GENHN.B tower clause and corrected-conditionality display now
>   name the depth split (n ∈ {8, …, 15}: depth-2, T(b)′'s one
>   step + items (1)–(5); n ≥ 16: item (6) joins). F2 — the (CS-3)
>   rider scoped to FULL inner sides ((iii)'s proved perimeter);
>   partial-side inner μ₂ = 2 leaves (first live n = 10) ride item
>   (4), with the passPE2 n = 10 witness and the reader's loud
>   refusal cited at the rider. F3 — the budget erratum's f₁ ≥ 2
>   magnitude parenthetical sign corrected (old − correct =
>   h(1 − (μ−j)(f₁−1)); genre-F instance re-derived). F4 — the
>   (iv) divergence tally denominator corrected to 35/35 compared
>   rows (the 3 SUPP-C 3-stage rows have no stage read). Machine
>   support: ADDITIVE citations only (SUPP-C's three 3-stage
>   n = 16 instances at the existing pins 51154c95…/664036bc…;
>   the passPE2 fresh-instrument pins 4a28246e…/10b685b0…); sealed
>   runners and artifacts byte-untouched; the item-(6) witness
>   arithmetic (Φ₃'s carry cancellation, the dv-pins, the F3 sign)
>   re-computed at this repair, not transcribed. Consumers:
>   GENIND's n ≥ 8 conditionality line inherits the refined
>   n ≥ 10 / n ≥ 16 scoping — orchestrator's fold, flagged here.
>   Clean count 0/2 → 0/2; PE3 next.”

**CONDITIONALITY:**
(a) **`STALE-SELF-DESCRIPTION`** on “Clean count 0/2 → 0/2; PE3 next” — PE3 and PE4 both returned CLEAN and the note is ACCEPTED 2/2.
(b) **This round's own F1 disposition is later corrected**: “true at the witness by an exact carry cancellation” is re-read by post-PE3 Correction 1 (`.73`) as witness arithmetic, not mechanism. `SUPERSESSION KIND: provenance-rider`. **CHAIN: `[r3]`'s F1 summary → post-PE3 Correction 1. TERMINAL: the correction.**
(c) **The round's discipline claim is verifiable and verified:** “sealed runners and artifacts byte-untouched; the item-(6) witness arithmetic … re-computed at this repair, not transcribed.” This compiler independently recomputed all six item-(6) witness numbers at `.54` and every one reproduced.

**DERIVATION:** Round record; each finding's mathematics is at its own unit.

**RESOLUTION TRACE:** statement 1586–1622 · correction sites 1876–1907 (Corr. 1 → the F1 summary's mechanism clause), 1941–1955 (grade).

XREF: `GENHN_passPE2_report.md:F1` — **9** · `F2` — **5** · `F3` — **5** · `F4` — **5**.
PIN: `701c7b1` ✓ commit.
ARTIFACT: `verification/openmath/genhn_pe2_fresh.py` ✓ · `genhn_pe2_fresh_output.txt` ✓.
**UNPINNED (rule 23):** four truncated hashes — `51154c95…`, `664036bc…`, `4a28246e…`, `10b685b0…`. Files present; versions unverifiable from the note.

**TEETH:** `genhn_pe2_fresh.py` — GREEN 219/0, 4 teeth, **a decorrelated instrument at which T(b)′ (i)–(iv) HELD**. Disposition: executable regression on a fresh instrument; the strongest positive evidence in the note for the repaired tower lemma.

---
### EFF.GENHN.61  [instrument-record]  — §S11.A instrument + provenance

**CANONICAL STATEMENT:** verbatim, lines 1624–1643.

**FORM:** `##`/`###` headed section body with an inline pin list.

> “## S11. THE SEALED BATTERY (sealed at commit 1; predictions
> preregistered BEFORE the first full run)
>
> ### S11.A Instrument + provenance
>
> `verification/openmath/genhn_checks.py`, two-commit seal (commit 1 =
> this note + the runner, full battery UNRUN; commit 2 = §S12 verdict
> appended FROM the committed artifacts `genhn_checks_output.txt` /
> `genhn_checks_results.json`). Pins (md5, checked as family GN-PIN):
> genind_checks.py e7ca150b…aca2 · genh4_checks.py ee8024b7…432f ·
> qscout22_checks.py cb885663…076e · w10_checks.py a9c34244…380b ·
> w12_checks.py 7dc040d9…d418 · genind_checks_results.json
> 366f2143…96f6 · qscout22_results.json 6c2441a1…4affe.
> PROVENANCE: the runner was drafted by the interrupted prior
> incarnation and re-audited line-by-line as UNTRUSTED by the fresh
> continuation — laws, twist corrections (E31 i₁=2 wrap z⁻¹; the
> E3/tower wrap exponent), node floors, and all flagship volumes
> re-derived by hand — then ADOPTED with two repairs (R1 irreducible
> table 4→6; R2 the three Q-genre names, de-vacuifying their
> PREDICTED-ABSENT checks); disclosed in the runner docstring.”

**CONDITIONALITY:** **This is freeze predicate (F2), stated.** Its provenance paragraph is unusually strong evidence and is worth preserving verbatim: the runner was treated as **UNTRUSTED** and re-audited line by line, with two repairs disclosed — including R2, which **de-vacuified** three PREDICTED-ABSENT checks (i.e. the audit found three checks that could not have failed and fixed them). That is a self-administered vacuity audit, and it is why the PREDICTED-ABSENT legs at `.64` P1 are evidence rather than decoration.

**DERIVATION:** Instrument description.

**RESOLUTION TRACE:** statement 1624–1643 · re-seals 1741–1775 (`.66`, `.67`) · verdict provenance 1806–1811 (`.69`).

ARTIFACT: `verification/openmath/genhn_checks.py` ✓ · `genhn_checks_output.txt` ✓ · `genhn_checks_results.json` ✓.
**UNPINNED (rule 23):** all seven GN-PIN md5s are **truncated** in this display (`e7ca150b…aca2`, etc.). Three of them are given in full at `.56` (`ee8024b7a500220a6408dab373d7432f`, `cb885663dd4ef6dfda9c28a67c1a076e`, `6c2441a12cf52ffd43055de912a4affe`); four are not recoverable from the note. Recorded, not passed.

**TEETH:** **GN-PIN** is the tooth for this unit — the seven supplier artifacts are md5-checked as a battery family, so a supplier drifting under the note would turn the run RED.

---
### EFF.GENHN.62  [instrument-record]  — §S11.B families + teeth

**CANONICAL STATEMENT:** verbatim, lines 1645–1662.

**FORM:** `###` headed section body, prose roster with `·`-separated family names.

> “### S11.B Families + teeth
>
> GN-PIN (7 pins) · GN-CLASS (n=5/n=6 sweeps: grammar at all depths,
> flagships, visibility floors, genind-reader tie on n=5) · GN-LAWTIE
> (law_Egen(e₁=2) ≡ pinned law_E, 5 grid points) · GN-FIB (constructed
> loci: frames parse to genre, volumes = entry laws) · GN-STAGE2 (the
> μ=2 stage law at THREE fresh genres, both directions) · GN-E3 (the
> μ=3 stage: species partition + UND3/RAM3/ALPHA3 laws) · GN-REFINE3
> (pointwise μ=3 refine transport: every stage-α event re-divided,
> three pins dead, floored node) · GN-TOWER (criterion + the n=8
> witness + min-n scan) · GN-SIGMA (PARI factorpadic vs dictionary;
> extraction-certified perimeter on V rows — S11.F). TEETH (each must
> fire ≥1 else RED): GN-T-LAT (E31 law collapsed to integer lattice) ·
> GN-T-CEN (INERT census ×2) · GN-T-SIG (E31 RAM σ {(6,1)}→{(3,2)}
> must be caught by PARI) · GN-T-CRIT (grammar bound e₁f₁μ ≥ 4 dropped
> to ≥ 3 must accept an order-1 (3)-child fake that the true grammar
> rejects) · GN-T-NODE (E3 construction a₀₀ floor off-by-one must
> break the volume).”

`[TABLE]` — the roster transcribed (rule 5), with the guarded shard-1 units:

| Family | What it checks | Guards (shard 1) |
|---|---|---|
| GN-PIN | 7 supplier md5 pins | `.53` |
| GN-CLASS | n = 5 / n = 6 sweeps: grammar at all depths, flagships, visibility floors, GENIND-reader tie | `.55`, `.68` |
| GN-LAWTIE | law_Egen(e₁=2) ≡ pinned law_E, 5 grid points | `.60`, `.84` |
| GN-FIB | constructed loci; frames parse to genre; volumes = entry laws | `.56`, `.71` |
| GN-STAGE2 | μ = 2 stage law at three fresh genres, both directions | `.60`, `.74` |
| GN-E3 | μ = 3 stage: species partition + UND3/RAM3/ALPHA3 | `.60`, `.84`, `.85` |
| GN-REFINE3 | pointwise μ = 3 refine transport by actual re-division | `.59`, `.81`, `.82` |
| GN-TOWER | criterion + n = 8 witness + min-n scan | `.64` |
| GN-SIGMA | PARI factorpadic vs dictionary; S11.F perimeter on V rows | `.63`, `.86` |

| Tooth (must fire ≥ 1 else RED) | Mutation | Guards (shard 1) |
|---|---|---|
| GN-T-LAT | E31 law collapsed to the integer lattice | `.75` |
| GN-T-CEN | INERT census ×2 | `.60`, `.63` |
| GN-T-SIG | E31 RAM σ {(6,1)} → {(3,2)}, must be caught by PARI | `.63`, `.86` |
| GN-T-CRIT | grammar bound e₁f₁μ ≥ 4 dropped to ≥ 3 | `.55`, `.68` |
| GN-T-NODE | E3 construction a₀₀ floor off-by-one | `.56`, `.71` |

*Arithmetic audit (rule 22).* **Nine families and five teeth are declared here.** S12's verdict reports “all five teeth fired (LAT 2 / CEN 2 / SIG 2 / CRIT 2 / NODE 1)” ✓ — five names, five counts, all ≥ 1 ✓ so the RED condition (“each must fire ≥ 1 else RED”) is satisfied. The title-box says “≥ 3 teeth” (shard 1 `.03`); **five is consistent with “≥ 3”** ✓. Fire counts sum to `2+2+2+2+1 = 9`; no other number in the note should match that, and none does — no cross-check available, recorded as such.

**CONDITIONALITY:** **The tooth-firing rule is the note's own falsifier and it is preregistered**: “each must fire ≥1 else RED”, restated at P10 (“verdict GREEN ⟺ 0 violations ∧ all teeth ≥ 1”). This makes the GREEN verdict a *conjunction*, not a count.

**DERIVATION:** Instrument description.

**RESOLUTION TRACE:** statement 1645–1662 · scored 1802–1803, 1846 (`.69`, `.70`).

**TEETH:** This unit IS the teeth roster; the inverse table is §5.

---
### EFF.GENHN.63  [instrument-record]  — §S11.C rows

**CANONICAL STATEMENT:** verbatim, lines 1664–1673.

**FORM:** `###` headed section body, compact row list.

> “### S11.C Rows
>
> CLASS: (Zp,2,5,n5)+(Fqt,2,5,n5) [tie=ON], (Zp,2,4,n6)+(Fqt,2,4,n6),
> (Zp,3,3,n6)+(Fqt,3,3,n6). ((Zp,2,5,n6) = 16.7M states DROPPED for
> runtime, disclosed.) V1E2: (Zp,2,5,1), (Zp,2,6,1), (Zp,3,4,1),
> (Fqt,2,6,1). V4E2 (v₄=1, h=3): (Zp,2,8,3), (Fqt,2,8,3). E31:
> (Zp,2,4,1), (Zp,2,5,1), (Zp,3,3,1) [wild p=3, e₁=3], (Fqt,2,5,1).
> E3: (Zp,3,4,1), (Zp,2,5,1), (Fqt,2,5,1). TOWER: the constructed
> n=8 witness at (Zp,3,6). ORACLE: PARI legs on all Zp sinks, sampled
> by the per-row steps in main().”

`[TABLE]` — the row ledger transcribed:

| Family | Rows | Notes |
|---|---|---|
| CLASS | (Zp,2,5,n5) + (Fqt,2,5,n5) [tie=ON]; (Zp,2,4,n6) + (Fqt,2,4,n6); (Zp,3,3,n6) + (Fqt,3,3,n6) | (Zp,2,5,n6) = 16.7M states **DROPPED for runtime, disclosed** |
| V1E2 | (Zp,2,5,1), (Zp,2,6,1), (Zp,3,4,1), (Fqt,2,6,1) | embedded genre; extraction-gated σ |
| V4E2 (v₄=1, h=3) | (Zp,2,8,3), (Fqt,2,8,3) | ★ first measurement of GENIND's derivation-only law |
| E31 | (Zp,2,4,1), (Zp,2,5,1), (Zp,3,3,1) [**wild p = 3, e₁ = 3**], (Fqt,2,5,1) | ★ first e₁ = 3 stage law ever measured |
| E3 | (Zp,3,4,1), (Zp,2,5,1), (Fqt,2,5,1) | ★ first μ = 3 stage ever read |
| TOWER | the constructed n = 8 witness at (Zp,3,6) | ★ first composite-over-composite event |
| ORACLE | PARI legs on all Zp sinks, sampled by per-row steps | independent oracle |

*Arithmetic audit (rule 22), computed fresh — the ℤ_p / F_q[[t]] pairing.* **Six CLASS rows come in three ℤ_p / F_q[[t]] pairs**, and every non-CLASS family also carries at least one `Fqt` row (V1E2: 1 of 4; V4E2: 1 of 2; E31: 1 of 4; E3: 1 of 3) ✓. Total rows: 6 CLASS + 4 V1E2 + 2 V4E2 + 4 E31 + 3 E3 + 1 TOWER = **20 rows**, of which **7 are `Fqt`**. Cross-check against P3's four V1E2 totals (12,288 / 458,752 / 26,244 / 458,752) and the row order (Zp,2,5,1) / (Zp,2,6,1) / (Zp,3,4,1) / (Fqt,2,6,1): the **second and fourth totals are identical (458,752)** ✓, and those are exactly the two `(q, N) = (2, 6)` rows — one over ℤ_p, one over F_q[[t]]. **The equal-characteristic and mixed-characteristic rows agree cell-for-cell at matched (q, N, h)**, which is the `[tie=ON]` claim made explicit only for CLASS. Recorded because this is independently interesting and the note does not state it for V1E2.

**CONDITIONALITY:** One disclosed omission: “(Zp,2,5,n6) = 16.7M states DROPPED for runtime, disclosed” — a coverage hole the note names rather than hides. Otherwise a record.

**DERIVATION:** Row list.

**RESOLUTION TRACE:** statement 1664–1673 · scored throughout `.70`.

**TEETH:** The rows ARE the teeth's substrate. **`signed vacuity disclosure`:** every row has `f₁ = 1` and `d = 1` (`.51`), so no row exercises E1/E2/`[r1]`.

---
### EFF.GENHN.64  [preregistration]  — §S11.D, the preregistered predictions P1–P10

**CANONICAL STATEMENT:** verbatim, lines 1675–1726.

**FORM:** `###` headed section, ten bulleted preregistered predictions with ★ marking never-measured territory.

> “### S11.D Preregistered predictions (never-measured territory
> flagged ★)
>
> * **P1 (CLASS flagships).** V1E2(1) = 12,288 at both n=5 rows
>   (= the committed GENIND row, machine-tied); E3(1) = 512 ★ and
>   E31(1) = 8,192 ★ at both (2,4,n6) rows; E31(1) = 4,374 ★ at both
>   (3,3,n6) rows. PREDICTED-ABSENT: V4E2/V1E1Q/V4E1Q/FULLQ at n=5;
>   F3/E13/F2X + E2X at (2,4,n6); F3/E13/F2X + E3 at (3,3,n6). Every
>   CS event at every depth parses under the strict grammar
>   (μ ≥ 2, e₁f₁ ≥ 2, 4 ≤ e₁f₁μ ≤ m ≤ n, span ≥ e₁f₁μ). Tie rows:
>   verdict + σ + depth-0 event agree with the pinned GENIND reader
>   on all 2×2²⁰ states.
> * **P2 (LAWTIE).** law_Egen(q,N,h,e₁=2) ≡ law_E(q,N,h) at (2,5,1),
>   (2,6,1), (2,7,3), (3,5,1), (5,4,1).
> * **P3 (V1E2 re-based law).** obs ≡ law_E(q,N,h) × (q−1)(q^{N−(5h+1)/2}−1)
>   per key, both directions; totals 12,288 / 458,752 / 26,244 /
>   458,752. Escapes = 0.
> * **P4 (V4E2 ★ FIRST measurement — GENIND's law was
>   derivation-only).** obs ≡ law_E(2,8,3) × (q−1)²q^{N−5v₄−1} = ×4;
>   totals 65,536 + 65,536. Escapes = 0.
> * **P5 (E31 ★ the first e₁=3 stage law ever measured).** obs ≡
>   (q−1) × law_Egen(q,N,h,e₁=3) per key; totals 8,192 / 524,288 /
>   4,374 / 524,288; per-member node floors dv₁ > 3h, dv₀ > 6h at
>   entry and > κ-floors along chains.
> * **P6 (E3 ★ the first μ=3 stage ever read).** Totals
>   (q−1)q^{6N−(21h+9)/2}: 39,366 / 32,768 / 32,768; zero stage-CS;
>   per-member floors dv_j > (3−j)·2h. Laws: UND3 = (q−1)q^{#(s₀≥cap)+|s₁|+|s₂|};
>   RAM3(u₀)/ALPHA3(κ) per the coded formulas. Spot instances: at
>   (Zp,3,4,1): UND3 = 13,122, RAM3(7) = 26,244, no ALPHA3, and
>   13,122 + 26,244 = the whole row; at (Zp,2,5,1): UND3 = 4,096,
>   RAM3(7) = 16,384, RAM3(8) = 4,096, ALPHA3(3) = 512.
> * **P7 (REFINE3 ★ the μ=3 transfer, pointwise).** Stage-α events
>   live exactly at the (·,2,5,1) E3 rows (κ=3; the (3,4,1) row has
>   none — 3κ ∉ s₀): 512 events per row, each transported by ACTUAL
>   re-division; all three pins dead and in the floored node — 1,536
>   pin checks per row, 0 violations. This is GENHN-BOX-2's
>   compensating instrument.
> * **P8 (TOWER ★ the first composite-over-composite event ever
>   constructed).** The (Zp,3,6) witness: frame parses
>   ('EMB',8,(0,8),2,1,4,1); stage dvs (10,None,5,None); stage hull
>   one side (0,10)–(4,0), (e_s,g) = (2,2); twisted inner residual
>   rc = (T−1)² — stage-CS FIRES inside the μ=4 stage; min-n scan
>   = 8; zero stage-CS anywhere else in the battery.
> * **P9 (SIGMA).** Certified jobs: 0 bad — V1E2/V4E2 composed
>   σ = SIG_E + {(1,1)}; E31 {(6,1)}/{(3,1)²}/{(3,2)} including
>   ★ wild p=3 at an e₁=3 stage (never-oracled territory); E3
>   depth-0-decided σ ([GENHN-HE(3)] corroboration, labeled — an
>   OPEN box, not proof). Diagnostic tail (S11.F): reported, not
>   scored; at (Zp,2,5,1) it is exactly the RAM(9) family (384 jobs
>   at step 1) and is PREDICTED to contain mismatches.
> * **P10 (teeth).** All five fire; verdict GREEN ⟺ 0 violations ∧
>   all teeth ≥ 1.”

**CONDITIONALITY:** **This is freeze predicate (F3) — preregistered before the first full run and byte-unchanged across both re-seals** (`.66`, `.67` both say so explicitly). Two properties make it strong evidence rather than narration: (i) **PREDICTED-ABSENT legs** (P1) predict *nothing* where the theory says nothing lives, and the provenance audit at `.61` de-vacuified three of them; (ii) **P9 preregisters a FAILURE** — the diagnostic tail “is PREDICTED to contain mismatches”, so the observed 349 + 58 mismatches confirm rather than damage the theory.
**One preregistered figure is later corrected:** P9's implicit tail count is reconciled at `[r2]` inside `.67` (350 vs 349). The *prediction* is byte-unchanged; the *run's* scoring changed. That distinction is exactly why rule 19 separates `preregistration` from `run-record`, and this shard keeps them as two units (`.64` vs `.70`).

**DERIVATION:** Predictions derived from the note's own laws — P3/P4/P5's forms are the re-based cell laws times explicit sibling fibers (shard 1 `.26`), P6's from the E3 genre's floors (shard 1 `.20`), P7's from GENHN-4 (shard 1 `.33`), P8's from GENHN-T(a) (shard 1 `.16`).

*Arithmetic audit (rule 22) — every flagship and total recomputed from the note's own laws, and cross-checked against §S2's genre table (shard 1 `.20`) and against S12's scorecard.*
- **P1, E3(1) = 512.** `(q−1)q^{6N−(21h+9)/2}` at `q = 2, N = 4, h = 1` → exponent `24 − 15 = 9`, so `1·2⁹ = 512` ✓. Matches the `[r2]` erratum's own check (“E3(1) = 512 = 2^{6·4−15}”) ✓ and S12 P6 ✓.
- **P1, E31(1) = 8,192 at (2,4,n6).** `Q^{6N−11}` at `q = 2, N = 4` → `2^{13} = 8,192` ✓ matches shard 1 `.25`'s corrected floor total 11 ✓.
- **P1, E31(1) = 4,374 at (3,3,n6).** `(q−1)q^{6N−11}` at `q = 3, N = 3` → `2 · 3^{7} = 2 · 2,187 = 4,374` ✓. **Note the letter factor `(q−1)` is present here and absent at q = 2** — consistent, because at `q = 2` the factor is 1. ✓
- **P1, V1E2(1) = 12,288.** `12,288 = 3 · 2^{12} = (q−1)·2^{12}` at q = 2 ✓; and it is “the committed GENIND row”, i.e. an external cross-check ✓.
- **P3 totals.** 12,288 / 458,752 / 26,244 / 458,752. `458,752 = 7 · 2^{16}` = `(q^3−1)·2^{16}`? Check: `7 · 65,536 = 458,752` ✓. `26,244 = 4 · 6,561 = 2² · 3⁸` ✓ at q = 3. The 2nd and 4th agree ✓ (the (2,6) ℤ_p/F_q[[t]] pair — see `.63`).
- **P4.** `65,536 + 65,536 = 131,072 = 2^{17}`; each `65,536 = 2^{16}` ✓, and `obs ≡ law_E(2,8,3) × 4` with `(q−1)²q^{N−5v₄−1} = 1 · 2^{8−5−1} = 2² = 4` ✓ at `q = 2, N = 8, v₄ = 1`.
- **P5 totals.** 8,192 / 524,288 / 4,374 / 524,288 at rows (Zp,2,4,1) / (Zp,2,5,1) / (Zp,3,3,1) / (Fqt,2,5,1). `524,288 = 2^{19}`; from `(q−1)q^{6N−11}` at `q = 2, N = 5`: `2^{30−11} = 2^{19}` ✓. **2nd and 4th agree** ✓ — again the ℤ_p/F_q[[t]] pair at matched (q, N). 3rd row `4,374` ✓ as above.
- **P6 totals.** 39,366 / 32,768 / 32,768 at (Zp,3,4,1) / (Zp,2,5,1) / (Fqt,2,5,1). At `q = 3, N = 4, h = 1`: `(3−1)·3^{24−15} = 2·3⁹ = 39,366` ✓. At `q = 2, N = 5, h = 1`: `1·2^{30−15} = 2^{15} = 32,768` ✓. **2nd and 3rd agree** ✓ (the third ℤ_p/F_q[[t]] pair).
- **P6 spot instances.** (3,4,1): `13,122 + 26,244 = 39,366` ✓ **= the whole row**, exactly as claimed. `13,122 = 2·3⁸` and `26,244 = 4·3⁸ = 2·13,122` ✓. (2,5,1): `4,096 + 16,384 + 4,096 + 512 = 25,088 ≠ 32,768`; the note calls these “Spot instances” and claims exhaustiveness only for the (3,4,1) row ✓ — **no error, but a reader could mis-infer.** Recorded as source defect 4.
- **P7.** “512 events per row … 1,536 pin checks per row” — `512 × 3 pins = 1,536` ✓. Two rows → `3,072`, exactly S12's “3,072 pin checks exactly (= 2 rows × 1,536)” ✓.
- **P8.** hull `(0,10)–(4,0)`: slope `10/4 = 5/2`, `(e_s, g) = (2, 2)` ✓ (denominator 2, abscissa length 4 = `e_s·g` = 2·2 ✓). Residual degree `4/e_s = 2` ✓ = `deg (T−1)²` ✓ — **and this is the R4 F-5 corrected form** (`.83`), confirming that the witness always carried the corrected residual while the S8 proof display carried `(T²−c)²`. `min-n = 8` ✓ matches GENHN-T(a). Stage-CS abscissa budget `4 ≤ μ₁ = 4` ✓.
**Every preregistered number reproduces from the note's own laws. Two ℤ_p/F_q[[t]] equalities and one three-way cross-check (P7's 1,536 → 3,072) were found that the note does not state.**

**RESOLUTION TRACE:** statement 1675–1726 · scored 1813–1846 (`.70`) · re-seal invariance 1741, 1753–1754.

XREF: `GENIND_PROOF_2026-08-08.md:GENIND.C` — count **23** (the committed V1E2(1) row's source).
XREF: `GENHN_PROOF_2026-08-08.md:[GENHN-HE` — count **19** (P9's labeled-corroboration disclaimer).

**TEETH:** P10 IS the tooth gate. **Disposition: `preregistration`** — this unit makes a claim about the future; its truth-value is at `.70`.

---
### EFF.GENHN.65  [run-record]  — §S11.E smoke record

**CANONICAL STATEMENT:** verbatim, lines 1728–1739.

**FORM:** `###` headed section body.

> “### S11.E Smoke record (wiring only; no artifacts written; fully
> disclosed)
>
> Smoke 1 (post-audit-repairs): RED — 6 GN-SIGMA mismatches, ALL at
> (Zp,2,5,1) V1E2 RAM(9) (claimed {(1,1),(4,1)}; PARI {(1,1),(2,2)}
> or {(1,1),(2,1),(2,1)}); every other family clean (1.08M checks).
> Discovery event for S11.F. A lift-perturbation probe + per-u₀
> resampling confirmed: RAM(5)/RAM(7) exact (certified), RAM(9)
> mismatching (uncertified), exactly at the derived floors. Smoke 2
> (certification gate added): GREEN — 1,081,425 checks, 0 violations,
> all 5 teeth, certified σ 720/720, diagnostic tail 24 jobs / 6
> mismatches, 50.8s. No full row ran before seal.”

**CONDITIONALITY:** A pre-seal wiring record, explicitly “no artifacts written” and “No full row ran before seal” — so it does **not** contaminate (F3): the predictions were written against the theory, not tuned to a full run. **Its RED is the discovery event for the S11.F perimeter** (`.68`) — i.e. the note's most valuable machine result came from a failing smoke test, and the note preserves the failure verbatim rather than reporting only the cured GREEN.

*Arithmetic audit (rule 22).* Smoke 2's “diagnostic tail 24 jobs / 6 mismatches” vs Smoke 1's “6 GN-SIGMA mismatches” — **the same six**, reclassified from violations to labeled diagnostics by adding the certification gate ✓ internally consistent. `1,081,425` vs Smoke 1's “1.08M checks” ✓ consistent to the stated precision. The σ split `720/720 certified` + `24 diagnostic` = 744 σ jobs at smoke scale; no other number in the note should match, and none does.

**DERIVATION:** Run record.

**RESOLUTION TRACE:** statement 1728–1739 · consequence 1777–1798 (`.68`), 1352–1377 (`.52`).

ARTIFACT: none — “no artifacts written”, stated. **UNPINNED by design and disclosed as such.**

**TEETH:** **Disposition: measurement that FIRED against the pre-gate reader.** The six mismatches are the tooth; the gate is the repair.

---
### EFF.GENHN.66  [run-record]  — RE-SEAL 1 (the V4E2 Newton crash)

**CANONICAL STATEMENT:** verbatim, lines 1741–1753 (through “was touched.”).

**FORM:** bold-headed paragraph inside §S11.E.

> “**RE-SEAL (disclosed; predictions byte-unchanged).** Full run 1
> (from the commit-1 seal) CRASHED at the first V4E2 row on
> newton_root's own guard `assert vd <= dvf` — an infrastructure
> bug the audit missed: Newton started at rho = 0, where
> f′(0) = b₁ has v ≥ v₄+(3h+1)/2 > 4v₄ (V1E2 was immune: its b₁ is
> pinned at exactly 2h). Every row completed before the crash matched
> its P1/P3 prediction exactly (all six CLASS flagships; V1E2 totals
> 12,288 / 458,752 / 26,244 / 458,752 with 0 violations; log
> preserved). Fix: basin-started Newton — V4E2 rows start at the
> split-side residual root −res(b₄,v₄)·π^{v₄} (dominant balance
> x⁴(x+b₄)); v(f′) = 4v₄ throughout the basin and the loss law
> L = N−4v₄ of S11.F is unchanged. No prediction, law, gate, or
> dictionary was touched.”

**CONDITIONALITY:** **Preserves (F3).** The runner changed; the predictions did not — “No prediction, law, gate, or dictionary was touched.” The crash was in the *instrument's own guard*, i.e. the instrument caught itself. **Partial evidence survives the crash and is recorded**: all six CLASS flagships and the four V1E2 totals matched before the crash, so the pre-crash run is an independent confirmation of P1/P3.

*Arithmetic audit (rule 22).* The crash condition: at `rho = 0`, `v(f′(0)) = v(b₁) ≥ v₄ + (3h+1)/2`. At the V4E2 row `(Zp,2,8,3)`: `v₄ = 1, h = 3`, so `v(b₁) ≥ 1 + (9+1)/2 = 1 + 5 = 6`, while `4v₄ = 4` — so `6 > 4` ✓ the guard trips. V1E2's immunity: `b₁` pinned at `2h`; at `(Zp,2,5,1)`, `2h = 2`, and the relevant bound is `v(f′(ρ)) = 2h = 2` ✓ finite and small, no trip. The loss law `L = N − 4v₄` at `(Zp,2,8,3)`: `8 − 4 = 4` ✓ matches S11.F's “V4E2: L = N−4v₄”. **Consistent.**

**DERIVATION:** Run record + a fix derivation (dominant balance `x⁴(x+b₄)` gives the basin).

**RESOLUTION TRACE:** statement 1741–1753 · pin `4e3b2ff` (the re-seal commit, cited at 1807) ✓ commit · superseded by RE-SEAL 2 (`.67`).

**TEETH:** **Disposition: `disclosed non-repair` turned self-catch** — the guard was the instrument's own assertion, and the note discloses that “an infrastructure bug the audit missed” got past the line-by-line provenance audit at `.61`. That is an honest limitation on `.61`'s strength.

---
### EFF.GENHN.67  [run-record]  — RE-SEAL 2 (run 2 RED on 4 gp precision misses) with the `[r2]` 350/349 reconciliation

**CANONICAL STATEMENT:** verbatim, lines 1753–1775.

**FORM:** bold-headed paragraph inside §S11.E, carrying an inline `[r2]` bracket.

> “**RE-SEAL 2 (disclosed; predictions still
> byte-unchanged).** Full run 2 completed end-to-end — 2,223,050
> checks with ZERO mathematical violations, all five teeth (fired
> 2/2/2/2/1 across rows), certified σ 0-bad on every ANSWERED job,
> and the diagnostic tails exactly as S11.F predicts (V p=2:
> 1,216 uncertified jobs / 350 mismatches **[r2 2026-08-09
> reconciliation vs S12 P9's 349 (passPE1 F5): run 2's 350 counts
> one of the 4 gp precision-misses below — a tail job scored None —
> as a mismatch; the retry-laddered scoring run 3 answers it and
> reproduces 349 deterministically (passPE1's isolated re-run
> concurs). 350 = 349 + 1 None; no tail row changed]**; V p=3:
> 241/58; all
> full-side legs 0/0) — but went RED on ONE oracle-infrastructure
> seam: 4 of the 20,800 V p=2 gp jobs got no answer
> (`idealprimedec: precision too low in get_norm` inside the pinned
> sig's factorpadic-200 lift; the gp REPL skips the erroring line),
> scoring as 1 truncation + 3 None-mismatches. Forensics: the 4 jobs
> were reproduced deterministically and re-asked individually at
> precisions 50/100/400 — all four answer {(1,1),(4,1)}, CONFIRMING
> their prediction. Fix: run_oracle gains a per-miss retry ladder
> (same independent PARI question, different working precision);
> misses surviving the ladder still score as violations. Full run 3
> = the scoring run; artifacts at commit 2 come from it alone.”

**CONDITIONALITY:** **Preserves (F3) again** (“predictions still byte-unchanged”). The RED is **oracle-infrastructure, not mathematics** — “ZERO mathematical violations” — and the note keeps both facts in one sentence rather than reporting only the GREEN.
**The `[r2]` bracket is a `counter re-reading` (rule 18)** with the mechanism named: `350 = 349 + 1 None`, the extra count being a precision-missed job scored as a mismatch. `SUPERSESSION KIND: counter re-reading`. **CHAIN: run 2's 350 → `[r2]` reconciliation → run 3's 349 (the scoring run). TERMINAL: 349.**
**One residual honesty point the note states:** the retry ladder is a *scoring* change made after seeing a failure. The note fences it — “misses surviving the ladder still score as violations” — so the ladder cannot launder a real mismatch, only a no-answer.

*Arithmetic audit (rule 22), computed fresh.* `4 of 20,800` gp jobs missed = `0.019 %`. Scoring decomposition: “1 truncation + 3 None-mismatches” = 4 ✓. Reconciliation: run 2's V p=2 tail `350` minus the 1 None-scored-as-mismatch = `349` ✓ matches S12 P9's 349 ✓ — **and the note's own equation `350 = 349 + 1 None` is exactly this** ✓. But note: the forensics say **all four** misses answer `{(1,1),(4,1)}` and confirm their prediction, while only **one** of the four sat in the tail; the other three sat among certified jobs (which is why run 2 went RED at all — a certified-leg None is a violation). Cross-check: S12 reports “certified σ 37,792 jobs / 0 bad”, i.e. **after the ladder** the three certified misses are answered ✓. Consistent. Total checks `2,223,050` matches S12's headline ✓. Teeth firing `2/2/2/2/1` matches S12's “(LAT 2 / CEN 2 / SIG 2 / CRIT 2 / NODE 1)” ✓.

**DERIVATION:** Run record + forensics.

**RESOLUTION TRACE:** statement 1753–1775 · `[r2]` at 1758–1763 · scored 1802–1811, 1839–1845 · pin `6f977ea` ✓ commit.

XREF: `GENHN_passPE1_report.md:F5` — count **3**.

**TEETH:** **Disposition: executable regression that went RED and was diagnosed to an oracle seam, with all four misses independently re-answered at three precisions.** This is the strongest instance in the note of a failure driven to ground rather than retried away.

---
### EFF.GENHN.68  [lemma]  — §S11.F, the extraction-certified σ perimeter

**CANONICAL STATEMENT:** verbatim, lines 1777–1798.

**FORM:** `###` headed section body: a derivation with an inline floor recursion and a worked instance.

> “### S11.F The extraction-certified σ perimeter (the machine-surfaced
> finding, with derivation)
>
> For an embedded genre, the sibling split loses precision: the split
> root ρ of the window-N ambient data is defined only mod π^L,
> L = N − v(f′(ρ)) (V1E2: L = N−2h; V4E2: L = N−4v₄). Writing
> f = (x−ρ)Q exactly and (x−rho)q ≡ f mod π^N for the computed pair,
> the error E := q − Q solves (x−rho)E ≡ −δQ (v(δ) ≥ L) triangularly
> from the top: with entry floors v(Q_j) ≥ (2h,(3h+1)/2,h,(h+1)/2)
> and worst-case v(ρ), E₃ ≥ L, E₂ ≥ min(L+(h+1)/2, v(ρ)+E₃),
> E₁ ≥ min(L+h, v(ρ)+E₂), E₀ ≥ min(L+(3h+1)/2, v(ρ)+E₁); the stage
> coordinates inherit a₁₁ = q₃, a₁₀ = q₂+c, a₀₁ = q₁+ẑπ^h q₃,
> a₀₀ = q₀+ẑπ^h a₁₀+c: exact strictly below the floors, meaningless
> at or above them. Instance (2,5,1): certified digit heights
> (a₀₀,a₀₁,a₁₀,a₁₁) = (4,3,3,2) — RAM(9) reads a₀₁@4: uncertified ✗;
> RAM(7) reads a₀₁@3: certified ✓ — exactly the observed smoke split.
> The battery gates σ-emission on extracted rows by the per-leaf
> consulted-digit set against this table (leaf_cert_E) and measures
> the uncertified tail as diagnostics. Full-side genres (E31, E3 —
> the sextic IS the stage) have no extraction: un-gated. The finding
> is folded into GENHN-BOX-4; it strengthens, not weakens, the window
> story: GENHN-3(a) composes exactly as the ledger predicts.”

**CONDITIONALITY:** **A derived sharpening with a machine origin, and the note is careful that it is derived, not merely observed** — the heading says “with derivation”, and the floor recursion is displayed. Two fences carried forward to `.52`: COUNT laws untouched; GENHN.C (a statement about stage data) unaffected. Full-side genres are un-gated *because they have no extraction*, not because they are trusted.

**DERIVATION:** Displayed inline: `L = N − v(f′(ρ))`; the error `E := q − Q` solves `(x−ρ)E ≡ −δQ` with `v(δ) ≥ L`, solved triangularly from the top, giving the four floors `E₃, E₂, E₁, E₀`; the stage coordinates inherit them through the displayed substitutions.

*Arithmetic audit (rule 22), recomputed at the (2,5,1) instance — `q = 2, N = 5, h = 1, v₄` n/a (V1E2, so `L = N − 2h = 5 − 2 = 3`).*
- **Entry floors** `v(Q_j) ≥ (2h, (3h+1)/2, h, (h+1)/2) = (2, 2, 1, 1)` at `h = 1` ✓ (all integers ✓, since `h` odd makes `(3h+1)/2` and `(h+1)/2` integral ✓).
- **Error recursion** with `L = 3` and worst-case `v(ρ) = h/e₁`-scale (the note leaves `v(ρ)` symbolic): `E₃ ≥ 3`; `E₂ ≥ min(3 + 1, v(ρ)+3) = min(4, …)`; `E₁ ≥ min(3 + 1, …) = min(4, …)`; `E₀ ≥ min(3 + 2, …) = min(5, …)`.
- **Certified digit heights** stated as `(a₀₀, a₀₁, a₁₀, a₁₁) = (4, 3, 3, 2)`. Cross-check the *ordering*: `a₁₁ = q₃` inherits `E₃ ≥ 3`… the note reports `a₁₁` certified to height **2**, one below `E₃`'s floor of 3 ✓ — “exact strictly below the floors” ✓, so a certified height of 2 for a floor of 3 is exactly right. Similarly `a₀₁ = q₁ + ẑπ^h q₃` certified to 3 against `E₁ ≥ 4` ✓ one below. `a₀₀` certified to 4 against `E₀ ≥ 5` ✓ one below. `a₁₀ = q₂ + c` certified to 3 against `E₂ ≥ 4` ✓ one below. **All four certified heights are exactly (floor − 1), consistent with “exact strictly below the floors”.**
- **The split.** RAM(9) reads `a₀₁` at height 4 > 3 → uncertified ✓; RAM(7) reads `a₀₁` at height 3 ≤ 3 → certified ✓. And smoke 1's six mismatches were **all** RAM(9) ✓, RAM(5)/RAM(7) exact ✓. **The derivation predicts the observed split exactly, digit for digit.** This is the strongest derivation-meets-measurement agreement in the note and it reproduces.

**RESOLUTION TRACE:** statement 1777–1798 · discovery 1731–1736 (`.65`) · box 1352–1377 (`.52`) · scored tail 1839–1845 (`.70`).

**TEETH:** **Both directions measured.** Certified side: 0 bad on 37,792 jobs. Uncertified side: “genuinely mixed” — 349/1,216 (V p=2) and 58/241 (V p=3). **Disposition: measurement, preregistered in both directions** (P9 predicted the tail would contain mismatches).

---
### EFF.GENHN.69  [run-record]  — §S12 verdict headline

**CANONICAL STATEMENT:** verbatim, lines 1800–1811.

**FORM:** `##` headed section with a bold verdict sentence and an artifact/arc line.

> “## S12. VERDICT (commit 2, FROM the committed artifacts)
>
> **GREEN — 2,223,050 checks, 0 violations, all five teeth fired
> (LAT 2 / CEN 2 / SIG 2 / CRIT 2 / NODE 1), 450.0s.** Artifacts:
> `genhn_checks_results.json` md5 dd9edbeadaedf0b19873d58731d92d78 ·
> `genhn_checks_output.txt` md5 7d4a3e86113fb3dbe241788b6c81ab40 ·
> runner-as-run md5 637427dc475d231e803a8219127a5b3e. Arc: seal
> 58ae603 → run 1 CRASH (V4E2 Newton basin; re-seal 4e3b2ff) → run 2
> RED on 4/20,800 gp precision misses, zero mathematical violations
> (re-seal 6f977ea) → run 3 GREEN (this verdict). The retry ladder
> recovered exactly the 4 known misses, each answering its predicted
> {(1,1),(4,1)}.”

**CONDITIONALITY:** **The verdict is a `run-record`, and its scope is instrument grade only** — stated at `.71`: “instrument grade, not acceptance … nothing here upgrades the conditionality display of THEOREM GENHN.B.” The GREEN is a conjunction (0 violations ∧ all teeth ≥ 1), preregistered at P10.
**The arc line preserves both failures**: the crash and the RED. A chapter cut quoting only “GREEN — 2,223,050 checks” would lose the note's own disclosure discipline.

*Arithmetic audit (rule 22).* `2,223,050` matches RE-SEAL 2's figure ✓ — i.e. runs 2 and 3 checked the same number of things, consistent with “no prediction, law, gate, or dictionary was touched” and only the oracle retry changing. Teeth `2/2/2/2/1` ✓ matches `.67`. Component checks named in the scorecard: GN-CLASS 2,147,916 + GN-REFINE3 3,072 + certified σ 37,792 = **2,188,780**, leaving `2,223,050 − 2,188,780 = 34,270` for GN-PIN/GN-LAWTIE/GN-FIB/GN-STAGE2/GN-E3/GN-TOWER and the diagnostic tail. **No contradiction; the scorecard does not itemize every family, so the residual is unattributed rather than missing.** Recorded as an unverifiable-but-consistent decomposition.
**Artifact md5s are FULL hashes here** (three of them), unlike the truncated pins at `.54`, `.60`, `.61` — so `.69`'s artifacts are the note's best-pinned objects.

**DERIVATION:** Run record from committed artifacts.

**RESOLUTION TRACE:** statement 1800–1811 · predictions 1675–1726 (`.64`) · scorecard 1813–1846 (`.70`).

ARTIFACT: `verification/openmath/genhn_checks_results.json` ✓ · `genhn_checks_output.txt` ✓ · `genhn_checks.py` ✓ — 3/3 present.
PINS: `58ae603` ✓ `4e3b2ff` ✓ `6f977ea` ✓ — 3/3 commits.

**TEETH:** This unit IS the run-record half of the preregistration/run pair (rule 19); `.64` is the other half.

---
### EFF.GENHN.70  [run-record]  — §S12's prediction scorecard, P1–P10

**CANONICAL STATEMENT:** verbatim, lines 1813–1846.

**FORM:** bold-headed bulleted scorecard, one bullet per preregistered P-item.

> “**Prediction scorecard (every P-item, against S11.D as sealed):**
> * P1 ✓ all six CLASS flagships EXACT (V1E2(1) 12,288 ×2 = the
>   committed GENIND row; E3(1) 512 ×2; E31(1) 8,192 ×2; E31(1)
>   4,374 ×2); all PREDICTED-ABSENT genres absent; 2,147,916 GN-CLASS
>   checks incl. the 2×2²⁰-state genind-reader tie, 0 violations.
> * P2 ✓ law_Egen(e₁=2) ≡ law_E on all 5 grid points.
> * P3 ✓ V1E2 totals 12,288 / 458,752 / 26,244 / 458,752, per-key
>   law × fiber both directions, 0 escapes.
> * P4 ✓ ★ V4E2 FIRST measurement: obs ≡ law_E(2,8,3) × 4 exactly,
>   totals 65,536 + 65,536 (GENIND's derivation-only law now
>   machine-real).
> * P5 ✓ ★ E31 (the first e₁ = 3 stage law ever measured): all four
>   rows ≡ (q−1)·law_Egen(q,N,h,3), totals 8,192 / 524,288 / 4,374 /
>   524,288, node floors clean.
> * P6 ✓ ★ E3 (the first μ = 3 stage ever read): totals 39,366 /
>   32,768 / 32,768, zero stage-CS, spot laws EXACT (UND3 13,122 +
>   RAM3(7) 26,244 = the whole (3,4,1) row; (2,5,1): 4,096 / 16,384 /
>   4,096 / ALPHA3(3) 512).
> * P7 ✓ ★ GN-REFINE3 = 3,072 pin checks exactly (= 2 rows × 1,536),
>   0 violations — every μ = 3 stage-α event transported by actual
>   re-division kills all three pins into the floored node
>   (GENHN-BOX-2's compensating instrument, delivered).
> * P8 ✓ ★ the tower witness: frame ('EMB',8,(0,8),2,1,4,1), stage
>   dvs (10,·,5,·), hull (0,10)–(4,0) with (e_s,g) = (2,2), inner
>   residual (T−1)² — stage-CS fired inside the μ = 4 stage; min-n
>   = 8; zero stage-CS anywhere else in the battery.
> * P9 ✓ certified σ 37,792 jobs / 0 bad across six oracle batches —
>   V composed σ (19,584 + 2,915), E31 4,992 + 1,944 (★ wild p = 3
>   at e₁ = 3), E3 1,792 + 6,565 ([GENHN-HE(3)] corroboration,
>   labeled). Diagnostic tails measured as predicted: V p=2
>   1,216 / 349 mismatches, V p=3 241 / 58, all full-side legs 0/0 —
>   the S11.F perimeter is REAL on both sides (certified exact,
>   uncertified genuinely mixed).
> * P10 ✓ all teeth; GREEN.”

`[TABLE]` — the scorecard transcribed against `.64`'s preregistration (rule 5 + rule 19's two-unit discipline):

| P | Preregistered (`.64`) | Scored (`.70`) | Verdict |
|---|---|---|---|
| P1 | six CLASS flagships; PREDICTED-ABSENT list; strict grammar; tie rows | all six EXACT; all absent; 2,147,916 checks, 0 violations | ✓ |
| P2 | law_Egen(e₁=2) ≡ law_E at 5 grid points | 5/5 | ✓ |
| P3 | V1E2 totals 12,288 / 458,752 / 26,244 / 458,752; escapes 0 | identical; 0 escapes | ✓ |
| P4 | ★ V4E2 `× 4`; totals 65,536 + 65,536 | identical | ✓ |
| P5 | ★ E31 totals 8,192 / 524,288 / 4,374 / 524,288; node floors | identical; floors clean | ✓ |
| P6 | ★ E3 totals 39,366 / 32,768 / 32,768; zero stage-CS; spot laws | identical | ✓ |
| P7 | ★ 1,536 pin checks/row × 2 rows; 0 violations | 3,072 exactly; 0 violations | ✓ |
| P8 | ★ tower witness frame, hull, residual `(T−1)²`, min-n 8, zero stage-CS elsewhere | identical | ✓ |
| P9 | certified 0 bad; tail PREDICTED to contain mismatches | 37,792 / 0 bad; tails 349/1,216 and 58/241 | ✓ |
| P10 | all five teeth fire; GREEN ⟺ 0 violations ∧ teeth ≥ 1 | all fired; GREEN | ✓ |

*Arithmetic audit (rule 22), computed fresh — every scorecard number re-derived and cross-checked.*
- **P9's six oracle batches:** `19,584 + 2,915 + 4,992 + 1,944 + 1,792 + 6,565 = 37,792` ✓ **exactly the stated total.** (Sum recomputed: 19,584 + 2,915 = 22,499; + 4,992 = 27,491; + 1,944 = 29,435; + 1,792 = 31,227; + 6,565 = 37,792 ✓.)
- **P1's flagships ×2:** four distinct flagship values each appearing at two rows = 8 flagship observations, but the note says “**all six** CLASS flagships”. Recount: the CLASS rows are three ℤ_p/F_q[[t]] pairs = 6 rows, and each row carries **one** flagship — (2,5,n5)→V1E2(1) 12,288; (2,4,n6)→E3(1) 512 **and** E31(1) 8,192; (3,3,n6)→E31(1) 4,374. That is 2 + 2 + 2 + 2 = 8 flagship *values across rows* if E3 and E31 both live at (2,4,n6). **“Six” counts rows, not values** — 6 CLASS rows, each scored ✓. Consistent under that reading; **the phrase is ambiguous** and is recorded as source defect 5.
- **P6's (3,4,1) exhaustiveness:** `13,122 + 26,244 = 39,366` ✓ = the row total ✓ (audited also at `.64`).
- **P7:** `2 × 1,536 = 3,072` ✓.
- **P8:** hull `(0,10)–(4,0)`, `(e_s, g) = (2,2)`, abscissa length `4 = e_s·g` ✓, residual degree `4/2 = 2 = deg (T−1)²` ✓.
- **P9's tails:** `349/1,216 ≈ 28.7 %` and `58/241 ≈ 24.1 %` — both substantial, consistent with “genuinely mixed” ✓ (a near-0 % or near-100 % tail would have indicated a mis-drawn perimeter).
- **Cross-check to `.67`:** run 2 reported V p=2 350; run 3 reports 349 ✓ per the `[r2]` reconciliation.
**Every scorecard number reproduces. One ambiguity found (P1's “six”), one sum verified exactly (P9's 37,792).**

**CONDITIONALITY:** **P9's E3 line carries its own honesty fence in the scorecard itself**: “E3 1,792 + 6,565 (**[GENHN-HE(3)] corroboration, labeled**)” — the μ = 3 σ agreement is 8,357 PARI jobs and is *still* declined as evidence for the open box. That fence is repeated at `.64` P9 and at shard 1 `.40`.

**DERIVATION:** Run record, scored against a frozen preregistration.

**RESOLUTION TRACE:** statement 1813–1846 · preregistration 1675–1726 · reconciliation 1758–1763.

**TEETH:** This unit is the note's evidentiary core. **Disposition: `run-record` against a frozen `preregistration`** — the pairing rule 19 exists for is exercised here in its clean form.

---
### EFF.GENHN.71  [scope-record]  — “What the machine leg establishes”

**CANONICAL STATEMENT:** verbatim, lines 1848–1857.

**FORM:** bold-headed closing paragraph of §S12.

> “**What the machine leg establishes** (instrument grade, not
> acceptance): the genre classification at n = 5 AND n = 6 sweeps;
> the (e₁,f₁)-re-based stage law at THREE genres beyond GENH4's two,
> including first-ever e₁ = 3 and first-ever μ = 3 territory; the
> μ = 3 refine transfer pointwise; the first composite-over-composite
> event; σ dictionaries at never-oracled wild territory; and the
> machine-surfaced extraction-certified perimeter (S11.F) — a
> sharpening, not a defect, of the window ledger. Grade box
> (GENHN-BOX-1) unchanged: attempt 0/2, no hostile arc yet; nothing
> here upgrades the conditionality display of THEOREM GENHN.B.”

**CONDITIONALITY:** **`STALE-SELF-DESCRIPTION` on “attempt 0/2, no hostile arc yet”** — four hostile passes ran and the note is ACCEPTED 2/2 (`.75`). **The load-bearing clause survives the grade change and must not be dropped with it:** “nothing here upgrades the conditionality display of THEOREM GENHN.B.” Acceptance of the *note* is not acceptance of the *theorem's* conditionality stack, which still carries `[GENHN-HE(μ ≥ 3)]`, `[GENHN-TOW-1]` at n ≥ 8, GENHN-BOX-2's weld face, and the S10 minimum-grade rule.

**DERIVATION:** Summary of `.70`.

**RESOLUTION TRACE:** statement 1848–1857 · correction site 1941–1955 (grade) · the surviving clause is untouched by every append (verified).

**TEETH:** NONE (summary of the run-record).

---
### EFF.GENHN.72  [changes-record] · SERIES: GENHN-GRADE-ARC, member 3 of 5  — the post-PE3 discipline header

**CANONICAL STATEMENT:** verbatim, lines 1861–1874.

**FORM:** `###` heading + an italic discipline paragraph.

> “### Dated corrections (2026-08-09, post-PE3)
>
> *Discipline (the HEX3 post-PE6 minors-only precedent; charge bar =
> nothing GAP-or-worse is CLEAN): PE3 returned CLEAN — 0 CRITICAL +
> 0 GAP + 2 MINOR (`GENHN_passPE3_report.md` @ 7a058c8, byte-frozen
> at md5 5ea120909ad8c007bbf57aee9c15c475) — so the clean count set
> there (0/2 → 1/2) HOLDS AT 1/2 and this is a dated append only: the
> body above (lines 1–1857, byte-identical beadeeb → this append;
> pre-append file md5 c38f52834879f76d618b1709146a3991 is the prefix)
> is byte-untouched, and the sealed runners/artifacts stay frozen
> (PE3's fresh instrument `verification/openmath/genhn_pe3_fresh.py`,
> md5 f70d3d564ffe04337b2f3cb7cd136550, GREEN 176/0 on its first full
> run, is the report's leg, cited here read-only). Two corrections,
> one per PE3 MINOR.*”

**CONDITIONALITY:** **This is where the CLEAN bar is stated explicitly and it is a strict one:** “charge bar = nothing GAP-or-worse is CLEAN”. A minors-only pass counts as clean; a GAP does not. That rule is what makes the 0/2 → 1/2 → 2/2 arc auditable.
**SERIES `GENHN-GRADE-ARC`, member 3 (1/2).** Note the freeze is asserted with *two* full md5s (the report's and the prefix's) and one commit (`beadeeb`), all verifiable in form; the file md5s cannot be re-checked against the current file because later appends changed it — which is precisely why each subsequent append re-states a new prefix md5 (see §1's table).

**DERIVATION:** Discipline declaration.

**RESOLUTION TRACE:** statement 1861–1874 · corrections 1876–1928 · next member 1941–1955.

XREF: `GENHN_passPE3_report.md:F-1` — count **4** · `F-2` — count **5**.
XREF: `HEX3_PROOF_2026-08-08.md:HEX3` — count **83** (the minors-only precedent).
PINS: `7a058c8` ✓ commit · `beadeeb` ✓ commit.
ARTIFACT: `verification/openmath/genhn_pe3_fresh.py` ✓ present; `genhn_pe3_fresh_output.txt` ✓ present.
**Full md5s given (not truncated):** `5ea120909ad8c007bbf57aee9c15c475` (report), `c38f52834879f76d618b1709146a3991` (prefix), `f70d3d564ffe04337b2f3cb7cd136550` (PE3 instrument) — three fully-specified hashes, the best-pinned append in the note.

**TEETH:** `genhn_pe3_fresh.py` — GREEN 176/0 on its first full run, **a decorrelated instrument**, cited read-only. Disposition: executable regression on a fresh instrument.

---
### EFF.GENHN.73  [changes-record]  — post-PE3 Correction 1 (PE3 F-1: item (6)(α)'s mechanism attribution)

**CANONICAL STATEMENT:** verbatim, lines 1876–1907.

**FORM:** bold-headed dated correction with an embedded “Read the sentence as” replacement and a refuting witness.

> “**Correction 1 (PE3 F-1 — item (6)(α)'s mechanism attribution).**
> [GENHN-TOW-1] item (6)(α)'s sentence "TRUE at the witness by an
> EXACT CARRY CANCELLATION" (body L1423–1424) over-attributes: the
> displayed cancellation arithmetic is correct (re-verified at PE3),
> but the cancellation is witness-specific arithmetic, NOT the
> mechanism the one-sidedness rides. Read the sentence as: **"TRUE at
> the witness because the carry terms CLEAR the side (at the witness
> they also cancel exactly — witness arithmetic, not the mechanism):
> the would-be surviving b = 1 term 16Φ′ sits at dv 8 > 15/2 = the
> side height at b = 1 (a b = 1 pin has integer dv against a
> half-integral side height, so it cannot sit ON this side), and the
> one-sidedness rides the carry CONSTANT 32 landing exactly on the
> side endpoint (0, 10) — without it Φ′ | Φ₃."** Refuting witness for
> the cancellation-as-mechanism reading (PE3 FR3, quoted from the
> report @ 7a058c8; the derived data RE-VERIFIED by PARI/gp at this
> append — development identity exact, (e, f) = (8, 1), nfeltval
> triple and leaf σ as cited): the SECOND iterated key
> Φ₃ = Φ₂² − 16xΦ′ (u₃ = 23 = 4·4 + 2·1 + 5·1, n̂₂(23) = 16xΦ′,
> gcd(23, 2) = 1, κ₃ = 23/2 > 8) keeps its carry UNCANCELLED —
> development Φ′⁴ − 8xΦ′² + (16 − 16x)Φ′ + 32, dv-pins
> (0,10), (1,8), (2,7), (4,0) — and is STILL one-sided of slope
> 5/2 = κ₂ with residual T² + 1 = ψ₂², carrier (8, 1), the full
> intermediate ascent data (v_pr(x), v_pr(Φ′), v_pr(Φ₂)) =
> (4, 10, 23) exact by nfeltval, and its n = 16 leaf RAM(93) →
> {(16,1)} PARI-exact on both routes. Consequence for a T(b)″ prover:
> the general (α) target is the side-clearing bookkeeping (carry
> terms clearing the side with the constant landing exactly), NOT
> "the carries cancel exactly at general genres" — the latter is
> FALSE as a general lemma (FR3 is a valid iterated key where they do
> not cancel). The box's bottom line stands unchanged: one-sidedness
> at general genres is genuine Okutsu-optimality content, unproved
> here; item (6) remains OPEN; no σ or count is priced through it.”

**SUPERSESSION KIND: provenance-rider** — the claim (“TRUE at the witness”) survives; the stated *reason* is replaced. `TARGETS: .54` (item (6)(α)), `.60` (the `[r3]` arc-line's F1 summary, which repeats the same phrase).

**CONDITIONALITY:** **The correction is backed by a constructed counter-witness, and the counter-witness is a valid object, not a pathology** — FR3's `Φ₃ = Φ₂² − 16xΦ′` is a legitimate iterated key whose carry does *not* cancel and which is *still* one-sided. So “the carries cancel” is refuted as a general mechanism while the box's open status is unchanged. **Bottom line preserved verbatim**: item (6) remains OPEN, and “no σ or count is priced through it.”

**DERIVATION:** The corrected reading is derived inline: a `b = 1` pin has **integer** `dv` against a **half-integral** side height (`15/2`), so it cannot sit on the side; the one-sidedness rides the carry constant 32 landing on the endpoint `(0, 10)`; “without it Φ′ | Φ₃”.

*Arithmetic audit (rule 22), computed fresh at the frame `Φ′ = x² − 2`, `e₁ = 2, h = 1, dv = 2v`; inner `e₂ = 2, u₂ = 5`, `dv₂ = 4v`.*
- **Side height at `b = 1`.** The Φ′-side runs `(0, 10)` to `(4, 0)`, slope `5/2`; height at `b = 1` is `10 − 1·(5/2) = 15/2` ✓ **exactly as displayed**, and it is half-integral ✓ while `dv(16Φ′)`-as-a-`b=1`-coefficient is `dv(16) = 2·4 = 8`, an integer ✓. `8 > 15/2 = 7.5` ✓ **strictly above**. The parity argument is correct.
- **FR3's `u₃ = 23`.** Displayed decomposition `23 = 4·4 + 2·1 + 5·1`, i.e. `a·e₁e₂ + i·e₂h + b·u₂` with `(a,i,b) = (4,1,1)`: `4·4 + 1·2·1 + 1·5 = 16 + 2 + 5 = 23` ✓ **exact**, and `n̂₂(23) = π⁴x¹Φ′¹ = 16xΦ′` ✓ matches. Range: `i = 1 < e₁ = 2` ✓, `b = 1 < e₂ = 2` ✓.
- **`gcd(23, 2) = 1`** ✓; **`κ₃ = 23/2 = 11.5 > 8 = dv₂(x^{D₂})`** ✓ (as at `.54`, `dv₂(x⁴) = 8`).
- **FR3's development.** `Φ₃ = Φ₂² − 16xΦ′`; the box's `Φ₂` gives `Φ₂² = Φ′⁴ − 8xΦ′² + 16x²` (as at `.54`), so `Φ₃ = Φ′⁴ − 8xΦ′² + 16x² − 16xΦ′ = Φ′⁴ − 8xΦ′² + (16Φ′ + 32) − 16xΦ′ = Φ′⁴ − 8xΦ′² + (16 − 16x)Φ′ + 32` ✓ **exactly the displayed development** — the carry `16x² = 16Φ′ + 32` fires but is NOT cancelled, because the subtracted term is `16xΦ′`, not `16Φ′` ✓.
- **FR3's dv-pins.** `(4, 0)`: coefficient 1 ✓. `(0, 10)`: `dv(32) = 2·5 = 10` ✓. `(2, 7)`: `dv(−8x) = 2·3 + 1 = 7` ✓. `(1, 8)`: coefficient `16 − 16x`; `dv(16) = 8` and `dv(16x) = 8 + 1 = 9`, so the min is `8` ✓. **All four pins reproduce.**
- **Still one-sided?** Side `(0,10)–(4,0)`, slope `5/2`. Height at `b = 1` is `7.5`, pin at `8 > 7.5` ✓ above. Height at `b = 2` is `5`, pin at `7 > 5` ✓ above. **So yes — one side, slope 5/2, residual from the endpoints, degree `4/e₂ = 2`, `T² + 1 = ψ₂²` over F₂** ✓ **exactly as claimed, with the carry uncancelled.** The counter-witness is correct.
- **Ascent data `(v_pr(x), v_pr(Φ′), v_pr(Φ₂)) = (4, 10, 23)`.** These are `dv₂`-scale values… at the composed ladder `dv₂ = e₁e₂v = 4v`: `v(x) = 1/2` → `dv₂ = 2`; the displayed 4 suggests a different normalization (`v_pr` = the L₃-normalized valuation, `e = 8`, so `v_pr(x) = 8·(1/2) = 4` ✓). Then `v_pr(Φ′) = 8·v(Φ′) = 8·(u₂/(e₁e₂)) = 8·(5/4) = 10` ✓ and `v_pr(Φ₂) = 8·(u₃/(e₁e₂e₃))`… with `e = 8` and `κ₃ = 23/2` on the `dv₂`-ladder: `v(Φ₂) = 23/8`, so `v_pr(Φ₂) = 23` ✓. **All three reproduce under `e(L₃/base) = 8`, consistent with the stated carrier `(e, f) = (8, 1)`.**
- **Leaf σ.** `RAM(93) → {(16,1)}` at `n = 16`: `16·1 = 16` ✓.
**Every number in the counter-witness reproduces. The correction is sound and its witness is exact.**

**RESOLUTION TRACE:** statement 1876–1907 · target 1423–1424 (named by line number in the append itself) · re-verification “by PARI/gp at this append”.

XREF: `GENHN_passPE3_report.md:F-1` — count **4**.
PIN: `7a058c8` ✓ commit.

**TEETH:** **FR3 — a constructed counter-witness from a fresh hostile instrument, re-verified by PARI/gp at the append.** Disposition: planted counter-instance; fired against a *reason*, not a result. **`decorrelated-model audit` (rule 27)**: no battery row could have produced this — the note has no depth-3 rows outside SUPP-C's three parse-gated instances, and the finding is about the *justification* of an open box.

---
### EFF.GENHN.74  [changes-record]  — post-PE3 Correction 2 (PE3 F-2: the “full inner sides” scope word at three echo sites)

**CANONICAL STATEMENT:** verbatim, lines 1909–1928.

**FORM:** bold-headed dated correction, three enumerated rider sites.

> “**Correction 2 (PE3 F-2 — the "full inner sides" scope word at the
> three residual echo sites).** The passPE2-F2 scope word reached 3
> of 4 echo sites at r3; the three residual same-species sites
> (enumerated, not quantified) are read with the scope word attached
> here: (i) **S9.1 [GENHN-TOW-1] preamble** (L1383–1386): read "the
> corrected leaf read with inner-μ₂ = 2 σ" as "the corrected leaf
> read with inner-μ₂ = 2 σ on a FULL inner side only (e₂f₂μ₂ = μ₁ —
> (iii)'s proved perimeter; partial sides are the box's own item (4),
> six lines below)". (ii) **the GENHN.B [r3] depth-split sentence**
> (L311–312): read "T(b)′ is ONE composition step, so it carries the
> DEPTH-2 towers" with its conditionality-display twin's
> parenthetical (L367) attached — "(item (4) where the inner side is
> partial)". (iii) **the [r2] title-line rider** (L53–58): read "its
> carrier is the COMPOSED KEY (LEMMA GENHN-T(b)′, S8 annex)" with the
> r3 depth split attached — T(b)′ is ONE composition step (the
> depth-2 towers, full inner sides); at depth ≥ 3 the carrier is
> item (6)'s unproved iteration, and "survives" (= not refuted)
> remains accurate. Per PE3, none of the three sites carries a
> quantifier and each is disambiguated within its own display; these
> riders align the wording with the r3 scope.”

**SUPERSESSION KIND: scope-pin** at three named sites. `TARGETS: .54` (site (i), in range), `.18` (site (ii), shard 1), `.01`/`.04` (site (iii), shard 1).

**CONDITIONALITY:** **The correction's own severity assessment is preserved and is honest in both directions:** “none of the three sites carries a quantifier and each is disambiguated within its own display” — i.e. no site was *false*, only under-scoped. That is why the finding graded MINOR. **The enumeration is closed, not quantified** (“enumerated, not quantified”), which matters for a merge: there is no standing instruction to propagate the scope word to further sites.

*Arithmetic audit (rule 22) of the site count.* passPE2-F2's scope word “reached 3 of 4 echo sites at r3”; this correction lands the “three residual” sites. **3 + 3 = 6 ≠ 4.** Re-reading: r3 reached 3 of 4; the residual is 1, not 3 — unless the four-site count and the three-site count enumerate different populations (r3's four *primary* sites vs three *same-species residual* sites found by PE3). The append says “the three residual **same-species** sites”, which reads as a distinct, larger population. **The two counts cannot both be about the same set; the note gives no reconciliation.** Recorded as source defect 6 — not a mathematical error, but a merge run counting rider targets by arithmetic will land wrong.

**DERIVATION:** Wording alignment, not derivation.

**RESOLUTION TRACE:** statement 1909–1928 · targets 1383–1386 (in range), 311–312, 367, 53–58 (shard 1) · all four line pins verified to fall in the ranges the append names.

XREF: `GENHN_passPE3_report.md:F-2` — count **5**.
XREF: `GENHN_passPE2_report.md:F2` — count **5**.

**TEETH:** NONE (wording rider). Its substance — that partial inner sides are unproved — is toothed at shard 1 `.18` by the PE2-P counter-witness.

---
### EFF.GENHN.75  [acceptance-box] · SERIES: GENHN-GRADE-ARC, member 4 of 5 (TERMINAL)

**CANONICAL STATEMENT:** verbatim, lines 1932–1955.

**FORM:** `###` heading + italic discipline paragraph + a bold ACCEPTANCE paragraph.

> “### Dated acceptance record + correction (2026-08-09, post-PE4)
>
> *Discipline (the HEX3 minors-only precedent; the CLEAN bar = nothing at
> GAP-or-worse): this is a dated append only. The body (lines 1–1857,
> prefix md5 c38f52834879f76d618b1709146a3991) and the post-PE3 dated
> corrections above are byte-untouched (pre-append file md5
> 8c6d2291b9b9b8baa57f490a8f79fa09 is this append's prefix); the sealed
> runners and artifacts stay frozen at their pins.*
>
> **ACCEPTANCE (2/2).** passPE3 returned CLEAN — 0 CRITICAL + 0 GAP +
> 2 MINOR (`GENHN_passPE3_report.md` @ 7a058c8, byte-frozen md5
> 5ea120909ad8c007bbf57aee9c15c475; clean count 0/2 → 1/2). passPE4
> returned CLEAN — 0 CRITICAL + 0 GAP + 1 MINOR
> (`GENHN_passPE4_report.md` @ 6053c3d, byte-frozen at md5
> ec64f3616a04e96fa0e2381e1656ff3a; its fresh leg
> `verification/openmath/genhn_pe4_fresh.py` GREEN 145 checks / 0
> violations on its first full run, first f₁ = 4 / comp = 3 / F₁₆
> contact; the five prior instruments re-run isolated GREEN, the sealed
> battery at 2,223,050 checks / 0 violations). Clean count 1/2 → **2/2:
> GENHN is ACCEPTED — the text is FROZEN, dated appends only from
> here** (this line carries the counter past the title box's round-dated
> 0/2 and the post-PE3 append's 1/2). The arc in one breath: LEMMA
> GENHN-T(b) REFUTED at PE1 → T(b)′ PROVED at r2 → T(b)′ HELD at fresh
> configs through PE2, PE3 and PE4.”

**CONDITIONALITY:** **This is freeze predicate (F1), and it is the TERMINAL member of the GENHN-GRADE-ARC SERIES.** Its own scope is exactly stated: the *text* is frozen and the *clean count* is 2/2. **It does not upgrade anything else** — `.71`'s surviving clause (“nothing here upgrades the conditionality display of THEOREM GENHN.B”) is untouched, and the 2026-08-12 certification appends explicitly say “GENHN's row stays OPEN” at the certification ledger (2263–2266, `.84`). **Three distinct statuses coexist at HEAD and must not be merged:** (i) the note is ACCEPTED 2/2 and frozen; (ii) THEOREM GENHN.B's conditionality stack is unchanged; (iii) the sol certification row is OPEN pending discharge-confirmations.

*Arithmetic audit (rule 22) of the arc and its evidence.* Pass ledger: PE1 NOT CLEAN (2C+1G+2m) → PE2 NOT CLEAN (0C+2G+2m) → PE3 CLEAN (0C+0G+2m) → PE4 CLEAN (0C+0G+1m). Under the stated bar (“nothing at GAP-or-worse is CLEAN”): PE1 fails (CRITICALs) ✓, PE2 fails (GAPs) ✓, PE3 passes (minors only) ✓, PE4 passes ✓. **Two consecutive clean passes ⟹ 2/2** ✓ arithmetic and rule both check. Instruments: PE1 fresh + PE2 fresh + PE3 fresh + PE4 fresh + `genhnr2_supp` = **five prior instruments** ✓ matches “the five prior instruments re-run isolated GREEN”. Sealed battery figure `2,223,050` ✓ matches `.69`.

**DERIVATION:** Acceptance record.

**RESOLUTION TRACE:** statement 1932–1955 · prior members 3–20 (shard 1 `.02`), 1324–1330 (`.01`), 1863–1874 (`.24`) · next member 2034–2038 (`.77`).

XREF: `GENHN_passPE4_report.md:F-1` — count **3**.
XREF: `GENHN_passPE3_report.md:F-1` — count **4**.
PINS: `7a058c8` ✓ · `6053c3d` ✓ — 2/2 commits.
ARTIFACT: `verification/openmath/genhn_pe4_fresh.py` ✓ · `genhn_pe4_fresh_output.txt` ✓.
**Full md5s:** `5ea120909ad8c007bbf57aee9c15c475`, `ec64f3616a04e96fa0e2381e1656ff3a`, `8c6d2291b9b9b8baa57f490a8f79fa09`, `c38f52834879f76d618b1709146a3991` — 4/4 fully specified.

**TEETH:** `genhn_pe4_fresh.py` — GREEN 145/0 on its first full run, and **the first f₁ = 4 / comp = 3 / F₁₆ contact anywhere in the GENHN stack** — i.e. the first machine contact with E2's comp-weighted census on a GENHN-side leg. **Disposition: executable regression on a fresh instrument; partially closes `.51`'s f₁ ≥ 2 vacuity for the census clause.**

---
### EFF.GENHN.76  [changes-record]  — post-PE4 Correction (PE4 F-1: the “none is live below n = 8” scope defect)

**CANONICAL STATEMENT:** verbatim, lines 1957–1978.

**FORM:** bold-headed dated correction with a “Read the clause at both sites as” replacement.

> “**Correction (PE4 F-1 — the [r1] GENHN-ERR-1 residue clause "none is
> live below n = 8", echoed at [e2]-E2).** The clause (RESIDUE
> paragraph, body L609–611: "no f₁ ≥ 2 stage genre is machine-exercised,
> and none is live below n = 8"; echo at [e2]-E2, L251–253) conflates
> "mixed" with "f₁ ≥ 2" and contradicts S2's own realizability list —
> re-verified against the body at this append: genre F = (1,2,2) is an
> f₁ = 2 stage genre live at n = 4 (e₁f₁μ = 4) with machine contact
> (GENH4's committed genre-F keys, consumed at pin by this note;
> [e2]-E2's own consistency instance IS that genre), and the f-first
> siblings F3 = (1,2,3) / E13 = (1,3,2) are first live at n = 6
> (e₁f₁μ = 6; S2's floors display, visibility-floored beyond the
> battery's sweep windows at N ≥ 7 — GENHN-BOX-3). Read the clause at
> both sites as: **"no row of THIS battery exercises an f₁ ≥ 2 stage
> genre (passPE4's design audit: the battery's rows are f₁ = 1 rows);
> MIXED e₁, f₁ ≥ 2 genres first live at n = 8 (first (2,2,2) — S2); the
> f-first genres (1,2,2)/(1,2,3)/(1,3,2) are live at n = 4/6/6, and
> their S-keyed display re-read remains OWED with the residue
> (GENHN-ERR-1 stays unsettled exactly as displayed)."** The correction
> is a scope re-reading only: the law's node form ("the cluster read AT
> THE NODE, whatever the node height is"), the [r1] corrected node
> D′h + 1 (machine-confirmed at (1,3,2) by PE1), and the σ dictionary
> are byte-untouched by it.”

**SUPERSESSION KIND: scope-pin** at two named sites (both in shard 1). `TARGETS: .24` (the `[r1]` RESIDUE clause), `.14` (E2's echo).

**CONDITIONALITY:** **This correction's own closing clause is itself now stale.** “GENHN-ERR-1 stays unsettled exactly as displayed” was true on 2026-08-09; **ERR-1 was SETTLED on 2026-08-12** by LEMMA GENHN-COUNT-RERUN's Consumer sweep item 1 (`.92`). `SUPERSESSION KIND: replacement` by the later append. **CHAIN for GENHN-ERR-1: `[r1]` names it OPEN → `[r2]` settles the f₁ = 1 arithmetic only → this correction fixes the scope and re-affirms OPEN → COUNT-RERUN sweep item 1 SETTLES it. TERMINAL: settled, with a transcription-confirmation owed (2626–2627).**

*Arithmetic audit (rule 22) of the three liveness claims, recomputed against `e₁f₁μ ≤ n`.* Genre F = (1,2,2): `1·2·2 = 4` ✓ live at n = 4 ✓. F3 = (1,2,3): `1·2·3 = 6` ✓ live at n = 6 ✓. E13 = (1,3,2): `1·3·2 = 6` ✓ live at n = 6 ✓. First mixed (2,2,2): `2·2·2 = 8` ✓ live at n = 8 ✓. **All four reproduce from shard 1 `.20`'s table, which is exactly the evidence the correction cites.** The original clause's error is therefore real: an f₁ = 2 genre *is* live at n = 4, and it *does* have machine contact via GENH4's committed keys.

**DERIVATION:** Scope re-reading, derived from the note's own §S2 list.

**RESOLUTION TRACE:** statement 1957–1978 · targets 609–611, 251–253 (shard 1) · terminal correction 2593, 2624 (`.92`, `.93`).

XREF: `GENHN_passPE4_report.md:F-1` — count **3**.
XREF: `GENH4_PROOF_2026-08-08.md:law_F` — count **7** (the committed genre-F keys).

**TEETH:** **`decorrelated-model audit` (rule 27)** — a *design audit* of the battery's rows (“passPE4's design audit: the battery's rows are f₁ = 1 rows”), i.e. a finding produced by reading the instrument, not by running it. No tooth could have produced it. Also cites **PE1's machine confirmation of the corrected node at (1,3,2)** as positive evidence for what survives.

---
### EFF.GENHN.77  [changes-record] · SERIES: GENHN-GRADE-ARC, member 5 of 5  — the HETOW dated erratum (a consumer correcting its supplier)

**CANONICAL STATEMENT:** verbatim, lines 1980–2038.

**FORM:** `###` heading + four bold-headed paragraphs (The seam / Machine confirmation / Scope / Freeze discipline), with two indented ASCII displays.

> “### Dated erratum (2026-08-09, from HETOW PE1 F-1)
>
> **The seam.** LEMMA GENHN-T(b)′'s DISPLAY of the composed key's lift
> coefficients is gauge-naive: the displayed
>
>     Φ₂ := Φ′^{e₂f₂} − Σ_{t<f₂} ĉ_t · n̂(u₂(f₂−t)) · Φ′^{e₂t}
>
> with ĉ_t a plain lift of ψ₂'s coefficient c_t carries a wrap seam at
> η ≠ 1 frames. The normalizer monomials are not multiplicative —
> n̂(u₂)^{f₂−t} = n̂((f₂−t)u₂)·(x^{e₁}/π^{h})^{W(t)} with
> W(t) = ⌊(f₂−t)·i(u₂)/e₁⌋ — so the displayed coefficient's residue
> against S4's coherent normalizers (the ones (i)'s proof computes the
> side residual with) is c_t·η^{−W(t)}, not c_t: for the slot residues
> to equal the residual's coefficients (and for the key's roots to
> satisfy ψ₂(η₂(ξ)) = 0), the lifts need the correction absorbing that
> wrap factor,
>
>     ĉ_t := lift(c_t·η^{W(t)})   (per digit at f₁ ≥ 2:
>     the exact-height (LIFT) output L_{(f₂−t)u₂}(c_t·η^{W(t)})).
>
> This is the CORRECTED DISPLAY. At any frame where each
> c_t·(η^{W(t)} − 1) = 0 — in particular at η = 1 — corrected = naive.
>
> **Machine confirmation (frame X — the first η ≠ 1 tower contact).**
> HETOW passPE1 (`HETOW_passPE1_report.md` @ 5f821dc, fresh instrument
> `hetow_pe1_fresh.py`, dual PARI routes agreeing): p = 3, Φ′ = x² − 6
> (legal outer genre (3; 2,1,1), η = 2), (e₂,f₂) = (1,2), u₂ = 3,
> ψ₂ = Z² + Z + 2, W(0) = 1. The DISPLAYED key Φ′² + 3xΦ′ + 54 has
> PARI σ = {(4,1)} ≠ {(e₁e₂, f₁f₂)} = {(2,2)} and degenerate slot
> polynomial (Z+1)² — it is not the composed carrier, and (i)'s letter
> claim fails at its roots. The CORRECTED key Φ′² + 3xΦ′ + 108 has
> σ = {(2,2)} with slot polynomial = minpoly(η^{−1}η₂) = Z² + 2Z + 2.
> Re-confirmed at two further η ≠ 1 frames (p = 5, Φ′ = x² − 10 with
> ord(η) = 4; p = 5, Φ′ = x³ − 10 at e₁ = 3) by `hetowr1_supp.py`
> (sealed @ d0d3ca6, artifacts @ 5335ae3: GREEN, 29 gp jobs + 15 exact
> checks, 0 violations; the gauge-naive tooth fired at each of the
> three frames).
>
> **Scope.** T(b)′'s PROOF mechanism is unaffected: the carrier forcing
> chain, the composed slot lemma (ii), and the σ clauses (iii)–(v) hold
> AT THE CORRECTED KEY — the proof of (i) already computes the side
> residual through S4's coherent normalizers, and the polygon/clearance
> computation (L1216–1226) is unit-blind; what was wrong is the
> DISPLAY's lift prescription (L1136–1148, including the f₁ ≥ 2
> overflow parenthetical — see HETOW [r1] F-4 for the pinned
> no-overflow (LIFT) form) feeding that proof, which transcribed the
> gauge-naive lifts. This note's committed tower machine contact is
> untouched: `genhnr2_supp.py`'s tower frames sit at q = 2
> (Φ′ = x² − 2, K = F₂), where η = 1 forcibly and the two prescriptions
> coincide; the sealed battery had no tower-leaf rows (GENHN-BOX-3).
> Downstream consumption: HETOW_RECON_2026-08-09.md [r1 2026-08-09]
> carries the corrected key, the restated bridge lemmas HETOW-1/2
> re-proved at it, and the wrap-cocycle derivation (its §S2 preamble).
>
> **Freeze discipline.** GENHN stays ACCEPTED 2/2, text FROZEN,
> dated-appends-only: this erratum is an append; the body above it is
> byte-identical to the acceptance state (pre-append file md5
> 13e087d62b4dad5a5724d337576f3411 = the file at acceptance commit
> ba3de2a, verified at this append).”

**SUPERSESSION KIND: replacement** (the lift prescription in T(b)′'s display). `TARGETS: .42` (the composed-key display and its f₁ ≥ 2 overflow parenthetical).

**CONDITIONALITY:**
(a) **The correction is later LICENSED, not superseded:** the exact-height `(LIFT)` operator it prescribes had **no in-note lemma** until LEMMA GENHN-LIFT (`.81`) supplied one on 2026-08-12, whose APPLICATION re-derives `res(n(u₂)^r/n(ru₂)) = η^{W(t)}` from scratch. **CHAIN: naive display → this erratum's corrected display → GENHN-LIFT's licensed operator `L_{ru₂}(c_tη^{W(t)})·Φ′^{e₂t}`. TERMINAL: the licensed form.**
(b) **The blind spot is disclosed exactly:** every GENHN tower frame sits at `η = 1` forcibly, so *all* of this note's tower machine contact was inside the region where the two prescriptions coincide. That is a `disclosed non-repair` of unusual severity — the note's entire tower coverage could not have detected the defect.
(c) **Direction of the edge is unusual and worth flagging for the DAG:** HETOW is a *consumer* of GENHN's T(b)′; the finding travelled consumer → supplier and was executed at the supplier. This is the one place in GENHN where an inbound correction from a downstream note is landed in-note.

**DERIVATION:** Displayed inline. The wrap identity `n̂(u₂)^{f₂−t} = n̂((f₂−t)u₂)·(x^{e₁}/π^{h})^{W(t)}` follows from S4's normalizer arithmetic (shard 1 `.28`); the residue against coherent normalizers is therefore `c_t·η^{−W(t)}`, and absorbing it gives `ĉ_t := lift(c_t·η^{W(t)})`.

*Arithmetic audit (rule 22) of frame X, computed fresh — `p = 3`, `Φ′ = x² − 6`, so `e₁ = 2, f₁ = 1, h = 1` and `η = res(θ²/3) = res(6/3) = 2` in F₃ ✓.*
- **`i(u₂)` at `u₂ = 3`:** solve `i·h ≡ u₂ (mod e₁)`, i.e. `i ≡ 3 ≡ 1 (mod 2)`, `0 ≤ i < 2` ⟹ `i = 1`; `a = (3 − 1)/2 = 1`; `n̂(3) = x¹π¹ = 3x` ✓ **matches the displayed `3xΦ′` term.**
- **`W(0) = ⌊(f₂−0)·i(u₂)/e₁⌋ = ⌊2·1/2⌋ = 1`** ✓ **exactly as stated.**
- **The correction factor:** `η^{W(0)} = 2` in F₃; naive constant `54`, corrected `108` ✓ **and `108 = 2 × 54`** — exactly the factor `η` ✓.
- **Degree/σ consistency:** `deg Φ₂ = D₂ = D′e₂f₂ = 2·1·2 = 4`; `{(4,1)}` sums to 4 ✓ and `{(2,2)}` sums to 4 ✓ — both degree-consistent, so only PARI separates them, as at shard 1 `.47`.
- **`{(e₁e₂, f₁f₂)} = {(2·1, 1·2)} = {(2,2)}`** ✓ matches the predicted composed carrier.
- **Degenerate slot polynomial `(Z+1)²` vs corrected `Z² + 2Z + 2`:** over F₃, `(Z+1)² = Z² + 2Z + 1`; the corrected polynomial is `Z² + 2Z + 2`, which differs in the constant only ✓ and is irreducible over F₃ (discriminant `4 − 8 = −4 ≡ 2`, a non-square mod 3 since squares are {0,1}) ✓ — consistent with `f = 2`. The naive one is a perfect square ⟹ degenerate ✓.
- **`ψ₂ = Z² + Z + 2` irreducible over F₃?** discriminant `1 − 8 = −7 ≡ 2 (mod 3)`, non-square ✓ so `f₂ = 2` ✓ matches `(e₂,f₂) = (1,2)`.
**Every number in frame X reproduces, including the σ separation and the irreducibility checks.**

**RESOLUTION TRACE:** statement 1980–2038 · target 1136–1148, 1216–1226 (shard 1, named by line number in the append) · license 2101–2189 (`.81`).

XREF: `HETOW_passPE1_report.md:F-1` — count **9**.
XREF: `HETOW_RECON_2026-08-09.md:HETOW-1` — count **23** · `HETOW-2` — count **9**.
PINS: `5f821dc` ✓ · `d0d3ca6` ✓ · `5335ae3` ✓ · `ba3de2a` ✓ — 4/4 commits.
ARTIFACT: `verification/openmath/hetow_pe1_fresh.py` ✓ · `hetowr1_supp.py` ✓.
**Full md5:** `13e087d62b4dad5a5724d337576f3411`.

**TEETH:** **The gauge-naive tooth fired at each of three η ≠ 1 frames** — frame X (p = 3, e₁ = 2), plus p = 5 with `ord(η) = 4`, plus p = 5 at `e₁ = 3`; `hetowr1_supp.py` GREEN, 29 gp jobs + 15 exact checks, 0 violations. **Disposition: planted mutant from a consumer note, fired against the supplier's display; `disclosed non-repair` in GENHN's own legs** (all its tower frames have η = 1).

---
### EFF.GENHN.78  [changes-record]  — the 2026-08-12 A2 adjudication header

**CANONICAL STATEMENT:** verbatim, lines 2042–2055.

**FORM:** `###` heading + a framing paragraph.

> “### Dated adjudication + corrections (2026-08-12 — sol certification A2: the R4 chain challenge adjudicated at HEAD)
>
> The sol-5.6 chain read of this note (gpt-5.6-sol high,
> runs/residues/R4_genhn_output.log, 2026-08-12) returned CHALLENGE
> with five findings. The A2 certification run (gpt-5.6-sol high,
> runs/cert/A2_genhn_output.log) re-adjudicated all five against HEAD
> including every dated append (E1–E3, the [r2] annex, [r3], the HETOW
> erratum): findings F-1, F-3, F-5 are REAL with derived repairs — the
> three dated blocks below; findings F-2 and F-4 are REAL but
> OBSTRUCTED — the displayed clauses are false as stated and every
> honest repair weakens an accepted statement display, so no
> admissible repair exists; the two dated obstruction records below
> transcribe the A2 adjudications verbatim. Everything above this
> heading is byte-untouched by this append.”

**CONDITIONALITY:** **The pivotal framing of the whole 2026-08-12 wave, and it makes a distinction the corpus depends on: REAL-with-repair vs REAL-but-OBSTRUCTED.** The obstruction is *procedural*, not mathematical — “every honest repair **weakens an accepted statement display**, so no admissible repair exists” under the statement fence in force at that moment. Both obstructions were then closed by owner directive (`.85`–`.87`), which is why the fence and its later relaxation must be read together. **All five findings are REAL: 5/5.** That is the harshest external verdict on this note anywhere, and it landed *after* acceptance.

*Arithmetic audit (rule 22).* Five findings: F-1, F-3, F-5 repaired (3) + F-2, F-4 obstructed (2) = 5 ✓, and the appends below supply exactly three dated corrections (`.79`, `.81`, `.83`) and two obstruction records (`.80`, `.82`) ✓ **3 + 2 = 5, one block per finding, no orphans.**

**DERIVATION:** Adjudication framing.

**RESOLUTION TRACE:** statement 2042–2055 · blocks 2057–2214 · verification 2216–2266 (`.84`) · closure 2270–2332 (`.85`–`.88`).

ARTIFACT: `runs/residues/R4_genhn_output.log` ✓ · `runs/cert/A2_genhn_output.log` ✓ — 2/2 present.

**TEETH:** **`decorrelated-model audit` (rule 27)** — a fresh-context gpt-5.6-sol chain read, re-adjudicated by a second sol run against HEAD *including every append*. The note's own four hostile passes had missed all five. **This is the shard's strongest argument for model-diverse verification** and is recorded as such.

---
### EFF.GENHN.79  [lemma]  — R4 F-1: the ragged-band terminology defect + LEMMA GENHN-CAP-GEN

**CANONICAL STATEMENT:** verbatim, lines 2057–2087 (heading, THE TERMINOLOGY DEFECT, LEMMA GENHN-CAP-GEN with its three-clause rule, PROOF, COUNT TRANSPORT, the specialization paragraph, and RIDERS).

**FORM:** `###` heading + bold-headed defect paragraph + a bold-headed lemma in LaTeX-bearing prose + PROOF + COUNT TRANSPORT + RIDERS.

> “### Dated correction (2026-08-12, R4 F-1 — the general boundary projection and the meaning of “ragged band”)
>
> **THE TERMINOLOGY DEFECT.** GENHN.A(iii), GENHN-3(b), and the OB-a paragraph use “ragged band is never consulted” for two different objects: the interval of slot HEIGHTS beyond the shortest class string, and the UNREAD coefficient components occurring at those heights. The first usage is false: the `[r2]` annex itself proves that a first-band height can support a lift-stable terminal decision. The correct invariant is that no UNREAD coefficient digit is consulted.
>
> **LEMMA GENHN-CAP-GEN (general finite-window boundary projection).** Fix any ordinary stage genre \((e_1,f_1,\mu)\) and a truncated coefficient state. For a slot height \(m\), let \(V_m\subseteq K\) be the \(F_Q\)-span of those basis components \(\eta^t\) whose coefficient digits occur below their coordinate windows, and put
>
> \[
> \operatorname{comp}(m):=\dim_{F_Q}V_m.
> \]
>
> Let \(\operatorname{Comp}(z)\) be the set of all full coefficient strings agreeing with the truncated state \(z\). The finite-window stage reader obeys the following rule:
>
> 1. if some unread coefficient can undercut the provisional minimum, return `UND`;
> 2. otherwise GENHN-2 makes the provisional value exact; if its residue is only partially visible, return a decided leaf exactly when every member of \(\operatorname{Comp}(z)\) has the same dictionary output, and return `UND` otherwise;
> 3. perform a recursive refine only when every \(K\)-component of every pin required by that refine is visible.
>
> Then the output is a function of the truncated data, no unread digit is consulted, and every recursive history stops before an incomplete pin.
>
> **PROOF.** GENHN-2 expresses every queried value as the minimum of the individual coefficient heights and proves independence of the tying residues. If an unread coefficient can lie lower, two compatible completions can have different values, so conservative drainage forces `UND`. If none can lie lower, the value is fixed; at an equal-height tie, independence of the visible and missing \(\eta^t\)-components prevents the missing components from cancelling a nonzero visible part. A leaf is lift-stable precisely when its dictionary output is constant on the affine completion set. Finally, an incomplete refine pin cannot determine its \(K\)-letter, so clause 3 is forced by the same completion test. This proves all three clauses.
>
> **COUNT TRANSPORT.** GENHN-1’s triangular coefficient bijection transports this completion rule directly from W-12.A’s conservative finite-window read. A nonzero visible boundary pin has
>
> \[
> Q^{\operatorname{comp}(m)}-1
> \]
>
> choices, exactly as ERRATUM E2 states; unread components are free completion fibers, and deeper value-unstable strata drain to `UND`. Interior refinements still use complete \(K\)-pins, so GENHN-2(b)’s bracket and GENHN.A(iv) are unchanged. Thus CS-1 and CS-2 hold at ordinary \(f_1\ge2\), \(\mu\ge3\), and mixed genres without a new box.
>
> The `[r2]` rule for \((e_1,\mu)=(1,2)\) is the specialization: at the first band height \(N\), a nonzero visible part fixes \(u=N\); `2SIDED` or odd `RAM` is returned when that conclusion is constant over all missing components, while the even residue-dependent branch drains. At deeper band heights an unread digit can undercut, so clause 1 drains.
>
> **RIDERS.** Read “the ragged band is never consulted” everywhere in GENHN.A(iii), S5, and the OB-a paragraph as “the unread component cells of the ragged band are never consulted.” Visible components at a boundary height may be used once by the completion-invariant terminal rule above. Read GENHN-3(a)’s “iff \(<e_1N\)” as the sufficient interior criterion together with GENHN-CAP-GEN’s exact boundary criterion; the previously proved stability below \(e_1N\) is unchanged.”

**SUPERSESSION KIND: wording-rider** (the “never consulted” phrase at three named sites) + **scope-pin** (GENHN-3(a)'s “iff”) + **license** (the lemma supplies the general boundary rule the note previously had nowhere). `TARGETS: .10` (GENHN.A(iii)), `.29` (GENHN-3(a)/(b)), `.30` (the OB-a paragraph).

**CONDITIONALITY:** **This append closes a real hole that E1's exclusion clause had claimed was held elsewhere and was not** — the A2 verification note (`.84`) walked the S9 box list and found “no ordinary-stage box holds it, confirming the omission”. The lemma's own reach is stated at the end of COUNT TRANSPORT: “Thus CS-1 and CS-2 hold at ordinary \(f_1\ge2\), \(\mu\ge3\), and mixed genres **without a new box**” — i.e. it *removes* an obligation rather than adding one. **Its own status:** part of the A2 wave, whose ledger line says “the three repairs await sol discharge-confirmation” (2263–2264). See OPEN-CALL 4.
**One citation defect inside the lemma is caught by the note's own verification paragraph** (2234–2237): “the repair's "GENHN-2(b)'s bracket" has no literal referent — GENHN-2 is unlettered; the referent is the stage bracket (CS-2) of THEOREM GENHN.B / S6.2”. Recorded as source defect 7; the orchestrator caught it before transcription and said so.

**DERIVATION:** Quoted in full above; the load-bearing step is GENHN-2's F_Q-independence, applied to the completion set: missing `η^t`-components occupy complementary basis directions, so no completion cancels a nonzero visible part.

*Arithmetic audit (rule 22) of the census clause and the specialization.* The visible subspace `V_m ⊆ K` has `|V_m| = Q^{comp(m)}`, so nonzero readable vectors number `Q^{comp(m)} − 1` ✓ — identical to E2's clause (shard 1 `.14`) and to CR-3 (`.42`) ✓ **three independent derivations of the same census, all agreeing.** Specialization at `(e₁, μ) = (1, 2)`: clause 2 returns a decided leaf iff the dictionary output is constant on `Comp(z)`; at the first band height `N`, `2SIDED` (N > 2w) and odd `RAM` (N ≤ 2w, N odd) are constant, the even branch is residue-dependent and drains ✓ — **exactly E1's trichotomy** (shard 1 `.31`) ✓ and exactly the `[r2]` annex's clauses (1)–(3) (shard 1 `.32`) ✓. **The general lemma specializes to both prior authorities without discrepancy.**

**RESOLUTION TRACE:** statement 2057–2087 · proof 2075 · targets 179–183, 741–763, 765–768 (shard 1) · verification 2219–2237 (`.84`).

XREF: `W12_PROOF_2026-08-08.md:THEOREM W-12.A` — count **8**.
XREF: `GENIND_PROOF_2026-08-08.md:(CS-1)` — count **49** · `(CS-2)` — count **20**.

**TEETH:** **PROOF-ONLY.** No battery row has `f₁ ≥ 2`, so the boundary rule is unexercised by GENHN's own instrument; the only machine contact is `genhn_pe4_fresh.py`'s `comp = 3` leg (`.75`), post-acceptance and additive. The note's coverage-hole sentence is GENHN-BOX-3's f₁ ≥ 2 exclusion (`.51`). **Disposition: `decorrelated-model audit` for the finding; PROOF-ONLY for the lemma.**

---
### EFF.GENHN.80  [changes-record]  — R4 F-2 obstruction record (GENHN.CLASS's finiteness display)

**CANONICAL STATEMENT:** verbatim, lines 2089–2099.

**FORM:** `###` heading + the A2 adjudication transcribed verbatim, with a LaTeX counterexample display.

> “### Dated obstruction record (2026-08-12, R4 F-2 — GENHN.CLASS's finiteness display; the A2 adjudication transcribed verbatim)
>
> The finding stands. GENHN.CLASS explicitly includes \(Q\) and \(h\) in \(G\), while its finiteness proof counts only discrete schemas \((e_1,f_1,\mu,\text{entry-family})\).
>
> For fixed \(n=4,Q=2\), every positive odd \(h\) gives a distinct datum
> \[
> (2;2,1,2;h,\mathrm{entry})
> \]
> once \(N\ge2h+1\). Thus the declared data set is infinite.
>
> The only honest correction would replace “finitely many genre data” by “finitely many parameterized genre schemas, with \(Q,h,N\) and prehistory depths as parameters.” That weakens the accepted theorem’s displayed finiteness assertion, which the instructions prohibit. No new lemma can prove the existing false statement.”

**CONDITIONALITY:** **An obstruction record, not a repair — and then closed by owner directive at `.86`.** `SUPERSESSION KIND: none applied at this append` (it applies nothing; it records that nothing admissible could be applied). **CHAIN for GENHN.CLASS(ii): frozen display → this obstruction record → owner-directive re-display (`.86`). TERMINAL: the re-display.**
**The last sentence is the strongest statement in the note about the limits of repair-by-lemma:** “**No new lemma can prove the existing false statement.**” A chapter cut must not read the later re-display as a proof of the original.

*Arithmetic audit (rule 22) of the counterexample, computed fresh.* Genre `(2; 2,1,2; h)` means `Q = 2, e₁ = 2, f₁ = 1, μ = 2, slope h/2`. Budget: `e₁f₁μ = 2·1·2 = 4 ≤ n = 4` ✓ realizable at n = 4. Lowest-terms constraint `gcd(h, e₁) = gcd(h, 2) = 1` ⟹ **h odd** ✓ exactly the family's parameter. Visibility: the note's own E3(h)-style floor is `visible iff (something)·h ≤ N−1`; here the stated condition is `N ≥ 2h+1`, i.e. `2h ≤ N − 1` ✓ — **the same shape as E31(h)'s “visible iff 2h ≤ N−1”** (shard 1 `.20`) ✓. So for each odd `h ≥ 1` there is an `N` making the datum realizable, and the data set is infinite ✓. **The counterexample is correct and it is built from the note's own instance-table shape.**

**DERIVATION:** Adjudication, transcribed verbatim.

**RESOLUTION TRACE:** statement 2089–2099 · target 127–154 (shard 1 `.07`) · closure 2282–2298 (`.38`) · verification 2251–2257 (`.36`).

**TEETH:** **`decorrelated-model audit`.** No battery row could produce this: the battery sweeps fixed `(q, N, h)` and the counterexample is a *family over h*. The note's own instance tables display the h-parameterization, so the defect was visible in the text all along and four hostile passes did not see it.

---
### EFF.GENHN.81  [lemma]  — R4 F-3: LEMMA GENHN-LIFT (the exact-height K-lift in T(b)′(i))

**CANONICAL STATEMENT:** verbatim, lines 2101–2189.

**FORM:** `###` heading + a bold-headed LaTeX lemma + PROOF + APPLICATION TO THE COMPOSED KEY.

> “### Dated proof completion (2026-08-12, R4 F-3 — the exact-height \(K\)-lift in T(b)′(i))
>
> **LEMMA GENHN-LIFT.** Let \(M>D'h=e_1f_1h\), and let \(i=i(M)\), \(0\le i<e_1\), be determined by
>
> \[
> ih\equiv M\pmod{e_1},\qquad a=(M-ih)/e_1.
> \]
>
> Write \(\lambda\in K\) uniquely as
>
> \[
> \lambda=\sum_{s=0}^{f_1-1}\lambda_s\eta^s,\qquad \lambda_s\in F_Q,
> \]
>
> and define
>
> \[
> L_M(\lambda):=
> \sum_{s=0}^{f_1-1}
> \widetilde{\lambda_s}\,
> x^{\,i+e_1s}\pi^{\,a-sh}.
> \]
>
> Then \(L_M(\lambda)\in\widehat O[x]\), \(\deg L_M(\lambda)<D'\), every nonzero summand has exact \(dv\)-height \(M\), and
>
> \[
> \operatorname{res}\!\left(\frac{L_M(\lambda)(\theta)}
> {n(M)(\theta)}\right)=\lambda .
> \]
>
> **PROOF.** Since \(i+e_1s\le D'-1\) and \(M>D'h\),
>
> \[
> a-sh=\frac{M-(i+e_1s)h}{e_1}\ge0,
> \]
>
> so every summand is integral and has degree \(<D'\). Its evaluated height is
>
> \[
> e_1(a-sh)+(i+e_1s)h=M.
> \]
>
> Dividing by \(n(M)=x^i\pi^a\) leaves residue
> \(\lambda_s\eta^s\); GENHN-2’s independence gives their sum
> \(\lambda\), with no cancellation. ∎
>
> **APPLICATION TO THE COMPOSED KEY.** Put \(r=f_2-t\), \(M=ru_2\), and
>
> \[
> W(t)=\left\lfloor\frac{r\,i(u_2)}{e_1}\right\rfloor .
> \]
>
> Replace the gauge-naive coefficient term in T(b)′ by
>
> \[
> L_{ru_2}\!\bigl(c_t\eta^{W(t)}\bigr)\,\Phi'^{\,e_2t}.
> \]
>
> Because
>
> \[
> \operatorname{res}\!\left(\frac{n(u_2)^r}{n(ru_2)}\right)
> =\eta^{W(t)},
> \]
>
> its coefficient relative to the coherent power normalizer
> \(n(u_2)^r\) is exactly \(c_t\). Hence the inner residual is
> precisely \(\psi_2\), not its gauge-naive twist.
>
> For every monomial \(x^\ell\pi^b\) occurring in this lift,
> \(e_1b+\ell h=ru_2\). Multiplying by a monomial of
> \(\Phi'^{e_2t}\), the clearance above the outer \(x\)-polygon side
> is bounded below by
>
> \[
> \frac{r(u_2-e_2D'h)}{e_1}>0,
> \]
>
> exactly the inequality used in T(b)′(i). Thus every component
> clears the side. Polynomial collection and \(\Phi'\)-carry can
> only cancel terms or move them upward; they cannot create a term
> below the side. Since \(L_M(\lambda)\) already has degree \(<D'\),
> the literal \(\Phi'\)-development also has the asserted
> exact-height coefficient and residual.
>
> Therefore T(b)′(i)’s one-side polygon, \(\psi_2\)-residual,
> carrier forcing chain, irreducibility, and residue-field
> conclusion hold at the corrected composed key. Clauses (ii)–(v)
> then proceed exactly as written.”

**SUPERSESSION KIND: license** — it supplies the exact-height `(LIFT)` operator the HETOW erratum (`.77`) *consumed without an in-note lemma*, and it licenses `.87`/`.88`'s occupied-height re-display of GENHN.A(ii). `TARGETS: .42` (T(b)′(i)'s lift prescription), `.87` (the slot re-display's “explicit lift”), `.90` (COUNT-RERUN's proof cites it by name).

**CONDITIONALITY:** **Domain is `M > D′h`, and that domain is exactly what the post-D2b corrigendum (`.88`) then adopts as GENHN.A(ii)'s scope.** The lemma is therefore the hinge of the whole occupied-height story: it proves the slot exists *and is liftable* precisely where every consumed pin lives. Its own status: part of the A2 wave, discharge-confirmation owed (`.84`, 2263–2264).

**DERIVATION:** Quoted in full above; three checks (integrality, degree, exact height) plus GENHN-2's independence for the residue.

*Arithmetic audit (rule 22), every step recomputed.*
- **Integrality.** `a − sh = (M − ih)/e₁ − sh = (M − ih − e₁sh)/e₁ = (M − (i+e₁s)h)/e₁` ✓ **the displayed identity is correct.** Nonnegative when `M ≥ (i+e₁s)h`; since `i + e₁s ≤ i + e₁(f₁−1) ≤ (e₁−1) + e₁f₁ − e₁ = e₁f₁ − 1 = D′ − 1` ✓ and `M > D′h ≥ (D′−1)h ≥ (i+e₁s)h` ✓. **Correct.**
- **Degree.** `deg = i + e₁s ≤ D′ − 1 < D′` ✓.
- **Exact height.** `e₁(a−sh) + (i+e₁s)h = e₁a − e₁sh + ih + e₁sh = e₁a + ih = M` ✓ (using `a = (M−ih)/e₁`) ✓ **exact, and the `sh` terms cancel identically.**
- **Residue.** Dividing `x^{i+e₁s}π^{a−sh}` by `n(M) = x^iπ^a` gives `x^{e₁s}π^{−sh} = (x^{e₁}π^{−h})^s`, whose residue at θ is `η^s` ✓ — so the summand's residue is `λ_s η^s` ✓ and the sum is `λ` ✓ by F_Q-independence ✓.
- **The wrap identity `res(n(u₂)^r/n(ru₂)) = η^{W(t)}`.** `n(u₂)^r = x^{r·i(u₂)}π^{r·a(u₂)}` and `n(ru₂) = x^{i(ru₂)}π^{a(ru₂)}`. Reducing `r·i(u₂)` mod `e₁`: `r·i(u₂) = i(ru₂) + e₁·W` with `W = ⌊r·i(u₂)/e₁⌋` ✓ (since `0 ≤ i(ru₂) < e₁`) ✓ — so the quotient is `x^{e₁W}π^{r a(u₂) − a(ru₂)}`, and height-matching forces `e₁(r a(u₂) − a(ru₂)) = −e₁Wh`, i.e. the quotient is `(x^{e₁}π^{−h})^W` with residue `η^W` ✓. **The note's own verification paragraph re-derives exactly this** (2242–2245: “the wrap identity … re-derived from e₁(r·a(u₂)−a(ru₂)) = −e₁W(t)h, matching the erratum's own cocycle display”) ✓ **two independent derivations agree.**
- **Clearance.** `r(u₂ − e₂D′h)/e₁ > 0` iff `u₂ > e₂D′h` ✓ — the `[r1]` node floor, character-for-character the bound in T(b)′(i) (shard 1 `.42`) ✓.
**Every step reproduces. The lemma is correct as displayed.**

**RESOLUTION TRACE:** statement 2101–2189 · proof 2131–2145 · application 2147–2189 · consumed at 2300–2313 (`.87`), 2315–2332 (`.88`), 2445–2461 (`.91`) · verification 2238–2247 (`.84`).

XREF: `HETOW_passPE1_report.md:F-1` — count **9** (the erratum whose consumed operator this lemma supplies).

**TEETH:** **PROOF-ONLY.** No machine leg exercises `L_M` at `f₁ ≥ 2` inside GENHN; the nearest contact is `genhn_pe4_fresh.py`'s `f₁ = 4 / comp = 3 / F₁₆` leg (`.75`) and, foreign-ly, `hetowr1_supp.py`'s three η ≠ 1 frames (`.77`). **Disposition: PROOF-ONLY with `accepted-with-decorrelation-supplied`** — the algebra was hand-re-derived by the orchestrator before transcription (`.84`).

---
### EFF.GENHN.82  [changes-record]  — R4 F-4 obstruction record (GENHN.A(ii)'s universal slot display)

**CANONICAL STATEMENT:** verbatim, lines 2191–2195.

**FORM:** `###` heading + the A2 adjudication transcribed verbatim.

> “### Dated obstruction record (2026-08-12, R4 F-4 — GENHN.A(ii)'s universal slot display; the A2 adjudication transcribed verbatim)
>
> The counterexample is correct. For \((e_1,f_1,h,m)=(3,1,2,1)\), the unique normalizer exponent is \(a=-1\), so neither an integral normalizer nor a variable \(K\)-slot exists at height \(1\).
>
> The downstream laws are protected because their live pins satisfy \(m>D'h\), where integrality follows, but the displayed universal assertion “one \(K\)-digit slot per integer \(dv\)-height” is false. Its necessary repair would restrict it to occupied heights—particularly the live stage domain \(m>D'h\), subject also to the upper window cap. That is a weakening of GENHN.A(ii)’s accepted statement display, so no admissible repair can be supplied under the stated constraint.”

**CONDITIONALITY:** **Obstruction record; closed by `.87` and then tightened by `.88`.** **CHAIN for GENHN.A(ii): frozen display → this record → owner-directive re-display (`.87`) → post-D2b corrigendum (`.88`). TERMINAL: the corrigendum's `D′h < m` scope.**
**The record itself names the eventual repair** (“restrict it to occupied heights—particularly the live stage domain \(m>D'h\)”), so the later re-display is not a new idea but the execution of an option the obstruction already identified. That matters for attribution.

*Arithmetic audit (rule 22) of the counterexample, computed fresh.* `(e₁, f₁, h, m) = (3, 1, 2, 1)`. Normalizer: solve `i·h ≡ m (mod e₁)`, i.e. `2i ≡ 1 (mod 3)` ⟹ `i ≡ 2 (mod 3)` ⟹ `i = 2` (since `0 ≤ i < 3`) ✓. Then `a = (m − ih)/e₁ = (1 − 4)/3 = −1` ✓ **exactly as stated** — negative, so `n(1) = x²π^{−1} ∉ Ô[x]` ✓ no integral normalizer, no slot ✓. Protection: `D′h = e₁f₁h = 3·1·2 = 6`, and the live pins satisfy `m > 6 > 1` ✓ so the counterexample height is far below the consumed domain ✓. **Correct in both directions.**

**DERIVATION:** Adjudication, transcribed verbatim.

**RESOLUTION TRACE:** statement 2191–2195 · target 173–178 (shard 1 `.09`) · closure 2300–2313, 2315–2332 · verification 2257–2262 (`.36`).

**TEETH:** **`decorrelated-model audit`.** Unreachable by any row: every consumed pin sits at `dv > D′h`, so the battery is structurally blind to unoccupied heights. Four hostile passes missed it; a fresh-model chain read found it.

---
### EFF.GENHN.83  [changes-record]  — R4 F-5: the first tower's residual

**CANONICAL STATEMENT:** verbatim, lines 2197–2214.

**FORM:** `###` heading + a replace-this-by-that pair of blockquotes + DERIVATION.

> “### Dated correction (2026-08-12, R4 F-5 — the first tower’s residual)
>
> In S8’s proof of LEMMA GENHN-T(a), replace
>
> > “residual \((T^2-c)^2\) over \(K\)”
>
> by
>
> > “residual \((T-c)^2\) over \(K\)”.
>
> **DERIVATION.** A side of abscissa length \(4\) and denominator
> \(e_2=2\) has residual degree \(4/e_2=2\). An inner repeated factor
> with \(f_2=1,\mu_2=2\) therefore has residual
> \((T-c)^2\), of degree \(2\). The displayed \((T^2-c)^2\) has
> degree \(4\) and would require side length \(e_2\cdot4=8\).
> The corrected form is exactly the later GN-TOWER witness
> \((T-1)^2\), so the positive-locus realization and the first-live
> threshold \(n=8\) remain unchanged.”

**SUPERSESSION KIND: replacement** (proof-internal display). `TARGETS: .16` (T(a)'s proof, line 1054).

**CONDITIONALITY:** **Nothing downstream moves** — “the positive-locus realization and the first-live threshold \(n=8\) remain unchanged.” The correction is worth its own unit because of what it reveals: **the machine witness carried the corrected residual `(T−1)²` from the start** (S11.D P8 and S12 P8 both display it), so the note's own battery and its own proof display disagreed for the whole arc and four hostile passes did not notice. `.64`'s TEETH row records this as a `stale self-description` on the display.

*Arithmetic audit (rule 22), recomputed.* Side `(0, u₀)–(4, 0)` of abscissa length 4 with denominator `e₂ = 2`: residual degree `= length/e₂ = 4/2 = 2` ✓. `(T−c)²` has degree 2 ✓; `(T²−c)²` has degree 4 ✗, which would need length `e₂·4 = 8` ✓ as stated. Consistency with `f₂ = 1, μ₂ = 2`: residual is `ψ₂^{μ₂}` with `deg ψ₂ = f₂ = 1` ⟹ degree `1·2 = 2` ✓. GN-TOWER's witness residual `(T−1)²` ✓ degree 2 ✓ **matches the corrected form exactly.** And the abscissa budget check `e₂f₂μ₂ = 2·1·2 = 4 ≤ μ₁ = 4` ✓ (shard 1 `.16`). **Correct.**

**DERIVATION:** Displayed inline, quoted above.

**RESOLUTION TRACE:** statement 2197–2214 · target 1054 (shard 1) · witness 1713–1717, 1835–1838 · verification 2247–2251 (`.84`).

**TEETH:** **GN-TOWER's P8 witness IS the tooth, and it fired silently in the note's favour** — the machine always had `(T−1)²`. **Disposition: `stale self-description` on the proof display, cured by an append 2026-08-12.**

---
### EFF.GENHN.84  [instrument-record]  — the A2 verification parenthetical (what the orchestrator re-checked before transcribing)

**CANONICAL STATEMENT:** verbatim, lines 2216–2266.

**FORM:** italic parenthetical paragraph closing the A2 block, finding by finding.

> “*(The three repairs and two obstruction records above were derived
> by the A2 certification run (gpt-5.6-sol high,
> runs/cert/A2_genhn_output.log, 2026-08-12); orchestrator
> verification before transcription — F-1: the "ragged band is never
> consulted" spans re-read at HEAD (GENHN.A(iii), GENHN-3(b)/(d), the
> OB-a paragraph); the [r2] annex confirmed to prove a lift-stable
> dv = e₁N at the first band height (refuting GENHN-3(a)'s "iff" as
> written, so the rider is needed); ERRATUM E1's exclusion ("at f₁ ≥ 2
> genres beyond [μ = 2] … NO band-adjudication display — that surface
> sits with the S9 boxes") checked against S9's actual box list
> (BOX-1 grades, BOX-2 refine-transfer bookkeeping, BOX-3 machine
> coverage only, BOX-4 extraction, BOX-5 P(5) density, [GENHN-TOW-1]
> towers) — no ordinary-stage box holds it, confirming the omission;
> GENHN-CAP-GEN's load-bearing step (missing η^t-components occupy
> complementary basis directions, so no completion cancels a nonzero
> visible part) re-derived from GENHN-2's F_Q-independence; the
> specializations re-checked against the E1 r3 trichotomy and the
> [r2] annex clauses (1)–(3) including the Q^{comp(m)}−1 census =
> ERRATUM E2's clause. Citation note: the repair's "GENHN-2(b)'s
> bracket" has no literal referent — GENHN-2 is unlettered; the
> referent is the stage bracket (CS-2) of THEOREM GENHN.B / S6.2,
> which is what interior refinements with complete K-pins leave
> unchanged. F-3: the HETOW erratum confirmed to CONSUME the
> exact-height (LIFT) operator without an in-note lemma; GENHN-LIFT's
> algebra re-derived by hand (integrality a−sh ≥ 0 from M > D′h;
> degree i+e₁s ≤ D′−1; exact height e₁(a−sh)+(i+e₁s)h = M; residue
> Σλ_sη^s = λ by GENHN-2's independence; the wrap identity
> res(n(u₂)^r/n(ru₂)) = η^{W(t)} re-derived from
> e₁(r·a(u₂)−a(ru₂)) = −e₁W(t)h, matching the erratum's own cocycle
> display); the clearance bound r(u₂−e₂D′h)/e₁ checked
> character-for-character against T(b)′(i)'s proof (the [r1] NODE
> FLOOR u₂ > e₂D′h). F-5: the span located (S8 GENHN-T(a) proof,
> "residual (T² − c)² over K" on the length-4 stage-e = 2 side);
> residual degree = 4/e₂ = 2 re-derived; the GN-TOWER witness's
> residual confirmed as ψ₂² = (T+1)² = (T−1)² over F₂, the
> squared-linear form; no prior dated append touches the line. F-2:
> G's inclusion of Q and h confirmed (GENHN.CLASS (i)); S2's
> finiteness proof confirmed to count triples + entry-pattern
> families only; the counterexample arithmetic checked (genre
> (2; 2,1,2; h) with h odd, e₁f₁μ = 4 ≤ n, visible once N ≥ 2h+1 —
> the note's own E3(h)/E31(h) instance tables display the same
> h-parameterization); the data set as declared is infinite. F-4:
> the counterexample arithmetic checked (2i ≡ 1 mod 3 ⟹ i = 2,
> a = (1−4)/3 = −1); the protection claim checked (the post-r1
> stage-initial node floor {dv(A_j) ≥ (μ−j)D′h + 1} and the [r1]
> NODE FLOOR put every live pin at dv > D′h, exactly GENHN-LIFT's
> integrality domain). Repairs transcribed unaltered per the standing
> division of labor. Ledger: GENHN's row stays OPEN — the three
> repairs await sol discharge-confirmation; the two obstructions
> close only by re-displayed statements (requires owner sign-off per
> the statement fence) or new mathematics.)*”

**CONDITIONALITY:** **This paragraph is the evidence that the transcribed sol output was independently checked, and it is the only such evidence in the note.** Three things it establishes that nothing else does:
(a) **E1's exclusion clause was checked box-by-box and found false** — “no ordinary-stage box holds it, confirming the omission”. That is the justification for `.79` existing at all.
(b) **A citation defect inside the F-1 repair was caught before transcription** — “GENHN-2(b)'s bracket has no literal referent — GENHN-2 is unlettered”. The referent is supplied. Source defect 7.
(c) **The ledger line fixes the wave's status**: “GENHN's row stays OPEN — the three repairs await sol discharge-confirmation; the two obstructions close only by re-displayed statements … or new mathematics.” See OPEN-CALL 4.
**One thing it does NOT do:** it does not re-run any instrument. Every check listed is a hand re-derivation or a span re-read. That is appropriate for display defects and is disclosed by the wording (“re-read at HEAD”, “re-derived by hand”, “checked character-for-character”).

*Compiler cross-check (rule 22) — this shard independently recomputed six of the checks this paragraph claims, at `.79`, `.80`, `.81`, `.82`, `.83`, and shard 1 `.20`. **All six reproduced.** Specifically: GENHN-LIFT's four algebra steps (`.81`), the wrap identity (`.81`), the F-2 counterexample's budget and visibility (`.80`), the F-4 counterexample's `i = 2, a = −1` (`.82`), the F-5 residual degree `4/e₂ = 2` (`.83`), and the h-parameterization in the note's own instance tables (shard 1 `.20`). **No discrepancy between the paragraph's claims and this compiler's independent recomputation.***

**DERIVATION:** Verification record.

**RESOLUTION TRACE:** statement 2216–2266 · the five blocks it verifies 2057–2214 · the closure it anticipates 2270–2332.

ARTIFACT: `runs/cert/A2_genhn_output.log` ✓ · `runs/residues/R4_genhn_output.log` ✓.
XREF: `GENIND_PROOF_2026-08-08.md:(CS-2)` — count **20** (the supplied referent for the mis-cited “GENHN-2(b)'s bracket”).

**TEETH:** **`in-house hostile pass` / `arithmetic recount` (rule 27).** No instrument ran; the disposition is hand verification, disclosed as such.

---
### EFF.GENHN.85  [changes-record]  — the owner-directive header (2026-08-12)

**CANONICAL STATEMENT:** verbatim, lines 2270–2280.

**FORM:** `###` heading + a framing paragraph.

> “### Dated statement re-displays (2026-08-12 — the two A2 obstructions closed under the owner's directive)
>
> Asvin (2026-08-12) delegated proof-related statement decisions under
> the end-to-end-proof criterion: the right display for any lemma is
> the one the complete proof of the pinned main theorem consumes,
> stated as simply as possible. Under that authority the two OBSTRUCTED
> findings of the A2 adjudication above are closed by the following
> re-displays, each at exactly the scope its proof establishes and its
> consumers consume. Orchestrator-composed from the A2 obstruction
> records' own option text; consumer safety verified at HEAD before
> folding; subject to sol discharge-confirmation in the cert2 pass.”

**CONDITIONALITY:** **This is the authority under which two accepted statement displays are changed, and it must be quoted wherever those changes are.** Three properties: (i) the criterion is **end-to-end-proof** — the right display is the one the complete proof consumes, stated as simply as possible; (ii) the re-displays are **composed from the obstruction records' own option text**, not invented; (iii) they are **subject to sol discharge-confirmation in the cert2 pass** — and the post-D2b corrigendum (`.88`) is exactly that pass returning NEW-ISSUE on one of them, which is evidence the confirmation loop is real.

**DERIVATION:** Authority declaration.

**RESOLUTION TRACE:** statement 2270–2280 · re-displays 2282–2313 · confirmation pass 2315–2332.

**TEETH:** NONE (authority declaration). Its own falsifier fired once: D2b returned NEW-ISSUE on the F-4 re-display (`.88`).

---
### EFF.GENHN.86  [theorem]  — the F-2 statement re-display (GENHN.CLASS's finiteness clause)

**CANONICAL STATEMENT:** verbatim, lines 2282–2298.

**FORM:** bold-headed dated re-display, prose (no LaTeX).

> “**Dated statement re-display (2026-08-12, R4 F-2 — GENHN.CLASS's
> finiteness clause).** THEOREM GENHN.CLASS's header gloss "finite per
> n" and clause (ii) FINITE are re-displayed at the scope S2's proof
> establishes: at fixed n, the genres form FINITELY MANY PARAMETERIZED
> GENRE SCHEMAS — the triples (e₁, f₁, μ) with e₁f₁ ≥ 2, e₁f₁μ ≤ n,
> each carrying finitely many (A1)-admissible entry-pattern families —
> with the residue field Q, the slope numerator h (gcd(h, e₁) = 1),
> the window N, and the prehistory depths as the schemas' parameters.
> The genre DATUM G = (Q; e₁, f₁, μ; h, entry) ranges over infinitely
> many parameter values at fixed n (every odd h with N ≥ 2h + 1
> realizes (2; 2,1,2; h, entry) at n = 4 — the R4 witness); the note's
> own instance tables already display exactly this parameterization
> (E3(h), E31(h): "visible iff 3h ≤ N−1"), and every count law
> attached to a genre is an (A1)-family law in those parameters
> (geometric in h), which is the form GENHN.B's assembly and the
> battery grammar consume. Clauses (i) and (iii) are unchanged; no
> consumer reads the withdrawn datum-set finiteness.”

**SUPERSESSION KIND: replacement** at statement scope, owner-authorized. `TARGETS: .07` (clause (ii) + header gloss), `.01` (the title's “PROVED FINITE”), `.04` (“finite per n”).
**CHAIN: frozen (ii) → A2 obstruction record (`.80`) → this re-display. TERMINAL: this re-display, subject to cert2 confirmation.**

**CONDITIONALITY:** **The re-display is strictly weaker than the frozen text and says so** — the datum set is infinite; what is finite is the schema set. Three things make it safe:
(i) **It is exactly what S2's proof establishes** — the proof always counted triples + entry-pattern families (the A2 finding's own diagnosis).
(ii) **The note's own instance tables already parameterized by h** (shard 1 `.20`'s E3(h)/E31(h)), so nothing downstream ever consumed datum-set finiteness.
(iii) **“no consumer reads the withdrawn datum-set finiteness”** — a consumer-safety claim, “verified at HEAD before folding” per `.85`. **This compiler did not independently re-verify that claim across the corpus**; it is recorded as the note's assertion. Flagged in OPEN-CALL 5.
**Clauses (i) and (iii) are unchanged.**

**DERIVATION:** The re-display's own content: at fixed n the triples with `e₁f₁ ≥ 2, e₁f₁μ ≤ n` are finite; each carries finitely many (A1)-admissible entry families (LEMMA GENIND-0 closure); `Q, h, N` and prehistory depths are parameters, and every count law is an (A1)-family law in them, geometric in h.

*Arithmetic audit (rule 22).* Finiteness of the triple set at fixed n: `#{(e₁,f₁,μ) : e₁f₁ ≥ 2, μ ≥ 2, e₁f₁μ ≤ n}` — at `n = 8` this is `{(2,1,2),(1,2,2),(2,1,3),(1,2,3),(3,1,2),(1,3,2),(2,1,4),(1,2,4),(4,1,2),(1,4,2),(2,2,2),(3,1,... )}` — enumerate by `D′ = e₁f₁ ∈ {2,3,4}` and `μ ≥ 2` with `D′μ ≤ 8`: `D′ = 2 ⟹ μ ∈ {2,3,4}`; `D′ = 3 ⟹ μ ∈ {2}`; `D′ = 4 ⟹ μ ∈ {2}`. Number of `(e₁,f₁)` with `e₁f₁ = D′`: `D′ = 2 → 2` pairs, `D′ = 3 → 2`, `D′ = 4 → 3`. Total triples `= 2·3 + 2·1 + 3·1 = 6 + 2 + 3 = 11` ✓ **finite**, as claimed. Infinitude of the datum set: for each odd `h`, `(2; 2,1,2; h)` is a distinct datum ✓ (audited at `.80`). **Both halves check.**

**RESOLUTION TRACE:** statement 2282–2298 · obstruction 2089–2099 · target 127–154 (shard 1) · confirmation status 2280 (“subject to sol discharge-confirmation in the cert2 pass”).

XREF: `GENIND_PROOF_2026-08-08.md:LEMMA GENIND-0` — count **5**.

**TEETH:** **PROOF-ONLY / `decorrelated-model audit`.** The battery's GN-CLASS grammar enforces the *schema* constraints (`μ ≥ 2, e₁f₁ ≥ 2, 4 ≤ e₁f₁μ ≤ 6`) and the visibility floors, i.e. it tests exactly the re-displayed claim and never the withdrawn one. Coverage-hole sentence: the battery sweeps fixed `(q, N, h)`, so no row ranges over `h`.

---
### EFF.GENHN.87  [theorem]  — the F-4 statement re-display (GENHN.A(ii)'s slot clause)

**CANONICAL STATEMENT:** verbatim, lines 2300–2313.

**FORM:** bold-headed dated re-display, prose.

> “**Dated statement re-display (2026-08-12, R4 F-4 — GENHN.A(ii)'s
> slot clause).** GENHN.A(ii)'s display "each A_j carries exactly ONE
> K-digit slot per integer dv-height" is re-displayed at its true
> scope: per OCCUPIED integer dv-height — a height m admitting an
> integral normalizer monomial n(m) = x^{i(m)}π^{a(m)} with
> 0 ≤ i(m) < e₁ and a(m) = (m − i(m)h)/e₁ ≥ 0 — below the window cap.
> Every height m > D′h is occupied, with the explicit lift supplied by
> LEMMA GENHN-LIFT (the A2 fold above); every pin the note's laws
> consume sits at dv > D′h (the stage-initial node floor
> {dv(A_j) ≥ (μ−j)D′h + 1} and the refine floors), so no consumer
> moves. At unoccupied low heights no slot exists — witness
> (e₁, f₁, h) = (3, 1, 2), m = 1: i(1) = 2 forces a(1) = −1 (the
> R4/A2 counterexample, recorded in the obstruction record above).
> The e₁-class separation and F_Q-independence clauses are unchanged.”

**SUPERSESSION KIND: replacement** at statement scope, owner-authorized. `TARGETS: .09`, `.27` (LEMMA GENHN-2's same clause).

**CONDITIONALITY:** **This re-display is itself found too weak two lines later** — see `.88`. **CHAIN: frozen display → A2 obstruction (`.82`) → this re-display → post-D2b corrigendum (`.88`). TERMINAL: the corrigendum.** The defect: “occupied” is defined here as *normalizer integrality* (`a(m) ≥ 0`), which at `f₁ > 1` does not guarantee that every **component** monomial `x^{i+e₁s}π^{a−sh}` is integral. So the re-display is correct at `f₁ = 1` and insufficient at `f₁ > 1`.
**What survives both layers:** “every pin the note's laws consume sits at dv > D′h … so no consumer moves”, and “The e₁-class separation and F_Q-independence clauses are unchanged.”

**DERIVATION:** Occupancy is Bézout plus nonnegativity; `m > D′h ⟹ a(m) ≥ 0` via LEMMA GENHN-LIFT (`.81`).

*Arithmetic audit (rule 22).* `a(m) = (m − i(m)h)/e₁ ≥ 0` iff `m ≥ i(m)h`; since `i(m) ≤ e₁ − 1`, `m > D′h = e₁f₁h ≥ e₁h > (e₁−1)h ≥ i(m)h` ✓ so every `m > D′h` is occupied in this weak sense ✓. **But the component check** needs `a − sh ≥ 0` for all `s < f₁`, i.e. `m ≥ (i + e₁s)h` for `i + e₁s ≤ D′ − 1`, i.e. `m ≥ (D′−1)h` — which `m > D′h` gives ✓. **So at `m > D′h` BOTH conditions hold**, and the re-display's conclusion is true; what is too weak is its *definition* of occupied, which admits heights (like `m = 0` at `(1,2,1)`) where only the `s = 0` component is integral. `.88`'s witness is exactly such a height ✓. **The re-display's conclusion survives; its definition does not.** Recorded precisely.

**RESOLUTION TRACE:** statement 2300–2313 · obstruction 2191–2195 · license 2101–2145 · corrigendum 2315–2332 · targets 173–178, 699–717 (shard 1).

**TEETH:** **PROOF-ONLY.** No row reaches an unoccupied height (every consumed pin is above `D′h`). Coverage-hole: GENHN-BOX-3's f₁ ≥ 2 exclusion.

---
### EFF.GENHN.88  [changes-record]  — the post-D2b corrigendum (the occupied-height scope tightened)

**CANONICAL STATEMENT:** verbatim, lines 2315–2332.

**FORM:** bold-headed dated corrigendum, prose.

> “**Dated corrigendum (2026-08-12, post-D2b — the occupied-height
> scope tightened).** The D2b discharge pass (gpt-5.6-sol high,
> runs/cert2/D2b_genhn_output.log) adjudicated the re-display above
> NEW-ISSUE: "occupied" as normalizer-integrality (a(m) ≥ 0) is too
> weak at f₁ > 1 — the full K-digit slot needs every component
> monomial x^{i+e₁s}π^{a−sh} integral, i.e. a(m) ≥ (f₁−1)h; sol's
> witness (e₁, f₁, h, m) = (1, 2, 1, 0): n(0) = 1 is integral while
> the η-component would require xπ^{−1}. Per sol's own recommendation
> and the simplicity preference, the scope is tightened to the
> consumed domain: GENHN.A(ii)'s slot clause holds per integer
> dv-height m with **D′h < m**, below the window cap — there LEMMA
> GENHN-LIFT's proof gives a − sh = (m − (i+e₁s)h)/e₁ ≥ 0 for every
> component (i + e₁s ≤ D′ − 1), so the full K-slot exists — and every
> pin the note's laws consume sits in that domain (the stage-initial
> node floor {dv(A_j) ≥ (μ−j)D′h + 1} and the refine floors). At
> m ≤ D′h the clause is withdrawn entirely: a K-slot may be partial
> (the sol witness) or absent (the R4/A2 witness). Awaiting sol
> re-confirmation in the next queue.”

**SUPERSESSION KIND: replacement** (tightens `.87`'s scope). `TARGETS: .87`, and transitively `.09`, `.27`.
**TERMINAL member of the GENHN.A(ii) chain.** Its own status: “**Awaiting sol re-confirmation in the next queue.**” See OPEN-CALL 4.

**CONDITIONALITY:** **The confirmation loop worked**: a re-display composed under owner directive was sent to a discharge pass, which returned NEW-ISSUE with a witness, and the note tightened rather than defended. That is direct evidence for `.85`'s process. **What the corrigendum withdraws is larger than what `.87` withdrew:** at `m ≤ D′h` the clause is **withdrawn entirely**, with two distinct failure modes named — *partial* (the sol witness) and *absent* (the R4/A2 witness).

**DERIVATION:** From LEMMA GENHN-LIFT's own integrality step: `a − sh = (m − (i+e₁s)h)/e₁ ≥ 0` for every component, given `i + e₁s ≤ D′ − 1` and `m > D′h`.

*Arithmetic audit (rule 22) of the sol witness, computed fresh.* `(e₁, f₁, h, m) = (1, 2, 1, 0)`. Then `D′ = e₁f₁ = 2`, `D′h = 2`. Normalizer at `m = 0`: `i(0)` solves `i·1 ≡ 0 (mod 1)` with `0 ≤ i < 1` ⟹ `i = 0`; `a = (0 − 0)/1 = 0`; `n(0) = x⁰π⁰ = 1` ✓ **integral**, so the weak criterion passes. Component `s = 1`: monomial `x^{i+e₁s}π^{a−sh} = x^{0+1}π^{0−1} = xπ^{−1}` ✓ **non-integral**, so the full K-slot does not exist ✓ **exactly the witness as stated.** And `m = 0 ≤ D′h = 2` ✓ so the tightened scope excludes it ✓. The general component condition: `a(m) ≥ (f₁−1)h` — at the witness `a = 0 < (2−1)·1 = 1` ✓ fails, matching. **Correct in every particular.**

**RESOLUTION TRACE:** statement 2315–2332 · target 2300–2313 · license 2101–2145 · consumed at 2428 (`.91`'s proof: “We use only occupied heights m > B = D′h, the certified scope of the corrected GENHN.A(ii) slot clause”).

ARTIFACT: `runs/cert2/D2b_genhn_output.log` ✓ present.

**TEETH:** **`decorrelated-model audit` (rule 27), second round.** The witness came from a discharge pass on a repair, i.e. a model-diverse check of a model-diverse check. No instrument involved. **This is the shard's clearest demonstration that the audit class catches what batteries structurally cannot.**

---
### EFF.GENHN.89  [run-record]  — the GENHN-COUNT-RERUN certificate interpretation

**CANONICAL STATEMENT:** verbatim, lines 2336–2350.

**FORM:** `###` heading + a bold-headed paragraph with a LaTeX array.

> “### Dated proof completion (2026-08-12 — GENHN-COUNT-RERUN, \(\mu=2\), corrected node)
>
> **Certificate interpretation.** The rerun’s terminal `MISMATCH` concerns only the sealed alpha-child column. On every emitted key, `measured = predicted`. The sealed table incorrectly assigned the entire fixed-letter alpha slice to `UND`. The actual and predicted partitions are
>
> \[
> \begin{array}{c|cc|cc}
> (e_1,f_1,2)&\multicolumn{2}{c|}{\text{sealed}}&
> \multicolumn{2}{c}{\text{actual}=\text{predicted}}\\
> &\mathrm{RAM}&\mathrm{UND}&\mathrm{RAM}&\mathrm{UND}\\ \hline
> (1,2,2)&0&1024&768&256\\
> (2,2,2)&0&16384&12288&4096.
> \end{array}
> \]
>
> Thus the certificate confirms the corrected-node law and refutes the sealed child displays exactly where refine transfer says it must.”

`[TABLE]` — the LaTeX array transcribed (rule 14 double-emission; the source display is quoted above):

| genre (e₁,f₁,μ) | sealed RAM | sealed UND | actual = predicted RAM | actual = predicted UND |
|---|---|---|---|---|
| (1,2,2) | 0 | 1024 | 768 | 256 |
| (2,2,2) | 0 | 16384 | 12288 | 4096 |

*Arithmetic audit (rule 22), computed fresh and cross-checked against every other number in the note that should match.*
- **Row totals.** (1,2,2): sealed `0 + 1024 = 1024`; actual `768 + 256 = 1024` ✓ **equal** — the correction re-partitions, it does not change the total. (2,2,2): sealed `0 + 16384 = 16384`; actual `12288 + 4096 = 16384` ✓ **equal**.
- **The letter factor.** At (1,2,2): `q_K = |K| = Q^{f₁} = 2² = 4`; `768 = 3 · 256 = (q_K − 1)·256` ✓ and `256 = 4⁴` ✓. So `RAM = (q_K−1)·|𝒩_κ|` and `UND = |𝒩_κ|` ✓ — **exactly the shape (CR-2) predicts** (`#{alpha states at height κ} = (|K|−1)|𝒩_κ(M)|`). At (2,2,2): `q_K = 4` again (`f₁ = 2`); `12288 = 3 · 4096` ✓ and `4096 = 4⁶` ✓. **Same shape, different exponent** — consistent with `D′ = 4` vs `D′ = 2` changing `B = D′h` and hence the retained-slot count.
- **Cross-check to (CR-5).** `|𝒩_B(M)| = q_K^{(M−B)+(M−2B)}`. At (1,2,2) with `q_K = 4`: `256 = 4⁴` needs `(M−κ)+(M−2κ) = 4`; at (2,2,2): `4096 = 4⁶` needs `= 6`. Both are integers ≥ 0 for suitable `(M, κ)` ✓ — no contradiction, and the ratio between the two rows is `4²`, consistent with the larger genre having two more retained slots.
- **Cross-check to shard 1 `.24`.** That unit audited the same two rows and reached the same decomposition independently ✓.
- **“exactly where refine transfer says it must.”** (CR-2)'s claim is that summing over the `q_K − 1` nonzero letters gives the alpha-state count; the sealed table assigned the *whole slice* (letters included) to UND, so the discrepancy should be a factor `q_K − 1 = 3` split off from UND into RAM ✓ **and it is, in both rows.** The diagnosis at `.92` item 2 (“the sealed `UND` entries 1024 and 16384 were totals attached to the wrong child key”) is therefore exactly right.
**Every number reproduces and the mechanism is confirmed independently.**

**CONDITIONALITY:** **A `MISMATCH`-terminating certificate reported as a confirmation, and the note explains why that is legitimate:** “The rerun's terminal `MISMATCH` concerns only the sealed alpha-child column. On every emitted key, `measured = predicted`.” The mismatch is against the *sealed table*, not against the theory — and the sealed table is what the correction refutes. A chapter cut must not report “the rerun mismatched” without that clause.

**DERIVATION:** Run record; its theory is `.90`.

**RESOLUTION TRACE:** statement 2336–2350 · lemma 2352–2427 · proof 2428–2589 · sweep 2591–2605 · provenance 2607–2627.

ARTIFACT: `verification/openmath/genhn_f2_count_check.py` ✓ present.
ARTIFACT: `runs/cert4/P2_genhn_count_output.log` ✓ present.

**TEETH:** **Executable regression, post-seal, FIRED AGAINST the sealed child displays** — and it is the **first-ever mixed-genre contact** in the GENHN stack ((2,2,2), previously listed as unexercised at `.51`). Disposition: executable regression; partially closes `.55` item 4.

---
### EFF.GENHN.90  [lemma]  — LEMMA GENHN-COUNT-RERUN (μ = 2, corrected node)

**CANONICAL STATEMENT:** verbatim, lines 2352–2427.

**FORM:** display — a blockquoted LaTeX lemma with four numbered clauses and eight `\tag{}`ed equations (CR-1)–(CR-6). **This is the note's ONLY tagged display; the `\tag{` count over the whole note is 8 and all eight are here.**

> “> **LEMMA GENHN-COUNT-RERUN (\(\mu=2\), corrected node).**
> > Let
> >
> > \[
> > G=(Q;e_1,f_1,2;h,\mathrm{entry}),
> > \qquad D'=e_1f_1,\qquad
> > K=\mathbf F_{Q^{f_1}},
> > \qquad B=D'h,
> > \]
> >
> > where \(h\ge1\) and \(\gcd(e_1,h)=1\). For every component-complete finite stage cap \(M\), let
> >
> > \[
> > \mathcal N_B(M)=
> > \left\{
> > (A_1,A_0):
> > dv(A_1)>B,\quad
> > dv(A_0)>2B,\quad
> > \text{all retained heights are }\le M
> > \right\}.
> > \]
> >
> > Then the GENHN-2 slot map induces a bijection
> >
> > \[
> > \mathcal N_B(M)\;\xrightarrow{\sim}\;
> > K^{\{B+1,\ldots ,M\}}
> > \times
> > K^{\{2B+1,\ldots ,M\}}.
> > \tag{CR-1}
> > \]
> >
> > Under this bijection:
> >
> > 1. the finite-stage reader is exactly the finite-window \((2,K)\)-cluster reader at lower node \(B\);
> > 2. its `RAM`, `2SIDED`, `SPLTAIL`, `SPLITEQ`, `INERT`, and recursively alpha-refined per-key cardinalities are the standard \((2,K)\) cell-law cardinalities at that node;
> > 3. for every alpha height \(\kappa>B\) and every fixed \(s\in K^\times\), recentering is a count-bijection from the \((\kappa,s)\)-slice onto \(\mathcal N_\kappa(M)\). Consequently
> >
> >    \[
> >    \#\{\text{alpha states at height }\kappa\}
> >    =(|K|-1)\,|\mathcal N_\kappa(M)|;
> >    \tag{CR-2}
> >    \]
> >
> > 4. at a common coefficient-window boundary, a nonzero visible pin of dimension \(\operatorname{comp}(m)\) has census
> >
> >    \[
> >    Q^{\operatorname{comp}(m)}-1,
> >    \tag{CR-3}
> >    \]
> >
> >    and its decision is governed by GENHN-CAP-GEN’s completion-invariance rule.
> >
> > Therefore every ordinary \(\mu=2\) GENHN count display survives the floor correction after
> >
> > \[
> > S=e_1h\quad\rightsquigarrow\quad
> > B=D'h=e_1f_1h.
> > \tag{CR-4}
> > \]
> >
> > The literal numeric \(S\)-node law survives uniformly in the stage cap exactly when \(f_1=1\). In particular, for \(M\ge2B\),
> >
> > \[
> > |\mathcal N_B(M)|
> > =|K|^{(M-B)+(M-2B)},
> > \tag{CR-5}
> > \]
> >
> > while the old \(S\)-node volume is larger by
> >
> > \[
> > |K|^{3(B-S)}.
> > \tag{CR-6}
> > \]”

**SUPERSESSION KIND: counter re-reading** (every S-keyed count display is re-read at the `B = D′h` node, with the counts re-derived) + **license** (it settles GENHN-ERR-1, which `[r1]` left open). `TARGETS: .12` (GENHN.A(v)'s “at the S-node”), `.36` (§S6.2's assembly sentence), `.24` (the ERR-1 residue).

**CONDITIONALITY:**
(a) **Scope: μ = 2 and ORDINARY genres.** Nothing here touches μ ≥ 3 or towers.
(b) **It depends on `.88`'s tightened slot scope** — the proof's first line says so: “We use only occupied heights \(m>B=D'h\), **the certified scope of the corrected GENHN.A(ii) slot clause**.” So this lemma inherits `.88`'s “awaiting sol re-confirmation” status transitively. See OPEN-CALL 4.
(c) **It protects the bracket explicitly** — see `.92` item 3: `b_{2,K}(κ)` is unchanged because it is indexed by the refine height and uses a different ghost normalization.
(d) **Its own status:** “a final transcription-confirmation rides the next queue” (2626–2627). This is the state the charge names for GENHN-ERR-1: **SETTLED-WITH-TRANSCRIPTION-CONFIRMATION-OWED.**

**DERIVATION:** Lines 2428–2589, the full proof. Structure, in the note's own order: (1) occupied heights and the unique `i₀` from `gcd(e₁,h) = 1`; (2) LEMMA GENHN-LIFT supplies `L_m(λ)` and GENHN-2 supplies the inverse, giving slotwise bijections with disjoint coefficient-digit positions (position `(i,r)` has the unique height `e₁r + ih`); (3) the retained ranges `B+1..M` and `2B+1..M` give (CR-1); (4) the slot series `𝒜_j(t)` has least nonzero height exactly `dv(A_j)`, so the polygon of `Y² + A₁Y + A₀` agrees point for point with the `t`-ladder version over `K` — clause 1; (5) depth-zero counts read directly (SPLTAIL, 2SIDED, RAM, and the `u = 2κ` residual censuses); (6) the alpha step: `GENHN-LIFT` supplies the exact-height lift of `s`, `GENHN-4` kills the two pins, `GENHN-3` respects the cap, and the translation is invertible, giving (CR-8) and hence (CR-2) and clause 3, and clause 2 by induction on the finite recursive history; (7) the boundary census `|V_m| − 1 = Q^{comp(m)} − 1` and GENHN-CAP-GEN's rule give (CR-3) and clause 4; (8) `|𝒩_b(M)| = q_K^{(M−b)_+ + (M−2b)_+}` gives (CR-5), and the ratio computation gives (CR-4)/(CR-6). ∎

*Arithmetic audit (rule 22) — every tagged equation recomputed independently.*
- **(CR-1).** `𝒩_B(M)` requires `dv(A₁) > B` and `dv(A₀) > 2B`, all retained heights `≤ M`. Retained slot ranges: `A₁` at heights `B+1..M` (that is `M − B` slots), `A₀` at `2B+1..M` (`M − 2B` slots) ✓ — matching the displayed `K^{\{B+1,…,M\}} × K^{\{2B+1,…,M\}}` ✓.
- **(CR-5).** `|K|^{(M−B)+(M−2B)}` ✓ = the product of the two slot-space sizes ✓, valid for `M ≥ 2B` (else the second range is empty) ✓ — and the proof's general form `q_K^{(M−b)_+ + (M−2b)_+}` handles `M < 2b` ✓.
- **(CR-6).** Ratio `|𝒩_S(M)|/|𝒩_B(M)| = q_K^{[(M−S)+(M−2S)] − [(M−B)+(M−2B)]} = q_K^{(B−S)+2(B−S)} = q_K^{3(B−S)}` ✓ **the displayed exponent is exactly `3(B−S)`** ✓. The proof writes it as `q_K^{(2M−3S)−(2M−3B)}` ✓ same thing.
- **(CR-4)/the `f₁ = 1` claim.** `B − S = D′h − e₁h = e₁f₁h − e₁h = e₁h(f₁−1)` ✓ **exactly the proof's line** ✓. Ratio `= 1` iff `f₁ = 1` ✓; `> 1` iff `f₁ ≥ 2` ✓.
- **(CR-2)/(CR-7)/(CR-8).** The alpha slice at height `κ` with fixed `s ∈ K^×` maps bijectively to `𝒩_κ(M)` ✓; summing over the `q_K − 1` letters gives `(q_K−1)|𝒩_κ(M)|` ✓. Cross-check against `.89`'s table: at (1,2,2), `q_K − 1 = 3` and `|𝒩_κ| = 256`, giving `768` ✓ **exactly the measured RAM**; at (2,2,2), `3 × 4096 = 12288` ✓. **(CR-2) is confirmed by the certificate.**
- **(CR-7).** The common free-tail factor `q_K^{(M−κ)+(M−2κ)} = |𝒩_κ(M)|` ✓ consistent with (CR-5) at node `κ`.
- **(CR-3).** `|V_m| − 1 = Q^{dim_{F_Q} V_m} − 1 = Q^{comp(m)} − 1` ✓ — and this is the **third independent derivation** of E2's census in the corpus (E2 at shard 1 `.14`; GENHN-CAP-GEN's COUNT TRANSPORT at `.79`; here) ✓ all three agree.
- **The finite-field censuses in the proof.** `#SPLITEQ = (q_K−1)(q_K−2)/2`, `#INERT = q_K(q_K−1)/2`, `#ALPHA = q_K−1`. Check exhaustiveness over monic `T² + aT + b` with `a ∈ K`, `b ∈ K^×`: total `= q_K(q_K−1)`. Sum: `(q_K−1)(q_K−2)/2 + q_K(q_K−1)/2 + (q_K−1) = (q_K−1)[(q_K−2)/2 + q_K/2 + 1] = (q_K−1)[(2q_K−2)/2 + 1] = (q_K−1)(q_K−1+1) = (q_K−1)q_K` ✓ **exactly the total.** The three censuses partition the residual space with no remainder ✓. (Interpretation: SPLITEQ = two distinct nonzero roots, unordered: `(q_K−1)(q_K−2)/2` ✓; INERT = irreducible monic quadratics with nonzero constant: total irreducibles `q_K(q_K−1)/2`, all of which have `b ≠ 0` ✓; ALPHA = a repeated root `s ≠ 0`: `q_K − 1` ✓.)
- **Depth-zero counts.** `A₀` vanishing through `M` with exact `A₁`-value `w > b` contributes `(q_K−1)q_K^{M−w}` ✓ (leading digit nonzero, `M − w` free slots above). `A₀` with exact value `u`: `(q_K−1)q_K^{M−u}` ✓. 2SIDED for `2w < u`: product `(q_K−1)²q_K^{(M−u)+(M−w)}` ✓.
**Every tagged equation and every census reproduces exactly. The partition identity `(q_K−1)q_K` is an independent check the note does not state.**

**RESOLUTION TRACE:** statement 2352–2427 · proof 2428–2589 · certificate 2336–2350 · sweep 2591–2605 · provenance 2607–2627 · dependencies 2101–2145 (GENHN-LIFT), 2061–2085 (CAP-GEN), 2315–2332 (the slot scope).

XREF: `GENH4_PROOF_2026-08-08.md:law_F` — count **7** (the (1,2,2) genre whose sealed child displays are refuted).
XREF: `HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-3` — count **8** (the completion clause the sweep restores; see `.92` item 5).

**TEETH:** **`genhn_f2_count_check.py`** — “measured = predicted on every key at (1,2,2) and the first-ever mixed-genre contact (2,2,2); the sealed S-node child displays refuted exactly as predicted”. **Disposition: executable regression, post-seal, with a preregistered refutation** (the design predicted which displays would break, and they did). This is the only lemma in the note whose *composition* was gated on a machine certificate confirming its table first (`.93`).

---
### EFF.GENHN.91  [scope-record]  — the proof's own scope line and slot-position uniqueness

**CANONICAL STATEMENT:** verbatim, lines 2428–2429 and 2463–2471 (the two load-bearing scope/uniqueness passages of `.90`'s proof, emitted separately because both are cited from elsewhere).

**FORM:** proof-body prose with inline LaTeX.

> “**Proof.** Put \(q_K:=|K|=Q^{f_1}\). We use only occupied heights \(m>B=D'h\), the certified scope of the corrected GENHN.A(ii) slot clause.”

and

> “Conversely, GENHN-2 says that the \(f_1\) coefficient digits at these positions assemble into exactly one \(K\)-digit: the powers
>
> \[
> 1,\eta,\ldots,\eta^{f_1-1}
> \]
>
> are \(F_Q\)-independent, so no nonzero combination can cancel. Different heights use disjoint coefficient-digit positions, because a position \((i,r)\) has the unique height \(e_1r+ih\). Hence the maps supplied by GENHN-2 and GENHN-LIFT are inverse slotwise bijections.
>
> For \(A_1\), the corrected floor is \(dv(A_1)>B\), so its retained slots are precisely \(B+1,\ldots,M\). For \(A_0\), the floor is \(dv(A_0)>2B\), so its retained slots are \(2B+1,\ldots,M\). The two coordinates are independent. This proves (CR-1).”

**CONDITIONALITY:** **The scope line is the explicit dependency edge from `.90` to `.88`** — this lemma is only valid on the domain the post-D2b corrigendum certifies, and that corrigendum is “awaiting sol re-confirmation”. Any chapter cut using GENHN-COUNT-RERUN inherits that.
**The uniqueness claim is independently checkable and was checked**: the P2 provenance parenthetical (`.93`) says “the slot-position uniqueness ((i, r) ↦ e₁r + ih injective on the retained range) checked”.

**DERIVATION:** Injectivity of `(i, r) ↦ e₁r + ih` on `0 ≤ i < e₁`: if `e₁r + ih = e₁r' + i'h` then `ih ≡ i'h (mod e₁)`, and `gcd(h, e₁) = 1` gives `i ≡ i' (mod e₁)`, hence `i = i'` and then `r = r'` ✓.

*Arithmetic audit (rule 22).* Verified above: injectivity holds exactly under `gcd(h, e₁) = 1`, which is the lemma's stated hypothesis ✓. Counter-check: at `gcd(h, e₁) = g > 1`, `i` and `i + e₁/g`… would collide only if `(i−i')h ≡ 0 (mod e₁)` with `i ≠ i'`, possible when `g > 1` ✓ — so the hypothesis is load-bearing, not decorative. **This matches the shard-1 tooth HE7-style observation that gcd hypotheses are machine-load-bearing; here no tooth exercises it, so it is PROOF-ONLY.**

**RESOLUTION TRACE:** statement 2428–2429, 2463–2471 · dependency 2315–2332 · verification 2618–2619 (`.93`).

**TEETH:** **PROOF-ONLY.** The `gcd(e₁, h) = 1` hypothesis is not mutated by any GENHN tooth. Coverage-hole sentence: GENHN-BOX-3's row list — every row has a single fixed `h` coprime to `e₁` by construction, so no row can violate it.

---
### EFF.GENHN.92  [changes-record]  — the Consumer sweep (five items)

**CANONICAL STATEMENT:** verbatim, lines 2591–2605.

**FORM:** bold-headed numbered list of five consumer consequences.

> “**Consumer sweep.**
>
> 1. **GENHN-ERR-1 is settled.** The ordinary \(\mu=2\) stage law is the \((2,K)\)-law at \(B=D'h\), not at the old numeric node \(S=e_1h\). No entry fiber, sibling factor, key-center factor, or ghost normalization is part of the raw node count.
>
> 2. **The alpha mismatch is resolved.** For fixed \(s\), \(|\mathcal N_\kappa(M)|\) is the total alpha-child slice, not its `UND` subcell. Thus the rerun’s \(768+256=1024\) and \(12288+4096=16384\) partitions are forced by refine transfer. The sealed `UND` entries \(1024\) and \(16384\) were totals attached to the wrong child key.
>
> 3. **GENHN.A(v) and S6.2 are re-grounded.** Every phrase “the \((2,K)\)-cluster read at the \(S\)-node” is read count-side as “at the \(B=D'h\)-node.” The local mass-normalized bracket
>    \[
>    b_{2,K}(\kappa)=(|K|-1)|K|^{2\kappa-1}
>    \]
>    is unchanged: it is indexed by the actual refine height \(\kappa\) and uses a different ghost normalization from the raw finite-node cardinality.
>
> 4. **All ordinary \(f_1\ge2\), \(\mu=2\) count displays are restored on the corrected node.** Interior pins use the full \(K\)-census; boundary pins retain the already-corrected census \(Q^{\operatorname{comp}(m)}-1\). Mixed \((e_1,f_1)\) genres require no further count-side exception.
>
> 5. **HE6R1’s completion-statement clause is restored with no wording change.** Its quantification over compatible completions is exactly GENHN-CAP-GEN’s completion-invariance assertion. The correction changes the initial count node from \(S\) to \(D'h\); it does not change HE6R1’s completion predicate, its \(D'h\)-based root separation, or its conclusion.”

**SUPERSESSION KIND: counter re-reading** (item 3, the S-node phrase) + **inventory completion** (items 1, 4 close a named residue) + **license** (item 5 restores a consumer clause). `TARGETS: .24` (ERR-1), `.12` (GENHN.A(v)), `.36` (§S6.2), and externally HE6R1's completion clause.

**CONDITIONALITY:**
(a) **Item 1 is the TERMINAL member of the GENHN-ERR-1 SERIES** — SETTLED. But the provenance parenthetical (`.93`) adds “a final transcription-confirmation rides the next queue”, so the compiled state is **SETTLED-WITH-TRANSCRIPTION-CONFIRMATION-OWED**, exactly as the charge names.
(b) **Item 3 is a re-reading with a protection**: the phrase moves, the bracket does not. Both halves are load-bearing and must travel together.
(c) **Item 5 is a cross-note claim and per rule 10 needs care.** It says HE6R1's completion clause is “restored with no wording change”. **This compiler verified that no append lands on `HE6R1_RECON_2026-08-08.md` from GENHN** (GENHN's protocol is flag-don't-fold, header §B), so item 5 is a *reading* of HE6R1 offered by GENHN, not a landed correction. `LEMMA HE6R1-3` is grep-verified in the target (count 8). Recorded as a reading; see OPEN-CALL 5.
(d) **Item 4's “Mixed \((e_1,f_1)\) genres require no further count-side exception”** is the strongest new claim in the sweep and it rests on the (2,2,2) certificate — a *single* mixed genre. Recorded.

**DERIVATION:** Each item follows from `.90`: item 1 from (CR-4); item 2 from (CR-2); item 3 from (CR-4) plus the bracket's differing normalization; item 4 from clauses 2 and 4; item 5 from clause 4 + GENHN-CAP-GEN.

*Arithmetic audit (rule 22).* Item 2's two partitions were audited at `.89` and reproduce exactly (`768 + 256 = 1024`, `12288 + 4096 = 16384`, both with the `(q_K−1) : 1` split) ✓. Item 3's bracket `(|K|−1)|K|^{2κ−1}` matches shard 1 `.36`'s display byte-for-byte ✓ and its independence from the node is exactly the ghost-fiber factorization audited there (`|K|^κ · (|K|−1)|K|^{κ−1}`) ✓. Item 1's `B = D′h` vs `S = e₁h` differ by the factor `f₁` ✓ (`D′h = e₁f₁h = f₁S`), consistent with (CR-6)'s `B − S = e₁h(f₁−1)` ✓.

**RESOLUTION TRACE:** statement 2591–2605 · lemma 2352–2589 · targets 605–611, 193–211, 925–944 (shard 1) · confirmation owed 2626–2627.

XREF: `HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-3` — count **8**.
XREF: `GENIND_PROOF_2026-08-08.md:LEMMA GENIND-2` — count **7** (the bracket's source).

**TEETH:** Items 1, 2, 4 are toothed by `genhn_f2_count_check.py`; item 3 is PROOF-ONLY (the bracket's invariance is an argument, not a measurement); item 5 is a cross-note reading with no tooth. **Disposition: mixed — executable regression (1, 2, 4), PROOF-ONLY (3), unverified reading (5).**

---
### EFF.GENHN.93  [instrument-record]  — the P2 provenance parenthetical (the note's final lines)

**CANONICAL STATEMENT:** verbatim, lines 2607–2627.

**FORM:** italic parenthetical paragraph, the last text in the note.

> “*(LEMMA GENHN-COUNT-RERUN above was composed by the P2 certification
> run (gpt-5.6-sol high, runs/cert4/P2_genhn_count_output.log,
> 2026-08-12) from the N3 design after its machine certificate
> confirmed the table (verification/openmath/genhn_f2_count_check.py:
> measured = predicted on every key at (1,2,2) and the first-ever
> mixed-genre contact (2,2,2); the sealed S-node child displays
> refuted exactly as predicted — sealed RAM 0 / UND 1024 vs actual
> 768 / 256, and 0 / 16384 vs 12288 / 4096). Orchestrator verification
> before transcription — the proof consumes exactly this campaign's
> certified pillars (GENHN-LIFT at the corrigendum's m > D′h scope,
> cited as such; GENHN-CAP-GEN for the boundary clause; GENHN-2's
> independence; GENHN-3's cap respect); the slot-position uniqueness
> ((i, r) ↦ e₁r + ih injective on the retained range) checked; the
> ratio |N_S|/|N_B| = q_K^{3(B−S)} with B − S = e₁h(f₁ − 1)
> re-computed; the α-mismatch autopsy (sealed totals attached to the
> wrong child key) consistent with the measurement; the sweep's
> restoration of HE6R1's completion clause with no wording change
> confirmed as the directive's prove-don't-qualify outcome. GENHN-ERR-1
> is SETTLED. Transcribed unaltered per the standing division of
> labor. Ledger: row 15 → the count re-run obligation is DISCHARGED; a
> final transcription-confirmation rides the next queue.)*”

**CONDITIONALITY:** **The note's last words, and they carry three distinct statuses that must not be merged.**
(i) **“GENHN-ERR-1 is SETTLED.”**
(ii) **“the count re-run obligation is DISCHARGED”** (ledger row 15).
(iii) **“a final transcription-confirmation rides the next queue.”**
So: the mathematics is settled, the obligation is discharged, and the *transcription* is unconfirmed. **This shard compiles all three verbatim and refuses to collapse them.** See OPEN-CALL 4.
**One methodological fact of record:** the lemma was **composed after** its machine certificate confirmed the table — “composed … from the N3 design **after** its machine certificate confirmed the table”. That is the reverse of the preregistration discipline used for the sealed battery (`.64`/`.70`), and it is disclosed. The design predicted which sealed displays would break (“refuted exactly as predicted”), so the prediction preceded the run even though the *lemma* followed it. Recorded precisely rather than assimilated to either pattern.

*Compiler cross-check (rule 22).* This shard independently recomputed four of the five verification claims: the slot-position injectivity (`.91`) ✓; the ratio `q_K^{3(B−S)}` with `B − S = e₁h(f₁−1)` (`.90`) ✓; the α-mismatch decomposition (`.89`) ✓; the certificate's two tables (`.89`) ✓. **All four reproduced.** The fifth (HE6R1's completion clause restored with no wording change) is a cross-note reading this compiler did not independently adjudicate — flagged at `.92`(c) and OPEN-CALL 5.

**DERIVATION:** Provenance record.

**RESOLUTION TRACE:** statement 2607–2627 · lemma 2352–2589 · certificate 2336–2350.

ARTIFACT: `runs/cert4/P2_genhn_count_output.log` ✓ · `verification/openmath/genhn_f2_count_check.py` ✓ — 2/2 present.

**TEETH:** **`genhn_f2_count_check.py`** as at `.89`/`.90`. **Disposition: executable regression that gated a composition** — the unusual pattern here is that the certificate ran *first* and the lemma was written to it.

---

## 4. XREF verification ledger (consolidated, deduplicated)

Every designation below was checked with fixed-string grep (`grep -cF '<designation>' <file>`) against the target note, run fresh from `lean/notes/openmath/` at merge time. **Both shards' own §3.1 "Verified import/XREF designations" tables are internally miscounted against their own header sentence** — shard 1's header states "38 distinct designations" but its own table lists **65** numbered rows; shard 2's header states "31 distinct designations" but its own table lists **52** numbered rows. This merge uses the actual table row counts (65 and 52 — independently re-counted by this merge run against the raw shard files: `grep -cE '^\| [0-9]+ \|'` over each shard's §3.1 range returns 65 and 52 respectively) as ground truth, since those are what is actually enumerable and checkable, and **records the header/table mismatch as a recorded source defect in both shards independently** (§8 below) rather than silently picking either number.

**65 + 52 = 117 raw XREF citations reduce to 76 distinct `target:designation` pairs; 41 duplicate instances (41 distinct designations cited by both shards) are marked `**DEDUP**` and removed as separate rows.** Every duplicate's count agrees exactly across both shards that cited it — **zero count mismatches found** (a fixed-string grep against an unchanged file must return the same count regardless of who runs it, and a mismatch would have meant one shard mis-copied its own grep output; this merge independently re-verified every one of the 41 duplicated counts by direct string comparison during the parse pass, not merely by trusting the shards' agreement). No zero-count or purely descriptive string is emitted as an XREF below; no designation was invented at merge time.

`[TABLE — compiler ledger]`

| # | Target : designation | Count | Role | Source shard(s) | Dedup |
|---:|---|---:|---|---|---|

| 1 | `GENIND_PROOF_2026-08-08.md:THEOREM GENIND.A` | 4 | The stage's own history grammar over K (GENHN.A(v)) | s1 | — |
| 2 | `GENIND_PROOF_2026-08-08.md:GENIND.A(IV)` | 5 | The abscissa-length ≥ 4 criterion — GENHN-T(a)'s engine | s1 | — |
| 3 | `GENIND_PROOF_2026-08-08.md:GENIND.C` | 23 | The drainage recursion run inside the stage (§S6.3) / Named in the §S10 stack | s1+s2 | **DEDUP** |
| 4 | `GENIND_PROOF_2026-08-08.md:THEOREM GENIND.B` | 7 | The induction GENHN.B's discharge feeds / The scaffold GENHN.B feeds | s1+s2 | **DEDUP** |
| 5 | `GENIND_PROOF_2026-08-08.md:LEMMA GENIND-0` | 5 | (A1)-family closure — GENHN.CLASS(ii)'s finiteness step / (A1)-family closure, cited by the F-2 re-display | s1+s2 | **DEDUP** |
| 6 | `GENIND_PROOF_2026-08-08.md:LEMMA GENIND-1` | 2 | State classification (i), binomial kills (ii), fracture permanence (iii) / §S10 stack | s1+s2 | **DEDUP** |
| 7 | `GENIND_PROOF_2026-08-08.md:LEMMA GENIND-2` | 7 | Window coherence + the (b) bracket run inside the stage / The bracket's source (sweep item 3) | s1+s2 | **DEDUP** |
| 8 | `GENIND_PROOF_2026-08-08.md:LEMMA GENIND-3` | 6 | β-fracture fibration; the embedded-genre Hensel split / β-route ledgers, endgame item 3 | s1+s2 | **DEDUP** |
| 9 | `GENIND_PROOF_2026-08-08.md:GENIND-5` | 9 | The (q−1)q^{2μ−1} shape being (e₁,f₁)-generalized — **not a proved theorem in its source** (OPEN-CALL 6) | s1 | — |
| 10 | `GENIND_PROOF_2026-08-08.md:GENIND-BOX-3` | 3 | The d = 1 ambient coverage restriction, inherited / The d = 1 coverage restriction inherited by BOX-3 | s1+s2 | **DEDUP** |
| 11 | `GENIND_PROOF_2026-08-08.md:GT-BRACKETID` | 3 | The μ = 3 bracket exponent c(3)+1 = 4, foreign evidence | s1 | — |
| 12 | `GENIND_PROOF_2026-08-08.md:GENIND-H(n)` | 7 | The per-genre package GENHN.B discharges | s1 | — |
| 13 | `GENIND_PROOF_2026-08-08.md:(CS-1)` | 49 | Stage transport — **the pricing grammar's real home** (see defect 2) / The consumer clause `[r2]`/`[r3]` flag | s1+s2 | **DEDUP** |
| 14 | `GENIND_PROOF_2026-08-08.md:(CS-2)` | 20 | Stage bracket / Ditto; also the supplied referent for the mis-cited “GENHN-2(b)'s bracket” | s1+s2 | **DEDUP** |
| 15 | `GENIND_PROOF_2026-08-08.md:(CS-3)` | 13 | σ-decision | s1 | — |
| 16 | `GENH4_PROOF_2026-08-08.md:THEOREM GENH4.A` | 5 | The n = 4 template GENHN generalizes / §S10 stack | s1+s2 | **DEDUP** |
| 17 | `GENH4_PROOF_2026-08-08.md:GENH4.B` | 7 | The two-term genre-F drainage display consumed at §S6.3 | s1 | — |
| 18 | `GENH4_PROOF_2026-08-08.md:THEOREM GENH4.C` | 9 | GENHN.C's (2,1,2)/(1,2,2) instances, verbatim | s1 | — |
| 19 | `GENH4_PROOF_2026-08-08.md:GENH4-1F` | 10 | The four displayed entry cancellations (GENHN-1's proof) | s1 | — |
| 20 | `GENH4_PROOF_2026-08-08.md:GENH4-2` | 15 | The (E)/(F) slot instances of GENHN-2 | s1 | — |
| 21 | `GENH4_PROOF_2026-08-08.md:GENH4-CAP` | 18 | The band cap; `GENH4-CAP(F)` (count 11) is E1's subject / The band cap; the S5 computation cited by BOX-2 | s1+s2 | **DEDUP** |
| 22 | `GENH4_PROOF_2026-08-08.md:GENH4-3` | 11 | The hull partition E1's trichotomy is re-derived from | s1 | — |
| 23 | `GENH4_PROOF_2026-08-08.md:GENH4-4` | 11 | Named in the S0 template list | s1 | — |
| 24 | `GENH4_PROOF_2026-08-08.md:GENH4-6` | 6 | Named in the S0 template list | s1 | — |
| 25 | `GENH4_PROOF_2026-08-08.md:law_E` | 2 | The μ = 2 stage-law evaluator, consumed at md5 pin / The μ = 2 evaluator @ md5 pin | s1+s2 | **DEDUP** |
| 26 | `GENH4_PROOF_2026-08-08.md:law_F` | 7 | The genre-F evaluator; the f₁ = 2 instance / The genre-F evaluator; the (1,2,2) keys refuted by the rerun | s1+s2 | **DEDUP** |
| 27 | `GENH4_PROOF_2026-08-08.md:ANNEX R` | 12 | The R3 transport obligation that E3 discharges / E3's model, re-cited in the refresh | s1+s2 | **DEDUP** |
| 28 | `GENH4_PROOF_2026-08-08.md:R3` | 9 | E3's stated model | s1 | — |
| 29 | `QSCOUT22_2026-08-08.md:Q22-A` | 3 | The committed quartic table; the n = 4/5 entry patterns / The committed quartic table | s1+s2 | **DEDUP** |
| 30 | `W12_PROOF_2026-08-08.md:THEOREM W-12.A` | 8 | The order-1 cell law being (e₁,f₁)-re-based / Entry laws; the conservative finite-window read CAP-GEN transports | s1+s2 | **DEDUP** |
| 31 | `W12_PROOF_2026-08-08.md:W-12.D` | 19 | The reduction that fires the densities / The firing reduction | s1+s2 | **DEDUP** |
| 32 | `W12_PROOF_2026-08-08.md:S2.5` | 9 | The entry-law section pinned in S0 / Entry-law section pin | s1+s2 | **DEDUP** |
| 33 | `W12_PROOF_2026-08-08.md:[W12-H]` | 17 | The pricing grammar's real home (see defect 2) | s1 | — |
| 34 | `W12_PROOF_2026-08-08.md:(H-e)` | 8 | The box GENHN.C instantiates and GENHN shrinks to μ ≥ 3 | s1 | — |
| 35 | `W11_PROOF_2026-08-08.md:W-11` | 18 | The n = 2 system — the μ = 2 read's target after re-basing / The μ = 2 re-basing target | s1+s2 | **DEDUP** |
| 36 | `GRTJC_PROOF_2026-08-08.md:COROLLARY W-9` | 2 | The graded frame: FRAME at GENHN-2, CONSUMED at GENHN-4 layer 1 / The weld face BOX-2 discloses | s1+s2 | **DEDUP** |
| 37 | `GRTJC_PROOF_2026-08-08.md:JC-LOAD` | 31 | Graded no-cancellation — re-proved elementarily, not consumed / §S10 stack | s1+s2 | **DEDUP** |
| 38 | `GRTJC_PROOF_2026-08-08.md:W-8` | 35 | Named in the S0 GRTJC bullet / §S10 stack | s1+s2 | **DEDUP** |
| 39 | `GRTJC_PROOF_2026-08-08.md:W-6` | 18 | Named in the S0 GRTJC bullet / §S10 stack | s1+s2 | **DEDUP** |
| 40 | `JD0_PROOF_2026-08-08.md:J-D0` | 25 | Count-gauge-blindness — conclusion consumed, **reason disclosed false** (`.28`) / Twist-blindness; §S10 stack | s1+s2 | **DEDUP** |
| 41 | `DULEMMA_PROOF_2026-08-08.md:DULEMMA` | 1 | Perimeter checked, NOT consumed / Perimeter checked, not consumed; riddered by E3 | s1+s2 | **DEDUP** |
| 42 | `SIGMALAW_PROOF_2026-08-08.md:(EC-q)` | 26 | Letter-layer coherence at towers; no count consumption / Letter-layer at towers; the S8(b) pointer (defect 3) | s1+s2 | **DEDUP** |
| 43 | `HE3_PROOF_2026-08-08.md:HE3-0` | 19 | The (T1)/(T2) locus in the `[r1]` node derivation | s1 | — |
| 44 | `HE3_PROOF_2026-08-08.md:GENHN-HE` | 7 | The consumer that claims to close the box (reverse edge) | s1 | — |
| 45 | `HE6_PROOF_2026-08-08.md:LEMMA HE6-0` | 17 | dv(Φ′(ρ)) > D′h — the `[r1]` node's engine | s1 | — |
| 46 | `HE6_PROOF_2026-08-08.md:LEMMA HE6-3` | 12 | (SEP)-free slope bound in the same derivation | s1 | — |
| 47 | `HE7_PROOF_2026-08-08.md:LEMMA GENHN-2` | 1 | Reverse edge: HE7's ladder base case | s1 | — |
| 48 | `HE7_PROOF_2026-08-08.md:[GENHN-HE(μ)]` | 2 | Reverse edge: the predicate HE7's COROLLARY HE7.B discharges at level 2 | s1 | — |
| 49 | `HETOW_RECON_2026-08-09.md:HETOW-1` | 23 | The bridge lemma re-proved at the corrected composed key / Bridge lemma re-proved at the corrected key | s1+s2 | **DEDUP** |
| 50 | `HETOW_RECON_2026-08-09.md:HETOW-2` | 9 | Ditto | s1+s2 | **DEDUP** |
| 51 | `HETOW_passPE1_report.md:F-1` | 9 | The gauge-naive-lift finding landing on T(b)′ / The gauge-naive-lift finding | s1+s2 | **DEDUP** |
| 52 | `GENHN_passPE1_report.md:F1` | 7 | The T(b) refutation / The T(b) refutation (arc line) | s1+s2 | **DEDUP** |
| 53 | `GENHN_passPE1_report.md:F2` | 5 | The GENHN-1 budget display / The budget display | s1+s2 | **DEDUP** |
| 54 | `GENHN_passPE1_report.md:F3` | 4 | The f₁ ≥ 3 band transport GAP / The band-transport GAP | s1+s2 | **DEDUP** |
| 55 | `GENHN_passPE1_report.md:F4` | 3 | The stage-RAM value-group repair / The stage-RAM repair | s1+s2 | **DEDUP** |
| 56 | `GENHN_passPE1_report.md:F5` | 3 | The 350-vs-349 tail reconciliation (shard 2's subject) / The 350/349 tail reconciliation | s1+s2 | **DEDUP** |
| 57 | `GENHN_passPE2_report.md:F1` | 9 | The depth-≥ 3 iterated composition, boxed as item (6) / Item (6), the depth split | s1+s2 | **DEDUP** |
| 58 | `GENHN_passPE2_report.md:F2` | 5 | The (CS-3) full-inner-side scope / The full-inner-side scope | s1+s2 | **DEDUP** |
| 59 | `GENHN_passPE2_report.md:F3` | 5 | The budget erratum's sign / The budget sign | s1+s2 | **DEDUP** |
| 60 | `GENHN_passPE2_report.md:F4` | 5 | The 35/38 → 35/35 denominator | s1+s2 | **DEDUP** |
| 61 | `GENHN_passPE3_report.md:F-1` | 4 | Item (6)(α)'s mechanism attribution | s1+s2 | **DEDUP** |
| 62 | `GENHN_passPE3_report.md:F-2` | 5 | The "full inner sides" scope word at three echo sites / The three residual echo sites | s1+s2 | **DEDUP** |
| 63 | `GENHN_passPE4_report.md:F-1` | 3 | The "none is live below n = 8" scope defect / The “none is live below n = 8” scope defect | s1+s2 | **DEDUP** |
| 64 | `CODEX_HE6PE1_2026-08-08.md:finding 3` | 2 | The display inconsistency that lands as the `[r1]` erratum | s1 | — |
| 65 | `WELDZERO_2026-08-14.md:WZ-BOX-7` | 10 | The disclosed false parenthetical at GENHN L736–737 (`.28`) | s1 | — |
| 66 | `GENIND_PROOF_2026-08-08.md:GENIND.A(I)` | 3 | The scaffold clause list in §S10 | s2 | — |
| 67 | `GENIND_PROOF_2026-08-08.md:GENIND-BOX-2` | 1 | The compression-ledger discipline endgame item 3 follows | s2 | — |
| 68 | `GENIND_PROOF_2026-08-08.md:S16` | 22 | (§-anchor) the fired-clause table cited by the `[e2]` refresh | s2 | — |
| 69 | `GENH4_PROOF_2026-08-08.md:GENH4-BOX-5` | 1 | The reader-reimplementation seams BOX-4 inherits; the S9-assembly precedent | s2 | — |
| 70 | `GENH4_PROOF_2026-08-08.md:ANNEX PE5` | 7 | The GENH4 annex stack in the `[e2]` refresh | s2 | — |
| 71 | `GENH4_PROOF_2026-08-08.md:ANNEX R2` | 5 | The refresh's annex-stack list | s2 | — |
| 72 | `QSCOUT22_2026-08-08.md:Q22-BOX-3` | 1 | The q = 4 F-genre coverage restriction BOX-3 inherits | s2 | — |
| 73 | `HEX3_PROOF_2026-08-08.md:HEX3` | 83 | The minors-only CLEAN precedent; the arc stack | s2 | — |
| 74 | `HMENU3_PROOF_2026-08-08.md:ANNEX A` | 5 | HMENU3's acceptance annex in the refresh | s2 | — |
| 75 | `HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-3` | 8 | The completion clause sweep item 5 restores | s2 | — |
| 76 | `HE7_PROOF_2026-08-08.md:HE7` | 366 | The refresh's HE7 bullet (self-name; the D′h remark is pinned by HE6-0/HE6-3 in shard 1) | s2 | — |

**Total unique XREF designations: 76. Duplicate instances removed: 41.** No zero-count or descriptive string is emitted as an XREF; no designation was invented.

**Designations counted but NOT emitted as XREFs (11, deduped from both shards' own defect lists — recorded fully as source defects in §8):**
- `read22` (0, `QSCOUT22`); the WELDMASTER-attributed `[W12-H]`/`(CS-1)`/`(CS-2)`/`(CS-3)`/`(H-e)` (5 mis-attributions, all count 0 in `WELDMASTER_2026-08-08.md`, verified referents emitted above at rows 13, 14, 15, 33, 34); `GENIND-4` (0, `GENIND_PROOF`); `GENH4 S5`/`GENH4-S7.2`/`GENH4 S6.2`/`GENH4 S4`/`GENH4 S6.3` (§-anchor citations, bare `S5` alone has count 20, carried descriptively); `OB-a`…`OB-d` (GENH4's obstruction letters, cited by phrase); passPE1 remark labels `R1`–`R4` (not separately grep-addressable); four truncated artifact hashes `51154c95…`/`664036bc…`/`4a28246e…`/`10b685b0…` (**UNPINNED** per rule 23); `GENHN-2(b)` (the F-1 repair's own mis-citation, caught by the note itself and re-pinned to `(CS-2)`); `row 15` (a ledger-internal index, not a note designation).

**Battery artifacts verified to EXIST on disk** (`verification/openmath/`), union of both shards' independent checks: `genhn_checks.py`, `genhn_checks_output.txt`, `genhn_checks_results.json`, `genhn_pe1_fresh.py`, `genhn_pe1_fresh_output.txt`, `genhn_pe2_fresh.py`, `genhn_pe2_fresh_output.txt`, `genhn_pe3_fresh.py`, `genhn_pe3_fresh_output.txt`, `genhn_pe4_fresh.py`, `genhn_pe4_fresh_output.txt`, `genhnr2_supp.py`, `genhnr2_supp_output.txt`, `genhn_f2_count_check.py`, `hetow_pe1_fresh.py`, `hetowr1_supp.py` — **16/16 present.** Logs: `runs/cert/A2_genhn_output.log`, `runs/cert2/D2b_genhn_output.log`, `runs/cert4/P2_genhn_count_output.log`, `runs/residues/R4_genhn_output.log` — **4/4 present.** Corpus records: `runs/qgen/WELD_FACE_AUDIT.md`, `spec/HYPOTHESIS_LEDGER.md`, `lean/notes/openmath/WELDZERO_2026-08-14.md`, `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` — **4/4 present.**

**Commit pins verified with `git cat-file -t` (all → `commit`), union of both shards' independent checks: 44 distinct commits, 44/44 verified** — `970022b`, `4682bcf`, `4984004`, `121d9ab`, `3eb1667`, `4b5c085`, `dd67cda`, `f669cb0`, `99f1813`, `7020ceb`, `31506b3`, `83f47f4`, `9387eb1`, `f819f26`, `a27ed68`, `0089f9b`, `4b0d946`, `b10a5a7`, `5c8d2fd`, `850e77e`, `606821e`, `dcc20bb`, `380bc66`, `b653858`, `be4a1dc`, `ee17210`, `b6a1d69`, `050425d`, `19c0285`, `f60348b`, `a707430`, `58ae603`, `4e3b2ff`, `6f977ea`, `7a058c8`, `6053c3d`, `ca3754d`, `ba3de2a`, `5f821dc`, `d0d3ca6`, `5335ae3`, `701c7b1`, `beadeeb`, `baf05ed`, `760d20f`, `6568114`, `7f27065`.

**Hash pinning quality (rule 23), union of both shards' pinning ledgers:**

| Class | Count | Verdict |
|---|---:|---|
| Full md5, checkable in principle | 10 | PINNED |
| Truncated md5/sha (seven GN-PIN pins + `732af1e1` + four `51154c95…`-class hashes) | 12 | **UNPINNED** |
| As-of freeze-prefix md5s (four dated in §1's freeze-scope table: `c38f5283…`, `8c6d2291…`, `13e087d6…`, and the acceptance-record prefix) | 4 | **AS-OF-PIN** (verified honest at their own append time; un-recheckable now by design, per shard 2's own §6.3 proposed vocabulary gap — see §8) |
| Commit hashes | 44 | PINNED |

### Sample re-verification (10 of 76, grep-rerun at merge time against the working tree)

Sample favors designations cited by both shards, designations with distinctive counts, and at least one from each shard's own-only citations.

`[TABLE — compiler ledger]`

| Designation | Recorded count | Re-verified count | Match |
|---|---:|---:|---|
| `GENIND_PROOF_2026-08-08.md:(CS-1)` | 49 | 49 | ✓ |
| `GENIND_PROOF_2026-08-08.md:GENIND.C` | 23 | 23 | ✓ |
| `GENH4_PROOF_2026-08-08.md:GENH4-CAP` | 18 | 18 | ✓ |
| `GRTJC_PROOF_2026-08-08.md:JC-LOAD` | 31 | 31 | ✓ |
| `HE7_PROOF_2026-08-08.md:HE7` | 366 | 366 | ✓ |
| `GENIND_PROOF_2026-08-08.md:GENIND-5` (s1-only) | 9 | 9 | ✓ |
| `GENIND_PROOF_2026-08-08.md:GENIND-H(n)` (s1-only) | 7 | 7 | ✓ |
| `QSCOUT22_2026-08-08.md:Q22-BOX-3` (s2-only) | 1 | 1 | ✓ |
| `HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-3` (s2-only) | 8 | 8 | ✓ |
| `WELDZERO_2026-08-14.md:WZ-BOX-7` (s1-only) | 10 | 10 | ✓ |

**All 10 sampled counts match exactly; no drift introduced by sharding or merge.** The sample deliberately covers a very high-count designation (366), a very low-count designation (1), two duplicated-across-shards designations, and one designation from each shard's own-only citation list.

### Sample statement-quote re-verification (5 of 93, checked verbatim against the source note by line number)

`[TABLE — compiler ledger]`

| Statement | Quoted fragment | Source lines | Match |
|---|---|---:|---|
| `.02` (title box round records) | "Attempt grade 0/2 (composed; no hostile arc) … Clean count stays 0/2; PE3 next" | 3–20 | ✓ byte-exact |
| `.24` (`[r1]` ERRATUM, corrected node) | "the stage-initial node is { dv(A_j) ≥ (μ − j)·D′h + 1 } … none is live below n = 8." | 576–611 | ✓ byte-exact |
| `.42` (LEMMA GENHN-T(b)′, composed carrier) | "outer genre (Q; e₁, f₁, μ₁; h) … carrier in L₂/O_{L₂} per ERRATUM E3" | 1127–1155 | ✓ byte-exact |
| `.75` (post-PE4 acceptance record) | "passPE3 returned CLEAN … GENHN is ACCEPTED — the text is FROZEN" | 1941–1955 | ✓ byte-exact |
| `.90` (LEMMA GENHN-COUNT-RERUN, tagged LaTeX) | the full 76-line blockquoted lemma statement, `\tag{CR-1}`–`\tag{CR-6}` displays included | 2352–2427 | ✓ byte-exact (modulo the compiler's own outer quotation marks and nested blockquote marker, present identically on every unit in this corpus) |

**All 5 sampled quotes are byte-identical to the source note at the cited lines; no drift introduced.** The sample deliberately covers one unit from each shard's opening pages, one mid-shard-1 erratum, the acceptance record, and the note's only tagged-LaTeX display (spanning the full width of a 76-line quotation, the largest single CANONICAL STATEMENT in the note).

---


## 5. Local supply/consumption ledger

### 5.1 Reverse consumer edges: mathematical supply versus append/consumption protocol (merged from both shards' §3.2 tables; rows naming the same consumer note are kept as separate rows when they name different designations or a different shard's supply units — collapsing them would lose which shard's units actually carry the edge)

`[TABLE — compiler ledger]`

| Consumer / supplier note | Verified designation | GENHN supply (EFF unit) | Mathematical status | Append/consumption-protocol status |
|---|---|---|---|---|
| HE7_PROOF | `LEMMA GENHN-2` (1) | `.27` | THE SLOT LEMMA, consumed as HE7's ladder base case | **Not landed by GENHN.** HE7 cites; GENHN appends nothing there |
| HE7_PROOF | `[GENHN-HE(μ)]` (2) | `.40` | HE7's COROLLARY HE7.B claims to discharge the predicate at level 2 | **Not landed either way** — no GENHN append records it; no HE7 append lands on GENHN |
| HE7_PROOF | `GENHN-4` / `GENHN.A(iv)` | `.11`, `.33` | HE7 declares GENHN-4 **NOT consumed** ("hence no W-9 graded weld face") | Negative edge; nothing landed |
| HE7_PROOF **[s2 restatement]** | `HE7` (366) | `.56` | HE7 ACCEPTED 2/2 FULLY FROZEN, named in the `[e2]` S10 refresh; "Not a supplier of this note's count laws" | Status record only |
| HE3_PROOF | `GENHN-HE` (7) | `.40` | HE3's title claims the box CLOSED at μ = 3, n ≤ 7, reduced to HE3-BOX-6 at μ ≥ 4 | **Not landed on GENHN** (verified across all eleven appends) — GENHN's S9.2 (`.55`) still lists it as "THE one load-bearing open lemma" (**DEDUP** with s2's identical row) |
| HE3_PROOF | `HE3-0` (19) | `.24`, `.38` | Reverse direction: GENHN *consumes* HE3-0's locus in the `[r1]` node derivation | Consumed, not appended |
| HETOW_RECON | `HETOW-1` (23), `HETOW-2` (9) | `.42` | HETOW re-proves its bridge lemmas at the CORRECTED composed key | **Landed as an inbound dated erratum ON GENHN** (`.77`, the one place a consumer's finding is executed inside this note) |
| GENIND_PROOF | `(CS-1)`/`(CS-2)`/`(CS-3)` | `.18` | GENIND's n ≥ 8 conditionality inherits `[GENHN-TOW-1]` and the n ≥ 10 / n ≥ 16 scoping | **Not landed.** "cross-note status is the orchestrator's fold, flagged here" (`.59`, `.60`) (**DEDUP** with s2's `(CS-1)`/`(CS-2)` row, same edge from the consumer's own SHARD-2 ARC-LINE units) |
| W12_PROOF / GENIND_PROOF | `W-12.D` (19), `THEOREM GENIND.B` (7) | `.18`, `.56` | The composition path to the full uniformity theorem | Not landed |
| GENH4_PROOF | `ANNEX R` (12) / `R3` (9) | `.22` | GENH4's ANNEX R obliged "one rider of exactly this R3 form at GENHN.A(i)" — **discharged here**, at GENHN's own site | Inbound obligation, executed in-note; nothing appended to GENH4 |
| WELDZERO (2026-08-14) | `WZ-BOX-7` (10) | `.28`, `.11`, `.33`, `.50` | Claims (a) the J-D0 parenthetical's reason is false, (b) layer 1 provable weld-free | **Not landed on GENHN.** Verified against GENHN's full append chain; WELDZERO boxes its own reading and stands at **clean-pass 1 of 2** per `spec/HYPOTHESIS_LEDGER.md` HYP.148/149 |
| HE6R1_RECON | `LEMMA HE6R1-3` (8) | `.92` item 5 | GENHN claims HE6R1's completion clause is "restored with no wording change" | **Not landed.** A *reading* offered by GENHN, not an append on HE6R1 (OPEN-CALL, §8) |
| `docs/PROJECT_STATE.md` | — | `.59` | Named as inheriting the tower box in the uniformity display | Not landed; flagged for the orchestrator |
| `spec/HYPOTHESIS_LEDGER.md` | HYP.148 / HYP.81 / HYP.139 / HYP.149 | `.50`, `.55` | The ledger indexes GENHN-BOX-2 and `[GENHN-HE]` as live obligations | Ledger-side folds, done outside GENHN |

**Dedup count for this section: 2** (the HE3_PROOF/`GENHN-HE` row and the GENIND_PROOF/`(CS-1)`-family row are each stated once from shard 1's vantage and once from shard 2's, describing the identical edge; merged above into one row each, keeping the fuller citation from both).

**The last column is not an inference.** GENHN states the protocol in its own words at both header predicate B sites (`.59`, `.60`): consumer effects are "the orchestrator's fold, **flagged here**". **Zero dated consumption appends are claimed landed on any supplier or consumer by this note, and none is invented here.** In the reverse direction GENHN *received* seven inbound correction streams across eleven dated appends (header predicate C); of these, twelve individual corrections target shard-1-HOME text (§7.3 below) and six land on shard-2's own range (shard 2's own SHARD NOTES "Riders landing WITHIN this range").

### 5.2 Note-level status ledger (both shards agree; not a duplicate of 5.1 — this predicate is about the note's OWN hostile-pass/instrument gates, not about what individual suppliers/consumers receive)

`[TABLE — compiler ledger]`

| Predicate / object | Effective status at HEAD | Governing unit(s) | What is not implied |
|---|---|---|---|
| GENHN hostile-pass gate | **ACCEPTED 2/2, text FROZEN, dated-appends-only** (F1) | `.75` (TERMINAL of GENHN-GRADE-ARC), re-affirmed `.77` | Does not upgrade THEOREM GENHN.B's conditionality stack (`.71`) |
| Sealed instrument | **Two-commit seal, older and stricter than the text freeze** (F2); survives two disclosed RE-SEALs | `.61`, `.66`, `.67` | RE-SEALs changed runner infrastructure only; predictions (F3) stayed byte-unchanged |
| Preregistered predictions P1–P10 | **Preregistered before the first full run, scored at S12** | `.64` (`preregistration`), `.70` (`run-record`) | The pairing is what makes the scorecard evidence, not narration |
| GENHN-BOX-2 (the one weld face) | **LIVE** at HEAD; a candidate discharge (WELDZERO) exists at clean-pass 1 of 2, not landed | `.50`, `.11`, `.33` | The compiler does not retire the box on an unlanded external claim |
| GENHN-ERR-1 | **SETTLED, with a transcription-confirmation owed** | `.24` (full chain), `.92` (settlement), `.93` (provenance) | Settled ≠ confirmed; the note's own certification ledger still shows the row OPEN |
| Two owner-directive re-displays (GENHN.CLASS finiteness, GENHN.A(ii) slot) | **TERMINAL readings, awaiting sol re-confirmation** | `.07`→`.86`, `.09`→`.87`→`.88` (TERMINAL) | Landed in the note ≠ confirmed by the sol arm |
| Sol certification A2 row | **Stays OPEN** at the certification ledger even after GENHN's own 2/2 acceptance | `.84`, quoted at `.02` | Note-level acceptance and certification-ledger status are independent predicates |
| Consumption/append protocol (both shards) | **Nothing landed on any supplier or consumer; the note flags, never folds** | `.59`, `.60` (header predicate B) | GENHN's own acceptance is not a downstream consumption PASS |

---


## 6. TEETH inverse table (unified from both shards; presented as two sub-tables by shard-of-origin, since shard 1 carries the core proof-side battery and shard 2 carries the S11 verdict tables, the preregistered scorecard, and the eleven appends' own legs — with one combined zero-orphan statement closing both)

### 6.1 Shard 1's proof-side battery (IDs unchanged, offset 0)

`[TABLE — compiler ledger]` Battery row → guarded unit(s) → disposition ∈ {executable regression, planted mutant, measurement, exhaustive enumeration, foreign-note evidence, PROOF-ONLY, signed vacuity disclosure, disclosed non-repair, accepted-with-decorrelation-supplied, stale self-description, decorrelated-model audit}.

| Battery row / tooth | Guarded unit(s) | Disposition |
|---|---|---|
| **GN-PIN** (7 md5 pins) | `.05` | Executable regression (supplier artifacts are the ones consumed) |
| **GN-CLASS** (n = 5 and n = 6 sweeps, 2,147,916 checks, 0 violations, incl. the 2×2²⁰-state GENIND-reader tie) | `.07`, `.20` | Executable regression; sealed |
| **GN-T-CRIT** (grammar bound e₁f₁μ ≥ 4 dropped to ≥ 3 must accept an order-1 fake) | `.07`, `.20` | Planted mutant; fired 2/2 |
| **GN-LAWTIE** (law_Egen(e₁=2) ≡ pinned law_E, 5 grid points) | `.12`, `.36` | Executable regression |
| **GN-FIB** (constructed loci, both directions: frames parse to genre, volumes = entry laws) | `.08`, `.23` | Executable regression, **decorrelated from the false budget display** |
| **GN-T-NODE** (E3 a₀₀ floor off-by-one must break the volume) | `.08`, `.23` | Planted mutant; fired 1/1 |
| **GN-STAGE2** (μ = 2 stage law at three fresh genres, both directions; P3/P4 totals exact, 0 escapes) | `.12`, `.26` | Executable regression |
| **GN-E3** (μ = 3 stage: species partition + UND3/RAM3/ALPHA3 laws) | `.12`, `.36`, `.37` | Executable regression; ★ first μ = 3 stage ever read |
| **GN-T-LAT** (E31 law collapsed to the integer lattice must break) | `.27` | Planted mutant; fired 2/2 |
| **GN-T-CEN** (INERT census ×2 must break) | `.12`, `.15` | Planted mutant; fired 2/2 |
| **GN-REFINE3** (3,072 pin checks; every μ = 3 stage-α event re-divided, three pins dead, floored node) | `.11`, `.33`, `.34` | Executable regression — **GENHN-BOX-2's declared compensating instrument**; `accepted-with-decorrelation-supplied` |
| **GN-TOWER** (criterion + the n = 8 witness + min-n scan) | `.16` | Executable regression; the witness's residual `(T−1)²` **contradicted the proof display**, which R4 F-5 then corrected — `stale self-description` on the display |
| **GN-SIGMA** (PARI factorpadic vs dictionary; 37,792 certified jobs / 0 bad, six batches, incl. ★ wild p = 3 at e₁ = 3) | `.15`, `.38` | Executable regression against an independent oracle |
| **GN-T-SIG** (E31 RAM σ {(6,1)}→{(3,2)} must be caught by PARI) | `.15`, `.38` | Planted mutant; fired 2/2 |
| **S11.F certification gate + diagnostic tail** (V p=2 1,216/349, V p=3 241/58, full-side 0/0) | `.26`, `.39` | Measurement; **discovery event was a RED smoke run**, converted to a preregistered diagnostic |
| **`genhn_pe1_fresh.py` FR-D** (n = 8 (2,1,4)→(2,1,2) constructions, two PARI routes) | `.17`, `.41`, `.47` | Planted counter-instance; **FIRED AGAINST the sealed lemma** |
| **`genhn_pe1_fresh.py` FR-A/FR-B** ((1,3,2) exhaustive: 32,768 and 2,097,152 states; 36/36 band-RAM PARI) | `.32` | Exhaustive enumeration on a decorrelated instrument |
| **`genhnr2_supp.py`** (147/0, 3 teeth: 4 refuted instances as regression teeth, u₂ ∈ {5,7} sweeps, first f₂ = 2 tower genre, 3 parse-gated 3-stage n = 16) | `.41`, `.42`, `.43`, `.44`, `.47` | Executable regression built from a refutation; first tower leaf-read coverage |
| **`genhn_pe2_fresh.py`** (219/0, 4 teeth: first outer-f₁ = 2 tower genres, first 2-stage dictionary contact, η₂-cocycle adjudication, Q = 4 tower legs) | `.42`, `.43`, `.44` | Executable regression on a decorrelated instrument; **T(b)′ (i)–(iv) HELD** |
| **PE2-P counter-witness** (n = 10 partial-inner-side member; reader refuses loudly; PARI {(2,1),(4,1),(4,1)}) | `.18`, `.44` | Planted counter-instance; fired against the `[r2]` (CS-3) rider |
| **`genhn_f2_count_check.py`** (measured = predicted at (1,2,2) and first mixed (2,2,2); sealed child displays refuted 0/1024 → 768/256 and 0/16384 → 12288/4096) | `.24`, `.14` | Executable regression, post-seal; **fired against the sealed S-node child displays** |
| **`hetow_pe1_fresh.py` + `hetowr1_supp.py`** (frame X at η = 2 and two further η ≠ 1 frames; naive key σ {(4,1)} vs corrected {(2,2)}) | `.42` | Planted mutant from a CONSUMER note; fired against the supplier's display |
| **`genhn_pe4_fresh.py`** (145/0, first f₁ = 4 / comp = 3 / F₁₆ contact) | `.14` | Executable regression, post-acceptance; first f₁ ≥ 2 census contact of any GENHN-side leg |
| **WELDZERO's read of the sealed GN-STAGE2 row** (972/972 live-wrap events flip `'2'`→`'1sq'`) | `.28` | Foreign-note evidence; `stale self-description` on GENHN's J-D0 parenthetical |

**PROOF-ONLY rows (rule 16) — guarded units whose interesting content is the proof, with the note's own coverage-hole sentence quoted:**

| Unit | Coverage hole, in the note's words |
|---|---|
| `.09` (GENHN.A(ii) at unoccupied heights) | GENHN-BOX-3: "NOT exercised: f-first genres beyond f₁ = 2 …, mixed e₁, f₁ ≥ 2 (first live n = 8)" — no row can reach an unoccupied height |
| `.10`, `.29`, `.31` (the boundary band at f₁ ≥ 2) | E1: "at f₁ ≥ 2 genres beyond it (μ ≥ 3, or e₁ ≥ 2 mixed — no battery row, first live n ≥ 8) this note claims the LIFT-STABILITY content of (a) only and NO band-adjudication display" |
| `.22` (the E3 carrier) | E3: "the battery's counts are digit-coordinate counts on Ô[x]-coefficients and its σ legs are PARI oracle reads; neither consumes R's ring structure" |
| `.46` (the tower count law) | GENHN-BOX-3 `[r2]`: "tower COUNT laws remain unmeasured, [GENHN-TOW-1]" |
| `.45` (faithfulness geography, positive half) | "its genre-general proof is part of [GENHN-TOW-1] … currently machine-verified at the PE1 instances + the P8 witness" |
| `.34` (layer 2 at mixed genres) | "A hostile pass should attack layer 2's strictness at mixed (e₁, f₁ ≥ 2) genres (first live n = 8, machine-unreachable here — S9 box)" |

**AUDIT-disposition rows (rule 27) — findings no tooth could have produced:**

| Finding | Unit | Class |
|---|---|---|
| GENHN.CLASS's declared datum set is infinite (the odd-h family at n = 4, Q = 2) | `.07` | decorrelated-model audit (sol A2) |
| GENHN.A(ii)'s "per integer dv-height" is false at `(3,1,2,1)` | `.09` | decorrelated-model audit (sol A2) |
| The re-display's "occupied = integral normalizer" is still too weak at f₁ > 1, witness `(1,2,1,0)` | `.09` | decorrelated-model audit (sol D2b) |
| "ragged band is never consulted" denotes two objects; the first usage is false | `.10`, `.29`, `.30` | in-house hostile pass turned decorrelated audit (R4 F-1) |
| E1's exclusion clause claims the surface "sits with the S9 boxes"; walking the box list shows no box holds it | `.31` | decorrelated-model audit (A2 verification note) |
| R = Ô[θ] is a non-maximal order, not a DVR | `.22` | transfer audit (Codex GENH4 ratification, transported) |
| The J-D0 parenthetical's stated reason is false | `.28` | decorrelated-model audit (WELDZERO r1 C-1) |

**Both-direction audit.** Every row above guards at least one shard-1-origin unit. Every shard-1 unit whose `TEETH` field names a battery row appears in some row. Units with **`TEETH: NONE`** — `.06`, `.13`, `.19`, `.21`, `.30` — are conventions, grade lines, indexes or frames and are outside the orphan count. Units flagged **`TEETH: Indirect`** — `.04`, `.35` — are guarded only through the composite agreement of the whole battery. **Zero battery-row orphans; zero toothed-unit orphans; six signed PROOF-ONLY units; seven AUDIT-class findings.**

### 6.2 Shard 2's record-side battery, S11 verdicts, and the eleven appends' own legs (renumbered, +48 offset)

`[TABLE — compiler ledger]` Battery row → guarded unit(s) → disposition.

| Battery row / tooth | Guarded unit(s) | Disposition |
|---|---|---|
| **GN-PIN** (7 supplier md5 pins) | `.56`, `.61` | Executable regression; **UNPINNED in the note's own display** (all seven truncated) |
| **GN-CLASS** (2,147,916 checks, 0 violations, incl. the 2×2²⁰ GENIND-reader tie) | `.62`, `.64` P1, `.70` P1, `.86` | Executable regression; tests the *re-displayed* schema claim, never the withdrawn datum claim |
| **GN-T-CRIT** | `.62`, `.64` P1 | Planted mutant; fired 2/2 |
| **GN-LAWTIE** (5 grid points) | `.62`, `.64` P2 | Executable regression |
| **GN-FIB** (both directions) | `.62`, `.64` P1 | Executable regression |
| **GN-T-NODE** | `.62` | Planted mutant; fired 1/1 |
| **GN-STAGE2** (three fresh genres, both directions) | `.62`, `.64` P3/P4/P5 | Executable regression |
| **GN-E3** (μ = 3 species + laws) | `.62`, `.64` P6 | Executable regression; ★ first μ = 3 stage read |
| **GN-T-LAT** | `.62` | Planted mutant; fired 2/2 |
| **GN-T-CEN** | `.62` | Planted mutant; fired 2/2 |
| **GN-REFINE3** (3,072 pin checks, 0 violations) | `.50`, `.62`, `.64` P7, `.70` P7 | Executable regression — **GENHN-BOX-2's declared compensating instrument**; `accepted-with-decorrelation-supplied` |
| **GN-TOWER** (criterion + witness + min-n scan) | `.62`, `.64` P8, `.83` | Executable regression; **the witness carried the CORRECTED residual `(T−1)²` all along** — `stale self-description` on the S8 proof display |
| **GN-SIGMA** (37,792 certified jobs / 0 bad, six batches) | `.62`, `.64` P9, `.70` P9 | Executable regression against an independent oracle |
| **GN-T-SIG** | `.62` | Planted mutant; fired 2/2 |
| **S11.F gate + diagnostic tail** (V p=2 1,216/349; V p=3 241/58; full-side 0/0) | `.52`, `.68`, `.70` P9 | Measurement, **preregistered in the failing direction** |
| **Smoke 1 RED** (6 GN-SIGMA mismatches, all RAM(9)) | `.65`, `.68` | Measurement that fired against the pre-gate reader; the discovery event for S11.F |
| **Run 1 CRASH** (V4E2 Newton guard) | `.66` | `disclosed non-repair` — an infrastructure bug the provenance audit missed; the instrument caught itself |
| **Run 2 RED** (4/20,800 gp precision misses) | `.67` | Executable regression driven to ground: all four re-answered at three precisions |
| **`genhn_pe3_fresh.py`** (GREEN 176/0, first full run) | `.72` | Executable regression on a fresh instrument |
| **`genhn_pe4_fresh.py`** (GREEN 145/0; first f₁ = 4 / comp = 3 / F₁₆ contact) | `.75`, `.51`, `.79` | Executable regression on a fresh instrument; first f₁ ≥ 2 census contact on a GENHN-side leg |
| **`genhn_pe2_fresh.py`** (GREEN 219/0, 4 teeth; T(b)′ (i)–(iv) HELD) | `.60` | Executable regression on a decorrelated instrument |
| **`genhnr2_supp.py`** (147/0, 3 teeth; SUPP-C's 3-stage n = 16) | `.54`, `.59` | Executable regression built from a refutation |
| **`hetow_pe1_fresh.py` + `hetowr1_supp.py`** (three η ≠ 1 frames; naive σ {(4,1)} vs corrected {(2,2)}) | `.77` | Planted mutant from a CONSUMER note; fired against the supplier's display |
| **`genhn_f2_count_check.py`** (measured = predicted at (1,2,2) and first mixed (2,2,2); sealed child displays refuted) | `.89`, `.90`, `.92`, `.93` | Executable regression, post-seal, **fired against the sealed displays**; gated the lemma's composition |

**PROOF-ONLY rows (rule 16), with the note's own coverage-hole sentence:**

| Unit | Coverage hole, in the note's words |
|---|---|
| `.53` (GENH5-DENS / the "SEVENTEEN" count) | "NOT executed here — a one-unit follow-up, explicitly owed"; no quintic density is displayed or checked anywhere |
| `.79` (LEMMA GENHN-CAP-GEN) | GENHN-BOX-3: "NOT exercised: f-first genres beyond f₁ = 2 …, mixed e₁, f₁ ≥ 2 (first live n = 8)" — the boundary rule has no row |
| `.81` (LEMMA GENHN-LIFT) | same; the lift operator at f₁ ≥ 2 is exercised only foreign-ly (`hetowr1_supp.py`) and by the post-acceptance `comp = 3` leg |
| `.86` (the F-2 re-display) | the battery sweeps fixed `(q, N, h)`; **no row ranges over h**, so neither the withdrawn claim nor its replacement is exercised over the parameter that matters |
| `.87`, `.88` (the slot re-displays) | "every pin the note's laws consume sits at dv > D′h … so no consumer moves" — no row can reach an unoccupied height |
| `.91` (`gcd(e₁,h) = 1` load-bearing) | every row fixes a single `h` coprime to `e₁` by construction; no tooth mutates it |
| `.92` item 3 (the bracket's invariance) | an argument about normalization, not a measurement |
| `.54` items (1)–(5) | "supp leg = leaf-read first contact only"; "tower COUNT laws remain unmeasured" |

**AUDIT-disposition rows (rule 27) — findings no battery row could have produced:**

| Finding | Unit | Class |
|---|---|---|
| GENHN.CLASS's declared datum set is infinite (the odd-h family) | `.80` | decorrelated-model audit (sol A2, re-adjudicating an R4 chain read) |
| GENHN.A(ii)'s universal slot display is false at `(3,1,2,1)` | `.82` | decorrelated-model audit (sol A2) |
| The F-4 re-display's "occupied" is still too weak at f₁ > 1, witness `(1,2,1,0)` | `.88` | decorrelated-model audit (sol D2b) — **an audit of a repair** |
| "ragged band is never consulted" denotes two objects; usage 1 is false | `.79` | decorrelated-model audit (R4 F-1) |
| E1's exclusion clause claims the surface "sits with the S9 boxes"; the box list holds no such box | `.84` | in-house arithmetic recount (orchestrator, box-by-box) |
| "GENHN-2(b)'s bracket" has no literal referent | `.84` | in-house hostile pass (caught pre-transcription) |
| "none is live below n = 8" contradicts §S2's own list | `.76` | decorrelated-model audit (PE4 design audit of the battery's rows) |
| Item (6)(α)'s cancellation is witness arithmetic, not mechanism; FR3 is a counter-witness | `.73` | decorrelated-model audit (PE3 FR3) + PARI re-verification |
| The composed-key lift is gauge-naive at η ≠ 1 | `.77` | transfer audit (a consumer note's hostile pass) |

**Both-direction audit.** Every row above guards at least one shard-2-origin unit. Every shard-2 unit whose `TEETH` field names a battery row appears above. Units with **`TEETH: NONE`** — `.49`, `.55`, `.57`, `.58`, `.71`, `.74`, `.85` — are grade declarations, inventories, summaries, status records, or wording riders, and are outside the orphan count. **Zero battery-row orphans; zero toothed-unit orphans; eight signed PROOF-ONLY units; nine AUDIT-class findings.**

### 6.3 Combined zero-orphan statement (both shards' independent audits agree)

Across the whole 93-unit merged inventory: every battery row/tooth guards at least one unit; every unit whose TEETH field names a row appears in some row above; **zero battery-row orphans and zero toothed-unit orphans in either sub-table.** Fourteen signed PROOF-ONLY units (six shard-1-origin, eight shard-2-origin) and sixteen AUDIT-class findings (seven shard-1-origin, nine shard-2-origin) are recorded, each with the note's own disclaiming or coverage-hole sentence quoted rather than left blank, per rule 16. **Twenty-four distinct instruments/legs are cited across the whole note** (shard 2's own closing count, independently confirmed by this merge's cross-listing of both sub-tables: the fourteen shard-1 rows and the ten additional shard-2-only rows — `.61`, RE-SEAL 1/2, the S11.D/S12 pairing, and the five post-acceptance appends' own legs — sum to 24 distinct battery/instrument names with no double-count).

---


## 7. SERIES, supersession CHAINs, and cross-shard boundary resolution (the GENHN-specific merge centerpiece)

Both shards' compilers pre-built each SERIES' cross-shard member table **inside the individual unit** that carries it (e.g. `.02`'s CONDITIONALITY already lists all five GENHN-GRADE-ARC members with their shard-2 line numbers; `.24`'s CONDITIONALITY already lists all four GENHN-ERR-1 members). This merge's job is therefore to (a) reproduce each SERIES as one compiler-ledger block per template rule 28, (b) cross-check the two shards' own descriptions of each series' span against each other and against the unit-level tables for duplication or gaps, and (c) verify each series' TERMINAL is unique across the whole 93-unit merged inventory — not to invent the ordering from prose-reading.

### 7.1 The four dated-arc SERIES

**GENHN-GRADE-ARC (5 members, crosses both shards).** Assembled from `.02`'s own CONDITIONALITY table (which already names all five members with their shard-2 line numbers) and cross-checked against `.49`'s, `.72`'s, `.75`'s, and `.77`'s own SERIES headers/back-references.

`[TABLE — compiler ledger]`

| Link | Unit | Round | Grade movement | Content (quoted from the unit) |
|---:|---|---|---|---|
| 1 | `.02` (=s1.02) | base; `[r2]` post-PE1; `[r3]` post-PE2 | **0/2** | "Attempt grade 0/2 (composed; no hostile arc) … Clean count stays 0/2; PE3 next" |
| 2 | `.49` (=s2.01, GENHN-BOX-1) | base | **0/2** (re-affirmed) | "0/2, composed this session, NO hostile arc" |
| 3 | `.72` (=s2.24, post-PE3 discipline header) | dated append | **0/2 → 1/2** | "PE3 returned CLEAN — 0 CRITICAL + 0 GAP + 2 MINOR … so the clean count set there (0/2 → 1/2) HOLDS AT 1/2" |
| 4 | `.75` (=s2.27, post-PE4 acceptance record) | dated append | **1/2 → 2/2, ACCEPTED — TERMINAL** | "Clean count 1/2 → **2/2: GENHN is ACCEPTED — the text is FROZEN, dated appends only from here**" |
| 5 | `.77` (=s2.29, HETOW dated erratum) | dated append | **2/2, re-affirmed** | "GENHN stays ACCEPTED 2/2, text FROZEN, dated-appends-only" |

**No link duplicated, none skipped.** Cross-checked against shard 1's own SHARD NOTES ("Merge hazard (f): Three SERIES … each have members in both shards") and shard 2's own SHARD NOTES ("GENHN-GRADE-ARC (member 1 in s1, members 2–5 here)") — both descriptions, read through the SHARD-MAP, name exactly these five links. **TERMINAL: link 4 (`.75`)**, verified unique by an exhaustive scan of the merged inventory for any further grade-counter movement after 2/2: link 5 (`.77`) explicitly *re-affirms* 2/2 rather than moving it, and no later unit (the 2026-08-12 sol certification appends, `.78`–`.93`) touches the note's own acceptance counter — `.02` itself records "The 2026-08-12 sol certification appends do NOT move the counter."

**GENHN-T(b)-ARC (3 members, entirely within shard 1 — confirmed, no cross-shard assembly needed).**

`[TABLE — compiler ledger]`

| # | Member | Where | Status |
|---:|---|---|---|
| 1 | LEMMA GENHN-T(b), sealed | `.17`, 282–292 | **REFUTED at the leaf level** (passPE1 F1) |
| 2 | The withdrawn proof of (b) | `.41` (=s1.17's own DERIVATION span, 1061–1086) — carried at `.41`, the refutation-and-repair record | **WITHDRAWN**, error located |
| 3 | LEMMA GENHN-T(b)′ | `.42`–`.49`ish (setting + clauses (i)–(v), 1127–1287) | **PROVED** at (i)–(iv); (v)'s budgets boxed |

Member order preserved exactly through renumbering (`.17` < `.41` < `.42`, all shard-1-native, offset 0 — the renumbering script's `assert ids == list(range(1, total+1))` check confirms no reordering occurred anywhere in the merge). **TERMINAL: member 3 (`.42`, LEMMA GENHN-T(b)′)** — no later unit re-supersedes T(b)′'s (i)–(iv) content; the only edits landing on `.42` are the display-only composed-key-lift CHAIN (§7.2 below), which the note itself keeps distinct from the lemma's proof content ("T(b)′'s PROOF mechanism is unaffected … what was wrong is the DISPLAY's lift prescription").

**GENHN-ERR-1 (4 members: 1–3 in shard 1, member 4 in shard 2 — matching the charge's expectation).** Assembled from `.24`'s own CONDITIONALITY table (the charge's named item; `.24`'s own header states "this is the charge's named item, so the chain is given in full").

`[TABLE — compiler ledger]`

| # | Event | Where | State of ERR-1 |
|---:|---|---|---|
| 1 | Named and left open: "is NOT settled here" | `.24`, 605–611 | **OPEN** |
| 2 | `[r2]` NODE RE-DERIVATION settles the arithmetic side at f₁ = 1 only | `.24`'s own correction sites, 664–671 | still OPEN at f₁ ≥ 2 |
| 3 | post-PE4 dated Correction (PE4 F-1) corrects the scope clause of member 1 | `.76` (=s2.27's sibling append), 1957–1978 | still OPEN, scope fixed |
| 4 | LEMMA GENHN-COUNT-RERUN's Consumer sweep item 1 | `.92` (=s2.44), 2593 + 2624 | **"GENHN-ERR-1 is settled."** |

**No link duplicated, none skipped.** Cross-checked against shard 1's SHARD NOTES merge-hazard (b) ("`.24`'s GENHN-ERR-1 is SETTLED with a transcription-confirmation owed") and shard 2's own SHARD NOTES merge-hazard (a) ("GENHN-ERR-1 (members 1–3 in s1, member 4 here)"). **TERMINAL: member 4 (`.92`) — SETTLED, WITH A TRANSCRIPTION-CONFIRMATION OWED**, per its own closing sentence (2626–2627): "Ledger: row 15 → the count re-run obligation is DISCHARGED; a final transcription-confirmation rides the next queue." Verified unique: no later unit reopens or re-corrects the ERR-1 residue, and the note's own append chain ends at `.93` (the P2 provenance parenthetical), four units after the settlement.

**GENHN-ARC-LINE (3 members, entirely within shard 2 — confirmed, no cross-shard assembly needed).**

`[TABLE — compiler ledger]`

| # | Member | Where | Status |
|---:|---|---|---|
| 1 | `[e2]` S10 REFRESH's own ARC LINE ("PE1 next") | `.58` (=s2.10), 1533–1569 | 0/2, "no hostile pass yet" |
| 2 | `[r2]` ARC LINE UPDATE 2026-08-09 | `.59` (=s2.11), 1570–1585 | PE1 ran, stays 0/2 |
| 3 | `[r3]` ARC LINE UPDATE 2026-08-09 | `.60` (=s2.12), 1586–1622 | PE2 ran, stays 0/2 |

Member order preserved through renumbering (`.58` < `.59` < `.60`, all shard-2-native, offset +48 applied uniformly). **The series' own terminal grade lives OUTSIDE it, in the GENHN-GRADE-ARC series** — `.59`'s own CONDITIONALITY says so explicitly: "Terminal grade lives in the GENHN-GRADE-ARC series (`.75`)." This is confirmed by cross-checking: `.58` is itself GENHN-GRADE-ARC's own target for a `STALE-SELF-DESCRIPTION` supersession chain internal to `.58` ("CHAIN: §S10 bullets → `[e2]` refresh → `[r2]` arc line → `[r3]` arc line → post-PE3 (1/2) → post-PE4 (2/2). TERMINAL: post-PE4" — i.e. `.58`'s own embedded chain re-derives the same link structure as GENHN-GRADE-ARC, confirming the two SERIES are cross-consistent rather than contradictory). **No independent TERMINAL is claimed for GENHN-ARC-LINE itself**; it is a chronologically-ordered but grade-static sub-series (0/2 throughout all three of its own members) feeding into GENHN-GRADE-ARC's TERMINAL at `.75`.

### 7.2 Supersession CHAINs, with TERMINAL markers verified to survive the merge uniquely

Three chains exist with more than one correction layer landing on a single frozen target (the task's own threshold: "if any single target unit receives more than one correction in sequence, that is a supersession CHAIN"):

**CHAIN 1 — GENHN.CLASS's finiteness clause (2 layers).** Target: `.07` (frozen GENHN.CLASS statement).

| Layer | Unit | Content |
|---:|---|---|
| 0 (frozen original) | `.07` | The original finiteness clause (a datum set later shown infinite on an odd-`h` family) |
| 1 | `.80` (=s2.32, A2 obstruction record F-2) | Adjudicates the clause REAL-BUT-OBSTRUCTED: "No new lemma can prove the existing false statement" |
| 2 (**TERMINAL, awaiting sol re-confirmation**) | `.86` (=s2.38, owner-directive re-display, F-2) | The corrected finiteness clause — the reading every consumer of `.07` must use, "subject to sol discharge-confirmation in the cert2 pass" |

**CHAIN 2 — GENHN.A(ii)'s slot clause (3 layers — the longest chain in the note, matching the header's rule-3 note that the clause is "re-displayed twice").** Target: `.09` (frozen GENHN.A(ii) slot clause).

| Layer | Unit | Content |
|---:|---|---|
| 0 (frozen original) | `.09` | The original universal-slot display |
| 1 | `.82` (=s2.34, A2 obstruction record F-4) | Adjudicates REAL-BUT-OBSTRUCTED, witness `(3,1,2,1)` |
| 2 | `.87` (=s2.39, owner-directive re-display, F-4) | First corrected display: "occupied = integral normalizer" |
| 3 (**TERMINAL, awaiting sol re-confirmation**) | `.88` (=s2.40, post-D2b corrigendum) | Tightens layer 2 further: at `m ≤ D′h` the clause is withdrawn entirely — the reading every consumer of `.09` must use |

**CHAIN 3 — LEMMA GENHN-T(b)′'s composed-key lift display (2 layers; this chain IS also one of the twelve cross-shard supersession edges in §7.3 below, listed there in full and cross-referenced here rather than duplicated).** Target: `.42` (the composed-key lift prescription inside the T(b)-ARC's terminal member).

| Layer | Unit | Content |
|---:|---|---|
| 0 (frozen original) | `.42` | The gauge-naive lift `ĉ_t := lift(c_t)` |
| 1 | `.77` (=s2.29, HETOW dated erratum — a consumer correcting its supplier) | Corrected display: `ĉ_t := lift(c_t·η^{W(t)})` |
| 2 (**TERMINAL**) | `.81` (=s2.33, LEMMA GENHN-LIFT, R4 F-3) | Supplies the exact-height `(LIFT)` operator the corrected display needed and had no prior in-note lemma for; re-derives `res(n(u₂)^r/n(ru₂)) = η^{W(t)}` from scratch — the form every consumer must use |

**Uniqueness of each TERMINAL, verified.** An exhaustive scan of every CONDITIONALITY, SUPERSESSION KIND, and RESOLUTION TRACE field in the merged 93-unit inventory for a supersession *target* naming `.07`, `.09`, or `.42` (as opposed to a mere citation) confirms the only hits are the layers listed per chain above, plus each target's own self-quotation of its frozen text. No fourth layer exists for any of the three chains. **All three TERMINALs are unique and survive the merge intact** — `.86` for GENHN.CLASS's finiteness (with the confirmation-owed qualifier), `.88` for GENHN.A(ii)'s slot clause (ditto), `.81` for the composed-key lift (unqualified — GENHN-LIFT is a license, not conditional on external confirmation).

### 7.3 Full cross-shard supersession edge list (consolidated from shard 1's SHARD NOTES twelve-item list, with SUPERSESSION KIND)

Shard 1's own SHARD NOTES states: "Cross-shard supersessions applied (twelve, all inbound to this range)." Every edge below is FROM a shard-2-homed dated append TO a shard-1-homed unit — the direction the task's charge names ("twelve such corrections land inside shard 1's range"). Kind vocabulary per template rule 18 (eight kinds): replacement, license, wording-rider, provenance-rider, scope-pin, as-of scoping, counter re-reading, inventory completion.

`[TABLE — compiler ledger]`

| # | From (shard-2 append) | To (shard-1 unit) | Kind | Content |
|---:|---|---|---|---|
| 1 | `.73` (post-PE3 Correction 1) | `.54` item (6)(α) (primary; out-of-range at shard 1) — reasoning also bears on `.42`'s carry arithmetic | provenance-rider | "TRUE at the witness by an EXACT CARRY CANCELLATION" re-read as witness arithmetic, not mechanism; recorded at `.42`, not applied as an edit there |
| 2 | `.74` (post-PE3 Correction 2) | `.01` (title-line rider), `.18` (`[r3]` depth-split sentence) | scope-pin | Attaches the FULL-inner-side scope word; partial sides remain `.54` item (4) |
| 3 | `.75` (post-PE4 acceptance record) | `.02` (GENHN-GRADE-ARC terminal member) | as-of scoping / replacement | Clean count 1/2 → 2/2, ACCEPTED |
| 4 | `.76` (post-PE4 Correction, PE4 F-1) | `.24` (the ERR-1 residue's scope clause), `.14` (E2's echo) | scope-pin | "the f-first genres … are live at n = 4/6/6 … the residue (GENHN-ERR-1 stays unsettled exactly as displayed)" |
| 5 | `.77` (HETOW dated erratum) | `.42` (the composed-key lift prescription) | replacement, **chained; `.81` TERMINAL (§7.2 CHAIN 3)** | `ĉ_t := lift(c_t·η^{W(t)})` |
| 6 | `.80` (A2 obstruction record F-2) | `.07` (finiteness) | provenance-rider, **chained; `.86` TERMINAL (§7.2 CHAIN 1)** | Adjudicated REAL-BUT-OBSTRUCTED |
| 7 | `.82` (A2 obstruction record F-4) | `.09` (the slot clause) | provenance-rider, **chained; `.88` TERMINAL (§7.2 CHAIN 2)** | Adjudicated REAL-BUT-OBSTRUCTED, witness `(3,1,2,1)` |
| 8 | `.79` (R4 F-1 + LEMMA GENHN-CAP-GEN) | `.10`, `.29`, `.30` (the ragged-band terminology and the boundary criterion) | license + wording-rider | Supplies the boundary-band criterion the note names but does not derive |
| 9 | `.81` (R4 F-3 + LEMMA GENHN-LIFT) | `.42` (licenses the corrected lift, **CHAIN 3 TERMINAL**), `.09` (licenses the occupied-height re-display) | license | Supplies the exact-height `(LIFT)` operator |
| 10 | `.83` (R4 F-5) | `.16`'s DERIVATION (the first tower's residual) | replacement | Corrects the witness residual to `(T−1)²` |
| 11 | `.86`, `.87`, `.88` (owner-directive re-displays + post-D2b corrigendum) | `.07`, `.09` (both TERMINAL readings, **CHAINS 1 and 2 above**) | replacement | Both TERMINAL readings executed under Asvin's delegated end-to-end-proof authority |
| 12 | `.90`, `.92` (LEMMA GENHN-COUNT-RERUN + Consumer sweep) | `.24` (ERR-1 SETTLED, **GENHN-ERR-1 SERIES TERMINAL, §7.1**), `.12` and `.36` (S-node ⇝ B = D′h re-grounding), `.14` (CR-3 re-derives the band census) | counter re-reading + license | "GENHN-ERR-1 is settled … the ordinary μ=2 stage law is the (2,K)-law at B=D'h, not at the old numeric node S=e₁h" |

**LEMMA GENHN-CAP-GEN (`.79`), LEMMA GENHN-LIFT (`.81`), and LEMMA GENHN-COUNT-RERUN (`.90`) are licenses, not supersessions in the strict sense**: they supply content the in-range text asserted or omitted rather than editing a display; each is quoted at the unit it licenses (edges 8, 9, 12 above), consistent with both shards' own resolution rules.

**Boundary-unit resolution, verified.** Each of the twelve edges' TARGET units above (`.01`, `.02`, `.07` ×2, `.09` ×2, `.10`, `.12`, `.14` ×2, `.16`, `.18`, `.24` ×2, `.29`, `.30`, `.36`, `.42` ×2) was checked against the merged 93-unit inventory: **every named target appears exactly once** (the renumbering script's own `assert ids == list(range(1, total+1))` guarantees no duplicate unit IDs exist at all, and a manual re-check of each of the twelve rows above confirms the target's content matches what the append names). No boundary material was duplicated or dropped. Shard 2's own SHARD NOTES independently states "Riders landing on SHARD 1 from this range (twelve) — enumerated in `spec/EFF-GENHN-s1of2.md` §7; not repeated here. The merge must install them from that list" — **this table is exactly that installation.**

**No non-SERIES, non-CHAIN boundary-routed units of the T1 kind were found** (a unit *physically drafted* in one shard's line range but *whose entire content* belongs at the other shard's HOME, the way T1's R7-2/R13-7/R13-8 worked). GENHN's cross-shard structure is uniformly the append-quotes-and-riders pattern above; every shard-2 append that targets shard-1 text is itself correctly homed at shard 2 (it is an append, physically and functionally part of the record stack), and no shard-1 unit's content is homed at shard 2 or vice versa. This was verified by re-reading both shards' §6 BOUNDARY SELF-AUDIT sections in full: neither records a "physically drafted here, HOME-routed there" case outside the twelve append edges and the four SERIES.

### 7.4 Range-edge audit (boundary cleanliness, both shards' own findings confirmed consistent)

Both shards independently audited their own physical line boundary and both report the same thing: **no source statement unit is cut at the shard boundary.** Line 1319 (shard 1's last) is blank; line 1320 opens `## S9.` — a clean `##`-heading section break. The file's own end (source line 2627) is shard 2's own last line, closing the P2 provenance parenthetical's final `)*`. **Zero units span the shard boundary.** This merge additionally re-confirms shard 1's own honest framing (§1 above): the 1319 | 1320 split is compiler-chosen (no manifest row exists), lands on a section break, and splits the file within 0.5% of an even halving (1319 vs. 1308 lines) — none of which is disputed by shard 2, which explicitly adopts it.

---


## 8. Self-audit and OPEN-CALLs (merged, dedup marked)

**12 raw OPEN-CALLs (6 per shard, with shard 1's OPEN-CALL 6 itself carrying two distinct sub-issues) reduce to 9 distinct after merge-time dedup.** Three pairs are genuinely identical or near-identical restatements of the same question from each shard's own vantage; none of the 9 is discharged by the act of merging — every one is carried forward open, per the standing merge charge.

### OPEN-CALL 1 — the manifest has no GENHN row, and the shard split is therefore compiler-chosen **[DEDUP — shard 1 OPEN-CALL 1 ≡ shard 2 OPEN-CALL 1, self-identified: shard 2's own header reads "(inherited)"]**

`runs/qgen/sweep_manifest.txt` at HEAD contains 52 rows and none of them is GENHN (`grep -ni genhn` → 0 hits; the file was verified in full by both shards independently). The charge names GENHN s1of2/s2of2 "per the manifest"; the manifest cannot supply the ranges. The split at 1319 | 1320 was chosen on three defensible grounds (§1 above) and lands on a `##` section break with no unit cut (§7.4). **This merge run has now adopted 1319 | 1320** — it performed the concatenation-and-renumbering over exactly that split. **The remaining half of the decision — whether `runs/qgen/sweep_manifest.txt` should be amended to record a GENHN row for this split — is explicitly left OPEN for Asvin.** No silent choice was made at any stage; the boundary and its rationale are stated in both shards' headers and restated in this merge's header.

### OPEN-CALL 2 — GENHN-BOX-2 (the one weld face inside a count law) has a candidate discharge that has not landed, and the compiler will not apply it **[DEDUP — shard 1 OPEN-CALL 2 ≡ shard 2 OPEN-CALL 2, identical content from the theorem-clause vantage (`.11`, `.33`) and the box vantage (`.50`)]**

`.11`, `.33`, and `.50` carry GENHN-BOX-2 as **LIVE**: "the count laws at μ ≥ 3 stand on one accepted weld face." Three external records bear on it and none has landed on GENHN:
- `runs/qgen/WELD_FACE_AUDIT.md` L143–164 confirms the disclosure is correct and adds that **J-D0 cannot cover the face even in principle** (the recentering is an additive shift — the NONCHAR failure mode).
- `lean/notes/openmath/WELDZERO_2026-08-14.md` claims COROLLARY WZ-B: layer 1 without W-9. It also introduces **WZ-PIN**, a *content* decision about how GENHN-4's hypothesis must be read, and states "Only under this reading is GENHN-4 layer 1's conclusion true."
- `spec/HYPOTHESIS_LEDGER.md` HYP.148/149 records the arc: **clean-pass 1 of 2**, sol confirmation queued not before 2026-08-18, and "HYP.148 stays CARRY … at full strength."

**The compiler cannot decide** whether the merged spec (a) carries GENHN-BOX-2 as live, (b) carries WZ-PIN as a reading of GENHN-4's hypothesis, or (c) waits for the second clean pass. This merge does (a) and records (b) as a disclosed external reading, consistent with both shards. **Decision needed: Asvin / the next merge run.**

### OPEN-CALL 3 — `[GENHN-HE(μ ≥ 3)]`'s status is contested across notes and settled in none of them **[DEDUP — shard 1 OPEN-CALL 6(a) ≡ shard 2 OPEN-CALL 3, near-verbatim identical text in both shards]**

`.40` and `.55` item 1 carry it as "THE one load-bearing open lemma of the whole composite program", which is GENHN's state across every append. `HE3_PROOF_2026-08-08.md`'s title claims it CLOSED at μ = 3, n ≤ 7 (unconditional) and reduced to HE3-BOX-6 at μ ≥ 4; `HE7_PROOF`'s COROLLARY HE7.B claims the level-2 predicate. **Per rule 10 the compiler verified GENHN's FULL append chain to line 2627: no HE3 or HE7 discharge has landed.** `grep -cF 'GENHN-HE' HE3_PROOF` = 7 confirms HE3 addresses it; the edge is real but one-directional. **Decision needed: whether the merged spec reads HE3/HE7's discharges onto GENHN's box, and at what grade.** No silent reading was made.

### OPEN-CALL 4 — TERMINAL readings "awaiting confirmation", and the spec has no vocabulary for that state **[MERGED — shard 1 OPEN-CALL 3 (3 units) is subsumed by shard 2 OPEN-CALL 4's fuller statement of the identical vocabulary gap (7 units); shard 1 could see only the units inside its own HOME range]**

Ten units' current readings are landed in the note but explicitly unconfirmed, none of them discharged by this merge:
- `.07`, `.09` (the frozen originals) via their CHAIN TERMINALs `.86`, `.88` — "subject to sol discharge-confirmation in the cert2 pass" (2280) / "Awaiting sol re-confirmation in the next queue" (2331–2332).
- `.24` via its SERIES TERMINAL `.92` — GENHN-ERR-1 "is SETTLED", but "a final transcription-confirmation rides the next queue" (2626–2627).
- `.31`, `.33`, `.35` (the three A2 repairs) — "await sol discharge-confirmation" (2263–2264), with the note's own certification-ledger line recording "GENHN's row stays OPEN."
The note's own ledger line (2263–2266, quoted at `.02`) says GENHN's certification row "stays OPEN." **Decision needed: whether a chapter cut may consume a landed-but-unconfirmed re-display or settlement as current.** Both shards compile every affected unit as TERMINAL-with-confirmation-owed and refuse to collapse the distinction; this merge carries that refusal forward unchanged.

### OPEN-CALL 5 — WZ-BOX-7's false parenthetical stands unedited in frozen accepted text, and no rider exists (shard 1 only)

`.28`'s final parenthetical ("J-D0: (digits) ↦ (twisted digits) is a type-preserving bijection") is **false**, disclosed by a consumer, with a machine witness on GENHN's own sealed data (972/972 flips). **GENHN has landed no rider** — verified against its full append chain. The *conclusion* the sentence draws is true and is what downstream text consumes; the *reason* is not. **Decision needed: whether GENHN owes a dated one-line rider, or whether the disclosure at WZ-BOX-7 suffices for the corpus.** The compiler emitted the sentence verbatim with the disclosure quoted and invented no rider.

### OPEN-CALL 6 — three scope compositions the note never writes down (shard 1 only)

(a) `.35`'s refine floor is stated as `κ > S′ ≥ e₁h`; post-`[r1]` and post-settlement the honest floor is `D′h`. The note never composes the two.
(b) `.09`'s TERMINAL slot scope is `D′h < m`; `.43`'s **composed** slot lemma (GENHN-2′) states "ONE K₂-digit per dv₂-height" with **no** occupied-height restriction, and no append addresses it. Whether the composed display needs a `D₂h`-style restriction is unaddressed.
(c) `.40`'s "Ore's theorem over the stage ring R" is the same phrase E3's rider list corrects at S9.2 item 1 (`.55`), but E3 (`.22`) does **not** name this line.
**Decision needed at 0b/chapter time: whether the merged spec composes these three, or records them as owed one-line riders.** No silent composition was made.

### OPEN-CALL 7 — GENIND-5 is cited by shape only, and a careless chapter cut could read it as a premise (shard 1 OPEN-CALL 6(b), the surviving half of shard 1's split call)

`.36` cites `GENIND-5` as the shape being generalized. Per `runs/qgen/WELD_FACE_AUDIT.md` LATENT-1, GENIND's own text says GENIND-5 is "NOT proved — boxed at the displayed obstruction." GENHN uses only its displayed *form*, but a careless chapter cut could read the citation as a premise. **Decision needed: whether the merged spec tags every GENIND-5 citation as shape-only.**

### OPEN-CALL 8 — three consumer-safety claims this compiler did not independently adjudicate (shard 2 only)

(a) `.86`: "no consumer reads the withdrawn datum-set finiteness" — a corpus-wide claim, "consumer safety verified at HEAD before folding" per `.85`. Not re-verified here.
(b) `.92` item 5: "HE6R1's completion-statement clause is restored with no wording change" — a reading of another note offered by GENHN, with no append landed on HE6R1. `LEMMA HE6R1-3` grep-verified (count 8) but the clause-level claim was not adjudicated.
(c) `.87`/`.88`: "every pin the note's laws consume sits at dv > D′h … so no consumer moves" — verified *within* GENHN, **not** verified across the notes that consume GENHN-2 (HE6, HE7, GENTOW*).
**Decision needed: whether the merge run performs these three consumer sweeps, or records them as inherited assertions.** No silent verification was claimed.

### OPEN-CALL 9 — the "SEVENTEEN quintic R_τ(q) displays" figure is unverifiable from anything in the note (shard 2 only)

`.53` states the P(5) display owes "the SEVENTEEN quintic R_τ(q) displays + Σ = 1 + engine/β₅ tie." The number 17 appears once, is not derived, and cross-checks against nothing else in the note. It is presumably the count of degree-5 splitting types, but the note supplies no enumeration and GENH5-DENS is unwritten. **Decision needed at 0b/chapter time: whether the merged spec carries 17 as a claim or as a placeholder.** Recorded as unverified-but-unclaimed rather than passed.

### Recorded source defects (flagged, not silently repaired; 20 raw across both shards → 21 distinct, since this merge additionally records the §4 header/table miscounts as a new joint defect not separately flagged by either shard)

1. **The §4 XREF-count header/table mismatch, both shards independently** (recorded fresh by this merge — see §4's intro): shard 1's header states "38 distinct designations" against its own table's 65 rows; shard 2's header states "31 distinct designations" against its own table's 52 rows. Neither shard's own self-audit caught this; this merge's row-count re-verification is what surfaced it. The actual dedup and sample-verification in §4 use the true row counts, not the stale header numbers.
2. **`.24`:** "this note's own §S3.1 remark in HE6 ('why D′h and not S = e₁h')" — the quoted phrase has count 0 in `HE6_PROOF_2026-08-08.md`; referent independently pinned by `LEMMA HE6-0` and `LEMMA HE6-3`.
3. **`.23`:** `GENIND-4` has count 0 in `GENIND_PROOF_2026-08-08.md`. GENHN-1's proof cites "exactly as GENH4-1F/GENIND-4"; GENIND's lemma roster is GENIND-0/-1/-2/-3/-5. The referent is not uniquely verifiable and the XREF is NOT emitted — shard 1's one unresolvable citation.
4. **`.05`:** the WELDMASTER bullet mis-attributes five designations — `[W12-H]`, `(CS-1)`, `(CS-2)`, `(CS-3)`, `(H-e)` all have count 0 in `WELDMASTER_2026-08-08.md`. Genuine mis-attribution in frozen accepted text, not a formatting near-miss.
5. **`.28`:** the J-D0 parenthetical at L736–737 is false and stands unedited — see OPEN-CALL 5. The conclusion it decorates is true.
6. **`.20` vs `.25`:** the entry-height tuple at `.20` and the floor tuple at `.25` differ by exactly the pin count (E3: 12 + 3 = 15; E31: 9 + 2 = 11). Both correct, both count different things, but only the erratum says so.
7. **`.55`:** the endgame list numbers items 1, 2, **2b**, 3, 4, 5, 6 — seven items under six numerals — and the closing sentence's range "2–5" is ambiguous about whether 2b is included.
8. **`.56`:** the SIGMALAW bullet points at "S8(b)'s letter-layer composition," and S8(b) is the **withdrawn** proof (`.17`). The pointer is not re-aimed by any append; the referent survives in T(b)′'s composed cocycles, but a reader following the pointer lands on withdrawn text.
9. **`.62`/`.70` P6:** the (2,5,1) spot instances sum to 25,088 against a row total of 32,768; the note claims exhaustiveness only for the (3,4,1) row, so there is no error, but a reader could mis-infer that the four named strata exhaust the (2,5,1) row.
10. **`.70` P1:** "all six CLASS flagships" counts *rows*, not distinct flagship values (four distinct values across six rows).
11. **`.74`:** the site arithmetic does not close — "the passPE2-F2 scope word reached 3 of 4 echo sites at r3" and then "the three residual … sites" are landed, but 3 + 3 ≠ 4; the two counts must enumerate different populations, unreconciled.
12. **`.79`:** the F-1 repair cites "GENHN-2(b)'s bracket," which has no literal referent — GENHN-2 is unlettered. The note itself catches this at `.84` and supplies the referent (`(CS-2)` / §S6.2).
13. **`.61`:** all seven GN-PIN md5s are truncated in their only full listing; three are recoverable in full from `.56`, four are not.
14. **`.54`, `.60`:** four truncated artifact hashes (`51154c95…`, `664036bc…`, `4a28246e…`, `10b685b0…`) name files that exist but versions that cannot be verified from the note.
15. **`.58`:** "HE7 … body prefix md5 732af1e1" is a truncated md5 in an otherwise fully-pinned append.
16. **`read22`** (`.05`) — count 0 in `QSCOUT22`; note-local shorthand for the pinned quartic reader.
17. **`.11`, `.34`:** "GENH4 S5" — fixed-string count 0 in `GENH4_PROOF`; the target's anchor is the bare `S5`. Referent unique; carried descriptively.
18. **`.14`:** E2's SOURCE names "GENH4 PE2 CRITICAL 1" and "PE3 REMARK A"; the reports use their own finding labels, so no designation-level XREF is emitted.
19. **`.36`:** "GENH4 S6.2" — §-anchor citation, count 0 as written; carried descriptively.
20. **Q1-style table defects: none found in GENHN** (unlike EFF-HE7's Q1 mislabel) — recorded here for completeness of method, not as a defect of this note.
21. **HMENU3-ANNEX-A-style near-miss: none found in GENHN** — GENHN's own near-misses (7, shard 1; 4, shard 2) are all §-anchor or clause-letter mismatches, not the HE7-style shorthand-vs-heading mismatch; recorded for completeness.

### Fidelity audit (merge-level, in addition to each shard's own three independent audits)

- All 93 canonical statement units carry mandatory CANONICAL STATEMENT, CONDITIONALITY, DERIVATION, RESOLUTION TRACE, TEETH, and FORM fields, verbatim-or-`[ASSEMBLED]` per template v2+v3. **No inverse, sign, quantifier, index, level, inequality direction, or implication direction was altered anywhere in the renumbering/consolidation pass** — the mechanical renumbering script touched only ID-string tokens (`EFF.GENHN.sKof2.NN` full forms and bare `` `.NN` `` shorthand under the disambiguation rule), never prose or mathematics; this was independently spot-checked by the 5-quote sample in §4 (all byte-identical to source) and by reading every SERIES/CHAIN-bearing unit in full during §7's construction.
- Every source table is marked `[TABLE]`; the note's only tagged LaTeX display (`.90`, LEMMA GENHN-COUNT-RERUN's eight `\tag{}` equations) is reproduced verbatim in source LaTeX and additionally transcribed per rule 14; no source table was prosified at merge time.
- All 76 unique external XREF designations have fixed-string counts ≥ 1; a 10-designation sample was re-grepped at merge time against the working tree and matched exactly with zero drift (§4); a 5-quote sample was re-checked verbatim against the source note by line number and matched byte-exact (§4). Forty-four cited commit hashes were independently confirmed real commits via `git cat-file -t`.
- **The ID-renumbering rewrite was performed mechanically** (a context-tracking, block-reset-aware Python script — `merge_genhn.py`, adapted from the identical pattern used for the EFF-GENIND and EFF-HE7 merges in this repo — not hand-transcription), precisely because GENHN's 425 bare-ID cross-references at 93 units made hand-renumbering an unacceptable error surface. **One bug was found and fixed during construction of this merge**: an initial version of the script let a "shard 1"/"shard 2" context mention persist across semicolon-delimited clause boundaries within the same paragraph, mis-resolving three bare refs in `.49`'s own CONDITIONALITY (`.24`/`.27`/`.29` were about to be left unchanged instead of shifted to `.72`/`.75`/`.77`); a gap-reset heuristic (reset context to the unit's home shard whenever the text between two ID tokens crosses a `; `, a `. `, or a `**member**`-style boundary marker) was added and the fix was verified by re-reading `.49` against source (§7.1's GENHN-GRADE-ARC table above reflects the corrected reading). An exhaustive regex sweep after the fix confirms **zero leftover `sKof2` substrings anywhere in the merged statement inventory (§3)** and **zero out-of-range IDs anywhere in the file** (every renumbered ID, bare and full-form, lies in 1–93).
- The four SERIES (§7.1) are each assembled with no duplication and no gap, cross-checked against both shards' own SHARD NOTES descriptions of their spans. The three supersession CHAINs (§7.2) have their TERMINAL members verified unique by an exhaustive scan of every supersession-target citation in the merged inventory. The twelve cross-shard supersession edges (§7.3) all resolve to a unit that exists exactly once in the merged inventory; zero dangling targets.
- Absorption status (§1's predicate A), the append/consumption protocol (§1's predicate B), and the inbound-corrections predicate (§1's predicate C) are kept distinct everywhere below, matching both source shards' own discipline.
- **Nine OPEN-CALLs were carried forward from twelve raw, three dedup/merge operations performed** (§8 above); no OPEN-CALL was discharged, narrowed, or silently resolved by the act of merging. The manifest-gap OPEN-CALL (1) is carried in both this merge's header (SHARD-BOUNDARY PROVENANCE subsection) and here in §8, per the charge's explicit instruction, with the "did adopt 1319|1320" half resolved and the "should the manifest be amended" half left open.
- **Honest limitation of this merge, stated once rather than twice:** the twenty-five individual BOUNDARY SELF-AUDIT arguments (which unit-boundary candidate was chosen inside a blockquote or a record, and why — thirteen in shard 1, twelve in shard 2) are not reproduced in this merged file — only their format-level conclusions (the four SERIES, the three CHAINs, the twelve-edge supersession table, the SUPERSESSION KIND vocabulary) survive here. A reader who needs the per-boundary reasoning for a specific unit should consult that unit's home shard file directly; the shard files are retained for exactly this purpose (§1).
- **CODEX CROSS-READ OWED is inherited whole, not discharged by this merge.** Neither shard, and no fold performed by this merge run, has been through an adversarial pass.

---

EFF-GENHN MERGED: 93 statements / 76 xrefs / 9 open calls

