# EFF-LIFTCORNER-s2of2 — CANONICAL EFFECTIVE-SPECIFICATION SHARD

**COMPILED-BY: opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). CODEX CROSS-READ OWED (post-reset).**

## 1. Shard header

**Source note:** `lean/notes/openmath/LIFTCORNER_2026-08-08.md` (2,083 lines / 133,230 bytes).

**HOME range:** source lines 1168–2083 inclusive (§S5 the consequence display + the five-line STATUS BLOCK + the `[r4, ARCHIVE]` region with its three superseded STATUS LINEs + the dating footer + the ★ ACCEPTANCE RECORD ★ + the two FC annexes + the three dated 2026-08-12 certifier adjudications, which carry annexes AC-1, AC-2, AC-3, AC-4 and AC-5 and their three orchestrator-verification parentheticals). Earlier text (lines 1–1167) is used ONLY to resolve material homed in that range; it is homed in shard 1 (`spec/EFF-LIFTCORNER-s1of2.md`).

**HEAD blob hash:** `d93c2aa253cdf5192f2e1525aa9f7b412b85b925` (fresh `git hash-object` at compile time; last touched by commit `33225dd9`).

**Compilation context:** `spec/EFF_TEMPLATE_v2.md` AT HEAD (rules 1–28), Stage 0a. Temporary IDs `EFF.LIFTCORNER.s2of2.<nn>`; the merge run renumbers.

**GENRE: MIXED — record surface + transcribed certifier proof.** This shard is the note's *status layer* (§S5, the STATUS BLOCK, the archive, the acceptance record) followed by ~600 lines of **transcribed external proof** (AC-1…AC-5, produced by the sol certification arc and transcribed unaltered by the orchestrator). The two halves need different compilation treatment and are kept separate throughout: the record surface is `changes-record` / `acceptance-box` / `scope record`; the certifier annexes are genuine `lemma` / `derivation` units whose author is NOT this note. `grep -c '\tag{'` = **6** over the whole note, and **all six are in this shard**, inside AC-5's (T1)–(T6) displays — so unlike shard 1, part of this shard is tag-carrying and its boundaries are read off the tags; the record-surface half remains tag-sparse and is covered by the BOUNDARY SELF-AUDIT in §7.

### FREEZE PREDICATES (v3 rule 21 — four in this shard, each with its own pin)

**FREEZE-1 (text freeze at acceptance).** `.17`: “**THIS NOTE IS ACCEPTED at 2/2**”, and the ANNEX heading (line 1457): “**ANNEX (dated appends; the frozen body is not edited)**”.

**FREEZE-1a (a SECOND, later text freeze at the certifier appends).** Line 1495:

> “Everything above this heading is
> byte-untouched by this append.”

This is a distinct predicate with a distinct date (2026-08-12) and a distinct scope (everything above line 1485, which now includes the acceptance record and both FC annexes). One freeze predicate must not stand for both.

**FREEZE-2 (sealed-runner instrument freeze).** Re-verified at compile time: `md5sum verification/openmath/liftcorner_checks.py` = `ccb4351c92573f5f962cae4ae952d8dd`, matching the acceptance record's own “md5 ccb4351c… byte-frozen dafc0b5 → HEAD”. `git cat-file -t dafc0b5` = commit.

**FREEZE-3 (children-generator instrument freeze).** The acceptance record's “children generator + A7 752/5,336/0” is re-verified against the committed table: `nodes reconciled: 752   children enumerated: 5336` ✓.

### Governing effective-text record

The rule is the same DERIVED rule as shard 1 (base + r1–r7 applied in text, strike-and-replace, superseded wording quoted inside the bracket that kills it), with two additions specific to this range:

**(a) After line 1431 the note is append-only, and every append is dated and quoted-unaltered.** Three appends state their own transcription discipline explicitly:

> “The E1 adjudication, transcribed unaltered:” (line 1496)

> “Transcribed unaltered:” (line 1616)

> “Transcribed unaltered:” (line 1831)

and each closes with an orchestrator-verification parenthetical that names what was re-derived before transcription. **The annexes are therefore NOT this note's mathematics**; they are external results, verified and transcribed. This compilation preserves that authorship distinction in every unit (`.22`–`.28`, `.31`–`.36`, `.39`–`.45` are marked `[TRANSCRIBED — certifier]`).

**(b) The `[r4, ARCHIVE]` region is explicitly dead.** Lines 1269–1272:

> “Nothing
> between the markers is live: it is superseded wholesale by the five-line STATUS
> BLOCK above, and is kept only because this note's discipline never silently
> deletes superseded wording.”

The three archived STATUS LINEs are emitted (`.13`–`.15`) because three corrections apply INSIDE the archive and the note states them so that no archived sentence can be misread as current — a chapter cut that dropped the archive would also drop those three corrections' targets.

**EFFECTIVE TEXT FOR THIS SHARD = lines 1168–2083 as written, with the archive region marked dead, the certifier annexes marked as transcribed external results, and the CHAINs below applied.**

### Supersession CHAINS in this shard (v3 rule 25; TERMINALs marked)

`[TABLE]`

| Chain | Layers, in source order | TERMINAL |
|---|---|---|
| **CHAIN-P (PROP / the all-rung rider)** | S4.3 PROP + S5 rider + FC-2's landed execution → **AC-1** SUSPENDS all three → **AC-4** narrows (constructor/telescope proved opaque; obstruction survives at (RM-1) alone) → **AC-5** proves (RM-1-TRANSPORT) and lifts the suspension | **AC-5** (`.45`) |
| **CHAIN-G (the grade counter)** | grade box “ATTEMPT 0/2” (×6, shard 1) + STATUS BLOCK COUNTER “0/2” (`.08`) → **ACCEPTANCE RECORD 2/2** (`.17`) | **`.17`** |
| **CHAIN-W (the W-2 cap)** | “GRTW2 is itself 0/2” (shard 1 `.72`) + the acceptance record's “the shift-descent consumption of GRTW2 (0/2, arc open) caps the discharge grade” (`.18`) → **FC-1**: read as “capped by an ACCEPTED supplier at its fenced scope” (`.19`) | **FC-1** (`.19`) |
| **CHAIN-S (the S5 deeper-level bookkeeping)** | r3 wording “NR-1 then leaves the ILNRES residual list … stays open as its own priced item” → **[r4, F4-6]** strikes it and replaces it with three paragraphs (`.02`–`.05`) → **AC-1 finding 2** re-affirms the fence as already curing the certifier's own finding (`.25`) | **[r4, F4-6]**, re-affirmed by finding 2 (`.03`–`.05`) |
| **CHAIN-F (FC-2's executed rider)** | acceptance record licenses (`.18`) → **FC-2** executes at `5054d69` and reports DISCHARGED (`.20`) → **AC-1** SUSPENDS the execution (`.23`) → **AC-5** reinstates it (`.45`) | **AC-5** (`.45`) — with the landed ITERLAWN annex still recording none of it (OPEN-CALL 1) |

### SERIES declared in this shard (v3 rule 28)

**SERIES REPAIR-ARC (continued from shard 1).** Shard 1 emitted links 1–7 (r1…r7). This shard continues with the STATUS BLOCK ARC bullet (`.07`, the whole arc as one dated line) and terminates the series at `.17` (the acceptance record, PE8 CLEAN → PE9 CLEAN).

**SERIES ARCHIVE-STATUS** — the three superseded STATUS LINEs, one unit per dated entry, in source order: `.13` (r1) → `.14` (r2, itself carrying two nested r3 brackets) → `.15` (r3). All three are DEAD; the series is recorded so that a merge run can reconstruct the order without prose-reading, and so that the three archive corrections (`.12`) can be pointed at the right member.

**SERIES CERTIFIER-ARC** — the (Φ₁-OPACITY) program, one unit per dated adjudication, in source order: **AC-1** (`.23`, containment, 2026-08-12 C1/E1) → **AC-4** (`.31`–`.36`, narrowing, 2026-08-12 P3) → **AC-5** (`.39`–`.45`, discharge, 2026-08-12 P4). The three share one ledger row (“row 19”) and one residual; emitting them as one merged “opacity record” would destroy the reader's ability to see which link a downstream citation used.

### Scope split — THREE predicates (rule 7 + v3 rule 17)

**A. Mathematical absorption / supply SET.** Fixed by the acceptance record (`.18`):

> “**WHAT IS ACCEPTED**: this note's theorems as fenced — (TAIL-STAB) via
> lexicographic (m, deg a) descent; READ-EQ; THE THEOREM (the display with
> the letter the lift carries, every orbit member); COR 1 (the ξ = 1
> slice); COR 2 (the corner restriction, as rescoped at r1/F3) — at the
> note's own conditionality”

**Five items, and PROP is not among them.** The supply set GREW after acceptance, by three transcribed certifier results that the note now carries: AC-2's CONTENT (integral-key form), AC-4's constructor/telescope opacity sublemma, and AC-5's (RM-1-TRANSPORT). None of the three is inside the accepted 2/2 scope; each is an append dated after acceptance.

**B. Append / consumption PROTOCOL scope — what this note has LANDED elsewhere.** Exactly **one** landed append, verified positively: the ITERLAWN fold annex (`grep -cF '## ★ FOLD ANNEX (orchestrator, 2026-08-07): THE NR-1 RIDER-REWRITE, LICENSED AND EXECUTED ★'` = 1, line 1518 — XREF Y10). Everything else is verified UNLANDED:

- `grep -cF 'OPACITY' ITERLAWN_PROOF_2026-08-08.md` = **0**
- `grep -cF 'AC-4' ITERLAWN_PROOF_2026-08-08.md` = **0**
- `grep -cF 'AC-5' ITERLAWN_PROOF_2026-08-08.md` = **0**
- `grep -cF 'LIFTCORNER' ILNRES_2026-08-08.md` = **0** (its single `LIFT-CORNER` hit is the S5.1 spec heading, i.e. the charge)

AC-5's own closing parenthetical schedules the first three (“transcription-confirm owed”). The consequence is stated as OPEN-CALL 1, not asserted as an error.

**C. Inbound corrections RECEIVED.** Five, all from the sol certification arc, all in this shard's range: AC-1, AC-2, AC-3 (from C1/E1), AC-4 (from P3), AC-5 (from P4). Four run logs verified to exist: `runs/cert/C1_liftcorner_output.log`, `runs/cert2/E1_liftcorner_output.log`, `runs/cert4/P3_opacity_output.log`, `runs/cert5/P4_rm1_output.log`. **Two of the five (AC-2, AC-3) replace statements homed in shard 1**; one (AC-1/AC-4/AC-5) resolves a shard-1 proposition; two more (finding 2, finding 5) are rebuttals that change nothing.

### Resolution rules applied

1. Lines 1168–2083 supply the HOME material.
2. The archive region (1297–1418) is DEAD; its three members are emitted with a dead-text marking and the three inside-archive corrections attached (`.12`).
3. **Certifier annexes are emitted as units of this note but attributed to their author.** The note transcribes them unaltered and says so; a compilation that silently re-attributed them to LIFTCORNER would misstate the DAG.
4. **The orchestrator-verification parentheticals are separate units** (`.29`, `.37`, `.46`), not footnotes to the annexes: they record what the orchestrator independently re-derived BEFORE transcription, which is a different warrant from the certifier's own.
5. Where an annex's consumer sweep names a target inside this note, the target unit carries the resulting reading in CONDITIONALITY; where it names a target in ANOTHER note, it becomes an XREF and a protocol obligation, never an assumed landing.
6. Designations cited by the annexes into `ITERLAWN_PROOF_2026-08-08.md` are grep-verified; three of them are NEAR-MISSes (v3 rule 15) because the annex writes an instantiated name (`CASE-SPLIT-(2)`, `READ-ADD-(1)`) where the source carries the schematic one (`CASE-SPLIT-(n)`, `READ-ADD-(m)`). These are recorded as NEAR-MISS with the verified referent, never suppressed and never emitted as clean XREFs.
7. Numbers are recomputed. AC-4's 194-hit partition, AC-5's (T1)/(T4) inequalities and the acceptance record's machine figures were each re-derived at compile time.

### Quotation discipline

CANONICAL STATEMENTs are verbatim or explicitly `[ASSEMBLED]`; `…` marks truncation. AC-5's LaTeX displays are reproduced in their source form (the note renders them in `\[…\]` inside blockquotes) rather than transliterated, because they are the six `\tag{}`-carrying displays of the whole note and a downstream Lean-spec cut will want the tags. No table is prosified.

---

## 2. Statement inventory

46 units, contiguous, in effective-text (= source) order. FORM is carried on every unit.

### EFF.LIFTCORNER.s2of2.01  [scope record]

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
(a) “ONCE THIS NOTE'S ARC CLOSES” — the condition is MET (`.17`) and the license was EXECUTED (`.20`).
(b) “at attempt grade (capped by the W-2 0/2 consumption)” — superseded by FC-1 (`.19`): read as capped by an ACCEPTED supplier at its fenced scope. SUPERSESSION KIND: **counter re-reading**.
(c) “ITER-LAW-n holds for EVERY lawful monic Φ₁, every n” — **SUSPENDED by AC-1** (`.23`), then **reinstated by AC-5** (`.45`): “**LIFTCORNER S5:** the every-\(n\) rider on the \(\Phi_1\) axis is no longer conditional on \((\Phi_1\)-OPACITY). The fence excluding independently chosen noncanonical higher keys remains unchanged.” SUPERSESSION KIND: **scope-pin**, then **license**. TERMINAL = AC-5.
**Residual scope a consumer must carry:** AC-5 reinstates the rider *at ITERLAWN's own conditionality*, and ITERLAWN's (RM-m) engine is **OPEN at m ≥ 2** by its own STATUS box (XREF Y06: “m ≥ 2: **OPEN.**”). “Every n at [ILN]'s own conditionality” is therefore not an unconditional all-rung theorem, and never was.

**RESOLUTION TRACE:** statement lines 1170–1176; correction sites 1433 (a), 1459–1471 (b), 1509 + 2053–2057 (c).

**TEETH:** XREF Y01 verifies ITERLAWN's rider text and Y10 the landed fold annex, which transcribes this display verbatim and calls it “verbatim from LIFTCORNER S5”, citing “lines 1168–1176 at acceptance” — the exact span of this unit.

---

### EFF.LIFTCORNER.s2of2.02  [changes-record]  *(CHAIN-S, link 2)*

**CANONICAL STATEMENT:**

> “**[r4, F4-6 — the bookkeeping sentence that followed is STRICKEN and replaced
> by the three paragraphs below. The r3 wording, quoted in full and superseded:**
> "NR-1 then leaves the ILNRES residual list; the T-class(n) conditionality of
> record shrinks to NR-2/NR-3 (+ NR-4's own closing arc). NOT covered, said
> plainly: non-canonical lawful lifts at DEEPER levels (Φ_{m+1}, m ≥ 1) — a
> separate corner (the g_m = 1 analogue), never part of (ITER-LAW-LIFT)'s
> displayed statement (wave-18 S0), stays open as its own priced item."**]**”

**FORM:** bold-headed bracketed strike quoting its target in full.

**DERIVATION:** `[RECORD]`. The reason is given at `.05`: the unit has no authority to create a residual, and an uncited new one would collide with ILNRES S7's recorded completeness.

**CONDITIONALITY:** SUPERSESSION KIND: **replacement** (one sentence by three paragraphs). The quoted r3 wording is DEAD.

**RESOLUTION TRACE:** statement lines 1178–1184; replacement at 1186–1223.

**TEETH:** the collision it avoids is verified — XREF Y03: ILNRES line 288, `S1's FOUR-MEMBER residual list is COMPLETE relative to the sources`, count 1.

---

### EFF.LIFTCORNER.s2of2.03  [scope record]

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

**CONDITIONALITY:** “PENDING THIS NOTE'S ARC (attempt 0/2, W-2-capped)” is superseded twice — by `.17` (2/2) and by FC-1 (`.19`). The PROP clause is CHAIN-P (TERMINAL AC-5). “this note edits no ledger” is true of the note and remains true; the ledger edit happened as a separate append on ITERLAWN (`.20`).

**RESOLUTION TRACE:** statement lines 1186–1198.

**TEETH:** **both embedded quotes independently re-verified at compile time under whitespace normalization** (they span source line breaks, so single-line `grep -F` fails; recorded as verified-by-normalized-match per v3 rule 15):
- XREF Y02 — `ILNRES_2026-08-08.md`, `Extend the [IL] L7 Case-II analysis to an arbitrary lawful lift Φ₁′ = Φ₁ + (π-excess) at g₀ = 1 ∧ δ₁ = 1, then ride S0.1's verbatim propagation` — count 1 (line 180).
- XREF Y04 — `ITERLAWLIFT_CORNER_2026-08-08.md`, `the honest OPEN displayed lemma **(ITER-LAW-LIFT)**: ITER-LAW for every lawful monic lift Φ₁` — count 1 (lines 35–36).
The note's parenthetical claim “both quotes verified at source” is therefore itself verified.

---

### EFF.LIFTCORNER.s2of2.04  [scope record]

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

**CONDITIONALITY:** **the note declines to adjudicate, and that declination is itself the effective content.** AC-1's finding 2 later cites this paragraph and `.05` as already curing a certifier objection (`.25`), which confirms the fence but does not resolve the discrepancy.

**RESOLUTION TRACE:** statement lines 1200–1207.

**TEETH:** XREF Y05 — `ILNRES_2026-08-08.md`, `nothing is claimed for any non-canonical lawful lift at any level`, count 1 (line 28, verified under normalization across a line break).

---

### EFF.LIFTCORNER.s2of2.05  [scope record]  *(CHAIN-S — TERMINAL of the in-note layers)*

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

### EFF.LIFTCORNER.s2of2.06  [instrument-record]

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

**CONDITIONALITY:** the rule was honoured: the block is still five bullets at HEAD (`.07`–`.11`), edited at r5, r6, r7 and never grown. Verified by inspection.

**RESOLUTION TRACE:** statement lines 1225–1231.

**TEETH:** disposition `instrument-record`; the instrument is the record surface itself. PE6 and PE7 both line-audited it and judged the bring-forward correct.

---

### EFF.LIFTCORNER.s2of2.07  [acceptance-box]  *(SERIES REPAIR-ARC, continuation)*

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

**CONDITIONALITY:** the terminal “PE8 = the next acceptance attempt” is SPENT: `.17` records PE8 CLEAN and PE9 CLEAN. SUPERSESSION KIND: **as-of scoping**.

**RESOLUTION TRACE:** statement lines 1233–1240; continuation at 1437–1439.

**TEETH:** ARITHMETIC AUDIT: seven repair rounds and seven passes are listed here; the acceptance record adds two more passes for **nine hostile passes, seven repair rounds** — which is exactly what it claims (“Nine hostile passes, seven repair rounds”). ✓ All nine report files exist; all nine commit pins resolve (shard 1 §3.4, P06–P15).

---

### EFF.LIFTCORNER.s2of2.08  [acceptance-box]  *(CHAIN-G, link 1)*

**CANONICAL STATEMENT:**

> “* **COUNTER.** Acceptance **0/2** — no pass has been clean, and a repair round
>   is not a pass. The grade is CAPPED by this unit's W-2 consumption (GRTW2
>   itself 0/2); the COR 1 / ξ = 1 chain is W-2-free, so if W-2's arc lags the
>   ξ = 1 discharge stands on this note's own arc alone.”

**FORM:** bullet (line 2 of 5).

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** **both halves superseded.** 0/2 → 2/2 (`.17`, CHAIN-G TERMINAL); “GRTW2 itself 0/2” → FC-1's accepted supplier (`.19`, CHAIN-W TERMINAL). The decoupling clause survives verbatim into the acceptance record.

**RESOLUTION TRACE:** statement lines 1241–1244; correction sites 1433, 1459–1471.

**TEETH:** as `.17`, `.19`.

---

### EFF.LIFTCORNER.s2of2.09  [acceptance-box]

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

**TEETH:** 25,409/0 re-verified against the committed artifact (shard 1 §6.3). The five proved items match the acceptance record's five (`.18`) exactly — a cross-check that the record surface and the acceptance record agree on the supply set.

---

### EFF.LIFTCORNER.s2of2.10  [acceptance-box]

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

**CONDITIONALITY:** item-by-item at HEAD: **(5) is DISCHARGED** by AC-4+AC-5 (CHAIN-P), though not by the census it asks for; **COR 2's (a)/(b) remain OWED** (AC-5 leaves COR 2 unchanged); **the ILNRES erratum candidate remains OPEN** (`.05`, verified negatively); “pending this note's arc” is spent (`.17`).

**RESOLUTION TRACE:** statement lines 1251–1257.

**TEETH:** the seven-item status table is compiled at shard 1 `.71`.

---

### EFF.LIFTCORNER.s2of2.11  [acceptance-box]

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

### EFF.LIFTCORNER.s2of2.12  [changes-record]

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

**CONDITIONALITY:** SUPERSESSION KIND: **replacement** (wholesale, of three status lines by one block), with three nested **provenance-rider**/**replacement** corrections inside the dead region. **TARGETS:** `s2of2.13`, `.14`, `.15`.

**RESOLUTION TRACE:** statement lines 1268–1295; the archive markers at 1297 (`<!-- ARCHIVE-BEGIN … -->`) and 1418 (`<!-- ARCHIVE-END -->`).

**TEETH:** the three corrections' terminals all live in shard 1 (`.25` for (1) and (3); `.10` for (2)) — this unit is the archive's index into CHAIN-A and CHAIN-B.

---

### EFF.LIFTCORNER.s2of2.13  [changes-record — DEAD]  *(SERIES ARCHIVE-STATUS, link 1)*

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

**CONDITIONALITY:** DEAD in full (`.12`), and its F4 clause additionally REFUTED by archive correction (1). It carries one fact worth preserving for the DAG: it names the r0 sentence it supersedes (“wave-18's price sheet is settled in full”), which is the note's own first overclaim and the origin of the “MODULO this note's own arc” formula repeated in every later status line.

**RESOLUTION TRACE:** statement lines 1299–1319; the refutation at 1274–1281.

**TEETH:** none (dead text); guarded by `.12`.

---

### EFF.LIFTCORNER.s2of2.14  [changes-record — DEAD]  *(SERIES ARCHIVE-STATUS, link 2)*

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

**CONDITIONALITY:** DEAD in full, and its `[r3, F-C]` bracket additionally corrected for PROVENANCE by archive correction (2) — whose terminal is shard 1 `.10`. **This is a three-deep nesting inside dead text** (dead status line ⊃ live-at-the-time r3 bracket ⊃ r4 correction stated in the archive preamble), and it is the reason `.12` exists as its own unit.

**RESOLUTION TRACE:** statement lines 1321–1379; corrections at 1282–1289.

**TEETH:** none (dead text). The r2 five-repair inventory it records (G1–G5) is compiled live at shard 1 `.42`, `.44`, `.46`, `.48`, `.51`.

---

### EFF.LIFTCORNER.s2of2.15  [changes-record — DEAD]  *(SERIES ARCHIVE-STATUS, link 3)*

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

### EFF.LIFTCORNER.s2of2.16  [record]

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

### EFF.LIFTCORNER.s2of2.17  [acceptance-box]  *(CHAIN-G — TERMINAL; SERIES REPAIR-ARC — TERMINAL)*

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

**TEETH:** `git cat-file -t c6097d7` = commit; `git cat-file -t 9b5175c` = commit; both `LIFTCORNER_passPE8_report.md` and `LIFTCORNER_passPE9_report.md` exist. ARITHMETIC AUDIT: the arc lists 9 passes and 7 rounds ✓, matching `.07`'s ARC bullet extended by two.

---

### EFF.LIFTCORNER.s2of2.18  [acceptance-box]

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

**CONDITIONALITY:** three riders. (a) “(0/2, arc open)” → FC-1 (`.19`), CHAIN-W. (b) “NOW LICENSED for execution” → discharged by FC-2 (`.20`), CHAIN-F, then suspended by AC-1 and reinstated by AC-5. (c) **PROP is not in the accepted list** — five items, and the all-rung propagation is not one of them; this is the fact AC-1 exploits and this compilation records it as a positive scope finding in both shards.

**RESOLUTION TRACE:** statement lines 1443–1453; correction sites 1459–1471 (a), 1473–1481 + 1509 + 2058 (b).

**TEETH:** the machine record's three figures re-verified at compile time: md5 ✓, `TOTAL checks 25409` ✓, `nodes reconciled: 752   children enumerated: 5336` ✓.

---

### EFF.LIFTCORNER.s2of2.19  [changes-record]  *(CHAIN-W — TERMINAL)*

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

**CONDITIONALITY:** SUPERSESSION KIND: **counter re-reading**, scoped “wherever this note bills GRTW2 at 0/2 / arc open”. **The cap does not disappear** — it becomes a cap by an accepted supplier AT ITS FENCED SCOPE, and GRTW2's fence is its own open box (W2-OPEN-2/OPEN-2a). **TARGETS:** `s1of2.02`, `s1of2.72`, `s2of2.08`, `s2of2.18`, and (transitively) the six shard-1 grade-box entries.

**RESOLUTION TRACE:** statement lines 1459–1471.

**TEETH:** the supplier acknowledgement is verified at count 1 — XREF Y07: `GRTW2_PROOF_2026-08-08.md` line 1351, “the accepted LIFTCORNER's shift-descent”, in the sentence “consumers riding W-2 at attempt grade (the accepted LIFTCORNER's shift-descent consumption; JB's W2-C1 restriction; WM's M4 face) now ride an ACCEPTED supplier at its fenced scope.” `git cat-file -t adc6cf3` = commit. **This is a two-way verified edge**: consumer declares, supplier acknowledges, both at count 1.

---

### EFF.LIFTCORNER.s2of2.20  [changes-record]  *(CHAIN-F, link 2)*

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

### EFF.LIFTCORNER.s2of2.21  [record]

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

**TEETH:** both run logs verified to exist: `runs/cert/C1_liftcorner_output.log`, `runs/cert2/E1_liftcorner_output.log`. ARITHMETIC AUDIT: 1 CRITICAL + 2 GAP + 2 MINOR = 5 findings; the adjudication dispositions listed are 1 OBSTRUCTED + 1 RESOLVED-ALREADY + 2 REAL + 1 ARTIFACT = **5** ✓, and all five are emitted below (`.22`–`.28`).

---

### EFF.LIFTCORNER.s2of2.22  [supplier-finding]  `[TRANSCRIBED — certifier]`

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

### EFF.LIFTCORNER.s2of2.23  [lemma-statement + scope-pin]  `[TRANSCRIBED — certifier]`  *(SERIES CERTIFIER-ARC, link 1; CHAIN-P link 2)*

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

### EFF.LIFTCORNER.s2of2.24  [preregistration]  `[TRANSCRIBED — certifier]`

**CANONICAL STATEMENT:**

> “> **PRE-PROOF NUMERICAL CERTIFICATE.** Use, without sampling, the 56 S3 orbit towers—48 twisted towers and 8 \(\xi=1\) dense controls—each paired with its same-residue standard lift \(\Phi''\), plus the exact PE1 counter-instance and its standard-lift mate. Run every pair through rungs \(n\in\{2,3,4,5\}\). At each of ITERLAWN S7’s 22 dependency sites record the branch decisions, degrees, valuations, residual coefficients, \(C_k\), telescope terms, and final read/cocycle data. Normalize each polynomial datum to formal \(\Phi_1\)-adic coordinates by replacing \(\Phi_1^i\) with a common symbol \(U^i\) and identifying the shared coefficient fields. The required predicate is equality of the complete normalized records for \(\Phi_1'\) and \(\Phi_1''\), together with an access trace showing that no non-leading coefficient of \(\Phi_1\) reaches a branch condition, valuation, residual coefficient, \(C_k\), telescope bound, or final read except through the opaque formal-power node \(\Phi_1^i\). Required verdict: zero normalized mismatches and zero forbidden coefficient accesses on all 57 tower pairs, all four tested rungs, and all 22 sites. This is an instance certificate only; the universal conclusion still requires a source-level proof of \((\Phi_1\)-OPACITY).”

**FORM:** bold-headed preregistration inside the AC-1 annex.

**DERIVATION:** `[PREREGISTERED]` — a falsifier specified before any run, with an explicit required verdict.

**CONDITIONALITY:** **NEVER EXECUTED, and superseded as unnecessary.** No artifact in `verification/openmath/` corresponds to it (verified: no file matching `*opacity*` or `*rm1*` exists there), and AC-5 discharged the residual by proof instead. Two of its design premises were also superseded: the “22 dependency sites” universe is replaced by AC-4's 194-hit machine census, and the “equality of the complete normalized records” predicate is exactly what AC-5 says is “generally the wrong statement”. Disposition **`preregistration, superseded-unexecuted`**.

**RESOLUTION TRACE:** statement line 1517; supersession at 1620 (census) and 2017–2024 (predicate).

**TEETH:** ARITHMETIC AUDIT: “57 tower pairs” = 56 orbit towers + the PE1 counter-instance ✓ (consistent with shard 1 `.21`'s independently recomputed 56). “22 sites” matches ITERLAWN S7's 22 data rows, independently recounted (XREF Y12, 24 pipe-lines − header − separator = 22) — so the certificate's design was correctly pinned even though its universe was later widened.

---

### EFF.LIFTCORNER.s2of2.25  [supplier-finding — rebuttal]  `[TRANSCRIBED — certifier]`

**CANONICAL STATEMENT:**

> “2. RESOLVED-ALREADY — the broader “at any level” reading remains fenced
>
> The finding conflates changing \(\Phi_1\) and propagating that fixed choice through canonical higher rungs with independently choosing a noncanonical \(\Phi_{m+1}\) at a deeper level.
>
> The exact cure is already in `[r4, F4-6]` … The acceptance record accepts “this note’s theorems **as fenced**.” FC-1 is explicitly a correction only of “the W-2 cap”; it changes the supplier grade from \(0/2\) to accepted and does not erase the `[r4, F4-6]` scope fence. Therefore the noncanonical-\(\Phi_2\) counter-configuration was already excluded from the discharged scope.
>
> This does not cure finding 1: propagation of a changed \(\Phi_1\) through canonical higher rungs still needs \((\Phi_1\)-OPACITY).”

**FORM:** numbered finding (rebuttal) quoting `.03` and `.04`.

**DERIVATION:** a scope distinction (changing Φ₁ vs independently choosing a noncanonical Φ_{m+1}) plus a reading of FC-1's scope.

**CONDITIONALITY:** **this unit constrains FC-1's reach and should be read alongside `.19`**: FC-1 is a counter re-reading of the W-2 cap ONLY and erases no scope fence. Nothing here changes; the finding is rebutted.

**RESOLUTION TRACE:** statement lines 1519–1533.

**TEETH:** the two quoted `[r4, F4-6]` sentences are verified verbatim in `.03` and `.04`. Disposition `AUDIT / decorrelated-model audit, rebutted at source`.

---

### EFF.LIFTCORNER.s2of2.26  [lemma]  `[TRANSCRIBED — certifier]`  *(supersedes shard 1 `.34`)*

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

**CONDITIONALITY:** SUPERSESSION KIND: **replacement**. **TARGETS:** `s1of2.34`. The consumer sweep (quoted at shard 1 `.34`) certifies that every consumer survives unchanged, and names the excluded counterexample: “The counterexample \(\Phi=x+p^{-1}\) is excluded precisely because \(\Phi\notin\mathcal O[x]\).”

**RESOLUTION TRACE:** statement lines 1535–1552.

**TEETH:** ORCHESTRATOR VERIFICATION quoted at `.29` re-checked the division proof independently. Compile-time check of the counterexample: for Φ = x + p⁻¹ and F = 1·x (content 0), dev gives digits involving p⁻¹, so the frozen “for monic Φ” statement is indeed false as displayed and the integrality hypothesis is load-bearing ✓. Disposition `AUDIT / decorrelated-model audit`.

---

### EFF.LIFTCORNER.s2of2.27  [derivation]  `[TRANSCRIBED — certifier]`  *(supersedes shard 1 `.55`)*

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

**CONDITIONALITY:** SUPERSESSION KIND: **replacement**. **TARGETS:** `s1of2.55` only.

**RESOLUTION TRACE:** statement lines 1554–1573.

**TEETH:** ARITHMETIC AUDIT: at d₀ = 1, deg Φ′ = e₀·1 = e₀, so the frozen “e₀ < deg Φ′” reads e₀ < e₀, false ✓; the corrected form gives s·1 < e₀·1, true for s < e₀ ✓. Disposition `AUDIT / decorrelated-model audit`.

---

### EFF.LIFTCORNER.s2of2.28  [supplier-finding — rebuttal]  `[TRANSCRIBED — certifier]`

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

### EFF.LIFTCORNER.s2of2.29  [instrument-record]

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

**CONDITIONALITY:** the ledger line “row 19 → AC-2/AC-3 folded; OPEN pending (Φ₁-OPACITY) + discharge” is superseded by `.37` and `.46`, which carry row 19 forward to “the (Φ₁-OPACITY) program is complete … transcription-confirm owed”.

**RESOLUTION TRACE:** statement lines 1587–1601.

**TEETH:** XREF Y13 — `docs/PROJECT_STATE.md` carries the row-19 tracking at count 1: `row 19 also ((Φ₁-OPACITY), numerical certificate` (line 3996). Disposition `accepted-with-decorrelation-supplied`: the orchestrator's re-derivations are independent of the certifier's.

---

### EFF.LIFTCORNER.s2of2.30  [record]

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

**CONDITIONALITY:** none; superseded in outcome by P4 (`.38`–`.45`), which proves the named residual.

**RESOLUTION TRACE:** statement lines 1607–1616.

**TEETH:** `runs/cert4/P3_opacity_output.log` exists. The “194 mapped hits” figure is verified against ITERLAWN's own machine-census bracket (XREF Y14, count 1, line 1233).

---

### EFF.LIFTCORNER.s2of2.31  [table + scope record]  `[TRANSCRIBED — certifier]`  *(SERIES CERTIFIER-ARC, link 2; CHAIN-P link 3)*

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

### EFF.LIFTCORNER.s2of2.32  [lemma]  `[TRANSCRIBED — certifier]`

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

**DERIVATION:** `.33`.

**CONDITIONALITY:** **the last sentence is the load-bearing fence and must travel with the lemma**: Θ is asserted only on displayed normal forms, NOT as commuting with arbitrary division. That fence is precisely why the (RM-1) division survives as an obstruction (`.34`).

**RESOLUTION TRACE:** statement lines 1639–1653; proof 1655–1729.

**TEETH:** designations verified in ITERLAWN: `### S4.1 Lemmas REALIZE-(m), WELL-DEF-(n), READ-ADD-(m)` (Y11, count 1); `### S4.2 L6-(n) …` (Y09, count 1); `TRUNC` count 14; `WELL-DEF` count 32; `realize_m(τ, β)` count 1.

---

### EFF.LIFTCORNER.s2of2.33  [derivation]  `[TRANSCRIBED — certifier]`

**CANONICAL STATEMENT:** AC-4's proof of `.32`, source lines 1655–1729, `[ASSEMBLED]` from its five stages (each quoted verbatim below in the DERIVATION field rather than duplicated here).

**FORM:** italic-headed proof with five stages and three displays.

**DERIVATION:** induction on m, in five stages.
- **Base m = 1:** “the displayed formula \(\operatorname{realize}_1(\tau,\beta) =\sum_i \operatorname{realize}_0\!\left( \epsilon_0(\gamma^{(i)})^{-1}\tau_i,\gamma^{(i)} \right)\Phi_0^{k_i}\) contains no \(\Phi _1\). Its coordinates \(\tau_i\), slots \(k_i\), weights \(\gamma^{(i)}\), field operations and \(\epsilon\)-factors are shared. Hence the two realizers are literally equal at this level.”
- **Step:** the level-m realizer's inputs “depend only on the shared field/read package. By induction the coefficients correspond, and the final occurrence of \(\Phi_{m-1}\) is an opaque formal power.”
- **REALIZE clauses:** “Clauses (R2) and (R3) use the already displayed sum as its \(\Phi_{m-1}\)-development: the coefficient-degree bound makes every summand a single legal digit, and distinct \(i\) give distinct slots. Thus no coefficient of \(\Phi_{m-1}\), and hence no non-leading coefficient of \(\Phi _1\), is opened.”
- **C_k and the canonical key:** “Its field input, weight and \(\epsilon_m\)-factor are shared, so the realizer induction gives \(\Theta(C_k'')=C_k'\) … Monicity comes from the top term \(\Phi_m^{e_mg_m}\); every lower term has smaller degree by (R1).”
- **TRUNC and the telescope:** “TRUNC merely discards the top level. On the two towers “identical lifts” must be read as “corresponding lifts under \(\Theta\)”… Finally, S4.2 uses only \(\deg a=\sum_{j<n}s_{j+1}\deg\Phi_j \le\sum_{j<n}(\deg\Phi_{j+1}-\deg\Phi_j) =\deg\Phi_n-d_0<\deg\Phi_n\). … It establishes that \(a\) is a single \(\Phi_n\)-digit without opening \(\Phi_n\). ∎”

**CONDITIONALITY:** every stage turns on the same mechanism — the key appears only as a formal power, never as a divisor. The proof does not and cannot cover a step that divides by the key; that is `.34`.

**RESOLUTION TRACE:** proof lines 1655–1729.

**TEETH:** ARITHMETIC AUDIT of the telescope inequality, recomputed: Σ_{j<n} s_{j+1}·deg Φ_j ≤ Σ_{j<n}(deg Φ_{j+1} − deg Φ_j) telescopes to deg Φ_n − deg Φ_0 = deg Φ_n − d₀ < deg Φ_n ✓. The step uses s_{j+1}·deg Φ_j ≤ deg Φ_{j+1} − deg Φ_j, i.e. (s_{j+1}+1)·deg Φ_j ≤ deg Φ_{j+1}, which holds under the class's degree recursion deg Φ_{j+1} = e_j g_j deg Φ_j with s_{j+1} ≤ e_j g_j − 1 — the same bound (R1) uses. ✓ Disposition `derivation, transcribed; arithmetic verified`.

---

### EFF.LIFTCORNER.s2of2.34  [supplier-finding]  `[TRANSCRIBED — certifier]`

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

**CONDITIONALITY:** this is the surviving obstruction after `.32`. It is what AC-5 discharges — not by removing the coefficient reading (“coefficient-reading by division is real”, AC-5's closing sentence) but by showing its effect lies strictly above every consumed interface line.

**RESOLUTION TRACE:** statement lines 1731–1771; the discharge at 2068–2070.

**TEETH:** the quoted ITERLAWN status is verified **verbatim at count 1** — XREF Y15: `m = 1: PROVED — [IL3] DIGIT-SPLIT + DEV-1` (ITERLAWN line 794, inside the boxed (RM-m) display at S4.6, Y16 count 1 line 777). ARITHMETIC AUDIT of the identity: R″ + Q″Φ₁″ = R″ + Q″(Φ₁′ − Δ) = (R″ − Q″Δ) + Q″Φ₁′ ✓.

---

### EFF.LIFTCORNER.s2of2.35  [lemma-statement]  `[TRANSCRIBED — certifier]`

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

**DERIVATION:** `[STATED]` here; PROVED at `.39`–`.43`.

**CONDITIONALITY:** **this statement REPLACES AC-1's (Φ₁-OPACITY) as the thing to prove.** SUPERSESSION KIND: **replacement** of a proof obligation. A consumer citing “(Φ₁-OPACITY) was proved” would be wrong on two counts: the constructor half was proved as a different lemma (`.32`), and the (RM-1) half was proved as this weaker one.

**RESOLUTION TRACE:** statement lines 1787–1795; proof at 1833–2024.

**TEETH:** `ITER-PKG-2` verified at count 1 in ITERLAWN (Y17). **Scope note carried forward:** ITERLAWN's own ledger row for the package reads “the induction package (ITER-PKG-r) | STATED; base r = 1 ACCEPTED, r = 2 = [IL3] 0/2” (line 279) — so ITER-PKG-2 itself rides [IL3] at grade 0/2. AC-5 constructs it for arbitrary same-residue Φ₁′ *on ITERLAWN's own proved perimeter*, and inherits that grade.

---

### EFF.LIFTCORNER.s2of2.36  [scope record]  `[TRANSCRIBED — certifier]`

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

**CONDITIONALITY:** **every one of the first three bullets is SUPERSEDED by AC-5's sweep** (`.45`), which lifts all three suspensions. The fourth bullet (the ITERLAWN certification) is NOT superseded — it stands and is strengthened. A consumer must read `.45`, not this unit, for PROP/S5/FC-2.

**RESOLUTION TRACE:** statement lines 1797–1815; supersession at 2053–2060.

**TEETH:** the fourth bullet's claim is a certification LANDED NOWHERE: `grep -cF 'OPACITY' ITERLAWN_PROOF_2026-08-08.md` = 0 (N1). ITERLAWN is certified Φ₁-opaque by an annex in another note that ITERLAWN does not reference. OPEN-CALL 1.

---

### EFF.LIFTCORNER.s2of2.37  [instrument-record]

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

**CONDITIONALITY:** the ledger line is superseded by `.46`.

**RESOLUTION TRACE:** statement lines 1817–1823.

**TEETH:** the orchestrator's arithmetic check (88+21+53+8+18+6 = 194) is re-verified independently at `.31` and agrees. `runs/cert4/P3_opacity_output.log` exists.

---

### EFF.LIFTCORNER.s2of2.38  [record]

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

### EFF.LIFTCORNER.s2of2.39  [lemma]  `[TRANSCRIBED — certifier]`  *(SERIES CERTIFIER-ARC, link 3; CHAIN-P — TERMINAL begins)*

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

**TEETH:** **MANDATORY ARITHMETIC AUDIT, recomputed:** since gcd(e₀,h₀) = 1 and 0 < k < e₀, e₀ ∤ (e₀−k)h₀, so ⌈(e₀−k)h₀/e₀⌉ ≥ ((e₀−k)h₀ + 1)/e₀, hence e₀·amin(k) ≥ (e₀−k)h₀ + 1 and e₀·amin(k) + kh₀ ≥ e₀h₀ + 1 = W + 1 ✓. For k = 0: weight ≥ e₀(h₀+1) = e₀h₀ + e₀ ≥ W + 1 since e₀ ≥ 1 ✓. (T1) is correct as displayed. **This is the same inequality LIFTCORNER's own `.42` derives**, re-used at a different level — a genuine reuse of the note's mathematics by its certifier.

---

### EFF.LIFTCORNER.s2of2.40  [lemma]  `[TRANSCRIBED — certifier]`

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

**TEETH:** the DIGIT-SPLIT bound is LIFTCORNER's CONTENT (`s1of2.34`, effective = AC-2's integral-key form); the lex measure is `s1of2.37`. ARITHMETIC AUDIT of the displayed child bound: e₀w₀(r) + (m−e₀+k)h₀ ≥ e₀(w₀(a)+w₀(b_k)) + (m−e₀+k)h₀, and with w₀(b_k) ≥ amin(k) satisfying e₀·amin(k) ≥ (e₀−k)h₀, this is ≥ e₀w₀(a) + (e₀−k)h₀ + (m−e₀+k)h₀ = e₀w₀(a) + mh₀ ✓, exactly as displayed.

---

### EFF.LIFTCORNER.s2of2.41  [derivation]  `[TRANSCRIBED — certifier]`

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

**CONDITIONALITY:** **this step CONSUMES ITERLAWN's (RM-1) theorem at its own scope**, which is the m = 1 engine fenced as in `.40`'s scope tension. The shared correction digit rides AC-4's `.33` base case.

**RESOLUTION TRACE:** statement lines 1913–1936.

**TEETH:** the (RM-1) interface's four consumed clauses are verified against ITERLAWN's boxed statement (Y16): the box displays `f·Ĉ_m = R + Q·Φ_m,   w_m(R) ≥ λ + γ_{m+1},   w_m(Q) ≥ λ + γ_{m+1} − w_mΦ_m   (Q = 0 allowed),   R_{m,λ+γ_{m+1}}(R) = z_m^{ε′}·v·τ_m` — **exactly the two degree bounds, two weight bounds and prescribed read that (RM-1-TRANSPORT) transports.** The correspondence is exact and was re-checked line by line at compile time.

---

### EFF.LIFTCORNER.s2of2.42  [derivation]  `[TRANSCRIBED — certifier]`

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

### EFF.LIFTCORNER.s2of2.43  [lemma]  `[TRANSCRIBED — certifier]`

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

**FORM:** numbered four-clause display list — the proof of `.35`.

**DERIVATION:** clauses 1–3 by the ultrametric on the differences of (T6); clause 4 by READ-ADD-(1)'s strict-above kill applied to w₁(A) ≥ μ+1 > μ.

**CONDITIONALITY:** **the uniformity claim is the whole point** — “The argument is uniform in \(f\)” answers AC-4's objection that no displayed argument covers every RM-1 input.

**RESOLUTION TRACE:** statement lines 1985–2015.

**TEETH:** **NEAR-MISS XREF (v3 rule 15)** — `READ-ADD-(1)` is absent from ITERLAWN as written (`grep -cF 'READ-ADD-(1)'` = 0); the verified referent is the schematic `READ-ADD-(m)`, at `ITERLAWN_PROOF_2026-08-08.md` line 499 (`### S4.1 Lemmas REALIZE-(m), WELL-DEF-(n), READ-ADD-(m)`, count 1) and line 564 (`**Lemma READ-ADD-(m) (read additivity with strict-above kill; generic).**`, count 1), whose title confirms the strict-above kill the clause invokes. Recorded as NEAR-MISS, not as a clean XREF and not suppressed. ARITHMETIC AUDIT: clauses 2 and 3 follow from (T5) and the displayed R″/Q″ bounds by the ultrametric ✓; clause 4 needs w₁(A) > μ, which (T5) gives as ≥ μ+1 ✓.

---

### EFF.LIFTCORNER.s2of2.44  [fence]  `[TRANSCRIBED — certifier]`

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

### EFF.LIFTCORNER.s2of2.45  [scope record]  `[TRANSCRIBED — certifier]`  *(CHAIN-P, CHAIN-F — TERMINAL)*

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

### EFF.LIFTCORNER.s2of2.46  [instrument-record]

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

**TEETH:** **both re-derivations independently reproduced at compile time and both are correct** — (T1)'s ceiling argument at `.39` and (T4)'s arithmetic at `.42`. `runs/cert5/P4_rm1_output.log` exists. Disposition `accepted-with-decorrelation-supplied`.

---

## 3. XREF verification ledger

All checks run at compile time (2026-08-14) with fixed-string `grep -cF`, counts and first lines recorded; multi-line quotations verified under whitespace normalization and marked as such; commit pins by `git cat-file -t`; artifacts by existence.

### 3.1 Positive designation XREFs

`[TABLE — compiler ledger]`

| ID | Target file | Verified designation | count | line | Role |
|---|---|---|---:|---:|---|
| Y01 | `ITERLAWN_PROOF_2026-08-08.md` | `* Lifts: Φ₁ := the STANDARD LIFT of ψ₀ (grb_order2_check :499–507); for` | 1 | 163 | the S0.1 rider `.01` rewrites |
| Y02 | `ILNRES_2026-08-08.md` | `Extend the [IL] L7 Case-II analysis to an arbitrary lawful lift Φ₁′ = Φ₁ + (π-excess) at g₀ = 1 ∧ δ₁ = 1, then ride S0.1's verbatim propagation` | 1 (normalized) | 180 | the spec deliverable quoted at `.03` |
| Y03 | same | `S1's FOUR-MEMBER residual list is COMPLETE relative to the sources` | 1 | 288 | the completeness sentence `.05` will not collide with |
| Y04 | `ITERLAWLIFT_CORNER_2026-08-08.md` | `the honest OPEN displayed lemma **(ITER-LAW-LIFT)**: ITER-LAW for every lawful monic lift Φ₁` | 1 (normalized, spans lines 35–36) | 35 | the wave-18 residual quoted at `.03` |
| Y05 | `ILNRES_2026-08-08.md` | `nothing is claimed for any non-canonical lawful lift at any level` | 1 (normalized) | 28 | the “at any level” clause of `.04` |
| Y06 | `ITERLAWN_PROOF_2026-08-08.md` | `m ≥ 2: **OPEN.**` | 1 | 806 | the inherited conditionality of `.01`/`.45` |
| Y07 | `GRTW2_PROOF_2026-08-08.md` | `the accepted LIFTCORNER's shift-descent` | 1 | 1351 | FC-1's quoted supplier acknowledgement (`.19`) |
| Y08 | `ITERLAWN_PROOF_2026-08-08.md` | `WELL-DEF` | 32 | — | AC-1/AC-4's constructor target |
| Y09 | same | `### S4.2 L6-(n) (ANCHOR-VAL = the ε-chain; all n, no engine, no DCX)` | 1 | 575 | the degree telescope's home |
| Y10 | same | `## ★ FOLD ANNEX (orchestrator, 2026-08-07): THE NR-1 RIDER-REWRITE, LICENSED AND EXECUTED ★` | 1 | 1518 | FC-2's LANDED execution (`.20`) |
| Y11 | same | `### S4.1 Lemmas REALIZE-(m), WELL-DEF-(n), READ-ADD-(m)` | 1 | 499 | AC-4's constructor subgraph |
| Y12 | same | `## S7. THE CONDITIONALITY LEDGER (the exact grade of every clause, per rung)` | 1 | 1148 | the 22-row sweep AC-1's certificate pins and AC-4 supersedes |
| Y13 | `docs/PROJECT_STATE.md` | `row 19 also ((Φ₁-OPACITY), numerical certificate` | 1 | 3996 | the certification ledger row tracking the arc |
| Y14 | `ITERLAWN_PROOF_2026-08-08.md` | `194 raw hits on 147 lines, 194/194 mapped, ZERO` | 1 | 1233 | the machine census AC-4 uses (`.31`) |
| Y15 | same | `m = 1: PROVED — [IL3] DIGIT-SPLIT + DEV-1` | 1 | 794 | the proof status AC-4 quotes (`.34`) |
| Y16 | same | `### S4.6 The engine (RM-m), and Cases II-1/II-2/II-3 — PROVED generic MODULO (RM-(n−1)), off DCX-(n)` | 1 | 777 | the (RM-m) box carrying the four interface clauses |
| Y17 | same | `ITER-PKG-2` | 1 | 1458 | the package AC-5 constructs. Its schematic form `(ITER-PKG-r)` is graded at ITERLAWN line 279: `STATED; base r = 1 ACCEPTED, r = 2 = [IL3] 0/2` (count 1) |
| Y18 | same | `{e₀ = 1 ∧ d₀ ≥ 2} general inputs enter [IL3]'s fenced DEV-1 corner —` | 1 | 803 | the scope tension of `.40` (OPEN-CALL 3) |
| Y19 | same | `### S4.4 CASE-SPLIT-(n) (the exact partition at the top of rung n)` | 1 | 709 | AC-5's sweep target (NEAR-MISS resolution, `.45`) |
| Y20 | same | `### S4.5 W-MULT-(n), Case I (single top digit) — PROVED, generic` | 1 | 750 | AC-5's sweep target |
| Y21 | same | `**Lemma READ-ADD-(m) (read additivity with strict-above kill; generic).**` | 1 | 564 | NEAR-MISS resolution for `READ-ADD-(1)` (`.43`) |

### 3.2 NEAR-MISS dispositions (v3 rule 15)

`[TABLE — compiler ledger]`

| Cited as | `grep -cF` | Verified referent | Disposition |
|---|---:|---|---|
| `CASE-SPLIT-(2)` (`.45`) | 0 | `CASE-SPLIT-(n)` at `ITERLAWN_PROOF_2026-08-08.md:709`, count 1, with the n = 2 instance named at line 737 (“At n = 2 this is [IL3] CASE-SPLIT verbatim”) | NEAR-MISS: instantiated name vs schematic name; referent unambiguous |
| `READ-ADD-(1)` (`.43`) | 0 | `READ-ADD-(m)` at `:499` and `:564`, count 1 each; the lemma's own title carries “strict-above kill” | NEAR-MISS: same pattern |
| `f\,\widehat C_m=R+Q\Phi_m` (`.34`) | 0 as LaTeX | the source renders it in an ASCII box: `f·Ĉ_m = R + Q·Φ_m,   w_m(R) ≥ λ + γ_{m+1},` inside Y16's display, count 1 | NEAR-MISS: notation transliteration, referent verified line by line |

### 3.3 Artifact and commit pins

`[TABLE — compiler ledger]`

| ID | Pin | Verified |
|---|---|---|
| Q01 | `runs/cert/C1_liftcorner_output.log`, `runs/cert2/E1_liftcorner_output.log`, `runs/cert4/P3_opacity_output.log`, `runs/cert5/P4_rm1_output.log` | ALL FOUR EXIST |
| Q02 | `c6097d7` (PE8), `9b5175c` (PE9), `adc6cf3` (GRTW2 acceptance), `5054d69` (FC-2), `08f61e9` (this note's acceptance), `dafc0b5` (the seal) | ALL SIX resolve as commits |
| Q03 | `LIFTCORNER_passPE8_report.md`, `LIFTCORNER_passPE9_report.md` | BOTH EXIST |
| Q04 | `verification/openmath/liftcorner_checks.py` md5 `ccb4351c92573f5f962cae4ae952d8dd` | MATCHES the acceptance record's figure |
| Q05 | children table `nodes reconciled: 752   children enumerated: 5336` | MATCHES the acceptance record's `752/5,336/0` |
| Q06 | PE9's p = 7 fresh-instance leg (2,178 nonzero digits, 0 violations) | **UNPINNED** — no committed artifact in `verification/openmath/` records it; only the PE9 report does. OPEN-CALL 5 |
| Q07 | AC-1's 57-pair pre-proof numerical certificate | **NEVER EXECUTED** — no corresponding artifact exists; superseded by AC-5's proof (`.24`) |

### 3.4 Verified NEGATIVE edges

`[TABLE — compiler ledger]`

| ID | Check | count | Meaning |
|---|---|---:|---|
| N1 | `grep -cF 'OPACITY' ITERLAWN_PROOF_2026-08-08.md` | 0 | AC-1/AC-4/AC-5 UNLANDED on ITERLAWN |
| N2 | `grep -cF 'AC-4' … ` / `grep -cF 'AC-5' …` | 0 / 0 | same, by annex name |
| N3 | `grep -cF 'LIFTCORNER' ILNRES_2026-08-08.md` | 0 | ILNRES's NR-1 ledger entry unfolded; its one `LIFT-CORNER` hit is the S5.1 charge heading |
| N4 | `grep -cF 'SUSPENDED' ITERLAWN_PROOF_2026-08-08.md` | 0 | the fold annex records neither AC-1's suspension nor AC-5's reinstatement |

---

## 4. Effective supply / consumption ledger

`[TABLE — compiler ledger]`

| Conclusion | Effective supply | Surviving fence | Protocol status |
|---|---|---|---|
| the note's five accepted theorems (`.18`) | shard 1 `.35`, `.54`, `.57`, `.60`, `.61` | at the note's own conditionality; COR 2's (a)/(b) owed | **ACCEPTED 2/2**; W-2 cap re-read as accepted-supplier (`.19`) |
| the S5 rider rewrite on ITERLAWN's Φ₁ axis | `.01`, executed by FC-2 | Φ₁ axis only; deeper noncanonical keys excluded (`.05`) | **LANDED** (Y10); suspension/reinstatement **UNRECORDED** there (N4) |
| CONTENT at integral-key scope | `.26` (AC-2) | Φ ∈ 𝒪[x] | **APPENDED here; UNLANDED anywhere else** (no other note carries AC-2) |
| READ-EQ's degree comparison | `.27` (AC-3) | holds at d₀ = 1 | **APPENDED here** |
| constructor/telescope Φ₁-opacity | `.32`, `.33` (AC-4) | Θ asserted only on displayed normal forms | **APPENDED here; ITERLAWN not informed** (N1) |
| (RM-1-TRANSPORT) | `.35`, `.39`–`.43` (AC-5) | the four interface clauses only; NOT full R,Q equality (`.44`) | **APPENDED here; ITERLAWN not informed** (N1) |
| all-rung PROP | `.45` | at ITERLAWN's own conditionality, whose (RM-m) is OPEN at m ≥ 2 (Y06) | **DISCHARGED conditionally**; transcription-confirm owed (`.46`) |

---

## 5. NON-IMPORTS

**NI-1 — the note edits no ledger.** `.03`: “this note edits no ledger.” The ITERLAWN fold annex is a separate, later, append-only act by the orchestrator, not an edit by this note.

**NI-2 — this unit does not choose between the two NR-1 readings.** `.04`: “The two readings live in different notes of record, and this unit does not choose between them.”

**NI-3 — no residual is created or repriced.** `.05`: “this unit has no authority to create a residual … Until ILNRES rules, **nothing here re-prices anything**”.

**NI-4 — FC-1 corrects the W-2 cap and NOTHING else.** `.25`: “FC-1 is explicitly a correction only of “the W-2 cap”; it changes the supplier grade from \(0/2\) to accepted and does not erase the `[r4, F4-6]` scope fence.”

**NI-5 — Θ does not commute with arbitrary division.** `.32`: “It is not asserted to commute with arbitrary division or re-development in \(\mathcal O[x]\).”

**NI-6 — full R,Q proof-data equality is neither proved nor claimed.** `.44`.

**NI-7 — AC-5 enlarges no ITERLAWN perimeter.** `.45`: “This does not enlarge ITERLAWN’s DCX, higher-\((RM)\), T-scope or deeper-noncanonical-lift perimeter.”

**NI-8 — the deeper-level fence survives every repair.** `.45`: “The fence excluding independently chosen noncanonical higher keys remains unchanged.”

Accordingly **no edge is created** from this shard to ITERLAWN's DCX layer, to higher (RM-m), to T-scope, to deeper noncanonical lifts, to ILNRES's residual list, or to any statement of complete R,Q invariance.

---

## 6. TEETH inverse inventory

This shard's material is a record surface plus transcribed external proof, so its teeth are of four kinds: pins (verified in §3), orchestrator re-derivations (`.29`, `.37`, `.46`), arithmetic audits (below), and the two consecutive clean passes.

### 6.1 Obligation → guarded units

`[TABLE — compiler ledger]`

| # | Obligation | Guarded units | Disposition |
|---:|---|---|---|
| 1 | PE8 CLEAN + PE9 CLEAN (the acceptance bar) | `.17`, `.18` | **AUDIT / in-house hostile pass** — two consecutive clean, model-diverse-arm passes |
| 2 | PE9's fresh-instance p = 7 leg | `.17` | executable regression, **UNPINNED** (Q06) |
| 3 | the sealed runner's machine record | `.11`, `.18` | executable regression, re-verified (md5, 25,409/0) |
| 4 | the children generator + A7 | `.18` | executable regression, re-verified (752/5,336) |
| 5 | C1's 5 findings adjudicated by E1 | `.21`–`.28` | **AUDIT / decorrelated-model audit**: 2 REAL repairs, 1 OBSTRUCTED, 2 rebutted |
| 6 | AC-1's 57-pair numerical certificate | `.24` | **preregistration, superseded-unexecuted** |
| 7 | AC-4's census partition | `.31` | arithmetic recount ✓ against ITERLAWN's own census (Y14) |
| 8 | AC-4's Θ-transport sublemma | `.32`, `.33` | derivation, transcribed; telescope arithmetic re-verified |
| 9 | AC-5's (T1)–(T6) | `.39`–`.43` | **arithmetic recount** ✓ every step; orchestrator re-derivation independent (`.46`) |
| 10 | the four consumed interface clauses vs ITERLAWN's box | `.41`, `.43` | verified line by line against Y16 |
| 11 | the three landed/unlanded protocol facts | `.19`, `.20`, `.36`, `.46` | 1 LANDED (Y10), 3 UNLANDED (N1–N4) |
| 12 | the archive's three inside corrections | `.12`–`.15` | dead-text discipline; terminals in shard 1 |

**Zero-orphan check:** 12 obligations, all mapped, 0 orphans. Units with no tooth of their own: `.01`–`.10`, `.16`, `.30`, `.38`, `.44` (scope/record/preamble units), guarded by the acceptance record and the pin ledger.

### 6.2 Arithmetic audit summary (v3 rule 22)

- **194** = 88+21+53+8+18+6 ✓, and every class count matches ITERLAWN's own census (Y14) exactly
- **5 findings** = 1 OBSTRUCTED + 1 RESOLVED-ALREADY + 2 REAL + 1 ARTIFACT ✓ (`.21`)
- **9 passes / 7 rounds** ✓ across `.07` and `.17`
- **57 pairs** = 56 orbit towers + 1 counter-instance ✓ (`.24`); **22 sites** = ITERLAWN S7's data rows, recounted ✓
- **8 occurrence sites** enumerated in the landed fold annex ✓ (`.20`)
- **(T1)**: gcd(e₀,h₀) = 1 ⇒ e₀·amin(k) + kh₀ ≥ e₀h₀+1 = W+1 ✓; k = 0 term ≥ e₀(h₀+1) ≥ W+1 ✓
- **(T4)**: (μ−W) + (W+1) = μ+1 ✓ — the single unit of strictness the whole discharge rests on
- **(T5)/(T6)**: R″ + Q″Φ₁″ = (R″−A) + (Q″−B)Φ₁′ ✓
- **telescope**: Σ_{j<n} s_{j+1} deg Φ_j ≤ deg Φ_n − d₀ < deg Φ_n ✓
- **AC-3**: at d₀ = 1, e₀ < deg Φ′ = e₀ is false; s·d₀ < e₀·d₀ is true ✓

**Zero arithmetic discrepancies found.**

---

## 7. BOUNDARY SELF-AUDIT

### 7.1 The rule applied

Two genres, two rules. For the **record surface** (`.01`–`.21`, `.29`, `.30`, `.37`, `.38`, `.46`), tag-sparse, the shard-1 rule applies: a unit is the smallest span a chapter could cut and still state correctly, with every dated superseding bracket its own unit. For the **transcribed certifier proof** (`.22`–`.28`, `.31`–`.36`, `.39`–`.45`), boundaries are read off the source's own structure — numbered findings, named annexes, `\tag{}`ed displays and bold-headed sections — because the certifier wrote them as a structured document.

### 7.2 Boundaries drawn, arguable ones both ways

1. **The STATUS BLOCK → five units (`.07`–`.11`) + a preamble (`.06`).** *Alternative:* one unit. *Chosen because* the block's own standing rule is “edit these five lines; do not grow a sixth” — the five-ness is load-bearing — and because the five bullets have different truth conditions at HEAD (ARC spent, COUNTER superseded, PROVED still correct, CONDITIONALITY partly discharged, NEXT/AUDIT stale).
2. **The archive → a preamble unit (`.12`) + three dead units (`.13`–`.15`).** *Alternative:* one unit for the whole dead region. *Chosen because* three corrections apply INSIDE it and must point at specific members, and because `.15` carries one live fact (PE3's blast-radius finding) recorded nowhere else.
3. **AC-1 → two units (`.23` annex, `.24` certificate).** *Chosen because* the certificate is a `preregistration` with its own truth conditions and its own (unexecuted) fate; folding it into the annex would hide that it was never run.
4. **AC-4 → six units (`.31`–`.36`).** *Chosen because* its census, its sublemma, its proof, its obstruction, its named residual and its sweep have four different types and four different fates under AC-5.
5. **AC-5 → seven units (`.39`–`.45`).** Boundaries follow the tags: (T1) at `.39`, (T2) at `.40`, the input setup at `.41`, (T3)–(T6) at `.42`, the four clauses at `.43`, the fence at `.44`, the sweep at `.45`. *This is the one place in either shard where the source's own tags fix the boundaries*, and they were followed exactly.
6. **The three orchestrator parentheticals → three separate units (`.29`, `.37`, `.46`), not footnotes.** *Arguable:* they read as parenthetical asides. *Chosen because* they carry an INDEPENDENT warrant (a second model's re-derivation before transcription) and a ledger line, which is different in kind from the certifier's own claim. A chapter cut needing “who checked this” must be able to cut them.
7. **`.01` (the consequence display) kept separate from `.02` (the F4-6 strike).** *Arguable:* the strike sits immediately below the display and refers to what followed it, not to the display itself. *Chosen* on that exact ground: the strike's target is the sentence AFTER the display, so merging would mis-target the supersession.

### 7.3 Merges deliberately NOT made

- `.19` (FC-1) and `.20` (FC-2) are adjacent annexes of the same date but different objects (a cap re-reading vs a license execution) with different terminals (FC-1 terminal; FC-2 superseded twice).
- `.32` (the sublemma statement) and `.33` (its proof) are separate because AC-5 cites the STATEMENT (via `.41`'s “AC-4’s \(m=1\) constructor calculation”) without the proof.
- `.35` ((RM-1-TRANSPORT) as stated by AC-4) is NOT merged into `.43` (its proof by AC-5): they are in different annexes by different runs, and the SERIES structure depends on keeping them apart.

### 7.4 Rules that fought this genre

- **Rule 3's authorship question is not answered by the template.** Units `.22`–`.28`, `.31`–`.36`, `.39`–`.45` are *in* this note but *by* the certifier. The template's TYPE ENUM has no author field, so this shard adds the marker `[TRANSCRIBED — certifier]` to every such unit. Recommended for the format: an explicit AUTHORSHIP field wherever a note carries transcribed external results, since the DAG edge “LIFTCORNER supplies X” is false for all fifteen of them while “LIFTCORNER carries X” is true.
- **Rule 25 (CHAIN with TERMINAL) is indispensable here and would have been actively misleading if applied naively**: CHAIN-P and CHAIN-F both have a *middle* link (AC-1) that a careless reader would take as current, and both terminate in a reversal.
- **Rule 28 (SERIES)** correctly separated the three certifier adjudications, which share one ledger row and would otherwise merge into an unreadable “opacity record”.
- **Rule 15 (NEAR-MISS)** fired three times, all from the same cause: the certifier instantiates schematic names (`CASE-SPLIT-(n)` → `CASE-SPLIT-(2)`) and transliterates ASCII displays into LaTeX. None is an invention; all three referents verify.

---

## 8. SHARD NOTES

**Cross-shard supersessions this shard EXPORTS into shard 1:** six. AC-2 (`.26`) → `s1of2.34`; AC-3 (`.27`) → `s1of2.55`; AC-1/AC-4/AC-5 (`.23`, `.36`, `.45`) → `s1of2.63` (CHAIN-P); the acceptance record (`.17`) → `s1of2.02` and the six grade-box entries `s1of2.65`–`.70`; FC-1 (`.19`) → `s1of2.02` and `s1of2.72`; AC-4's census pin (`.31`) → `s1of2.64`.

**Cross-shard supersessions this shard RECEIVES from shard 1:** none that change a statement. Three shard-1 chains have restatement sites here: CHAIN-A and CHAIN-B terminals are quoted inside the archive corrections (`.12`), and shard 1 `.13`'s F5-1 edit is what shaped `.09`'s PROVED line.

**Boundary units:** none split across line 1167/1168. The break is a `##` section boundary and is independently corroborated by ITERLAWN's fold annex citing “lines 1168–1176” (Y10).

**Numbering:** `EFF.LIFTCORNER.s2of2.01`–`.46`, contiguous. The merge run must preserve: the five CHAIN tables with TERMINALs, the three SERIES declarations, the `[TRANSCRIBED — certifier]` authorship markers on the fifteen certifier units, and the four FREEZE PREDICATES (in particular FREEZE-1a, the second text freeze at line 1495, which shard 1 does not carry).

---

## 9. Self-audit and OPEN-CALLS

### 9.1 Resolved compilation calls

- The certifier annexes are compiled as units of this note with explicit authorship markers, never as LIFTCORNER's own mathematics. The distinction changes seven DAG edges.
- Five CHAINs were reconstructed with TERMINALs; two of them (CHAIN-P, CHAIN-F) terminate in a REVERSAL of their middle link, so a compilation that stopped at AC-1 would be wrong at HEAD.
- Four FREEZE PREDICATES were separated, including a second text freeze (FREEZE-1a) that shard 1 has no occasion to notice.
- AC-1's (Φ₁-OPACITY) is recorded as **never proved and superseded as the wrong statement**; the two lemmas that were proved (`.32`, `.35`) are recorded under their own names. A consumer citing “(Φ₁-OPACITY) proved” would be wrong.
- The inherited conditionality of the discharged PROP is made explicit and verified: ITERLAWN's (RM-m) is OPEN at m ≥ 2 (Y06), and ITER-PKG-2 rides [IL3] at 0/2 (ITERLAWN line 279).
- Every arithmetic claim in the certifier annexes was recomputed; all reproduce. The single load-bearing step is (T4)'s +1, traced to S1's lawfulness bound via the gcd argument.
- 21 positive XREFs, 3 NEAR-MISS resolutions, 7 pin classes and 4 negative edges verified.

### 9.2 OPEN-CALLS

**OPEN-CALL 1 — the entire (Φ₁-OPACITY) program is unlanded on ITERLAWN, and the annex it repairs is landed there. FOR-0c/protocol — NEEDS ASVIN.**
FC-2's rider rewrite IS landed on `ITERLAWN_PROOF_2026-08-08.md` (Y10). AC-1 suspended that landed rewrite; AC-5 reinstated it; AC-4 additionally certifies four ITERLAWN objects Φ₁-opaque. **None of the three annexes is recorded on ITERLAWN** (N1, N2, N4), and AC-5's own last line says “transcription-confirm owed”. Net state is favorable, so nothing on ITERLAWN is currently false — but (i) ITERLAWN's rung-≥2 propagation now depends on a lemma proved in another note's annex, with no pointer; and (ii) the S4.1/WELL-DEF/C_k/TRUNC/L6 opacity certification exists nowhere in the note it certifies. Landing AC-4+AC-5 on ITERLAWN is a protocol action.

**OPEN-CALL 2 — ILNRES has not ruled on the (a)/(b) alternative. FOR-0c.**
`.05` flags an ILNRES-side erratum candidate with a clean binary: is “at any level” (a) a scope fence, in which case the Φ₁ corner is all of NR-1, or (b) a live conditionality, in which case NR-1 has a fifth member and ILNRES S7's completeness sentence needs amending? Verified unanswered: `grep -cF 'LIFTCORNER' ILNRES_2026-08-08.md` = 0. This is a live DAG edge, not a footnote — the answer determines whether NR-1 is discharged.

**OPEN-CALL 3 — does AC-5's e₀ = 1 termination argument reach ITERLAWN's fenced DEV-1 corner? FOR-0b/0d.**
ITERLAWN's (RM-m) STATUS box fences m = 1: “proved for e₀ ≥ 2, and at e₀ = 1 ∧ d₀ = 1 (junkΦ ≡ 0); at {e₀ = 1 ∧ d₀ ≥ 2} general inputs enter [IL3]'s fenced DEV-1 corner — open there” (Y18). AC-5's (T2) proof asserts termination at e₀ = 1 via the lex measure “including the flat case needed for the strict-excess correction below”. **Two readings:** (i) AC-5 supplies exactly the termination ITERLAWN's corner lacks, so the fence narrows; (ii) AC-5's argument covers only the strict-excess division it needs, and ITERLAWN's corner is untouched. Neither text decides. LIFTCORNER's own corner is unaffected either way (e₀ ≥ 2 by the S4 setting; δ₁ = 1 empty at e₀ = 1), so this is a question about what AC-5 gives ITERLAWN, not about this note's claims.

**OPEN-CALL 4 — PE3's blast-radius finding lives only inside dead archive text. FOR-0b.**
The r3 STATUS LINE (`.15`, DEAD) records that PE3 found “READ-EQ's one pass sits entirely in the deg a = 0 stratum, where the repaired proof shows there are no q-children at all, so the r0 defect could never have propagated there”. That is a substantive fact — it bounds the blast radius of the arc's only CRITICAL — and it appears nowhere in the live text. **Proposed disposition:** a one-line minors-only rider carrying the finding into the STATUS BLOCK PROVED bullet. Compiler suggestion, NOT source text; needs the note owner.

**OPEN-CALL 5 — PE9's p = 7 leg is unpinned. FOR-0b (bookkeeping).**
The acceptance record cites “a fresh-instance leg at p = 7 outside the sealed battery's roster: 2,178 nonzero digits, 0 violations”. It is the only evidence in the note outside the sealed roster (p ∈ {2,3}) and the children generator (p ∈ {2,3,5}), which makes it the note's best generalization evidence — and it is backed by no committed artifact, only by the PE9 report. Disposition `UNPINNED` per v3 rule 23. Committing the p = 7 run would close it.

**OPEN-CALL 6 — (T4) cites (T3), which it does not use. FOR-0b (wording).**
AC-5 writes “DIGIT-SPLIT’s product bound together with (T1) and (T3) gives \(\nu(H)\ge\nu(Q'')+\nu(\Delta)\ge(\mu-W)+(W+1)=\mu+1\)”. The inequality needs the quotient-weight bound \(w_1(Q'')\ge\mu-W\) (displayed immediately above (T3)) and (T1); **(T3) is the prescribed READ and enters only at interface clause 4.** The arithmetic is correct (recomputed at `.42`); the citation names the wrong neighbour. A minors-only fix in transcribed text is a note-owner call, not a compiler edit — and since the annex is “transcribed unaltered”, the correction would have to be a rider, not an edit.

### 9.3 Fidelity audit (compile-time, mechanical)

- Every CANONICAL STATEMENT is verbatim from `LIFTCORNER_2026-08-08.md` lines 1168–2083, or explicitly `[ASSEMBLED]` (three units: `.12`, `.14`, `.33`, whose components are quoted individually and whose seams are named).
- `…` marks every truncation (`.13`, `.14`, `.15`, `.25`, `.33`, `.34`, `.35`, `.39`, `.40`, `.45`).
- The certifier annexes' LaTeX is reproduced in source form, tags included; no display was transliterated, prosified or re-typeset.
- No quantifier, index, inequality, tag number, or scope was altered. Where this compilation computes something the source does not (the (T1)/(T4)/telescope re-derivations, the 194 cross-check, the d₀ = 1 counterexample), it is in a TEETH field and marked as recomputed.
- Cross-file quotations were each verified at count 1; the four spanning source line breaks (Y02, Y04, Y05, and the ITERLAWN r4 erratum used in shard 1) are recorded as verified under whitespace normalization rather than by single-line `grep -F`.
- Three NEAR-MISS designations are recorded as such (§3.2) — none suppressed, none emitted as a clean XREF, none invented.

EFF-LIFTCORNER-s2of2 COMPILED: 46 statements / 25 xrefs verified / 6 open calls
