# EFF-LIFTCORNER-s1of2 — CANONICAL EFFECTIVE-SPECIFICATION SHARD

**COMPILED-BY: opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). CODEX CROSS-READ OWED (post-reset).**

## 1. Shard header

**Source note:** `lean/notes/openmath/LIFTCORNER_2026-08-08.md` (2,083 lines / 133,230 bytes).

**HOME range:** source lines 1–1167 inclusive (title + machine-leg record + the seven repair-round records + sources of record + FENCES + §S1 the corner orbit and transport frame + §S2 the sealed prediction sheet + §S3 the VERDICT + §S4 the compose setting + §S4.1 (TAIL-STAB) + §S4.2 (READ-EQ) + §S4.3 THEOREM/COR 1/COR 2/PROP/grade box). Later text (§S5, the acceptance record, the FC annexes, the three 2026-08-12 certifier adjudications AC-1…AC-5) is used ONLY to resolve material homed in that range; it is homed in shard 2.

**HEAD blob hash:** `d93c2aa253cdf5192f2e1525aa9f7b412b85b925` (fresh `git hash-object` at compile time; clean in the working tree; last touched by commit `33225dd9`).

**Compilation context:** `docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md`, Stage 0a; governing template `spec/EFF_TEMPLATE_v2.md` AT HEAD (rules 1–28). Temporary IDs `EFF.LIFTCORNER.s1of2.<nn>`; the merge run renumbers.

**GENRE: TAG-SPARSE PROSE PROOF + SEALED-PREREGISTRATION NUMERICS.** `grep -c '\tag{'` over the whole note = **6**, and all six lie in the AC-5 annex (shard 2); the HOME range carries **zero** `\tag{`. Statement boundaries in this shard are therefore CHOSEN, not read off display tags — §7 below is the mandatory BOUNDARY SELF-AUDIT (template rule 9/v3). The note names its own genre in its header:

> “Genre: sealed-preregistration
> numerics (two-commit seal) + a conditional COMPOSE (S4; written only on a
> 0-violation verdict, per the probe-first discipline).”

The consequence for compilation is that this shard carries three distinct unit populations that must not be conflated: **preregistrations** (S2's sheet, written before the run), **run-records** (S3's verdict, read off committed artifacts), and **proof units** (S4's lemmas) — template v3 rule 19's three-way split, which this note's own two-commit seal makes literal rather than notional.

### FREEZE PREDICATES (template v3 rule 21 — three independent freezes, never one standing for the others)

**FREEZE-1 (text freeze, out of range, governs the whole shard).** The acceptance record (line 1433):

> “**THIS NOTE IS ACCEPTED at 2/2** — two consecutive clean hostile passes:
> PE8 (report c6097d7, CLEAN 0C/0G) and PE9 (report 9b5175c, CLEAN 0C/0G,
> including a fresh-instance leg at p = 7 outside the sealed battery's
> roster: 2,178 nonzero digits, 0 violations, the PE1 counter-instance
> identity re-multiplied exact).”

reinforced by the ANNEX heading (line 1457) “**ANNEX (dated appends; the frozen body is not edited)**” and by the 2026-08-12 adjudication's own sentence (line 1495) “Everything above this heading is byte-untouched by this append.” Pins verified: `git cat-file -t c6097d7` = commit; `git cat-file -t 9b5175c` = commit.

**FREEZE-2 (instrument freeze — the SEALED runner, two-commit seal).** Header lines 11–13 and 25–31:

> “**Machine leg:** `verification/openmath/liftcorner_checks.py` (this header +
> the runner commit BEFORE any full run; verdict appended in commit 2 from the
> artifacts `liftcorner_checks_output.txt` / `liftcorner_checks_results.json`).”

> “[r3] **BOTH MACHINE LEGS ARE BYTE-FROZEN AT r3** — repair round r3 is
> note-level only, and PE3 verified both legs before the round: sealed runner
> `git diff dafc0b5 HEAD` = **0 bytes**, md5 still
> `ccb4351c92573f5f962cae4ae952d8dd`, exit 0 at 25,409/0”

Pin verified at compile time: `md5sum verification/openmath/liftcorner_checks.py` = **`ccb4351c92573f5f962cae4ae952d8dd`** — byte-for-byte the note's figure, re-derived independently of the note's own tables. `git cat-file -t dafc0b5` = commit.

**FREEZE-3 (instrument freeze — the POST-HOC children generator, frozen only from r3 onward).** This is a *different* freeze with a *later* start date and an explicitly non-sealed status; conflating it with FREEZE-2 is the error the note's own r3 F-C corrects. Header lines 14–24:

> “[r1] A SECOND, post-hoc machine leg was added at repair round r1 and is NOT
> part of the sealed prediction battery: `liftcorner_tailstab_children.py` +
> its committed output `liftcorner_tailstab_children_table.txt` — the
> examples-first child-type table the repaired S4.1 induction is derived from
> (disclosed as written AFTER the refutation, hence evidence for a repair, not
> a prediction).”

Both files verified present; `md5sum liftcorner_tailstab_children_table.txt` = `bf9106e7edc535edf2b7a6b6a64f0f55` (2,986 lines) — recorded here because the note pins this leg by *reproducibility* (`diff` empty) rather than by md5, so a downstream re-runner needs a hash of record.

### Governing effective-text record (DERIVED — the note states no single "the effective text is …" sentence)

Four source facts fix it, and they agree.

**(i) The seven repair rounds were applied IN-TEXT, strike-and-replace, never by append.** r2's round record (lines 132–134):

> “Dispositions, each edit carrying a dated
> `[r2, G#]` bracket, strike-and-replace (the refuted r1 wording is quoted
> inside the bracket that supersedes it, never silently deleted)”

r3 (lines 176–178) and r4 (lines 229–232) repeat the formula verbatim for their own brackets. So every `[r1, F#]` / `[r2, G#]` / `[r3, F-#]` / `[r4, F4-#]` / `[r5, F5-#]` / `[r6, F6-#]` / `[r7, F7-#]` bracket inside lines 1–1167 is **already-landed text**, and the wording quoted INSIDE such a bracket is **dead** — retained, byte-intact, only because the note's discipline never deletes.

**(ii) The refuted wording inside a bracket is never live.** The archive preamble states the rule for the extreme case (lines 1269–1272, out of range):

> “Nothing
> between the markers is live: it is superseded wholesale by the five-line STATUS
> BLOCK above, and is kept only because this note's discipline never silently
> deletes superseded wording.”

**(iii) Sealed text is NOT edited even when refuted; the correcting bracket is the record.** [r4, F4-5] (lines 978–980):

> “**S1's CANDIDATE display is
> sealed pre-run text and is NOT edited**: it writes this cocycle as `c′(γ,γ′)`,
> and this bracket is the correction of record for it”

and, for the runner's own docstring, [r3, F-A, fence disclosure] (lines 530–534):

> “it is
> BYTE-FROZEN by the two-commit seal and is therefore NOT corrected — the seal
> outranks the wording, and this bracket is the correction of record.”

**(iv) After acceptance the body is closed to everything but dated appends** (FREEZE-1 above), and five out-of-range dated appends land ON in-range sentences.

**EFFECTIVE TEXT FOR THIS SHARD = lines 1–1167 exactly as written (r1–r7 brackets already landed; text quoted inside a superseding bracket is dead), READ AS CORRECTED by the out-of-range dated appends wherever they name an in-range sentence.** Five such appends land in this shard's range (FC-1, AC-1, AC-2, AC-3, AC-4/AC-5); each is applied at its unit and tabulated below. No in-range sentence is deleted by any of them.

### Supersessions REACHING INTO this shard from out of range

`[TABLE]`

| In-range target | Home lines | Out-of-range instrument | SUPERSESSION KIND | Effect |
|---|---:|---|---|---|
| CONTENT (sub-lemma) | 608–611 | **AC-2** (1541–1552) | replacement | “For monic \(\Phi\)” re-displayed at integral-key scope; proof replaced; consumer sweep says every consumer survives unchanged |
| §S4.2(a) “s < e₀ < deg” | 945 | **AC-3** (1560–1573) | replacement | the degree comparison corrected to \(\deg(\Phi_0^s)=sd_0<e_0d_0\); repairs the literal failure at \(d_0=1\) |
| PROP (all-rung propagation) | 1034–1042 | **AC-1 → AC-4 → AC-5** | scope-pin → scope-pin → license | SUSPENDED, then NARROWED to the (RM-1) interface, then the suspension LIFTED. See CHAIN-P below |
| Grade box “attempt 0/2”, all six entries | 1071–1145 | ACCEPTANCE RECORD (1433) | counter re-reading | 0/2 → **ACCEPTED 2/2**; the in-range “PE8 … is the next acceptance attempt” is spent |
| “GRTW2 is itself 0/2, so **the unit's grade is CAPPED at that consumption**” | 1161–1163 | **FC-1** (1459–1471) | counter re-reading | “Wherever this note bills GRTW2 at "0/2 / arc open" … read: capped by an ACCEPTED supplier at its fenced scope” |
| [r4, F4-4]'s “22 rows” sweep as the census of record | 1045–1047 | **AC-4** (1620) | scope-pin | “This adjudication uses ITERLAWN’s machine census of record, not the superseded 22-row or 23-row hand tables.” The 194-hit machine census replaces it |

**CHAIN-P (template v3 rule 25 — PROP's four-layer supersession, TERMINAL marked).**

`[TABLE]`

| Link | Instrument | Reading it imposes on PROP |
|---:|---|---|
| 1 | frozen S4.3 text (1034–1042) | “the discharge lifts to every rung AT [ILN]'s OWN conditionality”, with the rung-≥2 clause-(ii) census named a VERIFY-TARGET |
| 2 | AC-1 (1509–1517) | “The all-rung force of three earlier sentences is SUSPENDED”; the missing lemma named (Φ₁-OPACITY) |
| 3 | AC-4 (1618–1815) | constructor/telescope subgraph PROVED opaque; “AC-1 is narrowed but not discharged”, obstruction surviving at exactly one site, ITERLAWN S4.6's (RM-1) |
| 4 | **AC-5 (1833–2070) — TERMINAL** | (RM-1-TRANSPORT) PROVED; “**LIFTCORNER PROP:** its rung-\(\ge2\) suspension is lifted. The all-rung propagation now follows at ITERLAWN’s own conditionality.” |

The reading a chapter cut must use is **link 4**. Links 2 and 3 are live history, not live scope: quoting AC-1's suspension as current would be an error of the same kind as quoting the grade box's 0/2.

### Supersession CHAINS internal to this shard (all four are multi-layer; TERMINAL marked)

`[TABLE]`

| Chain | Layers, in source order | TERMINAL |
|---|---|---|
| **CHAIN-A (the assert pair)** | r0 description (“ψ₁ bytes equal, K₂ arithmetic representation shared”) → [r1, F4] promotes (i) → [r3, F-A] inverts, promotes (ii) → [r4, F4-1] demotes BOTH → [r5, F5-2] re-scopes F4-1's parenthetical to the ASSERTS | **[r4, F4-1] as re-scoped by [r5, F5-2]** (`.25`, restated at `.08`) |
| **CHAIN-B (“bit-identically”)** | r2 wording → [r3, F-C] strikes it as an overstatement of PE2's record → [r4, F4-3] corrects the PROVENANCE (origin is PE2's own report; r2 is the TRANSCRIBER), facts unchanged | **[r4, F4-3]** (`.10`) |
| **CHAIN-C (the r-to-q gain identity)** | r1 identity `gain(q) = gain(r) + e₁h₀` → [r2, G4] STRIKES it and re-derives per digit, with witness `a·b = 4x²+2` → [r3, F-B] replaces the witness with a realizable mid-branch one; **the strike itself stands** | **[r2, G4] strike + [r3, F-B] witness** (`.42`) |
| **CHAIN-D (the `c′` census warrant)** | [r4, F4-5] renames the cocycle to `c^{Φ′}` and opens the census → [r6, F6-2] extends it to the Q9 row, citing PE6's “42 occurrences” → [r7, F7-1] corrects the UNIT (hit-lines, not occurrences) and installs PE7's occurrence-level warrant | **[r7, F7-1]** (`.59`) |

### SERIES declared in this shard (template v3 rule 28)

**SERIES REPAIR-ARC** — the seven dated repair-round records (lines 43–339), one unit per dated entry, in source order: `.07` (r1) → `.09` (r2) → `.11` (r3) → `.12` (r4) → `.13` (r5) → `.14` (r6) → `.15` (r7). Continued in shard 2 by the STATUS BLOCK ARC line and the acceptance record.

**SERIES GRADE-BOX** — the six dated grade-box entries inside §S4.3 (lines 1071–1145), one unit per dated entry: `.65` ([r1], carrying the r0 box) → `.66` ([r2]) → `.67` ([r3]) → `.68` ([r4]) → `.69` ([r6]) → `.70` ([r7]). Note the deliberate GAP at r5: no r5 grade-box entry exists, and [r6, F6-1] says so in as many words (“the first bring-forward since r4”). A merge run must not silently interpolate one.

**SERIES MACHINE-LEG** — the dated machine-leg brackets in the header (lines 11–41): `.03` (the sealed leg, r0) → `.04` ([r1] the second, post-hoc leg added) → `.05` ([r2] the A7 amendment) → `.06` ([r3]+[r4] both legs byte-frozen; emitted as one unit because r4's bracket re-states r3's predicate verbatim over a fresh re-run, adding only the 4-wall-clock-line disclosure).

### Scope split — THREE predicates (template rule 7 + v3 rule 17), never conflated

**A. Mathematical absorption / supply SET.** What this shard's text claims to prove is fixed by the unit line and the S4 chain:

> “**Unit:** LIFT-CORNER (NR-1 of ILNRES S1; spec ILNRES S5.1, price M; route =
> the W-2 shift-descent covariance + window-calculus tail bookkeeping).”

The supply proper is **one sub-lemma (CONTENT), three lemmas/theorems ((TAIL-STAB), (READ-EQ), THE THEOREM), two corollaries (COR 1, COR 2), one propagation statement (PROP)**, over the corner \(g_0=1\wedge\delta_1=1\). The acceptance record's own inventory (out of range, line 1443) confirms the set and its fence:

> “**WHAT IS ACCEPTED**: this note's theorems as fenced — (TAIL-STAB) via
> lexicographic (m, deg a) descent; READ-EQ; THE THEOREM (the display with
> the letter the lift carries, every orbit member); COR 1 (the ξ = 1
> slice); COR 2 (the corner restriction, as rescoped at r1/F3) — at the
> note's own conditionality”

Note what the acceptance list does NOT contain: **PROP**. That is not an oversight of this compilation — it is the fact AC-1 later exploits, and it is recorded here as a positive scope finding, not as an inference.

**B. Append / consumption PROTOCOL scope — what this note has LANDED on other notes.** In range, the FENCES paragraph (lines 347–351) declares the negative:

> “**FENCES.** No edit to any accepted text (ITERLAW/ITERLAWN/ILNRES bodies,
> sealed falsifiers, wave-18 artifacts); committed engines consumed READ-ONLY
> (in-memory ledger override only, engine_ext precedent); no Lean change; no
> orders-≥3 machine claim (the battery is 2-read); no gr(w₂) claim; nothing
> here closes NR-1's ledger entry until this note's own acceptance arc runs.”

and §S5's opening (out of range, line 1170) repeats it: “ONCE THIS NOTE'S ARC CLOSES (and not before — no ledger or accepted text is edited now)”. **At the time of the HOME range, the protocol scope is therefore ZERO landed appends.** Post-acceptance the picture changed exactly twice, and both are verified positively here rather than assumed:

- **LANDED — ITERLAWN.** `grep -cF '## ★ FOLD ANNEX (orchestrator, 2026-08-07): THE NR-1 RIDER-REWRITE, LICENSED AND EXECUTED ★'` on `ITERLAWN_PROOF_2026-08-08.md` = 1 (XREF X14). Its License chain sentence names this note's acceptance commit `08f61e9` (verified: `git cat-file -t 08f61e9` = commit) and names the S5 display's lines as **“lines 1168–1176 at acceptance”** — which is precisely the shard-2 boundary this compilation drew independently.
- **LANDED — GRTW2 (reverse direction, supplier→consumer).** `GRTW2_PROOF_2026-08-08.md` line 1351 names this note: “the accepted LIFTCORNER's shift-descent consumption” (XREF X13, count 1).
- **NOT LANDED — ILNRES.** `grep -c 'LIFTCORNER\|LIFT-CORNER'` on `ILNRES_2026-08-08.md` = **1**, and that single hit is the pre-existing S5.1 spec heading “**S5.1 (NR-1 LIFT-CORNER unit), price M.**” (line 180), i.e. the *charge*, not an absorption append. ILNRES's NR-1 ledger entry has NOT been folded (negative edge N2).
- **NOT LANDED — the entire (Φ₁-OPACITY) program.** `grep -c 'OPACITY\|AC-4\|AC-5'` on `ITERLAWN_PROOF_2026-08-08.md` = **0** (negative edge N3). AC-5's own closing parenthetical says so — “transcription-confirm owed” — and this compilation verifies it rather than repeating it. Consequence for PROP's consumers: ITERLAWN's fold annex records neither AC-1's suspension nor AC-5's reinstatement, so a reader of ITERLAWN alone cannot learn that the rider it executed was suspended for the interval AC-1 → AC-5. See OPEN-CALL 3.

**C. Inbound corrections RECEIVED from supplier or certifier arcs (v3 rule 17).** This shard's range received **five**: AC-1 (PROP suspension), AC-2 (CONTENT), AC-3 (READ-EQ degree), AC-4 (the census-of-record re-pointing inside [r4, F4-4], plus PROP narrowing), AC-5 (PROP reinstatement). All five originate in the sol certification arc (`runs/cert/C1_liftcorner_output.log`, `runs/cert2/E1_liftcorner_output.log`, `runs/cert4/P3_opacity_output.log`, `runs/cert5/P4_rm1_output.log` — all four verified to exist), NOT in a supplier note. That is a distinct DAG edge class from both A and B, and it is the class that changed two proved statements of this shard.

### Resolution rules applied

1. Lines 1–1167 supply the HOME material. Every `[rN, …]` bracket in range is already-landed text; wording quoted inside such a bracket is dead and is emitted only when the supersession is load-bearing (rule 7 below).
2. Where a later in-range round touches text an earlier round already touched, the LATER round governs; the four multi-layer collisions are tabulated as CHAIN-A…CHAIN-D above with their TERMINALs named.
3. Where an out-of-range dated append names an in-range sentence, the corrected reading is carried in the unit's CANONICAL STATEMENT when the append is a “is SUPERSEDED by” replacement (AC-2, AC-3), and in CONDITIONALITY when it is a scope pin or a counter re-reading (AC-1/AC-4/AC-5, FC-1, the acceptance record).
4. **The sealed pre-run text of §S1 and §S2 is never rewritten**, per (iii) above. Where the sealed text is wrong (the `c′` collision), the unit carries the sealed bytes as its CANONICAL STATEMENT and the correcting bracket as CONDITIONALITY — never the reverse, because a downstream re-runner must be able to reproduce the sealed sheet byte-for-byte.
5. **Preregistrations and run-records are separate units even when the source displays them adjacently** (v3 rule 19). S2's thirteen-family sheet is a `preregistration`; S3's verdict is a `run-record`; the runner and the children generator are `instrument-record`s.
6. The r0 text survives ONLY where no round touched it. Four r0 claims are dead: “every child has m′ ≤ m−1” (killed at r1/F1), “gain(q-digit) = gain(r-digit) + e₁h₀” (killed at r2/G4), “valid EXACTLY on the flat corner d₀ = 1” (killed at r2/G5), and COR 2's W2-OPEN-1 identification (withdrawn at r1/F3).
7. A dead wording is emitted as its own unit only when a consumer could otherwise re-import it. Four qualify: the r0 strict-descent clause (`.36`, because the whole lex repair is unintelligible without it), the r0 W2-OPEN-1 identification (`.49`, because two things are still owed for the tie), the r1 promotion of assert (i) (`.19`, because the arc's own standing rule is derived from it), and the PE6 “42 occurrences” figure (`.47`, because the standing transcription rule is derived from it).
8. **Numbers are re-computed, never transcribed.** Every count in §S3, §S4.1's machine-leg brackets and the census arithmetic was re-derived at compile time from the committed artifacts (§3.4 and §6's arithmetic audit), independently of the note's own tables. Two figures the note does not display are supplied by the audit; zero discrepancies were found.
9. External reports (`LIFTCORNER_passPE1..PE9_report.md`) are reading notes for provenance verification only; no report text is imported as a statement.

### Quotation and table discipline

CANONICAL STATEMENTs are verbatim source quotation or explicitly marked `[ASSEMBLED]`; truncation inside a quotation is marked `…`. The note's ASCII displays (the b₀-split, the ω-gain inequalities, the counter-instance chain) are reproduced with their line structure intact inside fenced blocks, then, where they are tables, transcribed a second time as `[TABLE]` per v3 rule 14. The two source tables in range (S2's prediction sheet, S4.1's seven-genre census) are emitted as tables and flagged `[TABLE]`; neither is prosified. Compiler-authored ledgers in §§3–6 are flagged `[TABLE — compiler ledger]` and are not source statement units.

---

## 2. Statement inventory

72 units, contiguous, in effective-text (= source) order. Every unit carries FORM (v3 rule 11) because the shard is tag-sparse.

### EFF.LIFTCORNER.s1of2.01  [convention]

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

### EFF.LIFTCORNER.s1of2.02  [scope record]

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

### EFF.LIFTCORNER.s1of2.03  [instrument-record]  *(SERIES MACHINE-LEG, link 1)*

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

### EFF.LIFTCORNER.s1of2.04  [instrument-record]  *(SERIES MACHINE-LEG, link 2 — dated r1)*

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

### EFF.LIFTCORNER.s1of2.05  [instrument-record]  *(SERIES MACHINE-LEG, link 3 — dated r2)*

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

### EFF.LIFTCORNER.s1of2.06  [instrument-record]  *(SERIES MACHINE-LEG, link 4 — dated r3 + r4)*

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

### EFF.LIFTCORNER.s1of2.07  [repair-round record]  *(SERIES REPAIR-ARC, link 1 — r1)*

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

### EFF.LIFTCORNER.s1of2.08  [supersession rider]  *(CHAIN-A, links 3–4 as sited inside the r1 round record)*

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

### EFF.LIFTCORNER.s1of2.09  [repair-round record]  *(SERIES REPAIR-ARC, link 2 — r2)*

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

### EFF.LIFTCORNER.s1of2.10  [supplier-finding / provenance-rider]  *(CHAIN-B — TERMINAL)*

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

### EFF.LIFTCORNER.s1of2.11  [repair-round record]  *(SERIES REPAIR-ARC, link 3 — r3)*

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

### EFF.LIFTCORNER.s1of2.12  [repair-round record]  *(SERIES REPAIR-ARC, link 4 — r4)*

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

### EFF.LIFTCORNER.s1of2.13  [repair-round record]  *(SERIES REPAIR-ARC, link 5 — r5)*

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

### EFF.LIFTCORNER.s1of2.14  [repair-round record]  *(SERIES REPAIR-ARC, link 6 — r6)*

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

### EFF.LIFTCORNER.s1of2.15  [repair-round record]  *(SERIES REPAIR-ARC, link 7 — r7, TERMINAL of the series in this shard)*

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

### EFF.LIFTCORNER.s1of2.16  [fence]

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

### EFF.LIFTCORNER.s1of2.17  [fence]

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

### EFF.LIFTCORNER.s1of2.18  [definition]

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

### EFF.LIFTCORNER.s1of2.19  [definition]

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

### EFF.LIFTCORNER.s1of2.20  [preregistration]

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

### EFF.LIFTCORNER.s1of2.21  [preregistration]

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

### EFF.LIFTCORNER.s1of2.22  [preregistration] `[TABLE]`

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

### EFF.LIFTCORNER.s1of2.23  [instrument-record]

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

### EFF.LIFTCORNER.s1of2.24  [instrument-record]  *(CHAIN-A, link 3)*

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

### EFF.LIFTCORNER.s1of2.25  [instrument-record]  *(CHAIN-A — TERMINAL)*

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

### EFF.LIFTCORNER.s1of2.26  [derivation]

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

### EFF.LIFTCORNER.s1of2.27  [supersession rider]

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

### EFF.LIFTCORNER.s1of2.28  [run-record]

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

### EFF.LIFTCORNER.s1of2.29  [run-record] `[TABLE]`

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

### EFF.LIFTCORNER.s1of2.30  [run-record / disclosure]

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

### EFF.LIFTCORNER.s1of2.31  [scope record]

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
### EFF.LIFTCORNER.s1of2.32  [convention]

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

### EFF.LIFTCORNER.s1of2.33  [definition]

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

### EFF.LIFTCORNER.s1of2.34  [lemma]

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

**TARGETS:** `s1of2.34` (this unit) only. No other in-range span is touched.

**RESOLUTION TRACE:** statement lines 608–611; correction site 1535–1552 (shard 2, finding 3 REAL + AC-2).

**TEETH:** charge item (3) — “the CONTENT sub-lemma's base-fact status” — is precisely the item the certifier's finding hit. The teeth were correctly aimed and the in-house passes did not fire: disposition `AUDIT / decorrelated-model audit`.

---

### EFF.LIFTCORNER.s1of2.35  [lemma]

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

### EFF.LIFTCORNER.s1of2.36  [lemma]

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

### EFF.LIFTCORNER.s1of2.37  [derivation]

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

### EFF.LIFTCORNER.s1of2.38  [derivation]

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

### EFF.LIFTCORNER.s1of2.39  [table]  `[TABLE]`

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

### EFF.LIFTCORNER.s1of2.40  [derivation]

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

### EFF.LIFTCORNER.s1of2.41  [derivation]

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

### EFF.LIFTCORNER.s1of2.42  [derivation]  *(CHAIN-C — TERMINAL)*

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

### EFF.LIFTCORNER.s1of2.43  [run-record]

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

### EFF.LIFTCORNER.s1of2.44  [instrument-record + run-record]

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

### EFF.LIFTCORNER.s1of2.45  [fence]

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

### EFF.LIFTCORNER.s1of2.46  [derivation]

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

### EFF.LIFTCORNER.s1of2.47  [derivation]

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

### EFF.LIFTCORNER.s1of2.48  [derivation]

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

### EFF.LIFTCORNER.s1of2.49  [scope record]

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

### EFF.LIFTCORNER.s1of2.50  [changes-record]

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

### EFF.LIFTCORNER.s1of2.51  [changes-record]

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

### EFF.LIFTCORNER.s1of2.52  [derivation]

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

### EFF.LIFTCORNER.s1of2.53  [derivation]

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
### EFF.LIFTCORNER.s1of2.54  [lemma]

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

### EFF.LIFTCORNER.s1of2.55  [derivation]

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

**CONDITIONALITY:** SUPERSESSION KIND: **replacement**. AC-3's consumer sweep: “This is exactly the inequality consumed by the anchor and \(\delta_1=0\) parts of READ-EQ. It holds also at \(d_0=1\), where \(\deg\Phi'=e_0\) but \(s<e_0\). The separate \(\delta_1=1\) one-overflow argument is untouched. Therefore READ-EQ, the THEOREM, COR 1 and COR 2 survive unchanged.” **TARGETS:** `s1of2.55` only.

**RESOLUTION TRACE:** statement line 945; correction site 1554–1573 (shard 2, finding 4 REAL + AC-3).

**TEETH:** `AUDIT / decorrelated-model audit`. Note the pattern: BOTH certifier-found REAL defects in this shard (`.34`, `.55`) are *scope-of-display* errors in one-line statements that four in-house hostile passes read without firing — the note's teeth are aimed at the arguments, and its displays were the soft target.

---

### EFF.LIFTCORNER.s1of2.56  [derivation]

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

### EFF.LIFTCORNER.s1of2.57  [theorem]

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

### EFF.LIFTCORNER.s1of2.58  [changes-record]  *(CHAIN-D, link 1)*

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

**CONDITIONALITY:** SUPERSESSION KIND: **wording-rider**, with a **license** attached for the three sealed sites it cannot edit (S1's CANDIDATE display, S2's Q7 row, S2's Q9 row). **TARGETS:** `s1of2.20` (the CANDIDATE display, ×2 occurrences), `s1of2.22` (Q7 row, Q9 row), `s1of2.61` (COR 2).

**RESOLUTION TRACE:** statement lines 970–982; the Q7 extension at 269–271 (F5-3); the Q9 extension at 293–297 (F6-2).

**TEETH:** the census warrant is `.59`.

---

### EFF.LIFTCORNER.s1of2.59  [changes-record]  *(CHAIN-D — TERMINAL)*

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

### EFF.LIFTCORNER.s1of2.60  [corollary]

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

### EFF.LIFTCORNER.s1of2.61  [corollary]

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

### EFF.LIFTCORNER.s1of2.62  [changes-record]

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

### EFF.LIFTCORNER.s1of2.63  [proposition]  *(CHAIN-P, link 1 — SUPERSEDED; TERMINAL is AC-5)*

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

### EFF.LIFTCORNER.s1of2.64  [changes-record]

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

### EFF.LIFTCORNER.s1of2.65  [acceptance-box]  *(SERIES GRADE-BOX, link 1 — r1, carrying the r0 box)*

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

### EFF.LIFTCORNER.s1of2.66  [acceptance-box]  *(SERIES GRADE-BOX, link 2 — r2)*

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

### EFF.LIFTCORNER.s1of2.67  [acceptance-box]  *(SERIES GRADE-BOX, link 3 — r3)*

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

### EFF.LIFTCORNER.s1of2.68  [acceptance-box]  *(SERIES GRADE-BOX, link 4 — r4)*

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

### EFF.LIFTCORNER.s1of2.69  [acceptance-box]  *(SERIES GRADE-BOX, link 5 — r6; note the r5 GAP)*

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

### EFF.LIFTCORNER.s1of2.70  [acceptance-box]  *(SERIES GRADE-BOX, link 6 — r7, TERMINAL in range)*

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

### EFF.LIFTCORNER.s1of2.71  [fence]

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

### EFF.LIFTCORNER.s1of2.72  [scope record]

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
## 3. XREF verification ledger

Every positive XREF was checked with fixed-string `grep -cF` at compile time (2026-08-14) against the working tree, with the count and first line recorded. Negative edges N1–N4 are verified absences. Commit pins were checked with `git cat-file -t` (v3 rule 23); artifact pins by existence + md5.

### 3.1 Source-of-record designations (`.16`)

`[TABLE — compiler ledger]`

| ID | Target file | Verified designation | count | line | Role |
|---|---|---|---:|---:|---|
| X01 | `ILNRES_2026-08-08.md` | `**S5.1 (NR-1 LIFT-CORNER unit), price M.**` | 1 | 180 | the spec of record; the deliverable sentence quoted at §S5 |
| X02 | same | `**[NR-1] (ITER-LAW-LIFT), open exactly at g₀ = 1 ∧ δ₁ = 1.**` | 1 | 25 | the residual this unit attacks |
| X03 | `ITERLAWLIFT_CORNER_2026-08-08.md` | `**Step 2 (THE ONE OPEN STEP — displayed lemma (TAIL-STAB)).**` | 1 | 191 | wave-18's open step = this note's `.35` |
| X18 | same | `**Honesty box.** (TAIL-STAB) is UNPROVED` | 1 | 207 | the supplier's own pre-state, which `.35` closes |
| X04 | same | `104,404` | 3 | 122 | the LAWFUL slice measurement cited at `.19`/`.60` |
| X05 | `ITERLAWN_PROOF_2026-08-08.md` | `### S0.1 The (n+1)-read standard-lift harness class (the class pin)` | 1 | 144 | the class pin PROP rides |
| X06 | same | `* Lifts: Φ₁ := the STANDARD LIFT of ψ₀ (grb_order2_check :499–507); for` | 1 | 163 | the Lifts clause named as “the one pin a rung-≥2 census must clear” (`.64`) |
| X09 | `GRTW2_PROOF_2026-08-08.md` | `### 3.4 THE (ξ, w) CLOSED FORM (the display of record)` | 1 | 394 | the χ-chain/shift-descent source (`.19`, `.49`) |
| X10 | same | `### 5.3 The value layer: W2-OPEN-1 (displayed open lemma, machine-confirmed)` | 1 | 881 | the clause-3 ψ-transport + W2-OPEN-1 source (`.62`) |

### 3.2 Designations verified for the [r4, F4-4] / AC-4 census dispute (`.64`)

`[TABLE — compiler ledger]`

| ID | Target | Verified designation | count | line | Role |
|---|---|---|---:|---:|---|
| X07 | `ITERLAWN_PROOF_2026-08-08.md` | `## S7. THE CONDITIONALITY LEDGER (the exact grade of every clause, per rung)` | 1 | 1148 | the sweep's true home — **confirms [r5, F5-4]'s S9 → S7 correction**; the table carries exactly 22 data rows |
| X08 | same | `[attribution (errata r4, 2026-08-03; PE4-F1): + S4.1 at rungs ≥ 2` | 1 | 278 | the r4 erratum's L6 row, quoted verbatim by `.64`; the full quoted string matches at count 1 under whitespace normalization |
| X15 | same | `194 raw hits on 147 lines, 194/194 mapped, ZERO` | 1 | 1233 | ITERLAWN's own machine census of record — the object AC-4 uses in place of the 22-row hand table |
| X17 | same | `### S4.6 The engine (RM-m), and Cases II-1/II-2/II-3` | 1 | 777 | the site AC-4 isolates as the sole surviving obstruction, and AC-5 discharges |
| X16 | `ILNRES_2026-08-08.md` | `S1's FOUR-MEMBER residual list is COMPLETE relative to the sources` | 1 | 288 | the S7 completeness sentence the §S5 disposition paragraph (shard 2) will not collide with |

### 3.3 Reverse XREFs — consumers of this note

`[TABLE — compiler ledger]`

| ID | Consumer and verified designation | count | line | Supplied edge |
|---|---|---:|---:|---|
| X13 | `GRTW2_PROOF_2026-08-08.md` — `the accepted LIFTCORNER's shift-descent` | 1 | 1351 | the supplier's acceptance record names this consumer by name — the shard's one fully closed loop (`.72`) |
| X11 | same — `W2-OPEN-1` | 10 | 127 | the designation `.62` says two things are owed against; the ledger row at line 982 records it `**OPEN**, instance-confirmed 684 groups / 0` |
| X14 | `ITERLAWN_PROOF_2026-08-08.md` — `## ★ FOLD ANNEX (orchestrator, 2026-08-07): THE NR-1 RIDER-REWRITE, LICENSED AND EXECUTED ★` | 1 | 1518 | FC-2's execution, LANDED. Names LIFTCORNER's acceptance commit `08f61e9` and this compilation's shard boundary (“lines 1168–1176 at acceptance”) |
| RX19 | `spec/HYPOTHESIS_LEDGER.md` — `HYP.76  \`W2-VALUE\`` | 1 | 596 | the W-2 value-layer row whose CONSUMED-BY block adjudicates the LIFTCORNER/W-2 seam as NOT-REACHED for the spine |
| RX20 | same — `HYP.110  \`W12-BOX-5\`` | 1 | 893 | “Lean omCount is order-0 and W-2/LIFTCORNER lift-convention seam is unconsumed” |
| RX21 | `docs/in-progress/LEAN_SCOPING_consumption_map_2026-08-12.md` — `LIFTCORNER` | 5 | — | the Lean-scoping consumption read of this note |
| RX22 | `docs/PROJECT_STATE.md` — `row 19 also ((Φ₁-OPACITY), numerical certificate` | 1 | 3996 | the certification ledger's row-19 tracking of the AC-1 → AC-5 program |

### 3.4 Artifact and commit pins (v3 rule 23)

`[TABLE — compiler ledger]`

| ID | Pin | Kind | Verified |
|---|---|---|---|
| P01 | `verification/openmath/liftcorner_checks.py` | artifact | EXISTS; md5 `ccb4351c92573f5f962cae4ae952d8dd` — **identical to the note's figure at four separate quotation sites** |
| P02 | `verification/openmath/liftcorner_checks_output.txt` | artifact | EXISTS; `TOTAL checks 25409  elapsed 4.4s`, `VERDICT: ALL GREEN` |
| P03 | `verification/openmath/liftcorner_checks_results.json` | artifact | EXISTS |
| P04 | `verification/openmath/liftcorner_tailstab_children.py` | artifact | EXISTS; md5 `11f2d7858a66d4b8231b38b11f8751c3` (compiler-supplied; the note pins this leg by reproducibility, not hash) |
| P05 | `verification/openmath/liftcorner_tailstab_children_table.txt` | artifact | EXISTS; md5 `bf9106e7edc535edf2b7a6b6a64f0f55`, 2,986 lines |
| P06–P14 | `LIFTCORNER_passPE1..PE9_report.md` | artifacts | ALL NINE EXIST in `lean/notes/openmath/` |
| P15 | `30e570c` (PE1), `3367f3c` (PE2), `39ea0db` (PE3), `8b53efa` (PE4), `a5212e8` (PE5), `f2b48e7` (PE6), `58f7060` (PE7), `c6097d7` (PE8), `9b5175c` (PE9) | commits | ALL NINE resolve: `git cat-file -t` = commit |
| P16 | `dafc0b5` (the seal), `46e6e88` (PE6 HEAD), `91f0cde` (PE7 HEAD), `adc6cf3` (GRTW2 acceptance), `5054d69` (FC-2 execution), `08f61e9` (this note's acceptance) | commits | ALL SIX resolve |
| P17 | `runs/cert/C1_liftcorner_output.log`, `runs/cert2/E1_liftcorner_output.log`, `runs/cert4/P3_opacity_output.log`, `runs/cert5/P4_rm1_output.log` | artifacts | ALL FOUR EXIST (the certifier arc behind AC-1…AC-5) |

### 3.5 Source-code pins — PARTIAL disposition

The mutation trace (`.24`) and the `mk_field_ext` reading (`.25`, `.26`) cite file:line coordinates in four scripts: `liftcorner_checks.py:14/:36/:52/:179`, `grb_order2_check.py:333–334/:345/:499–507/:515/:651`, `iterlawlift_corner.py:145–155`, `strata_probe.py:389`. **Disposition: the `liftcorner_checks.py` pins are STABLE** (that file is byte-frozen by the two-commit seal, md5 re-verified). **The other three files carry no freeze predicate in this note**, so their line numbers are pins to a moving target. No drift was detected in the claims that matter (the note's *arguments* about `mk_field_ext` are structural, not line-dependent), but a mechanical re-checker should treat those coordinates as UNPINNED. See OPEN-CALL 4.

### 3.6 Verified NEGATIVE edges

`[TABLE — compiler ledger]`

| ID | Check | count | Meaning |
|---|---|---:|---|
| N1 | `grep -cF 'OPACITY' ITERLAWN_PROOF_2026-08-08.md` | 0 | the (Φ₁-OPACITY) program is UNLANDED on ITERLAWN |
| N2 | `grep -cF 'AC-5' ITERLAWN_PROOF_2026-08-08.md` | 0 | AC-5's discharge is UNLANDED on ITERLAWN — matching AC-5's own “transcription-confirm owed” |
| N3 | `grep -cF 'LIFTCORNER' ILNRES_2026-08-08.md` | 0 | ILNRES carries no absorption append; its single `LIFT-CORNER` hit (count 1, line 180) is the pre-existing S5.1 spec heading, i.e. the CHARGE, not a fold |
| N4 | `grep -cF 'NR-1 discharged' ILNRES_2026-08-08.md` | 0 | NR-1's ILNRES ledger entry is unfolded; the §S5 rider rewrite landed on ITERLAWN only (X14) |

---

## 4. Effective supply / consumption ledger

`[TABLE — compiler ledger]`

| Source conclusion or obligation | Effective supply in this shard | Surviving fence | Protocol status |
|---|---|---|---|
| wave-18's open step (TAIL-STAB) (X03, X18) | `.35`+`.36`, proved by the lex descent `.37`–`.48` | census completeness carried by algebra, machine leg instance-level (`.45`) | **CLOSED**; wave-18's honesty box is answered. No dated append landed on wave 18 (not required — wave 18 is a probe note, and FENCES bars edits to its artifacts) |
| ILNRES S5.1's deliverable (X01) | `.57` + `.60` + `.61` + `.63` | Φ₁ axis only; deeper levels fenced (shard 2) | **DELIVERED**; ILNRES ledger fold **NOT LANDED** (N3, N4) |
| [ILN] S0.1's rider on the Φ₁ axis (X05, X06) | `.63` (PROP), as discharged by AC-4+AC-5 | ITERLAWN's own DCX/(RM-m)/T-scope conditionality unchanged | **LANDED** as FC-2 on ITERLAWN (X14) — but landed BEFORE AC-1's suspension and never updated (OPEN-CALL 3) |
| GRTW2 clause 3 ψ-transport (X09, X10) | `.19` (the corner degeneration) and `.61` (COR 2) | COR 2 is about the HARNESS orbit only; (a)/(b) of `.62` owed for any W2-OPEN-1 tie | **CONSUMED**; acknowledged by name in GRTW2's acceptance record (X13) |
| the accepted [IL] ITER-LAW (standard lift) | consumed at `.57`'s reduction to Φ″ | 2-read only; no orders-≥3 claim (`.17`) | **CONSUMED, unmodified** |
| ITERLAWN S4.6's (RM-1) engine (X17) | NOT consumed in range; consumed by AC-5 (shard 2) | AC-5 proves only the four interface clauses, explicitly not full R,Q equality | **CONSUMED by the certifier arc; UNLANDED on ITERLAWN** (N1, N2) |

---

## 5. NON-IMPORTS

The note's explicit negative fences, load-bearing for the DAG.

**NI-1 — no accepted text is edited, and no engine is written to.** `.17`: “No edit to any accepted text (ITERLAW/ITERLAWN/ILNRES bodies, sealed falsifiers, wave-18 artifacts); committed engines consumed READ-ONLY (in-memory ledger override only, engine_ext precedent)”.

**NI-2 — no Lean edge.** `.17`: “no Lean change”. This shard creates NO edge to the Lean corpus.

**NI-3 — no orders-≥3 machine claim.** `.17`: “no orders-≥3 machine claim (the battery is 2-read)”. Every measured and every proved statement in the shard is 2-read.

**NI-4 — no gr(w₂) claim.** `.17`: “no gr(w₂) claim”. The NR-2 gr-semantics wrapper is a different residual (ILNRES [NR-2]) and is not touched.

**NI-5 — the runner's two asserts are consumed by NOTHING.** `.25`: “**NO CHAIN STEP CONSUMES EITHER**”. So no edge runs from the asserts to any proof step; the soundness edge runs from `mk_field_ext`'s g = 1 reading instead (`.26`).

**NI-6 — the r-to-q gain equality is consumed by nothing.** `.42`: the 896/896 equality is “an artifact of those instances' shapes, and no step below consumes it.”

**NI-7 — the branching count's VALUE is consumed by nothing.** `.48`: “**ONLY FINITENESS of this count is consumed** … no step anywhere uses the count's VALUE.”

**NI-8 — COR 2 imports no slice of W2-OPEN-1.** `.62`: “no equivalence between COR 2 and any slice of W2-OPEN-1 is derived anywhere in this note”, with (a) and (b) named as what a tie would need.

**NI-9 — Q6 LOC is not an independent leg.** `.30`: “A reader tallying S2's thirteen prediction families as thirteen independent legs over-counts by one.”

**NI-10 — the CERT family's PARI leg is not re-run.** `.22`: “PARI leg NOT re-run: wave-18 T11 on the same base roster is on file — disclosed reuse”.

Accordingly **no edge is created** from this shard to the Lean corpus, to any orders-≥3 statement, to gr(w₂), to W2-OPEN-1's battery, or from the runner's asserts to any proof step.

---

## 6. TEETH inverse inventory

Disposition vocabulary: `{proved-in-note, executable regression, AUDIT (decorrelated-model | in-house hostile pass), signed vacuity disclosure, disclosed non-repair, accepted-with-decorrelation-supplied, stale self-description, PROOF-ONLY}`.

### 6.1 Battery row → guarded units (forward)

`[TABLE — compiler ledger]`

| # | Battery row (source wording, abbreviated) | Guarded EFF units | Disposition |
|---:|---|---|---|
| 1 | Q1 GATE — every tower passes the lawfulness gate for its OWN ψ₀′ | `.18`, `.19`, `.21` | executable regression (56/56) |
| 2 | Q2 AV — ANCHOR-VAL with the transported ε₁′ | `.19`, `.54` | executable regression (656/0) |
| 3 | Q3 TLAW — THE CANDIDATE: measured cocycle = transported display | `.20`, `.57`, `.35` | executable regression (4,176/0) |
| 4 | Q4 PV — L7 PAIR-VAL both forms + single-slot shape | `.54`, `.56`, `.36` | executable regression (4,176/0) |
| 5 | Q5 INT — exponent integrality | `.20` (D₁ integrality) | executable regression (4,176/0) |
| 6 | Q6 LOC — δ₁ = 0 sub-violations (bug detector) | `.30` | **disclosed non-repair** (0 checks counted; nested, not independent) |
| 7 | Q7 CHI — cross-tower χ-ratio, measured vs MEASURED | `.61`, `.19` | executable regression (4,176/0) — the sharpest instrument shape in the sheet |
| 8 | Q8 COV — per twisted block: ≥1 δ₁ = 1 pair AND ≥1 pair with ξ^{D₁} ≠ 1 | `.21`, `.29` | executable regression (met: min 6 / min 6) |
| 9 | Q9 WRONGLET — per-pair set equivalence; total fires > 0 | `.61` (sharpness) | executable regression (3,816 exact, 1,576 fires) |
| 10 | Q10 XI1 — the ξ = 1 dense slice reproduces the unchanged display | `.60` | executable regression, **UNPINNED figure** (no independent counter in the artifact) |
| 11 | TRS — closed-form transcription vs `C.iter_law` | `.20`, `.57` | executable regression (4,176/0) |
| 12 | CERT — base towers G.T1_T2(nf=4) + G.T5 internal | `.22` | **disclosed reuse** (PARI leg not re-run) |
| 13 | ENG-GATE — `engine_ext.agreement_gate(full=False)` re-run in-unit | `.22` | executable regression (1 check, 0 new) |
| 14 | A1–A6 (children generator, r1) | `.39`, `.40`, `.41`, `.43`, `.46` | executable regression (752 probes / 4,438 digits / min slack 0) |
| 15 | A7(i)–(iv) (children generator, r2) | `.38`, `.44`, `.47`, `.48` | **accepted-with-decorrelation-supplied** (X built by direct multiplication, not from the shared pass identity) |
| 16 | Charge item (1) — census COMPLETENESS + row-7b drop | `.38`, `.41`, `.45` | **PROOF-ONLY** — the note's own coverage-hole sentence: “A7 is instance-level … the ∀ is carried by (A)'s algebra” |
| 17 | Charge item (2) — lex-order finiteness | `.47`, `.48` | proved-in-note; three hostile re-derivations |
| 18 | Charge item (3) — CONTENT's base-fact status | `.34` | **AUDIT / decorrelated-model** — statement too broad; repaired by AC-2 |
| 19 | Charge item (4) — READ-EQ close | `.55`, `.56` | **AUDIT / decorrelated-model** on the degree clause (AC-3); rest proved-in-note |
| 20 | Charge item (5) — PROP's census cite | `.63`, `.64` | **AUDIT / decorrelated-model** — AC-1 → AC-4 → AC-5 |
| 21 | Charge item (6) — COR 2 rescoped; (a)/(b) owed | `.61`, `.62` | **OPEN** — no instrument closes it; the note says so |
| 22 | Charge item (7) — eight per-digit ω-gain bounds | `.42`, `.39` | **accepted-with-decorrelation-supplied** (PE2 re-derived all eight; PE3, PE4 again) |

### 6.2 Reverse direction — units with no tooth

`.01`, `.02`, `.16`, `.17`, `.31`, `.49`, `.65`–`.70`, `.71`, `.72` are identification/scope/record units carrying no battery obligation of their own; they are guarded by the acceptance record and by §3's pin verification instead. `.03`–`.15` are instrument-records and round-records: their tooth is the pin ledger (§3.4), and every pin in it verified. `.59` carries a **stale self-description** disposition (its warrant is commit-pinned to 91f0cde and the note is at `33225dd9`). Every other unit — 47 of 72 — appears in at least one row of §6.1.

**Zero-orphan check:** 13 sealed-sheet families + 2 machine-generator assertion suites + 7 charge items = **22 obligations**, all mapped, **0 orphan rows**. The charge list (`.71`) is fully consumed and its per-item status is tabulated there.

### 6.3 Arithmetic audit summary (v3 rule 22)

Every count table in the shard was recomputed from primary artifacts:

- **25,409** = 56 + 656 + 5×4,176 + 3,816 + 0 + 0 + 1 ✓ (the ENG-GATE 1 is load-bearing and undisplayed in §S3 — OPEN-CALL 2)
- **56** towers = 48 twisted + 8 dense controls = 16 twistable × ≤2 draws × 2 variants + 8 ✓ (two independent routes)
- **2e₀+3** = 1 + 4 + (e₀−1) + (e₀−1) ✓; observed maxima 7, 9, 11, 13, 15 at e₀ = 2…6 ✓
- **220** m′ = m children, all genre 7b, all degA-DROP, min gain 2 ✓ (committed table)
- **752** nodes / **5,336** children / **4,438** digits / min slack **0** ✓ (committed table)
- **194** = 88+21+53+8+18+6 ✓ (AC-4's partition against ITERLAWN's own census, X15)
- **51** = 34+4+13 ✓ (PE7's `c′` partition); at HEAD the raw counts are 54/50, three above PE7's 51/47 — explained by the four post-91f0cde certifier appends
- Φ′ = Φ₀² + 2xΦ₀ + 2 = x⁴+4x³+5x²+4x+3 ✓; the double-development identity xΦ₀² = (x−2)Φ′ + (6x+2)Φ₀ + (−2x+4) ✓ (expanded in full at `.53`)
- the F-B witness: 4x²+2x = 4Φ₀ + (−2x−4), w₀ = 1/2/1 ✓; (αδ)² = −8, v₂ = 3 odd ✓

**Zero arithmetic discrepancies found.** One completeness gap (the undisplayed ENG-GATE count) and one staleness (the `c′` census at HEAD) are recorded as OPEN-CALLs, not as errors.

---

## 7. BOUNDARY SELF-AUDIT (tag-sparse prose genre; template rules 9 and 11)

### 7.1 The rule applied

Zero `\tag{` in the HOME range, so every unit boundary is a compiler choice. The rule used: **a unit is the smallest span that a downstream chapter could cut and still state correctly.** Consequences applied uniformly: (a) a dated bracket that SUPERSEDES named text is its own unit, never folded into its host paragraph, because the host and the bracket have different truth conditions; (b) a proof is split from its statement whenever a later instrument replaces one without the other (`.34`/`.55` are exactly these cases); (c) a table is a unit (rule 4).

### 7.2 Boundaries drawn, with the genuinely arguable ones recorded both ways

1. **The four machine-leg brackets → three units (`.03`–`.06`), merging [r3] and [r4].** *Alternative considered:* four units. *Chosen because* r4's bracket re-states r3's predicate verbatim and adds only the wall-clock disclosure; splitting would create a unit whose whole content is “still true”. *Risk accepted:* a merge run wanting per-round instrument granularity must re-split at line 32.
2. **The seven round records → seven units, with their in-round dispositions homed at their SUBJECT sites, not at the round.** *Alternative:* one unit per (round × disposition), ≈ 30 units. *Chosen because* every disposition already has a home site in §S2/§S3/§S4 where its content lives; homing it at the round would duplicate the content and split the supersession chains across two places. *Cost:* the round records are summaries with pointers, so a chapter cutting only a round record gets no mathematics. Recorded explicitly in each round unit.
3. **[r3, F-C] + [r4, F4-3] → ONE unit (`.10`).** *Alternative:* two units (strike; provenance correction). *Chosen because* F4-3 quotes F-C in full and supersedes only its attribution; the pair is unintelligible split. *This is the arguable one*: the two riders have different KINDS (replacement vs provenance-rider), and v3 rule 18 wants the kind declared per unit. Resolved by declaring the kind of the TERMINAL (provenance-rider) and recording the predecessor's kind inline.
4. **The assert saga → four units (`.23`, `.24`, `.25`, `.26`), not one.** *Chosen because* they have four different types: a disclosure list (instrument-record), a mutation trace (derivation over source), a final description (instrument-record), and the actual soundness argument (derivation). Folding them would bury `.26` — the only one that does mathematical work — inside three units of arc history.
5. **§S4.1's proof → twelve units (`.37`–`.48`).** *Alternative:* one “proof of TAIL-STAB” unit. *Chosen because* the proof contains three dated strikes, a table, two machine legs and two independently-consumed clauses; a single unit could not carry per-piece supersession or per-piece teeth.
6. **The counter-instance → two units (`.52` recursion chain, `.53` independent tie).** *Chosen because* `.53` is a DECORRELATED check (it does not use the recursion at all) and is the single strongest verification in the shard; folding it into `.52` would hide that independence.
7. **The grade box → six units + charge list + W-2 census (`.65`–`.72`).** *Chosen because* v3 rule 28 makes the dated arc a SERIES with mandatory per-entry emission. The r5 GAP is only visible under per-entry emission.
8. **`.35`/`.36` split (LEMMA statement vs its read-kill consequence).** *Arguable:* the source runs them together across a paragraph break. *Chosen* because READ-EQ consumes `.36` and never `.35` directly, so a chapter cut needs them separable.

### 7.3 Merges deliberately NOT made

- `.39` (the census table) was NOT merged into `.38` (the pass step) despite being its immediate consequence: rule 4 makes tables units.
- `.62` (the F3 withdrawal) was NOT merged into `.61` (COR 2): the withdrawal carries two live obligations (a)/(b) that a COR 2 cut must not swallow.
- `.63` (PROP) and `.64` (its cite correction) were kept separate: AC-1 quotes `.64`, while AC-5 discharges `.63`. Merged, the CHAIN-P table could not point at the right span.

### 7.4 Which template rules fought this genre

- **Rule 12 (three-slot RESOLUTION TRACE) is essential here** and was used at `.35`, `.42`, `.63`, `.64`: statement, proof and correction sites are hundreds of lines apart, and in `.63`'s case in a different section entirely.
- **Rule 19's three-way split (preregistration / run-record / instrument-record) is the single most useful v3 rule for this note.** A sealed-battery note that conflates the three cannot express what the two-commit seal buys.
- **Rule 22 (arithmetic audit) paid for itself twice**: it surfaced the undisplayed ENG-GATE check and confirmed the note's applicability chain link by link.
- **Rule 26 (STALE-SELF-DESCRIPTION) was needed once** (`.70`) and **rule 20's `stale self-description` disposition once** (`.59`) — both for commit-pinned census figures, exactly the failure mode the note's own standing rule (`.15`) predicts.

---

## 8. SHARD NOTES

**Cross-shard supersessions applied INTO this shard (all resolved here, all homed in shard 2):** six, tabulated in §1 — AC-2 → `.34`; AC-3 → `.55`; AC-1/AC-4/AC-5 → `.63` (CHAIN-P); the acceptance record → `.02` and the SERIES GRADE-BOX `.65`–`.70`; FC-1 → `.02` and `.72`; AC-4's census-of-record pin → `.64`.

**Boundary units:** none is split across line 1167. The break falls at a `##` section boundary (§S4.3's grade box closes at 1166; §S5's heading opens at 1168), and it is independently confirmed as a semantic boundary by ITERLAWN's fold annex, which cites LIFTCORNER's S5 display as “lines 1168–1176 at acceptance” (X14).

**Material homed in shard 2 that this shard REFERENCES but does not emit:** the §S5 consequence display and its [r4, F4-6] strike; the delivery/discrepancy/disposition paragraphs; the five-line STATUS BLOCK and the three archived STATUS LINEs; the footer dating record; the acceptance record; FC-1 and FC-2; the E1 adjudication's five findings including AC-1/AC-2/AC-3; AC-4; AC-5; and the three orchestrator-verification parentheticals.

**Numbering:** temporary IDs `EFF.LIFTCORNER.s1of2.01`–`.72`, contiguous. The merge run must preserve the four CHAIN tables and the three SERIES declarations of §1, whose TERMINAL markers are the only mechanical way to know which link of each chain a chapter cut should use.

---

## 9. Self-audit and OPEN-CALLS

### 9.1 Resolved compilation calls

- The effective-text rule is DERIVED (the note states none) from four agreeing source facts, with the strike-and-replace discipline quoted from three separate round records.
- Three independent FREEZE PREDICATES were separated (text freeze; sealed-runner instrument freeze; children-generator instrument freeze with a later start date). Conflating the last two is the exact error [r3, F-C] corrects, so the separation is the note's own.
- Four internal supersession CHAINS and one inbound CHAIN were reconstructed with TERMINALs named. CHAIN-P's terminal (AC-5) reverses AC-1's suspension; a compilation that stopped at AC-1 would have recorded PROP as suspended, which is false at HEAD.
- Three SERIES were declared with their order explicit, including the r5 GAP in SERIES GRADE-BOX, which is invisible without per-entry emission.
- The scope split is THREE-way: the note landed zero appends during the HOME range, landed exactly one afterwards (ITERLAWN's fold annex, verified), and RECEIVED five inbound certifier corrections — a class neither predicate A nor B can hold.
- Every number was recomputed from primary artifacts rather than transcribed; zero discrepancies. Two figures the note does not display were supplied by the audit.
- The dead r0 wordings are classified dead and emitted only where a consumer could re-import them (four sites, resolution rule 7).
- All 9 report artifacts, all 5 verification artifacts, all 4 certifier logs, all 15 commit pins and all 18 designation XREFs verified; 4 negative edges verified.

### 9.2 OPEN-CALLS

**OPEN-CALL 1 — Does AC-1's suspension change anything the note itself still claimed? FOR-0b.**
[r5, F5-1] had already removed “and PROP's rung propagation” from the STATUS BLOCK PROVED line on 2026-08-06, four days before AC-1, leaving “(5) PROP's rung-≥2 clause-(ii) census is OWED” as the status of record. AC-1 (2026-08-12) then SUSPENDS “PROP’s “the discharge lifts to every rung”, S5’s … rider, and FC-2’s execution”. So AC-1's real targets are the S5 rider and the LANDED ITERLAWN annex, not the note's PROVED inventory. **Whether the arc treats this as “AC-1 found a live overclaim” or “AC-1 found a stale display that F5-1 had already fenced” is a note-owner judgment**, and the two readings imply different things about whether the in-house passes missed something. Not decidable from the text: AC-1 does not cite F5-1.

**OPEN-CALL 2 — The ENG-GATE check is undisplayed but load-bearing for the headline total. FOR-0b.**
§S3 reports “ENG-GATE 0 new (full=False disclosed)” and never gives its check count. The committed artifact gives it as 1, and 25,409 does not reconcile without it (the other twelve families sum to 25,408). A reader recomputing the headline from §S3's prose alone lands one short and cannot tell why. **Proposed disposition:** a one-line minors-only rider giving ENG-GATE's count. Compiler suggestion, NOT source text. Needs the note owner; the artifact governs either way by §S3's own “these govern on any transcription discrepancy”.

**OPEN-CALL 3 — ITERLAWN's fold annex records neither AC-1's suspension nor AC-5's reinstatement. FOR-0c/protocol — NEEDS ASVIN.**
FC-2 executed the rider rewrite on `ITERLAWN_PROOF_2026-08-08.md` at `5054d69` (X14, verified landed). AC-1 then SUSPENDED that execution — “**FC-2:** its execution of the all-rung rider remains SUSPENDED and must be read conditionally” — and AC-5 reinstated it — “**FC-2:** its executed rider rewrite is reinstated on the \(\Phi_1\) axis.” **Neither event is recorded on ITERLAWN**: `grep -cF 'OPACITY'` = 0 and `grep -cF 'AC-5'` = 0 (N1, N2). AC-5's own closing parenthetical schedules the fix (“transcription-confirm owed”). The net state is favorable (suspension lifted), so nothing is currently *wrong* on ITERLAWN — but a consumer reading ITERLAWN alone learns nothing of the (Φ₁-OPACITY) program, and the rung-≥2 propagation there now rests on a lemma proved in a different note's annex. Landing the AC-4/AC-5 pair on ITERLAWN is a protocol action, not a compiler decision.

**OPEN-CALL 4 — three of the four cited script files carry no freeze predicate. FOR-0d.**
`.24`/`.25`/`.26` pin `grb_order2_check.py`, `iterlawlift_corner.py` and `strata_probe.py` by line number. Only `liftcorner_checks.py` is frozen (by the two-commit seal). The note's arguments about those files are structural and survive line drift, but the pins do not. Similarly, `.10`'s four PE2-report line numbers (33, 54, 67, 471) are asserted at commit 3367f3c, and the working-tree report is not pinned to it. **Whether the corpus wants engine-file pins under a freeze predicate, or wants them re-expressed structurally, is a Phase-0d protocol question.**

**OPEN-CALL 5 — is `.15`'s standing rule corpus-binding? FOR-0d.**
“[S]tanding rule henceforth: quote counts only WITH THEIR UNIT AND COMMIT” is stated inside one note's round record after three recurrences of the same defect in that note. It is exactly the kind of rule the corpus wants, and this compilation applied it (finding `.59`'s staleness by doing so). Whether it is adopted corpus-wide is not a compiler decision.

**OPEN-CALL 6 — the `c′` census is commit-pinned and the note has moved. FOR-0b (bookkeeping).**
PE7's warrant counts 51 occurrences / 47 lines at `91f0cde`; at HEAD the counts are **54 / 50**. The three additional occurrences are in text appended after that commit (the certifier annexes), and none is a bare-`c′`-as-cocycle site by inspection — but no warrant of record covers them. Classified `stale self-description`, not error. A one-line re-execution at HEAD would close it.

### 9.3 Fidelity audit (compile-time, mechanical)

- Every CANONICAL STATEMENT in §2 is a verbatim quotation from `LIFTCORNER_2026-08-08.md` lines 1–1167, or is explicitly marked `[ASSEMBLED]` (six units: `.07`, `.09`, `.11`, `.12`, `.14`, `.15` — all six being round records whose components are quoted individually and whose seams are named), or is an out-of-range quotation from an AC/FC annex explicitly attributed to it (`.34`, `.55`, `.63`).
- Truncation inside a quotation is marked `…` at every occurrence (`.06`, `.11`, `.12`, `.13`, `.29`, `.51`, `.64`, `.66`–`.70`).
- No quantifier, index, inequality, direction, row number, or scope was altered. The one place a compiler phrase appears inside a quotation-adjacent sentence (OPEN-CALL 2's proposed rider) is explicitly marked as a compiler suggestion and is not quoted.
- No table was prosified. The two source tables (`.22`, `.39`) are reproduced as tables; the two ASCII displays that are tables in substance (`.52`'s two child listings) are reproduced with their line structure intact inside the source quotation, and their content is audited arithmetically rather than re-tabulated, since the source renders them as aligned text rather than as a table.
- Cross-file quotations (ILNRES, wave 18, ITERLAWN, GRTW2, the committed artifacts) were each independently verified at count 1 under whitespace normalization; the four that span a source line break (wave-18's open-lemma sentence, ILNRES's S5.1 deliverable, ILNRES's “at any level” clause, ITERLAWN's Lifts clause) are recorded here as verified by normalized match rather than by single-line `grep -F`, per v3 rule 15's NEAR-MISS discipline.

EFF-LIFTCORNER-s1of2 COMPILED: 72 statements / 25 xrefs verified / 6 open calls
