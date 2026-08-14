# EFF-GENHN-s1of2 — CANONICAL EFFECTIVE-SPECIFICATION SHARD

**COMPILED-BY: opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). CODEX CROSS-READ OWED (post-reset).**

## 1. Shard header

**Source note:** `lean/notes/openmath/GENHN_PROOF_2026-08-08.md` (2627 lines).

**HOME range:** source lines **1–1319** inclusive (title + round records + instrument + one-breath frame + §S0 reconciliation/conventions + §S1 STATEMENTS with the `[e2]` E2 erratum + §S2 GENHN.CLASS proof + §S3 stage ring / fibration with the `[e2]` E3 and `[r1]`/`[r2]` errata + §S4 slots + §S5 window ledger with the `[e2]` E1 erratum and the `[r2]` band annex + §S6 refine transfer / bracket / drainage + §S7 GENHN.C + `[GENHN-HE(μ ≥ 3)]` + §S8 stage towers through the `[r2]` T(b)′ annex and its REMARKS DISPOSITION). Later text (§S9–S12 and all eleven dated appends, lines 1320–2627) is used ONLY to resolve material homed in that range.

**HEAD blob hash:** `26a5c58ad13f2acd1ab3f8519cbabaaa2d0a4cbb` (clean in the working tree; last touched by commit `06958241`).

**Compilation context:** `spec/EFF_TEMPLATE_v2.md` AT HEAD (rules 1–28, i.e. v2 + the v3 prose rules). Temporary IDs `EFF.GENHN.s1of2.<nn>`.

**SHARD-BOUNDARY PROVENANCE — OPEN-CALL 1 (see §8).** `runs/qgen/sweep_manifest.txt` at HEAD carries **no GENHN row** (52 rows: T1, T2, GENTOW5, W12, HE7, T4, T5, W11, JD0, SIGMALAW, HETOW, GENTOW1/3/4/6, HEX3, HMENU3, HE6, HE6R1, **HE3**, **GRTW2**, GRTJA, WELDMASTER, GENH4, GENIND, GRTJB, GRTJC, LIFTCORNER — verified by `grep -ni genhn runs/qgen/sweep_manifest.txt`, count **0**). The charge names GENHN s1of2/s2of2 "per the manifest"; the manifest cannot supply the ranges. The split was therefore **compiler-chosen at the §S8/§S9 section break** (1319 | 1320), which (a) is a `##`-heading boundary, (b) splits 1319/1308 — within 0.5 % of an even halving — and (c) puts the whole accepted mathematical body in shard 1 and the whole boxes/battery/appends stack in shard 2. No source unit is cut. Recorded, not silently assumed.

**GENRE: TAG-SPARSE PROSE PROOF with blockquoted statement displays.** `grep -c '\tag{'` = **8** over 2627 lines (0.003 tags/line, all eight in the s2 range's LEMMA GENHN-COUNT-RERUN LaTeX). In the HOME range the tag density is **0**. Statement boundaries here are read off the note's own convention — statements live in `> ` blockquotes with a bold `THEOREM/LEMMA/CONVENTION/ERRATUM/[BOX]` opener, proofs live in unquoted prose — but every boundary inside a multi-clause blockquote was **chosen**. §6 is the mandatory BOUNDARY SELF-AUDIT.

### Governing effective-text record

**FREEZE PREDICATES (template rule 21 — three independent freezes, each with its own quote and pin):**

**(F1) TEXT-FREEZE — the accepted body, frozen at acceptance (2026-08-09, post-PE4).** Lines 1950–1953:

> “Clean count 1/2 → **2/2:
> GENHN is ACCEPTED — the text is FROZEN, dated appends only from
> here** (this line carries the counter past the title box's round-dated
> 0/2 and the post-PE3 append's 1/2).”

re-asserted at 2034–2038:

> “**Freeze discipline.** GENHN stays ACCEPTED 2/2, text FROZEN,
> dated-appends-only: this erratum is an append; the body above it is
> byte-identical to the acceptance state (pre-append file md5
> 13e087d62b4dad5a5724d337576f3411 = the file at acceptance commit
> ba3de2a, verified at this append).”

`git cat-file -t ba3de2a` → **commit** (verified).

**(F2) INSTRUMENT-FREEZE — the sealed two-commit battery, frozen at seal, independent of (F1).** Lines 1629–1632:

> “`verification/openmath/genhn_checks.py`, two-commit seal (commit 1 =
> this note + the runner, full battery UNRUN; commit 2 = §S12 verdict
> appended FROM the committed artifacts `genhn_checks_output.txt` /
> `genhn_checks_results.json`).”

The instrument freeze is **older and stricter** than the text freeze: every one of the four pre-acceptance repair rounds (`[r1]`, `[e2]`, `[r2]`, `[r3]`) states that it leaves the runner and artifacts untouched — e.g. line 583, “the sealed battery runner and artifacts are UNTOUCHED, and every battery row has f₁ = 1, where the correction is invisible”. One freeze predicate must never stand for both: **(F1) began 2026-08-09 at PE4; (F2) began at commit 1, before any hostile pass**, and (F2) survives two disclosed RE-SEALs (lines 1741–1775) that changed the *runner infrastructure* while leaving *predictions byte-unchanged*.

**(F3) PREDICTION-FREEZE — S11.D preregistered before the first full run, and byte-unchanged across both re-seals.** Lines 1624–1626 (“sealed at commit 1; predictions preregistered BEFORE the first full run”) and 1741 / 1753–1754 (“**RE-SEAL (disclosed; predictions byte-unchanged)**” / “**RE-SEAL 2 (disclosed; predictions still byte-unchanged)**”). This is a distinct predicate from (F2): the runner changed twice, the predictions did not.

**EFFECTIVE TEXT FOR THIS SHARD = lines 1–1319 exactly as written (`[r1]`, `[e2]`, `[r2]`, `[r3]` tags already landed IN-TEXT), READ AS CORRECTED by the eleven out-of-range dated appends wherever they name an in-range sentence.** The pre-acceptance rounds were applied in place — the note's own mechanism sentence, line 580–583: “GENHN is at attempt grade 0/2 (unaccepted), so this is a tagged repair, not a frozen-note annex”. Every post-acceptance correction is instead an append that quotes its target and leaves it byte-intact. **Twelve such corrections land inside this shard's range**; each is applied at its unit and listed in §7.

### Scope split (template rule 7 + rule 17 — three predicates, never conflated)

**A. ABSORPTION / supply SET** (what the note claims to prove). §S1's five displayed statements — THEOREM GENHN.CLASS, THEOREM GENHN.A, THEOREM GENHN.C, LEMMA GENHN-T, THEOREM GENHN.B — plus the four working lemmas GENHN-1/-2/-3/-4 and, at `[r2]`, LEMMA GENHN-T(b)′. The note's own one-line inventory, lines 1526–1531 (out of HOME range, homed in shard 2):

> “**One line: THEOREM GENHN.CLASS + GENHN.A(i)–(iii) + GENHN.C +
> GENHN-T(a) rest on {GENIND lemmas, W-12.A, W-11, classical} @ pins
> with no weld face; GENHN.A(iv) at μ ≥ 3 adds ONE accepted weld face
> (W-9, disclosed); GENHN.B adds GENIND.B + W-12.D @ pins and the box
> family [GENHN-HE(μ ≥ 3)]. No axiom anywhere; grade = composition
> 0/2.**”

**B. APPEND / consumption PROTOCOL scope** (what THIS note lands on other notes). **GENHN lands nothing on any supplier from inside this range.** It receives; it does not append. Where a defect it finds belongs to a consumer, the note flags the fold rather than executing it — lines 1580–1585 (out of range, governing):

> “consumers with n ≥ 8 instances (GENIND's (CS-1)/
> (CS-2) citations, the S9.2 endgame list, PROJECT_STATE's
> uniformity display) inherit that box — cross-note status is the
> orchestrator's fold, flagged here.”

and 1619–1621: “Consumers: GENIND's n ≥ 8 conditionality line inherits the refined n ≥ 10 / n ≥ 16 scoping — orchestrator's fold, flagged here.” **Zero dated consumption appends are claimed landed on any supplier by this note, and none is invented here.**

**C. INBOUND CORRECTIONS RECEIVED from supplier and hostile arcs** (template rule 17 — the DAG edges neither A nor B records). GENHN is unusually correction-rich: **six distinct inbound sources** land on this shard's range.

| # | Source | Landing form | In-range targets |
|---|---|---|---|
| 1 | `CODEX_HE6PE1_2026-08-08.md` finding 3 (adjudicated) | `[r1]` ERRATUM, in-text | `.24` (the f₁ ≥ 2 node), riding on `.23`, `.12` |
| 2 | GENH4 PE2 CRITICAL 1 + PE3 REMARK A @ pin 4b0d946 | `[e2]` ERRATUM E2, in-text | `.14` → `.12` (GENHN.A(v)'s census) |
| 3 | GENH4 PE2 GAP 1 + PE3 MINOR 1 @ pin 4b0d946 | `[e2]` ERRATUM E1, in-text | `.31` → `.29` (GENHN-3(a)'s band exit) |
| 4 | CODEX GENH4 ratification F3 @ 5c8d2fd, model GENH4 ANNEX R R3 @ b10a5a7 | `[e2]` ERRATUM E3, in-text | `.22` → `.08`, `.21`, `.33`, `.35` |
| 5 | `GENHN_passPE1..PE4_report.md` (own hostile arc) | `[r2]`/`[r3]` in-text; PE3/PE4 as dated appends | `.17`, `.23`, `.25`, `.29`, `.32`, `.38`, `.43`–`.51`, `.24` |
| 6 | `HETOW_passPE1_report.md` F-1 (a *consumer* correcting its supplier) | dated append, out of range | `.44` (T(b)′'s Φ₂ display) |
| 7 | sol certification A2/D2b/P2 (2026-08-12) | five dated appends, out of range | `.07`, `.09`, `.10`, `.16`, `.24`, `.29`, `.44` |

### Resolution rules applied

1. Lines 1–1319 supply the HOME material. All four in-text repair rounds (`[r1]` 2026-08-08, `[e2]` 2026-08-09, `[r2]` 2026-08-09, `[r3]` 2026-08-09) are **already-landed base text**, applied at their own sites in chronology; the later bracket governs the earlier text it names (e.g. `[r3]` at `.25` supersedes the `[r2]` erratum's own magnitude parenthetical; `[r3]` at `.47` corrects the `[r2]` figure 35/38 → 35/35).
2. **Post-acceptance dated appends supersede in-range text only by explicit "read X as Y" riders**, never by edit. Twelve land in range; each is carried at its unit with the rider quoted, and the superseded sentence is quoted whenever load-bearing (the note keeps it byte-intact above).
3. **Two in-range statement DISPLAYS are re-displayed by owner directive** (2026-08-12, lines 2270–2313, plus the 2026-08-12 post-D2b corrigendum at 2315–2332): GENHN.CLASS's finiteness clause (`.07`) and GENHN.A(ii)'s slot clause (`.09`). These are `SUPERSESSION KIND: replacement` at statement scope, executed under Asvin's delegated end-to-end-proof authority, and each carries a **CHAIN** with a TERMINAL marker (rule 25) because the slot clause is re-displayed twice.
4. **Two in-range clauses were adjudicated REAL-BUT-OBSTRUCTED before being re-displayed** (2026-08-12 A2, lines 2089–2099 and 2191–2195). The obstruction records are the *reason* for rule 3's re-displays and are quoted at both units; they are homed in shard 2 as `supplier-finding`-adjacent obstruction records but their CONTENT is carried here as CONDITIONALITY.
5. Where an out-of-range correction supplies a *missing lemma* rather than editing a display (LEMMA GENHN-CAP-GEN, LEMMA GENHN-LIFT, LEMMA GENHN-COUNT-RERUN), it is a **license**, not a supersession, and is recorded as such at the unit it licenses.
6. Out-of-range statements are NOT emitted as units here merely because they resolve in-range text. §S9's six boxes, §S10's stack, §S11's battery, §S12's verdict, and all eleven dated appends are homed in shard 2.
7. External repo records (report files, `verification/openmath/*` artifacts, supplier notes) are **reading notes only**, never edits. Every cited commit hash in range was verified with `git cat-file -t` (43/43 → `commit`); every cited artifact filename was verified to exist on disk.

### Quotation and table discipline

CANONICAL STATEMENTs are verbatim source quotation or explicitly marked `[ASSEMBLED]`; truncation inside a quotation is marked `…`. Every statement unit carries a `FORM:` sub-field (rule 11). The note's ASCII/Unicode displays are reproduced with line structure intact; the only presentational change is Markdown blockquote framing. The two source tables in range (§S2's realizability-floor block at `.20`, §S8's corrected-leaf-label table at `.50`) are emitted per rule 14 — the ASCII block **twice** (verbatim, then `[TABLE]`), the Markdown table once as `[TABLE]` with a rule-22 arithmetic audit. Compiler-authored ledgers (§3, §4, §5) are flagged `[TABLE — compiler ledger]` and are not source statement units.

---

## 2. Statement inventory

### EFF.GENHN.s1of2.01  [changes-record]

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

### EFF.GENHN.s1of2.02  [changes-record] · SERIES: GENHN-GRADE-ARC, member 1 of 5

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

### EFF.GENHN.s1of2.03  [instrument-record]

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

### EFF.GENHN.s1of2.04  [scope-record]

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

**SUPERSESSION KIND:** the embedded `[r2]` bracket is a **replacement** for the withdrawn sentence (“GENHN.A applied inside its own stages” is *withdrawn*, not re-read) plus a **provenance-rider** on the carrier. `TARGETS: s1of2.01` (the title's composition clause), `s1of2.17` (LEMMA GENHN-T(b)), `s1of2.18` (GENHN.B's conditionality display).

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

### EFF.GENHN.s1of2.05  [fence]

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

### EFF.GENHN.s1of2.06  [convention]

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

### EFF.GENHN.s1of2.07  [theorem]

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

**SUPERSESSION KIND: replacement** (statement scope, owner-authorized). `TARGETS: s1of2.07` (clause (ii) + header gloss), `s1of2.01` (the title's "PROVED FINITE"), `s1of2.04` ("finite per n").
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

### EFF.GENHN.s1of2.08  [theorem]  — THEOREM GENHN.A clause (i) [FIBRATION]

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

### EFF.GENHN.s1of2.09  [theorem]  — THEOREM GENHN.A clause (ii) [SLOTS + NO-CANCELLATION]

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
**SUPERSESSION KIND: replacement** (twice, at statement scope, owner-authorized). `TARGETS: s1of2.09`.
**Why no consumer moves:** “every pin the note's laws consume sits in that domain (the stage-initial node floor {dv(A_j) ≥ (μ−j)D′h + 1} and the refine floors)” (2328–2330) — i.e. the `[r1]` corrected node of `.24` is exactly what protects the re-displayed clause.

**DERIVATION:** LEMMA GENHN-2 (`.27`) and its proof (719–727) — this clause IS GENHN-2, stated at theorem level. The added phrase “W-9's dim_K 𝒜(T) = E made literal and re-proved elementarily” is a *frame* citation, not a consumption: GENHN-2's own closing sentence (716–717) is “W-9's dim_K 𝒜(T) = E = e₁ is this statement's graded shadow (cited as frame)”.

**RESOLUTION TRACE:** statement 173–178 · proof 699–727 · correction sites 2191–2195 (A2 obstruction), 2300–2313 (re-display), 2315–2332 (post-D2b corrigendum), 2101–2145 (LEMMA GENHN-LIFT, the license that makes the re-display true).

XREF: `GRTJC_PROOF_2026-08-08.md:COROLLARY W-9` — count **2** (frame citation only — see §4).
ARTIFACT: `runs/cert2/D2b_genhn_output.log` ✓ present.

**TEETH:** **PROOF-ONLY at the corrected scope.** No battery row exercises an unoccupied height: every row has `f₁ = 1` and every consumed pin sits at `dv > D′h`. The note's own coverage-hole sentence, at 1339–1351 (GENHN-BOX-3): “NOT exercised: f-first genres beyond f₁ = 2 …, mixed e₁, f₁ ≥ 2 (first live n = 8)”. **Disposition: `decorrelated-model audit`** (rule 27) — both counterexamples (R4/A2's `(3,1,2,1)`; D2b's `(1,2,1,0)`) came from a fresh-model read of the display, and no tooth could have produced them.

---

### EFF.GENHN.s1of2.10  [theorem]  — THEOREM GENHN.A clause (iii) [WINDOW LEDGER]

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
**SUPERSESSION KIND: wording-rider** for (a), **scope-pin** for (b). `TARGETS: s1of2.10`, `s1of2.29` (GENHN-3(a)/(b)), `s1of2.30` (the OB-a paragraph).
The correction is **licensed, not merely asserted**: LEMMA GENHN-CAP-GEN (2061–2085) supplies the general boundary projection with a proof, and its own scope sentence (2083) reads “Thus CS-1 and CS-2 hold at ordinary \(f_1\ge2\), \(\mu\ge3\), and mixed genres **without a new box**.”

**DERIVATION:** LEMMA GENHN-3 (`.29`) and its in-display proof; the `[r2]` band annex (`.32`) supplies the f₁ ≥ 3 transport that shows (a)'s first usage to be false.

**RESOLUTION TRACE:** statement 179–183 · proof 741–763 (GENHN-3) + 807–861 (`[r2]` annex) · correction sites 2057–2087 (R4 F-1 + GENHN-CAP-GEN).

XREF: `GENH4_PROOF_2026-08-08.md:GENH4-CAP` — count **18**.

**TEETH:** **PROOF-ONLY for the boundary clause.** No battery row sits at f₁ ≥ 2, so the band is never exercised; the note's own hole sentence is E1's exclusion (798–801): “at f₁ ≥ 2 genres beyond it (μ ≥ 3, or e₁ ≥ 2 mixed — **no battery row, first live n ≥ 8**) this note claims the LIFT-STABILITY content of (a) only and NO band-adjudication display”. The `[r2]` annex's machine contact is `passPE1`'s fresh legs at (1,3,2), N = 7 and N = 8 (851–858), which is **foreign-instrument evidence** consumed as coverage, not a row of this note's sealed battery. Disposition: `accepted-with-decorrelation-supplied`.

---

### EFF.GENHN.s1of2.11  [theorem]  — THEOREM GENHN.A clause (iv) [REFINE TRANSFER]

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

### EFF.GENHN.s1of2.12  [theorem]  — THEOREM GENHN.A clause (v) [THE LAW] + the (CS-2) bracket

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

### EFF.GENHN.s1of2.13  [scope-record]  — THEOREM GENHN.A's GRADE line

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

### EFF.GENHN.s1of2.14  [changes-record]  — `[e2]` ERRATUM E2

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

**SUPERSESSION KIND: replacement** (the census formula at band pins) plus **scope-pin** (the "away from the band" qualifier propagated to three named echoes). `TARGETS: s1of2.12` (GENHN.A(v)), `s1of2.01` (title line), `s1of2.04` (one-breath paragraph), `s1of2.36` (S6.2's assembly sentence).

**CONDITIONALITY:** **Its own HONESTY clause contains a claim the note later corrects.** “no f₁ ≥ 2 STAGE row is machine-exercised (GENHN-ERR-1's geography, none live below n = 8)” — the trailing “none is live below n = 8” half is corrected by the post-PE4 dated Correction (1957–1978), which names *this* site (“echo at [e2]-E2, L251–253”) and reads it as: “no row of THIS battery exercises an f₁ ≥ 2 stage genre …; MIXED e₁, f₁ ≥ 2 genres first live at n = 8 …; the f-first genres (1,2,2)/(1,2,3)/(1,3,2) are live at n = 4/6/6, and their S-keyed display re-read remains OWED with the residue (GENHN-ERR-1 stays unsettled exactly as displayed).” `SUPERSESSION KIND: scope-pin`. **The final clause of that correction is itself now stale** — ERR-1 was SETTLED on 2026-08-12 (2593, 2624). **CHAIN: E2's HONESTY clause → post-PE4 correction (1957–1978) → GENHN-COUNT-RERUN settlement (2593/2624). TERMINAL: the settlement, with transcription-confirmation owed.**
Second layer: LEMMA GENHN-CAP-GEN's COUNT TRANSPORT (2077–2083) re-derives E2's census independently — “A nonzero visible boundary pin has \(Q^{\operatorname{comp}(m)}-1\) choices, **exactly as ERRATUM E2 states**” — and LEMMA GENHN-COUNT-RERUN clause 4 (CR-3) proves it again from the visible F_Q-subspace. **These are licenses (decorrelated re-derivations), not supersessions.**

**DERIVATION:** Quoted inline and self-contained: by GENHN-2 a height-m K-slot is f₁ F_Q-independent components; at band heights only comp(m) of them are readable; so a nonzero pin's census counts nonzero readable data only, `Q^{comp(m)} − 1`. Instance-checked at GENH4's (1,2,2) genre.

**RESOLUTION TRACE:** statement 219–257 · correction sites 1957–1978 (PE4 F-1), 2077–2083 (CAP-GEN transport), 2396–2403 + 2563–2570 (COUNT-RERUN CR-3).

XREF: `GENH4_PROOF_2026-08-08.md:GENH4-CAP` — count **18**.
XREF: `GENH4_passPE2_report.md` — ✓ file present (the SOURCE named; the report's own designation for the finding is not quoted by GENHN, so no designation-level XREF is emitted — see source defect 4).
PINS: `0089f9b` ✓ commit · `4b0d946` ✓ commit.

**TEETH:** **`signed vacuity disclosure` (rule 20).** The erratum's own header states the vacuity: “every battery row has f₁ = 1, where comp(m) ≡ 1 = f₁ and the two censuses coincide”. Machine contact exists only at the foreign (1,2,2) instance (GENH4's committed keys) and, post-acceptance, at `genhn_pe4_fresh.py` (“first f₁ = 4 / comp = 3 / F₁₆ contact”, 1948–1949, shard 2) and `genhn_f2_count_check.py` (the P2 certificate, 2610–2614, shard 2). Both are additive post-seal legs.

---

### EFF.GENHN.s1of2.15  [theorem]

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

### EFF.GENHN.s1of2.16  [lemma]  — LEMMA GENHN-T clause (a) [the tower criterion]

**CANONICAL STATEMENT:** verbatim, lines 275–281.

**FORM:** display (blockquoted lemma, clause (a) of two).

> “**LEMMA GENHN-T (stage towers: criterion + composition).**
> (a) [criterion — proved] a stage's own read admits a composite
> opening (a TOWER event) iff the stage multiplicity satisfies μ ≥ 4
> (GENIND.A(IV) applied inside the stage); hence towers exist at
> degree n iff n ≥ (e₁f₁)·μ ≥ 2·4 = 8. n = 8 = 2·2·2 is the first
> live instance ((e₁f₁) = 2, μ = 4, inner (e₂f₂) = 2, μ₂ = 2);
> n = 4..7 are tower-free.”

**CONDITIONALITY:** **(a) is explicitly UNTOUCHED by the `[r2]` refutation** — the `[r2]` bracket's last words are “(a) is untouched.” (line 301). One correction lands inside (a)'s **proof**, not its statement: the 2026-08-12 R4 F-5 dated correction (2197–2214) replaces the proof's “residual \((T^2-c)^2\) over \(K\)” by “residual \((T-c)^2\) over \(K\)”, with the derivation: “A side of abscissa length \(4\) and denominator \(e_2=2\) has residual degree \(4/e_2=2\) … The displayed \((T^2-c)^2\) has degree \(4\) and would require side length \(e_2\cdot4=8\). The corrected form is exactly the later GN-TOWER witness \((T-1)^2\), so the positive-locus realization and the first-live threshold \(n=8\) remain unchanged.” `SUPERSESSION KIND: replacement` (proof-internal display). `TARGETS: s1of2.16` (DERIVATION only).

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

### EFF.GENHN.s1of2.17  [lemma] · SERIES: GENHN-T(b)-ARC, member 1 of 3  — LEMMA GENHN-T clause (b), REFUTED

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

**SUPERSESSION KIND: replacement** (the lemma clause is withdrawn and replaced, not re-read). `TARGETS: s1of2.17`, `s1of2.01` (title's composition clause), `s1of2.04` (one-breath echo), `s1of2.18` (GENHN.B's tower clause).

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

### EFF.GENHN.s1of2.18  [theorem]

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

### EFF.GENHN.s1of2.19  [scope-record]

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

### EFF.GENHN.s1of2.20  [table]  — §S2's realizability floors

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

### EFF.GENHN.s1of2.21  [definition]  — §S3.1 the stage ring and its entry invariants

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

### EFF.GENHN.s1of2.22  [changes-record]  — `[e2]` ERRATUM E3 (the stage-ring carrier)

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

**SUPERSESSION KIND: replacement** (the carrier object) executed as a **named-site rider list** — six sites, enumerated, not edited. `TARGETS: s1of2.08` (GENHN.A(i)), `s1of2.21` (S3.1's closing bullet), `s1of2.35` (S6's invariant maintenance), `s1of2.33` (S6.1's “gr R”), `s1of2.05` (S0's DULEMMA line); plus two out-of-range sites (S10's DULEMMA line, S9.2 item 1's “Ore over the stage ring”) homed in shard 2.

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

### EFF.GENHN.s1of2.23  [lemma]  — LEMMA GENHN-1 (the fibration)

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

### EFF.GENHN.s1of2.24  [changes-record]  — `[r1]` ERRATUM (the stage-initial node at f₁ ≥ 2) + GENHN-ERR-1

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

**SUPERSESSION KIND: replacement** (the node height) plus an explicitly **named open residue** (GENHN-ERR-1). `TARGETS: s1of2.08` (GENHN.A(i)'s node), `s1of2.23` (GENHN-1's node + the offending one-line arithmetic).

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

### EFF.GENHN.s1of2.25  [changes-record]  — `[r2]` ERRATUM (LEMMA GENHN-1's per-coordinate budget display)

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

**SUPERSESSION KIND: replacement** (the floor formula) with a nested **counter re-reading** at `[r3]` (the magnitude parenthetical's sign). `TARGETS: s1of2.23` (the budget display and the proof's node parenthetical).
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

### EFF.GENHN.s1of2.26  [scope-record]

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

### EFF.GENHN.s1of2.27  [lemma]  — LEMMA GENHN-2, THE SLOT LEMMA

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

### EFF.GENHN.s1of2.28  [convention]  — the twist (letters only)

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

### EFF.GENHN.s1of2.29  [lemma]  — LEMMA GENHN-3 (caps, raggedness, consultation)

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

### EFF.GENHN.s1of2.30  [scope-record]  — the OB-a resolution paragraph

**CANONICAL STATEMENT:** verbatim, lines 765–768.

**FORM:** inline sentence (unquoted body prose).

> “The OB-a resolution, genre-generically: the coherent object is the
> e₁-fold cover (the full integer dv-ladder), raggedness confined to
> the never-consulted band — first measured (QSCOUT22), then a ledger
> (GENH4), now a one-congruence lemma.”

**CONDITIONALITY:** **Named as a rider target by R4 F-1** — “Read “the ragged band is never consulted” everywhere in GENHN.A(iii), S5, **and the OB-a paragraph** as “the unread component cells of the ragged band are never consulted.”” `SUPERSESSION KIND: wording-rider`. `TARGETS: s1of2.30`. Its provenance chain (measured → ledger → lemma) is unaffected.

**DERIVATION:** Summary of `.29`(b)(c).

**RESOLUTION TRACE:** statement 765–768 · correction site 2087 (R4 F-1 rider).

XREF: `QSCOUT22_2026-08-08.md:Q22-A` — count **3** (the “first measured” stage).
XREF: `GENH4_PROOF_2026-08-08.md:GENH4-CAP` — count **18** (the “ledger” stage).

**TEETH:** NONE (summary).

---

### EFF.GENHN.s1of2.31  [changes-record]  — `[e2]` ERRATUM E1

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

**SUPERSESSION KIND: replacement** (the band-exit rule) plus **scope-pin** (conditionalized to the (1,2) genre pending the `[r2]` upgrade). `TARGETS: s1of2.29`(a).

**CONDITIONALITY:** **E1's own scope restriction is lifted in the very next annex.** `[r2]` (`.32`) states: “E1's corrected sentence claimed the r3 trichotomy at every μ = 2, f₁ ≥ 2 genre on (1,2)-shaped authority only … E1's transport sentence is accordingly UPGRADED from (1,2)-authority to derived at (μ = 2, e₁ = 1, f₁ ≥ 2).” And E1's exclusion clause (“at f₁ ≥ 2 genres beyond it … NO band-adjudication display — that surface sits with the S9 boxes”) is **checked and found false** by the A2 verification note (2223–2229): no S9 box holds it. GENHN-CAP-GEN then supplies the general rule. **CHAIN: frozen “exits UND exactly as” → E1 trichotomy ((1,2)-scoped) → `[r2]` annex (derived at e₁ = 1, f₁ ≥ 2) → GENHN-CAP-GEN (all ordinary genres). TERMINAL: GENHN-CAP-GEN.**

**DERIVATION:** Transcribed from GENH4 r3 at pin 4b0d946, not re-derived here — the erratum says so (“re-derived there from GENH4-3(i)'s hull partition”). The `[r2]` annex is where GENHN derives it in its own frame.

**RESOLUTION TRACE:** statement 770–805 · correction sites 807–861 (`[r2]` upgrade), 2061–2087 (CAP-GEN), 2223–2229 (the A2 check of E1's exclusion clause).

XREF: `GENH4_PROOF_2026-08-08.md:GENH4-CAP(F)` — count **11** · `GENH4-3` — count **11** · `GENH4.B` — count **7**.
PINS: `0089f9b` ✓ · `4b0d946` ✓.

**TEETH:** **`signed vacuity disclosure`** in the header (“every battery row has f₁ = 1, where the f₁ ≥ 2 band clause is vacuous”), with **foreign machine evidence** from GENH4's committed counter-keys (the four numbers audited above) and, at `[r2]`, from passPE1's fresh legs. **Disposition: `accepted-with-decorrelation-supplied`.**

---

### EFF.GENHN.s1of2.32  [lemma]  — `[r2]` ANNEX: the f₁ ≥ 3 band transport, DERIVED

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

**SUPERSESSION KIND: license** (it supplies the derivation E1 asserted on foreign authority) plus **scope-pin** on E2's readability parenthetical. `TARGETS: s1of2.31` (E1's transport sentence), `s1of2.14` (E2's parenthetical).

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

### EFF.GENHN.s1of2.33  [lemma]  — LEMMA GENHN-4 (refine transfer at general (e₁, f₁, μ))

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

### EFF.GENHN.s1of2.34  [scope-record]  — the Grade note (honesty)

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

### EFF.GENHN.s1of2.35  [scope-record]  — Invariant maintenance

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

### EFF.GENHN.s1of2.36  [lemma]  — §S6.2, the (CS-2) bracket and its reconciliation

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

### EFF.GENHN.s1of2.37  [scope-record]  — §S6.3, drainage at general genres

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

### EFF.GENHN.s1of2.38  [lemma]  — §S7's transported facts (T1)/(T2) and the Y-trichotomy

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

### EFF.GENHN.s1of2.39  [scope-record]  — Remark `[r0-battery]` (stage data vs ambient window)

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

### EFF.GENHN.s1of2.40  [open-box]  — `[GENHN-HE(μ ≥ 3)]`

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

### EFF.GENHN.s1of2.41  [changes-record] · SERIES: GENHN-T(b)-ARC, member 2 of 3  — the `[r2]` refutation and its mechanism

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

### EFF.GENHN.s1of2.42  [lemma] · SERIES: GENHN-T(b)-ARC, member 3 of 3  — LEMMA GENHN-T(b)′, setting + clause (i) [COMPOSED CARRIER]

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
`SUPERSESSION KIND: replacement` (the lift prescription). `TARGETS: s1of2.42` (the display and the overflow parenthetical).
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

### EFF.GENHN.s1of2.43  [lemma]  — T(b)′ clause (ii) [COMPOSED SLOT LEMMA — GENHN-2′]

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

### EFF.GENHN.s1of2.44  [theorem]  — T(b)′ clause (iii) [THE CORRECTED LEAF READ + σ]

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

### EFF.GENHN.s1of2.45  [lemma]  — T(b)′ clause (iv) [THE STAGE SHADOW + FAITHFULNESS THRESHOLD]

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

**CONDITIONALITY:** **The faithfulness criterion is proved; the faithfulness GEOGRAPHY is boxed.** “its genre-general proof is part of [GENHN-TOW-1]” — item (3) of the box (1392–1394): “the genre-general FAITHFULNESS geography (in particular T(a)'s event-band survival as a theorem — currently machine-verified at the PE1 instances + the P8 witness)”. The `[r3]` bracket is a **counter re-reading**: `35/38 ⇝ 35/35`, with the mechanism of the miscount named (skipped rows counted in the denominator). `SUPERSESSION KIND: counter re-reading`. `TARGETS: s1of2.45`, `s1of2.49` (the same figure recurs in the supp-contact parenthetical).

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

### EFF.GENHN.s1of2.46  [scope-record]  — T(b)′ clause (v) [COUNT-LAW FORM + LEAF LABELS] and the GRADE line

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

### EFF.GENHN.s1of2.47  [table]  — the corrected leaf labels at the PE1 instances

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

### EFF.GENHN.s1of2.48  [changes-record]  — REMARKS DISPOSITION (passPE1 R1–R4)

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

## 3. Consumption tables

### 3.1 Verified import/XREF designations

`[TABLE — compiler ledger]` Every row's count is `grep -cF '<designation>' <file>` run at HEAD, from `lean/notes/openmath/`. **38 distinct designations, all count ≥ 1.**

| # | Target : designation | Count | Role in this shard |
|---|---|---|---|
| 1 | `GENIND_PROOF_2026-08-08.md:THEOREM GENIND.A` | 4 | The stage's own history grammar over K (GENHN.A(v)) |
| 2 | `GENIND_PROOF_2026-08-08.md:GENIND.A(IV)` | 5 | The abscissa-length ≥ 4 criterion — GENHN-T(a)'s engine |
| 3 | `GENIND_PROOF_2026-08-08.md:GENIND.C` | 23 | The drainage recursion run inside the stage (§S6.3) |
| 4 | `GENIND_PROOF_2026-08-08.md:THEOREM GENIND.B` | 7 | The induction GENHN.B's discharge feeds |
| 5 | `GENIND_PROOF_2026-08-08.md:LEMMA GENIND-0` | 5 | (A1)-family closure — GENHN.CLASS(ii)'s finiteness step |
| 6 | `GENIND_PROOF_2026-08-08.md:LEMMA GENIND-1` | 2 | State classification (i), binomial kills (ii), fracture permanence (iii) |
| 7 | `GENIND_PROOF_2026-08-08.md:LEMMA GENIND-2` | 7 | Window coherence + the (b) bracket run inside the stage |
| 8 | `GENIND_PROOF_2026-08-08.md:LEMMA GENIND-3` | 6 | β-fracture fibration; the embedded-genre Hensel split |
| 9 | `GENIND_PROOF_2026-08-08.md:GENIND-5` | 9 | The (q−1)q^{2μ−1} shape being (e₁,f₁)-generalized — **not a proved theorem in its source** (OPEN-CALL 6) |
| 10 | `GENIND_PROOF_2026-08-08.md:GENIND-BOX-3` | 3 | The d = 1 ambient coverage restriction, inherited |
| 11 | `GENIND_PROOF_2026-08-08.md:GT-BRACKETID` | 3 | The μ = 3 bracket exponent c(3)+1 = 4, foreign evidence |
| 12 | `GENIND_PROOF_2026-08-08.md:GENIND-H(n)` | 7 | The per-genre package GENHN.B discharges |
| 13 | `GENIND_PROOF_2026-08-08.md:(CS-1)` | 49 | Stage transport — **the pricing grammar's real home** (see defect 2) |
| 14 | `GENIND_PROOF_2026-08-08.md:(CS-2)` | 20 | Stage bracket |
| 15 | `GENIND_PROOF_2026-08-08.md:(CS-3)` | 13 | σ-decision |
| 16 | `GENH4_PROOF_2026-08-08.md:THEOREM GENH4.A` | 5 | The n = 4 template GENHN generalizes |
| 17 | `GENH4_PROOF_2026-08-08.md:GENH4.B` | 7 | The two-term genre-F drainage display consumed at §S6.3 |
| 18 | `GENH4_PROOF_2026-08-08.md:THEOREM GENH4.C` | 9 | GENHN.C's (2,1,2)/(1,2,2) instances, verbatim |
| 19 | `GENH4_PROOF_2026-08-08.md:GENH4-1F` | 10 | The four displayed entry cancellations (GENHN-1's proof) |
| 20 | `GENH4_PROOF_2026-08-08.md:GENH4-2` | 15 | The (E)/(F) slot instances of GENHN-2 |
| 21 | `GENH4_PROOF_2026-08-08.md:GENH4-CAP` | 18 | The band cap; `GENH4-CAP(F)` (count 11) is E1's subject |
| 22 | `GENH4_PROOF_2026-08-08.md:GENH4-3` | 11 | The hull partition E1's trichotomy is re-derived from |
| 23 | `GENH4_PROOF_2026-08-08.md:GENH4-4` | 11 | Named in the S0 template list |
| 24 | `GENH4_PROOF_2026-08-08.md:GENH4-6` | 6 | Named in the S0 template list |
| 25 | `GENH4_PROOF_2026-08-08.md:law_E` | 2 | The μ = 2 stage-law evaluator, consumed at md5 pin |
| 26 | `GENH4_PROOF_2026-08-08.md:law_F` | 7 | The genre-F evaluator; the f₁ = 2 instance |
| 27 | `GENH4_PROOF_2026-08-08.md:ANNEX R` | 12 | The R3 transport obligation that E3 discharges |
| 28 | `GENH4_PROOF_2026-08-08.md:R3` | 9 | E3's stated model |
| 29 | `QSCOUT22_2026-08-08.md:Q22-A` | 3 | The committed quartic table; the n = 4/5 entry patterns |
| 30 | `W12_PROOF_2026-08-08.md:THEOREM W-12.A` | 8 | The order-1 cell law being (e₁,f₁)-re-based |
| 31 | `W12_PROOF_2026-08-08.md:W-12.D` | 19 | The reduction that fires the densities |
| 32 | `W12_PROOF_2026-08-08.md:S2.5` | 9 | The entry-law section pinned in S0 |
| 33 | `W12_PROOF_2026-08-08.md:[W12-H]` | 17 | The pricing grammar's real home (see defect 2) |
| 34 | `W12_PROOF_2026-08-08.md:(H-e)` | 8 | The box GENHN.C instantiates and GENHN shrinks to μ ≥ 3 |
| 35 | `W11_PROOF_2026-08-08.md:W-11` | 18 | The n = 2 system — the μ = 2 read's target after re-basing |
| 36 | `GRTJC_PROOF_2026-08-08.md:COROLLARY W-9` | 2 | The graded frame: FRAME at GENHN-2, CONSUMED at GENHN-4 layer 1 |
| 37 | `GRTJC_PROOF_2026-08-08.md:JC-LOAD` | 31 | Graded no-cancellation — re-proved elementarily, not consumed |
| 38 | `GRTJC_PROOF_2026-08-08.md:W-8` | 35 | Named in the S0 GRTJC bullet |
| 39 | `GRTJC_PROOF_2026-08-08.md:W-6` | 18 | Named in the S0 GRTJC bullet |
| 40 | `JD0_PROOF_2026-08-08.md:J-D0` | 25 | Count-gauge-blindness — conclusion consumed, **reason disclosed false** (`.28`) |
| 41 | `DULEMMA_PROOF_2026-08-08.md:DULEMMA` | 1 | Perimeter checked, NOT consumed |
| 42 | `SIGMALAW_PROOF_2026-08-08.md:(EC-q)` | 26 | Letter-layer coherence at towers; no count consumption |
| 43 | `HE3_PROOF_2026-08-08.md:HE3-0` | 19 | The (T1)/(T2) locus in the `[r1]` node derivation |
| 44 | `HE3_PROOF_2026-08-08.md:GENHN-HE` | 7 | The consumer that claims to close the box (reverse edge) |
| 45 | `HE6_PROOF_2026-08-08.md:LEMMA HE6-0` | 17 | dv(Φ′(ρ)) > D′h — the `[r1]` node's engine |
| 46 | `HE6_PROOF_2026-08-08.md:LEMMA HE6-3` | 12 | (SEP)-free slope bound in the same derivation |
| 47 | `HE7_PROOF_2026-08-08.md:LEMMA GENHN-2` | 1 | Reverse edge: HE7's ladder base case |
| 48 | `HE7_PROOF_2026-08-08.md:[GENHN-HE(μ)]` | 2 | Reverse edge: the predicate HE7's COROLLARY HE7.B discharges at level 2 |
| 49 | `HETOW_RECON_2026-08-09.md:HETOW-1` | 23 | The bridge lemma re-proved at the corrected composed key |
| 50 | `HETOW_RECON_2026-08-09.md:HETOW-2` | 9 | Ditto |
| 51 | `HETOW_passPE1_report.md:F-1` | 9 | The gauge-naive-lift finding landing on T(b)′ |
| 52 | `GENHN_passPE1_report.md:F1` | 7 | The T(b) refutation |
| 53 | `GENHN_passPE1_report.md:F2` | 5 | The GENHN-1 budget display |
| 54 | `GENHN_passPE1_report.md:F3` | 4 | The f₁ ≥ 3 band transport GAP |
| 55 | `GENHN_passPE1_report.md:F4` | 3 | The stage-RAM value-group repair |
| 56 | `GENHN_passPE1_report.md:F5` | 3 | The 350-vs-349 tail reconciliation (shard 2's subject) |
| 57 | `GENHN_passPE2_report.md:F1` | 9 | The depth-≥ 3 iterated composition, boxed as item (6) |
| 58 | `GENHN_passPE2_report.md:F2` | 5 | The (CS-3) full-inner-side scope |
| 59 | `GENHN_passPE2_report.md:F3` | 5 | The budget erratum's sign |
| 60 | `GENHN_passPE2_report.md:F4` | 5 | The 35/38 → 35/35 denominator |
| 61 | `GENHN_passPE3_report.md:F-1` | 4 | Item (6)(α)'s mechanism attribution |
| 62 | `GENHN_passPE3_report.md:F-2` | 5 | The "full inner sides" scope word at three echo sites |
| 63 | `GENHN_passPE4_report.md:F-1` | 3 | The "none is live below n = 8" scope defect |
| 64 | `CODEX_HE6PE1_2026-08-08.md:finding 3` | 2 | The display inconsistency that lands as the `[r1]` erratum |
| 65 | `WELDZERO_2026-08-14.md:WZ-BOX-7` | 10 | The disclosed false parenthetical at GENHN L736–737 (`.28`) |

**Designations counted but NOT emitted as XREFs (7 — recorded as source defects in §8):**
- **`read22`** — count **0** in `QSCOUT22_2026-08-08.md`. Note-local shorthand; instrument pinned by runner md5 instead.
- **`[W12-H]` / `(CS-1)` / `(CS-2)` / `(CS-3)` / `(H-e)` attributed to WELDMASTER** — all count **0** in `WELDMASTER_2026-08-08.md`. Verified referents are `W12_PROOF` (`[W12-H]` 17, `(H-e)` 8) and `GENIND_PROOF` (`(CS-1)` 49, `(CS-2)` 20, `(CS-3)` 13); the XREFs above are emitted there.
- **`GENIND-4`** — count **0** in `GENIND_PROOF_2026-08-08.md`; cited in GENHN-1's proof as a precedent for unipotent elimination. Referent not uniquely verifiable. NOT emitted.
- **`GENH4 S5`, `GENH4-S7.2`, `GENH4 S6.2`, `GENH4 S4`, `GENH4 S6.3`** — §-anchor citations; the bare section strings match many lines. Carried descriptively.
- **`OB-a`…`OB-d`** — GENH4's obstruction letters, cited by phrase.
- **passPE1 remark labels `R1`–`R4`** — not separately grep-addressable in the report.
- **`51154c95…` / `664036bc…` / `4a28246e…` / `10b685b0…`** — truncated artifact hashes; **UNPINNED** per rule 23 (see `.47`).

**Battery artifacts verified to EXIST on disk** (`verification/openmath/`): `genhn_checks.py`, `genhn_checks_output.txt`, `genhn_checks_results.json`, `genhn_pe1_fresh.py`, `genhn_pe1_fresh_output.txt`, `genhn_pe2_fresh.py`, `genhn_pe2_fresh_output.txt`, `genhn_pe3_fresh.py`, `genhn_pe3_fresh_output.txt`, `genhn_pe4_fresh.py`, `genhn_pe4_fresh_output.txt`, `genhnr2_supp.py`, `genhnr2_supp_output.txt`, `genhn_f2_count_check.py` — **14/14 present.** Foreign legs cited in range: `hetow_pe1_fresh.py`, `hetowr1_supp.py` — **2/2 present.** Logs: `runs/cert/A2_genhn_output.log`, `runs/cert2/D2b_genhn_output.log`, `runs/cert4/P2_genhn_count_output.log`, `runs/residues/R4_genhn_output.log` — **4/4 present.**

**Commit pins verified with `git cat-file -t` (all → `commit`): 43/43** — `970022b`, `4682bcf`, `4984004`, `121d9ab`, `3eb1667`, `4b5c085`, `dd67cda`, `f669cb0`, `99f1813`, `7020ceb`, `31506b3`, `83f47f4`, `9387eb1`, `f819f26`, `a27ed68`, `0089f9b`, `4b0d946`, `b10a5a7`, `5c8d2fd`, `850e77e`, `606821e`, `dcc20bb`, `380bc66`, `b653858`, `be4a1dc`, `ee17210`, `b6a1d69`, `050425d`, `19c0285`, `f60348b`, `a707430`, `58ae603`, `4e3b2ff`, `6f977ea`, `7a058c8`, `6053c3d`, `ca3754d`, `ba3de2a`, `5f821dc`, `d0d3ca6`, `5335ae3`, `701c7b1`, `beadeeb`.

### 3.2 Reverse consumer edges: mathematical supply versus append protocol

`[TABLE — compiler ledger]`

| Consumer | Verified designation | Shard-1 supply | Mathematical status | Append/consumption-protocol status |
|---|---|---|---|---|
| HE7_PROOF | `LEMMA GENHN-2` (1) | `.27` | THE SLOT LEMMA, consumed as HE7's ladder base case | **Not landed by GENHN.** HE7 cites; GENHN appends nothing there |
| HE7_PROOF | `[GENHN-HE(μ)]` (2) | `.40` | HE7's COROLLARY HE7.B claims to discharge the predicate at level 2 | **Not landed either way** — no GENHN append records it; no HE7 append lands on GENHN |
| HE7_PROOF | `GENHN-4` / `GENHN.A(iv)` | `.11`, `.33` | HE7 declares GENHN-4 **NOT consumed** (“hence no W-9 graded weld face”) | Negative edge; nothing landed |
| HE3_PROOF | `GENHN-HE` (7) | `.40` | HE3's title claims the box CLOSED at μ = 3, n ≤ 7, reduced to HE3-BOX-6 at μ ≥ 4 | **Not landed on GENHN** (verified across all eleven appends) — GENHN's S9.2 still lists it as “THE one load-bearing open lemma” |
| HE3_PROOF | `HE3-0` (19) | `.24`, `.38` | Reverse direction: GENHN *consumes* HE3-0's locus in the `[r1]` node derivation | Consumed, not appended |
| HETOW_RECON | `HETOW-1` (23), `HETOW-2` (9) | `.42` | HETOW re-proves its bridge lemmas at the CORRECTED composed key | **Landed as an inbound dated erratum ON GENHN** (1980–2032) — the one place a consumer's finding is executed inside this note |
| GENIND_PROOF | `(CS-1)`/`(CS-2)`/`(CS-3)` | `.18` | GENIND's n ≥ 8 conditionality inherits `[GENHN-TOW-1]` and the n ≥ 10 / n ≥ 16 scoping | **Not landed.** “cross-note status is the orchestrator's fold, flagged here” (1584–1585) |
| W12_PROOF / GENIND_PROOF | `W-12.D` (19), `THEOREM GENIND.B` (7) | `.18` | The composition path to the full uniformity theorem | Not landed |
| GENH4_PROOF | `ANNEX R` (12) / `R3` (9) | `.22` | GENH4's ANNEX R obliged “one rider of exactly this R3 form at GENHN.A(i)” — **discharged here**, at GENHN's own site | Inbound obligation, executed in-note; nothing appended to GENH4 |
| WELDZERO (2026-08-14) | `WZ-BOX-7` (10) | `.28`, `.11`, `.33` | Claims (a) the J-D0 parenthetical's reason is false, (b) layer 1 provable weld-free | **Not landed on GENHN.** Verified against GENHN's full append chain; WELDZERO boxes its own reading and stands at **clean-pass 1 of 2** per `spec/HYPOTHESIS_LEDGER.md` HYP.148/149 |

**The last column is not an inference.** GENHN states the protocol twice in its own words (§7 header, predicate B): consumer effects are “the orchestrator's fold, **flagged here**”. **Zero dated consumption appends are claimed landed on any supplier or consumer by this note, and none is invented here.** In the reverse direction GENHN *received* seven inbound correction streams (header predicate C), of which six land inside this shard's range.

---

## 4. NON-IMPORTS

`[TABLE — compiler ledger]` The note's explicit negative-import fences homed in lines 1–1319.

| Fence | Explicit material NOT imported or NOT proved | Unit |
|---|---|---|
| The W-2 / LIFTCORNER seam | “canonical digit-lift letters (**the W-2/LIFTCORNER seam NOT consumed**; convention-keyed histories)” | `.06` |
| DULEMMA | “applicability at general e₁ ≥ 2 stages checked as charged … **but as at GENH4 it is NOT consumed**: the exact valuation of R is proved directly (S3)” | `.05`, `.21` |
| SIGMALAW in counts | “the (EC-q) gauge-coherence ladder — named at the tower section (S8) as the letter-layer mechanism … **NOT consumed by any count law** (J-D0 keeps counts twist-free)” | `.05`, `.17` |
| Weld faces inside count laws (μ = 2) | “the slot geometry and no-cancellation are **RE-PROVED elementarily** below (GENHN-2 …), so **no weld face sits inside the count laws**” — **true at μ = 2 only**; GENHN-BOX-2 discloses the μ ≥ 3 exception | `.05`, `.27`, `.11`, `.33` |
| JC-LOAD | “this is JC-LOAD's no-cancellation holding BY CLASS SEPARATION + RESIDUE-FIELD INDEPENDENCE — **elementary, hence not consumed**” | `.27` |
| W-9 at GENHN-2 | “W-9's dim_K 𝒜(T) = E = e₁ is this statement's **graded shadow (cited as frame)**” | `.27`, `.09` |
| Maximality of R | “R = O_L at enumerated corners only …; **no general maximality claim is made or needed**” | `.22` |
| Band adjudication beyond (1,2) | “at f₁ ≥ 2 genres beyond it (μ ≥ 3, or e₁ ≥ 2 mixed …) this note claims the LIFT-STABILITY content of (a) only and **NO band-adjudication display**” | `.31` |
| Mixed genres in the `[r2]` band annex | “the e₁ ≥ 2 mixed genres **stay OUTSIDE**, as E1's exclusion list already scopes” | `.32` |
| Tower count laws | “the composed ENTRY BUDGETS … and the inner refine transfer are **NOT derived here** — boxed, [GENHN-TOW-1]”; “The sealed note **displayed no explicit tower count law**” | `.46` |
| Genre-general faithfulness | “**No genre-general classification of the faithful region is claimed here** — [GENHN-TOW-1]” | `.45` |
| Depth ≥ 3 towers | “T(b)′ is ONE composition step and does NOT self-apply … **no displayed authority prices a Φ₃-carrier without item (6)**” | `.18` (and item (6), shard 2) |
| σ at μ ≥ 3 | “the σ-decision … **is OPEN**”; “Machine corroboration (**labeled, not proof**)” | `.40` |
| Ore / Montes at order ≥ 2 | “the classical Montes/GMN order-≥2 index theorem is **the literature target for a faithful cite**” — a target, not a citation | `.40` |
| Multiplicity-weighted composition proof | the `[r2]` withdrawal: “the sentences "No new mechanism" and "inheriting exactly GENHN.A's clause grades at each level" are **WITHDRAWN**” | `.17` |

---

## 5. Teeth inverse table

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
| `.09` (GENHN.A(ii) at unoccupied heights) | GENHN-BOX-3: “NOT exercised: f-first genres beyond f₁ = 2 …, mixed e₁, f₁ ≥ 2 (first live n = 8)” — no row can reach an unoccupied height |
| `.10`, `.29`, `.31` (the boundary band at f₁ ≥ 2) | E1: “at f₁ ≥ 2 genres beyond it (μ ≥ 3, or e₁ ≥ 2 mixed — **no battery row, first live n ≥ 8**) this note claims the LIFT-STABILITY content of (a) only and NO band-adjudication display” |
| `.22` (the E3 carrier) | E3: “the battery's counts are digit-coordinate counts on Ô[x]-coefficients and its σ legs are PARI oracle reads; **neither consumes R's ring structure**” |
| `.46` (the tower count law) | GENHN-BOX-3 `[r2]`: “**tower COUNT laws remain unmeasured**, [GENHN-TOW-1]” |
| `.45` (faithfulness geography, positive half) | “its genre-general proof is part of [GENHN-TOW-1] … **currently machine-verified at the PE1 instances + the P8 witness**” |
| `.34` (layer 2 at mixed genres) | “A hostile pass should attack layer 2's strictness at mixed (e₁, f₁ ≥ 2) genres (first live n = 8, **machine-unreachable here** — S9 box)” |

**AUDIT-disposition rows (rule 27) — findings no tooth could have produced:**

| Finding | Unit | Class |
|---|---|---|
| GENHN.CLASS's declared datum set is infinite (the odd-h family at n = 4, Q = 2) | `.07` | decorrelated-model audit (sol A2) |
| GENHN.A(ii)'s “per integer dv-height” is false at `(3,1,2,1)` | `.09` | decorrelated-model audit (sol A2) |
| The re-display's “occupied = integral normalizer” is still too weak at f₁ > 1, witness `(1,2,1,0)` | `.09` | decorrelated-model audit (sol D2b) |
| “ragged band is never consulted” denotes two objects; the first usage is false | `.10`, `.29`, `.30` | in-house hostile pass turned decorrelated audit (R4 F-1) |
| E1's exclusion clause claims the surface “sits with the S9 boxes”; walking the box list shows **no box holds it** | `.31` | decorrelated-model audit (A2 verification note) |
| R = Ô[θ] is a non-maximal order, not a DVR | `.22` | transfer audit (Codex GENH4 ratification, transported) |
| The J-D0 parenthetical's stated reason is false | `.28` | decorrelated-model audit (WELDZERO r1 C-1) |

**Both-direction audit.** Every row above guards at least one in-range unit. Every in-range unit whose `TEETH` field names a battery row appears in some row. Units with **`TEETH: NONE`** — `.06`, `.13`, `.19`, `.21`, `.30` — are conventions, grade lines, indexes or frames and are outside the orphan count. Units flagged **`TEETH: Indirect`** — `.04`, `.35` — are guarded only through the composite agreement of the whole battery. **Zero battery-row orphans; zero toothed-unit orphans; six signed PROOF-ONLY units; seven AUDIT-class findings.**

Out-of-range rows recorded but not counted here (homed in shard 2): the S11.D preregistration P1–P10 as `preregistration` units, the S12 scorecard as `run-record` units, the S11.E smoke record and both RE-SEALs, the S11.F derivation, and the five post-acceptance appends' own legs (`genhn_pe3_fresh.py`, `genhn_pe4_fresh.py`, `genhn_f2_count_check.py`).

---

## 6. BOUNDARY SELF-AUDIT

GENHN is prose-with-blockquotes: statements sit in `> ` blockquotes with bold `THEOREM/LEMMA/CONVENTION/ERRATUM` openers, proofs sit in unquoted body prose, and errata sit in blockquotes too. That convention resolves most boundaries — but not the ones inside multi-clause blockquotes, which is where every hard call in this shard lives.

### 6.0 The rule applied

> **A unit is the smallest span carrying one complete claim together with its proof obligations.**

Four tests, in order: (1) does the span have a proof obligation of its own? (2) is it cited BY DESIGNATION from elsewhere? (3) does it have its OWN supersession history? (4) does it have its own conditionality or consumer set?

Proofs are NOT units (template rule 1 makes DERIVATION a field): §S2's GENHN.CLASS proof → `.07`; GENHN-1's proof → `.23`; GENHN-2's proof → `.27`; §S7's trichotomy → `.38`; T(a)'s proof → `.16`; T(b)′'s four proofs → `.42`–`.45`.

### 6.1 Boundaries drawn, with the arguable ones recorded both ways

**1. THEOREM GENHN.A split into SIX units (`.08`–`.13`).** **The shard's most consequential call.** *Candidate A:* one unit — one blockquote, one theorem, one name. *Candidate B (chosen):* six — (i), (ii), (iii), (iv), (v), GRADE. **Decided by test 3, decisively and five times over:** (i) carries E3 + `[r1]`; (ii) carries the A2 obstruction + two re-displays + the D2b corrigendum; (iii) carries R4 F-1's rider; (iv) carries GENHN-BOX-2's weld face; (v) carries E2 + the ERR-1 settlement. Under candidate A a single CONDITIONALITY field would have to hold five mutually independent chains, and a merge run could not tell which rider edits which clause. *Cost:* the theorem's blockquote is quoted in six pieces; each piece is byte-verbatim and their union is the whole display minus nothing (verified line-by-line: 156–172, 173–178, 179–183, 184–192, 193–211, 212–217 = 156–217 contiguous).

**2. LEMMA GENHN-T split into `.16` (a) and `.17` (b).** Test 3, and the source itself forces it: the `[r2]` bracket ends “**(a) is untouched.**” Not arguable.

**3. LEMMA GENHN-T(b)′ split into FIVE units (`.42`–`.46`) plus the refutation record (`.41`) and the label table (`.47`).** Test 2 and 3. (i)–(v) are cited individually and often — GENHN.B's `[r2]` rider names “GENHN-T(b)′(iii)”, the `[r3]` bracket names “(iii)'s proved perimeter”, `[GENHN-TOW-1]` item (3) names (iv)'s geography, the HETOW erratum exempts “(ii) … and the σ clauses (iii)–(v)”. Each has its own proof paragraph. *Alternative:* one T(b)′ unit with five sub-clauses. *Rejected* — the HETOW erratum alone would then have a target it cannot name precisely. **Arguable sub-call:** whether (v) and the GRADE line should split. *Chosen:* kept together at `.46`, because the GRADE line's content is exactly “(v)'s form follows from (ii)+(iii) with the budgets boxed” — it is (v)'s own grade, not the lemma's.

**4. The five in-text errata emitted as UNITS (`.14`, `.22`, `.24`, `.25`, `.31`) rather than folded into their targets' CONDITIONALITY.** **Genuinely arguable, and the call that most shapes the shard.** *Candidate A:* fold each into the clause it corrects — an erratum is not a new claim. *Candidate B (chosen):* separate units. **Three reasons, any one sufficient:** (i) each erratum carries **its own derivation** — E2 derives the comp-weighted census, `[r1]` derives the D′h node from the opening locus independently of the finding that raised it, `[r2]` derives corrected floors and checks three instances; test 1 makes a span with its own proof obligation a unit. (ii) Each is **cited by designation** — “ERRATUM E1/E2/E3” appear by name at other sites (E2's echo list names three; E3's rider list names six; `[r1]`'s residue is named GENHN-ERR-1 and cited from four later sites). (iii) Each has **its own supersession history** — `[r2]`'s magnitude parenthetical is corrected by `[r3]`; E1 is upgraded by the `[r2]` annex; `[r1]`'s residue is settled by an append. *Cost:* the corrected clause and its correction are two units, so a chapter cut must read both. Mitigated by every target's CONDITIONALITY naming the erratum unit explicitly.

**5. The `[r2]` band annex (`.32`) as a unit, not part of E1.** Test 1 and 3. It is a four-step derivation with its own exhaustive machine leg, and it *upgrades* E1 rather than restating it. *Not seriously arguable.*

**6. `.20` (the realizability floors) as a unit, split out of §S2's proof.** **Arguable.** *Candidate A:* part of `.07`'s DERIVATION — it is physically inside §S2, after the ∎. *Candidate B (chosen):* a unit — it is a table (template rule 5), it is cited from GENHN.B and from the battery grammar by the note's own words (“used by GENHN.B and the battery grammar”), and **two later appends cite it as evidence against other claims of the note** (PE4 F-1 and the F-2 re-display). A block that later text uses as a witness is addressable. *Cost:* §S2 contributes one unit that is not the theorem's proof.

**7. `.38` ((T1)/(T2) + the trichotomy) split out of `.15`'s DERIVATION.** Test 2, decisively: `(T1)`/`(T2)` are cited by designation from `.24`, `.42`, `.43`, `.44`, and from HE3's own frame. A designation cited from five places must be addressable. *Cost:* §S7's proof is quoted at `.38` rather than at `.15`, and `.15`'s DERIVATION points there.

**8. `.28` (the twist convention) as a unit.** Test 3 and 4. It is the target of an external disclosure (WZ-BOX-7) that names its exact two lines, and it is the source of the “counts are twist-blind” claim consumed at three other units. *Not arguable* once WZ-BOX-7 exists.

**9. `.33`, `.34`, `.35` split (GENHN-4 / grade note / invariant maintenance).** Test 4: three different predicates — a lemma, a grade, and a chain-invariant. `.35` is separately riddered by E3. *Alternative:* one §S6.1 unit. *Rejected* — E3's rider names the invariant-maintenance sentence specifically.

**10. `.47` (the leaf-label table) as a unit.** Template rule 5 (tables are units) plus test 2 — the `[r3]` bracket appears in **both** `.45` and `.47` and corrects the same figure at two sites, which only makes sense if both are addressable.

**11. `.19` (the obstruction scoreboard) and `.30` (the OB-a paragraph) as separate units.** *Arguable for `.30`* — three lines, no proof. *Chosen as a unit* because R4 F-1's rider names “the OB-a paragraph” as a distinct rider target alongside GENHN.A(iii) and S5. A rider with a named target needs the target addressable. **Honest cost: if the cross-read judges three-line summaries to be noise, `.30` is the unit to cut** — nothing else depends on it, and its content duplicates `.29`(b)(c).

**12. `.48` (the REMARKS DISPOSITION) as a unit.** *Arguable.* *Candidate A:* a round-record tail, fold into `.41`. *Candidate B (chosen):* a unit — R1's arithmetic is *cited as authority* at `[r3]` and inside `[GENHN-TOW-1]` item (6), so a disposition marked “no note text change” turns out to be load-bearing. Test 2.

**13. Front matter split into `.01`/`.02`/`.03`/`.04`.** Test 3 for `.01` vs `.02` (the title's composition clause and the grade line have different chains); test 4 for `.03` (an instrument description, rule 19's `instrument-record`); test 1 for `.04` (the one-breath paragraph is a claim the `[r2]` rider edits).

### 6.2 Merges deliberately NOT made, and one conflation deliberately blocked

- **§S2's proof stays inside `.07`'s DERIVATION** rather than becoming a unit: it is cited only as “S2's proof”, never by an independent designation. But note that the A2 finding indicts *the proof*, not the statement — so `.07`'s DERIVATION carries the defect's location, flagged inline.
- **(T1₂)/(T2₂) stay inside `.43`** and **(T1′)/(T2′) stay inside `.44`**: each is parented to its own clause in every occurrence.
- **The three layers of GENHN-4 stay inside `.33`**: layer 1 is where the weld face sits and is cited as “layer 1”, but always as “GENHN-4's layer 1” — parented. (Note: WELDZERO cites “GENHN-4 layer 1” as an object. If a future merge finds that citation load-bearing, layer 1 becomes addressable and `.33` should split. Flagged.)
- **CR-1…CR-8, GENHN-CAP-GEN, GENHN-LIFT, GENHN-COUNT-RERUN stay in shard 2** even though they license in-range units; each is quoted at the unit it licenses.
- **DELIBERATE NON-CONFLATION:** the phrase “**No new mechanism**” occurs twice in range — at `.17` (LEMMA GENHN-T(b), **WITHDRAWN** by `[r2]`) and at `.37` (§S6.3 drainage, **untouched**). They are different claims about different objects. A merge or a chapter cut that greps the phrase will collide; both units say so.

### 6.3 Format notes (v3 rules exercised, and one gap)

Rules 11 (FORM), 12 (three-slot trace), 14 (double-emission at `.15`, `.20`, `.31`, `.44`), 15 (NEAR-MISS ×7), 16 (PROOF-ONLY ×6), 17 (predicate C ×7 streams), 18 (SUPERSESSION KIND — this shard needed **eight of the eight kinds**: replacement, license, wording-rider, provenance-rider, scope-pin, as-of scoping, counter re-reading, inventory completion), 19 (`instrument-record` at `.03`), 20 (all four disclosure labels used), 21 (three freeze predicates), 22 (arithmetic audits on eleven displays; **all reproduced the source exactly**), 23 (43 commits verified, 20 artifacts verified, four truncated hashes marked UNPINNED), 25 (CHAIN with TERMINAL ×9), 26 (STALE-SELF-DESCRIPTION at `.02`), 27 (AUDIT dispositions ×7), 28 (three SERIES: GENHN-GRADE-ARC, GENHN-T(b)-ARC, GENHN-ERR-1).

**One gap found in v3, recorded as format evidence:** rule 18's eight SUPERSESSION KINDs have no member for **“a claim withdrawn with nothing put in its place at that site.”** The `[r2]` withdrawal of “No new mechanism” and “inheriting exactly GENHN.A's clause grades” is not a replacement (nothing replaces those sentences), not a scope-pin, and not a license — the sentences simply cease to be claims. Filed as `replacement` faute de mieux at `.17`, with the withdrawal quoted. **Proposed fix: add `withdrawal` as a ninth kind.**

---

## 7. SHARD NOTES

- **Cross-shard supersessions applied (twelve, all inbound to this range).**
  (1) **post-PE3 Correction 1** (1876–1907) → out of range (item (6)(α) lives in shard 2), but its *reasoning* bears on `.42`'s carry arithmetic; recorded, not applied.
  (2) **post-PE3 Correction 2** (1909–1928) → `.01` (title-line rider), `.18` (the `[r3]` depth-split sentence), and out-of-range site (i).
  (3) **post-PE4 acceptance record** (1941–1955) → `.02` (the grade SERIES' terminal member).
  (4) **post-PE4 Correction (PE4 F-1)** (1957–1978) → `.24` (the ERR-1 residue's scope clause) and `.14` (E2's echo of it).
  (5) **HETOW dated erratum** (1980–2038) → `.42` (the composed-key lift prescription; the f₁ ≥ 2 overflow parenthetical).
  (6) **A2 obstruction record F-2** (2089–2099) → `.07` (finiteness).
  (7) **A2 obstruction record F-4** (2191–2195) → `.09` (the slot clause).
  (8) **R4 F-1 + LEMMA GENHN-CAP-GEN** (2057–2087) → `.10`, `.29`, `.30` (the ragged-band terminology and the boundary criterion).
  (9) **R4 F-3 + LEMMA GENHN-LIFT** (2101–2189) → `.42` (licenses the corrected lift), `.09` (licenses the occupied-height re-display).
  (10) **R4 F-5** (2197–2214) → `.16`'s DERIVATION (the first tower's residual).
  (11) **Owner-directive re-displays + post-D2b corrigendum** (2270–2332) → `.07`, `.09` (both TERMINAL readings).
  (12) **LEMMA GENHN-COUNT-RERUN + Consumer sweep** (2336–2627) → `.24` (ERR-1 SETTLED), `.12` and `.36` (S-node ⇝ B = D′h re-grounding, bracket protected), `.14` (CR-3 re-derives the band census).
  LEMMA GENHN-CAP-GEN, LEMMA GENHN-LIFT and LEMMA GENHN-COUNT-RERUN are **licenses**, not supersessions: they supply content the in-range text asserted or omitted. Each is quoted at the unit it licenses and each is homed in shard 2.
- **Range-edge audit.** Line 1316–1318 is the R4 remark closing the `[r2]` annex (“R4 (GN-TOWER min-n scan verifies the arithmetic minimum only): accurate as stated by the verifier, no action needed.”); line 1319 is blank; line 1320 opens `## S9.`. **No source statement unit is cut at the edge.** The shard boundary falls exactly on a section break. (See OPEN-CALL 1 for why the boundary is compiler-chosen at all.)
- **Outside-HOME material used only as resolver, never inventoried here:** §S9.1's six boxes (GENHN-BOX-1..5 + `[GENHN-TOW-1]`), §S9.2's endgame list, §S10's supplier stack and its three `[e2]`/`[r2]`/`[r3]` ARC LINE updates, §S11's battery (A–F), §S12's verdict and scorecard, and all eleven dated appends. Shard 2 owns them.
- **Protocol versus supply.** §S1–S8's supply set is inventoried; **no consumption append is claimed landed on any supplier or consumer note**, and none is invented. Seven inbound correction streams are recorded at their targets (header predicate C).
- **Numbering.** Temporary IDs `EFF.GENHN.s1of2.01`–`.48`, to be reconciled with shard 2 at the merge run. **Merge hazards to flag:**
  (a) `.07` and `.09` have **owner-directive re-displays as their TERMINAL readings**, both “awaiting sol re-confirmation”; the merge must wire `.07 → F-2 re-display` and `.09 → post-D2b corrigendum` as explicit edges, or a chapter cut will read the frozen (false) displays as current.
  (b) `.24`'s **GENHN-ERR-1 is SETTLED with a transcription-confirmation owed** — the merge must not present it as either open or closed without that qualifier.
  (c) `.42`'s composed-key display is corrected by an append that also **names line numbers** (L1136–1148); the merge must preserve that pin.
  (d) `.11`/`.33`'s **GENHN-BOX-2 is LIVE**; a merge that sees WELDZERO must not retire it (clean-pass 1 of 2).
  (e) `.17` and `.37` share the phrase “No new mechanism”; the merge must keep them distinct (§6.2).
  (f) Three SERIES (GENHN-GRADE-ARC, GENHN-T(b)-ARC, GENHN-ERR-1) each have members in both shards; the merge must reconstruct their order from the recorded indices, not by prose-reading.

---

## 8. Self-audit and OPEN-CALLs

### OPEN-CALL 1 — the manifest has no GENHN row, and the shard split is therefore compiler-chosen

`runs/qgen/sweep_manifest.txt` at HEAD contains 52 rows and **none of them is GENHN** (`grep -ni genhn` → 0 hits; the file was verified in full). The charge names GENHN s1of2/s2of2 “per the manifest”. The split at 1319 | 1320 was chosen on three defensible grounds (§1) and lands on a `##` section break with no unit cut. **Decision needed: whether the merge run and the s2 shard adopt 1319 | 1320, and whether the manifest should be amended to record it.** No silent choice was made; the boundary and its rationale are in the header.

### OPEN-CALL 2 — GENHN-BOX-2 (the one weld face inside a count law) has a candidate discharge that has not landed, and the compiler will not apply it

`.11` and `.33` carry GENHN-BOX-2 as **LIVE**: “the count laws at μ ≥ 3 stand on one accepted weld face.” Three external records bear on it and none has landed on GENHN:
- `runs/qgen/WELD_FACE_AUDIT.md` L143–164 confirms the disclosure is correct and adds that **J-D0 cannot cover the face even in principle** (the recentering is an additive shift — the NONCHAR failure mode).
- `lean/notes/openmath/WELDZERO_2026-08-14.md` claims COROLLARY WZ-B: layer 1 without W-9. It also introduces **WZ-PIN**, a *content* decision about how GENHN-4's hypothesis “residual (T − s)^μ, s ∈ K^×” must be read, and states “Only under this reading is GENHN-4 layer 1's conclusion true.”
- `spec/HYPOTHESIS_LEDGER.md` HYP.148/149 records the arc: **clean-pass 1 of 2**, sol confirmation queued not before 2026-08-18, and “HYP.148 stays CARRY … at full strength.”
**The compiler cannot decide** whether the merged spec (a) carries GENHN-BOX-2 as live, (b) carries WZ-PIN as a reading of GENHN-4's hypothesis, or (c) waits for the second clean pass. This shard does (a) and records (b) as a disclosed external reading. **Decision needed: Asvin / the merge run.**

### OPEN-CALL 3 — three of this shard's TERMINAL readings are “awaiting confirmation”, and the spec has no vocabulary for that state

Three units' current readings are landed in the note but explicitly unconfirmed:
- `.07`, `.09` — the owner-directive re-displays, “subject to sol discharge-confirmation in the cert2 pass” (2280) and “Awaiting sol re-confirmation in the next queue” (2331–2332).
- `.24` — GENHN-ERR-1 “is SETTLED”, but “a final transcription-confirmation rides the next queue” (2626–2627).
The note's own ledger line (2263–2266) says GENHN's row “stays OPEN”. **Decision needed: whether a chapter cut may consume a landed-but-unconfirmed re-display as current.** This shard compiles all three as TERMINAL-with-confirmation-owed and refuses to collapse the distinction.

### OPEN-CALL 4 — WZ-BOX-7's false parenthetical stands unedited in frozen accepted text, and no rider exists

`.28`'s final parenthetical (“J-D0: (digits) ↦ (twisted digits) is a type-preserving bijection”) is **false**, disclosed by a consumer, with a machine witness on GENHN's own sealed data (972/972 flips). **GENHN has landed no rider** — verified against its full append chain. The *conclusion* the sentence draws is true and is what downstream text consumes; the *reason* is not. **Decision needed: whether GENHN owes a dated one-line rider, or whether the disclosure at WZ-BOX-7 suffices for the corpus.** The compiler emitted the sentence verbatim with the disclosure quoted and invented no rider.

### OPEN-CALL 5 — three scope compositions the note never writes down

(a) `.35`'s refine floor is stated as `κ > S′ ≥ e₁h`; post-`[r1]` and post-settlement the honest floor is `D′h`. The note never composes the two.
(b) `.09`'s TERMINAL slot scope is `D′h < m`; `.43`'s **composed** slot lemma (GENHN-2′) states “ONE K₂-digit per dv₂-height” with **no** occupied-height restriction, and no append addresses it. Whether the composed display needs a `D₂h`-style restriction is unaddressed.
(c) `.40`'s “Ore's theorem over the stage ring R” is the same phrase E3's rider list corrects at S9.2 item 1, but E3 does **not** name this line.
**Decision needed at 0b/chapter time: whether the merged spec composes these three, or records them as owed one-line riders.** No silent composition was made.

### OPEN-CALL 6 — two cross-note status questions the shard cannot settle

(a) **`[GENHN-HE(μ ≥ 3)]`.** `.40` carries it as OPEN, which is GENHN's own state across every append. `HE3_PROOF_2026-08-08.md`'s title claims it CLOSED at μ = 3, n ≤ 7 and reduced to HE3-BOX-6 at μ ≥ 4, and `HE7_PROOF`'s COROLLARY HE7.B claims the level-2 predicate. **Neither has landed on GENHN.** Per template rule 10 the compiler verified GENHN's full append chain rather than the frozen sentence, and there is no landing. **Decision needed: whether the merged spec reads HE3/HE7's discharges onto GENHN's box, and at what grade.**
(b) **GENIND-5.** `.36` cites it as the shape being generalized. Per `runs/qgen/WELD_FACE_AUDIT.md` LATENT-1, GENIND's own text says GENIND-5 is “NOT proved — boxed at the displayed obstruction”. GENHN uses only its displayed *form*, but a careless chapter cut could read the citation as a premise. **Decision needed: whether the merged spec tags every GENIND-5 citation as shape-only.**

### Recorded source defects (flagged, not silently repaired)

1. **`.05`:** `read22` — count **0** in `QSCOUT22_2026-08-08.md`. Note-local shorthand for the pinned quartic reader; the instrument is pinned by runner md5 `cb885663…076e` instead. Carried descriptively.
2. **`.05`:** **the WELDMASTER bullet mis-attributes four designations.** `[W12-H]`, `(CS-1)`, `(CS-2)`, `(CS-3)` and `(H-e)` all have count **0** in `WELDMASTER_2026-08-08.md`. Verified referents: `[W12-H]` (17) and `(H-e)` (8) in `W12_PROOF_2026-08-08.md`; `(CS-1)`/`(CS-2)`/`(CS-3)` (49/20/13) in `GENIND_PROOF_2026-08-08.md`. **This is a genuine mis-attribution in frozen accepted text, not a formatting near-miss** — a DAG built by grepping WELDMASTER for these names would find nothing and would silently drop three edges.
3. **`.11`, `.34`:** “GENH4 S5” — fixed-string count **0** in `GENH4_PROOF_2026-08-08.md`; the target's anchor is the bare `S5`. Referent unique; carried descriptively.
4. **`.14`:** E2's SOURCE names “GENH4 PE2 CRITICAL 1” and “PE3 REMARK A”; the reports use their own finding labels, so no designation-level XREF is emitted (the report files themselves are verified present).
5. **`.23`:** **`GENIND-4` has count 0 in `GENIND_PROOF_2026-08-08.md`.** GENHN-1's proof cites “exactly as GENH4-1F/GENIND-4”; GENIND's lemma roster is GENIND-0/-1/-2/-3/-5. The referent is not uniquely verifiable and the XREF is NOT emitted. **This is the shard's one unresolvable citation.**
6. **`.24`:** “this note's own §S3.1 remark in HE6 ("why D′h and not S = e₁h")” — the quoted phrase has count **0** in `HE6_PROOF_2026-08-08.md`, and the possessive is confusing (“this note's own … remark in HE6”). Referent independently pinned by `LEMMA HE6-0` and `LEMMA HE6-3`.
7. **`.28`:** **the J-D0 parenthetical at L736–737 is false and stands unedited** — see OPEN-CALL 4. The conclusion it decorates is true.
8. **`.36`:** “GENH4 S6.2” — §-anchor citation, count 0 as written; carried descriptively.
9. **`.47`:** four truncated artifact hashes (`51154c95…`, `664036bc…`, `4a28246e…`, `10b685b0…`) are **UNPINNED** per rule 23 — no full hash, no verifiable object. The *files* they name are present; the *versions* are not verifiable from the note.
10. **`.20` vs `.25`:** the entry-height tuple at `.20` and the floor tuple at `.25` differ by exactly the pin count (E3: 12 + 3 = 15; E31: 9 + 2 = 11). Both are correct and count different things, but **only the erratum says so** — `.20`'s own display gives no hint that its heights are pre-pin. Recorded because a reader taking `.20`'s tuple as the floor list would compute the wrong volume.

### Fidelity audit

- Every CANONICAL STATEMENT is a verbatim source quotation or is explicitly marked `[ASSEMBLED]`. **No inverse, sign, quantifier, index, level, inequality direction, or implication direction was altered anywhere.** One quoted proof carries a bracketed compiler insertion, at `.16` (`[**read (T − c)² — R4 F-5**]`), marked inline and quoted again in the CONDITIONALITY.
- Truncations inside quotations: used at `.42` (the HETOW erratum, marked `…`) and `.43`/`.44` (proof paragraphs, marked `…`). Every truncation is marked and no truncation removes a hypothesis, a quantifier, or a negation.
- Terminal punctuation inside quoted displays is preserved as written; the note's ASCII displays are reproduced with line structure intact. Markdown blockquote framing (`> `) is the only presentational addition.
- **Four source displays are emitted TWICE** (rule 14): `.15`'s σ dictionary, `.20`'s genre block, `.31`'s trichotomy, `.44`'s composed dictionary — verbatim first, `[TABLE]` transcription second. `.47`'s source table is already Markdown and is emitted once, with an arithmetic audit.
- **Eleven `[TABLE]`/display arithmetic audits were computed fresh** (rule 22) at `.15`, `.18`, `.20`, `.22`, `.24`, `.25`, `.26`, `.29`, `.31`, `.32`, `.33`, `.36`, `.37`, `.38`, `.42`, `.43`, `.44`, `.47`. **Every one reproduced the source exactly.** Two produced findings the source does not state: (i) `.37` — the four spot strata at (2,5,1) do NOT exhaust that row (the note never claims they do, but a reader could infer it); (ii) `.20`/`.25` — the pre-pin/post-pin tuple distinction (source defect 10). One produced a strengthening: `.38`'s `[r2]` repair was verified to hold at **even** `e₁` as well, which the note's own argument sketch does not make explicit.
- **65 external XREF designations, every one grep-verified with a fixed-string count ≥ 1 recorded inline and in §3.1.** Seven candidate designations with count 0 are explicitly NOT emitted and are recorded as source defects 1, 2, 3, 5, 6, 8 plus the §-anchor and remark-label classes. Two §-anchor XREFs (`W12:S1`, `GENH4:GENH4-CAP`) carry caveats that their counts are upper bounds.
- **43 commit pins verified with `git cat-file -t` (43/43 → commit); 20 artifact filenames verified present on disk (20/20); four truncated hashes marked UNPINNED.**
- Status and mathematical content are kept as distinct predicates: the acceptance chronology governs grade (`.02`, the GENHN-GRADE-ARC SERIES), the note's own flag-don't-fold protocol governs consumption (header §B, §3.2), and no append is claimed landed.
- Out-of-range material is used only to resolve in-range HOME units (resolution rule 6); shard 2 owns §S9–S12 and all eleven dated appends.
- **Honest limitation of this shard:** every one of the twelve inbound corrections is physically in shard 2, and three of them (the two owner-directive re-displays and the ERR-1 settlement) *change what the reader should believe about a frozen display*. Every affected unit quotes the governing corrective text verbatim, so shard 1 is self-contained as a *reading*, but the merge run must still install the edges listed in §7.

EFF-GENHN-s1of2 COMPILED: 48 statements / 65 xrefs verified / 6 open calls
