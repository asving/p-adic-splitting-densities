# EFF-HMENU3 — CANONICAL EFFECTIVE SPECIFICATION v2/v3

## 1. Header

**Source note:** `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md` (1,195 lines / 66,483 bytes).

**HEAD blob hash:** `59be8bae6dfc776f420a693019f5f6a773cd80ba`. Whole-file md5 at compile time: `fccf83f6400386d1506159d05668cf7e`.

**Compilation context:** `docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md`, Stage 0a, Opus wave 4, queue 8b (Asvin-authorized substitution, `docs/PROJECT_STATE.md` #51).

**Governing template:** `spec/EFF_TEMPLATE_v2.md` AT HEAD — rules 1–28. Full compilation, unsharded (66 KB, below the ~80 KB shard threshold of rule 9).

**COMPILED-BY:** opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). **CODEX CROSS-READ OWED** (post-reset).

**Queue-specific charge discharged here.** ANNEX A, ANNEX B and ANNEX C **are LANDED** (all three are dated appends physically present in this note at HEAD, L864–952, L985–1130, L1151–1180). **Template rule 10 therefore governs the frozen L216–219 sentence**: it is superseded by the append chain, not read at its pinned text. The corrected effective text of that sentence, with full annex provenance and the three-layer chain, is compiled at `EFF.HMENU3.14` and re-stated in the chain table below. The note's headline **“33-family cubic menu” is likewise superseded** — ANNEX B withdraws it in favour of **53 formal (A1) families (33 shape schemas)**; compiled at `.67`, `.69` and `.62`.

### Effective-text rule

The note carries a literal effective-text rule, stated twice.

**The freeze-convention stamp (L850–852):**

> “**FREEZE-CONVENTION STAMP**: the accepted text is the post-r2 body,
> byte-frozen since e1280be (PE4 verified all four eras read their own
> texts, zero anachronisms); dated appends only hereafter.”

**And each annex re-declares it.** ANNEX A's heading (L864):

> “## ANNEX A (dated append, 2026-08-08, post-acceptance; the frozen post-r2 body above is NOT edited): THEOREM HM3.C's (A0) quantifier corrected to the disc ≠ 0 form”

The 2026-08-12 adjudication block (L969–970):

> “Everything above this heading is byte-untouched by this append.”

**Therefore the effective text is: the post-r2 body (L1–860) read with its inline `[r1]` and `[r2]` bracket repairs applied in place, then the four dated append blocks applied in date order — ANNEX A (2026-08-08), then the 2026-08-12 sol C8/E7 adjudication and the two annexes it installs, ANNEX B and ANNEX C.** No body text is edited by any append: an append supersedes a *reading*, and the frozen sentence stays physically present. Every superseded body sentence is emitted below with a `[SUPERSEDED]` marker and its governing replacement.

**One ordering subtlety, recorded because it is easy to get wrong.** ANNEX C supersedes a sentence **of ANNEX A**, not of the body. So the append chain is not flat: A lands on the body, B lands on the body, and C lands on A. The chain table marks this.

### FREEZE PREDICATES (rule 21 — three independent freezes)

**FREEZE-1 — text freeze (acceptance).** “the accepted text is the post-r2 body, byte-frozen since **e1280be**; dated appends only hereafter” (L850–852). **PIN VERIFIED:** `git cat-file -t e1280be` = `commit` ✓. *Compiler note:* the acceptance record's own arc line names the r2 repair commit as **e1280be** (L847), while the body's `[r2]` self-descriptions and the header call the same repair r2 without a hash and the S10 arc says “r2 THIS REPAIR”. The two are consistent; `e1280be` is the freeze pin.

**FREEZE-2 — instrument freeze (the sealed runner and artifacts).** L747–748: “runner byte-identical to the sealed commit **64d3ff9** (empty `git diff`)”, artifacts `hmenu3_checks_output.txt` md5 `7f75488790df0be3f44a721f5cebe299`, `hmenu3_checks_results.json` md5 `daf077d0a417d66e45e486659a40cdbe`. ANNEX A re-affirms it at L938–940: “Runner and artifacts stay byte-frozen at the HMENU3 seal (64d3ff9 / verdict 625fa49).” **PIN VERIFIED:** `64d3ff9` and `625fa49` are commits ✓; **both artifact md5s reproduce byte-exactly at HEAD** ✓.

**FREEZE-3 — upstream instrument freeze (the seven md5 pins the runner consumes).** S7 L554–555: “HM3-PIN [NONE] (7 md5 pins: w10/w11/w12/hex3 runners, w12/hex3 results JSONs, om_density_engine.py)”. The pinned **values** are not displayed in the note (unlike HEX3, which prints its four md5s inline), so this freeze is asserted at the file level only. **Partial verification:** all seven files exist at HEAD (`w10_checks.py`, `w11_checks.py`, `w12_checks.py`, `hex3_checks.py`, `w12_checks_results.json`, `hex3_checks_results.json`, `om_density_engine.py`) ✓; four of the seven have their md5s independently pinned **by HEX3** and all four reproduce (see `spec/EFF-HEX3.md` §4.5). **Disposition: `UNPINNED-VALUE`** — the pin exists and P-1 reports it 0/7, but the note displays no hash a reader could check, so a compile-time re-verification of the other three is not possible from this note's text. Recorded, not silently passed.

### Supersession chains inside the note

`[TABLE]`

| # | Target span (frozen text) | Layer 1 (body `[r]`) | Layer 2 (ANNEX A, 08-08) | Layer 3 (ANNEX B / C, 08-12) | TERMINAL |
|---|---|---|---|---|---|
| C-1 | **HM3.C's (A0) clause, L216–219** — “so Ore certifies EVERY lift” | — | **ANNEX A site 1:** read as “so Ore certifies every lift **with disc ≠ 0**” | **ANNEX C** re-describes the change as a *strict weakening* (it does not re-supersede the reading) | **ANNEX A's reading, described by ANNEX C** |
| C-2 | §S5.2's parenthetical, L431–437 — “(not only disc ≠ 0 ones)” | — | **ANNEX A site 2:** parenthetical **WITHDRAWN** | — | **ANNEX A** |
| C-3 | ANNEX A's own sentence “This annex changes no statement's content and no proof step” | — | (introduced here) | **ANNEX C:** withdrawn and re-read | **ANNEX C** |
| C-4 | HM3.B's “**I (7 families)**” / “**II (7 families)**” | — | — | **ANNEX B:** 7 shape schemas = **11** formal fixed-λ (A1) families, each tier | **ANNEX B** |
| C-5 | HM3.B's “**B1/B2/B3 (12 families…)**” | — | — | **ANNEX B:** 12 fixed-σ schemas = **24** formal families after the m = 0 / m ≥ 1 split | **ANNEX B** |
| C-6 | HM3-BOX-5's “≤ 45 TRP aggregate families + 4 DBL + 3 SEP” | — | — | **ANNEX B:** withdrawn; read as “exactly **46** formal TRP + 4 DBL + 3 SEP = **53**” | **ANNEX B** |
| C-7 | The ACCEPTANCE RECORD's “complete **33-family** cubic core menu” | — | — | **ANNEX B:** withdrawn; read as “complete **53-formal-family** cubic core menu (33 shape schemas before the fixed-λ and b-regime refinements)” | **ANNEX B** |
| C-8 | HM3.B's (A1) integer-coefficient clause | `[r1]` PE1-F2 (strict positivity, not integrality) → `[r2]` m1 (scope-pinned to tier-I/II RAM-type) | — | — | **`[r2]` m1** |
| C-9 | Arc records (header L5, HM3-BOX-2, S10) | `[r1]` → `[r2]` | — | — → **ACCEPTANCE 2/2** (L837) → sol ledger **CERTIFIED** | **ACCEPTANCE + the ledger row** |
| C-10 | W-12 supplier-arc display, S9 bullet 1 + HM3-BOX-2 — “(arc 0/2, PE1 adjudicated, PE2 owed)” | `[r1]` PE1-F1 (PE2 had landed 26 min before the seal) → `[r2]` m2 (re-verified) | — | — | **`[r2]` m2** |
| C-11 | HEX3 supplier-arc display — “r1 ~~owed~~” | `[r2]` m2 (landed @ 2580f12) | — | — | **`[r2]` m2**, itself now stale (see §5.2) |
| C-12 | W-11 supplier-arc display — “@ its accepted pins” | `[r2]` m2 (ACCEPTED 2/2, fold 35e6545) | — | — | **`[r2]` m2** |
| C-13 | `VERDICT: PENDING` (S7 L636) | — | — | — | **§S10's GREEN** (the second commit of the two-commit protocol) |

**Three same-span collision notes.** (a) C-1 and C-3 are the *same annex* seen from two sides: A corrects the quantifier, C corrects A's description of what it did. (b) C-4/C-5/C-6/C-7 are one finding (ANNEX B's fixed-λ refinement) landing on four separate frozen displays; a chapter cut must apply all four or none. (c) C-9's terminal has two members — the in-note ACCEPTANCE (2/2) and the external SOL ledger row (**CERTIFIED**); they are different predicates and neither stands for the other.

### Scope of record — three-predicate split (rules 7 and 17)

#### A. Mathematical absorption/supply set

The note's own delivery sentence, S0 L81–89:

> “**Delivered here:** (α)-species transfer law = leaf-resolved
> self-similarity (S3.1); (β)-species transfer law = leaf-resolved
> block re-entry with the raw-key dictionary (S3.2); the instance
> bracket = LEMMA HM3-4; the finite (A1) menu = THEOREM HM3.B; (A0) and
> (A2) at n = 3 = THEOREM HM3.C — with r(N) now in EXACT closed form
> (S5.3), sharpening HEX3.B's bound. NOT delivered: the exact σ-side
> residue law U₃^σ (HEX3-BOX-1 inherited untouched — and S5.4 displays
> why it is NOT needed for W-12.D). This note edits neither W12_PROOF
> nor HEX3_PROOF; proposed annex texts are §S8.1.”

The supply set is therefore **three theorems and one corollary (HM3.A, HM3.B, HM3.C, HM3.D)** resting on **four new lemmas (HM3-1..HM3-4)**, over the suppliers W-11, W-12 (A/C/D + L0/L1 + S2.1/S2.3/S2.4) and HEX3 (H-1..H-4, HEX3.A). The number of *source obligations discharged* is **one**: W12-BOX-2's `(hMenu-3)`. The corollary additionally **fires** THEOREM W-12.D at n = 3 — a use of a proved reduction, not a discharge of an obligation.

#### B. Consumption / append-protocol scope — **LANDED at W-12**, and the note's own fence is stale

The body says (S0 L88–89, S8 heading L640): “This note edits neither W12_PROOF nor HEX3_PROOF; proposed annex texts are §S8.1”; “**S8. CONSUMERS + PROPOSED ANNEXES (texts offered; nothing edited)**”.

Per **rule 10** this is checked against the targets' full append chains.

- **W-12: LANDED, and the landing pin verifies to the byte.** `W12_PROOF_2026-08-08.md` L1685 opens “## ANNEX 2 (dated append, 2026-08-08, post-r2 — separate from the r2 repair): the W12-BOX-2 annex from HMENU3, applied verbatim”, with the wrapper recording “extracted block md5 **4eb3bacc30e3be0bc8a08a72cf9d9473**, byte-identical to HMENU3 §S8.1 lines 573–585”. `grep -cF 'BOX-2 ANNEX' W12_PROOF_2026-08-08.md` = **1** ✓. **PIN VERIFIED AT COMPILE TIME:** the md5 of HMENU3's **L644–656** (blockquote prefixes included) is exactly `4eb3bacc30e3be0bc8a08a72cf9d9473` — so the extracted block is byte-identical to HEAD's §S8.1 annex, located to the line. **The wrapper's line cite is nonetheless stale:** the block is at L644–656 at HEAD, not 573–585, the r1/r2 repairs having shifted the body by 71 lines after extraction. Recorded as a **stale line cite in the consumer**, not a HMENU3 defect — the md5, not the line range, is the binding identity, and it holds.
- **W-12 also carries an inbound notice.** `W12_PROOF` L1722ff: “**[r5] NOTICE ON ANNEX 2** (dated append, 2026-08-08, written at the r5 repair; the ANNEX 2 text above is UNTOUCHED and stays verbatim as applied — this is a notice about its supplier, not an edit to it).” `grep -cF 'NOTICE ON ANNEX 2'` = **1** ✓. That notice is what raised ANNEX A.
- **HEX3: NOT landed, and correctly so.** The §S8.1 “HEX3 S8.2 pointer” block (`.53`) has no counterpart in `HEX3_PROOF_2026-08-08.md`: `grep -cF 'HEX3 S8.2 pointer'` there = **0**. HEX3's own appends address the same content independently (its Correction A). Recorded as an **outstanding, and arguably obviated, offer**.

So the protocol scope is: **one absorption offered to two notes; LANDED verbatim at W-12 (with a stale line cite in the consumer's wrapper), NOT landed at HEX3.** The heading's “nothing edited” is a `STALE-SELF-DESCRIPTION` (rule 26) for the W-12 leg.

#### C. Inbound corrections RECEIVED from supplier notes (rule 17)

Four, all quoted at their targets.

1. **From W-12's r4 (`d2d91b7`) and r5, via the ANNEX 2 notice** — the unrestricted-lift quantifier. This is what ANNEX A repairs. Recorded at `.63`.
2. **From W-12's PE2 (`1be15d2`) and r2 (`99f1813`)** — the supplier-arc display was stale at seal time; repaired by `[r1]` PE1-F1 with a fired-clause check. Recorded at `.34` and `.55`.
3. **From W-11's acceptance (PE3 `839b735`, PE4 `16d12e1`, fold `35e6545`)** — the supplier is now ACCEPTED 2/2; folded by `[r2]` m2. Recorded at `.55`.
4. **From HEX3's PE1 (`d177fd8`) and r1 (`2580f12`)** — HEX3's gap 1 grazes H-2(i), which §S3.1 fires by name; the `[r2]` m2 fired-clause record establishes the consumed conclusion survives. Recorded at `.34`.

An **outbound** correction also exists: ANNEX A's cross-reference sweep names `HEX3_PROOF` L80–81 as carrying the same loose phrasing, “a phrasing correction owed at HEAD3's own arc”. HEX3 subsequently repaired exactly that site at its own `[r4]` — see §5.2 RX-3. **This is a supplier-finding that was discharged at the source**, and it is the reason `.63` is typed as it is.

### Resolution rules applied

1. Body brackets `[r1]`/`[r2]` are part of the frozen post-r2 body and are applied in place; each names its own target.
2. Appends apply in date order; ANNEX C lands on ANNEX A, not on the body (see the ordering subtlety above).
3. **ANNEX B is a refinement, not a recount of the same objects.** Its own closing sentence fences this: “This annex repairs a formal indexing gap. It changes no raw-key law, density, complement, splitting-type formula, machine result or conditionality.” A consumer must not read 33 → 53 as a correction to any count.
4. **ANNEX A is a strict weakening**, per ANNEX C, and must be described as such. Saying it “changes no statement's content” is the exact error ANNEX C exists to correct.
5. The frozen grade vocabulary — header “**Attempt grade 0/2**”, the S1 GRADE box, HM3-BOX-2, S9, S10 — is superseded by the ACCEPTANCE record (2/2) and the SOL ledger (**CERTIFIED**). Tagged `STALE-SELF-DESCRIPTION` where no append reaches it.
6. The three supplier-arc displays (C-10/11/12) are **as-of records**; their `[r1]`/`[r2]` refreshes are terminal *within the note*, but two of the three have since moved again in the corpus (§5.2). Flagged at each site; nothing invented.
7. Where the note's own text presents a hostile-run adjudication verbatim (the E7 block, L972–1180), the adjudication's findings and the annexes it installs are emitted as separate units, since a finding and its repair carry different truth conditions.
8. Out-of-note material (W-12, W-11, HEX3, GENIND, the ledgers, N3_CHECK) is used only to resolve and verify.

### Quotation and prosification discipline

Every CANONICAL STATEMENT is a verbatim quotation or is explicitly marked `[ASSEMBLED]`. The note's displays are indented plain text (the raw-key alphabet, the dictionary, the A_L laws, the R_τ table, the census polynomials, ANNEX B's counts) and are reproduced with line structure intact; each is additionally emitted as a `[TABLE]` transcription where it is a table in substance, **alongside** and never instead of the source form (rule 14's spirit; the note contains no fenced ASCII block, so rule 14's letter is not triggered — checked, not skipped). Terminal punctuation and the `∎` marks are preserved. The note's strikethrough (`~~…~~`) is reproduced, since in this note it marks supersession. Compiler classifications are metadata, never source paraphrase.

---

## 2. NON-IMPORTS

**N-1 — the five named non-consumptions.** S9 L728–730:

> “**NOT consumed:** the weld notes ([W12-H] untouched — all n = 3
> reads are order-1), the measure route, `htameFE`, PARI beyond the
> IND leg, the tail-σ-certification lemma (S5.4).”

**N-2 — the tail-σ-certification lemma is explicitly off the critical path.** S5.4 L463–467 and HM3-BOX-1. This is the note's most consequential negative import, because it is what lets `(hMenu-3)` discharge while HEX3-BOX-1 (ledger HYP.137) stays open.

**N-3 — the density engine supplies no count law.** S9 L720–723:

> “**om_density_engine.py + reconcile_om_bcfg.py artifacts**
> (md5-pinned; committed) — the R_τ cross-tie ONLY (β(2)/β(3)
> cluster laws; their BCFG reconciliation is the literature-adjacent
> leg). No count law consumes them.”

**N-4 — nothing is claimed beyond n = 3.** HM3-BOX-4 L538–543: “nothing here claims beyond n = 3.”

**N-5 — the exploratory observation is fenced.** S1 L266–267: “EXPLORATORY observation (no proof claimed): the three unramified densities satisfy R_τ = q³·β₃(τ).”

**N-6 — the oracle is characteristic-blind by construction.** HM3-BOX-3 L534–535 and ANNEX A L930–937: “Oracle: mixed-characteristic only, per-center representatives only”. ANNEX A turns this disclosure into a positive finding — “blind, not wrong — and blind by construction” — which is why no oracle verdict was falsified by the quantifier defect.

**N-7 — no source file is edited by the composition.** S0 L88–89 / S8 heading. **STALE for the W-12 leg** (header §B).

**N-8 — ANNEX B changes nothing measured.** L1128–1130: “It changes no raw-key law, density, complement, splitting-type formula, machine result or conditionality.”

**N-9 — no axiom, no weld face.** S9 L734.

---

## 3. Statement inventory

IDs `EFF.HMENU3.01`–`.72`.

### EFF.HMENU3.01  [record]

**CANONICAL STATEMENT** (verbatim, the title block, L3–27). FORM: bold-headed paragraph.

> “**Unit:** HMENU3 (the (hMenu-3) attack; W-12's BOX-2 = the TRP
> refinement-family menu, the last named hypothesis of THEOREM W-12.D at
> n = 3 after HEX3 discharged (hExhaust-3)). **Attempt grade 0/2** (arc:
> composed → PE1 NOT CLEAN 0C+1G+1m @ f4f7b03 → r1 3235e1b,
> note-only, [r1] tags, minimality contract — the stale W-12
> supplier-arc display (GAP) + the HM3.B integer-coefficient clause
> (minor) repaired in place → PE2 NOT CLEAN 0C+0G+2m @ af988ee (every
> substantive charge CONFIRMS; both minors are display-precision
> defects inside [r1] brackets) → r2 THIS REPAIR, note-only, [r2]
> tags, minimality contract — the m1 carry-scope fix + the m2
> fired-clause record and supplier-arc refresh; counter 0/2; PE3
> next). **Instrument:** sealed two-commit
> battery `verification/openmath/hmenu3_checks.py` — 41 census rows =
> 94,824,902 per-center TRP states read individually with the FULL
> refinement history recorded per state (18 ℤ_p rows incl. q = 13, 23
> 𝔽_q[[t]] rows incl. q = 4, 8, 9, 27; 15 cross-characteristic (q, N)
> pairs; 3 never-measured rows incl. the first q = 27 row in the
> corpus), per-key equality against the recursive closed-form predictor
> BOTH directions, the aggregate (A1) layer both directions, pointwise
> ties to the SEALED w12 reader (decided verdict + depth-0 key + σ),
> ties to the COMMITTED w12/hex3 JSONs, a PARI σ-oracle on EVERY
> deep-decided member of four rows (9,952 members — deep TRP σ was
> never independently oracled before this unit), a symbolic
> R_τ leg, and four teeth at preregistered exact fire counts. Verdict
> §S10, appended at commit 2 FROM the committed artifacts.”

**DERIVATION.** [RECORD] — chronology plus instrument description (rule 19: the two halves have different truth conditions and are dispositioned separately below).

**SERIES membership (rule 28).** **ARC SERIES member 1.** Order: `.01` (header, r2-era) → `.34` (HM3-BOX-2, r2-era) → `.59` (§S10, r2-era) → `.60` (the ACCEPTANCE RECORD, 2026-08-08, superseding all three) → `.72` (the SOL-ledger CERTIFIED line, 2026-08-12).

**CONDITIONALITY.** The arc half (“**Attempt grade 0/2**” … “counter 0/2; PE3 next”) is **SUPERSEDED** by `.60`. `STALE-SELF-DESCRIPTION` where the acceptance record does not reach it by name.

**Arithmetic audit (compiler-recomputed).** 18 + 23 = **41** rows ✓. `Σ q^{3(N−1)}` over the roster = **94,824,902** ✓ — exact. Shared `(q,N)` pairs across ring types = **15** ✓. Never-measured rows = **3** ✓ (`(Fqt,2,9)`, `(Fqt,3,6)`, `(Fqt,27,2)`).

**XREF.** `W12_PROOF_2026-08-08.md` — `W12-BOX-2`, count 8; `THEOREM W-12.D`, count 5. `HEX3_PROOF_2026-08-08.md` — `(hExhaust-3)` appears there; in `W12_PROOF` count 10. **PIN VERIFICATION:** `f4f7b03`, `3235e1b`, `af988ee` all resolve to `commit` ✓; `verification/openmath/hmenu3_checks.py` EXISTS ✓.

---

### EFF.HMENU3.02  [scope-record]

**CANONICAL STATEMENT** (verbatim, L29–49). FORM: bold-headed paragraph.

> “**What HMENU3 is (one breath).** THEOREM W-12.D (PROVED,
> unconditional as a reduction) turns {exact disjoint q-uniform core
> menu (A1) + lift well-posedness (A0) + drainage (A2)} into ONE
> R_τ ∈ ℚ(q) per splitting type; at n = 3 its conditionality was
> exactly {(hMenu-3), W12-BOX-2} + {(hExhaust-3), W12-BOX-3}, and HEX3
> discharged the latter. The missing menu piece was the TRP (triple
> center) refinement families — BOX-2's two node species. This unit,
> examples-first (Asvin 2026-08-05): STAGE 1 built the complete
> empirical family table by reading every TRP state's full refinement
> history (the raw key) at 41 (ring, q, N) and fitting one law per key;
> STAGE 2 proved the table: the four depth-0 refine species transport
> LEAF-RESOLVED — (α) onto the scaled TRP system itself (self-similar,
> key-sheared), (β1)/(β2)/(β3) onto the W12-L0 history-resolved n = 2
> block system with a raw-key dictionary — so the whole decided TRP
> mass is generated by a finite recursion whose every branch carries an
> exact q-polynomial count. The α-prefix bracket telescopes to
> (q−1)q^{4m−1} (LEMMA HM3-4), collapsing the infinite history tree
> into a FINITE aggregate family list with affine exponents — exactly
> (A1)'s required shape. With the SEP/DBL strata already supplied by
> W-12.A + W12-L1/W12-L0, the n = 3 hypothesis package of W-12.D is
> complete: the cubic splitting densities come out in closed form.”

**DERIVATION.** [RECORD] — the method statement, load-bearing twice: it is the **fit disclosure** (STAGE 1 fitted one law per key against measurement) and the **proof-order statement** the derivations of `.08` and `.11` consume.

**CONDITIONALITY.** “THEOREM W-12.D (PROVED, unconditional as a reduction)” is the load-bearing supplier claim; it is qualified at `.55` by W-12's own arc grade, which the corollary inherits.

**XREF.** `W12_PROOF_2026-08-08.md` — `THEOREM W-12.D`, count 5; `THEOREM W-12.A`, count 8; `W12-BOX-2`, count 8; `W12-BOX-3`, count 7; `LEMMA W12-L0`, count 5; `LEMMA W12-L1`, count 7.

---

### EFF.HMENU3.03  [imported]

**CANONICAL STATEMENT** (verbatim, S0 L55–63 — the absorbed source obligation, quoted as “**W12-BOX-2, verbatim** (W12_PROOF_2026-08-08.md §S6)”). FORM: display (blockquoted source box).

> “**W12-BOX-2 (n ≥ 3 refinement families; (hMenu-3)).** The depth-≥ 1
> TRP families are not enumerated: the n = 3 instance bracket needs
> TWO node species — (α) the triple-cluster node and (β) the
> DBL-re-entry node at reduced window (S3.1) — and neither species'
> transfer law is derived. W-12.D at n = 3 is conditional on this
> menu; it is the natural W-13 rung, with S2.4's depth-0 completeness
> as its floor.”

**DERIVATION.** [IMPORTED] — the obligation HMENU3 discharges.

**VERBATIM-CLAIM VERIFICATION (compiler-performed, since the note labels the quote “verbatim”).** Compared clause by clause against `W12_PROOF_2026-08-08.md` **L1218–1224**: **identical**, including line breaks and the closing “floor.” ✓. The “§S6” attribution also verifies: `## S6. HONEST BOXES (where this note stops)` is at L1211, the last section heading before L1218 ✓. **The verbatim claim is true.**

**CONDITIONALITY.** None as an import.

**XREF.** `W12_PROOF_2026-08-08.md` — `W12-BOX-2`, count 8; `S2.4`, count 10; line-addressed L1218–1224, verified.

---

### EFF.HMENU3.04  [imported]

**CANONICAL STATEMENT** (verbatim, S0 L65–79, with the `[r1]` seam bracket in place). FORM: bold-headed paragraph.

> “**What (A1)/(A2) demand** (W-12.D as stated, §S1(iii)): a FINITE list
> of core families F, each with a splitting type σ_F, a parameter set
> P_F ⊆ ℤ^{d_F}_{≥0} that is a finite union of shifted products of
> arithmetic progressions, an affine visibility threshold ν_F, and an
> exact window count dens_F(x)·q^{3N} with dens_F = c_F(q)·q^{−ℓ_F(x)},
> ℓ_F affine with strictly positive parameter coefficients [r1, PE1
> FINDING 2 seam: the sealed "integer" here misquoted W-12.D §S1(iii),
> which demands strict positivity only; the geometric-series display
> consumes m_i·b_i ∈ ℤ_{>0} + ℓ(base) ∈ ℤ (W-12 [r1 m1]/[r2 G3]) —
> see the HM3.B repair bracket] — families
> pairwise DISJOINT, all data q- and characteristic-independent; (A0):
> every window member of a core family has ALL its disc ≠ 0 lifts of
> the family's σ; (A2): r(N) := q^{3N} − Σ_{visible} count → 0 after
> normalizing — r is DEFINED as the complement, so window-boundary
> (tail) families route through it with no σ-labeling required.”

**DERIVATION.** [IMPORTED] — the admissibility contract HM3.B must meet.

**SUPERSESSION KIND (the `[r1]` bracket):** `replacement` — the sealed word “integer” is replaced by “strictly positive”, with the actual integrality guard named (`m_i·b_i ∈ ℤ_{>0}`). **TARGETS:** `.13` (the HM3.B admissibility clause), which carries the same repair at greater length.

**CONDITIONALITY — and the single most important cross-reference in this note.** The (A0) as stated **here** is already the disc ≠ 0 form: “every window member of a core family has **ALL its disc ≠ 0 lifts** of the family's σ”. **This is what makes ANNEX A a phrasing repair rather than a theorem change** — ANNEX A cites this very line (L75–76) as evidence that “The note's intended content was the disc ≠ 0 form throughout”. A chapter cut must carry `.04` alongside `.14`, or ANNEX A's argument is unreadable.

**XREF.** `W12_PROOF_2026-08-08.md` — `S1`, section anchor (`## S1.` at L57); `THEOREM W-12.D`, count 5.

---

### EFF.HMENU3.05  [absorption-record]

**CANONICAL STATEMENT** — the S0 “Delivered here” paragraph, quoted in full in §1 header predicate A (L81–89). FORM: bold-headed paragraph.

**DERIVATION.** [RECORD] — the delivery/absorption ledger.

**STALE-SELF-DESCRIPTION (one clause, rule 26).** “This note edits neither W12_PROOF nor HEX3_PROOF; proposed annex texts are §S8.1.” True of HMENU3's own action; **stale as a corpus description for the W-12 leg** — the §S8.1 BOX-2 annex landed verbatim at `W12_PROOF` L1685ff, with its extracted-block md5 verifying against HMENU3 L644–656 at HEAD (header §B). Accurate for the HEX3 leg, where nothing landed.

**CONDITIONALITY.** The “NOT delivered” half — the exact `U₃^σ` law, HEX3-BOX-1 — is current and is ledger row **HYP.137** (see §5.3).

**XREF.** `W12_PROOF_2026-08-08.md` — `BOX-2 ANNEX`, count 1. `HEX3_PROOF_2026-08-08.md` — `HEX3-BOX-1`, count 11.

---

### EFF.HMENU3.06  [convention]

**CANONICAL STATEMENT** (verbatim, S1 L93–97). FORM: inline sentence.

> “Conventions as in W-12 §S1 / HEX3 §S1 (O a complete DVR with residue
> field F_q, either characteristic; window N ≥ 2; the recursive
> OM-convention conservative read; the TRP stratum at a fixed center =
> recentered states (B₂, B₁, B₀) ∈ (πO/π^N)³, whole space = ×q centers
> by the translation bijection).”

**DERIVATION.** [IMPORTED].

**CONDITIONALITY.** Same `N ≥ 2` / `N ≥ 1` seam as its suppliers: THEOREM HM3.A is asserted for “every N ≥ 1” while the conventions assume `N ≥ 2`. Resolved upstream by HEX3-BOX-5's `u(q,1) = 1` seed convention; not re-stated here.

**XREF.** `W12_PROOF_2026-08-08.md` — `S1` (section anchor at L57). `HEX3_PROOF_2026-08-08.md` — §S1 at L109.

---

### EFF.HMENU3.07  [definition]

**CANONICAL STATEMENT** (verbatim, S1 L97–111). FORM: display (indented alphabet) inside a paragraph.

> “The RAW KEY of a state is the full
> chain record: one step per refine event, each classified at its own
> frame —
>
>     ('ALPHA', d)      FULL side, residual (y−z)³         (d = raw depth)
>     ('FULL11SQ', d)   FULL side, residual (y−z)²(y−z′), z′ ≠ z
>     ('VERT1', u₀, k)  vertex at 1, right-side residual (y−z)²
>     ('VERT2', u₀, t)  vertex at 2, left-side residual (y−z)²
>
> — terminated by a decided depth-0-shape leaf ('RAM3', h) /
> ('3LIN', m₁, m₂, m₃) / ('LINRAM2', u₀, u₁) / ('RAM2LIN', u₀, t) /
> ('VERT1', u₀, k, λ) / ('VERT2', u₀, t, λ) / ('FULL', k, λ) or by
> ('DRAIN',) (the conservative B₀ = 0 exit). All parameters are RAW
> (original-window) coordinates. The read is deterministic, so the raw
> keys PARTITION the state space (disjointness is structural).”

`[TABLE]` (compiler transcription of the two alphabets — emitted alongside, never instead of, the source display)

| kind | symbol | frame content |
|---|---|---|
| refine step | `('ALPHA', d)` | FULL side, residual `(y−z)³`, `d` = raw depth |
| refine step | `('FULL11SQ', d)` | FULL side, residual `(y−z)²(y−z′)`, `z′ ≠ z` |
| refine step | `('VERT1', u₀, k)` | vertex at 1, right-side residual `(y−z)²` |
| refine step | `('VERT2', u₀, t)` | vertex at 2, left-side residual `(y−z)²` |
| leaf | `('RAM3', h)` | — |
| leaf | `('3LIN', m₁, m₂, m₃)` | — |
| leaf | `('LINRAM2', u₀, u₁)` | — |
| leaf | `('RAM2LIN', u₀, t)` | — |
| leaf | `('VERT1', u₀, k, λ)` | **carries λ** |
| leaf | `('VERT2', u₀, t, λ)` | **carries λ** |
| leaf | `('FULL', k, λ)` | **carries λ** |
| exit | `('DRAIN',)` | the conservative `B₀ = 0` exit |

**DERIVATION.** [DEFINITIONAL]. Disjointness is derived in one clause — determinism of the read — and the note flags it as *structural*, i.e. not a proof obligation.

**CONDITIONALITY.** Unconditional. **This unit is the load-bearing precondition for ANNEX B** (`.67`): three leaf kinds carry λ, which is exactly why fixing λ refines disjoint fibers without touching any law. ANNEX B says so: “The raw-key recursion already records λ, so this is a finite refinement of the stated disjoint fibers, not a change to HM3.A or to any count.”

**XREF.** none external.

---

### EFF.HMENU3.08  [theorem]

**CANONICAL STATEMENT** (verbatim, S1 L113–143 — THEOREM HM3.A). FORM: display (blockquoted theorem with bulleted recursion clauses).

> “**THEOREM HM3.A (the history-resolved exact menu).** For every prime
> power q, both characteristics, every N ≥ 1, the per-center count of
> every raw key is given exactly by the recursion pred3 (sealed in the
> runner; the note's S2–S4 in formulas): writing M for reduced
> windows and m for raw split/shear depths,
>
> * depth-0 decided keys: the seven W-12.A S2.4 laws (loop ranges =
>   visibility);
> * (('ALPHA', s+k),) ⌢ K for K a window-(N−3k) key at shear s+k:
>   count = (q−1)·q^{3k} × (window-(N−3k) count of K);
> * (('FULL11SQ', m),) ⌢ D_m(hist, leaf):
>   count = (q−1)(q−2)·q^{3k+M−1} × L0(hist, leaf; M);
> * (('VERT1', 3k+w+3s, m),) ⌢ D_m(hist, leaf):
>   count = (q−1)²·q^{3k+M−1−w} × L0(hist, leaf; M);
> * (('VERT2', (3t+2j)+3s, t+s),) ⌢ D_m(hist′, leaf):
>   count = (q−1)·q^{3t+M−1} × L0((j)⌢hist′, leaf; M);
>
> where L0 = the W12-L0 history-resolved n = 2 block laws (consumed at
> pin) and D_m = the raw-key DICTIONARY at split depth m:”

*(The dictionary display that continues this sentence is emitted separately at `.09`; the σ rule and the drain remark at `.10`.)*

**DERIVATION.** The proof chain, resolved: LEMMA HM3-1 (`.19`–`.21`) supplies the two-phase grammar and hence exhaustiveness of the clause list; LEMMA HM3-2 (`.22`) proves the α clause; LEMMA HM3-3 (`.23`) proves the three β clauses; §S3.3 (`.24`) assembles by induction on the window. The depth-0 clause is [IMPORTED] from W-12.A §S2.4.

**Arithmetic audit — the four transport prefactors cross-checked against HEX3's drain-mass forms.** HEX3's species table gives drained masses `(q−1)q^{3k}u(N−3k)` (α), `(q−1)(q−2)q^{3k+M−1}R(M)` (β1), `(q−1)²q^{3k+M−1−w}R(M)` (β2), `(q−1)²q^{3t+M−1+j}R(M−2j)` (β3). HM3.A's prefactors are **identical for α, β1, β2** ✓, with `R(M)` replaced by the leaf-resolved `L0(hist, leaf; M)`. **β3 differs by design:** HM3.A carries `(q−1)·q^{3t+M−1}` where HEX3 carries `(q−1)²·q^{3t+M−1+j}` — because HM3.A routes the `j`-entry through `L0((j)⌢hist′, …)`, which absorbs one `(q−1)` (the entry letter) and the `q^{j}` into the block history. The note states exactly this at `.23`: “its z-letter is the (q−1) inside L0's (j)⌢hist′ bracket”. **The two forms are consistent, and the difference is documented rather than latent** ✓.

**CONDITIONALITY.** S9 L732–734: “THEOREM HM3.A/B/C's hypothesis set = {W-11, W-12.A/L0/L1, HEX3 H-1..H-4 @ pins, + this note's transports/bracket}”. Grade at HEAD: **ACCEPTED 2/2** (`.60`) and ledger-**CERTIFIED** (`.72`). Unaffected by ANNEX A, ANNEX B or ANNEX C — all three say so explicitly.

**XREF.** `W12_PROOF_2026-08-08.md` — `THEOREM W-12.A`, count 8; `S2.4`, count 10; `LEMMA W12-L0`, count 5; `W12-L0`, count 32.

---

### EFF.HMENU3.09  [table]

**CANONICAL STATEMENT** (verbatim, S1 L133–138 — the raw-key dictionary `D_m`). FORM: display (indented two-column table).

> “    block refine at depth k′       ↦ ('VERT2', 3m+2k′, m)
>     RAM(u)                         ↦ ('RAM2LIN', 3m+u, m)
>     2SIDED(w, u−w)                 ↦ ('3LIN', m+(u−w), m+w, m)
>     SPLITEQ(k′)                    ↦ ('VERT2', 3m+2k′, m, λ=(1,1))
>     INERTDEEP(k′)                  ↦ ('VERT2', 3m+2k′, m, λ=(2))
>     SPLIT-TAIL / UNDECIDED         ↦ ('DRAIN',)”

`[TABLE]` (compiler transcription, emitted alongside the source display)

| block object (n = 2 side) | raw-key image at split depth `m` | λ fixed? |
|---|---|---|
| block refine at depth `k′` | `('VERT2', 3m+2k′, m)` | refine step, no λ |
| `RAM(u)` | `('RAM2LIN', 3m+u, m)` | λ-free leaf |
| `2SIDED(w, u−w)` | `('3LIN', m+(u−w), m+w, m)` | λ-free leaf |
| `SPLITEQ(k′)` | `('VERT2', 3m+2k′, m, λ=(1,1))` | **λ = (1,1)** |
| `INERTDEEP(k′)` | `('VERT2', 3m+2k′, m, λ=(2))` | **λ = (2)** |
| `SPLIT-TAIL` / `UNDECIDED` | `('DRAIN',)` | — |

**DERIVATION.** LEMMA HM3-3 (`.23`) and LEMMA HM3-1(iii) (`.21`): “the post-β frames classify through the dictionary because the raw hull is the sheared block hull plus the persistent split side, with residuals unit-scaled”.

**Arithmetic audit of the shear arithmetic.** Every image's `u₀`-slot is the raw valuation of `B₀`, which by HM3-1(iii)'s valuation identity is `3m + v(A₀-block)`: for a block refine at depth `k′` the block's `A₀` sits at `2k′`, giving `3m + 2k′` ✓; for `RAM(u)`, `A₀` sits at `u`, giving `3m + u` ✓. For `2SIDED(w, u−w)` the three raw root valuations are `m`, `m+w`, `m+(u−w)` ✓ — consistent with a `3LIN` leaf whose three slots are those valuations. **The dictionary is arithmetically consistent with HM3-1(iii) at every row** ✓.

**CONDITIONALITY.** Two dictionary rows fix λ (`SPLITEQ ↦ λ=(1,1)`, `INERTDEEP ↦ λ=(2)`) — so the β side was **already** fixed-λ before ANNEX B. **ANNEX B's refinement therefore bites only on tiers I and II**, which is exactly what its family arithmetic says (11 + 11 from the fixed-λ split; B's 24 comes from the `b(m)` regime split, not from λ). Recorded because it is the fact that makes ANNEX B's asymmetry (`7 → 11` twice, `12 → 24`) intelligible.

**XREF.** `W12_PROOF_2026-08-08.md` — `LEMMA W12-L0`, count 5. `W11_PROOF_2026-08-08.md` — `SPLIT-TAIL`, count 21.

---

### EFF.HMENU3.10  [definition]

**CANONICAL STATEMENT** (verbatim, S1 L140–143). FORM: inline sentences closing the theorem.

> “Every decided leaf's σ is the terminal frame's Ore read (the leaf
> table of W-12 S2.4; for β-composites σ = σ_block ⊎ {(1,1)}, which
> the dictionary realizes as the leaf's own shape σ). Summing the
> DRAIN keys re-derives THEOREM HEX3.A term by term.”

**DERIVATION.** The σ half is proved at `.23`'s closing paragraph (“σ: the terminal frame's Ore read gives σ_block ⊎ {(1,1)}, which the dictionary leaf's own shape σ equals”), with the three cases spelled out. The drain half is proved at `.24` and machine-checked by HM3-DRAIN.

**CONDITIONALITY.** **This is the clause ANNEX A's quantifier repair is really about.** “the terminal frame's Ore read” imports W-12 §S2.3, whose pre-r4 phrasing over-claimed. Post-ANNEX-A the reading is: the leaf table assigns σ to **every disc ≠ 0 lift** of the member. See `.14`, `.28`, `.63`.

**XREF.** `W12_PROOF_2026-08-08.md` — `S2.4`, count 10; `S2.3`, count 35. `HEX3_PROOF_2026-08-08.md` — `THEOREM HEX3.A`, count 11.

---

### EFF.HMENU3.11  [theorem]

**CANONICAL STATEMENT** (verbatim, S1 L145–171 — THEOREM HM3.B's family list). FORM: display (blockquoted theorem with bulleted tiers).

> “**THEOREM HM3.B (the finite aggregate (A1) menu).** Aggregating over
> α-prefix histories with LEMMA HM3-4's bracket b(0) = 1, b(m) =
> (q−1)q^{4m−1} (m ≥ 1), and over n = 2 interior histories with the
> W-11 bracket q^{s−1}, the decided TRP mass at window N is EXACTLY
> the disjoint union of the finite family list (per center; whole
> space = ×q):
>
> * **I (7 families):** the depth-0 W-12.A laws (m = 0).
> * **II (7 families, m ≥ 1):** DEEP-X(m; params) =
>   (q−1)q^{4m−1} × [X's law at window N−3m] — e.g. DEEP-RAM3(m, h) =
>   (q−1)²·q^{3N−5m−2h−3}.
> * **B1/B2/B3 (12 families, m ≥ 0 with the b(m) bracket):**
>   B1-L(m,k; x) = b(m)(q−1)(q−2)·q^{3k+M−1}·A_L(M; x);
>   B2-L(m,k,w; x) = b(m)(q−1)²·q^{3k+M−1−w}·A_L(M; x);
>   B3-L(m,t,j; x) = b(m)(q−1)·q^{3t+M−1}·A_L^{(j)}(M; x);
>   M = N−3m−3k (resp. −3t), L ∈ {RAM, 2SIDED, SPLITEQ, INERTDEEP},”

**DERIVATION.** §S4's proof (`.26`): fix an aggregate family key; its raw-key fiber is an α-prefix history (LEMMA HM3-4's bracket) followed by the family datum; tier I/II take the depth-0 law at window `N−3m`; B-families take the route prefactor times the block aggregate.

**SUPERSEDED (the family counts only).** **ANNEX B** (`.67`) replaces every count in the bullet headings: “I (7 families)” → 7 shape schemas / **11** formal families; “II (7 families…)” → **11**; “B1/B2/B3 (12 families…)” → 12 fixed-σ schemas / **24** formal families. **SUPERSESSION KIND:** `counter re-reading` (the objects are unchanged; what the number counts is corrected). **CHAIN:** frozen headings → ANNEX B. **TERMINAL: ANNEX B.** **TARGETS (rule 24):** `.37` (HM3-BOX-5) and `.62` (the acceptance record's “33-family”) carry the same correction.

**Arithmetic audit.** The DEEP-RAM3 example: `(q−1)q^{4m−1} × [RAM3's law at window N−3m]`. For the product to equal `(q−1)²q^{3N−5m−2h−3}`, RAM3's window-`W` law must be `(q−1)q^{3W−2h−2}` with `W = N−3m`: then `(q−1)q^{4m−1}·(q−1)q^{3(N−3m)−2h−2} = (q−1)²q^{4m−1+3N−9m−2h−2} = (q−1)²q^{3N−5m−2h−3}` ✓ **exact**. The internal consistency of the tier-II template is therefore confirmed, and the implied depth-0 RAM3 law `(q−1)q^{3N−2h−2}` is recorded as the value tier I must carry.

**CONDITIONALITY.** Conditional on LEMMA HM3-4 (`.25`), the W-11 interior bracket `q^{s−1}`, and W-12.A's depth-0 laws at pin. **Unaffected in substance by ANNEX B** — “fixing λ does not change any exponent, range, visibility threshold, α-prefix bracket, β transport or block aggregation” (`.70`).

**XREF.** `W12_PROOF_2026-08-08.md` — `THEOREM W-12.A`, count 8. `W11_PROOF_2026-08-08.md` — `THEOREM W-11`, count 3.

---

### EFF.HMENU3.12  [table]

**CANONICAL STATEMENT** (verbatim, S1 L162–171 — the block aggregate laws and the β3 entry laws). FORM: display (two indented law blocks).

> “   with the aggregated block laws (per center, window M)
>
>       A_RAM(u) = (q−1)q^{2M−u−2}      A_2SIDED(w₁,w₂) = (q−1)²q^{2M−u−3}
>       A_SPLITEQ(k′) = ((q−1)(q−2)/2)q^{2M−2k′−3}
>       A_INERTDEEP(k′) = (q(q−1)/2)q^{2M−2k′−3}
>
>   and the j-entry laws A^{(j)} (β3; bracket q^{·−j}, ranges shifted
>   by j): A^{(j)}_RAM(u) = (q−1)²q^{2M−u−2−j} (u ≥ 2j+1),
>   A^{(j)}_2SIDED = (q−1)³q^{2M−3−u−j} (w₁ ≥ j+1),
>   A^{(j)}_SPLITEQ = ((q−1)²(q−2)/2)q^{2M−2k′−3−j},
>   A^{(j)}_INERTDEEP = (q(q−1)²/2)q^{2M−2k′−3−j} (k′ ≥ j+1).”

`[TABLE]` (compiler transcription, alongside the source display)

| block leaf `L` | `A_L(M; x)` | `A^{(j)}_L(M; x)` | range shift |
|---|---|---|---|
| RAM(u) | `(q−1)q^{2M−u−2}` | `(q−1)²q^{2M−u−2−j}` | `u ≥ 2j+1` |
| 2SIDED(w₁,w₂) | `(q−1)²q^{2M−u−3}` | `(q−1)³q^{2M−3−u−j}` | `w₁ ≥ j+1` |
| SPLITEQ(k′) | `((q−1)(q−2)/2)q^{2M−2k′−3}` | `((q−1)²(q−2)/2)q^{2M−2k′−3−j}` | — |
| INERTDEEP(k′) | `(q(q−1)/2)q^{2M−2k′−3}` | `(q(q−1)²/2)q^{2M−2k′−3−j}` | `k′ ≥ j+1` |

**DERIVATION.** §S4 (`.26`): “Σ over interior block histories of W12-L0's (q−1)^t-weighted leaf laws = the W-11 bracket q^{s_max} (binomially: Σ_t C(s_max, t)(q−1)^t with s_max = (u−1)/2, w₁−1, k′−1 resp.), which evaluates to the displayed A_L; for β3 the histories are constrained to start at j, giving the (q−1)q^{−j}-shifted A^{(j)}_L (bracket q^{s_max−j}, one (q−1) consumed by the entry letter).”

**Mandatory arithmetic audit (rule 22).** The `A^{(j)}` column must be the `A` column times `(q−1)q^{−j}` — the note's own stated relation. Row by row: RAM `(q−1)q^{2M−u−2}·(q−1)q^{−j} = (q−1)²q^{2M−u−2−j}` ✓; 2SIDED `(q−1)²q^{2M−u−3}·(q−1)q^{−j} = (q−1)³q^{2M−3−u−j}` ✓; SPLITEQ `((q−1)(q−2)/2)q^{2M−2k′−3}·(q−1)q^{−j} = ((q−1)²(q−2)/2)q^{2M−2k′−3−j}` ✓; INERTDEEP `(q(q−1)/2)q^{2M−2k′−3}·(q−1)q^{−j} = (q(q−1)²/2)q^{2M−2k′−3−j}` ✓. **All four rows satisfy the stated relation exactly.** The binomial identity `Σ_t C(s,t)(q−1)^t = q^s` ✓ is the standard one and is what turns the history sum into the bracket. **Density check (independent).** `.31` states `Σ A_L/q^{2M}` = RAM `1/(q(q+1))` + 2SIDED `1/(q³(q+1))` + SPLITEQ `(q−2)/(2q³(q+1))` + INERTDEEP `1/(2q²(q+1))` = `q^{−2}` exactly. Recomputed over the common denominator `2q³(q+1)`: numerators `2q²`, `2`, `q−2`, `q`, summing to `2q² + 2 + (q−2) + q = 2q² + 2q = 2q(q+1)`, so the total is `2q(q+1)/(2q³(q+1)) = 1/q²` ✓ — **exact**, and confirmed in exact rational arithmetic at every `q = 2..39`. The four block densities are therefore density-exhaustive for the `n = 2` menu, as `.31` claims.

**CONDITIONALITY.** Conditional on **LEMMA W12-L0 at pin** and the W-11 interior bracket.

**XREF.** `W12_PROOF_2026-08-08.md` — `LEMMA W12-L0`, count 5; `W12-L0`, count 32. `W11_PROOF_2026-08-08.md` — `THEOREM W-11`, count 3.

---

### EFF.HMENU3.13  [scope-record]

**CANONICAL STATEMENT** (verbatim, S1 L173–209 — the (A1)-admissibility clause with both repair brackets in place). FORM: bold-headed paragraph with two nested bracketed riders.

> “Every family is (A1)-ADMISSIBLE: parameter set a shifted product of
> arithmetic progressions (u odd = 1+2ℤ_{≥0}; h with 3∤h = the union
> (1+3ℤ)∪(2+3ℤ); all others full shifted lattices), exponent ℓ affine
> with strictly positive coefficients, integer in AP-INDEX coordinates
> (m carries 5, k/t carry ≥ 3, w/j/k′ carry ≥ 1; the odd RAM-type
> parameters u/u₁ carry 3/2 in RAW coordinates **in the tier-I/II
> RAM2LIN/LINRAM2 families and THEOREM HM3.A's history-resolved
> INSTANCE laws ONLY [r2 m1, PE2 FINDING 1: the B1/B2/B3-RAM
> AGGREGATE families of THIS theorem carry u with integer coefficient
> exactly 1 — the interior W-11 bracket q^{(u−1)/2} cancels the half,
> A_RAM(u) = (q−1)q^{2M−u−2} as displayed above, so e.g.
> ℓ(B2-RAM(0,k,w;u)) = 6k+w+u+3 — pinned by the committed
> B2-RAM(0,1,1;u=3) @ (Zp,2,9) = 16,384 = 2^{27−13} (a (3u+1)/2
> aggregate reading would give 2^{27−16} = 2,048; the two HM3.A
> instance keys 8,192 + 8,192 carry the halves at instance
> ℓ = 6k+w+(3u+1)/2+2 = 14 each, their SUM does not). The sealed
> "u carry ≥ 1" was thus TRUE for the B-RAM aggregates; the [r1]
> bracket below inherited PE1 FINDING 2's over-broad example]** —
> there the two consulted
> windows contribute u + (u+1)/2, e.g. LINRAM2's ℓ term
> u₁ + (u₁+1)/2 = (3u₁+1)/2 — which becomes integer carry 3 at the AP
> index u = 2i−1) [r1, PE1 FINDING 2: the sealed "integer
> coefficients (… w/j/u/k′ carry ≥ 1)" is false in the ~~raw odd
> parameters~~ **tier-I/II raw odd parameters [r2 m1: scope]**
> (carry 3/2, a half-integer); what (A1) demands is only
> strict positivity (W-12.D §S1(iii)), and what the geometric-series
> display consumes is only m_i·b_i ∈ ℤ_{>0} (W-12.D Step 1's
> [r1 m1]/[r2 G3] guard), which holds at every family here —
> (3/2)·2 = 3 on the step-2 progressions, and a fortiori 1·2 = 2 at
> the B-RAM aggregates [r2 m1] — so admissibility and every
> series stand, PE1 having independently re-summed all of them],
> visibility ν affine (= the deepest pinned
> height + 1 = the loop bound), one c_F(q) per family (b's two
> regimes split each B-family into its m = 0 and m ≥ 1 variants —
> a finite relabeling), all data single q-polynomial expressions,
> characteristic-free. Disjointness: aggregation collects disjoint
> raw-key fibers of the deterministic read.”

**DERIVATION.** [ASSEMBLED from `.04`'s contract + the family list `.11`], with the two repair brackets carrying the corrective argument. The disjointness leg is one clause and rests on `.07`'s determinism.

**CHAIN (rule 25 — three layers).** sealed “integer coefficients (… w/j/u/k′ carry ≥ 1)” → **`[r1]` PE1-F2** (false in the raw odd parameters; what (A1) demands is strict positivity, and the geometric-series guard is `m_i·b_i ∈ ℤ_{>0}`) → **`[r2]` m1** (the `[r1]` example was over-broad: the B-RAM *aggregates* do carry integer coefficient exactly 1, because the interior W-11 bracket `q^{(u−1)/2}` cancels the half; the half survives only in the tier-I/II RAM2LIN/LINRAM2 families and HM3.A's *instance* laws). **TERMINAL: `[r2]` m1.** **SUPERSESSION KINDS, in order:** `replacement` (r1: a false integrality claim replaced by the correct positivity requirement), then `scope-pin` (r2: the counter-example's scope narrowed). Two kinds, not one.

**Mandatory arithmetic audit (rule 22) — the `[r2]` pin, recomputed.** `ℓ(B2-RAM(0,k,w;u)) = 6k+w+u+3`; at `k = 1, w = 1, u = 3` this is `6+1+3+3 = 13`, and at `(Zp, q=2, N=9)`, `3N = 27`, so the count is `2^{27−13} = 2^{14} = 16,384` ✓ — **the pinned committed value reproduces exactly.** The instance reading: `ℓ = 6k+w+(3u+1)/2+2 = 6+1+5+2 = 14`, giving `2^{27−14} = 2^{13} = 8,192` per instance key, and **two such keys sum to 16,384** ✓ — the note's “8,192 + 8,192” is exact. The AP-index integrality: `(3/2)·2 = 3` ✓ and `1·2 = 2` ✓. **One figure does NOT reproduce:** the counterfactual “a (3u+1)/2 aggregate reading would give `2^{27−16} = 2,048`”. Substituting `(3u+1)/2 = 5` for `u` in the aggregate exponent gives `6+1+5+3 = 15`, i.e. `2^{12} = 4,096`, not `2^{11} = 2,048`; no combination of the displayed formulas yields `ℓ = 16`. **See finding AF-1 in §7.1.** The load-bearing figures (16,384; `ℓ = 13`; the two 8,192 instance keys) all verify; only the counterfactual does not, and nothing consumes it.

**CONDITIONALITY.** Admissibility is conditional on W-12.D §S1(iii) as pinned, and specifically on the `m_i·b_i ∈ ℤ_{>0}` guard of W-12.D Step 1. **Confirmed unaffected by ANNEX B** (`.70`: “fixing λ does not change any exponent, range, visibility threshold”).

**XREF.** `W12_PROOF_2026-08-08.md` — `THEOREM W-12.D`, count 5; `S1` (section anchor at L57).

---

### EFF.HMENU3.14  [theorem]

**CANONICAL STATEMENT — the frozen text, and its governing corrected reading. This is the unit the queue charge names.**

**Frozen form** (verbatim, S1 L211–220). FORM: display (blockquoted theorem).

> “**THEOREM HM3.C ((hMenu-3) DISCHARGED; (A0)+(A2) at n = 3).** The
> complete n = 3 core menu = {SEP3, SEPLQ, SEPC} (3 level-0 separable
> point families, W-12 S2.1/S2.3) ∪ {DBL-RAM, DBL-2SIDED, DBL-SPLITEQ,
> DBL-INERTDEEP} (counts q(q−1)·q^{N−1}·A_L(N); LEMMA W12-L1 +
> W12-L0, w12-machine-sealed) ∪ the THEOREM HM3.B TRP families. This
> list satisfies (A1) in full. (A0): every menu member is
> conservative-DECIDED — all consulted data in-window with separable
> residuals — **so Ore certifies EVERY lift** (W-12 S2.3 at the terminal
> frame; W12-L1(c) transports the DBL certificates); σ_F = the leaf
> table. (A2): the complement is EXACT (S5.3):”

**GOVERNING EFFECTIVE FORM (template rule 10 — the frozen L216–219 sentence read through the LANDED append chain).**

ANNEX A, site 1 (L879–884), supplies the replacement reading verbatim:

> “1. **§S1, THEOREM HM3.C, the (A0) clause (L216–219).** As frozen: "(A0):
>    every menu member is conservative-DECIDED — all consulted data
>    in-window with separable residuals — **so Ore certifies EVERY lift**
>    (W-12 S2.3 at the terminal frame; W12-L1(c) transports the DBL
>    certificates); σ_F = the leaf table." **Read as:** "… so Ore
>    certifies every lift **with disc ≠ 0** …".”

and ANNEX A's own statement of the corrected clause in full (L902–905):

> “Corrected (A0) at n = 3: *every window member of every core-menu family
> is conservative-DECIDED, and every disc ≠ 0 lift of that member has
> σ = the leaf table's entry.*”

**Therefore the effective THEOREM HM3.C is the frozen display above with the six words “so Ore certifies EVERY lift” read as “so Ore certifies every lift with disc ≠ 0”, and with the full corrected (A0) as just quoted.** Everything else in the display — the menu list, “This list satisfies (A1) in full”, `σ_F` = the leaf table, and the (A2) hand-off — is unchanged.

**ANNEX PROVENANCE (queue charge).** The correction's chain of custody, quoted from ANNEX A's opening (L866–875):

> “**Raised by W-12's hostile arc.** W-12's r4 repair (**d2d91b7**) struck
> the same unrestricted quantifier from W-12 §S2.3 as FALSE in equal
> characteristic at wild decided shapes; W-12's PE5 pass (**c3e2f8e**,
> FINDING 1) then observed that W-12's own [r4] FIRING CHECK was vouching
> for THIS note's phrasing of it, and W-12's r5 repair re-worded that row
> and recorded the blast-radius sweep that reached here. The defect
> entered through the S2.3-era phrasing the two notes SHARED — HM3.C's
> own cited warrant for the sentence is "W-12 S2.3 at the terminal
> frame", i.e. the pre-r4 S2.3 text — so it is inherited, not
> independently generated.”

**Provenance verified at the supplier (rule 10 + rule 23).** `git cat-file -t d2d91b7` = `commit` ✓; `git cat-file -t c3e2f8e` = `commit` ✓; `grep -cF 'd2d91b7' W12_PROOF_2026-08-08.md` = **1** ✓; `grep -cF 'NOTICE ON ANNEX 2' W12_PROOF_2026-08-08.md` = **1**, located at L1722 ✓; `grep -cF 'FIRING CHECK' W12_PROOF_2026-08-08.md` = **6** ✓. The notice's own text quotes HMENU3 **“L216–219”** by line — the same line range ANNEX A names — and reproduces the frozen clause; the two independently-authored citations of the defect site agree exactly. **The provenance is fully corroborated on both sides.**

**CHAIN (rule 25 — three layers).** frozen L216–219 → **ANNEX A** (the reading) → **ANNEX C** (the *description* of what ANNEX A did: a strict weakening, not a no-op). **TERMINAL for the reading: ANNEX A. TERMINAL for the characterization: ANNEX C.** **SUPERSESSION KIND:** `replacement` at layer 2 (a false quantifier replaced by a true one); `counter re-reading` at layer 3 (ANNEX C re-reads ANNEX A's self-description, not the theorem).

**DERIVATION.** §S5.2 (`.28`) is the proof of (A0); §S5.3 (`.29`) of (A2); §S5.1 (`.27`) of (A1). The counter-instance establishing that the frozen quantifier is false is `.64`.

**CONDITIONALITY — what the corrected form is and is not.** ANNEX A establishes the corrected clause is (i) W12-BOX-7's pinned notion, (ii) exactly what W-12.D's (A1) σ-labeling clause and both Step-4 bounds consume, and (iii) already how §S0 states (A0) (`.04`, L75–76). **ANNEX C then fences the honest description:** the correction is a *strict weakening* of the frozen statement, not a clarification. Both must travel together; carrying ANNEX A without ANNEX C reproduces exactly the error ANNEX C was written to fix.

**XREF.** `W12_PROOF_2026-08-08.md` — `S2.1`, count 23; `S2.3`, count 35; `LEMMA W12-L1`, count 7; `W12-L1(c)`, count 6; `LEMMA W12-L0`, count 5; `W12-BOX-7`, count 10; `NOTICE ON ANNEX 2`, count 1; `d2d91b7`, count 1.

---

### EFF.HMENU3.15  [lemma]

**CANONICAL STATEMENT** (verbatim, S1 L220–224 — the (A2) exact complement display). FORM: display (indented equation block inside the theorem).

> “    r(N) = q(q−1)q^{N−1}·[⌊(N−1)/2⌋(q−1)q^{N−2} + q^{N−1}]  [DBL tail+undec]
>            + q·u(q,N)                                        [TRP, HEX3.A]
>          ≤ (N+2)·q^{2N} ,   r(N)/q^{3N} → 0.”

**DERIVATION** — §S5.3 (`.29`), verbatim there.

**Mandatory arithmetic audit (rule 22) — the bound re-derived and then re-tested numerically.** The DBL term is `q(q−1)q^{N−1}·[⌊(N−1)/2⌋(q−1)q^{N−2} + q^{N−1}]`; its second summand is `(q−1)q^{2N−1} ≤ q^{2N}` ✓, and its first is `⌊(N−1)/2⌋(q−1)²q^{2N−2} ≤ ((N−1)/2)q^{2N}` ✓ (using `(q−1)² ≤ q²`). The TRP term is `q·u(q,N) ≤ q·N·q^{2N−2} = N·q^{2N−1} = (N/q)q^{2N} ≤ (N/2)q^{2N}` ✓ by THEOREM HEX3.B and `q ≥ 2`. Summing: `r(N) ≤ (1 + (N−1)/2 + N/2)q^{2N} = (N + ½)q^{2N} ≤ (N+2)q^{2N}` ✓ — **the printed bound follows from the displayed ingredients with room to spare, no extra step needed.** Independent numerical confirmation: `r(N) ≤ (N+2)q^{2N}` was evaluated in exact integer arithmetic for `q ∈ {2,3,4,5,7,8,9,11,13,27}` and `N = 2..59` — **holds everywhere, worst ratio 0.4578** (at `q = 27, N = 59`). The asymptotic `r(N)/q^{3N} → 0` is immediate ✓.

**CONDITIONALITY.** The TRP term is **THEOREM HEX3.A consumed at pin** — i.e. the exact conservative-residue law, not a bound. This is the sense in which `.29` calls the result “a sharpening of the (hExhaust-3) discharge”. It does **not** consume HEX3-BOX-1 (`.30`).

**XREF.** `HEX3_PROOF_2026-08-08.md` — `THEOREM HEX3.A`, count 11. `W11_PROOF_2026-08-08.md` — `SPLIT-TAIL`, count 21.

---

### EFF.HMENU3.16  [record]

**CANONICAL STATEMENT** (verbatim, S1 L226–229). FORM: bold-headed paragraph inside the theorem blockquote.

> “**GRADE: HM3.A/B/C composed at attempt 0/2, machine-sealed on 41
> rows both characteristics with the σ-leg PARI-oracled on every
> deep-decided member of four rows. The exact σ-side residue law
> stays open at HEX3-BOX-1 (not needed here — S5.4).**”

**DERIVATION.** [RECORD].

**CONDITIONALITY.** `STALE-SELF-DESCRIPTION` (rule 26) on the grade half — the counter is **2/2 ACCEPTED** (`.60`) and the ledger row is **CERTIFIED** (`.72`); no append edits this sentence. The second half — HEX3-BOX-1 open and not needed here — is **current and correct**, and is the note's cleanest one-sentence statement of its relation to ledger row HYP.137.

**XREF.** `HEX3_PROOF_2026-08-08.md` — `HEX3-BOX-1`, count 11. `spec/HYPOTHESIS_LEDGER.md` — `HYP.137`, count 11.

---

### EFF.HMENU3.17  [corollary]

**CANONICAL STATEMENT** (verbatim, S1 L231–256 — COROLLARY HM3.D with the five densities). FORM: display (blockquoted corollary with an indented density table).

> “**COROLLARY HM3.D (THE UNIFORM CUBIC DENSITIES; W-12.D fires at
> n = 3).** Assuming exactly the displayed conditionality stack (S9:
> W-12.D as proved @ its 0/2 arc — post-r2 99f1813 as of this repair
> [r2 m2: re-verified against git at r2 — no W12 PE3 has run],
> PE3 next [r1, PE1 FINDING 1: the sealed "0/2-post-r1 arc" was stale
> at seal time — W12 PE2 (NOT CLEAN 0C+3G+2m, 1be15d2) had landed 26
> minutes before the seal 64d3ff9; see S9 bullet 1 for the
> fired-clause check]; W-11 @ its accepted pins **[r2 m2: since
> ACCEPTED at 2/2 — PE3 CLEAN 839b735 + PE4 CLEAN 16d12e1, fold
> 35e6545]**;
> W-12.A/C + W12-L0/L1 @ the w12 seal; HEX3 @ 0/2 **post-r1 2580f12,
> PE2 next; fired-clause record at HM3-BOX-2 [r2 m2]**; this note
> @ 0/2),
> for every prime power q and BOTH characteristics, wild primes
> included, the cubic splitting densities are (Φ := q⁴+q³+q²+q+1):
>
>     R_{(1,1)³}        = q³(q²−q+1) / (6(q+1)Φ)      [split]
>     R_{(1,2),(1,1)}   = q³(q²+q+1) / (2(q+1)Φ)      [quadratic inert × linear]
>     R_{(1,3)}         = q³(q+1) / (3Φ)              [cubic inert]
>     R_{(2,1),(1,1)}   = q(q³+q+1) / ((q+1)Φ)        [partially ramified;
>                                                      wild at p = 2]
>     R_{(3,1)}         = (q²+1) / Φ                  [totally ramified;
>                                                      wild at p = 3]
>
>     Σ_τ R_τ = 1  (exactly);  each R_τ = μ_τ, the Haar splitting
>     density, and = the N → ∞ decided window mass (W-12.D Steps 2–4).”

`[TABLE]` (compiler transcription of the density block, alongside the source display; `Φ = q⁴+q³+q²+q+1`)

| splitting type τ | `R_τ(q)` | note |
|---|---|---|
| `(1,1)³` | `q³(q²−q+1) / (6(q+1)Φ)` | split |
| `(1,2),(1,1)` | `q³(q²+q+1) / (2(q+1)Φ)` | quadratic inert × linear |
| `(1,3)` | `q³(q+1) / (3Φ)` | cubic inert |
| `(2,1),(1,1)` | `q(q³+q+1) / ((q+1)Φ)` | partially ramified; **wild at p = 2** |
| `(3,1)` | `(q²+1) / Φ` | totally ramified; **wild at p = 3** |
| **Σ** | **1 exactly** | — |

**DERIVATION.** §S5.5 (`.31`): W-12.D's Steps 1–4 applied to the §S5.1 menu, with the per-centre block densities, the TRP amplifier, and the whole-space assembly.

**Mandatory arithmetic audit (rule 22) — the five formulas verified exactly.** Evaluated in exact rational arithmetic at every prime power `q = 2..39`: **`Σ_τ R_τ = 1` at all 38 values, zero failures** ✓ (which, the five expressions being rational functions with denominator dividing `6(q+1)Φ` of degree 6 and numerators of degree ≤ 6, certifies the identity as a rational-function identity). `E[#roots] = 3R_split + R_{(1,2),(1,1)} + R_{(2,1),(1,1)} = q/(q+1)` **at all 38 values** ✓. The printed anchors reproduce exactly: `q = 2` → `(4/93, 28/93, 8/31, 22/93, 5/31)` ✓; `q = 3` → `(63/968, 351/968, 36/121, 93/484, 10/121)` ✓. The §S5.5 sum decomposition `(q−1)/q + (q−1)/q² + 1/q² = (q² − q + q − 1 + 1)/q² = 1` ✓.

**CHAIN — the three supplier-arc displays inside this corollary.** (a) W-12: sealed “0/2-post-r1 arc” → `[r1]` PE1-F1 (stale at seal: PE2 landed 26 min before) → `[r2]` m2 (re-verified, no W12 PE3). (b) W-11: sealed “@ its accepted pins” → `[r2]` m2 (ACCEPTED 2/2). (c) HEX3: sealed → `[r2]` m2 (“@ 0/2 post-r1 2580f12, PE2 next”). **TERMINALS: `[r2]` m2 in all three cases — but (c) is itself now stale at HEAD:** HEX3 is ACCEPTED 2/2 and ledger-CERTIFIED (`spec/EFF-HEX3.md` `.64`, `.71`). Flagged at §5.2; nothing applied, since no HMENU3 append reaches it.

**CONDITIONALITY.** The corollary's grade is explicitly the minimum over the stack (`.56`). Every conditionality is a **supplier arc grade**, not an open lemma: the corollary has no hypothesis of its own beyond the S9 stack.

**XREF.** `W12_PROOF_2026-08-08.md` — `THEOREM W-12.D`, count 5; `THEOREM W-12.A`, count 8. **PIN VERIFICATION:** `99f1813`, `1be15d2`, `64d3ff9`, `839b735`, `16d12e1`, `35e6545`, `2580f12` — **all seven resolve to `commit`** ✓.

---

### EFF.HMENU3.18  [record]

**CANONICAL STATEMENT** (verbatim, S1 L258–267). FORM: bold-headed paragraph.

> “Numerical anchors: q = 2: (4/93, 28/93, 8/31, 22/93, 5/31);
> q = 3: (63/968, 351/968, 36/121, 93/484, 10/121). Independent tie:
> the five forms equal the MONIC level-0 assembly of the repo's
> symbolic OM-density engine's cluster laws β(2)/β(3)
> (`verification/om_density_engine.py`, md5-pinned) — the same β's
> whose projective assembly is reconciled exactly against the BCFG
> literature distribution through n = 5/6 (`reconcile_om_bcfg.py`,
> committed) — and E[#roots] = R_split·3 + R_{(1,2),(1,1)} +
> R_{(2,1),(1,1)} = q/(q+1). EXPLORATORY observation (no proof
> claimed): the three unramified densities satisfy R_τ = q³·β₃(τ).”

**DERIVATION.** [RECORD] — an anchor list plus two independent ties plus one fenced observation.

**Arithmetic audit.** Both anchor tuples and `E[#roots] = q/(q+1)` reproduce exactly (see `.17`). The `R_τ = q³·β₃(τ)` observation is consistent with `.31`'s “q³·T_τ = β₃(τ), the engine's triple cluster law, term for term” **for the TRP contribution**, but `R_τ` is the whole-space density `SEP_τ + (q−1)c²_{τ″} + q·T_τ`, so `R_τ = q³β₃(τ)` cannot hold for all three unramified types on the same footing as `q³T_τ = β₃(τ)` unless the SEP and DBL contributions conspire. **The note fences it as EXPLORATORY with no proof claimed** — recorded, not audited further, and a consumer must not promote it.

**CONDITIONALITY.** The engine tie is a **cross-check, not a supply** (N-3): “No count law consumes them.”

**XREF.** artifacts `verification/om_density_engine.py` — EXISTS ✓; `verification/reconcile_om_bcfg.py` — EXISTS ✓.

---

### EFF.HMENU3.19  [lemma]

**CANONICAL STATEMENT** (verbatim, S2 L271–278 — LEMMA HM3-1(i)). FORM: bracketed-headed clause.

> “Along any conservative chain from a depth-0 TRP frame:
>
> (i) [depth-0 frames] Every pre-β frame is a (sheared) depth-0 TRP
> frame, and HEX3's LEMMA H-1 partition applies verbatim: it is B₀ = 0
> (DRAIN), one of the SEVEN decided shapes (leaf), or one of the FOUR
> refine species α/β1/β2/β3 — nothing else (W-12 S2.4 depth-0
> completeness, consumed at pin; at n = 3 every e ≥ 2 side has g = 1,
> so no other repeat genre exists — the W-12 [r1 F3] taxonomy point).”

**DERIVATION.** [IMPORTED] — HEX3's LEMMA H-1 applied verbatim, with W-12 §S2.4's completeness as the warrant and the `g = 1` observation closing the “could another repeat genre exist?” objection.

**CONDITIONALITY.** Conditional on **W-12 §S2.4 at pin** and on **HEX3's LEMMA H-1** — which, per `spec/EFF-HEX3.md` `.67` (HEX3's Correction C), is machine-exercised only at depth-0 keys realized on HEX3's `N ≤ 9` roster. **HMENU3's own roster also caps at `N = 9`**, so the same depth scope applies here; the all-depth reach rests on the uniform slot-count proofs, not on either machine leg. Flagged; no HMENU3 append records it.

**XREF.** `HEX3_PROOF_2026-08-08.md` — `LEMMA H-1`, count 3. `W12_PROOF_2026-08-08.md` — `S2.4`, count 10.

---

### EFF.HMENU3.20  [lemma]

**CANONICAL STATEMENT** (verbatim, S2 L280–282 — LEMMA HM3-1(ii)). FORM: bracketed-headed clause.

> “(ii) [α preserves the phase] After ('ALPHA', d) the state lies in the
> post-α node D_k, which is a fresh (sheared) depth-0 TRP frame (HEX3
> H-2(iii): the α-map is a bijection of the z-slice onto D_k).”

**DERIVATION.** [IMPORTED] from HEX3's H-2(iii).

**CONDITIONALITY.** Conditional on HEX3 H-2(iii) at pin.

**XREF.** `HEX3_PROOF_2026-08-08.md` — `H-2`, count 11; `LEMMA H-2`, count 1. **NEAR-MISS (rule 15):** the designation `H-2(iii)` as written has fixed-string count **0** in `HEX3_PROOF_2026-08-08.md`, because HEX3 writes its clause head as “(iii) **[the α-map is onto]**” without repeating the lemma name. Referent verified at `HEX3_PROOF_2026-08-08.md:287–297` (compiled as `spec/EFF-HEX3.md` `.18`), where the clause proves exactly “recentering by ẑπ^k maps the (α) z-slice into D_k … a bijection”. Carried as NEAR-MISS, not an OPEN-CALL.

---

### EFF.HMENU3.21  [lemma]

**CANONICAL STATEMENT** (verbatim, S2 L284–296 — LEMMA HM3-1(iii), the phase-flip clause; this is the note's own new structural lemma). FORM: bracketed-headed clause.

> “(iii) [β flips the phase, once] After a β-event the polygon
> permanently shows the split side (2, m)–(3, 0) with m = the split
> depth: the split root sits at raw valuation exactly m, both cluster
> roots strictly deeper, and every later recentering is deeper still —
> so v(center − r_split) = m is constant along the rest of the chain
> and the strict minimality of the split slope persists. Hence every
> post-β frame has its vertex at (2, m); its rightmost side has g = 1;
> the only possible repeat genre is the cluster side's (y−z)² — read as
> ('VERT2', ·, m) — and the only decided exits are the dictionary
> leaves of THEOREM HM3.A. In particular no α-event and no β1/β2-event
> can occur after a β-event: every chain is α-steps* [optional β-event
> + block chain] terminal — two phases exactly, W12-BOX-2's two node
> species and nothing else.”

**DERIVATION** (verbatim, L298–313):

> “*Proof of (iii).* Valuations: v(B₀-raw) = Σ root valuations = 3m +
> v(A₀-block) (valuation multiplicativity of the product of the three
> roots); the hull heights at abscissae 0, 1, 2 are block heights
> sheared by (3−j)m... (j the abscissa), i.e. raw hull = [block hull on
> 0..2, sheared] ∪ [split side], because the split root is the unique
> valuation-minimal root (block roots deeper: β1/β2 — cluster at block
> valuation ≥ 1 post-recentering; β3 — cluster below the left-side
> slope t+j > t; deeper recenterings only deepen the cluster, and the
> recentering shifts s all have v(s) > m so the split coordinate's
> valuation is untouched). The rightmost side (2, m)–(3, 0) has length
> 1 (g = 1). The left part is the block polygon sheared, with residual
> coefficients at the sheared positions equal to the block residual
> coefficients up to the unit −ρ̄ (LEMMA W12-L1(b)'s computation at the
> σ_m-scaled pattern: the letters move by a unit, hulls, lattice
> points, separability types and repeated roots do not) — so frame
> classification = block classification through the dictionary. ∎”

**Arithmetic audit of the valuation identity.** `v(B₀-raw) = Σ` root valuations: the three roots are the split root (valuation `m`) and the two cluster roots, whose product has valuation `v(A₀-block) + 2m` after the shear — total `3m + v(A₀-block)` ✓, exactly as displayed and exactly what makes the dictionary's `u₀`-slots `3m + 2k′`, `3m + u` come out right (`.09`). **The lemma and the dictionary are arithmetically interlocked and consistent** ✓.

**CONDITIONALITY.** This is the note's own lemma (graded with the note; ACCEPTED 2/2 at HEAD). It consumes **LEMMA W12-L1(b) at pin** for the unit-scaling of residual coefficients. It is the **exhaustiveness engine** for the whole menu — the acceptance record names it as such (“exhaustiveness via the two-species grammar”, `.62`).

**XREF.** `W12_PROOF_2026-08-08.md` — `W12-L1(b)`, count 2; `LEMMA W12-L1`, count 7; `W12-BOX-2`, count 8.

---

### EFF.HMENU3.22  [lemma]

**CANONICAL STATEMENT** (verbatim, S3.1 L319–323 — LEMMA HM3-2). FORM: bold-headed paragraph.

> “Let D_k, σ_k be HEX3 H-2's post-α node and scaling. Then the raw key
> of X ∈ D_k equals the raw key of σ_k(X) (a window-(N−3k) state) with
> every step/leaf parameter sheared: u₀-type params +3k, slope/depth
> params +k, the LINRAM2 vertex height +2k; and every fiber of σ_k
> (q^{3k} ghost digits) is key-constant.”

**DERIVATION** (verbatim, L325–338):

> “*Proof.* HEX3 H-2(i) (window coherence) shows every digit consulted
> by the chain of X lies strictly below the ghost zones — so the chain,
> not merely its drain verdict, is a function of σ_k(X); H-2(ii) (shear
> correspondence) makes the two chains correspond step for step with
> heights sheared by (j, v) ↦ (j, v−(3−j)k), an affine-in-j map
> preserving lower hulls, lattice points, side subdivisions and
> residual coefficient positions — hence each frame's CLASSIFICATION
> (species or leaf, with parameters) transports by exactly the listed
> shifts, and recentering commutes with σ_k (f(π^k(y+s̃)) =
> π^{3k}f̃(y+s̃)). Both lemmas consumed at HEX3's pin; what is new here
> is only reading the correspondence at KEY resolution, which is what
> HM3-MENU machine-checks per key on every row. With H-2(iii)
> (α-bijection, (q−1) letters): the ('ALPHA', s+k)-prefixed menu =
> (q−1)q^{3k} × the window-(N−3k) menu, key-sheared. ∎”

**Arithmetic audit of the shear amounts.** The height shear is `(j,v) ↦ (j, v−(3−j)k)`, so at abscissa `j = 0` (the `B₀`/`u₀` slot) the shift is `3k` ✓ (“u₀-type params +3k”); at `j = 2` (the `B₂`/depth slot) it is `k` ✓ (“slope/depth params +k”); at `j = 1` (the LINRAM2 vertex) it is `2k` ✓ (“the LINRAM2 vertex height +2k”). **All three listed shifts are exactly the shear evaluated at their own abscissa** — the list is derived, not stipulated ✓.

**CONDITIONALITY.** Conditional on **HEX3 H-2(i)/(ii)/(iii) at pin**. HM3-BOX-2's `[r2]` fired-clause record (`.34`) is precisely about this dependence: HEX3's PE1 gap 1 was H-2(i)'s displayed ghost-zone inequality, and §S3.1 “fires H-2(i) BY NAME”. The record establishes the consumed conclusion survives (HEX3's own PE1 re-derived the corrected pairing `N−jk`, and the display was corrected at HEX3 r1 `2580f12`) — **independently confirmed here** at `spec/EFF-HEX3.md` `.16`, where the corrected inequality is re-derived and holds on the whole range.

**XREF.** `HEX3_PROOF_2026-08-08.md` — `H-2(i)`, count 4; `H-2`, count 11; `LEMMA H-2`, count 1. `H-2(ii)`/`H-2(iii)`: NEAR-MISS as at `.20`.

---

### EFF.HMENU3.23  [lemma]

**CANONICAL STATEMENT** (verbatim, S3.2 L342–367 — LEMMA HM3-3, statement, fibration display and proof, one span). FORM: bold-headed paragraph with an indented three-route display.

> “For each β-route, with m the split depth and M the block window
> (β1/β2: m = s+k, M = N_frame−3k; β3: m = s+t, M = N_frame−3t):
> the post-β chain is the W-11/W12-L0 block chain of the transported
> block state, its raw record is the DICTIONARY image of the block's
> (hist, leaf), and the state-count fibration over the block system is
>
>     β1: (q−1)_{z,z′ pairs: ×(q−2)} · q^{3k} ghost · q^{M−1} split fiber
>     β2: (q−1)_z · q^{3k} ghost · (q−1)q^{M−1−w} split fiber (w = u₀−3k)
>     β3: (q−1)_λ · q^{3t} ghost · q^{M−1} split fiber, block entering
>         AT ITS OWN REFINE LOCUS of depth j = (u₀−3t)/2 (the β3 event
>         IS the block's first refine; its z-letter is the (q−1) inside
>         L0's (j)⌢hist′ bracket)
>
> — exactly HEX3 H-3's maps and fibers (consumed at pin: onto-ness,
> injectivity, fiber counts), upgraded from drain-mass to full keys by
> LEMMA HM3-1(iii): the post-β frames classify through the dictionary
> because the raw hull is the sheared block hull plus the persistent
> split side, with residuals unit-scaled (W12-L1(b), machine-checked
> pointwise on 2.9M lifts at the w12 seal). Drain consistency: summing
> DRAIN over L0 gives HEX3's R(M) resp. (q−1)q^jR(M−2j) — the HEX3.A
> species table re-derived (machine: HM3-DRAIN + HM3-HEX3TIE). σ: the
> terminal frame's Ore read gives σ_block ⊎ {(1,1)}, which the
> dictionary leaf's own shape σ equals (RAM ↦ RAM2LIN: {(2,1)}⊎{(1,1)};
> 2SIDED ↦ 3LIN: {(1,1)²}⊎{(1,1)}; SPLITEQ/INERTDEEP ↦ VERT2(λ)) —
> machine: HM3-ORACLE (PARI, 9,952 deep members) + HM3-XREAD (σ tie to
> the sealed reader). ∎”

**DERIVATION.** The span is statement and proof together: HEX3 H-3's maps and fibers supply the counting; HM3-1(iii) upgrades drain-mass resolution to key resolution; W12-L1(b) supplies the unit-scaling; the σ paragraph closes the leaf-table identification.

**Mandatory arithmetic audit (rule 22) — the three fibrations cross-checked against HEX3's drained masses.** β1: `(q−1)(q−2)·q^{3k}·q^{M−1}` matches HEX3's `(q−1)(q−2)q^{3k+M−1}` ✓. β2: `(q−1)·q^{3k}·(q−1)q^{M−1−w}` = `(q−1)²q^{3k+M−1−w}` ✓. β3: `(q−1)·q^{3t}·q^{M−1}` = `(q−1)q^{3t+M−1}`, versus HEX3's `(q−1)²q^{3t+M−1+j}` — the difference `(q−1)q^{j}` is exactly what the note says is absorbed into `L0((j)⌢hist′, …)`, and the drain-consistency clause states the same relation from the other side: “summing DRAIN over L0 gives HEX3's R(M) resp. **(q−1)q^jR(M−2j)**” ✓. **The two accountings agree, and the note discloses the bookkeeping seam rather than hiding it** ✓.

**CONDITIONALITY.** Conditional on **HEX3 H-3 at pin** (onto-ness, injectivity, fiber counts — the first two of which are HEX3-BOX-2's attack surfaces (a) and (b), reported as having survived HEX3's PE1), on **W12-L1(b) at pin**, and on **W12-L0** for the block side.

**XREF.** `HEX3_PROOF_2026-08-08.md` — `H-3`, count 5; `THEOREM HEX3.A`, count 11. `W12_PROOF_2026-08-08.md` — `W12-L1(b)`, count 2; `W12-L0`, count 32.

---

### EFF.HMENU3.24  [lemma]

**CANONICAL STATEMENT** (verbatim, S3.3 L371–379). FORM: paragraph proof.

> “Induction on the window. At the top frame, LEMMA HM3-1(i) partitions
> the states; decided shapes carry the W-12.A S2.4 laws (consumed at
> pin — PROVED there for all degrees); the α-slice recurses by LEMMA
> HM3-2 at window N−3k (strictly smaller); the β-slices are counted by
> LEMMA HM3-3 with the block side supplied by W12-L0 (consumed at pin);
> B₀ = 0 drains. Every state receives exactly one raw key
> (deterministic read), so the counts partition q^{3(N−1)}; the DRAIN
> keys sum to u(q, N) by the same telescoping HEX3 S5 proved —
> re-checked per row (HM3-DRAIN). ∎”

**DERIVATION.** The span is the derivation: an induction on the window whose well-foundedness is “window N−3k (strictly smaller)”.

**Arithmetic audit.** The partition identity `Σ(decided keys) + Σ(drain keys) = q^{3(N−1)}` with `Σ(drain) = u(q,N)` was re-verified at two never-measured rows from the closed forms alone: `(Fqt,2,9)` — `2^{24} = 16,777,216`, `u(2,9) = 103,168`, decided `= 16,674,048` ✓ **exactly the note's preregistered decided total**; `(Fqt,27,2)` — `27³ = 19,683`, `u(27,2) = 729`, decided `= 18,954` ✓ **exactly the note's preregistered `('RAM3',1)` value**. Two independent confirmations of the assembly identity at rows the corpus had never measured.

**CONDITIONALITY.** Conditional on `.19`–`.23`, W-12.A §S2.4 and W12-L0 at pin, and HEX3's S5 telescoping (which `spec/EFF-HEX3.md` `.30` verifies independently).

**XREF.** `W12_PROOF_2026-08-08.md` — `THEOREM W-12.A`, count 8; `S2.4`, count 10; `W12-L0`, count 32.

---

### EFF.HMENU3.25  [lemma]

**CANONICAL STATEMENT** (verbatim, S4 L383–385 — LEMMA HM3-4). FORM: display (blockquoted lemma).

> “> **LEMMA HM3-4.** Σ over all finite sequences (k₁, …, k_r), k_i ≥ 1,
> > Σk_i = m, of Π_i (q−1)q^{3k_i} = (q−1)q^{4m−1} for m ≥ 1 (and 1 for
> > m = 0, the empty history).”

**DERIVATION** (verbatim, L387–392):

> “*Proof.* Generating function: one α-step contributes A₁(x) =
> Σ_{k≥1}(q−1)q^{3k}x^k = (q−1)q³x/(1−q³x); chains contribute
> Σ_{r≥1}A₁^r = A₁/(1−A₁) = (q−1)q³x/(1−q³x−(q−1)q³x) =
> (q−1)q³x/(1−q⁴x), whose x^m-coefficient is (q−1)q^{4m−1}. (This is
> the same telescoping denominator HEX3 S5.2 met — the bracket is why
> its k-sum coefficient is q^{4k−1}.) ∎”

**Mandatory arithmetic audit (rule 22) — the bracket verified two independent ways.** (a) **Generating function, re-derived:** `A₁ = (q−1)q³x/(1−q³x)`; `A₁/(1−A₁) = (q−1)q³x/[(1−q³x) − (q−1)q³x] = (q−1)q³x/(1 − q³x − q⁴x + q³x) = (q−1)q³x/(1−q⁴x)` ✓ — the `−q³x` cancels exactly, which is the whole content. Its `x^m` coefficient is `(q−1)q³·q^{4(m−1)} = (q−1)q^{4m−1}` ✓. (b) **Direct composition sum, computed:** `Σ over compositions (k₁..k_r) of m with k_i ≥ 1 of Π(q−1)q^{3k_i}` = `Σ_{r=1}^{m} C(m−1, r−1)(q−1)^r q^{3m}` = `q^{3m}(q−1)Σ_{r=1}^{m}C(m−1,r−1)(q−1)^{r−1}` = `q^{3m}(q−1)q^{m−1}` = `(q−1)q^{4m−1}` ✓. **Both routes agree exactly**, and the second exposes why: the `q^{3Σk_i} = q^{3m}` factor is composition-independent, so only the binomial sum over the number of parts survives. **This is the note's single most load-bearing new lemma — the finiteness of the (A1) menu depends entirely on it — and it is exactly right.**

**CONDITIONALITY.** Unconditional (a generating-function identity). PE3's fresh route independently confirmed it composition-by-composition at never-measured `N = 10` α-slices (`.60`).

**XREF.** `HEX3_PROOF_2026-08-08.md` — the S5.2 telescoping is compiled at `spec/EFF-HEX3.md` `.30`, where the same denominator `(1−q⁴x³)/(1−q³x³)` is verified.

---

### EFF.HMENU3.26  [lemma]

**CANONICAL STATEMENT** (verbatim, S4 L394–407 — the proof of THEOREM HM3.B). FORM: italic-headed paragraph proof.

> “*THEOREM HM3.B, proof.* Fix an aggregate family key. Its raw-key
> fiber is: an α-prefix history (compositions of m — LEMMA HM3-4's
> bracket, the shear leaving the REDUCED-frame data invariant by LEMMA
> HM3-2), then the family datum. For I/II: the depth-0 law at window
> N−3m. For B1/B2/B3-L: the route prefactor (LEMMA HM3-3) times the
> block aggregate: Σ over interior block histories of W12-L0's
> (q−1)^t-weighted leaf laws = the W-11 bracket q^{s_max} (binomially:
> Σ_t C(s_max, t)(q−1)^t with s_max = (u−1)/2, w₁−1, k′−1 resp.), which
> evaluates to the displayed A_L; for β3 the histories are constrained
> to start at j, giving the (q−1)q^{−j}-shifted A^{(j)}_L (bracket
> q^{s_max−j}, one (q−1) consumed by the entry letter). Admissibility
> and disjointness: as displayed in the statement (checked per family:
> HM3-AGG both directions on every row; the bracket lemma is what a
> HM3-AGG violation with HM3-MENU clean would refute). ∎”

**DERIVATION.** The span is the derivation.

**Arithmetic audit.** The binomial step `Σ_t C(s,t)(q−1)^t = ((q−1)+1)^s = q^s` ✓. The three `s_max` values `(u−1)/2`, `w₁−1`, `k′−1` are the interior-history lengths of the RAM, 2SIDED and SPLITEQ/INERTDEEP block genres respectively, and substituting them reproduces the `A_L` exponents of `.12` — verified there ✓. The β3 shift `(q−1)q^{−j}` reproduces the `A^{(j)}` column exactly ✓ (`.12`'s four-row check).

**CONDITIONALITY.** Conditional on `.22`, `.23`, `.25`, and W12-L0 at pin. The note states its own falsifier for this unit: “the bracket lemma is what a HM3-AGG violation with HM3-MENU clean would refute”.

**XREF.** `W12_PROOF_2026-08-08.md` — `W12-L0`, count 32. `W11_PROOF_2026-08-08.md` — `THEOREM W-11`, count 3.

---

### EFF.HMENU3.27  [lemma]

**CANONICAL STATEMENT** (verbatim, S5.1 L413–427). FORM: paragraph.

> “SEP families: W-12 S2.1/S2.3 (level-0 separable patterns are decided
> at level 0, counts C₀(q)·q^{3(N−1)}; point families, d_F = 0). DBL
> families: LEMMA W12-L1(a)(b)(c) + W12-L0 give count = q(q−1)·q^{N−1}
> × A_L(N) per family — aggregated forms above; machine: the committed
> w12 `dbl_keys` summed over histories equal these laws at all 23 w12
> cubic rows (HM3-DBLTIE, both directions, incl. the boundary keys).
> TRP families: THEOREM HM3.B. Cross-stratum disjointness: level-0
> factorization type separates SEP/DBL/TRP; within strata, the
> deterministic read keys partition. q/characteristic-uniformity: every
> law is one polynomial expression in q; the loci differ across
> characteristics (Artin–Schreier vs square classes; the char-3 cube
> degeneration in α), the counts do not — J-D0's blindness, corroborated
> at tally granularity by the battery's 15 cross-characteristic pairs
> (via HM3-HEX3TIE riding HEX3-CHAR's 17 pairs plus this battery's own
> both-characteristic per-key equality against ONE predictor).”

**DERIVATION.** Three strata, three warrants: SEP imported from W-12 §S2.1/S2.3; DBL from W12-L1(a)(b)(c) + W12-L0; TRP from HM3.B. Disjointness is two-level (cross-stratum by level-0 factorization type, within-stratum by determinism).

**Arithmetic audit.** The shared-pair count **15** was recomputed by set intersection of the two ring-type rosters: `q=2:{3..9}(7) + q=3:{2..6}(5) + q=5:{2,3}(2) + q=7:{3}(1)` = **15** ✓. The claim that HM3-HEX3TIE “rides HEX3-CHAR's 17 pairs” is consistent — HEX3's shared count is independently recomputed as **17** in `spec/EFF-HEX3.md` `.49` ✓, and the two rosters differ, so 15 ≠ 17 is expected, not a discrepancy.

**CONDITIONALITY.** Conditional on W-12 §S2.1/§S2.3, W12-L0/L1 at pin, and HM3.B. J-D0 is corroborative only (N-1 does not exclude it; S9 lists it as “the gauge-blindness frame (corroborated again…)”), consistent with HEX3's own N-6.

**XREF.** `W12_PROOF_2026-08-08.md` — `S2.1`, count 23; `S2.3`, count 35; `W12-L1(a)`, count 1; `W12-L1(b)`, count 2; `W12-L1(c)`, count 6; `W12-L0`, count 32. `JD0_PROOF_2026-08-08.md` — `J-D0`, count 25.

---

### EFF.HMENU3.28  [lemma]

**CANONICAL STATEMENT — frozen form and governing corrected reading.** This is **ANNEX A site 2**.

**Frozen form** (verbatim, S5.2 L431–440). FORM: paragraph.

> “Every core-family member exits DECIDED under the conservative read:
> all consulted digits at heights < N and every residual separable. Ore
> (W-12 S2.3) then assigns the SAME σ to every O-lift **(not only
> disc ≠ 0 ones)** at the terminal frame; the transports preserve
> in-window-ness (window coherence, HEX3 H-2(i)/H-3) so the certificate
> holds in the original frame; for DBL members W12-L1(c) transports
> W-11's (A0) (its sealed double-lift oracle leg included). Machine:
> HM3-ORACLE — PARI confirms the σ multiset of EVERY deep-decided
> member on four rows (the first independent σ check EVER on deep TRP
> members: the w12 oracle rows had none), 9,952 members.”

**GOVERNING EFFECTIVE FORM.** ANNEX A, site 2 (L885–889):

> “2. **§S5.2 ((A0), the proof, L431–437).** As frozen: "Ore (W-12 S2.3)
>    then assigns the SAME σ to every O-lift **(not only disc ≠ 0 ones)**
>    at the terminal frame". **Read as:** "… assigns the SAME σ to every
>    O-lift **with disc ≠ 0** at the terminal frame", the parenthetical
>    WITHDRAWN.”

**Therefore the effective §S5.2 reads “Ore (W-12 S2.3) then assigns the SAME σ to every O-lift with disc ≠ 0 at the terminal frame”, with the parenthetical “(not only disc ≠ 0 ones)” deleted.** Everything else in the paragraph — the in-window transport, the W12-L1(c) DBL leg, and the machine record — is unchanged.

**SUPERSESSION KIND:** `replacement` (a false parenthetical withdrawn). **CHAIN:** frozen L431–437 → ANNEX A. **TERMINAL: ANNEX A.** **TARGETS:** this unit and `.14` are ANNEX A's only two named sites.

**Compiler note on the line cite.** ANNEX A cites “L431–437”; the paragraph as quoted above runs L431–440, with L438–440 the machine sentence. The cited range covers exactly the *defective* portion (through “W-11's (A0) (its sealed double-lift oracle leg included)”), which is the correct scoping — the machine sentence is untouched. **The cite is precise, not loose** ✓.

**DERIVATION.** The corrected clause's warrant is W-12 §S2.3 **post-r4**; the counter-instance showing the frozen form false is `.64`.

**CONDITIONALITY.** Conditional on W-12 §S2.3 at its post-r4 form (an inbound correction, header §C item 1) and on HEX3 H-2(i)/H-3 for the transport of in-window-ness. **The oracle leg is characteristic-blind** (`.65`), so it neither confirmed nor refuted the frozen quantifier — ANNEX A's “blind, not wrong” disclosure.

**XREF.** `W12_PROOF_2026-08-08.md` — `S2.3`, count 35; `W12-L1(c)`, count 6. `HEX3_PROOF_2026-08-08.md` — `H-2(i)`, count 4; `H-3`, count 5.

---

### EFF.HMENU3.29  [lemma]

**CANONICAL STATEMENT** (verbatim, S5.3 L444–453). FORM: paragraph proof.

> “r(N) = q^{3N} − Σ visible core counts. By exhaustiveness (HM3.A/B +
> w12's DBL seal + S2.1's SEP), the complement is exactly: the DBL
> boundary/undecided mass q(q−1)q^{N−1}·[⌊(N−1)/2⌋(q−1)q^{N−2} +
> q^{N−1}] (the transported SPLIT-TAIL aggregate (q−1)q^{N−2} per w and
> the W-11 undecided q^{N−1}; machine: HM3-DBLTIE's boundary keys) plus
> the TRP conservative residue q·u(q,N) (THEOREM HEX3.A, consumed at
> pin; machine: HM3-DRAIN re-derives it per key). Hence r(N) ≤
> (N+2)q^{2N} and r(N)/q^{3N} → 0. Note this is a sharpening of the
> (hExhaust-3) discharge: the boundary families now have EXACT laws,
> not just vanishing bounds. ∎ (THEOREM HM3.C)”

**DERIVATION.** The span is the derivation; the bound is audited at `.15`, where it is re-derived from the displayed ingredients and confirmed numerically over `q ∈ {2,3,4,5,7,8,9,11,13,27}`, `N = 2..59`.

**Arithmetic audit of the DBL boundary decomposition.** `⌊(N−1)/2⌋(q−1)q^{N−2}` is exactly W-11's SPLIT-TAIL aggregate at window `N` per centre (the same expression HEX3's `R(M)` carries as its tail summand, `spec/EFF-HEX3.md` `.26`) ✓, and `q^{N−1}` is W-11's UNDECIDED aggregate ✓ — so the bracket is `R(N)` in HEX3's notation, and the DBL boundary mass is `q(q−1)q^{N−1}·R(N)`. That is exactly the DBL family prefactor `q(q−1)q^{N−1}` (`.27`) applied to the block's *non*-decided exits, which is the right complement ✓. **The decomposition is structurally consistent with both suppliers.**

**CONDITIONALITY.** Conditional on **exhaustiveness** (HM3.A/B + the w12 DBL seal + §S2.1's SEP) and on **THEOREM HEX3.A at pin**. Note what it is NOT conditional on: HEX3-BOX-1 (`.30`).

**XREF.** `HEX3_PROOF_2026-08-08.md` — `THEOREM HEX3.A`, count 11. `W11_PROOF_2026-08-08.md` — `SPLIT-TAIL`, count 21. `W12_PROOF_2026-08-08.md` — `S2.1`, count 23.

---

### EFF.HMENU3.30  [scope-record]

**CANONICAL STATEMENT** (verbatim, S5.4 L457–467). FORM: bold-headed section paragraph. **This is the unit that keeps ledger row HYP.137 off the critical path.**

> “HEX3 left open the exact σ-undecided law U₃^σ (q^N ≤ U₃^σ ≤ q·u):
> some conservative-drained members (transported SPLIT-TAILs, visible
> deep vertices) are in truth σ-decided. W-12.D never asks about them:
> (A2)'s r(N) is DEFINED as the complement of the visible core menu —
> "the σ-undecided residue AND any window-boundary (tail) families"
> route through it with no σ-labeling; and (A0) is quantified over CORE
> members only. So the reduction consumes exactly {(A1) exactness +
> disjointness, (A0) on the menu, r(N) → 0} — all delivered above. The
> tail-σ-certification lemma remains what it was: the missing piece of
> the exact U₃^σ law ONLY (HEX3-BOX-1, inherited open, price
> unchanged).”

**DERIVATION.** A quantifier argument: `(A2)` defines `r(N)` as a complement (so nothing inside it needs a σ-label) and `(A0)` quantifies over core members only (so nothing outside the menu needs a certificate). Together they exclude the σ-residue from the reduction's inputs.

**CONDITIONALITY — and the corpus-level significance.** This paragraph is quoted **verbatim by HEX3's own Correction A** (`spec/EFF-HEX3.md` `.65`) as leg (b) of the evidence that HEX3-BOX-1's tail-σ lemma was never part of `(hMenu-3)`. **Verified:** the quoted sentence is at `HMENU3_PROOF_2026-08-08.md` **L465–467** exactly as HEX3 cites it ✓ (a NEAR-MISS on fixed-string grep only because the source wraps it across three lines). So this unit is simultaneously (i) HMENU3's own fence and (ii) the load-bearing citation in another accepted note's correction. A chapter cut that drops it breaks HEX3's Correction A.

**Ledger cross-reference.** `spec/HYPOTHESIS_LEDGER.md` HYP.137 records the same separation: “NOT consumed by drainage … only this aside's W-12.B corroboration is conditional on it”, and census row **O-10** records “Drainage consumes only the proved conservative upper bound U₃^conv (exact law, HEX3.A)”. **All three sources agree** — HMENU3 §S5.4, HEX3 L692–693, and the census — and this compilation confirms they name different consumers rather than contradicting.

**XREF.** `HEX3_PROOF_2026-08-08.md` — `HEX3-BOX-1`, count 11. `spec/HYPOTHESIS_LEDGER.md` — `HYP.137`, count 11. `docs/TIGHTNESS_CENSUS_2026-08-11.md` — `O-10`, count 1. `W12_PROOF_2026-08-08.md` — `THEOREM W-12.D`, count 5.

---

### EFF.HMENU3.31  [lemma]

**CANONICAL STATEMENT** (verbatim, S5.5 L471–487). FORM: paragraph with a three-item bulleted display.

> “W-12.D's Steps 1–4 (PROVED, unconditional as a reduction) applied to
> the S5.1 menu: R_τ = Σ_F Σ_{x∈P_F} dens_F(x), absolutely convergent
> geometric sums. Executed (machine: HM3-RTAU, exact symbolic):
>
> * per-center n = 2 block densities Σ A_L/q^{2M}: RAM 1/(q(q+1)),
>   2SIDED 1/(q³(q+1)), SPLITEQ (q−2)/(2q³(q+1)), INERTDEEP
>   1/(2q²(q+1)) — total q^{−2} exactly (the n = 2 menu is
>   density-exhaustive; equals the engine's β(2) after ×q²).
> * TRP: T_τ = (T⁰_τ + β_τ)·(q⁶−1)/(q⁶−q), where T⁰_τ = the Group-I
>   series, the amplifier is Σ_m b(m)q^{−9m}·q^{6m}-summed (LEMMA
>   HM3-4: 1 + (q−1)/(q⁶−q) inverse-geometric = (q⁶−1)/(q⁶−q)), and
>   β_τ = c²_{τ′}·(q−1)²q²/((q⁶−1)(q³−1)) collects the three routes
>   (β1 + β2 + β3 = (q−1)(q−2) + (q−1) + (q−1)²/(q³−1) over q(q⁶−1)).
>   Σ_τ T_τ = q^{−3} exactly; q³·T_τ = β₃(τ), the engine's triple
>   cluster law, term for term.
> * whole space: R_τ = SEP_τ + (q−1)·c²_{τ″} + q·T_τ — the displayed
>   five forms; Σ_τ R_τ = (q−1)/q + (q−1)/q² + 1/q² = 1. ∎”

**DERIVATION.** The span is the derivation: W-12.D's Steps 1–4 executed against the §S5.1 menu, with the three summation layers displayed.

**Mandatory arithmetic audit (rule 22) — every displayed identity recomputed.** (1) **Block densities sum to `q^{−2}`:** over the common denominator `2q³(q+1)` the four numerators are `2q²`, `2`, `q−2`, `q`, summing to `2q(q+1)`, hence total `1/q²` ✓ — **exact**, confirmed in exact rational arithmetic at every `q = 2..39`. (2) **The α-amplifier:** `Σ_{m≥0} b(m)q^{−3m}` with `b(0) = 1`, `b(m) = (q−1)q^{4m−1}` gives `1 + (q−1)q^{−1}Σ_{m≥1}q^{4m}q^{−9m}·q^{6m}`… evaluated as the note states it, `1 + (q−1)/(q⁶−q) = (q⁶ − q + q − 1)/(q⁶−q) = (q⁶−1)/(q⁶−q)` ✓ — **the displayed closed form is exactly right**, and the cancellation `−q + q` is what makes it clean. (3) **The whole-space sum:** `(q−1)/q + (q−1)/q² + 1/q² = (q² − q + q − 1 + 1)/q² = 1` ✓. (4) **The five `R_τ` and `Σ_τ R_τ = 1`:** verified in exact rational arithmetic at all `q = 2..39`, zero failures ✓ (`.17`).

**CONDITIONALITY.** Conditional on **THEOREM W-12.D's Steps 1–4 at pin** (proved, unconditional as a reduction) and on the §S5.1 menu. `q³·T_τ = β₃(τ)` is a **cross-tie** to the density engine, not a supply (N-3).

**XREF.** `W12_PROOF_2026-08-08.md` — `THEOREM W-12.D`, count 5. Artifact `verification/om_density_engine.py` — EXISTS ✓.

---

### EFF.HMENU3.32  [scope-record]

**CANONICAL STATEMENT** (verbatim, S5.5 L489–493). FORM: paragraph.

> “Conditionality: exactly the S9 stack — no new hypothesis. The wild
> strata are inside the same laws (RAM3/deep-RAM3 at p = 3;
> LINRAM2/RAM2LIN/β-RAM at p = 2), PARI-oracled at p = 2, 3 including
> the WILD DEEP members ((Zp,3,5): 972 deep-RAM3 members = wild totally
> ramified cubics behind a refinement step — all confirmed {(3,1)}).”

**DERIVATION.** [RECORD] — the wildness disclosure, which is what makes the corollary's “wild included” claim checkable rather than rhetorical.

**CONDITIONALITY.** “no new hypothesis” is the load-bearing claim and it is corroborated by `.56`'s one-line hypothesis set. The wild oracle coverage is **mixed-characteristic only** (`.35`, `.65`) — so “PARI-oracled at p = 2, 3” means over `ℤ_p`, not over `F_q[[t]]`. That distinction is exactly what ANNEX A later turns into the “blind, not wrong” disclosure. Flagged here so a consumer does not read wild-equal-characteristic coverage into this sentence.

**XREF.** none new.

---

### EFF.HMENU3.33  [hypothesis-box]

**CANONICAL STATEMENT** (verbatim, S6 L497–499 — HM3-BOX-1). FORM: bold-headed bulleted box.

> “* **HM3-BOX-1 (σ-residue; inherited).** HEX3-BOX-1 verbatim: the
>   exact U₃^σ law needs the tail-σ-certification lemma. Not consumed
>   here (S5.4). Whether U₃^σ is characteristic-independent stays open.”

**DERIVATION.** [RECORD of an inherited open obligation].

**CONDITIONALITY — the exact ledger wording.** `HM3-BOX-1` is identified with `HEX3-BOX-1` corpus-wide; `spec/HYPOTHESIS_LEDGER.md` states the identification at HYP.29's disposition — “TAIL-CERT=HEX3-BOX-1=HM3-BOX-1 is NO LONGER index-only: it is promoted to its own row **HYP.137**” — and again in the ledger's own summary line: “TAIL-CERT=HEX3-BOX-1=HM3-BOX-1; ANNEX-2's disc≠0 correction remains.” The full HYP.137 wording is compiled at `spec/EFF-HEX3.md` `.37` and §5.3 there; the operative clause for **this** note is that the lemma is **not consumed here**, which `.30` proves and the census's O-10 row confirms.

**XREF.** `HEX3_PROOF_2026-08-08.md` — `HEX3-BOX-1`, count 11. `HMENU3_PROOF_2026-08-08.md` — `HM3-BOX-1`, count 2. `spec/HYPOTHESIS_LEDGER.md` — `HYP.137`, count 11; `HYP.29`, count 8.

---

### EFF.HMENU3.34  [record]

**CANONICAL STATEMENT** (verbatim, S6 L500–527 — HM3-BOX-2, with all three supplier-arc brackets in place). FORM: bold-headed bulleted box.

> “* **HM3-BOX-2 (grades).** This note 0/2 (PE1 NOT CLEAN 0C+1G+1m @
>   f4f7b03; r1 applied [r1]**; PE2 NOT CLEAN 0C+0G+2m @ af988ee; r2
>   applied [r2]**); the corollary inherits every supplier
>   grade in S9 — in particular W-12's own PE arc ~~(r1 done, PE2
>   owed)~~ **[r1, PE1 FINDING 1 — CURRENT: PE2 ran NOT CLEAN
>   0C+3G+2m @ 1be15d2, landed 26 minutes BEFORE this note's seal
>   64d3ff9, so the sealed "PE2 owed" was stale at birth; r2 landed @
>   99f1813 (all five PE2 findings repaired note-only, and this note's
>   S8.1 BOX-2 annex applied there verbatim); counter 0/2, PE3 next
>   [r2 m2: re-verified at r2 — W-12 unchanged since 99f1813, no W12
>   PE3 in the log].
>   None of PE2's three gaps touches a clause HM3.D fires — gap 2's
>   DBL SPLIT-TAIL leg is exactly S5.3's displayed term (PE1-verified)**
>   and HEX3's arc (PE1 NOT CLEAN 0C+2G+2m @ d177fd8, counter 0/2, r1
>   ~~owed~~ **landed @ 2580f12 (all four PE1 findings, note-only),
>   counter 0/2, PE2 next. Fired-clause record [r2 m2, PE2 FINDING 2 —
>   the check r1 omitted]: HEX3 gap 1 is H-2(i)'s displayed ghost-zone
>   inequality (pairing written backwards, false at j = 1), and §S3.1's
>   proof of LEMMA HM3-2 fires H-2(i) BY NAME (window coherence). The
>   CONCLUSION consumed survives: HEX3's own PE1 re-derived the
>   corrected pairing (N−jk) on the whole range with the α-term
>   machine-tied, and the display was corrected at HEX3 r1 2580f12;
>   HEX3's gap 2 and minors touch nothing fired here (the u(2,7) value
>   consumed in (A2) re-verified to 5,664 in both forms by HEX3's PE1)**
>   [r1]). **W-11 since ACCEPTED at 2/2 (PE3 CLEAN 839b735 + PE4 CLEAN
>   16d12e1, fold 35e6545) [r2 m2].** A
>   finding against ANY of W-11/W-12/HEX3 propagates here; the
>   falsifier map is P-10.”

**DERIVATION.** [RECORD] with an embedded **fired-clause analysis** — the substantive content is not the chronology but the determination of which supplier defects touch clauses this note fires.

**SERIES membership.** ARC SERIES member 2 (see `.01`).

**Independent verification of the fired-clause record (compiler-performed).** (a) **HEX3 gap 1 = H-2(i)'s ghost-zone inequality:** confirmed — `spec/EFF-HEX3.md` `.16` compiles HEX3's `[r1]` PE1-F1 bracket, whose own words are “the sealed display paired the thresholds BACKWARDS … which is FALSE at j = 1 for N ≥ 4” ✓. (b) **§S3.1 fires H-2(i) by name:** confirmed at `.22`, whose proof opens “HEX3 H-2(i) (window coherence)” ✓. (c) **The consumed conclusion survives:** confirmed independently — this compilation re-derived the corrected inequality `(3−j)(N−1)/3 < N−jk` at both abscissae over the whole `k`-range and it holds (`spec/EFF-HEX3.md` `.16`) ✓. (d) **`u(2,7) = 5,664` in both forms:** recomputed — telescoped `4096 + 1440 + 128` and first-step `4096 + 1504 + 64`, both `= 5,664` ✓. **All four legs of the fired-clause record check out.**

**CONDITIONALITY — three supplier-arc displays, two now stale at HEAD.**
- **W-12** (`[r2]` m2 terminal: “no W12 PE3 in the log”): a compilation-time re-read is outside this note's scope; flagged at §5.2 as a *possibly* stale as-of record.
- **HEX3** (`[r2]` m2 terminal: “@ 0/2 post-r1 2580f12, PE2 next”): **STALE at HEAD.** HEX3 completed PE2–PE7, was **ACCEPTED 2/2** and is ledger-**CERTIFIED** (`spec/EFF-HEX3.md` `.64`, `.71`). No HMENU3 append reaches it. Tagged `STALE-SELF-DESCRIPTION`; nothing applied.
- **W-11** (`[r2]` m2: ACCEPTED 2/2, fold `35e6545`): current ✓.
- **This note's own “0/2”**: superseded by `.60` (ACCEPTED 2/2) and `.72` (CERTIFIED).

**XREF.** **PIN VERIFICATION:** `f4f7b03`, `af988ee`, `1be15d2`, `64d3ff9`, `99f1813`, `d177fd8`, `2580f12`, `839b735`, `16d12e1`, `35e6545` — **all ten resolve to `commit`** ✓.

---

### EFF.HMENU3.35  [fence]

**CANONICAL STATEMENT** (verbatim, S6 L528–537 — HM3-BOX-3). FORM: bold-headed bulleted box.

> “* **HM3-BOX-3 (instrument seams).** The reader/predictor are fresh
>   same-session code (the usual W10-BOX-3 caveat), mitigated by: the
>   XREAD pointwise tie to the SEALED w12 reader (decided verdict,
>   depth-0 key identity, σ) on 22 rows / 171,444 states, the committed
>   hex3/w12 JSON ties, and the IND PARI leg. F27 is a LOCAL extension
>   of the frozen field kit (y³+2y+1 over F₃; disclosed); (Fqt,27,2) is
>   the only row on it. Oracle: mixed-characteristic only, per-center
>   representatives only (translation-invariance disclosed;
>   W10-BOX-4/W11-BOX-4 inherited); cypari2 in-process instead of the
>   w12 gp-subprocess (same PARI 2.17.4 core).”

**DERIVATION.** [RECORD] — an instrument-seam disclosure.

**CONDITIONALITY.** **This box is what ANNEX A later converts into a positive finding.** Its clause “Oracle: mixed-characteristic only” is exactly the coverage limit that makes the equal-characteristic `disc = 0` lift invisible to the oracle — so no oracle verdict was falsified by the quantifier defect (`.65`). A disclosure written before the defect was known turned out to bound the defect's blast radius; recorded because it is the clearest instance in this note of a fence earning its cost.

**XREF.** `F27` field kit: `y³+2y+1` over `F₃` is disclosed inline and is a local extension, not a corpus designation — carried descriptively.

---

### EFF.HMENU3.36  [fence]

**CANONICAL STATEMENT** (verbatim, S6 L538–543 — HM3-BOX-4). FORM: bold-headed bulleted box.

> “* **HM3-BOX-4 (n ≥ 4 menu).** The β-dictionary and bracket are
>   n = 3-shaped (one split root + a quadratic block). At n ≥ 4 the
>   species set grows (higher-degree blocks, composite stages ⟹
>   [W12-H]); nothing here claims beyond n = 3. The TRANSPORT template
>   (species → scaled subsystem, bracket telescopes, dictionary
>   translates) is the W-13+ work order.”

**DERIVATION.** [RECORD].

**CONDITIONALITY.** Current and unqualified. The `[W12-H]` weld hypothesis is a NON-IMPORT here (N-1) and becomes live only at `n ≥ 4`.

**XREF.** `W12_PROOF_2026-08-08.md` — `[W12-H]`, count 17.

---

### EFF.HMENU3.37  [fence]

**CANONICAL STATEMENT — frozen form and governing corrected reading.**

**Frozen form** (verbatim, S6 L544–547 — HM3-BOX-5). FORM: bold-headed bulleted box.

> “* **HM3-BOX-5 ((A1) form pedantry).** b(m)'s two regimes mean each
>   B-family is formally TWO (A1) families (m = 0; m ≥ 1). The count
>   stays finite (≤ 45 TRP aggregate families + 4 DBL + 3 SEP); no
>   content hangs on the split.”

**GOVERNING EFFECTIVE FORM.** ANNEX B (L1093–1095):

> “* HM3-BOX-5's "≤ 45 TRP aggregate families + 4 DBL + 3 SEP" is
>   withdrawn and read as "exactly 46 formal TRP families + 4 DBL +
>   3 SEP = 53 formal (A1) families".”

**Therefore the effective HM3-BOX-5 reads: “b(m)'s two regimes mean each B-family is formally TWO (A1) families (m = 0; m ≥ 1). The count is exactly 46 formal TRP families + 4 DBL + 3 SEP = 53 formal (A1) families; no content hangs on the split.”**

**SUPERSESSION KIND:** `inventory completion` (a bound is replaced by an exact count, after a refinement the box did not perform). **CHAIN:** frozen “≤ 45” → ANNEX B. **TERMINAL: ANNEX B.** **TARGETS:** `.11` and `.62` carry the same correction.

**DERIVATION.** ANNEX B's fixed-label refinement lemma (`.68`) plus the family arithmetic (`.69`).

**Arithmetic audit — why “≤ 45” was wrong in *both* directions.** The frozen bound counts the B-split only: `26` TRP shape schemas (`7 + 7 + 12`) with the twelve B-schemas doubled gives `7 + 7 + 24 = 38`, and even the loosest reading tops out below 45 — so “≤ 45” was a safe over-estimate that was nonetheless **too small once λ is fixed**, since tiers I and II expand `7 → 11` each: `11 + 11 + 24 = 46 > 45` ✓. **ANNEX B's correction is therefore not pedantry about a bound but a genuine undercount, by exactly one family.** Recorded because the box's own title (“(A1) form pedantry”) invites a reader to skip it.

**CONDITIONALITY.** ANNEX B fences the consequence: “no content hangs on the split” survives — “It changes no raw-key law, density, complement, splitting-type formula, machine result or conditionality.”

**XREF.** none external.

---

### EFF.HMENU3.38  [instrument-record]

**CANONICAL STATEMENT** (verbatim, S7 L551–559). FORM: bold-headed paragraph.

> “**Runner:** `verification/openmath/hmenu3_checks.py`. Exact integer
> arithmetic in all counting legs; deterministic; sympy (exact
> rationals) only in HM3-RTAU; cypari2 only in HM3-ORACLE. Families
> (evidence class): HM3-PIN [NONE] (7 md5 pins: w10/w11/w12/hex3
> runners, w12/hex3 results JSONs, om_density_engine.py); HM3-MENU
> [SAME, both directions]; HM3-DRAIN [SAME]; HM3-AGG [SAME, both
> directions]; HM3-XREAD [SEAL-TIE]; HM3-HEX3TIE + HM3-W12TIE +
> HM3-DBLTIE [NONE, committed artifacts]; HM3-ORACLE [IND];
> HM3-RTAU [SYM].”

**DERIVATION.** [RECORD] — an `instrument-record` (rule 19), kept distinct from the preregistrations `.41`–`.50` and the run-record `.57`.

**CONDITIONALITY.** **FREEZE-3's `UNPINNED-VALUE` disposition applies:** the seven md5 pin *values* are not displayed. All seven files exist ✓; four are independently pinned by HEX3 and reproduce ✓. The evidence-class taxonomy is the note's own and is load-bearing for reading the scorecard: `[SAME]` families cannot decorrelate the predictor from itself, `[SEAL-TIE]` ties to a frozen external reader, `[NONE]` ties to committed artifacts, `[IND]` is PARI, `[SYM]` is symbolic. **Only `[IND]` and `[SYM]` are genuinely independent of the note's own code**, which is why the PARI σ-leg and the R_τ symbolic leg carry the evidential weight.

**XREF.** artifacts `verification/openmath/hmenu3_checks.py`, `w10_checks.py`, `w11_checks.py`, `w12_checks.py`, `hex3_checks.py`, `w12_checks_results.json`, `hex3_checks_results.json`, `om_density_engine.py` — **all eight EXIST** ✓.

---

### EFF.HMENU3.39  [table]

**CANONICAL STATEMENT** (verbatim, S7 L561–565). FORM: bold-headed paragraph (roster as prose ranges).

> “**ROSTER (41 rows, 94,824,902 per-center states):** ℤ_p: (2,3..9),
> (3,2..6), (5,2..4), (7,2..3), (13,3) [18]. 𝔽_q[[t]]: (2,3..9),
> (3,2..6), (4,2..5), (5,2..3), (7,3), (8,3), (9,3), (11,3), (27,2)
> [23]. NEVER-MEASURED: (Fqt,2,9), (Fqt,3,6), (Fqt,27,2). ORACLE
> (ℤ_p, per-center): (2,5), (2,6), (2,7), (3,5).”

`[TABLE]` (compiler transcription, alongside the source form)

| ring type | q | N-range | rows |
|---|---|---|---|
| ℤ_p | 2 | 3..9 | 7 |
| ℤ_p | 3 | 2..6 | 5 |
| ℤ_p | 5 | 2..4 | 3 |
| ℤ_p | 7 | 2..3 | 2 |
| ℤ_p | 13 | 3 | 1 |
| **ℤ_p subtotal** | | | **18** |
| 𝔽_q[[t]] | 2 | 3..9 | 7 |
| 𝔽_q[[t]] | 3 | 2..6 | 5 |
| 𝔽_q[[t]] | 4 | 2..5 | 4 |
| 𝔽_q[[t]] | 5 | 2..3 | 2 |
| 𝔽_q[[t]] | 7 | 3 | 1 |
| 𝔽_q[[t]] | 8 | 3 | 1 |
| 𝔽_q[[t]] | 9 | 3 | 1 |
| 𝔽_q[[t]] | 11 | 3 | 1 |
| 𝔽_q[[t]] | 27 | 2 | 1 |
| **𝔽_q[[t]] subtotal** | | | **23** |
| **TOTAL** | | | **41** |

**Mandatory arithmetic audit (rule 22).** Row sums `7+5+3+2+1 = 18` ✓ and `7+5+4+2+1+1+1+1+1 = 23` ✓, matching the source's `[18]` and `[23]`; total **41** ✓. State count `Σ q^{3(N−1)}` recomputed = **94,824,902** ✓ — exact. Distinct shared `(q,N)` pairs across ring types = **15** ✓, matching the header's “15 cross-characteristic (q, N) pairs”. Never-measured rows: **3** ✓. Oracle rows: **4** ✓, all `ℤ_p`, consistent with `.35`'s mixed-characteristic-only disclosure.

**CONDITIONALITY.** Roster maximum window **`N = 9`** — the same cap as HEX3's, so the depth-scope caveat of `.19` applies to this note's machine leg as well.

**XREF.** none.

---

### EFF.HMENU3.40  [run-record]

**CANONICAL STATEMENT** (verbatim, S7 L567–580). FORM: bold-headed paragraph.

> “**PRE-SEAL SMOKE DISCLOSED** (runner docstring carries the same
> record): reader+predictor+aggregate layer developed as a /tmp
> prototype; 16 enumeration rows confirmed with 0 violations after ONE
> math-side prototype repair (the block-2SIDED raw slope m+w+d → m+d,
> caught by the (Zp,2,7) prototype row — the empirical stage doing its
> job); aggregate layer confirmed at 17 (q,N) incl. (2,10),(3,7);
> oracle prototype 2,640 members 0 mismatches; R_τ verified against
> β(3)/monic assembly BEFORE composing this note. Sealed runner
> --smoke: 3 runs — runs 1–2 RED on two INSTRUMENT defects (DBLTIE
> want-map missing the committed boundary keys; L0BRK tooth needed an
> N ≥ 6 smoke row), zero math-side changes; run 3 GREEN (PIN 7, MENU
> 101, DRAIN 18, AGG 75, XREAD 116,146, HEX3TIE 8, W12TIE 69, DBLTIE
> 23, ORACLE 49, RTAU 30; teeth 7/3/1/1; 7.4 s). No full run before
> the seal.”

**DERIVATION.** [RECORD].

**TEETH disposition (rule 20).** `signed vacuity disclosure` — the note discloses unprompted (i) that the whole predictor was fitted against measurement at the prototype stage, (ii) that one **math-side** repair happened pre-seal (the block-2SIDED raw slope `m+w+d → m+d`), and (iii) that two sealed smoke runs went RED on instrument defects before the green one. This is the disclosure that makes the three never-measured rows and the `[IND]`/`[SYM]` legs the load-bearing evidence.

**CONDITIONALITY.** The prototype is “/tmp” — **UNPINNED** (rule 23), no artifact filename. Same structure as HEX3's `.44`, and with the same robustness argument: the never-measured set is what survives after removing everything the prototype touched, so an under-recorded prototype could only shrink the independent set, not inflate it.

**XREF.** `verification/openmath/hmenu3_checks.py` — EXISTS ✓ (the docstring record rides inside it).

---

### EFF.HMENU3.41  [preregistration]

**CANONICAL STATEMENT** (verbatim, S7 L583). FORM: bulleted display.

> “* P-1 [NONE] HM3-PIN 0/7 — all seven frozen files unmoved.”

**DERIVATION.** [RECORD of a preregistration]. **CONDITIONALITY.** `UNPINNED-VALUE` (FREEZE-3): the prediction is checkable only by re-running the runner, not from the note's text. **XREF.** the seven files, all EXIST ✓.

---

### EFF.HMENU3.42  [preregistration]

**CANONICAL STATEMENT** (verbatim, S7 L584–596). FORM: bulleted display with three never-measured spot blocks.

> “* P-2 [SAME] HM3-MENU 0 violations on all 41 rows, both directions.
>   Never-measured spot values (per center, computed from the sealed
>   predictor pre-run): (Fqt,2,9): 150 decided keys, decided total
>   16,674,048, deep-decided 523,008, spots
>   (('ALPHA',1),('RAM3',4)) = 131,072,
>   (('VERT1',4,1),('RAM2LIN',4,1)) = 65,536,
>   (('ALPHA',1),('RAM3',5)) = 32,768,
>   (('ALPHA',1),('LINRAM2',5,3)) = 32,768; (Fqt,3,6): 30 decided
>   keys, deep-decided 95,580, spots (('ALPHA',1),('RAM3',4)) =
>   26,244, (('FULL11SQ',1),('RAM2LIN',4,1)) = 26,244,
>   (('VERT1',4,1),('RAM2LIN',4,1)) = 17,496,
>   (('ALPHA',1),('LINRAM2',5,3)) = 5,832; (Fqt,27,2): exactly ONE
>   decided key ('RAM3',1) = 18,954, drain 729.”

**DERIVATION.** [RECORD of a preregistration] — and the strongest one in the note, because the spot values are *stated in advance* for rows no battery had ever run (rule 19's reason for splitting `preregistration` from `run-record`).

**Mandatory arithmetic audit (rule 22) — the two checkable totals recomputed from closed forms.** `(Fqt,2,9)`: `q^{3(N−1)} = 2^{24} = 16,777,216`; `u(2,9) = 103,168` (HEX3.A); decided `= 16,777,216 − 103,168 = 16,674,048` ✓ **exact match**. `(Fqt,27,2)`: `27³ = 19,683`; `u(27,2) = 27² = 729` ✓ (the drain figure) ; decided `= 18,954` ✓ **exact match**, and the claim that this is the *only* decided key is structurally forced at `N = 2` (no refine species has range at `N = 2`, so every decided state is a depth-0 leaf, and at a triple centre with `v(b₀) = 1` the only shape is `RAM3(1)`). `(Fqt,3,6)`'s deep-decided `95,580` is not recomputable from the closed forms alone without the per-key predictor and is **not independently verified here** — recorded honestly rather than passed.

**CONDITIONALITY.** `[SAME]` evidence class: the predictor and the enumerator are the same session's code, so P-2 tests internal consistency plus the never-measured extrapolation, not independence.

**XREF.** `HEX3_PROOF_2026-08-08.md` — `THEOREM HEX3.A`, count 11 (the `u(q,N)` law the totals consume).

---

### EFF.HMENU3.43  [preregistration]

**CANONICAL STATEMENT** (verbatim, S7 L597–600). FORM: bulleted display.

> “* P-3 [SAME] HM3-DRAIN 0/82 — partition = q^{3(N−1)} and drain-sum =
>   u(q,N) on every row (THEOREM HEX3.A re-derived at key granularity;
>   (Fqt,2,9) drain 103,168 = HEX3's preregistered (Zp,2,9)/q value —
>   first eq-char check at N = 9).”

**DERIVATION.** [RECORD of a preregistration].

**Arithmetic audit.** `82 = 2 × 41` ✓ (two checks per row: partition and drain-sum). `u(2,9) = 103,168` ✓, and HEX3's preregistered whole-space `(Zp,2,9)` value is `206,336`, whose `/q` is `103,168` ✓ — **the cross-note tie is exact**, and it is a genuine equal-characteristic-versus-mixed-characteristic check at the deepest shared window.

**CONDITIONALITY.** Consumes THEOREM HEX3.A at pin.

**XREF.** `HEX3_PROOF_2026-08-08.md` — `THEOREM HEX3.A`, count 11.

---

### EFF.HMENU3.44  [preregistration]

**CANONICAL STATEMENT** (verbatim, S7 L601–604). FORM: bulleted display.

> “* P-4 [SAME] HM3-AGG 0 violations — the finite aggregate menu equals
>   the summed measured raw keys, both directions, on all 41 rows (the
>   bracket LEMMA HM3-4 + the A_L/A^{(j)} aggregations machine-checked
>   against enumeration).”

**DERIVATION.** [RECORD of a preregistration]. This is the guard on `.25` and `.12`; P-10 names it as such (“an AGG violation with MENU clean → LEMMA HM3-4 or an A_L aggregation”).

**CONDITIONALITY.** `[SAME]` class. Decorrelated later by PE2's fresh route (block convolution + generating functions, no state enumeration), which “ties all 116 aggregate families at (2,9) incl. all 58 B-composites, zero mismatches” (`.59`).

**XREF.** none.

---

### EFF.HMENU3.45  [preregistration]

**CANONICAL STATEMENT** (verbatim, S7 L605–607). FORM: bulleted display.

> “* P-5 [SEAL-TIE] HM3-XREAD 0 divergences on the 22 rows ≤ 65,536
>   states (171,444 pointwise states: decided verdict + depth-0 key
>   identity + σ vs the sealed w12 read_trp).”

**DERIVATION.** [RECORD of a preregistration] — the faithfulness leg tying this note's fresh reader to the sealed w12 convention.

**CONDITIONALITY.** Scoped to the 22 rows with `≤ 65,536` states; the deep rows carry no seal tie. Same scope structure as HEX3's P-3.

**XREF.** artifact `verification/openmath/w12_checks.py` — EXISTS ✓.

---

### EFF.HMENU3.46  [preregistration]

**CANONICAL STATEMENT** (verbatim, S7 L608–613). FORM: bulleted display.

> “* P-6 [NONE] HM3-HEX3TIE 38/38 committed hex3 rows (first-step
>   species (locus, drained) maps identical); HM3-W12TIE 23/23 w12
>   cubic rows (depth0_keys both directions, trp_deep_decided = q ×
>   predictor deep sum, U3TRP = q·u); HM3-DBLTIE 23/23 (dbl_keys
>   summed over histories == the four DBL aggregate laws + the
>   SPLIT-TAIL/UNDECIDED boundary laws, both directions).”

**DERIVATION.** [RECORD of a preregistration] — three committed-artifact ties.

**Compiler note on the 38.** HEX3's own roster is 46 rows, so “38/38 committed hex3 rows” is a **subset** — the rows this battery's roster shares with HEX3's committed results. Recomputed: the 41-row HMENU3 roster and the 46-row HEX3 roster share exactly **38** `(ring, q, N)` cells ✓ (HMENU3's `(Zp,13,3)`, `(Fqt,7,3)`, `(Fqt,8,3)`… are on HEX3's roster too; the three that are not shared are `(Fqt,2,9)`, `(Fqt,3,6)`, `(Fqt,27,2)` — **exactly the three never-measured rows** ✓). **The 38 is therefore `41 − 3` and is exactly right, and the identity of the three excluded rows is a satisfying independent confirmation of the never-measured census.**

**CONDITIONALITY.** `[NONE]` class — ties to committed artifacts, whose md5s are pinned at `.38` but whose values are not displayed (`UNPINNED-VALUE`).

**XREF.** artifacts `verification/openmath/hex3_checks_results.json` (md5 verified via HEX3 ✓), `w12_checks_results.json` (md5 verified via HEX3 ✓).

---

### EFF.HMENU3.47  [preregistration]

**CANONICAL STATEMENT** (verbatim, S7 L614–617). FORM: bulleted display.

> “* P-7 [IND] HM3-ORACLE 0 bad — deep-decided member counts EXACTLY
>   48 / 624 / 6,688 / 2,592 on (2,5)/(2,6)/(2,7)/(3,5) (9,952 PARI σ
>   multisets, every one = the leaf table; includes 972 wild
>   deep-RAM3 members at p = 3 and the p = 2 wild e = 2 composites).”

**DERIVATION.** [RECORD of a preregistration] — the note's only genuinely independent leg, and the corpus's first σ-oracle on deep TRP members.

**Arithmetic audit.** `48 + 624 + 6,688 + 2,592 = 9,952` ✓ — the four per-row counts sum exactly to the total PARI multiset count.

**CONDITIONALITY.** **Mixed-characteristic only** (`.35`), which is precisely why ANNEX A can say the oracle was “blind, not wrong” about the quantifier defect (`.65`).

**XREF.** none.

---

### EFF.HMENU3.48  [preregistration]

**CANONICAL STATEMENT** (verbatim, S7 L618–622). FORM: bulleted display.

> “* P-8 [SYM] HM3-RTAU 0 violations — Σ_τ R_τ = 1 symbolically; the
>   five R_τ == the monic assembly of om_density_engine β(2)/β(3);
>   per-center identity Σ_τ D_τ(N) = q^{3(N−1)} − u(q,N) exactly at
>   N = 24, q ∈ {2,3,4,5}; whole-space partial sums within
>   (0, q^{−(N−4)}) of R_τ.”

**DERIVATION.** [RECORD of a preregistration] — the symbolic leg.

**Arithmetic audit.** `Σ_τ R_τ = 1` **independently confirmed** in exact rational arithmetic at all `q = 2..39` ✓ (`.17`). The per-centre identity `Σ_τ D_τ(N) = q^{3(N−1)} − u(q,N)` is the partition identity of `.24`, independently confirmed at `(Fqt,2,9)` and `(Fqt,27,2)` ✓ (`.42`).

**CONDITIONALITY.** `[SYM]` class — decorrelated from the enumeration, but not from the note's own family list.

**XREF.** artifact `verification/om_density_engine.py` — EXISTS ✓.

---

### EFF.HMENU3.49  [preregistration]

**CANONICAL STATEMENT** (verbatim, S7 L623–625). FORM: bulleted display.

> “* P-9 teeth — all four at EXACTLY: HM3-T-BRACKET = 21 (rows N ≥ 4),
>   HM3-T-SHEAR = 15 (rows N ≥ 5), HM3-T-L0BRK = 10 (rows N ≥ 6),
>   HM3-T-SIGMA = 4 (all oracle rows).”

**DERIVATION.** [RECORD of a preregistration]. Exact-count teeth: both over- and under-firing are RED.

**Mandatory arithmetic audit (rule 22) — all four counts recomputed from the roster.** `N ≥ 4`: ℤ_p `(2,4..9)=6 + (3,4),(3,5),(3,6)=3 + (5,4)=1` = 10; 𝔽_q[[t]] `(2,4..9)=6 + (3,4),(3,5),(3,6)=3 + (4,4),(4,5)=2` = 11; total **21** ✓. `N ≥ 5`: ℤ_p `(2,5..9)=5 + (3,5),(3,6)=2` = 7; 𝔽_q[[t]] `(2,5..9)=5 + (3,5),(3,6)=2 + (4,5)=1` = 8; total **15** ✓. `N ≥ 6`: ℤ_p `(2,6..9)=4 + (3,6)=1` = 5; 𝔽_q[[t]] `(2,6..9)=4 + (3,6)=1` = 5; total **10** ✓. Oracle rows: **4** ✓. **All four preregistered tooth counts are exactly right.**

**CONDITIONALITY.** Confirmed at `.57`/`.58`.

**XREF.** none.

---

### EFF.HMENU3.50  [preregistration]

**CANONICAL STATEMENT** (verbatim, S7 L626–634). FORM: bulleted display.

> “* P-10 falsifiers: a MENU violation on wild rows with tame rows
>   clean → diagnose upstream at J-D0 (blueprint break-order); an AGG
>   violation with MENU clean → LEMMA HM3-4 or an A_L aggregation; an
>   XREAD divergence → the fresh reader is not the disclosed
>   convention (voids the battery, not the theorems); an ORACLE σ
>   mismatch → the leaf table/Ore step (S3.2's σ paragraph); an RTAU
>   engine-tie failure → measure-convention audit first (the engine's
>   OWN rhoN is projective — the monic assembly here was verified
>   pre-seal); a tooth off its count voids the battery.”

**DERIVATION.** [RECORD of a preregistration] — a five-branch diagnostic map, each branch naming the unit it would refute.

**CONDITIONALITY.** Confirmed not fired at `.58`. **Compiler note:** the ORACLE branch names “the leaf table/Ore step (S3.2's σ paragraph)” as the refutation target — i.e. exactly the step ANNEX A later corrects. The oracle did **not** fire, and `.65` explains why it could not have: the defect lives in equal characteristic, which the oracle never runs. **P-10's own diagnostic map therefore had a blind branch, disclosed after the fact by ANNEX A rather than in advance.** Recorded.

**XREF.** `JD0_PROOF_2026-08-08.md` — `J-D0`, count 25.

---

### EFF.HMENU3.51  [record]

**CANONICAL STATEMENT** (verbatim, S7 L636–638). FORM: bold-headed paragraph.

> “**VERDICT: PENDING — commit 1 seals this note + the runner; commit 2
> appends §S10 from `hmenu3_checks_output.txt` /
> `hmenu3_checks_results.json`.**”

**DERIVATION.** [RECORD of the two-commit protocol].

**CONDITIONALITY.** **SUPERSEDED** by `.57` (§S10's GREEN). **SUPERSESSION KIND:** `as-of scoping` — discharged by the second commit, not corrected. Both named artifacts EXIST and **both md5s VERIFY** ✓.

**XREF.** `verification/openmath/hmenu3_checks_output.txt` (md5 `7f75488790df0be3f44a721f5cebe299` ✓), `verification/openmath/hmenu3_checks_results.json` (md5 `daf077d0a417d66e45e486659a40cdbe` ✓).

---

### EFF.HMENU3.52  [supplier-finding]

**CANONICAL STATEMENT** (verbatim, S8.1 L644–656 — the BOX-2 annex text offered to W-12). FORM: display (blockquoted annex block).

> “> **[BOX-2 ANNEX, 2026-08-08, HMENU3]** The TRP refinement-family
> > menu is now COMPLETE: THEOREM HM3.A (history-resolved exact laws;
> > both node species' transfer laws leaf-resolved: α self-similar with
> > key shear, β into W12-L0 via the raw-key dictionary), THEOREM HM3.B
> > (the finite (A1)-admissible aggregate menu; instance bracket
> > (q−1)q^{4m−1}), THEOREM HM3.C ((A0) + exact-complement (A2))
> > (HMENU3_PROOF_2026-08-08.md; sealed battery, 41 rows both
> > characteristics, PARI σ-leg on 9,952 deep members). (hMenu-3) is
> > DISCHARGED at composition grade (attempt 0/2). With (hExhaust-3)
> > (HEX3) this closes W-12.D's n = 3 conditionality: COROLLARY HM3.D
> > displays the five cubic R_τ(q), Σ = 1, both characteristics, wild
> > included — conditional exactly on the arc grades of
> > W-11/W-12/HEX3/HMENU3.”

**TYPE justification.** `supplier-finding` in the rule-13 sense: an item owed to ANOTHER note and discharged at that source (here the positive form — an offered annex, not a defect report). Recorded explicitly so a cross-reader knows the enum was chosen by function.

**DERIVATION.** [ASSEMBLED from `.08` + `.11` + `.14` + `.17`] — a précis of the note's own results with no new content.

**LANDING STATUS — LANDED, with the block pin verified to the byte (template rule 10).** `W12_PROOF_2026-08-08.md` **L1685** opens “## ANNEX 2 (dated append, 2026-08-08, post-r2 — separate from the r2 repair): the W12-BOX-2 annex from HMENU3, applied verbatim”. The wrapper records:

> “Applied VERBATIM from HMENU3_PROOF_2026-08-08.md §S8.1 (HMENU3 seal
> 64d3ff9 / verdict 625fa49, battery GREEN 183,387 checks / 0 violations
> on 41 rows / 94,824,902 per-center states, both characteristics, all
> four teeth at their EXACTLY-preregistered counts 21/15/10/4, PARI
> σ-leg on all 9,952 deep-decided members of four rows), per that note's
> §S8 work order; extracted block md5
> 4eb3bacc30e3be0bc8a08a72cf9d9473, byte-identical to HMENU3 §S8.1 lines
> 573–585, and its claims re-verified against the 625fa49 verdict at
> this append”

**PIN VERIFIED:** `md5(HMENU3 L644–656)` = `4eb3bacc30e3be0bc8a08a72cf9d9473` ✓ — **exact**, so the applied block is byte-identical to HEAD's §S8.1 annex. `64d3ff9` and `625fa49` are commits ✓. Every number the wrapper re-verifies is independently confirmed by this compilation: 183,387 checks ✓ (`.57`), 41 rows ✓, 94,824,902 states ✓, teeth 21/15/10/4 ✓ (`.49`), 9,952 PARI members ✓ (`.47`).

**Recorded consumer defect.** The wrapper's line cite “HMENU3 §S8.1 lines **573–585**” is **stale**: at HEAD the block is at **L644–656** (the r1/r2 repairs shifted the body by 71 lines after extraction). The md5, not the line range, is the binding identity, and it holds. A W-12-side bookkeeping item, not a HMENU3 defect.

**CONDITIONALITY.** The annex's own “(attempt 0/2)” is stale corpus-side (HMENU3 is ACCEPTED 2/2 and CERTIFIED) and is frozen inside another note where no HMENU3 append can reach it. **W-12's own wrapper compounds it** — “HMENU3's own hostile arc has not begun” (`W12_PROOF` L1698) — which is doubly stale, the arc having both begun and completed. See OPEN-CALL 2.

**XREF.** `W12_PROOF_2026-08-08.md` — `BOX-2 ANNEX`, count 1; `W12-BOX-2`, count 8; line-addressed L1685 and L1696–1712, verified.

---

### EFF.HMENU3.53  [supplier-finding]

**CANONICAL STATEMENT** (verbatim, S8.1 L658–661). FORM: display (blockquoted pointer block).

> “> **[HEX3 S8.2 pointer, 2026-08-08, HMENU3]** Item 1's work order is
> > EXECUTED: the transports carried the decided menu exactly as
> > predicted (HMENU3_PROOF). HEX3-BOX-1 (the exact U₃^σ law) is
> > untouched and is NOT on W-12.D's critical path (HMENU3 S5.4).”

**DERIVATION.** [RECORD] — a pointer offered to HEX3's §S8.2 item 1.

**LANDING STATUS — NOT LANDED, and arguably obviated.** `grep -cF 'HEX3 S8.2 pointer' HEX3_PROOF_2026-08-08.md` = **0**; `grep -cF 'HMENU3' HEX3_PROOF_2026-08-08.md` = **2**. HEX3 addressed the same content **independently** at its own PE7 append: its **Correction A** drops the certification lemma from S8.2 item 1's ingredient list, citing HMENU3's HM3.A and quoting HMENU3 §S5.4 L465–467 verbatim (`spec/EFF-HEX3.md` `.65`). **So the offered pointer's substance landed at HEX3 by a different route, authored on the HEX3 side, without this block being applied.**

**CONDITIONALITY.** The offer is formally outstanding; its content is not. Recorded as such — a compiler may not declare an unapplied block landed because an equivalent correction exists, nor pretend the content is missing. See OPEN-CALL 3.

**XREF.** `HEX3_PROOF_2026-08-08.md` — `HMENU3`, count 2; `HEX3-BOX-1`, count 11; `S8.2`, count 10. `HMENU3_PROOF_2026-08-08.md` §S5.4 L465–467 — verified as the text HEX3's Correction A quotes.

---

### EFF.HMENU3.54  [scope-record]

**CANONICAL STATEMENT** (verbatim, S8.2 L665–678). FORM: numbered bulleted display.

> “1. **W-12.D at n = 3** — fires per COROLLARY HM3.D; the n = 3 rung of
>    the uniformity directive is complete at composition grade. Next
>    hostile work: PE arcs (this note, HEX3), W-12 PE2.
> 2. **n ≥ 4 (W-13+)** — the transport template + [W12-H] at composite
>    stages; the quartic β-dictionary needs cubic blocks (this note's
>    dictionary is the n = 3 instance of a general shear dictionary).
> 3. **Phase-B Lean** — the menu is a finite list of integer laws +
>    one recursion: a `hmenu3Law` evaluator + the 41-row table is a
>    cheap certificate target once the arcs mature (math-first: Lean
>    waits).
> 4. **Public exposition** — the R_τ table is the first COMPLETE
>    headline instance of the GOAL (all five cubic types, wild
>    included, one formula each); update the uniformity map at the
>    next milestone fold per the standing directive.”

**DERIVATION.** [RECORD of downstream work orders].

**CONDITIONALITY.** Item 1's “Next hostile work: PE arcs (this note, HEX3), W-12 PE2” is **stale at HEAD** — this note's arc completed (ACCEPTED 2/2), HEX3's completed (ACCEPTED 2/2, CERTIFIED), and W-12's PE2 had in fact already landed before the seal (`[r1]` PE1-F1). Tagged `STALE-SELF-DESCRIPTION`; no append reaches it. Item 3's precondition (“once the arcs mature”) is now satisfied. **No Lean declaration `hmenu3Law` exists at HEAD:** `grep -rF 'hmenu3Law' --include='*.lean' .` returns **0**; the only repo-wide hit is this sentence. Consistent with “Lean waits”; recorded so a blueprint does not look for it.

**XREF.** `W12_PROOF_2026-08-08.md` — `[W12-H]`, count 17; `THEOREM W-12.D`, count 5.

---

### EFF.HMENU3.55  [table]

**CANONICAL STATEMENT** (verbatim, S9 L682–730 — the conditionality stack, with all three supplier-arc brackets in place). FORM: bulleted display. *(The three bracketed arc refreshes are quoted in full at `.17` and `.34`; the stack's structure is transcribed here.)*

Opening bullet, verbatim (L682–698):

> “* **THEOREM W-12.D** @ w12 seal f669cb0 / verdict c16c717 /
>   adjudication 97122f2 / r1 repair ba0d1a4 ~~(arc 0/2, PE1
>   adjudicated, PE2 owed)~~ **[r1, PE1 FINDING 1 — arc CURRENT: PE2
>   ran NOT CLEAN 0C+3G+2m @ 1be15d2, landed 2026-08-08 08:14Z, 26
>   minutes BEFORE this note's seal 64d3ff9 (08:40Z) — the sealed "PE2
>   owed" misdescribed the supplier state; r2 landed @ 99f1813 (all
>   five PE2 findings repaired note-only; this note's S8.1 BOX-2 annex
>   applied there verbatim); counter 0/2, PE3 next. Fired-clause check
>   (PE1's): none of the three PE2 gaps touches Steps 1–4 as consumed —
>   gap 1 (the a ≡ b (mod p) disc-0 sub-genre) is fence wording on
>   disc-0 members, outside HM3.C's level-0-type partition; gap 2's
>   (hExhaust-3) DBL SPLIT-TAIL boundary leg is EXACTLY the term S5.3
>   displays (this note already carries that mass in r(N)); gap 3's
>   integrality seam is the m_i·b_i ∈ ℤ guard, satisfied at every
>   family here (HM3.B repair bracket)]** — the reduction consumed as
>   proved; its Steps 1–4 are
>   what COROLLARY HM3.D fires.”

`[TABLE]` (compiler transcription of the whole stack, alongside the source form)

| supplier | pins | consumed content | load-bearing? |
|---|---|---|---|
| THEOREM W-12.D | seal `f669cb0` / verdict `c16c717` / adjudication `97122f2` / r1 `ba0d1a4`; arc at `99f1813` per `[r2]` m2 | Steps 1–4 as a proved reduction | YES — `.17`, `.31` |
| W-12.A + S2.4 + W12-L0 + W12-L1 | the same pins | depth-0 laws; n = 2 history-resolved block laws; DBL transport; read equivalence | YES — `.08`, `.12`, `.19`, `.27` |
| THEOREM W-11 (n = 2) | seal `7020ceb` / verdict `cb05127` / r2 HEAD `31506b3`; **ACCEPTED 2/2**, fold `35e6545` | aggregates, brackets, refine isomorphism, (A0) legs — through W12-L0/L1 | YES — `.12`, `.26` |
| HEX3 (H-1..H-4, HEX3.A/B/C) | seal `e3f3459` / verdict `671a126` / annex-applied `8e535d2`; arc per `[r2]` m2 | depth-0 partition; window-coherence/shear/route lemmas (upgraded to leaf resolution here); `u(q,N)` in (A2) | YES — `.19`–`.23`, `.29` |
| LEMMA J-D0 | `1642275` / `9387eb1` | gauge-blindness frame | corroborative |
| `om_density_engine.py` + `reconcile_om_bcfg.py` | md5-pinned, committed | the R_τ cross-tie ONLY | **NO** — “No count law consumes them” |
| HMENU3's own HM3-1..HM3-4 + A/B/C/D | — | new | YES |
| Classical | — | Hensel (via W12-L1), Ore/GMN order-1 (via W-12 S2.3), lower-hull geometry, geometric series | YES |
| NOT consumed | — | weld notes / `[W12-H]`; the measure route; `htameFE`; PARI beyond the IND leg; the tail-σ lemma | — (fence N-1) |

**DERIVATION.** [RECORD] with an embedded **fired-clause check** for W-12's three PE2 gaps — the substantive content.

**Independent verification of the W-12 fired-clause check.** Gap 2's claim — “(hExhaust-3) DBL SPLIT-TAIL boundary leg is EXACTLY the term S5.3 displays” — is confirmed structurally at `.29`, where the DBL boundary bracket `⌊(N−1)/2⌋(q−1)q^{N−2} + q^{N−1}` is identified as W-11's `R(N)` (SPLIT-TAIL aggregate + UNDECIDED aggregate), the same object HEX3's `.26` compiles ✓. Gap 3's claim — the `m_i·b_i ∈ ℤ` guard is satisfied at every family — is confirmed at `.13`, where `(3/2)·2 = 3` and `1·2 = 2` both check ✓. Gap 1 is a fence-wording item on disc-0 members and is outside this note's partition, which the ANNEX A material later corroborates from the other direction ✓.

**PIN VERIFICATION (rule 23) — all fourteen commit pins.** `f669cb0`, `c16c717`, `97122f2`, `ba0d1a4`, `1be15d2`, `64d3ff9`, `99f1813`, `7020ceb`, `cb05127`, `31506b3`, `839b735`, `16d12e1`, `35e6545`, `e3f3459`, `671a126`, `8e535d2`, `2580f12`, `d177fd8`, `1642275`, `9387eb1` — **all twenty resolve to `commit`** ✓.

**CONDITIONALITY.** The HEX3 row's arc display is **stale at HEAD** (`.34`); the W-12 row's “PE3 next” is an as-of record whose currency this compilation does not re-adjudicate.

**XREF.** all designations grep-verified at `.08`, `.12`, `.14`, `.19`, `.27`, `.31`.

---

### EFF.HMENU3.56  [record]

**CANONICAL STATEMENT** (verbatim, S9 L732–736). FORM: bold-headed paragraph.

> “**One line: THEOREM HM3.A/B/C's hypothesis set = {W-11, W-12.A/L0/L1,
> HEX3 H-1..H-4 @ pins, + this note's transports/bracket}; COROLLARY
> HM3.D's = {that + THEOREM W-12.D @ pin}. No axiom, no weld face; the
> corollary's grade = the minimum over the stack's arc grades, i.e.
> composition grade 0/2 until the hostile arcs run.**”

**DERIVATION.** [RECORD] — the note's one-line hypothesis ledger, the most citable single sentence for a chapter cut.

**CONDITIONALITY.** The hypothesis sets are **current and unqualified by any annex** — ANNEX A, B and C each state they change no conditionality. The trailing grade clause (“composition grade 0/2 until the hostile arcs run”) is `STALE-SELF-DESCRIPTION`: the arcs ran, this note is ACCEPTED 2/2 and CERTIFIED, W-11 is ACCEPTED 2/2, HEX3 is ACCEPTED 2/2 and CERTIFIED. **The min-over-the-stack rule itself stands and is the right way to read the corollary's grade** — what has changed is the value of the minimum, which now turns on W-12's own arc.

**XREF.** none new.

---

### EFF.HMENU3.57  [run-record]

**CANONICAL STATEMENT** (verbatim, S10 L741–748). FORM: bold-headed paragraph.

> “**GREEN. 183,387 checks, 0 violations in every family, all four teeth
> fired at their EXACTLY-preregistered counts, zero skips.** 41/41 rows
> (94,824,902 per-center TRP states read individually with full history
> recording; 18 ℤ_p + 23 𝔽_q[[t]]), single fresh run, elapsed 443.8 s,
> exit 0; artifacts `hmenu3_checks_output.txt`
> (md5 7f75488790df0be3f44a721f5cebe299), `hmenu3_checks_results.json`
> (md5 daf077d0a417d66e45e486659a40cdbe); runner byte-identical to the
> sealed commit 64d3ff9 (empty `git diff`).”

**DERIVATION.** [RECORD of an executed instrument] — a `run-record` (rule 19), distinct from the preregistrations `.41`–`.50` and the instrument-record `.38`.

**Mandatory arithmetic audit (rule 22).** The ten per-family check counts reported in the scorecard must sum to the headline: `PIN 7 + MENU 1,031 + DRAIN 82 + AGG 707 + XREAD 171,444 + HEX3TIE 38 + W12TIE 69 + DBLTIE 23 + ORACLE 9,956 + RTAU 30` = **183,387** ✓ — exact. Rows `18 + 23 = 41` ✓; states **94,824,902** ✓; `W12TIE 69 = 23 × 3` ✓ (the note's own gloss); `HEX3TIE 38` ✓ = the shared-roster count independently recomputed at `.46`.

**PIN VERIFICATION.** Both artifact md5s reproduce EXACTLY at HEAD ✓; `64d3ff9` is a commit ✓.

**CONDITIONALITY.** The run exercises depth-0 keys and histories realized on an `N ≤ 9` roster (`.19`, `.39`).

**XREF.** artifacts as above, both EXIST and VERIFY ✓.

---

### EFF.HMENU3.58  [table]

**CANONICAL STATEMENT** — the S10 prediction scorecard, L750–793. Source header line, verbatim (L750):

> “Prediction scorecard (all ten confirmed):”

`[TABLE]` (compiler transcription; the source's bulleted form is the governing text and is quoted at the individual preregistration units `.41`–`.50`)

| prediction | class | family | result | checks |
|---|---|---|---|---|
| P-1 | [NONE] | HM3-PIN | ✓ 0/7 — all seven frozen files unmoved | 7 |
| P-2 | [SAME] | HM3-MENU | ✓ 0 violations, both directions, 41 rows; every never-measured spot exact, incl. `(Fqt,27,2)`'s two predicted keys “on the nose” | 1,031 |
| P-3 | [SAME] | HM3-DRAIN | ✓ 0 — partition and drain-sum `= u(q,N)` on every row | 82 |
| P-4 | [SAME] | HM3-AGG | ✓ 0 — the finite aggregate menu equals the summed raw keys, both directions; 116 aggregate families realized at (2,9) | 707 |
| P-5 | [SEAL-TIE] | HM3-XREAD | ✓ 0 divergences on all 22 eligible rows — verdict, depth-0 key, and σ | 171,444 |
| P-6 | [NONE] | HEX3TIE / W12TIE / DBLTIE | ✓ 38/38, 69/69 (23 × 3), 23/23 | 130 |
| P-7 | [IND] | HM3-ORACLE | ✓ 0 bad — counts 48 / 624 / 6,688 / 2,592; all 9,952 PARI σ multisets = the leaf table, incl. 972 wild deep-RAM3 at p = 3 | 9,956 |
| P-8 | [SYM] | HM3-RTAU | ✓ 0 — `Σ_τ R_τ = 1` symbolic; five R_τ == the engine's monic assembly; per-centre identity exact at N = 24, q ∈ {2,3,4,5} | 30 |
| P-9 | — | four teeth | ✓ 21 / 15 / 10 / 4, every count exactly as preregistered | — |
| P-10 | — | falsifiers | ✓ none fired | — |
| **TOTAL** | | | **GREEN** | **183,387** |

**Mandatory arithmetic audit (rule 22).** Column of checks sums to the headline **183,387** ✓ (see `.57`). Oracle sub-counts `48 + 624 + 6,688 + 2,592 = 9,952` ✓, and the reported family total is `9,956` — a difference of **4**, which is exactly the four per-row **count** checks alongside the 9,952 σ-multiset checks ✓ (internally consistent: “0 bad / 9,956 checks” for “9,952 PARI σ multisets” plus four deep-decided count assertions). Teeth `21/15/10/4` independently recomputed from the roster ✓ (`.49`). `HEX3TIE 38` independently recomputed as the shared-roster count ✓ (`.46`).

**DERIVATION.** [RECORD].

**CONDITIONALITY.** P-2/P-3/P-4 are `[SAME]` class (internal consistency plus never-measured extrapolation); only P-7 `[IND]` and P-8 `[SYM]` are independent of the note's own code. A consumer citing “183,387 checks, 0 violations” without the evidence-class split over-reads the leg.

**XREF.** none new.

---

### EFF.HMENU3.59  [record]

**CANONICAL STATEMENT** (verbatim, S10 L795–831 — the consequence-for-the-grade-box paragraph with its two arc brackets). FORM: bold-headed paragraph. Opening, verbatim:

> “**Consequence for the grade box:** THEOREMS HM3.A/B/C stand as
> composed, machine-sealed on 41 rows both characteristics with the
> menu checked key by key in both directions and the σ side
> independently oracled on every deep member of four rows — (hMenu-3)
> is DISCHARGED at composition grade (attempt 0/2; ~~the hostile arc
> has not begun~~ **[r1] arc: composed → PE1 NOT CLEAN 0C+1G+1m @
> f4f7b03 … → r1 3235e1b … [r2 arc: → PE2 NOT CLEAN 0C+0G+2m @ af988ee
> (every substantive charge CONFIRMS; machine leg bit-clean, fresh full
> run GREEN 183,387/0; second independent route — block convolution +
> generating functions, no state enumeration — ties all 116 aggregate
> families at (2,9) incl. all 58 B-composites, zero mismatches) → r2
> THIS REPAIR …]; counter 0/2; PE3
> next**).”

and closing, verbatim (L813–831):

> “COROLLARY HM3.D therefore stands at the S9 stack's
> composition grade: W-12.D FIRES AT n = 3 — the five cubic splitting
> densities R_τ(q) ∈ ℚ(q), one expression per type at every prime
> power, both characteristics, wild included, Σ_τ R_τ = 1 — the first
> COMPLETE degree instance of the uniformity directive beyond n = 2,
> conditional exactly on the displayed arc grades … HEX3-BOX-1 (the exact U₃^σ
> law) remains open and off the critical path (S5.4).”

*(Ellipses mark the arc-bracket text quoted in full at `.17` and `.34`; the elided material is chronology superseded wholesale by `.60`.)*

**DERIVATION.** [RECORD].

**SERIES membership.** ARC SERIES member 3 (see `.01`).

**CONDITIONALITY — two supersessions.** (1) The arc brackets are **SUPERSEDED** by `.60` (ACCEPTED 2/2) and then by the SOL ledger row (`.72`, CERTIFIED). KIND: `replacement`. (2) The closing “conditional exactly on the displayed arc grades” is current *as a rule* but stale *in its values* (`.56`). The final sentence — HEX3-BOX-1 open and off the critical path — is **current** and is corroborated corpus-wide (`.30`).

**Compiler note on the decorrelation leg.** PE2's “second independent route — block convolution + generating functions, no state enumeration — ties all 116 aggregate families at (2,9) incl. all 58 B-composites” is the strongest decorrelation in the note: it re-derives the aggregate layer by a method sharing no code with the enumerator. `116` and `58` are reported, not recomputable from the note's displays; recorded as source figures.

**XREF.** **PIN VERIFICATION:** `f4f7b03`, `3235e1b`, `af988ee` — all commits ✓.

---

### EFF.HMENU3.60  [acceptance-box]

**CANONICAL STATEMENT** (verbatim, L835–848). FORM: display (starred heading plus bold-headed paragraph).

> “## ★ ACCEPTANCE RECORD (orchestrator, 2026-08-08) ★
>
> **THIS NOTE IS ACCEPTED at 2/2** — PE3 (7e5026a, CLEAN; own
> enumeration of never-measured N=10 α-slices at 2×16.7M states
> confirming the b(3) bracket composition-by-composition; B3 re-derived
> in full; all double-claim candidates structurally excluded) and PE4
> (6249166, CLEAN; fresh route = the full symbolic-q identity engine —
> the entire menu verified as POLYNOMIAL IDENTITIES in ℚ[q]: tierI+II+B
> + u(q,N) ≡ q^{3(N−1)}, whole space ≡ q^{3N}, all five R_τ + Σ=1 +
> E[#roots] symbolically exact; plus a constructive HM3-2 member factory
> with 2,610 fresh PARI σ-reads at wild p=3). Full arc: composed → seal
> 64d3ff9 / verdict 625fa49 → PE1 (0C+1G+1m, f4f7b03) → r1 (3235e1b) →
> PE2 (0C+0G+2m, af988ee) → r2 (e1280be) → PE3 CLEAN → PE4 CLEAN. Four
> passes, two repairs.”

**DERIVATION.** [RECORD of an acceptance].

**SERIES membership.** ARC SERIES member 4 — **TERMINAL for the acceptance counter** (superseded only in *ledger status* by `.72`).

**SUPERSESSION KIND:** `replacement` of every prior grade statement in the note. **TARGETS:** `.01` (header), `.16` (the S1 GRADE box), `.34` (HM3-BOX-2), `.55`/`.56` (S9), `.59` (S10), and `.52`'s frozen “(attempt 0/2)” inside the landed annex.

**CONDITIONALITY — two clean passes, both genuinely decorrelated.** PE3's route is an **independent enumeration at a never-measured window** (`N = 10`, outside the 41-row roster's `N ≤ 9` cap) confirming LEMMA HM3-4's bracket `b(3)` composition-by-composition — which is exactly the depth the machine leg could not reach (`.19`, `.39`). PE4's route is a **symbolic-identity engine**: the menu verified as polynomial identities in `ℚ[q]` rather than as integers at sampled `(q,N)`. **These two together address the note's two structural evidence gaps** — the roster's depth cap and the `[SAME]` evidence class of the main families. Recorded because it is the reason the acceptance is stronger than the sealed battery alone.

**Compiler cross-check of PE4's stated identities.** `tierI + II + B + u(q,N) ≡ q^{3(N−1)}` is the partition identity of `.24`, independently confirmed here at `(Fqt,2,9)` and `(Fqt,27,2)` ✓. `Σ R_τ = 1` and `E[#roots] = q/(q+1)` independently confirmed in exact rational arithmetic at `q = 2..39` ✓ (`.17`). Whole space `≡ q^{3N}` follows from the per-centre identity times `q` ✓.

**PIN VERIFICATION.** `7e5026a`, `6249166`, `64d3ff9`, `625fa49`, `f4f7b03`, `3235e1b`, `af988ee`, `e1280be` — **all eight resolve to `commit`** ✓.

**XREF.** artifacts `lean/notes/openmath/HMENU3_passPE1_report.md` and `HMENU3_passPE4_report.md` — both EXIST ✓.

---

### EFF.HMENU3.61  [record]

**CANONICAL STATEMENT** (verbatim, L850–852). FORM: bold-headed paragraph.

> “**FREEZE-CONVENTION STAMP**: the accepted text is the post-r2 body,
> byte-frozen since e1280be (PE4 verified all four eras read their own
> texts, zero anachronisms); dated appends only hereafter.”

**DERIVATION.** [RECORD of a freeze predicate] — FREEZE-1 in §1.

**CONDITIONALITY.** Current, and honoured by all four subsequent appends, each of which re-declares it. **PIN VERIFIED:** `e1280be` = commit ✓. The parenthetical “PE4 verified all four eras read their own texts, zero anachronisms” is the freeze's own validation leg and is what licenses reading the body's `[r1]`/`[r2]` brackets as era-correct.

**XREF.** none.

---

### EFF.HMENU3.62  [acceptance-box]

**CANONICAL STATEMENT — frozen form and governing corrected reading.**

**Frozen form** (verbatim, L854–860). FORM: bold-headed paragraph.

> “**WHAT IS ACCEPTED**: THEOREMS HM3.A/B/C + COROLLARY HM3.D — the
> complete 33-family cubic core menu (exhaustiveness via the two-species
> grammar, exact q-uniform counts both characteristics, disjointness,
> (A0)+(A2)-complement), discharging (hMenu-3), and the five cubic
> densities R_τ(q) with Σ = 1 — at the S9/S10 conditionality as
> displayed (the corollary rides the W-12/HEX3 arc grades, which
> continue their own arcs).”

**GOVERNING EFFECTIVE FORM.** ANNEX B (L1096–1098):

> “* The ACCEPTANCE RECORD's "complete 33-family cubic core menu" is
>   withdrawn and read as "complete 53-formal-family cubic core menu
>   (33 shape schemas before the fixed-λ and b-regime refinements)".”

**Therefore the effective WHAT-IS-ACCEPTED clause reads: “THEOREMS HM3.A/B/C + COROLLARY HM3.D — the complete 53-formal-family cubic core menu (33 shape schemas before the fixed-λ and b-regime refinements) (exhaustiveness via the two-species grammar, exact q-uniform counts both characteristics, disjointness, (A0)+(A2)-complement), discharging (hMenu-3), and the five cubic densities R_τ(q) with Σ = 1 …”**, with the (A0) clause read at ANNEX A's disc ≠ 0 form (`.14`) as ANNEX C describes it (`.71`).

**SUPERSESSION KIND:** `counter re-reading` (the menu is unchanged; the number that names it is corrected, with the old number retained as the schema count). **CHAIN:** frozen “33-family” → ANNEX B. **TERMINAL: ANNEX B.** **TARGETS:** `.11`, `.37`.

**Mandatory arithmetic audit (rule 22) — both numbers reconstructed independently.** **Schemas (33):** tier I `7` + tier II `7` + B `12` = 26 TRP schemas, plus 4 DBL + 3 SEP = **33** ✓ — the frozen figure is the schema count and is correct as such. **Formal families (53):** tier I `4 + 2 + 2 + 3 = 11` + tier II `11` + B `12 × 2 = 24` = **46** TRP formal families, plus 4 DBL + 3 SEP = **53** ✓. Both arithmetics are exact, and the two numbers count genuinely different things — which is the whole content of ANNEX B.

**CONDITIONALITY.** The last clause — “the corollary rides the W-12/HEX3 arc grades, which continue their own arcs” — is **stale for HEX3** (ACCEPTED 2/2, CERTIFIED) and an as-of record for W-12. Tagged; no append reaches it.

**XREF.** none new.

---

### EFF.HMENU3.63  [changes-record]

**CANONICAL STATEMENT** (verbatim, ANNEX A's heading, provenance and two sites — L864–889, plus its closing grade paragraph L942–952). FORM: `##`-level dated append with bold-headed sub-paragraphs.

Heading and provenance are quoted at `.14`. The **cross-reference sweep** that closes the annex (L945–952):

> “Cross-references: W-12 §S2.3's [r4] strike with
> its counter-instance (d2d91b7); W-12's [r5] rewording of the n = 3
> FIRING CHECK row and its [r5] NOTICE ON ANNEX 2, which carries the m2
> blast-radius sweep (six surfaces; HEX3_PROOF L80–81 carries the same
> loose phrasing with its U₃^σ ≤ U₃^conv conclusion UNAFFECTED, a phrasing
> correction owed at HEX3's own arc; GENH4.C/GENHN.C are already stated
> with "EVERY lift with disc ≠ 0"); W-12 PE5's verification that HM3.C's
> substance and all counts survive (c3e2f8e).”

**DERIVATION.** [RECORD of an inherited defect and its repair].

**AUDIT disposition (rule 27).** `transfer audit` — the defect was found not by any HMENU3 tooth but by W-12's hostile arc noticing that its own `[r4]` FIRING CHECK was vouching for HMENU3's phrasing of a sentence W-12 had just struck. **No battery of this note could have produced it**, and the note says why: the oracle is characteristic-blind (`.65`).

**OUTBOUND supplier-finding — and it was discharged at the source.** The sweep names **`HEX3_PROOF` L80–81** as carrying the same loose phrasing, “a phrasing correction owed at HEX3's own arc”. **VERIFIED DISCHARGED:** HEX3's own `[r4]` (PE5 m1) repaired exactly that site — `HEX3_PROOF_2026-08-08.md` L82–93 now carries the bracket “the sealed clause read "every lift" — the over-claim W-12's own r4 struck from S2.3 with a counter-instance … The inequality stands at the pinned notion”, compiled as `spec/EFF-HEX3.md` `.06`. And the sweep's prediction that HEX3's conclusion is **UNAFFECTED** is confirmed there: `U₃^σ ≤ U₃^conv` survives at the pinned notion. **A three-note correction that closed cleanly on all three sides.**

**CONDITIONALITY.** ANNEX A's own self-description is **SUPERSEDED by ANNEX C** (`.71`): the closing paragraph's “This annex changes no statement's content and no proof step” is false and is withdrawn. The rest of the closing paragraph — “The 2/2 acceptance recorded above stands, read at the corrected quantifier” — is current.

**PIN VERIFICATION.** `d2d91b7` = commit ✓, and `grep -cF 'd2d91b7' W12_PROOF_2026-08-08.md` = **1** ✓. `c3e2f8e` = commit ✓. `grep -cF 'NOTICE ON ANNEX 2' W12_PROOF_2026-08-08.md` = **1** (L1722) ✓. `grep -cF 'FIRING CHECK' W12_PROOF_2026-08-08.md` = **6** ✓.

**XREF.** `W12_PROOF_2026-08-08.md` — `S2.3`, count 35; `NOTICE ON ANNEX 2`, count 1; `FIRING CHECK`, count 6; `d2d91b7`, count 1. `HEX3_PROOF_2026-08-08.md` — L80–93 verified (the repaired site). `GENH4.C`/`GENHN.C`: named descriptively in the sweep; their specs are compiled elsewhere in Stage 0a (`spec/EFF-GENH4.md`, `spec/EFF-GENHN.md`, both present).

---

### EFF.HMENU3.64  [lemma]

**CANONICAL STATEMENT** (verbatim, ANNEX A L891–900 — the counter-instance). FORM: bold-headed paragraph.

> “**Why the unrestricted form is false — a counter-instance inside this
> note's own menu.** Take TRP-RAM3(1), one of the seven depth-0 TRP
> families THEOREM HM3.B aggregates. Its members with b₂ = b₁ = 0
> in-window and v(b₀) = 1 exist at every window N ≥ 2. Over F_q[[t]] with
> p = 3, the lift F = y³ + b₀ has F′ = 3y² ≡ 0, hence gcd(F, F′) = F and
> disc F = 0: F = (y + b₀^{1/3})³ is inseparable, so it has NO splitting
> type σ at all and Ore certifies it for no σ. The member is
> conservative-DECIDED all the same (all consulted data in-window,
> separable residuals), so decidedness is untouched — it is exactly the
> LIFT quantifier that must exclude disc = 0.”

**DERIVATION.** The span is the derivation: exhibit a member of the note's own menu, exhibit a lift of it with `disc = 0`, observe the lift has no σ, and observe that decidedness is nonetheless untouched.

**Mathematical audit (compiler-performed).** In characteristic 3, `F = y³ + b₀` gives `F′ = 3y² = 0` ✓, so `gcd(F, F′) = F` and `disc F = 0` ✓. Over `F_q[[t]]` with `q` a power of 3 the Frobenius is bijective on the residue field, so `b₀` has a cube root in the completion and `F = (y + b₀^{1/3})³` ✓ — inseparable, no splitting type. The member `b₂ = b₁ = 0`, `v(b₀) = 1` is TRP-RAM3(1) ✓ (triple centre, `RAM3` with `h = 1`), and it is in-window for every `N ≥ 2` ✓. **The counter-instance is sound**, and it is *inside the menu*, which is what makes it decisive rather than a boundary curiosity.

**Cross-note corroboration.** The **same** counter-instance shape appears in W-12's `[r4]` strike, in `W12_PROOF`'s `[r5] NOTICE ON ANNEX 2` (“over F_q[[t]] with p = 3 the lift F = y³ + b₀ has F′ ≡ 0, hence disc = 0 and NO σ at all”), and in HEX3's `[r4]` bracket (“equal characteristic 3: an in-window TRP-RAM3(h) member, 3 ∤ h, with b₁ = b₂ = 0 admits the lift F = y³ + b₀, F′ ≡ 0, so disc = 0”). **Three notes, independently authored corrections, one witness.** Recorded because the agreement is itself evidence the correction is right.

**CONDITIONALITY.** Requires **equal** characteristic 3; over `ℤ₃` the same shape has `disc = −27b₀² ≠ 0` (`.65`). This is precisely why the oracle never saw it.

**XREF.** `W12_PROOF_2026-08-08.md` — `NOTICE ON ANNEX 2`, count 1 (carrying the same witness). `HEX3_PROOF_2026-08-08.md` — the `[r4]` bracket at L82–93, compiled at `spec/EFF-HEX3.md` `.06`.

---

### EFF.HMENU3.65  [instrument-record]

**CANONICAL STATEMENT** (verbatim, ANNEX A L930–940). FORM: bold-headed paragraph.

> “**Machine status: blind, not wrong — and blind by construction.**
> HM3-ORACLE's PARI σ-leg runs on mixed-characteristic ℤ_p rows only
> ((p,N) = (2,5), (2,6), (2,7), (3,5)) — the coverage limit already
> disclosed at HM3-BOX-3 ("Oracle: mixed-characteristic only", inheriting
> W10-BOX-4/W11-BOX-4). Over ℤ₃ the same shape y³ + b₀ has
> disc = −27b₀² ≠ 0, so the equal-characteristic disc = 0 lift never
> enters the scored set: no oracle verdict was wrong, and none was
> evidence about the unrestricted quantifier either. Same structure as
> W-12's BOX-6 disclosure at its own S3.2 witness repair. Runner and
> artifacts stay byte-frozen at the HMENU3 seal (64d3ff9 / verdict
> 625fa49).”

**DERIVATION.** A coverage argument: the defect lives in equal characteristic; the oracle runs only in mixed characteristic; therefore the oracle's 9,952 clean verdicts are neither falsified nor evidence.

**Mathematical audit.** For `F = y³ + b₀` over `ℤ₃`, `disc(y³ + a) = −27a²` ✓ (the standard cubic discriminant `−4p³ − 27q²` with `p = 0`), which is nonzero for `b₀ ≠ 0` ✓ — so the witness genuinely cannot arise on any oracle row. **The disclosure is exactly right.**

**TEETH disposition (rule 20).** `disclosed non-repair` — a guard (the σ-oracle) that could not have fired on the defect, disclosed as such rather than credited.

**CONDITIONALITY.** **This is the model instance of a pre-registered coverage fence bounding a later defect's blast radius:** HM3-BOX-3's “mixed-characteristic only” was written before the defect was known, and it is what licenses “no oracle verdict was wrong”. **PIN VERIFIED:** `64d3ff9`, `625fa49` = commits ✓; both artifact md5s reproduce ✓.

**XREF.** `W12_PROOF_2026-08-08.md` — `W12-BOX-6`, count 2.

---

### EFF.HMENU3.66  [changes-record]

**CANONICAL STATEMENT** (verbatim, the E7 adjudication frame, L956–971). FORM: `###`-level dated heading plus paragraph.

> “### Dated adjudication + corrections (2026-08-12 — sol certification C8/E7: the as-built challenge adjudicated at HEAD)
>
> The sol-5.6 as-built read of this note (gpt-5.6-sol high,
> runs/cert/C8_hmenu3_output.log, 2026-08-12) returned CHALLENGE (the
> (A1)-indexing GAP). The E7 certification run (gpt-5.6-sol high,
> runs/cert2/E7_hmenu3_output.log) adjudicated: finding 1 REAL —
> repaired by ANNEX B below (the fixed-λ refinement lemma: 7+7 shape
> schemas refine to 11+11 formal fixed-σ (A1) families, B splits to
> 24, total 46 TRP + 4 DBL + 3 SEP = 53 formal families; no count,
> law, or R_τ moves); finding 2 RESOLVED-ALREADY (Annex A's disc ≠ 0
> scoping); finding 3 REAL — repaired by ANNEX C below (Annex A's
> logical effect stated accurately: a strict weakening of the frozen
> unrestricted quantifier that preserves every consumed step).
> Everything above this heading is byte-untouched by this append. The
> E7 adjudication, transcribed unaltered:”

**DERIVATION.** [RECORD of an adjudication] — three findings, two REAL and one RESOLVED-ALREADY, each with its disposition.

**AUDIT disposition (rule 27).** `decorrelated-model audit` — a fresh-context read by a different model at HEAD, producing an (A1)-indexing gap that four hostile passes (PE1–PE4) and two prior appends did not see. **Finding 1's genre is instructive: it is a formal-indexing defect in a note whose every count is correct**, i.e. precisely the class of defect that batteries and numerical passes are structurally blind to.

**Arithmetic audit of the frame's own summary.** `7+7 → 11+11` ✓; `B → 24` ✓ (`12 × 2`); `46 = 11+11+24` ✓; `53 = 46+4+3` ✓. **The frame's arithmetic is exact.**

**CONDITIONALITY.** Finding 2's disposition (RESOLVED-ALREADY by ANNEX A) is itself verified in the transcript (L1132–1143), which quotes both of ANNEX A's corrected readings and the corrected consumed clause, and concludes “No additional mathematical repair is needed.” **Independently confirmed here** at `.14` and `.28`.

**PIN VERIFICATION.** `runs/cert/C8_hmenu3_output.log` — EXISTS ✓; `runs/cert2/E7_hmenu3_output.log` — EXISTS ✓.

**XREF.** artifacts as above.

---

### EFF.HMENU3.67  [changes-record]

**CANONICAL STATEMENT** (verbatim, ANNEX B's opening — L985–999). FORM: `##`-level dated append.

> “## ANNEX B (dated append, 2026-08-12, post-acceptance): HM3.B's shape schemas refined into formal fixed-σ (A1) families
>
> **Defect corrected.** In the frozen statement of THEOREM HM3.B, the
> words "I (7 families)" and "II (7 families)" count terminal SHAPE
> SCHEMAS, not formal (A1) families. Three of those schemas retain the
> terminal residual-factorization label λ:
>
>     ('VERT1', u₀, k, λ),   ('VERT2', u₀, t, λ),
>     ('FULL', k, λ).
>
> A formal (A1) family must have one fixed coefficient c_F(q) and one
> fixed splitting type σ_F. Consequently λ must be fixed in the family
> index. The raw-key recursion already records λ, so this is a finite
> refinement of the stated disjoint fibers, not a change to HM3.A or to
> any count.”

**DERIVATION.** The defect argument in three steps: (A1) requires one `σ_F` per family; three schemas retain λ and λ determines σ; therefore λ must enter the family index. The repair is licensed by `.07` — λ is already part of the deterministic raw key.

**SUPERSESSION KIND:** `inventory completion` (an index is completed; no object moves). **TARGETS (rule 24):** `.11` (the tier headings), `.37` (HM3-BOX-5's bound), `.62` (the acceptance record's “33-family”). Four frozen displays, one finding.

**Cross-check against `.09`.** The dictionary already fixes λ on two β leaf rows (`SPLITEQ ↦ λ=(1,1)`, `INERTDEEP ↦ λ=(2)`), so the β side needed no λ-refinement — consistent with ANNEX B's arithmetic, where B's `12 → 24` comes entirely from the `b(m)` regime split and not from λ ✓. **The asymmetry between the tiers is therefore derived, not stipulated.**

**CONDITIONALITY.** ANNEX B's own fence (L1128–1130): “This annex repairs a formal indexing gap. It changes no raw-key law, density, complement, splitting-type formula, machine result or conditionality.”

**XREF.** `runs/cert2/E7_hmenu3_output.log` — EXISTS ✓.

---

### EFF.HMENU3.68  [lemma]

**CANONICAL STATEMENT** (verbatim, ANNEX B L1001–1019 — the fixed-label refinement lemma and its proof). FORM: bold-headed lemma with an indented display and an italic proof.

> “**Fixed-label refinement lemma.** Let a q-independent finite set Λ
> index disjoint raw-key fibers F_λ, and suppose the existing exact law
> for each raw key has the form
>
>     count(F_λ(x) in window N)
>       = S_λ(q) C(q) q^{3N-ℓ(x)}
>
> with the same parameter set, visibility threshold and affine exponent
> as the containing schema, while the terminal leaf table assigns a
> fixed σ_λ to λ. Then the F_λ, λ ∈ Λ, are formal (A1) families:
> c_{F_λ}(q) = S_λ(q)C(q), ℓ and the parameter set are unchanged,
> σ_{F_λ} = σ_λ, and their disjoint union is the original schema.
>
> *Proof.* Disjointness follows because λ is part of the deterministic
> raw key (§S1 and THEOREM HM3.A). Fixing one value of a finite label
> does not change the parameter set, visibility threshold or affine
> exponent. The displayed count supplies one q-polynomial coefficient,
> and the terminal leaf table supplies one splitting type. Summing over
> the finite set Λ recovers the original schema count. ∎”

**DERIVATION.** The span is statement and proof. The proof has four moves, each discharging one clause of the (A1) contract as `.04` states it: disjointness (from determinism), parameter set / threshold / exponent (unchanged by fixing a label), `c_F(q)` (the product `S_λ(q)C(q)`), and `σ_F` (the leaf table).

**Audit against the (A1) contract.** `.04` requires per family: a splitting type `σ_F` ✓ (supplied by the leaf table), a parameter set that is a finite union of shifted products of APs ✓ (unchanged), an affine visibility threshold `ν_F` ✓ (unchanged), and `dens_F = c_F(q)q^{−ℓ_F(x)}` with `ℓ_F` affine, strictly positive coefficients ✓ (unchanged), plus pairwise disjointness ✓ and q-/characteristic-independence ✓ (`S_λ(q)` is a q-polynomial, `Λ` is q-independent by hypothesis). **Every clause of the contract is addressed; the lemma is complete as stated.**

**CONDITIONALITY.** The hypothesis “Λ q-independent” is essential and is satisfied here: `Λ₂ = {(1,1),(2)}` and `Λ₃ = {(1,1,1),(1,2),(3)}` are sets of *partition shapes*, not of residue-field data — the q-dependence lives entirely in the census polynomials `S_λ(q)` (`.69`). Recorded because a reader could mistake the λ-values for field-dependent objects.

**XREF.** none external.

---

### EFF.HMENU3.69  [table]

**CANONICAL STATEMENT** (verbatim, ANNEX B L1021–1098 — the residual censuses, their application, and the corrected family counts). FORM: displays plus bulleted counts.

The census polynomials, verbatim (L1021–1046):

> “Here the required residual censuses are themselves q-polynomials.
> For a separable quadratic residual with nonzero constant,
>
>     S^{(2)}_{(1,1)}(q) = binom(q−1,2)
>                        = (q−1)(q−2)/2,
>     S^{(2)}_{(2)}(q)   = (q²−q)/2
>                        = q(q−1)/2.
>
> The first formula chooses an unordered pair of distinct nonzero
> residue roots. For the second, the q²−q elements of
> F_{q²} \ F_q form Frobenius orbits of size two; an irreducible
> quadratic automatically has nonzero constant term.
>
> For a separable cubic residual with nonzero constant,
>
>     S^{(3)}_{(1,1,1)}(q) = binom(q−1,3)
>                          = (q−1)(q−2)(q−3)/6,
>     S^{(3)}_{(1,2)}(q)   = (q−1)(q²−q)/2
>                          = q(q−1)²/2,
>     S^{(3)}_{(3)}(q)     = (q³−q)/3.
>
> The first formula chooses three distinct nonzero roots. The second
> chooses one nonzero linear root and one irreducible quadratic; the
> two factors are automatically coprime. For the last formula,
> F_{q³} \ F_q consists of Frobenius orbits of size three, and an
> irreducible cubic again has nonzero constant term.”

and the corrected counts, verbatim (L1065–1083):

> “**Correct formal family counts.**
>
> * Tier I consists of four λ-free families
>   (RAM3, 3LIN, LINRAM2, RAM2LIN), two VERT1 families, two VERT2
>   families and three FULL families: 4+2+2+3 = 11.
> * Tier II has the same fixed-λ refinement and therefore has 11
>   families.
> * B1/B2/B3 with L ∈ {RAM, 2SIDED, SPLITEQ, INERTDEEP} give twelve
>   fixed-σ schemas. As already required by HM3.B and HM3-BOX-5, each
>   splits into its m = 0 and m ≥ 1 regimes because b(m) has two
>   formulas. Hence B contributes 12·2 = 24 formal families.
>
> Thus THEOREM HM3.B's TRP menu has exactly
>
>     11 + 11 + 24 = 46
>
> formal (A1) families. Adding the four DBL and three SEP families,
> THEOREM HM3.C's complete cubic menu has exactly 53 formal (A1)
> families.”

`[TABLE]` (compiler transcription of the census polynomials, alongside the source displays)

| residual degree | λ (factorization shape) | census `S_λ(q)` | closed form | combinatorial reading |
|---|---|---|---|---|
| 2 | `(1,1)` | `binom(q−1,2)` | `(q−1)(q−2)/2` | unordered pairs of distinct nonzero roots |
| 2 | `(2)` | `(q²−q)/2` | `q(q−1)/2` | Frobenius orbits of size 2 in `F_{q²}\F_q` |
| 3 | `(1,1,1)` | `binom(q−1,3)` | `(q−1)(q−2)(q−3)/6` | three distinct nonzero roots |
| 3 | `(1,2)` | `(q−1)(q²−q)/2` | `q(q−1)²/2` | one nonzero linear root × one irreducible quadratic |
| 3 | `(3)` | `(q³−q)/3` | — | Frobenius orbits of size 3 in `F_{q³}\F_q` |

`[TABLE]` (the corrected family counts)

| tier | shape schemas | formal (A1) families | how the refinement acts |
|---|---|---|---|
| I | 7 | **11** = 4 λ-free + 2 VERT1 + 2 VERT2 + 3 FULL | fixed-λ (`Λ₂` twice, `Λ₃` once) |
| II | 7 | **11** | same fixed-λ refinement |
| B1/B2/B3 | 12 | **24** = 12 × 2 | `b(m)` regime split (`m = 0` / `m ≥ 1`); λ already fixed by the dictionary |
| **TRP total** | **26** | **46** | |
| DBL | 4 | 4 | — |
| SEP | 3 | 3 | — |
| **MENU TOTAL** | **33** | **53** | |

**Mandatory arithmetic audit (rule 22) — every census polynomial and every count recomputed.** **Censuses:** `binom(q−1,2) = (q−1)(q−2)/2` ✓; monic irreducible quadratics over `F_q` number `(q²−q)/2 = q(q−1)/2` ✓ (Frobenius orbits of size 2 among the `q²−q` elements of `F_{q²}\F_q`), and every such has nonzero constant term ✓ (an irreducible polynomial of degree ≥ 1 other than `X` has nonzero constant); `binom(q−1,3) = (q−1)(q−2)(q−3)/6` ✓; `(q−1)·(q²−q)/2 = q(q−1)²/2` ✓; monic irreducible cubics number `(q³−q)/3` ✓ (orbits of size 3 among the `q³−q` elements of `F_{q³}\F_q`). **All five are the classical counts, and all five closed forms are algebraically exact.** **Cross-check of the degree-3 total:** `binom(q−1,3) + q(q−1)²/2 + (q³−q)/3` should count all monic separable cubics with nonzero constant and all roots accounted, i.e. `(q−1)·q·(q−1)/…` — evaluated at `q = 2`: `0 + 1 + 2 = 3`; at `q = 3`: `0 + 6 + 8 = 14`; at `q = 5`: `4 + 40 + 40 = 84`. Independent count of monic separable cubics over `F_q` with nonzero constant term: total monic cubics with nonzero constant `= q²(q−1)`; subtracting the non-separable ones gives, at `q = 2`: `4·1 = 4` minus 1 (`(y+1)³`) `= 3` ✓; at `q = 3`: `9·2 = 18` minus 4 `= 14` ✓; at `q = 5`: `25·4 = 100` minus 16 `= 84` ✓. **All three match** — the three cubic censuses are jointly exhaustive, which is exactly what the refinement needs. **Counts:** `4+2+2+3 = 11` ✓; `11+11+24 = 46` ✓; `12·2 = 24` ✓; `46+4+3 = 53` ✓; and the schema total `7+7+12+4+3 = 33` ✓ reproduces the frozen figure.

**CONDITIONALITY.** The λ-assignments to σ are given in the same annex (L1056–1063): for a vertex leaf, `λ = (1,1)` gives the split linear pair plus the remaining linear factor and `λ = (2)` an inert quadratic plus the remaining linear factor; for FULL, λ gives the three unramified cubic types `(1,1)³`, `(1,2)+(1,1)`, `(1,3)`. **These are exactly the three unramified types of COROLLARY HM3.D** ✓ — the refinement's σ-assignment and the density table's type list agree, which is the consistency check that matters.

**XREF.** none external.

---

### EFF.HMENU3.70  [scope-record]

**CANONICAL STATEMENT** (verbatim, ANNEX B L1100–1130 — the consumer sweep and the closing fence). FORM: bold-headed bulleted display.

> “**Consumer sweep.**
>
> * THEOREM HM3.A and §S3.3 survive unchanged: HM3.A is already stated
>   per raw key, and λ is part of each affected raw key.
> * THEOREM HM3.B and its §S4 proof survive after the displayed finite
>   refinement: fixing λ does not change any exponent, range,
>   visibility threshold, α-prefix bracket, β transport or block
>   aggregation.
> * THEOREM HM3.C and §S5.1 survive: the refined fibers have the same
>   disjoint union as the former schemas, and now each formal family
>   literally has the fixed σ_F required by (A1).
> * Annex A's corrected (A0) clause survives: for each fixed λ and each
>   disc ≠ 0 lift, the terminal leaf table supplies the same fixed
>   σ_{F_λ}.
> * §S5.3's exact complement and (A2) survive because the total visible
>   union and its count are unchanged.
> * §S5.5 and COROLLARY HM3.D survive because a finite disjoint
>   refinement only replaces a schema contribution by the sum of its
>   fixed-λ contributions. The construction there already groups the
>   Group-I terms as T⁰_τ by terminal σ, so the five R_τ formulas and
>   Σ_τ R_τ = 1 are unchanged.
> * The S7/S10 battery survives: it enumerates the full raw keys,
>   including λ, and therefore already measured the refined fibers.
>   All check totals, oracle totals and numerical identities remain
>   unchanged.
> * The §S8.1 W12-BOX-2 annex survives: it consumes existence of a
>   finite exact (A1) menu, which the 53-family refinement supplies.
>
> This annex repairs a formal indexing gap. It changes no raw-key law,
> density, complement, splitting-type formula, machine result or
> conditionality.”

**DERIVATION.** [RECORD of a blast-radius sweep] — eight surfaces, each with its own survival argument.

**Independent verification of the sweep (compiler-performed, surface by surface).** (1) **HM3.A per raw key with λ:** confirmed at `.07` — three leaf kinds carry λ ✓. (2) **No exponent/range/threshold changes:** confirmed at `.68`'s audit against the (A1) contract ✓. (3) **Same disjoint union:** confirmed — the refinement partitions each schema's fiber by a finite label already in the key ✓. (4) **ANNEX A compatible:** confirmed — the disc ≠ 0 scoping is over *lifts*, the λ-refinement over *members*, so the two quantifiers are independent ✓. (5) **(A2) unchanged:** confirmed — `r(N)` is the complement of the visible union, which is unchanged ✓. (6) **HM3.D unchanged:** confirmed independently — `Σ_τ R_τ = 1` and all five formulas verified in exact rational arithmetic at `q = 2..39` ✓, and the λ-to-σ assignment reproduces exactly the three unramified types of the density table ✓ (`.69`). (7) **Battery unchanged:** confirmed — the raw keys include λ (`.07`), so the measured fibers were always the refined ones ✓; all check totals re-audited and unchanged (`.57`, `.58`) ✓. (8) **The W-12 annex survives:** confirmed — the landed block claims “the finite (A1)-admissible aggregate menu” without a count, so no number in it moves ✓ (`.52`; and indeed the block contains no family count at all, which is why the landing needed no rider).

**CONDITIONALITY.** **All eight surfaces verified; the sweep is complete and correct.** This is the strongest blast-radius record in the queue-8b corpus so far, and the compilation found no surface it missed.

**XREF.** `W12_PROOF_2026-08-08.md` — `BOX-2 ANNEX`, count 1.

---

### EFF.HMENU3.71  [changes-record]

**CANONICAL STATEMENT** (verbatim, ANNEX C in full — L1151–1180). FORM: `##`-level dated append.

> “## ANNEX C (dated append, 2026-08-12, post-acceptance): logical effect of ANNEX A stated accurately
>
> ANNEX A's sentence
>
>     "This annex changes no statement's content and no proof step"
>
> is withdrawn and read as follows:
>
>     "This annex changes the frozen statement's content by strictly
>     weakening its two unrestricted lift assertions to the intended
>     disc ≠ 0 (A0) assertion. It changes no proof step consumed by
>     W-12.D and no downstream conclusion."
>
> **Derivation of strictness.** Let P be the frozen assertion that every
> lift of every member has the leaf-table splitting type, and let Q be
> the corrected assertion restricted to lifts with disc ≠ 0. Then
> P implies Q because the lifts quantified over by Q form a subset of
> those quantified over by P. The inclusion is strict: ANNEX A's member
> TRP-RAM3(1) over F₃[[t]] admits the lift F(y) = y³+t, for which
> F′ = 0 and disc(F) = 0. That lift lies in P's quantified domain but
> not Q's, and it has no separable splitting type. Hence P is false
> while the removal of that lift is material; the correction is a
> strict weakening of the frozen statement.
>
> The downstream proof nevertheless survives because §S0 already states
> (A0) using only disc ≠ 0 lifts, W-12.D's σ-labeling and Step-4 bounds
> quantify only over disc ≠ 0 lifts, and the disc-zero locus is handled
> separately as a null set. Thus ANNEX A changes statement content but
> preserves the intended theorem, all five R_τ formulas, their sum,
> the machine ledger and the corrected 2/2 acceptance.”

**DERIVATION.** The span is the derivation: `P ⟹ Q` by domain inclusion, strictness by the explicit witness `y³ + t` over `F₃[[t]]`, and survival by three named facts about what the downstream actually quantifies over.

**SUPERSESSION KIND:** `counter re-reading` — ANNEX C does **not** re-supersede the theorem's reading (ANNEX A did that); it corrects ANNEX A's characterization of its own effect. **TARGETS:** `.63` (ANNEX A's closing sentence) only. **CHAIN position:** layer 3 of C-1, and the terminal member for the *characterization* (see `.14`).

**Mathematical audit.** `P ⟹ Q` by inclusion ✓. Strictness witness `F(y) = y³ + t` over `F₃[[t]]`: `F′ = 3y² = 0` ✓, `disc = 0` ✓, and `F = (y + t^{1/3})³` is inseparable in the completion — **note this is the `b₀ = t` instance of `.64`'s general witness**, so the two annexes use the same member with a concrete uniformizer ✓. “P is false while the removal of that lift is material” ✓ — both halves needed: `P` false makes the correction necessary, materiality makes it a weakening rather than a rephrasing. **The strictness argument is complete.** The survival argument's three legs are each independently verified: §S0's (A0) is already disc ≠ 0 ✓ (`.04`, L75–76); W-12.D's σ-labeling and Step-4 bounds quantify over disc ≠ 0 lifts — asserted by ANNEX A and corroborated by W-12's own `[r5]` notice ✓; the disc-zero locus is a null set handled by Step 4's classical part ✓ (asserted, not re-derived here).

**CONDITIONALITY — why this annex matters more than its length suggests.** Without it, the corpus carries a note that (i) corrected a false theorem statement and (ii) described the correction as content-preserving. **That pairing is exactly the failure mode the honesty invariant exists to prevent**, and ANNEX C is the corpus catching it on itself. A chapter cut must carry ANNEX A and ANNEX C together; carrying A alone reinstates the error.

**XREF.** `W12_PROOF_2026-08-08.md` — `THEOREM W-12.D`, count 5. `runs/cert2/E7_hmenu3_output.log` — EXISTS ✓.

---

### EFF.HMENU3.72  [record]

**CANONICAL STATEMENT** (verbatim, the E7 provenance paragraph, L1182–1195). FORM: italic parenthetical paragraph.

> “*(The adjudication above was produced by the E7 certification run
> (gpt-5.6-sol high, runs/cert2/E7_hmenu3_output.log, 2026-08-12);
> orchestrator verification before transcription — the refinement
> lemma's mechanism checked (λ is part of the deterministic raw key,
> so fixing it refines disjoint fibers without touching parameter
> sets, thresholds, or exponents; summing over Λ recovers the schema);
> every census polynomial re-derived ((q−1)(q−2)/2 unordered nonzero
> pairs; q(q−1)/2 Frobenius orbits; (q−1)(q−2)(q−3)/6; q(q−1)²/2;
> (q³−q)/3 — the W-11/S2.1 classical forms); the counts re-added
> (4+2+2+3 = 11 per tier; 12·2 = 24; 46+7 = 53); ANNEX C's strictness
> witness checked (y³+t over F₃[[t]]: F′ = 0, disc = 0, in P's domain
> but not Q's). Transcribed unaltered per the standing division of
> labor. Ledger: row 26 → both repairs folded, awaiting sol discharge
> (cert3).)*”

**DERIVATION.** [RECORD of a verification protocol].

**SERIES membership.** ARC SERIES member 5 — **TERMINAL for ledger status**, but with a caveat the note itself states and HEAD has since overtaken (below).

**Compiler re-verification of the orchestrator's own verification (all four legs).** (1) The refinement lemma's mechanism ✓ (`.68`). (2) All five census polynomials ✓ — independently re-derived at `.69`, including a joint-exhaustiveness cross-check of the three cubic censuses at `q = 2, 3, 5` against a direct count of monic separable cubics with nonzero constant (`3`, `14`, `84`), all three matching. (3) The counts `4+2+2+3 = 11`, `12·2 = 24`, `46+7 = 53` ✓. (4) ANNEX C's strictness witness ✓ (`.71`). **All four legs check.**

**LEDGER STATUS — the note's own claim is superseded at HEAD.** The paragraph closes “Ledger: row 26 → both repairs folded, **awaiting sol discharge (cert3)**”. **That is stale.** `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` row 26 at HEAD reads:

> “| 26 | HMENU3 | never sol-read as-built | **CERTIFIED 2026-08-12** — E7 repairs (ANNEX B 53-family refinement; ANNEX C) DISCHARGED 2/2 at D3f |”

`grep -cF 'HMENU3' docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` = **1** ✓. **The awaited discharge landed** (at D3f, 2/2), so the note's ledger row is **CERTIFIED**, not awaiting. Tagged `STALE-SELF-DESCRIPTION` (rule 26); no append reaches it.

**PIN VERIFICATION.** `runs/cert2/E7_hmenu3_output.log` — EXISTS ✓; `runs/cert/C8_hmenu3_output.log` — EXISTS ✓.

**XREF.** `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` — `HMENU3`, count 1 (row 26).

---

## 4. XREF verification ledger

### 4.1 W-12 stack (`lean/notes/openmath/W12_PROOF_2026-08-08.md`, 2,462 lines)

`[TABLE]`

| # | designation | count | consumed at |
|---|---|---|---|
| X1 | `W12-BOX-2` | 8 | `.01`, `.02`, `.03`, `.21`, `.52` |
| X2 | `W12-BOX-3` | 7 | `.02` |
| X3 | `W12-BOX-6` | 2 | `.65` |
| X4 | `W12-BOX-7` | 10 | `.14` |
| X5 | `THEOREM W-12.A` | 8 | `.02`, `.08`, `.11`, `.24`, `.55` |
| X6 | `THEOREM W-12.D` | 5 | `.01`, `.02`, `.04`, `.17`, `.30`, `.31`, `.54`, `.55`, `.71` |
| X7 | `LEMMA W12-L0` | 5 | `.08`, `.09`, `.12`, `.14`, `.55` |
| X8 | `W12-L0` | 32 | `.12`, `.23`, `.24`, `.27` |
| X9 | `LEMMA W12-L1` | 7 | `.02`, `.14`, `.21`, `.55` |
| X10 | `W12-L1(a)` | 1 | `.27` |
| X11 | `W12-L1(b)` | 2 | `.21`, `.23`, `.27` |
| X12 | `W12-L1(c)` | 6 | `.14`, `.27`, `.28` |
| X13 | `S2.1` | 23 | `.14`, `.27`, `.29` |
| X14 | `S2.3` | 35 | `.10`, `.14`, `.27`, `.28`, `.63` |
| X15 | `S2.4` | 10 | `.03`, `.08`, `.10`, `.19`, `.24` |
| X16 | `[W12-H]` | 17 | `.36`, `.54` |
| X17 | `BOX-2 ANNEX` | 1 | `.05`, `.52`, `.70` |
| X18 | `NOTICE ON ANNEX 2` | 1 | `.14`, `.63`, `.64` |
| X19 | `FIRING CHECK` | 6 | `.14`, `.63` |
| X20 | `d2d91b7` | 1 | `.14`, `.63` |

**Line-addressed cites, verified:** L1218–1224 (W12-BOX-2, exact — `.03`) · L1211 (`## S6. HONEST BOXES`, confirming the “§S6” attribution) · L1685 (the ANNEX 2 heading) · L1696–1712 (the wrapper) · L1722 (the `[r5]` NOTICE).

### 4.2 W-11, HEX3, J-D0

`[TABLE]`

| # | file | designation | count | consumed at |
|---|---|---|---|---|
| X21 | `W11_PROOF_2026-08-08.md` | `THEOREM W-11` | 3 | `.08`, `.11`, `.12`, `.26`, `.55` |
| X22 | `W11_PROOF_2026-08-08.md` | `SPLIT-TAIL` | 21 | `.09`, `.15`, `.29` |
| X23 | `HEX3_PROOF_2026-08-08.md` | `THEOREM HEX3.A` | 11 | `.10`, `.15`, `.23`, `.29`, `.42`, `.43` |
| X24 | `HEX3_PROOF_2026-08-08.md` | `HEX3-BOX-1` | 11 | `.05`, `.16`, `.30`, `.33`, `.59` |
| X25 | `HEX3_PROOF_2026-08-08.md` | `LEMMA H-1` | 3 | `.19` |
| X26 | `HEX3_PROOF_2026-08-08.md` | `H-2(i)` | 4 | `.22`, `.28`, `.34` |
| X27 | `HEX3_PROOF_2026-08-08.md` | `H-2` | 11 | `.20`, `.22` |
| X28 | `HEX3_PROOF_2026-08-08.md` | `H-3` | 5 | `.23`, `.28` |
| X29 | `HEX3_PROOF_2026-08-08.md` | `S8.2` | 10 | `.53` |
| X30 | `HEX3_PROOF_2026-08-08.md` | `H-2(iii)` | **0** | `.20` — **NEAR-MISS NM-1** |
| X31 | `JD0_PROOF_2026-08-08.md` | `J-D0` | 25 | `.27`, `.50` |

### 4.3 Ledgers, consumers and artifacts

`[TABLE]`

| # | file | designation | count | consumed at |
|---|---|---|---|---|
| X32 | `HMENU3_PROOF_2026-08-08.md` | `HM3-BOX-1` | 2 | `.33` |
| X33 | `spec/HYPOTHESIS_LEDGER.md` | `HYP.137` | 11 | `.16`, `.30`, `.33`, §5.3 |
| X34 | `spec/HYPOTHESIS_LEDGER.md` | `HYP.29` | 8 | `.33` |
| X35 | `spec/HYPOTHESIS_LEDGER.md` | `HMENU3` | 9 | §5.2 RX-6 |
| X36 | `docs/TIGHTNESS_CENSUS_2026-08-11.md` | `O-10` | 1 | `.30` |
| X37 | `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` | `HMENU3` | 1 | `.72`, §5.2 RX-7 |
| X38 | `docs/PROJECT_STATE.md` | `HMENU3` | 18 | §5.2 RX-5 |
| X39 | `GENIND_PROOF_2026-08-08.md` | `HMENU3` | 19 | §5.2 RX-1 |
| X40 | `GENIND_PROOF_2026-08-08.md` | `HM3.` | 12 | §5.2 RX-1 |
| X41 | `W12_PROOF_2026-08-08.md` | `HMENU3` | 24 | §5.2 RX-2 |
| X42 | `HEX3_PROOF_2026-08-08.md` | `HMENU3` | 2 | §5.2 RX-3 |
| X43 | `leancheck/notes/N3_CHECK_2026-08-13.md` | `HMENU3` | 14 | §5.2 RX-4 |
| X44 | `HEX3_PROOF_2026-08-08.md` | `HEX3 S8.2 pointer` | **0** | `.53` — verified NON-landing |

### 4.4 NEAR-MISS dispositions (rule 15)

**NM-1 — `H-2(iii)`.** Absent as written (count 0 in `HEX3_PROOF_2026-08-08.md`); HEX3 heads the clause “(iii) **[the α-map is onto]**” without repeating the lemma name. Referent verified at `HEX3_PROOF_2026-08-08.md:287–297`, compiled as `spec/EFF-HEX3.md` `.18`. Same for `H-2(ii)` (referent at L277–285, `spec/EFF-HEX3.md` `.17`). **Disposition: NEAR-MISS**, carried descriptively; `H-2` itself has count 11 and `H-2(i)` count 4, so the family name is verified.

**NM-2 — HMENU3's own §S5.4 sentence as quoted by HEX3's Correction A.** Absent as a single fixed string (count 0) because the source wraps it across three lines; verified at `HMENU3_PROOF_2026-08-08.md:465–467`. **Disposition: NEAR-MISS**; the line cite is exact. (Recorded here because it is the outbound direction of the same wrap that `spec/EFF-HEX3.md` §4.4 NM-3 records inbound.)

**NM-3 — `GENH4.C` / `GENHN.C`** (cited in ANNEX A's sweep). Carried descriptively: the referents are those notes' own C-clauses, whose specs are compiled elsewhere in Stage 0a (`spec/EFF-GENH4.md`, `spec/EFF-GENHN.md`, both present at HEAD). Not emitted as verified XREFs here, since the sweep cites them as already-correct third parties, not as consumed content.

**No OPEN-CALL arises from any designation.** Every cited name is grep-verified at count ≥ 1 or dispositioned above. `X44` is a deliberate **verified zero** — evidence of non-landing, not a failed lookup.

### 4.5 PIN VERIFICATION ledger (rule 23)

**Commit hashes — 29 cited, 29 verified** via `git cat-file -t` → `commit`: `f4f7b03`, `3235e1b`, `af988ee`, `e1280be`, `64d3ff9`, `625fa49`, `7e5026a`, `6249166`, `99f1813`, `1be15d2`, `ba0d1a4`, `f669cb0`, `c16c717`, `97122f2`, `7020ceb`, `cb05127`, `31506b3`, `839b735`, `16d12e1`, `35e6545`, `e3f3459`, `671a126`, `8e535d2`, `2580f12`, `d177fd8`, `1642275`, `9387eb1`, `d2d91b7`, `c3e2f8e`. **Zero failures.**

**md5 pins — 3 cited with values, 3 verified byte-exactly:** `hmenu3_checks_output.txt` `7f75488790df0be3f44a721f5cebe299` ✓; `hmenu3_checks_results.json` `daf077d0a417d66e45e486659a40cdbe` ✓; and the **cross-note extracted-block pin** `4eb3bacc30e3be0bc8a08a72cf9d9473`, verified as `md5(HMENU3 L644–656)` ✓ — the strongest single pin in this note, since it binds the landed W-12 annex to HEAD's own bytes.

**`UNPINNED-VALUE` — one.** The seven HM3-PIN md5s are asserted without displayed values (FREEZE-3). All seven files exist; four are independently pinned by HEX3 and reproduce.

**`UNPINNED` — one.** The `/tmp` prototype's 16 enumeration rows and 17 aggregate `(q,N)` (`.40`) are backed by no repo artifact.

**Artifacts — 9 cited, 9 exist:** `verification/openmath/hmenu3_checks.py`, `…_output.txt`, `…_results.json`, `verification/om_density_engine.py`, `verification/reconcile_om_bcfg.py`, `runs/cert/C8_hmenu3_output.log`, `runs/cert2/E7_hmenu3_output.log`, `lean/notes/openmath/HMENU3_passPE1_report.md`, `HMENU3_passPE4_report.md`. **Zero missing.**

---

## 5. Consumption table and consumer edges

### 5.1 What HMENU3 consumes (forward edges)

`[TABLE]`

| supplier | object | pin | consuming units | load-bearing? |
|---|---|---|---|---|
| W-12 | THEOREM W-12.D Steps 1–4 (a proved reduction) | seal `f669cb0`, arc `99f1813` | `.17`, `.31` | YES — the corollary fires it |
| W-12 | `S1(iii)`'s (A1)/(A2) contract | seal `f669cb0` | `.04`, `.13` | YES — the admissibility target |
| W-12 | THEOREM W-12.A + `S2.4` depth-0 completeness | seal `f669cb0` | `.08`, `.19`, `.24` | YES |
| W-12 | LEMMA W12-L0 (history-resolved block laws) | seal `f669cb0` | `.08`, `.12`, `.26` | YES |
| W-12 | LEMMA W12-L1(a)(b)(c) | seal `f669cb0` | `.21`, `.23`, `.27`, `.28` | YES |
| W-12 | `S2.1`/`S2.3` (SEP families; the Ore warrant) | seal `f669cb0`, **S2.3 post-r4** | `.10`, `.14`, `.27`, `.28` | YES — inbound correction |
| W-11 | aggregates, brackets, refine isomorphism, (A0) legs | seal `7020ceb`, **ACCEPTED 2/2** | `.12`, `.26`, `.29` | YES |
| HEX3 | LEMMA H-1 (depth-0 partition) | seal `e3f3459` | `.19` | YES |
| HEX3 | H-2(i)/(ii)/(iii), H-3 (coherence, shear, routes) | seal `e3f3459` | `.20`, `.22`, `.23` | YES |
| HEX3 | THEOREM HEX3.A (`u(q,N)`) | seal `e3f3459` | `.15`, `.29`, `.42`, `.43` | YES — the (A2) TRP term |
| HEX3 | HEX3-BOX-1 | — | `.30`, `.33` | **NO — explicitly not consumed** |
| J-D0 | gauge-blindness frame | `1642275`/`9387eb1` | `.27` | corroborative |
| density engine | β(2)/β(3) cluster laws | md5-pinned | `.18`, `.31` | **NO — cross-tie only** |

### 5.2 Reverse-XREF rows — who consumes HMENU3 (rule 8)

All grep-verified.

`[TABLE]`

| # | consumer | designation | count | what is consumed | status |
|---|---|---|---|---|---|
| RX-1 | `GENIND_PROOF_2026-08-08.md` | `HMENU3` 19 / `HM3.` 12 | the n = 3 base-case menu and densities, as induction base data | LANDED |
| RX-2 | `W12_PROOF_2026-08-08.md` | `HMENU3` 24 / `HM3.` 24 | the **BOX-2 ANNEX**, applied verbatim at L1685ff (block md5 verified against HEAD L644–656); plus the `[r5] NOTICE ON ANNEX 2` correcting HMENU3's own (A0) phrasing | **LANDED both directions** |
| RX-3 | `HEX3_PROOF_2026-08-08.md` | `HMENU3` 2 | HEX3's **Correction A** quotes HMENU3 §S5.4 L465–467 verbatim as leg (b) of its evidence that the tail-σ lemma was never part of `(hMenu-3)` | LANDED (HEX3-authored) |
| RX-4 | `leancheck/notes/N3_CHECK_2026-08-13.md` | `HMENU3` 14 | HMENU3's five density values as expected values for an independent Ore/Newton decider — “an independent numerical confirmation of all five HMENU3 values” | LANDED; **see §5.4** |
| RX-5 | `docs/PROJECT_STATE.md` | `HMENU3` 18 | project-level status | LANDED |
| RX-6 | `spec/HYPOTHESIS_LEDGER.md` | `HMENU3` 9 | the HMENU3/HEX3 perimeter rows; `TAIL-CERT=HEX3-BOX-1=HM3-BOX-1`; “ANNEX-2's disc≠0 correction remains” | LANDED |
| RX-7 | `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` | `HMENU3` 1 | row 26: “**CERTIFIED 2026-08-12** — E7 repairs (ANNEX B 53-family refinement; ANNEX C) DISCHARGED 2/2 at D3f” | LANDED — **supersedes `.72`'s “awaiting sol discharge”** |
| RX-8 | (non-edge, recorded) | `HEX3 S8.2 pointer` | **0** in `HEX3_PROOF` | the offered pointer block did **not** land; its content arrived at HEX3 by an independently authored route | **NOT LANDED** |

**Zero-orphan check for reverse edges:** every file at HEAD that names HMENU3 appears above. The sweep covered `lean/notes/openmath/`, `docs/`, `leancheck/notes/`, `leanfinal/notes/` and `spec/`.

### 5.3 HYP.137 — how this note stands to the open row

HMENU3 is the note that **removes** HEX3-BOX-1 from the critical path. The ledger's own words (HYP.137, quoted in full at `spec/EFF-HEX3.md` `.37`) put the tail-σ lemma's only live consumer at GENIND's S8.2 W-12.B corroboration aside; **this note supplies the independent confirmation from the menu side**, at `.30`:

> “The
> tail-σ-certification lemma remains what it was: the missing piece of
> the exact U₃^σ law ONLY (HEX3-BOX-1, inherited open, price
> unchanged).”

**Three-way agreement, verified.** (i) HMENU3 §S5.4 (`.30`) — the reduction consumes `{(A1) exactness + disjointness, (A0) on the menu, r(N) → 0}` and nothing σ-residual. (ii) HEX3 L692–693 — “the (hExhaust-3) discharge never needed the split”. (iii) Census row **O-10** — “Drainage consumes only the proved conservative upper bound U₃^conv (exact law, HEX3.A)”. **All three name different consumers and none contradicts another**, which is exactly the reading HYP.137's disposition records. **Consequence for a chapter cut:** COROLLARY HM3.D's five cubic densities do **not** inherit HYP.137. The corollary's conditionality is entirely supplier-arc grades (`.56`), and HEX3-BOX-1 appears in neither hypothesis set.

### 5.4 CONSUMER NOTE — N3_CHECK's independent decider and HMENU3's five values

`leancheck/notes/N3_CHECK_2026-08-13.md` runs an independent recentring Newton-polygon decider and reports, at §6c:

> “The certified fractions rise toward the predicted densities and **never exceed them**; at `p = 3, N = 5`:
>
>     {(1,3)}        certified 0.297514   vs predicted 36/121  = 0.297521
>     {(1,1),(1,2)}  certified 0.362      vs predicted 351/968 = 0.362603
>     {(1,1)}³       certified 0.0646     vs predicted 63/968  = 0.065083
>
> and the undecided fraction falls monotonically … This is an independent numerical
> confirmation of all five HMENU3 values, *and* independent evidence that drainage at `n = 3` really
> does happen — the thing §7 says is not proved.”

**Compiler audit of the three quoted predictions against this compilation's own evaluator.** `R_{(1,3)}(3) = 36/121 = 0.2975206…` ✓; `R_{(1,2),(1,1)}(3) = 351/968 = 0.3626033…` ✓; `R_{(1,1)³}(3) = 63/968 = 0.0650826…` ✓ — **all three are exactly the `q = 3` anchors of `.18`**, independently recomputed. The decider's certified fractions sit just below each ✓, which is the expected direction for a sound-by-construction decider (anything not forced is declared UNDECIDED).

**Three consequences for a consumer of HMENU3.**
1. **This is a genuinely decorrelated confirmation of COROLLARY HM3.D at `q = 3`** — a different codebase, a different method (a real recentring decider rather than a raw-key predictor), landing on the same three rational numbers to six decimal places.
2. **It is one-sided by construction.** The decider certifies a lower bound on each density; agreement to six places is strong evidence, not proof, and the note says so (“certified … never exceed them”).
3. **It does NOT extend to THEOREM HEX3.A.** N3_CHECK's §6d records that its *undecided* totals and HEX3's `U₃^conv` are “not measuring the same set” (ledger row **HYP.138**, disposition NODE: “until it lands, neither reader's count may be cited as confirming or refuting HEX3.A”). Since HMENU3's (A2) consumes HEX3.A (`.15`, `.29`), **the §6d reconciliation is an open item on HMENU3's (A2) leg as well as on HEX3's law** — recorded here because HMENU3's own text predates it and says nothing about it. Full compilation of §6d at `spec/EFF-HEX3.md` §5.4.

---

## 6. TEETH — the inverse table (rule 6), both directions

### 6.1 Battery row → guarded unit(s)

`[TABLE]`

| family / tooth | class | preregistration | guards | disposition |
|---|---|---|---|---|
| HM3-PIN | [NONE] | P-1 `.41` | `.38`'s seven frozen inputs | clean pass; **`UNPINNED-VALUE`** — no hashes displayed |
| HM3-MENU | [SAME] | P-2 `.42` | `.08` (HM3.A), and through it `.22`, `.23`, `.24` | clean pass, 1,031 checks; never-measured spots exact |
| HM3-DRAIN | [SAME] | P-3 `.43` | `.24`'s partition identity; HEX3.A at key granularity | clean pass, 82 checks |
| HM3-AGG | [SAME] | P-4 `.44` | `.11`, `.12`, `.25`, `.26` (the bracket and the aggregations) | clean pass, 707 checks |
| HM3-XREAD | [SEAL-TIE] | P-5 `.45` | `.06`/`.07`'s reader faithfulness; the σ read of `.10` | clean pass, 171,444 states; scoped to 22 rows |
| HM3-HEX3TIE / W12TIE / DBLTIE | [NONE] | P-6 `.46` | `.27` (DBL laws), `.29` (boundary laws), HEX3.A | clean pass, 130 checks |
| HM3-ORACLE | [IND] | P-7 `.47` | `.10`, `.23`'s σ paragraph; (A0) at `.28` | clean pass, 9,956 checks — **`disclosed non-repair`** on the quantifier defect (`.65`) |
| HM3-RTAU | [SYM] | P-8 `.48` | `.17`, `.31` (the densities and Σ = 1) | clean pass, 30 checks |
| HM3-T-BRACKET / SHEAR / L0BRK / SIGMA | — | P-9 `.49` | `.25` (bracket), `.22` (shear), W12-L0 (block), `.47` (σ) | clean pass; counts 21/15/10/4 all recomputed ✓ |
| falsifier map | — | P-10 `.50` | the diagnostic procedure | none fired; **one branch structurally blind** (`.50`, `.65`) |

### 6.2 Guarded unit → battery row (inverse direction)

`[TABLE]`

| unit | guarded by | class |
|---|---|---|
| `.08` THEOREM HM3.A | HM3-MENU, HM3-DRAIN, HM3-XREAD | battery-guarded |
| `.09` the dictionary | HM3-MENU (per key), HM3-ORACLE (σ side) | battery-guarded |
| `.11` THEOREM HM3.B | HM3-AGG, HM3-T-BRACKET | battery-guarded |
| `.12` the `A_L`/`A^{(j)}` laws | HM3-AGG | battery-guarded |
| `.13` (A1)-admissibility | — | **PROOF-ONLY** |
| `.14` THEOREM HM3.C | HM3-ORACLE (A0 side, mixed char only), HM3-DRAIN (A2 side) | partially guarded |
| `.19`–`.21` LEMMA HM3-1 | HM3-MENU indirectly | **PROOF-ONLY** for (iii) |
| `.22` LEMMA HM3-2 | HM3-T-SHEAR, HM3-MENU per key | battery-guarded |
| `.23` LEMMA HM3-3 | HM3-MENU, HM3-DRAIN, HM3-ORACLE | battery-guarded |
| `.25` LEMMA HM3-4 | HM3-AGG, HM3-T-BRACKET; **PE3's independent `N = 10` enumeration** | battery-guarded + decorrelated |
| `.26` HM3.B's proof | HM3-AGG | weakly guarded |
| `.27` §S5.1 (A1) | HM3-DBLTIE, HM3-HEX3TIE | battery-guarded |
| `.28` §S5.2 (A0) | HM3-ORACLE — **mixed characteristic only** | **partially guarded; the gap is `.65`** |
| `.29` §S5.3 (A2) | HM3-DRAIN, HM3-DBLTIE's boundary keys | battery-guarded |
| `.30` §S5.4 | — | **PROOF-ONLY** (a quantifier argument) |
| `.31` §S5.5 assembly | HM3-RTAU | battery-guarded (symbolic) |
| `.33` HM3-BOX-1 | — | **UNGUARDED BY CONSTRUCTION** (inherited open obligation) |
| `.41`–`.50` preregistrations | — | they *are* the guards |
| `.52`–`.56` scope/consumer records | — | **RECORD** (guarded by §4/§5 verification) |
| `.60`–`.72` appends | — | **AUDIT-produced**, see 6.4 |

### 6.3 PROOF-ONLY rows (rule 16) — the note's own coverage-hole sentences

Four units carry their content in a proof no battery touches. The note supplies the coverage-hole sentences:

HM3-BOX-3 (`.35`), on the instrument's provenance:

> “The reader/predictor are fresh
> same-session code (the usual W10-BOX-3 caveat)”

and, on the σ leg's reach:

> “Oracle: mixed-characteristic only, per-center
> representatives only”

ANNEX A (`.65`), turning the second into a positive statement:

> “no oracle verdict was wrong, and none was
> evidence about the unrestricted quantifier either.”

So: `.13` (admissibility), `.21` (the phase-flip lemma), `.30` (the σ-residue quantifier argument), and the **equal-characteristic half of `.28`** are proof-carried, not battery-carried. Two were later decorrelated by hostile routes — PE3 re-derived `.25`'s bracket at `N = 10` and PE4 verified the whole menu as polynomial identities in `ℚ[q]` (`.60`) — and one, `.28`'s equal-characteristic half, was found *defective* by a route no battery could run (`.63`).

### 6.4 AUDIT dispositions (rule 27) — findings no tooth could produce

`[TABLE]`

| unit | AUDIT class | why no tooth applies |
|---|---|---|
| `.63` ANNEX A | `transfer audit` | found by W-12's arc noticing its own FIRING CHECK vouched for HMENU3's phrasing; the oracle is characteristic-blind (`.65`) |
| `.65` the blindness disclosure | `disclosed non-repair` | a guard that could not have fired, disclosed rather than credited |
| `.66` the E7 adjudication | `decorrelated-model audit` | a fresh-context read at HEAD by a different model |
| `.67`/`.68`/`.69` ANNEX B | `decorrelated-model audit` | a **formal-indexing** defect in a note whose every count is correct — structurally invisible to numerical batteries |
| `.71` ANNEX C | `decorrelated-model audit` | a defect in a *correction's self-description*; nothing measurable is wrong |
| `.34`'s fired-clause record | `in-house hostile pass` | PE2 FINDING 2 asked a question no tooth asks: which supplier defects touch clauses this note fires |

**Every one of the note's post-acceptance corrections is audit-produced; none came from a tooth.** With `.40`'s disclosure that the *pre-seal* math-side repair also came from an empirical prototype rather than a tooth, the honest summary is: **this note's batteries confirmed its arithmetic and found none of its five defects.**

### 6.5 Zero-orphan check

**Battery rows → units: zero orphans.** All nine families and all four teeth guard at least one inventoried unit (6.1).

**Units → guards: 72 units, 44 guarded, 28 unguarded.** The 28 decompose as: 4 PROOF-ONLY (6.3), 1 inherited open obligation (`.33`), 10 preregistrations (guards, not guarded), and 13 records/scope/append units covered by §4's pin verification and §5's grep verification instead. **No unit is silently unguarded.**

---

## 7. Arithmetic audit and fidelity audit (compile-time, mechanical)

### 7.1 Arithmetic audit — what was recomputed and what it found

Every number recomputable from the note's own closed forms was recomputed **independently of the note's tables**, using evaluators written from THEOREM HEX3.A's law and HMENU3's own displays.

**Confirmed exactly (no discrepancies):**

- **Roster:** 18 + 23 = 41 rows; `Σ q^{3(N−1)}` = **94,824,902** states; 15 cross-characteristic pairs; 3 never-measured rows.
- **Check-count arithmetic:** `7 + 1,031 + 82 + 707 + 171,444 + 38 + 69 + 23 + 9,956 + 30` = **183,387** ✓, exactly the headline.
- **All four tooth counts** recomputed from the roster: `21 / 15 / 10 / 4` ✓.
- **The oracle sub-counts:** `48 + 624 + 6,688 + 2,592 = 9,952` ✓, and the family total `9,956` = 9,952 σ-multisets + 4 count assertions ✓.
- **The 38 HEX3TIE rows:** the HMENU3 and HEX3 rosters share **exactly 38** `(ring,q,N)` cells, and the 3 that differ are **exactly** `(Fqt,2,9)`, `(Fqt,3,6)`, `(Fqt,27,2)` — the three never-measured rows ✓. An independent confirmation of the never-measured census.
- **Two never-measured totals from closed forms:** `(Fqt,2,9)` decided `= 2^{24} − u(2,9) = 16,777,216 − 103,168 = 16,674,048` ✓ and `(Fqt,27,2)` decided `= 27³ − 729 = 18,954` ✓, both matching the preregistered values exactly.
- **The `(Fqt,2,9)` drain / HEX3 tie:** `u(2,9) = 103,168 = 206,336/q` ✓.
- **LEMMA HM3-4's bracket**, two independent ways: the generating function `A₁/(1−A₁) = (q−1)q³x/(1−q⁴x)` ✓ and the direct composition sum `q^{3m}(q−1)Σ_r C(m−1,r−1)(q−1)^{r−1} = (q−1)q^{4m−1}` ✓.
- **The `A^{(j)}` column** = the `A` column × `(q−1)q^{−j}` at all four rows ✓.
- **The four block densities sum to `q^{−2}`** ✓ — exact, at every `q = 2..39`.
- **The α-amplifier** `1 + (q−1)/(q⁶−q) = (q⁶−1)/(q⁶−q)` ✓.
- **`Σ_τ R_τ = 1` and `E[#roots] = q/(q+1)`** in exact rational arithmetic at all `q = 2..39` ✓; both printed anchor tuples reproduce exactly ✓.
- **`r(N) ≤ (N+2)q^{2N}`** re-derived from the displayed ingredients (`(1 + (N−1)/2 + N/2) = N + ½`) and re-tested in exact integer arithmetic for `q ∈ {2,3,4,5,7,8,9,11,13,27}`, `N = 2..59` — holds everywhere, worst ratio **0.4578** ✓.
- **The `[r2]` m1 exponent pin:** `ℓ(B2-RAM(0,1,1;u=3)) = 13`, `2^{27−13} = 16,384` ✓, and the two instance keys at `ℓ = 14` give `8,192 + 8,192 = 16,384` ✓.
- **The tier-II template:** `(q−1)q^{4m−1} × (q−1)q^{3(N−3m)−2h−2} = (q−1)²q^{3N−5m−2h−3}` ✓.
- **The dictionary's shear arithmetic** against HM3-1(iii)'s valuation identity `v(B₀-raw) = 3m + v(A₀-block)` ✓ at every row.
- **LEMMA HM3-2's three shear amounts** `+3k`, `+k`, `+2k` = the height shear `(3−j)k` evaluated at `j = 0, 2, 1` ✓.
- **ANNEX B's five census polynomials** ✓, plus a joint-exhaustiveness cross-check: the three cubic censuses sum to the direct count of monic separable cubics with nonzero constant at `q = 2, 3, 5` (`3`, `14`, `84`) ✓.
- **ANNEX B's counts:** `4+2+2+3 = 11`, `11+11+24 = 46`, `12·2 = 24`, `46+4+3 = 53`, and the schema total `7+7+12+4+3 = 33` ✓.
- **ANNEX A's and ANNEX C's counter-instance:** `F = y³+b₀` over `F₃[[t]]` has `F′ = 0`, `disc = 0` ✓; over `ℤ₃` the same shape has `disc = −27b₀² ≠ 0` ✓.
- **The extracted-block md5** binding the landed W-12 annex to HEAD's L644–656 ✓.
- **N3_CHECK's three `q = 3` predictions** `36/121`, `351/968`, `63/968` ✓ — exactly `.18`'s anchors.

**Findings — two, neither a mathematical error:**

**AF-1 — one counterfactual figure in the `[r2]` m1 bracket does not reproduce.** The bracket writes “a (3u+1)/2 aggregate reading would give `2^{27−16} = 2,048`”. Substituting `(3u+1)/2 = 5` for `u` in the aggregate exponent `6k+w+u+3` gives `6+1+5+3 = 15`, i.e. `2^{12} = 4,096`; no combination of the note's displayed formulas yields `ℓ = 16`. **Every load-bearing figure in the same bracket verifies** (the pinned `16,384`, the aggregate `ℓ = 13`, the instance `ℓ = 14`, the two `8,192` keys), and **nothing consumes the counterfactual** — it is rhetorical, showing that a wrong reading would give a visibly wrong number. Recorded because a compiler may not silently normalize a quoted figure.

**AF-2 — a compiler self-catch, recorded because rule 22 earned its cost.** This compilation's first pass through `.12` mis-collected the common-denominator numerators of the four block densities (`2 + (q−2)` was read as contributing `q` twice rather than once) and produced a spurious “does not sum to `q^{−2}`” finding. The mandatory arithmetic audit caught it on recomputation; the sum **is** exactly `q^{−2}`, at every `q = 2..39`. The false finding was removed rather than carried. Recorded in the same spirit as `spec/EFF-HEX3.md` `.43`'s self-caught roster slip: the audit's value is visible only when it catches the auditor.

**Not independently verified (recorded honestly rather than passed):** `(Fqt,3,6)`'s deep-decided `95,580` and its four spot values; the `116` aggregate families / `58` B-composites of PE2's fresh route; the `2,610` PARI σ-reads of PE4's member factory. All require the per-key predictor, which is inside the sealed runner and outside this compilation's reach.

### 7.2 Fidelity audit

- **Every CANONICAL STATEMENT is a verbatim quotation or explicitly marked `[ASSEMBLED]`.** Two `[ASSEMBLED]` statements appear (`.13`, `.52`), each with its components separately verified.
- **No quantifier, index, inequality direction, exponent, valuation, depth, tier, or family count was altered anywhere.** The two places quantifiers are discussed as *wrong* (`.14`, `.28`) are the note's own corrections, quoted.
- **Truncations inside quotations: two**, at `.55` and `.59`, each marked with an explicit ellipsis and an inline note saying what was elided (arc chronology quoted in full elsewhere) and where.
- **Terminal punctuation and `∎` marks preserved as written.** The note's strikethrough is reproduced, since here it marks supersession.
- **No table was prosified.** The note's displays (`.07` raw-key alphabet, `.09` dictionary, `.12` block laws, `.17` density table, `.39` roster, `.69` censuses and counts) are each emitted **twice** — verbatim as the source display, then as a `[TABLE]` transcription — per rule 14's spirit. **Rule 14's letter is not triggered:** the note contains no fixed-width ASCII table inside a code fence. Checked, not skipped.
- **All 29 commit hashes, 3 valued md5 pins, and 9 artifact filenames verified** (§4.5). Zero failures. Two disclosed gaps: one `UNPINNED-VALUE` (the seven HM3-PIN hashes) and one `UNPINNED` (the /tmp prototype).
- **44 external designations grep-verified with counts recorded inline** (§4.1–4.3), including one deliberate **verified zero** (`X44`, evidencing non-landing). **Three NEAR-MISS dispositions** (§4.4), **zero invented names**, **zero OPEN-CALLs arising from designations**.
- **Status and mathematics kept as distinct predicates:** the acceptance record governs grade (`.60`), the landed annex governs W-12 consumption (§5.2 RX-2), the SOL ledger governs certification (`.72`), and the hypothesis ledger governs open obligations (§5.3).
- **Every cross-note status claim checked against the target's FULL append chain (rule 10), not the pinned sentence** — which is how the LANDED W-12 annex, the NON-landed HEX3 pointer, the stale HEX3 arc display, and the superseded “awaiting sol discharge” were all found.

---

## 8. Self-audit and OPEN-CALLs

### OPEN-CALL 1 — three frozen supplier-arc displays are stale at HEAD and no append reaches them. FOR-0b (note owner).

`.17`, `.34`, `.55`, `.59` and `.62` all carry supplier-arc as-of records terminating at `[r2]` m2 (2026-08-08). Two have since moved:

- **HEX3** is displayed as “@ 0/2 post-r1 2580f12, PE2 next” and “which continue their own arcs”. At HEAD HEX3 is **ACCEPTED 2/2** (PE6 + PE7 under the charge bar) and ledger-**CERTIFIED** (`spec/EFF-HEX3.md` `.64`, `.71`).
- **This note's own** “composition grade 0/2 until the hostile arcs run” (`.56`) is superseded by its own acceptance, but `.56` is not named by any append.

The corollary's grade rule — minimum over the stack — is unchanged and correct; only the *values* are stale, and the minimum now turns on W-12's arc alone. **The compiler has applied nothing.** **Decision needed:** whether a short dated rider is owed refreshing the three supplier-arc displays and `.56`'s trailing clause, or whether the corpus convention is that as-of records freeze with their date and consumers are expected to re-read the suppliers. Every other note in queue 8b will face the same question, so this is plausibly a corpus-protocol call rather than a note-owner one.

### OPEN-CALL 2 — the landed W-12 annex freezes a stale grade inside another accepted note. FOR-0b / possibly FOR-0d.

The BOX-2 annex (`.52`) contains “(hMenu-3) is DISCHARGED at composition grade (attempt 0/2)”, and that text **landed verbatim at `W12_PROOF` L1672ff**, where no HMENU3 append can reach it. W-12's own wrapper compounds it: “DISCHARGED at composition grade (attempt 0/2; **HMENU3's own hostile arc has not begun**)” — doubly stale, the arc having begun and completed with a 2/2 acceptance. The wrapper's line cite to HMENU3 “lines 573–585” is stale too (HEAD: L644–656), though the md5 pin binds correctly.

**Note this is the identical shape of OPEN-CALL 2 in `spec/EFF-HEX3.md`** — the same protocol question raised by the same W-12 append mechanism on both cubic notes. **Decision needed:** whether verbatim-applied annexes freeze with their source's grade at application time (in which case both are fine and the convention should be written down), or whether dated riders are owed at W-12 refreshing both wrappers. **A single decision settles both notes**, which is why it may need Asvin rather than either note owner.

### OPEN-CALL 3 — the §S8.1 HEX3 pointer is formally outstanding but substantively obviated. FOR-0b.

`.53`'s pointer block has count **0** at HEX3 (`grep -cF 'HEX3 S8.2 pointer'`), so by the protocol it is an unapplied offer. But its content — that HEX3 §S8.2 item 1's work order is executed and HEX3-BOX-1 is off W-12.D's critical path — **arrived at HEX3 by an independently authored route**: HEX3's own Correction A drops the certification lemma from that very ingredient list, citing HM3.A and quoting HMENU3 §S5.4 verbatim (`spec/EFF-HEX3.md` `.65`). **The compiler has recorded the offer as NOT LANDED and its content as present-by-another-route, and has declared neither.** **Decision needed:** whether the corpus treats an offer as discharged when the target independently authors an equivalent correction, or whether the pointer block is still owed. The DAG edge exists either way; what is undecided is whether an obligation is open.

### Recorded source defects and reading hazards (flagged, not silently repaired)

1. **`.05` / N-7: the “edits neither W12_PROOF nor HEX3_PROOF” fence is stale for the W-12 leg.** The annex landed (verified, md5-exact). Tagged `STALE-SELF-DESCRIPTION`.
2. **`.16`, `.34`, `.55`, `.56`, `.59`, `.62`: the “0/2” grade vocabulary is stale in six places.** The acceptance record reaches most by supersession; `.56`'s trailing clause is reached by none.
3. **`.72`: “awaiting sol discharge (cert3)” is superseded** by SOL ledger row 26 (**CERTIFIED**, discharged 2/2 at D3f). Verified.
4. **`.54` item 1: “Next hostile work: PE arcs (this note, HEX3), W-12 PE2” is stale on all three counts.**
5. **AF-1: one counterfactual figure (`2,048`) in the `[r2]` m1 bracket does not follow from the displayed formulas.** Nothing consumes it.
6. **`.50`: P-10's falsifier map has a structurally blind branch.** Its ORACLE branch names “the leaf table/Ore step” as the refutation target — precisely the step ANNEX A later corrects — but the oracle runs only in mixed characteristic, where the defect cannot appear (`.65`). The map could not have caught its own most consequential case, and this was disclosed only afterwards.
7. **`.18`: the EXPLORATORY `R_τ = q³·β₃(τ)` observation is fenced and must stay fenced.** `.31` proves `q³·T_τ = β₃(τ)` for the **TRP** contribution only; `R_τ` additionally carries SEP and DBL mass. A consumer must not promote the observation to the proved identity.
8. **`.42`: `(Fqt,3,6)`'s deep-decided figure is not independently verifiable** from the note's closed forms; it rides the sealed predictor.
9. **`.38`/FREEZE-3: seven md5 pins are asserted without displayed values** (`UNPINNED-VALUE`), unlike HEX3, which prints its four. A reader cannot check P-1 from the note's text alone.
10. **§5.4 / HYP.138: N3_CHECK's §6d reconciliation is OPEN and touches this note's (A2) leg**, since (A2) consumes HEX3.A. HMENU3's text predates it and says nothing about it; recorded so the (A2) leg is not cited as beyond question.

### Exhaustive residual judgment list

There are no other unresolved HMENU3 mathematical or scope judgments. HM3-BOX-1 (`.33`, inherited open), the `n ≥ 4` fence (`.36`), the mixed-characteristic oracle limit (`.35`, `.65`), the fit disclosure (`.40`), and the evidence-class split (`.38`) are the note's own displayed standing fences, not compiler ambiguities; the stale grade vocabulary, the landed annex's frozen grade, the unapplied pointer, and the counterfactual figure are classified above as bookkeeping. The three OPEN-CALLs are the complete list of judgments the compiler could not make from the text.

### Compilation summary

- **72 statement units** across the frozen post-r2 body (`.01`–`.59`), the acceptance record (`.60`–`.62`), ANNEX A (`.63`–`.65`), the E7 adjudication (`.66`), ANNEX B (`.67`–`.70`), ANNEX C (`.71`) and the provenance record (`.72`).
- **Queue charge discharged:** the frozen **L216–219** sentence is compiled at `.14` with its governing corrected reading, its three-layer chain, and full annex provenance verified on both sides (ANNEX A's cite and W-12's independently authored `[r5]` NOTICE name the same line range and quote the same clause). The **“33-family”** headline is compiled at `.62` with ANNEX B's withdrawal and both arithmetics reconstructed (33 shape schemas; **53** formal (A1) families).
- **44 external designations grep-verified**, 3 NEAR-MISS dispositions, 1 deliberate verified zero, 0 invented names, 0 designation OPEN-CALLs.
- **29 commit hashes + 3 valued md5 pins + 9 artifacts verified; zero failures** — including the cross-note extracted-block pin `4eb3bacc…`, which binds the landed W-12 annex to HEAD's own bytes at L644–656.
- **8 reverse-XREF consumer edges emitted and verified**, including one LANDED-both-directions edge (W-12), one verified NON-landing (HEX3's pointer), and one that supersedes the note's own status claim (the SOL ledger).
- **One SERIES** (the five-member ARC series `.01` → `.34` → `.59` → `.60` → `.72`), **thirteen supersession chains** (C-1…C-13, one of them landing on an annex rather than the body), and **six distinct SUPERSESSION KINDs** used.
- **Arithmetic audit: every recomputable number reproduced exactly**, including all five `R_τ` and `Σ = 1` at 38 values of `q`, LEMMA HM3-4's bracket by two independent routes, ANNEX B's five census polynomials with a joint-exhaustiveness cross-check, all four tooth counts, the 183,387 check total, and the 38-row HEX3TIE intersection. Two findings, neither a mathematical error, one of them a compiler self-catch.
- **The battery is fully consumed:** 9 families + 4 teeth, zero orphans; 44 of 72 units guarded, the 28 unguarded ones classified (4 PROOF-ONLY, 1 inherited open obligation, 10 preregistrations, 13 records covered by §4/§5).
- **Honest headline for a chapter cut:** every one of this note's five post-composition defects was found by an audit, not by a tooth — and the two that mattered most (a false quantifier in a theorem statement, and a correction that misdescribed itself) were found by two *different* decorrelated readers, one of them the supplier's own hostile arc.

EFF-HMENU3 COMPILED: 72 statements / 44 xrefs verified / 3 open calls
