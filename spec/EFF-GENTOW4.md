# EFF-GENTOW4 — CANONICAL EFFECTIVE SPECIFICATION v2 (full compilation)

**COMPILED-BY: opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). CODEX CROSS-READ OWED (post-reset).**

## 1. Header

**Source note:** `lean/notes/openmath/GENTOW4_PROOF_2026-08-09.md` (1,088 lines / 61,780 bytes).

**HEAD blob hash:** `aa74689d5769233c4bb70712ba5a9ac792cc5381` (fresh `git hash-object`; last touched by commit `73b93fd0`).

**Compilation context:** Stage 0a; template `spec/EFF_TEMPLATE_v2.md` AT HEAD (rules 1–28). IDs `EFF.GENTOW4.<nn>`, contiguous, in effective-text order.

**GENRE: TAG-SPARSE ASCII PROSE PROOF + SEALED BATTERY + r1 ROUND + TWO MINORS-ONLY FOLDS + ONE POST-ACCEPTANCE ANNEX.** `grep -c '\tag{'` = **0**. Three unit populations (v3 rule 19): **preregistrations** (P-1…P-7 + T-1…T-6, sealed at `2aa5b16`), **run-records** (S6-VERDICT plus four fresh routes), **proof units** (S2–S5).

**Charged emphasis (queue brief):** this entry compiles **the m-A rider** (`.51`) and **GENTOW4-BOX-1/-2/-4 exactly as left** (`.36`, `.37`, `.39`), cross-checked against ledger row **HYP.144**.

### FREEZE PREDICATES (v3 rule 21 — five text pins, **all reconciled**; one deliberately NOT a HEAD prefix)

`[TABLE — compiler ledger]`

| # | Predicate | Stated | Compile-time verification |
|---:|---|---|---|
| F-1 | S8.4: “Body state before this round: md5 5272bb855a4cbd6f445aaf18a47b2bb3 (31,014 bytes) = the PE1 target (note last touched c43505d …)” | md5 + **byte count** + commit | **`git cat-file -p c43505d:<file> \| md5sum` = `5272bb855a4cbd6f445aaf18a47b2bb3`, and `git cat-file -s` = 31014** ✓ — **both** quantities |
| F-2 | post-PE3: “pre-fold body md5 eeb505576d990b1409f826acf54159ca (945 lines) = the rider state @ 6e1a0f8c, the exact text passPE3 verified” | md5 + line count | **NOT a HEAD prefix — correctly so.** The two fold brackets were inserted at L423 (`+44/−0`), so the 945-line rider text is not an initial segment of HEAD. **The arithmetic reconciles exactly: 945 + 44 = 989** ✓ |
| F-3 | same: “prefix through the first insertion, L423, byte-identical, md5 57fbeb69” | md5 + line number | **lines 1–423 hash to `57fbeb69…`** ✓ — at exactly the stated line |
| F-4 | same: “post-fold body md5 f96e23d01b194c49a04e513eda3cf3e0 (989 lines)” | md5 + lines | **lines 1–989 → `f96e23d01b194c49a04e513eda3cf3e0`** ✓ |
| F-5 | TOWERRAT2-C annex: “pre-append full-file md5 bf7e60d640f36365dac83979d1b6ea63 (1037 lines)” | md5 + lines | **lines 1–1037 → `bf7e60d640f36365dac83979d1b6ea63`** ✓ |

**Eleven stated quantities; ten reproduce directly and the eleventh (F-2) reconciles through the disclosed `+44/−0` insertion.** F-2 is the queue's only freeze pin that is deliberately not a prefix, and the note supplies exactly the data needed to reconcile it — an unusually careful record.

**Instrument freeze:** “Sealed artifacts BYTE-FROZEN: the four S8.4 md5s … re-verified before and after this fold”. **All four match**, plus the two PE2-fresh hashes (§3.2).

### Effective-text rule (DERIVED)

**(i) r1 was applied as bracketed IN-BODY insertions with a ten-site manifest** (S8.4), “checkable as `git diff d7ddf2e..HEAD` on this file”. **(ii) Two of those sites were in-place REWRITES, not insertions**, and the m-C rider says so (`.53`): the S2 count word and the S4 parenthetical, “both originals preserved inside their [GT4-r1] brackets”. **(iii) The post-PE2 and post-PE3 folds are minors-only riders, not rounds** — “No repair round owed; none of the five moves a conclusion”, and “Counter HOLDS at 1/2 (a rider is not a pass)”. **(iv) After PE3 the note is frozen**: “**THE NOTE IS FROZEN AT THIS RECORD: dated appends and dated brackets only; statement displays and sealed artifacts stay byte-untouched.**” **(v) The TOWERRAT2-C annex is a pure dated append superseding one parenthetical.**

**EFFECTIVE TEXT = the note as written (r1 brackets landed, two in-place rewrites disclosed), READ AS RIDERED by the five post-PE2 minors and the two post-PE3 minors, and AS SUPERSEDED by the TOWERRAT2-C annex at one parenthetical.**

### Supersession CHAINS (v3 rule 25 — TERMINALs marked)

`[TABLE]`

| Chain | Layers | TERMINAL |
|---|---|---|
| **CHAIN-GAUGE** | composed S0 display = gauge-naive `chat_t` → **[GT4-r1] S0 pin** (corrected `chat_t := lift(c_t·eta^{W(t)})`), with 4.1(c)/S3 re-pointed at the r1-RESTATED HETOW-1/2 and a supply audit | **[GT4-r1]** (`.05`, `.46`) |
| **CHAIN-COUNT (the S2 fullness count)** | composed “exactly THREE places” → **[GT4-r1] m-1**: recounted as **TWO lemma-level places spanning FIVE table rows** → **m-B rider**: reconciled with S3(iii)'s “three fullness rows” — three replaced by 4.1(a)(b)+(ii), the other two discharged by 4.1(d)'s peels; “No row is undischarged; the counts describe different partitions of the same five rows” | **m-B** (`.52`) |
| **CHAIN-SUPPLY (the S8.1 two-item routing)** | r1: HE6R1-2 **and** HE7-13′ both routed through HE7-12(c)'s transport → **m-A rider**: the second item is **MISATTRIBUTED** — HE7-13′ is **not** on HE7-12(c)'s displayed list (ANNEX F-1 postdates it); its supply is by its **own statement form** at `W = 0` | **m-A** (`.51`) |
| **CHAIN-MANIFEST** | S8.4: “insertions with the composed text standing” → **m-C**: imprecise; `git diff d7ddf2e..eb526a0d` = **265 insertions / 14 deletions**, TWO sites corrected in place | **m-C** (`.53`) |
| **CHAIN-93 (the adopted FR-M check count)** | r1 adopts “93 checks” → **m-D**: the count is **PADDED** — an else-branch check tests its own branch condition; **exactly 14 vacuous, 79 falsifiable** | **m-D** (`.54`) |
| **CHAIN-GRADES (BOX-4's supplier stack)** | composed: HETOW 0/2, GENTOW-1 0/2, HE6R1 0/2 → **m-E**: refreshed from the arc records — **all three ACCEPTED 2/2**; “the staleness was conservative (understated grades)” | **m-E** (`.39`, `.55`) |
| **CHAIN-MONIC (4.A(ii)'s parenthetical)** | composed: “top coefficient NOT monic — the partial-side signature” → **TOWERRAT2-C**: **FALSE as written** (the note's own witness refutes it: `C_2 = Φ′ + 4 = x²+2`, monic); display of record supplied, with the true signature `n > mu2·D2` | **TOWERRAT2-C** (`.57`) |
| **CHAIN-CG-CITE** | 4.C's pin equality cited to HE6R1-2**(b)** alone → **acceptance-fold m-i**: the citation is COMPLETED to **(b) AND (c)** — (b) alone gives an INEQUALITY at on-hull points; equality at side-INTERIOR abscissas rides (c)'s residual-scalar display | **m-i** (`.33`) |
| **CHAIN-CLASSMASS** | the adopted PE2 rows' class-degree-sum check read as `==` → **acceptance-fold m-ii**: the adopted instrument's check is **ONE-SIDED** (`ncls >= want_sum`); the sealed instrument's six checks and PE3's `ncls == want_sum` are two-sided | **m-ii** (`.50`) |

### SERIES declared (v3 rule 28)

**SERIES ARC** — `.02` (r1 header record) → `.03` (post-PE2 ARC record) → `.45`–`.49` (S8, the r1 round) → `.50`–`.55` (S9, the post-PE2 fold + the two post-PE3 fold brackets) → `.56` (acceptance 2/2) → `.57` (TOWERRAT2-C).

**SERIES MINORS-PE2** — the five folded minors in the note's own order: `.51` (m-A) → `.52` (m-B) → `.53` (m-C) → `.54` (m-D) → `.55` (m-E). Each is “RE-DERIVED from the note's own lemmas, the primary sources, and the committed artifacts, not transcribed from the report”.

**SERIES BOXES** — the four residue boxes as one ledger family, emitted per box: `.36` (BOX-1) → `.37` (BOX-2) → `.38` (BOX-3) → `.39` (BOX-4). **Ledger row `HYP.144` homes BOX-1/-2/-4 together** and is quoted at each.

### Scope split — THREE predicates

**A. Mathematical absorption / supply SET.** The charge:

> “Charge: [GENHN-TOW-1] item (4) — the inner CS event occupies only
> PART of the (J, dv(A_J))-polygon: e2f2·mu2 < mu1, because the
> polygon has other sides and/or the event side carries other
> residual classes.”

Delivered: **one bridge-repair lemma (GENTOW-4.1, four clauses), one theorem (GENTOW-4.A, five clauses), one tie lemma (GENTOW-4.2, pure-power sides only), one corollary (GENTOW-4.C)**. The note is explicit that the DECISION is not new: “Nothing about the DECISION is new: the two new proof obligations are the two full-side-dependent steps of HETOW's instantiation (repaired in S2) and the multiplicity TIE”.

**B. Append / consumption PROTOCOL scope.** Declared zero and verified:

> “**Consumption path (not executed here):** [GENHN-TOW-1] item (4)'s
> box text in GENHN_PROOF is the orchestrator's dated consumption
> update after this note's own hostile arc; GENHN_PROOF, HETOW_RECON,
> HE7_PROOF, HE6R1_RECON are byte-untouched by this unit.”

`grep -cF 'GENTOW' GENHN_PROOF_2026-08-08.md` = **0** (N1). A conditional future consumption is also named: “The GENHN.B (CS-3) partial-side rider (passPE2 F2's cure) can, after acceptance, cite THEOREM GENTOW-4.A(v) for inner-mu2 = 2 partial leaves at pure-power sides — with GENTOW4-BOX-1 named at mixed sides.” **Acceptance has now happened, so that cite is unlocked and unlanded** (OPEN-CALL 1).

**C. Inbound corrections RECEIVED — four sources:** GENHN's gauge erratum via HETOW (→ r1); this note's PE1/PE2/PE3; the **TOWERRAT2 run C** decorrelated ratification (→ `.57`); and, indirectly, HE7's ANNEX F-1 dating, which is what makes the m-A misattribution detectable.

### Resolution rules applied

1. `[GT4-r1]` brackets are landed; the two in-place rewrites are recorded with both wordings (m-C).
2. Rider brackets (`[rider (post-PE2 …)]`, `[acceptance fold (post-PE3) …]`) are landed at their sites; each unit carries the ridered reading in CONDITIONALITY with its KIND.
3. **Box wording is reproduced EXACTLY as left** (queue charge), and each box carries its `HYP.144` / `HYP.67`-family ledger cross-reference verbatim.
4. Numbers recomputed from committed artifacts and from the note's own displays.
5. Cited source lines in other instruments are read at compile time.

### Quotation and table discipline

Verbatim or `[ASSEMBLED]`; `…` marks truncation. ASCII preserved. Three source tables (`.09` families, the S1 worked instance block, the S6 family menu) are `[TABLE]`-flagged; the two fixed-width ASCII blocks are double-emitted per v3 rule 14.

---
