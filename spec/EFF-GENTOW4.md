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

## 2. Statement inventory

57 units, contiguous, in effective-text order. FORM on every unit.

### EFF.GENTOW4.01  [convention]

**CANONICAL STATEMENT:**

> “# GENTOW-4: PARTIAL INNER SIDES ([GENHN-TOW-1] item (4)) — the
> # partial-side tower read = the level-1 label-class BLOCK SPLIT +
> # LEMMA HE6R1-2's projection + per-block literal HE7.A instances at
> # the composed carrier, 2026-08-09”

with the status line:

> “**STATUS: COMPOSED (per-section commits; machine leg sealed-then-
> verdict, S6). Unit: GENTOW-4, BOX-CLOSURE campaign wave 22. Grade
> 0/2 (attempt; hostile arc owed).**”

**FORM:** four-line title + bold status.

**DERIVATION:** `[RECORD]` — the title states the whole architecture: block split + projection + per-block HE7.A instances.

**CONDITIONALITY:** grade → **ACCEPTED 2/2** (`.56`). The TOWERRAT2-C annex's finding C-2 explicitly rules that “the header grade lines are the frozen historical layer; the dated acceptance record above governs” — so this status line is frozen history by the note's own adjudication (`.57`).

**RESOLUTION TRACE:** lines 1–8; correction 993–1000; the C-2 ruling at 1046–1049.

**TEETH:** the machine leg is `.42`–`.44`.

---

### EFF.GENTOW4.02  [repair-round record]  *(SERIES ARC, link 1)*

**CANONICAL STATEMENT:**

> “**GT4-r1 repair round 2026-08-10 (this round): passPE1
> (GENTOW4_passPE1_report.md @ 8ae71864) returned NOT CLEAN — 1 GAP
> (F-1, the gauge seam, four sites) + 2 MINOR; counter stays 0/2.
> F-1 repaired by the dated gauge annex (S8): the corrected chat_t
> pinned at S0, 4.1(c)/S3 re-pointed at the [r1 2026-08-09]-restated
> HETOW-1/2 with the supply audit, GENTOW4-BOX-3 gains the eta-gauge
> axis ("uniform in all of these" withdrawn), the S4 remark re-scoped
> f1 = 1 -> eta = 1; FR-G/FR-M adopted as annex machine rows. m-1:
> the S2 fullness count recounted (TWO lemma-level places). m-2: T-2
> NOCG's even-p0 branch disclosed at the S6-VERDICT row. Edits
> [GT4-r1]-bracketed; sealed artifacts BYTE-FROZEN (md5s S8.4).
> Grade stays 0/2.**”

**FORM:** bold dated round record.

**DERIVATION:** `[RECORD]`; dispositions compiled at `.05` (S0 pin), `.20` (4.1(c)), `.38` (BOX-3), `.34` (S4 remark), `.47`–`.48` (FR-G/FR-M), `.49`/`.52` (m-1), `.44` (m-2).

**CONDITIONALITY:** counter superseded (`.56`). **The “four sites” of F-1 are the note's own count and are enumerated at `.46`.**

**RESOLUTION TRACE:** lines 10–21.

**TEETH:** `git cat-file -t 8ae71864` = commit ✓.

---

### EFF.GENTOW4.03  [acceptance-box]  *(SERIES ARC, link 2)*

**CANONICAL STATEMENT:**

> “**ARC (post-PE2, 2026-08-10): passPE2 (GENTOW4_passPE2_report.md
> @ 80280b66) returned CLEAN — 0 CRITICAL, 0 GAP, 5 MINOR; counter
> 0/2 -> 1/2, the arc's first clean pass. The five minors are folded
> as dated [rider (post-PE2)] brackets at their sites (S8.1 x2,
> S3(iii), S8.4, S7 BOX-4) + the S9 record — each RE-DERIVED from
> the note's own lemmas, the primary sources, and the committed
> artifacts, not transcribed from the report. Sealed artifacts stay
> BYTE-FROZEN (the four S8.4 md5s re-verified this fold). Counter
> HOLDS at 1/2; a rider is not a pass. PE3 next.**”

**FORM:** bold dated ARC record.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** **“a rider is not a pass”** — the same non-double-counting rule as HETOW/GENTOW1/GENTOW3. **The five rider SITES are named here**, which is what makes the SERIES MINORS-PE2 mechanically reconstructible.

**RESOLUTION TRACE:** lines 23–31.

**TEETH:** `git cat-file -t 80280b66` = commit ✓; all four S8.4 md5s re-verified at compile time (§3.2) ✓.

---

### EFF.GENTOW4.04  [fence]

**CANONICAL STATEMENT:** the charge and import inventory, source lines 33–45. The imports, verbatim:

> “Consumes (never edits): GENHN_PROOF S8 [r2] annex
> (LEMMA GENHN-T(b)': composed carrier (i), slot lemma GENHN-2' (ii))
> + the S3.2 [r1] node-floor erratum; HETOW_RECON (bridges HETOW-1/2,
> THEOREM HETOW.A's instantiation table); HE6R1_RECON (LEMMA HE6R1-2
> block projection + RIDER HE6R1-2R, LEMMA HE6R1-3 peel); HE7_PROOF
> (THEOREM HE7.A/C/D, LEMMAS HE7-5/6/9/10/11/12/13, ANNEX-LEMMA
> HE7-13'); HE6_PROOF (LEMMA HE6-3, LEMMA HE6-4, THEOREM HE6.A);
> GENTOW1_PROOF (E2, weight grammar, notation); GENHN_passPE2_report
> (the PE2-P witness). Frozen-file discipline: none of those notes is
> edited here.”

**FORM:** paragraph.

**DERIVATION:** `[RECORD]` — **the widest import set in this queue: six proof notes plus a report.**

**CONDITIONALITY:** **ANNEX-LEMMA HE7-13′ is in this list, and the m-A rider later shows its SUPPLY ROUTE was misattributed** (`.51`) — the import is real, the routing was wrong.

**RESOLUTION TRACE:** lines 33–45.

**TEETH:** all seven cited sources exist. N1 verifies the no-edit fence for GENHN.

---

### EFF.GENTOW4.05  [convention]  *(CHAIN-GAUGE — TERMINAL, in-body site)*

**CANONICAL STATEMENT:** the S0 setting with its gauge pin, verbatim (abridged at the setting's front, quoted in full at the pin):

> “PARTIAL:
> e2f2·mu2 < mu1. Composed key (same formula as T(b)'):
> Phi2 := Phi'^{e2f2} − Sum_{t<f2} chat_t·nhat(u2(f2−t))·Phi'^{e2t},
> deg D2 = D'e2f2; dv2 := e1e2·v; T2 = E2 := e2f2·u2 (GENTOW-1 S0).
> [GT4-r1 GAUGE PIN (S8; per erratum 59c1966 + HETOW [r1]):
>
>     chat_t := lift(c_t·eta^{W(t)}),
>     W(t)   := floor((f2−t)·i(u2)/e1)
>
> — the WRAP-CORRECTED lifts … The composed-at display's plain
> lifts chat_t = lift(c_t) are the GAUGE-NAIVE form — a DIFFERENT
> polynomial whenever some c_t·(eta^{W(t)} − 1) != 0; at eta = 1, and
> at any frame where every c_t·(eta^{W(t)} − 1) = 0 (automatic at
> f2 = 1, where W(0) = floor(i(u2)/e1) = 0), corrected = naive. This
> pin governs every Phi2 of S2–S5.]”

**FORM:** setting paragraph with a displayed dated pin.

**DERIVATION:** `[IMPORTED]` from GENHN's erratum + HETOW [r1].

**CONDITIONALITY:** SUPERSESSION KIND: **replacement**. **The f2 = 1 automatic-coincidence observation is this note's own addition** and is not in the sibling notes' pins: at f2 = 1, `W(0) = ⌊i(u2)/e1⌋ = 0` since `i(·) < e1`, so corrected = naive at every f2 = 1 frame. That is why three of the five battery families are gauge-blind for a second, independent reason.

**RESOLUTION TRACE:** lines 57–73; annex 728–792.

**TEETH:** **ARITHMETIC AUDIT: `W(0) = ⌊i(u2)/e1⌋` with `0 ≤ i(u2) < e1` gives `W(0) = 0` ✓** — the f2 = 1 claim is exact. The formula `W(t) = ⌊(f₂−t)i(u₂)/e₁⌋` matches HETOW, GENTOW1 and GENTOW3 verbatim — **a four-way cross-entry agreement**.

---

### EFF.GENTOW4.06  [scope record]

**CANONICAL STATEMENT:**

> “THE WITNESS (PE2-P, constructed by GENHN's passPE2 verifier; the
> box's protected instance): n = 10, genre (2,1,5) over Q_2,
> f = Phi'^5 + 4Phi'^4 + 32Phi' + 64x (Phi' = x^2 − 2). P(F) =
> (0,13)–(1,10)–(5,0): a slope-3 SIBLING side of length 1 plus a
> slope-5/2 INNER side of length 4 < mu1 = 5 carrying (T+1)^2 — an
> inner mu2 = 2 event on a partial side. The corrected T(b)'(iii)
> reader REFUSES it (the Phi2-development of f is not
> monic-of-length-mu2: deg f = 10 != mu2·D2 = 8) and no proved
> display priced its sigma (PARI: {(2,1),(4,1),(4,1)}).”

**FORM:** bold-headed witness paragraph.

**DERIVATION:** `[IMPORTED]` — the instance was constructed by another note's verifier as a counterexample to the full-side reader.

**CONDITIONALITY:** **the witness is the box's PROTECTED INSTANCE** — the thing item (4) exists to explain. That the corrected reader REFUSES it (rather than mispricing it) is the loud-failure property tooth T-1 later checks 117/117.

**RESOLUTION TRACE:** lines 75–83.

**TEETH:** **ARITHMETIC AUDIT: `D' = e1f1 = 2`, `mu2·D2 = 2·(2·2·1) = 8 ≠ 10 = deg f` ✓; the inner side length `e2f2mu2 = 2·1·2 = 4 < 5 = mu1` ✓ — PARTIAL confirmed from the genre data alone.** The σ is reproduced by the sealed battery at PE2P-0 (`.43` P-2).

---

### EFF.GENTOW4.07  [scope record]

**CANONICAL STATEMENT:** the answer's shape, verbatim:

> “THE ANSWER'S SHAPE (derived in S2–S4, verified at PE2-P in S5): a
> partial side means f_S — the block factor of the inner label — is a
> PROPER factor of f. The read is:
>
> 1. f splits along its level-1 LABEL CLASSES (kappa, r) — the
>    HE7-13' bouquet mechanism, here at the tower entry, with the
>    block factors supplied by LEMMA HE7-6 at each label datum;
> 2. each class is read through ITS OWN composed key by LEMMA
>    HE6R1-2 (block projection — proved in HE6R1_RECON for EXACTLY
>    this proper-block configuration …): the slope-> T2 part of
>    P2(f) IS P2(f_S) translated by the constant c_g = dv2(g(xi)) of
>    the complementary factor g = f/f_S, with the same slopes,
>    lengths, and residual factors up to a K2^x scalar;
> 3. THEOREM HE7.A (+ HE7.C/D, ANNEX HE7-13') then decides each
>    block at the composed carrier exactly as at HETOW's full sides …”

with the novelty fence:

> “Nothing about the DECISION is new: the two new proof obligations
> are the two full-side-dependent steps of HETOW's instantiation
> (repaired in S2) and the multiplicity TIE mu2* = mu2 …
> (proved at pure-power sides in S3; honestly boxed at mixed sides, S7).”

**FORM:** bold-headed three-step architecture + a novelty fence.

**DERIVATION:** `[RECORD]` of the proof plan, each step routed to an existing lemma.

**CONDITIONALITY:** **the novelty fence is the note's own scope discipline** and it is honoured: the two new obligations are exactly `.19`–`.22` (the bridge repairs) and `.30`/`.31` (the tie, proved then boxed).

**RESOLUTION TRACE:** lines 85–108.

**TEETH:** the architecture's three steps are the three headline predictions P-1/P-2/P-4.

---

### EFF.GENTOW4.08  [run-record]  `[TABLE]`

**CANONICAL STATEMENT:** the worked PE2-P instance. **Source display, verbatim** (v3 rule 14):

>     “f = Phi'^5 + 4Phi'^4 + 32Phi' + 64x,  Phi2 = Phi'^2 − 4x,
>     E2 = T2 = 10, dv2 = 4v.
>     Phi2-development of f:  C2 = x^2 + 2 = Phi' + 4,
>       C1 = 8x^3 + 16x + 16 = 8xPhi' + 32x + 16,  C0 = 128x^2 + 128x − 128.
>     Composed pins (slot-min, GENHN-2'): p0 = 28, p1 = 16, p2 = 5.
>     Polygon (0,28)–(1,16)–(2,5): slopes 12, 11 — BOTH > T2 = 10,
>     initial >T2 segment = the whole hull, right endpoint (2, 5):
>       mu2* = 2 = mu2 (the tie),  c_g = 5.
>     Translated block pins p^S = (23, 11, 0): floors (mu2−j)E2 + 1 =
>     (21, 11) both cleared, j = 1 EXACTLY at the node floor.
>     Two sides, distinct integer slopes -> composed-2SIDED ->
>     {(e1e2, f1f2)} x2 = {(4,1),(4,1)}.  Sibling side (0,13)–(1,10):
>     slope 3, length 1, residual linear -> (e1·1, f1·1) = (2,1).
>     PARI (both routes): sigma(f) = {(2,1),(4,1),(4,1)}  — EXACT”

`[TABLE]` — transcription with the compiler's independent recomputation:

| quantity | note | recomputed | ✓ |
|---|---|---|:-:|
| `E2 = T2 = e2f2u2` | 10 | `2·1·5 = 10` | ✓ |
| `dv2 = e1e2·v` | 4v | `2·2 = 4` | ✓ |
| polygon slopes | 12, 11 | `28−16 = 12`, `16−5 = 11` | ✓ |
| both `> T2` | yes | `12 > 10`, `11 > 10` | ✓ |
| `c_g` = height at abscissa `mu2*` | 5 | `p_2 = 5` | ✓ |
| block pins `p_j − c_g` | (23, 11, 0) | `28−5 = 23`, `16−5 = 11`, `5−5 = 0` | ✓ |
| floors `(mu2−j)E2 + 1` | (21, 11) | `2·10+1 = 21`, `1·10+1 = 11` | ✓ |
| j = 1 exact at the floor | yes | `11 = 11` | ✓ |
| `C_2 = x²+2 = Φ′+4` | — | `Φ′ + 4 = x²−2+4 = x²+2` | ✓ |
| `C_1 = 8x³+16x+16 = 8xΦ′+32x+16` | — | `8x(x²−2) + 32x + 16 = 8x³−16x+32x+16 = 8x³+16x+16` | ✓ |

**FORM:** fixed-width ASCII block (source) → table.

**DERIVATION:** `[RUN]` + hand derivation; re-derived at `.41`.

**CONDITIONALITY:** none. **This single instance exercises every mechanism of the note**: partial side, block split, c_g-translation, the tie, the floors, the trichotomy, and the sibling class.

**TEETH:** **every one of the ten quantities recomputes**, including both polynomial identities. The `C_2 = x²+2` computation is also what refutes the “top coefficient NOT monic” parenthetical (`.57`) — **the note's own S1 table contains the counterexample to its own S3 gloss**, and the annex says so.

---

### EFF.GENTOW4.09  [derivation]

**CANONICAL STATEMENT:**

> “Read off the table (then proved): (i) the >T2 initial segment of
> P2(f) has length exactly mu2 and right-endpoint height c_g — the
> block polygon rides ON f's polygon, translated; (ii) c_g here is
> ODD, so the f-level pin parity is WRONG for the block (p0 = 28
> even, p0^S = 23 odd): any reader that skips the c_g-translation
> misprices RAM — the load-bearing tooth T-NOCG; (iii) sibling
> factors sit at dv2(Phi2) = E2 (steeper flank) or < E2 (shallower
> flank), class factors strictly above E2: the field floor is the
> machine-visible class separator.”

**FORM:** bold-headed three-item reading.

**DERIVATION:** examples-first.

**CONDITIONALITY:** item (ii) identifies the note's **load-bearing seam**: the parity flip. It is guarded by tooth T-2 NOCG, which fires 49 times (`.44`).

**RESOLUTION TRACE:** lines 135–143.

**TEETH:** **ARITHMETIC AUDIT of the parity claim: `p0 = 28` is even, `p0^S = 23` is odd ✓** — the parity genuinely flips, so an f-level parity reader is wrong on this very witness.

---
### EFF.GENTOW4.10  [changes-record]  *(CHAIN-COUNT, link 2)*

**CANONICAL STATEMENT:** the S2 fullness audit with its recount, verbatim:

> “HETOW's instantiation map (HETOW_RECON S1, rows verbatim) consumes
> fullness in exactly TWO places [GT4-r1 (m-1): "THREE" recounted
> from the S1 table — two lemma-level places spanning FIVE table
> rows: HETOW-1's r-row (one row), and HETOW-3 across four rows (the
> Psi ∤ f_S peel convention, the label row, the f_S/mu2 row, the
> level-1 Phi' ∤ f frame row); the ladder row's "equality at full
> side" annotation is commentary, not a consumed hypothesis — its
> partial-side analogue is (ii)'s mu2* = deg f_S/D2]: HETOW-1(a)'s
> psi2(0) != 0 …, HETOW-3 wholesale (f_S = f), and nothing else —
> HETOW-2's proof
> consumes only Phi2's own construction, DEFINITION HE6-1's
> deg/dv/residue interfaces, and the node floor u2 > e2D'h, never the
> side's length (checked line by line at this unit …).”

with the r1 re-check at the restated bridge:

> “[GT4-r1: the audit
> was performed on the pre-[r1] HETOW-2; re-checked this round at
> the RESTATED HETOW-2 … — its proof
> adds the S2 wrap-cocycle preamble … and the (LIFT)-slot coefficient form, both
> side-blind, and its carry accounting (F-2) is stated per slot with
> no side-length input: the audit conclusion stands at the corrected
> key.]”

**FORM:** paragraph with two dated brackets (one an in-place word rewrite).

**DERIVATION:** a line-by-line dependency audit of another note's proof, performed twice (pre- and post-restatement).

**CONDITIONALITY:** SUPERSESSION KIND: **counter re-reading** (THREE → TWO, in place, original preserved in the bracket per m-C). Reconciled with S3(iii)'s “three fullness rows” by **m-B** (`.52`): different partitions of the same five rows, none undischarged.

**RESOLUTION TRACE:** lines 147–168; reconciliation 353–365; m-C's record 891–905.

**TEETH:** the audit's target is `EFF.HETOW.19`'s carry paragraph, which this queue independently compiled as “stated per slot” — **the side-blindness claim checks out against the HETOW entry's own reading of the same proof.**

---

### EFF.GENTOW4.11  [lemma]

**CANONICAL STATEMENT:**

> “> **LEMMA GENTOW-4.1.** In the S0 setting (partial side):
> > (a) [floor, every side] every side of P(F) has dv-slope > D'h;
> > in particular kappa2 > D'h and every sibling slope qualifies as a
> > level-2 datum slope.”

**FORM:** lemma clause (a).

**DERIVATION:** `.15`(a) — “the [r1] node-floor erratum's own derivation … which is side-blind”.

**CONDITIONALITY:** none; the derivation is quoted as side-blind, which is exactly what the partial-side setting needs.

**RESOLUTION TRACE:** statement lines 170–173; proof 196–201.

**TEETH:** consumed by every sibling class in `.26`(iv).

---

### EFF.GENTOW4.12  [lemma]

**CANONICAL STATEMENT:**

> “> (b) [psi2(0) != 0] the residual of EVERY side of P(F) has
> > nonzero constant term; in particular psi2(0) != 0, and HETOW-1
> > holds verbatim with this in place of its full-side endpoint step:
> > (kappa2, rtilde) is a level-2 datum of DEFINITION HE7-1 over the
> > outer frame, and the tower-node locus is its level-2 point set.”

**FORM:** lemma clause (b).

**DERIVATION:** `.15`(b) — a vertex-attainment argument: “BOTH endpoints of every side of P(F) are vertices of the polygon, hence ATTAINED pins (a vertex of a lower hull of an integer point set is a point of the set …)”.

**CONDITIONALITY:** **this clause REPLACES HETOW-1(a)'s full-side endpoint step** — the first of the two new obligations. The REMARK at `.16` fences what it does not claim.

**RESOLUTION TRACE:** statement lines 174–178; proof 201–213.

**TEETH:** consumed by the label vocabulary of `.24` and by 4.1(b)'s use in S3(iii).

---

### EFF.GENTOW4.13  [lemma]

**CANONICAL STATEMENT:**

> “> (c) [key bridge] HETOW-2
> > [GT4-r1: = the [r1 2026-08-09]-RESTATED HETOW-2, stated at the
> > WRAP-CORRECTED key of the S0 pin — the gauge-naive form was
> > refuted at eta != 1, f2 = 2 frames (S8; FR-G measured the
> > discrepancy AT dv2 = T2 exactly); the restated display supplies
> > Psi-membership with w = 0 under the (LIFT)-slot form at any f1]
> > holds verbatim: Phi2 = Psi_{kappa2,rtilde} − w with w = 0 or
> > dv2(w) > T2, so by LEMMA HE7-12 the §S5 package, THEOREM
> > HE7.A(1)(2), the refine package (HE7-12/13, HE7-8), the §S1
> > CONVENTION with LEMMA HE6R1-3's peel, ANNEX-LEMMA HE7-13', and
> > LEMMA HE6R1-2 with RIDER HE6R1-2R all hold with key Phi2.”

**FORM:** lemma clause (c) with a dated re-pointing bracket.

**DERIVATION:** the HETOW-2 audit of `.10` plus the transported package.

**CONDITIONALITY:** **the SUPPLY ROUTE of two items on this list is audited at `.46` and one is corrected by m-A** (`.51`): LEMMA HE6R1-2 + RIDER is correctly routed through HE7-12(c)'s displayed list; **ANNEX HE7-13′ is NOT**, and is supplied instead by its own statement form at `W = 0`. **The clause's conclusion is unchanged.** Cross-entry: the disjunct quoted here (`w = 0 or dv2(w) > T2`) is exactly the one T2's r12 cites as “`GENTOW-4-1` clause (c) gives that same disjunct at the partial tower” (`EFF.HETOW.43`'s consumer trace).

**RESOLUTION TRACE:** statement lines 178–188; audit 749–777; m-A 946–954.

**TEETH:** FR-G measures the naive-key failure at `dv2 = T2` exactly (`.47`).

---

### EFF.GENTOW4.14  [lemma]

**CANONICAL STATEMENT:**

> “> (d) [frame peels] if Phi' | f then Phi' EXACTLY divides f
> > (disc != 0), contributes one irreducible factor with
> > (e, f) = (e1, f1), and the read continues on f/Phi' (whose
> > development is the J-shift); if Phi2 | f likewise via LEMMA
> > HE6R1-3 at key Phi2 ((c)), contributing (e1e2, f1f2) and
> > dropping mu2 by 1. So assume Phi' ∤ f, Phi2 ∤ f below.”

**FORM:** lemma clause (d).

**DERIVATION:** `.15`(d).

**CONDITIONALITY:** **(d)'s peels are what discharge the two remaining fullness rows** per m-B (`.52`) — “in force at this theorem by its preamble ("after the S2 peels")”.

**RESOLUTION TRACE:** statement lines 189–194; proof 220–223.

**TEETH:** T-5 WRONGKEY's “incl. the key | f peel corner” exercises it (`.44`).

---

### EFF.GENTOW4.15  [derivation]

**CANONICAL STATEMENT:** the 4.1 proof, `[ASSEMBLED]` from lines 196–223. Clause (b)'s vertex argument, verbatim (the load-bearing one):

> “(b) BOTH endpoints of every side of P(F) are
> vertices of the polygon, hence ATTAINED pins (a vertex of a
> lower hull of an integer point set is a point of the set; the
> global endpoints (0, dv(A_0)) with A_0 != 0 by (d)'s reduction,
> and (mu1, 0) with C_{mu1} = 1, attain too). A side's residual
> R_kappa has constant term = the (twist-normalized) residue of
> the left-endpoint pin — attained, hence nonzero. psi2^{mu2}
> | R_{kappa2} and R_{kappa2}(0) != 0 force psi2(0) != 0. The rest
> of HETOW-1's proof is untouched: its clause (b) reads the locus
> definitions …, and its clause (a)'s
> minimal-polynomial computation consumes psi2 irreducible,
> psi2(0) != 0, and the residual division at a root of Phi2 —
> none of which mention the side length.”

**FORM:** four-clause proof.

**DERIVATION:** as quoted; (b) is a convexity/attainment fact plus a divisibility step.

**CONDITIONALITY:** **the proof also audits what it does NOT disturb in HETOW-1** — a dependency check, not just a substitution.

**RESOLUTION TRACE:** lines 196–223.

**TEETH:** the vertex-attainment mechanism is re-used at `.33` (m-i's equality-at-vertices argument), where the note calls it “4.1(b)'s mechanism at the level-2 pin set”.

---

### EFF.GENTOW4.16  [fence]

**CANONICAL STATEMENT:**

> “REMARK (what (b) does NOT claim): no statement about pins strictly
> inside a side, and no claim that A_0's residue feeds psi2 — at a
> partial side the left endpoint of the inner side is generally an
> interior vertex (PE2-P: (1,10)), and the residual's constant term
> is read THERE.”

**FORM:** bold-headed remark.

**DERIVATION:** `[RECORD]` of a scope limit, with the witness's own geometry as the illustration.

**CONDITIONALITY:** **essential**: at a partial side the inner side's left endpoint is NOT the global left endpoint, so the full-side argument would be wrong. This remark is the difference between (b) and HETOW-1(a).

**RESOLUTION TRACE:** lines 225–229.

**TEETH:** PE2-P's hull `(0,13)–(1,10)–(5,0)` has the inner side starting at the interior vertex `(1,10)` ✓ (`.06`).

---

### EFF.GENTOW4.17  [definition]

**CANONICAL STATEMENT:** the label vocabulary, verbatim (abridged at the r1 bracket, quoted next):

> “Label vocabulary (HE7's, at the tower entry via HETOW-1's
> translation): for a side of P(F) of slope kappa = u/l (lowest
> terms) and a monic irreducible factor r of its residual R_kappa,
> the LABEL CLASS is C_{kappa,r} := the roots x0 of f with
> dv(Phi'(x0)) = kappa whose twist-normalized letter beta_{x0} is a
> root of iota(rtilde_r) … LEMMA HE6-2''/HE6-4 give: the classes partition the roots of
> f, every (kappa, r) with r | R_kappa is realized, and the label is
> a label OF f in THEOREM HE7.A's sense.”

with the r1 re-definition bracket, verbatim:

> “[GT4-r1: per the [r1]-restated HETOW-1, rtilde_r has ONE
> definition — the minimal polynomial over K of the twisted letter
> beta = eta_theta^{−Q(u)}·(root of iota(r)), explicitly
> eta^{−Q(u)·d_r}·r(eta^{Q(u)}Z); "the pi-bar-normalized twist"
> names it. Its slot-residue characterization is the restated clause
> (c), proved AT the corrected key only; what this vocabulary and
> 4.1(b) consume is the POINTWISE clause (b) … which is wrap-free … and untouched by the restatement.]”

**FORM:** definitional paragraph with a dated re-definition bracket.

**DERIVATION:** `[IMPORTED]` from the restated HETOW-1.

**CONDITIONALITY:** SUPERSESSION KIND: **replacement** of a definition's status (one definition, not two). **The consumption is POINTWISE clause (b), which is wrap-free** — so this vocabulary survives the gauge correction untouched. Cross-entry: `EFF.HETOW.15`/`.16` compile the same restatement from the source side and record clause (b)'s wrap-freeness identically.

**RESOLUTION TRACE:** lines 233–251.

**TEETH:** the class partition is HE6-2″/HE6-4, imported.

---

### EFF.GENTOW4.18  [theorem]

**CANONICAL STATEMENT:**

> “> (i) [BOUQUET AT THE ENTRY] f = Prod_{(kappa,r)} f_{kappa,r} with
> > f_{kappa,r} in O[x] monic, the block factor of C_{kappa,r}
> > (LEMMA HE7-6's argument at each datum: Galois-stability by LEMMA
> > HE7-11, integrality, division of the squarefree f); the
> > factorization is disjoint over labels and D'·l·d_r | deg
> > f_{kappa,r} (LEMMA HE7-5's forcing).”

**FORM:** theorem clause (i).

**DERIVATION:** `.23`(i) — the classes partition roots; each class is Galois-stable; HE7-6's argument runs verbatim.

**CONDITIONALITY:** rides HE7-11's equivariance being datum-general, which the proof checks: “LEMMA HE7-11's equivariance computation reads Phi', the normalizers, and iota only, so it runs at every datum of GENTOW-4.1(b)”.

**RESOLUTION TRACE:** statement lines 257–262; proof 329–332.

**TEETH:** P-1 parse gate; T-3 SIBDROP (117/117) proves the bouquet is needed — tower-class-only σ ≠ PARI on every member.

---

### EFF.GENTOW4.19  [theorem]

**CANONICAL STATEMENT:**

> “> (ii) [PROJECTION, per class — LEMMA HE6R1-2 at the composed key]
> > fix the inner class S = C_{kappa2, psi2}, f_S := f_{kappa2,psi2},
> > g := f/f_S, and let f = Sum_j C_j Phi2^j be the Phi2-development
> > OF f (length M = floor(n/D2) >= mu2, top coefficient NOT monic —
> > the partial-side signature), with pins p_j := dv2(C_j(x0)) read
> > exactly by GENHN-2' on the tower-node locus. Then dv2(g(xi)) =
> > c_g, a constant, at every level-2 point xi of (kappa2, rtilde);
> > deg f_S = D2·mu2* where mu2* := Sum_{lambda2 > T2} L_{lambda2}
> > (P2(f)); the slope-> T2 part of P2(f) is the INITIAL segment of
> > the hull of {(j, p_j)}, spans abscissas [0, mu2*], and equals
> > P2(f_S) translated UP by c_g — same breakpoints, slopes,
> > lengths; and per side the residuals of f and f_S have the same
> > degree and the same monic irreducible factors, agreeing up to
> > the K2^x scalar gamma_g (LEMMA HE6R1-2(a)(b)(c) + RIDER
> > HE6R1-2R, all available at key Phi2 by GENTOW-4.1(c)).”

**FORM:** theorem clause (ii) — the projection, the note's central mechanism.

**DERIVATION:** `.23`(ii) — HE6R1-2 at the datum and key, with the initial-segment claim proved from hull-slope monotonicity.

**CONDITIONALITY:** **the parenthetical “top coefficient NOT monic — the partial-side signature” is SUPERSEDED by the TOWERRAT2-C annex** (`.57`): it is FALSE as written, and the display of record replaces it with “C_M monic of degree n − M·D2 < D2, the constant 1 exactly when D2 | n; the partial-side signature is n > mu2·D2”. SUPERSESSION KIND: **replacement**, scoped to the parenthetical: “the surrounding (ii) clause is unchanged”.

**RESOLUTION TRACE:** statement lines 264–278; proof 332–348; correction 1039–1088.

**TEETH:** P-4 (>T2 segment = [0, mu2*], c_g at the right endpoint, floors cleared) on every row ✓; the c_g-translation is guarded by T-2 NOCG (49 kills).

---

### EFF.GENTOW4.20  [theorem]

**CANONICAL STATEMENT:**

> “> (iii) [PER-BLOCK DECISION — the composed dictionary] THEOREM
> > HE7.A(1)–(3) + THEOREM HE7.C/D + ANNEX-LEMMA HE7-13' apply to
> > f_S at the datum (kappa2, rtilde) with key Phi2: every side of
> > P2(f_S) has slope lambda2 > T2 with Sum L_{lambda2} = mu2*; each
> > irreducible factor r2 of a separable level-2 residual gives ONE
> > irreducible factor of f with
> >
> >     e = e1e2·l2 ,   f = f1f2·deg r2 ;
> >
> > … By (ii) every input to
> > the decision — slopes, lengths, residual factors up to K2^x
> > scalar, all scale-invariantly consumed (HE7 §S1 convention) —
> > is computed from f's OWN development: f_S is never exhibited.”

**FORM:** theorem clause (iii) with the dictionary display.

**DERIVATION:** `.23`(iii) — HE7.A's hypothesis list discharged row by row against HETOW's S1 table with three rows replaced.

**CONDITIONALITY:** **the row accounting carries the m-B rider** (`.52`), quoted in full there: three rows replaced by 4.1(a)(b) and (ii), the remaining two discharged by 4.1(d)'s peels, “No row is undischarged”. **“f_S is never exhibited” is the practical payoff** — the reader works on f's own digits.

**RESOLUTION TRACE:** statement lines 280–296; proof 348–366 (including the m-B rider inline).

**TEETH:** P-2 HEADLINE: every member decided with σ = PARI exactly, both routes where run (117/117).

---

### EFF.GENTOW4.21  [theorem]

**CANONICAL STATEMENT:**

> “> (iv) [THE OTHER CLASSES] every other class C_{kappa,r} is priced
> > by the same clauses (i)–(iii) at ITS datum (kappa, rtilde_r): if
> > its own mu2*(kappa,r) = 1 … the class is one irreducible
> > factor with (e, f) = (e1·l, f1·d_r) — THEOREM HE6.A's dictionary
> > recovered through the level-2 read (consistency: two proofs
> > where R_kappa is separable); if r is repeated with l·d_r = 1 it
> > is the level-1 alpha-refine family …; if repeated with l·d_r >= 2 it is ITSELF a
> > tower class — an inner event on ITS side, read by this same
> > theorem (at PARTIAL sides) or by THEOREM HETOW.A (full side).
> > sigma(f) = the disjoint union over classes (+ the S2 peels).”

**FORM:** theorem clause (iv).

**DERIVATION:** the same instantiation at other data, with three cases by `l·d_r`.

**CONDITIONALITY:** **the recursion is genuine**: a repeated co-class is itself a tower class read by this same theorem. FR-M gives its first machine contact (`.48`) and FR-3B the first three-block instance (`.56`).

**RESOLUTION TRACE:** statement lines 298–309; proof 366–370.

**TEETH:** T-3 SIBDROP; the diagnostic census shows every family realized its full preregistered menu including the sibling component (`.43`).

---

### EFF.GENTOW4.22  [theorem]

**CANONICAL STATEMENT:**

> “> (v) [mu2* = 2 DECIDES — T(b)'(iii)'s trichotomy through the
> > projection] if mu2* = 2, the block decision is complete and
> > translation/scale-invariant on f's own data: with the >T2
> > segment spanning [0,2],
> >   TWO sides (distinct slopes)            -> {(e1e2, f1f2)} x2
> >   ONE side, l2 = 2 (half-integer slope)  -> {(2e1e2, f1f2)}
> >   ONE side, integer slope, residual
> >     (gamma_g-scaled) irreducible quadratic -> {(e1e2, 2f1f2)}
> >     split (two K2-roots)                   -> {(e1e2, f1f2)} x2
> >     double root                            -> alpha-refine, repeat
> > (slopes are translation-invariant; root/irreducibility tests are
> > invariant under the K2^x scaling gamma_g; the double-root refine
> > terminates by HE7-13 at the block, per HE7-13'(b)).”

**FORM:** theorem clause (v) with a five-row decision display.

**DERIVATION:** `.23`(v) — the three shapes of a `[0,2]` segment, each mapped under the c_g/γ_g invariances.

**CONDITIONALITY:** **this is the clause the future GENHN.B cite would use** (`.40`): “can, after acceptance, cite THEOREM GENTOW-4.A(v) for inner-mu2 = 2 partial leaves at pure-power sides — with GENTOW4-BOX-1 named at mixed sides.”

**RESOLUTION TRACE:** statement lines 311–323; proof 370–374.

**TEETH:** the whole battery is a μ₂ = 2 battery (BOX-3), so (v) is the clause the 117 members exercise. **The invariance argument is what makes the decision computable from f alone** — and T-2 NOCG shows the naive translation-free alternative fails 49 times.

---

### EFF.GENTOW4.23  [derivation]

**CANONICAL STATEMENT:** the 4.A proof, `[ASSEMBLED]` from lines 329–374. Clause (ii)'s geometric core, verbatim:

> “That the >T2 part is the
> INITIAL segment and spans [0, mu2*]: hull slopes (height drop
> per unit j) strictly decrease left to right, so the >T2 sides
> are leftmost; P2(f_S) spans [0, mu2*] entirely with ALL sides
> > T2 (LEMMA HE7-9(a) + HE7.A(1) at f_S) and right endpoint
> (mu2*, 0) (f_S monic of Phi2-length mu2*), so its c_g-translate
> — which HE6R1-2(b) identifies with the >T2 part of P2(f) —
> spans [0, mu2*] with right endpoint (mu2*, c_g).”

**FORM:** five-clause proof.

**DERIVATION:** as quoted; the initial-segment claim is a convexity argument, the span a transport of f_S's own polygon.

**CONDITIONALITY:** the GENHN-2′ pin read is checked to survive the partial side: “its proof reads coefficient degrees < D2 and the two-step class separation, both intact at the partial side; the top coefficient C_M has deg n − M·D2 < D2”. **That last clause is the CORRECT form the TOWERRAT2-C annex points to** — the proof was right where the (ii) parenthetical was wrong (`.57`).

**RESOLUTION TRACE:** lines 329–374.

**TEETH:** P-4 verifies the span and the endpoint on every row.

---

### EFF.GENTOW4.24  [lemma]

**CANONICAL STATEMENT:**

> “> **LEMMA GENTOW-4.2 (tie, PURE-POWER sides).** If the inner
> > side's residual is a pure power — R_{kappa2} = c·psi2^{mu2},
> > c in K^x (the PE2-P shape and every single-repeated-class side)
> > — then mu2* = mu2: the composed polygon length equals the
> > level-1 residual exponent, and deg f_S = D2·mu2 = D'·e2f2·mu2.
> >
> > *Proof.* LEMMA HE6-3 …: the side of length L_side =
> > e2·deg R_{kappa2} = e2f2·mu2 carries exactly n_{kappa2} =
> > D'·L_side roots of f with dv(Phi'(x0)) = kappa2. Every such
> > root's letter is a root of iota(c·psi2^{mu2}), whose only
> > irreducible factor is psi2 — so ALL of them lie in the one
> > class: |S| = D'e2f2·mu2. LEMMA HE6R1-2(b) (via GENTOW-4.A(ii))
> > gives |S| = deg f_S = D2·mu2* = D'e2f2·mu2*. Divide. ∎”

**FORM:** lemma + inline proof.

**DERIVATION:** a root count from two directions, divided.

**CONDITIONALITY:** **PURE-POWER sides only.** The mixed case is `.25` and is boxed.

**RESOLUTION TRACE:** lines 378–391.

**TEETH:** P-3: `mu2* = 2 = mu2` on every pure-side member ✓. **ARITHMETIC AUDIT: `D2·mu2* = D'e2f2·mu2*` and `|S| = D'e2f2·mu2` give `mu2* = mu2` on division** ✓ — the argument is a clean two-count identity.

---

### EFF.GENTOW4.25  [fence]

**CANONICAL STATEMENT:**

> “> At a MIXED side (R_{kappa2} = psi2^{mu2}·Rhat, Rhat coprime to
> > psi2, deg Rhat >= 1) the read is UNCHANGED — mu2* is computed
> > from f and the decision (iii)/(v) fires — but the TIE
> > mu2* = mu2 is NOT derived here: the level-1 count splits as
> > Sum_r |C_{kappa2,r}| = D'·L_side (LEMMA HE6-3) with each class
> > pinned only by its own projection, and matching each mu2*(r) to
> > the multiplicity m_r requires the residual-multiplicity
> > transport this corpus has not proved (HE7-BOX-4 declined
> > exactly this; Ore's second theorem / FGMN Lemma 2.17 content).
> > Honest box: GENTOW4-BOX-1 (S7). The battery includes a mixed
> > family (FAM-P5) run in read-mode: every decision PARI-exact,
> > tie checked EMPIRICALLY (mu2* = m_r on every member).”

**FORM:** bold fence following the lemma.

**DERIVATION:** `[RECORD]` of a non-derivation, with the missing ingredient named and attributed (Ore-II / FGMN Lemma 2.17).

**CONDITIONALITY:** **“the read is UNCHANGED” is the load-bearing scope split**: the DECISION works at mixed sides; only the level-1 PREDICTION of block length is lost. That distinction is repeated verbatim in BOX-1 (`.36`) and in ledger row HYP.144.

**RESOLUTION TRACE:** lines 393–404.

**TEETH:** FAM-P5 (mixed) in read-mode: “every decision PARI-exact, tie checked EMPIRICALLY”. Disposition `signed non-derivation with empirical measurement`.

---

### EFF.GENTOW4.26  [corollary]

**CANONICAL STATEMENT:**

> “> **COROLLARY GENTOW-4.C (the c_g-read — absolute block pins from
> > f's digits).** In GENTOW-4.A(ii): c_g = the height of P2(f) at
> > abscissa mu2* (the right endpoint of the >T2 initial segment),
> > and the block pins are p_j^S = p_j − c_g wherever (j, p_j) lies
> > on the >T2 hull. Consequently GENTOW-1(c)'s node floors are
> > VISIBLE THROUGH THE PROJECTION: p_j^S >= (mu2* − j)E2 + 1 for
> > j < mu2* (LEMMA GENTOW-1(c) applies to f_S, whose entry is
> > full-side by construction …). At PE2-P:
> > c_g = 5, p^S = (23, 11), floors (21, 11) — j = 1 exact.”

**FORM:** bold-headed corollary.

**DERIVATION:** `.27`, with the floor transport routed through f_S's own full-side entry.

**CONDITIONALITY:** **the citation of the pin equality is COMPLETED by the m-i acceptance-fold bracket** (`.33`): (b) alone gives an inequality; equality needs (b) + vertex attainment at hull vertices, and (c)'s residual-scalar display at side-interior abscissas.

**RESOLUTION TRACE:** statement lines 406–415; proof 417–422; the m-i bracket 424–449.

**TEETH:** **the PE2-P numbers recompute** (`.08`) ✓. P-4 tests the floors through the projection on every row.

---

### EFF.GENTOW4.27  [derivation]

**CANONICAL STATEMENT:**

> “> *Proof.* Right endpoint: displayed inside GENTOW-4.A(ii)'s
> > proof. Translation: HE6R1-2(b). The floor transport: f_S
> > satisfies GENTOW-1's 𝒯-definition at (Q; e1,f1, e2f2·mu2*; h)
> > with the same (u2, e2, psi2): its roots are exactly the class S,
> > all tower-node points; GENTOW-1(a)(c) applied to f_S gives the
> > floors; the projection carries them to f's pins. ∎”

**FORM:** proof.

**DERIVATION:** as quoted — **the key move is that f_S is a FULL-side object**, so GENTOW-1's full-side machinery applies to it and transports through the projection.

**CONDITIONALITY:** the “Translation: HE6R1-2(b)” cite is the one m-i completes.

**RESOLUTION TRACE:** lines 417–422.

**TEETH:** the transport claim is what makes GENTOW-1 (a 2/2-accepted full-side note) usable at partial sides — the note's cleanest reuse.

---

### EFF.GENTOW4.28  [fence]

**CANONICAL STATEMENT:**

> “> Note the LOAD-BEARING parity flip: the RAM test is p_0^S odd,
> > and c_g need not be even (PE2-P: c_g = 5), so the f-level parity
> > p_0 mod 2 is NOT the block parity. Equivalently (and how S3(v)
> > states it): decide RAM by the SLOPE's denominator, which is
> > translation-invariant. A reader using f-level pin parity is
> > wrong exactly on odd-c_g members — tooth T-NOCG.”

**FORM:** bold-headed note.

**DERIVATION:** immediate from `p_j^S = p_j − c_g` with `c_g` odd.

**CONDITIONALITY:** none. **This is the note's single most machine-load-bearing observation** and it names its own tooth.

**RESOLUTION TRACE:** lines 451–456.

**TEETH:** T-2 NOCG fires **49 times, every flip PARI-killed** (`.44`), and P-4 records `c_g` ODD on 71 tower reads and EVEN on 46 — **both parities live**, so the tooth is neither vacuous nor universal.

---
