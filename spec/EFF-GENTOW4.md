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
### EFF.GENTOW4.29  [derivation]

**CANONICAL STATEMENT:** the coherent-digit remark, `[ASSEMBLED]` from lines 458–494. The mechanism and display, verbatim:

> “**REMARK (coherent digits — machine-surfaced at the pre-seal
> smoke, derivation displayed).** S3(v)'s residual tests consume the
> residuals in HE7's COHERENT normalization; RAW slot residues are
> NOT them when the class letter eta2 != 1. At (e2, f2) = (2, 1),
> u2 odd: the wrap Phi'(x0)^2 = eta2·nhat(u2)(x0)·(1 + small) makes
> the height-0 monomial ratio x^{Δa} pi^{Δv} Phi'^{Δb} have residue
> eta2^{Δb/2} (Δb is forced even; the pi-relation has residue 1, and
> the x-relation x^{e1} = eta·pi^h·(1 + small) has residue eta — so
> this step, and the display below, are derived AT eta = 1 [GT4-r1:
> the composed parenthetical said "at f1 = 1", which is FALSE — f1 =
> 1 does not force eta = 1]), so the coherent digit at coordinate j
> of an integer-slope [0,2]-read is
>
>     delta_j = r_j · eta2^{(b_j − B_j)/2},
>     N_j := n2hat(c_g)·n2hat(lam)^{2−j},  B_j = b-exponent of N_j,”

and the defect it names, verbatim:

> “Feeding r_j instead of delta_j flips INERT/SPLIT
> exactly on eta2 != 1 members: FAM-P5 (psi2 = T+1 over F_3,
> eta2 = 2) exposed
> 12 such flips against PARI at the smoke; q = 2 families and
> eta2 = 1 rows are structurally blind to the defect. The corrected
> reader is the sealed one; the defect is preserved as tooth
> T-6 NOTWIST. (This is HETOW's T-BADTWIST phenomenon at the
> partial-side read — the S4-normalizer cocycle is machine-load-
> bearing here too.)”

**FORM:** bold-headed remark with a display and an in-place corrected parenthetical.

**DERIVATION:** a wrap computation, with the derivation's scope pinned to η = 1.

**CONDITIONALITY:** **TWO corrections here.** (1) The in-place parenthetical rewrite: “at f1 = 1” → the two-clause form, **because f1 = 1 does not force eta = 1** — the composed text was FALSE, and m-C records this as one of the two in-place rewrites (`.53`). (2) The `[GT4-r1 SCOPE]` bracket (`.30`) pins the whole display, and the sealed `coh()`, to η = 1.

**RESOLUTION TRACE:** lines 458–494; the scope pin 475–486; m-C's record 891–905.

**TEETH:** **T-6 NOTWIST fires 8 times, every flip PARI-killed** (`.44`); the pre-seal smoke exposed 12 flips at FAM-P5. **Cross-entry: this is `EFF.HETOW.37`'s T-BADTWIST phenomenon at the partial-side read**, and the note says so — the same cocycle is load-bearing in both.

---

### EFF.GENTOW4.30  [fence]

**CANONICAL STATEMENT:**

> “[GT4-r1 SCOPE (S8): the display — and the sealed coh() — is
> derived at eta = 1, which covers the whole battery (q = 2
> forcibly; the q = 3 families' Phi' = x^2−3 has eta = res(x^2/3) =
> 1) but NOT every f1 = 1 frame. At eta != 1 each b-wrap Phi'^2 ->
> eta2·nhat(u2) introduces x-exponent i(u2), and reducing the
> accumulated x-exponents through the x-relation contributes
> eta-powers the display omits — the same cocycle that corrects
> chat_t (S0 pin). What holds at f1 = 1, eta != 1 is the SLOPE layer
> of S3(v): FR-G's committed members (eta = 2, S8) are decided
> 2SIDED and RAM at the corrected key, PARI-exact, consuming no
> residual digits; no machine row in any leg yet exercises coh() at
> eta != 1.]”

**FORM:** dated scope bracket.

**DERIVATION:** identifies the omitted η-powers as the SAME cocycle that corrects `chat_t`.

**CONDITIONALITY:** SUPERSESSION KIND: **scope-pin**. **The residual-digit layer of S3(v) is η = 1-scoped; only the SLOPE layer is verified at η ≠ 1.** This is a genuine live gap and is carried into BOX-3 (`.38`): “no eta != 1 coh() row”.

**RESOLUTION TRACE:** lines 475–486.

**TEETH:** disposition `signed coverage disclosure`; FR-G's members are decided on slopes alone **by design** (`.47`).

---

### EFF.GENTOW4.31  [run-record]

**CANONICAL STATEMENT:** §S5, PE2-P verified exactly, `[ASSEMBLED]` from lines 498–520. The oracle close, verbatim:

> “ORACLE (PARI, factor + idealprimedec and factorpadic routes,
> 2026-08-09): disc != 0; sigma = {(2,1),(4,1),(4,1)} — EXACT.
> Per-factor valuations: deg-2 factor dv2(Phi2) = 10 = E2 exactly
> (steeper sibling: the t = 0 lift term of Phi2 dominates); deg-4
> factors dv2(Phi2) = 12 and 11 = THE TWO POLYGON SLOPES (HE7's
> side dictionary at the composed carrier, visible in nfeltval),
> both > E2 (GENTOW-1(d) at the block). dv2(Phi') = 5 = u2 on both
> tower factors ((T1_2) transport); dv(Phi') = 3 on the sibling
> factor (its own side slope).”

**FORM:** section body — a full hand computation checked against a dual-route oracle.

**DERIVATION:** hand computation, machine row PE2P-0.

**CONDITIONALITY:** none. **The per-factor valuation reading is the strongest structural confirmation in the note**: the polygon slopes ARE the factor valuations, visible in `nfeltval`.

**RESOLUTION TRACE:** lines 496–520.

**TEETH:** **ARITHMETIC AUDIT: the two deg-4 factors' `dv2(Phi2)` values 12 and 11 are exactly the two hull slopes of `.08`** ✓, and the deg-2 sibling sits at `E2 = 10` exactly ✓ — the field floor separates the classes as GENTOW-1(d) predicts. `dv2(Phi') = u2 = 5` ✓ on the tower factors.

---

### EFF.GENTOW4.32  [preregistration]  `[TABLE]`

**CANONICAL STATEMENT:** the family menu, source lines 528–534:

| family | genre | q | inner (e2,f2,u2) | sibling | n | menu (tower part) |
|---|---|---|---|---|---|---|
| P1 | (2,1,5) | 2 | (2,1,5) side [1,5] | slope 3, len 1, left | 10 | {(8,1)},{(4,2)},{(4,1)}x2 (+ {(2,1)}) |
| P2 | (2,1,5) | 2 | (1,2,3) side [1,5], K2=F4 | slope >=4, len 1, left | 10 | {(4,2)},{(2,4)},{(2,2)}x2 (+ {(2,1)}) |
| P3 | (2,1,5) | 3 | (2,1,5) side [1,5] | slope 3, len 1, left | 10 | {(8,1)},{(4,2)},{(4,1)}x2 (+ {(2,1)}) |
| P5 | (2,1,6) | 3 | (2,1,5) MIXED side [0,6]: (T+1)^2(T−1) | (same side, simple class) | 12 | {(8,1)},{(4,2)},{(4,1)}x2 (+ {(4,1)}) |
| P6 | (2,1,7) | 2 | (2,1,5) side [0,4] | slope 7/3, len 3, RIGHT | 14 | {(8,1)},{(4,2)},{(4,1)}x2 (+ {(6,1)}) |

**FORM:** table.

**DERIVATION:** `[DESIGN]` — five families spanning three genres, both e₂-branches, both sibling flanks, one mixed side.

**CONDITIONALITY:** **all five sit at η = 1** (`.49`) — the battery is structurally gauge-blind, disclosed twice.

**RESOLUTION TRACE:** lines 526–534.

**TEETH:** **ARITHMETIC AUDIT of the menus' degree sums.** P1 (n = 10, tower part 8 + sibling 2): `{(8,1)}` → 8 ✓; `{(4,2)}` → 8 ✓; `{(4,1)}×2` → 8 ✓; sibling `{(2,1)}` → 2 ✓; total 10 ✓. P2: `{(4,2)}` → 8 ✓, `{(2,4)}` → 8 ✓, `{(2,2)}×2` → 8 ✓, + 2 = 10 ✓. P5 (n = 12): tower 8 + simple class `{(4,1)}` = 4 → 12 ✓. P6 (n = 14): tower 8 + `{(6,1)}` = 6 → 14 ✓. **All five menus are degree-consistent.**

---

### EFF.GENTOW4.33  [changes-record]

**CANONICAL STATEMENT:** the m-i acceptance-fold bracket, verbatim (abridged):

> “[acceptance fold (post-PE3) 2026-08-10, m-i — THE CITATION
> COMPLETED: the displayed pin equality p_j^S = p_j − c_g rides
> HE6R1-2(b) AND (c). Re-derived at HE6R1_RECON S3.4. What (b)
> carries: the support-function identity h_{F2,f}(kappa2) =
> h_{F2,f_S}(kappa2) + c_g on (T2, ∞), so the >T2 hull of P2(f)
> is the >T2 hull of P2(f_S) translated by c_g … — from (b) alone an on-hull point (j, p_j)
> yields hull_{f_S}(j) = p_j − c_g <= p_j^S, an INEQUALITY; at
> hull VERTICES equality follows from (b) plus vertex attainment
> (a lower-hull vertex is a point of the cloud — 4.1(b)'s
> mechanism at the level-2 pin set). What (c) carries: at
> side-INTERIOR hull abscissas (the j = 1 of a one-side mu2* = 2
> shape) equality rides (c)'s residual scalar display … R^f_{lambda2} =
> gamma_g·R^{f_S}_{lambda2} with gamma_g ∈ K2^× nonzero by (a):
> interior hull attainment reads off a nonzero residual
> coefficient, a K2^×-scalar preserves nonzeroness coefficientwise,
> so f's interior attainment at j transfers to f_S and the
> displayed equality holds there too. … Machine contact (cited, PE3's
> fresh leg @ f0874ff9): the equality tested as an EQUATION
> against explicit f_S at the hull abscissas of 11 members incl.
> interior j = 1 at five 2SIDED blocks, 0 violations. No
> conclusion moves; the floors consequence needs only slopes > T2
> plus pin integrality, carried by (b) as displayed.]”

**FORM:** dated acceptance-fold bracket.

**DERIVATION:** a careful separation of what (b) gives (an inequality, upgraded to equality only at vertices) from what (c) gives (equality at side-interior abscissas).

**CONDITIONALITY:** SUPERSESSION KIND: **provenance-rider** — “No conclusion moves”. **The distinction is real mathematics, not bookkeeping**: without (c), the displayed equality would be unproved at the interior j = 1 of a one-side μ₂* = 2 shape, which is a shape the battery actually contains.

**RESOLUTION TRACE:** lines 424–449.

**TEETH:** **machine contact: “tested as an EQUATION against explicit f_S at the hull abscissas of 11 members incl. interior j = 1 at five 2SIDED blocks, 0 violations”** — the interior case is exactly the one (c) is needed for, and it is the one measured. `git cat-file -t f0874ff9` = commit ✓.

---

### EFF.GENTOW4.34  [preregistration]

**CANONICAL STATEMENT:** the seven predictions and six teeth, `[ASSEMBLED]` from lines 536–569. The headline and the boxed-tie prediction, verbatim:

> “* P-2 (HEADLINE): the S3/S4 reader (per-class composed read,
>   c_g-translation, slope/residual trichotomy, sibling classes at
>   their own data) decides every member with sigma = PARI exactly
>   (route 1 all members; route 2 subsample), including PE2P-0 (the
>   witness row) verbatim.
> * P-3 (tie): mu2* = mu2 on every pure-side member; on FAM-P5
>   (mixed) mu2* = 2 at the repeated class and 1 at the simple class
>   — an EMPIRICAL check of the boxed tie (measurement, not proof).”

The six teeth, verbatim in brief: **T-1 FULLREAD** (the monic reader refuses every member — “the loud failure stays loud”); **T-2 NOCG**; **T-3 SIBDROP**; **T-4 WITHHOLD**; **T-5 WRONGKEY**; **T-6 NOTWIST** (“added pre-seal from the disclosed smoke finding, S4 remark”).

**FORM:** two bulleted preregistration lists, sealed in the runner docstring before the first full run.

**DERIVATION:** `[PREREGISTERED]`

**CONDITIONALITY:** **P-3 is explicitly labelled “measurement, not proof”** — the preregistration itself refuses to let a green tie row discharge BOX-1. That is preregistration discipline of a high order.

**RESOLUTION TRACE:** lines 536–569.

**TEETH:** all seven and all six are scored at `.43`/`.44`.

---

### EFF.GENTOW4.35  [fence]

**CANONICAL STATEMENT:**

> “**What item (4) still keeps (named exactly):**”

**FORM:** bold-headed §S7 opening.

**DERIVATION:** `[RECORD]` — the residue inventory's header. Emitted as its own unit because the four boxes that follow are one ledger family (SERIES BOXES) and this sentence is their scope declaration.

**CONDITIONALITY:** “named exactly” is a discipline claim the four boxes honour.

**RESOLUTION TRACE:** line 576.

**TEETH:** the four boxes are `.36`–`.39`.

---

### EFF.GENTOW4.36  [fence]  *(SERIES BOXES; ledger HYP.144)*

**CANONICAL STATEMENT — reproduced EXACTLY as left (queue charge):**

> “* **GENTOW4-BOX-1 (the mixed-side multiplicity tie).** At sides
>   carrying >= 2 distinct residual classes with a repeated one, the
>   tie mu2*(r) = m_r (composed length = residual multiplicity per
>   class) is UNPROVED here (S4; Ore-II/FGMN Lemma 2.17 content —
>   a faithful-cite unit in GENTOW2's pattern would retire it). The
>   READ and sigma are unaffected (mu2* is computed, not assumed);
>   what is lost without the tie is only the level-1 PREDICTION of
>   each block's length. Machine: empirically exact on FAM-P5.”

**FORM:** bulleted box.

**DERIVATION:** `[RECORD]` of a non-derivation, with the missing content attributed to a citable published source.

**CONDITIONALITY:** **OPEN at HEAD.** **LEDGER CROSS-REFERENCE — `spec/HYPOTHESIS_LEDGER.md` row `HYP.144` (`GENTOW4-BOX-1/-2/-4`, WHERE: “L577–584, L585–590, L614–618”) states BOX-1 as:**

> “BOX-1 (mixed-side multiplicity tie) — the tie mu2*(r) = m_r “is UNPROVED here (S4; Ore-II/FGMN Lemma 2.17 content — a faithful-cite unit in GENTOW2’s pattern would retire it)”; READ and σ are unaffected, what is lost is the level-1 prediction of block length.”

with disposition “MATH — … BOX-1 is retirable by a faithful-cite unit”. **The ledger's WHERE line pins L577–584; this unit's home is lines 577–584 exactly** ✓ — the ledger row and the note agree line-for-line, and the ledger's quotation is verbatim from this box.

**RESOLUTION TRACE:** lines 577–584; ledger `HYP.144` at `spec/HYPOTHESIS_LEDGER.md:1136–1141`.

**TEETH:** `signed non-derivation`; FAM-P5's empirical tie (P-3) is measurement only, as both the box and the preregistration say.

---

### EFF.GENTOW4.37  [fence]  *(SERIES BOXES; ledger HYP.144 — the binding residue)*

**CANONICAL STATEMENT — reproduced EXACTLY as left:**

> “* **GENTOW4-BOX-2 (partial-side entry budgets / count laws).**
>   GENTOW-1's budget fibration is proved on the FULL-side locus 𝒯;
>   the partial-side locus (products of class boxes + sibling data)
>   has no budget/count display here — the item-(4) COUNT layer
>   stays open (it was open at full sides' LEDGERS too, GENTOW-1
>   remark). sigma-decision only in this unit.”

**FORM:** bulleted box.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** **OPEN at HEAD, and the ledger marks it the BINDING residue of the three.** `HYP.144`:

> “BOX-2 (partial-side entry budgets) — the budget fibration is proved only on the FULL-side locus 𝒯; “the item-(4) **COUNT layer stays open**”.”

with “CONSUMED BY: partial-side count laws feeding the same μ≥3 count layer as HYP.139 and HYP.142” and “PROPOSED DISPOSITION: MATH — BOX-2’s open COUNT layer is the binding residue”. **The ledger also links it to `HYP.68` (GENTOW6-BOX-2)**, whose CONSUMED-BY says the count-ledger obligation “belongs beside HYP.144’s GENTOW4-BOX-2 open COUNT layer, which is the same μ≥3 count-layer obligation family as HYP.139 and HYP.142.” **So BOX-2 is one member of a four-row obligation family** (HYP.139, HYP.142, HYP.144, HYP.68) — a DAG fact no single note carries.

**RESOLUTION TRACE:** lines 585–590; ledger `HYP.144` and `HYP.68`.

**TEETH:** the note's own cross-reference is exact: the count layer “was open at full sides' LEDGERS too, GENTOW-1 remark” = `EFF.GENTOW1.26`, which this queue independently compiled as a non-executed counting unit ✓.

---

### EFF.GENTOW4.38  [fence]  *(SERIES BOXES)*

**CANONICAL STATEMENT — reproduced EXACTLY as left, including the r1 rider:**

> “* **GENTOW4-BOX-3 (coverage).** mu2 = 2 inner events only (mu2 >= 3
>   partial towers = this read + [GENHN-HE(mu2)] for the block's
>   menu …); f1 = 1 outer keys; q in {2,3}; e2 in
>   {1,2}; depth 2; d = 1 ambients. The S2–S4 proofs are uniform in
>   all of these (S3(iii) is stated at any mu2*); the gap is
>   machine-side, named. [GT4-r1: the axis list above omitted the
>   ETA-GAUGE axis (eta = res(x^{e1}/pi^h)), and "uniform in all of
>   these" is WITHDRAWN (HETOW [r1] F-3's precedent). Honest status:
>   the S2–S4 statements and proofs hold AT THE WRAP-CORRECTED KEY
>   of the S0 pin — at the gauge-naive display, 4.1(c)'s key clause,
>   (ii)'s deg f_S = D2·mu2* display, and GENTOW-1(d)'s floor
>   transport FAIL at eta != 1, f2 = 2 frames (S8's FR-G: naive-key
>   sigma {(4,1)} != carrier {(2,2)}; naive mu2* = 0 with the class
>   invisible; nfeltval = E2 exactly) … Named
>   machine-side gaps now: no f1 >= 2 row, no eta != 1 coh() row,
>   depth 2 only.]”

**FORM:** bulleted box with a dated withdrawal rider.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** SUPERSESSION KIND: **replacement** — “uniform in all of these” is WITHDRAWN, explicitly following HETOW [r1] F-3's precedent. **Three named machine gaps at HEAD: no f1 ≥ 2 row, no η ≠ 1 `coh()` row, depth 2 only.** **Cross-entry: this is the fourth note in the queue to withdraw a uniformity sentence on the η axis** (HETOW `.30`, GENTOW1 `.48`/`.54`, GENTOW3 `.40`, here) — a corpus-wide pattern, all traceable to one erratum.

**RESOLUTION TRACE:** lines 591–613.

**TEETH:** `signed coverage disclosure`; FR-G supplies the η ≠ 1 slope-layer contact (`.47`), and the battery blindness is disclosed twice (`.49`).

---

### EFF.GENTOW4.39  [acceptance-box]  *(SERIES BOXES; ledger HYP.144; CHAIN-GRADES — TERMINAL)*

**CANONICAL STATEMENT — reproduced EXACTLY as left, with its m-E rider:**

> “* **GENTOW4-BOX-4 (grade).** 0/2 attempt, composed this session,
>   no hostile arc. Conditionality stack: LEMMA GENHN-T(b)'(i)(ii)
>   + the [r1] node floor (GENHN accepted 2/2 at PE4), HETOW-1/2
>   (HETOW 0/2), LEMMA HE6R1-2/HE6R1-3 + RIDER (HE6R1 post-r2,
>   0/2-grade annex stack), THEOREM HE7.A/C/D + HE7-12/13 + ANNEX
>   HE7-13' (HE7 accepted 2/2; annex F-1 post-acceptance), LEMMA
>   HE6-3/HE6-4 + THEOREM HE6.A (HE6 accepted, r1/r2 applied),
>   GENTOW-1 (0/2). Every consequence inherits the MINIMUM grade.
>   [rider (post-PE2, 2026-08-10; m-E): supplier grades refreshed
>   from the arc records …: HETOW-1/2 — HETOW
>   ACCEPTED 2/2 …; GENTOW-1 — ACCEPTED 2/2 (GENTOW1_PROOF's
>   dated record @ 4aff731, standing through its post-acceptance
>   R2a/b/c rounds); HE6R1 — ACCEPTED 2/2 … The composed line's 0/2s were stale in
>   the CONSERVATIVE direction (understated supplier grades). This
>   note's own grade after PE2: counter 1/2, one clean pass on
>   record.]”

**FORM:** bulleted box with a dated grade-refresh rider.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** SUPERSESSION KIND: **counter re-reading** (three supplier grades) — and the note's own counter is superseded again to **ACCEPTED 2/2** at `.56`. **LEDGER CROSS-REFERENCE — `HYP.144` states BOX-4 as:**

> “BOX-4 (grade) — “**0/2 attempt**, composed this session, no hostile arc”, over a conditionality stack including HETOW-1/2 (HETOW 0/2) and the HE6R1 0/2-grade annex stack.”

with “BOX-4 is a standing grade cap on all three”. **The ledger row quotes the COMPOSED wording (0/2) and does not carry the m-E refresh or the note's own 2/2** — so a ledger consumer would read three stale grades plus a stale self-grade. Recorded as OPEN-CALL 3.

**RESOLUTION TRACE:** lines 614–632; correction 991–1000; ledger `HYP.144`.

**TEETH:** **the m-E refresh is independently confirmed by this queue**: HETOW ACCEPTED 2/2 (`EFF.HETOW.46`), GENTOW-1 ACCEPTED 2/2 (`EFF.GENTOW1.59`, at commit `4aff731` — the same commit m-E cites ✓). “Every consequence inherits the MINIMUM grade” survives all refreshes.

---

### EFF.GENTOW4.40  [fence]

**CANONICAL STATEMENT:**

> “**Consumption path (not executed here):** [GENHN-TOW-1] item (4)'s
> box text in GENHN_PROOF is the orchestrator's dated consumption
> update after this note's own hostile arc; GENHN_PROOF, HETOW_RECON,
> HE7_PROOF, HE6R1_RECON are byte-untouched by this unit. The
> GENHN.B (CS-3) partial-side rider (passPE2 F2's cure) can, after
> acceptance, cite THEOREM GENTOW-4.A(v) for inner-mu2 = 2 partial
> leaves at pure-power sides — with GENTOW4-BOX-1 named at mixed
> sides.”

**FORM:** bold-headed protocol fence.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** **the conditional cite's precondition is now MET** (ACCEPTED 2/2, `.56`) **and the cite is unlanded** — `grep -cF 'GENTOW' GENHN_PROOF_2026-08-08.md` = 0 (N1). **Two obligations**: the item-(4) box discharge, and the GENHN.B partial-side rider cite. OPEN-CALL 1.

**RESOLUTION TRACE:** lines 634–641.

**TEETH:** N1 ✓.

---

### EFF.GENTOW4.41  [run-record]

**CANONICAL STATEMENT:**

> “**Artifacts.** `gentow4_checks_output.txt` (committed); sealed
> runner @ commit 1 = 2aa5b16, md5
> 98cdd4a4e5a47f1434bdf8ca5a1c4b4c (printed at artifact line 2; no
> post-seal edit — the verdict-run md5 is IDENTICAL to the sealed
> file). Runtime ~5 s + PARI (371 gp jobs).”

**FORM:** bold-headed artifact record.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** none.

**RESOLUTION TRACE:** lines 647–651.

**TEETH:** **`md5sum gentow4_checks.py` = `98cdd4a4e5a47f1434bdf8ca5a1c4b4c` ✓, AND the artifact's line 2 reads `runner md5: 98cdd4a4e5a47f1434bdf8ca5a1c4b4c`** ✓ — the “printed at artifact line 2” claim is literally verified. `git cat-file -t 2aa5b16` = commit ✓.

---

### EFF.GENTOW4.42  [run-record]

**CANONICAL STATEMENT:**

> “**Totals.** 117 members (P1 25 incl. PE2P-0, P2 24, P3 22, P5 22,
> P6 24), 0 dropped, 117 reader-decided, 117 sigma comparisons on
> PARI route 1 + subsample on route 2, per-factor valuation rows via
> nodev6 on every member. **1,740 checks, 0 violations.**”

with the headline: “**GREEN — 1,740 checks, 0 violations, 6/6 teeth**”.

**FORM:** bold-headed totals + section headline.

**DERIVATION:** `[RUN]`

**CONDITIONALITY:** none.

**RESOLUTION TRACE:** lines 645, 653–656.

**TEETH:** **ARITHMETIC AUDIT: 25 + 24 + 22 + 22 + 24 = 117 members** ✓. **The artifact's final lines read `TOTAL: 1740 checks, 0 violations, 4.9 s` / `VERDICT: GREEN`** ✓ — both the count and the ~5 s runtime match.

---

### EFF.GENTOW4.43  [run-record]

**CANONICAL STATEMENT:** the seven scored predictions, `[ASSEMBLED]` from lines 658–679. P-2, P-4 and P-5, verbatim (the load-bearing three):

> “* **P-2 ✓ (HEADLINE)** every member DECIDED by the S3/S4 reader
>   and sigma = PARI exactly, both routes where run; PE2P-0
>   reproduced the witness {(2,1),(4,1),(4,1)} — the box's
>   protected instance now has a proved, machine-checked read.
> * **P-4 ✓** >T2 initial segment = [0, mu2*] with c_g at the right
>   endpoint; GENTOW-1(c) floors cleared through the projection on
>   every row; c_g ODD on 71 tower reads (P1/P2/P3 flanks) and EVEN
>   on 46 (P5/P6) — both parities live.
> * **P-5 ✓** per factor per prime: class rows dv2(Phi2) > E2
>   STRICT with class degrees summing to D2·mu2* = 8; companion
>   rows = E2 exactly on steeper/same flanks and < E2 on P6's
>   shallow flank; dv2(Phi') = u2 exact on class rows.”

**FORM:** bulleted per-prediction list.

**DERIVATION:** `[RUN]`

**CONDITIONALITY:** **P-3's mixed-family result is empirical only** and the row says so: “(empirical tie only — GENTOW4-BOX-1 unchanged)”.

**RESOLUTION TRACE:** lines 658–679.

**TEETH:** **ARITHMETIC AUDIT: 71 + 46 = 117** ✓ — the parity split covers exactly the member set, so “both parities live” is exhaustive, not sampled. P-2's PE2P-0 row reproduces the witness σ recomputed at `.06`/`.08` ✓.

---

### EFF.GENTOW4.44  [run-record]

**CANONICAL STATEMENT:** the six teeth, `[ASSEMBLED]` from lines 680–695. T-2's row with its dated disclosure, verbatim:

> “T-2 NOCG (49 parity flips, every one PARI-killed — the
>   c_g-translation is machine-load-bearing) [GT4-r1 DISCLOSURE
>   (m-2), from the sealed runner L871–878: the flips split by
>   direction — on odd-p0/even-(p0−cg) rows the wrong sigma is the
>   parity rule's own forced RAM output (2e1e2, f1f2); on
>   even-p0/odd-(p0−cg) rows the parity rule says non-RAM without
>   determining WHICH, and the runner emits INERT (e1e2, 2f1f2) as a
>   HAND-ASSEMBLED representative wrong-sigma, not a mutant-reader
>   run through the trichotomy; the 49 kills are PARI-adjudicated in
>   both directions]”

the other five, verbatim in brief: T-1 FULLREAD 117/117 refused; T-3 SIBDROP 117/117; T-4 WITHHOLD (UNDETERMINED, 0 guesses); T-5 WRONGKEY 22/22 “incl. the key | f peel corner”; **T-6 NOTWIST** (8 INERT/SPLIT flips without the η₂-cocycle correction, every one PARI-killed).

**FORM:** teeth list with an embedded dated disclosure.

**DERIVATION:** `[RUN]`

**CONDITIONALITY:** **the m-2 disclosure downgrades HALF of T-2's construction**: in one direction the wrong σ is a HAND-ASSEMBLED representative, not a mutant-reader run. SUPERSESSION KIND: **disclosed non-repair**. The kills remain PARI-adjudicated in both directions, so the tooth still fires honestly — but its mechanism is asymmetric and now says so.

**RESOLUTION TRACE:** lines 680–695.

**TEETH:** **the cited runner lines are verified**: `gentow4_checks.py` L871 reads `            elif p0 % 2 == 0 and (p0 - cg) % 2 == 1:` ✓ — the even-p0 branch, at exactly the stated line, followed by the hand-assembly (`base = list(rd['sigma'])`, `base.remove(...)`) ✓. **The disclosure is accurate to the source.**

---
### EFF.GENTOW4.45  [run-record]

**CANONICAL STATEMENT:**

> “**Diagnostic census (non-sealed one-off, labeled):** every family
> realized its FULL preregistered menu — P1: {(2,1)}∪{(8,1)} x12 /
> {(4,2)} x6 / {(4,1)}² x7; P2: {(2,1)}∪{(4,2)} x20 / {(2,4)} x2 /
> {(2,2)}² x2; P3: 13/2/7; P5: {(4,1)}∪ 10/6/6; P6: {(6,1)}∪ 11/8/5.”

with the leg's honest close, verbatim:

> “**What the leg establishes** (instrument grade, not acceptance):
> the first machine contact anywhere with [GENHN-TOW-1] item (4) …
> is GREEN against
> an independent oracle, with the block decomposition, the HE6R1-2
> projection (c_g), and the per-block HE7.A trichotomy executed
> exactly as THEOREM GENTOW-4.A displays, and with three
> load-bearing seams (c_g-translation, label-keying, eta2-cocycle)
> each guarded by a fired tooth.”

**FORM:** bold-headed census + closing scope paragraph.

**DERIVATION:** `[RUN]`, with the census labelled non-sealed.

**CONDITIONALITY:** “instrument grade, not acceptance” — the standing disclaimer.

**RESOLUTION TRACE:** lines 697–710.

**TEETH:** **ARITHMETIC AUDIT of the census against the member counts:** P1 `12+6+7 = 25` ✓; P2 `20+2+2 = 24` ✓; P3 `13+2+7 = 22` ✓; P5 `10+6+6 = 22` ✓; P6 `11+8+5 = 24` ✓. **All five family censuses sum exactly to their member counts, and the total 25+24+22+22+24 = 117** ✓ — the census is complete and exhaustive.

---

### EFF.GENTOW4.46  [changes-record]  *(CHAIN-GAUGE — the annex)*

**CANONICAL STATEMENT:** §S8.1's seam and its four-site count, verbatim:

> “**The seam.** This note was composed, sealed, and verdicted
> 2026-08-09 15:39–16:06 (c8da214 -> 2aa5b16 -> c21b59e/c43505d) —
> BEFORE the GENHN dated gauge erratum (59c1966, 08-09 20:13,
> provoked by HETOW PE1 F-1) and HETOW's [r1] wrap-correction
> (5335ae3) … The note as composed transcribed the naive display at S0, consumed
> the pre-[r1] HETOW-1/2 at 4.1(c)/S3, claimed BOX-3 uniformity with
> no eta axis, and mis-attributed the S4 remark's residue-1
> x-relation to f1 = 1. All four sites carry [GT4-r1] pins this
> round; the corrected display itself is S0's (re-derived there from
> the wrap cocycle, not transcribed).”

**FORM:** bold-headed seam record.

**DERIVATION:** `[RECORD]` with a **minute-level timestamp chain**: composed/sealed/verdicted 15:39–16:06, erratum at 20:13 the same day.

**CONDITIONALITY:** **the four sites are enumerated and each is pinned** — S0's display, 4.1(c)/S3's consumption, BOX-3's uniformity, the S4 remark's f1 = 1 attribution.

**RESOLUTION TRACE:** lines 731–747.

**TEETH:** **all four commits in the timestamp chain resolve** (`c8da214`, `2aa5b16`, `c21b59e`, `c43505d`) ✓, as do `59c1966` and `5335ae3` ✓. **Cross-entry: three notes (GENTOW1 15:16, GENTOW3 15:53, GENTOW4 15:39–16:06) all verdicted within an hour of each other and all before the 20:13 erratum** — one erratum, three simultaneous naive consumptions, each caught by its own PE1.

---

### EFF.GENTOW4.47  [derivation]

**CANONICAL STATEMENT:** the restated-bridge supply audit, `[ASSEMBLED]` from lines 749–792. Item (1)'s conclusion, verbatim (pre-m-A):

> “(1) 4.1(c) consumes "Phi2 = Psi_{kappa2,rtilde} − w with
> w = 0 or dv2(w) > T2" plus the transported package. The RESTATED
> LEMMA HETOW-2 supplies exactly this at the wrap-corrected key —
> and more strongly: under the (LIFT)-slot coefficient form the
> membership is LITERAL (w = 0, at any f1); its "hence" clause hands
> over the §S5 package, THEOREM HE7.A(1)(2), the refine package
> (HE7-12/13, HE7-8), and the §S1 CONVENTION with HE6R1-3's peel —
> every item on 4.1(c)'s list except LEMMA HE6R1-2 + RIDER and ANNEX
> HE7-13', which 4.1(c)'s own proof supplies through HE7-12(c)'s
> transport …”

and the net verdict, verbatim:

> “Net: with the S0
> pin in force, LEMMA GENTOW-4.1, THEOREM GENTOW-4.A, LEMMA
> GENTOW-4.2, and COR GENTOW-4.C read at the wrap-corrected key with
> no other change; at the naive key FR-G (below) refutes 4.1(c)'s
> key clause (naive sigma {(4,1)} != carrier {(2,2)}), (ii)'s
> deg f_S = D2·mu2* display (naive mu2* = 0 against deg f_S = 8),
> and GENTOW-1(d)'s floor transport (nfeltval = E2 exactly).”

**FORM:** three-item supply audit.

**DERIVATION:** a per-item routing check against the restated source.

**CONDITIONALITY:** **item (1)'s two-item routing sentence is MISATTRIBUTED for its SECOND item and is corrected by m-A** (`.51`). Items (2) and (3) stand.

**RESOLUTION TRACE:** lines 749–792; m-A 762–777 and 946–954.

**TEETH:** the naive-key refutation is measured three ways at FR-G (σ, μ₂*, nfeltval) — `.48`.

---

### EFF.GENTOW4.48  [run-record]

**CANONICAL STATEMENT:** the two adopted machine rows, `[ASSEMBLED]` from lines 794–864. FR-G, verbatim (abridged):

> “* **FR-G — the first gauge-live partial side in any leg of this
>   unit (eta != 1, f2 = 2; no battery family has eta != 1).**
>   p = 3, Phi' = x^2−6 (genre (2,1,5), h = 1, eta = 2), inner
>   (e2,f2) = (1,2), u2 = 3, psi2 = Z^2+Z+2, mu2 = 2 on side [1,5]
>   of slope 3 — PARTIAL (4 < mu1 = 5), sibling g = x^2−15 at slope
>   4. Hand re-derivation of the keys this round: i(3) = 1, so
>   (W(0), W(1)) = (1, 0); c_0 = −2 ≡ 1, c_0·eta^{W(0)} = 2,
>   −2·nhat(6) = −2·27 = −54; the t = 1 term is gauge-blind
>   (−2·3x·Phi'). CORRECTED key Phi'^2 − 6x·Phi' − 54; NAIVE (the
>   composed S0 display) = same − 27. Committed numbers: sigma(naive
>   key) = {(4,1)} != {(2,2)} = sigma(corrected key) … at the NAIVE key both members' hulls
>   ((0,15)–(2,3)) have slope EXACTLY T2 = 6 — empty >T2 initial
>   segment, mu2* = 0, the tower class invisible; field floor:
>   corrected class rows 2·8 = 16, 2·7 = 14 > 12 = E2·e and
>   2·13 = 26 > 24, naive rows 2·6 = 12 and 2·12 = 24 exactly = E2·e
>   — GENTOW-1(d)'s separator collapses at the naive key.”

FR-M, verbatim in brief: “the first TWO-BLOCK partial member in any tower battery (q = 2, eta = eta2 = 1: gauge-clean …)”, `mu1 = 9, n = 18`, two inner sides A and B each carrying `(T+1)^2`, “both classes read through THEIR OWN keys with mu2* = 2 (LEMMA GENTOW-4.2's tie at TWO pure-power sides simultaneously — first exercise), c_g^A = 27 and c_g^B = 25 … (each class's c_g absorbs the other block's mass plus the sibling's: 20 + 7 and 20 + 5)”.

**FORM:** two bulleted adopted rows.

**DERIVATION:** `[RUN]` from a decorrelated fresh route, with the keys hand-re-derived at the round.

**CONDITIONALITY:** FR-G decides **on slopes alone by design** — no `coh()` contact at η ≠ 1 (`.30`). FR-M is gauge-clean and stresses geometry only.

**RESOLUTION TRACE:** lines 794–864.

**TEETH:** **ARITHMETIC AUDIT — FR-G, recomputed from the genre data:** `i(3) = 3 mod 2 = 1` ✓; `W(0) = ⌊2·1/2⌋ = 1`, `W(1) = ⌊1·1/2⌋ = 0` ✓; `nhat(6)` at `e1 = 2, h = 1` is `π^3 = 27` ✓; corrected constant `−(c_0·η^{W(0)})·nhat(6) = −2·27 = −54` vs naive `−1·27 = −27` ✓ — **the corrected/naive pair differs by exactly the factor η^{W(0)} = 2, matching the mechanism.** `E2 = e2f2u2 = 1·2·3 = 6` ✓, so the naive hull's slope `(15−3)/2 = 6 = T2` exactly ✓ — **an empty >T2 segment, hence μ₂* = 0, hence the class invisible: the failure mode is fully derivable from the displayed numbers.** Field floor: `E2·e = 6·2 = 12` and the naive rows sit at `12` and `24 = 6·4` exactly ✓ — the separator collapses to equality, as claimed. **FR-M:** `c_g^A = 20 + 7 = 27` ✓ and `c_g^B = 20 + 5 = 25` ✓ — both decompositions reproduce. Artifacts `gentow4_pe1_fresh.py` `5dc455dd…` and output `dac5110c…` both match ✓.

---

### EFF.GENTOW4.49  [fence]

**CANONICAL STATEMENT:**

> “**Battery blindness (disclosed).** All five sealed families sit at
> eta = 1 (P1/P2/P6: q = 2, Phi' = x^2−2, where eta = 1 forcibly —
> P2 the only f2 = 2 family; P3/P5: Phi' = x^2−3 over Q3, eta =
> res(x^2/3) = 1, and f2 = 1 anyway — verified at the sealed
> runner's PA/PB constants this round): the seal is structurally
> blind to the gauge seam. eta != 1 coverage on record: FR-G above
> plus the erratum lineage (frame X @ 59c1966/5f821dc;
> hetowr1_supp.py frames X/Z/W). No eta != 1 coh() row (the S4
> residual-digit read) exists in any leg yet — FR-G's members decide
> on slopes alone by design.”

**FORM:** bold-headed disclosure.

**DERIVATION:** `[RECORD]`, verified at the runner's own constants.

**CONDITIONALITY:** **the blindness is DOUBLE at three families**: P3/P5 are η = 1 *and* f2 = 1 (where corrected = naive automatically per `.05`). So even a hypothetical η ≠ 1 variant of those two would be gauge-blind.

**RESOLUTION TRACE:** lines 855–864.

**TEETH:** `hetowr1_supp.py` exists with md5 `dcb8452f…` — **the same instrument this queue verified for HETOW and GENTOW1**, a three-way shared η ≠ 1 leg ✓.

---

### EFF.GENTOW4.50  [instrument-record]  *(CHAIN-CLASSMASS — TERMINAL)*

**CANONICAL STATEMENT:** the m-ii acceptance-fold bracket, verbatim:

> “[acceptance fold (post-PE3) 2026-08-10, m-ii — INSTRUMENT-STRENGTH
> DISCLOSURE on the adopted PE2 machine rows above: the adopted
> instrument's class-degree-sum check is ONE-SIDED. Verified at the
> committed artifact itself (gentow4_pe2_fresh.py, keyval_checks,
> L281–300): the strict branch accumulates ncls = Sum e_·f_ over
> rows with 2v > E2·e and tests `chk(tag, ncls >= want_sum, …)` — a
> companion row misclassified ABOVE E2 would inflate ncls and still
> pass strict mode. The check is non-vacuous (its collapse branch
> emits a real violation — the m-D genre at one grade milder), and
> the committed output's parsed rows carry exact class masses, so
> the adopted FR-T/FR-C numbers stand; but those "GREEN" rows
> certify class degree-sum >= at strict separators, not ==. The
> sealed instrument's six degree-sum checks (8 = D2·mu2*, the m-D
> bullet below) and PE3's fresh instrument (gentow4_pe3_fresh.py
> L337: `ncls == want_sum`) test the sums TWO-SIDED; the == form is
> the standing shape for future frames.]”

**FORM:** dated acceptance-fold bracket at the §S9 head.

**DERIVATION:** a source reading of the adopted instrument, with the two-sided alternatives named.

**CONDITIONALITY:** SUPERSESSION KIND: **disclosed non-repair** — the adopted rows stand, but at a weaker predicate than a reader would assume. **The bracket also sets a standing shape: “the == form is the standing shape for future frames.”**

**RESOLUTION TRACE:** lines 929–944.

**TEETH:** **BOTH SOURCE CITATIONS VERIFIED at compile time.** `gentow4_pe2_fresh.py` line **281** reads `def keyval_checks(tag, lab, rows, E2, strict, want_sum):` — the function the bracket cites, at the stated line ✓, with its docstring confirming the strict/collapse structure. `gentow4_pe3_fresh.py` line **337** reads `        chk(tag, ncls == want_sum,` — **the two-sided `==` form, verbatim at the stated line** ✓. The bracket is accurate to both sources.

---

### EFF.GENTOW4.51  [changes-record]  *(SERIES MINORS-PE2, link 1; CHAIN-SUPPLY — TERMINAL) — QUEUE-CHARGED*

**CANONICAL STATEMENT:** the m-A rider. Its in-place form at S8.1, verbatim:

> “[rider (post-PE2, 2026-08-10; m-A): the two-item routing
> above is MISATTRIBUTED for the second item; re-derived at source
> this fold. LEMMA HE6R1-2 + RIDER: correctly routed — "LEMMA
> HE6R1-2's read" is ON LEMMA HE7-12(c)'s displayed transport list
> (HE7_PROOF §S5.8, verified verbatim this fold), and 4.1(c)'s
> proof walks exactly that consumption. ANNEX HE7-13': NOT on
> HE7-12(c)'s displayed list (the annex postdates it: ANNEX F-1 is
> 2026-08-09), and 4.1(c)'s proof body never mentions it. Its
> supply is by ITS OWN STATEMENT FORM: HE7-13' is stated at
> "Psi-tilde = Psi − W with W = 0 or as in LEMMA HE7-12(d)"
> (HE7_PROOF ANNEX F-1), and the restated LEMMA HETOW-2 gives
> Phi2 = Psi with w = 0 under the (LIFT)-slot form at any f1 — Phi2
> is literally in HE7-13''s hypothesis class at W = 0. This is the
> route the preceding "reads only the conclusion Phi2 = Psi − w"
> clause already half-states; the conclusion (4.1(c)'s full
> consumption supplied at the corrected key) is unchanged.]”

and its §S9 summary, verbatim:

> “* **m-A -> CORRECTED at the S8.1 supply audit.** The two-item
>   routing sentence misattributed HE7-13''s supply to HE7-12(c)'s
>   transport. Verified at source: HE7-12(c)'s displayed list
>   (HE7_PROOF §S5.8) carries "LEMMA HE6R1-2's read" — that leg is
>   right — but not HE7-13' (ANNEX F-1 postdates it). The bracket
>   states the true route: HE7-13' is stated at "Psi-tilde = Psi − W
>   with W = 0 or as in LEMMA HE7-12(d)", and the restated HETOW-2's
>   w = 0 (LIFT)-slot conclusion puts Phi2 in its hypothesis class
>   at W = 0 directly. Conclusion unchanged.”

**FORM:** an in-place dated rider at the audit site + a summary bullet in the fold record. **Both are emitted here as one unit** because the rider and its summary are the same act at two sites; the fold's own list names the site (`S8.1 x2`).

**DERIVATION:** a **source-level routing check**: HE7-12(c)'s displayed transport list was read verbatim, and HE7-13′ was found absent from it — with a DATING argument for why (ANNEX F-1 postdates HE7-12(c)).

**CONDITIONALITY:** SUPERSESSION KIND: **provenance-rider** — “Conclusion unchanged.” **What changes is the DAG edge**: 4.1(c)'s supply of ANNEX HE7-13′ does NOT run through HE7-12(c)'s transport; it runs directly through HE7-13′'s own hypothesis class at `W = 0`, which the restated HETOW-2 satisfies literally. **A consumer building the dependency graph from the r1 sentence would draw one wrong edge and miss one right one.**

**RESOLUTION TRACE:** the rider at lines 762–777; the summary at 946–954; the corrected target sentence at 757–761.

**TEETH:** disposition `AUDIT / in-house hostile pass` (PE2 found it) with a **source-verified re-derivation** (“HE7_PROOF §S5.8, verified verbatim this fold”). **The dating argument is independently checkable**: HE7's ANNEX F-1 is dated 2026-08-09 and HE7-12(c) predates it — consistent with `spec/EFF-HE7-s2of3.md`'s homing of ANNEX F-1 as a post-acceptance annex. **This is the queue's cleanest example of a correction that changes a DAG edge without changing a conclusion**, and it is exactly the class of defect a compilation must not smooth over.

---

### EFF.GENTOW4.52  [changes-record]  *(SERIES MINORS-PE2, link 2; CHAIN-COUNT — TERMINAL)*

**CANONICAL STATEMENT:** the m-B rider, in-place at S3(iii), verbatim:

> “[rider (post-PE2, 2026-08-10; m-B): "the three fullness
> rows" reconciled with the S2 [GT4-r1] FIVE-row recount, both
> re-verified against HETOW_RECON's S1 table this fold. The five
> fullness-consuming rows are HETOW-1's r-row plus HETOW-3's four
> (the §S1-CONVENTION Psi ∤ f_S peel row, the label row, the
> f_S/mu2 row, the level-1 Phi' ∤ f frame row). THREE are replaced
> as named here: the r-row and the label row by 4.1(a)(b), the
> f_S/mu2 row by (ii). The remaining TWO — the Psi ∤ f_S peel row
> and the Phi' ∤ f frame row — are discharged by 4.1(d)'s peels,
> in force at this theorem by its preamble ("after the S2 peels":
> Phi' ∤ f and Phi2 ∤ f assumed, and Phi2 ∤ f_S <=> Phi2 ∤ f per
> the (ii) proof's peel equivalence). No row is undischarged; the
> counts describe different partitions of the same five rows]”

**FORM:** in-place dated rider (+ a §S9 summary bullet).

**DERIVATION:** a row-by-row reconciliation of two counts against a third note's table.

**CONDITIONALITY:** SUPERSESSION KIND: **inventory completion** — neither count was wrong; they partition the same five rows differently. **The load-bearing addition is that the remaining two rows ARE discharged** (by 4.1(d)'s peels), which the composed text left implicit.

**RESOLUTION TRACE:** lines 353–365; summary 955–961.

**TEETH:** **ARITHMETIC AUDIT: 3 replaced + 2 discharged = 5 rows** ✓, and the five are named individually ✓. Cross-entry: the five rows are identifiable in `EFF.HETOW.09`'s transcribed S1 table — HETOW-1's r-row, and the four HETOW-3 rows (the §S1 CONVENTION row, the label row, the f_S/μ₂ row, the level-1 frame row) ✓ — **the reconciliation checks out against this queue's own compilation of the target table.**

---

### EFF.GENTOW4.53  [changes-record]  *(SERIES MINORS-PE2, link 3; CHAIN-MANIFEST — TERMINAL)*

**CANONICAL STATEMENT:** the m-C rider, verbatim:

> “[rider (post-PE2,
> 2026-08-10; m-C): the shape sentence is imprecise — re-checked
> `git diff d7ddf2e..eb526a0d` on this file this fold (265
> insertions, 14 deletions). At TWO disclosed sites the composed
> text did NOT stand and was corrected IN PLACE: (1) the S2 count
> word ("exactly THREE places" -> "exactly TWO places", the
> composed "THREE" preserved inside the [GT4-r1 (m-1)] bracket);
> (2) the S4 remark's parenthetical (the composed "(Δb is forced
> even; the x- and pi-relations have residue 1 at f1 = 1)" ->
> the corrected two-clause form, the bracket recording that the
> composed text said "at f1 = 1"). All 14 deletion lines sit at
> the manifest's disclosed sites (line re-wraps at bracket
> insertions plus these two rewrites); both original wordings are
> preserved inside their brackets, so the edits are auditable; at
> 4.1(c) and every other site the composed text stands. Statement
> displays untouched, re-verified.]”

**FORM:** in-place dated rider at the manifest (+ a §S9 summary bullet).

**DERIVATION:** a re-run of the manifest's own diff command, with the deletion lines accounted for site by site.

**CONDITIONALITY:** SUPERSESSION KIND: **replacement** of an imprecise edit-shape claim. **The correction preserves auditability**: both original wordings survive inside their brackets, so the in-place rewrites are still reconstructible.

**RESOLUTION TRACE:** lines 891–905; summary 962–967.

**TEETH:** `git cat-file -t d7ddf2e` and `git cat-file -t eb526a0d` both = commit ✓, so the cited diff is executable. **The two rewrites are visible in the effective text as claimed**: `.10` carries “exactly TWO places [GT4-r1 (m-1): "THREE" recounted …]” ✓ and `.29` carries the corrected parenthetical with “[GT4-r1: the composed parenthetical said "at f1 = 1", which is FALSE …]” ✓ — **both originals are preserved inside their brackets, exactly as the rider says.**

---

### EFF.GENTOW4.54  [changes-record]  *(SERIES MINORS-PE2, link 4; CHAIN-93 — TERMINAL)*

**CANONICAL STATEMENT:** the m-D rider, verbatim:

> “[rider (post-PE2, 2026-08-10; m-D): the raw
> "93 checks" count is PADDED — in the instrument's FR-M nfeltval
> loop the else-branch check `chk(tag, 4*v_ <= E2*e_, 'sep')` tests
> the very inequality that selected the branch, so it can never
> fire. Recounted this fold by an instrumented isolated /tmp copy
> (sealed file untouched; run reproduced GREEN 93/0): EXACTLY 14 of
> the 93 are such vacuous 'sep' confirmations (the non-class rows
> across FR-M's 3 members x 2 keys), so the falsifiable count is
> 79. The separator's substance is unaffected: the class side is
> tested strictly (ncls accumulates only at 4*v_ > E2*e_), and a
> misclassified non-class row moves the class degree sum off 8 =
> D2·mu2*, which the 6 degree-sum checks (3 members x 2 keys) test
> bidirectionally. The numbers this annex quotes from those rows
> (sigma, pins, c_g, keyvals, degree sums) are measured quantities,
> not products of the padded checks.]”

**FORM:** in-place dated rider at the adopted machine rows (+ a §S9 summary bullet).

**DERIVATION:** a **re-count by instrumented isolated copy**, with the sealed file untouched and the original verdict reproduced.

**CONDITIONALITY:** SUPERSESSION KIND: **counter re-reading** — 93 → **79 falsifiable**. **The substance argument is the important half**: the class side is tested strictly, and the 6 bidirectional degree-sum checks catch what the vacuous rows cannot.

**RESOLUTION TRACE:** lines 798–813; summary 968–974.

**TEETH:** **ARITHMETIC AUDIT: 14 vacuous = 3 members × 2 keys × ~2.33 rows** — the note attributes them to “the non-class rows across FR-M's 3 members x 2 keys”, and `93 − 14 = 79` ✓. The 6 degree-sum checks = 3 members × 2 keys ✓. **Disposition `disclosed vacuity` with the falsifiable remainder quantified — the strongest form of this disclosure in the queue** (compare `EFF.GENTOW3.50`, which discloses a dead branch but does not re-count).

---

### EFF.GENTOW4.55  [changes-record]  *(SERIES MINORS-PE2, link 5; CHAIN-GRADES)*

**CANONICAL STATEMENT:** the m-E summary, verbatim:

> “* **m-E -> REFRESHED at S7 BOX-4.** The supplier stack's stale
>   0/2s re-dated from the arc records: HETOW ACCEPTED 2/2,
>   GENTOW-1 ACCEPTED 2/2 (standing through R2a/b/c), HE6R1
>   ACCEPTED 2/2 — the staleness was conservative (understated
>   grades). The refresh PE1's sibling-lesson (6) had assigned to
>   the r1 annex lands here.”

with the fold's closing fence, verbatim:

> “Sealed artifacts BYTE-FROZEN: the four S8.4 md5s … re-verified before and
> after this fold; no runner edited, no committed artifact re-run
> in place. The statement fence: no theorem statement touched —
> every bracket sits in proof prose, audit records, or boxes.
> Counter HOLDS at 1/2 (a rider is not a pass). PE3 next.”

**FORM:** §S9 summary bullet + the fold's closing fence.

**DERIVATION:** `[RECORD]` of a grade refresh from arc records.

**CONDITIONALITY:** **“The statement fence: no theorem statement touched”** is the fold's own discipline claim, and it holds: all five minors land in prose, audits or boxes. The counter is superseded to 2/2 at `.56`.

**RESOLUTION TRACE:** lines 975–989.

**TEETH:** **all four S8.4 md5s re-verified at compile time** ✓. The three refreshed supplier grades are independently confirmed by this queue (HETOW `.46`, GENTOW1 `.59` at the same commit `4aff731`) ✓.

---

### EFF.GENTOW4.56  [acceptance-box]  *(SERIES ARC; CHAIN-GRADES)*

**CANONICAL STATEMENT:**

> “**GENTOW4 IS ACCEPTED 2/2** — passPE2 CLEAN (0 CRITICAL + 0 GAP +
> 5 MINOR, GENTOW4_passPE2_report.md @ 80280b66; counter 0/2 -> 1/2)
> followed by passPE3 CLEAN (0 CRITICAL + 0 GAP + 2 MINOR,
> GENTOW4_passPE3_report.md @ f0874ff9; counter 1/2 -> 2/2): two
> consecutive clean hostile passes, the standing acceptance bar.
> **THE NOTE IS FROZEN AT THIS RECORD …**”

with the arc's PE3 frames, verbatim:

> “-> PE3 CLEAN 2m @
> f0874ff9 (FR-3B the first THREE-BLOCK partial member anywhere,
> gauge-live, c_g = 39/37/27 with three simultaneous 4.2 ties +
> FR-Q the first f2 = 4 frame, W = (2,1,1,0), where the naive and
> carrier-but-wrong-datum teeth MERGE and mu2* = 0 still kills the
> naive read; the 4.C pin display tested as an EQUATION against
> explicit f_S at 11 members; the single run RED = the verifier's
> own disclosed KBN side-bet, a third carrier-but-wrong-datum
> instance).”

and the byte-freeze ledger, verbatim:

> “BYTE-FREEZE LEDGER (this round): pre-fold body md5
> eeb505576d990b1409f826acf54159ca (945 lines) = the rider state @
> 6e1a0f8c, the exact text passPE3 verified; the two fold brackets
> landed insertions-only (+44/-0; prefix through the first
> insertion, L423, byte-identical, md5 57fbeb69; commit bee0b56a),
> giving post-fold body md5 f96e23d01b194c49a04e513eda3cf3e0 (989
> lines) …”

**FORM:** bold-headed acceptance record with an arc and a freeze ledger.

**DERIVATION:** `[RECORD]` of two consecutive CLEAN passes.

**CONDITIONALITY:** none on the counter. **PE3's fresh frames reach three firsts**: the first three-block partial member anywhere, the first f2 = 4 frame, and the first `W = (2,1,1,0)` wrap profile.

**RESOLUTION TRACE:** lines 991–1037.

**TEETH:** **the freeze ledger is FULLY RECONCILED at compile time** (§1, F-2/F-3/F-4): `945 + 44 = 989` ✓; lines 1–423 hash to `57fbeb69…` ✓; lines 1–989 hash to `f96e23d0…` ✓. `git cat-file -t 6e1a0f8c`, `bee0b56a`, `f0874ff9` all = commit ✓. **ARITHMETIC AUDIT of FR-3B's three c_g values (39/37/27):** three simultaneous ties at three blocks — the note's own FR-M pattern (`.48`) shows each c_g absorbs the other blocks' mass plus the sibling's, and three distinct values are consistent with three distinct block masses. Not further checkable without the artifact; recorded as reported.

---

### EFF.GENTOW4.57  [changes-record]  *(CHAIN-MONIC — TERMINAL)*

**CANONICAL STATEMENT:** the TOWERRAT2-C annex. Provenance, verbatim:

> “*Provenance: post-acceptance decorrelated ratification run C
> (CODEX_TOWERRAT2_2026-08-10.md S4; session
> 019feb4c-3781-7ac2-96bc-40639ca426eb, model gpt-5.6-sol, outcome
> RATIFIED-WITH-ANNEX, 2 MINOR). Annex finding C-1 adjudicated REAL
> (display defect, MINOR) -> this correction, re-derived from this
> note's own displays; annex finding C-2 adjudicated ARTIFACT (the
> header grade lines are the frozen historical layer; the dated
> acceptance record above governs …). The
> acceptance (2/2) is untouched. This is a PURE dated append on the
> frozen body: pre-append full-file md5
> bf7e60d640f36365dac83979d1b6ea63 (1037 lines) …*”

The defect, verbatim:

> “**The defect, exactly.** THEOREM GENTOW-4.A(ii)'s display carries
> the parenthetical "(length M = floor(n/D2) >= mu2, top coefficient
> NOT monic — the partial-side signature)". The "top coefficient NOT
> monic" clause is false as written: f monic (S0 frame) and Phi2
> monic of degree D2 force, through the division algorithm that
> defines the Phi2-development, C_M monic of degree n − M·D2 — the
> 4.A proof itself carries the correct form … The note's own headline witness
> refutes the parenthetical in place: at PE2-P, C_2 = Phi' + 4 =
> x^2 + 2 (S1 battery table) — monic. Nor does the weaker reading
> "C_M is not the constant 1" serve as a partial-side signature: a
> partial datum with e2f2 | mu1 — e.g. (e2f2, mu2, mu1) = (2, 2, 6),
> so that e2f2·mu2 = 4 < 6 = mu1 and n = D'mu1 = 3·D2 — has exact
> division and C_M = 1.”

The display of record, verbatim:

>     “(length M = floor(n/D2) >= mu2; C_M monic of degree
>      n − M·D2 < D2, the constant 1 exactly when D2 | n; the
>      partial-side signature is n > mu2·D2 — the development is
>      not monic-of-length-mu2, S0's refusal criterion)”

**FORM:** dated append with provenance, defect, and a display of record.

**DERIVATION:** re-derived from the note's own frame: “PARTIAL means e2f2·mu2 < mu1, i.e. n = D'mu1 > D'e2f2·mu2 = D2·mu2, and M = floor(mu1/e2f2) >= mu2 follows.”

**CONDITIONALITY:** SUPERSESSION KIND: **replacement**, scoped to the parenthetical: “supersedes the parenthetical only; the surrounding (ii) clause is unchanged”. **TARGETS:** `.19`. The two adjacent consumers are checked to key on the corrected content, not the superseded clause.

**RESOLUTION TRACE:** lines 1039–1088.

**TEETH:** **THE REFUTATION IS DOUBLE AND BOTH HALVES RECOMPUTE.** (1) The note's own witness: `C_2 = Φ′ + 4 = x²−2+4 = x²+2`, **monic** ✓ (recomputed at `.08`) — **the S1 battery table contained the counterexample to the S3 parenthetical all along.** (2) The second-reading counterexample: at `(e2f2, mu2, mu1) = (2, 2, 6)`, `e2f2·mu2 = 4 < 6 = mu1` ✓ (partial), and `n = D'·6` with `D2 = D'·2` gives `n = 3·D2` ✓, so `D2 | n` and `C_M = 1` ✓ — **exact division at a genuinely partial datum, so “C_M ≠ 1” is not a signature either.** The corrected signature `n > mu2·D2` reproduces from `e2f2·mu2 < mu1` ✓. **FREEZE F-5 verified**: lines 1–1037 hash to `bf7e60d6…` ✓. Disposition `AUDIT / decorrelated-model audit`.

---

## 3. XREF verification ledger

### 3.1 Designation XREFs

| ID | Target | Check | count | Role |
|---|---|---|---:|---|
| X01 | `GENHN_PROOF_2026-08-08.md` | `GENHN-TOW-1` | **19** | the box; item (4) is this note's charge |
| X02 | `spec/HYPOTHESIS_LEDGER.md` | `HYP.144  \`GENTOW4-BOX-1/-2/-4\`` | 1 (L1136) | the ledger home of BOX-1/-2/-4; WHERE line pins L577–584, L585–590, L614–618 — **all three verified against this note's line numbers** |
| X03 | same | `HYP.68  \`GENTOW6-BOX-2\`` | 1 | links BOX-2 into the four-row μ≥3 count-layer family (HYP.139/142/144/68) |
| X04 | `CODEX_TOWERRAT2_2026-08-10.md` | exists | — | run C's record (`.57`) |
| X05 | `HETOW_RECON_2026-08-09.md`, `HE6R1_RECON_2026-08-08.md`, `HE7_PROOF_2026-08-08.md`, `HE6_PROOF_2026-08-08.md`, `GENTOW1_PROOF_2026-08-09.md` | all exist | — | the five consumed proof notes (`.04`) |

### 3.2 Commit and artifact pins (v3 rule 23)

| ID | Pin | Verified |
|---|---|---|
| P-01 | commits `8ae71864`, `80280b66`, `f0874ff9`, `2aa5b16`, `c8da214`, `c21b59e`, `c43505d`, `d7ddf2e`, `eb526a0d`, `aa92a9d4`, `abd25133`, `a6587325`, `6e1a0f8c`, `bee0b56a`, `59c1966`, `5335ae3` | **ALL SIXTEEN resolve** |
| P-02 | `gentow4_checks.py` `98cdd4a4…` | MATCHES; **also printed at artifact line 2, verified** |
| P-03 | `gentow4_checks_output.txt` `58f35305…` | MATCHES; `TOTAL: 1740 checks, 0 violations, 4.9 s` / `GREEN` |
| P-04 | `gentow4_pe1_fresh.py` `5dc455dd…`, output `dac5110c…` | BOTH MATCH |
| P-05 | `gentow4_pe2_fresh.py` `b4d795cb…`, output `8e404c4c…` | BOTH MATCH |
| P-06 | `gentow4_pe3_fresh.py` | EXISTS (md5 `74787ac0…`, compiler-supplied — the note pins no hash for it) |
| P-07 | `gentow4_pe2_fresh.py` L281–300 (`keyval_checks`) | **VERBATIM at L281** ✓ |
| P-08 | `gentow4_pe3_fresh.py` L337 (`ncls == want_sum`) | **VERBATIM at L337** ✓ |
| P-09 | `gentow4_checks.py` L871–878 (the even-p0 branch) | **VERBATIM at L871** ✓ |
| P-10 | the five text freezes | **ALL RECONCILED** (§1), including the deliberately-non-prefix F-2 |
| P-11 | `hetowr1_supp.py` (the shared η ≠ 1 leg) | EXISTS, md5 `dcb8452f…` — same instrument as HETOW/GENTOW1 |

### 3.3 Verified NEGATIVE edges

| ID | Check | count | Meaning |
|---|---|---:|---|
| N1 | `grep -cF 'GENTOW' GENHN_PROOF_2026-08-08.md` | **0** | item (4)'s box discharge AND the GENHN.B (CS-3) cite are both UNLANDED (`.40`) |

---

## 4. Effective supply / consumption ledger

| Obligation | Effective supply | Surviving fence | Protocol status |
|---|---|---|---|
| [GENHN-TOW-1] item (4): partial inner sides | `.18`–`.22` (4.A i–v) via `.11`–`.14` (4.1) and `.19` (the projection) | μ₂ = 2 only (BOX-3); σ-decision only (BOX-2); mixed-side tie boxed (BOX-1) | **DELIVERED, ACCEPTED 2/2, RATIFIED-WITH-ANNEX**; discharge UNLANDED (N1) |
| the PE2-P protected instance | `.06`, `.08`, `.31`, and P-2's machine row | — | **PRICED AND MACHINE-CHECKED** — “the box's protected instance now has a proved, machine-checked read” |
| the multiplicity tie | `.24` (pure-power sides, proved) | **mixed sides UNPROVED — BOX-1** (`.36`) | **PARTIAL**; retirable by a faithful-cite unit (ledger disposition) |
| the partial-side COUNT layer | not supplied | **BOX-2** (`.37`) | **OPEN — the binding residue** per HYP.144, in a four-row family |
| the corrected `chat_t` | `.05` | f2 = 1 ⟹ corrected = naive | **IMPORTED** |

---

## 5. NON-IMPORTS

**NI-1 — no consumed note is edited.** `.04`, `.40`; verified (N1).
**NI-2 — nothing about the DECISION is new.** `.07`: only two new obligations, both named.
**NI-3 — f_S is never exhibited.** `.20`: every decision input is computed from f's own development.
**NI-4 — the mixed-side tie is NOT derived.** `.25`, `.36`.
**NI-5 — no budget/count display at partial sides.** `.37`: “sigma-decision only in this unit.”
**NI-6 — “uniform in all of these” is WITHDRAWN.** `.38`.
**NI-7 — the coherent-digit display is η = 1-scoped.** `.30`: “no machine row in any leg yet exercises coh() at eta != 1.”
**NI-8 — (b) alone does NOT give the pin equality.** `.33`: it gives an inequality; equality needs vertices or (c).
**NI-9 — the adopted PE2 class-mass rows certify `>=`, not `==`.** `.50`.
**NI-10 — 14 of the adopted 93 checks are vacuous.** `.54`.

Accordingly **no edge is created** from this note to a mixed-side tie, to partial-side count laws, to μ₂ ≥ 3 partial towers, to η ≠ 1 residual-digit reads, or to any `==` class-mass certification from the adopted PE2 rows.

---

## 6. TEETH inverse inventory

### 6.1 Obligation → guarded units

| # | Row | Guarded units | Disposition |
|---:|---|---|---|
| 1 | P-1 parse gate | `.18`, `.32` | executable regression (117/117) |
| 2 | P-2 HEADLINE (σ = PARI, both routes) | `.20`, `.22`, `.06` | executable regression (117/117) — **prices the protected instance** |
| 3 | P-3 tie | `.24`, `.25` | **EMPIRICAL only at mixed sides, by preregistration design** |
| 4 | P-4 c_g + floors | `.19`, `.26`, `.28` | executable regression; **71 odd / 46 even = 117, both parities live** |
| 5 | P-5 field-floor separator | `.31` | executable regression, per factor per prime |
| 6 | P-6 windows | `.19` | executable regression (15 members × 2 lifts) |
| 7 | P-7 refine rows | `.22` | executable regression |
| 8 | T-1 FULLREAD | `.06` | **loud-failure tooth**, 117/117 |
| 9 | T-2 NOCG | `.28`, `.09` | executable regression, 49 kills — **with a disclosed hand-assembled direction** (`.44`) |
| 10 | T-3 SIBDROP | `.21`, `.18` | executable regression, 117/117 |
| 11 | T-4 WITHHOLD | `.34` | executable regression, 0 guesses |
| 12 | T-5 WRONGKEY | `.14`, `.21` | executable regression, 22/22 incl. the peel corner |
| 13 | T-6 NOTWIST | `.29` | executable regression, 8 kills — **the HETOW T-BADTWIST phenomenon here** |
| 14 | FR-G (η ≠ 1, first gauge-live partial side) | `.47`, `.48`, `.13` | **AUDIT / decorrelated frame** — slope layer only |
| 15 | FR-M (first two-block partial member) | `.48`, `.21` | **AUDIT / decorrelated frame** — first simultaneous double tie |
| 16 | FR-T / FR-C (PE2) | `.50` | **AUDIT / decorrelated frame**, with a one-sided class-mass disclosure |
| 17 | FR-3B / FR-Q (PE3) | `.33`, `.56` | **AUDIT / decorrelated frame** — three-block and f2 = 4 firsts |
| 18 | GENTOW4-BOX-1 | `.25`, `.36` | **OPEN, MATH** (HYP.144) |
| 19 | GENTOW4-BOX-2 | `.37` | **OPEN, the binding residue** (HYP.144) |
| 20 | GENTOW4-BOX-3 | `.38`, `.49` | **signed coverage disclosure** |
| 21 | GENTOW4-BOX-4 | `.39` | grade cap; supplier grades refreshed |
| 22 | TOWERRAT2 run C | `.57` | **AUDIT / decorrelated-model audit**, 1 REAL + 1 ARTIFACT |

**Zero-orphan check: 22 obligations, all mapped, 0 orphans.**

### 6.2 Arithmetic audit summary (v3 rule 22)

- **117 members** = 25+24+22+22+24 ✓; **1,740 checks / 0 violations** ✓ (artifact)
- **the diagnostic census** sums per family to 25/24/22/22/24 ✓ — all five exact
- **71 + 46 = 117** parity split ✓
- **PE2-P**: ten quantities incl. both polynomial identities ✓ (`.08`)
- **all five family menus** degree-consistent ✓ (`.32`)
- **FR-G**: `i(3) = 1`, `W = (1,0)`, `nhat(6) = 27`, corrected `−54` vs naive `−27`, `E2 = 6`, naive slope `= 6 = T2` ⟹ `mu2* = 0`, field floor `12`/`24` exactly at `E2·e` ✓ — **the entire failure mode re-derived**
- **FR-M**: `c_g^A = 20+7 = 27`, `c_g^B = 20+5 = 25` ✓
- **the tie**: `|S| = D'e2f2·mu2 = D2·mu2*` ⟹ `mu2* = mu2` ✓
- **the monic refutation**: `C_2 = x²+2` monic ✓; the `(2,2,6)` datum has `D2 | n` and `C_M = 1` ✓
- **m-B**: 3 replaced + 2 discharged = 5 rows ✓
- **m-D**: `93 − 14 = 79` ✓
- **the freezes**: `945 + 44 = 989` ✓, L423 prefix ✓, 989 ✓, 1037 ✓, and F-1's md5 + 31,014 bytes ✓

**Zero arithmetic discrepancies found.**

---

## 7. BOUNDARY SELF-AUDIT

### 7.1 The rule applied

Zero `\tag{`; smallest cuttable span. Lemma/theorem CLAUSES are units; the four boxes are units (the queue charge requires their exact wording); each folded minor is a unit (five distinct KINDs).

### 7.2 Boundaries drawn, arguable ones both ways

1. **The four boxes → four units (`.36`–`.39`).** *Required by the queue charge* (“compile exactly as left”) and independently right: HYP.144 homes three of them together but the ledger's WHERE line gives three distinct line ranges, so per-box emission is what makes the ledger cross-check possible.
2. **m-A emitted as ONE unit combining its in-place rider and its §S9 summary (`.51`).** *Arguable*: two sites, two units. *Chosen* because they are the same act — the fold's own list names the site (“S8.1 x2”) — and because splitting would put the DAG-edge correction in one unit and its statement in another.
3. **`.29` (the coherent-digit remark) kept whole with its in-place rewrite, and `.30` (the scope pin) split off.** *Chosen* because the rewrite is a correction INSIDE the derivation while the scope pin is a separate dated act with its own consequence for BOX-3.
4. **`.33` (m-i) and `.50` (m-ii) emitted at their bracket sites, not with the acceptance record.** *Chosen* because both are instrument/citation disclosures whose targets are elsewhere in the note (4.C's proof line; the adopted PE2 rows).
5. **`.08` (the worked PE2-P instance) kept separate from `.31` (§S5's full verification).** *Arguable*: they are the same instance. *Chosen* because `.08` is the S1 examples-first reading (laws read off) and `.31` is the S5 oracle-checked verification (laws confirmed) — different epistemic roles, and `.08` is where the monic counterexample lives.
6. **`.46`–`.49` (the S8.1 annex) split into seam / supply audit / machine rows / blindness.** *Chosen* because the supply audit is where m-A lands and the machine rows are where m-D lands — two different minors at two different sub-parts.

### 7.3 Merges deliberately NOT made

- `.36`/`.37` kept apart despite sharing HYP.144: the ledger marks BOX-2 alone as “the binding residue”.
- `.19`/`.23` kept apart: the parenthetical superseded by TOWERRAT2-C is in the statement, and the CORRECT form is in the proof — the annex turns on exactly that contrast.
- `.51`–`.55` kept as five units: five distinct SUPERSESSION KINDs (provenance-rider, inventory completion, replacement, counter re-reading, counter re-reading).

### 7.4 Rules that fought this genre

- **Rule 23 was decisive**: five text freezes including one that is *correctly* not a prefix. Without the `+44/−0` disclosure the F-2 pin would look like a failure; with it, the arithmetic closes. **This is the clearest case in the queue for pin verification being a reconciliation exercise, not a match test.**
- **Rule 18 (SUPERSESSION KIND) earned its place at `.51`**: m-A is a `provenance-rider` that changes a DAG edge while leaving the conclusion fixed — a kind that would be invisible under a flat “superseded by”.
- **Rule 22** surfaced that the note's own S1 table refutes its own S3 parenthetical (`.57`) — recomputing `C_2` was enough.
- **Rule 27 (`AUDIT`)** applies four times (FR-G/FR-M adoption, the two PE3 folds, run C), and three of those produce disclosures rather than repairs.

---

## 8. Deferred reconciliation obligations

1. **Two unlanded consumptions on GENHN — FOR-0c.** The item-(4) box discharge, and the GENHN.B (CS-3) partial-side rider's cite of 4.A(v), whose precondition (acceptance) is now met (N1).
2. **HYP.144 quotes the pre-m-E grades and the pre-acceptance self-grade — FOR-0d/ledger.** The ledger row states BOX-4 as “0/2 attempt … HETOW-1/2 (HETOW 0/2) and the HE6R1 0/2-grade annex stack”, which the m-E rider refreshed and which the acceptance record superseded.
3. **`gentow4_pe3_fresh.py` carries no md5 pin in the note — FOR-0b.** It is cited by line number (L337) but not hashed; the other four instruments are hashed. Compiler-supplied: `74787ac0…`.
4. **No η ≠ 1 `coh()` row exists in any leg — FOR-0d.** BOX-3's named gap; the residual-digit layer of S3(v) is unexercised at η ≠ 1.

---

## 9. Self-audit and OPEN-CALLS

### 9.1 Resolved compilation calls

- The effective-text rule separates r1's bracketed insertions from its **two disclosed in-place rewrites**, and both original wordings are located inside their brackets as m-C claims.
- **All five text freezes reconciled** — including the one that is deliberately not a prefix, whose `945 + 44 = 989` arithmetic closes exactly — and **six artifact md5s plus three source-line citations verified verbatim**.
- **The queue-charged m-A rider is compiled in full** (`.51`) with both its sites, its dating argument, and the DAG-edge consequence stated explicitly.
- **GENTOW4-BOX-1/-2/-3/-4 are reproduced exactly as left**, each with its HYP.144 (or HYP.68) ledger cross-reference quoted, and the ledger's three WHERE line-ranges verified against the note.
- Nine CHAINs with TERMINALs; five folded minors with five distinct KINDs.
- **Every number recomputed**, including the two independent halves of the TOWERRAT2-C refutation and FR-G's complete failure mode.

### 9.2 OPEN-CALLS

**OPEN-CALL 1 — two consumptions are unlocked and unlanded. FOR-0c.**
`.40` names both: the item-(4) box discharge in GENHN, and the GENHN.B (CS-3) rider's conditional cite of THEOREM GENTOW-4.A(v), which was gated on “after acceptance” and is now unblocked (`.56`). Verified unlanded (N1). The cite's own scope condition is already written: “for inner-mu2 = 2 partial leaves at pure-power sides — with GENTOW4-BOX-1 named at mixed sides.”

**OPEN-CALL 2 — is BOX-1 retirable as the ledger says? FOR-0d.**
`HYP.144`'s disposition reads “BOX-1 is retirable by a faithful-cite unit”, echoing the box's own “a faithful-cite unit in GENTOW2's pattern would retire it”. **Whether the corpus wants to spend a faithful-cite unit on Ore-II / FGMN Lemma 2.17 is a scheduling decision**, not a compiler call. Recorded because BOX-1 is the only box here with a named, concrete retirement path.

**OPEN-CALL 3 — the ledger row carries stale grades. FOR-0d/ledger.**
`HYP.144` quotes BOX-4's composed wording (0/2 self-grade; HETOW 0/2; HE6R1 0/2-grade annex stack). The m-E rider refreshed all three supplier grades to ACCEPTED 2/2 and the acceptance record moved the self-grade to 2/2. **A ledger consumer reading HYP.144 alone would carry four stale grades.** Direction is conservative in every case, so nothing downstream is over-claimed.

**OPEN-CALL 4 — the T-2 tooth is asymmetric by construction. FOR-0b.**
`.44`'s m-2 disclosure: in one of the two directions the wrong σ is a **hand-assembled representative INERT**, not a mutant-reader run through the trichotomy. The kills are PARI-adjudicated both ways, so the tooth fires honestly — but half of it does not exercise the reader. **Whether a future frame should run the mutant reader in both directions is an instrument-design question.**

**OPEN-CALL 5 — no η ≠ 1 `coh()` row exists. FOR-0d.**
The residual-digit layer of S3(v) is derived at η = 1 (`.30`) and no leg exercises it otherwise; FR-G's members decide on slopes alone by design. Since T-6 NOTWIST shows the cocycle correction IS load-bearing at η₂ ≠ 1, the untested combination (η ≠ 1 × residual-digit read) is the note's sharpest remaining machine gap.

### 9.3 Fidelity audit

- Every CANONICAL STATEMENT is verbatim, or `[ASSEMBLED]` (nine units: `.10`, `.15`, `.23`, `.29`, `.31`, `.34`, `.43`, `.44`, `.46`–`.48`), with `…` at every truncation.
- **The four boxes are reproduced without any abridgement**, per the queue charge.
- ASCII preserved. Three source tables emitted as tables; the two fixed-width ASCII blocks double-emitted per v3 rule 14.
- No quantifier, dictionary entry, pin, slope or σ tuple altered. Compiler-computed values appear only in TEETH fields, marked recomputed.
- 5 designation XREFs, 11 pin classes, 1 negative edge verified; **no designation invented**.

EFF-GENTOW4 COMPILED: 57 statements / 5 xrefs verified / 5 open calls
