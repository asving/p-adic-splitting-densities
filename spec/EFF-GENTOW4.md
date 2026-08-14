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
