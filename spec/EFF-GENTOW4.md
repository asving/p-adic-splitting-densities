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
