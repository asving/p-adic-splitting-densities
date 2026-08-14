# EFF-HETOW — CANONICAL EFFECTIVE SPECIFICATION v2 (full compilation)

**COMPILED-BY: opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). CODEX CROSS-READ OWED (post-reset).**

## 1. Header

**Source note:** `lean/notes/openmath/HETOW_RECON_2026-08-09.md` (864 lines / 53,279 bytes).

**HEAD blob hash:** `7c15a1140ad1e8ef4bf73f44b4713210d29b1373` (fresh `git hash-object` at compile time; last touched by commit `9f29a28b`).

**Compilation context:** `docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md`, Stage 0a; governing template `spec/EFF_TEMPLATE_v2.md` AT HEAD (rules 1–28). IDs `EFF.HETOW.<nn>`, contiguous, in effective-text order.

**GENRE: TAG-SPARSE PROSE PROOF + SEALED-PREREGISTRATION NUMERICS + POST-ACCEPTANCE APPEND STACK.** `grep -c '\tag{'` = **0** over the whole note, so every statement boundary is a compiler choice; §7 is the mandatory BOUNDARY SELF-AUDIT. Three unit populations must not be conflated (v3 rule 19): **preregistrations** (the sealed runner's menus and teeth), **run-records** (§S6, §S7's supp verdict, the 2026-08-10 machine paragraph), and **proof units** (§S1–S3, LEMMA HETOW-4).

### FREEZE PREDICATES (v3 rule 21 — four, each with its own pin, each independently re-verified)

**FREEZE-1 (sealed-battery instrument freeze).** §S6: “sealed runner `hetow_checks.py` @ commit 1 = 2e5c4b1; no post-seal edit”. `git cat-file -t 2e5c4b1` = commit; the runner and both artifacts exist.

**FREEZE-2 (supp-leg instrument freeze).** §S7: “artifacts `hetowr1_supp_output.txt` / `hetowr1_supp_results.json`, BYTE-FROZEN; runner md5 dcb8452f…, output b52eb226…, results 58f1ce0c…”. **All three re-computed at compile time and all three match**: `dcb8452fba908aa668de188d9021cd8a`, `b52eb226f2507fe921c4aa9437c6c167`, `58f1ce0c88069366172d1a9335566736`.

**FREEZE-3 (text freeze at the 2026-08-10 append).** Its BYTE-FREEZE line: “pre-append body md5 254d1765 (254d176563c21bf2261699f9138e18b5) = commit e38df9f, 41,452 bytes”. **Independently reproduced at compile time**: the note's first **652** lines hash to `254d176563c21bf2…` and measure exactly **41,452 bytes**, and `git cat-file -s` on the `e38df9f` blob of this file returns **41452**. Three independent quantities agree.

**FREEZE-4 (text freeze at the 2026-08-12 absorption append).** Its BYTE-FREEZE line: “pre-append body md5 6ded277db84f9eefb43d46021ba9c7e2”. **Independently reproduced**: the note's first **834** lines hash to `6ded277db84f9eef…` (51,589 bytes).

A fifth, weaker freeze predicate is asserted of OTHER notes and is a NON-IMPORT, not a freeze of this note: “**Frozen-file discipline:** GENHN_PROOF and HE7_PROOF are NOT edited by this unit” (`.05`).

### Effective-text rule (DERIVED — the note states no single rule)

Four source facts fix it.

**(i) The r1 round was applied IN PLACE, at dated tags.** Front matter (lines 17–18): “Repairs landed in place at [r1 2026-08-09] tags”. So every `[r1 2026-08-09 …]` bracket inside §S1–§S6 is already-landed text and the wording it replaces is gone (unlike the LIFTCORNER genre, r1 does NOT quote its predecessor in most places; §S7 is the record of what changed).

**(ii) After PE2 the body is frozen and corrections are dated appends that supersede a QUOTED sentence.** The post-PE2 heading's own italic preamble (lines 545–546):

> “The [r1] body above is BYTE-FROZEN
> — each correction below supersedes its quoted sentence of record.”

**(iii) After PE3 the body including the C-riders is frozen.** Lines 611–612:

> “The body above (through rider C-A/C-B/C-C) is
> **BYTE-FROZEN as of this record — dated appends only.***”

**(iv) The 2026-08-10 append GOVERNS the S1 rows it names, and is itself append-only.** Lines 666–668:

> “the body above stays BYTE-FROZEN — this append GOVERNS the
> S1 rows it names.”

**EFFECTIVE TEXT = the note as written (r1 already landed), READ AS CORRECTED by the four dated append blocks in date order, each superseding exactly the sentence it quotes.** Where two appends touch the same object the later governs; the two collisions are tabulated below.

### Supersession CHAINS (v3 rule 25 — TERMINALs marked)

`[TABLE]`

| Chain | Layers, in source order | TERMINAL |
|---|---|---|
| **CHAIN-KEY (the composed key)** | sealed gauge-naive display (plain lifts ĉ_t, GENHN-T(b)′'s form) → **[r1 F-1]** WRAP-CORRECTED key `Φ₂ := Φ′^{e₂f₂} − Σ_t L_{(f₂−t)u₂}(c_t·η^{W(t)})·Φ′^{e₂t}`, HETOW-1/2 re-proved at it | **[r1 F-1]** (`.13`) |
| **CHAIN-CARRY (HETOW-2's F-2 paragraph)** | sealed “every carry sits at value > T₂” → **[r1 F-2]** re-derived accounting (stationary tail lands in B_t) → **C-A(i)** withdraws the junk exemplar; **C-A(ii)** re-scopes the closing HE7-12 licence to **w = 0** | **C-A** (`.43`) — pinned downstream as `HETOW-KEY-BRIDGE-C-A` |
| **CHAIN-MECH (the §S2 preamble's non-absorption sentence)** | “W(t) is non-linear in t, so no K₂^×-rescale absorbs it” → **C-B** corrects the REASON at f₂ = 2 (the operative pin is `W(f₂−1) = 0` against the monic normalization), conclusion unchanged at frames X/Z/W | **C-B** (`.44`) |
| **CHAIN-BOX3 (machine coverage)** | sealed BOX-3 (no η axis; “uniform in all of these” line) → **[r1 F-3]** adds the η-gauge axis and withdraws the uniformity line → **C-C** adds the f₂ ≥ 3 multi-wrap axis, mooted by frame V → **F-α** folds the e₂f₂ ≥ 4 row against frame S at μ₂ ≤ 2 | **F-α** (`.47`) |
| **CHAIN-J-D0 (the S1 normalizer row)** | sealed justification “unit-residue discrepancy in K₂^× only; σ-content twist-invariant per HE7 §S1 CONVENTION (J-D0)” → **LEMMA HETOW-4** proves the ratio exactly and **supersedes the row** → **T3 absorption** re-homes HETOW-4's clauses (c)/(d)/(b) in `(ABS-HE4)`/`(HE4-COB)`, leaving (a) source-local | **HETOW-4 as absorbed** (`.50`, `.53`, `.57`) |
| **CHAIN-GRADE** | “Attempt grade 0/2” (front matter, §S7) → **post-PE2**: 0/2 → **1/2 and HOLDS THERE** → **post-PE3**: 1/2 → **2/2 — HETOW ACCEPTED** → the 2026-08-10 ratification: “The 2/2 acceptance stands ANNOTATED, now with the annotation DISCHARGED at this note's own grade” | **the 2026-08-10 append** (`.48`) |

### SERIES declared (v3 rule 28)

**SERIES ARC** — the dated pass/repair chronology, one unit per dated entry: `.04` ([r1], from passPE1) → `.42` (post-PE2 corrections preamble, counter 0/2 → 1/2) → `.46` (post-PE3 acceptance, 1/2 → 2/2) → `.48` (2026-08-10 TOWERRAT-R1 ratification, CHALLENGE 3 GAP, annotation discharged) → `.57` (2026-08-12 S-2 absorption). The note's own one-breath statement of the first three links is quoted at `.46`.

**SERIES CORRECTIONS-PE2** — the three dated post-PE2 riders in source order: `.43` (C-A) → `.44` (C-B) → `.45` (C-C). They cure three distinct MINOR findings and have three distinct SUPERSESSION KINDs; merging them would lose the fact that only C-A has a downstream consumer pin.

**SERIES BOX3** — the machine-coverage box's four dated states: sealed → `[r1 F-3]` → `C-C` → `F-α`, compiled as one unit `.30` with the arc recorded inline (the box is a single ledger object whose NOT-exercised list grows), and cross-referenced from `.45` and `.47`. This is the one place this compilation folds a SERIES into a single unit; the reason is audited in §7.2.

### Scope split — THREE predicates (rule 7 + v3 rule 17)

**A. Mathematical absorption / supply SET.** Fixed by the title and §S3: **one reconciliation theorem (HETOW.A, four clauses), three bridge lemmas (HETOW-1/2/3), one derived minimal-degree fact (n_min = 12), and — post-acceptance — one further lemma (HETOW-4).** The claim shape is “literal instance”: the note supplies a TRANSLATION, not new σ machinery. Its own statement of that (lines 48–52):

> “What needs proof is only the
> TRANSLATION between GENHN's composed-carrier coordinates (normalizer
> monomials n̂, letter η₂, residual ψ₂) and HE7's level-2 coordinates
> (normalizers ϖ^mΦ′^s, letter β, residual r): bridge lemmas HETOW-1/2/3,
> all proved in §S2. No hypothesis of HE7.A fails; nothing is boxed.”

**B. Append / consumption PROTOCOL scope — what this note has LANDED elsewhere.** The note's own fence says nothing is landed on its two frozen suppliers (`.05`), and the consumption fold is deferred (HETOW-BOX-4). Verified at compile time:

- **LANDED — GENHN.** `grep -c 'HETOW' GENHN_PROOF_2026-08-08.md` = **7**. The GENHN-side seam IS recorded there, as the note claims (“The GENHN-side seam is recorded at GENHN_PROOF's dated erratum (2026-08-09…)”). XREF X07.
- **LANDED — GENTOW1.** `grep -c 'HETOW' GENTOW1_PROOF_2026-08-09.md` = **5**, including line 575 (“from HETOW PE1 F-1) is a pinned consumption of this note”) and line 612 (“**THE PINNED CORRECTED DISPLAY (per erratum 59c1966 + HETOW [r1]):**”). XREF X08. **This is a reverse consumption the note itself does not record.**
- **NOT LANDED — the [GENHN-HE(μ₂)] rewording.** HETOW-BOX-4 defers it (“a LATER fold”), and no such rewording exists in GENHN: no GENHN occurrence of `discharged-at-grade` (count 0, N2).
- **CONSUMED DOWNSTREAM — T2.** `HETOW-KEY-BRIDGE-C-A` is pinned in `T2_SIGMA_LADDER_MASTER_2026-08-12.md` at line 4246 (count ≥ 1) as a `(PINS)` row over HETOW span **[548, 569]** — the exact span of `.43`. Full consumer trace at `.43`.

**C. Inbound corrections RECEIVED.** Three sources: (i) the three in-house hostile passes PE1/PE2/PE3; (ii) the **decorrelated codex ratification** `CODEX_TOWERRAT_2026-08-10.md` (CHALLENGE, 3 GAP), which produced the note's fifth lemma; (iii) the **S-2 simplification pass**, which absorbed that lemma into T3. Class (ii) is the one that changed the mathematics: F-1 REAL → LEMMA HETOW-4.

### Resolution rules applied

1. `[r1 2026-08-09 …]` brackets are already-landed text; the sealed wording they replace survives only where §S7 or a C-rider quotes it, and is then DEAD.
2. Each dated append supersedes exactly the sentence it quotes; where an append re-scopes rather than replaces, the unit carries the original as CANONICAL STATEMENT and the re-scoping in CONDITIONALITY with its KIND declared.
3. **The `[TABLE]` in §S1 is a unit** (`.09`), transcribed row-for-row, with the two rows superseded from outside (the normalizer row and the (SLOT₂) row) carrying their post-HETOW-4 reading inline.
4. Numbers are recomputed from the committed artifacts, never transcribed: §S6's totals, §S7's supp verdict, the per-row census, and all four byte-freeze md5s.
5. **Quotations of OTHER notes are re-verified verbatim.** One fails and is recorded as a fidelity finding, not silently repaired (`.54`, OPEN-CALL 3).
6. LEMMA HETOW-4's statement is byte-frozen and authoritative even after the T3 absorption — the absorption append says so explicitly, and the unit records both citation routes.

### Quotation and table discipline

CANONICAL STATEMENTs are verbatim or explicitly `[ASSEMBLED]`; `…` marks truncation. The two source tables (§S1's instantiation map, §S6's per-row census block) are emitted as tables and flagged `[TABLE]`; the census block is rendered in the source as a fixed-width ASCII display inside prose, so per v3 rule 14 it is emitted TWICE — verbatim, then transcribed. No source display is prosified.

---
