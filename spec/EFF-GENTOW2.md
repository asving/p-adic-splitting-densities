# EFF-GENTOW2 — CANONICAL EFFECTIVE SPECIFICATION v2 (template v3.1, rules 1–39)

## 1. Header

**Source note:** `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md` (1,525 lines / 91,755 bytes)

**HEAD blob hash:** `fd4e3c2e92426ca54a6815151e93addd8bd6ba42` (working tree clean at compile time — `git status --porcelain` on the file is empty)

**Compilation context:** `docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md`, Stage 0a. GENTOW2 is a **manifest-gap recovery**: the DAG draft found it dropped by the same manifest-generation defect that hit GENHN. It is load-bearing on three separate edges — it is the corpus's FGMN-cite carrier (`docs/TIGHTNESS_CENSUS_2026-08-11.md` row I-3: "the corpus's ONE load-bearing literature cite"), it supplies LEMMA GENTOW2-B″/B′ to T1/T3/T5 and the weld layer, and its S2 tower is the witness T1's r12 terminal-valuation binding and T1 battery check 10 both instantiate.

**Governing template:** `spec/EFF_TEMPLATE_v2.md` AT HEAD (all rules 1–39, v2 + v3 + v3.1). Full single-pass compilation — the note is 92 KB, above the ~80 KB sharding trigger of rule 9, but it is **tag-dense** (`\tag{}`-equivalent bold designations `[Q1]`–`[Q10]`, `(B-law)`, `(B-1)`, `(B-2)`, `(R-FGMN)`, `(R-repo)`, `(3)`–`(6)`, `(h-i)`–`(h-iv)`, `C-m1`/`C-m2`, `R3-1`–`R3-4`) and its append chain is strictly dated, so the boundary-choice risk rule 9 fences is absent. **Compiled as ONE full spec; not sharded.**

**COMPILED-BY:** opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). **CODEX CROSS-READ OWED (post-reset).**

### Effective-text rule

Unlike T4, this note carries an **explicit, repeated, literal** effective-text rule. It is stated first at the post-PE3 dated corrections (L1167–1169):

> “The body above is BYTE-FROZEN — each correction below
> supersedes its referenced text of record. Sealed machine artifacts
> untouched by this append.”

and re-declared at every subsequent append, e.g. the post-PE6 acceptance record (L1363–1364):

> “The note is FROZEN as of this record: dated appends only;
> statement displays and sealed artifacts byte-fixed.”

and the TOWERRAT-R3 annex (L1433–1435):

> “The 2/2 acceptance
> is unrevoked; the body stays BYTE-FROZEN; each item below GOVERNS
> the reading of its quoted sentence.”

**Therefore the effective text is: the body (L1–1156, i.e. S1–S10 as it stood at the post-PE3 freeze) read under every dated append's governing reading, appends applied in date order.** Inside the body the round brackets `[r1]`, `[r2]`, `[r3]` are **already applied in place** — the r1/r2/r3 repair rounds rewrote the body rather than appending to it (S9/S10/S11 are their records), so unlike T4 there is no span-by-span round replay to perform. Everything from L1157 onward is append-only supersession.

This is a **quoted** rule, not a derived one.

### FREEZE PREDICATES (rule 21 — four independent freezes, plus rule 35's acceptance-scope enumeration)

**FP-1 — TEXT FREEZE (acceptance).** L1358–1364:

> “**ACCEPTANCE 2/2 — GENTOW2 IS ACCEPTED.** PE6 came back CLEAN
> (0C/0G/1m; report `GENTOW2_passPE6_report.md` @ deba21b): the
> acceptance counter closed 1/2 -> **2/2** on two consecutive clean
> passes — PE5 @ 75923bc + PE6 @ deba21b — the note through the bar
> on its SECOND count (the PE3 clean was spent at the PE4 reset).”

Pin: `git cat-file -t deba21b` = commit ✓; `git cat-file -t 75923bc` = commit ✓.

**FP-2 — PREFIX BYTE-FREEZE INSTRUMENT (a SERIES of four, rule 28).** Each append declares the md5 of the body *as it stood before that append*, with a byte count. All four were **recomputed at compile time from the working tree** and all four match EXACTLY:

`[TABLE]`

| # | Declared prefix md5 | Declared bytes | Recomputed `head -c N \| md5sum` | Verdict |
|---|---|---:|---|---|
| BF-1 (post-PE5 rider, L1349–1351) | `399017ac32aac64e14c2bff5083c2c4d` = commit `d798529` | 78,190 | `399017ac32aac64e14c2bff5083c2c4d` | **MATCH** |
| BF-2 (post-PE6 acceptance, L1420–1423) | `8fce60f8992ab7b3964c5a65aec38cc5`, rider commit `188b894` | 82,457 | `8fce60f8992ab7b3964c5a65aec38cc5` | **MATCH** |
| BF-3 (TOWERRAT-R3, L1494–1496) | `e27b97f2f462d88370190f1aaa52042b` = commit `21293c8` | 86,321 | `e27b97f2f462d88370190f1aaa52042b` | **MATCH** |
| BF-4 (S-2 absorption, L1523–1524) | `69b71584e8a74e89479b067f66bfd491` | *(none declared)* | matches at byte **90,326** (= start of L1499) | **MATCH — byte count recovered by compiler search** |

**Disposition: PINNED, not AS-OF-PIN.** Rule 34's `AS-OF-PIN` class was designed for prefix-md5 declarations over append-only files that can no longer be rechecked (GENHN's four). GENTOW2's are different in kind: a *prefix* md5 over an append-only file is **permanently recheckable**, because appends never touch the prefix. All four re-verify today. BF-4 alone is degraded, and only in bookkeeping: it declares no byte count, so a checker must search for the length. Recorded as a MINOR inventory defect in §9 (OPEN-CALL 4), not as an unpinned claim.

**FP-3 — SEALED MACHINE-ARTIFACT FREEZE.** Declared independently at every repair round, e.g. S9 L1037–1040:

> “sealed machine artifacts byte-untouched this round
> (gentow2_checks.py, both run outputs, gentow2_pe1_fresh.py + its
> output — zero diffs under verification/openmath/ in the r1 commits)”

and S11 L1230–1232:

> “Sealed machine artifacts BYTE-UNTOUCHED this round; the
> PE4 fresh/decode artifacts are cited at their committed pins, not
> re-run.”

All 20 `gentow2_*` artifacts under `verification/openmath/` were verified to EXIST at compile time (§4.4).

**FP-4 — ACCEPTANCE-SCOPE ENUMERATION (rule 35).** The acceptance is scoped by three co-resident fences that any consumer of the 2/2 grade must quote alongside it:

1. **The theorem is scoped to the third stage.** S7 L965–972: “Scope of this note's theorem: the third stage (first live n = 16), which is what item (6) boxed”; depth ≥ 4 “NOT claimed here”.
2. **The (β) floor is a HYPOTHESIS, not a result.** S5 L312–314 makes `κ₃ > e₂f₂u₂` “an explicit HYPOTHESIS”; S7 L957–964 routes it to COR GENTOW-1.1 in GENTOW-1, “cites it AS IN-FLIGHT and does not re-derive it”.
3. **Rows 23–24 are DESCRIPTIVE, not consumed.** L1342–1347, the ledger gate of HYP.66/HYP.145 (unit `.78`).

The 2/2 grade covers the note's own statements at that scope and nothing beyond it. `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` row 6 records `GENTOW2 | CERTIFIED (batch-1 + RUN E discharge)`.

**FP-5 — POST-ACCEPTANCE RATIFICATION (a fifth freeze event, non-revoking).** TOWERRAT-R3's provenance line, L1430–1436: outcome `RATIFIED-WITH-ANNEX`, 4 MINOR, “The 2/2 acceptance is unrevoked”. Verified in `CODEX_TOWERRAT_2026-08-10.md` L56: `| GENTOW2 | **RATIFIED-WITH-ANNEX** | 4 MINOR | 4 REAL MINOR (hygiene) | R3 (batch) |`.

### Supersession chain inside the note

Nine dated appends supersede body text. Because a chain can have more than two layers, each is recorded in source order with its TERMINAL member marked (rules 25, 30).

`[TABLE]`

| Span | Frozen body text | Layer 1 | Layer 2 | TERMINAL |
|---|---|---|---|---|
| STATUS header's r1 bracket (L9–14) | “[r1 …; record in S9 … Grade stays 0/2; PE2 next.]” | C-m2 (post-PE3, L1196–1216) — the 3-bracket replacement | S11's own grade line; then the post-PE6 acceptance | **the post-PE6 acceptance record (`.80`)** for grade consumers; **C-m2's bracket block (`.70`)** for arc-history consumers |
| Consumption list of the restated LEMMA GENTOW2-B — **5 sites**: honesty box (L365), S5.1 clause-(4) bracket (L431), S11 item (ii) (L535 in PE6's census / body L1248), S5 proof step, S6 direction-of-fit (L938) | five mutually inconsistent inventories | post-PE5 `m1 CURE` (L1303–1331): “**the true consumption of the S5 proof's corrected step is B′(3) + B″**” over FOUR quoted forms | post-PE6 `[m-1] FOLD` (L1369–1383): the same reading governs over **FIVE** forms, the fifth being the S6 sentence | **the PE6 FOLD (`.81`)** — one TERMINAL, all consumer classes |
| S6.1 table rows | rows 1–22, byte-frozen | post-PE5 `m2 CURE` ADDS rows 23–24 by append (L1333–1341) | status disclosure (L1342–1347) fixes their grade at DESCRIPTIVE | **rows 23–24 at DESCRIPTIVE status (`.77`, `.78`)** |
| The three “w is not computed” sentences (body L411–413, L692–694, L1279–1280) | “not computed anywhere in the corpus” etc. | post-PE6 `w-DISCLOSURE DATED` bracket-riders (L1385–1418) | — | **the dated brackets (`.82`)**; the closed-form derivation stays open |
| (H-b) hypothesis-audit row's chain clause (body L924–925) | “— and Cor 6.4 needs only ‘a MacLane chain’, not optimality.” | TOWERRAT-R3-1 **STRUCK** (L1438–1449) | — | **STRUCK (`.86`)** |
| `digit(G)` token in B″ step (iv) (body L770–775) | “digit(Q₀) = digit(G) = res(ẑ(x₀))·res((N^d/M)(x₀))” | TOWERRAT-R3-2 governing reading (L1451–1463) | — | **R3-2's reading (`.87`)** |
| S5 proof opening's α display (body L342) | “**Proof.** Write α := e₃f₃(w₃...” | TOWERRAT-R3-3 completes it (L1465–1475) | — | **α := e₃f₃(w₃ + λ₃) (`.88`)** |
| Every occurrence of `ψ₂` | overloaded symbol | TOWERRAT-R3-4 disambiguation line (L1477–1492) | — | **ψ₂^FGMN / ψ₂^repo, per-site (`.89`)** |
| LEMMA GENTOW2-B″ display (6) + its corollary | S5.2, byte-frozen | S-2 absorption append (L1509–1521): absorbed as `(ABS-G2)` | — | **dual-cite: “consumers may cite either this display (6) or T3's (ABS-G2)” (`.92`)** |

Body-internal supersessions (already applied in place by r1/r2/r3, recorded here so a chapter cut does not re-open them):

`[TABLE]`

| Superseded body claim | Superseding text | KIND |
|---|---|---|
| “numbering verified against the arXiv v3 PDF at ledger 63091ce” (S1/S3/S6) | S6.1 PDF-provenance table (`.49`–`.52`) | replacement (r1 F1) |
| The `[W-2] graded-dictionary` provenance pointer for (B-2) | “the on-the-nose identification was FIRST MADE IN THIS NOTE” (`.29`) | provenance-rider (r1 F2) |
| The `y ↦ εy` fallback sentence | the true transformation law (`.31`) | replacement (r1 F3), the old sentence **deleted** |
| **(B-2) on the nose** — “the repo K₂-digit … equals the ε₂-normalized F₃-coordinate … ON THE NOSE” | **REFUTED** at letter-live grades; replaced by `u(β_t) = ϑ(t)·w^{f₃−t}` (`.28`, `.43`) | **withdrawal** (rule 29) — the claim becomes unavailable and is “CONSUMED NOWHERE” |
| The `(η₂ ↔ z₂)` identification parenthetical in (R-repo) | Prop 1.15 canonical evaluation + the LETTER FORMULA (`.33`, `.37`) | replacement (r2 F1) |
| B′(4) as “B-2 ⟺ u(β) = 1 at each grade the recipe uses” | per-grade restatement with consumed scope separated (`.34`) | scope-pin (r2 F4) |
| The h-step applying B-1 outside its `deg < D₂` scope | the Φ₂-division h-step, e₃ = 1 corner CLOSED (`.35`) | replacement (r2 F2) |
| “GENTOW5's LEMMA GENTOW5-A1 does NOT supply it” | “survives only for w; as a claim about the grade-variation it was WRONG” (`.40`) | **partial-withdrawal** (rule 36) — replacement display carried in `.40` |
| The `L1434` §6-header pin | `L1433` | replacement (r1 F5) |
| The `e₄-level data` label in S2's (e₃,f₃) row | FGMN (e₃,f₃) with m₄ = e₃f₃m₃ per eq (9) (`.05`) | replacement (r1 F6) |

### Scope of record — the mandatory three-predicate split (rules 7, 17)

#### A. Mathematical absorption/supply set

The note's own charge, L27–41, fixes what it takes on: item (6)(α) of `[GENHN-TOW-1]`, and nothing else of item (6). S7's residue statement (L949–979) closes it:

> “Item (6) = the iterated depth-≥3 carrier/slot/read (T(b)″). Its r3
> residue was (α) + (β):
>
> * **(α) — DISCHARGED here** (THEOREM GENTOW2-A(b)(c)(d) via FGMN
>   Cor 6.4; bridge LEMMA GENTOW2-B).
> * **(β) — rides item (1)** …”

Thus the mathematical supply set is exactly **one theorem (GENTOW2-A, five clauses), one bridge lemma (GENTOW2-B, restated), and two derived unit laws (GENTOW2-B′ with clauses (3)/(4)/(5), GENTOW2-B″ with display (6))** — four ledger statements, matching `docs/STATEMENT_LEDGER_2026-08-10.md` L295 exactly: “GENTOW2_PROOF_2026-08-09.md — commit `33f86204`, grade: ACCEPTED 2/2, 4 statements”. The number of *literature conclusions consumed* is **twelve statements + eq (14)** (S6's consumed list), of which **two are the theorem** — FGMN Thm 6.3 and Cor 6.4 — and the rest are supporting.

#### B. Consumption/append-protocol scope

**This note is the recipient, not the sender, of absorption appends.** It declares no dated append owed on any other note. The one absorption *of* it has LANDED, in-note, at L1501–1525 — the S-2 append. Verified positively:

- `grep -cF 'ABS-G2' T3_COCYCLE_TELESCOPE_2026-08-12.md` = **3** (the tag at T3 L520, the absorption-map row at T3 L908, the audit item at T3 L1195).
- `grep -n 'GENTOW2' runs/comp5/T3CC_output.log` → line 1 = `1. GENTOW2-B″ — PASS`. The consumption check the append cites has RUN and PASSED.

This is the reverse of T4's posture (whose two appends had NOT landed) and must not be read across: **GENTOW2's protocol scope is COMPLETE for the one absorption it records.**

Two protocol debts remain, both minor and both external: `docs/TIGHTNESS_CENSUS_2026-08-11.md` row O-14 (`RIDER-DEBT`) lists “GENTOW2's 4 ratification hygiene minors (#17)” as display debt — which the TOWERRAT-R3 annex at L1427–1498 **has since landed**, making that census row STALE (§8 item 2); and row I-3 records the stage-two obligation to declare the FGMN cite as an axiom with an `AXIOM_FAITHFULNESS` entry (§8 item 1).

#### C. Inbound corrections received (rule 17)

`[TABLE]`

| From | What landed here | Where |
|---|---|---|
| `GENTOW2_passPE1_report.md` @ 61daa69 | F1–F6 (2 GAP, 4 MINOR) | S9, L1033–1080 |
| `GENTOW2_passPE2_report.md` @ aff457c | F1–F4 (2 GAP, 2 MINOR) | S10, L1082–1155 |
| `GENTOW2_passPE3_report.md` @ 92ac16b | 2 MINOR → C-m1, C-m2 | L1157–1216 |
| `GENTOW2_passPE4_report.md` @ 2f95be6 | F1 (GAP — **B-2 refuted**), F2 (MINOR) | S11, L1218–1287 |
| `GENTOW2_passPE5_report.md` @ 75923bc | 2 MINOR → m1 CURE, m2 CURE | L1289–1354 |
| `GENTOW2_passPE6_report.md` @ deba21b | 1 MINOR → the `[m-1]` FOLD | L1369–1383 |
| `CODEX_TOWERRAT_2026-08-10.md` §S4 (Codex, session `019fe98f-1e70-7321-9422-de37059d2b46`) | R3-1…R3-4, 4 MINOR | L1427–1498 |
| S-2 simplification pass (`T3_COCYCLE_TELESCOPE_2026-08-12.md`) | the (ABS-G2) absorption record | L1501–1525 |

All seven report files and `CODEX_TOWERRAT_2026-08-10.md` exist under `lean/notes/openmath/` (§4.4).

### Resolution rules applied

1. The body is the post-PE3 frozen text; the r1/r2/r3 brackets are IN the body, not appended to it, so no round replay is performed. Only L1157→ appends supersede.
2. **(B-2) is dead, not merely doubted.** Every clause of the effective text that once consumed it now consumes `B′(3) + B″` instead, and the note says so twice: “u ≡ 1 (= B-2 on the nose) is REFUTED letter-live (honesty box) and is consumed NOWHERE in the repaired note” (L702–703). The (B-2) text is retained in the effective text as a **refutation record**, not as a live hypothesis.
3. **The consumption-list unification is TERMINAL and single.** Five body sentences name different `B′`-clause inventories. The PE6 FOLD (`.81`) governs all five with ONE reading: **the S5 proof's corrected step consumes B′(3) + B″**, with B′(4) surviving at exactly one consumer (the restated lemma's per-height-iff sentence) and B′(5) reclassified as a restatement, not a dependency. A chapter cut must install this reading; the five body sentences are byte-frozen and will otherwise disagree.
4. **The `w`-sentences are re-read, not corrected.** The post-PE6 brackets record that `w` is now MEASURED at four frames / six primes, while the closed-form derivation stays open. The frozen sentences saying “not computed anywhere in the corpus” therefore carry `STALE-SELF-DESCRIPTION` (rule 26) in CONDITIONALITY, not `superseded`.
5. **R3-1's strike is a `withdrawal`, and it is CONSERVATIVE, not corrective.** See OPEN-CALL 1: the struck clause was *source-accurate* against FGMN Def 3.1 (L613–615 distinguishes “MacLane chain” from “optimal MacLane chain”). The strike removes a true-but-unneeded claim; nothing downstream weakens, because S4 supplies an optimal chain anyway. The compiler records the strike as governing and the source reading as a note.
6. **The two S4 `ψ₂` sites are fenced individually** per R3-4: L252's display reads `ψ₂^FGMN`; the consumption note reads `ψ₂^repo`. No unit may carry an unqualified `ψ₂`.
7. **`ABS-G2` is a dual-cite, not a relocation.** The absorption append's own fence: “The S5.2 statement here stays byte-frozen and authoritative; consumers may cite either this display (6) or T3's (ABS-G2).” Both edges are live.
8. Pin line numbers, byte offsets, commit hashes, artifact filenames, and all four prefix-md5s are **independently re-verified at compile time** against the working tree (§4).
9. `GT`-style instance names do not exist here — GENTOW2 assigns no note-local instance name to any absorbed conclusion, so there is no analogue of T4's `GT3-THRESHOLD`/`GT6-CERT-TOP` negative-edge check.

### Quotation and prosification discipline

All source displays and tables below are reproduced as quotations or marked `[ASSEMBLED]`. Every source table is marked `[TABLE]`. The two ASCII-block displays (the FGMN chain at L69 and the ϑ-factorization at L401) are emitted verbatim as source displays (rule 14 double-emission applies only where a *table* is rendered as ASCII; neither of these is a table). No source display or table has been prosified. Truncation inside a quotation is marked with an explicit ellipsis. Compiler classifications `[IMPORTED]`, `[DEFINITIONAL]`, `[DERIVED]`, `[RECORD]`, `[REFUTED]`, `[STRUCK]` are metadata, not source paraphrases.

---

## 2. NON-IMPORTS

GENTOW2's negative fences are unusually load-bearing for the DAG because the note is a **cite carrier**: the whole point is that FGMN supplies the theorem and the repo supplies only a bridge. Every fence below is a place the DAG must NOT draw an edge.

**N-1 — the cite prices no σ and no count.** S6 “What the cite does NOT give”, L942–944:

> “(i) It does not price any σ or
> count: it feeds T(b)″'s ascent inputs only.”

**N-2 — the depth-3 node floor is NOT supplied.** Same passage, L944–946:

> “(ii) It does not supply
> the depth-3 node floor κ₃ > e₂f₂u₂ (item (6)(β)): positivity of λ₃
> is a HYPOTHESIS of the augmentation and its provenance at tower
> leaves is item (1)'s composed entry budgets.”

The floor is an **explicit hypothesis of LEMMA GENTOW2-B** (L312–314: “the positivity is the [r1]-style node-floor arithmetic, here an explicit HYPOTHESIS”), and TOOTH T1 in the machine battery exists precisely to make a floor breach visible (`.60`, `.64`).

**N-3 — GENHN-2′ and the slot grammar are NOT proved here.** L946–947:

> “(iii) It does not prove
> GENHN-2′ or the slot grammar — those are accepted corpus.”

**N-4 — no FGMN statement is stretched; the direction of fit is one-way.** S6 L935–940:

> “The citation is consumed in the DEDUCTIVE
> direction only: FGMN theorem → our instance. No repo lemma is used
> to justify an FGMN statement. The repo-side inputs — B-1 and [r3]
> the derived unit laws B′(3)–(5)/B″ (B-2 itself refuted and consumed
> nowhere) — enter only the bridge LEMMA GENTOW2-B (the recipe
> realizes (ii) at ψ₃^{(w)}), never the citation's own hypotheses.”

(The `B′(3)–(5)` inventory in this very sentence is the FIFTH consumption-list site; read under the PE6 FOLD, unit `.81`.)

**N-5 — the excluded preprint.** S6 L828–829:

> “NOT
> the excluded 2212.00294; no statement from 2212.00294 is consumed.”

**N-6 — `w` is CONSUMER-INVISIBLE, and no clause consumes its value.** L694–697:

> “and w is CONSUMER-INVISIBLE (it acts by the
> grade-covariant substitution y ↦ wy, preserving factor patterns;
> GENTOW2-A consumes only hypothesis (ii) with an admissible
> residual, and ψ₃^{(w)} is admissible).”

**N-7 — the ϑ ↔ GENTOW5-A1 correspondence is NOT consumed.** L699–702:

> “Whether ϑ
> literally coincides with GENTOW5-A1's ϑ_t (that note's arc is in
> flight) is left to that arc — nothing here consumes the
> correspondence.”

This is the corpus's most consequential GENTOW2 non-import, because **downstream notes have since adjudicated exactly that correspondence, and as an INVERSE** (§4.3 / OPEN-CALL 2).

**N-8 — depth ≥ 4 is NOT claimed.** S7 L965–972:

> “those are the item-(2)
> inner-refine-transfer territory at depth ≥ 4 and are NOT claimed
> here. Scope of this note's theorem: the third stage (first live
> n = 16), which is what item (6) boxed.”

**N-9 — rows 23–24 are NOT consumed.** L1342–1347:

> “Status disclosure: rows 23-24 enter at DESCRIPTIVE /
> record-interpretation status, not consumed status — the S5 / S5.1
> / S5.2 proofs do not rest on either; a future round elevating
> either cite to consumed status owes the S6.1 two-leg method
> (layout pin + fresh visual read) at that point, per the
> faithfulness standard rows 20-22 met.”

**N-10 — the r3 round's own not-claim list.** S11 L1275–1281, four items, reproduced in full at unit `.74`.

**N-11 — the S-2 absorption takes the CONCLUSION only.** L1517–1520:

> “The absorption is of the CONCLUSION only: the source-local read package
> remains this note's supply, and neither the displayed B-law nor a
> one-w family is an input to the T3 instance (T3 §3's fence).”

T3's own side of the fence, verified at `T3_COCYCLE_TELESCOPE_2026-08-12.md` L143–145: “T3 does **not** cite that conditional conclusion as a premise for `[GENTOW5-W(i)]` … This prevents circular use of the theorem being absorbed.”

Accordingly: **no edge is created** from GENTOW2 to the σ/count layer, to the (β) node floor, to GENHN-2′ or the slot grammar, to depth ≥ 4, to any `w`-value claim, to GENTOW5-A1's ϑ_t, or to rows 23–24's content.

---

## 3. Statement inventory

**93 units**, contiguous, in effective-text order (body first, then the append chain in date order).

### EFF.GENTOW2.01  [record — status/arc]

**CANONICAL STATEMENT:**

**FORM:** display (bold block, the note's opening STATUS box)

> “**STATUS: COMPOSED, item (6)(α) PROVED-VIA-CITE (THEOREM GENTOW2-A +
> LEMMA GENTOW2-B), battery GREEN (41 checks/0 violations, teeth T1 +
> T2′ fired; T2 = disclosed failed design). Grade 0/2 (attempt; hostile
> arc later). Unit: GENTOW-2, BOX-CLOSURE campaign.”

**DERIVATION:** `[RECORD]` The composition-time self-description.

**CONDITIONALITY:** **STALE-SELF-DESCRIPTION** (rule 26). “Grade 0/2 (attempt; hostile arc later)” is falsified by the note's own later history — six hostile passes ran, and the acceptance record closed 2/2. The sentence is not corrected under the freeze; the reader must be told it is no longer true. The battery figure (41/0, T1 + T2′) is NOT stale — it matches `gentow2_checks_output_run2.txt` exactly (§4.4).

**RESOLUTION TRACE:** statement lines 5–8. Correction sites: C-m2 (L1196–1216) replaces the *bracket* that followed; the grade line itself is superseded by `.80`.

**TEETH:** S8 battery verdict row (`.63`).

**TARGETS:** superseded for grade purposes by `.80`.

---

### EFF.GENTOW2.02  [changes-record — the arc brackets, SERIES member 1]

**CANONICAL STATEMENT:**

**FORM:** bracketed rider

> “[r1 2026-08-09, post-PE1 repair round: F1 PDF-provenance leg CLOSED
> (S6.1 table; arXiv fetch bit-identical), F2 B-2 partially derived +
> honestly re-attributed (LEMMA GENTOW2-B′, S5.1), F3 fallback clause
> corrected to the true transformation law, F4/F5/F6 minors cured;
> record in S9. Sealed machine artifacts untouched. Grade stays 0/2;
> PE2 next.]
> [r2 → PE3 → rider arc: see C-m2's superseding bracket in the dated
> corrections section.]
> [r3 2026-08-10, post-PE4 repair round (report @ 2f95be6, NOT CLEAN:
> 1 GAP + 1 MINOR): F1 B-2 REFUTED at letter-live grades by the PE4
> machine contact and FLIPPED to the measured cocycle form — LEMMA
> GENTOW2-B restated via the multiplicative prescription, u ↔ ϑ
> adjudicated as LEMMA GENTOW2-B″ (S5.2, PROVED); F2 Lemma 3.13(1)
> folded into the consumed inventory. ACCEPTANCE COUNTER RESET:
> 1/2 → 0/2 (the PE3 clean pass is spent; two consecutive clean
> passes required from here). Record in S11. Sealed machine
> artifacts untouched. Grade stays 0/2 (attempt); PE5 next.]**”

**DERIVATION:** `[RECORD]` Round-by-round arc log.

**CONDITIONALITY:** the r1 bracket is explicitly superseded by C-m2 (`.70`) — the r2 bracket line says so in place. The r3 bracket's terminal grade line (“Grade stays 0/2 (attempt); PE5 next”) is superseded by `.70` then `.74`.

**RESOLUTION TRACE:** lines 9–25. Correction sites: L1196–1216 (C-m2), L1291–1302 (PE5), L1358–1367 (PE6).

**SERIES:** ARC-SERIES, member 1 of 6 — `.02` (r1/r2/r3 in-header brackets) → `.70` (C-m2's three-bracket replacement, post-PE3) → `.71` (S11's r3 record) → `.75` (PE5 outcome) → `.80` (PE6 acceptance) → `.85` (TOWERRAT-R3 ratification). Order is chronological and is the order a merge run must reconstruct.

**TEETH:** none (record unit; guarded by §7).

---

### EFF.GENTOW2.03  [scope record — the charge]

**CANONICAL STATEMENT:**

**FORM:** bold-headed paragraph

> “Charge (BOX-CLOSURE item (6), LITERATURE-FIRST): the r3 T(b)″
> attempt (commit 08ec526, GENHN_PROOF S9.1 [GENHN-TOW-1] item (6))
> derived the iterated data (ladder normalizers n̂₂(m) = π^a x^i Φ′^b;
> iterated key Φ₃ = Φ₂^{e₃f₃} − Σ_t k̂_t Φ₂^{e₃t}) and left ONE hole,
> (α): the Φ′-adic development of Φ₃ is ONE-SIDED of slope κ₂ with
> residual a ψ₂-power — true at the constructed witnesses, unproved.
> This note discharges (α) from the local FGMN print
> (docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt; [r1]
> provenance: the 12 consumed statements + eq (14) verified against
> the arXiv v3 PDF itself by visual page read — 13-row table in S6.1,
> local PDF bit-identical to arXiv's serving copy, fetch disclosed
> there; the source is arXiv 1305.0775v3, Fernández–Guàrdia–Montes–
> Nart, "Residual ideals of MacLane valuations" — NOT the excluded
> 2212.00294).”

**DERIVATION:** `[IMPORTED]` The hole is GENHN's, quoted at XREF R01: `GENHN_PROOF_2026-08-08.md` L1419–1423 reads “both displayed: (α) the level-by-level ascent that forces a / Φ₃-root ξ's intermediate data — v(Φ′(ξ)) = u₂/(e₁e₂) exact with / η₂(ξ) a ψ₂-root, the input (ii)'s slot lemma needs at ξ — needs / the Φ′-adic development of Φ₃ to be ONE-SIDED of / slope κ₂ with residual a ψ₂-power.” Exact 5-line span match. `git cat-file -t 08ec526` = commit ✓.

**CONDITIONALITY:** none — this is the note's charge, not a claim.

**RESOLUTION TRACE:** lines 27–41. The `[r1]` provenance clause is r1's in-place repair of the pre-repair ledger pointer; correction site S6.1 (L839–893).

**TEETH:** S6.1's 22-row provenance table (`.52`); the S8 witness inventory (`.64`).

---

### EFF.GENTOW2.04  [scope record — the STEP-1 verdict]

**CANONICAL STATEMENT:**

**FORM:** bold-headed paragraph

> “**YES.** The needed statement is an instance of **FGMN Theorem 6.3 +
> Corollary 6.4** (one-sidedness of N_i(F) at EVERY intermediate level
> i of the MacLane chain, with the residual power law R_{i−1}(F) =
> ψ_{i−1}^{ℓ_i} and the exact intermediate values µ(φ_i) = v(φ_i(θ))),
> applied with F = φ = Φ₃ once Φ₃ is a key polynomial for the tower's
> terminal inductive valuation ν. The key-polynomial certificate for
> the T(b)″-recipe Φ₃ is **FGMN Lemma 5.3(2)** via the degree-forcing
> argument displayed inside the proof of **Theorem 5.8** (itself fed by
> **Corollary 4.12**, whose construction g = φ_r^{e_r f} + g₀ IS the
> recipe's shape). One bridge clause is repo-side and is proved below
> from the accepted corpus (S5): the recipe's level-3 residual read
> [r3: R_ν(Φ₃) = ψ₃^{(w)}, the target up to the consumer-invisible
> w-substitution, under the multiplicative prescription — the naked
> per-height form R_ν(Φ₃) = ψ₃ was machine-refuted at letter-live
> grades, PE4 F1/honesty box] — GENHN-2′'s digit grammar + FGMN's
> additivity (Cor 4.7(1)) + eq (14) + the S5.1/S5.2 unit laws. No FGMN statement is stretched: the quotes,
> the instantiation map, and the faithfulness paragraph are below.”

**DERIVATION:** `[RECORD]` The verdict is a routing statement; its content is discharged at `.20`–`.24` (the theorem) and `.25`–`.46` (the bridge).

**CONDITIONALITY:** the level-3 residual read is `ψ₃^{(w)}`, NOT `ψ₃` — the `[r3]` bracket is in-place and governs. Consumers reading “the recipe realizes ψ₃” without the `(w)` are reading pre-r3 text.

**RESOLUTION TRACE:** statement lines 44–60; proof lines 187–373 (S4 + S5); correction sites lines 55–58 (the in-place `[r3]` bracket), and the r1 repair of “verified at ledger 63091ce” at lines 108–110.

**TEETH:** the whole S8 battery; PE4's A-route 27/27 (`.24`).

---

### EFF.GENTOW2.05  [table — the tower ↔ MacLane-chain dictionary]

**CANONICAL STATEMENT:**

**FORM:** display + `[TABLE]`

Source display (the FGMN chain, ASCII):

>     µ₀ −(φ₁,λ₁)→ µ₁ −(φ₂,λ₂)→ µ₂ −(φ₃,λ₃)→ µ₃ = ν,   r = 3,

Source table, transcribed:

`[TABLE]`

| repo object | FGMN object | witness value (genre (2,1,4)→(2,1,2), 3rd stage) |
|---|---|---|
| base key x, slope h/e₁ | φ₁ = x, λ₁ = h/e₁ | λ₁ = 1/2 (e₁ = 2, h = 1) |
| level-1 key Φ′ | φ₂ | Φ′ = x² − 2 |
| composed key Φ₂ | φ₃ | Φ₂ = Φ′² − 4x |
| iterated key Φ₃ | the key φ ∈ KP(ν), φ ≁_ν φ₃ | Φ₃ = Φ₂² − 16Φ′ |
| ψ₂ (residual of Φ₂'s Φ′-read, = minpoly(η₂)) | FGMN ψ₂ = R₂(φ₃) = minpoly(z₂) (Cor 5.6(2)); canonically z₂ = η₂·z₁^{−⌊ℓ₁u₂/e₁⌋} (S5.1 LETTER FORMULA) [r2, PE2 F1: equal to the repo ψ₂ up to the z₁-twist; on the nose when z₁^{⌊ℓ₁u₂/e₁⌋} = 1, e.g. f₁ = 1 over q = 2] | T + 1 (f₁ = 1, q = 2 ⟹ z₁ = 1: twist trivial) |
| ψ₃ (stage-3 residual) | the prescribed ψ, R₃(Φ₃) = ψ | T − 1 |
| repo e₂, f₂ | FGMN e₂ = denom(e(µ₁)λ₂), f₂ = deg ψ₂ | 2, 1 |
| repo e₃, f₃ | FGMN (e₃, f₃): e₃ = e(µ₃)/e(µ₂) = denom. data of the λ₃-augmentation, f₃ = deg ψ₃ = [F₄:F₃]; the pair with m₄ = e₃f₃m₃ per eq (9) (PDF pp.15–16) — deg Φ₃ = m₄. [r1, PE1 F6: the pre-repair label "e₄-level data" named the F₄ residue-field LEVEL and was undefined; witness re-derivation: ν(Φ₂) = 21/8, denom 8 = e(µ₃) over e(µ₂) = 4 gives e₃ = 2] | 2, 1 |
| u₂ = dv₂(Φ′) | e(µ₂)(w₂ + λ₂), w₂ = µ₁(φ₂) | 5 |
| v(Φ′(ξ)) = u₂/(e₁e₂) | µ(φ₂) = w₂ + λ₂ (Cor 6.4) | 5/4 |
| κ₂ (repo Φ′-side slope) | e(µ₁)(w₂ + λ₂) | 5/2 |
| κ₃ (repo Φ₂-side slope) | e(µ₂)(w₃ + λ₃), w₃ = µ₂(φ₃) | 21/2 |
| dv₁, dv₂ ladders | e(µ₁)·v, e(µ₂)·v | 2v, 4v |

**ARITHMETIC AUDIT (rule 22 — computed fresh at compile time, not read off the note's labels).** Every witness value is internally derivable and every derived quantity agrees, including the four numbers the parent charge names (u₃ = 21, e₃ = 2, e(µ₂) = 4, e(µ₃) = 8) and the SPAN IDENTITIES that connect them:

`[TABLE]`

| Identity | Substituted | Result | Source of the constraint |
|---|---|---|---|
| e(µ₁) = e₁ | 2 | **2** | `dv₁ = e(µ₁)·v = 2v` row ✓ |
| e(µ₂) = e₁e₂ | 2·2 | **4** | `v(Φ′(ξ)) = u₂/(e₁e₂)` and `= u₂/e(µ₂)` both appear (L264) ⟹ e(µ₂) = e₁e₂; `dv₂ = 4v` row ✓ |
| e(µ₃) = e₃·e(µ₂) | 2·4 | **8** | the (e₃,f₃) row: “denom 8 = e(µ₃) over e(µ₂) = 4 gives e₃ = 2” |
| u₂ = e(µ₂)(w₂+λ₂) | 4·(5/4) | **5** | matches the declared u₂ = 5 ✓ |
| κ₂ = e(µ₁)(w₂+λ₂) | 2·(5/4) | **5/2** | matches ✓ |
| w₂ + λ₂ = 5/4 with λ₂ = 1/4 | ⟹ w₂ = **1** | | the SHEAR check (`.06`) uses λ₂ = 1/4 |
| e₂ = denom(e(µ₁)λ₂) | denom(2·1/4) = denom(1/2) | **2** | matches the declared e₂ = 2 ✓ |
| ν(Φ₂) = w₃ + λ₃ | 21/8 | | the (e₃,f₃) row's re-derivation |
| κ₃ = e(µ₂)·ν(Φ₂) | 4·(21/8) | **21/2** | matches ✓ |
| e₃ = denom(e(µ₂)λ₃) with λ₃ = 21/8 − 5/2 = 1/8 | denom(4·1/8) = denom(1/2) | **2** | matches ✓ (w₃ = µ₂(Φ₂) = 5/2) |
| **u₃ = e₃·κ₃** | 2·(21/2) | **21** | LEMMA GENTOW2-B's own definition (L310–311: “where u₃ = e₃·κ₃”) |
| **dv₂(Φ₂^{e₃}) = e(µ₂)·e₃·ν(Φ₂)** | 4·2·(21/8) | **21 = u₃** | T1 r12's R12-1 terminal-binding identity (XREF R06) |
| cross-check vs GENHN | GENHN L1416: “witness Φ₃ = Φ₂² − 16Φ′ (ψ₃ = T−1, u₃ = 21)” | **21** ✓ | independent occurrence in the supplier note |
| cross-check vs battery | `P-W1` docstring: “u2=5, u3=21”; run artifact `nfeltval(x,Phi',Phi2)=[4, 10, 21]` | **21** ✓ | independent occurrence in the sealed runner |

Four independent occurrences of u₃ = 21 (S2 dictionary, GENHN L1416, the runner docstring, the run artifact) and no disagreement anywhere. Zero arithmetic defects.

**DERIVATION:** `[DEFINITIONAL]` The dictionary is the instantiation map; its FGMN column is read off L785–803 (numerical data), L610–615 (display (4)), Cor 5.6(2) at L1263–1265, Cor 6.4 at L1523–1527 — all four PDF-verified (S6.1 rows 19, 10, 13; §4.2).

**CONDITIONALITY:** the ψ₂ row's identification is TWIST-AWARE — FGMN's ψ₂ = minpoly(z₂) and the repo's ψ₂ = minpoly(η₂) are DISTINCT symbols in general (R3-4, `.82`). The witness column is a single genre; nothing in the table is claimed uniformly.

**RESOLUTION TRACE:** statement lines 62–85 (heading + display + table). Correction sites: the (e₃,f₃) row's `[r1, PE1 F6]` bracket (in place, lines 80); the ψ₂ row's `[r2, PE2 F1]` bracket (in place, line 77); R3-4's standing disambiguation (L1477–1492).

**TEETH:** battery rows P-W1/P-N1/P-N2 (all pin the dictionary's numbers); T1 battery check 10 (XREF R07).

---

### EFF.GENTOW2.06  [lemma — the NORMALIZATION SHEAR]

**CANONICAL STATEMENT:**

**FORM:** bold-headed paragraph closing in an iff

> “NORMALIZATION SHEAR (the repo polygon = FGMN polygon, one affine map).
> The repo's "Φ′-adic development" plots pins (j, dv₁(a_j)) for the
> Φ′-expansion Φ₃ = Σ_j a_j Φ′^j (deg a_j < deg Φ′). FGMN's N₂(Φ₃) :=
> N_{µ₁,φ₂}(Φ₃) (operator definition at L871) plots (j, µ₁(a_j Φ′^j))
> = (j, µ₁(a_j) + j·w₂). Since dv₁ = e(µ₁)·v and µ₁(a_j) = dv₁(a_j)/e(µ₁)
> on coefficients of degree < deg Φ′ (the ladder value = the µ₁ value:
> GENHN-2′'s slot separation, accepted corpus), the invertible affine
> map (j, y) ↦ (j, y/e(µ₁) + j·w₂) carries the repo pin cloud onto the
> FGMN pin cloud, sends lines to lines and preserves on/on-or-above.
> Hence: repo development one-sided of slope κ₂ ⇔ N₂(Φ₃) one-sided of
> slope −λ₂, under κ₂ = e(µ₁)(w₂ + λ₂). (FGMN's own shear-invariance
> statement is Lemma 2.4, L464; witness check: κ₂ = 5/2 ↔ λ₂ = 1/4,
> pins (4,0),(2,7),(0,10) ↦ (4,4),(2,11/2),(0,5).)”

**DERIVATION:** `[DERIVED]` From two inputs: (a) `dv₁ = e(µ₁)·v` and GENHN-2′'s slot separation giving `µ₁(a_j) = dv₁(a_j)/e(µ₁)` on `deg < deg Φ′` coefficients — accepted corpus, NOT proved here (N-3); (b) FGMN's operator definition `N_i := N_{µ_{i−1},φ_i}` at L871, PDF-verified. FGMN's Lemma 2.4 (L464–465: “Let H : R² −→ R² be the affine transformation H(x, y) = (x, y + λx). Then, N_{µ′,φ}(g) = H(N_{µ,φ}(g)).”) is cited as the source's own shear-invariance, not as the proof.

**ARITHMETIC AUDIT (rule 22).** The witness check is exact. With e(µ₁) = 2 and w₂ = 1 the map is `(j,y) ↦ (j, y/2 + j)`:

`[TABLE]`

| repo pin | y/2 | + j·w₂ | FGMN pin | note's value | ✓ |
|---|---:|---:|---|---|---|
| (4, 0) | 0 | +4 | (4, 4) | (4,4) | ✓ |
| (2, 7) | 7/2 | +2 | (2, 11/2) | (2,11/2) | ✓ |
| (0, 10) | 5 | +0 | (0, 5) | (0,5) | ✓ |

Slopes: repo (4,0)→(0,10) has descent 10 over run 4 = **5/2 = κ₂** ✓; FGMN (4,4)→(0,5) has slope (5−4)/(0−4) = **−1/4 = −λ₂** ✓. The iff's two sides agree numerically on the witness.

**CONDITIONALITY:** requires GENHN-2′'s slot separation on `deg < deg Φ′` coefficients (accepted corpus, unproved here); requires the pin cloud to be read on the Φ′-expansion with `deg a_j < deg Φ′`.

**RESOLUTION TRACE:** lines 87–99. Untouched by r1–r3 and by every append.

**TEETH:** battery rows P-W1, P-W2, P-N1, P-N2 (each checks one-sidedness on the repo side against the predicted side and support); TOOTH T1 (a floor-breaching recipe MUST come back not-one-sided).

**XREF:** X-N2 (`N_i := N_{µ_{i−1},φ_i}`, L871, count 1); X-L24 (Lemma 2.4, L464, count 1).

---

### EFF.GENTOW2.07  [fence — the S3 quotation discipline + the r1 provenance correction]

**CANONICAL STATEMENT:**

**FORM:** bold-headed paragraph

> “All quotes from docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt;
> Lxxxx = layout line. [r1] Numbering AND statement content of each
> quote below re-verified directly against the arXiv v3 PDF (visual
> page read, decorrelated from the pdftotext extraction the layout
> pins live in) — per-statement table in S6.1. The pre-repair pointer
> "numbering verified at ledger 63091ce" over-claimed: that ledger
> entry was local-extraction-only and covered GRTJC's cite set (only
> Cor 4.7 + eq (14) overlap this note's) — PE1 finding F1, cured here.”

**DERIVATION:** `[RECORD]` A provenance correction. Its positive content is S6.1.

**SUPERSESSION KIND:** `replacement` — the ledger-63091ce sentence is replaced by the two-leg method statement. `git cat-file -t 63091ce` = commit ✓.

**CONDITIONALITY:** none. This is the corpus's **extraction-corruption discipline** applied (a non-textual leg — visual PDF read — decorrelating the shared pdftotext extraction).

**RESOLUTION TRACE:** lines 103–110. Correction site: S6.1 (L839–893) supplies the leg.

**TEETH:** S6.1's 22 MATCH rows (`.52`), each independently re-verified at compile time against the layout file (§4.1–4.2).

---

### EFF.GENTOW2.08  [cite — [Q1] FGMN Lemma 1.11]

**CANONICAL STATEMENT:**

**FORM:** bracketed cite + inline quotation

> “**[Q1] Lemma 1.11 (L275).** "Every φ ∈ KP(µ) is irreducible in Kv [x]."”

**DERIVATION:** `[IMPORTED]` Verbatim from the pinned print. **Compile-time re-verification:** layout L275 reads `Lemma 1.11. Every φ ∈ KP(µ) is irreducible in Kv [x].` — quote byte-exact modulo the statement-number prefix. ✓

**CONDITIONALITY:** FGMN's standing setting (`.50`/`.55`): K a field with a discrete valuation `v : K* → ℤ`, normalized.

**RESOLUTION TRACE:** line 112. Untouched.

**TEETH:** used at GENTOW2-A(a) (`.18`) to get irreducibility in `K_v[x]`; count of `[Q1]` in the note = 4.

---

### EFF.GENTOW2.09  [cite — [Q2] FGMN Corollary 1.13]

**CANONICAL STATEMENT:**

**FORM:** bracketed cite + inline quotation

> “**[Q2] Corollary 1.13 (L315).** "KP(µ) ⊂ O[x]."”

**DERIVATION:** `[IMPORTED]` **Compile-time re-verification:** layout L315 reads `Corollary 1.13. KP(µ) ⊂ O[x].` ✓

**CONDITIONALITY:** as `.08`.

**RESOLUTION TRACE:** line 114. Untouched.

**TEETH:** GENTOW2-A(a) — O-coefficients, hence `Φ₃ ∈ P`; count = 4.

---

### EFF.GENTOW2.10  [cite — [Q3] FGMN Definition 5.2]

**CANONICAL STATEMENT:**

**FORM:** bracketed cite + inline quotation

> “**[Q3] Definition 5.2 (L1238–1239).** "For a non-zero g ∈ K[x], we say
> that Nµ,φ (g) is one-sided of slope −λ if Nµ,φ (g) = Sλ (g), s(g) = 0
> and s′ (g) > 0."”

**DERIVATION:** `[IMPORTED]` **Compile-time re-verification:** L1238–1239 read `Definition 5.2. For a non-zero g ∈ K[x], we say that Nµ,φ (g) is one-sided of slope −λ if / Nµ,φ (g) = Sλ (g), s(g) = 0 and s′ (g) > 0.` ✓ (reflow across the two layout lines is the only difference).

**CONDITIONALITY:** this is the DEFINITION of “one-sided of slope −λ” that clause (b) of GENTOW2-A asserts; any consumer reading “one-sided” in a different sense reads a different statement.

**RESOLUTION TRACE:** lines 116–118. Untouched.

**TEETH:** clause (b) (`.17`); the S2 shear (`.06`); count = 2.

---

### EFF.GENTOW2.11  [cite — [Q4] FGMN Lemma 5.3]

**CANONICAL STATEMENT:**

**FORM:** bracketed cite + inline quotation

> “**[Q4] Lemma 5.3 (L1240–1244).** "A monic polynomial g ∈ K[x] belongs
> to KP(µ) if and only if either: (1) deg g = mr and g ∼µ φr , or
> (2) s(g) = 0, deg g = s′ (g)mr and Rr (g) is irreducible in Fr [y].
> In the last case, deg g = er (deg Rr (g))mr , Nr (g) is one-sided of
> slope −λr , and Rr (g) ∈ Fr [y] is monic."”

**DERIVATION:** `[IMPORTED]` **Compile-time re-verification:** L1240–1244 verbatim ✓ (five layout lines reflowed).

**CONDITIONALITY:** as `.08`.

**RESOLUTION TRACE:** lines 120–124. Untouched.

**TEETH:** BOTH clauses fire — (2) certifies `Φ₃ ∈ KP(ν)` at `.18`; (1) certifies `Φ₂ = φ₃ ∈ KP(ν)` at `.19` (the r1 F4 repair, without which Prop 5.7 would be applied with an argument not known to be a key polynomial). Count = 5.

**NOTE — foreign-document label defect.** `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` §NS-12 restates this note's inventory as “[Q4] Prop 1.12/Thm 3.11 … [Q6] Lemma 5.3”, which does not match the note. See OPEN-CALL 3.

---

### EFF.GENTOW2.12  [cite — [Q5] FGMN Corollary 4.12 + its proof's construction]

**CANONICAL STATEMENT:**

**FORM:** bracketed cite + two inline quotations joined by an em-dash

> “**[Q5] Corollary 4.12 (L1161–1163).** "Let ψ ∈ Fr [y] be a monic
> polynomial of degre f such that ψ(0) 6= 0. Then, for any α ∈ Γ(µ)
> there exists g ∈ K[x] monic such that deg g = er f mr , µ(g) =
> er f (wr + λr ) and Rr (g) = ψ." — and its proof's construction
> (L1164–1166): "... we may assume that deg g0 < er f mr . Then,
> g = φr^{er f} + g0 satisfies what we want."”

**DERIVATION:** `[IMPORTED]` **Compile-time re-verification:** L1161–1163 verbatim ✓ including the print's `degre` typo (S6.1 row 7 flags it: “MATCH (incl. the print's "degre" typo, visually present in the PDF)”) and the OCR renderings `6=` for `≠`. L1164–1166 verbatim from “we may assume” ✓; the leading ellipsis honestly truncates `Proof. Denote α := er f (wr + λr ). By Corollary 4.11, there exists g0 ∈ K[x] with µ(g0 ) = α / and Rr,α (g0 ) = ψ − y f . By dropping all terms with abscissa s ≥ er f from the φr -expansion / of g0 ,`.

**CONDITIONALITY:** `ψ(0) ≠ 0`, ψ monic of degree f. Both are provisos of GENTOW2-A.

**RESOLUTION TRACE:** lines 126–131. Untouched.

**TEETH:** the construction `g = φ_r^{e_r f} + g₀` is quoted because it **IS the recipe's shape** (`.04`: “whose construction g = φ_r^{e_r f} + g₀ IS the recipe's shape”) — this is what licenses treating the T(b)″ recipe as an instance rather than an ad-hoc object. Count = 2.

---

### EFF.GENTOW2.13  [cite — [Q6] FGMN Theorem 5.8's proof, the degree-forcing display]

**CANONICAL STATEMENT:**

**FORM:** bracketed cite + inline quotation with one internal ellipsis

> “**[Q6] Theorem 5.8, proof, the degree-forcing display (L1296–1302).**
> "If ψ 6= y, then there exists a monic polynomial φ ∈ K[x] of degree
> deg φ = er (deg ψ)mr such that Rr (φ) = ψ ... As a general fact,
> deg φ ≥ s′ (φ)mr . By Corollary 4.4, s′ (φ) − s(φ) = er deg ψ; thus:
> deg φ ≥ s′ (φ)mr ≥ (s′ (φ) − s(φ))mr = er (deg ψ)mr = deg φ.
> Hence, s(φ) = 0 and deg φ = s′ (φ)mr . Therefore, φ satisfies
> condition (2) of Lemma 5.3, and it is a key polynomial for µ."”

**DERIVATION:** `[IMPORTED]` **Compile-time re-verification, with an attribution check the compiler ran because the pin's first line is misleading.** Layout L1296 begins `Theorem 4.8. If ψ = y, then L = R(φr ), by Corollary 5.4. If ψ 6= y, then there exists a` — the token `Theorem 4.8.` there is the TAIL of a cross-reference (`under the isomorphism ∆ ≃ Fr [y] of / Theorem 4.8`) split across L1295–1296, **not** a statement heading. The enclosing statement is `Theorem 5.8` at L1289–1290 (`Theorem 5.8. Let µ be an inductive valuation. The mapping R : KP(µ) → Max(∆) / induces a bijection between KP(µ)/ ∼µ and Max(∆).`) whose proof runs L1291–1302. **The note's attribution “Theorem 5.8, proof” is CORRECT.** The quote's internal ellipsis honestly truncates `, by item 2 of / Corollary 4.12.`; the quote itself is byte-exact over L1296(part)–L1302(part), stopping before `By Corollary 5.4, R(φ) = ψ(yr )∆ = L.` ✓

**CONDITIONALITY:** consumed as an **argument schema**, not as a statement — S6's consumed list is explicit: “Thm 5.8 (proof display only, used as an argument-schema on our concrete Φ₃, not as a statement)”. A consumer that cites “Theorem 5.8” as a proposition is citing something GENTOW2 does not use.

**RESOLUTION TRACE:** lines 133–139. Untouched.

**TEETH:** `.18` applies the display “verbatim to Φ₃ in the role of its φ”. Count = 4.

---

### EFF.GENTOW2.14  [cite — [Q7] FGMN Proposition 5.7 + eq (14)]

**CANONICAL STATEMENT:**

**FORM:** bracketed cite + two inline quotations

> “**[Q7] Proposition 5.7 (L1276–1281).** "Let φ, φ′ ∈ KP(µ). The
> following conditions are equivalent: (1) R(φ) = R(φ′ ). (2) Rr (φ) =
> Rr (φ′ ). (3) φ ∼µ φ′ . (4) Hµ (φ) and Hµ (φ′ ) are associate in
> Gr(µ). (5) φ |µ φ′ ." — with eq (14) (L1004): "Ri,α (φsi ) = y^{⌊s/ei⌋},
> Ri (φsi ) = 1, 1 ≤ i ≤ r."”

**DERIVATION:** `[IMPORTED]` **Compile-time re-verification:** L1276–1281 verbatim ✓. L1004 reads `(14)                  Ri,α (φsi ) = y ⌊s/ei ⌋ ,   Ri (φsi ) = 1,   1 ≤ i ≤ r.` — the note renders the superscript as `y^{⌊s/ei⌋}`, a typographic normalization of the layout's `y ⌊s/ei ⌋`, not a content change ✓

**CONDITIONALITY:** **Prop 5.7 requires BOTH arguments in KP(µ)** — the r1 F4 repair exists precisely to discharge this for `Φ₂` (`.19`). A consumer applying (2)⇔(3) without both memberships is applying a stronger statement than the source has.

**RESOLUTION TRACE:** lines 141–145. Untouched.

**TEETH:** (2)⇔(3) gives `Φ₃ ≁_ν Φ₂` at `.19`, the hypothesis Cor 6.4 needs; eq (14) gives `R_{3,α}(Φ₂^{e₃f₃}) = y^{f₃}` at `.23` and the y-degree bookkeeping at `.39`(h-iii) and `.44`(iii). Count = 9 — the most-used quote in the note.

---

### EFF.GENTOW2.15  [cite — [Q8] FGMN Corollary 4.7]

**CANONICAL STATEMENT:**

**FORM:** bracketed cite + inline quotation

> “**[Q8] Corollary 4.7 (L1121–1126).** "Let 0 ≤ i ≤ r and α ∈ Γi .
> (1) Ri,α (g + h) = Ri,α (g) + Ri,α (h) for all g, h ∈ Pα (µi ).
> (2) If β ∈ Γi−1 , then Ri,α+β (gh) = Ri,α (g)Ri,β (h) for all
> g ∈ Pα (µi ), h ∈ Pβ (µi ). (3) Ri (gh) = Ri (g)Ri (h) for all
> g, h ∈ K[x]."”

**DERIVATION:** `[IMPORTED]` **Compile-time re-verification:** L1121 + L1124–1126 verbatim ✓. The layout interposes a running header at L1122 (`22  FERNÁNDEZ, GUÀRDIA, MONTES, AND NART`) and a blank at L1123; the note's quote correctly omits both without an ellipsis, since a page header is not source text. Flagged as a presentational elision, not a truncation.

**CONDITIONALITY:** **(2) carries NO degree hypothesis.** The note leans on this explicitly and twice — at `.39` (“Cor 4.7 carries no degree hypothesis, so the deg = m₃ product is legitimate HERE, unlike in B-1”) and at `.44`(i) (“no degree hypothesis — the B′ proof's own precedent”). Verified against the source: L1125 hypothesizes only `β ∈ Γi−1`, `g ∈ Pα(µi)`, `h ∈ Pβ(µi)`. ✓ The note's reading is faithful.

**RESOLUTION TRACE:** lines 147–151. Untouched.

**TEETH:** additivity (1) drives the S5 proof sum (`.23`) and the B′ proof (`.39`); multiplicativity (2) drives the grade-0 peel in B′ and the iterated peel in B″ (`.44`). Count = 8.

---

### EFF.GENTOW2.16  [cite — [Q9] FGMN Theorem 6.3 + its proof's opening]

**CANONICAL STATEMENT:**

**FORM:** bracketed cite + two inline quotations

> “**[Q9] Theorem 6.3 (L1458–1464).** "Let F ∈ P be a prime polynomial
> and θ ∈ K̄v a root of F . Let µ be an inductive valuation and φ a key
> polynomial for µ. Then, φ |µ F if and only if v(φ(θ)) > µ(φ).
> Moreover, if this condition holds, then: (1) Either F = φ, or the
> Newton polygon Nµ,φ (F ) is one-sided of slope −λ, where λ =
> v(φ(θ)) − µ(φ) ∈ Q>0 . (2) Let ℓ = ℓ(Nµ,φ (F )). Then, deg F =
> ℓ deg φ and F is µ-minimal. (3) F ∼µ φ^ℓ , so that R(F ) is a power
> of the maximal ideal R(φ)." — its proof opens (L1465): "If F = φ,
> then both conditions φ |µ F and v(φ(θ)) > µ(φ) hold."”

**DERIVATION:** `[IMPORTED]` **Compile-time re-verification:** L1458–1464 verbatim ✓ (the layout writes `K v` for `K̄v` and `φℓ` for `φ^ℓ` — OCR/typography, content identical). L1465 verbatim ✓.

**CONDITIONALITY:** requires `F ∈ P` (prime polynomial in Def 6.1's sense) and `φ ∈ KP(µ)`. Both are discharged at `.18`.

**RESOLUTION TRACE:** lines 153–161. Untouched.

**TEETH:** the proof-opening quote is load-bearing, not decorative: it is what makes the divisibility hypothesis `φ |_ν F` free when `F = φ` (`.20`). Count = 4.

---

### EFF.GENTOW2.17  [cite — [Q10] FGMN Corollary 6.4, THE theorem]

**CANONICAL STATEMENT:**

**FORM:** bracketed cite + inline quotation containing a numbered display

> “**[Q10] Corollary 6.4 (L1523–1527) — THE theorem.** "With the above
> notation, suppose that φ |µ F and µ admits a MacLane chain of length
> r as in (4) such that φ 6∼µ φr . Then, for any 1 ≤ i ≤ r, the Newton
> polygon Ni (F ) is one-sided of slope −λi , we have µ(φi ) = v(φi (θ))
> and
> (23)  F ∼µi−1 φi^{ℓi} ,  deg F = ℓi deg φi ,  Ri−1 (F ) = (ψi−1 )^{ℓi} ,
> where ℓi := ℓ(Ni (F )). In particular, ℓi = ei fi ℓi+1 for all
> 1 ≤ i < r."”

**DERIVATION:** `[IMPORTED]` **Compile-time re-verification:** L1523–1527 verbatim ✓ (layout writes `φℓi i` and `(ψi−1 )ℓi`; the note's superscript braces are typography).

**CONDITIONALITY:** three hypotheses — `φ |µ F`, a MacLane chain of length r **as in (4)**, and `φ ≁µ φr`. All three are discharged in `.20`'s opening. **The “as in (4)” clause is the subject of R3-1 (`.79`) and OPEN-CALL 1.**

**RESOLUTION TRACE:** lines 163–170. Correction site: R3-1, L1438–1449 (strikes the note's own gloss on this hypothesis, not the quote).

**TEETH:** every clause of GENTOW2-A(b)(c)(d) is an instantiation of this one quote (`.20`). Count = 6.

---

### EFF.GENTOW2.18  [cite — supporting notation quotes]

**CANONICAL STATEMENT:**

**FORM:** inline sentence, a compressed list of five pins

> “Supporting notation quotes: N_i := N_{µ_{i−1},φ_i} (L871); ψ_i ∈
> F_i[y] the minimal polynomial of z_i over F_i (L862) with R_i(φ_{i+1})
> = ψ_i (Cor 5.6(2), L1263–1265); the numerical data e_i, f_i, m_i,
> w_i := µ_{i−1}(φ_i), λ_i = h_i/(e₀···e_i) (L785–803); MacLane chain +
> optimality (Def 3.1, L608–615).”

**DERIVATION:** `[IMPORTED]` **All five re-verified at compile time:**

`[TABLE]`

| pin | layout text | ✓ |
|---|---|---|
| L871 | `Ni := Nµi−1 ,φi : K[x] −→ 2R ,   0 ≤ i ≤ r,` | ✓ |
| L862 | `ψi ∈ Fi [y], minimal polynomial of zi over Fi .` | ✓ |
| L1263–1265 | `Corollary 5.6. For all 0 ≤ i < r, / (1) Ni (φi+1 ) is one-sided of slope −λi . / (2) Ri (φi+1 ) = ψi , the minimal polynomial of zi over Fi .` | ✓ |
| L785–803 | the §3.2 numerical-data block: `ei := e(µi )/e(µi−1 ), mi := deg φi , / fi−1 := [Fi : Fi−1 ], wi := µi−1 (φi ), Vi := e(µi−1 )wi , / hi := e(µi )λi , …` and eq (9) at L799–803 incl. `λi = hi /(e0 · · · ei )` and `mi = ei−1 fi−1 mi−1` | ✓ |
| L608–615 | `Definition 3.1. A valuation µ ∈ V is called inductive …` + display (4) at L610–611 + `A chain of augmented valuations as in (4) is called a MacLane chain of length r of µ if / φi+1 6∼µi φi for all 1 ≤ i < r.` + `We say that (4) is an optimal MacLane chain of µ if deg φ1 < · · · < deg φr .` | ✓ |

**CONDITIONALITY:** none beyond FGMN's setting.

**RESOLUTION TRACE:** lines 172–176.

**TEETH:** L608–615's own distinction between “MacLane chain” and “optimal MacLane chain” is the fact OPEN-CALL 1 turns on.

**AUDIT (rule 27, `decorrelated-model audit`):** this unit's L608–615 pin is what allows the compiler to check R3-1 against the source rather than against the note. See OPEN-CALL 1.

---

### EFF.GENTOW2.19  [convention — the S4 setting]

**CANONICAL STATEMENT:**

**FORM:** bold-headed paragraph

> “Setting: a depth-2 tower per T(b)′ (S8 annex, accepted), FGMN chain
> as in S2's dictionary: µ₀ →(x, λ₁) µ₁ →(Φ′, λ₂) µ₂ →(Φ₂, λ₃) µ₃ = ν,
> an optimal MacLane chain (deg x < deg Φ′ < deg Φ₂ — the tower's
> stages are proper, e₂f₂ ≥ 2 in repo names). Base field K = ℚ (or a
> number field), v = the p-adic valuation, K_v complete discrete —
> FGMN's standing setting (their §6 header, L1433, PDF p.27 [r1: pin
> corrected from L1434, PE1 F5]).”

**DERIVATION:** `[IMPORTED + DEFINITIONAL]` The chain is S2's dictionary read as a hypothesis. **Compile-time re-verification of the corrected pin:** L1433 reads `6. MacLane-Okutsu invariants of prime polynomials` ✓ — the r1 F5 correction (L1434 → L1433) is right; L1434 is the section's first prose line, not the header.

**CONDITIONALITY:** **the chain is declared OPTIMAL here.** This is the fact R3-1 uses to strike the (H-b) gloss (`.86`). Properness `e₂f₂ ≥ 2` and `e₃f₃ ≥ 2` are what force strict degree growth. Base field is `ℚ` or a number field — narrower than FGMN's own scope, which is any discretely valued field (§4.2 row FGMN-§1); the narrowing is the note's, not the source's, and `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` §NS-12 resolves the corresponding audit rows to **COVERS-ALL-O** (§4.5, row RX16).

**RESOLUTION TRACE:** lines 179–185. Correction site: the in-place `[r1]` pin repair at line 185; R3-1 at L1438–1449 acts on the (H-b) row, not here.

**TEETH:** hypothesis-audit rows (H-a), (H-b) (`.55`).

---

### EFF.GENTOW2.20  [theorem — THEOREM GENTOW2-A]

**CANONICAL STATEMENT:**

**FORM:** display (bold-headed theorem with lettered clauses)

> “**THEOREM GENTOW2-A.** Let ψ₃ ∈ F₃[y] = K₂[y] be monic irreducible
> of degree f₃ ≥ 1 with ψ₃(0) ≠ 0, and let e₃ ≥ 1 be given with
> e₃f₃ ≥ 2 (proper third stage). Let Φ₃ ∈ K[x] be ANY monic polynomial
> with
>
>   (i) deg Φ₃ = e₃f₃ · deg Φ₂, and
>   (ii) R_ν(Φ₃) = ψ₃  (the level-3 FGMN residual; e_r := e₃ at ν's
>        augmentation data),
>
> — in particular the T(b)″-recipe polynomial Φ₃ = Φ₂^{e₃f₃} −
> Σ_{t<f₃} k̂_t Φ₂^{e₃t}, which satisfies (i) by construction and (ii)
> by LEMMA GENTOW2-B (S5) [r3: as RESTATED — under the multiplicative
> prescription c_t = ϑ(t)^{−1}a_t the realized residual is ψ₃^{(w)} =
> w^{f₃}ψ₃(y/w), admissible, and the theorem is consumed AT ψ₃^{(w)};
> the pre-repair per-height reading realized ψ₃ itself only where
> u(β_t) = 1 at the used slots (letter-dead tested geography), and is
> refuted letter-live — PE4 F1, honesty box]. Then:
>
>   (a) Φ₃ ∈ KP(ν), and Φ₃ is a PRIME POLYNOMIAL: monic, coefficients
>       in O_v, irreducible in K_v[x];
>   (b) [the (α) polygon clause] the Φ′-adic development of Φ₃ is
>       ONE-SIDED of repo-slope κ₂ = e(µ₁)(w₂ + λ₂): FGMN N₂(Φ₃) =
>       N_{µ₁,Φ′}(Φ₃) is one-sided of slope −λ₂, of length ℓ₂ =
>       e₂f₂e₃f₃, and the S2 shear transports one-sidedness to the
>       repo pin plot;
>   (c) [the (α) residual clause] R₂(Φ₃) = ψ₂^{ℓ₃} with ℓ₃ = e₃f₃ —
>       the residual of the Φ′-side is the ψ₂-POWER the r3 box asked
>       for;
>   (d) [the forced intermediate data] for every root ξ of Φ₃ in K̄_v:
>       v(Φ′(ξ)) = ν(Φ′) = w₂ + λ₂ = u₂/(e₁e₂) EXACTLY, and likewise
>       v(x(ξ)) = λ₁ = h/e₁ and v(Φ₂(ξ)) = ν(Φ₂) = w₃ + λ₃ = κ₃/(e₁e₂);
>   (e) [bonus, the recipe's own polygon] N₃(Φ₃) = N_{µ₂,Φ₂}(Φ₃) is
>       one-sided of slope −λ₃, length e₃f₃, residual R₃(Φ₃) = ψ₃.”

**DERIVATION:** proof at `.21`–`.23`. The theorem is stated for **ANY** monic Φ₃ satisfying (i)+(ii) — the recipe is a distinguished instance, not the subject. This quantifier is what makes the theorem survive the B-2 refutation intact (`.24`, `.46`).

**CONDITIONALITY (the full stack — a consumer must carry all of it):**
- ψ₃ monic irreducible over `K₂ = F₃`, `deg ψ₃ = f₃ ≥ 1`, `ψ₃(0) ≠ 0`;
- `e₃ ≥ 1` with `e₃f₃ ≥ 2` (PROPER third stage — an improper stage is a refinement, not a level, per `.55`(H-f));
- the S4 setting: an OPTIMAL length-3 MacLane chain (`.19`);
- hypothesis (ii) is consumed **AT ψ₃^{(w)}**, not at ψ₃, when the supplier is the recipe (the in-place `[r3]` bracket);
- clause (c)'s `ψ₂` is `ψ₂^FGMN`, per R3-4 site 1 (`.89`);
- `ℓ₃ = e₃f₃` and `ℓ₂ = e₂f₂e₃f₃` follow from (23) + the “in particular” of [Q10].

**RESOLUTION TRACE:** statement lines 187–219; proof lines 221–270; correction sites lines 196–203 (the in-place `[r3]` bracket), L1485–1487 (R3-4 fences the clause-(c) `ψ₂`).

**TEETH:** the entire S8 battery (`.60`–`.64`) checks clauses (b)/(c)/(e) at 7 witnesses on two decorrelated oracles; PE4's fresh route ran 27/27 GREEN on the A-route including the clause-(d) value triples (`.24`).

**XREF:** `[Q4]`, `[Q6]`, `[Q9]`, `[Q10]`; STATEMENT_LEDGER row 1 (lines 187–219, md5-8 `5d1ae5f0`) — the ledger's span is byte-identical to this unit's statement span ✓.

---

### EFF.GENTOW2.21  [proof — clause (a), the key certificate]

**CANONICAL STATEMENT:**

**FORM:** italic-headed proof paragraph

> “*(a) Key certificate.* Φ₃ is monic with deg Φ₃ = e₃(deg ψ₃)m₃
> (m₃ := deg Φ₂) and R₃(Φ₃) = ψ₃ irreducible, ψ₃ ≠ y (ψ₃(0) ≠ 0). The
> degree-forcing display quoted at [Q6] applies verbatim to Φ₃ in the
> role of its φ: deg Φ₃ ≥ s′(Φ₃)m₃ ≥ (s′(Φ₃) − s(Φ₃))m₃ =
> e₃(deg ψ₃)m₃ = deg Φ₃ (the middle equality is Cor 4.4(4), L1089),
> forcing s(Φ₃) = 0 and deg Φ₃ = s′(Φ₃)m₃ — condition (2) of Lemma 5.3
> [Q4], so Φ₃ ∈ KP(ν). Then Φ₃ is irreducible in K_v[x] by Lemma 1.11
> [Q1] and has O-coefficients by Cor 1.13 [Q2]; monic by hypothesis;
> hence Φ₃ ∈ P, a prime polynomial in FGMN's Definition 6.1 sense.”

**DERIVATION:** `[DERIVED]` A verbatim re-run of [Q6]'s schema. **Compile-time check of the cited middle equality:** L1089 reads `(4) deg Ri (g) = (s′ (g) − s(g))/ei and Ri (g)(0) 6= 0.` With `R₃(Φ₃) = ψ₃` this gives `deg ψ₃ = (s′ − s)/e₃`, i.e. `s′ − s = e₃ deg ψ₃` — exactly FGMN's own step (`By Corollary 4.4, s′ (φ)−s(φ) = er deg ψ`, L1298). ✓ The attribution to item (4) is correct.

**CONDITIONALITY:** `ψ₃ ≠ y` is derived from `ψ₃(0) ≠ 0`; Def 6.1 at L1439–1440 (`Let P = P(Ov ) ⊂ Ov [x] be the set of all monic irreducible polynomials in Ov [x].`) is the membership target — verified ✓, and it carries **no separability restriction** (§4.5 row RX16 / CITE-SCOPE NS-12).

**RESOLUTION TRACE:** lines 223–231.

**TEETH:** battery B-route PARI signatures at all 7 witnesses confirm irreducibility structure; hypothesis-audit row (H-c) (`.55`).

---

### EFF.GENTOW2.22  [proof — non-equivalence to the top key]

**CANONICAL STATEMENT:**

**FORM:** italic-headed proof paragraph

> “*Non-equivalence to the top key.* R₃(Φ₂) = R₃(φ₃¹) = 1 by eq (14)
> [Q7], while R₃(Φ₃) = ψ₃ with deg ψ₃ = f₃ ≥ 1; if e₃ = 1 and f₃ = 1
> were both allowed the degrees would still differ (ψ₃ ≠ 1), but under
> the properness proviso e₃f₃ ≥ 2 we simply have deg Φ₃ > deg Φ₂, and
> in all cases R₃(Φ₃) ≠ R₃(Φ₂), so Φ₃ ≁_ν Φ₂ by Prop 5.7 (2)⇔(3) [Q7].
> [r1, PE1 F4] Prop 5.7 requires BOTH arguments in KP(ν): Φ₃ ∈ KP(ν)
> by (a) above, and Φ₂ = φ₃ ∈ KP(ν) by Lemma 5.3(1) [Q4] — deg φ₃ =
> m₃ and φ₃ ∼_ν φ₃ (reflexivity of ∼_ν).”

**DERIVATION:** `[DERIVED]` The `[r1, PE1 F4]` clause is an in-place repair supplying the second membership. Verified against the source: Prop 5.7's hypothesis at L1276 is `Let φ, φ′ ∈ KP(µ)` — BOTH ✓; Lemma 5.3(1) at L1241 is `deg g = mr and g ∼µ φr` ✓.

**SUPERSESSION KIND:** `inventory completion` (r1 F4) — nothing is replaced; a missing hypothesis discharge is added.

**CONDITIONALITY:** none beyond the theorem's provisos. The argument is given in two independent forms (degree separation under properness; residual separation in all cases), so it does not depend on `e₃f₃ ≥ 2` alone.

**RESOLUTION TRACE:** statement/proof lines 233–240; correction site lines 238–240 (the in-place r1 F4 insertion). Record at S9 F4 (L1070–1071).

**TEETH:** required by [Q10]'s `φ ≁µ φr` hypothesis; hypothesis-audit row (H-e) (`.55`).

---

### EFF.GENTOW2.23  [proof — clauses (b)+(c)+(d)+(e), the cite fires]

**CANONICAL STATEMENT:**

**FORM:** italic-headed proof paragraph with four bulleted instantiations

> “*(b)+(c)+(d) The cite fires.* Apply Theorem 6.3 [Q9] with F = φ =
> Φ₃, µ = ν: F = φ, so φ |_ν F holds (the proof's opening line, quoted
> at [Q9]). Now Corollary 6.4 [Q10] applies: φ |_ν F, ν has the length-3
> MacLane chain of S2, and φ = Φ₃ ≁_ν φ₃ = Φ₂ (previous paragraph).
> Its conclusions, instantiated:
>
>   • i = 2 clause: N₂(Φ₃) one-sided of slope −λ₂ — clause (b), with
>     the S2 shear giving the repo statement at slope κ₂. Length:
>     ℓ₂ = e₂f₂ℓ₃ (the "in particular" of [Q10]) and ℓ₃ = deg Φ₃/deg Φ₂
>     = e₃f₃ (from (23) at i = 3), so ℓ₂ = e₂f₂e₃f₃.
>   • (23) at i = 3, residual part: R₂(Φ₃) = ψ₂^{ℓ₃} = ψ₂^{e₃f₃},
>     where FGMN's ψ₂ = R₂(φ₃) = minpoly(z₂) (Cor 5.6(2)) is the
>     z₁^{⌊ℓ₁u₂/e₁⌋}-twist of the repo ψ₂ = minpoly(η₂) — S5.1's
>     LETTER FORMULA z₂ = η₂·z₁^{−⌊ℓ₁u₂/e₁⌋} [r2, PE2 F1: the
>     pre-repair "is the repo ψ₂" is on the nose exactly when the
>     twist fixes ψ₂, e.g. z₁ = 1 at f₁ = 1 over q = 2 — true at
>     the S2 witness and at the 13 standing machine witnesses] —
>     clause (c) in the twist-aware form; the consumption note
>     below carries it through T(b)′. (Consistency: FGMN Cor 4.4(4)
>     gives deg R₂(Φ₃) = (s′−s)/e₂ = ℓ₂/e₂ = f₂e₃f₃ =
>     deg(ψ₂^{e₃f₃}) — the twist preserves the degree f₂. ✓)
>   • the middle clause "µ(φᵢ) = v(φᵢ(θ))" at i = 1, 2, 3: v(x(ξ)) =
>     ν(x) = λ₁, v(Φ′(ξ)) = ν(Φ′) = w₂ + λ₂ = u₂/e(µ₂) = u₂/(e₁e₂),
>     v(Φ₂(ξ)) = ν(Φ₂) = w₃ + λ₃ — clause (d). (These hold for each
>     root θ = ξ of F = Φ₃ separately: Theorem 6.3/Cor 6.4 are stated
>     for a fixed root θ, and every root of the irreducible F is such
>     a θ.)
>   • i = 3 clause: N₃(Φ₃) one-sided of slope −λ₃, ℓ₃ = e₃f₃; its
>     residual R₃(Φ₃) = ψ₃ is hypothesis (ii) — clause (e). ∎”

**DERIVATION:** `[DERIVED]` Pure instantiation of [Q9]+[Q10].

**ARITHMETIC AUDIT (rule 22).** The bracketed consistency check is exact: `deg R₂(Φ₃) = (s′−s)/e₂` (Cor 4.4(4)) `= ℓ₂/e₂` (since `ℓ₂ = ℓ(N₂) = (s′−s)` at i=2 by Cor 4.4(3)/(4) bookkeeping) `= e₂f₂e₃f₃/e₂ = f₂e₃f₃`, and `deg(ψ₂^{e₃f₃}) = (deg ψ₂)·e₃f₃ = f₂·e₃f₃`. Equal ✓. The `ℓ₂ = e₂f₂ℓ₃` step is [Q10]'s literal “In particular, ℓi = ei fi ℓi+1” at i = 2 ✓.

**CONDITIONALITY:** **clause (c) is stated in the TWIST-AWARE form only.** `ψ₂` here is `ψ₂^FGMN` (R3-4 site 1, `.89`). A consumer that reads `R₂(Φ₃) = (repo ψ₂)^{e₃f₃}` on the nose is reading the pre-r2 text. Clause (d) is per-root and requires the irreducibility from (a).

**RESOLUTION TRACE:** lines 242–270. Correction sites: the in-place `[r2, PE2 F1]` bracket at lines 255–259; R3-4 at L1485–1487.

**TEETH:** battery on-side residual-support checks at W1/W2/N1/N2 (each verifies the `ψ₂`-power support pattern predicted by clause (c)); TOOTH T2′ (`.61`) shows the polygon side alone certifies nothing without hypothesis (ii)'s irreducibility.

---

### EFF.GENTOW2.24  [instance record — the consumption note, with two robustness brackets]

**CANONICAL STATEMENT:**

**FORM:** italic-headed paragraph carrying two dated bracketed riders

> “*Consumption note.* Clause (d) + (c) are exactly the two inputs the
> r3 T(b)″ ascent needed at a Φ₃-root ξ ("v(Φ′(ξ)) = u₂/(e₁e₂) exact
> with η₂(ξ) a ψ₂-root, the input (ii)'s slot lemma needs at ξ" —
> GENHN_PROOF S9.1 item (6)(α), L1419–1423): the residual power
> ψ₂^{e₃f₃} has no root besides ψ₂'s, so the level-2 residual class
> η₂(ξ) read through T(b)′(ii)'s slot lemma is a ψ₂-root. [r2, PE2
> F1 — letter-twist robustness of this consumption: FGMN's clause is
> in the z₂-letter, the repo consumption in the η₂-letter, and the
> two differ by S5.1's LETTER FORMULA (z₂ = η₂·z₁^{−⌊ℓ₁u₂/e₁⌋}).
> Both ride the ONE field embedding σ: F₃ → k(L₃) that the level-3
> leaf read fixes: η₂ = z₂·z₁^{⌊ℓ₁u₂/e₁⌋} in F₃ is by definition a
> root of the repo ψ₂ = minpoly(η₂), and η₂(ξ) = σ(η₂), so "η₂(ξ)
> is a repo-ψ₂-root" holds with ψ₂'s coefficients read through the
> same σ — no clause of GENTOW2-A consumes an equality of the two
> letters.] [r3 — B-2-flip robustness of this consumption, per the
> PE4 record: THEOREM GENTOW2-A consumes only hypothesis (ii) with
> an admissible residual, never a digit string, so the B-2 flip does
> not touch it; at the same PE4 contact that refuted B-2, every
> GENTOW2-A clause check ran GREEN — 27/27 A-route at LD1/LD2/LD3
> incl. the clause-(c) letter-twist certificates {152,148,144,144,
> 144}, η₂-read = z₁ at 4/4 primes, and the exact value triples
> (clause (d)) — PE4 report §E/[F1], "THEOREM GENTOW2-A UNTOUCHED".]
> The PE3-F1
> correction's mechanism attribution ("the carry terms CLEAR the side")
> is now a THEOREM, not bookkeeping: Cor 6.4 forces every pin strictly
> above the side except the on-side residue pattern of ψ₂^{e₃f₃}.”

**DERIVATION:** `[DERIVED]` The GENHN quote is XREF R01, verified verbatim at `GENHN_PROOF_2026-08-08.md` L1419–1423 (5-line span, exact).

**CONDITIONALITY:** **the consumption is in the REPO letter, not the FGMN letter** — R3-4 site 2 (`.89`) fences it: “the S4 consumption note (body L272–293) consumes the root statement in the REPO letter ("η₂(ξ) is a repo-ψ₂-root"), translated through the single embedding σ per its [r2] bracket.” The single-embedding coherence argument is what carries it; no letter equality is consumed (N-7 adjacent).

**RESOLUTION TRACE:** statement lines 272–297; correction sites lines 277–286 (`[r2]` in place), lines 286–293 (`[r3]` in place), L1487–1492 (R3-4).

**TEETH:** PE4 A-route 27/27 GREEN at LD1/LD2/LD3 (`disclosed non-repair` for the B-2 tooth — it fired on B, not on A).

**AUDIT (rule 27, `decorrelated-model audit` → `hostile-pass certification` by rule 31):** the PE4 pass that refuted B-2 simultaneously **RE-DERIVED GENTOW2-A CLEAN** — “THEOREM GENTOW2-A UNTOUCHED”, 27/27. This is the note's strongest single piece of evidence and it comes from the pass that broke the note's other leg.

---

### EFF.GENTOW2.25  [lemma — LEMMA GENTOW2-B, as RESTATED at r3]

**CANONICAL STATEMENT:**

**FORM:** display (bold-headed lemma with a tagged law and a prescription)

> “**LEMMA GENTOW2-B [r3 RESTATED — PE4 F1: the pre-repair conclusion
> "R_ν(Φ₃) = ψ₃" for the PER-HEIGHT digit string is machine-refuted
> at letter-live frames (LD2, honesty box); the lemma now carries the
> MEASURED transformation law and the prescription that realizes any
> admissible target].** Let the recipe data be as in the r3 box:
> k̂_t ∈ K[x] with deg k̂_t < deg Φ₂, dv₂-height u₃(f₃ − t), and
> K₂-digit residual class c_t ∈ K₂ = F₃ (a GENHN-2′ ladder lift;
> k̂_t = 0 when c_t = 0, c₀ ≠ 0), where u₃ = e₃·κ₃, gcd-normalized so
> the pins (e₃t, u₃(f₃−t)) lie on the line through (e₃f₃, 0) of
> dv₂-slope κ₃, with κ₃ > e₂f₂u₂ (equivalently λ₃ := κ₃/(e₁e₂) −
> ν_{µ₂}(Φ₂)... > 0; the positivity is the [r1]-style node-floor
> arithmetic, here an explicit HYPOTHESIS). Then Φ₃ := Φ₂^{e₃f₃} −
> Σ_{t<f₃} k̂_t Φ₂^{e₃t} satisfies
>
>   (B-law)  R_ν(Φ₃) = y^{f₃} − Σ_{t<f₃} u(β_t)·c_t·y^t,
>            u(β_t) = ϑ(t)·w^{f₃−t},
>
> where u(β_t) := R_{3,β_t}(n̂₂(u₃(f₃−t))) is B′'s per-grade unit
> (S5.1), ϑ(t) := res((n̂₂(u₃(f₃−t))/n̂₂(u₃)^{f₃−t})(x₀)) is the
> repo-derivable n̂₂-cocycle (grade-determined, x₀-free, a z₁^j z₂^k
> letter monomial — LEMMA GENTOW2-B″, S5.2; ϑ(f₃−1) = 1), and
> w := R_{3,κ̄}(n̂₂(u₃)) ∈ K₂^× is a single slot-independent unit
> (κ̄ := u₃/e(µ₂), the top slot's grade). Consequently, given a
> TARGET ψ₃ = y^{f₃} − Σ_{t<f₃} a_t y^t ∈ K₂[y] monic irreducible
> with ψ₃(0) ≠ 0, the MULTIPLICATIVE-CONVENTION prescription
> c_t := ϑ(t)^{−1}·a_t realizes
>
>   R_ν(Φ₃) = w^{f₃}·ψ₃(y/w) =: ψ₃^{(w)},
>
> monic irreducible of degree f₃ with ψ₃^{(w)}(0) = w^{f₃}ψ₃(0) ≠ 0
> (the substitution y ↦ wy preserves monicity after the
> renormalization displayed, irreducibility, degree, and the nonzero
> constant) — an ADMISSIBLE residual, so the recipe realizes
> THEOREM GENTOW2-A's hypothesis (ii) with residual ψ₃^{(w)} for any
> admissible target ψ₃. The unadjusted PER-HEIGHT prescription
> (c_t = a_t) realizes ψ₃ itself iff u(β_t) = 1 at each used slot —
> holding at each letter-dead slot the standing record tested, and
> failing at PE4's letter-live LD2 (honesty box below).”

**DERIVATION:** proof at `.26`. **ϑ ORIENTATION RECORD (mandatory for consumers — the parent charge's item (b)):** GENTOW2's `ϑ` is a **single-argument, slot-indexed** unit defined by

>   ϑ(t) := res((n̂₂(u₃(f₃−t)) / n̂₂(u₃)^{f₃−t})(x₀))

— numerator at the SLOT height `u₃(f₃−t)`, denominator the `(f₃−t)`-th power of the TOP-SLOT normalizer. Under the substitution `s := f₃ − t` this is `res(n̂₂(su₃)/n̂₂(u₃)^s)`. The corpus's downstream notes carry the SAME object under three other names and one of them is the **inverse** of a fourth:

`[TABLE]`

| Note | Symbol | Definition | Relation to GENTOW2's ϑ(t) |
|---|---|---|---|
| GENTOW2 (this note) | `ϑ(t)` | `res((n̂₂(u₃(f₃−t))/n̂₂(u₃)^{f₃−t})(x₀))` | — (the reference) |
| T1 `T1_GAUGE_COCYCLE_2026-08-12.md`, box `(C3-Theta)` | `Θ_i(t)` | `ϑ_{i,f_{i+1}−t}^{−1} = res(n̂_i((f_{i+1}−t)u_{i+1})/n̂_i(u_{i+1})^{f_{i+1}−t})` | **`ϑ(t) = Θ₂(t)`** — same object; and `Θ_i(t) = ϑ_{i,f_{i+1}−t}^{−1}`, so GENTOW2's ϑ is the **INVERSE** of T1's two-index `ϑ_{i,s}` |
| T3 `T3_COCYCLE_TELESCOPE_2026-08-12.md`, box `(T1-THETA)` + the (ABS-G2) block | `Θ_N(s;q)` = `ϑ_{G2}(t)` | `ϑ_N(s;q)^{−1} = res(N(sq)/N(q)^s)`; and `ϑ_{G2}(t) := res(n̂₂(su₃)/n̂₂(u₃)^s) = Θ_N(s;u₃)` | **`ϑ(t) = ϑ_{G2}(t) = Θ_N(f₃−t; u₃)`**; T3 records the inverse orientation explicitly at its §8.1 check 2 |
| GENTOW5 `GENTOW5_PROOF_2026-08-09.md` L214–215, LEMMA GENTOW5-A1 | `vartheta_t` | `theta_t := [n2hat(lam)(x0)]^t * [n2hat(t*lam)(x0)]^{-1} = iota(vartheta_t)` | **RECIPROCAL**: A1's `theta_t = res(n̂₂(λ)^t/n̂₂(tλ))`, so `ϑ(t) = vartheta_{f₃−t}^{−1}` at `λ = u₃`. GENTOW2 itself **declines to adjudicate** this (N-7) |
| T5 `T5_WFRAME_2026-08-12.md` L991–993 | (the reconciliation sentence) | “B″'s single-argument `ϑ(t)` is this note's `Θ₂(t)`, the inverse-telescope orientation” | the acceptance-pass verdict that closes the loop |

**T5's acceptance pass hinged on this reconciliation** and returned **VERIFIED** on it (T5 §ledger item 2), against the byte span `L729–738 @ 33f86204` with the ledger md5-8 `d4c8b885`. Both legs re-checked at compile time: `git show 33f86204:…GENTOW2_PROOF_2026-08-09.md | sed -n '729,738p'` is byte-identical to HEAD's L729–738 ✓, and the raw-span md5 is `8978f8ba637beb26272fcbd362e277a3` — matching T5's own disclosed mechanism note (“a raw `sed -n '729,738p' | md5sum` of the byte span gives `8978f8ba…` — not a mismatch”) ✓.

**CONDITIONALITY (the full stack):**
- `deg k̂_t < deg Φ₂`; dv₂-height exactly `u₃(f₃−t)`; digit `c_t ∈ K₂`; `k̂_t = 0` when `c_t = 0`; `c₀ ≠ 0`;
- `u₃ = e₃κ₃`, gcd-normalized, pins on the line through `(e₃f₃, 0)` of dv₂-slope κ₃;
- **`κ₃ > e₂f₂u₂` is an EXPLICIT HYPOTHESIS** (N-2), NOT derived — it rides COR GENTOW-1.1 in GENTOW-1 (`.57`);
- `w` is not computed (N-6) but is consumer-invisible; the realized residual is `ψ₃^{(w)}`, not `ψ₃`;
- the per-height reading survives **iff** `u(β_t) = 1` at each used slot — this final sentence is **B′(4)'s sole surviving consumer** per the PE6 FOLD (`.81`).

**RESOLUTION TRACE:** statement lines 303–340; proof lines 342–373; correction sites — the whole statement IS r3's replacement (S11 F1(ii), L1244–1248); R3-3 completes the proof's α display (L1465–1475).

**SUPERSESSION KIND:** `replacement` — the pre-r3 conclusion `R_ν(Φ₃) = ψ₃` for the per-height digit string is replaced by (B-law) + the multiplicative prescription. Replacement display carried above in full.

**TEETH:** PE4's LD2 refutation (the tooth that bit); PE5's γ₂-live fresh route GREEN 91/0 (`.75`); the decode MULT/COC/MP pins (`.45`).

**XREF:** STATEMENT_LEDGER row 2 (lines 303–340, md5-8 `8a00bf44`) — span byte-verified ✓; T1 `SPAN PIN 2` cites `LEMMA GENTOW2-B, md5=8a00bf44d21f87e878c0be6226b13b61` ✓ same hash.

---

### EFF.GENTOW2.26  [proof — LEMMA GENTOW2-B]

**CANONICAL STATEMENT:**

**FORM:** bold-headed proof paragraph

> “**Proof.** Write α := e₃f₃(w₃... (FGMN: α = e_r f(w_r + λ_r) with
> e_r = e₃, f = f₃, w_r = w₃ = µ₂(Φ₂), λ_r = λ₃). Each term lies in
> P_α(ν): ν(Φ₂^{e₃f₃}) = e₃f₃(w₃ + λ₃) = α, and ν(k̂_t Φ₂^{e₃t}) =
> ν(k̂_t) + e₃t(w₃ + λ₃) = α exactly because dv₂(k̂_t) = u₃(f₃ − t) is
> the on-line height (dv₂ = e(µ₂)v and ν(k̂_t) = µ₂(k̂_t) =
> dv₂(k̂_t)/e(µ₂) for deg k̂_t < deg Φ₂ — GENHN-2′'s ladder = the
> µ₂-value, accepted corpus; the k̂_t are Φ₂-free so their ν- and
> µ₂-values agree, FGMN Prop 1.9/L258). By Cor 4.7(1) [Q8] (additivity
> on P_α(µ₃)):
>
>   R_{3,α}(Φ₃) = R_{3,α}(Φ₂^{e₃f₃}) − Σ_{t<f₃} R_{3,α}(k̂_t Φ₂^{e₃t}).
>
> Eq (14) [Q7] gives R_{3,α}(Φ₂^{e₃f₃}) = y^{f₃}. For the correction
> terms, Cor 4.7(2) [Q8] (multiplicativity) with g = k̂_t ∈ P_β(µ₃)
> (β = ν(k̂_t) ∈ Γ₂) and h = Φ₂^{e₃t}: R_{3,α}(k̂_t Φ₂^{e₃t}) =
> R_{3,β}(k̂_t) · y^t (eq (14) again for the power; the abscissa
> bookkeeping s_j = s(α) + je₃ with s(α) = 0 places the t-th
> contribution at y^t). Here R_{3,β}(k̂_t) ∈ F₃ is the degree-0
> residual of a polynomial of degree < deg Φ₂ = m₃ whose N₃-polygon is
> the single point (0, β): by Definition 3.16 (L916–923) its value is
> the K₂-digit class of k̂_t up to the unit constant ε₂(β) ∈ F₃*.
> [r3 — the pre-repair step identified that value with c_t ON THE
> NOSE (= B-2), machine-refuted at LD2; corrected step:] By LEMMA
> GENTOW2-B′(3)+(4) (S5.1, derived from the accepted corpus), with
> β = β_t the slot's grade: R_{3,β_t}(k̂_t) = u(β_t)·digit(k̂_t) =
> u(β_t)·c_t, the recipe's k̂_t having repo digit c_t by construction.
> Summing: R_{3,α}(Φ₃) = y^{f₃} − Σ u(β_t)c_t y^t — the (B-law) —
> and LEMMA GENTOW2-B″ (S5.2) factors u(β_t) = ϑ(t)·w^{f₃−t}. With
> the multiplicative prescription c_t = ϑ(t)^{−1}a_t the sum is
> y^{f₃} − Σ a_t w^{f₃−t} y^t = w^{f₃}ψ₃(y/w) = ψ₃^{(w)}. Since the
> constant term u(β₀)c₀ ≠ 0 (u a unit, c₀ ≠ 0) we get R₃(Φ₃) =
> R_{3,α}(Φ₃) (Def 3.18, L994–1000, j₀ = 0). ∎”

**DERIVATION:** `[DERIVED]` **Compile-time verification of the four FGMN pins used here:** Def 3.16 at L916–923 ✓ (`Ri,α (g) = … 0≤j ǫi−1 (αj ) Ri−1,αj (asj )(zi−1 ) y^j …, where sj := s(α) + jei and αj := α − sj (wi + λi )` — the note's `s_j = s(α) + je₃` bookkeeping is FGMN's own, exactly); Def 3.18 at L994–1000 ✓ (`Ri (g) := Ri,α (g)/y^{j0} …, where j0 = ⌊s(g)/ei⌋`); Prop 1.9 at L258–261 ✓ (item (2): `µ(g) = µ′ (g) if and only if φ ∤µ g`); Cor 4.7(1)/(2) at L1121–1126 ✓.

**GOVERNING CONSUMPTION READING (rule 3, TERMINAL):** this proof's corrected step **quotes** `B′(3)+(4)`, but the PE6 FOLD's governing reading (`.81`) is that the true consumption is **`B′(3) + B″`** — clause (4) is not used here. The quoted text is byte-frozen; the reading governs.

**ARITHMETIC AUDIT (rule 22).** The α display was truncated in the source and is completed by R3-3 (`.88`) to `α := e₃f₃(w₃ + λ₃)`. Self-consistency check: the proof's own next clause reads `ν(Φ₂^{e₃f₃}) = e₃f₃(w₃ + λ₃) = α` ✓, and the adjacent parenthetical `α = e_r f(w_r + λ_r)` with `e_r = e₃, f = f₃, w_r = w₃, λ_r = λ₃` instantiates to the same expression ✓ — two independent recoveries of the same completion. The prescription arithmetic: `Σ_t ϑ(t)w^{f₃−t}·(ϑ(t)^{−1}a_t) y^t = Σ_t a_t w^{f₃−t} y^t`, and `w^{f₃}ψ₃(y/w) = w^{f₃}[(y/w)^{f₃} − Σ a_t (y/w)^t] = y^{f₃} − Σ a_t w^{f₃−t} y^t` ✓ EXACT.

**CONDITIONALITY:** requires GENHN-2′'s ladder-value identity (accepted corpus, N-3); requires the `k̂_t` to be Φ₂-free with `deg < m₃`; `j₀ = 0` requires `u(β₀)c₀ ≠ 0`.

**RESOLUTION TRACE:** statement lines 342–373; correction sites lines 363–367 (the in-place `[r3]` corrected step), L1465–1475 (R3-3 completes α), L1303–1331 + L1369–1383 (the consumption-list unification and its FOLD).

**TEETH:** the decode probe's MULT checks at LD1/LD2 are “the statement 'realized = P' verbatim” (`.45`).

---

### EFF.GENTOW2.27  [instance record — honesty box leg (B-1)]

**CANONICAL STATEMENT:**

**FORM:** bold-headed italic box opener + labelled leg

> “*Honesty box for GENTOW2-B [r1 REWRITTEN — PE1 F2 (provenance) +
> F3 (false fallback clause) cured].* Two repo-side identifications
> carry this proof:
>
> (B-1) the dv₂ ladder value of a deg < D₂ ladder element equals its
> µ₂-value, exactly, with digit-0 meaning strictly-above (GENHN-2′'s
> two-step class separation + no-cancellation — LEMMA GENHN-T(b)′
> (ii), S8 annex, accepted corpus).”

**DERIVATION:** `[IMPORTED]` Accepted corpus. XREF R02: `grep -cF 'GENHN-T(b)′' GENHN_PROOF_2026-08-08.md` = **12**; `grep -cF 'GENHN-2′'` = **3**.

**CONDITIONALITY:** **`deg < D₂` is a HARD scope fence on (B-1)** — the r2 F2 finding was exactly that B′'s h-step applied it outside this scope (`.39`), and R3-2 (`.87`) re-fences it again at B″ step (iv). Any consumer applying (B-1) to a `deg ≥ D₂` object is applying something the note does not have.

**RESOLUTION TRACE:** lines 375–382. Correction sites: `.39` (the r2 h-step repair), L1451–1463 (R3-2).

**TEETH:** the worked N1 trace at `.36` exhibits the exact frame where the scope fence bites (`product = 2x²Φ′ of deg 4 = m₃ — B-1 inapplicable as written`).

---

### EFF.GENTOW2.28  [instrument-audit — honesty box leg (B-2), REFUTED]

**CANONICAL STATEMENT:**

**FORM:** bold-headed labelled leg carrying a refutation record

> “(B-2) [r3 REFUTED AT LETTER-LIVE GRADES, REPLACED BY THE MEASURED
> COCYCLE FORM — PE4 F1, machine]. The identification this box
> asserted through PE3 — "the repo K₂-digit of a Φ₂-free ladder
> element equals the ε₂-normalized F₃-coordinate of FGMN's Def 3.16
> at its grade, ON THE NOSE" — is FALSE at letter-live grades: at the
> first letters × depth contact (LP1 tower, stage-3 recipe e₃ = 1,
> f₃ = 2, κ₃ = 19; z₁ ∈ F₄∖F₂), frame LD2's per-height digit string
> (z₁, z₁²), prescribing the SPLIT ψ₃ = y²+z₁y+z₁² = (y+1)(y+z₁²),
> realized a SINGLE (4,4) prime with realized residual y²+z₁y+1
> (sealed fresh route RED 62/9, each of the 9 misses a
> B-2-on-the-nose prediction — runner gentow2_pe4_fresh.py, seal
> 23def87, output kept as-is; decode probe gentow2_pe4_decode.py
> GREEN 14/0 first-run-under-its-seal; PE4 report §E/[F1]). What
> replaces the assertion — DERIVED in S5.1 + S5.2 from the accepted
> corpus, not asserted: B′(3)'s per-grade unit at the recipe's used
> slots factors as
>
>     u(β_t) = ϑ(t) · w^{f₃−t}          (LEMMA GENTOW2-B″, S5.2)
>
> where ϑ(t) := res((n̂₂(u₃(f₃−t))/n̂₂(u₃)^{f₃−t})(x₀)) is the
> repo-internal n̂₂-COCYCLE — grade-determined, x₀-free, and
> LETTER-VALUED: a z₁^j z₂^k monomial by S5.2's γ-calculus; at the
> PE4 frames ϑ(0) = z₂^{−1}z₁^{−5} = z₁ (LP1 has z₂ = 1), matching
> the machine pin res(n̂₂(19)²/n̂₂(38)) = z₁² = ϑ(0)^{−1} (decode COC
> checks, both frames) — and w := R_{3,κ̄}(n̂₂(u₃)) ∈ K₂^× is a
> SINGLE slot-independent unit, the honest cross-frame residue
> (consumer-invisible: it acts by the grade-covariant substitution
> y ↦ wy, which preserves irreducibility and factor degrees; not
> computed anywhere in the corpus — see S5.1's re-scoped residue
> paragraph). Verdict-level machine data (prime-split patterns) is
> w-blind and constrains ϑ only: the standing 13-witness record's
> green B-routes support ϑ = 1 at each of its own tested slots, and
> LD1/LD2 measure ϑ(0) = z₁ ≠ 1 letter-live. The recipe-grammar
> consequence is LEMMA GENTOW2-B as RESTATED above (the
> multiplicative-convention prescription); the per-height on-the-nose
> reading survives only where the slot's letter monomial is trivial.”

**DERIVATION:** `[REFUTED — machine]` The refutation is a run, not an argument: `gentow2_pe4_fresh.py` (exists, 16,335 bytes) at seal `23def87` (`git cat-file -t` = commit ✓), RED 62/9; `gentow2_pe4_decode.py` (exists, 4,853 bytes) + `gentow2_pe4_decode_output.txt` (exists, 348 bytes), GREEN 14/0.

**SUPERSESSION KIND:** **`withdrawal`** (rule 29, ninth kind). (B-2) becomes UNAVAILABLE — the note says so in terms: “is CONSUMED NOWHERE” (L430), “consumed NOWHERE in the repaired note” (L703). The measured cocycle form is not a substitute *for the same site* — it is a different, derived law. A merge that reads this as an ordinary `replacement` will keep consuming a withdrawn input.

**CONDITIONALITY:** the refutation is at LETTER-LIVE grades. The on-the-nose reading “survives only where the slot's letter monomial is trivial”, i.e. it is not universally false, it is not universally true, and the note consumes it in neither direction.

**RESOLUTION TRACE:** lines 384–419. Correction sites: `.25` (the restated lemma), `.43`/`.44` (B″ replacing it), `.40` (the re-scoped residue paragraph).

**TEETH — disposition `signed vacuity disclosure` inverted:** this is the corpus's cleanest example of a tooth firing exactly where the note's own earlier scope disclosure said the record was blind. The `[r2]` disclosure (`.30`) is quoted by the note as “PROVED PRESCIENT by PE4 [F1], which found the box's scope warning load-bearing, not boilerplate.”

**AUDIT (rule 27, `in-house hostile pass` / `decorrelated-model audit`):** PE4's fresh route is the finding; no battery of the sealed 41-check suite could have produced it, because every sealed witness sits at `f₁ = 1 over q = 2` where `z₁ = 1` (`.30`).

---

### EFF.GENTOW2.29  [supplier-finding — the (B-2) provenance history]

**CANONICAL STATEMENT:**

**FORM:** bracketed rider inside the honesty box

> “[r1] Provenance history (stands as dated): the on-the-nose
> identification was FIRST MADE IN THIS NOTE. The pre-repair pointer ("the [W-2] graded-dictionary
> identification at level 2, the same one T(b)′'s proof already
> uses") was wrong on both legs — GRTW2's dictionary targets a
> different source text and GENHN/T(b)′ has no Def-3.16 contact (PE1
> F2). What the accepted corpus DOES derive is now separated out as
> LEMMA GENTOW2-B′ (S5.1): B-2 holds UP TO an x₀-free, g-free unit
> family u(β) ∈ K₂^× (u(β) = the FGMN coordinate of the repo ladder
> normalizer at grade β). [r3] The residue "u(β) = 1 at each grade
> the recipe uses", consumed DISCLOSED-NOT-DERIVED through PE3, is
> now REFUTED (LD2, above) and is CONSUMED NOWHERE: the restated
> lemma consumes only B′(3)–(5) + B″, all derived.”

**DERIVATION:** `[RECORD]` A defect report against the note's own earlier attribution and against two other notes' supposed supply (GRTW2's dictionary; GENHN/T(b)′). Type `supplier-finding` per rule 13 — the content is a negative finding about what other notes do NOT supply.

**SUPERSESSION KIND:** `provenance-rider` — the *claim* is unchanged in content; its *attribution* moves from “the [W-2] graded-dictionary identification” to “FIRST MADE IN THIS NOTE”.

**CONDITIONALITY:** the final sentence's inventory “B′(3)–(5) + B″” is **consumption-list site 1 of 5**; read under the PE6 FOLD (`.81`), the true consumption is `B′(3) + B″`.

**RESOLUTION TRACE:** lines 420–431. Correction sites: L1303–1331 (m1 CURE), L1369–1383 (PE6 FOLD).

**TEETH:** none of its own; guarded by the S9 F2 record (`.65`).

---

### EFF.GENTOW2.30  [run-record + preregistration — the machine-support history and the [r2] scope disclosure]

**CANONICAL STATEMENT:**

**FORM:** two bracketed riders, emitted together because the second is the falsifier the first's scope invited

> “Machine-support history (accurate as dated, per PE4 §S): the sealed battery (41/0)
> + the PE1 fresh route (20/0) sit at 10 witnesses whose B-route
> factorizations were predicted with u ≡ 1, including the
> F₄ × f₃ = 2 corner pair F2/F3 where flipping one digit flips
> irreducible ↔ split — twist families u that would alter those
> verdicts at the tested grades are excluded by that record; [r3]
> read via B″, that record supports ϑ = 1 at those tested slots and
> was structurally w-blind and z₁-blind (letter-dead).
> [r2] Scope disclosure (PE2 F1's letter-blindness point — PROVED
> PRESCIENT by PE4 [F1], which found the box's scope warning
> load-bearing, not boilerplate): the 13 witnesses standing at PE2
> (those 10 + the 3 PE2-fresh f₃ = 3 ones) each sit at f₁ = 1 over
> q = 2, where z₁ = 1 — the record supports u ≡ 1 on letter-dead
> geography only. The first letter-live machine contact is the r2
> probe (gentow2_r2_letter_probe.py, S10), which tests S5.1's LETTER
> FORMULA itself at f₁ = 2 (z₁ ∈ F₄∖F₂), not B-2; the first
> letter-live B-2 contact is PE4's LD1/LD2 — the tooth that bit.”

**DERIVATION:** `[RECORD]` Artifacts verified: `gentow2_pe1_fresh.py` + `gentow2_pe1_fresh_output.txt` exist; `gentow2_r2_letter_probe.py` + output exist.

**ARITHMETIC AUDIT (rule 22) — the witness census, recounted:**

`[TABLE]`

| Cohort | Count | Source sentence |
|---|---:|---|
| committed | 5 | S8: “the 5 committed ones (W1 … W5)” |
| battery-new | 2 | S8: “+ 2 NEW depth-3 witnesses” |
| PE1-fresh | 3 | S5.1(ii) enumeration |
| **subtotal (“10 witnesses”)** | **10** | this unit's first rider ✓ |
| PE2-fresh (f₃ = 3) | 3 | this unit's second rider |
| **total (“13 witnesses”)** | **13** | S5.1(ii): “5 committed + 2 battery-new + 3 PE1-fresh + 3 PE2-fresh” ✓ |

5+2+3 = 10 ✓ and 10+3 = 13 ✓ and 5+2+3+3 = 13 ✓. **No source-self-count error** (rule 39 clean here).

**CONDITIONALITY:** the support is for `ϑ = 1` **at the tested slots only**, and the record is structurally `w`-blind and `z₁`-blind. Any consumer citing the 13-witness record as evidence for `u ≡ 1` in general is citing a record the note has explicitly scoped away.

**RESOLUTION TRACE:** lines 431–448.

**TEETH — disposition `stale self-description` averted:** the `[r2]` disclosure is the note's own preregistration of its blindness, and PE4 is the run that filled it in. Emitted as ONE unit rather than two because the source writes the prediction and its later confirmation in one continuous passage; the `preregistration` half is the `[r2]` sentence, the `run-record` half is the parenthetical “PROVED PRESCIENT by PE4 [F1]”.

---

### EFF.GENTOW2.31  [lemma — (B-2-fallback), the TRUE transformation law, FIRED]

**CANONICAL STATEMENT:**

**FORM:** parenthetical-headed paragraph carrying two dated brackets and a corrected clause

> “(B-2-fallback, the TRUE transformation law) [r3: THE FALLBACK
> FIRED — PE4's LD2 realized exactly this clause's u ≢ 1
> grade-varying (ϑ-cocycle) mode, and the clause's survival analysis
> (re-parameterization c_t ↦ u(β_t)^{−1}c_t; GENTOW2-A untouched) is
> now PROMOTED into the restated LEMMA GENTOW2-B above and made
> effective by B″ (S5.2), which computes the needed u(β_t) up to the
> consumer-invisible w. Kept below as composed, the record of the r1
> correction.] [r1: the pre-repair
> clause — a fixed-unit discrepancy acts by "ψ₃ ↦ y ↦ εy
> substitution" and "every clause of GENTOW2-A survives verbatim" —
> was FALSE at f₃ ≥ 2: a fixed δ multiplies every non-leading digit,
> giving R = y^{f₃} − δ·Σ c_t y^t, which is not a y ↦ εy
> substitution (that one scales coefficient t by ε^{t−f₃}, the
> grade-covariant pattern; the two agree only at f₃ ≤ 1), and
> irreducibility can die: over K₂ = F₄, ψ₃ = y² + ωy + 1 is
> irreducible while the δ = ω twist y² + ω²y + ω has the root y = 1
> (PE1 F3's counter-instance).] Corrected clause: if a future audit
> finds ε-normalized digit = u(β)·(repo digit) — B′(3)'s own
> direction, R_{3,β}(g) = u(β)·digit(g) [r2, PE2 F3: the pre-repair
> hypothesis wrote the INVERSE convention (repo = u·ε-normalized);
> harmless in substance since u ranges over arbitrary unit families
> and c_t ↦ u^{−1}c_t absorbs either reading, but the box now
> matches the lemma it cites] — with u ≢ 1 — fixed OR
> grade-varying (the latter is the ϑ-cocycle mode of GENTOW5-A1's
> repo-internal dictionary, GENTOW-4's η₂-cocycle finding) — then by
> LEMMA GENTOW2-B′(5) the recipe at digit string (c_t) realizes
> R_ν(Φ₃) = y^{f₃} − Σ u(β_t)c_t y^t. Since u is x₀-free and the
> digit string is freely prescribable, re-parameterizing c_t ↦
> u(β_t)^{−1}c_t realizes any admissible target ψ₃ (monic
> irreducible, ψ₃(0) ≠ 0, degree f₃): THEOREM GENTOW2-A is untouched
> (it consumes only hypothesis (ii), never a digit string), LEMMA
> GENTOW2-B survives with the re-parameterized prescription, and the
> only casualty of u ≢ 1 would be the cosmetic claim that the repo
> digit string spells ψ₃'s coefficients. At f₃ ≤ 1 no
> re-parameterization is even needed for clause survival: y − δc₀
> stays monic irreducible with nonzero constant.”

**DERIVATION:** `[DERIVED]` A conditional-survival lemma, written before its antecedent was known to hold, then fired.

**ARITHMETIC AUDIT (rule 22) — the F₄ counter-instance, recomputed.** In `F₄ = {0,1,ω,ω²}` with `ω² = ω+1`, `ω³ = 1`: `ψ₃ = y² + ωy + 1` has `ψ₃(0) = 1 ≠ 0`, `ψ₃(1) = 1+ω+1 = ω ≠ 0`, `ψ₃(ω) = ω²+ω²+1 = 1 ≠ 0`, `ψ₃(ω²) = ω⁴+ω³+1 = ω+1+1 = ω ≠ 0` — **irreducible** ✓. The `δ = ω` twist `R = y² − δ(−ωy − 1)`… taking the note's stated form `y² + ω²y + ω`: at `y = 1`, `1 + ω² + ω = 1 + (ω+1) + ω = 0` — **root at y = 1** ✓. The claim “irreducibility can die” is verified. The two scaling patterns: a fixed `δ` on non-leading digits gives coefficient `t ↦ δ·c_t`; the `y ↦ εy` renormalized substitution gives `c_t ↦ ε^{t−f₃}c_t`. These agree for all `t < f₃` iff `ε^{t−f₃} = δ` for all such `t`, which at `f₃ ≥ 2` requires `ε^{−1} = ε^{−2}`, i.e. `ε = 1`, hence `δ = 1` — so they agree only at `f₃ ≤ 1` ✓ EXACT.

**SUPERSESSION KIND (two, chained — rule 25 `CHAIN`):**
`CHAIN:` frozen pre-repair `y ↦ εy` clause → **r1 F3 `replacement`** (the false clause DELETED; the true law displayed) → **r2 F3 `wording-rider`** (the hypothesis's direction flipped to match B′(3)) → **r3 `partial-withdrawal`** (rule 36): the survival analysis is PROMOTED into `.25`, and the clause is “Kept below as composed, the record of the r1 correction.” **TERMINAL: `.25`** for prescription consumers; **TERMINAL: this unit** for anyone reading the r1 correction's history. Two TERMINALs by consumer class (rule 30).

**CONDITIONALITY:** the corrected clause is stated in B′(3)'s direction (`ε-normalized = u·repo`). The r2 F3 note that the inverse reading is “harmless in substance” is a *substance* claim, not a licence to swap conventions in a formalization.

**RESOLUTION TRACE:** lines 450–485. Correction sites: lines 450–457 (`[r3]` in place), lines 466–472 (`[r2, PE2 F3]` in place); promotion target `.25` at lines 303–340.

**TEETH:** PE1 F3's counter-instance (a constructed counterexample, `Lean theorem` class); PE4's LD2 (the mode firing).

---

### EFF.GENTOW2.32  [fence — the citation is untouched by both identifications]

**CANONICAL STATEMENT:**

**FORM:** inline sentence

> “Neither identification touches the FGMN citation itself.”

**DERIVATION:** `[RECORD]` The honesty box's closing fence, and the reason the B-2 refutation did not revoke the cite.

**CONDITIONALITY:** none. It is a scope statement, elaborated at `.54` (direction of fit).

**RESOLUTION TRACE:** line 487.

**TEETH:** PE4's simultaneous A-route 27/27 GREEN (`.24`) is the empirical form of this sentence.

---

### EFF.GENTOW2.33  [definition — the two reads, (R-FGMN) and (R-repo)]

**CANONICAL STATEMENT:**

**FORM:** bold-headed paragraph + a two-item tagged display

> “Fix a grade β ∈ Γ₂ (so s₃(β) = 0: eq (12) at i = 3 with
> gcd(h₃, e₃) = 1 forces s ≡ 0, the S5 abscissa bookkeeping). Two
> reads are in play on Φ₂-free elements g (deg g < m₃ = deg Φ₂) of
> exact grade ν(g) = β:
>
>   (R-FGMN)  R_{3,β}(g) ∈ F₃ = K₂ — Def 3.16 at i = 3, single
>             j = 0 term: R_{3,β}(g) = ε₂(β)·R_{2,β}(g)(z₂), the
>             ε₂-normalized coordinate;
>   (R-repo)  digit(g) := res(g(x₀)/n̂₂(β̂)(x₀)) ∈ k(L2) ≅ K₂ — the
>             GENHN-2′ coherent read against the ladder normalizer
>             n̂₂(β̂) = π^a x^i Φ′^b at dv₂-height β̂ = e(µ₂)β,
>             through the CANONICAL EVALUATION identification
>             k(L2) ≅ F₃ [r2, PE2 F1]: Prop 1.15(1)/(2) (PDF p.7,
>             S6.1 row 17) — F₃ := Im(∆₂ → ∆₃) ≅ F_{φ₃} = k(L2) by
>             g + P₀⁺ ↦ res(g(x₀)), x₀ a Φ₂-root; FGMN make this
>             identification themselves at §3.2 (PDF p.15: "By
>             Proposition 1.15, Fᵢ is a field which may be
>             identified with the residue class field F_{φᵢ}"). The
>             pre-repair parenthetical here — "T(b)′(iii)'s
>             identification (η₂ ↔ z₂)" — was wrong on both legs:
>             T(b)′(iii) defines the repo leaf read and the repo
>             field K₂ = F_Q(η, η₂) with no FGMN contact, and under
>             the canonical identification the LETTERS do not
>             correspond in general — the letter formula below gives
>             z₂ = η₂·z₁^{−⌊ℓ₁u₂/e₁⌋}.”

**DERIVATION:** `[DEFINITIONAL]` (R-FGMN) is Def 3.16 read at `i = 3` with a single term; (R-repo) is the corpus's GENHN-2′ coherent read. **Compile-time verification of Prop 1.15:** L340–344 read `Proposition 1.15. If φ is a key polynomial for µ, then / (1) R(φ) is the kernel of the onto ring homomorphism ∆ ։ Fφ determined by g(x) + / P0+ 7→ g(θ) + mφ . In particular, R(φ) is a maximal ideal of ∆. / (2) For any augmented valuation µ′ = [µ; (φ, λ)], R(φ) = Ker(∆ → ∆(µ′ )). Thus, the / image of ∆ → ∆(µ′ ) is a field, canonically isomorphic to Fφ .` ✓ EXACT match for both cited items.

**SUPERSESSION KIND:** `replacement` (r2 F1) — the `(η₂ ↔ z₂)` parenthetical is replaced by the canonical evaluation identification. The replaced text is quoted in place, so nothing is lost.

**CONDITIONALITY:** the two reads are defined ONLY on Φ₂-free `g` with `deg g < m₃` and exact grade β. This is the scope fence R3-2 (`.87`) re-invokes at B″ step (iv), where `digit(G)` is applied to an object that can reach `deg ≥ m₃`.

**RESOLUTION TRACE:** statement lines 492–516. Correction sites: lines 509–516 (the in-place r2 F1 replacement); L1451–1463 (R3-2's `digit` fence).

**TEETH:** the r2 letter-live probe LP1 (`.67`) machine-refutes the pre-repair parenthetical: “the TOOTH fired: η₂ ≠ z₂”.

**XREF:** `(R-FGMN)` count in this note = 1; `(R-repo)` count = 8. T1 cites `(R-FGMN)` (count 4 in the T1 note) as “Scalar codomain of the `i=2` residual read”.

---

### EFF.GENTOW2.34  [lemma — LEMMA GENTOW2-B′]

**CANONICAL STATEMENT:**

**FORM:** display (bold-headed lemma, three numbered clauses)

> “**LEMMA GENTOW2-B′.** There is a unit u(β) ∈ K₂^× = F₃^*,
> depending only on the grade β (not on g, not on x₀), namely
> u(β) := R_{3,β}(n̂₂(β̂)), such that for each Φ₂-free g of exact
> grade β:
>
>   (3)  R_{3,β}(g) = u(β) · digit(g).
>
> Consequently: (4) per grade β: (the repo read = the ε₂-normalized
> coordinate on the Φ₂-free elements of exact grade β) ⟺ u(β) = 1
> — B-2 as stated quantifies this over its per-grade families, and
> the recipe consumes it only at its used grades β_t, so the
> CONSUMED form of B-2 is u(β_t) = 1 there [r2, PE2 F4: the
> pre-repair "(4) B-2 ⟺ u(β) = 1 at each grade the recipe uses"
> conflated B-2's stated scope with the consumed scope; the
> honest-residue paragraph below already carried the consumed form]
> [r3: that consumed form u(β_t) = 1 is now machine-REFUTED at
> letter-live grades (PE4 LD2, honesty box) and the restated lemma
> no longer consumes it — it consumes (3)+(5) here and B″ (S5.2)];
> and (5) with arbitrary u, GENTOW2-B's sum gives R_{3,α}(Φ₃) =
> y^{f₃} − Σ_{t<f₃} u(β_t)·c_t y^t (the honesty box's transformation
> law).”

**DERIVATION:** proof at `.35`.

**ORIENTATION RECORD (parent charge item (b)).** `u(β)` is defined **as an FGMN-side read of a repo-side object**: `u(β) := R_{3,β}(n̂₂(β̂))` — the FGMN residual operator applied to the repo ladder normalizer at the grade. Direction (3) reads `FGMN = u · repo`, i.e. **`R_{3,β}(g) = u(β)·digit(g)`**, NOT the inverse. The r2 F3 finding (`.31`) exists precisely because the fallback clause had written the inverse convention. **Every consumer must carry direction (3) as written**; T1's own `(C3-B-law)` box states `u(β_t) = Θ_i(t)w_i^{f_{i+1}−t}` in the same orientation, and T3's `(ABS-G2)` states `u(β_t) = ϑ_{G2}(t)·w^{f₃−t}` — all three agree.

**CONDITIONALITY:**
- `g` Φ₂-free, `deg g < m₃`, exact grade `ν(g) = β`, `β ∈ Γ₂` (so `s₃(β) = 0`);
- (4) is a per-grade EQUIVALENCE, and its **consumed form** is `u(β_t) = 1` at the used slots — which is **REFUTED** (`.28`);
- **(4) has exactly ONE surviving consumer** in the effective text: the restated lemma's per-height-iff sentence (`.25`'s last sentence), per the PE6 FOLD (`.81`);
- (5) is a restatement of the summation, not a dependency (m1 CURE, `.76`);
- the in-place bracket “it consumes (3)+(5) here and B″” is **consumption-list site 2 of 5**; governed by the FOLD.

**RESOLUTION TRACE:** statement lines 518–538; proof lines 540–606; correction sites lines 529–532 (`[r2, PE2 F4]` in place), lines 533–535 (`[r3]` in place), L1303–1331 + L1369–1383 (the two-stage unification).

**TEETH:** the worked N1 trace (`.36`); B″'s step (iv) consumes (3) (`.44`).

**XREF:** STATEMENT_LEDGER row 3 (lines 518–538, md5-8 `bae471b0`) — span byte-verified ✓.

---

### EFF.GENTOW2.35  [proof — LEMMA GENTOW2-B′, with the repaired h-step]

**CANONICAL STATEMENT:**

**FORM:** italic-headed proof with a division display and four tagged sub-steps

> “*Proof.* u(β) ≠ 0: the ladder monomial n̂₂(β̂) has exact grade β
> (B-1) and single-pin N₃-polygon {(0, β̂/e(µ₂))}, so R_{3,β}(n̂₂) ≠ 0
> by Cor 4.4(1) [L1089 region, PDF p.21]. Now take g with digit d :=
> digit(g) ∈ K₂^× and let ẑ_d be a grade-0 ladder lift of d (grade-0
> lifts exist and read to d: T(b)′(iii), accepted — a repo-internal
> supply, no FGMN contact). [r2, PE2 F2 — the pre-repair step applied
> B-1 to h := g − ẑ_d·n̂₂(β̂) directly, outside B-1's deg < D₂
> scope: deg(ẑ_d·n̂₂(β̂)) reaches m₃ = D₂ at the record's own N1
> frame (worked trace below). Repaired h-step:] Divide the lift
> product by Φ₂:
>
>     ẑ_d·n̂₂(β̂) = q·Φ₂ + ρ,   deg ρ < m₃,   deg q ≤ m₃ − 2
>
> (both factors have deg ≤ m₃ − 1). Then:
>
>   (h-i) digit(ρ) = d and ν(ρ) = β exactly: x₀ is a Φ₂-root, so
>         evaluation kills the qΦ₂ term — ρ(x₀) = ẑ_d(x₀)·n̂₂(β̂)(x₀)
>         — hence res(ρ(x₀)/n̂₂(β̂)(x₀)) = res(ẑ_d(x₀)) = d ≠ 0, and
>         B-1 (deg ρ < D₂: IN scope) turns the nonzero read into
>         ν(ρ) = µ₂(ρ) = β exact.
>   (h-ii) ν(qΦ₂) ≥ β: qΦ₂ = ẑ_d·n̂₂(β̂) − ρ, a difference of two
>         elements of ν-value β.
>   (h-iii) ν(qΦ₂) > β STRICTLY, so R_{3,β}(qΦ₂) = 0 by Lemma 3.17
>         [L982, PDF p.19, [r1]-added cite]. Two legs (q ≠ 0 WLOG,
>         else the term is absent). Leg e₃ ≥ 2: ν(qΦ₂) = ν(q) + w₃
>         + λ₃ with ν(q) = µ₂(q) ∈ Γ₂ (deg q < m₃, Φ₂-free, Prop
>         1.9) and w₃ ∈ Γ₂ but λ₃ ∉ Γ₂ (gcd(h₃, e₃) = 1, e₃ ≥ 2),
>         so ν(qΦ₂) ∉ Γ₂ ∋ β and (h-ii)'s ≥ sharpens to >. Leg
>         e₃ = 1 — the unit-q corner PE2 F2 flagged as unfenced,
>         CLOSED here rather than fenced: suppose ν(qΦ₂) = β.
>         Additivity gives R_{3,β}(ẑ_d·n̂₂(β̂)) = R_{3,β}(ρ) +
>         R_{3,β}(qΦ₂). The left side and R_{3,β}(ρ) have y-degree
>         0 (a grade-0 × single-pin product, resp. a deg < m₃
>         single-point-polygon element — Cor 4.4(3)); but Cor
>         4.7(2) at the Γ₂-graded factor q plus eq (14) [Q7] give
>         R_{3,β}(qΦ₂) = R_{3,ν(q)}(q)·R_{3,w₃+λ₃}(Φ₂) =
>         R_{3,ν(q)}(q)·y^{⌊1/e₃⌋} = R_{3,ν(q)}(q)·y at e₃ = 1,
>         of y-degree exactly 1 with coefficient R_{3,ν(q)}(q) ≠ 0
>         (Cor 4.4(1): exact grade, single-point polygon). A
>         y-degree-0 identity cannot carry a nonzero y-linear term:
>         contradiction, hence ν(qΦ₂) > β at e₃ = 1 too.
>   (h-iv) B-1, now in scope: h′ := g − ρ has deg < D₂ and repo
>         digit d − d = 0 at grade β (by (h-i)), hence ν(h′) > β by
>         B-1's no-cancellation clause — h′ ∈ P_β^+(µ₃) — so
>         R_{3,β}(h′) = 0 by Lemma 3.17.
>
> Additivity (Cor 4.7(1) [Q8], twice: g = h′ + ρ and ẑ_d·n̂₂(β̂) =
> qΦ₂ + ρ, with (h-iv) and (h-iii) killing the h′ and qΦ₂ terms)
> gives R_{3,β}(g) = R_{3,β}(ρ) = R_{3,β}(ẑ_d·n̂₂(β̂)), and
> multiplicativity at a grade-0 factor (Cor 4.7(2) [Q8], β′ = 0 ∈ Γ₂
> — Cor 4.7 carries no degree hypothesis, so the deg = m₃ product is
> legitimate HERE, unlike in B-1) factors it as
> R_{3,0}(ẑ_d)·R_{3,β}(n̂₂(β̂)). Finally R_{3,0}(ẑ_d) = d: the
> grade-0 degree-0 read is the F₃-algebra residue (Thm 4.8 [L1136,
> PDF p.22, [r1]-added cite]), and under the canonical evaluation
> identification (Prop 1.15(1), the (R-repo) display) that residue
> IS res(ẑ_d(x₀)) = d — no letter correspondence enters [r2, PE2
> F1: the pre-repair sentence attributed this step to "T(b)′(iii):
> η₂ ↔ z₂", wrong on both legs — see (R-repo) and the letter
> formula below]. Hence R_{3,β}(g) =
> d·u(β) = u(β)·digit(g). x₀-freeness of u is by inspection: u(β) =
> R_{3,β}(n̂₂(β̂)) never sees x₀. (4): the recipe's k̂_t has digit
> c_t by construction (a K₂-digit lift), so R_{3,β_t}(k̂_t) =
> u(β_t)c_t, and B-2's on-the-nose form is exactly u(β_t) = 1. (5):
> substitute into the Cor-4.7(1) sum of GENTOW2-B's proof;
> non-emptiness of each grade is Cor 3.3 [L647, PDF p.12, [r1]-added
> cite] or the ladder itself. ∎”

**DERIVATION:** `[DERIVED]` **All four `[r1]`-added FGMN cites re-verified at compile time:** Lemma 3.17 at L982 (`Lemma 3.17. For all 0 ≤ i ≤ r, α ∈ Γi , the operator Ri,α vanishes on Pα+ (µi ).`) ✓; Thm 4.8 at L1136 (`Theorem 4.8. The mapping Rr,0 : ∆ −→ Fr [y] is an isomorphism of Fr -algebras and…`) ✓; Cor 3.3 at L647 (`Corollary 3.3. Let 1 ≤ i ≤ r. For any (s, β) ∈ Z≥0 × Γ(µi−1 ), there exists a ∈ K[x] such that deg a < deg φi and Nµi−1 ,φi (aφsi ) = {(s, β)}.`) ✓; Cor 4.4 items (1)/(3) at L1085/L1088 ✓ — **NEAR-MISS on the L1089 pin**: item (1) is at L1085 and item (3) at L1088, not L1089 (which is item (4)); the note hedges with “[L1089 region]”, so this is recorded as a NEAR-MISS, not an error (§4.6 NM-1).

**SUPERSESSION KIND (two, chained):**
`CHAIN:` frozen pre-repair h-step (B-1 applied to `h := g − ẑ_d·n̂₂(β̂)`) → **r2 F2 `replacement`** (the Φ₂-division h-step, with the `e₃ = 1` corner CLOSED rather than fenced) → **r2 F1 `replacement`** at the `R_{3,0}(ẑ_d) = d` step (attribution moved from T(b)′(iii) to Prop 1.15/Thm 4.8). **TERMINAL: this unit** (both replacements are in place).

**CONDITIONALITY:** requires T(b)′(iii)'s grade-0 lift existence (accepted corpus, repo-internal, no FGMN contact); requires Cor 4.7(2)'s absence of a degree hypothesis (verified at `.15`); the `e₃ = 1` leg's y-degree contradiction requires `R_{3,ν(q)}(q) ≠ 0` from Cor 4.4(1).

**RESOLUTION TRACE:** statement lines 540–606; proof is the unit; correction sites lines 544–549 (`[r2, PE2 F2]` in place), lines 596–599 (`[r2, PE2 F1]` in place). Records at S10 F1/F2 (L1096–1126).

**TEETH:** the `[r2]` worked trace (`.36`) exhibits the repair at the record's own N1 frame — a `PROOF-ONLY` teeth row (rule 16): the interesting content is the proof, and the note's own coverage sentence is “the e₃ = 1 unit-q corner the report flagged as unfenced is thereby CLOSED, not fenced.”

---

### EFF.GENTOW2.36  [run-record — the worked trace of the repaired h-step at N1]

**CANONICAL STATEMENT:**

**FORM:** italic-headed worked example

> “*[r2] Worked trace of the repaired h-step at the frame PE2 F2
> exhibited (N1, K₂ = F₄, grade β̂ = 7 — the PE1-digit-table grade).*
> Frame data recomputed this round: Φ′ = x² − 2 (w₂ = 1, λ₂ = 1/2,
> µ₂(Φ′) = 3/2), Φ₂b = Φ′² − 2xΦ′ − 8 (m₃ = 4, w₃ = 3, λ₃ = 1/4,
> e₃ = 2, e(µ₂) = 2, Γ₂ = ½ℤ). ẑ_{η₂} = xΦ′/4 (ν = 1/2 + 3/2 − 2 =
> 0; the minimal grade-0 monomial lift of an F₄∖F₂ class there),
> n̂₂(7) = 8x (dv₂ = 2(3 + 1/2) = 7), product = 2x²Φ′ of deg 4 = m₃
> — B-1 inapplicable as written, the PE2 finding. Division:
> 2x²Φ′ = 2·Φ₂b + (4xΦ′ + 4Φ′ + 16), so q = 2, ρ = 4xΦ′ + 4Φ′ + 16,
> deg ρ = 3 < 4 ✓. (h-i): dv₂-pins of ρ — 4Φ′ ↦ 7 (the single
> on-grade monomial), 4xΦ′ ↦ 8, 16 ↦ 8 — so ν(ρ) = 7/2 = β exact;
> digit(ρ) = res(4Φ′(x₀)/(8x₀)) = res(ẑ_{η₂}(x₀))·res(2/x₀²) =
> d·z₁^{−1} = d (this frame: z₁ = 1, and independently x₀² = 2 +
> O(v > 1) forces res(x₀²/2) = 1 — note the z₁-power surfacing in a
> digit comparison, the F1 letter mechanism in miniature). (h-iii),
> e₃ = 2 leg: ν(2Φ₂b) = 1 + 13/4 = 17/4 ∉ Γ₂, dv₂ = 17/2 > 7 ✓
> strict. [The PE2 report's sketch wrote "dv₂(2Φ₂b) = 2 + 7 = 9";
> recomputed here dv₂(Φ₂b) = e(µ₂)(w₃ + λ₃) = 2·(13/4) = 13/2 — its
> 9 should be 17/2; the inequality 17/2 > 7 holds and the repair is
> unaffected.] (h-iv): h′ = g − ρ, deg < 4, digit 0, B-1 in scope. ✓”

**DERIVATION:** `[RECORD]` A hand computation, re-derived in the r2 round rather than transcribed from the report.

**ARITHMETIC AUDIT (rule 22) — every number recomputed fresh:**

`[TABLE]`

| Claim | Recomputation | ✓ |
|---|---|---|
| `µ₂(Φ′) = w₂ + λ₂ = 1 + 1/2 = 3/2` | 3/2 | ✓ |
| `n̂₂(7) = 8x` at `dv₂ = 2(3 + 1/2) = 7` | `dv₂(8x) = e(µ₂)·v(8x) = 2(3 + 1/2) = 7` | ✓ |
| `ẑ_{η₂} = xΦ′/4` has `ν = 0` | `1/2 + 3/2 − 2 = 0` | ✓ |
| product `= 2x²Φ′`, `deg 4 = m₃` | `(xΦ′/4)(8x) = 2x²Φ′`, degree `1+1+2 = 4` | ✓ |
| `2x²Φ′ = 2Φ₂b + (4xΦ′ + 4Φ′ + 16)` | `Φ′ = x²−2 ⟹ x² = Φ′+2 ⟹ 2x²Φ′ = 2Φ′² + 4Φ′`; and `2Φ₂b + 4xΦ′+4Φ′+16 = (2Φ′²−4xΦ′−16) + 4xΦ′+4Φ′+16 = 2Φ′²+4Φ′` | ✓ **EXACT** |
| `deg ρ = 3` | `deg(4xΦ′) = 3` | ✓ |
| pins `4Φ′ ↦ 7`, `4xΦ′ ↦ 8`, `16 ↦ 8` | `2(2+3/2)=7`; `2(2+1/2+3/2)=8`; `2·4=8` | ✓ |
| `ν(ρ) = 7/2 = β` | `min(7,8,8)/e(µ₂) = 7/2` | ✓ |
| `ν(2Φ₂b) = 1 + 13/4 = 17/4` | `ν(Φ₂b) = w₃+λ₃ = 3+1/4 = 13/4`; `ν(2) = 1` | ✓ |
| `17/4 ∉ Γ₂ = ½ℤ` | `17/4 = 4.25 ∉ {…, 4, 4.5, …}` | ✓ |
| `dv₂ = 17/2 > 7` | `2·17/4 = 17/2 = 8.5 > 7` | ✓ |
| the report's `9` should be `17/2` | `dv₂(Φ₂b) = 2·13/4 = 13/2`; `dv₂(2) = 2`; `13/2 + 2 = 17/2 ≠ 9` | ✓ **the note's correction of the report is right** |

Zero arithmetic defects; one **inbound supplier-finding confirmed** (the PE2 report's own slip).

**CONDITIONALITY:** a single frame (N1, `f₁ = 1` over `q = 2`, `z₁ = 1`). The trace's own parenthetical flags the letter-blindness in miniature.

**RESOLUTION TRACE:** lines 608–627.

**TEETH:** `PROOF-ONLY` row (rule 16) — the trace guards `.35`'s h-step and nothing else.

---

### EFF.GENTOW2.37  [lemma — the LETTER FORMULA]

**CANONICAL STATEMENT:**

**FORM:** italic-headed paragraph + a tagged display

> “*The letter formula ([r2] — PE2 F1's canonical identification).*
> Under the (R-repo) evaluation identification the two level-2
> letters are related by an explicit z₁-twist, derived from the PDF
> data (sources PDF-verified this round, S6.1 rows 17–19):
>
>     z₂ = η₂ · z₁^{−⌊ℓ₁u₂/e₁⌋}      (LETTER FORMULA)”

**DERIVATION:** proof at `.38`.

**CONDITIONALITY:** holds under the canonical evaluation identification (Prop 1.15(1)); `ℓ₁` is FGMN's §3.3 datum with `ℓ₁h₁ + ℓ′₁e₁ = 1`, `0 ≤ ℓ₁ < e₁`.

**RESOLUTION TRACE:** lines 629–634.

**TEETH:** the r2 letter-live probe LP1, GREEN 21/0 first-run-under-seal, which “fired LIVE — z₁ ∈ F₄∖F₂ (z₁² + z₁ + 1 = 0), η₂ = z₁, z₂ = 1 = η₂·z₁^{−4} at ⌊ℓ₁u₂/e₁⌋ = ⌊9/2⌋ = 4” (`.67`). **Arithmetic check:** `z₁³ = 1` in `F₄^×`, so `η₂·z₁^{−4} = z₁·z₁^{−4} = z₁^{−3} = 1 = z₂` ✓ EXACT. Also the S2 witness: `⌊ℓ₁u₂/e₁⌋ = ⌊1·5/2⌋ = 2`, giving `z₂ = η₂·z₁^{−2}` ✓ matching L655.

**XREF:** `LETTER FORMULA` count in this note = 11; T1's A7 SPAN PIN 1 pins it (“accepted file `GENTOW2`, S5.1 level-two letter display”), and T1's absorption row A7 records it as “**Verbatim** at level 2”.

---

### EFF.GENTOW2.38  [proof — the LETTER FORMULA]

**CANONICAL STATEMENT:**

**FORM:** italic-headed proof paragraph

> “*Derivation.* FGMN's letter is z₂ := the image of y₂ = H_{µ₂}(γ₂)
> under ∆₂ → ∆₃ (PDF p.17 display), where γ₂ = φ₂^{e₂}π₂^{−u₂} with
> u₂ := e₂V₂ + h₂ (Def 3.12, p.16: γᵢ = (Φᵢ)^{eᵢ}(πᵢ)^{−hᵢ},
> Φᵢ = φᵢπᵢ^{−Vᵢ}; the §3.2 data V₂ = e(µ₁)w₂, h₂ = e(µ₂)λ₂ with
> eq (9), pp.15–16, give e₂V₂ + h₂ = e(µ₂)(w₂ + λ₂) = the S2
> dictionary's u₂ = dv₂(Φ′)), and π₂ = Φ₁^{ℓ₁}π^{ℓ′₁} = x^{ℓ₁}π^{ℓ′₁}
> (§3.3, p.16: ℓ₁h₁ + ℓ′₁e₁ = 1, 0 ≤ ℓ₁ < e₁; Φ₁ = x since V₁ =
> e(µ₀)µ₀(x) = 0). Under Prop 1.15(1) (p.7) the class evaluates:
> z₂ = res(γ₂(x₀)) = res(Φ′(x₀)^{e₂}/π₂(x₀)^{u₂}). The repo letter
> is η₂ = res(Φ′(x₀)^{e₂}/n̂(u₂)(x₀)) with n̂(u₂) = x^iπ^a the
> letter-free ladder normalizer at dv₁-height u₂, 0 ≤ i < e₁
> (T(b)′(i) normal form). The ratio n̂(u₂)/π₂^{u₂} = x^{i−ℓ₁u₂}
> π^{a−ℓ′₁u₂} is a value-0 monomial, and a value-0 monomial
> x^{e₁k}π^{−h₁k} = γ₁^k has residue z₁^k (γ₁ = x^{e₁}π^{−h₁},
> Def 3.12 at i = 1). Both n̂(u₂) and π₂^{u₂} sit at dv₁-height u₂
> (dv₁(π₂) = ℓ₁h₁ + ℓ′₁e₁ = 1), so ih₁ ≡ ℓ₁h₁u₂ mod e₁, i.e.
> i ≡ ℓ₁u₂ mod e₁ (gcd(h₁, e₁) = 1); with 0 ≤ i < e₁ this pins
> k = (i − ℓ₁u₂)/e₁ = −⌊ℓ₁u₂/e₁⌋. Multiplying the two residues
> gives the display. ∎ At the S2 witness (e₁ = 2, h₁ = 1, u₂ = 5,
> ℓ₁ = 1 ⟹ π₂ = x; i = 1, a = 2): z₂ = η₂·z₁^{−2}.”

**DERIVATION:** `[DERIVED]` **Compile-time verification of the three FGMN legs.** Def 3.12 at L819–821: `Definition 3.12. We take π0 = π1 = π, Φ0 = φ0 = γ0 = x and / Φi = φi (πi )−Vi , γi = (Φi )ei (πi )−hi , πi+1 = (Φi )ℓi (πi )ℓ′i , 1 ≤ i ≤ r.` ✓ — matches the note's rendering exactly. §3.3's `ℓᵢ, ℓ′ᵢ` at L814–816: `we consider integers ℓi , ℓ′i uniquely determined by / ℓi hi + ℓ′i ei = 1, 0 ≤ ℓi < ei .` ✓. §3.2 data + eq (9) at L785–803: `Vi := e(µi−1 )wi`, `hi := e(µi )λi`, `λi = hi /(e0 · · · ei )` ✓.

**ARITHMETIC AUDIT (rule 22).** `e₂V₂ + h₂ = e₂·e(µ₁)w₂ + e(µ₂)λ₂ = e(µ₂)w₂ + e(µ₂)λ₂ = e(µ₂)(w₂+λ₂)` (using `e(µ₂) = e₂e(µ₁)`) ✓ = `u₂` per the S2 dictionary ✓. At the S2 witness: `e₁ = 2, h₁ = 1 ⟹ ℓ₁h₁ + ℓ′₁e₁ = 1` with `0 ≤ ℓ₁ < 2` gives `ℓ₁ = 1, ℓ′₁ = 0` ✓, so `π₂ = x` ✓; `i ≡ ℓ₁u₂ = 5 ≡ 1 mod 2` with `0 ≤ i < 2` gives `i = 1` ✓; `k = (1 − 5)/2 = −2 = −⌊5/2⌋` ✓ EXACT.

**CONDITIONALITY:** requires T(b)′(i)'s ladder normal form (accepted corpus). The `z₂ = res(γ₂(x₀))` step applies Prop 1.15(1) to a RATIONAL class; **that gap is closed by C-m1** (`.69`), a dated append.

**RESOLUTION TRACE:** statement/proof lines 636–655; correction sites L1171–1194 (C-m1's denominator-clearing bridge).

**TEETH:** LP1 (`.67`); the PE3 fresh route's `z₂ ≠ 1` contacts at `p = 3/F₉` (`.68`).

---

### EFF.GENTOW2.39  [scope record — the LETTER FORMULA's three consequences]

**CANONICAL STATEMENT:**

**FORM:** italic-headed paragraph, three numbered items

> “*Consequences ([r2]).* (i) FGMN's ψ₂ = minpoly(z₂) is the
> z₁^{⌊ℓ₁u₂/e₁⌋}-twist of the repo ψ₂ = minpoly(η₂); the two agree
> on the nose exactly when the twist fixes ψ₂ — in particular when
> z₁^{⌊ℓ₁u₂/e₁⌋} = 1 (e.g. ℓ₁ = 0, or f₁ = 1 over q = 2 which
> forces z₁ = 1). (ii) LETTER-BLINDNESS of the record, stated
> honestly: the 13 machine witnesses standing at PE2 (5 committed +
> 2 battery-new + 3 PE1-fresh + 3 PE2-fresh) each sit at f₁ = 1
> over q = 2, where z₁ = 1 and the twist is invisible — the record
> could not have caught the pre-repair "η₂ ↔ z₂" parenthetical; the
> r2 probe (S10, gentow2_r2_letter_probe.py) is the first
> letter-live (f₁ = 2, z₁ ∈ F₄∖F₂) machine contact and tests the
> LETTER FORMULA itself at a frame where the twist acts. (iii) B′
> SURVIVES the canonical identification (re-derived this round, per
> the PE2 charge): the lemma's statement and proof consume only the
> evaluation identification — never a letter correspondence — at
> exactly two sites (the (R-repo) display and the R_{3,0}(ẑ_d) = d
> step), both now labeled Prop 1.15; u(β), (3), (4), (5) and the
> x₀-/g-freeness inspection stand as displayed. The downstream
> consumption "η₂(ξ) is a ψ₂-root" survives the twist by the S4
> consumption note's [r2] clause (single-embedding coherence).”

**DERIVATION:** `[DERIVED]` from `.37`.

**CONDITIONALITY:** item (i) is the source of R3-4's standing disambiguation (`.89`) — `ψ₂^FGMN ≠ ψ₂^repo` in general.

**RESOLUTION TRACE:** lines 657–676. Correction site: R3-4 at L1477–1492 promotes item (i) into a per-site fence.

**TEETH — disposition `signed vacuity disclosure` (rule 20):** item (ii) is the note declaring, in advance, that its entire 13-witness record was tested on geography where the effect under test is invisible. This is the disclosure PE4 later cashed.

---

### EFF.GENTOW2.40  [instrument-audit — what remains cross-frame, RE-SCOPED at r3]

**CANONICAL STATEMENT:**

**FORM:** italic-headed paragraph with a dated re-scope bracket

> “*What remains cross-frame (the honest residue) [r3 RE-SCOPED — the
> pre-PE4 version of this paragraph overclaimed underivability; PE4
> [F1] flagged the tension, B″ resolves it].* u(β)'s per-grade
> VARIATION is repo-derivable after all: LEMMA GENTOW2-B″ (S5.2)
> proves u(β_t) = ϑ(t)·w^{f₃−t} with ϑ(t) the repo-internal
> n̂₂-cocycle — exactly the SPECIES this paragraph previously
> contrasted away ("per-height coherent digits vs the multiplicative
> side residual, both built on the same ladder normalizers"); the
> PE4-measured values (u₁, u₀) = (1, z₁) at the LD grades are
> (ϑ(1), ϑ(0)), w-quotiented by the decode frame. What remains
> genuinely cross-frame is the SINGLE slot-independent unit
> w = u(κ̄): by Thm 4.2's normal form H_µ(g) =
> x₃^{s}p₃^{u}R_{3,β}(g)(y₃), it is the coordinate of the one repo
> ladder monomial n̂₂(u₃) in FGMN's canonical homogeneous frame
> x₃, p₃, y₃ — an explicit z₁, z₂-monomial, computable by a level-3
> letter-formula-style derivation but not computed anywhere in the
> corpus — and w is CONSUMER-INVISIBLE (it acts by the
> grade-covariant substitution y ↦ wy, preserving factor patterns;
> GENTOW2-A consumes only hypothesis (ii) with an admissible
> residual, and ψ₃^{(w)} is admissible). The pre-repair sentence
> "GENTOW5's LEMMA GENTOW5-A1 does NOT supply it" survives only for
> w; as a claim about the grade-variation it was WRONG. Whether ϑ
> literally coincides with GENTOW5-A1's ϑ_t (that note's arc is in
> flight) is left to that arc — nothing here consumes the
> correspondence. u ≡ 1 (= B-2 on the nose) is REFUTED letter-live
> (honesty box) and is consumed NOWHERE in the repaired note.”

**DERIVATION:** `[RECORD — self-audit]` Type `instrument-audit` (rule 33): the note audits its OWN earlier scope claim and finds it overclaimed. Not `changes-record` (a mathematical statement does move — B″); not `run-record` (no run).

**SUPERSESSION KIND:** **`partial-withdrawal`** (rule 36). The sentence “GENTOW5's LEMMA GENTOW5-A1 does NOT supply it” is re-issued with most of the clause surviving. **Replacement display, verbatim:** *“The pre-repair sentence "GENTOW5's LEMMA GENTOW5-A1 does NOT supply it" survives only for w; as a claim about the grade-variation it was WRONG.”*

**CONDITIONALITY:**
- the Thm 4.2 normal-form sentence is **DESCRIPTIVE ONLY** — S6.1 row 23 (`.77`) records that “no lemma conclusion consumes it (w's unit-hood comes from Cor 4.4(1) in B″'s proof)”. HYP.145's gate;
- **`STALE-SELF-DESCRIPTION` (rule 26):** “not computed anywhere in the corpus” is falsified by PE6's measurement; the frozen sentence carries the dated bracket at `.82` (“[2026-08-10: measured (not derived) at 4 frames; the closed-form letter derivation stays open]”). The sentence is NOT corrected under the freeze; the reader must be told;
- N-7: the ϑ ↔ ϑ_t correspondence is explicitly NOT consumed here. See OPEN-CALL 2 — downstream notes have since adjudicated it, as an inverse.

**RESOLUTION TRACE:** statement lines 678–703; correction sites lines 678–681 (`[r3]` re-scope, in place), L1403–1407 (the post-PE6 dated bracket on body L692–694), L1339 (S6.1 row 23).

**TEETH:** PE6's `w`-measurement at 4 frames / 6 primes, GREEN 68/0 run-2 (`.82`); its two discrimination pairs both fired.

**AUDIT (rule 33 `instrument-audit`; rule 27 `decorrelated-model audit`):** the finding — that the paragraph “overclaimed underivability” — came from PE4, an outside pass, not from any battery.

---

### EFF.GENTOW2.41  [definition — the S5.2 setting and the ϑ-cocycle]

**CANONICAL STATEMENT:**

**FORM:** bold-headed paragraph + a tagged display

> “Setting: the recipe geometry of GENTOW2-B (slots t < f₃; slot
> grades β_t := u₃(f₃−t)/e(µ₂) ∈ Γ₂, s₃(β_t) = 0 as in S5.1's
> opening; κ̄ := β_{f₃−1} = u₃/e(µ₂) the top slot's grade). Define
>
>   ϑ(t) := res((n̂₂(u₃(f₃−t)) / n̂₂(u₃)^{f₃−t})(x₀)) ∈ K₂^×.”

**DERIVATION:** `[DEFINITIONAL]`

**ORIENTATION RECORD:** see `.25` — this is the defining display the whole downstream orientation table is anchored on. **`κ̄ = β_{f₃−1}` means `ϑ(f₃−1) = res(n̂₂(u₃)/n̂₂(u₃)^1) = 1`** — the top-slot normalization the note states at `.25` and T3 checks at its §8.1 item 1 (`ϑ_N(0;q) = ϑ_N(1;q) = 1`).

**CONDITIONALITY:** `s₃(β_t) = 0` inherits S5.1's opening argument (eq (12) at i = 3 with `gcd(h₃,e₃) = 1`).

**RESOLUTION TRACE:** lines 709–713.

**TEETH:** decode COC pins at both PE4 frames (`.45`); PE5's direct cocycle measurement `theta(0) = z2^2` at tower GB (`.75`).

---

### EFF.GENTOW2.42  [lemma — the γ-calculus: ϑ is x₀-free and letter-valued]

**CANONICAL STATEMENT:**

**FORM:** italic-headed paragraph

> “*γ-calculus (ϑ is x₀-free and letter-valued).* The ratio is a
> value-0 Laurent monomial in π, x, Φ′, and the value-0 Laurent
> monomials x^i π^a Φ′^b form exactly the group ⟨γ₁, γ₂⟩: value 0
> reads ih₁e₂ + ae₁e₂ + bu₂ = 0 after clearing e₁e₂; mod e₂ this
> forces bu₂ ≡ bh₂ ≡ 0 (u₂ = e₂V₂ + h₂, gcd(h₂, e₂) = 1), so e₂ | b;
> dividing by γ₂^{b/e₂} (γ₂ = Φ′^{e₂}π₂^{−u₂}, an x,π,Φ′-monomial by
> §3.3) leaves a value-0 x^{i′}π^{a′}, which is γ₁^{i′/e₁} (e₁ | i′
> from gcd(h₁, e₁) = 1). Residues under the evaluation
> identification: res(γ₁(x₀)) = z₁ and res(γ₂(x₀)) = z₂ — Def 3.12 +
> Prop 1.15 through the rider C-m1 denominator-clearing line, exact
> stable denominators, no new input. Hence ϑ(t) = z₁^j z₂^k for
> grade-determined integers j, k: x₀-free, letter-valued, equal to 1
> wherever that letter monomial is trivial; and ϑ(f₃−1) = 1.”

**DERIVATION:** `[DERIVED]` **Compile-time check of the source facts used:** `gcd(hi, ei) = 1` at L791 (`Lemma 3.2 shows that gcd(hi , ei ) = 1`) ✓; `γᵢ = (Φᵢ)^{eᵢ}(πᵢ)^{−hᵢ}` at L821 ✓; `πᵢ₊₁ = (Φᵢ)^{ℓᵢ}(πᵢ)^{ℓ′ᵢ}` at L821 ✓.

**CONDITIONALITY:** requires C-m1's denominator-clearing line (`.69`) for `res(γ₂(x₀)) = z₂` — a rational class, not a polynomial one. The note says so explicitly (“through the rider C-m1 denominator-clearing line”), which is a **forward reference from body text to an append** — the only one in the note, and it is coherent because C-m1 predates r3.

**RESOLUTION TRACE:** lines 715–727.

**TEETH:** the decode COC pins verify a γ-calculus prediction against a machine residue at two frames (`.45`).

---

### EFF.GENTOW2.43  [lemma — LEMMA GENTOW2-B″]

**CANONICAL STATEMENT:**

**FORM:** display (bold-headed lemma with one numbered identity and a corollary)

> “**LEMMA GENTOW2-B″.** For each slot t < f₃, with w := u(κ̄) =
> R_{3,κ̄}(n̂₂(u₃)):
>
>   (6)  u(β_t) = ϑ(t) · w^{f₃−t}.
>
> Consequently in the (B-law) sum (B′(5)): R_{3,α}(Φ₃) = y^{f₃} −
> Σ ϑ(t)w^{f₃−t}c_t y^t = w^{f₃}·P(y/w) with P(y) := y^{f₃} −
> Σ ϑ(t)c_t y^t — the realized residual is the w-substitution
> conjugate of the MULTIPLICATIVE-convention polynomial P, with P's
> irreducible-factor pattern for every value of w.”

**DERIVATION:** proof at `.44`.

**ARITHMETIC AUDIT (rule 22).** `Σ_t ϑ(t)w^{f₃−t}c_t y^t` versus `w^{f₃}P(y/w) = w^{f₃}[(y/w)^{f₃} − Σ_t ϑ(t)c_t(y/w)^t] = y^{f₃} − Σ_t ϑ(t)c_t w^{f₃−t}y^t` ✓ EXACT identity.

**BYTE-PIN (rule 23).** This unit's statement is the corpus's most-pinned display. Three independent pins, all re-verified at compile time:

`[TABLE]`

| Pin | Claim | Verification | ✓ |
|---|---|---|---|
| `docs/STATEMENT_LEDGER_2026-08-10.md` row 4 | `LEMMA GENTOW2-B″ \| 729–738 \| d4c8b885` at commit `33f86204` | `git cat-file -t 33f86204` = commit; L729–738 at `33f86204` byte-identical to HEAD | ✓ |
| `T5_WFRAME_2026-08-12.md` acceptance-pass ledger item 2 | “md5-8 `d4c8b885`, L729–738 @ `33f86204`”, with the disclosed mechanism note that a raw span md5 gives `8978f8ba…` | raw `sed -n '729,738p' \| md5sum` = `8978f8ba637beb26272fcbd362e277a3` — matches T5's disclosure exactly | ✓ |
| `runs/qgen/s0_check_postcampaign.txt` via HYPOTHESIS_LEDGER L1084 | “0 changed, 0 deleted, 2 added … both additions ADDED-allowed (HETOW-4 #2, GENTOW2-B″ #2)” | ledger-side statement-stability instrument, GREEN | ✓ |

**CONDITIONALITY:**
- `t < f₃`; the recipe geometry of `.41`;
- `w` is not computed here (N-6) and its value is not consumed; the factor-pattern claim is `for every value of w`;
- the corollary is stated “in the (B-law) sum (B′(5))” — B′(5) is a restatement per the m1 CURE (`.76`), so this is not a hidden dependency;
- **absorbed as `(ABS-G2)` by T3** (`.92`), with both cites live.

**RESOLUTION TRACE:** statement lines 729–738; proof lines 740–778; correction sites L1451–1463 (R3-2 fences step (iv)'s `digit(G)`), L1509–1521 (the S-2 absorption).

**TEETH:** decode MULT/COC/MP pins (`.45`); PE5's γ₂-live fresh route GREEN 91/0 including “first e3 = 2 x cocycle-live frame GA3” (`.75`).

---

### EFF.GENTOW2.44  [proof — LEMMA GENTOW2-B″]

**CANONICAL STATEMENT:**

**FORM:** italic-headed proof, four numbered steps

> “*Proof.* Fix t, write d := f₃ − t ≥ 1, N := n̂₂(u₃),
> M := n̂₂(u₃d): ladder monomials, deg < m₃, single-point N₃-polygon,
> exact grades κ̄ resp. β_t (B-1). Let ẑ be a grade-0 ladder lift of
> ϑ(t) (T(b)′(iii) supply, deg < m₃) and set G := ẑ·N^d, exact grade
> β_t.
>
> (i) R_{3,β_t}(G) = ϑ(t)·w^d, a y-degree-0 scalar: iterate Cor
> 4.7(2) [Q8] (no degree hypothesis — the B′ proof's own precedent;
> at each peel the split-off factor's grade, κ̄ resp. 0, lies in Γ₂)
> to get R_{3,β_t}(G) = R_{3,0}(ẑ)·R_{3,κ̄}(N)^d; R_{3,0}(ẑ) = ϑ(t)
> by Thm 4.8 + Prop 1.15 (the B′ proof's grade-0 step verbatim), and
> R_{3,κ̄}(N) = u(κ̄) = w by S5.1's definition of u; each factor is a
> y-degree-0 scalar (deg < m₃, single-point polygon — Cor 4.4(3)),
> hence so is the product.
>
> (ii) Φ₂-adic expansion G = Σ_{j≥0} Q_j Φ₂^j, deg Q_j < m₃. By Def
> 1.8 (ν = µ₃ = [µ₂; (Φ₂, λ₃)] is DEFINED by the expansion minimum
> µ′(g) = min_s µ′(g_sφ^s); PDF p.5, layout L250–255, [r3]-added
> cite, S6.1 row 21): ν(G) = min_j ν(Q_jΦ₂^j) = β_t, so every term
> has ν ≥ β_t and Cor 4.7(1) [Q8] gives R_{3,β_t}(G) =
> Σ_j R_{3,β_t}(Q_jΦ₂^j).
>
> (iii) Every j ≥ 1 term contributes 0 at y-degree 0: if
> ν(Q_jΦ₂^j) > β_t it dies by Lemma 3.17; if = β_t then — the S5.1
> h-iii dichotomy verbatim — either e₃ ∤ j, impossible since
> ν(Q_j) ∈ Γ₂ (deg < m₃, Φ₂-free, Prop 1.9) while jλ₃ ∉ Γ₂ would put
> the value outside Γ₂ ∋ β_t, or e₃ | j and Cor 4.7(2) + eq (14)
> [Q7] place R_{3,β_t}(Q_jΦ₂^j) = R_{3,ν(Q_j)}(Q_j)·y^{j/e₃} at
> y-degree ≥ 1.
>
> (iv) The j = 0 term: Φ₂(x₀) = 0 gives G(x₀) = Q₀(x₀), so
> digit(Q₀) = digit(G) = res(ẑ(x₀))·res((N^d/M)(x₀)) =
> ϑ(t)·ϑ(t)^{−1} = 1 ≠ 0; B-1 (deg Q₀ < m₃ = D₂, IN scope) gives
> ν(Q₀) = β_t exact, and B′(3) (S5.1, in scope: Φ₂-free, deg < m₃,
> exact grade) gives R_{3,β_t}(Q₀) = u(β_t)·digit(Q₀) = u(β_t),
> y-degree 0.
>
> Equating the y-degree-0 parts of (i) and (ii)–(iv):
> ϑ(t)·w^d = u(β_t). ∎”

**DERIVATION:** `[DERIVED]` **Compile-time verification of the `[r3]`-added cite:** Def 1.8 at L250–255 reads `Definition 1.8. Take φ ∈ KP(µ) and λ ∈ Q>0 . The augmented valuation of µ with respect / to these data is the valuation µ′ determined by the following action on K[x]: … • If g = Σ_{0≤s} gs φs is the φ-expansion of g, then µ′ (g) = min_{0≤s} {µ′ (gs φs )}.` ✓ — the note's step (ii) uses exactly the expansion-minimum clause.

**CONDITIONALITY:**
- step (iv)'s `digit(G)` token is **out of `digit`'s defined scope** at `d ≥ 2` (where `deg G` can reach `≥ m₃`). **R3-2 (`.87`) supplies the governing reading:** “`digit(G)` abbreviates the normalized evaluation residue `res(G(x₀)/M(x₀))`”. B-1 and B′(3) are invoked only on `Q₀`, which is in scope;
- step (iii) requires `gcd(h₃,e₃) = 1` for the `e₃ ∤ j` leg;
- consumes **B′(3)** at step (iv) and Cor 4.7(1)/(2), eq (14), Lemma 3.17, Def 1.8, Prop 1.9, Cor 4.4(3), Thm 4.8, Prop 1.15.

**ARITHMETIC AUDIT (rule 22).** Step (iv)'s digit computation: `digit(G) = res(G(x₀)/M(x₀)) = res(ẑ(x₀))·res(N(x₀)^d/M(x₀)) = ϑ(t)·ϑ(t)^{−1} = 1` — using `ϑ(t) := res((n̂₂(u₃d)/n̂₂(u₃)^d)(x₀)) = res(M/N^d)`, so `res(N^d/M) = ϑ(t)^{−1}` ✓ and `res(ẑ(x₀)) = ϑ(t)` by the lift's construction ✓. Consistent.

**RESOLUTION TRACE:** statement lines 740–778; correction sites L1451–1463 (R3-2), L1465–1475 (R3-3 acts on S5's α, not here).

**TEETH:** the `(BR1)`–`(BR5)` instantiation in T3's port is exactly this proof's steps (i)–(iv) (`.92`), and the S-2 consumption check ran PASS.

---

### EFF.GENTOW2.45  [run-record — machine verification of B″ at the PE4 frames]

**CANONICAL STATEMENT:**

**FORM:** italic-headed paragraph

> “*Machine verification at the PE4 frames (decode-probe pins CITED
> at their seals, not re-run: gentow2_pe4_decode.py +
> gentow2_pe4_decode_output.txt, GREEN 14/0 first-run-under-its-
> seal).* LP1 stage-3, e₃ = 1, f₃ = 2, u₃ = κ₃ = 19: N = n̂₂(19) =
> 4xΦ′, M = n̂₂(38) = 512x. γ-calculus RE-DERIVED this round:
> N²/M = 16x²Φ′²/(512x) = xΦ′²/32 = γ₂·γ₁⁵ — γ₁ = x²/2, γ₂ = Φ′²/x⁹
> (ℓ₁ = 1, ℓ′₁ = 0, u₂ = 9, e₂ = 2), exponent-lattice split:
> xΦ′²/32 ↦ (i,a,b) = (1,−5,2) = 1·(−9,0,2) + 5·(2,−1,0) — so
> ϑ(0)⁻¹ = res(N²/M) = z₂·z₁⁵ = z₂z₁² and ϑ(0) = z₂^{−1}z₁^{−5} =
> z₁ at LP1 (z₂ = 1 by the r2 probe; z₁³ = 1). Machine pin: decode COC = res(n̂₂(19)²/n̂₂(38)) = z₁² =
> ϑ(0)^{−1}, exact at both frames ✓. ϑ(1) = 1 (top slot). Realized
> residuals predicted by (6): P = y² + ϑ(1)c₁y + ϑ(0)c₀ =
> y² + z₁y + z₁c₀ — LD1 (c₀ = 1): y²+z₁y+z₁ ✓ decode MP1; LD2
> (c₀ = z₁²): y²+z₁y+z₁³ = y²+z₁y+1 ✓ decode MP2 (LD2 realized LD1's
> per-height prescription — the PE4 signature). The decode MULT
> checks (multiplicative digits (z₁, z₁) at LD1, (z₁, 1) at LD2) are
> the statement "realized = P" verbatim. LD3 (e₃ = 2, f₃ = 1,
> κ₃ = 37/2): a single slot t = 0 at d = 1, so ϑ(0) = 1 — no cocycle
> live at f₃ = 1, consistent with LD3 GREEN and with the fallback
> clause's f₃ ≤ 1 remark. The PE4-measured "(u₁, u₀) = (1, z₁) in
> the Φ₂/n̂₂(19)-read frame" is exactly (ϑ(1), ϑ(0)): that read
> frame is the w-conjugate frame, so it measures ϑ — the u ↔ ϑ VALUE
> coincidence the PE4 report flagged is identity (6) with w
> quotiented out, not an accident.”

**DERIVATION:** `[RECORD]` Artifacts verified to exist: `gentow2_pe4_decode.py` (4,853 B), `gentow2_pe4_decode_output.txt` (348 B).

**ARITHMETIC AUDIT (rule 22) — the γ-calculus recomputed from scratch:**

`[TABLE]`

| Step | Recomputation | ✓ |
|---|---|---|
| `N² = (4xΦ′)² ` | `16x²Φ′²` | ✓ |
| `N²/M = 16x²Φ′²/(512x)` | `= xΦ′²/32` (16/512 = 1/32) | ✓ |
| `xΦ′²/32` as `x^i π^a Φ′^b` at `π = 2` | `32 = 2⁵ ⟹ (i,a,b) = (1, −5, 2)` | ✓ |
| `γ₂ = Φ′^{e₂}π₂^{−u₂}` with `π₂ = x^{ℓ₁}π^{ℓ′₁} = x`, `u₂ = 9`, `e₂ = 2` | `Φ′²x^{−9} ⟹ (−9, 0, 2)` | ✓ (matches the note's `γ₂ = Φ′²/x⁹`) |
| `γ₁ = x^{e₁}π^{−h₁} = x²/2` | `(2, −1, 0)` | ✓ |
| lattice split `1·(−9,0,2) + 5·(2,−1,0)` | `(−9+10, 0−5, 2+0) = (1,−5,2)` | ✓ **EXACT** |
| `ϑ(0)^{−1} = z₂z₁⁵`, and `z₁³ = 1` | `z₁⁵ = z₁²`, so `= z₂z₁²`; at LP1 `z₂ = 1` ⟹ `z₁²` | ✓ matches decode COC |
| `ϑ(0) = z₂^{−1}z₁^{−5} = z₁^{−5} = z₁^{−5+6} = z₁` | `z₁` | ✓ |
| LD1 realized `P = y² + z₁c₁y + z₁c₀` at `c₁ = 1, c₀ = 1` | `y²+z₁y+z₁` | ✓ MP1 |
| LD2 at `c₀ = z₁²` | `y²+z₁y+z₁·z₁² = y²+z₁y+z₁³ = y²+z₁y+1` | ✓ MP2 |
| LD2's realized residual vs `.28`'s independent statement | `.28` says LD2 “realized a SINGLE (4,4) prime with realized residual y²+z₁y+1” | ✓ **cross-consistent** |
| LD3 at `f₃ = 1`: `ϑ(0) = ϑ(f₃−1) = 1` | top-slot normalization | ✓ |

Zero arithmetic defects across twelve independent checks.

**CONDITIONALITY:** two frames (LP1's LD1/LD2) plus LD3; `z₂ = 1` at LP1 is itself a machine result from the r2 probe, so the `ϑ(0) = z₁` conclusion is frame-specific.

**RESOLUTION TRACE:** lines 780–803.

**TEETH:** decode COC (cocycle value), MULT (multiplicative digits), MP (realized residual) — three independent pin families, GREEN 14/0.

---

### EFF.GENTOW2.46  [instrument-audit — the u ↔ ϑ adjudication]

**CANONICAL STATEMENT:**

**FORM:** italic-headed paragraph, four lettered items

> “*Adjudication of the u ↔ ϑ identity (the PE4 [F1] repair charge).*
> (a) YES, derivably: u's entire per-grade VARIATION is the
> repo-internal cocycle ϑ — identity (6), proved above at every
> recipe slot, no letter-dead restriction. (b) B-2's genuinely
> cross-frame content collapses from a per-grade family to the ONE
> unit w = R_{3,κ̄}(n̂₂(u₃)) per slot geometry, and w is
> consumer-invisible: factor patterns and prime splits are
> w-invariant, and GENTOW2-A consumes hypothesis (ii) with an
> admissible residual (ψ₃^{(w)} qualifies). (c) B-2 itself (u ≡ 1 at
> used slots) stays REFUTED: it would force ϑ(0)w² = 1 AND
> ϑ(1)w = 1 at LD2's geometry, i.e. z₁w² = 1 = w, impossible; the
> machine verdict (single prime against the prescribed split) is the
> realized witness. (d) Whether ϑ literally coincides with
> GENTOW5-A1's ϑ_t dictionary unit is NOT adjudicated here (that
> note's hostile arc is in flight; nothing here consumes the
> correspondence) — what is settled is that a repo-internal cocycle
> of exactly that species carries u's grade-variation.”

**DERIVATION:** `[DERIVED + RECORD]`

**ARITHMETIC AUDIT (rule 22) — item (c)'s impossibility, recomputed.** At LD2's geometry `f₃ = 2`, so slots are `t = 0` (`d = 2`) and `t = 1` (`d = 1`). `u(β_t) = 1` for both would give, via (6): `ϑ(0)w² = 1` and `ϑ(1)w¹ = 1`. With `ϑ(1) = 1` (top slot) the second forces `w = 1`; substituting into the first gives `ϑ(0) = 1`. But `ϑ(0) = z₁ ≠ 1` at LP1 (`.45`). **Contradiction** ✓ — and the note's compressed form “i.e. z₁w² = 1 = w” is the same computation ✓.

**CONDITIONALITY:** item (d) is the standing NON-IMPORT N-7. **See OPEN-CALL 2 — this is the single most consequential open call in the note, because T1/T3/T5 have since installed the correspondence as an INVERSE and GENTOW2's own text still says it is unadjudicated.**

**RESOLUTION TRACE:** lines 805–821.

**TEETH:** the LD2 machine verdict is item (c)'s realized witness.

**AUDIT (rule 27 `decorrelated-model audit`; rule 31 `hostile-pass certification`):** this unit IS the answer to an outside pass's repair charge, and the answer strengthened the note — `u`'s variation went from “genuinely cross-frame, underivable” to “derivable, identity (6)”.

---

### EFF.GENTOW2.47  [fence — the source declaration]

**CANONICAL STATEMENT:**

**FORM:** bold-headed paragraph

> “**Source.** Fernández, Guàrdia, Montes, Nart, "Residual ideals of
> MacLane valuations", arXiv:1305.0775v3
> (published J. Algebra 427 (2015) 30–75); local print
> docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt. NOT
> the excluded 2212.00294; no statement from 2212.00294 is consumed.”

**DERIVATION:** `[RECORD]` The AXIOM_FAITHFULNESS-discipline declaration.

**CONDITIONALITY:** none. N-5.

**RESOLUTION TRACE:** lines 825–829.

**TEETH:** `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` L48 independently records `[FGMN]`'s bibliographic identity and standing setting from the same local print at layout line 137 (§4.5 row RX16); `docs/TIGHTNESS_CENSUS_2026-08-11.md` row I-3 records it as “Standard literature (Fernández–Guàrdia–Montes–Nart), NOT 2212.00294”.

---

### EFF.GENTOW2.48  [supplier-finding — the [r1] provenance over-claim correction]

**CANONICAL STATEMENT:**

**FORM:** bracketed paragraph

> “[r1] The pre-repair sentence here read "numbering verified against
> the arXiv v3 PDF at ledger 63091ce" — an over-claim on both method
> and scope (PE1 F1): ledger 63091ce's check was against the LOCAL
> TEXT EXTRACTION (its own disclosed caveat), and its scope was
> GRTJC's cite set, of which only Cor 4.7 and eq (14) overlap this
> note's. The corrected provenance is S6.1 below, which closes the
> PDF leg directly.”

**DERIVATION:** `[RECORD]` A defect report against a prior repo ledger entry — type `supplier-finding` (rule 13). `git cat-file -t 63091ce` = commit ✓.

**SUPERSESSION KIND:** `replacement`.

**CONDITIONALITY:** none.

**RESOLUTION TRACE:** lines 831–837.

**TEETH:** S6.1 (`.50`), whose 22 rows all re-verify at compile time.

**AUDIT (rule 27 `transfer audit`):** the finding is that a verification performed for ANOTHER note's cite set was transferred to this note's without checking overlap. Only 2 of the 12 statements overlapped. This is the corpus's `extraction-corruption decorrelation` rule in action.

---

### EFF.GENTOW2.49  [instrument-record — the S6.1 two-leg method]

**CANONICAL STATEMENT:**

**FORM:** bold-headed paragraph

> “**Method.** (i) Identity: docs/references/
> fgmn_residual_ideals_1305.0775v3.pdf (md5
> da846c82f1fcb619cefb3feb8164191e, sha256
> 651b0cef64e6aea11526965d3ef7879d69ce7c0a31af497978c3e6192f615f35,
> 518,522 bytes) was compared 2026-08-09 against a fresh fetch of
> https://arxiv.org/pdf/1305.0775v3 — BIT-IDENTICAL (same md5, same
> size); PDF page 1 carries the stamp "arXiv:1305.0775v3 [math.NT]
> 26 Jul 2013" and the title/author block. (ii) Statement check: each
> row below was read VISUALLY off the rendered PDF page (Read-tool
> page extraction) and compared against the S3 quote — a leg
> decorrelated from the pdftotext layout extraction that the Lxxxx
> pins index (the extraction-corruption rule's independent leg).
> Verdict vocabulary: MATCH = statement content AND numbering agree
> with the S3 quote/instantiated use.”

**DERIVATION:** `[RECORD]`

**PIN VERIFICATION (rule 23) — recomputed at compile time:**

`[TABLE]`

| Declared | Recomputed | ✓ |
|---|---|---|
| md5 `da846c82f1fcb619cefb3feb8164191e` | `da846c82f1fcb619cefb3feb8164191e` | ✓ |
| sha256 `651b0cef64e6aea11526965d3ef7879d69ce7c0a31af497978c3e6192f615f35` | `651b0cef64e6aea11526965d3ef7879d69ce7c0a31af497978c3e6192f615f35` | ✓ |
| 518,522 bytes | `wc -c` = 518522 | ✓ |

**CONDITIONALITY:** leg (i)'s *bit-identity to arXiv's serving copy* is an **AS-OF-PIN** (rule 34): it was checkable evidence on 2026-08-09 and the local file still matches its own declared hash, but the remote comparison cannot be re-run offline. Leg (ii)'s visual reads are inherently non-reproducible by grep; the compiler re-verified their *targets* against the layout file instead (§4.1–4.2), which is the decorrelated leg's complement, not its substitute.

**RESOLUTION TRACE:** lines 841–854.

**TEETH:** the 22 MATCH rows themselves.

---

### EFF.GENTOW2.50  [table — S6.1 PDF-provenance rows 1–22]

**CANONICAL STATEMENT:**

**FORM:** `[TABLE]`

> | # | statement (S3 tag) | PDF page | layout pin | verdict |
> |---|---|---|---|---|
> | 1 | Lemma 1.11 [Q1] | 6 | L275 | MATCH |
> | 2 | Cor 1.13 [Q2] | 7 | L315 | MATCH |
> | 3 | Def 5.2 [Q3] | 24 | L1238–1239 | MATCH |
> | 4 | Lemma 5.3 [Q4] | 24 | L1240–1244 | MATCH |
> | 5 | Cor 4.4 (item 4 used) | 21 | L1089 | MATCH |
> | 6 | Cor 4.7 [Q8] | 21–22 | L1121–1126 | MATCH |
> | 7 | Cor 4.12 + proof constr. [Q5] | 22 | L1161–1166 | MATCH (incl. the print's "degre" typo, visually present in the PDF) |
> | 8 | Prop 5.7 [Q7] | 25 | L1276–1281 | MATCH |
> | 9 | eq (14) [Q7] | 19 | L1004 | MATCH |
> | 10 | Cor 5.6 | 24 | L1263–1265 | MATCH |
> | 11 | Thm 5.8 + degree-forcing display [Q6] | 25 | L1296–1302 | MATCH |
> | 12 | Thm 6.3 + proof opening [Q9] | 28 | L1458–1465 | MATCH |
> | 13 | Cor 6.4 + eq (23) [Q10] | 29 | L1523–1527 | MATCH |
> | 14 | Cor 3.3 (S5.1 [r1] cite) | 12 | L647 | MATCH |
> | 15 | Lemma 3.17 (S5.1 [r1] cite) | 19 | L982 | MATCH |
> | 16 | Thm 4.8 (S5.1 [r1] cite) | 22 | L1136 | MATCH |
> | 17 | Prop 1.15 (S5.1 [r2] identification + letter formula) | 7 | L340–344 | MATCH |
> | 18 | Def 3.12 + §3.3 ℓᵢ, ℓ′ᵢ data (S5.1 [r2] letter formula) | 16 | L813–821 | MATCH |
> | 19 | eq (9) + §3.2 data defs (S5.1 [r2] letter formula; S2 (e₃,f₃) row) | 15–16 | L785–806 | MATCH |
> | 20 | Lemma 3.13(1) (rider C-m1 bridge; [r3] elevated to consumed — PE4 F2) | 16 | L836–840 | MATCH |
> | 21 | Def 1.8 (S5.2 [r3] B″ proof: the φ-expansion minimum defines ν) | 5 | L250–255 | MATCH |
> | 22 | Prop 1.9(2) (S5 proof + S5.2(iii): Φ₂-free ⟹ ν = µ₂; [r3] inventory) | 6 | L258–261 | MATCH |

**DERIVATION:** `[RECORD]` The r1/r2/r3 two-leg verification record.

**ARITHMETIC AUDIT (rule 22) — row-count reconciliation, computed fresh, plus the layout-leg re-verification of every row:**

- The note's own count claims: S6's charge says “the 12 consumed statements + eq (14)”, S9 F1 says “13/13 MATCH (table S6.1), plus 3 [r1]-added cites (rows 14–16) and 8 supporting pins”, S10 says “16/16 provenance rows”, and PE5's m2 CURE adds rows 23–24.
- **Literal recount:** rows 1–13 = the 12 consumed statements + eq (14) as a separate row ✓ (13 rows for “12 + eq (14)” is internally consistent, since row 9 is eq (14) and rows 1–8, 10–13 are 12 statements). r1 adds rows 14–16 → **16 rows at r1**, which is exactly S10's “16/16 provenance rows” ✓. r2 adds rows 17–19 → **19**. r3 adds rows 20–22 → **22**. PE5 appends 23–24 → **24 total**, of which 22 are consumed-status and 2 are DESCRIPTIVE.
- **Every stated figure reconciles against a literal recount. Zero rule-39 source-self-count defects.**
- **Layout-leg re-verification at compile time:** all 22 layout pins were re-read from `fgmn_residual_ideals_1305.0775v3_layout.txt` at their cited line numbers. **21 of 22 land exactly on the cited statement.** Row 5 is a **NEAR-MISS** (§4.6 NM-1): L1089 is Cor 4.4 **item (4)**, which is indeed “the item used” per the row's own parenthetical — so row 5 is CORRECT as written; the near-miss is only in `.35`'s separate `[L1089 region]` citation of item (1), which lives at L1085.
- One presentational note on row 6: the layout interposes a running page header inside L1121–1126 (see `.15`).

**CONDITIONALITY:** the PDF-page column is not machine-checkable from the layout file; only the layout-pin column was re-verified. The two legs are, by design, decorrelated — the compiler can re-run one of them and does.

**RESOLUTION TRACE:** table lines 856–879. Correction site: L1333–1341 appends rows 23–24 (`.77`) — the table body above is byte-frozen and the append says so.

**TEETH:** each row is its own check.

---

### EFF.GENTOW2.51  [record — the supporting pins paragraph]

**CANONICAL STATEMENT:**

**FORM:** bold-headed paragraph

> “Supporting pins also PDF-verified on the same pass: Prop 1.9 (p.6),
> Lemma 2.4 (p.9), Def 3.1 + display (4) (p.12), the §3.2 numerical
> data table (pp.15–16), the N_i/R_{i,α} operator definitions + eq
> (12) (p.17), Def 3.15 (the ε_i(α) constants) + Def 3.16 (p.18),
> Def 3.18 + j₀ formula (p.19), the §6 header (bottom of p.27 —
> layout L1433; the pre-repair pin "L1434" was off by one, PE1 F5).
> [r2] Rows 17–19 were added in the PE2 repair round and verified by
> the SAME two-leg method (fresh visual reads of PDF pp.7, 15, 16,
> 17 against the layout pins), together with three [r2] supporting
> pins: the z_i/ψ_i definition display + y_i = H_{µ_i}(γ_i) (p.17,
> L855–863), Lemma 3.13 (µᵢ(γᵢ) = 0, µᵢ(πᵢ₊₁) = 1/e(µᵢ); p.16,
> L836–840), and §3.2's own Prop-1.15 identification sentence ("Fᵢ
> ... may be identified with the residue class field F_{φᵢ}", p.15).”

**DERIVATION:** `[RECORD]` **Layout-leg re-verification at compile time:** L1433 (§6 header) ✓; L464 (Lemma 2.4) ✓; L608–615 (Def 3.1 + display (4)) ✓; L785–803 (§3.2 data) ✓; L871–875 (N_i, R_{i,α}) ✓; L916–923 (Def 3.16) ✓; L994–1000 (Def 3.18 + j₀) ✓; L855–863 (`yi := Hµi (γi ) := (xi )ei (pi )−hi ∈ ∆i` at L856, `zi ∈ Fi+1 , the image of yi under ∆i −→ ∆i+1` at L861, `ψi ∈ Fi [y], minimal polynomial of zi over Fi` at L862) ✓; L836–840 (Lemma 3.13 items (1)/(3)) ✓; L258–261 (Prop 1.9) ✓.

**CONDITIONALITY:** these are supporting, not consumed — except Lemma 3.13(1), Def 1.8 and Prop 1.9(2), which r3 ELEVATED to consumed status as rows 20–22 (`.52`).

**RESOLUTION TRACE:** lines 881–893.

**TEETH:** the S11 F2 record (`.73`).

---

### EFF.GENTOW2.52  [record — the consumed-statement inventory]

**CANONICAL STATEMENT:**

**FORM:** bold-headed paragraph

> “**Statements consumed** (each quoted verbatim in S3): Lemma 1.11,
> Cor 1.13, Def 5.2, Lemma 5.3, Cor 4.4, Cor 4.7, Cor 4.12 (+ its
> proof's construction), Prop 5.7 + eq (14), Cor 5.6, Thm 5.8 (proof
> display only, used as an argument-schema on our concrete Φ₃, not as
> a statement), Thm 6.3, Cor 6.4. [r1] Added by the S5.1 derivation
> (LEMMA GENTOW2-B′): Cor 3.3, Lemma 3.17, Thm 4.8 — each
> PDF-verified, rows 14–16 of S6.1. [r2] Added by the S5.1 canonical
> identification + LETTER FORMULA (PE2 F1): Prop 1.15, Def 3.12
> (+ §3.3's ℓᵢ, ℓ′ᵢ), eq (9) with the §3.2 data definitions — each
> PDF-verified, rows 17–19 of S6.1. [r3] Added (PE4 F2 + the B″
> derivation): Lemma 3.13(1) — ELEVATED from the [r2] supporting-pin
> paragraph to consumed status, the rider C-m1 having made its exact
> stable value v(π₂(x₀)) = 1/e(µ₁) load-bearing in the
> denominator-clearing bridge; re-verified this round by the two-leg
> method (layout L836–840 + a fresh visual read of PDF p.16: the
> displayed clause µᵢ(πᵢ₊₁) = 1/e(µᵢ) is exactly what C-m1 consumes
> at i = 1) — row 20. Def 1.8 (the augmented valuation is DEFINED by
> the φ-expansion minimum), consumed by S5.2's B″ step (ii) —
> two-leg verified (layout L250–255 + fresh visual read of PDF p.5)
> — row 21. Prop 1.9(2) (Φ₂-free elements have ν = µ₂), already
> cited inline by the S5 proof and reused at S5.2(iii) but absent
> from this list — same F2 species of inventory drift, folded now
> rather than flagged (two-leg verified: layout L258–261 + fresh
> visual read of PDF p.6) — row 22.”

**DERIVATION:** `[RECORD]`

**SUPERSESSION KIND:** `inventory completion` (three times: r1 adds 3, r2 adds 3, r3 adds 3).

**ARITHMETIC AUDIT (rule 22).** Base list: Lemma 1.11, Cor 1.13, Def 5.2, Lemma 5.3, Cor 4.4, Cor 4.7, Cor 4.12, Prop 5.7, Cor 5.6, Thm 5.8, Thm 6.3, Cor 6.4 = **12 statements**, plus eq (14) as a thirteenth item ✓ matches “the 12 consumed statements + eq (14)” at `.03` and “13/13 MATCH” at `.65`. Additions: 3 (r1) + 3 (r2) + 3 (r3) = 9; 13 + 9 = **22** = S6.1's consumed-status row count ✓. **Zero count defects.**

**CONDITIONALITY:** Thm 5.8 is consumed as an **argument-schema, not as a statement** — the note fences this explicitly and it is the correct reading (`.13`). Lemma 3.13(1)'s elevation is what makes C-m1's bridge legitimate.

**RESOLUTION TRACE:** lines 895–918. Correction site: L1333–1347 (rows 23–24 enter at DESCRIPTIVE, i.e. explicitly NOT added to this list).

**TEETH:** the S6.1 rows; PE4 F2's finding that the list had drifted (`.73`) — the drift was found by an outside pass, twice (F2 at PE4, and the same species self-found while “the drawer was open”).

**AUDIT (rule 33 `instrument-audit`):** the note's own phrase “same F2 species of inventory drift, folded now rather than flagged” is a self-audit of its own inventory instrument.

---

### EFF.GENTOW2.53  [record — the hypothesis audit (H-a)–(H-f)]

**CANONICAL STATEMENT:**

**FORM:** bold-headed paragraph, six lettered rows

> “**Hypothesis audit** (why each FGMN hypothesis holds at our
> instance): (H-a) v discrete, K_v complete: v = v_p on ℚ. (H-b) ν
> inductive with a MacLane chain of length 3: the tower construction
> IS such a chain; optimality (deg strictly grows) from stage
> properness e₂f₂ ≥ 2 (T(b)′ setting) — and Cor 6.4 needs only "a
> MacLane chain", not optimality. (H-c) F ∈ P: from GENTOW2-A(a),
> which uses only [Q1],[Q2],[Q4],[Q6] + GENTOW2-B. (H-d) φ key for ν
> with φ|_ν F: F = φ. (H-e) φ ≁_ν φ_r: proved in S4 from ψ₃ ≠ y via
> [Q7]. (H-f) ψ₃(0) ≠ 0, monic irreducible /K₂, e₃f₃ ≥ 2: PROVISOS of
> GENTOW2-A, discharged at every tower stage the repo constructs
> (stage residuals are minimal polynomials of nonzero residue classes;
> a proper stage has e₃f₃ ≥ 2 by definition — an improper "stage"
> (e₃f₃ = 1) is a refinement, not a level, per FGMN Lemma 3.5/Prop 3.7
> collapsing).”

**DERIVATION:** `[RECORD]` A hypothesis-by-hypothesis discharge.

**CONDITIONALITY — one clause is STRUCK.** The (H-b) row's trailing clause “— and Cor 6.4 needs only "a MacLane chain", not optimality.” is **STRUCK** by TOWERRAT-R3-1 (`.86`). Governing reading: the clause is withdrawn; (H-b)'s license is the *preceding* derivation (stage properness ⟹ strict degree growth ⟹ optimal chain), and S4 consumes exactly that optimal chain. **See OPEN-CALL 1: the struck clause was source-accurate.**

(H-a) narrows the base field to ℚ; `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` §NS-12 resolves the corresponding audit rows Q4 A2 / B6 to **COVERS-ALL-O** (§4.5 row RX16).

**RESOLUTION TRACE:** statement lines 920–933; correction site L1438–1449 (R3-1).

**TEETH:** every row is a precondition of the cite; (H-c)/(H-e) are discharged by `.21`/`.22` and re-checked by the battery's PARI leg.

---

### EFF.GENTOW2.54  [fence — direction of fit]

**CANONICAL STATEMENT:**

**FORM:** bold-headed paragraph (reproduced in full at NON-IMPORT N-4; not duplicated here)

The unit's text is the four-sentence block at lines 935–940, quoted verbatim under **N-4** in §2.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** the phrase “the derived unit laws B′(3)–(5)/B″” is **consumption-list site 5 of 5**, the one PE6 found un-named. Governed by the FOLD (`.81`): the true consumption is `B′(3) + B″`. **Zero edits were made to this sentence** — PE6 states so explicitly (“Zero edits to the S6 sentence (byte-frozen)”).

**RESOLUTION TRACE:** lines 935–940; correction sites L1303–1331 (m1 CURE, which did NOT name this site), L1369–1383 (PE6 FOLD, which did).

**TEETH:** PE6's grep census, which pins the five sites at body `L365/L431/L535/L938/L1248` — see §4.6 NM-3 for the compiler's independent locate of these.

---

### EFF.GENTOW2.55  [fence — what the cite does NOT give]

**CANONICAL STATEMENT:**

**FORM:** bold-headed paragraph, three numbered items (reproduced in full at NON-IMPORTs N-1, N-2, N-3; not duplicated here)

The unit's text is lines 942–947, quoted verbatim as N-1/N-2/N-3 in §2.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** item (ii) is the note's own statement that its central hypothesis (`κ₃ > e₂f₂u₂`) is undischarged here.

**RESOLUTION TRACE:** lines 942–947.

**TEETH:** TOOTH T1 (a floor-breaching recipe MUST fail one-sidedness) is the machine coupling of item (ii) to the theorem (`.60`, `.64`).

---

### EFF.GENTOW2.56  [scope record — (α) DISCHARGED]

**CANONICAL STATEMENT:**

**FORM:** bulleted item

> “* **(α) — DISCHARGED here** (THEOREM GENTOW2-A(b)(c)(d) via FGMN
>   Cor 6.4; bridge LEMMA GENTOW2-B). The ascent that forces a
>   Φ₃-root's intermediate data now has its inputs as theorems.”

**DERIVATION:** `[DERIVED]` from `.20`–`.24`.

**CONDITIONALITY:** the whole conditionality stack of `.20` and `.25`, including the `(β)` floor hypothesis and the `ψ₃^{(w)}` reading of hypothesis (ii).

**RESOLUTION TRACE:** lines 954–956.

**TEETH:** the S8 battery; PE4's A-route 27/27.

---

### EFF.GENTOW2.57  [scope record — (β) rides item (1); the in-flight cite]

**CANONICAL STATEMENT:**

**FORM:** bulleted item

> “* **(β) — rides item (1)**, exactly as the r3 box said: the floor
>   κ₃ > e₂f₂u₂ (= λ₃ > 0, GENTOW2-B's hypothesis) at ACTUAL tower
>   leaves needs the composed entry budgets. GENTOW-1 (in-flight this
>   wave, same campaign: GENTOW1_PROOF_2026-08-09.md, status table
>   rows "item (1) PROVED (S2)" + "COR GENTOW-1.1 (the depth-3 floor
>   rider (6)(β)) PROVED (S2.4)", grade 0/2, hostile arc pending)
>   supplies it; this note cites it AS IN-FLIGHT and does not
>   re-derive it.”

**DERIVATION:** `[RECORD]`

**XREF VERIFICATION + NEAR-MISS.** `grep -cF 'COR GENTOW-1.1' GENTOW1_PROOF_2026-08-09.md` = **4** ✓ (clean XREF). But `grep -cF 'item (1) PROVED (S2)'` = **0** — **NEAR-MISS NM-2**: the designation is absent as written; the verified referent is at `GENTOW1_PROOF_2026-08-09.md:36` under the actual string `| (1) budgets + node | LEMMA GENTOW-1 | PROVED (S2) |`, and the companion at `:37` under `| (1) rider: depth-3 floor (6)(beta) | COR GENTOW-1.1 | PROVED (S2.4) |`. The note has compressed two table cells into one quoted phrase. Count of `PROVED (S2)` in that file = 1. Recorded as NEAR-MISS, not an OPEN-CALL: the referent is unambiguous and the status is as described.

**CONDITIONALITY — a STALE grade.** The parenthetical “grade 0/2, hostile arc pending” describes GENTOW-1 as of 2026-08-09. `docs/PROJECT_STATE.md` DATED APPEND #16 (2026-08-10) is titled **“GENTOW1 + GENTOW2 BOTH ACCEPTED”** and its tower board reads “HETOW ✓ · GENTOW1 ✓ · GENTOW2 ✓”. Tagged **`STALE-SELF-DESCRIPTION`** (rule 26) — the sentence is not corrected under the freeze, and a consumer must be told that GENTOW-1 is no longer in flight. This is the only stale *cross-note* status claim in the note, and per rule 10 it was verified against `GENTOW1_PROOF_2026-08-09.md`'s full append chain and PROJECT_STATE, not by re-grepping the pinned sentence.

**RESOLUTION TRACE:** lines 957–964.

**TEETH:** TOOTH T1 couples (α) to the (β) floor at the machine level.

---

### EFF.GENTOW2.58  [fence — depth ≥ 4 not claimed]

**CANONICAL STATEMENT:**

**FORM:** bulleted item (reproduced in full at NON-IMPORT N-8)

The text is lines 965–972, quoted verbatim as N-8 in §2.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** the proof pattern is asserted to be level-uniform PROVIDED the level-r analogues of (B-1)/(B-2) are proved. Since **(B-2) is REFUTED** (`.28`), the depth-≥4 conditional as written is now partly moot — its level-r (B-2) analogue is exactly what `[GENTOW5-W(i)]` supplies conditionally at `i ≥ 3` (T5's `𝒲_{≤i}` chain). Recorded as a note, not a defect: the sentence is a conditional and its antecedent's second conjunct has since been replaced corpus-wide by the B″-shaped law.

**RESOLUTION TRACE:** lines 965–972.

**TEETH:** none of its own (a negative fence).

---

### EFF.GENTOW2.59  [record — the assembly consequence]

**CANONICAL STATEMENT:**

**FORM:** paragraph, explicitly labelled a display and not a new claim

> “Assembly consequence (display, not a new claim): with (α) proved and
> (β) = COR GENTOW-1.1 (in-flight), T(b)″'s remaining content is pure
> T(b)′-mechanism iteration (carrier via GENTOW2-A(a), slot inputs via
> (c)+(d), read via T(b)′(iii) at the level-3 basis), i.e. item (6)
> reduces to the SAME acceptance state as items (1)–(5): no residue
> special to depth ≥ 3 remains open beyond them.”

**DERIVATION:** `[RECORD]` The note self-labels it “display, not a new claim”.

**CONDITIONALITY:** conditional on COR GENTOW-1.1 (now accepted, `.57`) and on T(b)′(iii) at the level-3 basis.

**RESOLUTION TRACE:** lines 974–979.

**TEETH:** none.

---

### EFF.GENTOW2.60  [run-record — the sealed battery run, T2 failed as designed]

**CANONICAL STATEMENT:**

**FORM:** bulleted item under a bold `SEAL STATE` head

> “* **Sealed run** (gentow2_checks_output.txt, runner as sealed at
>   commit c33f10e): **40 scored checks, 0 violations** — every pin
>   table, one-sidedness, on-side residual support, and Bareiss
>   resultant valuation EXACT on the A-route, and every PARI sig +
>   nfeltval intermediate triple EXACT on the B-route, at W1, W2,
>   W3–W5, N1, N2. TOOTH T1 FIRED (the floor-breaching recipe u₃ = 9
>   < 10 is flagged NOT one-sided — pin (3,2) below the chord —
>   machine-coupling (α)'s theorem to the (β) floor hypothesis).
>   **TOOTH T2 FAILED AS DESIGNED** (machine sig [(8,1)], predicted
>   [(4,1),(4,1)]): the design mis-read Lemma 5.3 — R = (y+1)² is a
>   prime POWER (one residual ideal), and FGMN Thm 6.6 splits only
>   across DISTINCT (λ, L) pairs, so non-key does NOT imply reducible;
>   Φ₂² − 64x is irreducible with e = 8 and the tower simply refines
>   further. As-sealed verdict: RED on the tooth criterion, with all
>   40 scored checks green. Disclosed, kept as a record row.”

**DERIVATION:** `[RECORD]` **Compile-time verification against the artifact.** `gentow2_checks_output.txt` (1,350 B) ends: `checks: 40, violations: 0, teeth: {'T1': True, 'T2': False}` / `GENTOW2 battery: RED` — **exact match** to the declared 40/0, T1 fired, T2 failed, verdict RED ✓. The T1 line in the artifact reads `-- TOOTH T1: pins {0: 9, 1: 7, 2: 7, 3: 2, 4: 0} -> one_sided=False (must be False)` — matching the note's “pin (3,2) below the chord” ✓. The T2 line reads `-- TOOTH T2: sig [(8, 1)] (must be [(4,1),(4,1)])` ✓. `git cat-file -t c33f10e` = commit ✓.

**CONDITIONALITY:** the sealed run's verdict is **RED**. It is kept as a record row and is NOT the note's evidence; the GREEN figure comes from the re-run (`.62`).

**RESOLUTION TRACE:** lines 984–998.

**TEETH — disposition `instrument-audit` + `disclosed non-repair` (rules 33, 20):** T2 is a tooth that was designed wrong and is disclosed rather than quietly re-specified. The failure diagnosis is itself a mathematical finding (Thm 6.6 splits only across DISTINCT `(λ, L)` pairs, so “non-key ⟹ reducible” is false) — and that diagnosis is the content of S6.1 row 24 (`.77`), at DESCRIPTIVE status.

---

### EFF.GENTOW2.61  [preregistration + run-record — the corrected tooth T2′]

**CANONICAL STATEMENT:**

**FORM:** bulleted item

> “* **Corrected tooth T2′** (preregistered before ITS first run,
>   commit after the disclosure; run artifact
>   gentow2_checks_output_run2.txt): at the N1 profile K₂ = F₄, the
>   residual y² + y + 1 = (y+ω)(y+ω²) SPLITS, so
>   Φ₂b² − 8xΦ₂b − 128 has a ONE-SIDED full-support polygon yet must
>   factor [(2,2),(2,2)] — and DID: T2′ FIRED. Hypothesis (ii)'s
>   irreducibility-over-K₂ is machine-load-bearing; the polygon side
>   alone certifies nothing.”

**DERIVATION:** `[RECORD]` **Artifact check:** `gentow2_checks_output_run2.txt` contains `-- TOOTH T2p: sig [(2, 2), (2, 2)] (must be [(2,2),(2,2)])` ✓ and the disclosure row `-- RECORD T2 (disclosed failed design, not scored): sig [(8, 1)] (the sealed prediction [(4,1),(4,1)] was a Lemma-5.3 mis-read; (y+1)^2 is a prime power)` ✓.

**ARITHMETIC AUDIT (rule 22).** Over `F₄ = {0,1,ω,ω²}`: `y²+y+1` at `y = ω` gives `ω²+ω+1 = 0` ✓ and at `y = ω²` gives `ω⁴+ω²+1 = ω+ω²+1 = 0` ✓ — SPLITS into `(y+ω)(y+ω²)` ✓ (in characteristic 2, `y+ω = y−ω`).

**CONDITIONALITY:** T2′ tests one profile (N1, `K₂ = F₄`).

**RESOLUTION TRACE:** lines 999–1006.

**TEETH:** this IS a tooth. Emitted as `preregistration` + `run-record` in ONE unit because the source writes both in one bullet; the preregistration half is “preregistered before ITS first run, commit after the disclosure”, the run-record half is “and DID: T2′ FIRED”. Rule 19's two-unit split is waived here because the source does not separate them and the sealing sequence is stated inline.

**AUDIT (rule 31 `hostile-pass certification`):** T2′ certifies something the note needs: hypothesis (ii)'s irreducibility is load-bearing, not decorative. A one-sided full-support polygon with a split residual does NOT give a prime.

---

### EFF.GENTOW2.62  [run-record — the re-run verdict]

**CANONICAL STATEMENT:**

**FORM:** bulleted item

> “* **Re-run verdict: GREEN — 41 checks, 0 violations, teeth T1 + T2′
>   both fired** (T2 recorded, not scored).”

**DERIVATION:** `[RECORD]` **Artifact check:** run2 ends `checks: 41, violations: 0, teeth: {'T1': True, 'T2p': True}` / `GENTOW2 battery: GREEN` ✓ — exact.

**ARITHMETIC AUDIT (rule 22).** 40 scored (sealed) + 1 (T2′ replacing the unscored T2) = 41 ✓ — the delta is exactly one check, consistent with T2 moving to “recorded, not scored” and T2′ entering as scored.

**CONDITIONALITY:** the GREEN figure is the note's headline battery evidence and it is the one the STATUS header quotes (`.01`).

**RESOLUTION TRACE:** lines 1007–1008.

**TEETH:** this is the verdict row itself.

---

### EFF.GENTOW2.63  [instance record — new-witness yields]

**CANONICAL STATEMENT:**

**FORM:** bulleted item

> “* New-witness yields: N2 is the FIRST machine witness of the
>   f₃ ≥ 2 K₂-digit branch (the gap PE3 remark R1 disclosed as
>   machine-unwitnessed anywhere); N1 is the first depth-3 contact at
>   an f₂ = 2 tower (K₂ = F₄), residual ψ₂² = T⁴ + T² + 1 read off
>   the machine side exactly as Cor 6.4 predicts.”

**DERIVATION:** `[RECORD]`

**ARITHMETIC AUDIT (rule 22).** `ψ₂ = T²+T+1` at N1 (runner docstring: `Phi2b = Phi'^2-2x*Phi'-8 (u2=3, psi2=T^2+T+1)`), so `ψ₂² = (T²+T+1)² = T⁴+T²+1` in characteristic 2 ✓ EXACT. The runner's own `P-N1` line confirms the support: `on-side J={0,2,4} = supp(psi2^2)=y^4+y^2+1 (e2=1)` ✓, and the run artifact's N1 A-route line reads `pins/side/support/resultants OK ({0: 12, 1: 11, 2: 6, 3: 4, 4: 0}, [0, 2, 4], (4, 12, 26))` — on-side set `[0,2,4]` matching `supp(T⁴+T²+1)` ✓.

**CONDITIONALITY:** N2's status as “the FIRST machine witness ANYWHERE” of the `f₃ ≥ 2` branch is a claim about the corpus at composition time.

**RESOLUTION TRACE:** lines 1009–1013.

**TEETH:** the N1 and N2 rows of the battery.

---

### EFF.GENTOW2.64  [instrument-record — the runner, the witnesses, the predictions, the teeth]

**CANONICAL STATEMENT:**

**FORM:** paragraph

> “Runner:
> verification/openmath/gentow2_checks.py, preregistered predictions in
> its module docstring (P-W1/P-W2/P-W3/4/5/P-N1/P-N2 + TOOTH-T1/T2),
> written BEFORE the first full run. Witness inventory: the 5 committed
> ones (W1 = the r3 box witness Φ₂² − 16Φ′; W2 = the PE3-F1/FR3
> uncancelled-carry key Φ₂² − 16xΦ′; W3–W5 = the three SUPP-C n = 16
> leaves) + 2 NEW depth-3 witnesses at other (e_i, f_i) profiles
> (N1: the f₂ = 2 tower (2,1,1,2,2,1), Φ₃ = (Φ′²−2xΦ′−8)² − 64x;
> N2: the f₃ = 2 branch (2,1,2,1,1,2), Φ₃ = Φ₂² − 2xΦ′Φ₂ − 32x — the
> first machine witness ANYWHERE of the K₂-digit f₃ ≥ 2 clause, the
> gap PE3 remark R1 disclosed). Oracle A = exact integer pins/hull/
> residual-support/Bareiss-resultants; oracle B = PARI/gp
> (factorpadic → per-factor idealprimedec + nfeltval intermediate
> triples). Teeth: T1 = a floor-breaching recipe (u₃ = 9 < 10) whose
> Φ′-development must be flagged NOT one-sided (machine-couples (α) to
> the (β) floor); T2 = a reducible-residual recipe (R = (y+1)²) that
> must factor [(4,1),(4,1)] — the polygon side alone must NOT certify.”

**DERIVATION:** `[RECORD]` **Artifact check:** `verification/openmath/gentow2_checks.py` exists (14,629 B); its module docstring carries the preregistered predictions `P-W1`, `P-W2`, `P-W3/4/5`, `P-N1`, `P-N2`, `TOOTH-T1`, `TOOTH-T2` verbatim, with the witness definitions matching this unit's inventory exactly (`W1 (committed, r3 box): Phi3a = Phi2^2 - 16*Phi', Phi2=(x^2-2)^2-4x, profile (2,1,2,1,2,1), u2=5, u3=21.`) ✓.

**ARITHMETIC AUDIT (rule 22) — the T1 floor breach, recomputed.** The floor is `κ₃ > e₂f₂u₂`. At the W1 profile `e₂ = 2, f₂ = 1, u₂ = 5`, so the floor in `u₃`-units is `e₃·e₂f₂u₂ = ...`; the runner's T1 witness has `u₃ = 9 < 10 = e₂f₂u₂` where `e₂f₂u₂ = 2·1·5 = 10` ✓ — the breach is by exactly one unit, and the run flags `one_sided=False` ✓. **The tooth is a genuine near-boundary probe, not a caricature.**

**CONDITIONALITY:** the predictions were sealed before the first full run (a preregistration claim); the T2 prediction was WRONG and is disclosed (`.60`).

**RESOLUTION TRACE:** lines 1015–1031.

**TEETH:** this unit IS the teeth inventory; see §6.

**PIN (rule 23):** `gentow2_checks.py` PINNED (exists, sealed at commit `c33f10e` ✓); both output artifacts PINNED.

---

### EFF.GENTOW2.65  [changes-record — S9, the PE1 repair record]

**CANONICAL STATEMENT:**

**FORM:** section with a bold-headed preamble and six lettered findings

> “Verifier: GENTOW2_passPE1_report.md (commit 61daa69; target blob at
> 531c212). Charge honored: repairs RE-DERIVED (the PDF pages were
> re-read visually; the B′ bridge and the F6 row were recomputed at
> the witness), sealed machine artifacts byte-untouched this round
> (gentow2_checks.py, both run outputs, gentow2_pe1_fresh.py + its
> output — zero diffs under verification/openmath/ in the r1 commits).
>
> * **F1 (GAP, provenance over-claim) → CURED at the strongest
>   available grade.** … 13/13 MATCH
>   (table S6.1), plus 3 [r1]-added cites (rows 14–16) and 8
>   supporting pins. … Commit 1e091d1.
> * **F2 (GAP, B-2 provenance pointer) → CURED: partially derived +
>   honestly re-attributed.** New LEMMA GENTOW2-B′ (S5.1) derives
>   from accepted corpus (B-1 + T(b)′(iii) + Cor 4.7/Lemma 3.17/
>   Thm 4.8): repo digit and FGMN ε₂-coordinate agree up to an
>   x₀-free, g-free unit family u(β) = R₃,β(n̂₂(β̂)). … Commit dd44d20.
> * **F3 (GAP, false fallback clause) → CURED.** … Commit dd44d20.
> * **F4 (MINOR) → CURED**: Φ₂ = φ₃ ∈ KP(ν) via Lemma 5.3(1) added
>   where Prop 5.7 fires (S4). This commit.
> * **F5 (MINOR) → CURED**: §6-header pin corrected L1434 → L1433
>   (PDF p.27). Commit 1e091d1.
> * **F6 (MINOR) → CURED**: the S2 (e₃, f₃) row now defines its
>   target — FGMN (e₃, f₃) with m₄ = e₃f₃m₃ (eq (9)); the undefined
>   "e₄-level data" label retired; witness denominator recomputed
>   (ν(Φ₂) = 21/8 → e₃ = 2). This commit.
>
> Grade: attempt 0/2 unchanged after r1. Next: PE2 (second hostile
> pass) on the repaired note.”

*(Ellipses mark the three GAP findings' full internal text, reproduced at `.48`, `.29`, `.31` respectively — the compiler does not duplicate a body passage that is already a unit.)*

**DERIVATION:** `[RECORD]`

**PIN VERIFICATION (rule 23).** `GENTOW2_passPE1_report.md` exists ✓. `git cat-file -t` on `61daa69`, `1e091d1`, `dd44d20` — all **commit** ✓. **`531c212` is a MISLABEL:** the note calls it a “target blob”, but `git cat-file -t 531c212` returns **commit**, and `git rev-parse --disambiguate=531c212` returns exactly one object, `531c212f6c8c7faf91102a14148283592b985f13`, a commit. Recorded as MINOR pin-vocabulary defect, §9 OPEN-CALL 4 — the object exists and is unambiguous; only its type-name is wrong.

**ARITHMETIC AUDIT (rule 22).** F1's “13/13 MATCH … plus 3 [r1]-added cites (rows 14–16) and 8 supporting pins”: 13 + 3 = 16 rows at r1 ✓ (matching S10's “16/16 provenance rows”); the 8 supporting pins are enumerable from `.51`'s first sentence — Prop 1.9, Lemma 2.4, Def 3.1 + display (4), the §3.2 data table, the `N_i`/`R_{i,α}` defs + eq (12), Def 3.15 + Def 3.16, Def 3.18 + j₀, the §6 header = **8** ✓ **exact**. F6's re-derivation `ν(Φ₂) = 21/8 → e₃ = 2` is verified at `.05`'s arithmetic audit ✓.

**CONDITIONALITY:** the grade line “attempt 0/2 unchanged after r1” is superseded (`.80`).

**RESOLUTION TRACE:** lines 1033–1080.

**SERIES:** ARC-SERIES member (see `.02`), between the composition and S10.

**TEETH:** each finding names its own cure site.

---

### EFF.GENTOW2.66  [changes-record — S10, the PE2 repair record]

**CANONICAL STATEMENT:**

**FORM:** section with a bold-headed preamble and four lettered findings

> “Verifier: GENTOW2_passPE2_report.md (commit aff457c). Verdict
> there: NOT CLEAN — 0 CRITICAL, 2 GAP (both inside the [r1]-new
> LEMMA GENTOW2-B′), 2 MINOR; 16/16 provenance rows, the theorem
> chain, the machine legs, and the f₃ = 3 fresh route HELD. Charge
> honored this round: the canonical formula was RE-DERIVED from the
> PDF (not copied from the report), the three F1 sources were
> PDF-verified by the two-leg method and added as S6.1 rows 17–19,
> and the F2 repair was re-derived at the record's own N1 grade-7
> frame. Sealed machine artifacts byte-untouched (zero diffs under
> verification/openmath/ for the sealed files in the r2 commits);
> machine support this round is ADDITIVE only.
>
> * **F1 (GAP, the "(η₂ ↔ z₂)" identification parenthetical) →
>   CURED.** … [full text at `.33`, `.37`, `.39`]
> * **F2 (GAP, B-1 applied outside its deg < D₂ scope in B′'s
>   h-step) → CURED, corner CLOSED.** … [full text at `.35`, `.36`]
> * **F3 (MINOR, u-direction slip) → CURED**: the fallback clause's
>   hypothesis now reads in B′(3)'s direction (ε-normalized =
>   u·repo). This commit.
> * **F4 (MINOR, B′(4) scope conflation) → CURED**: B′(4) restated
>   per-grade with the consumed scope (u(β_t) = 1 at used grades)
>   separated from B-2's stated scope. This commit.
>
> Grade: attempt 0/2 unchanged (the counter starts only on a CLEAN
> pass; PE2 was NOT CLEAN). Next: PE3 (hostile pass on the
> r2-repaired note; the letter-live geography now has a committed
> machine foothold at LP1, and HETOW's frame-Y/R family remains the
> candidate for a deeper letter-live route).”

**DERIVATION:** `[RECORD]`

**PIN VERIFICATION:** `GENTOW2_passPE2_report.md` exists ✓; `git cat-file -t aff457c` = commit ✓.

**ARITHMETIC AUDIT (rule 22).** “16/16 provenance rows” reconciles with the r1 row count 13 + 3 = 16 ✓ (`.65`). F3's direction claim is verified against `.34`'s clause (3) — `R_{3,β}(g) = u(β)·digit(g)`, i.e. `ε-normalized = u·repo` ✓ consistent.

**CONDITIONALITY:** grade line superseded (`.80`). The forward-looking sentence “HETOW's frame-Y/R family remains the candidate for a deeper letter-live route” is a plan, not a claim; PE4's LD frames on the LP1 tower are what actually ran.

**RESOLUTION TRACE:** lines 1082–1132.

**SERIES:** ARC-SERIES member.

**TEETH:** the LP1 probe (`.67`).

---

### EFF.GENTOW2.67  [run-record — the r2 letter-live probe LP1]

**CANONICAL STATEMENT:**

**FORM:** bulleted item

> “* **[r2] MACHINE LEG (additive; the PE2 report's disclosed PE3
>   fresh-route need): LETTER-LIVE PROBE GREEN — 21 checks, 0
>   violations, first run under seal.** Runner
>   verification/openmath/gentow2_r2_letter_probe.py (sealed at
>   commit d56e439 with preregistered predictions; no smoke run),
>   output gentow2_r2_letter_probe_output.txt. Frame LP1 = the
>   record's first f₁ = 2 contact (base slope 1/2, ψ₁ = y² + y + 1,
>   Φ′_LP1 = x⁴ + 2x² + 4, Φ₂_LP1 = Φ′² − 8x³, (e, f) = (4, 2)
>   confirmed): the LETTER FORMULA fired LIVE — z₁ ∈ F₄∖F₂
>   (z₁² + z₁ + 1 = 0), η₂ = z₁, z₂ = 1 = η₂·z₁^{−4} at
>   ⌊ℓ₁u₂/e₁⌋ = ⌊9/2⌋ = 4 — and the TOOTH fired: η₂ ≠ z₂, i.e. the
>   pre-repair "η₂ ↔ z₂" parenthetical is machine-refuted at LP1
>   while the canonical formula holds exactly. Dual routes: exact
>   integer v₂-resultants (4, 18, 8, 26, 32) + the polynomial
>   identity x⁶ − 8 = (x² − 2)Φ′_LP1 (an exact-algebra proof of
>   z₂ = 1) on the A-side, PARI factorpadic/idealprimedec/nfeltval/
>   nfmodpr on the B-side.”

**DERIVATION:** `[RECORD]` **Artifacts:** `gentow2_r2_letter_probe.py` (6,557 B) ✓ and `gentow2_r2_letter_probe_output.txt` (796 B) ✓ both exist; `git cat-file -t d56e439` = commit ✓.

**ARITHMETIC AUDIT (rule 22).** `x⁶ − 8 = (x² − 2)(x⁴ + 2x² + 4)` — expand: `x⁶ + 2x⁴ + 4x² − 2x⁴ − 4x² − 8 = x⁶ − 8` ✓ **EXACT**. `⌊ℓ₁u₂/e₁⌋ = ⌊9/2⌋ = 4` ✓ (`ℓ₁ = 1`, `u₂ = 9`, `e₁ = 2` — matching `.45`'s LP1 data). `z₂ = η₂z₁^{−4} = z₁·z₁^{−4} = z₁^{−3} = 1` since `z₁³ = 1` in `F₄^×` ✓ **EXACT**.

**COMPILER SELF-CORRECTION (recorded per rule 39).** A first pass of this compilation transcribed the penultimate clause as “on the B-side” and booked it as a source wording defect. The mechanical fidelity audit (§9) caught it: the note reads **“on the A-side”** at body L1148, which is CORRECT against the note's own oracle convention (`.64`: “Oracle A = exact integer …; oracle B = PARI/gp”). The quotation above is the corrected one and **no source defect exists here**. Recorded rather than deleted, because a compiler that silently repairs its own misquotation leaves no evidence that the fidelity audit works.

**CONDITIONALITY:** one frame (LP1). The probe tests the LETTER FORMULA, **not** B-2 — the note says so at `.30`.

**RESOLUTION TRACE:** lines 1133–1149.

**TEETH:** this is a tooth firing — `η₂ ≠ z₂` machine-refutes the pre-repair parenthetical. Disposition: **executable regression, first-run-under-seal, GREEN 21/0.**

---

### EFF.GENTOW2.68  [acceptance-box — the post-PE3 dated-corrections header]

**CANONICAL STATEMENT:**

**FORM:** italic-headed provenance block

> “*Source: `GENTOW2_passPE3_report.md` @ 92ac16b — verdict CLEAN
> (0 CRITICAL, 0 GAP, 2 MINOR); the r2 surfaces (LETTER FORMULA,
> h-step corner, LP1 probe) held under independent re-derivation, and
> the PE3 fresh route (first z₂ ≠ 1 letter-live contacts, p = 3/F₉)
> came back 50/0 GREEN first-run-under-seal. Per the arc the item-(6)
> acceptance counter moved 0/2 → **1/2 and HOLDS AT 1/2**: the two
> cures below are dated appends to MINOR findings, not a scoring
> round; one further clean pass on a fresh surface is required for
> acceptance. The body above is BYTE-FROZEN — each correction below
> supersedes its referenced text of record. Sealed machine artifacts
> untouched by this append.*”

**DERIVATION:** `[RECORD]` **This unit carries the note's effective-text rule** (§1). `GENTOW2_passPE3_report.md` exists ✓; `git cat-file -t 92ac16b` = commit ✓; `gentow2_pe3_fresh.py` (9,092 B) + `gentow2_pe3_fresh_output.txt` (1,756 B) exist ✓.

**CONDITIONALITY:** the counter value 1/2 here is superseded twice — reset to 0/2 at PE4 (`.71`), then closed at 2/2 (`.80`).

**RESOLUTION TRACE:** lines 1157–1169.

**SERIES:** ARC-SERIES member (between S10 and S11).

**TEETH:** the PE3 fresh route, 50/0 GREEN first-run-under-seal, at the first `z₂ ≠ 1` letter-live geography (`p = 3/F₉`) — a genuinely new frame family, decorrelated from LP1's `z₂ = 1`.

---

### EFF.GENTOW2.69  [lemma — C-m1, the denominator-clearing bridge]

**CANONICAL STATEMENT:**

**FORM:** display (bold-headed dated correction with an inline derivation)

> “**C-m1 (cures PE3 [m1] — the implicit evaluation-extension line in
> the S5.1 letter-formula derivation).** The derivation's first
> display ("Under Prop 1.15(1) (p.7) the class evaluates: z₂ =
> res(γ₂(x₀)) = res(Φ′(x₀)^{e₂}/π₂(x₀)^{u₂})") applies Prop 1.15(1)
> — stated for POLYNOMIAL classes g + P₀⁺ ↦ g(θ) + m_φ — to the
> rational class of γ₂ = Φ′^{e₂}π₂^{−u₂}. The denominator-clearing
> bridge, now displayed: pick a polynomial representative b of the
> letter class, H_{µ₂}(b) = y₂, i.e. (clearing the monomial
> denominator) µ₂(b·π₂^{u₂} − Φ′^{e₂}) > µ₂(Φ′^{e₂}) = e₂(w₂ + λ₂).
> Evaluating at the Φ₂-root x₀ with v ≥ µ₂ on polynomials gives
> v(b(x₀)π₂(x₀)^{u₂} − Φ′(x₀)^{e₂}) > e₂(w₂ + λ₂); the denominator's
> value is EXACT and stable, v(π₂(x₀)) = 1/e(µ₁) (Lemma 3.13(1), the
> [r2] supporting pin, PDF L836–840; dv₁(π₂) = 1), so v(π₂(x₀)^{u₂})
> = u₂/e(µ₁) = e(µ₂)(w₂ + λ₂)/e(µ₁) = e₂(w₂ + λ₂) exactly (e(µ₂) =
> e₂·e(µ₁), §3.2 data). Dividing: v(b(x₀) − γ₂(x₀)) > e₂(w₂ + λ₂) −
> e₂(w₂ + λ₂) = 0, hence res(b(x₀)) = res(γ₂(x₀)), and Prop 1.15(1)
> applied to the polynomial b yields the display. The γ₁^k residue
> step admits the same line verbatim with denominator a monomial in
> π₂ and π at exact values (v(π) = 1, π a base uniformizer — no
> stability input needed there). PE3 checked this line goes through
> ([m1]); the formula's conclusion is additionally machine-true at
> LP1 and at both LV frames. The two other identification use-sites
> ((R-repo); the R_{3,0}(ẑ_d) = d step) apply Prop 1.15/Thm 4.8 to
> polynomial classes and need no bridge.”

**DERIVATION:** `[DERIVED]` **Compile-time verification of Lemma 3.13(1):** L836–840 read `Lemma 3.13. For every index 0 ≤ i ≤ r, we have / (1) µi (πi ) = 1/e(µi−1 ), µi (πi+1 ) = 1/e(µi ). / (2) µi−1 (Φi ) = 0, µi (Φi ) = λi . / (3) µi (γi ) = 0. / Note that πi+1 ∈ K(x)∗ is a uniformizer of µi .` ✓ — at `i = 1`, item (1)'s second clause gives `µ₁(π₂) = 1/e(µ₁)` exactly what C-m1 consumes ✓.

**ARITHMETIC AUDIT (rule 22).** `v(π₂(x₀)^{u₂}) = u₂/e(µ₁)`; with `u₂ = e(µ₂)(w₂+λ₂)` and `e(µ₂) = e₂e(µ₁)`: `u₂/e(µ₁) = e₂e(µ₁)(w₂+λ₂)/e(µ₁) = e₂(w₂+λ₂)` ✓ **EXACT**. `dv₁(π₂) = ℓ₁h₁ + ℓ′₁e₁ = 1` by §3.3's defining equation ✓.

**SUPERSESSION KIND:** `inventory completion` — a missing justification step is supplied; the display it justifies is unchanged.

**CONDITIONALITY:** requires Lemma 3.13(1)'s **exact stable** value (not merely a bound) — which is why r3 ELEVATED it to consumed status (`.52`, row 20). The γ₁ leg needs no stability input.

**RESOLUTION TRACE:** statement lines 1171–1194; target span lines 643–644 (S5.1's first display).

**TARGETS (rule 24):** `.38` (the LETTER FORMULA derivation's first display) and `.42` (the γ-calculus's residue step, which cites C-m1 by name).

**TEETH:** PE3's own check ([m1]); machine-true at LP1 and both LV frames.

---

### EFF.GENTOW2.70  [changes-record — C-m2, the arc-bracket replacement]

**CANONICAL STATEMENT:**

**FORM:** bold-headed dated correction with a blockquoted replacement display

> “**C-m2 (cures PE3 [m2] — the STATUS header's arc bracket, stale at
> r2).** The header's closing bracket ("[r1 …; record in S9 … Grade
> stays 0/2; PE2 next.]") is SUPERSEDED by the arc through r2/PE3:
>
> > [r1 2026-08-09, post-PE1 repair round: F1 PDF-provenance leg
> > CLOSED, F2 B-2 partially derived + honestly re-attributed (LEMMA
> > GENTOW2-B′, S5.1), F3 fallback clause corrected, F4/F5/F6 minors
> > cured; record in S9. Grade stays 0/2.]
> > [r2 2026-08-09, post-PE2 repair round: F1 canonical
> > identification CURED — Prop 1.15 evaluation isomorphism + S5.1
> > LETTER FORMULA z₂ = η₂·z₁^{−⌊ℓ₁u₂/e₁⌋} (S6.1 rows 17–19); F2
> > h-step CURED with the e₃ = 1 corner CLOSED; F3/F4 minors cured;
> > LETTER-LIVE PROBE LP1 GREEN 21/0 (first f₁ = 2 contact; TOOTH
> > η₂ ≠ z₂ machine-refutes the pre-repair parenthetical); record in
> > S10. Grade stays 0/2.]
> > [PE3 2026-08-09: CLEAN — 0C/0G/2m (report @ 92ac16b); fresh route
> > 50/0 GREEN, first z₂ ≠ 1 letter-live contacts (p = 3/F₉, teeth on
> > both frames, direction opposite to LP1); acceptance counter
> > 0/2 → 1/2, HOLDS AT 1/2; the 2 MINORs cured in this dated
> > section. Next: acceptance attempt (second clean pass on a fresh
> > surface).]”

**DERIVATION:** `[RECORD]`

**SUPERSESSION KIND:** **`replacement`** — one bracket out, three brackets in, replacement display carried verbatim above.

**TARGETS (rule 24):** `.02` (the header's r1 bracket, body lines 9–14).

**CONDITIONALITY:** the third bracket's counter (1/2) is itself later superseded — reset at PE4 (`.71`), closed at PE6 (`.80`). **CHAIN:** `.02` → **`.70`** → `.71`'s reset → `.80`'s close. **TERMINAL: `.80`** for grade/counter consumers; **`.70`** for r1/r2/PE3 arc-history consumers (two TERMINALs by consumer class, rule 30).

**RESOLUTION TRACE:** lines 1196–1216.

**SERIES:** ARC-SERIES member 2.

**TEETH:** none of its own.

---

### EFF.GENTOW2.71  [changes-record — S11, the PE4 repair record and the counter reset]

**CANONICAL STATEMENT:**

**FORM:** italic-headed provenance block

> “*Source: `GENTOW2_passPE4_report.md` @ 2f95be6 — verdict NOT CLEAN
> (0 CRITICAL, 1 GAP, 1 MINOR). The acceptance attempt's fresh route
> (the first letters × depth contact anywhere: depth-3 recipe frames
> LD1/LD2/LD3 on the letter-live LP1 tower, f₁ = 2, z₁ ∈ F₄∖F₂)
> machine-refuted B-2 at letter-live grades — the tooth bit exactly
> where the [r2] scope disclosure said the record was blind. THEOREM
> GENTOW2-A took the same contact 100% green (27/27 A-route incl.
> the twist certificates; PE4 §E). **ACCEPTANCE COUNTER: 1/2 → 0/2 —
> the consecutive-clean streak breaks at the PE4 pass; nothing is
> banked; acceptance requires two consecutive clean passes from
> here.** Sealed machine artifacts BYTE-UNTOUCHED this round; the
> PE4 fresh/decode artifacts are cited at their committed pins, not
> re-run. Repairs RE-DERIVED (the γ-calculus, the LD cocycle values,
> and the B″ proof were recomputed fresh this round, then checked
> against the decode pins), not transcribed.*”

**DERIVATION:** `[RECORD]` `GENTOW2_passPE4_report.md` exists ✓; `git cat-file -t 2f95be6` = commit ✓; `gentow2_pe4_fresh.py` (16,335 B) + `gentow2_pe4_fresh_output.txt` (1,812 B) + `gentow2_pe4_decode.py` + its output all exist ✓.

**CONDITIONALITY:** counter superseded (`.75`, `.80`).

**RESOLUTION TRACE:** lines 1218–1234.

**SERIES:** ARC-SERIES member 3.

**TEETH — the campaign's cleanest simultaneous break-and-certify:** one contact refuted B-2 (`.28`) and re-derived GENTOW2-A clean at 27/27 (`.24`). Disposition: `in-house hostile pass` finding **and** `hostile-pass certification` (rules 27, 31), on the same run.

---

### EFF.GENTOW2.72  [changes-record — S11 F1, the flip-and-derive cure]

**CANONICAL STATEMENT:**

**FORM:** bulleted item, four roman sub-items

> “* **F1 (GAP — B-2 machine-refuted at letter-live grades; LEMMA
>   GENTOW2-B's conclusion false as stated there) → CURED BY
>   FLIP-AND-DERIVE, this round's four commits.** (i) Honesty box:
>   the (B-2) entry flipped from the ON-THE-NOSE assertion to
>   REFUTED + the MEASURED COCYCLE FORM u(β_t) = ϑ(t)·w^{f₃−t};
>   the 13-witness letter-dead record kept as correctly-disclosed
>   history (accurate as dated — PE4 §S; re-read through B″ it
>   supports ϑ = 1 at its own tested slots and was structurally w-
>   and z₁-blind). (ii) LEMMA GENTOW2-B RESTATED (S5): conclusion =
>   the (B-law) transformation law (B′(5)) + the MULTIPLICATIVE-
>   CONVENTION prescription c_t = ϑ(t)^{−1}a_t realizing R_ν(Φ₃) =
>   ψ₃^{(w)} = w^{f₃}ψ₃(y/w), an admissible GENTOW2-A(ii) residual;
>   the proof's false step now consumes B′(3)+(4) + B″, all DERIVED.
>   (iii) The u ↔ ϑ identity the report asked adjudicated: PROVED as
>   LEMMA GENTOW2-B″ (S5.2) — u's entire per-grade variation is the
>   repo-internal n̂₂-cocycle ϑ (letter-valued via the γ-calculus);
>   the honest cross-frame residue collapses to the ONE
>   slot-independent unit w = R_{3,κ̄}(n̂₂(u₃)), consumer-invisible
>   (grade-covariant substitution). Verified at the PE4 numbers:
>   ϑ(0) = z₂^{−1}z₁^{−5} = z₁ at LP1, matching the decode COC pin
>   res(n̂₂(19)²/n̂₂(38)) = z₁² = ϑ(0)^{−1} and the realized
>   residuals MP1/MP2 (LD1 y²+z₁y+z₁, LD2 y²+z₁y+1); LD3 has the
>   single trivial slot (f₃ = 1). The S5.1 residue paragraph
>   re-scoped: "GENTOW5-A1 cannot supply u(β)" survives only for w;
>   whether ϑ equals GENTOW5-A1's ϑ_t is left to that in-flight arc,
>   unconsumed here. (iv) Propagation: S1 bridge sentence, S5
>   section header, S4 in-particular clause + consumption note (now
>   carrying the PE4 GENTOW2-A-untouched citation), S6
>   direction-of-fit. No new runner: the sealed decode probe already
>   machine-checks the ϑ-prescription at the PE4 frames (MULT/COC/MP
>   pins), and B″'s w-leg is machine-invisible by construction.”

**DERIVATION:** `[RECORD]` The cure's targets are `.28` (i), `.25` (ii), `.43`/`.46` (iii), and (iv)'s four propagation sites `.04`, the S5 heading, `.20`/`.24`, `.54`.

**CONDITIONALITY — a governed inconsistency.** Sub-item (ii) says the corrected step “consumes B′(3)+(4) + B″”. This is **consumption-list site 3 of 5**; the PE6 FOLD (`.81`) governs it to `B′(3) + B″`. The quoted text is byte-frozen.

**TARGETS (rule 24):** `.28`, `.25`, `.43`, `.46`, `.04`, `.20`, `.24`, `.54`.

**RESOLUTION TRACE:** lines 1236–1266; correction sites L1303–1331, L1369–1383.

**TEETH:** the decode MULT/COC/MP pins; the fourth sentence of (iv) is a **disclosed non-repair** (rule 20) — no new runner was written, on the stated ground that the sealed decode probe already covers the prescription and `w` is machine-invisible. PE6 later measured `w` anyway (`.82`), which retro-narrows that ground without falsifying it.

---

### EFF.GENTOW2.73  [changes-record — S11 F2, the consumed-inventory fold]

**CANONICAL STATEMENT:**

**FORM:** bulleted item

> “* **F2 (MINOR — rider C-m1 elevates Lemma 3.13(1); S6 consumed
>   list omitted it) → CURED.** Folded into the consumed list, S6.1
>   row 20, re-verified by the two-leg method this round (layout
>   L836–840 + fresh visual read of PDF p.16). Same-species
>   inventory adds while the drawer was open: Def 1.8 (B″'s
>   expansion-minimum cite, row 21, PDF p.5 fresh visual read) and
>   Prop 1.9(2) (long cited inline by the S5 proof, row 22, PDF p.6
>   fresh visual read).”

**DERIVATION:** `[RECORD]`

**SUPERSESSION KIND:** `inventory completion` (three rows).

**CONDITIONALITY:** none.

**RESOLUTION TRACE:** lines 1267–1274; target `.52`.

**TEETH:** rows 20–22 of S6.1, all three layout-legs re-verified at compile time (`.50`).

**AUDIT (rule 33 `instrument-audit`):** the note's own phrase “Same-species inventory adds while the drawer was open” records a self-found defect of the same class as the reported one — the instrument (the consumed-list inventory) is audited, not merely patched.

---

### EFF.GENTOW2.74  [fence — the r3 not-claim list]

**CANONICAL STATEMENT:**

**FORM:** bulleted item, four clauses

> “* **What this round does NOT claim:** no letter-dead universal for
>   ϑ (its letter monomial is computed per grade pair by the
>   γ-calculus; the LD frames measured z₁, the 13-witness record's
>   green B-routes bound it to 1 at their own tested slots only);
>   no computation of w (a level-3 letter-formula-style derivation,
>   open); no depth ≥ 4 extension; the (β)-floor still rides item
>   (1) via COR GENTOW-1.1 (in-flight).”

**DERIVATION:** `[RECORD]` NON-IMPORT N-10.

**CONDITIONALITY:**
- clause 2 (“no computation of w”) carries a dated bracket at `.82`: **`STALE-SELF-DESCRIPTION`** — `w` is now MEASURED at 4 frames / 6 primes; the closed-form *derivation* stays open, so the clause is half-stale and the bracket says exactly which half;
- clause 4's “(in-flight)” is stale on the same terms as `.57` — GENTOW-1 is ACCEPTED (PROJECT_STATE append #16).

**RESOLUTION TRACE:** lines 1275–1281; correction sites L1408–1411 (the dated bracket on body L1279–1280).

**TEETH:** none (a negative fence).

---

### EFF.GENTOW2.75  [acceptance-box — the post-PE5 outcome]

**CANONICAL STATEMENT:**

**FORM:** bold-headed paragraph

> “**PE5 outcome (recorded here; S11's grade line above predates PE5
> and stands as dated).** PE5 came back CLEAN (0C/0G/2m; report
> `GENTOW2_passPE5_report.md` @ 75923bc): the acceptance counter
> moved **0/2 -> 1/2**. LEMMA GENTOW2-B'' survived independent
> re-derivation AND its first gamma2-live machine contact (fresh
> route GREEN 91/0 first-run-under-seal, seal a4b4495, output
> committed as-is at 0e816e8: tower GB with z2 = eta2 in F4\F2,
> direct cocycle measurement theta(0) = z2^2, opposite-direction
> teeth GA1/GA2, top-slot pin GA4, first e3 = 2 x cocycle-live frame
> GA3). The two MINORs are cured below by dated append; the body
> above is byte-frozen (zero deletions).”

**DERIVATION:** `[RECORD]` **Pins:** `GENTOW2_passPE5_report.md` exists ✓; `git cat-file -t` on `75923bc`, `a4b4495`, `0e816e8` — all commit ✓; `gentow2_pe5_fresh.py` (17,436 B) + `gentow2_pe5_fresh_output.txt` (4,272 B) exist ✓.

**CONDITIONALITY:** the counter value 1/2 is superseded by `.80`. **The unit's own parenthetical is a model of the freeze discipline**: “S11's grade line above predates PE5 and stands as dated” — the note declines to correct the frozen line and instead states the correct reading here.

**RESOLUTION TRACE:** lines 1291–1301.

**SERIES:** ARC-SERIES member 4.

**TEETH:** the PE5 fresh route is B″'s **first γ₂-live contact** — a frame family where `ϑ`'s `γ₂`-component acts (`z₂ = η₂ ∈ F₄∖F₂`), which is the surface `.71`'s closing sentence had named as a candidate. Direct cocycle measurement `θ(0) = z₂²`; opposite-direction teeth GA1/GA2; top-slot pin GA4 (i.e. `ϑ(f₃−1) = 1`); first `e₃ = 2` cocycle-live frame GA3. GREEN 91/0 first-run-under-seal.

---

### EFF.GENTOW2.76  [changes-record — m1 CURE, the consumption-list unification]

**CANONICAL STATEMENT:**

**FORM:** display (bold-headed cure with a numbered quotation list and a bolded governing reading)

> “**m1 CURE — the three B'-consumption lists unified.** The [r3]
> text carries three mutually inconsistent consumption lists for the
> restated LEMMA GENTOW2-B, quoted:
>
> 1. Honesty box, (B-2) paragraph (S5): "the restated lemma
>    consumes only B'(3)-(5) + B'', all derived."
> 2. S5.1 [r3] bracket at clause (4): "the restated lemma no longer
>    consumes it — it consumes (3)+(5) here and B'' (S5.2)."
> 3. S11 item (ii): "the proof's false step now consumes
>    B'(3)+(4) + B'', all DERIVED."
>
> A fourth site, the S5 proof's corrected step, cites "By LEMMA
> GENTOW2-B'(3)+(4) (S5.1, ...): R_{3,beta_t}(khat_t) =
> u(beta_t)*digit(khat_t)" — a step that uses (3) alone. UNIFIED
> READING (per PE5's adjudication, [m1] + repair guidance (i); this
> reading GOVERNS over the four quoted forms): **the true
> consumption of the S5 proof's corrected step is B'(3) + B''.**
> Clause (5) is the summation display itself — re-derived inside the
> S5 proof from Cor 4.7 additivity, a restatement rather than a
> dependency; clause (4) (the per-grade u = 1 equivalence, the form
> r3 stopped consuming at the refuted slots) is consumed at exactly
> one surviving site, the restated lemma's final per-height-iff
> sentence ("The unadjusted PER-HEIGHT prescription (c_t = a_t)
> realizes psi3 itself iff u(beta_t) = 1 at each used slot").
> Clauses (3), (4), (5) are each DERIVED in S5.1 — the inconsistency
> was dependency-inventory drift, with no mathematical content at
> stake; the failure mode PE5 named (a future round deleting or
> restating B'(4) as unconsumed per S5.1's list while the iff
> sentence still cites it) is closed by this unification.”

**DERIVATION:** `[RECORD + DERIVED]` The governing reading is an adjudication, not a text edit — the four quoted sites remain byte-frozen.

**SUPERSESSION KIND:** **`counter re-reading`** (rule 18) — no display is re-issued; four glosses are re-read under one governing inventory. NOT `replacement`.

**TARGETS (rule 24):** `.29` (site 1, body L365), `.34` (site 2, body L431), `.72` (site 3, body L1248), `.26` (site 4, the S5 proof's corrected step).

**CHAIN (rule 25):** frozen four/five inconsistent sites → **`.76`** (governs over FOUR) → **`.81`** (governs over FIVE). **TERMINAL: `.81`.** A chapter cut that installs `.76` alone will leave the S6 direction-of-fit sentence (`.54`) unresolved.

**CONDITIONALITY:** the unification is explicitly **inventory drift with no mathematical content at stake** — clauses (3), (4), (5) are all derived, so no proof changes. What changes is which clause a formalization must carry as a dependency edge.

**RESOLUTION TRACE:** lines 1303–1331.

**TEETH:** PE5's named failure mode — “a future round deleting or restating B′(4) as unconsumed per S5.1's list while the iff sentence still cites it” — is a **preregistered falsifier** against future edits. Disposition: `preregistration` (rule 19), no run.

---

### EFF.GENTOW2.77  [table — m2 CURE, S6.1 rows 23–24 (DESCRIPTIVE)]

**CANONICAL STATEMENT:**

**FORM:** bold-headed cure + `[TABLE]` append

> “**m2 CURE — the two descriptive FGMN cites inventoried.** S6.1's
> table body above is byte-frozen; rows 23-24 are ADDED here by
> dated append, with the PE5 pass's own verification cited:”

`[TABLE]`

> | # | statement | use sites (status) | verification |
> |---|---|---|---|
> | 23 | Thm 4.2 normal form / eq (16): H_mu(g) = phi_r(alpha)*R_{r,alpha}(g)(y_r), phi_r(alpha) = x_r^{s(alpha)}*p_r^{u(alpha)} | S5.1 re-scoped residue paragraph ("by Thm 4.2's normal form H_mu(g) = x3^s p3^u R_{3,beta}(g)(y3)") — DESCRIPTIVE ONLY: says what w IS; no lemma conclusion consumes it (w's unit-hood comes from Cor 4.4(1) in B''s proof) | PE5 pass's own content check, report finding [m2](a): layout L1028-1030 + the eq (16) display, "content-accurate" |
> | 24 | Thm 6.6 (primes split across DISTINCT (lambda, L) pairs; with Lemma 5.3(2) = row 4 this is the "#primes = #distinct residual factors" verdict surface) | honesty-box sentence "Verdict-level machine data (prime-split patterns) is w-blind and constrains theta only" (implicit ride); explicit prose at S8's T2 disclosure — RECORD-INTERPRETATION, not a proof step | PDF-verified as a citation surface in PE4's [F1] walk (PE4 report: "FGMN additivity + eq (14) + Lemma 5.3(2)/Thm 6.6 (all PDF-verified citation surfaces)"); re-walked at PE5 A3 |

**DERIVATION:** `[RECORD]` **Compile-time layout-leg check of row 23's pin:** L1028–1030 read `Theorem 4.2. Let g ∈ K[x] be a non-zero polynomial and let α = µ(g). Then, / Hµ (g) = ϕr (α)Rr,α (g)(yr ) = ϕr (g)Rr (g)(yr ). / In particular, Pα (µ)/Pα+ (µ) = ϕr (α)∆ is a free ∆-module of rank one.` ✓ — the row's rendering `H_mu(g) = phi_r(alpha)*R_{r,alpha}(g)(y_r)` matches the first equality exactly ✓. Row 24's Thm 6.6 has **no layout pin declared** and none was verified — consistent with its DESCRIPTIVE, record-interpretation status.

**SUPERSESSION KIND:** `inventory completion` on a **byte-frozen table** — the rows are appended, not inserted.

**CONDITIONALITY:** **DESCRIPTIVE / record-interpretation status only** (see `.78`). Row 23's content (the `avatar = w` identification) is HYP.66's gate and is “now **measured to GAP at LW3**” per HYP.145.

**RESOLUTION TRACE:** lines 1333–1341; target `.50` (the frozen table).

**TEETH:** row 23's verification is a *content check by the PE5 pass*, not the S6.1 two-leg method — which is exactly why it enters at DESCRIPTIVE status and owes the two-leg method on elevation (`.78`).

---

### EFF.GENTOW2.78  [fence — the rows 23–24 status disclosure, HYP.66/HYP.145's gate]

**CANONICAL STATEMENT:**

**FORM:** bold-headed paragraph (reproduced in full at NON-IMPORT N-9)

The text is lines 1342–1347, quoted verbatim as N-9 in §2.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** this is a **gate**, and the ledger treats it as one. `spec/HYPOTHESIS_LEDGER.md` **HYP.145** (`GENTOW2 S6.1 rows 23–24`, WHERE: `…GENTOW2_PROOF_2026-08-09.md` L1342) quotes this unit verbatim, classes it `scope-fence`, and records `CONSUMED BY: HYP.66 (WFRAME OPEN-3), which is gated on exactly this row; and any future consumed-status use of rows 23–24.` **HYP.66** (`WFRAME OPEN-3`, WHERE `T5_WFRAME_2026-08-12.md` L283–286, L392) reads back: “the gap is now MEASURED, not merely known … GENTOW2 S6.1 row 23, the avatar = w identification this row is gated on, is DESCRIPTIVE-status and ‘is now measured to GAP at LW3’ (`GENTOW5_WI_2026-08-10.md:480`). See HYP.145.” Both ledger rows re-read at compile time ✓.

`docs/TIGHTNESS_CENSUS_2026-08-11.md` row **O-6** carries the same gate: “**WFRAME OPEN-3** — a derived w-law (closed form; avatar = w at theorem strength): gated on GENTOW2 S6.1 row 23's two-leg elevation (row 23/24 at DESCRIPTIVE status — GENTOW2 L1333–1345).”

**The debt is precisely stated:** elevating either cite to consumed status **owes the S6.1 two-leg method** (layout pin + fresh visual read) at that point.

**RESOLUTION TRACE:** lines 1342–1347.

**TEETH:** the two-leg method itself, as the standard rows 20–22 met.

---

### EFF.GENTOW2.79  [instrument-record — BYTE-FREEZE BF-1, SERIES member 1 of 4]

**CANONICAL STATEMENT:**

**FORM:** inline paragraph

> “BYTE-FREEZE: pre-append body md5 399017ac
> (399017ac32aac64e14c2bff5083c2c4d) = commit d798529, 78,190 bytes,
> re-verified by prefix after this append; edit shape append-only;
> sealed artifacts and statement displays byte-untouched (the m1
> unification is a governing dated reading, zero edits to the three
> quoted sites).”

**DERIVATION:** `[RECORD]`

**PIN VERIFICATION (rule 23) — recomputed:** `head -c 78190 <file> | md5sum` = `399017ac32aac64e14c2bff5083c2c4d` ✓ **EXACT**. `git cat-file -t d798529` = commit ✓. **Disposition: PINNED** (a prefix md5 over an append-only file remains recheckable; see §1 FP-2).

**CONDITIONALITY:** the parenthetical “zero edits to the three quoted sites” is consistent with the m1 CURE being a `counter re-reading` (`.76`).

**RESOLUTION TRACE:** lines 1349–1354.

**SERIES:** BYTE-FREEZE SERIES, member 1 of 4 — `.79` (78,190 B) → `.84` (82,457 B) → `.90` (86,321 B) → `.93` (90,326 B, count undeclared). Order is chronological and monotone in byte count; a merge run can reconstruct the append order from the counts alone.

**TEETH:** the prefix recomputation is the instrument; it passes.

---

### EFF.GENTOW2.80  [acceptance-box — ACCEPTANCE 2/2]

**CANONICAL STATEMENT:**

**FORM:** display (bold-headed dated acceptance record)

> “**ACCEPTANCE 2/2 — GENTOW2 IS ACCEPTED.** PE6 came back CLEAN
> (0C/0G/1m; report `GENTOW2_passPE6_report.md` @ deba21b): the
> acceptance counter closed 1/2 -> **2/2** on two consecutive clean
> passes — PE5 @ 75923bc + PE6 @ deba21b — the note through the bar
> on its SECOND count (the PE3 clean was spent at the PE4 reset).
> The note is FROZEN as of this record: dated appends only;
> statement displays and sealed artifacts byte-fixed. The arc in one
> breath: seal -> PE1 -> r1 -> PE2 -> r2 -> PE3 CLEAN -> rider ->
> PE4 BROKE B-2 at the letters x depth contact (counter reset 0/2)
> -> r3 re-derived B'' -> PE5 CLEAN restart -> rider -> PE6 CLEAN.”

**DERIVATION:** `[RECORD]` **Pins:** `GENTOW2_passPE6_report.md` exists ✓; `git cat-file -t deba21b` = commit ✓; `git cat-file -t 75923bc` = commit ✓.

**ACCEPTANCE-SCOPE ENUMERATION (rule 35).** The grade's scope is fixed by three co-resident fences — see §1 FP-4. **No consumer may quote the 2/2 without them**: the theorem is third-stage only (`.58`), the (β) floor is a hypothesis (`.25`, `.55`), and rows 23–24 are DESCRIPTIVE (`.78`). Independently corroborated: `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` row 6 records `| 6 | GENTOW2 | CERTIFIED (batch-1 + RUN E discharge) | — |`; `docs/PROJECT_STATE.md` DATED APPEND #16 is titled “GENTOW1 + GENTOW2 BOTH ACCEPTED” and its board reads “HETOW ✓ · GENTOW1 ✓ · GENTOW2 ✓ (3 of 7 accepted)”; `docs/STATEMENT_LEDGER_2026-08-10.md` L295 records “grade: ACCEPTED 2/2”.

**CONDITIONALITY:** the model-diversity question is NOT settled by this record — the six passes PE1–PE6 are not identified by arm in the note. What IS decorrelated is the post-acceptance ratification (`.85`), which is Codex.

**CHAIN — the counter, in full (rule 25):** `0/2` (composition, `.01`) → `0/2` after r1 (`.65`) → `0/2` after r2 (`.66`) → **`1/2`** at PE3 (`.68`, `.70`) → **`0/2` RESET** at PE4 (`.71`) → **`1/2`** at PE5 (`.75`) → **`2/2`** at PE6 (**this unit**). **TERMINAL: `.80`.** Six layers; a flat “supersedes” field cannot express it.

**RESOLUTION TRACE:** lines 1358–1367.

**SERIES:** ARC-SERIES member 5.

**TEETH:** two consecutive clean fresh-context passes; §7.

---

### EFF.GENTOW2.81  [changes-record — PE6 [m-1] FOLD, the fifth consumption-list site]

**CANONICAL STATEMENT:**

**FORM:** display (bold-headed fold with a quoted target and a bolded governing reading)

> “**PE6 [m-1] FOLD — the FIFTH consumption-list site named.** The
> post-PE5 rider's m1 unification above declared its governing
> reading "over the four quoted forms"; PE6 found a fifth occurrence
> un-named: the S6 direction-of-fit sentence (body L938), quoted:
> "The repo-side inputs — B-1 and [r3] the derived unit laws
> B′(3)–(5)/B″ (B-2 itself refuted and consumed nowhere) — enter
> only the bridge LEMMA GENTOW2-B". FOLD: the governing reading —
> **the S5 proof's corrected step consumes B′(3) + B″** — governs
> over FIVE quoted forms: the rider's four plus this S6 sentence
> (content identical to quoted form 1, the honesty box's
> "(3)–(5) + B″", and resolved identically by the unification).
> PE6's grep census pins the five list sites at body
> L365/L431/L535/L938/L1248, with the restated lemma's final
> per-height-iff sentence as B′(4)'s sole surviving consumer. Zero
> edits to the S6 sentence (byte-frozen).”

**DERIVATION:** `[RECORD]`

**SUPERSESSION KIND:** **`counter re-reading`** with **`inventory completion`** — the reading does not change; its scope grows from four sites to five.

**TARGETS (rule 24):** `.29`, `.34`, `.72`, `.26`, **`.54`** (the newly named fifth).

**CHAIN:** frozen five sites → `.76` (four) → **`.81` (five)**. **TERMINAL: `.81`, single, all consumer classes.**

**COMPILER VERIFICATION OF THE GREP CENSUS (§4.6 NM-3).** PE6 pins the five sites at body `L365/L431/L535/L938/L1248`. Three land exactly: **L431** is inside `.34`'s `[r3]` bracket (“it consumes (3)+(5) here and B″ (S5.2)”) ✓; **L938** is `.54`'s direction-of-fit sentence, whose `B′(3)–(5)/B″` string sits at body L937–938 ✓; **L1248** is `.72`'s sub-item (ii) “all DERIVED” line ✓. **L365** falls inside `.26`'s corrected step (“By LEMMA / GENTOW2-B′(3)+(4) (S5.1, …)” at body L364–366) ✓ — i.e. PE6's L365 is the S5 *proof* site, which the m1 CURE lists as the fourth (unnumbered) site. **L535** falls inside `.34`'s clause-(4) region as well (body L535 = “no longer consumes it — it consumes (3)+(5) here and B″ (S5.2)];”), so **L431 and L535 both point into the S5.1 bracket's two halves**, and the honesty-box site (`.29`, body L430–431) shares L431. The census is therefore **correct as a set of five line pins but its site↔quotation assignment is ambiguous at L431/L535**; the compiler records this as a NEAR-MISS in line-attribution only (§4.6 NM-3), with the five *quotations* themselves unambiguous and each mapped to a unit above. No mathematical consequence; the governing reading is unaffected.

**CONDITIONALITY:** none — the reading is the same as `.76`'s.

**RESOLUTION TRACE:** lines 1369–1383.

**TEETH:** PE6's grep census is the instrument; disposition **`arithmetic recount`** (rule 27) — a count of occurrences, re-run by the compiler and found to be five quotations at ambiguous line attribution.

---

### EFF.GENTOW2.82  [run-record — the w-DISCLOSURE, three dated bracket-riders]

**CANONICAL STATEMENT:**

**FORM:** display (bold-headed disclosure + three bulleted bracket-riders)

> “**w-DISCLOSURE DATED (bracket-riders; the three frozen sentences
> stay byte-untouched and each now carries the dated bracket
> below).** PE6's fresh route MEASURED w — the first w measurement
> in the corpus (runner `verification/openmath/gentow2_pe6_fresh.py`,
> seal ade1727; run-1 68/1 RED kept as committed with the disclosed
> verifier-instrument literal, diagnostic 72a3f29 / disclosure
> 891fd96; run-2 GREEN 68/0 @ dfbc938). MEASURED DATA: w-avatar =
> z₁ (LD1, u₃ = 19), z₁² (LD3, u₃ = 37), z₂² (GA1, u₃ = 21),
> z₂ (GA3, u₃ = 41) — ≠ 1 at each of the 6 measured primes across
> the 4 frames, and u₃-DEPENDENT within each tower (both
> discrimination pairs fired: w-constant-per-tower and w ≡ 1 are
> killed on the measured record). The dated bracket, riding each of
> the three frozen "w not computed" sentences:
>
> * S5 honesty-box region (body L411–413), "not computed anywhere in
>   the corpus — see S5.1's re-scoped residue paragraph" —
>   [2026-08-10: now MEASURED at 4 frames, data above; ≠ 1 at each
>   measured prime].
> * S5.1 re-scoped residue paragraph (body L692–694), "an explicit
>   z₁, z₂-monomial, computable by a level-3 letter-formula-style
>   derivation but not computed anywhere in the corpus" —
>   [2026-08-10: measured (not derived) at 4 frames; the closed-form
>   letter derivation stays open].
> * S11 not-claim list (body L1279–1280), "no computation of w (a
>   level-3 letter-formula-style derivation, open)" —
>   [2026-08-10: the derivation stays open; the MEASUREMENT now
>   exists — values above, PE6 @ deba21b].”

**DERIVATION:** `[RECORD]` **Pins:** `gentow2_pe6_fresh.py` (18,139 B) ✓, `gentow2_pe6_fresh_output.txt` (2,437 B, the RED run-1) ✓, `gentow2_pe6_fresh_output_run2.txt` (2,479 B, the GREEN run-2) ✓ — **all three artifacts exist, including the RED run kept as committed.** `git cat-file -t` on `ade1727`, `72a3f29`, `891fd96`, `dfbc938` — all commit ✓.

**SUPERSESSION KIND:** **`as-of scoping`** (rule 18) — three frozen sentences are given a dated as-of reading. NOT `replacement` (no text moves), NOT `withdrawal` (nothing becomes unavailable): each sentence's *derivation* half stays true and its *computation* half becomes as-of-false.

**TARGETS (rule 24):** `.28` (body L411–413), `.40` (body L692–694), `.74` (body L1279–1280).

**CONDITIONALITY — the three targets carry `STALE-SELF-DESCRIPTION` (rule 26)**, and the bracket is what tells the reader which half is stale. The honest scope note (`.83`) fences the measurement itself.

**ARITHMETIC AUDIT (rule 22) — the frame/prime census:** 4 frames named (LD1, LD3, GA1, GA3) with `u₃ ∈ {19, 37, 21, 41}`; 6 measured primes. The frame count (4) and the avatar list (4 entries) agree ✓; the prime count (6) exceeds the frame count, which is consistent with multiple primes per frame and is stated as such (“6 measured primes across the 4 frames”). Cross-check: `.45` gives LD1 `u₃ = κ₃ = 19` ✓ and LD3 `κ₃ = 37/2` with `e₃ = 2`, so `u₃ = e₃κ₃ = 37` ✓ **EXACT**. GA1's `u₃ = 21` coincides with the S2 dictionary's `u₃` (`.05`) — a different tower, same value; recorded so a reader does not conflate them. T5's independent quotation of this record (`T5_WFRAME_2026-08-12.md` ledger item 3) reads “w-avatar = z₁ (LD1), z₁² (LD3), z₂² (GA1), z₂ (GA3) — ≠ 1 at all 6 primes of the 4 frames” ✓ **byte-consistent**.

**RESOLUTION TRACE:** lines 1385–1418.

**TEETH:** **two discrimination pairs, both fired** — `w`-constant-per-tower is killed (`w` is `u₃`-dependent within a tower) and `w ≡ 1` is killed. Disposition: `executable regression`, GREEN 68/0 on run-2, with run-1's RED disclosed and committed rather than discarded (**`disclosed non-repair`** handling of a verifier-instrument literal, rule 20).

**AUDIT (rule 31 `hostile-pass certification`):** PE6's route did not merely pass — it produced the corpus's FIRST `w` measurement, which is new positive content from a hostile pass.

---

### EFF.GENTOW2.83  [fence — the honest scope note on the w measurement]

**CANONICAL STATEMENT:**

**FORM:** paragraph

> “Scope note (honest): PE6 measured w at 4 frames / 6 primes; the
> level-3 letter-formula derivation of w in closed form remains
> open, and the measured record does not decide w at unmeasured
> frames. GENTOW5's arc reads this data before its next pass (its
> w_i = 1-open clause carries the matching dated note; see that
> note's S3(a) post-PE6 bracket).”

**DERIVATION:** `[RECORD]`

**XREF VERIFICATION:** `grep -n 'post-PE6' GENTOW5_PROOF_2026-08-09.md` → L815 (`post-PE6 acceptance record — measured at 4 frames; the closed-form`) ✓ count 1; `grep -c 'S3(a)'` in that file = 5 ✓; `grep -cF 'GENTOW2'` = 73 ✓. The cross-note obligation the sentence names has LANDED.

**CONDITIONALITY:** this is the fence on `.82`. **The measurement does not derive `w` and does not decide it off the measured frames.**

**RESOLUTION TRACE:** lines 1413–1418.

**TEETH:** none of its own.

---

### EFF.GENTOW2.84  [instrument-record — BYTE-FREEZE BF-2, SERIES member 2 of 4]

**CANONICAL STATEMENT:**

**FORM:** inline paragraph

> “BYTE-FREEZE: pre-append body md5 8fce60f8
> (8fce60f8992ab7b3964c5a65aec38cc5), 82,457 bytes (the post-PE5
> rider state, rider commit 188b894, unchanged through PE6),
> re-verified by prefix after this append; edit shape append-only;
> the five consumption-list sites, the three w-sentences, and the
> sealed artifacts byte-untouched.”

**DERIVATION:** `[RECORD]`

**PIN VERIFICATION (rule 23) — recomputed:** `head -c 82457 | md5sum` = `8fce60f8992ab7b3964c5a65aec38cc5` ✓ **EXACT**. `git cat-file -t 188b894` = commit ✓. **PINNED.**

**CONDITIONALITY:** none.

**RESOLUTION TRACE:** lines 1420–1425.

**SERIES:** BYTE-FREEZE SERIES member 2 of 4 (see `.79`).

**TEETH:** the prefix recomputation; passes.

---

### EFF.GENTOW2.85  [acceptance-box — the TOWERRAT-R3 ratification provenance]

**CANONICAL STATEMENT:**

**FORM:** italic-headed provenance block

> “*Provenance: the Codex ratification batch on the frozen accepted
> note (`CODEX_TOWERRAT_2026-08-10.md` §S4, session
> 019fe98f-1e70-7321-9422-de37059d2b46, outcome RATIFIED-WITH-ANNEX,
> 4 MINOR, each adjudicated REAL at annex grade). The 2/2 acceptance
> is unrevoked; the body stays BYTE-FROZEN; each item below GOVERNS
> the reading of its quoted sentence. Each repair is re-derived from
> the note's own lemmas and the FGMN citations, not transcribed.*”

**DERIVATION:** `[RECORD]` **XREF verification:** `lean/notes/openmath/CODEX_TOWERRAT_2026-08-10.md` exists ✓; L48 reads `- GENTOW2: session \`019fe98f-1e70-7321-9422-de37059d2b46\` (details in S4)` ✓; L56 reads `| GENTOW2 | **RATIFIED-WITH-ANNEX** | 4 MINOR | 4 REAL MINOR (hygiene) | R3 (batch) |` ✓; L252 is the heading `## S4. GENTOW2 — Codex findings + adjudication` ✓; L299 reads `**GENTOW2 outcome: RATIFIED-WITH-ANNEX.** No GAP-or-worse; the note` ✓.

**CONDITIONALITY:** the acceptance is **unrevoked**; the four items are hygiene, adjudicated REAL at annex grade.

**RESOLUTION TRACE:** lines 1430–1436.

**SERIES:** ARC-SERIES member 6 (final).

**TEETH — disposition `decorrelated-model audit` (rule 27):** this is a **different model** (Codex) on a **frozen accepted note**, and it found four real defects that six in-house passes did not — including a truncated display (`.88`) and a symbol overload (`.89`). It is the note's decorrelation evidence, and the strongest argument in the corpus for the standing Codex-as-adversarial-verifier rule.

---

### EFF.GENTOW2.86  [changes-record — R3-1, the [Q10] scope clause STRUCK]

**CANONICAL STATEMENT:**

**FORM:** display (bold-headed dated hygiene correction)

> “**R3-1 (the [Q10] scope clause, S6 hypothesis audit row (H-b),
> body L924–925).** Quoted: "— and Cor 6.4 needs only 'a MacLane
> chain', not optimality." **STRUCK** (governing reading: the clause
> is withdrawn). Re-derivation: [Q10] hypothesizes a chain "as in
> (4)", and this note's own S2 dictionary identifies display (4)
> with the OPTIMAL MacLane chain (degrees strictly increasing), so
> the quoted clause outruns the citation. The audit row's license is
> the derivation that PRECEDES the struck clause — stage properness
> (e₂f₂ ≥ 2, e₃f₃ ≥ 2) gives deg x < deg Φ′ < deg Φ₂ strict — and
> the S4 application consumes exactly that optimal chain. Consumer
> check at the (H-b) row: no other sentence of the note cites the
> struck clause.”

**DERIVATION:** `[RECORD]`

**SUPERSESSION KIND:** **`withdrawal`** (rule 29) with a **`deletion` sub-kind marker** — the clause is struck and nothing replaces it, AND the struck string remains byte-intact at body L924–925 unless the edge is installed. A merge that reads this as `replacement` will leave the clause readable as live text.

**TARGETS (rule 24):** `.53` (the (H-b) row).

**CONDITIONALITY:** the strike is **CONSERVATIVE, not corrective** — see OPEN-CALL 1. The consumer check is verified: `grep` for the struck string finds it only at its own site and at R3-1's quotation of it.

**RESOLUTION TRACE:** statement lines 1438–1449; target body lines 924–925.

**TEETH:** the note's own consumer check; independently, the compiler's re-read of FGMN Def 3.1 at L613–615 (`.18`) — which is what makes OPEN-CALL 1 statable at all.

---

### EFF.GENTOW2.87  [changes-record — R3-2, the `digit(G)` notation fence]

**CANONICAL STATEMENT:**

**FORM:** display (bold-headed dated hygiene correction)

> “**R3-2 (the `digit(G)` notation fence, LEMMA GENTOW2-B″ step (iv),
> body L770–775).** S5.1's (R-repo) defines `digit` on Φ₂-free
> elements of degree < m₃ (its opening sentence); G = ẑN^d is
> Φ₂-free of exact grade β_t (step (ii)) but its degree can reach
> ≥ m₃ at d ≥ 2, so the token "digit(G)" in the displayed chain
> "digit(Q₀) = digit(G) = res(ẑ(x₀))·res((N^d/M)(x₀))" sits outside
> the definition's scope. Governing reading: "digit(G)" abbreviates
> the normalized evaluation residue res(G(x₀)/M(x₀)) — which is what
> the chain computes (Φ₂(x₀) = 0 gives G(x₀) = Q₀(x₀), an equality
> of evaluations, hence of evaluation residues against the same M).
> B-1 and B′(3) are invoked only on Q₀ (deg Q₀ < m₃, Φ₂-free — in
> scope, as the display's own parenthetical pins); no clause of the
> proof applies B-1 to G.”

**DERIVATION:** `[RECORD]`

**SUPERSESSION KIND:** **`counter re-reading`** — a token is re-read; no display is re-issued and no proof step changes.

**TARGETS (rule 24):** `.44` (step (iv)), and definitionally `.33` (the (R-repo) scope).

**CONDITIONALITY:** the reading is exactly the same species of scope defect as PE2's F2 finding against B′'s h-step (`.35`) — **the third time in this note that a `deg < D₂` fence was crossed by notation.** Recorded in §8 as a standing formalization hazard.

**RESOLUTION TRACE:** statement lines 1451–1463; target body lines 770–775.

**TEETH:** the note's own scope-check on `Q₀`; disposition `Lean theorem` (a definitional obligation on `digit`'s domain).

---

### EFF.GENTOW2.88  [changes-record — R3-3, the truncated α display completed]

**CANONICAL STATEMENT:**

**FORM:** display (bold-headed dated hygiene correction with a completed display)

> “**R3-3 (the truncated α display, S5 proof opening, body L342).**
> Quoted: "**Proof.** Write α := e₃f₃(w₃...". Completed display:
>
>     α := e₃f₃(w₃ + λ₃).
>
> Re-derivation from the proof's own next sentence: ν(Φ₂^{e₃f₃}) =
> e₃f₃(w₃ + λ₃) = α, and the adjacent parenthetical (FGMN
> α = e_r f(w_r + λ_r) with e_r = e₃, f = f₃, w_r = w₃, λ_r = λ₃)
> instantiates to the same expression; every subsequent use of α in
> S5 computes with it. Typographical truncation; no computation
> changes.”

**DERIVATION:** `[RECORD]` The completion is doubly determined (see `.26`'s arithmetic audit).

**SUPERSESSION KIND:** **`replacement`** — a truncated display is replaced by the complete one. Replacement display carried verbatim above.

**TARGETS (rule 24):** `.26` (body L342).

**CONDITIONALITY:** none; “no computation changes”.

**RESOLUTION TRACE:** statement lines 1465–1475; target body line 342.

**TEETH:** none needed — the completion is forced.

**AUDIT (rule 27 `decorrelated-model audit`):** a truncated formula survived **six in-house hostile passes** and was caught by the first outside model. Named in §8 as the corpus's cheapest argument for decorrelated review.

---

### EFF.GENTOW2.89  [convention — R3-4, the ψ₂ disambiguation line]

**CANONICAL STATEMENT:**

**FORM:** display (bold-headed dated standing convention)

> “**R3-4 (the ψ₂ symbol overload — the standing disambiguation
> line).** Governing convention for every read of "ψ₂" in this note:
> **ψ₂^{FGMN} := R₂(φ₃) = minpoly(z₂)** (Cor 5.6(2)) and
> **ψ₂^{repo} := minpoly(η₂)** (the repo tower's Φ′-side residual)
> are DISTINCT symbols in general, related by S5.1's LETTER FORMULA
> z₂ = η₂·z₁^{−⌊ℓ₁u₂/e₁⌋} and equal exactly when the z₁-twist fixes
> ψ₂ — the note's own LP1 witness has z₂ = 1 while η₂ = z₁ ≠ 1, so
> their (linear) minimal polynomials differ there. The two S4 sites,
> fenced: (site 1) the Cor 6.4 instantiation display "R₂(Φ₃) =
> ψ₂^{ℓ₃}" (body L252) reads ψ₂ = ψ₂^{FGMN} — the [r2] "twist-aware
> form" bracket there already says so; (site 2) the S4 consumption
> note (body L272–293) consumes the root statement in the REPO
> letter ("η₂(ξ) is a repo-ψ₂-root"), translated through the single
> embedding σ per its [r2] bracket. No consumed inference equates
> the two letters; this line only fences which ψ₂ each display
> names.”

**DERIVATION:** `[RECORD]`

**SUPERSESSION KIND:** **`scope-pin`** (rule 18) — a standing convention is installed over every occurrence of a symbol. It supersedes nothing and replaces nothing; it types.

**TARGETS (rule 24):** `.23` (site 1, body L252), `.24` (site 2, body L272–293), and every unqualified `ψ₂` in the note — including `.05`'s dictionary row and `.20` clause (c).

**ARITHMETIC AUDIT (rule 22) — the note's “(linear)” is CORRECT; a first compiler pass wrongly flagged it.** FGMN indexes `ψ_i ∈ F_i[y]` as the minimal polynomial of `z_i` over `F_i` (X27, layout L862), and `z_i ∈ F_{i+1}`. So `ψ₂` — both readings — lives in `F₂[y]`, and at LP1 `ψ₁ = y² + y + 1` (the r2 probe, `.67`) gives `f₁ = 2` and `F₂ = F₁[z₁] = F₄`. Both `z₂ = 1` and `η₂ = z₁` therefore lie in `F₂ = F₄`, and their minimal polynomials **over `F₂`** are `y + 1` and `y + z₁` — **both linear, and distinct because `z₁ ≠ 1`**, exactly as R3-4 states. The first pass computed both minimal polynomials over the two-element field instead of over the level-2 residue field `F₂ = F₄` and wrongly concluded that `ψ₂^repo` is quadratic. Booked here per rule 39 rather than deleted. **No source defect.**

**CONDITIONALITY:** the two symbols coincide **exactly when** `z₁^{⌊ℓ₁u₂/e₁⌋}` fixes `ψ₂`; the S2 witness (`f₁ = 1` over `q = 2`, `z₁ = 1`) is such a case, and the note's dictionary row exploits that.

**RESOLUTION TRACE:** statement lines 1477–1492; targets body lines 252, 272–293, and the S2 row at line 77.

**TEETH:** the LP1 probe is the witness that separates the two letters (`.67`).

---

### EFF.GENTOW2.90  [instrument-record — BYTE-FREEZE BF-3, SERIES member 3 of 4]

**CANONICAL STATEMENT:**

**FORM:** inline paragraph

> “BYTE-FREEZE: pre-append body md5 e27b97f2
> (e27b97f2f462d88370190f1aaa52042b) = commit 21293c8, 86,321
> bytes, re-verified by prefix after this append; edit shape
> append-only; statement displays and sealed artifacts
> byte-untouched.”

**DERIVATION:** `[RECORD]`

**PIN VERIFICATION (rule 23) — recomputed:** `head -c 86321 | md5sum` = `e27b97f2f462d88370190f1aaa52042b` ✓ **EXACT**. `git cat-file -t 21293c8` = commit ✓. **PINNED.**

**CROSS-PIN:** commit `33f86204`'s own message independently states “Pure append verified by prefix md5 e27b97f2 at 86,321 bytes; acceptance 2/2 unrevoked” — the same figure declared in git metadata and in the note, agreeing ✓.

**CONDITIONALITY:** none.

**RESOLUTION TRACE:** lines 1494–1498.

**SERIES:** BYTE-FREEZE SERIES member 3 of 4.

**TEETH:** the prefix recomputation; passes.

---

### EFF.GENTOW2.91  [acceptance-box — the S-2 absorption provenance]

**CANONICAL STATEMENT:**

**FORM:** italic-headed provenance block

> “*Provenance: simplification pass S-2, blueprint protocol
> (`docs/SIMPLIFICATION_BLUEPRINT_2026-08-10.md` §5.3 item 4);
> T3 = `T3_COCYCLE_TELESCOPE_2026-08-12.md`, ACCEPTED 2/2 (T3P2 + T3P3
> clean; runs of record in that note). Edit shape append-only; the body
> above stays BYTE-FROZEN.*”

**DERIVATION:** `[RECORD]` **XREF verification:** `docs/SIMPLIFICATION_BLUEPRINT_2026-08-10.md` exists (38,971 B) ✓; `lean/notes/openmath/T3_COCYCLE_TELESCOPE_2026-08-12.md` exists ✓; T3's grade is independently corroborated at `docs/in-progress/LEAN_SCOPING_consumption_map_2026-08-12.md` §T3 (d): “**ACCEPTED 2/2 (2026-08-12)** — the only accepted T-unit. Arc: composed → revised vs certified seam → T3P1 (0C+1G, FRAME-C comparison-port arithmetic) → r1 → T3P2 CLEAN → T3P3 CLEAN.” ✓

**CONDITIONALITY:** none.

**RESOLUTION TRACE:** lines 1503–1507.

**TEETH:** T3's own acceptance arc.

---

### EFF.GENTOW2.92  [absorption-record — (ABS-G2), the S-2 absorption of B″]

**CANONICAL STATEMENT:**

**FORM:** display (bold-headed dated absorption record)

> “**LEMMA GENTOW2-B″ (S5.2, display (6) with its B-law/rescaling
> corollary) is ABSORBED by S-2's LEMMA COCYCLE-TELESCOPE as the
> instance (ABS-G2)** — T3's boundary-read port (T3-BR) at s = f₃ − t,
> q = u₃, N(q) = n̂₂(u₃), with (BR1)–(BR5) instantiated by this note's
> own peel, expansion, positive-degree elimination, exact constant-digit
> law, and root evaluation (the S5.2 proof's steps (i)–(iv));
> ϑ(t) = Θ_N(s; u₃) and w = R_{3,κ̄}(n̂₂(u₃)) — per the S-2 consumption
> check (runs/comp5/T3CC_output.log, GENTOW2-B″ leg: PASS). The
> absorption is of the CONCLUSION only: the source-local read package
> remains this note's supply, and neither the displayed B-law nor a
> one-w family is an input to the T3 instance (T3 §3's fence). The S5.2
> statement here stays byte-frozen and authoritative; consumers may
> cite either this display (6) or T3's (ABS-G2).”

**DERIVATION:** `[RECORD]`

**XREF VERIFICATION — every designation grep-verified in the target note:**

`[TABLE]`

| Designation | File | count | Located |
|---|---|---:|---|
| `LEMMA COCYCLE-TELESCOPE` | `T3_COCYCLE_TELESCOPE_2026-08-12.md` | 6 | ✓ |
| `ABS-G2` | same | 3 | T3 L520 (`\tag{ABS-G2}`), L908 (absorption-map row), L1195 (absorption-count audit) |
| `T3-BR` | same | 3 | ✓ |
| `(BR1)` | same | 5 | ✓ |
| `(BR5)` | same | 5 | ✓ |
| `GENTOW2-B″` | same | 2 | ✓ (plus 8 as `GENTOW2-B\('' \)` — see §4.6 NM-4) |
| `Theta_N` / `\Theta_N(s;q)` | same | 7 sites | T3 L108, 124, 139, 298, 400, 482, 644, 931 |
| `GENTOW2-B″ — PASS` | `runs/comp5/T3CC_output.log` | 1 | **line 1** of the log |

**ORIENTATION CROSS-CHECK (parent charge item (b)).** T3's own instantiation, from `T3_COCYCLE_TELESCOPE_2026-08-12.md` (the `(ABS-G2)` block, L475–520). The lead-in sentence is verbatim; the display beneath it is a **`[TRANSCRIBED from LaTeX]`** Unicode rendering of the source's `\[ … \]` block, not a byte quotation:

> “The source's B-law-oriented unit is”

`[TRANSCRIBED from LaTeX]` — source bytes: `\vartheta_{\rm G2}(t) := \operatorname{res}\!\left( \frac{\widehat n_2(su_3)}{\widehat n_2(u_3)^s} \right) = \Theta_N(s;u_3).`

    ϑ_G2(t) := res( n̂₂(su₃) / n̂₂(u₃)^s ) = Θ_N(s; u₃).

and T3's global orientation box `(T1-THETA)`, same treatment — `[TRANSCRIBED from LaTeX]`, source bytes `\Theta_N(s;q) := \vartheta_N(s;q)^{-1} = \operatorname{res}\!\left( \frac{N(sq)}{N(q)^s} \right).`:

    Θ_N(s;q) := ϑ_N(s;q)^{−1} = res( N(sq) / N(q)^s ).

So `ϑ_{G2}(t) = Θ_N(f₃−t; u₃) = ϑ_N(f₃−t; u₃)^{−1}` — **GENTOW2's ϑ is the INVERSE of the telescope cocycle ϑ_N**, exactly as T1's `(C3-Theta)` states with `Θ_i(t) = ϑ_{i,f_{i+1}−t}^{−1}`. Three notes, one orientation, verified at the byte level. The absorbed display `(ABS-G2)` reproduces `u(β_t) = ϑ_{G2}(t)w^{f₃−t}` and `y^{f₃} − Σ ϑ_{G2}(t)w^{f₃−t}c_t y^t = w^{f₃}P(y/w)` — **identical to display (6) and its corollary** ✓.

**SUPERSESSION KIND:** **NONE — this is a `dual-cite` absorption, not a supersession.** The note is explicit: “The S5.2 statement here stays byte-frozen and authoritative; consumers may cite either this display (6) or T3's (ABS-G2).” Both edges are live in the DAG. A merge that treats `(ABS-G2)` as replacing display (6) would delete a live authoritative statement.

**CONDITIONALITY:** absorption **of the CONCLUSION only**. The source-local read package (steps (i)–(iv)) remains GENTOW2's supply; T3 does not take it. And per T3's own anti-circularity fence (L143–145), T3 does NOT cite T1's conditional B-law as a premise for `[GENTOW5-W(i)]`.

**RESOLUTION TRACE:** lines 1509–1521.

**TEETH:** the S-2 consumption check RAN and PASSED (`runs/comp5/T3CC_output.log` line 1: `1. GENTOW2-B″ — PASS`). **This is the note's one landed protocol obligation and it is discharged** — the opposite posture from T4, whose two appends had not landed.

---

### EFF.GENTOW2.93  [instrument-record — BYTE-FREEZE BF-4, SERIES member 4 of 4]

**CANONICAL STATEMENT:**

**FORM:** inline paragraph

> “BYTE-FREEZE: pre-append body md5 69b71584e8a74e89479b067f66bfd491, re-verified
> by prefix after this append; edit shape append-only; statement
> displays and sealed artifacts byte-untouched.”

**DERIVATION:** `[RECORD]`

**PIN VERIFICATION (rule 23) — recomputed by search, since no byte count is declared:** the prefix md5 matches at **byte 90,326**, which is the start of body line 1499 (immediately before the two blank lines and the `### Dated absorption append` heading). Compiler method: exhaustive prefix scan over `[80000, 91755]`, unique hit. **PINNED**, with a MINOR inventory defect: this is the only one of the four byte-freeze declarations that omits its byte count, so it is the only one a checker cannot verify in O(1). Booked at §9 OPEN-CALL 4.

**CONDITIONALITY:** none.

**RESOLUTION TRACE:** lines 1523–1525 (the note's final lines).

**SERIES:** BYTE-FREEZE SERIES member 4 of 4, TERMINAL. Byte counts in order: 78,190 → 82,457 → 86,321 → 90,326; strictly increasing ✓, and the final append carries the file to 91,755 bytes ✓.

**TEETH:** the prefix recomputation; passes.

---

## 4. XREF verification ledger

Every positive XREF below was checked at compile time (2026-08-14) against the working tree, with the count or the located line recorded inline. Line numbers are 1-based.

### 4.1 FGMN layout pins — the [Q1]–[Q10] inventory

Source: `docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt` (2,057 lines / 150,185 bytes). **All ten quotes re-read at their cited lines; all ten land on the cited statement.** The inventory is compiled **as the note states it** (per the parent charge) — for the mismatch with `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md`'s restatement of the same inventory, see OPEN-CALL 3.

`[TABLE]`

| ID | Q-tag | Note's attribution | Cited lines | Layout head-of-span text | Verdict |
|---|---|---|---|---|---|
| X01 | [Q1] | Lemma 1.11 | L275 | `Lemma 1.11. Every φ ∈ KP(µ) is irreducible in Kv [x].` | **EXACT** |
| X02 | [Q2] | Corollary 1.13 | L315 | `Corollary 1.13. KP(µ) ⊂ O[x].` | **EXACT** |
| X03 | [Q3] | Definition 5.2 | L1238–1239 | `Definition 5.2. For a non-zero g ∈ K[x], we say that Nµ,φ (g) is one-sided of slope −λ if` | **EXACT** (2-line reflow) |
| X04 | [Q4] | Lemma 5.3 | L1240–1244 | `Lemma 5.3. A monic polynomial g ∈ K[x] belongs to KP(µ) if and only if either:` | **EXACT** (5-line reflow) |
| X05 | [Q5] | Corollary 4.12 + proof construction | L1161–1163, L1164–1166 | `Corollary 4.12. Let ψ ∈ Fr [y] be a monic polynomial of degre f such that ψ(0) 6= 0.` … `of g0 , we may assume that deg g0 < er f mr . Then, g = φerr f + g0 satisfies what we want.` | **EXACT**, incl. the `degre` typo; leading ellipsis honest |
| X06 | [Q6] | **Theorem 5.8, proof**, degree-forcing display | L1296–1302 | span begins mid-L1296 at `If ψ 6= y, then there exists a`; **enclosing statement is `Theorem 5.8` at L1289–1290**, proof L1291–1302 | **EXACT + attribution CONFIRMED** (the `Theorem 4.8.` token at the head of L1296 is a split cross-reference, not a heading) |
| X07 | [Q7] | Proposition 5.7 + eq (14) | L1276–1281, L1004 | `Proposition 5.7. Let φ, φ′ ∈ KP(µ). The following conditions are equivalent:` ; `(14)   Ri,α (φsi ) = y ⌊s/ei ⌋ , Ri (φsi ) = 1, 1 ≤ i ≤ r.` | **EXACT** (superscript typography normalized) |
| X08 | [Q8] | Corollary 4.7 | L1121–1126 | `Corollary 4.7. Let 0 ≤ i ≤ r and α ∈ Γi .` (items at L1124–1126; L1122–1123 are a running header + blank, correctly elided) | **EXACT** |
| X09 | [Q9] | Theorem 6.3 + proof opening | L1458–1464, L1465 | `Theorem 6.3. Let F ∈ P be a prime polynomial and θ ∈ K v a root of F .` ; `Proof. If F = φ, then both conditions φ |µ F and v(φ(θ)) > µ(φ) hold.` | **EXACT** |
| X10 | [Q10] | Corollary 6.4 + eq (23) | L1523–1527 | `Corollary 6.4. With the above notation, suppose that φ |µ F and µ admits a MacLane` | **EXACT** |

**In-note occurrence counts** (`grep -cF` on the note): `[Q1]` 4 · `[Q2]` 4 · `[Q3]` 2 · `[Q4]` 5 · `[Q5]` 2 · `[Q6]` 4 · `[Q7]` 9 · `[Q8]` 8 · `[Q9]` 4 · `[Q10]` 6. **Total 48 tagged uses.** No Q-tag is decorative: every one has at least two uses (statement + at least one consumption site).

### 4.2 FGMN supporting and consumed pins (S6.1 rows 5, 10, 14–23 + the supporting paragraph)

`[TABLE]`

| ID | Statement | Cited lines | Layout head-of-span text | Verdict |
|---|---|---|---|---|
| X11 | Cor 4.4 item (4) (S6.1 row 5) | L1089 | `(4) deg Ri (g) = (s′ (g) − s(g))/ei and Ri (g)(0) 6= 0.` | **EXACT** |
| X12 | Cor 4.4 item (1) (cited at `.35` as “L1089 region”) | actually **L1085** | `(1) Ri,α (g)(yi ) = 0 if and only if Ri,α (g) = 0 if and only if g ∈ Pα+ (µi ).` | **NEAR-MISS NM-1** |
| X13 | Cor 4.4 item (3) (cited at `.35`) | actually **L1088** | `(3) deg Ri,α (g) = ⌊s′ (g)/ei ⌋ and ordy (Ri,α (g)) = ⌊s(g)/ei ⌋.` | **NEAR-MISS NM-1** |
| X14 | Cor 5.6 (S6.1 row 10) | L1263–1265 | `Corollary 5.6. For all 0 ≤ i < r,` … `(2) Ri (φi+1 ) = ψi , the minimal polynomial of zi over Fi .` | **EXACT** |
| X15 | Cor 3.3 (row 14) | L647 | `Corollary 3.3. Let 1 ≤ i ≤ r. For any (s, β) ∈ Z≥0 × Γ(µi−1 ), there exists a ∈ K[x] such` | **EXACT** |
| X16 | Lemma 3.17 (row 15) | L982 | `Lemma 3.17. For all 0 ≤ i ≤ r, α ∈ Γi , the operator Ri,α vanishes on Pα+ (µi ).` | **EXACT** |
| X17 | Thm 4.8 (row 16) | L1136 | `Theorem 4.8. The mapping Rr,0 : ∆ −→ Fr [y] is an isomorphism of Fr -algebras and` | **EXACT** |
| X18 | Prop 1.15 (row 17) | L340–344 | `Proposition 1.15. If φ is a key polynomial for µ, then` (items (1) L341–342, (2) L343–344) | **EXACT** |
| X19 | Def 3.12 + §3.3 ℓᵢ,ℓ′ᵢ (row 18) | L813–821 | `3.3. Rational functions attached to a MacLane chain.` (L814) … `Definition 3.12.` (L819) … `Φi = φi (πi )−Vi , γi = (Φi )ei (πi )−hi , πi+1 = (Φi )ℓi (πi )ℓ′i , 1 ≤ i ≤ r.` (L821) | **EXACT** |
| X20 | eq (9) + §3.2 data (row 19) | L785–806 | `To these objects we attach several numerical data.` (L785); eq (9) at L799–803 | **EXACT** |
| X21 | Lemma 3.13(1) (row 20) | L836–840 | `Lemma 3.13. For every index 0 ≤ i ≤ r, we have / (1) µi (πi ) = 1/e(µi−1 ), µi (πi+1 ) = 1/e(µi ).` | **EXACT** |
| X22 | Def 1.8 (row 21) | L250–255 | `Definition 1.8. Take φ ∈ KP(µ) and λ ∈ Q>0 .` … `µ′ (g) = min0≤s {µ′ (gs φs )}.` | **EXACT** |
| X23 | Prop 1.9(2) (row 22) | L258–261 | `Proposition 1.9. …` / `(2) For a non-zero g ∈ K[x], µ(g) = µ′ (g) if and only if φ ∤µ g.` | **EXACT** |
| X24 | Thm 4.2 / eq (16) (row 23, **DESCRIPTIVE**) | L1028–1030 | `Theorem 4.2. Let g ∈ K[x] be a non-zero polynomial and let α = µ(g). Then, / Hµ (g) = ϕr (α)Rr,α (g)(yr ) = ϕr (g)Rr (g)(yr ).` | **EXACT** |
| X25 | Thm 6.6 (row 24, **DESCRIPTIVE**) | *(no layout pin declared)* | — | **UNPINNED by design** — record-interpretation status, per `.78` |
| X26 | N_i operator def | L871 | `Ni := Nµi−1 ,φi : K[x] −→ 2R ,   0 ≤ i ≤ r,` | **EXACT** |
| X27 | ψ_i / z_i defs + `yi := Hµi (γi )` | L855–863 | `yi := Hµi (γi ) := (xi )ei (pi )−hi ∈ ∆i` (L856); `zi ∈ Fi+1 , the image of yi under ∆i −→ ∆i+1` (L861); `ψi ∈ Fi [y], minimal polynomial of zi over Fi .` (L862) | **EXACT** |
| X28 | Def 3.1 + display (4) + optimality | L608–615 | `Definition 3.1. A valuation µ ∈ V is called inductive …` ; L613–614 `A chain of augmented valuations as in (4) is called a MacLane chain of length r of µ if / φi+1 6∼µi φi for all 1 ≤ i < r.` ; L615 `We say that (4) is an optimal MacLane chain of µ if deg φ1 < · · · < deg φr .` | **EXACT — and this is OPEN-CALL 1's evidence** |
| X29 | Lemma 2.4 (shear invariance) | L464 | `Lemma 2.4. Let H : R2 −→ R2 be the affine transformation H(x, y) = (x, y + λx). Then,` | **EXACT** |
| X30 | Def 3.16 | L916–923 | `Definition 3.16. For 0 ≤ i ≤ r, α ∈ Γi , and g = 0≤s as φsi the φi -expansion of g ∈ Pα (µi ),` | **EXACT** |
| X31 | Def 3.18 + j₀ | L994–1000 | `Definition 3.18. For g ∈ K[x], g 6= 0, let α = µi (g).` … `where j0 = ⌊s(g)/ei ⌋.` | **EXACT** |
| X32 | §6 header (r1's L1434→L1433 repair) | L1433 | `6. MacLane-Okutsu invariants of prime polynomials` | **EXACT — the repair is right** |
| X33 | FGMN §1 standing setting (CITE-SCOPE's pin) | L137 | `Let K be a field equipped with a discrete valuation v : K ∗ −→ Z, normalized so that` | **EXACT** |
| X34 | Def 6.1 (prime polynomial) | L1439–1440 | `Definition 6.1. Let P = P(Ov ) ⊂ Ov [x] be the set of all monic irreducible polynomials in / Ov [x]. We say that an element in P is a prime polynomial with respect to v.` | **EXACT — no separability restriction** |
| X35 | Lemma 6.2 + inseparability clause | L1447–1453 | `Lemma 6.2. Let F, F ′ ∈ P be two prime polynomials …` ; proof L1451–1453 carries `where Z(F ) is the multiset of` | **EXACT** |

**Total: 35 FGMN pins, 33 EXACT, 1 DESCRIPTIVE-unpinned by design (X25), 2 NEAR-MISS in line number only (X12, X13, one shared hedged citation).**

### 4.3 Repo-internal designation XREFs

`[TABLE]`

| ID | Target file — designation | count | Role |
|---|---|---:|---|
| R01 | `GENHN_PROOF_2026-08-08.md` L1419–1423, the (α) hole | 5-line span, exact | the charge this note discharges (`.03`, `.24`) |
| R02 | same — `[GENHN-TOW-1]` | 19 | the box family |
| R03 | same — `GENHN-T(b)′` | 12 | (B-1)'s supplier |
| R04 | same — `GENHN-2′` | 3 | slot separation / ladder grammar (N-3) |
| R05 | same — `T(b)′(i)` 4, `T(b)′(iii)` 1 | 4 / 1 | ladder normal form; grade-0 lift existence |
| R06 | `GENTOW1_PROOF_2026-08-09.md` — `COR GENTOW-1.1` | 4 | the (β) floor rider (`.57`) |
| R07 | same — `PROVED (S2)` | 1 (**NEAR-MISS NM-2** — see §4.6) | the item-(1) status row |
| R08 | `GENTOW5_PROOF_2026-08-09.md` — `GENTOW5-A1` | 7 | the ϑ_t dictionary GENTOW2 declines to identify (N-7) |
| R09 | same — `vartheta_t` at L214–219 | 6 | the ASCII form of A1's ϑ_t; **reciprocal orientation** (`.25`) |
| R10 | same — `post-PE6` | 1 (L815) | GENTOW5's matching dated note (`.83`) |
| R11 | same — `GENTOW2` | 73 | GENTOW5's consumption density |
| R12 | `GENTOW4_PROOF_2026-08-09.md` — `cocycle` | 6 sites | the η₂-cocycle finding cited at `.31` |
| R13 | `CODEX_TOWERRAT_2026-08-10.md` — `## S4. GENTOW2 — Codex findings + adjudication` | 1 (L252) | the ratification annex's home (`.85`) |
| R14 | same — `RATIFIED-WITH-ANNEX` for GENTOW2 | L56, L299 | the outcome |
| R15 | `T3_COCYCLE_TELESCOPE_2026-08-12.md` — `ABS-G2` | 3 | the absorption (`.92`) |
| R16 | same — `LEMMA COCYCLE-TELESCOPE` 6, `T3-BR` 3, `(BR1)` 5, `(BR5)` 5 | as listed | the port and its hypotheses |
| R17 | `runs/comp5/T3CC_output.log` — `GENTOW2-B″ — PASS` | 1 (line 1) | the S-2 consumption check, RUN and PASSED |
| R18 | `docs/SIMPLIFICATION_BLUEPRINT_2026-08-10.md` | exists, 38,971 B | the S-2 protocol (`.91`) |

### 4.4 PIN verification — commits, artifacts, hashes (rules 23, 34)

**All 23 cited commit hashes verified with `git cat-file -t`; all return `commit`:**
`08ec526` · `63091ce` · `c33f10e` · `61daa69` · `531c212` · `1e091d1` · `dd44d20` · `aff457c` · `d56e439` · `92ac16b` · `2f95be6` · `23def87` · `75923bc` · `a4b4495` · `0e816e8` · `d798529` · `deba21b` · `ade1727` · `72a3f29` · `891fd96` · `dfbc938` · `188b894` · `21293c8`. Plus `33f86204` (the STATEMENT_LEDGER's pin) ✓.

**One MISLABEL:** `531c212` is cited as “target blob” (`.65`) but is a commit (unique under `--disambiguate`). Booked, not reconciled (OPEN-CALL 4).

**All cited artifacts exist:**

`[TABLE]`

| Artifact | bytes | Cited at |
|---|---:|---|
| `docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt` | 150,185 | `.07`, all Q-tags |
| `docs/references/fgmn_residual_ideals_1305.0775v3.pdf` | 518,522 | `.49` — **md5 `da846c82f1fcb619cefb3feb8164191e` ✓, sha256 `651b0cef…f615f35` ✓, byte count ✓, all three recomputed** |
| `verification/openmath/gentow2_checks.py` | 14,629 | `.64` |
| `…/gentow2_checks_output.txt` | 1,350 | `.60` — verdict line matches declared 40/0 RED ✓ |
| `…/gentow2_checks_output_run2.txt` | 1,594 | `.62` — verdict line matches declared 41/0 GREEN ✓ |
| `…/gentow2_pe1_fresh.py` + `_output.txt` | 5,474 / 694 | `.30`, `.65` |
| `…/gentow2_pe2_fresh.py` + `_output.txt` | 6,416 / 796 | (the PE2-fresh f₃=3 cohort, `.39`(ii)) |
| `…/gentow2_pe3_fresh.py` + `_output.txt` | 9,092 / 1,756 | `.68` (50/0 GREEN) |
| `…/gentow2_r2_letter_probe.py` + `_output.txt` | 6,557 / 796 | `.67` |
| `…/gentow2_pe4_fresh.py` + `_output.txt` | 16,335 / 1,812 | `.28` (RED 62/9, kept as-is) |
| `…/gentow2_pe4_decode.py` + `_output.txt` | 4,853 / 348 | `.45` (GREEN 14/0) |
| `…/gentow2_pe5_fresh.py` + `_output.txt` | 17,436 / 4,272 | `.75` (GREEN 91/0) |
| `…/gentow2_pe6_fresh.py` + `_output.txt` + `_output_run2.txt` | 18,139 / 2,437 / 2,479 | `.82` (RED 68/1 kept, GREEN 68/0) |
| `lean/notes/openmath/GENTOW2_passPE1…PE6_report.md` | all 6 exist | `.65`–`.82` |
| `lean/notes/openmath/CODEX_TOWERRAT_2026-08-10.md` | exists | `.85` |
| `runs/comp5/T3CC_output.log` | 3,664 | `.92` |
| `docs/SIMPLIFICATION_BLUEPRINT_2026-08-10.md` | 38,971 | `.91` |

**Zero UNPINNED runs.** Every reported run names a runner file AND an output file, and every one of both exists — including the two RED runs (PE4 fresh, PE6 run-1) that the note kept committed rather than discarded.

**The four prefix byte-freezes: ALL FOUR RECOMPUTED, ALL FOUR EXACT** — see §1 FP-2 and units `.79`, `.84`, `.90`, `.93`.

**One AS-OF-PIN (rule 34):** `.49`'s leg (i), the 2026-08-09 bit-identity comparison against `https://arxiv.org/pdf/1305.0775v3`. Honest checkable evidence at its own time; not re-runnable offline now. The *local* half of the claim (md5/sha256/size) IS re-verified above.

### 4.5 Reverse-XREFs — consumers of GENTOW2 (rule 8)

`[TABLE]`

| ID | Consumer file — verified designation | count | Supplied edge |
|---|---|---:|---|
| RX01 | `T3_COCYCLE_TELESCOPE_2026-08-12.md` — `ABS-G2` | 3 | **absorption of B″'s conclusion** (`.92`); consumption check PASSED (R17) |
| RX02 | `T1_GAUGE_COCYCLE_2026-08-12.md` — `## A7 — GENTOW2` (L1921) | 1 | T1's absorption block: `SPAN PIN 1` = S5.1 letter formula, `SPAN PIN 2` = `LEMMA GENTOW2-B, md5=8a00bf44d21f87e878c0be6226b13b61` |
| RX03 | same — absorption-map rows (L1066–1068) | 3 rows | `S5.1 letter formula → C1 : **Verbatim** at level 2` · `S5.2 B-law → C3 : **Verbatim** after the explicit inverse orientation Θ=ϑ^{-1}` · `Factor-pattern invariance → C3 : **Verbatim**: ψ^{(w)}=w^fψ(y/w)` |
| RX04 | same — the r12 terminal-binding witness (L3865) | 1 | “the accepted `GENTOW2_PROOF_2026-08-09.md` witness tower, S2 dictionary, genre (2,1,4)→(2,1,2). There e(µ₂)=4, e₃=2, ν(Φ₂)=21/8, κ₃=21/2, and **u₃ = e₃κ₃ = 21**” — the S2 dictionary used to BIND T1's grade normalization |
| RX05 | same — battery check 10 (L4247) | 1 | “Instantiate a witness tower with e_{i+1} ∤ u_{i+1} — **the accepted GENTOW2 S2 tower at i = 2 (u₃ = 21, e₃ = 2, e(µ₂) = 4, e(µ₃) = 8)** is one” |
| RX06 | same — `(R-FGMN)` | 4 | scalar codomain of the i=2 residual read (DAG row `EFF.T1.05`) |
| RX07 | same — `GENTOW2-B\('\)` / `GENTOW2-B″` | 8 / 5 | the per-grade-unit supplier at i=2 (**NEAR-MISS NM-4** on the plain-text form) |
| RX08 | `T5_WFRAME_2026-08-12.md` — `GENTOW2-B\(^{\prime\prime}\)` | 8 (18 for `GENTOW2-B`) | the **unconditional i=2 rung** of LEMMA W-FRAME-LAW |
| RX09 | same — the acceptance-pass ledger item 2 (L982–1000) | 1 | **VERIFIED** against `L729–738 @ 33f86204`, md5-8 `d4c8b885`, with the raw-span `8978f8ba…` mechanism note — all three re-verified here |
| RX10 | same — ledger item 3 (L1004–1015) | 1 | GENTOW2-PE6's six-prime/four-frame `w` record |
| RX11 | same — the ϑ/Θ reconciliation (L991–993) | 1 | “B″'s single-argument ϑ(t) is this note's Θ₂(t), the **inverse-telescope orientation**” |
| RX12 | `GENTOW5_PROOF_2026-08-09.md` — `THEOREM GENTOW2-A` | 2 | admissibility quantifier + clause (d)'s i=2 node data (DAG row `EFF.GENTOW5.s1of2.06`) |
| RX13 | same — `GENTOW2` | 73 | the level-2 law consumed verbatim; `[GENTOW5-W(i)]` is its level-general analogue |
| RX14 | `GENTOW6_PROOF_2026-08-09.md` — `GENTOW2` | 13 | GENTOW6 S1 re-consumes FGMN through GENTOW2's dictionary (TIGHTNESS row I-3) |
| RX15 | `GRTJC_PROOF_2026-08-08.md` — `GENTOW2` | 1 | the FGMN-WELD cite family's shared two-leg method |
| RX16 | `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` — `### NS-12 — FGMN inventory consumed by GENTOW2/GENTOW5 ([Q1]–[Q10])` | 1 (L279) | **CITE-SCOPE resolution: `COVERS-ALL-O`** — see below and OPEN-CALL 3 |
| RX17 | `spec/HYPOTHESIS_LEDGER.md` — `HYP.145  GENTOW2 S6.1 rows 23–24` | 1 (L1143) | the DESCRIPTIVE-status fence, class `scope-fence` |
| RX18 | same — `HYP.66  \`WFRAME OPEN-3\`` | 1 (L524) | **gated on exactly row 23** |
| RX19 | `docs/TIGHTNESS_CENSUS_2026-08-11.md` — row `I-3` **FGMN-MAIN** | 1 (L47) | “the corpus's ONE load-bearing literature cite … consumed at GENTOW2-A (item 6α)”, status `cite-VERIFIED` |
| RX20 | same — row `I-4` **FGMN-WELD** | 1 (L48) | GRTJC's FGMN cites discharged **by GENTOW2's S6.1 two-leg method** |
| RX21 | same — row `O-6` **WFRAME OPEN-3** | 1 (L89) | “gated on GENTOW2 S6.1 row 23's two-leg elevation … GENTOW2 L1333–1345” |
| RX22 | same — row `O-14` **RIDER-DEBT** | 1 (L97) | “GENTOW2's 4 ratification hygiene minors (#17)” — **STALE**, they landed (`.85`–`.89`); see §8 item 2 |
| RX23 | `docs/STATEMENT_LEDGER_2026-08-10.md` L295–302 | 1 section | 4 statement rows with spans + md5-8s, at commit `33f86204`, grade ACCEPTED 2/2 |
| RX24 | `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` row 6 | 1 | `GENTOW2 \| CERTIFIED (batch-1 + RUN E discharge)` |
| RX25 | `docs/PROJECT_STATE.md` DATED APPEND #16 | 1 | “GENTOW1 + GENTOW2 BOTH ACCEPTED”; board “GENTOW2 ✓ (3 of 7 accepted)” |
| RX26 | `docs/in-progress/LEAN_SCOPING_consumption_map_2026-08-12.md` §T1 (c), §T3, §T5 | 3 | A7 GENTOW2 row; `(ABS-G2)`'s replacement scope; T5's I2/I3 instance records |
| RX27 | `spec/DAG.tsv` rows 347, 357, 858–860, 1401, 1487–1488, 1562, 1620 | 9 rows | the existing DAG edges into/out of `EXT:GENTOW2_PROOF_2026-08-09.md` — **all currently typed `EXT:`/`OPEN`, i.e. GENTOW2 has no `EFF.GENTOW2.*` node yet. This spec is what supplies it.** |

**THE CITE-SCOPE RESOLUTION (parent charge item (a)) — reading note, not a supersession.** `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` §NS-12 records the audit rows **Q4 A2** (“FGMN's ambient scope is not quoted”) and **Q4 B6** against GENTOW2/GENTOW5, and resolves them:

> “**Verdict:** **COVERS-ALL-O**, and it resolves both sub-questions the audit could not settle from
> the pasted record: (a) arbitrary discretely valued fields — yes, including `F_q((t))`; (b)
> inseparable prime polynomials such as `x^p − t` — **yes, `P` contains them and FGMN handles them
> explicitly**. *The GENTOW2 flag is discharged by pasting FGMN §1 + Def 6.1 + Lemma 6.2's
> inseparability clause into the faithfulness record.* No mathematics changes.”

and its action table row: `| Q4 A2 / B6 (GENTOW2, GENTOW5) | "FGMN's ambient scope is not quoted" | NS-12 | **paste [FGMN] §1 + Def 6.1 + Lemma 6.2** into the faithfulness record; no math change |`.

**Compiler verification of all three pasted sources:** X33 (§1 setting, L137) ✓, X34 (Def 6.1, L1439–1440 — “no separability restriction on `P`”) ✓, X35 (Lemma 6.2 + the inseparability clause in its proof, L1447–1453) ✓. **The resolution is sound and the paste is a one-edit obligation with no mathematical content.** It is a **reading note on `.53`(H-a)'s ℚ-narrowing**, NOT a supersession of any GENTOW2 unit: GENTOW2's own hypothesis audit is *narrower* than the source permits, which is the safe direction.

### 4.6 NEAR-MISS dispositions (rule 15)

**NM-1 — `Cor 4.4(1)` / `Cor 4.4(3)` cited as “L1089 region”.** `.35` writes “Cor 4.4(1) [L1089 region, PDF p.21]”. Item (1) is at **L1085**, item (3) at **L1088**; L1089 is item (4). Designation absent as written at the exact line; verified referent at `docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt:1085` under `(1) Ri,α (g)(yi ) = 0 if and only if …`, count 1, and at `:1088` under `(3) deg Ri,α (g) = ⌊s′ (g)/ei ⌋ …`, count 1. The note hedges with “region”, so this is a NEAR-MISS, not an OPEN-CALL, and **S6.1 row 5 is correct as written** (it says “Cor 4.4 (item 4 used)” and pins L1089, which is item 4).

**NM-2 — `item (1) PROVED (S2)` in GENTOW1.** `.57` quotes GENTOW-1's status table as `"item (1) PROVED (S2)" + "COR GENTOW-1.1 (the depth-3 floor rider (6)(β)) PROVED (S2.4)"`. `grep -cF 'item (1) PROVED (S2)'` on `GENTOW1_PROOF_2026-08-09.md` = **0**. Designation absent as written; verified referent at `GENTOW1_PROOF_2026-08-09.md:36` under `| (1) budgets + node | LEMMA GENTOW-1 | PROVED (S2) |` and `:37` under `| (1) rider: depth-3 floor (6)(beta) | COR GENTOW-1.1 | PROVED (S2.4) |`, `grep -cF 'PROVED (S2)'` = 1, `grep -cF 'COR GENTOW-1.1'` = 4. The note has compressed two table cells into one quoted phrase; referent unambiguous.

**NM-3 — PE6's grep census line pins.** `.81` pins the five consumption-list sites at body `L365/L431/L535/L938/L1248`. All five lines exist and all five carry consumption-list text, but **L431 and L535 both fall in the S5.1/honesty-box region** and their site↔quotation assignment is ambiguous (`.29`'s honesty-box list ends at body L431; `.34`'s clause-(4) bracket spans L529–535). The five *quotations* are unambiguous and each is mapped to a unit in this spec (`.29`, `.34`, `.72`, `.26`, `.54`). Line-attribution NEAR-MISS only; governing reading unaffected.

**NM-4 — LaTeX-escaped designations in the T-unit consumers.** `grep -cF 'LEMMA GENTOW2-B′'` on `T1_GAUGE_COCYCLE_2026-08-12.md` = **0**, because T1 writes `GENTOW2-B\('\)` (count 8) and `GENTOW2-B\(''\)` in T3 (count 8) and `GENTOW2-B\(^{\prime\prime}\)` in T5 (count 8). Designations absent as written in plain-text form; verified referents at those escaped strings, counts recorded in §4.5 RX07/RX08/R15. **Any mechanical DAG builder that greps the plain-text designations against the T-units will report zero edges where eight exist** — recorded in §8 as a build hazard.

---

## 5. Effective supply/consumption ledger

`[TABLE]`

| Source conclusion | Effective GENTOW2 supply | Surviving fence | Protocol status |
|---|---|---|---|
| **FGMN Thm 6.3 + Cor 6.4** (one-sidedness at every level; `µ(φᵢ) = v(φᵢ(θ))`; `R_{i−1}(F) = ψ_{i−1}^{ℓᵢ}`) | **THEOREM GENTOW2-A(b)(c)(d)(e)** (`.20`, `.23`) — item (6)(α) DISCHARGED | third stage only (N-8); optimal length-3 chain; clause (c) in the twist-aware `ψ₂^FGMN` form (`.89`); the `(β)` floor is a hypothesis (N-2) | **ACCEPTED 2/2; no append owed** (GENTOW2 is the consumer of the literature, not of a repo note) |
| FGMN Lemma 5.3(2) + Thm 5.8's degree-forcing schema + Lemma 1.11 + Cor 1.13 | **GENTOW2-A(a)**: `Φ₃ ∈ KP(ν)` and `Φ₃ ∈ P` (`.21`) | Thm 5.8 consumed as an argument-schema, never as a statement (`.13`) | ACCEPTED |
| FGMN Prop 5.7 (2)⇔(3) + eq (14) + Lemma 5.3(1) | `Φ₃ ≁_ν Φ₂` (`.22`), the hypothesis Cor 6.4 needs | requires BOTH arguments in `KP(ν)` — the r1 F4 repair | ACCEPTED |
| FGMN Cor 4.7(1)/(2) + eq (14) + Def 3.16/3.18 + Prop 1.9 + Lemma 3.17 + Cor 4.4 + Thm 4.8 + Prop 1.15 + Cor 3.3 + Def 1.8 + Lemma 3.13(1) + Def 3.12 + eq (9)/§3.2 + §3.3 | **the bridge**: LEMMA GENTOW2-B (`.25`), B′ (`.34`), B″ (`.43`), the LETTER FORMULA (`.37`), C-m1 (`.69`) | 22 consumed statements, each two-leg verified (`.50`); (B-2) **WITHDRAWN** and consumed nowhere | ACCEPTED |
| FGMN Cor 4.12's construction `g = φ_r^{e_rf} + g₀` | licenses the T(b)″ recipe's SHAPE as an FGMN instance (`.12`) | not a uniqueness claim | CITED |
| FGMN Thm 4.2 / eq (16) | **DESCRIPTIVE ONLY** — says what `w` IS (`.77` row 23) | **not consumed**; `w`'s unit-hood comes from Cor 4.4(1) instead | **DESCRIPTIVE — elevation owes the two-leg method** (HYP.145) |
| FGMN Thm 6.6 (+ Lemma 5.3(2)) | **RECORD-INTERPRETATION ONLY** — the “#primes = #distinct residual factors” verdict surface (`.77` row 24) | not a proof step; underwrites the T2 disclosure (`.60`) and the w-blindness sentence | **DESCRIPTIVE — no layout pin** |
| GENHN-2′ / LEMMA GENHN-T(b)′(ii) — the ladder-value identity + no-cancellation | **(B-1)** (`.27`), the shear's coefficient identity (`.06`), the recipe's digit lifts | accepted corpus, **not proved here** (N-3); hard `deg < D₂` scope fence, crossed by notation twice and re-fenced twice (`.35`, `.87`) | IMPORTED |
| T(b)′(i) ladder normal form; T(b)′(iii) grade-0 lift existence + leaf read | the LETTER FORMULA's repo side (`.38`); the `ẑ_d`/`ẑ` lifts in B′ and B″ (`.35`, `.44`) | repo-internal, **no FGMN contact** — the r2 F1 repair turns on exactly this | IMPORTED |
| COR GENTOW-1.1 (GENTOW-1) — the depth-3 node floor `κ₃ > e₂f₂u₂` | **NOT absorbed** — cited AS IN-FLIGHT (`.57`) and left as GENTOW2-B's explicit hypothesis | grade parenthetical is **STALE** (GENTOW-1 is ACCEPTED) | **CITED, not absorbed** |
| GENTOW5-A1's `ϑ_t` dictionary | **NOT consumed** (N-7); the coincidence is explicitly unadjudicated (`.46`(d)) | downstream notes HAVE adjudicated it, as an **inverse** — OPEN-CALL 2 | **NON-IMPORT — with a live downstream tension** |
| — (GENTOW2's own supply going out) | **LEMMA GENTOW2-B″ display (6)** absorbed by T3 as `(ABS-G2)` (`.92`) | **conclusion only**; the read package stays here; **dual-cite** | **ABSORBED, consumption check RUN and PASSED** (R17) |
| — | **LEMMA GENTOW2-B′(3) + B″(6)** consumed by T1 (A7), T5 (I2), GENTOW5 | inverse orientation `Θ = ϑ^{−1}` must be carried (`.25`) | LIVE |
| — | **the S2 tower dictionary** consumed by T1's r12 terminal binding + battery check 10 (RX04, RX05) | `u₃ = 21, e₃ = 2, e(µ₂) = 4, e(µ₃) = 8`, span identities at `.05` | LIVE |
| — | **GENTOW2-PE6's `w` record** consumed by T5 (I3) and GENTOW5's S3(a) bracket | measurement, not derivation (`.83`) | LIVE |
| — | **S6.1's two-leg method** consumed as a *methodology* by GRTJC/WELDMASTER's FGMN-WELD discharge (RX20) | the method, not the rows | LIVE |

---

## 6. TEETH inverse inventory (rules 6, 16, 20, 27, 31)

Disposition vocabulary: `{Lean theorem, executable regression, signed non-applicability, PROOF-ONLY, preregistration, AUDIT}`, with the disclosure sub-labels `{signed vacuity disclosure, disclosed non-repair, accepted-with-decorrelation-supplied, stale self-description}` and the AUDIT sub-labels `{decorrelated-model audit, in-house hostile pass, transfer audit, arithmetic recount, hostile-pass certification}`.

Unlike T4, **GENTOW2 owns its machine evidence**: five sealed runners plus a decode probe, all first-party, all present in the tree.

`[TABLE]`

| # | Battery row / instrument (source wording, abbreviated) | Guarded EFF units | Disposition |
|---|---|---|---|
| 1 | `P-W1` — Φ′-pins {0:10, 2:7, 4:0}; one side (4,0)–(0,10) slope 5/2 = κ₂; on-side J={0,4}=2·supp(ψ₂); Φ₂-pins {0:21,2:0}; resultants (4,10,21); PARI [(8,1)] | `.05`, `.06`, `.20`(b)(c), `.23` | executable regression (A+B routes, GREEN) |
| 2 | `P-W2` — the FR3 uncancelled-carry key, resultants (4,10,23) | `.20`(b)(c), `.23`, `.64` | executable regression |
| 3 | `P-W3/4/5` — the three SUPP-C n=16 leaves; PARI sig₂ {(16,1)}/{(16,1)}/{(8,1),(8,1)} | `.20`(a), `.64` | executable regression |
| 4 | `P-N1` — f₂=2 tower, K₂=F₄; on-side J={0,2,4}=supp(ψ₂²)=y⁴+y²+1 | `.20`(c), `.23`, `.63` | executable regression |
| 5 | `P-N2` — the f₃≥2 K₂-digit branch, first machine witness anywhere; residual y²+y+1=ψ₃ | `.25`, `.63`, `.64` | executable regression |
| 6 | `TOOTH-T1` — a floor-breaching recipe (u₃=9<10=e₂f₂u₂) must be flagged NOT one-sided | `.25` (the (β) hypothesis), `.55`(ii), `.57`, `.60` | **executable regression, FIRED** — machine-couples (α) to the (β) floor |
| 7 | `TOOTH-T2` — a reducible-residual recipe must factor [(4,1),(4,1)] | `.60`, `.77` row 24 | **instrument-audit / disclosed failed design** — the prediction mis-read Lemma 5.3; kept as a record row, RED as sealed |
| 8 | `TOOTH-T2′` — at N1, ψ₂-split residual ⟹ must factor [(2,2),(2,2)] | `.20`(hypothesis (ii)'s irreducibility), `.61` | **executable regression, FIRED** + `hostile-pass certification`: the polygon side alone certifies nothing |
| 9 | r2 letter-live probe LP1 — the LETTER FORMULA at f₁=2 | `.33`, `.37`, `.38`, `.39`, `.67`, `.89` | **executable regression, FIRED (η₂ ≠ z₂)**, GREEN 21/0 first-run-under-seal |
| 10 | PE3 fresh route — first `z₂ ≠ 1` letter-live contacts, p=3/F₉, teeth both frames | `.37`, `.38`, `.68` | executable regression, GREEN 50/0 |
| 11 | PE4 fresh route LD1/LD2/LD3 — the first letters × depth contact | `.28`, `.31`, `.71` | **the tooth that bit** — RED 62/9, **(B-2) WITHDRAWN**; `in-house hostile pass` |
| 12 | PE4 A-route at the same contact | `.20`, `.23`, `.24` | **`hostile-pass certification`** — 27/27 GREEN, “THEOREM GENTOW2-A UNTOUCHED” |
| 13 | PE4 decode probe — COC / MULT / MP pins | `.41`, `.42`, `.43`, `.44`, `.45` | executable regression, GREEN 14/0 first-run-under-seal |
| 14 | PE5 fresh route — first γ₂-live contact, tower GB; direct θ(0)=z₂²; teeth GA1/GA2; top-slot pin GA4; first e₃=2 cocycle-live frame GA3 | `.41`, `.43`, `.44`, `.75` | executable regression, GREEN 91/0 |
| 15 | PE6 fresh route — the corpus's FIRST `w` measurement; two discrimination pairs | `.40`, `.74`, `.82`, `.83` | executable regression, GREEN 68/0 (run-1 RED 68/1 disclosed and committed); `hostile-pass certification` |
| 16 | The S6.1 two-leg provenance method (22 rows) | `.07`, `.48`, `.49`, `.50`, `.51`, `.52` | **AUDIT — `transfer audit`** (r1 F1: a verification done for another note's cite set had been transferred) + compile-time re-verification of all 22 layout legs |
| 17 | The `[r2]` letter-blindness scope disclosure | `.30`, `.39`(ii) | **`signed vacuity disclosure`** — 13 witnesses all at letter-dead geography; PE4 cashed it |
| 18 | PE1 F3's F₄ counter-instance (`y²+ωy+1` irreducible, its ω-twist has root 1) | `.31` | **Lean theorem** (a constructed counterexample; recomputed exact here) |
| 19 | The m1/[m-1] consumption-list unification's named failure mode | `.76`, `.81` | **`preregistration`** — a falsifier against future edits; no run |
| 20 | The four prefix byte-freezes | `.79`, `.84`, `.90`, `.93` | **executable regression** — all four recomputed EXACT at compile time |
| 21 | The Codex TOWERRAT-R3 ratification (4 MINOR on a frozen accepted note) | `.85`, `.86`, `.87`, `.88`, `.89` | **AUDIT — `decorrelated-model audit`**; found a truncated display and a symbol overload six in-house passes missed |
| 22 | The S-2 consumption check (`runs/comp5/T3CC_output.log`) | `.43`, `.92` | executable regression, **PASS** |
| 23 | `statement_ledger.py --check` post-campaign | `.20`, `.25`, `.34`, `.43` | executable regression — “178 baseline statements; 0 changed, 0 deleted, 2 added … GREEN: every baseline statement byte-stable (normalized)” |

**Zero-orphan check.** The battery declares 7 preregistered prediction families + 2 teeth (rows 1–8), and the arc adds 7 fresh/decode routes (rows 9–15) plus 8 non-executable instruments (rows 16–23). **23 of 23 instruments are mapped; 0 orphan rows.** Cross-check against the note's own tallies: the sealed run's 40 scored checks and the re-run's 41 both reconcile (`.62`); the fresh-route figures 20/0 (PE1), 21/0 (r2), 50/0 (PE3), 62/9 RED (PE4), 14/0 (decode), 91/0 (PE5), 68/0 (PE6) each appear in exactly one row.

**PROOF-ONLY rows (rule 16).** `.35` (B′'s repaired h-step) and `.36` (its worked N1 trace) carry no battery; their interesting content is the proof, and the note's own coverage sentence is quoted at `.35`: “the e₃ = 1 unit-q corner the report flagged as unfenced is thereby CLOSED, not fenced.” Likewise `.44` (B″'s four-step proof) is guarded by row 22's absorption check rather than by a battery of its own.

**Reverse direction — units with no tooth.** `.01`, `.02`, `.03`, `.32`, `.47`, `.54`, `.56`, `.58`, `.59`, `.65`, `.66`, `.70`, `.73`, `.74`, `.78`, `.83`, `.85`, `.91` are record, fence, or provenance units and carry no instrument of their own; they are guarded by §7. **Every other unit (75 of 93) appears in at least one row above.**

---

## 7. Acceptance and evidence fence

The acceptance bar is the campaign's standing one and `.80` supplies it: **two consecutive clean fresh-context passes** — PE5 @ `75923bc` (0C/0G/2m) and PE6 @ `deba21b` (0C/0G/1m). The PE3 clean was **spent** at the PE4 reset and is not banked; the note says so and the counter chain in `.80` records all six layers.

**What the grade does NOT cover** (rule 35, the acceptance-scope enumeration — a consumer must carry all three):

1. **Third stage only.** `.58`: depth ≥ 4 is “NOT claimed here”; the level-uniformity remark is conditional on level-r analogues of (B-1)/(B-2), and **(B-2) is withdrawn** (`.28`), so the level-general law is `[GENTOW5-W(i)]`'s conditional territory, not GENTOW2's.
2. **The (β) floor is a hypothesis.** `.25` makes `κ₃ > e₂f₂u₂` “an explicit HYPOTHESIS”; `.55`(ii) says the cite does not supply it; `.57` routes it to COR GENTOW-1.1. TOOTH T1 exists to make a breach visible.
3. **S6.1 rows 23–24 are DESCRIPTIVE.** `.78`; HYP.145; HYP.66 is gated on exactly row 23.

**Evidence posture — the opposite of T4's.** GENTOW2 contributes **first-party machine evidence**: five sealed runners plus a decode probe, all present, including **two RED runs kept as committed** (`gentow2_pe4_fresh_output.txt`, `gentow2_pe6_fresh_output.txt`). Nothing in this specification cites inherited evidence from another note. The one *methodological* export is S6.1's two-leg method, which GRTJC/WELDMASTER's FGMN-WELD discharge reuses (RX20).

**Decorrelation.** The six in-house passes are not identified by model arm in the note. What IS decorrelated is `.85` — the Codex ratification on the frozen accepted note, `RATIFIED-WITH-ANNEX`, 4 MINOR, each adjudicated REAL. Disposition: **`accepted-with-decorrelation-supplied`** (rule 20). And the strongest single evidence item is `.24`/`.71`: the pass that BROKE (B-2) simultaneously re-derived GENTOW2-A clean at 27/27.

**The literature cite's own status.** `docs/TIGHTNESS_CENSUS_2026-08-11.md` row I-3 marks FGMN-MAIN `cite-VERIFIED` and records the stage-two obligation: “CITE — already verified; stage two owes the declaration: axiom + AXIOM_FAITHFULNESS entry + semantic-guardian pass (blueprint §4 names it the one new axiom candidate).” This is a process debt, not a mathematical one (§8 item 1).

---

## 8. Deferred reconciliation obligations

Named cross-spec bookkeeping. None of these is an unresolved GENTOW2 scope judgment.

1. **The FGMN axiom declaration — FOR-stage-two.** GENTOW2-A is the corpus's single load-bearing literature consumption. `docs/TIGHTNESS_CENSUS_2026-08-11.md` row I-3 records that stage two owes an axiom declaration + an `AXIOM_FAITHFULNESS.md` entry + a semantic-guardian pass, and the repo's axiom policy (project CLAUDE.md) requires all three before any new axiom lands. GENTOW2's S6 faithfulness paragraph (`.47`–`.55`) is written to that standard already; what is owed is the *declaration*, not more verification. **Action item.**

2. **`docs/TIGHTNESS_CENSUS_2026-08-11.md` row O-14 is STALE on GENTOW2 — FOR-0b.** RX22 lists “GENTOW2's 4 ratification hygiene minors (#17)” as outstanding display debt, with the caveat “Some may have landed in B-wave folds; not re-verified here.” **They landed**: the TOWERRAT-R3 annex at note L1427–1498 carries all four (`.86`–`.89`), pure-append verified by prefix md5 `e27b97f2` at 86,321 bytes (`.90`), commit `21293c8`. Per template rule 10 this was checked against the note's FULL append chain, not by re-grepping a pinned sentence. **Census refresh owed.**

3. **The `deg < D₂` notation hazard — FOR-formalization.** Three separate defects in this note are the same species: a `digit`/`B-1` scope fence crossed by notation. PE2 F2 (`.35`, B′'s h-step, `deg` reaching `m₃`), TOWERRAT R3-2 (`.87`, `digit(G)` at `d ≥ 2`), and, latent, the (R-repo) definition's own scope sentence (`.33`). A Lean formalization should make `digit`'s domain a typed subobject rather than a side condition, or the same defect will recur a fourth time. **Design note, not an open call.**

4. **Cross-note designation escaping — FOR-DAG-build.** NM-4: every T-unit consumer writes `GENTOW2-B′`/`GENTOW2-B″` in LaTeX-escaped form (`GENTOW2-B\('\)`, `GENTOW2-B\(''\)`, `GENTOW2-B\(^{\prime\prime}\)`). A mechanical DAG builder greping the plain-text designations will report **zero** edges where **24** exist (8 in T1, 8 in T3, 8 in T5). `spec/DAG.tsv` currently carries GENTOW2 only as `EXT:` nodes (RX27). **Build-tooling note for the merge/DAG stage.**

5. **GENTOW-1's grade parenthetical inside a frozen sentence — FOR-0b.** `.57` and `.74` describe COR GENTOW-1.1 as “in-flight”, which `docs/PROJECT_STATE.md` DATED APPEND #16 falsifies (GENTOW1 ACCEPTED, same day). Both sites are byte-frozen and neither has a dated bracket. The corpus's own remedy pattern exists — the `w`-disclosure brackets (`.82`) — and was not applied here. Whether to add a dated bracket is a note-owner decision, not a compiler decision; the compiler tags both units `STALE-SELF-DESCRIPTION`.

---

## 9. Self-audit

### Resolved compilation calls

- **The effective-text rule is QUOTED, not derived** — a material difference from EFF-T4. Body frozen at post-PE3; nine dated appends supersede by governing reading; r1/r2/r3 are in-place body rewrites, so there is no round replay.
- **(B-2) is classified `withdrawal`, not `replacement`** (rule 29). The note says twice that it is “consumed NOWHERE”. Filing it as a replacement would leave a merge consuming a withdrawn input.
- **The consumption-list unification is a two-layer CHAIN with a single TERMINAL** — `.76` (four sites) → `.81` (five sites), TERMINAL `.81`. Five byte-frozen sentences disagree; one governing reading resolves all five; B′(4) has exactly one surviving consumer. A chapter cut that installs `.76` alone leaves `.54` unresolved.
- **The counter chain has six layers** and is recorded in full at `.80`: 0/2 → 0/2 → 0/2 → 1/2 → **0/2 RESET** → 1/2 → 2/2.
- **Two TERMINALs by consumer class** (rule 30) appear twice: `.70` (grade consumers → `.80`; arc-history consumers → `.70`) and `.31` (prescription consumers → `.25`; r1-correction-history consumers → `.31`).
- **`(ABS-G2)` is a dual-cite, not a supersession** — both display (6) and T3's `(ABS-G2)` are live and authoritative, per the note's own sentence. The DAG must carry both edges.
- **The ϑ/Θ orientation is compiled with its exact statements at every site** (`.25`, `.41`, `.43`, `.92`), and the four-way table at `.25` resolves GENTOW2's single-argument `ϑ(t)` against T1's `Θ_i(t) = ϑ_{i,f_{i+1}−t}^{−1}`, T3's `Θ_N(s;q) = ϑ_N(s;q)^{−1}`, and GENTOW5-A1's reciprocal `vartheta_t`. T5's acceptance-pass verdict on this reconciliation (**VERIFIED**) was re-checked at the byte level.
- **The S2 tower dictionary is emitted with span identities and a fresh arithmetic audit** (`.05`): `e(µ₂) = e₁e₂ = 4`, `e(µ₃) = e₃e(µ₂) = 8`, `κ₃ = e(µ₂)ν(Φ₂) = 21/2`, `u₃ = e₃κ₃ = 21`, `dv₂(Φ₂^{e₃}) = 4·2·21/8 = 21 = u₃`, `e₃ = denom(e(µ₂)λ₃) = 2` with `λ₃ = 1/8`. Four independent occurrences of `u₃ = 21` and no disagreement.
- **All four prefix byte-freezes recomputed EXACT**, including BF-4 whose byte count (90,326) the note omits and the compiler recovered by exhaustive prefix scan.
- **The [Q1]–[Q10] inventory is compiled AS THE NOTE STATES IT**, with the CITE-SCOPE resolution recorded as a reading note (§4.5) and its label mismatch booked as OPEN-CALL 3.
- **[Q6]'s attribution was independently confirmed** against the source: the `Theorem 4.8.` token at the head of L1296 is a split cross-reference, and the enclosing statement is Theorem 5.8 at L1289–1290. The note is right.
- **Every arithmetic claim the note makes was recomputed fresh**, not read off its labels: the shear witness, the N1 worked trace, the LP1 γ-calculus lattice split, the F₄ counter-instance, the `ψ₃^{(w)}` substitution, the `ϑ(0)w² = 1 = ϑ(1)w` impossibility, the witness censuses (10/13), the S6.1 row counts (13→16→19→22→24), the battery counts (40→41), and the `x⁶−8` factorization. **Zero arithmetic defects found in the note.**
- **One source-level MINOR defect was BOOKED, not silently reconciled** (rule 39): the `531c212` blob/commit mislabel (OPEN-CALL 4). **Two further candidates were raised by a first compiler pass and then RETRACTED by this specification's own mechanical audits** — the “B-side” wording at `.67` (the note reads “A-side”, a compiler misquotation caught by the verbatim-containment audit) and the “(linear) minimal polynomials” clause at `.89` (the note is right; the first pass computed minimal polynomials over the wrong residue field). Both retractions are recorded at their units rather than erased.
- **No table was prosified.** The S2 dictionary, S6.1's 22 rows, S6.1's appended rows 23–24, the supersession chains, and every ledger are emitted as tables. The two ASCII displays (the FGMN chain, the ϑ-factorization) are emitted verbatim as displays.

### OPEN-CALLS

**OPEN-CALL 1 — R3-1's strike is CONSERVATIVE, and the struck clause was source-accurate. FOR-0b (note owner).**

TOWERRAT-R3-1 (`.86`) **STRUCK** the (H-b) clause “— and Cor 6.4 needs only 'a MacLane chain', not optimality.” on the ground that “[Q10] hypothesizes a chain 'as in (4)', and this note's own S2 dictionary identifies display (4) with the OPTIMAL MacLane chain”.

Read against the source, the struck clause was **true**. FGMN Definition 3.1, layout L613–615 (XREF X28), distinguishes the two notions explicitly:

> “A chain of augmented valuations as in (4) is called a MacLane chain of length r of µ if
> φi+1 6∼µi φi for all 1 ≤ i < r.
> We say that (4) is an optimal MacLane chain of µ if deg φ1 < · · · < deg φr .”

So “a MacLane chain of length r as in (4)” in Cor 6.4 (X10) does NOT carry optimality — optimality is a further, separately named property. R3-1's argument is about **this note's own S2 dictionary**, which happens to instantiate display (4) with an optimal chain; that is an internal-consistency observation, not a citation-accuracy finding.

**Disposition:** the strike is recorded as **GOVERNING** (a `withdrawal` — the compiler does not overrule a landed annex), and its effect is nil: `.19` declares the chain optimal, `.53`'s license is the preceding properness derivation, and `.23` consumes exactly that chain. **Nothing weakens.** But a chapter cut that wants Cor 6.4 at *non-optimal* chains — e.g. a depth-≥4 or refinement setting where degrees do not strictly grow — will find GENTOW2 has withdrawn the only sentence that said the citation permits it, and will have to re-derive the permission from FGMN Def 3.1 itself. Whether to restore the clause with a source pin is a note-owner decision.

**OPEN-CALL 2 — GENTOW2 declines to adjudicate ϑ ↔ GENTOW5-A1's ϑ_t; three downstream notes have since adjudicated it, as an INVERSE. FOR-0b / merge stage.**

`.46`(d) and `.40` both state, as a standing NON-IMPORT (N-7): “Whether ϑ literally coincides with GENTOW5-A1's ϑ_t (that note's arc is in flight) is left to that arc — nothing here consumes the correspondence.”

Since the freeze, the correspondence has been settled downstream and it is **not** a coincidence:

- **T1** `(C3-Theta)`: `Θ_i(t) = ϑ_{i,f_{i+1}−t}^{−1} = res(n̂_i((f_{i+1}−t)u_{i+1}) / n̂_i(u_{i+1})^{f_{i+1}−t})` — the right-hand side is GENTOW2's `ϑ(t)` at `i = 2`, so **GENTOW2's ϑ = T1's Θ₂ = the INVERSE of T1's two-index ϑ**.
- **T3** `(T1-THETA)`: `Θ_N(s;q) := ϑ_N(s;q)^{−1}`, and `(ABS-G2)`: `ϑ_{G2}(t) := res(n̂₂(su₃)/n̂₂(u₃)^s) = Θ_N(s;u₃)`.
- **T5** L991–993: “B″'s single-argument ϑ(t) is this note's Θ₂(t), the **inverse-telescope orientation**.”
- **GENTOW5-A1** itself, L214–215: `theta_t := [n2hat(lam)(x0)]^t * [n2hat(t*lam)(x0)]^{-1} = iota(vartheta_t)` — i.e. `res(n̂₂(λ)^t/n̂₂(tλ))`, the **reciprocal** of GENTOW2's `ϑ` at `λ = u₃`, `t = f₃−t'`.

The four definitions are consistent and the relation is exactly `ϑ_{GENTOW2}(t) = vartheta_{A1,\,f₃−t}^{-1}`. **GENTOW2's frozen text is not wrong** — it declines to consume a correspondence, which remains a safe posture. But a chapter cut that reads GENTOW2's N-7 as “the relation is unknown” will be reading a fence that the corpus has since walked past, and — worse — a formalization that carries GENTOW2's `ϑ` and GENTOW5-A1's `vartheta_t` under one name **in the same orientation** will have an inverse-sign error that no GENTOW2 tooth can catch, because GENTOW2 tests only its own orientation. **This is the single highest-value merge-stage edge in the note.** Proposed disposition: the DAG carries an explicit orientation-typed edge `GENTOW2.ϑ = T1.Θ₂ = T3.Θ_N(·;u₃) = (GENTOW5-A1.vartheta)^{−1}`, and any consumer node is annotated with which orientation it takes. Needs the note owner (or the merge run) to install; the compiler will not silently create a consumption edge the source note fences off.

**OPEN-CALL 3 — `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` §NS-12 mislabels two Q-tags. FOR-0d (supplier-finding against another document).**

NS-12 restates GENTOW2's inventory as:

> “`GENTOW2_PROOF_2026-08-09.md` §S3 pins [Q1] Lemma 1.11, [Q2] Cor 1.13,
> [Q4] Prop 1.12/Thm 3.11, [Q6] Lemma 5.3, [Q8] Cor 4.7(1)+eq (14), [Q9] **Theorem 6.3**,
> [Q10] **Corollary 6.4**; plus Cor 5.4, Cor 5.6, Thm 5.8, Def 3.16.”

Against the note (§4.1): `[Q4]` is **Lemma 5.3**, not “Prop 1.12/Thm 3.11”; `[Q6]` is **Theorem 5.8's proof display**, not “Lemma 5.3”; and eq (14) rides `[Q7]` (Prop 5.7), not `[Q8]`. Also, `Cor 5.4` appears in NS-12's “plus” list but is consumed nowhere in GENTOW2 (`grep -c 'Cor 5.4'` on the note = 0), while `Thm 5.8` and `Def 3.16` are indeed used and `Cor 5.6` is S6.1 row 10.

**None of this affects NS-12's verdict** — `COVERS-ALL-O` rests on FGMN §1 + Def 6.1 + Lemma 6.2, all three of which the compiler verified (X33–X35), and the note's actual inventory is *narrower* than NS-12's restatement in the safe direction. But NS-12's Q-tag map is what a downstream reader will use to find the quotes, and two of its seven entries point at the wrong statement. **This spec compiles the inventory as the NOTE states it** (per the parent charge) and books NS-12's map as a defect against that document. Proposed disposition: correct NS-12's tag map to `[Q3] Def 5.2, [Q4] Lemma 5.3, [Q5] Cor 4.12, [Q6] Thm 5.8 (proof display), [Q7] Prop 5.7 + eq (14), [Q8] Cor 4.7`, and drop `Cor 5.4`. One-line edit; no mathematics changes. Needs the CITE-SCOPE document's owner.

**OPEN-CALL 4 — ONE MINOR source defect, booked per rule 39; TWO first-pass candidates RETRACTED by this specification's own audits. FOR-0b (note owner).**

The surviving defect is quoted and diagnosed; it is not corrected here. The two retractions are stated in full, because a compilation that reports only its surviving findings hides the rate at which its own findings are wrong.

(a) **`.65` — a commit called a blob.** “Verifier: GENTOW2_passPE1_report.md (commit 61daa69; **target blob at 531c212**).” `git cat-file -t 531c212` = `commit`; `git rev-parse --disambiguate=531c212` returns exactly one object, the commit `531c212f6c8c7faf91102a14148283592b985f13`. The object exists and is unambiguous; only the type-name is wrong. Consequence: a pin-checker written to `git cat-file blob` will fail on a hash that is fine.

**(b) RETRACTED — `.67`'s “B-side”.** A first pass transcribed the clause as “on the B-side, PARI …” and booked the doubled side-label as a source defect. The mechanical verbatim-containment audit (below) flagged the segment as non-matching, and the source at body L1148 reads **“on the A-side, PARI factorpadic/idealprimedec/nfeltval/ nfmodpr on the B-side”** — correct against the note's own oracle convention. **The defect was the compiler's, not the note's.** The quotation at `.67` is corrected and the retraction is recorded there.

**(c) RETRACTED — `.89`'s “(linear)”.** A first pass computed `minpoly(z₁)` over the two-element field, got `y²+y+1`, and booked R3-4's “(linear) minimal polynomials” as an imprecision. Wrong residue field: FGMN's `ψ_i ∈ F_i[y]` is the minimal polynomial of `z_i` **over `F_i`** (X27, layout L862), and at LP1 `ψ₁ = y²+y+1` makes `F₂ = F₄`, in which both `z₂ = 1` and `η₂ = z₁` sit. Over `F₂ = F₄` the two minimal polynomials are `y + 1` and `y + z₁` — **both linear, both distinct**. R3-4 is exactly right. Retraction recorded at `.89`.

**Proposed disposition for (a):** a minors-only dated append changing “target blob at 531c212” to “target commit 531c212”. No display, no statement, no count, and no grade is touched. A compiler may not normalize a quoted source sentence, so it is booked here instead. **(b) and (c) need nothing** — the note was right both times.

### Fidelity audit (compile-time, mechanical)

**The verbatim-containment instrument, and what it caught.** A script extracted every maximal blockquote run from this specification (**112 segments**) and tested each for containment in the source note under a normalization removing only presentational reflow (line wrapping, blockquote `>` prefixes, curly-quote/apostrophe forms). **105 segments are verbatim in `GENTOW2_PROOF_2026-08-09.md`.** The remaining **7** resolve as:

- **3 explicitly ellipsis-compressed quotations** — §1's S7 residue block, `.65`'s S9 preamble+findings, `.66`'s S10 preamble+findings. Each carries a visible `…` or a bracketed pointer at the elision, and each component was separately re-tested and found verbatim (e.g. `.65`'s F4 bullet, `.66`'s F3 bullet, S7's (α) bullet — all OK).
- **4 cross-file quotations**, each independently verified in its own file: `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md`'s NS-12 verdict and its `[Q1]–[Q10]` pin list (both OK), the same document's Q4 A2/B6 action row (OK), and FGMN Def 3.1 at layout L613–615 (OK).
- **2 `[TRANSCRIBED from LaTeX]` displays** at `.92`, marked as such with the source bytes reproduced alongside the Unicode rendering (T3's `ϑ_G2` definition and its `(T1-THETA)` box). These are **not** counted as quotations and are not claimed to be byte-exact.

**The instrument earned its place: it caught one compiler misquotation.** `.67`'s LP1 clause was first transcribed as “on the B-side, PARI …”; the audit flagged the segment, the source read “on the A-side”, and a would-be source defect was retracted (OPEN-CALL 4(b)). A second finding — R3-4's “(linear) minimal polynomials” — was retracted by the residue-field re-derivation at `.89` (OPEN-CALL 4(c)). **Two of three first-pass source defects were the compiler's own errors; both retractions are recorded at their units and in §9 rather than erased.**

**Field completeness across the 93 units.** `FORM:` 93/93 · `DERIVATION:` 93/93 · `CONDITIONALITY` 93/93 (95 occurrences, 2 being sub-headed) · `RESOLUTION TRACE:` 93/93 · `TEETH:` 87 (the 6 without are §1/§2 cross-referenced fences) · `SUPERSESSION KIND:` 21 · `CHAIN` 9 · `TARGETS` 12 · `SERIES:` 13 · `[TABLE]` 28 · `ARITHMETIC AUDIT` 24 · `AUDIT (rule …)` dispositions 35.

**Orientation fidelity, checked specifically**, because it is this note's principal export: every occurrence of `ϑ`, `Θ`, `u(β_t)`, `w`, `ψ₃^{(w)}`, and `P(y)` was compared against the source display and against the three consumer notes' boxes. `u(β_t) = ϑ(t)·w^{f₃−t}` appears in the same orientation in GENTOW2's (6), T1's `(C3-B-law)`, T3's `(ABS-G2)`, and T5's ledger item 2. **Zero orientation drift.** No quantifier, index, inequality, direction, slot index, grade, byte count, hash, or scope was altered anywhere.

**Pins.** 35 FGMN layout pins, 18 repo-internal designation XREFs, 27 reverse-XREFs, 24 commit hashes, 20 artifact files, 4 prefix-md5s, and 1 PDF md5 + sha256 + byte count — **all verified at compile time**, with line numbers and counts re-derived independently of the note's own tables. **4 NEAR-MISS dispositions** recorded (§4.6); **0 invented designations**; **0 unverifiable designations emitted as clean XREFs**; **0 UNPINNED runs**.

**Arithmetic.** 24 `ARITHMETIC AUDIT` blocks, every number recomputed fresh rather than read off the note's labels: the S2 span identities (`u₃ = 21`, `e(µ₃) = 8`, `λ₃ = 1/8`), the shear witness map, the N1 worked trace (12 checks), the LP1 γ-calculus exponent-lattice split, the F₄ counter-instance, the `ψ₃^{(w)}` substitution identity, the `ϑ(0)w² = 1 = ϑ(1)w` impossibility, the witness censuses (10 and 13), the S6.1 row-count ladder (13→16→19→22→24), the battery counts (40→41), the `x⁶−8` factorization, and the four byte-freeze prefixes. **Zero arithmetic defects found in the note.**

**No `[TABLE]` was prosified.** **`[ASSEMBLED]` count: 0** — every canonical statement is a verbatim source quotation.


### Exhaustive residual judgment list

There are no other unresolved GENTOW2 mathematical or scope judgments. The four standing fences — depth-≥4 non-extension, the (β) floor hypothesis, `w`'s uncomputed closed form, and rows 23–24's DESCRIPTIVE status — are the note's own displayed scope statements (`.58`, `.25`, `.83`, `.78`), not compiler ambiguities. The FGMN axiom declaration, the stale census row, the `deg < D₂` notation hazard, the designation-escaping build hazard, and GENTOW-1's stale grade parenthetical are classified in §8 as bookkeeping. The four OPEN-CALLs above are the complete list of items needing a human decision.

EFF-GENTOW2 COMPILED: 93 statements / 80 xrefs verified (35 FGMN + 18 repo-internal + 27 reverse-consumer) + 51 pins (24 commits, 20 artifacts, 4 prefix-md5s, 3 PDF hashes) / 4 NEAR-MISS / 4 open calls
