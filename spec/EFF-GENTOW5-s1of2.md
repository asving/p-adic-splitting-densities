# EFF-GENTOW5-s1of2 — CANONICAL EFFECTIVE-SPECIFICATION SHARD

**COMPILED-BY: gpt-5.6-sol high (2026-08-18), compiler/cross-read replacement of the 2026-08-14 opus draft.**

## 1. Shard header

**Source note:** `lean/notes/openmath/GENTOW5_PROOF_2026-08-09.md`

**HOME range:** source lines 1–1474 inclusive (front matter + CHARGE + SOURCES + STATUS TABLE + §§S0–S7). Later text is used only to resolve material homed in that range.

**HEAD blob hash:** `00a4c7e80cfd652bc4416edb476d44ae6ca0a420` (fresh `git hash-object`; source clean in the working tree; last touched by commit `ddfc6b61`, verified by `git cat-file -t` = `commit`).

**Compilation context:** `spec/EFF_TEMPLATE_v2.md`; temporary IDs `EFF.GENTOW5.s1of2.<nn>`.

### Governing effective-text record

The note states an explicit effective-text rule. The acceptance record (out of HOME range, lines 1671–1741) reads:

> “**GENTOW5 IS ACCEPTED 2/2** — passPE4 CLEAN (0 CRITICAL + 0 GAP + 2 MINOR, GENTOW5_passPE4_report.md @ b22b37b; counter 0/2 -> 1/2) followed by passPE5 CLEAN (0 CRITICAL + 0 GAP + 3 MINOR, GENTOW5_passPE5_report.md @ 18900e03; counter 1/2 -> 2/2): two consecutive clean hostile passes, the standing acceptance bar.
> **THE NOTE IS FROZEN AT THIS RECORD: dated appends and dated brackets only; statement displays and sealed artifacts stay byte-untouched.**”

> “Grade after this record: **ACCEPTED 2/2**. Dated appends only beyond this line.”

The post-acceptance appends state the same rule as a supersession discipline (S11 head, line 1752):

> “The note is frozen: these are dated corrections BY SUPERSESSION — the superseded sentences are quoted, stay byte-intact above, and read as corrected here.”

**Effective text for this shard = the base body of lines 1–1474 exactly as written, READ AS CORRECTED by (i) the dated brackets already landed inside that range, (ii) the out-of-range dated appends S8–S12 and the post-D3i corrigendum wherever they name an in-range sentence.** No in-range sentence was deleted by any later round; every correction is a supersession that quotes its target.

### Scope split

**A. ABSORPTION/supply SET** (what the note claims to prove). S6, line 1306:

> “**What this note PROVES (grade 0/2, hostile arc owed):**”

with the two target bullets quoted at `EFF.GENTOW5.s1of2.38`, and the STATUS TABLE at `EFF.GENTOW5.s1of2.04`. The grade clause of that heading is superseded by the acceptance record above (ACCEPTED 2/2); the *content* of the supply set is not.

**B. APPEND/consumption PROTOCOL scope** (what has been landed on other notes). S6, lines 1389–1394 records the state at composition time:

> “**Consumption path (not executed here):** GENTOW1_PROOF's S3 grade note and S6 GENTOW-BOX-1, GENHN_PROOF's GENHN-BOX-2 and [GENHN-TOW-1] item (6) depth->=4 sentence, and GENTOW2_PROOF S7's depth->=4 bullet are candidates for the orchestrator's dated consumption updates after this note's own hostile arc; the four source notes are byte-untouched by this unit.”

and S1.4(ii), lines 347–349:

> “GENHN_PROOF is frozen; recording the consumption there is the orchestrator's dated update, not this note's edit.”

That remains the disposition for the four named source notes. The later dated consumption append (lines 2315–2435) adds a distinct outbound consumer: T5 consumes S12.1's conditionality fence and S11.2's proved fixed-unit half, not an unconditional GENTOW5 theorem. It expressly preserves the frozen reading:

> “Certification of the WI companion does not discharge these conjuncts from the frozen GENTOW5 statements. Both the higher-rung supplier law and every downstream conclusion retain their explicit cumulative hypothesis.”

These predicates are not conflated below: GENTOW5 supplies its two mathematical targets; no append lands on the four source notes listed in S6; T5 later consumes the conditional fence under its cumulative hypothesis.

**C. INBOUND corrections RECEIVED from supplier notes.** Three supplier-state changes are folded into in-range text: GENHN's corrected gauge digit (`ĉ_t := lift(c_t·η^{W(t)})`, source commit `59c1966`); GENTOW2's landed r3 cocycle law (`LEMMA GENTOW2-B′/″`, culminating at `d798529`); and HE7 ANNEX R's acceptance lift (`4a613d8` → `a472155`, consumed by HETOW at `e38df9f`). These change the support/provenance read of the GENTOW5 recipe and pin stack; they do not edit the supplier notes from this unit.

### Freeze predicates

1. **Text freeze:** “THE NOTE IS FROZEN AT THIS RECORD: dated appends and dated brackets only; statement displays and sealed artifacts stay byte-untouched.” Pin: dated acceptance record, lines 1671–1741.
2. **Instrument freeze:** “Sealed machine artifacts BYTE-FROZEN at their committed md5s” (`gentow5_checks.py` `5fa684c7…`, exact output `dc499a49…`, full output `839a8660…`). Pins are rechecked in §3.2.
3. **Acceptance-scope enumeration:** S6's two “What this note PROVES” bullets enumerate TARGET 1 and TARGET 2; the acceptance record changes their grade to ACCEPTED 2/2 but does not enlarge their content. Units `.38` and `.04` carry the enumeration.

### Resolution rules applied

1. Base body lines 1–1474 supplies the HOME material for this shard: front matter/ARC records, CHARGE, SOURCES CONSUMED, STATUS TABLE, §S0 setting, §S1 (GENTOW5-A0/A1/A + A′ + BOX-1 disposition), §S2 (DEF GENTOW5-1, GENTOW5-C, GENTOW5-D), §S3 (THEOREM GENTOW5-B and its proof), §S4 (depth-4 witness), §S5 (machine leg), §S6 (residue/grade box), §S7 (PE1 repair record).
2. Dated brackets landed *inside* the range — `[GT5-r1]`, `[GT5-r2]`, `[GT5-r3]`, `[rider]` (post-PE4), `[acceptance fold]` (post-PE5) — are applied in chronology at their own sites; the later bracket governs the earlier text it names.
3. The out-of-range acceptance record governs STATUS: every in-range “grade 0/2”, “counter stays 0/2”, “counter 1/2”, and “PEn next” sentence is historical and superseded by **ACCEPTED 2/2**.
4. S11 `[GT5-r4]` (lines 1743–2029) corrects in-range text by dated supersession at five named sites: A-F1 → S2.4's converse-rewriting sentence and consequence clause, plus S3(c) Step 2's parenthetical; A-F2 → S3(a)'s i ≥ 3 (B-2) transport, fenced behind the open lemma `[GENTOW5-W(i)]`; A-F3 → clause (a) at i = 1; A-F4 → S2.1's `lift_i(c; m)` display; A-F5 → clause (b)'s residual display.
5. S12 `[GT5-r5]` (lines 2033–2313) supersedes parts of S11: **R-i2** withdraws S11.2's “unaffected” list and propagates the `[GENTOW5-W(i)]` conditionality through (a) ⟹ (b) ⟹ S11.1.1/S11.1.3 ⟹ (c) ⟹ (e) at every index n ≥ 3; **R-i4** withdraws S11.4's `bound_{i+1}` range assertion and replaces it with the `bound_i` threshold plus the boxed `bound_i < E_i`.
6. The post-D3i dated corrigendum (lines 2299–2313) re-indexes the twist in S12.1's clause-(b) display: read every `ψ_j^{(ω_j)}` as `ψ_j^{(ω_{j−1})}`, with ω₁ the S11.3 unit. This governs how in-range clause (b) reads at i ≥ 3.
7. Where an out-of-range correction lands on an in-range unit, the corrected reading is carried in that unit's CONDITIONALITY and RESOLUTION TRACE, and the superseded sentence is quoted when it is load-bearing (the note keeps it byte-intact above).
8. Repair-round records homed *inside* the range (S7) are emitted as units; S8/S9/S10 and S11/S12 are homed in shard 2 and appear here only as resolvers.
9. External repo records (the SOL certification ledger, the CITE-SCOPE resolution) are **reading notes only**, never edits — recorded in §8 below.
10. The 2026-08-15 consumption append (lines 2315–2435) makes no correction to the frozen mathematical text. It resolves the earlier corpus-perimeter ambiguity in favor of retaining `𝒲_{≤n}` on GENTOW5's frozen statements, while recording T5 as a consumer of the fence.

---

## 2. Statement inventory

### EFF.GENTOW5.s1of2.01  [changes-record]

**FORM:** bracketed rider

**CANONICAL STATEMENT:** [ASSEMBLED — front-matter status line plus the four in-range ARC verdict sentences, quoted verbatim; the repair-item bodies of each bracket are inventoried at their own repair-record units]

> “**2026-08-09 — SKELETON (per-section commits follow). Unit: GENTOW-5, BOX-CLOSURE campaign wave B1. Grade target 0/2 (attempt; hostile arc owed).**”

> “**[ARC — passPE1 2026-08-09: NOT CLEAN, 1 CRITICAL + 2 GAP + 3 MINOR (GENTOW5_passPE1_report.md @ 0160b94); counter stays 0/2.”

> “**[ARC — passPE2 2026-08-10: NOT CLEAN, 0 CRITICAL + 2 GAP + 2 MINOR (GENTOW5_passPE2_report.md @ 40f313a); counter stays 0/2.”

> “**[ARC — passPE3 2026-08-10: NOT CLEAN, 0 CRITICAL + 1 GAP + 2 MINOR (GENTOW5_passPE3_report.md @ 39c36aa); counter stays 0/2.”

> “**[ARC — passPE4 2026-08-10: CLEAN, 0 CRITICAL + 0 GAP + 2 MINOR (GENTOW5_passPE4_report.md @ b22b37b); counter 0/2 -> 1/2 — the arc's first clean pass.”

**CONDITIONALITY:** Historical. Every counter value above is superseded by the out-of-range acceptance record (**ACCEPTED 2/2**, resolution rule 3). The bracket bodies duplicate, in summary form, the repair records S7 (in range, `.43`) and S8/S9/S10 (shard 2).

**DERIVATION:** Not a mathematical unit; the record is the arc's own chronology, each verdict pinned to its committed report file and commit hash.

**RESOLUTION TRACE:** Base front matter lines 4–86; status superseded at lines 1671–1741.

**TEETH:** The arc itself is the note's tooth of record; per-pass batteries are inventoried at `.37` and §5.

---

### EFF.GENTOW5.s1of2.02  [scope-record]

**FORM:** inline sentence

**CANONICAL STATEMENT:**

> “CHARGE: (1) PROVE or box-with-obstruction GENTOW-BOX-1 — LEMMA GENTOW-2 layer 1 at general mu2 (the composed graded frame; GENTOW1_PROOF S3/S6). (2) THE LEVEL-r LADDER GRAMMAR: the normalizer recursion n-hat_i(m), the composed key recipe Phi_{i+1}, the digit ladder at general i, the general-depth composition theorem (FGMN Cor 6.4 is level-general; HE7 ANNEX R's HE7-2'/R1-a/R1-b is the template one level down); depth-4 witness at n = 32, q = 2 if reachable.”

**CONDITIONALITY:** None — this is the unit's charge, not a claim.

**DERIVATION:** Charge text; no derivation.

**RESOLUTION TRACE:** Base lines 88–95; untouched by later rounds.

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:LEMMA GENTOW-2` — grep-verified count **7**.

XREF: `lean/notes/openmath/HE7_PROOF_2026-08-08.md:ANNEX-LEMMA R1-a` — grep-verified count **6**.

XREF: `lean/notes/openmath/HE7_PROOF_2026-08-08.md:ANNEX-THEOREM R1-b` — grep-verified count **4**.

**TEETH:** The depth-4 witness clause is discharged at `.34`–`.36`; the “if reachable” proviso was met (GREEN both routes).

---

### EFF.GENTOW5.s1of2.03  [fence]

**FORM:** inline sentence

**CANONICAL STATEMENT:**

> “SOURCES CONSUMED (never edited): GENTOW1_PROOF_2026-08-09.md (S0 notation, LEMMA GENTOW-1 + Step 0, LEMMA GENTOW-2 + grade note, LEMMA GENTOW-5, S6 boxes); GENTOW2_PROOF_2026-08-09.md (FGMN quotes [Q1]-[Q10] at verified numbering, THEOREM GENTOW2-A, LEMMA GENTOW2-B + honesty box, S7 depth->=4 scope sentence); GENHN_PROOF_2026-08-08.md (S6.1 LEMMA GENHN-4 + GENHN-BOX-2, S8 [r2] annex T(b)' + GENHN-2', [GENHN-TOW-1] r3 item (6) text); HE7_PROOF_2026-08-08.md ANNEX R (ANNEX-DEF HE7-2', ANNEX-LEMMA R1-a, ANNEX-THEOREMS R1-b/R1-c, R1.2 audit, R1.3 run record).”

**CONDITIONALITY:** “never edited” is the note's own import fence: consumption is one-directional, and the four source notes stay byte-untouched (cross-checked against S6's consumption-path sentence, header scope split).

**DERIVATION:** Declaration, not derivation.

**RESOLUTION TRACE:** Base lines 97–105; reaffirmed at S6 line 1394 (“the four source notes are byte-untouched by this unit”).

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:LEMMA GENTOW-1` — grep-verified count **7**.

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:LEMMA GENTOW-5` — grep-verified count **6**.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:THEOREM GENTOW2-A` — grep-verified count **8**.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B` — grep-verified count **32**.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:LEMMA GENHN-4` — grep-verified count **3**.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN-BOX-2` — grep-verified count **5**.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:[GENHN-TOW-1]` — grep-verified count **19**.

XREF: `lean/notes/openmath/HE7_PROOF_2026-08-08.md:ANNEX-THEOREM R1-c` — grep-verified count **3**.

**READING NOTE (designation orthography, not an edit).** GENTOW5's body is ASCII; three consumed designations carry a Unicode prime in their home notes. Verified forms and counts: `GENHN-2′` **3** (the ASCII `GENHN-2'` also occurs, count **5**); `LEMMA GENHN-T(b)` **11** (`T(b)′` **31**; the ASCII `T(b)'` has count **0** in GENHN_PROOF); `ANNEX-DEF HE7-2′` **6** (the ASCII `ANNEX-DEF HE7-2'` has count **0** in HE7_PROOF). No invented designation is emitted; the Unicode form is the verified one.

**TEETH:** NONE (import declaration).

---

### EFF.GENTOW5.s1of2.04  [TABLE] [scope-record]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** [TABLE — the note's STATUS TABLE, transcribed]

> “STATUS TABLE (updated per section as composed):”

| target | item | status |
|---|---|---|
| (1) | THEOREM GENTOW5-A (composed graded frame, general mu2) | PROVED (S1) |
| (1) | GENTOW-BOX-1 disposition | RETIRED into GENTOW5-A's pin stack (S1.5) |
| (2) | DEF GENTOW5-1 (level-r ladder grammar) | STATED (S2.1) |
| (2) | LEMMA GENTOW5-C ((SLOT_i) for the tower ladder) | PROVED at annex-template grade (S2.3) |
| (2) | LEMMA GENTOW5-D (Step-0 carry monotonicity is level-agnostic) | PROVED (S2.4) |
| (2) | THEOREM GENTOW5-B (general-depth composition) | PROVED with named pins (S3) [GT5-r2: (a) at the twisted residual psi^{(w_i)}; w_i = 1 open] |
| (2) | depth-4 witness n = 32 q = 2 | GREEN: ladder (16,40,84,170,341) exact, resultant + PARI routes (S4.3) |
| battery | gentow5_checks.py | GREEN 92 checks / 0 violations, 5/5 teeth-and-flags as predicted (S5) |

**ARITHMETIC AUDIT:** 8 rows = 2 TARGET-1 rows + 5 TARGET-2 rows + 1 battery row. The battery's `92 = 86 exact + 6 PARI` and `0 violations` agree with the re-opened committed outputs; its stated `5/5` is a source summary of tooth/flag groups, not a claim that only five individual inverse-table rows exist.

**CONDITIONALITY:** The “PROVED with named pins” row for GENTOW5-B is further conditioned by the out-of-range appends: at i ≥ 3 clauses (a), (b), (c), (e) are conditional on `[GENTOW5-W(i)]` (S12.1, resolution rule 5), at i = 1 clause (a) reads at S11.3's re-scoped form, and clause (b)'s residual display reads at S11.5's re-index with the post-D3i twist index.

**DERIVATION:** Status ledger; each row's derivation is the section it names.

**RESOLUTION TRACE:** Base lines 107–118. The `[GT5-r2]` annotation is landed inside the table row. No later round rewrites the table; the conditional narrowing lives in S11/S12.

**TEETH:** Battery row of the table itself is `.37` (92 checks / 0 violations).

---

### EFF.GENTOW5.s1of2.05  [hypothesis]

**FORM:** inline sentence

**CANONICAL STATEMENT:** [ASSEMBLED — §S0 SETTING, quoted in full]

> “Depth-2 tower per T(b)' (accepted): outer genre (Q; e1, f1, mu1; h), key Phi' of degree D' = e1f1; inner side data (u2, e2, psi2, mu2) with gcd(u2, e2) = 1, f2 = deg psi2, e2f2mu2 = mu1; composed key Phi2, deg D2 = D'e2f2; composed ladder dv2 = e1e2*v; K = F_{Q^{f1}}, K2 = F_{Q^{f1f2}}; E2 := e2f2u2; node floor u2 > e2D'h. Ladder normalizers n2hat(m) := pi^{a} x^{i} Phi'^{b} (i < e1, b < e2, e1e2*a + i*e2h + b*u2 = m; unique (i,b) per residue class mod e1e2 — GENTOW-1 S3). GENHN-2' (accepted, T(b)'(ii)): on the tower-node locus, dv2(A(x0)) = the slot minimum EXACTLY, one K2-digit per dv2-height per coordinate. Event setting of LEMMA GENTOW-2: f in the tower locus whose composed polygon (j, p_j), p_j = dv2(C_j(x0)), is ONE side of integer dv2-slope lam > E2 with residual (T - s)^{mu2} over K2, s in K2^x; refine Phi2+ := Phi2 - lift(s; lam). GENTOW-2's layers 2 (corrections land strictly deeper) and 3 (triangular bijection) are PROVED at general mu2 in GENTOW1_PROOF S3; layer 1 (the graded kills) is proved there at mu2 = 2 pointwise only — GENTOW-BOX-1 is exactly that gap. L2 := the completion of the leaf at a fixed root x0 (v extended, normalized v(Q-uniformizer of the BASE) = 1 as everywhere in the corpus); k(L2) its residue field; iota: K2 -> k(L2) the transport of T(b)'/S4 convention.”

**CONDITIONALITY:** The whole setting is hypothesis, imported at the accepted grade: `T(b)′` and `GENHN-2′` are accepted corpus; the event hypothesis carries `lam > E2` (the composed node floor) and `s in K2^x`.

**DERIVATION:** Restatement, explicitly labelled “one-pass restate; GENTOW-1 S0 + HE7-2' names”. The only derived content is the identification of the box: GENTOW-2's layers 2 and 3 are already general-mu2, layer 1 is pointwise at mu2 = 2, so the gap is exactly layer 1.

**RESOLUTION TRACE:** Base §S0, lines 120–142; untouched by any later round.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN-2′` — grep-verified count **3**; supplies the exact-slot-minimum/one-digit-per-height clause.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:LEMMA GENHN-T(b)` — grep-verified count **11**; the accepted depth-2 tower datum.

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:LEMMA GENTOW-2` — grep-verified count **7**; the event setting and the boxed layer 1.

**TEETH:** §S5's P-A1/A2/A3 rows exercise this setting at mu2 = 3 across three frames.

---

### EFF.GENTOW5.s1of2.06  [lemma]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** LEMMA GENTOW5-A0 (gr of a valued field is a graded division ring)

> “For the dv2-rescaled valuation on L2 (values in (1/e1e2)Z on the relevant subfield, rationals in general), set for each rational m
>
>     gr(L2)_m := {a in L2 : dv2(a) >= m} / {a : dv2(a) > m},
>     gr(L2)   := (+)_m gr(L2)_m,   [a] := the class of a in degree dv2(a).
>
> Then gr(L2) is a commutative graded ring, multiplication induced by L2's; every nonzero homogeneous element is invertible; in particular gr(L2) is a domain on homogeneous elements: [a][b] = [ab] != 0 for a, b in L2^x.”

**CONDITIONALITY:** Unconditional — “elementary, self-contained” (S1.5's own characterization). Requires only that L2 is a field with a valuation.

**DERIVATION:** Quoted proof:

> “*Proof.* Well-definedness and distributivity are the ultrametric axioms. Invertibility: for a in L2^x, dv2(a^{-1}) = -dv2(a) and [a][a^{-1}] = [1] != 0 (1 is not in the >0 part). [a][b] = [ab] is dv2(ab) = dv2(a) + dv2(b), a valuation identity on a FIELD (no zero divisors to break it). Degree-0 part: gr(L2)_0 = k(L2). ∎”

With the framing consequence the note attaches (lines 179–183):

> “The point of A0: **pointwise, at a root, there is no carry problem.** Carries are a phenomenon of the slot GRID (rewriting a polynomial between monomial bases); evaluation at x0 is blind to them. The graded frame the box asked for is gr(L2) + the two bookkeeping lemmas below, which translate between grid data and gr(L2) classes.”

**RESOLUTION TRACE:** Base §S1.1, lines 159–183; untouched by every later round (S12.1's unaffected-scope sentence explicitly re-affirms: “LEMMAS GENTOW5-A0/A1 … remain unaffected”).

**TEETH:** NONE dedicated; it is the frame every S5 A-row runs inside.

---

### EFF.GENTOW5.s1of2.07  [definition]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** DEFINITION (multiplicative side residual), with its normalizer class

> “Fix the event slope lam and set N := [n2hat(lam)(x0)] in gr(L2)_{lam} — invertible by A0 (n2hat(lam)(x0) != 0 and its dv2 is lam exactly, GENHN-2' at the single-monomial slot).”

> “**DEFINITION (multiplicative side residual).** For the development f = Sum_{j <= mu2} C_j Phi2^j (C_{mu2} = 1, deg C_j < D2) with pins on or above the side of slope lam through (mu2, 0), the **multiplicative residual** of the side at x0 is
>
>     R_N(T) := Sum_{j} c_j T^j in k(L2)[T],
>     c_j := [C_j(x0)] * N^{-(mu2-j)}  if dv2(C_j(x0)) = (mu2-j)lam,
>     c_j := 0                          if dv2(C_j(x0)) > (mu2-j)lam,
>
> (c_{mu2} = 1 since C_{mu2} = 1 at height 0).”

**CONDITIONALITY:** Requires the pins on or above the side, and `GENHN-2′` for the exactness of the normalizer's height.

**DERIVATION:** The convention's justification, quoted:

> “This is the convention under which residual-of-product = product-of-residuals holds by A0 alone, and it is the corpus's operative convention: GENTOW-1 Step 1 consumes exactly this multiplicativity ("graded layer of a product = product of graded layers"), the level-1 assembly carries the z^{fl}-powers relating n(kappa)^t to n(t*kappa) (GENHN-4 layer 1's display), and FGMN's R-operators — the dictionary target of GENTOW2_PROOF S2 — are multiplicative by Cor 4.7(3) [Q8 @ GENTOW2].”

**RESOLUTION TRACE:** Base §S1.2, lines 185–208; untouched by later rounds.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:[Q8]` — grep-verified count **8**; the pinned FGMN Corollary 4.7. **Clause check:** the `[Q8]` quote block (GENTOW2_PROOF line 147) prints clause “(3) Ri (gh) = Ri (g)Ri (h) for all g, h ∈ K[x]”, so GENTOW5's `Cor 4.7(3)` citation for un-graded multiplicativity is the correct clause (GENTOW2's own consumption uses clauses (1) and (2)).

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:LEMMA GENHN-4` — grep-verified count **3**; the level-1 assembly display.

**TEETH:** §S5's T-A4W (“THE CONVENTION TOOTH FIRED: the naive-digit twin keeps its pin at 22 exactly”).

---

### EFF.GENTOW5.s1of2.08  [lemma]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** LEMMA GENTOW5-A1 (dictionary to the per-height coherent digits)

> “Let gamma_j := the coherent per-height residue of C_j(x0) (the GENHN-2'/S4 digit read against n2hat((mu2-j)lam)). Then
>
>     c_j = iota(gamma_j) * theta_{mu2-j}^{-1},
>     theta_t := [n2hat(lam)(x0)]^t * [n2hat(t*lam)(x0)]^{-1}
>              = iota(vartheta_t),  vartheta_t in K2^x FIXED
>     (theta_0 = theta_1 = 1; equivalently gamma_j = c_j*vartheta_{mu2-j}),
>
> with vartheta_t independent of x0 and of the polynomial read, given by the telescoping vartheta_{t+1} = vartheta_t * res(tau(t*lam, lam)) where tau(a,b) := n2hat(a)n2hat(b)/n2hat(a+b) is the ladder cocycle. tau(a,b) is a Laurent monomial in pi, x, Phi' of dv2-value 0 whose residue at every tower-node point is the transport of a fixed element of K2^x (the two-wrap letter monomial).”

**CONDITIONALITY:** Consumes `GENHN-2′` (coherent digit read) and the S4/T(b)′(iii) wrap letters — “all accepted corpus” per S1.5.

**DERIVATION:** Quoted proof:

> “*Proof.* The first display is A0 arithmetic: [C_j(x0)] = iota(gamma_j)*[n2hat((mu2-j)lam)(x0)] by the definition of the coherent digit, and N^{mu2-j}/[n2hat((mu2-j)lam)(x0)] = theta_{mu2-j}. Telescoping: n2hat(lam)^{t+1}/n2hat((t+1)lam) = [n2hat(lam)^t/n2hat(t*lam)] * [n2hat(t*lam)n2hat(lam)/n2hat((t+1)lam)], the second bracket = tau(t*lam, lam). Cocycle shape: write n2hat(a)n2hat(b) = pi^{a1+a2} x^{i1+i2} Phi'^{b1+b2}; reducing the exponents to ladder range costs one x-wrap x^{e1} = (unit)*pi^{h}*(1 + Phi'-tail/x^{e1}-side data) per overflow and one Phi'-wrap Phi'^{e2} = (unit)*n(u2)*(1 + strictly-above) per overflow — at a tower-node point x0 both wraps have dv2-value 0 with residues the two letters (the eta-wrap z1 := res(x(x0)^{e1}/pi^h * n-correction) and the eta2-wrap z2 := res(Phi'(x0)^{e2}/n(u2)(x0))); both are the transports iota of fixed K2-elements: z1 by GENHN's S4 level-1 cocycle (accepted; the ITER-LAW z-letter), z2 by T(b)'(iii)'s (T22)-transport (Phi'(x0)^{e2}/n(u2)(x0) has residue a fixed unit times psi2-data of eta2(x0), transported through iota — the same S4 computation GENTOW-1 Step 5 runs). Hence res(tau(a,b)(x0)) = iota(z-letter monomial), fixed in K2^x, x0-free through iota. This is ANNEX-LEMMA R1-a(iii) [HE7_PROOF ANNEX R] specialized to the depth-2 tower ladder — reproved here in the tower's own letters rather than cited, since the base conventions differ (HE7's base is varpi-powers; ours is the ladder monomials pi^a x^i). ∎”

**RESOLUTION TRACE:** Base §S1.2, lines 209–247; untouched (S12.1: “LEMMAS GENTOW5-A0/A1 … remain unaffected”).

XREF: `lean/notes/openmath/HE7_PROOF_2026-08-08.md:ANNEX-LEMMA R1-a` — grep-verified count **6**; the precedent whose (iii) clause this lemma re-proves tower-side.

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:Step 5` — grep-verified count **3**; the S4 computation re-run for the second wrap letter.

**TEETH:** §S5's P-A4 / T-A4W (the live-twist mu2 = 2 kill and its naive-digit twin).

---

### EFF.GENTOW5.s1of2.09  [fence]

**FORM:** inline sentence

**CANONICAL STATEMENT:** Convention consequence (displayed for honesty)

> “At mu2 = 2 only vartheta_2 can differ from 1 (vartheta_0 = vartheta_1 = 1 by definition), and in char 2 every element of K2 is a square, so "R is a perfect square" is convention-independent there and the root s re-parameterizes by vartheta_2^{1/2} — which is why the mu2 = 2 battery rows never saw the convention. At mu2 >= 3 with a live cocycle the per-height-digit coefficient vector of a perfect power is NOT itself a perfect-power vector unless the vartheta_t are carried: **fixing the multiplicative convention is part of the box's content**, not a cosmetic choice. All event statements below are in the multiplicative convention; LEMMA GENTOW5-A1 is the exact translation, with fixed re-parameterization only (J-D0: counts are twist-blind, letters re-coordinatize).”

**CONDITIONALITY:** Scope declaration for every downstream event statement: they are all read in the multiplicative convention.

**DERIVATION:** The char-2/mu2 = 2 degeneration argument quoted above is itself the derivation of why the earlier batteries could not see the convention.

**RESOLUTION TRACE:** Base §S1.2, lines 249–261; untouched.

**TEETH:** §S5's T-A4W is the convention tooth this fence predicts.

---

### EFF.GENTOW5.s1of2.10  [lemma]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** THEOREM GENTOW5-A (the substitution theorem = LEMMA GENTOW-2 layer 1 at general mu2)

> “Setting as in S0 (the GENTOW-2 event), with the residual hypothesis read in the multiplicative convention: R_N(T) = (T - w)^{mu2} in k(L2)[T], where w := [lift(s; lam)(x0)] * N^{-1} = iota(s) ON THE NOSE (theta_1 = 1: at the single height lam the two conventions coincide, so the lift's digit IS the root's coordinate — coherence, not invariance, per HE7 ANNEX R R1.2 item 3).
> Set what := -lift(s; lam), Phi2+ := Phi2 + what, and let C_k+ be the Phi2+-development coefficients of f. Then for every k < mu2:
>
>     dv2(C_k+(x0)) > (mu2 - k) * lam        (ALL mu2 PINS DIE),
>
> and the new multiplicative residual of the side is T^{mu2}.”

**CONDITIONALITY:** The S0 event hypotheses (one side of integer slope `lam > E2`, residual `(T-s)^{mu2}` in the multiplicative convention) plus GENTOW-2 layer 2 at general mu2, which is imported from `GENTOW1_PROOF` S3.

**DERIVATION:** Quoted proof, both steps:

> “*Proof.* Substitute Phi2 = Phi2+ - what into the development and expand IN THE POLYNOMIAL RING (no reduction yet):
>
>     f = Sum_j C_j (Phi2+ - what)^j = Sum_k B_k Phi2+^k,
>     B_k := Sum_{j >= k} binom(j, k) (-what)^{j-k} C_j
>          = Sum_{j >= k} binom(j, k) lift^{j-k} C_j.
>
> Step A (the graded identity, in gr(L2)). Evaluate B_k at x0 — a SUM OF PRODUCTS in the field L2; A0 gives, writing [lift(x0)] = w*N:
>
>     class of Sum_j binom(j,k) lift(x0)^{j-k} C_j(x0) at height
>     (mu2-k)lam  =  N^{mu2-k} * Sum_j binom(j, k) w^{j-k} c_j
>                 =  N^{mu2-k} * (coefficient of T^k in R_N(T + w)),
>
> the second equality the Taylor/substitution identity in k(L2)[T] (if R(T) = Sum c_j T^j then R(T + w) = Sum_k [Sum_j binom(j,k) w^{j-k} c_j] T^k — an identity of polynomials, valid over any commutative ring, both characteristics). By hypothesis R_N(T + w) = (T + w - w)^{mu2} = T^{mu2}: for k < mu2 the coefficient is 0, i.e. the height-(mu2-k)lam class of B_k(x0) VANISHES:
>
>     dv2(B_k(x0)) > (mu2 - k) * lam   for every k < mu2.
>
> Note the identity is a SUBSTITUTION identity — the binomials appear transiently but the conclusion (T - w)^{mu2}|_{T -> T+w} = T^{mu2} is binomial-free; char q divides some binom(mu2, k) harmlessly (the corresponding c-coefficients vanish on BOTH sides).
>
> Step B (from B_k to C_k+: layer 2, already proved at general mu2). B_k has x-degree up to (mu2 - k + 1)D2 - ish; the canonical coefficients C_k+ are obtained from the B_k by reduction mod the monic Phi2+ (carries between coordinates) and in-coordinate x-/Phi'-carries. GENTOW-2 layer 2 (PROVED at general mu2 — GENTOW1_PROOF S3, whose grade note restricts only layer 1) prices every such correction: in-coordinate carries are weight-nondecreasing (GENTOW-1 Step 0), and each flow UP one Phi2-coordinate trades weight >= (mu2-k)lam at coordinate k for a contribution at coordinate k+1 of weight >= (mu2-k)lam - E2 > (mu2-k-1)lam (using lam > E2, the composed node floor) — strictly above coordinate (k+1)'s threshold. Weights lower-bound dv2 at x0 on the tower-node locus (GENTOW-1 Step 0 + GENHN-2'). Hence
>
>     dv2(C_k+(x0) - B_k(x0)-contribution) > (mu2 - k) * lam,
>
> and with Step A, dv2(C_k+(x0)) > (mu2 - k)lam for k < mu2. The top coefficient C_{mu2}+ = 1 and the new side's multiplicative residual is T^{mu2} by the same Step-A display at k = mu2. ∎”

**RESOLUTION TRACE:** Base §S1.3, lines 263–325. Step B's grid translation consumes LEMMA GENTOW5-D in the FORWARD direction only, which is exactly what survives S11.1's withdrawal of the two-directional closure (S11.1's consumption walk: “VERIFIED at GENTOW5-A Step B”). S12.1's unaffected-scope sentence keeps the refine-transfer content at its stated event hypotheses.

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:Step 0` — grep-verified count **11**; the carry pricing consumed in Step B.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN-2′` — grep-verified count **3**; weights lower-bound dv2 on the tower-node locus.

**TEETH:** §S5's P-A1/P-A2/P-A3 (the three mu2 = 3 pointwise re-division kills) and T-A1W/T-A2W (wrong height, wrong digit).

---

### EFF.GENTOW5.s1of2.11  [lemma]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** COROLLARY GENTOW5-A′ (i) — GENTOW-2 closes at general mu2

> “(i) LEMMA GENTOW-2's clauses (ii), (iii), (iv) hold at general mu2: (ii) is THEOREM GENTOW5-A; (iii)'s triangularity/bijection consumed layer 1 only through (ii) (GENTOW1_PROOF S3 layer 3, general-mu2 as written); (iv)'s reverse transport is the SAME Step-A computation run on Phi2 = Phi2+ + lift with R_N(T) = T^{mu2} at the refined frame: coordinate j receives minimal class binom(mu2, j) w^{mu2-j} N^{mu2-j} from C_{mu2}+ = 1 — pin (mu2-j)lam with multiplicative residue binom(mu2, j)(-w)^{mu2-j} exactly where q does not divide binom(mu2, j), strictly above where it does. (ii)'s GRADE NOTE restriction is hereby lifted.”

**CONDITIONALITY:** Inherits THEOREM GENTOW5-A's hypotheses; the reverse-transport residue statement is characteristic-sensitive by design (“exactly where q does not divide binom(mu2, j), strictly above where it does”).

**DERIVATION:** As quoted — clause (ii) is `.10`; clause (iii) is imported unchanged from GENTOW1_PROOF S3 layer 3; clause (iv) is the Step-A computation of `.10` re-run at the refined frame.

**RESOLUTION TRACE:** Base §S1.4(i), lines 330–339; untouched by later rounds.

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:LEMMA GENTOW-2` — grep-verified count **7**; the clauses whose grade-note restriction is lifted.

**TEETH:** §S5's P-A1/A2/A3 rows are the pointwise instances of the lifted clause.

---

### EFF.GENTOW5.s1of2.12  [instance-record]

**FORM:** bracketed rider

**CANONICAL STATEMENT:** COROLLARY GENTOW5-A′ (ii) — the level-1 rider

> “(ii) *Level-1 rider (display, no new claim on frozen text).* The S1.1–S1.3 argument runs verbatim one level down (gr(L1) at a stage leaf, N := [n(kappa)(x0)], GENHN-2 in place of GENHN-2', GENHN-4 layer 2 in place of GENTOW-2 layer 2): it is an elementary general-mu carry display of exactly the kind GENHN-BOX-2's text names as its retirement condition ("the GENH4-S5 computation at general (e1, f1, mu)"). GENHN_PROOF is frozen; recording the consumption there is the orchestrator's dated update, not this note's edit.”

**CONDITIONALITY:** Explicitly “no new claim on frozen text”: the rider is a display, and the corresponding GENHN consumption append is NOT landed. Downstream, S3's index-0 scope fold *does* claim clause (d) at index 0 “via S1.4(ii)'s level-1 rider” (see `.26`, `.30`).

**DERIVATION:** The rider's derivation is the verbatim transport of §§S1.1–S1.3 one level down, with the two named substitutions.

**RESOLUTION TRACE:** Base §S1.4(ii), lines 341–349; consumed by the post-PE5 acceptance fold at S3 (lines 769–773) for (d)@0.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN-BOX-2` — grep-verified count **5**; the box whose retirement condition this rider matches.

**TEETH:** None inside this note's battery — the rider is not machine-exercised at level 1 here.

---

### EFF.GENTOW5.s1of2.13  [scope-record]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** S1.5 GENTOW-BOX-1 DISPOSITION

> “**RETIRED as a mathematical box; the residue is grade-only.** What LEMMA GENTOW-2 layer 1 at mu2 >= 3 now consumes: LEMMA GENTOW5-A0 (elementary, self-contained), LEMMA GENTOW5-A1 (self-contained given GENHN-2' + the S4/T(b)'(iii) wrap letters — all accepted corpus), THEOREM GENTOW5-A (this note), and GENTOW-2 layer 2 @ GENTOW1_PROOF (grade 0/2). No W-9-analogue weld face is consumed; the graded frame is gr(L2) itself. Honest conditionality: this note is at grade 0/2 (hostile arc owed), GENTOW-1/GENTOW-2 are at 0/2, and the accepted pins are T(b)'(i)/(ii)/(iii) + S4's coherent normalizers (GENHN accepted 2/2 at PE4). Machine leg: S5's CHECK-A rows are the FIRST mu2 = 3 pointwise re-division kills anywhere in the program (the GN-REFINE3 pattern at the composed key), including a char-3 row and an f2 = 2 two-flavor-lift row.”

**CONDITIONALITY:** The “grade 0/2” self-assessment is superseded by the acceptance record (**ACCEPTED 2/2**, resolution rule 3); the *pin-stack* conditionality (GENTOW-1/GENTOW-2 at their own grades) is not superseded by this note.

**DERIVATION:** The disposition is read off `.06`, `.08`, `.10`: the frame the box demanded is `gr(L2)`, which A0 supplies for free, so no weld face is needed.

**RESOLUTION TRACE:** Base §S1.5, lines 351–365; grade sentence superseded at lines 1671–1741.

**SUPERSESSION KIND:** as-of scoping (grade only).

**TARGETS:** `EFF.GENTOW5.s1of2.13`'s frozen “grade 0/2” clause.

**CHAIN:** S1.5 grade 0/2 → dated acceptance record **TERMINAL (status consumer): ACCEPTED 2/2**. The mathematical box disposition is unchanged.

**NON-IMPORT (explicit):** “No W-9-analogue weld face is consumed.”

**TEETH:** §S5 CHECK-A rows (P-A1/A2/A3, incl. the char-3 and f2 = 2 frames).

---

### EFF.GENTOW5.s1of2.14  [definition]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** DEF GENTOW5-1 (the depth-r tower data) — indices, ladders, floor chain

> “Indices: level 1 = the outer stage (key Phi_1 := Phi', deg D_1 = e1f1); level i has stage data (e_i, f_i) with properness l_i := e_i f_i >= 2 at every i >= 2 (an improper stage is a refinement, not a level — FGMN Lemma 3.5/Prop 3.7 collapsing, per GENTOW2 S6 (H-f)). Write ehat_i := e_1 ... e_i, D_i := l_1 ... l_i (l_1 := e1f1), K_0 := F_Q, K_i := F_{Q^{f_1...f_i}}.”

> “* **Ladders.** dv_i := ehat_i * v. Heights at level-(i+1) points: u_1 := h = dv_1(x); u_{i+1} := dv_{i+1}(Phi_i(xi)) with gcd(u_{i+1}, e_{i+1}) = 1; so dv_i(Phi_j) = (ehat_i/ehat_{j+1}) * u_{j+1} for j < i. Side constants E_i := e_i f_i u_i (E_1 = D_1 h). **Floor chain:** u_{i+1} > e_{i+1} E_i (provenance: the level-i budgets' node corollary, S3(e); at i = 1 this is the [r1] node floor u_2 > e_2 D'h verbatim since E_1 = D'h).”

**CONDITIONALITY:** Datum-level hypotheses: properness `l_i >= 2` at `i >= 2`, coprimality `gcd(u_{i+1}, e_{i+1}) = 1`, and the floor chain. The floor chain's *provenance* is S3(e), which at index n ≥ 3 is itself conditional on `[GENTOW5-W(i)]` after S12.1 — S12.1 makes the distinction explicit:

> “Later arguments may still use that inequality unconditionally when it is included explicitly in the fixed tower datum; only its claimed automatic derivation from the recipe is conditional.”

Rung 1 of the chain is unconditional: it “rides the accepted [r1] node floor u_2 > e_2 E_1 = e_2 D'h directly”.

**DERIVATION:** Definitional. The one derived line is `dv_i(Phi_j) = (ehat_i/ehat_{j+1}) * u_{j+1}` for `j < i`, which is the ladder rescaling of the level-(j+1) height `u_{j+1}`.

**RESOLUTION TRACE:** Base §S2.1, lines 372–385. Floor-chain provenance re-verified at the post-PE4 rider (lines 874–876) and re-scoped at S12.1 item 4 (out of range).

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:Lemma 3.5` — grep-verified count **1**; the FGMN collapsing statement for improper stages.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:Prop 3.7` — grep-verified count **1**; same clause.

**TEETH:** §S5's P-B1/B2 (“floor chain tight (u = 5, 21, 85, 341)”).

---

### EFF.GENTOW5.s1of2.15  [definition]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** DEF GENTOW5-1 — the normalizer recursion

> “* **Normalizers (the recursion of HE7-2', tower-based).** n1hat(m) := pi^a x^{i0} (i0 < e1, e1*a + i0*h = m); for i >= 1
>
>       nhat_{i+1}(k) := nhat_i(m_i(k)) * Phi_i^{b_i(k)},
>       e_{i+1} m_i(k) + b_i(k) u_{i+1} = k,  0 <= b_i(k) < e_{i+1}
>
>   (unique since gcd(u_{i+1}, e_{i+1}) = 1). Unrolled: nhat_i(m) = pi^a x^{i0} Phi_1^{b_1} ... Phi_{i-1}^{b_{i-1}} with i0 < e1, b_j < e_{j+1}. At i = 2 this is GENTOW-1 S3's n2hat verbatim. NOTE the base differs from HE7-2's varpi-powers (varpi^k has unreduced x-degree); the two systems differ per height by a fixed unit — S2.3's remark.”

**CONDITIONALITY:** Uniqueness needs `gcd(u_{i+1}, e_{i+1}) = 1` from `.14`. Existence at a given height is not universal: S11.4 (out of range) records that a flavor base can demand a negative-height normalizer, and the note's own proviso excludes those (see `.17`).

**DERIVATION:** Definitional recursion; the unrolled form follows by iterating the two-line solve, and uniqueness of `(m_i(k), b_i(k))` is the coprimality solve mod `e_{i+1}`.

**RESOLUTION TRACE:** Base §S2.1, lines 387–398. The `i = 2` verbatim identification with GENTOW-1's `n2hat` is re-checked numerically at §S2.2 (`.21`).

XREF: `lean/notes/openmath/HE7_PROOF_2026-08-08.md:ANNEX-DEF HE7-2′` — grep-verified count **6** (Unicode prime; the ASCII form used in GENTOW5's body has count 0 in HE7_PROOF — see the reading note at `.03`).

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:S3` — grep-verified count **14**; the level-2 normalizer this recursion reproduces.

**TEETH:** §S2.2's worked pins (`.21`) and §S5's P-B1/B2.

---

### EFF.GENTOW5.s1of2.16  [definition]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** DEF GENTOW5-1 — cocycle and letters

> “* **Cocycle + letters.** tau_i(a, b) := nhat_i(a) nhat_i(b) / nhat_i(a+b); the level letters Lam_i := Phi_i^{e_{i+1}} / nhat_i(u_{i+1}) (dv-value 0 at level-(i+1) points), beta_{i,xi} := res(Lam_i(xi)); transport tower iota^{(i+1)} extending iota^{(i)} by beta_i -> beta_{i,xi} — ANNEX-DEF HE7-2''s attached objects, tower-instantiated.”

**CONDITIONALITY:** The value-0 claim for `Lam_i` holds at level-(i+1) points (the node locus of `.19`).

**DERIVATION:** Definitional; the `dv`-value-0 claim is the height arithmetic `dv_i(Phi_i^{e_{i+1}}) = e_{i+1} u_{i+1} / e_{i+1}`-normalized against `nhat_i(u_{i+1})`, i.e. equal heights by `.14`'s ladder.

**RESOLUTION TRACE:** Base §S2.1, lines 400–405; the residue computation for `res(tau_i)` is carried out at §S2.3 step (3) (`.22`) and, at level 2, at `.08`.

XREF: `lean/notes/openmath/HE7_PROOF_2026-08-08.md:ANNEX-DEF HE7-2′` — grep-verified count **6**.

**TEETH:** §S5's T-A4W (letter-live twist) and the PE1 fresh frame FR-1 cited at `.18`.

---

### EFF.GENTOW5.s1of2.17  [definition]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** DEF GENTOW5-1 — K_i-digit lifts, at the `[GT5-r2]` CORRECTED DISPLAY

> “* **K_i-digit lifts. [GT5-r2 CORRECTED DISPLAY — PE2 F-2: the composed display bound the base exponents (i0, b_j) to nhat_i(m)'s and stepped only x and Phi_j; at seam-live heights the stepped monomial's compensating pi-exponent goes NON-INTEGER and the displayed flavor DOES NOT EXIST. The corrected display RE-SOLVES the base per flavor.]** For c in K_i and height m, the f_1 f_2 ... f_i within-class FLAVOR MONOMIALS at height m are
>
>       M_{r,t}(m) := nhat_i(m - Delta(r,t)) * x^{e_1 r} *
>                     Phi_1^{e_2 t_1} ... Phi_{i-1}^{e_i t_{i-1}},
>       Delta(r,t) := e_1 r * (ehat_i/e_1) h
>                     + Sum_{j<i} e_{j+1} t_j (ehat_i/ehat_{j+1})
>                       u_{j+1},
>
>   indexed by 0 <= r < f_1, 0 <= t_j < f_{j+1} (a flavor is absent when nhat_i(m - Delta(r,t)) has no ladder solution). Each M_{r,t}(m) sits at dv_i-height m EXACTLY, and its exponents stay in ladder range (x-exponent i0' + e_1 r < e_1 f_1 = D_1 since i0' < e_1; Phi_j-exponent b_j' + e_{j+1} t_j < e_{j+1} f_{j+1} = l_{j+1} since b_j' < e_{j+1}), so deg M_{r,t} < D_i. Then
>
>       lift_i(c; m) := Sum_{r,t} d_{r,t} * M_{r,t}(m),
>
>   O-digit coefficients d_{r,t} realizing c in the coherent normalization (res((lift_i(c; m)/nhat_i(m))(xi)) = iota^{(i)}(c)); existence/freeness is LEMMA GENTOW5-C's (LIFT_i) clause, and the derivation IS the class-separation lemma: within the height-m class mod ehat_i the slots differ by the steps e_1 r, e_{j+1} t_j, each slot's base is the normalizer of the COMPLEMENTARY height m - Delta(r,t) — NOT nhat_i(m)'s base — and the flavor residues res((M_{r,t}(m)/nhat_i(m))(xi)) are the FIXED letter units of the tau_i-cocycle (S2.3 step (3)), so the d_{r,t} are the inverse-twisted K_{i-1}-expansion digits of c.”

**CONDITIONALITY:** Two later corrections govern the height range of this display, in sequence.

S11.4 (out of range) attaches an m-range:

> “the flavor display and the realization sentence ("O-digit coefficients d_{r,t} realizing c") read AT HEIGHTS m IN (LIFT_i)'S VALIDITY RANGE — k-uniformly above the bound_{i+1} recursion of LEMMA GENTOW5-C”

S12.2 (out of range) **withdraws** that bracket and fixes the correct rung:

> “**Superseded S11.4 bracket.** The sentence placing the displayed \(\operatorname{lift}_i(c;m)\) above \(\operatorname{bound}_{i+1}\) is WITHDRAWN. That display realizes \(c\in K_i\) by a polynomial of degree \(<D_i\); hence it consumes the PRECEDING lift instance and has threshold \(\operatorname{bound}_i\), not \(\operatorname{bound}_{i+1}\).”

**Effective reading:** the display is valid for `m > bound_i`, supplied by `(LIFT_{i-1})` at `i >= 2` and by the accepted base lift at `i = 1`; the “flavor is absent when nhat_i(m - Delta(r,t)) has no ladder solution” proviso already excludes negative-height bases (S11.4's own worked failure: `i = 1, e_1 = 2, f_1 = 2, h = 1, m = 0`, where the `r = 1` flavor demands `pi^{-1}`).

**DERIVATION:** [ASSEMBLED — the note's own derivation sentence plus its machine verification] The derivation named in the display is LEMMA GENTOW5-C's class-separation step (3): flavor residues are the fixed tau_i-cocycle letter units, so the coefficients are the inverse-twisted `K_{i-1}`-expansion digits. The corrected base-solve is verified numerically:

> “VERIFICATION AT PE2's FR-A (p = 3, e_1 = 2, h = 1, e_2 = 1, u_2 = 3; m = 14, nhat_2(14) = 3^7): the t_1 = 1 flavor is M_{0,(1)}(14) = nhat_2(14 - 3) * Phi_1 = 3^5 * x * Phi_1 (nhat_2(11) = 3^5 x — the x-exponent RE-SOLVES 0 -> 1); the composed fixed-base display demanded pi-exponent (14 - 0 - 3)/2 = 11/2, NO such monomial. Machine row: check FA1-LIFT (gentow5_pe2_fresh.py @ 40f313a, 22/0) asserts the fixed-base flavor's non-existence AND the green chain runs on the re-solved member 3^5*x*Phi_1 = FR-A's khat_0.”

And its ripple fence:

> “Ripple (checked): the recipe's khat_t and S2.4's value-blind leg read HEIGHTS only — each M_{r,t}(m) sits at height m exactly, unchanged; (LIFT_i)'s bound arithmetic and deg < D_i are as displayed; no other consumer in this note reads the flavor bases.”

**RESOLUTION TRACE:** Base §S2.1 display, replaced in place by `[GT5-r2]` (PE2 F-2, lines 407–458); m-range bracket added by S11.4; that bracket superseded by S12.2 (resolution rule 5).

**SUPERSESSION KIND:** replacement (display) plus scope-pin (range), terminal replacement attached.

**TARGETS:** `EFF.GENTOW5.s1of2.17`'s frozen fixed-base lift display and its S11.4 range bracket.

**CHAIN:** composed fixed-base display → `[GT5-r2]` per-flavor re-solve → S11.4 `m > bound_{i+1}` range → **S12.2 `m > bound_i` TERMINAL**.

**NON-IMPORT (explicit):** “GENTOW1 S3's fixed-base READING of its lift display fails the same way at seam-live heights — a display-level defect there, flagged for that note's own arc, not consumed here.”

**TEETH:** `FA1-LIFT` (gentow5_pe2_fresh.py @ 40f313a, 22 checks / 0 violations).

---

### EFF.GENTOW5.s1of2.18  [definition]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** `[ASSEMBLED — S2.1 recipe statement and its terminal in-bullet scope sentence]` DEF GENTOW5-1 — THE COMPOSED KEY RECIPE, at the `[GT5-r1]` GAUGE PIN

> “* **THE COMPOSED KEY RECIPE (the charge's display). [GT5-r1 GAUGE PIN — the governing pin of the r1 round; PE1 F-1 CRITICAL].** Given stage data (e_{i+1}, f_{i+1}) and monic irreducible psi_{i+1} = y^{f_{i+1}} - Sum_{t<f_{i+1}} c_t y^t over K_i with c_0 != 0:
>
>       Phi_{i+1} := Phi_i^{e_{i+1} f_{i+1}}
>                    - Sum_{t < f_{i+1}} khat_t * Phi_i^{e_{i+1} t},
>       khat_t := lift_i(c_t * vartheta_{i, f_{i+1}-t};
>                        u_{i+1}(f_{i+1} - t))        (0 if c_t = 0),
>
>   where vartheta_{i,s} := res(nhat_i(u_{i+1})^s / nhat_i(s*u_{i+1})) in K_i^x is the FIXED telescope unit of the tau_i-cocycle (S1.2's vartheta and S2.3 step (3), run at level i and heights multiples of u_{i+1}): vartheta_{i,0} = vartheta_{i,1} = 1, vartheta_{i,s+1} = vartheta_{i,s} * res(tau_i(s*u_{i+1}, u_{i+1})).”

> “  Monic of degree D_{i+1}; every side term at dv_{i+1}-height E_{i+1} exactly (e_{i+1} * u_{i+1}(f_{i+1}-t) + e_{i+1} t u_{i+1} = E_{i+1}; the top term e_{i+1} f_{i+1} u_{i+1} = E_{i+1} — the vartheta twist is a residue-level unit, height-blind). At i = 1 this is T(b)''s Phi2 AT ITS ERRATUM-CORRECTED DISPLAY (59c1966), NOT the gauge-naive original; at i = 2 the r3 box's Phi3 with vartheta_2-corrected digits.”

**CONDITIONALITY:** The recipe's lifts must exist in range. S12.2 discharges exactly that, unconditionally:

> “For a nonzero recipe coefficient \(c_t\), put \(s=f_{i+1}-t\). Since \(t<f_{i+1}\), one has \(s\ge1\), and the recipe height is \[ m_t=s\,u_{i+1}\ge u_{i+1} >e_{i+1}E_i\ge E_i>\operatorname{bound}_i. \]”

with the boxed inequality it rests on: `bound_i < E_i for every i >= 1`.

**DERIVATION:** [ASSEMBLED — the r1 gauge-pin derivation, quoted] The twist is derived in the building direction from `.08`'s dictionary:

> “[GT5-r1 derivation, NOT a transcription. Why the twist: grouping the recipe in Phi_i-slots, the slot-t MULTIPLICATIVE residual coefficient (S1.2's convention — the side residual's read; [GT5-r2] per the landed GENTOW2 r3 B-law the FGMN R-read differs from it by the cross-frame unit w_i per grade — the S3(a) re-scope) is res(khat_t / nhat_i(u_{i+1})^{f-t}) = digit(khat_t) * res(nhat_i((f-t)u_{i+1}) / nhat_i(u_{i+1})^{f-t}) = digit(khat_t) * vartheta_{i,f-t}^{-1} (f := f_{i+1}); for that coefficient to equal psi_{i+1}'s c_t, the prescribed COHERENT digit must be c_t * vartheta_{i,f-t} — LEMMA GENTOW5-A1's dictionary gamma = c * vartheta, applied in the BUILDING direction. The plain lift lift_i(c_t; ·) is the GAUGE-NAIVE form: its multiplicative coefficient is c_t * vartheta^{-1}, wrong wherever the letters are live.”

Level-2 recovery, the derivation's own consistency check against the accepted GENHN erratum:

> “Level-2 recovery: n1hat monomials are pi^a x^{i0}; multiplying s copies of n1hat(u_2) accumulates x-exponent s*i(u_2), reduced to ladder range by floor(s*i(u_2)/e1) x-wraps x^{e1} = pi^h * (x^{e1}/pi^h), so vartheta_{1,s} = eta^{floor(s*i(u_2)/e1)}; at s = f_2 - t this is EXACTLY the GENHN dated erratum's corrected chat_t := lift(c_t*eta^{W(t)}), W(t) = floor((f_2-t)*i(u_2)/e1) (erratum 59c1966, provoked by HETOW PE1 F-1; pinned at GENTOW1 by [GT1-r1] 477b1b1).”

Degeneracy fence and the machine tooth:

> “At any frame where each c_t * (vartheta_{i,f-t} - 1) = 0 — in particular all letters = 1, or f_{i+1} = 1 (only s = 1 occurs, vartheta_{i,1} = 1) — corrected = naive. MACHINE VERIFICATION at a letter-live frame (the PE1 fresh instrument gentow5_pe1_fresh.py @ 0160b94, FR-1: p = 3, Phi_1 = x^2 - 6, eta = 2, (e_2,f_2) = (1,2), u_2 = 3, psi_2 = y^2 + y + 2, i(u_2) = 1 so W(1) = 0, W(0) = 1): the corrected key Phi_1^2 - 6x*Phi_1 - 54 is the carrier — sigma = (2,2), nfeltval(Phi_1) = 3 exact; the gauge-naive key Phi_1^2 - 6x*Phi_1 - 27 has sigma = {(4,1)} with degenerate residual (y-1)^2 — THEOREM GENTOW5-B (a)/(b) fail at the naive display there.”

**RESOLUTION TRACE:** Base §S2.1 recipe display, pinned by `[GT5-r1]` (PE1 F-1, lines 460–520) with the `[GT5-r2]` parenthetical inserted at the R-read sentence. Its governing scope is declared inside the pin: “This pin governs khat_t at its uses below (S2.4's INV-j heights — value-blind, see there; S3's statement + (a), (b), (c) Step 5, (d); S4.1's witness keys — seam-blind, see there).”

**SUPERSESSION KIND:** replacement.

**TARGETS:** `EFF.GENTOW5.s1of2.18`'s gauge-naive recipe.

**CHAIN:** plain `lift_i(c_t;·)` recipe → **`[GT5-r1]` vartheta-twisted recipe TERMINAL**; `[GT5-r2]` changes the FGMN residual reading, not this recipe display.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:W(t) = ⌊(f₂−t)·i(u₂)/e₁⌋` — grep-verified count **1** (GENHN_PROOF line 1990); the erratum's exponent law that the level-2 specialization reproduces. The erratum's corrected digit is printed there as `ĉ_t := lift(c_t·η^{W(t)})` — grep-verified count **1** (line 1997); GENTOW5's ASCII `chat_t` is the transliteration of that Unicode designation (the ASCII string `chat_t` has count **0** in GENHN_PROOF).

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:[GT1-r1]` — grep-verified count **5**; the round at which the erratum was pinned there.

**TEETH:** PE1 fresh frame FR-1 (gentow5_pe1_fresh.py @ 0160b94, 15/0 — the corrected/naive key discrimination); §S5's T-A4W convention tooth.

---

### EFF.GENTOW5.s1of2.19  [definition]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** DEF GENTOW5-1 — the depth-(i+1) node locus

> “* **The depth-(i+1) node locus P_{i+1}** := roots xi with v(x(xi)) = h/e1 exactly, eta(xi) a psi_1-root, and inductively v(Phi_j(xi)) = u_{j+1}/ehat_{j+1} exactly with the level-(j+1) residue class a psi_{j+1}-root, for j < i+1 — the tower transport chain (T(b)'(iii) at i = 1; GENTOW2-A(d)'s data at i = 2).”

**CONDITIONALITY:** Definitional; nonemptiness of `P_{i+1}` is a hypothesis wherever it is consumed (explicitly assumed in LEMMA GENTOW5-C, `.22`).

**DERIVATION:** Definition; the claim that recipe roots lie in it is clause (b) of THEOREM GENTOW5-B (`.28`), not part of this definition.

**RESOLUTION TRACE:** Base §S2.1, lines 522–526; untouched by later rounds.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:THEOREM GENTOW2-A` — grep-verified count **8**; its clause (d) supplies the i = 2 data.

**TEETH:** §S4.2's P-B4/P-C2 ladder rows are the witness's `P`-membership evidence (exact ladder 16, 40, 84, 170, 341).

---

### EFF.GENTOW5.s1of2.20  [lemma]

**FORM:** inline sentence

**CANONICAL STATEMENT:** first-live arithmetic

> “First-live arithmetic: a depth-r tower with a live top problem mu_r >= 2 needs n = D_r * mu_r >= 2^{r+1}; depth 4 first lives at n = 32 (S4's witness is exactly minimal).”

**CONDITIONALITY:** Uses properness `l_i >= 2` at `i >= 2` from `.14` (so `D_r >= 2^r`) and a live top problem `mu_r >= 2`.

**DERIVATION:** [ASSEMBLED — from the note's own datum] `D_r = l_1...l_r` with every `l_i >= 2` gives `D_r >= 2^r`, and `mu_r >= 2` gives `n = D_r mu_r >= 2^{r+1}`; at `r = 4` this is `n >= 32`, attained by §S4's witness.

**RESOLUTION TRACE:** Base §S2.1, lines 528–530; untouched.

**TEETH:** §S4's witness is the attainment instance (`deg 32 = the first-live depth-4 degree`).

---

### EFF.GENTOW5.s1of2.21  [instance-record]

**FORM:** inline sentence

**CANONICAL STATEMENT:** §S2.2 Consistency checks on the recursion (worked pins)

> “n3hat(85) at the S4 chain ((e_i) = (2,2,2,2), h = 1, u = 5, 21, 85): recursion: b_3... level 3: 2m + 21b = 85, b < 2 -> b = 1, m = 32; level 2: 2m' + 5b' = 32, b' < 2 -> b' = 0, m' = 16; base: 2a + i0 = 16 -> i0 = 0, a = 8. n3hat(85) = 2^8 * Phi_2 — matching the direct unrolled solve (16a + 8 i0 + 20 b_1 + 42 b_2 : mod-parity forces b_2 = 1, then b_1 = 0, i0 = 0, a = 8... on the dv_4 ladder; see S4). The r3 witness n2hat(21) = 16 Phi' is the recursion at level 2: 2m + 5b = 21 -> b = 1, m = 8 -> 2a + i0 = 8 -> 2^4. Both match the committed runners' values (genhnr2_supp L388-389; gentow2 W1).”

**CONDITIONALITY:** Two worked instances of `.15`, not a general claim.

**DERIVATION:** The displayed solves are the derivation.

**RESOLUTION TRACE:** Base §S2.2, lines 532–542; untouched.

**TEETH:** Cross-checked against committed runner values (`genhnr2_supp` L388–389; `gentow2` W1) and reproduced in §S4.1's key list.

---

### EFF.GENTOW5.s1of2.22  [lemma]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** `[ASSEMBLED — statement plus acceptance-fold replacement]` LEMMA GENTOW5-C ((SLOT_i) + (LIFT_i) for the tower ladder)

> “**Statement.** Let i >= 1 and assume the tower data of DEF GENTOW5-1 through level i+1 with P_{i+1} nonempty, and (SLOT_{i-1}) at level i (base: i = 1 is GENHN-2 + HE6-1's transport identity; i = 2 is GENHN-2' — both accepted). Let xi in P_{i+1}, C in O[x] with 0 != deg C < D_{i+1}, developed C = Sum_{b < e_{i+1} f_{i+1}} c_b Phi_i^b with deg c_b < D_i. Then dv_{i+1}(C(xi)) equals the slot minimum EXACTLY; the minimizing b lie in one class mod e_{i+1}; and the height-k residue against nhat_{i+1}(k)(xi) is iota^{(i+1)}(Sum_t gamma_t vartheta_t beta_i^t) != 0 with gamma_t the level-i digit symbols ((SLOT_{i-1})) and vartheta_t the FIXED twist units of the telescoped tau_i-cocycle — i.e. one K_{i+1}-digit per dv_{i+1}-height, class separation mod e_{i+1} between Phi_i-slots and mod ehat_{i+1} overall. (LIFT_i): k-uniformly above the bound recursion bound_{i+1} = (l_{i+1}-1)u_{i+1} + e...*bound_i, every K_{i+1}-residue at height k is realized by some C with deg < D_{i+1} (inverse-twisted digits).”

The truncated token in the bound display is restored by the in-range acceptance fold:

> “[acceptance fold 2026-08-10 (PE5-F-3): the bound display's truncated token "e..." reads e_{i+1} — bound_{i+1} = (l_{i+1}-1)u_{i+1} + e_{i+1}*bound_i. Re-derived at the primary source, not restored from memory: ANNEX-THEOREM R1-c displays the recursion bound_{i+1} := (L_i - 1)u_i + l_i*bound_i with L_i = l_i g_i the stage size and l_i the ramification multiplier (HE7_PROOF ANNEX R; its arithmetic line m_0 = (k - s_0 u_i)/l_i >= (g_i - 1)u_i + bound_i), and in this lemma's tower names the step-(1) height split is k = e_{i+1}*m + b*u_{i+1} with b <= l_{i+1} - 1 (slots b < e_{i+1}f_{i+1}), so the slot term saturates at (l_{i+1}-1)u_{i+1} and the level-i threshold scales by the ramification factor e_{i+1}. Grep-scoped this fold: bound_i appears in this note only at this statement display — no numeric consumption site found (the proof's own remark: the bound arithmetic never sees residues).]”

**CONDITIONALITY:** Induction hypothesis `(SLOT_{i-1})` at level i, `P_{i+1}` nonempty, and the DEF GENTOW5-1 datum through level i+1. Base cases i ≤ 2 rest on accepted corpus; at i ≥ 3 the argument rides the HE7 ANNEX R precedent pin (now at acceptance grade — see the DERIVATION's dated fold). Note that S12.2 (out of range) keeps `(LIFT_i)`'s own threshold at `bound_{i+1}` — it is `lift_i`, not `(LIFT_i)`, whose rung was mis-stated:

> “By contrast, the clause labelled \(({\rm LIFT}_i)\) in LEMMA GENTOW5-C constructs \(K_{i+1}\)-digits of degree \(<D_{i+1}\) and therefore correctly has threshold \(\operatorname{bound}_{i+1} =(l_{i+1}-1)u_{i+1} +e_{i+1}\operatorname{bound}_i.\)”

**DERIVATION:** Quoted proof:

> “**Proof: ANNEX-THEOREM R1-b/R1-c's proofs, re-based.** The HE7 ANNEX R proofs consume exactly four clauses of their level-i datum: (a) values exact one level down ((SLOT_{i-1}), our induction hypothesis); (b) the defining clause w_{i+1}(Phi_i(xi)) = u_{i+1} exactly (our P_{i+1}, clause j = i); (c) gcd(u_{i+1}, e_{i+1}) = 1 (DEF GENTOW5-1); (d) {1, beta_i, ..., beta_i^{g-1}} a K_i-basis of K_{i+1} with beta_i := the level-(i+1) residue letter, r_i := its minimal polynomial irreducible (our psi_{i+1}-root clause of P_{i+1}, f_{i+1} = deg psi_{i+1}). Steps: (1) values of c_b(xi)Phi_i(xi)^b are e_{i+1}*w_i(c_b) + b*u_{i+1} exactly by (a)+(b); (2) cross-class ties impossible: b*u_{i+1} mod e_{i+1} bijective by (c); (3) within one class, slots b0 + e_{i+1}t: the monomial identity of R1-b (R1.2) with theta_t telescoping into tau_i-values; each theta_t has residue a fixed K_i^x-unit by the S1.2-style cocycle computation run at level i (the letter monomial — tau_i is a Laurent monomial in pi, x, Phi_1, ..., Phi_{i-1} of dv-value 0, residue a fixed product of the letters beta_1 ... beta_{i-1} through iota^{(i)}); (4) summing the class, the residue is the displayed K_i-combination of beta_i-powers, nonzero by (d) since the gamma_t vanish iff their slots do not attain and at least one attains — no cancellation, value exact. (LIFT_i): R1-c verbatim — prescribe the level-i digits INVERSE-twisted by vartheta_t^{-1} ((LIFT_{i-1}) supplies them one level down; base = the level-1/2 lift lemmas, accepted); the bound arithmetic never sees residues.”

Grade fold on the precedent pin:

> “**Grade honesty:** this is HE7 ANNEX R's R1-b/R1-c argument transported onto the tower ladder — [GT5-r1 DATED FOLD 2026-08-10, orchestrator-authorized (ledger B8, 87a7b61): the annex stack is now ACCEPTED 2/2 (annexpass CLEAN 4a613d8 -> annexpass2 CLEAN a472155, "the annex stack is ACCEPTED 2/2"; the HETOW acceptance record e38df9f consumes it); the composition-time wording "POST-RATIFICATION, UNPASSED (annex grade)" is superseded in the CONSERVATIVE direction — the pin claimed weaker support than the truth]; the transport itself (the four-clause instantiation table above) is this note's, and the base cases i <= 2 rest only on accepted corpus. Every i >= 3 consumer below carries this pin explicitly, now at the acceptance grade. ∎”

**RESOLUTION TRACE:** Base §S2.3, lines 544–613, with the `[GT5-r1]` grade fold inside the proof and the post-PE5 `[acceptance fold]` on the bound token. Step (3) of this proof is the derivation cited by `.17` and by `.27`'s i ≥ 3 leg — and it is precisely the leg that S11.2 (out of range) fences: it carries per-grade fixedness, **not** the single-w monomial form.

**SUPERSESSION KIND:** replacement (truncated bound token) plus provenance-rider (annex grade).

**TARGETS:** `EFF.GENTOW5.s1of2.22`'s `e...*bound_i` token and its stale “POST-RATIFICATION, UNPASSED” provenance.

**CHAIN:** `e...*bound_i` → **`e_{i+1}*bound_i` TERMINAL (formula consumer)**; annex-grade cap → **HE7 ANNEX R ACCEPTED 2/2 TERMINAL (provenance consumer)**.

XREF: `lean/notes/openmath/HE7_PROOF_2026-08-08.md:ANNEX-THEOREM R1-b` — grep-verified count **4**.

XREF: `lean/notes/openmath/HE7_PROOF_2026-08-08.md:ANNEX-THEOREM R1-c` — grep-verified count **3**.

XREF: `lean/notes/openmath/HE7_PROOF_2026-08-08.md:R1.2` — grep-verified count **7**; the monomial identity consumed at step (3).

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN-2` — grep-verified count **28**; the accepted `i = 1` base (`GENHN-2′`, count **3**, is the `i = 2` base).

**TEETH:** No dedicated committed row at i ≥ 3; the note's own coverage box (`.40`) names this as the machine-side gap. §S5's A-rows exercise the i ≤ 2 instances.

---

### EFF.GENTOW5.s1of2.23  [fence]

**FORM:** inline sentence

**CANONICAL STATEMENT:** Remark (HE7 base vs tower base)

> “*Remark (HE7 base vs tower base).* HE7-2''s n_1 = varpi-powers and our n1hat differ per height by the fixed wrap letter (both are value-m monomials; the quotient is a value-0 Laurent monomial in x, pi with residue a fixed power of the level-1 letter). By J-D0 (counts twist-blind, letters re-coordinatize; R1.2 item 7) every count/degree/vanishing statement transports between the two systems; residue letters re-coordinatize by fixed units. We work in the tower base throughout; no invariance under CHANGING systems mid-argument is consumed (that stronger claim is false — HE7-T-BADTWIST).”

**CONDITIONALITY:** The transport is asserted for count/degree/vanishing statements only.

**DERIVATION:** The quotient of the two normalizer systems is a value-0 Laurent monomial, so J-D0 applies.

**RESOLUTION TRACE:** Base §S2.3 remark, lines 615–623; untouched.

**NON-IMPORT (explicit):** “no invariance under CHANGING systems mid-argument is consumed (that stronger claim is false — HE7-T-BADTWIST)”.

XREF: `lean/notes/openmath/HE7_PROOF_2026-08-08.md:R1.2` — grep-verified count **7**; item 7 is the twist-blindness audit.

**TEETH:** NONE.

---

### EFF.GENTOW5.s1of2.24  [definition]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** the level-i weight functional, at the `[GT5-r1]` top-grid repair

> “**Weight. [GT5-r1 — PE1 F-3: the top-grid term is now DEFINED.]** On monomials M = pi^v x^{a} Phi_1^{J_1} ... Phi_i^{J_i} (exponents unbounded) define
>
>     wt_i(M) := ehat_i*v + a*(ehat_i/e1)h
>                + Sum_{j<i} J_j * (ehat_i/ehat_{j+1}) u_{j+1}
>                + J_i * E_i,
>
> i.e. the TOP variable Phi_i carries weight E_i = e_i f_i u_i per unit exponent — the in-datum lower bound (dv_i(Phi_i(xi)) > E_i on the tower locus by the field floor, vs the EXACT interior values dv_i(Phi_j(xi)) = (ehat_i/ehat_{j+1})u_{j+1} for j < i); the pre-repair display left this term as an undefined "E-part". Note wt_i consumes NO data beyond the depth-i datum: u_{i+1} does not appear.”

**CONDITIONALITY:** The top term is a *lower bound*, not an exact value — that asymmetry is the whole content of the r1 repair.

**DERIVATION:** Definitional; the top weight is fixed at `E_i` because the exact value `dv_i(Phi_i(xi))` is only known to exceed `E_i` (field floor), while interior values are exact.

**RESOLUTION TRACE:** Base §S2.4 weight display, replaced by `[GT5-r1]` (PE1 F-3, lines 628–642).

**SUPERSESSION KIND:** replacement.

**TARGETS:** `EFF.GENTOW5.s1of2.24`'s undefined top-grid “E-part”.

**CHAIN:** undefined top-grid `E-part` → **top variable `Phi_i` priced at `E_i` TERMINAL**.

**NON-IMPORT (explicit):** “wt_i consumes NO data beyond the depth-i datum: u_{i+1} does not appear.”

**TEETH:** §S7's F-3 worked grid-4 equality instance (170 = 170 = 170).

---

### EFF.GENTOW5.s1of2.25  [lemma]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** `[ASSEMBLED — statement, riders, and quoted superseded clauses]` LEMMA GENTOW5-D (Step-0 carry monotonicity is level-agnostic), at the `[GT5-r1]`/`[GT5-r2]` restatement

> “**Statement [GT5-r1 restated — strictness weakened to what the induction needs].** For every level i, the i reduction moves — the x-carry (a >= D_1) and the Phi_j-carries (J_j >= l_{j+1}, j < i) — are wt_i-NONDECREASING; lift-generated terms preserve weight exactly; the key-part of each INTERIOR carry (the x-carry WHEN i >= 2, and the Phi_j-carries with j < i-1) strictly raises it, while the TOP carry's key-part (j = i-1: key-part Phi_i at weight E_i = wt(Phi_{i-1}^{l_i})) PRESERVES it exactly.”

> “[GT5-r2 — PE2 F-3, the i = 1 edge: at i = 1 the ONLY move is the x-carry and it IS the top carry (j = 0 = i-1): key-part Phi_1 at wt_1(Phi_1) = E_1 = D_1 h = wt_1(x^{D_1}) — PRESERVED, not strict; and the proof's rung range "1 (x-carry) through i-1" is EMPTY there (no floor rung consumed — the x-carry's strict pricing would reference u_2, out-of-datum at depth 1, the same disease [GT5-r1] cured at the top grid). Unconsumed edge: the named consumers instantiate i >= 2 (GENTOW5-A Step B at i = 2; S3(c)/(d) at i + 2 >= 3).]”

**Superseded consequence clause (quoted; corrected out of range).** The base text continues:

> “Hence "all slots at weight >= W" is the same condition on every grid of the tower (the two-directional rewriting closes), and per-slot weight arithmetic converts to the digit floors verbatim as in GENTOW-1 Step 0.”

and closes its proof with:

> “The converse rewriting (Phi_{j+1} = Phi_j^{l_{j+1}} - weight-E_{j+1} lifts) is weight-nondecreasing by the same displays. ∎”

S11.1 `[A-F1, CRITICAL]` withdraws both:

> “— FALSE as written. And the statement's consequence clause: "Hence 'all slots at weight >= W' is the same condition on every grid of the tower (the two-directional rewriting closes)" — WITHDRAWN to the one-directional form below.”

**Effective reading:** forward carry moves are `wt_i`-nondecreasing (statement untouched); the converse rewriting is weight-NONINCREASING — preserved exactly at the top rung, strictly lowered at each interior rung by the corresponding floor rung. The one surviving converse remnant is the SINGLE-STEP top-rung expansion, which preserves slot weights exactly.

**CONDITIONALITY:** Consumes only `(INV-j)` and `(FLOOR-j)`, both in-datum:

> “The only inputs are (INV-j): the recipe keys' side terms at exact height E_{j+1} (DEF GENTOW5-1's construction, gauge-pin-stable) and (FLOOR-j): u_{j+1} > e_{j+1} E_j, consumed at rungs 1 (x-carry) through i-1 (deepest interior carry; the range is EMPTY at i = 1, where no rung is consumed — the [GT5-r2] edge clause) — all inside the depth-i datum.”

**DERIVATION:** Quoted proof (the two displays, uniform in j):

> “* x-carry: x^{D_1} = Phi_1 + tail, tail monomials x^c pi^g with g >= (D_1 - c)h/e1 (Phi_1's one side): tail wt >= (ehat_i/e1) D_1 h = wt(x^{D_1}), equality on the side lattice; Phi_1-part wt = (ehat_i/ehat_2) u_2 > (ehat_i/ehat_2) e_2 E_1 = (ehat_i/e1) D_1 h — STRICT by the floor chain at j = 1 [GT5-r2: this pricing reads rung 1 (u_2), in-datum only when i >= 2; at i = 1 Phi_1 is the TOP variable, priced at wt_1(Phi_1) = E_1 = wt_1(x^{D_1}) — PRESERVED, the statement's edge clause].
> * Phi_j-carry: Phi_j^{l_{j+1}} = Phi_{j+1} + Sum_t khat_t Phi_j^{e_{j+1}t}; each lift term has wt = (ehat_i/ehat_{j+1}) [e_{j+1} u_{j+1}... ] — compute: khat_t's monomials all sit at dv_j-height u_{j+1}(f_{j+1}-t) exactly (single-height lifts, DEF GENTOW5-1 — [GT5-r1] the gauge pin's vartheta twist is a residue unit, so the corrected khat_t sits at the SAME heights: this display is value-blind, the GENTOW1 [GT1-r1] Step-0 immunity verbatim), contributing (ehat_i/ehat_{j+1}) e_{j+1} u_{j+1}(f_{j+1}-t) + e_{j+1} t (ehat_i/ehat_{j+1}) u_{j+1} = (ehat_i/ehat_{j+1}) E_{j+1} = wt(Phi_j^{l_{j+1}}) — PRESERVED exactly; the key-part splits [GT5-r1]:
>     - INTERIOR (j <= i-2): the Phi_{j+1}-part has wt = (ehat_i/ehat_{j+2}) u_{j+2} > (ehat_i/ehat_{j+2}) e_{j+2} E_{j+1} = (ehat_i/ehat_{j+1}) E_{j+1} — STRICT by floor rung j+1 (u_{j+2} > e_{j+2}E_{j+1}), which is IN-DATUM since j+2 <= i;
>     - TOP (j = i-1): the Phi_i-part has wt = E_i = l_i u_i = wt(Phi_{i-1}^{l_i}) — PRESERVED exactly, NO floor rung consumed (the pre-repair uniform pricing read the top key-part at u_{i+1}/e_{i+1}: non-integer, and at the top grid of a depth-r tower rung r references u_{r+1} = EVENT data outside the statement's floor chain — PE1 F-3's audit; the repair prices it at the defined weight E_i instead).”

**Failure-mode fence carried by the statement** (the r1 consumer note):

> “[GT5-r1 consumer note: nondecreasing is all any named consumer of this lemma uses (GENTOW5-A Step B's grid translation, S3(c) Steps 0/3, S3(d)); the strict FLOW-UP pricing there comes from lam > E separately, never from this lemma's strict clause. The pre-repair blanket "the key-part of each carry strictly raises it" was FALSE at the top carry — and contradicted the lemma's own i = 2 instance: GENTOW1_PROOF S2 Step 0 prices the Phi_2-part "at weight E2 exactly" (PRESERVED). … Failure mode fenced, worked at the S4 witness chain's grid 4 (u = (1,5,21,85), E_4 = 170): the top carry Phi_3^2 = Phi_4 + 2^8*Phi_2 has wt_4(Phi_3^2) = 2*(ehat_4/ehat_4)*u_4 = 2*85 = 170, Phi_4-part = E_4 = 170, and lift-part wt(2^8*Phi_2) = 16*8 + 2*21 = 170 — all three EQUAL: any downstream lean on top-carry strictness would be unsound; none exists in this note (checked at PE1 and re-checked this round).]”

**RESOLUTION TRACE:** Base §S2.4, lines 644–727, restated by `[GT5-r1]` and edged by `[GT5-r2]`; the consequence clause and the converse-direction sentence are superseded out of range by S11.1 (resolution rule 4). S11.1's own consumption walk re-verifies that the in-range consumers (`.10` Step B, `.29` Steps 0/3, `.30`) use only the forward direction.

**SUPERSESSION KIND:** partial-withdrawal.

**TARGETS:** `EFF.GENTOW5.s1of2.25`'s blanket strictness clause, two-directional closure, and converse-direction sentence.

**CHAIN:** blanket strictness → `[GT5-r1]` interior-only strictness/top preservation → `[GT5-r2]` i=1 top-carry edge → S11.1 withdrawal of two-directional closure → **forward nondecreasing theorem + converse nonincreasing replacement TERMINAL**.

**REPLACEMENT DISPLAY:** “forward carry moves are `wt_i`-nondecreasing; converse rewriting is weight-NONINCREASING, preserved at the top rung and strictly lowered at interior rungs.”

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:S2 Step 0` — grep-verified count **2**; the i = 2 instance whose “Phi_2-part at weight E2 exactly” the restatement now matches.

**TEETH:** §S7 F-3's grid-4 equality instance (170 = 170 = 170); out of range, S11.1's isolated re-check `gentow5_af1_direction_check.py` (8 checks / 0 violations) exercises both directions.

---

### EFF.GENTOW5.s1of2.26  [scope-record]

**FORM:** bracketed rider

**CANONICAL STATEMENT:** `[ASSEMBLED — statement header plus post-PE5 scope fold]` THEOREM GENTOW5-B

> “**Statement.** Fix a base (Q; h) and a depth-r tower datum per DEF GENTOW5-1: stage data (e_i, f_i, psi_i) with properness l_i >= 2 (i >= 2), heights u_i satisfying the floor chain u_{i+1} > e_{i+1} E_i, keys Phi_1, ..., Phi_r built by THE RECIPE [GT5-r1: in its GAUGE-CORRECTED form — the S2.1 pin's vartheta-twisted khat_t; every clause below reads AT that form, and (a)/(b) are FALSE at the gauge-naive display on letter-live frames (PE1 FR-1's machine counter-instance, quoted at the S2.1 pin)], and the terminal inductive valuation nu_r (the MacLane chain mu_0 -(x, lam_1)-> mu_1 -(Phi_1, lam_2)-> ... -> mu_r = nu_r in FGMN coordinates, the GENTOW2 S2 dictionary at every level). Then, by induction on i < r:”

The index-0 scope, per the in-range acceptance fold (PE5-F-1), clause by clause:

> “[acceptance fold 2026-08-10 (PE5-F-1) — INDEX-0 SCOPE for (a)/(b)/(d), completing the post-PE4 rider's (c)/(e) scoping to the clause list. The blanket header's index i = 0 is claimed for (d) ONLY; (a) and (b), like (c) and (e), are claimed at induction indices i >= 1. Per clause, derived from this note's own displays: (a) at i = 0 is NOT claimed — its display dereferences w_0 = R_{1,kbar_0}(nhat_0(u_1)), and nhat_0 is not a DEF GENTOW5-1 object (the normalizer recursion bases at n1hat; nhat_i exists at i >= 1), so the twisted form is not well-formed at index 0. … (b) at i = 0 is NOT claimed by this proof (the (b)-cite enters through (a)'s certificate at the same index: Thm 6.3 consumes Phi_{i+1} in KP(nu_i) + prime, Cor 6.4 the non-equivalence step); its index-0 instance reduces to the j = 1 leg … (d) at i = 0 IS claimed and covered: its display is well-formed at index 0 (lift_1, dv_1, E_1 are DEF objects) and the instance is S1.4(ii)'s level-1 rider … The index-0 entry locus T_1 stays unclaimed per the (c) rider below; the PE5 fresh route instantiated it TRUE at one frame (f4 = Phi_1^2 - 25x over p = 5: level-0 read one side of kappa_1 = 1/2, residual (y-1)^2 = psi_1^2 mod 5, box at 5 = 2E_1 + 1 — gentow5_pe5_fresh.py, GREEN 40/0), so leaving it unclaimed costs the note nothing at the checked frame.]”

The fold also fixes how the header's own “keys built by THE RECIPE” reads:

> “Phi_1 := Phi' is the DEF-datum (S2.1 — so "keys Phi_1, ..., Phi_r built by THE RECIPE" reads honestly as Phi_2, ..., Phi_r recipe-built over the datum Phi_1; the recipe consumes nhat_i at i >= 1)”

**CONDITIONALITY:** Claimed index set by clause: (a) i ≥ 1; (b) i ≥ 1; (c) i ≥ 1; (d) i ≥ 0; (e) i ≥ 1. All clauses read at the gauge-corrected recipe. Out of range, S12.1 adds the `[GENTOW5-W(i)]` conditionality at every index n ≥ 3 for (a), (b), (c), (e).

**DERIVATION:** The fold's per-clause derivations are quoted above (well-formedness of the index-0 display for each clause, and where the index-0 content instead lives — the accepted T(b)′ datum and the GENTOW2 S2 dictionary).

**RESOLUTION TRACE:** Base §S3 statement header, lines 731–742, with `[GT5-r1]`'s gauge clause inline; the index-0 scope is the post-PE5 `[acceptance fold]` at lines 744–779, itself completing the post-PE4 `[rider]` scoping of (c)/(e) at lines 864–880.

**SUPERSESSION KIND:** scope-pin.

**TARGETS:** `EFF.GENTOW5.s1of2.26`'s blanket “by induction on i < r” reading.

**CHAIN:** blanket `i < r` → post-PE4 `(c)/(e): i ≥ 1` → **post-PE5 per-clause index set TERMINAL**: `(a),(b),(c),(e): i ≥ 1`; `(d): i ≥ 0`.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:S2` — grep-verified count **15**; the MacLane-chain dictionary consumed at every level.

**TEETH:** `gentow5_pe5_fresh.py` (GREEN 40/0) instantiates the unclaimed T_1 case TRUE at one frame; FR-1 is the counter-instance for the gauge clause.

---

### EFF.GENTOW5.s1of2.27  [lemma]

**FORM:** inline sentence

**CANONICAL STATEMENT:** `[ASSEMBLED — base clause plus effective r2/r4/r5 readings]` THEOREM GENTOW5-B clause (a) — KEY CERTIFICATE

> “(a) [KEY CERTIFICATE, level-general — GT5-r2 RE-SCOPED (PE2 F-1): the realized residual is the w-TWISTED form] Phi_{i+1} is a key polynomial for nu_i and a PRIME polynomial (monic, O-coefficients, irreducible over K_v), with
>
>     R_{nu_i}(Phi_{i+1}) = psi_{i+1}^{(w_i)}
>                         := w_i^{f_{i+1}} * psi_{i+1}(y / w_i),
>
> where w_i := R_{i+1,kbar_i}(nhat_i(u_{i+1})) in K_i^x is the single slot-independent CROSS-FRAME UNIT of the landed GENTOW2 r3 B-law (kbar_i := u_{i+1}/e(mu_i), the top slot's grade; at i = 2 this is LEMMA GENTOW2-B [r3 RESTATED] + LEMMA GENTOW2-B'''s w verbatim, GENTOW2_PROOF S5 @ d798529). psi_{i+1}^{(w_i)} is GENTOW2-A-ADMISSIBLE at each value of w_i — monic irreducible of degree f_{i+1} with nonzero constant term (y -> w*y is a substitution automorphism; B'' + the PE5 verification "psi_3^{(w)} is verifiably admissible for every w in K_2^x", GENTOW2_passPE5_report @ 75923bc) — and GENTOW2-A's hypothesis (ii) quantifier accepts it … THE w_i = 1 CASE IS OPEN: w_i is the uncomputed cross-frame unit ("not computed anywhere in the corpus" — GENTOW2 S5), and verdict-level machine data is w-blind, so no committed run discriminates it; R_{nu_i}(Phi_{i+1}) = psi_{i+1} on the nose is NOT claimed.”

with the in-range dated measurement note:

> “[DATED NOTE (2026-08-10, post-GENTOW2-PE6): GENTOW2's PE6 pass MEASURED w for the first time (fresh route GREEN 68/0, seal ade1727; report GENTOW2_passPE6_report.md @ deba21b, GENTOW2 ACCEPTED 2/2 there): w-avatar = z_1 (LD1), z_1^2 (LD3), z_2^2 (GA1), z_2 (GA3) — != 1 at each of the 6 measured primes across the 4 frames, and u_3-DEPENDENT within each tower. On the measured record the open w_i = 1 case is NOT the generic one: the psi^{(w)} form of this clause is the operative one. The quoted "not computed anywhere in the corpus" is dated by GENTOW2's post-PE6 acceptance record — measured at 4 frames; the closed-form letter derivation of w stays open, and the measured record does not decide w_i at unmeasured frames or levels i > 2.]”

and the clause's own w-blindness list:

> “sigma, values, degrees, irreducibility, and the REPO-side residue classes are w-blind — checked per consumer in the [GT5-r2] walk after (e).”

**CONDITIONALITY — three regimes, after the out-of-range appends.** S11.3 corrects the i = 1 instance:

> “Dated statement correction (honest re-scope, standing authority): clause (a) AT i = 1 reads
>
>     R_{nu_1}(Phi_2) = psi_2^{(u1)},  u1 in K_1^x a FIXED
>     z_1-letter-power unit (the letter formula's species);
>     the tie u1 = w_1 = R_{2,kbar_1}(nhat_1(u_2)) is OPEN.”

S11.2 fences i ≥ 3 behind the open lemma:

> “NOT PROVED at i >= 3: the single-w geometric form
>
>       [GENTOW5-W(i)]   u_i(beta_t) = theta_i(t) * w_i^{f_{i+1}-t},
>                        w_i = R_{i+1,kbar_i}(nhat_i(u_{i+1})),
>
>   which per-grade fixedness underdetermines (fixed families exist that fit no single w) — this is GENTOW2-B'''s computation run at level i, which this note does not reproduce. [GENTOW5-W(i)] is hereby an OPEN transported lemma, the honest-sorry analogue.”

S11.3's own summary of the three regimes:

> “Net position after S11.2 + S11.3: the pinned-w_i form is unconditionally realized at i = 2 exactly; at i = 1 the shape is proved with the tie open; at i >= 3 the form is open behind [GENTOW5-W(i)].”

S12.1 adds that at n ≥ 3 the certificate legs go with it: “Without \([{\rm GENTOW5\!-\!W}(n)]\), per-grade fixedness supplies no single substitution \(y\mapsto w_ny\), so none of those certificate legs is established for the pinned key.”

**DERIVATION:** [ASSEMBLED — the (B-1)/(B-2) legs and the FGMN certificate run, quoted] The proof opens by naming GENTOW2's level-uniformity proviso:

> “*(a) — GENTOW2-A's proof with r+1 for 4.* GENTOW2 S7 already recorded that THEOREM GENTOW2-A's proof pattern is level-uniform ("Cor 6.4 is proved for chains of any length r, and the recipe/bridge argument reads verbatim with r+1 in place of 4 PROVIDED the level-r analogues of (B-1)/(B-2) are proved"). The two provisos are now supplied:”

(B-1):

> “  (B-1 at level i) the dv_i ladder value of a deg < D_i ladder element equals its mu_i-value — this is LEMMA GENTOW5-C's (SLOT_i) value clause (exactness of the slot minimum), which identifies the grid minimum with the inductive-valuation value on deg < D_i polynomials at level-i points; at i <= 2 it is the accepted GENHN-2/2'.”

(B-2), at the landed GENTOW2 r3 B-law, with the cancellation computation that produces the surviving w-leg:

> “      u_i(beta_t) = theta_i(t) * w_i^{f_{i+1}-t},
>       theta_i(t) := res(nhat_i(u_{i+1}(f_{i+1}-t)) /
>                         nhat_i(u_{i+1})^{f_{i+1}-t}),
>       w_i := R_{i+1,kbar_i}(nhat_i(u_{i+1})) in K_i^x,
>
>   and theta_i(t) = vartheta_{i,f_{i+1}-t}^{-1} — the definitions are RECIPROCAL (S2.1's vartheta_{i,s} = res(nhat_i(u)^s / nhat_i(su)); same monomial quotient, inverse read). At the S2.1-pinned digit string — the statement's OWN keys, coherent digit c_t * vartheta_{i,f_{i+1}-t} — the B-law residual coefficient at y^t is therefore
>
>       u_i(beta_t) * (c_t * vartheta_{i,f_{i+1}-t})
>         = theta_i(t) * w_i^{f_{i+1}-t} * c_t * theta_i(t)^{-1}
>         = c_t * w_i^{f_{i+1}-t},
>
>   i.e. R_{nu_i}(Phi_{i+1}) = y^{f_{i+1}} - Sum_t c_t w_i^{f_{i+1}-t} y^t = w_i^{f_{i+1}} psi_{i+1}(y/w_i) = psi_{i+1}^{(w_i)}: the vartheta twist cancels the theta LEG ONLY; the w-leg SURVIVES.”

with the honesty fence attached to it:

> “Honest conditionality, named: what is consumed is the landed cocycle law (measured to its theta leg at PE4's decode 14/0 and derived as B''), never B-2 on-the-nose (u = 1), which is FALSE at letter-live grades; the w-leg is UNMEASURED (w-blind verdict data) and w_i = 1 is OPEN. (The alternative prescription c_t -> u_i(beta_t)^{-1}c_t would realize psi_{i+1} on the nose but builds a DIFFERENT key from the pinned recipe, and w_i being uncomputed it is not repo-constructible; the statement stays at the pinned key and the twisted residual.)”

and the certificate run itself:

> “With (B-1)/(B-2 as corrected), LEMMA GENTOW2-B's proof runs at level i on the pinned prescription: additivity (Cor 4.7(1) [Q8]) + eq (14) [Q7] give R_{nu_i}(Phi_{i+1}) = y^{f_{i+1}} - Sum c_t w_i^{f_{i+1}-t} y^t = psi_{i+1}^{(w_i)} as displayed; the degree-forcing display [Q6] + Lemma 5.3(2) [Q4] certify Phi_{i+1} in KP(nu_i) (admissibility of psi^{(w)} at each w — the statement's (a) clause); Lemma 1.11 [Q1] + Cor 1.13 [Q2] give prime. Non-equivalence to the previous key: R(Phi_{i+1}) = psi_{i+1}^{(w_i)} != 1 = R(Phi_i) by eq (14), Prop 5.7 [Q7]. ∎(a)”

The i = 1 line of the two level lists is supplied by the in-range acceptance fold (PE5-F-2), whose own disclaimer is what S11.3 then makes the statement's:

> “an exponent-level tie of the w_1 display to the letter formula is NOT claimed (no consumer on the record read needs it).”

**RESOLUTION TRACE:** Base §S3(a) statement (lines 781–820) and proof (lines 894–1003), rewritten by `[GT5-r1]` (F-2, the deleted `y -> eps*y` fallback), re-scoped by `[GT5-r2]` (PE2 F-1) at the landed GENTOW2 r3 law, dated by `[GT5-r3]` (PE3 F-2) at the measured record, completed at i = 1 by the post-PE5 `[acceptance fold]`; then corrected out of range by S11.2 (i ≥ 3 fence), S11.3 (i = 1 re-scope) and S12.1 (certificate legs conditional at n ≥ 3).

**SUPERSESSION KIND:** scope-pin.

**TARGETS:** `EFF.GENTOW5.s1of2.27`'s original on-the-nose residual and its later unconditional transported reading.

**CHAIN:** on-the-nose `psi_{i+1}` → `[GT5-r2] psi_{i+1}^{(w_i)}` → S11.3 **TERMINAL for i=1:** `psi_2^{(u1)}`, tie `u1=w_1` OPEN; landed GENTOW2 law **TERMINAL for i=2:** `psi_3^{(w_2)}`; S11.2 + S12.1 **TERMINAL for i≥3:** clause and certificate conditional on `𝒲_{≤i}`.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B″` — grep-verified count **11** (Unicode double prime; GENTOW5's ASCII `LEMMA GENTOW2-B''` has count **1** in GENTOW2_PROOF — see `.03`'s reading note).

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B′` — grep-verified count **9**; the B′(3)/(5) per-grade-unit law the r1 discharge consumed.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:S5.1` — grep-verified count **42**; the letter formula and the u(beta) definition.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:S7` — grep-verified count **1**; the level-uniformity proviso quoted verbatim above.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:[Q7]` — grep-verified count **9** (Prop 5.7 + eq (14)); `[Q6]` — count **4**; `[Q4]` — count **5** (Lemma 5.3); `[Q1]` — count **4** (Lemma 1.11); `[Q2]` — count **4** (Cor 1.13); `[Q8]` — count **8** (Cor 4.7).

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:Def 3.16` — grep-verified count **3**; the epsilon-normalized coordinate the u_i-family compares against.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:Lemma 3.17` — grep-verified count **7**; consumed in the B′(3) derivation.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:Cor 5.6` — grep-verified count **6**; the i = 1 fold's FGMN residual identification.

**TEETH:** PE1 fresh FR-1 (corrected vs gauge-naive key); GENTOW2 PE4 `@ 2f95be6` (B-2 on-the-nose machine-REFUTED at letter-live grades); GENTOW2 PE6 (w measured ≠ 1 at 6 primes / 4 frames); GENTOW2 PE5 `@ 75923bc` (admissibility of `psi_3^{(w)}` for every w).

---

### EFF.GENTOW5.s1of2.28  [lemma]

**FORM:** inline sentence

**CANONICAL STATEMENT:** `[ASSEMBLED — base clause, rider, and terminal residual-display corrections]` THEOREM GENTOW5-B clause (b) — ONE-SIDEDNESS AT EVERY LEVEL

> “(b) [ONE-SIDEDNESS AT EVERY LEVEL — the FGMN cite, arbitrary chain length] for every j <= i+1, the level-(j-1) polygon N_j(Phi_{i+1}) is one-sided of slope -lam_j with residual R_{j-1}(Phi_{i+1}) = psi_{j-1}^{l_j ... l_{i+1}}, and every root xi of Phi_{i+1} has the EXACT intermediate values v(Phi_{j-1}(xi)) = u_j / ehat_j — i.e. xi in P_{i+1}: the recipe's roots ARE depth-(i+1) node points.”

> “[GT5-r2 rider (PE2 F-1(iii)): each psi in the residual display reads at ITS level's twisted form per the re-scoped (a) — the FGMN residual powers inherit the per-level w-twists (psi^{(w)}-powers). The exact-value clause and the P_{i+1} clause are w-blind: P_{i+1} is defined by REPO residue classes, and the FGMN class is w times the repo class (B''), so a psi^{(w)}-root FGMN-side IS a psi-root repo-side — FR-A's machine leg carried psi_3 exactly repo-side.]”

**Superseded residual display (quoted; corrected out of range).** S11.5 `[A-F5]`:

> “Dated bracket on the statement's (b): the residual display "R_{j-1}(Phi_{i+1}) = psi_{j-1}^{l_j ... l_{i+1}}" dereferences psi_0 at j = 1 and fails the residual-degree count. Corrected, in this note's stage numbering:
>
>     R_{j-1}(Phi_{i+1}) = psi_j^{l_{j+1} ... l_{i+1}}
>     (1 <= j <= i+1; empty product = 1 at j = i+1),”

S12.1 then attaches the per-level twist, and the post-D3i corrigendum fixes the twist's index:

> “\[ R_{j-1}(\Phi_{n+1}) =\bigl(\psi_j^{(\omega_j)}\bigr)^{\,l_{j+1}\cdots l_{n+1}} \qquad(1\le j\le n+1), \]”

> “read every ψ_j^{(ω_j)} in S12.1's clause (b) as ψ_j^{(ω_{j−1})} with ω₁ = the S11.3 unit (the outer ψ₁ leg handled separately as accepted). The display as first written demanded w_{n+1} at the top term, exceeding the assumed 𝒲_{≤n}.”

**CONDITIONALITY:** At i = 2 unconditional (landed GENTOW2 law); at n ≥ 3 **all** of clause (b) is conditional on `𝒲_{≤n} := ⋀_{3≤q≤n}[GENTOW5-W(q)]`, S12.1 having withdrawn S11.2's contrary claim:

> “but its subsequent assertion that exact values, repo-side residue classes, \(P\)-membership, clause (c), and clause (e) remain unconditional is WITHDRAWN. A fixed per-grade unit family is not enough: “\(w\)-blind” means invariance AFTER the family has been proved to have the single-\(w_i\) geometric form. It does not construct that form.”

> “Corollary 6.4 fires only after clause (a) has supplied the key-polynomial/prime certificate for \(\Phi_{n+1}\).”

**DERIVATION:** Quoted proof:

> “*(b) — the cite fires at arbitrary r.* Theorem 6.3 [Q9] with F = phi = Phi_{i+1}, mu = nu_i (F = phi so phi |_mu F); Corollary 6.4 [Q10] with the length-(i+1) chain: its quantifier is "for any 1 <= j <= r" — THE ONE-SIDEDNESS IS LEVEL-GENERAL IN THE SOURCE; no per-level work remains. Its display (23) gives the residual powers R_{j-1}(F) = psi_{j-1}^{l_j...} and the middle clause mu(phi_j) = v(phi_j(theta)) gives the exact intermediate values at every root — with the psi_{j}-root residue classes from the residual power (no root besides psi_j's, the GENTOW2-A consumption note verbatim), every root lies in P_{i+1}. [GT5-r2: with the re-scope the FGMN residual powers are psi^{(w)}-powers, whose roots are w times the psi-roots; the repo transport divides by that w (B''), so the P_{i+1} membership — a REPO-class condition — is as stated. Statement rider + consumer walk below.] The repo polygon = FGMN polygon under the S2 shear (GENTOW2 S2, level-general as an affine map per level). ∎(b)”

S11.5's re-derivation of the corrected index (out of range, but it is the derivation of the effective display):

> “re-derived from the note's own rows: the level-(j-1) polygon of Phi_{i+1} has length l_j...l_{i+1}, and one full side of slope lam_j (gcd(u_j, e_j) = 1) carries residual degree l_j...l_{i+1}/e_j = f_j * l_{j+1}...l_{i+1} = deg of the corrected display (the composed display's degree f_{j-1}*l_j...l_{i+1} fails this count)”

**RESOLUTION TRACE:** Base §S3(b) statement (lines 821–833) and proof (lines 1005–1020); rider by `[GT5-r2]`; residual display re-indexed by S11.5; twist attached by S12.1 and re-indexed by the post-D3i corrigendum; conditionality set by S12.1 item 2.

**SUPERSESSION KIND:** replacement plus scope-pin.

**TARGETS:** `EFF.GENTOW5.s1of2.28`'s `psi_{j-1}` residual display and its former unconditional exact-value/P-membership reading.

**CHAIN:** `psi_{j-1}^{l_j⋯l_{i+1}}` → S11.5 `psi_j^{l_{j+1}⋯l_{i+1}}` → S12.1 `psi_j^{(ω_j)}` → **post-D3i `psi_j^{(ω_{j-1})}` TERMINAL (display consumer)**; former w-blind scope → **S12.1 `𝒲_{≤n}` TERMINAL (n≥3 consumer)**.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:[Q9]` — grep-verified count **4**; FGMN Theorem 6.3.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:[Q10]` — grep-verified count **6**; FGMN Corollary 6.4. **Source-display check:** the `[Q10]` quote block prints display (23) as “R_{i−1}(F) = (ψ_{i−1})^{ℓ_i}”, confirming S11.5's diagnosis that the base display transcribed the source's own index convention rather than this note's stage numbering.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:(23)` — grep-verified count **4**.

**TEETH:** §S4.2's P-B3 (10 polygons one-sided with on-chord support exactly the char-2 binomial spots) and §S5's P-B3 verdict row; FR-A's repo-side `psi_3` class row.

---

### EFF.GENTOW5.s1of2.29  [lemma]

**FORM:** inline sentence

**CANONICAL STATEMENT:** `[ASSEMBLED — re-indexed clause, scope rider, and Step-2 correction]` THEOREM GENTOW5-B clause (c) — BUDGETS AT LEVEL i+1

> “(c) [BUDGETS AT LEVEL i+1 — GENTOW-1 re-based. GT5-r3 RE-INDEXED (PE3 F-1): the composed display paired these (i+1)-anchored degree/weight/pin/floor clauses with an (i+2)-anchored entry-read clause ("level-(i+1) read, slope kappa_{i+2}, residual psi_{i+2}^{mu}"). That pairing fails the residual-degree count … and is refuted at the committed witness rows P-B3 f32@Phi4 and Phi4@Phi3 … The read clause below is the uniform GENTOW-1 transport 2 -> i+1 …] the level-(i+1) tower-entry locus T_{i+1} (monic f of degree n = mu * D_{i+1} whose level-i stage read exhibits the full side of slope kappa_{i+1} := u_{i+1}/e_{i+1} with residual psi_{i+1}^{mu} — the Phi_i-adic polygon of length mu * l_{i+1}, one side, residual degree mu*l_{i+1}/e_{i+1} = mu*f_{i+1} = deg psi_{i+1}^{mu}) is weight-characterized: f in T_{i+1} iff every slot of f - Phi_{i+1}^{mu} clears weight mu*E_{i+1} + 1, with the per-slot digit floors, the fibration, the node pins p_j >= (mu-j)E_{i+1} + 1, and the field floor dv_{i+1}(Phi_{i+1}(xi)) > E_{i+1}, exactly as in LEMMA GENTOW-1 (a)-(d).”

with the post-PE4 index scope:

> “[rider (post-PE4, 2026-08-10; PE4-F-1): SCOPE — clause (c), and clause (e) whose proof consumes (c)'s pins at the same index, are claimed at induction indices i >= 1 only (the entry loci T_2, ..., T_r): the proof's base is GENTOW-1 = the index-1 instance and each step enters at Phi_{i+2} (proving index i+1 from index-i data, i = 1..r-2), so the blanket header's index 0 is not covered and is NOT claimed. … Left unclaimed rather than cited.]”

**CONDITIONALITY:** Index `i >= 1` only. At n ≥ 3 conditional on `𝒲_{≤n}` (S12.1 item 3): “Thus clause (c) at index \(n\ge3\), including its sufficiency direction, deeper-read ascent, fibration, node pins, and field-floor conclusion, is conditional on \(\mathcal W_{\le n}\).”

**DERIVATION:** Quoted proof (the substitution table plus the five audited steps), with the r3 anchoring note:

> “*(c) — GENTOW-1's Steps 0-5 with the substitution table (D', e2, u2, E2, GENHN-2') -> (D_{i+1} composition data, e_{i+2}, u_{i+2}, E_{i+2}, (SLOT_{i+1})). [GT5-r3 (PE3 F-1): the table and the step displays below sit at ONE anchoring — the entered stage Phi_{i+2} (the composed table's garbled "E_{i+1} -> E_{i+2}" entry resolved to E_{i+2}). At that anchoring they prove the re-indexed statement (c) AT INDEX i+1 … with GENTOW-1 as the index-1 instance verbatim, indices 1..r-1 are covered.]*”

> “  Step 0 = LEMMA GENTOW5-D (proved level-agnostic; the ONLY level-sensitive content was the carry pricing, now uniform).
>   Step 1 (the key power's own development): R_{nu}(Phi_{i+2}^{mu}) = psi_{i+2}^{mu} by multiplicativity Cor 4.7(3) [Q8] — cleaner than the level-2 hand display; slots at weight >= mu*E_{i+2} with the graded layer psi-power by (b) + LEMMA GENTOW5-D's grid translation.
>   Step 2 (realizability): digits above floors put every slot of g := f - Phi_{i+2}^{mu}… above the side; the level-(i+1) stage read then shows the full side with residual psi^{mu} exactly ((SLOT_{i+1}) + Step 1). THE DEEPER READS: rather than the level-2 x-polygon display, run the entry ladder bottom-up: at level j (j <= i), given xi forced to P_j, the level-j read of f has pins = Phi_{i+2}^{mu}'s (g strictly above, by GENTOW5-D both grids agree on "above"), whose side residual is the psi_j-power of (b)+Cor 4.7(3); the zero-sum 0 = f(xi) forces the level-j side polynomial to vanish at the next residue class, i.e. the class is a psi_j-root: xi in P_{j+1}. Induction up to j = i+1, then Thm 6.3 fires on each prime factor (v(Phi_{i+1}(theta)) > nu(Phi_{i+1}) read off the top side) and Cor 6.4 pins the factor's data. [This replaces GENTOW-1 Step 2's outer-grammar display, which does not transpose as one line; the ladder argument is the classical Ore/Montes ascent and each rung is one (SLOT_j) read.]
>   Step 3 (necessity + fibration): verbatim — lattice-digit cancellation to one digit higher, off-lattice strictly above, Step 0 conversion, triangularity via monic division unipotent in the x-filtration (a composition of i+2 monic divisions now — the same unipotence).
>   Step 4 (node): (SLOT_{i+1}) reads p_j as the slot-min; equality realized in every residue class mod ehat_{i+2} by the ITERATED class separation (the CRT solve now runs down the recursion: choose b_{i+1} mod e_{i+2}, then descend — DEF GENTOW5-1's uniqueness clause).
>   Step 5 (field floor): every recipe side term at dv-height E_{i+2} exactly, common coherent normalizer, residue assembles to (unit)*psi_{i+2}(class) = 0, ultrametric strict — verbatim with the S1.2 cocycle in place of the level-2 wraps. ∎(c)”

**Superseded step (quoted; corrected out of range).** S11.1 identifies Step 2's parenthetical as the broken consumption of the withdrawn two-directional closure:

> “* S3(c) Step 2's parenthetical "(g strictly above, by GENTOW5-D both grids agree on 'above')" — THE BROKEN CONSUMPTION (the deeper reads at level j <= i sit across interior rungs, where the grids do NOT agree). Superseded by the derivation S11.1.1-S11.1.3; the ladder's conclusion stands on the new route.”

**Effective reading:** Step 2's aboveness is re-derived one-directionally through S11.1.1 (descent floor), S11.1.2 (the rho-ladder = the floor chain) and S11.1.3 (aboveness), all homed in shard 2; Step 1 and Step 3's necessity leg survive as written (S11.1's consumption walk).

**RESOLUTION TRACE:** Base §S3(c) statement (lines 834–880) and proof (lines 1022–1075), re-indexed by `[GT5-r3]` (PE3 F-1) and scoped by the post-PE4 `[rider]`; Step 2 superseded by S11.1; conditionality set by S12.1 item 3.

**SUPERSESSION KIND:** replacement plus scope-pin.

**TARGETS:** `EFF.GENTOW5.s1of2.29`'s mixed `(i+2)` entry-read pairing, broken Step-2 parenthetical, and former unconditional n≥3 scope.

**CHAIN:** mixed `(i+2)` read → `[GT5-r3]` uniform `(i+1)` read → S11.1 one-directional descent proof → **S12.1 conditional-on-`𝒲_{≤n}` reading TERMINAL for n≥3**.

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:LEMMA GENTOW-1` — grep-verified count **7**; the index-1 instance the transport re-bases.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:[Q8]` — grep-verified count **8**; Cor 4.7(3) multiplicativity at Step 1 (clause (3) verified at the quote block, see `.07`).

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:Theorem 6.3` — grep-verified count **5**; fired on each prime factor at Step 2.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:Cor 6.4` — grep-verified count **11**; pins the factor's data at Step 2.

**TEETH:** §S4.2/§S5's P-B3 rows: `f32@Phi4` and `Phi4@Phi3` REFUTE the retired (i+2)-pairing; `f32@Phi3` and `Phi4@Phi2` VERIFY the corrected pairing (both re-derived by hand at S9 and machine-checked at the post-PE4 rider's `gentow5_rider_f32dev.py`, 7 checks / 0 violations).

---

### EFF.GENTOW5.s1of2.30  [lemma]

**FORM:** inline sentence

**CANONICAL STATEMENT:** THEOREM GENTOW5-B clause (d) — REFINE TRANSFER AT LEVEL i+1, GENERAL mu

> “(d) [REFINE TRANSFER AT LEVEL i+1, GENERAL mu] at a composed event of integer dv_{i+1}-slope lam > E_{i+1} with residual (T-s)^{mu} (multiplicative convention), the refine Phi_{i+1}+ := Phi_{i+1} - lift_{i+1}(s; lam) kills the mu pins and bijects onto the lam-floored node — THEOREM GENTOW5-A's statement with 2 -> i+1.”

**CONDITIONALITY:** Claimed at index i ≥ 0 (the only clause the PE5 fold claims at index 0, discharged there by `.12`'s level-1 rider). S12.1's unaffected-scope sentence keeps it out of the `[GENTOW5-W(i)]` chain: “LEMMAS GENTOW5-A0/A1, the refine-transfer clause (d) at its stated event hypotheses, … remain unaffected.” Its lift is in range by S12.2: “THEOREM GENTOW5-A and clause (d)'s refine lifts also land in their required ranges”, since `λ > E_{i+1} > bound_{i+1}`.

**DERIVATION:** Quoted proof:

> “*(d)* — S1's proof is level-blind: LEMMA GENTOW5-A0 holds at any leaf field; LEMMA GENTOW5-A1's cocycle computation is S2.3's step (3) (the tau_i letter monomial); layer 2 = LEMMA GENTOW5-D + the flow-up pricing lam > E_{i+1} (the floor); layer 3 as in GENTOW-2. ∎(d)”

**RESOLUTION TRACE:** Base §S3(d) statement (lines 881–885) and proof (lines 1076–1080); index-0 coverage by the post-PE5 `[acceptance fold]`; lift-range discharge by S12.2.

**TEETH:** §S5's P-A1/A2/A3 (the pointwise mu2 = 3 kills at the composed key) are the i = 1 instances of this clause's mechanism.

---

### EFF.GENTOW5.s1of2.31  [lemma]

**FORM:** inline sentence

**CANONICAL STATEMENT:** THEOREM GENTOW5-B clause (e) — NODE-FLOOR COROLLARY

> “(e) [NODE-FLOOR COROLLARY = the floor chain's provenance] every side of the level-(i+1) composed polygon of an f in T_{i+1} has dv-slope > E_{i+1} > dv_{i+1}(x^{D_{i+1}}); hence the NEXT stage's height obeys u_{i+2} > e_{i+2} E_{i+1} automatically at tower leaves — the induction feeds itself (COR GENTOW-1.1 at every level).”

**CONDITIONALITY:** Index i ≥ 1 (the post-PE4 rider scopes (e) with (c)). At n ≥ 3 conditional on `𝒲_{≤n}` (S12.1 item 4), with the explicit carve-out that the inequality may still be used unconditionally when it is part of the fixed tower datum — only its *automatic derivation* is conditional.

**DERIVATION:** Quoted proof:

> “*(e)* — COR GENTOW-1.1's two-line convexity argument with E_2 -> E_{i+1}: pins >= (mu-j)E_{i+1} + 1 with right endpoint (mu, 0) force every side slope > E_{i+1}; and E_{i+1} = e_{i+1}f_{i+1} u_{i+1} > e_{i+1}f_{i+1} e_{i+1} E_i >= dv_{i+1}(x^{D_{i+1}}) = D_{i+1} * (ehat_{i+1}/e1) h by telescoping the floor chain down to E_1 = D_1 h. ∎(e)”

**RESOLUTION TRACE:** Base §S3(e) statement (lines 886–890) and proof (lines 1081–1086); scoped with (c) by the post-PE4 `[rider]`; conditionality set by S12.1 item 4. Re-verified at `[GT5-r3]`: “(e) consumes the pins + box at E_{i+1} (the sound half) and its conclusion u_{i+2} > e_{i+2}E_{i+1} matches DEF GENTOW5-1's floor-chain provenance one index down”.

**SUPERSESSION KIND:** scope-pin.

**TARGETS:** `EFF.GENTOW5.s1of2.31`'s automatic-next-floor claim at n≥3.

**CHAIN:** unconditional automatic derivation → **S12.1 conditional-on-`𝒲_{≤n}` automatic derivation TERMINAL**; explicit floor-chain datum remains independently usable.

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:COR GENTOW-1.1` — grep-verified count **4**; the two-line convexity argument transported.

**TEETH:** §S5's P-B1/B2 (“floor chain tight (u = 5, 21, 85, 341)”).

---

### EFF.GENTOW5.s1of2.32  [changes-record]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** `[ASSEMBLED — r2 walk plus terminal partial withdrawal]` THE RE-SCOPE'S CONSUMER WALK

> “**[GT5-r2] THE RE-SCOPE'S CONSUMER WALK (PE2 F-1 ripple — checked per consumer, no blanket claim).** Consumers of (a)/(b) inside this note, each read against the twisted residual psi^{(w_i)}:
> * (b)'s cite legs (Thm 6.3 [Q9] / Cor 6.4 [Q10]): consume Phi_{i+1} in KP(nu_i) + prime + the chain data — an ADMISSIBLE residual suffices (the (a) admissibility clause); the residual DISPLAYS inherit the per-level twists — carried by the (b) rider, no on-the-nose psi identification consumed.
> * (b)'s P_{i+1} clause: a REPO-class condition; FGMN class = w * repo class (B''), so it reads THROUGH the twist unchanged. Machine leg: FR-A's corrected key carried the psi_3-class repo-side exactly (gentow5_pe2_fresh.py, 22/0).
> * (c)'s budgets: T_{i+1} is DEFINED by the repo stage read (multiplicative convention) — weights, digit floors, fibration, node pins, field floor are value/repo-class data. Step 1's FGMN read becomes R_{nu}(Phi_{i+2}^{mu}) = (psi_{i+2}^{(w_{i+1})})^{mu} (Cor 4.7(3)); its repo-side translation is psi_{i+2}^{mu} by the SAME per-grade w-dictionary applied at the power — the repo-side clauses of (c) are w-blind. Step 2's ladder ascent consumes repo-side (SLOT_j) reads; w never enters.
> * (d)'s refine transfer: THEOREM GENTOW5-A is stated and proved in the multiplicative (repo) convention throughout — w-free.
> * (e)'s node floor: value arithmetic only — w-blind.
> * The S4 witness: K_i = F_2 at each rung, so K_i^x = {1} and w_i = 1 trivially — the witness does not discriminate the w-leg (its w-triviality is recorded at S6's TARGET-2 bullet's [GT5-r2] rider; the coverage box tracks the SEAM axis — S4.1's re-check — and carries no w row) [GT5-r3 pointer corrected, PE3 F-3].
> * sigma / degrees / irreducibility / factor patterns: y -> w*y is a substitution automorphism of K_i[y], factor patterns preserved at each w (B''; PE5's admissibility verification) — w-blind.
> * External consumers: none executed (S6's consumption path is candidates only); any future consumption of (a)/(b) must ride the w-annotation.”

**CONDITIONALITY — the walk's w-blindness verdicts are PARTIALLY WITHDRAWN out of range.** S12.1 states the distinction that breaks them at n ≥ 3:

> “A fixed per-grade unit family is not enough: “\(w\)-blind” means invariance AFTER the family has been proved to have the single-\(w_i\) geometric form. It does not construct that form.”

**Effective reading:** the walk stands as written at i = 2 (landed law) and at the S4 witness (K_i^× = {1}, “each required geometric law is tautological there”). At n ≥ 3 the (b)/(c)/(e) rows are conditional on `𝒲_{≤n}`; the (d) row survives (S12.1's unaffected list), and the sigma/degree/irreducibility row survives only downstream of an established twist.

**DERIVATION:** Per-consumer audit, quoted above; each row cites the mechanism (repo-class definition, value arithmetic, substitution automorphism) that makes it w-blind.

**RESOLUTION TRACE:** Base §S3, lines 1088–1121, added by `[GT5-r2]` (PE2 F-1 ripple), one pointer corrected by `[GT5-r3]` (PE3 F-3); partially withdrawn by S12.1.

**SUPERSESSION KIND:** partial-withdrawal.

**TARGETS:** `EFF.GENTOW5.s1of2.32`'s w-blind consumer claims for exact values, repo residue classes, P-membership, (c), and (e).

**CHAIN:** `[GT5-r2]` w-blind walk → **S12.1 partial withdrawal TERMINAL**; clause (d), formal monicity/degrees, recipe-height arithmetic, and the S4 witness survive.

**REPLACEMENT DISPLAY:** “At n ≥ 3 the named `(b)/(c)/(e)` consequences require `𝒲_{≤n}`; the expressly unaffected carve-outs remain unconditional at their stated hypotheses.”

**TEETH:** FR-A (`gentow5_pe2_fresh.py`, 22/0); PE5's admissibility verification.

---

### EFF.GENTOW5.s1of2.33  [scope-record]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** What the induction consumes, per rung (the honest pin stack)

> “**What the induction consumes, per rung (the honest pin stack).** Accepted 2/2: T(b)'(i)/(ii)/(iii) + GENHN-2/2' + S4 normalizers (rungs i <= 2). Cited at verified numbering: FGMN [Q1]-[Q10] (level-general by their own quantifiers; faithfulness per GENTOW2 S6, unchanged). Grade 0/2: GENTOW-1 (budgets pattern), GENTOW-2 (refine pattern), GENTOW2-A/B (cite pattern), THIS NOTE. HE7 ANNEX R's R1-b/R1-c ARGUMENT, consumed at rungs i >= 3 through LEMMA GENTOW5-C (the proof is reproduced tower-side, but its correctness precedent is the annex's — named, not hidden) [GT5-r1 dated fold: ACCEPTED 2/2 since a472155; see the S2.3 fold]. The depth->=4 region has machine contact ONLY through S4's witness (one exact instance) + HE7 R1.3's level-3 leg one ladder over; no count law at depth >= 3 is claimed measured.”

**CONDITIONALITY:** The “Grade 0/2 … THIS NOTE” row is superseded by the acceptance record (ACCEPTED 2/2); the grades of GENTOW-1/GENTOW-2/GENTOW2-A/B are their own notes' business and are not updated here.

**DERIVATION:** Inventory, not derivation.

**RESOLUTION TRACE:** Base §S3, lines 1123–1135; the annex-pin row folded by `[GT5-r1]`; this note's own grade superseded at lines 1671–1741.

XREF: `lean/notes/openmath/HE7_PROOF_2026-08-08.md:R1.3` — grep-verified count **5**; the level-3 machine leg named as the only other depth ≥ 3 contact.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:S6` — grep-verified count **25**; the FGMN faithfulness audit relied on for the cite row.

**NON-IMPORT (explicit):** “no count law at depth >= 3 is claimed measured.”

**TEETH:** S4's witness is the sole depth-4 machine contact (`.34`–`.36`).

---

### EFF.GENTOW5.s1of2.34  [instance-record]

**FORM:** inline sentence

**CANONICAL STATEMENT:** `[ASSEMBLED — chain, seam re-check, and terminal degree-32 member]` §S4.1 The minimal chain

> “q = 2, h = 1, all stages (e_i, f_i) = (2, 1), all psi_i = y - 1 (K_i = F_2 throughout — the minimal alphabet; properness l_i = 2). The floor chain u_{i+1} > e_{i+1}E_i = 4u_i admits the MINIMAL odd solutions u_{i+1} = 4u_i + 1 from u_1 = h = 1:
>
>     u = (1,) 5, 21, 85, 341;   E_i = 2u_i = (2,) 10, 42, 170;
>     dv_i = 2^i v;  D_i = 2^i.
>
> Keys by THE RECIPE (each khat = nhat_i(u_{i+1}), digit 1; S2.2's recursion solves):
>
>     Phi_1 = x^2 - 2
>     Phi_2 = Phi_1^2 - 4x            (nhat_1(5)  = 4x)
>     Phi_3 = Phi_2^2 - 16 Phi_1      (nhat_2(21) = 16 Phi_1)
>     Phi_4 = Phi_3^2 - 256 Phi_2     (nhat_3(85) = 256 Phi_2)
>
> (Phi_2, Phi_3 are the committed W1 objects of GENTOW2; Phi_4 is NEW — the first depth-4 key anywhere in the program.)”

> “The degree-32 member, one more tight rung (m\* = 4\*341/4... the top height m\* > e\*E_4 = 340, minimal odd 341 on dv_4):
>
>     f32 := Phi_4^2 - 2^16 Phi_3     (nhat_4(341) = 2^16 Phi_3),
>
> deg 32 = the first-live depth-4 degree (S2.1's arithmetic 2^{r+1}).”

**Seam re-check attached to the chain** (`[GT5-r1]`):

> “[GT5-r1 SEAM RE-CHECK (PE1 F-1's charge): this witness chain is GAUGE-SEAM-BLIND on two INDEPENDENT grounds — (i) K_i = F_2 at every level, so every letter (eta, beta_j) = 1 and vartheta is identically 1; (ii) every stage has f_{i+1} = 1, so the recipe's only slot is t = 0 with s = f - t = 1 and vartheta_{i,1} = 1 BY DEFINITION, letters notwithstanding. Corrected = naive khat at every rung; the displayed keys Phi_2/Phi_3/Phi_4 and f32 ARE the gauge-corrected recipe's outputs unchanged, and the committed sealed artifacts stand as-is. The witness therefore does not discriminate the seam — the seam-live machine leg is the PE1 fresh instrument's FR-1 frame, cited at the S2.1 pin.]”

**CONDITIONALITY:** One constructed chain, not a sweep. It is seam-blind (above) and w-trivial (`K_i^× = {1}`), so it discriminates neither the gauge seam nor the w-leg — both disclosed by the note and re-affirmed by S12.1 (“At S4 every \(K_i^\times=\{1\}\), so each required geometric law is tautological there”).

**DERIVATION:** The floor chain of `.14` forces `u_{i+1} > 4u_i`; the minimal odd solutions give the displayed ladder; the keys are `.18`'s recipe with digit 1 and the normalizers solved by `.15`/`.21`.

**RESOLUTION TRACE:** Base §S4.1, lines 1139–1175, with the `[GT5-r1]` seam re-check inserted at 1159–1169.

**RECORDED SOURCE DEFECT (not repaired by any later round):** the parenthetical “m\* = 4\*341/4...” is a truncated token in the source, of the same species as the `(LIFT_i)` bound's “e...” which PE5-F-3 restored. The sentence's conclusion is nevertheless complete and self-checking (`m* > e*E_4 = 340`, minimal odd `341`), and the value 341 is machine-confirmed at P-B4/P-C2. No repair is invented here.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:S5.1` — grep-verified count **42**; W1's committed Phi_2/Phi_3 objects live in the GENTOW2 witness stack.

**TEETH:** P-B1/B2 (floor chain tight); P-B4 and P-C2 (the two independent ladder routes); `genhnr2_supp.py` L387–389 independently carries `Phi3 = Phi2^2 - 16*Phi'` with `n2(21) = 16*Phi'`, matching `.21`.

---

### EFF.GENTOW5.s1of2.35  [preregistration]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** `[ASSEMBLED — selected preregistered prediction and tooth rows]` §S4.2 Preregistered predictions

> “By THEOREM GENTOW5-B (b)+(e) every root xi of f32 carries the EXACT ladder v(x) = 1/2, v(Phi_1) = 5/4, v(Phi_2) = 21/8, v(Phi_3) = 85/16, v(Phi_4) = 341/32; f32 is irreducible over Q_2 with e = 32, f = 1 (RAM leaf at the odd top height). Machine forms:
> * P-B4 (RESULTANT LADDER, exact-integer — the "nfeltval-only" route, PARI-free): v_2(Res(f32, g)) = 32\*v(g(xi)) for g = x, Phi_1, Phi_2, Phi_3, Phi_4 -> (16, 40, 84, 170, 341); and at the depth-4 KEY itself: v_2(Res(Phi_4, g)) -> (8, 20, 42, 85).
> * P-B3 (ONE-SIDEDNESS AT EVERY LEVEL — Cor 6.4's display, exact): the Phi_j-adic polygons of Phi_{i+1} and f32 are one-sided of the predicted slopes (5, 21, 85/2, 341/2 at the top reads; chords with on-chord support ONLY at the char-2-surviving binomial spots {0, l...}: e.g. Phi_1-adic Phi_4 on-chord at j in {0, 8} only, Phi_2-adic Phi_4 at j in {0, 4} only — (y+1)^{2^k} = y^{2^k}+1).
> * P-B1/B2 (grammar arithmetic): floor chain tight; every recipe side term at height E_{i+1} exactly.
> * P-C (PARI leg, DETACHED): factorpadic(f32, 2) returns ONE factor of degree 32; nfinit([f32,[2]]) + idealprimedec gives a single prime with (e, f) = (32, 1) and nfeltval ladder (16, 40, 84, 170, 341). Budgeted with timeout; infeasibility disclosed, not fatal.”

> “* T-B1 (tooth, the even-height mutant AT the node — STRONG FORM, hand-derived before the seal): f32m := Phi_4^2 - 2^20 Phi_1 (height 340 = 2\*E_4 exactly, gcd(340, 2) != 1). Derivation (pre-seal, disclosed): f32m = Phi_3^4 - 512 Phi_2 Phi_3^2 + 2^16(Phi_2^2 - 16 Phi_1) = Phi_3 \* (Phi_3^3 - 512 Phi_2 Phi_3 + 2^16) since Phi_2^2 - 16 Phi_1 = Phi_3 — the node-height digit hits the key relation exactly and the mutant COLLAPSES INTO THE DRAIN: Phi_3 | f32m over Z. Machine form: remainder(f32m, Phi_3) = 0, hence Res(f32m, Phi_3) = 0 (ladder entry infinite != 170) and the single-(e = 32)-factor read is refuted without PARI. The gcd != 1 proviso is machine-load-bearing at depth 4.”

**CONDITIONALITY:** Predictions are preregistered (sealed in the docstring before the first run, commit `4b279a7`); the PARI leg is detached and budgeted. The withdrawn over-claim about the PARI-free route's standalone strength is quoted at `.43` (F-6).

**DERIVATION:** The predicted ladder is clause (b)+(e) of THEOREM GENTOW5-B applied to the `.34` chain; the T-B1 derivation is the displayed exact factorization over `Z` using the key relation `Phi_2^2 - 16 Phi_1 = Phi_3`.

**RESOLUTION TRACE:** Base §S4.2, lines 1179–1219, with the `[GT5-r1]` F-6 wording correction inserted inside the P-C bullet.

**SUPERSESSION KIND:** withdrawal.

**TARGETS:** `EFF.GENTOW5.s1of2.35`'s counterfactual “P-B4 is the exact witness either way” clause.

**CHAIN:** PARI-free standalone-strength claim → **`[GT5-r1]` withdrawal TERMINAL**; the as-run two-route prediction and verdict survive.

**TEETH:** This unit IS the battery frame; its rows are inventoried in §5's inverse table.

---

### EFF.GENTOW5.s1of2.36  [run-record]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** §S4.3 Run record (VERDICT)

> “**GREEN on both routes.** Exact-integer route (P-B4, artifact `gentow5_output_exact.txt`): v2(Res(f32, g)) = (16, 40, 84, 170, 341) for g = (x, Phi_1, Phi_2, Phi_3, Phi_4) and v2(Res(Phi_4, g)) = (8, 20, 42, 85) — EXACT at the predicted rungs. PARI route (P-C, artifact `gentow5_output_full.txt`): factorpadic(f32, 2) = one degree-32 factor; nfinit([f32,[2]]) + idealprimedec = one prime with (e, f) = (32, 1); nfeltval ladder [16, 40, 84, 170, 341] EXACT. Polygon reads (P-B3): 10 polygons one-sided with on-chord support exactly the char-2 binomial spots, pin tables printed in the artifacts. T-B1 fired (drain collapse exact + `C4 nfactors=2 degs=[8, 24]`). **f32 = Phi_4^2 - 2^16 Phi_3 is the first depth-4 contact anywhere in the program: a degree-32, e = 32 witness whose four-rung intermediate ladder is exact on two independent routes.**”

**CONDITIONALITY:** One instance. Both artifacts are committed and byte-frozen at their md5s (`dc499a49…`, `839a8660…`).

**DERIVATION:** Run verdict, appended from the committed artifacts after the sealed run.

**RESOLUTION TRACE:** Base §S4.3, lines 1224–1236; untouched.

**TEETH:** This unit IS the verdict for P-B3/P-B4/P-C/T-B1.

---

### EFF.GENTOW5.s1of2.37  [instrument-record]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** `[ASSEMBLED — instrument seal, exact verdict, PARI verdict, and disclosure]` §S5 MACHINE LEG

> “INSTRUMENT: `verification/openmath/gentow5_checks.py`, sealed at commit 4b279a7 (predictions P-A1..A4, T-A1W/T-A2W/T-A4W, P-B1..B4, T-B1, P-C1..C4 in the docstring BEFORE the first run; the T-B1 drain factorization and the A-row residual arithmetic were hand-derived pre-seal and disclosed in S4.2/S1.2). Run 1: 85/86 — the single flag was an instrument-wiring defect in T-A1W's survivor comparison (the predicted survivor (j=2, slotmin 10) WAS in the alive list; the check read the first list entry — the wrong-height refine also drags the j = 0, 1 coordinates below their event pins, which is additional tooth-firing). Repaired + disclosed in the docstring (committed before re-run); no prediction changed; no reader/kill logic touched. UNIT NOTE (disclosed): the f32@\* and Phi4@Phi3 polygon rows print one dv-scale above the canonical N_j normalization; one-sidedness and on-chord support are affine-invariant.”

> “VERDICT RUN (exact leg, artifact `gentow5_output_exact.txt`):
>
>     GREEN — 86 checks, 0 violations, exit 0.
>     * P-A1/A2/A3 mu2 = 3 KILLS: all three pins die at all three
>       frames (q = 2; q = 3 char-3; K2 = F4 two-flavor lift) — the
>       FIRST mu2 = 3 pointwise re-division transports at the composed
>       key anywhere in the program (GN-REFINE3 one level up).
>     * P-A4 live-twist mu2 = 2 kill: the vartheta_2-corrected member
>       dies; T-A4W THE CONVENTION TOOTH FIRED: the naive-digit twin
>       keeps its pin at 22 exactly — LEMMA GENTOW5-A1's fixed-unit
>       dictionary is machine-load-bearing, not decorative.
>     * T-A1W (wrong height) and T-A2W (wrong digit, char 3, surviving
>       pin 33 exactly) FIRED as predicted.
>     * P-B1/B2: floor chain tight (u = 5, 21, 85, 341), recipe side
>       heights (10, 42, 170) = (E2, E3, E4) and top event 341 exact.
>     * P-B3: 10 polygons (Phi2/Phi3/Phi4/f32 at every lower key)
>       one-sided with on-chord support EXACTLY the char-2 binomial
>       spots {0, L} — Cor 6.4's display verified at depth 4, incl.
>       the pin tables printed in the artifact.
>     * P-B4 THE RESULTANT LADDERS: v2(Res(f32, ·)) =
>       (16, 40, 84, 170, 341) and v2(Res(Phi4, ·)) = (8, 20, 42, 85)
>       EXACT — the depth-4 witness by the PARI-free integer route.
>     * T-B1 FIRED: Phi3 | f32m exactly (remainder 0, resultant 0) —
>       the even-height-at-node mutant collapses into the drain.”

> “**GREEN — full run 92 checks, 0 violations** (86 exact + 6 PARI; `grep -c VIOLATION` = 0).”

**CONDITIONALITY:** Instrument-strength disclosure inside the C3 lines (`[GT5-r1]`, PE1 F-5):

> “[GT5-r1 instrument-strength disclosure (PE1 F-5): the sealed chk lines machine-assert only `C3a nfactors=1` + a deg=4 occurrence and `C3b nfactors=1`; the e = 4 values (and C3b's deg) are PRINTED to the committed artifact and human-verified in the quoted lines here, not chk-asserted — the sealed runner is byte-frozen, so the gap is recorded rather than retro-patched; any future battery revision should assert e and deg on both rows]”

**DERIVATION:** Run record; the preregistration discipline (docstring sealed before first run) is the derivation of its evidential weight.

**RESOLUTION TRACE:** Base §S5, lines 1240–1302; the F-5 disclosure inserted by `[GT5-r1]`.

**TEETH:** This unit IS the battery of record (92 checks / 0 violations); the inverse mapping is §5 below.

---

### EFF.GENTOW5.s1of2.38  [scope-record]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** `[ASSEMBLED — both target bullets with their dated riders]` §S6 — What this note PROVES

> “**What this note PROVES (grade 0/2, hostile arc owed):**
> * TARGET 1: THEOREM GENTOW5-A + LEMMAS GENTOW5-A0/A1 — LEMMA GENTOW-2 layer 1 at GENERAL mu2. GENTOW-BOX-1 is RETIRED as a mathematical box: the "composed graded frame" is gr(leaf field) (a graded division ring — elementary) + GENHN-2' (accepted) + the fixed-unit dictionary; no W-9-analogue weld face. Residue: this note's own arc grade; and the mu2 >= 3 machine rows are three constructed frames, not a sweep (GENTOW-BOX-2's coverage discipline applies to them verbatim).
> * TARGET 2: DEF GENTOW5-1 + LEMMAS GENTOW5-C/D + THEOREM GENTOW5-B — the level-r ladder grammar and the general-depth composition theorem, with the depth-4 witness EXACT on two independent routes. [GT5-r2: (a) holds at the TWISTED residual psi_{i+1}^{(w_i)} (GENTOW2-A-admissible at each w_i); w_i = 1 — the on-the-nose psi_{i+1} — is OPEN, the uncomputed cross-frame unit.] [GT5-r3 DATED 2026-08-10 (PE3 F-2): "uncomputed" is dated — w is MEASURED != 1 at the 7 measured primes (GENTOW2 PE6's 6 across LD1/LD3/GA1/GA3 + the PE3 fresh leg W's carrier-(8,4) prime at GA3\*, where psi_3^{(w)}(Y) = 0 held on the nose at w = z2); the closed-form w-law and unmeasured frames/levels stay open — see the S3(a) dated note.]”

**CONDITIONALITY:** “grade 0/2, hostile arc owed” is superseded by the acceptance record (**ACCEPTED 2/2**). The TARGET 2 supply is further narrowed out of range: at i ≥ 3 clauses (a)/(b)/(c)/(e) are conditional on `𝒲_{≤n}` (S12.1), at i = 1 clause (a) reads at S11.3's form.

**DERIVATION:** Supply inventory; each bullet's derivation is its named section.

**RESOLUTION TRACE:** Base §S6, lines 1306–1326, with the `[GT5-r2]` and `[GT5-r3]` brackets landed inline; grade superseded at lines 1671–1741; conditional narrowing at S11.2/S11.3/S12.1.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:COROLLARY W-9` — grep-verified count **3**; the twisted-algebra pin the note declares it does NOT need an analogue of.

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:GENTOW-BOX-2` — grep-verified count **2**; the coverage discipline imported for the three constructed frames.

**NON-IMPORT (explicit):** “no W-9-analogue weld face”.

**TEETH:** §S5's A-rows for TARGET 1; §S4/§S5's B-rows for TARGET 2.

---

### EFF.GENTOW5.s1of2.39  [scope-record]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** §S6 — Named conditionality stack (per consumer)

> “**Named conditionality stack (per consumer):**
> * Accepted 2/2: LEMMA GENHN-T(b)'(i)/(ii)/(iii), GENHN-2/2', the S4 coherent normalizers, the [r1] node floor (= floor chain rung 1).
> * Cited at verified numbering: FGMN [Q1]-[Q10] via GENTOW2_PROOF S3 (Cor 6.4's level quantifier "for any 1 <= i <= r" carries the one-sidedness at every depth; faithfulness audit GENTOW2 S6).
> * Grade 0/2 (same campaign, hostile arcs owed): GENTOW-1, GENTOW-2 layers 2-3, GENTOW2-A/B, THIS NOTE.
> * HE7 ANNEX R's R1-a/R1-b/R1-c ARGUMENT — consumed at rungs i >= 3 through LEMMA GENTOW5-C (reproved tower-side, but the argument's precedent and its hostile scrutiny live in the annex). [GT5-r1 DATED FOLD 2026-08-10 (PE1 F-4; orchestrator-authorized, ledger B8 87a7b61): the annex stack is ACCEPTED 2/2 — annexpass CLEAN 1/2 (4a613d8), annexpass2 CLEAN "the annex stack is ACCEPTED 2/2" (a472155); the HETOW acceptance record (e38df9f) consumes it. The composition-time cap sentence ("THE GRADE CAP FOR DEPTH >= 3 CLAIMS IS THIS PIN plus this note's arc") is LIFTED to the acceptance grade on the annex leg: the remaining depth >= 3 grade cap is this note's own arc plus the campaign-0/2 notes it consumes (GENTOW-1/-2, GENTOW2-A/B) — the annex pin no longer caps below acceptance.]”

**CONDITIONALITY:** “THIS NOTE” at grade 0/2 is superseded (ACCEPTED 2/2). The other notes' grades are as recorded here and are not updated by this shard.

**DERIVATION:** Inventory.

**RESOLUTION TRACE:** Base §S6, lines 1328–1348; annex row folded by `[GT5-r1]`.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:LEMMA GENHN-T(b)` — grep-verified count **11**.

XREF: `lean/notes/openmath/HE7_PROOF_2026-08-08.md:ANNEX-LEMMA R1-a` — grep-verified count **6**.

**READING NOTE (external, not an edit).** The FGMN cite row is covered corpus-wide by `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` **NS-12**, whose verdict for the `[Q1]`–`[Q10]` inventory consumed by GENTOW2/GENTOW5 is **COVERS-ALL-O** — i.e. no retarget is needed for these cites (unlike the Ore/GMN rows handled elsewhere in that document).

**TEETH:** NONE (inventory).

---

### EFF.GENTOW5.s1of2.40  [open-obligation]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** `[ASSEMBLED — base coverage bullet plus r1/r2 coverage riders]` §S6 — Machine coverage

> “* Machine coverage (GENTOW5-BOX-A): CHECK-A exercises mu2 in {2,3}, q in {2,3}, K2 in {F2, F3, F4}, e2 in {1,2}, f2 in {1,2}, d = 1, depth 2; CHECK-B exercises ONE depth-4 chain (all-(2,1) stages, q = 2, minimal heights). The proofs are uniform in the stage data; the coverage gap is machine-side, named here. The vartheta direction (theta vs theta^{-1}) is machine-tested only up to self-inverse units (F3; disclosed at T-A4W) — an F5-frame or F4-live-twist row would pin it; proof-side the direction is S1.2's derivation.”

> “[GT5-r1 THE SEAM AXIS (PE1 F-1's coverage finding — the axis this box omitted at composition): the committed battery is GAUGE-SEAM-BLIND BY CONSTRUCTION. CHECK-B is q = 2 with every f_i = 1 (vartheta trivialized twice over — S4.1 re-check); CHECK-A's only eta != 1 frame (A-2/A-4, p = 3, eta = 2) has f2 = 1, where W = 0 and naive = corrected. No committed row exercises the recipe at a letter-live frame with f_stage >= 2. The seam-live row that exists is the PE1 fresh instrument's FR-1 (gentow5_pe1_fresh.py + artifact @ 0160b94, 15/0: corrected key = carrier sigma (2,2) + exact ladder; naive key sigma {(4,1)} — the tooth). A letter-live recipe row inside this note's OWN battery remains a named gap (sealed runner byte-frozen; the fresh instrument is the current coverage).]”

> “[GT5-r2 THE COMPOUND ROW (PE2 F-4): seam-live x e_stage >= 2. The seam-live machine contact that exists is e-TRIVIAL at the live stage — FR-1 has e_2 = 1, and PE2's FR-A (the first seam-live depth-3 chain) has e_2 = e_3 = 1 — while the committed battery is seam-blind (above); the program's committed rows thus leave the compound (vartheta live x e_{i+1} >= 2) with NO machine contact. That compound is where the multiplicative slot convention reads THROUGH the mod-e_{i+1} class separation (S2.3 step (3)). Proof-side the S2.3 derivation is uniform in e_{i+1}; this row is a coverage fact — an honest named gap, coverage-box precision only.]”

**CONDITIONALITY:** These are declared *machine-side* gaps, not proof gaps: the note asserts the proofs are uniform in the stage data and locates the missing coverage precisely (letter-live × f_stage ≥ 2; letter-live × e_stage ≥ 2; the vartheta direction beyond self-inverse units).

**DERIVATION:** Coverage audit of the committed rows against the parameter axes.

**RESOLUTION TRACE:** Base §S6, lines 1349–1380, with the seam axis added by `[GT5-r1]` and the compound row by `[GT5-r2]`.

**TEETH:** This unit IS the note's honest teeth-coverage record; FR-1 and FR-A are its named partial coverage.

---

### EFF.GENTOW5.s1of2.41  [open-obligation]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** §S6 — What stays OPEN (not claimed)

> “**What stays OPEN (not claimed):** tower COUNT laws at depth >= 3 (no ledger, no measurement); partial inner sides ([GENHN-TOW-1] item (4)) at every depth; the genre-general faithfulness geography (item (3)); sigma laws behind [GENHN-HE(mu >= 3)] wherever the top problem has mu >= 3 — none of these is touched by GENTOW5-B, which is a carrier/read/budget/refine theorem, not a density display.”

**CONDITIONALITY:** The list is the note's own negative claim set.

**DERIVATION:** Declaration.

**RESOLUTION TRACE:** Base §S6, lines 1382–1387; untouched.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:[GENHN-TOW-1]` — grep-verified count **19**; items (3) and (4) are named there.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:[GENHN-HE(μ ≥ 3)]` — grep-verified count **7** (Unicode form; GENTOW5's ASCII rendering `[GENHN-HE(mu >= 3)]` has count **0** in GENHN_PROOF — orthography, see `.03`).

**TEETH:** NONE (negative claim).

---

### EFF.GENTOW5.s1of2.42  [scope-record]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** §S6 — Consumption path (not executed here)

> “**Consumption path (not executed here):** GENTOW1_PROOF's S3 grade note and S6 GENTOW-BOX-1, GENHN_PROOF's GENHN-BOX-2 and [GENHN-TOW-1] item (6) depth->=4 sentence, and GENTOW2_PROOF S7's depth->=4 bullet are candidates for the orchestrator's dated consumption updates after this note's own hostile arc; the four source notes are byte-untouched by this unit.”

**CONDITIONALITY:** This is the APPEND/consumption PROTOCOL predicate of the header's scope split. It asserts that **no** dated append had been landed on any source note by this unit; the four named targets are *candidates*.

**DERIVATION:** Declaration.

**RESOLUTION TRACE:** Base §S6, lines 1389–1394; untouched by S7–S12 (none of the later appends claims to land a consumption append on a source note).

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:GENTOW-BOX-1` — grep-verified count **5**; the candidate consumption site.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN-BOX-2` — grep-verified count **5**; likewise.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:S7` — grep-verified count **1**; the depth ≥ 4 bullet.

**TEETH:** NONE (protocol declaration).

---

### EFF.GENTOW5.s1of2.43  [changes-record]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** `[ASSEMBLED — repair header, six findings, and closing status]` §S7 `[GT5-r1]` PE1 REPAIR RECORD

> “PE1 verdict (GENTOW5_passPE1_report.md @ 0160b94): NOT CLEAN — 1 CRITICAL (F-1) + 2 GAP (F-2, F-3) + 3 MINOR (F-4, F-5, F-6); counter stays 0/2. This section is the r1 repair round. Tag convention: this round's edits are marked [GT5-r1]; bare [r1] in the body refers, as composed, to GENHN-1's node-floor erratum. Sealed machine artifacts BYTE-FROZEN at their committed md5s (gentow5_checks.py 5fa684c7..., gentow5_output_exact.txt dc499a49..., gentow5_output_full.txt 839a8660...); no runner edited, no re-run. Pre-r1 note body md5 02deb7e0 (43,779 bytes = the 87a7b61-era file, the PE1 target state).”

The six items, each landing on an in-range unit:

> “* **F-1 (CRITICAL) -> REPAIRED at the S2.1 GAUGE PIN.** … Ripple pins: S3 statement (keys = corrected recipe), S2.4 (value-blind), S4.1 (witness seam-blind on two grounds), S6 coverage box (the seam axis added). No fresh frames composed: FR-1 suffices as the seam-live verification, per the charge.
> * **F-2 (GAP) -> REPAIRED in S3(a).** The y -> eps\*y fallback (deleted as false at its source, GENTOW2 r1 dd44d20) is replaced by GENTOW2-B'(3)/(5)'s per-grade-unit law with the re-parameterization discharge; B-2 on-the-nose is named machine-REFUTED at letter-live grades (GENTOW2 PE4 @ 2f95be6) and is NOT consumed. …
> * **F-3 (GAP) -> REPAIRED in S2.4.** Top-grid weight DEFINED (Phi_i at E_i); strict clause restricted to interior carries (rungs 1..i-1, in-datum); top carry priced PRESERVED — the i = 2 instance now matches GENTOW1 S2 Step 0 verbatim; grid-4 equality instance worked (170 = 170 = 170).
> * **F-4 (MINOR) -> FOLDED (orchestrator-authorized, ledger B8 87a7b61).** HE7 ANNEX R pin lifted to ACCEPTED 2/2 (4a613d8 -> a472155; HETOW acceptance e38df9f consumes it) at S2.3, the S3 pin stack, and the S6 cap sentence.
> * **F-5 (MINOR) -> DISCLOSED at S5's C3 lines** (chk asserts nfactors only; e/deg human-verified from the artifact; runner byte-frozen).
> * **F-6 (MINOR) -> WITHDRAWN at S4.2 P-C** (the "either way" clause; the as-run two-route record stands).”

F-2's mid-round update carries its own later correction, landed in place:

> “[GT5-r2 CORRECTION (PE2 F-1): the clause "consistent both ways; the S3(a) text stands as written" that closed this bullet was WRONG at the w-leg, as was the S3(a) in-flight pin's sentence (removed at the r2 rewrite there) "realizes psi_{i+1} with NO re-parameterization (its vartheta twist IS the u-family)": the vartheta twist cancels theta(t) ONLY, and the landed law's second leg w^{f_3-t} survives — at the pinned recipe the realized residual is psi_{i+1}^{(w_i)}, not psi_{i+1} (open unless w_i = 1, the uncomputed cross-frame unit). The PRECISE statement: (i) the landed u IS an instance of the per-grade x0-free family, so the r1 discharge's EXISTENCE leg stands; (ii) the r1 discharge's re-parameterized key is NOT the statement's pinned key (digits differ by w-powers), so (a) at the pinned key required the r2 re-scope to psi^{(w_i)} — S3(a) as rewritten this round.]”

> “Grade: 0/2 UNCHANGED (this is a repair round, not a pass); PE2 next. TARGET 1 (GENTOW5-A/A0/A1) was not at stake and is untouched beyond the pins named here.”

**CONDITIONALITY:** Historical record; its closing grade sentence is superseded by the acceptance record. The F-6 withdrawal is the note's own retraction of a counterfactual claim, quoted at `.35`'s trace.

**DERIVATION:** Repair-round bookkeeping; each item's mathematical derivation lives at the unit it repaired (`.18`, `.27`, `.24`/`.25`, `.22`, `.37`, `.35`).

**RESOLUTION TRACE:** Base §S7, lines 1396–1473; F-2's closing clause corrected in place by `[GT5-r2]`. This is the last section homed in the shard: S8 begins at line 1475.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN-1` — grep-verified count **11**; the note whose node-floor erratum the bare `[r1]` tag denotes.

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:S2 Step 0` — grep-verified count **2**; F-3's matching instance.

**TEETH:** F-3's grid-4 equality instance; FR-1 for F-1; GENTOW2 PE4 `@ 2f95be6` for F-2.

---

## 3. Consumption tables

### 3.1 Verified import/XREF designations

Every designation below was checked with fixed-string `grep -cF` in the named target file. Counts are recorded per `EFF_TEMPLATE_v2.md` rule 2.

**[TABLE]**

| # | Target and designation | Count | Material consumed by GENTOW5 §§1–1474 |
|---:|---|---:|---|
| 1 | `GENTOW1_PROOF_2026-08-09.md:LEMMA GENTOW-1` | 7 | Budgets template re-based at clause (c) |
| 2 | `GENTOW1_PROOF_2026-08-09.md:LEMMA GENTOW-2` | 7 | The event setting; layers 2/3 imported, layer 1 is the box |
| 3 | `GENTOW1_PROOF_2026-08-09.md:LEMMA GENTOW-5` | 6 | Named in SOURCES CONSUMED |
| 4 | `GENTOW1_PROOF_2026-08-09.md:COR GENTOW-1.1` | 4 | Clause (e)'s convexity argument |
| 5 | `GENTOW1_PROOF_2026-08-09.md:Step 0` | 11 | Carry pricing consumed at GENTOW5-A Step B |
| 6 | `GENTOW1_PROOF_2026-08-09.md:S2 Step 0` | 2 | The i = 2 instance matched by the GENTOW5-D restatement |
| 7 | `GENTOW1_PROOF_2026-08-09.md:Step 5` | 3 | The S4 computation re-run for the second wrap letter |
| 8 | `GENTOW1_PROOF_2026-08-09.md:S3` | 14 | Level-2 normalizers; layers 2/3 at general mu2 |
| 9 | `GENTOW1_PROOF_2026-08-09.md:GENTOW-BOX-1` | 5 | The box this note retires; a consumption candidate |
| 10 | `GENTOW1_PROOF_2026-08-09.md:GENTOW-BOX-2` | 2 | Coverage discipline for constructed frames |
| 11 | `GENTOW1_PROOF_2026-08-09.md:[GT1-r1]` | 5 | Erratum pin precedent for the gauge twist |
| 12 | `GENTOW2_PROOF_2026-08-09.md:THEOREM GENTOW2-A` | 8 | Admissibility quantifier; clause (d)'s i = 2 node data |
| 13 | `GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B` | 32 | The cite pattern run at level i |
| 14 | `GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B′` | 9 | Per-grade unit family (B′(3)/(5)) |
| 15 | `GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B″` | 11 | The landed r3 B-law's `w` and the root correspondence |
| 16 | `GENTOW2_PROOF_2026-08-09.md:S5.1` | 42 | `u(beta)` definition + the letter formula |
| 17 | `GENTOW2_PROOF_2026-08-09.md:S2` | 15 | MacLane-chain dictionary / polygon shear |
| 18 | `GENTOW2_PROOF_2026-08-09.md:S6` | 25 | FGMN faithfulness audit |
| 19 | `GENTOW2_PROOF_2026-08-09.md:S7` | 1 | Level-uniformity proviso; depth ≥ 4 bullet (consumption candidate) |
| 20 | `GENTOW2_PROOF_2026-08-09.md:[Q1]` | 4 | FGMN Lemma 1.11 (prime) |
| 21 | `GENTOW2_PROOF_2026-08-09.md:[Q2]` | 4 | FGMN Cor 1.13 (prime) |
| 22 | `GENTOW2_PROOF_2026-08-09.md:[Q4]` | 5 | FGMN Lemma 5.3(1)/(2) (KP membership) |
| 23 | `GENTOW2_PROOF_2026-08-09.md:[Q6]` | 4 | Degree-forcing display |
| 24 | `GENTOW2_PROOF_2026-08-09.md:[Q7]` | 9 | FGMN Prop 5.7 + eq (14) |
| 25 | `GENTOW2_PROOF_2026-08-09.md:[Q8]` | 8 | FGMN Cor 4.7 — clause (1) additivity, clause (3) multiplicativity |
| 26 | `GENTOW2_PROOF_2026-08-09.md:[Q9]` | 4 | FGMN Theorem 6.3 |
| 27 | `GENTOW2_PROOF_2026-08-09.md:[Q10]` | 6 | FGMN Corollary 6.4 + display (23) |
| 28 | `GENTOW2_PROOF_2026-08-09.md:(23)` | 4 | The source display re-indexed by S11.5 |
| 29 | `GENTOW2_PROOF_2026-08-09.md:Def 3.16` | 3 | ε-normalized coordinate (the u_i-family's other side) |
| 30 | `GENTOW2_PROOF_2026-08-09.md:Lemma 3.17` | 7 | Consumed in the B′(3) derivation |
| 31 | `GENTOW2_PROOF_2026-08-09.md:Cor 5.6` | 6 | The i = 1 fold's FGMN residual identification |
| 32 | `GENTOW2_PROOF_2026-08-09.md:Lemma 3.5` | 1 | Improper-stage collapsing |
| 33 | `GENTOW2_PROOF_2026-08-09.md:Prop 3.7` | 1 | Improper-stage collapsing |
| 34 | `GENTOW2_PROOF_2026-08-09.md:Theorem 6.3` | 5 | Fired per prime factor at (c) Step 2 |
| 35 | `GENTOW2_PROOF_2026-08-09.md:Cor 6.4` | 11 | Pins the factor data at (c) Step 2 |
| 36 | `GENHN_PROOF_2026-08-08.md:GENHN-2′` | 3 | Exact slot minimum, one digit per height (i = 2 base) |
| 37 | `GENHN_PROOF_2026-08-08.md:GENHN-2` | 28 | The i = 1 base of (SLOT) |
| 38 | `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-4` | 3 | Level-1 assembly display; layer-2 substitute in the rider |
| 39 | `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-T(b)` | 11 | The accepted depth-2 tower datum (i)/(ii)/(iii) |
| 40 | `GENHN_PROOF_2026-08-08.md:GENHN-BOX-2` | 5 | Retirement condition matched by the level-1 rider; consumption candidate |
| 41 | `GENHN_PROOF_2026-08-08.md:[GENHN-TOW-1]` | 19 | Items (3)/(4)/(6): open list + consumption candidate |
| 42 | `GENHN_PROOF_2026-08-08.md:[GENHN-HE(μ ≥ 3)]` | 7 | The sigma-law gate left open |
| 43 | `GENHN_PROOF_2026-08-08.md:COROLLARY W-9` | 3 | The twisted-algebra pin explicitly NOT needed |
| 44 | `GENHN_PROOF_2026-08-08.md:GN-REFINE3` | 5 | The pattern the mu2 = 3 kills instantiate one level up |
| 45 | `GENHN_PROOF_2026-08-08.md:T22` | 9 | The (T22)-transport for the second wrap letter |
| 46 | `GENHN_PROOF_2026-08-08.md:GENHN-1` | 11 | The bare `[r1]` node-floor erratum's home |
| 47 | `GENHN_PROOF_2026-08-08.md:W(t) = ⌊(f₂−t)·i(u₂)/e₁⌋` | 1 | The erratum exponent law reproduced by `vartheta_{1,s}` |
| 48 | `GENHN_PROOF_2026-08-08.md:ĉ_t := lift(c_t·η^{W(t)})` | 1 | The erratum's corrected digit (GENTOW5's ASCII `chat_t`) |
| 49 | `HE7_PROOF_2026-08-08.md:ANNEX-DEF HE7-2′` | 6 | The normalizer recursion re-based tower-side |
| 50 | `HE7_PROOF_2026-08-08.md:ANNEX-LEMMA R1-a` | 6 | Clause (iii) = the cocycle letter statement |
| 51 | `HE7_PROOF_2026-08-08.md:ANNEX-THEOREM R1-b` | 4 | (SLOT_i) precedent proof |
| 52 | `HE7_PROOF_2026-08-08.md:ANNEX-THEOREM R1-c` | 3 | (LIFT_i) precedent proof + the bound recursion |
| 53 | `HE7_PROOF_2026-08-08.md:R1.2` | 7 | Monomial identity; item 3 (coherence) and item 7 (twist-blindness) |
| 54 | `HE7_PROOF_2026-08-08.md:R1.3` | 5 | The level-3 machine leg named in the pin stack |
| 55 | `HE7_PROOF_2026-08-08.md:HE7-T-BADTWIST` | 7 | The false stronger claim the S2.3 remark fences off |
| 56 | `HE6_PROOF_2026-08-08.md:LEMMA HE6-1` | 15 | The transport identity in GENTOW5-C's i = 1 base |
| 57 | `JD0_PROOF_2026-08-08.md:J-D0` | 25 | Counts twist-blind / letters re-coordinatize |

**ARITHMETIC AUDIT:** 57 designation rows; the fresh sum of the 57 fixed-string occurrence counts is **475**. This is a raw-occurrence checksum, not a count of distinct mathematical imports. All 57 row counts were recomputed; three changed because `GENTOW2_PROOF_2026-08-09.md` grew after the opus draft (`LEMMA GENTOW2-B`: 30→32; `B′`: 8→9; `B″`: 10→11).

**Designation counted but NOT emitted as an XREF:** `GENTOW2-A(d)` (count **0** in GENTOW2_PROOF). The parent designation `THEOREM GENTOW2-A` is verified (row 12); the clause letter is not separately greppable there, so the clause reference is carried descriptively rather than as a designation.

### 3.2 Pin verification ledger

Per template rules 23 and 34, commits were checked with `git cat-file -t`; artifacts were checked for existence, and the sealed core artifacts were also re-md5ed.

**[TABLE]**

| Pin class | Pins checked | Fresh disposition |
|---|---|---|
| Source blob / last-touch commit | `00a4c7e80cfd652bc4416edb476d44ae6ca0a420`; `ddfc6b61` | Blob recomputed; commit object verified |
| Referenced commits | `0160b94`, `18900e03`, `2f95be6`, `39c36aa`, `40f313a`, `477b1b1`, `4a613d8`, `4b279a7`, `59c1966`, `75923bc`, `87a7b61`, `9f0eca7`, `a472155`, `ade1727`, `b22b37b`, `cb010522`, `d798529`, `dd44d20`, `deba21b`, `e38df9f` | All 20 resolve as `commit` |
| Sealed runner | `verification/openmath/gentow5_checks.py` | Exists; md5 `5fa684c74326aea31d2b065b373fcf22` |
| Exact output | `verification/openmath/gentow5_output_exact.txt` | Exists; md5 `dc499a4967537d157756905c21104acb`; verdict 86 checks / 0 violations |
| Full output | `verification/openmath/gentow5_output_full.txt` | Exists; md5 `839a866006f9f6fc341a789c463a763a`; verdict 92 checks / 0 violations |
| Fresh instruments | `gentow5_pe1_fresh.py`, `gentow5_pe2_fresh.py`, `gentow5_pe3_fresh.py`, `gentow5_pe5_fresh.py` under `verification/openmath/` | All exist |
| Repair helpers | `gentow5_rider_f32dev.py`, `gentow5_af1_direction_check.py` under `verification/openmath/` | Both exist; md5s `81bbb5db3a8a40b211a7f1101d865e91`, `82acd3d2f48e5d03b50c4e2cf181370b` |
| Cross-check runner | `verification/openmath/genhnr2_supp.py` | Exists; md5 `51154c9501156d9c14917ae35a274c1e` |
| Pass reports | GENTOW5 PE1–PE5; GENTOW2 PE5/PE6; HE7 annexpass/annexpass2 under `lean/notes/openmath/` | All 9 named report files exist |
| External reading records | `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md`, `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` | Both exist |
| Historical body md5 `02deb7e0…` | Pre-r1 body named by S7 | **AS-OF-PIN**: honest at append time, not a current whole-file checksum after designed insertions/appends |

**ARITHMETIC AUDIT:** 11 pin rows: 1 source-blob row, 1 grouped row of 20 verified commits, 7 current artifact/report/resource rows, 1 external-record row, and 1 AS-OF-PIN row. The two output verdicts cross-check `86 exact + 6 PARI = 92 full`; both report 0 violations.

No reported in-range run lacks a filename: **zero UNPINNED run records**.

### 3.3 Reverse consumer edges: mathematical supply versus append protocol

**[TABLE]**

| Consumer (candidate) | Exact verified designation | GENTOW5 supply | Mathematical status | Append/consumption-protocol status |
|---|---|---|---|---|
| GENTOW1_PROOF | `GENTOW-BOX-1` (5) | `.10`, `.11`, `.13` | Box RETIRED as a mathematical box; residue grade-only | **Not landed** — “candidates for the orchestrator's dated consumption updates”; source byte-untouched |
| GENTOW1_PROOF | `S3` (14) | `.11` | The S3 grade-note restriction on layer 1 is lifted by COROLLARY GENTOW5-A′ | **Not landed** (same sentence) |
| GENHN_PROOF | `GENHN-BOX-2` (5) | `.12` | The level-1 rider matches the box's stated retirement condition; explicitly “no new claim on frozen text” | **Not landed**; “recording the consumption there is the orchestrator's dated update, not this note's edit” |
| GENHN_PROOF | `[GENHN-TOW-1]` (19) | `.38`, `.41` | Item (6)'s depth ≥ 4 sentence is a candidate; items (3)/(4) are declared still open | **Not landed** |
| GENTOW2_PROOF | `S7` (1) | `.27`, `.33` | The depth ≥ 4 bullet's proviso ((B-1)/(B-2) at level r) is supplied — at i = 2 unconditionally, at i ≥ 3 behind `[GENTOW5-W(i)]` | **Not landed** |
| GENTOW5_WI_2026-08-10.md | `[GENTOW5-W(i)]` (24) | reverse direction: WI proves the lemma GENTOW5 leaves open | Homed in shard 2 (S11.2 fence); recorded here because it governs `.27`–`.29`, `.31` at i ≥ 3 | The 2026-08-15 append confirms certification does **not** discharge the frozen GENTOW5 conditionality |

**ARITHMETIC AUDIT:** 6 rows = 5 candidate consumers named by the in-range S6 protocol sentence + 1 reverse supplier edge. The first five designations duplicate verified rows in §3.1; `[GENTOW5-W(i)]` is the one additional designation, fixed-string count **24** in `GENTOW5_WI_2026-08-10.md`. Thus this shard has **58 verified XREF designations** total, not 57.

The last column is not an inference: it is §S6's own consumption-path sentence, quoted in the header's scope split.

---

## 4. NON-IMPORTS

**[TABLE]**

| Fence | Explicit material not imported or not proved in lines 1–1474 |
|---|---|
| Sources | “SOURCES CONSUMED (never edited)” — consumption is one-directional; “the four source notes are byte-untouched by this unit.” |
| Graded frame | “No W-9-analogue weld face is consumed; the graded frame is gr(L2) itself.” |
| Normalizer systems | “no invariance under CHANGING systems mid-argument is consumed (that stronger claim is false — HE7-T-BADTWIST).” |
| Weight functional | “wt_i consumes NO data beyond the depth-i datum: u_{i+1} does not appear.” |
| GENTOW5-D strictness | “nondecreasing is all any named consumer of this lemma uses … the strict FLOW-UP pricing there comes from lam > E separately, never from this lemma's strict clause.” |
| B-2 | “never B-2 on-the-nose (u = 1), which is FALSE at letter-live grades” — the `y -> eps*y` fallback is “deleted as false at its source”. |
| Alternative key | The re-parameterized prescription “builds a DIFFERENT key from the pinned recipe … it is not repo-constructible; the statement stays at the pinned key and the twisted residual.” |
| Lift display | “GENTOW1 S3's fixed-base READING of its lift display fails the same way at seam-live heights — a display-level defect there, flagged for that note's own arc, not consumed here.” |
| Clause (c) pairing | The composed `(i+2)`-read pairing is refuted by the residual-degree count and at committed rows; “no sentence in the note consumes the retired (i+2)-read pairing.” |
| Index 0 | (a)@0 and (b)@0 “NOT claimed”; the entry locus `T_1` “stays unclaimed”, “Left unclaimed rather than cited.” |
| Depth ≥ 3 measurement | “no count law at depth >= 3 is claimed measured.” |
| Open list | “tower COUNT laws at depth >= 3 … partial inner sides … the genre-general faithfulness geography … sigma laws behind [GENHN-HE(mu >= 3)] — none of these is touched by GENTOW5-B, which is a carrier/read/budget/refine theorem, not a density display.” |
| External consumers | “External consumers: none executed (S6's consumption path is candidates only); any future consumption of (a)/(b) must ride the w-annotation.” |
| Instrument strength | The sealed `C3a`/`C3b` lines “machine-assert only nfactors … the e = 4 values (and C3b's deg) are PRINTED … not chk-asserted”. |
| PARI-free route | The withdrawn “(P-B4 is the exact witness either way)” — the per-root ladder needs the single-prime read. |

---

## 5. Teeth inverse table

**[TABLE]**

| Battery row / tooth | Guarded unit(s) | Disposition |
|---|---|---|
| §S5 P-A1 / P-A2 / P-A3 (mu2 = 3 kills, three frames incl. char 3 and K2 = F4) | `.05`, `.10`, `.11`, `.13`, `.30`, `.38` | Executable regression (sealed battery, 86 exact checks) |
| §S5 P-A4 (live-twist mu2 = 2 kill) | `.07`, `.08`, `.09`, `.10` | Executable regression |
| §S5 T-A1W (wrong-height refine) | `.10`, `.37` | Planted mutant; fired as predicted |
| §S5 T-A2W (wrong digit, char 3, surviving pin 33) | `.10`, `.17` | Planted mutant; fired as predicted |
| §S5 T-A4W (the convention tooth — naive-digit twin keeps pin 22) | `.07`, `.08`, `.09`, `.18`, `.40` | Planted mutant; fired — “machine-load-bearing, not decorative” |
| §S4.2/§S5 P-B1 + P-B2 (floor chain tight; recipe side heights = E_i) | `.14`, `.18`, `.31`, `.34` | Executable regression |
| §S4.2/§S5 P-B3 (10 one-sided polygons, char-2 binomial on-chord support) | `.28`, `.29`, `.34`, `.35`, `.36` | Executable regression; also the REFUTING rows (`f32@Phi4`, `Phi4@Phi3`) for the retired (i+2)-pairing |
| §S4.2/§S5 P-B4 (resultant ladders 16,40,84,170,341 / 8,20,42,85) | `.19`, `.34`, `.35`, `.36` | Executable regression (PARI-free integer route) |
| §S4.2/§S5 T-B1 (even-height mutant at the node → drain collapse) | `.35`, `.36`, `.37` | Planted mutant; fired (remainder 0, resultant 0) |
| §S5 P-C1/C2/C3/C4 (PARI leg: factorpadic, nfeltval ladder, refined keys, mutant split) | `.34`, `.36`, `.37` | Executable regression, detached leg; C3's e/deg values disclosed as printed-not-asserted |
| PE1 fresh FR-1 (`gentow5_pe1_fresh.py` @ 0160b94, 15/0) | `.18`, `.26`, `.27`, `.40` | Executable regression on a fresh (unsealed) instrument — the only seam-live recipe row |
| PE2 fresh FR-A / `FA1-LIFT` (`gentow5_pe2_fresh.py` @ 40f313a, 22/0) | `.17`, `.28`, `.32`, `.40` | Executable regression; asserts the fixed-base flavor's NON-existence and runs the re-solved member |
| PE3 fresh leg W (`gentow5_pe3_fresh.py` @ 9f0eca7) | `.27`, `.38` | Measurement (w ≠ 1 at the GA3\* carrier prime) |
| PE5 fresh (`gentow5_pe5_fresh.py`, GREEN 40/0) | `.26`, `.29` | Executable regression; instantiates the unclaimed `T_1` TRUE at one frame |
| post-PE4 rider helper (`gentow5_rider_f32dev.py`, 7/0) | `.29`, `.35`, `.36` | Executable regression on the canonical f32 development |
| §S2.2 worked pins (`n3hat(85)`, `n2hat(21)`) vs `genhnr2_supp.py` L387–389 / `gentow2` W1 | `.15`, `.21`, `.34` | Hand computation cross-checked against committed runner values |
| §S7 F-3 grid-4 equality instance (170 = 170 = 170) | `.24`, `.25` | Signed failure-mode fence (no downstream lean on top-carry strictness exists) |
| GENTOW2 PE4 @ 2f95be6 (B-2 on-the-nose REFUTED at letter-live grades) | `.27`, `.43` | Foreign-note regression consumed as a negative result |
| GENTOW2 PE6 (w measured ≠ 1, 6 primes / 4 frames) + PE5 @ 75923bc (psi^{(w)} admissible for every w) | `.27`, `.38` | Foreign-note measurement + verification |
| PROOF-ONLY: LEMMA GENTOW5-C at i ≥ 3 | `.17`, `.22`, `.27` | **PROOF-ONLY** — no dedicated committed row; the note says “The depth->=4 region has machine contact ONLY through S4's witness (one exact instance) + HE7 R1.3's level-3 leg one ladder over” |
| Committed-battery seam axis | `.18`, `.40` | **signed vacuity disclosure** for the sealed battery (“GAUGE-SEAM-BLIND BY CONSTRUCTION”); **accepted-with-decorrelation-supplied** by fresh FR-1 |
| Seam-live × `e_stage ≥ 2` compound | `.22`, `.40` | **disclosed non-repair** — “NO machine contact”; proof-side derivation remains uniform |
| S11.1 `gentow5_af1_direction_check.py` | `.25`, `.29` | **AUDIT — decorrelated-model audit**; corrected converse direction and one-directional Step 2, GREEN 8/0 |

**ARITHMETIC AUDIT:** 23 data rows. The sealed core contributes 86 exact checks plus 6 PARI checks = 92 full checks, matching `.04`, `.36`, `.37`, and the two committed output verdicts; violation totals are 0 on both routes. Fresh/helper row totals (15/0, 22/0, 40/0, 7/0, 8/0) are independent runs and are not added to the sealed 92. Every guarded-unit column is nonempty.

**Both-direction audit:** every row above guards at least one in-range unit, and every in-range unit carrying a non-empty `TEETH` field appears in at least one row. Units with `TEETH: NONE` (`.03`, `.23`, `.39`, `.41`, `.42`) are declarations or inventories and are outside the orphan count. **Zero battery-row orphans; zero toothed-unit orphans.** The S11.1 audit is homed in shard 2 but is included because it guards corrected readings of in-range units `.25` and `.29`.

---

## 6. Boundary self-audit

GENTOW5 is a **tag-sparse prose-proof** note (`\tag{` density 0.00 — `runs/qgen/EFFT3_crossread.md` §4.4), so statement boundaries had to be chosen rather than read off display tags. The rule applied: **split at a change of consumer, supplier perimeter, conditionality, or executable tooth** — never at paragraph length. Boundaries chosen:

1. `.01`–`.04` separate front matter by *function*: arc chronology (status, superseded), charge (no claim), import fence (declaration), status ledger (`[TABLE]`, transcribed as a table per template rule 5).
2. `.05` keeps the whole §S0 setting as one hypothesis unit: it has one conditionality (the accepted depth-2 datum) and every §S1 unit reads against all of it.
3. `.06`–`.10` follow §S1's own lemma names (A0, the convention + definition, A1, the theorem). The convention `.07` and the dictionary `.08` are split because A1's *statement* is a translation law while the convention is a *choice*, and `.09` fences that choice as load-bearing — three different conditionalities.
4. `.11` and `.12` split COROLLARY GENTOW5-A′'s two clauses: (i) is a mathematical closure claim, (ii) is explicitly “display, no new claim on frozen text” with a protocol consequence. Merging them would let a downstream cut read the level-1 rider as a landed consumption.
5. `.14`–`.20` follow DEF GENTOW5-1's own bullet structure. This is the shard's most consequential boundary choice: the definition's bullets have *different* correction histories (the lift display was rewritten at r2 and re-ranged twice; the recipe carries the r1 gauge pin; the ladders/floor-chain bullet is the one S12.1 re-scopes). One merged “DEF” unit would have made those histories inseparable.
6. `.22` keeps LEMMA GENTOW5-C whole (statement + bound fold + proof + grade fold) because its four-clause instantiation table is a single argument; `.23`'s remark is split off since it is a NON-IMPORT fence about a different object (the HE7 base).
7. `.24`/`.25` split the weight functional from the monotonicity lemma: the functional survives S11.1 untouched, the lemma's consequence clause does not.
8. `.26`–`.31` follow THEOREM GENTOW5-B's own clause letters, with the statement header + index-0 scope as a separate scope-record because it governs all five clauses at once. `.32` (the consumer walk) and `.33` (the pin stack) are separate because S12.1 withdraws part of the first and not the second.
9. `.34`–`.37` split the witness into chain / preregistered predictions / run verdict / battery, matching the note's own S4.1/S4.2/S4.3/S5 seams and keeping each battery row addressable in the inverse table.
10. `.38`–`.42` follow §S6's four bullet groups, kept separate because they are four different predicates: supply set, conditionality stack, machine coverage gap, open list, protocol scope. `.43` is the distinct historical repair record.

Merges deliberately NOT made: the (B-1)/(B-2) legs stay inside `.27`'s DERIVATION rather than becoming units, because they are the proof of clause (a) and have no independent consumer in this range; §S1.2's convention consequence stays a fence rather than a lemma, because the note itself displays it “for honesty”, not as a claim.

---

## 7. SHARD NOTES

- **Cross-shard supersessions applied (resolution rules 3–6):** the acceptance record (status → ACCEPTED 2/2); S11.1 (S2.4's converse direction + two-directional closure withdrawn; S3(c) Step 2's parenthetical superseded); S11.2 (`[GENTOW5-W(i)]` fence at i ≥ 3); S11.3 ((a)@i=1 re-scoped to `psi_2^{(u1)}`, tie to `w_1` open); S11.4 (lift m-range) as itself superseded by S12.2 (threshold `bound_i`, boxed `bound_i < E_i`); S11.5 (clause (b) residual display re-indexed); S12.1 (`𝒲_{≤n}` conditionality propagated to (a)/(b)/(c)/(e) at n ≥ 3, S11.2's unaffected list withdrawn); the post-D3i corrigendum (twist index `ψ_j^{(ω_{j−1})}`).
- **Later non-superseding consumption record:** the 2026-08-15 T5 append is outside HOME and explicitly makes no correction to this note. It nevertheless resolves the former WI perimeter call: T5 carries `𝒲_{≤n}` rather than treating the certified companion as discharging GENTOW5's frozen conjuncts. T5's `WF-w` designation is grep-verified count **16**, but is not added to this shard's XREF total because the consumed S11/S12 fence is homed in shard 2.
- **Range-edge audit:** line 1473 is S7's closing sentence (“TARGET 1 … untouched beyond the pins named here.”); line 1474 is blank and line 1475 opens `## S8`. **No source statement unit is cut at the edge.** S8's own content (the PE2 repair record) is homed in shard 2; its *effects* on in-range text (the r2 rewrites at S3(a), S2.1, S2.4, S6) are already landed in the base text inside this range and are inventoried at their units.
- **Outside-HOME material not inventoried:** S8, S9, S10, the acceptance record, S11 and S12 are NOT emitted as units here merely because they resolve in-range text. They appear only in the header, in CONDITIONALITY/RESOLUTION TRACE fields, and in this shard-notes list. Shard 2 owns them.
- **Protocol versus absorption:** §S6's supply set is inventoried; no consumption append is claimed landed on any of the four source notes. The later T5 fence-consumption append is recorded separately and does not enlarge the supply set.
- **Numbering:** temporary IDs `EFF.GENTOW5.s1of2.01`–`.43`, to be reconciled with shard 2's at the merge run.

---

## 8. Self-audit and OPEN-CALLS

### OPEN-CALL 1 — the `ITER-LAW` designation is not in the note it is attributed to

LEMMA GENTOW5-A1's proof (`.08`) sources the first wrap letter as “z1 by GENHN's S4 level-1 cocycle (accepted; the ITER-LAW z-letter)”. Fixed-string grep for `ITER-LAW` in `GENHN_PROOF_2026-08-08.md` returns **0**. The designation does exist in the corpus — `DITER_RESTATE_2026-08-08.md` (**16**) and `GRTJC_PROOF_2026-08-08.md` (**5**) — but attributing it to GENHN's S4 cannot be verified, and no XREF is emitted for it. The verified part of the same sentence (`T22`, count **9** in GENHN_PROOF, for the second wrap letter) is emitted. **Decision needed:** whether the z-letter's supplier for this note is GENHN's S4 cocycle (designation unnamed there) or the DITER `ITER-LAW` unit.

### OPEN-CALL 2 — the accepted outer `ψ₁` leg is unnamed

The post-D3i corrigendum governing `.28` says “`ω₁ = the S11.3 unit (the outer ψ₁ leg handled separately as accepted)`”. Fixed-string grep finds `outer ψ₁ leg` exactly **1** time in this note and **0** times in every other openmath note; no supplier designation is given. The S11.3 unit names the `ψ₂` residual re-scope, not a separately named outer-`ψ₁` theorem. No XREF is invented. **Decision needed:** identify the accepted source unit for the outer `ψ₁` leg, or make the acceptance self-contained in a later append.

### Resolved former calls

1. **WI perimeter:** resolved by the 2026-08-15 append. `[GENTOW5-W(i)]` occurs **24** times in `GENTOW5_WI_2026-08-10.md`, but the current GENTOW5 tail explicitly says certification of that companion “does not discharge these conjuncts from the frozen GENTOW5 statements”. The terminal reading remains conditional on `𝒲_{≤n}`.
2. **Floor-chain provenance:** resolved as two predicates, exactly as S12.1 instructs. As a fixed tower datum, `u_{i+1}>e_{i+1}E_i` is usable unconditionally; its claimed automatic derivation from clause (e) is conditional on `𝒲_{≤n}` for n ≥ 3. Units `.14` and `.31` carry the two readings separately.

### Recorded source defects (flagged, not silently repaired)

1. **`.34`, S4.1:** the parenthetical `m* = 4*341/4...` is a truncated token (same species as the `(LIFT_i)` bound's `e...`, which PE5-F-3 restored). No later round repairs it. The sentence's arithmetic conclusion is complete without it.
2. **`.17`:** S11.4's bracket is addressed to “the S2.2 K_i-digit-lifts display”, but the `lift_i(c; m)` display is homed in §S2.1 (§S2.2 is the consistency-checks section). The referent is unique in the note, so the bracket is applied to the §S2.1 display; the mis-pointer is recorded rather than corrected. S12.2, which supersedes that bracket, refers to it without a section number.
3. **`.27`:** clause-level references `GENTOW2-A(d)` and `HE7 ANNEX R R1.2 item 3` are sub-designation pointers: the parent designations are verified (`THEOREM GENTOW2-A` = 8; `R1.2` = 7) but the clause/item letters are not separately greppable. Carried descriptively.

### Fidelity audit

- Every CANONICAL STATEMENT is either verbatim quotation or explicitly marked `[ASSEMBLED]`; no inverse, sign, quantifier, index, level, or implication direction was altered. Truncations inside quotations are marked with `…`.
- The note's own ASCII displays are reproduced with their line structure intact; the only presentational change is Markdown blockquote framing (and backslash-escaping of `*` inside quoted prose where Markdown would otherwise consume it, at `.34`, `.35`, `.37`, `.38`).
- The one source table (STATUS TABLE) is emitted as a table and flagged `[TABLE]`; no source table was prosified.
- All **58** external XREF designations carry fixed-string counts ≥ 1: 57 import rows in §3.1 plus the reverse-supplier `[GENTOW5-W(i)]` row in §3.3. Three ASCII/Unicode orthography differences are recorded as reading notes with the verified (Unicode) form; one candidate designation with count 0 (`GENTOW2-A(d)`) is explicitly NOT emitted as an XREF; unverifiable names are OPEN-CALLs, never invented XREFs.
- Structural recount: **43** units, **43** FORM fields, **43** CANONICAL STATEMENT fields, **43** DERIVATION fields, **43** RESOLUTION TRACE fields, and **43** TEETH fields; zero retired `regression-record` types.
- Status and absorption are kept as distinct predicates throughout: the acceptance record governs grade; §S6 leaves the four named source-note appends unlanded; the later T5 append consumes only the conditional fence and is recorded separately.
- Commit/artifact pins are recorded in §3.2: all named commits resolve, every reported run has a filename, the sealed md5s match, and the historical pre-r1 checksum is classified AS-OF-PIN rather than falsely current.
- Out-of-range material is used only to resolve in-range HOME units, per resolution rule 8.

EFF-GENTOW5-s1of2 COMPILED: 43 statements / 58 xrefs verified / 2 open calls
