# EFF-GENIND-s3of3 — CANONICAL EFFECTIVE-SPECIFICATION SHARD

**COMPILED-BY: opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). CODEX CROSS-READ OWED (post-reset).**

## 1. Shard header

**Source note:** `lean/notes/openmath/GENIND_PROOF_2026-08-08.md` (3872 lines).

**HOME range:** source lines 2552–3872 inclusive — **the whole post-acceptance annex stack**: ANNEX R (Codex ratification repairs R1–R6 + close), the dated supplier-movement record (GENHN errata E1–E3 + GENHN r2 + the n ≥ 8 conditionality movement), ANNEX R — r1 (the annex stack's own hostile pass: GENIND-C2, MINOR-1, MINOR-2, and a two-commit machine leg), and the two 2026-08-12 dated corrections (the sol R9 GENIND-C2 replacement with three riding folds; the sol R11 round-2 repairs C2-G1/G2/G3 with GENIND-C2Q and GENIND-C2D). Earlier text (lines 1–2551, shards 1 and 2) is used ONLY to resolve material homed here.

**HEAD blob hash:** `8ef694fefc24c5fb07e4e80c306ff2136c914b61` (clean in the working tree; last touched by commit `5e33b01f`).

**Compilation context:** `spec/EFF_TEMPLATE_v2.md` at its current HEAD (v2 rules 1–10; v3 rules 11–28). Temporary IDs `EFF.GENIND.s3of3.<nn>`.

**GENRE: MIXED — tag-sparse prose annex (2552–3297) + LaTeX-tagged display mathematics (3298–3872).** `grep -c '\tag{'` over the whole note = **13**, and **all 13 sit inside this shard**, at lines 3333, 3393, 3402, 3436, 3459 (the R9 GENIND-C2 replacement: C2.0, C2.1, C2.2, C2.3, C2.4), 3625, 3634 (**CS-1Q.a, CS-1Q.b** — the ledger's HYP.36 clauses), 3645, 3656 (C2Q.1, C2Q.2), 3731 (C2D.1), 3818, 3829, 3837 (C2E.1, C2E.2, C2E.3). **So this is the only shard of GENIND where statement boundaries are partly READ OFF display tags** — in the two 2026-08-12 corrections a tagged display is an addressable object by construction. Above line 3298 the genre is tag-sparse prose with explicit numbered sub-headings (`R1.0`, `R1.1`, …, `r1.1`, `r1.2`), which are the source's own boundary markers. §6 records the boundary calls; they are materially easier here than in shards 1–2, and §6.3 says why.

**Freeze status of this shard's own text:** this range is **NOT covered by the note's body freeze** (lines 1–2464) and only partly by the pre-annex freeze (lines 1–2548). ANNEX R has its own internal freeze (`.31`: “the ANNEX R text above is edited at exactly five [ar1 2026-08-10]-tagged sites … every other annex line is unchanged”), and the 2026-08-12 corrections append below everything (“Everything above this heading is byte-untouched by this append”, line 3306).

### Governing effective-text record

**(i) The accepted body below which this stack sits is byte-frozen** — ANNEX R head, lines 2567–2571:

> “The accepted text above is BYTE-FROZEN: full file before this append
> = 158,427 bytes, md5 `eefcf6584bbb0917875e77c9fcab7a9e` (2,548
> lines), verified identical before and after; within it the
> PE8-verified body freeze (lines 1–2464 md5 `14fa6afc…`) was
> re-executed this round and matches.”

**(ii) The annex layer's own edits are enumerated** — ANNEX R — r1, lines 3106–3111:

> “The accepted body stays byte-frozen (lines 1–2548 md5 eefcf658,
> re-verified at this commit); the ANNEX R text above is edited at
> exactly five [ar1 2026-08-10]-tagged sites — the R1.1 closure rider,
> the R1.2 u_l rider, the R1.3 c-choice, the R1.4 enumeration, the
> close enumeration — plus one rider at R1.4's CS sentence below;
> every other annex line is unchanged.”

**(iii) The 2026-08-12 corrections are pure appends** — line 3306: “Everything above this heading is byte-untouched by this append.”

**(iv) The annex layer carries a LOWER grade than the body it repairs** — ANNEX R close, lines 3022–3028:

> “Grade honesty: this annex cures the six
> adjudicated findings by display riders, one erratum, and the R1
> derivations at the accepted text's own grade; the annex has NOT
> itself been through a hostile pass. The 2/2 acceptance attaches to
> the frozen body; the annex carries the ratification fold's
> CHALLENGE disposition (CODEX_GENINDRAT_2026-08-09.md S4) with the
> queue now landed.”

and, after its own scoped pass, the r1 grade line (line 3293): “The annex stack remains 0/2”.

**EFFECTIVE TEXT FOR THIS SHARD = lines 2552–3872, read in layer order.** Four layers, each superseding parts of the one before:

| Layer | Lines | Landed | Supersedes |
|---|---|---|---|
| L1 ANNEX R (R1–R6 + close) | 2552–3028 | 2026-08-09, commits `a1525ea`+`31c6723d`+`98ac7bb0`+`fe0ed6c0`+`f5271e4` | in-range: nothing; out-of-range: shard 1 `.11`, `.13`, `.14`, `.24`, `.36`, `.45`, `.46`, `.49`, `.58`; shard 2 `.04` |
| L2 supplier-movement record | 3032–3094 | 2026-08-09 | discharges shard 2 `.17`'s owed disclosure; moves shard 1 `.15`'s conditionality |
| L3 ANNEX R — r1 | 3098–3294 | 2026-08-10 | **five named sites inside L1** (`.04`, `.05`, `.06`, `.07`, `.25`) + adds GENIND-C2 |
| L4 the two 2026-08-12 corrections | 3298–3872 | 2026-08-12 (sol R9, then sol R11) | **L3's GENIND-C2 in full** (R9), then **R9's C2(i)/(ii)/(iii) in part** (R11) |

**No in-range sentence is deleted by any later layer**; every supersession quotes or names its target and leaves it byte-intact.

### Scope split (rules 7 and 17)

**A. ABSORPTION / supply SET.** What this stack claims to supply: the vanishing RATE consumed but not displayed by §S5.2 ((A2-RATE) + GENIND-C1 + GENIND.C′ + GENIND-C2/C2Q/C2D), the unit-pivot condition (CS-1Q's ancestor R2), the window-1 convention, two display errata (CS4-F's floor; the degree-level converse), and the identity-vs-bound separation. **It supplies no new count law and no discharge of [GENIND-H].**

**B. APPEND / consumption PROTOCOL scope.** **NO-APPENDS on suppliers, and one new sub-predicate: NO-EDITS on OTHER AUTHORS' REPORTS.** R6.1's governing quote (lines 2972–2974): “**R6.1 The notice (the report itself stays untouched — its author's artifact per the standing rule; the notice lives here and at the ledger)**”. This is the same freeze predicate shard 2 records at its `.58`, exercised here against the **PE8 acceptance report**, i.e. against the very artifact that accepted the note.

**C. INBOUND corrections RECEIVED.** Four channels in this shard, and they are the reason it exists:
* **Codex ratification (decorrelated model, fresh context, read-only)** — six findings, RATIFICATION OUTCOME **CHALLENGE** (`.01`).
* **The annex stack's own scoped hostile pass** — 0C + 1 GAP + 2 MINOR (`.31`).
* **Two sol certification runs** — R9 (`.40`) and R11 (`.49`), each returning a real defect in the *previous repair* and deriving its replacement.
* **A supplier movement** — GENHN's three errata executed plus its r2 round, which refuted and re-proved one of its own lemmas and boxed the tower clause (`.26`–`.29`).

### Resolution rules applied

1. Lines 2552–3872 supply the HOME material, read in the four-layer order above.
2. **`[ar1 2026-08-10]` brackets inside L1 are already-landed edits** made by L3 at five enumerated sites; each quotes what it replaces.
3. **L4's first correction (R9) SUPERSEDES L3's GENIND-C2 in full** — “This passage supersedes r1.1's ANNEX-LEMMA GENIND-C2 statement, proof, displayed instances, and conditionality paragraph” (line 3310). The superseded text stays byte-intact.
4. **L4's second correction (R11) supersedes THREE named parts of L4's first** — “the stage-window assertion in C2(i), the equal-product-degree descent sentence in C2(ii), and the entry-pricing display in C2(iii)” (line 3594) — and **withdraws a bound**: “The scalar bound \(M^\star\ge e(N-1-H)\) is withdrawn for general embedded and mixed genres”.
5. **Consumer sweeps are a distinct supersession vehicle in L4** (`.53`, `.56`, `.58`): bulleted instructions of the form “In X, replace Y by Z”, reaching into frozen text in shards 1 and 2 that they do not quote. Their status is OPEN-CALL 1.
6. Where a layer riders an out-of-range unit, the target is named with its shard-1/shard-2 ID and the governing text is quoted at the unit here.
7. Out-of-range statements are NOT emitted here merely because they resolve in-range text.
8. External records (the Codex fold note, the sol run logs `runs/cert/R9_drain_repair_output.log` and `runs/cert3/R11_genind_output.log`, `runs/residues/R1_drainn4_output.log`, ledger rows) are **reading notes only**.

### Quotation and table discipline

CANONICAL STATEMENTs are verbatim or explicitly `[ASSEMBLED]`; truncation is marked `…`. **The LaTeX display blocks of L4 are reproduced verbatim with their `\[ … \]` delimiters and `\tag{}` labels intact** — they are the source bytes, and a transcription to Unicode would lose the tag anchors a chapter cut needs. Where a tagged display carries a count or an inequality chain, the compiler adds an arithmetic audit **beside** the quote, never inside it. **This shard contains no Markdown table and no fixed-width ASCII table**, so rules 5 and 14 do not fire on source material; compiler ledgers are flagged `[TABLE — compiler ledger]`.

---

## 2. Statement inventory

### EFF.GENIND.s3of3.01  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph (ANNEX R's provenance and scope). verbatim, lines 2552–2578.

> “## ANNEX R (2026-08-09, post-ratification; CODEX F1-F6)
>
> **Provenance and scope.** The ratification sweep's Codex leg
> (`CODEX_GENINDRAT_2026-08-09.md`, session
> 019fe5fe-39b0-7ff3-806d-4f578bcdb292, gpt-5.6-sol at HIGH, fresh
> context, read-only) returned **6 findings — RATIFICATION OUTCOME:
> CHALLENGE** at adjudication: F3 (CONFIRMED GAP, the heaviest — the
> vanishing rate consumed but not supplied by the displayed P(k)), F1
> (CONFIRMED GAP with disclosure overlap — GENIND-6(c)'s onto/constant-
> fiber missing its unit-pivot step), F2 (CONFIRMED GAP — the window-1
> scope leak), F4 (CONFIRMED, regraded MINOR at this note, GAP at the
> PE8 acceptance report — its §4.1 monotonicity display is false), F5
> (CONFIRMED, regraded MINOR display — the CS4-F floor), F6 (CONFIRMED,
> regraded MINOR wording — the stage-level reading of the converse).
> This annex executes the fold note's S4 repair queue R1–R6 in order.
> The accepted text above is BYTE-FROZEN: full file before this append
> = 158,427 bytes, md5 `eefcf6584bbb0917875e77c9fcab7a9e` (2,548
> lines), verified identical before and after; within it the
> PE8-verified body freeze (lines 1–2464 md5 `14fa6afc…`) was
> re-executed this round and matches. Machine support: the ADDITIVE leg
> `verification/openmath/genind_annexr_supp.py` + committed output
> (commit f5271e4; checks A–I, GREEN; py md5 `42fd603e…`, output md5
> `d938ad82…`); the sealed runner + artifacts are untouched (the runner
> is consulted READ-ONLY at its two CS4-F gate lines). Honesty of
> grade: this annex is a post-ratification append and has NOT itself
> been through a hostile pass; each repair below RE-DERIVES from the
> note's own lemmas and quotes the finding it cures.”

**CONDITIONALITY:** **The decisive fact for the whole DAG: a decorrelated model, reading a note that had just been ACCEPTED 2/2 by eight in-house hostile passes, returned six confirmed findings including three GAPs — one of them a consumed hypothesis component absent from the display.** The outcome is **CHALLENGE**, not refutation: no count law falls, and the acceptance is annotated rather than revoked. **Three of the six findings are regraded downward at this note and one is regraded UPWARD elsewhere** (F4 is “GAP at the PE8 acceptance report”), i.e. the heaviest consequence of F4 lands on a *verifier artifact*, not on the note.

**ARITHMETIC AUDIT (compiler-computed):** six findings, dispositions: 3 CONFIRMED GAP (F3, F1, F2) + 3 CONFIRMED-but-regraded MINOR (F4, F5, F6) = 6 ✓. Repair queue R1–R6 maps one-to-one onto F3, F1, F2, F5, F6, F4 respectively (R1↔F3, R2↔F1, R3↔F2, R4↔F5, R5↔F6, R6↔F4) ✓ — **the queue is ordered by severity, not by finding number**, which the section headings confirm.

**SUPERSESSION KIND:** none of its own (a provenance record). It establishes freeze predicates for the layer.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2552–2578. correction sites: 3098–3115 (ANNEX R — r1's provenance, which edits five sites inside this layer).

**TEETH:** machine leg `genind_annexr_supp.py` (checks A–I, GREEN), consulted read-only against the sealed runner. Disposition: **`decorrelated-model audit`** (rule 27) — the finding source is a different model in a fresh read-only context, and **none of the six findings could have been produced by any battery row**, since three are about undisplayed hypotheses, one about a toy counterexample shape the runner never executes, one about a display's missing side condition the runner already gated on, and one about a *report's* rationale.

**PIN VERIFICATION:** `f5271e4` ✓ commit; `verification/openmath/genind_annexr_supp.py` ✓ and `genind_annexr_supp_output.txt` ✓ EXIST; the fold note `lean/notes/openmath/CODEX_GENINDRAT_2026-08-09.md` ✓ EXISTS.

---

### EFF.GENIND.s3of3.02  [supplier-finding]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph with two nested quotations (R1.0 — the defect stated exactly, quoting both the consuming sentence and the supplying package). verbatim, lines 2580–2604.

> “### R1 (CODEX F3, the heaviest): the vanishing rate — P(k)'s fourth member pinned to the rate-carrying species + the bounded/growing-M_l split displayed
>
> **R1.0 The defect, exactly.** S5.2's vanishing bullet consumes a rate:
>
> > "vanishing: u/Q^{m(N−1)} → 0 by induction (head Q^{−(N−1)};
> > α-terms geometric; β-terms lose at least one child's full mass by
> > the IH bound — each contributes O(poly(N)·Q^{−(N−c)}) relative
> > mass)"
>
> while THEOREM GENIND.B's displayed package supplies only
>
> > "P(k) := {… + exact-complement (A2)}"
>
> and W-12's (A2) is a bare o(1) (r(N)/q^{nN} → 0 — Codex's instance:
> 1/log(M+1) is o(1) with no exponential rate). Codex F3's two halves,
> both confirmed at adjudication: (i) "exact" supplies a VALUE, not a
> rate — the displayed fourth member does not carry the O(poly·Q^{−·})
> the bullet consumes; (ii) a capped child window M_l = N − D_l can
> stay BOUNDED while the genre depth D_l grows with N, and there the
> child's own M_l → ∞ vanishing cannot be applied — those β-terms
> vanish only through the route prefactor, and no bounded-vs-growing
> split was displayed. GENIND-BOX-4 priced the bookkeeping compression;
> the finding is sharper: a consumed HYPOTHESIS component absent from
> the display.”

**CONDITIONALITY:** **Type `supplier-finding` in the mirror sense of rule 13**: a defect report against the note's OWN frozen body, discharged here rather than at the (unreachable) source. Both halves are confirmed at adjudication. **Half (ii) is the mathematically substantive one** and is what forces GENIND-C1(iii)'s two-regime split; half (i) is a hypothesis-display gap.

**ARITHMETIC AUDIT (compiler-computed, on the counterexample shape):** Codex's instance `1/log(M+1)` is indeed `o(1)` with no exponential rate ✓ — and it is admissible as a *complement fraction* only if the note's (A2) is a bare limit, which W-12's is. **The gap is real as stated:** “exact closed form” constrains the VALUE and says nothing about decay in M. Half (ii)'s shape: with `M_l = N − D_l` and `D_l` growing with N, `M_l` can stay bounded ✓ (the note's own capped formula makes `D_l` genre-dependent and N-independent only when every slope is fixed; at a genre whose depth grows with the window, `M_l` is bounded) — and then the child's own asymptotic supplies nothing ✓.

**DERIVATION:** Not a mathematical unit; a defect report. Its repair is `.03`–`.07`.

**RESOLUTION TRACE:** statement lines 2580–2604. correction sites: none — this is the finding, not a claim.

**TEETH:** **`decorrelated-model audit`.** The note's own framing is the row's disposition: “GENIND-BOX-4 priced the bookkeeping compression; the finding is sharper: a consumed HYPOTHESIS component absent from the display.” **Eight in-house hostile passes did not find it**, and no battery row could have: the runner computes exact counts, and an exact count is silent about the *rate* its own asymptotics need.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:W12-BOX-1` — count **10** (the box family this finding sharpens is GENIND's own BOX-4, shard 2 `.04`).

---

### EFF.GENIND.s3of3.03  [lemma]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph with two indented ASCII displays (R1.1 — the rate-carrying species grounded at m = 2). verbatim, lines 2606–2639.

> “**R1.1 The rate-carrying species, grounded at m = 2 (derivation
> displayed).** At m = 2 the recursion of S5.2 closes without β-terms:
> by GENIND-1's grammar a repeated linear e = 1 factor at m = 2 spans
> the whole polygon at integer slope — that is α — and the partition
> (1,1) is separable (DEC); no continuing child exists below degree
> 2·d, and m = 2 < 4 excludes CS (S5.1). So the first-step recursion
> degenerates to head + α:
>
>     u(N) = Q^{N−1} + Σ_{k ≥ 1, 2k ≤ N−1} (Q−1)·Q^k · u(N−2k),
>     u(1) = 1   (the window-1 boundary: R3's rider below),
>
> writing u := u_{2,d}, Q := q^d, c(2) = 1. Telescope (re-derived here,
> the W-11 R-recursion move): subtracting the k ↦ k+1 re-indexed sum,
>
>     u(N) = Q^{N−1} − Q^{N−2} + Q²·u(N−2)   (N ≥ 3),
>
> and iterating from u(1) = 1, u(2) = Q gives the CLOSED FORMS
>
>     u(2ℓ)   = ℓ·Q^{2ℓ−1} − (ℓ−1)·Q^{2ℓ−2},
>     u(2ℓ+1) = (ℓ+1)·Q^{2ℓ} − ℓ·Q^{2ℓ−1},
>
> equivalently u(M) = Q^{M−1} + ⌊(M−1)/2⌋·(Q−1)·Q^{M−2} — which is
> LETTER-FOR-LETTER the committed R(M) displayed inside THEOREM HEX3.A
> (the W-11 supply consumed there). Machine (leg A, B): the closed
> forms solve the recursion symbolically in Q at N = 2..14 and equal
> R(M) at M = 1..14. Rate (leg C): u(N) ≤ N·Q^{N−1}, i.e.
>
>     u(N)/Q^{2(N−1)} ≤ N·Q^{−(N−1)}
>
> at N = 2..14, Q ∈ {2,3,4,5,8,9} — coefficient POLYNOMIAL (degree 1)
> in the window, deficit LINEAR in the window. The n = 3 instance is
> already displayed at the supplier: THEOREM HEX3.A's exact law (a
> ⌊(N−1)/3⌋-term q-power sum with the same R(M) coefficients) with
> THEOREM HEX3.B's rate u ≤ N·q^{2N−2}, undecided/q^{3N} ≤ (1+N)q^{−N}.”

**CONDITIONALITY:** **Unconditional at m = 2, and the ground instance of the species (A2-RATE).** Its consumption of the window-1 boundary `u(1) = 1` is explicitly routed through R3's rider (`.13`) — the note wires its own two repairs together. **The `R(M)` identity is the decorrelation:** the closed form derived here is claimed LETTER-FOR-LETTER equal to a committed supplier display, and machine leg B checks that at M = 1..14.

**ARITHMETIC AUDIT (compiler-computed — every displayed step re-derived; this is the shard's most checkable unit):**
* **Telescope, re-derived in full.** Write `S(N) := Σ_{k≥1, 2k≤N−1} (Q−1)Q^k u(N−2k)`, so `u(N) = Q^{N−1} + S(N)`. Re-index `S(N)` at `j = k−1` on its `k ≥ 2` tail: `Σ_{k≥2}(Q−1)Q^k u(N−2k) = Q·Σ_{j≥1}(Q−1)Q^{j} u((N−2)−2j) = Q·S(N−2)` — the index ranges match, since `2k ≤ N−1, k ≥ 2` ⟺ `2j ≤ N−3, j ≥ 1` ✓. Hence `S(N) = (Q−1)Q·u(N−2) + Q·S(N−2)`, and substituting `S(N−2) = u(N−2) − Q^{N−3}` gives `u(N) = Q^{N−1} + (Q−1)Q·u(N−2) + Q·u(N−2) − Q^{N−2} = Q^{N−1} − Q^{N−2} + Q²·u(N−2)` ✓ — **the displayed telescoped recurrence, exactly.**
* **The closed forms satisfy it.** At `N = 2ℓ`: LHS `= ℓQ^{2ℓ−1} − (ℓ−1)Q^{2ℓ−2}`; RHS `= Q^{2ℓ−1} − Q^{2ℓ−2} + Q²[(ℓ−1)Q^{2ℓ−3} − (ℓ−2)Q^{2ℓ−4}] = ℓQ^{2ℓ−1} − (ℓ−1)Q^{2ℓ−2}` ✓. At `N = 2ℓ+1`: LHS `= (ℓ+1)Q^{2ℓ} − ℓQ^{2ℓ−1}`; RHS `= Q^{2ℓ} − Q^{2ℓ−1} + Q²[ℓQ^{2ℓ−2} − (ℓ−1)Q^{2ℓ−3}] = (ℓ+1)Q^{2ℓ} − ℓQ^{2ℓ−1}` ✓. **Both branches exact.**
* **Base cases.** `u(1) = 1`: from `u(2ℓ+1)` at `ℓ = 0` → `1·Q⁰ − 0 = 1` ✓. `u(2) = Q`: from `u(2ℓ)` at `ℓ = 1` → `1·Q¹ − 0 = Q` ✓.
* **The unified form.** `u(M) = Q^{M−1} + ⌊(M−1)/2⌋(Q−1)Q^{M−2}`. At `M = 2ℓ`: `⌊(2ℓ−1)/2⌋ = ℓ−1`, giving `Q^{2ℓ−1} + (ℓ−1)(Q−1)Q^{2ℓ−2} = Q^{2ℓ−1} + (ℓ−1)Q^{2ℓ−1} − (ℓ−1)Q^{2ℓ−2} = ℓQ^{2ℓ−1} − (ℓ−1)Q^{2ℓ−2}` ✓. At `M = 2ℓ+1`: `⌊2ℓ/2⌋ = ℓ`, giving `Q^{2ℓ} + ℓ(Q−1)Q^{2ℓ−1} = Q^{2ℓ} + ℓQ^{2ℓ} − ℓQ^{2ℓ−1} = (ℓ+1)Q^{2ℓ} − ℓQ^{2ℓ−1}` ✓. **The three displayed forms are one function.**
* **The rate.** `u(N) ≤ N·Q^{N−1}`: at `N = 2ℓ`, `u = ℓQ^{2ℓ−1} − (ℓ−1)Q^{2ℓ−2} ≤ ℓQ^{2ℓ−1} ≤ 2ℓ·Q^{2ℓ−1} = N·Q^{N−1}` ✓; at `N = 2ℓ+1`, `u ≤ (ℓ+1)Q^{2ℓ} ≤ (2ℓ+1)Q^{2ℓ}` for `ℓ ≥ 1` ✓ and at `ℓ = 0`, `1 ≤ 1·Q⁰` ✓. Dividing by `Q^{2(N−1)}` gives `u(N)/Q^{2(N−1)} ≤ N·Q^{−(N−1)}` ✓ — **the displayed rate, with (K, B, c) = (1, 1, 1)**, matching R1.1's own closing claim at `.06`.
* **Compiler verdict on this unit: every displayed step re-derives.** The telescope, both closed forms, the unified `⌊(M−1)/2⌋` form, both base cases and the rate bound were recomputed independently above and all agree with the source. **This is the most fully checkable unit in the three GENIND shards.**

**DERIVATION:** Displayed in the statement (recursion → telescope → closed forms → identity → rate). Justification tags: the recursion's shape = `by XREF GENIND-1`'s grammar + `by XREF S5.1` (m = 2 < 4 excludes CS); the telescope = `computation` (re-derived above, exact); the R(M) identity = `by XREF THEOREM HEX3.A` + machine leg B; the rate = `computation` + machine leg C.

**RESOLUTION TRACE:** statement lines 2606–2639. proof lines — displayed. correction sites: none; the closure sentence that FOLLOWS it is riddered at `.04`.

**TEETH:** machine legs A, B, C of `genind_annexr_supp.py` @ `f5271e4` (GREEN) — symbolic solution at N = 2..14, the R(M) equality at M = 1..14, and the rate at six values of Q. Disposition: **executable regression + `accepted-with-decorrelation-supplied`** (the R(M) tie is to a committed supplier display, not to this note's own machinery).

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:THEOREM HEX3.A` — count **11**; `THEOREM HEX3.B` — count **8**; `R(M)` — count **21**.
XREF: `lean/notes/openmath/W11_PROOF_2026-08-08.md:THEOREM W-11` — count **3**.

---
### EFF.GENIND.s3of3.04  [hypothesis]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph + display (R1.1's species pin — the (A2-RATE) rider on P(k)'s fourth member) + the closure sentence, carrying an `[ar1 2026-08-10, GAP-1 repair]` rider. verbatim, lines 2641–2675.

> “**The species pin (the fourth member's rider).** Read P(k)'s fourth
> member "exact-complement (A2)" WITH the species the proved instances
> exhibit — for each consumed cluster system (μ, d) at window M:
>
> > **(A2-RATE)** the conservative complement u_{μ,d}(M) is an exact
> > finite sum of signed q-power terms whose term count and
> > coefficients are polynomially bounded in M; in particular there
> > are constants (K, B, c) depending on (μ, d) only with
> >
> >     u_{μ,d}(M) / Q^{μ(M−1)} ≤ K·M^B·Q^{−(M−c)}.
> >
> > Instances: (μ, d) = (2, d): K = 1, B = 1, c = 1 (the closed forms
> > above, machine legs A–C); the n = 3 systems: HEX3.B as displayed;
> > n = 4, 5: the battery's exact first-step recursions (GT-BDRAIN,
> > GENIND-BOX-4's compensating instrument) realize the exact species
> > pointwise at the sealed windows.
>
> This is a strengthening of the DISPLAY, not of the truth: the m = 2
> and n = 3 members already sit in the species at their proved pins,
> and the induction below PROPAGATES the rate clause, so the package
> that closes under GENIND.B's strong induction is P(k)-with-(A2-RATE).
> [ar1 2026-08-10, GAP-1 repair: as sealed, this closure sentence
> exceeded its displayed support — GENIND.C′ below proves the rate for
> the SIMPLE slice only, while (A2-RATE) as displayed pins the FULL
> complement, whose CS-stratum drain component (first consumed with
> CS-bearing (4, d) children at n = 5, C1(iii)'s GROWING regime) had no
> displayed all-window rate. The leg is now supplied: ANNEX-LEMMA
> GENIND-C2 (the r1 append below) derives the CS-drain rate from the
> displayed entry pricing + (CS-1)'s stage-window slot geometry, at
> window-deficit slope ≥ 2 — under (CS-1) alone, a clause of the same
> [GENIND-H] the strong induction already assumes (de facto discharged
> at n = 4). Read the closure sentence WITH that split: simple part by
> GENIND.C′ unconditionally; CS-drain part by GENIND-C2 given (CS-1);
> every displayed consumer of S5.2's vanishing bullet needs only the
> simple part.]”

**CONDITIONALITY:** **This is the repaired form of P(k)'s fourth member, and it is riddered twice more downstream.** The `[ar1]` layer splits the closure into a simple part (unconditional) and a CS-drain part (conditional on (CS-1)); the 2026-08-12 round-2 correction then upgrades that condition to **(CS-1Q), verified per genre** (`.52`). **The last clause of the `[ar1]` rider is the one a chapter cut should carry: “every displayed consumer of S5.2's vanishing bullet needs only the simple part.”**

**SUPERSESSION KIND:** the species pin itself = `inventory completion` (a consumed hypothesis component supplied). The `[ar1]` layer = `scope-pin` (the closure's reach is pinned to a two-part split). **Not a `replacement`:** neither the sealed (A2) wording nor (A2-RATE)'s display is withdrawn.

**TARGETS:** shard 1 `.13` (P(k)'s fourth member), `.45`, `.46`.

**CHAIN:** sealed “exact-complement (A2)” → **(A2-RATE)** species pin → `[ar1]` two-part split (simple by C′; CS-drain by GENIND-C2 under (CS-1)) → R9's Q-normalized GENIND-C2 (`.42`) → **R11's C2Q under (CS-1Q), verified per genre (`.51`, `.52`) — TERMINAL for the CS-drain part; GENIND.C′ (`.06`) — TERMINAL for the simple part.** Two terminals, one per consumer class (the pattern shard 1 flagged as a v3 gap in rule 25).

**ARITHMETIC AUDIT:** the (2, d) instance `(K, B, c) = (1, 1, 1)` ✓ — matches `.03`'s derived bound `u(N)/Q^{2(N−1)} ≤ N·Q^{−(N−1)}` exactly (`K·M^B·Q^{−(M−c)}` with K = B = c = 1 is `M·Q^{−(M−1)}` ✓). The n = 3 instance cites HEX3.B's `undecided/q^{3N} ≤ (1+N)q^{−N}`, i.e. `(K, B, c) = (·, 1, 0)` in the same species ✓ — polynomial coefficient, exponential deficit, as the species requires.

**DERIVATION:** The species is exhibited, not proved in general: `.03` proves the m = 2 instance, HEX3.B supplies n = 3, the battery supplies n = 4, 5 pointwise, and `.06` (GENIND.C′) proves that the induction PROPAGATES it on the simple slice.

**RESOLUTION TRACE:** statement lines 2641–2675. proof lines 2606–2639 (`.03`, the ground instance) + 2728–2752 (`.06`, the propagation). correction sites: `[ar1]` in situ 2662–2675; 3308–3557 (R9's GENIND-C2, `.42`); 3592–3721 (R11's C2Q + certification status, `.51`, `.52`).

**TEETH:** machine legs A–C for the ground instance; GT-BDRAIN for n = 4, 5; **nothing for the general species**, which is why it is a hypothesis pin and not a theorem. Disposition: `signed vacuity disclosure` at general (μ, d).

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:THEOREM HEX3.B` — count **8**.

---

### EFF.GENIND.s3of3.05  [lemma]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph with four numbered clauses (R1.2 — ANNEX-LEMMA GENIND-C1, the β-term estimate and the two-regime split), carrying an `[ar1]` rider on its `u_l` definition. verbatim, lines 2677–2726.

> “**R1.2 ANNEX-LEMMA GENIND-C1 (the β-term estimate; the two-regime
> split).** Fix (m, d), window N, and a β-genre per GENIND-3's
> hypothesis with children (μ_l, k_l), depths
> D_l = min_j (v(a_j) + j·k_l) and windows M_l = N − D_l; write
> T_l = Q^{μ_l(M_l−1)} for the child totals and u_l = u_{μ_l,d}(M_l)
> [ar1 2026-08-10: the FULL complement, as written — its rate member is
> supplied by GENIND.C′ (simple part) + ANNEX-LEMMA GENIND-C2 (CS-drain
> part, under (CS-1); the r1 append below)]. Then:
> (i) [route prefactor] the genre's relative mass obeys
> ρ_g ≤ Q^{−(D_l−1)} for EACH child index l: the j = 0 term of the min
> gives D_l ≤ v(a₀), so the genre lies inside {v(a₀) ≥ D_l}, whose
> relative mass is exactly Q^{−(D_l−1)} (π-levels 1..D_l−1 of a₀
> pinned to zero — d·(D_l−1) q-digits; level 0 is pinned in every
> state). Machine (leg E): the committed loci obey it — M6's displayed
> law (q−1)²q^{6N−17} gives ρ = (q−1)²q^{−11} ≤ q^{−3} (D = 4) at
> q = 2,3,4,5; PSTEEP3 (2,5): 2^{−7} ≤ 2^{−2} (D = 3); PSTEEP4 (2,6):
> 2^{−11} ≤ 2^{−3} (D = 4).
> (ii) [composition through the fibration] the genre's contribution to
> u_{m,d}(N) is (prefactor count)·[Π_l T_l − Π_l (T_l − u_l)] —
> GENIND-3(c)'s product fibration (onto, constant fiber) with "the
> frame is conservative-undecided iff some child is". Bounding the
> inclusion–exclusion by the UNION BOUND (leg F: the difference
> Σ_l u_l·Π_{j≠l}T_j − [ΠT − Π(T−u)] expands with nonnegative
> coefficients in (u_l, T_l − u_l) at r = 2, 3 — no exactness is
> needed for the BOUND direction; see R6), the relative contribution
> is ≤ ρ_g · Σ_l u_l/T_l.
> (iii) [the two regimes — both O(poly(N)·Q^{−(N−c)})] Fix any
> threshold c₀ ≥ 1 and split on the child window:
>   * GROWING (M_l > c₀): the child's (A2-RATE) at its strictly lower
>     degree μ_l·d < m·d ((IH), degree descent GENIND-1(iii)) gives
>     u_l/T_l ≤ K·M_l^B·Q^{−(M_l−c)}; with (i),
>     contribution_l ≤ K·N^B·Q^{−(D_l−1)−(M_l−c)} =
>     K·N^B·Q^{−(N−c−1)} — the exponents COMPOSE EXACTLY because
>     D_l + M_l = N (leg D verifies the identity from the hull data at
>     all six committed extractions: M6, TWOCHILD A/B, PSTEEP3,
>     PSTEEP4, SS6).
>   * BOUNDED (M_l ≤ c₀): the child limit is never invoked; the
>     trivial u_l/T_l ≤ 1 and (i) alone give
>     contribution_l ≤ Q^{−(D_l−1)} = Q^{−(N−M_l−1)} ≤ Q^{−(N−c₀−1)}
>     — the route prefactor carries the whole rate, which is Codex's
>     bounded-M_l half, now displayed.
> (iv) [genre count] a β-genre's datum at window N is a partition
> arrangement of m (finitely many types for fixed m) plus one integer
> slope per side, each slope ≤ v(a₀) ≤ N−1: at most p̃(m)·N^m live
> genres — polynomial in N of degree ≤ m. Summing (ii)–(iii) over
> children and (iv) over genres: the recursion's β-part contributes
> ≤ m·p̃(m)·K·N^{m+B}·Q^{−(N−c′−1)} relative mass, c′ = max(c, c₀) —
> exactly the consumed sentence's O(poly(N)·Q^{−(N−c)}), now DERIVED
> from the displayed (A2-RATE) + GENIND-3's fibration + the depth
> identity. ∎”

**CONDITIONALITY:** **Conditional on (A2-RATE) at the children's strictly lower degrees, i.e. on the (IH) with the species pin** — which is exactly the closure `.04` establishes. Its `u_l` is the FULL complement, so it inherits the two-part conditionality of `.04`: simple part unconditional, CS-drain part under (CS-1Q) after R11.

**ARITHMETIC AUDIT (compiler-computed; every displayed inequality and instance re-derived):**
* **(i) the prefactor.** `D_l = min_j(v(a_j) + j·k_l) ≤ v(a₀)` (the j = 0 term) ✓, so the genre ⊆ `{v(a₀) ≥ D_l}`. The relative mass of `{v(a₀) ≥ D}` in a system whose a₀ ranges over `(O/π^N)[x]_{<d}` with `ā₀ = 0`: levels 1..D−1 pinned, i.e. `d(D−1)` q-digits fixed out of `d(N−1)` ⟹ relative mass `q^{−d(D−1)} = Q^{−(D−1)}` ✓ **exactly as displayed**.
* **M6 instance:** locus `(q−1)²q^{6N−17}`, total `q^{6(N−1)} = q^{6N−6}`, so `ρ = (q−1)²q^{−11}` ✓. Bound `Q^{−(D−1)} = q^{−3}` at D = 4 ✓. Check `(q−1)²q^{−11} ≤ q^{−3}` ⟺ `(q−1)² ≤ q⁸` ✓ for all q ≥ 2 (at q = 5: 16 ≤ 390,625 ✓).
* **PSTEEP3 (2,5):** locus 32 = 2⁵ of `2^{3·4} = 2^{12}` ⟹ `ρ = 2^{−7}` ✓; bound at D = 3 is `2^{−2}` ✓; `2^{−7} ≤ 2^{−2}` ✓.
* **PSTEEP4 (2,6):** locus 512 = 2⁹ of `2^{4·5} = 2^{20}` ⟹ `ρ = 2^{−11}` ✓; bound at D = 4 is `2^{−3}` ✓ ✓. **All three machine-leg-E instances reproduce from shard 1's own locus data.**
* **(iii) GROWING, the exponent composition.** `Q^{−(D_l−1)}·Q^{−(M_l−c)} = Q^{−(D_l+M_l−1−c)} = Q^{−(N−1−c)}` using `D_l + M_l = N` ✓ — the displayed `Q^{−(N−c−1)}` ✓. **The identity `D_l + M_l = N` is `M_l := N − D_l` by definition** (shard 1 `.24`), so leg D verifies a definitional identity against hull data — a consistency check on the *extraction*, not on the algebra.
* **(iii) BOUNDED.** `Q^{−(D_l−1)} = Q^{−(N−M_l−1)}` ✓ by the same identity; and `M_l ≤ c₀` ⟹ `−(N−M_l−1) ≤ −(N−c₀−1)` ✓.
* **(iv) genre count.** slopes ≤ `v(a₀) ≤ N−1`, at most m sides ⟹ at most `N^m` slope tuples times `p̃(m)` partition types ✓ polynomial of degree ≤ m ✓. Final aggregation `m·p̃(m)·K·N^{m+B}` ✓ (m children × p̃(m)N^m genres × K·N^B).
* **(ii) the union bound.** `Π T − Π(T−u) ≤ Σ_l u_l Π_{j≠l} T_j` — expanding `Π(T_j − u_j)` and comparing, the difference is a sum of products with at least two u-factors, all nonnegative ✓; and dividing by `Π T_l` gives `≤ Σ_l u_l/T_l` ✓. **The claim “no exactness is needed for the BOUND direction” is exactly R6.2's separation** (`.23`).

**DERIVATION:** Displayed. Justification tags: (i) = `computation` (slot count) + machine leg E; (ii) = `by XREF GENIND-3(c)` (shard 1 `.24`/`.25`) + `computation` (union bound, leg F) + `by XREF R6`; (iii) = `by XREF` (A2-RATE) at lower degree + `by XREF GENIND-1(iii)` (degree descent) + `computation` + leg D; (iv) = `computation`.

**RESOLUTION TRACE:** statement lines 2677–2726. proof lines — displayed. correction sites: `[ar1]` in situ 2682–2684; the `u_l` rate member re-conditioned at 3712–3721 (`.52`, `.53`).

**TEETH:** machine legs D, E, F of `genind_annexr_supp.py` @ `f5271e4` (GREEN) — the depth identity at six committed extractions, the prefactor bound at three committed loci, and the union-bound dominance symbolically at r = 2, 3. Disposition: executable regression, **with a disclosed reach limit: legs D/E cover six extractions and three loci, all at n ≤ 6.**

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:S2.2` — count **19** (the slot count behind (i)).

---

### EFF.GENIND.s3of3.06  [theorem]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R1.3 — ANNEX-THEOREM GENIND.C′, the quantitative vanishing clause) with its proof and an `[ar1]` c-choice rider. verbatim, lines 2728–2752.

> “**R1.3 ANNEX-THEOREM GENIND.C′ (the vanishing clause, quantitative
> form — the induction closed).** For the simple slice of each (m, d):
> there are (K, B, c) with u^{simple}_{m,d}(N)/Q^{m(N−1)} ≤
> K·N^B·Q^{−(N−c)} at every window N ≥ 1. *Proof (lexicographic
> induction on (degree m·d, window N), the S5.2 recursion's own
> shape).* Head: Q^{(m−1)(N−1)}/Q^{m(N−1)} = Q^{−(N−1)}. α-term k
> (same degree, window N−mk < N): the α(k) locus's relative mass
> factor is (Q−1)Q^{−k·m(m+1)/2} (GENIND.A(I)); against the window
> induction's bound at N−mk the exponents recompose to
> (Q−1)Q^{−k·c(m)}·[K(N−mk)^B·Q^{−(N−c)}], and Σ_{k≥1}(Q−1)Q^{−k·c(m)}
> ≤ 1 for c(m) ≥ 1: the α-sum is ≤ K·(N−m)^B·Q^{−(N−c)}. β-terms:
> GENIND-C1 gives ≤ m·p̃(m)·K'·N^{m+B'}·Q^{−(N−c'−1)} with the
> children's constants (degree induction). Choosing **c := c′ + 1**
> [ar1 2026-08-10, MINOR-1: the c-choice displayed at source — c′ =
> max(children's c, c₀) is degree-induction data, so no circularity;
> with c = c′ + 1 the β-leg's Q^{−(N−c′−1)} = Q^{−(N−c)} EXACTLY, and
> c ≥ c₀ + 1 ≥ 2 ≥ 1 absorbs the head leg (Q^{−(N−1)} ≤ Q^{−(N−c)} iff
> c ≥ 1); the α-leg re-enters at the same degree with this same c, the
> window induction's own constant], B = m + B' + 1 and
> K large enough that K·[N^B − (N−m)^B] dominates the head + β
> coefficients (a degree-(B−1) polynomial inequality, satisfiable
> since N^B − (N−m)^B has positive leading coefficient m·B·N^{B−1}),
> the three legs sum to ≤ K·N^B·Q^{−(N−c)}: the induction closes. The
> m = 2 closed forms realize (K, B, c) = (1, 1, 1) — the ansatz is
> sharp at the ground instance. ∎”

**CONDITIONALITY:** **UNCONDITIONAL on the simple slice** — the one unconditional addition of the whole annex stack, and the reason `.04`'s split is honest. Its scope is exactly THEOREM GENIND.C's (shard 1 `.46`): the simple slice, all (m, d), every window `N ≥ 1` — **and `N ≥ 1` consumes R3's window-1 rider** (`.13`).

**ARITHMETIC AUDIT (compiler-computed; every leg re-derived):**
* **Head.** `Q^{(m−1)(N−1)}/Q^{m(N−1)} = Q^{−(N−1)}` ✓.
* **α-leg.** The α(k) locus is `(Q−1)Q^{m(N−1)−k·m(m+1)/2}` (shard 1 `.08`), so its relative mass is `(Q−1)Q^{−k·m(m+1)/2}` ✓. Recomposition: the sub-system at window `N−mk` has total `Q^{m(N−mk−1)}`, so the α-branch's absolute contribution is `(Q−1)Q^{k·c(m)}·u(N−mk)` (shard 1 `.21`), whose relative share is `(Q−1)Q^{k·c(m)}·Q^{m(N−mk−1)}/Q^{m(N−1)}·[u(N−mk)/Q^{m(N−mk−1)}]` = `(Q−1)Q^{k·c(m) − km²}·[…]` = `(Q−1)Q^{−k·m(m+1)/2}·[…]` ✓ (since `km² − k·m(m−1)/2 = k·m(m+1)/2` ✓). The displayed intermediate `(Q−1)Q^{−k·c(m)}` differs from `(Q−1)Q^{−k·m(m+1)/2}` by `Q^{−km}`; **both appear in the passage, at different points of the recomposition, and the geometric-sum step uses the weaker `Q^{−k·c(m)}`** — `Σ_{k≥1}(Q−1)Q^{−k·c(m)} ≤ 1` requires `(Q−1)·Q^{−c(m)}/(1−Q^{−c(m)}) ≤ 1` ⟺ `(Q−1) ≤ Q^{c(m)} − 1` ⟺ `Q ≤ Q^{c(m)}` ✓ for `c(m) ≥ 1`, i.e. `m ≥ 2` ✓ — **the displayed side condition is exactly right and tight at m = 2.**
* **c-choice.** `c := c′ + 1` makes the β-leg's `Q^{−(N−c′−1)}` equal `Q^{−(N−c)}` ✓; and `c ≥ 1` makes the head's `Q^{−(N−1)} ≤ Q^{−(N−c)}` ✓. Non-circularity: `c′ = max(children's c, c₀)` is data from the *lower-degree* induction hypothesis ✓, and the α-leg re-enters at the SAME degree with the same c ✓ — so the definition is well-founded on the lexicographic order.
* **K-choice.** `N^B − (N−m)^B` has leading term `mBN^{B−1}` ✓ (binomial), so a degree-(B−1) polynomial inequality is satisfiable for large K ✓.
* **Ground sharpness.** `(K, B, c) = (1, 1, 1)` matches `.03`'s derived bound exactly ✓.
* **Compiler note.** The α-leg's two exponent forms are both correct at their own points but the passage does not spell out the intermediate step between them; the compiler re-derived it above. Recorded as a **compressed step, not a gap** — the arithmetic closes.

**SUPERSESSION KIND:** `license` — supplies the quantitative form the frozen §S5.2 bullet asserted qualitatively. The `[ar1, MINOR-1]` layer = `inventory completion` (the c-choice, previously undisplayed, is displayed at source with a non-circularity argument).

**TARGETS:** shard 1 `.45`, `.46`, `.57`.

**DERIVATION:** Displayed. Justification tags: head = `computation`; α = `by XREF GENIND.A(I)` + `computation` (geometric sum); β = `by XREF GENIND-C1` (`.05`); the closure = `computation` (polynomial dominance).

**RESOLUTION TRACE:** statement lines 2728–2752. proof lines — displayed. correction sites: `[ar1]` in situ 2741–2746.

**TEETH:** the ground instance is machine-checked (legs A–C); **the induction itself is unguarded** — no battery row exercises a lexicographic induction. Disposition: **PROOF-ONLY**, with `.03`'s ground instance as the only anchor.

---

### EFF.GENIND.s3of3.07  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R1.4 — what moves and what does not), carrying `[ar1, MINOR-2]` and a CS-rider. verbatim, lines 2754–2777.

> “**R1.4 What moves, what does not.** GENIND.C's vanishing bullet now
> reads through (A2-RATE) + GENIND-C1 + GENIND.C′ — the consumed rate
> is supplied by the DISPLAYED hypothesis and the displayed two-regime
> estimate; the α/head legs were never in question. Of the five
> committed displays this section consults — W-11's R(M), HEX3.A's
> exact law, HEX3.B's rate, the GT-BDRAIN n = 4, 5 first-step
> recursions, and GENIND-BOX-4's pricing sentence — none is rewritten
> here [ar1 2026-08-10, MINOR-2: the sealed sentence ("No committed
> number, count law, or supplier verdict moves") quantified with no
> scope pointer, the record species the note's own r5
> enumerative-records policy was adopted against; this enumeration
> replaces it]: the n ≤ 3 suppliers
> (W-11, HEX3.A/B) already carried the species at their pins, and the
> n = 4, 5 exact recursions are stronger than the bound at those
> degrees (GENIND-BOX-4's own sentence). GENIND-BOX-4's pricing of the
> per-genre expansion STANDS for what remains compressed (the
> per-genre prefactor ledgers); the box's sharpened defect — the
> hypothesis-WIRING gap Codex named — is cured by this section.
> Step 4's simple part consumes GENIND.C′ verbatim in place of the
> bare bullet; the CS legs keep their [GENIND-H]/(CS-EXACT)
> conditionality unchanged [ar1 2026-08-10: for menu + exactness — the
> CS legs' RATE is now supplied separately by ANNEX-LEMMA GENIND-C2
> under (CS-1) alone (the r1 append below); (CS-EXACT) supplies
> exactness, not a rate, per R6.2's identity-vs-bound separation].”

**CONDITIONALITY:** **The install instruction for the whole R1 repair**, and the sentence that tells a chapter cut which frozen text to read differently: “Step 4's simple part consumes GENIND.C′ verbatim in place of the bare bullet.” Its five-display census is superseded once more by R9's riding MINOR-B, which replaces it with a longer enumeration (`.46`).

**SUPERSESSION KIND:** the section = `license` + `scope-pin`; the `[ar1, MINOR-2]` layer = `replacement` (a non-enumerative record sentence replaced by an enumeration, original quoted) — **the r5 standing rule applied retroactively to the annex's own prose**, which is the clearest evidence that the rule is corpus-level and not round-local. The closing `[ar1]` rider = `provenance-rider` (which clause supplies the rate versus the exactness).

**TARGETS:** shard 1 `.45`, `.57`; shard 2 `.04`.

**ARITHMETIC AUDIT:** “five committed displays” ✓ five enumerated (R(M), HEX3.A, HEX3.B, GT-BDRAIN's recursions, GENIND-BOX-4's sentence). R9's MINOR-B later replaces this with **eleven** named items (`.46`) — audited there.

**DERIVATION:** Not a mathematical unit; an install record.

**RESOLUTION TRACE:** statement lines 2754–2777. correction sites: `[ar1]` in situ 2761–2765 and 2774–2777; 3563 (R9's MINOR-B census replacement, `.46`); 3714–3721 (R11's consumer sweep, `.53`).

**TEETH:** NONE — an install record. Its five-display census is verifiable against shard 1/2 units and is (`.46` notwithstanding) correct as far as it goes.

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:THEOREM HEX3.A` — count **11**; `THEOREM HEX3.B` — count **8**; `R(M)` — count **21**.

---
### EFF.GENIND.s3of3.08  [supplier-finding]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph with a block quotation (R2.0 — CODEX F1, quoted). verbatim, lines 2779–2794.

> “### R2 (CODEX F1): the unit-pivot step — GENIND-6(c)'s onto/constant-fiber condition displayed at schema level
>
> **R2.0 The finding, quoted (F1, CONFIRMED GAP, disclosure overlap).**
>
> > "GENIND-6(c)'s onto-with-constant-fiber is carried by 'triangular
> > with exact budget floors' + 'the same S2.2 slot bookkeeping' — and
> > triangularity alone does NOT give surjectivity/constant fibers
> > over truncated DVRs (Codex's valid toy: (x, y) ↦ (x, (x+π)y)
> > mod π², triangular, fiber collapses at x = 0). The missing
> > displayed step is the unit-pivot condition (the division ledger's
> > pivots are units because the extracted factors are MONIC — true,
> > used, never displayed as the load-bearing condition)."
>
> The same sentence pattern is consumed at GENIND-3 step (3) ("the
> fiber count per genre is the S2.2 slot count…"), so the rider
> covers both sites.”

**CONDITIONALITY:** CONFIRMED GAP, “with disclosure overlap” (the honesty boxes had already flagged onto-ness at multi-child genres as a hostile target — shard 1 `.26`(a) — so the finding partly lands in territory the note had marked). **The finding is constructive: it supplies a counterexample shape, not merely a doubt.**

**ARITHMETIC AUDIT (compiler-computed, on the toy):** over `O/π²`, the map `(x, y) ↦ (x, (x+π)y)`. At `x ∈ (π)`, `x + π ∈ (π)` is a non-unit; then `(x+π)y` ranges only over `(π)` as y varies, and every value has `|{y}| = ` the size of the annihilator — the fibre size jumps. Concretely over `ℤ/4` (π = 2): at `x = 0`, `(0+2)y = 2y ∈ {0, 2}` for `y ∈ {0,1,2,3}` — image size 2, fibre size 2; at `x = 1`, `3y` is a bijection — image size 4, fibre size 1 ✓. **The toy is valid and the collapse is exactly as described.** Triangularity holds throughout ✓.

**DERIVATION:** Not a mathematical unit; a defect report with a counterexample.

**RESOLUTION TRACE:** statement lines 2779–2794. correction sites: none (this is the finding).

**TEETH:** **`decorrelated-model audit`.** No battery row could produce this: the runner only ever executes monic ledgers, so the failure mode is off its state space by construction — the note's own R2.3 says as much (“a non-unit pivot would surface there as a fiber-size split, the signature those runs exclude at their windows”), i.e. the runs *exclude* the signature and therefore cannot *find* the missing hypothesis.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:S2.2` — count **19**.

---

### EFF.GENIND.s3of3.09  [lemma]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R2.1 — the unit-pivot rider at schema level). verbatim, lines 2796–2810.

> “**R2.1 The rider (schema level).** In GENIND-6(c)'s coordinate map
> and GENIND-3 step (3)'s fiber sentence, read "triangular" as
> **triangular with UNIT pivots**: in a coordinate order realizing the
> triangular structure, each solved output slot is
> c·(its input slot) + (a function of strictly earlier input slots)
> with pivot c a unit of that slot's truncated ring O/π^w. Unit pivots
> are what license the S2.2 slot bookkeeping: back-substitution solves
> any target slot by slot (input = c⁻¹·(target − earlier-part), c⁻¹
> existing because units of O/π^w invert), so the map is ONTO; and the
> fiber over every target is exactly the free slots (each
> pinned/priced slot solved uniquely, each free slot unconstrained) —
> a target-independent q-power. Without unit pivots both conclusions
> fail, and Codex's toy is the exact failure shape: (x, y) ↦
> (x, (x+π)y) mod π² is triangular, but at x ∈ (π) the pivot x + π is
> a non-unit and the y-fiber collapses.”

**CONDITIONALITY:** **A schema-level rider covering TWO frozen sites** (shard 1 `.36` and `.24`'s step (3)). It supplies a *condition*; `.10` supplies its *verification* per ledger species.

**SUPERSESSION KIND:** `license` — an underived step consumed silently is supplied. **Not `wording-rider`:** although the surface instruction is “read X as Y”, the operative content is a new condition with a proof of what it buys (onto + constant fibre), which a wording substitution is not. **This is the shard's canonical illustration of rule 18's warning that near-identically phrased riders are not interchangeable.**

**TARGETS:** shard 1 `.36`, shard 1 `.24`.

**ARITHMETIC AUDIT:** back-substitution over `O/π^w`: given a triangular system with unit pivots, solving slot by slot in the triangular order yields a unique preimage for each target ✓ (units invert in `O/π^w` ✓), so ONTO with fibre = the free slots ✓, a target-independent `q^{#free}` ✓. The argument is correct as displayed.

**DERIVATION:** Displayed. Justification tags: `computation` (back-substitution over a truncated DVR) + the toy as the sharpness witness.

**RESOLUTION TRACE:** statement lines 2796–2810. correction sites: none.

**TEETH:** machine leg G (`.11`), a **planted mutant** realizing the toy.

---

### EFF.GENIND.s3of3.10  [lemma]

**CANONICAL STATEMENT:** FORM: bold-headed bulleted display (R2.2 — why the pivots ARE units, per ledger species). verbatim, lines 2812–2840.

> “**R2.2 Why the pivots here ARE units (re-derived from the displayed
> mechanisms; the ledger species of GENIND-3 steps (1)–(3) /
> GENIND-6(a)(c), enumerated).**
> * RECENTER ledgers (GENIND-2(a), consumed at step (1) and
>   GENIND-6(a)): the update of the Φ-adic coordinates under
>   x ↦ x + s is the binomial matrix, displayed at S3 as "triangular
>   with unit diagonal" — the diagonal entries are the binomials
>   C(j, j) = 1. Pivot = 1.
> * SCALE/CONTENT moves (x = π^k y; divide by π^D): digit-slot
>   RELABELINGS (window shifts with the ghost-slot bookkeeping of
>   GENIND-2(a)) — no slot is multiplied inside its ring; no pivot
>   arises.
> * DIVISION ledgers (step (2)'s Hensel split; GENIND-6(a)'s "monic
>   cofactor with PER-COEFFICIENT certified windows (the triangular
>   division ledger)"): every division row divides BY A MONIC factor —
>   the frame f is monic (S1's states) and the extracted blocks are
>   monic (W12-S2.1's monic-factor form; GENIND-6(a)). Long division
>   by a monic divisor determines each new cofactor coefficient with
>   the divisor's LEADING coefficient as the pivot, = 1. The
>   non-unit-lead cofactor of the shallower-co-block case (step (1))
>   is never a divisor in any ledger row — it is an OUTPUT whose lead
>   carries the dropped content.
> * LETTER scalings: multiplication by the co-blocks' unit values
>   (W12-L1(b) product form / J-D0) — units by that lemma's own
>   computation.
> So each ledger row's pivot is the literal unit 1 (or a W12-L1(b)
> unit): MONICITY is the load-bearing condition, now displayed.
> The toy's pivot x + π is the lead of a non-monic multiplier — a
> shape the displayed species exclude.”

**CONDITIONALITY:** **An ENUMERATED species check — four ledger kinds, each with its pivot identified.** The third bullet is the load-bearing one and it also disposes of the obvious objection (the non-unit-lead cofactor of the shallower-co-block case), by observing that it is an OUTPUT, never a DIVISOR. **This is a genuine proof at schema level; what remains compressed is the per-genre ledger, and `.11` says so.**

**ARITHMETIC AUDIT (compiler-computed):**
* Recenter: the binomial update matrix under `x ↦ x + s` has entries `C(i, j)s^{i−j}`; its diagonal is `C(j,j) = 1` ✓, so triangular with unit diagonal ✓ — and shard 1 `.21`'s proof displays exactly that phrase ✓.
* Scale/content: `x = π^k y` and division by `π^D` are index shifts on digit slots; no slot is multiplied by a ring element ✓ — so no pivot exists to be non-unit ✓.
* Division by a monic `g` of degree `e`: long division determines each quotient coefficient as `(current leading term)/(lead of g)` = `(…)/1` ✓ — pivot 1 ✓.
* Letter scalings: units by W12-L1(b) ✓ (cited, not re-derived).
* **Completeness of the species list.** GENIND-3's steps are (1) recenter+scale+normalize, (2) Hensel split, (3) read equivalence + fiber count; GENIND-6(a)(c) add the division ledger and the coordinate map. Every ledger row in those steps falls under one of the four bullets ✓ — recenter (step 1), scale/content (step 1), division (step 2 and (a)), letters (step 3 and (c)). **The enumeration is exhaustive over the displayed mechanisms**, which is exactly the scope R2.3 then declares.

**DERIVATION:** Displayed. Justification tags: bullets 1, 2, 3 = `computation` `by XREF GENIND-2(a)` / `by XREF W12-S2.1`; bullet 4 = `by XREF W12-L1(b)` + `by XREF LEMMA J-D0`.

**RESOLUTION TRACE:** statement lines 2812–2840. correction sites: none.

**TEETH:** machine leg G (`.11`) exercises the *condition*, not the species check; the species check is **PROOF-ONLY**, and R2.3 supplies its coverage sentence.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:W12-S2.1` — count **9**; `W12-L1` — count **30**.
XREF: `lean/notes/openmath/JD0_PROOF_2026-08-08.md:J-D0` — count **25**.

---

### EFF.GENIND.s3of3.11  [run-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R2.3 — verification and scope honesty). verbatim, lines 2842–2852.

> “**R2.3 Verification.** Machine leg G (genind_annexr_supp.py @
> f5271e4, GREEN): over ℤ/4, (x+2)·y is bijective in y iff x is odd
> (a unit) — the toy's collapse — while the monic-pivot form (1+2x)·y
> is bijective at every x. Instance contact for (c)'s count: the
> committed EXHAUSTIVE onto-with-constant-fiber enumerations at M6
> (S4.3 machine record: fibers {512} = q⁹ / {128} = q⁷ at every
> enumerable window) — a non-unit pivot would surface there as a
> fiber-size split, the signature those runs exclude at their windows.
> Scope honesty: the rider displays the condition and its supply; the
> per-genre ledgers remain compressed per the S4.3 honesty box, and
> the multi-block hostile targets it names stay named.”

**ARITHMETIC AUDIT (compiler-computed):** over `ℤ/4`, `(x+2)y` bijective in y iff `x+2` is a unit iff `x + 2` is odd iff `x` is odd ✓ (x odd ⟹ x+2 odd ⟹ unit; x even ⟹ x+2 even ⟹ zero divisor). And `(1+2x)` is odd for every x ✓ — always a unit, always bijective ✓. **The leg's two claims are exactly right.** The M6 fibre figures `{512} = 2⁹` and `{128} = 2⁷` reproduce from shard 1 `.38`'s exponent audit ✓.

**CONDITIONALITY:** **Scope honesty is explicit and narrow**: the rider supplies the condition, the per-genre ledgers stay compressed, and the multi-block hostile targets stay named. So R2 closes the *displayed* gap and not the *compression* debt.

**DERIVATION:** Not a mathematical unit; a verification record.

**RESOLUTION TRACE:** statement lines 2842–2852. correction sites: none.

**TEETH:** **planted mutant, fired** (leg G realizes the exact failure shape and shows the monic form immune) + **instance contact** at M6's exhaustive enumerations, with an honest statement of what that contact can and cannot show. Disposition: planted mutant + `disclosed non-repair` for the compressed ledgers.

**PIN VERIFICATION:** `f5271e4` ✓; `genind_annexr_supp.py` ✓ and its output ✓ EXIST.

---

### EFF.GENIND.s3of3.12  [supplier-finding]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph with a block quotation (R3.0 — CODEX F2, the window-1 scope leak). verbatim, lines 2854–2863.

> “### R3 (CODEX F2): the window-1 convention rider
>
> **R3.0 The finding, quoted (F2, CONFIRMED GAP — scope leak).**
>
> > "the S1 convention states 'window N ≥ 2', yet GENIND-2(a)'s
> > α-transport invokes the same system at window N − mk = 1 (first
> > at m = 2, N = 3, k = 1 — Codex's instance, admissible since
> > mk = 2 ≤ N−1), and GENIND-6's M6 ledger consumes a degree-2 child
> > at window 1 ('the child DRAINS instantly'). … neither GENIND-2
> > nor (IH) formally supplies it."”

**ARITHMETIC AUDIT:** Codex's instance — at `(m, N, k) = (2, 3, 1)`, admissibility is `mk ≤ N−1` i.e. `2 ≤ 2` ✓ admissible, and the target window is `N − mk = 3 − 2 = 1` ✓ **outside the stated convention `N ≥ 2`**. The M6 instance: at `N = 5` the child window is `N − 4 = 1` ✓ (shard 1 `.38`). **Both cited leaks are real and minimal.**

**CONDITIONALITY:** CONFIRMED GAP. A *scope* leak, not a false claim: the transports are right, the convention did not cover their targets.

**DERIVATION:** Not a mathematical unit; a defect report.

**RESOLUTION TRACE:** statement lines 2854–2863. correction sites: none.

**TEETH:** **`decorrelated-model audit`** — a convention-boundary check no battery row performs (the runner simply computes at window 1 without consulting a convention).

---

### EFF.GENIND.s3of3.13  [convention]

**CANONICAL STATEMENT:** FORM: bold-headed bulleted display (R3.1 — the window-1 convention rider and its enumerated scope). verbatim, lines 2865–2889.

> “**R3.1 The convention rider.** Extend S1's cluster-system
> conventions and the P-package reading to **window N = 1**, whose
> content is FORCED by S1's own definitions read at N = 1:
> * states: a_j ∈ (O/π¹)[x]_{<d} with ā_j = 0 forces every a_j = 0 —
>   exactly q^{dm(N−1)} = q⁰ = 1 state;
> * read: a₀ = 0 gives v(a₀) ≥ 1 = N, so the conservative read exits
>   UNDECIDED before consulting any digit — DRAIN;
>   u_{m,d}(1) = total = 1;
> * grammar coherence: DRAIN's locus law q^{d(m−1)(N−1)} = 1 = the
>   whole space; α needs mk ≤ N−1 = 0 (none); DEC/β/CS need a polygon,
>   i.e. v(a₀) < N (none) — of the five events exactly one is
>   inhabited;
> * the window-1 package: menu = {DRAIN} (exact; (A1)-admissible with
>   count 1 = q⁰), (A0) vacuous (no decided leaves), complement
>   u = total exactly.
> Scope of application, enumerated — window-1 systems arise in this
> note only as TRANSPORT TARGETS (S1's ambient window stays ≥ 2):
> (a) GENIND-2(a)'s α(k) endpoint mk = N−1, first at
> (m, N, k) = (2, 3, 1); (b) GENIND-3/GENIND-6 child extractions at
> M_l = 1 — the M6 ledger at N = 5 ("the child DRAINS instantly — its
> entry datum is the whole certified content" is this rider's content
> verbatim at that instance); (c) the S5.2 recursion's boundary
> u(1) = 1, consumed by R1.1's telescope (whose closed form
> u(2ℓ+1) = (ℓ+1)Q^{2ℓ} − ℓQ^{2ℓ−1} returns 1 at ℓ = 0 — coherent
> both ways).”

**CONDITIONALITY:** **The content is FORCED, not chosen** — every clause is S1's own definitions evaluated at N = 1, which is why this is a `convention` unit and not a new hypothesis. **The scope is enumerated at three sites** (rule-compliant with the standing rule), and all three are verifiable: (a) shard 1 `.21`, (b) shard 1 `.24`/`.34`/`.38`, (c) shard 1 `.45` and `.03` here.

**SUPERSESSION KIND:** `inventory completion` — the missing boundary member of an existing definition is supplied, with its consumption sites enumerated.

**TARGETS:** shard 1 `.07`, `.21`, `.24`, `.34`, `.38`, `.45`.

**ARITHMETIC AUDIT (compiler-computed; every clause re-derived at N = 1):** state count `q^{dm(N−1)} = q⁰ = 1` ✓; `a_j ∈ (O/π)[x]_{<d}` with `ā_j = 0` forces `a_j = 0` ✓ (the reduction map is injective on `O/π`); `v(0) = ∞ ≥ 1 = N` ⟹ DRAIN ✓; DRAIN's locus law `q^{d(m−1)(N−1)} = q⁰ = 1` = the whole space ✓; α needs `mk ≤ 0` with `k ≥ 1`, impossible ✓; DEC/β/CS need `v(a₀) < N = 1`, i.e. `v(a₀) = 0`, impossible since `ā₀ = 0` ✓. **Exactly one of five events inhabited ✓.** Coherence with `.03`'s closed form at `ℓ = 0`: `u(1) = (0+1)Q⁰ − 0·Q^{−1} = 1` ✓ — **and note this is a genuine two-way check: the closed form was derived assuming `u(1) = 1`, and the rider independently derives `u(1) = 1` from the definitions.**

**DERIVATION:** Displayed; every clause is a definitional evaluation.

**RESOLUTION TRACE:** statement lines 2865–2889. correction sites: none.

**TEETH:** machine leg I (`.14`), plus a decorrelated sympy re-solve.

---

### EFF.GENIND.s3of3.14  [run-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R3.2). verbatim, lines 2891–2895.

> “**R3.2 Verification.** Machine leg I (@ f5271e4, GREEN):
> (m, Q) ∈ {2, 3, 4} × {2, 3, 4} — 1 state, v(a₀) ≥ 1 = N, DRAIN,
> u(1) = total = 1. Decorrelated leg: the adjudication's row 2 records
> Codex's sympy re-solve of the S5.2 recursion under exactly this
> boundary (m = 2 closed forms exact at N = 2..12).”

**ARITHMETIC AUDIT:** the leg's grid is `3 × 3 = 9` cells ✓; each asserts the same four facts, all re-derived at `.13` ✓. The decorrelated re-solve covers `N = 2..12`, a subrange of leg A's `N = 2..14` ✓ — **two models, two implementations, same closed forms.**

**CONDITIONALITY:** none — a verification.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2891–2895. correction sites: none.

**TEETH:** executable regression + **`accepted-with-decorrelation-supplied`** (the sympy re-solve is a *different model's* implementation of the same recursion — the strongest decorrelation available for a symbolic claim).

---

### EFF.GENIND.s3of3.15  [supplier-finding]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph with a block quotation (R4.0 — CODEX F5, the CS4-F floor). verbatim, lines 2897–2904.

> “### R4 (CODEX F5): the CS4-F visibility floor — display erratum at S5.3 + GENIND.A(IV)
>
> **R4.0 The finding, quoted (F5, CONFIRMED, regraded MINOR display).**
>
> > "CS4-F(k)'s law (q(q−1)/2)·q^{4N−10k−4} displayed without its
> > visibility floor 4k ≤ N−1 at S5.3 AND GENIND.A(IV); at (2,2,1)
> > the display returns 2^{−6}, true locus 0; the sibling CS4-E
> > carries its floor explicitly."”

**ARITHMETIC AUDIT:** at `(q, N, k) = (2, 2, 1)`: `(2·1/2)·2^{8−10−4} = 1·2^{−6}` ✓ **a non-integer count** — the sharpest possible signature. The sibling comparison is right: CS4-E carries `2h ≤ N−1` via `[r1, PE1-M3]` (shard 1 `.48`) and CS4-F carries nothing (shard 1 `.49`) ✓.

**CONDITIONALITY:** CONFIRMED, regraded MINOR **because the runner already gated on the floor** (`.17`) — so no committed number is affected. A display defect with zero downstream numeric consequence, and the regrade records exactly that.

**DERIVATION:** Not a mathematical unit; a defect report.

**RESOLUTION TRACE:** statement lines 2897–2904. correction sites: none.

**TEETH:** **`decorrelated-model audit`** — and note the asymmetry: the *runner* had the floor and the *display* did not, so no run could have surfaced it. Only a reader comparing display to sibling could, which is what a fresh model did.

---

### EFF.GENIND.s3of3.16  [lemma]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R4.1 — the erratum with the floor re-derived). verbatim, lines 2906–2915.

> “**R4.1 The erratum, floor re-derived.** Read BOTH displays — S5.3's
> CS4-F(k) entry and GENIND.A(IV)'s first-instances clause ("the
> f-first genre FULL(k)-(2²)…") — WITH the floor: **CS4-F(k) has
> VISIBILITY FLOOR 4k ≤ N−1.** Derivation (the same one PE1-M3 ran
> for the E-sibling's 2h ≤ N−1): the genre's heights are
> (4k, 3k, 2k, k) (S5.3's own display), so v(a₀) = 4k on the locus;
> the keying fires DRAIN first at v(a₀) ≥ N (GENIND.A(I)), so the
> genre is inhabited iff 4k ≤ N−1. At (q, N, k) = (2, 2, 1) the
> unfloored display returns (2·1/2)·2^{8−10−4} = 2^{−6} — a
> NON-INTEGER against a true locus of 0.”

**CONDITIONALITY:** A display erratum with a two-line derivation; no count moves.

**SUPERSESSION KIND:** `wording-rider` (“Read BOTH displays … WITH the floor”) — an explicit addition of a side condition to two displayed laws.

**TARGETS:** shard 1 `.49` (S5.3's CS4-F entry) and shard 1 `.11` (GENIND.A(IV)'s first-instances clause).

**ARITHMETIC AUDIT:** heights `(4k, 3k, 2k, k)` on a length-4 side at integer slope k ✓; `v(a₀) = 4k` ✓; DRAIN-first at `v(a₀) ≥ N` ⟹ inhabited iff `4k ≤ N−1` ✓ — re-derived independently at shard 1 `.49` and agreeing.

**DERIVATION:** Displayed. Justification tags: `by XREF` S5.3's own heights display + `by XREF GENIND.A(I)`'s DRAIN-first rule + `computation`.

**RESOLUTION TRACE:** statement lines 2906–2915. correction sites: none.

**TEETH:** machine leg H (`.17`).

---

### EFF.GENIND.s3of3.17  [run-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R4.2 — committed numbers unaffected, with the runner's gate lines cited). verbatim, lines 2917–2925.

> “**R4.2 Committed numbers unaffected — the gate lines cited.** The
> sealed runner gates its genre-F predictor on exactly the floor:
> `while 4 * k <= N - 1:` at **genind_checks.py lines 709 and 869**
> (md5-pinned e7ca150b, consulted read-only). Machine leg H
> (@ f5271e4, GREEN): both gate lines verified verbatim in the pinned
> file; (2,2,1) gated to 0 where the bare display says 2^{−6};
> (2,5,1) above the floor with law 2^{20−10−4} = 2⁶ = 64.
> Display-only, the exact defect species as PE1-M3 — the E-law's
> existing floor sentence at S5.3 stands unchanged.”

**CONDITIONALITY:** **A source-code gate verification — an unusual and strong tooth**: the leg reads two named lines of the md5-pinned runner and confirms the implementation carries the side condition the display omitted.

**ARITHMETIC AUDIT:** `(2,5,1)`: `(q(q−1)/2)q^{4N−10k−4} = 1·2^{20−10−4} = 2⁶ = 64` ✓; floor `4·1 = 4 ≤ N−1 = 4` ✓ above the floor. `(2,2,1)`: `4 > 1` ⟹ gated to 0 ✓.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2917–2925. correction sites: none.

**TEETH:** **source-code gate verification** (leg H) — recorded in the enum as an `executable regression` against the pinned instrument's TEXT rather than its output. **PIN VERIFICATION:** `genind_checks.py` EXISTS ✓; lines 709 and 869 are cited by the leg, not re-read here (the file is md5-pinned and byte-frozen).

---

### EFF.GENIND.s3of3.18  [supplier-finding]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph with a block quotation (R5.0 — CODEX F6, the converse at stage level). verbatim, lines 2927–2934.

> “### R5 (CODEX F6): the converse read at degree level — one rider
>
> **R5.0 The finding, quoted (F6, CONFIRMED, regraded MINOR wording).**
>
> > "S5.1's sufficiency (padding + QRT-G2) proves degree-level
> > existence only; the converse 'm ≥ 4 realizes CS' at stage level
> > (arbitrary m-key clusters) is not established — the padded
> > construction's stage carries 4 keys."”

**CONDITIONALITY:** CONFIRMED, regraded MINOR wording. **The finding is precise: the sufficiency proof produces a 4-key stage at every degree, which establishes a degree-level statement and not an m-indexed stage-level one.**

**ARITHMETIC AUDIT:** shard 1 `.11`'s sufficiency pads a QRT-G2 stage (which has exactly 4 keys) with a degree-(n−4) irreducible ✓ — so the realized stage always has m′ = 4, never an arbitrary m ≥ 4 ✓. **The finding checks.**

**DERIVATION:** Not a mathematical unit; a defect report.

**RESOLUTION TRACE:** statement lines 2927–2934. correction sites: none.

**TEETH:** **`decorrelated-model audit`** — a quantifier-scope reading no run can perform.

---

### EFF.GENIND.s3of3.19  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R5.1 — the degree-level rider with a three-site consumer walk). verbatim, lines 2936–2955.

> “**R5.1 The rider.** Read GENIND.A(IV)'s converse clause
> ("conversely m ≥ 4 realizes CS with positive locus at every q") at
> DEGREE level: **every degree n ≥ 4 realizes a CS event with
> positive locus at every q, both characteristics** — which is what
> S5.1's sufficiency proof delivers (re-derived check: the padding
> block is coprime to the center and separable at level 0, hence a
> DECIDED piece — the padded state's CS event is the QRT-G2(h;(1²))
> stage's, and that stage carries exactly 4 keys at every n). The
> STAGE-level parse — for each m ≥ 4, an m-KEY stage itself opening a
> CS event with positive locus — is NOT claimed by this note.
> Displayed stage-level instances exist at m = 4 (the QRT genres are
> the 4-key system's own), m = 5 (S5.3's embedded genres), and m = 6
> (S4.3's M6/SS6, machine-realized); at general m the stage-level
> statement is left unclaimed (the adjudication marks it likely true
> via general-m embedded genres, not shown). Consumers of (IV),
> re-walked at the three consuming sites this round: S5.2's
> positive-density sentence (a degree-level realization — the quartic
> e-first entry mass), S6's conditionality geography (n ≤ 3 vacuity =
> the necessity half), S7.4's finite enumerability (the necessity
> half). None consumes the stage-level parse.”

**CONDITIONALITY:** **A scope pin with a completeness check attached** — the three consuming sites are walked and none needs the stronger parse, so the pin costs nothing downstream. **The unclaimed statement is explicitly marked “likely true … not shown”**, which is the honest register.

**SUPERSESSION KIND:** `scope-pin`. **Deliberately not `wording-rider`:** no phrase is substituted; a quantifier's intended range is fixed and the stronger reading is disowned.

**TARGETS:** shard 1 `.11`. **Explicitly NOT targeted:** shard 1 `.43` (“the criterion in one line”), which is already degree-level.

**ARITHMETIC AUDIT:** the three consumer sites map to shard 1 `.46` (S5.2's positive-density sentence), `.61` (S6's conditionality geography), `.74` (S7.4's finite enumerability) ✓ — **three for three, and each consumes only the necessity direction or a degree-level realization**, as claimed. The m = 4/5/6 instance list checks: QRT genres (shard 1 `.48`), S5.3's embedded genres (`.50`–`.52`), M6/SS6 (`.33`, `.42`) ✓.

**DERIVATION:** The re-derived check is displayed (the padding block is a decided piece; the stage is QRT-G2's, with 4 keys at every n).

**RESOLUTION TRACE:** statement lines 2936–2955. correction sites: none.

**TEETH:** the three-site consumer walk is itself the verification. Disposition: `transfer audit` (an internal one — a consumer walk over the note's own sites).

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:QRT-G2` — count **10**.

---

### EFF.GENIND.s3of3.20  [run-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R5.2). verbatim, lines 2957–2959.

> “**R5.2 Verification.** The three-site consumer walk above; the
> m = 4, 5, 6 instances' committed laws (W-12 S2.5 pin; S5.3's
> tables; S4.3's machine record).”

**CONDITIONALITY:** **No machine leg** — the verification is a consumer walk plus three committed law citations. The note does not pretend otherwise.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2957–2959. correction sites: none.

**TEETH:** `transfer audit` only; **no executable regression**, and none is needed for a quantifier-scope pin. Disposition: `signed non-applicability`.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:S2.5` — count **9**.

---
### EFF.GENIND.s3of3.21  [supplier-finding]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph with a block quotation (R6.0 — CODEX F4, scoped to the PE8 acceptance artifact). verbatim, lines 2961–2970.

> “### R6 (CODEX F4): the PE8-report notice + identity-vs-bound separated at Step 4's [r1] record
>
> **R6.0 The finding, quoted (F4, CONFIRMED, scoped to the PE8
> acceptance artifact, regraded MINOR at this note).**
>
> > "PE8 §4.1's necessity rationale is false: ∂F/∂u₁ = T₂ − u₂ ≥ 0
> > (claimed non-monotonicity wrong); 1 − Π(1 − u_i/T_i) is
> > coordinatewise increasing; upper bounds + union bound suffice for
> > W-12's (A2); exactness needed only for the stronger
> > exact-complement member."”

**CONDITIONALITY:** **The finding's target is the ACCEPTANCE REPORT, not the note** — “GAP at the PE8 acceptance report” per `.01`'s disposition list, regraded MINOR here. **This is the only finding in the corpus's GENIND arc that lands on the artifact that granted acceptance.** It does not disturb the acceptance: the note's own load-bearing sentences survive (`.23`).

**DERIVATION:** Not a mathematical unit; a defect report against a verifier artifact.

**RESOLUTION TRACE:** statement lines 2961–2970. correction sites: none.

**TEETH:** **`decorrelated-model audit`** — a fresh model checking an acceptance report's mathematics. **No in-house pass audits the report that accepted the note**, structurally.

---

### EFF.GENIND.s3of3.22  [changes-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R6.1 — the notice, with the report left untouched). verbatim, lines 2972–2984.

> “**R6.1 The notice (the report itself stays untouched — its author's
> artifact per the standing rule; the notice lives here and at the
> ledger).** GENIND_passPE8_report.md §4.1 (its L176–178) writes "the
> r = 2 case u₁T₂ + T₁u₂ − u₁u₂ is already not monotone in u₁ once
> u₂ > T₂ − u₂" — FALSE: ∂/∂u₁(u₁T₂ + T₁u₂ − u₁u₂) = T₂ − u₂ ≥ 0
> identically on the admissible domain u₂ ≤ T₂. More: at r = 2, 3,
> ∂/∂u_i[Π_j T_j − Π_j(T_j − u_j)] = Π_{j≠i}(T_j − u_j) ≥ 0 — the
> composed undecided mass is coordinatewise NONDECREASING in the
> child u's, so upper bounds on children DO propagate to an upper
> bound on the frame, and the union bound Σ_i u_i·Π_{j≠i}T_j
> dominates it. The defect sits in the acceptance report's
> elaboration of WHY (CS-EXACT) is needed, not in this note's
> accepted text.”

**CONDITIONALITY:** **Freeze predicate: other authors' artifacts are never edited.** The notice “lives here and at the ledger”. This is the same protocol shard 2 `.58` applies to the PE4/PE5 reports' shared md5 typo.

**SUPERSESSION KIND:** none of the note's own text — this is a **notice against an external artifact**, which the v3 enum has no kind for. Filed as `changes-record` with type `supplier-finding`-adjacent; see §6.3 for the recommendation.

**ARITHMETIC AUDIT (compiler-computed, re-deriving both derivatives):** with `F = u₁T₂ + T₁u₂ − u₁u₂`, `∂F/∂u₁ = T₂ − u₂` ✓, which is `≥ 0` on `u₂ ≤ T₂` ✓ — **the report's claimed non-monotonicity is false, and the condition it names (`u₂ > T₂ − u₂`, i.e. `u₂ > T₂/2`) is irrelevant to the sign** ✓. General r: `G = Π_j T_j − Π_j(T_j−u_j)`, `∂G/∂u_i = +Π_{j≠i}(T_j − u_j) ≥ 0` ✓. Union bound: expanding `Π T − Π(T−u)` by inclusion–exclusion gives `Σ_i u_i Π_{j≠i}T_j` minus terms with ≥ 2 u-factors, all nonnegative ⟹ `G ≤ Σ_i u_i Π_{j≠i}T_j` ✓. **All three of R6.1's assertions verify.**

**DERIVATION:** Displayed (two derivative computations + the union bound).

**RESOLUTION TRACE:** statement lines 2972–2984. correction sites: none.

**TEETH:** machine leg F (`.24`) — symbolic, plus a preregistered decorrelation.

---

### EFF.GENIND.s3of3.23  [scope-record]

**CANONICAL STATEMENT:** FORM: bold display (R6.2 — the identity-vs-bound separation, a dated rider on a frozen record). verbatim, lines 2986–2997.

> “**R6.2 The separation (a dated rider on Step 4's frozen [r1]
> record).** The record's load-bearing sentences STAND ("an identity
> only if those u's are exact" — true; P(n)'s fourth member fails
> under bound-only inputs — true, the member is an equality). The
> rider: **(CS-EXACT) is required because the induction propagates
> the exact-complement IDENTITY (P's fourth member — the
> inclusion–exclusion as an equality), NOT because bounds fail to
> propagate: upper bounds propagate by monotonicity + union bound
> (R6.1), which is exactly the mechanism GENIND-C1(ii) (R1.2 above)
> uses for the vanishing-rate BOUND. The two consumers want different
> strengths; only the identity consumer needs (CS-EXACT).** This
> discharges R1.2(ii)'s "see R6" pointer.”

**CONDITIONALITY:** **The cleanest conceptual repair in the stack, and it changes nothing downstream** — (CS-EXACT) is still required, for a different and correct reason. **Its practical consequence is what makes GENIND-C2 possible:** because bounds propagate, a RATE leg can be built under (CS-1) alone, without (CS-EXACT) (`.35`, `.44`, `.51`).

**SUPERSESSION KIND:** `provenance-rider` — the *reason* is replaced; the clause and its necessity are untouched. **Conflating this with a `replacement` would imply (CS-EXACT) was withdrawn, which is the opposite of the finding.**

**TARGETS:** shard 1 `.14` (the (CS-EXACT) clause's rationale), shard 1 `.58` (Step 4's `[r1]` record), shard 1 `.25`/`.37` (the composition clauses), and `.05`(ii) here (whose “see R6” pointer this discharges).

**DERIVATION:** The separation follows from `.22`'s monotonicity + union bound (bounds propagate) and from the observation that P's fourth member is an equality (so its propagation is an identity claim).

**RESOLUTION TRACE:** statement lines 2986–2997. correction sites: none.

**TEETH:** machine leg F (`.24`).

---

### EFF.GENIND.s3of3.24  [run-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R6.3 — verification with a decorrelation record). verbatim, lines 2999–3004.

> “**R6.3 Verification.** Machine leg F (@ f5271e4, GREEN, symbolic):
> dF/du₁ = T₂ − u₂; ∂G/∂u_i = Π_{j≠i}(T_j − u_j) at r = 2, 3; the
> union-bound dominance certificates (UB − G with nonnegative
> coefficients in (u_i, T_i − u_i)). Decorrelation record: the fold's
> scaffold P-4 PREREGISTERED the same arithmetic before the run and
> its sympy leg confirmed it — two decorrelated models, same kill.”

**CONDITIONALITY:** **“two decorrelated models, same kill”** — a preregistered prediction (the fold's scaffold P-4) confirmed by an independent symbolic implementation. The strongest decorrelation record in the shard.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 2999–3004. correction sites: none.

**TEETH:** executable regression (symbolic) + **`accepted-with-decorrelation-supplied`** with an explicit preregistration.

**PIN VERIFICATION:** `f5271e4` ✓.

---

### EFF.GENIND.s3of3.25  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + paragraph (the ANNEX R close), carrying an `[ar1, MINOR-2]` enumeration. verbatim, lines 3006–3028.

> “### ANNEX R — close (2026-08-09)
>
> The S4 repair queue is EXECUTED in full: R1 (F3) @ a1525ea +
> machine leg f5271e4; R2–R6 in this append stack. Byte-freezes at
> the close: accepted body + pre-annex appends lines 1–2548 md5
> eefcf658 (re-verified at each annex commit); the R1 annex slice
> (lines 2549–2745) byte-identical to a1525ea's; the pinned artifacts
> this annex consults are exactly four — genind_checks.py e7ca150b
> (read-only at its two gate lines), genind_annexr_supp.py 42fd603e +
> its committed output d938ad82 (the additive leg), and this note's own
> bytes 1–2548 eefcf658 — each verified at its pin at this close
> [ar1 2026-08-10, MINOR-2: the sealed clause "sealed runner e7ca150b
> and every sealed artifact untouched" quantified without enumeration,
> against the note's own r5 policy; this enumeration replaces it. The
> annex's five commits — a1525ea2, 31c6723d, 98ac7bb0, fe0ed6c0
> (note-only) and f5271e4 (the supp pair) — touch no file beyond this
> note and that pair]. Grade honesty: this annex cures the six
> adjudicated findings by display riders, one erratum, and the R1
> derivations at the accepted text's own grade; the annex has NOT
> itself been through a hostile pass. The 2/2 acceptance attaches to
> the frozen body; the annex carries the ratification fold's
> CHALLENGE disposition (CODEX_GENINDRAT_2026-08-09.md S4) with the
> queue now landed.”

**CONDITIONALITY:** **“the annex has NOT itself been through a hostile pass” is a STALE-SELF-DESCRIPTION as of the r1 append** (`.31`), which runs exactly such a pass — 0C + 1 GAP + 2 MINOR — and it is **not edited**, only followed. Tagged `STALE-SELF-DESCRIPTION (uncured)` (rule 26). **“The 2/2 acceptance attaches to the frozen body”** is the sentence a chapter cut must carry with any annex-derived result.

**SUPERSESSION KIND:** the `[ar1, MINOR-2]` layer = `replacement` (a non-enumerative freeze sentence replaced by an enumeration of four artifacts + five commits, original quoted) — the r5 standing rule applied to the annex's own close.

**ARITHMETIC AUDIT (compiler-computed):** “exactly four” pinned artifacts ✓ enumerated (runner, supp py, supp output, the note's own bytes); “five commits” ✓ enumerated (`a1525ea2`, `31c6723d`, `98ac7bb0`, `fe0ed6c0`, `f5271e4`). **Both numerals reconcile with their enumerations** — unlike shard 2 `.53`'s “eight”. The R1 annex slice is cited as lines 2549–2745; the pre-annex freeze is 1–2548 ✓ contiguous, no gap ✓.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 3006–3028. correction sites: `[ar1]` in situ 3017–3022; the “no hostile pass” clause overtaken at 3098–3115 (`.31`).

**TEETH:** `arithmetic recount` (4/4 and 5/5 reconciled). **PIN VERIFICATION:** `a1525ea` ✓, `f5271e4` ✓ resolve; `31c6723d`, `98ac7bb0`, `fe0ed6c0`, `a1525ea2` are 8-hex prefixes — `a1525ea` ✓ resolves as the 7-prefix and the others are cited in the annex's own enumeration and are **not independently re-verified here** (recorded, §8 defect 2).

---

### EFF.GENIND.s3of3.26  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph (the dated supplier-movement record's owed-disclosure discharge). verbatim, lines 3032–3041.

> “### Dated supplier-movement record (2026-08-09): GENHN errata E1–E3 EXECUTED + GENHN r2 — the n ≥ 8 leg gains [GENHN-TOW-1]
>
> **Owed disclosure discharged (S16 row 6: "execution disclosure owed
> at the next dated append").** GENHN's three queued errata are
> EXECUTED: E1 @ bc1b996 (LEMMA GENHN-3(a)'s f₁ ≥ 2 band-exit clause
> conditionalized to the GENH4-r3 trichotomy), E2 @ 961d0ff
> (GENHN.A(v)'s census clause gains the comp-weighted band clause,
> Q^{comp}−1 per band pin), E3 @ 46bf675 (the stage-ring carrier at
> GENHN.A(i)/S3.1 restated in L/O_L), plus the S10 box refresh
> @ 58b1080 — all 2026-08-09, before GENHN's PE1.”

**CONDITIONALITY:** **Discharges an obligation created two shards earlier** (shard 2 `.17`, `.62` row 6) — the note's obligation-tracking working as designed. All three errata land on clauses GENIND consumes or neighbours.

**SUPERSESSION KIND:** `inventory completion` (an owed disclosure supplied).

**TARGETS:** shard 2 `.17`, shard 2 `.62` row 6.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 3032–3041. correction sites: none.

**TEETH:** `transfer audit` (the per-clause screen at `.28`). **PIN VERIFICATION:** `bc1b996` ✓, `961d0ff` ✓, `46bf675` ✓, `58b1080` ✓.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:LEMMA GENHN-3` — count **3**; `GENHN.A(v)` — count **6**; `GENHN.A(i)` — count **11**.

---

### EFF.GENIND.s3of3.27  [changes-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (the new supplier movement: GENHN r2). verbatim, lines 3043–3053.

> “**New movement: GENHN r2 (its PE1 repair round).** GENHN's PE1
> hostile pass REFUTED LEMMA GENHN-T(b); r2 landed the repair —
> @ d16869c (T(b) WITHDRAWN; **LEMMA GENHN-T(b)′ stated AND PROVED**;
> the **new box [GENHN-TOW-1]** (entry budgets, inner refine,
> faithfulness geography, partial sides, composed window); GENHN.B's
> tower clause + EXACTLY display restated honestly — **n ≤ 7 as
> sealed; n ≥ 8 adds TOW-1**), @ 7650b20 (LEMMA GENHN-1's budget
> display corrected; the node floor (μ−j)S+1 RE-DERIVED from the true
> floors, standing), @ 438608a (band transport derived at the E1
> annex; S7 stage-RAM rider; run reconciliation; arc line: 0/2 stays,
> PE2 next), @ 9636b7e (T(b)′ statement rigor parenthetical).”

**CONDITIONALITY:** **A supplier lemma was REFUTED and replaced behind a new box.** This is the strongest inbound movement in the GENIND arc: not a display correction, not a re-pin, but a withdrawn lemma. Its consequence for GENIND is `.29`.

**SUPERSESSION KIND:** none of GENIND's own text; a supplier-movement record. **The v3 enum's gap again** (§6.3).

**ARITHMETIC AUDIT:** four r2 commits enumerated ✓ (`d16869c`, `7650b20`, `438608a`, `9636b7e`), plus the four E1–E3 + box-refresh commits at `.26` = **eight commits of supplier movement** ✓ — matching `.30`'s “exactly the eight commits enumerated above” ✓.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 3043–3053. correction sites: none.

**TEETH:** foreign-note evidence (GENHN's own PE1/r2 arc). **PIN VERIFICATION:** `d16869c` ✓, `7650b20` ✓, `438608a` ✓, `9636b7e` ✓.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:LEMMA GENHN-T(b)` — count **11**; `GENHN-TOW-1` — count **19**.

---

### EFF.GENIND.s3of3.28  [changes-record]

**CANONICAL STATEMENT:** FORM: bold-headed bulleted display (the per-clause consumption screen over the seven PE7-m2 sites). verbatim, lines 3055–3074.

> “**Consumption verdicts at ledger granularity (the seven PE7-m2
> sites, screened against the 850e77e → HEAD diff this round):**
> * GENHN.A(iv), consumed at GENIND-6(b) (the stage node floor
>   S_b + 1): clause text not in the diff; its node-floor arithmetic
>   was re-derived and STANDS at 7650b20 — SURVIVES.
> * GENHN.A(v), consumed at (CS-1)/S7.1: E2 ADDS the comp-weighted
>   band census — the exact form this note's Step 4 already consumes
>   in its r2-corrected sentence ("q^{comp}−1 per RAM/2SIDED pin") —
>   alignment, SURVIVES.
> * LEMMA GENHN-3, consumed at (CS-1) + S6 Step 4 (ragged-band
>   CONFINEMENT at the discharged genres): E1 conditionalizes the
>   f₁ ≥ 2 band-EXIT phrasing; the discharged genres consumed here
>   are f₁ = 1 — SURVIVES.
> * S6.2, consumed at (CS-2): E2's tag reaches its assembly
>   sentence's census factor, the same alignment as A(v) — SURVIVES.
> * The three PE7-m2 cites (S11.F @ this note's L684; S6.3 @ L1094;
>   the GENIND-6(a) statement echo @ L623): none named by the
>   E1–E3/r2 commit set (diff-grep, this round); S6.3's display is
>   consumed here WITH the genre-F granularity caveat Step 4 already
>   carries — SURVIVE.”

**CONDITIONALITY:** **A seven-site diff-granularity screen — strictly stronger than shard 2 `.17`'s ledger-granularity check**, and it honours PE7-m2's instruction (“screen future GENHN errata against the seven sites, not four”) exactly.

**ARITHMETIC AUDIT:** the screen covers 4 clauses + 3 cites = **seven sites** ✓, matching PE7-m2's count ✓; they map to shard 1 `.35`, `.63`/`.37`, `.57`/`.63`, `.64`, `.34` (×2), `.57` ✓. Every one returns SURVIVES ✓ — **7/7**, with two distinct grounds (clause text not in the diff; the erratum aligns with the consumed form).

**DERIVATION:** Not a mathematical unit; a per-clause transfer check.

**RESOLUTION TRACE:** statement lines 3055–3074. correction sites: none.

**TEETH:** **`transfer audit`** at diff granularity — the strongest form in the corpus short of verbatim text matching, and an escalation over shard 2's ledger-granularity screen.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN.A(iv)` — count **3**; `GENHN.A(v)` — count **6**; `LEMMA GENHN-3` — count **3**; `S6.2` — count **6**; `S11.F` — count **10**; `S6.3` — count **3**.

---

### EFF.GENIND.s3of3.29  [hypothesis]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (THE CONDITIONALITY MOVEMENT — the n ≥ 8 conjunction). verbatim, lines 3076–3088.

> “**THE CONDITIONALITY MOVEMENT (this record's point).** S16 row 1's
> firing geography names GENHN.C at μ = 2 stages with n ≥ 6 =
> [GENHN-HE(μ ≥ 3)] (read per PE7-m3: the content rides inside
> [GENIND-H]'s display). After T(b)'s refutation and T(b)′'s proof,
> GENHN.B carries its tower clause at n ≥ 8 through the boxed
> [GENHN-TOW-1]. Accordingly, read THIS note's conditionality at
> n ≥ 8 as: **[GENIND-H(n)] + [GENHN-HE(μ ≥ 3)] + [GENHN-TOW-1]** —
> the n ≥ 8 leg rests on [GENHN-TOW-1] IN ADDITION TO
> [GENHN-HE(μ ≥ 3)], per GENHN.B's restated clause; at n ≤ 7 nothing
> moves (sealed grade, the same clause). No count law, theorem
> clause, consumption verdict at n ≤ 7, or frozen number of this note
> moves — the movement is conditionality bookkeeping at the open
> frontier.”

**CONDITIONALITY:** **THE most consequential single unit of this shard for the capstone DAG.** The note's headline claim — “the distance from the n = 3 theorem to the FULL uniformity theorem is exactly ONE displayed hypothesis family” (shard 1 `.04`) — is true at n ≤ 7 and **false as stated at n ≥ 8**, where the conjunction is three families. The movement is *bookkeeping* in the sense that no proof changes; it is *substantive* in the sense that the capstone's hypothesis block grows.

**SUPERSESSION KIND:** `scope-pin` — a range-indexed re-reading of the conditionality, with n ≤ 7 explicitly unmoved.

**TARGETS:** shard 1 `.15` (the GENIND.B consequence clause), and by inheritance shard 1 `.04`, `.13`, `.61`.

**DERIVATION:** Not a proof; a conditionality composition read off the supplier's restated clause.

**RESOLUTION TRACE:** statement lines 3076–3088. correction sites: none.

**TEETH:** NONE — a conditionality statement. Disposition: `signed vacuity disclosure` at n ≥ 8 (nothing in this note's evidence base reaches degree 8 except PE4's N8MIX construction and PE7/PE8's routes, none of which exercises [GENHN-TOW-1]).

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN-TOW-1` — count **19**; `GENHN.C` — count **19**.
**NEAR-MISS:** `[GENHN-HE(μ ≥ 3)]` — count **0** in GENHN; the reading is fixed by PE7-m3 (shard 2 `.71`) and this unit cites that fix explicitly (“read per PE7-m3”).

---

### EFF.GENIND.s3of3.30  [changes-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (the record's pins and byte-freeze). verbatim, lines 3090–3094.

> “**Pins (git log at THIS commit).** GENHN note HEAD = 9636b7e (arc
> 0/2, its PE2 next — a consumer flag GENHN's own S10 carries);
> supplier movement since this note's last pin 850e77e = exactly the
> eight commits enumerated above (E1–E3, 58b1080, r2 ×4). Byte-freeze
> re-verified at this commit: lines 1–2548 md5 eefcf658.”

**ARITHMETIC AUDIT:** “exactly the eight commits enumerated above (E1–E3, 58b1080, r2 ×4)” = 3 + 1 + 4 = **8** ✓ — **the numeral reconciles with its enumeration** (as at `.25`, and unlike shard 2 `.53`).

**CONDITIONALITY:** **GENHN's new HEAD is `9636b7e` with arc 0/2 and PE2 pending** — so this note's n ≥ 8 conditionality now rides a supplier at grade 0/2 whose own next hostile pass has not run. The note flags the consumer signal explicitly.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 3090–3094. correction sites: none.

**TEETH:** `arithmetic recount` (8/8) + commit-time git-log check. **PIN VERIFICATION:** `9636b7e` ✓, `850e77e` ✓.

---
### EFF.GENIND.s3of3.31  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph (ANNEX R — r1's provenance and enumerated edit scope). verbatim, lines 3098–3115.

> “## ANNEX R — r1 (2026-08-10; the ANNEX R hostile pass's repair queue)
>
> **Provenance and scope.** The annex stack's scoped hostile pass
> (`GENIND_ANNEXR_pass_report.md`, 2026-08-10) returned **UNREFUTED,
> NOT CLEAN: 0 CRITICAL + 1 GAP + 2 MINOR** — GAP-1 = the
> full-vs-simple complement seam at R1.1's closure sentence; MINOR-1 =
> R1.3's undisplayed c-choice; MINOR-2 = two non-enumerative universal
> record sentences (close + R1.4). This r1 executes all three. The
> accepted body stays byte-frozen (lines 1–2548 md5 eefcf658,
> re-verified at this commit); the ANNEX R text above is edited at
> exactly five [ar1 2026-08-10]-tagged sites — the R1.1 closure rider,
> the R1.2 u_l rider, the R1.3 c-choice, the R1.4 enumeration, the
> close enumeration — plus one rider at R1.4's CS sentence below;
> every other annex line is unchanged. Repairs are RE-DERIVED from the
> note's own lemmas (GENIND-4's budgets, S7.1/S7.3's slot geometry,
> S5.1's criterion arithmetic, S5.3's entry tables, W-11's R(M) tie,
> R6.1's monotonicity); no verifier sentence is transcribed. Annex
> stack stays 0/2.”

**CONDITIONALITY:** **The annex layer gets its own hostile pass, and the pass finds a GAP in the repair that cured the heaviest GAP** — the recursion the whole arc exhibits. “no verifier sentence is transcribed” is a provenance guarantee (the repairs are the note's own derivations, not the verifier's prose).

**ARITHMETIC AUDIT:** “exactly five … sites … plus one rider” ✓ — five enumerated (R1.1 closure `.04`, R1.2 u_l `.05`, R1.3 c-choice `.06`, R1.4 enumeration `.07`, close enumeration `.25`) **plus one at R1.4's CS sentence (`.07`'s closing rider)** = six `[ar1]` tags in the layer ✓. Compiler check: this compilation carries `[ar1]` layers at exactly `.04`, `.05`, `.06`, `.07` (×2 — the MINOR-2 enumeration and the CS rider) and `.25` ✓ — **six, matching.**

**SUPERSESSION KIND:** the layer as a whole = `replacement` at five named sites + `inventory completion` (GENIND-C2 added).

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 3098–3115. correction sites: none for this paragraph.

**TEETH:** `in-house hostile pass` (scoped to the annex stack). **PIN VERIFICATION:** `lean/notes/openmath/GENIND_ANNEXR_pass_report.md` EXISTS ✓. **Compiler note for the merge:** a second report `lean/notes/openmath/GENIND_ANNEXR_pass2_report.md` also exists on disk and **is cited nowhere in the note** — the annex stack's “pass #2”, whose result the note (frozen at 2026-08-12) does not carry. Recorded as source defect 3 (§8): the annex stack's grade line “remains 0/2 … queues for its own scoped hostile pass” (`.39`) may be stale against the repo, and this compilation does not adjudicate it.

---

### EFF.GENIND.s3of3.32  [supplier-finding]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph (r1.1's defect statement). verbatim, lines 3117–3127.

> “### r1.1 (GAP-1): ANNEX-LEMMA GENIND-C2 — the CS-drain rate
>
> **The defect, exactly.** GENIND.C′ (R1.3) proves the (A2-RATE) decay
> for the SIMPLE slice; (A2-RATE) as displayed (R1.1) pins the FULL
> complement u_{μ,d}(M). The difference — the mass that enters a CS
> event and stays conservative-undecided, the CS-STRATUM DRAIN — had
> exactness ((CS-EXACT)) but no displayed all-window rate, while
> GENIND-C1(iii)'s GROWING regime consumes the full member's rate at
> (4, d) children from n = 5 on. The entry mass alone cannot supply it:
> the CS entry loci have POSITIVE relative density (S5.2's own
> sentence), so the decay must come from inside the stage.”

**CONDITIONALITY:** **A seam between two of the same repair's own components** — C′ covers the simple slice, (A2-RATE) pins the full complement, and the CS-drain difference had no rate. **The last sentence is the sharp one: the decay cannot come from the entry mass, because the entry loci have positive relative density (shard 1 `.46`), so it must come from inside the stage** — which is what forces `.33`'s conditionality on (CS-1).

**ARITHMETIC AUDIT:** “from n = 5 on” — a (4, d) child requires a parent of degree > 4·d, first at n = 5 with d = 1 ✓; and a degree-4 system is the first that can bear CS (shard 1 `.11`) ✓, so the first CS-bearing child appears at n = 5 ✓. The positive-density claim is shard 1 `.46`'s, audited there (`Σ_h (q−1)q^{−5h−3}` is N-independent ✓).

**DERIVATION:** Not a mathematical unit; a defect report.

**RESOLUTION TRACE:** statement lines 3117–3127. correction sites: none.

**TEETH:** `in-house hostile pass` (the annex's own scoped pass).

---

### EFF.GENIND.s3of3.33  [lemma]

**CANONICAL STATEMENT:** FORM: display (blockquote, ANNEX-LEMMA GENIND-C2 as first stated at r1.1). verbatim, lines 3129–3182. **This statement is SUPERSEDED IN FULL by the 2026-08-12 R9 replacement (`.42`) and then partly by R11 (`.51`); it is emitted because it is the version the r1 machine leg (`.38`) was preregistered and run against.**

> “> **ANNEX-LEMMA GENIND-C2 (the CS-drain rate; conditional on (CS-1)
> > only).** Fix (m, d) with m·d ≥ 4, window N, and a CS genre of the
> > S5.2 recursion's inventory: entry-height datum with v(a₀) = H on
> > the opening locus (the DRAIN-first key height; visibility floor
> > H ≤ N−1, R4's species), stage data (μ, e, ψ, E = e, K,
> > |K| = q^{d·deg ψ}) per S7.1. Assume, of [GENIND-H]'s clauses,
> > **(CS-1) only** — the stage count isomorphism with its slot
> > geometry (one K-digit per (abscissa, v′-height), E slots per
> > v-unit: COROLLARY W-9/JC-F1's dim_K 𝒜(T) = E; ragged-corrected
> > below the uniform threshold). Then the genre's conservative-drain
> > contribution to u_{m,d}(N) obeys the (A2-RATE) species. Precisely:
> >
> > (i) [stage window supply] the stage read is a (μ, K)-cluster read
> > at stage window M★ ≥ E·(N−1−H): every consulted slot string runs
> > from its node height (deepest = E·H) to the uniform boundary
> > E·(N−1) in v′-units; the visibility floor H ≤ N−1 is exactly
> > M★ ≥ 0. Instances: the (2,2)-E stage — GENIND-4's node
> > C(4h+1, 2h+1) in dv-units against S7.3's uniform boundary 2N−2,
> > H = 2h, so M★ = 2N−2−4h (the stage-α(2h) transported window, the
> > W-11 shape); genre F — H = 4k, v′ = v, M★ = N−1−4k over K = F_{q²}.
> >
> > (ii) [stage drain rate] at μ ≤ 3 the stage read is CS-FREE (S5.1's
> > criterion AT the stage: CS needs ≥ 4 keys and the stage has μ), so
> > GENIND.C′ applies to the whole stage complement: stage-drain
> > fraction ≤ K★·M★^{B★}·|K|^{−(M★−c★)}. At μ ≥ 4 (first possible at
> > m ≥ e·μ·deg ψ ≥ 8) recurse this lemma jointly with C′: the stage's
> > product-degree μ·(d·deg ψ) ≤ m·d (S5.1's side-length arithmetic
> > m ≥ e·μ·deg ψ) and its window M★ < N — CS legs enter GENIND.C′'s
> > lexicographic (degree, window) induction exactly as α-legs do.
> >
> > (iii) [composition at slope ≥ 2] drain contribution ≤ (entry
> > relative mass ρ) × (stage drain fraction): decided split-off pieces
> > contribute no drain, and at MIXED genres (stage + β-children
> > coexisting, first at n = 6) the frame drain composes by
> > GENIND-6(d)'s inclusion–exclusion, bounded by the union bound as in
> > GENIND-C1(ii) — bounds propagate by R6.2's separation, no
> > (CS-EXACT) needed. In original q-units,
> > |K|^{−(M★−c★)} ≤ q^{−(e·d·deg ψ)·(N−1−H)+O(1)} with
> > **e·deg ψ ≥ 2 — the CS-DEFINING inequality (S5.1's necessity
> > arithmetic)**: a composite stage certifies at least TWO q-digits
> > per remaining window unit. The entry mass ρ decays geometrically in
> > H (the entry laws are order-1 W-12.A-priced shapes: S5.3's tables
> > at n = 4, 5; S5.2's exactly-known entry mass at general n), so the
> > height sum converges and the genre count is ≤ p̃(m)·N^m
> > (GENIND-C1(iv)'s species). Summing:
> >
> >     CS-drain part of u_{m,d}(N)/Q^{m(N−1)} ≤ K_c·N^{B_c}·q^{−(N−c_c)},
> >
> > with window-deficit slope ≥ 2 where the stage window is live and
> > ≥ 5/2 from the entry mass alone at floor-adjacent strata (E:
> > ρ = (q−1)q^{1−5h} at 2h ≥ N−2; F: (q(q−1)/2)q^{−10k} at
> > 4k ≥ N−2) — the crossover is the visibility floor. In particular
> > an n = 4 CS drain at window-deficit slope < 1 is excluded twice
> > over. ∎”

**CONDITIONALITY:** **SUPERSEDED IN FULL.** Two defects were found later and both are real:
1. **The d-factor defect (R9, `.41`):** “the preceding stage calculation retained \(d\), but the conclusion changed from \(Q=q^d\) to \(q\)” — visible in the displayed conclusion `≤ K_c·N^{B_c}·q^{−(N−c_c)}` against the normalization `Q^{m(N−1)}`.
2. **The stage-window scalar bound (R11, `.49`):** `M★ ≥ e(N−1−H)` is **WITHDRAWN for general embedded and mixed genres**, because (CS-1) supplies ragged per-coordinate windows and permits sibling-Hensel losses without pricing them.
Also withdrawn implicitly: (ii)'s equal-product-degree descent sentence “its window M★ < N”, replaced by a truncation argument (`.55`).

**SUPERSESSION KIND:** received `replacement` (R9, full) then `replacement` again at three named parts (R11).

**CHAIN:** **this statement → R9's Q-normalized GENIND-C2 (`.42`) → R11's C2Q under (CS-1Q) (`.51`) — TERMINAL.** A chapter cut must NOT read this version; it survives only as the object the r1 machine leg was run against.

**ARITHMETIC AUDIT (compiler-computed, on the defect R9 names):** the normalization is `u/Q^{m(N−1)}` with `Q = q^d`; (ii)'s stage estimate is in `|K| = q^{d·deg ψ}` and (iii) converts it to `q^{−(e·d·deg ψ)(N−1−H)}`, retaining d ✓ — **but the displayed conclusion writes `q^{−(N−c_c)}`, base q, against a `Q^{m(N−1)}` denominator.** At `d ≥ 2` the two disagree by a factor `q^{(d−1)(N−c_c)}` ✓ — **the d-factor defect is real and exactly as R9 describes.** The instance displays (E: `M★ = 2N−2−4h` with `H = 2h`, so `E(N−1−H) = 2(N−1−2h) = 2N−2−4h` ✓; F: `M★ = N−1−4k` with `E = 1, H = 4k` ✓) are consistent with the withdrawn scalar bound at `d = 1` ✓.

**DERIVATION:** Displayed. Superseded; the live derivations are `.42` and `.51`.

**RESOLUTION TRACE:** statement lines 3129–3182. correction sites: 3298–3317 and 3319–3557 (R9, `.41`/`.42`); 3592–3721 (R11, `.49`–`.53`).

**TEETH:** the r1 machine leg (`.36`, `.38`) — **preregistered and run against THIS version**, which is why the version is emitted rather than dropped.

XREF: `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md:COROLLARY W-9` — count **2**; `JC-F1` — count **18**; `dim_K 𝒜(T) = E` — count **3**.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:THEOREM W-12.A` — count **8**.

---

### EFF.GENIND.s3of3.34  [instance-record]

**CANONICAL STATEMENT:** FORM: bold-headed bulleted display (r1.1's displayed instances at n = 4, 5). verbatim, lines 3184–3195.

> “**Displayed instances (n = 4, 5 — the degrees C1 first consumes).**
> * CS4-E(h): ρ = (q−1)q^{1−5h}, M★ = 2N−2−4h, |K| = q: composed
>   contribution ≤ poly(N)·q^{−(2N+h)+O(1)} — h-sum geometric.
> * CS4-F(k): ρ = (q(q−1)/2)·q^{−10k}, M★ = N−1−4k, |K| = q²: composed
>   ≤ poly(N)·q^{−(2N+2k)+O(1)}.
> * CS5-V1E2(h): entry_rel = (q−1)q^{2−(15h+1)/2}·(1−q^{−(N−(5h+1)/2)})
>   — constant-order in N (the S5.2 positive-density display; the
>   fifth root's headroom fiber is a DECIDED piece) — times the same
>   (2,2)-E stage at M★ = 2N−2−4h: composed ≤ poly(N)·q^{−2N+O(h)};
>   the N-decay comes entirely from inside the stage. CS5-V4E2 and the
>   S5.3 siblings: same composition species (entry geometric in its
>   height data × a (2,2)-type stage), displayed by the table.”

**CONDITIONALITY:** Superseded by R9's corrected checks (`.43`), which re-display the same three instances in `Q`-units. **The exponents are unchanged at d = 1**, which R9's own audit confirms.

**ARITHMETIC AUDIT (compiler-computed):**
* CS4-E: `ρ` = law/total = `(q−1)q^{4N−5h−3}/q^{4(N−1)} = (q−1)q^{1−5h}` ✓. Composed: `ρ·q^{−|K|-exponent}` with `|K| = q` and `M★ = 2N−2−4h` gives `q^{1−5h}·q^{−(2N−2−4h)} = q^{−2N+3−h}` ✓ = `q^{−(2N+h)+O(1)}` ✓.
* CS4-F: `ρ = (q(q−1)/2)q^{4N−10k−4}/q^{4N−4} = (q(q−1)/2)q^{−10k}` ✓. Composed with `|K| = q²`, `M★ = N−1−4k`: `q^{−10k}·q^{−2(N−1−4k)} = q^{−2N+2−2k}` ✓ = `q^{−(2N+2k)+O(1)}` ✓.
* CS5-V1E2: entry_rel = law/total = `(q−1)q^{4N−5h−3}(q^{N−(5h+1)/2}−1)/q^{5(N−1)}` = `(q−1)q^{−N−5h+2}(q^{N−(5h+1)/2}−1)` = `(q−1)q^{2−5h−(5h+1)/2}(1 − q^{−(N−(5h+1)/2)})` = `(q−1)q^{2−(15h+1)/2}(1−q^{−(N−(5h+1)/2)})` ✓ **exactly the displayed form** (since `5h + (5h+1)/2 = (15h+1)/2` ✓). Composed: constant-order × `q^{−(2N−2−4h)}` = `q^{−2N+O(h)}` ✓.
**All three displayed compositions re-derive exactly.**

**DERIVATION:** Instantiation of `.33`.

**RESOLUTION TRACE:** statement lines 3184–3195. correction sites: 3508–3541 (R9's corrected checks, `.43`).

**TEETH:** the r1 machine leg's P1–P4 (`.38`).

---

### EFF.GENIND.s3of3.35  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (r1.1's conditionality). verbatim, lines 3197–3208.

> “**Conditionality, honestly.** GENIND-C2 consumes (CS-1) ONLY — not
> (CS-2), not (CS-3), not (CS-EXACT). At n = 4,
> (CS-1) is de facto discharged (GENH4 @ r3 4b0d946 per Step 4's [r3]
> record: GENIND-4 + GENH4-1F + GENH4-2/-3/-4), so u_{4,d}'s FULL
> (A2-RATE) — the member C1(iii) consumes at n = 5 — rides pinned
> theorems. At n ≥ 5 the CS-drain leg is conditional on (CS-1) ⊂
> [GENIND-H(n)], the box GENIND.B's reduction ALREADY assumes: the
> closure sentence "P(k)-with-(A2-RATE) closes under GENIND.B's strong
> induction" now holds at the theorem's own conditionality, with no
> new hypothesis. Rider on R1.4's last sentence: the CS legs keep
> [GENIND-H]/(CS-EXACT) for menu + exactness; their RATE is GENIND-C2
> under (CS-1) alone.”

**CONDITIONALITY:** **“with no new hypothesis” is the claim R11 later overturns.** The R11 certification-status paragraph (`.52`) replaces “(CS-1) only” with “(CS-1Q), verified per genre” and states that the displayed (CS-1) does **not** establish (CS-1Q.b) for embedded or mixed genres — **so the closure DOES rest on more than the box GENIND.B already assumes, at those genres.** This is the single most important supersession in the shard.

**SUPERSESSION KIND:** received `replacement` (of the conditionality label) — audited at `.52`.

**CHAIN:** “(CS-1) ONLY … with no new hypothesis” → **R11: “(CS-1Q), verified per genre”; “A universal discharge for embedded and mixed genres remains obstructed” — TERMINAL.**

**TARGETS:** shard 1 `.13`, `.37`, `.57`, `.63`; `.04`, `.05` here.

**DERIVATION:** Not a mathematical unit; a conditionality declaration.

**RESOLUTION TRACE:** statement lines 3197–3208. correction sites: 3712 and 3714–3721 (`.52`, `.53`).

**TEETH:** the n = 4 de facto discharge is a citation (shard 1 `.59`, `.66`), riding GENH4's accepted body; the n ≥ 5 leg is `signed vacuity disclosure`.

XREF: `lean/notes/openmath/GENH4_PROOF_2026-08-08.md:GENH4-1F` — count **10**; `GENH4-2` — count **15**.

---

### EFF.GENIND.s3of3.36  [preregistration]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (r1.1's two-commit machine seal, PENDING — a preregistration with teeth and a roster). verbatim, lines 3210–3226.

> “**Machine leg (two-commit seal; PENDING at this commit).**
> `verification/openmath/genind_annexr1_checks.py`, sealed UNRUN with
> preregistered checks P1 (per-stratum window bound
> UND ≤ entry·M★·|K|^{−(M★−1)} at 10 scored fresh rows), P2 (species
> bound at (K,B,c) = (1,1,2) per swept (q,N)), P3 (slope: consecutive-N
> relative-drain ratio ≤ q^{−3/2} — kills slope ≤ 1; expected ≈ q^{−3}),
> P4 (the CS5-V1E2 entry identity + composed n = 5 bound, sympy + grid
> to N = 40), P5 (C1(iii)'s D+M = N composition identity, sympy), and
> teeth T-SLOPE (a fabricated slope-1/2 n = 4 drain — the pass report's
> failure scenario made flesh — must violate P1) and T-WIN (a
> mis-derived stage window 2N−2−2h must be refuted by the committed
> deep row (Zp, 2, 11, h = 5) of the GENH4 battery). Fresh rows are
> walked by the PINNED GENH4 sealed walker (read-only; its own per-row
> checks stay live and must stay silent), roster E: q=2 h=1 N=4..7,
> q=2 h=3 N=8..9, q=3 h=1 N=4..5; F: q=2 k=1 N=7..9, q=3 k=1 N=6
> (schedule: floor-adjacent, P2 only). Verdict from committed artifacts at
> commit 2.”

*(Compiler note: the parenthetical at the last roster entry reads “(floor-adjacent, P2 only)” in the source; the word “schedule:” is NOT in the source and is a transcription slip in this quotation — **corrected here**: the source reads “q=3 k=1 N=6 (floor-adjacent, P2 only)”. Flagged rather than silently fixed, per the fidelity rules.)*

**CONDITIONALITY:** **A genuine two-commit preregistration with two armed teeth**, one of which (“T-SLOPE — the pass report's failure scenario made flesh”) instantiates the verifier's own worry as a mutant. **“P1 … at 10 scored fresh rows” is corrected to 11 by R9's riding MINOR-A** (`.45`).

**ARITHMETIC AUDIT (compiler-computed):** roster E rows: (2, h=1, N=4..7) = 4 + (2, h=3, N=8..9) = 2 + (3, h=1, N=4..5) = 2 → **8**; roster F rows: (2, k=1, N=7..9) = 3 + (3, k=1, N=6) = 1 → **4**; total **12 fresh rows** ✓ — matching `.38`'s “the 12th, F q=3 N=6, is floor-adjacent M★ = 1: disclosed, not scored” and hence **11 scored** ✓, which is MINOR-A's correction. **The preregistered “10” is wrong against the note's own roster arithmetic** ✓ — MINOR-A is right.
Check the floor-adjacency: at `(q, k, N) = (3, 1, 6)`, `M★ = N−1−4k = 6−1−4 = 1` ✓ floor-adjacent.
T-WIN's control row `(Zp, 2, 11, h = 5)`: the correct window is `M★ = 2N−2−4h = 22−2−20 = 0`… **recomputed: `2·11 − 2 − 4·5 = 0`**, while the mis-derived `2N−2−2h = 22−2−10 = 10`. So the tooth contrasts a true window of 0 against a wrong window of 10 ✓ — and `.38` reports the tooth firing with “UND 32,768 vs wrong-window bound 1,280” ✓, consistent with a wrong window that is far too generous.

**DERIVATION:** Not a mathematical unit; a preregistration.

**RESOLUTION TRACE:** statement lines 3210–3226. correction sites: 3561 (R9's riding MINOR-A, `.45`).

**TEETH:** this unit IS the tooth specification; `.38` is its scoring. **PIN VERIFICATION:** `verification/openmath/genind_annexr1_checks.py` EXISTS ✓, with `_output.txt` ✓ and `_results.json` ✓.

---

### EFF.GENIND.s3of3.37  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + paragraph (r1.2 and r1.3, executed inline). verbatim, lines 3228–3235.

> “### r1.2 (MINOR-1) and r1.3 (MINOR-2): executed inline
>
> MINOR-1: the c-choice c := c′ + 1 displayed at source in R1.3 (the
> β-leg exponent absorbed exactly; head leg at c ≥ 1; no circularity —
> c′ is degree-induction data). MINOR-2: both record sentences
> rewritten enumeratively at their sites (R1.4: the five consulted
> displays named; close: the four consulted pins + the five annex
> commits named). No further annex sentence was touched in r1.2/r1.3.”

**CONDITIONALITY:** Both executed; both audited at their sites (`.06`, `.07`, `.25`). The closing sentence is an enumerative scope claim (rule-compliant).

**ARITHMETIC AUDIT:** “the five consulted displays” ✓ (`.07`), “the four consulted pins + the five annex commits” ✓ (`.25`) — **all three numerals reconcile with their enumerations.**

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 3228–3235. correction sites: 3563 (MINOR-B later replaces R1.4's five-display census, `.46`).

**TEETH:** `arithmetic recount`.

---

### EFF.GENIND.s3of3.38  [run-record]

**CANONICAL STATEMENT:** FORM: bold-headed bulleted display (r1's machine record at commit 2, including one FLAGGED line and a RED exit). verbatim, lines 3237–3283.

> “**Machine record (2026-08-10, commit 2 — FROM the committed artifacts
> `genind_annexr1_output.txt` / `genind_annexr1_results.json`; single
> run, no check edited after any output was seen).**
> * Pins: genh4_checks.py ee8024b7 (the sealed GENH4 battery walker,
>   imported read-only; its own per-row law checks — GH-FRESH
>   volume/law ties, GH-UND, GH-BRACKET — ran live at all 12 fresh rows
>   and flagged nothing at any of the 12); genh4_checks_results.json
>   cbcff562; genind_checks.py e7ca150b. 144 preregistered checks
>   (PIN 4 + P1 11 + P2 9 + P3 7 + P4 112 + P5 1): 143 GREEN, 1
>   flagged (adjudicated below); both teeth FIRED.
> * **P1 GREEN 11/0** — the window bound UND ≤ entry·M★·|K|^{−(M★−1)}
>   at all 11 scored fresh rows (the 12th, F q=3 N=6, is
>   floor-adjacent M★ = 1: disclosed, not scored).
> * **P2 GREEN 9/0** — the species bound at (K,B,c) = (1,1,2) at every
>   swept (q,N); margins 10²–10⁴.
> * **P3 6-of-7 + the headline numbers** — genre E's measured
>   window-deficit slope is EXACTLY 2.00 at every consecutive pair:
>   q=2 h=1, UND_rel 2^{−7} → 2^{−9} → 2^{−11} → 2^{−13} at
>   N = 4→5→6→7; q=2 h=3 at 8→9; q=3 h=1 ratio 3^{−2} at 4→5 — the
>   lemma's slope-≥2 claim measured on the nose, slope < 1 excluded
>   with a full q^{±1} margin at 5 of the 7 pairs and q^{±1/2} at the
>   flagged one. **The 1 flagged line (F q=2 k=1, N 7→8: ratio 0.5 =
>   single-step slope 1.00 > the preregistered cap q^{−3/2}) is an
>   INSTRUMENT CAP LITERAL, adjudicated NOT a counter-instance:** the
>   odd→even step is exactly where GENH4.B's committed TWO-term even-N
>   display lands (the CAP(F) boundary band (q−1)q^{N+2k−1} — the same
>   granularity the box's (CS-EXACT) [r2, PE2-m1] correction names).
>   The run's own next step measures slope 3.00 (8→9: ratio 0.125);
>   the parity-PAIRED run data give UND_rel 2^{−15} → 2^{−19} over
>   N = 7→9, i.e. slope 2.00 per step; and the committed und_F law
>   closes it by hand (decorrelated leg): the main term
>   q^{2⌊N/2⌋+2k−1} steps by q²·q⁰ on alternating parities and the
>   even-N extra term is q^{−3N+12k+3+N mod 2} in relative mass —
>   per-stratum paired slope 3.00. The preregistered SINGLE-step cap
>   was miscalibrated for genre F's parity band; no BOUND check
>   (P1/P2) fails at any of the 12 rows. The instrument's own strict
>   gate therefore printed RED (1 violation, script exit 1); artifacts
>   kept byte-frozen as run, per the run-1-RED precedent.
> * **P4 GREEN 112/0** — the CS5-V1E2 entry identity (sympy) + the
>   composed n = 5 drain bound on the grid q ∈ {2,3,7}, N ≤ 40.
> * **P5 GREEN 1/0** — C1(iii)'s D + M = N exponent composition
>   (sympy).
> * **Both teeth FIRED**: T-SLOPE — the pass report's failure scenario
>   made flesh, a fabricated slope-1/2 n = 4 E-drain (262,144) violates
>   the P1 bound (65,536) at (2,7,1); T-WIN — the mis-derived window
>   2N−2−2h is refuted by the committed deep row (Zp,2,11,h=5):
>   UND 32,768 vs wrong-window bound 1,280.”

**CONDITIONALITY:** **A RED run kept and disclosed rather than re-run** — “the instrument's own strict gate therefore printed RED (1 violation, script exit 1); artifacts kept byte-frozen as run, per the run-1-RED precedent”. **The adjudication is that the CAP was miscalibrated, not that the lemma failed**, and it is supported three ways (the next step's slope 3.00; the parity-paired slope 2.00; a by-hand decorrelated derivation from the committed und_F law). **This is the honest handling of a failed preregistered check and should be read as such: the note did not move the goalposts silently — it printed RED, kept the artifact, and argued the adjudication in the open.**

**ARITHMETIC AUDIT (compiler-computed; every displayed number checked):**
* **Check tally:** `PIN 4 + P1 11 + P2 9 + P3 7 + P4 112 + P5 1 = 144` ✓ **exact**; `143 GREEN + 1 flagged = 144` ✓.
* **P3 genre-E slopes:** `2^{−7} → 2^{−9} → 2^{−11} → 2^{−13}` — each step a factor `2^{−2}` ✓ = slope 2.00 per window ✓ at q = 2, h = 1, N = 4→7 (three steps, four values ✓). At q = 3: ratio `3^{−2}` ✓ = slope 2.00 ✓.
* **The flagged F line:** ratio 0.5 = `2^{−1}` = single-step slope 1.00 ✓ > the cap `q^{−3/2} = 2^{−1.5}` ✓ (0.5 > 0.354) — **the check genuinely fails as preregistered.**
* **The adjudication's arithmetic:** the next step's ratio 0.125 = `2^{−3}` = slope 3.00 ✓; the paired data `2^{−15} → 2^{−19}` over two windows = `2^{−4}` = **slope 2.00 per step** ✓; **so the two-window average is 2.00 and the parity oscillation is (1.00, 3.00)** ✓ — arithmetically consistent, and the mean is exactly the lemma's claimed slope ≥ 2 ✓.
* **T-SLOPE:** `262,144 = 2^{18}` against the P1 bound `65,536 = 2^{16}` ✓ — a factor 4 violation ✓, the mutant fires ✓.
* **T-WIN:** `UND 32,768 = 2^{15}` against the wrong-window bound `1,280` ✓ — the wrong window under-bounds by a factor 25.6 ✓, so the tooth fires ✓.
* **Roster:** 12 fresh rows ✓ (audited at `.36`); 11 scored + 1 disclosed ✓.
* **Compiler observation on the flagged line's adjudication.** The three supports are: (a) the next step measures 3.00; (b) the paired data give 2.00/step; (c) a by-hand derivation from the committed und_F law gives per-stratum paired slope 3.00. **(b) and (c) do not agree with each other** — (b) says 2.00 per step over the pair, (c) says “per-stratum paired slope 3.00”. Both may be true of different quantities (a run-level relative mass versus a per-stratum law), but **the note does not reconcile them**, and the compiler cannot from the displayed data. **Recorded as a disclosed non-reconciliation (§8, defect 4), NOT as an error** — no BOUND check fails at any row, which is the load-bearing fact.

**DERIVATION:** Not a mathematical unit; an executed instrument's result.

**RESOLUTION TRACE:** statement lines 3237–3283. correction sites: 3561 (MINOR-A corrects the preregistration's “10 scored rows” to 11, `.45`).

**TEETH:** two planted mutants, both fired; five preregistered checks, four fully GREEN and one flagged with an open adjudication. Disposition: **executable regression with a `disclosed non-repair`** (the miscalibrated cap is not re-preregistered) and an `accepted-with-decorrelation-supplied` for the adjudication's by-hand leg.

**PIN VERIFICATION:** the three artifacts EXIST ✓; the GENH4 walker `verification/openmath/genh4_checks.py` — **verified to EXIST ✓** (md5 pins `ee8024b7`, `cbcff562` are the note's values, not re-computed here).

---

### EFF.GENIND.s3of3.39  [changes-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (r1's grade line). verbatim, lines 3285–3294.

> “**r1 grade line.** GAP-1's PROVE-FIRST charge LANDED: the CS-drain
> rate is DERIVED (GENIND-C2, conditional on (CS-1) only — within the
> box the closure sentence's theorem already assumes, de facto at
> n = 4), not re-scoped; the n = 4 machine instances measure the
> derived slope-2 mechanism exactly, and the failure scenario (an
> n = 4 CS drain at window-deficit slope < 1) is excluded by P1 at 11
> scored rows, by the measured slopes at 7 ratio pairs, and by the
> fired T-SLOPE tooth. MINOR-1 and MINOR-2 executed inline. The annex
> stack remains 0/2 — this r1 answers the ANNEX R pass and queues for
> its own scoped hostile pass behind the chain notes.”

**CONDITIONALITY:** **“conditional on (CS-1) only” is superseded by R11** (`.52`), so this grade line's central claim is **STALE (uncured)** — the CS-drain rate is now conditional on (CS-1Q), verified per genre, and “A universal discharge for embedded and mixed genres remains obstructed”. The line is not edited. Tagged `STALE-SELF-DESCRIPTION (uncured)` (rule 26). **“The annex stack remains 0/2”** is the grade a chapter cut must carry for everything in this shard.

**ARITHMETIC AUDIT:** “P1 at 11 scored rows” ✓, “7 ratio pairs” ✓ (P3's count), “the fired T-SLOPE tooth” ✓ — all three consistent with `.38`.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 3285–3294. correction sites: none in place; overtaken at 3712 (`.52`).

**TEETH:** as `.38`.

---
### EFF.GENIND.s3of3.40  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + paragraph (the 2026-08-12 R9 correction's provenance). verbatim, lines 3298–3306.

> “### Dated corrections (2026-08-12 — sol certification R9: the annex-pass d-factor GAP repaired at HEAD)
>
> The sol-5.6 annex read (runs/residues/R1_drainn4_output.log,
> 2026-08-12) found the d-factor GAP in ANNEX-LEMMA GENIND-C2 plus
> three riding MINORs. The R9 certification run (gpt-5.6-sol high,
> runs/cert/R9_drain_repair_output.log) re-adjudicated all four
> against HEAD (all REAL) and derived the repairs — the dated
> replacement passage and three riding folds below. Everything above
> this heading is byte-untouched by this append.”

**CONDITIONALITY:** **A second decorrelated-model channel** (the sol certification campaign) finding a real defect in a repair that had already survived a scoped hostile pass. **All four findings re-adjudicated REAL against HEAD.**

**DERIVATION:** Not a mathematical unit; a provenance record.

**RESOLUTION TRACE:** statement lines 3298–3306. correction sites: none.

**TEETH:** **`decorrelated-model audit`.** **PIN VERIFICATION:** `runs/residues/R1_drainn4_output.log` — **EXISTS ✓** (the directory `runs/residues/` is present in the working tree); `runs/cert/R9_drain_repair_output.log` — **EXISTS ✓**. Both are run logs, not commits.

---

### EFF.GENIND.s3of3.41  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph (the R9 replacement's supersession declaration and defect statement). verbatim, lines 3308–3317.

> “### Dated correction (2026-08-12): ANNEX-LEMMA GENIND-C2 — the residue-degree factor retained through the height sum
>
> **Supersession and scope.** This passage supersedes r1.1's
> ANNEX-LEMMA GENIND-C2 statement, proof, displayed instances, and
> conditionality paragraph. The defect was confined to the last
> normalization and height summation: the preceding stage calculation
> retained \(d\), but the conclusion changed from \(Q=q^d\) to \(q\).
> The repair below keeps \(Q\) from entry pricing through the final
> sum. No accepted theorem statement is weakened; no count law or
> frozen number moves.”

**CONDITIONALITY:** **A full-statement supersession with a precisely localized defect** — “confined to the last normalization and height summation”. The scope claim (“No accepted theorem statement is weakened”) is true: GENIND-C2 is annex material, not accepted-body material.

**SUPERSESSION KIND:** `replacement` — statement, proof, instances and conditionality, all four, of `.33`/`.34`/`.35`.

**TARGETS:** `s3of3.33`, `.34`, `.35`.

**ARITHMETIC AUDIT:** the defect as described is exactly what the compiler independently found at `.33` (the conclusion displays base q against a `Q^{m(N−1)}` denominator, disagreeing by `q^{(d−1)(N−c_c)}` at `d ≥ 2`) ✓ — **the localization is right and the compiler's independent recount agrees with the finding.**

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 3308–3317. correction sites: 3592–3721 (R11's partial re-supersession, `.49`).

**TEETH:** `decorrelated-model audit`.

---

### EFF.GENIND.s3of3.42  [lemma]

**CANONICAL STATEMENT:** FORM: **display (blockquote) with LaTeX tagged equations** — the R9-replaced ANNEX-LEMMA GENIND-C2 (Q-normalized), statement and proof. verbatim, lines 3319–3506. Quoted in full below with its `\tag{}` anchors intact (rule: the tags are the addressable objects a chapter cut needs).

> “> **ANNEX-LEMMA GENIND-C2 (the CS-drain rate, \(Q\)-normalized;
> > conditional on the (CS-1) clause family only).** Fix a cluster
> > system \((m,d,N)\), put \(Q:=q^d\), and fix a composite block in a
> > CS genre. Write
> >
> > \[
> >   \gamma:=\deg\psi,\qquad a:=e\gamma,\qquad
> >   L:=e\mu\gamma,\qquad |K|=q^{d\gamma}=Q^\gamma .
> > \]
> >
> > Thus \(a\ge2\), \(\mu\ge2\), and
> >
> > \[
> >   L\ge2a,\qquad
> >   b:=\frac{L+1}{2}\ge a+\frac12.                 \tag{C2.0}
> > \]
> >
> > Let \(H\) be the vertical drop of the side carrying the composite
> > block. On a full side \(H=v(a_0)\); at an embedded side the other
> > sides and split-off pieces impose additional conditions and can
> > only decrease the relative entry mass. Assume (CS-1) for this
> > stage and, recursively, for any composite stages occurring inside
> > it. Then the contribution in which this stage remains
> > conservative-undecided satisfies
> >
> > \[
> >   \frac{u^{\mathrm{CS}}_{m,d}(N)}
> >        {Q^{m(N-1)}}
> >       \le K_c N^{B_c}Q^{-(N-c_c)}
> > \]
> >
> > for constants \(K_c,B_c,c_c\) depending only on the fixed
> > degree/genre data.
> >
> > **Proof.**
> >
> > **(i) Stage-window supply in \(Q\)-units.** By (CS-1), the stage is
> > a \((\mu,K)\)-cluster read at a ragged-corrected stage window
> > \(M^\star\) satisfying \(M^\star\ge e(N-1-H)\). This is S7.1's
> > slot geometry: one \(K\)-digit per \(v'\)-height, \(E=e\) such
> > heights per old valuation unit. At the quartic e-first stage, for
> > example, \(M^\star=2N-2-4h=2(N-1-H)\) with \(H=2h\).
> >
> > **(ii) Stage-drain rate.** If \(\mu\le3\), the stage is CS-free by
> > S5.1, so GENIND.C′ applied over \(K\) gives
> > \(\delta_{\mathrm{stage}}(M^\star)\le K_\star(M^\star)^{B_\star}|K|^{-(M^\star-c_\star)}\).
> > If \(\mu\ge4\), use the same estimate by joint lexicographic
> > induction with GENIND.C′ and this lemma. Indeed \(\mu d\gamma\le md\)
> > follows from \(m\ge e\mu\gamma\); when equality of product degrees
> > is possible (\(e=1\)), the visible opening has \(H>0\), hence
> > \(M^\star<N\). Thus either degree or window strictly decreases.
> > In terms of \(Q\), part (i) gives
> > \(\delta_{\mathrm{stage}}(M^\star)\le K_\star N^{B_\star}(Q^\gamma)^{-(M^\star-c_\star)}
> > \le K_\star N^{B_\star}Q^{-e\gamma(N-1-H)+\gamma c_\star}
> > =K_\star N^{B_\star}Q^{-a(N-1-H)+\gamma c_\star}\). \tag{C2.1}
> >
> > **(iii) Entry pricing and the missing height comparison.** S2.2's
> > slot count supplies, for fixed side/partition data,
> > \(\rho_H\le Q^{-bH+C_0}\), \(b=\frac{L+1}{2}\) \tag{C2.2},
> > with \(C_0=O_m(1)\). Indeed, relative to the right endpoint, the
> > supporting line forces the \(L\) coefficient valuations at heights
> > \(\frac{H}{L},\frac{2H}{L},\ldots,\frac{LH}{L}\); their sum is
> > \(\sum_{r=1}^{L}\frac{rH}{L}=\frac{L+1}{2}H=bH\).
> > Passing to lattice ceilings and remembering that the level-zero
> > digits are already pinned changes this by only \(O_m(1)\) slots;
> > the residual-factor and letter census contributes only another
> > \(Q^{O_m(1)}\). Extra sides, vertices, and decided pieces add
> > constraints, so ignoring them is a valid upper bound.
> >
> > Combining (C2.1) and (C2.2), the normalized contribution at height
> > \(H\), while the stage-window estimate is live, is
> > \(\rho_H\,\delta_{\mathrm{stage}}(M^\star)
> > \le K_1N^{B_\star}Q^{-bH-a(N-1-H)+C_1}
> > =K_1N^{B_\star}Q^{-a(N-1)-(b-a)H+C_1}
> > \le K_1N^{B_\star}Q^{-a(N-1)-H/2+C_1}\), \tag{C2.3}
> > where the last inequality is exactly (C2.0):
> > \(b-a=\frac{L+1}{2}-e\deg\psi\ge\frac12\).
> > Thus the stage factor's growth with \(H\) is strictly dominated by
> > the entry-price decay; entry decay alone was not the reason the
> > height sum converges.
> >
> > **(iv) Height summation, retaining \(Q=q^d\).** Summing (C2.3)
> > gives \(\sum_H \rho_H\,\delta_{\mathrm{stage}}(M^\star)
> > \le K_1N^{B_\star}Q^{-a(N-1)+C_1}\sum_{H\ge0}Q^{-H/2}
> > \le K_2N^{B_\star}Q^{-a(N-1)+C_1}\) \tag{C2.4},
> > because \(Q\ge2\) and \(\sum_{H\ge0}Q^{-H/2}\le(1-2^{-1/2})^{-1}\).
> > Since \(a=e\deg\psi\ge2\), the right side is
> > \(\le K_2N^{B_\star}Q^{-(N-c_2)}\) for an \(N\)-independent \(c_2\).
> >
> > For the floor-adjacent range in which the quantitative stage
> > estimate is not invoked, fix its finite threshold \(M_0\).
> > From \(M^\star\ge e(N-1-H)\) and \(M^\star<M_0\) one gets
> > \(H>N-1-\frac{M_0}{e}\). The trivial stage-drain bound \(1\),
> > together with (C2.2), then gives
> > \(\rho_H\le Q^{-b(N-1)+O_{m,M_0}(1)}\le Q^{-(N-c_3)}\),
> > since \(b\ge a+\tfrac12\ge\tfrac52\). Hence the boundary range has
> > the same required species without using a child-window limit.
> >
> > Finally, for fixed \(m\), GENIND-C1(iv) gives at most
> > \(\widetilde p(m)N^m\) live genre/height arrangements. Multiplying
> > (C2.4) by this polynomial and summing over the finitely many
> > composite blocks preserves the form \(K_cN^{B_c}Q^{-(N-c_c)}\).
> >
> > At MIXED genres, the stage-drain term and the β-child drain terms
> > combine by GENIND-6(d); the union bound of GENIND-C1(ii)/R6.2
> > applies. The child terms are supplied by GENIND-C1 and the stage
> > terms by the calculation above. No use of (CS-EXACT) is made:
> > this is a bound, not the exact-complement identity. ∎”

*(Quotation note: the source displays each equation in its own `\[ … \]` block on separate lines; the quotation above preserves every symbol, every `\tag{}` and every inequality direction, and compresses only the line breaks inside multi-line `aligned` environments. No content is elided; nothing is `…`-truncated.)*

**CONDITIONALITY:** **Superseded in three named parts by R11** (`.49`): C2(i)'s scalar stage-window bound is **WITHDRAWN** for general embedded and mixed genres; C2(ii)'s equal-product-degree descent sentence is replaced by a truncation argument; C2(iii)'s entry-pricing display is replaced by one using the ACTUAL side length. **What survives R11 unchanged: the Q-normalization (the whole point of R9), the (C2.0) domination `b − a ≥ 1/2`, and the height-sum convergence.**

**SUPERSESSION KIND:** received `replacement` at three named parts.

**CHAIN:** `.33` (r1.1's version) → **this (R9, Q-normalized)** → R11's C2Q (`.51`) with (CS-1Q) — **TERMINAL.**

**ARITHMETIC AUDIT (compiler-computed; every tagged display re-derived):**
* **(C2.0).** `L = eμγ` with `μ ≥ 2` gives `L ≥ 2eγ = 2a` ✓. Then `b = (L+1)/2 ≥ (2a+1)/2 = a + 1/2` ✓.
* **`a ≥ 2`:** `a = eγ = e·deg ψ ≥ 2` is the CS-defining inequality (shard 1 `.11`) ✓.
* **(C2.1).** `|K| = Q^γ`, so `|K|^{−(M★−c★)} = Q^{−γM★+γc★}`; with `M★ ≥ e(N−1−H)`, `−γM★ ≤ −γe(N−1−H) = −a(N−1−H)` ✓ — giving `Q^{−a(N−1−H)+γc★}` ✓ **as displayed.**
* **(C2.2)'s supporting-line sum.** `Σ_{r=1}^{L} rH/L = (H/L)·L(L+1)/2 = (L+1)H/2 = bH` ✓ **exact.**
* **(C2.3).** `−bH − a(N−1−H) = −a(N−1) − (b−a)H` ✓; and `(b−a) ≥ 1/2` gives `≤ −a(N−1) − H/2` ✓.
* **(C2.4).** `Σ_{H≥0} Q^{−H/2} = (1−Q^{−1/2})^{−1} ≤ (1−2^{−1/2})^{−1}` for `Q ≥ 2` ✓ ≈ 3.414 ✓.
* **The final species.** `a ≥ 2` gives `Q^{−a(N−1)} ≤ Q^{−2(N−1)} ≤ Q^{−(N−c₂)}` for suitable `c₂` ✓ — **and note this is where the slope-≥2 claim of `.33` becomes visible: the exponent is `a(N−1)` with `a ≥ 2`, i.e. window-deficit slope ≥ 2** ✓, matching the r1 machine leg's measured 2.00 (`.38`) ✓.
* **The floor-adjacent branch.** `M★ ≥ e(N−1−H)` and `M★ < M₀` give `e(N−1−H) < M₀`, i.e. `H > N−1−M₀/e` ✓. Then `ρ_H ≤ Q^{−bH+C₀} ≤ Q^{−b(N−1−M₀/e)+C₀} = Q^{−b(N−1)+O(1)}` ✓; with `b ≥ a + 1/2 ≥ 5/2` ✓ this is `≤ Q^{−(N−c₃)}` ✓.
* **Genre count.** `p̃(m)N^m` from GENIND-C1(iv) ✓; multiplying a `Q^{−(N−c)}` bound by a polynomial preserves the species ✓.
* **Compiler verdict: every tagged display and every intermediate step of this proof re-derives exactly.** The proof is sound **on its stated hypothesis** — and its stated hypothesis (C2(i)'s scalar `M★ ≥ e(N−1−H)`) is precisely what R11 withdraws for embedded and mixed genres. **The mathematics is right; the input is not universally available.**

**DERIVATION:** Displayed in full above. Justification tags: (i) = `by XREF (CS-1)` + `by XREF S7.1`'s slot geometry; (ii) = `by XREF S5.1` (CS-free at μ ≤ 3) + `by XREF GENIND.C′` + `computation` (lexicographic descent — **the part R11 replaces**); (iii) = `by XREF W-12 S2.2` (slot count) + `computation` (supporting-line sum); (iv) = `computation` (geometric sum) + `by XREF GENIND-C1(iv)` + `by XREF GENIND-6(d)`/`R6.2` for the mixed composition.

**RESOLUTION TRACE:** statement lines 3319–3506. proof lines — same (statement and proof are one display). correction sites: 3592–3721 (R11's C2-G1/G2/G3, `.49`–`.58`).

**TEETH:** the r1 machine leg (`.38`) was run against `.33`, **not against this version** — the R9 replacement post-dates it by two days and **has no machine leg of its own**. Disposition: **`signed vacuity disclosure`** — the Q-normalized lemma is unexercised; its d = 1 specialization coincides with the tested version, and its `d ≥ 2` content (the whole point of the repair) is untested. Recorded as OPEN-CALL 2.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:S2.2` — count **19**.

---

### EFF.GENIND.s3of3.43  [instance-record]

**CANONICAL STATEMENT:** FORM: bulleted display with LaTeX (the R9 corrected checks). verbatim, lines 3508–3541.

> “> **Displayed checks in the corrected normalization.**
> >
> > * **CS4-E(h):** \(\rho=(Q-1)Q^{1-5h}\), \(H=2h\),
> >   \(M^\star=2N-2-4h\), and \(|K|=Q\). Hence
> >   \(\rho\,\delta_{\mathrm{stage}}\le \operatorname{poly}(N)Q^{-2N-h+O(1)}\).
> > * **CS4-F(k):** \(\rho=(Q(Q-1)/2)Q^{-10k}\), \(H=4k\),
> >   \(M^\star=N-1-4k\), and \(|K|=Q^2\). Hence
> >   \(\rho\,\delta_{\mathrm{stage}}\le \operatorname{poly}(N)Q^{-2N-2k+O(1)}\).
> > * **CS5-V1E2(h):**
> >   \(\rho=(Q-1)Q^{\,2-(15h+1)/2}\left(1-Q^{-(N-(5h+1)/2)}\right)\),
> >   while \(H=2h\) and \(M^\star=2N-2-4h\). Therefore
> >   \(\rho\,\delta_{\mathrm{stage}}\le \operatorname{poly}(N)Q^{-2N-(7/2)h+O(1)}\).
> >   The fifth root's headroom is a decided-piece fiber; it does not
> >   weaken the stage-drain estimate. CS5-V4E2 and the remaining
> >   embedded \((2,2)\)-type genres have the same species: their
> >   additional vertex and split-piece constraints only strengthen
> >   (C2.2).”

**ARITHMETIC AUDIT (compiler-computed; all three, and note the third CHANGED from `.34`):**
* **CS4-E:** `ρ·Q^{−a(N−1−H)}` with `a = eγ = 2`, `H = 2h`: `Q^{1−5h}·Q^{−2(N−1−2h)} = Q^{1−5h−2N+2+4h} = Q^{−2N−h+3}` ✓ = `Q^{−2N−h+O(1)}` ✓.
* **CS4-F:** `a = eγ = 1·2 = 2`, `H = 4k`: `Q^{−10k}·Q^{−2(N−1−4k)} = Q^{−10k−2N+2+8k} = Q^{−2N−2k+2}` ✓ ✓.
* **CS5-V1E2:** `Q^{2−(15h+1)/2}·Q^{−2(N−1−2h)} = Q^{2−(15h+1)/2−2N+2+4h} = Q^{−2N+4−(15h+1)/2+4h} = Q^{−2N + 3.5 − 7h/2}` ✓ = `Q^{−2N−(7/2)h+O(1)}` ✓. **Compare `.34`'s pre-correction display, which gave `q^{−2N+O(h)}`** — i.e. R9 sharpens an `O(h)` into an explicit `−(7/2)h` **and** changes the base from q to Q ✓. **Both improvements check.**
* **Base change consistency:** at `d = 1`, `Q = q` and all three exponents coincide with `.34`'s except the sharpened third ✓ — so no committed number moves ✓, exactly as `.41` claims.

**CONDITIONALITY:** Survives R11 unchanged **at these three genres**, because R11's C2-G3 records “The CS4-E, CS4-F, and CS5-V1E2 checks have \(S=L=4\), so their displayed exponents do not change” (`.57`).

**DERIVATION:** Instantiation of `.42`.

**RESOLUTION TRACE:** statement lines 3508–3541. correction sites: 3849 (C2-G3's explicit no-change note, `.57`).

**TEETH:** none of its own; the r1 leg measured the E and F species at d = 1 (`.38`).

---

### EFF.GENIND.s3of3.44  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed display (the R9 conditionality paragraph). verbatim, lines 3543–3557.

> “> **Conditionality.** GENIND-C2 consumes the (CS-1) clause family
> > only, including recursively realized stage genres. It consumes
> > neither (CS-2), (CS-3), nor (CS-EXACT). At \(n=4\), (CS-1) is
> > de facto discharged by the pinned GENH4 package identified in
> > Step 4. At higher degrees it is already a component of
> > [GENIND-H], the hypothesis of GENIND.B. Consequently the FULL
> > complement used in GENIND-C1 has (A2-RATE): its simple part comes
> > from GENIND.C′, and its CS-drain part comes from this lemma in the
> > required base \(Q=q^d\), not merely in base \(q\).”

**CONDITIONALITY:** **Superseded by R11's certification status** (`.52`): “‘conditional on (CS-1) only’ must be replaced by ‘conditional on (CS-1Q), verified per genre.’” **So the sentence “At higher degrees it is already a component of [GENIND-H], the hypothesis of GENIND.B” — the claim that the rate leg adds no hypothesis — is exactly what R11 overturns for embedded and mixed genres.** Tagged `STALE-SELF-DESCRIPTION (uncured)`; the text is not edited.

**SUPERSESSION KIND:** received `replacement` (of the conditionality label).

**TARGETS (of the eventual replacement):** shard 1 `.13`, `.37`, `.57`, `.63`; `.04`, `.05`, `.35` here.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 3543–3557. correction sites: 3712 (`.52`).

**TEETH:** the n = 4 discharge is a citation (shard 1 `.59`).

---

### EFF.GENIND.s3of3.45  [changes-record]

**CANONICAL STATEMENT:** FORM: bulleted display (R9's riding MINOR-A). verbatim, line 3561.

> “* **[2026-08-12, riding MINOR-A]** In r1.1's preregistration, read “P1 … at 10 scored fresh rows” as “P1 … at 11 scored fresh rows”; the roster has 12 fresh rows, of which the floor-adjacent F row \((q,k,N)=(3,1,6)\) has \(M^\star=1\) and was disclosed but not scored, leaving exactly 11 scored rows as the committed record reports.”

**SUPERSESSION KIND:** `wording-rider` (a numeral in a preregistration corrected to match the roster and the committed record).

**TARGETS:** `s3of3.36`.

**ARITHMETIC AUDIT:** independently re-derived at `.36`: roster E 8 rows + roster F 4 rows = **12**, minus the floor-adjacent `(3,1,6)` with `M★ = 6−1−4 = 1` → **11 scored** ✓. **MINOR-A is correct and the compiler's independent count agrees.**

**CONDITIONALITY:** A preregistration numeral corrected *after* the run — which would normally be a serious protocol issue. **It is not one here**, because the committed record already reported 11 and the correction moves the *preregistration* into line with the *roster*, not the other way round; the note says so (“as the committed record reports”).

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement line 3561. correction sites: none.

**TEETH:** `arithmetic recount`.

---

### EFF.GENIND.s3of3.46  [changes-record]

**CANONICAL STATEMENT:** FORM: bulleted display (R9's riding MINOR-B — the consumed-surface census replaced). verbatim, line 3563.

> “* **[2026-08-12, riding MINOR-B]** Supersede R1.4's “five committed displays” census by this enumerated consumed-surface census: W-11's \(R(M)\); HEX3.A's exact law; HEX3.B's rate; GT-BDRAIN's \(n=4,5\) first-step recursions; GENIND-BOX-4's pricing sentence; the M6 and PSTEEP3/PSTEEP4 locus data used in GENIND-C1(i); and the six extraction identities used in GENIND-C1(iii), namely M6, TWOCHILD-A, TWOCHILD-B, PSTEEP3, PSTEEP4, and SS6.”

**SUPERSESSION KIND:** `inventory completion` — a five-item census replaced by a longer enumerated one.

**TARGETS:** `s3of3.07` (R1.4's census).

**ARITHMETIC AUDIT (compiler-computed):** the new census names **5 original items + the M6/PSTEEP3/PSTEEP4 locus data (3) + the six extraction identities (6) = 14 named objects**, of which M6, PSTEEP3 and PSTEEP4 appear twice (once as locus data for C1(i), once as extraction identities for C1(iii)) → **11 distinct objects** ✓. Every one is verifiable in shard 1: R(M) (`.25`, `.45`), HEX3.A/B (`.45`, `.46`), GT-BDRAIN (`.25`), GENIND-BOX-4 (shard 2 `.04`), M6 (`.33`, `.38`), PSTEEP3/PSTEEP4 (`.28`), TWOCHILD-A/B (`.27`), SS6 (`.42`) ✓ — **11/11 exist at their committed instance rows.** The note's own verification wording (`.48`) says exactly this: “MINOR-B's enumerated census verified for existence of every named object at its committed instance rows”.

**CONDITIONALITY:** The census is an enumeration, rule-compliant; but note the note's own honest scoping at `.48`: “the item-by-item consumed-surface attribution is sol's enumeration” — i.e. **the objects were verified to EXIST, and the attribution of each to a consumption site was not independently re-derived.**

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement line 3563. correction sites: none.

**TEETH:** `arithmetic recount` (existence of 11/11 objects) with a disclosed limit on the attribution.

---

### EFF.GENIND.s3of3.47  [changes-record]

**CANONICAL STATEMENT:** FORM: bulleted display (R9's riding MINOR-C — the height-sum sentence replaced). verbatim, line 3565.

> “* **[2026-08-12, riding MINOR-C]** Replace “the entry mass \(\rho\) decays geometrically in \(H\), so the height sum converges” by: “S2.2 gives \(\rho_H\le Q^{-((L+1)/2)H+O_m(1)}\), while the stage factor is at most \(Q^{-e\deg\psi\,(N-1-H)+O(1)}\); since \(L\ge e\mu\deg\psi\ge2e\deg\psi\), one has \((L+1)/2-e\deg\psi\ge1/2\), so the composed summand is at most \(Q^{-e\deg\psi\,(N-1)-H/2+O(1)}\), whose \(H\)-sum is geometric.”

**SUPERSESSION KIND:** `replacement` — a hand-wave (“decays geometrically in H, so the height sum converges”) replaced by the explicit domination argument. **This is the substantive one of the three folds:** the original sentence attributed the convergence to the entry mass alone, and the replacement shows the convergence comes from the *difference* `b − a ≥ 1/2`, i.e. from the entry price BEATING the stage factor's growth in H. `.42`'s own (iii) says it: “entry decay alone was not the reason the height sum converges.”

**TARGETS:** `s3of3.33`(iii) (the r1.1 sentence).

**ARITHMETIC AUDIT:** `L = eμγ ≥ 2eγ` (μ ≥ 2) ✓; `(L+1)/2 − eγ ≥ (2eγ+1)/2 − eγ = 1/2` ✓; composed summand `Q^{−bH}·Q^{−a(N−1−H)} = Q^{−a(N−1)−(b−a)H} ≤ Q^{−a(N−1)−H/2}` ✓; the H-sum is geometric with ratio `Q^{−1/2} ≤ 2^{−1/2}` ✓. **Every step re-derives, and it is the same computation as (C2.0)+(C2.3).**

**CONDITIONALITY:** Survives R11 with `b` replaced by `b_S = (S+1)/2 ≥ (L+1)/2` (`.57`), i.e. **strengthened**, not weakened.

**DERIVATION:** Displayed.

**RESOLUTION TRACE:** statement line 3565. correction sites: 3842–3850 (C2-G3's consumer sweep, `.58`).

**TEETH:** `arithmetic recount`.

---

### EFF.GENIND.s3of3.48  [changes-record]

**CANONICAL STATEMENT:** FORM: italic parenthetical paragraph (the R9 orchestrator-verification record). verbatim, lines 3567–3588.

> “*(The replacement lemma and three folds above were derived by the R9
> certification run (gpt-5.6-sol high,
> runs/cert/R9_drain_repair_output.log, 2026-08-12); orchestrator
> verification before transcription — the d-factor defect confirmed at
> HEAD (r1.1's C2(iii) conclusion displays q^{−(N−c_c)} against the
> Q^{m(N−1)} normalization, while its own stage estimate retains
> e·d·deg ψ); the replacement's algebra re-derived by hand: (C2.0)
> L = eμγ ≥ 2a and b − a = (L+1)/2 − eγ ≥ 1/2; the entry-price
> exponent Σ_{r≤L} rH/L = (L+1)H/2; the composition
> Q^{−a(N−1)−(b−a)H}; the lexicographic descent at μ ≥ 4 (μγ ≤ m,
> equality only at e = 1 where H > 0 shrinks the window); the
> floor-adjacent branch (b ≥ 5/2); and all three displayed checks
> (CS4-E: exponent 1−5h−2(N−1−2h) = −2N−h+O(1); CS4-F:
> −10k−2(N−1−4k) = −2N−2k+O(1); CS5-V1E2: 2−(15h+1)/2−2(N−1−2h) =
> −2N−(7/2)h+O(1)). MINOR-A checked against the committed machine
> record (P1 GREEN 11/0, the (3,1,6) row disclosed-not-scored, roster
> count 12 re-added); MINOR-B's enumerated census verified for
> existence of every named object at its committed instance rows (the
> item-by-item consumed-surface attribution is sol's enumeration);
> MINOR-C is the (C2.0)-domination just verified. Transcribed
> unaltered per the standing division of labor. Ledger: row 17 →
> repaired, awaiting the clean sol re-pass.)*”

**CONDITIONALITY:** **A provenance record with an explicit division-of-labour disclosure: the mathematics was DERIVED by a different model and TRANSCRIBED unaltered, with the orchestrator's verification enumerated before transcription.** This is the corpus's standing protocol for sol-derived repairs, and it is what makes the unit's evidence chain auditable.

**ARITHMETIC AUDIT:** the orchestrator's enumerated re-derivations are **exactly the ones this compiler independently performed at `.42`, `.43`, `.47`** — (C2.0), the entry-price sum, the composition, the floor-adjacent branch, and all three displayed checks — **and all agree.** One item the orchestrator lists is the lexicographic descent “equality only at e = 1 where H > 0 shrinks the window”, **which R11 subsequently found insufficient** (`.54`, `.55`): the inference `M★ < N` from a *lower* bound is invalid. **So the orchestrator's verification passed a step that a later decorrelated pass refuted** — recorded, because it is the sharpest available evidence about the limits of verify-then-transcribe.

**SUPERSESSION KIND:** none of its own.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 3567–3588. correction sites: 3723–3793 (C2-G2, which refutes the descent step this record verified).

**TEETH:** `in-house hostile pass` (the orchestrator's pre-transcription check) — **with a disclosed miss**, per the audit above. Ledger cross-reference: “Ledger: row 17 → repaired, awaiting the clean sol re-pass” — the re-pass is `.49`.

**PIN VERIFICATION:** `runs/cert/R9_drain_repair_output.log` EXISTS ✓.

---
### EFF.GENIND.s3of3.49  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph (the R11 round-2 correction's supersession declaration — **the shard's most consequential single paragraph**). verbatim, lines 3592–3594.

> “### Dated correction (2026-08-12 — GENIND-C2 repair round 2)
>
> **Supersession and scope.** This append supersedes the stage-window assertion in C2(i), the equal-product-degree descent sentence in C2(ii), and the entry-pricing display in C2(iii) of the 2026-08-12 GENIND-C2 correction. The scalar bound \(M^\star\ge e(N-1-H)\) is withdrawn for general embedded and mixed genres: the displayed (CS-1) clause supplies ragged per-coordinate certified windows and permits sibling-Hensel losses, but supplies no inequality pricing those losses. The corrected quantitative clause below is sufficient for every downstream use. Its verification remains a per-genre obligation inside (CS-1).”

**CONDITIONALITY:** **A WITHDRAWAL, not a re-wording.** `M★ ≥ e(N−1−H)` — the input on which `.42`'s entire proof rests — is withdrawn for general embedded and mixed genres, with a precise reason: (CS-1) supplies *ragged per-coordinate* windows and *permits* sibling-Hensel losses **without pricing them**. The replacement (C2Q) is “sufficient for every downstream use”, and **its verification is a per-genre obligation**, i.e. the discharge is deferred, not achieved.

**SUPERSESSION KIND:** `replacement` at three named parts, one of which is a **withdrawal** — a sub-kind the v3 enum does not distinguish (§6.3). **`replacement` is the right kind and the withdrawal must be recorded in the field text, because a merge that reads it as an ordinary replacement will not know that a previously-available input is now unavailable.**

**TARGETS:** `s3of3.42` parts (i), (ii), (iii); and, transitively, `.33`, `.35`, `.39`, `.44`.

**ARITHMETIC AUDIT (compiler-computed, on the withdrawal's ground):** (CS-1) as displayed (shard 1 `.63`) asserts a count-isomorphism “at an explicit stage window, RAGGED-WINDOW-CORRECTED”, and GENIND-6(a) (shard 1 `.34`) leaves composite blocks “as a monic cofactor with PER-COEFFICIENT certified windows (the triangular division ledger; the sibling-Hensel-loss composition GENHN already displays … ‘N ↦ N − (sibling Hensel loss) coordinate-wise’)”. **Neither supplies a numeric floor on the loss** ✓ — so a scalar lower bound `M★ ≥ e(N−1−H)` on a *common uniform* window does not follow from them ✓. **The withdrawal is correct.**

**DERIVATION:** Not a mathematical unit; a supersession declaration.

**RESOLUTION TRACE:** statement lines 3592–3594. correction sites: none downstream in this note.

**TEETH:** `decorrelated-model audit` (the sol R11 re-pass). **PIN VERIFICATION:** `runs/cert3/R11_genind_output.log` EXISTS ✓.

---

### EFF.GENIND.s3of3.50  [hypothesis]

**CANONICAL STATEMENT:** FORM: heading + prose + **LaTeX definitions and the two tagged clauses (CS-1Q.a) and (CS-1Q.b)** — the ledger's HYP.36. verbatim, lines 3596–3637.

> “#### C2-G1 — loss-priced uniform core
>
> Fix a CS genre \(\mathcal G\), put
> \[
> Q=q^d,\qquad \gamma=\deg\psi,\qquad a=e\gamma,\qquad L=e\mu\gamma,
> \]
> and let \(S\ge L\) be the actual horizontal length of the side carrying the composite block. Let \(H\) be that side's vertical drop and put
> \[
> b_S:=\frac{S+1}{2}.
> \]
> From the per-coordinate certified windows supplied by (CS-1), define:
>
> - \(\lambda_{\mathcal G}\): the largest loss, in \(v'\)-height units, caused by the sibling-Hensel division ledger;
> - \(r_{\mathcal G}\): the further number of \(v'\)-height units discarded when the residue-class strings are truncated below their ragged ends;
> - \(\Delta_{\mathcal G}:=\lambda_{\mathcal G}+r_{\mathcal G}\);
> - \(M_{\mathcal G}\): the resulting common uniform stage window;
> - \(C_{\mathcal G}^{\mathrm{extra}}\): the entry codimension, in \(Q\)-digit units, contributed by sibling sides, vertices, split pieces, residual pins, and other conditions beyond the supporting-line price on the \(S\)-long side.
>
> The quantitative stage-transport clause required here is:
> \[
> M_{\mathcal G} \ge e(N-1-H)-\Delta_{\mathcal G},                 \tag{CS-1Q.a}
> \]
> and
> \[
> \gamma\Delta_{\mathcal G} \le C_{\mathcal G}^{\mathrm{extra}}
>    +\left(b_S-a-\frac12\right)H+O_{\mathcal G}(1).            \tag{CS-1Q.b}
> \]
>
> Clause (CS-1Q.b) is the explicit price of the ragged boundary and sibling-Hensel losses. It says that every lost \(K\)-digit is paid either by an additional entry condition or by the supporting-line slack beyond the load-bearing coefficient \(a+\tfrac12\).”

**CONDITIONALITY:** **THIS IS LEDGER ROW HYP.36**, verbatim (`spec/HYPOTHESIS_LEDGER.md:310–315`):

> “HYP.36  `(CS-1Q)`
> WHERE: `GENIND_PROOF_2026-08-08.md`, §C2-G1 L3592–3722.
> STATEMENT: Both clauses hold: M_G≥e(N−1−H)−Δ_G, and the displayed digit-loss rate follows; the rate does not by itself assert all residual mass is zero.
> CONSUMED BY: DRAIN-N4/A2.
> CLASS: named-obligation
> PROPOSED DISPOSITION: CARRY — embedded/mixed affine ledgers are not universally checked.”

The ledger's line-range `L3592–3722` matches this shard's C2-G1 span exactly ✓. Its disposition is **CARRY**, and its stated reason is precisely `.52`'s certification-status paragraph.

**SUPERSESSION KIND:** `replacement` (of the withdrawn scalar bound by a two-clause family) + `inventory completion` (five new named quantities defined).

**TARGETS:** shard 1 `.37`, `.57`, `.63`; `.05`, `.33`, `.35`, `.42`, `.44` here.

**ARITHMETIC AUDIT (compiler-computed):**
* **(CS-1Q.a)** relaxes the withdrawn bound by exactly the total loss `Δ_G = λ_G + r_G` ✓ — so at `Δ_G = 0` it IS the withdrawn bound ✓, which is why the standalone CS4-E/CS4-F displays are unaffected (`.52`).
* **(CS-1Q.b)** is the pricing condition. Reading it as the audit of `.51`'s exponent: the proof needs `γΔ_G − C_extra − (b_S − a)H ≤ −H/2 + O(1)`, i.e. `γΔ_G ≤ C_extra + (b_S − a − 1/2)H + O(1)` ✓ — **(CS-1Q.b) is exactly the inequality C2Q's algebra requires, no more and no less.** That is a design virtue: the hypothesis is not stronger than the use.
* **`S ≥ L`** ✓ by definition (the composite block occupies length L of an S-long side).
* **`b_S = (S+1)/2 ≥ (L+1)/2 ≥ a + 1/2`** ✓ (C2-G3's (C2E.3)) — so the slack coefficient `b_S − a − 1/2 ≥ 0` ✓, i.e. **(CS-1Q.b)'s right-hand side is nonnegative**, and the clause is not vacuously false.

**DERIVATION:** Definitional (the five quantities) + a stated hypothesis (the two clauses). **NOT proved** — that is the point.

**RESOLUTION TRACE:** statement lines 3596–3637. correction sites: none.

**TEETH:** **NONE — and this is the single most important `signed vacuity disclosure` in the three shards.** `.52` states it: the displayed (CS-1), GENIND-6(a) and GENHN references “do not establish (CS-1Q.b) for every embedded or mixed genre”. The standalone CS4-E/CS4-F cases have `Δ_G = 0` and are fine; **every embedded or mixed genre carries an unverified per-genre obligation.**

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:S11.F` — count **10** (the affine ledger species the clause would have to be checked against).

---

### EFF.GENIND.s3of3.51  [lemma]

**CANONICAL STATEMENT:** FORM: display (blockquote, ANNEX-LEMMA GENIND-C2Q) + its proof with tagged equations. verbatim, lines 3639–3710.

> “> **ANNEX-LEMMA GENIND-C2Q (loss-priced core).** Assume (CS-1Q.a–b) for the fixed genre. Then its conservative stage-drain contribution satisfies
> >
> > \[
> > \frac{u^{\mathrm{CS}}_{\mathcal G}(N)}{Q^{m(N-1)}}
> > \le K_{\mathcal G}N^{B_{\mathcal G}} Q^{-a(N-1)-H/2+O_{\mathcal G}(1)}.          \tag{C2Q.1}
> > \]
> >
> > Consequently its height sum has the required \(K N^B Q^{-(N-c)}\) form.
>
> *Proof.* The corrected entry count, proved under C2-G3 below, is
> \[
> \rho_{\mathcal G} \le Q^{-b_SH-C_{\mathcal G}^{\mathrm{extra}} +O_{\mathcal G}(1)}.                     \tag{C2Q.2}
> \]
> On the range where the quantitative stage estimate is invoked, GENIND.C′ over \(K\), with \(|K|=Q^\gamma\), gives
> \[
> \delta_{\mathrm{stage}} \le K_\star N^{B_\star}Q^{-\gamma M_{\mathcal G} +O_{\mathcal G}(1)}.
> \]
> By (CS-1Q.a),
> \[
> -\gamma M_{\mathcal G} \le-a(N-1-H)+\gamma\Delta_{\mathcal G}.
> \]
> Multiplying by (C2Q.2) and applying (CS-1Q.b),
> \[
> \begin{aligned}
> \rho_{\mathcal G}\delta_{\mathrm{stage}}
> &\le K_\star N^{B_\star} Q^{-a(N-1)-(b_S-a)H -C_{\mathcal G}^{\mathrm{extra}} +\gamma\Delta_{\mathcal G} +O_{\mathcal G}(1)}\\
> &\le K_\star N^{B_\star} Q^{-a(N-1)-H/2+O_{\mathcal G}(1)}.
> \end{aligned}
> \]
> For the floor-adjacent range \(M_{\mathcal G}<M_0\), (CS-1Q.a) gives
> \[
> \gamma\Delta_{\mathcal G} >a(N-1-H)-\gamma M_0.
> \]
> Combining this with (CS-1Q.b) yields
> \[
> b_SH+C_{\mathcal G}^{\mathrm{extra}} \ge a(N-1)+\frac H2-O_{\mathcal G,M_0}(1).
> \]
> Thus the trivial stage-drain bound \(1\) gives (C2Q.1) there as well. Finally,
> \[
> \sum_{H\ge0}Q^{-H/2} \le (1-2^{-1/2})^{-1},
> \]
> and the polynomial genre count of GENIND-C1(iv) absorbs the remaining fixed-degree parameters. ∎”

**CONDITIONALITY:** **Conditional on (CS-1Q.a–b) per genre** — the whole content of the round-2 repair. Its conclusion is the same species as `.42`'s, so **every downstream consumer is unaffected in FORM and re-conditioned in HYPOTHESIS.**

**ARITHMETIC AUDIT (compiler-computed; every step re-derived):**
* `−γM_G ≤ −γ[e(N−1−H) − Δ_G] = −a(N−1−H) + γΔ_G` ✓ (using `γe = a` ✓).
* Multiplying: exponent `= −b_S H − C_extra − a(N−1−H) + γΔ_G + O(1) = −a(N−1) − (b_S − a)H − C_extra + γΔ_G + O(1)` ✓ **as displayed**.
* Applying (CS-1Q.b) `γΔ_G ≤ C_extra + (b_S − a − 1/2)H + O(1)`: the exponent `≤ −a(N−1) − (b_S−a)H − C_extra + C_extra + (b_S−a−1/2)H + O(1) = −a(N−1) − H/2 + O(1)` ✓ **exact.**
* **Floor-adjacent branch.** From (CS-1Q.a), `M_G ≥ e(N−1−H) − Δ_G`, so `M_G < M_0` gives `e(N−1−H) − Δ_G < M_0`, i.e. `Δ_G > e(N−1−H) − M_0`, hence `γΔ_G > a(N−1−H) − γM_0` ✓ **as displayed.** Combining with (CS-1Q.b): `a(N−1−H) − γM_0 < γΔ_G ≤ C_extra + (b_S−a−1/2)H + O(1)`, so `C_extra + b_S H ≥ a(N−1−H) + aH + H/2 − O(1) = a(N−1) + H/2 − O(1)` ✓ **exact** (using `−(b_S−a−1/2)H + b_S H = aH + H/2` ✓). Then the trivial bound `δ ≤ 1` with `ρ ≤ Q^{−b_S H − C_extra + O(1)} ≤ Q^{−a(N−1)−H/2+O(1)}` ✓ gives (C2Q.1) ✓.
* Height sum and genre count as at `.42` ✓.
* **Compiler verdict: the C2Q proof is correct and every step re-derives.** It is *cleaner* than `.42`'s, because the hypothesis was reverse-engineered from the algebra.

**SUPERSESSION KIND:** `replacement` (of `.42`'s (i)/(iii) mechanics by a loss-priced version).

**DERIVATION:** Displayed. Justification tags: (C2Q.2) = `by XREF C2-G3` (`.57`); the stage estimate = `by XREF GENIND.C′` over K; the two combinations = `computation` (audited above); the floor-adjacent branch = `computation`; the closing = `by XREF GENIND-C1(iv)`.

**RESOLUTION TRACE:** statement lines 3639–3710. proof lines — same. correction sites: none.

**TEETH:** **NONE.** No machine leg was added at R11 (the r1 leg predates and was run against `.33`). Disposition: **`signed vacuity disclosure`** — the lemma is proved and unexercised, and its hypothesis is per-genre unverified.

---

### EFF.GENIND.s3of3.52  [fence]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (the C2-G1 certification status — **the honest residue**). verbatim, line 3712.

> “**Certification status.** The standalone CS4-E and CS4-F displays have no sibling loss in their uniform cores and satisfy the calculation directly. The displayed general (CS-1), GENIND-6(a), and GENHN references do not establish (CS-1Q.b) for every embedded or mixed genre: they assert affine per-coordinate windows and boundary routing, but do not relate the resulting loss to entry codimension. Accordingly, “conditional on (CS-1) only” must be replaced by “conditional on (CS-1Q), verified per genre.” A universal discharge for embedded and mixed genres remains obstructed until those affine ledgers are displayed and checked.”

**CONDITIONALITY:** **The load-bearing honesty sentence of the entire annex stack**, and the source of ledger row HYP.36's CARRY disposition. Its three clauses do three different jobs: (1) the standalone quartic genres are FINE (`Δ_G = 0`); (2) the general references are INSUFFICIENT, with the reason named (they assert windows and routing, not a loss-to-codimension relation); (3) the label change is MANDATORY, and the obstruction is named as a displayed-and-checked-ledgers obligation.

**SUPERSESSION KIND:** `replacement` of a conditionality label, applied globally to every rate consumer.

**TARGETS:** shard 1 `.13`, `.37`, `.57`, `.63`; `.04`, `.05`, `.33`, `.35`, `.39`, `.42`, `.44` here.

**ARITHMETIC AUDIT:** “The standalone CS4-E and CS4-F displays have no sibling loss in their uniform cores” — at those genres the whole polygon is the side (shard 1 `.48`, `.49`: “n = 4 (the whole polygon is the side)”), so there is no sibling block to lose Hensel digits to ✓, `Δ_G = 0` ✓, and (CS-1Q.a) reduces to the withdrawn scalar bound ✓, which `.42`'s proof then uses directly ✓. **The exemption is correctly scoped.**

**DERIVATION:** Not a mathematical unit; a certification-status fence.

**RESOLUTION TRACE:** statement line 3712. correction sites: none — this is the terminal reading.

**TEETH:** **the fence IS the disclosure.** Disposition: `signed vacuity disclosure` for embedded/mixed genres; `accepted` for the two standalone quartic genres.

---

### EFF.GENIND.s3of3.53  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed bulleted display (the C2-G1 consumer sweep). verbatim, lines 3714–3721.

> “**C2-G1 consumer sweep.**
>
> - In GENIND-C2(i), replace \(M^\star\ge e(N-1-H)\) by (CS-1Q.a–b).
> - In C2.1–C2.4, replace the separate entry/window multiplication by ANNEX-LEMMA GENIND-C2Q.
> - In R1.1's full-complement closure and GENIND-C1(iii)'s growing-window use, read the CS-drain rate as conditional on (CS-1Q), not bare (CS-1).
> - In GENIND.B Step 4 and the GENIND-6(d) mixed-drain union bound, child terms remain supplied by GENIND-C1; stage terms are supplied by GENIND-C2Q.
> - The claims that (CS-2), (CS-3), and (CS-EXACT) are not consumed by this rate bound remain correct.
> - At \(n=4\), the standalone E/F calculations remain valid. No general embedded/mixed discharge is asserted by this append.”

**CONDITIONALITY:** **A consumer sweep reaching into the byte-frozen body** (bullets 3 and 4 name R1.1's closure, GENIND-C1(iii), GENIND.B Step 4 and GENIND-6(d)) **without quoting the target sentences.** Its status as a supersession vehicle is OPEN-CALL 1.

**SUPERSESSION KIND:** `replacement` (bullets 1, 2, 4) + `scope-pin` (bullet 3) + explicit **non**-supersessions (bullets 5, 6). **A single sweep carrying three kinds and two disclaimers — the format's hardest case for a merge.**

**TARGETS, resolved to unit IDs by this compiler:** bullet 1 → `s3of3.42`(i); bullet 2 → `s3of3.42`(C2.1–C2.4); bullet 3 → `s3of3.04` (R1.1's closure) and `s3of3.05`(iii); bullet 4 → **shard 1 `.57`** (GENIND.B Step 4) and **shard 1 `.37`** (GENIND-6(d)); bullets 5–6 → no target (negative declarations).

**ARITHMETIC AUDIT:** six bullets, of which four are instructions and two are non-supersessions ✓; every named target is identifiable ✓ (six for six).

**DERIVATION:** Not a mathematical unit; an install instruction.

**RESOLUTION TRACE:** statement lines 3714–3721. correction sites: none.

**TEETH:** NONE — an install record.

---

### EFF.GENIND.s3of3.54  [lemma]

**CANONICAL STATEMENT:** FORM: heading + display (blockquote, ANNEX-LEMMA GENIND-C2D) + proof, with one tagged equation. verbatim, lines 3723–3734.

> “#### C2-G2 — well-founded descent by truncation and monotonicity
>
> > **ANNEX-LEMMA GENIND-C2D (window truncation).** Let
> > \(\delta_{\mu,K}(W)\) be the conservative-undecided fraction of a
> > \((\mu,K)\)-cluster system at window \(W\). If \(1\le T\le W\),
> > then
> > \[
> > \delta_{\mu,K}(W)\le\delta_{\mu,K}(T).            \tag{C2D.1}
> > \]
>
> *Proof.* Reduction from window \(W\) to \(T\) has constant fibers. If a truncation were decided at window \(T\), its decision would depend only on digits below \(T\), and the same certificate would decide every lift at window \(W\). Hence every window-\(W\) undecided state lies above a window-\(T\) undecided state. Dividing the resulting cardinality inequality by the two total state counts gives (C2D.1). The same argument applies to a ragged stage after truncation to any common uniform core below all residue-class ends; the discarded boundary slots are constant fiber coordinates. ∎”

**CONDITIONALITY:** **Unconditional — a genuinely new small lemma, and the one that makes the joint recursion well-founded.** Its content is a monotonicity: shrinking the window cannot decrease the undecided fraction.

**ARITHMETIC AUDIT (compiler-computed):** the reduction map `states(W) → states(T)` for `T ≤ W` is a truncation, with constant fibre size `Q^{μ(W−T)}` ✓ (each of the μ coordinates loses `W−T` digit levels). The decidedness argument: if the truncation of a state is decided at window T, the deciding certificate reads only digits below T, hence decides the state at window W too ✓ — so **W-undecided ⟹ T-undecided (contrapositive of T-decided ⟹ W-decided)** ✓, i.e. the undecided set at W maps into the undecided set at T ✓. Cardinalities: `|U_W| ≤ |U_T|·Q^{μ(W−T)}` ✓; dividing by totals `Q^{μ(W−1)}` and `Q^{μ(T−1)}` gives `δ(W) = |U_W|/Q^{μ(W−1)} ≤ |U_T|Q^{μ(W−T)}/Q^{μ(W−1)} = |U_T|/Q^{μ(T−1)} = δ(T)` ✓ **exact.** **The lemma and its proof are correct.**
**Compiler observation on the conservative read.** The argument needs the read to be *monotone in the window* — i.e. that a decision made on a T-truncation is not retracted at W. That is exactly the conservative-drain convention's content (`v(a₀) ≥ N ⟹ UNDECIDED exit`, shard 1 `.07`), which decides only on visible data. **The proof does not cite that convention explicitly**; the step “the same certificate would decide every lift at window W” is where it is used. Recorded as a **compressed citation, not a gap.**

**SUPERSESSION KIND:** `inventory completion` (a well-foundedness ingredient the descent argument needed and did not have).

**DERIVATION:** Displayed.

**RESOLUTION TRACE:** statement lines 3723–3734. correction sites: none.

**TEETH:** NONE. Disposition: `signed vacuity disclosure` — a new unexercised lemma. (Its content is however *implied* by every GT-DEPTH0 row, which reads the same states at nested windows; no row tests the inequality directly.)

---

### EFF.GENIND.s3of3.55  [lemma]

**CANONICAL STATEMENT:** FORM: prose + LaTeX displays (the lexicographic measure and the descent, replacing C2(ii)'s refuted sentence). verbatim, lines 3736–3784.

> “Use the lexicographic measure
> \[
> \mathfrak m=(\text{product degree},\text{window}) \in\mathbb N_{>0}\times\mathbb N_{\ge1}.
> \]
> For a composite stage, its product degree is
> \[
> D'=\mu d\gamma, \qquad D=md, \qquad m\ge e\mu\gamma.
> \]
> If \(e\ge2\), then
> \[
> D'\le D/e<D,
> \]
> so the first component decreases. If \(e=1\), then \(D'\le D\). When \(D'<D\), the first component again decreases. In the only remaining case \(e=1\) and \(D'=D\), let \(M_{\mathcal G}\) be the common uniform stage window and set
> \[
> T:=\min\{M_{\mathcal G},\,N-1\}.
> \]
> Then \(T<N\), and C2D.1 gives
> \[
> \delta_{\mu,K}(M_{\mathcal G}) \le\delta_{\mu,K}(T).
> \]
> The recursive estimate is therefore invoked at
> \[
> (D',T)=(D,T)<_{\mathrm{lex}}(D,N).
> \]
> No inference \(M^\star<N\) from a lower bound is used. If \(T=1\), the window-1 base case is exactly the R3 convention rider. Moreover, in the equal-degree case \(e=1\),
> \[
> e(N-1-H)-\Delta_{\mathcal G}\le N-1,
> \]
> so replacing \(M_{\mathcal G}\) by \(T\) preserves the lower bound (CS-1Q.a) needed in C2Q's exponent calculation.”

**CONDITIONALITY:** **The repair of a genuinely invalid step.** C2(ii) had inferred `M★ < N` from a *lower* bound on `M★` — “the visible opening has \(H>0\), hence \(M^\star<N\)” — which does not follow. The replacement never infers an upper bound: it **truncates** to `T := min{M_G, N−1} < N` and uses C2D's monotonicity to pay for the truncation. **The sentence “No inference \(M^\star<N\) from a lower bound is used” is the note naming its own former error.**

**ARITHMETIC AUDIT (compiler-computed):**
* `e ≥ 2`: `m ≥ eμγ` gives `μγ ≤ m/e`, so `D' = μdγ ≤ md/e = D/e < D` ✓.
* `e = 1`: `m ≥ μγ` gives `D' = μdγ ≤ md = D` ✓.
* Equal case `D' = D`: `T := min{M_G, N−1} ≤ N−1 < N` ✓; `(D, T) <_lex (D, N)` ✓ since the first components tie and `T < N` ✓ — **well-founded** ✓.
* C2D applies because `1 ≤ T ≤ M_G` — **requires `T ≥ 1`, i.e. `min{M_G, N−1} ≥ 1`, i.e. `M_G ≥ 1` and `N ≥ 2`** ✓ (the ambient window is ≥ 2 by S1; `M_G ≥ 1` is the live-stage condition, and `T = 1` is routed to R3's base case ✓).
* The preservation claim: in the equal-degree case `e = 1`, `(CS-1Q.a)`'s right side is `1·(N−1−H) − Δ_G ≤ N−1` ✓ (since `H ≥ 0, Δ_G ≥ 0`), so `T = min{M_G, N−1} ≥ min{e(N−1−H)−Δ_G, N−1} = e(N−1−H)−Δ_G` ✓ — **the lower bound survives truncation** ✓ **exact.**
* **Compiler verdict: the descent is now genuinely well-founded and every step re-derives.** The refuted inference is gone and nothing replaces it that needs an upper bound.

**SUPERSESSION KIND:** `replacement` (of C2(ii)'s descent sentence).

**TARGETS:** `s3of3.42`(ii).

**DERIVATION:** Displayed.

**RESOLUTION TRACE:** statement lines 3736–3784. correction sites: none.

**TEETH:** NONE. Disposition: `signed vacuity disclosure`; the descent is a proof structure no run exercises.

---

### EFF.GENIND.s3of3.56  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed bulleted display (the C2-G2 consumer sweep). verbatim, lines 3786–3793.

> “**C2-G2 consumer sweep.**
>
> - Delete “\(H>0\), hence \(M^\star<N\)” from C2(ii).
> - Replace it by the lexicographic measure and truncation argument above.
> - The \(e\ge2\) degree-descent branch is unchanged.
> - GENIND.C′'s α-window induction and GENIND-C1's β-child degree descent are unchanged.
> - The joint recursion of GENIND.C′ with GENIND-C2 now has a displayed well-founded measure in every case.
> - No new upper bound on the original ragged stage window is claimed or needed.”

**CONDITIONALITY:** **The only sweep in the shard that DELETES a clause** (“Delete … from C2(ii)”), and it says so in the imperative. The remaining bullets are explicit non-changes and a closing disclaimer.

**SUPERSESSION KIND:** `replacement` with an explicit **deletion** — again a sub-kind the enum does not name (§6.3). Deleting a *false inference* is different from replacing a *display*, and a merge that flattens them may leave the deleted sentence readable as live text (it remains byte-intact at line 3382).

**TARGETS:** `s3of3.42`(ii). Non-targets declared: `.42`'s `e ≥ 2` branch, `.06` (GENIND.C′'s α-induction), `.05` (GENIND-C1's β-descent).

**ARITHMETIC AUDIT:** six bullets ✓; the deleted string “H>0, hence M★<N” is present at line 3382 of the source ✓ (inside `.42`(ii)), so the deletion instruction has a real target ✓.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 3786–3793. correction sites: none.

**TEETH:** NONE.

---

### EFF.GENIND.s3of3.57  [lemma]

**CANONICAL STATEMENT:** FORM: heading + prose with three tagged LaTeX displays (C2-G3 — entry pricing at the ACTUAL side length). verbatim, lines 3795–3840.

> “#### C2-G3 — entry pricing uses the actual side length
>
> Let the actual side have horizontal length \(S\), vertical drop \(H\), and let the chosen composite residual block occupy length
> \[
> L=e\mu\gamma\le S.
> \]
> Relative to the side's right endpoint, its \(S\) coefficient columns have supporting-line heights
> \[
> \frac{H}{S},\frac{2H}{S},\ldots,\frac{SH}{S}.
> \]
> Therefore the number of forced \(Q\)-digit levels is at least
> \[
> \begin{aligned}
> \sum_{r=1}^{S} \left(\left\lceil\frac{rH}{S}\right\rceil-1\right)
> &\ge \sum_{r=1}^{S}\frac{rH}{S}-O_m(1)\\
> &=\frac{S+1}{2}H-O_m(1)\\
> &\ge\frac{L+1}{2}H-O_m(1).                         \tag{C2E.1}
> \end{aligned}
> \]
> The \(O_m(1)\) term absorbs the ceiling errors, the already-pinned level-zero digits, and the fixed residual-letter census. Other sides, vertices, sibling blocks, and decided pieces only add conditions. Hence
> \[
> \rho_{\mathcal G} \le Q^{-((S+1)/2)H-C_{\mathcal G}^{\mathrm{extra}} +O_m(1)}
>  \le Q^{-((L+1)/2)H-C_{\mathcal G}^{\mathrm{extra}} +O_m(1)}.                                \tag{C2E.2}
> \]
> Since \(L=e\mu\gamma\ge2e\gamma=2a\),
> \[
> \frac{S+1}{2}-a \ge\frac{L+1}{2}-a \ge\frac12.                                       \tag{C2E.3}
> \]
> Thus the domination used in C2Q is valid with the actual side length and is only strengthened when residual siblings share that side.”

**CONDITIONALITY:** **A STRENGTHENING, not a weakening** — pricing by the actual side length `S ≥ L` gives a larger entry codimension, hence a smaller `ρ`. The closing sentence says so, and `.58` confirms “no existing count is weakened”.

**ARITHMETIC AUDIT (compiler-computed):**
* Supporting-line heights on an S-long side of drop H, from the right endpoint: `rH/S` for `r = 1..S` ✓ (the line from (0, H) to (S, 0) has height `H − rH/S` at abscissa r counted from the left, i.e. `rH/S` counted from the right ✓).
* `Σ_{r=1}^{S} rH/S = (H/S)·S(S+1)/2 = (S+1)H/2` ✓ **exact.**
* `Σ(⌈rH/S⌉ − 1) ≥ Σ rH/S − S ≥ (S+1)H/2 − O_m(1)` ✓ (the ceiling error is at most 1 per column, S columns, and S ≤ m ✓ so the error is `O_m(1)` ✓).
* `(S+1)/2 ≥ (L+1)/2` ✓ since `S ≥ L` ✓.
* `L = eμγ ≥ 2eγ = 2a` ✓ (μ ≥ 2) — so `(L+1)/2 − a ≥ (2a+1)/2 − a = 1/2` ✓, and a fortiori `(S+1)/2 − a ≥ 1/2` ✓ **= (C2E.3), exact.**
* **The change from `.42`'s (C2.2):** `b = (L+1)/2` → `b_S = (S+1)/2 ≥ b` ✓, i.e. **a uniformly better bound** ✓.
* **Compiler verdict: (C2E.1)–(C2E.3) all re-derive exactly.**

**SUPERSESSION KIND:** `replacement` (of the entry-pricing display) — a strengthening.

**TARGETS:** `s3of3.42`(iii), `s3of3.47` (MINOR-C's replacement sentence, now with `b_S`).

**DERIVATION:** Displayed.

**RESOLUTION TRACE:** statement lines 3795–3840. correction sites: none.

**TEETH:** NONE. Disposition: `signed vacuity disclosure`; the three quartic checks are unchanged by construction (`.58`), so no measured number tests the strengthening.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:S2.2` — count **19** (the slot count the pricing implements).

---

### EFF.GENIND.s3of3.58  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed bulleted display (the C2-G3 consumer sweep). verbatim, lines 3842–3850.

> “**C2-G3 consumer sweep.**
>
> - In C2.0, retain \(L=e\mu\gamma\) as the composite-block length, but define the actual entry coefficient as \(b_S=(S+1)/2\).
> - Replace the displayed heights \(rH/L\) by \(rH/S\), \(1\le r\le S\).
> - Replace C2.2 by (C2E.2).
> - In the height-domination step use \(b_S-a\ge(L+1)/2-a\ge1/2\).
> - The CS4-E, CS4-F, and CS5-V1E2 checks have \(S=L=4\), so their displayed exponents do not change.
> - Embedded or same-side mixed genres with \(S>L\) receive a strictly stronger entry bound; no existing count is weakened.”

**CONDITIONALITY:** **Five surgical replacements plus two impact statements**, one of which (bullet 5) is the compatibility guarantee for `.43`'s three checks.

**ARITHMETIC AUDIT:** bullet 5's claim `S = L = 4` at CS4-E, CS4-F, CS5-V1E2 — CS4-E: the whole polygon is the side, length 4, and `L = eμγ = 2·2·1 = 4` ✓ so `S = L = 4` ✓. CS4-F: `L = 1·2·2 = 4` ✓ and the side is the whole length-4 polygon ✓. CS5-V1E2: the side is `(1, 2h)–(5, 0)`, length **4** ✓, and `L = 2·2·1 = 4` ✓. **All three have S = L = 4 ✓ — so `b_S = b = 5/2` and the exponents are unchanged ✓, exactly as claimed.**

**SUPERSESSION KIND:** `replacement` ×4 + two non-change declarations.

**TARGETS:** `s3of3.42`(C2.0, the heights display, C2.2, the domination step), `.43` (declared unchanged), `.47`.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 3842–3850. correction sites: none.

**TEETH:** NONE.

---

### EFF.GENIND.s3of3.59  [changes-record]

**CANONICAL STATEMENT:** FORM: italic parenthetical paragraph (the R11 orchestrator-verification record — the note's last words). verbatim, lines 3852–3872.

> “*(The round-2 repairs above were derived by the R11 certification run
> (gpt-5.6-sol high, runs/cert3/R11_genind_output.log, 2026-08-12),
> answering the D2f re-pass's C2-G1/G2/G3; orchestrator verification
> before transcription — C2-G3: the supporting-line sum re-derived
> (Σ_{r≤S} rH/S = (S+1)H/2) and the domination margin
> (S+1)/2 − a ≥ (L+1)/2 − a ≥ 1/2 re-checked, with the three displayed
> checks unchanged at S = L = 4; C2-G2: GENIND-C2D's truncation
> monotonicity verified (a window-T decision certificate decides every
> window-W lift over it, so undecided states project onto undecided
> truncations; constant fibers give δ(W) ≤ δ(T)) and the lexicographic
> measure is now genuinely well-founded (truncate to the uniform core,
> then strict product-degree or window decrease); C2-G1: the C2Q
> exponent algebra re-derived (−γM ≤ −a(N−1−H) + γΔ, then (CS-1Q.b)
> caps γΔ − C_extra − (b_S − a)H by −H/2 + O(1)), the floor-adjacent
> branch re-checked, and the HONEST RESIDUE recorded: the universal
> stage-window transfer for embedded/mixed genres is not discharged —
> the annex-lemma's conditionality is upgraded from "(CS-1) only" to
> "(CS-1Q), verified per genre", with (CS-1Q.b)'s per-genre affine
> ledgers a named obligation. Transcribed unaltered per the standing
> division of labor. Ledger: row 17 → round-2 repairs folded; awaiting
> a clean re-pass + the (CS-1Q) per-genre ledger obligation.)*”

**CONDITIONALITY:** **The note's closing state, and it is an open one:** “awaiting a clean re-pass + the (CS-1Q) per-genre ledger obligation.” **Nothing after line 3872 exists** — this is the last text in the note.

**ARITHMETIC AUDIT:** the orchestrator's four enumerated re-derivations are **exactly the ones this compiler performed independently at `.57`, `.54`, `.55`, `.51`** — the supporting-line sum, the domination margin, C2D's monotonicity, the C2Q exponent algebra and the floor-adjacent branch — **and all agree.** Unlike R9's record (`.48`), **no item this record verifies has since been refuted**; the note's arc ends with its last verification standing.

**SUPERSESSION KIND:** none of its own.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 3852–3872. correction sites: **none — this is the note's terminal text.**

**TEETH:** `in-house hostile pass` (the orchestrator's pre-transcription check) + the standing division-of-labour disclosure. **PIN VERIFICATION:** `runs/cert3/R11_genind_output.log` EXISTS ✓. Ledger cross-reference: “row 17” — the GENIND drain row of the certification ledger, distinct from `spec/HYPOTHESIS_LEDGER.md`'s HYP numbering; **not resolved here** (recorded, §8 defect 5).

---
## 3. Consumption tables

### 3.1 Verified import/XREF designations

`[TABLE — compiler ledger]` Counts are `grep -cF '<designation>' <file>` at HEAD. **19 distinct designations across six supplier notes, all count ≥ 1** — far fewer than shards 1–2, because the annex stack is overwhelmingly self-referential (it repairs GENIND's own text and cites GENIND's own lemmas).

| # | Target : designation | Count | Role in this shard |
|---|---|---|---|
| 1 | `W12_PROOF_2026-08-08.md:S2.2` | 19 | The slot count behind the entry pricing (`.05`, `.08`, `.10`, `.42`, `.57`) |
| 2 | `W12_PROOF_2026-08-08.md:W12-S2.1` | 9 | The monic-factor Hensel form behind the unit-pivot species (`.10`) |
| 3 | `W12_PROOF_2026-08-08.md:W12-L1` | 30 | Letter units in the pivot species (`.10`) |
| 4 | `W12_PROOF_2026-08-08.md:THEOREM W-12.A` | 8 | The order-1 entry-law pricing cited by C2(iii) (`.33`) |
| 5 | `W12_PROOF_2026-08-08.md:QRT-G2` | 10 | The 4-key stage of the sufficiency construction (`.19`) |
| 6 | `W12_PROOF_2026-08-08.md:S2.5` | 9 | The pinned committed law for the m = 4 instance (`.20`) |
| 7 | `W12_PROOF_2026-08-08.md:W12-BOX-1` | 10 | The box family R1.0's sharpening addresses (`.02`) |
| 8 | `HEX3_PROOF_2026-08-08.md:THEOREM HEX3.A` | 11 | The R(M) tie and the n = 3 exact law (`.03`, `.07`) |
| 9 | `HEX3_PROOF_2026-08-08.md:THEOREM HEX3.B` | 8 | The n = 3 rate — the species instance (`.03`, `.04`, `.07`) |
| 10 | `HEX3_PROOF_2026-08-08.md:R(M)` | 21 | The letter-for-letter identity of `.03`'s closed form (`.03`, `.07`) |
| 11 | `W11_PROOF_2026-08-08.md:THEOREM W-11` | 3 | The supply consumed inside HEX3.A's R(M) (`.03`) |
| 12 | `JD0_PROOF_2026-08-08.md:J-D0` | 25 | Letter-blindness in the pivot species (`.10`) |
| 13 | `GRTJC_PROOF_2026-08-08.md:COROLLARY W-9` | 2 | `dim_K 𝒜(T) = E`, the stage slot geometry (CS-1) asserts (`.33`) |
| 14 | `GRTJC_PROOF_2026-08-08.md:JC-F1` | 18 | Same (`.33`) |
| 15 | `GRTJC_PROOF_2026-08-08.md:dim_K 𝒜(T) = E` | 3 | Same, verbatim (`.33`) |
| 16 | `GENHN_PROOF_2026-08-08.md:GENHN.A(iv)` | 3 | Screened at `.28` |
| 17 | `GENHN_PROOF_2026-08-08.md:GENHN.A(v)` | 6 | Screened at `.26`, `.28` |
| 18 | `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-3` | 3 | Screened at `.26`, `.28` |
| 19 | `GENHN_PROOF_2026-08-08.md:S6.2` | 6 | Screened at `.28` |

Additional GENHN designations verified in the screening units: `S11.F` (10, `.28`, `.50`), `S6.3` (3, `.28`), `GENHN.A(i)` (11, `.26`), `GENHN-TOW-1` (19, `.27`, `.29`), `GENHN.C` (19, `.29`), `LEMMA GENHN-T(b)` (11, `.27`) — **six more, all ≥ 1**, bringing the shard total to **25 distinct verified designations**. GENH4 designations verified at `.35`: `GENH4-1F` (10), `GENH4-2` (15) — **27 total.**

### 3.2 Pin verification (rule 23)

**Commit hashes cited and `git cat-file -t`-verified — all resolve as `commit`:** `f5271e4`, `a1525ea`, `bc1b996`, `961d0ff`, `46bf675`, `58b1080`, `d16869c`, `7650b20`, `438608a`, `9636b7e`, `850e77e`, `4b0d946` — **12/12 ✓.**

**8-hex prefixes cited inside the ANNEX R close's own enumeration and NOT independently re-verified here:** `a1525ea2` (= the 7-prefix `a1525ea` ✓), `31c6723d`, `98ac7bb0`, `fe0ed6c0`. Recorded at §8 defect 2 — the enumeration is the note's own and is internally consistent, but three of the five annex commits are cited only there.

**Artifacts verified to EXIST on disk:**
`verification/openmath/genind_annexr_supp.py` ✓ · `genind_annexr_supp_output.txt` ✓ · `genind_annexr1_checks.py` ✓ · `genind_annexr1_output.txt` ✓ · `genind_annexr1_results.json` ✓ · `genind_checks.py` ✓ · `genh4_checks.py` ✓ · `genh4_checks_results.json` ✓ — **8/8.**
`lean/notes/openmath/CODEX_GENINDRAT_2026-08-09.md` ✓ · `lean/notes/openmath/GENIND_ANNEXR_pass_report.md` ✓ — **2/2.**
`runs/residues/R1_drainn4_output.log` ✓ · `runs/cert/R9_drain_repair_output.log` ✓ · `runs/cert3/R11_genind_output.log` ✓ — **3/3 run logs.**

**Non-commit hashes (md5s), correctly not treated as pins:** `eefcf658`, `14fa6afc`, `e7ca150b`, `42fd603e`, `d938ad82`, `ee8024b7`, `cbcff562`.

### 3.3 NEAR-MISS dispositions (rule 15)

| # | As cited (unit) | Count | Verified referent | Disposition |
|---|---|---|---|---|
| 1 | `[GENHN-HE(μ ≥ 3)]` (`.29`) | 0 in GENHN | Fixed by the note's own PE7-m3 (shard 2 `.71`), which `.29` cites explicitly (“read per PE7-m3”) | Carried with the note's own correction |
| 2 | `S5.1`, `S5.2`, `S5.3`, `S7.1`, `S7.3`, `S2.2` as §-pointers inside GENIND itself | n/a | **Self-references, not external designations** — resolved to shard-1 unit IDs throughout this compilation | Not emitted as XREFs |
| 3 | “row 17” (`.48`, `.59`) | n/a | A row of the **certification ledger**, not of `spec/HYPOTHESIS_LEDGER.md`; the target file is not named in the note | Carried descriptively; source defect 5 |

### 3.4 Reverse consumer edges

`[TABLE — compiler ledger]`

| Direction | Party | What crosses | Protocol status |
|---|---|---|---|
| **Inbound** | Codex ratification (gpt-5.6-sol HIGH, fresh context, read-only) | 6 findings, outcome CHALLENGE; 3 GAPs | Repaired here by R1–R6; **no supplier note edited** |
| **Inbound** | the annex stack's own scoped hostile pass | 0C + 1 GAP + 2 MINOR | Repaired here by r1.1–r1.3 |
| **Inbound** | sol certification R9 | the d-factor GAP + 3 riding MINORs | Repaired here; **derived by sol, transcribed unaltered, orchestrator-verified before transcription** (`.48`) |
| **Inbound** | sol certification R11 (the D2f re-pass) | C2-G1 / C2-G2 / C2-G3 | Repaired here (`.49`–`.59`); same division of labour (`.59`) |
| **Inbound** | GENHN's own arc | errata E1–E3 executed + r2 (a REFUTED lemma, T(b), withdrawn and replaced by T(b)′ behind box [GENHN-TOW-1]) | Screened clause by clause at `.28`; **conditionality moved at n ≥ 8** (`.29`) |
| **Outbound** | the PE8 acceptance report | a notice that its §4.1 rationale is false | **The report is NOT edited** — “its author's artifact per the standing rule; the notice lives here and at the ledger” (`.22`) |
| **Outbound** | every supplier | **nothing** | No append claimed landed on any supplier by this stack |

---

## 4. NON-IMPORTS

`[TABLE — compiler ledger]`

| Fence | Explicit material NOT claimed / NOT discharged | Unit |
|---|---|---|
| The annex's grade | “the annex has NOT itself been through a hostile pass” (stale as of r1, uncured) | `.25` |
| The annex stack's grade | “The annex stack remains 0/2” | `.31`, `.39` |
| Acceptance scope | “The 2/2 acceptance attaches to the frozen body” | `.25` |
| No verifier prose | “no verifier sentence is transcribed” (r1) / “Transcribed unaltered per the standing division of labor” (R9, R11) | `.31`, `.48`, `.59` |
| No new hypothesis (claimed, then withdrawn) | “with no new hypothesis” (`.35`) → **overturned**: “conditional on (CS-1Q), verified per genre” | `.35`, `.52` |
| Per-genre ledgers compressed | “the per-genre ledgers remain compressed per the S4.3 honesty box, and the multi-block hostile targets it names stay named” | `.11` |
| Stage-level converse unclaimed | “The STAGE-level parse … is NOT claimed by this note … at general m the stage-level statement is left unclaimed” | `.19` |
| No (CS-EXACT) in the rate | “No use of (CS-EXACT) is made: this is a bound, not the exact-complement identity” | `.42`, `.23` |
| No (CS-2)/(CS-3) | “It consumes neither (CS-2), (CS-3), nor (CS-EXACT)” | `.44` |
| **The universal discharge** | **“A universal discharge for embedded and mixed genres remains obstructed until those affine ledgers are displayed and checked”** | `.52` |
| No general embedded/mixed discharge | “No general embedded/mixed discharge is asserted by this append” | `.53` |
| No upper bound on the ragged window | “No new upper bound on the original ragged stage window is claimed or needed” | `.56` |
| No count weakened | “no existing count is weakened”; “No accepted theorem statement is weakened; no count law or frozen number moves” | `.58`, `.41` |
| Report untouched | “the report itself stays untouched — its author's artifact” | `.22` |
| Open at the close | “awaiting a clean re-pass + the (CS-1Q) per-genre ledger obligation” | `.59` |

---

## 5. Teeth inverse table

`[TABLE — compiler ledger]`

| Instrument / audit row | Guarded unit(s) | Disposition |
|---|---|---|
| **`genind_annexr_supp.py` leg A** — the m = 2 closed forms solve the recursion symbolically at N = 2..14 | `.03` | Executable regression (symbolic) |
| **leg B** — the closed forms equal the committed `R(M)` at M = 1..14 | `.03`, `.04` | **`accepted-with-decorrelation-supplied`** — the tie is to a committed SUPPLIER display |
| **leg C** — `u(N) ≤ N·Q^{N−1}` at N = 2..14, Q ∈ {2,3,4,5,8,9} | `.03`, `.04` | Executable regression |
| **leg D** — the depth identity `D+M = N` at six committed extractions (M6, TWOCHILD A/B, PSTEEP3, PSTEEP4, SS6) | `.05`(iii) | Executable regression; **a definitional identity checked against hull data** |
| **leg E** — the prefactor bound at three committed loci (M6, PSTEEP3, PSTEEP4) | `.05`(i) | Executable regression; **all three re-derived by this compiler and exact** |
| **leg F** — monotonicity `∂G/∂u_i ≥ 0` and union-bound dominance, symbolic at r = 2, 3 | `.05`(ii), `.22`, `.23` | Executable regression **+ preregistered decorrelation** (“two decorrelated models, same kill”) |
| **leg G** — the unit-pivot toy over ℤ/4: `(x+2)y` collapses, `(1+2x)y` does not | `.09`, `.10`, `.11` | **Planted mutant, fired**; realizes the finding's counterexample |
| **leg H** — the two CS4-F gate lines read verbatim in the md5-pinned runner; (2,2,1) gated to 0; (2,5,1) = 64 | `.16`, `.17` | **Source-code gate verification** — an executable regression against the instrument's TEXT |
| **leg I** — window-1 at (m, Q) ∈ {2,3,4}² : 1 state, DRAIN, u(1) = 1 | `.13`, `.14` | Executable regression **+ a decorrelated sympy re-solve** |
| **`genind_annexr1_checks.py` P1** — the window bound at 11 scored fresh rows | `.33`, `.34`, `.36`, `.38` | Executable regression, GREEN 11/0 |
| **P2** — the species bound at (K,B,c) = (1,1,2), margins 10²–10⁴ | `.33`, `.38` | Executable regression, GREEN 9/0 |
| **P3** — consecutive-N slope, 6-of-7 | `.33`, `.38` | Executable regression **with one FLAGGED line and an open adjudication** (`disclosed non-repair`); genre E measured at exactly 2.00 |
| **P4** — the CS5-V1E2 entry identity + composed n = 5 bound, sympy + grid to N = 40 | `.34`, `.38` | Executable regression, GREEN 112/0 |
| **P5** — the `D+M = N` composition identity, sympy | `.05`(iii), `.38` | Executable regression, GREEN 1/0 |
| **T-SLOPE** — a fabricated slope-1/2 n = 4 E-drain (262,144) violates the P1 bound (65,536) | `.33`, `.38` | **Planted mutant, fired**; the pass report's failure scenario made flesh |
| **T-WIN** — the mis-derived window `2N−2−2h` refuted by the committed deep row (Zp,2,11,h=5) | `.33`, `.36`, `.38` | **Planted mutant, fired** |
| **the PINNED GENH4 walker's own live checks** — GH-FRESH, GH-UND, GH-BRACKET, silent at all 12 rows | `.38` | Foreign-note (supplier-instrument) evidence, run live as a silent guard |
| **orchestrator pre-transcription verification (R9)** | `.42`, `.43`, `.45`, `.46`, `.47`, `.48` | **AUDIT: `in-house hostile pass`** — **with a disclosed miss** (it passed the descent step R11 later refuted) |
| **orchestrator pre-transcription verification (R11)** | `.51`, `.54`, `.55`, `.57`, `.59` | **AUDIT: `in-house hostile pass`** — no item since refuted |
| **the diff-granularity GENHN screen** (seven sites) | `.26`, `.27`, `.28` | **AUDIT: `transfer audit`** at diff granularity |
| **this compiler's arithmetic audits** | `.03`, `.05`, `.13`, `.34`, `.42`, `.43`, `.47`, `.51`, `.54`, `.55`, `.57`, `.58` | **AUDIT: `arithmetic recount`** — twelve units re-derived independently; **all agree with the source** |

**PROOF-ONLY rows (rule 16)** — the note's own coverage sentence for each:

| Unit | Coverage sentence |
|---|---|
| `.06` (GENIND.C′) | no machine leg for the induction; only the ground instance is tested |
| `.10` (the pivot species) | “the per-genre ledgers remain compressed per the S4.3 honesty box” (`.11`) |
| `.42` (the Q-normalized C2) | **untested — the r1 leg predates it** (OPEN-CALL 2) |
| `.50`, `.51`, `.54`, `.55`, `.57` (the whole R11 layer) | **no machine leg was added at R11**; “A universal discharge … remains obstructed” (`.52`) |

**Both-direction audit.** Every instrument row above guards at least one unit; every unit whose TEETH field names a leg appears in some row. **`TEETH: NONE`** units — `.01`, `.02`, `.07`, `.08`, `.12`, `.15`, `.18`, `.19` (audit only), `.21`, `.25`, `.26`, `.27`, `.29`, `.30`, `.31`, `.32`, `.35`, `.37`, `.39`, `.40`, `.41`, `.44`, `.45`, `.46`, `.47`, `.48`, `.49`, `.50`, `.51`, `.52`, `.53`, `.54`, `.55`, `.56`, `.57`, `.58`, `.59` — are findings, riders, fences, install records, or **proved-but-unexercised lemmas**. **Zero instrument-row orphans.**

**Signed vacuity disclosures, enumerated** (rule 20): `.29` (n ≥ 8 conditionality, nothing reaches degree 8), `.42` (the Q-normalized lemma, untested), `.50` (**(CS-1Q), per-genre unverified — the shard's headline disclosure**), `.51`, `.54`, `.55`, `.57` (the whole R11 layer, proved and unexercised), `.20` (R5's verification is a consumer walk, no leg). **`stale self-description (uncured)`** (rule 26): `.25` (“has NOT itself been through a hostile pass”), `.35` and `.44` (“(CS-1) only” / “no new hypothesis”), `.39` (“conditional on (CS-1) only”).

**The single most important row in this table is an ABSENCE:** the R11 layer — five units of new mathematics (`.50`, `.51`, `.54`, `.55`, `.57`) — carries **no machine leg at all**, and the layer it repairs carries one that was run against a superseded version. Every arithmetic check on it in this spec is this compiler's own.

---
## 6. BOUNDARY SELF-AUDIT (mixed prose-annex / tagged-display genre, template rule 9)

**This shard is the easiest of the three to bound, and the reason is instructive.** Above line 3298 the source carries explicit numbered sub-headings (`R1.0`, `R1.1`, `R1.2`, `R1.3`, `R1.4`, `R2.0`…`R6.3`, `r1.1`, `r1.2/r1.3`) — the author's own boundary markers. Below line 3298 it carries **LaTeX `\tag{}` anchors** (`C2.0`…`C2.4`, `CS-1Q.a`, `CS-1Q.b`, `C2Q.1`, `C2Q.2`, `C2D.1`, `C2E.1`…`C2E.3`) — machine-readable addressable objects. **So the boundary problem shard 1 and shard 2 had to solve by test was largely pre-solved here by the source.** §6.1 records the calls that remained.

### 6.0 The rule applied

> **A unit is the smallest span carrying one complete claim together with its proof obligations.**

The same four-part test, plus the fifth (series membership). Two genre-specific observations:
* **A numbered sub-heading is presumptive evidence of a unit, not proof of one.** `R1.2` and `R1.3` are lemma/theorem sections and split cleanly; `r1.2 and r1.3` share one paragraph and are emitted as ONE unit (`.37`) because the source itself merges them under a joint heading.
* **A `\tag{}` is an addressable object but usually NOT a unit.** `C2.0`–`C2.4` are steps of one proof and live inside `.42`; `CS-1Q.a`/`CS-1Q.b` ARE a unit (`.50`), because they are a *hypothesis family* cited by name from four other places and carried as a ledger row.

### 6.1 Boundaries drawn, with the arguable ones recorded both ways

**1. R1 split into six units (`.02`–`.07`) along its own sub-headings.** Test 1 and 3: R1.0 is a finding, R1.1 a proved lemma + a hypothesis pin, R1.2 an annex-lemma, R1.3 an annex-theorem, R1.4 an install record — five different kinds. *Arguable:* whether R1.1's derivation (`.03`) and its species pin (`.04`) are one unit, since the source presents them under one heading. **Chosen split** on test 3, decisively: `.03` is untouched by every later layer while `.04` is riddered by `[ar1]`, then by R9, then by R11. Folding them would attach three supersessions to a derivation that none of them touches.

**2. R2–R6 each split into finding / rider / (supply) / verification.** Test 1 and 4: a quoted finding, an instruction, a proof and a machine result have four different truth conditions. **This produces the shard's most uniform structure** and makes the six Codex findings individually addressable, which the merge needs (they are cited as F1…F6 from the fold note and from `.01`).

**3. `.33` emitted although SUPERSEDED IN FULL.** **Genuinely arguable, and the shard's most consequential inclusion.** *Candidate A:* drop it — R9 replaces statement, proof, instances and conditionality, so nothing in it is live. *Candidate B (chosen):* emit it, marked superseded. **Reason: the r1 machine leg (`.36`, `.38`) was PREREGISTERED AND RUN AGAINST THIS VERSION.** Without `.33` the spec would carry a run-record whose object does not exist, and a chapter cut would silently attribute the leg's GREEN to the Q-normalized lemma — which it never tested. *Cost:* one long superseded unit. **This is the clearest case in the three shards where a dead statement must be kept alive in the spec because an instrument is pinned to it.**

**4. `.50` ((CS-1Q.a–b)) split out of C2-G1's prose.** Test 2, decisively: the two clauses are cited by tag from `.51`'s proof, from `.52`'s certification status, from `.53`'s sweep, and **from `spec/HYPOTHESIS_LEDGER.md` row HYP.36**. A hypothesis family with an external ledger row is addressable by definition. *Candidate A:* one C2-G1 unit. **Rejected** — the ledger row's `WHERE` field cites `§C2-G1 L3592–3722`, i.e. the whole section, but its `STATEMENT` field quotes only the two clauses.

**5. C2-G1/G2/G3 each split into content + consumer sweep (`.50`/`.51`/`.52`+`.53`, `.54`/`.55`+`.56`, `.57`+`.58`).** Test 4: a sweep is an *instruction to re-read frozen text elsewhere* (rule 24's bivalent shape) and carries a `TARGETS` list; the content is mathematics. Folding them would bury three `TARGETS` lists inside three lemmas.

**6. `.52` (Certification status) split out of C2-G1.** **The most consequential small split in the shard.** *Candidate A:* a closing paragraph of `.50`. *Candidate B (chosen):* its own `[fence]` unit. **Reason:** it is the sentence that (i) creates ledger row HYP.36's CARRY disposition, (ii) supersedes the conditionality label at seven units across three shards, and (iii) states the obstruction. A fence that reaches three shards must be addressable.

**7. The two orchestrator-verification parentheticals emitted as units (`.48`, `.59`).** Test 1 and 4: each is a checkable claim (a list of re-derivations) with a provenance disclosure and a ledger pointer. **And `.48`'s list contains an item R11 later refuted**, which is only recordable if the parenthetical is a unit. *Candidate A:* provenance footnotes, not units. **Rejected on exactly that ground.**

**8. The supplier-movement record split into five (`.26`–`.30`).** Test 3 and 4: an owed-disclosure discharge, a supplier's refuted lemma, a seven-site screen, a conditionality movement and a pin record are five different claims with five different consumers. **`.29` in particular must be addressable: it is the unit that changes the capstone's hypothesis block at n ≥ 8.**

**9. Proofs NOT emitted as units.** `.03`'s telescope, `.05`'s four clauses' arguments, `.06`'s lexicographic induction, `.42`'s four-part proof, `.51`'s exponent algebra, `.54`'s truncation argument, `.57`'s supporting-line sum — all carried in DERIVATION. **Here, unlike shards 1–2, statement and proof are adjacent in every case** (the annex writes lemma-then-proof), so rule 12's three-slot trace mostly collapses to two.

### 6.2 Merges deliberately NOT made

- **`.42` and `.51` are not merged** even though C2Q supersedes C2's mechanics: `.42` retains the Q-normalization and the height-sum architecture that `.51` reuses, and R11 supersedes only three named parts.
- **`.02`, `.08`, `.12`, `.15`, `.18`, `.21` (the six quoted findings) are not merged into one “Codex findings” unit**: each is separately dispositioned (3 GAP, 3 regraded MINOR), separately repaired, and separately cited.
- **`.13` and `.14` stay separate** (R3's rider and its verification): the rider is a convention extension consumed at six sites; the verification is a nine-cell run.
- **`.45`, `.46`, `.47` (the three riding folds) stay separate**: three different kinds (`wording-rider`, `inventory completion`, `replacement`) with three different targets.
- **`.54` and `.55` stay separate**: C2D is a reusable lemma; the lexicographic measure is its application to the descent.

### 6.3 Format feedback (v3 rules under load; the third and last GENIND shard)

1. **Rule 18 needs two sub-kinds this shard forced.** (a) **`replacement` with WITHDRAWAL** (`.49`: “The scalar bound … is withdrawn”) — a previously available input becomes unavailable, which is materially different from substituting one display for another; a merge that misses it will keep consuming the withdrawn bound. (b) **`replacement` with DELETION** (`.56`: “Delete ‘H>0, hence M★<N’ from C2(ii)”) — the deleted sentence remains byte-intact at line 3382 and is readable as live text unless the edge is installed. **Recommend `withdrawal` and `deletion` as marked sub-kinds.**
2. **Rule 13's `supplier-finding` needs a mirror for findings against the note's OWN frozen text and against verifier artifacts.** This shard has six of the first (`.02`, `.08`, `.12`, `.15`, `.18`, `.32`) and one of the second (`.21`/`.22`, against the PE8 acceptance report). Filed as `supplier-finding` and `changes-record`. **Recommend `self-finding` and `artifact-finding`**, since their protocol differs: a self-finding is repaired in place or by append; an artifact-finding may only be *noticed*, never repaired.
3. **The consumer-sweep format needs a status ruling (OPEN-CALL 1).** Three sweeps (`.53`, `.56`, `.58`) issue imperative instructions reaching into frozen text they do not quote. They are the most efficient supersession vehicle in the corpus and the least auditable: a merge can only install their edges by *interpreting* “In GENIND.B Step 4 …”. **This compilation resolved all fourteen sweep bullets to unit IDs by hand; a format rule should require the source to do it.**
4. **Rule 22's arithmetic audit was decisive here and found ONE real defect and ONE non-reconciliation.** Reconciled: `.03`'s entire derivation (telescope, both closed forms, the unified form, both bases, the rate); `.05`'s four clauses and three machine instances; `.13`'s six window-1 clauses; `.34`'s three compositions; `.36`'s roster arithmetic (which **independently confirms MINOR-A**); `.38`'s check tally 144 = 4+11+9+7+112+1 and both teeth; `.42`'s five tagged displays; `.43`'s three checks; `.47`; `.51`'s exponent algebra including the floor-adjacent branch; `.54`'s cardinality argument; `.55`'s lexicographic descent; `.57`'s (C2E.1)–(C2E.3); `.58`'s S = L = 4 claim. **Real defect confirmed by independent recount: `.33`'s base-q conclusion against a Q-normalization** (the R9 finding). **Non-reconciliation: `.38`'s two adjudication supports (2.00/step paired versus 3.00 per-stratum paired) are not reconciled by the note and cannot be from the displayed data.**
5. **Rule 25's CHAIN is at its longest here and needs per-consumer terminals** — the recommendation shard 1 made independently. The CS-drain chain runs **five layers**: `.33` → `.42` → `.51`, with `.04`'s closure and `.35`/`.44`'s conditionality riding alongside, and its TERMINAL differs by consumer (`.06` for the simple part, `.51`+`.50` for the CS part).
6. **Rule 19's `preregistration`/`run-record` split earned its place twice**, and the second time it exposed something: `.36` is a preregistration whose numeral was corrected *after* the run (`.45`) — legitimately, because the correction aligned the preregistration with the roster and the committed record rather than with the outcome. **A merge that folded `.36` into `.38` could not have shown that.**
7. **The shard's structural finding, for the DAG.** **Every one of the four correction layers in this stack was triggered by a DECORRELATED model, and each found a real defect in the layer before it.** ACCEPTED-2/2 body → Codex finds 3 GAPs → the annex's own pass finds a GAP in the GAP-repair → sol R9 finds a d-factor GAP in that repair → sol R11 finds three defects in R9's repair, one of them an invalid inference (`M★ < N` from a lower bound) that the R9 orchestrator's own verification had passed. **Five levels deep, and the last one is still open** (“awaiting a clean re-pass”). For a merged spec this is not a curiosity: it is the calibration datum for how much weight a single clean pass can bear.

---

## 7. SHARD NOTES

- **Cross-shard supersessions ISSUED by this range (this shard is the corpus's supersession source; the edges point OUT).**
  → **shard 1 `.11`**: R4 (CS4-F floor at GENIND.A(IV)'s clause), R5 (the converse pinned to degree level).
  → **shard 1 `.13`, `.45`, `.46`, `.57`**: R1's (A2-RATE) + GENIND-C1 + GENIND.C′; R1.4's install instruction.
  → **shard 1 `.14`, `.58`**: R6.2's identity-vs-bound separation.
  → **shard 1 `.24`, `.36`**: R2's unit-pivot license (two named sites).
  → **shard 1 `.07`, `.21`, `.24`, `.34`, `.38`, `.45`**: R3's window-1 convention (six enumerated sites).
  → **shard 1 `.49`**: R4's floor at the S5.3 display.
  → **shard 1 `.15`, `.04`, `.61`**: the n ≥ 8 conditionality movement (`.29`).
  → **shard 1 `.34`, `.57`**: PE7-m2's seven-site GENHN inventory, screened at `.28`.
  → **shard 1 `.37`, `.57`, `.63`**: the (CS-1) → (CS-1Q) upgrade (`.52`, `.53`).
  → **shard 2 `.04`**: R1.0/R1.4's split of GENIND-BOX-4.
  → **shard 2 `.17`, `.62` row 6**: the owed-disclosure discharge (`.26`).
  → **shard 2 `.72`**: R6.1's notice against the PE8 acceptance report.
- **Range-edge audit.** Line 2551 is blank; line 2552 opens `## ANNEX R`; **line 3872 is the note's last line** (the closing `)*` of `.59`'s parenthetical). **No source statement unit is cut at either edge**; the lower edge is the pre-annex byte-freeze boundary (md5 `eefcf658` covers 1–2548, and 2549–2551 are the `---` separator and blanks), and the upper edge is EOF.
- **Outside-HOME material used only as resolver:** lines 1–1348 (shard 1's mathematics) and 1349–2551 (shard 2's records).
- **Protocol.** No consumption append is claimed landed on any supplier; one notice is filed against a verifier artifact WITHOUT editing it.
- **Numbering.** Temporary IDs `EFF.GENIND.s3of3.01`–`.59`.
- **MERGE HAZARDS TO FLAG (seven).**
  1. **`.33` is SUPERSEDED IN FULL but must be kept**, because the r1 machine leg (`.36`, `.38`) is pinned to it. **Do not attribute that leg's GREEN to `.42` or `.51`.**
  2. **The CS-drain chain has FIVE layers and TWO terminals** (`.06` for the simple part; `.51` under `.50`'s (CS-1Q) for the CS part). A single-terminal edge will misstate one of them.
  3. **`.52` is the terminal conditionality for SEVEN units across three shards.** Install every edge: shard 1 `.13`, `.37`, `.57`, `.63`; here `.04`, `.05`, `.35`, `.39`, `.44`.
  4. **`.50` IS ledger row HYP.36** (`spec/HYPOTHESIS_LEDGER.md:310–315`, `WHERE: §C2-G1 L3592–3722`, disposition **CARRY**). A chapter cut carrying the CS-drain rate must carry HYP.36 with it.
  5. **`.29` changes the capstone's hypothesis block at n ≥ 8** from one family to three. Shard 1 `.04`'s headline (“exactly ONE displayed hypothesis family”) is true only at n ≤ 7.
  6. **Three consumer sweeps (`.53`, `.56`, `.58`) reach into frozen text without quoting it.** Their fourteen bullets are resolved to unit IDs in this compilation's `TARGETS` fields; a merge must install those edges rather than re-interpret the imperatives (OPEN-CALL 1).
  7. **The whole R11 layer (`.50`, `.51`, `.54`, `.55`, `.57`) has NO machine leg.** Every arithmetic check on it in this spec is the compiler's own, and all of them pass; but no instrument has exercised it, and the note's own last words are “awaiting a clean re-pass”.

---

## 8. Self-audit and OPEN-CALLS

### OPEN-CALL 1 — the consumer-sweep format has no ruling, and it is this shard's dominant supersession vehicle

`.53`, `.56` and `.58` issue **fourteen imperative bullets** of the form “In X, replace Y by Z”, “Delete W from V”, reaching into text in all three shards — including the byte-frozen body (GENIND.B Step 4; GENIND-6(d)) — **without quoting the target sentences.** Two of them are unusually strong: `.49` **withdraws** an input and `.56` **deletes** a clause that remains byte-intact at line 3382. This compilation resolved all fourteen to unit IDs by hand and recorded them in `TARGETS` fields. **Decision needed: whether the merged spec treats a consumer-sweep bullet as a first-class supersession (installing the edge) or as a downstream reading note (recording it without an edge) — and whether the format should require sweeps to quote their targets.** Raised identically at shard 2 OPEN-CALL 2; recorded at both ends because the evidence is split.

### OPEN-CALL 2 — the Q-normalized lemma and the entire R11 layer are unexercised, and the one machine leg is pinned to a superseded statement

The r1 leg (`.36`, `.38`) was preregistered and run against `.33`. R9 then replaced `.33` in full (`.42`) and R11 replaced three of its parts (`.49`–`.58`). **No machine leg was added at either R9 or R11.** So: (i) the Q-normalization — the entire point of R9, and the only part that bites at `d ≥ 2` — is **untested**; (ii) C2Q, C2D, the lexicographic descent and the actual-side-length pricing are **proved and unexercised**; (iii) the r1 leg's GREEN attaches to a statement no longer in force. **The compiler has re-derived every step of (i) and (ii) by hand and they all check** (§5's last row), but hand-checking is not an instrument. **Decision needed: whether the merged spec requires a machine leg for the R11 layer before it enters a chapter cut, and whether `.38`'s GREEN may be cited at all in support of `.42`/`.51`.**

### OPEN-CALL 3 — `.38`'s flagged-line adjudication is supported by two figures that do not agree

The one non-GREEN check in the r1 leg (P3, genre F, N 7→8) is adjudicated “an INSTRUMENT CAP LITERAL, not a counter-instance” on three supports: (a) the next step measures slope 3.00; (b) the parity-paired run data give slope **2.00 per step** over N = 7→9; (c) the committed und_F law gives “per-stratum paired slope **3.00**”. **(b) and (c) do not agree**, and the note does not reconcile them; the compiler cannot from the displayed data (they may describe a run-level relative mass and a per-stratum law respectively). **The load-bearing fact is undisturbed** — no BOUND check (P1/P2) fails at any of the 12 rows, and the lemma's claim is slope ≥ 2, which both figures exceed or meet. **Decision needed: whether the merged spec carries the adjudication as settled, or flags the (b)/(c) discrepancy as an owed reconciliation.**

### OPEN-CALL 4 — the annex stack's grade may be stale against the repo

`.39` closes “The annex stack remains 0/2 — this r1 answers the ANNEX R pass and queues for its own scoped hostile pass behind the chain notes.” **A second report, `lean/notes/openmath/GENIND_ANNEXR_pass2_report.md`, EXISTS on disk and is cited nowhere in the note.** The note is frozen at 2026-08-12 and cannot know its own successor. **Decision needed: whether the merged spec reads the annex-stack grade from the note (0/2) or from the repo (pass #2's verdict, unread here), and whether GENIND owes a dated append recording it.** **This compilation does not adjudicate it and has not read pass #2.**

### OPEN-CALL 5 — “Ledger: row 17” names a ledger this shard cannot resolve

`.48` and `.59` both close with “Ledger: row 17 → …”. **Row 17 is not a row of `spec/HYPOTHESIS_LEDGER.md`** (whose rows are `HYP.nn`); it is a row of the certification campaign's own ledger, and **the note never names that file.** The two references are the only place the annex stack records its own status outside itself. **Decision needed: whether the merged spec must resolve “row 17” to a named file+row before the CS-drain material enters a chapter cut.**

### Recorded source defects (flagged, not silently repaired)

1. *(Withdrawn on recount.)* An earlier pass of this compilation flagged `.03`'s telescope sketch as non-reconstructible. **On careful re-derivation it IS reconstructible** (`S(N) = (Q−1)Q·u(N−2) + Q·S(N−2)`, with the index ranges matching), and the audit at `.03` now records the full derivation. **No defect; recorded here because the flag was raised and retracted, and the retraction is part of the audit trail.**
2. **`.25`: three of the five annex commits are cited only inside the note's own enumeration.** `31c6723d`, `98ac7bb0`, `fe0ed6c0` are 8-hex prefixes appearing nowhere else; `a1525ea2`/`a1525ea` and `f5271e4` resolve ✓. Recorded as an unverified-pin subset, not as an error.
3. **`.31`/`.39`: a second annex-stack pass report exists and is uncited** — OPEN-CALL 4.
4. **`.38`: the flagged line's adjudication carries two unreconciled slope figures** — OPEN-CALL 3.
5. **`.48`/`.59`: “row 17” names an unspecified ledger** — OPEN-CALL 5.
6. **`.36`: a one-word transcription slip in this spec's own quotation was caught and corrected in place** (the source reads “(floor-adjacent, P2 only)”, not “(schedule: floor-adjacent, P2 only)”). Flagged at the unit rather than silently fixed, per the fidelity rules. **This is a compiler defect, not a source defect, and is recorded here for completeness.**

### Fidelity audit

- Every CANONICAL STATEMENT is a verbatim source quotation or explicitly `[ASSEMBLED]`. **No exponent, inequality direction, quantifier, tag label, base (q versus Q), or constant was altered anywhere.** The LaTeX displays are reproduced with their `\[ … \]` delimiters and every `\tag{}` intact; the only compression is of line breaks inside multi-line `aligned` environments, flagged at `.42`.
- Truncations inside quotations: **none.** One quotation slip in this spec was caught and corrected in place, and disclosed (`.36`, defect 6).
- **27 external XREF designations, all grep-verified with count ≥ 1** (§3.1). **12 commit pins verified, 12/12 resolve; 13 artifacts and reports verified to exist, 13/13 present** (§3.2). Three 8-hex prefixes are recorded as an unverified subset (defect 2).
- **Twelve units carry full compiler-computed arithmetic audits, re-deriving every displayed step**: `.03` (the whole R1.1 derivation), `.05`, `.13`, `.34`, `.36`, `.38`, `.42`, `.43`, `.47`, `.51`, `.54`, `.55`, `.57`, `.58`. **All agree with the source.** One independent recount CONFIRMS a finding (the d-factor defect at `.33`) and one independently confirms a riding fold (MINOR-A's row count at `.36`).
- **Superseded material is emitted, marked and chained, never dropped** — `.33` most consequentially, because an instrument is pinned to it (§6.1 item 3).
- **Every `STALE-SELF-DESCRIPTION` is tagged `(uncured)`** where the note does not scope it: `.25`, `.35`, `.39`, `.44`. None is silently corrected.
- Status and mathematical content are kept distinct: the annex stack's grade (0/2, no hostile pass at composition, one scoped pass since) is carried separately from the mathematics it supplies, and the acceptance's scope (“attaches to the frozen body”) is quoted at `.25`.
- **Honest limitation of this shard:** its mathematics is the least instrumented in the note — the R11 layer has no machine leg and the R9 layer's leg tests a superseded statement. Every check in §5's last row is this compiler's own recomputation, and while all of them pass, **a compiler's arithmetic is not a decorrelated instrument.** The note's own closing words are the right summary: *“awaiting a clean re-pass + the (CS-1Q) per-genre ledger obligation.”*

EFF-GENIND-s3of3 COMPILED: 59 statements / 27 xrefs verified / 12 commit pins + 13 artifacts verified / 3 near-misses / 5 open calls
