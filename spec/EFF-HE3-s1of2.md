# EFF-HE3-s1of2 — CANONICAL EFFECTIVE-SPECIFICATION SHARD

**COMPILED-BY: opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). CODEX CROSS-READ OWED (post-reset).**

## 1. Shard header

**Source note:** `lean/notes/openmath/HE3_PROOF_2026-08-08.md` (1853 lines).

**HOME range:** source lines **1–1275** inclusive, per `runs/qgen/sweep_manifest.txt` row 31 (`HE3|lean/notes/openmath/HE3_PROOF_2026-08-08.md|1|1275|s1of2`). That covers: title + status + instruments · §S0 consumption fences · §S0′ the `[r1]` repair record + consumer trace · §S0″ the `[r2]` repair record · §S1 STATEMENTS (the corrected node with its Ψ-comparison derivation, DEFINITION 1 + its `[r2]` construction pin, DEFINITION 2, THEOREM HE3.A, COROLLARY HE3.B, COROLLARY HE3.C) · §S2 the mechanism · §S3 LEMMA HE3-1 / HE3-1L / HE3-1′ + the `[r2]` twist Remark and its witness · §S4 LEMMA HE3-0 / COROLLARY HE3-0′ · §S5 LEMMA HE3-2 + COROLLARY HE3-2′ · §S6.1 LEMMA HE3-3 with (SEP) and the `[r1-N1]` supplement · §S6.2 LEMMA HE3-4 · §S6.3 the proof of THEOREM HE3.A + LEMMA HE3-6 · §S6.4 COROLLARY HE3.B's proof + the μ = 2 cross-check · §S6.5 LEMMA HE3-5 and its Interpretation. Later text (§S7 boxes, §S8 battery, §S9/§S9′ verdicts, and the two dated append blocks — post-PE3 and the 2026-08-12 A5 corrections R8-1..R8-5, lines 1276–1853) is used ONLY to resolve material homed in this range.

**HEAD blob hash:** `79bbbb638c39cf4a9658e466210626bf5d6c90a5` (clean in the working tree; last touched by commit `62400944`).

**Compilation context:** `spec/EFF_TEMPLATE_v2.md` AT HEAD (rules 1–28). Temporary IDs `EFF.HE3.s1of2.<nn>`.

**GENRE: TAG-SPARSE PROSE PROOF with blockquoted statement displays and heavy in-line strike-through.** `grep -c '\tag{'` = **0** over the whole note. Statements sit in `> ` blockquotes with bold `LEMMA/THEOREM/COROLLARY/DEFINITION` openers; proofs sit in unquoted body prose. **The distinguishing feature of this note's genre is that repairs are applied IN PLACE with `~~strike-through~~` plus a bracketed `[r1, Fn]` / `[r2, F-n]` replacement** — so a single displayed sentence routinely contains both the refuted text and its correction, byte-adjacent. §6 records how that was handled; it is the shard's dominant boundary problem.

### Governing effective-text record

**FREEZE PREDICATES (rule 21 — this note has TWO, and they are unusually asymmetric):**

**(F1) NO TEXT-FREEZE on the body during r1/r2 — repairs are IN-PLACE.** The note states the mechanism at lines 4–7:

> “**Status:** complete at commit 3; **[r1] REPAIR ROUND 2026-08-09** applied
> in place (this note is at attempt grade 0/2, unaccepted, so tagged in-place
> repairs per the GENHN [r1] mechanism; the sealed battery runner and its
> artifacts are byte-untouched).”

re-asserted at §S0′ (94–96): “Repairs are re-derived from this note's lemmas and the finding mechanisms, **tagged in place**”. **After PE3 the discipline switches to dated appends**: line 1589 (out of range) — “The body above, §S1 (iii) included, stays BYTE-FROZEN; the correction lives here” — and line 1631–1632 — “Everything above this heading is byte-untouched by this append.”

**(F2) INSTRUMENT-FREEZE — the sealed battery, byte-frozen through every round.** Lines 6–7, 126–128 (“the §S8 battery and its artifacts stay byte-frozen; `he3r1_supp.py` is touched at the docstring only (F-4: stdout byte-identical, §S9′ pin updated)”), and the §S9′ pin at 1494–1500. **The one exception is disclosed and quantified**: the `he3r1_supp.py` docstring changed at `[r2]`, with the old and new md5s BOTH displayed (`9cd132a8ce174f5703542757675f7960` → `93681e8d47d447dcbfd46db0ddfe0c55`) and the stdout certified byte-identical. That is the cleanest instrument-freeze accounting in the corpus.

**(F3) CONSUMER-PIN FREEZE — three specific displays are byte-frozen because frozen consumers pin them.** Lines 129–130:

> “DEFINITION 1, HE3-2(b)'s consumed above-λ clause, and the (★) display
> stay byte-identical (the frozen consumers' pins).”

This is a **third, distinct** freeze predicate: it protects three named spans against the note's own in-place repair mechanism, because HE6 and HE7 are frozen at `HE3 @ 7a95449` and consume them. It is why DEFINITION 1's `[r2]` construction pin is appended *after* the definition rather than edited into it (`.14` vs `.13`).

**EFFECTIVE TEXT FOR THIS SHARD = lines 1–1275 as written, with `[r1]` and `[r2]` already landed in place (struck text is REFUTED text preserved for the record, never current), READ AS CORRECTED by the six out-of-range dated corrections wherever they name an in-range sentence.** Six such corrections land inside this range (one from PE3, five from the 2026-08-12 A5 wave); each is applied at its unit and listed in §7.

**Reading rule for strike-through (compiler-declared, because the note does not state one):** `~~X~~ **[rN, Fm: Y]**` means **X is REFUTED and Y is the current reading**. The struck text is quoted at its unit whenever it is load-bearing — the note deliberately preserves it so a reader can see what was wrong — but it is never the CANONICAL STATEMENT. Where a unit's statement contains struck material, the CANONICAL STATEMENT quotes the whole span verbatim (strike markers included) and the CONDITIONALITY names which half is current.

### Scope split (rules 7 + 17 — three predicates)

**A. ABSORPTION / supply SET.** The note's own inventory is its title and §S1: **THEOREM HE3.A** (the stage-σ recursion), **COROLLARY HE3.B** ([GENHN-HE(μ)] for all μ; unconditional at μ ≤ 3), **COROLLARY HE3.C** (the program consequence), supported by **DEFINITION 1/2** and **LEMMAS HE3-0, HE3-0′, HE3-1, HE3-1L, HE3-1′, HE3-2, HE3-2′, HE3-3, HE3-4, HE3-5, HE3-6**. The claimed absorption target is GENHN's open box: the title says “**[GENHN-HE(μ ≥ 3)] CLOSED AT ITS FIRST-LIVE CASE (μ = 3, degrees n ≤ 7: UNCONDITIONAL) AND REDUCED TO ONE NAMED BRANCH AT μ ≥ 4 (HE3-BOX-6)**”.

**B. APPEND / consumption PROTOCOL scope — what HE3 lands on other notes.** **Nothing.** HE3 *reports* on its consumers rather than appending to them — §S0′'s CONSUMER TRACE (110–118) is a table of four consumers with a SAFE/N-A verdict each, computed by HE3 and landed nowhere. Its own words for the GENIND row: “no consumption site of HE3 found in `GENIND_PROOF_2026-08-08.md` (grep, this round)”. **Zero dated consumption appends are claimed landed on any consumer, and none is invented here.** Crucially, **HE3's discharge of `[GENHN-HE]` has NOT landed on GENHN** — verified per rule 10 against GENHN's full append chain to its line 2627 (see `.09` and OPEN-CALL 2).

**C. INBOUND CORRECTIONS RECEIVED.** Four streams, all landing in this range:

| # | Source | Landing form | Count | In-range targets |
|---|---|---|---|---|
| 1 | Fable PE1 @ `7950ee4` (`HE3_passPE1_report.md`) | in-place `[r1]` tags | 8 findings + 1 self-found (N1) | `.03`, `.10`, `.11`, `.16`–`.19`, `.21`–`.29`, `.31`, `.33` |
| 2 | Fable PE2 @ `6d0ff09` (`HE3_passPE2_report.md`) | in-place `[r2]` tags | 5 findings | `.10`, `.14`, `.17`, `.24`, `.27` |
| 3 | Fable PE3 (`HE3_passPE3_report.md`) | dated append (out of range) | 1 MINOR | `.12` (§S1 (iii)'s starved-corner parenthetical) |
| 4 | sol certification A5 (2026-08-12), re-adjudicating the R8 chain read | dated appends (out of range) | 5, all REAL | `.28`, `.29`, `.32`, `.20`, `.34` |

### Resolution rules applied

1. Lines 1–1275 supply the HOME material. `[r1]` and `[r2]` tags are **already-landed base text**; struck spans are refuted-but-preserved.
2. **Post-PE3 corrections are dated appends and never edit.** Six land in range; each is applied at its unit with the rider quoted.
3. **The three consumer-pinned displays (DEFINITION 1, HE3-2(b)'s above-λ clause, the (★) display) are byte-frozen even against this note's own in-place mechanism.** Where a repair was needed at a pinned display, it is landed *adjacent* rather than *inside* — `.14` (DEFINITION 1's `[r2]` construction pin) is the pattern. Recorded because a merge that flattens `.13` and `.14` would violate the consumers' pins.
4. **Two out-of-range appends PROVE previously boxed material** (R8-2 proves branch (i); R8-3 proves the D′ = 1 case). They are **licenses**, not supersessions, and each *narrows* HE3-BOX-6 rather than widening it. Applied at `.28`/`.32` with the box's own state re-stated.
5. Out-of-range statements are NOT emitted here merely because they resolve in-range text. §S7's six boxes, §S8's battery, §S9/§S9′'s verdicts, and all six dated corrections are homed in shard 2.
6. Every cited commit hash in range was verified with `git cat-file -t`; every cited artifact was verified to exist; truncated hashes are marked **UNPINNED** (rule 23).

### Quotation and table discipline

CANONICAL STATEMENTs are verbatim or explicitly `[ASSEMBLED]`; truncations marked `…`; **strike-through markers are reproduced exactly** (`~~…~~`), since removing them would silently promote refuted text. Every statement unit carries `FORM:`. The three source tables in range (§S0′'s two, §S6.4's cross-check listing) are transcribed as `[TABLE]` per rule 5, with rule-22 arithmetic audits. Compiler-authored ledgers (§3–§5) are flagged `[TABLE — compiler ledger]`.

---

## 2. Statement inventory

### EFF.HE3.s1of2.01  [changes-record]

**CANONICAL STATEMENT:** verbatim, line 1 (the title headline with both round riders).

**FORM:** display (H1 heading, one sentence + two bracketed round records).

> “# HE3 — [GENHN-HE(μ ≥ 3)] CLOSED AT ITS FIRST-LIVE CASE (μ = 3, degrees n ≤ 7: UNCONDITIONAL) AND REDUCED TO ONE NAMED BRANCH AT μ ≥ 4 (HE3-BOX-6): the σ-decision at composite stages of ANY multiplicity, by THEOREM HE3.A (the stage-σ recursion: σ at a μ-stage = the label read of the degree-μ stage resolvent over the stage ring, composed multiplicatively) + COROLLARY HE3.B ([GENHN-HE(μ)] for ALL μ by induction with strict descent μ′ ≤ μ/2, base μ ≤ 3 composite-stage-free) **[r1 2026-08-09: repaired in place after Fable PE1's two f₁ ≥ 2 CRITICALs; the μ ≤ 3 headline survives WITH the corrected machinery (HE3-1L letters, D′h thresholds, HE3-6 equivariance) — §S0′ for the record, §S9′ for the supplementary machine leg; grade 0/2]** **[r2 2026-08-09: repaired in place after Fable PE2's 2 GAPs (the R_λ coherent-convention seam, now PINNED at DEFINITION 1 [r2] with the coboundary Remark; the §S1 attainment step, now the Ψ-comparison) + 3 MINORs — §S0″ for the record; grade stays 0/2, PE3 next]**”

**CONDITIONALITY:** **Four separate qualifications, and the headline is materially different at HEAD from what it says here.**
(a) **“REDUCED TO ONE NAMED BRANCH AT μ ≥ 4 (HE3-BOX-6)” is NARROWED by the 2026-08-12 R8-2 append** (1691–1734, shard 2): the box had *two* base-change branches under it as §S6.2 displayed them, and R8-2 **proves branch (i)** (LEMMA HE3-4U), leaving “branch (ii) alone is BOXED”. So the headline's “ONE named branch” — which §S1 already said and §S6.2 contradicted — becomes true only after R8-2. `SUPERSESSION KIND: license`.
(b) **“degrees n ≤ 7” rests on an undisplayed `D′ ≥ 2`**, supplied by R8-3's LEMMA HE3-4D1 (1736–1772, shard 2): “The implication “μ ≥ 4, i.e. n ≥ D′μ ≥ 8” requires a case split; an ambient genre has not been assumed to satisfy D′ ≥ 2.” After HE3-4D1 the D′ = 1 case is unconditional at every μ, so “the advertised unconditional range n ≤ 7 survives, now with the missing derivation displayed.” `SUPERSESSION KIND: license`.
(c) **`STALE-SELF-DESCRIPTION` (rule 26)** on both “grade 0/2” clauses: PE3 returned CLEAN and moved the counter to **1/2** (1579–1583, shard 2). **The note is NOT accepted** — the arc stops at 1/2, and the 2026-08-12 ledger line says “HE3's row → 5 repairs folded, **awaiting sol discharge-confirmation**” (1851–1853).
(d) **“CLOSED” has not landed on GENHN.** GENHN's own §S9.2 still lists `[GENHN-HE(μ ≥ 3)]` as “THE one load-bearing open lemma of the whole composite program”, and no GENHN append records HE3's discharge (verified against GENHN's full chain). See OPEN-CALL 2.
**CHAIN for the μ ≥ 4 reservation:** headline “ONE named branch” → §S6.2's “BOTH … BOXED” (contradicting it) → R8-2 proves (i) → “branch (ii) alone is BOXED”. **TERMINAL: R8-2's reading, awaiting sol discharge-confirmation.**

**DERIVATION:** Not a mathematical unit; the headline indexes `.15` (HE3.A), `.16` (HE3.B), `.17` (HE3.C).

**RESOLUTION TRACE:** statement line 1 · correction sites 1579–1583 (grade), 1691–1734 (R8-2), 1736–1772 (R8-3), 1851–1853 (ledger).

XREF: `GENHN_PROOF_2026-08-08.md:[GENHN-HE` — grep-verified count **19**.
XREF: `HE3_passPE1_report.md` ✓ present · `HE3_passPE2_report.md` ✓ present.

**TEETH:** NONE (index headline).

---

### EFF.HE3.s1of2.02  [changes-record] · SERIES: HE3-GRADE-ARC, member 1 of 4

**CANONICAL STATEMENT:** verbatim, lines 3–20.

**FORM:** bold-headed paragraph (Unit / Status / Attempt grade / Instruments).

> “**Unit:** HE3 (the last open mathematics of the uniformity program).
> **Status:** complete at commit 3; **[r1] REPAIR ROUND 2026-08-09** applied
> in place (this note is at attempt grade 0/2, unaccepted, so tagged in-place
> repairs per the GENHN [r1] mechanism; the sealed battery runner and its
> artifacts are byte-untouched). Statements §S1, mechanism §S2, proofs
> §S3–S6, boxes §S7, sealed battery §S8, verdict §S9 (GREEN, 0 violations).
> **Attempt grade 0/2 on the μ ≤ 3 statement**: the first counted
> fresh-context pass (Fable PE1, `HE3_passPE1_report.md` @ 7950ee4) returned
> NOT CLEAN — 2 CRITICAL + 4 GAP + 2 MINOR — and this [r1] round repairs the 8 findings at their
> sites (see the [r1] REPAIR RECORD in §S0′). The earlier Codex pass
> adjudicated in the composer's own context is preserved at
> `CODEX_HE3PE1_2026-08-08.md` and does not count toward the grade.
> **Instruments:** `verification/openmath/he3_checks.py` (sealed battery;
> artifacts `he3_checks_output.txt`, `he3_checks_results.json`; ℤ_p rows,
> PARI σ-oracle, 4 wired teeth — see HE3-BOX-4b) and, this round,
> `verification/openmath/he3r1_supp.py` (additive leg: the repaired peel at
> the PE1 counter-instance and f₁ ∈ {2, 3} sweeps; §S9′).”

*(Truncation marked: the phrase “confined at CRITICAL level to the f₁ ≥ 2 geography” is elided at the `…`-free join above; it is quoted at `.03`.)*

**CONDITIONALITY:** **`STALE-SELF-DESCRIPTION` (rule 26).** SERIES `HE3-GRADE-ARC`, source order:

| # | Event | Where | Grade after |
|---|---|---|---|
| 1 | composed; PE1 NOT CLEAN (2C + 4G + 2M); `[r1]` repairs | **this unit**, 3–20 | 0/2 |
| 2 | PE2 NOT CLEAN (0C + 2G + 3M); `[r2]` repairs | 120–139 (`.10`) | 0/2 |
| 3 | HE3-BOX-1's grade box | 1278–1294 (shard 2) | 0/2 |
| 4 | **PE3 CLEAN (0C + 0G + 1M)** — “The consecutive-clean count moves 0/2 → **1/2** and HOLDS at 1/2 through this correction” | 1579–1583 (shard 2) | **1/2 (TERMINAL)** |

**The arc stops at 1/2. HE3 is NOT accepted**, and the 2026-08-12 A5 wave added five further REAL findings *after* the clean pass, with the ledger line “awaiting sol discharge-confirmation”. A chapter cut must not read the μ ≤ 3 “UNCONDITIONAL” headline as an accepted result.
One methodological note preserved verbatim and worth keeping: **a pass adjudicated in the composer's own context does not count** (“The earlier Codex pass adjudicated in the composer's own context … does not count toward the grade”). That is the corpus's decorrelation rule, stated here as a grade decision.

**DERIVATION:** Round record.

**RESOLUTION TRACE:** statement 3–20 · correction sites 120–139, 1278–1294, 1579–1583, 1851–1853.

PIN: `7950ee4` ✓ commit.
ARTIFACT: `verification/openmath/he3_checks.py` ✓ · `he3_checks_output.txt` ✓ · `he3_checks_results.json` ✓ · `he3r1_supp.py` ✓ · `he3r1_supp_output.txt` ✓ · `he3r1_supp_results.json` ✓ — 6/6 present.
XREF: `CODEX_HE3PE1_2026-08-08.md:HE3` — count **15** (the uncounted pass, preserved).

**TEETH:** the sealed battery (`.03`'s instrument) plus the additive `he3r1_supp.py` leg; both inventoried in §5 and homed as verdict units in shard 2. **`disclosed non-repair`:** “4 wired teeth” against five promised — the shortfall is disclosed at HE3-BOX-4b (shard 2), and one of the four (HE-T-NODE) “does not test what its name claims”.

---

### EFF.HE3.s1of2.03  [fence]

**CANONICAL STATEMENT:** verbatim, lines 24–77 (§S0's positive-consumption list, including the two large `[r1]` correction brackets inside the GENHN bullets).

**FORM:** bulleted declaration list under a `##` heading, with two multi-line in-place corrections.

> “## S0. WHAT THIS UNIT CONSUMES (pins, and what it does NOT consume)
>
> Consumed at pin (HEAD = f2a7164 unless stated):
>
> * **GENHN @ HEAD** (`GENHN_PROOF_2026-08-08.md`, battery GREEN
>   2,223,050/0 per its §S12 — machine-verified, contrary to the charge's
>   assumption of an unrun battery):
>   - THEOREM GENHN.CLASS (the genre datum G = (Q; e₁, f₁, μ; h, entry);
>     finiteness; uniformity in n) — consumed as the *definition layer*.
>   - GENHN.A(i) LEMMA GENHN-1 (the stage ring R = Ô[x]/(Φ′) with
>     e = e₁, f = f₁, K = F_{Q^{f₁}} — carrier corrected, see the [r1, F7]
>     note at §S1; the Φ′-development f = Φ′^μ + Σ_{j<μ}A_jΦ′^j; the node
>     ~~dv(A_j) ≥ (μ−j)S + 1, S = e₁h~~ **[r1, F2: GENHN at HEAD carries
>     erratum [r1 2026-08-08] — the stage-initial node at f₁ ≥ 2 is
>     {dv(A_j) ≥ (μ−j)·D′h + 1}, D′h = e₁f₁h = f₁S; at f₁ = 1 the two
>     coincide. HE3's pin f2a7164 predates that erratum; this note now
>     consumes the corrected node and re-derives it from its own locus in
>     §S1]**, dv := e₁v).
>   - **GENHN.A(ii) LEMMA GENHN-2 (THE SLOT LEMMA) — the single most
>     load-bearing import**: ~~for A = Σ_{i<D′}a_i x^i and ANY element ξ
>     with (T1)/(T2)~~ **[r1, F4: GENHN's LEMMA GENHN-2 is stated at roots
>     θ of Φ′ only ("for every root θ of Φ′ and every lift"), not at
>     arbitrary (T1)/(T2) points; the paste above overconsumed it. The
>     ξ-form this note uses at roots of f and at roots of test keys is
>     LEMMA HE6-0″ (`HE6_PROOF_2026-08-08.md` §S1, frozen at HEAD, cited
>     as-of 2026-08-09), whose one-paragraph proof re-runs GENHN-2's
>     mechanism: (T1) is used only to separate the e₁ slot classes
>     (i ↦ ih mod e₁ bijective since gcd(h,e₁) = 1), (T2) only to make
>     {1, η_ξ, …, η_ξ^{f₁−1}} F_Q-independent; Φ′(ξ) = 0 is never used.]**
>     For A = Σ_{i<D′}a_i x^i and any point ξ with (T1) v(ξ) = h/e₁,
>     gcd(h, e₁) = 1 and (T2) η_ξ := res(ξ^{e₁}π^{−h}) a root of ψ
>     (deg ψ = f₁),
>         dv(A(ξ)) = min_i (e₁·v(a_i) + i·h)   EXACTLY,
>     and the residue of the attaining slot is the universal polynomial
>     Σ_t res(a_{i+e₁t})·η_ξ^t evaluated at η_ξ [by GENHN-2 at ξ = θ; by
>     HE6-0″ at other (T1)/(T2) points, up to its fixed normalizer-ratio
>     twist, which the n(κ)-reads below never see].
>   - GENHN.A(iii) LEMMA GENHN-3 (window ledger: lift-stability iff
>     dv < e₁N; consulted digits in-window; carries upward only).
>   - GENHN.C (σ at every μ = 2 stage) — consumed as a CROSS-CHECK only:
>     §S6 re-derives it as the μ = 2 case of HE3.A, so no circularity.
>   - GENHN's §S11.F extraction-certified perimeter (embedded genres:
>     the ambient window certifies stage leaves only below explicit
>     per-coordinate floors) — consumed as the machine-side gate.
> * **GENIND @ 4682bcf**: THEOREM GENIND.A(I) (the species partition
>   DRAIN/DEC/α/β/CS) and **GENIND.A(IV) (THE COMPOSITE CRITERION: a CS
>   event inside a system of multiplicity μ requires abscissa length
>   ≥ 4, hence needs μ ≥ 4)** — this is the descent engine of
>   COROLLARY HE3.B.
> * **GENIND-3** (scale-then-Hensel sibling fibration) — embedded genres.
> * **Classical:** Hensel; the ultrametric Newton-polygon read of a
>   polynomial over a complete DVR (values = slopes, residues = roots of
>   the residual polynomial); Galois theory of local fields (e, f
>   multiplicativity, unramified base change); resultants/norms.”

**CONDITIONALITY:** **Two of the three GENHN imports were OVER-CONSUMED and are corrected in place; both corrections are load-bearing for the whole note.**
(a) **`[r1, F2]` — the node.** HE3's pin `f2a7164` predates GENHN's own `[r1]` erratum, so HE3 was consuming a node GENHN had already corrected. HE3's response is not merely to re-pin but to **re-derive the corrected node from its own locus** (`.11`). This is a rare pattern: a consumer discovering its supplier moved, and proving the moved statement independently rather than citing it.
(b) **`[r1, F4]` — the SLOT LEMMA's quantifier.** GENHN-2 is stated at **roots θ of Φ′ only**; HE3 needs it at arbitrary (T1)/(T2) points (roots of f, roots of test keys). The over-consumption is corrected by routing the ξ-form through **LEMMA HE6-0″** (a *different* note's lemma), cited as-of 2026-08-09. **This is the single most load-bearing citation in the note** — every slot read at ρ or θ″ rides it. Its correctness was later re-checked by R8-5 (1795–1819, shard 2), which found the HE3-0 proof sentence still citing GENHN-2 and re-pointed it. `SUPERSESSION KIND: replacement` (the source of the ξ-form).
(c) The GENHN.C bullet's **“consumed as a CROSS-CHECK only … so no circularity”** is the note's own non-circularity fence and is re-asserted at `.31` (§S6.4's cross-check: “no circularity: GENHN.C is not used above”).
(d) The pin line “HEAD = f2a7164” is as-of; GENHN has moved substantially since (its 2026-08-12 appends). The note anticipates this only for the node.

**DERIVATION:** Declaration, not derivation. The re-derivations it promises are at `.11` (the node) and, for the ξ-form, at HE6-0″ (external).

**RESOLUTION TRACE:** statement 24–77 · re-derivations 169–237 (`.11`) · correction sites 1795–1819 (R8-5's provenance fix at §S4).

XREF: `GENHN_PROOF_2026-08-08.md:THEOREM GENHN.CLASS` — count **7**.
XREF: `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-1` — count **4**.
XREF: `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-2` — count **2**.
XREF: `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-3` — count **3**.
XREF: `GENHN_PROOF_2026-08-08.md:THEOREM GENHN.C` — count **11**.
XREF: `GENHN_PROOF_2026-08-08.md:S11.F` — count **10**.
XREF: `GENIND_PROOF_2026-08-08.md:GENIND.A(I)` — count **3**.
XREF: `GENIND_PROOF_2026-08-08.md:GENIND.A(IV)` — count **5**.
XREF: `GENIND_PROOF_2026-08-08.md:LEMMA GENIND-3` — count **6**.
XREF: `HE6_PROOF_2026-08-08.md:HE6-0″` — count **7**.
PINS: `f2a7164` ✓ commit · `4682bcf` ✓ commit.

*Compiler cross-check (rule 22) of the GENHN battery figure quoted here.* “battery GREEN 2,223,050/0 per its §S12” — verified against `GENHN_PROOF_2026-08-08.md` line 1802: “**GREEN — 2,223,050 checks, 0 violations**” ✓ **exact match.** The parenthetical “contrary to the charge's assumption of an unrun battery” is a process remark, not a claim about mathematics.

**TEETH:** NONE (import declaration).

---

### EFF.HE3.s1of2.04  [fence]  — the NOT-consumed fence

**CANONICAL STATEMENT:** verbatim, lines 79–88.

**FORM:** bold-headed paragraph with three lettered clauses.

> “**NOT consumed (deliberate).** (a) **GENHN.A(iv)/LEMMA GENHN-4 is NOT
> consumed**, hence **the W-9 graded weld face (GENHN-BOX-2) is NOT
> inherited**: GENHN-4 is the *digit-space bijection* used for COUNT
> laws; this unit needs only the *valuations and residues* of a
> recentered development, which §S5 proves elementarily (LEMMA HE3-2).
> So HE3's σ-theorem stands on strictly fewer weld faces than GENHN's
> count laws. (b) The Montes/GMN order-≥2 index theorem — named in
> GENHN's box as the "faithful-cite target" — is **not** cited: §S3–S6
> prove what is needed from the resultant identity + the ultrametric
> read. (c) SIGMALAW, JC-LOAD, DULEMMA: not consumed.”

**CONDITIONALITY:** **Unconditional, load-bearing for the DAG, and independently corroborated.**
(a) is the note's strongest structural claim and it is confirmed from outside: `spec/HYPOTHESIS_LEDGER.md` records “HE3 explicitly declines GENHN-4, so the σ chain carries HYP.81 without carrying HYP.148”, and `runs/qgen/WELD_FACE_AUDIT.md` designates GENHN-4 layer 1 as the corpus's one live weld face — which HE3 therefore does not touch. **Verified independently here:** `grep -cF 'LEMMA GENHN-4' HE3_PROOF_2026-08-08.md` finds the designation only in this fence and in the HE3-BOX-1 restatement (shard 2), never at a consumption site.
(b) is re-asserted at HE3-BOX-6's repair route (“This is the higher-order Montes construction”, 1365–1366, shard 2) — named as the *route*, still not cited.
(c) is a clean triple negative with no later qualification.
**One thing (a) does NOT claim:** that HE3 is weld-free overall. It says HE3's σ-theorem carries fewer faces than GENHN's count laws. HE3 still consumes GENHN-1/-2/-3 and HE6-0″, each at its own grade.

**DERIVATION:** Declaration; discharged by §S5's elementary LEMMA HE3-2 (`.24`), which proves the recentered valuations/residues with no digit-space bijection — the lemma says so in its own words: “**No graded frame and no digit-space bijection is used: (a)–(c) are statements about valuations and residues only.**”

**RESOLUTION TRACE:** statement 79–88 · discharge 700–809 (`.24`) · restatement 1291–1294 (shard 2).

XREF: `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-4` — count **3**.
XREF: `GENHN_PROOF_2026-08-08.md:GENHN-BOX-2` — count **5**.
XREF: `GRTJC_PROOF_2026-08-08.md:JC-LOAD` — count **31**.
XREF: `SIGMALAW_PROOF_2026-08-08.md:(EC-q)` — count **26**.
XREF: `DULEMMA_PROOF_2026-08-08.md:DULEMMA` — count **1**.
ARTIFACT: `runs/qgen/WELD_FACE_AUDIT.md` ✓ · `spec/HYPOTHESIS_LEDGER.md` ✓.

**TEETH:** NONE (negative fence). Its correctness is a grep-checkable property of the note, verified above.

---

### EFF.HE3.s1of2.05  [table]  — §S0′'s `[r1]` repair record (nine rows)

**CANONICAL STATEMENT:** verbatim, lines 92–108 (the heading, the discipline sentence, and the nine-row table).

**FORM:** `##` heading + a discipline paragraph + a Markdown table (finding → disposition → site).

> “## S0′. [r1] REPAIR RECORD (2026-08-09, after Fable PE1 @ 7950ee4)
>
> Repairs are re-derived from this note's lemmas and the finding
> mechanisms, tagged in place; the sealed battery and its artifacts are
> byte-untouched. Finding → disposition, with the site:”

`[TABLE]` — transcribed verbatim (the source is already a Markdown table; emitted once, per rule 14's tables-are-units clause):

| # | PE1 finding | disposition at [r1] |
|---|---|---|
| F1 | CRITICAL: peel letters reach only F_Q ⊊ K at f₁ ≥ 2 | REPAIRED: LEMMA HE3-1L (§S3, derived from HE6-1L's mechanism at the n(κ)-read, where the coset factor cancels); peel re-run with C-letters (§S6.2); verified on the PE1 counter-instance + f₁ ∈ {2,3} sweeps (§S9′) |
| F2 | CRITICAL: S = e₁h thresholds false at f₁ ≥ 2 | REPAIRED: node → (μ−j)D′h + 1 re-derived from the locus (§S1); HE3-1's band > D′h with the x²+18/x²+27 counter-instances recorded; HE3-2(c), HE3-1′, §S6.1 samples, (SEP) index re-keyed; leg-A2 off-locus member fenced by locus scoping (§S1); PE1's own MODERATION verified the on-locus μ ≤ 3 values survive the S → D′h repair, and §S9′ re-verifies on fresh members |
| F3 | GAP: headline vs the assumed finding-6 clause | DISCHARGED: LEMMA HE3-6 (§S6.3, level-1 derivation, HE6-5 template); headline rescope block at HE3.B |
| F4 | GAP: GENHN-2 overconsumed at ξ ≠ roots of Φ′ | REPAIRED: §S0 import restated at roots θ; ξ-form routed through LEMMA HE6-0″ (as-of cite, frozen at HEAD); §S4 proof-sketch cite corrected |
| F5 | GAP: two mutually-canceling false displays | REPAIRED: §S6.2 equivalence single-clause + the direct route (class size = D′m) operative; HE3-2(b) collapse clause with (Z+s)^T·R_λ(Z+s)/Z^m; §S6.3 stage-α sentence re-keyed to the above-λ read |
| F6 | GAP: n(λ)-read at ℓ ≥ 2 undefined | REPAIRED: β = res(y^ℓ/n(u)) in HE3-0(iii)/HE3-0′ (HE6-0′ form); μ ≤ 3-vacuous, μ ≥ 4 display corrected |
| F7 | MINOR: "R a complete DVR" | REPAIRED: order-in-L carrier (§S1); HE3-1 norm through the field L″; stage-CS O_L note (μ ≥ 4, boxed region) |
| F8 | MINOR: ±s sign seam across three sites | REPAIRED: minus convention Φ″ = Φ′ − C; the three sites now agree; battery semantics invariant under s ↦ −s |
| N1 | self-found this round (not in PE1) | the old HE3-3 step (3) is silent at three CONSECUTIVE integer slopes when K^× has no generic letter ((Q,f₁) = (2,1)); closed by the recenter-then-invert supplement (§S6.1), both branches machine-demonstrated (§S9′); LEMMA HE6-3 covers it independently as-of 2026-08-09 |

*Arithmetic audit (rule 22).* PE1's verdict is stated at `.02` as “2 CRITICAL + 4 GAP + 2 MINOR” = **8 findings**. The table has **9 rows**, of which N1 is explicitly “self-found this round (not in PE1)” ✓ so `9 − 1 = 8` ✓ **matches exactly**. Class counts in the table: CRITICAL F1, F2 = **2** ✓; GAP F3, F4, F5, F6 = **4** ✓; MINOR F7, F8 = **2** ✓. **All three class counts reproduce.** Cross-check against `.02`'s prose (“this [r1] round repairs the 8 findings at their sites”) ✓ consistent.

**CONDITIONALITY:**
(a) **F5's row is the shard's most consequential disposition** and it is honest about *why* the defect survived: two false displays that “mutually cancel”. `.29` carries the note's own explanation — “which is why the sealed battery never caught either (PE1 F5)”. A defect invisible to the instrument because two errors cancel is exactly the class rule 27's AUDIT disposition exists for.
(b) **F7's row understates itself as MINOR.** “R a complete DVR” is false, and the repair re-carriers the entire note through `L`/`O_L`. The note grades it MINOR because no conclusion moves — but the *display* change is large (`.10`, `.20`, `.34`).
(c) **N1 is a self-found gap in a repair round** — a genuine instance of the note auditing its own patch.
(d) Every row's promise is checkable against the body, and this shard checked all nine: F1 → `.21`; F2 → `.11`, `.20`, `.27`(c), `.29`; F3 → `.35`; F4 → `.03`, `.25`; F5 → `.27`(b), `.32`, `.34`; F6 → `.25`, `.26`; F7 → `.10`, `.20`, `.34`; F8 → `.21`, `.27`; N1 → `.30`. **All nine sites located and non-empty.**

**DERIVATION:** Repair record.

**RESOLUTION TRACE:** statement 92–108 · sites as listed above · later re-audit 1691–1734, 1795–1819 (R8-2, R8-5 re-open F5-adjacent and F4-adjacent material).

XREF: `HE6_PROOF_2026-08-08.md:LEMMA HE6-1L` — count **4** · `HE6-0″` — count **7** · `LEMMA HE6-3` — count **12** · `LEMMA HE6-5` — count **5** · `HE6-0′` — count **5**.
PIN: `7950ee4` ✓ commit.
ARTIFACT: `verification/openmath/he3r1_supp.py` ✓.

**TEETH:** `he3r1_supp.py` P1–P4 — the additive leg built to verify the r1 repairs; inventoried in §5, homed in shard 2. **Disposition: executable regression built from a repair round.**

---

### EFF.HE3.s1of2.06  [table]  — §S0′'s CONSUMER TRACE (four rows)

**CANONICAL STATEMENT:** verbatim, lines 110–118.

**FORM:** bold-headed paragraph + a Markdown table (consumer → pin → consumed clauses → verdict).

> “**CONSUMER TRACE (the frozen/accepted consumers of HE3's exports, at the
> repaired text).**”

`[TABLE]` — transcribed verbatim:

| consumer | pin | consumed clauses | verdict at [r1] |
|---|---|---|---|
| HE6 (frozen) | HE3 @ 7a95449 | DEF 1; DEF 2; HE3-0 (locus (T1)/(T2)); HE3-1 (resultant identity); (★) of HE3-3 step 1; §S6.3 assembly + HE3.B descent; HE3-2(b)+HE3-3 for the stage-α class size (its §S6.3) | SAFE. DEF 1 and (★) byte-unchanged; DEF 2 renamed node only; HE3-0's consumed clauses byte-unchanged ((iii)'s ℓ ≥ 2 read is re-proved inside HE6 as HE6-2″, not consumed); HE3-1 consumed only at HE6's own test heights κ > D′h (DEFINITION HE6-1's floor), inside the corrected hypothesis — the [r1] band repair VALIDATES HE6's stricter usage, which its §S3.1 Remark had already recorded; HE3-2(b)'s consumed clause (above-λ length = m·ℓ) survives verbatim in the corrected display; the assembly is strengthened (its assumed finding-6 clause is now LEMMA HE3-6) |
| HE7 (frozen) | HE3 @ 7a95449 | DEF 1/2; the convex duality (★) of HE3-3 step 1 | SAFE — both byte-unchanged in content (DEF 2's [r1] tag renames the node only) |
| GENHN (accepted-track, at HEAD with [r1]/[r2]/[e2] errata) | HE3-0 cited in its [r1] node erratum | (T1)/(T2) on the opening locus | SAFE — clauses byte-unchanged; HE3's [r1] node display now MATCHES GENHN's [r1] erratum (the stale-at-HEAD divergence PE1 F2 reported is closed) |
| GENIND (accepted) | — | no consumption site of HE3 found in `GENIND_PROOF_2026-08-08.md` (grep, this round) | N/A — trivially safe |

**CONDITIONALITY:** **This table is a cross-note claim in four parts and rule 10 requires it be checked against each target's full state, not against a pinned sentence. This compiler checked all four:**
(a) **HE6 row — CONFIRMED at the designation level.** `grep -cF 'HE3-0' HE6_PROOF_2026-08-08.md` = **9**; `DEFINITION 1` = **1**; `HE3-2(b)` = **1**; `HE3.B` = **2**; `HE3-1` = **1**. All five consumed designations are present in the target ✓. The clause-level “byte-unchanged” claims were **not** re-verified byte-for-byte here (that would require the 7a95449 blob); recorded as OPEN-CALL 3.
(b) **HE7 row — CONFIRMED at the designation level.** `grep -cF 'HE3-3' HE7_PROOF_2026-08-08.md` = **2** ✓, matching the (★)-of-HE3-3 citation. (`spec/EFF-HE7-s1of3.md` §3.1 independently records `HE3_PROOF:HE3-3` count 15 in the reverse direction and `HE3-BOX-6` count 12 — i.e. HE7 also consumes HE3-BOX-6, **which this trace does not list**. Recorded as source defect 1.)
(c) **GENHN row — CONFIRMED and still true at HEAD.** GENHN's `[r1]` erratum cites HE3-0 (its line 592–593: “Every root ρ of f on the genre-G opening locus satisfies (T1)/(T2) (HE3-0)”) ✓, and HE3's corrected node `{dv(A_j) ≥ (μ−j)D′h + 1}` matches GENHN's erratum display character-for-character ✓ **verified by direct comparison of the two notes at HEAD.**
(d) **GENIND row — CONFIRMED.** `grep -c 'HE3' GENIND_PROOF_2026-08-08.md` finds no HE3 consumption site ✓.
**One structural observation the trace does not make:** the table is computed *by HE3 about its consumers*, and **nothing is landed on any of them** — see header §B. If a consumer's own maintainer disagrees, this table has no force.

**DERIVATION:** Consumer audit.

**RESOLUTION TRACE:** statement 110–118 · verified externally as above · no correction site in HE3 (verified across both append blocks).

XREF: `HE6_PROOF_2026-08-08.md:HE3-0` — count **9** · `DEFINITION 1` — count **1** · `HE3-2(b)` — count **1** · `HE3.B` — count **2** · `HE3-1` — count **1** · `HE6-2″` — count **2**.
XREF: `HE7_PROOF_2026-08-08.md:HE3-3` — count **2**.
PIN: `7a95449` ✓ commit.

**TEETH:** NONE (audit table). **Disposition: `transfer audit` (rule 27)** — a finding-class produced by reading other notes, which no battery could generate.

---

### EFF.HE3.s1of2.07  [table]  — §S0″'s `[r2]` repair record (five rows)

**CANONICAL STATEMENT:** verbatim, lines 120–139.

**FORM:** `##` heading + a discipline paragraph + a Markdown table.

> “## S0″. [r2] REPAIR RECORD (2026-08-09, after Fable PE2 @ 6d0ff09)
>
> PE2's verdict: NOT CLEAN — 2 GAP + 3 MINOR, 0 CRITICAL; the eight r1
> repairs, HE3-1L, HE3-5, HE3-6, the N1 supplement and the consumer trace
> HELD under that pass's attacks, and its fresh e₁ ≥ 2 ∧ f₁ ≥ 2 route ran
> GREEN (`he3_pe2fresh.py`, 7/7 PARI members, 0 violations). The five
> findings are repaired below, re-derived in place; the §S8 battery and
> its artifacts stay byte-frozen; `he3r1_supp.py` is touched at the
> docstring only (F-4: stdout byte-identical, §S9′ pin updated).
> DEFINITION 1, HE3-2(b)'s consumed above-λ clause, and the (★) display
> stay byte-identical (the frozen consumers' pins).”

`[TABLE]` — transcribed verbatim:

| # | PE2 finding | disposition at [r2] |
|---|---|---|
| F-1 | GAP: R_λ construction unpinned; the §S3 Remark's twist-invariance sentence false as displayed (machine-adjudicated type flip at (e₁,f₁) = (2,2)) | REPAIRED: DEFINITION 1 [r2] construction pin (the coherent assembly — HE6 ϖ-CONVENTION / GENHN §S4 class); §S3 Remark's false sentence struck, replaced by the coboundary statement with the (3;2,2,2;1) witness re-derived (naive (Z−1)² phantom refine vs coherent irreducible, PARI σ = {(2,4)}); pointers at the grep sites (§S3 HE3-1′ proof, §S4 (ii), §S5 (b) display + proof, §S6.2 HE3-4) |
| F-2 | GAP: the §S1 node re-derivation inferred polygon slopes from root values without attainment | REPAIRED: the Ψ-comparison display (j = 0 pin direct; general pin via COUNT + R(D′h+1) with the μ ≤ 3 low/mid enumeration; honest scope — the letter-starved corner and μ ≥ 4 consumed from GENHN [r1] via HE6-3(a); the fence stands as independent support) |
| F-3 | MINOR: HE3-3 step (2) justified by the retired monomial carrier | REPAIRED: parenthetical re-keyed to the ξ-form slot read at ρ (HE6-0″ / HE3-1L mechanism, F_Q-independence of {η_ρ^t}) |
| F-4 | MINOR: supp P4 quasi-tautological; docstring sympy/Bareiss slip | DISCLOSED + FIXED: P4's scope stated at §S9′ (T(κ) bookkeeping, not residue arithmetic); PE2's FR-C (`nfeltval`/`nfmodpr`, κ = 0..5 at (2,2,1)) cited as the decorrelated leg; docstring corrected, runner pin updated, [r2] re-run stdout byte-identical |
| F-5 | MINOR: [r1-N1] demo geography label loose | DISCLOSED: the (3,2) demo scope stated at the §S9′ pin; PE2's FR-D (both branches over ℤ₂ at the live (2,1) geography) cited as the machine contact; coverage note dated |

*Arithmetic audit (rule 22).* PE2's verdict “2 GAP + 3 MINOR, 0 CRITICAL” = **5 findings**; the table has **5 rows** ✓. Class split: GAP F-1, F-2 = **2** ✓; MINOR F-3, F-4, F-5 = **3** ✓; CRITICAL = **0** ✓. **All three reproduce.**

**CONDITIONALITY:**
(a) **The `HELD` list is positive evidence and should travel with the note:** “the eight r1 repairs, HE3-1L, HE3-5, HE3-6, the N1 supplement and the consumer trace HELD under that pass's attacks”. A second hostile pass re-attacking the first pass's repairs and finding them sound is the strongest form of repair validation available.
(b) **F-1 is the shard's deepest mathematical finding** — the R_λ construction was *unpinned*, and two natural constructions give different factorization types. It is repaired at `.14` and its witness is `.24`. **This is a defect that would have emitted wrong σ inside the μ ≤ 3 headline's own scope** (`.24` says so).
(c) **F-4 and F-5 are DISCLOSED rather than repaired** — the leg's weakness is stated and a decorrelated substitute is cited. That is rule 20's `signed vacuity disclosure` and `accepted-with-decorrelation-supplied` in the source's own vocabulary.
(d) **The consumer-pin sentence is freeze predicate (F3)** and is quoted in §1.

**DERIVATION:** Repair record.

**RESOLUTION TRACE:** statement 120–139 · sites F-1 → `.14`, `.22`, `.23`, `.24`, `.25`, `.27`, `.32`; F-2 → `.11`; F-3 → `.29`; F-4/F-5 → §S9′ (shard 2). **All five located.**

PIN: `6d0ff09` ✓ commit.
ARTIFACT: `verification/openmath/he3_pe2fresh.py` ✓ present.

**NEAR-MISS (rule 15):** **`ϖ-CONVENTION`** — cited in F-1's disposition as “HE6 ϖ-CONVENTION”; fixed-string count **0** in `HE6_PROOF_2026-08-08.md`. The target's actual heading is `> **CONVENTION (ϖ-normalizers: twist-free).**` at line 104, verified. Referent unique; carried descriptively. Source defect 2.

**TEETH:** `he3_pe2fresh.py` — GREEN, 7/7 PARI members, 0 violations, at the first `e₁ ≥ 2 ∧ f₁ ≥ 2` geography HE3 ever exercised. Its FR-C and FR-D legs are cited as the decorrelated substitutes for the two disclosed weaknesses. **Disposition: executable regression on a decorrelated instrument; also the source of the F-1 witness.**

---

### EFF.HE3.s1of2.08  [hypothesis]  — §S1's standing frame

**CANONICAL STATEMENT:** verbatim, lines 144–149 (the frame sentence up to the stage-ring clause, which is `.10`).

**FORM:** inline sentence (unquoted body prose opening §S1).

> “Throughout: O a complete DVR with finite residue field F_Q, both
> characteristics; π a uniformizer; v the valuation with v(π) = 1,
> extended to a fixed algebraic closure of K₀ := Frac(O). G a composite-
> stage genre with data (Q; e₁, f₁, μ; h, entry); D′ := e₁f₁; Φ′ the
> current key (monic, degree D′, irreducible, roots of valuation h/e₁);”

**CONDITIONALITY:** Inherited hypothesis set; unconditional as a hypothesis. **“both characteristics” is load-bearing and re-asserted three times**: at `.24` (“Both characteristics: the only algebraic input is the SUBSTITUTION identity Z ↦ Z + s applied to R_λ, which is characteristic-free”), at `.19`'s mechanism paragraph (“it is *characteristic-free* (no binomial expansion is used — only the substitution identity for residual polynomials)”), and at `.24`'s PE1-finding-4 repair, which is *precisely* about characteristic: “the summand carries binom(i, j), whose valuation can be positive in mixed characteristic … and which can vanish in equal characteristic p”. **The machine leg does NOT match the proof's characteristic coverage** — HE3-BOX-4 (shard 2) discloses that PARI's oracle exists only on the ℤ_p side.

**DERIVATION:** Hypothesis.

**RESOLUTION TRACE:** statement 144–149 · untouched by any round or append (verified) · characteristic coverage disclosed at 1313–1320 (shard 2).

**TEETH:** NONE (hypothesis). The char-p side is a disclosed machine hole.

---

### EFF.HE3.s1of2.09  [scope-record]  — the absorption target

**CANONICAL STATEMENT:** [ASSEMBLED — the note's claim on GENHN's box, stated in the title (line 1) and discharged at COROLLARY HE3.C (369–378); the two spans are quoted at `.01` and `.17`. This unit records the CROSS-NOTE STATUS of that claim, which no single sentence of HE3 states.]

**FORM:** bracketed rider (compiler-assembled scope record; not a source display).

**CONDITIONALITY:** **HE3 claims to close GENHN's `[GENHN-HE(μ ≥ 3)]` at μ ≤ 3; the claim has NOT landed on GENHN. Verified per rule 10 against GENHN's FULL append chain, not a pinned sentence:**
- GENHN's own §S9.2 item 1 (its lines 1449–1453) still reads: “**[GENHN-HE(μ ≥ 3)]** — the σ-decision at stage leaves of multiplicity μ ≥ 3 … **THE one load-bearing open lemma of the whole composite program.**”
- GENHN's eleven dated appends run to its line 2627 and **none names HE3's discharge**. Its last append is the 2026-08-12 GENHN-COUNT-RERUN.
- The only HE3 → GENHN edge that HAS landed is the reverse direction: GENHN's `[r1]` node erratum cites HE3-0 (GENHN line 592–593), which `.06`'s trace records correctly.
- `grep -cF 'GENHN-HE' HE3_PROOF_2026-08-08.md` = **7**; `grep -cF '[GENHN-HE' GENHN_PROOF_2026-08-08.md` = **19**. Both notes discuss the box; neither records the other's disposition of it.
**Compiled state: HE3 CLAIMS the discharge at μ ≤ 3 (unconditional) and at μ ≥ 4 (conditional on HE3-BOX-6 branch (ii), after R8-2 narrowed it); GENHN records the box as OPEN. The compiler does not adjudicate.** See OPEN-CALL 2.
**Grade note:** even taking HE3's claim at face value, it arrives at **attempt grade 1/2** (`.02`), with five REAL findings folded after the clean pass and “awaiting sol discharge-confirmation”.

**DERIVATION:** Cross-note status record; the mathematics is `.15`–`.17`.

**RESOLUTION TRACE:** HE3-side statement 1, 369–378 · GENHN-side status `GENHN_PROOF_2026-08-08.md` 1029–1042, 1449–1453 · HE3's grade 1579–1583 (shard 2) · the ledger line 1851–1853 (shard 2).

XREF: `GENHN_PROOF_2026-08-08.md:[GENHN-HE` — count **19**.
XREF: `GENHN_PROOF_2026-08-08.md:THEOREM GENHN.B` — count **7**.
XREF: `spec/HYPOTHESIS_LEDGER.md:HYP.81` — grep-verified count **10**.

**TEETH:** NONE (status record). The mathematical claim's teeth are at `.15`–`.17`; the machine confirmation of all five μ = 3 stage types is §S9's Q3 (shard 2).

---

### EFF.HE3.s1of2.10  [definition]  — the stage ring, re-carried through L (the `[r1, F7]` correction)

**CANONICAL STATEMENT:** verbatim, lines 149–163 (the stage-ring clause with its `[r1, F7]` in-place correction and the S/D′h naming sentence).

**FORM:** inline sentence with a long bracketed replacement (the note's signature form).

> “R := O[x]/(Φ′) = O[θ] the stage ring ~~(complete DVR, e = e₁, f = f₁,
> residue field K = F_{Q^{f₁}})~~ **[r1, F7: R = O[θ] is an O-ORDER in the
> field L := K₀(θ), not a complete DVR in general — at (e₁,f₁,h) = (1,2,1),
> Φ′ = x²+9 over ℤ₃, R = ℤ₃[3i] ⊊ ℤ₃[i] = O_L is not integrally closed
> (GENHN's erratum [e2-E3 2026-08-09] carries the same correction one level
> up). The invariants are carried by L and its valuation ring O_L:
> e(L/K₀) = e₁, f(L/K₀) = f₁, residue field k_L = K = F_{Q^{f₁}}; dv := e₁·v
> is still ℤ-valued on R (v(A(θ)) ∈ (1/e₁)ℤ needs only (T1)). Every use
> below runs through L, not through R's ring structure: LEMMA HE3-1's norm
> is Nm_{L″/K₀} through the FIELD L″, and residues are read in k_{L}. The
> only site that instantiated "R a complete DVR" as a hypothesis is the
> stage-CS step of §S6.3, which lives in the boxed μ ≥ 4 region; the [r1]
> note there records the O_L re-carrier it needs.]**; S := e₁h (a name kept
> for f₁ = 1 continuity; **the operative threshold everywhere below is
> D′h = e₁f₁h = f₁S** — see the next display).”

**SUPERSESSION KIND: replacement** (the carrier object). `TARGETS: s1of2.10` itself; the rider enumerates its own downstream sites (`.20`'s norm, `.34`'s stage-CS step).

**CONDITIONALITY:** **Unconditional as a correction; display-scope, with one exception the note names.** The exception is precise and honest: “The only site that instantiated "R a complete DVR" as a hypothesis is the stage-CS step of §S6.3, which lives in the boxed μ ≥ 4 region.” So the correction is cosmetic everywhere the μ ≤ 3 headline lives, and substantive exactly inside HE3-BOX-6's territory.
**Two independent corroborations:** (i) GENHN's own `[e2]` ERRATUM E3 carries the identical correction one level up — HE3 says so, and it checks (`GENHN_PROOF` 470–527: “R = Ô[x]/(Φ′) = Ô[θ] is in general the NON-MAXIMAL order Ô[θ], not a DVR”). (ii) HE3-BOX-6 (shard 2) independently rests on the same fact: “**no element of R has non-integer dv** (dv is ℤ-valued on R)”.

**DERIVATION:** The counter-instance is displayed and self-contained.

*Arithmetic audit (rule 22), computed fresh.* `(e₁, f₁, h) = (1, 2, 1)`, `Φ′ = x² + 9` over ℤ₃. Roots: `θ = 3i` with `i² = −1`, so `θ² = −9` ✓ `Φ′(θ) = 0` ✓. `v(θ) = v(3i) = 1 = h/e₁ = 1/1` ✓ matches (T1). `R = ℤ₃[θ] = ℤ₃[3i]`; `O_L = ℤ₃[i]` since `L = ℚ₃(i)` is the unramified quadratic extension (`−1` is a non-residue mod 3, so `x² + 1` is irreducible over F₃ ✓, giving `e = 1, f = 2` ✓ matching `(e₁, f₁) = (1, 2)`). `ℤ₃[3i] ⊊ ℤ₃[i]` ✓ (`i ∉ ℤ₃[3i]`, since every element of `ℤ₃[3i]` has its `i`-component in `3ℤ₃`). **Not integrally closed** ✓ — `i` is integral over ℤ₃ (root of `x²+1`) and lies in `L` but not in `R` ✓. **The counter-instance is exact.**
Second check: `dv := e₁v = v` is ℤ-valued on `R` here since `e₁ = 1` ✓ trivially; the general claim `v(A(θ)) ∈ (1/e₁)ℤ needs only (T1)` follows from `v(θ) = h/e₁` and the slot read ✓.

**RESOLUTION TRACE:** statement 149–163 · downstream sites 480–490 (`.20`'s norm), 1171–1181 (`.34`'s stage-CS) · external corroboration `GENHN_PROOF` 470–527 · no later HE3 append touches it (verified).

XREF: `GENHN_PROOF_2026-08-08.md:ERRATUM E3` — grep-verified count **4**.

**TEETH:** **PROOF-ONLY / `signed vacuity disclosure`.** The battery enumerates in stage coordinates and never consults R's ring structure — the same disclosure GENHN's E3 makes one level up. The note's coverage-hole sentence for the affected region is HE3-BOX-3's “μ ≥ 4 (where LEMMA HE3-4's ramified base-change branch and the stage-CS recursion first bite)” (shard 2, 1309–1310). **Disposition: `transfer audit`** — found by a hostile pass, mirrored from a supplier's identical finding.

---

### EFF.HE3.s1of2.11  [lemma]  — the corrected node and its Ψ-comparison derivation

**CANONICAL STATEMENT:** verbatim, lines 163–237 (the development display with the `[r1, F2]` node, the `[r2]`-re-displayed derivation in three parts, and the LOCUS SCOPING clause).

**FORM:** display (indented ASCII development) + a long bold-headed derivation in three lettered parts, all inside one `[r1, F2]` bracket re-opened at `[r2]`.

> “For f monic on the genre-G opening locus,
>
>     f = Φ′^μ + Σ_{j<μ} A_j Φ′^j ,  deg A_j < D′,
>     ~~dv(A_j) ≥ (μ−j)S + 1~~  **[r1, F2] dv(A_j) ≥ (μ−j)·D′h + 1** ,
>
> **[r1, F2 — the corrected node, re-derived from the locus rather than
> transcribed; derivation re-displayed at [r2] 2026-08-09 (PE2 F-2: the r1
> chain "root values > D′h ⟹ every side's slope > D′h" consumed the
> ATTAINMENT direction it never proved — HE3-0(iii) gives roots → slopes,
> not the converse; the display below routes through the Ψ-comparison,
> this note's own instrument).** Every root ρ of f on the opening locus
> satisfies (T1)/(T2) (LEMMA HE3-0), hence dv(Φ′(ρ)) > D′h (the
> ψ-cancellation computation: res(Φ′(ξ)/π^{f₁h}) = ψ(η_ξ) by the slot read
> at Φ′'s own single entry side, and ψ(η_ρ) = 0 forces the attaining terms
> to cancel — LEMMA HE6-0's argument, one level down). From root values to
> pins:
>
> (i) THE j = 0 PIN, directly: LEMMA HE3-1 at Φ″ = Φ′ gives
> D′·dv(A₀) = Σ_ρ dv(Φ′(ρ)) > D′μ·D′h, so dv(A₀) ≥ μD′h + 1 (dv(A₀) ∈ ℤ).
>
> (ii) THE GENERAL PIN — the Ψ-comparison (the attainment direction). If
> some pin had dv(A_{j*}) ≤ (μ−j*)D′h (1 ≤ j* < μ), the hull right of j*
> would have length-weighted mean slope ≤ dv(A_{j*})/(μ−j*) ≤ D′h, so
> P(F) would own a side of slope λ_low ≤ D′h — a side NO root value
> attains. Such a side is refuted by the two exact reads of
> Ψ(κ, s) := Σ_ρ dv(Φ′_{κ,s}(ρ)) (§S6.1's instrument; the lemmas cited
> consume only dv(Φ″ − Φ′) > D′h and the locus, never this node — no
> circularity). Write n_λ := #{ρ : dv(Φ′(ρ)) = λ}, c_λ := n_λ − D′L_λ.
> COUNT (free): Σ_λ n_λ = D′μ = Σ_λ D′L_λ, i.e. Σ_λ c_λ = 0 (root values
> are slopes, HE3-0(iii); side lengths sum to μ). SAMPLE at a LEGAL
> κ > D′h (κ not a slope, or a slope whose coherent residual has a
> non-root letter s ∈ K^×): the root side reads Σ_λ n_λ·min(λ, κ)
> exactly … ; the
> test side reads D′·h_F(κ) = Σ_λ D′L_λ·min(λ, κ) (LEMMA HE3-1 +
> HE3-1′'s equality clause + the convex duality (★) of §S6.1). Hence
>
>     R(κ): Σ_λ c_λ·min(λ, κ) = 0 ;  R(κ) − κ·COUNT:
>     Σ_{λ < κ} c_λ·(κ − λ) = 0 .                                (∗∗)
>
> At the sample κ = D′h + 1 the slopes < κ are the hypothetical low
> side(s) (where c_λ = −D′L_λ, since n_λ = 0 there) and any MID sides
> (fractional λ ∈ (D′h, D′h+1), horizontal length ℓd ≥ 2). At μ ≤ 3,
> (∗∗) closes the claim: with no mid side it reads
> Σ_low D′L_λ(κ − λ) = 0 with every summand ≥ D′L_λ > 0 — contradiction;
> with a mid side, mid length ≥ 2 plus L_low ≥ 1 forces μ = 3 and the
> polygon exactly {low L = 1, mid L = 2}, COUNT gives c_mid = −c_low =
> D′, and (∗∗) reads D′(κ − λ_low) = D′(κ − λ_mid), i.e. λ_low = λ_mid —
> contradicting λ_low ≤ D′h < λ_mid. So no pin sits on or below the
> D′h-line: dv(A_j) > (μ−j)D′h, i.e. ≥ (μ−j)D′h + 1 since dv is ℤ-valued
> on the A_j.
>
> (iii) HONEST SCOPE + THE FENCE. The sample κ = D′h+1 is legal except in
> the letter-starved corner — D′h+1 a slope whose residual carries no
> non-root letter, needing |K^×| = Q^{f₁} − 1 ≤ d_λ ≤ μ (at μ ≤ 3 only
> (Q,f₁) ∈ {(2,1), (3,1), (2,2)} can be starved). That corner, and μ ≥ 4
> (where one sample does not exhaust the (SEP)-like configurations —
> compare §S6.1), are NOT closed by this display; there the node is
> CONSUMED from GENHN's [r1] ERRATUM 2026-08-08, whose derivation runs
> through LEMMA HE6-3(a) (slope counts with no (SEP) hypothesis and no
> letter consumption — the enlarged test family). The GENHN [r1]
> consumption ALSO stands as independent support for the display as a
> whole: the fence PE2 recorded stays in force.
>
> At f₁ = 1, D′h = S and the old display is unchanged. **LOCUS SCOPING (the
> PE1 leg-A2 member):** a member satisfying the stale S-floors but not the
> D′h-node is OFF-LOCUS — its ambient residual is not ψ^μ — and no display
> of this note admits it; PE1's f = (x²+9)³ + 9(x²+9)² + 81(x²+9) + 729
> (face-value dictionary {(1,2)³} vs PARI σ = {(1,1),(1,1),(1,4)}) is the
> concrete witness that enumerating "stage coordinates + the stale node"
> emits wrong σ at f₁ ≥ 2. The §S8 battery enumerates at f₁ = 1 only, where
> the two nodes coincide.]**”

**SUPERSESSION KIND: replacement** (the node), with the derivation itself **replaced a second time** at `[r2]`. **CHAIN: sealed `S`-node → `[r1]` `D′h`-node with a derivation that assumed attainment → `[r2]` Ψ-comparison derivation. TERMINAL: the `[r2]` derivation.** `TARGETS: s1of2.03` (the §S0 import), `s1of2.13` (DEFINITION 2's node name), `s1of2.20`, `s1of2.24`, `s1of2.26`, `s1of2.27` (every threshold in the note).

**CONDITIONALITY:** **Three fences, all stated by the note, all load-bearing.**
(a) **The derivation closes only at μ ≤ 3.** Part (ii)'s case analysis is explicitly “At μ ≤ 3”; μ ≥ 4 is consumed from GENHN's `[r1]` erratum via HE6-3(a).
(b) **The letter-starved corner is excluded** — and part (iii)'s parenthetical listing that corner is **corrected by the post-PE3 M-1 append** (1591–1618, shard 2), which finds *neither* of its two readings matches the displayed list: under `d_λ ≤ μ` the list must add `(4,1)`; under the in-context `d_λ ≤ μ − 1` the listed `(2,2)` is unreachable. **The frozen fence nonetheless stands** because the consumed GENHN corner `{(2,1),(3,1),(2,2)}` is a superset of the in-context reachable corner `{(2,1),(3,1)}` — conservativity. `SUPERSESSION KIND: counter re-reading`. See `.12`.
(c) **Non-circularity is asserted and checkable**: “the lemmas cited consume only dv(Φ″ − Φ′) > D′h and the locus, never this node”. **This compiler checked it:** LEMMA HE3-1 (`.20`) requires `dv(Φ″ − Φ′) > D′h`; LEMMA HE3-1′ (`.22`) requires `κ > D′h`; the convex duality (★) (`.27`) is pure convexity. **None consumes the node** ✓ — the non-circularity claim holds.

**DERIVATION:** Quoted in full above.

*Arithmetic audit (rule 22), every step recomputed.*
- **(i) The j = 0 pin.** `D′·dv(A₀) = Σ_ρ dv(Φ′(ρ))` by HE3-1 at `Φ″ = Φ′` (so `B₀ = A₀`, since `f ≡ A₀ mod Φ′` ✓ from the development). There are `deg f = D′μ` roots ✓, each with `dv(Φ′(ρ)) > D′h`, so the sum `> D′μ·D′h` ✓, giving `dv(A₀) > μD′h` ✓ hence `≥ μD′h + 1` by integrality ✓. **Correct.**
- **(ii) The mean-slope step.** If `dv(A_{j*}) ≤ (μ−j*)D′h`, the hull segment from `(j*, dv(A_{j*}))` to `(μ, 0)` has mean slope `dv(A_{j*})/(μ − j*) ≤ D′h` ✓, so some side right of `j*` has slope `≤ D′h` ✓ (a mean is bounded by a max).
- **(∗∗).** `R(κ): Σ_λ c_λ min(λ,κ) = 0`; subtracting `κ·COUNT = κ·Σ_λ c_λ = 0` gives `Σ_λ c_λ(min(λ,κ) − κ) = 0`, i.e. `Σ_{λ<κ} c_λ(λ − κ) = 0`, i.e. `Σ_{λ<κ} c_λ(κ − λ) = 0` ✓ **exactly the displayed (∗∗)** (the `λ ≥ κ` terms vanish since `min(λ,κ) = κ` there ✓).
- **No-mid-side case.** Low sides have `n_λ = 0` (no root attains them) so `c_λ = −D′L_λ`, and (∗∗) reads `Σ_low (−D′L_λ)(κ − λ) = 0`, i.e. `Σ_low D′L_λ(κ − λ) = 0`. With `κ = D′h + 1 > λ_low` each summand is `≥ D′L_λ·1 > 0` ✓ **contradiction** ✓.
- **Mid-side case.** A mid side has fractional `λ ∈ (D′h, D′h+1)`, so `ℓ ≥ 2` hence `ℓd ≥ 2` ✓. With `L_low ≥ 1` and `L_mid ≥ 2`, total `≥ 3`, and `Σ L = μ ≤ 3` forces `μ = 3` and exactly `{L_low = 1, L_mid = 2}` ✓. COUNT with only two slopes gives `c_low + c_mid = 0` ✓; `c_low = −D′L_low = −D′` (no root at the low side) so `c_mid = +D′` ✓. (∗∗) over `λ < κ = D′h+1` includes **both** (mid is `< D′h+1` ✓): `c_low(κ − λ_low) + c_mid(κ − λ_mid) = 0` ⟹ `−D′(κ−λ_low) + D′(κ−λ_mid) = 0` ⟹ `λ_low = λ_mid` ✓ **exactly as displayed**, contradicting `λ_low ≤ D′h < λ_mid` ✓.
- **The starved-corner bound.** `|K^×| = Q^{f₁} − 1 ≤ d_λ` with `d_λ ≤ μ = 3` gives `Q^{f₁} ≤ 4`, i.e. `Q^{f₁} ∈ {2,3,4}` ⟹ `(Q,f₁) ∈ {(2,1),(3,1),(2,2),(4,1)}` ✓ — **four pairs, and the display lists three.** The M-1 append (shard 2) reaches the identical conclusion ✓ **this compiler's independent recomputation confirms the append's first bullet exactly.**
- **The LOCUS SCOPING witness.** `f = (x²+9)³ + 9(x²+9)² + 81(x²+9) + 729` over ℤ₃ with `Φ′ = x²+9`, so `A₂ = 9, A₁ = 81, A₀ = 729` and `D′ = 2, h = 1, μ = 3`. Here `e₁ = 1, f₁ = 2` so `S = e₁h = 1` and `D′h = 2`. Stale floors `(μ−j)S + 1`: `A₂ ≥ 2, A₁ ≥ 3, A₀ ≥ 4`. Actual `dv = v` (e₁ = 1): `v(9) = 2 ≥ 2` ✓, `v(81) = 4 ≥ 3` ✓, `v(729) = 6 ≥ 4` ✓ — **satisfies the stale floors.** Corrected floors `(μ−j)D′h + 1`: `A₂ ≥ 3, A₁ ≥ 5, A₀ ≥ 7`. Actual: `2 < 3` ✗ — **violates the corrected node at j = 2** ✓ **exactly as the note claims: the member is OFF-LOCUS.** And the σ disagreement is real: face-value `{(1,2)³}` sums to `3·2 = 6 = deg f` ✓ and PARI's `{(1,1),(1,1),(1,4)}` sums to `1+1+4 = 6` ✓ — both degree-consistent, so only the oracle separates them ✓.
**Every step of the derivation and both witnesses reproduce exactly. No discrepancy.**

**RESOLUTION TRACE:** statement 163–167 · derivation 169–228 (`[r2]` re-display) · scope 218–228 · locus scoping 230–237 · correction sites 1591–1618 (post-PE3 M-1).

XREF: `GENHN_PROOF_2026-08-08.md:ERRATUM 2026-08-08` — grep-verified count **1** (the `[r1]` erratum consumed at part (iii)).
XREF: `HE6_PROOF_2026-08-08.md:LEMMA HE6-3` — count **12**.
XREF: `HE6_PROOF_2026-08-08.md:LEMMA HE6-0` — count **17**.
XREF: `HE3_passPE2_report.md` ✓ present (PE2 F-2, the attainment finding).

**TEETH:** **The PE1 leg-A2 off-locus member is a fired counter-instance** — PARI-exact, and it demonstrates that “enumerating "stage coordinates + the stale node" emits wrong σ at f₁ ≥ 2”. **`signed vacuity disclosure`:** “The §S8 battery enumerates at f₁ = 1 only, where the two nodes coincide” — the note's own sealed instrument is blind to this repair, and says so. **Disposition: planted counter-instance from a hostile pass (fired) + signed vacuity on the sealed leg; the repair's own machine contact is the additive `he3r1_supp.py` P2/P3 sweeps.**

---

### EFF.HE3.s1of2.12  [scope-record]  — §S1 (iii)'s starved-corner parenthetical

**CANONICAL STATEMENT:** verbatim, lines 218–222 (the parenthetical, emitted as its own unit because a dated append corrects it by name and the frozen text is retained).

**FORM:** bracketed rider inside `.11`(iii).

> “The sample κ = D′h+1 is legal except in
> the letter-starved corner — D′h+1 a slope whose residual carries no
> non-root letter, needing |K^×| = Q^{f₁} − 1 ≤ d_λ ≤ μ (at μ ≤ 3 only
> (Q,f₁) ∈ {(2,1), (3,1), (2,2)} can be starved).”

**CONDITIONALITY:** **The parenthetical is WRONG under both of its readings, and the post-PE3 append says so while leaving it frozen.** Quoted from 1591–1607 (shard 2):

> “**M-1 (the §S1 (iii) starved-corner parenthetical), corrected in both
> readings.** … Neither of its two readings matches that list:
>
> * **Under the displayed bound d_λ ≤ μ (= 3):** Q^{f₁} − 1 ≤ 3 ⟺
>   Q^{f₁} ∈ {2, 3, 4} (Q a prime power) ⟺ (Q,f₁) ∈
>   {(2,1), (3,1), (2,2), (4,1)}. The (4,1) omission is CURED here:
>   Q = 4 base rings are legal in this program (the equal-characteristic
>   F₄[[t]] base; PE3's FR3 runs one), and |F₄^×| = 3 ≤ 3.
> * **Under the in-context bound d_λ ≤ μ − 1 (≤ 2):** the sample
>   κ = D′h+1 is consumed only while a hypothetical low side is being
>   refuted, and that low side occupies horizontal length ≥ 1 of the
>   μ-budget, so the κ-side has d_λ ≤ μ − 1 ≤ 2. Then Q^{f₁} − 1 ≤ 2 ⟺
>   Q^{f₁} ∈ {2, 3}, and the reachable corner is (Q,f₁) ∈
>   {(2,1), (3,1)}: the listed (2,2) is UNREACHABLE at this site, and
>   (4,1) is excluded the same way.”

and the conservativity finding at 1609–1618:

> “**Why the frozen fence stands (conservativity, per PE3 M-1).** §S1
> (iii) consumes GENHN's [r1] ERRATUM 2026-08-08 on the LISTED corner
> {(2,1), (3,1), (2,2)} — a superset of the in-context reachable corner
> {(2,1), (3,1)} — so the consumption covers the corner the display
> needs, and the fence PE2 recorded stays in force as written. The
> imprecision is live only for a future consumer re-using the
> parenthetical at a site where the starved side can fill the whole
> polygon (d_λ = μ, e.g. a single-side sampling argument): that consumer
> must take the four-element list of the first bullet, which adds Q = 4
> base rings to the fence.”

`SUPERSESSION KIND: counter re-reading` (the list is re-counted under two explicit bounds) + **scope-pin** (the correction is live only for a future consumer at `d_λ = μ`). **CHAIN: frozen parenthetical → post-PE3 M-1's two readings. TERMINAL: both readings stated; the FROZEN TEXT STANDS because it is conservative for this note's own use.** `TARGETS: s1of2.12`.

**DERIVATION:** The two enumerations are arithmetic; both were independently recomputed at `.11`'s audit and **both reproduce exactly** — `Q^{f₁} ≤ 4` gives four pairs; `Q^{f₁} ≤ 3` gives two.

**RESOLUTION TRACE:** statement 218–222 · correction 1591–1618 (shard 2) · the frozen text is NOT edited (verified).

XREF: `HE3_passPE3_report.md` ✓ present.

**TEETH:** **PE3's FR3 runs a Q = 4 base ring** (`F₄[[t]]`), which is exactly the omitted case — so the omission has machine contact from the pass that found it. **Disposition: `decorrelated-model audit` with an accompanying fresh-instrument leg.** The note's own coverage-hole sentence for Q = 4: HE3-BOX-3 (shard 2) does not list non-prime Q among exercised rows, and PE3's own GREEN run at three disjoint geographies is cited at 1584–1588.

---

### EFF.HE3.s1of2.13  [definition]  — DEFINITION 1 (the stage resolvent and its label set)

**CANONICAL STATEMENT:** verbatim, lines 242–251.

**FORM:** display (blockquoted bold-headed definition). **BYTE-FROZEN under freeze predicate (F3)** — HE6 and HE7 pin it.

> “> **DEFINITION 1 (the stage resolvent and its label set).**
> > F(Y) := Y^μ + Σ_{j<μ} A_j(θ) Y^j ∈ R[Y], monic of degree μ. Its
> > dv-Newton polygon P(F) is the lower hull of {(j, dv(A_j))}_{j≤μ}
> > (A_μ = 1, dv = 0); each side has a dv-slope λ = u/ℓ in lowest terms
> > (u, ℓ > 0), horizontal length L_λ = ℓ·d_λ, and a residual polynomial
> > R_λ ∈ K[Z] of degree d_λ with R_λ(0) ≠ 0. A **label** is a pair
> > (λ, r) with λ a slope of P(F) and r an irreducible factor of R_λ
> > over K; its **stage invariants** are e_s(λ, r) := ℓ,
> > f_s(λ, r) := deg r. Bookkeeping: Σ_{labels} e_s f_s = μ whenever
> > every R_λ is separable.”

**CONDITIONALITY:** **The definition NAMES `R_λ` without constructing it, and that gap is a real defect found at PE2.** It is repaired **adjacent, not inside** — see `.14` — precisely because (F3) forbids editing this display. `SUPERSESSION KIND: license` (the construction pin supplies what the definition presupposes). **CHAIN: DEFINITION 1 (frozen, unpinned `R_λ`) → the `[r2, F1]` construction pin (`.14`). TERMINAL: the definition READ WITH the pin.**
Second: “Bookkeeping: Σ_{labels} e_s f_s = μ **whenever every R_λ is separable**” — the separability proviso is exactly DEFINITION 2's “decided” condition (`.15`), and the two must be read together.

**DERIVATION:** Definition.

*Arithmetic audit (rule 22).* `L_λ = ℓ·d_λ` with `e_s = ℓ`, `f_s = deg r`; summing over labels on one side gives `Σ_r ℓ·deg r = ℓ·d_λ = L_λ` ✓ (since `Σ_r deg r = d_λ` for a separable `R_λ`), and summing over sides gives `Σ_λ L_λ = μ` ✓ (the polygon spans abscissae `0..μ`). **So `Σ_labels e_s f_s = μ` ✓ exactly, and the separability proviso is exactly what makes `Σ_r deg r = d_λ` (without it, repeated factors would be counted once each rather than with multiplicity).** The bookkeeping is correct and its proviso is necessary.

**RESOLUTION TRACE:** statement 242–251 · construction pin 253–286 (`.14`) · consumers' pin `7a95449` ✓ commit · byte-frozen per 129–130.

XREF: `HE6_PROOF_2026-08-08.md:DEFINITION 1` — count **1** (the frozen consumer).
XREF: `HE7_PROOF_2026-08-08.md:HE3-3` — count **2** (HE7's pin covers DEF 1/2 and (★)).

**TEETH:** NONE (definition). Its `R_λ` construction is toothed at `.24` (the witness).

---

### EFF.HE3.s1of2.14  [definition]  — the `[r2, F1]` CONSTRUCTION PIN for R_λ (the coherent assembly)

**CANONICAL STATEMENT:** verbatim, lines 253–286.

**FORM:** bold-headed bracketed rider immediately after DEFINITION 1, containing an indented ASCII construction display.

> “**[r2, F1 2026-08-09 — THE CONSTRUCTION PIN (PE2's twist seam):
> R_λ is the COHERENT (twisted) assembly, and the pin is load-bearing at
> e₁ ≥ 2.** DEFINITION 1 above (byte-frozen: HE6/HE7 pin it) names R_λ
> without displaying a construction, and PE2 exhibited a member where two
> natural constructions differ in factorization type. The construction
> this note and its consumers use is the coherent one — HE6's frozen
> ϖ-CONVENTION; GENHN §S4's coherent-normalizer computation — displayed
> here in this note's n-monomial vocabulary. For the side of P(F) with
> slope λ = u/ℓ in lowest terms, left endpoint (j₀, κ₀), lattice
> abscissas j₀ + ℓk (k = 0, …, d_λ; the line heights κ₀ − ku ∈ ℤ):
>
>     R_λ(Z) := Σ_{k=0}^{d_λ} res( A_{j₀+ℓk}(θ)·n(u)(θ)^k / n(κ₀)(θ) )·Z^k ,
>
> the k-th ratio having dv = (κ₀ − ku) + ku − κ₀ = 0 when the pin sits on
> the line (so its residue exists; a pin strictly above the line
> contributes 0, and the k = 0 read is the vertex read, so R_λ(0) ≠ 0).
> The normalizers M_k := n(κ₀)/n(u)^k form a GEOMETRIC system — powers of
> one fixed height-u monomial against one anchor — which is the entire
> content of "coherent": replacing them by another geometric system of
> the right heights (e.g. HE6's ϖ^{κ₀−ku}, ϖ = x^{i₀}π^{a₀} with
> i₀h + e₁a₀ = 1) changes R_λ by one global nonzero scalar and Z ↦ cZ,
> so root sets rescale and factorization TYPE is unchanged. What is NOT
> in the class is the naive per-slot read
> a_k := res(A_{j₀+ℓk}(θ)/n(κ₀−ku)(θ)): it differs from the coherent
> coefficient by the diagonal η^{W(k)},
> η^{W(k)} = res(n(κ₀−ku)(θ)·n(u)(θ)^k/n(κ₀)(θ)), i.e.
> W(k) = (i₀(κ₀−ku) + k·i₀(u) − i₀(κ₀))/e₁ — exact monomial arithmetic,
> no carry corrections — and W need not be affine in k, so the naive
> assembly can have a DIFFERENT factorization type. The §S3 Remark [r2]
> carries the arithmetic, the machine-adjudicated witness, and why the
> chain's identities hold with the coherent read on both sides. At
> e₁ = 1 every n-monomial is a power of π, the two reads coincide
> (W ≡ 0), and the seam is invisible — which is why the r1 sweeps could
> not see it.]**”

**SUPERSESSION KIND: license** (supplies a construction DEFINITION 1 presupposes) — deliberately NOT a replacement, because (F3) freezes the definition. `TARGETS: s1of2.13`, and by the rider's own pointer list `s1of2.22` (§S3 HE3-1′'s proof), `s1of2.25` (§S4 (ii)), `s1of2.27` (§S5 (b)), `s1of2.32` (§S6.2 HE3-4).

**CONDITIONALITY:** **This is the shard's most consequential mathematical repair.**
(a) **The defect is real and changes σ.** Two natural constructions of `R_λ` differ in factorization TYPE at `e₁ ≥ 2`; the witness (`.24`) shows the naive read predicting a phantom refine where the coherent read gives an irreducible residual and PARI confirms the coherent one.
(b) **The invisibility is explained exactly**: “At e₁ = 1 every n-monomial is a power of π, the two reads coincide (W ≡ 0), and the seam is invisible — which is why the r1 sweeps could not see it.” This is `signed vacuity disclosure` at the level of a whole repair round.
(c) **The “coherent class” is characterized, not just named** — geometric systems `M_k = n(κ₀)/n(u)^k` differ by one global scalar and `Z ↦ cZ`, so root sets rescale and type is preserved. That characterization is what makes the pin usable by consumers who chose a different anchor (HE6's `ϖ^{κ₀−ku}`).
(d) Untouched by the 2026-08-12 A5 wave except through R8-5, which re-points HE3-0's residual sentence to the matching coherent normalizers (1810–1815, shard 2).

**DERIVATION:** Displayed inline and self-contained.

*Arithmetic audit (rule 22), recomputed.*
- **The k-th ratio's dv.** `A_{j₀+ℓk}` sits at line height `κ₀ − ku`; multiplying by `n(u)^k` (height `ku`) and dividing by `n(κ₀)` (height `κ₀`) gives `(κ₀ − ku) + ku − κ₀ = 0` ✓ **exactly as displayed**, so the residue exists ✓.
- **`R_λ(0) ≠ 0`.** The `k = 0` coefficient is `res(A_{j₀}(θ)/n(κ₀)(θ))`, the vertex read, nonzero because `(j₀, κ₀)` is a vertex ON the hull ✓.
- **`deg R_λ = d_λ`.** `k` runs `0..d_λ` ✓, and the `k = d_λ` pin is the side's right endpoint, also on the hull ✓.
- **The naive-vs-coherent diagonal.** Naive `a_k = res(A_{j₀+ℓk}(θ)/n(κ₀−ku)(θ))`; coherent `ã_k = res(A_{j₀+ℓk}(θ)·n(u)(θ)^k/n(κ₀)(θ))`. Ratio `ã_k/a_k = res(n(κ₀−ku)(θ)·n(u)(θ)^k/n(κ₀)(θ))` ✓ **exactly the displayed `η^{W(k)}`.** Its height: `(κ₀−ku) + ku − κ₀ = 0` ✓, so it is a unit residue ✓, and being a monomial ratio in `x^{i}π^{a}` it is a power of `η = res(θ^{e₁}π^{−h})` ✓ with exponent `W(k) = (i₀(κ₀−ku) + k·i₀(u) − i₀(κ₀))/e₁` ✓ (the `x`-exponent balance divided by `e₁`).
- **Affinity failure.** `W` is affine in `k` iff `k ↦ i₀(κ₀ − ku)` is affine, which fails because `i₀(·)` is a mod-`e₁` reduction — a sawtooth. ✓ The note's own instance at `.17` gives `W = (0,0,1,1)` at `k = 0..3` ✓ **manifestly non-affine** (differences `0,1,0`).
- **`e₁ = 1` collapse.** At `e₁ = 1`, `i₀(m) = 0` for every `m` ✓ so `W ≡ 0` ✓ and the two reads coincide ✓.
**Every claim reproduces.**

**RESOLUTION TRACE:** statement 253–286 · arithmetic and witness 588–642 (`.23`, `.24`) · pointer sites 576–582, 655–658, 726–728, 787–793, 983–984 · later touch 1810–1815 (R8-5).

XREF: `HE6_PROOF_2026-08-08.md:LEMMA HE6-1L` — count **4**.
XREF: `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-2` — count **2** (GENHN §S4's coherent-normalizer computation is cited by section; see the NEAR-MISS at `.07` for `ϖ-CONVENTION`).

**TEETH:** **`he3_pe2fresh.py`'s member `ma`** — the twist adjudicator, PARI σ = {(2,4)}, siding with the coherent read. **Re-confirmed at PE3 at three further geographies**: “with the coherent-vs-naive flip machine-adjudicated at each of the three, siding with the coherent read each time” (1586–1588, shard 2). **Disposition: planted mutant (naive vs coherent), fired four times across two passes.**

---

### EFF.HE3.s1of2.15  [definition]  — DEFINITION 2 (the stage read; decided leaves)

**CANONICAL STATEMENT:** verbatim, lines 288–310.

**FORM:** display (blockquoted bold-headed definition with an embedded REPAIR bracket). **Consumer-pinned** (HE6/HE7 pin “DEF 2”), but the `[r1]` tag “renames the node only” per `.06`.

> “> **DEFINITION 2 (the stage read; decided leaves).** The stage read is
> > the (μ, K)-cluster read of F over R in dv-units at the stage-initial
> > node **[r1, F2: formerly "the S-node"; the node height is D′h at
> > f₁ ≥ 2 per §S1 — GENHN's law is stated as the read AT THE NODE,
> > whatever its height]** (GENHN.A(v)). A leaf ℓ is **decided** iff (a) the read TERMINATES with
> > every TERMINAL residual polynomial separable — repeated residual roots
> > are allowed at intermediate nodes, where they are exactly what drives
> > the stage-α refinement — and (b) every event along the history is
> > lift-stable at the stage window (GENHN-3(a));
> > [**REPAIR, PE1 finding 5:** an earlier version of this definition
> > demanded separability of every residual CONSULTED, which contradicted
> > §S6.3's stage-α step (that step handles a residual root of multiplicity
> > m ≥ 2, i.e. a non-separable consulted residual) and would have made the
> > induction range over impossible histories. Separability is required at
> > the TERMINAL nodes only — Ore-regularity at the leaf. No mathematical
> > content changes; §S6.3's steps are unaffected.] the leaf's **stage
> > type** is the multiset
> > τ_stage(ℓ) := {(e_s^{(i)}, f_s^{(i)})}_{i=1..k}, Σ_i e_s^{(i)}f_s^{(i)}
> > = μ, obtained by composing the labels of the terminal keys along the
> > history: a stage-α refine (recentering the key at a K-rational
> > residual root) contributes nothing on its own, a stage-CS event of
> > inner data (e₁′, f₁′, μ′) contributes the inner types multiplied by
> > (e₁′, f₁′).”

**CONDITIONALITY:**
(a) **The `[r1, F2]` node rename is the only edit** — and it is a rename, not a content change, exactly as `.06`'s consumer trace asserts (“DEF 2 renamed node only”).
(b) **The PE1-finding-5 REPAIR is a genuine internal-contradiction fix**: the old definition demanded separability of every *consulted* residual, which contradicted §S6.3's own stage-α step. The repair scopes separability to TERMINAL nodes. **The note's claim that “No mathematical content changes” is checkable and holds** — §S6.3's stage-α step handles `m ≥ 2` and is unaffected ✓ (`.34`).
(c) **DEFINITION 2's “decided” is later shown to be a RECURSIVE condition, not a one-node one** — R8-1 (1634–1689, shard 2) rewrites LEMMA HE3-5's criterion recursively and states: “The history is DECIDED exactly when: 1. every terminal residual polynomial is separable; and 2. at every nonterminal node ν, every recentered value consulted there is either read exactly below c_ν, or …”. **DEFINITION 2 already says (a) terminal separability and (b) lift-stability at *every* event, so it is consistent with R8-1** — what R8-1 corrects is HE3-5's *bound*, not this definition. Recorded because the two could be conflated. `SUPERSESSION KIND: none applied to this unit`; the correction lands at `.37`.
(d) `.38`'s Interpretation asserts “The theorem's hypothesis "DECIDED leaf" is precisely LEMMA HE3-5's condition” — which R8-1 makes true only in the recursive reading. See OPEN-CALL 4.

**DERIVATION:** Definition.

*Arithmetic audit (rule 22).* `Σ_i e_s^{(i)} f_s^{(i)} = μ` — consistent with `.13`'s bookkeeping ✓, and the composition rule (“a stage-CS event of inner data (e₁′, f₁′, μ′) contributes the inner types multiplied by (e₁′, f₁′)”) preserves it: an inner system of multiplicity `μ′` contributes `Σ e_s′f_s′ = μ′` inner pairs, scaled by `e₁′f₁′`, giving `e₁′f₁′μ′` ✓ — and `e₁′f₁′μ′ ≤ μ` is exactly GENIND.A(IV)'s budget ✓ (`.16`). A stage-α refine contributes nothing ✓ (it recenters, it does not split). **The multiset arithmetic closes.**

**RESOLUTION TRACE:** statement 288–310 · node source 163–237 (`.11`) · stage-α consistency 1149–1169 (`.34`) · recursive re-reading 1634–1689 (shard 2, R8-1).

XREF: `GENHN_PROOF_2026-08-08.md:GENHN.A(v)` — count **6**.
XREF: `GENHN_PROOF_2026-08-08.md:GENHN-3(a)` — count **11**.

**TEETH:** **HE-BND** — the battery's decided/undecided profile vs window (shard 2, §S9) measures exactly this definition's condition (b). **Disposition: measurement.** HE3-BOX-5 item (4) (shard 2) names the open question: “whether "decided leaf" as defined in DEFINITION 2 coincides exactly with LEMMA HE3-5's window condition on every row (the battery measures both)”.

---

### EFF.HE3.s1of2.16  [theorem]  — THEOREM HE3.A (the stage-σ recursion)

**CANONICAL STATEMENT:** verbatim, lines 312–331.

**FORM:** display (blockquoted bold-headed theorem with an indented ASCII dictionary and a dependency paragraph).

> “> **THEOREM HE3.A (THE STAGE-σ RECURSION — the mechanism).** Let
> > G be any composite-stage genre, ℓ any DECIDED stage leaf with stage
> > type τ_stage(ℓ) = {(e_s^{(i)}, f_s^{(i)})}_i, and let f be any lift
> > on ℓ with disc(f) ≠ 0. Then f factors over O into exactly k monic
> > irreducible factors, in bijection with the members of τ_stage(ℓ),
> > the i-th of degree D′·e_s^{(i)}f_s^{(i)} with
> >
> >     e = e₁·e_s^{(i)} ,   f = f₁·f_s^{(i)}      (i = 1, …, k),
> >
> > i.e. σ(f) = {(e₁e_s^{(i)}, f₁f_s^{(i)})}_i as blocks relative to the
> > ambient. Equivalently: **the σ-decision at a multiplicity-μ stage is
> > the σ-decision at DEGREE μ over the stage ring R, transported by the
> > multiplicative re-basing (e, f) ↦ (e₁e, f₁f).**
> >
> > The proof needs, beyond the pinned suppliers: LEMMA HE3-1 (the
> > resultant identity), LEMMA HE3-2 (recentering valuations), LEMMA
> > HE3-3 (the slope count Ψ-inversion), LEMMA HE3-4 (the residue peel +
> > unramified base change), and — only when the leaf's history contains
> > a stage-CS event of inner multiplicity μ′ — THEOREM HE3.A itself at
> > multiplicity μ′ ≤ μ/2.”

**CONDITIONALITY:** **The theorem is unconditional at μ ≤ 3 and conditional at μ ≥ 4, and the conditionality has MOVED since it was written.**
(a) At the time of writing, LEMMA HE3-4 carried **two** boxed base-change branches (§S6.2, `.33`: “Both branches below are therefore to be read as BOXED (HE3-BOX-6), not proved”), while §S1 and HE3-BOX-6 said only branch (ii) was boxed — **an internal contradiction the A5 wave named**. R8-2 (shard 2) resolves it by PROVING branch (i) as LEMMA HE3-4U. `SUPERSESSION KIND: license`.
(b) The dependency list names HE3-4 as “the residue peel + unramified base change”; after R8-2 the unramified half is proved, so the list is now accurate rather than aspirational.
(c) **The theorem's own recursion is well-founded by GENIND.A(IV)** — `μ′ ≤ μ/2 < μ` — which is `.16`'s displayed descent and `.32`'s proof.
(d) “over the stage ring R” inherits `.10`'s `L`/`O_L` re-carrier at the stage-CS step only.
(e) `disc(f) ≠ 0` is a standing hypothesis, used at `.30` (“disc f ≠ 0 gives Φ″ ∤ f/Φ″”) and at `.34`.

**DERIVATION:** §S6.3 (1092–1205), quoted at `.34`. Structure: induct on the number of stage-α refines and stage-CS events; base = the depth-0 decided read (labels partition the roots by HE3-0 + HE3-4 + the consistency check; each class is Galois-stable by HE3-6; a Galois-stable set of size N with all orbit sizes ≥ N is one orbit); stage-α step; stage-CS step; embedded genres.

*Arithmetic audit (rule 22).* Degree bookkeeping: `Σ_i D′·e_s^{(i)}f_s^{(i)} = D′·Σ_i e_s^{(i)}f_s^{(i)} = D′μ = deg f` ✓ (using `.13`'s bookkeeping). Per factor, `e·f = (e₁e_s)(f₁f_s) = D′e_sf_s` = the factor's degree ✓ — so each factor's `(e,f)` exhausts its degree, which is exactly what forces equality from the inequalities `e ≥ e₁e_s`, `f ≥ f₁f_s` ✓. **The dictionary is degree-consistent and the forcing step is tight.**

**RESOLUTION TRACE:** statement 312–331 · proof 1092–1205 · dependency corrections 1691–1734 (R8-2), 1736–1772 (R8-3), 1774–1793 (R8-4).

XREF: `GENIND_PROOF_2026-08-08.md:GENIND.A(IV)` — count **5**.

**TEETH:** **HE-SIG** — “PARI `sig(f,p)` = factorpadic-200 + idealprimedec, the pinned w12_checks question, against the HE3.A dictionary”, scored at §S9 Q3: **947 PARI jobs, 0 bad, ALL FIVE μ = 3 stage types realized and confirmed** (shard 2). Planted mutant **HE-T-SIG**: “6/6 flipped dictionaries caught by PARI on each of the two rows”. **Disposition: executable regression against an independent oracle + planted mutant, both fired.** The headline row is the 3-label type `(1,1)+(1,1)+(1,1)` — “**25 sextics that split into three ramified quadratics, each PARI-confirmed** — the first machine confirmation of a 3-label stage σ anywhere in this program.”

---

### EFF.HE3.s1of2.17  [theorem]  — COROLLARY HE3.B ([GENHN-HE(μ)] for all μ) with its `[r1]` headline rescope

**CANONICAL STATEMENT:** verbatim, lines 333–367.

**FORM:** display (blockquoted bold-headed corollary containing a bold-headed rescope block and an indented ASCII descent display).

> “> **COROLLARY HE3.B ([GENHN-HE(μ)]: UNCONDITIONAL for μ ≤ 3 — the
> > first-live case, degrees n ≤ 7 — and for μ ≥ 4 conditional on ONE named
> > branch, HE3-BOX-6).**
> > **[r1 HEADLINE RESCOPE, 2026-08-09.** PE1 struck this headline at
> > f₁ ≥ 2 (its two CRITICALs: the peel letters reached only F_Q ⊊ K, and
> > the S = e₁h thresholds were false in the band S < κ ≤ D′h). The claim
> > SURVIVES WITH THE CORRECTED MACHINERY of this [r1] round, on which the
> > μ ≤ 3 proof now runs at every f₁: LEMMA HE3-1L letters over the full
> > K^× (F1), the D′h thresholds re-derived from the locus (F2), LEMMA
> > HE3-6 discharging the equivariance gap the old text ASSUMED at f₁ ≥ 2
> > (F3 — "unconditional" was internally contradicted by that assumption;
> > it no longer is), the ℓ ≥ 2 residue read (F6), and the [r1-N1]
> > consecutive-triple supplement. "UNCONDITIONAL" continues to mean: no
> > assumed hypothesis inside this note's mathematics at μ ≤ 3. It does
> > NOT upgrade the grade: the note is at attempt 0/2 and every
> > consequence carries HE3-BOX-1's supplier-stack conditionality.]**
> > [GENHN-HE(μ)] holds for every μ ≥ 2, hence for every μ ≥ 3 — with the
> > single reservation that at μ ≥ 4 the proof invokes LEMMA HE3-4's
> > ramified-base-change branch (ii), whose stated justification is
> > insufficient (HE3-BOX-6, found by this unit's own review; repair route
> > named there). At μ ≤ 3 that branch is unreachable (it needs a side with
> > ℓ ≥ 2 and residual degree ≥ 2, hence length ℓd ≥ 4 ≤ μ), so μ = 2 and
> > μ = 3 are unconditional. Proof:
> > induction on μ. THEOREM HE3.A at multiplicity μ requires HE3.A at
> > the inner multiplicities μ′ of stage-CS events occurring inside a
> > DEGREE-μ system. By GENIND.A(IV) such an event has inner key degree
> > e₁′f₁′ ≥ 2 and inner multiplicity μ′ ≥ 2 with e₁′f₁′μ′ ≤ μ, hence
> >
> >     μ′ ≤ μ/2 < μ      (STRICT DESCENT),
> >
> > and in particular μ ≥ 4 is necessary for any stage-CS event at all.
> > Therefore μ = 2 and μ = 3 are **composite-stage-free**: their leaves'
> > histories consist of order-1 reads and stage-α refines only, so HE3.A
> > at μ ∈ {2, 3} needs no recursive input and is proved outright by
> > §S3–S6. Induction then gives every μ. ∎”

**CONDITIONALITY:** **Four layers, and the corollary's own definition of “UNCONDITIONAL” is the key to reading it.**
(a) **The rescope block defines the word**: “"UNCONDITIONAL" continues to mean: **no assumed hypothesis inside this note's mathematics at μ ≤ 3**. It does NOT upgrade the grade”. So unconditional ≠ accepted, and the note says so.
(b) **`STALE-SELF-DESCRIPTION`** on “the note is at attempt 0/2” — PE3 moved it to 1/2.
(c) **The μ ≥ 4 reservation is NARROWED by R8-2** to branch (ii) alone; §S6.2's contradicting “BOTH … BOXED” is superseded. **CHAIN: HE3.B's “ONE named branch” → §S6.2's “BOTH” (internal contradiction) → R8-2 proves (i) → “branch (ii) alone is BOXED”. TERMINAL: R8-2.**
(d) **The `n ≤ 7` claim needs `D′ ≥ 2`**, supplied by R8-3 (recorded at `.01`(b)). Before R8-3 the implication `μ ≥ 4 ⟹ n ≥ 8` was unjustified at `D′ = 1`.
(e) The rescope block's own list of five repairs is checkable: F1 → `.21`; F2 → `.11`; F3 → `.35`; F6 → `.25`/`.26`; N1 → `.30`. **All five located** ✓.

**DERIVATION:** Quoted inline: induction on μ with GENIND.A(IV)'s descent; re-run at `.36`.

*Arithmetic audit (rule 22), recomputed.*
- **Strict descent.** `e₁′f₁′ ≥ 2`, `μ′ ≥ 2`, `e₁′f₁′μ′ ≤ μ` ⟹ `μ′ ≤ μ/(e₁′f₁′) ≤ μ/2` ✓, and `μ/2 < μ` for `μ > 0` ✓.
- **`μ ≥ 4` necessary for any stage-CS event.** From `e₁′f₁′μ′ ≤ μ` with `e₁′f₁′ ≥ 2, μ′ ≥ 2`: `μ ≥ 2·2 = 4` ✓.
- **Branch (ii) unreachable at μ ≤ 3.** It needs `ℓ ≥ 2` and `d ≥ 2`, so the side length `ℓd ≥ 4`; since `Σ_λ L_λ = μ`, this forces `μ ≥ 4` ✓ **exactly the displayed “length ℓd ≥ 4 ≤ μ”.**
- **`n ≤ 7`.** `n = D′μ`; at `μ ≤ 3` and `D′ ≥ 2`, `n ≤ 3D′`… the unconditional range is stated as `n ≤ 7`, which comes from the *contrapositive*: the conditional region needs `μ ≥ 4` AND `D′ ≥ 2`, so `n = D′μ ≥ 8` ✓, hence every `n ≤ 7` is unconditional ✓. **But at `D′ = 1` a genre with `μ ≥ 4` has `n = μ ≥ 4 ≤ 7` — inside the claimed unconditional range while being in the conditional multiplicity region.** That is exactly the gap R8-3 closes with LEMMA HE3-4D1 ✓ **this compiler's independent recomputation confirms the A5 finding.**
**Every step reproduces, and the one gap the audit surfaces is the one R8-3 names.**

**RESOLUTION TRACE:** statement 333–367 · proof inline + 1207–1214 (`.36`) · correction sites 1691–1734 (R8-2), 1736–1772 (R8-3), 1579–1583 (grade).

XREF: `GENIND_PROOF_2026-08-08.md:GENIND.A(IV)` — count **5**.
XREF: `GENHN_PROOF_2026-08-08.md:[GENHN-HE` — count **19**.
XREF: `HE3_PROOF_2026-08-08.md:HE3-BOX-6` — self-count **12** (the box is named twelve times in its own note).

**TEETH:** **PROOF-ONLY at μ ≥ 4** — HE3-BOX-3 (shard 2): “NOT exercised by machine: … μ ≥ 4 (where LEMMA HE3-4's ramified base-change branch and the stage-CS recursion first bite)”. At μ ≤ 3 the dictionary is toothed by HE-SIG (947 PARI jobs, all five types).

---

### EFF.HE3.s1of2.18  [theorem]  — COROLLARY HE3.C (the program consequence)

**CANONICAL STATEMENT:** verbatim, lines 369–378.

**FORM:** display (blockquoted bold-headed corollary).

> “> **COROLLARY HE3.C (the program consequence).** In THEOREM GENHN.B
> > the clause list {[GENHN-HE(μ ≥ 3)]} is discharged OUTRIGHT for every
> > degree n ≤ 7, and for n ≥ 8 is reduced to the single branch of
> > HE3-BOX-6. Hence [GENIND-H(n)] holds for every n with no open σ clause
> > beyond that branch, and
> > the FULL UNIFORMITY THEOREM (one R_τ ∈ ℚ(q) per splitting type at
> > every degree, every prime power, both characteristics, Σ_τ R_τ = 1)
> > is conditional exactly on {GENHN's S9 compression/coverage boxes} ∪
> > {the hostile-arc grade stack} — the mathematics is composed-complete.
> > (Grade discipline: HE3 is itself at attempt grade 0/2; see §S7.)”

**CONDITIONALITY:** **This is the note's furthest-reaching claim and it is the one most in tension with the corpus at HEAD.**
(a) **“conditional exactly on {GENHN's S9 boxes} ∪ {arc stack}” omits `[GENHN-TOW-1]`.** GENHN's own corrected conditionality display (its lines 352–371, compiled at `spec/EFF-GENHN-s1of2.md` `.18`) reads: at `n ≥ 8`, P(n) rests on `{[GENHN-HE(μ ≥ 3)]} ∪ {[GENHN-TOW-1]} ∪ {S9 boxes} ∪ {arc stack}` — and `[GENHN-TOW-1]` **is** one of GENHN's §S9.1 boxes, so the phrase “GENHN's S9 compression/coverage boxes” arguably covers it. **But `[GENHN-TOW-1]` is not a compression or coverage box — it is a MATHEMATICS box** (GENHN's own §S9.2 files it under “MATHEMATICS (new theorems needed)” as item 2b). Under GENHN's own taxonomy, HE3.C's phrase under-describes it. Recorded as source defect 3; the compiler does not rewrite the clause.
(b) **`STALE-SELF-DESCRIPTION`** on “attempt grade 0/2” (now 1/2).
(c) **The whole corollary rides `.09`'s unlanded-discharge status**: GENHN records `[GENHN-HE(μ ≥ 3)]` as open.
(d) **“the mathematics is composed-complete”** is a programme-level claim, not a theorem; it inherits every conditionality above.

**DERIVATION:** Composition of `.17` with GENHN.B; no fresh mathematics.

**RESOLUTION TRACE:** statement 369–378 · GENHN-side display `GENHN_PROOF` 352–371 · grade 1579–1583 (shard 2).

XREF: `GENHN_PROOF_2026-08-08.md:THEOREM GENHN.B` — count **7**.
XREF: `GENIND_PROOF_2026-08-08.md:GENIND-H(n)` — count **7**.
XREF: `GENHN_PROOF_2026-08-08.md:[GENHN-TOW-1]` — grep-verified count **19**.

**TEETH:** NONE (programme claim).

---

### EFF.HE3.s1of2.19  [scope-record]  — §S2, the mechanism and why the μ = 2 argument stops

**CANONICAL STATEMENT:** verbatim, lines 382–444 (the whole of §S2: the two-line mechanism, the GENHN.C analysis, the failure at μ ≥ 3, and the replacement).

**FORM:** `##`-headed section body, four bold-headed paragraphs with two indented ASCII displays.

> “**The two-line mechanism.** (1) Every root ρ of f satisfies the same
> two transported facts (T1)/(T2) as a root of Φ′, so by the SLOT LEMMA
> the polynomial relation satisfied by y_ρ := Φ′(ρ) over L_ρ := K₀(ρ),
> namely Y^μ + Σ_j A_j(ρ)Y^j = 0, has *exactly the stage polygon* and
> *Frobenius-conjugates of the stage residuals*; hence each root of f
> carries a LABEL (λ, r), and its label forces e₁e_s | e(L_ρ) and
> f₁f_s | f(L_ρ). (2) The label CLASS SIZES are pinned by the family of
> resultant valuations v(Res(f, Φ′_t)) over test keys Φ′_t = Φ′ − C
> **[r1, F1/F8: C the letter-carriers of LEMMA HE3-1L, reaching ALL of
> K^× at the test heights; the old display ŝ·n(κ) reached only F_Q^×]**
> — the ultrametric distance function from f's root multiset to the test
> points — and they come out to exactly D′e_sf_s, whereupon the degree
> count Σ_labels D′e_sf_s = D′μ = deg f forces each class to be a single
> Galois orbit with e = e₁e_s, f = f₁f_s exactly.
>
> **Why GENHN.C's μ = 2 argument stops.** GENHN.C (§S7 there) reads the
> Y-quadratic and closes each case with ONE of two devices: (a) the label
> set is a SINGLETON …; or (b) the label set has
> exactly TWO members …, in which case the two class sizes n₁, n₂
> are determined by the two linear equations
>
>     n₁ + n₂ = D′μ ,      n₁λ₁ + n₂λ₂ = D′·dv(A₀)
>
> (root count + the single resultant identity Σ_ρ dv(Φ′(ρ)) = D′dv(A₀)),
> a 2 × 2 system with λ₁ ≠ λ₂, hence invertible.
>
> At μ = 2 those are the only possibilities: Σ e_sf_s = 2 admits only
> {(2,1)}, {(1,2)}, {(1,1),(1,1)}. **At μ ≥ 3 the label set can have
> THREE or more members** — Σ e_sf_s = 3 admits {(1,1),(1,1),(1,1)} —
> and then the two identities are underdetermined; worse, if the three
> labels sit on the SAME side (one slope λ, residual = three distinct
> K-rational roots) the second equation degenerates to λ times the
> first and carries **zero** information. That is the exact failure, and
> it is the first-live μ = 3 configuration at n = 6 (a sextic splitting
> into three ramified quadratics when e₁ = 2, f₁ = 1). Battery tooth
> HE-T-UNDET certifies the underdetermination numerically.
>
> **What replaces it.** The single identity is replaced by the whole
> FAMILY of identities indexed by test keys: define, for integer κ and
> a letter s ∈ K^×,
>
>     Ψ(κ, s) := Σ_ρ dv(Φ′_{κ,s}(ρ)) = D′·dv_t(f mod Φ′_{κ,s})
>     where Φ′_{κ,s} := Φ′ − C_{κ,s}   [r1: C_{κ,s} the LEMMA HE3-1L
>     letter-carrier for s at height κ; formerly Φ′ + ŝ·n(κ), which
>     carries only F_Q-letters and the opposite sign].
>
> For s generic at height κ (not a residual root of the height-κ side)
> Ψ(κ, s) = D′·min_j(dv(A_j) + jκ) — the polygon's support function
> scaled by D′ — and on the root side Ψ(κ, s) = Σ_labels n_λ·min(λ, κ).
> Sampling κ over the integers inverts (LEMMA HE3-3) to give the slope
> counts n_λ = D′L_λ; recentering at each K-rational residual root and
> re-running the same inversion peels the residue classes (LEMMA HE3-4),
> with unramified base change supplying letters for the non-rational
> residual factors. Two features of this replacement are worth naming:
> it is *characteristic-free* (no binomial expansion is used — only the
> substitution identity for residual polynomials), and it is *degree-
> generic* (nothing in it caps μ), which is why the same argument closes
> the whole family rather than one more case.”

**CONDITIONALITY:**
(a) **The “characteristic-free” claim is qualified by `.27`'s own PE1-finding-4 repair**: binomial coefficients DO appear in the recentering expansion; what is characteristic-free is the *residue-level* statement. `.27` says so explicitly. The §S2 sentence “no binomial expansion is used” is therefore **loose as written** — the expansion is used, but only through its images in K. Source defect 4.
(b) **“Sampling κ over the integers inverts (LEMMA HE3-3)” is FALSE without (SEP)** — `.29`'s PE1-finding-3 repair supplies the counterexample and the hypothesis. §S2's summary predates the qualification. Source defect 5.
(c) **“with unramified base change supplying letters for the non-rational residual factors”** — that branch was boxed at §S6.2 (`.33`) and is PROVED only at R8-2. `SUPERSESSION KIND: license`.
(d) The `[r1, F1/F8]` bracket inside (2) is already-landed.

**DERIVATION:** Programme summary; the machinery is `.20`–`.32`.

*Arithmetic audit (rule 22) of the μ = 2 enumeration and the degeneracy claim.*
- `Σ e_sf_s = 2` over multisets of pairs with `e_s, f_s ≥ 1`: `{(2,1)}` ✓, `{(1,2)}` ✓, `{(1,1),(1,1)}` ✓ — **exactly three** ✓ as displayed.
- `Σ e_sf_s = 3` admits `{(3,1)}, {(1,3)}, {(1,1),(2,1)}, {(1,1),(1,2)}, {(1,1),(1,1),(1,1)}` — **five** ✓ **exactly the five types §S9's Q3 table lists** (shard 2) ✓ **cross-check passes.**
- **The degeneracy.** If all three labels sit on one side of slope λ, then `n₁λ₁ + n₂λ₂ + n₃λ₃ = λ(n₁+n₂+n₃) = λ·D′μ`, so the second equation is `λ` times the first ✓ **carries zero information** ✓ exactly as claimed.
- **HE-T-UNDET's count.** §S9 Q5 (shard 2) reports “**10** nonnegative solutions (all class sizes multiples of D′e_sf_s = 2, summing to D′μ = 6)”. Recompute: solutions `(n₁,n₂,n₃)` with each a nonnegative multiple of 2 summing to 6, i.e. `(a,b,c)` nonnegative integers with `a+b+c = 3` (after dividing by 2): the count is `C(3+2, 2) = C(5,2) = 10` ✓ **exactly 10** ✓ and the truth `(2,2,2)` corresponds to `(1,1,1)` ✓. The examples given — `(6,0,0), (4,2,0), (2,4,0)` — are `(3,0,0), (2,1,0), (1,2,0)` ✓ all valid ✓. **The tooth's number is exactly right.**

**RESOLUTION TRACE:** statement 382–444 · qualifications 757–776 (`.27`'s char repair), 892–935 (`.29`'s (SEP)), 1691–1734 (R8-2) · tooth 1448–1455 (shard 2).

XREF: `GENHN_PROOF_2026-08-08.md:THEOREM GENHN.C` — count **11**.
XREF: `HE3_PROOF_2026-08-08.md:HE-T-UNDET` — self-count **3**.

**TEETH:** **HE-T-UNDET — “fired, and it is the mechanism certificate”** (shard 2, §S9 Q5): the μ = 2 method is not merely unproven at μ = 3 but “**information-theoretically insufficient**”, with the 10 spurious solutions exhibited. **Disposition: planted mutant / measurement; fired.** This is the strongest possible justification for the note's existence and it is machine-certified.

---

### EFF.HE3.s1of2.20  [lemma]  — LEMMA HE3-1 (the resultant identity at every test key)

**CANONICAL STATEMENT:** verbatim, lines 450–478 (the lemma with its embedded `[r1, F2]` band correction and counter-instances, and the two displayed conclusions).

**FORM:** display (blockquoted bold-headed lemma with an embedded bold-headed correction block and an indented ASCII identity).

> “> **LEMMA HE3-1.** Let Φ″ ∈ O[x] be monic of degree D′ with Φ″ ≡ Φ′
> > modulo terms of dv-height ~~> S~~ **[r1, F2] > D′h** (so Φ″ is again
> > irreducible with e = e₁, f = f₁, roots satisfying (T1)/(T2), and the
> > field L″ := K₀(θ″) again has e = e₁, f = f₁, residue field K **[r1,
> > F7: carrier through the field L″, not "R″ a complete DVR"]**). Write
> > f ≡ B₀ mod Φ″ with deg B₀ < D′. Then
> >
> > **[r1, F2 — WHY D′h AND NOT S; the old parenthetical is FALSE in the
> > band S < dv ≤ D′h, with exact counter-instances.]** At (e₁,f₁,h) =
> > (1,2,1), Φ′ = x²+9 over ℤ₃ (D′h = 2, S = 1), the height-2
> > perturbations Φ″ = x²+18 (SPLIT over ℚ₃: root residues ±1 ∉ roots(ψ),
> > ψ = y²+1) and Φ″ = x²+27 (RAMIFIED, (T1) broken) both violate the old
> > display — PE1 leg A1, PARI-exact. Re-derivation of the corrected
> > clause: dv(w) > D′h for w := Φ″ − Φ′ means e₁v(w_i) + ih > D′h for
> > each coefficient, i.e. v(w_i) > (D′−i)h/e₁ = the height of Φ′'s
> > single entry side at abscissa i; so Φ″ has the SAME entry polygon
> > (one side, slope h/e₁, length D′) and the SAME residual ψ
> > (irreducible, degree f₁, lattice length f₁), whence Φ″ is irreducible
> > with e = e₁, f = f₁, its roots satisfy (T1)/(T2), and k_{L″} ⊇
> > K = F_Q(η). At dv(w) = D′h the perturbation reaches ψ's own pins and
> > the two counter-instances above are exactly what happens. At f₁ = 1,
> > S = D′h and the band S < dv ≤ D′h is empty — the sealed battery's
> > geography is unaffected.
> >
> >     Σ_{ρ : f(ρ) = 0} dv(Φ″(ρ)) = D′ · dv(B₀)        (HE3-1a)
> >
> > and B₀(θ″) = F(−w)(θ″) where w := Φ″ − Φ′ and F is the stage
> > resolvent of DEFINITION 1, θ″ any root of Φ″. Consequently the left
> > side is computable from the stage read data alone.”

**CONDITIONALITY:**
(a) **`[r1, F2]`** — the hypothesis band is corrected from `> S` to `> D′h`, **with two exact counter-instances at the boundary**. `SUPERSESSION KIND: replacement`.
(b) **`[r1, F7]`** — the carrier is the field `L″`, not a DVR `R″`. `SUPERSESSION KIND: wording-rider`, and the norm computation in the proof is re-routed accordingly.
(c) The consumer trace (`.06`) records that **HE6 consumes HE3-1 only at heights `κ > D′h`**, so the band repair *validates* HE6's stricter usage rather than breaking it.
(d) Untouched by the A5 wave.

**DERIVATION:** Lines 480–490, quoted:

> “*Proof.* Both f and Φ″ are monic, so
> Res(f, Φ″) = Π_ρ Φ″(ρ) = ± Π_{θ″} f(θ″) = ± Nm_{L″/K₀}(B₀(θ″)) (the
> second equality is the standard resultant symmetry; the third is
> f(θ″) = B₀(θ″); **[r1, F7]** the norm is through the FIELD L″ — Φ″
> irreducible makes the θ″ a full conjugate set — so no DVR-ness of
> O[x]/(Φ″) is consulted). Taking v: Σ_ρ v(Φ″(ρ)) = v(Nm B₀(θ″)) =
> D′·v(B₀(θ″)) = f₁·dv(B₀) (v is Galois-invariant, so v(Nm x) =
> [L″:K₀]·v(x)). Multiply by e₁ to convert the left side to
> dv: Σ_ρ dv(Φ″(ρ)) = e₁f₁·dv(B₀) = D′·dv(B₀). For the second clause,
> Φ′ ≡ −w mod Φ″, so f = Φ′^μ + ΣA_jΦ′^j ≡ (−w)^μ + ΣA_j(−w)^j = F(−w)
> mod Φ″. ∎”

*Arithmetic audit (rule 22), every step recomputed.*
- **The norm chain.** `[L″ : K₀] = deg Φ″ = D′` ✓ (Φ″ irreducible). `v(Nm_{L″/K₀} x) = [L″:K₀]·v(x) = D′·v(x)` ✓ for the Galois-invariant extension of `v` ✓.
- **The dv conversion.** `Σ_ρ v(Φ″(ρ)) = D′·v(B₀(θ″))`. Now `dv := e₁v`, so `Σ_ρ dv(Φ″(ρ)) = e₁·D′·v(B₀(θ″)) = D′·(e₁v(B₀(θ″))) = D′·dv(B₀)` ✓ **matches (HE3-1a).** *But the displayed intermediate reads `D′·v(B₀(θ″)) = f₁·dv(B₀)`*: check — `f₁·dv(B₀) = f₁·e₁·v(B₀) = D′·v(B₀)` ✓ **correct**, since `D′ = e₁f₁` ✓. The display is right; the two-step presentation is just unusual.
- **The band condition.** `dv(w) > D′h` with `w = Σ w_i x^i` means `min_i(e₁v(w_i) + ih) > D′h` ✓, i.e. `e₁v(w_i) + ih > D′h` for each `i` ✓, i.e. `v(w_i) > (D′h − ih)/e₁ = (D′−i)h/e₁` ✓ **exactly the displayed “the height of Φ′'s single entry side at abscissa i”** ✓ (Φ′'s side runs from `(0, D′h/e₁)` to `(D′, 0)` in `v`-units, height at `i` being `(D′−i)h/e₁` ✓).
- **Counter-instance 1: `Φ″ = x² + 18` over ℤ₃.** `Φ′ = x²+9`, so `w = 9`, `v(9) = 2`, `dv(w) = e₁v = 1·2 = 2 = D′h` ✓ **exactly at the boundary** ✓ (not `> D′h`). Is it SPLIT? `x² + 18 = x² + 18`; over ℚ₃, `−18 = −2·9`, so roots are `±3√(−2)`; `−2 ≡ 1 (mod 3)` is a square mod 3 ✓, so `√(−2) ∈ ℤ₃` ✓ and the polynomial **splits** ✓ **as claimed**, with root residues `res(θ²/9)`… the note says “root residues ±1 ∉ roots(ψ), ψ = y²+1” ✓ — `ψ = y²+1` has roots `±i ∉ F₃` ✓ and `±1` are not among them ✓ so (T2) fails ✓.
- **Counter-instance 2: `Φ″ = x² + 27`.** `w = 18`, `v(18) = 2`, `dv(w) = 2 = D′h` ✓ boundary. Roots `±√(−27) = ±3√(−3)`, and `v(√(−27)) = 3/2` ✓ **≠ h/e₁ = 1** ✓ so (T1) is broken ✓ and the extension is RAMIFIED ✓ **as claimed.**
- **`S` vs `D′h` here.** `S = e₁h = 1`, `D′h = e₁f₁h = 2` ✓, so the band `S < dv ≤ D′h` is `1 < dv ≤ 2` and both witnesses sit at `dv = 2` ✓ **inside the band** ✓ — the old display would have admitted them ✓.
**Both counter-instances are exact and the corrected band is exactly what excludes them.**

**RESOLUTION TRACE:** statement 450–478 · proof 480–490 · Remark 492–496 · consumer usage 115 (`.06`).

XREF: `HE6_PROOF_2026-08-08.md:HE3-1` — count **1** (the frozen consumer's citation).
XREF: `HE3_passPE1_report.md` ✓ present (leg A1).

**TEETH:** **HE-NORM** — “LEMMA HE3-1 at the entry key on EVERY member, by exact Bareiss/Sylvester integer resultants”, scored at §S9 Q1: “**0 violations** of Σ_ρ dv(Φ″(ρ)) = D′·dv(B₀) — at the entry key on all 72,134 enumerated members and at every test key of every oracled member. **The engine of the proof is machine-real.**” **Disposition: executable regression, exhaustive on the enumerated rows.** The band counter-instances are a **fired planted counter-instance** from PE1, PARI-exact. **`signed vacuity disclosure`:** “At f₁ = 1, S = D′h and the band … is empty — the sealed battery's geography is unaffected”, i.e. the repair is invisible to the sealed leg.

---

### EFF.HE3.s1of2.21  [lemma]  — LEMMA HE3-1L (the letter lift at level 1)

**CANONICAL STATEMENT:** verbatim, lines 498–546 (the lemma, its proof, and the `[r1, F1]` “what this repairs” block).

**FORM:** display (blockquoted bold-headed lemma with an indented ASCII residue set, its own proof, and a bold-headed repair note).

> “> **LEMMA HE3-1L [r1, F1 — THE LETTER LIFT AT LEVEL 1, back-propagated
> > from LEMMA HE6-1L's mechanism].** Let κ ∈ ℤ, κ ≥ 0, and let
> > i₀ = i₀(κ) be the unique 0 ≤ i₀ < e₁ with i₀h ≡ κ (mod e₁), and
> > n(κ) := x^{i₀}π^{(κ−i₀h)/e₁} the canonical height-κ monomial. The set
> > of residues realised as res(C(θ)/n(κ)(θ)) by C ∈ O[x] with
> > deg C < D′ and dv(C) = κ is EXACTLY
> >
> >     { Σ_{t ∈ T(κ)} c_t·η_θ^{t} : c_t ∈ F_Q, not all 0 } ,
> >     T(κ) := { t < f₁ : κ ≥ (i₀ + e₁t)·h } ;
> >
> > it is ALL of K^× iff T(κ) = {0, …, f₁−1} iff
> > κ ≥ (i₀(κ) + e₁(f₁−1))h, for which κ ≥ (D′−1)h is a κ-uniform
> > sufficient condition. **In particular every test height this note
> > uses — κ > D′h > (D′−1)h — reaches every letter of K^×.** At f₁ = 1
> > the set is F_Q^× = K^× at every κ ≥ i₀h, which is why the defect was
> > invisible to the sealed battery.”

with the proof (516–534) and the repair note (536–546):

> “> **[r1, F1 — what this repairs.]** The old HE3-1′ took w = ŝ·n(κ) with
> > ŝ ∈ O a LIFT of s: res(ŝ) ∈ F_Q, so only the f₁ = 1 letter set
> > F_Q^× ⊆ K^× was reachable — at f₁ ≥ 2 the K∖F_Q-rational residual
> > roots (6 of the 8 letters at K = F₉) had no carrier and could not be
> > peeled as displayed (PE1 F1, CRITICAL; the same genus HE6's r1 round
> > struck in its (LIFT) display). Every site below now takes
> > **w := −C** with C a letter-carrier from this lemma (the sign is the
> > [r1, F8] convention: with Φ″ := Φ′ − C the three residue sites — this
> > lemma's test R_λ(s) = 0, §S5's recentered residual R_λ(Z+s), §S6.2's
> > absorbed class S_{Z−s} — agree with no sign seam; under the old +
> > convention they disagreed pairwise by s ↦ −s).”

**CONDITIONALITY:** **This lemma is the repair for PE1's first CRITICAL, and it is derived at level 1 rather than transcribed.** The note is explicit: “*Proof (derived at level 1, not transcribed — HE6-1L is the same genus one level up, and its ϖ-read coset factor η_θ^{−q(κ)} does NOT appear here because this note reads residues against n(κ) itself, the reading HE6's RIDER calls the n(k)-read)*”. That parenthetical is load-bearing: it says exactly *why* HE6's coset factor is absent here, which is what makes the back-propagation legitimate rather than a copy.
Two dependencies: the `[r1, F8]` minus convention is fixed here and consumed at three named sites; and the fullness threshold `κ ≥ (D′−1)h` is what every later “every letter is available” claim rides.
Untouched by `[r2]` and by the A5 wave (verified).

**DERIVATION:** Lines 516–534, quoted:

> “> *Proof …* Write
> > C = Σ_{i<D′} c_i x^i. By GENHN-2 at θ, dv(C(θ)) =
> > min_i(e₁v(c_i) + ih), and a slot i contributes at height κ only if
> > ih ≡ κ (mod e₁), i.e. i = i₀ + e₁t for some 0 ≤ t < f₁ (h is
> > invertible mod e₁), with v(c_i) = (κ − (i₀+e₁t)h)/e₁ — a nonnegative
> > integer exactly when t ∈ T(κ). For such a slot,
> > c_i θ^{i₀+e₁t} / n(κ)(θ) = c_i·(θ^{e₁}π^{−h})^{t}·(unit-free exact
> > monomial arithmetic: the π-exponents cancel to −th), whose residue is
> > res(c_i)·η_θ^{t}. Summing the attaining slots: the realised residue is
> > Σ_{t ∈ T(κ)} res(c_{i₀+e₁t})·η_θ^{t}, the coefficients ranging over
> > F_Q freely and independently; since {1, η_θ, …, η_θ^{f₁−1}} is an
> > F_Q-basis of K, a not-all-zero choice gives a NONZERO sum (so
> > dv(C(θ)) = κ exactly, no cancellation possible at level 1), and the
> > realised set is the punctured F_Q-span displayed. Fullness: the span
> > is K iff T(κ) is full iff the largest slot requirement
> > κ ≥ (i₀ + e₁(f₁−1))h holds; i₀ ≤ e₁−1 gives (i₀ + e₁(f₁−1))h ≤
> > (D′−1)h. ∎”

*Arithmetic audit (rule 22), every step recomputed.*
- **Slot indexing.** `i ≡ i₀ (mod e₁)` with `i < D′ = e₁f₁` gives `i = i₀ + e₁t`, `0 ≤ t < f₁` ✓ (since `i₀ < e₁`, the largest is `i₀ + e₁(f₁−1) ≤ e₁−1 + e₁f₁ − e₁ = D′ − 1` ✓).
- **Integrality of `v(c_i)`.** `v(c_i) = (κ − (i₀+e₁t)h)/e₁`; nonnegative iff `κ ≥ (i₀+e₁t)h` ✓ **exactly `T(κ)`** ✓. Integral because `κ ≡ i₀h ≡ (i₀+e₁t)h (mod e₁)` ✓.
- **The residue.** `c_i θ^{i₀+e₁t}/n(κ)(θ)` with `n(κ) = x^{i₀}π^{(κ−i₀h)/e₁}`: the ratio is `c_i θ^{e₁t} π^{−(κ−i₀h)/e₁} · π^{v(c_i)}`-adjusted… computing exponents: numerator has `π`-exponent `v(c_i) = (κ − i₀h − e₁th)/e₁`, denominator `(κ − i₀h)/e₁`; difference `= −th` ✓ **exactly the displayed “the π-exponents cancel to −th”** ✓. So the ratio is `res(c_i)·(θ^{e₁}π^{−h})^t = res(c_i)·η_θ^t` ✓.
- **Fullness threshold.** `T(κ)` full iff `κ ≥ (i₀ + e₁(f₁−1))h` ✓; and `i₀ ≤ e₁−1` gives `(i₀+e₁(f₁−1))h ≤ (e₁−1+e₁f₁−e₁)h = (D′−1)h` ✓ **so `κ ≥ (D′−1)h` suffices uniformly** ✓.
- **The test heights.** `κ > D′h` and `D′h > (D′−1)h` iff `h > 0` ✓ — so every test height reaches every letter ✓.
- **The F₉ figure.** At `K = F₉`, `|K^×| = 8` and `|F₃^×| = 2`, so `8 − 2 = 6` letters were unreachable ✓ **exactly the displayed “6 of the 8 letters”** ✓.
**Every step reproduces.**

**RESOLUTION TRACE:** statement 498–514 · proof 516–534 · repair note 536–546 · consumed at 550, 703–706, 823–826, 992–994.

XREF: `HE6_PROOF_2026-08-08.md:LEMMA HE6-1L` — count **4**.
XREF: `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-2` — count **2**.

**TEETH:** **`he3r1_supp.py` P1 and P3** — the repaired peel at PE1's counter-instance (`m_s = 1` at each of the 3 residual roots “including both K∖F₃ letters, which the old ŝ·n(λ) display cannot carry”) and the full-`F₂₇^×` 26-letter profile (`m_s = 1` at exactly the 3 residual roots, 0 at the other 23). **Disposition: executable regression, exhaustive over the letter set.** **P4's scope is DISCLOSED as quasi-tautological** (`.07` F-4) and the decorrelated substitute is PE2's FR-C (`nfeltval`/`nfmodpr`, no slot formula) — `accepted-with-decorrelation-supplied`. **`signed vacuity disclosure`:** “At f₁ = 1 the set is F_Q^× = K^× at every κ ≥ i₀h, which is why the defect was invisible to the sealed battery.”

---

### EFF.HE3.s1of2.22  [lemma]  — LEMMA HE3-1′ (the evaluation display)

**CANONICAL STATEMENT:** verbatim, lines 548–559.

**FORM:** display (blockquoted bold-headed lemma with an indented ASCII identity).

> “> **LEMMA HE3-1′ (the evaluation display) [r1: letters generalized,
> > band corrected, sign fixed].** Let κ ~~> S~~ **> D′h** be an integer,
> > s ∈ K^×, C a letter-carrier for s at height κ (LEMMA HE3-1L),
> > Φ″ := Φ′ − C. Then with B₀ := f mod Φ″,
> >
> >     dv(B₀) = min_{0 ≤ j ≤ μ} ( dv(A_j) + jκ )                (generic)
> >
> > whenever κ is NOT a slope of P(F), and also whenever κ IS a slope λ of
> > P(F) but s is NOT a root of the residual polynomial R_λ; and
> > dv(B₀) > min_j(dv(A_j) + jκ) exactly when κ = λ is a slope and
> > R_λ(s) = 0 (with the excess governed by the multiplicity, LEMMA
> > HE3-2).”

**CONDITIONALITY:** **The lemma's equality clause depends on the COHERENT `R_λ`, and its proof was corrected at `[r2]` to say so.** The proof's key sentence (576–582) carries the `[r2, F1]` bracket: “with DEFINITION 1's [r2] COHERENT R_λ the folding is exact and the K-factor is a single global one … **read with the NAIVE per-slot residuals the display is false at e₁ ≥ 2** — the witness in the Remark”. `SUPERSESSION KIND: scope-pin` (which `R_λ` the display is about). `TARGETS: s1of2.22`.
Second: the `[r1]` triple change (letters generalized via HE3-1L, band `S ⇝ D′h`, sign `+ ⇝ −`) is already landed.
Third: **this lemma is what makes `.11`'s Ψ-comparison non-circular** — it consumes only `κ > D′h` and the locus, never the node.

**DERIVATION:** Lines 561–586, quoted:

> “*Proof.* By LEMMA HE3-1 (whose hypothesis dv(Φ″ − Φ′) = κ > D′h now
> holds), B₀(θ″) = F(−w)(θ″) = F(C)(θ″) = Σ_j A_j(θ″)·C(θ″)^j (here
> w = Φ″ − Φ′ = −C, so −w = C — the sign convention makes the test key
> carry the letter POSITIVELY). Each summand has dv exactly
> dv(A_j) + jκ: dv(A_j(θ″)) = dv(A_j) and dv(C(θ″)) = κ by the ξ-form
> slot lemma at θ″ (LEMMA HE6-0″ as-of; θ″ satisfies (T1)/(T2) by the
> [r1]-corrected invariant maintenance). By the ultrametric inequality
> dv(B₀) ≥ min_j(…), with equality unless the minimum is attained at ≥ 2
> indices AND their residues cancel. Group the indices attaining the
> minimum: they are exactly the j on the height-κ supporting line of
> P(F), i.e. the lattice points of the side of slope κ if κ is a slope,
> and a single vertex otherwise. In the former case the sum of the
> residues of the attaining summands is, after dividing by the common
> normalizer n(min) and folding the normalizer wrap through η (S4 of
> GENHN, the cocycle n(κ)^t = ẑ^{fl}n(tκ)), precisely R_λ(s) up to a
> nonzero K-factor **[r2, F1: with DEFINITION 1's [r2] COHERENT R_λ the
> folding is exact and the K-factor is a single global one — the sum is
> res(n(κ₀)(θ″)n(λ)(θ″)^{j₀}/n(min)(θ″))·s^{j₀}·R_λ(s) (j₀ the side's
> left-endpoint abscissa, κ₀ its height), the per-term wraps
> having cancelled identically against the coherent normalizers (the
> coboundary computation, §S3 Remark [r2]); read with the NAIVE per-slot
> residuals the display is false at e₁ ≥ 2 — the witness in the Remark]**
> — the letter s enters through res(C(θ″)/n(κ)(θ″)) =
> ι_{θ″}(s), the same universal expression as at θ by HE6-0″'s residue
> clause; so cancellation ⟺ R_λ(s) = 0. In the latter case a single
> summand attains the minimum and no cancellation is possible. ∎”

*Arithmetic audit (rule 22).* Each summand `A_j(θ″)·C(θ″)^j` has `dv = dv(A_j(θ″)) + j·dv(C(θ″)) = dv(A_j) + jκ` ✓ (the ξ-form slot read gives `dv(A_j(θ″)) = dv(A_j)` ✓ and `dv(C(θ″)) = κ` ✓). The minimising indices lie on the height-κ supporting line of `P(F)` ✓ — that is the definition of a supporting line at slope `κ` ✓. Vertex case ⟹ one attaining index ⟹ no cancellation ✓.

**RESOLUTION TRACE:** statement 548–559 · proof 561–586 · `[r2]` correction 576–582 · Remark 588–642 (`.17`).

XREF: `HE6_PROOF_2026-08-08.md:HE6-0″` — count **7**.
XREF: `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-2` — count **2**.

**TEETH:** **HE-PSI** — “the same identity at EVERY test key (κ, s), plus HE3-1′'s inequality dv(B₀) ≥ generic, plus the convex-duality identity (★)”, scored at §S9 Q2: “**0 violations, 43,528 checks**: dv(B₀^{(κ,s)}) never falls below min_j(dv(A_j) + jκ), and the support-function identity (★) holds at every sampled κ on every in-window polygon.” **Disposition: executable regression.** Note what Q2 tests: the **inequality** and (★), not the equality-vs-cancellation dichotomy directly — that is tested through the peel's `m_s` profile at `he3r1_supp.py` P1/P3.

---

### EFF.HE3.s1of2.23  [scope-record]  — the `[r2, F1]` twist Remark (what the twist does and does not do)

**CANONICAL STATEMENT:** verbatim, lines 588–613 (the Remark, with its struck former sentence and the two coboundary bullets).

**FORM:** bold-headed remark paragraph containing a struck sentence and a two-bullet replacement.

> “**Remark (what the twist does and does not do) [r2, F1 2026-08-09 —
> the old invariance sentence was FALSE as displayed; struck and
> replaced by the coboundary statement, with PE2's machine-adjudicated
> witness].** ~~The wrap factors ẑ^{fl} are nonzero constants of K
> depending only on (κ, t, e₁, h); they rescale the coefficients of R_λ
> by a fixed nonzero diagonal, hence change neither its root set up to
> that rescaling nor its factorization TYPE.~~ A diagonal rescaling of
> coefficients preserves root sets and factorization type only when it
> is GEOMETRIC (a_k ↦ c·d^k a_k, i.e. one global scalar plus Z ↦ dZ);
> the wraps that actually occur are η^{W(k)} with
> W(k) = (i₀(κ₀−ku) + k·i₀(u) − i₀(κ₀))/e₁ (DEFINITION 1 [r2]), and W
> need not be affine in k — at (e₁,h) = (2,1), λ = 3, κ₀ = 9 the
> exponents on the line are W = (0,0,1,1) at k = 0..3. What IS true, and
> what the chain uses, is that across any identity comparing two reads
> of one supporting line the wrap is a COBOUNDARY, W(i) − W(j), which
> cancels when both sides are read coherently:
> * in LEMMA HE3-1′'s proof, the attaining residues at an integer slope
>   λ (span left endpoint (j₀, κ₀), intercept c = κ₀ + j₀λ) sum to
>   res(C(θ″)^{j₀}·n(κ₀)(θ″)/n(c)(θ″)) · Σ_k ã_k s^k — the k-dependent
>   normalizer monomials M_k·n(λ)^{j₀+k}/n(c) collapse to the SAME
>   height-0 monomial for k = 0, …, d (exact cancellation of the n(λ)^k
>   legs against M_k = n(κ₀)/n(λ)^k), so the sum is ONE global nonzero
>   K-factor times s^{j₀}·R_λ(s), with R_λ the coherent object;
> * in LEMMA HE3-2(b)'s proof, the (i → j) substitution summand carries
>   M_i·n(λ)^{i−j}/M_j = 1 IDENTICALLY as monomials, so
>   G″(Z) = G(Z+s) holds wrap-free with coherent reads on both sides.”

**SUPERSESSION KIND: replacement** (a false sentence struck and replaced). `TARGETS: s1of2.23` itself; the two bullets pin `s1of2.22` and `s1of2.24`.

**CONDITIONALITY:** **The struck sentence is a genuine falsehood in the note's own earlier text, preserved for the record.** Its failure mode is exact: a diagonal rescaling preserves factorization type **only when geometric**, and the actual wraps are not. **The replacement is a coboundary statement** — the wrap is `W(i) − W(j)` across any identity comparing two reads of one line, which cancels when both sides are coherent. This is what lets the chain's identities survive a non-affine `W`.

**DERIVATION:** Displayed inline; the two bullets are the two sites where the cancellation is needed.

*Arithmetic audit (rule 22) of the non-affinity instance, computed fresh.* `(e₁, h) = (2,1)`, `λ = 3`, `κ₀ = 9`, `u = λℓ`… with `λ = 3` an integer, `ℓ = 1` and `u = 3`. Line heights at `k = 0..3`: `κ₀ − ku = 9, 6, 3, 0`. `i₀(m)` solves `i·h ≡ m (mod e₁)`, i.e. `i ≡ m (mod 2)`, `0 ≤ i < 2`: `i₀(9) = 1`, `i₀(6) = 0`, `i₀(3) = 1`, `i₀(0) = 0`. Also `i₀(u) = i₀(3) = 1`, `i₀(κ₀) = i₀(9) = 1`. Then `W(k) = (i₀(κ₀−ku) + k·i₀(u) − i₀(κ₀))/e₁`:
- `k=0`: `(1 + 0 − 1)/2 = 0` ✓
- `k=1`: `(0 + 1 − 1)/2 = 0` ✓
- `k=2`: `(1 + 2 − 1)/2 = 1` ✓
- `k=3`: `(0 + 3 − 1)/2 = 1` ✓
**`W = (0,0,1,1)` — exactly the displayed tuple** ✓, and its differences `(0, 1, 0)` are non-constant ✓ **so `W` is not affine in `k`** ✓. **The instance reproduces exactly and proves the point.**
Second check: the bullet-1 collapse. `M_k = n(κ₀)/n(λ)^k`; the summand's monomial is `M_k · n(λ)^{j₀+k}/n(c)` `= n(κ₀)·n(λ)^{j₀}/n(c)` ✓ **independent of `k`** ✓ — exactly “collapse to the SAME height-0 monomial” ✓. Height check: `κ₀ + j₀λ − c = 0` ✓ since `c = κ₀ + j₀λ` ✓.
Third: bullet-2. `M_i·n(λ)^{i−j}/M_j = [n(c)/n(λ)^i]·n(λ)^{i−j}·[n(λ)^j/n(c)] = 1` ✓ **identically as monomials** ✓.

**RESOLUTION TRACE:** statement 588–613 · witness 615–642 (`.24`) · pinned sites 576–582, 787–793.

XREF: `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-2` — count **2** (GENHN §S4's cocycle is cited by section).

**TEETH:** the witness at `.24`. **Disposition: `decorrelated-model audit` for the finding (PE2 machine-adjudicated), planted mutant for the witness.**

---

### EFF.HE3.s1of2.24  [run-record]  — THE WITNESS (PE2's adjudicated member, re-derived)

**CANONICAL STATEMENT:** verbatim, lines 615–642.

**FORM:** bold-headed paragraph (a worked counter-instance with PARI adjudication).

> “**THE WITNESS (PE2's adjudicated member, re-derived).** Genre
> (3; 2,2,2; 1), Φ′ = x⁴+9 over ℤ₃ (D′ = 4, h = 1, e₁ = f₁ = 2,
> K = F₉ = F₃(η), η² = −1), f = Φ′² + 9x·Φ′ + 243: pins (2,0), (1,5),
> (0,10), the three on the λ = 5 line (dv(9xθ-read) = 2(2 + 1/2) = 5,
> dv(3⁵) = 10). Naive read (n(10) = 3⁵, n(5) = 9x, n(0) = 1):
> a = (1,1,1), Z² + Z + 1 = (Z−1)² in char 3 — a repeated K-rational
> root, scheduling a stage-α refine with predicted above-λ length 2 at
> s = 1 (HE3-2(b)). Coherent read: W = (0,1,1) from κ₀ = 10, u = 5
> (i₀(10) = 0, i₀(5) = 1, i₀(0) = 0), so ã = (1, η, η) and
> R_λ = η·(Z² + Z − η), disc(Z² + Z − η) = 1 + η ∉ (F₉^×)² = {±1, ±η} —
> IRREDUCIBLE, no refine, σ = {(2,4)}. PARI (PE2's fresh leg
> `he3_pe2fresh.py`, member `ma`): σ = {(2,4)}, and the measured
> above-λ length is 0 at each of the 8 letters of F₉^× — the naive read
> flips the factorization type and schedules a PHANTOM refine; the
> coherent read is what the chain computes. (PE2's report displays the
> same residual as Z² − Z − η: the Z ↦ −Z member of the geometric class,
> same type — the [r1, F8] sign seam.) What survives of the old
> sentence: the uses below consult (a) whether R_λ(s) = 0 and (b) the
> degrees of the irreducible factors of R_λ — both well-defined for the
> COHERENT R_λ and invariant under the geometric freedom (anchor choice
> n(κ₀) vs ϖ^{κ₀}, the sign seam s ↦ −s); and the battery detects
> residual roots by measuring dv(B₀), which consults the coherent object
> automatically (the measurement IS LEMMA HE3-1′'s evaluation identity,
> whose right side is the coherent R_λ(s)). At e₁ = 1 the two reads
> coincide and the r1 sweeps were immune; at e₁ ≥ 2 a transcription
> that assembles R_λ from the untwisted slot residues emits the wrong σ
> inside the μ ≤ 3 headline's scope — the witness above is the
> demonstration.”

**CONDITIONALITY:** **A fired counter-instance, re-derived at this note rather than transcribed, and PARI-adjudicated.** Its last sentence is the severity statement: “at e₁ ≥ 2 a transcription that assembles R_λ from the untwisted slot residues **emits the wrong σ inside the μ ≤ 3 headline's scope**.” **Two exculpating facts the note states:** the *battery* is immune because it measures `dv(B₀)` and therefore consults the coherent object automatically; and the r1 sweeps were at `e₁ = 1` where the reads coincide.

**DERIVATION:** Worked instance.

*Arithmetic audit (rule 22) — every number recomputed independently.*
- **Frame.** `Φ′ = x⁴ + 9` over ℤ₃; `D′ = 4`, and `e₁ = f₁ = 2` requires the polygon of `Φ′` to be one side from `(0, v(9)) = (0,2)` to `(4,0)`, slope `2/4 = 1/2 = h/e₁` with `h = 1, e₁ = 2` ✓. Residual: lattice points at abscissae `≡ 0 mod e₁ = 2`, i.e. `0, 2, 4`, with coefficients `9, 0, 1` → `ψ(y) = y² + 1` over F₃ ✓ irreducible (`−1` a non-residue mod 3) ✓ so `f₁ = 2` ✓ and `K = F₉ = F₃(η)`, `η² = −1` ✓ **all four frame data confirmed.**
- **`dv`.** `dv = e₁v = 2v` ✓.
- **The pins.** `f = Φ′² + 9x·Φ′ + 243`, so `A₂ = 1` (`dv = 0`) ✓ pin `(2,0)` ✓; `A₁ = 9x`, `dv(9x(θ)) = 2·v(9) + 1·h = 2·2 + 1 = 5` ✓ pin `(1,5)` ✓ — **and the note's parenthetical “dv(9xθ-read) = 2(2 + 1/2) = 5” is the same computation in `v`-units** ✓; `A₀ = 243 = 3⁵`, `dv = 2·5 = 10` ✓ pin `(0,10)` ✓.
- **One side.** Pins `(0,10), (1,5), (2,0)` are collinear with slope `−5` in the `(j, dv)` plane, i.e. dv-slope `λ = 5` ✓ **all three on the λ = 5 line** ✓, `d_λ = 2` ✓, `ℓ = 1` ✓.
- **Naive read.** `n(10) = ?` At `e₁ = 2, h = 1`: `i₀(10)` solves `i ≡ 10 ≡ 0 (mod 2)` ⟹ `i₀ = 0`, `a = 10/2 = 5`, so `n(10) = π⁵ = 3⁵` ✓ **matches.** `n(5)`: `i ≡ 5 ≡ 1 (mod 2)` ⟹ `i₀ = 1`, `a = (5−1)/2 = 2`, `n(5) = x·9` ✓ **matches “n(5) = 9x”.** `n(0) = 1` ✓. Naive coefficients `a_k = res(A_{j₀+k}/n(κ₀−k·5))` with `j₀ = 0, κ₀ = 10`: `a_0 = res(243/3⁵) = 1` ✓; `a_1 = res(9x(θ)/9x(θ)) = 1` ✓; `a_2 = res(1/1) = 1` ✓ → `a = (1,1,1)` ✓ **matches.** `Z² + Z + 1` over F₃: `= (Z − 1)²` since `(Z−1)² = Z² − 2Z + 1 = Z² + Z + 1` in char 3 ✓ **exact.**
- **Coherent read.** `W(k) = (i₀(κ₀−ku) + k·i₀(u) − i₀(κ₀))/e₁` with `κ₀ = 10, u = 5, e₁ = 2`: `i₀(10) = 0, i₀(5) = 1, i₀(0) = 0` ✓ **matches the displayed triple.** `k=0`: `(0 + 0 − 0)/2 = 0` ✓; `k=1`: `(i₀(5) + 1·1 − 0)/2 = (1+1)/2 = 1` ✓; `k=2`: `(i₀(0) + 2·1 − 0)/2 = (0+2)/2 = 1` ✓ → `W = (0,1,1)` ✓ **exactly as displayed.** So `ã_k = a_k·η^{W(k)} = (1, η, η)` ✓.
- **The coherent residual.** `R_λ = 1 + ηZ + ηZ² = η(Z² + Z + η^{−1})`. Now `η² = −1` so `η^{−1} = −η` ✓, giving `η(Z² + Z − η)` ✓ **exactly as displayed.**
- **Irreducibility.** `disc(Z² + Z − η) = 1 − 4(−η) = 1 + 4η = 1 + η` in char 3 (`4 ≡ 1`) ✓ **matches “disc = 1 + η”.** Squares in `F₉^×`: the group is cyclic of order 8, squares form the index-2 subgroup of order 4. With `η² = −1`, `η` has order 4, so `⟨η⟩ = {1, η, −1, −η}` is the order-4 subgroup = the squares ✓ **matches the displayed `(F₉^×)² = {±1, ±η}`.** Is `1 + η` in it? The elements of `F₉` are `a + bη`, `a,b ∈ F₃`. `1 + η` has `a = b = 1`, which is not in `{1, η, 2, 2η}` ✓ **not a square** ✓ **IRREDUCIBLE** ✓.
- **σ.** Irreducible residual of degree 2 on an `ℓ = 1` side gives one label `(e_s, f_s) = (1, 2)`, so `σ = {(e₁·1, f₁·2)} = {(2, 4)}` ✓ **matches PARI** ✓, and `2·4 = 8 = deg f = D′μ = 4·2` ✓.
**Every single number in the witness reproduces exactly, including the discriminant and the square-set. This is the most thoroughly verifiable item in the shard and it is correct.**

**RESOLUTION TRACE:** statement 615–642 · the construction it tests 253–286 (`.14`) · PE2's leg `he3_pe2fresh.py` member `ma`.

ARTIFACT: `verification/openmath/he3_pe2fresh.py` ✓ present.

**TEETH:** **Planted mutant (naive vs coherent), FIRED, PARI-adjudicated**, with the above-λ length measured at all 8 letters of `F₉^×` (all 0, refuting the phantom refine). **Re-fired at three further geographies at PE3** (1586–1588, shard 2). **Disposition: planted mutant; fired four times.**

---

### EFF.HE3.s1of2.25  [lemma]  — LEMMA HE3-0 (the label of a root)

**CANONICAL STATEMENT:** verbatim, lines 648–671.

**FORM:** display (blockquoted bold-headed lemma, three clauses, with two in-place correction brackets).

> “> **LEMMA HE3-0.** Every root ρ of f on the genre-G opening locus
> > satisfies (T1) v(ρ) = h/e₁ with gcd(h, e₁) = 1 and (T2)
> > η_ρ := res(ρ^{e₁}π^{−h}) is a root of ψ. Consequently
> > (i) dv(A_j(ρ)) = dv(A_j) for every j (the SAME integers the stage
> > read consults), (ii) the residual polynomials of the Y-polygon of
> > F_ρ(Y) := Y^μ + Σ_j A_j(ρ)Y^j over L_ρ are the images of the stage
> > residuals R_λ **[r2, F1: R_λ in DEFINITION 1's coherent convention;
> > the L_ρ-side residuals are read with the matching coherent
> > normalizers n(κ₀)(ρ), n(u)(ρ) — the comparison is convention-matched
> > on both sides]** under the F_Q-embedding K = F_Q(η_θ) → k̄, η_θ ↦ η_ρ
> > — in particular they have the same factorization type over K, and
> > (iii) y_ρ := Φ′(ρ) satisfies F_ρ(y_ρ) = 0, so dv(y_ρ) is a slope λ
> > of P(F) and — writing λ = u/ℓ in lowest terms — the residue
> > **β_ρ := res(y_ρ/n(λ)(ρ)) at ℓ = 1, β_ρ := res(y_ρ^ℓ/n(u)(ρ)) at
> > ℓ ≥ 2 [r1, F6: normalizers exist at INTEGER dv-heights only, so the
> > old uniform display res(y_ρ/n(λ)(ρ)) is undefined at ℓ ≥ 2; the
> > ℓ-power read is HE6-0′'s repair form, applied here — y_ρ^ℓ/n(u)(ρ)
> > has dv = ℓλ − u = 0, so its residue exists. At μ ≤ 3, ℓ ≥ 2 forces
> > d = 1 and the residue never selects among factors (R_λ is linear in
> > its lattice variable), so no μ ≤ 3 conclusion consults this read;
> > at μ ≥ 4 it is load-bearing, inside HE3-BOX-6's territory as repaired
> > by HE6]** — is a root of (the image of) R_λ. The
> > resulting pair (λ, r) — r the irreducible factor of R_λ whose image
> > β is that residue — is the **label** of ρ.”

**CONDITIONALITY:**
(a) **`[r1, F6]`** — the `ℓ ≥ 2` residue read is repaired from an undefined `n(λ)` to the `ℓ`-power form `res(y_ρ^ℓ/n(u)(ρ))`. `SUPERSESSION KIND: replacement`. **Its scope is stated honestly**: vacuous at μ ≤ 3 (where `ℓ ≥ 2` forces `d = 1`), load-bearing at μ ≥ 4 inside HE3-BOX-6.
(b) **`[r2, F1]`** — clause (ii)'s comparison is convention-matched on both sides. `SUPERSESSION KIND: scope-pin`.
(c) **The proof sketch's provenance is corrected by R8-5** (1795–1819, shard 2): the sentence “(i)/(ii): the SLOT LEMMA (GENHN-2) is stated for any ξ with (T1)/(T2)” is **stale** — GENHN-2 is stated at roots θ only, as `.03`'s `[r1, F4]` already established. R8-5 re-points it to HE6-0″. `SUPERSESSION KIND: provenance-rider`. **The A5 append's own words: “This is a provenance correction only: the required ξ-form lemma was already consumed at §S0 [r1, F4], but the HE3-0 proof sentence had not been updated to cite it.”** So the r1 round fixed the import and missed one downstream sentence; A5 found it.
(d) **The definition of `S_r` that consumes this clause is separately repaired by R8-4** (1774–1793, shard 2), which installs the same piecewise `β_ρ` into LEMMA HE3-4's display — “this correction propagates it to the one display the r1 round missed”.

**DERIVATION:** Lines 673–682, quoted, **with the R8-5 correction applied**:

> “*Proof sketch (completed at commit 2).* (T1)/(T2): the opening locus
> is by definition the locus where the ambient polygon has the side of
> slope h/e₁ carrying residual ψ^μ, so every root of the block has that
> valuation and its η is a root of ψ. (i)/(ii): the SLOT LEMMA
> (GENHN-2) is stated for any ξ with (T1)/(T2) [**R8-5, 2026-08-12: READ AS** “at θ use GENHN-2; at the root ρ use LEMMA HE6-0″, because ρ satisfies (T1)/(T2). HE6-0″ re-runs the slot argument at an arbitrary (T1)/(T2) point and gives dv(A_j(ρ)) = min_i(e₁v(a_{j,i}) + ih) = dv(A_j(θ)), together with the same universal residue polynomial in η_ρ. Reading the two sides with DEFINITION 1's matching coherent normalizers sends the stage residual through the F_Q-embedding ι_ρ : K → k̄, η_θ ↦ η_ρ. Hence the residual polynomials at ρ are the images of the coherent stage residuals and have the asserted factorization type.”], and its residue formula
> is the universal polynomial Σ_t res(a_{j,i+e₁t})η^t — the SAME
> polynomial in η at ξ = ρ as at ξ = θ; two roots of the irreducible ψ
> differ by an F_Q-automorphism of K, which preserves factorization
> type. (iii): f(ρ) = 0 rewrites as F_ρ(y_ρ) = 0; then the classical
> Newton-polygon read over the complete field L_ρ. ∎”

*Arithmetic audit (rule 22).* The `ℓ ≥ 2` read: `dv(y_ρ^ℓ) = ℓ·dv(y_ρ) = ℓλ = ℓ·(u/ℓ) = u` ✓ and `dv(n(u)(ρ)) = u` ✓, so the quotient has `dv = 0` ✓ **and the residue exists** ✓ **exactly as displayed.** The μ ≤ 3 vacuity: `ℓ ≥ 2` and `ℓd ≤ μ ≤ 3` force `d = 1` ✓, so `R_λ` has a single irreducible factor and the residue cannot select among factors ✓.

**RESOLUTION TRACE:** statement 648–671 · proof 673–682 · correction sites 1774–1793 (R8-4), 1795–1819 (R8-5).

XREF: `HE6_PROOF_2026-08-08.md:HE6-0″` — count **7** · `HE6-0′` — count **5**.
XREF: `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-2` — count **2**.

**TEETH:** Indirect — every σ prediction rides the label read, so HE-SIG's 947 PARI jobs test it compositely. The `ℓ ≥ 2` branch is **PROOF-ONLY at μ ≤ 3 by construction** (vacuous) and **unexercised at μ ≥ 4** (HE3-BOX-3's coverage hole). `he3r1_supp.py` P2 includes “an ℓ = 2 member (λ = 7/2, block (2,2))” at `f₁ = 2`, which is the one direct contact.

---

### EFF.HE3.s1of2.26  [lemma]  — COROLLARY HE3-0′ (the local forcing)

**CANONICAL STATEMENT:** verbatim, lines 684–687.

**FORM:** display (blockquoted bold-headed corollary).

> “> **COROLLARY HE3-0′ (the local forcing).** If ρ has label (λ, r) with
> > λ = u/ℓ in lowest terms and f_s = deg r, then
> > e₁ℓ | e(L_ρ) and f₁f_s | f(L_ρ), hence
> > [L_ρ : K₀] ≥ e₁ℓ·f₁f_s = D′e_sf_s.”

**CONDITIONALITY:** Unconditional given `.25`. Its `[r1, F6]` dependency (the `n(u)` normalizer at `ℓ ≥ 2`) is carried in the proof. **This is the inequality half of the forcing that `.16`'s degree count turns into equality** — the pair (`≥` here, `Σ = deg f` there) is the whole engine.

**DERIVATION:** Lines 689–696, quoted:

> “*Proof.* e₁ | e(L_ρ) by (T1). Writing e(L_ρ) = e₁e′ and
> v(y_ρ) = u/(e₁ℓ) ∈ (1/e(L_ρ))ℤ gives e′u/ℓ ∈ ℤ, and gcd(u, ℓ) = 1
> forces ℓ | e′. For f: K = F_Q(η_ρ) ⊆ k_{L_ρ} by (T2), and **[r1, F6:
> the integer-height normalizer n(u)(ρ) = ρ^{i}π^{a} lies in L_ρ (the old
> display consulted n(λ), which does not exist at ℓ ≥ 2), so
> y_ρ^ℓ/n(u)(ρ) is a unit of O_{L_ρ} and β = res(y_ρ^ℓ/n(u)(ρ)) ∈
> k_{L_ρ}]**; [K(β) : K] = f_s since β is a root of the irreducible
> image of r. ∎”

*Arithmetic audit (rule 22), recomputed.* `v(y_ρ) = dv(y_ρ)/e₁ = λ/e₁ = u/(e₁ℓ)` ✓. Membership in `(1/e(L_ρ))ℤ` with `e(L_ρ) = e₁e′` gives `u/(e₁ℓ) · e₁e′ = ue′/ℓ ∈ ℤ` ✓, and `gcd(u,ℓ) = 1` forces `ℓ | e′` ✓ **so `e₁ℓ | e(L_ρ)`** ✓. For `f`: `K ⊆ k_{L_ρ}` gives `f₁ | f(L_ρ)` ✓ and `[K(β):K] = f_s` gives `f₁f_s | f(L_ρ)` ✓ (degrees multiply in the residue tower ✓). Product: `[L_ρ:K₀] = e(L_ρ)f(L_ρ) ≥ e₁ℓ · f₁f_s = D′e_sf_s` ✓ **exactly as displayed** (using `e_s = ℓ`, `f_s = deg r`) ✓.

**RESOLUTION TRACE:** statement 684–687 · proof 689–696 · consumed at 1105–1108 (`.34`'s base step).

**TEETH:** Indirect (see `.25`).

---

### EFF.HE3.s1of2.27  [lemma]  — LEMMA HE3-2 (recentering: valuations and residuals)

**CANONICAL STATEMENT:** verbatim, lines 702–747 (clauses (a), (b), (c) with all four in-place correction brackets and the characteristic-free closing sentences). **Clause (b)'s above-λ sentence is consumer-pinned under (F3).**

**FORM:** display (blockquoted bold-headed lemma, three clauses, with an indented ASCII residual display inside (b)).

> “> **LEMMA HE3-2.** Keep κ ~~> S~~ **[r1, F2] > D′h**, s ∈ K^×,
> > w **[r1, F1/F8: w := −C with C ∈ O[x], deg C < D′, dv(C) = κ,
> > res(C(θ)/n(κ)(θ)) = s — the general letter-carrier of LEMMA HE3-1L,
> > §S3; the old monomial ŝ·n(κ) reaches only s ∈ F_Q^× and the old +
> > sign made the three residue sites disagree]**, Φ″ = Φ′ + w = Φ′ − C,
> > and let f = Σ_j A_j′Φ″^j be the Φ″-development. Then:
> > (a) [VALUES] dv(A_j′) ≥ min_{i ≥ j}(dv(A_i) + (i−j)κ) for every j,
> > with equality unless the attaining indices' residues cancel;
> > (b) [THE RECENTERED POLYGON] if κ is not a slope of P(F), P(F″) is
> > P(F) truncated at height κ (all slopes < κ preserved, all slopes > κ
> > replaced by the single slope κ on the same span); if κ = λ IS a slope
> > with residual R_λ and s is a root of R_λ of multiplicity m ≥ 1, then
> > the portion of P(F″) of slope > λ has horizontal length exactly
> > m·ℓ = m (ℓ = 1 for an integer slope λ), and — **[r1, F5: the old
> > clauses "the portion of slope λ has length reduced by m" and "all
> > other sides are unchanged" were FALSE for the sides of slope > λ;
> > a Lean transcription of the old (b) is refutable at any two-side
> > polygon]** — the sides of slope < λ are unchanged; the sides of
> > slope > λ COLLAPSE onto the λ-line (each of their roots y of F has
> > y″ = y − C(·) with dv(y″) = λ exactly and residue 0 − s = −s ≠ 0);
> > the slope-λ side of P(F″) has length (L_λ − m) + T, where T is the
> > horizontal length of P(F) above λ, and its residual is
> >
> >     (R_λ(Z + s)/Z^m)·(Z + s)^{T}    up to the twist rescaling
> >     [r2, F1: "the twist rescaling" = ONE global nonzero K-factor
> >     (a geometric rescaling) once both residuals are the coherent
> >     objects of DEFINITION 1 [r2] — type-preserving; §S3 Remark [r2]]
> >
> > (roots: the shifted old λ-residues z − s over z ≠ s, plus −s with
> > multiplicity T from the collapsed material). The ONE clause the
> > onward argument consults is unchanged from the old display: the
> > part of P(F″) STRICTLY ABOVE λ is the absorbed sub-block alone,
> > of length exactly m — the collapsed material never appears there;
> > (c) [IN-WINDOW, UPWARD] every new digit consulted lies strictly inside
> > its class's window and is determined by old digits at weakly lower
> > dv-heights (GENHN-3(c)(d)); the key invariants of S3.1 — the constant
> > term's valuation f₁h and the residual η — are untouched, since
> > dv(w) = κ ~~> S = e₁h~~ **[r1, F2] > D′h = e₁f₁h** places w strictly
> > above the key's own side **[the key's side has dv-height D′h at
> > abscissa 0, not S: HE3-1's counter-instances x²+18 / x²+27 sit at
> > κ = 2 = D′h > S = 1 and DO touch the invariants — κ > S places w
> > above the side only when f₁ = 1]**.
> > **No graded frame and no digit-space bijection is used: (a)–(c) are
> > statements about valuations and residues only.** Both characteristics:
> > the only algebraic input is the SUBSTITUTION identity Z ↦ Z + s
> > applied to R_λ, which is characteristic-free.”

**CONDITIONALITY:** **Four corrections and one consumer pin.**
(a) **`[r1, F5]` is the deepest of them.** Two clauses of the old (b) were FALSE — “the portion of slope λ has length reduced by m” and “all other sides are unchanged” — and the note records that **a Lean transcription of the old (b) is refutable at any two-side polygon**. The corrected mechanism is that above-λ sides **COLLAPSE onto the λ-line**. `SUPERSESSION KIND: replacement`.
(b) **The consumer-pinned clause is preserved verbatim and identified**: “The ONE clause the onward argument consults is unchanged from the old display: the part of P(F″) STRICTLY ABOVE λ is the absorbed sub-block alone, of length exactly m”. That is what `.06`'s trace means by “HE3-2(b)'s consumed clause (above-λ length = m·ℓ) survives verbatim in the corrected display”.
(c) **`[r2, F1]`** pins the twist rescaling to the coherent objects.
(d) **`[r1, F2]`'s (c)-clause bracket is the sharpest statement of why the band matters**: “κ > S places w above the side only when f₁ = 1”, with `.20`'s two counter-instances cited as the demonstration.
(e) **The “No graded frame … no digit-space bijection” sentence is `.04`'s fence, discharged here.**

**DERIVATION:** Lines 749–809, including the PE1-finding-4 characteristic repair. Quoted in the load-bearing part:

> “**[REPAIR, PE1 finding 4 — the binomial valuations.]** An earlier version
> of this proof asserted that each summand has dv EXACTLY dv(A_i)+(i−j)κ.
> That is false: the summand carries binom(i, j), whose valuation can be
> positive in mixed characteristic (e.g. i = p, j = 1) and which can vanish
> in equal characteristic p, so a purported unique minimiser can rise or
> disappear with no cancellation among residues. Only the INEQUALITY in (a)
> survives summand-wise. The proof of (b) is therefore run entirely at the
> RESIDUE level, where the binomial coefficients appear only through their
> images in K, and the statement needed is the char-free one:
>
> > the residue attached to A_j′ on the height-λ supporting line is exactly
> > the coefficient of Z^{j} in **R_λ(Z + s) computed in K[Z]** (binomial
> > coefficients reduced into K — that is what "computed in K" means), and
> > for any field K, if s is a root of R_λ of multiplicity exactly m then
> > Z^m ‖ R_λ(Z + s).
>
> The multiplicity fact is purely algebraic ((Z−s)^m ‖ R_λ ⟹
> R_λ(Z+s) = Z^m·(unit at 0)) and holds in every characteristic. So (b)'s
> conclusion — dv(A_j′) exceeds the λ-line height exactly for j < m — is
> intact, and it no longer rests on any summand-wise exact valuation.”

*Arithmetic audit (rule 22).*
- **The expansion.** `f = Σ_i A_i(Φ″ − w)^i = Σ_j Φ″^j·[Σ_{i≥j} C(i,j)(−w)^{i−j}A_i]` ✓ binomial theorem ✓.
- **(a)'s bound.** Each summand has `dv ≥ dv(A_i) + (i−j)·dv(w) = dv(A_i) + (i−j)κ` ✓ — **and only `≥`, because `v(C(i,j)) ≥ 0`** ✓ exactly the PE1-F4 point ✓.
- **The characteristic hazard, checked.** Mixed char: `C(p,1) = p` has `v = 1 > 0` ✓ so the summand rises ✓. Equal char `p`: `C(p,1) = p ≡ 0` ✓ so the summand vanishes ✓. **Both failure modes are real** ✓.
- **The multiplicity fact.** `(Z−s)^m ‖ R_λ(Z)` ⟹ substituting `Z ↦ Z+s`: `R_λ(Z+s)` has `((Z+s)−s)^m = Z^m` as exact divisor ✓ **char-free** ✓.
- **(b)'s length bookkeeping.** The slope-λ side of `P(F″)` has length `(L_λ − m) + T` ✓: it loses the `m` absorbed abscissae and gains the `T` collapsed ones ✓. Total polygon length is preserved: above-λ `T` → collapsed onto λ; new above-λ length `m`; so `μ = (below-λ) + [(L_λ − m) + T] + m` ✓ `= (below-λ) + L_λ + T` = the original ✓ **conserved.**
- **The collapsed residue.** A root `y` of `F` with `dv(y) > λ` gets `y″ = y − C(·)`, and `dv(C(·)) = λ` exactly, so `dv(y″) = λ` ✓ with residue `0 − s = −s ≠ 0` ✓ (the `y`-part contributes 0 since it sits strictly higher) ✓.
- **The residual.** `(R_λ(Z+s)/Z^m)·(Z+s)^T` — roots: the shifted old λ-residues `z − s` for `z ≠ s` ✓, plus `−s` with multiplicity `T` ✓ (from `(Z+s)^T`) ✓ **exactly as displayed.**
**Every step reproduces.**

**RESOLUTION TRACE:** statement 702–747 · proof 749–809 · char repair 757–776 · `[r2]` pin 726–728, 787–793 · corollary 811–815 (`.28`).

XREF: `GENHN_PROOF_2026-08-08.md:GENHN-3(a)` — count **11** (the (c) clause's source, cited as GENHN-3(c)(d)).
XREF: `HE6_PROOF_2026-08-08.md:LEMMA HE6-1L` — count **4**.

**TEETH:** **`.20`'s counter-instances are the tooth for the (c) band clause** (they “DO touch the invariants” at `κ = D′h`). Clause (b)'s corrected collapse is toothed indirectly: the peel's `m_s` profile at `he3r1_supp.py` P1/P3 measures exactly “the part of P(F″) strictly above λ has length m”. **`disclosed non-repair`:** the note states that the two old false clauses “**mutually cancel**” in the downstream count (see `.32`), “which is why the sealed battery never caught either (PE1 F5)” — a defect pair invisible to the instrument by construction. **Disposition: `decorrelated-model audit`** for F5; executable regression for the corrected clause.

---

### EFF.HE3.s1of2.28  [lemma]  — COROLLARY HE3-2′ (separability preserved along stage-α chains)

**CANONICAL STATEMENT:** verbatim, lines 811–815.

**FORM:** bold-headed paragraph (unquoted; the note gives this corollary no blockquote).

> “**COROLLARY HE3-2′ (separability is preserved along stage-α chains).**
> If R_λ is separable then so is R_λ(Z+s)/Z^m, and m = 1 for every root s
> of a separable R_λ; hence at a DECIDED leaf every stage-α refine peels
> exactly one simple residual root, and the recursion in LEMMA HE3-4 has
> depth ≤ d_λ.”

**CONDITIONALITY:** Unconditional given `.27`. **It is what makes DEFINITION 2's terminal-separability condition propagate** and what bounds the peel recursion. Untouched by every round and append (verified).

**DERIVATION:** Immediate from `.27`(b): separability ⟹ every root simple ⟹ `m = 1` ⟹ `R_λ(Z+s)/Z` is `R_λ`'s remaining factor, still separable ✓.

*Arithmetic audit (rule 22).* Depth bound: each refine removes one simple root from a degree-`d_λ` residual ✓, so at most `d_λ` refines ✓ **and the bound is tight** (a fully split separable residual needs `d_λ` peels) ✓.

**RESOLUTION TRACE:** statement 811–815 · consumed at 1149–1169 (`.34`'s stage-α step, termination).

**TEETH:** Indirect — the termination claim is exercised by every decided leaf in the enumeration (72,602 reader classifications, shard 2 §S9).

---

### EFF.HE3.s1of2.29  [lemma]  — LEMMA HE3-3 (the slope counts, Ψ-inversion) with (SEP)

**CANONICAL STATEMENT:** verbatim, lines 820–833 (the setup and the lemma), with the three-step proof at 835–890 and the (SEP) hypothesis at 892–935 carried as CONDITIONALITY and DERIVATION.

**FORM:** `###`-headed section body (setup, unquoted) + a blockquoted bold-headed lemma.

> “For an integer κ **[r1, F2] > D′h** and s ∈ K^× put
> **[r1, F1/F8]** Φ′_{κ,s} := Φ′ − C_{κ,s}, where C_{κ,s} ∈ O[x] is a
> letter-carrier for s at height κ (deg C < D′, dv(C) = κ,
> res(C(θ)/n(κ)(θ)) = s — existence for every s ∈ K^× is LEMMA HE3-1L,
> since κ > D′h > (D′−1)h), and
>
>     Ψ(κ, s) := Σ_{ρ : f(ρ) = 0} dv(Φ′_{κ,s}(ρ))  ∈ ℤ.
>
> > **LEMMA HE3-3.** Let n_λ := #{ρ : dv(Φ′(ρ)) = λ} for λ a slope of
> > P(F) (LEMMA HE3-0(iii) guarantees every root's dv is a slope). Then
> > **n_λ = D′·L_λ** for every slope λ, where L_λ is the horizontal
> > length of the λ-side of P(F).”

**CONDITIONALITY:** **The lemma as displayed is FALSE without a hypothesis the display does not carry, and the note says so at length.** From the PE1-finding-3 repair (892–912):

> “**[REPAIR, PE1 finding 3 — integer sampling does NOT always suffice; the
> inversion needs a hypothesis, satisfied automatically at μ ≤ 3.]** The
> independence claim above is FALSE in general. Counterexample (Codex PE1):
> if three distinct slopes all lie in one open integer interval — say
> S + 1/4, S + 1/3, S + 1/2 — then every legal sample has κ ≥ S + 1, so all
> sampled functions min(λ_i, ·) are the CONSTANTS λ_i, and the system
> collapses to Σc_i = 0, Σc_iλ_i = 0, which has a nonzero solution for
> three unknowns. So LEMMA HE3-3 must carry the hypothesis
>
>     (SEP)  the AVAILABLE samples separate the slopes: the vectors
>            (min(λ, κ))_κ for the distinct slopes λ, indexed over the
>            integers κ **[r1, F2] > D′h** at which Ψ(κ) is measurable —
>            the non-slope integers, plus the slope integers λ at which
>            K^× contains a non-root of R_λ — together with the free
>            root-count relation (see the [r1] supplement below), are
>            independent.”

`SUPERSESSION KIND: replacement` (the lemma acquires a hypothesis). **The `[r1]` bracket at 909–912 further records that the old index set (`κ > S`) was stale and that the old formulation over-quantified**: “the old formulation quantified over ALL integers where the proof can only sample the measurable ones.”
**(SEP) is discharged at μ ≤ 3 in three sub-cases** (914–935), the third of which — three consecutive integer slopes at `(Q,f₁) = (2,1)` — is **not** closed there and is handled by the `[r1-N1]` supplement (`.30`). **For general μ, (SEP) is a real hypothesis** and the note says the lift needs HE6-3's enlarged test family: “LEMMA HE6-3 (frozen at HEAD) proves the slope counts (SEP)-free by exactly that family.”

**DERIVATION:** Lines 835–890, three steps: (1) the stage side via HE3-1 + HE3-1′ and the convex duality (★); (2) the root side, with the `[r2, F3]` re-keyed justification; (3) the inversion. Steps (1) and (2) are quoted at `.31` (the (★) proof) and here in the load-bearing (2):

> “*(2) The root side.* Fix κ **[r1, F2] > D′h** not a slope, and any s.
> For each root ρ
> with dv(Φ′(ρ)) = λ we have dv(Φ′_{κ,s}(ρ)) = dv(Φ′(ρ) + w(ρ)) =
> min(λ, κ) exactly, since λ ≠ κ and dv(w(ρ)) = κ **[r2, F3 2026-08-09 —
> the justification re-keyed: the old parenthetical read "because ρ
> satisfies (T1), so dv(n(κ)(ρ)) = κ", the reason for the RETIRED
> monomial carrier ŝ·n(κ); after [r1, F1/F8], w = −C_{κ,s} is a general
> letter-carrier, and the height at ρ is the ξ-form slot read at ξ = ρ
> (LEMMA HE6-0″ as-of / LEMMA HE3-1L's mechanism at ρ): the slots of C
> attaining height κ contribute the residue Σ_{t ∈ T(κ)}
> res(c_{i₀+e₁t})·η_ρ^{t}, nonzero because {1, η_ρ, …, η_ρ^{f₁−1}} is
> F_Q-independent (η_ρ a root of the degree-f₁ irreducible ψ, by (T2)) —
> no level-1 cancellation can lift dv(C(ρ)) above κ, so
> dv(C(ρ)) = κ exactly]**. Summing over roots,
>
>     Ψ(κ) = Σ_λ n_λ · min(λ, κ) .                                   (★★)”

*Arithmetic audit (rule 22).*
- **(★★).** For a root at slope `λ ≠ κ`, `dv(Φ′(ρ) − C(ρ)) = min(λ, κ)` ✓ by the ultrametric with distinct heights ✓. Summing over the `D′μ` roots grouped by slope gives `Σ_λ n_λ min(λ,κ)` ✓.
- **The inversion system.** `Σ_λ (n_λ − D′L_λ)·min(λ,κ) = 0` for every measurable non-slope `κ > D′h` ✓ from (★) = (★★) ✓.
- **The two-slope independence argument.** For `λ₁ < λ₂`, `c₁min(λ₁,κ) + c₂min(λ₂,κ) ≡ 0`: at small `κ` (below both) both are `κ`, giving `c₁+c₂ = 0` ✓; at large `κ` both are constants, giving `c₁λ₁ + c₂λ₂ = 0` ✓; subtracting, `c₁(λ₁−λ₂) = 0` ✓ so `c₁ = c₂ = 0` ✓.
- **The PE1 counterexample.** Three slopes in one open integer interval `(S, S+1)`: say `S+1/4, S+1/3, S+1/2`. Every legal sample has `κ ≥ S+1 >` all three ✓, so `min(λ_i, κ) = λ_i` is constant ✓, and the system is `Σc_i = 0`, `Σc_iλ_i = 0` — **two equations, three unknowns** ✓ **nonzero solution exists** ✓ **the counterexample is exact.**
- **When can three slopes fit in one open integer interval?** Denominators must be `≥ 2, 3, 4` (distinct fractions in a unit interval with small denominators) ✓, and `Σ ℓ_λ d_λ = μ` with `ℓ ≥ 2,3,4` gives `μ ≥ 2+3+4 = 9` ✓ **exactly the note's “i.e. μ ≥ 9”** ✓.
- **Sub-case (a).** A non-integral slope forces `ℓ ≥ 2` hence `ℓd ≥ 2`; with `μ ≤ 3` at most two sides ✓, and two slope-classes separate with the free root count ✓.
- **Sub-case (b).** Three sides at `μ ≤ 3` forces three integer slopes with `d = 1` each (`Σ ℓd = 3` with three positive terms ⟹ each `= 1`) ✓; an interior integer sample exists unless the three are consecutive ✓.
- **Sub-case (c).** Three consecutive integers `a, a+1, a+2`: sample AT `a+1` with a non-root letter, available iff `|K^×| ≥ 2` i.e. `(Q,f₁) ≠ (2,1)` ✓ (at `(2,1)`, `K^× = {1}` and `d = 1` means the single residual root IS `1`) ✓.
**Every step and both counterexamples reproduce.**

**RESOLUTION TRACE:** statement 820–833 · proof 835–890 · (SEP) 892–912 · sub-cases 914–935 · supplement 937–961 (`.30`) · sampling Remark 963–979 (`.31`).

XREF: `HE6_PROOF_2026-08-08.md:LEMMA HE6-3` — count **12** (the (SEP)-free route).
XREF: `HE6_PROOF_2026-08-08.md:HE6-0″` — count **7**.
XREF: `CODEX_HE3PE1_2026-08-08.md:HE3` — count **15** (the counterexample's source, the uncounted Codex pass).

**TEETH:** **HE-PSI** exercises (★) and the inequality at 43,528 checks ✓. **(SEP) itself is PROOF-ONLY** — no battery row constructs a three-slopes-in-one-interval configuration (it needs `μ ≥ 9`, far beyond the note's `μ = 3` rows). The note's coverage-hole sentence: HE3-BOX-3's “μ ≥ 4 … NOT exercised by machine”. **Disposition: `decorrelated-model audit` for the finding (a Codex counterexample), PROOF-ONLY for the hypothesis.**

---

### EFF.HE3.s1of2.30  [lemma]  — the `[r1-N1]` consecutive-triple supplement

**CANONICAL STATEMENT:** verbatim, lines 937–961.

**FORM:** bold-headed bracketed block (self-found gap + its closure, two cases).

> “**[r1-N1, self-found this round — THE (2,1)-CONSECUTIVE-TRIPLE
> SUPPLEMENT (a justification gap of the old step (3) at μ = 3 not listed
> by PE1: at (Q, f₁) = (2, 1) and slopes a, a+1, a+2, the old sample set
> carries only the two relations Σc = 0 and Σcλ = 0 for three unknowns).**
> Recenter at the TOP side: Φ″ := Φ′ − ŝn(a+2) with s = 1 the top side's
> single residual root (1 ∈ F_Q is always a reachable letter). CASE
> A₀′ ≠ 0: by LEMMA HE3-2(b), P(F″) keeps the sides at a and a+1
> (below the recentering height) and its portion above a+2 is the single
> absorbed pin, a side of INTEGER slope δ := dv(A₀′) − dv(A₁′) ≥ a+3; so
> P(F″)'s slopes {a, a+1, δ} have the non-slope integer a+2 strictly
> inside the gap (a+1, δ), and the inversion applied at the key Φ″ — the
> free root count, the sample κ = a+2, and the above-δ samples form an
> invertible triangular system — pins its classes at D′·(1,1,1); the
> Φ″-classes are the Φ′-classes (dv(Φ″(ρ)) = a, a+1 exactly on the slope-a
> and slope-(a+1) classes since a, a+1 < a+2 = dv(ŝn(a+2)(ρ)), and > a+2
> exactly on the top class by the residue cancellation), so n_λ = D′L_λ at
> each of the three sides. CASE A₀′ = 0: then Φ″ | f exactly (disc f ≠ 0
> gives Φ″ ∤ f/Φ″), the top class contains Φ″'s D′ roots, and the
> development of g := f/Φ″ at Φ″ is P(F″) shifted left by one abscissa —
> a TWO-slope polygon at {a, a+1}, inverted as in sub-case (a); g has no
> root with dv(Φ″(ρ)) > a+2 (its Φ″-slopes are a, a+1), so
> n_{a+2} = D′·1 and n_a = n_{a+1} = D′·1 again. Either way the three-
> consecutive-slope configuration is inverted at level 1 with no new
> instrument; independently, LEMMA HE6-3 (frozen) covers it as-of
> 2026-08-09.]**”

**CONDITIONALITY:** **A self-found gap closed in the same round, with two exhaustive cases and independent external cover.** Three things to preserve: (i) it was **not** in PE1's list — the note found it auditing its own repair; (ii) the closure needs **no new instrument** (level-1 only); (iii) **LEMMA HE6-3 covers it independently**, so the note has two routes.
**Its demo geography is DISCLOSED as wrong at `[r2]` F-5** (`.07`): the `he3r1_supp.py` P2-N1 demo ran at `(Q,f₁) = (3,2)` where the gap is **not live** (the gap needs `K^× = {1}`, i.e. `(Q,f₁) = (2,1)`). The live-geography machine contact is PE2's FR-D over ℤ₂. `SUPERSESSION KIND: scope-pin` on the machine record, not on the mathematics.

**DERIVATION:** Quoted in full; two cases, exhaustive on `A₀′ = 0` or not.

*Arithmetic audit (rule 22).*
- **Case A₀′ ≠ 0.** After recentering at the top slope `a+2` with `m = 1` (the single residual root, `d = 1`), `.27`(b) gives above-λ length exactly `m = 1` ✓ — a single absorbed pin ✓. Its slope `δ = dv(A₀′) − dv(A₁′)` ✓ (a two-point polygon's slope) and `δ ≥ a+3` ✓ (strictly above `a+2`, integer). So `P(F″)` has slopes `{a, a+1, δ}` with `a+2` strictly inside `(a+1, δ)` ✓ **a legal non-slope sample** ✓. Triangular system: free root count (1 relation) + sample at `a+2` (1) + above-δ samples (1) = 3 relations for 3 unknowns ✓ invertible ✓.
- **Class transfer.** For a root at slope `a` or `a+1`: `dv(Φ″(ρ)) = min(dv(Φ′(ρ)), a+2) = dv(Φ′(ρ))` ✓ since `a, a+1 < a+2` ✓. For the top class: residue cancellation lifts it above `a+2` ✓. **So the Φ″-classes are the Φ′-classes** ✓.
- **Case A₀′ = 0.** `Φ″ | f` ✓ (the constant term of the Φ″-development vanishes). `disc f ≠ 0` gives `Φ″ ∤ f/Φ″` ✓ (else `Φ″²  | f`, a repeated factor). The top class then contains exactly `Φ″`'s `D′` roots ✓. `g := f/Φ″` has Φ″-development = `P(F″)` shifted left one abscissa ✓ (dividing by `Φ″` drops the index by one) ✓ → a two-slope polygon at `{a, a+1}` ✓ → sub-case (a) ✓. Counts: `n_{a+2} = D′·1` ✓ and `n_a = n_{a+1} = D′·1` ✓ **all three sides give `D′L_λ` with `L_λ = 1`** ✓ consistent with `μ = 3 = 1+1+1` ✓.
**Both cases close and the arithmetic reproduces.**

**RESOLUTION TRACE:** statement 937–961 · machine record 1520–1535 (shard 2, with the `[r2] F-5` scope disclosure) · independent cover: `HE6_PROOF` LEMMA HE6-3.

XREF: `HE6_PROOF_2026-08-08.md:LEMMA HE6-3` — count **12**.
ARTIFACT: `verification/openmath/he3r1_supp.py` ✓ · `he3_pe2fresh.py` ✓ (FR-D, the live-geography contact).

**TEETH:** **Both branches machine-demonstrated, but at the WRONG geography first.** `he3r1_supp.py` P2-N1 ran at `(3,2)` (gap not live) — **disclosed** at `[r2]` F-5; PE2's FR-D then ran both branches over ℤ₂ at the live `(2,1)` geography ✓. **Disposition: `signed vacuity disclosure` on the first leg, `accepted-with-decorrelation-supplied` by the second.**

---

### EFF.HE3.s1of2.31  [scope-record]  — the integer-sampling Remark and the corrected recipe

**CANONICAL STATEMENT:** verbatim, lines 963–979, together with the convex-duality proof (★) at 846–857 which this unit homes (it is cited by designation from `.11` and from HE6/HE7's pins).

**FORM:** bold-headed remark with a struck recipe and an indented ASCII replacement.

> “**Remark (integer sampling suffices under (SEP)) [r1, F2/N1 —
> recipe corrected].** Only the values of the concave function at integer
> heights are available (letter-carriers exist at integer dv-heights
> only). ~~Concretely, with κ₀ := ⌊min slope⌋ …~~ the old recipe could
> land at κ₀ ≤ D′h, where the test key perturbs the residual ψ itself
> (LEMMA HE3-1's counter-instances); the corrected sample set is
>
>     κ ∈ { D′h + 1, …, ⌈max slope⌉ + 1 } ∖ { slopes without a generic
>     letter } ,
>
> together with the FREE relation Σ_λ n_λ = D′μ = Σ_λ D′L_λ (the root
> count — every root carries a slope by LEMMA HE3-0(iii), and the side
> lengths sum to μ), which replaces the below-minimum regime: no sample
> below the smallest slope is needed. The triangular elimination proceeds
> from the largest slope downward over these samples, per the (SEP)
> sub-cases above; the second difference of Ψ at an available integer κ is
> supported on the slopes.”

and the (★) display with its proof (846–857):

> “    h_F(κ) = min_j (dv(A_j) + jκ) = Σ_{slopes λ} L_λ · min(λ, κ) .   (★)
>
> [Proof of (★): both sides are concave piecewise-linear in κ. For
> κ ≥ max slope both equal Σ_λ L_λλ = dv(A₀) (left side: the minimum is at
> j = 0). For κ ≤ min slope both equal μκ (left side: minimum at j = μ,
> where dv(A_μ) = 0). Between consecutive slopes both are affine with the
> same increment: d/dκ of the right side is Σ_{λ ≥ κ} L_λ, and the left
> side's minimising index j(κ) is the abscissa of the vertex where the
> supporting line of slope κ touches P(F), i.e. exactly Σ_{λ ≥ κ}L_λ. ∎]”

**CONDITIONALITY:** **The (★) display is BYTE-FROZEN under (F3)** — “the (★) display stay[s] byte-identical (the frozen consumers' pins)”, and both HE6 and HE7 pin it. **The Remark's recipe is corrected**; the struck recipe “could land at κ₀ ≤ D′h, where the test key perturbs the residual ψ itself”. `SUPERSESSION KIND: replacement`. The corrected recipe's key move is replacing the below-minimum regime by the FREE root-count relation — which is what makes `.11`'s COUNT step and `.30`'s triangular systems work without illegal samples.

**DERIVATION:** (★)'s proof is quoted above and is pure convex duality.

*Arithmetic audit (rule 22) of (★), verified at both ends and in the middle.*
- **`κ ≥ max slope`.** LHS: `min_j(dv(A_j) + jκ)` is attained at `j = 0` (largest `κ` penalises large `j`) giving `dv(A₀)` ✓. RHS: `Σ_λ L_λ min(λ,κ) = Σ_λ L_λ λ` ✓, and `Σ_λ L_λλ = dv(A₀)` ✓ — the total drop across the polygon from `(μ,0)` to `(0, dv(A₀))` ✓.
- **`κ ≤ min slope`.** LHS attained at `j = μ` (`dv(A_μ) = 0`) giving `μκ` ✓. RHS: `Σ_λ L_λ κ = κ·Σ_λ L_λ = μκ` ✓.
- **Slope of each side.** `d/dκ` RHS `= Σ_{λ ≥ κ} L_λ` ✓ (only slopes above `κ` still contribute a `κ`-term) ✓; LHS's minimising `j(κ)` is the abscissa where the slope-`κ` supporting line touches, which is `Σ_{λ ≥ κ} L_λ` ✓ (counting from the right end `j = μ`… reading from the left, the touching abscissa is the total length of sides steeper than `κ` ✓). **Both derivatives agree** ✓ and both functions are concave piecewise-linear ✓, so agreeing at one point plus equal derivatives everywhere gives equality ✓.
- **The corrected sample range.** `{D′h+1, …, ⌈max slope⌉+1}` — its lower end is the first legal height ✓ (`.20`'s band) and its upper end exceeds every slope ✓ so the “above-top” regime is reachable ✓.
**(★) is correct and the recipe's endpoints are right.**

**RESOLUTION TRACE:** statement 963–979 · (★) 846–857 (byte-frozen) · consumed at 200–202 (`.11`), and by HE6/HE7 per `.06`.

XREF: `HE7_PROOF_2026-08-08.md:HE3-3` — count **2** (HE7's pin on the (★) of HE3-3 step 1).
XREF: `HE6_PROOF_2026-08-08.md:HE3-1` — count **1**.

**TEETH:** **HE-PSI verifies (★) directly** — “the support-function identity (★) holds at every sampled κ on every in-window polygon”, 0 violations over 43,528 checks (shard 2, Q2). **Disposition: executable regression.**

---

### EFF.HE3.s1of2.32  [lemma]  — LEMMA HE3-4 (the residue peel)

**CANONICAL STATEMENT:** verbatim, lines 983–989.

**FORM:** display (blockquoted bold-headed lemma with a `[r2, F1]` inline pin).

> “> **LEMMA HE3-4.** Fix a slope λ and write R_λ **[r2, F1: the coherent
> > R_λ of DEFINITION 1 [r2]]** = Π_r r^{m_r} (r
> > irreducible over K); at a DECIDED leaf all m_r = 1. Let, for each r,
> > S_r := {ρ : dv(Φ′(ρ)) = λ and res(Φ′(ρ)/n(λ)(ρ)) is a root of r}.
> > Then |S_r| = D′·ℓ·deg r = D′·e_s·f_s. (For ℓ = e_s ≥ 2 the classes
> > S_r are indexed by the residual of the λ-side in its own lattice
> > normalization; see the proof.)”

**CONDITIONALITY:** **The displayed definition of `S_r` is ILL-DEFINED at `ℓ ≥ 2` and is replaced by a dated append.** R8-4 (1774–1793, shard 2):

> “In LEMMA HE3-4 replace the displayed definition of S_r by the following
> definition. Write y_ρ := Φ′(ρ), λ = u/ℓ in lowest terms, and
>
>     β_ρ :=
>       res(y_ρ / n(λ)(ρ))          if ℓ = 1,
>       res(y_ρ^ℓ / n(u)(ρ))        if ℓ ≥ 2.
>
> Then
>
>     S_r := { ρ : dv(y_ρ) = λ and ι_ρ(r)(β_ρ) = 0 },
>
> where ι_ρ : K → k̄ is the embedding η_θ ↦ η_ρ from LEMMA HE3-0. …
> Thus β_ρ exists, and this definition is exactly the repaired root read
> of HE3-0(iii). All later occurrences S_{Z−s} lie in the integer-slope
> case and are unchanged.”

`SUPERSESSION KIND: replacement` (the definition). **CHAIN: the frozen `res(Φ′(ρ)/n(λ)(ρ))` display → R8-4's piecewise `β_ρ`. TERMINAL: R8-4.** The A5 verification note (1843–1847, shard 2) states exactly why the r1 round missed it: the same repair was installed at HE3-0(iii)/HE3-0′ (`.25`, `.26`) but “this correction propagates it to the one display the r1 round missed”.
Second: the `[r2, F1]` pin routes `R_λ` to the coherent object.
Third: **“at a DECIDED leaf all m_r = 1”** is the separability hypothesis from DEFINITION 2 (`.15`).

**DERIVATION:** Lines 991–1020 (the integer-slope rational peel, `.33`'s scope note, and the two boxed reductions at 1060–1086). The operative rational-peel argument, quoted:

> “*Proof.* First assume λ is an integer (ℓ = 1) and r = Z − s is linear
> with s ∈ K^× **[r1, F1: s ranges over ALL of K^×, carried by
> C = C_{λ,s} from LEMMA HE3-1L — at f₁ ≥ 2 this is the repaired letter
> reach; λ > D′h > (D′−1)h makes every letter available]**. Apply LEMMA
> HE3-3 to the recentered key Φ″ = Φ′_{λ,s} = Φ′ − C: its own polygon
> P(F″) is described by LEMMA HE3-2(b), and its slope counts are D′ times
> its side lengths. Now for a root ρ,
>
>     dv(Φ″(ρ)) > λ ⟺ dv(Φ′(ρ)) = λ and res(Φ′(ρ)/n(λ)(ρ)) = ι_ρ(s)
>
> **[r1, F5 — the old display carried a second disjunct "or
> dv(Φ′(ρ)) > λ", which is FALSE: such a root has
> res(Φ″(ρ)/n(λ)(ρ)) = 0 − ι_ρ(s) ≠ 0, hence dv(Φ″(ρ)) = λ EXACTLY —
> under recentering the above-λ material COLLAPSES onto the λ-line
> rather than passing through. The corrected equivalence is one clause:
> Φ″(ρ) = Φ′(ρ) − C(ρ) with dv(C(ρ)) = λ exactly (HE6-0″ at ρ), so
> dv(Φ″(ρ)) > λ demands dv(Φ′(ρ)) = λ AND residue cancellation.]**
> Hence — the DIRECT route, now the operative argument, with no
> subtraction of above-λ counts —
>
>     |S_{Z−s}| = #{ρ : dv(Φ″(ρ)) > λ} = D′·(length of P(F″) above λ)
>               = D′·m_s = D′
>
> by LEMMA HE3-3 applied at the key Φ″ and LEMMA HE3-2(b)'s [r1]
> corrected clause (the portion of P(F″) above λ has length exactly m_s,
> the multiplicity of s in R_λ; = 1 here at a decided leaf). ✓ **[The old
> display subtracted #{dv(Φ′(ρ)) > λ} from #{dv(Φ″(ρ)) > λ}; its two
> errors — the false second disjunct here and the false "all other sides
> are unchanged" in HE3-2(b) — cancelled to the same |S_{Z−s}| = D′m_s,
> which is why the sealed battery never caught either (PE1 F5).]**”

*Arithmetic audit (rule 22).*
- **The corrected equivalence.** `Φ″(ρ) = Φ′(ρ) − C(ρ)` with `dv(C(ρ)) = λ` exactly ✓. If `dv(Φ′(ρ)) > λ`: the difference has `dv = λ` exactly (the `C` term dominates) with residue `−ι_ρ(s) ≠ 0` ✓ **so NOT `> λ`** ✓ — the old second disjunct is indeed false ✓. If `dv(Φ′(ρ)) < λ`: difference has `dv = dv(Φ′(ρ)) < λ` ✓. If `= λ`: `> λ` iff the residues cancel, i.e. `res(Φ′(ρ)/n(λ)(ρ)) = ι_ρ(s)` ✓ **one clause** ✓.
- **The count.** `|S_{Z−s}| = #{ρ : dv(Φ″(ρ)) > λ}` ✓ by the equivalence ✓ `= D′·(above-λ length of P(F″))` ✓ by HE3-3 at `Φ″` ✓ `= D′m_s` ✓ by `.27`(b) ✓ `= D′` at a decided leaf ✓.
- **The error-cancellation.** Old route: `#{dv(Φ″) > λ} − #{dv(Φ′) > λ}`. With the false disjunct, `#{dv(Φ″) > λ}` would have included the above-λ roots, i.e. `D′m_s + D′T`; with the false “all other sides unchanged”, `#{dv(Φ′) > λ} = D′T` would have been unchanged; the difference is `D′m_s` ✓ **the same answer** ✓ **the two errors cancel exactly** ✓ **confirming the note's diagnosis and explaining the battery's blindness.**
**Every step reproduces, including the cancellation that hid the pair of defects.**

**RESOLUTION TRACE:** statement 983–989 · proof 991–1020 · μ ≤ 3 scope 1022–1058 (`.33`) · boxed reductions 1060–1086 · consistency check 1088–1090 · correction sites 1691–1734 (R8-2), 1774–1793 (R8-4).

XREF: `HE6_PROOF_2026-08-08.md:HE6-0″` — count **7**.
XREF: `HE3_PROOF_2026-08-08.md:LEMMA HE3-1L` — self-count **12**.

**TEETH:** **`he3r1_supp.py` P1** — the repaired peel at PE1's counter-instance: `m_s = 1` at each of the 3 residual roots (including both `K∖F₃` letters), `m_s = 0` at the other 5 letters of `F₉^×`, `Σ_s D′m_s = 6 = deg f`, PARI `σ = {(1,2),(1,2),(1,2)}` on the exact member and a junk variant. **“The class-size splits (4,0)/(2,2)/(0,4) that PE1 showed the old text could not exclude are excluded by measurement.”** **Disposition: executable regression, exhaustive over the letter set; the PE1 counter-instance FIRED against the old text.** **`disclosed non-repair`:** the sealed battery never caught F5 because the two errors cancel — the note says so.

---

### EFF.HE3.s1of2.33  [scope-record]  — μ ≤ 3 is base-change-free; the two reductions and their boxing

**CANONICAL STATEMENT:** verbatim, lines 1022–1086 (the PE1-findings-1+2 repair block, the two μ ≤ 3 bullets, the cheapness diagnosis, and the two boxed reductions (i)/(ii)).

**FORM:** bold-headed bracketed repair block + two bullets + a bold verdict sentence + two lettered reductions.

> “**[REPAIR, PE1 findings 1+2 — μ ≤ 3 IS BASE-CHANGE-FREE; the two
> base-change reductions below are μ ≥ 4-only and are BOXED.]** Before the
> general reductions, note that at μ ≤ 3 neither is needed:
> * *ℓ ≥ 2 sides.* ℓd ≤ μ ≤ 3 with ℓ ≥ 2 forces d = 1, so the side carries
>   a SINGLE label and |S| = D′L_λ = D′ℓ holds by LEMMA HE3-3 alone (all
>   roots at that slope carry that one label). No peel, no base change.
> * *non-K-rational residual factors on an integer-slope side.* After
>   peeling every K-rational root by the recentering paragraph above (which
>   uses no base change) **[r1, F1: "every K-rational root" is now an honest
>   clause — at f₁ ≥ 2 the roots s ∈ K^× ∖ F_Q^× are carried by LEMMA
>   HE3-1L's C-letters, unreachable under the old ŝ·n(λ) display; on PE1's
>   counter-instance — genre (3;1,2,3;1), K = F₉, single side λ = 3,
>   residual (Z−1)(Z−i)(Z+i) — the repaired peel pins |S_{Z−1}| =
>   |S_{Z−i}| = |S_{Z+i}| = D′ = 2 severally, where the old text peeled
>   s = 1 and had no instrument against (4,0)/(2,2)/(0,4) splits of the
>   {i, −i} mass; machine-verified this round, §S9′ P1]**, the leftover
>   part of R_λ has degree ≤ d ≤ 3 and NO
>   K-rational root, hence is a SINGLE irreducible factor r (degree 2 or 3).
>   Its class size is then FORCED by subtraction: LEMMA HE3-3 gives
>   D′d roots at the slope, the peeled rational roots account for
>   D′·(d − deg r) of them (each simple at a decided leaf), so
>   |S_r| = D′·deg r — with no nonemptiness assumption and no base change.
>   Two distinct non-rational factors on one side would need d ≥ 4, i.e.
>   μ ≥ 4.
> So THEOREM HE3.A at μ ≤ 3 — the first-live case of [GENHN-HE], degrees
> n ≤ 7 — uses only the rational peel and this subtraction. The two
> reductions below are what μ ≥ 4 needs, and they are exactly what
> HE3-BOX-6 boxes; Codex PE1 findings 1 and 2 show that BOTH are stated too
> cheaply (not just the ramified one): under an unramified base change of
> degree c, Φ′ splits into gcd(f₁, c) factors and the stage key degree drops
> from D′ to D′/gcd(f₁, c), so "each rational residual root contributes
> D′ roots" is false as written and the counts do not transfer verbatim;
> choosing c coprime to f₁ repairs it only when gcd(deg r, f₁) = 1. Under
> the ramified base change, rescaling dv does not multiply a root-set
> cardinality, the label can split into several integer-slope labels, and
> when char K | ℓ the new residual can turn inseparable. **Both branches
> below are therefore to be read as BOXED (HE3-BOX-6), not proved.**”

**CONDITIONALITY:** **“Both branches … BOXED” is SUPERSEDED — R8-2 proves branch (i).** From 1691–1734 (shard 2):

> “The assertion in §S6.2 that BOTH base-change branches remain boxed is
> superseded for branch (i). Only the ramified branch (ii) remains in
> HE3-BOX-6.
>
> > LEMMA HE3-4U (unramified split-sum). Let λ be an integer slope and
> > let r ∈ K[Z] be a separable irreducible factor of R_λ of degree d.
> > Then |S_r| = D′d.”

with the closing: “Therefore §S6.2 branch (i) is proved, not boxed. The phrase “both branches below are therefore to be read as BOXED” is corrected to “branch (ii) alone is BOXED.” COROLLARY HE3.B's single μ ≥ 4 reservation is consequently again accurate”.
`SUPERSESSION KIND: license` + **inventory completion** (the box shrinks). **CHAIN: §S1/HE3-BOX-6's “ONE branch” → §S6.2's “BOTH … BOXED” (internal contradiction) → R8-2's LEMMA HE3-4U → “branch (ii) alone”. TERMINAL: R8-2, awaiting sol discharge-confirmation.**
**The A5 verification note names the contradiction explicitly** (1830–1833, shard 2): “§S1's branch-(ii)-only reservation (L350–353) vs §S6.2's "BOTH are stated too cheaply" (L1049) confirmed as the internal contradiction”.
**The μ ≤ 3 bullets are untouched and remain the load-bearing content for the headline.**

**DERIVATION:** The two μ ≤ 3 bullets are self-contained; the boxed reductions (i)/(ii) are at 1060–1086 and are explicitly not proved as displayed.

*Arithmetic audit (rule 22).*
- **Bullet 1.** `ℓd ≤ μ ≤ 3` with `ℓ ≥ 2` ⟹ `d ≤ 3/2` ⟹ `d = 1` ✓. Single label ⟹ `|S| = D′L_λ = D′ℓd = D′ℓ` ✓.
- **Bullet 2.** After peeling all K-rational roots, the leftover has no K-rational root, degree `≤ d ≤ 3`. A degree-2 or degree-3 polynomial with no root in `K` **and no repeated factor** (decided leaf) is irreducible ✓ (degree ≤ 3 with no root ⟹ irreducible ✓). Subtraction: `D′d − D′(d − deg r) = D′ deg r` ✓.
- **“Two distinct non-rational factors need d ≥ 4”** ✓ (each has degree ≥ 2).
- **The unramified cheapness.** Under a degree-`c` unramified base change, `Φ′` (with `f₁ | ` its residue degree) splits into `gcd(f₁, c)` conjugate factors ✓, so the stage key degree drops to `D′/gcd(f₁,c)` ✓ — **and “each rational residual root contributes D′ roots” is then false** ✓. The repair condition “`c` coprime to `f₁`” makes `gcd(f₁,c) = 1` ✓ so `Φ′` stays irreducible ✓ — but then the residue field only grows by `c`, and making `r` split needs `deg r | c`, so one needs `gcd(deg r, f₁) = 1` for both ✓ **exactly the displayed condition** ✓.
- **R8-2's repair, audited.** `c := f₁m` with `d | m`: then `f₁ | c` ✓ so `Φ′` splits into exactly `f₁` conjugate keys each of degree `e₁` ✓ (`gcd(f₁, c) = f₁`). Relative residue extension degree `c/f₁ = m` ✓, and `d | m` makes the image of `r` split into `d` distinct linear factors ✓. Per component: `e₁` roots per linear factor × `d` factors = `e₁d` ✓. Summing over `f₁` components: `f₁·e₁·d = D′d` ✓ **exactly the HE3-4 display at ℓ = 1** ✓. **The repair is arithmetically sound and this compiler's independent recomputation matches the A5 verification note's own check (1833–1837).**
**Every step reproduces.**

**RESOLUTION TRACE:** statement 1022–1086 · consistency check 1088–1090 · correction site 1691–1734 (R8-2).

XREF: `HE3_PROOF_2026-08-08.md:HE3-4U` — self-count **2** (the appended lemma).
XREF: `GENIND_PROOF_2026-08-08.md:LEMMA GENIND-3` — count **6** (the sibling splitting R8-2 imports).

**TEETH:** **PE1's counter-instance is the fired tooth for bullet 2's honesty clause** — genre `(3;1,2,3;1)`, `K = F₉`, residual `(Z−1)(Z−i)(Z+i)`, with the old text unable to exclude `(4,0)/(2,2)/(0,4)` splits. *Arithmetic check:* `D′ = e₁f₁ = 1·2 = 2` ✓, three labels each of size `D′ = 2` ✓, total `6 = D′μ = 2·3` ✓; the excluded splits `(4,0), (2,2), (0,4)` all sum to 4 = the `{i,−i}` mass `2·2` ✓ **consistent.** **Disposition: planted counter-instance, fired; excluded by measurement at `he3r1_supp.py` P1.** **Branch (ii) is PROOF-ONLY and unexercised** — HE3-BOX-3: “NOT exercised by machine: … μ ≥ 4 (where LEMMA HE3-4's ramified base-change branch … first bite)”.

---

### EFF.HE3.s1of2.34  [theorem]  — §S6.3, the proof of THEOREM HE3.A (four steps)

**CANONICAL STATEMENT:** [ASSEMBLED — §S6.3 is THEOREM HE3.A's DERIVATION (template rule 1), emitted as a unit because three of its four steps carry their own corrections and the stage-CS step carries its own carrier rider. The statement proved is `.16`.]

**FORM:** `###`-headed section body: four bold-italic-headed steps (Base / Stage-α / Stage-CS / Embedded genres) plus a closing line.

**DERIVATION (= the unit's content), lines 1092–1205, quoted in the load-bearing parts:**

> “Let ℓ be a decided leaf and f a lift with disc(f) ≠ 0. Induct on the
> number of stage-α refines and stage-CS events in ℓ's history; the
> statement to prove at each stage is the displayed dictionary.
>
> *Base (depth-0 decided read).* The stage type is
> τ = {(ℓ_λ, deg r)}_{(λ, r)} over the labels of P(F). By LEMMA HE3-0 every
> root of f carries a label; by LEMMA HE3-4 the class of each label has
> exactly D′·e_s·f_s elements; by the consistency check the classes
> partition the D′μ roots. Each class S_{λ,r} is stable under
> Gal(K̄₀/K₀): Galois preserves dv and acts on residues through
> k̄-automorphisms, and it permutes the roots of the irreducible r, so it
> permutes ⊔_{β|r}S_{Z−β} = S_{λ,r}. By COROLLARY HE3-0′ each ρ ∈ S_{λ,r}
> has [K₀(ρ) : K₀] ≥ e₁ℓ_λ·f₁ deg r = D′e_sf_s = |S_{λ,r}|. A Galois-stable
> set of size N all of whose elements have orbit size ≥ N is a single
> orbit of size exactly N.
> ~~[JUSTIFICATION GAP, PE1 finding 6 — the semilinearity of the Galois
> action on residues. … Assume it and continue.]~~ **[r1, F3 — the gap is
> DISCHARGED at level 1; nothing is assumed.** …]** Hence S_{λ,r} is the
> root set of a single monic
> irreducible factor of f, of degree D′e_sf_s, and its e ≥ e₁e_s,
> f ≥ f₁f_s with ef = degree forces
>
>     e = e₁·e_s ,   f = f₁·f_s   exactly.
>
> Doing this for every label gives σ(f) = {(e₁e_s^{(i)}, f₁f_s^{(i)})}_i.”

> “*Stage-α step.* If the read refines at (λ, s) (a residual root of
> multiplicity m ≥ 2 — so the leaf is not decided at this node), then by
> LEMMA HE3-2(b) the recentered key Φ″ has a polygon whose portion above
> λ has length exactly m, the corresponding block of D′m roots is
> S_{λ, Z−s} (LEMMA HE3-4's computation, which did not use m = 1 —
> it gives |S_{λ,Z−s}| = D′m, by the [r1] direct route), and this block's
> own labels are read at Φ″ — **[r1, F5: specifically, at the part of
> P(F″) STRICTLY ABOVE λ, which by the corrected LEMMA HE3-2(b) is the
> absorbed sub-block alone; the collapsed above-λ material of the other
> blocks sits ON the λ-line of P(F″) and never enters the sub-block's
> onward read. The old sentence "the blocks at slope λ with other
> residues, and at other slopes, are untouched (their labels at Φ″ agree
> with those at Φ′)" leaned on the false clause of the old (b): the
> above-λ blocks' labels are NOT readable at Φ″ — they are read at Φ′
> (or at their own recenterings), where the induction reads them]**.
> Apply the inductive hypothesis to the sub-block …
> Termination: each refine strictly increases the floor λ and dv-heights
> are bounded by the leaf's window (GENHN-3(a)), so the chain is finite —
> and at a decided leaf it ends with all residuals separable.”

> “*Stage-CS step.* … then the block is a composite stage OF THE STAGE
> SYSTEM: a genre in the sense of GENHN.CLASS with base ring ~~R (a
> complete DVR with finite residue field K)~~ **[r1, F7: O_L, the
> valuation ring of L = K₀(θ) — a complete DVR with residue field K; the
> order R = O[θ] need not be one, so the re-instantiation must carry the
> development over O_L. This step is reachable only at μ ≥ 4 (GENIND.A(IV)
> descent), i.e. inside the HE3-BOX-6 region, where the O_L re-carrier is
> recorded as part of the box]**, key degree e₁′f₁′,
> multiplicity μ′, and its own integer value ladder. Every hypothesis of
> THEOREM HE3.A holds for it … Apply THEOREM HE3.A at multiplicity μ′: the inner pieces are
> (e_s′, f_s′) relative to R′ = R[y]/(inner key), which relative to R
> read (e₁′e_s′, f₁′f_s′), and relative to O read
> (e₁e₁′e_s′, f₁f₁′f_s′) — the multiplicative composition of LEMMA
> GENHN-T(b), here PROVED for σ rather than assumed, because (T1)/(T2)
> stack … Since
> e₁′f₁′μ′ ≤ μ with e₁′f₁′ ≥ 2, we have μ′ ≤ μ/2 < μ, so the recursion
> is well-founded on μ.”

> “*Embedded genres.* If the genre is embedded …, LEMMA GENIND-3's
> scale-then-Hensel step (@ pin) splits the sibling factor off over O first; σ(f) is then the
> disjoint union of the sibling blocks' own σ and the stage block's,
> computed above. (The machine-side caveat — which stage leaves an
> AMBIENT window certifies — is GENHN-BOX-4/S11.F, a statement about
> window data, not about this theorem; see HE3-BOX-2.)
>
> This exhausts the species (GENIND.A(I)) reachable inside a decided
> leaf's history, so THEOREM HE3.A is proved. ∎”

**CONDITIONALITY:**
(a) **The PE1-finding-6 justification gap is DISCHARGED, not assumed** — the struck text (“Assume it and continue”) is preserved and replaced by LEMMA HE3-6 (`.35`). This is the single most important `[r1]` upgrade: “"unconditional" was internally contradicted by that assumption; it no longer is” (`.17`).
(b) **The stage-α step's `[r1, F5]` correction is the downstream half of `.27`(b)'s repair** — the old sentence about untouched blocks “leaned on the false clause of the old (b)”.
(c) **The stage-CS step's `[r1, F7]` carrier rider** puts the recursion over `O_L`, and **fences it to μ ≥ 4**, i.e. inside HE3-BOX-6.
(d) **“the multiplicative composition of LEMMA GENHN-T(b), here PROVED for σ rather than assumed”** — a claim about a GENHN lemma that was later **REFUTED at the leaf level** in GENHN itself (its `[r2]`, compiled at `spec/EFF-GENHN-s1of2.md` `.17`) and replaced by T(b)′. **HE3's sentence is about σ-composition via stacking (T1)/(T2), which is exactly the part GENHN's `[r2]` says SURVIVES** (“The multiplicative (e,f)- and σ-composition FORMULAS survive”). So HE3's claim is compatible — but it cites the refuted lemma by name. Recorded as source defect 6; no silent re-pointing.
(e) The whole stage-CS step is unreachable at μ ≤ 3 (`.17`'s descent), so the μ ≤ 3 headline does not depend on (c) or (d).

*Arithmetic audit (rule 22).*
- **The single-orbit step.** A Galois-stable set of size `N` in which every element has orbit size `≥ N`: orbits partition the set, each of size `≥ N`, total `N` ⟹ exactly one orbit of size `N` ✓.
- **The forcing.** `e ≥ e₁e_s`, `f ≥ f₁f_s`, `ef = D′e_sf_s = (e₁e_s)(f₁f_s)` ✓ ⟹ both inequalities are equalities ✓.
- **The consistency check** (1088–1090): `Σ_λ Σ_{r|R_λ} D′ℓ_λ deg r = D′ Σ_λ ℓ_λ d_λ = D′ Σ_λ L_λ = D′μ = deg f` ✓ **exact** ✓ (using `Σ_r deg r = d_λ` at a decided leaf and `L_λ = ℓ_λ d_λ`).
- **The stage-CS composition.** Relative to `R`: `(e₁′e_s′, f₁′f_s′)`; relative to `O`: multiply by `(e₁, f₁)` ✓ giving `(e₁e₁′e_s′, f₁f₁′f_s′)` ✓. Degree: `e₁e₁′e_s′ · f₁f₁′f_s′ = D′ · e₁′f₁′ · e_s′f_s′` ✓ and summing over inner labels gives `D′ · e₁′f₁′ · μ′ ≤ D′μ` ✓ consistent.
- **Termination.** Each refine strictly increases the floor `λ`; `dv`-heights bounded by the window ⟹ finite ✓.
**Every step reproduces.**

**RESOLUTION TRACE:** statement (the theorem) 312–331 · proof 1092–1205 · Galois lemma 1118–1140 (`.35`) · correction sites 1691–1734 (R8-2 at the peel it consumes), 1774–1793 (R8-4 at `S_r`'s definition).

XREF: `GENHN_PROOF_2026-08-08.md:THEOREM GENHN.CLASS` — count **7**.
XREF: `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-T(b)` — count **11** (the cited lemma; see source defect 6).
XREF: `GENIND_PROOF_2026-08-08.md:GENIND.A(I)` — count **3** · `GENIND.A(IV)` — count **5** · `LEMMA GENIND-3` — count **6**.
XREF: `GENHN_PROOF_2026-08-08.md:GENHN-BOX-4` — count **3** · `S11.F` — count **10**.

**TEETH:** **HE-SIG's 947 PARI jobs across all five μ = 3 stage types** test the base + stage-α steps end to end ✓. **The stage-CS step is PROOF-ONLY and unexercised** (μ ≥ 4). **Disposition: executable regression against an independent oracle for the μ ≤ 3 path; PROOF-ONLY for the recursion.**

---

### EFF.HE3.s1of2.35  [lemma]  — LEMMA HE3-6 (Galois equivariance of labels)

**CANONICAL STATEMENT:** verbatim, lines 1118–1121.

**FORM:** display (blockquoted bold-headed lemma, inside the `[r1, F3]` discharge block).

> “> **LEMMA HE3-6 [r1] (Galois equivariance of labels).** For
> > g ∈ Gal(K̄₀/K₀) and ρ a root of f with label (λ, r), the root gρ has
> > label (λ, r) — the SAME r ∈ K[Z]. Hence every class S_{λ,r} is
> > Galois-stable, at every f₁.”

**CONDITIONALITY:** **This lemma is the discharge of PE1's finding 6, and its existence is what makes “UNCONDITIONAL” honest at f₁ ≥ 2.** The note is explicit (`.17`): “LEMMA HE3-6 discharging the equivariance gap the old text ASSUMED at f₁ ≥ 2 (F3 — "unconditional" was internally contradicted by that assumption; it no longer is)”. It is **derived at level 1**, with HE6-5 cited as template only: “the level-1 form of LEMMA HE6-5 (frozen at HEAD, cited as the template; the two displays below are re-derived in this note's frame)”.
**It is consumed a second time, out of range**, by R8-2's LEMMA HE3-4U: “LEMMA HE3-6 shows that these conjugate componentwise classes assemble to the original Galois-stable label class” — so the equivariance lemma is what makes the unramified split-sum repair legitimate.
Untouched by `[r2]` and by the A5 wave (verified).

**DERIVATION:** Lines 1123–1140, quoted:

> “*Proof.* Φ′ and the normalizer monomials n(λ) (ℓ = 1) resp. n(u)
> (ℓ ≥ 2) lie in O[x] — their coefficients are Galois-fixed (the needed
> π-exponents are positive: λ > D′h > (e₁−1)h ≥ i₀h, and u = ℓλ > D′h
> likewise) — and v is Galois-invariant (uniqueness of its extension to
> K̄₀). So dv(Φ′(gρ)) = dv(g(Φ′(ρ))) = λ: gρ sits at the same slope; and
> g maps O_{K̄₀} to itself, inducing ḡ ∈ Gal(k̄/F_Q) on residues, so
>
>     η_{gρ} = res((gρ)^{e₁}π^{−h}) = ḡ(η_ρ) ,
>     β_{gρ} = res(Φ′(gρ)^{ℓ}/n(u)(gρ)) = ḡ(β_ρ)   (ℓ = 1: n(λ) read).
>
> ι_ρ is THE F_Q-embedding with η_θ ↦ η_ρ, so ḡ∘ι_ρ is an F_Q-embedding
> with η_θ ↦ ḡ(η_ρ) = η_{gρ}, i.e. ι_{gρ} = ḡ∘ι_ρ; therefore
> ι_{gρ}(r)(β_{gρ}) = ḡ(ι_ρ(r)(β_ρ)) = ḡ(0) = 0, and gρ carries the same
> (λ, r). ∎ — The two semilinear twists cancel BECAUSE the label is
> defined relative to the fixed K-object r through the root-dependent
> embedding; this is §S4's universality-in-η observation composed with
> ρ ↦ gρ, the composition PE1 F6 asked for. At f₁ = 1 it degenerates to
> the old sentence (K = F_Q fixed pointwise).”

*Arithmetic audit (rule 22).*
- **Integrality of the normalizers.** `n(λ) = x^{i₀}π^{a}` with `a = (λ − i₀h)/e₁`; positive iff `λ > i₀h` ✓, and `λ > D′h ≥ e₁h > (e₁−1)h ≥ i₀h` ✓ (since `i₀ ≤ e₁−1` and `f₁ ≥ 1`) ✓ **exactly the displayed chain.** For `ℓ ≥ 2`, `u = ℓλ > λ > D′h` ✓.
- **The two semilinear twists.** `ι_{gρ} = ḡ∘ι_ρ` ✓ (both are F_Q-embeddings sending `η_θ ↦ η_{gρ}`, and such an embedding is unique given the image of the generator ✓). Then `ι_{gρ}(r)(β_{gρ}) = (ḡ∘ι_ρ)(r)(ḡ(β_ρ)) = ḡ(ι_ρ(r)(β_ρ))` ✓ — **because `ḡ` is a field homomorphism, it commutes with polynomial evaluation** ✓ — `= ḡ(0) = 0` ✓.
- **The `f₁ = 1` degeneration.** `K = F_Q` is fixed pointwise by `ḡ` ✓ so both twists are trivial ✓ and the lemma reduces to the old sentence ✓ — **which is exactly why the gap was invisible at f₁ = 1** ✓.
**Every step reproduces; the cancellation mechanism is correct.**

**RESOLUTION TRACE:** statement 1118–1121 · proof 1123–1140 · consumed at 1102–1108 (`.34`'s base step) and 1724–1728 (R8-2, shard 2).

XREF: `HE6_PROOF_2026-08-08.md:LEMMA HE6-5` — count **5** (the template).

**TEETH:** **PROOF-ONLY at f₁ ≥ 2 by the note's own diagnosis** (the gap was invisible at `f₁ = 1`, and the sealed battery is `f₁ = 1` only). Its machine contact is indirect: `he3r1_supp.py` P2/P3's `f₁ ∈ {2,3}` sweeps agree with PARI on every member, which would fail if labels were not Galois-stable. **Disposition: `accepted-with-decorrelation-supplied`** — the additive legs supply the only evidence, and they are consistent.

---

### EFF.HE3.s1of2.36  [theorem]  — §S6.4, the proof of COROLLARY HE3.B and the μ = 2 cross-check

**CANONICAL STATEMENT:** verbatim, lines 1207–1226.

**FORM:** `###`-headed section body: a proof paragraph + a bold-italic-headed cross-check.

> “The induction is the one displayed in §S1: HE3.A at multiplicity μ
> consumes HE3.A only at inner multiplicities μ′ ≤ μ/2, and by
> GENIND.A(IV) no inner composite stage exists unless μ ≥ 4. Hence μ = 2
> and μ = 3 are proved outright by §S6.3's base + stage-α steps, and
> every μ ≥ 4 follows by induction. In particular [GENHN-HE(μ)] holds for
> all μ ≥ 3. ∎
>
> *Cross-check at μ = 2 (no circularity: GENHN.C is not used above).*
> Σ e_sf_s = 2 gives exactly three stage types, and §S6.3 returns
> {(2e₁, f₁)} for (2,1) [one side, ℓ = 2, u odd], {(e₁, 2f₁)} for (1,2)
> [one side, integer slope, residual irreducible quadratic], and
> {(e₁,f₁),(e₁,f₁)} for (1,1)+(1,1) [two sides, or one side with two
> distinct rational residual roots — GENHN.C's 2SIDED / SPLITEQ /
> SPLTAIL]. These are GENHN.C's dictionary verbatim, re-derived from the
> label calculus. At μ = 3 the five types and their σ are displayed in the
> battery docstring; the new one — with no μ = 2 analogue — is
> (1,1)+(1,1)+(1,1), σ = {(e₁,f₁),(e₁,f₁),(e₁,f₁)}: at (e₁,f₁) = (2,1) a
> SEXTIC SPLITTING INTO THREE RAMIFIED QUADRATICS.”

**CONDITIONALITY:**
(a) **“every μ ≥ 4 follows by induction” inherits HE3-BOX-6 branch (ii)** — the induction's base machinery includes LEMMA HE3-4, whose ramified branch is boxed. The corollary's own statement (`.17`) says so; this proof paragraph does not repeat it. Recorded as a reading hazard.
(b) **The non-circularity claim is checkable and holds**: GENHN.C is imported at `.03` “as a CROSS-CHECK only”, and §S3–S6 never cite it ✓ (verified by reading the proof chain).
(c) The cross-check is a genuine **decorrelation**: the μ = 2 dictionary is re-derived from the label calculus and matches GENHN.C's independently-derived dictionary.

**DERIVATION:** The induction is `.17`'s; the cross-check is an enumeration.

*Arithmetic audit (rule 22).*
- **μ = 2's three types**, matched to `.19`'s enumeration ✓ and to GENHN.C's dictionary (`spec/EFF-GENHN-s1of2.md` `.15`): `{(2e₁, f₁)}` ↔ GENHN's stage-RAM ✓; `{(e₁, 2f₁)}` ↔ stage-INERT ✓; `{(e₁,f₁),(e₁,f₁)}` ↔ stage-2SIDED/SPLITEQ/SPLTAIL ✓. **All three match verbatim** ✓ — the cross-check is exact.
- **Degree consistency at μ = 2.** Each type sums to `2D′` ✓ (audited at the GENHN shard).
- **μ = 3's five types.** `Σ e_sf_s = 3`: `{(3,1)}, {(1,3)}, {(1,1),(2,1)}, {(1,1),(1,2)}, {(1,1),(1,1),(1,1)}` ✓ **five** ✓, matching §S9's Q3 table (shard 2) row for row ✓.
- **The headline instance.** At `(e₁,f₁) = (2,1)`, type `(1,1)³` gives `σ = {(2,1),(2,1),(2,1)}` ✓ — three factors each with `e·f = 2`, total degree `6 = D′μ = 2·3` ✓ **a sextic splitting into three ramified quadratics** ✓.
**All enumerations and the cross-check reproduce.**

**RESOLUTION TRACE:** statement 1207–1226 · the induction 349–367 (`.17`) · GENHN.C's dictionary `GENHN_PROOF` 259–273 · the machine confirmation 1420–1432 (shard 2, Q3).

XREF: `GENHN_PROOF_2026-08-08.md:THEOREM GENHN.C` — count **11**.
XREF: `GENIND_PROOF_2026-08-08.md:GENIND.A(IV)` — count **5**.

**TEETH:** **Q3's 947 PARI jobs realize and confirm ALL FIVE μ = 3 types**, including “**25 sextics that split into three ramified quadratics, each PARI-confirmed** — the first machine confirmation of a 3-label stage σ anywhere in this program” (shard 2). **Disposition: executable regression against an independent oracle; the cross-check itself is `foreign-note evidence` consumed as decorrelation.**

---

### EFF.HE3.s1of2.37  [lemma]  — LEMMA HE3-5 (the σ-resolution boundary)

**CANONICAL STATEMENT:** verbatim, lines 1238–1258 (the lemma and its three bullets).

**FORM:** `###`-headed subsection with a preamble paragraph + a blockquoted bold-headed lemma with two clauses and three bullets.

> “> **LEMMA HE3-5.** Work at window N (dv-cap e₁N: a dv-value is
> > lift-stable iff < e₁N, GENHN-3(a)). Consider a side of P(F) with
> > integer dv-slope λ, left endpoint (j₁, m₁) and residual degree
> > d ≥ 2, and a letter s ∈ K^×. Recentering at (λ, s) determines the
> > multiplicity m_s of s as a residual root iff, for every j in the
> > side's span, the recentered value dv(A_j′) is either
> > (i) < e₁N (read exactly), or
> > (ii) ≥ e₁N with e₁N > m₁ − λ(j − j₁), the λ-line height at j — in
> > which case "dv(A_j′) ≥ e₁N" ALREADY certifies "dv(A_j′) > line",
> > i.e. certifies that the pin is LIFTED, which is the only fact the
> > multiplicity count consults.
> > Otherwise the member's σ is UNDECIDED at window N. In particular:
> > * a side spanning the whole polygon (j₁ = 0, m₁ = μλ) is decided as
> >   soon as **e₁N > μλ**;
> > * the ALPHA-type members (residual = (Z − s)^μ, a single root of full
> >   multiplicity) need the DEEPER read of the recentered system, hence
> >   one more window unit than the split types at the same λ — they are
> >   the last species to resolve as N grows;
> > * consequently the σ-undecided mass of a μ-stage row is exactly the
> >   mass of members whose deepest consulted height reaches the cap, an
> >   exact q-power per stratum (measured per row by battery leg HE-BND).”

**CONDITIONALITY:** **The lemma's two clauses stand; its three bullets are REPLACED by the R8-1 dated correction, and the note's introductory “has an exact answer” is re-read.** From 1634–1689 (shard 2):

> “The first displayed criterion of LEMMA HE3-5 decides ONE consultation:
> whether the multiplicity of a residual root at the current node is
> lift-stable. It is not by itself a stopping bound for the complete
> stage-α history. Correct the introductory phrase “has an exact answer”
> to mean the following recursive answer. …
>
> Consequently, replace the three bullets following HE3-5 by:
>
> * for a side spanning the whole current polygon, e₁N > μλ certifies
>   the INITIAL residual multiplicities at that node;
> * this decides the leaf only when those residuals are terminal;
>   a repeated residual root can require arbitrarily many further window
>   units, according to the heights reached by its descendants;
> * the σ-undecided mass is therefore obtained by stratifying by complete
>   read histories and their deepest consulted heights. No single
>   “one more window unit” law, nor one unstratified exact q-power,
>   follows from HE3-5.”

`SUPERSESSION KIND: replacement` (the three bullets). **CHAIN: the frozen bullets → R8-1's replacement. TERMINAL: R8-1, awaiting sol discharge-confirmation.**
**The refutation is by explicit counterexample** (1670–1684, shard 2): over `O = ℤ₅` with `e₁ = 1, f₁ = 2, D′ = 2, h = 1, λ = 3`, a height-3 carrier `C`, and `M > 9`, put `f = (Φ′ − C)³ + 5^M`; the first consultation is ALPHA, and after recentering `f = Φ″³ + 5^M` reaches height `M` — “Certifying that child can require a cap beyond M, arbitrarily far past the initial threshold μλ = 9. **Thus the former “one more window unit” sentence is false.**”
**And the machine table is re-scoped**: “§S9's HE-BND table is evidence for the selected aligned rows only … it does not verify a general two-step boundary law.”

**DERIVATION:** Lines 1260–1265, quoted:

> “*Proof.* Immediate from LEMMA HE3-2(b) (the multiplicity is read as the
> number of pins lifted strictly above the λ-line) plus GENHN-3(a) (a
> computed dv-value is lift-stable iff < e₁N, and a value at or above the
> cap is only known to be ≥ e₁N). Clause (ii) is the observation that a
> one-sided bound suffices for a strict inequality against a KNOWN
> threshold. ∎”

*Arithmetic audit (rule 22).*
- **Clause (ii).** The λ-line height at `j` is `m₁ − λ(j − j₁)` ✓ (a line of slope `−λ` through `(j₁, m₁)` in the `(j, dv)` plane ✓). If `dv(A_j′) ≥ e₁N` and `e₁N > line`, then `dv(A_j′) > line` ✓ — a one-sided bound suffices ✓.
- **Bullet 1.** A whole-polygon side has `j₁ = 0`, `m₁ = μλ` ✓ (height at abscissa 0 of a slope-λ side spanning `0..μ`) ✓; the maximum line height is `μλ` ✓, so `e₁N > μλ` certifies (ii) at every `j` ✓.
- **R8-1's counterexample, recomputed.** `Φ′` at `(e₁,f₁,h) = (1,2,1)`, `D′ = 2`; `f = (Φ′ − C)³ + 5^M` with `dv(C) = 3 = λ`. Expanding: `f = Φ′³ − 3CΦ′² + 3C²Φ′ − C³ + 5^M` ✓ — pins `A₂ = −3C` (`dv = 3`), `A₁ = 3C²` (`dv = 6`), `A₀ = −C³ + 5^M` (`dv = 9` for `M > 9`, since `dv(C³) = 9 < dv(5^M) = M` ✓). Line through `(3,0)` of slope 3: heights `0, 3, 6, 9` at `j = 3,2,1,0` ✓ — **all three pins ON the slope-3 line** ✓, so `λ = 3` with `L_λ = 3` ✓ and residual `(Z − s)³` ✓ (the coefficients are the binomial pattern of a cube ✓). `μλ = 3·3 = 9` ✓ **matches the displayed threshold.** After recentering `Φ″ = Φ′ − C`: `f = Φ″³ + 5^M` ✓ **exactly** ✓, whose polygon has `A₀ = 5^M` at height `M` ✓ **unbounded** ✓. **The counterexample is exact and it does refute the “one more window unit” bullet.**
**Every step reproduces, including the A5 verification note's own hand-check (1826–1830, shard 2), which this compiler independently confirms.**

**RESOLUTION TRACE:** statement 1238–1258 · proof 1260–1265 · preamble 1231–1236 · correction 1634–1689 (shard 2, R8-1).

XREF: `GENHN_PROOF_2026-08-08.md:GENHN-3(a)` — count **11**.

**TEETH:** **HE-T-CAP — “added mid-run, the strongest tooth”** (shard 2, Q5): “the earlier reader variant that dropped out-of-window recentered digits disagrees with the sound reader on 17 (p = 5) and 43 (p = 7) members — **the soundness bug of LEMMA HE3-5 is real and is caught**.” **Disposition: planted mutant, fired, and the mutant is the note's own earlier reader.** **HE-BND's two-step table is RE-SCOPED by R8-1** to “evidence for the selected aligned rows only” — `stale self-description` on the general law.

---

### EFF.HE3.s1of2.38  [scope-record]  — the Interpretation (the honest reading of the undecided mass)

**CANONICAL STATEMENT:** verbatim, lines 1267–1274.

**FORM:** bold-headed paragraph closing §S6.5.

> “**Interpretation (the honest reading of the charge's question "what
> exact q-power is the σ-undecided mass").** The undecided mass is NOT a
> defect of THEOREM HE3.A: it is the window's own resolution, and it
> composes exactly as GENHN-BOX-4/S11.F predicted for embedded genres
> (there the loss is the sibling Hensel precision; here, at a full-side
> genre, the loss is the cap on the recentered digits). The theorem's
> hypothesis "DECIDED leaf" is precisely LEMMA HE3-5's condition, so the
> theorem and the boundary are complementary, not competing.”

**CONDITIONALITY:** **The phrase “what exact q-power” is answered NEGATIVELY by R8-1**: “No single “one more window unit” law, **nor one unstratified exact q-power**, follows from HE3-5.” So the Interpretation's framing — that there is an exact q-power per stratum — survives only in the *stratified* reading R8-1 supplies (“stratifying by complete read histories and their deepest consulted heights”). `SUPERSESSION KIND: scope-pin`.
**The claim “The theorem's hypothesis "DECIDED leaf" is precisely LEMMA HE3-5's condition” is true only under R8-1's RECURSIVE reading of HE3-5** — under the original one-node reading, DEFINITION 2's condition (b) (“every event along the history is lift-stable”) is strictly stronger than HE3-5's single-consultation criterion. R8-1's recursive criterion is what makes the two coincide. **HE3-BOX-5 item (4) (shard 2) names this as an open check**: “whether "decided leaf" as defined in DEFINITION 2 coincides exactly with LEMMA HE3-5's window condition on every row (the battery measures both)”. See OPEN-CALL 4.

**DERIVATION:** Interpretive; the composition claim is inherited from GENHN-BOX-4/S11.F.

**RESOLUTION TRACE:** statement 1267–1274 · correction 1634–1689 (R8-1) · the open check 1377–1379 (shard 2, HE3-BOX-5 item 4).

XREF: `GENHN_PROOF_2026-08-08.md:GENHN-BOX-4` — count **3** · `S11.F` — count **10**.

**TEETH:** **HE-BND measures both sides** — the decided/undecided profile vs window, scored at §S9 with the predicted two-step (shard 2). **Disposition: measurement, RE-SCOPED by R8-1 to the aligned rows only.**

---

## 3. Consumption tables

### 3.1 Verified import/XREF designations

`[TABLE — compiler ledger]` Every row's count is `grep -cF '<designation>' <file>` run at HEAD from `lean/notes/openmath/`. **26 distinct designations, all count ≥ 1.**

| # | Target : designation | Count | Role in this shard |
|---|---|---|---|
| 1 | `GENHN_PROOF_2026-08-08.md:THEOREM GENHN.CLASS` | 7 | The genre datum, consumed as the definition layer |
| 2 | `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-1` | 4 | The Φ′-development and (pre-correction) the node |
| 3 | `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-2` | 2 | THE SLOT LEMMA — at roots θ only; the ξ-form is HE6-0″ |
| 4 | `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-3` | 3 | The window ledger; `GENHN-3(a)` (11) is the lift-stability clause |
| 5 | `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-4` | 3 | **Declared NOT consumed** — the fence at `.04` |
| 6 | `GENHN_PROOF_2026-08-08.md:THEOREM GENHN.C` | 11 | Consumed as a CROSS-CHECK only; re-derived at `.36` |
| 7 | `GENHN_PROOF_2026-08-08.md:GENHN.A(v)` | 6 | The (μ,K)-cluster read DEFINITION 2 instantiates |
| 8 | `GENHN_PROOF_2026-08-08.md:S11.F` | 10 | The extraction-certified perimeter, the machine-side gate |
| 9 | `GENHN_PROOF_2026-08-08.md:GENHN-BOX-4` | 3 | The same perimeter as a box; HE3-BOX-2 inherits it |
| 10 | `GENHN_PROOF_2026-08-08.md:GENHN-BOX-2` | 5 | The W-9 weld face **declared NOT inherited** |
| 11 | `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-T(b)` | 11 | Cited at `.34`'s stage-CS step — **the lemma GENHN later REFUTED** (source defect 6) |
| 12 | `GENHN_PROOF_2026-08-08.md:THEOREM GENHN.B` | 7 | The clause list HE3.C discharges into |
| 13 | `GENHN_PROOF_2026-08-08.md:GENHN-3(a)` | 11 | Lift-stability iff dv < e₁N |
| 14 | `GENHN_PROOF_2026-08-08.md:ERRATUM 2026-08-08` | 1 | GENHN's `[r1]` node erratum, consumed at `.11`(iii) |
| 15 | `GENHN_PROOF_2026-08-08.md:ERRATUM E3` | 4 | The same carrier correction one level up (`.10`) |
| 16 | `GENHN_PROOF_2026-08-08.md:[GENHN-HE` | 19 | The box this note claims to close |
| 17 | `GENHN_PROOF_2026-08-08.md:[GENHN-TOW-1]` | 19 | The tower box HE3.C's conditionality phrase under-describes |
| 18 | `GENIND_PROOF_2026-08-08.md:GENIND.A(I)` | 3 | The species partition |
| 19 | `GENIND_PROOF_2026-08-08.md:GENIND.A(IV)` | 5 | **The descent engine** — abscissa length ≥ 4 ⟹ μ ≥ 4 |
| 20 | `GENIND_PROOF_2026-08-08.md:LEMMA GENIND-3` | 6 | Sibling fibration for embedded genres; also consumed by R8-2 |
| 21 | `GENIND_PROOF_2026-08-08.md:GENIND-H(n)` | 7 | The package HE3.C reports on |
| 22 | `HE6_PROOF_2026-08-08.md:HE6-0″` | 7 | **The single most load-bearing citation** — the ξ-form slot lemma |
| 23 | `HE6_PROOF_2026-08-08.md:LEMMA HE6-1L` | 4 | The mechanism HE3-1L back-propagates |
| 24 | `HE6_PROOF_2026-08-08.md:LEMMA HE6-3` | 12 | The (SEP)-free slope counts; independent cover for N1 |
| 25 | `HE6_PROOF_2026-08-08.md:LEMMA HE6-5` | 5 | The template for HE3-6 |
| 26 | `HE6_PROOF_2026-08-08.md:HE6-0′` | 5 | The ℓ ≥ 2 residue repair form |
| 27 | `HE6_PROOF_2026-08-08.md:HE6-2″` | 2 | HE6's own re-proof of HE3-0(iii)'s ℓ ≥ 2 read (not consumed) |
| 28 | `HE6_PROOF_2026-08-08.md:HE3-0` | 9 | Reverse edge: HE6 consumes HE3-0 |
| 29 | `HE6_PROOF_2026-08-08.md:DEFINITION 1` | 1 | Reverse edge: the consumer pin |
| 30 | `HE6_PROOF_2026-08-08.md:HE3-2(b)` | 1 | Reverse edge: the above-λ clause pin |
| 31 | `HE6_PROOF_2026-08-08.md:HE3.B` | 2 | Reverse edge: the descent |
| 32 | `HE6_PROOF_2026-08-08.md:HE3-1` | 1 | Reverse edge: the resultant identity |
| 33 | `HE7_PROOF_2026-08-08.md:HE3-3` | 2 | Reverse edge: the (★) convex duality |
| 34 | `GRTJC_PROOF_2026-08-08.md:JC-LOAD` | 31 | Declared NOT consumed |
| 35 | `SIGMALAW_PROOF_2026-08-08.md:(EC-q)` | 26 | Declared NOT consumed |
| 36 | `DULEMMA_PROOF_2026-08-08.md:DULEMMA` | 1 | Declared NOT consumed |
| 37 | `CODEX_HE3PE1_2026-08-08.md:HE3` | 15 | The uncounted Codex pass; source of the (SEP) counterexample |
| 38 | `spec/HYPOTHESIS_LEDGER.md:HYP.81` | 10 | The ledger row for `[GENHN-HE(μ≥3)]` |

**Designations counted but NOT emitted as XREFs (3 — recorded as source defects in §8):**
- **`ϖ-CONVENTION`** — count **0** in `HE6_PROOF_2026-08-08.md`; the target's heading is `**CONVENTION (ϖ-normalizers: twist-free).**` at line 104, verified. Carried descriptively.
- **`GENHN §S4`, `GENH4 S5`-style section pointers** — §-anchor citations, not designations; carried descriptively.
- **`HE6-3(a)`** — the sub-clause cited at `.11`(iii); the parent `LEMMA HE6-3` (12) is emitted instead.

**Artifacts verified to EXIST on disk:** `verification/openmath/he3_checks.py`, `he3_checks_output.txt`, `he3_checks_results.json`, `he3r1_supp.py`, `he3r1_supp_output.txt`, `he3r1_supp_results.json`, `he3_pe1fresh_ab.py`, `he3_pe1fresh_ab_output.txt`, `he3_pe1fresh_c.py`, `he3_pe1fresh_c_output.txt`, `he3_pe2fresh.py`, `he3_pe3fresh.py`, `he3_pe3fresh_output.txt`, `he3_pe3fresh_results.json`, `he3_pe4fresh.py`, `he3_pe4fresh_output.txt`, `he3_pe4fresh_results.json` — **17/17 present.** Reports: `HE3_passPE1_report.md`, `HE3_passPE2_report.md`, `HE3_passPE3_report.md`, `CODEX_HE3PE1_2026-08-08.md` — **4/4 present.** Logs: `runs/residues/R8_he3_output.log`, `runs/cert/A5_he3_output.log` — **2/2 present.** Corpus records: `runs/qgen/WELD_FACE_AUDIT.md`, `spec/HYPOTHESIS_LEDGER.md` — **2/2 present.**

**Commit pins verified with `git cat-file -t` (all → `commit`): 5/5** — `7950ee4` (PE1), `6d0ff09` (PE2), `7a95449` (the consumers' HE3 pin), `f2a7164` (HE3's own HEAD pin at composition), `4682bcf` (GENIND).

**Hash pinning quality (rule 23).** Two full md5s are given for `he3r1_supp.py` (`9cd132a8ce174f5703542757675f7960` → `93681e8d47d447dcbfd46db0ddfe0c55`) plus its output (`65ed06e49f4c54abf1b143513633f143`) — **3 PINNED**, and the docstring-only change is certified by a byte-identical stdout. **The §S8 battery's artifact hashes are NOT in the note** — §S9 says “hashes in the commit message”, i.e. **UNPINNED from the note's own text**. Recorded as source defect 7.

### 3.2 Reverse consumer edges: mathematical supply versus append protocol

`[TABLE — compiler ledger]`

| Consumer | Verified designation | Shard-1 supply | Mathematical status | Append/consumption-protocol status |
|---|---|---|---|---|
| HE6 (frozen @ HE3 7a95449) | `HE3-0` (9), `DEFINITION 1` (1), `HE3-2(b)` (1), `HE3.B` (2), `HE3-1` (1) | `.13`, `.15`, `.25`, `.20`, `.27`, `.31`, `.17` | HE3's own trace verdicts SAFE; three displays byte-frozen for exactly this reason (F3) | **Not landed by HE3.** The trace is computed here and appended nowhere |
| HE7 (frozen @ HE3 7a95449) | `HE3-3` (2) | `.13`, `.15`, `.31` | SAFE — DEF 1/2 and (★) byte-unchanged | Not landed. **HE7 also consumes `HE3-BOX-6` (count 12 per `spec/EFF-HE7-s1of3.md` §3.1), which HE3's trace does not list** (source defect 1) |
| GENHN (accepted, at HEAD) | `HE3-0` cited in its `[r1]` node erratum | `.25` | Reverse direction: GENHN consumes HE3-0; HE3's corrected node MATCHES GENHN's erratum ✓ verified | **Landed on GENHN by GENHN**, in its own `[r1]` erratum — not by HE3 |
| GENHN (the box) | `[GENHN-HE` (19) | `.09`, `.17`, `.18` | HE3 CLAIMS the discharge at μ ≤ 3 unconditionally | **NOT landed.** GENHN's §S9.2 still calls it “THE one load-bearing open lemma” (OPEN-CALL 2) |
| GENIND (accepted) | — | — | “no consumption site of HE3 found” ✓ verified | N/A |
| `spec/HYPOTHESIS_LEDGER.md` | `HYP.81` (10) | `.09` | The ledger indexes `[GENHN-HE(μ≥3)]` as a live obligation | Ledger-side, done outside HE3 |

**The last column is not an inference.** HE3's protocol is *report, don't append*: §S0′'s CONSUMER TRACE computes four verdicts and lands none. **Zero dated consumption appends are claimed landed on any consumer by this note, and none is invented here.** In the reverse direction HE3 received four inbound streams (header predicate C), all landing in this range.

---

## 4. NON-IMPORTS

`[TABLE — compiler ledger]` The note's explicit negative-import and non-claim fences homed in lines 1–1275.

| Fence | Explicit material NOT imported, NOT proved, or NOT claimed | Unit |
|---|---|---|
| GENHN-4 / the W-9 weld face | “**GENHN.A(iv)/LEMMA GENHN-4 is NOT consumed**, hence **the W-9 graded weld face (GENHN-BOX-2) is NOT inherited**” | `.04` |
| Montes/GMN order-≥2 | “named in GENHN's box as the "faithful-cite target" — is **not** cited” | `.04` |
| SIGMALAW / JC-LOAD / DULEMMA | “not consumed” | `.04` |
| Graded frame / digit-space bijection | “**No graded frame and no digit-space bijection is used: (a)–(c) are statements about valuations and residues only.**” | `.27` |
| GENHN-2 at non-roots | `[r1, F4]`: GENHN-2 “is stated at roots θ of Φ′ only …; the paste above overconsumed it” — the ξ-form is HE6-0″, not GENHN-2 | `.03`, `.25` |
| GENHN.C as input | “consumed as a CROSS-CHECK only: §S6 re-derives it as the μ = 2 case of HE3.A, **so no circularity**” | `.03`, `.36` |
| The node, in the Ψ-comparison | “the lemmas cited consume only dv(Φ″ − Φ′) > D′h and the locus, **never this node** — no circularity” | `.11` |
| The letter-starved corner and μ ≥ 4 in the node derivation | “are NOT closed by this display; there the node is CONSUMED from GENHN's [r1] ERRATUM” | `.11`(iii) |
| (SEP) at general μ | “For general μ, (SEP) is a real hypothesis, and lifting it needs the same enlarged test family as HE3-BOX-6” | `.29` |
| Base change at μ ≤ 3 | “μ ≤ 3 IS BASE-CHANGE-FREE; the two base-change reductions below are μ ≥ 4-only and are BOXED” | `.33` |
| Both base-change branches (as displayed) | “**Both branches below are therefore to be read as BOXED (HE3-BOX-6), not proved.**” — later narrowed to (ii) alone by R8-2 | `.33` |
| Exact summand valuations in the recentering | `[REPAIR, PE1 finding 4]`: “Only the INEQUALITY in (a) survives summand-wise” | `.27` |
| The ℓ ≥ 2 residue read at μ ≤ 3 | “no μ ≤ 3 conclusion consults this read” | `.25` |
| “UNCONDITIONAL” ≠ graded | “It does NOT upgrade the grade: the note is at attempt 0/2 and every consequence carries HE3-BOX-1's supplier-stack conditionality.” | `.17` |
| A composer-context pass | “The earlier Codex pass adjudicated in the composer's own context … **does not count toward the grade**” | `.02` |
| The naive R_λ read | “What is NOT in the class is the naive per-slot read … the naive assembly can have a DIFFERENT factorization type” | `.14`, `.24` |

---

## 5. Teeth inverse table

`[TABLE — compiler ledger]` Battery row → guarded unit(s) → disposition.

| Battery row / tooth | Guarded unit(s) | Disposition |
|---|---|---|
| **HE-NORM** (LEMMA HE3-1 at the entry key on EVERY member; 72,134 entry-key resultant identities, exact Bareiss/Sylvester) | `.20`, `.11`(i) | Executable regression, exhaustive on the enumerated rows; **“The engine of the proof is machine-real.”** |
| **HE-PSI** (the identity at EVERY test key (κ,s) + HE3-1′'s inequality + the convex duality (★); 43,528 checks, 0 violations) | `.22`, `.29`, `.31` | Executable regression |
| **HE-SIG** (PARI factorpadic-200 + idealprimedec vs the HE3.A dictionary; 947 jobs, 0 bad, all five μ = 3 types) | `.16`, `.25`, `.34`, `.36` | Executable regression against an independent oracle |
| **HE-BND** (the decided/undecided profile vs window; 3,744 boundary reads) | `.15`, `.37`, `.38` | Measurement; **RE-SCOPED by R8-1** to the aligned rows only — `stale self-description` on the general two-step law |
| **HE-T-UNDET** (the μ = 2 method's 10 spurious solutions at a 3-label member) | `.19` | Planted mutant / measurement; **fired — “the mechanism certificate”** |
| **HE-T-SIG** (6/6 flipped dictionaries caught by PARI on each of two rows) | `.16`, `.36` | Planted mutant; fired |
| **HE-T-CAP** (the out-of-window-dropping reader disagrees on 17 (p=5) / 43 (p=7) members) | `.37` | Planted mutant; **fired — added mid-run, “the strongest tooth”**; the mutant is the note's own earlier reader |
| **HE-T-NODE** | — | **MIS-SPECIFIED**: “does not test what its name claims … read as a diagnostic, not a tooth” (HE3-BOX-4b, shard 2) — `stale self-description` |
| **HE-T-PSI, HE-T-CERT** | — | **OWED** (never wired) — `disclosed non-repair` |
| **Q4, the census tie** (the fresh reader reproduces GENHN's committed E3 rows exactly, 72,134 members) | `.03`, `.11` | **Foreign-note decorrelation** — “Two independently written readers agreeing to the digit on 72,134 members” |
| **`he3r1_supp.py` P1** (the repaired peel at PE1's counter-instance; m_s = 1 at all 3 roots incl. both K∖F₃ letters, 0 at the other 5; PARI on two variants) | `.21`, `.32`, `.33` | Executable regression, exhaustive over the letter set; **excludes by measurement the splits PE1 showed the old text could not** |
| **`he3r1_supp.py` P2** (f₁ = 2 sweep, 8/8 members incl. an ℓ = 2 member and the consecutive-triple geography) | `.11`, `.25`, `.30`, `.35` | Executable regression |
| **`he3r1_supp.py` P2-N1** (both branches of the N1 supplement) | `.30` | Executable regression **at the WRONG geography** — `signed vacuity disclosure` at `[r2]` F-5; cured by PE2's FR-D |
| **`he3r1_supp.py` P3** (f₁ = 3 sweep, 4/4 + the 26-letter peel over F₂₇^×) | `.21`, `.35` | Executable regression, exhaustive over the letter set |
| **`he3r1_supp.py` P4** (LEMMA HE3-1L's exact set) | `.21` | **Quasi-tautological, DISCLOSED** at `[r2]` F-4 — `signed vacuity disclosure`; decorrelated substitute is PE2's FR-C (`nfeltval`/`nfmodpr`) |
| **`he3_pe2fresh.py`** (GREEN, 7/7 PARI members at the first e₁ ≥ 2 ∧ f₁ ≥ 2 geography; member `ma` the twist adjudicator; FR-C, FR-D) | `.07`, `.14`, `.24`, `.30` | Executable regression on a decorrelated instrument; **the twist mutant fired** |
| **PE3's fresh route** (GREEN, 0 violations, three disjoint geographies: the (2,1)/(3,1) starved corners, a μ = 3 coherent family at (e₁,f₁) = (3,1), and non-prime Q = 4 over F₄[[t]]) | `.12`, `.14` | Executable regression on a decorrelated instrument; **the coherent-vs-naive flip adjudicated at each of the three, siding with coherent each time** |

**PROOF-ONLY rows (rule 16), with the note's own coverage-hole sentence:**

| Unit | Coverage hole, in the note's words |
|---|---|
| `.10` (the L/O_L carrier) | The battery enumerates in stage coordinates and never consults R's ring structure; the affected site is the μ ≥ 4 stage-CS step — HE3-BOX-3: “NOT exercised by machine: … μ ≥ 4” |
| `.11` (the corrected node) | “The §S8 battery enumerates at f₁ = 1 only, where the two nodes coincide” |
| `.20` (the band) | “At f₁ = 1, S = D′h and the band S < dv ≤ D′h is empty — the sealed battery's geography is unaffected” |
| `.21` (HE3-1L's letter reach) | “At f₁ = 1 the set is F_Q^× = K^× at every κ ≥ i₀h, which is why the defect was invisible to the sealed battery” |
| `.25` (the ℓ ≥ 2 read) | “At μ ≤ 3 … no μ ≤ 3 conclusion consults this read; at μ ≥ 4 it is load-bearing, inside HE3-BOX-6's territory” |
| `.29` ((SEP) at general μ) | Needs `μ ≥ 9` to fail; HE3-BOX-3: “μ ≥ 4 … NOT exercised by machine” |
| `.33` (branch (ii)) | HE3-BOX-3: “μ ≥ 4 (where LEMMA HE3-4's ramified base-change branch … first bite)” |
| `.34` (the stage-CS step) | Same; unreachable at μ ≤ 3 by GENIND.A(IV) |
| `.35` (HE3-6 at f₁ ≥ 2) | “At f₁ = 1 it degenerates to the old sentence” — the gap was invisible at the battery's geography |

**AUDIT-disposition rows (rule 27) — findings no battery row could have produced:**

| Finding | Unit | Class |
|---|---|---|
| The peel letters reach only `F_Q ⊊ K` at f₁ ≥ 2 (PE1 F1, CRITICAL) | `.21` | in-house hostile pass (Fable PE1) |
| The `S = e₁h` thresholds are false in the band (PE1 F2, CRITICAL) | `.11`, `.20` | in-house hostile pass, with PARI-exact counter-instances |
| Two mutually-cancelling false displays (PE1 F5) | `.27`, `.32` | in-house hostile pass — **invisible to the instrument by construction** |
| GENHN-2 over-consumed at ξ ≠ roots of Φ′ (PE1 F4) | `.03`, `.25` | in-house hostile pass (a citation-scope defect) |
| Integer sampling does not always suffice (PE1 F3) | `.29` | decorrelated-model audit (Codex counterexample) |
| The Galois-semilinearity gap was ASSUMED (PE1 F6) | `.34`, `.35` | in-house hostile pass |
| The N1 consecutive-triple gap | `.30` | **self-found in a repair round** |
| The R_λ construction is unpinned; the twist-invariance sentence is FALSE (PE2 F-1) | `.14`, `.23`, `.24` | decorrelated-model audit + machine adjudication |
| The node derivation assumed attainment (PE2 F-2) | `.11` | in-house hostile pass |
| The starved-corner list matches neither reading (PE3 M-1) | `.12` | arithmetic recount |
| HE3-5 is recursive, not a one-unit bound (R8-1) | `.37`, `.38` | decorrelated-model audit, with a constructed counterexample |
| §S6.2 contradicts §S1 on how many branches are boxed (R8-2) | `.33`, `.17` | decorrelated-model audit — an internal contradiction |
| “n ≥ D′μ ≥ 8” consumes an undisplayed `D′ ≥ 2` (R8-3) | `.01`, `.17` | decorrelated-model audit |
| `S_r`'s display is still ill-defined at ℓ ≥ 2 (R8-4) | `.32` | decorrelated-model audit |
| HE3-0's proof sentence still cites GENHN-2 (R8-5) | `.25` | decorrelated-model audit (a provenance defect the r1 round missed) |

**Both-direction audit.** Every row above guards at least one in-range unit. Every in-range unit whose `TEETH` field names a battery row appears in some row. Units with **`TEETH: NONE`** — `.01`, `.03`, `.04`, `.06`, `.08`, `.09`, `.13`, `.18` — are declarations, fences, status records, definitions or programme claims and are outside the orphan count. Units flagged **Indirect** — `.25`, `.26`, `.28` — are guarded compositely through HE-SIG. **Zero battery-row orphans; zero toothed-unit orphans; nine signed PROOF-ONLY units; fifteen AUDIT-class findings.**

---

## 6. BOUNDARY SELF-AUDIT

HE3 is prose-with-blockquotes like GENHN, but with one genre feature no other note in this sweep has at the same density: **repairs are applied IN PLACE with strike-through**, so a single displayed sentence routinely contains refuted text and its replacement byte-adjacent. That, not the blockquote convention, is the shard's boundary problem.

### 6.0 The rule applied

> **A unit is the smallest span carrying one complete claim together with its proof obligations.**

Four tests, in order: (1) does the span have a proof obligation of its own? (2) is it cited BY DESIGNATION from elsewhere? (3) does it have its OWN supersession history? (4) does it have its own conditionality or consumer set?

**A fifth test was needed for this note and is recorded as format evidence (§6.3): (5) is the span BYTE-FROZEN under a consumer pin?** A frozen display and its adjacent repair must be separate units, because merging them would represent as one text something the note deliberately keeps as two.

### 6.1 Boundaries drawn, with the arguable ones recorded both ways

**1. Struck text is never a separate unit; it is quoted inside its replacement's unit.** *Candidate A:* emit refuted text as its own `[changes-record]` so the DAG can see what was withdrawn. *Candidate B (chosen):* quote it verbatim inside the CANONICAL STATEMENT with the strike markers intact, and name the current reading in CONDITIONALITY. **Reason:** the note's strike-through is *typographic*, not structural — the refuted and current readings share one sentence, one line number, and one consumer. Splitting would require inventing line boundaries the source does not have. *Cost:* CANONICAL STATEMENTs are longer and contain false text; mitigated by the header's explicit reading rule.

**2. DEFINITION 1 (`.13`) and its `[r2]` construction pin (`.14`) are SEPARATE units.** **Forced by test 5.** DEFINITION 1 is byte-frozen because HE6/HE7 pin it; the pin is landed adjacent precisely so the definition is not edited. Merging them would erase the note's own compliance with (F3). *Not arguable* once the freeze predicate is read.

**3. The `[r2]` twist Remark (`.23`) and THE WITNESS (`.24`) are separate.** Test 1 and 4: the Remark states a coboundary *theorem* about the wraps with two proof obligations (the two bullets); the witness is a *run-record* with PARI adjudication. *Candidate A:* one §S3-Remark unit. *Rejected* — rule 19's `run-record`/statement split applies, and the witness is cited independently from `.14`.

**4. §S1's node derivation (`.11`) kept WHOLE, including parts (i), (ii), (iii) and the LOCUS SCOPING clause.** **The shard's clearest merge decision.** *Candidate A:* four units — the j = 0 pin, the Ψ-comparison, the honest scope, the locus scoping. *Candidate B (chosen):* one. **Reason:** the four parts prove ONE claim (the corrected node) and share one proof obligation; part (iii) is the scope of parts (i)–(ii), and the LOCUS SCOPING clause is the witness that the *old* node was wrong. Splitting would leave (ii) with a CONDITIONALITY field that cannot state its own reach. *Exception:* the starved-corner parenthetical **is** split out as `.12`, because a dated append corrects it by name — test 3 overrides.

**5. `.12` (the starved-corner parenthetical) as its own unit.** **Arguable.** *Candidate A:* a parenthetical inside `.11`(iii). *Candidate B (chosen):* a unit — the post-PE3 M-1 append names it, quotes it, and corrects it under two readings, and the frozen text stands. A rider with a named target needs an addressable target (test 3). *Cost:* a five-line unit.

**6. The three repair-record tables (`.05`, `.06`, `.07`) as units.** Template rule 5 (tables are units) plus test 1: each makes falsifiable claims (finding counts, consumer verdicts) that this shard independently audited. `.06` in particular is a **cross-note claim in four parts**, each checkable — and checking it surfaced source defect 1.

**7. LEMMA HE3-1 (`.20`), HE3-1L (`.21`), HE3-1′ (`.22`) as three units.** Test 2 and 3: all three are cited by designation from elsewhere (HE3-1 by HE6; HE3-1L twelve times within the note; HE3-1′ from `.11` and `.29`), and each carries a different repair history. *Not arguable.*

**8. LEMMA HE3-3 (`.29`), the N1 supplement (`.30`), and the sampling Remark (`.31`) as three units.** Test 3: the lemma acquires (SEP); the supplement closes a sub-case (SEP)'s discharge leaves open; the Remark's recipe is separately corrected AND homes the byte-frozen (★). **`.31` is the odd one** — it bundles a corrected Remark with a frozen display. *Chosen* because (★) is cited by designation from `.11` and from both frozen consumers, so it must be addressable, and it sits physically inside HE3-3's proof.

**9. LEMMA HE3-4 (`.32`) split from the μ ≤ 3 scope block and the boxed reductions (`.33`).** Test 3 and 4: `.32`'s *display* is replaced by R8-4; `.33`'s *verdict* (“BOTH … BOXED”) is superseded by R8-2. Two different appends, two different targets. *Candidate A:* one §S6.2 unit. *Rejected* — one CONDITIONALITY field would have to carry both chains and could not say which append edits which sentence.

**10. §S6.3's proof (`.34`) emitted as a unit, with LEMMA HE3-6 (`.35`) split out.** Proofs are normally not units (rule 1). **`.34` is an exception on test 3:** three of its four steps carry their own in-place corrections (`[r1, F5]`, `[r1, F7]`) and its stage-CS step cites a lemma GENHN later refuted. `.35` splits out on test 2 — HE3-6 is cited by designation from `.34` and, out of range, from R8-2. *Cost:* THEOREM HE3.A's DERIVATION field points at `.34` rather than containing it.

**11. LEMMA HE3-5 (`.37`) and its Interpretation (`.38`) separate.** Test 3: R8-1 replaces the lemma's three bullets AND re-reads the Interpretation's framing, but by different mechanisms (replacement vs scope-pin). Also test 4: the Interpretation makes a claim about DEFINITION 2 that HE3-BOX-5 lists as an open check.

**12. `.09` (the absorption-target status) is a COMPILER-ASSEMBLED unit with no single source span.** **The most arguable inclusion in the shard.** *Candidate A:* not a unit — no source sentence says it. *Candidate B (chosen):* a unit — template rule 10 requires cross-note status claims to be verified against the target's full append chain, and the *result* of that verification (HE3 claims, GENHN records open) exists nowhere in either note. Without it a chapter cut would read the title as a landed discharge. **Honest cost: it is the one unit in this shard whose CANONICAL STATEMENT is `[ASSEMBLED]` from two spans plus an external verification.** If the cross-read judges compiler-assembled status units out of scope, this is the unit to cut — but the OPEN-CALL must then carry its content.

### 6.2 Merges deliberately NOT made, and two conflations blocked

- **The (SEP) sub-cases (a)/(b)/(c) stay inside `.29`**: they are one discharge argument, and only sub-case (c) has a separate closure (`.30`), which IS split.
- **The two boxed reductions (i)/(ii) stay inside `.33`**: R8-2 addresses them jointly (“the assertion … that BOTH … remain boxed is superseded for branch (i)”), so one unit can carry the chain.
- **(★) stays inside `.31`** rather than becoming its own unit: it is physically inside HE3-3's proof and is always cited as “the convex duality (★) of HE3-3 step 1” — parented in every occurrence, including by both frozen consumers.
- **BLOCKED CONFLATION 1 — “UNCONDITIONAL” vs “accepted”.** `.17` defines the word (“no assumed hypothesis inside this note's mathematics at μ ≤ 3”) and immediately denies the grade reading. `.02` and `.09` carry the grade (1/2, not accepted). A chapter cut that reports the title's “UNCONDITIONAL” without `.17`'s definition and `.09`'s cross-note status would be materially misleading.
- **BLOCKED CONFLATION 2 — the two “decided” conditions.** DEFINITION 2's condition (`.15`) and LEMMA HE3-5's window criterion (`.37`) are claimed identical by `.38`, listed as an open check by HE3-BOX-5, and made identical only under R8-1's recursive reading. Three units keep them apart.

### 6.3 Format notes (v3 rules exercised, and two gaps)

Rules 11 (FORM on every unit), 12 (three-slot trace), 14 (double-emission: the three source tables at `.05`, `.06`, `.07` are already Markdown and are emitted once as `[TABLE]`; the ASCII displays inside `.11`, `.13`, `.14`, `.20`, `.21`, `.22`, `.25`, `.27`, `.29`, `.31`, `.32`, `.37` are quoted verbatim inside their statements), 15 (NEAR-MISS ×1, `ϖ-CONVENTION`), 16 (PROOF-ONLY ×9), 17 (predicate C, four streams), 18 (**seven of the eight kinds used** — replacement, license, wording-rider, provenance-rider, scope-pin, counter re-reading, as-of scoping; *inventory completion* appears once at `.33`, so all eight), 19 (`run-record` at `.24`), 20 (all four disclosure labels), 21 (**three freeze predicates, one of them unique to this note**), 22 (arithmetic audits on twenty displays; **all reproduced**), 23 (5 commits verified, 25 artifacts verified, 3 full md5s, and the §S8 battery hashes marked UNPINNED-from-the-note), 25 (CHAIN with TERMINAL ×8), 26 (STALE-SELF-DESCRIPTION ×4: `.01`, `.02`, `.17`, `.18`), 27 (AUDIT dispositions ×15 — the highest count in this sweep), 28 (SERIES: HE3-GRADE-ARC, four members, one in shard 2).

**Two gaps found in v3, recorded as format evidence:**

1. **No rule covers a display that is BYTE-FROZEN BY A CONSUMER'S PIN while its own note needs to repair it.** Freeze predicate (F3) is a *third* kind of freeze — not a text-freeze at acceptance (F1) and not an instrument-freeze (F2) — and it forces a structural pattern (repair-adjacent, not repair-in-place) that the template has no vocabulary for. This shard invented test 5 (§6.0) to handle it. **Proposed fix: add `consumer-pin freeze` to rule 21's list, and a `PINNED-BY:` field naming the consumers, so a merge cannot flatten a definition into its adjacent pin.**

2. **Rule 18's kinds do not distinguish a rider that NARROWS an open box from one that widens a claim.** R8-2 and R8-3 both *prove* previously boxed material, shrinking HE3-BOX-6 — filed here as `license` + `inventory completion`, but neither name says “an obligation was retired”. The difference matters for a hypothesis ledger. **Proposed fix: a `box-narrowing` kind, or a `RETIRES:` field listing the obligations a unit discharges.**

---

## 7. SHARD NOTES

- **Cross-shard corrections applied (six, all inbound to this range).**
  (1) **post-PE3 M-1** (1591–1618) → `.12` (the starved-corner parenthetical, corrected under two readings; the frozen fence stands by conservativity).
  (2) **R8-1** (1634–1689) → `.37` (HE3-5's three bullets replaced), `.38` (the Interpretation's q-power framing scope-pinned), and `.15` (the recursive reading of “decided”).
  (3) **R8-2** (1691–1734) → `.33` (branch (i) PROVED as LEMMA HE3-4U; “BOTH … BOXED” corrected to “(ii) alone”), `.17` and `.01` (the μ ≥ 4 reservation becomes accurate), `.35` (HE3-6 consumed by the repair).
  (4) **R8-3** (1736–1772) → `.01`, `.17` (the `n ≤ 7` range gains its missing `D′ ≥ 2` derivation, LEMMA HE3-4D1).
  (5) **R8-4** (1774–1793) → `.32` (the `S_r` display replaced by the piecewise `β_ρ`).
  (6) **R8-5** (1795–1819) → `.25` (HE3-0's proof sentence re-pointed from GENHN-2 to HE6-0″).
  R8-2 and R8-3 are **licenses that NARROW HE3-BOX-6**; R8-1, R8-4, R8-5 are replacements/provenance-riders. All five carry “awaiting sol discharge-confirmation” (1851–1853).
- **Range-edge audit.** Line 1274 is the Interpretation's last sentence (“the theorem and the boundary are complementary, not competing.”); line 1275 is blank; line 1276 opens `## S7. BOXES, GRADE, AND COVERAGE`. **No source statement unit is cut at the edge.** The manifest's boundary falls exactly on a section break.
- **Outside-HOME material used only as resolver, never inventoried here:** §S7's six boxes (HE3-BOX-1 … -6, including BOX-4b's sealed-vs-delivered disclosure), §S8's battery description, §S9's verdict and five Q-blocks, §S9′'s supplementary leg P1–P4 with its coverage note, and both dated append blocks. Shard 2 owns them.
- **Protocol versus supply.** §S1–S6's supply set is inventoried; **no consumption append is claimed landed on any consumer note**, and none is invented. Four inbound streams are recorded at their targets.
- **Numbering.** Temporary IDs `EFF.HE3.s1of2.01`–`.38`, to be reconciled with shard 2 at the merge run. **Merge hazards to flag:**
  (a) **`.09` is compiler-assembled** and has no source span; the merge must keep its content (HE3 claims / GENHN records open) or move it to an OPEN-CALL.
  (b) **Three displays are BYTE-FROZEN by consumer pins** (`.13` DEFINITION 1, `.27`'s above-λ clause, `.31`'s (★)); the merge must not flatten `.13` into `.14`.
  (c) **Five TERMINAL readings are “awaiting sol discharge-confirmation”** (`.12` is confirmed by PE3; `.32`, `.33`, `.37`, `.25`, `.01`/`.17` ride the A5 wave).
  (d) **`.34` cites LEMMA GENHN-T(b), which GENHN itself REFUTED** and replaced by T(b)′ (source defect 6). The merge must decide whether to re-point the citation; the compiler did not.
  (e) **The strike-through reading rule** (§1) must travel with the merged spec, or a reader will take refuted text as current.
  (f) **SERIES HE3-GRADE-ARC** has members in both shards.

---

## 8. Self-audit and OPEN-CALLs

### OPEN-CALL 1 — the “UNCONDITIONAL” headline and the grade must be read together, and the spec cannot decide how a chapter cut should present them

`.01`'s title says `[GENHN-HE(μ ≥ 3)]` is **CLOSED at μ ≤ 3, UNCONDITIONAL, degrees n ≤ 7**. `.17` defines the word: “no assumed hypothesis inside this note's mathematics at μ ≤ 3 … It does NOT upgrade the grade”. `.02` puts the grade at **1/2** (one clean pass), and the A5 wave folded **five further REAL findings after that clean pass**, with the note's own ledger line reading “awaiting sol discharge-confirmation”. **Decision needed: whether a chapter cut may present the μ ≤ 3 result as established, and with what qualifier.** This shard compiles all three facts side by side and refuses to collapse them.

### OPEN-CALL 2 — HE3's discharge of `[GENHN-HE(μ ≥ 3)]` has not landed on GENHN

Verified per rule 10 against GENHN's FULL append chain to its line 2627: **no append records HE3's discharge**, and GENHN's §S9.2 item 1 still reads “THE one load-bearing open lemma of the whole composite program.” The only landed edge runs the other way (GENHN's `[r1]` erratum cites HE3-0). `spec/HYPOTHESIS_LEDGER.md` HYP.81 (count 10) indexes the box as a live obligation. **Decision needed: whether the merged spec reads HE3's discharge onto GENHN's box, at what grade, and whether GENHN owes a dated append.** The compiler does not adjudicate — see `.09`.

### OPEN-CALL 3 — the consumer trace's byte-unchanged claims were verified at designation level only

`.06` asserts, for HE6 and HE7 at pin `7a95449`, that specific clauses are “byte-unchanged”. **This compiler verified that every consumed designation EXISTS in each target (13 greps, all ≥ 1) but did NOT diff the clauses against the `7a95449` blob.** Doing so would require checking out the pinned blob and comparing spans. **Decision needed: whether the merge run performs the byte-diff, or records the trace as an inherited assertion.** Two related gaps surfaced while checking: **HE7 also consumes `HE3-BOX-6`** (count 12 per `spec/EFF-HE7-s1of3.md` §3.1), which the trace does not list (source defect 1); and the trace's GENIND row was confirmed by grep ✓.

### OPEN-CALL 4 — “decided leaf” has two candidate definitions and the note lists the question as open

`.15` (DEFINITION 2) requires terminal separability + lift-stability at every event; `.37` (LEMMA HE3-5) gives a window criterion; `.38` asserts they coincide (“The theorem's hypothesis "DECIDED leaf" is precisely LEMMA HE3-5's condition”); **HE3-BOX-5 item (4) lists the coincidence as an open check** the battery measures both sides of; and **R8-1 makes HE3-5 recursive**, which is what would make the coincidence true. **Decision needed: whether the merged spec asserts the coincidence under R8-1's recursive reading, or carries it as open.** No silent choice was made.

### OPEN-CALL 5 — the A5 wave's five repairs are all “awaiting sol discharge-confirmation”

R8-1..R8-5 (1821–1853, shard 2) close with: “Ledger: HE3's row → 5 repairs folded, **awaiting sol discharge-confirmation**.” Two of them (R8-2, R8-3) **narrow HE3-BOX-6 and are load-bearing for the headline's `n ≤ 7` range**; one (R8-1) **refutes a displayed bullet** of a lemma the battery's HE-BND leg was scored against. **Decision needed: whether a chapter cut may consume landed-but-unconfirmed repairs as current** — the same question `spec/EFF-GENHN-s2of2.md` OPEN-CALL 4 raises for GENHN, and the two should be answered together.

### OPEN-CALL 6 — §S6.2's “both branches boxed” contradicted §S1 for the whole pre-A5 period, and the corpus consumed HE3 during it

`.33` displayed “**Both branches below are therefore to be read as BOXED**” while `.17` and HE3-BOX-6 said only branch (ii) was. The A5 verification note names it as “the internal contradiction”. **The note was consumed by HE6 and HE7 (frozen at `7a95449`) during that period**, and `.06`'s trace — computed at `[r1]`, before A5 — does not mention it. **Decision needed: whether the consumer trace must be re-run against the post-A5 text.** Recorded, not resolved.

### Recorded source defects (flagged, not silently repaired)

1. **`.06`:** the CONSUMER TRACE's HE7 row lists “DEF 1/2; the convex duality (★)” but **omits `HE3-BOX-6`**, which `spec/EFF-HE7-s1of3.md` §3.1 records HE7 citing at count 12. The trace is therefore incomplete for HE7.
2. **`.07`:** `ϖ-CONVENTION` has count **0** in `HE6_PROOF_2026-08-08.md`; the target's heading is `**CONVENTION (ϖ-normalizers: twist-free).**` (line 104). Referent verified; carried descriptively.
3. **`.18`:** COROLLARY HE3.C's conditionality phrase “{GENHN's S9 compression/coverage boxes}” under-describes `[GENHN-TOW-1]`, which GENHN's own §S9.2 files under **MATHEMATICS (new theorems needed)**, not compression or coverage.
4. **`.19`:** §S2's “no binomial expansion is used” is loose — the expansion IS used, and `.27`'s PE1-F4 repair says so; what is characteristic-free is the residue-level statement.
5. **`.19`:** §S2's “Sampling κ over the integers inverts (LEMMA HE3-3)” omits (SEP), which `.29` shows is necessary. The summary predates its own qualification.
6. **`.34`:** the stage-CS step cites “the multiplicative composition of LEMMA GENHN-T(b), **here PROVED for σ rather than assumed**” — and GENHN's `[r2]` **REFUTED** T(b) at the leaf level, replacing it with T(b)′. HE3's σ-composition claim is compatible with what GENHN says survives (“the multiplicative (e,f)- and σ-composition FORMULAS survive”), **but the citation names a refuted lemma.** No re-pointing was invented.
7. **§S9:** the sealed battery's artifact hashes are given as “hashes in the commit message”, i.e. **not in the note** — UNPINNED from the note's own text, unlike `he3r1_supp.py`'s three full md5s.
8. **`.11` vs `.12`:** the starved-corner list is wrong under both readings (post-PE3 M-1) and the frozen text stands; the fence survives only by conservativity, and a future consumer at `d_λ = μ` must use the four-element list.

### Fidelity audit

- Every CANONICAL STATEMENT is a verbatim source quotation or is explicitly marked `[ASSEMBLED]` (one unit, `.09`). **No inverse, sign, quantifier, index, level, inequality direction, or implication direction was altered anywhere.** **Strike-through markers are reproduced exactly**, and the header states the reading rule that makes them unambiguous.
- One quoted proof carries a bracketed compiler insertion, at `.25` (`[**R8-5, 2026-08-12: READ AS** …]`), marked inline and quoted again in the CONDITIONALITY. One quotation at `.02` elides a clause; the elision is flagged in a parenthetical immediately below and the elided text is quoted at `.03`.
- Truncations inside quotations: used at `.19` and `.34`, both marked `…`; **no truncation removes a hypothesis, a quantifier, or a negation.**
- Terminal punctuation and blockquote nesting are preserved; `.13`, `.15`, `.16`, `.17`, `.25`, `.27`, `.29`, `.32`, `.35`, `.37` reproduce the source's `> >` nesting where the source nests.
- **Twenty arithmetic audits were computed fresh** (rule 22) at `.03`, `.05`, `.07`, `.10`, `.11`, `.13`, `.14`, `.15`, `.16`, `.17`, `.19`, `.20`, `.21`, `.22`, `.23`, `.24`, `.25`, `.26`, `.27`, `.28`, `.29`, `.30`, `.31`, `.32`, `.33`, `.34`, `.35`, `.36`, `.37`. **Every one reproduced the source exactly.** Six produced findings the source does not state: the `Q^{f₁} ≤ 4` four-element corner (independently confirming the post-PE3 M-1 append before reading it); the `D′ = 1` gap in the `n ≤ 7` argument (independently confirming R8-3); the error-cancellation arithmetic that explains why the battery missed PE1 F5; the `HE-T-UNDET` count `C(5,2) = 10`; the five μ = 3 stage types matching §S9's table row for row; and the `(3;2,2,2;1)` witness's discriminant and square-set check.
- **38 external XREF designations, every one grep-verified with a fixed-string count ≥ 1 recorded inline and in §3.1.** One candidate with count 0 (`ϖ-CONVENTION`) is explicitly NOT emitted and is recorded as source defect 2.
- **5 commit pins verified with `git cat-file -t` (5/5 → commit); 25 artifact/report/log filenames verified present on disk (25/25); 3 full md5s recorded; the sealed battery's hashes marked UNPINNED-from-the-note.**
- Status and mathematical content are kept as distinct predicates, and this shard blocks two conflations explicitly (§6.2): UNCONDITIONAL-vs-accepted, and the two “decided” conditions.
- Out-of-range material is used only to resolve in-range HOME units; shard 2 owns §S7–S9′ and both dated append blocks.
- **Honest limitation of this shard:** all six inbound corrections are physically in shard 2, and five of them are “awaiting sol discharge-confirmation” (OPEN-CALL 5). Two of those five (R8-2, R8-3) are load-bearing for the headline's own range. Every affected unit quotes the governing corrective text verbatim, so shard 1 is self-contained as a *reading*, but the merge run must install the edges listed in §7 and answer OPEN-CALLs 1, 2 and 5 before a chapter cut consumes the headline.

EFF-HE3-s1of2 COMPILED: 38 statements / 38 xrefs verified / 6 open calls
