# EFF-W11 — CANONICAL EFFECTIVE SPECIFICATION v2

## 1. Header

**Source note:** `lean/notes/openmath/W11_PROOF_2026-08-08.md`

**HEAD blob hash:** `c83597ab24a2e38836543accde5bc3de22615dac`

**Compilation context:** `docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md`, Revision 2, Stage 0a.

**Governing template:** `spec/EFF_TEMPLATE_v2.md` (all rules; full compilation).

**COMPILED-BY:** opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). CODEX CROSS-READ OWED (post-reset).

### Effective-text rule

This note's supersession structure is **unlike T3/T4/T5**: it is not a base plus round-appended replacement instructions. It is a **byte-frozen accepted body with in-line strike-and-replace markup**, plus a **dated annex of four post-acceptance corrections**. Both mechanisms are declared in the note.

Mechanism 1 — in-body strikeout. The r1 and r2 repairs were applied **into the body** as `~~struck~~` **[r-tag, finding]** replacement pairs, and the body is then frozen:

> “**FREEZE-CONVENTION STAMP**: the accepted text is the post-r2 body,
> byte-frozen since 31506b3 (PE4 verified `git diff` empty AND that each
> prior pass provably read exactly its era's text); this record and any
> future annex are dated appends only.”

Mechanism 2 — the dated annex. Four corrections were folded post-acceptance:

> “The E9 fold run
> (gpt-5.6-sol high, runs/cert2/E9_w11_annex_output.log) adjudicated
> all four REAL at HEAD and derived the repairs below, each with its
> consumer sweep. Everything above this heading is byte-untouched by
> this append.”

Each of the four announces its own supersession scope in its own first sentence — C7-F1: “This append supersedes every occurrence of “seven-family decided menu,” “the decided leaves are exactly the seven families,” and “Rows (i) with counts (ii) are the complete specification the grown omMenu must transcribe” by the following precise statement.”; C7-F2: “Clause (iv), S4.1’s “complete specification,” and the corresponding acceptance language are superseded by the following display.”; C7-F3: “The sentence in S2.5 beginning “NOTE the counts are EXACT window counts equal to (limit density)·q^(2N)” is superseded by the following.”; C7-F4: “Every unqualified assertion in S2.2, S5, S7/S10, or the acceptance record that “every p = 2 RAM member is wild” is superseded by the following case distinction.”

**Therefore the effective text is: the byte-frozen post-r2 body (strikeouts resolved to their replacements), plus the acceptance record, plus the four C7 corrections applied to their declared targets.** The `~~…~~` spans are historical; the bracketed `[r1, F#]` / `[r2, PE2-F#]` texts govern.

### Supersession chain

`[TABLE]`

| Target | Superseded text | Governing text | Mechanism |
|---|---|---|---|
| Clause (i)'s “seven families” | S1(i) table header + acceptance phrase “seven-family decided menu” | **C7-F1**'s (i′): six shape families + one finite-window σ-boundary family | dated annex |
| Clause (iv) + S4.1 “complete specification” | S1(iv), S4.1 | **C7-F2**'s (iv′): mathematical type-indexed target + finite density corollary; the API choice is open | dated annex |
| S2.5's no-truncation sentence | “NOTE the counts are EXACT window counts equal to (limit density)·q^(2N)” | **C7-F3**: exact for genuine rows; SPLIT-TAIL is a moving boundary cell with mass (q−1)q^(−N−1) | dated annex |
| “every p = 2 RAM member is wild” | S2.2, S5, S7/S10, acceptance | **C7-F4**: three arithmetic subcases; the inseparable one is ramified-not-tame but not called wild | dated annex |
| S2.4's evaluated legs | `~~q²·X, X, q·X, total (q²+q+1)·X = μ_s~~` | **[r1, F1]** q·X, X/q, X, total ((q²+q+1)/q)·X = q^(−3s−2) = μ_s | in-body strike |
| S2.2's disc = 0 side-claim | `~~never decided at any window … v(disc) = ∞ forces u = w = ∞~~` | **[r1, F2]** the two-case mixed/equal-characteristic statement | in-body strike |
| S4.2's INERTDEEP sum | `~~·q~~` (a double-applied center factor) | **[r1, F3]** Σ_k (q−1)/(2q^(2k+1)) = 1/(2q(q+1)) = 1/12 at q = 2 | in-body strike |
| S5's wildness sentence | `~~every RAM member has v(disc) ∈ {h+1, h+2}~~` | **[r1, F4]** MIXED …, while in EQUAL characteristic 2 … ∪ {∞} | in-body strike |
| SPLIT-TAIL's absorption | `~~absorbed into 2SIDED/SPLITEQ as N → ∞~~` | **[r1, F5]** absorbed into 2SIDED only (plus the measure-zero x(x+A₁) locus) | in-body strike |
| S2.4's undecided-residue claim | `~~(contains split, inert AND ram lifts)~~` | **[r1, F6]** scoped to set level; per member a ram lift can be ABSENT | in-body strike |
| S1/S2.2/S5's “mixed Z_p-type” | unpinned | **[r2, PE2-F2]** = ABSOLUTELY UNRAMIFIED, v(p) = 1, with the Z₂[√2] counterexample and a sweep | in-body strike |
| S2.5's every-window split = inert | limit-fraction argument alone | **[r2, PE2-F1]** the finite telescoping identity, transcribed from `W11_passPE2_report.md` @ 473a993 | in-body strike |
| S10's arc wording | `~~the hostile arc has not begun~~` | **[r1]** + **[r2 echo]**, then the ACCEPTANCE RECORD | in-body strike, then append |
| The header S-STATUS grade “0/2” | every “Attempt 0/2” / “counter 0/2” | **the ACCEPTANCE RECORD: ACCEPTED at 2/2** | append |

### Scope of record — mandatory two-predicate split

#### A. Mathematical claim set

The acceptance record states what is accepted, without truncation:

> “**WHAT IS ACCEPTED**: THEOREM W-11(n=2) — the seven-family decided
> menu of monic quadratics over any complete DVR with exact q-polynomial
> window counts, σ-undecided EXACTLY q^N (hExhaust at n=2 with exact
> drainage rate), limit densities split = inert = q/(2(q+1)), ram =
> 1/(q+1), Σ = 1, both characteristics, wild p=2 included — at its
> displayed boxes and conditionality.”

Two of its phrases are then re-read by the annex. C7-F1: “The acceptance record’s phrase “seven-family decided menu” is henceforth read as “six decided shape families plus one finite-window σ-boundary family.”” C7-F4: “The acceptance phrase “wild p = 2 included” is henceforth read as asserting the included separable wild members, alongside separately included purely inseparable ramified members.”

So the accepted mathematical claim set is: **clauses (i′), (ii), (iii) PROVED at n = 2; clause (iv′) as the proved mathematical target (not an API transcription); the general-n W-11 is a stated program (BOX-1), not proved.**

#### B. Consumption/protocol scope

Two distinct protocol facts, both explicit.

(a) **Downstream consumption is LIVE, not deferred** — unlike T3/T4/T5, W-11's consumers already exist. The acceptance record's PE3 leg reads: “downstream-consumption audit of W-12/HMENU3 honest”. S8 lists four consumers. Each C7 correction ships its own CONSUMER SWEEP paragraph.

(b) **The Lean tie is a TARGET, not a landed edge.** S9:

> “**Lean anchors at HEAD** (`OM/RealInstanceV2.lean`
> `montes_unconditional_exhaustive`/`hExhaust`, `OMCountV2.omMenu`/
> `omMenu_order0`, `gate3_inert_q2`) — cited as the tie TARGETS (S4.1/
> S4.2), no Lean changed.”

Verified at compile time: **no Lean source file names W-11 or W11** (`grep -rlF 'W11' lean/LeanUrat/` returns only `MovesS/MANIFEST.json`; `grep -rlF 'W-11' lean/LeanUrat/` returns nothing). The edge runs one way — W-11 → the Lean gates as targets — and BOX-2 keeps it there.

### Resolution rules applied

1. Every `~~struck~~` span is historical; the bracketed replacement immediately following it governs. Thirteen such pairs are tabulated above.
2. The four C7 corrections govern their declared targets in full, including the acceptance record's own two re-read phrases.
3. Each C7 correction's CONSUMER SWEEP is part of the effective text — it is what makes the correction non-destructive, and it names exactly which downstream reads survive.
4. C7-F1 changes the **type** of SPLIT-TAIL, not any count: “The S7/S10 SPLIT-TAIL census keys remain valid as window-cell keys, not typeOf keys.” No number in the note moves.
5. C7-F3 removes a false *identification* only: “only the false identification of the boundary count with a fixed limit-density multiple is removed.”
6. C7-F4 is terminology plus a case split: “The count and σ = ram assignment are uniform across all three; only the terminology differs.”
7. The body is byte-frozen since `31506b3`; the annex is a dated append. The compiler verified `31506b3` exists and that the note is clean in the working tree.
8. All grade language (“Attempt 0/2”, “counter 0/2”, “PE3 = the next attempt”) is historical after the acceptance record.
9. The machine record is FIRST-PARTY and re-verifiable: the compiler re-checked the runner's byte-identity to its seal and all six md5 pins (§4.4).
10. Numbers quoted from S7/S10 are machine records, not derivations; every closed form they check is separately derived in S2.

### Quotation and prosification discipline

All source displays and tables are quotations or marked `[ASSEMBLED]`; every source table is `[TABLE]`; nothing is prosified; truncation carries an explicit ellipsis. Struck text is reproduced inside `~~…~~` exactly as the note writes it, so the historical reading stays visible to the cross-read.

---

## 2. NON-IMPORTS

W-11 carries an explicit **perimeter-hygiene section** — §S3, “NOT CONSUMED (perimeter hygiene, displayed)” — which is unusual and load-bearing: it names three accepted suppliers the note deliberately does not use.

**N-1 — DULEMMA / (DMULT-s).** S3:

> “**DULEMMA / (DMULT-s)** [PROVED-conditional at 048cf6d/f819f26, perimeter
> e_m ≥ 2]: NOT consumed anywhere above — no clause needs value-layer
> multiplicativity, and in particular the e_m = 1 rows here (INERTDEEP,
> SPLITEQ — e = 1 reads) are COUNT statements, not (DMULT) statements: no
> stretch of DULEMMA's measured e_m = 1 row occurs.”

**N-2 — the JC composite-stage warrant.** S3:

> “**JC composite-stage warrant** (JC-PSIKER/JC-LOAD @ 83f47f4): not needed
> at n = 2 — there are no composite stages; the refinement recursion is
> proved directly (S2.3). Enters only the general-n program (S4.3).”

**N-3 — the JB row-12 u ≥ 0 proviso.** S3:

> “**JB row-12 u ≥ 0 proviso** (GRTJB @ 83f47f4): not consumed — all
> polygons computed outright on the finite grid {0,1,2} (W-10 H-3's
> pattern). Owed by the general program only.”

**N-4 — no Lean code is written or changed.** BOX-2:

> “**W11-BOX-2 (the Lean menu is not grown here).** No Lean code is written
> or changed; `omMenu` remains the order-0 slice at HEAD. Clause (iv) is
> the proved SPEC (what Phase-B must transcribe), not the transcription.”

**N-5 — no `htameFE` contact.** BOX-7:

> “**W11-BOX-7 (no per-row FE claim).** The proved split = inert symmetry
> (every window, exact) is displayed as structure; its relation to the
> tame functional equation / palindromy (`htameFE`) is NOT claimed — no
> clause of this note discharges or weakens the htameFE hypothesis.”

This is a sharp fence: split = inert at every window is *exactly* the kind of symmetry a palindromy argument would want, and the note declines the inference.

**N-6 — the two alternative charges are not composed.** The Divergence box:

> “(a) the shape-generic W-10 (all decided shapes at all orders/degrees)
> remains OPEN — W10-BOX-1 stands untouched … (b) the
> R_τ ∈ ℚ(q) tie falls out at n = 2 as a corollary … — delivered as display, not
> as the general-r theorem.”

**N-7 — no general-n claim.** BOX-1: “Nothing at n ≥ 3 is claimed.”

**N-8 — J-D0 is a frame, not a premise, at the instance.** S9: “the n = 2 census equalities are proved directly here, so J-D0 is corroborating at the instance, load-bearing only for the general-program framing (S4.3 inherits its BOX-2 gauge-form perimeter).”

**N-9 — PARI covers mixed characteristic only.** BOX-4: “PARI is mixed-characteristic only; eq-char rows are SAME-class”. C7-F4 sharpens it: the TAMEDISC tooth “supplies no equal-characteristic evidence.”

**N-10 — the general weld suppliers are template cites only.** S9: the six accepted weld suppliers are “cited for the TEMPLATE faces only (S4.3, W11-TOWER's grid tie γ = e·wPhi + h); S2's n = 2 proofs are self-contained elementary arithmetic + Hensel.”

Accordingly **no edge is created** from W-11 to value-layer multiplicativity, to the JC/JB open faces, to `htameFE`, to any n ≥ 3 statement, or to any Lean term.

---

## 3. Statement inventory

42 units, contiguous, in effective-text order.

### EFF.W11.01  [scope-record]

**CANONICAL STATEMENT — the unit line and instrument** `[ASSEMBLED: the header's unit/instrument sentences; the S-STATUS arc narrative is reproduced in EFF.W11.40's trace rather than here, being superseded by the acceptance record]`:

> “**Unit:** W-11, the J-D block's rung after THEOREM W-10(2,1,1)
> (GRT_WELD_BLUEPRINT_2026-08-08 §S3.1 row W-11; WELD_SYNTHESIS_2026-08-05
> §4(ii) execution order step (3)).”

> “Per the effort directive (Asvin 2026-08-05) this is an INTERMEDIATE
> theorem: disclosure-grade honesty, honest boxes over reach. **Instrument:**
> sealed two-commit battery `verification/openmath/w11_checks.py` (30 census
> rows = 1,235,872 monic quadratics enumerated at the seal commit's row list;
> 8-tower frozen-roster realization leg incl. a (2,3,1) wild realization;
> PARI/GP independent per-polynomial oracle leg); verdict §S10, appended at
> commit 2 FROM the committed artifacts.”

**DERIVATION:** `[RECORD]` The two-commit seal discipline — seal the unrun runner at commit 1, append the verdict from the committed artifacts at commit 2 — is what makes S10 evidence rather than assertion.

**CONDITIONALITY:** “INTERMEDIATE theorem” is the standing effort directive, not a hedge on clauses (i′)–(iii), which are graded PROVED.

**RESOLUTION TRACE:** header; the embedded `**Attempt grade 0/2** ~~(composed; no hostile arc)~~ **[r1→r2] S-STATUS …**` block is historical after EFF.W11.40.

**TEETH:** S7's five teeth; §S10's scorecard.

---

### EFF.W11.02  [scope-record]

**CANONICAL STATEMENT:**

> “**What W-11 is (one breath).** W-10 proved ONE menu row's count equality
> (the (2,1,1) Eisenstein stratum). W-11 asks the next J-D question: WHICH
> decided shapes exist, do their densities exhaust the space, and does the
> undecided residue drain — the mathematics behind the Lean capstone's
> `hExhaust` hypothesis (`montes_unconditional_exhaustive`,
> `OM/RealInstanceV2.lean`: `undecidedCount N / realP^(nN) → 0`) and behind
> the omMenu growth obligation (PROJECT_STATE Phase B). THIS note answers all
> three AT n = 2, COMPLETELY: the full decided menu (seven leaf families,
> each ONE polynomial/rational family in q, both characteristics, wild p = 2
> included), the exact window-N count of every row, the exhaustiveness sum
> = 1, and the drainage law EXACTLY — the σ-undecided mass at window N is
> q^(−N), not merely o(1). The general-n menu tie is STATED as mathematics
> with its obligations displayed (S4.3), not claimed.”

**DERIVATION:** `[SCOPE RECORD]` The `hExhaust` shape quoted here is **verified byte-literally against Lean at compile time** (XREF L02): `OM/RealInstanceV2.lean` lines 439–442 read

```
theorem montes_unconditional_exhaustive (n : ℕ) (hn : 0 < n) (σ : FactorizationType)
    (hσ : σ.degree = n) (htameFE : TameFunctionalEquation realF2 n σ)
    (hExhaust : Filter.Tendsto
      (fun N => (realM2 n hn).undecidedCount N / (M9.realP : ℚ) ^ (n * N))
```

— exactly the `undecidedCount N / realP^(nN) → 0` the note paraphrases.

**CONDITIONALITY:** “seven leaf families” is re-read as six shape families plus one boundary family per C7-F1 (EFF.W11.08).

**RESOLUTION TRACE:** header; the “seven leaf families” phrase falls under C7-F1's supersession of “the decided leaves are exactly the seven families” by extension of its declared scope, and is read accordingly.

**TEETH:** the whole battery.

---

### EFF.W11.03  [table]

**CANONICAL STATEMENT — the blueprint's W-11 row, verbatim:**

> “| **W-11** | menu tie: decided order-r shapes ↔ grown omMenu entries
> (typeOf-keyed), hExhaust program stated as mathematics | J-D | **M** |
> W-10 | omMenu order-0 slice (Lean, capstone); L5fix menu finiteness
> (math) |”

**DERIVATION:** `[IMPORTED — charge]` Source `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md` §S3.1 (XREF X01). The note reproduces it because the charge mandates the display (S0's heading: “RECONCILIATION WITH THE BLUEPRINT (charge-mandated display)”).

**CONDITIONALITY:** none; this is the charge.

**RESOLUTION TRACE:** S0; unchanged.

**TEETH:** EFF.W11.04's two-bullet reconciliation.

---

### EFF.W11.04  [scope-record]

**CANONICAL STATEMENT:**

> “**What this note composes and why.** Exactly the blueprint's W-11, executed
> instance-first at the n = 2 slice — the same pattern W-10 set (prove the
> first concrete rung completely; state the general rung as a program):
>
> * "decided order-r shapes ↔ grown omMenu entries (typeOf-keyed)" → the
>   COMPLETE decided menu at n = 2, proved (S2), displayed as the exact
>   row-list the grown `omMenu 2 σ` must equal (S4.1) — the mathematical
>   side of the tie is now a theorem; the Lean side (writing the order-≥ 1
>   `omMenu`/`omCount` entries) remains the Phase-B code obligation (BOX-2).
> * "hExhaust program stated as mathematics" → EXCEEDED at n = 2: not only
>   stated but PROVED, with an exact law (clause (iii): σ-undecided count
>   = q^N of q^(2N), so the normalized undecided mass is exactly q^(−N));
>   stated as mathematics at general n (S4.3).”

**DERIVATION:** `[SCOPE RECORD]` The second bullet's “EXCEEDED” is the note's central delivery: the blueprint asked for a *stated program* and got a *theorem with an exact rate*.

**CONDITIONALITY:** the first bullet's “the exact row-list the grown `omMenu 2 σ` must equal” is superseded by C7-F2 (EFF.W11.12): the six families are the **mathematical** target, not a term of the current bounded interface.

**RESOLUTION TRACE:** S0; first bullet re-scoped by C7-F2.

**TEETH:** S4.1, S4.2.

---

### EFF.W11.05  [fence]

**CANONICAL STATEMENT:**

> “**Divergence box (charge: box any divergence).** The charge named two
> alternative readings of "the natural next rung": (a) generalizing W-10's
> count equality toward the shape-generic statement, and (b) the R_τ ∈ ℚ(q)
> tie. Neither is the blueprint's W-11, and neither is composed AS SUCH here:
> (a) the shape-generic W-10 (all decided shapes at all orders/degrees)
> remains OPEN — W10-BOX-1 stands untouched; within n = 2, however, the count
> equality IS proved for every menu row (clause (ii)), which is the n = 2
> restriction of general W-10 as a by-product of the menu proof. (b) the
> R_τ ∈ ℚ(q) tie falls out at n = 2 as a corollary (every menu row and every
> σ-total is one rational function of q, S2.5/S5) — delivered as display, not
> as the general-r theorem. No other divergence: the statement below IS the
> blueprint row at its first slice.”

**DERIVATION:** `[FENCE]` **This is where the R_σ(q) / R_τ ∈ ℚ(q) content of the note is scoped**: every menu row and every σ-total is one rational function of q, delivered as a *display* at n = 2, explicitly NOT as the general-r theorem. The rational functions themselves are EFF.W11.07/.09/.10/.12.

**CONDITIONALITY:** the general-r R_τ tie and the shape-generic W-10 are both OPEN (W10-BOX-1, W11-BOX-1).

**RESOLUTION TRACE:** S0; unchanged.

**TEETH:** S6's boxes.

---

### EFF.W11.06  [convention]

**CANONICAL STATEMENT** `[ASSEMBLED: S1's setting sentence with the r2 PE2-F2 pin resolved in place]`:

> “Fix n = 2. Let O be a complete DVR with residue field F_q (either
> characteristic: mixed Z_p-type **[r2, PE2-F2 pin: "mixed Z_p-type" =
> ABSOLUTELY UNRAMIFIED, v(p) = 1 — a residue field alone does not pin
> absolute ramification. The pin is load-bearing ONLY for the two mixed-2
> disc-spectrum displays (S2.2 RAM bullet, S5); clauses (i)–(iii) and
> every count/σ law hold over any ramified mixed base too — the proof
> never uses v(p) (S2.3's mixed-2 leg needs only v(2s) ≥ k+1, true for
> any v(2))]** or equal F_q[[t]]-type), π a uniformizer,
> N ≥ 2 a truncation window; enumerate monic quadratics f = x² + a₁x + a₀
> over O/π^N (q^(2N) of them). The classifier read is the RECURSIVE n = 2
> read: level-0 factorization of f̄; on a double root, recenter (W-10 S2.1
> mechanics) and read the Newton polygon on {(0, u = v(a₀′)), (1, w =
> v(a₁′)), (2, 0)}; on a residual double root (the refinement case),
> recenter again at depth k and recurse. σ ∈ {split, inert, ram} is the
> splitting type.”

**DERIVATION:** `[DEFINITIONAL + IMPORTED]` The recentering mechanics are W-10's S2.1, “consumed, not re-proved” (S2's opening). The r2 pin's own blast-radius statement is what keeps the pin from narrowing the theorem: the counting clauses hold over any ramified mixed base.

**CONDITIONALITY:** the v(p) = 1 pin binds **only** the two mixed-2 discriminant-spectrum displays. Clauses (i)–(iii) do not use it.

**RESOLUTION TRACE:** S1, with the r2 PE2-F2 bracket inserted at the phrase “mixed Z_p-type”. The same bracket records an out-of-scope hit it declines to repair: “W10_PROOF_2026-08-08.md S1 uses the same unpinned "mixed Z_p-type" phrase with its p = 2 disc laws at v(2) = 1 — that note is sealed; same latent fence, its own arc's to carry”.

**TEETH:** the S2.2/S5 disc displays; the machine rows (“the battery's mixed rows are Z_p exactly, v(2) = 1 — no machine surface touched”).

---

### EFF.W11.07  [table]

**CANONICAL STATEMENT — clause (i) MENU, the row table** (the *table* survives C7-F1 intact; only the word “seven” and SPLIT-TAIL's TYPE are re-read):

> “(i) [MENU] The decided leaves of the n = 2 read are EXACTLY the seven
>     families (params absolute; k ≥ 1, h ≥ 1 odd, 1 ≤ w₁ < w₂):”

`[TABLE]`

| leaf | shape data | σ | limit density (whole space) |
|---|---|---|---|
| SEP-SPLIT | order-0, two distinct linear | split | (q−1)/(2q) |
| SEP-INERT | order-0, irreducible quadratic | inert | (q−1)/(2q) |
| RAM(h) | d0 = 1, one side (e,h,g) = (2,h,1) | ram | (q−1)/q^(h+1) |
| 2SIDED(w₁,w₂) | two length-1 sides, slopes w₁,w₂ | split | (q−1)²/q^(w₁+w₂+2) |
| SPLITEQ(k) | e = 1 side at height k, residual sep-split | split | (q−1)(q−2)/(2q^(2k+2)) |
| INERTDEEP(k) | e = 1 side at height k, residual irreducible | inert | (q−1)/(2q^(2k+1)) |
| SPLIT-TAIL(w) | σ-decided split, shape-truncated at the window | split | (window boundary family; ~~absorbed into 2SIDED/SPLITEQ as N → ∞~~ **[r1, F5] absorbed into 2SIDED only as N → ∞ (plus the measure-zero exact x(x+A₁) locus): tail members have w < N/2 ≤ u/2, so every lift's roots sit at strictly distinct valuations — SPLITEQ (equal-valuation roots) is unreachable from the tail**) |

**DERIVATION:** `[PROVED — S2]` Each row is a leaf of the S2.1 trichotomy (EFF.W11.15) refined by the S2.1 residual census (EFF.W11.16), with limit densities from the S2.5 bracket assembly (EFF.W11.23, EFF.W11.27). **These seven rational functions of q are the note's R_σ(q) forms** — one closed form per row, uniform in q across both characteristics and tame/wild p (EFF.W11.32).

**⚠ THE ROW COUNT IS SIX PLUS ONE, NOT SEVEN.** C7-F1 (EFF.W11.08) re-types SPLIT-TAIL(w) as a finite-window σ-boundary cell family, not a decided shape and not a typeOf key. Every *number* in the table stands.

**CONDITIONALITY:** k ≥ 1, h ≥ 1 odd, 1 ≤ w₁ < w₂; the limit densities are whole-space (not per-center) — the distinction that r1's F3 correction turns on (EFF.W11.30).

**RESOLUTION TRACE:** S1(i), with r1's F5 replacement inside the SPLIT-TAIL cell, and the row's TYPE re-read by C7-F1.

**TEETH:** W11-CENSUS (every (leaf, params) key on 30 rows); P-2.

---

### EFF.W11.08  [lemma]

**CANONICAL STATEMENT — C7-F1's (i′), the governing menu statement:**

> “(i′) [SIX SHAPE FAMILIES + ONE FINITE-WINDOW σ-BOUNDARY FAMILY]
> The decided typeOf-keyed leaves of the recursive n = 2 read are EXACTLY
> the following six families:
>
>   SEP-SPLIT, SEP-INERT, RAM(h), 2SIDED(w₁,w₂),
>   SPLITEQ(k), INERTDEEP(k),
>
> with h ≥ 1 odd, k ≥ 1, and 1 ≤ w₁ < w₂. Their σ-values, shape data,
> limit densities, and exact visible-row counts are exactly those displayed
> in S1(i)–(ii).
>
> At a finite window N there is in addition the σ-decided boundary family
>
>   SPLIT-TAIL_N(w),  1 ≤ w ≤ ⌊(N−1)/2⌋.
>
> It is a family of window cells, not a decided shape and not a typeOf key.
> At a node instance its defining data are A₀ ≡ 0 mod π^N and v(A₁) = w.
> Every lift has u = v(A₀) ≥ N > 2w and hence lies in the split two-sided
> case, but its second root valuation is u−w and is not determined by the
> window. Indeed, choosing lifts with u = 2w+r gives the distinct shapes
> 2SIDED(w,w+r), while the exact lift A₀ = 0 is x(x+A₁). Thus σ = split is
> certified, whereas no single typeOf shape is certified.
>
> Accordingly, the exact finite-window partition in clause (iii) is:
>
>   six genuine decided-shape families
>   ⊔ SPLIT-TAIL_N boundary cells
>   ⊔ σ-UNDECIDED cells.
>
> The limit typeOf menu contains only the six genuine shape families.
> SPLIT-TAIL_N contributes to the finite-window split count and is absorbed
> into the 2SIDED sum as N → ∞, apart from the measure-zero A₀ = 0 locus;
> it is never an omMenu shape entry.”

**DERIVATION:** `[PROVED — one counter-instance]` The argument is a single observation: a SPLIT-TAIL cell's lifts realize *many distinct* typeOf shapes (2SIDED(w,w+r) for every r, plus the exact x(x+A₁)), so the cell certifies σ but not a type. The orchestrator re-checked the instance before transcription: “C7-F1: the boundary counter-instance re-checked (window cell (q,N,w) = (2,4,1) admits lifts of shape 2SIDED(1,4), 2SIDED(1,5), … and the exact A₀ = 0 lift x(x+A₁): one σ, no single typeOf key)”.

**CONSUMER SWEEP (part of the correction):**

> “CONSUMER SWEEP. S2.2’s σ-assignment survives because every tail lift is
> split. S2.4’s finite-window partition survives with SPLIT-TAIL understood
> as a boundary cell. S2.5’s finite telescope survives and still requires
> that boundary cell. Clause (iii), the q^N σ-drainage law, and the
> every-window split = inert identity are unchanged. S4.1 now consistently
> specifies only the six typeOf families. S4.2 and BOX-5 retain their two
> undecided conventions verbatim: the σ-convention counts the boundary as
> decided, while the shape convention counts it as undecided. The S7/S10
> SPLIT-TAIL census keys remain valid as window-cell keys, not typeOf keys.
> W-12/J-D1 consumes the unchanged exhaustive partition; Phase-B consumes
> only the six-family shape target; the general W-10/W-11 template and the
> public density story consume unchanged counts and limits. The acceptance
> record’s phrase “seven-family decided menu” is henceforth read as “six
> decided shape families plus one finite-window σ-boundary family.””

**CONDITIONALITY:** 1 ≤ w ≤ ⌊(N−1)/2⌋ for the boundary family; the six shape families are window-free.

**RESOLUTION TRACE:** dated annex, C7-F1. Supersedes S1(i)'s “seven families”, the acceptance phrase, and (jointly with C7-F2) S4.1's transcription claim.

**TEETH:** the S7/S10 SPLIT-TAIL census keys, now typed as window cells.

---

### EFF.W11.09  [lemma]

**CANONICAL STATEMENT — clause (ii) COUNT LAWS:**

> “(ii) [COUNT LAWS] Every window-visible row's count is ONE q-polynomial,
>     EXACT (no truncation error), summed over all refinement histories
>     (per center; q centers): RAM(h = 2k−1): (q−1)·q^(2N−2k−1);
>     2SIDED(w₁,w₂): (q−1)²·q^(2N−3−w₁−w₂); SPLITEQ(k):
>     ((q−1)(q−2)/2)·q^(2N−2k−3); INERTDEEP(k): ((q−1)/2)·q^(2N−2k−2);
>     SPLIT-TAIL(w): (q−1)·q^(N−2), independent of w; SEP-SPLIT =
>     SEP-INERT = ((q²−q)/2)·q^(2N−2) (whole space, no center factor). The
>     k = 1 RAM row IS THEOREM W-10(2,1,1), consumed at pin (S2.1).”

**DERIVATION:** `[PROVED — S2.5]` Each law is (leaf count from one node instance) × the history bracket q^(k−1) (EFF.W11.23), worked in S2.5:

> “Every window law in clause (ii) is (leaf count from one node
> instance) × q^(k−1), e.g. RAM(2k−1): (q−1)q^(N−1−(2k−1))·q^(N−k)·q^(k−1)
> = (q−1)q^(2N−2k−1); INERTDEEP(k): (q(q−1)/2)·q^(N−2k−1)·q^(N−k−1)·q^(k−1)
> = ((q−1)/2)q^(2N−2k−2); SPLIT-TAIL(w): (q−1)q^(N−1−w)·q^(w−1) =
> (q−1)q^(N−2) (w-independent).”

The w-independence of SPLIT-TAIL is the striking one and is visible raw in the artifact (S10, P-2: “SPLIT-TAIL(1)=(2)=(3)=128 — the w-independence law visible raw”).

**⚠ THE “no truncation error” PHRASE IS SCOPED BY C7-F3.** It holds for the six genuine rows; SPLIT-TAIL is a moving boundary cell with no fixed limit density (EFF.W11.25).

**CONDITIONALITY:** “window-visible”; the per-center vs whole-space convention is explicit (SEP rows carry no center factor).

**RESOLUTION TRACE:** S1(ii); unchanged in the body; the accompanying S2.5 sentence superseded by C7-F3.

**TEETH:** W11-CENSUS 0/375 (P-2); W11-W10TIE 0/1,235,872 (P-3) for the k = 1 RAM row.

---

### EFF.W11.10  [lemma]

**CANONICAL STATEMENT — clause (iii), the exhaustiveness and exact drainage law:**

> “(iii) [EXHAUSTIVENESS + THE EXACT DRAINAGE LAW] The families of (i) plus
>     the σ-undecided residue partition all q^(2N) polynomials, and the
>     σ-undecided count is EXACTLY q^N — normalized undecided mass q^(−N)
>     → 0: the hExhaust statement is TRUE at n = 2 with exact rate. The
>     limit densities sum to 1: split-total = inert-total = q/(2(q+1)),
>     ram-total = 1/(q+1). Moreover split-decided = inert-decided EXACTLY
>     at EVERY window (not just in the limit).”

**DERIVATION:** `[PROVED — S2.4 + S2.5]` Three independent legs: the per-node exhaustiveness identity (EFF.W11.21, nothing leaks at any node), the drainage computation (EFF.W11.26, q^N exactly), and the limit-density sum with the finite telescope (EFF.W11.27). The clause is unchanged by every one of the four C7 corrections — C7-F1: “Clause (iii), the q^N σ-drainage law, and the every-window split = inert identity are unchanged.”; C7-F2: “Clauses (i′)–(iii) are unchanged.”; C7-F3: “Clause (iii)’s partition and q^N drainage law are unchanged.”; C7-F4: “W-12/J-D1, hExhaust, the density totals, and all Lean consumers use only the unchanged counts and σ-partition.”

**⚠ THIS IS THE UNIT THE LEAN CAPSTONE'S `hExhaust` HYPOTHESIS CORRESPONDS TO** — at n = 2, as mathematics. See EFF.W11.30 for the exact tie and its two conventions.

**CONDITIONALITY:** n = 2; the σ-convention of undecidedness (BOX-5; the shape-truncated convention's law is displayed in S4.2 and also drains).

**RESOLUTION TRACE:** S1(iii); untouched by every round and every C7 correction. **The most stable unit in the note.**

**TEETH:** W11-EXHAUST 0/150 — “undecided = q^N EXACTLY on all 30 rows … split-decided = inert-decided EXACTLY on all 30 rows; all 90 classical-sandwich inequalities hold as exact rationals.”

---

### EFF.W11.11  [scope-record]

**CANONICAL STATEMENT — clause (iv) as composed** `[SUPERSEDED by C7-F2; reproduced because its numeric tie survives]`:

> “(iv) [MENU TIE, typeOf-keyed] Rows (i) with counts (ii) are the complete
>     specification the grown `omMenu 2 σ` / `omCount` must transcribe
>     (S4.1); the order-0 slice already in Lean (`omMenu_order0` =
>     `sepShapesOf`) is exactly the SEP rows; the capstone's decided
>     order-0 inert value 1/4 at q = 2 (`gate3_inert_q2`) + the proved
>     deep-inert tail 1/12 = the full inert density 1/3 = q/(2(q+1)).”

**DERIVATION:** `[SPEC DISPLAY]` The arithmetic tie 1/4 + 1/12 = 1/3 is verified: `gate3_inert_q2` is confirmed at compile time (XREF L01, `OM/OMCountV2.lean:646`) to read `theorem gate3_inert_q2 : omCount (sepShape 2 lam2) 2 = 1 / 4 := by`, and the deep-inert tail Σ_{k≥1}(q−1)/(2q^(2k+1)) = 1/(2q(q+1)) = 1/12 at q = 2 is EFF.W11.30.

**⚠ TWO SUPERSESSIONS AND ONE UNRESOLVED CLAUSE.**
(1) “the complete specification the grown `omMenu 2 σ` / `omCount` must transcribe” is superseded in full by C7-F2 (EFF.W11.12).
(2) The middle clause — “the order-0 slice already in Lean (`omMenu_order0` = `sepShapesOf`) is exactly the SEP rows” — is **NOT** superseded by any correction, and it does not survive a compile-time check on its SPLIT half. See OPEN-CALL 1 (§9): Lean's order-0 model is a₀-unit-conditioned, W-11's SEP rows are not, and the two agree on INERT while disagreeing on SPLIT.

**CONDITIONALITY:** “the proved spec display”, per the GRADE box — clause (iv) was never graded PROVED as mathematics, only as a display.

**RESOLUTION TRACE:** S1(iv) → superseded in its transcription claim by C7-F2; its numeric capstone tie survives (C7-F2's sweep: “S4.2’s q = 2 capstone computation consumes the aggregate INERTDEEP value 1/(2q(q+1)) and survives verbatim”).

**TEETH:** no battery row — the Lean side is not machine-tied here (BOX-3: “The Lean evaluator tie remains order-0.”).

---

### EFF.W11.12  [lemma]

**CANONICAL STATEMENT — C7-F2's (iv′), the governing tie statement:**

> “(iv′) [MATHEMATICAL TYPE-INDEXED TARGET + FINITE DENSITY COROLLARY]
> The six genuine shape families of C7-F1 form the countable mathematical
> menus
>
>   M_split = {SEP-SPLIT}
>             ⊔ {2SIDED(w₁,w₂) : 1 ≤ w₁ < w₂}
>             ⊔ {SPLITEQ(k) : k ≥ 1},
>
>   M_inert = {SEP-INERT}
>             ⊔ {INERTDEEP(k) : k ≥ 1},
>
>   M_ram   = {RAM(2k−1) : k ≥ 1}.
>
> Each individual key carries the rational density displayed in S1(i);
> the exact window counts in S1(ii) prove those densities. These data are
> the complete MATHEMATICAL typeOf-keyed target. They are not, by
> themselves, a term of the current bounded omMenu interface, which has
> neither a countable-sum constructor nor a window parameter.
>
> For the density-only consumer, the infinite families admit the following
> finite aggregate corollary, derived from their displayed row densities:
>
>   Σ_{k≥1} (q−1)/q^(2k) = 1/(q+1),                         [RAM]
>
>   Σ_{k≥1} (q−1)/(2q^(2k+1)) = 1/(2q(q+1)),               [INERTDEEP]
>
>   Σ_{1≤w₁<w₂} (q−1)²/q^(w₁+w₂+2)
>     = 1/(q²(q+1)),                                       [2SIDED]
>
>   Σ_{k≥1} (q−1)(q−2)/(2q^(2k+2))
>     = (q−2)/(2q²(q+1)),                                  [SPLITEQ]
>
> and hence
>
>   Σ 2SIDED + Σ SPLITEQ = 1/(2q(q+1))
>                         = Σ INERTDEEP.
>
> Adding the SEP rows gives
>
>   density_split = density_inert = q/(2(q+1)),
>   density_ram = 1/(q+1).
>
> Thus an end-to-end Lean implementation has two honest possible designs:
> (a) extend the interface to a countable summable menu and retain one key
> per typeOf shape; or (b) add explicit finite summary keys carrying the
> aggregate rational functions above, sufficient for the density theorem
> but not literally one key per typeOf shape. A per-window finite menu is
> not an implementation of the current interface unless N is added to that
> interface. This note proves the mathematical inputs for both designs but
> does not choose or implement either design; that choice remains Phase-B
> code/API work under BOX-2.”

**DERIVATION:** `[PROVED — four geometric sums]` Each aggregate is the geometric sum of its row density over the parameter family. The orchestrator re-derived all of them by hand before transcription: “C7-F2: every aggregate sum re-derived by hand (Σ RAM = 1/(q+1); Σ INERTDEEP = 1/(2q(q+1)); Σ 2SIDED = 1/(q²(q+1)); Σ SPLITEQ = (q−2)/(2q²(q+1)); Σ 2SIDED + Σ SPLITEQ = 1/(2q(q+1)) = Σ INERTDEEP; the totals reproduce the note's committed limits split = inert = q/(2(q+1)), ram = 1/(q+1))”.

Note the RAM aggregate re-indexes: S1(i) displays RAM(h) at (q−1)/q^(h+1) for h odd, and h = 2k−1 turns that into (q−1)/q^(2k), summing to (q−1)·q^(−2)/(1−q^(−2)) = (q−1)/(q²−1) = 1/(q+1). ✓

**⚠ THESE FOUR AGGREGATES ARE THE R_σ(q) FORMS A DENSITY-ONLY LEAN CONSUMER WOULD CARRY** — design (b)'s “explicit finite summary keys carrying the aggregate rational functions above”. Neither design is implemented; BOX-2 is open.

**CONSUMER SWEEP (part of the correction):**

> “CONSUMER SWEEP. Clauses (i′)–(iii) are unchanged. S4.1 is now a
> mathematical target rather than a claim of immediate transcription into
> the present API. S4.2’s q = 2 capstone computation consumes the aggregate
> INERTDEEP value 1/(2q(q+1)) and survives verbatim. The order-0 Lean anchor
> omMenu_order0 remains unchanged. Phase-B/DecidedOmCountTie must choose
> design (a) or (b); no existing Lean theorem is claimed to make that
> choice. W-12/J-D1 and the PE3 W-12/HMENU3 consumption audit use the proved
> exhaustiveness and aggregate densities, so they survive. BOX-2 remains
> open, now without the overclaim that it is merely a transcription of an
> already API-complete specification.”

**CONDITIONALITY:** the SPLITEQ aggregate (q−2)/(2q²(q+1)) vanishes at q = 2 — consistent with the note's own q = 2 remark “SPLITEQ empty at q = 2”.

**RESOLUTION TRACE:** dated annex, C7-F2. Supersedes clause (iv) and S4.1's “complete specification”.

**TEETH:** the aggregates are corollaries of the census-checked row densities; no separate battery row.

---

### EFF.W11.13  [acceptance-box]

**CANONICAL STATEMENT — the GRADE box as composed** (superseded in its grade by EFF.W11.40, retained for its clause-by-clause split):

> “**GRADE: PROVED at n = 2 ((i)–(iii) mathematics S2 + sealed battery S7
> + independent PARI leg per polynomial; (iv) = the proved spec display).
> The GENERAL W-11 (all degrees/orders) is a stated program (S4.3), NOT
> proved — BOX-1. Attempt 0/2.**”

**DERIVATION:** `[GRADE RECORD]` The clause-by-clause split is what the acceptance record then ratifies: (i′)–(iii) are theorem-grade; (iv′) is a target display; the general case is a program.

**CONDITIONALITY:** “Attempt 0/2” is `[SUPERSEDED]` — the note was ACCEPTED at 2/2 (EFF.W11.40). Everything else stands.

**RESOLUTION TRACE:** S1 tail → acceptance record.

**TEETH:** §7 of this specification.

---

### EFF.W11.14  [convention]

**CANONICAL STATEMENT:**

> “Work per center c̄ (the level-0 double-root menu: q centers, W-10 S2.1's
> recentering is a measure-preserving bijection per center — consumed, not
> re-proved). After recentering, (a₀′, a₁′) ∈ (πO)² =: C(1,1). Write
> C(a,b) = {(A₀,A₁) : v(A₀) ≥ a, v(A₁) ≥ b}; over O/π^N, #C(a,b) =
> q^(N−a)·q^(N−b).”

**DERIVATION:** `[IMPORTED + DEFINITIONAL]` The per-center decomposition is W-10's recentering bijection, consumed at pin 2e6fdd8/9506a55. The box-count formula is immediate.

**CONDITIONALITY:** q centers; the SEP rows sit at level 0 and carry no center factor (EFF.W11.09).

**RESOLUTION TRACE:** S2 opening; unchanged.

**TEETH:** W11-W10TIE.

---

### EFF.W11.15  [lemma]

**CANONICAL STATEMENT — S2.1, the node trichotomy:**

> “At a node C(2s+1, s+1) (s = 0 is the root; the invariant is proved in
> S2.3), let u = v(A₀), w = v(A₁). The lower hull of (0,u),(1,w),(2,0):
>
> * **u odd, w ≥ (u+1)/2** — one side, slope u/2, denominator e = 2, length
>   2, residual degree 1, letter res(A₀/π^u) ≠ 0: **RAM(u)**, decided. At
>   u = 1 (only possible at the root: refined nodes have u ≥ 3) this is
>   T(2,1,1) — THEOREM W-10 verbatim, consumed at pin 2e6fdd8/9506a55: count
>   per center (q−1)q^(2N−3), density (q−1)/q³. [machine: W11-W10TIE,
>   pointwise per polynomial against the SEALED w10_checks classifier.]
> * **w < u/2** — two sides, slopes w and u−w, each length 1, each carrying
>   a monic degree-1 factor (side of length one ⟹ a root in O, by the
>   factorization step at a one-point side — degree-1 Hensel): **2SIDED(w,
>   u−w)**, decided, σ = split, roots at valuations w < u−w.
> * **u = 2k even, w ≥ k** — one side, integer slope k, e = 1, length 2:
>   substitute x = π^k y and reduce: the residual quadratic R(y) = y² + c₁y
>   + c₀ over F_q, c₁ = digit_k(A₁) (zero iff w > k), c₀ = digit_2k(A₀) ≠ 0.
>   Hensel at the separable residual:
>   - R separable with two roots: **SPLITEQ(k)** (split; roots at equal
>     valuation k, distinct leading digits);
>   - R irreducible: **INERTDEEP(k)** (inert: f irreducible, unramified,
>     residual degree 2);
>   - R = (y − z̄)², z̄ ≠ 0: NOT decided — **REFINE** (S2.3).”

with its completeness argument:

> “Completeness: every (u,w) with u ≤ N−1 exact falls in exactly one bullet
> (u odd: w ≥ (u+1)/2 xor 2w < u; u even: w ≥ k xor 2w < u). The window
> cases u ≥ N are S2.4's tail. ∎(trichotomy)”

**DERIVATION:** `[PROVED]` One Newton-polygon read on the three-point grid {(0,u),(1,w),(2,0)}, plus Hensel at each decided leaf: degree-1 Hensel at a length-one side, separable-residual Hensel at the e = 1 side. The completeness dichotomy is the trivial xor on (u,w). Step justifications: the polygon read `computation`; the factorization steps `by classical Hensel` (S9's classical inputs); the RAM(1) count `by XREF X02` (W-10 at pin 2e6fdd8/9506a55).

**CONDITIONALITY:** the node invariant C(2s+1, s+1) is proved in S2.3, not assumed here (EFF.W11.20); u ≤ N−1 exact — the tail is EFF.W11.22.

**RESOLUTION TRACE:** S2.1; unchanged by r1, r2, and all four C7 corrections. C7-F4's sweep: “S2.1’s RAM classification, every count law, and σ = ram survive.”

**TEETH:** W11-W10TIE (pointwise, RAM(1) ⟺ the sealed w10 classifier's '211'); W11-CENSUS.

---

### EFF.W11.16  [table]

**CANONICAL STATEMENT — the residual census (the L3 leg at the deep rows), both characteristics:**

> “Pairs (c₁, c₀) ∈ F_q × F_q^*, counted by the type of R:”

`[TABLE]`

| type of R | char ≠ 2 locus | char 2 locus | COUNT (both) |
|---|---|---|---|
| separable split | c₁² − 4c₀ a nonzero square | c₁ ≠ 0, Tr(c₀/c₁²) = 0 | (q−1)(q−2)/2 |
| irreducible | c₁² − 4c₀ a nonsquare | c₁ ≠ 0, Tr(c₀/c₁²) = 1 | q(q−1)/2 |
| double root ≠ 0 | c₁ ≠ 0, c₀ = c₁²/4 | c₁ = 0, c₀ arbitrary ≠ 0 | q − 1 |

with its derivation and its interpretive claim:

> “(Char ≠ 2: per c₁, the split count is #{nonzero squares s ≠ c₁²} = (q−3)/2
> for c₁ ≠ 0 and (q−1)/2 for c₁ = 0, total (q−1)(q−2)/2; irreducible:
> (q−1)/2 per c₁, total q(q−1)/2; double: one c₀ per c₁ ≠ 0. Char 2: write
> c₀ = c₁²d, d ≠ 0: Artin–Schreier splits by Tr(d): (q/2 − 1) split, q/2
> irreducible, per c₁ ≠ 0; c₁ = 0 makes y² + c₀ the inseparable square
> (y − √c₀)². Row sums: q(q−1) both. ✓) THE LOCI DIFFER ACROSS
> CHARACTERISTICS; THE COUNTS DO NOT — J-D0's value-blindness surfacing at
> the branching level (the mechanism cited from pin 9387eb1; the counts here
> are proved directly, J-D0 is the frame). [machine: inside W11-CENSUS — the
> closed forms below consume exactly these three constants.]”

**DERIVATION:** `[PROVED — two disjoint classical censuses with equal totals]` Char ≠ 2 by square-class counting; char 2 by Artin–Schreier trace. The row sums agree at q(q−1) in both, and the ✓ is the note's own check. **This table is the counting-side face of J-D0's gauge-blindness** (EFF.W11.32) and the source of the three constants every deep row consumes.

**CONDITIONALITY:** (c₁, c₀) ∈ F_q × F_q^*; J-D0 is a **frame** here, not a premise — the counts are proved directly (NON-IMPORT N-8).

**RESOLUTION TRACE:** S2.1's residual census; unchanged.

**TEETH:** W11-CENSUS.

---

### EFF.W11.17  [lemma]

**CANONICAL STATEMENT — S2.2, σ-assignment and discriminant laws** `[ASSEMBLED: the four surviving bullets with the r2 PE2-F2 pin resolved in place; the fifth (disc = 0) bullet is EFF.W11.19]`:

> “disc f = a₁′² − 4a₀′ is recentering-invariant. For decided leaves:
> * RAM(h): Eisenstein after the slope-h/2 scaling — irreducible, totally
>   ramified e = 2, f = 1. v(disc): p odd: v(a₁′²) ≥ h+1 > h = v(4a₀′) ⟹
>   v(disc) = h (odd — tame). p = 2 mixed **[r2, PE2-F2: the {h+1, h+2}
>   spectrum below assumes the S1 pin v(2) = 1 (it uses v(4a₀′) = h+2);
>   over a ramified mixed-2 base v(disc) = min(2w, 2e₀+h) with e₀ = v(2)
>   (the min is always attained — 2w even, 2e₀+h odd), and the spectrum
>   grows. Counterexample (why the pin is needed): O = Z₂[√2] (e₀ = 2) —
>   a RAM(h) member with w = (h+3)/2 has v(disc) = h+3 ∉ {h+1, h+2}.
>   "Never tame" survives any e₀ (min(2w, 2e₀+h) ≥ h+1 ≥ 2 > 1), as do
>   clauses (i)–(iii) and every count/σ law (the S1 pin). …]**:
>   v(4a₀′) = h+2, v(a₁′²) = 2w ⟹
>   v(disc) = h+1 if w = (h+1)/2, else h+2 — NEVER the tame e−1 = 1: every
>   p = 2 member is wildly ramified (W-10 clause (iii) generalized to all h).
> * 2SIDED(w₁,w₂)/SPLIT-TAIL(w₁): split, roots in O at valuations w₁ (< w₂
>   or < u/2 ≥ N/2 resp.); v(disc) = 2w₁, both characteristics.
> * SPLITEQ(k): split, roots at valuation k, distinct digits; v(disc) = 2k
>   (residual disc ≠ 0; in char 2 separability forces c₁ ≠ 0 hence w = k).
> * INERTDEEP(k): inert — R irreducible ⟹ f irreducible over O with
>   unramified quadratic splitting field (e = 1, f = 2); v(disc) = 2k.”

**DERIVATION:** `[PROVED]` RAM by Eisenstein after slope scaling; the split rows by root valuations; INERTDEEP by residual irreducibility giving an unramified quadratic. The mixed-2 spectrum is a two-case valuation comparison, and the r2 pin makes its base hypothesis explicit with a genuine counterexample (O = Z₂[√2], v(disc) = h+3).

**⚠ “every p = 2 member is wildly ramified” IS SUPERSEDED BY C7-F4** (EFF.W11.18): in equal characteristic 2 with A₁ = 0 the member is purely inseparable — ramified and not tame, but not called wild.

**CONDITIONALITY:** the {h+1, h+2} spectrum requires v(2) = 1 (EFF.W11.06's pin). “Never tame” survives any e₀.

**RESOLUTION TRACE:** S2.2 bullets 1–4, with the r2 bracket; the wildness phrase superseded by C7-F4. C7-F4's sweep: “S2.2’s discriminant spectra survive as polynomial-discriminant statements, but the tame/wild comparison is applied only in the separable subcases.”

**TEETH:** W11-ORACLE (per-polynomial PARI (σ,e,f,v(disc))); W11-T-TAMEDISC (1,440 firings).

---

### EFF.W11.18  [lemma]

**CANONICAL STATEMENT — C7-F4, separable wildness and the inseparable case:**

> “In mixed characteristic with residue characteristic 2, every RAM(h)
> quadratic is separable, has ramification index e = 2, and is wildly
> ramified because the residue characteristic divides e.
>
> In equal characteristic 2 the derivative of the recentered polynomial
>
>   f(x) = x² + A₁x + A₀
>
> is f′ = A₁.
>
> * If A₁ ≠ 0, the RAM(h) extension is separable. It has e = 2 in residue
>   characteristic 2 and is therefore wildly ramified.
>
> * If A₁ = 0, then f = x² + A₀. In the RAM(h) row, v(A₀) = h is odd, so
>   A₀ cannot be a square because every square has even valuation.
>   Consequently f is irreducible and defines a degree-two purely
>   inseparable extension with e = 2. It is ramified and is not tame, but
>   it is not called “wildly ramified” here because the usual tame/wild
>   ramification dichotomy and different-exponent comparison are being
>   used only for finite separable extensions. The example x² + t lies in
>   exactly this case and has polynomial discriminant zero.
>
> Thus the uniform counting row RAM(h) legitimately contains three
> arithmetic subcases: mixed-characteristic separable wild, equal-
> characteristic separable wild, and equal-characteristic purely
> inseparable ramified. The count and σ = ram assignment are uniform across
> all three; only the terminology differs.
>
> The TAMEDISC statement is also henceforth scoped exactly as follows:
> the tooth fires once for every p = 2 RAM member in the disclosed
> mixed-characteristic PARI oracle rows — 1,440 such sampled members. It
> supplies no equal-characteristic evidence. The equal-characteristic
> conclusions above follow instead from f′ = A₁, the odd valuation of A₀,
> and e = 2.”

**DERIVATION:** `[PROVED — three lines]` f′ = A₁ in characteristic 2; A₁ = 0 makes f inseparable; v(A₀) = h odd makes A₀ a non-square (every square has even valuation), so x² + A₀ is irreducible; e = 2. The orchestrator re-checked: “C7-F4: the char-2 case split re-checked (f′ = A₁ in equal characteristic; v(A₀) = h odd makes A₀ a non-square, so A₁ = 0 gives the purely inseparable member; the 1,440 TAMEDISC sample figure is sol's read of the disclosed oracle rows)”.

**⚠ THE UNIFORMITY SURVIVES THE TERMINOLOGY SPLIT** — “The count and σ = ram assignment are uniform across all three; only the terminology differs.” This is the point: three genuinely different arithmetic phenomena share one count row, which is exactly W-11's J-D weight (EFF.W11.32).

**CONSUMER SWEEP (part of the correction):**

> “CONSUMER SWEEP. S2.1’s RAM classification, every count law, and σ = ram
> survive. S2.2’s discriminant spectra survive as polynomial-discriminant
> statements, but the tame/wild comparison is applied only in the separable
> subcases. S5’s uniformity claim survives because it concerns counts, not
> separability. BOX-4, P-6, P-7, and S10 already restrict PARI to mixed
> characteristic and remain correct under the explicit scope above.
> W-12/J-D1, hExhaust, the density totals, and all Lean consumers use only
> the unchanged counts and σ-partition. The acceptance phrase “wild p = 2
> included” is henceforth read as asserting the included separable wild
> members, alongside separately included purely inseparable ramified
> members.”

**CONDITIONALITY:** the TAMEDISC evidence is mixed-characteristic only; the equal-characteristic conclusions rest on the three-line argument, not on the machine.

**RESOLUTION TRACE:** dated annex, C7-F4. Supersedes every unqualified “every p = 2 RAM member is wild” in S2.2, S5, S7/S10, and the acceptance record.

**TEETH:** W11-T-TAMEDISC, now explicitly scoped to 1,440 mixed-characteristic sampled members.

---

### EFF.W11.19  [record]

**CANONICAL STATEMENT — the disc = 0 two-case statement (r1's F2 replacement):**

> “~~Degenerate perfect squares (disc = 0): never decided at any window
> (v(disc) = ∞ forces u = w = ∞ in-window) — measure zero, part of the
> undecided residue at every N.~~ **[r1, F2 — the struck side-claim is
> FALSE in equal characteristic 2, and its displayed mechanism was wrong
> even in mixed characteristic; the true two-case statement:]** Degenerate
> disc = 0 members (measure zero in both cases):
>   - MIXED characteristic: disc = 0 exactly ⟺ f is a perfect square, and
>     such f is indeed never decided at any window — but NOT via u = w = ∞:
>     the read runs the refine chain at finite visible (u, w) and exits at
>     the σ-undecided tail cell (u ≥ N, w > (N−1)/2), with w = v(2) +
>     v(root offset) possibly < N and visible. PE1 witness: (x+2)² over Z₂
>     at N = 8 classifies UNDECIDED with realized refine history (1,2,3),
>     all intermediate reads at finite (u, w).
>   - EQUAL characteristic 2: disc = a₁², so disc = 0 ⇎ perfect square, and
>     disc = 0 members CAN be decided. Witness: f = x² + t over F_q[[t]]
>     has disc ≡ 0 identically yet is DECIDED RAM(1) at every window N ≥ 2
>     (u = 1 odd, w = ∞; irreducible, e = 2 in the value-group sense —
>     inseparable; machine-confirmed by PE1's fresh classifier).”

**DERIVATION:** `[REPAIR — two witnesses]` The struck claim failed twice: its *mechanism* (u = w = ∞) was wrong even where its conclusion held, and its *conclusion* was false in equal characteristic 2 where disc = a₁² decouples from perfect-squareness. Both replacements carry an explicit witness: (x+2)² over Z₂ at N = 8 (mixed), x² + t over F_q[[t]] (equal). The second witness is exactly the purely inseparable member C7-F4 later isolates (EFF.W11.18).

**BLAST-RADIUS SWEEP (recorded by r1, part of the effective text):**

> “**[r1, F2 blast-radius sweep, recorded: grep over lean/,
> docs/, verification/ for consumers of the struck claim — patterns
> "never decided at any window", "u = w = ∞", "disc = 0 …
> undecided/never decided", plus every file citing both W-11 and an
> S2.2 — finds NO surface outside this bullet, the frozen PE1 report,
> and the byte-frozen runner's own bracket (the in-note S7/P-6 mentions
> describe that same mixed-only machine bracket and are true as machine
> records). No count or density law consumes the struck claim (x² + t is
> correctly counted in RAM(1) by note, runner, and PE1's fresh census
> alike; the count laws never reference disc). Zero blast radius on
> clauses (i)–(iii), as PE1 adjudicated.]**”

**CONDITIONALITY:** the machine bracket is mixed-characteristic only, and the note explains why 0 violations is the *correct* outcome there: “the runner takes poldisc of the EXACT canonical lift, so its "disc = 0" means exact perfect square, precisely the case where the claim is true; 0 violations is the correct outcome (W11-BOX-4)”.

**RESOLUTION TRACE:** S2.2 fifth bullet, struck and replaced by r1's F2.

**TEETH:** W11-ORACLE's `disc = 0 ⟹ window-undecided` bracket (mixed only, BOX-4).

---

### EFF.W11.20  [lemma]

**CANONICAL STATEMENT — S2.3, the refinement isomorphism:**

> “At the refine case (depth k, letter z̄ ∈ F_q^*), recenter by s = z·π^k (z
> a lift of z̄): A₁ ↦ A₁ + 2s, A₀ ↦ s² + A₁s + A₀. CLAIM: for each letter
> z̄, the refine locus L(z̄) maps isomorphically (affine, Haar-preserving)
> ONTO C(2k+1, k+1).
>
> Char ≠ 2: L(z̄) = {digit_k(A₁) = −2z̄, v(A₀) ≥ 2k, digit_2k(A₀) = z̄²},
> measure q^(−k−1)·q^(−2k−1). Image: digit_k drops to 0 (−2z̄ + 2z̄);
> digit_2k(A₀″) = z̄² − 2z̄² + z̄² = 0; the map is affine invertible on
> (πO)², measures match #C(2k+1,k+1) = q^(−(2k+1))·q^(−(k+1)) — bijective
> onto. Char 2 (equal or mixed): L(z̄) = {v(A₁) ≥ k+1, digit_2k(A₀) = z̄²},
> same measure; A₁ unchanged (+2s has v ≥ k+1 in mixed char 2, = 0 in equal
> char); digit_2k(A₀″) = z̄² + 0 + z̄² = 2z̄² ≡ 0 — same conclusion. In both
> cases the refined state is EXACTLY the node C(2k+1, k+1): the recursion is
> self-similar, the node invariant (lo0, lo1) = (2s+1, s+1) propagates, and
> each refinement step multiplies by q−1 letter branches of equal measure.
> ∎(S2.3) [machine: the closed-form predictor implements exactly this
> recursion — a census violation anywhere would break this paragraph.]”

**DERIVATION:** `[PROVED — two characteristic cases, same conclusion]` The recentering is an explicit affine map; both cases compute digit_2k(A₀″) = 0 and match measures against #C(2k+1, k+1). **This is the self-similarity that makes the whole note work**: it establishes the node invariant EFF.W11.15 assumes and produces the q−1 equal-measure letter branches EFF.W11.23's bracket sums.

Note the char-2 subtlety the proof handles explicitly: the mixed case has v(2s) ≥ k+1 so A₁'s digit is untouched, and the equal case has 2s = 0 outright — the two reasons differ, the conclusion is the same. This is also the only place v(2) enters, and it enters only as “v(2s) ≥ k+1, true for any v(2)” (EFF.W11.06's pin remark).

**CONDITIONALITY:** z̄ ∈ F_q^*; depth k.

**RESOLUTION TRACE:** S2.3; unchanged by every round and every C7 correction.

**TEETH:** the whole W11-CENSUS — “a census violation anywhere would break this paragraph”; the history-depth check (“max history depth = ⌊(N−1)/2⌋ on every row”).

---

### EFF.W11.21  [lemma]

**CANONICAL STATEMENT — S2.4, the per-node exhaustiveness identity** `[ASSEMBLED: the display with r1's F1 corrected leg values in place, and the struck values recorded]`:

> “Node mass μ_s = q^(−(3s+2)) (per center, normalized). Summing S2.1's cases
> over u ≥ 2s+1 in the limit N → ∞:
>
>     RAM leg      Σ_{k≥s+1} (1−1/q)·q^(−(3k−1))       = q·X
>     2SIDED leg   Σ_{w≥s+1} Σ_{u≥2w+1} (1−1/q)²q^(−u−w) = X/q
>     e=1 leg      Σ_{k≥s+1} q(q−1)·q^(−3k−2)           = X
>       (all q(q−1) residual pairs: split + irreducible + refine)
>
> with X = (1−1/q)·q^(−3(s+1))/(1−q^(−3)) = q^(−3s−1)/(q²+q+1); total
> q·X + X/q + X = ((q²+q+1)/q)·X = q^(−3s−2) = μ_s exactly. ∎(nothing
> leaks at any node)”

with r1's F1 correction record, quoted in full:

> “**[r1, F1 — strike-and-replace of the display's
> evaluations: the r0 legs read q²·X, X, q·X with total (q²+q+1)·X = μ_s;
> every evaluated leg carried a spurious factor q, and the struck total
> equation is FALSE — (q²+q+1)·X = q^(−3s−1) = q·μ_s. The three SUMMANDS
> were and are correct; the leg values above are PE1's re-derived TRUE
> evaluations. Numerical check of the corrected display at q = 2, s = 0:
> X = 1/14, μ₀ = 1/4, and the legs give 1/7 + 1/28 + 1/14 = 1/4 = μ₀ ✓
> (the struck display gave 2/7 + 1/14 + 1/7 = 1/2 = 2μ₀ ✗). The
> conclusion — nothing leaks at any node — is TRUE, re-proved
> independently at PE1, and the finite-window per-key counts the machine
> census checks were never affected.]**”

**DERIVATION:** `[PROVED — three geometric sums, one identity]` The three legs are the three S2.1 bullets summed over the node's parameter range; the e = 1 leg absorbs all q(q−1) residual pairs (split + irreducible + refine), which is why the refine branch does not leak. The total collapses because ((q²+q+1)/q)·q^(−3s−1)/(q²+q+1) = q^(−3s−2) = μ_s.

**⚠ THIS IS THE NOTE'S ONE ARITHMETIC ERROR, CAUGHT AND FIXED.** The r0 evaluations were each off by a factor q and the total was off by q. The compiler re-checked the numerical witness independently: at q = 2, s = 0, X = (1/2)·2^(−3)/(1−1/8) = (1/16)/(7/8) = 1/14 ✓; μ₀ = 2^(−2) = 1/4 ✓; q·X = 2/14 = 1/7, X/q = 1/28, X = 1/14, and 1/7 + 1/28 + 1/14 = 4/28 + 1/28 + 2/28 = 7/28 = 1/4 = μ₀ ✓. The struck values give 2/7 + 1/14 + 1/7 = 4/14 + 1/14 + 2/14 = 7/14 = 1/2 = 2μ₀ ✗. Both of r1's arithmetic claims confirm.

**CONDITIONALITY:** limit N → ∞ for the display; the finite-window version is EFF.W11.22.

**RESOLUTION TRACE:** S2.4 display, struck and replaced by r1's F1.

**TEETH:** W11-CENSUS (the finite-window per-key counts — explicitly stated to have been unaffected by the error).

---

### EFF.W11.22  [scope-record]

**CANONICAL STATEMENT — the finite window and the tail** `[ASSEMBLED: the S2.4 paragraph with r1's F6 replacement in place]`:

> “At finite window N (per node instance): every u ≤ N−1 case is fully
> observable (all pinned digits sit at positions ≤ N−1); the tail u ≥ N
> splits into SPLIT-TAIL(w) (w ≤ (N−1)/2: any lift has u > 2w — σ = split
> certified, shape truncated) and the σ-UNDECIDED residue {A₀ ≡ 0 mod π^N,
> w > (N−1)/2 or A₁ ≡ 0} — genuinely ambiguous ~~(contains split, inert AND
> ram lifts)~~ **[r1, F6 — scoped to set level: as a SET the residue
> contains split, inert AND ram lifts; per MEMBER, split and inert lifts
> BOTH always exist (so σ-undecidedness itself is airtight member by
> member), but a ram lift can be ABSENT — a char-2 member with exact
> w = N/2 has only split and inert lifts, its residual c₁ ≠ 0 blocking the
> refine a ram lift would need]**. [machine: W11-CENSUS checks every key
> exactly; W11-EXHAUST the σ-sums.]”

**DERIVATION:** `[REPAIR — quantifier scoping]` The struck parenthetical read as a per-member claim and is false in that reading; the replacement separates set level from member level and, crucially, checks that the *load-bearing* direction survives: σ-undecidedness needs two σ-values per member, and split + inert always both exist. The blocking mechanism for the third is given explicitly (a char-2 member at exact w = N/2 has residual c₁ ≠ 0, so the refine a ram lift needs is unavailable).

**CONDITIONALITY:** per node instance; the SPLIT-TAIL leg is re-typed as a boundary cell by C7-F1 (EFF.W11.08), whose sweep confirms: “S2.4’s finite-window partition survives with SPLIT-TAIL understood as a boundary cell.”

**RESOLUTION TRACE:** S2.4 tail, struck and replaced by r1's F6.

**TEETH:** W11-CENSUS, W11-EXHAUST.

---

### EFF.W11.23  [lemma]

**CANONICAL STATEMENT — S2.5, the instance bracket:**

> “**The instance bracket.** A node at state s is reached by histories
> (k₁ < ⋯ < k_t = s); by S2.3 each history contributes (q−1)^t equal-measure
> instances, and Σ_t C(s−1, t−1)(q−1)^t = (q−1)·q^(s−1). Hence for any leaf
> datum read at u (or k) from all nodes below it, the total instance weight
> is Σ_{s<k} instances(s) = 1 + Σ_{s=1}^{k−1}(q−1)q^(s−1) = q^(k−1) — THE
> BRACKET.”

**DERIVATION:** `[PROVED — two binomial sums]` The first is the binomial theorem: Σ_t C(s−1,t−1)(q−1)^t = (q−1)Σ_{t−1} C(s−1,t−1)(q−1)^(t−1) = (q−1)q^(s−1). The second telescopes: 1 + (q−1)(1 + q + ⋯ + q^(k−2)) = 1 + (q−1)(q^(k−1)−1)/(q−1) = q^(k−1). Both rest on EFF.W11.20's “each refinement step multiplies by q−1 letter branches of equal measure”.

**⚠ THE BRACKET q^(k−1) IS THE SINGLE MOST REUSED QUANTITY IN THE NOTE** — every clause-(ii) law is (one-node count) × q^(k−1) (EFF.W11.09), the drainage sum uses it (EFF.W11.26), and C7-F3 re-derives the boundary count with it (EFF.W11.25).

**CONDITIONALITY:** none beyond the S2.3 recursion.

**RESOLUTION TRACE:** S2.5; unchanged.

**TEETH:** W11-CENSUS's history-depth check; P-2's realized depth-3 histories at N = 8.

---

### EFF.W11.24  [lemma]

**CANONICAL STATEMENT — the window laws and the (superseded) no-truncation sentence:**

> “Every window law in clause (ii) is (leaf count from one node
> instance) × q^(k−1), e.g. RAM(2k−1): (q−1)q^(N−1−(2k−1))·q^(N−k)·q^(k−1)
> = (q−1)q^(2N−2k−1); INERTDEEP(k): (q(q−1)/2)·q^(N−2k−1)·q^(N−k−1)·q^(k−1)
> = ((q−1)/2)q^(2N−2k−2); SPLIT-TAIL(w): (q−1)q^(N−1−w)·q^(w−1) =
> (q−1)q^(N−2) (w-independent). NOTE the counts are EXACT window counts equal
> to (limit density)·q^(2N) — no truncation error on visible rows.”

**DERIVATION:** `[PROVED]` Each is EFF.W11.23's bracket applied to the corresponding S2.1 leaf count, with EFF.W11.16's residual constant where the leaf is an e = 1 row.

**⚠ THE FINAL SENTENCE IS SUPERSEDED BY C7-F3** (EFF.W11.25): it holds for the six genuine rows but not for SPLIT-TAIL, which is a moving boundary cell with normalized mass (q−1)q^(−N−1) → 0 and therefore no fixed limit density to multiply.

**CONDITIONALITY:** as EFF.W11.09.

**RESOLUTION TRACE:** S2.5; the closing sentence superseded by C7-F3.

**TEETH:** W11-CENSUS; the raw w-independence display in S10's P-2.

---

### EFF.W11.25  [lemma]

**CANONICAL STATEMENT — C7-F3, exact counts versus boundary mass:**

> “For SEP and each fixed genuine shape row RAM(h), 2SIDED(w₁,w₂),
> SPLITEQ(k), and INERTDEEP(k), once the row is visible at window N, its
> whole-space count (the displayed per-center count multiplied by q
> centers) is EXACTLY
>
>   (that row’s fixed limit density) · q^(2N).
>
> There is no truncation error for those genuine rows.
>
> SPLIT-TAIL_N(w) is different because it is a moving window-boundary cell,
> not a fixed limiting row. For one center, the number of coefficients with
> v(A₁) = w is (q−1)q^(N−w−1), and the history bracket below w is q^(w−1);
> therefore
>
>   #SPLIT-TAIL_N(w) per center
>     = (q−1)q^(N−w−1)q^(w−1)
>     = (q−1)q^(N−2).
>
> After multiplying by q centers its whole-space count and normalized mass
> are
>
>   q(q−1)q^(N−2),             (q−1)q^(−N−1),
>
> respectively. The latter tends to zero for fixed q, so the boundary family
> has no positive fixed-row limit density. At q = 2, N = 4, w = 1 this gives
> 8/2^8 = 1/32, exactly as required.”

**DERIVATION:** `[PROVED — one bracket computation]` (q−1)q^(N−w−1)·q^(w−1) = (q−1)q^(N−2) per center; × q centers = q(q−1)q^(N−2); normalized by q^(2N) gives (q−1)q^(N−1)/q^(2N) = (q−1)q^(−N−1) → 0. Compile-time check of the stated witness: at q = 2, N = 4, w = 1 the per-center count is (2−1)·2^(4−2) = 4, whole-space 2·4 = 8, and 8/2^8 = 8/256 = 1/32 ✓; the formula (q−1)q^(−N−1) = 1·2^(−5) = 1/32 ✓. Both agree. The orchestrator's own re-derivation is recorded: “C7-F3: the boundary count re-derived ((q−1)q^{N−w−1}·q^{w−1} = (q−1)q^{N−2} per center, whole-space normalized mass (q−1)q^{−N−1} → 0, and 8/2⁸ = 1/32 at the (2,4,1) witness)”.

**CONSUMER SWEEP (part of the correction):**

> “CONSUMER SWEEP. All clause-(ii) count formulas remain unchanged with
> their stated per-center convention. S2.5’s finite telescope still uses
> the nonzero tail count and therefore still proves split-decided =
> inert-decided at every window. Clause (iii)’s partition and q^N drainage
> law are unchanged. S4.2’s shape-undecided correction retains this same
> boundary mass. The S7/S10 census values are unchanged; only the false
> identification of the boundary count with a fixed limit-density multiple
> is removed.”

**CONDITIONALITY:** “once the row is visible at window N” for the genuine rows.

**RESOLUTION TRACE:** dated annex, C7-F3. Supersedes S2.5's closing no-truncation sentence.

**TEETH:** W11-CENSUS (values unchanged); the S7 smoke table's (Zp,2,4) SPLIT-TAIL(1) = 8.

---

### EFF.W11.26  [lemma]

**CANONICAL STATEMENT — S2.5, the drainage law:**

> “**The drainage law.** σ-undecided per node instance = q^(⌈(N−1)/2⌉)
> (A₀ ≡ 0; A₁ free above position ⌊(N−1)/2⌋, including 0). Reachable states
> s = 0, …, ⌊(N−1)/2⌋; summing the bracket: undecided per center =
> q^(⌈(N−1)/2⌉)·q^(⌊(N−1)/2⌋) = q^(N−1); × q centers = **q^N EXACTLY**.
> Normalized: q^(−N) → 0. ∎(hExhaust at n = 2, exact rate)”

**DERIVATION:** `[PROVED — one ceiling/floor identity]` The per-node-instance count is q^(⌈(N−1)/2⌉) (the free A₁ digits above position ⌊(N−1)/2⌋, with A₀ ≡ 0 forced). Summing EFF.W11.23's bracket over reachable states s = 0, …, ⌊(N−1)/2⌋ contributes q^(⌊(N−1)/2⌋). The product uses ⌈(N−1)/2⌉ + ⌊(N−1)/2⌋ = N−1 exactly (true for both parities of N). × q centers gives q^N.

**⚠ THIS IS THE hExhaust INSTANCE.** Not o(1) — the exact rate q^(−N). It is what makes the Lean capstone's `hExhaust` hypothesis TRUE at n = 2 as mathematics (EFF.W11.30), and it is the unit that survives every correction untouched.

**CONDITIONALITY:** the σ-convention; the shape-truncated convention's law is in EFF.W11.30 and also drains.

**RESOLUTION TRACE:** S2.5; unchanged by r1, r2, and all four C7 corrections.

**TEETH:** W11-EXHAUST (“undecided = q^N EXACTLY on all 30 rows”); W11-T-DRAIN (30 firings).

---

### EFF.W11.27  [lemma]

**CANONICAL STATEMENT — limit densities, the finite telescope, and the sum** `[ASSEMBLED: the S2.5 paragraph with r2's PE2-F1 telescope bracket in place]`:

> “**Limit densities and the sum.** Summing each family over histories
> (bracket) and parameters: RAM(h): (q−1)/q^(h+2) per center, total ram =
> Σ_{h odd}(q−1)q^(−h−2)·q = 1/(q+1). Split-deep = 2SIDED + SPLITEQ (+ the
> tail, absorbed as N → ∞): per node q/(2(q²+q+1)) of the node mass — equal
> to INERTDEEP's fraction **[r2, PE2-F1 — the equal limit fractions prove
> the LIMIT equality only; at finite N the tail is load-bearing, and the
> every-window claim rests on the finite telescoping identity (supplied by
> the PE2 report's F1, `W11_passPE2_report.md` @ 473a993; transcribed and
> re-verified): per node instance, per w ∈ {s+1, …, ⌊(N−1)/2⌋}, the split
> legs at A₁-valuation w telescope,
> Σ_{u=2w+1}^{N−1} (q−1)q^(N−1−u) + 1_tail = q^(N−1−2w) (geometric sum
> q^(N−1−2w) − 1, plus the tail cell's 1), so 2SIDED(w,·) + TAIL(w) =
> (q−1)·q^(N−1−w)·q^(N−1−2w); adding SPLITEQ(w) =
> ((q−1)(q−2)/2)·q^(N−1−w)·q^(N−1−2w) gives the factor (q−1)(1 + (q−2)/2)
> = q(q−1)/2 = INERTDEEP(w)'s census constant — equality per node
> instance, per w, at every window, both characteristics; the k-ranges
> agree (2w < N ⟺ w ≤ ⌊(N−1)/2⌋ = the SPLITEQ/INERTDEEP range). Checked
> at q = 2: the telescope at N = 6, w = 1 is 4+2+1 + 1_tail = 8 = 2³; the
> factor is 1·(1+0) = 1 = q(q−1)/2 (SPLITEQ empty at q = 2), matching the
> S7 smoke table's (Zp,2,4) 2SIDED(1,2) + SPLIT-TAIL(1) = 8 + 8 = 16 =
> INERTDEEP(1)]**, whence **split-decided = inert-decided at every
> window** (with SEP-SPLIT = SEP-INERT = (q²−q)/2·q^(2N−2) at level 0);
> totals: split = inert = (q−1)/(2q) + 1/(2q(q+1)) = q/(2(q+1)). Sum:
> 2·q/(2(q+1)) + 1/(q+1) = 1. ∎(i)(ii)(iii)”

**DERIVATION:** `[PROVED — a limit argument PLUS a separate finite identity]` This is the note's most carefully repaired unit, and the repair is a genuine strengthening: the r0 argument proved only the LIMIT equality from equal limit fractions, while the every-window claim in clause (iii) needs a finite identity. r2 supplies it — a geometric telescope over u whose deficit is exactly filled by the tail cell's single element, after which the split census constant (q−1)(1 + (q−2)/2) = q(q−1)/2 coincides with INERTDEEP's constant from EFF.W11.16. Compile-time check of the arithmetic: (q−1)(1 + (q−2)/2) = (q−1)·(2 + q − 2)/2 = q(q−1)/2 ✓, which is exactly the “irreducible” row of EFF.W11.16 ✓. The q = 2, N = 6, w = 1 numerical check: Σ_{u=3}^{5} 1·2^(5−u) = 4+2+1 = 7, plus 1 = 8 = 2^(6−1−2) = 2³ ✓.

The final totals: split = SEP-SPLIT + Σ2SIDED + ΣSPLITEQ = (q−1)/(2q) + 1/(q²(q+1)) + (q−2)/(2q²(q+1)); C7-F2 (EFF.W11.12) confirms Σ2SIDED + ΣSPLITEQ = 1/(2q(q+1)), giving (q−1)/(2q) + 1/(2q(q+1)) = ((q−1)(q+1) + 1)/(2q(q+1)) = q²/(2q(q+1)) = q/(2(q+1)) ✓. And 2·q/(2(q+1)) + 1/(q+1) = q/(q+1) + 1/(q+1) = 1 ✓.

**⚠ THE TAIL IS LOAD-BEARING AT FINITE N.** C7-F3's sweep restates it: “S2.5’s finite telescope still uses the nonzero tail count and therefore still proves split-decided = inert-decided at every window.” This is why C7-F1 re-types SPLIT-TAIL rather than deleting it.

**CONDITIONALITY:** both characteristics; the k-ranges agreement is checked explicitly.

**RESOLUTION TRACE:** S2.5, with r2's PE2-F1 bracket. The telescope identity is **imported from the PE2 report** (`W11_passPE2_report.md` @ 473a993) and transcribed — an unusual provenance for a load-bearing step, and the note flags it as “transcribed and re-verified”.

**TEETH:** W11-EXHAUST (“split-decided = inert-decided EXACTLY on all 30 rows”); the S7 smoke table.

---

### EFF.W11.28  [fence]

**CANONICAL STATEMENT — S3, NOT CONSUMED:** reproduced in full as NON-IMPORTS N-1, N-2, N-3 (§2 above).

**DERIVATION:** `[FENCE]` Perimeter hygiene: three accepted suppliers are named and declined, each with the reason it is not needed at n = 2 and the note (JC, JB) of where it *would* be needed — the general program S4.3.

**CONDITIONALITY:** all three become live obligations at general n (EFF.W11.31).

**RESOLUTION TRACE:** S3; unchanged. Independently corroborated in `spec/HYPOTHESIS_LEDGER.md`, whose weld-face audit records for the JB row “No capstone-path consumer. W11 L391–393 (re-v…” (RX-2).

**TEETH:** no battery row — this is a displayed perimeter, not a check.

---

### EFF.W11.29  [scope-record]

**CANONICAL STATEMENT — S4.1, the typeOf-keyed spec:**

> “Lean anchors (`OM/RealInstanceV2.lean`, `OM/OMCountV2.lean`): `density m σ
> q' := Σ_{T ∈ omMenu m σ} omCount T q'`; at R1 the menu is the order-0
> slice, `omMenu_order0 : omMenu n σ = sepShapesOf n σ`. The proved n = 2
> spec: `omMenu 2 split` must grow to {SEP-SPLIT} ∪ {2SIDED(w₁,w₂)} ∪
> {SPLITEQ(k)}, `omMenu 2 inert` to {SEP-INERT} ∪ {INERTDEEP(k)}, `omMenu 2
> ram` to {RAM(h) : h odd} — typeOf-keyed by the shape data of table (i) —
> with `omCount` the S2.5 laws. These are countable menus with geometric
> density tails: the Lean transcription needs either parametrized shape
> families or a per-window finite menu (the window-N visible menu is finite:
> h ≤ N−1, k ≤ (N−1)/2, w₁+w₂ ≤ N−1 — the L5fix menu-finiteness partial's
> shape at this slice). Growing it is Phase-B CODE, not open mathematics —
> at n = 2 the mathematics is now closed (this note).”

**DERIVATION:** `[SPEC DISPLAY]` The three target menus are exactly C7-F2's M_split, M_inert, M_ram (EFF.W11.12). The Lean anchors are verified at compile time: `omMenu_order0` and `sepShapesOf` both exist in `lean/LeanUrat/OM/OMCountV2.lean` and `OM/RealInstanceV2.lean` (XREFs L03, L04); `omCount` and `omMenu` likewise (L05, L06).

**⚠ RE-SCOPED BY C7-F2.** Its own sweep: “S4.1 is now a mathematical target rather than a claim of immediate transcription into the present API.” C7-F2 diagnoses precisely the sentence above that hedges without choosing: “S4.1 acknowledges “either parametrized shape families or a per-window finite menu,” but chooses neither. BOX-2 discloses missing code; it does not resolve the mismatch between an infinite type-indexed family and the displayed bounded, window-free Lean interface.” And it rules one branch out: “A per-window finite menu is not an implementation of the current interface unless N is added to that interface.”

**CONDITIONALITY:** BOX-2 open; the API design choice (a) or (b) is Phase-B work and is not made here.

**RESOLUTION TRACE:** S4.1 → re-scoped by C7-F2.

**TEETH:** none in this note's battery — the Lean side is untested here (BOX-3).

---

### EFF.W11.30  [record]

**CANONICAL STATEMENT — S4.2, the capstone tie** `[ASSEMBLED: with r1's F3 strike-and-replace in place]`:

> “The machine-checked order-0 value (`gate3_inert_q2`): decided order-0
> inert density = (q−1)/(2q) = 1/4 at q = 2. THIS note's deep-inert tail:
> Σ_k (q−1)/(2q^(2k+1))~~·q~~ = 1/(2q(q+1)) = 1/12 at q = 2 **[r1, F3: the
> summand is already the WHOLE-SPACE density (table (i)'s INERTDEEP(k)
> row), so the struck ·q double-applied the center factor — with it the
> left side would be 1/(2(q+1)) = 1/6 at q = 2; the RHS 1/(2q(q+1)) = 1/12
> and the capstone tie below are correct and stand]**. Full inert density
> = 1/4 + 1/12 = 1/3 = q/(2(q+1)) at q = 2. The capstone's honest
> conditionality ("the certified value is the DECIDED density; the
> full-density tie sits behind hExhaust") is exactly this displayed gap, and
> at n = 2 the gap is now priced: the bracket width is q^(−N) exactly
> (clause (iii)), so `montes_unconditional_exhaustive`'s bracket-uniqueness
> conclusion has its hypothesis TRUE at n = 2 as mathematics. Convention
> note: if the Lean `undecidedCount` unfolds to the SHAPE-truncated
> convention (SPLIT-TAIL counted undecided because its type parameters are
> unread), the drainage law becomes q^N + q·⌊(N−1)/2⌋(q−1)q^(N−2) — still
> exact, still O(N·q^(−N)) normalized → 0: hExhaust holds under EITHER
> convention; the term-level Lean tie is Phase-B (BOX-3).”

**DERIVATION:** `[COMPUTATION + the capstone tie]` The inert aggregate is EFF.W11.12's Σ INERTDEEP = 1/(2q(q+1)); at q = 2 that is 1/(2·2·3) = 1/12 ✓. Adding gate3_inert_q2's 1/4 gives 1/3, and q/(2(q+1)) at q = 2 is 2/6 = 1/3 ✓.

The r1 F3 correction is a center-factor bookkeeping fix: the table's INERTDEEP(k) density is already whole-space, so multiplying by q double-counted. The struck value 1/6 would have broken the tie (1/4 + 1/6 = 5/12 ≠ 1/3).

The shape-truncated convention's law is EFF.W11.25's boundary count summed over w: q·⌊(N−1)/2⌋·(q−1)q^(N−2) added to q^N, normalized O(N·q^(−N)) → 0.

**⚠ THIS IS THE R_σ(q) → LEAN-GATE CONSUMPTION EDGE, AND IT IS VERIFIED.** Compile-time check (XREF L01): `lean/LeanUrat/OM/OMCountV2.lean` line 646 reads exactly

```
theorem gate3_inert_q2 : omCount (sepShape 2 lam2) 2 = 1 / 4 := by
```

Moreover the underlying Lean closed form matches W-11's SEP-INERT row **as a rational function of q**, not just at q = 2. `omCount_sepShape_eval_poly` reduces `omCount (sepShape 2 lam2) q` to `availPoly 2` evaluated at q, times q^(−2); and `availPoly_two_eval` states `(availPoly 2).eval x = (x ^ 2 - x) / 2`. So the Lean inert order-0 value is ((q²−q)/2)·q^(−2) = (q−1)/(2q) — **identically W-11's SEP-INERT limit density**. The second Lean gate confirms it at another point: `gate3_inert_q3 : omCount (sepShape 2 lam2) 3 = 1 / 3` and (3−1)/(2·3) = 1/3 ✓ (XREF L07 — a corroborating instance the note does not cite; compiler observation).

**The SPLIT half of the same identification does NOT check out** — see OPEN-CALL 1.

**CONDITIONALITY:** the “term-level Lean tie is Phase-B (BOX-3)”; which convention `realM2.undecidedCount` unfolds to is deferred, and both inputs are proved.

**RESOLUTION TRACE:** S4.2, with r1's F3 strike; the INERTDEEP aggregate re-derived by C7-F2, whose sweep confirms “S4.2’s q = 2 capstone computation consumes the aggregate INERTDEEP value 1/(2q(q+1)) and survives verbatim.”

**TEETH:** no W-11 battery row covers the Lean side; the arithmetic is checked by W11-CENSUS on the INERTDEEP rows.

---

### EFF.W11.31  [open-obligation]

**CANONICAL STATEMENT — S4.3, the general-n hExhaust program:**

> “For general degree n: (P1) the node system = the classifier's
> recenter/rescale states, one per (level, refinement) datum; (P2) the
> per-node exhaustiveness identity (S2.4's analogue): the residual censuses
> S_λ(q) over each K_j sum with the lattice q-powers to the node mass —
> OWED: the universal census polynomials at g ≥ 2 (classical), the JA-GRID/
> JB-VTX position faces at their accepted grades incl. JB row-12's open
> membership residue, and the JC no-cancellation warrant at composite stages
> (the two GRTJC clauses named in S3); (P3) the drainage bound: undecided at
> window N ⊆ {some level's residual datum still degenerate at all read
> depths ≤ N} with per-refinement mass ratio ≤ c(q) < 1 uniformly — at
> n = 2, c = q^(−3)·(q−1) per depth step (S2.3–S2.5); the general claim is
> the same geometric mechanism per tower branch, made uniform over the
> finite window-visible menu (L5fix finiteness). None of (P1)–(P3) is proved
> here beyond n = 2 — this is the program, BOX-1.”

**DERIVATION:** `[PROGRAM — three named obligations with named owed inputs]` (P1) generalizes EFF.W11.20's node system; (P2) generalizes EFF.W11.21 and is where the three NON-IMPORTS of §2 become live; (P3) generalizes EFF.W11.26, with the n = 2 contraction constant given explicitly as c = q^(−3)(q−1) per depth step.

**CONDITIONALITY:** none of it is proved. Carried downstream as ledger row HYP.146 (RX-1): “`W11-BOX-1` … CONSUMED BY: any W-11 use above n=2; its named owed inputs are HYP.21 (JB row 12), HYP.20 (JC warrant), and the drainage rows HYP.27/HYP.30.”

**RESOLUTION TRACE:** S4.3; unchanged.

**TEETH:** none — a program carries no battery row.

---

### EFF.W11.32  [scope-record]

**CANONICAL STATEMENT — S5, uniformity content** `[ASSEMBLED: with r1's F4 and r2's PE2-F2 strikes in place]`:

> “Every count in this note — all seven families, all windows, the drainage
> law — is ONE expression in q across mixed/equal characteristic and
> tame/wild p. The wild rows are genuinely wild (S2.2: at p = 2 ~~every RAM
> member has v(disc) ∈ {h+1, h+2}~~ **[r1, F4 — the "mixed" fence S2.2
> carries and this sentence dropped, restored:] MIXED every RAM member has
> v(disc) ∈ {h+1, h+2}, while in EQUAL characteristic 2 disc = A₁² gives
> v(disc) = 2w ∈ {h+1, h+3, h+5, …} ∪ {∞} (x² + t realizes ∞)** **[r2,
> PE2-F2: MIXED here = the S1 pin, v(2) = 1; a ramified mixed-2 base
> realizes v(disc) = min(2w, 2e₀+h) ∉ {h+1, h+2} (O = Z₂[√2],
> w = (h+3)/2 ⟹ v(disc) = h+3 — the S2.2 pin)]**, never
> tame — every value ≥ 2 > e−1 = 1, both cases; the battery's TAMEDISC tooth
> fires once per member), and the char-2 residual loci are Artin–Schreier
> where the char-≠2 loci are square-classes (S2.1's table) — DIFFERENT value
> geography, SAME counts. This is J-D0's gauge-blindness realized on an
> entire menu rather than one stratum, and it is the counting-side face of
> HUMAN_PROOF §0's separator: the unramified total q/(q+1) (= split + inert
> here, proved) is the uniform volume; ∫|disc| is not uniform because it
> prices the letters (v(disc) = h, 2k, 2w₁ — letter-adjacent data), which
> the counts never consume.”

**DERIVATION:** `[SCOPE RECORD — the note's thesis]` The uniformity claim is the reason W-11 “carries J-D weight”: two genuinely different value geographies (square-classes vs Artin–Schreier, EFF.W11.16) produce identical counts, and the separator statement identifies exactly which functional is uniform (the unramified volume q/(q+1)) and which is not (∫|disc|, because it prices the letters).

**⚠ TWO SCOPINGS APPLY.** “all seven families” reads as six shape families plus one boundary family (C7-F1). “genuinely wild” reads with C7-F4's case split — and C7-F4's sweep confirms the *uniformity claim itself* is untouched: “S5’s uniformity claim survives because it concerns counts, not separability.”

**CONDITIONALITY:** the MIXED spectrum needs v(2) = 1; “never tame” does not.

**RESOLUTION TRACE:** S5, with r1's F4 restoration of the dropped “mixed” fence and r2's PE2-F2 base pin.

**TEETH:** W11-T-TAMEDISC; W11-CENSUS across both characteristics.

---

### EFF.W11.33  [fence]

**CANONICAL STATEMENT — S6, the seven honest boxes:**

> “* **W11-BOX-1 (n = 2 only).** The general W-11 — the menu tie at all
>   degrees and orders — is NOT proved: S4.3 is a program with named owed
>   inputs (S_λ(q) censuses, JB row-12 residue, JC warrant, uniform
>   drainage). Nothing at n ≥ 3 is claimed. W10-BOX-1 (shape-generic count
>   equality) also stands untouched.
> * **W11-BOX-2 (the Lean menu is not grown here).** No Lean code is written
>   or changed; `omMenu` remains the order-0 slice at HEAD. Clause (iv) is
>   the proved SPEC (what Phase-B must transcribe), not the transcription.
>   The `DecidedOmCountTie` genre now has its complete n = 2 target table.
> * **W11-BOX-3 (classifier reimplementation).** The battery's recursive
>   classifier is a convention-faithful reimplementation (W10-BOX-3
>   inherited); the engine tie is carried by W11-TOWER (frozen-roster
>   realized (2,h,1) levels incl. h = 3 wild) + the pointwise W11-W10TIE
>   against W-10's SEALED instrument + the accepted JB-VTX face. The Lean
>   evaluator tie remains order-0.
> * **W11-BOX-4 (oracle coverage).** PARI is mixed-characteristic only;
>   eq-char rows are SAME-class (disclosed in the runner; W10-BOX-4
>   inherited verbatim, incl. no mixed-char prime-power rows).
> * **W11-BOX-5 (σ-undecided vs shape-undecided).** The exact q^(−N) law is
>   for the σ-convention; the shape-truncated convention adds the SPLIT-TAIL
>   boundary family (exact law displayed in S4.2, still drains). Which
>   convention `realM2.undecidedCount` unfolds to is a Lean-term question
>   deferred to Phase-B; BOTH mathematical inputs are proved.
> * **W11-BOX-6 (density-chain consumption).** That these counts are what
>   L2core → L6M4 → U-DENS consume is the standing assembly identification
>   (W-10's H-2), consumed not re-proved.
> * **W11-BOX-7 (no per-row FE claim).** The proved split = inert symmetry
>   (every window, exact) is displayed as structure; its relation to the
>   tame functional equation / palindromy (`htameFE`) is NOT claimed — no
>   clause of this note discharges or weakens the htameFE hypothesis.”

**DERIVATION:** `[FENCE]` BOX-1 ↔ EFF.W11.31 (ledger HYP.146); BOX-2 ↔ EFF.W11.12/.29; BOX-3 ↔ the battery's provenance (EFF.W11.34); BOX-4 ↔ EFF.W11.19's mixed-only bracket; BOX-5 ↔ EFF.W11.26/.30's two conventions; BOX-6 ↔ the standing assembly identification; BOX-7 ↔ NON-IMPORT N-5. **BOX-2's phrase “Clause (iv) is the proved SPEC (what Phase-B must transcribe)” is re-scoped by C7-F2**, whose sweep says BOX-2 “remains open, now without the overclaim that it is merely a transcription of an already API-complete specification.” **BOX-5 is explicitly preserved verbatim by C7-F1**: “S4.2 and BOX-5 retain their two undecided conventions verbatim”.

**CONDITIONALITY:** these are the note's displayed stopping points, re-displayed at acceptance (“at its displayed boxes and conditionality”).

**RESOLUTION TRACE:** S6; BOX-2's transcription phrasing re-scoped by C7-F2.

**TEETH:** BOX-3's engine tie is carried by W11-TOWER + W11-W10TIE; the rest are fences.

---

### EFF.W11.34  [battery-frame]

**CANONICAL STATEMENT — S7, the sealed battery:**

> “**Runner:** `verification/openmath/w11_checks.py`. **Families:** W11-PIN /
> W11-CENSUS (every (leaf,params) key vs closed forms; exhaustiveness sum;
> history-depth census must reach ⌊(N−1)/2⌋) / W11-W10TIE (pointwise, RAM(1)
> ⟺ the sealed w10 classifier's '211') / W11-EXHAUST (drainage q^N exact;
> split = inert exact; classical sandwich) / W11-TOWER (8 frozen towers, all
> (2,h,1) levels) / W11-ORACLE (per-polynomial PARI (σ,e,f,v(disc)) vs leaf
> prediction; disc = 0 ⟹ undecided; double-lift well-posedness). **Teeth
> (each ≥ 1 or RED):** W11-T-MISSING / W11-T-SHADOW / W11-T-DRAIN /
> W11-T-SIGMA / W11-T-TAMEDISC (see runner docstring for their plants).
> **Census rows (30):** Zp (p,N) ∈ {2}×{2,3,4,6,8} ∪ {3}×{2,3,4} ∪
> {5,7}×{2,3}; Fqt q ∈ {2,…,9 prime powers} with N ∈ {2,3} + deep rows
> (2,4),(2,6),(2,8),(3,4) — 1,235,872 monic quadratics (unit: polynomials
> enumerated; fixed at the seal commit's row list). Deep rows realize
> chained refinement histories to depth 3 and rows through RAM(7). **Tower
> subset (8):** W-10's seven (C2A, C2C, C2E, C2F, P3A, J7A, P1B) + C3E (the
> (2,3,1) wild p = 2 realization — the charge's ≥ 2 beyond-(2,1,1) shapes are
> carried by the census (RAM(3), RAM(5), RAM(7), INERTDEEP, SPLITEQ, 2SIDED,
> …) AND by this realized roster level). Frozen imports md5-pinned:
> iterlawn_pe_reimpl cae45db2, grt_jc_probe 03811b69, jd0_checks d3a5e13d,
> w10_checks a9c34244 (full md5s in the runner). **Oracle rows:**
> per-polynomial at (p,N) ∈ {(2,3),(2,4),(2,6),(3,2),(3,3),(5,2),(7,2)} =
> 8,252 polynomials; double-lift on all 1,070 decided members of
> {(2,3),(2,4),(3,2),(3,3)}.”

with the disclosed pre-seal smoke:

> “**PRE-SEAL SMOKE DISCLOSED:** developed against
> census rows (Zp,2,3),(Zp,2,4),(Zp,3,2),(Fqt,4,2),(Fqt,9,3), towers
> C2A/C3E, oracle (2,3)+(3,2) with dlift (3,2): all families 0 violations,
> all five teeth fired; the S1 spot tables were hand-computed from the S2
> closed forms FIRST and confirmed at smoke ((Fqt,9,3): SEP 236196 each,
> RAM(1) 52488, INERTDEEP(1) 2916, SPLITEQ(1) 2268, SPLIT-TAIL(1) 648,
> undecided 729 — summing to 531,441; (Zp,2,4): SEP 64 each, RAM(1) 64,
> RAM(3) 16, 2SIDED(1,2) 8, INERTDEEP(1) 16, SPLIT-TAIL(1) 8, undecided 16).
> `gp` availability probed pre-seal (disclosed in the docstring). No full
> run before the seal.”

**DERIVATION:** `[MACHINE FRAME — independently re-verified]` **Compile-time re-verification (2026-08-14):**

- The runner is STILL byte-identical to its seal: `git diff 7020ceb -- verification/openmath/w11_checks.py` is empty (exit 0).
- All four frozen-import md5-8 pins MATCH: `iterlawn_pe_reimpl.py` = `cae45db2318b89520dd5484466ef3604`; `grt_jc_probe.py` = `03811b695cf7aa1bd5b52d5b0cd8bcd6`; `jd0_checks.py` = `d3a5e13df97d3768573800960a0ec509`; `w10_checks.py` = `a9c34244a3af19f5fa864375b494380b`.
- The two artifact md5s of S10 MATCH: `w11_checks_output.txt` = `c0b6b10bab40519c5977c397cf29ae9e`; `w11_checks_results.json` = `72ad156752788ccfa3a813f7084117da`.

The disclosed pre-seal smoke is a genuine honesty item: the runner was *developed against* five census rows, so those rows are not blind. The mitigating discipline is stated — the spot tables were hand-computed from the closed forms FIRST — and the remaining 25 rows were blind.

Two spot values re-derived at compile time from the S2 closed forms: at (Fqt,9,3), SEP = ((81−9)/2)·9^(2·3−2) = 36·6561 = 236,196 ✓ and the row sums to 9^6 = 531,441 ✓; at (Zp,2,4), SEP = ((4−2)/2)·2^6 = 64 ✓, RAM(1) = (2−1)·2^(8−2−1) = 32 — **the note records 64**. Recomputing with the clause-(ii) law RAM(h = 2k−1) at k = 1: (q−1)q^(2N−2k−1) = 1·2^(8−2−1) = 2^5 = 32 per the formula, versus the note's 64; but the note's S2.1 RAM(1) bullet gives “count per center (q−1)q^(2N−3)” = 1·2^5 = 32 **per center**, and × q = 2 centers = 64 ✓ — the clause-(ii) laws are per-center for RAM (as clause (ii) says: “per center; q centers”), and the smoke table reports whole-space. The two conventions reconcile; the note's numbers are right.

**CONDITIONALITY:** BOX-3 (the classifier is a reimplementation, not the engine) and BOX-4 (PARI is mixed-characteristic only) fence what the battery can evidence.

**RESOLUTION TRACE:** S7; unchanged.

**TEETH:** this IS the battery frame; see §6 for the inverse table.

---

### EFF.W11.35  [battery-frame]

**CANONICAL STATEMENT — S7's preregistered predictions:**

> “**PREREGISTERED PREDICTIONS (commit 1), evidence class per row (IND =
> independent engine; SAME = this runner's own arithmetic/prediction
> recursion; NONE = bookkeeping):**
> * P-1 [NONE] W11-PIN 0/4 — all four frozen imports unmoved.
> * P-2 [SAME] W11-CENSUS: 0 violations on all 30 rows — every (leaf,params)
>   count equals its closed form; sums q^(2N) exactly; max history depth =
>   ⌊(N−1)/2⌋ on every row (3 at N = 8). Spot values (computed from the
>   closed forms before any full run): (Zp,2,8): RAM(1/3/5/7) = 16384/4096/
>   1024/256, undecided 256; (Fqt,8,3): SEP each 114688, RAM(1) 28672,
>   SPLITEQ(1) 1344, INERTDEEP(1) 1792, SPLIT-TAIL(1) 448, undecided 512
>   (sum 262,144 ✓ precomputed).
> * P-3 [SAME] W11-W10TIE: 0/1,235,872 pointwise — the sealed W-10
>   classifier's '211' bucket ⟺ this note's RAM(1), every polynomial.
> * P-4 [SAME] W11-EXHAUST: undecided = q^N on every row; split-decided =
>   inert-decided on every row; all 90 sandwich inequalities hold as exact
>   rationals.
> * P-5 [SAME] W11-TOWER: 0 violations on all realized (2,h,1) levels of the
>   8 towers; ≥ 1 wild realization and ≥ 1 with h ≠ 1 (predict: C3E level 2
>   = (2,3,1), p = 2, γ = 13, wild — observed at smoke).
> * P-6 [IND] W11-ORACLE: 0 bad among all 8,252 polynomials — every decided
>   leaf's (σ, e, f, v(disc)) confirmed by PARI (incl. the p = 2 wild-disc
>   rule per member); every disc = 0 member window-undecided; 0 double-lift
>   disagreements among the 1,070 decided members.
> * P-7 teeth: all five fire at exactly-predicted counts: MISSING = SHADOW =
>   DRAIN = 30 (once per census row), SIGMA = 3,020 (once per decided inert
>   member per oracle row: 20+80+1344+27+270+250+1029), TAMEDISC = 1,440
>   (once per p = 2 RAM member: 16+80+1344).
> * P-8 (falsifiers, blueprint break-analysis order): a census/model
>   mismatch on a WILD row with tame rows clean refutes the uniformity
>   clause and hits J-D0's mechanism; a drainage violation (undecided ≠ q^N)
>   refutes clause (iii) = the hExhaust instance — diagnose the S2.4/S2.5
>   algebra first; an oracle σ mismatch on a decided leaf means the read
>   does not mean its arithmetic — per GRT_WELD_BLUEPRINT S4's J-D row,
>   diagnose as an upstream WELD error FIRST; a tooth not firing voids the
>   battery, not the theorem.”

**DERIVATION:** `[PREREGISTRATION]` The evidence-class tagging is what makes the record honest: only P-6 is `[IND]`, an independent engine. P-2 through P-5 are `[SAME]` — the runner checking its own recursion against the note's closed forms, which tests transcription and arithmetic but not the model. P-8's falsifier ordering is itself load-bearing: a wild-row-only mismatch is routed to J-D0's mechanism, and an oracle σ mismatch is routed upstream to the WELD layer before the note.

**CONDITIONALITY:** “a tooth not firing voids the battery, not the theorem” — the teeth are instrument checks, not mathematical content.

**RESOLUTION TRACE:** S7; unchanged. All eight confirmed at S10 (EFF.W11.38).

**TEETH:** see §6.

---

### EFF.W11.36  [record]

**CANONICAL STATEMENT — S8, consumers:**

> “1. **W-12 / J-D1** — the composition display can now cite a PROVED
>    exhaustiveness instance instead of a bare program row.
> 2. **Phase-B omMenu growth / `DecidedOmCountTie`** — S4.1 is the complete
>    n = 2 transcription spec with certified target values.
> 3. **The general W-10/W-11** — S2's node system + instance bracket is the
>    template; S4.3 names what each generalization step owes and to whom.
> 4. **The public uniformity story** — the smallest COMPLETE display: one
>    degree, the whole menu, densities summing to 1, one formula per row at
>    every prime, PARI confirming wildness where the count never moves; and
>    the capstone's 1/4 vs 1/3 gap priced exactly (S4.2).”

**DERIVATION:** `[RECORD]` Consumer 2's wording “the complete n = 2 transcription spec” is re-scoped by C7-F2 to a mathematical target (EFF.W11.12). Consumers 1 and 4 are confirmed live: the acceptance record's PE3 leg audited “downstream-consumption … of W-12/HMENU3”, and C7-F2's sweep states “W-12/J-D1 and the PE3 W-12/HMENU3 consumption audit use the proved exhaustiveness and aggregate densities, so they survive.” Consumer 2's Lean target `DecidedOmCountTie` is verified to exist as `lean/LeanUrat/OM/DecidedOmCountTie.lean` (XREF L08), and its own docstring confirms it is an order-1 module, not an order-≥1 menu growth: “**DecidedOmCountTie — CLOSING the order-1 decided-shape `omCount` tie**”.

**CONDITIONALITY:** consumer 2 re-scoped by C7-F2.

**RESOLUTION TRACE:** S8; consumer 2 re-scoped.

**TEETH:** none; a consumer list.

---

### EFF.W11.37  [table]

**CANONICAL STATEMENT — S9, the conditionality stack with as-of pins:**

`[TABLE]` (the note displays this as a bulleted list; transcribed as a table without reordering, each cell in the note's own wording)

| Supplier | Pin | Consumed as |
|---|---|---|
| **THEOREM W-10(2,1,1)** | two-commit seal **2e6fdd8/9506a55** (1,090,364 checks / 0 violations at that commit) | “the RAM(1) row (count + arithmetic, S2.1), the recentering mechanics (its S2.1, cited not re-proved), and its SEALED classifier as the W11-W10TIE reference instrument (md5 a9c34244, pinned)” |
| **LEMMA J-D0** | seal 1642275/**9387eb1** | “the shape-keying/value-blindness FRAME (S2.1's census remark, S5); the n = 2 census equalities are proved directly here, so J-D0 is corroborating at the instance, load-bearing only for the general-program framing (S4.3 inherits its BOX-2 gauge-form perimeter)” |
| **Accepted weld suppliers** (all six ACCEPTED 2/2; ledger fold **17d2a32**) | GRTJA @ **f131c53**, GRTJB + GRTJC @ **83f47f4**, GRTW2 @ **adc6cf3**, LIFTCORNER @ **08f61e9**, WELDMASTER @ **66b3498** | “cited for the TEMPLATE faces only (S4.3, W11-TOWER's grid tie γ = e·wPhi + h); S2's n = 2 proofs are self-contained elementary arithmetic + Hensel” |
| **DULEMMA** | **048cf6d/f819f26** | “NOT consumed (S3, displayed)” |
| **Lean anchors at HEAD** | `OM/RealInstanceV2.lean` `montes_unconditional_exhaustive`/`hExhaust`, `OMCountV2.omMenu`/`omMenu_order0`, `gate3_inert_q2` | “cited as the tie TARGETS (S4.1/ S4.2), no Lean changed” |
| **Classical inputs** | none (standard) | “Hensel's lemma (degree-1/separable-residual factorization steps), Eisenstein irreducibility, Artin–Schreier square/trace censuses over F_q — standard, cited without commit pins” |
| **L2core assembly identification** (W-10's H-2) | as stated there | “consumed as stated there (BOX-6)” |

with the note's own one-line summary:

> “**One line: the theorem's hypothesis set = {W-10 @ 2e6fdd8, J-D0 @ 9387eb1
> (frame), L2core assembly id, classical Hensel/Eisenstein/AS-census} —
> everything else in S2 is self-contained elementary arithmetic plus the
> sealed machine leg.**”

**DERIVATION:** `[CONDITIONALITY STACK — fully re-verified]` **All twenty commit hashes named anywhere in this note were confirmed to be git commit objects at compile time** (§4.3), including all thirteen in this table. Note the deliberate asymmetry: only W-10 is load-bearing as a *theorem*; J-D0 is a frame, the weld suppliers are template cites, DULEMMA is declined, the Lean anchors are targets. The hypothesis set is remarkably small for a note of this size.

**CONDITIONALITY:** the whole stack is “as-of” pinned; a supplier moving would require a re-pin.

**RESOLUTION TRACE:** S9; unchanged.

**TEETH:** W11-PIN (0/4, the four frozen imports unmoved); W11-W10TIE.

---

### EFF.W11.38  [table]

**CANONICAL STATEMENT — S10, the verdict:**

> “**GREEN. 30/30 census rows (1,235,872 polynomials enumerated), 12 realized
> (2,h,1) tower levels (7 wild, 1 beyond-(2,1,1)), 8,252 oracle polynomials
> + 1,070 double-lift members, 1,250,280 checks, 0 violations in every
> family, all five teeth fired at their exactly-predicted counts, zero
> skips.** Artifacts: `w11_checks_output.txt` (md5
> c0b6b10bab40519c5977c397cf29ae9e), `w11_checks_results.json` (md5
> 72ad156752788ccfa3a813f7084117da); runner byte-identical to the sealed
> commit 7020ceb (empty `git diff`); elapsed 49.9 s; exit 0; single fresh
> run, no prior artifacts.”

`[TABLE]` The prediction scorecard, transcribed (the note displays it as eight bullets; each cell is the note's own wording, abbreviated only where marked with an ellipsis):

| Pred | Class | Result | Decisive detail |
|---|---|---|---|
| P-1 ✓ | NONE | W11-PIN 0/4 | “all four frozen imports unmoved (iterlawn_pe_reimpl cae45db2, grt_jc_probe 03811b69, jd0_checks d3a5e13d, w10_checks a9c34244)” |
| P-2 ✓ | SAME | W11-CENSUS 0/375 | “every (leaf, params) key equals its closed form on all 30 rows, both characteristics; every exhaustiveness sum = q^(2N); max history depth = ⌊(N−1)/2⌋ on every row … (Zp,2,8): RAM(1/3/5/7) = 16384/4096/1024/256, undecided 256, depth-3 histories realized (64 members with history (1,2,3)); (Fqt,8,3): SEP 114688 each, RAM(1) 28672, SPLITEQ(1) 1344, INERTDEEP(1) 1792, SPLIT-TAIL(1) 448, undecided 512 — sum 262,144. … the (Zp,2,8) 2SIDED spectrum (1,2)…(3,4) all at (q−1)²q^(2N−3−w₁−w₂) (2048/1024/512/256/128/512/256/128/128) and SPLIT-TAIL(1)=(2)=(3)=128 — the w-independence law visible raw” |
| P-3 ✓ | SAME | W11-W10TIE 0/1,235,872 | “RAM(1) ⟺ the SEALED w10 classifier's '211' bucket, pointwise on every polynomial of every row: THEOREM W-10 consumed at pin with a machine-checked seam” |
| P-4 ✓ | SAME | W11-EXHAUST 0/150 | “undecided = q^N EXACTLY on all 30 rows (the drainage law, clause (iii)); split-decided = inert-decided EXACTLY on all 30 rows; all 90 classical-sandwich inequalities hold as exact rationals” |
| P-5 ✓ | SAME | W11-TOWER 0/50 | “endpoints (0,γ)–(2,0), γ odd = e·wPhi+h, interior strictly above on all 12 realized (2,h,1) levels; wild realizations 7 (C2A×2, C2E×2, P1B×2, C3E); the beyond-(2,1,1) realization C3E level 2 = (2,3,1), p = 2, γ = 13, WILD — as predicted from smoke” |
| P-6 ✓ | **IND** | W11-ORACLE 0 bad / 8,252 | “PARI (factorpadic + nfinit/idealprimedec) confirms every decided leaf's (σ, e, f, v(disc)) at all seven Z_p rows, including the p = 2 wild-disc rule per member and the (2,6) deep row (4,096 polynomials); every disc = 0 member is window-undecided; double-lift 0 bad / 1,070 decided members (56 + 240 + 72 + 702) — decidedness is lift-well-posed as proved” |
| P-7 ✓ | — | teeth | “all five at the EXACT preregistered counts: MISSING = SHADOW = DRAIN = 30 (once per census row), SIGMA = 3,020 (every decided inert member of every oracle row: 20+80+1344+27+270+250+1029), TAMEDISC = 1,440 (every p = 2 RAM member: 16+80+1344 — the tame prediction v(disc) = 1 failed on every wild member)” |
| P-8 ✓ | — | no falsifier fired | “nothing to diagnose upstream” |

**DERIVATION:** `[MACHINE RECORD — re-verified]` **Compile-time re-verification (2026-08-14):** both artifact md5s recomputed and MATCH; `git diff 7020ceb -- verification/openmath/w11_checks.py` is still empty, so the runner remains byte-identical to its seal six days later. Arithmetic spot-check of P-7's SIGMA total: 20+80+1344+27+270+250+1029 = 3,020 ✓; TAMEDISC: 16+80+1344 = 1,440 ✓; P-6's double-lift: 56+240+72+702 = 1,070 ✓. All three sums confirm.

**CONDITIONALITY:** the evidence classes of EFF.W11.35 apply — only P-6 is independent-engine evidence, and BOX-4 restricts it to mixed characteristic. C7-F4 sharpens P-7's TAMEDISC scope: it “supplies no equal-characteristic evidence.”

**RESOLUTION TRACE:** S10, appended at commit 2 from the committed artifacts; scoped by C7-F4 for the wildness wording.

**TEETH:** this IS the teeth record.

---

### EFF.W11.39  [record]

**CANONICAL STATEMENT — S10's consequence paragraph** `[ASSEMBLED: with the r1/r2 echo strike in place]`:

> “**Consequence for the grade box:** THEOREM W-11(n = 2) stands as composed
> — clauses (i)–(iii) PROVED (elementary proof S2 + GREEN sealed battery +
> independent PARI leg per polynomial), clause (iv) the proved spec display,
> the S6 boxes open exactly as displayed (the general W-11 remains the S4.3
> program per BOX-1). hExhaust at n = 2 is now a THEOREM with exact rate
> q^(−N). Attempt 0/2; ~~the hostile arc has not begun~~ **[r1: commit-2
> wording, superseded — arc status lives in the header S-STATUS: PE1 run
> (2 CRITICAL + 2 GAPS + 2 MINOR, all display/side-claim level), r1
> applied, counter 0/2, PE2 = the next attempt] [r2 echo: PE2 run
> (0 CRITICAL + 1 GAP + 1 MINOR, both display-level, 473a993), r2
> applied, counter 0/2, PE3 = the next attempt]**. The J-D block may
> proceed to W-12 with a proved exhaustiveness instance in hand.”

**DERIVATION:** `[RECORD]` The headline sentence — “hExhaust at n = 2 is now a THEOREM with exact rate q^(−N)” — is the note's deliverable in one line.

**CONDITIONALITY:** “Attempt 0/2” and both bracketed arc echoes are `[SUPERSEDED]` by EFF.W11.40; clause (iv)'s “proved spec display” is re-scoped by C7-F2.

**RESOLUTION TRACE:** S10 tail, with the r1 strike and r2 echo; grade superseded by the acceptance record.

**TEETH:** §7 of this specification.

---

### EFF.W11.40  [acceptance-box]

**CANONICAL STATEMENT — the acceptance record, freeze stamp, and non-finding remarks:**

> “**THIS NOTE IS ACCEPTED at 2/2** — PE3 (839b735, CLEAN; fresh route:
> 1,114,112 quadratics brute-forced on never-checked 𝔽₄ rows;
> downstream-consumption audit of W-12/HMENU3 honest) and PE4 (16d12e1,
> CLEAN; fresh route: disc-fibration counting on new territory incl. 𝔽₉
> N=4 = 43,046,721 pairs, third independent derivation of every-window
> split = inert; PLUS the arc's first 4-mutant audit of the sealed
> battery — all four planted corruptions caught RED). Full arc: composed
> → seal 7020ceb / verdict cb05127 → PE1 (2C+2G+2m, fbf0a02) → r1
> (8c87fa3) → PE2 (0C+1G+1m, 473a993) → r2 (31506b3) → PE3 CLEAN → PE4
> CLEAN. Five passes, two repairs.”

> “**FREEZE-CONVENTION STAMP**: the accepted text is the post-r2 body,
> byte-frozen since 31506b3 (PE4 verified `git diff` empty AND that each
> prior pass provably read exactly its era's text); this record and any
> future annex are dated appends only.”

> “**WHAT IS ACCEPTED**: THEOREM W-11(n=2) — the seven-family decided
> menu of monic quadratics over any complete DVR with exact q-polynomial
> window counts, σ-undecided EXACTLY q^N (hExhaust at n=2 with exact
> drainage rate), limit densities split = inert = q/(2(q+1)), ram =
> 1/(q+1), Σ = 1, both characteristics, wild p=2 included — at its
> displayed boxes and conditionality. Non-finding remarks recorded at
> acceptance: R-a (sealed SPLITEQ k-scaling evidence is k=1; the arc's
> sole k=2 instance is PE3's fresh (Fqt,4,5)); R-b (2SIDED/RAM(h≥3)
> machine-realized at q∈{2,3}, disclosed row-list boundary).”

**DERIVATION:** `[ACCEPTANCE RECORD — five passes, three independent routes]` The evidential strength here is unusual for the corpus: PE3 brute-forced 1,114,112 quadratics on **never-checked 𝔽₄ rows** (a fresh route, not a re-run), PE4 ran a **disc-fibration** derivation on 𝔽₉ N=4 (43,046,721 pairs) giving a **third independent derivation** of the every-window split = inert identity, and PE4 additionally ran a **4-mutant audit of the sealed battery with all four planted corruptions caught RED** — the arc's first mutant audit, which is what converts “0 violations” from an absence of evidence into evidence of sensitivity. All eight commits verified to exist at compile time (§4.3).

**⚠ TWO PHRASES RE-READ BY THE ANNEX.** “seven-family decided menu” → “six decided shape families plus one finite-window σ-boundary family” (C7-F1). “wild p = 2 included” → “the included separable wild members, alongside separately included purely inseparable ramified members” (C7-F4).

**R-a and R-b are honest coverage boundaries, not findings:** the sealed battery's SPLITEQ evidence is k = 1 only (the sole k = 2 instance came from PE3's fresh route, outside the seal), and 2SIDED/RAM(h ≥ 3) are machine-realized only at q ∈ {2,3}.

**CONDITIONALITY:** “at its displayed boxes and conditionality” — the seven boxes of EFF.W11.33 and the S9 stack of EFF.W11.37 are part of the accepted statement.

**RESOLUTION TRACE:** the acceptance record; supersedes every grade line. The body has been byte-frozen since `31506b3`, verified to exist; the working tree is clean on this file.

**TEETH:** §7 of this specification.

---

### EFF.W11.41  [changes-record]

**CANONICAL STATEMENT — the dated annex fold header:**

> “### Dated annex fold (2026-08-12 — sol certification C7/E9: the four annex items repaired at HEAD)
>
> The sol-5.6 as-built ratification of this note (gpt-5.6-sol high,
> runs/cert/C7_w11_output.log, 2026-08-12) returned RATIFIED-WITH-ANNEX:
> all nine core checks CLEAN (the node trichotomy, the residual
> censuses, the refinement bracket q^{k−1}, all six window-count laws,
> the q^N σ-undecided law, the finite telescope, the limit densities,
> the v(2) = 1 fence, the disc-zero distinction); four annex items owed
> in the omMenu-specification language and side claims. The E9 fold run
> (gpt-5.6-sol high, runs/cert2/E9_w11_annex_output.log) adjudicated
> all four REAL at HEAD and derived the repairs below, each with its
> consumer sweep. Everything above this heading is byte-untouched by
> this append.”

**DERIVATION:** `[CERTIFICATION RECORD]` The nine CLEAN core checks map onto EFF.W11.15, .16, .23, .09/.24, .26, .27, .27's limit half, .06's pin, and .19 respectively — i.e. **every mathematical unit of S2 passed a fresh-model independent ratification.** The four annex items are all in “the omMenu-specification language and side claims”, which is why none of them moves a number: C7-F1 and C7-F2 are specification-language, C7-F3 removes a false identification, C7-F4 is terminology.

**CONDITIONALITY:** RATIFIED-**WITH-ANNEX**, not unconditionally; the four repairs are the annex, and they are now folded.

**RESOLUTION TRACE:** dated append after the acceptance record; the body is byte-untouched.

**TEETH:** the nine core checks are the certification's own; the note's battery is unchanged.

---

### EFF.W11.42  [record]

**CANONICAL STATEMENT — the E9 orchestrator-verification footnote:**

> “*(The four corrections above were derived by the E9 certification run
> (gpt-5.6-sol high, runs/cert2/E9_w11_annex_output.log, 2026-08-12);
> orchestrator verification before transcription — C7-F1: the boundary
> counter-instance re-checked (window cell (q,N,w) = (2,4,1) admits
> lifts of shape 2SIDED(1,4), 2SIDED(1,5), … and the exact A₀ = 0 lift
> x(x+A₁): one σ, no single typeOf key); C7-F2: every aggregate sum
> re-derived by hand (Σ RAM = 1/(q+1); Σ INERTDEEP = 1/(2q(q+1));
> Σ 2SIDED = 1/(q²(q+1)); Σ SPLITEQ = (q−2)/(2q²(q+1));
> Σ 2SIDED + Σ SPLITEQ = 1/(2q(q+1)) = Σ INERTDEEP; the totals
> reproduce the note's committed limits split = inert = q/(2(q+1)),
> ram = 1/(q+1)); C7-F3: the boundary count re-derived
> ((q−1)q^{N−w−1}·q^{w−1} = (q−1)q^{N−2} per center, whole-space
> normalized mass (q−1)q^{−N−1} → 0, and 8/2⁸ = 1/32 at the (2,4,1)
> witness); C7-F4: the char-2 case split re-checked (f′ = A₁ in equal
> characteristic; v(A₀) = h odd makes A₀ a non-square, so A₁ = 0 gives
> the purely inseparable member; the 1,440 TAMEDISC sample figure is
> sol's read of the disclosed oracle rows). Transcribed unaltered per
> the standing division of labor. Ledger: row 25 → CERTIFIED
> (RATIFIED-W-ANNEX, annex folded).)*”

**DERIVATION:** `[VERIFICATION RECORD]` This is the two-model discipline made visible: sol derived, the orchestrator independently re-checked each of the four before transcription, then transcribed unaltered. **The compiler independently re-checked all four re-derivations** and they hold — the four aggregates (EFF.W11.12), the boundary mass and its 1/32 witness (EFF.W11.25), the char-2 case split (EFF.W11.18), and the counter-instance's logic (EFF.W11.08).

**CONDITIONALITY:** the 1,440 TAMEDISC figure is flagged by the note itself as “sol's read of the disclosed oracle rows”, i.e. a read of the record rather than a fresh count — the compiler confirms it equals the note's own P-7 arithmetic 16+80+1344 = 1,440.

**RESOLUTION TRACE:** the annex's closing footnote; the last line of the note.

**TEETH:** none; a provenance record.

---

## 4. XREF verification ledger

All designations grep-verified at compile time (2026-08-14) with fixed-string matching; commit objects verified with `git cat-file -t`; digests recomputed with `md5sum`.

### 4.1 Lean anchors (the tie targets)

| ID | Verified location and designation | Verification | Role |
|---|---|---|---|
| L01 | `lean/LeanUrat/OM/OMCountV2.lean:646` — `theorem gate3_inert_q2 : omCount (sepShape 2 lam2) 2 = 1 / 4 := by` | line read; **exact match to the note's cite** | the capstone's decided order-0 inert value (EFF.W11.11, .30) |
| L02 | `lean/LeanUrat/OM/RealInstanceV2.lean:439–442` — `montes_unconditional_exhaustive` with `hExhaust : Filter.Tendsto (fun N => (realM2 n hn).undecidedCount N / (M9.realP : ℚ) ^ (n * N))` | lines read; **exact match to the note's cite** | the `hExhaust` hypothesis W-11 instantiates at n = 2 (EFF.W11.02, .10, .30) |
| L03 | `omMenu_order0` | found in `OM/RealInstanceV2Gates.lean`, `OM/RealInstanceV2.lean`, `OM/OMCountV2.lean` | the order-0 slice anchor (EFF.W11.29) |
| L04 | `sepShapesOf` | found in 18 files incl. `OM/OMCountV2.lean`, `OM/RealInstanceV2.lean` | the order-0 menu (EFF.W11.29) |
| L05 | `omCount` | found in 42 files | the per-shape count (EFF.W11.29) |
| L06 | `omMenu` | found in 32 files | the menu (EFF.W11.29) |
| L07 | `lean/LeanUrat/OM/OMCountV2.lean` — `theorem gate3_inert_q3 : omCount (sepShape 2 lam2) 3 = 1 / 3 := by` | line read | **corroborating instance, not cited by the note**: (q−1)/(2q) at q = 3 = 1/3 ✓, so the Lean inert order-0 form matches W-11's SEP-INERT at a second point |
| L08 | `lean/LeanUrat/OM/DecidedOmCountTie.lean` — `# DecidedOmCountTie — CLOSING the order-1 decided-shape \`omCount\` tie` | file read | consumer 2's Lean target (EFF.W11.36); its own docstring scopes it to **order-1**, not the order-≥1 menu growth W-11 specifies |
| L09 | `lean/LeanUrat/OM/OMCountV2.lean` — `theorem availPoly_two_eval (x : ℚ) : (availPoly 2).eval x = (x ^ 2 - x) / 2 := by` | line read | **the Lean closed form behind L01**: `omCount (sepShape 2 lam2) q = ((q²−q)/2)·q^(−2) = (q−1)/(2q)` — identically W-11's SEP-INERT density |
| L10 | same — `theorem availPoly_one_eval (x : ℚ) : (availPoly 1).eval x = x - 1 := by` | line read | **the punctured linear pool** — the a₀-unit condition behind OPEN-CALL 1 |
| L11 | same — `theorem gate5_empty : omCount (sepShape 2 lam11) 2 = 0 := by` | line read | **the SPLIT-half mismatch**: Lean gives 0 at q = 2 where W-11's SEP-SPLIT density is (q−1)/(2q) = 1/4 (OPEN-CALL 1) |
| L12 | same — `theorem gate3_split_q3 : omCount (sepShape 2 lam11) 3 = 1 / 9 := by` | line read | second SPLIT-half data point: 1/9 vs W-11's 1/3 at q = 3 (OPEN-CALL 1) |
| L13 | same — `the Phase-A classifier emits only the a₀-unit-conditioned \`sepShape\` strata (SIGMA-1)` | line read (file line 45) | **the stated reason for the divergence** (OPEN-CALL 1) |

### 4.2 Verified NEGATIVE edge (the Lean side is a target, not a consumer)

| ID | Check | Result | Meaning |
|---|---|---|---|
| N1 | `grep -rlF 'W-11' lean/LeanUrat/` | no files | no Lean source cites W-11 |
| N2 | `grep -rlF 'W11' lean/LeanUrat/` | `MovesS/MANIFEST.json` only | no Lean **source** cites W11; the single hit is a manifest |

Consistent with S9's own statement, “cited as the tie TARGETS (S4.1/
S4.2), no Lean changed”, and with BOX-2.

### 4.3 Commit locators (all 20 verified as git commit objects)

`[TABLE]`

| Hash | Role in the note |
|---|---|
| `7020ceb` | the seal commit (runner sealed unrun) — **runner still byte-identical: `git diff 7020ceb -- verification/openmath/w11_checks.py` empty** |
| `cb05127` | the commit-2 verdict |
| `fbf0a02` | `W11_passPE1_report.md` (2C+2G+2m) |
| `8c87fa3` | r1 note-only repair (F1–F6) |
| `473a993` | `W11_passPE2_report.md` (0C+1G+1m) — also the provenance of the finite telescope (EFF.W11.27) |
| `31506b3` | r2 — **the byte-freeze point of the accepted body** |
| `839b735` | PE3 CLEAN |
| `16d12e1` | PE4 CLEAN (4-mutant audit) |
| `2e6fdd8`, `9506a55` | W-10's two-commit seal (EFF.W11.37) |
| `1642275`, `9387eb1` | J-D0's seal |
| `17d2a32` | the weld-supplier ledger fold |
| `f131c53` | GRTJA |
| `83f47f4` | GRTJB + GRTJC |
| `adc6cf3` | GRTW2 |
| `08f61e9` | LIFTCORNER |
| `66b3498` | WELDMASTER |
| `048cf6d`, `f819f26` | DULEMMA (NOT consumed) |

### 4.4 Digest locators (all 6 recomputed, all MATCH)

| Artifact | Note's md5-8 pin | Recomputed | Verdict |
|---|---|---|---|
| `verification/openmath/w11_checks_output.txt` | `c0b6b10bab40519c5977c397cf29ae9e` (full) | `c0b6b10bab40519c5977c397cf29ae9e` | MATCH |
| `verification/openmath/w11_checks_results.json` | `72ad156752788ccfa3a813f7084117da` (full) | `72ad156752788ccfa3a813f7084117da` | MATCH |
| `verification/openmath/iterlawn_pe_reimpl.py` | `cae45db2` | `cae45db2318b89520dd5484466ef3604` | MATCH |
| `verification/openmath/grt_jc_probe.py` | `03811b69` | `03811b695cf7aa1bd5b52d5b0cd8bcd6` | MATCH |
| `verification/openmath/jd0_checks.py` | `d3a5e13d` | `d3a5e13df97d3768573800960a0ec509` | MATCH |
| `verification/openmath/w10_checks.py` | `a9c34244` | `a9c34244a3af19f5fa864375b494380b` | MATCH |

### 4.5 Source-note designations

| ID | Target and verified designation | count | Role |
|---|---|---:|---|
| X01 | `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md` | file exists | the charge's §S3.1 W-11 row (EFF.W11.03) |
| X02 | `lean/notes/openmath/W10_PROOF_2026-08-08.md` | file exists | THEOREM W-10(2,1,1); also the note's declined out-of-scope hit (EFF.W11.06) |
| X03 | `lean/notes/openmath/W11_passPE1_report.md` | file exists | PE1, the source of F1–F6 |
| X04 | `lean/notes/openmath/W11_passPE2_report.md` | file exists | PE2, **the provenance of the finite telescoping identity** (EFF.W11.27) |
| X05 | `lean/notes/openmath/W11_passPE3_report.md` | file exists | PE3 CLEAN |
| X06 | `lean/notes/openmath/W11_passPE4_report.md` | file exists | PE4 CLEAN + the 4-mutant audit |

### 4.6 Reverse-XREFs: consumers of W-11

| ID | Consumer file and verified designation | count | Supplied edge |
|---|---|---:|---|
| RX-1 | `spec/HYPOTHESIS_LEDGER.md` — `HYP.146  \`W11-BOX-1\`` | 1 | EFF.W11.31/.33; “CONSUMED BY: any W-11 use above n=2; its named owed inputs are HYP.21 (JB row 12), HYP.20 (JC warrant), and the drainage rows HYP.27/HYP.30” |
| RX-2 | same — the weld-face-audit row citing `W11 L391–393` | 1 | EFF.W11.28's JB non-import, independently corroborated as “No capstone-path consumer” |
| RX-3 | `lean/notes/openmath/W12_passPE6_report.md` | 4 mentions of `W-11` | the W-12 consumption; note its own correction: “…counter
0/2" for W-11, which is ACCEPTED 2/2 at repo HEAD (fold 35e6545).” — a downstream note that had a stale grade and fixed it |
| RX-4 | `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md` | cites W-11 | the HMENU3 consumption audited CLEAN at PE3 |
| RX-5 | `lean/notes/openmath/GENH4_PROOF_2026-08-08.md` | cites W-11 | a further downstream consumer |
| RX-6 | `docs/in-progress/LEAN_MAIN_THEOREM_SIGNOFF_2026-08-12.md` | cites W-11 | the Lean sign-off document's read of W-11 |

---

## 5. Effective supply/consumption ledger

`[TABLE]`

| Supplier / target | Effective W-11 relation | Surviving fence | Status |
|---|---|---|---|
| THEOREM W-10(2,1,1) @ `2e6fdd8/9506a55` | CONSUMED as the RAM(1) row, the recentering bijection, and the W11-W10TIE reference instrument | W10-BOX-1 (shape-generic count equality) stands untouched | **CONSUMED at pin, machine-seamed** (P-3, 0/1,235,872) |
| LEMMA J-D0 @ `9387eb1` | FRAME only — the n = 2 censuses are proved directly | load-bearing only for the general program (S4.3) | **FRAME, corroborating** |
| Six accepted weld suppliers | TEMPLATE faces only | S2 is self-contained elementary arithmetic + Hensel | **CITED, not load-bearing at n = 2** |
| DULEMMA @ `048cf6d/f819f26` | — | e_m ≥ 2 perimeter; e = 1 rows here are COUNT statements | **NOT CONSUMED (N-1)** |
| JC warrant, JB row-12 proviso @ `83f47f4` | — | needed only at composite stages / general polygons | **NOT CONSUMED (N-2, N-3); owed by S4.3** |
| Classical Hensel / Eisenstein / Artin–Schreier | CONSUMED without pins | standard | **CONSUMED** |
| L2core → L6M4 → U-DENS assembly id | CONSUMED as stated in W-10's H-2 | BOX-6 | **CONSUMED, not re-proved** |
| Lean `gate3_inert_q2` (`OMCountV2.lean:646`) | **CONSUMED BY W-11** as the order-0 half of the capstone tie: 1/4 + 1/12 = 1/3 | the deep half is W-11's own | **VERIFIED at compile time (L01, L09); the inert identification holds as a rational function of q** |
| Lean `omMenu_order0` / `sepShapesOf` | claimed identical to the SEP rows (clause (iv)) | — | **INERT half verified (L07, L09); SPLIT half FAILS — OPEN-CALL 1 (L10–L13)** |
| Lean `montes_unconditional_exhaustive` / `hExhaust` | W-11 supplies the n = 2 mathematics making the hypothesis TRUE | the Lean term-level tie is Phase-B (BOX-3, BOX-5) | **TARGET; no Lean edge landed (N1, N2)** |
| Lean `omMenu` growth / `DecidedOmCountTie` | W-11 supplies the mathematical target (C7-F2's designs (a)/(b)) | BOX-2 open; the API choice is not made | **TARGET; `DecidedOmCountTie` is order-1 only (L08)** |
| W-12 / J-D1, HMENU3, GENH4 | W-11 SUPPLIES the proved exhaustiveness instance and the aggregate densities | the general W-11 is a program (BOX-1) | **LIVE downstream consumers, audited CLEAN at PE3** |

---

## 6. TEETH inverse inventory

Disposition vocabulary is `{Lean theorem, executable regression, signed non-applicability}`. W-11's battery is **first-party and re-runnable** (unlike T4's inherited evidence), so most rows are executable regressions; the note's own honesty is that only W11-ORACLE is `[IND]`.

| # | Battery row / prediction | Guarded EFF units | Disposition |
|---|---|---|---|
| 1 | W11-PIN / P-1 — four frozen imports unmoved | EFF.W11.34, .37 | executable regression (md5 pins; all four re-verified MATCH at compile time) |
| 2 | W11-CENSUS / P-2 — every (leaf,params) key vs closed form on 30 rows; sums q^(2N); history depth ⌊(N−1)/2⌋ | EFF.W11.07, .09, .15, .16, .20, .21, .23, .24, .25 | executable regression `[SAME]` |
| 3 | W11-W10TIE / P-3 — RAM(1) ⟺ the sealed w10 '211' bucket, pointwise | EFF.W11.14, .15, .37 | executable regression `[SAME]`, machine-seamed to a sealed external instrument |
| 4 | W11-EXHAUST / P-4 — drainage q^N exact; split = inert exact; the classical sandwich | EFF.W11.10, .22, .26, .27 | executable regression `[SAME]` |
| 5 | W11-TOWER / P-5 — 8 frozen towers, all realized (2,h,1) levels, the grid tie γ = e·wPhi + h | EFF.W11.33 (BOX-3), .34, .37 | executable regression `[SAME]` |
| 6 | W11-ORACLE / P-6 — per-polynomial PARI (σ,e,f,v(disc)); disc = 0 ⟹ undecided; double-lift | EFF.W11.17, .19, .32 | executable regression **`[IND]`** — the only independent-engine row; **mixed characteristic only** (BOX-4) |
| 7 | W11-T-MISSING (30) | EFF.W11.34 | executable regression (instrument tooth) |
| 8 | W11-T-SHADOW (30) | EFF.W11.34 | executable regression (instrument tooth) |
| 9 | W11-T-DRAIN (30) | EFF.W11.10, .26 | executable regression (instrument tooth) |
| 10 | W11-T-SIGMA (3,020) | EFF.W11.17 (INERTDEEP σ), .38 | executable regression (instrument tooth) |
| 11 | W11-T-TAMEDISC (1,440) | EFF.W11.17, .18, .32 | **signed non-applicability in equal characteristic** — C7-F4: “It supplies no equal-characteristic evidence.” Executable regression in mixed characteristic. |
| 12 | P-8 falsifier ordering (wild-row mismatch → J-D0; drainage violation → clause (iii); oracle σ mismatch → upstream WELD) | EFF.W11.10, .32, .35 | signed non-applicability (a diagnostic protocol, not a check) |
| 13 | PE4's 4-mutant audit — four planted corruptions, all caught RED | EFF.W11.34, .40 | executable regression (the sensitivity check that makes “0 violations” informative) |

**Zero-orphan check:** 13 of 13 battery obligations mapped (6 check families + 5 teeth + the falsifier protocol + the mutant audit); 0 orphan rows.

**Reverse direction — units with no tooth:** the note itself states which units the battery cannot reach. EFF.W11.11, .12, .29, .30 (the Lean tie) are untested — BOX-3: “The Lean evaluator tie remains order-0.” EFF.W11.31 (the general program) is untested by construction. EFF.W11.03, .04, .05, .28, .33, .36, .37, .41, .42 are records and fences. Every mathematical unit of S2 (EFF.W11.14–.27) is guarded by at least one row.

---

## 7. Acceptance and evidence fence

W-11's acceptance is the corpus's **strongest evidential position among the four notes in this queue**, and the reasons are worth naming precisely.

**Five passes, three genuinely fresh routes.** PE1 re-derived clauses (i)–(iii) independently and built its own classifier (7 census rows, ≈345k polynomials, 0 mismatches). PE3 brute-forced 1,114,112 quadratics on **never-checked 𝔽₄ rows**. PE4 ran a **disc-fibration** derivation on new territory (𝔽₉ N = 4, 43,046,721 pairs) yielding a **third independent derivation** of the every-window split = inert identity.

**A mutant audit.** PE4's 4-mutant audit — “all four planted corruptions caught RED” — is what licenses reading “0 violations in every family” as evidence rather than as a null result.

**A byte-frozen, still-verifiable instrument.** The runner remains byte-identical to its seal (`git diff 7020ceb` empty at compile time, six days on), all six md5 pins re-verified MATCH, and the two-commit discipline means S10's verdict was appended *from* the committed artifacts.

**What it is NOT.** (1) Only P-6 is independent-engine evidence, and BOX-4 restricts PARI to mixed characteristic; C7-F4 sharpens this — the TAMEDISC tooth “supplies no equal-characteristic evidence.” (2) Five census rows were pre-seal smoke rows (disclosed). (3) R-a/R-b are real coverage boundaries: sealed SPLITEQ evidence is k = 1 only, and 2SIDED/RAM(h ≥ 3) are machine-realized only at q ∈ {2,3}. (4) **Nothing above n = 2 is evidenced or claimed** (BOX-1). (5) The Lean tie is untested at every order (BOX-3).

**The certification layer.** Independently of the hostile arc, the sol C7 run returned RATIFIED-WITH-ANNEX with nine core checks CLEAN and four annex items, all four adjudicated REAL and folded (EFF.W11.41). Every one of the four is specification-language or terminology; **no number in the note moved.**

---

## 8. Deferred reconciliation obligations

1. **The clause-(iv) SPLIT-half identification — FOR-0d.** See OPEN-CALL 1. This is the only place in the note where a compile-time check against a cited target fails, and it is a convention mismatch rather than an arithmetic error.

2. **Phase-B must choose C7-F2's design (a) or (b).** C7-F2 proves the inputs for both and chooses neither: “This note proves the mathematical inputs for both designs but does not choose or implement either design; that choice remains Phase-B code/API work under BOX-2.” `DecidedOmCountTie` currently closes only the **order-1** tie (L08), so the order-≥1 menu growth W-11 specifies is not started. Action item.

3. **The W-10 latent fence, recorded and declined.** r2's PE2-F2 sweep found the identical unpinned “mixed Z_p-type” phrase in `W10_PROOF_2026-08-08.md` S1 with its p = 2 disc laws at v(2) = 1, and explicitly declined to repair it: “that note is sealed; same latent fence, its own arc's to carry”. W-10's arc owns it. Cross-note bookkeeping.

4. **The finite telescope's provenance.** EFF.W11.27's every-window split = inert identity rests on an identity **transcribed from the PE2 report** (`W11_passPE2_report.md` @ 473a993) rather than derived in the note's own voice. The note flags this (“transcribed and re-verified”), PE4 later gave a third independent derivation, and the compiler re-checked its arithmetic — so the step is sound. Recorded only because a blueprint consumer tracing S2.5's proof to its source will land in a pass report, not in the note.

5. **W-12's stale grade, already fixed downstream.** `W12_passPE6_report.md` records having read “…counter
0/2" for W-11, which is ACCEPTED 2/2 at repo HEAD (fold 35e6545).” — i.e. a downstream note that carried a stale W-11 grade and corrected it. No action; recorded so the cross-read does not re-flag it.

---

## 9. Self-audit

### Resolved compilation calls

- The effective text is derived under a **two-mechanism** rule (in-body strike-and-replace + dated annex), unlike the round-append structure of T3/T4/T5. Thirteen strike pairs and four annex corrections are tabulated in §1 with their governing text named.
- Struck text is reproduced inside `~~…~~` rather than deleted, so the historical reading — including the *false* r0 evaluations of S2.4 — stays visible to the cross-read.
- Each C7 correction's CONSUMER SWEEP is compiled as part of the correction, because that is what makes each one non-destructive; all four sweeps agree that clauses (i′)–(iii) are untouched.
- **Every arithmetic claim the corrections rest on was independently re-checked**: r1-F1's numerical witness (1/7 + 1/28 + 1/14 = 1/4 ✓, and the struck 2/7 + 1/14 + 1/7 = 1/2 ✗), C7-F2's four aggregates and the totals, C7-F3's boundary mass and its 8/2⁸ = 1/32 witness, C7-F4's case split, EFF.W11.27's telescope factor (q−1)(1 + (q−2)/2) = q(q−1)/2, and the final Σ = 1.
- Three sums in the machine record were re-added and confirm: SIGMA 3,020; TAMEDISC 1,440; double-lift 1,070.
- One apparent numerical discrepancy in the S7 smoke table (RAM(1) = 64 at (Zp,2,4) versus the clause-(ii) formula's 32) was chased and **resolved as a per-center vs whole-space convention difference**, exactly as clause (ii) declares — not an error.
- All 20 commit locators verified as git objects; all 6 digests recomputed MATCH; the runner's byte-identity to its seal re-confirmed.
- Both Lean line-cites verified byte-literally (`OMCountV2.lean:646`, `RealInstanceV2.lean:439–442`).
- The Lean edge is confirmed **one-directional** by two negative greps (N1, N2), matching S9 and BOX-2.
- Six reverse-XREFs emitted, including one downstream note that carried and fixed a stale W-11 grade.
- Battery fully consumed: 13 obligations, 0 orphans; the units the battery cannot reach are named with the note's own reason.
- No table prosified: the menu table, the residual census, the conditionality stack, the prediction scorecard, the supersession chain, and both locator tables are tables.

### Fidelity audit (compile-time, mechanical)

- Quoted segments extracted from this specification and tested for verbatim containment in the source note under a normalization removing only presentational reflow. Script: `scratchpad/verb2.py`.
- **228 quoted segments checked, 219 verbatim.** The 9 non-matches are exclusively (a) **cross-file quotations** — 2 from `spec/HYPOTHESIS_LEDGER.md`, 3 from `lean/LeanUrat/OM/` sources, 1 from `lean/notes/openmath/W12_passPE6_report.md`, each independently grep-verified at count 1 in its own file — and (b) explicitly marked `[ASSEMBLED]` composites (EFF.W11.01, .06, .17, .21, .22, .27, .32, .39), whose components were verified individually.
- Three quotation repairs were made during the audit: two line-wrap rejoins restored to the source's wrapping, and one sub-quote that had silently dropped a parenthetical was replaced by the full quotation.
- Struck spans are reproduced with their `~~` markers intact, so no strike is silently resolved.
- No quantifier, index, count, density, valuation, or verdict was altered anywhere.

### OPEN-CALLS

**OPEN-CALL 1 — clause (iv)'s order-0 identification fails on its SPLIT half. FOR-0d — NEEDS ASVIN.**

Clause (iv) asserts:

> “the order-0 slice already in Lean (`omMenu_order0` =
> `sepShapesOf`) is exactly the SEP rows”

No C7 correction touches this clause. A compile-time check splits it.

**The INERT half holds, and holds strongly.** `omCount_sepShape_eval_poly` reduces `omCount (sepShape 2 lam2) q` to `availPoly 2` evaluated at q times q^(−2), and `availPoly_two_eval` (L09) gives `(availPoly 2).eval x = (x ^ 2 - x) / 2`. So the Lean value is ((q²−q)/2)·q^(−2) = (q−1)/(2q), which is **identically W-11's SEP-INERT limit density as a rational function of q** — confirmed at two points by the landed gates: `gate3_inert_q2 = 1/4` at q = 2 (L01) and `gate3_inert_q3 = 1/3` at q = 3 (L07).

**The SPLIT half does not hold.** Lean's split order-0 value uses `availPoly 1`, and `availPoly_one_eval` (L10) gives `(availPoly 1).eval x = x - 1` — a pool of q−1 monic linears, not q. Consequently `omCount (sepShape 2 lam11) q = ((q−1)(q−2)/2)·q^(−2)`, and the landed gates read `gate5_empty : omCount (sepShape 2 lam11) 2 = 0` (L11) and `gate3_split_q3 : omCount (sepShape 2 lam11) 3 = 1 / 9` (L12). W-11's SEP-SPLIT limit density is (q−1)/(2q) — **1/4 at q = 2 and 1/3 at q = 3**. The two disagree at both points and as rational functions.

**The cause is stated in the Lean source, not hidden.** `OM/OMCountV2.lean` line 45 (L13): “the Phase-A classifier emits only the a₀-unit-conditioned `sepShape` strata (SIGMA-1)”, and the `gate5_empty` docstring makes the mechanism explicit: “the split stratum is genuinely EMPTY at `q = 2` (`ff(q−1, 2) = 0` — any two distinct monic linears over `F₂` include `X`; SIGMA-1 honesty, do NOT "fix")”. So Lean counts a₀-**unit** strata; W-11's SEP rows count **all** monic quadratics, including those with a root at 0. For the inert row the restriction is vacuous (an irreducible quadratic has nonzero constant term automatically), which is exactly why the inert half matches and the split half does not.

**Why this matters and why it does not invalidate anything proved.** It does not touch clauses (i′)–(iii): W-11's counts are internally consistent, machine-verified on 30 rows, and independently re-derived three times. It does not touch S4.2's capstone tie, which consumes only the INERT row (EFF.W11.30) — 1/4 + 1/12 = 1/3 stands. What it touches is the *tie statement*: a Phase-B implementer reading clause (iv) literally would expect the landed order-0 split gate to be W-11's SEP-SPLIT row and would find a different rational function, with the discrepancy maximal at q = 2 (1/4 versus 0). Either W-11's SEP-SPLIT row must be re-stated in the a₀-unit convention, or clause (iv)'s identification must be scoped to the inert row plus a stated convention-translation, or the two models must be reconciled at the Phase-B interface. Deciding which is a note-owner/Phase-B call and cannot be read off the text. Note also that the a₀-unit convention **breaks W-11's split = inert symmetry** ((q−1)(q−2)/2 ≠ (q²−q)/2), which is precisely what Lean's `gate6_sigma_separation` is designed to exhibit — so the two models are not merely differently normalized, they disagree about a structural feature W-11 proves.

**OPEN-CALL 2 — “seven leaf families” in the header survives C7-F1's declared supersession list. FOR-0b (note owner).**

C7-F1 supersedes three named phrases: “seven-family decided menu”, “the decided leaves are exactly the seven families”, and the omMenu-transcription sentence. The header's “What W-11 is (one breath)” paragraph says instead “the full decided menu (seven leaf families, each ONE polynomial/rational family in q …)” — a fourth phrasing, not on the list. EFF.W11.02 reads it under C7-F1 by extension of the correction's evident intent, since C7-F1 explicitly re-reads even the acceptance record's phrasing. But the compiler is extending a declared list, which is a judgment. **Proposed disposition:** add the header phrase to C7-F1's supersession list in a minors-only rider. Needs the note owner.

**OPEN-CALL 3 — the S1(i) table's SPLIT-TAIL row still carries a “limit density” column entry. FOR-0b.**

C7-F3 proves SPLIT-TAIL has *no positive fixed-row limit density* (normalized mass (q−1)q^(−N−1) → 0), and C7-F1 re-types it as a window cell. The S1(i) table's SPLIT-TAIL cell nonetheless sits in a column headed “limit density (whole space)” and contains a parenthetical rather than a density. This is not an error — the cell says “(window boundary family; … absorbed into 2SIDED only as N → ∞ …)”, i.e. it declines to give a density — but a mechanical reader extracting a density-per-row map from the table gets a type error on exactly one row, and neither correction restates the table. Recorded so the cross-read does not re-derive it. Whether the table should be re-drawn with the boundary family in a separate block is a presentation call.

### Exhaustive residual judgment list

There are no other unresolved W-11 mathematical or scope judgments. BOX-1's general program, BOX-2's API choice, BOX-3's evaluator tie, BOX-4's oracle coverage, BOX-5's two conventions, BOX-6's assembly identification, and BOX-7's htameFE fence are the note's own displayed stopping points, re-displayed at acceptance; R-a/R-b are disclosed coverage boundaries; the W-10 latent fence, the telescope provenance, and W-12's already-fixed stale grade are classified in §8 as bookkeeping.

EFF-W11 COMPILED: 42 statements / 47 xrefs verified / 3 open calls
