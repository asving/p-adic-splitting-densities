# GRTJC pass PE7 — HOSTILE VERIFICATION REPORT (fresh context; fixes nothing)

**Target:** `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md` **at HEAD**, i.e.
after the r6 NOTE-ONLY round (commit `4b804b4`: the two-edit pointer repair
PE6 prescribed — the dated [r6, G-1] annotation inside §0's [r4, G-1] bracket
+ the [r5, G-2] parenthetical's "as such" struck and corrected — plus the
§9.5 group-12 as-of pin PE6 noted; note **byte-identical `4b804b4` → HEAD**,
verified by `git diff` (0 lines); `4b804b4` touches ONLY the note
(116 insertions / 9 deletions, no `verification/` file, no `.lean`)).
Runners: `grt_jc_checks.py` (r0), `grt_jc_r1_checks.py` (r1),
`grt_jc_r2_checks.py` (r2), instrument `grt_jc_probe.py` — all in
`verification/openmath/`, all BYTE-FROZEN at r6 as claimed (all four md5s at
their sealed values, §M).
**Verifier role:** quote-and-classify only. CRITICAL ERROR = breaks the logical
chain (dependents not checked further); JUSTIFICATION GAP = assume and continue.
Fences and boxes are graded as part of the statement.
**Pass date:** 2026-08-06 wallclock (campaign 2026-08-08). **SEVENTH acceptance
attempt** (two consecutive clean passes accept; a clean pass here STARTS the
count).

## VERDICT

**0 CRITICAL · 0 GAPS — CLEAN.** This is the arc's FIRST clean pass; per the
acceptance rule it STARTS the count (advancing the counter to 1/2 is the
orchestrator's ledger action, not this report's). The full note was re-read
top to bottom at HEAD; the r6 diff was verified at every edit site including
the historical claims at both pinned commits; the arc-accounting system is
consistent AND true at HEAD; the decorrelated re-derivations (one by a route
no prior pass used, one on out-of-roster instances no runner has ever built)
returned zero exceptions; and the statement-level truth sweep of the W-6..W-9
clause boxes and the (DMULT-w)/(DMULT-s) tier system found every graded claim
true as fenced. Machine legs 4/4: exit 0 on all three batteries + the
instrument, r0/instrument stdout byte-identical, r1/r2 wallclock-digits-only
diffs, every committed JSON artifact reproduced byte-for-byte
(`git status verification/openmath/` clean), all four md5s at sealed values.

---

## §A THE CHARGES, CHECKED TO THE BOTTOM

### A1. Charge (1): the r6 diff, line by line — CLEAN at all six edit sites

The diff (`git show 4b804b4`) contains exactly: (i) the [r5] S-STATUS header
re-labelled SUPERSEDED-at-r6 (wording matches the [r2]/[r3]/[r4] precedents
verbatim-adapted); (ii) the new [r6] S-STATUS block with the full ARC display;
(iii) the [REPAIR ROUND r6] block; (iv) the dated [r6, G-1] annotation inside
§0's [r4, G-1] bracket; (v) the §9.5 group-12 [r6] as-of pin; (vi) the §10.1
arc brought forward per convention (the [r5] display struck, not deleted; the
[r6] extension; the "[r6] Grade deltas: NONE" line) + the [r5, G-2]
parenthetical fix. Nothing else — the ONE-FIX discipline held (the diff
contains PE6's two prescribed edits, the one-liner PE6 "noted but did not
weight", and the arc bookkeeping the convention requires, nothing more).

* **The historical claims verified at both pinned commits.** The [r6, G-1]
  annotation asserts "current stacks" and "supersede this display" were
  *both true at the r4 state (`edbb966`) and are inverted since r5*. I
  checked both halves at source: at `edbb966` the note contains ZERO
  round-record language (grep: no `ROUND-RECORD`/`round-record` hit) and
  §10.2's [r1]/[r2] displays were the most recent stack statements, with
  §0's one-liner deferring to them — both clauses in force; at `3870bc8`
  (r5) the [r5, G-2] blocks introduce `ROUND-RECORDS` at exactly two sites
  while §0's [r4, G-1] bracket is byte-identical to its r4 form
  (un-annotated) — the inversion is r5-bred, exactly as PE6 GAP 1 and the
  r6 disposition state.
* **Quotations byte-faithful.** "current stacks" / "supersede this display"
  (both fragments byte-exact substrings of the L590 bracket); the ellipsis
  form "the current stacks … which supersede this display" in the [r5, G-2]
  correction elides only "(§10.2 [r1]/[r2],"; the precedent quote "[r4 —
  true at the r3 commit …]" resolves at the §9.5 [r3] block (L2472); the
  PE6 verdict fragment "the r5 diff's substance is exact, everywhere I
  could machine-check it" is PE6 L24 verbatim (initial letter
  case-adapted, the arc display's standing convention).
* **The PE6 summary inside the [REPAIR ROUND r6] block is accurate against
  the PE6 report**: 18/18 per-alias numbers (§A1), the four `4.8`-only
  lines with dispositions (§A1), the [r5, G-2] consumption attribution
  line-by-line (§A2), the JC-SCAL decorrelated leg 6 rows / 0 exceptions
  (§A4), union 172 / zero new refuted-content lines (§A1), 18/18 hashes
  (§A3), and the honestly-qualified "stdouts byte-identical on
  r0/r2/instrument" (§M: r1 had two wallclock digits).
* **The new annotation's content claims true at HEAD**: §10.2's [r1]/[r2]
  displays are round-records ([r5, G-2]); the current stack is [r5, G-2]'s
  completed form; §0's display carries the completion in place and nothing
  at HEAD claims to supersede it; and the clause-(c) content the bracket
  goes on to state (consumed ONLY as (DMULT-w) via JC-LOC on B, (d)(e)
  unchanged) is unchanged and true — re-verified by the union-census diff
  (§A2 below).
* **The [r5, G-2] fix is exact**: "quoted for its content as of the citing
  round" is what §0 [r4, G-1] actually does (cites their r4 content under
  the since-annotated "current"/"supersede" label), and "that bracket now
  carries its own dated [r6] annotation in place" is true.
* **"[r6] Grade deltas: NONE" TRUE** — the diff touches no grade cell, no
  measured quantity, no `verification/` file.

### A2. Charge (2): the arc-accounting system at HEAD — CONSISTENT AND TRUE

* **[r6] S-STATUS (CURRENT): SIX passes, SIX rounds** ✓. All 21 hashes
  resolve in `git log` with matching subjects: seal/verdict
  `6ad01d1`/`8f07904`, PE1 `1a27be3`, r1 `85d5811`/`54904cc` + mini-seal
  `f45b63c`/`66263ce`, PE2 `4a76d52`, r2 `5742e25` + `79611a4`/`db12666`,
  PE3 `e4b6fbf`, r3 `126c33f`, PE4 `d5072b6`, r4 `edbb966`, PE5 `b38f3f4`,
  r5 `3870bc8`, PE6 `66760f6`, instrument `7212e56`/`fc89b03`, and r6
  itself `4b804b4`. ✓
* **Round-record figures match all six reports' own verdict lines**
  (re-read at source this pass): PE1 "2 CRITICAL · 8 GAPS", PE2 "0
  CRITICAL, 9 gaps", PE3 "0 CRITICAL, 8 gaps", PE4 "0 CRITICAL · 4 GAPS",
  PE5 "0 CRITICAL · 2 GAPS + 1 minor", PE6 "0 CRITICAL · 1 GAP". ✓
* **Exactly two CURRENT arc displays, both ending "JC-PE7 next"** (header
  L181, §10.1 L2649). Stale "JC-PE6 next" pointers survive only inside the
  annotated-SUPERSEDED [r5] S-STATUS block (L143) and the struck [r5] §10.1
  arc display (L2632). ✓
* **Strike system: 116 `~~` tokens / 0 odd paragraphs** (my own
  paragraph-split count) = PE6's 112 + the §10.1 [r5]-display strike-pair +
  the "as such" strike-pair — exactly the r6 commit message's census. ✓
* **Grade-delta convention lines [r2]..[r6] all present**, the [r6] one
  true (A1). Counter 0/2 at all 44 occurrences (PE6's 41 + 3 in r6's own
  blocks); no gate fires/retires; no density/menu/count statement; no
  `.lean` touched anywhere in the r6 diff. ✓
* **The union census discipline holds at r6.** My own execution of the
  eight-alias union grep (fresh script, substring match, `-B` forms
  excluded by the literal closing paren): **177 hit-lines at HEAD vs 172 at
  `3870bc8`** — 5 added, 0 removed. All five added lines verified at
  source: two inside the [r6] S-STATUS/§10.1 arc displays (the r5 entry's
  "FGMN (a)(b)" wording, RECORD), one in the [REPAIR ROUND r6] header (the
  `4.8` PE6-summary line, RECORD), and two in the [r6, G-1] annotation
  itself (L595-596, stating the CORRECTED footprint "FGMN (a)(b) +
  (DMULT-w) on B + Thm 4.8/Cor 4.9 + Cor 2.7"). **Zero new lines state
  (IN-3)(c)-on-gr, (COORD), (MULT), the Thm-4.2-on-gr_{O[x]} transport, or
  the bare "FGMN (c)" alias.** ✓
* **Pointer-site sweep to fixed point**: every "current stack"/"supersede"
  site at HEAD is either the repaired §0 bracket (now [r6]-annotated), the
  [r5, G-2] current-stack declaration itself (live and true), the
  [r6]-pinned §9.5 group-12 line, or repair-history record. No remaining
  inverted pointer. ✓

### A3. Charge (3): the decorrelated re-derivation — TWO legs, routes disclosed

**Leg A (mathematical; a route no prior pass used).** **LEMMA JC-GAUGE
(§2.2) re-proved by the coarsened-grading + component-comparison route** —
chosen because it is load-bearing for every clause (the ℤ → ℤ/E collapse
underlies W-6(ii), W-7's grading, JC-IND, and the 𝒜_ν ≅ K display) and every
prior re-derivation (PE1's included) followed the note's own σ-retraction
proof. My route: (a) coarsen B to the ℤ/E-grading C = ⊕_ν B^{(ν)}; ϑ ∈ B_E ⊆
C_0, so ϑ−1 is a DEGREE-0 homogeneous element of C, and the quotient of a
graded ring by the ideal generated by a degree-0 homogeneous element is
graded with the ideal splitting componentwise — clauses (i)+(ii) drop out
with no computation. (b) For (iii), B_n → A_ν: surjectivity because
b ≡ ϑ^{-k}b mod (ϑ−1)B^{(ν)} for b ∈ B_{n+kE} (ϑ^k − 1 ∈ (ϑ−1)B for every
k ∈ ℤ, negative k via ϑ^k−1 = −ϑ^k(ϑ^{-k}−1)); injectivity WITHOUT the
retraction: if x ∈ B_n ∩ (ϑ−1)B^{(ν)}, write x = (ϑ−1)Σ_k y_k (finite
support, y_k ∈ B_{n+kE}); comparing components at every degree n+kE, k ≠ 0
gives the two telescoping chains y_k = ϑ^k y_0 (k ≥ 0) and
y_{−j} = ϑ^{−(j−1)}y_{−1} (j ≥ 1), each of which forces its seed to vanish
against finite support (ϑ invertible), so y = 0 and x = 0. Hypothesis audit:
the unit is needed exactly for surjectivity's ϑ^{-k} and the downward chain
(the upward chain needs only a nonzerodivisor) — consistent with the note's
placement of the gauge strictly AFTER TC-1. The note's own σ-proof was
independently re-checked en route and is sound (σ well defined, kills the
ideal piece, converse via ϑ^{-k}b(ϑ^k−1) ∈ (ϑ−1)B ∩ B^{(ν)} = the ideal
piece by (i)). Both routes land the same statement; A_0 ≅ B_0 as rings via
the subring inclusion composed with the quotient. **CLEAN.**

**Leg B (machine; instances no runner has ever built).** All four runners'
rosters use p ∈ {2,3,5}. I built **two p = 7 stages** through the frozen
instrument's own `Stage` constructor (read-only, in-memory, nothing staged):
**X7A** (m = 1, E = 6, reads (2,1,1),(3,1,1), g_m = 1, e_m = 3, K = 𝔽₇) and
**X7B** (m = 1, E = 6, reads (3,1,1),(2,1,2), ψ₁ = y²+1 irreducible /𝔽₇,
g_m = 2, e_m = 2, K = 𝔽₄₉), and tested the note's clauses on the full E×E
anchor grids: w(π) = E on both; JC-PER byte-identity at k = 1,2 + s-tuple
periodicity + u₁-shift (24 checks); JC-FIB 6-tuple bijection (both); JC-ANCHMON
slot set {0} on all 12 anchors; **JC-SPAN slot set == {δ} with δ ∈ {0,1} on
72/72 grid pairs**; **JC-COB's sharp form u == a_γ·a_{γ′} on 72/72** —
out-of-roster evidence for the MEASURED tier (DMULT-s) at a prime and residue
field (𝔽₄₉) no committed artifact contains; **JC-LOAD's RAW dichotomy on
72/72 solve calls** — on X7A the 12 δ = 1 pairs (δ ≥ g_m = 1, the load set)
all have NO pre-TC-3 scalar and all 24 δ = 0 pairs are RAW-solvable; on X7B
the load set is EMPTY (δ ∈ {0,1} < g_m = 2) and all 36 pairs RAW-solvable,
exactly the g_m ≥ 2 geography of §3.2 consequence 3; W-9(i)/(ii) cocycle +
integer-carry identities on 400 triples. **0 violations anywhere.** And the
adversarial extra §9.2 finding 2 explicitly invited ("a hostile pass should
build g_m ≥ 2 rows with small tables" — the roster has only 2 rows off the
collapse geography): **X7B is a NEW off-collapse-geography row (|K| = 49,
g_m = 2, e₀ = 3) with a decidable table (E = 6 ≤ 8)**, and the r0 battery's
own `adjudicate` (fresh import) returns **NOT-CYCLIC (3 distinct non-1
values)** — JC-CYC(d)'s OPEN inclusion "CYCLIC ⟹ collapse geography"
survives a fresh instance it was never tested on, by JC-CYC(b)'s obstruction
mechanism, exactly as the note predicts for the generic composite situation
(X7A, in the collapse geography, comes back CYCLIC — also consistent). ✓

### A4. Charge (4): statement-level truth sweep — W-6..W-9 boxes and the tier displays, TRUE AS FENCED at HEAD

* **W-6 box.** (i) JC-DOM/JC-GAUGE — both proofs re-checked (JC-GAUGE
  decorrelated, A3). (ii) The corrected `A_ν ≅ B_n` display + the
  strictly-bigger parenthetical: I re-derived the "grows strictly …
  infinitely often" claim independently — maxslot(n+kE) is unbounded in k
  (⌊λ/γ_{m+1}⌋ grows linearly, s_NR is E-periodic) and JC-BSURJ's own
  construction realizes every slot with β_j ≥ wΦ_m, so dim_{K_m} gr_{n+kE}
  → ∞ and the injective transitions cannot be eventually onto; the R1-BND
  ladder census ([0,0,1,1] etc.) is its machine shadow. (iii) JC-PER —
  fresh p = 7 leg. (iv) JC-LOAD — fresh p = 7 leg, both directions, load
  set caught. (v) JC-PSIKER — witness re-read, (ii)/(iii) quantifiers as
  repaired. Grade lines: the r0 input list is superseded by [r1]
  "input-list-only" exactly as flagged, and the [r1] line's
  "(IN-3)(a)(b)(e) + (IN-5) unchanged" is consistent with the [r5, G-2]
  completed stack. **TRUE as fenced** (JC-BOX-4 carries the corner).
* **W-7 box.** OB-2 (JC-PER, byte-exact — fresh leg ✓); OB-3
  EXISTENCE+STRUCTURE "PROVED on ALL window pairs" with the sharp form
  fenced at e_m ≥ 2 → JC-BOX-4 (whose [r1] second proof closes all e_m = 1
  cases on (DMULT-w), no g_m hypothesis — internally consistent); OB-3
  VALUE on exactly [ILN]†'s stratum via W-8 + (IN-1); OB-4's [r2, G-4]
  regenerated grade line true (the Δ-module input measured in digit form:
  R1-DMULT 2,784/0, R1-COB 869/869, R2-BIL 261 — all reproduced this pass,
  + my 72/72 out-of-roster COB); OB-5's architecture discharge with the
  G8 call-site disclosure. Germ split: H-D REFUTED 138/669 and the 27-stage
  val law — both figures reproduced from the instrument this pass. **TRUE
  as fenced.**
* **W-8 box.** Input list consistent with §2.10's tier split ((c) entering
  only through (DMULT-w) on B); P5-OB6 0/669 reproduced; the b_×
  tier-blindness (same constant both sides, ω symmetric) re-read — PE5's
  re-derivation stands, nothing moved since. **TRUE as fenced.**
* **W-9 box.** (i)/(ii) machine-checked on 400 fresh triples (A3); (iii)
  the twisted-group-algebra display (PE5's decorrelated item) unchanged;
  (iv) re-derived: β_{k+1} = β_k·c(1,k) with β₁ = 1 gives v^E =
  ∏_{k=1}^{E−1}c(1,k)·[φ₀] = ζ_T, and JC7's E-fold chain matched the orbit
  product on all 15 E ≤ 8 rows in this pass's re-run. **TRUE.**
* **The (DMULT-w)/(DMULT-s) tier displays.** The (DMULT-w) derivation
  re-checked line by line (ω = c_{λ+μ}/(c_λc_μ), the coboundary of the
  line-wise unit system; nothing gives ω ≡ 1); the κ = 1 pinning re-checked
  (t = in(π^k), ρ^B_0(t) = 1 by JC-PER + φ₀ = 1, JC-PIINV(c) exact, κ
  line-only so the special t pins all t); the consumer split re-read
  against every site — a 127-line DMULT grep classified: **every
  (DMULT-s) site carries measured/tier/blast-radius language; no live
  proof consumes (DMULT-s) as cited**; JC-BOX-3 items 1–3, JC-BOX-4's
  two-footprint closure, the §10.2 [r2] stack, W-6/W-7/W-8's grade lines,
  §9.3 finding 1 and §9.4's "does NOT convert (DMULT-s) to CITED" all
  state the same two-tier system. TR-3′-GEN's quotation stands in its
  [r3, G-6]-corrected form. **CONSISTENT AND TRUE.**

### A5. Dangling-observation sweep (nothing silently abandoned)

* **PE1 §C7 / the c_val ↔ [ILN]† tie**: re-verified at source this pass —
  `ITERLAWN_PROOF_2026-08-08.md` L210: "c_{n+1}(γ,γ′) := val(φ_γ·φ_{γ′}) /
  val(φ_{γ+γ′})" — the note's c_val verbatim. Still cleared-but-unwritten
  in §3.3 (r6 did not touch it, nor was it asked to). Stands.
* **R1-PSIK-HI's uncapped prereg quote vs NU_CAP 8**: disclosed in the same
  table's verdict cell + runner docstring. Stands as disclosed.
* **(IN-2) declared, consumed only at J-C(i)**: safe-direction
  over-declaration. Stands.
* **JC-BOX-3 item 2, the printed-source numbering Codex leg**: still owed,
  still boxed, still honestly displayed at every FGMN citation site.
* **PE6's two ungraded parentheticals** ("JC-DOM's proof twice" as PE5's
  transcribed wording; FGMN (a)/(b) entering via the same §S6a quotation
  the owed leg covers): both re-read; both remain sub-minor transcription/
  coverage notes with the sources visible; not re-gradeable.

---

## §M MACHINE LEG (mandatory; re-run this pass, nothing edited)

Nothing in the repo was modified by this pass except this report file. All
runs from the working tree at HEAD. **All four legs RUN** (no NOT-RUN legs).

### (a) Seals, md5s, commit shape

* Note **byte-identical** at `4b804b4` and HEAD (`git diff` 0 lines);
  `4b804b4` touches ONLY the note (116 insertions / 9 deletions) —
  "batteries + instrument BYTE-FROZEN" literally true. ✓
* md5s at HEAD, all at their sealed values: r0
  `adb555e1134d3ae0b0174d62e8b3446c`, r1
  `7f896bfa27d06158f95c5987c7299770`, r2
  `c02bf06029a72259512ea005bd2562fd`, instrument
  `03811b695cf7aa1bd5b52d5b0cd8bcd6`. ✓

### (b) The three batteries + instrument — all reproduced, exit 0

* **r0** `grt_jc_checks.py`: exit **0**, 2.0 s, 0 violations, silent teeth
  NONE; stdout **exactly byte-identical** (0-line diff). 8,566 samples /
  10 families (JC1 2,594 … JC8 898), teeth 103+285+4+29+633 = **1,054
  firings**, JC3 slot-span 609/609, cyclic split 6/14/9 with the six named
  rows, E-fold chain matched on all 15 E ≤ 8 rows.
* **r1** `grt_jc_r1_checks.py`: exit **0**, 2.6 s, 0 violations; stdout
  differs on FOUR per-row wallclock digits only (C3A 0.3→0.4, C3G 0.6→0.7,
  C4C 1.1→1.2, I4A 1.7→1.8). R1-DMULT 2,784, R1-COB 869 pairs, R1-UNIT
  869/0/0/0, PSIK 197/197, teeth 29+29+1,392+29+406 = **1,885**, TOOTH-ROW
  145 — the [r2, G-8] decomposition exactly.
* **r2** `grt_jc_r2_checks.py`: exit **0**, 7.4 s, 0 violations; stdout
  differs on TWO wallclock digits only (C3G 0.9→1.0, C4H 3.0→3.1). 3,655
  rows, U1 **261/261**, U2 **261/261**, U2 on r1-tested pairs **0**, dense
  bilinear content on exactly C2I/C4I.
* **instrument** `grt_jc_probe.py`: exit **0**, 18.3 s, total violations 0;
  stdout **exactly byte-identical** (0-line diff). P5-OB6 0/669, P1-RAW
  134 == 134, H-B 215 / H-C 73 / H-D 138 of 669, MT2 14/6/9 — the note's
  figures.
* `git status verification/openmath/` after all four re-runs: **clean** —
  every committed JSON artifact reproduced byte-for-byte. ✓

### (c) Figures vs the note — every headline cell checked this pass

§9.2's table (samples per family, the JC8 re-label, MJ firings, the cyclic
split and its six rows), §9.3's table + [r2, G-8] decomposition + the three
findings' figures (c_π value set {1, z̄ᵃ}, a ∈ {1,2,3,4,6,8}, 9/20 split),
§9.4's verdict block (261/87/2,813/58, the C2I/C4I census), §3.3's germ
figures (27 stages, 138/669), §3.5's MT3 figures (197/206, 9 escapes), and
§2.9's 29-row window-base list — all match the re-run outputs and committed
artifacts. The fresh-instance leg (§A3 leg B) adds 144 grid-pair checks + 24
periodicity checks + 400 triple checks at p = 7 with 0 violations — OUTSIDE
every committed artifact's parameter range.

---

## §C WHAT SURVIVED THE PASS (beyond §A; re-checked, no defect found)

1. **The [r6] S-STATUS + repair block** — every figure, hash, and quoted
   fragment resolves at source (PE6's verdict figures, its §A1/A2/A3/A4
   claims, the honest r0/r2/instrument byte-identity qualification).
2. **The [r6, G-1] annotation** — both historical clauses verified at
   `edbb966` (round-record language absent; the designation in force) and
   the inversion verified r5-bred at `3870bc8` (§A1); the current-stack
   pointer and the "superseded by nothing" claim true at HEAD.
3. **The [r5, G-2] parenthetical's corrected characterization** — matches
   what [r4, G-1] actually does, byte-checked against the bracket.
4. **The strike system** — 116/0, all r6 keys placed ([r6, G-1] at §0 + the
   [r5, G-2] interior + the group-12 pin + S-STATUS/arc/grade-delta), the
   struck [r5] arc display preserved verbatim inside its strike.
5. **Header/status hygiene** — counter 0/2 at all 44 occurrences; no gate
   fires/retires (J3b BLOCKED-ON-CARRIER-TIE displayed, not retired; the
   GRTW2/J-A/J-B 0/2 fences ride); no density/menu/count statement;
   JC-BOX-2/JC-BOX-8(i) residues still displayed as having no machine leg.
6. **The census self-reference discipline** — the r6-added lines are
   census-record under the disclosed conventions and the note nowhere cites
   a stale count as current (PE6's 172 is attributed and past-tense; my own
   execution at HEAD returns 177 with all five additions record/annotation).

## OBSERVATIONS (ungraded; recorded so they do not dangle)

1. The [r6, G-1] annotation's parenthetical "(FGMN (a)(b) + (DMULT-w) on B +
   Thm 4.8/Cor 4.9 + Cor 2.7)" glosses the FGMN ENTRY of the completed
   stack, not the whole stack (which also carries [ILN]†/GRB/W-1..J-B); the
   authoritative reference is the pointer to §10.2 [r5, G-2], the bracket's
   subject is the FGMN footprint, and PE6 §A2 used the same compression.
   Not a defect.
2. W-8's [r2, G-4] grade-line gloss "(FGMN (b)(e) + (c)-only-through-
   (DMULT-w))" names the clause's DIRECT citations; (a) enters W-8 only
   through JC-DOM/B, whose own grade line (W-6 [r1]) and the completed
   stack both carry it. Per-clause direct-input convention; the system
   footprint is correctly displayed at the stack. Not a defect.

---

## §R RECOMMENDATION

**CLEAN: 0 CRITICAL, 0 GAPS.** The r6 diff is exactly PE6's prescription,
executed faithfully with the arc's own conventions, and every historical
claim inside it is true at its pinned commit. The pointer-record system —
the last surface with a live defect — is now self-consistent at HEAD. Per
the acceptance rule this pass STARTS the count; advancing the counter to
1/2 is the orchestrator's ledger action. **JC-PE8 is the acceptance pass**:
a fresh hostile read of the whole note at HEAD (no diff to lean on), with
the weakest mathematical links unchanged and still honestly ranked at §10.2
[r2] — (1) (DMULT-w) at composite order + W-1's transport (TR-3′-GEN open),
(2) JC-BOX-2's off-stratum existence claim (proof-only, zero machine
support), (3) the non-integral residue JC-BOX-8(i), (4) (DMULT-s)'s
measured-only status under JC-COB's sharp displays, (5) the top-flat corner
(JC-BOX-4, closed only on (DMULT-w)), (6) JC-F1/JC-F2 REVIEW-OWED. My
out-of-roster p = 7 leg (X7A/X7B, §A3) is available as a template if PE8
wants a wider fresh-instance net; the alt-corrected dense variant named at
[r3, G-3] remains NAMED, NOT BUILT.

— GRTJC pass PE7, hostile verifier unit (fresh context), fixes nothing.
