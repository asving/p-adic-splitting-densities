# GRTJC pass PE5 — HOSTILE VERIFICATION REPORT (fresh context; fixes nothing)

**Target:** `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md` **at HEAD**, i.e.
after the r4 NOTE-ONLY round (commit `edbb966`: the final alias sweep — §0
stack's fourth alias struck + re-pointed, the §0 (c) content-line annotation,
the union-pattern census 144 = 42/28/74 audited by content, the two JC-LOAD
constant displays re-tiered to b_× = a_{λ+N}/(a_λa_N), the §10.1 arc brought
forward with the grade-deltas convention lines; note byte-identical
`edbb966` → HEAD, verified). Runners: `grt_jc_checks.py` (r0),
`grt_jc_r1_checks.py` (r1), `grt_jc_r2_checks.py` (r2), instrument
`grt_jc_probe.py` — all in `verification/openmath/`, all BYTE-FROZEN at r4 as
claimed (md5s verified; `edbb966` touches ONLY the note, 230 insertions / 12
deletions).
**Verifier role:** quote-and-classify only. CRITICAL ERROR = breaks the logical
chain (dependents not checked further); JUSTIFICATION GAP = assume and continue.
Fences and boxes are graded as part of the statement.
**Pass date:** 2026-08-06 wallclock (campaign 2026-08-08). **FIFTH acceptance
attempt** (two consecutive clean passes accept; a clean pass here would start
the count).

## VERDICT

**0 CRITICAL · 2 GAPS + 1 minor — NOT CLEAN.** Counter stays **0/2**.

**The r4 diff's mathematics is sound.** I re-derived the [r4, G-3] re-tiering
from the note's own machinery and it is exact — sharper than PE4 §A1, and
correctly so: at E | N the anchor at line N is π^{N/E} (JC-PER), so
A(λ,N) = ρ_{λ+N}(in φ_λ·in π^{N/E}) = ρ_λ(φ_λ) = 1 EXACTLY by JC-PIINV(c),
proved not cited, which pins the multiplier to the anchor coboundary
b_× = a_{λ+N}/(a_λa_N) = ω(λ,N) on (DMULT-w) alone; both sides of the iff use
the pair (γ+γ′, N), the unit cancels, tier-blind (§A1). I re-executed the
union-pattern census at HEAD: **144 hit-lines exactly**, and my independent
line-by-line classification lands on **42 LIVE / 28 STRUCK / 74 RECORD** —
bucket for bucket, with all twelve content groups' line sets reproduced and
the LIVE bucket's content audit verified (zero live hits state the refuted
content; the 74-RECORD sub-itemization sums and locates exactly) (§A2). The
arc-accounting system is now CONSISTENT at HEAD for the first time in the arc
— every commit hash verified in `git log`, one current arc display in the
header and one in §10.1, both ending "JC-PE5 next", the [r3]/[r4] grade-delta
convention lines present and true (§A3). The strike system holds: **108 `~~`
tokens, zero odd paragraphs**, all four [r4, G-#] keys placed at their sites,
nothing silently deleted (§A5). Machine legs 4/4: all three batteries + the
instrument re-run **exit 0, 0 violations**, stdout byte-identical to the
committed artifacts except wallclock digits (r2 EXACTLY byte-identical), every
committed JSON reproduced byte-for-byte, md5s at their sealed values (§M).

The two gaps are both in the census/stack RECORD surface, not in any proof:

* **GAP 1** — the r4 census's own protocol remark is **false on its own
  grep**: it claims the two added-for-completeness patterns (`Theorem 4.2`,
  `4.8`) "contribute no hit-lines of their own … all such lines are …
  RECORD by construction", but `4.8` alone contributes FOUR hit-lines
  (union-minus-`4.8` returns 140, not 144), of which THREE are lines the
  census's own groups 1 and 10 itemize as LIVE and one is STRUCK — the
  sweep-record-misreports-its-own-machine-checkable-claim species ([r3, G-2],
  PE4-on-r3-headline) in its third recurrence, inside the block that was
  written to end it.
* **GAP 2** — the un-repaired HALF of PE4's GAP 1: every one-line stack
  display at HEAD still omits FGMN clauses **(a)/(b)** from the cited
  footprint — §0's repaired one-liner now reads "FGMN ~~(c)~~(d)(e) CITED"
  and §10.2's [r1]/[r2] "current form" stacks name only (DMULT) + Thm
  4.8/Cor 4.9 + Cor 2.7 — while the note's live proofs consume (IN-3)(a)
  and (IN-3)(b) as cited literature (JC-DOM, JC-LOC/G6, (MULT-B)), and the
  r4 census itself certifies those consumptions LIVE (its groups 2, 4, 6).
  PE4 stated this omission verbatim inside GAP 1; r4 repaired the alias and
  left the omission.

Minor (m-1): the re-set RHS display "ranges exactly over b_×·{polynomials of
degree < g_m} as c ranges over K^*" is strictly false at the zero polynomial
(unattained for c ∈ K^*); the [r4, G-3] bracket's own parenthetical uses the
correct "{nonzero polynomials…}" form.

---

## §A WHAT I RE-DERIVED (the charges, checked to the bottom)

### A1. Charge (1a): the [r4, G-3] re-tiering — SOUND and EXACT; the A(λ,N) = 1 pinning verified on the note's own lemmas

The bracket's claim, re-derived from scratch on the declared footprint
((MULT-B)|gr riding (DMULT-w) + the in-note lemmas):

* **b_× is the true multiplier.** (MULT-B)|gr at the pair (λ, N), λ := γ+γ′:
  𝑅_{λ+N}(f·X_N) = a_{λ+N}·A(λ,N)·ρ_λ(f)·ρ_N(X_N). 𝑅_N(X_N) = 1 EXACTLY
  (JC-SCAL(b) + R3 + K_m ↪ K injective on constants — §4.1, tier-blind), so
  ρ_N(in X_N) = 1/a_N.
* **A(λ,N) = 1 exactly, via JC-PER + JC-PIINV as the bracket says.** E | N
  gives φ_N = π^{N/E} (JC-PER, φ_0 = 1), so A(λ,N) = ρ_{λ+N}(in φ_λ·in
  π^{N/E}) = ρ_λ(φ_λ) = 1 by JC-PIINV(c) (ρ exactly π-invariant — PROVED, the
  same mechanism as (COORD-B)(2)'s κ = 1 pinning, correctly attributed).
  Both lemmas are in-note theorems, so the pinning adds NO conditionality.
* Hence 𝑅_{λ+N}(fX_N) = [a_{λ+N}/(a_λa_N)]·𝑅_λ(f) = b_×·𝑅_λ(f), with
  b_× ∈ K_m^* — and comparing with (DMULT-w) applied to (f, X_N), b_× =
  ω(λ,N), so "b_× = 𝑅(X_N) (= 1) exactly when ω(λ,N) ≡ 1, i.e. on (DMULT-s)"
  is exactly right. Consistent with PE4 §A1's multiplier
  [A(λ,N)·a_{λ+N}/(a_λa_N)] (PE4's GAP-3 text itself asserted the pinning).
* **Same constant both sides.** LHS multiplies φ_γφ_{γ′} ∈ gr_λ by
  X_N ∈ gr_N: pair (λ,N). RHS multiplies φ_λ ∈ gr_λ by Λ_N(c) ∈ gr_N: pair
  (λ,N) (ω symmetric, as the bracket notes, covering the ordering). RHS range
  = b_×·a_λ·{𝑅_N(Λ_N(c))} = b_×·{nonzero canonical degree-<g_m reps} — the
  a_λ absorbed because a unit constant scales that set bijectively, the
  mechanism the second bracket states. LHS = b_×·u·y^δ. b_× cancels; the iff
  "solvable ⟺ δ < g_m" is tier-blind. ✓ (The one wording residue is m-1.)
* λ+N ∈ W so a_{λ+N} exists: u_1(λ+N) = u_1(λ) + N/E ≥ 0. ✓

### A2. Charge (1b): the union-pattern census — REPRODUCED EXACTLY; all 12 content groups audited; ONE false protocol remark found (GAP 1)

* **Count**: `grep -c '(IN-3)\|Thm 4\.2\|Theorem 4\.2\|FGMN\|4\.8\|Cor 2\.7\|(COORD)\|(MULT)'`
  at HEAD (= the committing state, note byte-identical) returns **144**. ✓
* **Independent classification, all 144 lines**: my own pass lands on
  **42 LIVE / 28 STRUCK / 74 RECORD** under the disclosed conventions.
  LIVE by group (line numbers at HEAD): g1 = {381, 383, 384, 389, 401, 403,
  405, 427} (8); g2 = {541, 542, 553} (3); g3 = {671} (1); g4 = {864, 877,
  895, 902, 911, 914, 924, 928/929} (8); g5 = {1023, 1024, 1036, 1052, 1056}
  (5); g6 = {1119, 1156} (2); g7 = {1377, 1398, 1399} (3); g8 = {1440} (1);
  g9 = {1594, 1598} (2); g10 = {1793, 1801, 1802, 1804, 1809, 1817} (6);
  g11 = {1851} (1); g12 = {2448, 2459} (2). RECORD sub-itemization: headers
  13 = {125,132,151,168,169,171,213,218,219,221,228,294,318}; §0 [r4]
  brackets 3 = {393,394,430}; W-6 box 3 = {518,527,531}; §2.10 narratives 6;
  JC-BOX-3 verdict narrative 2 = {1789,1790}; consumers row 1 = {1235};
  R1-BND 2 = {2003,2050}; §10 histories 4 = {2412,2435,2443,2445} (2438 sits
  INSIDE the ~~weakest links~~ strike → STRUCK; 2429's hits inside `~~…~~` →
  STRUCK per the disclosed convention); §9.5 records 40 (13 + 6 + 21 across
  the r2/r3/r4 blocks — exact). Sums: 74 RECORD, 28 STRUCK. **Bucket for
  bucket with the census.**
* **Content audit spot-verified on groups 1, 2, 4, 5, 9, 10, 11, 12** (well
  past the charge's four): every audited line SAYS what the census says it
  says — declaration lines about FGMN's own objects (g1, incl. the §S6a
  quotation), never-refuted (a)/(b)/(e)/(d) consumptions within hypotheses
  (g2/g3/g6/g9), the JC-LOC re-route and tier split (g4/g5/g7/g8/g12), and
  the fences (g10/g11). **Zero live hits state (IN-3)(c)-on-gr, (COORD),
  (MULT), the Thm-4.2-on-gr_{O[x]} transport, or the bare "FGMN (c)" stack
  alias — confirmed independently.**
* **The protocol remark is FALSE for `4.8`** — GAP 1 below. (`Theorem 4.2`'s
  half is true: 2 hit-lines, both pattern displays; and the [r4] annotation
  in the [r3] block — "0 hits before r4" — verified at `126c33f`: 0.)
* The [r4, G-4] content-line annotation at §0(c): accurate against §2.10
  [r1, F1] and JC-BOX-3 [r1] ("only through JC-LOC, as (DMULT-w) on B ≅
  gr_{K[x]}(w)"), and the disclosed protocol limit ("counts hit-LINES by
  NAME … cannot certify the absence of further such lines by grep") is the
  honest form PE4 asked for. ✓

### A3. Charge (2): the arc-accounting system at HEAD — CONSISTENT, first time in the arc

* **[r4] S-STATUS** (CURRENT): FOUR passes, FOUR rounds ✓. Every recorded
  hash verified in `git log` with matching subjects: PE1 `1a27be3`, PE2
  `4a76d52`, PE3 `e4b6fbf`, PE4 `d5072b6` (0 CRITICAL + 4 gaps ✓), r1
  `85d5811`/`54904cc` + mini-seal `f45b63c`/`66263ce`, r2 `5742e25` +
  `79611a4`/`db12666`, r3 `126c33f`, seal/verdict `6ad01d1`/`8f07904`,
  instrument `7212e56`/`fc89b03`. ✓
* **Supersession chain**: [r1] struck; [r2] and [r3] blocks annotated
  SUPERSEDED (kept for their ARC displays, reason stated); the interior
  "JC-PE3/JC-PE4 = next" lines live only inside annotated-superseded blocks.
  The two CURRENT displays (header, §10.1 [r4, G-2]) agree: "JC-PE5 next". ✓
* **§10.1**: the [r2] arc is now struck (the convention r2 set), the
  extended arc's figures match the reports (PE3 0C+8G, PE4 0C+4G), and the
  missing "[r3] Grade deltas: NONE" / "[r4] Grade deltas: NONE" lines are
  present and TRUE (r3/r4 diffs move no grade cell and no measured quantity
  — verified against both diffs; r4's commit touches only the note). ✓

### A4. Charge (3): fresh-eyes sweep over the four reports' re-derivation complement — no defect found

* **W-9(iii)** (the twisted-group-algebra display — in NO report's
  re-derivation list; PE4 §A5 covered (i)(ii), PE1 §C6 covered (iv)):
  re-derived. 𝒜(T) = ⊕_ν K·[φ_{γ_ν}] (W-7's Ψ bijective), [φ_{γ_ν}][φ_{γ_μ}]
  = c(ν,μ)[φ_{γ_{ν+μ}}] with c descending to ℤ/E (JC-PER) and c(ν,μ) ∈ K^*
  (JC-CARRY-m: (u/a)·z̄^δ, all units since ψ_m(0) ≠ 0), cocycle identity =
  (i). That IS K^c[ℤ/E]; "restatement of W-7's Ψ" is a correct proof. ✓
* **JC-F1's basis algebra**: v^{k+1} = β_k·c(k,1)[φ_{γ_{k+1}}] with c
  symmetric gives β_{k+1} = β_k·c(1,k) ✓; v^E = ζ_T = ∏_{k=1}^{E−1}c(1,k) ✓;
  distinct ℤ/E-degrees ⟹ independence ⟹ K[v]/(v^E − ζ_T) ≅ 𝒜(T) by E = E. ✓
* **§2.2–2.6 proper** (PE1-cleared; re-read fresh): JC-GAUGE's σ
  construction (kernel = (ϑ−1)B^{(ν)} both inclusions) ✓; JC-PER's descent
  induction ✓; JC-FIB's injectivity (l_m invertible mod e_m, descend) ✓;
  JC-ANCHMON's telescoping bound ✓; JC-SCAL via REALIZE ✓.
* **§4.1 conclusion chain** re-derived through (†)/(‡) with the A(λ,N)
  cancellation (Δ a domain) ✓; **§4.3** by construction ✓; **§3.3
  JC-INNER** = W-8 ∘ [ILN]† on the stratum, second form by K_m ↪ K ✓.
* **§7's table** vs the reproduced artifacts: row 4's 134/669 printed by the
  probe re-run this pass ("no-solution pairs 134 == delta>=1 pairs 134"),
  H-B 215 / H-C 73 / H-D 138 match §3.2/§3.3's figures exactly; row 1's
  g_m ≥ 2 census (C2I/C4I only) matches R1-CEN. ✓
* **§9.1/9.2 family sums**: 2,594+570+2,484+24+443+855+116+581+898+1 =
  8,566 ✓; tooth firings 103+285+4+29+633 = 1,054 ✓.

### A5. Charge (4): strike system [r1..r4] — BALANCED, 108 tokens

**108 `~~` tokens at HEAD; 0 paragraphs with an odd count** (python
paragraph-split check, this pass) — the claimed figure, balanced. r4 added
10 tokens (96 at PE4 + the (c) strike ×2, the two 𝑅(X_N)→b_× strike-pairs
×6, the [r2] arc strike ×2). [r4, G-#] brackets at their sites: G-1 ×7
(disposition + §0 + census), G-2 ×2 (disposition + §10.1), G-3 ×2 (the two
§2.8 brackets), G-4 ×5 (disposition + §0 content line + census disclosure),
plus the one [r4 —] annotation in the [r3] census block. Nothing silently
deleted — every r4 strike carries its superseding bracket with the struck
wording preserved.

---

## GAP 1 — the r4 census's protocol remark is FALSE on its own grep: `4.8` DOES contribute hit-lines of its own, and they are LIVE lines of the census's own itemization, not "RECORD by construction"

**Offending passage (verbatim), §9.5 [r4, G-1]:**

> (the last two excluding `-B` forms, as always; the two names added only for
> completeness — the spelled-out variant of the theorem number and the bare
> numeral — contribute no hit-lines of their own: every line containing
> either also carries another swept name, and all such lines are the
> sweep-protocol displays and this census's own itemization, RECORD by
> construction; …)

Machine check, this pass: the union pattern returns **144**; the union with
`4.8` removed returns **140**. The four `4.8`-only hit-lines (verified to
match NO other swept name) are **L383** and **L401** (§0's §S6a quotation
line and (d)'s `[Thm 4.8 / Cor 4.9]` tag-line — both itemized LIVE by the
census's own group 1: "the §S6a pinned quotation (two lines…)", "(d)'s
`[Thm 4.8 / Cor 4.9]`"), **L1801** (JC-BOX-3 [r1] item 1 — LIVE, group 10),
and **L1782** (inside the struck r0 JC-BOX-3 — STRUCK). So both halves of
the remark fail: `4.8` contributes four lines of its own, and none of them
is a sweep-protocol display or RECORD. The census's TOTALS are unaffected
(they come from the executed grep, and the group itemization correctly
carries these lines as LIVE) — the false statement is the redundancy claim
about the census's own pattern, i.e. exactly the species [r3, G-2] repaired
(a sweep record misreporting its own machine-verifiable figure) in its THIRD
recurrence, this time inside the block headlined "the species ended the
census way". A reader trusting the remark would shrink the pattern by `4.8`
and lose two LIVE declaration lines and a LIVE fence line from every future
sweep. **Classification: JUSTIFICATION GAP** (false machine-checkable
protocol remark inside the census record; fixed point and totals verified
unaffected).

## GAP 2 — every one-line stack display at HEAD still omits FGMN (a)/(b) from the cited footprint: the half of PE4's GAP 1 that r4 did not repair

**Offending passages (verbatim).** §0 (post-r4):

> `… + FGMN ~~(c)~~(d)(e) CITED + W-1/W-2/J-A/J-B ATTEMPT (0/2)`,

and §10.2 [r1] (the "current form" the [r4, G-1] bracket points to):

> `… + (DMULT) on B [= FGMN Thm 4.2's content via JC-LOC] + Thm 4.8/Cor 4.9
> + Cor 2.7 CITED (numbering re-verification still owed) + …`

PE4's GAP 1 said, verbatim: "(and it lists (c)(d)(e) while the note also
consumes (a)(b) — JC-DOM, JC-LOC, G6 — so it is not even the right r0
list)". At HEAD the note's live proofs consume **(IN-3)(a)** (JC-DOM's proof
twice; JC-LOC's G6-1/G6-3) and **(IN-3)(b)** (JC-DOM, JC-LOC's proof,
(MULT-B) and its |gr display) as CITED literature — the r4 census itself
certifies all of these LIVE (groups 2, 4, 6) — yet no one-line stack display
names (a) or (b): §0's lists (d)(e); §10.2's [r1]/[r2] stacks list
(DMULT) + Thm 4.8/Cor 4.9 + Cor 2.7. The [r4, G-1] bracket asserts "§10.2's
[r1]/[r2] stacks … say … what is true", transferring authority to displays
that carry the same omission. Nothing false is concluded — the (IN-3)
declaration block five lines up carries (a)/(b) as CITED, and W-6's [r1]
grade line says "(IN-3)(a)(b)(e) + (IN-5) unchanged" — but the note's
summary conditionality displays understate the literature footprint by two
consumed clauses, three rounds after PE4 printed the observation.
**Classification: JUSTIFICATION GAP** (incomplete repair of a reported
display defect; one-word fixes at the three stack displays).

## m-1 (minor) — the re-set RHS display's "exactly" claim includes the unattained zero polynomial

§2.8 (post-r4): "by JC-SCAL(a)(c) the RHS ranges exactly over
**b_×**·{polynomials of degree < g_m} as c ranges over K^*". For c ∈ K^* the
canonical representative is never 0, so the attained set is
b_×·{NONZERO polynomials of degree < g_m}; the [r4, G-3] bracket's own
parenthetical states the correct nonzero form. Inherited r0 wording, re-set
by r4's strike-and-replace; harmless to the iff (the LHS b_×·u·y^δ is
nonzero). **Minor wording defect**, noted because r4 re-displayed the line.

---

## §M MACHINE LEG (mandatory; re-run this pass, nothing edited)

Nothing in the repo was modified by this pass except this report file. All
runs from the working tree at HEAD.

### (a) Seals, md5s, commit shape

* Note **byte-identical** at `edbb966` and HEAD (`git diff` empty); r4
  touches ONLY the note (230 insertions / 12 deletions, no `verification/`
  file, no `.lean`). "batteries + instrument BYTE-FROZEN" literally true. ✓
* md5s at HEAD, all at their sealed values: r0
  `adb555e1134d3ae0b0174d62e8b3446c`, r1
  `7f896bfa27d06158f95c5987c7299770`, r2
  `c02bf06029a72259512ea005bd2562fd`, instrument
  `03811b695cf7aa1bd5b52d5b0cd8bcd6`. ✓

### (b) The three batteries + instrument — all reproduced, exit 0

* **r0** `grt_jc_checks.py`: exit **0**, 2.0 s, 0 violations, silent teeth
  NONE; stdout vs committed output byte-identical except ONE per-row
  wallclock digit (I4C 0.9→1.0). Headlines: 8,566 samples, 10 families,
  1,054 firings, cyclic split 6/14/9 — as committed.
* **r1** `grt_jc_r1_checks.py`: exit **0**, 2.6 s, 0 violations; stdout
  byte-identical except ONE wallclock digit (C3A 0.4→0.3).
* **r2** `grt_jc_r2_checks.py`: exit **0**, 7.4 s, 0 violations; stdout
  **byte-identical**. U1 261/261, U2 261/261, R2-BIL 261 dense pairs,
  deg-3 dense 29/29 — as the §9.4 cells state.
* **instrument** `grt_jc_probe.py`: exit **0**, 18.2 s, total violations 0;
  stdout differs on FOUR wallclock digits only. P1-RAW 134 == 134 (0), P3
  inner ≠ 1 on 215, H-B 215 / H-C 73 / H-D 138 of 669 — the note's figures.
* `git status verification/openmath/` after all four re-runs: **clean** —
  every committed JSON artifact reproduced byte-for-byte. ✓

### (c) The r4-added figures — every one checked this pass

* Union census **144** at HEAD ✓; independent classification **42/28/74**
  bucket-exact ✓; RECORD sub-itemization sums 13+3+3+6+2+1+2+4+40 = 74 and
  locates ✓; `Theorem 4.2` = 2 lines (both pattern displays) ✓, = 0 at
  `126c33f` ✓; **`4.8` contributes 4 own hit-lines — GAP 1** (the one
  r4-added figure-claim that FAILS).
* r3-pattern reference figures re-verified: 90 at `126c33f` ✓ (and 101 at
  HEAD, moved by the r4 record text itself — consistent with the census's
  grep-at-committing-state discipline).
* Strike tokens **108**, odd paragraphs **0** ✓. Arc hashes: 16/16 verified
  in `git log` (§A3). ✓
* b_× re-derivation: §A1 (mathematical, not numerical — the machine leg for
  the display is the frozen R1-COB/R2-BIL families, unchanged).

---

## §C WHAT SURVIVED THE PASS (beyond §A; re-checked, no defect found)

1. **The [r4] S-STATUS + disposition block** — every figure and hash exact;
   the note-only discipline literally verified (commit shape).
2. **The [r4, G-4] content-line annotation** — accurate against §2.10
   [r1, F1] and JC-BOX-3 [r1]; the disclosed NAME-pattern protocol limit is
   the honest form, and its §0-read-through discharge claim is consistent
   with my own read of the input block.
3. **The [r4, G-2] arc extension** — figures match the four reports; the
   convention lines true.
4. **The [r4, G-3] brackets** — both mathematically exact (§A1); "PE4 §A1
   verified this; transcribed" is honest attribution.
5. **W-9(iii), JC-F1's algebra, §§2.2–2.6, §4.1–4.3, §3.1–3.4, §7's table**
   — the fresh-eyes complement, all re-derived or re-checked clean (§A4).
6. **Header/status hygiene** — counter 0/2 at every occurrence; no gate
   fires/retires; no density/menu/count statement; JC-BOX-2/8(i) residues
   still displayed as having no machine leg on any runner.

---

## §R RECOMMENDATION

**Not clean; 0 CRITICAL, 2 gaps + 1 minor; counter stays 0/2.** The
mathematics r4 touched is exact — the b_× re-tiering is the sharpest form
of that display the arc has produced, and the census's totals, buckets, and
content audit all reproduce independently. Both gaps are one-to-three-line
record repairs:

1. **G1:** correct the census's completeness parenthetical to the truth —
   `Theorem 4.2` contributes nothing; `4.8` contributes exactly four
   hit-lines (two LIVE in group 1, one LIVE in group 10, one STRUCK), which
   is WHY it belongs in the union — and drop "RECORD by construction".
2. **G2:** add (a)/(b) to the FGMN entry at the three stack displays (§0's
   one-liner and §10.2's [r1]/[r2] forms), or bracket why they are omitted.
3. **m-1:** "nonzero polynomials" at the §2.8 RHS display.
4. PE6 should re-run the union grep (the count will move with the fixes),
   re-check the two remarks, and — if clean — start the acceptance count.
   The weakest mathematical links remain §10.2 [r2]'s ranking, headed by
   (DMULT-w) + W-1's transport; nothing found this pass moves that ranking.

— GRTJC pass PE5, hostile verifier unit (fresh context), fixes nothing.
