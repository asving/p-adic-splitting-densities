# LIFT-CORNER — NR-1 ((ITER-LAW-LIFT) at g₀ = 1 ∧ δ₁ = 1): the lift-ORBIT transport instrument + the shift-descent compose

**Unit:** LIFT-CORNER (NR-1 of ILNRES S1; spec ILNRES S5.1, price M; route =
the W-2 shift-descent covariance + window-calculus tail bookkeeping).
Wallclock 2026-08-04, campaign date 2026-08-08. Genre: sealed-preregistration
numerics (two-commit seal) + a conditional COMPOSE (S4; written only on a
0-violation verdict, per the probe-first discipline). **Grade cap (read
first): everything this unit proves is at attempt grade 0/2 AND capped by its
W-2 consumption (GRTW2_PROOF, itself attempt 0/2, no acceptance arc run).**

**Machine leg:** `verification/openmath/liftcorner_checks.py` (this header +
the runner commit BEFORE any full run; verdict appended in commit 2 from the
artifacts `liftcorner_checks_output.txt` / `liftcorner_checks_results.json`).
[r1] A SECOND, post-hoc machine leg was added at repair round r1 and is NOT
part of the sealed prediction battery: `liftcorner_tailstab_children.py` +
its committed output `liftcorner_tailstab_children_table.txt` — the
examples-first child-type table the repaired S4.1 induction is derived from
(disclosed as written AFTER the refutation, hence evidence for a repair, not
a prediction). The sealed runner is byte-untouched (md5 unchanged, S3).
[r2] That post-hoc generator was AMENDED at repair round r2 (assertion **A7**
added, curing PE2's G3: the enumerated children now have to reconstruct the
very polynomial A6 develops) and its output recommitted; its r1 data sections
(§§1–6) regenerate byte-identically, A7 adds assertions only. The sealed
runner is STILL byte-untouched at r2 (md5 `ccb4351c92573f5f962cae4ae952d8dd`).
[r3] **BOTH MACHINE LEGS ARE BYTE-FROZEN AT r3** — repair round r3 is
note-level only, and PE3 verified both legs before the round: sealed runner
`git diff dafc0b5 HEAD` = **0 bytes**, md5 still
`ccb4351c92573f5f962cae4ae952d8dd`, exit 0 at 25,409/0; children generator +
its committed table regenerate **byte-identically** (`diff` empty) with A7's
four legs PASS (752 nodes / 5,336 children, 0/0/0/0). No script or table is
touched at r3.
[r4] **STILL BYTE-FROZEN AT r4** — repair round r4 is note-level only, and PE4
re-ran both legs before the round: sealed runner md5
`ccb4351c92573f5f962cae4ae952d8dd`, `git diff dafc0b5 HEAD` = **0 bytes**,
exit 0 at 25,409/0 with every counted family at 0 violations (its output
differs from the committed artifact `liftcorner_checks_output.txt` at exactly
4 wall-clock lines — three per-block stamps plus `elapsed 4.3s` vs `4.4s` —
and the diff is empty under timing normalisation); children generator
regenerates its committed table **byte-identically** (`diff` empty) with A7's
four legs PASS (752 nodes / 5,336 children, 0/0/0/0). No script or table is
touched at r4.

**[REPAIR ROUND r1 — 2026-08-08 campaign (wallclock 2026-08-05).** Applied
against LIFTCORNER-PE1 (hostile pass, fresh context, report
`LIFTCORNER_passPE1_report.md`, commit 30e570c: **1 CRITICAL + 3 gaps**;
ledger entry BRIDGE_ADJUDICATIONS_2026-07-30.md "PE1 VERDICTS"). PE1's
machine leg was bit-identical (exit 0, 25,409/0, fires 1,576, all roster
counts independently re-derived, two-commit seal verified), so nothing in
S1–S3 or in the corner measurement moved; the critical finding is confined
to one line of the S4.1 PROOF. Dispositions, each edit carrying a dated
`[r1, F#]` bracket: **F1** (CRITICAL) — the S4.1 strict-descent clause
"every child has m′ ≤ m−1" is FALSE at the top-mid q-digit child (k = e₀−1,
which sits at m′ = m; PE1's counter-instance reproduced numerically in
S4.1). REPAIRED, statement byte-unchanged, by replacing the single
induction on m with the LEXICOGRAPHIC (m, deg a) induction: the child census
is now displayed in full (seven genres), the one m-preserving genre is proved
to drop deg a strictly, the deg a = 0 stratum is proved to have NO
m-preserving child at all, and BOTH consumers (the induction; the
termination/dev-linearity finiteness) are re-closed on the lex order with an
explicit depth bound. The case list is DERIVED FROM the examples-first
table (standing directive, Asvin 2026-08-05), which is committed with this
round: 29 towers over p ∈ {2,3,5}, d₀ ∈ {1,2,3}, e₀ ∈ {2,…,6} (the e₀ = 2
boundary included), all four lift genres, PE1's counter-instance verbatim —
0 children dropping neither coordinate, and the (LEDGER) conclusion itself
re-verified on the honestly recomputed double development. **F2** — the
wave-18 S1 split b₀ = ĉ′π^{h₀} + t₀ is now defined in-note at first use
(S4 setting), with its source cited inline. **F3** — COR 2's identification
with "W2-OPEN-1 RESTRICTED to the base junction" is WITHDRAWN as underived;
COR 2 is rescoped to exactly what S4 proves (the harness monic-lift orbit),
with a box naming the two things still owed for the W2-OPEN-1 tie.
**F4** — S2 disclosure (c) now says exactly what the runner asserts (full
ψ₁-byte carryover + a one-element K₂ smoke check) and where the
modulus-independence verification actually lives (`mk_field_ext` at g = 1).
[**r3, F-A:** that F4 repair landed on the WRONG HALF of its own sentence —
"full ψ₁-byte carryover" is a snapshot-consistency no-op that cannot fail, and
the demoted one-element K₂ check is the only substantive half of the pair. See
S2 disclosure (c)'s [r3, F-A] bracket; the `mk_field_ext` relocation, which is
where the soundness actually lives, stands.
**[r4, F4-1 — the SECOND half of that r3 sentence is stricken too.]** "the
demoted one-element K₂ check is the only substantive half of the pair" is
FALSE: `C.K2["one"]` is a structural constant of (d₀, g₀, g₁) that never reads
a ψ₁ coefficient, so assert (ii) is as incapable of firing as assert (i).
**BOTH asserts are inert**; nothing in this note consumes either; the
soundness is in `mk_field_ext`'s g = 1 reading. Final description: S2
disclosure (c)'s **[r4, F4-1]** bracket. What survives of r3's F-A is (i)'s
no-op diagnosis and the `mk_field_ext` relocation.]
Acceptance counter unchanged at 0/2 — a repair round is not a pass; round r2
(a fresh hostile pass on THIS text) is the next acceptance attempt.]**

**[REPAIR ROUND r2 — 2026-08-08 campaign (wallclock 2026-08-05).** Applied
against LIFTCORNER-PE2 (hostile pass, fresh context, on the r1 text; report
`LIFTCORNER_passPE2_report.md`, commit 3367f3c: **0 CRITICAL + 5 gaps**;
ledger entry BRIDGE_ADJUDICATIONS_2026-07-30.md "LIFT PE2: THE REPAIR HOLDS").
Naming, since r1's closing sentence used "round r2" for the pass: the hostile
pass on the r1 text was **PE2**; **r2 is this REPAIR round**; the next
acceptance attempt is **PE3**, a fresh hostile pass on THIS text. **F1 IS
CURED and HELD** — PE2 re-derived every load-bearing piece of the lex repair
independently (9 ↦ 7 mapping total and disjoint; row 7b's degree drop correct
at the deg a = 0 and deg b = 0 edges; both emptiness strata PROVED not merely
measured; ρ strictly drops on every edge, so the lex order well-founds both
consumers) and both machine legs re-ran clean at PE2 on the pre-r2 artifacts
(before this round's A7 amendment to the children generator). **[r3, F-C —
"bit-identically" STRICKEN here as an overstatement of PE2's own record.]** The
r2 wording was "both machine legs re-ran **bit-identically** at PE2"; PE2's
report says something weaker for the sealed leg, verbatim: its family table is
"identical line-for-line modulo the `elapsed`/per-block timestamp fields only
(diff of the two outputs with timing normalised is empty)" — the committed
artifact `liftcorner_checks_output.txt` reads `elapsed 4.4s`, PE2's and PE3's
re-runs both printed `elapsed 4.3s`, so the runner's OUTPUT FILE carries
wall-clock fields and is demonstrably not bit-identical across runs. Every
COUNTED quantity is identical (25,409 checks, 0 violations in every family,
1,576 WRONGLET fires, coverage minima, md5). The children-generator table IS
bit-identical (`diff` empty at both PE2 and PE3) — the defect was the word
"both".
**[r4, F4-3 — the PROVENANCE in the sentence above is corrected; the FACTS
are unchanged.]** The r3 wording, quoted and superseded: "**"bit-identically"
STRICKEN here as an overstatement of PE2's own record** … PE2's report says
something weaker for the sealed leg". That misassigns the origin. PE2's report
(`LIFTCORNER_passPE2_report.md`, 3367f3c) states the UNQUALIFIED form for the
sealed runner at **three** sites — its verdict summary (line 33, "The sealed
runner re-runs **bit-identically**"), its section header (line 54, "### (a)
The SEALED runner — **bit-identical**, seal intact") and its closing
machine-legs line (line 471) — and the qualified form at **one** (line 67,
the family-table paragraph: "identical line-for-line modulo the
`elapsed`/per-block timestamp fields only"). So the overstatement
**ORIGINATES in PE2's report**; the r2 round **transcribed** PE2's own
headline word rather than dropping a qualification the source only ever gave
qualified. The truth, unchanged and independently re-confirmed at PE3 and at
PE4 (4 differing lines, all wall-clock): the runner's OUTPUT FILE is
**identical modulo timing fields**, not bit-identical, while every COUNTED
quantity is identical; the children-generator table IS bit-identical.
No critical finding, so no r2 edit touches the chain. Dispositions, each edit carrying a dated
`[r2, G#]` bracket, strike-and-replace (the refuted r1 wording is quoted
inside the bracket that supersedes it, never silently deleted): **G1** — the
(C)(ii) branching count "≤ 2e₀+1" is FALSE (its own parenthetical sums to
2e₀+3, and the committed table shows 7 children at e₀ = 2); corrected to
**≤ 2e₀+3**, attained at every e₀ in the battery, with the disclosure that
ONLY finiteness of this count is consumed and the quantitative claim is the
independent ρ bound. **G2** (honesty) — the F1 box credited PE1 with
independently re-verifying "all ω-gains", but rows 3/5/7a/7b are NEW per-digit
displays PE1 never saw; the attribution is corrected (PE1 checked r0's four
per-branch rows; the eight per-digit bounds were first hostile-read at PE2,
which re-derived all eight and found them correct and tight) and the charge
list gains item **(7)** naming them. **G3** — the children generator never
asserted that its enumeration EXHAUSTS the development (A6 bypasses
`children()` entirely, so a missing branch would leave the table green); PE2
supplied that leg ad hoc (0/752 mismatches) and r2 makes it DURABLE as
assertion **A7** in the committed generator, with the output recommitted.
**G4** — "gain(q-digit) = gain(r-digit) + e₁h₀" is STRICKEN (not an identity;
PE2's witness a·b = 4x²+2 over ℤ₂ has w₀(q) = 2 > 1 = w₀(r) — **[r3, F-B:** that
DIVIDEND is not realizable as a branch product at d₀ = 2; the witness is
replaced in S4.1 by a = x, b₁ = 4x+2 at a legal mid, and the strike itself
stands**]**) and replaced by
the direct CONTENT application to the q-digit, which yields the same displayed
"≥" column; the equality is recorded as an OBSERVATION (held on all 896
battery r/q pairs), not a law, and nothing consumes it. **G5** — "valid
EXACTLY on the flat corner d₀ = 1" weakened to the true statement (d₀ = 1 is
sufficient; the r0 clause also holds vacuously wherever no m-preserving child
occurs, and the table has such d₀ = 2 rows: A12, B14). Acceptance counter
unchanged at **0/2**: PE2 was a hostile pass but returned 5 gaps, and the r2
repairs are themselves unaudited.]**

**[REPAIR ROUND r3 — 2026-08-08 campaign (wallclock 2026-08-05).** Applied
against LIFTCORNER-PE3 (hostile pass, fresh context, on the r2 text — the
FIRST acceptance attempt of the arc; report `LIFTCORNER_passPE3_report.md`,
commit 39ea0db: **0 CRITICAL + 5 gaps**). PE3 was directed at the veins the
first two passes had not mined: S2/S3's measurement design, the (TAIL-STAB)
consumer interface, the r2 patches themselves, and the arc's own grade
arithmetic. **The mathematics held at every point it touched** — PE3
re-derived independently all eight per-digit ω-gain bounds, the 2e₀+3
branching arithmetic, the counter-instance's two passes and its
double-development tie, the whole S2 applicability arithmetic (16 → 48 → 56 →
656/4,176/3,816 → 25,409), and the (TAIL-STAB) interface at every downstream
site; both machine legs re-ran clean (see the [r3] machine-leg bracket above).
All five gaps land in the EVIDENCE-DESCRIPTION layer, not in the chain.
Dispositions, each edit carrying a dated `[r3, F-#]` bracket,
strike-and-replace (the superseded r1/r2 wording is quoted inside the bracket
that replaces it, never silently deleted): **F-A** (the substantive one) — S2
disclosure (c)'s evidential ranking of the runner's two asserts is INVERTED:
assert (i) (`[tuple(c) for c in T.psi1] == psi1_base`), which r1's F4 repair
promoted as the genuine leg, is a snapshot-consistency NO-OP that provably
cannot fail and certifies nothing about carryover, while (ii)
(`C.K2["one"] == C0.K2["one"]`), which r1 demoted, is the only one of the two
that compares distinct objects. CORRECTED, source-verified afresh at r3 (the
mutation trace is displayed in (c)); **no claim in this note consumes (i)**, so
nothing is re-fenced and no new script is added. **[r4, F4-1: the promotion of
(ii) — "the only one of the two that compares distinct objects", read as an
evidential ranking — is STRICKEN. `C.K2["one"]` is a constant of (d₀, g₀, g₁);
(ii) compares two occurrences of that constant and cannot fire either. BOTH
asserts are inert. What stands from F-A: (i)'s no-op diagnosis, the
`mk_field_ext` relocation, and "no claim in this note consumes (i)" — which
r4 states of (ii) as well. Final description: S2 (c)'s [r4, F4-1] bracket.]**
**F-B** — the witness r2's G4
bracket displayed for the stricken r-to-q identity (a·b = 4x²+2) is NOT
realizable as a branch product in its own setting (Φ₀ = x²+x+1 forces
deg a, deg b ≤ 1, and the factorization would need a square root of −8 in ℚ₂
with v₂(−8) = 3 odd); replaced by PE3's realizable substitute at a LEGAL mid
branch (a = x, b₁ = 4x+2 ⟹ w₀(q) = 2 > 1 = w₀(r) = w₀(a·b₁)), re-verified in
exact integer arithmetic at r3. The strike itself stands unchanged — the
identity is still false and nothing consumes it. **F-C** — "both machine legs
re-ran BIT-IDENTICALLY at PE2" is corrected at both sites to PE2's own
qualified record (line-for-line identical *modulo the elapsed/per-block
timestamp fields*; committed artifact 4.4 s vs re-runs 4.3 s). **F-D** — the
r2 status line labelled charge items (1)–(2) "unaudited" in the same paragraph
crediting PE2 with re-deriving exactly them; relabelled to item (7)'s accurate
pattern (re-derived by hostile passes, no acceptance credit). **F-E** — Q6
LOC's family count (zero: the runner emits no `note("LOC")` at all) is
supplied in S3 so no family count is omitted, and the wording that read it as
an affirmative observation on a probed stratum is stricken. Acceptance counter
unchanged at **0/2** — PE3 was a hostile pass and found no critical, but 5
gaps is not a clean pass, so no acceptance slot closed; **PE4 — a fresh
hostile pass on THIS text — is the next acceptance attempt.**]**

**[REPAIR ROUND r4 — 2026-08-08 campaign (wallclock 2026-08-05).** Applied
against LIFTCORNER-PE4 (hostile pass, fresh context, on the r3 text — the
arc's SECOND acceptance attempt; report `LIFTCORNER_passPE4_report.md`,
commit 8b53efa: **0 CRITICAL + 6 gaps**). PE4 was directed at S1's
definitions, S4.2/S4.3 end to end, COR 1 + the PROP rider, S5 as the note's
summary of record, the bracket system as a system, and the ILNRES NR-1
interplay. **The mathematics held everywhere it pushed** — PE4 re-derived
from scratch all eight per-digit ω-gain bounds, the census/lex/ρ consumers,
READ-EQ's δ₁ = 1 comparison digit by digit on both towers, the
counter-instance's two passes and its double-development tie, and the
THEOREM + COR 2 exactly on a concrete ℤ₂/𝔽₄ orbit member; it also
established a POSITIVE fact this note now records (S5 STATUS BLOCK, PROVED bullet): **δ₁ = 1 is
empty at e₀ = 1**, so S4's e₀ ≥ 2 Setting costs COR 1 nothing and the corner
is covered in full. Both machine legs reproduce (timing-only diffs; see the
[r4] machine-leg bracket above). All six gaps land in the
evidence-description / bookkeeping layer, not in the chain. Dispositions,
each edit carrying a dated `[r4, F4-#]` bracket, strike-and-replace (the
superseded r1/r2/r3 wording is quoted inside the bracket that replaces it,
never silently deleted): **F4-1** (the assert saga, act three — ENDED) — r3
promoted assert (ii) (`C.K2["one"] == C0.K2["one"]`) as "the half that can
actually fire"; that is FALSE, and the round-by-round pattern (r0 described
the pair, r1 promoted (i), r3 promoted (ii)) is closed by promoting NOTHING:
**both asserts are inert**, no chain step consumes either, the soundness is
`mk_field_ext`'s g = 1 reading. Final description in S2 (c). **F4-2** — S5's
r1 status line still carried the F4 clause r3's own F-A refutes; struck, and
superseded in place by a pointer to F4-1's final description. **F4-3** — the
"bit-identically" overstatement is re-attributed to its true origin (PE2's
own report, three unqualified sites, one qualified) with r2 recorded as the
TRANSCRIBER; the factual correction ("identical modulo timing fields") is
unchanged. **F4-4** — PROP's rung-≥2 clause-(ii) census cite is re-pointed
from the (false) "[ILN]/ILNRES consumption tables" to ITERLAWN's own r4
erratum, and the pin a rung-≥2 census must clear is named explicitly.
**F4-5** — the `c′` collision (residue scalar vs cocycle) in the headline
display is fixed by renaming the COCYCLE to `c^{Φ′}`, with a renaming note
between the THEOREM and COR 2. **F4-6** — S5's "NR-1 then leaves the ILNRES
residual list" is rewritten to exactly what this note delivers (the Φ₁-only
corner), with the deeper-level discrepancy stated neutrally and flagged as an
ILNRES-side erratum candidate (ILNRES is NOT edited). **STRUCTURAL:** S5's
status block — which produced findings in three consecutive passes — is
REGENERATED from a minimal five-line template; every removed sentence is
quoted verbatim inside S5's `[r4, ARCHIVE]` bracket. Acceptance counter
unchanged at **0/2** — PE4 was a hostile pass and found no critical, but 6
gaps is not a clean pass, so no acceptance slot closed; **PE5 — a fresh
hostile pass on THIS text — is the next acceptance attempt.**]**

**[REPAIR ROUND r5 — 2026-08-08 campaign (wallclock 2026-08-06): MINIMAL round
against LIFTCORNER-PE5 (`LIFTCORNER_passPE5_report.md`, commit a5212e8:
**0 CRITICAL + 5 gaps**, all five in the r4 edits), per the ledgered
arc-dynamics diagnosis (each round's new prose has bred ~5 defects) — exactly
five one-line fixes, each superseding the quoted prior wording: **F5-1** the
STATUS BLOCK PROVED line drops "and PROP's rung propagation" (the
CONDITIONALITY line's "(5) PROP's rung-≥2 clause-(ii) census is OWED" is its
status of record); **F5-2** the [r4, F4-1] parenthetical "(ψ₁ and K₂ enter no
counted predicate of S3 and no step of S4)" re-scoped to the ASSERTS (ψ₁ and
K₂ themselves DO enter S4.2 as shared read data); **F5-3** S3's Q7 bullet
"c_base = c′·ξ^{D₁}" renamed to c^{Φ′}·ξ^{D₁} and the [r4, F4-5]
correction-of-record clause extended to S2's sealed Q7 sheet row; **F5-4** the
[r4, F4-4] bracket's "ITERLAWN_PROOF's S9" corrected to **S7** (the 22-row
sweep sits in ITERLAWN S7, verified at source; ITERLAWN's S9 is a table-free
scope box); **F5-5** the r4 header's "(S4.3, COR 1)" pointer re-aimed at the
true site, the S5 STATUS BLOCK PROVED bullet — plus the STATUS BLOCK ARC-line
update, NOTHING else; both machine legs BYTE-FROZEN and untouched. Acceptance
counter unchanged at **0/2**; **PE6 — a fresh hostile pass on THIS text — is
the next acceptance attempt.**]**

**[REPAIR ROUND r6 — 2026-08-08 campaign (wallclock 2026-08-06): MINIMAL round
against LIFTCORNER-PE6 (`LIFTCORNER_passPE6_report.md`, commit f2b48e7:
**0 CRITICAL + 3 gaps** — the arc's first ZERO-defect diff: all 32 r5
insertions verified true, all five fixes correctly placed, the mathematics
clean on its sixth hostile reading; all three gaps in record surfaces r5 did
not touch), same discipline — exactly three record-surface fixes, each
superseding the quoted prior wording: **F6-1** the STATUS BLOCK is brought
forward to match its own r5-updated ARC line (superseded, NEXT/AUDIT bullet:
"PE5, a fresh hostile pass on THIS text. Unaudited going in: **the r4
edits**. Read once: the r3 edits (PE4). Read twice: the r2 edits (PE3,
PE4)." and its machine-leg clause "re-run clean at PE4"; superseded, label:
"STATUS BLOCK [r4]"), and the S4.3 grade box gains a dated [r6] bracket —
its last entry, the [r4] bracket, still closed "the r4 edits are UNAUDITED …
PE5 … is the next acceptance attempt" (true when dated, stale as the box's
last word; the first bring-forward since r4); **F6-2** the [r4, F4-5]
correction-of-record clause is extended to S2's sealed Q9 sheet row, the
THIRD bare-`c′`-as-cocycle site (superseded: "for S2's sealed Q7 sheet row,
whose `c′` is likewise this cocycle"); with Q9 the census is COMPLETE —
PE6's sweep of "all 42 `c′` occurrences" at its HEAD (46e6e88) found NO
fourth site **[r7, F7-1 — UNIT: PE6's "42" is a hit-LINE count; the raw
count at 46e6e88 is 46 occurrences on 42 lines (four lines carry two, all
scalar pairs); the occurrence-level warrant of record is PE7's re-execution
(commit 58f7060) at 91f0cde — 51 occurrences / 47 lines = 34 scalar + 4
covered-cocycle + 13 mention/quotation, NO fourth site — restated in full
at the [r4, F4-5] bracket]**; the sealed sheet text itself is NOT edited; **F6-3** the
closing dating record gains its missing r5 line (wallclock 2026-08-06) and
this round's r6 line (superseded terminator: "repair round r4 applied
2026-08-08 campaign (wallclock 2026-08-05).") — plus the STATUS BLOCK
ARC-line update, NOTHING else; both machine legs BYTE-FROZEN and untouched.
Acceptance counter unchanged at **0/2**; **PE7 — a fresh hostile pass on
THIS text — is the next acceptance attempt.**]**

**[REPAIR ROUND r7 — 2026-08-08 campaign (wallclock 2026-08-06): ONE-CLAUSE
round against LIFTCORNER-PE7 (`LIFTCORNER_passPE7_report.md`, commit 58f7060:
**0 CRITICAL + 1 gap (minor)** — all four r6 hunks verified true and
correctly placed except one clause; the record system judged CONSISTENT AND
TRUE AT HEAD for the first time in the arc; r6's disclosed NEXT/AUDIT
deviation judged CORRECT; the mathematics clean on its SEVENTH hostile
reading; both machine legs re-run clean), exactly one fix: **F7-1** the
census-completeness warrant's figure — PE6's "all 42 `c′` occurrences",
transcribed twice at r6 — is a hit-LINE count, not an occurrence count (at
46e6e88: **46** occurrences on 42 lines, four lines carrying two, all scalar
pairs), so the stated sweep universe did not reproduce under its own unit;
both census sites now carry PE7's occurrence-level warrant of record — at
91f0cde, 51 occurrences / 47 lines = 34 residue-scalar + 4 covered-cocycle
(S1 CANDIDATE ×2, Q7, Q9 — all inside the correction of record) + 13
mention/quotation, NO fourth site — (superseded, at the [r4, F4-5] bracket:
"with Q9 the census is COMPLETE — PE6's sweep of "all 42 `c′` occurrences"
at its HEAD (46e6e88) found NO fourth site."; the r6 round block's twin
clause is dated text and gains a dated [r7, F7-1] bracket instead).
PROVENANCE: the figure and its unit word originate in PE6's report (its
F6-2 sweep sentence); r6 TRANSCRIBED them inside quotation marks — the
arc's documented transcription mechanism, now its THIRD recurrence ([r3,
F-C]/[r4, F4-3]: PE2's "bit-identically"; [r5] F5-4: PE4's "S9") — standing
rule henceforth: quote counts only WITH THEIR UNIT AND COMMIT. Plus the
round-close record surfaces brought to HEAD truth (the r6/F6-1 + F6-3
precedent; PE7 §3 verified that bring-forward judgment CORRECT): the STATUS
BLOCK ARC-line + NEXT/AUDIT bullet, a dated [r7] grade-box entry, and the
footer r7 dating line — NOTHING else; both machine legs BYTE-FROZEN and
untouched. Acceptance counter unchanged at **0/2**; **PE8 — a fresh hostile
pass on THIS text — is the next acceptance attempt.**]**

**Sources of record:** ILNRES_2026-08-08.md S1 [NR-1] + S5.1 (the spec);
ITERLAWLIFT_CORNER_2026-08-08.md (wave 18: the LAWFUL slice measured
104,404/0; the S7 sketch + its one open step (TAIL-STAB)); ITERLAWN_PROOF
S0.1 (the standard-lift class pin + the verbatim residual propagation rider);
GRTW2_PROOF §3.4 (χ-chain/shift-descent), §5 (clause 3 ψ-transport, W2-OPEN-1).

**FENCES.** No edit to any accepted text (ITERLAW/ITERLAWN/ILNRES bodies,
sealed falsifiers, wave-18 artifacts); committed engines consumed READ-ONLY
(in-memory ledger override only, engine_ext precedent); no Lean change; no
orders-≥3 machine claim (the battery is 2-read); no gr(w₂) claim; nothing
here closes NR-1's ledger entry until this note's own acceptance arc runs.

## S1. The corner orbit and the transport frame (derived; sealed pre-run)

At g₀ = 1: ψ₀ = y + c₀ (c₀ ≠ 0), K₁ = K₀, z₁ = −c₀ a SCALAR. The full monic
lift orbit at the corner (deg = e₀d₀, w₁ = e₀h₀, nonzero order-1 residual):
Φ′ = Φ₀^{e₀} + Σ_{k<e₀} b_kΦ₀^k, deg b_k < d₀, with w₀(b₀) = h₀,
c′ := res(b₀/π^{h₀}) ≠ 0, and w₀(b_k) ≥ amin(k) := ⌈(e₀−k)h₀/e₀⌉ (k ≥ 1;
strict-above automatic, gcd(e₀,h₀) = 1). Stratification by the residue c′:

* c′ = c₀ — the LAWFUL class of ψ₀ (wave-18's slice: measured exact, 0/104,404);
* c′ ≠ c₀ — the lawful class of the ξ-CONJUGATE ψ₀^{(ξ)} := ξ^{−1}ψ₀(ξy)
  = y + c₀/ξ at ξ := c₀/c′; letters z₁ = ξ·z₁′, z₁′ := −c′. This is exactly
  W-2 clause 3's ψ-transport, DEGENERATE at the corner: K₁ = K₀ carries no
  letter, so the tower transport is the bare scalar substitution z₁ ↦ z₁′
  (the clause-3 re-coordination step is vacuous). The ε-degeneration the
  charge names: ε₁-corrections are z₁-powers of a scalar, so the whole
  value layer transports by one character — the χ-law.

**CANDIDATE (the transport law, preregistered).** On the tower built on ANY
orbit member Φ′ (ledger transported: ψ₀ ↦ y + c′, all deeper data
byte-identical, canonical Φ₂ rebuilt on the transported letter), the accepted
2-read display holds WITH THE LETTER THE LIFT CARRIES:

    c′(γ,γ′) = z̄^{δ₂} · (z₁′)^{D₁},   D₁ := (s₁+s₁′−s₁″+ℓ₀γ₂δ₂)/e₀,
    equivalently  c_base(γ,γ′) = c′(γ,γ′) · ξ^{D₁}   (the χ-ratio law),

with all integer data (splits, D₁, δ₂, windows) lift-independent. The ξ = 1
slice is wave-18's measured law; the ξ ≠ 1 direction is NEW — no instance
evidence exists anywhere in the corpus before this battery.

## S2. Sealed prediction sheet (`liftcorner_checks.py`, seed 20260911)

Roster: the wave-18 rows CA–CF verbatim (all g₀ = 1, E₂ ∈ {4,6,8,6,10,3}),
× rings {ℤ₂, ℤ₃, F₂[[t]], F₃[[t]]}; windows W1×W1 + mixed W1×W3. Twists
exist iff |K₀| > 2 (deterministic applicability: d₀ = 2 rows on all rings;
d₀ = 1 rows on p = 3 rings only; 16 twistable (ring,row) instances). Per
instance: c′-draws (≤ 2, deterministic enumeration) × variants {pure twist,
twist + dense tails/mids} = 48 twisted towers; plus the ξ = 1 dense controls
(rows CB/CF × 4 rings) and the 24 base (standard) towers for the χ-cache.

| family | content | prediction |
|---|---|---|
| Q1 GATE | every generated tower passes the lawfulness gate FOR ITS OWN ψ₀′ (residual = y + c′) | 0 failures |
| Q2 AV | ANCHOR-VAL with the transported ε₁′ (z₁′-powers), letters W1+W3 | 0 |
| Q3 TLAW | **THE CANDIDATE: measured cocycle = transported display (z₁′)** | 0 |
| Q4 PV | L7 PAIR-VAL both forms + single-slot shape, transported letters | 0 |
| Q5 INT | exponent integrality | 0 |
| Q6 LOC | δ₁ = 0 sub-violations (lift-form-free legs; bug detector) | 0 |
| Q7 CHI | cross-tower χ-ratio: c_base == c′·ξ^{D₁}, measured vs MEASURED | 0 |
| Q8 COV | per twisted block: ≥ 1 δ₁ = 1 pair AND ≥ 1 pair with ξ^{D₁} ≠ 1 | met |
| Q9 WRONGLET | control: per-pair (c′ ≠ wrong-letter form) ⟺ (ξ^{D₁} ≠ 1), exact set equivalence; total fires > 0 | 0 / fires |
| Q10 XI1 | the ξ = 1 dense slice reproduces the UNCHANGED display (wave-18 tie) | 0 |
| TRS | closed-form transcription vs C.iter_law (transported automatically) | 0 |
| CERT | base towers: G.T1_T2(nf=4) + G.T5 internal (PARI leg NOT re-run: wave-18 T11 on the same base roster is on file — disclosed reuse) | 0 |
| ENG-GATE | engine_ext.agreement_gate(full=False) re-run in-unit (standing rule) | 0 new |

**Disclosures (pre-seal):** (a) a `--shakedown` crash-freedom run (1 ring,
2 rows, 1 twist, no json) runs before commit 1; (b) exact arithmetic,
deterministic full windows, no sampling beyond the seeded pert residues;
(c) the ledger override (ψ₀ ↦ y + c′) is IN-MEMORY on a fresh Tower object —
sound because at g₀ = 1 the degree-1 extension arithmetic of K₁ is
modulus-independent (mk_field_ext at g = 1: products never touch the reducer),
so ψ₁ and every deeper byte carries over verbatim; **(d) SP bug-detector
counters recorded.**

**[r4, structural — item (d) is RESTORED to the pre-seal list.]** r3 inserted
its F-A bracket between (c) and (d), leaving (d) hanging off the end of a
post-hoc correction so that a reader could not tell it belonged to the SEALED
pre-run disclosure (PE4 §3(e), recorded there but not numbered). The list
(a)–(d) is now complete and unbroken; the r3/r4 correction brackets follow it.
No claim changes.

**[r3, F-A — the r1 ranking of the runner's two asserts is INVERTED;
corrected here, source-verified afresh at r3.]** The r1 wording, quoted in full
and SUPERSEDED: "**[r1, F4 — corrected wording]** the runner asserts, before
any comparison, (i) full ψ₁-BYTE carryover
(`[tuple(c) for c in T.psi1] == psi1_base`) and (ii) a single-element byte
check on the K₂ table (`C.K2["one"] == C0.K2["one"]`) — (ii) is a SMOKE CHECK
on one element, NOT an assertion that the K₂ arithmetic representation is
shared, as the r0 text's parenthesis "(ψ₁ bytes equal, K₂ arithmetic
representation shared)" implied." Both asserts do exist verbatim in the sealed
runner (`liftcorner_checks.py:36`/`:52` and `:179`), and (ii)'s SCOPE
downgrade stands. What is wrong is the bracket's whole rhetorical structure —
a CONTRAST promoting (i) as the genuine leg and demoting (ii) — because the
contrast is backwards (PE3, report `LIFTCORNER_passPE3_report.md`, commit
39ea0db, F-A; the mutation trace below re-read line by line at r3):

* **assert (i) is a SNAPSHOT-CONSISTENCY NO-OP: it cannot fail, and it
  certifies NOTHING about carryover.** `psi1_base` is snapshotted from the SAME
  object `T` that is then mutated — `liftcorner_checks.py:36`, one line after
  `T = LC.make_tower(...)` — and nothing between the snapshot and the assert
  writes `T.psi1`. Exhaustively: `T.psi1` is assigned exactly ONCE, in
  `Tower.__init__` (`grb_order2_check.py:515`,
  `self.psi1 = self._psi1_override if … else pick_irreducible(self.K1, self.g1,
  idx=(self.h0) % 2)`), i.e. BEFORE `make_orbit_tower` ever sees `T` (and with
  no override on this path — `LC.make_tower` passes none); the override block
  writes only `T.psi0`, `T.K1`, `T.z1`, `T.Phi1_std`; `LC.apply_pert`
  (`iterlawlift_corner.py:145–155`) writes only `T.Phi1` and `T.Phi2`, as its
  own docstring says; and `build_Phi2` (`grb_order2_check.py:651`) only READS
  `self.psi1`. So (i) compares `T.psi1` against a copy of itself across code
  that provably never touches it. In particular it never RECOMPUTES ψ₁ on the
  transported K₁ — the one act that could have made it a carryover check.
  Its honest job is a REGRESSION GUARD against a future edit that makes the
  override path (or `apply_pert`/`build_Phi2`) recompute ψ₁.
* **[r4, F4-1 — the r3 bullet on assert (ii) is STRICKEN, and NOTHING is
  promoted in its place.]** The r3 wording, quoted in full and SUPERSEDED:
  "*assert (ii) is the only substantive one of the two.*
  `C.K2["one"] == C0.K2["one"]` (`liftcorner_checks.py:179`) *compares two
  DISTINCT objects* — the K₂ table built on the transported tower against the
  one on the base standard tower — *so it is the half that can actually fire.*
  It remains a one-element check and does not certify that the whole K₂
  arithmetic representation is shared (r1's correction of the r0 parenthesis is
  right about that); *but a one-element check on two objects carries strictly
  more evidence than a tautology on one.*" **That ranking is false: `K2["one"]`
  is a structural CONSTANT of (d₀, g₀, g₁).** From source,
  `mk_field_ext(K, psi)` (`grb_order2_check.py:333–334`) sets
  `g = len(psi) − 1` and
  `one = tuple([K["one"]] + [K["zero"]]*(g−1))` — it never reads a single
  coefficient of `psi`, and never reads the reduction data `red` built from it.
  Composing the two levels: `T.K1 = mk_field_ext(K0, T.psi0)` at g₀ = 1 gives
  `K1["one"] = (K0["one"],)`, independent of the residue the override writes
  into `T.psi0`; `C.K2 = mk_field_ext(T.K1, T.psi1)`
  (`strata_probe.py:389`) then gives `K2["one"] = ((K0["one"],),)` for ANY ψ₁;
  and `T`, `T0` come from the SAME `LC.make_tower(kind, p, d₀, r₀, r₁, ·)`
  call (`liftcorner_checks.py:35` and `:144`), so g₁ agrees on both. Hence (ii)
  compares two occurrences of one constant and is **structurally incapable of
  failing — on exactly the same footing as (i).** Re-verified at r4 from source
  AND empirically on the note's own d₀ = 2 row CB over ℤ₂ (K₀ = 𝔽₄, both twist
  draws exist): `K2["one"] = (((1,0),),)` on the base tower, on both twist draws
  c′, and again with ψ₁ perturbed — while the letter `z₁` DOES move under the
  override, so the override is doing real work to which this assert is blind.
  Failure scenario it cannot catch: if the transported K₂ arithmetic were built
  on stale reduction data, every K₂ product would be wrong and (ii) would still
  pass, because it inspects only the multiplicative identity.

Stated plainly: **r1's F4 repair promoted the wrong half of its own sentence**,
and both later passes signed off on the unfixed half — PE1 called (i)
"genuine", PE2 checked only that the quoted source line matched verbatim (a
text match, not a semantic one) — so the overstatement survived two hostile
readings before PE3 traced the mutations. **No claim in this note consumes (i).**

**[r4, F4-1 — THE FINAL DESCRIPTION OF THE PAIR, promoting nothing.] BOTH
asserts are INERT: neither can fire on any input this battery generates.**
(i) is a snapshot-consistency no-op — a regression guard against a future edit
that recomputes ψ₁ on the transported K₁; (ii) is a comparison of two
occurrences of a constant — a regression guard against a future change of the
(d₀, g₀, g₁) ↦ identity-element representation. **NO CHAIN STEP CONSUMES
EITHER**: the ψ₁-site walk below establishes it for (i), and the same walk
gives it for (ii) verbatim (the ASSERTS enter no counted predicate of S3 and
no proof step of S4; ψ₁ and K₂ themselves enter S4.2 as shared read data).
**The soundness of the K₂ layer lives in `mk_field_ext`'s g = 1
reading** — `grb_order2_check.py:345`, where the reduction loop
`range(len(out)−1, g−1, −1)` is `range(0, 0, −1)`, empty, so products never
touch the reducer — **not in either assert.** *Arc of this pair, recorded in
one sentence so that no future round re-promotes either half:* r0 described it
("ψ₁ bytes equal, K₂ arithmetic representation shared"), r1 promoted (i), r3
promoted (ii), and **r4 demotes both** — every promotion so far has been an
overclaim, and there is no third half left to promote.

Checked at r3 by walking every ψ₁ site in the note: S2 (c)'s own soundness
claim is discharged by READING `mk_field_ext` (next sentence), not by the
asserts; S3's figures are the runner's counted families (GATE/AV/TLAW/PV/INT/
CHI/COV/WRONGLET/TRS/CERT/ENG-GATE), and ψ₁ enters none of their predicates;
and S4.2 READ-EQ's "the towers share every read datum (reads, ψ₁, K₂, …)" is a
statement about the Φ′- and Φ″-TOWERS OF THE PROOF, proved from the S4 setting
(both are monic lifts over the same K₁ = K₀ at g₀ = 1), with no dependence on
any runner assert. So nothing is re-fenced and NO new supplementary script is
added at r3: there is no claim for a genuine carryover check to hold up.
The modulus-independence itself is
verified by READING `mk_field_ext`: at g = 1 its reduction loop
`range(len(out)-1, g-1, -1)` is empty, so products never touch the reducer —
that is where the override's soundness lives (PE1 F4 re-derived it there
independently; PE3 re-derived it independently again AND checked the consequence
the sheet actually needs, which no assert checks: at g₀ = 1 the K₁ elements are
1-tuples over K₀ with modulus-free multiplication, so `_field_elems(K1)`
enumerates them in a c′-independent order and `pick_irreducible(K1, g1, idx)`
returns the same ψ₁ bytes for every residue c′ — i.e. the transported ψ₁ IS
the base ψ₁, as a fact about the code, not as a machine assertion) — not in
the runner's asserts. **[r3, F-A, fence disclosure]** The SEALED runner's own
module docstring carries the same overstatement ("the runner ASSERTS psi1-byte
carryover and shared K2 representation", `liftcorner_checks.py:14`); it is
BYTE-FROZEN by the two-commit seal and is therefore NOT corrected — the seal
outranks the wording, and this bracket is the correction of record. Anyone
reading that docstring should read it as **[r4, F4-1 — the re-reading
instruction is corrected; the r3 wording, quoted and superseded, was "assert
(i) is a regression guard, assert (ii) is a one-element check on two objects,
and the soundness is in `mk_field_ext`"]**: **BOTH asserts are inert
regression guards that certify nothing about carryover**, and the soundness is
in `mk_field_ext`'s g = 1 reading.

## S3. VERDICT (commit 2; from the artifacts; seal dafc0b5, runner
byte-untouched, md5 ccb4351c92573f5f962cae4ae952d8dd)

**ALL GREEN, FIRST RUN, exit 0** — 25,409 checks, **0 violations in every
family**, elapsed 4.4 s (`liftcorner_checks_output.txt`,
`liftcorner_checks_results.json`; these govern on any transcription
discrepancy):

* Q1 GATE 56/56 orbit towers pass the lawfulness gate for their OWN ψ₀′
  (48 twisted + 8 ξ = 1 dense controls — exactly the deterministic
  applicability counts of the sheet); Q2 AV 656/0;
* **Q3 TLAW 4,176/0 — THE CANDIDATE: the display holds with the letter the
  lift carries (z₁′ = −c′) on every ξ-twisted tower**, both pair blocks;
* **Q7 CHI 4,176/0 — the χ-ratio law c_base = c^{Φ′}·ξ^{D₁} EXACT, measured
  against measured** (no closed form in the comparison): the W-2 covariance
  carries the corner;
* Q4 PV / Q5 INT / TRS 4,176/0 each; **[r3, F-E — the one omitted family
  count, supplied; the r2 wording "Q6 LOC 0 (no δ₁ = 0 anomaly)" STRICKEN as
  reading like an affirmative observation on a probed stratum]** Q6 LOC
  **0 checks counted / 0 violations**: the runner emits no `note("LOC")` call
  at all, so LOC has no check counter and contributes 0 of the 25,409 (the
  committed artifact reads `LOC       pred 0  obs     0  (     0)  GREEN`), and
  `viol("LOC", …)` fires only NESTED inside the violation branches of PV, INT
  and TLAW. So LOC's content is LOGICALLY IMPLIED by those three being green and
  carries no information they do not already carry — it is the nested bug
  detector S2's sheet row calls it, not an independent leg. A reader tallying
  S2's thirteen prediction families as thirteen independent legs over-counts by
  one. (Q8 COV also counts 0 but is NOT in this position: its `if ncov == 0` /
  `nteeth == 0` checks can fire independently of every other family, and its
  substance is reported explicitly in the next bullet.)
* Q8 COV met — min 6 δ₁ = 1 pairs and min 6 teeth pairs (ξ^{D₁} ≠ 1) per
  twisted block; Q9 WRONGLET: per-pair set equivalence EXACT on 3,816
  samples, total fires 1,576 > 0 (the wrong-letter form fails exactly where
  ξ^{D₁} ≠ 1 — the transport is sharp, not slack);
* Q10 XI1: the ξ = 1 dense slice reproduces the unchanged display (wave-18
  tie re-confirmed); CERT internal 0; ENG-GATE 0 new (full=False disclosed);
  SP bug-detector 0.

STATUS EFFECT of S3 alone (before S4): the ξ ≠ 1 orbit direction — where NO
corpus evidence existed — is now MEASURED-TRANSPORT-EXACT: the displays
change under the lift orbit by EXACTLY the χ-law, W-2 clause 3's prediction
degenerate at the corner. The S4 compose is earned per the seal condition.

## S4. THE COMPOSE (earned by S3; the shift-descent route)

Setting: the S1 corner (g₀ = 1, e₀ ≥ 2; at e₀ = 1 no Case II exists —
COR-3's degeneration, theorem-backed, outside this unit). Φ′ an orbit member
with residue c′; Φ″ := Φ₀^{e₀} + lift(c′)·π^{h₀} the STANDARD lift of
ψ₀^{(ξ)} = y + c′. Base facts as [IL S1]/[ILN] S0.2 (division algorithm by
monic keys, w₀ a valuation, res additive + kills strict π-excess), plus:

**[r1, F2 — notation, defined here at first use.]** The b₀-SPLIT, used by the
S4.1 branch table and by S4.2 and imported from wave-18 S1
(ITERLAWLIFT_CORNER_2026-08-08.md S1, a source of record above; it was used
in the r0 text without an in-note binding):

    b₀ = ĉ′·π^{h₀} + t₀,   deg ĉ′ < d₀, res(ĉ′) = c′ ≠ 0 (so w₀(ĉ′) = 0),
                            deg t₀ < d₀, w₀(t₀) ≥ h₀ + 1.

Existence and uniqueness given a choice of the lift ĉ′ of c′: w₀(b₀) = h₀ (S1)
lets one divide b₀ by π^{h₀}, take ĉ′ := any degree-<d₀ lift of the residue
c′ = res(b₀/π^{h₀}), and set t₀ := b₀ − ĉ′π^{h₀}, whose residue at level h₀
vanishes — i.e. w₀(t₀) ≥ h₀+1. "ĉ′π^{h₀}" is the b₀-MAIN part, "t₀" the
b₀-TAIL; the STANDARD lift Φ″ is the orbit member with ĉ′ = lift(c′) and
t₀ = 0 and all mids b_k = 0 (k ≥ 1).

**CONTENT (sub-lemma).** For monic Φ, the digits of dev(F, Φ) satisfy
w₀-content ≥ w₀-content(F). *Proof:* induction through the division step —
each subtraction removes lc(F)·x^i·Φ with lc(F) a coefficient of the current
remainder; w₀ is a valuation. ∎

### S4.1 LEMMA (TAIL-STAB) — the wave-18 open step, closed (proof REPAIRED at r1; statement byte-unchanged)

For X = a·Φ₀^m·Φ′^j (a ∈ O[x], deg a < d₀) put the LEDGER weight
ω(X) := e₁(e₀·w₀(a) + m·h₀) + j·γ₂, γ₂ = e₁e₀h₀ + h₁. Then in the double
development X = Σ_j A_jΦ′^j, A_j = Σ_i a_{ji}Φ₀^i (dev by Φ′ then Φ₀):

    (LEDGER)  every nonzero digit obeys e₁(e₀·w₀(a_{ji}) + i·h₀) + jγ₂ ≥ ω(X).

Hence w₂(X) ≥ ω(X), and for any read weight Γ < ω(X) every level-2 read of X
at Γ contributes 0 at every grid slot (on-line: strict-excess summands die in
res; off-line: C_j = 0; digit collisions: w₀ ultrametric, min bounds survive).

*Proof (r1).* Induction on the pair (m, deg a) in the LEXICOGRAPHIC order on
ℕ × ({−∞} ∪ {0,…,d₀−1}) — m first, then deg a, with deg 0 := −∞ (a zero
coefficient contributes no digit and generates no child). Lex products of
well-orders are well-founded, which is all the induction uses; the statement
is proved for every (a, m, j) with deg a < d₀, uniformly in j.

**Base m < e₀** (any deg a): deg(aΦ₀^m) ≤ (d₀−1) + (e₀−1)d₀ < e₀d₀ = deg Φ′,
so by dev uniqueness the double dev is the single digit a at (i, j) = (m, j):
(LEDGER) with equality.

**Step m ≥ e₀:** one pass of the orbit identity Φ₀^{e₀} = Φ′ − b₀ −
Σ_{k≥1}b_kΦ₀^k gives X = aΦ₀^{m−e₀}Φ′^{j+1} − ab₀Φ₀^{m−e₀}Φ′^j −
Σ_{k≥1} ab_kΦ₀^{m−e₀+k}Φ′^j, with b₀ = ĉ′π^{h₀} + t₀ split as above. Each
level-0 coefficient is a product a·b with b ∈ {1, ĉ′π^{h₀}, t₀, b_1, …,
b_{e₀−1}}, so deg(a·b) ≤ deg a + d₀ − 1 < 2d₀ and its Φ₀-redigit
a·b = r + qΦ₀ has deg r, deg q < d₀ with w₀(r), w₀(q) ≥ w₀(a·b) ≥
w₀(a) + w₀(b) by CONTENT. Every child is again of the lemma's shape.

**(A) THE CHILD CENSUS — seven genres** (this case list matches the genre
list of the r1 examples-first table under the explicit 9 ↦ 7 label mapping
displayed in the machine-leg bracket below; the two coordinates are read off
per row, then justified):

| # | child genre | a′ | (m′, j′) | m-descent | lex (m, deg a) descent | ω-gain ≥ |
|---|---|---|---|---|---|---|
| 1 | key | a | (m−e₀, j+1) | m′ ≤ m−2 | 1st coord | γ₂ − e₁e₀h₀ = h₁ > 0 |
| 2 | b₀-main r-digit | −r(aĉ′π^{h₀}) | (m−e₀, j) | m′ ≤ m−2 | 1st | **0** (the only 0-gain genre) |
| 3 | b₀-main q-digit | −q(aĉ′π^{h₀}) | (m−e₀+1, j) | m′ ≤ m−1 | 1st | e₁h₀ |
| 4 | b₀-tail r-digit | −r(a t₀) | (m−e₀, j) | m′ ≤ m−2 | 1st | e₁e₀ |
| 5 | b₀-tail q-digit | −q(a t₀) | (m−e₀+1, j) | m′ ≤ m−1 | 1st | e₁e₀ + e₁h₀ |
| 6 | mid r-digit, 1 ≤ k ≤ e₀−1 | −r(a b_k) | (m−e₀+k, j) | m′ ≤ m−1 | 1st | e₁ |
| 7a | mid q-digit, 1 ≤ k ≤ e₀−2 | −q(a b_k) | (m−e₀+k+1, j) | m′ ≤ m−1 | 1st | e₁(h₀+1) |
| 7b | **mid q-digit at k = e₀−1 (the TOP mid)** | −q(a b_{e₀−1}) | **(m, j)** | **NONE: m′ = m** | **2nd: deg a′ ≤ deg a − 1** | e₁(h₀+1) |

*The m′ column.* Read off the pass identity (a q-digit sits one Φ₀-power
above its r-digit). Rows 1–5 use e₀ ≥ 2 (the S4 setting; e₀ = 1 is COR-3's
degeneration, out of scope): m−e₀ ≤ m−2 and m−e₀+1 ≤ m−1. Row 6:
k ≤ e₀−1 ⟹ m−e₀+k ≤ m−1. Row 7a: k ≤ e₀−2 ⟹ m−e₀+k+1 ≤ m−1. Row 7b:
k = e₀−1 gives m′ = m exactly — the one m-preserving genre.

*Row 7b drops the second coordinate.* Its q-digit is nonzero only if
deg(a b_{e₀−1}) ≥ d₀, and then, using only deg b_k < d₀ (S1),

    deg a′ = deg q = deg(a b_{e₀−1}) − d₀ ≤ deg a + (d₀−1) − d₀ = deg a − 1.

So every one of the seven genres has (m′, deg a′) <_lex (m, deg a) and the IH
applies to every child.

*The ω-gains.* For a branch with factor b at Φ₀-exponent M = m−e₀+k and
w₀(b) ≥ β, a digit a′ landing at Φ₀-exponent M′ has
gain = e₁[e₀(w₀(a′) − w₀(a)) + (M′−m)h₀], with M′ = M for the r-digit and
M′ = M+1 for the q-digit. **[r2, G4 — the q-digit bound RE-DERIVED; the r1
identity STRICKEN.]** CONTENT is applied to EACH digit separately: from
a·b = r + qΦ₀ it gives w₀(r) ≥ w₀(a·b) ≥ w₀(a) + β AND w₀(q) ≥ w₀(a·b) ≥
w₀(a) + β, i.e. w₀(a′) − w₀(a) ≥ β for either digit. Hence

    gain(r-digit) ≥ e₁[e₀β − (e₀−k)h₀],
    gain(q-digit) ≥ e₁[e₀β − (e₀−k)h₀ + h₀],

the q-digit's extra e₁h₀ coming from its Φ₀-exponent being one higher, NOT
from any relation between w₀(q) and w₀(r). The r1 text's
"gain(q-digit) = gain(r-digit) + e₁h₀" is STRICKEN: it is not an identity.
The ultrametric only forces min(w₀(r), w₀(q)) = w₀(a·b), so the other digit
may sit strictly higher. **[r3, F-B — the witness is REPLACED by a realizable
one; the strike stands.]** The r2 display, quoted and superseded: "over ℤ₂ with
Φ₀ = x²+x+1, **a·b = 4x²+2** gives q = 4 and r = −4x−2, so
w₀(q) = 2 > 1 = w₀(r) = w₀(a·b) (PE2 G4's witness), and there
gain(q) − gain(r) = e₁[e₀·1 + h₀] ≠ e₁h₀." Its division arithmetic is right
(4x²+2 = 4Φ₀ − 4x − 2, w₀ = 1, 2, 1) but the dividend is labelled "a·b", i.e.
a level-0 BRANCH coefficient, and at Φ₀ = x²+x+1 the lemma's own hypotheses
(deg a < d₀ = 2, deg b < d₀ = 2 by S1) forbid it: a = αx+β, b = γx+δ forces
αγ = 4, βδ = 2, αδ+βγ = 0, hence (αδ)(βγ) = 8 with αδ = −βγ, so (αδ)² = −8 —
and v₂(−8) = 3 is odd, so −8 is not a square in ℚ₂. **4x²+2 is not a·b for any
a, b ∈ ℤ₂[x] of degree ≤ 1** (PE3 F-B), so the r2 text exhibited the phenomenon
for a general dividend while attaching a branch-level conclusion to it. PE2, who
authored the witness, had hedged exactly there ("witness for the ARITHMETIC
phenomenon"); the hedge was load-bearing and r2 dropped it. The replacement
witness is realizable AT A LEGAL BRANCH — same corner (ℤ₂, d₀ = 2, e₀ = 2,
h₀ = 1, Φ₀ = x²+x+1), take

    a = x  (deg 1 < d₀)   and the mid   b₁ = 4x+2  (deg 1 < d₀,
                                        w₀(b₁) = 1 = amin(1), so a LEGAL mid):
    a·b₁ = 4x²+2x = 4·Φ₀ + (−2x−4),  i.e.  q = 4,  r = −2x−4,
    w₀(a·b₁) = 1,   **w₀(q) = 2 > 1 = w₀(r) = w₀(a·b₁)**,

so there gain(q) − gain(r) = e₁[e₀(w₀(q)−w₀(r)) + h₀] = e₁[e₀·1 + h₀] = 3e₁ ≠
e₁h₀ = e₁ — the inequality, and the failure of the stricken identity, realized
at a genuine mid branch of a genuine orbit member. (Both divisions and the
non-factorization criterion re-verified in exact integer arithmetic at r3,
coefficient lists written LOW→HIGH:
`a·b₁ = [0,2,4] → q=[4], r=[−4,−2]` (i.e. r = −2x−4) with
w₀(a·b₁)/w₀(q)/w₀(r) = 1/2/1 and `q·Φ₀+r == a·b₁` exactly;
`4x²+2 = [2,0,4] → q=[4], r=[−2,−4]` (i.e. r = −4x−2), w₀ = 1/2/1,
reproducing the r2 numbers; v₂(−8) = 3.) Nothing in the table's "ω-gain
≥" column changes: those entries are exactly what the two displayed
inequalities give. OBSERVATION, not law, recorded so the stricken step leaves a
trace: the equality did hold on all **896** r/q branch pairs of the committed
battery (PE2 checked gain(q) − gain(r) == e₁h₀ pairwise, 0 exceptions) — an
artifact of those instances' shapes, and no step below consumes it. Row 1:
b = 1, but j′ = j+1 adds γ₂ and the Φ₀-drop costs e₁e₀h₀, net h₁ > 0. Rows
2–3: β = h₀, k = 0. Rows 4–5: β = h₀+1. Rows 6–7: β = amin(k) with
e₀·amin(k) ≥ (e₀−k)h₀ + 1, forced by gcd(e₀, h₀) = 1 (e₀ | kh₀ ⟺ e₀ | k,
impossible for 1 ≤ k < e₀). Every gain is ≥ 0 and the ONLY zero is row 2.

**[r1 MACHINE LEG for (A)/(B) — the examples-first table.]**
`verification/openmath/liftcorner_tailstab_children.py`, output committed as
`liftcorner_tailstab_children_table.txt` (exit 0, ALL GREEN; independent of
the sealed battery, which is byte-untouched). 29 towers spanning p ∈ {2,3,5},
d₀ ∈ {1,2,3}, e₀ ∈ {2,3,4,5,6} (the e₀ = 2 boundary and e₀ ≥ 3 both), all
four lift genres (pure = Φ″, dense = tail + mids, mids-only, tail-only), plus
PE1's counter-instance verbatim as row CTR; 752 (a, m, j) probes; **2,668
child rows**. Its §3 genre summary reports NINE normalized labels, which map
onto the seven rows above exactly: `key` = 1, `b0-main-r/q` = 2/3,
`b0-tail-r/q` = 4/5, `mid[k<e0-1]-r` and `mid[TOP=e0-1]-r` both = 6 (same
bound m′ ≤ m−1), `mid[k<e0-1]-q` = 7a, `mid[TOP=e0-1]-q` = 7b. Observed lex
deltas per label: `m-DROP` for all eight non-7b labels, `degA-DROP` for all
220 instances of 7b; **0 children dropping NEITHER coordinate**. Observed
ω-gains per label agree with the table's bounds, with `b0-main-r` the unique
label whose gain set is exactly {0}. The 220 m′ = m children are ALL of
genre 7b, all with deg a′ < deg a, all at deg a ≥ 1, all at d₀ ≥ 2 (the (B)
predictions), min gain +2. Assertions A1 (lex descent on every child),
A2 (every m′ = m child is 7b with deg a′ ≤ deg a − 1), A3 (none at
deg a = 0), A4 (none at d₀ = 1), A5 (gain ≥ 0, zero only at row 2), and
A6 — (LEDGER) itself re-verified on the HONESTLY RECOMPUTED double
development (dev by Φ′, then each Φ′-digit by Φ₀) over 752 probes / 4,438
nonzero digits, minimum slack 0 (the equality thread realized) — all PASS.
The table is evidence for the case split, not a substitute for (A)–(C): it
is a finite battery, and the proof above is what carries the ∀.

**[r2, G3 — the completeness leg made DURABLE: assertion A7.]** PE2's G3:
A1–A6 cannot certify the census's COMPLETENESS, which is exactly charge item
(1). A6 recomputes the double development of X *directly* and never calls
`children()`, so an enumeration missing a whole branch would have left every
assertion green — the prose and the script shared ONE transcription of the pass
identity (the standing extraction-corruption trap: a second leg pinned to the
first inherits its corruption). PE2 supplied the missing leg ad hoc
(Σ children == X, 0 mismatches on 752 nodes); r2 puts it INSIDE the committed
generator as **A7**, over the same 752 (a, m, j) probes A6 walks, with X built
by direct multiplication from Φ₀ and Φ′ — not from the pass identity — so a
missing or a spurious branch fails the check:

* **A7(i) SUM IDENTITY** Σ_children a′Φ₀^{m′}Φ′^{j′} = X exactly — **0
  mismatches over 752 nodes / 5,336 enumerated children**;
* **A7(ii) SHAPE** deg a′ < d₀ and m′ ≥ 0 for every child (so every child is a
  legal IH target) — 0 violations;
* **A7(iii) DIGIT-WISE dev-linearity** — the slot-wise sum of the children's
  double developments IS X's double development, i.e. the digits A6 walks are
  exactly the digits the children generate — 0 mismatches; this machine-checks
  (C)(i)'s additivity step ("polynomial devs carry no carries") at every probe;
* **A7(iv) BRANCHING** ≤ 2e₀+3 (G1's corrected count) — 0 violations, observed
  maximum per node exactly 2e₀+3 at e₀ = 2, 3, 4, 5, 6.

Regeneration discipline: the r1 DATA sections (§§1–6 — roster, the 2,668 child
rows, genre summary, the m′ = m stratum, LEDGER statistics, counter-instance
tree) come back BYTE-IDENTICAL; the diff old → new is **7 pure INSERTIONS**
(one provenance line in the header, six A7 verdict lines in §7) with **0
deleted and 0 modified lines**, and §7's pre-existing lines — "assertion
failures: 0", A1–A6 all PASS, "ANY CHILD DROPPING NEITHER COORDINATE: NO",
"OVERALL: ALL GREEN" — are unchanged. A7 adds assertions, not table content.
HONEST LIMIT: A7 is instance-level. It certifies that AT
THESE 752 NODES the enumeration is exhaustive and non-spurious; the ∀ is
carried by (A)'s algebra (Φ₀^{e₀} = Φ′ − Σ_{k<e₀}b_kΦ₀^k gives exactly the key
+ b₀ + (e₀−1) mid terms, and deg(a·b) ≤ 2d₀−2 forces exactly two digits per
branch and forbids a redigit cascade — PE2 re-derived both independently), and
A7 says nothing about the genre LABELS, only about the summands.

**(B) The deg a = 0 stratum (the second coordinate's base) and the d₀ = 1
corner.** At deg a = 0 row 7b is EMPTY: deg(a b_{e₀−1}) ≤ 0 + (d₀−1) < d₀,
so its q-digit vanishes and the top-mid branch contributes only its r-child.
Hence at deg a = 0 EVERY child drops m, and the lex induction needs no
separate base for the second coordinate — it bottoms out on the m < e₀ base
alone. Two consequences worth recording: (i) at most deg a ≤ d₀−1
consecutive m-preserving steps can occur from any node, so the recursion is
equally a single induction on m with an inner chain of length < d₀; (ii) at
d₀ = 1 NO branch ever produces a q-digit (deg(a·b) ≤ 0 < 1 = d₀), so the r0
single-m induction was in fact valid on the whole flat corner d₀ = 1 — which
is why no d₀ = 1 row could have exposed the defect, and why the
counter-instance below is at d₀ = 2. **[r2, G5 — "exactly" STRICKEN.]** The r1
wording "valid EXACTLY on the flat corner d₀ = 1" claimed a
characterization and is false: d₀ = 1 is SUFFICIENT, not necessary. The r0
clause "every child has m′ ≤ m−1" also holds VACUOUSLY at any node with no
m-preserving child — in particular on any orbit member whose top mid
b_{e₀−1} vanishes, since row 7b is then absent for every a. Such instances
exist at d₀ ≥ 2 in the note's own committed table: `A12` (ℤ₂, d₀ = 2, e₀ = 2,
genre `pure`) and `B14` (ℤ₂, d₀ = 2, e₀ = 5, genre `pure`) have all mids zero
and contribute NO row to the table's §4 m′ = m stratum. What (ii) is consumed
for is unaffected: d₀ = 1 rows cannot exhibit the defect, so the
counter-instance has to sit at d₀ ≥ 2.

**(C) The two consumers, re-closed on the lex order.** (i) *The induction.*
The IH is invoked only on the children of one pass; each is strictly lex-below
its parent by (A), so the appeal is legitimate. With the gains of (A) every
child satisfies (LEDGER) at its own ω(child) ≥ ω(X); dev-linearity (the
double dev of X is the digit-wise sum of the children's — polynomial devs
carry no carries) plus the ultrametric close then gives (LEDGER) for X.
(ii) *Termination/finiteness* (the job the false clause was doing). The
recursion tree is FINITELY BRANCHING, and by (A) has no infinite path, hence
is FINITE (König), so the dev-linearity sum is finite. **[r2, G1 — the count
CORRECTED; the r1 number was false.]** The r1 text said "≤ 2e₀+1 children per
node (row 1, rows 2–5, and ≤ e₀−1 realizations each of rows 6 and 7)"; its own
parenthetical sums to 1 + 4 + (e₀−1) + (e₀−1) = **2e₀+3**, and the note's own
committed table exhibits 7 children at e₀ = 2 (row `A1`, a = x+1, m = 2), which
already refutes "≤ 5". The correct bound is

    #children(node) ≤ 2e₀+3
      = 1 (row 1) + 4 (rows 2–5, counted per DIGIT: b₀-main r and q,
                       b₀-tail r and q)
        + (e₀−1) (row 6) + (e₀−1) (rows 7a+7b),

the r1 number having come from counting rows 2–5 as two BRANCHES while rows
6/7 were counted as digits. It is attained: the committed table's observed
maximum children per node is exactly 2e₀+3 at every e₀ in the battery
(e₀ = 2, 3, 4, 5, 6 → 7, 9, 11, 13, 15), and the bound is now machine-asserted
per node as A7(iv) (0 violations, 752 nodes). **ONLY FINITENESS of this count
is consumed** — by the König step in the previous sentence and by the
finiteness of (i)'s dev-linearity sum; 2e₀+3 is finite, so both go through
unchanged, and no step anywhere uses the count's VALUE. The quantitative claim
that does matter is the ρ depth bound next, which is independent of the
branching count. Explicit
depth bound: ρ(m, deg a) := m·d₀ + max(deg a, 0) strictly drops along every
child edge (an m-drop of ≥ 1 costs ≥ d₀ and can restore at most d₀−1 in the
second coordinate; an m-preserving step drops the second coordinate by ≥ 1),
so every root-to-leaf path has length ≤ m·d₀ + d₀ − 1. The r0 bound
⌈m/e₀⌉ survives in its correct scope: it bounds the ω-EQUALITY thread, whose
only genre is row 2 (gain 0), which drops m by exactly e₀ per step. ∎

[This IS the shift-descent bookkeeping: one key up costs h₁, exactly the
χ-chain's descent step (GRTW2 §3.4 rem. 1); the window-calculus ledger ω is
the tail-weight bookkeeping ILNRES S5.1 priced. Machine mirror: Q3/Q4 — the
tail never reaches the read.]

**[r1, F1 — CRITICAL (PE1): what changed, and what did not.]** The r0 proof
asserted "Every child is again of the lemma's shape with m′ ≤ m−1 (strict
descent; termination)" and closed "The ONLY 0-gain branch is b₀-main's
r-digit, which also strictly drops m: the ω(X)-thread terminates in
≤ ⌈m/e₀⌉ passes." The first clause is FALSE at row 7b (m′ = m), so the
strong induction on m alone had no IH at that child and the finiteness claim
rode the same clause; PE1 graded this CRITICAL and the ledger dropped
(TAIL-STAB) to PROVED-MODULO-F1. The LEMMA STATEMENT is byte-unchanged. NEW
at r1: the lex order, the seven-genre census with its per-genre descent
column, the (B) deg a = 0 / d₀ = 1 analysis, and the (C)(ii) finiteness with
an explicit depth bound. UNCHANGED in content and re-verified by PE1
independently: the base case, the one-pass identity, all ω-gains (now
displayed per digit, hence sharper on rows 3, 5, 7 than r0's per-branch
lower bounds), the gain-0 census (row 2 only), CONTENT, dev-linearity, the
(LEDGER) ⟹ w₂(X) ≥ ω(X) tie and the read-kill close, and the ⌈m/e₀⌉
equality-thread bound in its correct scope.

**[r2, G2 — that attribution is CORRECTED; it was self-refuting.]** The
sentence above put "all ω-gains (now displayed per digit, hence sharper on rows
3, 5, 7 than r0's per-branch lower bounds)" inside the list of things
"UNCHANGED in content and re-verified by PE1 independently" — but bounds that
are NEW and SHARPER at r1 are by construction not unchanged, and PE1, which
read the r0 table, cannot have verified them. The honest split:

* **What PE1 re-verified** (verbatim scope, from its F1 repair observation:
  "all four ω-gain rows of the branch table (checked, using
  e₀·amin(k) ≥ (e₀−k)h₀+1 which I re-derived from gcd(e₀,h₀) = 1 …)"): r0's
  **four PER-BRANCH** ω-gain rows, plus the base case, the one-pass identity,
  the gain-0 census (row 2 only), CONTENT, dev-linearity, the
  (LEDGER) ⟹ w₂(X) ≥ ω(X) tie and read-kill close, and the ⌈m/e₀⌉ bound in
  its correct scope.
* **What PE1 never saw**: the r1 table's **eight PER-DIGIT** gain entries
  (rows 1, 2, 3, 4, 5, 6, 7a, 7b). Rows 3, 5, 7a, 7b are new at r1.
* **Who first hostile-read them**: **PE2** (report
  `LIFTCORNER_passPE2_report.md`, commit 3367f3c, G2's "for the record"), which
  re-derived ALL EIGHT independently — row 1 = exactly +h₁; row 2 =
  e₁e₀[w₀(r) − w₀(a) − h₀] ≥ 0; row 3 ≥ e₁h₀; row 4 ≥ e₁e₀; row 5 ≥ e₁e₀+e₁h₀;
  row 6 ≥ e₁; rows 7a/7b ≥ e₁(h₀+1), with e₀·amin(k) ≥ (e₀−k)h₀+1 re-derived
  from gcd(e₀,h₀) = 1 — and found them CORRECT and, against the battery's
  minimal (e₁, h₀, e₀), TIGHT.

The r1 charge list also pointed away from these bounds (its items (1)–(6) name
neither) — the same defect PE1 recorded against r0's charge list, recurring one
round later on a different step. r2 adds charge item **(7)** for them (grade
box). Their audit status after r2, stated plainly: displayed at r1, re-derived
ONCE by a hostile pass (PE2), and now named in the charge list — one
independent re-derivation, no acceptance credit, PE3 owed.

**[r1, F1 — the counter-instance's own descent chain, numerically.]** PE1's
instance: O = ℤ₂, d₀ = 2, e₀ = 2, h₀ = 1, Φ₀ = x²+x+1, b₀ = 2 (so ĉ′ = 1,
t₀ = 0, c′ = 1), b₁ = 2x (w₀ = 1 = amin(1)); Φ′ = Φ₀² + b₁Φ₀ + b₀ =
x⁴+4x³+5x²+4x+3. Take e₁ = h₁ = 1, so γ₂ = e₁e₀h₀+h₁ = 3 and
ω(aΦ₀^mΦ′^j) = 2w₀(a) + m + 3j. Root X = xΦ₀^2, i.e. (m, deg a) = (2, 1),
ω(X) = 2. One pass, its four nonzero branches (mid digits from
2x² = 2Φ₀ − 2x − 2, i.e. r = −2x−2, q = 2, negated by the identity's sign):

    key        → a′ = x      (m′,j′) = (0,1)  ω = 3  gain +1 = h₁        [m-DROP]
    b₀-main r  → a′ = −2x              (0,0)  ω = 2  gain  0            [m-DROP]
    mid[1] r   → a′ = 2x+2             (1,0)  ω = 3  gain +1 = e₁       [m-DROP]
    mid[1] q   → a′ = −2               (2,0)  ω = 4  gain +2 = e₁(h₀+1)
                                     [m′ = m = 2, deg a′ = 0 < 1 = deg a: row 7b]

The r0 induction stops dead at the fourth child. Under the lex order that
child, (m, deg a) = (2, 0), is expanded once more:

    key        → a′ = −2              (0,1)  ω = 5  gain +1             [m-DROP]
    b₀-main r  → a′ = 4               (0,0)  ω = 4  gain  0            [m-DROP]
    mid[1] r   → a′ = 4x              (1,0)  ω = 5  gain +1            [m-DROP]

— and NO mid q-child, exactly as (B) predicts at deg a = 0 (a·b₁ = −4x has
degree 1 < 2 = d₀). All six leaves sit at m ≤ 1 < e₀ = 2, i.e. on the base
case: the tree is 8 nodes, depth 2, well inside the (C)(ii) bound
m·d₀ + d₀ − 1 = 5. (This whole chain is machine-printed in §6 of the r1
table, digit for digit.) Independent tie (not via the recursion): the honest double
development of the root is

    xΦ₀² = (x−2)·Φ′ + (6x+2)·Φ₀ + (−2x+4),

digits at (j,i) = (1,0), (0,1), (0,0) with weights 3, 3, 2 against
ω(X) = 2 — (LEDGER) holds, slacks 1, 1, 0, and the equality thread is the
(0,0) digit, precisely row 2's gain-0 thread.

### S4.2 LEMMA (READ-EQ) — the Φ′-tower reads = the Φ″-tower reads

Every 2-read battery object (anchors φ_γ = π^{u₁}Φ₀^{s₁}K^{s₂}; pair
products φ_γφ_{γ′}; K = the tower's own key) has IDENTICAL level-2 reads
(weight, grid, every slot coefficient) on the Φ′- and Φ″-towers. *Proof.*
The towers share every read datum (reads, ψ₁, K₂, and the LETTER z₁′ = −c′
in ε₁) — only key bytes differ. (a) Anchors and δ₁ = 0 products are
π^uΦ₀^sK^S with s < e₀ < deg: single K-slot coefficient π^uΦ₀^s — identical
bytes, the key power never opened (any δ₂-carry is grid bookkeeping, no
reduction at the top level of a 2-read). (b) δ₁ = 1 products (g₀ = 1 ⟹
s₁+s₁′ ≤ 2e₀−2: EXACTLY one overflow): P = π^UΦ₀^{e₀+S₁″}K^{S₂},
ω(P) = Γ := γ+γ′ (the split identity γ = e₁(e₀u₁+s₁h₀) + s₂γ₂). One pass on
each tower; compare children. Key child π^UΦ₀^{S₁″}K^{S₂+1}: identical
bytes, ledger Γ+h₁ — strictly above on BOTH towers (reads 0 both; it is the
E₁ digit). b₀-main children: −π^{U+h₀}ĉ′Φ₀^{S₁″}K^{S₂} vs
−π^{U+h₀}lift(c′)Φ₀^{S₁″}K^{S₂}: single digits; their difference has
w₀(ĉ′−lift(c′)) ≥ 1 (both lift c′), ledger ≥ Γ + e₁e₀. Φ′-only children
(t₀, mids): ledger ≥ Γ+1, and by TAIL-STAB every digit they generate stays
> Γ. So the on-Γ-line digit content coincides; all deviations are strict
π-excess at their slots; res kills them and the ultrametric keeps w₂ = Γ and
the on-line status equal on both sides. Reads agree slot-by-slot. ∎

### S4.3 THEOREM (the corner discharge) and the two corollaries

**THEOREM.** For EVERY orbit member Φ′ (any residue c′ ≠ 0), the 2-read
ITER-LAW display holds on the Φ′-tower with the letter the lift carries:
c^{Φ′}(γ,γ′) = z̄^{δ₂}·(z₁′)^{D₁}, z₁′ = −c′, all γ,γ′ ∈ W₂. *Proof.* READ-EQ
transports every anchor value, pair value and cocycle to the Φ″-tower; Φ″ is
a STANDARD-LIFT instance of the accepted class with ψ₀ ↦ ψ₀^{(ξ)} (same
(e,h,g) data, ψ₀^{(ξ)}(0) = c′ ≠ 0), where the ACCEPTED ITER-LAW gives the
display with its letter z₁′. ∎ [Machine: Q3 4,176/0.]

**[r4, F4-5 — NOTATION, one line, fixing a `c′` collision inside the unit's
headline identity; a pure renaming, no content changes.]** From here on
**`c^{Φ′}(γ,γ′)`** denotes the 2-read COCYCLE on the Φ′-tower and `c_base(γ,γ′)`
the cocycle on the base standard tower, while **`c′` (no arguments) stays the
RESIDUE SCALAR** `res(b₀/π^{h₀}) ∈ K₀` of S1. The r1–r3 text wrote the same
cocycle two ways — `c(γ,γ′)` in the THEOREM and `c′(γ,γ′)` in COR 2 — and the
second collides with the scalar inside COR 2's own display (`ξ := c₀/c′`); both
are renamed to `c^{Φ′}` here, and they were always the same function (PE3
recorded the collision, PE4 numbered it F4-5). **S1's CANDIDATE display is
sealed pre-run text and is NOT edited**: it writes this cocycle as `c′(γ,γ′)`,
and this bracket is the correction of record for it and for S2's sealed Q7
and Q9 sheet rows, whose `c′` is likewise this cocycle in each (the same
precedent as the sealed runner's docstring under [r3/r4, F4-1]); with Q9 the
census is COMPLETE — warrant of record at OCCURRENCE level **[r7, F7-1]**:
PE7's independent re-execution (report `LIFTCORNER_passPE7_report.md`, commit
58f7060) counts, at its HEAD 91f0cde, **51 `c′` occurrences on 47 lines =
34 residue-scalar + 4 covered-cocycle (S1's CANDIDATE display ×2, S2's Q7
row, S2's Q9 row — all inside this correction of record) + 13
mention/quotation — NO fourth bare-`c′`-as-cocycle site**; at PE6's HEAD
46e6e88 the same sweep gives 46 occurrences on 42 lines (four lines carry
two, all scalar pairs) — PE6's "42" was its hit-LINE count, and the four
uncounted occurrences are scalar second occurrences on already-classified
lines, so no site was lost.

**COR 1 ((ITER-LAW-LIFT), the corner).** ξ = 1 slice (c′ = c₀): the display
holds UNCHANGED for every LAWFUL monic lift — the 2-read (ITER-LAW-LIFT) is
proved at g₀ = 1 ∧ δ₁ = 1, exactly where it was open (ITERLAW S7: only
PAIR-VAL Case II consumes Φ₁'s form; all other strata lift-form-free).
[Machine: Q10 + wave-18's 104,404/0.]

**COR 2 (the χ-covariance; RESCOPED at r1).** Across the HARNESS monic-lift
orbit of S1 the 2-read display transports by the letter alone: for every
orbit member Φ′ with residue scalar c′ and ξ := c₀/c′,

    c_base(γ,γ′) = c^{Φ′}(γ,γ′)·ξ^{D₁}   for all γ, γ′ ∈ W₂.

*Proof.* The THEOREM applied on the Φ′-tower and on the base tower, plus
z₁ = ξ·z₁′ (S1) and the lift-independence of D₁ (S1/S2). ∎ This is the
corner-degenerate FORM that W-2 clause 3's value-layer transport predicts,
and (with Q9's sharpness) evidence that it is the true covariance there.
Nothing beyond the displayed identity on the harness orbit is claimed.
[Machine: Q7 4,176/0 measured-vs-measured; Q9 sharpness 1,576 fires exact.]

**[r1, F3 — WITHDRAWN identification + what is still owed for the W2-OPEN-1
tie.]** The r0 text said this corollary "is W-2 clause 3's value-layer
statement (W2-OPEN-1) RESTRICTED to the base junction at the corner — now
PROVED at this note's grade there, upgraded from instance-confirmed". That
identification is WITHDRAWN as underived (PE1 F3): no equivalence between
COR 2 and any slice of W2-OPEN-1 is derived anywhere in this note.
W2-OPEN-1 as recorded (GRTW2 §5.3) quantifies over the committed
value/cocycle battery — K5/K6/K7, K12 = π-shift/ρ-monodromy, K1–K4/K13
riding — WITH THE TRANSPORTED CLASSIFIER LIFTS substituted for the harness
lifts. Two things are therefore owed before even the base-junction slice of
that statement may be claimed, and NEITHER is in this note: **(a) an
orbit-membership display** — that the transported CLASSIFIER key at the base
junction is an S1 orbit member (monic, degree e₀d₀, w₁ = e₀h₀, nonzero
order-1 residual y + c′), which needs the GMN key-polynomial normalization
plus W2-C3(ii), not merely the harness parametrization this note uses;
**(b) the battery legs outside the display/anchor families** — K12 above
all — under the restriction. Until both are displayed, COR 2 is a statement
about the harness monic-lift orbit only. The unit's W-2 grade cap (grade
box) is unaffected: it was and remains driven by S1's and this corollary's
consumption of clause 3's FRAMING.

**PROP (propagation to every level — the S0.1 rider leg).** (ITER-LAW-n)
for every lawful monic Φ₁ at the corner, all n: the [ILN] chain consumes
Φ₁'s explicit bytes only through (i) monicity/degree/w₁Φ₁ = e₀g₀h₀ (shared
by every orbit member) and (ii) the level-1 base package (= [IL], replaced
here by COR 1; at n = 1 clause (ii) is ITERLAW S7's own display). Riding
S0.1's verbatim propagation, the discharge lifts to every rung AT [ILN]'s
OWN conditionality (T-class/(RM-m)/DCX ledger unchanged). VERIFY-TARGET for
the arc: the clause-(ii) census at rungs ≥ 2 (no rung leg opens Φ₁'s bytes
outside the level-1 package) is NOT re-proved here.
**[r4, F4-4 — the CITE for that census is re-pointed; the r3 wording, quoted
and superseded, was "is cited from the [ILN]/ILNRES consumption tables, not
re-proved here".]** That cite was false as to location: ITERLAWN_PROOF's S7
dependency/exemption sweep (22 rows) and ILNRES S6's "consumption census" are
both keyed to *accepted-package* consumption (which levels, which of
[IL]/[IL3]†/(RM-m)/DCX), and NEITHER contains any row about how much of Φ₁'s
explicit form a rung leg opens (PE4 read all 22 rows; the nearest, rows 1 and
10, are level-scope claims). **The true site of record, and the one pin a
rung-≥2 census must clear, is ITERLAWN's own r4 erratum:** its S0.3 clause
table, L6 row, now reads "PROVED given only the [IL] base … **[attribution
(errata r4, 2026-08-03; PE4-F1): + S4.1 at rungs ≥ 2 — the canonical-lift
certification (WELL-DEF-(n)/(R1) + C_k existence) consumed via the S0.1 class
pin and the S4.2 degree-telescope input; S4.1's m = 1 base rides [IL3]†; rung 1
given [IL] alone]**" (same erratum: sweep rows 4/12/19 at status C-r4, and the
S4.1 → L6-(n) DAG edge added). **The pin, named explicitly**, is ITERLAWN
S0.1's Lifts clause, verbatim: "**Φ₁ := the STANDARD LIFT of ψ₀**
(grb_order2_check :499–507); for 1 ≤ m ≤ n−1, Φ_{m+1} := the CANONICAL
ε_m-CORRECTED LIFT of ψ_m" — i.e. exactly the clause PROP relaxes on the Φ₁
axis. So a rung-≥2 clause-(ii) census must show that S4.1/WELL-DEF-(n) and the
S4.2 telescope read Φ₁ only through monicity, degree e₀d₀ and w₁Φ₁ = e₀g₀h₀
(plausible — the C_k are built from ψ_m, γ_{m+1}, ε_m, realize_m and Φ_m, and
Φ₂ = Σ_k C_kΦ₁^{e₁k} uses Φ₁ only as a power) — **an argument this note does
not make, and which neither the two formerly cited tables nor ITERLAWN's own
r4 erratum supplies** (PE4 read all 22 sweep rows and ILNRES S6's census; no
row is about how much of Φ₁ a rung leg opens). Charge item (5)
is re-scoped to exactly that: the census is OWED, its site of record is
ITERLAWN's r4 erratum, and the deeper-level fence of S5 is untouched by it.

**Grade box + W-2 consumption census (the cap).** This note: ATTEMPT 0/2 —
r1 is a REPAIR round, not a pass; one hostile pass has run (PE1: 1 CRITICAL
+ 3 gaps, all four repaired here) and the arc is OWED on THIS text.
**[r2 — grade box updated.]** TWO hostile passes have now run: **PE1** on the
r0 text (1 CRITICAL + 3 gaps → repair round r1) and **PE2** on the r1 text
(**0 CRITICAL + 5 gaps** → this repair round r2; report
`LIFTCORNER_passPE2_report.md`, commit 3367f3c). PE2 confirmed the F1 repair
holds and re-derived its load-bearing pieces independently, but it returned 5
gaps, so **no acceptance slot closed: the counter stays 0/2**, and the r2 edits
(G1–G5) are themselves unaudited. **PE3 — a fresh hostile pass on THIS text —
is the next acceptance attempt.**
**[r3 — grade box updated.]** THREE hostile passes have now run: **PE1** on the
r0 text (1 CRITICAL + 3 gaps → r1), **PE2** on the r1 text (0 CRITICAL + 5
gaps → r2), and **PE3** on the r2 text — the arc's FIRST acceptance attempt
(**0 CRITICAL + 5 gaps** → this repair round r3; report
`LIFTCORNER_passPE3_report.md`, commit 39ea0db). PE3 found no defect in the
mathematics it audited, and all five of its gaps are evidence-DESCRIPTION
defects (F-A the ψ₁-assert ranking, F-B the G4 witness display, F-C a machine
quote attributed to PE2, F-D the grade box's own audit labels, F-E a zero-count
family reported as a result), so no r3 edit touches the chain either. **The
counter stays 0/2** — 5 gaps is not a clean pass, and a repair round is not a
pass. Audit state after r3, plainly: charge items **(1), (2), (7)** have been
re-derived by TWO hostile passes (PE2, PE3) with no acceptance credit; the r2
edits have been read ONCE (PE3); **the r3 edits are UNAUDITED**. **PE4 — a
fresh hostile pass on THIS text — is the next acceptance attempt.**
**[r4 — grade box updated.]** FOUR hostile passes have now run: **PE1** on the
r0 text (1 CRITICAL + 3 gaps → r1), **PE2** on the r1 text (0 CRITICAL + 5
gaps → r2), **PE3** on the r2 text — the arc's FIRST acceptance attempt (0
CRITICAL + 5 gaps → r3) — and **PE4** on the r3 text, the SECOND acceptance
attempt (**0 CRITICAL + 6 gaps** → this repair round r4; report
`LIFTCORNER_passPE4_report.md`, commit 8b53efa). PE4 found no defect in the
mathematics and re-derived, from scratch, the eight per-digit ω-gain bounds,
the census/lex/ρ consumers, READ-EQ digit by digit on both towers, the
counter-instance's two passes and its double-development tie, and the THEOREM
+ COR 2 on a concrete ℤ₂/𝔽₄ orbit member; all six of its gaps are
evidence-description / bookkeeping defects (F4-1 the assert pair, F4-2 an
un-superseded refuted S5 clause, F4-3 the "bit-identical" provenance, F4-4
PROP's census cite, F4-5 the `c′` collision, F4-6 the NR-1 bookkeeping
sentence), so no r4 edit touches the chain. **The counter stays 0/2** — 6 gaps
is not a clean pass, and a repair round is not a pass. Audit state after r4:
items **(1), (2), (7)** have been re-derived by **THREE** hostile passes (PE2,
PE3, PE4) with NO acceptance credit; the r2 edits have been read twice (PE3,
PE4) and the r3 edits once (PE4); **the r4 edits are UNAUDITED**. **PE5 — a
fresh hostile pass on THIS text — is the next acceptance attempt.**
**[r6 — grade box brought forward (the first since r4; the close just above is
dated [r4] text).]** SIX hostile passes have now run — the two since the [r4]
entry: **PE5** on the r4 text, the THIRD acceptance attempt (0 CRITICAL + 5
gaps → r5, the five one-line fixes; report `LIFTCORNER_passPE5_report.md`,
commit a5212e8), and **PE6** on the r5 text, the FOURTH acceptance attempt
(**0 CRITICAL + 3 gaps** → this repair round r6; report
`LIFTCORNER_passPE6_report.md`, commit f2b48e7). PE6's line-audit found ZERO
defects in the r5 diff itself (all 32 insertions true, all five fixes
correctly placed — the arc's first zero-new-defect round) and no defect in the
mathematics on its sixth hostile reading; all three of its gaps are
record-surface defects (F6-1 the STATUS BLOCK's stale NEXT/AUDIT bullet and
this box's stale close, F6-2 the sealed Q9 row as a third bare-`c′` cocycle
site, F6-3 the footer dating record missing r5), cured at r6. **The counter
stays 0/2** — 3 gaps is not a clean pass, and a repair round is not a pass.
Audit state after r6: the r6 edits are UNAUDITED; the r5 edits were read once
(PE6); **PE7 — a fresh hostile pass on THIS text — is the next acceptance
attempt.**
**[r7 — grade box brought forward (the close just above is dated [r6]
text).]** SEVEN hostile passes have now run — the one since the [r6] entry:
**PE7** on the r6 text, the FIFTH acceptance attempt (**0 CRITICAL + 1 gap,
minor** → this repair round r7, the one-clause F7-1 fix; report
`LIFTCORNER_passPE7_report.md`, commit 58f7060). PE7's line-audit verified
the r6 diff true and correctly placed at every hunk except the one census
clause (F7-1, a transcribed unit mismatch: PE6's "42 occurrences" is a
hit-LINE count), found the record system consistent and true at HEAD for
the first time in the arc, judged r6's disclosed deviation CORRECT, and
found no defect in the mathematics on its seventh hostile reading. **The
counter stays 0/2** — a gap is not a clean pass, and a repair round is not a
pass. Audit state after r7: the r7 edits are UNAUDITED; the r6 edits were
line-audited by PE7; **PE8 — a fresh hostile pass on THIS text — is the next
acceptance attempt.** Charge
(r1-updated, item (7) added at r2 per PE2 G2; the r0 charge list named neither
the step that broke nor the
r1 argument — PE1 F1's closing observation, accepted): **(1) the S4.1
seven-genre child census's COMPLETENESS** — that the pass identity, after
the b₀-split and the r/q redigit, produces no branch outside rows 1–7 — and
the row-7b degree drop; **(2) the lex-order finiteness argument** ((C)(ii):
finite branching + the ρ depth bound); **(3)** the CONTENT sub-lemma's
base-fact status; **(4)** the READ-EQ on-line-content/ultrametric close;
**(5)** PROP's census cite; **(6)** COR 2's rescoped statement (the F3 box's
(a)/(b) are owed for any W2-OPEN-1 tie, and are NOT part of this note's
claim); **[r2, G2] (7) the EIGHT PER-DIGIT ω-gain bounds** of (A)'s last column
(rows 1, 2, 3, 4, 5, 6, 7a, 7b) together with the CONTENT application that
derives them per digit — new at r1, never named by the r1 charge list,
re-derived once by PE2 (correct and tight) and, per (A)'s [r2, G4] bracket, no
longer resting on the stricken r-to-q identity. W-2
consumption: COR 2 and the S1 orbit frame consume GRTW2 clause 3 (the
ψ-transport definition + its corner degeneration) — GRTW2 is itself 0/2, so
**the unit's grade is CAPPED at that consumption, as charged**. Honest
decoupling fact the arc may use: the COR 1 chain (TAIL-STAB + READ-EQ +
accepted ITER-LAW) is W-2-free — if W-2's arc lags, the ξ = 1 discharge
stands on this note's own arc alone.

## S5. Consequence display (what [ILN]'s rider becomes; at the capped grade, pending arcs)

ONCE THIS NOTE'S ARC CLOSES (and not before — no ledger or accepted text is
edited now): ITERLAWN S0.1's rider "(ITER-LAW-LIFT) open exactly at
g₀ = 1 ∧ δ₁ = 1; nothing is claimed for any non-canonical lawful lift at any
level" becomes, on the Φ₁ axis: "(ITER-LAW-LIFT) DISCHARGED at attempt grade
(capped by the W-2 0/2 consumption; ξ = 1 core W-2-free): ITER-LAW-n holds
for EVERY lawful monic Φ₁, every n, at [ILN]'s own conditionality, and
covariantly for the full Φ₁-orbit by the χ-law".

**[r4, F4-6 — the bookkeeping sentence that followed is STRICKEN and replaced
by the three paragraphs below. The r3 wording, quoted in full and superseded:**
"NR-1 then leaves the ILNRES residual list; the T-class(n) conditionality of
record shrinks to NR-2/NR-3 (+ NR-4's own closing arc). NOT covered, said
plainly: non-canonical lawful lifts at DEEPER levels (Φ_{m+1}, m ≥ 1) — a
separate corner (the g_m = 1 analogue), never part of (ITER-LAW-LIFT)'s
displayed statement (wave-18 S0), stays open as its own priced item."**]**

**What this note delivers, exactly.** The **Φ₁ corner** of NR-1:
(ITER-LAW-LIFT) for every lawful monic lift Φ₁ at g₀ = 1 ∧ δ₁ = 1 (COR 1),
plus the χ-covariance across the harness Φ₁-orbit (COR 2) and PROP's rung
propagation at [ILN]'s own conditionality. That is exactly the deliverable of
the spec of record, ILNRES S5.1 — "Extend the [IL] L7 Case-II analysis to an
arbitrary lawful lift Φ₁′ = Φ₁ + (π-excess) at g₀ = 1 ∧ δ₁ = 1, then ride
S0.1's verbatim propagation" — and exactly the residual as DISPLAYED at
wave-18 S0: "the honest OPEN displayed lemma **(ITER-LAW-LIFT)**: ITER-LAW for
every lawful monic lift Φ₁" (Φ₁ only; both quotes verified at source, and PE4
independently confirmed the delivery matches the spec). **So the honest claim
is: NR-1's Φ₁ corner is DISCHARGED PENDING THIS NOTE'S ARC** (attempt 0/2,
W-2-capped; the ξ = 1 core W-2-free). No residual leaves any list until the arc
closes, and this note edits no ledger.

**The discrepancy, stated neutrally.** NR-1 as RECORDED in ILNRES S1 is wider
than the residual as DISPLAYED at wave-18 S0: the recorded statement quotes the
[IL] rider "nothing is claimed for any non-canonical lawful lift **at any
level**", which reads on Φ_{m+1} for m ≥ 1 as well. This note covers the Φ₁
level only. Under the wave-18 / S5.1 reading NR-1 is addressed in full here;
under the ILNRES S1 "at any level" reading a deeper-level remainder survives.
The two readings live in different notes of record, and this unit does not
choose between them.

**Disposition of the deeper levels — NOT a new priced item.** Non-canonical
lawful lifts at levels m ≥ 1 (Φ_{m+1}, the g_m = 1 analogue) are **not covered
here and are not priced by this note**; r3's "stays open as its own priced
item" is withdrawn, because this unit has no authority to create a residual and
an uncited new one would collide with ILNRES S7's recorded outcome that "S1's
FOUR-MEMBER residual list is COMPLETE relative to the sources of record — NO
FIFTH RESIDUAL EXISTS". **Flagged for the next fold as an ILNRES-side ERRATUM
CANDIDATE (ILNRES is NOT edited here):** ILNRES's own ledger entry should rule
whether the "at any level" clause of NR-1's recorded statement is (a) a scope
fence in the genre of its perimeter fact (iii) ("orders ≥ 3 untouched … is
subsumed by [ILN] itself"), in which case the Φ₁ corner is the whole of NR-1
and this note discharges it on its arc; or (b) a live conditionality, in which
case it is a fifth member and the S7 completeness sentence needs amending.
Until ILNRES rules, **nothing here re-prices anything**, and the consequence
display above should be read as changing the **Φ₁ axis** of the rider only.

**STATUS BLOCK [r4; edited r5, r6, r7] — REGENERATED from a minimal five-line template.** This
block is the note's whole status of record; it replaces the r1, r2 and r3
STATUS LINEs wholesale (they are quoted verbatim, byte-unchanged, inside the
[r4, ARCHIVE] region below). The status surface produced findings in three
consecutive passes — PE2's G2 attribution, PE3's F-C/F-D, PE4's F4-2/F4-3 —
so it is now five lines and nothing else. **Standing rule for future rounds:
edit these five lines; do not grow a sixth.**

* **ARC.** PE1 (1 CRITICAL + 3 gaps) → r1 → PE2 (0C + 5G) → r2 → PE3 (0C + 5G;
  the arc's FIRST acceptance attempt) → r3 → PE4 (0C + 6G; the SECOND
  acceptance attempt) → r4 → PE5 (0C + 5G; the THIRD acceptance attempt) →
  r5 (the five one-line fixes F5-1…F5-5) → PE6 (0C + 3G; the FOURTH
  acceptance attempt) → r6 (the three record-surface fixes F6-1…F6-3) →
  PE7 (0C + 1 minor; the FIFTH acceptance attempt) → **r7 (this round: the
  one-clause census-unit fix F7-1, nothing else)** → **PE8 = the next
  acceptance attempt.**
* **COUNTER.** Acceptance **0/2** — no pass has been clean, and a repair round
  is not a pass. The grade is CAPPED by this unit's W-2 consumption (GRTW2
  itself 0/2); the COR 1 / ξ = 1 chain is W-2-free, so if W-2's arc lags the
  ξ = 1 discharge stands on this note's own arc alone.
* **PROVED (at that grade).** (TAIL-STAB) by S4.1 as repaired at r1, statement
  byte-unchanged, its argument re-derived independently by PE2, PE3 and PE4;
  and on it READ-EQ, the THEOREM, **COR 1** ((ITER-LAW-LIFT) at the corner —
  and δ₁ = 1 is EMPTY at e₀ = 1, so S4's e₀ ≥ 2 Setting costs COR 1 nothing),
  and COR 2 on the harness orbit. S3's corner
  measurement (25,409 checks / 0 violations) is machine fact either way.
* **CONDITIONALITY.** Grade-box charge items (1)–(7), of which **(5) PROP's
  rung-≥2 clause-(ii) census is OWED** with its site of record re-pointed at
  [r4, F4-4]; COR 2's W2-OPEN-1 tie needs (a) and (b) of the [r1, F3] box;
  NR-1's discharge is the **Φ₁ corner** only, pending this note's arc, with the
  deeper-level reading flagged as an ILNRES-side erratum candidate ([r4,
  F4-6]); wave-18's price sheet is settled MODULO this note's own arc, not "in
  full".
* **NEXT / AUDIT STATE.** PE8, a fresh hostile pass on THIS text. Unaudited
  going in: **the r7 edits** (the r6 edits were line-audited by PE7 — all
  four hunks verified true except the one census clause, its F7-1 — the r5
  edits by PE6, the r4 edits by PE5; earlier edit sets read twice or more).
  Items (1), (2), (7): re-derived by three hostile passes, NO acceptance
  credit. Both machine legs BYTE-FROZEN and re-run clean at PE7
  (sealed runner exit 0, 25,409/0, md5 `ccb4351c92573f5f962cae4ae952d8dd`,
  `git diff dafc0b5 HEAD` = 0 bytes, output identical modulo timing fields;
  children table regenerates byte-identically, A7's four legs PASS).

**[r4, ARCHIVE — the three superseded STATUS LINEs (r1, r2, r3) follow between
the ARCHIVE-BEGIN / ARCHIVE-END markers, quoted BYTE-UNCHANGED.]** Nothing
between the markers is live: it is superseded wholesale by the five-line STATUS
BLOCK above, and is kept only because this note's discipline never silently
deletes superseded wording. THREE corrections apply INSIDE the archive and are
stated here so no sentence in it can be misread as current:
**(1) [F4-2]** the r1 STATUS LINE's clause "S2 disclosure (c) corrected to what
the runner actually asserts (F4)" is **REFUTED** — r3's own F-A showed r1's F4
repair landed on the wrong half of its sentence, and r4's F4-1 shows the other
half was wrong too; the FINAL description of the runner's two asserts is S2
disclosure (c)'s **[r4, F4-1]** bracket (BOTH inert, nothing consumes either,
the soundness is `mk_field_ext`'s g = 1 reading). r3 bracketed the header
occurrence of this claim and missed this one; that omission is what F4-2
records, and the sentence is now dead text inside the archive.
**(2) [F4-3]** the r2 STATUS LINE's `[r3, F-C]` bracket says PE2's own
qualification was "dropped in the r2 paraphrase" — the **PROVENANCE is wrong**:
PE2's report carries the unqualified word "bit-identically" at three sites and
the qualified form at one, so the overstatement ORIGINATES with PE2 and r2
TRANSCRIBED it. The factual correction is unchanged and is not in dispute: the
sealed runner's output file is **identical modulo timing fields**, every counted
quantity is identical, and the children table is bit-identical. The corrected
provenance of record is the **[r4, F4-3]** bracket in the r2 header round.
**(3) [F4-1, third site]** the r3 STATUS LINE's own summary of F-A — "the
sealed runner's ψ₁ assert is now described as the no-op it is and the K₂
one-element check **as the only substantive half of that pair**" — carries the
same refuted promotion; `K2["one"]` is a constant of (d₀, g₀, g₁) and BOTH
asserts are inert. Same final description: S2 disclosure (c)'s [r4, F4-1]
bracket.

<!-- ARCHIVE-BEGIN (superseded at r4; retained verbatim; NOT live status) -->

**STATUS LINE (r1-honest; supersedes the r0 sentence "The wave-18 sketch's
one open step (TAIL-STAB) is CLOSED by S4.1 (its ω is this ledger; the
monomial form is subsumed); wave-18's price sheet is settled in full").**
As of repair round r1: (TAIL-STAB) is PROVED by S4.1 AS REPAIRED — the r0
proof's strict-descent clause (m′ ≤ m−1 at every child) was REFUTED by PE1
at the top-mid q-child (m′ = m), the lemma STATEMENT is byte-unchanged, and
the argument now rides the lexicographic (m, deg a) descent over a
seven-genre child census derived from the committed examples-first table
(`liftcorner_tailstab_children.py` / `..._table.txt`). Its ω is this ledger
and wave-18's monomial form is subsumed, as r0 said. Grade: **attempt 0/2**
— PE1 was a hostile pass but returned 1 CRITICAL, so no acceptance credit
accrued; the r1 argument itself has NEVER been hostile-read, and the grade
box's charge (1)–(2) names exactly which of its steps are unaudited. So:
wave-18's price sheet is settled MODULO this note's own arc, not "in full".
The three r1 gap repairs, for the record: ĉ′/t₀ now defined in-note (F2);
COR 2's W2-OPEN-1 identification WITHDRAWN and rescoped, with (a)/(b) owed
(F3); S2 disclosure (c) corrected to what the runner actually asserts (F4).
Everything downstream of (TAIL-STAB) — READ-EQ, the THEOREM, COR 1, PROP —
stands exactly as PE1 verified it GIVEN (TAIL-STAB), and the corner
measurement (S3, the covariance carrying the corner) is machine fact,
untouched by F1 in either direction.

**STATUS LINE [r2] (supersedes the r1 clause "the r1 argument itself has NEVER
been hostile-read, and the grade box's charge (1)–(2) names exactly which of
its steps are unaudited" — the r1 argument HAS now been hostile-read, and the
charge list has grown).** As of repair round r2: **(TAIL-STAB) is PROVED by
S4.1 as repaired at r1 and confirmed at PE2 — 0 CRITICAL** on the r1 argument,
with PE2 independently re-deriving the 9 ↦ 7 genre mapping (total, disjoint),
row 7b's degree drop at every boundary (deg a = 0, deg b = 0, a or b zero), the
two emptiness strata as PROVED rather than measured, and the ρ depth function's
strict drop on every child edge. **THE ARC:** PE1 (1 CRITICAL + 3 gaps) → r1 →
PE2 (0 CRITICAL + 5 gaps) → **r2 (this round, G1–G5 applied)** → **PE3 = the
next acceptance attempt**. Grade: **attempt 0/2, unchanged** — PE2 was a
hostile pass and found no critical, but 5 gaps is not a clean pass, and the r2
repairs (the corrected branching count, the corrected PE1 attribution, the new
A7 assertion, the stricken r-to-q gain identity, the weakened d₀ = 1 claim)
have never been read by anyone. **[r3, F-D — the audit LABELS on charge items
(1)–(2) are corrected (the r2 sentence was internally inconsistent), and the r2
clause "the r2 repairs … have never been read by anyone" is SUPERSEDED: PE3 has
now read them.]** The r2
wording, quoted and superseded: "Which steps are unaudited is now the grade
box's charge **(1)–(2) and (7)**, plus the r2 edits themselves." But item (1)
(the seven-genre census's COMPLETENESS + the row-7b degree drop) and item (2)
(the lex-order finiteness argument: finite branching + the ρ depth bound) are
exactly what the SAME paragraph credits PE2 with re-deriving, so "unaudited"
contradicts its own two preceding sentences; item (7)'s label two hundred lines
earlier already had the accurate pattern ("re-derived ONCE by a hostile pass
(PE2) … one independent re-derivation, no acceptance credit"). Corrected, and
brought up to date through PE3, whose §§1(b′)/3/4 re-derived (1)'s pass-identity
and two-digits-per-branch algebra plus row 7b's drop, (2)'s 2e₀+3 arithmetic and
ρ's strict drop, and (7)'s eight per-digit bounds from scratch: **items (1), (2)
and (7) have each now been RE-DERIVED BY TWO HOSTILE PASSES (PE2 and PE3) and
carry NO ACCEPTANCE CREDIT** — neither pass was clean, and re-derivation inside
a gap-returning pass is not acceptance. The r2 edits (G1–G5) have been read
ONCE (PE3), which confirmed G1/G2/G3/G5 and found G4's substance sound but its
displayed witness non-realizable (r3's F-B). The r3 edits themselves are
UNAUDITED; PE4 is owed. The five r2
repairs, for the record: (C)(ii)'s branching count corrected 2e₀+1 → **2e₀+3**
with only finiteness consumed (G1); PE1's verification scope corrected and the
eight per-digit ω-gain bounds attributed to PE2 and charged as item (7) (G2);
the census-completeness leg made durable as generator assertion **A7**
(Σ children = X, 0 mismatches / 752 nodes, plus shape, digit-wise
dev-linearity, and the 2e₀+3 branching bound) (G3);
"gain(q) = gain(r) + e₁h₀" STRICKEN as a non-identity and re-derived by
applying CONTENT to the q-digit, the equality demoted to a battery observation
(896/896) (G4); "valid EXACTLY on d₀ = 1" weakened to sufficiency, with the
table's own d₀ = 2 vacuous rows A12/B14 named (G5). Wave-18's price sheet
remains settled MODULO this note's own arc, not "in full". **[r3, F-C — second
site of the same overstatement; corrected to PE2's own record.]** The r2
wording: "S3's corner measurement and both machine legs re-ran
**bit-identically** at PE2 (sealed runner 25,409/0, md5
`ccb4351c92573f5f962cae4ae952d8dd` intact and still intact at r2; children
table's data sections byte-identical under the A7 amendment)." Corrected: at
PE2 the sealed runner re-ran to the SAME COUNTED RESULT (25,409 checks, 0
violations in every family, md5 `ccb4351c92573f5f962cae4ae952d8dd` intact and
still intact at r2/r3) with its output "identical line-for-line **modulo the
`elapsed`/per-block timestamp fields only**" — PE2's own qualification, dropped
in the r2 paraphrase; the committed artifact reads `elapsed 4.4s` against
PE2's and PE3's `elapsed 4.3s`, so the runner's output FILE is not bit-identical
across runs. The children table's data sections ARE byte-identical under the A7
amendment (`diff` empty at PE2 and again at PE3).

**STATUS LINE [r3] (supersedes the r2 clause "the r2 repairs … have never been
read by anyone" — PE3 has read them — and carries the arc forward one hop).**
As of repair round r3: **(TAIL-STAB) is PROVED by S4.1 as repaired at r1,
confirmed at PE2 (0 CRITICAL) and confirmed again at PE3 (0 CRITICAL)** — three
hostile readings, and the third re-derived independently, from scratch, all
eight per-digit ω-gain bounds, the 2e₀+3 branching arithmetic, the two
emptiness strata, ρ's strict drop on every child edge, the counter-instance's
two passes and its double-development tie, and the (TAIL-STAB) consumer
interface at every downstream site (finding that READ-EQ's one pass sits
entirely in the deg a = 0 stratum, where the repaired proof shows there are no
q-children at all, so the r0 defect could never have propagated there).
**THE ARC:** PE1 (1 CRITICAL + 3 gaps) → r1 → PE2 (0 CRITICAL + 5 gaps) → r2 →
PE3 (0 CRITICAL + 5 gaps; the arc's FIRST acceptance attempt) → **r3 (this
round, F-A…F-E applied)** → **PE4 = the next acceptance attempt**. Grade:
**attempt 0/2, unchanged** — PE3 was a hostile pass and found no critical, but
5 gaps is not a clean pass, so no acceptance slot has opened; a repair round is
not a pass; and the W-2 cap still binds (GRTW2 itself 0/2), with the honest
decoupling fact intact (the COR 1 / ξ = 1 chain is W-2-free). What r3 changed
is entirely the note's EVIDENCE-DESCRIPTION layer, never the chain: the sealed
runner's ψ₁ assert is now described as the no-op it is and the K₂ one-element
check as the only substantive half of that pair, with the explicit statement
that **no claim in this note consumes the ψ₁ assert** (F-A); the G4 strike's
witness is replaced by one realizable at a legal mid branch, the strike itself
unchanged (F-B); "bit-identically at PE2" is corrected at both sites to PE2's
own timestamp qualification (F-C); charge items (1)–(2) are relabelled to the
accurate "re-derived, no acceptance credit" pattern, now reading "re-derived by
TWO hostile passes (PE2, PE3)" (F-D); and Q6 LOC's zero family count is
supplied in S3 with the disclosure that it is a nested derived counter, not an
independent leg (F-E). Which steps are unaudited after r3: **the r3 edits
themselves**, and nothing else has changed status — items (1), (2), (7) stand
at two independent re-derivations with no acceptance credit, and the r2 edits at
one. Wave-18's price sheet remains settled MODULO this note's own arc, not "in
full". Both machine legs are BYTE-FROZEN at r3 and were re-run clean by PE3
(sealed runner exit 0, 25,409/0, `git diff dafc0b5 HEAD` = 0 bytes, md5
`ccb4351c92573f5f962cae4ae952d8dd`; children generator table regenerates
byte-identically with A7's four legs PASS at 752 nodes / 5,336 children).

<!-- ARCHIVE-END -->

— LIFT-CORNER unit, campaign date 2026-08-08 (wallclock 2026-08-04);
repair round r1 applied 2026-08-08 campaign (wallclock 2026-08-05);
repair round r2 applied 2026-08-08 campaign (wallclock 2026-08-05);
repair round r3 applied 2026-08-08 campaign (wallclock 2026-08-05);
repair round r4 applied 2026-08-08 campaign (wallclock 2026-08-05);
repair round r5 applied 2026-08-08 campaign (wallclock 2026-08-06);
repair round r6 applied 2026-08-08 campaign (wallclock 2026-08-06);
repair round r7 applied 2026-08-08 campaign (wallclock 2026-08-06).

---

## ★ ACCEPTANCE RECORD (orchestrator, 2026-08-06) ★

**THIS NOTE IS ACCEPTED at 2/2** — two consecutive clean hostile passes:
PE8 (report c6097d7, CLEAN 0C/0G) and PE9 (report 9b5175c, CLEAN 0C/0G,
including a fresh-instance leg at p = 7 outside the sealed battery's
roster: 2,178 nonzero digits, 0 violations, the PE1 counter-instance
identity re-multiplied exact). Full arc: PE1 (1C+3G) → r1 → PE2 (0C+5G)
→ r2 → PE3 (0C+5G) → r3 → PE4 (0C+6G) → r4 → PE5 (0C+5G) → r5 → PE6
(0C+3G) → r6 → PE7 (0C+1m) → r7 → PE8 CLEAN → PE9 CLEAN. Nine hostile
passes, seven repair rounds, every substantive component re-derived by
at least two independent fresh readers.

**WHAT IS ACCEPTED**: this note's theorems as fenced — (TAIL-STAB) via
lexicographic (m, deg a) descent; READ-EQ; THE THEOREM (the display with
the letter the lift carries, every orbit member); COR 1 (the ξ = 1
slice); COR 2 (the corner restriction, as rescoped at r1/F3) — at the
note's own conditionality: **the shift-descent consumption of GRTW2
(0/2, arc open) caps the discharge grade; the ξ = 1 core chain is
W-2-free as displayed.** NR-1's discharge is hereby at ACCEPTED grade
modulo the W-2 cap. The S5 rider-rewrite display (what [ILN]'s NR-1
entry becomes) is NOW LICENSED for execution at the next ledger fold.
Machine record: sealed runner 25,409/0 (md5 ccb4351c… byte-frozen
dafc0b5 → HEAD); children generator + A7 752/5,336/0.

---

## ANNEX (dated appends; the frozen body is not edited)

> **[ANNEX 2026-08-08, orchestrator, fold-carry closure FC-1 — the W-2
cap.]** The acceptance record above reads "the shift-descent consumption
of GRTW2 (0/2, arc open) caps the discharge grade" and "NR-1's discharge
is hereby at ACCEPTED grade modulo the W-2 cap". The cap's supplier has
since been ACCEPTED at 2/2 — GRTW2 at adc6cf3 (2026-08-07), with
W2-OPEN-2/OPEN-2a accepted AS A BOX (the weld's one fenced open lemma) —
and the supplier's acceptance record names this consumer: "the accepted
LIFTCORNER's shift-descent consumption … now ride[s] an ACCEPTED supplier
at its fenced scope." Wherever this note bills GRTW2 at "0/2 / arc open"
(the record above; the grade box's W-2 cap), read: capped by an ACCEPTED
supplier at its fenced scope — NR-1's discharge stands at ACCEPTED grade
riding accepted suppliers throughout, and the ξ = 1 core chain stays
W-2-free as displayed. Direction: FAVORABLE.

> **[ANNEX 2026-08-08, FC-2 — the rider-rewrite license.]** The record's
clause "The S5 rider-rewrite display (what [ILN]'s NR-1 entry becomes) is
NOW LICENSED for execution at the next ledger fold" is DISCHARGED:
executed at 5054d69 (2026-08-07) as an append-only fold annex on
`ITERLAWN_PROOF_2026-08-08.md` (the S5 display transcribed verbatim; all
8 occurrence sites enumerated and governed; grade = ACCEPTED mod the W-2
cap), then supplemented at adc6cf3 after GRTW2's acceptance (the cap = an
accepted supplier). Direction: FAVORABLE (license executed; nothing
further owed on this item).

---

### Dated adjudication (2026-08-12 — sol certification C1/E1: the as-built challenge adjudicated at HEAD)

The sol-5.6 as-built read of this note (gpt-5.6-sol high,
runs/cert/C1_liftcorner_output.log, 2026-08-12) returned CHALLENGE
(1 CRITICAL, 2 GAP, 2 MINOR). The E1 certification run (gpt-5.6-sol
high, runs/cert2/E1_liftcorner_output.log) adjudicated all five:
finding 2 RESOLVED-ALREADY (the [r4, F4-6] fence), finding 5 ARTIFACT
(rebutted from the note's own [r3]/[r4] lines), findings 3 and 4 REAL
with repairs (annexes AC-2, AC-3), and finding 1 OBSTRUCTED with the
containment annex AC-1 naming the missing lemma (Φ₁-OPACITY) and its
pre-proof numerical certificate. Everything above this heading is
byte-untouched by this append. The E1 adjudication, transcribed
unaltered:

1. OBSTRUCTED — PROP’s higher-rung conclusion is unsupported

The finding stands. TAIL-STAB and READ-EQ prove the level-2 comparison, but nothing in the note proves that ITERLAWN’s rung-\(\ge2\) construction is insensitive to the non-leading coefficients of \(\Phi_1\). The note expressly admits this in `[r4, F4-4]`:

> “an argument this note does not make, and which neither the two formerly cited tables nor ITERLAWN's own r4 erratum supplies”

Thus PROP, S5’s all-\(n\) rider, and FC-2 outrun the proved chain. The missing lemma cannot be derived from the note’s own lemmas because WELL-DEF-\((n)\), the \(C_k\) construction, and the degree telescope are not defined here.

Verbatim-ready containment and obstruction append:

> **[ANNEX 2026-08-12, certifier AC-1 — PROP’S RUNG-\(\ge2\) CENSUS REMAINS OPEN.]** The all-rung force of three earlier sentences is SUSPENDED: PROP’s “the discharge lifts to every rung”, S5’s “ITER-LAW-\(n\) holds for EVERY lawful monic \(\Phi_1\), every \(n\)”, and FC-2’s execution of that rider rewrite. TAIL-STAB, READ-EQ, the THEOREM, COR 1 and COR 2 remain accepted exactly at their displayed 2-read / harness-\(\Phi_1\)-orbit scope.
>
> The missing statement is:
>
> **\((\Phi_1\)-OPACITY).** Let \(\Phi_1'\) and \(\Phi_1''\) be lawful monic level-1 keys with the same degree, \(w_1\)-value and accepted level-1 base package. For every rung \(n\ge2\), every use of \(\Phi_1\) in ITERLAWN S4.1/WELL-DEF-\((n)\), the \(C_k\)-existence construction and the S4.2 degree telescope factors through monicity, degree, \(w_1\Phi_1\), and the accepted level-1 package; equivalently, replacing \(\Phi_1''\) by \(\Phi_1'\) leaves every rung-\(\ge2\) proof datum and conclusion invariant after the formal identification \((\Phi_1'')^i\leftrightarrow(\Phi_1')^i\).
>
> This lemma is NOT proved by the present note. TAIL-STAB and READ-EQ control level-2 developments and reads; they contain no definitions of WELL-DEF-\((n)\), the higher \(C_k\), or the degree telescope from which \((\Phi_1\)-OPACITY) could be derived. The existing facts that the two keys share monicity, degree, \(w_1\), and the level-1 package do not logically exclude a higher-rung operation from inspecting a non-leading coefficient. Consequently the all-rung repair is **OBSTRUCTED pending a proof of \((\Phi_1\)-OPACITY)**. Until then, PROP and the executed S5/FC-2 rider are conditional on that lemma and carry no accepted conclusion.
>
> **PRE-PROOF NUMERICAL CERTIFICATE.** Use, without sampling, the 56 S3 orbit towers—48 twisted towers and 8 \(\xi=1\) dense controls—each paired with its same-residue standard lift \(\Phi''\), plus the exact PE1 counter-instance and its standard-lift mate. Run every pair through rungs \(n\in\{2,3,4,5\}\). At each of ITERLAWN S7’s 22 dependency sites record the branch decisions, degrees, valuations, residual coefficients, \(C_k\), telescope terms, and final read/cocycle data. Normalize each polynomial datum to formal \(\Phi_1\)-adic coordinates by replacing \(\Phi_1^i\) with a common symbol \(U^i\) and identifying the shared coefficient fields. The required predicate is equality of the complete normalized records for \(\Phi_1'\) and \(\Phi_1''\), together with an access trace showing that no non-leading coefficient of \(\Phi_1\) reaches a branch condition, valuation, residual coefficient, \(C_k\), telescope bound, or final read except through the opaque formal-power node \(\Phi_1^i\). Required verdict: zero normalized mismatches and zero forbidden coefficient accesses on all 57 tower pairs, all four tested rungs, and all 22 sites. This is an instance certificate only; the universal conclusion still requires a source-level proof of \((\Phi_1\)-OPACITY).

2. RESOLVED-ALREADY — the broader “at any level” reading remains fenced

The finding conflates changing \(\Phi_1\) and propagating that fixed choice through canonical higher rungs with independently choosing a noncanonical \(\Phi_{m+1}\) at a deeper level.

The exact cure is already in `[r4, F4-6]`:

> “**What this note delivers, exactly.** The **\(\Phi_1\) corner** of NR-1”

and:

> “Under the ILNRES S1 ‘at any level’ reading a deeper-level remainder survives. The two readings live in different notes of record, and this unit does not choose between them.”

The acceptance record accepts “this note’s theorems **as fenced**.” FC-1 is explicitly a correction only of “the W-2 cap”; it changes the supplier grade from \(0/2\) to accepted and does not erase the `[r4, F4-6]` scope fence. Therefore the noncanonical-\(\Phi_2\) counter-configuration was already excluded from the discharged scope.

This does not cure finding 1: propagation of a changed \(\Phi_1\) through canonical higher rungs still needs \((\Phi_1\)-OPACITY).

3. REAL — CONTENT must be displayed at its integral-key scope

The displayed wording “For monic \(\Phi\)” is literally too broad. The proof uses integrality of every coefficient of \(\Phi\), not merely monicity.

Verbatim-ready repair:

> **[ANNEX 2026-08-12, certifier AC-2 — CONTENT RE-DISPLAYED AT ITS PROVED-AND-CONSUMED SCOPE.]** The S4 CONTENT display
>
> “For monic \(\Phi\), the digits of \(\operatorname{dev}(F,\Phi)\) satisfy \(w_0\)-content \(\ge w_0\)-content\((F)\)”
>
> is SUPERSEDED by:
>
> **CONTENT (integral-key form).** Let \(\Phi\in\mathcal O[x]\) be monic and \(F\in\mathcal O[x]\). Every coefficient of every digit of \(\operatorname{dev}(F,\Phi)\) has valuation at least \(w_0\text{-content}(F)\).
>
> *Proof.* Put \(c=w_0\text{-content}(F)\). During monic long division, assume every coefficient of the current dividend has valuation at least \(c\). Its leading coefficient \(\lambda\) then has \(w_0(\lambda)\ge c\). Because every coefficient of \(\Phi\) lies in \(\mathcal O\), every coefficient of \(\lambda x^i\Phi\) has valuation at least \(c\). Subtracting it preserves that lower bound by the ultrametric inequality. Thus both the quotient coefficients and the remainder coefficients have valuation at least \(c\). Repeating the same division on successive quotients produces the \(\Phi\)-adic development and preserves the bound at every digit. ∎
>
> **Consumer sweep.** S4.1 applies CONTENT only to
> \(a b=r+q\Phi_0\), where \(a,b,\Phi_0\in\mathcal O[x]\) and \(\Phi_0\) is monic. Hence the bounds \(w_0(r),w_0(q)\ge w_0(ab)\), all eight per-digit \(\omega\)-gain bounds, the lexicographic induction, TAIL-STAB, READ-EQ, the THEOREM and both corollaries survive unchanged. No consumer uses CONTENT for a monic polynomial with a nonintegral coefficient. The counterexample \(\Phi=x+p^{-1}\) is excluded precisely because \(\Phi\notin\mathcal O[x]\).

4. REAL — correct the degree comparison in READ-EQ

The literal \(e_0<\deg\Phi'\) fails when \(d_0=1\). The consumed inequality is the degree of the coefficient against the key degree.

Verbatim-ready repair:

> **[ANNEX 2026-08-12, certifier AC-3 — READ-EQ DEGREE CORRECTION.]** In S4.2(a), the clause
>
> “with \(s<e_0<\deg\)”
>
> is SUPERSEDED by:
>
> “with \(s<e_0\); since \(\deg\Phi_0=d_0\) and
> \(\deg\Phi'=\deg\Phi''=e_0d_0\),
> \[
> \deg(\Phi_0^s)=sd_0<e_0d_0=\deg\Phi'=\deg\Phi'',
> \]
> so \(\pi^u\Phi_0^s\) is a single key-slot coefficient and the key power is never opened.”
>
> **Consumer sweep.** This is exactly the inequality consumed by the anchor and \(\delta_1=0\) parts of READ-EQ. It holds also at \(d_0=1\), where \(\deg\Phi'=e_0\) but \(s<e_0\). The separate \(\delta_1=1\) one-overflow argument is untouched. Therefore READ-EQ, the THEOREM, COR 1 and COR 2 survive unchanged.

5. ARTIFACT — “bit-exactly modulo timing fields” does not claim raw-file identity

The quoted PE9 sentence is not part of the note at HEAD. Moreover, its parenthetical explicitly states the equivalence relation: equality after removing disclosed wall-clock fields.

That is consistent with the note’s corrections:

- `[r3, F-C]`: “identical line-for-line **modulo the `elapsed`/per-block timestamp fields only**”
- `[r4, F4-3]`: the runner output is “**identical modulo timing fields, not bit-identical**”
- `[r4]` machine record: the raw output differs at wall-clock lines, while timing normalization gives an empty diff.

The acceptance record itself calls the runner bytes “byte-frozen” and separately calls the children table reproducible; it never asserts that the raw timed runner output is byte-identical. No repair is needed.

*(The adjudication above was produced by the E1 certification run
(gpt-5.6-sol high, runs/cert2/E1_liftcorner_output.log, 2026-08-12);
orchestrator verification before transcription — AC-2's division
proof re-checked (integral Φ keeps every λx^iΦ coefficient at
valuation ≥ c; ultrametric subtraction preserves the bound; the
C1 counterexample Φ = x + p^{−1} is excluded by Φ ∉ O[x], and every
consumer site is in O[x]); AC-3's inequality re-checked
(s·d₀ < e₀·d₀ = deg Φ′, valid at d₀ = 1 where the sealed e₀ < deg
failed); the RESOLVED-ALREADY and ARTIFACT rebuttals checked against
the note's own [r4, F4-6] fence and [r3, F-C]/[r4, F4-3] lines at
HEAD; AC-1's containment matches the note's own [r4, F4-4] admission,
and the (Φ₁-OPACITY) statement + 57-pair certificate spec are
recorded as the proof unit. Transcribed unaltered per the standing
division of labor. Ledger: row 19 → AC-2/AC-3 folded; OPEN pending
(Φ₁-OPACITY) + discharge.)*

---

### Dated source adjudication (2026-08-12 — sol certification P3: (Φ₁-OPACITY) narrowed to the (RM-1) interface)

The P3 certification run (gpt-5.6-sol high,
runs/cert4/P3_opacity_output.log) adjudicated (Φ₁-OPACITY) directly
against ITERLAWN's r6 census of record (194 mapped hits): the
constructor/telescope subgraph is PROVED opaque (the Θ-transport
sublemma below), and the obstruction survives at exactly one site —
ITERLAWN S4.6's (RM-1) reduction, which divides by Φ₁ and reads its
non-leading coefficients. The residual obligation is the (RM-1)
INTERFACE LEMMA named inside the annex (the four consumed interface
clauses survive the key swap; full R,Q proof-data equality is the
wrong statement). Transcribed unaltered:

> **[ANNEX 2026-08-12, certifier AC-4 — \((\Phi _1\)-OPACITY SOURCE ADJUDICATION: CONSTRUCTOR/Telescope SUBGRAPH PROVED; ALL-RUNG LEMMA OBSTRUCTED AT \((RM\text{-}1)\).]**
>
> This adjudication uses ITERLAWN’s machine census of record, not the superseded 22-row or 23-row hand tables. The r6 universe is **194 mapped hits on 147 lines**, partitioned as follows:
>
> 1. **88** table-row occurrences, duplicates and dated cure-brackets;
> 2. **21** occurrences in the seven substantive site-families \(F1\)–\(F7\);
> 3. **53** verification-apparatus occurrences;
> 4. **8** quotations of external records;
> 5. **18** non-genre occurrences;
> 6. **6** positive proof displays.
>
> The apparatus, quotation, archive and duplicate classes perform no polynomial operation and therefore cannot inspect a coefficient of \(\Phi _1\). The operative occurrences in the remaining classes reduce to five source-operation classes:
>
> * shared numerical and field data: \(e_j,h_j,g_j,\gamma_j,w_j\Phi_j,\psi_j,K_j,z_j,\epsilon_j\);
> * the recursive realizers \(\operatorname{realize}_m\);
> * the \(C_k\)-existence and canonical-key construction;
> * TRUNC, WELL-DEF and the S4.2 degree telescope;
> * the S4.6 reduction engines \((RM\text{-}m)\).
>
> The first four classes are \(\Phi _1\)-opaque in the required formal-power sense. The fifth is not shown opaque and, at \(m=1\), genuinely opens \(\Phi _1\).
>
> **Proved sublemma — constructor/telescope opacity.** Let \(\Phi _1'\) and \(\Phi _1''\) be lawful monic level-1 keys having the same residue package, degree, \(w_1\)-value and accepted level-1 data. Fix all remaining tower parameters. In every displayed construction in ITERLAWN S4.1 and S4.2, transport an explicitly displayed \(\Phi _1''\)-normal form by
> \[
> \Theta\!\left(\sum_i A_i(\Phi _1'')^i\right)
>   :=\sum_i\Theta(A_i)(\Phi _1')^i,
> \]
> recursively replacing each constructed higher key by its corresponding primed key. Then:
>
> 1. \(\Theta(\operatorname{realize}_m''(\tau,\beta))
>    =\operatorname{realize}_m'(\tau,\beta)\);
> 2. \(\Theta(C_k'')=C_k'\) for every canonical-lift coefficient;
> 3. \(\Theta(\Phi _{m+1}'')=\Phi _{m+1}'\);
> 4. all degree, weight and explicitly constructed single-digit read data in REALIZE-\((m)\), WELL-DEF-\((n)\), TRUNC and L6-\((n)\) agree;
> 5. the S4.2 degree telescope is identical on the two sides.
>
> Here \(\Theta\) is asserted only on the normal forms supplied by the displayed constructions. It is not asserted to commute with arbitrary division or re-development in \(\mathcal O[x]\).
>
> *Proof.* Proceed by induction on \(m\).
>
> For \(m=1\), the displayed formula
> \[
> \operatorname{realize}_1(\tau,\beta)
>  =\sum_i
>    \operatorname{realize}_0\!\left(
>       \epsilon_0(\gamma^{(i)})^{-1}\tau_i,\gamma^{(i)}
>    \right)\Phi_0^{k_i}
> \]
> contains no \(\Phi _1\). Its coordinates \(\tau_i\), slots \(k_i\), weights
> \(\gamma^{(i)}\), field operations and \(\epsilon\)-factors are shared.
> Hence the two realizers are literally equal at this level.
>
> Assume the assertion below level \(m\). ITERLAWN defines
> \[
> \operatorname{realize}_m(\tau,\beta)
>   =\sum_i
>      \operatorname{realize}_{m-1}
>        \!\left(\epsilon_{m-1}(\gamma^{(i)})^{-1}\tau_i,
>        \gamma^{(i)}\right)\Phi_{m-1}^{k_i}.
> \]
> The power-basis coordinates \(\tau_i\), the integers \(k_i\) and
> \(\gamma^{(i)}\), and the \(\epsilon_{m-1}\)-factors depend only on the
> shared field/read package. By induction the coefficients correspond, and
> the final occurrence of \(\Phi_{m-1}\) is an opaque formal power.
> Therefore the two displayed realizers correspond under \(\Theta\).
>
> REALIZE’s clauses (R1)–(R3) do not perform division by a changed key.
> Clause (R1) uses only
> \[
> k_i\le e_{m-1}g_{m-1}-1,\qquad
> \deg\operatorname{realize}_{m-1}<\deg\Phi_{m-1},
> \]
> and
> \[
> \deg\Phi_m=e_{m-1}g_{m-1}\deg\Phi_{m-1}.
> \]
> Clauses (R2) and (R3) use the already displayed sum as its
> \(\Phi_{m-1}\)-development: the coefficient-degree bound makes every
> summand a single legal digit, and distinct \(i\) give distinct slots.
> Thus no coefficient of \(\Phi_{m-1}\), and hence no non-leading
> coefficient of \(\Phi _1\), is opened.
>
> For \(k<g_m\),
> \[
> C_k=\operatorname{realize}_m\!\left(
>   \epsilon_m((g_m-k)\gamma_{m+1})^{-1}\psi_{m,k},
>   (g_m-k)\gamma_{m+1}\right).
> \]
> Its field input, weight and \(\epsilon_m\)-factor are shared, so the
> realizer induction gives \(\Theta(C_k'')=C_k'\). Consequently
> \[
> \Phi_{m+1}
>   =\sum_{k\le g_m}C_k\Phi_m^{e_mk},\qquad C_{g_m}=1,
> \]
> corresponds term by term. Monicity comes from the top term
> \(\Phi_m^{e_mg_m}\); every lower term has smaller degree by (R1).
> This proves equal degree and the WELL-DEF existence claims using only
> monicity, degree and the shared read package.
>
> TRUNC merely discards the top level. On the two towers “identical lifts”
> must be read as “corresponding lifts under \(\Theta\)”; its split,
> window and field data are literally shared.
>
> Finally, S4.2 uses only
> \[
> \deg a=\sum_{j<n}s_{j+1}\deg\Phi_j
> \le\sum_{j<n}(\deg\Phi_{j+1}-\deg\Phi_j)
> =\deg\Phi_n-d_0<\deg\Phi_n.
> \]
> The degrees and \(s\)-data agree, so this is the same telescope on both
> towers. It establishes that \(a\) is a single \(\Phi_n\)-digit without
> opening \(\Phi_n\). Its weight and read then come from the corresponding
> induction hypothesis. This proves constructor/telescope opacity. ∎
>
> **Exact obstruction to the stated all-rung lemma.** ITERLAWN S4.6 contains
> the load-bearing display
> \[
> f\,\widehat C_m=R+Q\Phi_m,\qquad
> \deg R,\deg Q<\deg\Phi_m,
> \]
> with weight bounds and a prescribed read of \(R\). At \(m=1\) this is
> \[
> \boxed{\,f\,\widehat C_1=R+Q\Phi_1\,}.
> \]
> Its displayed proof status is:
>
> > “\(m=1\): PROVED — [IL3] DIGIT-SPLIT + DEV-1 … each coefficient product
> > splits by DIGIT-SPLIT and reduces by DEV-1.”
>
> This reduction genuinely inspects the non-leading coefficients of
> \(\Phi _1\). In ordinary long division, cancelling a leading term
> \(\lambda x^t\) subtracts \(\lambda x^{t-d}\Phi _1\); for every \(r<d\)
> it therefore reads \([x^r]\Phi _1\) and changes the developing remainder
> by \(-\lambda[x^r]\Phi _1x^{t-d+r}\). In the corner’s \(\Phi _0\)-adic
> notation the same access is the substitution
> \[
> \Phi_0^{e_0}
>   =\Phi_1-b_0-\sum_{k\ge1}b_k\Phi_0^k,
> \]
> which explicitly reads the \(b_0\)-tail and every mid \(b_k\).
>
> Algebraically, if
> \(\Delta=\Phi _1'-\Phi _1''\) and
> \(F=R''+Q''\Phi _1''\), then
> \[
> F=(R''-Q''\Delta)+Q''\Phi _1'.
> \]
> Thus the new remainder already contains the non-leading coefficients of
> \(\Delta\); if its degree is too large, further reductions read them
> again. Same residue and same \(w_1\)-value can make these new terms
> strictly above a relevant read line, but do not make them zero and do not
> make the complete \(R,Q\) data invariant. Formal replacement
> \((\Phi _1'')^i\leftrightarrow(\Phi _1')^i\) does not remove this
> difference because \(R\) is a coefficient—the \(U^0\) digit—rather than
> an opaque key power.
>
> This is not bypassed by ITERLAWN’s verified sentence “rung \(\ge3\) steps
> never consume RM-1.” The all-rung induction must first obtain
> ITER-PKG-2, the 3-read link. ITERLAWN takes that link from [IL3], and its
> displayed \(m=1\) engine proof is exactly DIGIT-SPLIT + DEV-1 above.
> Later transitions call \(RM-m\) with \(m\ge2\), but they cannot climb from
> an arbitrary \(\Phi _1\) without the rung-2 package.
>
> LIFTCORNER’s TAIL-STAB makes an \(RM\)-interface transport plausible:
> strict-excess terms may be invisible to the particular consumed weight
> and read clauses. No displayed argument, however, proves that statement
> for every \(RM\)-1 input \(f\), and TAIL-STAB does not make the complete
> quotient/remainder records equal. The missing repair is therefore a
> weaker and accurately scoped lemma:
>
> **\((RM\text{-}1\text{-TRANSPORT})\).** Under replacement by a lawful
> same-residue \(\Phi _1\), the four *consumed interface clauses* of
> \(RM\)-1—degree bounds, the two weight bounds and the prescribed read of
> \(R\)—survive for every input class used in constructing ITER-PKG-2.
>
> Proving this interface lemma, followed by the S4.4–S4.6 rung-2 package
> construction, could discharge the all-rung rider. Equality of complete
> \(R,Q\) proof data should not be required and is generally the wrong
> statement.
>
> **Consumer sweep.**
>
> * **LIFTCORNER PROP:** remains SUSPENDED. Constructor/telescope opacity
>   repairs the S4.1 \(\to\) L6 edge but does not supply arbitrary-\(\Phi _1\)
>   ITER-PKG-2 across \(RM\)-1.
> * **LIFTCORNER S5:** its every-\(n\) rider remains conditional on the
>   missing \(RM\)-1 transport/rung-2 package. TAIL-STAB, READ-EQ, the
>   THEOREM, COR 1 and COR 2 retain their accepted 2-read scopes.
> * **FC-2:** its execution of the all-rung rider remains SUSPENDED and must
>   be read conditionally. The fold’s standard-lift ITERLAWN theorem and
>   all unrelated accepted conclusions are unchanged.
> * **ITERLAWN:** S4.1, WELL-DEF-\((n)\), canonical \(C_k\)-existence,
>   TRUNC and L6-\((n)\) are certified \(\Phi _1\)-opaque in the formal
>   constructor sense proved above. Its existing standard-lift theorem,
>   integer layer, EXP-KIT and conditional \(RM\)-ledger are unaffected.
>
> Accordingly, AC-1 is narrowed but not discharged: its alleged opacity
> problem is absent from the constructor/telescope subgraph and survives
> exactly at the rung-2 \(RM\)-1 reduction interface.

*(Orchestrator verification: the census partition sums to 194
(88+21+53+8+18+6); the Θ-transport's five clauses ride the same
block-unitriangular mechanisms verified at P1; the (RM-1) division
genuinely opens Φ₁ (the m = 1 display f·Ĉ₁ = R + QΦ₁ is proved by
DIGIT-SPLIT + DEV-1 reduction mod Φ₁ — coefficient-reading is real).
AC-1 is NARROWED, not discharged. Ledger: row 19 → open on the
(RM-1) interface lemma only (P4, next queue).)*
