# GENIND ANNEX — scoped hostile pass 2 (2026-08-10, post-r1)

## VERDICT

**CLEAN — 0 CRITICAL, 0 GAP, 3 MINOR.** Under the standing charge bar
(nothing GAP-or-worse = CLEAN) the annex stack PASSES this round; the
annex-stack clean counter moves 0/2 → 1/2. The pass-1 GAP-1 repair is
adjudicated **PROVE-FIRST LANDED AND SOUND**: ANNEX-LEMMA GENIND-C2
re-derives from the body's own displays (S7.2's node C(4h+1, 2h+1),
S7.3's uniform boundary 2N−2, S5.1's criterion arithmetic, S5.3's
tables, S7.1's (CS-1) as stated), its conditionality claim ((CS-1)
only, inside the box GENIND.B already assumes) is exact, and the
pass-1 failure scenario — an n = 4 CS drain at window-deficit slope
< 1 — is now excluded three ways at n = 4: by GENIND-C2's derivation
(slope ≥ 2 live / ≥ 5/2 floor-adjacent), by the committed GENH4.B
drainage THEOREMS themselves (genre E aggregate (q−1)^{r+1}q^{2N−h−2}
= relative slope exactly 2 at every window; genre F main term paired
slope 3 with the even-N CAP(F) band), and by measurement (r1's 7
ratio pairs + this pass's fresh deep-h pair, slopes 2.00 on the
nose). MINOR-1 and MINOR-2 executed as charged. The three new MINORs
(below) are display/record blemishes; none touches a consumed
conclusion. The frozen 2/2 body is untouched (freeze re-verified);
the r1 machine leg reproduces bit-identically in isolation.

## Charge and scope

The GENIND note's annex stack (ANNEX R lines 2552–3095 + the r1
append 3098–3294 at HEAD dfd58316) after pass 1 returned UNREFUTED /
NOT CLEAN (0C/1G/2m, `GENIND_ANNEXR_pass_report.md` @ 4c89666f) and
r1 landed (seal e0adefb4 + verdict dfd58316). Scope: the annex stack
ONLY; the 2/2 body is accepted and re-litigated nowhere. Pass-1's
route (R2–R6 re-derivations, freeze/pin census, N = 40 Q = 7, 27
fresh leg) is NOT re-walked. Surfaces: (1) the GAP-1 repair
(GENIND-C2) re-derived and stressed at the pass-1 failure scenario +
instances the repair did not use; (2) the c := c′+1 arithmetic;
(3) the enumerative rewrites vs the actual artifact/number census;
(4) free hunt across the annex stack; machine legs (pins, isolated
re-run, tautology audit); one fresh out-of-battery route disjoint
from pass 1's. Protocol: quote-and-classify, fix nothing.

## The GAP-1 adjudication (surface 1 — the heavy item)

**Charge species: PROVE-FIRST landed** (a rate lemma, not a
re-scope), so the required stress is the lemma itself.

**C2(i) re-derived (stage window supply).** GENIND-4 (body S7.2)
proves the stage-initial node dv(A₀) ≥ 4h+1 = 2S+1, S = 2h; S7.3
displays the uniform boundary dv = 2N−2 ("uniform statements hold
below dv = 2N−2", the ragged odd-slot extension 2N+h−2 above it).
Slot count 4h+1 .. 2N−2 = 2N−2−4h = E(N−1−H) at E = 2, H = 2h —
the claimed M★ EXACT at the E instance ✓. Genre F: H = v(a₀) = 4k
(S5.3's heights (4k,3k,2k,k)), E = e = 1, K = F_{q²}, M★ = N−1−4k ✓.
Visibility floor H ≤ N−1 ⟺ M★ ≥ 0 ✓ both genres. Stressed at the
VERTEX genre CS5-V1E2 (the (i) formula's hardest reading: the true
displayed window is 2N−2−4h while H = v(a₀) ≥ (5h+1)/2 varies above
the side): E(N−1−H) ≤ 2N−3−5h ≤ 2N−2−4h — the (i) INEQUALITY is
loose-but-true there, and the composition (iii) correctly uses the
side-height window, with a₀'s headroom a DECIDED fiber ✓.

**C2(ii) re-derived (stage drain rate).** μ ≤ 3 stage reads are
CS-free by S5.1's criterion AT the stage (CS needs a side of length
e·μ·degψ ≥ 4 hence ≥ 4 keys; the stage has μ) — so full = simple at
the stage and GENIND.C′ applies through (CS-1)'s count isomorphism
(S7.1: "count-isomorphic to a degree-m′ cluster-system read over K
at an explicit stage window, RAGGED-WINDOW-CORRECTED" — verbatim the
form C2 consumes; the ragged band only ADDS certification above the
uniform window, so the uniform-window bound is conservative for an
upper bound) ✓. μ ≥ 4 recursion: lex well-founded — stage q-degree
μ·d·degψ < m·d strictly when e ≥ 2 (μ·degψ ≤ m/e), and at the e = 1
equality case M★ = N−1−H < N with same degree, i.e. exactly the
α-leg descent shape; first possible at m ≥ e·μ·degψ ≥ 8 ✓.

**C2(iii) re-derived (composition; the slope claims).** In q-units
|K|^{−(M★−c★)} ≤ q^{−(e·d·degψ)(N−1−H)+O(1)} with e·degψ ≥ 2 =
S5.1's CS-defining inequality ✓. Composed instances re-computed by
hand and all three displayed lines are exact: CS4-E
q^{1−5h}·q^{−(2N−2−4h)+c★} = q^{−(2N+h)+O(1)} ✓; CS4-F
q^{−10k}·q^{−2(N−1−4k)+2c★} = q^{−(2N+2k)+O(1)} ✓; CS5-V1E2
(entry constant-order in N) × the (2,2)-E stage = q^{−2N+O(h)} ✓.
Floor-adjacent entry-alone slopes: E at 2h ≈ N−2 gives q^{−5(N−2)/2}
(slope 5/2) ✓, F at 4k ≈ N−2 the same 5/2 ✓. Height-sum
convergence: per height unit of the CS side's top, the side's pins
contribute (L+1)/2 Q-digits (straight side; vertex genres pin more)
against the stage-window loss e·degψ, and L ≥ e·μ·degψ ≥ 2·e·degψ
(μ ≥ 2) gives (L+1)/2 ≥ e·degψ + 1/2 — a UNIVERSAL margin 1/2, so
the sum is dominated at the deep end (slope e·d·degψ ≥ 2) with the
floor-adjacent end at slope ≥ 5/2: "the crossover is the visibility
floor" ✓ and "an n = 4 CS drain at window-deficit slope < 1 is
excluded twice over" ✓. (The comparison (L+1)/2 > e·degψ is the one
undisplayed step — MINOR-C below; machine-checked over the whole
inventory to m = 12 in the fresh leg PF3.) Mixed genres: composition
by GENIND-6(d) (a PROVED lemma, S4.3) + union bound = C1(ii)'s
mechanism, bounds propagating per R6.2 — no (CS-EXACT) ✓.

**Conditionality audit.** (CS-1) only: entry pricing = W-12.A
(proved), GENIND-6 (proved), R6.2's separation (bound direction) —
(CS-2)/(CS-3)/(CS-EXACT) genuinely unconsumed for a BOUND ✓. n = 4
de facto: body L1079 displays "CS-1 = GENIND-4 + GENH4-1F + …" per
GENH4.D at r3 4b0d9468 (commit verified) ✓, so u_{4,d}'s full
(A2-RATE) — the member C1(iii) consumes at n = 5 — rides pinned
theorems ✓. At n ≥ 5 the CS-drain leg sits inside [GENIND-H(n)],
which THEOREM GENIND.B's reduction already assumes: the repaired
closure sentence adds NO new hypothesis ✓. The closure rider's
"split" phrasing (simple part / CS-drain part) compresses what is
operatively a JOINT lexicographic induction (C2(ii): "CS legs enter
GENIND.C′'s (degree, window) induction exactly as α-legs do" — deep
CS openings are carried by the α/β legs consuming the full member
recursively); the mechanism is displayed, the compression read as
intended.

**The failure scenario, stressed.** At the r1 rows the measured
slopes are 2.00 exactly (E, 5 pairs) and 1.00/3.00 parity-paired
2.00 (F); the flagged P3 line (F 7→8 single-step 1.00 > cap
q^{−1.5}) is adjudicated an INSTRUMENT CAP LITERAL, and this pass
confirms the note's hand closure from the committed law: GENH4.B's
genre-F per-(ψ,H₂) law q^{2⌊N/2⌋+2k−1} + 1_{2|N}(q−1)q^{N+2k−1}
(GENH4 note, verified in place) steps q²·q⁰ on alternating parities
(⌊N/2⌋) and the CAP(F) band term is q^{−3N+12k+3} relative to the
entry stratum at even N — per-stratum paired slope 3.00 ✓; the
run's measured aggregate paired slope is 2.00 (2^{−15} → 2^{−19}
over 7→9) ✓; a single-step slope 1.00 with a 3.00 partner is
consistent with (and here caused by) the parity band, contradicts no
C2 claim (an envelope, not a per-step monotone law), and no BOUND
check (P1/P2) fails at any row ✓. Decisive: GENH4.B's genre-E
aggregate (q−1)^{r+1}q^{2N−h−2} predicts every one of the r1's 8
fresh E-row UND tallies EXACTLY (32/128/512/2048 at q=2 h=1
N=4..7; 2048/8192 at h=3; 486/4374 at q=3), i.e. relative slope
exactly 2 at every window as a THEOREM — the n = 4 slope-<1
scenario is dead at theorem grade, not merely at sampled windows.

**GAP-1 verdict: CURED at prove-first grade.** The repair is honest
about what changed (the six [ar1] tags), transcribes no verifier
sentence (the C2 derivation runs through GENIND-4/S7.3/S5.1/S5.3
material pass-1 never displayed), and the annex's five [ar1] riders
+ close enumeration match the actual diff exactly (verified hunk by
hunk against fe0ed6c0).

## Findings (all MINOR; none GAP-or-worse)

**MINOR-A (r1.1 machine-leg seal paragraph — P1 scored-row count).**
Quoted: "P1 (per-stratum window bound … at **10 scored fresh
rows**)" (note L3213). The sealed script scores every roster row
with M★ ≥ 2 = 8 E rows + 3 F rows = **11**, and the commit-2 machine
record says "all 11 scored fresh rows". The operative preregistration
(the sealed script's docstring, byte-identical seal → verdict →
HEAD, md5 45a8a322) carries no count, so no prediction moved; the
seal PARAGRAPH miscounts by one and the record paragraph does not
flag it. Failure scenario: a reader reconciling seal vs record
suspects a post-seal roster change where none occurred (the git
diff refutes it). Repair species: one-word erratum at the seal
paragraph.

**MINOR-B (R1.4's [ar1] display census — "the five committed
displays this section consults").** The enumeration (W-11's R(M),
HEX3.A's law, HEX3.B's rate, GT-BDRAIN recursions, GENIND-BOX-4's
pricing) is REAL (each verified present) and the non-rewriting claim
holds for all five — but the census presupposition is short: R1
also consults, as committed displays, M6's locus law (q−1)²q^{6N−17}
+ PSTEEP3/PSTEEP4's laws (R1.2 leg E) and the six committed hull
extractions (leg D). None of those is rewritten either, so nothing
substantive fails; but "the five … this section consults" is a false
census of the exact record species MINOR-2's cure was adopted
against. Failure scenario: a future supplier-movement sweep trusts
the census and skips re-checking M6's law against an R1 consumption.
Repair species: "five" → the displays whose SUPPLIER STATUS this
section touches, or extend the enumeration.

**MINOR-C (GENIND-C2(iii) — the height-sum convergence step's
displayed support).** Quoted: "The entry mass ρ decays geometrically
in H (the entry laws are order-1 W-12.A-priced shapes …), so the
height sum converges". Geometric decay of ρ alone does NOT give
convergence of Σ_H ρ(H)·|K|^{−(M★(H)−c★)}: the stage factor GROWS
in H at rate e·d·degψ per height unit, so the step needs
rate(ρ) > e·degψ (in Q-digits per unit side height). That
comparison is TRUE with universal margin 1/2 — side pins ≥ (L+1)/2
per height unit and L ≥ e·μ·degψ ≥ 2e·degψ by S5.1's DISPLAYED
side-length arithmetic — and the lemma's own conclusion line
displays the two boundary rates correctly (≥ 2 live, ≥ 5/2
floor-adjacent, crossover at the floor), but the comparison itself
is displayed only through the n = 4/5 instances. Classified MINOR,
not GAP: unlike pass-1's GAP-1 (a consumed rate with NO derivation
anywhere), the missing step is a two-line consequence of material
the lemma already cites (S5.1's necessity arithmetic), re-derived
here and machine-checked over every inventory shape with
e·μ·degψ ≤ 12 (fresh leg PF3: min(entry rate, stage rate) ≥ 2 and
margin ≥ 1/2 at all shapes). Failure scenario (display-level only):
a reader grants "geometric ⇒ convergent" and misses that the claim
needs the rate comparison; no inventory genre realizes a failure.
Repair species: one sentence displaying (L+1)/2 ≥ e·degψ + 1/2.

## Clean charges (each verified this pass)

* **c := c′+1 (surface 2)**: β-leg Q^{−(N−c′−1)} = Q^{−(N−c)} at
  c = c′+1 EXACT ✓; head absorbed iff c ≥ 1, and c ≥ c₀+1 ≥ 2 from
  C1(iii)'s c₀ ≥ 1 ✓; no circularity (c′ = max(children's c, c₀) is
  degree-induction data; the α-leg re-enters at the same degree with
  the same c, the window induction's own constant) ✓; the K-absorb
  polynomial inequality unchanged from pass-1's clean walk ✓.
* **Close enumeration (surface 3)**: the four pins each verified at
  HEAD (e7ca150b / 42fd603e / d938ad82 / eefcf658) ✓; the five annex
  commits verified by footprint — a1525ea2 (+197 note-only),
  31c6723d (+118), 98ac7bb0 (+125), fe0ed6c0 (+66), f5271e43 (supp
  pair only) — "touch no file beyond this note and that pair" TRUE ✓.
* **r1 header's edit census**: pre-r1 (fe0ed6c0) → HEAD diff on the
  annex slice = exactly the six [ar1] hunks (5 named + the R1.4 CS
  rider) + one trailing blank line ✓ "every other annex line
  unchanged" ✓.
* **r1 arithmetic spot-checks**: 144 = 4+11+9+7+112+1 ✓; P3 = 7
  pairs ✓ from the roster; 12 rows = 8E+4F ✓; UND_rel ladders
  recomputed by hand from the raw tallies (2^{−7}..2^{−13} etc.) ✓;
  T-SLOPE arithmetic 2^{18} = 262,144 > 2^{16} = 65,536 ✓; T-WIN
  65,536·10·2^{−9} = 1,280 < 32,768 ✓.
* **Repair rule**: C2/c-choice/enumerations re-derived from body
  lemmas; no pass-1 verifier sentence transcribed (the [ar1] defect
  descriptions quote the FINDING, which is the disclosure duty, not
  the repair) ✓.
* **Body freeze**: head -c 158427 = head -n 2548 = eefcf658 at HEAD ✓.
* **Annex↔body**: C2 contradicts no body display (its E/F windows
  and laws re-derived FROM the body's own S7.2/S7.3/S5.3; GENIND.C's
  "can NOT be absorbed into (A2) by bounds" sentence is about entry
  mass, C2 drains INSIDE the stage — consistent) ✓.

## Machine legs

* **Pins at HEAD**: genind_annexr1_checks.py 45a8a322 (byte-identical
  at e0adefb4, dfd58316, HEAD — sealed UNRUN then untouched ✓);
  output c4ea3dec / results c1868892 (landed at dfd58316 only ✓);
  consumed pins genh4_checks.py ee8024b7, genh4_checks_results.json
  cbcff562, genind_checks.py e7ca150b — all verified ✓.
* **Tautology audit**: UND tallies come from the pinned GENH4 walker
  ENUMERATING states (read-only import, its own live law checks
  snapshotted before/after and required silent — they were); the
  bound side is formulaic — decorrelated, not circular ✓. Teeth are
  armed for real (a slope-1/2 fake violates a bound every real row
  satisfies; a mis-derived window is refuted by committed data) ✓.
  Gate strict (GREEN requires 0 violations AND both teeth) ✓; the
  run's RED/exit 1 kept and disclosed per the run-1-RED precedent ✓.
* **Isolated re-run** (fresh /tmp copy of the 4 pinned files +
  transitive walker deps via PYTHONPATH, openmath venv): exit 1,
  stdout identical to the committed output up to per-row timing
  strings; results JSON identical up to elapsed_s ✓ (178.0s vs
  176.1s).

## Fresh route (out-of-battery; disjoint from pass 1 and r1)

`genind_annexr_pass2_fresh.py` (verifier-authored; checks PF1–PF5 +
teeth TF-PAIR/TF-LAW preregistered in the docstring before the run;
single run) → `genind_annexr_pass2_fresh_output.txt`:

* **PF1 GREEN** — walker rows never enumerated by any committed leg:
  E q=2 h=5 N=12,13 (first fresh h=5 rows; the deep-h SLOPE PAIR)
  and E q=5 N=4 h=1 (first q=5 row anywhere on this claim). P1
  window bound holds at all three; the pinned walker's own law
  checks stayed silent; committed-law ties EXACT as preregistered:
  UND(2,12,5) = 131,072 = 2^{17}, UND(2,13,5) = 524,288 = 2^{19},
  UND(5,4,1) = 12,500 = 4·5^5 — three more theorem-grade contacts
  for (q−1)q^{2N−h−2}. Pair slope N 12→13 at h=5: ratio 0.25 =
  slope 2.00 — the derived mechanism measured on the nose at a
  stratum the repair never used.
* **PF2 GREEN** — the union bound at r = 6 (two past every committed
  check): ∂G/∂u_i = Π_{j≠i}(T_j−u_j) exact and UB − G
  nonneg-coefficient in (u_i, T_i−u_i), 57 monomials.
* **PF3 GREEN** — MINOR-C's missing comparison machine-checked over
  the WHOLE CS inventory with side length L = e·μ·degψ ≤ 12 (28
  shapes, 56 checks): entry rate (L+1)/2 ≥ e·degψ + 1/2 and
  min(rates) ≥ 2 at every shape — the slope-<1 scenario excluded at
  every inventory shape reachable below degree 13, not just n = 4.
* **PF4 GREEN** — CS5-V4E2 (the displayed C2 instance the repair did
  NOT machine-use): composed drain grid with the S5.3 law
  (q−1)²q^{1−5v₄−5h}, vertex condition h ≥ 2v₄+1, species window
  2(N−1−v₄−2h): Σ ≤ N·q^{−(N−1)} at q ∈ {2,3,7}, N ≤ 40, 111/0.
* **PF5 GREEN** — the Q non-prime-power algebra corner (admissible:
  polynomial identities in Q): exact-integer closed-form and species
  checks at Q = 6 and Q = 10, N ≤ 25 — disjoint from pass 1's
  Q = 7, 27 leg.
* **Both teeth FIRED**: TF-PAIR (a slope-1 pair ratio at the new
  deep row breaches the q^{−1.5} pair cap — the pass-1 scenario made
  flesh at a row no committed leg used); TF-LAW (a corrupted
  aggregate exponent 2N−h−1 mismatches the measured 131,072).
* **Run total: 280 checks / 0 violations / 2 teeth fired, GREEN,
  exit 0, 329.3s** (single run; no check edited after any output was
  seen; the one row-label cosmetic in the say-format is disclosed as
  an output literal, arithmetic unaffected).

## Grade line

**CLEAN: 0 CRITICAL + 0 GAP + 3 MINOR — the annex stack takes its
first clean; the counter moves to 1/2.** The pass-1 GAP is cured at
prove-first grade with the conditionality exactly as the theorem
already carries; the three MINORs (a seal-paragraph miscount, a
short display census, one undisplayed two-line comparison) are
repair-queue items for the next dated append, none blocking. Per the
standing bar the stack needs one more clean scoped pass (behind the
chain notes) for 2/2.
