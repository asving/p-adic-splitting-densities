# HEX3 passPE3 report — hostile verification of HEX3_PROOF_2026-08-08.md (post-r2)

**Pass:** PE3 (third hostile pass; arc PE1 0C+2G+2m @ d177fd8 → r1 @ 2580f12 →
PE2 0C+1G+1m @ f60348b → r2 @ a707430). **Verifier:** fresh-context Fable,
2026-08-08. **Target:** HEX3_PROOF_2026-08-08.md at HEAD after r2 (a707430);
runner + artifacts byte-frozen at seal e3f3459. Both prior reports and both
repair diffs read in full. **Charges:** (1) the [r2] brackets audited with the
same hostility that caught the [r1] brackets twice — the 12-set census recounted
from primary sources, the S8.2 k = 1 factor re-derived; (2) the S2 β1 route
(the remaining under-derived route) re-derived IN FULL; (3) adversarial hunt for
a sixth depth-0 class; (4) the W12TIE family — what ties, currency post-W12-r2;
(5) supplier/consumer currency at read time (HMENU3 since ACCEPTED at 050425d,
W-11 accepted, W-12 at r2). Machine leg: pins, byte-identity, full re-run,
count reconciliation, smoke reproduction. Fresh route (differs from PE1's
enumerator and from PE2's poly-identities + W-11 block reader + TRP enumerator):
a GF/transfer-operator leg with an OWN exact polynomial engine (no sympy, no
runner imports) producing a NEW derived object (an order-9 constant-coefficient
linear recurrence for u), PLUS enumeration in NINE never-instantiated DVR types
(ramified mixed-characteristic Eisenstein rings, unramified mixed-char
prime-power Witt-type rings, first-ever q = 25/49), PLUS a letter-resolution
transport probe (finer granularity than the battery or either prior pass).

**Provenance disclosure.** An earlier incarnation of this same PE3 task was
interrupted mid-write, leaving an untracked draft report and three /tmp leg
scripts. This session treated all of it as unverified: the three scripts were
audited line-by-line (ring arithmetic, hull walk, root multiplicities, shift3,
classifier, closed-form transcriptions) and RE-EXECUTED fresh; the full battery
and smoke were re-run fresh; every hand recount below was redone from the
primary artifacts. All outputs matched the interrupted logs. Three defects
found in the DRAFT (never committed, note untouched) are corrected in this
report: its full-run elapsed time was the committed §S10 value rather than a
fresh figure (this pass's own run: 331.5 s); its k ≥ 2 floor-mass exponent
read 2N−2k−4 where the true whole-space leading exponent is 2N−2k−2 (the
comparison < 2N−4 for k ≥ 2 is unaffected); and it overstated the (8,3)
evidence as "re-measured by my own F₈[[t]] path" when the own-code leg carries
no F₈ tables — the honest (8,3) evidence is stated under charge 1a.

**VERDICT: CLEAN — 0 CRITICAL + 0 JUSTIFICATION GAPS + 0 MINOR** (two remarks,
below, neither rising to a finding; both are about wording that is accurate but
could be sharpened, no change required). The [r2] census is finally right —
TWELVE, recounted here from the frozen primary sources with every element and
every value independently confirmed; the [r2] k = 1 factor is exactly the law's
own k = 1 summand, proved by exponent algebra and symbolically; the β1 route
survives full re-derivation down to letter-resolution machine fibers; no sixth
depth-0 class exists (hand case-grid + machine hunt over 20 full rows in 14
distinct rings); the W12TIE is current, with the two post-verdict W12 edit
hunks near consumed material individually cleared; no supplier or consumer
grade is misstated. Machine leg bit-reconciled GREEN. The fresh route confirms
the law in territory NO battery in the corpus has ever touched, including
totally ramified mixed-characteristic O — where the theorem's stated scope
("O a complete DVR with residue field F_q") had zero prior machine evidence.
**First clean pass of the arc: counter 1/2. PE4 = the accepting attempt.**

---

## Charge 1 — the [r2] brackets audited (the twice-burned lineage)

### 1a. The census: TWELVE is right, recounted from the frozen primary sources

Every ingredient of the r2 bracket's basis was re-extracted here from the
primary artifacts, not from any prior report (the extraction-inheritance trap
is exactly what [r1] fell into):

* **Roster = 29 distinct (q,N) pairs.** From the frozen runner's ROWS_ZP/
  ROWS_FQT: 21 ℤ_p rows {(2,3..9),(3,2..6),(5,2..4),(7,2..3),(11,2..3),
  (13,2..3)}, 25 𝔽_q[[t]] rows {(2,3..8),(3,2..5),(4,2..5),(5,2..4),(7,2..3),
  (8,2..3),(9,2..3),(11,2..3)}; shared pairs recounted by hand: 6 (q=2) + 4
  (q=3) + 3 (q=5) + 2 + 2 = **17** ✓; 21 + 25 − 17 = **29** ✓.
* **w12 committed = 14 pairs.** Extracted MYSELF from the pinned
  `w12_checks_results.json` (md5 re-hashed = 05776c9e… = the PIN): its `cubic`
  table has 23 rows carrying exactly the 14 distinct pairs {(2,3..7),(3,2..4),
  (4,2),(4,3),(5,2),(7,2),(8,2),(9,2)} ✓. Stronger: a recursive sweep of EVERY
  (q,N) pair appearing ANYWHERE in that JSON (cubic + qrt + l0hist + oracles)
  returns only {those 14} ∪ {(5,3)} — **q = 8 and q = 9 appear nowhere at
  N ≥ 3 in the entire pinned w12 artifact**, so (8,3) is clean.
* **Prototype = +3 pairs.** From the byte-frozen docstring: prototype rows
  Zp (2,3..7),(3,2..4),(5,2),(5,3),(7,3),(11,2) + Fqt (2,4),(2,7),(3,3),(3,4),
  (4,2),(4,3) — 18 rows, adding exactly {(5,3),(7,3),(11,2)} beyond the w12 14.
* **Smoke ⊆ union.** SMOKE_ZP = (2,3),(2,4),(2,5),(3,2),(3,3),(3,4),(5,2);
  SMOKE_FQT = (2,3),(2,4),(3,3),(4,2),(5,2) — 12 rows, every pair inside the
  w12-committed 14 ✓ (the bracket's parenthetical is true).
* **Decontamination.** HEX3 seal e3f3459 = 2026-08-08T06:39:44Z; the only
  other batteries that touch n = 3 TRP territory all post-date it (commit
  timestamps read this pass: HMENU3 seal 64d3ff9 08:40:17Z, QSCOUT22 seal
  970197d 09:53Z / verdict dd67cda 10:00Z, GENIND seal c3212cc 10:16Z, GENH4
  seal 121d9ab 11:45Z); w11 = n = 2 blocks, w10 = order 1 — neither measures
  U₃. Nothing else measured any roster pair pre-seal.
* 29 − 17 = **12**, and the difference set computed by hand is
  {(2,8),(2,9),(3,5),(3,6),(4,4),(4,5),(5,4),(8,3),(9,3),(11,3),(13,2),(13,3)}
  — element-for-element the r2 bracket's honest 12-set ✓. All twelve
  whole-space values re-derived from my OWN law transcription (closed form AND
  first-step form, equal): ALL EXACT (leg 1(4)). The (8,3) = 32,768 = 8⁵
  evidence, honestly itemized: PE2's independent no-runner-imports enumerator
  (its own F₈ tables) measured it; this pass's fresh full re-run of the sealed
  runner re-measured it (Fqt row, 262,144 states, u = 4096); and my own law
  transcription gives 8·8⁴ symbolically. The set-vs-label subtlety ("happens
  to equal the sealed label's twelve entries, but as a DIFFERENT set — (5,3),
  (7,3) out; (8,3),(13,2) in") verified against the sealed list in the frozen
  docstring (12 entries labeled "the 11 rows", including (5,3),(7,3),
  excluding (8,3),(13,2)) ✓. All four note sites carry the r2 correction
  (S1 header, S1 anchors, S7 P-1, S10 P-1) ✓ matching the r2 commit's claim,
  with the [r1] list preserved as struck history (strike-and-extend) ✓.

### 1b. The S8.2 k = 1 factor: it is the law's own k = 1 summand

Re-derived by hand from THEOREM HEX3.A: the k = 1 summand's floor-bearing
part, whole space (×q), is

    q · (q−1)q³(q^{N−3}−1) · ⌊(N−4)/2⌋(q−1)q^{N−5}
      = ⌊(N−4)/2⌋(q−1)²(q^{2N−4} − q^{N−1})
      = ⌊(N−4)/2⌋(q−1)²q^{2N−4}(1 − q^{−(N−3)})

(exponent algebra: q·q³·q^{N−5}·q^{N−3} = q^{2N−4}; q·q³·q^{N−5} = q^{N−1}),
verified additionally as an EXACT polynomial identity in q for N = 5..29
(leg 1(5)). At (2,7): 1024 − 64 = **960**; the pre-r2 display's value was
1024 — the r2 correction and its attribution ("the −q^{N−1} is the k = 1
term's own, from the (q^{N−3}−1) factor, not a smaller k ≥ 2 term") are both
exactly right: the k-th floor mass is ⌊(N−3k−1)/2⌋(q−1)²(q^{2N−2k−2} −
q^{N+k−2}), whose leading exponent 2N−2k−2 ≤ 2N−6 < 2N−4 for k ≥ 2, strictly
smaller. The Θ-claims are unchanged by the (1 − q^{−(N−3)}) → 1 factor ✓; the
aside's "N-linear" scoping (the ⌊(N−4)/2⌋-bearing part; the k = 1 summand's
non-floor part (q−1)q^{2N−3} is N-independent) is coherent; "of U₃^conv" =
whole-space ✓ (the [r1] re-check's ⌊3/2⌋(q−1)²q^{10}(1−q^{−4}) = 960 is
whole-space ✓).

## Charge 2 — the β1 route re-derived IN FULL (FULL(k)-⟨1²,1⟩, m = k)

* **Letters + locus.** Residual cubic on the single slope-k side =
  (y−z)²(y−z′): c₀ = digit_{3k}(B₀) = −z²z′ ≠ 0 (v(B₀) = 3k exact) forces
  z ≠ 0 AND z′ ≠ 0; z ≠ z′ by species; the (double, simple) root data is
  recoverable from the coefficient triple (unique factorization by root
  multiset, characteristic-free), so distinct (z,z′) pin distinct
  (c₂,c₁,c₀) = (−(2z+z′), z²+2zz′, −z²z′): (q−1)(q−2) letter pairs. Free
  slots: (N−1−k) + (N−1−2k) + (N−1−3k) ⟹ locus (q−1)(q−2)q^{3N−3−6k} ✓ = S2.
* **The recentered shape.** Recentering at ẑπ^k shifts the residual by z:
  (y+z−z)²(y+z−z′) = y²(y − w), w := z′−z ≠ 0 — so digit_k(B₂′) = −w ≠ 0,
  digit_{2k}(B₁′) = 0, digit_{3k}(B₀′) = 0. Checked coefficient-wise, three
  universal identities: c₂+3z = z−z′; c₁+2c₂z+3z² = z²+2zz′−4z²−2zz′+3z² = 0;
  c₀+c₁z+c₂z²+z³ = −z²z′+z³+2z²z′−2z³−z²z′+z³ = 0 — valid verbatim in char
  2 and 3. σ_k is then exact division (v(B₂′) = k, v(B₁′) ≥ 2k+1,
  v(B₀′) ≥ 3k+1) and the scaled state's level-0 reduction is x²(x−w): a
  LEVEL-0 DBL member of the window-M system, M = N−3k — exactly where
  W12-L1(a) (Hensel product bijection: block (A₁,A₀) ∈ (πO/π^M)², q^{2(M−1)},
  × unit root r ≡ w, q^{M−1} deeper digits free) applies.
* **m = k is the right m.** The split root's coordinate relative to the new
  center is (z′−z)π^k + O(π^{k+1}): valuation exactly k since w ≠ 0; all later
  recenterings are strictly deeper (inside the cluster), so v(center − r) = k
  is chain-constant.
* **Onto-ness.** recenter ∘ σ_k maps the (z,z′)-slice INTO the reduction-
  x²(x−w) slice, injectively modulo the q^{3k} ghost fiber (2k B₂-digits + k
  B₁-digits); cardinalities: target = q^{3(M−1)} (B̄₂ level-0 digit pinned to
  −w, all else free), and q^{3M−3}·q^{3k} = q^{3N−9k−3+3k} = q^{3N−3−6k} =
  #slice ⟹ ONTO.
* **Drain count.** In the scaled window-M frame B̃₀ = Ã₀·(−r̃) with r̃ a unit
  ⟹ v(B̃₀) = v(Ã₀), and v(B₀) ≥ N ⟺ v(B̃₀) ≥ M (exact division by π^{3k}) —
  so drain ⟺ Ã₀ = 0 in window M; by W12-L1(b) (consumed at pin) + window
  coherence along the β-chain the continued read IS the W-11 block read,
  drain ⟺ block ∈ the R(M) set, r-independent ⟹ drained =
  (q−1)(q−2)·q^{3k}·q^{M−1}·R(M) ✓ the S5.1 table row.
* **Machine, at LETTER resolution (new granularity).** The battery and both
  prior passes check species keys aggregated over letters. Leg 3 checks the
  transport at per-letter fibers at (Zp,3,6): each of the 2 (z,z′) pairs has
  locus 19,683 = q⁹ and drains EXACTLY 3,645 = q³·q²·R(3) (R(3) = 15);
  aggregate (39,366, 7,290) == the committed FULL11SQ(1) tally. Same probe on
  the other routes, aggregates tied to the committed JSON per key this pass:
  VERT1(4,1) per (z,c) fiber (6,561, 1,215) ×4 = (26,244, 4,860) ✓;
  VERT1(5,1) (2,187, 405) ×4 = (8,748, 1,620) ✓; VERT2(5,1) per (λ,z)
  (729, 729 = ALL, M−2j = 1) ×4 = (2,916, 2,916) ✓; ALPHA(1) per z
  (19,683, 2,187 = q³u(3,3)) ×2 = (39,366, 4,374) ✓, with the char-3
  degenerate pin (0,0,−z³) live. Every constructed state also asserted to
  classify to its intended key by the leg-2 classifier. ALL GREEN.

## Charge 3 — the sixth-class hunt (five-way partition completeness)

**Hand case-grid, exhaustive over hull shapes × residual types.** Points
(0,u₀),(1,u₁),(2,u₂),(3,0), u₀ ≤ N−1 (else B0ZERO):

* hull {0,3}: 3 ∤ u₀ ⟹ g = 1, e = 3, linear residual ⟹ RAM3 (DEC).
  3 | u₀ = 3k ⟹ g = 3 cubic residual with c₀ ≠ 0; over F_q its repeated-factor
  options are exactly (y−z)³ (→ α) and (y−z)²(y−z′) (→ β1): a repeated factor
  of degree 2 is impossible in degree 3 (2·2 > 3), and a repeated root is
  forced INTO F_q (multiplicity 2: (minpoly)² | f needs deg ≤ 3 ⟹ deg 1;
  multiplicity 3 likewise; char 3: y³−a = (y−a^{1/3})³ with a^{1/3} ∈ F_q by
  Frobenius bijectivity). Separable ⟹ DEC. z or z′ = 0 excluded by c₀ ≠ 0
  within this hull; would-be z′ = 0 states have v(B₀) > 3k and live in OTHER
  hull shapes.
* hull {0,1,3}: left side width 1, g = 1, never repeats. Right side width 2:
  u₁ odd ⟹ g = 1, e = 2 (LINRAM2, DEC). u₁ = 2k ⟹ residual y² + c₂y + c₁
  with c₁ ≠ 0 (vertex): double root z with z² = c₁ ≠ 0 ⟹ z ≠ 0 (→ β2);
  separable ⟹ DEC. Vertex condition (1,2k) strictly below the chord ⟺
  2k < 2u₀/3 ⟺ u₀ > 3k ✓ the S2 range.
* hull {0,2,3}: right side width 1, never repeats. Left side width 2:
  u₀ ≢ u₂ (2) ⟹ g = 1, e = 2 (RAM2LIN, DEC). u₀ ≡ u₂ =: t (2) ⟹ g = 2
  residual λy² + c₁y + c₀, c₀ = digit_{u₀}(B₀) ≠ 0: double root z ≠ 0
  (z² = c₀/λ ≠ 0) (→ β3, j = (u₀−3t)/2 ≥ 1 from u₀ > 3t (vertex) + parity ⟹
  u₀ ≥ 3t+2); separable ⟹ DEC.
* hull {0,1,2,3}: three width-1 sides, all g = 1 ⟹ 3LIN (DEC).
* No state can carry TWO repeated-residual sides: a repeated residual needs a
  width-≥ 2 side with e = 1; two such sides need total width ≥ 4 > 3 (the
  width budget). Nothing is left over: **B0ZERO + five refine species + DEC
  exhaust**, with every letter/pin count matching S2's closed forms.

**Machine hunt.** My own classifier (independent transcription of S2, own hull
code) ran over EVERY state of 20 full rows — 5 corpus validation rows PLUS the
15 new-ring/new-(q,N) rows of leg 2, spanning 14 distinct rings — asserting
(i) every state receives exactly one class (an unclassifiable hull RAISES, and
a repeated residual root on an e ≥ 2 side or a double refine RAISES),
(ii) class loci == the S2 closed forms, both directions, (iii) partition sum
== q^{3(N−1)} exactly, and (iv) **DEC states NEVER drain** (a sixth,
drain-capable class hiding inside DEC would fire here). DECdrain = 0 on all
20 rows; zero raises. No sixth class.

## Charge 4 — HEX3-W12TIE: what ties, and its currency post-W12-r2

**What ties (code read).** For each of the 23 rows of the pinned w12 JSON's
`cubic` table, keyed (kind,q,N): `q * sum(drained over this battery's species
tally)` — i.e., THIS battery's independently measured q·u — must equal the
committed `U3TRP_measured_conservative`; a w12 row missing from the roster is
itself a violation (coverage direction). So P-4's gloss is warranted by
LAW + W12TIE jointly: law == u_measured (LAW) and q·u_measured == committed
(W12TIE) ⟹ the law retro-predicts the w12 EXPLORATORY column with zero free
parameters ✓. Closed independently this pass: my own law transcription
evaluated directly against the committed U3TRP column — 23/23 EXACT, and the
committed column is itself char-uniform at every shared pair (re-checked).

**Currency.** `w12_checks_results.json` has exactly ONE commit in its entire
history (c16c717, the w12 verdict); working-tree md5 re-hashed ==
05776c9e… == the HEX3-PIN value. W-12's r1 (ba0d1a4), annex (8e535d2), r2 +
ANNEX 2 (99f1813) are all note-only. The full post-verdict W12_PROOF diff
(c16c717..HEAD, 24 removed lines) was read and every hunk near HEX3-consumed
material cleared individually: (a) the S2.3 trichotomy edit is W12-r1-F3's
own repair (e ≥ 2-side repeated residuals open composite stages, not
"recenter deeper"), explicitly and correctly n = 3-harmless — at n = 3 every
e ≥ 2 side has g = 1, which my hand grid AND leg 2's never-firing
`assert e == 1` independently confirm; (b) the exploratory-column edit
(W12-r1-m2) only rescopes the char-uniformity SENTENCE to the nine genuinely
shared pairs — the U3TRP values and the JSON are untouched; (c) everything
else is W-12.A display (not consumed here), conditionality-wrapper and
arc-record lines. The tie is CURRENT. Bonus: HEX3's §S8.1 annex text
re-extracted from the note at HEAD and diffed against the block inside
W12_PROOF at HEAD (both quote-normalized): **EQUAL** (768 bytes) — the W12
r2 edits left the applied annex intact, as claimed.

## Charge 5 — supplier/consumer currency at read time

Facts established from git at read time: HMENU3 ACCEPTED 2/2 at 050425d
(PE3 7e5026a + PE4 6249166 clean); W-11 ACCEPTED (fold 35e6545; diff
31506b3..HEAD on W11_PROOF_2026-08-08.md has ZERO removed lines, 30 appended
— the consumed body is frozen at exactly HEX3-S9's r2-HEAD pin 31506b3 ✓);
W-12 at r2 (99f1813), no PE3 yet. Findings: **none**. HEX3 nowhere states a
consumer's grade (grep: no HMENU3/GENIND/QSCOUT/GENH4/GENHN mention anywhere
in the note); its (hMenu-3) surfaces ("untouched here", BOX-4's "No claim
that W-12.D fires at n = 3 yet") are scope statements about THIS unit's
claims, not grade assertions about others, and remain literally true (HEX3
itself is still in-arc). S9's supplier pins are as-of pins that remain
accurate: W-11 @ 7020ceb/cb05127/31506b3 ✓ (commits verified); W-12 @
f669cb0/c16c717/97122f2 ✓; J-D0 @ 1642275/9387eb1 ✓ (JD0 seal/verdict,
2026-08-07, exist as pinned). BOX-2's [r2] arc record and S10's [r2] bracket
were checked line-by-line against the actual PE2 report f60348b (census
basis, q = 27 row, N ≤ 40 poly leg, 39 R(M) cases, (8,3) = 32,768): accurate.

**Remark 1 (no finding).** §S8.1's title "(text offered; W12_PROOF not
edited)" predates the annex's application at 8e535d2 and can be read stale;
it is accurate about this note's own commits (the application was a separate
W12-side dated append, and the applied block is equal at HEAD — checked
above). Same convention HMENU3-PE4 ratified on the BOX-2 annex.

## Machine leg (this pass; all runs fresh in this session)

* PINS: all four md5s re-hashed and MATCH (w12_checks.py 7dc0…, w11_checks.py
  500a…, w10_checks.py a9c3…, w12 JSON 0577…).
* Runner md5 83faf7ed… == seal e3f3459 (`git diff e3f3459 -- runner` empty);
  both repair commits verified single-file note-only by `--stat`.
* FULL RE-RUN (single fresh run): exit 0, **GREEN, 158,512 checks /
  0 violations** — PIN 4, LAW 92, SPECIES 172, XREAD 158,204, W12TIE 23,
  CHAR 17; teeth fired 10/20/13 == preregistered, with all three fire-row
  sets re-derived from the roster by hand (T-FLOOR: the ⌊(M−1)/2⌋→⌊M/2⌋
  corruption changes R(M) only at even M = N−3k, k ≥ 1 ⟹ N ∈ {5,7,8,9} ⟹
  10 rows; T-ALPHA: N ≥ 4 ⟹ 10 Zp + 10 Fqt = 20; T-VERT1: N ≥ 5 ⟹ 7 + 6 =
  13). 331.5 s. XREAD roster sum re-derived by hand: 77,500 ℤ_p + 80,704
  𝔽_q[[t]] = 158,204 ✓. 46/46 rows, 67,410,225 states (JSON-summed ✓).
  Fresh JSON == committed with ZERO non-timing leaf diffs (full recursive
  diff; 20 elapsed_s leaves differ); fresh output txt diff = timing lines
  only; artifacts restored, md5s (6e4b…, ce6f…) == §S10's display.
* SMOKE: `--smoke` reproduces S7's disclosed record to the digit
  (PIN 4 / LAW 24 / SPECIES 30 / XREAD 26,730 / W12TIE 12 / CHAR 4, teeth
  1/4/1, GREEN 0.4 s).

## Fresh route (no runner imports; /tmp/hex3_pe3_leg{1,2,3}.py, audited + re-run)

**Leg 1 — GF/transfer-operator route (own exact polynomial engine;
sympy-free).** Z[q]-coefficient power series in x, all-integer arithmetic.
(i) The renewal equation U = S + A·(U + T − S) (S = B0ZERO column, T = the
drained β-bracket (q^M−1)R(M), A = the α re-entry kernel Σ(q−1)q^{3k}x^{3k})
solved by exact series INVERSION (not iteration): coefficients == THEOREM
HEX3.A's closed form **symbolically in q**, N = 1..36; the first-step
recursion iterated independently agrees. (ii) NEW OBJECT: D(x)·U(x) is a
polynomial for D = (1−q²x)²(1+q²x)(1−qx)²(1+qx)(1−q⁴x³) — i.e. u(q,N)
satisfies an ORDER-9 constant-coefficient linear recurrence (N ≥ 10), the
transfer-operator form of the law; verified symbolically as the series
identity through x^40 and directly on closed-form values N ≤ 36 (and D is
exactly the rational-denominator budget of S, T, A/(1−A), so the recurrence
is structural, not empirical). (iii) The twelve-set values ALL EXACT; closed
form == committed u_measured on 46/46 rows. (iv) The S8.2 k = 1 mass identity
(charge 1b) proved symbolically, N = 5..29.

**Leg 2 — nine never-instantiated DVR types, own reader (own hull via slope
walk, own root multiplicities, own generic shift3, own field tables incl.
F₂₅ = F₅(√2), F₄₉ = F₇(√3)).** After validating on 5 corpus rows (u values ==
committed; species == the S5.1 forms the committed JSON equals): **totally
ramified mixed char** ℤ₂[√2] (e = 2, π² = 2, componentwise carries audited)
at N = 4,5,6,7; ℤ₃[√3] at N = 4,5; ℤ₂[∛2] (e = 3) at N = 4,5,6; **unramified
mixed char at prime-power q** W(F₄) at (4,4), W(F₉) at (9,3) — the corpus's
prime-power rows were 𝔽_q[[t]]-only, so these are the FIRST mixed-char
prime-power instances of the law anywhere; **first-ever q = 25 and q = 49**:
F₂₅[[t]], W(F₂₅), F₄₉[[t]], W(F₄₉) at N = 2. ALL 15 new rows: u == law,
species tables == S5.1 both directions, partition sum exact, DEC-drain 0
(fresh run this session, output identical to the interrupted log). This is
the first machine evidence for THEOREM A's stated scope beyond the two
battery ring types — "independent of which DVR realizes F_q" now holds at
e = 2, e = 3 Eisenstein carries and prime-power Witt carries.

**Leg 3 — letter-resolution transport fibers at (Zp,3,6)** (described under
charge 2): all four routes' per-letter (locus, drained) fibers exact — 2 β1
pairs, 8 β2 fibers, 4 β3 fibers, 2 α fibers — and all five key aggregates
tied to the committed JSON tallies this session. GREEN.

**Remark 2 (no finding; positive).** THEOREM HEX3.A's S1 conventions scope O
to ANY complete DVR with residue field F_q while the proof prose says "both
ring types" at several points (H-2(i), S5.4) and the battery covers only
ℤ_p/𝔽_q[[t]]. The counting arguments are in fact transversal-generic (nothing
uses e = 1 or equal characteristic; pins are residue-field identities; window
coherence is a quotient-hom statement), and leg 2's ramified/Witt rows now
corroborate the full-scope reading at 9 new-type rows, 0 violations. A future
fold could sharpen the S5.4 wording from "both ring types" to "any O as in
S1"; nothing is wrong.

## Disposition

0 CRITICAL, 0 GAPS, 0 MINOR; 2 remarks recorded above (S8.1 dated-artifact
wording; S5.4 scope wording — both no-change-required), plus the provenance
disclosure (draft defects corrected before commit; the note itself untouched
by them). Every charge confirmed: the [r2] repairs are correct and complete
at all four sites; the repair-bracket lineage's third audit found nothing
left to catch. **First clean pass of the arc: counter 1/2; per protocol PE4
is the accepting attempt.**
