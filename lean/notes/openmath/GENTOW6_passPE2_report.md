# GENTOW6 passPE2 — HOSTILE VERIFIER REPORT (second pass), 2026-08-10

**Target:** `lean/notes/openmath/GENTOW6_PROOF_2026-08-09.md` @ HEAD
(r1 verdict commit 3b6bf5ce). Arc: seal 59ea785/5fb8fd7 → PE1 NOT
CLEAN 1C/1G/4m (cd74ef6f) → r1 = e004788 (scope pin + gauge annex +
LEMMA GENTOW-6.4) / 1432968 (cap-lemma seal) / e803c21 (run-1 RED,
kept) / 3b6bf5c (verdict). Counter at entry: 0/2. Protocol:
quote-and-classify, fix nothing.

**VERDICT: CLEAN — 2 MINOR, nothing GAP-or-worse. The F-2 repair is
ADJUDICATED REPAIRED-PROVED: LEMMA GENTOW-6.4 survived independent
re-derivation and a fresh stress at a partial-side member the repair
never used; its conditional COR GENTOW-4.C cite is displayed at both
consumption points. The f1 = 1 scope pin is complete at every
load-bearing site; my fresh f1 = 2 / eta != 1 frames BROKE the
sealed (c) exactly where the pin predicts (the boundary tooth fired)
while ANNEX-THEOREM 6.3'(b')'s certificate display verified EXACT
at both. Machine: all seals byte-intact, three isolated re-runs
green (caplemma bit-identical), post-seal instrument-repair diff =
exactly the two disclosed fixes. Counter: 0/2 ⇒ 1/2.**

## FINDINGS

### F-1 (MINOR) — two stale summary sites still read the pre-r1
### genre-general scope

Quotes: STATUS TABLE row (3) (L50): "PROVED at mu2 = 2 (CERT-TOP
unconditional; regimes 3/4 displayed; mu2 >= 3 = GENTOW6-BOX-1)";
S3 section header (L311–312): "THEOREM GENTOW-6.3 (the attainment
certificate — GENTOW3-BOX-1 made genre-general at mu2 = 2)".
Neither carries the f1 = 1 pin or a pointer to GENTOW6-BOX-4; the
table's residue census names only mu2 >= 3. Every LOAD-BEARING site
is pinned (theorem head rider L344–354; quadrichotomy rider L476;
S5 consumption rider L564–570; S3 setting gauge pin L319–330; the
header ARC block L10–19 names the repair 25 lines above the table).
Failure scenario: a consumer skims the status table or section
header, cites "attainment at mu2 = 2, every genre, CERT-TOP
unconditional" into a downstream note without the f1 = 1 scope, and
re-imports PE1's F-1 one document over. Repair shape: a pin token
on the two summary sites.

### F-2 (MINOR) — LEMMA GENTOW-6.4(a)'s bijection codomain is
### over-stated at D2 ∤ n members

Quote (S6.2): "and induces, per window N, a bijection (monic f of
degree n mod pi^N) <-> (digit tuples mod pi^N, top digit pinned to
1)". The digit grid is declared on j <= M = floor(n/D2), a < D',
b < e2f2 — (M+1)·D2 slots. At partial-side members D2 ∤ n (e.g.
FRAME-P: n = 10, 12 slots), so the grid has slots of slot degree
> n whose digits are FORCED to zero by the triangular display; the
map bijects onto tuples supported on slot degrees <= n with top
pinned 1, not onto all top-pinned tuples. Failure scenario: a
consumer reads (a) as a per-window COUNT law on the full grid at a
partial-side member and over-counts free digits by the above-top
slots. Nothing downstream bites today: COR 6.2C(d)'s chain consumes
only (a)'s triangularity + (b)'s band-1 cap (per-slot congruence),
both of which I verified independently; the count layer at blocks
rides GENTOW-1(b) at f_S on 𝒯* (in scope). The machine leg cannot
see this (P-A/P-B test triangularity/congruence; no surjectivity
tooth). Repair shape: "supported on slot degrees <= n" in the
codomain (or "above-top digits pinned to 0").

## THE F-2 ADJUDICATION (charge 1) — REPAIRED-PROVED

r1 chose prove-first (per the standing directive): LEMMA GENTOW-6.4
is claimed NEW this wave. My verdict: **the lemma is correct, its
proof mechanism is sound, and it supplies COR GENTOW-6.2C(d)'s
window sentence at exactly the consumed strength.**

* **Independent re-derivation (a).** Division with remainder by a
  FIXED monic key is Ô-linear in the dividend, and each output
  coefficient at degree d = (dividend's degree-d coefficient) +
  Ô-combination of strictly higher dividend coefficients (each
  reduction step subtracts top·x^{deg−D}·key, touching only lower
  degrees). Stage 1 (Phi2-adic): [C_j]_d = [f]_{jD2+d} + comb of
  [f]_{>jD2+d} (higher coordinates included — all above the slot
  degree). Stage 2 (Phi'-adic within C_j) acts within the block and
  is triangular in bD'+a. The composite is triangular-unimodular in
  total slot degree jD2+bD'+a. Verified by hand at a D2 = 2 toy
  (c_{0,1} = [f]_1 − β[f]_2 + (β²−γ)[f]_3 for key x²+βx+γ). No 𝒯
  input anywhere — the PE1 observation ("triangularity is division
  algebra, not locus geometry") holds up.
* **Independent re-derivation (b).** Both directions checked: (i) a
  digit with v(c) < N keeps its valuation across any pi^N-lift
  (c' ≡ c mod pi^N), so its height e1e2·v + w is lift-stable; (ii)
  an unread digit (v >= N) has v(c') >= min(v, N) = N in EVERY
  lift — it can DROP to exactly N but never below — so its height
  stays >= e1e2·N (w >= 0) and can neither move nor tie a minimum
  landing < e1e2·N. The undercut instance (the w = 0 slot at v = N,
  height exactly e1e2·N) shows the cap is sharp. GENTOW-5(a)'s
  band-1 mechanism, run without the locus — as claimed.
* **(c) + the conditional cite.** The block correspondence rides
  HE6R1-2(b) + COR GENTOW-4.C; the note displays the conditionality
  TWICE ("the latter at GENTOW4's 0/2 attempt grade, conditional" in
  6.4(c); "conditional, named" in the (d) rider) — the charge's
  display requirement is met. The c_g self-stability parenthetical
  (m >= 0 ⟹ c_g <= m + c_g < e1e2·N ⟹ c_g stable by (b)) is
  sound since c_g = p_{mu2*} is itself a slot-min.
* **Consumer walk of the (d) rider.** "COR 6.2C(d) consumes only the
  below-cap band, so nothing narrows" — verified against the sealed
  (d) text: its window sentence is a strictly-below-cap statement
  ("caps consulted block heights at e1e2·N − c_g"); GENTOW-5's
  clauses (b)–(e) are consumed only at f_S, which LEMMA GENTOW-6.2
  puts on 𝒯* (in scope). The display reads verbatim as sealed; the
  citation of record is re-pointed in an in-place rider. No
  narrowing anywhere.
* **Statement stress at a member the repair did NOT use** (fresh
  leg B below): the deg-18, two-class + sibling member at TWO grids,
  including the first e2f2 = 6 (six b-slot) grid in the arc —
  triangularity diagonal exact at all 18 degrees x 2 eps x 2 grids,
  window congruence, pin stability below cap, undercut hitting
  EXACTLY e1e2·N, and the (c)-projection (59,15) − 15 = (44,0)
  reproduced through COR 4.C's displacement. One statement-wording
  gap found = F-2 above (MINOR, unconsumed).

## SCOPE-PIN COMPLETENESS (charge 2)

Grepped every 6.3/(a)/quadrichotomy/CERT-TOP consumer, in-note and
repo-wide:
* Pinned and governing: theorem head (rider directly under the
  head), (b)'s "UNCONDITIONALLY at every genre with 2i_{t*} >= D'"
  (literally true even at f1 >= 2 — hypothesis empty there; and
  governed by the head rider), quadrichotomy (own rider), S5
  consumption line (rider), S3 setting (gauge pin + x-free rider),
  S6.1 annex self-scoped ("machine-unexercised at f1 >= 2,
  GENTOW6-BOX-4").
* Cross-note: BRIDGE_ADJUDICATIONS' B3 record (pre-PE1, "PROVED at
  mu2 = 2" unpinned) is superseded within the same ledger by the
  dated PE1 record (L15098+, full scope display) — dated-append
  discipline holds; PROJECT_STATE append #19 carries the corrected
  scope; GENTOW3's consumer walk cites only GENTOW-3(i) + BOX-1
  framing (not 6.3's content). No stale ungoverned consumer outside
  the note.
* Residual stale sites in-note = F-1 (two summary displays).
* **Vacuity inequality re-verified** (hand + machine): i_{t*} <=
  e1 − 1 gives 2i_{t*} <= 2e1 − 2 < 2e1 <= e1·f1 = D' for f1 >= 2
  (strict since e1(f1−2) + 2 > 0); the sealed (b) hypothesis is
  unsatisfiable there, so sealed-(b) is vacuously true, not false —
  the note's classification is exact. P-E's 132-pair scan re-run
  green; the inequality is also an instance-check in my leg A.

## S5 BOX-1 UNDER THE NEW SCOPE (charge 3)

**Fence HOLDS.** GENTOW6-BOX-1 asserts a restriction ("THEOREM 6.3
is scoped to mu2 = 2"), displays the mu2 >= 3 temptation ("the
diagonal argument LOOKS uniform") and claims nothing. Under the r1
pin the theorem is scoped to mu2 = 2 AND f1 = 1; the box's
restriction sentence is incomplete but not false, and the f1 axis
is fenced by its own box (GENTOW6-BOX-4, adjacent in the same
list). A future BOX-1 closer at f1 >= 2 would need the monomial-
pair census compounded with the k-extraction ledger — the box's
top-tuple observation (coefficient 1 through (t*,...,t*)) survives
the corrected lifts (top x-degree k·I_{t*} attained only by the
all-(t*,r*) tuple, same max-forces-diagonal argument). No repair
owed; no consumption of mu2 >= 3 anywhere in the note.

## FREE HUNT (charge 4) — clean charges

* S6.1 (LIFT) integrality re-derived: a_t = (m_t − i_t·h)/e1 >
  (f1−1)h >= r·h since m_t >= u2 > e2D'h >= e1f1·h; x-support
  i_t + e1·r pairwise distinct, all <= e1f1 − 1 < D'. Exact.
* 6.3'(b') deltas: (i) Y-uniqueness x-shape-free — checked; (ii)
  top-monomial uniqueness (r,r' <= r* forces diagonal) — checked,
  and the DISTINCT-slot claim for non-top overflowing pairs
  machine-verified at A-rich (the x^4 pair extracts to slot (0,1),
  certificate slot (2,1) untouched); (iii) digit/valuation/height
  formula machine-verified at two frames (v = 2(a_{t*} − r*h),
  height = THETA_{j*} exactly). (c') equivalence (pairwise <=>
  2·max I_t < D') — checked.
* COR 6.1C(c) re-fence (F-6), S0 census rider (F-5(i)), S4 seal
  pins (F-5(ii)), F-4 closure record, S5 GAUGE-AXIS row — all match
  what I could independently confirm (constructor grep: PHI1 ∈
  {x²−2, x³−2, x²−3} across the sealed runners; every frame f1 = 1,
  eta = 1).
* Honest-status displays: 6.3' rides GENTOW3 S7.1 (GT3-r1, arc open
  at 0/2) and says so; the S1 cite-conditionality box unchanged.
* Record sentences: enumerative throughout the r1 additions; no
  universal quantifier found in any record sentence.

## MACHINE LEG (charge 5)

* **Seals:** all six S6.4 md5s re-verified at HEAD (checks runner
  121e5c4a…, output 1bcb950…; pe1_fresh 59fe76c…/9de6132…; r1
  caplemma bf953a8…/fa9d7bf…); the caplemma seal md5 640b31ff at
  1432968 confirmed by `git show | md5sum`.
* **Post-seal instrument-repair diff audited** (1432968 → HEAD):
  exactly the two disclosed fixes — the FRAME-P key literal
  [9,-9] → [0,-9] (Phi'²−9x+9 → Phi'²−9x) and the full-grid digit
  dict (zero slots included). Predictions, teeth, frames, checks
  byte-untouched. The run-1 RED story (303/34, both families
  instrument-side, artifact kept at e803c21) is exactly as
  disclosed.
* **Isolated re-runs (fresh dir):** gentow6_r1_caplemma.py GREEN
  303/0, 2/2 teeth (T-TRI x28 = 10+10+8 degrees, T-CAP x3),
  BIT-IDENTICAL to the committed artifact; gentow6_checks.py GREEN
  401/0, 4/4 teeth (differs only by a gp stack-size stderr line +
  timing suffix, as at PE1); gentow6_pe1_fresh.py GREEN 22/0,
  identical.
* **Tautology audit (r1 leg):** check-count arithmetic verified
  (112 TRI + 50 window/pin + 9 undercut + 132 VAC = 303). Digits
  are measured through actual iterated division; P-C's pin
  predictions are hand-derived and carry the projection content
  (26 = 21 + c_g, 5 = 0 + c_g through the c_g-displacement) —
  non-tautological. One redundancy observed (not a finding): the
  BLOCK-STAB rows are arithmetically implied by PIN-STAB + constant
  c_g (both sides shift by the same constant); the independent
  block-side evidence lives in the P-C pin predictions and in my
  fresh projection row, not in BLOCK-STAB.
* Note detail confirmed: S6.2's "pins (26, 16, 5)" at FRAME-P = the
  MEASURED triple (p_1 = 16 measured, unregistered; preregistered
  were p_0 = 26, p_2 = 5) — phrasing honest.

## FRESH ROUTE (charge 6) — disjoint from PE1's legs

Instrument `verification/openmath/gentow6_pe2_fresh.py` (own
integer-exact core, no sealed-runner imports; gp/PARI as the
decorrelated oracle; predictions preregistered in the docstring).
**Run 2 GREEN — 213 checks, 0 violations, 2/2 teeth; isolated
re-run bit-identical. Run 1 RED, kept** (transcript tail,
gentow6_pe2_fresh_output_run1_RED.txt): three verifier-side defects
(an off-grid coded literal for the top dev coefficient; a K2y sign
already carried by the lift literal; the LEG B side placed at [0,8]
where the Minkowski order puts the steeper sibling side LEFT — hull
(0,26)→(1,20)→(9,0), the 5/2-side is [1,9]), all hand-traced before
repair; no content prediction (residuals, multiplicities, tie
values, pins, certificate digits/heights) changed.

* **LEG A — the f1 = 2 / eta != 1 boundary tooth + first contact
  for 6.3'(b').** First f1 >= 2 frames anywhere in the GENTOW6 arc:
  Q2, Phi' = x⁴+2x²+4 (e1 = 2, f1 = 2, h = 1, D' = 4; eta =
  res(x²/2) generates F_4), genre e2 = 2, f2 = 1, u2 = 9, E2 = 18,
  delta = 1, THETA_0 = 37; PARI confirms Phi' and both Phi2's
  irreducible over Q2 (genuine keys). Two digit data: c_0 = eta
  (lift 8x³) and c_0 = 1 + eta (lift 16x + 8x³). At BOTH: the
  sealed (c)'s hypothesis holds (2i_0 = 2 < 4) while its conclusion
  FAILS — dev(Phi2²) carries the nonzero Phi'¹-coefficient
  64x² ∓ 128 (T-NAIVE fired x2): **the r1 scope pin's predicted
  boundary break, demonstrated from outside, dual-oracle exact
  (own division = gp divrem = the hand ledger).** Simultaneously
  ANNEX-6.3'(b') verified at the display level: honest read DRAIN;
  shadow Ghat_2 = 1, Ghat_1 = 0; certificate slot (j*,a*,b*) =
  (0,2,1) with digit 64 = lift(lambda)²·2^{2(4−1)}, v = 6 =
  2(a_{t*} − r*h), unit part 1, slot height 24 + w(2,1) = 37 =
  THETA_0 — divergence EXACTLY on the floor; at A-rich the second
  overflowing (non-top) monomial pair extracts to the DISTINCT slot
  (0,1) and leaves the certificate digit byte-unchanged (delta (ii)
  of (b') exercised). GENTOW6-BOX-4 remains OPEN as the note's own
  obligation (my leg tests the dev/shadow displays, not the sealed
  battery apparatus) — but the annex now has its first external
  machine contact, and it held.
* **LEG B — first f2 = 3 mixed-side class (l·deg r = 6) + the 6.4
  stress member.** Q3, Phi' = x²−3, slope-5/2 side: keys Phi2_c =
  Phi'⁶ − 3⁵Phi'² − 3⁷x (psi_c measured = T³−T−1, irreducible,
  deg 3 — beyond the sealed fence's named l·deg r = 4 gap) and
  Phi2_l = Phi'² − 9x (psi_l = T−1); member f = (Phi2_c + 3^{11})
  ·(Phi2_l + 3⁶)·(Phi' − 27), deg 18. Results, each preregistered:
  R(f) monic-normalized = psi_c·psi_l EXACTLY (the (MULT)/UFD
  display; m_c = m_l = 1 with psi² ∤ R); composed reads: cubic-key
  pins (59, 15), hull drop 44 > T2 = 30, mu2*(c) = 1; mu2*(l) = 1
  — **LEMMA 6.1's tie mu2*(r) = m_r at an f2 = 3 class, both
  classes**; PARI decorrelated leg: factor degrees {12, 4, 2},
  poldisc != 0, class degree sums 12 = D'·l·deg(r)·m_r and 4 via
  per-root resultant valuations, sibling excluded with its
  valuations landing exactly AT the floors (7.5/2.5, matching the
  hand-derived no-cancellation units psi_c(1) != 0, u² ∉ F_3).
  LEMMA 6.4 stress at this member (unused by r1): TRI diagonal
  exact (18 degrees × 2 eps × 2 grids, incl. the six-b-slot grid),
  window congruence + in-window valuations (N = 7), pins below cap
  28 stable, undercut moved p_0 from 59 to EXACTLY 20 = e1e2·N_u
  with p_1 = 15 held, projection p_j(f) − c_g = p_j(B_c) = (44, 0)
  and the linear-key analogue (24, 0).

Artifacts: gentow6_pe2_fresh.py (md5 061639c322dfd98a48dc399f07e6dd04)
· gentow6_pe2_fresh_output.txt (2c512551332f20580dfaac142e1cb40a,
exit 0) · gentow6_pe2_fresh_output_run1_RED.txt
(c3ee20a648cc1afc39a4e19ed739c114) — committed at 55fb9074.

## GRADE LINE

**CLEAN: 0 CRITICAL, 0 GAP, 2 MINOR (F-1 stale summary sites, F-2
bijection codomain wording). Nothing GAP-or-worse survives ⇒ the
counter advances 0/2 → 1/2.** The two minors are one-token repairs
and neither is consumed by anything at HEAD; they can ride to the
acceptance fold (sibling-arc pattern) or be folded in an r2 at the
composer's discretion — they do NOT hold the counter. The r1 repair
raised the note's floor: the scope pin is honest and complete where
it bites, the gauge annex re-derives rather than transcribes, and
LEMMA GENTOW-6.4 is real mathematics that survived a hostile stress
at a new member. PE3 = the acceptance attempt; suggested fresh
surfaces there: an eta != 1, f1 = 1 tie frame (the S5 fence's other
axis), and the BOX-4 leg if the composer lands it.

Verifier: GENTOW6 passPE2 (fresh context, zero prior stake).
