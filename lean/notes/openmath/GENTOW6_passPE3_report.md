# GENTOW6 passPE3 — HOSTILE VERIFIER REPORT (acceptance attempt), 2026-08-10

**Target:** `lean/notes/openmath/GENTOW6_PROOF_2026-08-09.md` @ HEAD
(rider commits e7a6b8c2 + 1194b1a4). Arc: seal 59ea785/5fb8fd7 →
PE1 NOT CLEAN 1C/1G/4m (cd74ef6f) → r1 3b6bf5ce (scope pin + gauge
annex + LEMMA GENTOW-6.4) → PE2 CLEAN 0C/0G/2m (161e8ce1, counter
0/2 → 1/2) → post-PE2 rider (PE2-F-1/F-2 folds). Counter at entry:
1/2. Protocol: quote-and-classify, fix nothing.

**VERDICT: CLEAN — 0 CRITICAL, 0 GAP, 1 MINOR (F-1, the BOX-4 /
S6.1 "no machine contact" sentences stale in the conservative
direction at HEAD). Nothing GAP-or-worse survives. The two rider
folds re-derived exactly (the codomain bracket's n mod D2 ≠ D2−1
condition is correct and sharper than the PE2 report's framing);
the cap lemma survived a full system re-walk plus a fresh band-1 +
codomain stress at a member no prior leg used; the three count-
grade boxes are honest at the final text; the fresh route is GREEN
61/0 with 6/6 teeth and delivered the FIRST gauge-live (η ≠ 1)
tie frame anywhere — LEMMA 6.1's display held exactly while the
η-blind mutant read broke on cue. Counter: 1/2 ⇒ 2/2 —
GENTOW6 ACCEPTED.**

## FINDINGS

### F-1 (MINOR) — GENTOW6-BOX-4 and the S6.1 honest-status sentence
### still assert "NO machine contact ... in any leg (sealed or
### fresh)" — false at HEAD in the conservative direction

Quotes: S5 BOX-4 (L633–639): "[GT6-r1] ANNEX-THEOREM GENTOW-6.3'
(S6.1) and the corrected-lift readings above have NO machine
contact anywhere in this note's arc: no f1 >= 2 frame, no
eta != 1 frame, exists in any leg (sealed or fresh)"; S6.1 honest
status (L798–800): "NO machine contact: every battery and fresh
frame in this note's arc is f1 = 1 and eta = 1". Both are dated
[GT6-r1] and were true at r1; at HEAD the arc contains PE2's fresh
instrument (gentow6_pe2_fresh.py @ 55fb9074: first f1 = 2 /
eta != 1 frames, 6.3'(b') display verified exact at two digit
data) — and this pass adds eta != 1, f1 = 1 contact (below). The
S6.5 fold did not refresh either sentence. The box's OPEN status
remains CORRECT: its ask is a sealed battery-grade leg (the
verifier legs test the dev/shadow displays, not the sealed
apparatus), so 6.3' stays prose-only in the note's own grading.
Failure scenario: a consumer reads BOX-4 at HEAD, concludes 6.3'
has zero machine evidence of any kind, and re-runs a redundant
first-contact leg or under-prices the annex in a downstream
grading decision. Direction conservative (understates evidence);
consumed by nothing. Repair shape: a dated bracket on the two
sentences (acceptance-fold species).

No other finding survived verification.

## RIDER AUDIT (charge 1) — both folds re-derived, EXACT

**PE2-F-1 fold (the two summary sites).** Diff 161e8ce1..HEAD on
the note = exactly the five disclosed edit sites (head ARC block,
STATUS TABLE row (3), S3 section header, the 6.4(a) bracket, S6.5)
+ the two rider artifacts; sealed statement displays byte-
untouched. Row (3) and the S3 header now carry the theorem-head
pin's content verbatim-in-substance: "every genre" reads AT f1 = 1
at the corrected chat_t; CERT-TOP unconditional at f1 = 1 genres
with 2i_{t*} >= D' and VACUOUS at f1 >= 2; f1 >= 2 =
ANNEX-6.3'/GENTOW6-BOX-4. Checked against the pinned head (L368–
378): the vacuity direction (2i_{t*} <= 2e1−2 < 2e1 <= e1f1 = D',
strict at f1 >= 2) re-verified by hand; no residual unpinned
summary site found by grep (attainment/genre-general/CERT-TOP
sweeps).

**PE2-F-2 fold (the 6.4(a) codomain).** Re-derived from the
lemma's own triangular display, independently of the bracket: the
slot-degree map (j,a,b) ↦ jD2 + bD' + a bijects the grid onto
0..(M+1)D2−1 (within a coordinate, bD' + a is the base-D'
representation of 0..D2−1); monic f of degree n has coefficients
[f]_0..[f]_n with [f]_n = 1; c at slot degree d = [f]_d +
Ô-comb of strictly-higher [f]_{d'}, so every above-top digit is
forced to 0 and the slot-degree-n digit to 1. Above-top slots
exist iff (M+1)D2 − 1 > n ⟺ n mod D2 <= D2 − 2 ⟺
**n mod D2 ≠ D2 − 1**, with count D2 − 1 − (n mod D2): the
bracket's exact condition is CORRECT and strictly sharper than the
PE2 report's D2 ∤ n framing (FRAME-F: n = 8, D2 = 4, count 3 —
a D2 | n member WITH above-top slots, as the bracket says;
FRAME-P/P2: count 1 each). The corrected codomain (supported on
slot degrees <= n, top pinned 1) makes the free-coordinate counts
match (n slots of degree < n ↔ [f]_0..[f]_{n−1}), so the
unit-diagonal triangularity gives the bijection mod pi^N.
Machine leg audited: gentow6_rider_codomain.py is self-contained
exact-integer; 24 = 3 frames × 8 checks; the 56 = 2n perturbed
members (20+20+16); reconstruction runs through an independent
multiplication path (not the division code) — non-tautological;
T-COD's tampered tuple genuinely leaves the degree-n member set.
Consumer walk re-run: (b)'s proof consumes Ô-linearity
(congruence) + heights only; (c) substitutes (b); 6.2C(d)'s rider
cites 6.4(c); the bijection/count face is consumed nowhere at
HEAD (the block COUNT layer rides GENTOW-1(b) at f_S on 𝒯*, COR
6.2C(b)) — the bracket's walk statement is accurate.

## THE CAP LEMMA AS A SYSTEM (charge 2) — no residual daylight

* **Statement:** monic f of any degree, no locus hypothesis —
  scope honest (partial-side members included; 𝒯-free).
* **(a) triangularity:** re-derived — division by a fixed monic
  key is Ô-linear (uniqueness of quotient/remainder) and each
  reduction step subtracts top·x^{deg−D}·key, touching only
  strictly lower degrees; the two-stage composite is triangular-
  unimodular in total slot degree; bijection mod pi^N on the free
  coordinates with the rider codomain. Stressed fresh (LEG B
  below): TRI diagonal exact across 36 perturbed members of a
  deg-18 member never used in any leg, on TWO grids (D2 = 4, 8).
* **(b) band-1, both directions:** (i) v(c) < N ⟹ every pi^N-lift
  keeps v and the leading residue (c' ≡ c mod pi^N); (ii) unread
  digits have v(c') >= N in EVERY lift, height >= e1e2·N — they
  can drop to the cap but never below, so no computed slot-min
  landing < e1e2·N moves or ties; the (0,0)-slot v = N instance
  realizes e1e2·N exactly (cap sharp). The statement's "agrees in
  value" = the computed dv2-value, the corpus idiom of GENTOW-5(a)
  ("a computed dv2-value is LIFT-STABLE"), and the proof line
  disambiguates one sentence down — no finding. The p_j = slot-min
  identification is the dev-representation valuation exactness;
  availability at partial sides cited to GENTOW-4.A(ii). Fresh
  stress: congruence + in-window valuations + p_4 = 5 stable on 8
  random 3³-lifts; undercut moved p_3 from 15 to EXACTLY 12 =
  e1e2·N touching only slot (3,0,0).
* **(c) the c_g-correspondence:** substitution of (b) into the
  displayed block/f height translation (HE6R1-2(b) + COR
  GENTOW-4.C); the c_g self-stability parenthetical is sound
  (c_g = p_{mu2*} is itself a slot-min; m >= 0 ⟹ c_g <= m + c_g
  < e1e2·N). **Conditionality displayed at both sites** ("the
  latter at GENTOW4's 0/2 attempt grade — conditional, named" in
  the (d) rider; "conditional" in 6.4(c)). AS-OF adjudication:
  GENTOW4 @ HEAD = 1/2 (passPE2 CLEAN + rider, arc open), so the
  dated "0/2" grade-number is stale in the conservative direction
  while the conditionality claim itself remains true either way —
  per the as-of rule the display stands; no finding.
* **(d) consumption:** COR 6.2C(d)'s window sentence ("caps
  consulted block heights at e1e2·N − c_g") = exactly 6.4(c)'s
  strength; GENTOW-5(b)–(e) consumed only at f_S on 𝒯* (in scope
  via LEMMA 6.2); nothing narrows; the (d) display reads verbatim
  as sealed with the citation-of-record rider in place.
* **BLOCK-STAB redundancy (PE2's observation) ADJUDICATED:** the
  observation is arithmetically correct — the runner's block-pin
  stability rows are implied by PIN-STAB + the constancy of c_g
  (itself among the checked pins). Redundant-but-harmless: the
  note claims no independent evidence from those rows; the
  independent block-side content is carried by the preregistered
  pin VALUES through the c_g-displacement (FRAME-P (26,·,5) =
  (2E2+1+c_g, ·, c_g)), by PE2's fresh projection row, and by this
  pass's pins (53,37,25,15,5) with c_g = 25 = p_2. Not a finding;
  no note edit owed.

## BOX FENCES AT ACCEPTANCE (charge 3)

* **GENTOW6-BOX-1 (mu2 >= 3): HONEST.** Theorem scoped to mu2 = 2
  at every display incl. the rider-folded summary sites; grep
  finds no mu2 >= 3 consumption; the box's "LOOKS uniform" stays a
  flagged temptation.
* **GENTOW6-BOX-2 (count LEDGER): HONEST.** The product-measure
  pricing is named open at S2 and S5 and consumed nowhere; the
  budget half's closure claims only the per-block layer.
* **GENTOW6-BOX-3 (regime-3): HONEST.** 6.3(d) and quadrichotomy
  clause (3)/(3') stay display-only; E-ENTRY remains a
  PARI-adjudicated construction, no theorem claimed.
* **GENTOW6-BOX-4 (f1 >= 2 / eta != 1 machine leg): fence intact,
  text stale = F-1.** Nothing consumes 6.3'; the box's ask (a
  battery-grade leg) is still owed; only the "no contact" census
  sentence has gone conservative-stale.
* Nothing outside the boxes consumes box-interior content
  (grep-walked: mu2 >= 3, product-measure, 6.3', regime-3
  attainment).

## FREE HUNT (charge 4) — clean charges

* Record sentences in the rider additions: enumerative only
  ("GREEN 24/0 at the three S6.2 frames", "across 56 perturbed
  members"); no universal quantifier found in any record sentence
  added since PE2.
* Statement fence: the rider diff inserts brackets and re-scopes
  two summary sites only; every sealed statement display
  byte-untouched; brackets govern without weakening (the codomain
  correction restricts (a)'s image claim to what its proof
  delivers — nothing downstream strengthens).
* S6.5's "load-bearing sites already pinned at r1 and untouched"
  — verified in the diff.
* Cross-note: GENTOW3's consumer walk cites GENTOW-3(i) + BOX-1
  framing only; PROJECT_STATE B14–B16 records carry the pinned
  scope; no stale ungoverned consumer found outside the note.
* 6.4(b) "agrees in value and residue" wording probed and cleared
  (see cap-lemma walk).

## MACHINE LEG

* **Seals:** the six S6.4 md5s re-verified byte-identical at HEAD
  (checks 121e5c4a…/1bcb950…, pe1_fresh 59fe76c…/9de6132…,
  caplemma bf953a8…/fa9d7bf…); rider artifacts present
  (gentow6_rider_codomain.py 2cde0eac…, output b952e97d…); the
  post-PE2 diff touches nothing else in verification/.
* **Isolated re-runs (fresh /tmp dir, this pass):** five for five
  GREEN — caplemma 303/0 (BIT-IDENTICAL), rider codomain 24/0
  (BIT-IDENTICAL), pe1_fresh 22/0 (BIT-IDENTICAL), pe2_fresh 213/0
  (BIT-IDENTICAL), sealed battery 401/0 (identical modulo the
  known environmental gp stack-size stderr line + timing suffix,
  as at PE1/PE2).
* **Tautology audit (rider leg):** digits via iterated division
  vs reconstruction via independent multiplication; forced-zero
  claims tested under perturbation (P-R4), not inferred from
  P-R3; T-COD leaves the member set by degree — real teeth.

## FRESH ROUTE (charge: disjoint from PE1/PE2 legs) — GREEN 61/0,
## 6/6 teeth; run 1 RED kept

Instrument `verification/openmath/gentow6_pe3_fresh.py` (own
exact-integer core, no sealed-runner imports; gp/PARI decorrelated
oracle; predictions preregistered in the docstring; seal commit
before first run, md5 b06e61f2). **Run 2 GREEN — 61 checks, 0
violations (T-GAUGE x2, T-COD2 x2, T-CERTV2 x2); isolated re-run
BIT-IDENTICAL. Run 1 RED kept** (gentow6_pe3_fresh_output_run1.txt):
one verifier-side prereg arithmetic slip — the S/Phi2_C resultant
TOTAL written as 5 where per-root 5 × 2 conjugate roots = 10;
hand-traced (27⁴ − 243 = 531198 = 2·3⁵·u), the per-root floor
value 5 = E2_C/4 exactly as predicted; no content prediction
changed.

* **LEG A — THE GAUGE-LIVE TIE (first η ≠ 1 tie frame anywhere;
  PE2's suggested surface).** Q3, Phi' = x²−6 (e1 = 2, f1 = 1,
  h = 1, η = res(x²/3) = 2 ≠ 1 — every prior tie frame had η = 1
  per the S5 GAUGE AXIS row). Slope-5/2 mixed side, TWO classes of
  distinct degree: L (Phi2_L = Phi'²−9x, ψ_L deg 1, m_L = 2 via
  g1·g2 = (Phi2_L+27)(Phi2_L+81)) and C (Phi2_C = Phi'⁴−243, ψ_C
  = T²+1 deg 2 irreducible, m_C = 1), plus a live sibling
  (Phi'−27). The coherent wrap was hand-derived from the graded
  algebra (X² = 2P): w_k = carry count, (0,0,1,1,2) on f's side.
  Results, each preregistered: level-1 hull (0,26)-(1,20)-(9,0);
  raw digits d = γ·(1,2,1,1,1); monicized R_coh(f) =
  (T+1)²(T²+1) = ψ_L²·ψ_C EXACTLY — Step II/III's (MULT)+UFD
  display at η ≠ 1; composed reads mu2*(L) = 2 = m_L and
  mu2*(C) = 1 = m_C with pins (53,37,25,15,5)/(49,25,5) exact —
  **LEMMA 6.1's tie, gauge-live, both classes**; PARI: all three
  keys irreducible, factorpadic degrees {2,4,4,8}, class degree
  sums 8 = D2_L·m_L and 8 = D2_C·m_C via resultant valuations
  (12/16/48), cross-exclusions EXACT AT the floors (per-root 5
  and 5/2, the g_i/Phi2_C exclusion decided by residue arithmetic
  2+2 = 1 ≠ 0 mod 3). **T-GAUGE tooth fired both ways:** the
  η-blind residual (w ≡ 0) grows a root at T = 1 while
  (ψ_L²ψ_C)(1) = 2 — the wrap units are load-bearing at this
  frame; an η-blind reader breaks exactly here.
* **LEG B — the rider codomain + LEMMA 6.4 at the fresh member.**
  The deg-18 member on TWO grids: D2 = 4 (above-top count 1) and
  D2 = 8 (above-top count 5 — a new value of the bracket's
  D2−1−(n mod D2) formula): census, reconstruction, forced
  zeros + top pin, T-COD2 off-degree on both grids; TRI diagonal
  across 36 perturbations; band-1 on 8 seeded lifts with p_4 = 5
  stable below cap 12; undercut 15 → 12 = e1e2·N exactly, single
  slot touched; c_g = p_{mu2*} = 25.
* **LEG C — the first η ≠ 1 certificate row, at the in-coordinate
  top corner.** Genre (e2,f2) = (2,1), u2 = 5, Phi2 = Phi'²−9cx,
  f = Phi2², c ∈ {1,2}: 2i_0 = 2 = D' (the regime-2 boundary),
  certificate slot (j*,a*,b*) = (0,0,1) with b* = e2f2−1 — the
  corner OPPOSITE PE1's (0,0) quotient-transfer corner. Hand-
  derived and machine-matched: dev(Phi2²) = Y⁴−18cxY²+81c²Y+486c²
  (single x-carry), honest read DRAIN, shadow Ĝ₂ = 1, Ĝ₁ = 0,
  Ĝ₀ = 81c²·Y exactly: digit 81c², v = 4 = 2a_{t*}, unit ≡ c²
  (wrap unit 1 measured), height 16+5 = 21 = THETA_0 — attainment
  ON the floor at an η ≠ 1 frame (the S5 exposed face "S3 digit
  VALUES at eta != 1" gets its first contact, and 6.3(b)'s display
  held). T-CERTV2: swapped-slot (1,0) empty; v and height mutants
  fail. Both keys PARI-irreducible.

Artifacts: gentow6_pe3_fresh.py (md5 post-run-1-fix
0ef76baa4aca861c8dc823520f9459a0; sealed b06e61f2 pre-run) ·
gentow6_pe3_fresh_output.txt (5e97d42e…, exit 0) ·
gentow6_pe3_fresh_output_run1.txt (f8d74ba6…, the kept RED).

## GRADE LINE

**CLEAN: 0 CRITICAL, 0 GAP, 1 MINOR (F-1, stale-conservative
BOX-4/S6.1 machine-contact sentences — unconsumed, one-bracket
fold). Nothing GAP-or-worse survives ⇒ the counter advances
1/2 → 2/2: GENTOW6 ACCEPTED (2 consecutive clean passes).** The
note's load-bearing content — the mixed-side tie (now exercised
gauge-live), the block budget layer, the f1 = 1-scoped attainment
certificate with its honest annex and boxes, and the 𝒯-free cap
lemma — survived three hostile passes, two of them with fresh
out-of-battery instruments, and every repair in the arc was
re-derived at source. F-1 can ride to the acceptance fold
(sibling-arc pattern); it does not hold the counter.

Verifier: GENTOW6 passPE3 (fresh context, zero prior stake).
