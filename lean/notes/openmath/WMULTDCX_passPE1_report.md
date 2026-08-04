# WMULTDCX-PE1 — first hostile content verification pass (fresh context)

Object: `lean/notes/openmath/WMULTDCX_2026-08-08.md` at commit **9bec735**
(confirmed via `git log -1 --format=%h -- <file>`).  Charge: verify the
row-11c refutation, the W-D1..W-D7 chain, the (SURV-(m+1)) box, grades +
fences, and the machine legs.  Role: verify only; nothing fixed.
Independent instrument written for this pass:
`verification/openmath/wmultdcx_pe1_ext.py` (NEW file; committed referees
consumed read-only, never mutated).

Verifier's independent legs (summary; details in the findings and the
machine section):

* **Fresh re-implementation** of: the γ eq-(12) split (brute-force digit
  search), the anchors, the u-chain, the pools/carries (from the S6.1
  display), the two-stage E1-priority promotion-profiled tree (from the
  S2.2 child inventory; breadth-first, separate bookkeeping), the
  profile-part sums, and the W-D4/W-D6/W-D6c per-cell checks.  Engine
  primitives (polynomial ring ops, Φ-tower, Ĉ_m, d-cells, digit split,
  correction table) consumed from the committed engine as shared object
  language; every canonical division INDEPENDENTLY verified by
  re-multiplication (Q·Φ + R == input, deg R < deg Φ).
* Run on the EXACT sealed 412-row selection (keys read from the committed
  stress results JSON, never recomputed): **my divergence set equals the
  sealed 72 records EXACTLY** (tower, key, level, maxnz, c — set equality).
* 8 chosen instances re-derived in detail (both sealed "+2" witnesses,
  both "sharpest" pc₂ = 3 > L-CAP witnesses, one g₀ = 2, one d₀ = 2
  replica, one m = 4 flat, one small tower with a full hand-audited edge
  trace) — all CONFIRMED.
* Hand derivation (no machine) of the W3FMID (95,95) divergence: u-chain,
  pools, carries, the 28-edge two-stage tree, the LED_l ledger on both Q¹
  cells, and the beyond-floor nonzero part — reproduced below in finding
  V1.  It confirms the sealed record exactly.

---

## Part A — positive verifications (what survived hostile checking)

### V1. THE REFUTATION of row 11c is SOUND (charge item 1)

The sealed claim: 72 instance-keyed PID-MAX divergences — nonzero
promotion-profile parts of Q¹ at pc_l = c_l + 1 (twice +2), i.e. RM-GEN
S8 row 11c ("the maximal promotion count into level l is
⌊pool_l/e_{l−1}⌋") is false as an upper bound on surviving mass.

**JSON layer re-read (5+ records):** `wmultdcx_stress_results.json`
`pid_divergences` holds exactly 72 records, all family PID-MAX, spread
over 17 towers (g₀ = 1 and 2, m = 3 and 4, Z₃/Z₅/F₂[[t]], flats
included) — matching the note's S0 census.  Gap distribution
maxnz − c: 70 at +1, 2 at +2 (W3DEEP4 (1263,1271) level 1: 3 > 1;
W3TRK1 (327,335) level 1: 3 > 1) — "twice +2" verified.  Sharpest
witnesses as displayed: W3TRK1 (335,335) and W3G2A (687,687) carry
nonzero parts at pc₂ = 3 > 2 = c₂, above the L-CAP constant 2.
Physical promotion depth up to 4 across the battery (maxpc_all) —
"physical depth up to 4 > L-CAP's 2" verified.  All 72 records join to
LIVE rows in the per-tower `pid` records (0 on dead rows) — the stress
S5 "all 72 divergences sit on live rows" verified.

**Independent re-derivation (my instrument):** on the identical 412-row
selection my freshly written two-stage tree reproduces 412 rows, 858 Q¹
cells, 286 live rows, and a divergence set (nonzero part with
pc_l > c_l) that is **set-equal to the sealed 72**.  Chosen-instance
confirmations (all "MY verdict: CONFIRMED" in the run log):

| tower | key | sealed claim | my maxnz | my cs | live |
|---|---|---|---|---|---|
| W3FMID | (95,95) | lvl 1: 2 > 1 | [2, 1] | [1, 1] | yes |
| W3DEEP | (659,667) | lvl 1: 2 > 1 | [2, 1] | [1, 1] | yes |
| W3DEEP4 | (1263,1271) | lvl 1: 3 > 1 (+2) | [3, 2] | [1, 2] | yes |
| W3TRK1 | (327,335) | lvl 1: 3 > 1 (+2); lvl 2: 3 > 2 | [3, 3] | [1, 2] | yes |
| W3TRK1 | (335,335) | lvl 1: 3 > 2; lvl 2: 3 > 2 | [3, 3] | [2, 2] | yes |
| W3G2A | (687,687) | lvl 2: 3 > 2 | [2, 3] | [2, 2] | yes |
| XM3B | (1055,1055) | lvl 1: 1 > 0 | [1, 1] | [0, 1] | yes |
| W4FLAT | (399,399) | lvl 2: 3 > 2 | [1, 3, 2] | [1, 2, 2] | yes |

**Hand derivation, W3FMID (95,95)** (reads (e,h,g) =
(2,1,1),(1,1,1),(2,1,2 top),(2,1,1); m = 3; P = [2,1,2]):
γ₁ = 1, γ₂ = 1·2+1 = 3, γ₃ = 2·3+1 = 7, γ₄ = 2·14+1 = 29.
u₃ = 29, s₃(29) at (2,1): 29−1 ≡ 0 mod 2 ⟹ s₃(u₃) = 1,
u₂ = (29−7)/2 = 11; s₂(11) at (1,1) = 0, u₁ = 11; s₁(11) at (2,1) = 1.
Split of γ = 95: s₄ = 1 (u = 47, b = 47−14 = 33), s₃ = 1 (u = 16,
b = 16−3 = 13), s₂ = 0, s₁ = 1, u₁-tail = 6.  Pair (95,95): σ = (2,0,2),
TRACK (s₄ = s₄′ = e₃−1 = 1).  Pools: pool₁ = 2+1 = 3, c₁ = ⌊3/2⌋ = 1;
pool₂ = 0+0+1 = 1, c₂ = ⌊1/1⌋ = 1 (e₁ = 1, flat).  D = 2+1 = 3,
k = 4−3 = 1; law clause 3+1 ≥ 4 — live.  The full 28-edge trace (dumped
by my instrument) yields exactly 2 Q¹ cells:
A: sign +, j = [1,0,0], pc = [1,1,2], dmp = 0, principal d-cell;
B: sign −, j = [0,0,0], pc = [2,1,2], dmp = [1,0,0], ncorr = [0,1,0],
principal d-cell.  Cell B is its own singleton part at pc₁ = 2 > c₁ = 1
and its polynomial is a nonzero monomial cell (w₀ = 18) — a NONZERO part
beyond the floor.  Ledger hand-check on B, all three levels:
l = 0: 0 = 2 + 1 + 0 + 1 − 4 ✓; l = 1: 0 = 0 + 0 + 2 + 0 − (1+1) ✓;
l = 2: 0 = 2 + 1 + 1 + 0 − 4 ✓.  W-D4 on both cells: π₂ = 1 = k + 2r +
j₂ with r = 0, j₂ = 0 ✓.  The divergence is real, and it rides the dump
channel (dmp₀ = 1 from a level-1 correction) exactly as W-D6c derives.

**Instrument legitimacy (is it measuring what row 11c asserts?):** yes.
Row 11c's "maximal promotion count into level l" is a statement about
the S2.2 E1-priority tree; the instrument takes the max over NONZERO
profile parts (surviving mass), which is the CHARITABLE reading — a
nonzero part at pc_l > c_l implies a fortiori that tree paths exceed the
floor, so the refutation kills both the surviving-mass reading and the
weaker all-paths reading.  The seeding is pinned by W-D1 (see V2).  The
stage-1/stage-2 reassembly into the canonical divisions (checked by my
instrument with re-multiplied divisions on all 412 rows) ties the part
decomposition to Q¹ exactly.

**Verdict on charge 1: the refutation is SOUND; REFUTED-as-literally-
worded stands, independently reproduced.**

### V2. The W-D chain — each lemma re-derived (charge item 2)

* **W-D1 (seed identity).**  â and â′ are literally monomials
  π^{u}∏Φ_l^{s}; their product is the monomial cell X₀ with b = π^{u+u′},
  j_{l−1} = σ_l.  This is a polynomial identity, not a convention; my
  instrument asserts â·â′ == cellpoly(X₀) on ALL 412 rows — 0 failures.
  The disclosed alternative (Φ-adic re-development) genuinely
  redistributes exponent mass, so the caveat discharge is correct.
  SOUND.
* **W-D2 (u-chain + inventory).**  (0) integrality: eq-(12-int) gives
  u_l − s_l(u_l)h_{l−1} ∈ e_{l−1}ℤ and γ_l − h_{l−1} = e_{l−1}w_{l−1}Φ_{l−1}
  — correct.  Nonnegativity: see finding G2 (minor gap — the displayed
  argument consumes principal-cell existence).  (i) at g_{m−1} = 1:
  reduced gives j_{m−1} ≤ e_{m−1}−1 (needs g_{m−1} = 1 so that
  P_{m−1}−1 = e_{m−1}−1), on-grid gives the congruence — the top pin is
  exactly where (H2) is consumed, consistent with the class pins (all 20
  battery towers have g_{m−1} = 1).  (ii)–(iv): the on-grid forcing is
  right; machine-checked at g₀ ∈ {1,2} only, exactly as F4 discloses.
  The four g₀ = 2 towers: 2 d-cells each, principal PRESENT, ψ₀ pattern
  (1,1) — verified in the committed inv records.  SOUND modulo G2.
* **W-D3 (ledger LED_l).**  Re-derived from the S2.2 child inventory,
  child type by child type: promotion at i moves (j_i, j_{i+1}) by
  (−P_i, +1) → cons_i += P_i, π_{i+1} += 1; exit moves j_{m−1} by
  −P_{m−1} → cons_{m−1}; correction (k,d) at i moves j_i by −(P_i − e_ik)
  → cons_i, adds a_{d,l} at l < i → dmp_l, +1 at l = 0 on the Y child
  → dmp₀; L/X children change no exponent; stage-2 seeding adds j(D)
  (+1 at l = 0 on Y → dmp₀); seed contributes σ_{l+1}.  EVERY child type
  of the S2.2 inventory (and of both committed tree codes) is covered;
  signs correct; no other edge type exists.  Hand-verified on W3FMID
  (above) and machine-verified by MY bookkeeping on all 858 cells ×
  all levels — 0 failures.  SOUND.
* **W-D4 (top threshold, cellwise).**  Specialization checked:
  dmp_{m−1} = 0 (corrections dump strictly below their reduction level;
  no reduction level exceeds m−1; Y-dumps land at level 0) — correct;
  j_{m−1}(D) = s_m(u_m) by W-D2(i) (H2); cons_{m−1} = (2+r)e_{m−1} at
  g_{m−1} = 1 (two exits, k = 0 the only correction index — both facts
  need exactly (H2)); j ≥ 0 throughout the tree (every subtraction is
  guarded by j ≥ P).  Rearrangement gives π_{m−1} = k + e_{m−1}r +
  j_{m−1} ≥ k exactly.  My instrument re-checked the identity AND the
  inequality on all 858 cells with MY counters — 0 failures.  The
  upgrade from parts to cells is genuine (a cellwise identity).  SOUND.
* **W-D5 (line floor).**  Per-edge line laws are consumed from accepted
  RM-GEN S3.2 rows (in-scope citations); the assembly (sum over edges,
  q_{m−1} = h_{m−1}, π_{m−1} ≥ k from W-D4, w_m of a digit sum ≥ min
  line, exit cofactors are top-single digits per the S2.2 structural
  remark — quoted correctly) is arithmetic and checks out.  Machine:
  floor 0/858, junk-free equality 0/801, weight floor 0/286 live rows —
  the note's brackets state these scopes honestly.  Depth-0 existence on
  direct rows: σ_m ≥ e_{m−1}+1 forces a promotion-free two-exit path
  (corrections exist at every level since C₀ = Φ_{i+1} − Φ_i^{e_i} ≠ 0,
  L-children never vanish, dumps go strictly down, the top is untouched
  by lower reductions) — SOUND as an existence-of-cells claim, and the
  note correctly leaves residue survival to S9.
* **W-D6 (dump-free cap).**  The derivation from LED_{l−1} (dmp = 0,
  principal j(D) = s_l(u_l) — which holds for the t⃗ = 0 cell g-free;
  cons_{l−1} ≥ π_l P_{l−1}; j ≥ 0; floor-monotone induction) is correct,
  and ĉ_l ≤ c_l always (P ≥ e).  My instrument re-checked the cap with
  my own counters on all dump-free principal cells — 0 failures.  SOUND.
* **W-D6c (excess channels).**  Valid contrapositive of W-D6.  My
  instrument: all 112 beyond-floor cells (count matches the committed
  112) carry a dump or a non-principal d-cell — 0 exceptions.  Every
  nonzero part beyond the floor is a sum of beyond-floor cells, so the
  mechanism claim for the 72 is genuine.  SOUND.
* **W-D7 (cascade).**  (i) a_l + b_l = c_l is the standard carry-split
  identity: with σ_l + a_{l−1} = e·a_l + r_l, ⌊(σ_l + s_l(u_l) +
  a_{l−1} + b_{l−1})/e⌋ = a_l + ⌊(r_l + s_l(u_l) + b_{l−1})/e⌋; base
  c₀ = a₀ = b₀ = 0.  Algebraically verified; machine 302/302.
  (ii) legality: E1-priority forces all lower-level pumping to complete
  before a level fires, so the pump totals are exactly the a_l (stage 1)
  and b_l (stage 2); the second-exit condition (σ_m + a_{m−1} − e_{m−1})
  + s_m(u_m) + b_{m−1} ≥ e_{m−1} rearranges via (i) to D + c_{m−1} ≥
  2e_{m−1} verbatim.  The IFF is genuine BOTH WAYS **for the greedy
  path itself** (deterministic bookkeeping: if the total top stock
  misses e_{m−1} the path leaves a reduced leaf, no second exit).
  (STK) is honestly explicit (F6) and honestly NOT derived from TRACK.
  (iii) two-sidedness: see finding G1 — the equality needs the law
  clause as well; only the achievability hypothesis (STK) is displayed.
  SOUND modulo G1.

### V3. The box and the assembly (charge items 3, 4)

* (SURV-(m+1)) is stated precisely: both directions displayed as (i)
  survival and (ii) cancellation, quantified over TRACK on (H1)–(H2) in
  the S1 class/window.  I verified the equivalence claim: on TRACK the
  locus clause of the measured side is automatic (Tsum = 2e_m − 2 gives
  ⌊Tsum/e_m⌋ = 1 at e_m ≥ 2; the e_m = 1 branch matches), so
  law ⟺ (Q¹ ≠ 0 ⟺ c_{m−1} ≥ k) ⟺ (i)+(ii) — "EXACTLY LAW-DCX-(m+1)
  minus this note's proved layers" is right.
* Nothing graded PROVED consumes (SURV): checked every W-D proof and
  the PID† assembly — the S4 census (minnz = k, 286/0) and the S5
  depth-0 remark are explicitly marked as inputs to S9, not claims.
* The meta-claim "provably NOT closable by mass arguments": see finding
  C1 — the (ii) leg is REFUTED by the committed artifacts themselves.
* Grades/fences sweep: row 11c stays REFUTED (no silent upgrade — the
  RM-GEN table is untouched and PID† is presented as a new, corrected
  statement); LAW-DCX-(m+1) row and F5 keep the law at m ≥ 2 conjecture
  — genuinely unchanged; (H2) consumption sites match F1; F2/F3/F4/F6/F7
  match the proof bodies (F7's "uniform in m" is fair: the displayed
  proofs are general-m arguments; instances are m ∈ {2,3,4}).  Header
  "PROVED at attempt grade ... 0/2 hostile passes" is honest.

---

## Part B — findings (quote-and-classify)

### C1. CRITICAL ERROR — the S9 "obstruction" paragraph asserts, as derived, a claim its own cited evidence CONTRADICTS on the (ii) leg

Quote (S9):

> **Why (i)/(ii) cannot be closed by mass arguments (the exact
> obstruction, now derived, not just measured):** for (ii) —
> beyond-floor cells EXIST (W-D6c channels; 112 in the battery, 72
> sealed nonzero parts), so deadness at c_{m−1} < k is a cancellation
> phenomenon, not path non-existence; ...

My derivation.  The cited populations sit ENTIRELY on live rows: (a) by
direct census of the committed `wmultdcx_derive_checks_results.json`,
the 126 dead traced rows carry **0 Q¹ cells** (858/858 cells are on the
286 live rows), so 0 of the 112 beyond-floor cells are on dead rows;
(b) the sealed stress JSON agrees (0 dead traced rows with any nonzero
part; all 72 divergences live); (c) my independent instrument
reproduces both counts (beyond-floor on dead rows: 0).  Note also that
on a dead TRACK row every Q¹ cell would automatically be beyond-floor
at the top (W-D4 forces π_{m−1} ≥ k > c_{m−1} there), so "0 beyond-floor
cells on dead rows" IS "0 Q¹ cells on dead rows".

Consequences.  (1) The inference "beyond-floor cells EXIST ⟹ deadness
is a cancellation phenomenon" is invalid: the exhibited beyond-floor
cells live on rows where the law clause HOLDS; they say nothing about
clause-failing rows.  (2) Worse, the assertion "not path non-existence"
is contradicted by every probed instance: on ALL 126 traced dead rows
(which include the hunted just-miss/deficit-edge dead strata) deadness
is EXACTLY path non-existence — zero two-exit paths — so the entire
available instance evidence is CONSISTENT with (SURV-(m+1))(ii) being
closable by a pure path-non-existence (mass/combinatorial) argument.
(3) The header "now derived, not just measured" is wrong on both legs:
for (ii) nothing is derived (and the measurement points the other way);
for (i) at g₀ ≥ 2 the derived part is only the conditional mechanism
(W-D6's P₀-divisor cap), while the existence of live rows at
pool₁ < P₀ is the sealed m = 2 record — measured.  The upstream stress
S5 phrasing "on every DEAD row the beyond-floor promotion mass cancels
TOTALLY (zero nonzero parts at ANY depth)" was already vacuous (there
are no parts at all on the traced dead rows); this note upgraded that
vacuous phrasing into a positive structural claim.

Classification: CRITICAL ERROR, scoped to the S9 obstruction paragraph.
It breaks nothing in W-D1–W-D7/PID† (no PROVED-graded item consumes it),
but it is a false assertion presented as derived, and it materially
mis-frames the boxed residual: (ii)'s difficulty profile ("cancellation
of signed recycled families") is asserted where the data shows
path-scarcity.  The paragraph's honest content would be: for (ii), a
mass-conservation UPPER bound at the floor is unavailable (the 72 live
witnesses kill it), but a path-non-existence route to (ii) is NOT
excluded — on the battery it is exactly what happens.

### G1. JUSTIFICATION GAP — the two-sided identification (S0, S8(b), W-D7(iii)) omits the law clause from its displayed hypotheses

Quotes:

> (S0) the floor c_l = ⌊pool_l/e_{l−1}⌋ is the exact maximum of the
> promotion count on the DUMP-FREE PRINCIPAL subtree (two-sided there,
> W-D6+W-D7)

> (S8(b)) **dump-free identification, two-sided [W-D6 + W-D7; (H3) ∧
> g₀ = 1; the achievability leg under (STK)]:** max π_l over dump-free
> principal Q¹ cells = c_l = ⌊pool_l/e_{l−1}⌋ — row 11c verbatim, on
> exactly this subtree.

> (W-D7(iii)) With W-D6: **the maximum of π_l over dump-free principal
> Q¹ cells equals c_l — the corrected two-sided pool identification.**

My derivation.  The only displayed maximizer is the greedy terminal
cell of W-D7(ii), which EXISTS iff (STK) ∧ (D + c_{m−1} ≥ 2e_{m−1})
(the second-exit iff).  On clause-failing rows the note proves only the
one-sided cap π_l ≤ c_l (W-D6); nothing shown guarantees the dump-free
principal part of Q¹ is nonempty there, let alone that it attains c_l —
and indeed on all 126 traced dead rows there are NO Q¹ cells at all, so
"max π_l" there is a maximum over the empty set.  S8(b) displays
"(H3) ∧ g₀ = 1" and "(STK)" but NOT the clause; the S0 reconciliation
sentence and the "true verbatim on the dump-free principal subtree"
line display no condition at all.  No battery instance contradicts the
equality where defined (all 302 all-g = 1 traced rows satisfy (STK),
and every live one satisfies the clause), so this is a display/scope
gap, not a refuted claim.  Repair: state (b) as "π_l ≤ c_l always
[(H3) ∧ g₀ = 1], with equality attained by the cascade cell whenever
(STK) ∧ D + c_{m−1} ≥ 2e_{m−1}".

Classification: JUSTIFICATION GAP (hypothesis under-display on a
PROVED-graded assembly clause; PID†(b) and two S0/S8 display sentences
affected; the underlying lemmas W-D6/W-D7 are sound as stated).

### G2. JUSTIFICATION GAP (minor) — W-D2(0)'s nonnegativity argument consumes principal-cell existence without citing it

Quote (S2, W-D2 proof of (0)):

> Moreover u_l ≥ 0: by RM-GEN S2.1 every cell of Ĉ_m is reduced,
> ON-LINE at γ_{m+1} and ON-GRID; by L-GRID the λ-chain values of the
> principal cell (t⃗ = 0 below) are its truncation lines, hence
> ∈ ℤ_{≥0}, and these values ARE the u_l.

My derivation.  The displayed argument presupposes that a principal
(t⃗ = 0) d-cell EXISTS.  At interior g ≡ 1 with g₀ = 1 it is the only
cell (forced); at g₀ ≥ 2 its existence is exactly what fence F3 admits
is "a certified input (present on all battery towers), not derived".
So as displayed, (0)'s nonnegativity leg rests on F3 at g₀ ≥ 2, but
neither the proof line nor the W-D2 claims-table row carries the F3
pin.  Repairable without F3 under the note's own (H3): every d-cell's
λ-chain equals the u-chain down to level 1 (level-0 t-freedom does not
touch λ_{l}, l ≥ 1), so u_1..u_m are truncation lines of ANY d-cell,
and Ĉ_m ≠ 0 supplies one.  (u₀ appears only in (iii)/(iv), where
nonnegativity of the coefficient weights is automatic.)  The battery
verifies u ≥ 0 outright (STRUCT leg).

Classification: JUSTIFICATION GAP, minor (mis-attributed dependency;
a correct scope-free repair exists and is one line).

### N1. NOTE — the (STK) census denominator is described loosely

Quote (W-D7 machine bracket): "(STK) census: 302/302 traced TRACK rows
satisfy it"; F6: "census 302/302 on the battery's traced TRACK rows".
The census ran only inside the all-g = 1 guard: 302 = the traced rows
on the 16 all-g = 1 towers; the 110 rows on the four g₀ = 2 towers were
never stock-censused.  Content unaffected (W-D7 is (H3) ∧ g₀ = 1-scoped
anyway), but "traced TRACK rows" reads as all 412.

### N2. NOTE — LED_l machine coverage is terminal-cell-only

W-D3 claims the ledger "along any root-to-node path ... for every
level"; the machine bracket honestly states its scope ("858 Q¹ cells ×
all levels"), i.e. terminal cells only.  The edge-by-edge proof covers
interior nodes, and my hand trace verified interior bookkeeping on
W3FMID, so this is a coverage remark, not a defect.

---

## Part C — machine section (charge item 5)

* **Pins.**  `wmultdcx_derive_checks.py` md5
  bea1a43d619a3c91a9a0b2f32c0920c0, output
  2b5395adca632fa0c2e3564db12e668d, results
  000ac228dc4aa4ea6309cf24d0a648ec — all three MATCH the note's S0 and
  dependency-line pins.  Stress chain: runner
  15315cca59c87e6c2001ea744c50aab5, output
  2ff1cdc7a80a0cc19b8a1cc20999194c, results
  41cbf2f1939d1a1548c0f5784a5cb3e8 — MATCH the stress note's S5 pins.
  The results JSON's internal provenance block matches the on-disk
  `rmengine_pe_reimpl.py` / `grb_order2_check.py` md5s.
* **Read-only re-run.**  `wmultdcx_derive_checks.py` re-executed in a
  sandbox COPY (/tmp/pe1_rerun; committed artifacts untouched, verified
  by md5 above): all 11 DCK families GREEN [0 violations], 412 rows,
  858 cells, 112 beyond-floor, 801/858 junk-free, minnz census 286/0,
  stock 302/0, greedy 218, output IDENTICAL to the committed output
  modulo timing, results JSON IDENTICAL modulo `elapsed`.
* **Selection tie.**  The 412-row selection in the derive battery is
  per-tower key-set IDENTICAL to the sealed stress battery's `pid`
  records — "the 412 rows here ARE the sealed battery's 412" verified.
* **Independent instrument.**  `wmultdcx_pe1_ext.py` (this pass): fresh
  split/anchors/u-chain/pools/tree/parts, divisions re-multiplied;
  results: 72/72 divergence set equality; W-D4 identity+threshold
  0 failures; W-D6 cap 0 failures; W-D6c channels 0 failures;
  112 beyond-floor cells, 0 on dead rows; 286 live rows; W-D1 identity
  0 failures on all 412 rows.
* **g₀ = 2 inventory.**  Committed inv records for
  W3G2A/W3G2B/W3G2P5/XM3B: 2 d-cells each, principal present, ψ₀
  nonzero pattern (1,1) — matches the W-D2 bracket verbatim.

---

## Verdict block

The refutation layer (charge 1) and the W-D1–W-D7 mathematics survive
hostile checking, including full independent replication of the sealed
72 and a by-hand instance audit; the machine legs reproduce exactly.
Two justification gaps (G1 display-scope on the two-sided clause; G2
minor dependency mis-attribution in W-D2(0)) and two notes are
repairable without touching any lemma body.  One CRITICAL error stands:
the S9 meta-paragraph asserts as "derived" that deadness is
"a cancellation phenomenon, not path non-existence", while every
committed artifact (and this pass's independent instrument) shows the
opposite on all 126 probed dead rows — zero Q¹ cells — so the
"not closable by mass arguments" claim for (SURV)(ii) is unsupported
and its displayed justification is invalid.  Nothing graded PROVED
consumes that paragraph, but under the acceptance bar a false
assertion presented as derived blocks a clean pass.

WMULTDCX-PE1 FINDINGS: 1 critical, 2 gaps
VERDICT: NOT-CLEAN
