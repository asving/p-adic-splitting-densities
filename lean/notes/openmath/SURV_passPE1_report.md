# SURV pass PE1 — first hostile content verification (fresh context)

Object: `lean/notes/openmath/SURV_PROOF_2026-08-08.md` at commit 0b895d0
(confirmed via `git log -1 --format=%h -- <file>`).  Verifier: PE1 (Fable,
fresh context).  Charge: quote-and-classify (CRITICAL / GAP / NOTE), fix
nothing; re-derive S-L0–S-L4 + S-THM from the accepted/consumed sources;
re-derive both committed cancellation instances by hand; independent
instrument `verification/openmath/surv_pe1_ext.py` on fresh rows; re-run
the committed machine leg read-only.

## 0. Machine-leg replication (read-only re-run) — IDENTICAL

* All md5 pins CONFIRMED against the note's S0/S10 displays:
  `surv_derive_checks.py` 2365289e1f925404e66c8ce2b3e827ed · output
  d3eb83d286eda103c9210a37361e52cd · results
  12b2ef306dc946ce12d641a828ebca56; consumed runners
  `empty_derive_checks.py` 8fed9240…, `wmultdcx_stress.py` 15315cca…,
  `wmultdcx_derive_checks.py` bea1a43d…, `rmengine_pe_reimpl.py`
  103c1a9c…, `grb_order2_check.py` dab62713… — all match on disk.
* Sandbox re-run (`/tmp/surv_pe1_rerun`, all engine modules copied
  byte-identical): **output IDENTICAL mod timings; results json IDENTICAL
  mod `elapsed`** — 10 verdict families, 0 violations, deterministic as
  disclosed.
* The sealed-phase selection loop (`run_sealed_tower` pid-key double loop
  + cap + sort) was diffed against `empty_derive_checks.py`'s: **byte-line
  identical** (modulo the trace_row signature and the print line), so the
  "selection loop copied byte-faithfully" claim in S0 is accurate; the
  412/858/126 sealed tallies re-add exactly from the per-tower output
  lines (sealed live rows = 286, sealed cells = 858, dead = 126; fresh
  live = 200, total live = 486; total cells 858 + 948 = 1,806).
* Controls: CTRL-MULTI 25 · CTRL-ABOVE 134 (= 57 above + 77 direct, as
  the note's "includes the sub-threshold directs" says) · CTRL-NONCASC
  301 · CTRL-CANCEL 2 — **all fired**, confirmed from the output and the
  json, not just the summary line.

## 1. Committed-census claims re-derived from the committed json

Every instance number in S1/S7/S8 was re-computed independently from
`surv_derive_checks_results.json` (g₀ attribution keyed off the roster
reads, not off any note text):

* partnered cascade slots: 55, **all six g₀ ≥ 2 towers and only they**
  (W3G2A/W3G2B/W3G2P5/XM3B/EQ3G2A/EQ3G2B); killed 52; on ALL 52 killed
  rows the netted bottom survived with w_m(Q¹) = β_min — S7 display 2
  exact.  At g₀ = 1: partnered 0/379 ✓.
* multi-cell netted bottoms: 25, all g₀ ≥ 2 ✓ (MINSTRAT n=2 = 24 thresh
  + 1 above ✓).
* g₀ = 1 same-slot bottom collisions (nmin_raw > nmin_net): **exactly 13
  rows — 11 net to one nonzero cell, 2 net to zero** (W3DEEPF[663,667],
  EQ3T3F[831,835], both p = 2), every one with min_ncorr_tot = {1} (each
  collision cell rides EXACTLY one correction, junk = 0, r = 0) — the S7
  "13 collisions / 11 survive / 2 cancel / every pair rides ≥ 1
  correction" display is exact.
* the p = 3 characteristic witness: W3DEEP[663,667] (same reads
  (3,2,1)(2,1,1)(2,1,1)(2,1,1) as W3DEEPF per the frozen rosters, Zp
  p = 3): nmin_raw = 2 → nmin_net = 1, bottom survives, same c⃗ = (2,1),
  D = 3, k = 1 ✓.
* route-decision numbers (S1): 459 unique netted bottoms; 183 = cascade
  (ALL g₀ = 1, so 377 − 183 = 194 non-cascade at g₀ = 1 ✓); the 194 ride
  1–3 corrections exactly (dist 135/42/17, junk 0 everywhere) — the
  "lazier profiles riding 1–3 corrections" gloss is exact; the 0-corr
  non-cascade bottoms (29 + mixed) sit ONLY on g₀ ≥ 2 towers (the
  t-family), consistent with S-L4(iii)'s uniqueness at g₀ = 1.
* MINSTRAT strata 352/57/77, CTRL-ABOVE 134 ✓; (STK) held on all 379
  g₀ = 1 live rows ✓; allg1 flag agrees with roster g₀ on all 486 ✓.
* Tower displays in S7 checked against the frozen rosters: W3DEEPF =
  (3,2,1)(2,1,1)(2,1,1)(2,1,1) over F₂((t)), d₀ = 1 ✓; EQ3T3F =
  (3,1,1)(2,1,1)(3,2,1)(2,1,1) over F₂((t)) ✓; β_min/survivor
  slot/line values 456/458 and 576/579 with survivor slot (0,1,0) ✓
  from the committed CANCGRADE output lines and json anatomy.

## 2. Upstream-transfer audit (S-L0 sources; the consumed blocks)

Read against `RMENGINE_2026-08-08.md` ([RMG], ACCEPTED),
`WMULTDCX_2026-08-08.md` (attempt, 0/2), `EMPTY_PROOF_2026-08-08.md`
(attempt, 1/2):

* S-L0 def of w_m via the S0.2 mirror recursion: matches [RMG] S0.1/S0.2
  consumption ("consumed as definitions") ✓.  S-L0(a)/(b) are standard
  ultrametric facts, proofs displayed and correct ✓.
* S-L0(c): the [RMG] S2.2 structural remark ("exit cofactors are
  top-single digits... the sub-cell S := b∏_{l≤m−2}Φ_l^{j_l} is REDUCED
  AT LEVEL m−1 (deg S < deg Φ_{m−1}), and the cofactor is a SINGLE
  Φ_{m−1}-digit whatever the top exponent") + L-LINE(iv) ("w_m(C) =
  line(C) EXACTLY" on reduced cells) transfer accurately; the degree
  telescope needs deg b < d₀, which is [RMG] S2.1's cell definition and
  a tree invariant (L-NORM splits keep deg < d₀).  Machine: SDK-DIGIT
  1,806/1,806 ✓.
* S-L1's ρ_l: E-L4's "ρ_l := (t_l + c_{l−1}) mod e_{l−1}" with
  t_l := σ_l + s_l(u_l) (EMPTY S1 abbreviations) = pool_l mod e_{l−1} —
  transfer exact, and re-derived inline in S-L1 as claimed ✓.
* W-D1 (b₀ = π^{u₁+u₁′}), W-D2(i)–(iii) (d-cell exponents forced;
  w₀(b_D) = u₀ at g₀ = 1), W-D3 (LED_l), W-D5 (line law), W-D7(ii)
  (cascade existence/profile/top exponent/line under (STK) ∧ clause):
  all quoted at their true scopes, (H3) ∧ g₀ = 1 pins carried ✓.
  Independent re-derivation of the interior-exponent computation:
  LED_{l−1} with dmp = 0, j(D) = s_l(u_l), π_{l−1} = c_{l−1},
  cons_{l−1} = e_{l−1}c_l gives j_{l−1} = pool_l − e_{l−1}⌊pool_l/
  e_{l−1}⌋ = ρ_l ✓ (l = 1 handled by π₀ = 0, c₀ = 0).
* S-L1's unique-d-cell claim at (H3) ∧ g₀ = 1, any d₀: W-D2(i)+(ii)+(iii)
  force EVERY d-cell's full exponent vector to (s₁(u₁),…,s_m(u_m));
  L-CELL(i)'s development is by DISTINCT reduced cells, so ≤ 1 cell;
  Ĉ_m ≠ 0 supplies one.  Sound; the d₀ ≥ 2 ∧ g₀ = 1 machine hole is
  honestly fenced (F-C) ✓.
* L-NORM(a) transfer at S-L1 (valuation exact, residue = b̄c̄ ≠ 0 in the
  field K₀): verbatim-accurate against [RMG] S2.1 ✓; b̄₀ = 1 since b₀ is
  a π-power ✓.
* EMPTY consumption: ρ_l notation re-derived inline ✓; the E-L6
  mechanism at S-L4(iii) is cited with its one-line degree argument
  (deg b₀ = 0 ⟹ deg(b̂₀ĉ) = deg ĉ < d₀ ⟹ Ŷ = 0 canonically) whose
  pieces sit in accepted [RMG] L-NORM(c) + [IL3]† DIGIT-SPLIT
  canonicity — the "NOT load-bearing" grading of EMPTY is defensible
  (see finding N-2 for the one place it thins).

## 3. Core re-derivations (S-L2, S-L3, S-THM)

* **S-L2 re-derived SOUND.**  H = the other surviving netted slots; each
  netted coefficient is a sum of deg < d₀ coefficients, hence deg < d₀;
  interior exponents reduced automatically at two-exit terminals (the
  S2.2 structural remark applies at the exit, both stages); S-L0(c) is
  top-exponent-free; so w_m(each H-cell) = its line > β_min, w_m(B) =
  β_min, and S-L0(b) closes.  No (RW₀) needed — correctly displayed as
  pin-free.  Machine SDK-SEP 459 + 486 ✓.
* **S-L3 (THE load-bearing step) re-derived SOUND, with the exact
  mechanism checked.**  The feared failure mode — two distinct exponent
  vectors producing the same monomial after reduction — is excluded
  precisely because (i) every terminal coefficient has deg < d₀ (tree
  invariant from L-NORM/DIGIT-SPLIT: lift, X̂, Ŷ all deg < d₀), (ii)
  interior exponents are reduced automatically (E1-priority at the
  exit), (iii) the top exponent is pinned reduced by (RW₀) — displayed
  as an explicit hypothesis, REDWIN 1,806/1,806 instance-clean, and
  correctly listed OPEN at m ≥ 3 in the claims table.  Under (i)–(iii)
  distinct slots have distinct x-degrees (mixed-radix: deg C = deg b +
  Σ j_l deg Φ_l with deg b < deg Φ₀, j_l ≤ P_l − 1, telescoping), so
  L-CELL(i)'s "DISTINCT reduced cells, uniqueness of division" applies
  verbatim: a nonempty signed sum of distinct reduced cells with
  nonzero coefficients is nonzero and w_m = min line.  Every netted
  bottom slot is "genuinely reduced at the exit" in the displayed
  sense: interior automatic + top by pin; coefficient degree preserved
  under netting (sums don't raise degree).  No counterexample found.
* **S-THM(a)/(b)/(c) assembly re-derived SOUND** given S-L1–S-L4(ii):
  (c) uses (NEP) to make the cascade slot's equal-line subsum the
  single S-L1 term (residue ≠ 0 in K₀), S-L4(ii) to survive the
  higher-valuation slot-mates, and (RW) + L-CELL(i) to make the netted
  slot list THE development of Q¹, hence Q¹ ≠ 0.  Note (c) does NOT
  route through S-L4(iii)'s resonance clause — findings below do not
  touch S-THM.
* Pins displayed per lemma ✓ (F-A audited against each statement);
  nothing graded PROVED consumes (NEP)/(RW)/(SURV-DISJ) as facts — they
  enter only as displayed hypotheses of (b)/(c) and are listed OPEN in
  S10 ✓; the grade-cap sentence (everything capped at WMULTDCX's 0/2
  attempt grade) is present in the header, F-E, and the dependency
  line ✓; the null-instrument disclosure is present (S0 + S8(i)) and
  ACCURATE (no dedicated SURV instrument artifact exists anywhere in
  the tree — checked: `verification/openmath/` has only
  `surv_derive_checks.*` for this arc, and no SURV instrument note
  exists in `lean/notes/openmath/`).

[Findings and the independent-instrument results follow.]

## 4. Independent instrument (surv_pe1_ext.py) — the fresh census

`verification/openmath/surv_pe1_ext.py` (md5
937317c75fb381eec96b59b8a1f743ad; NEW file, this pass; consumes the five
committed engines byte-untouched, pins re-checked green; run in the
`/tmp/surv_pe1_rerun` sandbox, outputs kept out of the repo per the pass
charge; deterministic, exact arithmetic).  Three phases; **545 live rows
traced** (the frozen EQ roster at RAISED per-stratum caps 12/6 vs the
committed 6/3, plus a NEW 8-tower PX roster: char-3 Fpt twins of BOTH
committed cancellation shapes, Zp p = 2 twins (residue characteristic 2
in MIXED characteristic), and Fpt p = 2 twins of the other
collision-carrying sealed shapes).  Verdict families PX-PIN / PX-CONS /
PX-DIGIT / PX-LINE / PX-CASC (S-L1's clauses, 478 fresh all-g=1 (STK)
rows) / PX-SEP (S-L2 + the S-L3 instance form): **0 violations** — every
PROVED lemma held on every fresh row, including all new towers.

**(a) Both committed cancellation instances RE-DERIVED BY HAND from the
committed engines** (Phase A dumps, quoted):

* W3DEEPF[663,667] (F₂((t))): raw bottom = TWO cells, slot (0,0,0),
  line 456, BOTH sign −1, BOTH coefficient exactly t³⁸ (w₀ = 38,
  residue 1), each with exactly one correction edge ce = ((0,0,(),0),)
  (level-0, k = 0, dumpless), profile (1,1)+two exits.  Net =
  −(t³⁸ + t³⁸) = −2·t³⁸ = 0 in characteristic 2 — EXACT ZERO.  Netted
  spectrum head = single slot (0,1,0) at 458 = the cascade's slot and
  line; w_m(Q¹) = 458.  The note's display is exact.
* EQ3T3F[831,835]: same anatomy (pair at 576, w₀ = 32, residue 1 each,
  one level-0 correction each), net ZERO; survivor = cascade slot
  (0,1,0) at 579 = w_m(Q¹).  Exact.
* The p = 3 witness W3DEEP[663,667] (identical reads, Zp p = 3):
  IDENTICAL pair anatomy (equal coefficients, w₀ = 38, residue 2 each,
  signs −1,−1), net = −2b ≠ 0 (residue 2·2 ≡ 1 mod 3), slot survives at
  456 = w_m(Q¹).  Raw 2 → net 1 — the characteristic-sensitivity
  reading confirmed: the kill is 2·(unit) ≡ 0 mod p, i.e. mod-p
  arithmetic of a path-multiplicity-2 collision (two interleavings of
  the same correction firing), fatal exactly at residue char 2.

**(b) FOUR NEW total-bottom-cancellation instances found (CANCHUNT), all
residue characteristic 2, all g₀ = 1, all threshold-genre, and on ALL of
them the survivor is EXACTLY the cascade slot at the cascade line:**

    PXT3Z2[831,835]   Zp  p=2  (EQ3T3F reads)  — MIXED characteristic:
                      pair kills at grade (net 2·b, valuation +1: slot
                      resurfaces at 594 = β_min + E_m), bottom DEAD at
                      β_min = 576, w_m(Q¹) = 579 = the cascade line.
    PXDEEP4F[1257,1271] Fpt p=2 (W3DEEP4 reads) — β_min 860 dead,
                      survivor = cascade slot (1,1,0) at 862.
    PXTRK1F[330,335]  Fpt p=2 (W3TRK1 reads) — 564 dead, cascade at 566.
    PXFLTF[123,123]   Fpt p=2 (EQ3FLT reads) — 90 dead, cascade at 93.

  The mixed-characteristic instance sharpens the note's "both
  characteristic 2" framing: the phenomenon is RESIDUE-characteristic-2
  (mod-p), not equal-characteristic — exactly the note's own "sign
  structure mod p" reading, now decorrelated from the Fpt ring.  **No
  p > 2 cancellation exists in the probed class**: the char-3 Fpt twins
  of BOTH committed shapes (PXDEEPF3, PXT3F3, 67 live rows) carry the
  same collision pairs and net NONZERO everywhere (2·res ≢ 0 mod 3).
  (SURV-DISJ) instance record extends: 545 fresh rows + 6 unique
  cancellation rows, ZERO counterexamples — bottom-or-cascade held
  everywhere, and on every kill the minimal survivor was the cascade
  slot AT the cascade line (not merely some slot).

**(c) Same-slot equal-line census (EQLGRP, full multisets, 545 rows):**
377 groups (n up to 6); 58 at the bottom line, 44 killed.  ALL 44 killed
groups have equal residues; sign split: 7 same-sign pairs (ALL residue
char 2 — the committed 2 + the 4 new + 1 Phase-A duplicate) and **37
OPPOSITE-sign pairs, all on EQ3G2B (g₀ = 2, p = 3, the t-family)** —
sign-flip cancellation of equal residues is CHARACTERISTIC-BLIND and
instance-real at g₀ ≥ 2 (on every such row the bottom survived at
another slot; no total kill).  This genre sits inside the note's g₀ ≥ 2
displays and its S7 "not the only cancellation genre" disclaimer, but it
is worth the record: a (SURV-DISJ) proof must handle sign-pair kills
(char-blind) as well as mod-p multiplicity kills.

**(d) Partner anatomy (PRT):** 39 equal-line cascade-slot partners on
the fresh g₀ ≥ 2 rows — ALL junk-free, ALL riding a non-principal d-cell
plus ≥ 1 correction; 0 partners on any g₀ = 1 row (the (NEP) instance
record extends to ~460 fresh g₀ = 1 rows).  MIXJUNK: exactly ONE
same-slot equal-line group with MIXED junk counts anywhere in 545 rows —
EQ3G2A[2321,2321], slot (0,0,0), line 1584, n = 3, junks {1,2}, ncorr
{1,2,3} — cells with DIFFERENT promotion sums Σπ_l q_l sharing a line
via junk-gain compensation.  No group mixing junk = 0 with junk > 0 was
found.  This bears directly on finding G-1 below.

## 5. FINDINGS (quote-and-classify)

**G-1 (GAP, S-L4(iii) + its S5 proof line + the header echo — the
"junk-free forced" inference).**  Quote (S5, proof of (iii)): *"A
partner at the cascade's slot AND line is junk-free with equal quantum
sum by W-D5's exact line law."* and (statement) *"(junk-free forced:
junk gains are strictly positive, W-D5)"*.  W-D5 gives line = λ̂ +
Σ π_l q_l + (junk gains ≥ 0, = 0 iff junk-free).  For an equal-line
partner this yields ONE equation Σ c_l q_l = Σ π_l q_l + J with J ≥ 0,
i.e. only Σ π_l q_l ≤ Σ c_l q_l; concluding J = 0 (junk-free) AND the
resonance equation needs the reverse inequality Σ π_l q_l ≥ Σ c_l q_l,
which is displayed nowhere and is not obviously true at m ≥ 3: W-D4 +
the shared top exponent pin only π_{m−1} = c_{m−1} + e_{m−1}r ≥ c_{m−1}
(top level), leaving interior promotion deficits free to be compensated
by junk gains.  (At m = 2 the claim DOES follow — Σπq = π_{m−1}q_{m−1} ≥
c_{m−1}q_{m−1} = Σcq by exactly this W-D4 leg — but that reduction is
not displayed either.)  The compensation mechanism is instance-real:
EQ3G2A[2321,2321] carries three cells at ONE slot and ONE line with
junk counts {1,2} and correction counts {1,2,3} (Phase C above).  No
junk-0/junk-positive mixed group exists anywhere in 545 rows, so the
CLAUSE has no instance countermodel — the failure is the displayed
justification, not (on present evidence) the claim.  Same gap infects
the sub-claim "carries ≥ 1 correction L-edge" (a junk-riding partner
could carry a correction π-junk child and no L-edge; and the exclusion
of correction-free seeding-π-junk partners — same exponent dynamics ⟹
same profile ⟹ line strictly above the cascade's — is sound but
UNDISPLAYED).  Echo sites: the header S-L4 bullet ("cascade-slot
partners must carry corrections and satisfy an exact quantum-resonance
equation") and the S7 box sentence "A proof of (NEP) is a
quantum-resonance analysis of the S-L4(iii) equation (no cancellation
lemma)" — a (NEP) proof must ALSO exclude junk-riding partners (still
combinatorial/valuation-side, so the "NO residue input" tag survives).
Downstream: NOTHING graded PROVED consumes the gapped clause — S-THM(c)
consumes (NEP) directly (all partner paths, junk or not) plus
S-L4(ii), both sound; S-L4(iii)'s UNIQUENESS half (the cascade is the
unique correction/junk/Y₂-free path) re-derived SOUND (deterministic
firings + single promotion/exit children + unique d-cell + the E-L6
degree mechanism for the Y₂ fork).  CONFIRMED (as a justification gap).

**N-1 (NOTE, header bullet S-L4, line ~26).**  Quote: *"at (H3) ∧ g₀ =
1 the cascade is the UNIQUE correction-free two-exit path"* — the
body's qualifiers "no junk edge and no Y₂-edge" are dropped; as worded
the header claims more than S-L4(iii) states (a correction-free path
with a nonzero π-junk seeding sibling would be a second correction-free
two-exit path; none occurs on any probed row — CGRP/PRT partnered = 0
at g₀ = 1 across 379 committed + ~460 fresh rows, which incidentally
shows the cascade seeding's X̂ vanished on every probed instance — but
nothing displayed excludes it on the class).

**N-2 (NOTE, S-L0(c) wording).**  *"whatever the two top exponents"* —
a level-m cell has ONE top exponent (j_{m−1}); the [RMG] source remark
and the machine check both say "whatever the top exponent" (singular).
Also S-L2's proof parenthetical cites S-L0(b) for "raw cells … net to
coefficients of the same or higher valuation", which is subadditivity =
S-L0(a).  Wording only; both proofs are otherwise exact.

**N-3 (NOTE, EMPTY consumption).**  The "NOT load-bearing" grading of
EMPTY_PROOF is accurate for ρ_l (re-derived inline at S-L1) and
defensible at S-L4(iii): the E-L6 mechanism is re-derived as a
compressed parenthetical (deg b₀ = 0 ⟹ deg(b̂₀ĉ) = deg ĉ < d₀ ⟹ Ŷ = 0)
whose pieces live in ACCEPTED [RMG] L-NORM(c) + [IL3]† DIGIT-SPLIT
canonicity — but note the Y₂-exclusion it powers is load-bearing for
S-L4(iii)'s uniqueness half, so the parenthetical is doing real work;
if the E-L6 transfer were ever retracted the uniqueness clause would
need its own display.

**N-4 (NOTE, census breadth — favorable, for the record).**  The new
instrument data of §4: 4 new residue-char-2 cancellation rows (one
MIXED-characteristic), 0 at p > 2, survivor = the cascade slot at the
cascade line on all 6 unique kills; 37 characteristic-blind
opposite-sign slot kills at g₀ = 2 (bottom survived elsewhere on every
one); (NEP)/(RW)/(STK)/S-L1/S-L2/S-L3 instance-clean on all 545 fresh
rows including 4 tower shapes and one ring kind (Zp p = 2) never
probed by any committed battery.

## 6. VERDICT

* Machine leg: replicated exactly (output + json identical mod
  timings); pins green; selection-loop byte-faithfulness confirmed;
  all four controls fired from the artifacts.
* Both committed cancellation instances re-derived BY HAND from the
  committed engines; the p = 3 witness re-derived; every displayed
  number in S0/S1/S7/S8 re-computed independently and found exact.
* S-L0, S-L1, S-L2, S-L3 (the load-bearing step), S-L4(i)(ii), and
  S-THM(a)(b)(c): re-derived SOUND at the displayed pins; the honest
  perimeter (grade cap, open rows, disclosures, fences) is accurate.
* One justification gap: S-L4(iii)'s "junk-free forced" inference
  (G-1), with no downstream PROVED consumer.
* (SURV-DISJ) extended: 545 fresh rows + 4 new kills, 0 counterexamples.

SURV-PE1 FINDINGS: 0 critical, 1 gaps
VERDICT: GAPS-ONLY
