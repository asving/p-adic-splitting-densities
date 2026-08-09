# GENH4 passPE4 report — hostile verification of GENH4_PROOF_2026-08-08.md

**Verifier:** fresh-context hostile pass PE4 (quote-and-classify; fixes
nothing; the clean-count attempt). **Target:** `lean/notes/openmath/
GENH4_PROOF_2026-08-08.md` at HEAD (note body = r3, 4b0d946). **Arc:**
seal 121d9ab → RED 3eb1667 → GREEN 4b5c085 → PE1 263a36f → r1 dff23f8 →
PE2 2618e9b → r2 fd35416/5279a11 → PE3 a011533/3b88321 → r3 4b0d946 →
**PE4 = this**. **Charges:** (1) the [r3] trichotomy re-derived from
LEMMA GENH4-3(i) and checked against EVERY committed cell in BOTH
artifact JSONs (not the four the r3 unit checked), including the
w = dv(A₁) = ∞ corner; (2) the [r3] mnemonic scoping + the S10-BOX-1
[r3] stack refresh under the standing as-of standard (GENIND has since
moved to r2 + PE3); (3) PE3 remarks residue; (4) the full
[r1]+[r2]+[r3] tag set for cross-round contradictions; (5) structural
free hunt — the S9 assembly re-walked END-TO-END on two branches with
the genre-F line live. Machine leg (md5 + isolated re-run + instrument
audit) and a fresh route disjoint from all five prior routes below.

## VERDICT: CLEAN — 0 CRITICAL + 0 GAPS + 0 MINOR (+2 remarks).

Nothing at any finding tier survived my verification attempts. The r3
trichotomy is exhaustive and pairwise disjoint over every admissible
(N, w, parity) configuration including the hidden-A₁ corner, is
lift-robust (my own undercut analysis), matches the runner's source
branch-for-branch, and matches every committed key group in both
artifact JSONs — 134/134 own-law checks, 0 violations, covering 16
(row, prehistory, history) F-genre groups incl. the k = 2 cell, the
constructed feven row, and history-level groups no pass had law-checked
before. The machine leg reproduces bit-identically (main + supp). The
fresh route opens genuinely new territory — the FIRST non-prime-q
genre-F measurements ever (q = 4, the F₁₆ kit GENH4-BOX-3 discloses as
unbuilt) — and every preregistered count landed exactly, with both
pre-r2 counter-hypotheses fired. A NEW symbolic identity (expected
number of irreducible quadratic factors) ties five of the eleven R_τ
to an independently derived classical value, exactly in ℚ(q). **Per
the program's counter convention this pass starts GENH4's 2-clean
count: 0/2 → 1/2.**

### REMARKS (not findings)

* **REMARK A (wave-ordinal label in the [r3] BOX-1 text).** The [r3]
  stack refresh says GENIND "r2 dispatched at the wave-4 fold
  (4dbba60)"; commit 4dbba60's subject is "**Wave 3** folded" (the
  wave-4 fold is b3c05be, which reports r2 COMPLETE). The hash, the
  supplier state, and the counter in the same sentence are all correct
  (verified against git: GENIND r2's three commits 01:00/01:21/01:35
  all post-date r3's 00:50:10, so "dispatched" was exactly right at
  commit); the sentence even admits the true reading "dispatched into
  wave 4 at that fold". No consumer state can move on a fold ordinal
  when the pin is hash-correct — below the arc's own MINOR bar (PE1's
  minor was a wrong supplier STATE; this is a label on a correctly
  identified commit).
* **REMARK B (verdict-time stack refresh, per the [r3] standing
  as-of disclosure — executed, nothing owed).** Since r3: GENIND r2
  landed (2abf419/ad6f31d/52fb6ff, GENIND-6 transport proved,
  2,128,163/0) and GENIND passPE3 adjudicated NOT CLEAN 0C+2G+4m
  (f89b565), counter 0/2. HEX3 (b6a1d69), W-12 (be4a1dc/ee17210),
  HMENU3, W-11: zero note motion since their pins (checked by git log
  on each file). Minimum grade over the stack UNCHANGED at 0/2, so
  P(4)'s conditionality display is unaffected — and the [r3] standing
  disclosure prices exactly this. Load-bearing sub-check: GENIND
  PE3-G2 (GENIND-3's M_ℓ window display false at multi-child
  distinct-slope genres) touches nothing GENH4 quotes — grep of the
  note: **zero** hits for GENIND-3/M_ℓ; GENH4's S11 consumes
  GENIND-1(ii)/GENIND-4/GENIND.B + grammar only, at pins, at the
  stack grade.

---

## Charge 1 — the [r3] trichotomy: re-derived, corner-complete, and checked at ALL committed cells

**(a) Re-derivation from GENH4-3(i).** GENH4-3's interior partition has
antecedents {u odd ∧ u ≤ 2w} → RAM(u) (the "(needs u ≤ 2w: one side;
else (ii))" parenthetical), {u > 2w} → 2SIDED(w, u−w), {u even ∧
u ≤ 2w} → residual read. At u = N the residual read's S₀-pair sits at
height N, out of window (GENH4-CAP(F)) — so the third clause exits UND
and the boundary trichotomy is exactly r3's (a) N > 2w (either
parity) / (b) N ≤ 2w, N odd / (c) N ≤ 2w, N even. **Pairwise
disjoint** ({N > 2w} ∩ {N ≤ 2w} = ∅; (b)/(c) split by parity) and
**exhaustive** over every (N, w) including w undefined-by-window.

**(b) The w = dv(A₁) corners (the charged attack).** (i) A₁
window-hidden (all slots ≤ N+k−1 zero, incl. A₁ ≡ 0): every lift has
w_lift ≥ N ≥ N/2⁺, so N ≤ 2w_lift for EVERY lift — clauses (b)/(c)
catch it with lift-robust conclusions. (ii) w read in the band
(N ≤ w ≤ N+k−1, value NOT lift-stable): an out-of-window α₀ digit at
height N can undercut w to N but never below (α₀'s in-window digits
below N are already zero on the locus), so N ≤ 2w_lift again survives
every lift. (iii) In clause (a), N > 2w forces w < N/2 ≤ N−1: w is
interior, lift-stable, and the two length-1 hull sides need no
residual — decided shape-only. So all three conclusions are
lift-theorems, not window artifacts. My q = 4 leg-A walker (below)
realizes corner (i) raw: A₁-hidden members classify RAM(5) by raw
division on every lift representative, matching (b).

**(c) All-cells machine check (`/tmp/pe4/trichotomy_allcells.py`, own
code, no runner import).** For EVERY F-genre key group in
`qscout22_results.json` (23 rows) AND `genh4_checks_results.json`
(9 rows) — 16 (row, prehistory, H₂) groups: presence/absence exactly
as the trichotomy predicts given the floors (RAM(N) present iff N odd,
absent at even N; 2SIDED(w, N−w) present for exactly the slots
2k+1 ≤ w < N/2 above the history floor, forbidden at 2w ≥ N; band-UND
at even N only), PLUS the exact count of every u = N key against my
own comp-weighted law, PLUS every UND total against GENH4.B's
two-term closed form at both parities and both history depths:
**134 checks, 0 violations.** Coverage beyond r3's four cells: the
k = 2 cell (Zp,2,9,2) — where RAM(9) = 2048 exercises the A₀-band
free factor above N — the feven constructed row at BOTH histories,
the equal-char cells, both full-sweep rows with F keys, and the
history-level groups (e.g. (2,8,1) H₂ = (3,): 2SIDED(3,5) correctly
ABSENT because the floor w > 3 makes (a) unrealizable, while UND =
3,072 = 3·(512+512) keeps the two-term law H₂-independent). Full rows
at N < 4k+1 carry zero F keys — the S0/S1 [r2] admissibility floor,
confirmed in the negative direction.

**(d) The r3 box's own four counter-key claims** re-read directly from
the committed JSONs: 2SIDED(3,4) = 384 and RAM(7) = 128 at (Zp,2,7,k1)
empty history (the r2 clause order would predict 512/0 ✓);
RAM(5) = 2,117,682 at (Zp,7,5,k1) with key set exactly {RAM(5), UND}
((a) unrealizable at w ≥ 3 ✓); 2SIDED(3,5) = 1,536 vs UND = 1,024 at
(Zp,2,8,k1) ✓. All accurate.

**(e) The runner implements the trichotomy verbatim** (source read,
lines ~206–232 of `law_F`): odd dv0 → RAM with slots 2s > dv0 freed
(= (b), hidden-A₁ members included); 2SIDED for every 2·dv1 < dv0
either parity (= (a)); even dv0 = N → UND inside the even branch
(= (c)); ex0/ex1 = `q**comp(·) − 1` (the [r2] census). Display ≡
implementation.

## Charge 2 — the [r3] mnemonic scoping + the stack refresh: VERIFIED

* **Mnemonic (PE3 REMARK A repaired):** both sites now scoped — S1's
  statement close ("— away from the genre-F boundary band, whose pins
  are censused q^{comp}−1 = q−1 by the [r2] clause above, not by the
  re-based field") and S6.1's close (same content, pointing at the
  [r2] clause of S1). The scoping is CORRECT (my law evaluator and the
  q = 4 legs both live on exactly that exception), and no other
  unscoped survival found: S6.1's "F_{q²} censuses at the even-dμ
  residual events" is interior-only (true); S0's one-breath "census
  re-base proved" is an obstruction title, not a law display.
* **Stack refresh (PE3 REMARK B repaired):** every [r3] pin verified
  against git — HEAD-at-repair cc20066 IS 4b0d946's parent; GENIND
  PE2 50db400 (00:39:33, subject = 0C+2G+1m ✓); HEX3 r3 b6a1d69 ✓
  0/2; W-12 r5 be4a1dc/ee17210 ✓ 0/2; HMENU3/W-11 accepted 2/2,
  no motion ✓; "r2 dispatched" true at 00:50:10 (the three r2 commits
  landed 01:00–01:35). The standing as-of-commit-timestamp disclosure
  is now IN the box — the structural cure PE1/PE2/PE3 kept asking
  for. Residuals: REMARK A (wave ordinal) and my own verdict-time
  refresh (REMARK B above), which the disclosure explicitly assigns
  to the verifier.

## Charge 3 — PE3 residue: nothing repair-owed was left unrepaired

PE3 left exactly three items (MINOR 1 + REMARK A + REMARK B); the r3
diff (5279a11..4b0d946, read hunk-by-hunk) touches exactly five spots:
the S1 mnemonic scope, the GENH4-CAP(F) box restatement, the S4
bracket restatement, the BOX-1 [r3] append, and the S13.2 arc append —
the three items plus the arc line, nothing else. Runner + all
artifacts byte-untouched through r3 (md5 identity chain below). The
restated trichotomy was RE-DERIVED (its antecedents differ in form
from PE3's suggested one-token patch — disjoint-antecedent display
rather than "ODD N ≤ 2w" insertion), consistent with the ledgered
"re-derive, never transcribe" lesson; and S4 carries the equivalent
first-match form. No new defect introduced: every fresh [r3] numeric
claim re-verified (charge 1d), both restatements equivalent.

## Charge 4 — cross-round tag consistency ([r1]+[r2]+[r3]): COHERENT

Hunted specifically for contradictions BETWEEN repair rounds:
* r2's census clause (S1/S6.1) vs r3's trichotomy at the same pins:
  coherent — my single evaluator implements both simultaneously and
  reproduces every committed number (charge 1c).
* r3's CAP-box disjoint-antecedent display vs r3's S4 first-match
  display: logically equivalent (first-match (a)-else-(b)-else-(c) =
  the disjoint antecedents).
* GENH4.B's sealed "present at even N only" vs (c): same content;
  the two-term law's band term verified at BOTH histories of both
  even-N cells.
* S6.3's slot-by-slot display vs GENH4.B's closed forms: the exponent
  identities re-checked (Σcomp(A₁, 2s ≥ N) = 2⌊N/2⌋+k; deep₀ =
  q^{k−1}); consistent both parities.
* S13.1 [r1] "3ψ" gloss, S12 [r2] GH-DENS relabel, S11 [r2] W-12.D
  re-pin: unchanged since PE3 verified them; spot re-checks agree.
* Header line "Attempt grade 0/2 (composed; no hostile arc)" is
  sealed-frozen text superseded by the BOX-1/S13.2 r-tags — the
  arc's standing append-only convention, priced by three prior
  passes; not re-litigated.

## Charge 5 — structural free hunt: the S9 assembly re-walked END-TO-END on two branches (genre F live)

The eleven-R_τ assembly had survived PE1–PE3 via symbolic Σ-checks,
engine ties and anchors, but no verifier had re-derived a branch from
the polygon masses. I rebuilt TWO single-prime branches from scratch
(`/tmp/pe4/symbolic_leg2.py`), using only the W-12.A pinned entry
volumes and the note's block vectors:

* **R_{(2,2)}:** ν₄({(2,2)}) = [Σ_{h odd} q^{1−5h}·(q(q−1)/2
  [G2(h;'2') decided] + (q−1)/(2(q+1)) [E-entry × μ_E-inert]) +
  Σ_k (q²−q)/2·q^{−10k}·q²/(q²+1) [F-entry × μ_F-RAM]] / (1 −
  Σ_k (q−1)q^{−10k}) [D4 self-loop]; then R_{(2,2)} =
  [n₂·q²/(q²+1) + q·ν₄({(2,2)})]/q⁴ — **equals the S9.4 display
  symbolically in ℚ(q)**.
* **R_{(1,4)}:** ν₄({(1,4)}) = [Σ_k q^{−10k}·(n₂/(2(q²+1))
  [F-entry × μ_F-inert] + n₄ [FULL(k; irreducible-quartic residual),
  decided])]/(1 − loop); R_{(1,4)} = [n₄ + n₂/(2(q²+1)) +
  q·ν₄({(1,4)})]/q⁴ — **equals the display symbolically**.
* **Engine tie at the branch level (finer than any prior pass):**
  β₄({(2,2)}) and β₄({(1,4)}) from the md5-pinned engine equal my ν₄
  values EXACTLY at q = 2, 3, 5 (566/7665, 31/10220, 15813/393640,
  121/393640, 629725/38085918, 781/50781224).
* **Honesty disclosure of my own two first-cut errors** (both mine,
  both instructive for the assembly's completeness): I initially
  omitted the FULL(k; 4̄) family — the deficit came out EXACTLY
  (q²−1)/(4q²(q⁹−1)), which is that family's mass, confirming the
  note's s4-census family table is complete where my quick read was
  not; and my first classical side of the new identity (below) used
  maximal-order integrals where conductor stratification is needed.
  After fixing MY legs, everything is exact.

Genre F's line is live in both branches (μ_F({(2,2)}) = q²/(q²+1),
μ_F({(1,4)}) = 1/(2(q²+1)), mass (q²−q)/2·q^{−10k}), so this is the
charged "genre-F contribution re-walked at full rigor", twice over.

## MACHINE LEG: GREEN, bit-identical; instrument honest

* **Pins 11/11:** runner `ee8024b7…`, output `9e6ca9b3…`, results
  `cbcff562…`, supp runner `7d0445c5…`, supp output `8ce5faa8…`, supp
  results `c966d311…`, qscout22 `cb885663…`/`6c2441a1…`, w10
  `a9c34244…`, w12 `7dc040d9…`, engine `7240a916…` — all match the
  note's displays at worktree = HEAD. Runner byte-identical at
  4b5c085 = fd35416 = 5279a11 = 4b0d946 = HEAD; seal 121d9ab =
  `e5e435c3…` (the one disclosed repaired line). r3 is note-only ✓.
* **Isolated re-run** (fresh copy of `verification/` under /tmp/pe4;
  committed artifacts never written): **GREEN, 1,245.2 s**, families
  6/481/54/5/192,000/8/46,590/92/157/115/6,185 = 245,693 checks,
  0 violations; teeth LAT 19 / CEN 14 / ALPH 4 / SIG 2 / DENS 1 —
  identical to S13.2. Results-JSON leaf-diff vs committed: **1 leaf,
  elapsed_s only.** Output txt identical ex-timing. Environment note:
  the first launch died at import (this shell disables user
  site-packages, ENABLE_USER_SITE=None); relaunched with PYTHONPATH —
  no artifact was produced by the aborted attempt.
* **Supp leg re-run:** GREEN, 1.9 s; results leaf-diff = elapsed
  only; output file identical ex-timing.
* **Instrument tautology audit:** `law_F` source read directly — it
  IS the r3 trichotomy plus the [r2] census (`ex0 = q**comp(dv0)−1`),
  so display ≡ machine; qscout22 consumed as READER only (`read22`
  at the two fresh-row sites; zero model calls); my own two
  from-scratch instruments (charge 1c walker-law + the q = 4 raw
  walkers) independently reproduce the rows the battery ties to —
  the battery is not self-certifying.

## FRESH ROUTE (disclosed: disjoint from all five prior routes)

Prior: PE1 = tuple scans + Zp walkers + own NP derivation; PE2 =
symbolic GENH4-1F + 504-case ledger closure + tame primes 11/13 +
mechanism-free σ at 11/13; PE3 = equal-char raw walkers at (2,8)/(5,5)
+ mechanism-free σ at wild p = 2, 3; r2 supp = HMENU3-derived T_τ tie;
r3 = counter-key reads. **This pass: (A/B) the first NON-PRIME-q
genre-F measurements ever, (C) a new symbolic identity, (D) the
two-branch assembly re-walk (charge 5).**

**(A) `/tmp/pe4/q4_walker.py` leg A — (Fqt, q=4, N=5, k=1), the FULL
consF row, 24,576 members.** GENH4-BOX-3 discloses "genre-F rows at
q = 4 remain unbuilt (F₁₆ kit)"; the laws claim every prime power.
Enumerated RAW from B-space (level-1 polygon digit pins, residual
ψ² per irreducible quadratic ψ over F₄ — all 6 ψ's have c₁ ≠ 0, as
char-2 irreducibility forces; no fibration used), each member
classified by my own raw φ-adic division reader with hand-rolled
GF(4) arithmetic. Preregistered from my comp-weighted law:
RAM(5) = 6ψ·(q−1)·q⁵ = 18,432 and UND = 6ψ·q⁵ = 6,144. **Observed:
EXACTLY those two keys at exactly those counts.** Armed counters both
FIRED: (i) the pre-r2 "u = N → UND always" exit predicts RAM(5) = 0
(obs 18,432); (ii) the pre-r2 Q−1 band census predicts RAM(5) =
6·15·4⁵ = 92,160 > the whole row — the mass-conservation kill,
now at non-prime q.

**(B) `/tmp/pe4/q4_walker.py` leg B — (Fqt, q=4, N=7, k=1)
conditioned box, 6,144 members: the F₁₆ kit exercised.** Box =
{v₁(A₀) ≥ 6, A₁ slots > 3 zeroed, slot-3 pair free}, built THROUGH
the GENH4-1F development map (constructive validation, the GH-FEVEN
precedent) with EVERY member then re-verified raw on the F(1,ψ)
entry locus (6,144/6,144) and read by raw division + raw recentering.
Eight preregistered keys, hand-derived from the note's laws before
running — ALL EXACT:
SPLITEQ(3) 2,520 · INERT(3) 2,880 · 2SIDED(3,4) 270 · RAM(7)@() 18 ·
SPLTAIL(3) 90 · UND@() 6 · RAM(7)@(3,) 270 · UND@(3,) 90.
What this exercises, all firsts: the F₁₆ residual censuses — per
(ψ, slot-7) the 240 (S₁, S₀≠0)-states split **105/120/15 =
(Q−1)(Q−2)/2 / Q(Q−1)/2 / (Q−1) at Q = 16** (an F₄-census
counter-reading would give 3/6/3-pattern — wildly refuted); 360 raw
refine events at ODD dμ = 3 in equal characteristic 2 at q = 4 (the
carry C = ŝ_a²t⁴ live on the 12/15 letters with ŝ_a ≠ 0; the 3
F₄-pure letters ride the carry-free cascade), with the GENH4-4
floored-node image claim asserted at every re-entry (0 violations)
and the post-refine 45:15 = (q−1):1 split landing exactly; the r3
trichotomy live at u = N = 7 — (a) vs (b) separated at empty history
(2SIDED(3,4) = 270 vs RAM(7) = 18) exactly as the disjoint
antecedents predict; the char-2 Artin–Schreier '1sq' ⟺ S₁ = 0
degeneration pointwise on all 360 events. Every S5 key invariant
(v(p₀) = 2k exact, residue pair ψ) asserted at every recenter.

**(C) `/tmp/pe4/symbolic_leg2.py` — a NEW identity in ℚ(q), never
checked anywhere in the arc: E[#irreducible quadratic factors].**
Display side: R_{(1,1)²(1,2)} + R_{(1,1)²(2,1)} + 2R_{(1,2)²} +
2R_{(1,2)(2,1)} + 2R_{(2,1)²} (five of the eleven R_τ, weights =
number of ef = 2 primes). Classical side, derived independently by
quadratic-remainder co-area: E = Σ_g E_h|Res(g,h)| over irreducible
monic quadratics g, stratified by conductor index m (vol{v(disc) =
2m nonsquare} = (1−1/q)q^{−2m}/2, vol{v(disc) = 2m+1} =
(1−1/q)q^{−2m−1}), with the order-integrals I(inert, m), I(ram, m)
computed via no-cancellation minima (residue-independence at inert
ties; parity at ramified ties — the GENH4-2 mechanisms, resurfacing
in a decorrelated derivation), summed over m in closed form:
**display ≡ classical, exactly, symbolic in ℚ(q)** (both = 72/155 at
q = 2). The naive maximal-order shortcut (my disclosed first cut,
Q/(Q+1) and q/(q+1) applied at every conductor) gives
q³/(2(q+1)(q²+1)) + q/(q+1)² ≠ the display — the conductor
stratification is load-bearing, and the display sits exactly on the
correct side of that distinction. Guards: the eleven forms re-typed
by hand and pinned on the note's 22 anchors (0 mismatches);
Σ_τ R_τ = 1 and E[#roots] = q/(q+1) re-verified symbolically.
Derived tame-side (odd q), so it pins the rational function — a
five-type, distinct-weight linear constraint on the display that no
Σ = 1 or E[#roots] check could supply.

## Clean charges (executed, nothing found)

Charge 1 (trichotomy: derivation + corners + 134/0 all-cells + runner
source); charge 2 (mnemonic scoped at both sites; stack pins all
verified; as-of disclosure present); charge 3 (r3 = exactly the three
owed items + arc line; no collateral edit; runner/artifacts frozen);
charge 4 (no cross-round contradiction; r2 census ⊕ r3 trichotomy
jointly implemented by one evaluator that matches everything);
charge 5 (two assembly branches re-derived to the display and to the
engine, genre-F line live); machine leg (11/11 pins; GREEN
bit-identical re-runs, main + supp; instrument non-tautological).

## GRADE LINE

**CLEAN: 0 CRITICAL + 0 GAPS + 0 MINOR (+2 remarks, neither
repair-owed).** Every attack the charge sheet ordered was executed;
nothing at any tier survived. Honest steelman of the nearest
candidate finding: the "wave-4 fold" ordinal (REMARK A) is a label
slip on a hash-correct, state-correct pin — it cannot move any
consumer and sits below this arc's demonstrated MINOR bar; I will
not manufacture a finding from it. **The 2-clean count STARTS:
counter 0/2 → 1/2. PE5 (or the program's accepting attempt) is next;
acceptance requires one more clean pass on the then-current body.**
The note's substance survived: the discharge [GENIND-H(4)], THEOREMS
GENH4.A/B/C, the eleven R_τ — still conditional exactly on the S11
arc-grade stack (minimum grade 0/2 at verdict time; GENIND 0/2 with
its own arc live), exactly as displayed.

## Verifier's session artifacts (all under /tmp/pe4; repo untouched except this report)

* `/tmp/pe4/trichotomy_allcells.py` — the all-cells trichotomy + boundary-law checker (134/0).
* `/tmp/pe4/q4_walker.py` — the q = 4 raw walkers, legs A and B (GF(4)/F₁₆ hand-rolled kit).
* `/tmp/pe4/symbolic_leg.py`, `symbolic_leg2.py` — identities + assembly re-walk (first cut with my two disclosed errors; corrected run GREEN).
* `/tmp/pe4/run/`, `/tmp/pe4/supprun/` — isolated re-runs (`rerun.log`, `supp.log`).
