# SURVDISJ-PE2 — hostile content verification pass 2 (fresh context)

Object: `lean/notes/openmath/SURVDISJ_PROOF_2026-08-08.md` at **012d738**
(confirmed via `git log -1 --format=%h -- <file>`; this is the SD-r1
text).  Charge: the orchestrator's 5-point round-2 charge — (1) the r1
remedy hostile (the principal-d-cell pin re-derived, echo sites,
consumers); (2) the four note fixes; (3) the full spine standing alone
(re-derived, round 1 NOT trusted); (4) both machine legs re-run
read-only + one fresh hand-re-derivation per kill regime; (5) fresh
eyes.  I verify; I fix nothing.  Date: 2026-08-08 campaign (wallclock
2026-08-04).

Sources read at the cited displays or in full: SURVDISJ_PROOF (whole,
762 lines), the 4f7c3ff→012d738 diff (whole), SURVDISJ_passPE1_report.md
(whole), SURVDISJ_INSTRUMENT (verdict sections), WMULTDCX (S1 setting +
(H1)–(H3), W-D1, W-D2(0)–(iv), W-D3/LED_l, W-D4, W-D7 claims row),
SURV_PROOF (S2 S-L0, S3 S-L1, S4 S-L2/L3, S5 S-L4 incl. the S-r1
rescope, S6 S-THM), RMENGINE (S0.1 class pin, S2.1 L-CELL + L-NORM
display, S2.2 child inventory, acceptance record — round 7 PC7+PE7
double-clean, counter 2/2, [RMG] ACCEPTED), EMPTY_PROOF (header, S6
E-L6 + the W-D1 leg, E-r2 record), `survdisj_derive_checks.py` (whole,
485 lines), `survdisj_instrument.py` (selection + group/verdict code),
both committed artifact sets, commits 61e9e36/00e19b4/7314525.

## §1. Charge 1 — the r1 remedy, hostile: the pin is CORRECT, SHARP, and correctly consumed

**The pinned clauses re-derived fresh (not from PE1's text).**  Under
the pin [c_D = the PRINCIPAL d-cell, w₀(c_D) = u₀]:
b₀ = π^{u₁+u₁′} (W-D1: the formal-cell identity; deg b₀ = 0, w₀ =
u₁+u₁′), so L-NORM(a) on b₀·c_D gives the L-child at w₀ EXACTLY
(u₁+u₁′) + u₀ = ŵ with normalized residue b̄₀·c̄_D = 1·c̄_D ≠ 0 (K₀ a
field, nonzero primitive part) — clause (ii) TRUE verbatim; L-NORM(b)
gives the π-junk child, if nonzero, at w₀ ≥ w + 1 = ŵ + 1 at the SAME
exponent vector — clause (iii) TRUE verbatim.  RMENGINE S2.1's L-NORM
display re-read directly (lines 450–477): (a)/(b) say exactly this.

**The falsity shape at t ≥ 1 seeds re-derived.**  W-D2(iv) (read
directly at WMULTDCX lines 177–178): at g₀ ≥ 2 every d-cell has
j₀(D) = s₁(u₁) + t·e₀, 0 ≤ t < g₀, **w₀(b_D) = u₀ − t·h₀**.  On the
class h₀ = γ₁ ≥ 1 (RM-GEN S0.1: w₁Φ₁ = e₀g₀γ₁ must be positive;
RMENGINE's own census leg "needs only h ≥ 1" presupposes it; every
probed g₀ ≥ 2 read has h₀ = 1 or 2), so for t ≥ 1 the L-child sits at
ŵ − t·h₀ < ŵ strictly and the X-bound reads off the wrong base — the
unpinned clauses are FALSE there, exactly as the SD-r1 bracket states.

**The automatic-on-locus claim.**  W-D2(iii) + S-L1's parenthetical
(SURV_PROOF lines 242–246): at (H3) ∧ g₀ = 1 every d-cell's exponent
vector is forced to (s₁(u₁), …, s_m(u_m)) and L-CELL(i) keys cells by
exponent vector, so Ĉ_m is a SINGLE cell with w₀(c_D) = u₀ — i.e. the
unique d-cell IS principal, at ANY d₀ (not only d₀ = 1).  The bracket's
"automatic at (H3) ∧ g₀ = 1" is exact, and covers the (SD-YJ) box's
d₀ ≥ 2 use of (★) as well.

**Echo sites.**  All three carry the pin: the S3 statement (both
clauses bracketed), the S9 claims row ("(ii)/(iii) AT THE PRINCIPAL
d-cell [SD-r1 pin]", consumption extended by W-D2(iii)/(iv)†), and F-A
("SD-L4(i) is any-seed/any-d₀, while SD-L4(ii)/(iii) carry the
principal-d-cell pin").  Clause (i) correctly stays any-seed: E-L6
(EMPTY S6, re-read) needs only deg b̂₀ = 0, giving deg(b̂₀ĉ_D) =
deg ĉ_D < d₀ at ANY seed and d₀.  No other site in the note consumes
the ŵ clauses — grepped every SD-L4 mention.

**Consumers re-verified independently.**  (a) SD-THM-A(i) consumes
(ii)/(iii) only after establishing CE(C) = ∅, where the seeding is
b₀·c_D "with the unique principal d-cell" — on the theorem's locus
(H3) ∧ g₀ = 1 ∧ d₀ = 1 the seed IS the unique principal cell
(W-D2(iii): the single principal cell π^{u₀}∏Φ^{s}), so the pin is
satisfied, not merely assumed.  (b) SD-L5's proof consumes NO clause of
SD-L4 at all: junk-free directly excludes the X/Y children, and the
claims row lists only W-D2(iv)†/W-D3†/S2.2-determinism.  The brackets'
phrase "SD-L5 consumes only the fork-counting" (PE1's own wording) is
a conservative over-statement of dependence in the safe direction —
checked, harmless.  (c) Statement-fence: the 4f7c3ff→012d738 diff
touches only SD-L4's clauses + brackets, the K2-box census line, the
two S8 TRACK bullets, the S9 SD-L4 row, F-A/F-E, the header, and the
appended repair record; SD-THM-A and SD-L1/L2/L3/L5/L6/L7 statements
are byte-unchanged as claimed.  **The remedy is the correct fix and is
the SHARP pin (true exactly at principal seeds, false off them).**

## §2. Charge 2 — the four note fixes: ALL FAITHFUL

**N-1 cure (CROSS confinement).**  The removed "complementarity"
framing was indeed tautological (a killed ±1-class group has signed
count ≢ 0 mod every p, hence CROSS by the genre definition —
`classify_group` read directly: CROSS := not all-zero and not all
≡ 0 mod p).  The replacement is genuinely empirical and I verified it
from the committed artifacts: **exactly 9 CROSS kills** (killdec) —
8 × p = 3, g₀ = 1, junk-free, signed (∓2, ±1) (i.e. 2·res_a = res_b in
F₃) + 1 × p = 2, g₀ = 2, SDG2AF[2321,2321], junks {1,2}, signed
(−3, +1, −1) (res_a + res_b = res_c in char 2); **at_bottom = False on
all 9**, and cross-checking each against its row's survdec: no CROSS
kill line equals its row's β_min or any survivor netline (clash = False
on all 9).  The dated bracket below the box records the removal
accurately.  Bonus: the box's "12 observed (−2)-vector survivors need
p ∤ 2" also verified — eqlgrp has exactly 12 surviving bottom groups
with signed vector (−2) (plus 151 off-bottom, and 22 (+2) off-bottom).

**N-2 cure (TRACK).**  Both S8 bullets now display TRACK with dated
brackets; SD-THM-A's head and the header verdict always carried it
(confirmed at 4f7c3ff).  Exact.

**N-3 cure (DRV-NEPS disclosure).**  The composer family does
condition on `casc_rec is not None`
(survdisj_derive_checks.py:222–224).  Both backstops verified: the
instrument fires SDI-SURV UNCONDITIONALLY on
`allg1 and stk and len(casc) != 1` (survdisj_instrument.py:265–266;
0 violations in my re-run), and the arithmetic holds — pbrows (the
g₀ ≥ 2 live rows) = 286, 979 − 286 = 693 = neps_ok = P-A's denominator,
so no g₀ = 1 row was in fact skipped.  The S4 bracket + S7 pointer
state exactly this.

**N-4 cure (EMPTY header, cross-file).**  The 012d738 diff on
EMPTY_PROOF is confined to the header counter (0/1 → 1/2 CLEAN) plus
the dated [SD-r1 cross-file] bracket, nothing else.  Commit 7314525
verified: "(EMPTY) round 2: PE2 CLEAN 0C/0G … counter 1/2 CLEAN", and
the E-r2 tail record in EMPTY_PROOF concurs.  Correct and properly
bracketed.

## §3. Charge 3 — the spine, re-derived standing alone

**SD-L2.**  Re-derived from LED_l (W-D3, re-read with its proof)
against the [RMG] S2.2 inventory (re-read): Σ E_l·(LED_l) gives
M(j⃗(C)) = M(σ⃗) + M(j⃗(D)) + Y₂ − 2P_{m−1}E_{m−1}
− Σ π_l(P_{l−1}E_{l−1} − E_l) − Σ_c defc_c with
defc_c = (P_{i_c} − e_{i_c}k_c)E_{i_c} − Σ_{l<i_c} a_{c,l}E_l − Y_c —
term by term: seeds (σ from X₀ via W-D1, j⃗(D) at stage 2, +1 at l = 0
per Y-edge whether at a correction (Y_c) or the seeding (Y₂));
consumption P_l per promotion-out/exit, P_i − e_ik per correction;
dumps a_{c,l} at l < i_c; π-junk children move no exponents; i = 0
correction children carry no dump vector.  Every S2.2 child type
accounted; EXACT as displayed.  ∎

**SD-L1.**  (H2) + (H3) + g₀ = 1 give g_l = 1 for ALL 0 ≤ l ≤ m−1
((H3) = interior 1..m−2, (H2) = m−1, g₀ = 1 = level 0), so P_l = e_l
and k_c = 0 everywhere — the parenthetical is right.  Consumption
= E_{i+1} exactly; dump ≤ Σ_{l<i}(e_l − 1)E_l = E_i − 1 (mixed-radix
telescope, re-checked; empty at i = 0 consistently); hence defc ≥
E_{i+1} − E_i + 1 − Y_c ≥ 0, defc ≥ 1 at Y_c = 0, and equality forces
e_i = 1 ∧ Y_c = 1 ∧ full dump.  All three legs re-derived.  ∎

**(★).**  Pool telescope re-checked bracket by bracket
(ρ_l = σ_l + s_l(u_l) + c_{l−1} − e_{l−1}c_l; carries telescope to
−c_{m−1}E_{m−1}; top term added/removed with D = σ_m + s_m(u_m);
k = 2e_{m−1} − D and e_{m−1}E_{m−1} = E_m): M(ĵ) = M(σ⃗) + M(j⃗_prin)
− 2E_m.  SD-L2 at all-g = 1 (promotion-loss zero, exits 2E_m, unique
principal-exponent seed by W-D2(i)–(iii) at ANY d₀) subtracts to
Σ defc = Y₂(C) ∈ {0,1}.  ∎  (The any-d₀ validity matters for the
(SD-YJ) box and holds — S-L1's uniqueness parenthetical is any-d₀.)

**SD-L3.**  Consumed verbatim from accepted L-NORM(c) (display
re-read): at d₀ = 1, deg(b̂ĉ) ≤ 2d₀ − 2 = 0 < d₀ at every L-NORM
invocation, Ŷ ≡ 0.  Faithful; labeled consumed-not-composed.  ∎

**SD-THM-A(i)–(v).**  (i): (★) + SD-L3 kill Y₂ and every Y_c; SD-L1
then forces CE(C) = ∅; correction-free ⟹ stage-1 exit coefficient b₀
(the E-L6 "why b stays monomial" leg, re-read); seeding = b₀·c_D,
unique principal seed; Y-child nonexistent (SD-L4(i)); the only fork
in the whole tree for a correction-free path is L vs X at the seeding
(L-NORM splits occur only at corrections and seedings); post-seeding
walk exponent-driven deterministic (S2.2 promotion/exit unique,
E1-priority; = the UNrescoped uniqueness half of S-L4(iii)) — so C = Ĉ
or the ≤ 1 X-mate with same exponents, junk ≥ 1, w₀ ≥ ŵ + 1.  (ii):
line affine in w₀ at fixed slot (S-L4(i)) puts any mate at
β̂ + E_m(w₀ − ŵ) > β̂; β̂-population = {Ĉ} = (NEP).  (iii): S-L0(b) at
w₀.  (iv): immediate.  (v): S-THM(c) re-read at SURV_PROOF S6 — its
hypothesis list (TRACK, (H1)–(H2), c ≥ k, (H3) ∧ g₀ = 1 ∧ (STK), (RW),
(NEP)) is fully covered by the theorem head + clause (ii); the rescoped
m = 2-forcing half of S-L4(iii) is consumed NOWHERE in this note
(checked every citation site).  ∎  Pins in the head and F-A exact.

**SD-L5.**  Seed inventory W-D2(iv); no forks given the seed
(junk-free excludes X/Y directly, no correction forks, determinism);
LED_0 with no corrections/dumps/Y: j₀ = σ₁ + s₁(u₁) + te₀ − P₀π₁;
equal slots force (t − t′)e₀ = e₀g₀(π₁ − π₁′) ⟹ t ≡ t′ (mod g₀) ⟹
t = t′ ⟹ same path.  θ₀ = 0 remark right (only distinctness of t·e₀
mod e₀g₀ is used).  ∎

**SD-L6.**  Same slot+line ⟹ same w₀ (S-L4(i)); reduction mod π
additive on primitive parts of degree < d₀ (no quotient collapse);
nonzero residue sum ⟹ w₀ exact ⟹ line exact; zero ⟹ B_G = 0 or w₀
raised ⟹ line rises by E_m per unit.  Biconditional exact.  ∎

**SD-L7.**  Case (a) ±r_a ≠ 0 (residues nonzero by L-NORM(a));
case (b) r_a − r_b ≠ 0 by distinctness — characteristic-free.  Warning
display correct ((+1,+1) unprotected since r_b = −r_a is a real
distinct class at char ≠ 2).  ∎

**Boxes.**  (SURV-K2): existence half only; the reduction wiring
(SD-L6 + SD-L7 + S-L3 ⟹ bottom survives ⟹ with (RW₀) S-THM(b) ⟹
Q¹ ≠ 0) checks.  Constraint census verified from artifacts (§4b).
(SD-YJ): the deficit analysis re-derived — a companion ≠ Ĉ/X-mate at
g₀ = 1 has Σ defc = Y₂ ∈ {0,1}, each defc ∈ {0,1} (nonneg integers,
sum ≤ 1); Y₂ = 0 ⟹ every correction defc = 0 (e_i = 1 ∧ Y-child ∧
full dump) with ≥ 1 correction needed (else it's Ĉ/X-mate); Y₂ = 1 ⟹
the seeding itself is a Φ₀Y-edge; either way ≥ 1 real Φ₀-overflow —
impossible at d₀ = 1, open at d₀ ≥ 2; the displayed deficit-1 examples
check (e_i = 1 full-dump L/X: defc = 1; i = 0, e₀ = 2, Y: 2 − 1 = 1).
Machine-dark verified directly: NO g₀ = 1 ∧ d₀ ≥ 2 tower in WS.ROSTER
∪ ED.FRESH_ROSTER ∪ PX ∪ SD (all d₀ = 2 towers — W3G2B, W3G2P5, XM3B,
EQ3G2A, SDG2AF, SDG2AZ — are g₀ = 2).  Nothing PROVED consumes either
box (claims-table consumption edges checked).

**Grade cap + consequence display + records.**  All five consumption
grades verified at the sources' own heads TODAY: WMULTDCX 0/2 CLEAN;
SURV_PROOF 0 CLEAN (S-r1, GAPS-ONLY repaired); EMPTY 1/2 CLEAN (now
also in its own header); RMENGINE ACCEPTED (round-7 PC7+PE7
double-clean, counter 2/2 — ledger re-read); own arc 0/1 CLEAN, stated
in the header, F-E, S8 item (4), and the tail record consistently.
S8's LAW-DCX display: c ≥ k leg = SD-THM-A(v) ((RW) in the pinned
class ✓), c < k leg = E-THM ((H1)–(H3), g₀-free — re-read at EMPTY's
claims table; zero two-exit paths ⟹ Q¹ = 0 as an empty sum).  The
10-item still-open list, F-A–F-G, the head bracket, and the tail
REPAIR RECORD all match the PE1 report and the diff.  S1's regime
recap verified from artifacts: the six K1 rows ARE the 6 CANC
(bottom-dead) rows, surv_is_casc on all 6; the 97 bottom SIGN-PAIR
kills (66 p3 + 30 p2 + 1 p5) all sit on rows with bottom_surv = True.

## §4. Charge 4 — machine legs

**(a) Pins + re-runs.**  All four committed md5s match the note's pins
(runner 3eaf69c…, output be088ed…, results 868f719…, instrument
3df33c7…); the composer's PINS dict = the instrument's 7 + the
instrument runner (8, all green).  Both runners re-run read-only to
/tmp this pass: **composer results JSON non-elapsed diff = [], stdout
identical mod timings** (10 families, 0 violations; all counters,
DEFC_MIN, group census, controls digit-identical); **instrument
results JSON non-elapsed diff = []** (0 violations).  Phase split
re-counted from output lines: 286 sealed + 330 EQ + 212 PX + 151 SD
= 979 ✓.  Two-commit seal re-verified genuine: 61e9e36 = runner +
design note only (PRED-1..7 sealed, results PENDING); 00e19b4 adds
artifacts + verdict, `git diff 61e9e36 00e19b4 -- survdisj_instrument.py`
EMPTY.

**(b) Note-vs-artifact numbers.**  mass_ok 3,606; defc_ok_g1 2,167
(min 1,2,3,4 at e = 1,2,3,4, all Y = 0 — sharp); y0_ok 3,274 + CTRL-Y
60; seedx_zero 1,355 / seedx_nonzero absent; neps_ok 693; rig_rows 979
+ CTRL-RIGSEEDS 123; crit_ok 280 + CTRL-KILL 352 (= 632 groups);
m1_protected 56 + CTRL-M1 576; CTRL-XSEED 388; CTRL-DEFNEG SILENT
(disclosed at S7(i)/F-C); group census g1 6/12 bottom + 140/160 off,
g2+ 97/31 + 109/77 — ALL matching the note.  From the instrument
artifacts, re-aggregated independently: P-A **693/693 ok, 0 fail**;
PB-mult1-some **286/286**; P-C 97 ok / **103 fail** of 200; M-B1
oddkill **39**; the P-M1 census recomputed cell-by-cell over all 211
minimal survivors of the 200 kill rows: **{(+1)×85, (−1)×115,
(−1,0)×5, (0,+1)×4, (−1,+1)×2}** EXACT (as multisets of class-count
vectors; artifact encounter-order writes (0,−1)/(0,1) — same content);
cross_kills 9.  The runner's check-transcriptions verified against the
displays line by line: DRV-MASS = the SD-L2 formula termwise; DRV-DEF's
bound = E_{i+1} − E_i + 1 − Y_c exactly; DRV-NEPS's companion shape =
SD-THM-A(i)'s X-mate clause; protected() = SD-L7(a)/(b) verbatim.

**(c) Fresh hand-re-derivations, one per regime (rows DISJOINT from
PE1's three):**

* **K1 regime — PXFLTF[123,123]** (Fpt p = 2, m = 3, e⃗ = (3,1,2),
  all g = 1, d₀ = 1; E⃗ = (1,3,3), E₃ = 6).  Bottom slot (0,0,0) at
  β_min = 90: TWO cells, each one i = 0, k = 0 correction; sign
  (−1)¹ = −1 both ✓; factorizations b0[w₀=10]·cd(i=0,k=0)[w₀=1,res=1]·
  cD(jD=[2,0,1])[w₀=4,res=1] ⟹ w₀ = 15 both ✓ (L-NORM(a) additivity),
  residues 1·1 = 1 equal ✓; net −2·(unit) ≡ 0 in char 2 — MODP kill ✓.
  Survivor = the cascade: slot (0,0,1) at line 93, single cell,
  correction-free, w₀ = 14 = 10 + 4 = ŵ ✓, sumfree, is_casc ✓ —
  SD-THM-A realized on a CANC row.  LEDGER: M((0,0,0)) = 0,
  M(ĵ) = E₂ = 3, each killed cell's Σ defc = P₀E₀ = 3 ⟹ M(ĵ) − M =
  Σ defc EXACT.  Also the off-bottom MODP pair at (1,0,0): the i = 1
  correction dumped a₀ = 1, defc = e₁E₁ − 1 = 2 ≥ 1 = the SD-L1 bound
  at e₁ = 1 ✓, and M(ĵ) − M = 3 − 1 = 2 = defc EXACT — a live test of
  the ledger at an interior e_i = 1 level.
* **K2 regime — W3G2A[683,687]** (Zp p = 3, g₀ = 2, sealed).  Bottom
  slot (0,0,0) at β_min = 468: cell A (t = 1 seed jD = [5,1,1],
  w₀(cD) = 10) rides k = 1 + k = 0 corrections, sign (+1) = (−1)² ✓,
  w₀ = 26+1+2+10 = 39 ✓, residue 1·2·2 = 4 ≡ 1 ✓; cell B (t = 0
  principal seed jD = [2,1,1], w₀(cD) = 11) rides one k = 0
  correction, sign −, w₀ = 26+2+11 = 39 ✓, residue 2·2 ≡ 1 ✓.  Equal
  residues, opposite signs ⟹ net 0: SIGN-PAIR, char-blind ✓.  The
  seed pair directly instantiates W-D2(iv): j₀ 2 vs 5 = 2 + 1·e₀
  (e₀ = 3), w₀ 11 vs 10 = u₀ − 1·h₀ (h₀ = 1) — the exact structure
  behind PE1's G-1, seen live; and the pair realizes the K2-box's
  correction ↔ t-seed toggle.  Bottom survived elsewhere: slot (3,0,0)
  nets +r₂ − r₁ − r₂ = −r₁ ≠ 0 in F₃ (residue chain re-multiplied by
  hand: 1·1·2 = 2, 2·2 ≡ 1, 1·2 = 2) — a NETTED-SUM survivor whose
  vector (0,−1) is protected: SD-L7 case (a) live, bottom_surv ✓.
  Bonus: the same row's (0,1,0) group kills a correction-free
  junk-free cell against a 1-correction rider — one correction-free
  member only, as SD-L5 demands, and a live instance of why the
  cascade leg FAILS at g₀ ≥ 2 (out of SD-THM-A's locus, as boxed).

All hand arithmetic agrees with the artifacts and the note's displayed
mechanisms.

## §5. Charge 5 — fresh eyes

**N-1 (NOTE — DRV-SEEDY's coverage parenthetical undersells its own
count).**  Quote (S3 machine bracket, echoed in the SD-r1 bracket and
S7): "1,355 b₀-seeding splits recomputed directly (every d-cell on
every live row)".  In the runner the DRV-SEEDY loop
(survdisj_derive_checks.py:133–139) executes BEFORE the live-row gate
(line 161, `if kdef > ctop or not q2sink: return None`), so
sealed-phase rows that are traced but then rejected as non-live also
contribute splits: the live-only census is bounded by 693·1 + 286·2 =
1,265 < 1,355 (gap 90 = the non-live sealed contributions).  The
quantifier claim itself is TRUE — every live row's every d-cell IS
covered — and the surplus only widens the evidence for the any-seed
clause (i); but a reader reconstructing 1,355 as the live-only count
fails.  One clause ("plus traced non-live sealed rows") would cure it.
No proof step affected; F-D's "never observed in 1,355 splits" is a
bare count and stays accurate.  Classification: **NOTE** (display
precision in a machine bracket).

Checked and NOT findings: the "±" in SD-THM-A(iii) (conservative — both
signs are +, as PE1 noted); the brackets' "SD-L5 consumes only the
fork-counting" (over-states dependence in the safe direction; the
claims row is the accurate display); DRV-NEPS not machine-checking the
"at most one X-mate" sub-clause (vacuous on this roster — zero mates
observed — and the note claims only the observed {Ĉ} population);
SD-L2's claims-row scope (H1)–(H2) (conservative; LED_l is per-path
scope-free); defc counted per terminal path (the displayed reading).

## VERDICT BLOCK

* CRITICAL: none.  The SD-r1 pin is the correct, sharp repair,
  re-derived fresh from W-D1/W-D2(iii)(iv)/L-NORM(a)(b) with the
  falsity shape confirmed (h₀ ≥ 1 checked back to the class pin); all
  echo sites carry it; both consumers verified undamaged by direct
  re-reading (SD-THM-A's locus supplies the pin; SD-L5 consumes no
  SD-L4 clause).  All four PE1 note-cures faithful, the empirical
  replacements re-verified from the committed artifacts (9/9 CROSS
  off-bottom and off every survivor line; 693 = 979 − 286 with the
  unconditional SDI-SURV backstop read in the instrument source; the
  EMPTY cure confined to the header and matching commit 7314525).
  The whole spine re-derived standing alone: SD-L2 termwise from
  LED_l × S2.2, SD-L1 all three legs, the pool telescope and (★)
  (any-d₀, as (SD-YJ) needs), SD-L3's verbatim consumption,
  SD-THM-A(i)–(v) with pins exact and no rescoped-S-L4(iii)
  consumption, SD-L5/L6/L7, both boxes, the grade caps at all five
  sources' current heads.  Machine: all md5 pins green, both runners
  reproduce IDENTICALLY (non-elapsed artifact diffs empty), the
  two-commit seal genuine, headline censuses re-aggregated
  independently (P-A 693/693, PB-mult1-some 286/286, P-C 103/200
  refuted, M-B1 39, P-M1 census exact over 211 minimal survivors),
  and two FRESH hand-re-derivations (PXFLTF[123,123] K1;
  W3G2A[683,687] K2) agree with the artifacts cell for cell including
  the ledger cross-checks.
* GAPS: none.
* NOTES (1): N-1 — the DRV-SEEDY bracket's "(every d-cell on every
  live row)" parenthetical describes a proper subset of the 1,355
  counted splits (the loop also runs on traced non-live sealed rows;
  live-only max = 1,265); quantifier true, count accurate, framing
  imprecise.  No repair required for soundness.

This pass re-derived the round-1 repair text fresh (the stated purpose
of round 2 after verifier/repairer coincidence at SD-r1) and found it
correct.  0 critical, 0 gaps ⟹ this IS a CLEAN pass; the arc counter
moves to 1/2 CLEAN.  The model-diverse Codex leg remains owed before
any acceptance claim (F-E), and every grade stays capped by the W arc
(0/2 CLEAN) exactly as the note displays.

SURVDISJ-PE2 FINDINGS: 0 critical, 0 gaps
VERDICT: CLEAN
