# EMPTY-PE1 — hostile content verification pass 1 on EMPTY_PROOF_2026-08-08.md (commit 4eb1719)

Verifier: fresh-context Fable (PE1 of the (EMPTY) arc). Charge: quote-and-classify
(CRITICAL ERROR / JUSTIFICATION GAP / NOTE); fix nothing. Object: the (EMPTY-(m+1))
proof note at 4eb1719 (confirmed via `git log -1 --format=%h -- <file>`), its machine
leg `verification/openmath/empty_derive_checks.py` (md5 8fed92402bcffe6e0c536f1f9d847612
— matches the note's pin), upstream consumption WMULTDCX_2026-08-08.md (attempt grade,
0/2 CLEAN) and RMENGINE_2026-08-08.md ([RMG] accepted). Independent instrument:
`verification/openmath/empty_pe1_ext.py` (NEW file, this pass).

Protocol executed:
1. Re-derived E-L1 (telescope), E-L2/E-L2h (payment), E-L4 (unroll), E-L5 (c-plus
   chain + Y-tight classification), E-L6 (monomial Y-kill), and the S7 assembly + E-L7
   forcing FROM the consumed displays (LED_l, W-D2, W-D4, S2.2 inventory, L-NORM,
   DIGIT-SPLIT), independently of the note's proofs.
2. Read the full runner source; checked every verdict family's code against the lemma
   it claims to check.
3. Read-only re-run of the committed runner in a sandbox copy (/tmp/pe1_rerun):
   17/17 families reproduce with 0 violations; all counters, controls, per-row records
   and min-slack IDENTICAL to the committed artifacts (output/results md5 differences
   are exactly the elapsed-time fields; `violations/counters/controls/sealed/rows/
   min_pay_slack/tight_witnesses/provenance` compare SAME field-by-field).
4. All md5 pins verified: the 3 machine-leg files match the note's S0 pins; the 4
   consumed-runner pins (EDC-PIN dict) match the on-disk files; the salvage files match
   (design f4ff4a90…, runner bytes 6994bfc2… ≠ smoke self-pin, per the 8d1449b salvage
   record and the note's instrument disclosure).
5. Machine extension `empty_pe1_ext.py`: E-L5 exhaustive grid battery, the tight-
   stratum remainder lemma (the repair's key step), instance hunts for the S7 display,
   CTRL-PAY1 corner analysis + teeth, EDC-CPLUS guard probe, and 3 hand-traced fresh
   dead rows. Results quoted per finding below.

Verdict summary up front: the LEMMAS E-L1, E-L2, E-L2h, E-L4, E-L5, E-L6 are all
correct as displayed (each re-derived below); the THEOREM (EMPTY-(m+1)) is TRUE on
(H1)-(H3) — I re-derived it end-to-end with my own assembly. But the note's OWN
assembly step (the S7 "every slack collected on one side" display, from which E-L7 is
read off in one line) is FALSE AS PRINTED — refuted both by arithmetic and by the
batteries' own at-equality cells — and the one-line derivation of E-L7 from it is
therefore invalid as written. The repair needs a case analysis + one small lemma
(tight-stratum remainder vanishing) that the note nowhere states, though every
ingredient is present. Findings below.

---
## Numbered findings

### Finding 1 — CRITICAL ERROR. The S7 assembly as printed is invalid: the master
### slack display is FALSE (refuted by the batteries' own two-exit cells), and
### E-L7 is read off it in one line.

Quoted (S7, the assembled chain and display):

>     π₁ ≤ ⌊( t₁ + t·e₀ + Y₂ + Σ_{CE}(a_{c,0} + y_c) − Σ_{CE, i=0}(P₀ − e₀k_c − y_c) )/P₀⌋
>        ≤ c⁺₁(Y₂) + Σ_{CE, i≥1} ⌈(a_{c,0}+y_c)/P₀⌉ − 𝟙[some level-0 correction]
>        ≤ c⁺₁(Y₂) + #CE_{≥1} − 𝟙[CE₀ ≠ ∅]
>
> "and, for the last step, that each level-0 correction removes P₀ − e₀k − y ≥
> e₀ − 1 ≥ 1 from the numerator on the (H1) branches where level-0 corrections
> can matter"
>
>     k  ≤  c_{m−1} + 𝟙[Y-tight stratum ∧ Y₂ = 1]
>           − Σ_{l=2}^{m−1} ρ⁺_l·W_{l−1}     [E-L4/E-L5 unroll slack; = 0 iff remainders maximal]
>           − Σ_{CE, 1≤i≤m−2} (e_i − 1)·W_i  − (e_{m−1} − 1)·r
>           − 𝟙[CE₀ ≠ ∅]·W₁ − j_{m−1}(C) − Σ_{l=1}^{m−2} W_l·j_l(C)
>
> "Since k and c_{m−1} are integers: **Lemma E-L7 (forcing).** If k ≥ c_{m−1}+1
> then EVERY slack vanishes"

and, from the header: "every displayed intermediate machine-checked at instance
level".

Three concrete defects, each verified:

**(1a) The middle step of the π₁ chain (the unconditional −𝟙[CE₀] deduction) is
false arithmetic.** Removing ≥ 1 from a floor's numerator does not lower the
floor by 1 unless the numerator sits at a multiple of P₀. Explicit witness
(in-scope, d₀ ≥ 2 branch): e₀ = 2, g₀ = 2, P₀ = 4, t₁ = 4, d-cell t = 1, Y₂ = 0,
one level-0 correction (k = 1, y = 1, removal 1): line 1 = ⌊6/4⌋ = 1 but
line 2 = c⁺₁(0) − 1 = 0.  Grid census (empty_pe1_ext.py, EXT-MIDSTEP): the
printed step fails in 655 of the enumerated parameter cases.  The step IS valid
exactly where the E-L7 forcing needs it — on the Y-tight boundary with Y₂ = 1,
where the numerator t₁ + (g₀−1)e₀ + 1 ≡ 0 (mod P₀) — but only in the corrected
form of (1b): TRUE-ledger form 0 failures on the tight boundary (of 68 cases)
vs 511 failures unconditionally.

**(1b) The printed numerator double-counts the Y-dump of level-0 correction
edges.** Σ_{CE}(a_{c,0} + y_c) includes the i = 0 edges' y_c, and the removal
term −(P₀ − e₀k_c − y_c) re-adds y_c: the printed numerator equals
(σ₁ + jD₀ + dmp₀ − ccons₀) + Σ_{CE,i=0} y_c — an overcount of +y per level-0
Y-edge.  As line 1 (an upper bound) this is merely weak; but with it, the
−𝟙[CE₀] step fails EVEN on the tight boundary (6 of 68 grid cases, e.g.
e₀ = 2, g₀ = 1, t₁ = 1, k = 0, y = 1) — the printed chain is unrepaira­ble
without also correcting the numerator to the true ledger form, in which each
level-0 correction nets exactly −(P₀ − e₀k − y) ≤ −1.

**(1c) The master display is false under every reading of ρ⁺_l, and is refuted
by the batteries' own cells.** The symbol ρ⁺_l is never defined as a number
(E-L5 defines "ρ⁺_l-propagation" as a congruence condition); the bracket
"= 0 iff remainders maximal" forces the distance-from-maximal reading, the
E-L4 notation forces the plain-remainder reading. I evaluated all three
natural readings (A1 plain c-chain remainders, A2 plain c⁺(Y₂)-chain
remainders, B distance-from-maximal) on 492 two-exit cells re-walked from 195
live rows of 8 battery towers (EXT-DISPLAY): the display is VIOLATED on
290 (A1) / 283 (A2) / 437 (B) of the 492 cells — while the theorem's
conclusion k ≤ c_{m−1} holds on every one of them (0 breaches).  Two witness
shapes: (i) a two-exit cell at k = c_{m−1} on W3DEEP4 whose path took a
level-0 correction (the display then asserts k ≤ c − W₁ < k); (ii) a
correction-free, junk-free two-exit cell at k = c_{m−1} on a row with
non-maximal remainders (the display then asserts k ≤ c − Σδ·W < k).  The
derivation-level reason: summing the (valid) ingredient inequalities yields
k ≤ c⁺_{m−1}(Y₂) + Σ_{l≥2} ρ⁺_l·w_{l−1} − [correction/terminal slacks] — the
remainder term enters with a PLUS sign (headroom < 1 to be killed by
integrality), not as a subtracted slack; no sign-fix alone repairs the display
because the (1 − W₁)-sized headroom it silently drops is exactly what the
integrality step must absorb.  Consequently the header's "every displayed
intermediate machine-checked at instance level" is also wrong for this
display: EDC-BND checks only the WEAKER midpoint bound π_{m−1} ≤
Σ W_l(σ_{l+1}+jD_l) + Y₂W₀ + r (which I re-derived as a true consequence of
E-L1 + E-L2 — that family is sound); the master display itself was never
machine-checked, and is instance-false.

**Why this is CRITICAL and not a gap:** the display is asserted for every
two-exit path, it is false on 59–89% of the two-exit cells the program has
ever produced, and the note derives E-L7 — the load-bearing forcing that
feeds E-THM — from it in a single sentence.  As written, the chain from E-L1
… E-L5 to E-L7 is broken.

**The theorem survives — full repair (my derivation, every ingredient already
in the note).**  Fix a two-exit path, (H1)–(H3), TRACK.  (R1) Truncated E-L1
at level 1 + LED₀ with j₀ ≥ 0:  k = π_{m−1} − e_{m−1}r − j_{m−1}(C), and
π₁ ≤ ⌊(t₁ + te₀ + Y₂ + Σ_{CE,i≥1}(a₀+y) − Σ_{CE,i=0}(P₀−e₀k−y))/P₀⌋ (true
ledger form).  (R2) Peel the i ≥ 1 edges by floor subadditivity; each ⌈⌉W₁
unit is paid by E-L2h, which simultaneously leaves the strict loss:
Σ_{1≤l<i}a_lW_l + ⌈(a₀+y)/P₀⌉W₁ ≤ W_i ≤ (P_i−e_ik)W_i − (e_i−1)W_i, and at
i = m−1 the dump value ≤ 1 against cost e_{m−1}.  (R3) The c⁺-unroll at
levels ≥ 1 (W_l = w_l under (H3)) gives EXACTLY W₁c⁺₁(Y₂) + Σ_{l≥2}t_lw_{l−1}
= c⁺_{m−1}(Y₂) + Σ_{l≥2}ρ⁺_l w_{l−1}, ρ⁺_l := (t_l + c⁺_{l−1}(Y₂)) mod e_{l−1}.
Assembling:  k ≤ c⁺_{m−1}(Y₂) + Σ_{l≥2}ρ⁺_l·w_{l−1} − Σ_{CE,1≤i≤m−2}(e_i−1)W_i
− (e_{m−1}−1)r − [CE₀ term, so far omitted] − j_{m−1}(C) − Σ W_l j_l(C).
(R4) Now suppose k ≥ c_{m−1}+1 and case-split.  If Y₂ = 0 or the row is off
the Y-tight stratum: c⁺_{m−1}(Y₂) ≤ c_{m−1} (E-L5) and Σρ⁺w ≤ 1 − w₁ < 1
forces k ≤ c_{m−1} + (1−w₁) < c_{m−1}+1, contradiction.  So Y₂ = 1 AND the
row is Y-tight (this also disposes of d₀ = 1 outright via L-NORM(c)).
(R5) THE KEY STEP THE NOTE NEVER STATES: on the Y-tight stratum the +1 rides
the boundary at EVERY level — c⁺_l(1) = c_l + 1 for all 1 ≤ l ≤ m−1 and the
c⁺(1)-chain remainders VANISH: ρ⁺_l = 0 for every 2 ≤ l ≤ m−1 (since
t_l + c_{l−1} ≡ e_{l−1}−1 gives t_l + c_{l−1} + 1 = e_{l−1}(c_l+1) exactly).
[Machine: EXT-TIGHT-RHO, 4,468 tight grid cases, 0 failures.]  So the entire
slack budget collapses to ZERO: c_{m−1}+1 ≤ k ≤ (c_{m−1}+1) + 0 − Σ(e_i−1)W_i
− (e_{m−1}−1)r − [CE₀] − j-terms.  (R6) On this forced corner the CE₀ term
IS valid: the level-0 numerator sits at a multiple of P₀ (t₁+(g₀−1)e₀+1 ≡ 0
mod P₀; a non-worst d-cell t < g₀−1 lowers it by ≥ e₀), and each level-0
correction removes P₀−e₀k−y ≥ e₀−1 ≥ 1 (d₀ ≥ 2 ⟹ e₀ ≥ 2), dropping c⁺₁(1) by
≥ 1.  [Machine: EXT-MIDSTEP true-form, 0/68 tight-boundary failures.]
(R7) Hence at d₀ ≥ 2 ((H1): all e_i ≥ 2 including the top): every correction
slack is strictly positive, so CE = ∅, r = 0, j_l(C) = 0 — E-L7(a)+(b) — and
E-L6 kills Y₂ = 1 on the correction-free prefix: contradiction.  E-THM holds.
This repair consumes nothing beyond the note's own pins.

### Finding 2 — JUSTIFICATION GAP. The tight-stratum remainder-vanishing lemma
### (repair step R5) is nowhere stated, and without it "every slack vanishes"
### does not follow even from a sign-corrected display.

Quoted (S7): "Since k and c_{m−1} are integers: Lemma E-L7 (forcing). If
k ≥ c_{m−1} + 1 then EVERY slack vanishes".  Integrality of k and c alone
yields only k ≤ c⁺_{m−1}(Y₂) (killing the fractional headroom Σρ⁺w < 1); at
k = c_{m−1}+1 = c⁺_{m−1}(1) it leaves the real-valued budget Σρ⁺w ≥ 0
available to absorb correction losses — a correction edge with
(e_i−1)W_i ≤ Σρ⁺w would NOT be forced out.  The forcing needs the exact
identity that ON the Y-tight stratum with Y₂ = 1 the c⁺(1)-chain remainders
are all ZERO (R5 above), so the budget is not merely < 1 but = 0.  This is
one displayed line of arithmetic ((t_l + c_{l−1}) + 1 = e_{l−1}(c_l + 1)) and
is machine-true (EXT-TIGHT-RHO 4,468/4,468), but it is a distinct lemma the
note must display; E-L5(ii) as stated gives only the top value
c⁺_{m−1}(1) = c_{m−1}+1, not the level-by-level remainder collapse.

### Finding 3 — JUSTIFICATION GAP. The CTRL-PAY1 disclosure names an impossible
### corner; the REAL tightness corner is different, in-scope, and inventory-
### realizable on two committed towers — the control's non-firing is a genuine
### coverage hole, not structural headroom.

Quoted (S3 machine bracket): "control CTRL-PAY1 (tightening by W₀ must fire)
did NOT fire: the exact-tightness corner (e_i = 1 with maximal dump vector AND
the Y-child) is not realized in these batteries — DISCLOSED, S8."  And S8(i):
"the tightness corner (e_i = 1, maximal dump vector, plus Y-child) is not
realized in these batteries; … the corner is instance-unprobed."

Adjudication of the flagged control question, by exact corner enumeration
(EXT-PAY, 8,308 in-scope corner cases) plus roster inventory scan:

* The NAMED corner is CLASS-EMPTY under (H1): e_i = 1 at an interior level is
  only in T-scope on the d₀ = 1 branch, where the Y-child is identically
  absent (L-NORM(c)).  At that corner (e_i = 1, full house, y = 0) the slack
  is exactly W₀ — which does NOT fire CTRL-PAY1 (fires iff slack < W₀
  strictly).  So the disclosure's corner could never have fired the control
  on any in-scope instance: as written it explains nothing.
* The ONLY in-scope sub-W₀ corner is: i = m−1 (payment ≤ 1 regardless of
  e-values), FULL-HOUSE dump vector a_l = P_l − 1 at every l ≤ m−2, AND the
  Y-child, at d₀ ≥ 2 — slack exactly 0.  All 150 sub-W₀ cases in the 8,308-
  case enumeration are this corner and no other.
* That corner is NOT exotic: 14 of the 35 roster towers carry a full-house
  top-level d-cell in their committed correction tables, including TWO at
  d₀ = 2 (XM3B: a⃗ = (3,2); EQ3G2A: a⃗ = (3,2)).  What the batteries never
  realized is a PATH reaching such a correction with a coefficient whose
  DIGIT-SPLIT has Φ₀-overflow (nonzero Y-child).  The detector logic itself
  is sound: fed the synthetic corner edge it fires (EXT-PAY self-test).
* The measured "min slack 1/12 — comfortably positive" (S3) is exactly W₀ of
  the g₀ = 2 towers (1/(P₀P₁) = 1/12), attained at a second-tightest corner
  (witness edge: W3G2B, i = 0, k = 1, y = 1, slack = W₀ exactly): the payment
  inequality runs at ZERO margin above the control threshold, not
  "comfortably".
* E-L2 ITSELF IS SOUND — re-derived from the RMENGINE inventory bounds
  (a_l ≤ P_l−1, k ≤ g_i−1, y ≤ 1); no countermodel exists given those pins,
  and equality at the top corner does not hurt the assembly (top corrections
  are killed by the e_{m−1}-cost of E-L3, not by payment slack).  The gap is
  purely in the disclosure: it should say the corner that matters is the
  top-full-house-Y corner at d₀ ≥ 2, that it is inventory-present in XM3B/
  EQ3G2A, and that the batteries' paths never realized it.

### Finding 4 — NOTE. Two machine-bracket accuracy items.

(i) The EDC-CPLUS guard "the Y-unit crossed the level-0 floor off tight₀"
(quoted in the E-L5 machine bracket as evidence: "the guard … never fired")
is a PHANTOM check: its firing condition is satisfiable by clean in-scope
arithmetic with every E-L5 clause holding — e.g. e₀ = 2, g₀ = 2, t₁ = 5 gives
c⁺₁(1) = 2 > c⁺₁(0) = 1 with tight₀ false, while (i)/(ii)/classification all
hold (c₁ = 2).  Crossing c⁺₁(0) is not the event E-L5(ii) bounds (that event
is crossing c₁).  Its non-firing is roster coverage, not law; a future
battery hitting t₁ ≡ e₀−1 (mod P₀) with q ≥ 1 at g₀ ≥ 2 would report a
phantom EDC-CPLUS violation.  (E-L5 itself is unaffected — see the positive
section: exhaustive grid, 0 failures.)

(ii) S7's "The Y-tight stratum is populated: 116 traced rows … — all dead":
"all dead" is definitionally forced, not a census outcome — the runner's
tight flag conjoins kdef = c_{m−1}+1 (which implies law-dead) with the E-L5
arithmetic; rows on the E-L5 stratum with other deficits are not counted.
The populated-corner claim itself stands (116 rows, 12 at d₀ ≥ 2).

### Finding 5 — NOTE. The header's consumption range "(W-D0–W-D7)" is loose:
S0 and the dependency line correctly exclude the W-D7 (STK)/law-clause pins
("NOT consumed") and W-D5; the header parenthetical reads as if all of
W-D0–W-D7 were consumed.  Cosmetic, but the grade-cap sentence is the
note's most-quoted line and should name the consumed set exactly.

---
## Positive verification record (per the charge, items 1-5)

**E-L1 (charge 1) — CORRECT, re-derived.** From LED_l (W-D3, consumed): along
any path, cons_l for l ≤ m−2 decomposes as P_l·π_{l+1} + ccons_l (each
promotion out of level l consumes P_l; a path takes one child per reduction;
exits consume only at m−1 — checked against the S2.2 child inventory).  Then
W_l(σ_{l+1}+jD_l+dmp_l−ccons_l−j_l) = W_l(P_lπ_{l+1} − π_l) and
Σ_{l=0}^{m−2}(W_{l+1}π_{l+1} − W_lπ_l) = π_{m−1} (π₀ = 0, W_lP_l = W_{l+1},
W_{m−1} = 1) — EXACT, and in fact at every NODE, not only terminals (LED_l is
per-node; the note claims terminals only, which is fine; the machine's
terminal-only coverage is disclosed via the W-D3 consumption line).  The
stage-2 seed's Y₂ rides inside dmp₀ consistently in note and runner.  E-L1 is
scope-free as claimed.  Machine: EDC-TEL re-run 0/22,261; CTRL-TEL0 fired
11,731; my independent recomputation at the EXT-TRACE rows agrees.

**E-L2 / E-L2h (charge 2) — CORRECT, re-derived; no countermodel exists.**
Pure form: Σ_{l<i}a_lW_l ≤ Σ(P_l−1)W_l = W_i − W₀ (telescope), +yW₀ gives
≤ W_i ≤ e_i(g_i−k)W_i = pay (k ≤ g_i−1); at i = m−1 the same telescope gives
≤ 1.  Hybrid: telescope from level 1 plus a₀+y ≤ P₀ ⟹ ⌈·⌉ ≤ 1 worth W₁.  The
only inventory inputs are a_l ≤ P_l−1 (reduced C_k digits, RMENGINE S2.2,
accepted), a_l = 0 for l ≥ i, one +1 at level 0 per Y-child, k < g_i — hunted
for a countermodel corner and found none: with those pins the bound is forced;
extreme digit patterns can only attain equality (top full house + Y, slack 0),
never exceed.  Both simultaneously-needed consequences in the assembly
(⌈⌉W₁-unit cancellation AND the (e_i−1)W_i strict loss) fit under the same
W_i: verified, since Σ+⌈⌉W₁ ≤ W_i ≤ (P_i−e_ik)W_i − (e_i−1)W_i.  CTRL-PAY1
adjudication: Finding 3.  Machine: EDC-PAY/EDC-PAYH re-run 0/54,615; my
re-walk 301 edges, min slack 1/12 = W₀ with the slack-=-W₀ edge exhibited.

**E-L4/E-L5, the hard core (charge 3) — CORRECT, re-derived + exhaustively
machine-tested.**  E-L4: unrolling c_l = (t_l+c_{l−1}−ρ_l)/e_{l−1} gives
c_{m−1} = Σt_l·w_{l−1} − Σρ_l·w_{l−1} exactly, and Σρ_lw_{l−1} ≤ Σ(e_{l−1}−1)
w_{l−1} = 1 − w₀ (telescope) — g-free arithmetic, correctly labeled.
E-L5(i): with t₁ = qe₀+s, the displayed equivalence chain
t₁+(g₀−1)e₀ < (q+1)e₀g₀ ⟺ q−1+s/e₀ < qg₀ checks at q = 0 and q ≥ 1; upper
floors monotone.  E-L5(ii): c⁺₁(1) ≥ q+1 ⟺ s+1+(g₀−1)e₀ ≥ qe₀(g₀−1)+e₀g₀
with LHS ≤ e₀g₀ (eq iff s = e₀−1) and RHS ≥ e₀g₀ — forces q(g₀−1) = 0 ∧
s = e₀−1 = tight₀, exactly as displayed; never +2 (t₁+(g₀−1)e₀+1 ≤ t₁+P₀);
above level 0 the +1 survives iff remainder maximal, level by level.  The
g₀-freeing mechanism is real: the worst non-principal d-cell excess (g₀−1)e₀
is absorbed because the level-0 divisor is P₀ = e₀g₀, not the law's literal
e₀ — both channels priced by one floor.  The stratum boundary machine test
the charge asked for: EXT-GRID-EL5, 61,317 grid cases over m ∈ {2,3,4},
e ∈ {1,2,3}^{m−1}, g₀ ∈ {1,2,3}, t-vectors through 3 periods — (i), (ii)-cap,
and the EXACT (+1 ⟺ Y-tight) classification: 0 failures; EXT-GRID-EL4
20,439 cases 0 failures; EDC-UNROLL/EDC-CPLUS re-run 0 violations.

**E-L6 (charge 4) — CORRECT on the displayed canonicity pin.**  deg b = 0 ⟹
b̂ is a unit scalar ⟹ deg(b̂ĉ) = deg ĉ < d₀ ⟹ the CANONICAL Ŷ =
quo(b̂ĉ, Φ₀) = 0.  Important and verified: the decomposition lift + πX + Φ₀Y
is NOT unique without the canonicity pin (Y ≡ 0 mod π alternatives exist), so
E-L6 genuinely consumes "the canonical Y = quo of the primitive product by
Φ₀" — which the note displays in S0 and which EDC-YMON(a) enforces at every
digit_split call (0/… violations; 1,373 nonzero-Y calls elsewhere = the
detector's teeth).  Monomiality IS forced exactly by correction-freeness: per
S2.2 + W-D1, the only b-mutating edges are correction edges and the stage-2
seeding; junk children exist only AS members of those L-NORM splits, so the
charge's "promotion-only path through junk children" cannot occur — a
promotion-only stage-1 prefix carries b = π^{u₁+u₁′} verbatim (u₁+u₁′ ≥ 0 by
W-D2(0) under (H3), consumed).  Machine: EDC-YMON both clauses re-run clean;
all 61 Y₂-edges sit on corrected prefixes.

**E-L7 (charge 4) — statement TRUE, derivation as printed invalid (Finding 1);
slack-by-slack audit under the repair:** Y₂/tight forced by integrality
against the < 1 headroom (no slack silently assumed integral — the ONLY
integrality used is k, c ∈ ℤ); interior corrections killed by (e_i−1)W_i > 0
(needs (H1) d₀ ≥ 2 branch, displayed); top corrections by (e_{m−1}−1)r > 0
(needs e_{m−1} ≥ 2 — the note correctly flags that the (H1) d₀ ≥ 2 branch
bounds the TOP e too; at d₀ = 1 with e_{m−1} = 1 a full-house top correction
has exactly zero net loss, but there the forcing never reaches (b): Y₂ = 1 is
already impossible, matching the note's own "at d₀ = 1 nothing is needed");
level-0 corrections by the tight-boundary floor drop (R6); terminal
exponents by weight positivity; the unroll slack by R5.

**Scope hygiene (charge 5) — CLEAN.**  (H3) displayed at every consumption
site I could find: E-L5 statement, the S5 d-cell inventory line, the S7
assembly opening, the weights remark (W_l = w_l for l ≥ 1), the theorem box,
claims table, F-A.  The grade-cap sentence is present, correct, and repeated
at the dependency line and the (SURV)(ii) bullet; every PROVED row says
"attempt".  (SURV)(ii)'s derivation from E-THM + W-D0 (T² computes Q¹, (H1))
is valid and carries the cap.  (EMPTY-gen) and (SURV)(i) boxes are honest
(the (i)-box correctly says this note only bounds paths above).  Machine-
coverage fences (F-D, S8(ii)-(iv)) match the artifacts exactly (I re-summed:
1,380 = Σ fresh censuses; 793 = Σ fresh dead; 616 = 126+490; 490 vs 303
untraced; caps 24/10 per stratum match the runner; 22,261/54,615/1,009/116/
61 all reproduce).  No claim exceeding the pins found beyond Findings 1-5.

## Machine section (charge 6)

* Commit confirmed: note last touched at 4eb1719; runner/output/results md5s
  match the note's pins (8fed924… / ddae4007… / 229a1b1…); the four consumed-
  runner pins match on-disk files; salvage files match the 8d1449b record
  (design f4ff4a90…, runner bytes 6994bfc2…).
* Read-only re-run (sandbox copy, /tmp/pe1_rerun): exit 0, 17/17 verdict
  families at 0 violations; counters, controls, min-slack, tight witnesses,
  sealed 412/858/126, and ALL per-row records identical to the committed
  results json (only elapsed-time fields differ — the committed output md5 is
  therefore not reproducible bit-for-bit, as expected for a wall-clock-
  stamped log; every semantic field compares SAME).
* Sealed-selection replication: the selection block of run_sealed_tower is a
  structural copy of wmultdcx_derive_checks.run_tower (same want/cap/sort
  keys) — the 412/858/126 EDC-SEAL reproduction is genuine, not a re-tuned
  selection.
* New instrument: verification/openmath/empty_pe1_ext.py (md5
  44d032e1f4edddb026dc210a778fc287), output empty_pe1_ext_output.txt
  (42e2f3dcb9bca1d2f02785f80ae6120b), results empty_pe1_ext_results.json
  (74076344623bc7c44392e7a4afb7d2bb); 0 instrument failures, 0 engine-harness
  violations during its walks.  Sections: EXT-GRID-EL4 (20,439), EXT-GRID-EL5
  (61,317), EXT-TIGHT-RHO (4,468), EXT-MIDSTEP (note-form 655 fails/6 on
  tight boundary; true-form 511/0), EXT-DISPLAY (195 rows, 492 cells,
  290/283/437 display violations, 0 theorem breaches), EXT-PAY (8,308
  corners; 14-tower full-house inventory; detector self-test fires; slack=W₀
  edge), EXT-CPGUARD (phantom demo), EXT-TRACE (3 rows).
* Hand traces (3 fresh dead rows through E-L1/E-L5, numbers re-derived by me
  and machine-confirmed):
  - EQ3T4A row (993,999), e = (2,2,4), g = (1,1,1), d₀ = 1: σ = (1,2,3),
    s(u) = (0,0,1) ⟹ t = (1,2); c-chain: c₁ = ⌊1/2⌋ = 0, c₂ = ⌊(2+0)/2⌋ = 1;
    D = 3+1 = 4, k = 2·4 − 4 = 4 > 1+2 headroom: c⁺(0) = c⁺(1) = 1, not
    tight; max fundable π₂ ≤ c₂ + 1 = 2 < 4 = k.  Walk: 1 stage-1 exit, ZERO
    two-exit terminals; telescope exact at each terminal.
  - EQ3G2A row (2305,2321), e = (2,3,3), g = (2,1,1), d₀ = 2 (the g₀ = 2 ∧
    d₀ = 2 corner): σ = (2,3,2), s(u) = (0,1,1) ⟹ t = (2,4); c₁ = ⌊2/2⌋ = 1,
    c₂ = ⌊(4+1)/3⌋ = 1; k = 6−3 = 3 (c ≤ k−2 stratum); c⁺₁(0) =
    ⌊(2+2)/4⌋ = 1 (the non-principal excess t·e₀ = 2 absorbed by P₀ = 4),
    c⁺(1) = 1, not tight (t₁ = 2 ≠ e₀−1 = 1).  ZERO two-exit terminals.
  - EQ4T3A row (2305,2309), m = 4, e = (2,2,2,3), g ≡ 1, d₀ = 1: σ =
    (1,0,2,2), s(u) = (1,0,0,1) ⟹ t = (2,0,2); c-chain (1,0,1); k = 3;
    c⁺(0) = c⁺(1) = 1, not tight.  ZERO two-exit terminals.
  All three: kdef > c_{m−1}, no two-exit path — E-THM instance-true; the
  E-L1 telescope re-verified exactly at every terminal I recomputed.

## Verdict block

E-L1, E-L2, E-L2h, E-L4, E-L5, E-L6: PROVED as displayed (each re-derived
here, each with clean machine legs).  E-THM/(EMPTY-(m+1)) and (SURV)(ii): the
STATEMENTS are true on (H1)-(H3) — independently re-derived in this pass via
the repair of Finding 1 — but the note's own S7 assembly (the master slack
display and the one-line E-L7 read-off) is false as printed and must be
rewritten (Findings 1-2) before the note can count a clean pass; the CTRL-
PAY1 disclosure must name the real corner (Finding 3).  Grade cap correctly
carried; scope hygiene otherwise clean; machine leg reproduces exactly.

Chain verdicts: E-L1 VALID · E-L2/E-L2h VALID (tightness corner
re-adjudicated, Finding 3) · E-L3 consumed at grade · E-L4 VALID · E-L5 VALID
(exhaustive grid) · E-L6 VALID on the canonicity pin · S7 assembly INVALID AS
PRINTED (repairable, repair supplied and machine-verified) · E-L7/E-THM
statements TRUE, derivation broken as written · (SURV)(ii) rides the same.

EMPTY-PE1 FINDINGS: 1 critical, 2 gaps
VERDICT: NOT-CLEAN
