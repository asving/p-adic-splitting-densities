# ITER-LAW hostile pass PE — Fable execution leg (F2c from-note reimplementation + sealed re-run) + full hostile content read

**Pass:** PE (Fable leg; execution + content; model-diverse counterpart to the Codex
content pass PC). **Target:** `lean/notes/openmath/ITERLAW_2026-08-08.md` (the ITER-LAW
proof note, attempt grade, acceptance counter 0/2 at pass start). **Statement of
record:** `lean/notes/openmath/DITER_RESTATE_2026-08-08.md` §S2 (ITER-LAW display),
verified byte-identical to commit 242ba1e at pass start (no concurrent bracket
growth). **Discipline:** quote-and-classify; CRITICAL = breaks the logical chain,
GAP = assume conclusion and keep verifying downstream; nothing fixed. F2c ordering
honored STRICTLY: the reimplementation `verification/openmath/iterlaw_f2c_reimpl.py`
was written and run to green from the note text ALONE; the sealed falsifier
`verification/openmath/iterlaw_check.py` was opened only afterwards.
**Wallclock:** 2026-08-03.

## VERDICT BLOCK

**FINDINGS: 0 critical, 0 gaps.**
**VERDICT: CLEAN.**

* **F2c from-note reimplementation (verifier-owned, seed 20260803): ALL GREEN, exit
  0.** 89,056 samples / 0 violations over 21 check families on 6 fresh verifier rows
  (all four base rings, d0 in {1,2}, E2 up to 8); all 4 mutation controls DETECTED;
  all coverage duties MET. The note text alone was SUFFICIENT to reimplement the
  entire calculus and every load-bearing lemma — no underspecification was hit.
* **Sealed re-run: exit 0, ALL GREEN, 35,232 samples, 0 violations** — every number
  matches the note's S8 verdict block exactly (per-family table in the execution
  record below), including Case-II coverage [36,36,36,36,72,72,72,72] MET and F10
  NOT-CYCLIC 4/4 with exact value-set match. Runner byte-untouched (md5 equals seal
  commit ab7c31c); the committed `iterlaw_check_results.json` was reproduced
  byte-identically by the re-run (deterministic).
* **Semantic diff (reimpl vs sealed+harness): NO disagreement about what the note
  pins.** Three value-identical implementation variants documented as observations
  O1-O3 below; none is a semantic divergence on the harness tower class.
* **Content read: every proof step re-derived by hand** (L1-L7, Lemma EXP incl. the
  Bezout delivery of the exponent identity, Case-II reduction incl. the sign
  -psi0(0) = z1 and the exactness of the two-digit development, case exhaustion,
  S5 assembly, COR-1..5, S6.6): no critical error, no justification gap found.
  Recovered-not-consumed HOLDS (no W-MULT / Thm 4.2/4.8 / GMN semantics in the
  chain); residuals honesty HOLDS (ITER-LAW-LIFT open exactly at g0 = 1 AND
  delta1 = 1; gr(w2) wrapper conditional on the GRB retarget; orders >= 3 untouched;
  fences honored — commit file-lists checked).

## 1. Findings

None. (No numbered findings; the pass is CLEAN.)

## 2. Observations (non-findings; no logical weight)

**O1 (below-line digits).** Note S0: "a digit contributes iff w0(b) = u(beta)−m h0
exactly (else 0; digits strictly below the line do not occur when w1(a) >= beta)".
The harness `R1w` instead RAISES on a below-line digit
(`raise AssertionError("R1w: digit below line...")`) where the note's rule would
return 0. On the class both agree: a grid digit with w0 below the required ordinate
would have level-1 weight < beta <= w1(a), contradicting minimality — the note's
parenthetical is a true assertion and the harness guard is unreachable in every use
here. Value-identical; not a pin disagreement.

**O2 (above-the-line digits in the R2 read).** The note's C_j rule zeroes off-line
digits by the on-line test `w1(a_{s_j}) = gamma_j`. The harness `R2w` instead
computes the inner read whenever `vals[sj] >= gj` and relies on it evaluating to 0
for strictly-above-line digits (every grid digit then fails the exact-w0 test — same
minimality argument as O1, one level down). Provably value-identical; my
reimplementation used the note's reading and agreed with the sealed run on every
overlapping claim.

**O3 (negative slot weights).** The harness `R2w` hard-zeroes slots with gj < 0
(`if a and gj >= 0`); the note's definition needs no such guard — for gamma_j < 0
the on-line test fails automatically since w1 >= 0 on nonzero O[x] polynomials.
Value-identical.

**O4 (class scoping vs the statement of record).** The DITER_RESTATE §S2 setting
carries E2 = e0*e1 > 1; the note proves the display for e0 >= 1, e1 >= 1 — a
SUPERSET of the pinned setting (sound direction; nothing lost). The (ITER-LAW)
display itself is verbatim (provenance appendix, slice A vs slice B). The
restatement's "anchor window" is sharpened by the note to W = {gamma : u1(gamma)
>= 0} with closure proved (L3); every harness window (Composite.Gamma0-based) is
inside W.

**O5 (citations and freshness verified).** The note's harness line-cites are exact
(`Tower.__init__` std-lift loop at grb_order2_check.py:499–507; gamma2 at :510).
The sealed rows P,Q,R,S,U,V,W verified FRESH against the full 13-row strata roster
(A–E, G–N, from grb_order2_check.py:1128–1137 + strata_probe.py NEW_ROWS); X =
(2;2,1,1;2,1,2) is exactly the row-N shape, as declared. The S8 sample-count
arithmetic closes exactly: 468+2604+2604+516+4108+2604+156+1736+20000+4+432 = 35,232.

**O6 (reimpl row-shape coincidences — disclosure).** My six verifier rows were
chosen BEFORE opening the sealed script or the strata roster. Post-hoc comparison:
VC (1;1,2,2;3,2,1) coincides in shape with strata row B, and VF (2;4,3,1;2,1,1)
with sealed row Q; the INSTANCES differ (my seeded psi0/psi1 picks are my own,
seed 20260803; e.g. VF runs over F3[[t]] with psi0 = y + 2X). The other four rows
(VA, VB, VD, VE) are off both rosters in shape. Blind-choice overlap does not
contaminate the F2c independence claim (the implementation, not the rows, is the
decorrelated leg); recorded for honesty.

## 3. Content-read log (what was checked, step by step)

**Statement-of-record match.** The note's S0 THEOREM display equals DITER_RESTATE
§S2's (ITER-LAW) display verbatim (slices A/B in the appendix), with the note
supplying the precise domain (gamma, gamma' in W, closure by L3) and the
delta2 in {0,1} clause (L1 at level 2). Scoping per O4.

**L1 EQ12-ADD.** 0 <= s+s' <= 2e−2 gives delta in {0,1}; s+s'−delta*e lands in
[0,e) in both branches; adding the defining equations + uniqueness. Checked incl.
the e = 1 edge (s = 0, delta = 0) and exact-multiple edge s+s' = e (delta = 1,
s'' = 0). Sound. [My draws: 24,000 samples/0; sealed F9 inside 20,000/0.]

**L2 INNER-SHIFT.** Substitution of L1-level-2 into gamma1 = u2 − s2*w1Phi1;
the delta2(h1 + e1*w1Phi1) = delta2*gamma2 collection is exact. Sound.
[12,000 draws/0.]

**L3 WINDOW.** delta2 = 0 branch: u(beta'') = u+u'+delta1*h0 >= 0. delta2 = 1
branch re-derived: e0*u(beta'') = e0(u+u') + (s+s'−s'')h0 + gamma2 with
s+s'−s'' >= −(e0−1) and gamma2 = e0e1g0h0 + h1 >= e0h0 + h1, so e0*u(beta'')
>= h0+h1 > 0. Checked at e0 = 1 (s-terms vanish) and e1 = 1 (branch never fires,
delta2 = 0). Sound. [1,584 window pairs/0.]

**L4 EPS-CLOSED.** ell0*beta = ell0*e0*u + (1−ell0p*e0)s, so s − ell0*beta =
e0(ell0p*s − ell0*u): integrality and the exponent identity simultaneously — the
Bezout input is exactly 1 = ell0*h0 + ell0p*e0. Sound; e0 = 1 edge (ell0 = 0,
ell0p = 1, eps1 == 1) consistent. [12,000 integer draws + 1,200 field draws/0.]

**L5 EPS-MULT.** Exponent bookkeeping via L4 twice + L1; the delta1 terms cancel.
Equality of z1-powers concluded from equality of INTEGER exponents (the safe
direction — no order-of-z1 issue). Sound. [12,000 + 1,200 field/0.]

**Lemma EXP (the compose kernel).** Verified that the Bezout argument delivers the
exponent identity: substituting s(beta+beta') = s+s'−delta1*e0 (L1) and
ell0(beta''−beta−beta') = ell0*gamma2*delta2 into the left side collapses the
delta1 terms and yields (s+s'−s(beta'')+ell0*gamma2*delta2)/e0 exactly;
integrality flows from L4 applied at beta+beta' and beta'' (each quotient an
integer), NOT from the conclusion — no circularity. Sound. [12,000 draws/0;
sealed F9.]

**L6 ANCHOR-VAL.** Single-digit development at slot s2 (degree bound
s1*d0 <= (e0−1)d0 < e0*g0*d0), w1(a) = beta, w2(phi_gamma) = gamma; grid j = 0
only; inner read m = 0 digit pi^{u1} with exact ordinate u(beta) contributing 1.
val = eps1(beta) != 0 (z1 != 0, K2 a field). Sound. [128 anchors/0 incl.
single-slot shape; sealed F1 468/0.]

**L7 PAIR-VAL, Case I (S1 < e0*g0).** Single digit A = pi^U Phi0^{S1} at
UNREDUCED slot S2; w2(P) = gamma'' via L2/L1; slot j = delta2 on the s2''-grid;
slot weight = beta+beta' on-line; inner read puts pi^U at inner slot m = delta1
with exact ordinate U = u(beta+beta')−delta1*h0, contributing z1^{delta1}.
Exhaustion: g0 >= 2 forces Case I (2e0−2 < e0g0); g0 = 1 splits exactly by
delta1. Sound.

**L7 PAIR-VAL, Case II (g0 = 1, delta1 = 1).** The standard lift at g0 = 1 is
EXACTLY Phi1 = Phi0^{e0} + chat*pi^{h0} (verified against the S0 lift formula:
lift(psi0,0)*pi^{h0} + Phi0^{e0}); substituting Phi0^{e0} = Phi1 − chat*pi^{h0}
gives the two-cofactor expression, and BOTH cofactors have degree < deg Phi1
(deg A1 = S1''d0 <= (e0−2)d0; deg A0 <= (e0−1)d0 − 1), so by uniqueness it IS the
development — the reduction is exact, one step, no tail. Weight bookkeeping:
w1(A0) = beta+beta', w1(A1) = beta+beta'−e0h0; slot S2+1 line value =
gamma''+h1 > gamma'' (g0 = 1 makes gamma2−e0e1h0 = h1); at e1 = 1 the A1 digit is
on-grid but strictly above the line (slot weight = w1(A1)−h1), read 0 by the
on-line test; at e1 >= 2 it is off-grid (S2+1 incongruent to s2'' mod e1). Sign:
res(−chat) = −c0 = z1 in K1 = K0[z1]/(z1+c0) — the SAME z1^{delta1}. delta1 = 1
forces e0 >= 2 (e0 <= S1 <= 2e0−2). Sound. [My Case-II coverage 416 pairs/0 on
rows VA/VB/VF; sealed F4 516/0 with the development identity checked digit-exactly.]

**S5 assembly.** c = val(P)/val(phi_{gamma''}) with the denominator a unit (L6);
Lemma EXP applied at (beta, beta', delta2) with beta'' = gamma1(gamma+gamma')
matching L2, and EXP's delta1 equal to L7's (s(beta) = s1 by definition);
s(beta'') = s1(gamma+gamma') by definition. The displayed D and the z-bar carry
assemble exactly. Sound. [1,584 theorem pairs/0; sealed F3 2,604/0.]

**COR-1.** Lemma EXP's integrality clause verbatim. [1,584 + sealed 2,604/0.]

**COR-2 (B0a), both proofs.** Structural: c = zbar-carry times the coboundary of
F = eps1 o gamma1; the delta2 2-cocycle identity re-derived from L1-level-2
telescoping (both associations equal the symmetric total carry — INTEGER identity,
so the zbar-exponents match without any order caveat). Closed-form: s1-telescope +
symmetric delta2-total, both multiplied by the SAME 1/e0. Sound. [Sealed F5
4,108/0 measured AND closed-form.]

**COR-3.** e0 = 1: numerator identically 0 (s1 == 0, ell0 = 0) — D-REAL's carry
law verbatim, Case I only. e1 = 1: delta2 == 0 and D = delta1 by L1. Sound.
[My dedicated degenerate rows VC/VD 72+72 pairs/0; sealed F7 156/0.]

**COR-4 (B0c).** gamma+E2 fixes s2, shifts u2 by e0, gamma1 by e0, u1 by 1:
phi_{gamma+E2} = pi*phi_gamma exactly; all s-values and carries depend only on
residues mod E2. The gauge caveat (eps1(beta+e0) = eps1(beta)z1^{−ell0}) checked
against L4. Sound. [My W0-vs-W5 (+5*E2) windows agree on all laws; sealed F8
1,736/0 at +E2 and +7*E2.]

**COR-5 (W-MULT recovered).** L7 second form + L6, evaluation at y -> zbar.
Circularity audit: the S2-S5 chain consumes ONLY the division algorithm in O[x],
w0 a valuation with res additive, integer arithmetic/Bezout, and (Case II only)
the standard lift's two-term shape. No W-MULT, no printed Thm 4.2/4.8, no (R1)/(R2)
hypothesis, no GMN semantics anywhere in the chain — recovered-not-consumed HOLDS.

**S6.6 gate.** Displayed consequence + measurement; sealed F10 re-run NOT-CYCLIC
4/4 with the exact value sets {z1, zbar, zbar*z1^2} (p = 2) and {z1, zbar,
zbar*z1} (p = 3) — the note's "b in {1,2}" claim verbatim.

**Residuals honesty (S7).** Confirmed by consumption analysis: only Case II
touches the lift form, so (ITER-LAW-LIFT) is open EXACTLY at g0 = 1 AND delta1 = 1
and everything else is lift-form-free (L6 uses only deg Phi1 and the w1Phi1 datum).
gr(w2) wrapper: correctly displayed as riding the GRB retarget, consumed by
IFACE(c) consumers, not by this theorem. Orders >= 3: no claim found. Fences: the
unit's two commits (ab7c31c, 242ba1e) touch only the note, the falsifier, the run
artifacts, and the ledger — no TR3-S2/TWIST-LAW/DITER_RESTATE/GRB edits.

## 4. Execution record

### 4.1 Sealed re-run (step 3 of the pass; runner UNTOUCHED)

Invocation: `python3 iterlaw_check.py` from `verification/openmath/` (per header;
deterministic seed 20260825 internal). Integrity: working-copy md5
`bfd5ef71257a79aee827b516fccfc03d` == `git show ab7c31c:...iterlaw_check.py` md5
(seal commit). Exit code: **0**. Elapsed 16.4s. The run rewrote
`iterlaw_check_results.json` byte-identically to the committed artifact
(`git diff` empty afterwards) — full determinism confirmed.

| family | expected (note S8) | observed (this re-run) | verdict |
|---|---|---|---|
| F1 L6 ANCHOR-VAL | 468 / 0 | 468 / 0 | GREEN |
| F2 L7 PAIR-VAL both forms + shape | 2,604 / 0 | 2,604 / 0 | GREEN |
| F3 THEOREM (ITER-LAW) | 2,604 / 0 | 2,604 / 0 | GREEN |
| F4 Case-II development identity | 516 / 0, coverage MET | 516 / 0, coverage [36,36,36,36,72,72,72,72] MET | GREEN |
| F5 COR-2 B0a (measured + closed) | 4,108 / 0 | 4,108 / 0 | GREEN |
| F6 COR-1 integrality | 2,604 / 0 | 2,604 / 0 | GREEN |
| F7 COR-3 degenerations | 156 / 0 | 156 / 0 | GREEN |
| F8 COR-4 rep independence | 1,736 / 0 | 1,736 / 0 | GREEN |
| F9 integer layer symbolic | 20,000 / 0 | 20,000 / 0 | GREEN |
| F10 NOT-CYCLIC gate row X | 4/4 exact sets | 4/4; p=2: {z1, zbar, zbar*z1^2}; p=3: {z1, zbar, zbar*z1} | GREEN |
| CERT (T1/T2/T5/T11+PARI) | 432 / 0 | 432 / 0 (PARI leg fired; no cypari2 warning) | GREEN |
| TOTAL | 35,232 | 35,232 | ALL GREEN |

### 4.2 F2c from-note reimplementation (step 2; written BEFORE opening the seal)

File: `verification/openmath/iterlaw_f2c_reimpl.py` (exact arithmetic only: own
field-tower classes Fp/Ext, own DVR classes ZpO (exact Z proxy) / FptO
(F_p[t] reps), own O[x] division, developments, eq12/bezout, eps1 reading C,
R1/R2 reads, anchors, window scan — all transcribed from the note's S0 alone).
Seed 20260803. Windows: first run of 2*E2 consecutive gammas in W, plus the same
shifted by +5*E2 (off the sealed script's window schedule). Exit code: **0**.
Artifacts: `iterlaw_f2c_reimpl_output.txt`, `iterlaw_f2c_reimpl_results.json`.

Verifier rows (name; ring; d0; e0,h0,g0; e1,h1,g1; duty):

| row | ring | d0 | read0 | read1 | E2 | duty |
|---|---|---|---|---|---|---|
| VA | F3[[t]] | 1 | 2,1,1 | 4,3,2 | 8 | E2>=8; Case II (128 pairs) |
| VB | Z2 | 2 | 3,2,1 | 2,1,2 | 6 | d0=2 + Case II (96 pairs), l0p=-1 |
| VC | Z3 | 1 | 1,2,2 | 3,2,1 | 3 | e0=1 degeneration control |
| VD | F2[[t]] | 1 | 3,1,2 | 1,1,2 | 3 | e1=1 degeneration control |
| VE | Z2 | 1 | 2,3,2 | 2,1,1 | 4 | g0=2: Case-I-delta1=1 route |
| VF | F3[[t]] | 2 | 4,3,1 | 2,1,1 | 8 | E2>=8, d0=2, Case II (192 pairs), l0=3 |

Check families (samples / violations) — TOTAL 89,056 / 0:

| check | n | viol |
|---|---|---|
| I-L1-lvl1 / I-L1-lvl2 (EQ12-ADD both levels) | 12,000 each | 0 / 0 |
| I-L2-INNER-SHIFT | 12,000 | 0 |
| I-L4-EPS-CLOSED (integrality + exponent tie) | 12,000 | 0 |
| I-L5-EPS-MULT (exponent identity) | 12,000 | 0 |
| I-EXP (Lemma EXP, both integrality legs + equality) | 12,000 | 0 |
| F-L4 / F-L5 (field-level eps1 laws in K1) | 1,200 each | 0 / 0 |
| W-membership + L3-WINDOW closure | 128 + 1,584 | 0 / 0 |
| L6-ANCHOR-VAL (value + single-slot j=0 + w2=gamma + nonzero) | 128 | 0 |
| L7-PAIR-VAL formA / formB / SINGLE-SLOT at j=delta2 | 1,584 each | 0 / 0 / 0 |
| CASE-PARTITION (Case I <=> S1 < e0*g0) | 1,584 | 0 |
| T-W2-ADDITIVE (w2(P) = gamma+gamma') + T-DENOM-NONZERO | 1,584 each | 0 / 0 |
| COR1-INTEGRALITY | 1,584 | 0 |
| THEOREM-ITER-LAW (val(P) == zbar^d2 z1^D val(phi'')) | 1,584 | 0 |
| COR3-e0=1 (D == 0) / COR3-e1=1 (d2 == 0 and D == d1) | 72 each | 0 / 0 |

Mutation controls (the law's constants perturbed ONE AT A TIME; detection =
nonzero mismatches vs the measured val; ALL FOUR DETECTED):

| mutation | perturbation | samples | detections | verdict |
|---|---|---|---|---|
| M-ZBAR | zbar exponent delta2 -> 1-delta2 | 1,584 | 1,584 | DETECTED |
| M-FIB | drop the l0*gamma2*delta2 term | 1,584 | 424 | DETECTED |
| M-DIV | exponent divisor /e0 -> /1 | 1,584 | 536 | DETECTED |
| M-FLOOR | delta2 floor divisor e1 -> e1+1 | 1,584 | 344 | DETECTED |

Coverage: global caseI_d0 = 1,112, caseI_d1 = 56 (rows VD/VE, the g0>=2 inner-wrap
route), caseII = 416 (VA 128, VB 96, VF 192). Duties all MET (E2>=8 present;
Case-II > 0; e0=1 and e1=1 rows present; Case-I-delta1=1 > 0).

Underspecification findings from the reimplementation: **none** — every object
needed (res map, lift, standard lift, eq12, both reads, eps1, anchors, window,
cocycle) is pinned by the note's S0 text precisely enough to reimplement without
consulting any code. The only free choices were the class parameters themselves
(rows, psi0/psi1, windows), which the theorem quantifies over.

### 4.3 Order-of-operations attestation

(1) Note + DITER_RESTATE read first (restatement checked byte-identical to
242ba1e). (2) `iterlaw_f2c_reimpl.py` written and run to ALL GREEN with the sealed
falsifier still unopened. (3) Sealed header read, seal md5 verified, re-run
executed unchanged, harness semantics (grb_order2_check.py Tower/R1w/R2w/eps1/
eq12/bezout/w1/w2_data; strata_probe.py Composite/split/anchor/anchor_val/cocycle/
iter_law/Gamma0/cyc_adjudicate) read and diffed against the reimplementation.
(4) Content read. (5) This report. The sealed falsifier and the proof note were
not edited at any point.

## 5. Provenance appendix (exact slices verified against; complete, tails intact)

**Slice A — the statement of record, DITER_RESTATE_2026-08-08.md §S2 (the display
+ its scoping lines), working copy == commit 242ba1e:**

> **D-ITER (restated).**  The degree-0 composite digit algebra of gr(w₂) on the
> canonical anchor alphabet is the ITERATED TWISTED GROUP ALGEBRA
>
>     𝒟₂ = ⊕_{γ ∈ ℤ/E₂} K₂·u_γ,   u_γ·u_{γ′} = c(γ,γ′)·u_{γ+γ′},
>
> with the two-constant structure cocycle
>
>     (ITER-LAW)   c(γ,γ′) = z̄^{δ₂} · z₁^{(s₁(γ)+s₁(γ′)−s₁(γ+γ′) + ℓ₀γ₂δ₂)/e₀},
>                  δ₂ := ⌊(s₂(γ)+s₂(γ′))/e₁⌋.

and its setting line:

> **Setting (order 2; the tower data).**  A two-read OM tower with reads (e₀,h₀,ψ₀)
> then (e₁,h₁,ψ₁); E₂ := e₀e₁ > 1; residue tower K₁ (level 1, containing the frame
> letter z₁) and K₂ := K₁[z̄]/(ψ₁) via y ↦ z̄; ℓ₀ := the NORMALIZED Bézout inverse
> (0 ≤ ℓ₀ < e₀, ℓ₀h₀ ≡ 1 mod e₀ — the standing GMN-convention hypothesis, TR3-S1 S0);
> w₁(Φ₁) = e₀g₀h₀; γ₂ := e₁·w₁(Φ₁) + h₁ (the weight of the level-2 abscissa-step
> generator — tower datum; harness: `grb_order2_check.py:510`).

**Slice B — the note's THEOREM (ITERLAW_2026-08-08.md S0):**

> **THEOREM (ITER-LAW; proved below at attempt grade; falsifier
> `verification/openmath/iterlaw_check.py` sealed pre-run, verdict S8).**
> For all γ, γ′ ∈ W (then γ+γ′ ∈ W, Lemma WINDOW), with
> δ₂ := ⌊(s₂(γ)+s₂(γ′))/e₁⌋ ∈ {0,1}:
>
>     c(γ,γ′) = z̄^{δ₂} · z₁^{(s₁(γ) + s₁(γ′) − s₁(γ+γ′) + ℓ₀γ₂δ₂)/e₀},
>
> the exponent an integer. This is DITER_RESTATE §S2's (ITER-LAW) display verbatim,
> on the class its setting pins (every one of the 0/804 + 0/840 instances is in this
> class). No (R1)/(R2) hypothesis, no printed theorem, no GMN semantics consumed.

**Slice C — the calculus definitions implemented from-note (S0, the load-bearing
five):**

> * w₁(A) := min_k { e₀·w₀(b_k) + k·h₀ } over the Φ₀-development A = Σ_k b_k Φ₀^k
>   (deg b_k < d₀), nonzero digits.
> * ε₁(β) := z₁^{ℓ₀′ s(β) − ℓ₀ u(β)} ∈ K₁^× (harness `eps1`, reading C).
> * R₁-read: R_{1,β}(a)(z₁) := Σ_{m ≥ 0} res(b_{s(β)+m e₀} / π^{u(β)−m h₀}) · z₁^m,
>   where a digit contributes iff w₀(b) = u(β)−m h₀ exactly (else 0; digits strictly
>   below the line do not occur when w₁(a) ≥ β). (Harness `R1w`/`R1w_at_z1`.)
> * w₂(f), for 0 ≠ f = Σ_j a_j Φ₁^j (Φ₁-development, deg a_j < deg Φ₁):
>   w₂(f) := min_j { e₁·w₁(a_j) + j·γ₂ }.
> * R₂-read: with γ := w₂(f), s₂ := s₂(γ), slot abscissas s_j := s₂ + j e₁ and slot
>   weights γ_j := (γ − s_j γ₂)/e₁ (integral),
>   C_j(f) := ε₁(γ_j)·R_{1,γ_j}(a_{s_j})(z₁) if w₁(a_{s_j}) = γ_j (on-line), else 0.
>   (Harness `R2w`, reading C.)

and the anchors:

> * Canonical anchors: for γ ∈ ℤ set s₂ := s₂(γ), u₂ := u₂(γ),
>   γ₁(γ) := u₂ − s₂·w₁Φ₁ (so γ = e₁γ₁(γ) + s₂γ₂), s₁(γ) := s(γ₁(γ)),
>   u₁(γ) := u(γ₁(γ)), and φ_γ := π^{u₁(γ)} Φ₀^{s₁(γ)} Φ₁^{s₂(γ)}.
>   WINDOW W := {γ ∈ ℤ : u₁(γ) ≥ 0}.
> * Cocycle on anchors: c(γ,γ′) := val(φ_γ·φ_{γ′}) / val(φ_{γ+γ′}).

**Slice D — Lemma EXP in full (S3; the Bezout kernel):**

> **Lemma EXP (the compose kernel).** Let β, β′ ∈ ℤ, δ₂ ∈ {0,1}, β″ := β+β′+δ₂γ₂,
> and δ₁ := ⌊(s(β)+s(β′))/e₀⌋. Then
>
>     δ₁ + [ (s(β+β′) − ℓ₀(β+β′)) − (s(β″) − ℓ₀β″) ]/e₀
>       = ( s(β) + s(β′) − s(β″) + ℓ₀γ₂δ₂ )/e₀ ,
>
> an integer.
> *Proof.* By L1, s(β+β′) = s(β)+s(β′)−δ₁e₀, and ℓ₀(β″−β−β′) = ℓ₀γ₂δ₂; substitute
> both and collect over the common denominator e₀ — the δ₁ terms cancel.
> Integrality: the left side is δ₁ plus a difference of two integers (L4 twice).
> ∎ (Two lines — the TR3-S2 Lemma-EXP genre on the nose.)

**Slice E — the Case-II core (S4; the one lift-form-consuming step):**

> **Case II: g₀ = 1 and δ₁ = 1** (so e₀ ≥ 2, S₁ = e₀ + S₁″ with
> 0 ≤ S₁″ := S₁−e₀ ≤ e₀−2). At g₀ = 1 the standard lift is EXACTLY the two-term
> Φ₁ = Φ₀^{e₀} + ĉπ^{h₀}, ĉ := lift(c₀), c₀ := ψ₀(0) ≠ 0 in K₀ (monic degree-1 ψ₀ =
> y + c₀), and z₁ = −c₀ in K₁ = K₀[z₁]/(z₁ + c₀). Substitute Φ₀^{e₀} = Φ₁ − ĉπ^{h₀}:
>
>     P = π^U Φ₀^{S₁″} Φ₁^{S₂+1}  −  ĉ π^{U+h₀} Φ₀^{S₁″} Φ₁^{S₂}.
>
> Both cofactors have degree < deg Φ₁ = e₀d₀ (deg(ĉΦ₀^{S₁″}) ≤ (d₀−1) + (e₀−2)d₀
> < (e₀−1)d₀), so this IS the Φ₁-development: digit A₁ := π^UΦ₀^{S₁″} at slot S₂+1,
> digit A₀ := −ĉπ^{U+h₀}Φ₀^{S₁″} at slot S₂, zero elsewhere.

**Slice F — the note's S8 verdict block (matched exactly by the re-run):**

> **ALL GREEN, FIRST RUN, exit 0** — 35,232 samples, 0 violations in every family:
> F1 468/0 · F2 2,604/0 · F3 2,604/0 · F4 516/0 with Case-II coverage MET
> (per-instance 36 on each P, 72 on each Q; W/X rows also contribute) ·
> F5 4,108/0 · F6 2,604/0 · F7 156/0 · F8 1,736/0 · F9 20,000/0 ·
> F10 NOT-CYCLIC 4/4 with EXACT value-set match — the fresh row-X tables reproduce
> the strata-probe row-N sets {z₁, z̄, z̄z₁^b}, b ∈ {1,2}, verbatim at the fresh
> seed and windows · CERT 432 samples/0 (PARI T11 leg fired on the ℤ_p instances).

**Slice G — the scope box's open-lemma display (S7, residuals honesty):**

> * **General lawful lifts.** Only PAIR-VAL Case II consumes Φ₁'s explicit form (the
>   standard lift's exact two-term shape at g₀ = 1). For a general lawful monic lift
>   (TR3-S2 S0's class: correct degree, w₁, residual condition), the g₀ = 1 ∧ δ₁ = 1
>   stratum needs a development-reduction induction (the correction tail spreads
>   over slots with recursive re-reduction) — an honest OPEN displayed lemma:
>   **(ITER-LAW-LIFT)** ITER-LAW for every lawful monic lift Φ₁. Everything else
>   (L1–L6, EXP, Case I, S5, S6) is lift-form-free. All 52 + all JUNCFORGE towers
>   are standard-lift, so the entire instance base sits INSIDE the proved class; no
>   instance evidence exists outside it.

— pass PE report, campaign date 2026-08-08 (wallclock 2026-08-03). Verifier: the
Fable execution leg. Files of record for this pass:
`lean/notes/openmath/ITERLAW_passPE_report.md` (this file),
`verification/openmath/iterlaw_f2c_reimpl.py`,
`verification/openmath/iterlaw_f2c_reimpl_output.txt`,
`verification/openmath/iterlaw_f2c_reimpl_results.json`.
