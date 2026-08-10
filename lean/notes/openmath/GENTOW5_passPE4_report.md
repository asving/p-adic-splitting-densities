# GENTOW5 passPE4 — HOSTILE VERIFIER REPORT

**VERDICT: CLEAN — 0 CRITICAL + 0 GAP + 2 MINOR. Counter starts at
1/2.** The r3 repair is CORRECT and was re-derived independently at
every layer this pass could reach: the corrected THEOREM
GENTOW5-B(c) entry-read clause is the uniform GENTOW-1 transport
(verified verbatim against the GENTOW1 source template), the
residual-degree count kills the retired (i+2)-pairing both ways
(mu*l_{i+1}/e_{i+1} = mu*f_{i+1} exact at the corrected clause;
floor(mu/e_{i+2}) < mu*f_{i+2} at every proper stage for the old
one), the four committed witness rows check by hand AND against the
committed artifact bit-for-bit, (c) HOLDS at depth 5/6 (the f64
ladder — hand-derived dev confirmed by machine), and this pass's
fresh route verified the corrected biconditional at TWO new frames
on the exact axis the old clause miscounted — including the FIRST
(c)-read with deg psi > 1 (proper (e,f) = (2,2) stage, residual
psi_2^2 with support {0,4,8}) and the FIRST full-content residual
read (p = 3: all five on-chord digits (1,1,2,2,1) = psi_2^2 mod 3,
unfakeable by support) — 70 checks / 0 violations ON RUN 1 (the
arc's first defect-free first run). The two MINORs are
display-hygiene at the edges of the repair, not defects in it.
Machine leg: seals verified, artifacts byte-frozen through r3,
FIVE isolated re-runs BIT-IDENTICAL (incl. the first isolated
re-run of PE3's own instrument).

**Pass:** GENTOW5-passPE4, fresh context, zero prior stake,
2026-08-10. **Target:** `GENTOW5_PROOF_2026-08-09.md` @ HEAD (arc:
seal -> PE1 1C+2G+3m @ 0160b94 -> r1 -> PE2 0C+2G+2m @ 40f313a ->
r2 -> PE3 0C+1G+2m @ 39c36aa -> r3 = 1e1406f + d0631cb). Protocol:
quote-and-classify, fix nothing. Context read: the note in full at
HEAD; the PE1/PE2/PE3 reports in full (their routes — the psi^{(w)}
re-scope discharge, the lift-display re-derivation, the GA3* w-live
leg, the f64 depth-5/6 leg — NOT re-walked; consumed as disclosed);
both r3 diffs; GENTOW1_PROOF S2 (LEMMA GENTOW-1, the transport
template) **read at ITS HEAD = 4e81a57** (post-acceptance-2/2 +
post S3 fixed-base lift correction; the TOWERRAT R2a/b/c repairs
adjudicated REAL against GENTOW1 had NOT yet landed on the note at
read time — the parallel-unit disclosure below). As-of carried:
GENTOW2 ACCEPTED 2/2 + Codex RATIFIED-WITH-ANNEX (vartheta/B''
annex); GENTOW1 ACCEPTED with repairs in flight; w measured != 1
at 7 primes.

---

## S1. FINDINGS

### PE4-F-1 MINOR — the statement's blanket induction header leaves
### (c)'s index-0 instance formally in scope while the r3 coverage
### sentence names indices 1..r-1 only

Quote (S3 statement): "Then, by induction on i < r: (a) ... (c)
...". Quote (the r3 bracket in the (c)-proof): "with GENTOW-1 as
the index-1 instance verbatim, indices 1..r-1 are covered." At
i = 0 the (c) clause reads T_1 (level-0 read, kappa_1 = u_1/e_1,
residual psi_1^{mu}, box vs Phi_1^{mu} at mu*E_1 + 1) — a true
statement (the classical level-1 entry budget, accepted-corpus
territory one level below GENTOW-1), but outside the proof's named
base and step. Unconsumed edge: DEF GENTOW5-1's floor-chain rung 1
explicitly rides the accepted [r1] node floor ("at i = 1 this is
the [r1] node floor u_2 > e_2 D'h verbatim"), NOT (e)@index-0, and
no other sentence instantiates (c)/(e) at index 0. Same species and
weight as PE2-F-3 (unconsumed edge, one-clause scope fix: "(c) for
i >= 1" or a named level-1 base cite). Pre-r3 the proof had the
same GENTOW-1 base, so this is not an r3 regression — the r3
coverage sentence made the scope visible for the first time.

### PE4-F-2 MINOR — S9's f32 "digit expansion" is displayed halfway
### reduced; a reader re-deriving the pins from it as written gets
### p_1 = 341, not the quoted inf

Quote (S9, PE3-F-1 bullet): "re-derived by hand this round from the
digit expansions f32 = Phi_3^4 - 512 Phi_2 Phi_3^2 - 2^16 Phi_3 +
2^16 Phi_2^2 and Phi_4 = Phi_2^4 - 32 Phi_1 Phi_2^2 + 1024x (after
Phi_1^2 = Phi_2 + 4x): f32@Phi3 (pins [340,inf,186,inf,0] ...)".
The f32 identity is TRUE but is not the canonical Phi_3-adic
development: its C_0 slot 2^16 Phi_2^2 has degree 8 = deg Phi_3
(illegal), and completing the reduction (Phi_2^2 = Phi_3 + 16
Phi_1, the analogue of the parenthetical shown only for Phi_4)
CANCELS the -2^16 Phi_3 term, giving the canonical dev Phi_3^4 -
512 Phi_2 Phi_3^2 + 2^20 Phi_1 with C_1 = 0 — which is what the
quoted pins (p_1 = inf) and the committed artifact row encode.
Failure scenario: a reader computing pins from the displayed
expansion slot-by-slot reads C_1 = -2^16 and gets p_1 = 341,
conflicting with the note's own quoted [340,inf,186,inf,0]; they
must notice the illegal C_0 degree to reconcile. No conclusion
moves (on-chord support {0,4}, residual psi_4^2, box 341 are
invariant either way — 341 > chord 255 at j = 1). One-parenthetical
fix ("after Phi_2^2 = Phi_3 + 16 Phi_1"). Verified: my own dev
computation confirms the canonical form and the artifact pins.

### Disclosure (not a finding): GENTOW1 as-of state

The (c) clause cites "exactly as in LEMMA GENTOW-1 (a)-(d)".
GENTOW-1(b)'s free-count display is the target of TOWERRAT R2a
(Codex F-1, adjudicated REAL: unclipped count, false at N < max
floor), landing in a PARALLEL unit this wave; at my read of
GENTOW1 HEAD (4e81a57) it had not landed. GENTOW5's (c) cites by
reference and re-displays nothing of the count, so it auto-inherits
the source repair; no defect lives in this note's text. Noted so
the orchestrator's fold can confirm inheritance after R2a lands.

## S2. CLEAN CHARGES (attacked and survived), incl. the r3 repair

* **The (c) re-index (r3, THE repair) — re-derived, not re-read.**
  (i) Template at source: GENTOW1 S2's T is "monic f of degree
  n = mu2*D2 whose LEVEL-1 stage read exhibits the full inner side
  ... slope kappa2 = u2/e2 from (0, mu1*kappa2) to (mu1, 0) with
  twist-coherent residual psi2^{mu2}", box vs Phi2^{mu2} at
  mu2*E2+1, pins (mu2-j)E2+1, floor dv2(Phi2(x0)) > E2 — every
  clause anchored at the KEY'S stage, read one level below. The
  corrected T_{i+1} clause is this transport verbatim at 2 -> i+1;
  GENTOW-1 IS the index-1 instance. (ii) The count both ways:
  corrected — polygon length mu*l_{i+1}, full kappa_{i+1}-side,
  residual degree mu*l_{i+1}/e_{i+1} = mu*f_{i+1} = deg
  psi_{i+1}^{mu}, exact (e | mu*l always); retired — length mu,
  kappa_{i+2}-side residual degree floor(mu/e_{i+2}) vs
  mu*f_{i+2}: equality forces l_{i+2} = 1 (improper), and the
  inequality is robust even when e_{i+2} does not divide mu.
  (iii) The four committed rows re-derived BY HAND and checked
  against the committed artifact verbatim: refuted rows f32@Phi4
  [682,inf,0] / Phi4@Phi3 [170,inf,0] (residual degree 1, boxes
  341 = 2E_4+1 / 85 = 2E_3+1 hold); corrected rows f32@Phi3
  [340,inf,186,inf,0] / Phi4@Phi2 [84,inf,50,inf,0] (one side,
  support {0,4}, residual (y-1)^2 = psi^2, LHS and RHS both hold).
  The canonical devs (f32@Phi3 = Phi_3^4 - 512 Phi_2 Phi_3^2 +
  2^20 Phi_1 with the C_1 cancellation; Phi_4@Phi_2 = Phi_2^4 -
  32 Phi_1 Phi_2^2 + 1024x) confirmed by an auxiliary exact
  computation (disclosed post-seal helper, verifying my own hand
  work). The j = 0 digits re-solved against the normalizer
  recursion (nhat_4(340) = 2^20 Phi_1, nhat_3(84) = 2^10 x —
  digits exactly 1, residuals y^2 + 1).
* **THE CHARGE'S DEPTH-5/6 QUESTION: (c) HOLDS at the f64 ladder.**
  f64@Phi4 dev = Phi_4^4 - 2^17 Phi_3 Phi_4^2 + 2^40 Phi_2 (the
  same C_1-cancellation pattern; machine-confirmed): pins
  [1364, inf, 714, inf, 0] on dv_5 — one kappa_5-side (chord
  4*341 = 1364; j = 2 at 714 > 682 strictly above), support {0,4},
  residual (y-1)^2 = psi_5^{mu}, box 1365 = 2E_5+1 (wt_5(2^32
  Phi_4) = 1024 + 341) — LHS and RHS of the corrected (c) both
  hold at the T_5 entry. The retired clause fails AGAIN at depth 6
  (f64@f32 pins [2730, inf, 0]: residual degree 1 != 2). PE3's
  committed leg-D5 ladder (32,80,168,340,682,1365)/64 supplies the
  root values consumed here; re-run bit-identical this pass.
* **(c)'s consumers post-change — walked.** (e) consumes the
  (i+1)-anchored pins + box (unchanged by r3) and its convexity
  re-derived: pins >= (mu-j)E_{i+1}+1 with right endpoint (mu, 0)
  force side slopes > E_{i+1}, hence u_{i+2} > e_{i+2}E_{i+1} —
  matching DEF GENTOW5-1's floor-chain provenance one index down.
  (d) self-contained (GENTOW5-A's pattern, repo convention). The
  S4 witness consumes (b)+(e). GREP AUDIT: every occurrence of the
  (i+2)-read pairing in the note lives inside the r3 brackets
  (explaining the retirement) or the proof's entered-stage displays
  (Step 1/2/5 at Phi_{i+2}, proving index i+1 — the consistent
  anchoring); no sentence consumes the retired clause. The proof's
  index bookkeeping closes: base index 1 + steps at entered stage
  i+2 for i = 1..r-2 = indices 1..r-1 (residue: PE4-F-1's index-0
  scope display). Step 1's bare psi_{i+2}^{mu} display remains
  glossed by the [GT5-r2] walk bullet (FGMN read is the twisted
  power; repo-side translation w-blind) — coherent with the r2
  layer.
* **The r3 F-2/F-3 repairs.** Both "uncomputed" flanks now carry
  dated brackets whose content matches the record (7 measured
  primes = PE6's 6 + PE3's GA3* carrier prime; w_i = 1-OPEN claims
  correctly scoped to closed-form + unmeasured frames/levels); the
  consumer-walk pointer now names S6's TARGET-2 rider, and I
  checked the actual S6 box: seam axis + compound rows present, no
  w row — pointer now TRUE.
* **The system post-three-rounds (r1+r2+r3 interaction).** The
  dated layers cohere: the r1 gauge pin's consumer list ("(c) Step
  5") still points at an existing, entered-stage display; S7's r1
  record carries the r2 correction bracket without contradiction;
  the status table's "(a) at psi^{(w_i)}; w_i = 1 open" survives
  the r3 dating (measured != 1 at 7 primes does not close the
  closed-form question); S2.4's INV-j and the S2.1 pin are
  untouched by r3 (height-blind, as stated). No sentence found
  that a later append contradicts.

## S3. MACHINE-LEG INTEGRITY

* **Pins:** gentow5_checks.py md5 5fa684c7... = the note's claim;
  artifacts dc499a49... (exact) / 839a8660... (full) = the note's
  claims; `git diff --stat 39c36aa..HEAD` touches notes/docs only —
  sealed artifacts BYTE-FROZEN through r3 as S9 promises.
* **Isolated re-runs (/tmp/gt5pe4_iso, this pass): FIVE for five
  BIT-IDENTICAL** — exact leg 86/0; full leg (--pari) 92/0; PE1
  fresh 15/0; PE2 fresh 22/0; **PE3 fresh 48/0 (its first isolated
  re-run by a later pass)**. Diff vs committed artifacts empty in
  each case.
* **Tautology audit:** the PE1-PE3 audits stand (nothing machine-
  side changed since 39c36aa). This pass's instrument: predictions
  hand-derived in the sealed docstring (commit 891de3a, py_compile
  only, no smoke run); pin computations are monomial-exact ladder
  arithmetic independent of the slot theory under test; own-Bareiss
  resultants independent of the PARI legs; residual digits are
  integer monomial ratios compared against an independently
  expanded psi^2; single-line gp prints throughout (the documented
  stdin trap, not re-hit).

## S4. FRESH ROUTE (disjoint from PE1 FR-1/2/3, PE2 FR-A, PE3 legs
## W/D5 and the committed battery — new keys, new frames, new check
## species; `gentow5_pe4_fresh.py`, RUN 1 GREEN 70/0)

**LEG CS-A — the (c)-STRESS at the first proper (e_2,f_2) = (2,2)
machine (c)-read (p = 2, u_2 = 7 SLACK, next stage e_3 = 2 — the
exact axis the retired clause miscounted).** Phi_2 = Phi_1^4 -
8x Phi_1^2 - 128 (Phi_1 = x^2-2, psi_2 = y^2+y+1): carrier ONE
prime (4, 2), dual-oracle ladders exact. Entry f16 = Phi_2^2 -
2^12 x Phi_1 (u_3 = 57 = 2E_2 + 1): corrected-(c) LHS verified —
pins [28,25,23,inf,14,12,9,inf,0] exact, ONE kappa_2 = 7/2 side,
on-chord support EXACTLY {0,4,8} (j = 2,6 strictly above),
residual y^4 + y^2 + 1 = psi_2^2 — **the first machine (c)-read
whose residual is a genuine psi-power with deg psi > 1**; RHS box
57 = 2E_2+1 holds; f16 = ONE prime (8, 2), RES (8, 28, 114) =
nfeltval (4, 14, 57) dual-exact. **OLD-clause kill at NEW
geometry:** f16@Phi_2 pins [57, inf, 0] — kappa_3-side of residual
DEGREE 1 != 2 = deg psi_3^{mu} while the box holds (the committed
refutation rows were all-f = 1 towers; this one is f_2 = 2).
**Depth-4 continuation:** f32' = Phi_3^2 - 2^21 x Phi_2 (u_4 =
229) — ONE prime **(e, f) = (16, 2)**, the program's first depth-4
witness with a live f-part; RES ladder (16, 56, 228, 458) =
nfeltval (8, 28, 114, 229), both routes exact. **Two teeth fired:**
f16m = Phi_2^2 - 2^14 (box at 2E_2 exactly, gcd proviso violated)
collapses — the hand-derived factorization Phi_1^2 (Phi_1^2 - 8x)
(Phi_1^4 - 8x Phi_1^2 - 256) holds EXACTLY, Res(f16m, Phi_1) = 0,
factorpadic [2,4,4,4]; f16b = f16 - 2^13 x^2 (one slot at 56 <
57, box fails) kills C_0 exactly — the full-side read collapses,
factorpadic [2,6,8]. The biconditional held in BOTH directions at
every probe.

**LEG CS-B — residual CONTENT (p = 3, the non-F_2 leg).** Phi_1 =
x^2 - 3, psi_2 = y^2 - y - 1 over F_3 (rootless — irreducible),
Phi_2 = Phi_1^4 - 9x Phi_1^2 - 243 (u_2 = 5), entry f16_3 =
Phi_2^2 - 3^9 Phi_1 (u_3 = 41 = 2E_2+1): pins [20,18,15,inf,10,
8,5,inf,0], one kappa_2 = 5/2 side, ALL FIVE lattice slots
on-chord with coherent digits (j = 8,6,4,2,0) = **(1, 1, 2, 2, 1)
= (y^2 - y - 1)^2 mod 3 coefficient-for-coefficient** — three
digits != 1, so the psi^{mu}-residual clause is verified by
CONTENT, unfakeable by support (every committed (c)-adjacent row
lives over F_2 where support determines everything). Carrier +
entry dual-oracle exact ((4,2) and (8,2); ladders (2,5) / (4,10,
41); RES v3 = (4, 10) / (8, 20, 82)). Disclosed: both fresh frames
are letter-dead (eta = 1) — the (c) axis is orthogonal to the
gauge seam by design; the seam and w axes keep their PE1/PE2/PE3
coverage.

**Run record:** run 1 = 70 checks / 0 violations, exit 0 — no
instrument defects, no re-run (the arc's first clean first run;
seal 891de3a, artifact 8af40a2).

## S5. GRADE LINE

**CLEAN: 0 CRITICAL + 0 GAP + 2 MINOR (PE4-F-1 the (c) index-0
scope display; PE4-F-2 the S9 halfway-reduced f32 expansion) —
nothing GAP-or-worse survived this pass's verification. Counter
moves 0/2 -> 1/2.** The two MINORs are one-clause hygiene at the
repair's edges; neither moves a conclusion, neither has a consumer.
What this pass adds in the conservative direction for the next
fold: the corrected (c) now has live machine contact at a proper
(2,2) stage (both directions + both teeth), at residual content
(p = 3, five nontrivial digits), and at depth 5/6 (f64 — holds);
the retired pairing has a THIRD independent refutation geometry
(f_stage = 2); and the depth-4 witness axis now includes an
(e, f) = (16, 2) leaf.

Verifier artifacts: `verification/openmath/gentow5_pe4_fresh.py`
(sealed 891de3a, md5 6397cf30) + `gentow5_pe4_fresh_output.txt`
(GREEN 70/0, 8af40a2). Isolated re-runs in /tmp/gt5pe4_iso
(session-local; verdicts quoted in S3).
