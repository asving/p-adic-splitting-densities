# GENTOW5 passPE2 — HOSTILE VERIFIER REPORT

**VERDICT: NOT CLEAN — 0 CRITICAL + 2 GAP + 2 MINOR. Counter stays
0/2.** The r1 gauge pin's mathematics is CORRECT and survived a
seam-live depth-3 machine attack (this pass's FR-A: the first
i >= 2 vartheta instance ever run, corrected key = carrier 22/0,
naive tooth fired at i = 2). The two GAPs are at the pin's two
FLANKS: (PE2-F-1) the S3(a) leg's compatibility claim with GENTOW2
r3 AS LANDED is wrong at the w-leg — the landed B-law makes the
S2.1-pinned recipe realize psi^{(w)}, not psi, so THEOREM
GENTOW5-B(a)'s "R_{nu_i}(Phi_{i+1}) = psi_{i+1}" is unproven at the
statement's own keys (open unless w = 1); (PE2-F-2) DEF GENTOW5-1's
K_i-digit lift DISPLAY (inherited from GENTOW1 S3) admits NO
monomial at the flavors the gauge-corrected khat_t needs on
seam-live frames — khat_0 is undefined-as-displayed at this pass's
FR-A (pi-exponent 11/2), while the intended re-solved family is
what every instrument implements and is machine-green. Machine leg:
all three committed artifacts re-run isolated BIT-IDENTICAL
(86/0 exact, 92/0 full-PARI, 15/0 PE1-fresh).

**Pass:** GENTOW5-passPE2, fresh context, zero prior stake,
2026-08-10. **Target:** `GENTOW5_PROOF_2026-08-09.md` @ HEAD (r1 =
62191bd/014f517/5413c70/63bec72/be58a62; arc: seal -> PE1 NOT CLEAN
1C+2G+3m @ 0160b94 -> r1). Protocol: quote-and-classify, fix
nothing. Context read: the note in full at HEAD; the PE1 report in
full; the five r1 commit diffs; GENHN erratum 59c1966; GENTOW2 S5
AT HEAD (r3 LANDED through d798529: LEMMA GENTOW2-B restated, B'',
honesty box); GENTOW1 S3 lift display; both sealed runners; the
HE7 annexpass/annexpass2 verdict heads (F-4 fold check).

TIMELINE FACT (drives PE2-F-1): the r1 round's commit 2 (014f517)
pinned GENTOW2 r3 as IN-FLIGHT (HEAD then 7532acb); r3 landed IN
FULL (117b2c0..d798529) before this pass. The r1 mid-round
addendum (be58a62) saw only r3 commit 1/4's message. This pass
verifies against the landed text — the first pass that could.

---

## S1. FINDINGS

### PE2-F-1 GAP — THEOREM GENTOW5-B(a)'s "= psi_{i+1}" is unproven
### at the S2.1-pinned recipe under the LANDED GENTOW2 r3 B-law:
### the pinned keys realize psi^{(w)}, and the S3(a)/S7 compatibility
### sentences drop the w-leg

Quotes (S3, statement + (a) + the in-flight pin; S7 addendum):

    keys Phi_1, ..., Phi_r built by THE RECIPE [GT5-r1: in its
    GAUGE-CORRECTED form — the S2.1 pin's vartheta-twisted khat_t ...]
    (a) ... with R_{nu_i}(Phi_{i+1}) = psi_{i+1}.

    [In-flight pin ...] GENTOW2 r3 — flipping B-2 to its cocycle
    form u(beta) = the vartheta-telescope unit, i.e. FGMN R-read =
    the repo MULTIPLICATIVE read ... If r3 lands the cocycle form,
    the S2.1 gauge-corrected recipe realizes psi_{i+1} with NO
    re-parameterization (its vartheta twist IS the u-family)

    [S7 mid-round update:] That form is an INSTANCE of the
    per-grade x0-free family the S3(a) discharge consumes ...
    consistent both ways; the S3(a) text stands as written

What LANDED at GENTOW2 HEAD (S5, LEMMA GENTOW2-B [r3 RESTATED] +
B''): u(beta_t) = theta(t)*w^{f3-t} with theta(t) :=
res(nhat_2(u_3(f_3-t))/nhat_2(u_3)^{f_3-t}) — the repo cocycle —
AND a second leg w := R_{3,kbar}(nhat_2(u_3)) in K_2^x, "a SINGLE
slot-independent unit, the honest cross-frame residue ... not
computed anywhere in the corpus"; the restated lemma's conclusion
under the multiplicative prescription c_t = theta(t)^{-1}a_t is
R_nu(Phi_3) = psi_3^{(w)} := w^{f_3}psi_3(y/w) — explicitly NOT
psi_3 — and GENTOW2's own consumer was re-scoped accordingly (r3
commit 3/4: "S4 in-particular clause re-scoped ... consumption AT
psi3^(w)").

The arithmetic (one line): theta(t) = vartheta_{i,f-t}^{-1} (the
definitions are reciprocal). The S2.1-pinned recipe's digits are
c_t*vartheta_{i,f-t}, so the B-law residual coefficient at y^t is
u(beta_t)*c_t*vartheta_{i,f-t} = theta(t)*w^{f-t}*c_t*
theta(t)^{-1} = c_t*w^{f-t}: R = psi^{(w)}. The vartheta twist
cancels the theta leg ONLY. Hence: (i) the in-flight sentence
"realizes psi_{i+1} with NO re-parameterization" is FALSE at the
landed form unless w = 1 (open — GENTOW2: w is uncomputed and
verdict-level machine data is w-blind); its characterization "FGMN
R-read = the repo MULTIPLICATIVE read" likewise (the reads differ
by exactly w; PE4's decode leg 14/0 confirmed the theta leg, not
w = 1); (ii) the S3(a) discharge's re-parameterized digit string
u_i(beta_t)^{-1}c_t = c_t*vartheta_{i,f-t}*w^{-(f-t)} is a
DIFFERENT key from the statement's pinned key (differs by the
w-powers) — the discharge proves (a) for a key the statement does
not build, and the statement's key gets psi^{(w)}; (iii) (b)'s
residual displays R_{j-1}(Phi_{i+1}) = psi_{j-1}^{l_j...} inherit
per-level w-twists. Failure scenario: at a letter-live frame with
w != 1, a consumer reads (a)/(b) in the FGMN convention and
identifies an FGMN residual coefficient with a psi-coefficient on
the nose — wrong by w-powers. Blast radius (checked): contained —
irreducibility, degrees, sigma, values, and the REPO-side residue
classes are w-blind (this pass's FR-A verified psi_3 carried
exactly repo-side; no consumer inside THIS note breaks), and the
GENTOW2-A re-scope shows the repair shape ((a) at psi^{(w)}, or an
honest w = 1 lemma). The S7 addendum's "consistent both ways" is
wrong as written; the discharge's "arbitrary x0-free u" leg does
survive (theta(t)*w^{f-t} IS per-grade, x0-free, g-free).

### PE2-F-2 GAP — DEF GENTOW5-1's K_i-digit lift display admits NO
### monomial at the flavors the gauge-corrected khat_t needs on
### seam-live frames (khat undefined-as-displayed; machine-refuted
### family shape, this pass's FR-A)

Quote (S2.1, K_i-digit lifts):

    lift_i(c; m) := the sum of the f_1...f_i within-class monomials
    x^{i0+e1 r} Phi_1^{b_1 + e_2 t_1} ... at height m with O-digit
    coefficients realizing c in the coherent normalization ...;
    at i = 2 this is GENTOW-2's lift(s; m).

The anchor (GENTOW1 S3) binds (i, b) to n2hat(m)'s exponents, so
the displayed family fixes the base exponents across flavors and
only steps x by e1*r and Phi_1 by e_2*t_1. At FR-A's khat_0 height
m = 14 (dv_2-ladder pi = 2, x = 1, Phi_1 = 3; nhat_2(14) = 3^7,
i0 = 0): the t_1 = 1 flavor needs pi-exponent (14 - 0 - 3)/2 =
11/2 — NO such monomial exists. The true within-class family
re-solves the base per flavor: {3^7 -> 1, 3^5*x*Phi_1 -> eta*beta_1}
(x-exponent jumps 0 -> 1). The gauge-corrected digit there is
c_0*vartheta_{2,2} = 2*eta_2, which has NO component on the
surviving displayed flavor — so khat_0, hence Phi_3, hence THEOREM
GENTOW5-B's hypothesis, is undefined under the display exactly at
the first seam-live i = 2 frame. First live precisely on the r1
repair's own geography (letters live x f_stage >= 2 x digit outside
the prime field); every committed battery row sits where the display
happens to work (prime-field digits or parity-compatible heights;
the sealed battery's own A-3 "eta2-flavor lift" 4*Phi' already
implements the re-solved object). Machine: FR-A ran the re-solved
khat_0 = 3^5*x*Phi_1 — 22/0 incl. sigma, exact ladders, and the
psi_3 residue class (S4 below); the strict-display flavor
non-existence is asserted as check FA1-LIFT. Failure scenario: a
depth-r consumer (or formalizer) implements lift_i as displayed and
either crashes (non-integer exponent) or silently realizes only the
prime-field sub-span — wrong keys at every seam-live frame.
Repairable at display level (per-flavor base re-solve, equivalently
lift_i(c; m) = Sum_t d_t * nhat_i(m - t*u_...)-chain * Phi^t); the
coherent-normalization clause already forces the intended object.

### PE2-F-3 MINOR — LEMMA GENTOW5-D's restated strict clause still
### misclassifies the i = 1 edge (the x-carry IS the top carry there)

The [GT5-r1] statement: "the key-part of each INTERIOR carry (the
x-carry and the Phi_j-carries with j < i-1) strictly raises it,
while the TOP carry's key-part (j = i-1 ...) PRESERVES it." At
i = 1 the only move is the x-carry and it IS the j = 0 = i-1 top
carry: key-part Phi_1 at wt_1 = E_1 = D_1*h = wt_1(x^{D_1}) —
PRESERVED, not strict; and the proof's own rung accounting
("(FLOOR-j) ... consumed at rungs 1 (x-carry) through i-1") is the
EMPTY range at i = 1 while the x-carry display consumes rung 1
(u_2, out-of-datum at i = 1 — the same disease F-3 cured at the top
grid). Unconsumed edge: every named consumer instantiates i >= 2
(GENTOW5-A Step B at i = 2; S3(c)/(d) at i + 2 >= 3), so MINOR; the
fix is one clause ("the x-carry when i >= 2").

### PE2-F-4 MINOR — the seam-live coverage that now exists is all
### e_stage = 1; the pin's class-separation leg (e_{i+1} >= 2 with
### live letters) has no seam-live machine contact anywhere

The S6 seam-axis box discloses FR-1 as "the seam-live row that
exists"; FR-1 has e_2 = 1, and this pass's FR-A has e_2 = e_3 = 1.
At e_{i+1} >= 2 the multiplicative slot convention reads through
the mod-e_{i+1} class separation (S2.3 step (3)) — that compound
(vartheta live x e_stage >= 2) is machine-untouched everywhere in
the program. Proof-side the derivation is uniform; coverage-box
precision only.

## S2. CLEAN CHARGES (attacked and survived)

* **The [GT5-r1] GAUGE PIN itself (S2.1).** Re-derived from A1's
  dictionary in the building direction (multiplicative slot
  coefficient = digit * vartheta^{-1}; digit := c_t *
  vartheta_{i,f-t} — matches gamma = c*vartheta, S1.2 line-exact);
  the telescope recursion vartheta_{i,s+1} = vartheta_{i,s} *
  res(tau_i(s*u_{i+1}, u_{i+1})) re-derived (two-bracket split);
  level-2 recovery re-derived: n1hat(u_2)^s accumulates x-exponent
  s*i(u_2), floor(s*i(u_2)/e1) wraps, vartheta_{1,s} =
  eta^{floor(s*i(u_2)/e1)} = the erratum's eta^{W(t)} at s = f_2-t
  EXACTLY; FR-1 numbers re-checked (i(u_2) = 1, W = (1,0), khat =
  (6x, 54)) and the PE1 artifact re-run bit-identical. NEW: the
  first i >= 2 instance verified live (FR-A: vartheta_{2,2} = eta
  = 2 at u_3 = 7, corrected khat_0 = 3^5*x*Phi_1 -> carrier
  sigma {(2,4)}, psi_3-class carried; naive digits -> the
  vartheta^{-1}-twisted residual, machine-exact). The trivial-twist
  scope clause and both S4.1 seam-blindness grounds check ((i)
  K_i = F_2 kills all letters; (ii) f = 1 forces s = 1,
  vartheta_{i,1} = 1 by definition — independent).
* **LEMMA GENTOW5-D as repaired, at i >= 2.** Top-grid weight now
  defined and in-datum; x-carry/interior/top pricing re-derived
  (identity (ehat_i/ehat_{j+2})e_{j+2}E_{j+1} =
  (ehat_i/ehat_{j+1})E_{j+1} checked); the grid-4 equality instance
  340 = 340 = 170*2 re-computed; the i = 2 instance = GENTOW1 Step
  0's display verbatim. Consumer walk ((2) of the charge):
  GENTOW5-A Step B, S3(c) Steps 0/1/3, S3(d) consume NONDECREASING
  only; every strict flow-up there is priced by lam > E separately
  — the theorem consumes exactly what D now delivers (residue:
  PE2-F-3's i = 1 edge, unconsumed).
* **S3(a)'s discharge core.** "Arbitrary x0-free per-grade u +
  (LIFT_i) re-parameterization" is sound as an existence argument,
  and the landed u = theta(t)*w^{f3-t} IS an instance of the
  consumed family (per-grade, x0-free, g-free) — the S7 addendum's
  instance claim is TRUE; only its "consistent both ways" and the
  in-flight w-free identification fail (PE2-F-1).
* **F-4/F-5/F-6 repairs.** The annex fold verified against the
  actual verdict heads (4a613d8 CLEAN 1/2; a472155 "ACCEPTED 2/2";
  e38df9f exists) — conservative direction confirmed; the F-5
  disclosure matches the sealed runner's chk lines ("C3b
  nfactors=1" only — verified in source); the F-6 withdrawal's
  residue (resultant certifies the root-SUM; per-root needs the
  single-prime read) is the correct scoping.
* **S2.2/S4 grammar pins.** nhat_3(85) = 2^8*Phi_2, nhat_2(21) =
  16*Phi', nhat_4(341) = 2^16*Phi_3 re-solved by hand through the
  recursion; first-live n = 2^{r+1} and S3(e)'s telescoped
  inequality (base-rung equality) re-derived.

## S3. MACHINE-LEG INTEGRITY

* **Pins:** gentow5_checks.py md5 5fa684c7... = note's claim;
  artifacts dc499a49... (exact) / 839a8660... (full) = note's
  claims; sealed artifacts byte-frozen through r1 as promised (r1
  touched the note only).
* **Isolated re-runs (/tmp copies, this pass):** exact leg 86/0
  exit 0 BIT-IDENTICAL; full leg (--pari) 92/0 BIT-IDENTICAL; PE1
  fresh instrument 15/0 BIT-IDENTICAL. Three for three.
* **Tautology audit:** PE1's audit stands (kill-checks read the
  refined development, not the pin engine; resultant and gp legs
  independent). Fresh-route addition disclosed: FR-A's residue rows
  r2a/r2b return +oo because they ARE the key identity
  (P3(th)/(729 th^2) = 0) — the discriminating p-adic content is
  carried by sigma, the exact ladders, the t1-row (val = 1, genuinely
  p-adic), and the 0 vs +oo FLIP between the two keys; stated so in
  the artifact.

## S4. FRESH ROUTE (disjoint; `gentow5_pe2_fresh.py`, 22/0)

FR-A — THE FIRST SEAM-LIVE DEPTH-3 CHAIN ANYWHERE (the axis the
charge named: seam x depth; disjoint from the battery, the depth-4
witness, and PE1's FR-1/FR-2/FR-3, which were i = 1 or seam-blind):
p = 3, Phi_1 = x^2-6 (eta = 2), stage 2 = FR-1's (1,2)-stage
(u_2 = 3, psi_2 = y^2+y+2, corrected Phi_2), stage 3 = (e_3,f_3) =
(1,2), u_3 = 7, psi_3 = y^2 - y - eta_2 over F_9 (disc = eta_2^7
non-square — irreducible; hand F_9 algebra machine-confirmed).
vartheta_{2,2} = res(nhat_2(7)^2/nhat_2(14)) = res(x^2/3) = eta =
2 — the first live vartheta at i >= 2. Corrected key Phi_2^2 -
27x*Phi_2 - 243x*Phi_1 vs gauge-naive (khat_0 twice as large).
* Corrected: ONE deg-8 factor over Q_3, sigma {(2,4)}, nfeltval
  ladder (x, Phi_1, Phi_2) = (1, 3, 7) EXACT; beta_1 a psi_2-root
  (val 1); beta_2 a psi_3-root; twisted residual NOT carried;
  eta = 2 confirmed at the leaf.
* NAIVE TOOTH: sigma = {(2,2),(2,2)} (the vartheta^{-1}-twisted
  residual y^2-y-2*eta_2 has square disc eta_2^2, splits) — THEOREM
  GENTOW5-B (a)/(b) fail at the gauge-naive recipe AT i = 2, the
  depth extension of PE1's i = 1 refutation, at exactly the pin's
  predicted twist; per-branch ladders (1,3,7) exact; per-branch the
  twisted residual IS carried and psi_3 is NOT.
* Both oracles: exact integer resultants (own Sylvester/fraction
  code) give (4, 12, 28) for BOTH keys — value data seam-blind, as
  the theory prices; sigma/residue rows on PARI (factor +
  factorpadic + idealprimedec + nfeltval).
* Run record (honest): run 1 RED 10/12 — ALL 12 were instrument
  defects, disclosed in-line and committed before re-run (gp-stdin
  multi-line loops need {} wrapping, so the PRIME rows never
  printed; one wrong arithmetic expression in my FA1 check; regex
  didn't parse PARI's +oo). Every mathematical prediction that
  printed on run 1 was already correct (NF3=1 DEGS3=[8] /
  NF3=2 DEGS3=[4,4]). Run 2 (parser fixes only, no prediction
  changed): 22/0 exit 0.
* Bonus for PE2-F-2: check FA1-LIFT machine-asserts the displayed
  lift family's flavor non-existence (11/2) at the frame the whole
  green chain then runs on with the re-solved member.

## S5. GRADE LINE

NOT CLEAN: 0 CRITICAL + 2 GAP (PE2-F-1 the psi^{(w)} flank of the
S3(a)/GENTOW2-r3 weld; PE2-F-2 the lift-display flank of the S2.1
pin) + 2 MINOR (PE2-F-3 GENTOW5-D's i = 1 edge; PE2-F-4 e >= 2
seam-live coverage). Counter stays 0/2; a repair round is owed
((a)/(b) re-scoped to psi^{(w)} or an honest w-clause, GENTOW2-A
r3-pattern; the lift display re-solved per flavor; the two minors).
What is NOT at stake: the gauge pin's repo-side content (verified
live at i = 2 this pass), TARGET 1, LEMMA GENTOW5-D's consumed
clauses, the depth-4 witness, and all committed machine records.

Verifier artifacts: `verification/openmath/gentow5_pe2_fresh.py` +
`gentow5_pe2_fresh_output.txt` (committed with this report; run-1
state committed separately for the honest RED disclosure).
