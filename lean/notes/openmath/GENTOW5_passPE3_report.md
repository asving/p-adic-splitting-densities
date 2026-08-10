# GENTOW5 passPE3 — HOSTILE VERIFIER REPORT

**VERDICT: NOT CLEAN — 0 CRITICAL + 1 GAP + 2 MINOR. Counter stays
0/2.** The r2 repairs as a system are CORRECT and survived a
measured-w live attack: the psi^{(w)} re-scope's discharge is
arithmetic-exact against the landed GENTOW2 B-law, the corrected
lift display re-derives from class separation with the Delta(r,t)
bookkeeping exact at two frames, and this pass's fresh route
verified THEOREM GENTOW5-B(a) AS RE-SCOPED **on the nose at a
measured w != 1 frame** (the first contact between the PE6-measured
cross-frame unit and this note's displays) while the NOSE tooth
fired against the pre-r2 on-the-nose claim. The one GAP is in the
PE1/PE2-unwalked remainder my charge named: THEOREM GENTOW5-B(c)'s
displayed statement carries a one-level index conflation (its
entry-read clause sits at stage i+2 while its degree/weight/pin/
floor clauses sit at stage i+1), making the displayed biconditional
false at every proper stage by a residual-degree count — and the
note's own committed witness f32 instantiates the counter-instance.
Machine leg: all four committed instruments re-run isolated
BIT-IDENTICAL (86/0 exact, 92/0 full-PARI, 15/0 PE1-fresh, 22/0
PE2-fresh); seals verified (5fa684c7 / dc499a49 / 839a8660);
artifacts byte-frozen through r2 as promised.

**Pass:** GENTOW5-passPE3, fresh context, zero prior stake,
2026-08-10. **Target:** `GENTOW5_PROOF_2026-08-09.md` @ HEAD (arc:
seal -> PE1 NOT CLEAN 1C+2G+3m @ 0160b94 -> r1 -> PE2 NOT CLEAN
0C+2G+2m @ 40f313a -> r2 = d37221e/f900dff/2d26c1a -> w-note rider
2b19e77). Protocol: quote-and-classify, fix nothing. Context read:
the note in full at HEAD; the PE1 + PE2 reports in full (routes
disclosed there NOT re-walked); the three r2 diffs + the rider
diff; GENTOW2_PROOF S5 AT HEAD (LEMMA GENTOW2-B [r3 RESTATED], B',
B'', the S5.1 re-scoped residue paragraph, the S4 re-scope
acdf97a); GENTOW2_passPE5 head + PE6 report/instrument/artifacts;
GENTOW1_PROOF S2 (LEMMA GENTOW-1's T-locus, the (c) template).
As-of rule carried: GENTOW2 ACCEPTED 2/2 (PE6 measured w != 1 at
the 6 measured primes of 4 frames); GENTOW5-B(a) re-scoped to
psi^{(w)}; the lift display = the per-flavor base re-solve.

---

## S1. FINDINGS

### PE3-F-1 GAP — THEOREM GENTOW5-B(c)'s displayed statement
### conflates two adjacent levels: the entry-read clause (level,
### slope, residual) sits at stage i+2 while the degree/weight/pin/
### floor clauses sit at stage i+1; as displayed the biconditional
### fails at every proper stage, incl. at the note's own witness

Quote (S3 (c), verbatim):

    (c) [BUDGETS AT LEVEL i+1 — GENTOW-1 re-based] the level-(i+1)
    tower-entry locus T_{i+1} (monic f of degree n = mu * D_{i+1}
    whose level-(i+1) stage read exhibits the full side of slope
    kappa_{i+2} := u_{i+2}/e_{i+2} with residual psi_{i+2}^{mu}) is
    weight-characterized: f in T_{i+1} iff every slot of f -
    Phi_{i+1}^{mu} clears weight mu*E_{i+1} + 1, with ... the node
    pins p_j >= (mu-j)E_{i+1} + 1, and the field floor
    dv_{i+1}(Phi_{i+1}(xi)) > E_{i+1}, exactly as in LEMMA
    GENTOW-1 (a)-(d).

The template (GENTOW-1's T, quoted at its source) anchors ALL its
clauses at the entered stage: degree mu2*D2, level-1 read, slope
kappa2 = u2/e2, residual psi2^{mu2}, box vs Phi2^{mu2} at
mu2*E2+1, floor dv2(Phi2) > E2 — read one level below the key,
stage data = the KEY'S OWN stage. Uniform transport therefore
forces the read clause of a Phi_{i+1}-anchored T_{i+1} to be
"level-i read, slope kappa_{i+1}, residual psi_{i+1}^{mu}". The
display instead pairs the (i+1)-anchored degree/weight/pin/floor
half with an (i+2)-anchored read half. Dimension count killing the
displayed pairing: deg f = mu*D_{i+1} gives a level-(i+1) polygon
of length mu; a full side of slope kappa_{i+2} (gcd(u_{i+2},
e_{i+2}) = 1) has lattice slots every e_{i+2}, residual degree
mu/e_{i+2}; the displayed residual psi_{i+2}^{mu} has degree
mu*f_{i+2}; equality forces e_{i+2}f_{i+2} = 1 — an improper
stage, excluded by DEF GENTOW5-1's properness l_i >= 2. The
proof's own displays sit at the THIRD anchoring: Step 1 prices
Phi_{i+2}^{mu} at weight mu*E_{i+2}, Step 2 sets g := f -
Phi_{i+2}^{mu}, and its parenthetical "(level i+2 per the
statement's (c) at i+1 — indices as displayed)" acknowledges the
shift but resolves it the wrong way (asserting the mixed display).
The substitution table at the head of the (c) proof itself says
"E2 -> E_{i+2}" while the statement displays E_{i+1}.

Failure scenario AT THE NOTE'S OWN WITNESS (committed record):
i+1 = 4, f = f32 (deg 32 = 2*D_4, mu = 2). Its level-4 read is ONE
side of slope 341/2 = kappa_5 with on-chord support {0, 2}
(committed artifact P-B3 row "f32@Phi4"), residual degree 1 =
psi_5 = y - 1 — NOT psi_5^{mu} = (y-1)^2, which cannot fit on a
2-slot side with e_5 = 2. Yet f32 satisfies the displayed weight
box exactly (g = -2^16*Phi_3 at wt_4 = 256 + 85 = 341 =
mu*E_4 + 1). So f32 satisfies the RHS of the displayed
biconditional and falsifies its LHS residual clause: (c) as
written is refuted by the note's own depth-4 record. A depth-r
consumer instantiating T_{i+1} as displayed either finds it empty
(residual-degree mismatch) or mis-sizes the entry problem by a
factor l_{i+2}.

Blast radius (checked): CONTAINED. (e) consumes only the
(i+1)-anchored pin clause — the sound half — and its conclusion
u_{i+2} > e_{i+2}E_{i+1} is DEF GENTOW5-1's floor-chain rung,
matching the DEF's provenance sentence; (d) is self-contained
(THEOREM GENTOW5-A's pattern); the S4 witness consumes (b) + (e);
no sentence in the note consumes the conflated residual clause;
external consumption not executed (S6). Repair shape (one clause):
re-index the read clause to "level-i stage read ... slope
kappa_{i+1} := u_{i+1}/e_{i+1} ... residual psi_{i+1}^{mu}" (then
GENTOW-1 is the i+1 = 2 instance verbatim, (e) and the DEF
provenance match as displayed, and Steps 1-2's displays prove the
i -> i+1 shifted instance, as their parenthetical half-says);
equivalently re-anchor degree/weight/pins/floor at i+2. This is
the species and weight of PE1's F-3 and PE2's F-2 (display-level
statement defect, intended content recoverable, no consumer
broken): GAP.

### PE3-F-2 MINOR — the w-note rider's single-site placement leaves
### two standalone "uncomputed" sentences stale

The rider (2b19e77) dates the w = 1-open disclosure at the S3(a)
statement site only. Post-PE6 (w MEASURED at the 6 primes of 4
frames; and this pass's fresh route adds a 7th prime), two sites
still read as composed with no rider adjacency: (i) the S6 grade
box, "w_i = 1 — the on-the-nose psi_{i+1} — is OPEN, the uncomputed
cross-frame unit" (TARGET 2 bullet); (ii) the (a)-proof
parenthetical "w_i being uncomputed it is not repo-constructible".
The w_i = 1-OPEN claims themselves remain true (closed form open;
unmeasured frames/levels undecided — the rider says exactly this);
only the word "uncomputed" as a standing description is dated.
Failure scenario: a consumer reading S6 alone (the standing grade
box) plans a w-measurement unit that PE6 already executed. Fix is
a one-line dated bracket at each site or a rider pointer.

### PE3-F-3 MINOR — the consumer walk's S4-witness bullet points at
### a record that is not at the pointed location

Quote (the [GT5-r2] walk): "the witness does not discriminate the
w-leg (recorded with the seam axis in S6's coverage box)". S6's
coverage box (the GENTOW5-BOX-A paragraph with the [GT5-r1] seam
axis and [GT5-r2] compound rows) carries NO w row; the witness's
w-triviality is recorded at the S6 TARGET-2 bullet instead.
Failure scenario: a reader auditing coverage from the box takes
the w axis as tracked there and misses that the witness's
w-blindness is a separate (bullet-level) record. One-pointer fix.

## S2. CLEAN CHARGES (attacked and survived)

* **The psi^{(w)} re-scope's proof discharge (r2 F-1, the central
  leg).** Verified against GENTOW2 S5 AT HEAD, quote-exact: the
  landed B-law u(beta_t) = theta(t)*w^{f3-t} with theta(t) :=
  res(nhat_2(u_3(f_3-t))/nhat_2(u_3)^{f_3-t}) and w :=
  R_{3,kbar}(nhat_2(u_3)), kbar = u_3/e(mu_2) — the note's
  theta_i(t)/w_i displays match verbatim at i = 2. Reciprocality
  theta_i(t) = vartheta_{i,f-t}^{-1} checked at the definitions
  (same monomial quotient, inverse read). The cancellation
  re-derived independently: pinned digit c_t*vartheta_{i,f-t}
  meets u_i(beta_t) to give c_t*w^{f-t}; y^f - Sum c_t w^{f-t} y^t
  = w^f psi(y/w) expanded and confirmed = psi^{(w)}. The theta leg
  cancels, the w-leg survives — exactly as displayed. At i = 2 the
  pinned recipe IS GENTOW2's multiplicative prescription (c_t :=
  theta(t)^{-1} a_t), so the re-scoped (a) is the landed lemma
  verbatim; the i >= 3 transport honestly rides the named S2.3
  annex pin. Admissibility cites verified at source: the PE5 quote
  ("psi_3^{(w)} is verifiably admissible for every w in K_2^x",
  75923bc line-exact), the GENTOW2-A consumption note ("consumes
  only hypothesis (ii) with an admissible residual"), the S4
  re-scope commit acdf97a ("consumption AT psi3^(w)"). MACHINE:
  this pass's leg W verified the display live at measured w != 1
  (S4 below) — the first non-arithmetic contact the re-scope has.
* **The per-consumer ripple walk (r2 F-1's second half) — five
  consumers re-verified independently:** (1) (b)'s P_{i+1} clause:
  psi^{(w)}(y0) = 0 iff psi(y0/w) = 0, so an FGMN psi^{(w)}-root
  divided by w is a repo psi-root — re-derived, and machine-pinned
  live (leg W: Y == W*B measured, B a psi_3-root, psi_3(Y) != 0);
  the "(B'')" cite is fair (B'''s consequently-clause displays the
  w-conjugacy). (2) (c) Step 1's power dictionary:
  (psi^{(w)})^{mu} = (psi^{mu})^{(w)} since y -> y/w is a ring map;
  the repo-side translation psi^{mu} follows by the same per-grade
  w-division — checked as arithmetic. (3) the S4 witness: K_i =
  F_2 forces K_i^x = {1}, w_i = 1 — trivial, and this pass's
  depth-6 extension (all-F_2) is likewise w-trivial, consistent.
  (4) sigma/degrees/irreducibility: y -> wy is a K_i[y]
  substitution automorphism; factor patterns preserved at each w —
  checked, and leg W's naive-twin row shows exactly a residual
  CONTENT change (split vs inert) never a pattern-transport
  failure. (5) (d): S1.3's statement re-read — gr(L2), R_N,
  multiplicative convention throughout, no FGMN read consumed:
  w-free as claimed.
* **The w-note rider itself (2b19e77).** Pure insert at the (a)
  disclosure site; claims verified against the PE6 record: 6
  measured primes (NPR 1/1/2/2 over LD1/LD3/GA1/GA3, run-2 68/0,
  seal ade1727, report deba21b), avatars z1/z1^2/z2^2/z2,
  u3-dependence (both same-tower pairs differ), acceptance 2/2
  (21293c8). Its fences are honest: closed-form derivation open;
  unmeasured frames/levels undecided; "measured record does not
  decide w_i at ... levels i > 2" — correct (PE6 is i = 2 only).
  Residue: the two stale flank sentences = PE3-F-2.
* **The corrected lift display (r2 F-2) RE-DERIVED, not just
  re-read.** Height bookkeeping: dv_i(x^{e_1 r}) = e_1 r
  (ehat_i/e_1)h and dv_i(Phi_j^{e_{j+1}t_j}) = e_{j+1}t_j
  (ehat_i/ehat_{j+1})u_{j+1} sum to Delta(r,t) — so M_{r,t}(m) =
  nhat_i(m - Delta)*step sits at height m exactly; ladder-range
  bounds re-derived (i0' + e_1 r <= e_1 f_1 - 1; b_j' + e_{j+1}t_j
  <= l_{j+1} - 1); deg M < D_i by the telescoping max (e_1f_1 - 1)
  + Sum (D_{j+1} - D_j) = D_i - 1; flavor indexing injective (b' <
  e_{j+1} forces t_j = floor(exponent/e_{j+1})), count f_1...f_i =
  the within-class census. FR-A's numbers re-solved by hand
  (nhat_2(11) = 3^5 x, the 0 -> 1 x-re-solve; fixed-base demand
  11/2). NEW MACHINE CONTACT at a second frame (GA3, e_2 = 2
  tower): the fixed-base t_1 = 1 flavor demands pi-exponent 35/2
  at height 82 and 13/2 at height 41 (both non-existent, machine-
  asserted); the re-solved members 2^18*PHIP^2 (x-exp re-solves
  1 -> 0 — the direction OPPOSITE to FR-A's) and 64x*PHIP^3 are
  exact; the flavor residues computed by the gamma-lattice are the
  fixed letter z2 at both heights, and the inverse-twisted digit
  solve (z2^2 = 1 + z2 -> digits (1,1)) produced the key the whole
  green chain then ran on. The derivation-from-class-separation
  claim checks at both frames; its general-i leg rides S2.3 step
  (3) as stated.
* **LEMMA GENTOW5-D's r2 edge (F-3) + the weight system.** The
  i = 1 edge re-derived (wt_1(Phi_1) = E_1 = D_1 h = wt_1(x^{D_1}):
  the x-carry IS the top carry, PRESERVED; rung range empty); the
  x-carry's i >= 2 strict pricing consumes rung 1 in-datum; the
  grid-4 equality 340 = 340 = 340 re-computed (Phi_3^2 = Phi_4 +
  2^8 Phi_2 with wt(2^8 Phi_2) = 128 + 42 at dv_4... = 170 scale:
  170 = 170 = 170 as displayed). Named consumers instantiate
  i >= 2 — the edge is unconsumed, as stated.
* **The compound coverage row (r2 F-4).** Accurately worded as
  composed (FR-1 e_2 = 1; FR-A e_2 = e_3 = 1; battery seam-blind).
  Note for the orchestrator's next fold: this pass's leg W is the
  first machine contact AT the compound (z2 live x e_3 = 2 x
  f_3 = 2), so the row is now dated in the conservative direction.
* **Level-r grammar + depth-4 witness (the unwalked remainder,
  minus (c) = PE3-F-1).** Normalizer recursion re-solved by hand
  at nhat_1(5)/nhat_2(21)/nhat_3(85)/nhat_4(341) and the S2.2
  dv_4-ladder solve (RHS 170, parity forcing b_2 = 1); floor chain
  5 > 4, 21 > 20, 85 > 84, 341 > 340 tight; first-live n = 2^{r+1}
  re-derived from D_r >= 2^r x mu >= 2; T-B1's drain factorization
  re-expanded exactly; S3(e)'s telescoped inequality re-derived
  (base-rung equality only); khat side-height identity
  e_{i+1}u_{i+1}(f-t) + e_{i+1}t u_{i+1} = E_{i+1} checked; (b)'s
  cite instantiation (F = phi, the "for any 1 <= j <= r"
  quantifier) re-read against the note's fence. MACHINE: the
  grammar extended one rung past the committed record (leg D5) and
  held exactly.

## S3. MACHINE-LEG INTEGRITY

* **Pins:** gentow5_checks.py md5 5fa684c7... = the note's claim;
  artifacts dc499a49... (exact) / 839a8660... (full) = the note's
  claims; diffstat 40f313a..HEAD shows the r2 round + rider touched
  the note only — sealed artifacts BYTE-FROZEN through r2 as S8
  promises.
* **Isolated re-runs (/tmp copies, this pass): four for four
  BIT-IDENTICAL** — exact leg 86/0 exit 0; full leg (--pari) 92/0;
  PE1 fresh 15/0; PE2 fresh 22/0 (diff vs committed artifacts
  empty in each case).
* **Tautology audit:** PE1's and PE2's audits stand (nothing
  machine-side changed since). This pass's instrument: predictions
  hand-derived pre-seal in the docstring; the own-arithmetic legs
  (Fractions heights, gamma-lattice splits, Bareiss resultants)
  are independent of the PARI legs (factorpadic/nfinit/nfeltval/
  nfmodpr); the one arithmetic-closure row (Y == W*B) is disclosed
  as such in the docstring — the discriminating physics is carried
  by WW/WB/WPSIW/WNOSE and the two teeth; the naive-twin row
  doubles as a cross-check against the committed GA3 record and
  matched it ([16,16]).

## S4. FRESH ROUTE (disjoint from PE1's FR-1/2/3 and PE2's FR-A;
## `gentow5_pe3_fresh.py`, run-2 48/0)

**LEG W — GA3\*: the first w-LIVE contact with this note's displays,
at the PE2-F-4 compound.** Frame = GENTOW2-PE6's GA3 tower (GB:
PHIP = x^2-2, e1=2 f1=1, e2=2 f2=2, u2=5, z2 live; stage 3 e3=2,
f3=2, u3=41 — vartheta_{2,2} = z2 live x e_stage = 2 = the
compound, machine-untouched before this pass), but the KEY IS NEW:
the S2.1 pinned recipe run for the irreducible target psi_3 =
y^2 - y - z2 (khat_1 = 512*PHIP; khat_0 = lift(z2*vartheta_{2,2};
82) = lift(z2^2; 82) = 2^20 x + 2^18 PHIP^2 by the r2 display).
Results (each preregistered): carrier — ONE factor deg 32, ONE
prime (8,4) (the program's first (8,4) leaf); ladder (4,10,41)
exact + v(pi3) = e/4 (a new Lemma 3.13(1) pin); dual oracle
(own-Bareiss RES 16/40/164 = 32x the exact values); repo class B
satisfies psi_3 exactly and generates F16 (the re-scope's w-blind
clause, live); THETA0 = z2^2 remeasured at the new prime; **w
MEASURED at a 7th prime, first carrier-(8,4) geometry: w = z2 !=
1**; **PSIW: psi_3^{(w)}(Y) = 0 — THEOREM GENTOW5-B(a) AS
RE-SCOPED, verified on the nose at measured w != 1** (Y = the FGMN
class avatar); **NOSE TOOTH FIRED: psi_3(Y) != 0** — the pre-r2
on-the-nose claim fails at this frame, exactly as the re-scope
prices; MULT0 = c_0 (the vartheta cancellation measured live at
e_3 = 2 — the S2.1 pin's derivation at the compound); NAIVE TWIN
(= the committed GA3 key, which IS the untwisted prescription for
this target) splits [16,16], matching the committed record.

**LEG D5 — the first depth-5/6 contact at the witness ladder.**
The S4.1 chain extended one rung: u_6 = 1365 (minimal odd > 2*E_5
= 1364), nhat_5(1365) = 2^32*Phi_4 (recursion re-solved), f64 :=
f32^2 - 2^32*Phi_4 = the first depth-6 key, deg 64. Results (each
preregistered): RES ladder v2(Res(f64, g)) = (32, 80, 168, 340,
682, 1365) for g = (x, Phi_1..Phi_4, f32) EXACT on own-Bareiss
(96x96 top); factorpadic ONE factor deg 64; nfinit leg (budgeted)
came back GREEN: ONE prime e = 64, f = 1, nfeltval ladder
bit-equal to the resultant route; Phi_4's own irreducibility
pinned (never a committed chk row); TOOTH: f64m := f32^2 -
2^40*Phi_2 (height 1364 = 2*E_5, gcd proviso violated) collapses
into the drain — the hand-derived pre-seal identity f64m =
Phi_4*(Phi_4^3 - 2^17 Phi_3 Phi_4 + 2^32) holds exactly,
Res(f64m, Phi_4) = 0, factorpadic [16, 48]. The gcd proviso is
machine-load-bearing at depth 6.

**Run record (honest):** run 1 RED 48/2 (committed as-is,
eb4103d) — both misses one instrument defect, the documented
gp-stdin trap (the only two multi-line gp print statements never
printed; the factorizations behind them were computed); print
lines joined, no prediction changed, disclosed in-line; run 2
48/0 exit 0 (9f0eca7). Every mathematical prediction that printed
on run 1 was already green.

## S5. GRADE LINE

NOT CLEAN: 0 CRITICAL + 1 GAP (PE3-F-1, the (c) statement's index
conflation — refuted at the note's own witness record) + 2 MINOR
(PE3-F-2 stale "uncomputed" flanks; PE3-F-3 the coverage-box
pointer). **Counter stays 0/2**; a repair round is owed (one-clause
re-index of (c)'s read half + the two dated one-liners). What is
NOT at stake: the r2 repairs themselves (the psi^{(w)} re-scope
now carries a live measured-w verification; the lift display now
has two-frame machine necessity), the w-note rider, TARGET 1,
LEMMA GENTOW5-D, (b)/(d)/(e), the depth-4 witness, and the
committed machine records — all attacked and held. The fresh
route's two firsts (w-live contact at the compound; depth-6
extension) are conservative-direction data for the S6 coverage
rows at the orchestrator's next fold.

Verifier artifacts: `verification/openmath/gentow5_pe3_fresh.py`
(sealed 0d94ed8, md5 a62c3894 pre-repair) +
`gentow5_pe3_fresh_output.txt` (run-1 RED, kept) +
`gentow5_pe3_fresh_output_run2.txt` (GREEN 48/0). Isolated re-runs
in /tmp/gt5pe3_iso (session-local; verdicts quoted in S3).
