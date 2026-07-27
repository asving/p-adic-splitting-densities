# FABLE VERIFY — §X-EXHAUST rev 7 (fresh-instance dual half; 2026-07-27)

Scope: MOVES_2026-07-24.md lines 10947–11555 (§X-EXHAUST rev 7) + pass records
(passes 1–7, Codex acceptance at passes 8+9). Codex half already CLEAN; this is
the independent Fable half. Verifier charge: quote-and-classify, fix nothing.

## A. Index-table recomputation (duty a, part 1) — VERIFIED

(IND) recomputed against the (P1) pin (GMN_citations.md, Def 4.12 verbatim):
E=el, H=hl, d=l gives (EH-E-H+d)/2 = l(ehl-e-h+1)/2 — the T1 entry EXACT.
Pick split re-derived: interior (EH-E-H-d)/2+1 plus on-side d-1 sums to (IND). OK.
- T1 lower bound: ehl-e-h+1 = e(hl-1)-(h-1), increasing in e (hl>1 at l>=2);
  at e=1 it equals h(l-1); so >= h(l-1) >= 1 at l>=2. Bracket EXACT.
- T1 witness (s+e, u+(l-1)h): on S (y-value at x=s+e is u+(l-1)h), height
  (l-1)h >= 1 above L, s+e > s. Needs ON-OR-BELOW — pinned at (P1). OK.
- T2 = l=1 case of (IND): (eh-e-h+1)/2 = (e-1)(h-1)/2; integrality from
  gcd(e,h)=1 (not both even). Witness (s+1,u+1): strictly below S iff
  e < h(e-1) iff (e-1)(h-1) > 1 — algebra checks; (2,2) gcd-excluded, so
  min value (e-1)(h-1)/2 >= 1 over e,h >= 2 coprime. EXACT.
- T3: (e-1)(1-1)/2 = 0; T4: (1-1)(h-1)/2 = 0; endpoint rulings match
  Remark 4.14's two strictness clauses. OK.
- Degree charge: each T3 has e >= 2, Pi e_i <= n along a branch, so
  #T3 <= floor(log2 n). OK (n=3 -> 1, as env* uses).
- X.1b reduction arithmetic: d_total <= v/2 + floor(log2 n) + s*v gives
  v >= (d_total - floor(log2 n))/(s + 1/2). OK.

## B. Letter-instance census check (duty a, part 2) — PASS (0 violations)

Checker: lean/notes/xexh_check_FABLE_2026-07-27.py (independent construction).
Layer 1 (order-0 sweep, STRONGER than one branch's CUM(0): v_p(disc f) >=
2*Sum_{all principal sides} ind(S)): cubics p=2 box 8^3 (445 f, rows hit
T1=16/T2=8/T3=72/T4=103), cubics p=3 box 9^3 (644 f), quartics p=2 box 8^4
(3564 f, T1=155/T2=32) — 0 violations in 4653 checked; min slack 0
(tight instances exist, e.g. x^2+2x+4: L = Q2(sqrt-3) UNRAMIFIED (v(disc L)=0),
so (P2) forces ind = v2(-12)/2 = 1 — a p=2 DISCRIMINATING witness for
ON-OR-BELOW, independent of the record's Z3 witness; strictly-below gives 0).
Single instances, exact (P2) identity: x^2+8 (T2, e=2,h=3: ind=1;
v2(disc)=5 = 2*1 + 3 = 2ind + v2(disc Q2(sqrt-2))); x^2+6x+36/Z3 (the (P1)
witness: v3 = 3 = 2*1 + 1) — both EXACT.
Layer 2 (a T1 -> depth-1 letter instance): f = (x^2-2)^2 - 2^m over Z2,
m = 5..15 odd. Level-0 read: e=2,h=1,l=2 (T1), ind0 = 2, selection (1,2).
Depth-1 normalized side (0,2m)-(2,0): e=1,h=m,l=2, T1 row, ind1 = m by (IND).
Measured: v2(disc) = 2m + 10 exactly = 2*(ind0 + ind1) + 6 (two ramified
quadratic leaves at v(disc)=3 each) — the claimed increment accounts for the
FULL disc growth (+4 per m->m+2 = 2*Delta ind1). The raw-frame height of the
same side differs from the normalized m — a live illustration that
(X1a-ALIGN)'s raw-vs-normalized duty is real and correctly fenced OPEN.

## C. Four-population partition break attempts (duty b) — NO BREAK

Population = {T1/T2 increments} u {T1 recenterings} u {T3} u {T4}, over
continuing nodes (selection != bottom). Attack lines, all closed:
1. Node in NO row: rows key on (l>=2 | l=1&e>=2&h>=2 | l=1&e>=2&h=1 |
   l=1&e=1) — exhaustive/disjoint over e,h,l >= 1. h >= 1 at every read by
   (I-aug) (line 1148: side slope exceeds u(key), re-established per landing);
   slope-minus-infinity / no-eligible-side is the (tau-ns) CELL status — a
   halt, never a continuing node. T0 openings and T5 terminals excluded by
   X.0's definitions. No orphan found.
2. Node in TWO populations: increment/recentering is a function of the
   node's own (e,g): e*g >= 2 increment, e*g = 1 recentering — total
   dichotomy per line 6228 ("NO OTHER MOVE EXISTS") + D.10 Species lemma
   (recenterings only at e_read = 1; at e >= 2 the slot-1 value escapes the
   coefficient value group via gcd(e,h)=1). Matches (G5) POST-INC/POST-REC.
   Hence: T2/T3 (e>=2) are increment-only; T4 (l=1 forces g=mu=1, e=1) is
   recentering-only; T1 splits cleanly by e*g. No double count.
3. Probed corner: (g,mu)=(1,1) selections on l>=2 sides (engine-continuing
   below-halt reads; mu=1 is the tau-irr saturation at the PARENT) — these
   are T1 nodes in exactly one class by e*g; NOTE the T1 row's parenthetical
   gloss ("ALL increments with mu*g >= 2 AND all mu >= 2 recenterings live
   here") does not name them, but the row KEY (l >= 2) and the partition
   (by e*g) carry them fine — gloss imprecision only, see F.3.
4. d_total is defined on T_can (engine tree, below-halt reads included) per
   X.0 — so mu=1 continuations counting as nodes is consistent; X.2's
   family (tau-halted branches/prefixes) are chains of T_can too. Coherent.

## D. (τ-ns)-FREE decidability + cap conventions (duty c) — COHERENT

- (tau-ns) is a CELL status: empty branch set / J(f) = 0 (line 7106), i.e.
  the cluster factor is EXACTLY Phi^mu ((z-3)). Per-node, given f exactly,
  this is determined by f's cell data — the predicate "(tau-ns)-FREE" is
  well-defined pointwise. It is NOT finite-level decidable (an exact
  condition), and the note NEVER claims it is: X.3's (NS-ROUTE) paragraph
  explicitly types Undec(N) as never a level-N residue of an exact ns
  condition, and ns-leaf f sit in Undec(N) at every N per (NS-d). Coherent.
- Boundary instances tried: (i) f ns-looking to level N but not exactly ns:
  its branch is (tau-ns)-FREE with large threshold — exactly the bridge's
  existential; no contradiction. (ii) H = read-free root history (tau-hen):
  cap := 0 (hen/no-window), max h(empty) := 0 — both conventions fire, cap
  TOTAL. (iii) H = continuing prefix: cap := 0, consistent (leaf-detection
  cell not reached). (iv) confirming W=1 read: T5/selection-bottom by (G6)
  — not continuing, detection charged at the parent (mu=1), consistent with
  TB-CAP. (v) mixed tree (tau-irr + tau-ns leaves): f lands in the ns-fiber
  piece; its (tau-ns)-FREE branches may also witness piece 4 — the
  decomposition is a COVER, not a partition, so overlap is harmless. OK.

## E. Elementary tail arithmetic (duty d) — VERIFIED (one cosmetic slip)

- (3b) restated VERBATIM from the accepted decomposition note (Lemma 3.3,
  line 399 there). Numeric legs recomputed: p=2, 2*2^{-ceil(D/2)} at
  D=2,4,6,8 -> 1, 0.5, 0.25, 0.125 EXACT; p=3, v_3(3)=1, n*v=3:
  2*3^{-ceil((D-3)/2)} at D=5,7,9 -> 2/3, 2/9, 2/27 EXACT.
- Deep-leg plumbing: D = (d* - floor(log2 3))/(s+1/2) = (N/2-2)/2.5 into
  (3b)'s exponent — matches env*(N)'s display; real (non-integer) D is safe
  (the bound is monotone: mu{v>=D} = mu{v>=ceil(D)} <= displayed). OK.
- env* toothlessness recomputed: p=2, N=8: deep = 2*2^{-1} = 1, tall =
  53*2^{-3} = 6.625; p=3, N=8: deep exponent ceil(-1.1) = -1 -> deep = 6,
  tall ~ 1.96 — env* > 1 everywhere at N <= 8, both primes. HONEST as
  declared. C_T(3) = 53 = the M-n3 catalogue letter count (53 letters,
  groups 21/21/6/1/4) — the union-bound COUNT is derived as claimed.
- COSMETIC SLIP (F.2 below): the parenthetical slope expression
  "c_d/(2(s+1/2)(n-1)) = 1/10" evaluates to 1/20 as written; the correct
  expression is c_d/((s+1/2)(n-1)) = (1/2)/(2.5*2) = 1/10. The quoted VALUE
  1/10 and the toothless conclusion are both correct (recomputed directly:
  dE/dN = (1/2)/2.5/2 = 1/10). Formula display only.

## F. Fresh sweep (duty e) — findings list

1. GAP (record staleness). The section STATUS block (line 11544) still reads
   "STATUS: rev 4, 2026-07-27 — ... Awaits pass 4" while the live text is
   rev 7, Codex-accepted at passes 8+9. Nothing mathematical inside the
   block is wrong (kernel/hypothesis lists match), but the rev stamp
   contradicts the acceptance record. Same class as §T-ASSEMBLY pass-4's
   "stale bracket" gaps.
2. COSMETIC (arithmetic display). X.5(iii)'s deep-leg slope parenthetical:
   spurious factor 2 in the displayed constant expression (see E). Value
   and conclusion unaffected.
3. COSMETIC (gloss imprecision). T1 row parenthetical omits the mu*g = 1
   engine-continuing selections on l >= 2 sides: an e>=2, (g,mu)=(1,1)
   increment is not covered by "increments with mu*g >= 2", and an
   e=1,(g,mu)=(1,1) recentering is not covered by "mu >= 2 recenterings".
   Row key and the partition classify both correctly; no display below
   consumes the parenthetical. Gloss only.
4. Checked clean, no finding: (X.1a)'s assembly chain (one-branch lower
   bound needs no multiplicity correction — nonneg terms; (P2) reducible
   form via Def 4.11 + resultant multiplicativity, per the pin); the
   X.1b/X.3 tag discipline ("NO route avoids X.1b" — verified against both
   (a1)/(a2) routes: (X1a-ALIGN) indeed bounds nothing about T4);
   WEIGHT-CHARGE's non-claim status (no derivation smuggled); the
   Koenig bridge (finite side menus + finite residual factors); X.3(d)'s
   monotone assembly (trichotomy closes the undetected-at-every-level
   case to ns); (X2-HYP)'s d_total+1 counting (one terminal read max);
   s(3)-probe well-definedness (a recentering forces a level-0 repeated
   factor, v_p(disc) >= 1); c_0(3)=4 line (3h+1 <= 4h at h >= 1);
   X.5(i)'s prefix-sweep framing (disc-zero f vacuous at v = infinity).

## VERDICT

0 CRITICAL. 1 GAP (record staleness: the rev-4 STATUS stamp on rev-7
accepted text). 2 COSMETIC (the 1/20-vs-1/10 slope display; the T1
parenthetical gloss). Duties: (a) index table recomputed EXACT from the
(P1) pin + census PASS (4653 f, 0 violations; depth-1 instance matches GMN
to the unit); (b) partition NOT broken (dichotomy total by e*g + Species
lemma); (c) predicate/cap conventions coherent on all boundary instances
tried; (d) tail arithmetic exact. None of the three findings touches a
displayed claim's truth or a kernel's fencing. CLEAN at the dual bar
(findings are record/display class, below the critical/gap-that-blocks
threshold used for acceptance; the one GAP is a one-line stamp fix).
