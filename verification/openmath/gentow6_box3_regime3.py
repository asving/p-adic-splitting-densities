#!/usr/bin/env python3
"""GENTOW6-BOX-3 machine leg: THEOREM GENTOW-6.7 (regime-3 top-slot
classification at mu2 = 2) + COROLLARY-THEOREM GENTOW-6.7C (the
j*-1 band one m up) — sealed instrument, two-commit seal (docstring
preregistered at commit 1, BEFORE the first run). Note:
lean/notes/openmath/GENTOW6_BOXES_2026-08-10.md S8.

ENGINE: imports the COMMITTED gentow6_box1_mu3.py (md5 of record
c98cb423ce3acecf65a6e6a02a979b2d, asserted at import, never edited)
for its Frame class carrying the DUAL R/E division routes; adds a
FRESH route F (own dev + own exact Y-division + one terminal
reduction, independent code in this file) — triple-route
slot-dict equality is the functoriality face. PARI/gp decorrelation:
factorpadic carrier shapes on the five NEW keys + P36, poldisc on
j' = 0 perturbed members.

FRAMES — five NEW regime-3 genres (mu2 = 2):
 R3A p=2 Phi'=x^3-2 (e1=3) e2=1 f2=2 u2=4 c=(1,1):
     Phi2 = Phi'^2-2x*Phi'-4x^2; i=(2,1), s*=1, chi=2c0c1=0 mod 2.
 R3B p=3 Phi'=x^3-3 e2=1 f2=2 u2=4 c=(-2,-1):
     Phi2 = Phi'^2+3x*Phi'+18x^2; chi=2c0c1=4=1 mod 3 (attain).
 R3C p=2 Phi'=x^4-2 (e1=4) e2=1 f2=2 u2=5 c=(1,1):
     Phi2 = Phi'^2-2x*Phi'-4x^2; i=(2,1), s*=0: j*3=0 — the
     above-top clause frame (ShC_1 == 0 identically).
 R3D p=3 Phi'=x^4-3 e2=1 f2=3 u2=5 c=(1,1,1): Phi2 = Phi'^3
     -3x*Phi'^2-9x^2*Phi'-27x^3; i=(3,2,1), s*=2 via TWO pairs
     {1,1},{0,2} at one slot: chi=c1^2+2c0c2=3=0 mod 3 (cancel BY
     UNITS at odd p).
 R3E p=3 same shape, c=(2,2,1): Phi2 = Phi'^3-3x*Phi'^2-18x^2*Phi'
     -54x^3; chi=4+4=8=2 mod 3 (attain) — the unit-flip sibling.
COROLLARY frames: P34/P35/P36 = GEN-P3 genre (Q3, Phi'=x^2-3,
u2=5, Phi2=Phi'^2-18x, chat=2) at mu2=4/5/6; X3 = FR5X at mu2=3 and
A53 = FAM-A5 at mu2=3 (6.5-battery reproduction rows, committed
vectors); P33 cross-pin.

CONSTANTS (asserted): R3A E2=8 delta=1 THETA=[17,9]; R3B same;
R3C E2=10 delta=1 THETA=[21,11]; R3D/R3E E2=15 delta=1
THETA=[31,16]; P3m THETA_j=(m-j)*10+1; X3 [87,61,35]; A53 [31,21,11].

PREREGISTERED PREDICTIONS (hand-ledger-derived from 6.7/6.7C before
any run; no pre-seal smoke; run-1 RED kept + disclosed if any):
 P-TRIPLE routes R == E == F slot-dict-identical on every scored
   self-shadow (10 frames), R == E also on perturbation rows.
 P-DRAIN honest read of each key power = DRAIN (C_j all zero).
 P-R3A ShC_1 = {(0,0): 16} exact (v=4 > 3: chi = 0 mod 2), graded
   height-9 = THETA_1 digit at (0,0) ZERO, pin(ShC_1) = 12; the
   cascade: ShC_0 = {(1,1): 48, (2,0): 64} exact, pin 17 = THETA_0,
   graded-17 digit at (1,1) NONZERO (the s=0 diagonal survives one
   coordinate DOWN while the top slot cancels).
 P-R3B ShC_1 = {(0,0): 108} exact (v = 3 = a0+a1, chi = 1 mod 3),
   graded-9 NONZERO, pin 9 = THETA_1 (attainment ON the floor);
   ShC_0 = {(2,0): -1944} exact with slot (1,1) ABSENT (the
   +324x/-324x INTEGRAL cancellation), pin 17 = THETA_0, graded
   NONZERO at (2,0).
 P-R3C ShC_0 = {(0,1): 16} exact, v = 4 = 2a_0, graded-21 NONZERO,
   pin 21 = THETA_0; ShC_1 = {} IDENTICALLY (6.7(a) above-s*).
 P-R3D ShC_1 = {(0,0): 243} exact (chi = 3*81: v = 5 > 4), graded
   height-16 = THETA_1 digit ZERO (odd-p unit cancellation), pin
   20; ShC_0 = {(1,2): 1215, (2,1): 2916, (3,0): 6561} exact, pin
   31 = THETA_0, graded-31 NONZERO at (1,2) and at (2,1).
 P-R3E ShC_1 = {(0,0): 648} exact (chi = 8*81: v = 4), graded-16
   NONZERO, pin 16 = THETA_1; ShC_0 = {(2,1): 14580, (1,2): 3888,
   (3,0): 34992} exact, pin 31, graded-31 NONZERO at all three.
 P-C34 [corrected of record, 6.7C'] P34 ShC_1 slot (1,1) = 46656 =
   2*C(4,3)*8*729 exact, graded height-31 = THETA_1 NONZERO,
   pin(ShC_1) = 31 (rest of the coordinate recorded; run-1
   measured (0,0): 104976 = C(4,4)*18^4, matching the k=4 e=2
   branch prediction).
 P-C35 [corrected] P35 ShC_2 slot (1,1) = 116640 = 2*C(5,3)*8*729
   exact (v = 6, 20 a 3-unit), graded height-31 = THETA_2 NONZERO,
   pin(ShC_2) = 31 (the (0,0) slot recorded; run-1 measured
   524880 = C(5,4)*18^4 as predicted).
 P-C36 [corrected] P36 ShC_3 slot (1,1) = 233280 = 2*C(6,3)*8*729
   exact (v = 6, 40 a 3-unit), graded height-31 = THETA_3 NONZERO,
   pin(ShC_3) = 31 — attainment at j*-1 = 3 at p = 3 WHILE the top
   coordinate cancels (3 | C(6,2) = 15): ShC_4 = {(0,1): 4860}
   exact with graded height-21 = THETA_4 digit ZERO (v = 5 > 4),
   pin(ShC_4) = 25; ShC_5 = {} (6.5(c)).
 P-CBAT committed 6.5-battery vectors reproduced bit-exactly:
   X3 [{(1,1): 524288} pin 91, {(0,1): 12288} pin 61, {}];
   A53 [{(1,1): 128} pin 35, {(0,1): 48} pin 21, {}];
   P33 [{(1,1): 11664} pin 31, {(0,1): 972} pin 25, {}] — and the
   6.7C' closed form 2*C(m,3)*chat^3*p^{3a0} EQUALS the measured
   j*-1 slot at X3 (2*2^18 = 524288), A53 (2*2^6 = 128), P33
   (2*8*729 = 11664), P34 (8*5832 = 46656), P35 (20*5832), P36
   (40*5832 = 233280).
 P-FLOOR every frame, every member (self + 2 perturbed per new
   frame), every j: mindiff_j None or >= THETA_j.
 P-PARI factorpadic carriers {(3,2)} R3A/R3B, {(4,2)} R3C,
   {(4,3)} R3D/R3E, {(4,1)} P36; poldisc != 0 at the j' = 0
   perturbed members of R3B, R3C, R3E (3 jobs).
TEETH (kill counts asserted):
 T-TOPPAIR mutant "the top slot is the (t*,t*) pair's whenever some
   pair overflows" (pin(ShC at floor((2 e2 t*+1)/(e2f2))) = THETA
   there) — dies at R3A (12 != 9), R3C ({} at j1), R3D (20 != 16):
   3 kills; blind at R3B/R3E (disclosed: there j_mut = j*3 anyway).
 T-CHI mutant chi WITHOUT the 2-delta multiplicities (all
   coefficients 1) — predicts attain at R3A (c0c1 = 1 != 0) and
   R3D (1+1 = 2 != 0), predicts CANCEL at R3E (4+2 = 6 = 0 mod 3):
   3 kills; blind at R3B/R3C (mutant = truth there).
 T-CVAL v*-1 at the attained s*-slots (R3B, R3C, R3E): 3 kills.
 T-M5SUM corollary mutant coefficient C(m,2)+C(m,3): wrong value
   at X3 (4*2^18), P34 (10*5832) and P36 (35*5832): 3 kills; BLIND
   at P35 (10+10 = 20 = 2*C(5,3) coincidentally — disclosed).
 T-OLDLAW the seal's refuted C(m,2)-C(m,3) display as a mutant:
   wrong value at P34 (2*5832) and P36 (-5*5832), predicts an
   ABSENT (1,1) at P35: 3 kills; BLIND at m = 3 frames (the two
   laws coincide there — which is how the seal slipped).
 T-PARITY mutant "the graded j*-1 digit sits at the even slot
   (1,0)" — graded read at (1,0) must be zero at X3-j0, P34-j1,
   P36-j3: 3 kills.

RUN-1 RED DISCLOSURE (5 violations, THEOREM-FACING, artifact kept
at gentow6_box3_regime3_output_run1_RED.txt md5 c07980ad, sealed
instrument md5 17fecec4 @ commit after 82a51147): the seal's
corollary rows P-C34/35/36 + CFORM carried COROLLARY 6.7C's
binom(m,2)-binom(m,3) coefficient; the instrument measured
46656/116640/233280 = (8/20/40)*5832 at the three (1,1) slots —
the hand ledger had priced the pair branch's descent as ONE step
of coefficient chat*nhat, but the iterated K2-division at T = {0}
is the K2-adic binomial (LEMMA GENTOW-6.7D in the note): descent
from entry coordinate r to coordinate j carries multiplicity
binom(r, j); the corrected law (pair (m-2)*C(m,2) minus triple
C(m,3)) = 2*C(m,3) reproduces every measured value and coincides
with the refuted law at m = 3 (multiplicity 1) — which is why the
committed FR5X/A53/P33 rows could not catch it. The m = 5
"integral degeneration" is WITHDRAWN; p = 2 | 2*C(m,3) explains
the X3/A53 slack rows uniformly. NO regime-3 (6.7) want changed:
the R3A-R3E rows, battery reproductions, floors, triple-route,
teeth T-TOPPAIR/T-CHI/T-CVAL/T-PARITY and PARI rows were GREEN on
run 1. Corrections in this repair: P-C34/35/36 wants, CFORM,
T-M5SUM (4 -> 3 kills + P35 blind), NEW tooth T-OLDLAW (3 kills).
"""
import hashlib, os, random, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
B1_MD5 = 'c98cb423ce3acecf65a6e6a02a979b2d'
with open(os.path.join(HERE, 'gentow6_box1_mu3.py'), 'rb') as fh:
    assert hashlib.md5(fh.read()).hexdigest() == B1_MD5, 'engine md5!'
import gentow6_box1_mu3 as B1

random.seed(20260810)
NCHK = NVIO = 0
KILLS = {}
def chk(tag, cond, msg):
    global NCHK, NVIO
    NCHK += 1
    if not cond:
        NVIO += 1
        print('VIOLATION [%s] %s' % (tag, msg))

def tooth(name, killed, msg):
    KILLS[name] = KILLS.get(name, 0) + (1 if killed else 0)
    chk('TEETH', killed, 'tooth %s NOT killed: %s' % (name, msg))

# ---------- fresh route F (own code, one terminal reduction) ---------
def f_pdiv(f, g):
    f = list(f)
    dg = len(g) - 1
    q = [0] * max(1, len(f) - dg)
    while f and f[-1] == 0:
        f.pop()
    while f and len(f) - 1 >= dg:
        d = len(f) - 1 - dg
        c = f[-1]
        q[d] = c
        for k in range(len(g)):
            f[d + k] -= c * g[k]
        while f and f[-1] == 0:
            f.pop()
    return q, f

def routeF(F, f):
    A, r = [], list(f)
    for _ in range(F.mu1 + 1):
        r, rem = f_pdiv(r, F.PHI1)
        A.append(rem)
    assert not [c for c in r if c]
    out = []
    for _ in range(F.mu2):
        q = [[] for _ in range(max(1, len(A) - F.m))]
        for i in range(len(A) - 1, F.m - 1, -1):
            c = A[i]
            if [x for x in c if x]:
                q[i - F.m] = B1.padd(q[i - F.m], c)
                A[i] = []
                for k in range(F.m):
                    A[i - F.m + k] = B1.padd(
                        A[i - F.m + k], B1.pneg(B1.pmul(c, F.K2[k])))
        out.append([f_pdiv(list(A[b]), F.PHI1)[1] for b in range(F.m)])
        A = q
    return out

# ---------- frames ----------------------------------------------------
FR = {}
FR['R3A'] = B1.Frame('R3A', 2, [-2, 0, 0, 1], 1, 3, 1, 2, 2, 4,
                     [4, 4, -4, -4, -2, 0, 1])
FR['R3B'] = B1.Frame('R3B', 3, [-3, 0, 0, 1], 1, 3, 1, 2, 2, 4,
                     [9, -9, 18, -6, 3, 0, 1])
FR['R3C'] = B1.Frame('R3C', 2, [-2, 0, 0, 0, 1], 1, 4, 1, 2, 2, 5,
                     [4, 4, -4, 0, -4, -2, 0, 0, 1])
FR['R3D'] = B1.Frame('R3D', 3, [-3, 0, 0, 0, 1], 1, 4, 1, 3, 2, 5,
                     [-27, -27, 27, -27, 27, 18, -9, 0, -9, -3, 0, 0, 1])
FR['R3E'] = B1.Frame('R3E', 3, [-3, 0, 0, 0, 1], 1, 4, 1, 3, 2, 5,
                     [-27, -27, 54, -54, 27, 18, -18, 0, -9, -3, 0, 0, 1])
FR['P33'] = B1.Frame('P33', 3, [-3, 0, 1], 1, 2, 2, 1, 3, 5,
                     [9, -18, -6, 0, 1])
FR['P34'] = B1.Frame('P34', 3, [-3, 0, 1], 1, 2, 2, 1, 4, 5,
                     [9, -18, -6, 0, 1])
FR['P35'] = B1.Frame('P35', 3, [-3, 0, 1], 1, 2, 2, 1, 5, 5,
                     [9, -18, -6, 0, 1])
FR['P36'] = B1.Frame('P36', 3, [-3, 0, 1], 1, 2, 2, 1, 6, 5,
                     [9, -18, -6, 0, 1])
FR['X3'] = B1.Frame('X3', 2, [-2, 0, 1], 1, 2, 2, 1, 3, 13,
                    [4, -64, -4, 0, 1])
FR['A53'] = B1.Frame('A53', 2, [-2, 0, 1], 1, 2, 2, 1, 3, 5,
                     [4, -4, -4, 0, 1])
assert [FR['R3A'].theta(j) for j in range(2)] == [17, 9]
assert [FR['R3B'].theta(j) for j in range(2)] == [17, 9]
assert [FR['R3C'].theta(j) for j in range(2)] == [21, 11]
assert [FR['R3D'].theta(j) for j in range(2)] == [31, 16]
assert [FR['R3E'].theta(j) for j in range(2)] == [31, 16]
assert [FR['X3'].theta(j) for j in range(3)] == [87, 61, 35]
assert [FR['A53'].theta(j) for j in range(3)] == [31, 21, 11]
assert FR['P36'].theta(3) == 31 and FR['P36'].theta(4) == 21

SH = {}
for name, F in FR.items():
    f = B1.ppow(F.PHI2, F.mu2)
    hon = F.honest(list(f))
    chk('DRAIN', all(not B1.pstrip(list(c)) for c in hon),
        '%s honest not DRAIN' % name)
    sR, sE, sF = F.shadow_R(list(f)), F.shadow_E(list(f)), routeF(F, f)
    for j in range(F.mu2):
        dR = F.slotdict(sR[j])
        chk('TRIPLE', dR == F.slotdict(sE[j]) == F.slotdict(sF[j]),
            '%s j%d route mismatch' % (name, j))
    SH[name] = sR

def slot(name, j):
    return FR[name].slotdict(SH[name][j])

def pin(name, j):
    return FR[name].pin(SH[name][j])

def grd(name, j, a, b, H):
    return FR[name].graded_nonzero(SH[name][j], a, b, H)

# ---------- regime-3 wants (theorem-facing + cascade displays) -------
WANT = [
    # (name, j, exact dict, pin, [(a,b,H,graded_bool)...])
    ('R3A', 1, {(0, 0): 16}, 12, [(0, 0, 9, False)]),
    ('R3A', 0, {(1, 1): 48, (2, 0): 64}, 17, [(1, 1, 17, True)]),
    ('R3B', 1, {(0, 0): 108}, 9, [(0, 0, 9, True)]),
    ('R3B', 0, {(2, 0): -1944}, 17, [(2, 0, 17, True)]),
    ('R3C', 0, {(0, 1): 16}, 21, [(0, 1, 21, True)]),
    ('R3C', 1, {}, None, []),
    ('R3D', 1, {(0, 0): 243}, 20, [(0, 0, 16, False)]),
    ('R3D', 0, {(1, 2): 1215, (2, 1): 2916, (3, 0): 6561}, 31,
     [(1, 2, 31, True), (2, 1, 31, True)]),
    ('R3E', 1, {(0, 0): 648}, 16, [(0, 0, 16, True)]),
    ('R3E', 0, {(2, 1): 14580, (1, 2): 3888, (3, 0): 34992}, 31,
     [(2, 1, 31, True), (1, 2, 31, True), (3, 0, 31, True)]),
    # committed 6.5-battery reproductions
    ('X3', 0, {(1, 1): 524288}, 91, []),
    ('X3', 1, {(0, 1): 12288}, 61, []),
    ('X3', 2, {}, None, []),
    ('A53', 0, {(1, 1): 128}, 35, []),
    ('A53', 1, {(0, 1): 48}, 21, []),
    ('A53', 2, {}, None, []),
    ('P33', 0, {(1, 1): 11664}, 31, []),
    ('P33', 1, {(0, 1): 972}, 25, []),
    ('P33', 2, {}, None, []),
    # corollary full-dict rows
    ('P36', 4, {(0, 1): 4860}, 25, [(0, 1, 21, False)]),
    ('P36', 5, {}, None, []),
]
for name, j, d, pw, greads in WANT:
    chk('SLOT', slot(name, j) == d,
        '%s ShC_%d = %s want %s' % (name, j, slot(name, j), d))
    chk('PIN', pin(name, j) == pw,
        '%s pin_%d = %s want %s' % (name, j, pin(name, j), pw))
    for a, b, H, gw in greads:
        chk('GRADED', grd(name, j, a, b, H) == gw,
            '%s j%d (%d,%d)@%d graded want %s' % (name, j, a, b, H, gw))

# corollary slot-scoped rows [wants corrected to 6.7C', see the
# RUN-1 RED DISCLOSURE in the docstring]
c34 = slot('P34', 1)
chk('C34', c34.get((1, 1)) == 46656 and pin('P34', 1) == 31
    and grd('P34', 1, 1, 1, 31), 'P34 j1 %s pin %s' % (c34, pin('P34', 1)))
print('RECORD P34 ShC_1 full: %s' % c34)
c35 = slot('P35', 2)
chk('C35', c35.get((1, 1)) == 116640 and pin('P35', 2) == 31
    and grd('P35', 2, 1, 1, 31), 'P35 j2 %s pin %s' % (c35, pin('P35', 2)))
print('RECORD P35 ShC_2 full: %s' % c35)
c36 = slot('P36', 3)
chk('C36', c36.get((1, 1)) == 233280 and pin('P36', 3) == 31
    and grd('P36', 3, 1, 1, 31), 'P36 j3 %s pin %s' % (c36, pin('P36', 3)))
print('RECORD P36 ShC_3 full: %s' % c36)
# the closed form ties (6.7C': 2*C(m,3)*chat^3*pi^{3a0})
chk('CFORM', slot('X3', 0).get((1, 1)) == 2 * 2**18
    and slot('A53', 0).get((1, 1)) == 2 * 2**6
    and slot('P33', 0).get((1, 1)) == 2 * 8 * 729
    and c34.get((1, 1)) == 2 * 4 * 8 * 729
    and c35.get((1, 1)) == 2 * 10 * 8 * 729
    and c36.get((1, 1)) == 2 * 20 * 8 * 729, 'closed-form ties')

# ---------- floors on perturbed members ------------------------------
GP_DISC = []
for name in ('R3A', 'R3B', 'R3C', 'R3D', 'R3E'):
    F = FR[name]
    for row, jp in enumerate((0, 1)):
        alpha = random.randrange(F.Dp)
        g = B1.pmul([F.p ** 45], [0] * alpha + [1])
        gk = list(g)
        for _ in range(jp):
            gk = B1.pmul(gk, F.PHI2)
        f = B1.padd(B1.ppow(F.PHI2, F.mu2), gk)
        hon = F.honest(list(f))
        chk('PERT', any(B1.pstrip(list(c)) for c in hon),
            '%s pert%d honest DRAIN' % (name, row))
        sR, sE = F.shadow_R(list(f)), F.shadow_E(list(f))
        for j in range(F.mu2):
            chk('PDUAL', F.slotdict(sR[j]) == F.slotdict(sE[j]),
                '%s pert%d j%d' % (name, row, j))
            md = F.mindiff(hon[j], sR[j])
            chk('FLOOR', md is None or md >= F.theta(j),
                '%s pert%d mindiff_%d = %s < %d'
                % (name, row, j, md, F.theta(j)))
        if jp == 0 and name in ('R3B', 'R3C', 'R3E'):
            GP_DISC.append((name, f))
# floors on the self-shadows too
for name, F in FR.items():
    for j in range(F.mu2):
        pj = pin(name, j)
        chk('FLOOR', pj is None or pj >= F.theta(j),
            '%s self pin_%d = %s' % (name, j, pj))

# ---------- teeth -----------------------------------------------------
tooth('T-TOPPAIR', pin('R3A', 1) != FR['R3A'].theta(1), 'R3A')
tooth('T-TOPPAIR', pin('R3C', 1) != FR['R3C'].theta(1), 'R3C')
tooth('T-TOPPAIR', pin('R3D', 1) != FR['R3D'].theta(1), 'R3D')
tooth('T-CHI', grd('R3A', 1, 0, 0, 9) is False, 'R3A')
tooth('T-CHI', grd('R3D', 1, 0, 0, 16) is False, 'R3D')
tooth('T-CHI', grd('R3E', 1, 0, 0, 16) is True, 'R3E')
tooth('T-CVAL', B1.vp(slot('R3B', 1)[(0, 0)], 3) != 2, 'R3B')
tooth('T-CVAL', B1.vp(slot('R3C', 0)[(0, 1)], 2) != 3, 'R3C')
tooth('T-CVAL', B1.vp(slot('R3E', 1)[(0, 0)], 3) != 3, 'R3E')
tooth('T-M5SUM', slot('X3', 0).get((1, 1)) != 4 * 2**18, 'X3')
tooth('T-M5SUM', c34.get((1, 1)) != 10 * 5832, 'P34')
tooth('T-M5SUM', c36.get((1, 1)) != 35 * 5832, 'P36')
# blind row disclosed: at P35 the sum mutant coincides (10+10 = 20)
tooth('T-OLDLAW', c34.get((1, 1)) != 2 * 5832, 'P34')
tooth('T-OLDLAW', c35.get((1, 1)) is not None, 'P35')
tooth('T-OLDLAW', c36.get((1, 1)) != -5 * 5832, 'P36')
tooth('T-PARITY', not grd('X3', 0, 1, 0, 87), 'X3')
tooth('T-PARITY', not grd('P34', 1, 1, 0, 31), 'P34')
tooth('T-PARITY', not grd('P36', 3, 1, 0, 31), 'P36')

# ---------- gp leg ----------------------------------------------------
def poly_str(f):
    return '+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f)
                    if c) or '0'
lines = ['default(parisizemax, 2000000000);',
         'sig(f,p)={my(fa=factor(f),out=List());'
         'for(i=1,matsize(fa)[1],my(g=fa[i,1]);'
         'if(poldegree(g)==1,listput(out,[1,1]),'
         'my(nf=nfinit([g,[p]]),dec=idealprimedec(nf,p));'
         'for(j=1,#dec,listput(out,[dec[j].e,dec[j].f]))));'
         'vecsort(Vec(out))}']
sig_want = {}
for name, want in (('R3A', [(3, 2)]), ('R3B', [(3, 2)]),
                   ('R3C', [(4, 2)]), ('R3D', [(4, 3)]),
                   ('R3E', [(4, 3)]), ('P36', [(4, 1)])):
    lines.append('print("SIG%s ", sig(%s, %d))'
                 % (name, poly_str(FR[name].PHI2), FR[name].p))
    sig_want['SIG' + name] = sorted(want)
for name, f in GP_DISC:
    lines.append('print("DISC%s ", poldisc(%s))' % (name, poly_str(f)))
out = subprocess.run(['gp', '-q', '-f'], input='\n'.join(lines) +
                     '\nquit\n', capture_output=True, text=True,
                     timeout=1800)
got = {}
for line in out.stdout.splitlines():
    parts = line.split(' ', 1)
    if len(parts) == 2:
        got[parts[0]] = parts[1].strip()
for tag, want in sig_want.items():
    gv = B1.sig_parse(got[tag]) if tag in got else None
    chk('GP', gv == want, 'gp %s: %s want %s' % (tag, gv, want))
for name, _ in GP_DISC:
    t = 'DISC' + name
    chk('GP', t in got and got[t].lstrip('-').isdigit()
        and int(got[t]) != 0, 'gp %s: %s' % (t, got.get(t)))

print('== SUMMARY == checks %d violations %d' % (NCHK, NVIO))
print('KILLS %s' % sorted(KILLS.items()))
ok = (KILLS.get('T-TOPPAIR', 0) == 3 and KILLS.get('T-CHI', 0) == 3
      and KILLS.get('T-CVAL', 0) == 3 and KILLS.get('T-M5SUM', 0) == 3
      and KILLS.get('T-OLDLAW', 0) == 3
      and KILLS.get('T-PARITY', 0) == 3)
print('VERDICT %s' % ('GREEN' if (NVIO == 0 and ok) else 'RED'))
