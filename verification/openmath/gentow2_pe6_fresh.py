#!/usr/bin/env python3
"""GENTOW2 passPE6 FRESH ROUTE (acceptance attempt, second count,
2026-08-10): THE w-DETECTING PROBE — the FIRST measurement anywhere of
the cross-frame unit w, the ONE object of the B″ complex never
computed ("not computed anywhere in the corpus" — GENTOW2 S5.1
re-scoped residue paragraph; "w_i = 1 IS OPEN" — GENTOW5 r2).

Route DISJOINT from all six prior contacts by OBJECT, not merely by
frame: every prior machine contact (battery, PE1 F-frames, PE2
f3 = 3, r2 probe, PE3 LV, PE4 LD + decode, PE5 GB/GA) measured
verdict-level data or the w-QUOTIENTED cocycle theta; none measured w.

WHAT IS MEASURED (the w-avatar).  w := R_{3,kbar}(nhat2(u3)),
kbar = u3/e(mu2) — per S5.1 [r3], "the coordinate of the one repo
ladder monomial nhat2(u3) in FGMN's canonical homogeneous frame
x3, p3, y3".  By FGMN Thm 4.2/eq (16) (layout L1028-1050; DESCRIPTIVE
status in the note, rider row 23) with s3(kbar) = 0 and eq (12)
u(kbar) = e(mu2)*kbar = u3, the normal form is H(nhat2(u3)) =
p3^{u3} * w with p3 = H(pi3), pi3 = the Def 3.12 level-3 uniformizer
pi3 = PHItilde2^{l2} pi2^{l'2} (mu3(pi3) = 1/e(mu2), Lemma 3.13(1) =
S6.1 row 20, CONSUMED).  Evaluating at a PHI3-root xi through the
C-m1-style bridge (v >= mu3 on polynomials at xi; denominator exact
and stable, v(pi3(xi)) = 1/e(mu2) — forced by GENTOW2-A(d)'s exact
value triples since pi3 is an x,pi,PHIP-monomial; measured below as
the PI3V rows) gives the w-AVATAR

    W := res( (nhat2(u3) / pi3^{u3})(xi) ),

a value-0 monomial in x, pi, PHIP — hence by the note's OWN S5.2
gamma-calculus a LETTER MONOMIAL z1^j z2^k with hand-derivable
integer exponents (exponent-lattice split against gamma1 = x^2/2 =
(2,-1,0) and gamma2 = PHIP^2/x^{u2} = (-u2,0,2) in (i,a,b) = exps of
(x, pi=2, PHIP)).  The probe measures W at every prime of four
committed frames on two towers and checks it against the
hand-derived letter monomial expressed in THE SAME PRIME's own letter
reads R1 := res(x^2/2), R2 := res(PHIP^2/x^{u2}).  Also measured, at
the f3 = 2 frames: U0 := res((nhat2(2*u3)/pi3^{2*u3})(xi)) — the
FIRST direct canonical-frame measurement of B′'s unit u(beta_0)
itself (all prior measurements were w-quotiented) — and THETA0 :=
res((nhat2(2*u3)/nhat2(u3)^2)(xi)) = theta(0), closing LEMMA
GENTOW2-B″'s identity (6) u(beta_0) = theta(0)*w^2 in the
w-INCLUSIVE frame for the first time.  (The IDY row is multiplicative
residue arithmetic — disclosed as consistency closure, not
independent physics; the physics rows are the three VALUE
measurements against hand exponents.)

TOWERS AND FRAMES (all committed objects; LP1 = the PE4 tower, GB =
the PE5 tower; pi2 = x on both (l1 = 1, l'1 = 0); pi3 = PHIP/x^{V2},
l2 = 1, l'2 = 0, h2 = 1 on both):
  LP1: PHIP = x^4+2x^2+4, PHI2 = PHIP^2-8x^3; e1 = 2, f1 = 2 (z1
       LIVE, z1^2+z1+1 = 0), e2 = 2, f2 = 1, z2 = 1; u2 = 9, w2 = 2,
       V2 = 4, e(mu2) = 4, pi3 = PHIP/x^4 (v = 9/4 - 2 = 1/4).
       gamma1 = x^2/2, gamma2 = PHIP^2/x^9.
    LD1: PHI3 = PHI2^2 - 2x^3*PHIP*PHI2 - 512x (e3 = 1, f3 = 2,
         u3 = 19, nhat2(19) = 4x*PHIP, nhat2(38) = 512x).
    LD3: PHI3 = PHI2^2 - 64x^2*PHIP (e3 = 2, f3 = 1, u3 = 37,
         nhat2(37) = 128*PHIP).
  GB:  PHIP = x^2-2, PHI2 = PHIP^4-4x*PHIP^2-32; e1 = 2, f1 = 1
       (z1 = 1), e2 = 2, f2 = 2 (z2 = eta2 LIVE, z2^2+z2+1 = 0);
       u2 = 5, w2 = 1, V2 = 2, e(mu2) = 4, pi3 = PHIP/x^2
       (v = 5/4 - 1 = 1/4).  gamma1 = x^2/2, gamma2 = PHIP^2/x^5.
    GA1: PHI3 = PHI2^2 - 16*PHIP*PHI2 - 256*PHIP^2 (e3 = 1, f3 = 2,
         u3 = 21, nhat2(21) = 16*PHIP, nhat2(42) = 1024x).
    GA3: PHI3 = PHI2^4 - 512*PHIP*PHI2^2 - 262144*PHIP^2 (e3 = 2,
         f3 = 2, u3 = 41, nhat2(41) = 512*PHIP, nhat2(82) = 2^20*x).

PREREGISTERED PREDICTIONS (hand-derived exponent-lattice splits;
sealed before the first run; python3 -m py_compile only, no smoke
run).  Lattice notation: ratio exponents (i, a, b) = j*gamma1 +
k*gamma2, W = z1^j z2^k.

  LD1: W-ratio nhat2(19)/pi3^19 = 4x^77/PHIP^18, (77,2,-18) =
       -2*g1 - 9*g2  ->  W = z1^{-2}z2^{-9} = z1^{-2} = z1
       (z2 = 1, z1^3 = 1):  W == R1, W != 1, W != R1^2.
       THETA0-ratio 512x/(4x*PHIP)^2 = 32/(x*PHIP^2), (-1,5,-2) =
       -5*g1 - 1*g2 -> z1^{-5} = z1:  THETA0 == R1  (= the PE4
       decode pin theta(0) = z1, independent remeasurement).
       U0-ratio 512x*x^152/PHIP^38 = 512x^153/PHIP^38, (153,9,-38)
       = -9*g1 - 19*g2 -> z1^{-9} = 1:  U0 == 1.
       IDY: U0 == THETA0 * W^2  (B″(6) at t = 0: 1 = z1*z1^2 ✓).
       B-route anchors: NPR 1; EF (4,4); VALS (x,PHIP,PHI2) =
       (2,9,19); PI3V val(pi3) = 1; R1PAT R1^2+R1+1 == 0, R1 != 1;
       R2PAT R2 == 1.
  LD3: W-ratio 128*PHIP*x^148/PHIP^37 = 128x^148/PHIP^36,
       (148,7,-36) = -7*g1 - 18*g2 -> z1^{-7} = z1^2:
       W == R1^2, W != 1, W != R1.   << with LD1: same tower,
       different u3 -> DIFFERENT w (kills "w constant per tower").
       f3 = 1: single slot, theta(0) = 1 trivially; no U0/IDY rows.
       Anchors: NPR 1; EF (8,2); VALS (4,18,37); PI3V 2; R1PAT;
       R2PAT R2 == 1.
  GA1: W-ratio 16*PHIP*x^42/PHIP^21 = 16x^42/PHIP^20, (42,4,-20) =
       -4*g1 - 10*g2 -> z2^{-10} = z2^{-1} = z2^2 (z1 = 1, z2^3 =
       1):  W == R2^2, W != 1, W != R2.
       THETA0-ratio 1024x/(16*PHIP)^2 = 4x/PHIP^2, (1,2,-2) =
       -2*g1 - 1*g2 -> z2^{-1} = z2^2:  THETA0 == R2^2  (= PE5's
       COC pin, independent remeasurement).
       U0-ratio 1024x*x^84/PHIP^42 = 1024x^85/PHIP^42, (85,10,-42)
       = -10*g1 - 21*g2 -> z2^{-21} = 1:  U0 == 1.
       IDY: U0 == THETA0 * W^2  (1 = z2^2*z2^4 ✓).
       Anchors: NPR 2; EF (4,2) x2; VALS (2,5,21); PI3V 1; R1PAT
       R1 == 1; R2PAT R2^2+R2+1 == 0, R2 != 1.  All value rows at
       BOTH primes.
  GA3: W-ratio 512*PHIP*x^82/PHIP^41 = 512x^82/PHIP^40, (82,9,-40)
       = -9*g1 - 20*g2 -> z2^{-20} = z2:  W == R2, W != 1,
       W != R2^2.   << with GA1: same tower, different u3 ->
       DIFFERENT w; also the first e3 = 2 x f3 = 2 w-value.
       THETA0-ratio 2^20*x/(512*PHIP)^2 = 4x/PHIP^2 -> THETA0 ==
       R2^2 (same monomial as GA1 — grade-pair-determined).
       U0-ratio 2^20*x*x^164/PHIP^82 = 2^20*x^165/PHIP^82,
       (165,20,-82) = -20*g1 - 41*g2 -> z2^{-41} = z2^{-2} = z2:
       U0 == R2.
       IDY: U0 == THETA0 * W^2  (z2 = z2^2*z2^2 = z2^4 ✓).
       Anchors: NPR 2; EF (8,2) x2; VALS (4,10,41); PI3V 2; R1PAT
       R1 == 1; R2PAT live.  Both primes.

A-route (own exact integer/rational arithmetic in this file):
  RATIO0: each measured ratio is value-0 in exact Fractions
    (v = i*lam1 + a + b*(w2+lam2) == 0), per frame.
  LATTICE: the integer split (i,a,b) = j*g1 + k*g2 solved and
    checked to equal the docstring (j,k) literally, per ratio.
  RES: v2(Res(PHI3, g)) by Sylvester/fraction-free Bareiss, PHI3
    built by own poly arithmetic from the displayed formulas:
    LD1 (x, PHIP, PHI2) -> (8, 36, 76); LD3 -> (8, 36, 74);
    GA1 -> (8, 20, 84); GA3 -> (16, 40, 164)  [= 16 or 32 times
    the exact GENTOW2-A(d) values 1/2, 9/4|5/4, 19/4|37/8|21/4|41/8
    — the A-route leg pinning the exact values the avatar bridge
    consumes; agree with the committed PE4/PE5 pins].

B-route: PARI/gp nfinit([PHI3,[2]]) + idealprimedec + nfeltval +
nfmodpr; all elements value-0 at the measured prime.  The PI3V rows
are the FIRST direct machine pins of Lemma 3.13(1)'s stable value
v(pi3(xi)) = 1/e(mu2) at PHI3-roots (scaled: e(P)/4).

TEETH (what a wrong theory would do): w == 1 everywhere (the
per-height-friendly world) fails every W row; "w depends only on
the tower" fails the LD1-vs-LD3 and GA1-vs-GA3 pairs; the
wrong-sign alternative w = z^{+|j|} fails the three-way
discrimination (W equals exactly one of {1, z, z^2} and the rows
pin WHICH); a wrong pi3 normalization (dropping the V2-shift,
pi3' = PHIP) fails RATIO0/LATTICE (value 3/2 resp 1/2 != 0) before
any residue is read.
"""

import subprocess, sys
from fractions import Fraction as Fr

# ---------- tiny integer poly kit (ascending coeff lists) ----------
def norm(p):
    while p and p[-1] == 0: p.pop()
    return p

def pmul(a, b):
    r = [0]*(len(a)+len(b)-1)
    for i, ca in enumerate(a):
        if ca:
            for j, cb in enumerate(b): r[i+j] += ca*cb
    return norm(r)

def padd(a, b):
    r = [0]*max(len(a), len(b))
    for i, c in enumerate(a): r[i] += c
    for i, c in enumerate(b): r[i] += c
    return norm(r)

def psub(a, b): return padd(a, [-c for c in b])

def pscal(c, a): return norm([c*x for x in a])

def xpow(n): return [0]*n + [1]

def v2(n):
    n = abs(n); k = 0
    while n % 2 == 0: n //= 2; k += 1
    return k

def sylvester_res(f, g):
    n, m = len(f)-1, len(g)-1
    N = n + m
    M = [[0]*N for _ in range(N)]
    for i in range(m):
        for j, c in enumerate(reversed(f)): M[i][i+j] = c
    for i in range(n):
        for j, c in enumerate(reversed(g)): M[m+i][i+j] = c
    # fraction-free Bareiss
    prev = 1
    for k in range(N-1):
        if M[k][k] == 0:
            piv = next((r for r in range(k+1, N) if M[r][k] != 0), None)
            if piv is None: return 0
            M[k], M[piv] = M[piv], M[k]
            for r in range(k+1, N):
                for c in range(N): M[r][c] = -M[r][c]
        for r in range(k+1, N):
            for c in range(k+1, N):
                M[r][c] = (M[r][c]*M[k][k] - M[r][k]*M[k][c]) // prev
            M[r][k] = 0
        prev = M[k][k]
    return M[N-1][N-1]

class T:
    def __init__(self): self.n = 0; self.bad = 0
    def chk(self, ok, msg):
        self.n += 1
        if not ok:
            self.bad += 1
            print('VIOLATION:', msg)
        else:
            print('  ok:', msg)

# ---------- tower data ----------
# (name, lam1, u2, w2lam2 = w2+lam2, gamma2 = (-u2, 0, 2))
TOWERS = {
    'LP1': dict(lam1=Fr(1,2), u2=9, wl=Fr(9,4)),
    'GB':  dict(lam1=Fr(1,2), u2=5, wl=Fr(5,4)),
}

def ratio_val(tw, i, a, b):
    d = TOWERS[tw]
    return i*d['lam1'] + a + b*d['wl']

def lattice_split(tw, i, a, b):
    # solve (i,a,b) = j*(2,-1,0) + k*(-u2,0,2); return (j,k) or None
    u2 = TOWERS[tw]['u2']
    if b % 2: return None
    k = b // 2
    j = -a
    if 2*j - u2*k != i: return None
    return (j, k)

# ratios: tag -> (tower, (i,a,b), predicted (j,k))
RATIOS = [
    ('LD1_W',  'LP1', (77, 2, -18),  (-2, -9)),
    ('LD1_T0', 'LP1', (-1, 5, -2),   (-5, -1)),
    ('LD1_U0', 'LP1', (153, 9, -38), (-9, -19)),
    ('LD3_W',  'LP1', (148, 7, -36), (-7, -18)),
    ('GA1_W',  'GB',  (42, 4, -20),  (-4, -10)),
    ('GA1_T0', 'GB',  (1, 2, -2),    (-2, -1)),
    ('GA1_U0', 'GB',  (85, 10, -42), (-10, -21)),
    ('GA3_W',  'GB',  (82, 9, -40),  (-9, -20)),
    ('GA3_T0', 'GB',  (1, 2, -2),    (-2, -1)),
    ('GA3_U0', 'GB',  (165, 20, -82), (-20, -41)),
]

def build_polys():
    # LP1
    PHIPa = [4, 0, 2, 0, 1]
    PHI2a = psub(pmul(PHIPa, PHIPa), pscal(8, xpow(3)))
    LD1 = psub(psub(pmul(PHI2a, PHI2a),
                    pmul(pscal(2, xpow(3)), pmul(PHIPa, PHI2a))),
               pscal(512, xpow(1)))
    LD3 = psub(pmul(PHI2a, PHI2a), pmul(pscal(64, xpow(2)), PHIPa))
    # GB
    PHIPb = [-2, 0, 1]
    P2 = pmul(PHIPb, PHIPb)
    PHI2b = psub(psub(pmul(P2, P2), pmul(pscal(4, xpow(1)), P2)), [32])
    GA1 = psub(psub(pmul(PHI2b, PHI2b), pscal(16, pmul(PHIPb, PHI2b))),
               pscal(256, pmul(PHIPb, PHIPb)))
    PHI2b2 = pmul(PHI2b, PHI2b)
    GA3 = psub(psub(pmul(PHI2b2, PHI2b2),
                    pscal(512, pmul(PHIPb, PHI2b2))),
               pscal(262144, pmul(PHIPb, PHIPb)))
    return PHIPa, PHI2a, LD1, LD3, PHIPb, PHI2b, GA1, GA3

RES_PRED = {
    'LD1': (8, 36, 76), 'LD3': (8, 36, 74),
    'GA1': (8, 20, 84), 'GA3': (16, 40, 164),
}

GP = r"""
default(parisize, 512000000);
probe(tag, F, PHIP, u2, V2, u3, NH, NH2, f3) = {
  my(K, prs, xF, PP, pi3num, R1, R2, W, T0, U0, np);
  K = nfinit([F, [2]]);
  prs = idealprimedec(K, 2);
  np = #prs;
  print(tag, " NPR ", np);
  xF = Mod(x, F); PP = Mod(PHIP, F);
  for(ii = 1, np,
    my(pr = prs[ii], e, f, vx, vp, v2f, vpi3, r1, r2, w, t0, u0);
    e = pr.e; f = pr.f;
    print(tag, " EF ", e, " ", f);
    vx = nfeltval(K, xF, pr); vp = nfeltval(K, PP, pr);
    v2f = nfeltval(K, Mod(PHI2v, F), pr);
    vpi3 = vp - V2*vx;
    print(tag, " VALS ", vx, " ", vp, " ", v2f);
    print(tag, " PI3V ", vpi3);
    r1 = nfmodpr(K, xF^2/2, pr);
    r2 = nfmodpr(K, PP^2/xF^u2, pr);
    print(tag, " R1PAT ", r1^2 + r1 + 1 == 0, " ", r1 == 1);
    print(tag, " R2PAT ", r2^2 + r2 + 1 == 0, " ", r2 == 1);
    w = nfmodpr(K, (NH / (PP/xF^V2)^u3), pr);
    print(tag, " W1 ", w == 1);
    print(tag, " WR1 ", w == r1, " ", w == r1^2);
    print(tag, " WR2 ", w == r2, " ", w == r2^2);
    if(f3 == 2,
      t0 = nfmodpr(K, NH2/NH^2, pr);
      u0 = nfmodpr(K, (NH2 / (PP/xF^V2)^(2*u3)), pr);
      print(tag, " T0R1 ", t0 == r1, " ", t0 == r2^2);
      print(tag, " U01 ", u0 == 1, " ", u0 == r2);
      print(tag, " IDY ", u0 == t0*w^2);
    );
  );
};
PHIP = x^4+2*x^2+4; PHI2v = PHIP^2-8*x^3;
F = PHI2v^2 - 2*x^3*PHIP*PHI2v - 512*x;
probe("LD1", F, PHIP, 9, 4, 19, 4*Mod(x,F)*Mod(PHIP,F), 512*Mod(x,F), 2);
F = PHI2v^2 - 64*x^2*PHIP;
probe("LD3", F, PHIP, 9, 4, 37, 128*Mod(PHIP,F), 0, 1);
PHIP = x^2-2; PHI2v = PHIP^4-4*x*PHIP^2-32;
F = PHI2v^2 - 16*PHIP*PHI2v - 256*PHIP^2;
probe("GA1", F, PHIP, 5, 2, 21, 16*Mod(PHIP,F), 1024*Mod(x,F), 2);
F = PHI2v^4 - 512*PHIP*PHI2v^2 - 262144*PHIP^2;
probe("GA3", F, PHIP, 5, 2, 41, 512*Mod(PHIP,F), 2^20*Mod(x,F), 2);
print("GPDONE");
"""

def main():
    t = T()
    # ---------- A-route ----------
    for tag, tw, iab, jk in RATIOS:
        t.chk(ratio_val(tw, *iab) == 0, '%s RATIO0 value-0 exact' % tag)
        t.chk(lattice_split(tw, *iab) == jk,
              '%s LATTICE split == %s' % (tag, (jk,)))
    PHIPa, PHI2a, LD1, LD3, PHIPb, PHI2b, GA1, GA3 = build_polys()
    t.chk(len(LD1)-1 == 16 and len(LD3)-1 == 16 and len(GA1)-1 == 16
          and len(GA3)-1 == 32, 'DEGS 16/16/16/32')
    for tag, F, gx, gp_, g2 in (('LD1', LD1, xpow(1), PHIPa, PHI2a),
                                ('LD3', LD3, xpow(1), PHIPa, PHI2a),
                                ('GA1', GA1, xpow(1), PHIPb, PHI2b),
                                ('GA3', GA3, xpow(1), PHIPb, PHI2b)):
        want = RES_PRED[tag]
        for g, w_, nm in ((gx, want[0], 'x'), (gp_, want[1], 'PHIP'),
                          (g2, want[2], 'PHI2')):
            r = sylvester_res(F, g)
            t.chk(r != 0 and v2(r) == w_,
                  '%s RES %s v2 = %d' % (tag, nm, w_))
    # ---------- B-route ----------
    out = subprocess.run(['gp', '-q'], input=GP, capture_output=True,
                         text=True, timeout=3600)
    lines = out.stdout.splitlines()
    if out.stderr.strip():
        print('gp stderr:', out.stderr.strip().splitlines()[-1])
    def has(s): return any(l.strip() == s for l in lines)
    def count(s): return sum(1 for l in lines if l.strip() == s)
    t.chk(has('GPDONE'), 'gp completed')
    t.chk(has('LD1 NPR 1') and has('LD3 NPR 1') and has('GA1 NPR 2')
          and has('GA3 NPR 2'), 'NPR 1/1/2/2')
    t.chk(has('LD1 EF 4 4'), 'LD1 EF (4,4)')
    t.chk(has('LD3 EF 8 2'), 'LD3 EF (8,2)')
    t.chk(count('GA1 EF 4 2') == 2, 'GA1 EF (4,2) x2')
    t.chk(count('GA3 EF 8 2') == 2, 'GA3 EF (8,2) x2')
    t.chk(has('LD1 VALS 2 9 19'), 'LD1 VALS (2,9,19)')
    t.chk(has('LD3 VALS 4 18 37'), 'LD3 VALS (4,18,37)')
    t.chk(count('GA1 VALS 2 5 21') == 2, 'GA1 VALS (2,5,21) x2')
    t.chk(count('GA3 VALS 4 10 41') == 2, 'GA3 VALS (4,10,41) x2')
    t.chk(has('LD1 PI3V 1'), 'LD1 v(pi3) = 1/4 exact (scaled 1)')
    t.chk(has('LD3 PI3V 2'), 'LD3 v(pi3) = 1/4 exact (scaled 2)')
    t.chk(count('GA1 PI3V 1') == 2, 'GA1 v(pi3) = 1/4 exact x2')
    t.chk(count('GA3 PI3V 2') == 2, 'GA3 v(pi3) = 1/4 exact x2')
    # letter patterns: "R1PAT <psi1root> <is1>", "R2PAT <psi2root> <is1>"
    t.chk(has('LD1 R1PAT 1 0') and has('LD3 R1PAT 1 0'),
          'LP1 z1 LIVE (psi1-root, != 1) both frames')
    t.chk(has('LD1 R2PAT 0 1') and has('LD3 R2PAT 0 1'),
          'LP1 z2 == 1 both frames (char-2: 1 is NOT a psi2-root)')
    t.chk(count('GA1 R1PAT 0 1') == 2 and count('GA3 R1PAT 0 1') == 2,
          'GB z1 == 1 all primes')
    t.chk(count('GA1 R2PAT 1 0') == 2 and count('GA3 R2PAT 1 0') == 2,
          'GB z2 LIVE (psi2-root, != 1) all primes')
    # THE w MEASUREMENTS
    t.chk(has('LD1 W1 0'), 'LD1 w != 1  << FIRST w MEASUREMENT')
    t.chk(has('LD1 WR1 1 0'), 'LD1 w == z1 (not z1^2)')
    t.chk(has('LD3 W1 0'), 'LD3 w != 1')
    t.chk(has('LD3 WR1 0 1'), 'LD3 w == z1^2 (not z1) << u3-dependence')
    t.chk(count('GA1 W1 0') == 2, 'GA1 w != 1 x2')
    t.chk(count('GA1 WR2 0 1') == 2, 'GA1 w == z2^2 (not z2) x2')
    t.chk(count('GA3 W1 0') == 2, 'GA3 w != 1 x2')
    t.chk(count('GA3 WR2 1 0') == 2,
          'GA3 w == z2 (not z2^2) x2 << u3-dependence, e3 = 2 frame')
    # THETA0 remeasurements + U0 canonical-frame firsts + identity (6)
    t.chk(has('LD1 T0R1 1 0'), 'LD1 theta(0) == z1 (decode pin re-met)')
    t.chk(has('LD1 U01 1 0'), 'LD1 u(beta_0) == 1 CANONICAL FRAME')
    t.chk(has('LD1 IDY 1'), 'LD1 B″(6): u0 = theta0*w^2 closed')
    t.chk(count('GA1 T0R1 0 1') == 2, 'GA1 theta(0) == z2^2 x2')
    t.chk(count('GA1 U01 1 0') == 2, 'GA1 u(beta_0) == 1 x2')
    t.chk(count('GA1 IDY 1') == 2, 'GA1 B″(6) closed x2')
    t.chk(count('GA3 T0R1 0 1') == 2, 'GA3 theta(0) == z2^2 x2')
    t.chk(count('GA3 U01 0 1') == 2, 'GA3 u(beta_0) == z2 x2 (!= 1:'
          ' the first letter-valued CANONICAL unit measured)')
    t.chk(count('GA3 IDY 1') == 2, 'GA3 B″(6) closed x2')
    print('== passPE6 FRESH-ROUTE VERDICT ==')
    print('checks: %d, violations: %d' % (t.n, t.bad))
    print('GENTOW2 passPE6 fresh route: %s'
          % ('GREEN' if t.bad == 0 else 'RED'))
    sys.exit(1 if t.bad else 0)

if __name__ == '__main__':
    main()
