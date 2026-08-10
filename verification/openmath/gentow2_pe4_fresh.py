#!/usr/bin/env python3
"""GENTOW2 passPE4 FRESH ROUTE (acceptance-attempt hostile verifier, 2026-08-09).

Route DISJOINT from all prior contacts: the sealed battery W1-W5/N1/N2,
PE1's F1-F3 (F4 x f3=2, letter-DEAD base), PE2's G1-G3 (f3=3,
letter-dead), the r2 probe LP1 and PE3's LV1/LV2 (letter-LIVE but
DEPTH-2 letter-formula probes only).  THIS is the first combination
LETTERS x DEPTH anywhere in the record: full depth-3 GENTOW2-A
witnesses on a letter-live tower (f1 = 2, z1 in F4\F2), with a
letter-valued K2-digit at f3 = 2 (LD1/LD2 pair, digit tooth) and the
first e3 >= 2 letter-live stage (LD3).  Also the FIRST machine contact
relevant to B-2 (u == 1) at letter-live grades: the honesty box
discloses the u == 1 record as letter-dead-only; LD1 vs LD2 differ by
one letter digit and flip irreducible <-> split, so a letter-grade
unit twist would strike here.

TOWER (the committed LP1 frame, r2 probe / note S10): p = 2, base key
x, lam1 = 1/2 (e1 = 2, h1 = 1); PHIP = x^4 + 2x^2 + 4 (psi1 = y^2+y+1,
f1 = 2, z1 = res(x0^2/2), z1^2 + z1 + 1 = 0, ord(z1) = 3); PHI2 =
PHIP^2 - 8x^3 (w2 = 2, lam2 = 1/4, e2 = 2, f2 = 1, e(mu2) = 4,
u2 = 9, l1 = 1, nhat(9) = 16x, nhat(18) = 512, nhat(19) = 512x;
eta2 = z1, z2 = 1 at LP1).  K2 = F3 = F4 with the LIVE level-1 letter
z1.  dv1 = 2v, dv2 = 4v; dv2(x) = 2, dv2(2) = 4, dv2(PHIP) = 9,
dv2(PHI2) = 18 = e2*f2*u2 (the depth-3 floor).

STAGE-3 FRAMES (kappa3 > 18 floor holds at each):
  LD1: e3 = 1, f3 = 2, kappa3 = 19 (lam3 = 1/4), u3 = 19.
       digits (c1, c0) = (z1, 1): k1 = zhat_{z1}*nhat2(19) =
       (x^2/2)*4x*PHIP = 2x^3*PHIP; k0 = nhat2(38) = 512x.
       PHI3 = PHI2^2 - 2x^3*PHIP*PHI2 - 512x.
       psi3 = y^2 + z1*y + 1, IRREDUCIBLE over F4 (y = z1*t gives
       t^2 + t + z1, Tr_{F4/F2}(z1) = 1 != 0).
  LD2: same stage data, digits (z1, z1^2): k0 = (x^2/2 + 1)*512x =
       256x^3 + 512x (z1^2 = z1 + 1).
       PHI3 = PHI2^2 - 2x^3*PHIP*PHI2 - 256x^3 - 512x.
       psi3 = y^2 + z1*y + z1^2 = (y+1)(y+z1^2): SPLIT, distinct roots.
  LD3: e3 = 2, f3 = 1, kappa3 = 37/2 (lam3 = 1/8), u3 = 37.
       digit c0 = z1: k0 = (x^2/2)*128*PHIP = 64x^2*PHIP.
       PHI3 = PHI2^2 - 64x^2*PHIP.  psi3 = y - z1.

PREREGISTERED PREDICTIONS (hand-derived; sealed before the first run;
no smoke run — python3 -m py_compile syntax check only, which executes
no check).

A-route (own exact integer arithmetic written in this file: polynomial
ops, PHIP/PHI2-adic expansions by monic division, formal ladder
heights, Sylvester-matrix resultants by fraction-free Bareiss):
  PHIP-adic expansions (hand-derived literals; x^6 = (x^2-2)PHIP + 8):
    LD1: a4=1, a3=-2x^3, a2=-16x^3+16x^2-32, a1=64x^2, a0=512-512x
    LD2: a4,a3,a2,a1 IDENTICAL to LD1; a0 = 512-512x-256x^3
    LD3: a4=1, a3=0, a2=-16x^3, a1=-128, a0=512
  dv1 pin heights (j=0..4) and shape — one-sided of repo slope
  kappa2 = 9/2 with s = 0, on-side support {0,4}, pins at j=1,2,3
  STRICTLY above (at j=2 this is the char-2 psi2-power signature:
  the middle coefficient of a square vanishes):
    LD1: (18, 14, 10, 5, 0)   LD2: (18, 14, 10, 5, 0)
    LD3: (18, 14, 11, None, 0)
  PHI2-adic expansions + dv2 ladder heights:
    LD1: A2=1, A1=-2x^3*PHIP, A0=-512x;   heights (38, 19, 0), all ON
         the side (0,38)-(2,0) of dv2-slope kappa3 = 19, full support
         {0,1,2} = supp(psi3)
    LD2: A2=1, A1 same, A0=-256x^3-512x;  heights (38, 19, 0)
    LD3: A2=1, A1=0,    A0=-64x^2*PHIP;   heights (37, None, 0),
         slope 37/2 half-odd-integral: e3 = 2 forced by the polygon
  v2(Res(PHI3, g)) exact certificates (= sum of v2 over the 16 roots;
  PHI3 monic):
    all frames: g=x: 8;  g=PHIP: 36;  g=PHI2: 76 (LD1, LD2) / 74 (LD3)
    LD1 constant-digit certificates at dv1-grade 18:
      g1 = a0-512           = -512x:               152 (per-height digit = 1)
      g2 = a0-(x^2/2+1)*256x^2 = 1024-512x-128PHIP: 148 (mult digit = z1^2)
      g3 = a0-512*(x^2/2)   = 512-512x-256x^2:     144 (per-height != z1)
      g4 = a0-512*(x^2/2+1) = -512x-256x^2:        144 (per-height != z1^2)
      g5 = a0-(x^2/2)*256x^2 = 1024-512x+256x^2-128PHIP: 144 (mult != z1)
    LD2: g1' = a0-512 = -256x^3-512x: 152 (two monomials at dv1 = 19,
      classes z1 + 1 = z1^2 != 0 — same numeric value as LD1's g1: the
      level-2 A-face of the tooth pair is IDENTICAL);
      g2' = a0-(x^2/2+1)*256x^2 = 1024-256x^3-512x-128PHIP: 148;
      g3' = a0-256x^2: 144;  g4' = a0-512*(x^2/2+1): 144
    LD3: g2 = a0-(x^2/2+1)*256x^2 = 1024-128PHIP: 148;
      g3 = 512-256x^2: 144;  g5 = a0-128x^4 = 1024+256x^2-128PHIP: 144
  THE LETTER-TWIST READING (clause (c) twist-aware, machine form): the
  constant digit is 1 in the per-height convention (z2-letter side,
  z2 = 1 here) and z1^2 in the multiplicative convention (eta2-letter
  side, eta2^2 = z1^2) — ratio z1^2 = (eta2/z2)^2 =
  (z1^floor(l1*u2/e1))^2 = (z1^4)^2 = z1^8 = z1^2, EXACTLY the S5.1
  LETTER FORMULA raised to ell3 = 2; certified by {152,148,144,144,144}
  above and by DPH/DMU on the B-route.

B-route (PARI/gp subprocess: factorpadic prec 80; factor(F) over Q,
then per rational factor nfinit([.,[2]]) + idealprimedec + nfeltval +
nfmodpr — per-PRIME predictions are unchanged however F factors /Q):
  LD1: NFAC 1 (deg 16); NQFAC 1; NPR 1; EF 4 4; VALS (x,PHIP,PHI2) =
       (2, 9, 19); R1OK (r1 = res(x0^2/2): r1^2+r1+1 = 0, r1 != 1);
       ETA2: res(PHIP^2/(16x)) == r1  [the (alpha)-consumption read:
       eta2(xi) is the repo-psi2 root, = z1];
       PSI3: r3 = res(PHI2/(4x*PHIP)) satisfies r3^2 + r1*r3 + 1 = 0
       [the level-3 slot read hits a psi3-root — letters x depth];
       DEEP: r3^4 != r3 [r3 generates F16 over F4: f3 = 2 live];
       DPH: res(a0/512) == 1;  DMU: res(a0/(256x^2)) == r1 + 1.
  LD2: NFAC 2 (degs [8, 8]); NQFAC 1; NPR 2; per prime: EF 4 2, VALS
       (2, 9, 19), R1OK, ETA2 == r1, PSI3: r3^2 + r1*r3 + r1^2 == 0;
       ROOT: the two primes read DISTINCT psi3-roots (one R1 = 1, one
       RW = z1^2 = r1+1; Thm-6.6-style prime <-> factor matching).
  LD3: NFAC 1; NQFAC 1; NPR 1; EF 8 2; VALS (4, 18, 37); R1OK;
       ETA2 == r1; PSI3 (e3 = 2 leg): res(PHI2^2/(128*PHIP)) == r1.

TOOTH LD1-vs-LD2 (the letter-digit tooth, first anywhere): identical
a3/a2/a1, identical pin tuples and polygon shapes at BOTH levels,
per-height constant digit 1 both — yet NFAC 1 vs 2: only the
letter-valued K2 digit (c0 = 1 vs z1^2) separates them, exactly
GENTOW2-A hypothesis (ii) + GENTOW2-B's digit grammar at a live
letter.  A unit twist u != 1 in B-2 at these grades would flip the
pair: green = the record's first letter-live u == 1 machine support.
"""

import subprocess, sys

def v2(n):
    n = abs(n); assert n != 0
    k = 0
    while n % 2 == 0: n //= 2; k += 1
    return k

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

def pneg(a): return [-c for c in a]

def gsub(a, b): return padd(a, pneg(b))

def pdivmod_monic(a, b):
    a = a[:]; q = [0]*max(1, len(a)-len(b)+1)
    while len(a) >= len(b):
        c = a[-1]; d = len(a)-len(b); q[d] = c
        for i, cb in enumerate(b): a[d+i] -= c*cb
        norm(a)
    return norm(q), norm(a)

def expand_adic(g, base):
    g = g[:]; out = []
    while g:
        g, r = pdivmod_monic(g, base)
        out.append(r)
    return out

def dv1(p):
    return None if not p else min(2*v2(c)+k for k, c in enumerate(p) if c)

def dv2lad(p, PHIP):
    if not p: return None
    b = expand_adic(p, PHIP); h = []
    for i, bi in enumerate(b):
        for k, c in enumerate(bi):
            if c: h.append(4*v2(c)+2*k+9*i)
    return min(h)

def sylv_res(a, b):
    n, m = len(a)-1, len(b)-1
    N = n+m
    M = [[0]*N for _ in range(N)]
    for i in range(m):
        for j, c in enumerate(a): M[i][i+n-j] = c
    for i in range(n):
        for j, c in enumerate(b): M[m+i][i+m-j] = c
    prev = 1
    for k in range(N-1):
        if M[k][k] == 0:
            sw = next((r for r in range(k+1, N) if M[r][k]), None)
            if sw is None: return 0
            M[k], M[sw] = M[sw], M[k]
        for i in range(k+1, N):
            for j in range(k+1, N):
                M[i][j] = (M[i][j]*M[k][k] - M[i][k]*M[k][j])//prev
            M[i][k] = 0
        prev = M[k][k]
    return M[N-1][N-1]

class G:
    def __init__(self): self.n = 0; self.bad = 0
    def chk(self, ok, msg):
        self.n += 1
        if not ok: self.bad += 1; print('VIOLATION:', msg)
    def say(self, s): print(s)

GP = r"""
default(parisize, 256000000);
frame(tag, F, PHIP, PHI2, A0, e3leg, ld1) = {
  my(fp, fq, npr, K, dec, pr, Fq, xF, r1, e2r, r3, dph, dmu);
  fp = factorpadic(F, 2, 80);
  print(tag, " NFAC ", matsize(fp)[1], " DEGS ", vector(matsize(fp)[1], i, poldegree(fp[i,1])));
  fq = factor(F)[,1]~;
  print(tag, " NQFAC ", #fq);
  npr = 0;
  for(qi = 1, #fq,
    Fq = fq[qi];
    K = nfinit([Fq, [2]]);
    dec = idealprimedec(K, 2);
    npr += #dec;
    for(i = 1, #dec,
      pr = dec[i];
      xF = Mod(x, Fq);
      print(tag, " EF ", pr.e, " ", pr.f);
      print(tag, " VALS ", nfeltval(K, xF, pr), " ", nfeltval(K, Mod(PHIP,Fq), pr), " ", nfeltval(K, Mod(PHI2,Fq), pr));
      r1 = nfmodpr(K, xF^2/2, pr);
      print(tag, " R1OK ", (r1^2 + r1 + 1 == 0) && (r1 != 1));
      e2r = nfmodpr(K, Mod(PHIP,Fq)^2/(16*xF), pr);
      print(tag, " ETA2 ", e2r == r1);
      if(e3leg == 1,
        r3 = nfmodpr(K, Mod(PHI2,Fq)^2/(128*Mod(PHIP,Fq)), pr);
        print(tag, " PSI3 ", r3 == r1),
        r3 = nfmodpr(K, Mod(PHI2,Fq)/(4*xF*Mod(PHIP,Fq)), pr);
        if(ld1 == 1,
          print(tag, " PSI3 ", r3^2 + r1*r3 + 1 == 0);
          print(tag, " DEEP ", r3^4 != r3);
          dph = nfmodpr(K, Mod(A0,Fq)/512, pr);
          dmu = nfmodpr(K, Mod(A0,Fq)/(256*xF^2), pr);
          print(tag, " DPH ", dph == 1);
          print(tag, " DMU ", dmu == r1 + 1),
          print(tag, " PSI3 ", r3^2 + r1*r3 + r1^2 == 0);
          print(tag, " ROOT ", if(r3 == 1, "R1", if(r3 == r1 + 1, "RW", "BAD")));
        );
      );
    );
  );
  print(tag, " NPR ", npr);
}
"""

def main():
    g = G()
    PHIP = [4, 0, 2, 0, 1]
    PHI2 = gsub(pmul(PHIP, PHIP), [0, 0, 0, 8])
    k1 = pmul([0, 0, 0, 2], PHIP)              # 2x^3*PHIP, digit z1 at dv2 = 19
    frames = {
        'LD1': gsub(gsub(pmul(PHI2, PHI2), pmul(k1, PHI2)), [0, 512]),
        'LD2': gsub(gsub(pmul(PHI2, PHI2), pmul(k1, PHI2)), [0, 512, 0, 256]),
        'LD3': gsub(pmul(PHI2, PHI2), pmul([0, 0, 64], PHIP)),
    }
    A1 = pneg(pmul([0, 0, 0, 2], PHIP))
    a0 = {'LD1': [512, -512], 'LD2': [512, -512, 0, -256], 'LD3': [512]}
    exp_a = {'LD1': [[512, -512], [0, 0, 64], [-32, 0, 16, -16], [0, 0, 0, -2], [1]],
             'LD2': [[512, -512, 0, -256], [0, 0, 64], [-32, 0, 16, -16], [0, 0, 0, -2], [1]],
             'LD3': [[512], [-128], [0, 0, 0, -16], [], [1]]}
    exp_pins1 = {'LD1': (18, 14, 10, 5, 0), 'LD2': (18, 14, 10, 5, 0),
                 'LD3': (18, 14, 11, None, 0)}
    exp_A = {'LD1': [pneg([0, 512]), A1, [1]],
             'LD2': [pneg([0, 512, 0, 256]), A1, [1]],
             'LD3': [pneg(pmul([0, 0, 64], PHIP)), [], [1]]}
    exp_pins2 = {'LD1': (38, 19, 0), 'LD2': (38, 19, 0), 'LD3': (37, None, 0)}
    x4 = [0, 0, 0, 0, 128]                     # 128x^4 = (x^2/2)*256x^2 lift product
    mzz = padd([0, 0, 256], x4)                # (x^2/2+1)*256x^2
    certs = {
        'LD1': [([0, 1], 8), (PHIP, 36), (PHI2, 76),
                (gsub(a0['LD1'], [512]), 152), (gsub(a0['LD1'], mzz), 148),
                (gsub(a0['LD1'], [0, 0, 256]), 144),
                (gsub(a0['LD1'], [512, 0, 256]), 144),
                (gsub(a0['LD1'], x4), 144)],
        'LD2': [([0, 1], 8), (PHIP, 36), (PHI2, 76),
                (gsub(a0['LD2'], [512]), 152), (gsub(a0['LD2'], mzz), 148),
                (gsub(a0['LD2'], [0, 0, 256]), 144),
                (gsub(a0['LD2'], [512, 0, 256]), 144)],
        'LD3': [([0, 1], 8), (PHIP, 36), (PHI2, 74),
                (gsub(a0['LD3'], mzz), 148),
                (gsub(a0['LD3'], [0, 0, 256]), 144),
                (gsub(a0['LD3'], x4), 144)],
    }

    for tag in ('LD1', 'LD2', 'LD3'):
        F = frames[tag]
        g.chk(len(F)-1 == 16, tag+' deg 16')
        aj = expand_adic(F, PHIP)
        g.chk(aj == exp_a[tag], tag+' PHIP-adic literals: got %s' % (aj,))
        pins = tuple(dv1(c) for c in aj)
        g.chk(pins == exp_pins1[tag], '%s dv1 pins %s' % (tag, pins))
        g.say('  %s dv1 pins %s' % (tag, pins))
        onside = all(p is None or 2*p >= 9*(4-j) for j, p in enumerate(pins))
        strict = all(pins[j] is None or 2*pins[j] > 9*(4-j) for j in (1, 2, 3))
        g.chk(onside and strict and pins[0] == 18 and pins[4] == 0,
              tag+' one-sided kappa2 = 9/2, s = 0, support {0,4}')
        Aj = expand_adic(F, PHI2)
        g.chk(Aj == exp_A[tag], tag+' PHI2-adic literals')
        pins2 = tuple(dv2lad(c, PHIP) for c in Aj)
        g.chk(pins2 == exp_pins2[tag], '%s dv2 pins %s' % (tag, pins2))
        g.say('  %s dv2 pins %s' % (tag, pins2))
        for gpoly, pred in certs[tag]:
            got = v2(sylv_res(F, list(gpoly)))
            g.chk(got == pred, '%s v2Res pred %s got %s' % (tag, pred, got))
            g.say('  %s v2 Res = %s (pred %s)' % (tag, got, pred))
    a1j = expand_adic(frames['LD1'], PHIP); a2j = expand_adic(frames['LD2'], PHIP)
    g.chk(a1j[1:] == a2j[1:] and dv1(a1j[0]) == dv1(a2j[0]) == 18,
          'TOOTH level-2 A-face LD1 == LD2 (only the letter digit differs)')

    gp_prog = GP
    for tag, e3leg, ld1 in (('LD1', 0, 1), ('LD2', 0, 0), ('LD3', 1, 0)):
        lit = lambda p: 'Pol(%s)' % list(reversed(p))
        gp_prog += 'frame("%s", %s, %s, %s, %s, %d, %d);\n' % (
            tag, lit(frames[tag]), lit(PHIP), lit(PHI2), lit(a0[tag]), e3leg, ld1)
    out = subprocess.run(['gp', '-q', '-f'], input=gp_prog, capture_output=True,
                         text=True, timeout=1200)
    lines = [l.strip() for l in out.stdout.splitlines() if l.strip()]
    g.say('-- gp output --')
    for l in lines: g.say('  ' + l)
    if out.stderr.strip(): g.say('gp stderr: ' + out.stderr.strip()[:800])
    has = lambda s: any(l == s for l in lines)
    count = lambda s: sum(1 for l in lines if l == s)
    g.chk(has('LD1 NFAC 1 DEGS [16]'), 'LD1 single deg-16 factor (psi3 irreducible /F4)')
    g.chk(has('LD2 NFAC 2 DEGS [8, 8]'), 'LD2 splits 8+8 (psi3 split /F4) — TOOTH FIRED')
    g.chk(has('LD3 NFAC 1 DEGS [16]'), 'LD3 single deg-16 factor')
    for t in ('LD1', 'LD2', 'LD3'): g.chk(has(t+' NQFAC 1'), t+' Q-irreducible')
    g.chk(has('LD1 NPR 1') and has('LD2 NPR 2') and has('LD3 NPR 1'), 'prime counts 1/2/1')
    g.chk(has('LD1 EF 4 4'), 'LD1 (e,f) = (4,4)')
    g.chk(count('LD2 EF 4 2') == 2, 'LD2 (e,f) = (4,2) x2')
    g.chk(has('LD3 EF 8 2'), 'LD3 (e,f) = (8,2)')
    g.chk(has('LD1 VALS 2 9 19'), 'LD1 nfeltval (2,9,19)')
    g.chk(count('LD2 VALS 2 9 19') == 2, 'LD2 nfeltval (2,9,19) x2')
    g.chk(has('LD3 VALS 4 18 37'), 'LD3 nfeltval (4,18,37)')
    g.chk(count('LD1 R1OK 1') == 1 and count('LD2 R1OK 1') == 2 and
          count('LD3 R1OK 1') == 1, 'z1 live in every residue field')
    g.chk(count('LD1 ETA2 1') == 1 and count('LD2 ETA2 1') == 2 and
          count('LD3 ETA2 1') == 1, 'eta2(xi) = z1: the psi2-root consumption read')
    g.chk(has('LD1 PSI3 1'), 'LD1 slot read is a psi3-root (letter coefficient)')
    g.chk(has('LD1 DEEP 1'), 'LD1 leaf letter generates F16 over F4 (f3 = 2 live)')
    g.chk(has('LD1 DPH 1'), 'LD1 per-height constant digit = 1 (z2-side)')
    g.chk(has('LD1 DMU 1'), 'LD1 mult constant digit = z1^2 (eta2-side twist)')
    g.chk(count('LD2 PSI3 1') == 2, 'LD2 slot reads are psi3-roots x2')
    g.chk(count('LD2 ROOT R1') == 1 and count('LD2 ROOT RW') == 1,
          'LD2 distinct psi3-roots {1, z1^2} across the two primes')
    g.chk(has('LD3 PSI3 1'), 'LD3 e3 = 2 slot read = z1')
    print('== passPE4 FRESH-ROUTE VERDICT ==')
    print('checks: %d, violations: %d' % (g.n, g.bad))
    print('GENTOW2 passPE4 fresh route: %s' % ('GREEN' if g.bad == 0 else 'RED'))
    return g.bad

if __name__ == '__main__':
    sys.exit(1 if main() else 0)
