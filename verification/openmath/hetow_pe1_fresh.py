#!/usr/bin/env python3
"""HETOW passPE1 FRESH ROUTE (hostile verifier instrument; disjoint from
the sealed battery hetow_checks.py).

The sealed battery runs BOTH cases at the frame Phi' = x^2 - p, where
eta = res(theta^2/pi) = 1: HETOW-1's varpi-twist layer eta^{-Q(k)} is
IDENTICALLY 1 there (machine-blind gauge).  This instrument works at an
eta != 1 frame and at an f1 = 2 frame, all exact, PARI-adjudicated on
two routes (route 1 factorpadic+idealprimedec; route 2 factor/Q +
idealprimedec), zero code shared with the program's readers.

FRAME X (eta != 1):  p = 3, Phi' = x^2 - 6 (e1=2, f1=1, h=1, D'=2,
  varpi = x, eta = res(theta^2/3) = 2).  Tower (e2,f2) = (1,2),
  u2 = 3 = kappa2 > D'h = 2, psi2 = Z^2+Z+2 irreducible over F3
  (c1 = -1, c0 = -2 in psi2 = Z^2 - c1 Z - c0).  mu2 = 3, n = 12,
  D'' = 4, T2 = 6, K2 = F9.  dv2(x,pi,Phi') = (1,2,3).
FL1 (display seam): Phi2_naive (plain lifts c1h=-1, c0h=-2 in the
  GENHN/HETOW display) vs Phi2_coh (wrap-corrected c0' = c0*eta, from
  E(t) = [(f2-t)i(u2)+... ]/e1 cocycle count).  Predictions:
  sig(Phi2_coh) = {(2,2)} (genuine composed carrier), sig(Phi2_naive)
  != {(2,2)} ((T2_2) fails at face value; probed {(4,1)}).
FL2 (HETOW-1 at eta != 1, exact): the two definitions of r-tilde --
  (i) varpi-residues of Phi2_coh's exact-height slot parts, (ii) the
  minimal polynomial of beta = eta^{-Q(u2)} eta2 -- must coincide
  (predict Z^2+2Z+2 != psi2); and for Phi2_naive the killed polynomial
  of beta must be DEGENERATE ((Z+1)^2, beta in F3) -- the seam.
FL3 (sigma menu at eta != 1, n = 12, mu2 = 3): members
  f = Phi2_coh^3 + A2 Phi2^2 + A1 Phi2 + A0, monomial pins; every PARI
  sigma must lie in the case-B menu {(6,2)},{(2,6)},{(2,2)}^3,
  {(2,4),(2,2)},{(4,2),(2,2)}; forced rows (3RAM -> {(6,2)},
  2+1 -> {(4,2),(2,2)}) must match exactly.  NAIVE-KEY rows (same pins
  on Phi2_naive) reported (informative): expected to leave the menu.
FRAME Y (f1 = 2):  p = 3, Phi' = x^4 + 9 (e1=2, f1=2, h=1, D'=4,
  eta^2 = -1, K = F9).  Tower (e2,f2) = (2,1), u2 = 11 (kappa2 = 11/2
  > 4), psi2 = Z - eta, B = x^3 pi^4 (canonical lift, res = eta).
  Phi2 = Phi'^2 - 81x^3, D'' = 8, T2 = 22, dv2(x,pi,Phi') = (2,4,11).
FL4: sig(Phi2) = {(4,2)} (first f1 >= 2 composed-carrier machine
  contact); {(12,2)}-member f = Phi2^3 + 3^14 Phi' (lam2 = 67/3); and
  integer-slope members: sigma in the f1=2 menu {(12,2)},{(4,6)},
  {(4,2)}^3,{(4,4),(4,2)},{(8,2),(4,2)}.
VERDICT: GREEN iff 0 violations on scored checks.
"""
import json, subprocess, time

P = 3

# ---------------------------------------------------- tiny exact Z[x]
def padd(a, b):
    n = max(len(a), len(b)); out = [0]*n
    for i, c in enumerate(a): out[i] += c
    for i, c in enumerate(b): out[i] += c
    while out and out[-1] == 0: out.pop()
    return out

def pscal(k, a): return [k*c for c in a] if k else []

def pmul(a, b):
    if not a or not b: return []
    out = [0]*(len(a)+len(b)-1)
    for i, c in enumerate(a):
        for j, d in enumerate(b): out[i+j] += c*d
    while out and out[-1] == 0: out.pop()
    return out

def ppow(a, k):
    out = [1]
    for _ in range(k): out = pmul(out, a)
    return out

def pdivmod(a, b):
    # b monic
    a = list(a); q = []
    while len(a) >= len(b) and a:
        c = a[-1]; d = len(a)-len(b)
        q = padd(q, [0]*d + [c])
        a = padd(a, pscal(-c, [0]*d + b))
    return q, a

def polystr(f):
    return '+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f) if c) or '0'

# ------------------------------------------------------- F9 = F3[Z]/(psi2)
PSI2 = (2, 1)   # Z^2 + 1*Z + 2 : Z^2 = -Z - 2 = 2Z + 1
def f9mul(a, b):
    c0 = a[0]*b[0]; c1 = a[0]*b[1] + a[1]*b[0]; c2 = a[1]*b[1]
    return ((c0 + 1*c2) % 3, (c1 + 2*c2) % 3)   # Z^2 -> 2Z+1
def f9pow(a, k):
    out = (1, 0)
    for _ in range(k): out = f9mul(out, a)
    return out
F9INV = {}
for x0 in range(3):
    for x1 in range(3):
        if (x0, x1) != (0, 0):
            for y0 in range(3):
                for y1 in range(3):
                    if f9mul((x0, x1), (y0, y1)) == (1, 0):
                        F9INV[(x0, x1)] = (y0, y1)

# --------------------------------------- frame X objects and residues
PHIP = [-6, 0, 1]                       # x^2 - 6
def v3(n):
    if n == 0: return 10**9
    k = 0
    while n % 3 == 0: n //= 3; k += 1
    return k

def slot_res_varpi(c, k):
    """varpi-read residue of level-1 coefficient c (deg < 2) at height k,
    on the frame-X node locus: monomial x^i 3^g (2g + i = k) has
    res(x^i 3^g / x^k) = res((3/x^2)^g) = eta^{-g}, eta = 2.
    Returns element of F3 (K = F3 at f1 = 1), or None if dv(c) != k."""
    r, seen = 0, False
    for i, ci in enumerate(c):
        if ci == 0: continue
        h = 2*v3(ci) + i
        if h < k: return None
        if h == k:
            seen = True
            g = v3(ci)
            u = ci // 3**g
            r = (r + u * pow(2, (-g) % 2, 3)) % 3   # eta=2, eta^{-g}
    return r if seen else 0

def phi2_pair():
    """(Phi2_naive, Phi2_coh) per the display vs wrap-corrected lifts.
    psi2 = Z^2 - c1 Z - c0, c1 = -1, c0 = -2; n(3) = 3x, n(6) = 27.
    coherent: c0' = c0*eta = -4 -> lift -1 (== 2 mod 3... use -4 itself),
    c1' = c1 (E(1)-E(2) = 0 twist sits on t=0 here: E=(0,1,1))."""
    n3 = [0, 3]; n6 = [27]
    naive = padd(ppow(PHIP, 2),
                 padd(pscal(-1, pmul(pscal(-1, n3), PHIP)), pscal(-1, pscal(-2, n6))))
    coh = padd(ppow(PHIP, 2),
               padd(pscal(-1, pmul(pscal(-1, n3), PHIP)), pscal(-1, pscal(-4, n6))))
    return naive, coh

def killed_poly(phi2):
    """beta-killed polynomial from Phi2's slot varpi-residues:
    Z^2 + r1 Z + r0 (F3 coefficients), heights (3, 6) at slots (1, 0)."""
    q1, c0 = pdivmod(phi2, PHIP)
    q2, c1 = pdivmod(q1, PHIP)
    assert q2 == [1], q2
    r1 = slot_res_varpi(c1, 3)
    r0 = slot_res_varpi(c0, 6)
    return r1, r0

def minpoly_beta():
    """min poly of beta = eta^{-Q(3)} eta2 = 2*eta2 over F3, eta2 root of
    psi2: brute force in F9."""
    beta = (0, 2)                       # 2*eta2  (eta2 = (0,1)) [PE1 fix:
    # the drafted line f9mul((0,2),(0,1)) computed 2*eta2^2, not 2*eta2]
    b2 = f9mul(beta, beta)
    for r1 in range(3):
        for r0 in range(3):
            s = ((b2[0] + r1*beta[0] + r0) % 3, (b2[1] + r1*beta[1]) % 3)
            if s == (0, 0):
                return r1, r0
    return None

# ------------------------------------------------------------- oracle
GP_HDR = r"""
default(parisize, "2000M");  \\ PE1 fix: deg-24 FL4 jobs overflow the 8M default
ef(g, p) = { if (poldegree(g) == 1, return([1, 1]));
  my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
  [dec[1].e, dec[1].f] }
sig(f, p) = { my(F = factorpadic(f, p, 400));
  vecsort(vector(matsize(F)[1], i, ef(liftall(F[i, 1]), p))) }
sigq(f, p) = { my(fa = factor(f), out = List());
  for (i = 1, matsize(fa)[1], my(g = fa[i, 1]);
    if (poldegree(g) == 1, listput(out, [1, 1]),
        my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
        for (j = 1, #dec, listput(out, [dec[j].e, dec[j].f]))));
  vecsort(Vec(out)) }
"""

def gp_sigs(jobs):
    lines = [GP_HDR]
    for i, f in enumerate(jobs):
        ps = polystr(f)
        lines.append('print("R %d ", poldisc(Pol(%s)) != 0, " ", sig(%s, %d),'
                     ' " | ", sigq(%s, %d))' % (i, ps, ps, P, ps, P))
    lines.append('quit')
    out = subprocess.run(['gp', '-q', '-f'], input='\n'.join(lines),
                         capture_output=True, text=True, timeout=1800)
    got = {}
    for line in out.stdout.splitlines():
        if not line.startswith('R '): continue
        idx, rest = line[2:].split(' ', 1)
        dnz, rest = rest.split(' ', 1)
        r1txt, r2txt = rest.split('|')
        def prs(t):
            ns = [int(x) for x in t.replace('[',' ').replace(']',' ')
                  .replace(',',' ').split()]
            return tuple(sorted(zip(ns[0::2], ns[1::2])))
        got[int(idx)] = (dnz == '1', prs(r1txt), prs(r2txt))
    return got

VIOL = []
def check(leg, ok, detail):
    print('  %-28s %s  %s' % (leg, 'ok' if ok else '!! VIOLATION', detail))
    if not ok: VIOL.append((leg, str(detail)[:300]))

MENU_X = {((2,6),), ((6,2),), ((2,2),(2,2),(2,2)), ((2,2),(2,4)), ((2,2),(4,2))}
MENU_Y = {((12,2),), ((4,6),), ((4,2),(4,2),(4,2)), ((4,2),(4,4)), ((4,2),(8,2))}

def mono(a, g, b, phi):          # x^a * 3^g * Phi'^b  (as Z[x])
    return pmul([0]*a + [3**g], ppow(phi, b))

def main():
    t0 = time.time()
    print('HETOW passPE1 fresh route (eta != 1 + f1 = 2), p = %d' % P)
    naive, coh = phi2_pair()
    print('Phi2_naive =', polystr(naive)); print('Phi2_coh   =', polystr(coh))
    # FL2 exact residue algebra
    kn, kc = killed_poly(naive), killed_poly(coh)
    mp = minpoly_beta()
    print('killed(naive) Z^2+%dZ+%d   killed(coh) Z^2+%dZ+%d   minpoly(beta) Z^2+%dZ+%d'
          % (kn + kc + mp))
    check('FL2-rtilde-two-defs', kc == mp, 'slot-residues %s vs minpoly %s' % (kc, mp))
    check('FL2-rtilde-nontrivial-twist', mp == (2, 2) and mp != (1, 2),
          'r-tilde = Z^2+2Z+2 != psi2 = Z^2+Z+2 (the eta-twist is visible)')
    check('FL2-naive-degenerate', kn == (2, 1),
          'naive killed poly (Z+1)^2: beta rational, (T2_2) fails at face value')
    # FL1 + FL3 jobs
    jobs, tags, pred = [], [], []
    jobs.append(coh);   tags.append('FL1-coh');   pred.append({((2,2),)})
    jobs.append(naive); tags.append('FL1-naive'); pred.append('NOT-(2,2)')
    p3 = ppow(coh, 3); p2 = ppow(coh, 2)
    def member(key, A0, A1, A2):
        f = ppow(key, 3)
        f = padd(f, pmul(A2, ppow(key, 2)))
        f = padd(f, pmul(A1, key))
        return padd(f, A0)
    A0s21 = [pscal(c, mono(*rep, PHIP)) for c in (1, 2)
             for rep in ((1, 10, 0), (0, 9, 1))]
    A1s14 = [[], mono(0, 7, 0, PHIP), mono(1, 5, 1, PHIP),
             padd(mono(0, 7, 0, PHIP), pscal(2, mono(1, 5, 1, PHIP)))]
    A2s7 = [[], mono(1, 3, 0, PHIP), pscal(2, mono(0, 2, 1, PHIP))]
    for i0, A0 in enumerate(A0s21):
        for i1, A1 in enumerate(A1s14):
            for i2, A2 in enumerate(A2s7):
                if (i1 + i2) % 2 == (i0 % 2):   # thin the grid ~ half
                    jobs.append(member(coh, A0, A1, A2))
                    tags.append('FL3-ONE21'); pred.append(MENU_X)
    for c in (1, 2):
        for rep in ((0, 10, 0), (1, 8, 1)):
            jobs.append(member(coh, pscal(c, mono(*rep, PHIP)), [], []))
            tags.append('FL3-3RAM'); pred.append({((6,2),)})
    for c in (1, 2):
        for rep0, rep1 in (((0, 11, 0), (1, 7, 0)), ((1, 9, 1), (0, 6, 1))):
            jobs.append(member(coh, pscal(c, mono(*rep0, PHIP)),
                               mono(*rep1, PHIP), mono(1, 3, 0, PHIP)))
            tags.append('FL3-2+1'); pred.append({((2,2),(4,2))})
    for rep in ((1, 10, 0), (0, 9, 1)):
        jobs.append(member(naive, mono(*rep, PHIP), mono(0, 7, 0, PHIP),
                           mono(1, 3, 0, PHIP)))
        tags.append('FL3-NAIVEKEY'); pred.append('INFO')
    # FL4 (frame Y, f1 = 2, deg 24)
    PHIY = [9, 0, 0, 0, 1]
    PH2Y = padd(ppow(PHIY, 2), pscal(-1, mono(3, 4, 0, PHIY)))
    jobs.append(PH2Y); tags.append('FL4-key'); pred.append({((4,2),)})
    jobs.append(member(PH2Y, mono(0, 14, 1, PHIY), [], []))
    tags.append('FL4-12-2'); pred.append({((12,2),)})
    for c in (1, 2):
        for rep in ((1, 14, 1), (3, 13, 1)):
            jobs.append(member(PH2Y, pscal(c, mono(*rep, PHIY)), [], []))
            tags.append('FL4-int-slope'); pred.append(MENU_Y)
    jobs.append(member(PH2Y, mono(1, 14, 1, PHIY), mono(1, 11, 0, PHIY),
                       mono(0, 3, 1, PHIY)))
    tags.append('FL4-int-slope'); pred.append(MENU_Y)
    print('%d gp jobs (both routes on all) ...' % len(jobs))
    got = gp_sigs(jobs)
    census = {}
    for i, tag in enumerate(tags):
        if i not in got:
            check(tag, False, 'gp job %d missing' % i); continue
        dnz, s1, s2 = got[i]
        check(tag + '-routes-agree', s1 == s2, '%s vs %s' % (s1, s2))
        if not dnz:
            print('  %-28s DROPPED (disc = 0)' % tag); continue
        if pred[i] == 'INFO':
            print('  %-28s INFO sigma = %s  in-menu = %s'
                  % (tag, s1, s1 in MENU_X))
        elif pred[i] == 'NOT-(2,2)':
            check(tag, s1 != ((2, 2),), 'sigma = %s' % (s1,))
        else:
            check(tag, s1 in pred[i], 'sigma = %s' % (s1,))
        census[tag + ':' + str(s1)] = census.get(tag + ':' + str(s1), 0) + 1
    print('\ncensus:')
    for k in sorted(census): print('   %-52s %d' % (k, census[k]))
    print('\nTOTAL jobs %d violations %d (%.1fs)'
          % (len(jobs), len(VIOL), time.time() - t0))
    print('VERDICT: %s' % ('GREEN' if not VIOL else 'RED'))
    json.dump({'viol': VIOL, 'census': census, 'jobs': len(jobs)},
              open('hetow_pe1_fresh_results.json', 'w'), indent=1)

if __name__ == '__main__':
    main()
