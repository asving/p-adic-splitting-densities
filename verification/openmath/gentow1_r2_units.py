#!/usr/bin/env python3
"""GENTOW1 TOWERRAT-R2 supplement: machine legs for the three dated
corrections (R2a clip / R2b ONTO-by-cardinality / R2c three-band cap).

Charge (CODEX_TOWERRAT_2026-08-10.md S3 / S6 R2a-c), re-derived from the
note's own displays:

U-A (R2a, the clipped free-count):
  * Codex instance mu2=2, e1=f1=e2=1, f2=2, h=1, u2=2 (gcd(u2,e2)=1,
    node floor u2=2 > e2D'h=1): floors from the note's own (a) display
    = (9,7,5,3); at N=1 the sealed display gives -20 while the box mod
    pi has exactly 1 string (0 free digits) = the CLIPPED display's
    value Sum max(0, N-floor) = 0.
  * FAM-A5 floors [6,5,4,4 | 3,3,2,1] and FAM-B floors [7,6,5,5 |
    4,3,2,2] recomputed from the display formula == the committed S1
    budget tables; clip-inactive identity Sum(N-floor) ==
    Sum max(0,N-floor) at N = maxfloor and maxfloor+2 per family;
    the two displays DIFFER at N = 3 (clip active below max floor).

U-B (R2b, ONTO at a battery row): FAM-A5, the A5-R1 refine row
  (lam = 13, s = 1, what = -n2hat(13) = -4*Phi', Phi2+ = Phi2 - 4Phi'),
  window N = 4: DOM_4 (event slice: C0 = 64x pinned at height 26,
  C1 = 0 at heights <= 13, free digits above) has 16 members =
  2^(0+0+0+0 + 0+1+1+2) = |COD_4| (the lam-floored node box); the
  triangular map f -> Phi2+-digits sends all 16 into COD_4's window
  box, images DISTINCT and covering the box EXACTLY (onto verified by
  enumeration, not by cardinality alone).

U-C (R2c, the three bands at FAM-B; p=2, e2=1, f2=2, u2=3,
  Phi2 = Phi'^2-2xPhi'-8, dv2 = 2v, K2 = F4, N = 4, cap = e1e2*N = 8;
  lift family = 6 T-preserving window-4 lifts):
  * BAND 1 (below cap): C1 = 4Phi' (height 7 < 8): dv2(C1'(x0)) = 7
    for every lift, slot-arithmetic AND PARI (2*nfeltval == 7*pr.e).
  * BAND 2 (at cap): C1 = 4xPhi' (height 8 = cap, eta2-flavor):
    dv2 = 8 EXACT for every lift (PARI: 2*nfeltval == 8*pr.e) while
    the height-8 (0,0)-flavor digit DIFFERS between lifts 0 and
    2^4*Phi2 -- value exact, residue undetermined; 8 is NOT < cap:
    the sealed iff's only-if direction has a machine counter-instance.
  * BAND 3 (above cap): C1 = 2^5xPhi' (height 14 > 8): lift 0 reads 14,
    lift 2^4*x^3*Phi2 reads 11 -- value NOT stable (PARI both).

VERDICT: GREEN iff 0 violations.  (Supplement grade: predictions
derived in this docstring before the first full run; smoke = U-A only.)
"""
import subprocess, time

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
    a = list(a); q = []
    while len(a) >= len(b) and a:
        c = a[-1]; d = len(a)-len(b)
        q = padd(q, [0]*d + [c])
        a = padd(a, pscal(-c, [0]*d + b))
    return q, a

def polystr(f):
    return '+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f) if c) or '0'

def vp(n, p):
    if n == 0: return 10**9
    k = 0
    while n % p == 0: n //= p; k += 1
    return k

VIOL = []
def check(leg, ok, detail=''):
    print('  %-34s %s  %s' % (leg, 'ok' if ok else '!! VIOLATION', detail))
    if not ok: VIOL.append((leg, str(detail)[:300]))

def ceil_div(a, b): return -((-a)//b)

def floor_display(mu2, E2, e1e2, w, j):
    """the note's (a) display: ceil(((mu2-j)E2 - w)/e1e2) + [pin]."""
    t = (mu2 - j)*E2 - w
    pin = 1 if (t >= 0 and t % e1e2 == 0) else 0
    return ceil_div(t, e1e2) + pin

# ---------------------------------------------------------------- U-A
def unit_A():
    print('U-A (R2a): the clip')
    # Codex instance
    fl = [floor_display(2, 4, 1, w, j) for j in (0, 1) for w in (0, 2)]
    check('UA-codex-floors', fl == [9, 7, 5, 3], fl)
    N = 1
    unclipped = sum(N - f for f in fl)
    clipped = sum(max(0, N - f) for f in fl)
    nbox = 1  # every floor > 0 forces the zero digit; one string mod pi
    for f in fl: nbox *= 2**max(0, N - f)  # |K| irrelevant: exponent 0
    check('UA-codex-N1', (unclipped, clipped, nbox) == (-20, 0, 1),
          (unclipped, clipped, nbox))
    # battery rows: FAM-A5 (E2=10, e1e2=4, w = 2a+5b), FAM-B (E2=6,
    # e1e2=2, w = a+3b); committed S1 tables
    fam = {'A5': (10, 4, [0, 2, 5, 7], [6, 5, 4, 4, 3, 3, 2, 1]),
           'B':  (6, 2, [0, 1, 3, 4], [7, 6, 5, 5, 4, 3, 2, 2])}
    for name, (E2, e1e2, ws, table) in fam.items():
        fl = [floor_display(2, E2, e1e2, w, j) for j in (0, 1) for w in ws]
        check('UA-%s-floors' % name, fl == table, fl)
        mf = max(fl)
        for N in (mf, mf + 2):
            same = sum(N - f for f in fl) == sum(max(0, N - f) for f in fl)
            check('UA-%s-clip-inactive-N%d' % (name, N), same,
                  'sum = %d' % sum(max(0, N - f) for f in fl))
        N = 3
        check('UA-%s-clip-active-N3' % name,
              sum(N - f for f in fl) != sum(max(0, N - f) for f in fl),
              '%d vs %d' % (sum(N - f for f in fl),
                            sum(max(0, N - f) for f in fl)))

# ---------------------------------------------------------------- U-B
PHIP_A5 = [-2, 0, 1]                      # x^2 - 2
PHI2_A5 = padd(ppow(PHIP_A5, 2), pscal(-4, [0, 1]))     # Phi'^2 - 4x

def slots(C, phip):
    """[(v, a, b, coeff)] of C's composed-grid monomials (p = 2)."""
    out, b = [], 0
    while C:
        C, cb = pdivmod(C, phip)
        for a, c in enumerate(cb):
            if c: out.append((vp(c, 2), a, b, c))
        b += 1
    return out

def unit_B():
    print('U-B (R2b): ONTO at the A5-R1 row (lam = 13, N = 4)')
    N, H0, H1 = 4, 26, 13
    w = lambda a, b: 2*a + 5*b
    phi2p = padd(PHI2_A5, pscal(-4, PHIP_A5))            # Phi2 - 4Phi'
    free = [(1, 0, 3), (0, 1, 3), (1, 1, 2), (1, 1, 3)]  # (a, b, v), j = 1
    # counting formulas (identical floors both sides)
    flp = [max(0, ((H if H >= wv else -1) - wv)//4 + 1)
           for j, H in ((0, H0), (1, H1))
           for wv in (0, 2, 5, 7)]
    dom_exp = sum(max(0, N - f) for f in flp)
    check('UB-count-16', 2**dom_exp == 16, 'floors %s' % flp)
    images = set()
    for mask in range(16):
        C1 = []
        for bit, (a, b, v) in enumerate(free):
            if (mask >> bit) & 1:
                C1 = padd(C1, pmul([0]*a + [2**v], ppow(PHIP_A5, b)))
        f = padd(padd(ppow(PHI2_A5, 2), pmul(C1, PHI2_A5)),
                 pscal(64, [0, 1]))                      # + 64x
        q1, C0p = pdivmod(f, phi2p)
        q2, C1p = pdivmod(q1, phi2p)
        assert q2 == [1]
        vec = []
        for j, Cp, H in ((0, C0p, H0), (1, C1p, H1)):
            for (a, b) in ((0, 0), (1, 0), (0, 1), (1, 1)):
                coeff = 0
                for (vv, aa, bb, c) in slots(Cp, PHIP_A5):
                    if (aa, bb) == (a, b): coeff = c
                coeff %= 2**N
                for v in range(N):
                    if 4*v + w(a, b) <= H:               # killed zone
                        if (coeff >> v) & 1:
                            check('UB-kill-m%d' % mask, False,
                                  (j, a, b, v)); break
                    else:
                        vec.append((j, a, b, v, (coeff >> v) & 1))
        images.add(tuple(vec))
    check('UB-onto', len(images) == 16,
          '%d distinct window images of 16 = full box' % len(images))

# ---------------------------------------------------------------- U-C
PHIP_B = [-2, 0, 1]
PHI2_B = padd(padd(ppow(PHIP_B, 2), pscal(-2, pmul([0, 1], PHIP_B))),
              [-8])                                      # Phi'^2-2xPhi'-8

def lifts_B():
    """six T-preserving window-4 lifts (added to the member)."""
    yield 'L0', []
    yield 'LC1-1', pscal(16, PHI2_B)
    yield 'LC1-x', pscal(16, pmul([0, 1], PHI2_B))
    yield 'LC1-xF', pscal(16, pmul(pmul([0, 1], PHIP_B), PHI2_B))
    yield 'LC1-x3', pscal(16, pmul([0, 0, 0, 1], PHI2_B))
    yield 'LC0', [128]

def read_C1(g):
    q1, C0 = pdivmod(g, PHI2_B)
    q2, C1 = pdivmod(q1, PHI2_B)
    assert q2 == [1]
    return C1

def slotmin(C):
    wv = {(0, 0): 0, (1, 0): 1, (0, 1): 3, (1, 1): 4}
    return min(2*v + wv[(a, b)] for v, a, b, c in slots(C, PHIP_B))

def digit00_at8(C):
    for v, a, b, c in slots(C, PHIP_B):
        if (a, b) == (0, 0): return ((c % 32) >> 4) & 1
    return 0

def unit_C(jobs, tags, preds):
    print('U-C (R2c): the three bands at FAM-B (N = 4, cap = 8)')
    base = lambda C1: padd(padd(ppow(PHI2_B, 2), pmul(C1, PHI2_B)), [128])
    rows = (('BAND1', pscal(4, PHIP_B), 7),
            ('BAND2', pscal(4, pmul([0, 1], PHIP_B)), 8),
            ('BAND3', pscal(32, pmul([0, 1], PHIP_B)), 14))
    d8 = {}
    for band, C1, m in rows:
        for lname, lift in lifts_B():
            if band == 'BAND3' and lname not in ('L0', 'LC1-x3'): continue
            g = padd(base(C1), lift)
            C1p = read_C1(g)
            sm = slotmin(C1p)
            pred = m if band != 'BAND3' else (14 if lname == 'L0' else 11)
            check('UC-%s-%s-slotmin' % (band, lname), sm == pred,
                  'slot-min %d' % sm)
            jobs.append((g, C1p)); tags.append('UC-%s-%s' % (band, lname))
            preds.append(pred)
            if band == 'BAND2' and lname in ('L0', 'LC1-1'):
                d8[lname] = digit00_at8(C1p)
    check('UC-BAND2-residue-moves', d8.get('L0') != d8.get('LC1-1'),
          '(0,0)-flavor digit at height 8: %s' % d8)

GP_HDR = r"""
default(parisize, "2000M");
vals(f, c) = { my(fa = factor(f), out = List());
  for (i = 1, matsize(fa)[1], my(g = fa[i, 1]);
    my(nf = nfinit([g, [2]]), dec = idealprimedec(nf, 2));
    for (j = 1, #dec,
      listput(out, [dec[j].e, nfeltval(nf, Mod(c, g), dec[j])])));
  Vec(out) }
"""

def run_gp(jobs, tags, preds):
    lines = [GP_HDR]
    for i, (g, c) in enumerate(jobs):
        lines.append('print("R %d ", vals(Pol(%s), Pol(%s)))'
                     % (i, polystr(g), polystr(c)))
    lines.append('quit')
    out = subprocess.run(['gp', '-q', '-f'], input='\n'.join(lines),
                         capture_output=True, text=True, timeout=1200)
    got = {}
    for line in out.stdout.splitlines():
        if not line.startswith('R '): continue
        idx, rest = line[2:].split(' ', 1)
        ns = [int(x) for x in rest.replace('[', ' ').replace(']', ' ')
              .replace(',', ' ').split()]
        got[int(idx)] = list(zip(ns[0::2], ns[1::2]))
    for i, tag in enumerate(tags):
        if i not in got:
            check(tag + '-pari', False, 'gp row missing'); continue
        ok = all(2*val == preds[i]*e for e, val in got[i]) and got[i]
        check(tag + '-pari', ok, 'dv2 = %d at %s' % (preds[i], got[i]))

def main():
    t0 = time.time()
    print('GENTOW1 R2 supplement: U-A / U-B / U-C')
    unit_A(); unit_B()
    jobs, tags, preds = [], [], []
    unit_C(jobs, tags, preds)
    print('%d gp jobs ...' % len(jobs))
    run_gp(jobs, tags, preds)
    print('\nTOTAL violations %d (%.1fs)' % (len(VIOL), time.time() - t0))
    print('VERDICT: %s' % ('GREEN' if not VIOL else 'RED'))

if __name__ == '__main__':
    main()
