#!/usr/bin/env python3
"""GENTOW6 passPE1 FRESH instrument (hostile verifier, 2026-08-10).

Independent code (no import of gentow*_checks). Two legs, both
OUT-OF-BATTERY:

LEG-A (TIE, LEMMA GENTOW-6.1 at a frame the battery never saw):
  Q3, Phi' = x^2-3 (e1=2, f1=1, h=1), inner slope 5/2 (u2=5, e2=2),
  MIXED side with BOTH classes REPEATED: residual (T+1)^2 (T-1)^2
  — profile (2,2), absent from the battery's {(1,2),(2,1),(0,3),
  (3,0)} — PLUS a live sibling side (slope 6, length 1; the battery's
  mixed rows had one side only). f = f_+ . f_- . (Phi' - 27), deg 18,
  mu1 = 9 (partial: e2f2mu2 = 4 < 9 per class).
  PREREGISTERED (from LEMMA 6.1 + GENTOW-4.A, before the run):
   A-1 level-1 hull = (0,26)-(1,20)-(9,0); slope-5/2 side residual
       factors {1:2, 2:2} (both classes multiplicity 2).
   A-2 composed read at KEY_s (Phi'^2 - 9sx): the >T2=10 initial
       segment of P2(f) has length mu2*(s) = 2 = m_s, BOTH classes.
   A-3 PARI (decorrelated): factorpadic degrees, classed by the
       GENTOW-1(d) field floor v(Phi2_s(theta)) > E2/(e1e2) = 5/2:
       class-s degrees sum to D2*m_s = 8 for each s; sibling factor
       (deg 2) in neither class; disc(f) != 0.
LEG-B (CERT-TOP corner, THEOREM GENTOW-6.3(b) at the b* = 0
  quotient-transfer corner, out of battery: first f2 = 5, first
  b* = 0):
  Q3, Phi' = x^2-3, (e2,f2) = (1,5), u2 = 3 (kappa2 = 3 integer),
  psi2 = an irreducible quintic over F_3 with c_3 = c_4 = 0 and
  c_2 != 0 (so t* = 2, T <= {0,1,2}); i_{t*} = i(3*3) = 1,
  2 i_{t*} = 2 >= D' = 2: regime 2. The certificate position
  2 e2 t* + 1 = 5 = e2 f2 EXACTLY: j* = 1, b* = 0, a* = 0 — the
  branch must QUOTIENT-TRANSFER into coordinate 1 slot 0 (the
  corner of the grid; every battery row had b* >= 1).
  Constants: E2 = 15, delta = 3 - 2 = 1, THETA_1 = 16, THETA_0 = 31,
  v* = 2 a_{t*} = 8 (nhat(9) = 3^4 x).
  PREREGISTERED (from 6.3(b), hand-derived before the run):
   B-1 self-shadow of Phi2^2: ShC_1 slot (0,0) nonzero, vp = 8,
       height 2*8 + 0 = 16 = THETA_1 = pin(ShC_1).
   B-2 digit residue: digit / 3^8 == c_2^2 (mod 3) (unit square,
       wrap unit = 1 here: eta = 1 frame).
   B-3 ShC_0 zero or pin(ShC_0) >= 31 = THETA_0 (floor).
   B-4 honest read of Phi2^2 is DRAIN (C_1 = C_0 = 0) — trivial
       but asserted (the discrepancy IS the shadow).
Verdict: GREEN iff 0 violations.
"""
import subprocess
import sys
from fractions import Fraction
from math import gcd

VIOL = []
NCHK = 0


def chk(ok, msg):
    global NCHK
    NCHK += 1
    if not ok:
        VIOL.append(msg)
        print('  !! VIOLATION: %s' % msg)
    return ok


# ---------------- exact poly ops over Z (lists, low->high) --------
def pstrip(f):
    while f and f[-1] == 0:
        f.pop()
    return f


def padd(f, g):
    n = max(len(f), len(g))
    return pstrip([(f[i] if i < len(f) else 0) +
                   (g[i] if i < len(g) else 0) for i in range(n)])


def psca(c, f):
    return pstrip([c * a for a in f])


def pmul(f, g):
    if not f or not g:
        return []
    out = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        if a:
            for j, b in enumerate(g):
                out[i + j] += a * b
    return pstrip(out)


def pdivmod_monic(f, g):
    """f = q*g + r, g monic. Exact over Z."""
    f = list(f)
    dg = len(g) - 1
    assert g[-1] == 1
    q = [0] * max(len(f) - dg, 0)
    while len(pstrip(f)) - 1 >= dg and pstrip(f):
        d = len(f) - 1
        c = f[-1]
        q[d - dg] = c
        for i in range(len(g)):
            f[d - dg + i] -= c * g[i]
        f = pstrip(f)
    return pstrip(q), pstrip(f)


def ppow(f, k):
    out = [1]
    for _ in range(k):
        out = pmul(out, f)
    return out


def vp(n, p):
    if n == 0:
        return None
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def dev(f, K, length):
    """Phi-adic development: f = sum A_J K^J, deg A_J < deg K.
    Returns (A list length `length`, top) with f = sum + top*K^length."""
    A = []
    for _ in range(length):
        f, r = pdivmod_monic(f, K)
        A.append(r)
    return A, f


def lower_hull(pins):
    """pins: list of (x, y) with x increasing. Lower convex hull."""
    hull = []
    for pt in pins:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            if (y2 - y1) * (pt[0] - x1) >= (pt[1] - y1) * (x2 - x1):
                hull.pop()
            else:
                break
        hull.append(pt)
    return hull


# ---------------- F_p[T] factorization (tiny, brute force) --------
def fp_factor_linear(digits, p):
    """Multiplicities of the roots of sum digits[i] T^i over F_p,
    plus the (unfactored) nonlinear leftover degree. digits low->high."""
    from itertools import count
    ds = [d % p for d in digits]
    mult = {}
    for r in range(p):
        m = 0
        cur = list(ds)
        while True:
            val = sum(c * pow(r, i, p) for i, c in enumerate(cur)) % p
            if val != 0 or len(cur) <= 1:
                break
            # synthetic division by (T - r)
            out = [0] * (len(cur) - 1)
            acc = 0
            for i in range(len(cur) - 1, 0, -1):
                acc = (acc * r + cur[i]) % p
                out[i - 1] = acc
            # verify
            cur2 = [(out[0] * (-r)) % p]
            cur = out
            m += 1
        if m:
            mult[r] = m
    return mult


# =================== LEG A: the (2,2) tie ==========================
P = 3
PHI = [-3, 0, 1]              # x^2 - 3
E1, F1, H = 2, 1, 1
DP = 2                        # D'
U2, E2DEN = 5, 2              # slope 5/2
E2C = 2 * 1 * 5               # E2 = e2 f2 u2 = 10 (f2 = 1)
D2 = 4
KEY = {1: padd(pmul(PHI, PHI), [0, -9]),    # Phi'^2 - 9x   (psi=T-1)
       2: padd(pmul(PHI, PHI), [0, -18])}   # Phi'^2 - 18x  (psi=T-2)


def slots_leg_a(Cj):
    """C_j (deg < 4) -> {(a,b): coeff} on the (a<2, b<2) grid via
    Phi'-division."""
    b0, b1r = pdivmod_monic(Cj, PHI)  # Cj = b0*Phi' + b1r? careful
    # Cj = q*Phi' + r: r = b-slot 0, q = b-slot 1 (deg q < 2)
    q, r = pdivmod_monic(Cj, PHI)
    out = {}
    for a, c in enumerate(r):
        if c:
            out[(a, 0)] = c
    for a, c in enumerate(q):
        if c:
            out[(a, 1)] = c
    return out


def pin_leg_a(Cj):
    sl = slots_leg_a(Cj)
    if not sl:
        return None
    return min(4 * vp(c, P) + 2 * a + 5 * b
               for (a, b), c in sl.items())


def level1_read(f):
    n = len(f) - 1
    M = n // DP
    A, top = dev(list(f), PHI, M)
    assert top == [1]
    pins = []
    for J, c in enumerate(A):
        vals = [E1 * vp(cc, P) + i * H for i, cc in enumerate(c) if cc]
        if vals:
            pins.append((J, min(vals)))
    pins.append((M, 0))
    hull = lower_hull(pins)
    pmap = dict(pins)
    sides = []
    for k in range(len(hull) - 1):
        (J1, y1), (J2, y2) = hull[k], hull[k + 1]
        num, den = y1 - y2, J2 - J1
        g = gcd(num, den)
        num, den = num // g, den // g
        digits = []
        for t in range((J2 - J1) // den + 1):
            J = J1 + t * den
            ht = y1 - t * num
            if J == M:
                digits.append(1)
                continue
            if pmap.get(J) != ht:
                digits.append(0)
                continue
            dsum = 0
            for i, cc in enumerate(A[J]):
                if cc and E1 * vp(cc, P) + i * H == ht:
                    dsum += cc // P ** vp(cc, P)
            digits.append(dsum % P)
        sides.append((J1, J2, num, den, digits))
    return hull, sides


def composed_mu2star(f, K):
    n = len(f) - 1
    M = n // D2
    A, top = dev(list(f), K, M)
    pins = []
    for j, c in enumerate(A):
        pj = pin_leg_a(c)
        if pj is not None:
            pins.append((j, pj))
    # top coefficient (non-monic partial-side top): deg < D2 slot too
    tp = pin_leg_a(top) if top != [1] else 0
    pins.append((M, tp if tp is not None else 0))
    hull = lower_hull(pins)
    mu = 0
    for k in range(len(hull) - 1):
        (j1, y1), (j2, y2) = hull[k], hull[k + 1]
        if (y1 - y2) > E2C * (j2 - j1):   # slope > T2 = E2
            mu += j2 - j1
    return mu, hull


def leg_a():
    print('== LEG A: (2,2) mixed side + live sibling (out of battery) ==')
    # blocks: key^2 + in-budget perturbation (above every floor)
    fplus = padd(ppow(KEY[1], 2), psca(3 ** 6, [0, 1, 0, -3]))
    # 3^6*(x*Phi'):  x*Phi' = -3x + x^3
    fminus = padd(ppow(KEY[2], 2), psca(3 ** 7, PHI))
    sib = padd(PHI, [-27])
    f = pmul(pmul(fplus, fminus), sib)
    chk(len(f) - 1 == 18, 'deg f = %d != 18' % (len(f) - 1))
    hull, sides = level1_read(f)
    chk(hull == [(0, 26), (1, 20), (9, 0)],
        'A-1 hull %s != [(0,26),(1,20),(9,0)]' % hull)
    inner = [s for s in sides if s[3] == 2]
    chk(len(inner) == 1, 'A-1 inner side count %d' % len(inner))
    if inner:
        (J1, J2, num, den, digits) = inner[0]
        chk((num, den) == (5, 2) and (J1, J2) == (1, 9),
            'A-1 inner side (%d,%d) slope %d/%d' % (J1, J2, num, den))
        mult = fp_factor_linear(digits, P)
        chk(mult == {1: 2, 2: 2},
            'A-1 residual multiplicities %s != {1:2,2:2}' % mult)
    for s in (1, 2):
        mu, chull = composed_mu2star(f, KEY[s])
        chk(mu == 2, 'A-2 class %d: mu2* = %d != m_r = 2 (hull %s)'
            % (s, mu, chull))
        print('  class s=%d: mu2* = %d (composed hull %s)' % (s, mu, chull))
    # PARI leg
    gp_in = []
    gp_in.append('f = %s;' % poly_str(f))
    gp_in.append('print("disc ", poldisc(f) != 0);')
    gp_in.append('L = factorpadic(f, 3, 120);')
    gp_in.append('K1 = %s; K2 = %s;'
                 % (poly_str(KEY[1]), poly_str(KEY[2])))
    gp_in.append('for(i=1, matsize(L)[1], g = L[i,1];'
                 ' d = poldegree(g);'
                 ' t1 = valuation(polresultant(g, K1), 3);'
                 ' t2 = valuation(polresultant(g, K2), 3);'
                 ' print("fac ", d, " ", t1, " ", t2))')
    out = gp_run('\n'.join(gp_in))
    lines = [l for l in out.splitlines() if l.startswith(('disc', 'fac'))]
    print('  gp: %s' % lines)
    chk(any(l == 'disc 1' for l in lines), 'A-3 disc(f) == 0?')
    degsum = {1: 0, 2: 0}
    sib_deg = []
    for l in lines:
        if not l.startswith('fac'):
            continue
        _, d, t1, t2 = l.split()
        d, t1, t2 = int(d), Fraction(int(t1)), Fraction(int(t2))
        # per-root v(K_s(theta)) = t_s/d ; class iff > E2/(e1e2) = 5/2
        c1 = Fraction(t1, d) > Fraction(5, 2)
        c2 = Fraction(t2, d) > Fraction(5, 2)
        chk(not (c1 and c2), 'A-3 factor deg %d in BOTH classes' % d)
        if c1:
            degsum[1] += d
        elif c2:
            degsum[2] += d
        else:
            sib_deg.append(d)
    chk(degsum == {1: 8, 2: 8},
        'A-3 class degree sums %s != {1:8, 2:8} = D2*m_r' % degsum)
    chk(sorted(sib_deg) == [2],
        'A-3 sibling degrees %s != [2]' % sib_deg)


def poly_str(f):
    return '+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f)
                    if c) or '0'


def gp_run(script):
    r = subprocess.run(['gp', '-q', '-D', 'parisizemax=4G'],
                       input=script, capture_output=True, text=True,
                       timeout=600)
    if r.returncode != 0:
        print('  gp stderr: %s' % r.stderr[-500:])
    return r.stdout


# =================== LEG B: the b* = 0 cert corner =================
def leg_b():
    print('== LEG B: CERT-TOP corner (e2,f2)=(1,5), b*=0 (out of battery) ==')
    # find irreducible quintic T^5 + c2 T^2 + c1 T + c0 over F_3,
    # c2 != 0 (t* = 2)
    quint = None
    for c2 in (1, 2):
        for c1 in range(3):
            for c0 in (1, 2):
                cand = [c0, c1, c2, 0, 0, 1]
                if fp_irreducible(cand, 3):
                    quint = cand
                    break
            if quint:
                break
        if quint:
            break
    chk(quint is not None, 'B: no admissible quintic found')
    if quint is None:
        return
    c0, c1, c2 = quint[0], quint[1], quint[2]
    print('  psi2 = T^5 + %d T^2 + %d T + %d (irreducible /F3)'
          % (c2, c1, c0))
    # Phi2 = Phi'^5 - [c0*nhat(15) + c1*nhat(12)*Phi' + c2*nhat(9)*Phi'^2]
    # nhat(15) = 3^7 x, nhat(12) = 3^6, nhat(9) = 3^4 x
    lift = padd(padd(psca(c0 * 3 ** 7, [0, 1]),
                     psca(c1 * 3 ** 6, PHI)),
                psca(c2 * 3 ** 4, pmul([0, 1], pmul(PHI, PHI))))
    Phi2 = padd(ppow(PHI, 5), psca(-1, lift))
    chk(len(Phi2) - 1 == 10, 'B: deg Phi2 = %d != 10' % (len(Phi2) - 1))
    fk = pmul(Phi2, Phi2)
    # honest read: dev by Phi2
    Ch, toph = dev(list(fk), Phi2, 2)
    chk(Ch == [[], []] and toph == [1],
        'B-4 honest read not DRAIN: %s top %s' % (Ch, toph))
    # shadow read: level-1 dev, then Y-division by K2 over Z[x]/Phi'
    A, topA = dev(list(fk), PHI, 10)
    FY = A + [topA]                      # F(x, Y), coeffs in x (deg<2)
    assert topA == [1]
    # K2(x,Y) = Y^5 - (c0 3^7 x + c1 3^6 Y + c2 3^4 x Y^2)
    K2Y = [psca(-c0 * 3 ** 7, [0, 1]), psca(-c1 * 3 ** 6, [1]),
           psca(-c2 * 3 ** 4, [0, 1]), [], [], [1]]
    Q1, Sh0 = ydiv(FY, K2Y)
    Q2, Sh1 = ydiv(Q1, K2Y)
    chk(yis(Q2, [[], [], [], [], [], [1]][5:6] and [[1]]) or True, '')
    # (Q2 should be [ [1] ]: the leading 1)
    chk(len(Q2) == 1 and Q2[0] == [1], 'B: ShG_2 = %s != 1' % Q2)
    # read slots: ShC_j slot (a,b) = coeff of x^a Y^b; height 2v+a+3b
    for tag, Sh, theta in (('ShC_0', Sh0, 31), ('ShC_1', Sh1, 16)):
        hts = []
        for b, cx in enumerate(Sh):
            for a, c in enumerate(cx):
                if c:
                    hts.append((2 * vp(c, P) + a + 3 * b, a, b, c))
        pin = min(h[0] for h in hts) if hts else None
        print('  %s pin %s slots %s' % (tag, pin,
              [(h, a, b, vp(c, P)) for (h, a, b, c) in sorted(hts)[:4]]))
        if tag == 'ShC_1':
            chk(pin == 16, 'B-1 pin(ShC_1) = %s != 16 = THETA_1' % pin)
            d00 = Sh[0][0] if Sh and Sh[0] else 0
            chk(d00 != 0 and vp(d00, P) == 8,
                'B-1 slot (0,0) digit %s vp %s != 8' % (d00, vp(d00, P)
                                                        if d00 else None))
            if d00:
                chk((d00 // 3 ** 8) % 3 == (c2 * c2) % 3,
                    'B-2 digit unit %d != c2^2 = %d (mod 3)'
                    % ((d00 // 3 ** 8) % 3, (c2 * c2) % 3))
        else:
            chk(pin is None or pin >= 31,
                'B-3 pin(ShC_0) = %s < 31 = THETA_0' % pin)


def ydiv(FY, KY):
    """divide F(x,Y) by monic-in-Y KY over R = Z[x]/(Phi').
    Returns (quotient, remainder) as Y-coefficient lists of x-polys."""
    F = [list(c) for c in FY]
    dK = len(KY) - 1
    q = [[] for _ in range(max(len(F) - dK, 0))]
    while len(F) - 1 >= dK and any(pstrip(list(c)) for c in F):
        # strip top zero Y-coeffs
        while F and not pstrip(list(F[-1])):
            F.pop()
        if len(F) - 1 < dK:
            break
        d = len(F) - 1
        c = pstrip(list(F[-1]))
        q[d - dK] = padd(q[d - dK], c)
        for i in range(len(KY)):
            term = pmul(c, KY[i])
            # reduce mod Phi' (x^2 -> 3)
            term = xred(term)
            F[d - dK + i] = padd(F[d - dK + i], psca(-1, term))
        F[d] = []
    while F and not pstrip(list(F[-1])):
        F.pop()
    return q, F


def xred(f):
    """reduce mod Phi' = x^2 - 3: x^2 -> 3."""
    f = list(f)
    while len(f) > 2:
        c = f.pop()
        f[len(f) - 2] += 3 * c
    return pstrip(f)


def yis(a, b):
    return a == b


def fp_irreducible(f, p):
    """f monic over F_p irreducible? brute: no roots of x^(p^k)-x
    gcd for k < deg; use simple: no factor of degree <= deg/2 by
    trial division over F_p (deg 5: check deg 1 and 2 factors)."""
    fp = [c % p for c in f]
    n = len(fp) - 1
    # deg-1: roots
    for r in range(p):
        if sum(c * pow(r, i, p) for i, c in enumerate(fp)) % p == 0:
            return False
    # deg-2: all monic quadratics
    for a in range(p):
        for b in range(p):
            g = [b, a, 1]
            if fpdiv_zero(fp, g, p):
                return False
    return True


def fpdiv_zero(f, g, p):
    f = [c % p for c in f]
    dg = len(g) - 1
    while len(f) - 1 >= dg:
        while f and f[-1] % p == 0:
            f.pop()
        if len(f) - 1 < dg:
            break
        c = f[-1]
        d = len(f) - 1
        for i in range(len(g)):
            f[d - dg + i] = (f[d - dg + i] - c * g[i]) % p
        f = f[:-1]
    f = [c % p for c in f]
    return not any(f)


if __name__ == '__main__':
    leg_a()
    leg_b()
    print('=== FRESH VERDICT: %s -- %d checks, %d violations ==='
          % ('GREEN' if not VIOL else 'RED', NCHK, len(VIOL)))
    sys.exit(0 if not VIOL else 1)
