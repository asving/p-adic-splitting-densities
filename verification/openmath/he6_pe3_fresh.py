"""HE6 passPE3 — FRESH hostile-route legs (verifier-built, decorrelated).

Disjoint from: the sealed he6 battery ((2,1,1), f1=1, mu=4, q in {3,5,7}),
he6r1's 682 (level-2 at f1=1), HE7's arc legs, PE2's ell=3 label battery
((2,1,1) over Z_5) and PE2's f1=2 coset certificate ((2,2,3) over Z_3, q=1).

LEG A — the FIRST f1 = 3 sigma legs of this unit's arc (every prior sigma
leg had f1 = 1; PE2's f1 = 2 leg was a display-refutation leg, not sigma).
Frames: (e1,f1,h) = (1,3,1), D' = 3, mu = 4, lambda = 7/2 (ell = 2), so
deg f = 12; K = F_{q^3}.
  A1 (Z_2, Phi' = x^3+4x+8, psi = T^3+T+1):
     SPLIT-FROB: R_lam = (Z-eta)(Z-eta^2) — the two labels are FROBENIUS
     CONJUGATES over F_2, the exact configuration LEMMA HE6-5 makes
     Galois-stable separately (no prior machine row tested it: every
     battery row had f1 = 1, where iota is trivial).
     Predicted sigma (THEOREM HE6.A): {(2,3),(2,3)}.
     INERT2: R_lam = Z^2+Z+(1+eta) irreducible over F_8 (Tr = 1).
     Predicted sigma: {(2,6)} (d_r = 2: class size D' ell d_r = 12 = deg f).
  A2 (Z_3, Phi' = x^3-9x-27, psi = T^3-T-1): SPLIT-FROB with s2 = eta^3 =
     eta+1 = Frob(eta); INERT2 with a brute-found irreducible quadratic.
     Same predictions.
Members: base + perturbations strictly above the lambda-line; an
independent reader re-derives (development, dv, polygon, R_lam over
F_{q^3}) from the integer coefficients of every member and must reproduce
the intended outer data. sigma oracle: gp factor(f) over Q, then
nfinit([g,[p]]) + idealprimedec per rational factor (nf route — NOT the
battery's factorpadic route).

LEG B — fresh coset certificate at q(k) = 3 (PE2's witness had q = 1).
Frame: (e1,f1,h) = (2,2,5), O = Z_3, Phi' = x^4 + 3^10 (roots v = 5/2,
eta = res(theta^2/3^5), eta^2 = -1, K = F_9), varpi = x*pi^{-2}
(i0 = 1, a0 = -2 from 5*i0 + 2*a0 = 1).
  k = 7 : i0(7) = 1, T(7) = {0} proper, q(7) = (1*7 - 1)/2 = 3.
     LEMMA HE6-1L [r2] predicts realized varpi-read set
     = eta^{-3} * F_3^x = {eta, 2eta}  (eta^{-3} = eta since eta^2 = -1);
     the [r1] bare span predicted {1,2} — DISJOINT.
  k = 15 = (D'-1)h : T full; predicted ALL 8 of F_9^x (twist-invisible).
Exhaustive enumeration of C in O[x], deg C < 4, over a truncated coefficient
grid; exact residue arithmetic in Q[x]/(x^4+3^10) via Fractions.

LEG C — the RIDER identity res(varpi(theta)^k / n(k)(theta)) = eta^{q(k)},
q(k) = (i0*k - i0(k))/e1, verified numerically for k = 0..16 on the leg-B
frame (independent of the enumeration).

PREREGISTERED (violations counted):
  FB-1: every member's reader-derived polygon is the single side
        (0,14)-(4,0) and R_lam == the intended residual, per member.
  FB-2: PARI sigma == THEOREM HE6.A's dictionary on every member of every
        leg-A row, invariant under all perturbations.
  FB-3: leg-B k=7 realized set == {eta, 2eta} (and != the bare span);
        k=15 realized set == all of F_9^x.
  FB-4: leg-C RIDER identity holds at every k in 0..16.
"""
import subprocess, json, itertools, sys, time
from fractions import Fraction as Fr

VIOL = []
NOTES = {}


def note(leg, k=1):
    NOTES[leg] = NOTES.get(leg, 0) + k


def viol(leg, msg, data=None):
    VIOL.append((leg, msg, data))
    print('  ** VIOLATION [%s] %s %s' % (leg, msg, data))


# ------------------------------------------------------- small F_{q^3}
class F3q:
    """F_{q^3} = F_q[T]/psi, psi monic cubic, elements = tuples len 3."""
    def __init__(self, q, psi):
        self.q, self.psi = q, psi          # psi: list of 4 ints, monic
    def red(self, v):
        v = [c % self.q for c in v]
        while len(v) > 3:
            lead = v.pop()
            d = len(v)                      # popped monomial was T^d
            for i in range(3):              # T^d = T^{d-3} * (-psi[0..2])
                v[d - 3 + i] = (v[d - 3 + i] - lead * self.psi[i]) % self.q
        while len(v) < 3:
            v.append(0)
        return tuple(v)
    def add(self, a, b):
        return tuple((x + y) % self.q for x, y in zip(a, b))
    def mul(self, a, b):
        out = [0] * 5
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                out[i + j] = (out[i + j] + x * y) % self.q
        return self.red(out)
    def eltall(self):
        return [tuple(v) for v in itertools.product(range(self.q), repeat=3)]
    zero = property(lambda s: (0, 0, 0))
    one = property(lambda s: (1, 0, 0))


def vp(n, p):
    if n == 0:
        return None
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


# --------------------------------------------- leg A frame + reader
class FrameA:
    def __init__(self, p, phi, psi):
        self.p, self.phi, self.psi = p, phi, psi   # phi: monic cubic int list
        self.K = F3q(p, psi)

    def develop(self, f, mu=4):
        """Phi'-development of f (int coeff list, ascending), exact."""
        A, cur = [], list(f)
        for j in range(mu + 1):
            q, r = poldivmod(cur, self.phi)
            A.append(r + [0] * (3 - len(r)))
            cur = q
        assert not any(cur), 'development leftover'
        return A

    def dv(self, Aj):
        vals = [vp(c, self.p) + i for i, c in enumerate(Aj[:3]) if c]
        return min(vals) if vals else None

    def residue(self, Aj, m):
        """res(A_j(theta)/pi^m) in F_{q^3} (e1 = 1, varpi = pi, h = 1)."""
        out = [0, 0, 0]
        for i, c in enumerate(Aj[:3]):
            if c and vp(c, self.p) + i == m:
                out[i] = (c // self.p ** (m - i)) % self.p
        return self.K.red(out)

    def read(self, f):
        """polygon + residual at the (expected) single side lam = 7/2."""
        A = self.develop(f)
        dvs = [self.dv(a) for a in A]
        pins = [(j, dvs[j]) for j in range(5) if dvs[j] is not None]
        # single-side check: (0,14),(4,0) on hull, everything else above
        ok = (dvs[0] == 14 and dvs[4] == 0 and
              all(dvs[j] is None or dvs[j] > 14 - Fr(7, 2) * j
                  for j in (1, 3)) and (dvs[2] is None or dvs[2] >= 7))
        R = [self.residue(A[0], 14), self.residue(A[2], 7),
             self.residue(A[4], 0)]
        return ok, dvs, R

    def roots_of_quad(self, R):
        """roots in F_{q^3} of R = R[0] + R[1] Z + R[2] Z^2 (R[2] = 1)."""
        K = self.K
        return [s for s in K.eltall()
                if K.add(K.add(R[0], K.mul(R[1], s)),
                         K.mul(K.mul(s, s), R[2])) == K.zero]


def poldivmod(f, g):
    """exact division with remainder, g monic, integer lists ascending."""
    f = list(f)
    q = [0] * max(1, len(f) - len(g) + 1)
    while len(f) >= len(g) and any(f):
        while f and f[-1] == 0:
            f.pop()
        if len(f) < len(g):
            break
        c, d = f[-1], len(f) - len(g)
        q[d] = c
        for i, gc in enumerate(g):
            f[d + i] -= c * gc
    while len(f) > len(g) - 1:
        assert f[-1] == 0
        f.pop()
    return q, f + [0] * (len(g) - 1 - len(f))


def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
            for i in range(n)]


def pmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def build_f(A, phi):
    f = [0]
    for j in range(len(A) - 1, -1, -1):
        f = padd(pmul(f, phi), list(A[j]))
    return f


def lift_res(res_elt, m, p):
    """A_j (int list, deg<3) with dv = m and residue res_elt at pi = p."""
    return [res_elt[i] * p ** (m - i) if res_elt[i] else 0 for i in range(3)]


# ----------------------------------------------------------- gp oracle
def gp_run(script):
    r = subprocess.run(['gp', '-q'], input=script.encode(),
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       timeout=1800)
    if r.returncode != 0:
        raise RuntimeError('gp failed: %s' % r.stderr.decode()[:400])
    return r.stdout.decode()


def polystr(f):
    return '+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f) if c) or '0'


GP_SIG = r"""
sig(f, p) = {
  my(fa = factor(f)[,1]~, out = List());
  for (i = 1, #fa,
    my(g = fa[i], nf, dec);
    if (poldegree(g) == 1, listput(out, [1,1]),
      nf = nfinit([g, [p]]);
      dec = idealprimedec(nf, p);
      for (j = 1, #dec, listput(out, [dec[j].e, dec[j].f]))));
  vecsort(Vec(out))
}
"""


def gp_sig_batch(polys, p):
    lines = [GP_SIG]
    for i, f in enumerate(polys):
        lines.append('print("R %d ", sig(%s, %d)); ' % (i, polystr(f), p))
    lines.append('print("D ", vector(%d, i, poldisc(%s)!= 0 )); quit'
                 % (1, polystr(polys[0])))
    out = gp_run('\n'.join(lines) + '\n')
    got = {}
    for line in out.splitlines():
        if line.startswith('R '):
            idx, rest = line[2:].split(' ', 1)
            sig = tuple(sorted(tuple(int(x) for x in pair.strip('[] ').split(','))
                               for pair in rest.strip()[1:-1].split('], [')))
            got[int(idx)] = sig
    return got


# ---------------------------------------------------------------- leg A
def leg_A():
    print('== LEG A: f1 = 3 sigma rows (first of the arc) ==')
    rows = []
    # frame A1: Z_2
    frA1 = FrameA(2, [8, 4, 0, 1], [1, 1, 0, 1])       # x^3+4x+8, T^3+T+1
    # frame A2: Z_3
    frA2 = FrameA(3, [-27, -9, 0, 1], [-1, -1, 0, 1])  # x^3-9x-27, T^3-T-1
    for fr, tag in [(frA1, 'Z_2'), (frA2, 'Z_3')]:
        p, K = fr.p, fr.K
        eta = (0, 1, 0)
        frob = tuple  # eta^q computed below
        eta_q = K.mul(eta, eta) if p == 2 else K.mul(K.mul(eta, eta), eta)
        # SPLIT-FROB: R = (Z - eta)(Z - eta^q)
        s1, s2 = eta, eta_q
        r0 = K.mul(s1, s2)
        r1 = tuple((-(a + b)) % p for a, b in zip(s1, s2))
        cfgs = [('SPLIT-FROB', [r0, r1], ((2, 3), (2, 3)))]
        # INERT2: brute-find c with Z^2 + Z + c irreducible over F_{q^3}
        for c in K.eltall():
            if c == K.zero:
                continue
            if not fr.roots_of_quad([c, K.one, K.one]):
                cfgs.append(('INERT2', [c, K.one], ((2, 6),)))
                break
        for name, rco, sig_pred in cfgs:
            base = {0: lift_res(rco[0], 14, p), 2: lift_res(rco[1], 7, p),
                    4: [1, 0, 0]}
            perts = [dict()]
            # strictly-above-line perturbations (dv targets: j=1 >= 11,
            # j=3 >= 4; deeper digits on j=0 (>14) and j=2 (>7))
            perts += [{1: [p ** 11, 0, 0]}, {1: [0, p ** 11, 0]},
                      {3: [p ** 4, 0, 0]}, {3: [0, 0, p ** 4]},
                      {0: [p ** 15, 0, 0]}, {0: [0, p ** 14, 0]},
                      {2: [0, 0, p ** 8]}, {2: [p ** 8, 0, 0]},
                      {1: [0, 0, p ** 12], 3: [0, p ** 4, 0]}]
            members = []
            for pt in perts:
                A = [list(base.get(j, [0, 0, 0])) for j in range(5)]
                for j, ad in pt.items():
                    A[j] = padd(A[j], ad)
                members.append(build_f(A, fr.phi))
            # reader per member (FB-1)
            for m_i, f in enumerate(members):
                ok, dvs, R = fr.read(f)
                note('PE3-READ')
                want_R = [rco[0], rco[1] if len(rco) > 1 else K.zero, K.one]
                if not ok or R != want_R:
                    viol('FB-1', 'reader outer data mismatch',
                         dict(row=tag, cfg=name, member=m_i, dvs=dvs, R=R))
            # sigma oracle (FB-2)
            got = gp_sig_batch(members, p)
            n_ok = 0
            for m_i in range(len(members)):
                note('PE3-SIG')
                if got.get(m_i) != tuple(sorted(sig_pred)):
                    viol('FB-2', 'PARI sigma != HE6.A dictionary',
                         dict(row=tag, cfg=name, member=m_i,
                              got=got.get(m_i), want=sig_pred))
                else:
                    n_ok += 1
            print('  %s %-10s members=%d sigma_pred=%s PARI_agree=%d'
                  % (tag, name, len(members), sig_pred, n_ok))
            rows.append(dict(row=tag, cfg=name, members=len(members),
                             agree=n_ok, pred=sig_pred))
    return rows


# ---------------------------------------------------------------- leg B
# Q(theta), theta^4 = -3^10; elements = 4-vectors of Fractions.
P = 3
THETA4 = -(P ** 10)


def qmul(a, b):
    out = [Fr(0)] * 7
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    for i in range(6, 3, -1):
        out[i - 4] += out[i] * THETA4
        out[i] = Fr(0)
    return out[:4]


def v3fr(x):
    if x == 0:
        return None
    v = 0
    n, d = x.numerator, x.denominator
    while n % P == 0:
        n //= P
        v += 1
    while d % P == 0:
        d //= P
        v -= 1
    return v


def qval(z):
    """dv = 2*v of z in Q(theta) (v(theta) = 5/2 -> dv(theta^j) = 5j)."""
    vals = [2 * v3fr(c) + 5 * j for j, c in enumerate(z) if c != 0]
    return min(vals) if vals else None


def qres(z):
    """residue in F_9 = F_3(eta) of a UNIT z (dv = 0); eta = res(theta^2/3^5).
    Returns (a, b) = a + b*eta."""
    assert qval(z) == 0, 'not a unit'
    a, b = 0, 0
    for j, c in enumerate(z):
        if c != 0 and 2 * v3fr(c) + 5 * j == 0:
            assert j % 2 == 0, 'odd theta-power attains integer dv'
            t = j // 2
            u = c / Fr(P) ** v3fr(c)
            r = (u.numerator * pow(u.denominator, -1, P)) % P
            if t == 0:
                a = (a + r) % P
            else:                       # t = 1: eta
                b = (b + r) % P
    return (a, b)


def f9mul(x, y):
    # (a+b eta)(c+d eta), eta^2 = -1
    a, b = x
    c, d = y
    return ((a * c - b * d) % P, (a * d + b * c) % P)


def leg_B():
    print('== LEG B: coset certificate at q(k) = 3, frame (2,2,5)/Z_3 ==')
    e1, f1, h = 2, 2, 5
    results = {}
    for k in (7, 15):
        i0k = k % 2 if (k % 2) * 5 % 2 == k % 2 else None
        i0k = next(i for i in range(e1) if (i * h - k) % e1 == 0)
        Tk = [t for t in range(f1) if k >= (i0k + e1 * t) * h]
        q = (1 * k - i0k) // e1          # i0(1) = 1 (varpi = x pi^-2)
        realized = set()
        grid = [Fr(0)] + [Fr(c * P ** m) for c in (1, 2) for m in range(0, 9)]
        cnt = 0
        for a in itertools.product(grid, repeat=4):
            C = list(a)
            sv = [2 * v3fr(c) + 5 * i for i, c in enumerate(C) if c != 0]
            if not sv or min(sv) != k:
                continue
            cnt += 1
            # z = C(theta) / varpi(theta)^k, varpi(theta) = theta * 3^-2
            # C/theta^k = C * theta^{4m-k} / (theta^4)^m,  m = ceil(k/4)
            m = -(-k // 4)
            z = [Fr(0)] * 4
            z[0] = Fr(1)
            for _ in range(4 * m - k):
                z = qmul(z, [Fr(0), Fr(1), Fr(0), Fr(0)])
            z = qmul(C, z)
            scale = Fr(1, THETA4 ** m) * Fr(P) ** (2 * k)
            z = [c * scale for c in z]
            realized.add(qres(z))
        results[k] = (i0k, Tk, q, sorted(realized), cnt)
        print('  k=%d: i0=%d T=%s q=%d  members=%d  realized=%s'
              % (k, i0k, Tk, q, cnt, sorted(realized)))
    # FB-3 checks: eta = (0,1); eta^{-3} = eta (eta^2 = -1)
    k7 = results[7]
    note('PE3-COSET', k7[4])
    if set(k7[3]) != {(0, 1), (0, 2)}:
        viol('FB-3', 'k=7 realized != {eta, 2eta}', k7[3])
    if set(k7[3]) == {(1, 0), (2, 0)}:
        viol('FB-3', 'k=7 realized == bare span (twist absent!)', k7[3])
    k15 = results[15]
    note('PE3-FULL', k15[4])
    allF9x = {(a, b) for a in range(3) for b in range(3)} - {(0, 0)}
    if set(k15[3]) != allF9x:
        viol('FB-3', 'k=15 realized != F_9^x', k15[3])
    return {k: dict(i0=r[0], T=r[1], q=r[2], realized=r[3], members=r[4])
            for k, r in results.items()}


def leg_C():
    print('== LEG C: RIDER identity res(varpi^k/n(k)) = eta^{q(k)}, k=0..16 ==')
    ok_all = True
    for k in range(17):
        i0k = next(i for i in range(2) if (i * 5 - k) % 2 == 0)
        q = (k - i0k) // 2
        # varpi^k / n(k) = (theta 3^-2)^k / (theta^{i0k} 3^{(k-5 i0k)/2})
        #               = theta^{k - i0k} * 3^{-2k - (k-5 i0k)/2}
        j = k - i0k
        m = -(-j // 4) if j else 0
        z = [Fr(0)] * 4
        z[0] = Fr(1)
        for _ in range(j):
            z = qmul(z, [Fr(0), Fr(1), Fr(0), Fr(0)])
        ex = -2 * k - (k - 5 * i0k) // 2
        z = [c * Fr(P) ** ex if ex >= 0 else c / Fr(P) ** (-ex) for c in z]
        got = qres(z)
        want = (1, 0)
        for _ in range(q % 4):
            want = f9mul(want, (0, 1))
        note('PE3-RIDER')
        if got != want:
            ok_all = False
            viol('FB-4', 'RIDER identity fails', dict(k=k, q=q, got=got,
                                                      want=want))
    print('  all k in 0..16: %s' % ('OK' if ok_all else 'FAIL'))


def main():
    t0 = time.time()
    rows = leg_A()
    legB = leg_B()
    leg_C()
    out = dict(rows=rows, legB=legB, notes=NOTES,
               viol=[(l, m, str(d)) for l, m, d in VIOL],
               secs=round(time.time() - t0, 1))
    with open('he6_pe3_fresh_results.json', 'w') as fh:
        json.dump(out, fh, indent=1, default=str)
    print('\nNOTES: %s' % NOTES)
    print('VIOLATIONS: %d' % len(VIOL))
    print('%.1fs' % (time.time() - t0))
    return 1 if VIOL else 0


if __name__ == '__main__':
    sys.exit(main())
