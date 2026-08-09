"""HE7 passPE3 FRESH ROUTE — a constructed f1 = 2 family at e1 = 1
(unramified level 1): the LAST never-machine-exercised sigma-genre that
HE7-BOX-2 names (f1 >= 2 stage genres).  Independent reader written from
the note's text (HE7_PROOF_2026-08-08.md S1-S8) alone; no he6/he7 import.

FRAME (new in every level-1 coordinate).  O = Z_p, p in {3, 5};
psi = T^2 - 2 irreducible over F_p (2 a non-residue mod 3 and 5);
Phi' = x^2 - 2p^2 (monic irreducible over Q_p, both roots of v = 1,
eta_theta = res(theta/p) = sqrt(2)); (e1, f1, h) = (1, 2, 1), D' = 2,
K = F_{p^2}, varpi = p (i0 = 0, a0 = 1), dv = e1*v = v on slot values
dv(b0 + b1 x) = min(v(b0), v(b1) + 1).  Level-2 datum: l = 2, u in
{5, 7} odd (lam = u/2 > D'h = 2), r = Z - s with s in F_{p^2}^x —
INCLUDING s outside F_p (a level-1 residual root in the PROPER quadratic
extension, reached by no prior leg); d_r = 1, K2 = K = F_{p^2},
D'' = 4, T2 = 2u, dv2 = 2 dv.  Psi = Phi'^2 + B0, dv(B0) = u,
res(B0(theta)/p^u) = -s (DEFINITION HE6-1).  Members
f = Psi^2 + A1 Psi + A0 (mu2 = 2), slot-built by (LIFT2) plus noise
strictly above the line.  DICTIONARY at this frame (e = e1*l*l2 = 2*l2,
f = f1*d_r*d_r2 = 2*d_r2): lam2 not in Z -> {(4,2)}; lam2 in Z with R2
inert over F_{p^2} -> {(2,4)}; split -> {(2,2),(2,2)}; two sides ->
{(2,2),(2,2)}; R2 = (Z-s2)^2 -> alpha-refine (LEMMAS HE7-12/13);
Psi | f -> peel (LEMMA HE6R1-3) -> {(2,2),(2,2)}.  The residual twist
(S1 cocycle at odd lam2): R2 = Z^2 + a1 Z + a0 * s^{-1} — the twist
factor is now an element of F_{p^2} (beta = iota(s)), the first leg where
the cocycle acts through a PROPER residue extension.

PREREGISTERED PREDICTIONS (written before the full run).
 P1 sigma(read) == sigma(PARI) member by member, zero mismatches.
 P2 the level-1 read of every kept member is the boxed node: single
    Phi'-side slope u/2, level-1 residual EXACTLY (Z - s)^2 over F_{p^2}.
 P3 every level-2 polygon slope > T2 (THEOREM HE7.A(1)), and the letter
    alphabet is exactly {(4,2)} / {(2,4)} / {(2,2),(2,2)} — no 4th letter.
 P4 every alpha-refine chain terminates with STRICTLY increasing slopes
    (LEMMA HE7-13 at f1 = 2), and slot geometry holds at every refine
    (Psi's occupied slots exactly at T2; w's slot-min exactly lam2 > T2).
 P5 TOOTH (twist): dropping the s^{-1} twist flips the predicted sigma
    on some odd-lam2 members with s != 1, and EVERY flipped prediction is
    refuted by PARI while the twisted read stays 100%.
 P6 TOOTH (lazy dictionary): misreading the repeated residual as split
    ({(2,2),(2,2)}) is refuted by PARI on every refine member whose true
    sigma differs.
SMOKE RECORD (disclosed): before sealing, run_member was exercised on TWO
members only — (p,u,s) = (3,5,(1,0)) genre int-split and (3,5,(0,1))
genre int-repeated (refine fired, terminated, sigma == PARI both), plus
pari_sigma on x^8 smoke.  No row and no other genre ran pre-seal.
"""
import sys, os, json, time, random
sys.path.insert(0, '/data/users/asvin/.local/lib/python3.10/site-packages')
import cypari2
pari = cypari2.Pari()
pari.allocatemem(1 << 30)

HERE = os.path.dirname(os.path.abspath(__file__))
BIG = 10 ** 9
RES = {'rows': [], 'checks': {}, 'viol': [], 'genres': {}, 'teeth': {},
       'secs': 0}


def viol(what, detail):
    RES['viol'].append({'what': what, 'detail': str(detail)[:300]})
    print('  !! VIOLATION %s %s' % (what, str(detail)[:200]))


def note(k, n=1):
    RES['checks'][k] = RES['checks'].get(k, 0) + n


# ---------------- exact Z[x] arithmetic (coefficient lists, low first)
def trim(a):
    while a and a[-1] == 0:
        a.pop()
    return a


def padd(a, b):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                 for i in range(n)])


def pneg(a):
    return [-c for c in a]


def pmul(a, b):
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return trim(out)


def pdivmod(a, b):
    """a = q*b + r with b MONIC; exact over Z (synthetic division)."""
    a = list(a)
    db = len(b) - 1
    if len(a) < len(b):
        return [], trim(a)
    q = [0] * (len(a) - db)
    for k in range(len(a) - db - 1, -1, -1):
        c = a[k + db]
        q[k] = c
        if c:
            for i in range(db + 1):
                a[k + i] -= c * b[i]
    return trim(q), trim(a[:db])


def development(f, g, nslots):
    """f = sum_j c_j g^j, deg c_j < deg g; returns [c_0..c_{nslots-1}]."""
    out, cur = [], list(f)
    for _ in range(nslots):
        cur, r = pdivmod(cur, g)
        out.append(r)
    if cur:
        raise RuntimeError('development overflow')
    return out


def vp(n, p):
    if n == 0:
        return BIG
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


# ---------------- F_{p^2} = F_p(eta), eta^2 = 2: elements (a, b) = a+b*eta
class F2:
    def __init__(self, p):
        self.p = p
        self.els = [(a, b) for a in range(p) for b in range(p)]

    def add(self, x, y):
        return ((x[0] + y[0]) % self.p, (x[1] + y[1]) % self.p)

    def neg(self, x):
        return ((-x[0]) % self.p, (-x[1]) % self.p)

    def mul(self, x, y):
        return ((x[0] * y[0] + 2 * x[1] * y[1]) % self.p,
                (x[0] * y[1] + x[1] * y[0]) % self.p)

    def inv(self, x):
        # (a+b eta)^-1 = (a - b eta)/(a^2 - 2 b^2)
        d = (x[0] * x[0] - 2 * x[1] * x[1]) % self.p
        di = pow(d, self.p - 2, self.p)
        return ((x[0] * di) % self.p, ((-x[1]) * di) % self.p)

    def sq_roots(self, x):
        return [z for z in self.els if self.mul(z, z) == x]

    def quad_roots(self, a1, a0):
        """roots of Z^2 + a1 Z + a0 over F_{p^2} (p odd)."""
        # Z = (-a1 +- sqrt(a1^2 - 4 a0)) / 2
        disc = self.add(self.mul(a1, a1),
                        self.neg(self.mul((4 % self.p, 0), a0)))
        rts = self.sq_roots(disc)
        if not rts:
            return []
        inv2 = self.inv((2 % self.p, 0))
        out = []
        for r in rts:
            out.append(self.mul(self.add(self.neg(a1), r), inv2))
        return sorted(set(out))

# ---------------- the frame
class Frame:
    def __init__(self, p, u, s):
        self.p, self.u, self.s = p, u, s          # s = (a,b) in F_{p^2}^x
        self.F = F2(p)
        self.Phi = [-2 * p * p, 0, 1]             # x^2 - 2p^2
        self.T2 = 2 * u
        self.B0 = self.lift1(u, self.F.neg(s))    # res -s at height u
        self.Psi0 = padd(pmul(self.Phi, self.Phi), self.B0)

    def lift1(self, m, g):
        """c in Z[x], deg < 2, dv(c) = m (if g != 0), level-1 residue g."""
        b0 = g[0] * self.p ** m
        b1 = g[1] * self.p ** (m - 1) if g[1] else 0
        return trim([b0, b1])

    def dv1(self, c):
        """dv of a deg<2 slot: min(v(b0), v(b1)+1)."""
        if not c:
            return BIG
        b0 = c[0] if len(c) > 0 else 0
        b1 = c[1] if len(c) > 1 else 0
        return min(vp(b0, self.p), vp(b1, self.p) + 1)

    def res1(self, c, m):
        """level-1 residue of c at height m (in F_{p^2})."""
        b0 = c[0] if len(c) > 0 else 0
        b1 = c[1] if len(c) > 1 else 0
        g0 = (b0 // self.p ** m) % self.p if vp(b0, self.p) == m else 0
        g1 = (b1 // self.p ** (m - 1)) % self.p \
            if m >= 1 and vp(b1, self.p) == m - 1 else 0
        return (g0, g1)

    def slots2(self, C, nslots=2):  # [post-seal repair, disclosed]
        """occupied Phi'-slot values 2*dv1(c_s) + s*u, s = 0,1 (deg C < 4)."""
        cs = development(C, self.Phi, nslots)
        return [(s, 2 * self.dv1(cs[s]) + s * self.u)
                for s in range(nslots) if self.dv1(cs[s]) < BIG]

    def dv2(self, C):
        sv = self.slots2(C)
        return min(v for _, v in sv) if sv else BIG

    def res2(self, C, k):
        """level-2 residue of C at height k = dv2(C); class-checked."""
        s0 = k % 2
        cs = development(C, self.Phi, 2)
        m0 = (k - s0 * self.u) // 2
        # cross-class strictness: the other slot must sit strictly above
        oth = 1 - s0
        if 2 * self.dv1(cs[oth]) + oth * self.u <= k:
            viol('res2 cross-class tie', {'k': k})
        if 2 * self.dv1(cs[s0]) + s0 * self.u != k:
            viol('res2 attaining slot off', {'k': k})
        return self.res1(cs[s0], m0)

    def lift2(self, k, g):
        """(LIFT2) polynomial: deg < 4, dv2 = k, level-2 residue g."""
        s0 = k % 2
        m0 = (k - s0 * self.u) // 2
        c = self.lift1(m0, g)
        return pmul(c, self.Phi) if s0 else c


# ---------------- the independent level-2 reader (from the note's text)
def read_level1(fr, f):
    """the boxed-node check: single Phi'-side slope u/2, residual (Z-s)^2."""
    a = development(f, fr.Phi, 5)
    w = [fr.dv1(c) for c in a]
    if not (w[0] == 2 * fr.u and w[2] == fr.u and w[4] == 0):
        return False
    if not (2 * w[1] > 3 * fr.u and 2 * w[3] > fr.u):   # strictly above line
        return False
    r0, r2 = fr.res1(a[0], 2 * fr.u), fr.res1(a[2], fr.u)
    ss, s2 = fr.F.mul(fr.s, fr.s), fr.F.mul((2 % fr.p, 0), fr.s)
    return r0 == ss and r2 == fr.F.neg(s2)              # (Z-s)^2


def read_level2(fr, f, use_twist=True, max_ref=40):
    """returns (sigma tuple, nrefines, peel?, trace) or ('VIOL', ...)."""
    Psi = list(fr.Psi0)
    refs = 0
    last_lam2 = -BIG
    while True:
        A = development(f, Psi, 3)
        if A[2] != [1]:
            viol('not monic in key', {})
            return None
        y0, y1 = fr.dv2(A[0]), fr.dv2(A[1])
        if y0 >= BIG:                                   # Psi | f: the PEEL
            if fr.dv2(A[1]) >= BIG:
                viol('double key division', {})
                return None
            # f = Psi * (Psi + A1); both factors (e,f) = (2,2)
            return (((2, 2), (2, 2)), refs, True, (y0, y1))
        # polygon of {(0,y0),(1,y1),(2,0)}
        two_sides = (2 * y1 < y0)
        if two_sides:
            lam_hi, lam_lo = y0 - y1, y1
            if lam_lo <= fr.T2:
                viol('slope <= T2', {'lam': lam_lo})
            return (((2, 2), (2, 2)), refs, False, (y0, y1))
        lam2x2 = y0                                     # side slope = y0/2
        if lam2x2 <= 2 * fr.T2:
            viol('slope <= T2', {'y0': y0})
        if lam2x2 % 2 == 1:                             # lam2 not integer
            return (((4, 2),), refs, False, (y0, y1))
        lam2 = lam2x2 // 2
        a1 = fr.res2(A[1], lam2) if y1 == lam2 else (0, 0)
        a0 = fr.res2(A[0], 2 * lam2)
        if use_twist and lam2 % 2 == 1:
            a0t = fr.F.mul(a0, fr.F.inv(fr.s))          # the S1 cocycle
        else:
            a0t = a0
        rts = fr.F.quad_roots(a1, a0t)
        if not rts:
            return (((2, 4),), refs, False, (y0, y1))
        if len(rts) == 2:
            return (((2, 2), (2, 2)), refs, False, (y0, y1))
        # repeated root: alpha-refine (LEMMAS HE7-12/HE7-13)
        s2 = rts[0]
        if s2 == (0, 0):
            viol('refine residue 0', {})
            return None
        w = fr.lift2(lam2, s2)
        # P4 slot geometry: w's slot-min exactly lam2 > T2
        svw = fr.slots2(w)
        if min(v for _, v in svw) != lam2 or lam2 <= fr.T2:
            viol('refine slot geometry', {'sv': svw, 'lam2': lam2})
        if lam2 <= last_lam2:
            viol('HE7-13 slope not increasing', {'lam2': lam2,
                                                 'last': last_lam2})
        last_lam2 = lam2
        Psi = padd(Psi, pneg(w))
        refs += 1
        if refs > max_ref:
            viol('refine bound hit', {})
            return None


# ---------------- PARI oracle (global factor + nfinit/idealprimedec)
def pari_sigma(f, p):
    fx = pari('+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f) if c))
    fac = pari.factor(fx)
    out = []
    for i in range(int(pari.matsize(fac)[0])):
        F, mult = fac[i, 0], int(fac[i, 1])
        if int(pari.poldegree(F)) < 1:
            continue
        if mult != 1:
            raise RuntimeError('repeated global factor')
        K = pari.nfinit(F)
        for pr in pari.idealprimedec(K, p):
            out.append((int(pr[2]), int(pr[3])))
    return tuple(sorted(out))


def disc_nonzero(f):
    fx = pari('+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f) if c))
    return int(pari.poldisc(fx) != 0)


# ---------------- member construction (slot-built + noise above the line)
def build_A(fr, base_k, base_g, rng, extra=2):
    """A = lift2(base_k, base_g) + noise at heights base_k+1..base_k+3;
    if base_g == 0, noise only (heights base_k+1..)."""
    A = fr.lift2(base_k, base_g) if base_g != (0, 0) else []
    for _ in range(extra):
        k = base_k + 1 + rng.randrange(3)
        g = (rng.randrange(fr.p), rng.randrange(fr.p))
        if g != (0, 0):
            A = padd(A, fr.lift2(k, g))
    return A


def gen_members(fr, rng):
    """yield (tag, f) over the six genres."""
    F, u = fr.F, fr.u
    T2 = fr.T2
    for parity_h in (1, 3):                        # G-frac: y0 = 4u+1, 4u+3
        y0 = 4 * u + parity_h
        a0 = (rng.randrange(fr.p), rng.randrange(fr.p))
        while a0 == (0, 0):
            a0 = (rng.randrange(fr.p), rng.randrange(fr.p))
        A0 = build_A(fr, y0, a0, rng)
        A1 = build_A(fr, (y0 + 3) // 2, (0, 0), rng)   # strictly above
        yield 'frac', padd(padd(pmul(fr.Psi0, fr.Psi0), pmul(A1, fr.Psi0)),
                           A0)
    for lam2 in (T2 + 1, T2 + 2):                  # G-int: split/inert/rep
        tw = fr.F.inv(fr.s) if lam2 % 2 == 1 else (1, 0)
        twi = F.inv(tw)
        # split: two distinct roots
        z1 = rng.choice([z for z in F.els if z != (0, 0)])
        z2 = rng.choice([z for z in F.els if z not in ((0, 0), z1,
                                                       F.neg(z1))])
        for kind, (r1, r2) in (('split', (z1, z2)), ('rep', (z1, z1))):
            a1 = F.neg(F.add(r1, r2))
            a0t = F.mul(r1, r2)
            a0 = F.mul(a0t, twi)                   # un-twist for the build
            A1 = build_A(fr, lam2, a1, rng) if a1 != (0, 0) else \
                build_A(fr, lam2 + 1, (0, 0), rng, extra=3)
            A0 = build_A(fr, 2 * lam2, a0, rng)
            yield 'int-' + kind, padd(padd(pmul(fr.Psi0, fr.Psi0),
                                           pmul(A1, fr.Psi0)), A0)
        # inert: random until irreducible
        while True:
            a1 = (rng.randrange(fr.p), rng.randrange(fr.p))
            a0t = (rng.randrange(fr.p), rng.randrange(fr.p))
            if a0t != (0, 0) and not F.quad_roots(a1, a0t):
                break
        a0 = F.mul(a0t, twi)
        A1 = build_A(fr, lam2, a1, rng) if a1 != (0, 0) else \
            build_A(fr, lam2 + 1, (0, 0), rng, extra=3)
        A0 = build_A(fr, 2 * lam2, a0, rng)
        yield 'int-inert', padd(padd(pmul(fr.Psi0, fr.Psi0),
                                     pmul(A1, fr.Psi0)), A0)
    # G-2sides: pins (0, y0), (1, y1) with T2 < y1 < y0 - y1
    y1 = T2 + 1 + rng.randrange(2)
    y0 = 2 * y1 + 1 + rng.randrange(2)
    g1 = (rng.randrange(1, fr.p), rng.randrange(fr.p))
    g0 = (rng.randrange(1, fr.p), rng.randrange(fr.p))
    A1 = build_A(fr, y1, g1, rng)
    A0 = build_A(fr, y0, g0, rng)
    yield '2sides', padd(padd(pmul(fr.Psi0, fr.Psi0), pmul(A1, fr.Psi0)),
                         A0)
    # G-peel: A0 = 0 exactly
    g1 = (rng.randrange(1, fr.p), rng.randrange(fr.p))
    A1 = build_A(fr, T2 + 1 + rng.randrange(2), g1, rng)
    yield 'peel', padd(pmul(fr.Psi0, fr.Psi0), pmul(A1, fr.Psi0))


def s_values(p, F, rng):
    if p == 3:
        return [z for z in F.els if z != (0, 0)]        # all 8
    zs = [z for z in F.els if z != (0, 0)]
    rng.shuffle(zs)
    keep = zs[:10]
    for spec in ((1, 0), (0, 1), (2, 1)):               # ensure key shapes
        if spec not in keep:
            keep.append(spec)
    return keep


def main():
    t0 = time.time()
    rng = random.Random(20260809)
    print('HE7 passPE3 fresh route: f1 = 2 / e1 = 1 constructed family')
    tw_flips = tw_caught = lazy_caught = lazy_diff = 0
    proper_s = 0
    for p in (3, 5):
        for u in (5, 7):
            row = {'p': p, 'u': u, 'members': 0, 'agree': 0,
                   'genres': {}, 'refines': 0, 'peels': 0}
            Fq = F2(p)
            for s in s_values(p, Fq, rng):
                fr = Frame(p, u, s)
                # frame check: Psi's occupied slots all exactly at T2
                if any(v != fr.T2 for _, v in fr.slots2(fr.Psi0, 3)):
                    viol('Psi slot geometry', {'p': p, 'u': u})
                for seed in range(2):
                    for tag, f in gen_members(fr, rng):
                        if not disc_nonzero(f):
                            note('disc0-discard')
                            continue
                        if not read_level1(fr, f):
                            viol('P2 level-1 boxed-node check', {
                                'p': p, 'u': u, 's': s, 'tag': tag})
                            continue
                        note('P2-level1-ok')
                        got = read_level2(fr, f)
                        if got is None:
                            continue
                        sig, refs, peeled, tr = got
                        row['members'] += 1
                        row['genres'][tag] = row['genres'].get(tag, 0) + 1
                        row['refines'] += (refs > 0)
                        row['peels'] += peeled
                        if s[1] != 0:
                            proper_s += 1
                        gs = pari_sigma(f, p)
                        if gs == sig:
                            row['agree'] += 1
                        else:
                            viol('P1 sigma mismatch', {
                                'p': p, 'u': u, 's': s, 'tag': tag,
                                'read': sig, 'pari': gs})
                        RES['genres'][str(sig)] = \
                            RES['genres'].get(str(sig), 0) + 1
                        # tooth P5: untwisted read
                        got_u = read_level2(fr, f, use_twist=False)
                        if got_u is not None and got_u[0] != sig:
                            tw_flips += 1
                            if got_u[0] != gs:
                                tw_caught += 1
                        # tooth P6: lazy dictionary at refine members
                        if refs > 0:
                            lazy = ((2, 2), (2, 2))
                            if lazy != sig:
                                lazy_diff += 1
                                if lazy != gs:
                                    lazy_caught += 1
            print('row p=%d u=%d: members %d agree %d refines %d peels %d '
                  '%s' % (p, u, row['members'], row['agree'],
                          row['refines'], row['peels'], row['genres']))
            RES['rows'].append(row)
    RES['teeth'] = {'twist-flips': tw_flips, 'twist-caught': tw_caught,
                    'lazy-diff': lazy_diff, 'lazy-caught': lazy_caught,
                    'proper-s-members': proper_s}
    RES['secs'] = round(time.time() - t0, 1)
    tot = sum(r['members'] for r in RES['rows'])
    agr = sum(r['agree'] for r in RES['rows'])
    print('TOTAL members %d, PARI agree %d, violations %d, teeth %s, '
          '%.1fs' % (tot, agr, len(RES['viol']), RES['teeth'],
                     RES['secs']))
    print('genre alphabet:', RES['genres'])
    verdict = 'GREEN' if (not RES['viol'] and agr == tot and
                          tw_flips > 0 and tw_caught == tw_flips and
                          lazy_caught == lazy_diff and lazy_diff > 0) \
        else 'RED'
    print('VERDICT:', verdict)
    RES['verdict'] = verdict
    with open(os.path.join(HERE, 'he7_pe3_fresh_results.json'), 'w') as fh:
        json.dump(RES, fh, indent=1, sort_keys=True)
    return 0 if verdict == 'GREEN' else 1


if __name__ == '__main__':
    sys.exit(main())
