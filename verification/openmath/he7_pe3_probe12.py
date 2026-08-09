"""HE7 passPE3 PROBE LEG 2 — the MIXED-RESIDUAL refine seam at mu2 = 3
(n = 12), the configuration this pass's finding names: a single integer-
slope level-2 side whose residual is (Z-a)^2 (Z-b), a != b (repeated PLUS
simple factor), where LEMMA HE7-13/HE7-8's displayed hypotheses (pure
power (Z-s2)^{mu2}) do not literally apply and S6(iii)'s block sentence
names only "several distinct REPEATED factors".  Also the FIRST machine
contact of any refine at mu2 = 3 (PE1's n = 12 family skipped refines),
including PURE (Z-a)^3 nodes (LEMMA HE7-13's hypothesis genuinely at
mu2 = 3) and post-refine 2-step chains.

FRAME = the sealed battery's: (e1,f1,h) = (2,1,1), Phi' = x^2 - p,
varpi = x, K = K2 = F_p, l = 2, d_r = 1, u = 5 (lam = 5/2), D'' = 4,
T2 = 10, deg f = 12, mu2 = 3, p in {5, 7}, s in {1, 2}.
f = Psi^3 + A2 Psi^2 + A1 Psi + A0, single side of slope lam2 in
{11, 12} with prescribed cubic residual (twist exponents c_j =
(s(y_j) + t s(u2) - s(y_{j0}))/2 hand-derived from the S1 cocycle and
validated against PARI end-to-end).

CONTINUATION ROUTE UNDER TEST (derived, not displayed in the note):
refine at the STEEPEST side carrying a repeated linear factor (top-first
order, so lower sides are untouched: dv2(w) = lam2_side exceeds every
lower side's root value), re-read the whole f at the refined key, loop;
simple factors decided by THEOREM HE7.A(2) at the current key (licensed
by LEMMA HE7-12(c)); peel when the key divides.  PREDICTIONS: sigma ==
PARI member by member; every refine strictly increases the touched
slope; chains terminate; letters have e = 4*l2, f = deg r2, sum ef = 12.
SMOKE (disclosed): one mixed member (5,5,lam2=11,s=1,a=1,b=2) end-to-end
before the batch.
"""
import sys
import os
import json
import time
import random
sys.path.insert(0, '/data/users/asvin/.local/lib/python3.10/site-packages')
import cypari2
pari = cypari2.Pari()
pari.allocatemem(1 << 30)

HERE = os.path.dirname(os.path.abspath(__file__))
BIG = 10 ** 9
RES = {'rows': [], 'checks': {}, 'viol': [], 'genres': {}, 'secs': 0}


def viol(what, detail):
    RES['viol'].append({'what': what, 'detail': str(detail)[:300]})
    print('  !! VIOLATION %s %s' % (what, str(detail)[:200]))


def note(k, n=1):
    RES['checks'][k] = RES['checks'].get(k, 0) + n


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


def gcdi(a, b):
    while b:
        a, b = b, a % b
    return a


class Fr12:
    """(2,1,1) frame: Phi' = x^2 - p, varpi = x, dv = 2v-graded slot-min."""

    def __init__(self, p, u, s):
        self.p, self.u, self.s = p, u, s
        self.Phi = [-p, 0, 1]
        self.T2 = 2 * u
        # B0: dv = u (odd), residue -s: [0, (-s % p) * p^((u-1)/2)]
        self.Psi0 = padd(pmul(self.Phi, self.Phi),
                         self.lift1(u, (-s) % p))

    def lift1(self, m, g):
        if g % self.p == 0:
            return []
        if m % 2 == 0:
            return [g * self.p ** (m // 2)]
        return [0, g * self.p ** ((m - 1) // 2)]

    def dv1(self, c):
        if not c:
            return BIG
        b0 = c[0] if len(c) > 0 else 0
        b1 = c[1] if len(c) > 1 else 0
        return min(2 * vp(b0, self.p), 2 * vp(b1, self.p) + 1)

    def res1(self, c, m):
        b0 = c[0] if len(c) > 0 else 0
        b1 = c[1] if len(c) > 1 else 0
        if m % 2 == 0:
            return (b0 // self.p ** (m // 2)) % self.p \
                if 2 * vp(b0, self.p) == m else 0
        return (b1 // self.p ** ((m - 1) // 2)) % self.p \
            if 2 * vp(b1, self.p) + 1 == m else 0

    def dv2(self, C):
        cs = development(C, self.Phi, 2)
        return min(2 * self.dv1(cs[t]) + t * self.u for t in range(2))

    def res2(self, C, k):
        s0 = k % 2
        cs = development(C, self.Phi, 2)
        oth = 1 - s0
        if 2 * self.dv1(cs[oth]) + oth * self.u <= k:
            viol('res2 cross-class tie', {'k': k})
        m0 = (k - s0 * self.u) // 2      # l*m0 + s0*u = k, l = 2
        return self.res1(cs[s0], m0)

    def lift2(self, k, g):
        s0 = k % 2
        c = self.lift1((k - s0 * self.u) // 2, g % self.p)
        return pmul(c, self.Phi) if s0 else c


def fp_factor_roots(coeffs, p):
    """factor a monic poly (deg<=3, coeff list low-first, mod p) over F_p:
    returns (list of (root, mult), leftover irreducible part degree)."""
    c = [x % p for x in coeffs]
    roots = []
    while len(c) > 1:
        r = next((z for z in range(p)
                  if sum(cc * pow(z, i, p) for i, cc in enumerate(c)) % p
                  == 0), None)
        if r is None:
            break
        # synthetic division by (Z - r)
        out = [0] * (len(c) - 1)
        acc = 0
        for i in range(len(c) - 1, 0, -1):
            acc = (acc * r + c[i]) % p
            out[i - 1] = acc
        c = out
        roots.append(r)
    from collections import Counter
    return Counter(roots), len(c) - 1


def read12(fr, f, max_ref=60):
    """the derived continuation route on the whole f; returns
    (sigma, nref, npeel, mixed_nodes, chainlens) or None."""
    p, u = fr.p, fr.u
    Psi = list(fr.Psi0)
    W_so_far = []
    nref = npeel = mixed = 0
    slopes_hit = []
    for _ in range(max_ref + 1):
        # development of f in the current key, mu slots
        g = list(f)
        sigma = []
        # peel loop: strip key factors first
        A = development(g, Psi, len(g) // 4 + 1)
        mu = (len(g) - 1) // 4
        while fr_dv2A(fr, A[0]) >= BIG:
            q, r = pdivmod(g, Psi)
            if r:
                viol('peel division not exact', {})
                return None
            sigma.append((4, 1))
            npeel += 1
            g = q
            mu -= 1
            if mu == 0:
                break
            A = development(g, Psi, mu + 1)
        if mu == 0:
            return tuple(sorted(sigma)), nref, npeel, mixed, slopes_hit
        ys = [fr_dv2A(fr, A[j]) for j in range(mu)] + [0]
        # lower hull of (j, ys[j])
        pins = [(j, ys[j]) for j in range(mu + 1) if ys[j] < BIG]
        hull = [pins[0]]
        for pt in pins[1:]:
            while len(hull) >= 2 and \
                (hull[-1][1] - hull[-2][1]) * (pt[0] - hull[-1][0]) >= \
                    (pt[1] - hull[-1][1]) * (hull[-1][0] - hull[-2][0]):
                hull.pop()
            hull.append(pt)
        # sides left->right, slopes decreasing; find repeated-linear sides
        refine_at = None            # (slope, s2) at the STEEPEST such side
        decided = []
        for i in range(len(hull) - 1):
            (j0, y0), (j1, y1) = hull[i], hull[i + 1]
            L = j1 - j0
            num, den = y0 - y1, L
            gg = gcdi(num, den)
            u2, l2 = num // gg, den // gg
            if 2 * num <= fr.T2 * 2 * den:      # slope <= T2
                viol('slope <= T2', {'num': num, 'den': den})
                return None
            # residual over F_p with twist exponents
            cs = []
            for t in range(L // l2 + 1):
                j = j0 + l2 * t
                yj = y0 - t * u2
                if ys[j] if j < mu else 0 == yj:
                    pass
                raw = fr.res2(A[j], yj) if j < mu else \
                    (1 if yj == 0 else 0)
                if (ys[j] if j < mu else 0) != yj:
                    raw = 0
                dl = (yj % 2) + t * (u2 % 2) - (y0 % 2)
                if dl % 2 != 0:
                    viol('twist exponent parity', {})
                    return None
                cj = dl // 2
                cs.append((raw * pow(fr.s, cj % (p - 1) or (p - 1), p))
                          % p if raw else 0)
            if cs[-1] == 0:
                viol('side top residue 0', {})
                return None
            top_inv = pow(cs[-1], p - 2, p)
            cs = [(c * top_inv) % p for c in cs]
            rts, irr_deg = fp_factor_roots(cs, p)
            if any(m >= 2 for m in rts.values()):
                mixed_here = (len(rts) > 1 or irr_deg > 0)
                mixed += mixed_here
                s2 = max((m, z) for z, m in rts.items())[1]
                cand = (u2, l2, s2)
                if refine_at is None or \
                        u2 * refine_at[1] > refine_at[0] * l2:
                    refine_at = cand
                continue
            for z, m in rts.items():
                decided.append((4 * l2, 1))
            if irr_deg > 0:
                decided.append((4 * l2, irr_deg))
        if refine_at is None:
            return tuple(sorted(sigma + decided)), nref, npeel, mixed, \
                slopes_hit
        u2, l2, s2 = refine_at
        if l2 != 1:
            viol('repeated at fractional slope (level-3!)', {})
            return None
        lam2 = u2
        slopes_hit.append(lam2)
        w = fr.lift2(lam2, s2)
        if fr.dv2(w) != lam2 or fr.res2(w, lam2) != s2 % p:
            viol('lift2 contract', {'lam2': lam2})
            return None
        Psi = padd(Psi, pneg(w))
        nref += 1
    viol('refine bound hit', {})
    return None


def fr_dv2A(fr, A):
    return fr.dv2(A) if A else BIG


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


def build(fr, lam2, cres, rng, noise=2):
    """f = Psi^3 + sum A_j Psi^j with single side slope lam2, residual
    Z^3 + cres[2] Z^2 + cres[1] Z + cres[0] (target, twist-corrected)."""
    p = fr.p
    f = pmul(pmul(fr.Psi0, fr.Psi0), fr.Psi0)
    for j in range(3):
        yj = (3 - j) * lam2
        # twist: c_j = (s(y_j) + j*s(lam2) - s(3 lam2))/2 ; raw = c * s^{c3-cj}
        e_j = ((yj % 2) + j * (lam2 % 2) - ((3 * lam2) % 2)) // 2
        e_3 = ((0 % 2) + 3 * (lam2 % 2) - ((3 * lam2) % 2)) // 2
        raw = (cres[j] * pow(fr.s, (e_3 - e_j) % (p - 1) or (p - 1), p)) % p \
            if cres[j] % p else 0
        A = fr.lift2(yj, raw) if raw else []
        for _ in range(noise):
            k = yj + 1 + rng.randrange(3)
            gg = rng.randrange(p)
            if gg:
                A = padd(A, fr.lift2(k, gg))
        f = padd(f, pmul(A, [pw for pw in
                             (pmul(fr.Psi0, fr.Psi0) if j == 2 else
                              (fr.Psi0 if j == 1 else [1]))]))
    return f


def main():
    t0 = time.time()
    rng = random.Random(1208)
    print('HE7 passPE3 probe leg 2: mixed-residual refine at mu2 = 3, n=12')
    for p in (5, 7):
        for s in (1, 2):
            for lam2 in (11, 12):
                fr = Fr12(p, 5, s)
                row = {'p': p, 's': s, 'lam2': lam2, 'members': 0,
                       'agree': 0, 'mixed': 0, 'refs': {}, 'sig': {}}
                targets = []
                for a in (1, 2):
                    for b in (3, 4):
                        # mixed (Z-a)^2 (Z-b)
                        targets.append(('mixed',
                                        [(-a * a * b) % p,
                                         (a * a + 2 * a * b) % p,
                                         (-(2 * a + b)) % p]))
                    targets.append(('pure',
                                    [(-a ** 3) % p, (3 * a * a) % p,
                                     (-3 * a) % p]))
                for seed in range(3):
                    for kind, cres in targets:
                        f = build(fr, lam2, cres, rng)
                        if not disc_nonzero(f):
                            note('disc0-discard')
                            continue
                        got = read12(fr, f)
                        if got is None:
                            continue
                        sig, nref, npeel, mixed, slopes = got
                        if sum(e * ff for e, ff in sig) != 12:
                            viol('sum ef != 12', {'sig': sig})
                            continue
                        if slopes != sorted(slopes) or \
                                len(set(slopes)) != len(slopes):
                            viol('slopes not strictly increasing',
                                 {'slopes': slopes})
                        row['members'] += 1
                        row['mixed'] += (mixed > 0)
                        row['refs'][nref] = row['refs'].get(nref, 0) + 1
                        gs = pari_sigma(f, p)
                        if gs == sig:
                            row['agree'] += 1
                        else:
                            viol('sigma mismatch', {
                                'p': p, 's': s, 'lam2': lam2, 'kind': kind,
                                'read': sig, 'pari': gs})
                        row['sig'][str(sig)] = row['sig'].get(str(sig),
                                                              0) + 1
                        note('kind-' + kind)
                print('row p=%d s=%d lam2=%d: members %d agree %d '
                      'mixed %d refs %s sig %s' %
                      (p, s, lam2, row['members'], row['agree'],
                       row['mixed'], row['refs'], row['sig']))
                RES['rows'].append(row)
    RES['secs'] = round(time.time() - t0, 1)
    tot = sum(r['members'] for r in RES['rows'])
    agr = sum(r['agree'] for r in RES['rows'])
    mix = sum(r['mixed'] for r in RES['rows'])
    print('TOTAL %d members, %d agree, %d mixed-node members, checks %s, '
          'violations %d, %.1fs' % (tot, agr, mix, RES['checks'],
                                    len(RES['viol']), RES['secs']))
    verdict = 'GREEN' if not RES['viol'] and agr == tot and mix > 0 \
        else 'RED'
    print('VERDICT:', verdict)
    RES['verdict'] = verdict
    with open(os.path.join(HERE, 'he7_pe3_probe12_results.json'),
              'w') as fh:
        json.dump(RES, fh, indent=1, sort_keys=True)
    return 0 if verdict == 'GREEN' else 1


if __name__ == '__main__':
    sys.exit(main())
