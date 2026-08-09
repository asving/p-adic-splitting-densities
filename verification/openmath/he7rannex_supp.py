"""HE7 ANNEX R supplementary leg (additive; every sealed artifact
byte-frozen) — the FIRST machine contact of the level >= 3 region
anywhere in the program, at the corrected normalizer chain of
ANNEX-DEF HE7-2' (CODEX HE7RAT F1's repair).

FRAME = the sealed battery's (2,1,1): Phi' = x^2 - p, varpi = x,
K = K2 = F_p, l = 2, d_r = 1, u = 5 (lam = 5/2), D'' = 4, T2 = 10.
ONE constructed n = 16 family where LEVEL 3 ACTUALLY FIRES, by the
ladder mu = 8 -> mu2 = 4 -> mu3 = 2:
  level-1 node: single side lam = 5/2, residual (Z - s)^4 (mult 4);
  level-2 node: single side lam2 = u2/2 (u2 odd, > T2*l2... slope
    > T2 = 10, u2 in {21, 23}), residual (Z - s2)^2 with l2 = 2 —
    repeated with l2*deg r2 = 2 >= 2: THE JUMP GATE of THEOREM
    HE7.A(3), passing to level 3 (NOT an alpha-refine);
  level-3 problem: key Psi2 := Psi^2 - lift2(u2, s2) (DEFINITION
    HE7-3's key one level up, monic deg 8), mu3 = 2, K3 = K2 = F_p
    (g2 = 1), T3 = 2*u2, w3 = 2*dv2; members f := Psi2^2 + A1*Psi2
    + A0 with A_j prescribed n3-monomial lifts + small above-pin
    noise; the level-3 polygon decided by the mu2 = 2 dictionary one
    level up ((16,1) at l3 = 2; two classes / inert quadratic at
    l3 = 1 separable; level-3 alpha-refine at (Z-c)^2).

THE CORRECTED HE7-2' CHAIN UNDER TEST. n3(k) := n2(m2(k))*Psi^{s2(k)}
with l2*m2 + s2*u2 = k, 0 <= s2 < 2 — every n3(k) a Laurent monomial
x^alpha * Phi'^sigma * Psi^{s2}. The level-3 residual assembly carries
the tau3-cocycle of ANNEX-LEMMA R1-a: the slot-t twist unit
theta_t = n3(y_j)*n3(u3)^t/n3(y0) is a monomial in BOTH letters
Lam2 = Psi^2/n2(u2) (residue s2) and Lam1 = Phi'^2/x^5 (residue s),
computed here by exact exponent-vector arithmetic (V(k) below) and
applied as the multiplier s2^{a2} * s^{a1}. At level 2 the same
formula degenerates to the sealed reader's single-letter s^{c_j}
(a2-component absent) — R1-a(iv). Within-class deep twists
(vartheta_t, t >= 1) are INVISIBLE at this family's g2 = 1 (single
slot per class); DISCLOSED — exercising vartheta needs d_{r2} >= 2
(K3 = F_{p^2}), not constructed here.

PREREGISTERED PREDICTIONS (sealed pre-run).
  P1  the ladder fires as constructed, READ FORWARD from f (not
      assumed): level-1 single side 5/2 residual == (Z-s)^4; level-2
      single side u2/2 residual == (Z-s2)^2 (assembled with the
      sealed twist convention); level-3 reached with mu3 = 2 and
      every level-3 slope > T3 = 2*u2.
  P2  sigma (level-3 read via the corrected chain) == PARI
      factorpadic-equivalent oracle, member by member, sum ef = 16.
  P3  TOOTH (BADTWIST one level up): dropping the DEEP letter from
      the level-3 assembly (multiplier s2^{a2} only, a1 component
      dropped — what a single-letter reading of the broken DEF HE7-2
      would compute) CHANGES at least one member's sigma across the
      family (all members carry live level-1 twist s in {2, 3}).
  P4  level-3 alpha-refine chains, where they fire, strictly
      increase the refined-at slope (floor discipline), and NO
      level-4 node appears (impossible at mu3 = 2: a repeated factor
      with l3*d >= 2 needs side length >= 4).
BUDGET: 10-member smoke, then the full grid (~40 members) detached.
Oracle = the ANNEX F-1 leg's deg-16 pari route (nfinit p-maximal
hint; both-oracle cross-check on the smoke member).  Members are
Z_p only (char-p rows have no oracle at this degree) — DISCLOSED.

SMOKE RECORD (disclosed, pre-seal instrument history): smoke 1
(kinds K1/K2/K3, u2 = 21 only) — 10 members GREEN, PARI 10/10,
3 naive flips, 0 refines (no repeated level-3 residual appeared);
kind K2R (forced (Z-c)^2 via inverse-twisted targets) and u2 = 23
then ADDED so P4 is exercised; smoke 2 — 10 members GREEN, PARI
10/10, 2 refines.  No reader/twist logic changed between the smokes
and the sealed run; the only edits were the K2R builder and the grid.
"""
import sys
import os
import json
import time
import random

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from he7_pe3_probe12 import (Fr12, padd, pneg, pmul, pdivmod,
                             development, vp, gcdi, disc_nonzero, BIG)
import he7_pe3_probe12 as probe_mod
from he7annex_supp import pari_sigma16, fp_monic

pari = probe_mod.pari

RES = {'rows': [], 'checks': {}, 'viol': [], 'secs': 0}


def viol(what, detail):
    RES['viol'].append({'what': what, 'detail': str(detail)[:300]})
    print('  !! VIOLATION %s %s' % (what, str(detail)[:200]))


def note(k, n=1):
    RES['checks'][k] = RES['checks'].get(k, 0) + n


def fp_factor2(c, p):
    """factor a poly of degree <= 2 over F_p (coeff list low-first):
    dict {monic factor tuple: mult}."""
    c = list(fp_monic(c, p))
    d = len(c) - 1
    if d == 1:
        return {tuple(c): 1}
    assert d == 2
    roots = [z for z in range(p)
             if (c[0] + c[1] * z + z * z) % p == 0]
    if not roots:
        return {tuple(c): 1}
    if len(roots) == 1:
        return {((-roots[0]) % p, 1): 2}
    return {((-roots[0]) % p, 1): 1, ((-roots[1]) % p, 1): 1}


class Fr3:
    """level-3 kit on top of Fr12, at a fixed level-2 node (u2, s2)."""

    def __init__(self, fr, u2, s2):
        assert u2 % 2 == 1 and u2 > 2 * fr.T2  # gcd(u2,2)=1; slope>T2
        self.fr, self.p, self.s = fr, fr.p, fr.s
        self.u2, self.s2 = u2, s2
        self.T3 = 2 * u2
        self.Psi = list(fr.Psi0)
        self.key0 = padd(pmul(self.Psi, self.Psi),
                         pneg(fr.lift2(u2, s2)))   # Psi^2 - W2, deg 8

    # ---- corrected HE7-2' normalizer bookkeeping -------------------
    def m2(self, k):
        return (k - (k % 2) * self.u2) // 2

    def V(self, k):
        """exponent vector of n3(k) = x^alpha Phi'^sigma Psi^{s2c}."""
        s2c = k % 2
        m2 = self.m2(k)
        sig = m2 % 2                      # u = 5 odd: s1(m) = m mod 2
        alp = (m2 - 5 * sig) // 2
        # dv3-value identity: 4*alp + 10*sig + u2*s2c == k
        assert 4 * alp + 10 * sig + self.u2 * s2c == k
        return (alp, sig, s2c)

    def twist3(self, yj, t, u3, y0):
        """residue of theta_t = n3(yj) n3(u3)^t / n3(y0) as the letter
        monomial Lam2^{a2} Lam1^{a1} (ANNEX-LEMMA R1-a(iii));
        returns multiplier s2^{a2} s^{a1} mod p, or None on parity
        failure (theory says impossible; checked)."""
        E = [a + t * b - c for a, b, c
             in zip(self.V(yj), self.V(u3), self.V(y0))]
        if E[2] % 2:
            return None
        a2 = E[2] // 2
        # remove Lam2^{a2} = (Psi^2 x^{-p1} Phi'^{-p2})^{a2},
        # p2 = u2 mod 2 = 1, p1 = (u2 - 5)/2
        Esig = E[1] + a2 * 1
        if Esig % 2:
            return None
        a1 = Esig // 2
        m = (pow(self.s2, a2 % (self.p - 1), self.p) *
             pow(self.s, a1 % (self.p - 1), self.p)) % self.p
        return m, a2, a1

    # ---- level-3 slot algebra --------------------------------------
    def dv3(self, A):
        if not A:
            return BIG
        cs = development(A, self.Psi, 2)
        return min(2 * (self.fr.dv2(c) if c else BIG) + t * self.u2
                   for t, c in enumerate(cs))

    def res3(self, A, k):
        s2c = k % 2
        cs = development(A, self.Psi, 2)
        oth = 1 - s2c
        vo = 2 * (self.fr.dv2(cs[oth]) if cs[oth] else BIG) \
            + oth * self.u2
        if vo <= k:
            viol('res3 cross-class tie', {'k': k})
        return self.fr.res2(cs[s2c], self.m2(k)) if cs[s2c] else 0

    def lift3(self, k, g):
        s2c = k % 2
        c = self.fr.lift2(self.m2(k), g % self.p)
        return pmul(c, self.Psi) if s2c else c


# ---------- generic polygon (pins low-first, integer heights)

def hull_of(pins):
    hull = [pins[0]]
    for pt in pins[1:]:
        while len(hull) >= 2 and \
            (hull[-1][1] - hull[-2][1]) * (pt[0] - hull[-1][0]) >= \
                (pt[1] - hull[-1][1]) * (hull[-1][0] - hull[-2][0]):
            hull.pop()
        hull.append(pt)
    return hull


# ---------- the forward ladder read (P1) ---------------------------

def read_level1(fr, f):
    """f's Phi'-polygon: expect single side 5/2, residual (Z-s)^4."""
    p = fr.p
    A = development(f, fr.Phi, 9)
    ys = [fr.dv1(a) if a else BIG for a in A[:8]] + [0]
    pins = [(j, ys[j]) for j in range(9) if ys[j] < BIG]
    h = hull_of(pins)
    if len(h) != 2 or h[0] != (0, 20) or h[1] != (8, 0):
        return None
    # level 1 is twist-free (n1 = varpi-powers): slots j = 2t
    csr = []
    for t in range(5):
        y = 20 - 5 * t
        csr.append(fr.res1(A[2 * t], y)
                   if ys[2 * t] == y else 0)
    want = fp_monic([pow((-fr.s) % p, 4 - t, p) *
                     [1, 4, 6, 4, 1][t] % p for t in range(5)], p)
    return fp_monic(csr, p) == want


def read_level2(fr, f, u2, s2):
    """f's Psi-polygon: expect single side u2/2, residual (Z-s2)^2
    (assembled with the sealed reader's twist convention)."""
    p = fr.p
    A = development(f, fr.Psi0, 5)
    ys = [fr.dv2(a) if a else BIG for a in A[:4]] + [0]
    if ys[0] >= BIG:
        return 'peel'
    pins = [(j, ys[j]) for j in range(5) if ys[j] < BIG]
    h = hull_of(pins)
    if len(h) != 2 or h[0] != (0, 2 * u2) or h[1] != (4, 0):
        return 'shape'
    csr = []
    for t in range(3):
        j, y = 2 * t, 2 * u2 - t * u2
        raw = fr.res2(A[j], y) if (j < 4 and ys[j] == y) else \
            (1 if j == 4 else 0)
        dl = (y % 2) + t * (u2 % 2) - ((2 * u2) % 2)
        if dl % 2:
            return 'parity'
        csr.append((raw * pow(fr.s, (dl // 2) % (p - 1), p)) % p)
    want = fp_monic([(s2 * s2) % p, (-2 * s2) % p, 1], p)
    return 'ok' if fp_monic(csr, p) == want else 'res'


def sides3(f3, g, key):
    """level-3 polygon of g at key (mu3 slots); returns
    ('ok', sides) / ('peel',) / error strings.  Each side dict:
    l3, u3(num/den lowest), L, cs (twisted, monic), cs_naive
    (deep letter dropped, monic) — the P3 comparison column."""
    p = f3.p
    mu3 = (len(g) - 1) // 8
    A = development(g, key, mu3 + 1)
    ys = [f3.dv3(a) for a in A[:mu3]] + [0]
    if ys[0] >= BIG:
        return ('peel', None)
    pins = [(j, ys[j]) for j in range(mu3 + 1) if ys[j] < BIG]
    h = hull_of(pins)
    sides = []
    for i in range(len(h) - 1):
        (j0, y0), (j1, y1) = h[i], h[i + 1]
        L = j1 - j0
        num, den = y0 - y1, L
        gg = gcdi(num, den)
        u3, l3 = num // gg, den // gg
        if num <= f3.T3 * den:
            return ('badslope', None)
        cs, csn = [], []
        for t in range(L // l3 + 1):
            j = j0 + l3 * t
            y = y0 - t * u3
            raw = f3.res3(A[j], y) if j < mu3 else \
                (1 if y == 0 else 0)
            if (ys[j] if j < mu3 else 0) != y:
                raw = 0
            tw = f3.twist3(y, t, u3, y0)
            if tw is None:
                return ('twistparity3', None)
            m, a2, a1 = tw
            if a1:
                note('deep-letter-fired')
            cs.append((raw * m) % p)
            csn.append((raw * pow(f3.s2, a2 % (p - 1), p)) % p)
        if cs[0] == 0 or cs[-1] == 0:
            return ('endpoint0', None)
        sides.append({'j0': j0, 'L': L, 'u3': u3, 'l3': l3,
                      'cs': fp_monic(cs, p),
                      'cs_naive': fp_monic(csn, p)})
    return ('ok', sides)


def read_level3(f3, f, naive_twist=False, cap=12):
    """the level-3 read at the corrected chain; returns
    (letters, nref, maxdepth) or an error string.  naive_twist=True
    swaps cs -> cs_naive (the P3 tooth reader)."""
    p = f3.p
    key = list(f3.key0)
    g = list(f)
    letters = []
    floor = f3.T3
    nref = 0
    while True:
        st, sides = sides3(f3, g, key)
        if st == 'peel':
            q, r = pdivmod(g, key)
            if r:
                return 'peelfail'
            letters.append((8, 1))       # HE6R1-3 one level up
            note('peel3')
            g = q
            if len(g) == 1:
                return (letters, nref, 0)
            continue
        if st != 'ok':
            return st
        refine = None
        for S in sides:
            col = S['cs_naive'] if naive_twist else S['cs']
            fac = fp_factor2(col, p)
            for poly, m in sorted(fac.items()):
                d = len(poly) - 1
                if m == 1:
                    letters.append((8 * S['l3'], d))
                elif d == 1 and S['l3'] == 1:
                    lam = S['u3']
                    if lam <= floor:
                        return 'floorfail'
                    if refine is not None:
                        return 'tworefines'
                    refine = (lam, (-poly[0]) % p)
                else:
                    note('L4-node')
                    return 'L4'
        if refine is None:
            return (letters, nref, 0)
        nref += 1
        if nref > cap:
            return 'refcap'
        lam, root = refine
        w = f3.lift3(lam, root)
        if f3.dv3(w) != lam or f3.res3(w, lam) != root:
            return 'lift3contract'
        key = padd(key, pneg(w))
        floor = lam
        note('refine3')


# ---------- member construction ------------------------------------

def build_member(f3, kind, rng):
    """f = Psi2^2 + A1 Psi2 + A0 with the level-3 pins prescribed;
    small noise strictly above every pin."""
    p, u2 = f3.p, f3.u2
    key = f3.key0
    if kind == 'K1':                     # single side, l3 = 2
        u3 = 4 * u2 + rng.choice([1, 3])
        A0 = f3.lift3(u3, rng.randrange(1, p))
        A1 = []
    elif kind == 'K2':                   # single side, l3 = 1
        lam = 2 * u2 + rng.choice([2, 4])
        A0 = f3.lift3(2 * lam, rng.randrange(1, p))
        A1 = f3.lift3(lam, rng.randrange(1, p)) \
            if rng.randrange(3) else []
    elif kind == 'K2R':                  # forced (Z-c)^2: the level-3
        lam = 2 * u2 + rng.choice([2, 4])  # alpha-refine (P4), built
        c = rng.randrange(1, p)            # by INVERSE-twisting the
        tws = [f3.twist3(2 * lam - t * lam, t, lam, 2 * lam)[0]
               for t in range(3)]          # target (R1-c mechanism)
        inv = lambda x: pow(x, p - 2, p)
        raw1 = ((-2 * c) % p) * tws[2] % p * inv(tws[1]) % p
        raw0 = (c * c) % p * tws[2] % p * inv(tws[0]) % p
        A0 = f3.lift3(2 * lam, raw0)
        A1 = f3.lift3(lam, raw1)
    else:                                # K3: two sides
        la = 2 * u2 + rng.choice([1, 2])
        lb = la + 1 + rng.randrange(3)
        A1 = f3.lift3(la, rng.randrange(1, p))
        A0 = f3.lift3(la + lb, rng.randrange(1, p))
    for _ in range(2):                   # noise above the pins
        gg = rng.randrange(p)
        if gg:
            base = f3.dv3(A0) if A0 else 4 * u2 + 4
            A0 = padd(A0, f3.lift3(base + 1 + rng.randrange(3), gg))
    f = padd(padd(pmul(key, key), pmul(A1, key)), A0)
    return f, A0, A1


def process(fr, f3, kind, rng, do_naive):
    p = f3.p
    f, A0, A1 = build_member(f3, kind, rng)
    if len(f) != 17:
        viol('degree', {'deg': len(f) - 1})
        return None
    if not disc_nonzero(f):
        note('disc0-discard')
        return None
    # P1: the ladder, read forward
    if not read_level1(fr, f):
        viol('P1 level-1 node', {'kind': kind})
        return None
    st2 = read_level2(fr, f, f3.u2, f3.s2)
    if st2 != 'ok':
        viol('P1 level-2 node ' + st2, {'kind': kind})
        return None
    note('P1-ladder')
    out = read_level3(f3, f)
    if isinstance(out, str):
        viol('level-3 read ' + out, {'kind': kind})
        return None
    letters, nref, _ = out
    sig = tuple(sorted(letters))
    if sum(e * fdeg for e, fdeg in sig) != 16:
        viol('sum ef != 16', {'sig': sig})
        return None
    # P2: oracle
    sig_pari = pari_sigma16(f, p)
    ok = (sig == sig_pari)
    if not ok:
        viol('P2 sigma mismatch', {'read': sig, 'pari': sig_pari,
                                   'kind': kind})
    else:
        note('P2-sigma-agree')
    # P3: the naive (deep-letter-dropped) reader
    flip = None
    if do_naive:
        outn = read_level3(f3, f, naive_twist=True)
        sign = tuple(sorted(outn[0])) if not isinstance(outn, str) \
            else ('ERR', outn)
        flip = (sign != sig)
        if flip:
            note('P3-naive-flip')
    return {'kind': kind, 'p': p, 's': fr.s, 'u2': f3.u2,
            's2': f3.s2, 'sigma': list(sig), 'pari_ok': ok,
            'nref': nref, 'naive_flip': flip}


def main(smoke=False):
    t0 = time.time()
    rng = random.Random(20260809)
    grid = []
    for p in (5, 7):
        for s in (2, 3):
            for u2 in (21, 23):
                for s2 in (1, 2):
                    grid.append((p, s, u2, s2))
    kinds = ['K1', 'K2', 'K2', 'K2R', 'K3']
    members = 0
    for (p, s, u2, s2) in grid:
        fr = Fr12(p, 5, s)
        f3 = Fr3(fr, u2, s2)
        for kind in kinds:
            rec = process(fr, f3, kind, rng, do_naive=True)
            if rec is None:
                continue
            RES['rows'].append(rec)
            members += 1
            if smoke and members >= 10:
                break
        if smoke and members >= 10:
            break
    RES['secs'] = round(time.time() - t0, 1)
    agree = sum(1 for r in RES['rows'] if r['pari_ok'])
    flips = sum(1 for r in RES['rows'] if r['naive_flip'])
    refs = sum(r['nref'] for r in RES['rows'])
    sigs = {}
    for r in RES['rows']:
        sigs[str(tuple(map(tuple, r['sigma'])))] = \
            sigs.get(str(tuple(map(tuple, r['sigma']))), 0) + 1
    RES['summary'] = {'members': members, 'pari_agree': agree,
                      'naive_flips': flips, 'refines3': refs,
                      'sigmas': sigs, 'violations': len(RES['viol'])}
    print(json.dumps(RES['summary'], indent=1))
    verdict = 'GREEN' if (not RES['viol'] and agree == members
                          and members > 0 and flips >= 1) else 'RED'
    print('VERDICT %s — %d members, PARI %d/%d, naive flips %d, '
          'level-3 refines %d, %.1f s'
          % (verdict, members, agree, members, flips, refs,
             RES['secs']))
    RES['verdict'] = verdict
    if not smoke:
        base = os.path.join(HERE, 'he7rannex_supp')
        with open(base + '_results.json', 'w') as fh:
            json.dump(RES, fh, indent=1)
    return verdict


if __name__ == '__main__':
    main(smoke=('--smoke' in sys.argv))
