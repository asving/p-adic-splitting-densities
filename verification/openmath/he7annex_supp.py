"""HE7 ANNEX F-1 supplementary leg (additive; every sealed artifact
byte-frozen) — machine contact for ANNEX-LEMMA HE7-13' at configurations
beyond the PE3 probe: TWO repeated classes at one side, and mu2 = 4
(n = 16) refines.

FRAME = the sealed battery's (2,1,1): Phi' = x^2 - p, varpi = x,
K = K2 = F_p, l = 2, d_r = 1, u = 5 (lam = 5/2), D'' = 4, T2 = 10;
deg f = 16, mu2 = 4; p in {5,7}, s in {1,2}, lam2 in {11,12}.
f = Psi^4 + sum_{j<4} A_j Psi^j, single side of slope lam2 with
prescribed quartic residual (twist exponents generalized from the
committed probe's mu2 = 3 formula; arithmetic primitives IMPORTED from
the committed he7_pe3_probe12.py so the level-1/level-2 kit is
byte-identical to the PE3 record).

CONFIGURATIONS.
  (A) R2 = (Z-a)^2 (Z-b)^2  — two repeated classes at ONE side (the
      first machine contact anywhere in the program);
  (B) R2 = (Z-a)^3 (Z-b)    — repeated class of multiplicity 3 plus a
      parked SIMPLE class (the R-a disposition: b's letter is emitted
      at the ORIGINAL key, before any refine);
  (C) R2 = (Z-a)^4          — pure controls (LEMMA HE7-13 as displayed).

CONTINUATION UNDER TEST = the annex wiring (per class, from the node's
OWN key): at any node, simple residual factors are decided at the
current key; each repeated K2-rational linear class is refined by its
own thread key' = key - w(lam, class-root) and its read recurses on the
sides STRICTLY ABOVE lam only (floor = lam) — clauses (c)/(d)/(e) of
ANNEX-LEMMA HE7-13' make this isolation exact (companions and lower
sides park at their values; dragged steeper material parks AT lam).

PREREGISTERED PREDICTIONS (sealed pre-run; annex commit 1 = a4a91ee).
  P1  sigma == PARI member by member (configs A, B, C), sum ef = 16.
  P2  clause (c) exactness: at each depth-1 thread entry the lam2 side
      PERSISTS with the translated residual EXACTLY — config A, thread
      c0 with companion c1: monic (Z-(c1-c0))^2, length 2; config B,
      thread a: (Z-(b-a)), length 1, at EVERY a-chain key.
  P3  per-thread refined-at slopes strictly increase (recursion floor;
      LEMMA HE7-13 at the pure sub-nodes).
  P4  TOOTH (the naive route is REFUTED): the single-key sequential
      route (the PE3 probe's own selection rule) FAILS on every
      config-A member — refine cap hit with the lam2 slope revisited
      (the clause-(e) drag cycle).
  P5  TOOTH (the mixed/pure boundary): on config-C controls the lam2
      side does NOT survive the first refine (every post-refine slope
      > lam2) — while on configs A/B it ALWAYS survives.
Level-3 sub-nodes (repeated non-linear factor at a block) are expected
NEVER (configs A/B: block mu2 <= 3 makes them impossible; config C:
possible in principle at a deg-4 sub-residual) — any occurrence is
counted, skipped for P1, and disclosed.

SMOKE (disclosed): one config-A member (p=5, s=1, lam2=11, a=1, b=2)
end-to-end before the batch, plus a 2-member PARI timing probe at
deg 16.  Instrument note (pre-run, disclosed): the sigma oracle is the
probe's global factor + idealprimedec route, but with
nfinit([F, [p]]) — the order certified maximal AT p, which is all
idealprimedec(., p) consults — because a full deg-16 nfinit must factor
a ~100-digit discriminant and stalls; the smoke member was scored by
BOTH oracles (identical sigma) before the switch.
"""
import sys
import os
import json
import time
import random

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from he7_pe3_probe12 import (Fr12, padd, pneg, pmul, pdivmod, trim,
                             development, vp, gcdi, pari_sigma,
                             disc_nonzero, BIG)

RES = {'rows': [], 'checks': {}, 'viol': [], 'secs': 0}

import he7_pe3_probe12 as probe_mod
pari = probe_mod.pari


def pari_sigma16(f, p):
    """probe's pari_sigma with the nfinit p-maximal hint (see the
    docstring's instrument note)."""
    fx = pari('+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f)
                       if c))
    fac = pari.factor(fx)
    out = []
    for i in range(int(pari.matsize(fac)[0])):
        F, mult = fac[i, 0], int(fac[i, 1])
        if int(pari.poldegree(F)) < 1:
            continue
        if mult != 1:
            raise RuntimeError('repeated global factor')
        K = pari.nfinit([F, [p]])
        for pr in pari.idealprimedec(K, p):
            out.append((int(pr[2]), int(pr[3])))
    return tuple(sorted(out))


def viol(what, detail):
    RES['viol'].append({'what': what, 'detail': str(detail)[:300]})
    print('  !! VIOLATION %s %s' % (what, str(detail)[:200]))


def note(k, n=1):
    RES['checks'][k] = RES['checks'].get(k, 0) + n


# ---------- exact F_p[Z] factorization for deg <= 4 (monic, low-first)

def fp_monic(c, p):
    c = [x % p for x in c]
    while c and c[-1] == 0:
        c.pop()
    inv = pow(c[-1], p - 2, p)
    return tuple((x * inv) % p for x in c)


def fp_divmod(a, b, p):
    a = [x % p for x in a]
    db = len(b) - 1
    binv = pow(b[-1], p - 2, p)
    q = [0] * max(len(a) - db, 0)
    for k in range(len(a) - db - 1, -1, -1):
        c = (a[k + db] * binv) % p
        q[k] = c
        if c:
            for i in range(db + 1):
                a[k + i] = (a[k + i] - c * b[i]) % p
    r = [x % p for x in a[:db]]
    while r and r[-1] == 0:
        r.pop()
    return q, r


def fp_factor_full(c, p):
    """full factorization of a monic poly of degree <= 4 over F_p:
    returns dict {monic factor tuple (low-first): multiplicity}."""
    c = list(fp_monic(c, p))
    assert len(c) - 1 <= 4
    out = {}
    # linear factors first (with multiplicity)
    z = 0
    while z < p and len(c) > 1:
        lin = [(-z) % p, 1]
        q, r = fp_divmod(c, lin, p)
        if not r:
            out[tuple(lin)] = out.get(tuple(lin), 0) + 1
            c = q
        else:
            z += 1
    # quadratic irreducible factors
    if len(c) - 1 >= 2:
        for b0 in range(p):
            for b1 in range(p):
                quad = [b0, b1, 1]
                if any(((z * z + b1 * z + b0) % p) == 0 for z in range(p)):
                    continue          # reducible quadratic
                while len(c) - 1 >= 2:
                    q, r = fp_divmod(c, quad, p)
                    if not r:
                        out[tuple(quad)] = out.get(tuple(quad), 0) + 1
                        c = q
                    else:
                        break
                if len(c) - 1 < 2:
                    break
            if len(c) - 1 < 2:
                break
    # leftover of degree 3 or 4 with no factor of degree <= 2: irreducible
    if len(c) > 1:
        out[tuple(fp_monic(c, p))] = out.get(tuple(fp_monic(c, p)), 0) + 1
    return out


# ---------- member builder at mu2 = 4 (deg f = 16)

def build16(fr, lam2, cres, rng, noise=2):
    """f = Psi^4 + sum_{j<4} A_j Psi^j, single side of slope lam2,
    residual Z^4 + cres[3] Z^3 + ... + cres[0] (target, twist-corrected;
    the probe's mu2 = 3 exponent formula at mu2 = 4)."""
    p = fr.p
    Psi = fr.Psi0
    Psi2 = pmul(Psi, Psi)
    pw = [[1], Psi, Psi2, pmul(Psi2, Psi)]
    f = pmul(Psi2, Psi2)
    e_top = (0 + 4 * (lam2 % 2) - ((4 * lam2) % 2)) // 2
    for j in range(4):
        yj = (4 - j) * lam2
        e_j = ((yj % 2) + j * (lam2 % 2) - ((4 * lam2) % 2)) // 2
        raw = (cres[j] * pow(fr.s, (e_top - e_j) % (p - 1) or (p - 1), p)) \
            % p if cres[j] % p else 0
        A = fr.lift2(yj, raw) if raw else []
        for _ in range(noise):
            k = yj + 1 + rng.randrange(3)
            gg = rng.randrange(p)
            if gg:
                A = padd(A, fr.lift2(k, gg))
        f = padd(f, pmul(A, pw[j]))
    return f


# ---------- polygon sides + residual assembly (the probe's logic,
# ---------- extracted; generic in mu)

def dv2A(fr, A):
    return fr.dv2(A) if A else BIG


def sides_of(fr, g, key):
    """develop g at key, peel-free; returns (mu, A, list of side dicts)
    or None on a degenerate hull; caller handles the peel loop."""
    mu = (len(g) - 1) // 4
    A = development(g, key, mu + 1)
    if dv2A(fr, A[0]) >= BIG:
        return ('peel', mu, A, None)
    ys = [dv2A(fr, A[j]) for j in range(mu)] + [0]
    pins = [(j, ys[j]) for j in range(mu + 1) if ys[j] < BIG]
    hull = [pins[0]]
    for pt in pins[1:]:
        while len(hull) >= 2 and \
            (hull[-1][1] - hull[-2][1]) * (pt[0] - hull[-1][0]) >= \
                (pt[1] - hull[-1][1]) * (hull[-1][0] - hull[-2][0]):
            hull.pop()
        hull.append(pt)
    p = fr.p
    sides = []
    for i in range(len(hull) - 1):
        (j0, y0), (j1, y1) = hull[i], hull[i + 1]
        L = j1 - j0
        num, den = y0 - y1, L
        gg = gcdi(num, den)
        u2, l2 = num // gg, den // gg
        if num <= fr.T2 * den:
            return ('badslope', mu, A, None)
        cs = []
        for t in range(L // l2 + 1):
            j = j0 + l2 * t
            yj = y0 - t * u2
            raw = fr.res2(A[j], yj) if j < mu else (1 if yj == 0 else 0)
            if (ys[j] if j < mu else 0) != yj:
                raw = 0
            dl = (yj % 2) + t * (u2 % 2) - (y0 % 2)
            if dl % 2 != 0:
                return ('twistparity', mu, A, None)
            cj = dl // 2
            cs.append((raw * pow(fr.s, cj % (p - 1) or (p - 1), p)) % p
                      if raw else 0)
        if cs[-1] == 0 or cs[0] == 0:
            return ('endpoint0', mu, A, None)
        sides.append({'j0': j0, 'j1': j1, 'L': L, 'num': num, 'den': den,
                      'u2': u2, 'l2': l2, 'cs': fp_monic(cs, p)})
    return ('ok', mu, A, sides)


# ---------- the annex-wired reader: per class, from the node's own key

def read_threads(fr, f, key, floor, entry_expect, parked_expect, depth):
    """returns list of letters, or a string status on failure.
    floor: only sides with slope > floor belong to this thread.
    entry_expect: None, ('NONE',), or ('EQ', coeffs, length) — the P2/P5
    check on the parked side at slope == floor, at THIS invocation.
    parked_expect: None or (lam2, coeffs) — the persistent clause-(c)
    check on any parked side at slope == lam2, every invocation."""
    if depth > 12:
        viol('thread depth cap', {'floor': floor})
        return 'depthcap'
    p = fr.p
    letters = []
    g = list(f)
    # peel loop at this key
    while True:
        st, mu, A, sides = sides_of(fr, g, key)
        if st == 'peel':
            q, r = pdivmod(g, key)
            if r:
                viol('peel not exact', {'depth': depth})
                return 'peelfail'
            letters.append((4, 1))
            note('peel')
            g = q
            if len(g) == 1:
                return letters
            continue
        if st != 'ok':
            viol('side assembly ' + st, {'depth': depth})
            return st
        break
    above = [S for S in sides if S['num'] > floor * S['den']]
    parked = [S for S in sides if S['num'] <= floor * S['den']]
    # P2 / P5: the parked side exactly at slope == floor, at entry
    if entry_expect is not None:
        at = [S for S in parked
              if S['l2'] == 1 and S['u2'] == floor]
        if entry_expect[0] == 'NONE':
            if at:
                viol('P5 pure control: lam2 side survived',
                     {'depth': depth, 'side': at[0]['cs']})
            else:
                note('P5-pure-no-survivor')
        else:
            _, coeffs, length = entry_expect
            if len(at) != 1 or at[0]['L'] != length or \
                    at[0]['cs'] != coeffs:
                viol('P2 parked residual mismatch',
                     {'got': at[0]['cs'] if at else None,
                      'want': coeffs})
            else:
                note('P2-parked-exact')
    # persistent clause-(c) check along the lineage
    if parked_expect is not None:
        lam2p, coeffs = parked_expect
        for S in parked:
            if S['l2'] == 1 and S['u2'] == lam2p:
                if S['cs'] != coeffs:
                    viol('P2 persistent parked mismatch',
                         {'got': S['cs'], 'want': coeffs})
                else:
                    note('P2B-persist')
    # read the thread's own sides
    for S in above:
        fac = fp_factor_full(S['cs'], p)
        for poly, m in sorted(fac.items()):
            d = len(poly) - 1
            if m == 1:
                letters.append((4 * S['l2'], d))
                note('decided-simple')
            elif d == 1 and S['l2'] == 1:
                lam = S['u2']
                if lam <= floor:
                    viol('P3 refined-at slope not above floor',
                         {'lam': lam, 'floor': floor})
                    return 'P3fail'
                note('refine')
                root = (-poly[0]) % p
                w = fr.lift2(lam, root)
                if fr.dv2(w) != lam or fr.res2(w, lam) != root:
                    viol('lift2 contract', {'lam': lam})
                    return 'liftfail'
                key2 = padd(key, pneg(w))
                sub = read_threads(fr, f, key2, lam, None,
                                   parked_expect, depth + 1)
                if isinstance(sub, str):
                    return sub
                letters += sub
            else:
                note('L3-node')
                return 'L3'
    return letters


# ---------- the naive single-key sequential route (P4 tooth target)

def read_naive(fr, f, cap=24):
    """the PE3 probe's own selection rule, single global key; returns
    (status, slopes_hit)."""
    p = fr.p
    key = list(fr.Psi0)
    slopes_hit = []
    g0 = list(f)
    for _ in range(cap):
        g = list(g0)
        letters = []
        while True:
            st, mu, A, sides = sides_of(fr, g, key)
            if st == 'peel':
                q, r = pdivmod(g, key)
                if r:
                    return ('peelfail', slopes_hit)
                letters.append((4, 1))
                g = q
                if len(g) == 1:
                    return ('decided', slopes_hit)
                continue
            if st != 'ok':
                return (st, slopes_hit)
            break
        refine_at = None
        for S in sides:
            fac = fp_factor_full(S['cs'], p)
            reps = {(-poly[0]) % p: m for poly, m in fac.items()
                    if m >= 2 and len(poly) == 2}
            if any(m >= 2 for poly, m in fac.items()
                   if len(poly) - 1 >= 2):
                return ('L3', slopes_hit)
            if reps:
                if S['l2'] != 1:
                    return ('L3', slopes_hit)
                s2 = max((m, z) for z, m in reps.items())[1]
                cand = (S['u2'], s2)
                if refine_at is None or cand[0] > refine_at[0]:
                    refine_at = cand
        if refine_at is None:
            return ('decided', slopes_hit)
        lam, s2 = refine_at
        slopes_hit.append(lam)
        w = fr.lift2(lam, s2)
        key = padd(key, pneg(w))
    return ('cap', slopes_hit)


# ---------- member processing

def target_cres(kind, a, b, p):
    if kind == 'A':                       # (Z-a)^2 (Z-b)^2
        return [(a * a * b * b) % p, (-2 * a * b * (a + b)) % p,
                (a * a + b * b + 4 * a * b) % p, (-2 * (a + b)) % p]
    if kind == 'B':                       # (Z-a)^3 (Z-b)
        return [(a ** 3 * b) % p, (-(3 * a * a * b + a ** 3)) % p,
                (3 * a * a + 3 * a * b) % p, (-(3 * a + b)) % p]
    return [(a ** 4) % p, (-4 * a ** 3) % p,
            (6 * a * a) % p, (-4 * a) % p]  # (Z-a)^4


def process_member(fr, lam2, kind, a, b, rng):
    """returns dict record or None (discard)."""
    p = fr.p
    cres = target_cres(kind, a, b, p)
    f = build16(fr, lam2, cres, rng)
    if not disc_nonzero(f):
        note('disc0-discard')
        return None
    st, mu, A, sides = sides_of(fr, f, fr.Psi0)
    if st != 'ok' or len(sides) != 1 or sides[0]['l2'] != 1 or \
            sides[0]['u2'] != lam2:
        viol('top node not single side lam2', {'st': st})
        return None
    want = fp_monic([cres[0], cres[1], cres[2], cres[3], 1], p)
    if sides[0]['cs'] != want:
        viol('top residual != target', {'got': sides[0]['cs']})
        return None
    note('top-node-exact')
    letters = []
    l3 = False
    fac = fp_factor_full(sides[0]['cs'], p)
    for poly, m in sorted(fac.items()):
        d = len(poly) - 1
        if m == 1:
            letters.append((4, d))        # l2 = 1
            note('decided-simple-at-top')  # the R-a route: no refine
            continue
        if d != 1:
            viol('unexpected repeated non-linear at top', {})
            return None
        r0 = (-poly[0]) % p
        # entry / persistent expectations per configuration
        if kind == 'A':
            r1 = b if r0 == a % p else a
            t = (r1 - r0) % p
            coeffs = ((t * t) % p, (-2 * t) % p, 1)
            entry = ('EQ', coeffs, 2)
            parked = (lam2, coeffs)
        elif kind == 'B':
            t = (b - a) % p
            coeffs = ((-t) % p, 1)
            entry = ('EQ', coeffs, 1)
            parked = (lam2, coeffs)
        else:
            entry = ('NONE',)
            parked = None
        w = fr.lift2(lam2, r0)
        if fr.dv2(w) != lam2 or fr.res2(w, lam2) != r0:
            viol('lift2 contract at entry', {'lam2': lam2})
            return None
        note('refine')
        key2 = padd(list(fr.Psi0), pneg(w))
        sub = read_threads(fr, f, key2, lam2, entry, parked, 1)
        if sub == 'L3':
            l3 = True
            break
        if isinstance(sub, str):
            return None                   # viol already recorded
        letters += sub
    if l3:
        note('L3-skip')
        return {'kind': kind, 'l3': True}
    sig = tuple(sorted(letters))
    if sum(e * ff for e, ff in sig) != 16:
        viol('sum ef != 16', {'sig': sig})
        return None
    gs = pari_sigma16(f, p)
    agree = (gs == sig)
    if not agree:
        viol('sigma mismatch', {'kind': kind, 'a': a, 'b': b,
                                'read': sig, 'pari': gs})
    else:
        note('P1-pari-agree')
    rec = {'kind': kind, 'l3': False, 'sig': sig, 'agree': agree}
    if kind == 'A':                       # P4 tooth: the naive route
        stn, slopes = read_naive(fr, f)
        cyc = (stn == 'cap' and slopes.count(lam2) >= 2)
        rec['naive'] = {'status': stn, 'lam2_hits': slopes.count(lam2),
                        'nref': len(slopes)}
        if cyc:
            note('P4-naive-cycle-caught')
        else:
            viol('P4 naive route did not cycle',
                 {'status': stn, 'slopes': slopes[:12]})
    return rec


def main(smoke_only=False):
    t0 = time.time()
    rng = random.Random(20260809)
    print('HE7 ANNEX F-1 supp: two repeated classes + mu2=4 refines '
          '(n=16)')
    if smoke_only:
        fr = Fr12(5, 5, 1)
        rec = process_member(fr, 11, 'A', 1, 2, rng)
        print('SMOKE record:', rec)
        # cross-check the two oracles on the same member (fresh rng)
        rng2 = random.Random(20260809)
        f = build16(fr, 11, target_cres('A', 1, 2, 5), rng2)
        print('SMOKE oracle cross-check: full-nfinit %s == p-maximal %s'
              % (pari_sigma(f, 5), pari_sigma16(f, 5)))
        print('SMOKE secs: %.1f' % (time.time() - t0))
        return 0
    # disclosed smoke happens pre-seal via the 'smoke' CLI arg; the
    # batch below is the sealed run.
    for p in (5, 7):
        for s in (1, 2):
            for lam2 in (11, 12):
                fr = Fr12(p, 5, s)
                row = {'p': p, 's': s, 'lam2': lam2, 'members': 0,
                       'agree': 0, 'l3': 0, 'sig': {}, 'kinds': {}}
                jobs = []
                for a0, b0 in ((1, 2), (1, 3), (2, 3)):
                    for seed in range(2):
                        jobs.append(('A', a0, b0))
                for a0, b0 in ((1, 3), (2, 1)):
                    for seed in range(2):
                        jobs.append(('B', a0, b0))
                for a0 in (1, 2):
                    jobs.append(('C', a0, 0))
                for kind, a0, b0 in jobs:
                    rec = process_member(fr, lam2, kind, a0, b0, rng)
                    if rec is None:
                        continue
                    if rec['l3']:
                        row['l3'] += 1
                        continue
                    row['members'] += 1
                    row['agree'] += rec['agree']
                    row['kinds'][kind] = row['kinds'].get(kind, 0) + 1
                    k = str(rec['sig'])
                    row['sig'][k] = row['sig'].get(k, 0) + 1
                print('row p=%d s=%d lam2=%d: members %d agree %d l3 %d '
                      'kinds %s sig %s' %
                      (p, s, lam2, row['members'], row['agree'],
                       row['l3'], row['kinds'], row['sig']))
                RES['rows'].append(row)
    import he7_pe3_probe12 as probe_mod
    for v in probe_mod.RES['viol']:
        viol('probe-module ' + v['what'], v['detail'])
    RES['secs'] = round(time.time() - t0, 1)
    tot = sum(r['members'] for r in RES['rows'])
    agr = sum(r['agree'] for r in RES['rows'])
    l3 = sum(r['l3'] for r in RES['rows'])
    print('TOTAL %d members, %d agree, %d L3-skips, checks %s, '
          'violations %d, %.1fs' % (tot, agr, l3, RES['checks'],
                                    len(RES['viol']), RES['secs']))
    ok = (not RES['viol'] and agr == tot and l3 == 0 and
          RES['checks'].get('P2-parked-exact', 0) > 0 and
          RES['checks'].get('P2B-persist', 0) > 0 and
          RES['checks'].get('P4-naive-cycle-caught', 0) > 0 and
          RES['checks'].get('P5-pure-no-survivor', 0) > 0 and
          RES['checks'].get('decided-simple-at-top', 0) > 0)
    verdict = 'GREEN' if ok else 'RED'
    print('VERDICT:', verdict)
    RES['verdict'] = verdict
    with open(os.path.join(HERE, 'he7annex_supp_results.json'),
              'w') as fh:
        json.dump(RES, fh, indent=1, sort_keys=True)
    return 0 if verdict == 'GREEN' else 1


if __name__ == '__main__':
    sys.exit(main(smoke_only=(len(sys.argv) > 1 and
                              sys.argv[1] == 'smoke')))
