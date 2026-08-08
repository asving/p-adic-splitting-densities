"""HEX3 — the U3^TRP exact-law battery (HEXHAUST-3 unit; consumes W-12 BOX-3).

THE LAW UNDER TEST (preregistered P-1; per prime power q, window N >= 2,
both characteristics; "conservative convention" = the sealed w12 TRP
reader's tail rule: any read state with v(B0) >= N exits UNDECIDED, no
tail sigma-certification — W12-BOX-3/BOX-7 disclosed convention):

    U3^conv(q, N) = q * u(q, N)                     [q centers, exact]
    u(q, N) = q^(2N-2)
            + (q-1) * SUM_{k=1..floor((N-1)/3)} q^(4k-1) * (q^(N-3k) - 1) * R(N-3k)
    R(M)    = q^(M-1) + floor((M-1)/2) * (q-1) * q^(M-2)      [R(1) = 1]

and the DEPTH-0 SPECIES DECOMPOSITION (P-2), per center, with
M = N-3k, w = u0-3k, j = (u0-3t)/2:
    B0ZERO         locus q^(2N-2),                            drained ALL
    ALPHA(k)       locus (q-1)q^(3N-3-6k),          drained (q-1)q^(3k)u(N-3k)
    FULL11SQ(k)    locus (q-1)(q-2)q^(3N-3-6k),     drained (q-1)(q-2)q^(3k+M-1)R(M)
    VERT1(u0,k)    locus (q-1)^2 q^(3N-3-u0-3k),    drained (q-1)^2 q^(3k+M-1-w)R(M)
    VERT2(u0,t)    locus (q-1)^2 q^(3N-3-u0-t-(u0+t)/2),
                                                    drained (q-1)^2 q^(3t+M-1+j)R(M-2j)
    (depth-0 decided families drain 0; both directions: unexpected keys or
     missing predicted keys are violations)

EVIDENCE CLASSES: the fresh reader below is THIS runner's own arithmetic
(SAME); the pointwise tie to the SEALED w12 read_trp (md5-pinned import)
is SEAL-TIE; the tie to the COMMITTED w12_checks_results.json U3TRP
values (md5-pinned) is a bookkeeping tie to the frozen wave-12 artifacts.
No PARI leg: sigma-content was independently oracled by the sealed W12
battery; this battery's claim is the exact COUNT law of the disclosed
convention's residue.

FAMILIES:
  HEX3-PIN     [NONE] md5 pins: w12_checks.py, w11_checks.py,
               w10_checks.py, w12_checks_results.json (values below).
  HEX3-LAW     [SAME] per-row per-center drained total == u(q,N).
  HEX3-SPECIES [SAME] per-row per-key (locus, drained) == the closed
               forms, BOTH directions.
  HEX3-XREAD   [SEAL-TIE] pointwise fresh-reader vs sealed w12 read_trp
               (drain verdict + depth-0-decided agreement) on every row
               with <= 65536 states.
  HEX3-W12TIE  [NONE] q * u_measured == the committed w12 JSON's
               U3TRP_measured_conservative at all 23 w12 cubic rows.
  HEX3-CHAR    [SAME] full species tallies IDENTICAL across Zp/Fqt at
               every shared (q, N) — 17 pairs.

TEETH (preregistered fire counts; a tooth that does not fire at its
exact count makes the battery RED):
  HEX3-T-FLOOR  R(M) corrupted floor((M-1)/2) -> floor(M/2): must
                mismatch HEX3-LAW on exactly the 10 rows with some
                N-3k even (N in {5,7,8,9} on this roster).
  HEX3-T-ALPHA  ALPHA drained corrupted (q-1) -> q: must mismatch
                HEX3-SPECIES on exactly the 20 rows with N >= 4.
  HEX3-T-VERT1  VERT1 drained corrupted q^(M-1-w) -> q^(M-w): must
                mismatch HEX3-SPECIES on exactly the 13 rows with a
                VERT1 key (N >= 5).

ROSTER (46 rows, 67,410,225 per-center states read; per-center
enumeration at the recentered origin — exact for the whole space by the
translation bijection, whole-space U3 = q * u):
  Zp  (mixed char): (2,3..9), (3,2..6), (5,2..4), (7,2..3), (11,2..3),
                    (13,2..3)                                  [21 rows]
  Fqt (equal char): (2,3..8), (3,2..5), (4,2..5), (5,2..4), (7,2..3),
                    (8,2..3), (9,2..3), (11,2..3)              [25 rows]
  Shared (q,N) cross-char pairs: 17.

PRE-SEAL SMOKE DISCLOSED: the fresh reader + species predictions were
developed as a /tmp prototype and confirmed pre-seal on 18 rows
(Zp (2,3..7),(3,2..4),(5,2),(5,3),(7,3),(11,2); Fqt (2,4),(2,7),(3,3),
(3,4),(4,2),(4,3)) — all totals and species tables matched the law;
runner --smoke run once pre-seal (record in the note S7).  The law was
FITTED on the committed w12 U3TRP table + those prototype rows and then
DERIVED (note S3-S5); the 11 rows (2,8),(2,9),(3,5),(3,6),(4,4),(4,5),
(5,3),(5,4),(7,3),(9,3),(11,3),(13,3) marked NEW were never measured
before this battery (values preregistered in the note S7 table).

Exact integer arithmetic throughout; deterministic; no floats.
"""

import sys, os, json, time, hashlib, itertools
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import w10_checks as W10
import w12_checks as W12

PINS = {
    'w12_checks.py':            '7dc040d94fbbb1e8d20ac817b665d418',
    'w11_checks.py':            '500aae152bb5b5e9df3712904a6d73a6',
    'w10_checks.py':            'a9c34244a3af19f5fa864375b494380b',
    'w12_checks_results.json':  '05776c9e00071c5d7524abdfbe894442',
}

FAMILIES = ['HEX3-PIN', 'HEX3-LAW', 'HEX3-SPECIES', 'HEX3-XREAD',
            'HEX3-W12TIE', 'HEX3-CHAR']
TEETH = ['HEX3-T-FLOOR', 'HEX3-T-ALPHA', 'HEX3-T-VERT1']
TEETH_EXPECT = {'HEX3-T-FLOOR': 10, 'HEX3-T-ALPHA': 20, 'HEX3-T-VERT1': 13}

VIOL = {f: [] for f in FAMILIES}
NCHK = {f: 0 for f in FAMILIES}
FIRE = {t: 0 for t in TEETH}
LOG = []


def say(msg):
    print(msg)
    sys.stdout.flush()
    LOG.append(msg)


def note(fam, n=1):
    NCHK[fam] += n


def viol(fam, tag, detail):
    VIOL[fam].append((tag, str(detail)))
    say('  VIOLATION [%s] %s: %s' % (fam, tag, detail))


# ------------------------------------------------------------ the law (P-1)
def R_law(M, q):
    return q ** (M - 1) + (((M - 1) // 2) * (q - 1) * q ** (M - 2)
                           if M >= 2 else 0)


def u_law(N, q):
    tot = q ** (2 * N - 2)
    for k in range(1, (N - 1) // 3 + 1):
        M = N - 3 * k
        tot += (q - 1) * q ** (4 * k - 1) * (q ** M - 1) * R_law(M, q)
    return tot


# corrupted laws (teeth)
def R_bad_floor(M, q):
    return q ** (M - 1) + ((M // 2) * (q - 1) * q ** (M - 2)
                           if M >= 2 else 0)


def u_bad_floor(N, q):
    tot = q ** (2 * N - 2)
    for k in range(1, (N - 1) // 3 + 1):
        M = N - 3 * k
        tot += (q - 1) * q ** (4 * k - 1) * (q ** M - 1) * R_bad_floor(M, q)
    return tot


# ------------------------------------------------- species predictions (P-2)
def species_pred(q, N, alpha_coeff_bad=False, vert1_exp_bad=False):
    pred = {('B0ZERO',): (q ** (2 * N - 2), q ** (2 * N - 2))}
    for k in range(1, (N - 1) // 3 + 1):
        M = N - 3 * k
        ac = q if alpha_coeff_bad else (q - 1)
        pred[('ALPHA', k)] = ((q - 1) * q ** (3 * N - 3 - 6 * k),
                              ac * q ** (3 * k) * u_law(M, q))
        pred[('FULL11SQ', k)] = (
            (q - 1) * (q - 2) * q ** (3 * N - 3 - 6 * k),
            (q - 1) * (q - 2) * q ** (3 * k + M - 1) * R_law(M, q))
        for u0 in range(3 * k + 1, N):
            w = u0 - 3 * k
            ve = (M - w) if vert1_exp_bad else (M - 1 - w)
            pred[('VERT1', u0, k)] = (
                (q - 1) ** 2 * q ** (3 * N - 3 - u0 - 3 * k),
                (q - 1) ** 2 * q ** (3 * k + ve) * R_law(M, q))
    for t in range(1, N):
        M = N - 3 * t
        for u0 in range(3 * t + 2, N):
            if (u0 - 3 * t) % 2:
                continue
            j = (u0 - 3 * t) // 2
            pred[('VERT2', u0, t)] = (
                (q - 1) ** 2 * q ** (3 * N - 3 - u0 - t - (u0 + t) // 2),
                (q - 1) ** 2 * q ** (3 * t + M - 1 + j) * R_law(M - 2 * j, q))
    return {k: v for k, v in pred.items() if v[0] > 0}


# ------------------------------------------------------------ fresh reader
def hull(points):
    pts = sorted((x, y) for (x, y) in points if y is not None)
    h = []
    for pt in pts:
        while len(h) >= 2:
            (x1, y1), (x2, y2) = h[-2], h[-1]
            if (y2 - y1) * (pt[0] - x1) >= (pt[1] - y1) * (x2 - x1):
                h.pop()
            else:
                break
        h.append(pt)
    return h


def kroots_mult(K, coeffs):
    out = []
    poly = list(coeffs)
    for z in K.elems():
        m = 0
        while len(poly) > 1:
            n = len(poly) - 1
            quot = [K.zero()] * n
            acc = poly[n]
            for i in range(n - 1, -1, -1):
                quot[i] = acc
                acc = K.add(poly[i], K.mul(acc, z))
            if K.is_zero(acc):
                m += 1
                poly = quot
            else:
                break
        if m:
            out.append((z, m))
    return out, len(poly) - 1


def rint(R, m):
    one = 1 if R.kind == 'Zp' else R.lift(R.K.one())
    out = 0 if R.kind == 'Zp' else tuple([R.K.zero()] * R.N)
    for _ in range(m):
        out = R.add(out, one)
    return out


def pipow(R, m):
    out = rint(R, 1)
    for _ in range(m):
        out = R.mul(out, R.pi())
    return out


def shift3(R, a2, a1, a0, s):
    s2 = R.mul(s, s)
    s3 = R.mul(s2, s)
    b2 = R.add(a2, R.mul(rint(R, 3), s))
    b1 = R.add(R.add(a1, R.mul(R.mul(rint(R, 2), a2), s)),
               R.mul(rint(R, 3), s2))
    b0 = R.add(R.add(R.add(a0, R.mul(a1, s)), R.mul(a2, s2)), s3)
    return b2, b1, b0


def _is_cube(K, coeff, R, k):
    c2 = R.res(coeff[2], k)
    c1 = R.res(coeff[1], 2 * k)
    c0 = R.res(coeff[0], 3 * k)
    roots, cof = kroots_mult(K, [c0, c1, c2, K.one()])
    return len(roots) == 1 and roots[0][1] == 3


def read_fresh(R, q, B2, B1, B0):
    """conservative chain of a per-center depth-0 TRP state.
    Returns (drained, depth0_key)."""
    K = R.K
    d0key = None
    first = True
    it = 0
    while True:
        it += 1
        assert it <= 3 * R.N + 8, 'read_fresh loop cap'
        u0 = R.val(B0)
        if u0 is None:
            if first:
                d0key = ('B0ZERO',)
            return True, d0key
        coeff = {0: B0, 1: B1, 2: B2}
        pts = [(0, u0), (1, R.val(B1)), (2, R.val(B2)), (3, 0)]
        hv = hull(pts)
        refine = None
        for i in range(len(hv) - 1):
            (j0, y0), (j1, y1) = hv[i], hv[i + 1]
            dx, dy = j1 - j0, y0 - y1
            g = gcd(dx, dy) if dy else dx
            e = dx // g
            hstep = dy // g
            if g == 1:
                continue
            rc = []
            for i2 in range(g + 1):
                j = j0 + i2 * e
                h = y0 - i2 * hstep
                rc.append(K.one() if j == 3 else R.res(coeff[j], h))
            lead = rc[-1]
            invl = K.inv(lead)
            rcm = [K.mul(x, invl) for x in rc]
            roots, cofdeg = kroots_mult(K, rcm)
            for (z, m) in roots:
                if m > 1:
                    assert refine is None and e == 1
                    refine = (z, hstep, g, hv)
        if first:
            first = False
            if refine is not None:
                z, k, g, hv0 = refine
                if len(hv0) == 2:
                    assert g == 3
                    d0key = (('ALPHA', k) if _is_cube(K, coeff, R, k)
                             else ('FULL11SQ', k))
                else:
                    vx, vy = hv0[1]
                    d0key = (('VERT1', u0, k) if vx == 1
                             else ('VERT2', u0, vy))
            else:
                return False, ('DECIDED',)
        if refine is None:
            return False, d0key
        z, k, _, _ = refine
        s = R.mul(R.lift(z), pipow(R, k))
        B2, B1, B0 = shift3(R, B2, B1, B0, s)


# ------------------------------------------------------------ row runner
def enum_row(kind, q, N, do_xread):
    R = W10.ZpWin(q, N) if kind == 'Zp' else W10.FqtWin(q, N)
    K = R.K
    if kind == 'Zp':
        elems1 = [q * b for b in range(q ** (N - 1))]
        zero_res = 0
    else:
        els = list(K.elems())
        elems1 = [(K.zero(),) + rest
                  for rest in itertools.product(els, repeat=N - 1)]
        zero_res = K.zero()
    tally = {}
    xdiv = 0
    t0 = time.time()
    for B2 in elems1:
        for B1 in elems1:
            for B0 in elems1:
                drained, key = read_fresh(R, q, B2, B1, B0)
                loc, dr = tally.get(key, (0, 0))
                tally[key] = (loc + 1, dr + (1 if drained else 0))
                if do_xread:
                    rec = W12.read_trp(R, q, B2, B1, B0, zero_res)
                    if rec['decided'] != (not drained):
                        xdiv += 1
                    if (key == ('DECIDED',)) != (rec['depth0'] is not None):
                        xdiv += 1
    el = time.time() - t0
    total_dr = sum(d for (_, d) in tally.values())
    return tally, total_dr, xdiv, el


def check_row(kind, q, N, do_xread):
    tally, dr, xdiv, el = enum_row(kind, q, N, do_xread)
    states = q ** (3 * (N - 1))
    row = {'kind': kind, 'q': q, 'N': N, 'states': states,
           'u_measured': dr, 'u_law': u_law(N, q),
           'U3': q * dr, 'elapsed_s': round(el, 2)}

    # HEX3-LAW
    note('HEX3-LAW')
    if dr != u_law(N, q):
        viol('HEX3-LAW', '%s q=%d N=%d' % (kind, q, N),
             'measured %d != law %d' % (dr, u_law(N, q)))

    # partition bookkeeping
    note('HEX3-LAW')
    if sum(l for (l, _) in tally.values()) != states:
        viol('HEX3-LAW', 'partition %s q=%d N=%d' % (kind, q, N),
             'sum of loci != q^(3N-3)')

    # HEX3-SPECIES (both directions)
    pred = species_pred(q, N)
    keys = set(pred) | {k for k in tally if k != ('DECIDED',)}
    sp_ok = True
    for key in sorted(keys):
        note('HEX3-SPECIES')
        pl, pd = pred.get(key, (0, 0))
        ml, md = tally.get(key, (0, 0))
        if (pl, pd) != (ml, md):
            sp_ok = False
            viol('HEX3-SPECIES', '%s q=%d N=%d %s' % (kind, q, N, key),
                 'pred (locus,drained)=(%d,%d) measured (%d,%d)'
                 % (pl, pd, ml, md))
    dec_l, dec_d = tally.get(('DECIDED',), (0, 0))
    note('HEX3-SPECIES')
    if dec_d != 0:
        sp_ok = False
        viol('HEX3-SPECIES', '%s q=%d N=%d DECIDED' % (kind, q, N),
             'depth-0-decided member drained (%d)' % dec_d)

    # HEX3-XREAD
    if do_xread:
        note('HEX3-XREAD', states)
        if xdiv:
            viol('HEX3-XREAD', '%s q=%d N=%d' % (kind, q, N),
                 '%d divergences vs sealed read_trp' % xdiv)

    # teeth on this row
    if u_bad_floor(N, q) != dr:
        FIRE['HEX3-T-FLOOR'] += (u_bad_floor(N, q) != u_law(N, q))
    else:
        if u_bad_floor(N, q) != u_law(N, q):
            viol('HEX3-LAW', 'tooth-floor %s q=%d N=%d' % (kind, q, N),
                 'corrupted law matched measurement')
    bad_a = species_pred(q, N, alpha_coeff_bad=True)
    if bad_a != pred:
        caught = any(bad_a.get(k, (0, 0)) != tally.get(k, (0, 0))
                     for k in bad_a)
        if caught:
            FIRE['HEX3-T-ALPHA'] += 1
        else:
            viol('HEX3-SPECIES', 'tooth-alpha %s q=%d N=%d' % (kind, q, N),
                 'corrupted alpha prediction matched measurement')
    bad_v = species_pred(q, N, vert1_exp_bad=True)
    if bad_v != pred:
        caught = any(bad_v.get(k, (0, 0)) != tally.get(k, (0, 0))
                     for k in bad_v)
        if caught:
            FIRE['HEX3-T-VERT1'] += 1
        else:
            viol('HEX3-SPECIES', 'tooth-vert1 %s q=%d N=%d' % (kind, q, N),
                 'corrupted vert1 prediction matched measurement')

    say('  [%s q=%d N=%d] states=%d u=%d law=%d U3=%d species=%s '
        'xread=%s %.2fs'
        % (kind, q, N, states, dr, u_law(N, q), q * dr,
           'ok' if sp_ok else 'VIOL',
           ('%d-div' % xdiv) if do_xread else 'skip', el))
    row['species_tally'] = {repr(k): v for k, v in sorted(tally.items())}
    return row, tally


ROWS_ZP = ([(2, N) for N in range(3, 10)] + [(3, N) for N in range(2, 7)]
           + [(5, 2), (5, 3), (5, 4), (7, 2), (7, 3), (11, 2), (11, 3),
              (13, 2), (13, 3)])
ROWS_FQT = ([(2, N) for N in range(3, 9)] + [(3, N) for N in range(2, 6)]
            + [(4, 2), (4, 3), (4, 4), (4, 5), (5, 2), (5, 3), (5, 4),
               (7, 2), (7, 3), (8, 2), (8, 3), (9, 2), (9, 3), (11, 2),
               (11, 3)])
XREAD_CAP = 65536

SMOKE_ZP = [(2, 3), (2, 4), (2, 5), (3, 2), (3, 3), (3, 4), (5, 2)]
SMOKE_FQT = [(2, 3), (2, 4), (3, 3), (4, 2), (5, 2)]


def main(smoke=False):
    t0 = time.time()
    say('HEX3 battery %s' % ('SMOKE' if smoke else 'FULL'))

    # HEX3-PIN
    for fn, md5 in PINS.items():
        note('HEX3-PIN')
        with open(os.path.join(HERE, fn), 'rb') as f:
            got = hashlib.md5(f.read()).hexdigest()
        if got != md5:
            viol('HEX3-PIN', fn, 'md5 %s != pinned %s' % (got, md5))

    rows_zp = SMOKE_ZP if smoke else ROWS_ZP
    rows_fqt = SMOKE_FQT if smoke else ROWS_FQT
    results = []
    tallies = {}
    for kind, roster in (('Zp', rows_zp), ('Fqt', rows_fqt)):
        for (q, N) in roster:
            do_x = q ** (3 * (N - 1)) <= XREAD_CAP
            row, tally = check_row(kind, q, N, do_x)
            results.append(row)
            tallies[(kind, q, N)] = tally

    # HEX3-CHAR: identical species tallies across characteristics
    shared = sorted({(q, N) for (k, q, N) in tallies if k == 'Zp'}
                    & {(q, N) for (k, q, N) in tallies if k == 'Fqt'})
    for (q, N) in shared:
        note('HEX3-CHAR')
        if tallies[('Zp', q, N)] != tallies[('Fqt', q, N)]:
            viol('HEX3-CHAR', '(q=%d,N=%d)' % (q, N),
                 'Zp and Fqt species tallies differ')
    say('HEX3-CHAR: %d shared (q,N) pairs compared' % len(shared))

    # HEX3-W12TIE: committed w12 JSON values
    with open(os.path.join(HERE, 'w12_checks_results.json')) as f:
        w12res = json.load(f)
    n_tie = 0
    for r in w12res['cubic']:
        key = (r['kind'], r['q'], r['N'])
        if key not in tallies:
            if not smoke:
                viol('HEX3-W12TIE', str(key), 'w12 row not covered by roster')
            continue
        note('HEX3-W12TIE')
        n_tie += 1
        mine = r['q'] * sum(d for (_, d) in tallies[key].values())
        if mine != r['U3TRP_measured_conservative']:
            viol('HEX3-W12TIE', str(key),
                 'q*u=%d != committed %d'
                 % (mine, r['U3TRP_measured_conservative']))
    say('HEX3-W12TIE: %d committed rows tied' % n_tie)

    elapsed = time.time() - t0
    say('')
    say('==== SUMMARY ====')
    red = False
    for f in FAMILIES:
        say('%-14s checks=%-9d violations=%d'
            % (f, NCHK[f], len(VIOL[f])))
        if VIOL[f]:
            red = True
    for t in TEETH:
        exp = TEETH_EXPECT[t] if not smoke else None
        ok = (FIRE[t] == exp) if exp is not None else (FIRE[t] >= 1)
        say('%-14s fired=%d expected=%s %s'
            % (t, FIRE[t], exp if exp is not None else '>=1',
               'OK' if ok else 'RED'))
        if not ok:
            red = True
    verdict = 'RED' if red else 'GREEN'
    say('VERDICT: %s (%.1fs)' % (verdict, elapsed))

    out = {'smoke': smoke, 'rows': results,
           'families': {f: {'checks': NCHK[f], 'violations': VIOL[f]}
                        for f in FAMILIES},
           'teeth': {t: FIRE[t] for t in TEETH},
           'teeth_expected': TEETH_EXPECT,
           'char_pairs': len(shared), 'w12_ties': n_tie,
           'verdict': verdict, 'elapsed_s': round(elapsed, 1)}
    if not smoke:
        with open(os.path.join(HERE, 'hex3_checks_results.json'), 'w') as f:
            json.dump(out, f, indent=1)
        with open(os.path.join(HERE, 'hex3_checks_output.txt'), 'w') as f:
            f.write('\n'.join(LOG) + '\n')
    return 0 if verdict == 'GREEN' else 1


if __name__ == '__main__':
    sys.exit(main(smoke='--smoke' in sys.argv))
