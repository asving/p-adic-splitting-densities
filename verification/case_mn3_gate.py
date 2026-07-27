#!/usr/bin/env python3
"""case_mn3_gate.py — SEALED gate M-n3 census (SP.6 of MOVES §M-SPECIES).

Seal: CASE_MN3_SEALED_PREDICTIONS.md (committed BEFORE this script existed):
the 53-letter n=3 catalogue, the menu map, per-prime exclusions (11 at p=2,
2 at p=3).  Census: ALL monic cubics f = x^3+c2x^2+c1x+c0 over Z_p at
p=2 N=8 (2^24) and p=3 N=5 (3^15); every T_can chain walked to depth 2
(root read + one continuation read per eligible (side,psi) branch,
canonical S6b lifts); every decided read datum classified against the
catalogue; per-letter hits + transition matrix tallied.  Checks (zero
tolerance): (i) strays, (ii) two-sided realization (42/53 at p=2, 51/53 at
p=3, absences = the sealed field-size explanations), (iii) menu edges,
(iv) loop classes (letter-level, FC9).  FAIL is a valid outcome; the seal
is never touched.  Long output -> /tmp/mn3_census.out; machine-readable ->
results/case_mn3_results.json.   Run: uv run --with numpy python3 case_mn3_gate.py
"""
import json, os, sys, time
from fractions import Fraction
from itertools import product
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
OUTPATH = '/tmp/mn3_census.out'
JSONPATH = os.path.join(HERE, 'results', 'case_mn3_results.json')
CONFIGS = [(2, 8), (3, 5)]

# ---------------- the sealed catalogue (53 letters) ----------------
# letter key: (group, e, l, a, flankL, flankR, lam, sel)
#   group: 'R','Q3','Q2','Q1','I21','I22','I31','I33'; flanks: width tuples;
#   lam: sorted tuple of (g,mu) entries (one per distinct irreducible factor);
#   sel: (g,mu) or 'V' (terminal verdict, W=1 letters).
L2ROWS = ((((2, 1),), (2, 1)), (((1, 2),), (1, 2)), (((1, 1), (1, 1)), (1, 1)))
L3ROWS = ((((3, 1),), (3, 1)),
          (((1, 1), (2, 1)), (2, 1)), (((1, 1), (2, 1)), (1, 1)),
          (((1, 3),), (1, 3)),
          (((1, 1), (1, 2)), (1, 2)), (((1, 1), (1, 2)), (1, 1)),
          (((1, 1), (1, 1), (1, 1)), (1, 1)))


def build_catalogue():
    cat = []
    for G in ('R', 'Q3'):                      # 21 rows each, stage (1,1,3)
        for fr in ((2,), (1, 1)):
            cat.append((G, 1, 1, 0, (), fr, ((1, 1),), (1, 1)))      # R1
        cat.append((G, 1, 1, 1, (1,), (1,), ((1, 1),), (1, 1)))      # R2
        for fl in ((2,), (1, 1)):
            cat.append((G, 1, 1, 2, fl, (), ((1, 1),), (1, 1)))      # R3
        for lam, sel in L2ROWS:
            cat.append((G, 1, 2, 0, (), (1,), lam, sel))             # R4
        for lam, sel in L2ROWS:
            cat.append((G, 1, 2, 1, (1,), (), lam, sel))             # R5
        for lam, sel in L3ROWS:
            cat.append((G, 1, 3, 0, (), (), lam, sel))               # R6
        cat.append((G, 2, 1, 0, (), (1,), ((1, 1),), (1, 1)))        # R7 s0'=0
        cat.append((G, 2, 1, 0, (1,), (), ((1, 1),), (1, 1)))        # R7 s0'=1
        cat.append((G, 3, 1, 0, (), (), ((1, 1),), (1, 1)))          # R8
    G = 'Q2'                                    # 6 letters, stage (1,1,2)
    cat.append((G, 1, 1, 0, (), (1,), ((1, 1),), (1, 1)))            # Q2.1
    cat.append((G, 1, 1, 1, (1,), (), ((1, 1),), (1, 1)))            # Q2.2
    for lam, sel in L2ROWS:
        cat.append((G, 1, 2, 0, (), (), lam, sel))                   # Q2.3
    cat.append((G, 2, 1, 0, (), (), ((1, 1),), (1, 1)))              # Q2.4
    cat.append(('Q1', 1, 1, 0, (), (), ((1, 1),), 'V'))              # Q1
    for G in ('I21', 'I22', 'I31', 'I33'):                           # 4 I's
        cat.append((G, 1, 1, 0, (), (), ((1, 1),), 'V'))
    assert len(cat) == 53 and len(set(cat)) == 53
    return cat


def excluded_letters(cat, p):
    """Sealed field-size rule SP.4(i): lambda needs more distinct nonzero
    roots (= its number of degree-1 entries, each a DISTINCT linear factor,
    all nonzero by the endpoint convention) than F_p holds (p-1)."""
    return {k for k in cat if sum(1 for (g, m) in k[6] if g == 1) > p - 1}


# ---------------- F_p polynomial utilities ----------------
def fp_factor(coeffs, p):
    """Factor a nonzero poly over F_p (low->high tuple, deg<=3, nonzero
    constant term) into monic irreducibles: list of (factor_tuple, mult)."""
    c = list(coeffs)
    while c and c[-1] % p == 0:
        c.pop()
    assert c and c[0] % p != 0
    inv = pow(c[-1], p - 2, p) if p > 2 else 1
    c = [(x * inv) % p for x in c]              # monic
    out = []
    for r in range(1, p):                       # nonzero roots only can occur
        m = 0
        while len(c) > 1 and sum(cf * pow(r, i, p) for i, cf in enumerate(c)) % p == 0:
            q = [0] * (len(c) - 1)              # divide by (z - r)
            for i in range(len(c) - 1, 0, -1):
                q[i - 1] = c[i] % p
                c[i - 1] = (c[i - 1] + r * q[i - 1]) % p
            assert c[0] % p == 0
            c = q
            m += 1
        if m:
            out.append((((-r) % p, 1), m))
    if len(c) > 1:
        out.append((tuple(c), 1))               # deg 2/3 irreducible remainder
    return out


# ---------------- the window reader ----------------
def hull_sides(pts):
    """Lower-hull sides of exact points pts = [(j, h), ...] (j ascending).
    Returns [(j1, j2, drop)]: maximal collinear segments, descending only."""
    sides, cur = [], 0
    while cur < len(pts) - 1:
        j0, h0 = pts[cur]
        best, bs = None, None
        for k in range(cur + 1, len(pts)):
            s = Fraction(pts[k][1] - h0, pts[k][0] - j0)
            if bs is None or s < bs or (s == bs):
                if bs is None or s < bs:
                    best, bs = k, s
                else:
                    best = k                     # tie: extend (max collinear)
        assert bs <= 0, 'ascending hull side'
        sides.append((j0, pts[best][0], h0 - pts[best][1]))
        cur = best
    return sides


def read_data_one(hts, digs, W, root, hkey):
    """All reads of one completion. hts: exact heights per slot 0..W (None =
    absent); digs: digit per slot or 'X' (capped sentinel).  Returns
    ([(sidekey, datum)], faults).  datum = (e, l, a, flankL, flankR, rescoeffs,
    s0, hnum); rescoeffs entries may be 'X' (unstable across completions)."""
    pts = [(j, hts[j]) for j in range(W + 1) if hts[j] is not None]
    mn = min(h for _, h in pts)
    last = max(i for i, (_, h) in enumerate(pts) if h == mn)
    pts = pts[:last + 1]                         # descending part only
    if len(pts) < 2:
        return [], []
    sides = hull_sides(pts)
    faults = []
    lead = pts[0][0]
    widths = ([lead] if lead > 0 else []) + [j2 - j1 for j1, j2, _ in sides]
    out = []
    for i, (j1, j2, drop) in enumerate(sides):
        w_ = j2 - j1
        fr = Fraction(drop, w_)
        if not root and fr <= hkey:
            faults.append(((j1, j2), ('Iaug', j1, j2, str(fr), hkey)))
        e, hn = fr.denominator, fr.numerator
        if fr == 0:
            e, hn = 1, 0
        ell = w_ // e
        res = []
        for k in range(ell + 1):
            j = j1 + k * e
            line = hts[j1] - k * hn
            on = hts[j] is not None and hts[j] == line
            res.append(digs[j] if on else 0)
        a = j1 // e                              # extended-line slots left (FC4)
        pre = ([lead] if lead > 0 else [])
        fl = tuple(pre + [s[1] - s[0] for s in sides[:i]])
        frk = tuple(s[1] - s[0] for s in sides[i + 1:])
        out.append(((j1, j2),
                    (e, ell, a, fl, frk, tuple(res), j1, hn, hts[j1])))
    return out, faults


def classify_window(codes, W, N, p, root, hkey):
    """codes: per slot 0..W: None (absent/exact 0) or (vcap, dig) with
    vcap in 0..N (N = capped, dig then meaningless).  Returns
    (decided reads [(datum)], n_undecided_sidekeys, faults)."""
    capped = [j for j in range(W + 1) if codes[j] is not None and codes[j][0] >= N]
    vals = list(range(N, 4 * N - 2)) + [5 * N]
    seen, sidefaults = {}, {}
    ncomp = 0
    for comp in product(vals, repeat=len(capped)):
        ncomp += 1
        hts = [None] * (W + 1)
        digs = [0] * (W + 1)
        for j in range(W + 1):
            if codes[j] is None:
                continue
            v, d = codes[j]
            if v >= N:
                hts[j] = comp[capped.index(j)]
                digs[j] = 'X'
            else:
                hts[j], digs[j] = v, d
        reads, fl = read_data_one(hts, digs, W, root, hkey)
        for sk, ff in fl:
            sidefaults.setdefault(sk, ff)
        for sk, dat in reads:
            seen.setdefault(sk, []).append(dat)
    decided, undecided, faults = [], 0, []
    for sk, dats in seen.items():
        stable = (len(dats) == ncomp and all(d == dats[0] for d in dats)
                  and sk[0] not in capped and sk[1] not in capped
                  and 'X' not in dats[0][5])
        if stable:
            decided.append(dats[0])
            if sk in sidefaults:
                faults.append(sidefaults[sk])
        else:
            undecided += 1
    return decided, undecided, faults


IGROUP = {(1, 2): 'I22', (1, 3): 'I33', (2, 1): 'I21', (3, 1): 'I31'}
QGROUP = {1: 'Q1', 2: 'Q2', 3: 'Q3'}
GROUPW = {'R': 3, 'Q3': 3, 'Q2': 2, 'Q1': 1,
          'I21': 1, 'I22': 1, 'I31': 1, 'I33': 1}


def rows_from_reads(reads, group, p, W):
    """Reader data -> [(letterkey, branchspec)] + faults.  branchspec is
    None (W = 1 verdict, or depth-2 letters whose moves are not taken) or
    ('rec', hn, t_unit, mu, hmu) / ('inc', e, hn, g, psi, wf_e)."""
    rows, faults = [], []
    for (e, ell, a, fl, frk, res, s0, hn, u1) in reads:
        facs = fp_factor(res, p)
        lam = tuple(sorted((len(f) - 1, m) for f, m in facs))
        if sum(g * m for g, m in lam) != ell:
            faults.append(('partition', group, e, ell, lam))
            continue
        if W == 1:
            rows.append(((group, e, ell, a, fl, frk, lam, 'V'), None))
            continue
        for f, m in facs:
            g = len(f) - 1
            key = (group, e, ell, a, fl, frk, lam, (g, m))
            if e * g == 1:                       # recentering (D.10)
                r = (-f[0]) % p                  # psi = z - r, r != 0
                wf = u1 + s0 * hn
                rows.append((key, ('rec', hn, r, m, wf - m * hn)))
            else:                                # increment (D.5/D.8)
                wf_e = e * u1 + s0 * hn
                rows.append((key, ('inc', e, hn, g, f, wf_e)))
    return rows, faults


REC_MEMO, INC_MEMO, ROOT_MEMO = {}, {}, {}


def classify_rec(p, N, hn, hmu, mu, codes):
    """Depth-2 read after a recentering: window [0, mu], codes per slot.
    Returns (rows, n_undecided, faults, n_unverified)."""
    key = (p, N, hn, hmu, mu, codes)
    if key in REC_MEMO:
        return REC_MEMO[key]
    faults, unver = [], 0
    v = codes[mu][0]
    if v < N:
        if v != hmu:
            faults.append(('VERTEX', hn, hmu, mu, codes))
    elif N > hmu:
        faults.append(('VERTEX-cap', hn, hmu, mu, codes))
    else:
        unver += 1
    for j in range(mu):
        need = hmu + (mu - j) * hn               # (BOX): v(B'_j) > need
        vj = codes[j][0]
        if vj < N:
            if vj <= need:
                faults.append(('BOX', j, hn, hmu, mu, codes))
        elif N <= need:
            unver += 1
    reads, undec, rf = classify_window(codes, mu, N, p, False, hn)
    faults += rf
    rows, ff = rows_from_reads(reads, QGROUP[mu], p, mu)
    faults += ff
    out = (rows, undec, faults, unver)
    REC_MEMO[key] = out
    return out


def classify_inc(p, N, e, hn, g, wf_e, vq, comps):
    """Depth-2 confirming read after an increment.  comps: tuple of capped
    v_p's of B0's x-slots i = 0..; component value = e*v + i*hn.  vq =
    capped v_p(q0) (eg = 2) or None (eg = 3, B1 = 1).  Returns
    (rows, n_undecided, faults, n_unverified)."""
    key = (p, N, e, hn, g, wf_e, vq, comps)
    if key in INC_MEMO:
        return INC_MEMO[key]
    faults, unver = [], 0
    ehg = e * hn * g
    if vq is None:                               # B1 = 1: w(B1) = 0
        if wf_e != ehg:
            faults.append(('VERTEX-inc', e, hn, g, wf_e))
    else:                                        # B1 = x + q0
        w1 = min(e * vq, hn) if vq < N else (hn if hn <= e * N else None)
        if w1 is None:
            unver += 1
        elif w1 != wf_e - ehg:
            faults.append(('VERTEX-inc', e, hn, g, wf_e, vq))
    exact = [e * v + i * hn for i, v in enumerate(comps) if v < N]
    lb = [e * N + i * hn for i, v in enumerate(comps) if v >= N]
    if exact and (not lb or min(exact) <= min(lb)):
        if min(exact) <= wf_e:
            faults.append(('BOX-inc', e, hn, g, wf_e, comps))
        out = ([((IGROUP[(e, g)], 1, 1, 0, (), (), ((1, 1),), 'V'), None)],
               0, faults, unver)
    else:
        out = ([], 1, faults, unver)
    INC_MEMO[key] = out
    return out


def root_classify(p, N, codes):
    key = (p, N, codes)
    if key not in ROOT_MEMO:
        reads, undec, rf = classify_window(codes, 3, N, p, True, 0)
        rows, ff = rows_from_reads(reads, 'R', p, 3)
        ROOT_MEMO[key] = (rows, undec, rf + ff)
    return ROOT_MEMO[key]


def sealed_target(rk):
    """The sealed menu-map arm of a root row (group of the next read)."""
    _, e, _, _, _, _, _, sel = rk
    if e == 2:
        return 'I21'
    if e == 3:
        return 'I31'
    return {(1, 1): 'Q1', (1, 2): 'Q2', (1, 3): 'Q3',
            (2, 1): 'I22', (3, 1): 'I33'}[sel]


def census(p, N, catset):
    M, t0 = p ** N, time.time()
    K = (p - 1) * N + 1
    xs = np.arange(M, dtype=np.int64)
    v_tab = np.zeros(M, np.int16)
    for k in range(1, N):                        # ascending: deepest wins
        v_tab[xs % (p ** k) == 0] = k
    v_tab[xs % (p ** N) == 0] = N                # only x = 0 here
    assert all(int(v_tab[x]) == min(next(k for k in range(N + 1)
               if x % p ** (k + 1) or k == N), N) for x in
               list(range(min(M, 64))) + [0, p ** (N - 1), M - 1])
    d_tab = (xs // p ** np.minimum(v_tab, N - 1).astype(np.int64)) % p
    code_tab = np.where(v_tab >= N, K - 1,
                        v_tab * (p - 1) + (d_tab - 1)).astype(np.int16)

    def dec(code):
        code = int(code)
        return (N, 0) if code == K - 1 else (code // (p - 1),
                                             code % (p - 1) + 1)

    c1v = np.repeat(xs, M)
    c0v = np.tile(xs, M)
    sig01 = code_tab[c1v] * K + code_tab[c0v]
    order = np.argsort(sig01, kind='stable')
    uniq01, starts = np.unique(sig01[order], return_index=True)
    ends = np.append(starts[1:], M * M)
    c1s, c0s = c1v[order], c0v[order]
    del c1v, c0v, sig01, order
    hits, faults, trans, strays = {}, {}, {}, {}
    undec = {'root': 0, 'rec': 0, 'inc': 0}
    unver = 0

    def tally_child(rk, ck, n, exf):
        hits[ck] = hits.get(ck, 0) + n
        trans[(rk, ck)] = trans.get((rk, ck), 0) + n
        if ck not in catset and ck not in strays:
            strays[ck] = exf()

    for c2 in range(M):
        code2 = int(code_tab[c2])
        for gi in range(len(uniq01)):
            codes = (dec(uniq01[gi] % K), dec(uniq01[gi] // K),
                     dec(code2), (0, 1))
            rows, ud, rf = root_classify(p, N, codes)
            n = int(ends[gi] - starts[gi])
            undec['root'] += ud * n
            for ff in rf:
                faults[str(ff)] = faults.get(str(ff), 0) + n
            sl = slice(int(starts[gi]), int(ends[gi]))
            for rk, br in rows:
                hits[rk] = hits.get(rk, 0) + n
                if rk not in catset and rk not in strays:
                    strays[rk] = (c2, int(c1s[sl][0]), int(c0s[sl][0]))
                if br is None:
                    continue
                c1a, c0a = c1s[sl], c0s[sl]
                if br[0] == 'rec':
                    _, hn, r, mu, hmu = br
                    t = r * p ** hn
                    c2p = (c2 + 3 * t) % M
                    c1p = (c1a + 2 * c2 * t + 3 * t * t) % M
                    c0p = (c0a + c1a * t + c2 * t * t + t ** 3) % M
                    comb = code_tab[c0p] * K + code_tab[c1p]
                    uu, cc = np.unique(comb, return_counts=True)
                    for cb, n2 in zip(uu, cc):
                        ch = (dec(cb // K), dec(cb % K))
                        if mu >= 2:
                            ch += (dec(int(code_tab[c2p])),)
                        if mu == 3:
                            ch += ((0, 1),)
                        rows2, ud2, f2, uv2 = classify_rec(
                            p, N, hn, hmu, mu, ch)
                        n2 = int(n2)
                        undec['rec'] += ud2 * n2
                        unver += uv2 * n2
                        for ff in f2:
                            faults[str(ff)] = faults.get(str(ff), 0) + n2
                        def exf(cb=cb):
                            i0 = int(np.argmax(comb == cb))
                            return (c2, int(c1a[i0]), int(c0a[i0]))
                        for ck, _ in rows2:
                            tally_child(rk, ck, n2, exf)
                else:                            # increment branch
                    _, e, hn, g, psi, wf_e = br
                    if e * g == 2:               # deg Phi-hat = 2
                        A1 = (psi[1] * p ** hn) % M if g == 2 and psi[1] else 0
                        A0 = (psi[0] * p ** (g * hn)) % M
                        q0 = (c2 - A1) % M
                        r1 = (c1a - A0 - A1 * q0) % M
                        r0 = (c0a - A0 * q0) % M
                        vq = int(v_tab[q0])
                        comb = v_tab[r0] * (N + 1) + v_tab[r1]
                        uu, cc = np.unique(comb, return_counts=True)
                        for cb, n2 in zip(uu, cc):
                            comps = (int(cb) // (N + 1), int(cb) % (N + 1))
                            rows2, ud2, f2, uv2 = classify_inc(
                                p, N, e, hn, g, wf_e, vq, comps)
                            n2 = int(n2)
                            undec['inc'] += ud2 * n2
                            unver += uv2 * n2
                            for ff in f2:
                                faults[str(ff)] = faults.get(str(ff), 0) + n2
                            def exf(cb=cb):
                                i0 = int(np.argmax(comb == cb))
                                return (c2, int(c1a[i0]), int(c0a[i0]))
                            for ck, _ in rows2:
                                tally_child(rk, ck, n2, exf)
                    else:                        # deg Phi-hat = 3
                        if g == 3:
                            A2 = (psi[2] * p ** hn) % M if psi[2] else 0
                            A1 = (psi[1] * p ** (2 * hn)) % M if psi[1] else 0
                            A0 = (psi[0] * p ** (3 * hn)) % M
                        else:                    # e = 3, g = 1
                            A2, A1 = 0, 0
                            A0 = (psi[0] * p ** hn) % M
                        b2 = (c2 - A2) % M
                        b1 = (c1a - A1) % M
                        b0 = (c0a - A0) % M
                        vb2 = int(v_tab[b2])
                        comb = v_tab[b0] * (N + 1) + v_tab[b1]
                        uu, cc = np.unique(comb, return_counts=True)
                        for cb, n2 in zip(uu, cc):
                            comps = (int(cb) // (N + 1),
                                     int(cb) % (N + 1), vb2)
                            rows2, ud2, f2, uv2 = classify_inc(
                                p, N, e, hn, g, wf_e, None, comps)
                            n2 = int(n2)
                            undec['inc'] += ud2 * n2
                            unver += uv2 * n2
                            for ff in f2:
                                faults[str(ff)] = faults.get(str(ff), 0) + n2
                            def exf(cb=cb):
                                i0 = int(np.argmax(comb == cb))
                                return (c2, int(c1a[i0]), int(c0a[i0]))
                            for ck, _ in rows2:
                                tally_child(rk, ck, n2, exf)
    return dict(hits=hits, faults=faults, trans=trans, strays=strays,
                undec=undec, unver=unver, secs=round(time.time() - t0, 1))


def classify_one(p, N, c2, c1, c0):
    """Scalar depth-2 classification of one box (witness spot checks).
    Returns [(rootrow, [childletters])]."""
    M = p ** N

    def code(x):
        x %= M
        if x == 0:
            return (N, 0)
        v = 0
        while x % p == 0:
            x //= p
            v += 1
        return (v, x % p)
    rows, _, _ = root_classify(p, N, (code(c0), code(c1), code(c2), (0, 1)))
    out = []
    for rk, br in rows:
        chs = []
        if br and br[0] == 'rec':
            _, hn, r, mu, hmu = br
            t = r * p ** hn
            ch = (code(c0 + c1 * t + c2 * t * t + t ** 3),
                  code(c1 + 2 * c2 * t + 3 * t * t))
            if mu >= 2:
                ch += (code(c2 + 3 * t),)
            if mu == 3:
                ch += ((0, 1),)
            chs = [ck for ck, _ in classify_rec(p, N, hn, hmu, mu, ch)[0]]
        elif br:
            _, e, hn, g, psi, wf_e = br
            if e * g == 2:
                A1 = (psi[1] * p ** hn) if g == 2 and psi[1] else 0
                A0 = psi[0] * p ** (g * hn)
                q0 = (c2 - A1) % M
                comps = (code(c0 - A0 * q0)[0], code(c1 - A0 - A1 * q0)[0])
                chs = [ck for ck, _ in classify_inc(
                    p, N, e, hn, g, wf_e, code(q0)[0], comps)[0]]
            else:
                A2 = (psi[2] * p ** hn) if g == 3 and psi[2] else 0
                A1 = (psi[1] * p ** (2 * hn)) if g == 3 and psi[1] else 0
                A0 = psi[0] * p ** (g * hn) if g == 3 else psi[0] * p ** hn
                comps = (code(c0 - A0)[0], code(c1 - A1)[0], code(c2 - A2)[0])
                chs = [ck for ck, _ in classify_inc(
                    p, N, e, hn, g, wf_e, None, comps)[0]]
        out.append((rk, chs))
    return out


def lname(k):
    return (f'{k[0]}[e{k[1]} l{k[2]} a{k[3]} fl{list(k[4])}|{list(k[5])} '
            f'lam{list(k[6])} sel{k[7]}]')


LOOPSEAL = {('Q2', 1, 2, 0, (), (), ((1, 2),), (1, 2)),
            ('Q3', 1, 3, 0, (), (), ((1, 3),), (1, 3))}


def evaluate(p, N, res, cat, out):
    catset = set(cat)
    excl = excluded_letters(cat, p)
    predicted = [k for k in cat if k not in excl]
    realized = {k for k in catset if res['hits'].get(k, 0) > 0}
    orphans = [k for k in predicted if k not in realized]
    viol = sorted(k for k in excl if k in realized)
    offmenu = [(rk, ck, n) for (rk, ck), n in res['trans'].items()
               if ck[0] != sealed_target(rk)]
    loops = {k for k in realized if k[0] in ('Q2', 'Q3') and k[7] != 'V'
             and k[7] == (1, GROUPW[k[0]])}
    v = {'F1_strays': len(res['strays']) == 0,
         'F2_orphans': len(orphans) == 0,
         'F3_exclusions': len(viol) == 0,
         'F4_offmenu': len(offmenu) == 0,
         'F5_loops': loops == LOOPSEAL,
         'counts': len(realized) == {2: 42, 3: 51}[p],
         'engine_faults': len(res['faults']) == 0}
    out.append(f'\n== EVALUATION p={p} N={N} (box {p}^{3 * N} = {p ** (3 * N)};'
               f' census {res["secs"]}s) ==')
    out.append(f'  realized letters: {len(realized)}/53 (sealed '
               f'{ {2: 42, 3: 51}[p] }); excluded absent: '
               f'{len(excl) - len(viol)}/{len(excl)}')
    out.append(f'  F1 strays: {len(res["strays"])} '
               f'{[(lname(k), ex) for k, ex in list(res["strays"].items())[:4]]}'
               f' -> {"PASS" if v["F1_strays"] else "FAIL"}')
    out.append(f'  F2 orphans: {len(orphans)} {[lname(k) for k in orphans[:6]]}'
               f' -> {"PASS" if v["F2_orphans"] else "FAIL"}')
    out.append(f'  F3 exclusion violations: {len(viol)} '
               f'{[lname(k) for k in viol[:4]]}'
               f' -> {"PASS" if v["F3_exclusions"] else "FAIL"}')
    out.append(f'  F4 off-menu transitions: {len(offmenu)} '
               f'{[(lname(a), lname(b), n) for a, b, n in offmenu[:3]]}'
               f' -> {"PASS" if v["F4_offmenu"] else "FAIL"}')
    out.append(f'  F5 loop classes: {sorted(lname(k) for k in loops)} '
               f'-> {"PASS" if v["F5_loops"] else "FAIL"}')
    out.append(f'  realized-count == sealed -> '
               f'{"PASS" if v["counts"] else "FAIL"}')
    out.append(f'  engine faults (FC11, reported): {len(res["faults"])} '
               f'{list(res["faults"].items())[:4]} '
               f'{"(clean)" if v["engine_faults"] else "(NONZERO)"}')
    out.append(f'  undecided reads (reported): {res["undec"]}; '
               f'unverifiable-at-N landing checks: {res["unver"]}')
    return v, realized, orphans, viol, offmenu


def witness_checks(out):
    """SP.6's two displayed worked witnesses (p = 2), depth-2 arrows."""
    w = classify_one(2, 8, 1, 1, 2)              # x^3+x^2+x+2
    d = {rk: chs for rk, chs in w}
    r5 = ('R', 1, 2, 1, (1,), (), ((2, 1),), (2, 1))
    r1 = ('R', 1, 1, 0, (), (2,), ((1, 1),), (1, 1))
    w1 = (r5 in d and any(c[0] == 'I22' for c in d[r5]) and r1 in d)
    w2f = classify_one(2, 8, (-3) % 256, 3, (-3) % 256)  # (x-1)^3 - 2
    d2 = {rk: chs for rk, chs in w2f}
    r6 = ('R', 1, 3, 0, (), (), ((1, 3),), (1, 3))
    q3e3 = ('Q3', 3, 1, 0, (), (), ((1, 1),), (1, 1))
    w2 = (r6 in d2 and q3e3 in d2[r6])
    out.append(f'  witness 1 (x^3+x^2+x+2: R5 lam{{(2,1)}} sel(2,1) -> I(2,2),'
               f' + R1): {"PASS" if w1 else "FAIL"} [{[lname(k) for k in d]}]')
    out.append(f'  witness 2 ((x-1)^3-2: R6 sel(1,3) -> Q3 e=3 letter): '
               f'{"PASS" if w2 else "FAIL"}')
    return w1 and w2


def main():
    t0 = time.time()
    cat = build_catalogue()
    catset = set(cat)
    assert len(excluded_letters(cat, 2)) == 11    # sealed exclusion counts
    assert len(excluded_letters(cat, 3)) == 2
    out = ['SEALED GATE M-n3 CENSUS (seal: CASE_MN3_SEALED_PREDICTIONS.md, '
           'committed before this script existed)',
           'catalogue: 53 letters (21 R + 21 Q3 + 6 Q2 + 1 Q1 + 4 I); '
           'depth 2: root read + one continuation read per branch',
           '\n== SP.6 worked witnesses ==']
    wok = witness_checks(out)
    allv, alljson = {}, {}
    for p, N in CONFIGS:
        res = census(p, N, catset)
        v, realized, orphans, viol, offmenu = evaluate(p, N, res, cat, out)
        allv[f'p{p}'] = v
        out.append(f'  per-letter hits (catalogue order; 0* = sealed-excluded):')
        for k in cat:
            mark = '*' if k in excluded_letters(cat, p) else ''
            out.append(f'    {res["hits"].get(k, 0):>9}{mark}  {lname(k)}')
        out.append(f'  transitions ({len(res["trans"])} realized pairs):')
        for (rk, ck), n in sorted(res['trans'].items(),
                                  key=lambda x: -x[1]):
            out.append(f'    {n:>9}  {lname(rk)} -> {lname(ck)}')
        alljson[f'p{p}'] = dict(
            N=N, box=p ** (3 * N), secs=res['secs'],
            realized=len(realized), sealed_realized={2: 42, 3: 51}[p],
            hits={lname(k): res['hits'].get(k, 0) for k in cat},
            strays={lname(k): ex for k, ex in res['strays'].items()},
            orphans=[lname(k) for k in orphans],
            exclusion_violations=[lname(k) for k in viol],
            offmenu=[(lname(a), lname(b), n) for a, b, n in offmenu],
            transitions=[(lname(a), lname(b), n)
                         for (a, b), n in sorted(res['trans'].items())],
            undecided=res['undec'], unverified=res['unver'],
            engine_faults=res['faults'],
            verdicts={k: bool(x) for k, x in v.items()})
    gate = wok and all(all(v.values()) for v in allv.values())
    summary = ['=' * 72, 'SUMMARY — SEALED GATE M-n3:',
               f'  witnesses: {"PASS" if wok else "FAIL"}']
    for pk, v in allv.items():
        summary.append(f'  {pk}: ' + '  '.join(
            f'{k}:{"PASS" if x else "FAIL"}' for k, x in v.items()))
    summary.append(f'GATE VERDICT: {"PASS" if gate else "FAIL"}   '
                   f'(wall {time.time() - t0:.0f}s)')
    summary.append('=' * 72)
    out.extend(summary)
    os.makedirs(os.path.dirname(JSONPATH), exist_ok=True)
    with open(JSONPATH, 'w') as fh:
        json.dump(dict(seal='CASE_MN3_SEALED_PREDICTIONS.md',
                       witnesses=bool(wok), results=alljson,
                       gate='PASS' if gate else 'FAIL'), fh, indent=1)
    with open(OUTPATH, 'w') as fh:
        fh.write('\n'.join(out) + '\n')
    print('\n'.join(summary))
    return 0


if __name__ == '__main__':
    sys.exit(main())
