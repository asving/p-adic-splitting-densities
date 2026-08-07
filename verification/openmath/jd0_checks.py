#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
jd0_checks.py -- SEALED BATTERY for JD0_PROOF_2026-08-08.md
(LEMMA J-D0: COUNT GAUGE-BLINDNESS -- the classifier stratum counts are
invariant under the carry gauge and blind to the entire value layer).

TWO-COMMIT SEAL.  Commit 1 = this runner + the note with its preregistered
predictions, battery UNRUN on the full roster; commit 2 = the verdict
appended to the note FROM the committed artifacts (jd0_checks_output.txt /
jd0_checks_results.json).  PRE-SEAL SMOKE DISCLOSED: the runner was
developed and debugged against the smoke subset {C2A, C2I, C2B, J7A, P2A,
P2B} (`--smoke`); observed on the smoke rows: all violation families 0,
all four teeth firing.  No full-roster run happened before the seal.
DEVICE PROBES DISCLOSED (pre-seal, on C2A only): realize-at-line anchor
re-choice works (wlev == line, read == target); realize at w-level 0 is
REFUSED by the engine's (I_m) invariant (beta >= e*g*gamma_m), which is
why the gauge is implemented by anchor RE-CHOICE at window lines, not by
val-0 unit multipliers.

WHAT IS KEYED (note section in brackets):

  JD0-PIN   md5 pins of the frozen imports (violation if moved).
  JD0-L3    [note S2, L3 leg]  residual-count gauge-blindness by FULL
            ENUMERATION: for every tower level j and degree D (D in
            {1,2,3}, capped at |K_j|^D <= 20000), every monic R in K_j[y]
            of degree D, and the seeded residual gauge xi != 1 (when
            |K_j| > 2): the gauged polynomial g(R) := xi^{-D} R(xi*y)
            (a) has the SAME factorization type as R (POINTWISE -- the
            load-bearing check; census equality is a corollary),
            (b) g is a bijection of the monic-degree-D family,
            (c) the per-type censuses agree, and (d) the letter-menu
            count (# monic irreducible with nonzero constant) agrees.
  JD0-COB   [note S2, L4 leg]  the carry gauge = anchor re-choice by a
            1-cochain u_gamma in K_top^*: gauged anchors a'_g :=
            realize(u_g * val(a_g), gamma) satisfy (1) wlev(a'_g) ==
            gamma (POSITIONS unmoved), (2) read(a'_g) == u_g*val(a_g)
            (the gauge acts on reads as the unit character), (3)
            wlev(a'_g * a'_g') == gamma+gamma' == the direct product's
            level, (4) the gauged carry c'(g,g') == c(g,g') *
            u_g u_g' u_{g+g'}^{-1} -- the carry moves by EXACTLY the
            coboundary du, (5) fuzz blindness: adding pi^3-junk of
            strictly higher w to a'_g changes neither wlev nor read.
            The integer layer (delta, S_j, D_j from T.constants) is
            split-only (consumes NO value); recorded, not scored.
  JD0-STRAT [note S3]  the assembled stratum-count record per tower
            (L3 censuses + letter-menu counts per level, polygon integer
            records, E/gam/wPhi, anchor-line record): the value-dependent
            legs recomputed THROUGH the gauge must reproduce the direct
            record -- count(direct) == count(gauged), per tower.
  JD0-BLIND [note S4]  >= 2 pairs of DIFFERENT towers with IDENTICAL
            shape data (p, d0, reads) but DIFFERENT letter-prices:
            (C2A, P1B) same shape, letters z_1 = Xbar vs Xbar^2;
            (P2A, P2B) p=7 wild (7,2,1), letters -1 (ord 2) vs -3 (ord 3);
            (P3A, P3B) p=3 depth-2 wild, letters 2 (ord 2) vs 1 (trivial).
            Checks: shape-equal (spec + realized gam/wPhi/E/G0 + polygon
            records), value-layer DIFFERS (letter tuples / letter order),
            stratum-count records EQUAL across the pair.

  TEETH (each must fire >= 1 GLOBALLY or the battery is RED):
  JD0-T-NONCHAR  the NON-character slot map gBAD(R) := g(R) + 1 (constant
                 bump; a bijection of the family that is NOT induced by a
                 unit character) must BREAK pointwise type preservation.
  JD0-T-NONUNIT  the NON-unit anchor rescaling pi * a_gamma must MOVE the
                 position (wlev changes) -- the gauge's unit condition is
                 load-bearing.
  JD0-T-COB      the corrupted coboundary (dropping u_{g+g'}^{-1}) must
                 break the carry-gauge law whenever u_{g+g'} != 1.
  JD0-T-SHAPE    the NEGATIVE-CONTROL pair (C2A, C2B) -- DIFFERENT shape
                 data -- must FAIL the count-record equality (the blind
                 comparison has teeth against shape drift).

ROSTER: grt_jc_probe.ROSTER imported FROZEN (29 rows: m <= 3, p in
{2,3,5}, d0 <= 3, wild legs, g_j = 2 branching, eq-char rows, I4A/I4B/
I4C) + the OUT-OF-ROSTER p = 7 GENRE (J7A wild (7,1,1); J7B d0=2 F49
with wild top (7,3,1); J7C g0=2 -> F49) + the constructed same-shape
pair members (P1B, P2A, P2B, P3A, P3B).  37 towers total.  Tower
construction is ITL.build_tower, the same code path the sealed J-C /
WELDMASTER batteries used.

GAUGE SEEDING: deterministic ("random nontrivial") -- every gauge unit is
drawn by md5(tower-id, tag, index) from K^* \ {1} when |K| > 2, else
forced 1 (F_2 levels: the residual gauge group is trivial; DISCLOSED --
those rows' JD0-COB still re-realizes anchors freshly, so the
representative-independence content survives; the per-tower census
reports whether the gauge was residue-nontrivial).

FROZEN-IMPORT PINS (JD0-PIN; violation if a pinned file's md5 moved):
  iterlawn_pe_reimpl.py  cae45db2318b89520dd5484466ef3604
  grt_jc_probe.py        03811b695cf7aa1bd5b52d5b0cd8bcd6

Exact arithmetic throughout (integers, finite-field tuples); no floating
point; deterministic (seeded md5 draws only).
"""

import sys, os, json, time, hashlib

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import iterlawn_pe_reimpl as ITL
import grt_jc_probe as JCP

PINS = {
    'iterlawn_pe_reimpl.py': 'cae45db2318b89520dd5484466ef3604',
    'grt_jc_probe.py':       '03811b695cf7aa1bd5b52d5b0cd8bcd6',
}

# ---------------------------------------------------------------- roster
P7_GENRE = [
    dict(id='J7A', ring='Zp', p=7, d0=1, Phi0=[0, 1],
         reads=[(7, 1, 1), (2, 1, 1)], psi=[[1, 1], [1, 1]]),
    dict(id='J7B', ring='Zp', p=7, d0=2, Phi0=[1, 0, 1],
         reads=[(2, 1, 1), (7, 3, 1)],
         psi=[[('X', 1), 1], [('z', 1, 1), 1]]),
    dict(id='J7C', ring='Zp', p=7, d0=1, Phi0=[0, 1],
         reads=[(2, 1, 2), (2, 1, 1)],
         psi=[[1, 0, 1], [('z', 1, 1), 1]]),
]

PAIR_MEMBERS = [
    dict(id='P1B', ring='Zp', p=2, d0=2, Phi0=[1, 1, 1],
         reads=[(2, 1, 1), (2, 1, 1)],
         psi=[[('X', 2), 1], [('z', 1, 1), 1]]),
    dict(id='P2A', ring='Zp', p=7, d0=1, Phi0=[0, 1],
         reads=[(7, 2, 1), (2, 1, 1)], psi=[[1, 1], [1, 1]]),
    dict(id='P2B', ring='Zp', p=7, d0=1, Phi0=[0, 1],
         reads=[(7, 2, 1), (2, 1, 1)], psi=[[3, 1], [1, 1]]),
    dict(id='P3A', ring='Zp', p=3, d0=1, Phi0=[0, 1],
         reads=[(3, 1, 1), (2, 1, 1), (2, 1, 1)],
         psi=[[1, 1], [1, 1], [1, 1]]),
    dict(id='P3B', ring='Zp', p=3, d0=1, Phi0=[0, 1],
         reads=[(3, 1, 1), (2, 1, 1), (2, 1, 1)],
         psi=[[2, 1], [1, 1], [1, 1]]),
]

# blind pairs: (idA, idB, must_be_equal)
BLIND_PAIRS = [('C2A', 'P1B', True), ('P2A', 'P2B', True),
               ('P3A', 'P3B', True), ('C2A', 'C2B', False)]  # last = tooth

SMOKE_IDS = ('C2A', 'C2I', 'C2B', 'J7A', 'P2A', 'P2B')

FAMILIES = ['JD0-PIN', 'JD0-L3', 'JD0-COB', 'JD0-STRAT', 'JD0-BLIND']
TEETH = ['JD0-T-NONCHAR', 'JD0-T-NONUNIT', 'JD0-T-COB', 'JD0-T-SHAPE']

VIOL = {f: [] for f in FAMILIES}
NCHK = {f: 0 for f in FAMILIES}
FIRE = {t: 0 for t in TEETH}
CENSUS = {'realize_skip': 0, 'pair_skip': 0, 'gauge_res_trivial_rows': [],
          'gauge_res_nontrivial_rows': [], 'l3_trivial_gauge_levels': 0,
          'l3_nontrivial_gauge_levels': 0}


def note(fam, n=1):
    NCHK[fam] += n


def viol(fam, tag, detail):
    VIOL[fam].append((tag, detail))
    print('  VIOLATION [%s] %s: %s' % (fam, tag, detail))


def seeded(tid, tag, idx, mod):
    """deterministic draw in [0, mod) from md5(tid|tag|idx)."""
    h = hashlib.md5(('%s|%s|%d' % (tid, tag, idx)).encode()).hexdigest()
    return int(h, 16) % mod


# ---------------------------------------------------------------- poly kit
# monic polys over a field K: tuples low->high incl. leading coeff (== one)
def pmul(K, f, g):
    out = [K.zero()] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        if K.is_zero(a):
            continue
        for j, b in enumerate(g):
            out[i + j] = K.add(out[i + j], K.mul(a, b))
    return tuple(out)


def peval(K, f, a):
    v = K.zero()
    for c in reversed(f):
        v = K.add(K.mul(v, a), c)
    return v


def pdiv_linear(K, f, a):
    """divide monic f by (y - a); returns quotient (assumes root)."""
    n = len(f) - 1
    q = [K.zero()] * n
    q[n - 1] = f[n]
    for i in range(n - 2, -1, -1):
        q[i] = K.add(f[i + 1], K.mul(a, q[i + 1]))
    return tuple(q)


def ptype(K, f, els):
    """factorization type of monic f, deg <= 3: sorted degree multiset."""
    deg = len(f) - 1
    assert 1 <= deg <= 3
    out = []
    g = f
    for a in els:
        while len(g) > 1 and K.is_zero(peval(K, g, a)):
            out.append(1)
            g = pdiv_linear(K, g, a)
        if len(g) == 1:
            break
    rd = len(g) - 1
    if rd > 0:
        # no roots and rd <= 3 => irreducible (rd in {2,3} only)
        out.append(rd)
    return tuple(sorted(out))


def monics(K, els, D):
    """all monic degree-D polys over K (generator of coeff tuples)."""
    import itertools
    one = K.one()
    for tail in itertools.product(els, repeat=D):
        yield tuple(tail) + (one,)


def gauge_poly(K, f, xi, xinv):
    """g(f) := xi^{-D} f(xi*y), monic when f is."""
    D = len(f) - 1
    out = []
    xp = K.one()                       # xi^i
    xd = K.one()                       # xinv^D
    for _ in range(D):
        xd = K.mul(xd, xinv)
    for i, c in enumerate(f):
        out.append(K.mul(K.mul(c, xp), xd))
        xp = K.mul(xp, xi)
    return tuple(out)


def fsig(K):
    """structural signature of a field object (for the census cache)."""
    if hasattr(K, 'base'):
        return ('EXT', fsig(K.base), repr(K.mod))
    return ('GF', K.p)


L3_CACHE = {}


def l3_level(tid, K, D, xi_idx_tag):
    """run the JD0-L3 checks for (field K, degree D) with a seeded gauge.
    Returns (census dict {type: count}, menu_count, gauged_menu_count,
             xi_nontrivial, tooth_fired)."""
    els = list(K.elems())
    r = len(els)
    units = [c for c in els if not K.is_zero(c)]
    # seeded gauge unit xi (nontrivial when possible)
    nontriv = [c for c in units if c != K.one()]
    if nontriv:
        xi = nontriv[seeded(tid, xi_idx_tag, D, len(nontriv))]
        xi_nt = True
    else:
        xi = K.one()
        xi_nt = False
    key = (fsig(K), D, xi)
    if key in L3_CACHE:
        return L3_CACHE[key]
    xinv = K.inv(xi)
    census, census_g = {}, {}
    menu, menu_g = 0, 0
    seen, seen_g = set(), set()
    tooth, nv = 0, 0
    one = K.one()
    for fidx, f in enumerate(monics(K, els, D)):
        t = ptype(K, f, els)
        gf = gauge_poly(K, f, xi, xinv)
        tg = ptype(K, gf, els)
        note('JD0-L3')
        if tg != t:
            nv += 1
            viol('JD0-L3', 'pointwise', 'field r=%d D=%d f=%s: type %s -> %s'
                 % (r, D, f, t, tg))
        census[t] = census.get(t, 0) + 1
        census_g[tg] = census_g.get(tg, 0) + 1
        seen.add(f)
        seen_g.add(gf)
        if t == (D,) and not K.is_zero(f[0]):
            menu += 1
        if tg == (D,) and not K.is_zero(gf[0]):
            menu_g += 1
        # tooth NONCHAR: constant bump breaks type preservation somewhere
        # (sampled: first 500 polys per family -- cost bound, disclosed)
        if fidx < 500:
            bad = (K.add(gf[0], one),) + gf[1:]
            if ptype(K, bad, els) != t:
                tooth += 1
    if seen_g != seen:
        nv += 1
        viol('JD0-L3', 'bijection', 'field r=%d D=%d: gauged family != family'
             % (r, D))
    note('JD0-L3', 2)
    if census_g != census:
        nv += 1
        viol('JD0-L3', 'census', 'field r=%d D=%d: %s vs %s'
             % (r, D, census, census_g))
    if menu_g != menu:
        nv += 1
        viol('JD0-L3', 'menu', 'field r=%d D=%d: %d vs %d'
             % (r, D, menu, menu_g))
    out = (census, menu, menu_g, xi_nt, tooth, nv)
    L3_CACHE[key] = out
    return out


# ---------------------------------------------------------------- tower kit
def build(spec):
    return ITL.build_tower(spec)


def window_G0(T, E, egg):
    G0 = ((egg + E - 1) // E) * E
    for _ in range(50):
        if all(T.inW(G0 + r) for r in range(E)):
            return G0
        G0 += E
    raise RuntimeError('no window found')


def pair_sample(tid, E):
    if E <= 6:
        return [(r1, r2) for r1 in range(E) for r2 in range(r1, E)]
    out, seen = [], set()
    i = 0
    while len(out) < 24 and i < 200:
        r1 = seeded(tid, 'pr1', i, E)
        r2 = seeded(tid, 'pr2', i, E)
        if (r1, r2) not in seen:
            seen.add((r1, r2))
            out.append((r1, r2))
        i += 1
    return out


def run_tower(spec):
    """all per-tower families; returns the stratum-count record."""
    tid = spec['id']
    T = build(spec)
    NR, P = T.NR, T.P
    K = T.K[NR]
    E = 1
    for e in T.e:
        E *= e
    egg = T.e[NR - 1] * T.g[NR - 1] * T.gam[NR]
    rec = {'id': tid, 'p': spec['p'], 'ring': spec['ring'],
           'd0': spec['d0'], 'reads': [list(r) for r in spec['reads']],
           'E': E, 'gam': T.gam[1:NR + 1], 'wPhi': T.wPhi[1:NR + 1]}

    # ---- JD0-L3 per level (letters live in K_j, j = 0..n)
    l3rec, menurec = [], []
    l3_nv = 0
    for j in range(NR):
        Kj = T.K[j]
        r = len(list(Kj.elems()))
        degs = [D for D in (1, 2, 3) if r ** D <= 20000]
        gj = T.g[j]
        if gj not in degs and r ** gj <= 20000:
            degs.append(gj)
        for D in degs:
            census, menu, menu_g, xi_nt, tooth, nv = l3_level(
                tid, Kj, D, 'xi:j%d' % j)
            l3_nv += nv
            l3rec.append([j, r, D, sorted(
                ('.'.join(map(str, t)), c) for t, c in census.items())])
            if D == gj:
                menurec.append([j, r, gj, menu])
            if xi_nt:
                CENSUS['l3_nontrivial_gauge_levels'] += 1
            else:
                CENSUS['l3_trivial_gauge_levels'] += 1
            FIRE['JD0-T-NONCHAR'] += tooth
    rec['L3'] = l3rec
    rec['menu'] = menurec

    # ---- polygon integer records (positions from the realized lifts)
    poly = []
    for j in range(NR):
        Phi_next = T.Phi[j + 1] if j + 1 <= T.n else T._build_lift(T.n)
        dv = P.dev(Phi_next, T.Phi[j])
        pts = [[i, T.wlev(j, A)] for i, A in enumerate(dv) if A]
        poly.append([j, pts])
    rec['polygon'] = poly

    # ---- JD0-COB: window, anchors, cochain, gauged anchors
    G0 = window_G0(T, E, egg)
    rec['G0'] = G0
    units = [c for c in list(K.elems()) if not K.is_zero(c)]
    nontriv = [c for c in units if c != K.one()]
    res_nt = bool(nontriv)
    (CENSUS['gauge_res_nontrivial_rows'] if res_nt else
     CENSUS['gauge_res_trivial_rows']).append(tid)

    def u_of(gamma, idx):
        if not nontriv:
            return K.one()
        # ~1/6 of draws trivial to exercise mixed cochains
        pool = nontriv + [K.one()]
        return pool[seeded(tid, 'u', gamma * 7919 + idx, len(pool))]

    anchors, vals, gauged, uco = {}, {}, {}, {}

    def prep(gamma, idx):
        if gamma in anchors:
            return True
        if not T.inW(gamma):
            CENSUS['pair_skip'] += 1
            return False
        a = T.tanch(gamma, T.n)
        w = T.wlev(NR, a)
        v = T.read(NR, gamma, a) if w == gamma else None
        if v is None or K.is_zero(v):
            CENSUS['realize_skip'] += 1
            return False
        u = u_of(gamma, idx)
        try:
            ag = T.realize(NR, K.mul(u, v), gamma, check=False)
        except Exception:
            CENSUS['realize_skip'] += 1
            return False
        anchors[gamma], vals[gamma], uco[gamma], gauged[gamma] = a, v, u, ag
        return True

    pairs = pair_sample(tid, E)
    scored = 0
    anchor_ok = True
    for (r1, r2) in pairs:
        ga, gb = G0 + r1, G0 + r2
        ss = ga + gb
        if not (prep(ga, r1) and prep(gb, r2) and prep(ss, r1 + E * r2)):
            continue
        aa, ab, ac = anchors[ga], anchors[gb], anchors[ss]
        Aa, Ab, Ac = gauged[ga], gauged[gb], gauged[ss]
        ua, ub, uc = uco[ga], uco[gb], uco[ss]
        va, vb, vc = vals[ga], vals[gb], vals[ss]
        # (1) positions unmoved by the gauge
        note('JD0-COB', 3)
        for g_, A_ in ((ga, Aa), (gb, Ab), (ss, Ac)):
            if T.wlev(NR, A_) != g_:
                viol('JD0-COB', 'pos', '%s: wlev(gauged anchor@%d) moved'
                     % (tid, g_))
                anchor_ok = False
        # (2) gauge acts on reads as the unit character
        note('JD0-COB', 2)
        if T.read(NR, ga, Aa) != K.mul(ua, va):
            viol('JD0-COB', 'char', '%s@%d' % (tid, ga))
        if T.read(NR, gb, Ab) != K.mul(ub, vb):
            viol('JD0-COB', 'char', '%s@%d' % (tid, gb))
        # (3) product line direct == gauged == ga+gb
        note('JD0-COB', 2)
        wd = T.wlev(NR, P.mul(aa, ab))
        wg = T.wlev(NR, P.mul(Aa, Ab))
        if wd != ss:
            viol('JD0-COB', 'prodline-direct', '%s (%d,%d): %s' %
                 (tid, ga, gb, wd))
            continue
        if wg != ss:
            viol('JD0-COB', 'prodline-gauged', '%s (%d,%d): %s' %
                 (tid, ga, gb, wg))
            continue
        # (4) carry coboundary law
        num = T.read(NR, ss, P.mul(aa, ab))
        c_dir = K.mul(num, K.inv(vc))
        numg = T.read(NR, ss, P.mul(Aa, Ab))
        c_g = K.mul(numg, K.inv(T.read(NR, ss, Ac)))
        expect = K.mul(c_dir, K.mul(K.mul(ua, ub), K.inv(uc)))
        note('JD0-COB')
        if c_g != expect:
            viol('JD0-COB', 'cob', '%s (%d,%d)' % (tid, ga, gb))
        # tooth JD0-T-COB: drop u_{g+g'}^{-1}
        wrong = K.mul(c_dir, K.mul(ua, ub))
        if uc != K.one() and c_g != wrong:
            FIRE['JD0-T-COB'] += 1
        # (5) fuzz blindness (higher-w junk invisible to position + read)
        note('JD0-COB', 2)
        Af = P.add(Aa, P.scal(T.R.pi_pow(3), Aa))
        if T.wlev(NR, Af) != ga:
            viol('JD0-COB', 'fuzz-pos', '%s@%d' % (tid, ga))
        if T.read(NR, ga, Af) != K.mul(ua, va):
            viol('JD0-COB', 'fuzz-read', '%s@%d' % (tid, ga))
        # integer layer record (split-only; recorded, not scored)
        cst = T.constants(ga, gb)
        scored += 1
        if scored == 1:
            rec['int_layer_sample'] = {
                'pair': [ga, gb], 'delta': cst['delta'],
                'D': cst['D'][1:NR], 'S': cst['S'][0:NR]}
        # tooth JD0-T-NONUNIT (once per tower, first scored pair)
        if scored == 1:
            note('JD0-COB')
            if T.wlev(NR, P.scal(T.R.pi_pow(1), aa)) != ga:
                FIRE['JD0-T-NONUNIT'] += 1
            else:
                viol('JD0-COB', 'tooth-nonunit-dead',
                     '%s: pi*anchor did not move' % tid)
    rec['cob_pairs_scored'] = scored
    rec['gauge_res_nontrivial'] = res_nt
    if scored == 0:
        viol('JD0-COB', 'empty', '%s: no scorable pair' % tid)

    # ---- JD0-STRAT: assembled record, direct vs gauged
    # (the value-dependent legs above were recomputed through the gauge;
    #  the assembled equality is: L3 censuses + menu counts (gauged ==
    #  direct, checked in l3_level) AND anchor lines (gauged == direct,
    #  checked in (1)/(3)).  Score the assembly per tower.)
    note('JD0-STRAT')
    strat_ok = (anchor_ok and scored > 0 and l3_nv == 0)
    if not strat_ok:
        viol('JD0-STRAT', 'assembly', tid)
    rec['strat_gauge_equal'] = strat_ok
    return rec


# ---------------------------------------------------------------- blind leg
def shape_record(rec):
    """the SHAPE-ONLY projection of a stratum-count record: everything the
    count consumes (integer positions + censuses + menu counts + weights);
    letters/carry values appear NOWHERE."""
    return {'p': rec['p'], 'd0': rec['d0'], 'reads': rec['reads'],
            'E': rec['E'], 'gam': rec['gam'], 'wPhi': rec['wPhi'],
            'G0': rec['G0'], 'polygon': rec['polygon'],
            'L3': rec['L3'], 'menu': rec['menu']}


def letters_of(spec):
    T = build(spec)
    out = []
    for j in range(1, T.NR + 1):
        z = T.z[j]
        # multiplicative order (invariant across representations)
        o, acc = 1, z
        while acc != T.K[j].one():
            acc = T.K[j].mul(acc, z)
            o += 1
            assert o <= 4096
        out.append((repr(z), o))
    return out


def run_blind(records):
    for (ida, idb, want_eq) in BLIND_PAIRS:
        if ida not in records or idb not in records:
            continue
        ra, rb = records[ida], records[idb]
        sa, sb = shape_record(ra), shape_record(rb)
        eq = (sa == sb)
        note('JD0-BLIND')
        if want_eq:
            if not eq:
                keys = [k for k in sa if sa[k] != sb[k]]
                viol('JD0-BLIND', 'count-mismatch',
                     '(%s,%s) differ at %s' % (ida, idb, keys))
        else:
            if eq:
                viol('JD0-BLIND', 'tooth-shape-dead',
                     '(%s,%s) unexpectedly equal' % (ida, idb))
            else:
                FIRE['JD0-T-SHAPE'] += 1


def verify_letters_differ(specs):
    """the same-shape pairs must have genuinely different letter-prices."""
    by_id = {s['id']: s for s in specs}
    out = {}
    for (ida, idb, want_eq) in BLIND_PAIRS:
        if not want_eq or ida not in by_id or idb not in by_id:
            continue
        la, lb = letters_of(by_id[ida]), letters_of(by_id[idb])
        differs = (la != lb)
        out['%s|%s' % (ida, idb)] = {
            'letters_A': la, 'letters_B': lb, 'differs': differs}
        note('JD0-BLIND')
        if not differs:
            viol('JD0-BLIND', 'letters-equal',
                 '(%s,%s): pair is vacuous' % (ida, idb))
    return out


# ---------------------------------------------------------------- main
def main(smoke=False):
    t0 = time.time()
    print('JD0 SEALED BATTERY -- %s mode' % ('SMOKE' if smoke else 'FULL'))
    # pins
    for fn, want in PINS.items():
        note('JD0-PIN')
        got = hashlib.md5(open(os.path.join(HERE, fn), 'rb').read()
                          ).hexdigest()
        if got != want:
            viol('JD0-PIN', fn, '%s != %s' % (got, want))
    specs = [dict(s) for s in JCP.ROSTER] + P7_GENRE + PAIR_MEMBERS
    if smoke:
        specs = [s for s in specs if s['id'] in SMOKE_IDS]
    print('roster: %d towers: %s' % (len(specs),
                                     ','.join(s['id'] for s in specs)))
    records = {}
    for s in specs:
        t1 = time.time()
        try:
            records[s['id']] = run_tower(s)
            print('  [%s] done (%.1fs, cob pairs %d, res-gauge %s)'
                  % (s['id'], time.time() - t1,
                     records[s['id']]['cob_pairs_scored'],
                     'NT' if records[s['id']]['gauge_res_nontrivial']
                     else 'trivial'))
        except Exception as ex:
            viol('JD0-COB', 'build/run', '%s: %s: %s'
                 % (s['id'], type(ex).__name__, ex))
    letters = verify_letters_differ(specs)
    run_blind(records)

    nviol = sum(len(v) for v in VIOL.values())
    teeth_ok = all(FIRE[t] >= 1 for t in TEETH) if not smoke else \
        all(FIRE[t] >= 1 for t in
            ('JD0-T-NONCHAR', 'JD0-T-NONUNIT', 'JD0-T-COB', 'JD0-T-SHAPE'))
    verdict = 'GREEN' if (nviol == 0 and teeth_ok) else 'RED'
    summary = {
        'mode': 'smoke' if smoke else 'full',
        'towers': len(records), 'verdict': verdict,
        'checks': NCHK, 'violations': {f: len(VIOL[f]) for f in FAMILIES},
        'violation_detail': {f: VIOL[f][:50] for f in FAMILIES},
        'teeth_fires': FIRE, 'census': CENSUS,
        'blind_letters': letters,
        'records': {k: records[k] for k in records},
        'elapsed_s': round(time.time() - t0, 1),
    }
    tag = '_smoke' if smoke else ''
    with open(os.path.join(HERE, 'jd0_checks_results%s.json' % tag),
              'w') as fh:
        json.dump(summary, fh, indent=1, default=repr)
    lines = ['JD0 BATTERY VERDICT: %s' % verdict,
             'towers: %d   checks: %s' % (len(records), sum(
                 NCHK.values())),
             'violations: ' + ' '.join('%s=%d' % (f, len(VIOL[f]))
                                       for f in FAMILIES),
             'teeth: ' + ' '.join('%s=%d' % (t, FIRE[t]) for t in TEETH),
             'gauge census: res-nontrivial rows=%d, res-trivial rows=%d, '
             'L3 nontrivial levels=%d, trivial levels=%d' % (
                 len(CENSUS['gauge_res_nontrivial_rows']),
                 len(CENSUS['gauge_res_trivial_rows']),
                 CENSUS['l3_nontrivial_gauge_levels'],
                 CENSUS['l3_trivial_gauge_levels']),
             'skips: realize=%d pair=%d' % (CENSUS['realize_skip'],
                                            CENSUS['pair_skip']),
             'elapsed: %.1fs' % (time.time() - t0)]
    print('\n'.join(lines))
    if not smoke:
        with open(os.path.join(HERE, 'jd0_checks_output.txt'), 'w') as fh:
            fh.write('\n'.join(lines) + '\n')
    return 0 if verdict == 'GREEN' else 1


if __name__ == '__main__':
    sys.exit(main(smoke='--smoke' in sys.argv))
