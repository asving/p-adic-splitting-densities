#!/usr/bin/env python3
"""GENTOW4 passPE1 FRESH instrument (hostile verifier's own code).

Out-of-battery frames stressing THEOREM GENTOW-4.A's partial-side
geometry, written independently from the note text (not from the
sealed runner's reader).  Exact integer arithmetic + dual PARI
oracles (sig1 = factor+idealprimedec, sig2 = factorpadic).

FR-G (gauge-live partial side; eta != 1, f2 = 2 -- NO battery family
  has this: P2 is f2 = 2 at q = 2 where eta = 1 forcibly):
  p = 3, Phi' = x^2 - 6 (outer genre (2,1,5), h = 1, eta = 2),
  inner (e2,f2) = (1,2), u2 = 3, psi2 = Z^2+Z+2, mu2 = 2 on side
  [1,5] slope 3 (PARTIAL: 4 < mu1 = 5), sibling slope 4 len 1.
  Keys: CORRECTED (GENHN erratum 59c1966 / HETOW [r1]):
    what_t = lift(c_t*eta^W(t)), W(t) = floor((f2-t)*i(u2)/e1):
    W(0) = 1, W(1) = 0 -> PHI2C = Phi'^2 - 6x*Phi' - 54.
  NAIVE (the note's S0 display, plain lifts): PHI2N = same - 27.
  Members f = fS*g, fS built at PHI2C (2SIDED and RAM shapes --
  trichotomy rows that need NO residual digits), g = x^2 - 15.
  CHECKS: level-1 hull; PARI sigma(f) exact both routes; corrected-
  key read gives mu2* = 2, c_g, floors, verdict = PARI; carrier:
  sigma(PHI2C) = {(2,2)}.  TEETH: sigma(PHI2N) != {(2,2)} (the key
  is not the carrier); naive-key development has EMPTY >T2 initial
  segment (mu2* = 0: the class is INVISIBLE at the note's displayed
  key); nfeltval: dv2(PHI2N) = E2 exactly at class factors (the
  GENTOW-1(d) field floor collapses), dv2(PHI2C) > E2 strict.

FR-M (two-block + maximal partiality; q = 2, eta = eta2 = 1, all
  displays gauge-clean -- pure partial-side-geometry stress):
  p = 2, Phi' = x^2 - 2, mu1 = 9, n = 18: hull
  (0,28)-(1,24)-(5,10)-(9,0): sibling slope 4 len 1 (g = x^2-6),
  side A [1,5] slope 7/2 carrying (T+1)^2 (u2 = 7, E2A = 14),
  side B [5,9] slope 5/2 carrying (T+1)^2 (u2 = 5, E2B = 10).
  TWO tower classes on TWO sides of one f (no battery member has
  two repeated classes); event length 4 vs mu1 = 9 (max partiality;
  battery max mu1 = 7).  Members: 3 label combos.  CHECKS: hull;
  both classes read through THEIR OWN keys: mu2* = 2 (GENTOW-4.2
  tie at two pure-power sides simultaneously), c_gA = 27 (includes
  block B's mass 20 + sibling 7), c_gB = 25, floors, per-class
  trichotomy = design; PARI sigma(f) = sigA u sigB u {(2,1)} both
  routes; nfeltval separator per key: class rows dv2(key) > E2
  strict, non-class rows <= E2.

FR-W (witness re-derivation): PE2P-0 = Phi'^5+4Phi'^4+32Phi'+64x
  at Phi2 = Phi'^2-4x: pins (28,16,5), c_g = 5, block pins (23,11),
  floors (21,11), 2SIDED, sigma {(2,1),(4,1),(4,1)} -- S1/S5's hand
  table re-derived by this independent code.
"""
import subprocess
import sys

NCHK = 0
NVIO = 0


def say(s):
    print(s)
    sys.stdout.flush()


def chk(tag, ok, msg):
    global NCHK, NVIO
    NCHK += 1
    if not ok:
        NVIO += 1
        say('VIOLATION [%s] %s' % (tag, msg))


# ---- dense integer polys, ascending ----
def pstrip(f):
    f = list(f)
    while len(f) > 1 and f[-1] == 0:
        f.pop()
    return f


def padd(f, g):
    n = max(len(f), len(g))
    return pstrip([(f[i] if i < len(f) else 0) +
                   (g[i] if i < len(g) else 0) for i in range(n)])


def pmul(f, g):
    r = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        if a:
            for j, b in enumerate(g):
                r[i + j] += a * b
    return pstrip(r)


def psca(c, f):
    return pstrip([c * v for v in f])


def ppow(g, k):
    r = [1]
    for _ in range(k):
        r = pmul(r, g)
    return r


def pdivmod_monic(f, g):
    f = list(f)
    dg = len(g) - 1
    assert g[-1] == 1
    q = [0] * max(1, len(f) - dg)
    for i in range(len(f) - 1, dg - 1, -1):
        c = f[i]
        if c:
            q[i - dg] += c
            for j, gj in enumerate(g):
                f[i - dg + j] -= c * gj
    return pstrip(q), pstrip(f[:dg])


def dev(f, key, times):
    g, out = list(f), []
    for _ in range(times):
        g, r = pdivmod_monic(g, key)
        out.append(r)
    return out, g


def vp(n, p):
    if n == 0:
        return None
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def poly_str(f):
    return '+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f)
                    if c) or '0'


def lower_hull(pts):
    hull = []
    for pt in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            if (y2 - y1) * (pt[0] - x1) >= (pt[1] - y1) * (x2 - x1):
                hull.pop()
            else:
                break
        hull.append(pt)
    return hull


# ---- frame-generic slot heights ----
# dv2-height of c * x^i * Phi'^b (i < e1=2, b < e2*f2) at the class:
#   m*vp(c) + i*(e2*h) + b*u2, with m = e1*e2, h = 1 throughout.
def pins_of_dev(p, PHI1, C_list, e2f2, e2, u2, m):
    pins = {}
    for j, Cj in enumerate(C_list):
        if not Cj:
            continue
        B, gg = dev(list(Cj), PHI1, e2f2)
        assert gg in ([], [0]), 'slot overflow'
        best = None
        for b, rb in enumerate(B):
            for i, c in enumerate(rb):
                if c:
                    ht = m * vp(c, p) + i * e2 + b * u2
                    if best is None or ht < best:
                        best = ht
        if best is not None:
            pins[j] = best
    return pins


def read_class(p, PHI1, f, key, e2, f2, u2, M):
    """Independent GENTOW-4.A(ii)+(v) pin read (no digits needed:
    only 2SIDED/RAM rows are exercised).  Returns dict."""
    m = 2 * e2
    T2 = e2 * f2 * u2
    C, g = dev(list(f), key, M + 1)
    assert g in ([], [0]), 'dev overflow'
    pins = pins_of_dev(p, PHI1, C, e2 * f2, e2, u2, m)
    if 0 not in pins:
        return {'status': 'PEEL'}
    hull = lower_hull(sorted(pins.items()))
    mu2s, cg = 0, None
    for k in range(len(hull) - 1):
        (j1, y1), (j2, y2) = hull[k], hull[k + 1]
        if (y1 - y2) > T2 * (j2 - j1):
            mu2s, cg = j2, y2
        else:
            break
    out = {'status': 'OK', 'mu2s': mu2s, 'cg': cg, 'pins': pins,
           'hull': hull}
    if mu2s != 2:
        return out
    p0, p1 = pins[0], pins.get(1)
    vertex1 = p1 is not None and any(v == (1, p1) for v in hull)
    if vertex1:
        out['verdict'] = '2SIDED'
    elif (p0 - cg) % 2 == 1:
        out['verdict'] = 'RAM'
    else:
        out['verdict'] = 'RESIDUAL'      # not exercised here
    return out


def level1_hull(p, PHI1, f, mu1):
    A, g = dev(list(f), PHI1, mu1)
    assert g == [1], 'not monic length mu1'
    pins = []
    for J, c in enumerate(A):
        vals = [2 * vp(cc, p) + i for i, cc in enumerate(c) if cc]
        if vals:
            pins.append((J, min(vals)))
    pins.append((mu1, 0))
    return lower_hull(pins)


# ---- gp ----
GP_HDR = r"""
default(parisizemax, 2000000000);
sig1(f, p) = {
  my(fa = factor(f), out = List());
  for (i = 1, matsize(fa)[1],
    my(g = fa[i, 1]);
    if (poldegree(g) == 1,
        listput(out, [1, 1]),
        my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
        for (j = 1, #dec, listput(out, [dec[j].e, dec[j].f]))));
  vecsort(Vec(out))
}
sig2(f, p) = {
  my(F = factorpadic(f, p, 400), out = List());
  for (i = 1, matsize(F)[1],
    my(g = liftall(F[i, 1]),
       nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
    for (j = 1, #dec, listput(out, [dec[j].e, dec[j].f])));
  vecsort(Vec(out))
}
keyval(f, p, K) = {
  my(fa = factor(f), out = List());
  for (i = 1, matsize(fa)[1],
    my(g = fa[i, 1]);
    if (poldegree(g) > 1,
      my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
      for (j = 1, #dec,
        listput(out, [dec[j].e, dec[j].f,
                      nfeltval(nf, Mod(K, g), dec[j])]))));
  Vec(out)
}
"""


def run_gp(lines):
    src = GP_HDR + '\n' + '\n'.join(lines) + '\nquit\n'
    out = subprocess.run(['gp', '-q', '-f'], input=src,
                         capture_output=True, text=True, timeout=1800)
    if out.stderr.strip():
        say('  gp stderr tail: %s' % out.stderr[-200:])
    res = {}
    for line in out.stdout.splitlines():
        parts = line.split(' ', 1)
        if len(parts) == 2 and parts[0]:
            res[parts[0]] = parts[1].strip()
    return res


def sig_parse(s):
    s = s.replace('[', ' ').replace(']', ' ').replace(',', ' ')
    nums = [int(t) for t in s.split()]
    return sorted((nums[i], nums[i + 1])
                  for i in range(0, len(nums), 2))


def tup_parse(s, k):
    s = s.replace('[', ' ').replace(']', ' ').replace(',', ' ')
    nums = [int(t) for t in s.split()]
    return [nums[i:i + k] for i in range(0, len(nums), k)]


def main():
    say('GENTOW4 passPE1 fresh instrument')
    jobs = []

    # ================= FR-G =================
    p = 3
    P1G = [-6, 0, 1]                     # x^2 - 6, eta = 2
    PHI2C = padd(padd(pmul(P1G, P1G), pmul([0, -6], P1G)), [-54])
    PHI2N = padd(padd(pmul(P1G, P1G), pmul([0, -6], P1G)), [-27])
    gG = [-15, 0, 1]                     # sibling, slope 4
    # block shapes at the CORRECTED key (dv2: p->2, x->1, Phi'->3)
    n7 = psca(27, [0, 1])                # 27x, height 7
    n13 = psca(729, [0, 1])              # 729x, height 13
    n15 = psca(2187, [0, 1])             # 2187x, height 15
    fS_2S = padd(padd(pmul(PHI2C, PHI2C), pmul(n7, PHI2C)), n15)
    fS_RAM = padd(pmul(PHI2C, PHI2C), n13)
    MG = [('FRG-2S', pmul(fS_2S, gG), '2SIDED',
           [(2, 1), (2, 2), (2, 2)]),
          ('FRG-RAM', pmul(fS_RAM, gG), 'RAM',
           [(2, 1), (4, 2)])]
    jobs.append('print("keyC ", sig1(%s, 3))' % poly_str(PHI2C))
    jobs.append('print("keyN ", sig1(%s, 3))' % poly_str(PHI2N))
    for tag, f, verd, sig in MG:
        hull = level1_hull(p, P1G, f, 5)
        chk(tag, hull == [(0, 16), (1, 12), (5, 0)],
            'level-1 hull %s' % hull)
        rc = read_class(p, P1G, f, PHI2C, 1, 2, 3, 2)
        chk(tag, rc['status'] == 'OK' and rc['mu2s'] == 2,
            'corrected-key mu2* = %s != 2' % rc.get('mu2s'))
        if rc.get('mu2s') == 2:
            chk(tag, rc['verdict'] == verd,
                'corrected verdict %s != %s' % (rc['verdict'], verd))
            cg = rc['cg']
            chk(tag, cg == 3, 'c_g %s != 3' % cg)
            for j in range(2):
                pj = rc['pins'].get(j)
                chk(tag, pj is None or pj - cg >= (2 - j) * 6 + 1,
                    'floor j=%d: %s' % (j, pj))
        rn = read_class(p, P1G, f, PHI2N, 1, 2, 3, 2)
        chk(tag, rn['status'] == 'OK' and rn['mu2s'] == 0,
            'TOOTH naive-key mu2* = %s (expect 0: class invisible)'
            % rn.get('mu2s'))
        say('%s: corrected pins %s hull %s | naive pins %s hull %s'
            % (tag, sorted(rc['pins'].items()), rc['hull'],
               sorted(rn['pins'].items()), rn['hull']))
        jobs.append('print("%s.s1 ", sig1(%s, 3))'
                    % (tag, poly_str(f)))
        jobs.append('print("%s.s2 ", sig2(%s, 3))'
                    % (tag, poly_str(f)))
        jobs.append('print("%s.d ", poldisc(%s) != 0)'
                    % (tag, poly_str(f)))
        jobs.append('print("%s.kC ", keyval(%s, 3, %s))'
                    % (tag, poly_str(f), poly_str(PHI2C)))
        jobs.append('print("%s.kN ", keyval(%s, 3, %s))'
                    % (tag, poly_str(f), poly_str(PHI2N)))

    # ================= FR-M =================
    q = 2
    P1M = [-2, 0, 1]
    KA = padd(pmul(P1M, P1M), psca(-1, psca(8, [0, 1])))   # Phi'^2-8x
    KB = padd(pmul(P1M, P1M), psca(-1, psca(4, [0, 1])))   # Phi'^2-4x
    gM = [-6, 0, 1]

    def n2(u2, mth):                     # q=2 ladder monomial
        for b in range(2):
            r = mth - b * u2
            if r < 0:
                continue
            for i in range(2):
                rr = r - i * 2
                if rr >= 0 and rr % 4 == 0:
                    return pmul([0] * i + [2 ** (rr // 4)],
                                ppow(P1M, b))
        return None

    def blockM(K, u2, lab):
        E2 = 2 * u2
        if lab == 'RAM':
            return padd(pmul(K, K), n2(u2, 2 * E2 + 1))
        if lab == '2SIDED':
            return padd(padd(pmul(K, K),
                             pmul(n2(u2, E2 + 1), K)),
                        n2(u2, 2 * E2 + 3))
        if lab == 'INERT':               # T^2+T+1 at slope E2+2
            return padd(padd(pmul(K, K),
                             pmul(n2(u2, E2 + 2), K)),
                        n2(u2, 2 * E2 + 4))
        raise ValueError(lab)

    SIG = {'RAM': [(8, 1)], '2SIDED': [(4, 1), (4, 1)],
           'INERT': [(4, 2)]}
    COMBOS = [('RAM', '2SIDED'), ('2SIDED', 'INERT'),
              ('INERT', 'RAM')]
    for la, lb in COMBOS:
        tag = 'FRM-%s-%s' % (la[:3], lb[:3])
        f = pmul(pmul(blockM(KA, 7, la), blockM(KB, 5, lb)), gM)
        hull = level1_hull(q, P1M, f, 9)
        chk(tag, hull == [(0, 28), (1, 24), (5, 10), (9, 0)],
            'level-1 hull %s' % hull)
        rA = read_class(q, P1M, f, KA, 2, 1, 7, 4)
        rB = read_class(q, P1M, f, KB, 2, 1, 5, 4)
        for (r, cg_want, lab, nm) in ((rA, 27, la, 'A'),
                                      (rB, 25, lb, 'B')):
            chk(tag, r['status'] == 'OK' and r['mu2s'] == 2,
                'class %s mu2* = %s != 2 (tie at two pure sides)'
                % (nm, r.get('mu2s')))
            if r.get('mu2s') != 2:
                continue
            chk(tag, r['cg'] == cg_want,
                'class %s c_g %s != %d' % (nm, r['cg'], cg_want))
            want_v = lab if lab != 'INERT' else 'RESIDUAL'
            chk(tag, r['verdict'] == want_v,
                'class %s verdict %s != %s'
                % (nm, r['verdict'], want_v))
            E2 = 14 if nm == 'A' else 10
            for j in range(2):
                pj = r['pins'].get(j)
                chk(tag, pj is None or
                    pj - r['cg'] >= (2 - j) * E2 + 1,
                    'class %s floor j=%d: %s' % (nm, j, pj))
        say('%s: A pins %s cg %s | B pins %s cg %s'
            % (tag, sorted(rA['pins'].items()), rA.get('cg'),
               sorted(rB['pins'].items()), rB.get('cg')))
        sig = sorted(SIG[la] + SIG[lb] + [(2, 1)])
        jobs.append('print("%s.s1 ", sig1(%s, 2))'
                    % (tag, poly_str(f)))
        jobs.append('print("%s.s2 ", sig2(%s, 2))'
                    % (tag, poly_str(f)))
        jobs.append('print("%s.d ", poldisc(%s) != 0)'
                    % (tag, poly_str(f)))
        jobs.append('print("%s.kA ", keyval(%s, 2, %s))'
                    % (tag, poly_str(f), poly_str(KA)))
        jobs.append('print("%s.kB ", keyval(%s, 2, %s))'
                    % (tag, poly_str(f), poly_str(KB)))
        globals().setdefault('WANTSIG', {})[tag] = sig

    # ================= FR-W =================
    PE2P0 = padd(padd(padd(ppow(P1M, 5), psca(4, ppow(P1M, 4))),
                      psca(32, P1M)), [0, 64])
    rW = read_class(q, P1M, PE2P0, KB, 2, 1, 5, 2)
    chk('FRW', rW['status'] == 'OK' and rW['mu2s'] == 2 and
        rW['cg'] == 5 and rW['verdict'] == '2SIDED' and
        sorted(rW['pins'].items()) == [(0, 28), (1, 16), (2, 5)],
        'witness table %s' % rW)
    chk('FRW', rW['pins'][0] - 5 >= 21 and rW['pins'][1] - 5 == 11,
        'witness floors')
    jobs.append('print("FRW.s1 ", sig1(%s, 2))' % poly_str(PE2P0))

    # ---- gp adjudication ----
    say('running gp (%d jobs)...' % len(jobs))
    res = run_gp(jobs)
    chk('FRG', sig_parse(res.get('keyC', '')) == [(2, 2)],
        'corrected key sigma %s != {(2,2)} (carrier)'
        % res.get('keyC'))
    chk('FRG', sig_parse(res.get('keyN', '')) != [(2, 2)],
        'TOOTH naive key IS the carrier (unexpected)')
    say('naive key sigma: %s (carrier is [(2,2)])'
        % res.get('keyN'))
    for tag, f, verd, sig in MG:
        chk(tag, res.get(tag + '.d') == '1', 'disc = 0')
        for rt in ('.s1', '.s2'):
            got = sig_parse(res.get(tag + rt, ''))
            chk(tag, got == sorted(sig),
                'sigma%s %s != %s' % (rt, got, sorted(sig)))
        # field floor: class rows (e,f)=(2,2): corrected strict,
        # naive collapses to E2 (dv2 = 2*val here: e=2 rows,
        # nfeltval in P-units; dv2(key) = (m/e_row)*val... use
        # m*val/e = 2*val/e * ... compare 2*val vs E2*e: e=2:
        # corrected > 12 <=> val > 6; naive val == 6.
        kc = tup_parse(res.get(tag + '.kC', ''), 3)
        kn = tup_parse(res.get(tag + '.kN', ''), 3)
        for (e_, f_, v_) in kc:
            if (e_, f_) != (2, 1):       # class rows
                chk(tag, 2 * v_ > 6 * e_,
                    'corrected key val %d not > E2 at (%d,%d)'
                    % (v_, e_, f_))
        for (e_, f_, v_) in kn:
            if (e_, f_) != (2, 1):
                chk(tag, 2 * v_ == 6 * e_,
                    'TOOTH naive key val %d != E2 exactly at '
                    '(%d,%d)' % (v_, e_, f_))
        say('%s: keyC vals %s | keyN vals %s' % (tag, kc, kn))
    for la, lb in COMBOS:
        tag = 'FRM-%s-%s' % (la[:3], lb[:3])
        chk(tag, res.get(tag + '.d') == '1', 'disc = 0')
        want = WANTSIG[tag]
        for rt in ('.s1', '.s2'):
            got = sig_parse(res.get(tag + rt, ''))
            chk(tag, got == want,
                'sigma%s %s != %s' % (rt, got, want))
        for (key_l, E2, other) in (('.kA', 14, [(8, 1), (4, 1),
                                                (4, 2)]),
                                   ('.kB', 10, None)):
            rows = tup_parse(res.get(tag + key_l, ''), 3)
            ncls = 0
            for (e_, f_, v_) in rows:
                dv2q = (4 // 1) * v_      # m = 4, dv2 = 4*v/e_row
                if 4 * v_ > E2 * e_:
                    ncls += e_ * f_
                else:
                    chk(tag, 4 * v_ <= E2 * e_, 'sep')
            chk(tag, ncls == 8,
                '%s class degree sum %d != 8 (= D2*mu2*)'
                % (key_l, ncls))
    chk('FRW', sig_parse(res.get('FRW.s1', '')) ==
        [(2, 1), (4, 1), (4, 1)], 'witness sigma %s'
        % res.get('FRW.s1'))

    say('')
    say('TOTAL: %d checks, %d violations' % (NCHK, NVIO))
    say('VERDICT: %s' % ('GREEN' if NVIO == 0 else 'RED'))


if __name__ == '__main__':
    main()
