#!/usr/bin/env python3
"""GENTOW4 passPE2 FRESH instrument (hostile verifier's own code,
written independently of the sealed runner and of the PE1 instrument;
frames disjoint from the battery and from FR-G/FR-M/FR-W).

FR-T (f2 = 3 at odd p, eta != 1 -- FIRST frame in any leg with a
  NON-LINEAR wrap profile: W(t) = floor((3-t)*i(u2)/e1) = (1,1,0),
  which no single rescale can absorb; every prior eta != 1 contact
  had f2 = 2, i.e. one live W value):
  p = 3, Phi' = x^2 - 6 (genre (2,1,7), h = 1, eta = 2), inner
  (e2,f2) = (1,3), u2 = 3, psi2 = Z^3 - Z + 1 (irreducible /F3),
  mu2 = 2 on side [1,7] slope 3 -- PARTIAL (6 < mu1 = 7); sibling
  g = x^2 - 15 (slope 4, length 1).  Hand-derived keys:
    c2,c1,c0 = 0,1,2 ; Q(3) = 1 ; nhat(9),nhat(6),nhat(3) = 81x,27,3x
    CORRECTED KT = Phi'^3 - 54*Phi' - 81x
      (t=1: lift(c1*eta^1)=2 -> 2*27; t=0: lift(c0*eta^1)=lift(4)=1)
    NAIVE     KN = Phi'^3 - 27*Phi' - 162x   (plain lifts 1, 2)
    RESCALE   KL = Phi'^3 - 54*Phi' - 162x   (the wrap-corrected key
      OF the lam = 2 K^x-RESCALED datum: c_t' = c_t*lam^{t-f2} =
      (1,1), rtilde' = minpoly(2*beta) = Z^3 - Z - 2; a CARRIER --
      2*beta generates the same field -- but a DIFFERENT datum:
      2*beta is not in beta's Galois orbit (beta^3 = beta + 1,
      beta^9 = beta + 2 from rtilde = Z^3 - Z - 1))
  PREREG: sigma(KT) = {(2,3)} = carrier; sigma(KL) = {(2,3)} (still
  an irreducible letter, same field -- the carrier test sigma(key)
  = {(e1e2,f1f2)} does NOT certify the datum key); sigma(KN) =
  {(2,1),(2,2)} (the naive skewed letter poly Z^3 - 2Z - 2 =
  (Z-1)(Z^2+Z+2) /F3);
  members read at KT: mu2* = 2, c_g = 3, floors ((2-j)*9+1 = 19,10;
  j=1 EXACT), verdict = design, sigma = PARI dual routes; at KN AND
  at KL: mu2* = 0 (empty >T2 segment -- class invisible at the
  wrong gauge AND at the rescaled datum); nfeltval: class rows
  2v > 9e strict at KT with class degree sum = 12 = D2*mu2*, class
  rows 2v = 9e EXACTLY at KN (field-floor collapse).
  Members: fS*g, fS = KT^2 + 243*KT + 59049x (2SIDED, pins
  (0,21),(1,10),(2,0), slopes 11,10) and KT^2 + 59049x (RAM, slope
  21/2); sigma = {(2,1),(2,3),(2,3)} resp. {(2,1),(4,3)}.

FR-C (the gauge-live TWO-BLOCK compound -- PE1's two firsts
  combined, first anywhere: eta != 1 AND two repeated classes on
  two sides of one f):
  p = 3, Phi' = x^2 - 6 (genre (2,1,9), h = 1, eta = 2), n = 18;
  side A [1,5] slope 5: (e2,f2) = (1,2), u2 = 5, psi2A = Z^2+Z+2,
    W = (1,0), KA = Phi'^2 - 18x*Phi' - 486 (naive KAN = .. - 243),
    T2A = 10;
  side B [5,9] slope 3: (e2,f2) = (1,2), u2 = 3, psi2B = Z^2+2Z+2,
    W = (1,0), KB = Phi'^2 - 3x*Phi' - 54 (naive KBN = .. - 27),
    T2B = 6;
  sibling g = x^2 - 33 (slope 6, length 1).  Level-1 hull
  (0,38),(1,32),(5,12),(9,0).
  PREREG: sigma(KA) = sigma(KB) = {(2,2)} (hand: rtilde = Z^2+Z+2
  both, irreducible); sigma(KAN), sigma(KBN) != {(2,2)} (naive
  letter polys degenerate: (Z+2)^2 both); members (3 combos of
  2SIDED/RAM blocks): class A reads at KA with mu2* = 2, c_g = 17,
  floors ((2-j)*10+1; j=1 EXACT), class B at KB with mu2* = 2,
  c_g = 15, floors ((2-j)*6+1; j=1 EXACT), verdicts = design,
  sigma = PARI dual routes; naive keys: mu2* = 0 at BOTH classes;
  nfeltval: at KA class-A rows 2v > 10e strict, degree sum 8; at KB
  class-B rows 2v > 6e strict, degree sum 8; naive keys collapse
  (class rows 2v = E2*e exactly).
  Blocks: A-2S = KA^2 + 243x*KA + 177147x (pins (0,23),(1,11)),
  A-RAM = KA^2 + 177147x; B-2S = KB^2 + 27x*KB + 2187x, B-RAM =
  KB^2 + 2187x.  Block sigmas: 2S {(2,2)}x2, RAM {(4,2)}.

All arithmetic exact integers; PARI dual oracles (factor +
idealprimedec; factorpadic) adjudicate every sigma.
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


# ---- dense integer polys (ascending) ----
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


# ---- level-1 hull (dv = 2*v3(c) + i, h = 1, e1 = 2) ----
def level1_hull(p, PHI1, f, mu1):
    A, g = dev(list(f), PHI1, mu1)
    assert g == [1], 'not monic of level-1 length mu1'
    pins = []
    for J, c in enumerate(A):
        vals = [2 * vp(cc, p) + i for i, cc in enumerate(c) if cc]
        if vals:
            pins.append((J, min(vals)))
    pins.append((mu1, 0))
    return lower_hull(pins)


# ---- composed pins + initial-segment read (e2 = 1 frames: dv2 = dv;
#      slot height of c*x^i*Phi'^b = 2*vp(c) + i + b*u2) ----
def read_class(p, PHI1, f, key, e2f2, u2, M):
    T2 = e2f2 * u2
    C, g = dev(list(f), key, M + 1)
    assert g in ([], [0]), 'dev overflow'
    pins = {}
    for j, Cj in enumerate(C):
        if not Cj:
            continue
        B, gg = dev(list(Cj), PHI1, e2f2)
        assert gg in ([], [0]), 'slot overflow'
        vals = [2 * vp(c, p) + i + b * u2
                for b, rb in enumerate(B) for i, c in enumerate(rb)
                if c]
        if vals:
            pins[j] = min(vals)
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
    p1 = pins.get(1)
    if p1 is not None and any(v == (1, p1) for v in hull):
        out['verdict'] = '2SIDED'
    elif (pins[0] - cg) % 2 == 1:
        out['verdict'] = 'RAM'
    else:
        out['verdict'] = 'RESIDUAL'   # digit branch: NOT exercised
    return out


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


def keyval_checks(tag, lab, rows, E2, strict, want_sum):
    """class rows := rows with 2v > E2*e; strict => expect them
    strict and degree-sum = want_sum; collapse => expect the rows
    NOT below E2 to sit at 2v = E2*e exactly and still sum to
    want_sum (the collapse tooth: class rows land ON the floor)."""
    ncls = 0
    for (e_, f_, v_) in rows:
        if strict:
            if 2 * v_ > E2 * e_:
                ncls += e_ * f_
        else:
            if 2 * v_ >= E2 * e_:
                if 2 * v_ == E2 * e_:
                    ncls += e_ * f_
                else:
                    chk(tag, False,
                        '%s naive row (%d,%d,v=%d) ABOVE E2 = %d'
                        % (lab, e_, f_, v_, E2))
    chk(tag, ncls >= want_sum, '%s %s rows degree sum %d < %d'
        % (lab, 'strict' if strict else 'at-E2', ncls, want_sum))


def main():
    say('GENTOW4 passPE2 fresh instrument (FR-T f2=3 nonlinear-W; '
        'FR-C gauge-live two-block)')
    p = 3
    P1 = [-6, 0, 1]                                # Phi' = x^2-6
    jobs = []

    # ================= FR-T =================
    KT = padd(padd(pmul(pmul(P1, P1), P1), psca(-54, P1)), [0, -81])
    KN = padd(padd(pmul(pmul(P1, P1), P1), psca(-27, P1)), [0, -162])
    KL = padd(padd(pmul(pmul(P1, P1), P1), psca(-54, P1)), [0, -162])
    gT = [-15, 0, 1]
    fS_2S = padd(padd(pmul(KT, KT), psca(243, KT)), [0, 59049])
    fS_RAM = padd(pmul(KT, KT), [0, 59049])
    MT = [('FRT-2S', pmul(fS_2S, gT), '2SIDED',
           [(2, 1), (2, 3), (2, 3)]),
          ('FRT-RAM', pmul(fS_RAM, gT), 'RAM', [(2, 1), (4, 3)])]
    jobs.append('print("KT ", sig1(%s, 3))' % poly_str(KT))
    jobs.append('print("KL ", sig1(%s, 3))' % poly_str(KL))
    jobs.append('print("KN ", sig1(%s, 3))' % poly_str(KN))
    for tag, f, verd, sig in MT:
        hull = level1_hull(p, P1, f, 7)
        chk(tag, hull == [(0, 22), (1, 18), (7, 0)],
            'level-1 hull %s' % hull)
        rc = read_class(p, P1, f, KT, 3, 3, 2)
        chk(tag, rc['status'] == 'OK' and rc.get('mu2s') == 2,
            'corrected mu2* = %s != 2' % rc.get('mu2s'))
        if rc.get('mu2s') == 2:
            chk(tag, rc['verdict'] == verd,
                'verdict %s != %s' % (rc['verdict'], verd))
            chk(tag, rc['cg'] == 3, 'c_g %s != 3' % rc['cg'])
            for j, fl in ((0, 19), (1, 10)):
                pj = rc['pins'].get(j)
                chk(tag, pj is None or pj - 3 >= fl,
                    'floor j=%d: %s - 3 < %d' % (j, pj, fl))
        rn = read_class(p, P1, f, KN, 3, 3, 2)
        chk(tag, rn['status'] == 'OK' and rn.get('mu2s') == 0,
            'TOOTH naive mu2* = %s (want 0)' % rn.get('mu2s'))
        rl = read_class(p, P1, f, KL, 3, 3, 2)
        chk(tag, rl['status'] == 'OK' and rl.get('mu2s') == 0,
            'TOOTH rescaled-key mu2* = %s (want 0)' % rl.get('mu2s'))
        say('%s: KT pins %s | KN pins %s | KL pins %s'
            % (tag, sorted(rc['pins'].items()),
               sorted(rn['pins'].items()), sorted(rl['pins'].items())))
        for nm, K in (('kT', KT), ('kN', KN)):
            jobs.append('print("%s.%s ", keyval(%s, 3, %s))'
                        % (tag, nm, poly_str(f), poly_str(K)))
        jobs.append('print("%s.s1 ", sig1(%s, 3))' % (tag, poly_str(f)))
        jobs.append('print("%s.s2 ", sig2(%s, 3))' % (tag, poly_str(f)))
        jobs.append('print("%s.d ", poldisc(%s) != 0)'
                    % (tag, poly_str(f)))

    # ================= FR-C =================
    KA = padd(padd(pmul(P1, P1), pmul([0, -18], P1)), [-486])
    KAN = padd(padd(pmul(P1, P1), pmul([0, -18], P1)), [-243])
    KB = padd(padd(pmul(P1, P1), pmul([0, -3], P1)), [-54])
    KBN = padd(padd(pmul(P1, P1), pmul([0, -3], P1)), [-27])
    gC = [-33, 0, 1]
    fA = {'2S': padd(padd(pmul(KA, KA), pmul([0, 243], KA)),
                     [0, 177147]),
          'RAM': padd(pmul(KA, KA), [0, 177147])}
    fB = {'2S': padd(padd(pmul(KB, KB), pmul([0, 27], KB)),
                     [0, 2187]),
          'RAM': padd(pmul(KB, KB), [0, 2187])}
    BSIG = {'2S': [(2, 2), (2, 2)], 'RAM': [(4, 2)]}
    for nm, K in (('KA', KA), ('KB', KB), ('KAN', KAN), ('KBN', KBN)):
        jobs.append('print("%s ", sig1(%s, 3))' % (nm, poly_str(K)))
    COMBOS = [('2S', 'RAM'), ('RAM', '2S'), ('2S', '2S')]
    MC = []
    for la, lb in COMBOS:
        tag = 'FRC-%s-%s' % (la, lb)
        f = pmul(pmul(fA[la], fB[lb]), gC)
        MC.append((tag, f, la, lb))
        hull = level1_hull(p, P1, f, 9)
        chk(tag, hull == [(0, 38), (1, 32), (5, 12), (9, 0)],
            'level-1 hull %s' % hull)
        for (K, KNv, e2f2, u2, cg_w, fl, lab, dsg) in (
                (KA, KAN, 2, 5, 17, (21, 11), 'A', la),
                (KB, KBN, 2, 3, 15, (13, 7), 'B', lb)):
            r = read_class(p, P1, f, K, e2f2, u2, 4)
            chk(tag, r['status'] == 'OK' and r.get('mu2s') == 2,
                'class %s mu2* = %s != 2' % (lab, r.get('mu2s')))
            if r.get('mu2s') == 2:
                chk(tag, r['cg'] == cg_w,
                    'class %s c_g %s != %d' % (lab, r['cg'], cg_w))
                want = '2SIDED' if dsg == '2S' else 'RAM'
                chk(tag, r['verdict'] == want,
                    'class %s verdict %s != %s'
                    % (lab, r['verdict'], want))
                for j in (0, 1):
                    pj = r['pins'].get(j)
                    chk(tag, pj is None or pj - cg_w >= fl[j],
                        'class %s floor j=%d: %s' % (lab, j, pj))
            rn = read_class(p, P1, f, KNv, e2f2, u2, 4)
            chk(tag, rn['status'] == 'OK' and rn.get('mu2s') == 0,
                'TOOTH class %s naive mu2* = %s (want 0)'
                % (lab, rn.get('mu2s')))
            say('%s.%s: pins %s cg %s | naive pins %s'
                % (tag, lab, sorted(r['pins'].items()), r.get('cg'),
                   sorted(rn['pins'].items())))
        for nm, K in (('kA', KA), ('kB', KB), ('kAN', KAN),
                      ('kBN', KBN)):
            jobs.append('print("%s.%s ", keyval(%s, 3, %s))'
                        % (tag, nm, poly_str(f), poly_str(K)))
        jobs.append('print("%s.s1 ", sig1(%s, 3))' % (tag, poly_str(f)))
        jobs.append('print("%s.s2 ", sig2(%s, 3))' % (tag, poly_str(f)))
        jobs.append('print("%s.d ", poldisc(%s) != 0)'
                    % (tag, poly_str(f)))

    # ---- gp adjudication ----
    say('running gp (%d jobs)...' % len(jobs))
    res = run_gp(jobs)

    chk('FRT', sig_parse(res.get('KT', '')) == [(2, 3)],
        'corrected key sigma %s != {(2,3)}' % res.get('KT'))
    chk('FRT', sig_parse(res.get('KL', '')) == [(2, 3)],
        'rescaled key sigma %s != {(2,3)} (carrier-but-wrong-datum)'
        % res.get('KL'))
    chk('FRT', sig_parse(res.get('KN', '')) == [(2, 1), (2, 2)],
        'naive key sigma %s != predicted {(2,1),(2,2)}'
        % res.get('KN'))
    say('FR-T keys: KT %s | KL %s | KN %s'
        % (res.get('KT'), res.get('KL'), res.get('KN')))
    for tag, f, verd, sig in MT:
        chk(tag, res.get(tag + '.d') == '1', 'disc = 0')
        for rt in ('.s1', '.s2'):
            got = sig_parse(res.get(tag + rt, ''))
            chk(tag, got == sorted(sig),
                'sigma%s %s != %s' % (rt, got, sorted(sig)))
        keyval_checks(tag, 'kT', tup_parse(res.get(tag + '.kT', ''), 3),
                      9, True, 12)
        keyval_checks(tag, 'kN', tup_parse(res.get(tag + '.kN', ''), 3),
                      9, False, 12)
        say('%s: kT %s | kN %s' % (tag, res.get(tag + '.kT'),
                                   res.get(tag + '.kN')))

    for nm in ('KA', 'KB'):
        chk('FRC', sig_parse(res.get(nm, '')) == [(2, 2)],
            '%s sigma %s != {(2,2)}' % (nm, res.get(nm)))
    for nm in ('KAN', 'KBN'):
        chk('FRC', sig_parse(res.get(nm, '')) != [(2, 2)],
            'TOOTH %s IS the carrier (unexpected)' % nm)
    say('FR-C keys: KA %s KB %s | naive KAN %s KBN %s'
        % (res.get('KA'), res.get('KB'), res.get('KAN'),
           res.get('KBN')))
    for tag, f, la, lb in MC:
        chk(tag, res.get(tag + '.d') == '1', 'disc = 0')
        want = sorted(BSIG[la] + BSIG[lb] + [(2, 1)])
        for rt in ('.s1', '.s2'):
            got = sig_parse(res.get(tag + rt, ''))
            chk(tag, got == want,
                'sigma%s %s != %s' % (rt, got, want))
        keyval_checks(tag, 'kA', tup_parse(res.get(tag + '.kA', ''), 3),
                      10, True, 8)
        keyval_checks(tag, 'kB', tup_parse(res.get(tag + '.kB', ''), 3),
                      6, True, 8)
        # naive collapse: the CLASS rows only (companion rows can sit
        # below E2 legitimately); check no row is ABOVE E2 and the
        # at-E2 mass covers the block degree 8.
        keyval_checks(tag, 'kAN', tup_parse(res.get(tag + '.kAN', ''),
                                            3), 10, False, 8)
        keyval_checks(tag, 'kBN', tup_parse(res.get(tag + '.kBN', ''),
                                            3), 6, False, 8)
        say('%s: kA %s | kB %s' % (tag, res.get(tag + '.kA'),
                                   res.get(tag + '.kB')))
        say('%s: kAN %s | kBN %s' % (tag, res.get(tag + '.kAN'),
                                     res.get(tag + '.kBN')))

    say('')
    say('TOTAL: %d checks, %d violations' % (NCHK, NVIO))
    say('VERDICT: %s' % ('GREEN' if NVIO == 0 else 'RED'))


if __name__ == '__main__':
    main()
