#!/usr/bin/env python3
"""GENTOW4 passPE3 FRESH instrument (acceptance-attempt verifier's own
code, written independently of the sealed runner and of the PE1/PE2
instruments; frames disjoint from the battery and from
FR-G/FR-M/FR-W/FR-T/FR-C).

FR-3B (the FIRST THREE-BLOCK partial member anywhere, gauge-live):
  p = 3, Phi' = x^2 - 6 (h = 1, eta = 2), genre (2,1,13), n = 26.
  THREE inner classes, each (e2,f2) = (1,2), mu2 = 2, on three sides,
  plus a sibling:
    side A [1,5]  slope 7: psi2A = Z^2+Z+2  (c1=2,c0=1), W = (1,0),
      KA = Phi'^2 - 54x*Phi' - 4374  (chat1 = lift(2*2^0) = 2 -> 2*27x;
      chat0 = lift(1*2^1) = 2 -> 2*2187), T2A = 14; naive
      KAN = .. - 2187 (chat0N = lift(1) = 1); naive letter datum
      c0' = 2 (from lift(c0'*2) = 1): Z^2-2Z-2 = (Z-1)^2 /F3 DEGENERATE.
    side B [5,9]  slope 5: psi2B = Z^2+2Z+2 (c1=1,c0=1), W = (1,0),
      KB = Phi'^2 - 9x*Phi' - 486, T2B = 10; naive KBN = .. - 243;
      naive letter Z^2-Z-2 = (Z-2)^2 DEGENERATE.
    side C [9,13] slope 3: psi2C = Z^2+1   (c1=0,c0=2), W = (.,1) on
      the only live slot t=0: chat0 = lift(2*2) = 1 -> KC = Phi'^2 - 27,
      T2C = 6; naive KCN = Phi'^2 - 54 = the CORRECTED key of the
      GHOST datum c0'' = 1 (lift(c0''*2) = 2): letter Z^2-1 =
      (Z-1)(Z+1) REDUCIBLE.
    sibling g = x^2 - 87 (dv(6-87) = 8, slope 8, length 1, (2,1)).
  Level-1 hull: (0,68),(1,60),(5,32),(9,12),(13,0).
  Blocks (deg 8 each; slot height of c*x^i*Phi'^b = 2*v3(c)+i+b*u2):
    A-2S = KA^2 + 2187x*KA + 3^15*x  (pins 31,15,0; slopes 16,15)
    A-RAM = KA^2 + 3^15*x            (slope 31/2)
    B-2S = KB^2 + 243x*KB + 3^11*x   (pins 23,11,0; slopes 12,11)
    B-RAM = KB^2 + 3^11*x            (slope 23/2)
    C-2S = KC^2 + 27x*KC + 3^7*x     (pins 15,7,0;  slopes 8,7)
    C-RAM = KC^2 + 3^7*x             (slope 15/2)
  Members (3): M1 = (A-2S, B-RAM, C-2S)*g, M2 = (A-RAM, B-2S, C-2S)*g,
  M3 = (A-2S, B-2S, C-RAM)*g.
  Hand-derived c_g per class (sum of the OTHER factors' level-1
  support values at the class slope):
    c_gA = h_fB(7)+h_fC(7)+h_g(7) = 20+12+7 = 39
    c_gB = h_fA(5)+h_fC(5)+h_g(5) = 20+12+5 = 37
    c_gC = h_fA(3)+h_fB(3)+h_g(3) = 12+12+3 = 27
  PREREG: level-1 hulls exact; per member per class at the CORRECTED
  key: mu2* = 2, c_g = (39,37,27), verdict = design (2SIDED/RAM),
  floors (2-j)*E2+1 with j=1 EXACT on 2S blocks (p1-c_g = E2+1);
  sigma = PARI (both routes) = sig_A u sig_B u sig_C u {(2,1)} with
  2S -> {(2,2)}x2, RAM -> {(4,2)}; key sigmas: KA=KB=KC={(2,2)}
  (carriers), KAN/KBN != {(2,2)}, KCN = {(2,1),(2,1)} (the ghost
  SPLIT datum); TOOTH T-N: naive keys read mu2* = 0 at their class
  on every member; nfeltval: class rows 2v > E2*e STRICT with class
  degree sum = 8 = D2*mu2* at each corrected key (checked ==, both
  sides; no vacuous branch — the m-D lesson); COR GENTOW-4.C PIN
  DISPLAY (explicit-f_S leg): pins_f[j] - c_g == pins_fS[j] at every
  hull abscissa j in {0,1,2} of the block read (f_S is constructed,
  so 4.C's translation is tested as an EQUATION, not just floors).

FR-Q (the FIRST f2 >= 4 frame anywhere; non-linear W = (2,1,1,0) at
  eta = 2, and the MERGED naive/rescale tooth):
  p = 3, Phi' = x^2 - 6, genre (2,1,9), n = 18; inner (e2,f2) =
  (1,4), u2 = 3, psi2 = Z^4 + Z + 2 (irreducible /F3; c3=c2=0, c1=2,
  c0=1), mu2 = 2 on side [1,9] slope 3 (length 8) — PARTIAL
  (8 < mu1 = 9); sibling g = x^2 - 15 (slope 4). D2 = 8, E2 = T2 = 12.
  W(t) = floor((4-t)/2) = (2,1,1,0); eta^2 = 4 = 1 /F3, so the
  W-even slot t=0 is GAUGE-BLIND (chat0 = lift(1*4) = 1 = naive) and
  the whole correction lives at t=1: chat1 = lift(2*2) = 1 vs naive 2.
    KQ  = Phi'^4 - 81x*Phi' - 729   (corrected; letter Z^4-2Z-1 =
          psi2 twisted: beta^4 = 2beta+1)
    KQN = Phi'^4 - 162x*Phi' - 729  (naive; letter Z^4-Z-1)
  MERGED TOOTH: KQN is BYTE-IDENTICAL to the corrected key of the
  lam = 2 rescaled datum (c_t' = c_t*2^t: c1' = 1, c0' = 1; minpoly
  of 2beta = Z^4-Z-1, irreducible): at f2 = 4 with eta^2 = 1 the
  naive key IS a carrier ({(2,4)}) — the naive and
  carrier-but-wrong-datum teeth MERGE; the datum keying alone
  separates them.
  Blocks: Q-2S = KQ^2 + 729x*KQ + 3^13*x (pins 27,13,0; slopes
  14,13), Q-RAM = KQ^2 + 3^13*x (slope 27/2). Members Q-2S*g, Q-RAM*g
  (deg 18). c_g = h_g(3) = 3. Level-1 hull (0,28),(1,24),(9,0).
  PREREG: sigma(KQ) = {(2,4)}; sigma(KQN) = {(2,4)} TOO (carrier,
  wrong datum); corrected reads mu2* = 2, c_g = 3, floors (25,13)
  with j=1 EXACT on 2S, verdicts 2SIDED/RAM, sigma = PARI both
  routes ({(2,1),(2,4),(2,4)} resp. {(2,1),(4,4)}); TOOTH: KQN
  reads mu2* = 0 on both members (the t=1 discrepancy (1-2)*81x*Phi'
  sits at slot height 8+1+3 = 12 = T2 exactly); nfeltval at KQ:
  class rows 2v > 12e strict, degree sum 16 = D2*mu2*; at KQN the
  class rows sit AT 2v = 12e (collapse); 4.C pin display as above.

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
    assert g in ([], [0], [1]), 'dev overflow'
    pins = {}
    if g == [1]:                      # monic exact-length input (f_S)
        pins[M] = 0
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


def pin_display_check(tag, lab, rf, rs):
    """COR GENTOW-4.C explicit-f_S leg: pins_f[j] - c_g == pins_fS[j]
    at every hull abscissa of the block read (>T2 initial segment
    spans [0,2] here, so the hull abscissas are the vertex set)."""
    cg = rf.get('cg')
    chk(tag, rs.get('cg') == 0,
        '%s f_S own read has c_g %s != 0' % (lab, rs.get('cg')))
    for (j, y) in rf['hull']:
        if j > rf['mu2s']:
            continue
        pf, ps = rf['pins'].get(j), rs['pins'].get(j)
        chk(tag, pf is not None and ps is not None and pf - cg == ps,
            '%s 4.C pin display j=%d: f pin %s - cg %s != fS pin %s'
            % (lab, j, pf, cg, ps))


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


def sep_checks(tag, lab, rows, E2, want_sum, collapse):
    """Field-floor separator, TWO-SIDED (the m-D lesson: no branch
    tests its own condition; class mass checked with == not >=).
    strict mode (collapse=False): class rows := 2v > E2*e; their
    degree sum must EQUAL want_sum, and no non-class row may exceed
    E2 (enforced by the same partition).  collapse mode: no row above
    E2, and the at-E2 mass must cover want_sum."""
    ncls = nat = 0
    for (e_, f_, v_) in rows:
        if 2 * v_ > E2 * e_:
            ncls += e_ * f_
        elif 2 * v_ == E2 * e_:
            nat += e_ * f_
    if collapse:
        chk(tag, ncls == 0,
            '%s collapse: rows ABOVE E2=%d (mass %d)' % (lab, E2, ncls))
        chk(tag, nat >= want_sum,
            '%s collapse: at-E2 mass %d < %d' % (lab, nat, want_sum))
    else:
        chk(tag, ncls == want_sum,
            '%s strict class degree sum %d != %d' % (lab, ncls,
                                                     want_sum))


def main():
    say('GENTOW4 passPE3 fresh instrument (FR-3B first three-block '
        'member, gauge-live; FR-Q first f2=4, W=(2,1,1,0), merged '
        'naive/rescale tooth)')
    p = 3
    P1 = [-6, 0, 1]                                # Phi' = x^2-6
    jobs = []

    # ================= FR-3B =================
    KA = padd(padd(pmul(P1, P1), pmul([0, -54], P1)), [-4374])
    KAN = padd(padd(pmul(P1, P1), pmul([0, -54], P1)), [-2187])
    KB = padd(padd(pmul(P1, P1), pmul([0, -9], P1)), [-486])
    KBN = padd(padd(pmul(P1, P1), pmul([0, -9], P1)), [-243])
    KC = padd(pmul(P1, P1), [-27])
    KCN = padd(pmul(P1, P1), [-54])
    g3 = [-87, 0, 1]
    fA = {'2S': padd(padd(pmul(KA, KA), pmul([0, 3 ** 7], KA)),
                     [0, 3 ** 15]),
          'RAM': padd(pmul(KA, KA), [0, 3 ** 15])}
    fB = {'2S': padd(padd(pmul(KB, KB), pmul([0, 3 ** 5], KB)),
                     [0, 3 ** 11]),
          'RAM': padd(pmul(KB, KB), [0, 3 ** 11])}
    fC = {'2S': padd(padd(pmul(KC, KC), pmul([0, 3 ** 3], KC)),
                     [0, 3 ** 7]),
          'RAM': padd(pmul(KC, KC), [0, 3 ** 7])}
    BSIG = {'2S': [(2, 2), (2, 2)], 'RAM': [(4, 2)]}
    for nm, K in (('KA', KA), ('KB', KB), ('KC', KC), ('KAN', KAN),
                  ('KBN', KBN), ('KCN', KCN)):
        jobs.append('print("%s ", sig1(%s, 3))' % (nm, poly_str(K)))
    COMBOS = [('M1', '2S', 'RAM', '2S'), ('M2', 'RAM', '2S', '2S'),
              ('M3', '2S', '2S', 'RAM')]
    CLS = (('A', KA, KAN, 7, 14, 39),
           ('B', KB, KBN, 5, 10, 37),
           ('C', KC, KCN, 3, 6, 27))
    M3B = []
    for mnm, la, lb, lc in COMBOS:
        tag = 'FR3B-' + mnm
        f = pmul(pmul(pmul(fA[la], fB[lb]), fC[lc]), g3)
        M3B.append((tag, f, la, lb, lc))
        hull = level1_hull(p, P1, f, 13)
        chk(tag, hull == [(0, 68), (1, 60), (5, 32), (9, 12),
                          (13, 0)], 'level-1 hull %s' % hull)
        for (lab, K, KNv, u2, E2, cgw), dsg, fX in zip(
                CLS, (la, lb, lc), (fA[la], fB[lb], fC[lc])):
            r = read_class(p, P1, f, K, 2, u2, 13)
            chk(tag, r['status'] == 'OK' and r.get('mu2s') == 2,
                'class %s mu2* = %s != 2' % (lab, r.get('mu2s')))
            if r.get('mu2s') != 2:
                continue
            chk(tag, r['cg'] == cgw,
                'class %s c_g %s != %d' % (lab, r['cg'], cgw))
            want = '2SIDED' if dsg == '2S' else 'RAM'
            chk(tag, r['verdict'] == want,
                'class %s verdict %s != %s' % (lab, r['verdict'],
                                               want))
            for j in (0, 1):
                pj = r['pins'].get(j)
                chk(tag, pj is None or pj - cgw >= (2 - j) * E2 + 1,
                    'class %s floor j=%d: %s - %d < %d'
                    % (lab, j, pj, cgw, (2 - j) * E2 + 1))
            if dsg == '2S':
                chk(tag, r['pins'].get(1) == cgw + E2 + 1,
                    'class %s j=1 floor not EXACT: %s != %d'
                    % (lab, r['pins'].get(1), cgw + E2 + 1))
            rs = read_class(p, P1, fX, K, 2, u2, 4)
            pin_display_check(tag, 'class ' + lab, r, rs)
            rn = read_class(p, P1, f, KNv, 2, u2, 13)
            chk(tag, rn['status'] == 'OK' and rn.get('mu2s') == 0,
                'TOOTH class %s naive mu2* = %s (want 0)'
                % (lab, rn.get('mu2s')))
            say('%s.%s: pins01 %s cg %s | fS pins %s | naive hull %s'
                % (tag, lab, [r['pins'].get(0), r['pins'].get(1)],
                   r['cg'], sorted(rs['pins'].items()),
                   rn['hull'][:3]))
        sig = sorted(BSIG[la] + BSIG[lb] + BSIG[lc] + [(2, 1)])
        for nm, K in (('kA', KA), ('kB', KB), ('kC', KC)):
            jobs.append('print("%s.%s ", keyval(%s, 3, %s))'
                        % (tag, nm, poly_str(f), poly_str(K)))
        jobs.append('print("%s.s1 ", sig1(%s, 3))' % (tag, poly_str(f)))
        jobs.append('print("%s.s2 ", sig2(%s, 3))' % (tag, poly_str(f)))
        jobs.append('print("%s.d ", poldisc(%s) != 0)'
                    % (tag, poly_str(f)))
        globals().setdefault('WANT3B', {})[tag] = sig
    # naive keyval collapse rows on M1 only
    jobs.append('print("FR3B-M1.kAN ", keyval(%s, 3, %s))'
                % (poly_str(M3B[0][1]), poly_str(KAN)))
    jobs.append('print("FR3B-M1.kCN ", keyval(%s, 3, %s))'
                % (poly_str(M3B[0][1]), poly_str(KCN)))

    # ================= FR-Q =================
    KQ = padd(padd(ppow4(P1), pmul([0, -81], P1)), [-729])
    KQN = padd(padd(ppow4(P1), pmul([0, -162], P1)), [-729])
    gQ = [-15, 0, 1]
    fQ = {'2S': padd(padd(pmul(KQ, KQ), pmul([0, 3 ** 6], KQ)),
                     [0, 3 ** 13]),
          'RAM': padd(pmul(KQ, KQ), [0, 3 ** 13])}
    jobs.append('print("KQ ", sig1(%s, 3))' % poly_str(KQ))
    jobs.append('print("KQN ", sig1(%s, 3))' % poly_str(KQN))
    MQ = [('FRQ-2S', pmul(fQ['2S'], gQ), '2SIDED',
           [(2, 1), (2, 4), (2, 4)]),
          ('FRQ-RAM', pmul(fQ['RAM'], gQ), 'RAM', [(2, 1), (4, 4)])]
    for tag, f, verd, sig in MQ:
        hull = level1_hull(p, P1, f, 9)
        chk(tag, hull == [(0, 28), (1, 24), (9, 0)],
            'level-1 hull %s' % hull)
        r = read_class(p, P1, f, KQ, 4, 3, 2)
        chk(tag, r['status'] == 'OK' and r.get('mu2s') == 2,
            'corrected mu2* = %s != 2' % r.get('mu2s'))
        if r.get('mu2s') == 2:
            chk(tag, r['cg'] == 3, 'c_g %s != 3' % r['cg'])
            chk(tag, r['verdict'] == verd,
                'verdict %s != %s' % (r['verdict'], verd))
            for j, fl in ((0, 25), (1, 13)):
                pj = r['pins'].get(j)
                chk(tag, pj is None or pj - 3 >= fl,
                    'floor j=%d: %s - 3 < %d' % (j, pj, fl))
            if verd == '2SIDED':
                chk(tag, r['pins'].get(1) == 3 + 13,
                    'j=1 floor not EXACT: %s' % r['pins'].get(1))
            fS = fQ['2S' if verd == '2SIDED' else 'RAM']
            rs = read_class(p, P1, fS, KQ, 4, 3, 2)
            pin_display_check(tag, 'block', r, rs)
        rn = read_class(p, P1, f, KQN, 4, 3, 2)
        chk(tag, rn['status'] == 'OK' and rn.get('mu2s') == 0,
            'TOOTH naive/rescaled mu2* = %s (want 0)'
            % rn.get('mu2s'))
        say('%s: pins %s cg %s | naive pins %s'
            % (tag, sorted(r['pins'].items()), r.get('cg'),
               sorted(rn['pins'].items())))
        for nm, K in (('kQ', KQ), ('kQN', KQN)):
            jobs.append('print("%s.%s ", keyval(%s, 3, %s))'
                        % (tag, nm, poly_str(f), poly_str(K)))
        jobs.append('print("%s.s1 ", sig1(%s, 3))' % (tag, poly_str(f)))
        jobs.append('print("%s.s2 ", sig2(%s, 3))' % (tag, poly_str(f)))
        jobs.append('print("%s.d ", poldisc(%s) != 0)'
                    % (tag, poly_str(f)))

    # ---- gp adjudication ----
    say('running gp (%d jobs)...' % len(jobs))
    res = run_gp(jobs)

    for nm in ('KA', 'KB', 'KC'):
        chk('FR3B', sig_parse(res.get(nm, '')) == [(2, 2)],
            '%s sigma %s != {(2,2)}' % (nm, res.get(nm)))
    for nm in ('KAN', 'KBN'):
        chk('FR3B', sig_parse(res.get(nm, '')) != [(2, 2)],
            'TOOTH %s IS the carrier (unexpected)' % nm)
    chk('FR3B', sig_parse(res.get('KCN', '')) == [(2, 1), (2, 1)],
        'ghost-split KCN sigma %s != {(2,1),(2,1)}' % res.get('KCN'))
    say('FR-3B keys: KA %s KB %s KC %s | KAN %s KBN %s KCN %s'
        % tuple(res.get(nm) for nm in ('KA', 'KB', 'KC', 'KAN',
                                       'KBN', 'KCN')))
    for tag, f, la, lb, lc in M3B:
        chk(tag, res.get(tag + '.d') == '1', 'disc = 0')
        want = WANT3B[tag]
        for rt in ('.s1', '.s2'):
            got = sig_parse(res.get(tag + rt, ''))
            chk(tag, got == want,
                'sigma%s %s != %s' % (rt, got, want))
        for nm, E2 in (('kA', 14), ('kB', 10), ('kC', 6)):
            sep_checks(tag, nm, tup_parse(res.get(
                '%s.%s' % (tag, nm), ''), 3), E2, 8, False)
        say('%s: kA %s' % (tag, res.get(tag + '.kA')))
        say('%s: kB %s | kC %s' % (tag, res.get(tag + '.kB'),
                                   res.get(tag + '.kC')))
    sep_checks('FR3B-M1', 'kAN', tup_parse(res.get('FR3B-M1.kAN', ''),
                                           3), 14, 8, True)
    sep_checks('FR3B-M1', 'kCN', tup_parse(res.get('FR3B-M1.kCN', ''),
                                           3), 6, 8, True)
    say('FR3B-M1: kAN %s | kCN %s' % (res.get('FR3B-M1.kAN'),
                                      res.get('FR3B-M1.kCN')))

    chk('FRQ', sig_parse(res.get('KQ', '')) == [(2, 4)],
        'corrected key sigma %s != {(2,4)}' % res.get('KQ'))
    chk('FRQ', sig_parse(res.get('KQN', '')) == [(2, 4)],
        'MERGED TOOTH: naive=rescaled key sigma %s != {(2,4)} '
        '(expected CARRIER)' % res.get('KQN'))
    say('FR-Q keys: KQ %s | KQN %s (naive = rescaled-datum corrected '
        'key, byte-identical)' % (res.get('KQ'), res.get('KQN')))
    for tag, f, verd, sig in MQ:
        chk(tag, res.get(tag + '.d') == '1', 'disc = 0')
        for rt in ('.s1', '.s2'):
            got = sig_parse(res.get(tag + rt, ''))
            chk(tag, got == sorted(sig),
                'sigma%s %s != %s' % (rt, got, sorted(sig)))
        sep_checks(tag, 'kQ', tup_parse(res.get(tag + '.kQ', ''), 3),
                   12, 16, False)
        sep_checks(tag, 'kQN', tup_parse(res.get(tag + '.kQN', ''), 3),
                   12, 16, True)
        say('%s: kQ %s | kQN %s' % (tag, res.get(tag + '.kQ'),
                                    res.get(tag + '.kQN')))

    say('')
    say('TOTAL: %d checks, %d violations' % (NCHK, NVIO))
    say('VERDICT: %s' % ('GREEN' if NVIO == 0 else 'RED'))


def ppow4(f):
    f2 = pmul(f, f)
    return pmul(f2, f2)


if __name__ == '__main__':
    main()
